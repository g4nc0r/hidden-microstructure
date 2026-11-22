// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test, console} from "forge-std/Test.sol";
import {MockCLPoolV2} from "../src/MockCLPoolV2.sol";
import {TickHelpers} from "./helpers/Tick.sol";
import {V3Math} from "./helpers/V3Math.sol";

/// @title MasterEquationT1Mock
/// @notice Network-free tests of Theorem 1, the per-event jump of the dust ledger:
///
///             L_new   = min(hat_x / g_x, hat_y / g_y)
///             x_dust' = hat_x - L_new g_x,   y_dust' = hat_y - L_new g_y
///
///         with hat = withdrawn + standing balance - swap.
///
/// The pool is the integer model in `helpers/V3Math.sol` (liquidity as the position
/// manager sizes it, amounts as the pool takes them), which the fork tests check
/// against two unmodified position managers to the base unit. Each test here runs a
/// mint through that model and checks it against the theorem by three statements that
/// do not reuse the model's own formula for the liquidity:
///
///   - the liquidity minted is the largest both inputs allow (one more unit would
///     need more of some token than was offered);
///   - the token that binds is used up, to within what one unit of liquidity takes;
///   - what is left of the other token is the offered amount less the binding
///     amount times g_slack / g_binding, computed here in 512-bit arithmetic.
///
/// Token0 is called WETH and token1 USDC after the pool the paper's example uses.
/// Values are in token1 units at the pool price.
contract MasterEquationT1Mock is Test {
    MockCLPoolV2 internal tickMath;

    // The anchor of the Geometric Siphon suite: a position opened at tick 78,244 into a
    // range of 500 ticks either side, withdrawn after the price has moved 200 ticks up.
    int24 constant BASE_TICK = 78244;
    int24 constant DISPLACED_TICK = 78444;
    int24 constant TICK_SPACING = 100;

    struct Setup {
        uint160 s;
        uint160 sa;
        uint160 sb;
        uint256 wd0;
        uint256 wd1;
    }

    function setUp() public {
        tickMath = new MockCLPoolV2(0);
    }

    function _sqrt(int24 tick) internal view returns (uint160) {
        return tickMath.getSqrtRatioAtTick(tick);
    }

    function _nearest(int24 t) internal pure returns (int24) {
        return TickHelpers.nearest(t, TICK_SPACING);
    }

    /// @dev The anchor position withdrawn at the displaced price, and a new range of
    ///      `halfWidth` ticks either side of that price.
    function _anchor(int24 halfWidth) internal view returns (Setup memory u) {
        uint160 sOpen = _sqrt(BASE_TICK);
        uint160 oldA = _sqrt(_nearest(BASE_TICK - 500));
        uint160 oldB = _sqrt(_nearest(BASE_TICK + 500));
        uint128 lOld = V3Math.liquidityForAmounts(sOpen, oldA, oldB, 1 ether, 2500e6);
        u.s = _sqrt(DISPLACED_TICK);
        (u.wd0, u.wd1) = V3Math.amountsDown(u.s, oldA, oldB, lOld);
        u.sa = _sqrt(_nearest(DISPLACED_TICK - halfWidth));
        u.sb = _sqrt(_nearest(DISPLACED_TICK + halfWidth));
    }

    /// @dev Mint (hat0, hat1) into [sa, sb] at an interior price and check the three
    ///      statements of Theorem 1 listed in the contract note.
    function _jump(uint160 s, uint160 sa, uint160 sb, uint256 hat0, uint256 hat1)
        internal
        pure
        returns (V3Math.Jump memory j)
    {
        require(sa < s && s < sb, "price not interior");
        j = V3Math.mint(s, sa, sb, hat0, hat1);

        // Largest liquidity both inputs allow.
        (uint256 more0, uint256 more1) = V3Math.amountsUp(s, sa, sb, j.liquidity + 1);
        assertTrue(more0 > hat0 || more1 > hat1, "eq:lnew: one more unit of liquidity is not affordable");

        // The binding token is used up, to within one unit of liquidity.
        (uint256 unit0, uint256 unit1) = V3Math.amountsUp(s, sa, sb, 1);
        bool binds0 = more0 > hat0;
        if (binds0) assertLe(j.left0, unit0, "eq:newdust: the binding token is used up");
        else assertLe(j.left1, unit1, "eq:newdust: the binding token is used up");

        // The other token's leftover in closed form: hat_slack - hat_binding * g_slack / g_binding,
        // with g_y / g_x = (s - sa) s sb / ((sb - s) 2^192).
        // Intermediate results carry 64 extra bits so that small integer amounts lose nothing.
        uint256 ratio = V3Math.mulDiv(s - sa, sb, sb - s); // Q96 times g_y / (g_x s)
        if (binds0) {
            uint256 need1 = V3Math.mulDiv(V3Math.mulDiv(hat0 << 64, s, V3Math.Q96), ratio, V3Math.Q96) >> 64;
            assertApproxEqAbs(j.left1, hat1 - need1, unit1 + 2, "eq:newdust: slack-side leftover");
        } else {
            uint256 need0 = V3Math.mulDiv(V3Math.mulDiv(hat1 << 64, V3Math.Q96, ratio), V3Math.Q96, s) >> 64;
            assertApproxEqAbs(j.left0, hat0 - need0, unit0 + 2, "eq:newdust: slack-side leftover");
        }
    }

    /// @dev Value in token1 units of three base units of token0 at sqrt price `s`. Token0
    ///      amounts are small integers at this anchor, so a value statement cannot be
    ///      tighter than this.
    function _grain(uint160 s) internal pure returns (uint256) {
        return 3 * V3Math.value0(1e6, s) / 1e6 + 3;
    }

    function _value(uint256 a0, uint256 a1, uint160 s) internal pure returns (uint256) {
        return V3Math.value0(a0, s) + a1;
    }

    // =========================================================================
    // 1. No swap, empty ledger: the geometric residual of the prior paper.
    // =========================================================================
    function test_t1_swapfree_zeroDust() public view {
        Setup memory u = _anchor(1000);
        V3Math.Jump memory j = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1);

        console.log("dust0After (WETH):", j.left0);
        console.log("dust1After (USDC):", j.left1);
        console.log("Withdrawn value (token1 units):", _value(u.wd0, u.wd1, u.s));

        // After an upward move the position is long token1, and token1 is what is left.
        assertGt(j.left1, 1e6, "the leftover is in token1");
        assertLe(j.left0, 1, "token0 binds");
        // The prior paper reports 2,061 USDC for this set-up; the exact tick arithmetic
        // here gives a figure within 5% of it.
        assertApproxEqRel(j.left1, 2061e6, 0.05e18, "within 5% of the prior paper's residual");
    }

    // =========================================================================
    // 2. No swap, a standing balance of the binding token: the mint grows and the
    //    leftover of the other token falls by the balance times g_y / g_x.
    // =========================================================================
    function test_t1_swapfree_nonzeroDust_boundSide() public view {
        Setup memory u = _anchor(1000);
        V3Math.Jump memory base = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1);

        // A balance of token0 worth a tenth of the base leftover.
        uint256 added0 = V3Math.amount0ForValue(base.left1 / 10, u.s);
        V3Math.Jump memory j = _jump(u.s, u.sa, u.sb, u.wd0 + added0, u.wd1);

        console.log("Base L_new / with balance:", uint256(base.liquidity), uint256(j.liquidity));
        console.log("Base dust1After / with balance:", base.left1, j.left1);

        assertGt(j.liquidity, base.liquidity, "L_new grows with the binding input");
        uint256 ratio = V3Math.mulDiv(u.s - u.sa, u.sb, u.sb - u.s);
        uint256 taken1 = V3Math.mulDiv(V3Math.mulDiv(added0 << 64, u.s, V3Math.Q96), ratio, V3Math.Q96) >> 64;
        assertApproxEqAbs(base.left1 - j.left1, taken1, 4, "the leftover falls by the balance times g_y / g_x");
    }

    // =========================================================================
    // 3. No swap, a standing balance of the slack token: the mint is unchanged and
    //    the leftover rises by exactly the balance.
    // =========================================================================
    function test_t1_swapfree_nonzeroDust_slackSide() public view {
        Setup memory u = _anchor(1000);
        V3Math.Jump memory base = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1);
        uint256 added1 = 5000e6;
        V3Math.Jump memory j = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1 + added1);

        console.log("Base dust1After / with balance:", base.left1, j.left1);
        assertEq(uint256(j.liquidity), uint256(base.liquidity), "L_new unchanged by the slack input");
        assertEq(j.left0, base.left0, "binding-side leftover unchanged");
        assertEq(j.left1, base.left1 + added1, "the leftover rises by exactly the balance");
    }

    // =========================================================================
    // 4. A swap short of the amount that would leave nothing: the same token is
    //    left, and less of it.
    // =========================================================================
    function test_t1_swap_belowThreshold() public view {
        Setup memory u = _anchor(1000);
        V3Math.Jump memory base = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1);

        (uint256 a, uint256 b) = V3Math.requiredValues(u.s, u.sa, u.sb);
        uint256 perfect = V3Math.mulDiv(_value(u.wd0, u.wd1, u.s), a, a + b) - V3Math.value0(u.wd0, u.s);
        uint256 paid1 = perfect / 2;
        uint256 got0 = V3Math.amount0ForValue(paid1, u.s);
        V3Math.Jump memory j = _jump(u.s, u.sa, u.sb, u.wd0 + got0, u.wd1 - paid1);

        console.log("Leftover (token1) without / with the swap:", base.left1, j.left1);
        assertLe(j.left0, 1, "token0 still binds");
        assertLt(j.left1, base.left1, "the swap reduces the leftover");
        assertApproxEqAbs(
            j.left1,
            V3Math.mulDiv(perfect - paid1, a + b, a),
            2 * _grain(u.s),
            "leftover: shortfall over the required share"
        );
    }

    // =========================================================================
    // 5. A swap beyond that amount: the binding side flips and the token the swap
    //    bought is left.
    // =========================================================================
    function test_t1_swap_overshoot() public view {
        Setup memory u = _anchor(1000);
        (uint256 a, uint256 b) = V3Math.requiredValues(u.s, u.sa, u.sb);
        uint256 perfect = V3Math.mulDiv(_value(u.wd0, u.wd1, u.s), a, a + b) - V3Math.value0(u.wd0, u.s);
        uint256 paid1 = perfect * 3 / 2;
        uint256 got0 = V3Math.amount0ForValue(paid1, u.s);
        V3Math.Jump memory j = _jump(u.s, u.sa, u.sb, u.wd0 + got0, u.wd1 - paid1);

        console.log("Overshoot dust0After / dust1After:", j.left0, j.left1);
        assertLe(j.left1, 2, "token1 now binds");
        assertApproxEqAbs(
            V3Math.value0(j.left0, u.s),
            V3Math.mulDiv(paid1 - perfect, a + b, b),
            2 * _grain(u.s),
            "leftover in token0: excess over the required share"
        );
    }

    // =========================================================================
    // 6. The price outside the new range, and inside it.
    // =========================================================================
    function test_t1_threeSubcases() public view {
        Setup memory u = _anchor(1000);

        // (a) New range wholly above the price: the mint takes token0 only.
        {
            uint160 sa = _sqrt(_nearest(DISPLACED_TICK + 1500));
            uint160 sb = _sqrt(_nearest(DISPLACED_TICK + 3500));
            V3Math.Jump memory j = V3Math.mint(u.s, sa, sb, u.wd0, u.wd1);
            (uint256 more0,) = V3Math.amountsUp(u.s, sa, sb, j.liquidity + 1);
            console.log("Subcase (a) above the price: dust0 / dust1 =", j.left0, j.left1);
            assertEq(j.left1, u.wd1, "above the price: token1 is credited whole");
            assertEq(j.used1, 0, "above the price: no token1 is taken");
            assertGt(more0, u.wd0, "above the price: the mint takes all the token0 it can");
        }
        // (b) New range wholly below the price: the mint takes token1 only.
        {
            uint160 sa = _sqrt(_nearest(DISPLACED_TICK - 3500));
            uint160 sb = _sqrt(_nearest(DISPLACED_TICK - 1500));
            V3Math.Jump memory j = V3Math.mint(u.s, sa, sb, u.wd0, u.wd1);
            (, uint256 more1) = V3Math.amountsUp(u.s, sa, sb, j.liquidity + 1);
            console.log("Subcase (b) below the price: dust0 / dust1 =", j.left0, j.left1);
            assertEq(j.left0, u.wd0, "below the price: token0 is credited whole");
            assertEq(j.used0, 0, "below the price: no token0 is taken");
            assertGt(more1, u.wd1, "below the price: the mint takes all the token1 it can");
        }
        // (c) The price inside the new range: Theorem 1 as stated.
        {
            V3Math.Jump memory j = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1);
            console.log("Subcase (c) inside: dust0 / dust1 =", j.left0, j.left1);
            assertGt(j.used0, 0, "inside: token0 is taken");
            assertGt(j.used1, 0, "inside: token1 is taken");
        }
    }

    // =========================================================================
    // 7. A leftover drawn into another position's mint. Position A leaves token1.
    //    Position B is opened with inputs short of token1 by 2,000 units of value and
    //    takes that much of A's leftover; the rest stays in the ledger.
    // =========================================================================
    function test_t1_multiPosition_recycle() public view {
        Setup memory u = _anchor(1000);
        V3Math.Jump memory ja = _jump(u.s, u.sa, u.sb, u.wd0, u.wd1);
        uint256 ledger1 = ja.left1;

        // B: a range centred in tick space on the price, so it takes the tokens in equal value.
        uint160 sa = _sqrt(DISPLACED_TICK - 600);
        uint160 sb = _sqrt(DISPLACED_TICK + 600);
        uint256 fresh0 = V3Math.amount0ForValue(3000e6, u.s);
        uint256 fresh1 = 1000e6;

        V3Math.Jump memory alone = _jump(u.s, sa, sb, fresh0, fresh1);
        V3Math.Jump memory shared = _jump(u.s, sa, sb, fresh0 + ja.left0, fresh1 + ledger1);

        console.log("Ledger entry of token1 after A / after B:", ledger1, shared.left1);
        console.log("B's liquidity alone / with the ledger:", uint256(alone.liquidity), uint256(shared.liquidity));

        assertGt(V3Math.value0(alone.left0, u.s), 1900e6, "alone, B leaves token0: it is short of token1");
        assertGt(shared.liquidity, alone.liquidity, "with the ledger, B mints more");
        assertLe(shared.left0, 1, "B now uses its token0");
        // B needed 2,000 more of token1 and took it from what A left.
        assertApproxEqAbs(ledger1 - shared.left1, 2000e6, 2 * _grain(u.s), "B drew its shortfall from A's leftover");
        assertLt(shared.left1, ledger1, "the ledger entry fell");
    }

    // =========================================================================
    // 8. The mock pool in `src/` and the model used above agree on a burn and on
    //    the liquidity for given amounts.
    // =========================================================================
    function test_mock_poolAgreesWithModel() public {
        MockCLPoolV2 pool = new MockCLPoolV2(BASE_TICK);
        int24[5] memory moves = [int24(-400), int24(-150), int24(0), int24(200), int24(450)];
        int24 lo = _nearest(BASE_TICK - 500);
        int24 hi = _nearest(BASE_TICK + 500);
        for (uint256 i = 0; i < moves.length; i++) {
            pool.movePriceToTick(BASE_TICK + moves[i]);
            uint160 s = _sqrt(BASE_TICK + moves[i]);
            uint128 l = pool.getLiquidityForAmounts(1 ether, 2500e6, lo, hi);
            assertEq(
                uint256(l),
                uint256(V3Math.liquidityForAmounts(s, _sqrt(lo), _sqrt(hi), 1 ether, 2500e6)),
                "liquidity for amounts"
            );
            (uint256 a0, uint256 a1) = pool.getAmountsForLiquidity(l, lo, hi);
            (uint256 m0, uint256 m1) = V3Math.amountsDown(s, _sqrt(lo), _sqrt(hi), l);
            assertEq(a0, m0, "token0 of a burn");
            assertEq(a1, m1, "token1 of a burn");
        }
    }
}
