// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test, console, Vm} from "forge-std/Test.sol";
import {MockCLPoolV2} from "../../src/MockCLPoolV2.sol";
import {IUniswapV3Pool, IERC20} from "../../src/interfaces/Slipstream.sol";
import {TickHelpers} from "./Tick.sol";
import {V3Math} from "./V3Math.sol";

/// @title ForkScenarios
/// @notice The fork-test scenarios, written once and run against each position manager
///         through a thin adapter (`SlipstreamAdapter`, `UniV3Adapter`).
///
/// The scenarios of Theorem 1 state what the reference manager will mint and leave,
/// and compare with `assertEq`. The statement is Theorem 1: the mint takes
/// the liquidity the scarcer input allows at the price at which it is struck, and what
/// remains of the other token is the new ledger entry. With a swap the inputs are
/// reduced by what the swap paid and the price is the price after the swap, both read
/// from the pool's own Swap event, as they are on chain.
///
/// After every call the ledger is also checked against custody: the manager holds
/// exactly the tokens its ledger says it holds.
abstract contract ForkScenarios is Test {
    address constant WETH = 0x4200000000000000000000000000000000000006;
    address constant USDC = 0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913;
    address constant CBBTC = 0xcbB7C0000aB88B473b1f5aFd9ef808440eed33Bf;
    address constant AERO = 0x940181a94A35A4569E4529A3CDfB74e38FD98631;

    /// 10 March 2026, inside the paper's data window; the pin of the Geometric Siphon suite.
    uint256 constant FORK_BLOCK = 43_175_000;

    bytes32 constant POOL_SWAP_TOPIC = keccak256("Swap(address,address,int256,int256,uint160,uint128,int24)");
    bytes32 constant NFPM_COLLECT_TOPIC = keccak256("Collect(uint256,address,uint256,uint256)");

    struct PoolRef {
        address pool;
        address token0;
        address token1;
        int24 spacing;
        uint24 key; // tick spacing on Slipstream, fee on Uniswap V3
    }

    struct Held {
        PoolRef p;
        uint256 id;
    }

    /// V3 TickMath, used for tick-to-price only.
    MockCLPoolV2 internal tickMath;
    address internal depositor = makeAddr("depositor");

    // -------------------------------------------------------------------------
    // Adapter hooks
    // -------------------------------------------------------------------------

    function _pmAddr() internal view virtual returns (address);
    function _nfpmAddr() internal view virtual returns (address);
    function _mainPool() internal view virtual returns (PoolRef memory);
    function _secondPool() internal view virtual returns (PoolRef memory);
    function _pmMint(PoolRef memory p, int24 lo, int24 hi, uint256 extra0, uint256 extra1)
        internal
        virtual
        returns (uint256 id, uint128 liquidity, uint256 left0, uint256 left1);
    function _pmRebalance(uint256 id, int24 lo, int24 hi)
        internal
        virtual
        returns (uint256 newId, uint128 liquidity, uint256 left0, uint256 left1);
    function _pmRebalanceWithSwap(uint256 id, int24 lo, int24 hi, uint256 amountIn, bool zeroForOne)
        internal
        virtual
        returns (uint256 newId, uint128 liquidity, uint256 left0, uint256 left1);
    function _pmDust(address token) internal view virtual returns (uint256);
    function _pmWithdrawDust(address token, uint256 amount) internal virtual;
    function _positionOf(uint256 id) internal view virtual returns (int24 lo, int24 hi, uint128 liquidity);

    // -------------------------------------------------------------------------
    // Set-up and small helpers
    // -------------------------------------------------------------------------

    function _setUpFork() internal {
        vm.createSelectFork("base", FORK_BLOCK);
        tickMath = new MockCLPoolV2(0);
        deal(WETH, depositor, 100 ether);
        deal(USDC, depositor, 250000e6);
        deal(CBBTC, depositor, 10e8);
        deal(AERO, depositor, 100000e18);
    }

    function _approveAll(address spender) internal {
        vm.startPrank(depositor);
        IERC20(WETH).approve(spender, type(uint256).max);
        IERC20(USDC).approve(spender, type(uint256).max);
        IERC20(CBBTC).approve(spender, type(uint256).max);
        IERC20(AERO).approve(spender, type(uint256).max);
        vm.stopPrank();
    }

    function _sqrt(int24 tick) internal view returns (uint160) {
        return tickMath.getSqrtRatioAtTick(tick);
    }

    function _slot0(PoolRef memory p) internal view returns (uint160 s, int24 t) {
        (s, t) = IUniswapV3Pool(p.pool).slot0();
    }

    function _nearest(int24 t, int24 spacing) internal pure returns (int24) {
        return TickHelpers.nearest(t, spacing);
    }

    /// @dev Theorem 1 at sqrt price `s` for a mint offered (hat0, hat1) into [lo, hi].
    function _predict(uint160 s, int24 lo, int24 hi, uint256 hat0, uint256 hat1)
        internal
        view
        returns (V3Math.Jump memory)
    {
        return V3Math.mint(s, _sqrt(lo), _sqrt(hi), hat0, hat1);
    }

    function _burnAmounts(PoolRef memory p, uint256 id) internal view returns (uint256 a0, uint256 a1) {
        (int24 lo, int24 hi, uint128 liq) = _positionOf(id);
        (uint160 s,) = _slot0(p);
        (a0, a1) = V3Math.amountsDown(s, _sqrt(lo), _sqrt(hi), liq);
    }

    /// @dev The ledger is backed to the base unit: with one depositor, the manager's
    ///      balance of each token equals that depositor's ledger entry.
    function _assertBacked() internal view {
        address[4] memory toks = [WETH, USDC, CBBTC, AERO];
        for (uint256 i = 0; i < toks.length; i++) {
            assertEq(IERC20(toks[i]).balanceOf(_pmAddr()), _pmDust(toks[i]), "ledger entry equals tokens held");
        }
    }

    function _assertJump(V3Math.Jump memory j, uint128 liquidity, uint256 left0, uint256 left1) internal pure {
        assertEq(uint256(liquidity), uint256(j.liquidity), "liquidity: Theorem 1 (eq:lnew)");
        assertEq(left0, j.left0, "token0 left: Theorem 1 (eq:newdust)");
        assertEq(left1, j.left1, "token1 left: Theorem 1 (eq:newdust)");
    }

    /// @dev Open a position and check the opening mint against Theorem 1 as well.
    function _open(PoolRef memory p, int24 lo, int24 hi, uint256 extra0, uint256 extra1)
        internal
        returns (uint256 id, uint128 liquidity)
    {
        (uint160 s,) = _slot0(p);
        V3Math.Jump memory j = _predict(s, lo, hi, extra0 + _pmDust(p.token0), extra1 + _pmDust(p.token1));
        uint256 l0;
        uint256 l1;
        (id, liquidity, l0, l1) = _pmMint(p, lo, hi, extra0, extra1);
        _assertJump(j, liquidity, l0, l1);
        _assertBacked();
    }

    function _emptyLedger(PoolRef memory p) internal {
        uint256 d0 = _pmDust(p.token0);
        uint256 d1 = _pmDust(p.token1);
        if (d0 > 0) _pmWithdrawDust(p.token0, d0);
        if (d1 > 0) _pmWithdrawDust(p.token1, d1);
        _assertBacked();
    }

    struct Observed {
        int256 swap0; // pool frame: positive is what the manager paid in
        int256 swap1;
        uint160 sqrtPriceAfter;
        uint256 collected0;
        uint256 collected1;
        bool swapSeen;
        bool collectSeen;
    }

    /// @dev Read the pool's Swap event and the position manager's Collect event from the
    ///      logs of the last call.
    function _observe(PoolRef memory p) internal view returns (Observed memory o) {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        for (uint256 i = 0; i < logs.length; i++) {
            if (logs[i].topics.length == 0) continue;
            if (logs[i].emitter == p.pool && logs[i].topics[0] == POOL_SWAP_TOPIC) {
                (o.swap0, o.swap1, o.sqrtPriceAfter,,) =
                    abi.decode(logs[i].data, (int256, int256, uint160, uint128, int24));
                o.swapSeen = true;
            } else if (logs[i].emitter == _nfpmAddr() && logs[i].topics[0] == NFPM_COLLECT_TOPIC) {
                (, o.collected0, o.collected1) = abi.decode(logs[i].data, (address, uint256, uint256));
                o.collectSeen = true;
            }
        }
    }

    // -------------------------------------------------------------------------
    // Theorem 1
    // -------------------------------------------------------------------------

    /// Scenario 1. One rebalance without a swap, with a standing balance from the opening mint.
    function _scSwapFree() internal {
        PoolRef memory p = _mainPool();
        (uint160 s, int24 t) = _slot0(p);
        int24 lo1 = _nearest(t - 500, p.spacing);
        int24 hi1 = _nearest(t + 500, p.spacing);
        (uint256 id, uint128 lOld) = _open(p, lo1, hi1, 1 ether, 2500e6);

        int24 lo2 = _nearest(t - 1500, p.spacing);
        int24 hi2 = _nearest(t + 1500, p.spacing);
        (uint256 wd0, uint256 wd1) = V3Math.amountsDown(s, _sqrt(lo1), _sqrt(hi1), lOld);
        V3Math.Jump memory j = _predict(s, lo2, hi2, wd0 + _pmDust(p.token0), wd1 + _pmDust(p.token1));

        (, uint128 lNew, uint256 l0, uint256 l1) = _pmRebalance(id, lo2, hi2);

        console.log("swap-free: liquidity predicted / actual", uint256(j.liquidity), uint256(lNew));
        console.log("swap-free: token0 left predicted / actual", j.left0, l0);
        console.log("swap-free: token1 left predicted / actual", j.left1, l1);
        _assertJump(j, lNew, l0, l1);
        _assertBacked();
    }

    /// Scenario 2. One rebalance with an in-pool swap and a standing balance. The old range
    /// sits below the price, and the opening mint has left token0 in the ledger, so the
    /// manager sells token0. The size of the swap is arbitrary here (scenario 5 sizes it).
    /// Inputs to the mint are the amounts withdrawn, the standing balance and the swap's
    /// two legs, and the price is the price the swap left.
    function _scSwapCorrected() internal {
        PoolRef memory p = _mainPool();
        (uint160 s, int24 t) = _slot0(p);
        int24 c0 = _nearest(t - 300, p.spacing);
        int24 lo1 = c0 - 500;
        int24 hi1 = c0 + 500;
        (uint256 id, uint128 lOld) = _open(p, lo1, hi1, 1 ether, 2500e6);

        int24 lo2 = _nearest(t - 1000, p.spacing);
        int24 hi2 = _nearest(t + 1000, p.spacing);
        (uint256 wd0, uint256 wd1) = V3Math.amountsDown(s, _sqrt(lo1), _sqrt(hi1), lOld);
        uint256 pre0 = _pmDust(p.token0);
        uint256 pre1 = _pmDust(p.token1);

        vm.recordLogs();
        assertGt(pre0, 0.05 ether, "the opening mint left token0 in the ledger");
        (, uint128 lNew, uint256 l0, uint256 l1) = _pmRebalanceWithSwap(id, lo2, hi2, 0.05 ether, true);
        Observed memory o = _observe(p);

        assertTrue(o.swapSeen && o.collectSeen, "swap and collect events present");
        assertEq(o.collected0, wd0, "token0 withdrawn: burn at the price before the swap");
        assertEq(o.collected1, wd1, "token1 withdrawn: burn at the price before the swap");
        assertEq(o.swap0, int256(0.05 ether), "the swap paid in what was asked");
        assertLt(o.swap1, 0, "the swap returned token1");
        assertLt(o.sqrtPriceAfter, s, "the swap moved the price");

        uint256 hat0 = uint256(int256(wd0 + pre0) - o.swap0);
        uint256 hat1 = uint256(int256(wd1 + pre1) - o.swap1);
        V3Math.Jump memory j = _predict(o.sqrtPriceAfter, lo2, hi2, hat0, hat1);

        console.log("swap-corrected: sqrt price before / after", uint256(s), uint256(o.sqrtPriceAfter));
        console.log("swap-corrected: liquidity predicted / actual", uint256(j.liquidity), uint256(lNew));
        console.log("swap-corrected: token0 left predicted / actual", j.left0, l0);
        console.log("swap-corrected: token1 left predicted / actual", j.left1, l1);
        _assertJump(j, lNew, l0, l1);
        _assertBacked();
    }

    /// Scenario 3. A leftover from one pool is drawn into a mint in another pool that
    /// shares the token. Position A leaves WETH; position B, in a second pool, is opened
    /// with its other token only and takes its WETH from the ledger.
    function _scCrossPool() internal {
        PoolRef memory pa = _mainPool();
        (, int24 ta) = _slot0(pa);
        (uint256 idA,) = _open(pa, _nearest(ta - 500, pa.spacing), _nearest(ta + 500, pa.spacing), 1 ether, 2500e6);

        // Move A to a range that sits low about the price: it needs less WETH than A holds.
        {
            int24 lo = _nearest(ta - 900, pa.spacing);
            int24 hi = _nearest(ta + 300, pa.spacing);
            (uint160 s,) = _slot0(pa);
            (uint256 wd0, uint256 wd1) = _burnAmounts(pa, idA);
            V3Math.Jump memory ja = _predict(s, lo, hi, wd0 + _pmDust(pa.token0), wd1 + _pmDust(pa.token1));
            (, uint128 lA, uint256 a0, uint256 a1) = _pmRebalance(idA, lo, hi);
            _assertJump(ja, lA, a0, a1);
            _assertBacked();
        }
        uint256 wethBefore = _pmDust(WETH);
        assertGt(wethBefore, 0.01 ether, "position A left WETH in the ledger");

        PoolRef memory pb = _secondPool();
        (uint160 sb_, int24 tb) = _slot0(pb);
        int24 loB = _nearest(tb - 1000, pb.spacing);
        int24 hiB = _nearest(tb + 1000, pb.spacing);
        address other = pb.token0 == WETH ? pb.token1 : pb.token0;
        uint256 otherExtra = other == CBBTC ? 0.05e8 : (other == AERO ? 2000e18 : 2500e6);
        uint256 extra0 = pb.token0 == WETH ? 0 : otherExtra;
        uint256 extra1 = pb.token0 == WETH ? otherExtra : 0;

        V3Math.Jump memory j =
            _predict(sb_, loB, hiB, extra0 + _pmDust(pb.token0), extra1 + _pmDust(pb.token1));
        (, uint128 lB, uint256 l0, uint256 l1) = _pmMint(pb, loB, hiB, extra0, extra1);
        uint256 wethAfter = _pmDust(WETH);

        console.log("cross-pool: WETH in the ledger before / after B's mint", wethBefore, wethAfter);
        console.log("cross-pool: WETH left predicted", pb.token0 == WETH ? j.left0 : j.left1);
        console.log("cross-pool: liquidity of B predicted / actual", uint256(j.liquidity), uint256(lB));
        _assertJump(j, lB, l0, l1);
        assertEq(wethAfter, pb.token0 == WETH ? j.left0 : j.left1, "ledger entry of the shared token");
        assertGt(uint256(lB), 0, "B minted from the ledger's WETH");
        assertLt(wethAfter, wethBefore, "B's mint drew on what A left");
        _assertBacked();
    }

    /// Scenario 4. Three rebalances in a row, the ledger carried from each to the next.
    function _scSequence() internal {
        PoolRef memory p = _mainPool();
        (uint160 s, int24 t) = _slot0(p);
        (uint256 id,) = _open(p, _nearest(t - 500, p.spacing), _nearest(t + 500, p.spacing), 1 ether, 2500e6);

        int24[3] memory halfWidths = [int24(1000), int24(800), int24(1500)];
        for (uint256 i = 0; i < halfWidths.length; i++) {
            (uint256 wd0, uint256 wd1) = _burnAmounts(p, id);
            int24 lo = _nearest(t - halfWidths[i], p.spacing);
            int24 hi = _nearest(t + halfWidths[i], p.spacing);
            V3Math.Jump memory j = _predict(s, lo, hi, wd0 + _pmDust(p.token0), wd1 + _pmDust(p.token1));
            (uint256 newId, uint128 lNew, uint256 l0, uint256 l1) = _pmRebalance(id, lo, hi);
            id = newId;
            console.log("sequence event", i);
            console.log("  token0 left predicted / actual", j.left0, l0);
            console.log("  token1 left predicted / actual", j.left1, l1);
            _assertJump(j, lNew, l0, l1);
            _assertBacked();
        }
    }

    // -------------------------------------------------------------------------
    // Proposition 1 and the swap-corrected rule
    // -------------------------------------------------------------------------

    /// Scenario 5. Which token a swap-corrected rebalance leaves. The old range sits below
    /// the price and the ledger is empty, so without a swap the position would leave
    /// token1, the token it came out long. From the same state the manager sells first
    /// nine tenths and then eleven tenths of the amount that would leave nothing. The
    /// first leaves token1, the second leaves token0, the token the swap bought, and the
    /// value left is the shortfall or excess of the swap divided by the share the new
    /// range requires of the token used up (Proposition 1; Corollary 2 for a centred range).
    function _scResidualSign() internal {
        PoolRef memory p = _mainPool();
        (uint160 s, int24 t) = _slot0(p);
        int24 c0 = _nearest(t - 300, p.spacing);
        (uint256 id, uint128 lOld) = _open(p, c0 - 500, c0 + 500, 1 ether, 2500e6);
        _emptyLedger(p);

        int24 lo2 = _nearest(t - 1000, p.spacing);
        int24 hi2 = _nearest(t + 1000, p.spacing);
        (uint256 wd0, uint256 wd1) = V3Math.amountsDown(s, _sqrt(c0 - 500), _sqrt(c0 + 500), lOld);
        uint256 v0 = V3Math.value0(wd0, s);
        uint256 value = v0 + wd1;
        (uint256 a, uint256 b) = V3Math.requiredValues(s, _sqrt(lo2), _sqrt(hi2));
        uint256 need0 = V3Math.mulDiv(value, a, a + b);
        assertGt(need0, v0, "the position came out long token1");
        uint256 perfect = need0 - v0; // token1 to sell, before fee and price impact

        // Without a swap the mint would leave token1 (Proposition 1, with the share of
        // token0 offered below the share required).
        V3Math.Jump memory free = _predict(s, lo2, hi2, wd0, wd1);
        assertGt(free.left1, 0, "swap-free: token1 is left");
        assertLe(V3Math.value0(free.left0, s), 1, "swap-free: token0 is used up");

        uint256 snap = vm.snapshotState();

        // A swap short of the exact amount.
        (,, uint256 u0, uint256 u1) = _pmRebalanceWithSwap(id, lo2, hi2, perfect * 9 / 10, false);
        uint256 shortBy = perfect / 10;
        uint256 expectU = V3Math.mulDiv(shortBy, a + b, a);
        console.log("undershoot: token0 / token1 left", u0, u1);
        console.log("undershoot: value left, and shortfall over the required share", u1, expectU);
        assertLe(V3Math.value0(u0, s), 1, "undershoot: token0 is used up");
        assertApproxEqRel(u1, expectU, 0.03e18, "undershoot: token1 left, the token the position held");
        _assertBacked();

        vm.revertToState(snap);

        // A swap beyond it.
        (,, uint256 o0, uint256 o1) = _pmRebalanceWithSwap(id, lo2, hi2, perfect * 11 / 10, false);
        uint256 expectO = V3Math.mulDiv(shortBy, a + b, b);
        uint256 valueO = V3Math.value0(o0, s);
        console.log("overshoot: token0 / token1 left", o0, o1);
        console.log("overshoot: value left, and excess over the required share", valueO, expectO);
        assertLe(o1, 1, "overshoot: token1 is used up");
        assertApproxEqRel(valueO, expectO, 0.03e18, "overshoot: token0 left, the token the swap bought");
        _assertBacked();
    }

    // -------------------------------------------------------------------------
    // Theorem 2
    // -------------------------------------------------------------------------

    function _total(Held[2] memory h, address token) internal view returns (uint256 m) {
        m = _pmDust(token);
        for (uint256 k = 0; k < 2; k++) {
            (uint256 a0, uint256 a1) = _burnAmounts(h[k].p, h[k].id);
            if (h[k].p.token0 == token) m += a0;
            if (h[k].p.token1 == token) m += a1;
        }
    }

    /// Scenario 6. Two positions in two pools that share a token, eight rebalances without
    /// a swap. For each token, the amount the positions would return at their pools'
    /// prices plus the ledger entry is unchanged by a rebalance, except for the base unit
    /// the pool keeps when it rounds a mint up. A token outside the rebalanced pool does
    /// not move at all. The ledger equals custody throughout.
    function _scConservation() internal {
        Held[2] memory h;
        h[0].p = _mainPool();
        h[1].p = _secondPool();
        (, int24 ta) = _slot0(h[0].p);
        (, int24 tb) = _slot0(h[1].p);
        (h[0].id,) =
            _open(h[0].p, _nearest(ta - 500, h[0].p.spacing), _nearest(ta + 500, h[0].p.spacing), 1 ether, 2500e6);
        {
            address other = h[1].p.token0 == WETH ? h[1].p.token1 : h[1].p.token0;
            uint256 otherExtra = other == CBBTC ? 0.02e8 : (other == AERO ? 1000e18 : 1250e6);
            (h[1].id,) = _open(
                h[1].p,
                _nearest(tb - 1000, h[1].p.spacing),
                _nearest(tb + 1000, h[1].p.spacing),
                h[1].p.token0 == WETH ? 0.5 ether : otherExtra,
                h[1].p.token0 == WETH ? otherExtra : 0.5 ether
            );
        }

        address[4] memory toks = [WETH, USDC, CBBTC, AERO];
        uint256[4] memory start;
        for (uint256 i = 0; i < 4; i++) start[i] = _total(h, toks[i]);

        // (position, offset of the new centre from the pool's tick, half-width), in ticks.
        int24[3][8] memory plan = [
            [int24(0), int24(-400), int24(800)],
            [int24(1), int24(600), int24(1400)],
            [int24(0), int24(300), int24(1000)],
            [int24(1), int24(-800), int24(1200)],
            [int24(0), int24(0), int24(1600)],
            [int24(1), int24(0), int24(2000)],
            [int24(0), int24(-700), int24(900)],
            [int24(1), int24(400), int24(1000)]
        ];

        uint256 maxLoss;
        for (uint256 e = 0; e < plan.length; e++) {
            uint256 k = uint256(uint24(plan[e][0]));
            PoolRef memory p = h[k].p;
            (, int24 t) = _slot0(p);
            uint256[4] memory before;
            for (uint256 i = 0; i < 4; i++) before[i] = _total(h, toks[i]);

            (h[k].id,,,) = _pmRebalance(
                h[k].id,
                _nearest(t + plan[e][1] - plan[e][2], p.spacing),
                _nearest(t + plan[e][1] + plan[e][2], p.spacing)
            );
            _assertBacked();

            for (uint256 i = 0; i < 4; i++) {
                uint256 afterTotal = _total(h, toks[i]);
                if (toks[i] == p.token0 || toks[i] == p.token1) {
                    assertLe(afterTotal, before[i], "a rebalance creates no token");
                    assertLe(before[i] - afterTotal, 1, "at most the pool's rounding unit leaves the total");
                    if (before[i] - afterTotal > maxLoss) maxLoss = before[i] - afterTotal;
                } else {
                    assertEq(afterTotal, before[i], "a token outside the pool does not move");
                }
            }
        }

        string[4] memory names = ["WETH", "USDC", "cbBTC", "AERO"];
        for (uint256 i = 0; i < 4; i++) {
            uint256 end = _total(h, toks[i]);
            if (start[i] > 0) {
                console.log(
                    string.concat("conservation: ", names[i], " total at start / after eight rebalances"),
                    start[i],
                    end
                );
            }
            assertLe(start[i] - end, plan.length, "total over the run");
        }
        console.log("conservation: largest change at one rebalance, base units", maxLoss);
    }
}
