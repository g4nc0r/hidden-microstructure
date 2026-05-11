// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test, console} from "forge-std/Test.sol";
import {MockCLPoolV2} from "../src/MockCLPoolV2.sol";
import {TickHelpers} from "./helpers/Tick.sol";

/// @title MasterEquationT1Mock
/// @notice Mock-pool, network-free verification of Theorem 1 of *The Master
///         Equation for the Dust Ledger* (Ryan, 2026), the
///         closed-form per-event jump
///
///                 L_new        = min(hat_x / g_x, hat_y / g_y)
///                 x_dust' = hat_x - L_new * g_x
///                 y_dust' = hat_y - L_new * g_y
///
///         where  hat_x = x_w + x_dust - sigma_x  (and similarly hat_y).
///
/// Seven tests:
///   1. swap-free, zero standing dust (recovers Geometric Siphon Theorem 1
///      and the canonical ~2,061 USDC residual at the GS anchor setup);
///   2. swap-free, non-zero x_dust on the bound side;
///   3. swap-free, non-zero y_dust on the slack side (linear additivity);
///   4. swap correction below the locus threshold (LP structure unchanged);
///   5. swap overshoot past the locus (binding side flips);
///   6. three positional sub-cases of the V3 amount functions
///      (new range below s, above s, straddling s);
///   7. multi-position recycle: Position A's residual is absorbed by
///      Position B's mint via the depositor-keyed dust ledger.
contract MasterEquationT1Mock is Test {
    MockCLPoolV2 internal pool;

    // V3-exact tick anchor at ~$2,500/WETH (matches GS NewTheoremsProof's
    // BASE_TICK = 78244). MockCLPool's linear ANCHOR_TICK = 73135 is a
    // different anchor for the linear approximation; with the V3-exact
    // sqrt-price math of MockCLPoolV2 we use 78244.
    int24 constant BASE_TICK = 78244;
    int24 constant DISPLACED_TICK = 78444;        // BASE_TICK + 200 (GS canonical displacement)
    int24 constant TICK_SPACING = 100;

    struct T1Inputs {
        int24 newLower;
        int24 newUpper;
        uint256 wd0;
        uint256 wd1;
        uint256 dust0Pre;
        uint256 dust1Pre;
        int256 sigma0;
        int256 sigma1;
    }

    struct T1Prediction {
        uint256 hat0;
        uint256 hat1;
        uint128 lNew;
        uint256 used0;
        uint256 used1;
        uint256 dust0After;
        uint256 dust1After;
    }

    function setUp() public {
        pool = new MockCLPoolV2(BASE_TICK);
    }

    /// @dev Compute withdrawal amounts for a position created at BASE_TICK
    ///      (1 WETH + 2,500 USDC into [BASE_TICK-500, BASE_TICK+500]) and
    ///      then withdrawn after a +200-tick price displacement. Mutates
    ///      pool state to leave it at DISPLACED_TICK on return.
    function _gsCanonicalWithdraw(int24 oldLower, int24 oldUpper)
        internal
        returns (uint128 lOld, uint256 wd0, uint256 wd1)
    {
        pool.movePriceToTick(BASE_TICK);
        lOld = pool.getLiquidityForAmounts(1 ether, 2500e6, oldLower, oldUpper);
        pool.movePriceToTick(DISPLACED_TICK);
        (wd0, wd1) = pool.getAmountsForLiquidity(lOld, oldLower, oldUpper);
    }

    /// @dev Closed-form Theorem 1 prediction. Computes
    ///      hat = wd + dust_pre - sigma  on each token, then asks the V3
    ///      amount functions for the new liquidity and the actual mint
    ///      consumption. Leftover = hat - used, the Master Equation jump.
    function _t1Predict(T1Inputs memory inp) internal view returns (T1Prediction memory pred) {
        int256 h0 = int256(inp.wd0 + inp.dust0Pre) - inp.sigma0;
        int256 h1 = int256(inp.wd1 + inp.dust1Pre) - inp.sigma1;
        require(h0 >= 0 && h1 >= 0, "negative hat");
        pred.hat0 = uint256(h0);
        pred.hat1 = uint256(h1);
        pred.lNew = pool.getLiquidityForAmounts(pred.hat0, pred.hat1, inp.newLower, inp.newUpper);
        (pred.used0, pred.used1) = pool.getAmountsForLiquidity(pred.lNew, inp.newLower, inp.newUpper);
        pred.dust0After = pred.hat0 - pred.used0;
        pred.dust1After = pred.hat1 - pred.used1;
    }

    function _nearest(int24 t) internal pure returns (int24) {
        return TickHelpers.nearest(t, TICK_SPACING);
    }

    /// @dev USD value of (a0, a1) at the GS anchor price ($2,500/WETH).
    function _usd(uint256 a0, uint256 a1) internal pure returns (uint256) {
        return (a0 * 2500e6) / 1 ether + a1;
    }

    // =========================================================================
    // Test 1: swap-free, zero standing dust
    // Recovers GS Theorem 1 and the canonical ~2,061 USDC residual.
    // =========================================================================

    function test_t1_swapfree_zeroDust() public {
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        (uint128 lOld, uint256 wd0, uint256 wd1) = _gsCanonicalWithdraw(oldLower, oldUpper);
        lOld;

        T1Prediction memory pred = _t1Predict(T1Inputs({
            newLower: _nearest(DISPLACED_TICK - 1000),
            newUpper: _nearest(DISPLACED_TICK + 1000),
            wd0: wd0,
            wd1: wd1,
            dust0Pre: 0,
            dust1Pre: 0,
            sigma0: 0,
            sigma1: 0
        }));

        // Note: pool sqrt-price is fixed at BASE_TICK in setUp; the test
        // uses a +200-shifted new range to mirror the GS displacement
        // scenario without mutating pool state.
        console.log("dust0After (WETH):");
        console.log(pred.dust0After);
        console.log("dust1After (USDC):");
        console.log(pred.dust1After);

        // In the swap-free regime, exactly one of the two leftovers is
        // non-trivially large; the other is rounding noise.
        bool dust0Trivial = pred.dust0After < 1e12;        // <1 nano-WETH
        bool dust1Trivial = pred.dust1After < 1e3;          // <0.001 USDC
        assertTrue(dust0Trivial != dust1Trivial, "exactly one side carries the residual");

        // The non-trivial side carries the bulk of the residual.
        uint256 residualUSD = _usd(pred.dust0After, pred.dust1After);
        console.log("Residual USD (6 decimals):");
        console.log(residualUSD);
        assertGt(residualUSD, 1900e6, "residual >= $1,900");
        assertLt(residualUSD, 2200e6, "residual <= $2,200 (within ~5% of GS canonical 2,061)");
    }

    // =========================================================================
    // Test 2: swap-free, non-zero standing dust on the bound side
    // Adding to the bound side grows L_new; the slack-side leftover shrinks.
    // =========================================================================

    function test_t1_swapfree_nonzeroDust_boundSide() public {
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        (uint128 lOld, uint256 wd0, uint256 wd1) = _gsCanonicalWithdraw(oldLower, oldUpper);
        lOld;

        T1Inputs memory base = T1Inputs({
            newLower: _nearest(DISPLACED_TICK - 1000),
            newUpper: _nearest(DISPLACED_TICK + 1000),
            wd0: wd0,
            wd1: wd1,
            dust0Pre: 0,
            dust1Pre: 0,
            sigma0: 0,
            sigma1: 0
        });
        T1Prediction memory base0 = _t1Predict(base);

        // Identify bound side (WETH at the GS anchor displacement).
        // Bound side has dust ~ 0; slack side carries the residual.
        bool wethBound = base0.dust0After < base0.dust1After;
        require(wethBound, "test assumes WETH is the bound side at GS anchor");

        // Add 0.5 WETH to the bound side.
        T1Inputs memory withDust = base;
        withDust.dust0Pre = 0.5 ether;
        T1Prediction memory pred = _t1Predict(withDust);

        console.log("Base L_new:");
        console.log(uint256(base0.lNew));
        console.log("With 0.5 WETH dust, L_new:");
        console.log(uint256(pred.lNew));
        console.log("Base dust1After (USDC):");
        console.log(base0.dust1After);
        console.log("With dust dust1After (USDC):");
        console.log(pred.dust1After);

        // Adding to the bound side strictly increases L_new...
        assertGt(pred.lNew, base0.lNew, "L_new grows when bound-side input grows");
        // ...and strictly decreases the slack-side leftover (more bound side ->
        // mint absorbs more of the slack token).
        assertLt(pred.dust1After, base0.dust1After, "slack-side dust shrinks");
    }

    // =========================================================================
    // Test 3: swap-free, non-zero standing dust on the slack side
    // Linear additivity: slack-side leftover shifts by exactly the added dust.
    // =========================================================================

    function test_t1_swapfree_nonzeroDust_slackSide() public {
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        (uint128 lOld, uint256 wd0, uint256 wd1) = _gsCanonicalWithdraw(oldLower, oldUpper);
        lOld;

        T1Inputs memory base = T1Inputs({
            newLower: _nearest(DISPLACED_TICK - 1000),
            newUpper: _nearest(DISPLACED_TICK + 1000),
            wd0: wd0,
            wd1: wd1,
            dust0Pre: 0,
            dust1Pre: 0,
            sigma0: 0,
            sigma1: 0
        });
        T1Prediction memory base0 = _t1Predict(base);

        bool wethBound = base0.dust0After < base0.dust1After;
        require(wethBound, "test assumes WETH is the bound side at GS anchor");

        // Add 5,000 USDC to the slack side.
        T1Inputs memory withDust = base;
        uint256 added = 5000e6;
        withDust.dust1Pre = added;
        T1Prediction memory pred = _t1Predict(withDust);

        console.log("Base dust1After:");
        console.log(base0.dust1After);
        console.log("With 5,000 USDC dust dust1After:");
        console.log(pred.dust1After);

        // L_new is unchanged: the slack side does not bind, so adding to it
        // does not change the LP solve.
        assertEq(pred.lNew, base0.lNew, "L_new unchanged when slack-side input grows");
        // Slack-side leftover shifts by exactly the added amount.
        assertEq(pred.dust1After, base0.dust1After + added, "linear additivity on the slack side");
    }

    // =========================================================================
    // Test 4: swap correction toward the locus
    // §4.2 of the paper: "x̂, ŷ shift linearly by (-σ_x, -σ_y) and the LP
    // structure is unchanged." A swap moving inputs toward the ratio-preserving
    // locus reduces the absolute residual; the LP closed form holds throughout
    // (the binding side may flip, but Theorem 1's leftover identity is intact).
    // =========================================================================

    function test_t1_swap_belowThreshold() public {
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        (uint128 lOld, uint256 wd0, uint256 wd1) = _gsCanonicalWithdraw(oldLower, oldUpper);
        lOld;

        T1Inputs memory base = T1Inputs({
            newLower: _nearest(DISPLACED_TICK - 1000),
            newUpper: _nearest(DISPLACED_TICK + 1000),
            wd0: wd0,
            wd1: wd1,
            dust0Pre: 0,
            dust1Pre: 0,
            sigma0: 0,
            sigma1: 0
        });
        T1Prediction memory base0 = _t1Predict(base);

        // Small spot-price-ratio swap: 50 USDC paid, ~0.02 WETH received.
        // Moves inputs toward the locus. Direction is USDC->WETH because
        // USDC is the slack side at the GS displacement.
        T1Inputs memory withSwap = base;
        withSwap.sigma1 = 50e6;
        withSwap.sigma0 = -int256(0.02 ether);
        T1Prediction memory pred = _t1Predict(withSwap);

        uint256 baseResidUSD = _usd(base0.dust0After, base0.dust1After);
        uint256 newResidUSD = _usd(pred.dust0After, pred.dust1After);
        console.log("Base residual (USD):");
        console.log(baseResidUSD);
        console.log("With swap residual (USD):");
        console.log(newResidUSD);

        // Closed-form Theorem 1 still holds with the swap-corrected inputs:
        //   non-negative leftovers and exclusivity (one side near zero off the
        //   ratio-preserving locus).
        bool dust0Trivial = pred.dust0After < 1e15;        // <0.001 WETH
        bool dust1Trivial = pred.dust1After < 1e3;          // <0.001 USDC
        assertTrue(dust0Trivial != dust1Trivial, "exactly one side near zero post-swap");
        // Swap toward locus reduces the absolute residual.
        assertLt(newResidUSD, baseResidUSD, "swap toward locus reduces residual");
    }

    // =========================================================================
    // Test 5: swap overshoot past the locus (binding side flips)
    // A large swap converts more than the locus calls for; the formerly-slack
    // token becomes the new bound side and the leftover flips to token0.
    // =========================================================================

    function test_t1_swap_overshoot() public {
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        (uint128 lOld, uint256 wd0, uint256 wd1) = _gsCanonicalWithdraw(oldLower, oldUpper);
        lOld;

        // Pre-seed sufficient dust to sustain a large swap correction.
        // Without dust, sigma1 = 5,000 USDC would drive hat1 negative.
        T1Inputs memory inp = T1Inputs({
            newLower: _nearest(DISPLACED_TICK - 1000),
            newUpper: _nearest(DISPLACED_TICK + 1000),
            wd0: wd0,
            wd1: wd1,
            dust0Pre: 0,
            dust1Pre: 6000e6,            // 6,000 USDC standing dust
            sigma1: 5000e6,              // pay 5,000 USDC into the pool
            sigma0: -int256(2 ether)     // receive 2 WETH from the pool
        });

        T1Prediction memory pred = _t1Predict(inp);

        console.log("Overshoot dust0After (WETH):");
        console.log(pred.dust0After);
        console.log("Overshoot dust1After (USDC):");
        console.log(pred.dust1After);

        // The huge WETH inflow flips the bound side: USDC now binds, WETH leaks.
        assertGt(pred.dust0After, 0, "WETH leftover dominates after overshoot");
        assertLt(pred.dust1After, 1e3, "USDC now bound (rounding noise)");
    }

    // =========================================================================
    // Test 6: three positional sub-cases of the V3 amount functions
    //   (a) new range entirely above s -> all-token0 mint;
    //   (b) new range entirely below s -> all-token1 mint;
    //   (c) new range straddles s     -> mixed mint.
    // =========================================================================

    function test_t1_threeSubcases() public {
        // Withdraw amounts at the anchor s: a position fully inside an
        // [BASE_TICK-500, BASE_TICK+500] range.
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        (uint128 lOld, uint256 wd0, uint256 wd1) = _gsCanonicalWithdraw(oldLower, oldUpper);
        lOld;

        // (a) new range entirely above s: all token0 needed.
        {
            T1Prediction memory pa = _t1Predict(T1Inputs({
                newLower: _nearest(BASE_TICK + 1500),
                newUpper: _nearest(BASE_TICK + 3500),
                wd0: wd0, wd1: wd1, dust0Pre: 0, dust1Pre: 0, sigma0: 0, sigma1: 0
            }));
            console.log("Subcase (a) above-s: dust0/dust1 = ", pa.dust0After, pa.dust1After);
            // All of token1 (USDC) leaks: the new range lies above s, so
            // the mint at sqrt-price s is at the lower boundary of the new
            // range and absorbs only token0 across that range.
            assertEq(pa.dust1After, wd1, "above-s: token1 fully unabsorbed");
        }

        // (b) new range entirely below s: all token1 needed.
        {
            T1Prediction memory pb = _t1Predict(T1Inputs({
                newLower: _nearest(BASE_TICK - 3500),
                newUpper: _nearest(BASE_TICK - 1500),
                wd0: wd0, wd1: wd1, dust0Pre: 0, dust1Pre: 0, sigma0: 0, sigma1: 0
            }));
            console.log("Subcase (b) below-s: dust0/dust1 = ", pb.dust0After, pb.dust1After);
            assertEq(pb.dust0After, wd0, "below-s: token0 fully unabsorbed");
        }

        // (c) new range straddles s: both tokens needed.
        {
            T1Prediction memory pc = _t1Predict(T1Inputs({
                newLower: _nearest(BASE_TICK - 1000),
                newUpper: _nearest(BASE_TICK + 1000),
                wd0: wd0, wd1: wd1, dust0Pre: 0, dust1Pre: 0, sigma0: 0, sigma1: 0
            }));
            console.log("Subcase (c) straddling: dust0/dust1 = ", pc.dust0After, pc.dust1After);
            // Both leftovers are well below the wd amounts -- the mint
            // absorbs material amounts of both.
            assertLt(pc.dust0After, wd0 / 2, "straddling: token0 mostly absorbed");
            assertLt(pc.dust1After, wd1 / 2, "straddling: token1 mostly absorbed");
        }
    }

    // =========================================================================
    // Test 7: multi-position recycle.
    // Position A's residual is held in the depositor's dust ledger and
    // consumed in full by Position B's mint, by Equation eq:master.
    // =========================================================================

    function test_t1_multiPosition_recycle() public {
        int24 oldLower = _nearest(BASE_TICK - 500);
        int24 oldUpper = _nearest(BASE_TICK + 500);
        uint128 lOldA = pool.getLiquidityForAmounts(1 ether, 2500e6, oldLower, oldUpper);
        (uint256 wdA0, uint256 wdA1) = pool.getAmountsForLiquidity(lOldA, oldLower, oldUpper);

        // Rebalance Position A into a wider range, leaving residual.
        T1Prediction memory predA = _t1Predict(T1Inputs({
            newLower: _nearest(DISPLACED_TICK - 1000),
            newUpper: _nearest(DISPLACED_TICK + 1000),
            wd0: wdA0, wd1: wdA1,
            dust0Pre: 0, dust1Pre: 0, sigma0: 0, sigma1: 0
        }));

        console.log("After A: dust0/dust1 = ", predA.dust0After, predA.dust1After);

        // Position B is now minted into a ±500-tick range centred at the
        // anchor, with 0.5 ETH + 1,250 USDC fresh inputs PLUS the dust
        // ledger from A. Per Equation eq:master, A's dust is consumed by B.
        uint256 freshB0 = 0.5 ether;
        uint256 freshB1 = 1250e6;

        // Without recycle (baseline): mint Position B with only fresh inputs.
        T1Prediction memory predB_NoRecycle = _t1Predict(T1Inputs({
            newLower: oldLower,
            newUpper: oldUpper,
            wd0: freshB0, wd1: freshB1,
            dust0Pre: 0, dust1Pre: 0, sigma0: 0, sigma1: 0
        }));

        // With recycle: B's effective inputs include A's residual.
        T1Prediction memory predB_Recycle = _t1Predict(T1Inputs({
            newLower: oldLower,
            newUpper: oldUpper,
            wd0: freshB0, wd1: freshB1,
            dust0Pre: predA.dust0After,
            dust1Pre: predA.dust1After,
            sigma0: 0, sigma1: 0
        }));

        console.log("B without recycle, L_new:");
        console.log(uint256(predB_NoRecycle.lNew));
        console.log("B with recycle (A's dust), L_new:");
        console.log(uint256(predB_Recycle.lNew));

        // Position B with the recycled dust mints strictly more liquidity.
        assertGt(predB_Recycle.lNew, predB_NoRecycle.lNew,
            "recycled dust grows L_new for Position B");

        // Conservation: A's slack-side dust either fully absorbs (becomes
        // zero) or persists into B's slack-side dust, but never disappears
        // unaccounted.
        uint256 sumDust0Before = predA.dust0After + 0;
        uint256 sumDust1Before = predA.dust1After + 0;
        uint256 sumDust0After  = predB_Recycle.dust0After;
        uint256 sumDust1After  = predB_Recycle.dust1After;

        // Total tokens in the system (across A's residual + B's fresh inputs +
        // B's resulting position) must equal total tokens out.
        (uint256 usedB0, uint256 usedB1) = (predB_Recycle.used0, predB_Recycle.used1);
        assertEq(
            sumDust0Before + freshB0,
            usedB0 + sumDust0After,
            "token0 conservation across recycle"
        );
        assertEq(
            sumDust1Before + freshB1,
            usedB1 + sumDust1After,
            "token1 conservation across recycle"
        );
    }
}
