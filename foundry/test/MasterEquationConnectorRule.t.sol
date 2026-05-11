// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test, console} from "forge-std/Test.sol";
import {MockCLPool} from "../src/MockCLPool.sol";
import {TickHelpers} from "./helpers/Tick.sol";

/// @title MasterEquationConnectorRule
/// @notice Mock-pool, network-free verification of Proposition 1 of *The
///         Master Equation for the Dust Ledger* (Ryan, 2026):
///         the per-pool sign-keyed correlation between signed sqrt-price
///         displacement and signed connector-side dust.
///
/// The proposition predicts a deterministic correlation sign:
///   - Connector token T* at the T0 position  ⇒  correlation > 0
///   - Connector token T* at the T1 position  ⇒  correlation < 0
///
/// where the "signed connector-side dust quantity" at a rebalance is
///   (dust on non-connector side) − (dust on connector's side)
/// and "signed sqrt-price displacement" is the per-event tick change
/// driving the rebalance.
///
/// Foundry implementation: drive K rebalances with i.i.d. ±300-tick
/// displacements (deterministic PRNG); record per-event
/// sign(displacement) × sign(connector-side dust); the running sum is
/// the Spearman-equivalent under symmetric sign data, and its sign
/// matches the proposition's prediction. The mechanism is structural in
/// the V3 amount equations and does not depend on which mock-pool tick
/// math is used; we use the linear MockCLPool here for symmetry with
/// the conservation test.
contract MasterEquationConnectorRule is Test {
    MockCLPool internal pool;

    int24 constant INIT_TICK = 73135;
    int24 constant TICK_SPACING = 100;
    int24 constant RANGE_HALF = 1000;
    // Balanced V3-locus inputs at the linear MockCLPool's ±1000-tick range
    // around INIT_TICK. With these inputs the initial mint absorbs both
    // sides essentially fully, so standing dust starts near zero and
    // per-event dust dynamics dominate the signed_dust signal.
    uint256 constant A0_LOCUS = 1.51e8;          // ~0.151 micro-WETH
    uint256 constant A1_LOCUS = 2500e6;          // 2,500 USDC

    function setUp() public {
        pool = new MockCLPool(0);
        pool.movePriceToTick(INIT_TICK);
    }

    function _nearest(int24 t) internal pure returns (int24) {
        return TickHelpers.nearest(t, TICK_SPACING);
    }

    /// @dev Run K rebalance events with random signed displacement at each
    ///      step. Returns sum_i sign(δ_i) × sign(signed_dust_i).
    /// @param connectorAtT0 if true, T* sits at the T0 position; otherwise T1
    function _runConnectorEvents(bool connectorAtT0, uint256 k, bytes32 seed)
        internal
        returns (int256 sumSignProducts, uint256 evaluatedEvents)
    {
        // Initial position centred at INIT_TICK with V3-locus-balanced inputs
        // so initial standing dust is negligible.
        int24 lo = _nearest(INIT_TICK - RANGE_HALF);
        int24 hi = _nearest(INIT_TICK + RANGE_HALF);
        uint128 liquidity = pool.getLiquidityForAmounts(A0_LOCUS, A1_LOCUS, lo, hi);
        (uint256 used0, uint256 used1) = pool.getAmountsForLiquidity(liquidity, lo, hi);
        uint256 dust0 = A0_LOCUS - used0;
        uint256 dust1 = A1_LOCUS - used1;

        for (uint256 i = 0; i < k; i++) {
            bytes32 h = keccak256(abi.encode(seed, i));
            uint256 hu = uint256(h);

            // Signed displacement in ±300 ticks (step = 100).
            int256 mag = int256(hu % 4 + 1) * 100;     // 100, 200, 300, 400
            bool positive = ((hu >> 8) & 1) == 0;
            int256 displacement = positive ? mag : -mag;

            int24 newTick = pool.tick() + int24(displacement);
            pool.movePriceToTick(newTick);

            // Rebalance to a range centred on the new tick.
            (uint256 wd0, uint256 wd1) = pool.getAmountsForLiquidity(liquidity, lo, hi);
            uint256 hat0 = wd0 + dust0;
            uint256 hat1 = wd1 + dust1;
            int24 newLo = _nearest(newTick - RANGE_HALF);
            int24 newHi = _nearest(newTick + RANGE_HALF);
            uint128 lNew = pool.getLiquidityForAmounts(hat0, hat1, newLo, newHi);
            (uint256 u0, uint256 u1) = pool.getAmountsForLiquidity(lNew, newLo, newHi);
            uint256 newDust0 = hat0 - u0;
            uint256 newDust1 = hat1 - u1;

            // Signed connector-side dust = (non-connector dust) − (connector dust).
            int256 signedDust = connectorAtT0
                ? (int256(newDust1) - int256(newDust0))
                : (int256(newDust0) - int256(newDust1));

            int256 dispSign = displacement > 0 ? int256(1) : int256(-1);
            int256 dustSign;
            if (signedDust > 0) dustSign = 1;
            else if (signedDust < 0) dustSign = -1;
            else dustSign = 0;                     // measure-zero locus event; skip

            if (dustSign != 0) {
                sumSignProducts += dispSign * dustSign;
                evaluatedEvents++;
            }

            // Carry state into next event.
            liquidity = lNew;
            lo = newLo;
            hi = newHi;
            dust0 = newDust0;
            dust1 = newDust1;
        }
    }

    // =========================================================================
    // Proposition 1 Test 1: connector at T0 ⇒ positive correlation.
    // The proposition's magnitude bound is the variance share of the
    // connector-shared component in the per-pool displacement decomposition;
    // our single-pool mock has no shared component (single source of
    // displacement), so we verify the sign claim only — the mechanism that
    // makes the production-data correlation strongly negative or positive.
    // =========================================================================
    function test_prop1_connectorAtT0_positiveCorrelation() public {
        (int256 sumSign, uint256 nEvents) = _runConnectorEvents(true, 80, keccak256("prop1-T0"));
        console.log("Sum sign products (T* at T0):");
        console.logInt(sumSign);
        console.log("Evaluated events:");
        console.log(nEvents);
        assertGt(sumSign, 0, "T* at T0: positive sign correlation between displacement and signed connector-side dust");
    }

    // =========================================================================
    // Proposition 1 Test 2: connector at T1 ⇒ negative correlation.
    // Recovers the GS sign of the original Connector Rule observation,
    // whose sample was T1-only connectors (10 per-pool Spearman correlations
    // in the range −0.56 to −0.98).
    // =========================================================================
    function test_prop1_connectorAtT1_negativeCorrelation() public {
        (int256 sumSign, uint256 nEvents) = _runConnectorEvents(false, 80, keccak256("prop1-T1"));
        console.log("Sum sign products (T* at T1):");
        console.logInt(sumSign);
        console.log("Evaluated events:");
        console.log(nEvents);
        assertLt(sumSign, 0, "T* at T1: negative sign correlation");
    }
}
