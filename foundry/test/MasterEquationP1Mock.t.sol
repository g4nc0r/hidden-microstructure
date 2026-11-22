// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Test, console} from "forge-std/Test.sol";
import {MockCLPoolV2} from "../src/MockCLPoolV2.sol";
import {V3Math} from "./helpers/V3Math.sol";

/// @title MasterEquationP1Mock
/// @notice Network-free tests of Proposition 1 (the binding-side criterion) and its two
///         corollaries, the swap-free rule and the swap-corrected rule.
///
/// The pool is the integer model in `helpers/V3Math.sol`, which the fork tests check
/// against two unmodified position managers to the base unit. The statements tested are
/// written in value shares and in the displacement of the price from the old range, and
/// are computed here by their own formulas:
///
///   Proposition 1.  With w_hat the share of token0 in the value offered to the mint and
///     w' the share the new range requires, the leftover is in token1 and worth
///     W (w' - w_hat) / w' if w_hat < w', and in token0 and worth
///     W (w_hat - w') / (1 - w') if w_hat > w'.
///
///   Corollary 1.  Old and new ranges centred in tick space, no swap. With no standing
///     balance the leftover is in token1 after an upward move and in token0 after a
///     downward one, and is the fraction
///         alpha(l) = sinh|l| / (e^h - cosh l)
///     of the withdrawn value V (all of it at or beyond a bound). A standing balance
///     worth less than alpha V leaves the token unchanged whatever its composition; a
///     balance worth alpha V in the binding token removes the leftover; more moves it.
///
///   Corollary 2.  As Corollary 1 with a swap of value (1/2) alpha V (1 + eps) from the
///     surplus token into the binding one. The leftover is worth alpha V |eps|, in the
///     token of Corollary 1 if eps < 0 and in the token the swap bought if eps > 0.
///
/// Every case is deterministic. Amounts are of order 1e21 base units, so integer
/// rounding is below one part in 1e12 and the tolerances are stated at 1e-9 of the
/// value involved.
contract MasterEquationP1Mock is Test {
    MockCLPoolV2 internal tickMath;

    uint256 constant Q96 = 0x1000000000000000000000000;
    uint256 constant Q128 = 1 << 128;

    int24 constant CENTRE = 6000; // old range centred here, in ticks
    int24 constant HALF = 500; // its half-width, in ticks
    uint256 constant SIZE = 1e21; // value of each side at the centre, token1 units

    struct Out {
        uint160 s; // price at the rebalance
        uint256 wd0;
        uint256 wd1;
        uint256 v0; // value of wd0
        uint256 value; // V, withdrawn value
        uint256 alphaV; // alpha(l) V
        bool up; // price above the old centre
    }

    function setUp() public {
        tickMath = new MockCLPoolV2(0);
    }

    function _sqrt(int24 tick) internal view returns (uint160) {
        return tickMath.getSqrtRatioAtTick(tick);
    }

    function _tol(uint256 value) internal pure returns (uint256) {
        return value / 1e9 + 8;
    }

    /// @dev alpha(l) V with l = ln(s / s0) and h = ln(s_b / s0), from
    ///      sinh l = (x - 1/x) / 2 and cosh l = (x + 1/x) / 2 with x = s / s0.
    function _alphaV(uint160 s, uint160 s0, uint160 sbOld, uint256 value, bool outside)
        internal
        pure
        returns (uint256)
    {
        if (outside) return value;
        uint256 x = V3Math.mulDiv(s, Q96, s0);
        uint256 inv = V3Math.mulDiv(s0, Q96, s);
        uint256 eh = V3Math.mulDiv(sbOld, Q96, s0);
        uint256 num = x > inv ? x - inv : inv - x;
        return V3Math.mulDiv(value, num, 2 * eh - x - inv);
    }

    /// @dev The standard position, opened at the centre of [CENTRE - HALF, CENTRE + HALF]
    ///      and withdrawn after the price has moved `d` ticks.
    function _withdrawAt(int24 d) internal view returns (Out memory o) {
        uint160 s0 = _sqrt(CENTRE);
        uint160 sa = _sqrt(CENTRE - HALF);
        uint160 sb = _sqrt(CENTRE + HALF);
        uint128 lOld = V3Math.liquidityForAmounts(s0, sa, sb, V3Math.amount0ForValue(SIZE, s0), SIZE);
        o.s = _sqrt(CENTRE + d);
        (o.wd0, o.wd1) = V3Math.amountsDown(o.s, sa, sb, lOld);
        o.v0 = V3Math.value0(o.wd0, o.s);
        o.value = o.v0 + o.wd1;
        o.up = d > 0;
        o.alphaV = _alphaV(o.s, s0, sb, o.value, d >= HALF || d <= -HALF);
    }

    /// @dev Mint (hat0, hat1) into a range of `half` ticks either side of the price tick,
    ///      and return what is left, in value.
    function _mintCentred(Out memory o, int24 d, int24 half, uint256 hat0, uint256 hat1)
        internal
        view
        returns (uint256 leftValue0, uint256 left1)
    {
        V3Math.Jump memory j = V3Math.mint(o.s, _sqrt(CENTRE + d - half), _sqrt(CENTRE + d + half), hat0, hat1);
        leftValue0 = V3Math.value0(j.left0, o.s);
        left1 = j.left1;
    }

    // =========================================================================
    // Proposition 1 on 400 arbitrary mints: any price, any range about it, any inputs.
    // =========================================================================
    function test_p1_criterion_arbitraryInputs() public view {
        uint256 in0;
        uint256 in1;
        for (uint256 i = 0; i < 400; i++) {
            uint256 r = uint256(keccak256(abi.encode("master-equation-p1", i)));
            int24 tick = int24(int256(r % 40001)) - 20000;
            int24 below = int24(int256((r >> 16) % 3000)) + 10;
            int24 above = int24(int256((r >> 32) % 3000)) + 10;
            uint160 s = _sqrt(tick);
            uint160 sa = _sqrt(tick - below);
            uint160 sb = _sqrt(tick + above);
            uint256 hat1 = 1e18 + (r >> 48) % 1e24;
            uint256 hat0 = V3Math.amount0ForValue(1e18 + (r >> 128) % 1e24, s);

            uint256 v0 = V3Math.value0(hat0, s);
            uint256 w = v0 + hat1;
            (uint256 a, uint256 b) = V3Math.requiredValues(s, sa, sb);
            uint256 shareOffered = V3Math.mulDiv(v0, Q128, w);
            uint256 shareRequired = V3Math.mulDiv(a, Q128, a + b);

            V3Math.Jump memory j = V3Math.mint(s, sa, sb, hat0, hat1);
            uint256 left0 = V3Math.value0(j.left0, s);

            if (shareOffered < shareRequired) {
                uint256 expected = V3Math.mulDiv(w, shareRequired - shareOffered, shareRequired);
                assertApproxEqAbs(j.left1, expected, _tol(w), "leftover in token1: W (w' - w_hat) / w'");
                assertLe(left0, _tol(w), "token0 is used up");
                in1++;
            } else {
                uint256 expected = V3Math.mulDiv(w, shareOffered - shareRequired, Q128 - shareRequired);
                assertApproxEqAbs(left0, expected, _tol(w), "leftover in token0: W (w_hat - w') / (1 - w')");
                assertLe(j.left1, _tol(w), "token1 is used up");
                in0++;
            }
        }
        console.log("Mints leaving token0 / token1:", in0, in1);
        assertGt(in0, 100, "both sides are exercised");
        assertGt(in1, 100, "both sides are exercised");
    }

    // =========================================================================
    // Corollary 1(i): no balance, no swap. The token left follows the direction of the
    // move and its value is alpha(l) V, for any width of the new range.
    // =========================================================================
    function test_p1_cor1_swapFreeRule() public view {
        int24[13] memory moves = [
            int24(-700),
            int24(-500),
            int24(-499),
            int24(-300),
            int24(-100),
            int24(-1),
            int24(0),
            int24(1),
            int24(100),
            int24(300),
            int24(499),
            int24(500),
            int24(700)
        ];
        int24[3] memory widths = [int24(250), int24(500), int24(1200)];
        for (uint256 i = 0; i < moves.length; i++) {
            Out memory o = _withdrawAt(moves[i]);
            for (uint256 k = 0; k < widths.length; k++) {
                (uint256 left0, uint256 left1) = _mintCentred(o, moves[i], widths[k], o.wd0, o.wd1);
                if (moves[i] > 0) {
                    assertApproxEqAbs(left1, o.alphaV, _tol(o.value), "upward move: token1 left, worth alpha V");
                    assertLe(left0, _tol(o.value), "upward move: token0 is used up");
                } else if (moves[i] < 0) {
                    assertApproxEqAbs(left0, o.alphaV, _tol(o.value), "downward move: token0 left, worth alpha V");
                    assertLe(left1, _tol(o.value), "downward move: token1 is used up");
                } else {
                    assertLe(left0 + left1, _tol(o.value), "at the centre nothing is left");
                }
            }
            if (moves[i] == 300) console.log("Move of +300 ticks: withdrawn value / alpha V:", o.value, o.alphaV);
            if (moves[i] == 500) assertEq(o.alphaV, o.value, "at the bound the whole value is left");
        }
    }

    // =========================================================================
    // Corollary 1(ii): a standing balance. Below alpha V the rule holds whatever the
    // balance is made of; at alpha V in the binding token nothing is left; above it
    // the leftover moves to the other token.
    // =========================================================================
    function test_p1_cor1_standingBalanceBound() public view {
        int24[4] memory moves = [int24(-400), int24(-200), int24(200), int24(400)];
        for (uint256 i = 0; i < moves.length; i++) {
            int24 d = moves[i];
            Out memory o = _withdrawAt(d);
            // After an upward move token1 is in surplus and token0 binds.
            for (uint256 mix = 0; mix < 3; mix++) {
                uint256 worth = o.alphaV * 9 / 10;
                uint256 inBinding = mix == 0 ? worth : (mix == 1 ? 0 : worth / 2);
                uint256 inSurplus = worth - inBinding;
                (uint256 left0, uint256 left1) = _withBalance(o, d, inBinding, inSurplus);
                // The balance in the binding token reduces the leftover; the balance in
                // the surplus token adds to it.
                uint256 expected = o.alphaV - inBinding + inSurplus;
                if (o.up) {
                    assertApproxEqAbs(left1, expected, _tol(o.value), "below the bound: token1 is still left");
                    assertLe(left0, _tol(o.value), "below the bound: token0 still binds");
                } else {
                    assertApproxEqAbs(left0, expected, _tol(o.value), "below the bound: token0 is still left");
                    assertLe(left1, _tol(o.value), "below the bound: token1 still binds");
                }
            }
            {
                (uint256 left0, uint256 left1) = _withBalance(o, d, o.alphaV, 0);
                assertLe(left0 + left1, 2 * _tol(o.value), "at the bound nothing is left");
            }
            {
                uint256 worth = o.alphaV * 11 / 10;
                (uint256 left0, uint256 left1) = _withBalance(o, d, worth, 0);
                if (o.up) {
                    assertApproxEqAbs(left0, worth - o.alphaV, _tol(o.value), "above the bound: token0 is left");
                    assertLe(left1, _tol(o.value), "above the bound: token1 binds");
                } else {
                    assertApproxEqAbs(left1, worth - o.alphaV, _tol(o.value), "above the bound: token1 is left");
                    assertLe(left0, _tol(o.value), "above the bound: token0 binds");
                }
            }
        }
    }

    /// @dev Mint with a standing balance given by its value in the binding and in the
    ///      surplus token.
    function _withBalance(Out memory o, int24 d, uint256 inBinding, uint256 inSurplus)
        internal
        view
        returns (uint256 left0, uint256 left1)
    {
        uint256 hat0 = o.wd0 + V3Math.amount0ForValue(o.up ? inBinding : inSurplus, o.s);
        uint256 hat1 = o.wd1 + (o.up ? inSurplus : inBinding);
        return _mintCentred(o, d, 500, hat0, hat1);
    }

    // =========================================================================
    // Corollary 2: a swap of value (1/2) alpha V (1 + eps) from the surplus token into
    // the binding one, at the price, with no fee. The last move is the paper's example:
    // the price at the upper bound, where alpha is one.
    // =========================================================================
    function test_p1_cor2_swapCorrectedRule() public view {
        int24[5] memory moves = [int24(-400), int24(-200), int24(200), int24(400), int24(500)];
        int256[5] memory epsBps = [int256(-5000), int256(-400), int256(0), int256(400), int256(5000)];
        for (uint256 i = 0; i < moves.length; i++) {
            int24 d = moves[i];
            Out memory o = _withdrawAt(d);
            for (uint256 k = 0; k < epsBps.length; k++) {
                uint256 q = o.alphaV * uint256(10000 + epsBps[k]) / 20000;
                uint256 hat0;
                uint256 hat1;
                if (o.up) {
                    hat0 = o.wd0 + V3Math.amount0ForValue(q, o.s);
                    hat1 = o.wd1 - q;
                } else {
                    hat0 = o.wd0 - V3Math.amount0ForValue(q, o.s);
                    hat1 = o.wd1 + q;
                }
                (uint256 left0, uint256 left1) = _mintCentred(o, d, 500, hat0, hat1);
                uint256 size = epsBps[k] >= 0 ? uint256(epsBps[k]) : uint256(-epsBps[k]);
                uint256 expected = o.alphaV * size / 10000;
                // Undershoot leaves the token of Corollary 1; overshoot leaves the token bought.
                bool leftIsToken1 = o.up ? epsBps[k] < 0 : epsBps[k] > 0;
                if (epsBps[k] == 0) {
                    assertLe(left0 + left1, 2 * _tol(o.value), "an exact swap leaves nothing");
                } else if (leftIsToken1) {
                    assertApproxEqAbs(left1, expected, _tol(o.value), "token1 left, worth alpha V |eps|");
                    assertLe(left0, _tol(o.value), "token0 is used up");
                } else {
                    assertApproxEqAbs(left0, expected, _tol(o.value), "token0 left, worth alpha V |eps|");
                    assertLe(left1, _tol(o.value), "token1 is used up");
                }
                if (d == 500 && epsBps[k] == 400) {
                    console.log("Example, swap 4% too large: withdrawn value / value left in token0:", o.value, left0);
                }
                if (d == 500 && epsBps[k] == -400) {
                    console.log("Example, swap 4% too small: withdrawn value / value left in token1:", o.value, left1);
                }
            }
        }
    }
}
