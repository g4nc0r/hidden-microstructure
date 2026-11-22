// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {SlipstreamAdapter} from "./helpers/SlipstreamAdapter.sol";

/// @title MasterEquationT1Fork
/// @notice Theorem 1 (the per-event jump of the dust ledger) against the unmodified
///         Aerodrome Slipstream position manager on Base, at block 43,175,000.
///
/// The unit under test is `ReferencePM`, a wrapper that adds a depositor-keyed ledger
/// shared across pools and leaves every V3 step to the position manager. Each test
/// predicts the liquidity minted and the two ledger entries with Theorem 1, before the
/// transaction where there is no swap and from the swap's own event where there is one,
/// and compares with `assertEq`; the scenarios are in `helpers/ForkScenarios.sol`.
contract MasterEquationT1Fork is SlipstreamAdapter {
    function test_t1_swapfree_predictsDustCredit_slipstream() public {
        _scSwapFree();
    }

    function test_t1_swapCorrected_predictsDustCredit_slipstream() public {
        _scSwapCorrected();
    }

    function test_t1_crossPool_residualAbsorbed_slipstream() public {
        _scCrossPool();
    }

    function test_t1_consecutiveRebalances_predictsAllEvents_slipstream() public {
        _scSequence();
    }
}

/// @title MasterEquationP1Fork
/// @notice Proposition 1 and the swap-corrected rule on the same position manager: a
///         swap short of the amount that would leave nothing leaves the token the
///         position held, and a swap beyond it leaves the token the swap bought.
contract MasterEquationP1Fork is SlipstreamAdapter {
    function test_p1_swapCorrected_residualSign_slipstream() public {
        _scResidualSign();
    }
}

/// @title MasterEquationT2Fork
/// @notice Theorem 2 (per-token conservation across pools without a swap) on the same
///         position manager, with the ledger checked against the tokens held.
contract MasterEquationT2Fork is SlipstreamAdapter {
    function test_t2_conservationAcrossPools_slipstream() public {
        _scConservation();
    }
}
