// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {UniV3Adapter} from "./helpers/UniV3Adapter.sol";

/// @title MasterEquationT1ForkUniV3
/// @notice Theorem 1 against the unmodified Uniswap V3 position manager on Base, at
///         block 43,175,000. The same scenarios as `MasterEquationT1Fork`, through
///         `ReferencePMUniV3`; the two managers differ in how a pool is keyed (fee
///         here, tick spacing on Slipstream) and in nothing the theorem uses.
contract MasterEquationT1ForkUniV3 is UniV3Adapter {
    function test_t1_swapfree_predictsDustCredit_uniV3() public {
        _scSwapFree();
    }

    function test_t1_swapCorrected_predictsDustCredit_uniV3() public {
        _scSwapCorrected();
    }

    function test_t1_crossPool_residualAbsorbed_uniV3() public {
        _scCrossPool();
    }

    function test_t1_consecutiveRebalances_predictsAllEvents_uniV3() public {
        _scSequence();
    }
}

/// @title MasterEquationP1ForkUniV3
/// @notice Proposition 1 and the swap-corrected rule on Uniswap V3.
contract MasterEquationP1ForkUniV3 is UniV3Adapter {
    function test_p1_swapCorrected_residualSign_uniV3() public {
        _scResidualSign();
    }
}

/// @title MasterEquationT2ForkUniV3
/// @notice Theorem 2 on Uniswap V3.
contract MasterEquationT2ForkUniV3 is UniV3Adapter {
    function test_t2_conservationAcrossPools_uniV3() public {
        _scConservation();
    }
}
