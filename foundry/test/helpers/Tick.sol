// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @title TickHelpers
/// @notice Shared tick-rounding helper used by every test contract in this suite.
library TickHelpers {
    /// @notice Round `tick` down to the nearest multiple of `spacing`,
    ///         consistent with Uniswap V3 / Aerodrome Slipstream conventions.
    function nearest(int24 tick, int24 spacing) internal pure returns (int24) {
        int24 compressed = tick / spacing;
        if (tick < 0 && tick % spacing != 0) compressed--;
        return compressed * spacing;
    }
}
