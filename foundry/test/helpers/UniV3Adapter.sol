// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {ReferencePMUniV3} from "../../src/ReferencePMUniV3.sol";
import {INfpmUniV3, IFactoryUniV3} from "../../src/interfaces/UniswapV3.sol";
import {IUniswapV3Pool} from "../../src/interfaces/Slipstream.sol";
import {ForkScenarios} from "./ForkScenarios.sol";

/// @title UniV3Adapter
/// @notice Runs the fork scenarios against `ReferencePMUniV3` over the unmodified
///         Uniswap V3 position manager on Base. Pools are keyed by fee.
abstract contract UniV3Adapter is ForkScenarios {
    address constant NFPM = 0x03a520b32C04BF3bEEf7BEb72E919cf822Ed34f1;
    address constant FACTORY = 0x33128a8fC17869897dcE68Ed026d694621f6FDfD;

    ReferencePMUniV3 internal pm;

    function setUp() public {
        _setUpFork();
        pm = new ReferencePMUniV3(NFPM, FACTORY);
        _approveAll(address(pm));
    }

    function _pmAddr() internal view override returns (address) {
        return address(pm);
    }

    function _nfpmAddr() internal pure override returns (address) {
        return NFPM;
    }

    /// @dev Fee 500 has tick spacing 10 and fee 3000 has tick spacing 60.
    function _ref(address a, address b, uint24 fee) internal view returns (PoolRef memory p) {
        p.pool = IFactoryUniV3(FACTORY).getPool(a, b, fee);
        if (p.pool == address(0)) return p;
        p.token0 = IUniswapV3Pool(p.pool).token0();
        p.token1 = IUniswapV3Pool(p.pool).token1();
        p.spacing = fee == 500 ? int24(10) : int24(60);
        p.key = fee;
    }

    function _mainPool() internal view override returns (PoolRef memory p) {
        p = _ref(WETH, USDC, 500);
        require(p.pool != address(0), "no WETH/USDC pool at the pin");
    }

    function _secondPool() internal view override returns (PoolRef memory p) {
        p = _ref(WETH, CBBTC, 500);
        if (p.pool == address(0)) p = _ref(WETH, CBBTC, 3000);
        if (p.pool == address(0)) p = _ref(WETH, USDC, 3000);
        require(p.pool != address(0), "no second pool at the pin");
    }

    function _pmMint(PoolRef memory p, int24 lo, int24 hi, uint256 extra0, uint256 extra1)
        internal
        override
        returns (uint256, uint128, uint256, uint256)
    {
        vm.prank(depositor);
        return pm.mint(
            ReferencePMUniV3.MintArgs({
                token0: p.token0,
                token1: p.token1,
                fee: p.key,
                tickLower: lo,
                tickUpper: hi,
                amount0Extra: extra0,
                amount1Extra: extra1
            })
        );
    }

    function _pmRebalance(uint256 id, int24 lo, int24 hi)
        internal
        override
        returns (uint256, uint128, uint256, uint256)
    {
        vm.prank(depositor);
        return pm.rebalance(id, lo, hi);
    }

    function _pmRebalanceWithSwap(uint256 id, int24 lo, int24 hi, uint256 amountIn, bool zeroForOne)
        internal
        override
        returns (uint256, uint128, uint256, uint256)
    {
        vm.prank(depositor);
        return pm.rebalanceWithSwap(id, lo, hi, amountIn, zeroForOne);
    }

    function _pmDust(address token) internal view override returns (uint256) {
        return pm.dustBalance(depositor, token);
    }

    function _pmWithdrawDust(address token, uint256 amount) internal override {
        vm.prank(depositor);
        pm.withdrawDust(token, amount);
    }

    function _positionOf(uint256 id) internal view override returns (int24 lo, int24 hi, uint128 liquidity) {
        (,,,,, lo, hi, liquidity,,,,) = INfpmUniV3(NFPM).positions(id);
    }
}
