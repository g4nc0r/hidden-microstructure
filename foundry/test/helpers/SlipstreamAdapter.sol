// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {ReferencePM} from "../../src/ReferencePM.sol";
import {
    INonfungiblePositionManager,
    IUniswapV3Pool,
    IUniswapV3Factory
} from "../../src/interfaces/Slipstream.sol";
import {ForkScenarios} from "./ForkScenarios.sol";

/// @title SlipstreamAdapter
/// @notice Runs the fork scenarios against `ReferencePM` over the unmodified Aerodrome
///         Slipstream position manager on Base. Pools are keyed by tick spacing.
abstract contract SlipstreamAdapter is ForkScenarios {
    address constant NFPM = 0x827922686190790b37229fd06084350E74485b72;
    address constant FACTORY = 0x5e7BB104d84c7CB9B682AaC2F3d509f5F406809A;

    ReferencePM internal pm;

    function setUp() public {
        _setUpFork();
        pm = new ReferencePM(NFPM, FACTORY);
        _approveAll(address(pm));
    }

    function _pmAddr() internal view override returns (address) {
        return address(pm);
    }

    function _nfpmAddr() internal pure override returns (address) {
        return NFPM;
    }

    function _ref(address a, address b, int24 spacing) internal view returns (PoolRef memory p) {
        p.pool = IUniswapV3Factory(FACTORY).getPool(a, b, spacing);
        if (p.pool == address(0)) return p;
        p.token0 = IUniswapV3Pool(p.pool).token0();
        p.token1 = IUniswapV3Pool(p.pool).token1();
        p.spacing = spacing;
        p.key = uint24(spacing);
    }

    function _mainPool() internal view override returns (PoolRef memory p) {
        p = _ref(WETH, USDC, 100);
        require(p.pool != address(0), "no WETH/USDC pool at the pin");
    }

    function _secondPool() internal view override returns (PoolRef memory p) {
        p = _ref(WETH, CBBTC, 200);
        if (p.pool == address(0)) p = _ref(WETH, CBBTC, 2000);
        if (p.pool == address(0)) p = _ref(WETH, AERO, 200);
        require(p.pool != address(0), "no second pool at the pin");
    }

    function _pmMint(PoolRef memory p, int24 lo, int24 hi, uint256 extra0, uint256 extra1)
        internal
        override
        returns (uint256, uint128, uint256, uint256)
    {
        vm.prank(depositor);
        return pm.mint(
            ReferencePM.MintArgs({
                token0: p.token0,
                token1: p.token1,
                tickSpacing: p.spacing,
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
        (,,,,, lo, hi, liquidity,,,,) = INonfungiblePositionManager(NFPM).positions(id);
    }
}
