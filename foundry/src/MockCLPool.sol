// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @title MockCLPool
/// @notice Minimal CL pool with linearised tick math, sufficient to demonstrate
///         the geometric residual at order of magnitude. Used by
///         GeometricResidualProofClean and ZeroSwapExtinctionProof.
contract MockCLPool {
    uint160 public sqrtPriceX96;
    int24 public tick;

    uint256 constant Q96 = 2**96;

    /// @notice Tick anchor for the linear sqrt-price approximation;
    ///         corresponds to a price of ≈2500 (sqrt(2500) ≈ 50).
    int24 internal constant ANCHOR_TICK = 73135;
    uint256 internal constant ANCHOR_SQRT_PRICE = 314748404868481885948183330816; // sqrt(2500) * 2^96

    constructor(uint160 _sqrtPriceX96) {
        sqrtPriceX96 = _sqrtPriceX96;
        tick = ANCHOR_TICK;
    }
    
    /// @notice Get token amounts for given liquidity and range
    /// @dev Simplified CL math: amount0 = L * (1/sqrtP - 1/sqrtPb), amount1 = L * (sqrtP - sqrtPa)
    function getAmountsForLiquidity(
        uint128 liquidity,
        int24 tickLower,
        int24 tickUpper
    ) public view returns (uint256 amount0, uint256 amount1) {
        uint160 sqrtPriceLower = getSqrtRatioAtTick(tickLower);
        uint160 sqrtPriceUpper = getSqrtRatioAtTick(tickUpper);
        uint160 currentPrice = sqrtPriceX96;
        
        if (currentPrice <= sqrtPriceLower) {
            // Price below range: all token0
            amount0 = getAmount0ForLiquidity(sqrtPriceLower, sqrtPriceUpper, liquidity);
            amount1 = 0;
        } else if (currentPrice < sqrtPriceUpper) {
            // Price in range: both tokens
            amount0 = getAmount0ForLiquidity(currentPrice, sqrtPriceUpper, liquidity);
            amount1 = getAmount1ForLiquidity(sqrtPriceLower, currentPrice, liquidity);
        } else {
            // Price above range: all token1
            amount0 = 0;
            amount1 = getAmount1ForLiquidity(sqrtPriceLower, sqrtPriceUpper, liquidity);
        }
    }
    
    /// @notice Get liquidity for given token amounts and range
    function getLiquidityForAmounts(
        uint256 amount0,
        uint256 amount1,
        int24 tickLower,
        int24 tickUpper
    ) public view returns (uint128 liquidity) {
        uint160 sqrtPriceLower = getSqrtRatioAtTick(tickLower);
        uint160 sqrtPriceUpper = getSqrtRatioAtTick(tickUpper);
        uint160 currentPrice = sqrtPriceX96;
        
        if (currentPrice <= sqrtPriceLower) {
            // All token0
            liquidity = getLiquidityForAmount0(sqrtPriceLower, sqrtPriceUpper, amount0);
        } else if (currentPrice < sqrtPriceUpper) {
            // Both tokens - take minimum
            uint128 liq0 = getLiquidityForAmount0(currentPrice, sqrtPriceUpper, amount0);
            uint128 liq1 = getLiquidityForAmount1(sqrtPriceLower, currentPrice, amount1);
            liquidity = liq0 < liq1 ? liq0 : liq1;
        } else {
            // All token1
            liquidity = getLiquidityForAmount1(sqrtPriceLower, sqrtPriceUpper, amount1);
        }
    }
    
    /// @notice Move price to new tick
    function movePriceToTick(int24 newTick) external {
        tick = newTick;
        sqrtPriceX96 = getSqrtRatioAtTick(newTick);
    }

    /// @notice Set sqrt-price and tick directly. Used by the fork tests to
    ///         mirror a live pool's slot0 exactly when computing closed-form
    ///         predictions; not used outside testing.
    function setSqrtPriceX96(uint160 _sqrtPriceX96, int24 _tick) external {
        sqrtPriceX96 = _sqrtPriceX96;
        tick = _tick;
    }
    
    // =============================================================================
    // Internal Math Functions
    // =============================================================================
    
    function getAmount0ForLiquidity(
        uint160 sqrtRatioAX96,
        uint160 sqrtRatioBX96,
        uint128 liquidity
    ) internal pure returns (uint256 amount0) {
        if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96, sqrtRatioAX96);
        
        return mulDiv(
            uint256(liquidity) * Q96,
            sqrtRatioBX96 - sqrtRatioAX96,
            sqrtRatioBX96
        ) / sqrtRatioAX96;
    }
    
    function getAmount1ForLiquidity(
        uint160 sqrtRatioAX96,
        uint160 sqrtRatioBX96,
        uint128 liquidity
    ) internal pure returns (uint256 amount1) {
        if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96, sqrtRatioAX96);
        
        return mulDiv(liquidity, sqrtRatioBX96 - sqrtRatioAX96, Q96);
    }
    
    function getLiquidityForAmount0(
        uint160 sqrtRatioAX96,
        uint160 sqrtRatioBX96,
        uint256 amount0
    ) internal pure returns (uint128 liquidity) {
        if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96, sqrtRatioAX96);
        
        uint256 intermediate = mulDiv(sqrtRatioAX96, sqrtRatioBX96, Q96);
        liquidity = uint128(mulDiv(amount0, intermediate, sqrtRatioBX96 - sqrtRatioAX96));
    }
    
    function getLiquidityForAmount1(
        uint160 sqrtRatioAX96,
        uint160 sqrtRatioBX96,
        uint256 amount1
    ) internal pure returns (uint128 liquidity) {
        if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96, sqrtRatioAX96);
        
        liquidity = uint128(mulDiv(amount1, Q96, sqrtRatioBX96 - sqrtRatioAX96));
    }
    
    /// @notice Linear-approximation sqrtPrice from tick around ANCHOR_TICK.
    /// @dev    Each tick ≈ 0.01% price change ≈ 0.005% sqrt-price change, so the
    ///         linear coefficient is 5 / 100,000 per tick offset from ANCHOR_TICK.
    ///         Sufficient for ≤1% rounding versus exact V3 TickMath in the
    ///         reported §6 mock-pool numbers; see MockCLPoolV2 for the exact
    ///         override used by Theorems 4-6.
    function getSqrtRatioAtTick(int24 _tick) public pure virtual returns (uint160) {
        int256 tickDelta = int256(_tick) - int256(ANCHOR_TICK);
        int256 adjustment = int256(ANCHOR_SQRT_PRICE) * tickDelta * 5 / 100000;
        return uint160(uint256(int256(ANCHOR_SQRT_PRICE) + adjustment));
    }
    
    /// @notice Multiply two uint256 values and divide by denominator
    function mulDiv(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256 result) {
        uint256 prod = a * b;
        require(denominator > 0);
        result = prod / denominator;
    }
}
