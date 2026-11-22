// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @title V3Math
/// @notice The integer arithmetic of a V3 mint and burn, written out for the tests.
///
/// A V3 position manager sizes a mint with `LiquidityAmounts.getLiquidityForAmounts`
/// (v3-periphery) at the pool's current sqrt price, and the pool then takes the token
/// amounts of `SqrtPriceMath.getAmount{0,1}Delta` rounded up (v3-core). A burn returns
/// the same amounts rounded down. The functions below reproduce those three steps, so
/// that a test can state in advance, to the base unit, what a mint will leave.
///
/// The fork tests check this model against two unmodified position managers with
/// `assertEq`. The mock tests then use it as the pool.
library V3Math {
    uint256 internal constant Q96 = 0x1000000000000000000000000;

    // -------------------------------------------------------------------------
    // 512-bit multiply-divide (v3-core FullMath, Solidity 0.8 form)
    // -------------------------------------------------------------------------

    function mulDiv(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            uint256 prod0;
            uint256 prod1;
            assembly {
                let mm := mulmod(a, b, not(0))
                prod0 := mul(a, b)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }
            if (prod1 == 0) {
                require(denominator > 0, "V3Math: zero denominator");
                assembly {
                    result := div(prod0, denominator)
                }
                return result;
            }
            require(denominator > prod1, "V3Math: overflow");
            uint256 remainder;
            assembly {
                remainder := mulmod(a, b, denominator)
            }
            assembly {
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }
            uint256 twos = (0 - denominator) & denominator;
            assembly {
                denominator := div(denominator, twos)
            }
            assembly {
                prod0 := div(prod0, twos)
            }
            assembly {
                twos := add(div(sub(0, twos), twos), 1)
            }
            prod0 |= prod1 * twos;
            uint256 inv = (3 * denominator) ^ 2;
            inv *= 2 - denominator * inv;
            inv *= 2 - denominator * inv;
            inv *= 2 - denominator * inv;
            inv *= 2 - denominator * inv;
            inv *= 2 - denominator * inv;
            inv *= 2 - denominator * inv;
            result = prod0 * inv;
            return result;
        }
    }

    function mulDivUp(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256 result) {
        result = mulDiv(a, b, denominator);
        if (mulmod(a, b, denominator) > 0) {
            require(result < type(uint256).max, "V3Math: overflow");
            result++;
        }
    }

    function divUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return x / y + (x % y > 0 ? 1 : 0);
    }

    // -------------------------------------------------------------------------
    // Amounts between two sqrt prices (v3-core SqrtPriceMath)
    // -------------------------------------------------------------------------

    function amount0Between(uint160 sA, uint160 sB, uint128 liquidity, bool roundUp) internal pure returns (uint256) {
        if (sA > sB) (sA, sB) = (sB, sA);
        uint256 numerator1 = uint256(liquidity) << 96;
        uint256 numerator2 = sB - sA;
        return roundUp
            ? divUp(mulDivUp(numerator1, numerator2, sB), sA)
            : mulDiv(numerator1, numerator2, sB) / sA;
    }

    function amount1Between(uint160 sA, uint160 sB, uint128 liquidity, bool roundUp) internal pure returns (uint256) {
        if (sA > sB) (sA, sB) = (sB, sA);
        return roundUp ? mulDivUp(liquidity, sB - sA, Q96) : mulDiv(liquidity, sB - sA, Q96);
    }

    /// @notice Token amounts of a position of `liquidity` over [sa, sb] at sqrt price `s`.
    function amounts(uint160 s, uint160 sa, uint160 sb, uint128 liquidity, bool roundUp)
        internal
        pure
        returns (uint256 amount0, uint256 amount1)
    {
        if (s <= sa) {
            amount0 = amount0Between(sa, sb, liquidity, roundUp);
        } else if (s < sb) {
            amount0 = amount0Between(s, sb, liquidity, roundUp);
            amount1 = amount1Between(sa, s, liquidity, roundUp);
        } else {
            amount1 = amount1Between(sa, sb, liquidity, roundUp);
        }
    }

    /// @notice What the pool takes when `liquidity` is minted (rounded up).
    function amountsUp(uint160 s, uint160 sa, uint160 sb, uint128 liquidity)
        internal
        pure
        returns (uint256, uint256)
    {
        return amounts(s, sa, sb, liquidity, true);
    }

    /// @notice What the pool returns when `liquidity` is burnt (rounded down).
    function amountsDown(uint160 s, uint160 sa, uint160 sb, uint128 liquidity)
        internal
        pure
        returns (uint256, uint256)
    {
        return amounts(s, sa, sb, liquidity, false);
    }

    // -------------------------------------------------------------------------
    // Liquidity for offered amounts (v3-periphery LiquidityAmounts)
    // -------------------------------------------------------------------------

    function liquidityForAmount0(uint160 sA, uint160 sB, uint256 amount0) internal pure returns (uint256) {
        if (sA > sB) (sA, sB) = (sB, sA);
        return mulDiv(amount0, mulDiv(sA, sB, Q96), sB - sA);
    }

    function liquidityForAmount1(uint160 sA, uint160 sB, uint256 amount1) internal pure returns (uint256) {
        if (sA > sB) (sA, sB) = (sB, sA);
        return mulDiv(amount1, Q96, sB - sA);
    }

    function liquidityForAmounts(uint160 s, uint160 sa, uint160 sb, uint256 amount0, uint256 amount1)
        internal
        pure
        returns (uint128)
    {
        uint256 liquidity;
        if (s <= sa) {
            liquidity = liquidityForAmount0(sa, sb, amount0);
        } else if (s < sb) {
            uint256 l0 = liquidityForAmount0(s, sb, amount0);
            uint256 l1 = liquidityForAmount1(sa, s, amount1);
            liquidity = l0 < l1 ? l0 : l1;
        } else {
            liquidity = liquidityForAmount1(sa, sb, amount1);
        }
        require(liquidity <= type(uint128).max, "V3Math: liquidity overflow");
        return uint128(liquidity);
    }

    // -------------------------------------------------------------------------
    // The mint as Theorem 1 states it
    // -------------------------------------------------------------------------

    struct Jump {
        uint128 liquidity;
        uint256 used0;
        uint256 used1;
        uint256 left0;
        uint256 left1;
    }

    /// @notice A mint offered (hat0, hat1) into [sa, sb] at sqrt price `s`: the liquidity
    ///         it takes, what it uses, and what it leaves on each token.
    function mint(uint160 s, uint160 sa, uint160 sb, uint256 hat0, uint256 hat1)
        internal
        pure
        returns (Jump memory j)
    {
        j.liquidity = liquidityForAmounts(s, sa, sb, hat0, hat1);
        (j.used0, j.used1) = amountsUp(s, sa, sb, j.liquidity);
        j.left0 = hat0 - j.used0;
        j.left1 = hat1 - j.used1;
    }

    // -------------------------------------------------------------------------
    // Values in token1 units at sqrt price s
    // -------------------------------------------------------------------------

    /// @notice Value of `amount0` of token0 in token1 units at sqrt price `s` (rounded down).
    function value0(uint256 amount0, uint160 s) internal pure returns (uint256) {
        return mulDiv(mulDiv(amount0, s, Q96), s, Q96);
    }

    /// @notice Token0 amount worth `value` token1 units at sqrt price `s` (rounded down).
    function amount0ForValue(uint256 value, uint160 s) internal pure returns (uint256) {
        return mulDiv(mulDiv(value, Q96, s), Q96, s);
    }

    /// @notice Per unit of liquidity, the value of token0 and of token1 that a range
    ///         [sa, sb] takes at an interior sqrt price `s`, both in Q96 token1 units.
    ///         The share of token0 the range requires is a / (a + b).
    function requiredValues(uint160 s, uint160 sa, uint160 sb) internal pure returns (uint256 a, uint256 b) {
        a = mulDiv(s, sb - s, sb);
        b = s - sa;
    }
}
