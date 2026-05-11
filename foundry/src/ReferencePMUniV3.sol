// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {INfpmUniV3, IFactoryUniV3} from "./interfaces/UniswapV3.sol";
import {IUniswapV3Pool, IERC20, V3Bounds} from "./interfaces/Slipstream.sol";

/// @title ReferencePMUniV3
/// @notice Minimal multi-pool PM-class wrapper around an unmodified Uniswap V3
///         NonfungiblePositionManager, adding a depositor-keyed shared dust
///         ledger `dustBalance[depositor][token]`. The Uniswap V3 sibling of
///         `ReferencePM`; differs only in NFPM ABI (pool key is `fee`
///         (uint24) instead of `tickSpacing` (int24)).
///
/// @dev    The closed-form Theorem 1 is V3-mechanical and identical across
///         the two DEXes. Cross-DEX equivalence on Base under the same
///         block pin demonstrates the Master Equation governs the
///         architectural class of multi-pool PM contracts with shared
///         depositor-keyed dust accounting, independent of which V3-flavoured
///         DEX hosts the underlying pools.
contract ReferencePMUniV3 {
    INfpmUniV3 public immutable nfpm;
    IFactoryUniV3 public immutable factory;

    mapping(address => mapping(address => uint256)) public dustBalance;
    mapping(uint256 => address) public positionOwner;
    address private _activeSwapPool;

    event Deposited(address indexed depositor, address indexed token, uint256 amount);
    event Withdrawn(address indexed depositor, address indexed token, uint256 amount);
    event DustCredited(address indexed depositor, address indexed token, uint256 newBalance);
    event PositionMinted(address indexed depositor, uint256 indexed tokenId, uint128 liquidity);
    event PositionClosed(address indexed depositor, uint256 indexed tokenId, uint256 amount0, uint256 amount1);
    event Rebalanced(
        address indexed depositor,
        uint256 indexed oldTokenId,
        uint256 indexed newTokenId,
        uint128 newLiquidity,
        uint256 dust0After,
        uint256 dust1After
    );
    event SwapCorrection(
        address indexed depositor,
        uint256 indexed tokenId,
        int256 sigma0,
        int256 sigma1
    );

    constructor(address _nfpm, address _factory) {
        nfpm = INfpmUniV3(_nfpm);
        factory = IFactoryUniV3(_factory);
    }

    function deposit(address token, uint256 amount) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
        uint256 newBal = dustBalance[msg.sender][token] + amount;
        dustBalance[msg.sender][token] = newBal;
        emit Deposited(msg.sender, token, amount);
        emit DustCredited(msg.sender, token, newBal);
    }

    function withdrawDust(address token, uint256 amount) external {
        uint256 bal = dustBalance[msg.sender][token];
        require(bal >= amount, "insufficient dust");
        unchecked { dustBalance[msg.sender][token] = bal - amount; }
        IERC20(token).transfer(msg.sender, amount);
        emit Withdrawn(msg.sender, token, amount);
        emit DustCredited(msg.sender, token, bal - amount);
    }

    struct MintArgs {
        address token0;
        address token1;
        uint24 fee;
        int24 tickLower;
        int24 tickUpper;
        uint256 amount0Extra;
        uint256 amount1Extra;
    }

    function mint(MintArgs calldata args)
        external
        returns (uint256 tokenId, uint128 liquidity, uint256 dust0After, uint256 dust1After)
    {
        if (args.amount0Extra > 0) {
            IERC20(args.token0).transferFrom(msg.sender, address(this), args.amount0Extra);
        }
        if (args.amount1Extra > 0) {
            IERC20(args.token1).transferFrom(msg.sender, address(this), args.amount1Extra);
        }
        uint256 hat0 = args.amount0Extra + dustBalance[msg.sender][args.token0];
        uint256 hat1 = args.amount1Extra + dustBalance[msg.sender][args.token1];
        dustBalance[msg.sender][args.token0] = 0;
        dustBalance[msg.sender][args.token1] = 0;

        (tokenId, liquidity, dust0After, dust1After) = _mintAndCredit(
            msg.sender,
            args.token0,
            args.token1,
            args.fee,
            args.tickLower,
            args.tickUpper,
            hat0,
            hat1
        );
    }

    function rebalance(uint256 tokenId, int24 newTickLower, int24 newTickUpper)
        external
        returns (uint256 newTokenId, uint128 newLiquidity, uint256 dust0After, uint256 dust1After)
    {
        return _rebalance(tokenId, newTickLower, newTickUpper, 0, false);
    }

    function rebalanceWithSwap(
        uint256 tokenId,
        int24 newTickLower,
        int24 newTickUpper,
        uint256 swapAmountIn,
        bool zeroForOne
    )
        external
        returns (uint256 newTokenId, uint128 newLiquidity, uint256 dust0After, uint256 dust1After)
    {
        return _rebalance(tokenId, newTickLower, newTickUpper, swapAmountIn, zeroForOne);
    }

    function closePosition(uint256 tokenId)
        external
        returns (uint256 amount0, uint256 amount1)
    {
        require(positionOwner[tokenId] == msg.sender, "not owner");
        (
            ,, address token0, address token1,,,, uint128 liquidity,,,,
        ) = nfpm.positions(tokenId);

        nfpm.decreaseLiquidity(INfpmUniV3.DecreaseLiquidityParams({
            tokenId: tokenId,
            liquidity: liquidity,
            amount0Min: 0,
            amount1Min: 0,
            deadline: block.timestamp
        }));

        (amount0, amount1) = nfpm.collect(INfpmUniV3.CollectParams({
            tokenId: tokenId,
            recipient: address(this),
            amount0Max: type(uint128).max,
            amount1Max: type(uint128).max
        }));

        uint256 newBal0 = dustBalance[msg.sender][token0] + amount0;
        uint256 newBal1 = dustBalance[msg.sender][token1] + amount1;
        dustBalance[msg.sender][token0] = newBal0;
        dustBalance[msg.sender][token1] = newBal1;
        emit DustCredited(msg.sender, token0, newBal0);
        emit DustCredited(msg.sender, token1, newBal1);
        emit PositionClosed(msg.sender, tokenId, amount0, amount1);
        delete positionOwner[tokenId];
    }

    // -----------------------------------------------------------------------
    // Internals
    // -----------------------------------------------------------------------

    function _rebalance(
        uint256 tokenId,
        int24 newTickLower,
        int24 newTickUpper,
        uint256 swapAmountIn,
        bool zeroForOne
    )
        internal
        returns (uint256 newTokenId, uint128 newLiquidity, uint256 dust0After, uint256 dust1After)
    {
        address depositor = positionOwner[tokenId];
        require(depositor == msg.sender, "not owner");

        (
            ,, address token0, address token1, uint24 fee,,, uint128 liquidity,,,,
        ) = nfpm.positions(tokenId);

        nfpm.decreaseLiquidity(INfpmUniV3.DecreaseLiquidityParams({
            tokenId: tokenId,
            liquidity: liquidity,
            amount0Min: 0,
            amount1Min: 0,
            deadline: block.timestamp
        }));
        (uint256 wd0, uint256 wd1) = nfpm.collect(INfpmUniV3.CollectParams({
            tokenId: tokenId,
            recipient: address(this),
            amount0Max: type(uint128).max,
            amount1Max: type(uint128).max
        }));
        delete positionOwner[tokenId];

        uint256 hat0 = wd0 + dustBalance[depositor][token0];
        uint256 hat1 = wd1 + dustBalance[depositor][token1];
        dustBalance[depositor][token0] = 0;
        dustBalance[depositor][token1] = 0;

        if (swapAmountIn > 0) {
            address pool = factory.getPool(token0, token1, fee);
            require(pool != address(0), "no pool");
            (int256 a0, int256 a1) = _swap(pool, zeroForOne, int256(swapAmountIn), token0, token1);
            if (a0 > 0) {
                hat0 -= uint256(a0);
            } else if (a0 < 0) {
                hat0 += uint256(-a0);
            }
            if (a1 > 0) {
                hat1 -= uint256(a1);
            } else if (a1 < 0) {
                hat1 += uint256(-a1);
            }
            emit SwapCorrection(depositor, tokenId, a0, a1);
        }

        (newTokenId, newLiquidity, dust0After, dust1After) = _mintAndCredit(
            depositor, token0, token1, fee, newTickLower, newTickUpper, hat0, hat1
        );

        emit Rebalanced(depositor, tokenId, newTokenId, newLiquidity, dust0After, dust1After);
    }

    function _mintAndCredit(
        address depositor,
        address token0,
        address token1,
        uint24 fee,
        int24 tickLower,
        int24 tickUpper,
        uint256 hat0,
        uint256 hat1
    )
        internal
        returns (uint256 tokenId, uint128 liquidity, uint256 dust0After, uint256 dust1After)
    {
        IERC20(token0).approve(address(nfpm), hat0);
        IERC20(token1).approve(address(nfpm), hat1);

        uint256 used0;
        uint256 used1;
        (tokenId, liquidity, used0, used1) = nfpm.mint(
            INfpmUniV3.MintParams({
                token0: token0,
                token1: token1,
                fee: fee,
                tickLower: tickLower,
                tickUpper: tickUpper,
                amount0Desired: hat0,
                amount1Desired: hat1,
                amount0Min: 0,
                amount1Min: 0,
                recipient: address(this),
                deadline: block.timestamp
            })
        );

        positionOwner[tokenId] = depositor;
        dust0After = hat0 - used0;
        dust1After = hat1 - used1;
        dustBalance[depositor][token0] = dust0After;
        dustBalance[depositor][token1] = dust1After;
        emit DustCredited(depositor, token0, dust0After);
        emit DustCredited(depositor, token1, dust1After);
        emit PositionMinted(depositor, tokenId, liquidity);
    }

    function _swap(
        address pool,
        bool zeroForOne,
        int256 amountSpecified,
        address token0,
        address token1
    ) internal returns (int256 amount0Delta, int256 amount1Delta) {
        uint160 sqrtPriceLimitX96 = zeroForOne
            ? V3Bounds.MIN_SQRT_RATIO_PLUS_ONE
            : V3Bounds.MAX_SQRT_RATIO_MINUS_ONE;
        _activeSwapPool = pool;
        (amount0Delta, amount1Delta) = IUniswapV3Pool(pool).swap(
            address(this),
            zeroForOne,
            amountSpecified,
            sqrtPriceLimitX96,
            abi.encode(token0, token1)
        );
        _activeSwapPool = address(0);
    }

    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external {
        require(msg.sender == _activeSwapPool, "callback: unknown pool");
        (address token0, address token1) = abi.decode(data, (address, address));
        if (amount0Delta > 0) IERC20(token0).transfer(msg.sender, uint256(amount0Delta));
        if (amount1Delta > 0) IERC20(token1).transfer(msg.sender, uint256(amount1Delta));
    }
}
