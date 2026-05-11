// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {
    INonfungiblePositionManager,
    IUniswapV3Pool,
    IUniswapV3Factory,
    IERC20,
    V3Bounds
} from "./interfaces/Slipstream.sol";

/// @title ReferencePM
/// @notice Minimal multi-pool PM-class wrapper around an unmodified V3 NFPM,
///         adding a depositor-keyed shared dust ledger
///         `dustBalance[depositor][token]`. This is the architectural
///         precondition the Master Equation requires: per §7.1 of the
///         Geometric Siphon paper, a stock NFPM cannot host cross-position
///         dust absorption because every position is an independent NFT
///         that consumes only the tokens its mint() is given. ReferencePM
///         adds the shared mapping minimally and otherwise delegates all
///         V3 mechanics to the underlying NFPM.
///
/// @dev    Verification code, not production: the swap callback trusts
///         msg.sender is the pool we just called (no authentication beyond
///         that). The contract is the unit under test in
///         MasterEquationT1Fork; mock-pool tests verify the closed form
///         directly without involving this contract.
contract ReferencePM {
    INonfungiblePositionManager public immutable nfpm;
    IUniswapV3Factory public immutable factory;

    /// @notice Standing dust balance per depositor per token. Aggregated
    ///         across all of the depositor's positions in any pool that
    ///         contains the token.
    mapping(address => mapping(address => uint256)) public dustBalance;

    /// @notice Position ownership in the PM frame. The underlying NFPM owner
    ///         of every minted tokenId is `address(this)`; the depositor
    ///         identity lives in this mapping.
    mapping(uint256 => address) public positionOwner;

    /// @notice Set during `_swap` and read by `uniswapV3SwapCallback` to
    ///         check the callback comes from the pool we are mid-call to.
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
        nfpm = INonfungiblePositionManager(_nfpm);
        factory = IUniswapV3Factory(_factory);
    }

    /// @notice Pull tokens from depositor's wallet directly into their dust
    ///         balance. Useful for tests and for seeding a position.
    function deposit(address token, uint256 amount) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
        uint256 newBal = dustBalance[msg.sender][token] + amount;
        dustBalance[msg.sender][token] = newBal;
        emit Deposited(msg.sender, token, amount);
        emit DustCredited(msg.sender, token, newBal);
    }

    /// @notice Send dust from depositor's balance back to their wallet.
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
        int24 tickSpacing;
        int24 tickLower;
        int24 tickUpper;
        uint256 amount0Extra;
        uint256 amount1Extra;
    }

    /// @notice Open a position. Depositor's existing dust on the pool's two
    ///         tokens is auto-recycled in full; `amountExtra` is pulled from
    ///         their wallet on top.
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
            args.tickSpacing,
            args.tickLower,
            args.tickUpper,
            hat0,
            hat1
        );
    }

    /// @notice Atomic rebalance with no swap correction (S = 0).
    function rebalance(uint256 tokenId, int24 newTickLower, int24 newTickUpper)
        external
        returns (uint256 newTokenId, uint128 newLiquidity, uint256 dust0After, uint256 dust1After)
    {
        return _rebalance(tokenId, newTickLower, newTickUpper, 0, false);
    }

    /// @notice Atomic rebalance with an in-pool swap correction. The swap
    ///         routes through the same pool as the position; depositor pays
    ///         from their (in-flight) standing balance.
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

    /// @notice Close a position fully and credit the returned tokens to dust.
    function closePosition(uint256 tokenId)
        external
        returns (uint256 amount0, uint256 amount1)
    {
        require(positionOwner[tokenId] == msg.sender, "not owner");
        (
            ,, address token0, address token1,,,, uint128 liquidity,,,,
        ) = nfpm.positions(tokenId);

        nfpm.decreaseLiquidity(INonfungiblePositionManager.DecreaseLiquidityParams({
            tokenId: tokenId,
            liquidity: liquidity,
            amount0Min: 0,
            amount1Min: 0,
            deadline: block.timestamp
        }));

        (amount0, amount1) = nfpm.collect(INonfungiblePositionManager.CollectParams({
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
            ,, address token0, address token1, int24 tickSpacing,,, uint128 liquidity,,,,
        ) = nfpm.positions(tokenId);

        // Withdraw old position fully into ReferencePM custody.
        nfpm.decreaseLiquidity(INonfungiblePositionManager.DecreaseLiquidityParams({
            tokenId: tokenId,
            liquidity: liquidity,
            amount0Min: 0,
            amount1Min: 0,
            deadline: block.timestamp
        }));
        (uint256 wd0, uint256 wd1) = nfpm.collect(INonfungiblePositionManager.CollectParams({
            tokenId: tokenId,
            recipient: address(this),
            amount0Max: type(uint128).max,
            amount1Max: type(uint128).max
        }));
        delete positionOwner[tokenId];

        // Mint inputs: withdrawn tokens + standing dust on the pool's pair.
        uint256 hat0 = wd0 + dustBalance[depositor][token0];
        uint256 hat1 = wd1 + dustBalance[depositor][token1];
        dustBalance[depositor][token0] = 0;
        dustBalance[depositor][token1] = 0;

        // Optional in-pool swap correction. Adjust mint inputs by signed deltas.
        if (swapAmountIn > 0) {
            address pool = factory.getPool(token0, token1, tickSpacing);
            require(pool != address(0), "no pool");
            (int256 a0, int256 a1) = _swap(pool, zeroForOne, int256(swapAmountIn), token0, token1);
            // Pool frame: positive delta = paid into pool, negative = received from pool.
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
            depositor, token0, token1, tickSpacing, newTickLower, newTickUpper, hat0, hat1
        );

        emit Rebalanced(depositor, tokenId, newTokenId, newLiquidity, dust0After, dust1After);
    }

    function _mintAndCredit(
        address depositor,
        address token0,
        address token1,
        int24 tickSpacing,
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
            INonfungiblePositionManager.MintParams({
                token0: token0,
                token1: token1,
                tickSpacing: tickSpacing,
                tickLower: tickLower,
                tickUpper: tickUpper,
                amount0Desired: hat0,
                amount1Desired: hat1,
                amount0Min: 0,
                amount1Min: 0,
                recipient: address(this),
                deadline: block.timestamp,
                sqrtPriceX96: 0
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

    /// @notice V3 swap callback. Pays the pool the owed token amounts from
    ///         contract custody.
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external {
        require(msg.sender == _activeSwapPool, "callback: unknown pool");
        (address token0, address token1) = abi.decode(data, (address, address));
        if (amount0Delta > 0) IERC20(token0).transfer(msg.sender, uint256(amount0Delta));
        if (amount1Delta > 0) IERC20(token1).transfer(msg.sender, uint256(amount1Delta));
    }
}
