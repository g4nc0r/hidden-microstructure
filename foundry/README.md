# Foundry verification suite

[![Foundry tests](https://github.com/g4nc0r/hidden-microstructure/actions/workflows/foundry.yml/badge.svg)](https://github.com/g4nc0r/hidden-microstructure/actions/workflows/foundry.yml)
![Solidity](https://img.shields.io/badge/Solidity-0.8.26-363636?logo=solidity&logoColor=white)
![Tests](https://img.shields.io/badge/tests-24-b7410e)
![Fork pin](https://img.shields.io/badge/Base_fork-block_43175000-0052ff)

Part of [The Hidden Microstructure of Shared Balance Concentrated Liquidity](../README.md). The proofs in real arithmetic are in [`../lean/`](../lean/).

Twenty-four tests across eight contracts check Theorem 1, Proposition 1 with Corollaries 1 and 2, and Theorem 2 of the paper in the integer arithmetic of a V3 pool. Twelve run on an integer model of a V3 mint and burn with no network access. Twelve run on a fork of Base against two unmodified position managers, Aerodrome Slipstream and Uniswap V3. The captured output is in [`PROOF_OUTPUT.md`](./PROOF_OUTPUT.md) and is the regression target.

Section and statement numbers refer to the November 2026 revision of the paper. Its Section 9.1 and Appendix H describe the suite, and the supplement goes through it scenario by scenario.

## Coverage

| Result | Paper | Integer model | Slipstream fork | Uniswap V3 fork |
|---|---|---|---|---|
| Theorem 1, the jump of the ledger | §4.1 | 8 tests | 4 tests | 4 tests |
| Proposition 1, binding-side criterion | §5.1 | 1 test | 1 test, with Corollary 2 | 1 test, with Corollary 2 |
| Corollary 1, swap-free rule | §5.1 | 2 tests | | |
| Corollary 2, swap-corrected rule | §5.1 | 1 test | the same test | the same test |
| Theorem 2, conservation without a swap | §5.2 | | 1 test | 1 test |

In the fork tests of Theorem 1 every prediction is compared with `assertEq`, stated before the transaction where there is no swap and from the swap's own event where there is one. The liquidity minted and both ledger entries are equal to the base unit on both position managers: without a swap, with a swap, across three consecutive rebalances, and when the leftover of a position in one pool is drawn into the mint of a position in another. After every call the ledger is checked against the tokens the manager holds. There is no tolerance in the fork tests of Theorem 1, and those of Theorem 2 allow each total to fall by the one base unit a mint keeps.

Not covered here:

- Theorem 2 has no test on the integer model. Without custody of tokens its statement is an identity of a test's own bookkeeping, so it is tested on the fork, where the ledger can be compared with the tokens held.
- Lemma 1, on transfers between positions, is an accounting definition. The paper evaluates it on the chain record. Its proof is in Lean.
- The model of §6 (Lemma 2, Propositions 2 to 5, Lemma 3, and Proposition S1 of the supplement) concerns laws over many rebalances. It is proved in the paper and the supplement and checked there by simulation and by replays of the chain record.
- The tests on the integer model carry no fee and no price impact. The swap in `MasterEquationP1Mock` exchanges value at the price. The fork tests swap in the live pools, with both.

## Tests

Each fork scenario runs once on each position manager, as `..._slipstream` and `..._uniV3`.

| Test | Contract | Runs on | Checks |
|---|---|---|---|
| `test_t1_swapfree_zeroDust` | `MasterEquationT1Mock` | integer model | The anchor of the prior paper's suite: a re-mint after a move of 200 ticks, with an empty ledger, leaves one token only, within 5% of the prior paper's figure |
| `test_t1_swapfree_nonzeroDust_boundSide` | `MasterEquationT1Mock` | integer model | A standing balance of the binding token raises the liquidity and lowers the leftover |
| `test_t1_swapfree_nonzeroDust_slackSide` | `MasterEquationT1Mock` | integer model | A standing balance of the other token leaves the liquidity unchanged and is added whole to the leftover |
| `test_t1_swap_belowThreshold` | `MasterEquationT1Mock` | integer model | Half the exact swap halves the leftover, on the same token |
| `test_t1_swap_overshoot` | `MasterEquationT1Mock` | integer model | One and a half times the exact swap moves the leftover to the other token |
| `test_t1_threeSubcases` | `MasterEquationT1Mock` | integer model | New range above, below and around the price |
| `test_t1_multiPosition_recycle` | `MasterEquationT1Mock` | integer model | A second position's mint draws the first position's leftover from the ledger |
| `test_mock_poolAgreesWithModel` | `MasterEquationT1Mock` | integer model | `MockCLPoolV2` and the integer model agree on a burn and on the liquidity for given amounts, at five prices |
| `test_p1_criterion_arbitraryInputs` | `MasterEquationP1Mock` | integer model | Proposition 1 in share form on 400 mints at arbitrary prices, ranges and inputs: the token left and its value |
| `test_p1_cor1_swapFreeRule` | `MasterEquationP1Mock` | integer model | Corollary 1(i) at 13 displacements and three widths of the new range: the token left follows the move and is worth `α(ℓ) V` |
| `test_p1_cor1_standingBalanceBound` | `MasterEquationP1Mock` | integer model | Corollary 1(ii) at four displacements: a balance worth less than `α(ℓ) V` leaves the token unchanged, one of `α(ℓ) V` in the token the swap-free mint uses up leaves nothing, and a larger one moves the leftover to the other token |
| `test_p1_cor2_swapCorrectedRule` | `MasterEquationP1Mock` | integer model | Corollary 2 at five displacements and five execution residuals: the value left is `α(ℓ) V` times the size of the residual, in the token of Corollary 1 for an undershoot and in the token bought for an overshoot |
| `test_t1_swapfree_predictsDustCredit_*` | `MasterEquationT1Fork`, `MasterEquationT1ForkUniV3` | Base fork | One rebalance without a swap: the liquidity and both ledger entries, predicted and equal |
| `test_t1_swapCorrected_predictsDustCredit_*` | `MasterEquationT1Fork`, `MasterEquationT1ForkUniV3` | Base fork | The same with a swap in the live pool, predicted from the pool's `Swap` event and the position manager's `Collect` event |
| `test_t1_consecutiveRebalances_predictsAllEvents_*` | `MasterEquationT1Fork`, `MasterEquationT1ForkUniV3` | Base fork | Three consecutive rebalances, each predicted with the balance the one before it left |
| `test_t1_crossPool_residualAbsorbed_*` | `MasterEquationT1Fork`, `MasterEquationT1ForkUniV3` | Base fork | The leftover of a position in one pool is drawn into the mint of a position in a second pool that shares a token |
| `test_p1_swapCorrected_residualSign_*` | `MasterEquationP1Fork`, `MasterEquationP1ForkUniV3` | Base fork | A swap 10% short of the exact amount leaves the token the position held, and one 10% beyond it leaves the token the swap bought; the value left is within 3% of Proposition 1's expression with the swap taken at the pool's price, the difference being the fee and the price impact |
| `test_t2_conservationAcrossPools_*` | `MasterEquationT2Fork`, `MasterEquationT2ForkUniV3` | Base fork | Two positions in two pools that share a token, eight rebalances without a swap: the total of each token never rises and falls by at most one base unit at a rebalance |

`PROOF_OUTPUT.md` ends with a table of twelve deliberate faults and the tests that fail under each.

## Running

```bash
git submodule update --init --recursive   # first time only
forge build

# Tests on the integer model, no network access (12 tests)
forge test -vv --no-match-contract Fork

# Full suite, with the 12 fork tests (24 tests)
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test -vv

# One position manager
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract 'Fork$' -vv        # Slipstream
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract 'ForkUniV3$' -vv   # Uniswap V3

# A single test
forge test --match-test test_t1_swapfree_zeroDust -vvv
```

Any Base RPC with archive support works in `RPC_BASE_ALCHEMY`. The twelve fork tests are pinned to Base block `43_175_000` (10 March 2026, 10:42 UTC), inside the paper's data window and before V9 was deployed, so the captured numbers are reproducible. The statements tested hold at any block at which the two position managers are deployed and the pools have liquidity; the numbers would differ. The continuous-integration workflow runs the twelve tests on the integer model.

## Managers, model and pools

The Master Equation needs a ledger of leftovers keyed by depositor and shared across positions, `dustBalance[depositor][token]`. A stock position manager keeps none, since every position is an independent NFT that takes only what its `mint()` is given. The fork tests therefore run against reference managers that wrap an unmodified position manager and add the ledger.

| Source | What it is | Used by |
|---|---|---|
| `src/ReferencePM.sol` | Reference manager over the Aerodrome Slipstream position manager at `0x827922686190790b37229fd06084350E74485b72`. Pools are keyed by tick spacing | Slipstream fork tests |
| `src/ReferencePMUniV3.sol` | The same contract over the Uniswap V3 position manager at `0x03a520b32C04BF3bEEf7BEb72E919cf822Ed34f1` (factory `0x33128a8fC17869897dcE68Ed026d694621f6FDfD`). Pools are keyed by fee | Uniswap V3 fork tests |
| `test/helpers/V3Math.sol` | The integer arithmetic of a V3 mint and burn: the liquidity a position manager computes for offered amounts (v3-periphery `LiquidityAmounts`), the amounts the pool takes, rounded up, and the amounts a burn returns, rounded down (v3-core `SqrtPriceMath`) | The fork tests predict with it; the other tests use it as the pool |
| `test/helpers/ForkScenarios.sol`, `SlipstreamAdapter.sol`, `UniV3Adapter.sol` | The six fork scenarios, written once, and the adapters that run them on each manager | Fork tests |
| `src/MockCLPoolV2.sol` | Exact V3 `TickMath`, tick to sqrt price | Every test |
| `src/MockCLPool.sol` | Parent of `MockCLPoolV2`. Its linearised tick arithmetic is not used by any test here | |

The two mock pools are shared by copy with the suite of *The Geometric Siphon*. Pools on the fork: WETH/USDC at tick spacing 100 on Slipstream and at fee 500 on Uniswap V3, with WETH/AERO at tick spacing 200 and WETH/cbBTC at fee 500 as the second pools.

## The claim under test

At a rebalance of pool `P_k`, with withdrawn amounts `(x_w, y_w)`, the standing balances `(x_dust, y_dust)` of the pool's two tokens in the shared ledger, and the signed legs `(σ_x, σ_y)` of the swap, the mint is offered

```
x̂ = x_w + x_dust − σ_x,   ŷ = y_w + y_dust − σ_y
```

The new range takes `(g_x, g_y)` per unit of liquidity at the current price, and the mint takes

```
L_new = min( x̂ / g_x,  ŷ / g_y )
```

Theorem 1 gives the ledger after the event,

```
x_dust' = x̂ − L_new · g_x,    y_dust' = ŷ − L_new · g_y
```

with the entries of every other token unchanged. Unless the offered amounts are in exactly the ratio the range requires, one of the two is zero and the other holds the whole leftover. Proposition 1 says which, by comparing the share of one token in what is offered with the share the range requires. Theorem 2 says that for each token of a portfolio, what the positions hold plus the ledger entry is unchanged by a rebalance without a swap, each position being read at the price of its own pool:

```
Σ_k a_{k,i}(τ) + D_{pool,i}(τ)  =  const
```

The fork tests compute these quantities in the integer arithmetic of `V3Math` and compare them with what the position managers do.

## Layout

```
foundry/
├── src/
│   ├── ReferencePM.sol                      reference manager over Slipstream
│   ├── ReferencePMUniV3.sol                 reference manager over Uniswap V3
│   ├── MockCLPool.sol                       mock pool, linearised ticks (parent of the next)
│   ├── MockCLPoolV2.sol                     exact V3 TickMath
│   └── interfaces/
├── test/
│   ├── MasterEquationT1Mock.t.sol           Theorem 1, integer model
│   ├── MasterEquationP1Mock.t.sol           Proposition 1 and corollaries, integer model
│   ├── MasterEquationT1Fork.t.sol           Theorems 1 and 2, Proposition 1, Slipstream
│   ├── MasterEquationT1ForkUniV3.t.sol      Theorems 1 and 2, Proposition 1, Uniswap V3
│   └── helpers/                             V3Math, ForkScenarios, the two adapters, Tick
├── lib/forge-std/                           submodule
├── foundry.toml
├── PROOF_OUTPUT.md                          captured forge output, by statement
└── README.md
```

## Requirements

- Foundry, `forge` 1.5 or later
- Solidity 0.8.26, set in `foundry.toml`
- `forge-std`, as a git submodule under `lib/`. A source archive without git history, such as the Zenodo snapshot, has an empty `lib/forge-std`; clone `https://github.com/foundry-rs/forge-std` into it and check out commit `8b531a0`

## Licence

MIT. See [`../LICENSE`](../LICENSE).
