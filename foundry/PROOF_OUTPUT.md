# Captured Foundry test output

Part of [The Hidden Microstructure of Shared Balance Concentrated Liquidity](../README.md). The suite is described in [`README.md`](./README.md).

Output of `forge test -vv`, kept under version control as the regression target. **24 tests in 8 contracts.** Twelve are network-free. Twelve run on a fork of Base at block `43_175_000` (2026-03-10 10:42 UTC, inside the paper's data window, before V9 was deployed) against two unmodified V3 position managers, Aerodrome Slipstream and Uniswap V3. Captured with forge 1.8.6 on 2026-11-20.

Statements are named as in the November 2026 revision of the paper: Theorem 1 (§4.1), Proposition 1 with Corollaries 1 and 2 (§5.1), Theorem 2 (§5.2).

| Contract | Tests | Network | Statement |
|---|---:|---|---|
| `MasterEquationT1Mock` | 8 | none | Theorem 1 on the integer pool model |
| `MasterEquationP1Mock` | 4 | none | Proposition 1, Corollary 1, Corollary 2 |
| `MasterEquationT1Fork` | 4 | Base fork | Theorem 1 against the Slipstream position manager (`0x827922686190790b37229fd06084350E74485b72`) |
| `MasterEquationP1Fork` | 1 | Base fork | Proposition 1 and the swap-corrected rule, Slipstream |
| `MasterEquationT2Fork` | 1 | Base fork | Theorem 2, Slipstream |
| `MasterEquationT1ForkUniV3` | 4 | Base fork | Theorem 1 against the Uniswap V3 position manager (`0x03a520b32C04BF3bEEf7BEb72E919cf822Ed34f1`) |
| `MasterEquationP1ForkUniV3` | 1 | Base fork | Proposition 1 and the swap-corrected rule, Uniswap V3 |
| `MasterEquationT2ForkUniV3` | 1 | Base fork | Theorem 2, Uniswap V3 |

## How the two layers fit

`test/helpers/V3Math.sol` writes out the integer arithmetic of a V3 mint and burn: the liquidity a position manager computes for offered amounts, the amounts the pool takes (rounded up) and the amounts a burn returns (rounded down). The fork tests use it to state the liquidity the reference manager will mint and the two ledger entries it will leave, and compare with `assertEq`, before the transaction where there is no swap and from the swap's own event where there is one. Every comparison of a prediction of Theorem 1 in the fork tests is an equality in base units; there is no tolerance. The tests of Proposition 1 compare the value left with the proposition's expression, the swap taken at the pool's price, to within 3%, and the tests of Theorem 2 allow each total to fall by the one base unit a mint keeps.

The network-free tests then use the same model as the pool and check the paper's statements against it by their own formulas, over many configurations.

After every call in the fork tests the ledger is also checked against custody: the manager's balance of each token equals its ledger entry.

## Run summary

```
Suite                               Tests   Pass  Fail
MasterEquationT1Mock                    8      8     0
MasterEquationP1Mock                    4      4     0
MasterEquationT1Fork (fork)             4      4     0
MasterEquationP1Fork (fork)             1      1     0
MasterEquationT2Fork (fork)             1      1     0
MasterEquationT1ForkUniV3 (fork)        4      4     0
MasterEquationP1ForkUniV3 (fork)        1      1     0
MasterEquationT2ForkUniV3 (fork)        1      1     0
                                       --     --    --
                                       24     24     0
```

## Theorem 1 against the two position managers

Sources: `MasterEquationT1Fork.t.sol`, `MasterEquationT1ForkUniV3.t.sol`; scenarios in `test/helpers/ForkScenarios.sol`. Pools: WETH/USDC at tick spacing 100 (Slipstream) and at fee 500 (Uniswap V3). In each row the predicted and the actual value are equal, and the test asserts that.

| Scenario | Quantity | Slipstream | Uniswap V3 |
|---|---|---:|---:|
| No swap, one rebalance | liquidity | 657,215,162,506,520 | 631,497,931,618,818 |
| | WETH left (wei) | 706 | 213 |
| | USDC left (raw) | 249,980,633 | 418,199,469 |
| Swap-corrected, one rebalance | liquidity | 948,147,209,119,380 | 891,602,398,389,104 |
| | WETH left (wei) | 283 | 941 |
| | USDC left (raw) | 363,150,183 | 612,788,020 |
| Three rebalances, event 0 | WETH, USDC left | 69; 142,456,347 | 292; 405,158,378 |
| Three rebalances, event 1 | WETH, USDC left | 594; 58,204,098 | 368; 395,322,046 |
| Three rebalances, event 2 | WETH, USDC left | 704; 249,980,631 | 211; 418,199,467 |
| Cross-pool mint | WETH in the ledger before (wei) | 706,160,093,942,592,145 | 605,533,377,748,812,294 |
| | WETH in the ledger after (wei) | 484,375,590,415,751,947 | 1,723 |
| | liquidity of the second position | 439,594,390,459,935,097,074 | 21,294,174,357,435 |

Swap-corrected. The manager withdraws, sells 0.05 WETH in the pool, and mints. The prediction takes the amounts withdrawn (a burn at the price before the swap, checked against the position manager's `Collect` event), adds the standing balance, subtracts the two legs of the swap as the pool's `Swap` event reports them, and applies Theorem 1 at the price that event reports. The swap moved the sqrt price from 3593322747735482000000000 to 3593322210102831182525630 on Slipstream and from 3593244741629284492354006 to 3593240611873594684191907 on Uniswap V3.

Cross-pool. Position A in WETH/USDC is moved to a range that needs less WETH than it holds and leaves WETH in the ledger. Position B is then opened in a second pool that shares WETH (WETH/AERO at tick spacing 200 on Slipstream, WETH/cbBTC at fee 500 on Uniswap V3) with its other token only, and takes its WETH from the ledger. The liquidity of B and the WETH left are predicted and equal to the base unit.

## Proposition 1 and the swap-corrected rule against the two position managers

Sources: `MasterEquationP1Fork`, `MasterEquationP1ForkUniV3`. The old range sits 300 ticks below the price and the ledger is emptied, so the position comes out long USDC and, without a swap, would leave USDC. From the same state the manager sells nine tenths and then eleven tenths of the USDC amount that would leave nothing (computed without fee or price impact). Values in raw USDC.

| | Slipstream | Uniswap V3 |
|---|---:|---:|
| Swap 10% short: WETH left (wei), USDC left | 176; 206,693,589 | 273; 188,971,076 |
| Shortfall over the share of WETH required | 206,314,223 | 189,100,773 |
| Swap 10% over: WETH left (wei), USDC left | 87,315,936,632,135,845; 0 | 90,344,693,084,258,382; 0 |
| Value of the WETH left | 179,608,465 | 185,830,534 |
| Excess over the share of USDC required | 180,012,520 | 185,676,328 |

A swap short of the exact amount leaves the token the position held. A swap beyond it leaves the token the swap bought. The value left agrees to within 0.3% with Proposition 1's expression, the swap taken at the pool's price, the difference being the pool's fee and the swap's price impact; the test allows 3%.

## Theorem 2 against the two position managers

Sources: `MasterEquationT2Fork`, `MasterEquationT2ForkUniV3`. Two positions in two pools that share WETH, eight rebalances without a swap, alternating between the positions. For each token the test adds what the positions would return at their pools' prices to the ledger entry.

```
Slipstream
  WETH total at start / after eight rebalances   1499999999999999998   1499999999999999990
  USDC total at start / after eight rebalances   2499999999            2499999995
  AERO total at start / after eight rebalances   999999999999999999999 999999999999999999995
  largest change at one rebalance, base units    1

Uniswap V3
  WETH total at start / after eight rebalances   1499999999999999998   1499999999999999990
  USDC total at start / after eight rebalances   2499999999            2499999995
  cbBTC total at start / after eight rebalances  1999999               1999995
  largest change at one rebalance, base units    1
```

A rebalance never raises a total, lowers the total of a token in its pool by at most one base unit (the unit the pool keeps when it rounds a mint up), and leaves the total of a token outside its pool unchanged. The ledger equals the tokens held after every call.

## Theorem 1 on the integer pool model

Source: `MasterEquationT1Mock.t.sol`. The anchor of the Geometric Siphon suite: a position opened at tick 78,244 into 500 ticks either side, withdrawn after a move of 200 ticks up, re-minted into 1,000 ticks either side. Every mint is checked against Theorem 1 by three statements that do not reuse the model's own formula for the liquidity: one more unit of liquidity is not affordable, the binding token is used up to within what one unit of liquidity takes, and the other token's leftover equals the offered amount less the binding amount times `g_slack / g_binding`.

| Test | Captured |
|---|---|
| `test_t1_swapfree_zeroDust` | token0 left 0; token1 left 2,132,175,995 of 4,633,196,746 withdrawn (within 5% of the prior paper's 2,061 USDC) |
| `test_t1_swapfree_nonzeroDust_boundSide` | liquidity 507,769,304 to 598,227,458; token1 left 2,132,175,995 to 1,899,840,296 |
| `test_t1_swapfree_nonzeroDust_slackSide` | liquidity unchanged; token1 left 2,132,175,995 to 7,132,175,995, the 5,000,000,000 added |
| `test_t1_swap_belowThreshold` | half the exact swap: token1 left 2,132,175,995 to 1,066,090,720 |
| `test_t1_swap_overshoot` | one and a half times the exact swap: token0 left 383,607; token1 left 1 |
| `test_t1_threeSubcases` | range above the price: token1 credited whole (3,436,347,382); below: token0 credited whole (469,278), token1 left 4; inside: as test 1 |
| `test_t1_multiPosition_recycle` | ledger entry of token1 2,132,175,995 after A, 132,176,879 after B; B's liquidity 670,029,020 alone, 2,010,086,468 with the ledger |
| `test_mock_poolAgreesWithModel` | `MockCLPoolV2` and the model agree on a burn and on the liquidity for given amounts at five prices |

## Proposition 1 and its corollaries on the integer pool model

Source: `MasterEquationP1Mock.t.sol`. Old range of 500 ticks either side of tick 6,000; new ranges centred in tick space on the price; amounts of order 1e21 base units; tolerances at one part in 1e9 of the value involved.

| Test | What is checked | Captured |
|---|---|---|
| `test_p1_criterion_arbitraryInputs` | Proposition 1 in share form on 400 mints at arbitrary prices, ranges and inputs: the token left and its value | 178 leave token0, 222 leave token1 |
| `test_p1_cor1_swapFreeRule` | Corollary 1(i) at 13 displacements (from 700 ticks below to 700 above) and three widths of the new range: the token left follows the move and is worth `alpha(l) V` | at +300 ticks, `alpha V` = 1,203,017,385,703,302,005,749 of `V` = 2,021,202,596,517,728,640,715 |
| `test_p1_cor1_standingBalanceBound` | Corollary 1(ii) at four displacements: a balance worth 0.9 `alpha V` in three compositions leaves the token unchanged; `alpha V` in the binding token leaves nothing; 1.1 `alpha V` moves the leftover to the other token | passes at every case |
| `test_p1_cor2_swapCorrectedRule` | Corollary 2 at five displacements and five execution residuals (0, 4% and 50% either way): the value left is `alpha V` times the size of the residual, in the token of Corollary 1 for an undershoot and in the token bought for an overshoot | the paper's example (price at the bound, 4%): 81,012,553,558,670,624,981 left in token1 for the swap too small and 81,012,553,558,670,624,974 in token0 for the swap too large, of 2,025,313,838,966,765,624,454 |

## Sensitivity of the suite

Run on 2026-11-20 in a scratch copy, one fault at a time. The two rows that name a function or a token were run again on 2026-11-22.

| Fault | Tests that fail |
|---|---|
| Model: liquidity halved | all 24 |
| Model: larger in place of smaller liquidity | all 24 |
| Model: mint amounts rounded down, in `V3Math.mint` | the 12 fork tests (placed in `V3Math.amountsUp`, which the network-free tests use as the pool, the fault also fails 6 of the 8 `MasterEquationT1Mock` tests) |
| `ReferencePM`: standing token0 ignored at a rebalance | 5 of the 6 Slipstream tests (the sixth runs with an empty ledger) |
| `ReferencePMUniV3`: the same | 5 of the 6 Uniswap V3 tests |
| `ReferencePM`: one raw unit of token1 over-credited | all 6 Slipstream tests |
| `ReferencePM`: swap leg mis-deducted by one unit | the Slipstream test whose swap pays that token: `test_t1_swapCorrected_predictsDustCredit_slipstream` for token0, `test_p1_swapCorrected_residualSign_slipstream` for token1 |
| `ReferencePM`: opening mint ignores the ledger | the cross-pool and conservation tests |
| Test formula: `alpha` with a wrong denominator | the three corollary tests |
| Test formula: Proposition 1's two denominators exchanged | `test_p1_criterion_arbitraryInputs` |
| Test formula: Corollary 2's token reversed | `test_p1_cor2_swapCorrectedRule` |
| Test formula: the bound of Corollary 1(ii) set at 0.8 `alpha V` | `test_p1_cor1_standingBalanceBound` |

## Not tested here

Theorem 2 has no network-free test: without custody of tokens its statement is an identity of the test's own bookkeeping. Lemma 1 (transfers between positions) is an accounting definition evaluated on the chain record in the paper. Section 6 of the paper (the model of the ledger and propagation of chaos) is checked by proof, simulation and replay, not by this suite.

## Run

```bash
git submodule update --init --recursive
forge build

# Network-free (12 tests)
forge test -vv --no-match-contract Fork

# Full suite (24 tests, needs a Base RPC with archive state)
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test -vv

# One position manager
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract 'Fork$' -vv        # Slipstream
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract 'ForkUniV3$' -vv   # Uniswap V3
```
