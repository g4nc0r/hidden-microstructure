# Foundry verification suite

Foundry verification suite for *The Hidden Microstructure of Shared Balance Concentrated Liquidity: A Master Equation for the Dust Ledger and Propagation of Chaos* (K. R. Ryan, 2026), the multi-pool extension of *The Geometric Siphon* (K. R. Ryan, 2026). Section references in this README and in `PROOF_OUTPUT.md` correspond to the manuscript at `paper/master-equation.tex`.

The suite is **19 tests across 5 contracts**. It verifies the closed-form per-event jump (Theorem 1), the multi-pool mass-conservation result (Theorem 2), and the sign-keyed Connector Rule (Proposition 1). The asymptotic propagation-of-chaos result (Propositions 2A/2B) is verified by simulation outside this suite. See `PROOF_OUTPUT.md` for the captured output and the test-to-section mapping.

## What the suite verifies

| Theorem / claim | Paper section | Test contract | Tests | Network |
|---|---|---|---|---|
| Thm 1, closed-form per-event jump | §4.1, §4.2 | `MasterEquationT1Mock` | 7 | none (mock) |
| Thm 1, same claims against live Aerodrome Slipstream NFPM | §4.1 | `MasterEquationT1Fork` | 4 | Base fork |
| Thm 1, same claims against live Uniswap V3 NFPM | §4.1 | `MasterEquationT1ForkUniV3` | 4 | Base fork |
| Thm 2, multi-pool mass conservation under shared-balance accounting | §5.2 | `MasterEquationT2` | 2 | none (mock) |
| Prop 1, sign-keyed Connector Rule | §5.1 | `MasterEquationConnectorRule` | 2 | none (mock) |

The two parallel fork tracks demonstrate cross-DEX equivalence: closed-form predictions match actuals to within 1 wei on every event on both DEXes, evidencing that the Master Equation governs the architectural class of multi-pool position-manager contracts with depositor-keyed shared dust accounting, not a specific DEX implementation.

## Running

```bash
git submodule update --init --recursive   # first time only

forge build

# Mock-pool tests only, no network access required (11 tests)
forge test -vv --no-match-contract Fork

# Full suite, including the 8 live fork tests on Base (19 tests)
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test -vv

# Slipstream fork only
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract MasterEquationT1Fork$ -vv

# Uniswap V3 fork only
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract MasterEquationT1ForkUniV3 -vv

# Single test
forge test --match-test test_t1_swapfree_zeroDust -vvv

# Gas report
forge test --gas-report
```

Any working Base RPC URL is acceptable in `RPC_BASE_ALCHEMY`. The public endpoint above supports Base archive queries. All eight fork tests are pinned to Base block `43_175_000` (2026-03-10 10:42 UTC), inside the paper's Phase 2 V9 data window. Both the qualitative claims and the captured numerical residuals are bit-reproducible at this pin.

## Architecture

The Master Equation requires a depositor-keyed shared dust mapping `dustBalance[depositor][token]`. A stock NFPM does not maintain such a mapping (every position is an independent NFT that consumes only the tokens its `mint()` is given), so the fork tests verify the equation against minimal reference position-manager contracts that wrap unmodified V3-compatible NFPMs and add the shared ledger.

- **`MockCLPool.sol`** implements the V3 amount equations as a minimal CL pool with a linearised `getSqrtRatioAtTick`. Used by `MasterEquationT2` and `MasterEquationConnectorRule` for the structural claims that do not require V3-exact tick math.
- **`MockCLPoolV2.sol`** has the same surface but uses the exact Uniswap V3 `TickMath` exponential constants verbatim from `v3-core`. Used by `MasterEquationT1Mock` and as the closed-form predictor inside the fork tests, where it is synced to the live pool's `slot0` so that predictions are computed with the same tick math the live pool runs internally.
- **`ReferencePM.sol`** wraps the unmodified Aerodrome Slipstream NFPM (`0x827922686190790b37229fd06084350E74485b72`) and adds the depositor-keyed dust ledger. Pool key is `tickSpacing` (int24). The unit under test in `MasterEquationT1Fork`.
- **`ReferencePMUniV3.sol`** wraps the unmodified Uniswap V3 NFPM (`0x03a520b32C04BF3bEEf7BEb72E919cf822Ed34f1`, factory `0x33128a8fC17869897dcE68Ed026d694621f6FDfD`) and adds the same ledger. Pool key is `fee` (uint24). The unit under test in `MasterEquationT1ForkUniV3`.

Otherwise the two reference PMs are identical: same dust ledger, same rebalance flow, same swap-correction logic, same V3-mechanical math. The mock-pool tests verify the equation directly against the amount functions; no reference PM is under test there, the equation itself is.

## Mathematical foundation

At each rebalance event on pool $P_k$, with withdrawn amounts $(x_w, y_w)$, standing dust $(x_{\text{dust}}, y_{\text{dust}})$ pulled from the shared ledger, and signed swap correction $(\sigma_x, \sigma_y)$, the mint inputs are

```
hat_x = x_w + x_dust − sigma_x,   hat_y = y_w + y_dust − sigma_y
```

The LP-binding solve gives the new liquidity

```
L_new = min(hat_x / g_x,  hat_y / g_y)
```

where $(g_x, g_y)$ are the per-unit-$L$ token amounts at the new range. The dust ledger then jumps to

```
x_dust' = hat_x − L_new · g_x,    y_dust' = hat_y − L_new · g_y
```

with all other tokens' ledger entries unchanged. Off a measure-zero locus exactly one of $(x_{\text{dust}}', y_{\text{dust}}')$ is zero in the swap-free regime, and the non-zero side holds the entire leftover. This is the per-event jump on $D_{\text{pool}}(t)$, turning the ledger into a piecewise-deterministic Markov process whose increments are governed by the V3 mint geometry. See §4 of the paper for the derivation; Theorem 2 of §5.2 gives the multi-pool conservation identity

```
sum_k a_{k,i}(tau) + D_{pool,i}(tau)  =  const
```

for each portfolio token $T_i$, evaluated at the contemporaneous sqrt-price of each event.

## Layout

```
foundry/
├── src/
│   ├── MockCLPool.sol                       linear-tick CL pool (Thm 2, Prop 1)
│   ├── MockCLPoolV2.sol                     exact V3 TickMath CL pool (Thm 1 mock + fork predictor)
│   ├── ReferencePM.sol                      Slipstream-wrapping reference PM
│   ├── ReferencePMUniV3.sol                 Uniswap V3-wrapping reference PM
│   └── interfaces/
├── test/
│   ├── MasterEquationT1Mock.t.sol           Thm 1 (mock, V3-exact)
│   ├── MasterEquationT2.t.sol               Thm 2 (mock, conservation)
│   ├── MasterEquationConnectorRule.t.sol    Prop 1 (mock, sign-keyed correlation)
│   ├── MasterEquationT1Fork.t.sol           Thm 1 against live Slipstream NFPM
│   ├── MasterEquationT1ForkUniV3.t.sol      Thm 1 against live Uniswap V3 NFPM
│   └── helpers/
├── lib/
│   └── forge-std/
├── foundry.toml
├── PROOF_OUTPUT.md
└── README.md
```

## Limitations

- **Propositions 2A and 2B (asymptotic propagation of chaos) are not Foundry-verifiable.** They are large-$N$ distributional limits over many rebalances and are verified by simulation against the V9 lake; the relevant scripts live outside this suite and are referenced from the manuscript §6.2 and Appendix F.
- **`MockCLPool` uses linear tick math.** Order-of-magnitude correct; not used for displacement-level Theorem 1 tests, where the V3-exact `MockCLPoolV2` and the fork tests are the references. The linear mock is adequate for Theorem 2 (mass conservation is structural, independent of tick math) and Proposition 1 (the sign claim is structural).
- **No fees, no slippage in the mock tests.** The mock suites isolate the geometric jump; swap-fee and slippage frictions are orthogonal and analysed separately in the paper.
- **Fork tests are pinned to Base block `43_175_000`** (2026-03-10 10:42 UTC, mid-Phase 2 of the V9 data window). The pin locks the captured numerical residuals in `PROOF_OUTPUT.md` and protects the Slipstream tests against the planned Aerodrome merge in July 2026 (after which Slipstream contract addresses may change). Qualitative claims (closed-form prediction matches actual to within 1 wei) hold at any block where the named NFPMs are deployed and the pools have non-trivial liquidity.

## Dependencies

- Foundry (`forge ≥ 1.5`)
- Solidity 0.8.26
- `forge-std` (cloned into `lib/forge-std`)

## Licence

MIT.
