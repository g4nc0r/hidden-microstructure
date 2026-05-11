# The Hidden Microstructure of Shared Balance Concentrated Liquidity

Paper source and Foundry verification code for *The Hidden Microstructure of Shared Balance Concentrated Liquidity: A Master Equation for the Dust Ledger and Propagation of Chaos* (K. R. Ryan, 2026).

The paper is the multi-pool extension of *The Geometric Siphon*. Under a position manager that retains the per-event geometric residual in a depositor-keyed dust ledger shared across multiple pools, the residual stops being a per-rebalance leftover and becomes a hidden state variable coupling the portfolio. Theorem 1 (the Master Equation) gives the exact closed-form per-event jump law on any pool, Theorem 2 generalises zero-swap extinction to a per-token mass-conservation identity across multi-pool rebalances with a donor/absorber partition under heterogeneous arrival, and Proposition 1 promotes the prior paper's Connector Rule conjecture to a sign-keyed correlation. On the homogeneous hub-spoke topology, Propositions 2 and 3 establish a conditional propagation-of-chaos limit and a closed-form atom-mixture spoke marginal, with a half-normal special case under symmetric Gaussian slippage. A 19-test Foundry suite verifies the closed-form jump (Theorem 1), the conservation result (Theorem 2), and the Connector Rule sign (Proposition 1) against unmodified V3-compatible NFPMs on Base mainnet, with two parallel fork tracks against Aerodrome Slipstream and Uniswap V3 demonstrating cross-DEX equivalence.

| | |
|---|---|
| **Author** | K. R. Ryan, independent researcher |
| **Contact** | [gancor.xyz](https://gancor.xyz) · ORCID [0009-0004-6295-7040](https://orcid.org/0009-0004-6295-7040) · code/reproduction questions via [GitHub Issues](https://github.com/g4nc0r/hidden-microstructure/issues) |
| **Companion paper** | [*The Geometric Siphon* (SSRN 6686798)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6686798) |
| **Foundry** | `forge` ≥ 1.5; Solidity 0.8.26 |
| **Licence** | code MIT (`LICENSE`); paper PDF and LaTeX source © K. R. Ryan, all rights reserved |

**Status.** SSRN abstract [6745218](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6745218) submitted and pending approval; the preprint will be the citable record once visible. The Foundry verification suite reproduces every closed-form claim in the paper bit-exactly.

## Paper

| Title | Where | Status |
|---|---|---|
| The Hidden Microstructure of Shared Balance Concentrated Liquidity: A Master Equation for the Dust Ledger and Propagation of Chaos | [SSRN 6745218](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6745218); source in `paper/` | Preprint, pending SSRN approval |

## Citation

Cite the SSRN preprint once it goes live. The parent paper is the companion citation:

```bibtex
@techreport{ryan2026hiddenmicrostructure,
  author      = {Ryan, K. R.},
  title       = {The Hidden Microstructure of Shared Balance Concentrated
                 Liquidity: A Master Equation for the Dust Ledger and
                 Propagation of Chaos},
  institution = {SSRN},
  number      = {6745218},
  year        = {2026},
  url         = {https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6745218}
}

@techreport{ryan2026siphon,
  author      = {Ryan, K. R.},
  title       = {The Geometric Siphon},
  institution = {SSRN},
  number      = {6686798},
  year        = {2026},
  url         = {https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6686798}
}
```

A `CITATION.cff` with the same metadata is included at the repository root.

## Quick start

```bash
# Foundry suite (19 tests, ~3s mock + ~1min fork)
cd foundry
git submodule update --init --recursive
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test
# expected: Suite result: ok. ... 19 tests passed, 0 failed, 0 skipped
```

## Layout

```
.
├── paper/                      LaTeX source (master-equation.tex), figure, build PDF
├── foundry/                    Foundry verification suite (19 tests, 5 contracts)
│   ├── src/                      MockCLPool.sol, MockCLPoolV2.sol,
│   │                             ReferencePM.sol (Slipstream wrapper),
│   │                             ReferencePMUniV3.sol (Uniswap V3 wrapper)
│   ├── test/                     5 test contracts + helpers/ + interfaces/
│   ├── PROOF_OUTPUT.md           captured forge test output
│   └── README.md
├── CITATION.cff
├── LICENSE
└── README.md
```

## Foundry verification suite

19 tests across 5 contracts. Eleven mock-pool tests are network-free and verify Theorem 1, Theorem 2, and Proposition 1 against the V3-exact tick math directly. Eight live fork tests, all pinned to Base block `43_175_000`, verify Theorem 1 against two unmodified V3-compatible `NonfungiblePositionManager` contracts on Base. The two parallel fork tracks (Aerodrome Slipstream and Uniswap V3) demonstrate cross-DEX equivalence: closed-form predictions match actuals to within 1 wei on every event on both DEXes. Test-to-section mapping is in [`foundry/PROOF_OUTPUT.md`](./foundry/PROOF_OUTPUT.md); a per-contract description is in [`foundry/README.md`](./foundry/README.md).

```bash
cd foundry
git submodule update --init --recursive   # first time only

# Mock-pool tests only, no network access required (11 tests)
forge test -vv --no-match-contract Fork

# Full suite, including 8 live fork tests on Base (19 tests)
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test -vv

# Slipstream fork tests only
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract MasterEquationT1Fork$ -vv

# Uniswap V3 fork tests only
RPC_BASE_ALCHEMY=https://mainnet.base.org forge test --match-contract MasterEquationT1ForkUniV3 -vv
```

Any Base RPC URL with archive support works in `RPC_BASE_ALCHEMY`. Fork tests are pinned to Base block `43_175_000` (matching the *Geometric Siphon* suite's pin), so captured numerical residuals are bit-reproducible. Forge caches RPC responses under `~/.foundry/cache`, so repeat runs are fast.
