# Simulation

![Python](https://img.shields.io/badge/Python-3.9+-3776ab?logo=python&logoColor=white)
![NumPy](https://img.shields.io/badge/needs-NumPy-4d77cf?logo=numpy&logoColor=white)

Part of [The Hidden Microstructure of Shared Balance Concentrated Liquidity](../README.md). The model is that of §6 of the paper, and the runs are those of §7.1 and of Tables S1 and S2 of the supplement.

The hub-spoke kernel of the paper in Python: one hub token shared by *N* pools, each event drawing a pool, a direction and an execution residual, and leaving the leftover on the hub or on that pool's spoke token. The statements of §6 about this chain are laws over many events (a stationary law, independence at rate 1/*N*, the mass at zero of a spoke's balance). The Lean files cover what holds at one event and not these laws, so this folder is the check of them that a reader can run.

Three residual laws are included, each inside assumption (A1′): Gaussian, uniform and skewed, as defined in §7.1. The paper's fourth law, measured on the chain record, is not published. The simulations of the deployed contract (§7.2) and the replays of the chain record (§8.4) are not here either. The exact engine that the contract simulations extend is the simulator in the repository of [*The Geometric Siphon*](https://github.com/g4nc0r/the-geometric-siphon).

## Files

| File | Contents | Needs |
|---|---|---|
| [`kernel.py`](./kernel.py) | The kernel: many independent chains at once in float64, and the same rule on exact rationals | NumPy |
| [`laws.py`](./laws.py) | The three residual laws and their exact constants (*q*, κ₁, γ±, χ±, *b*\*), the exact mean balances and the exact covariances of the Remark after Proposition 2 | NumPy |
| [`check_exact.py`](./check_exact.py) | The float kernel against exact arithmetic, with the single-event facts the proofs use asserted at every event | NumPy |
| [`reproduce.py`](./reproduce.py) | The tables below | NumPy |

## Running

```bash
python3 laws.py                 # the constants of the three laws
python3 check_exact.py          # two seconds
python3 reproduce.py --quick    # under a minute
python3 reproduce.py            # about four minutes
python3 reproduce.py --long     # about half an hour, N up to 256
```

Seeds are fixed, so a run repeats. The paper's runs used many more events on a GPU, so the figures here agree with the paper's within Monte Carlo error and not digit for digit. Standard errors, in brackets below, are taken across 16 groups of independent chains.

## The exact check

`check_exact.py` runs 4,000 events of a five-pool chain in rational arithmetic, for two ledgers under the same events, and asserts at every event that

- one of the two entries the event touches is zero, and the spoke's is zero exactly when ηε ≥ 0 (the side rule behind the atom of Proposition 3);
- every balance stays at or below *b*\* and the imbalance stays positive (the invariant set of Lemma 2);
- the ℓ¹ distance between the two ledgers over the touched entries is |ε| times the difference of their imbalances (the identity behind the contraction of Lemma 2).

The float64 kernel stays within 10⁻¹⁶ of the exact ledger throughout.

## What `reproduce.py` prints

From a default run (`Lw` = 1, *c*₀ = 1).

**The mass at zero and the mean balances**, against *q* of Proposition 3 and the exact means. The atom does not depend on *N*.

| Law | *N* | P(*B* = 0) | *q* | Mean spoke balance | Exact | Mean hub balance | Exact |
|---|---|---|---|---|---|---|---|
| Gaussian | 64 | 0.49993 (0.00005) | 0.5000 | 0.019950 (0.000003) | 0.01995 | 0.019944 (0.000002) | 0.01995 |
| Uniform | 64 | 0.50006 (0.00005) | 0.5000 | 0.112485 (0.000015) | 0.11250 | 0.112510 (0.000013) | 0.11250 |
| Skewed | 64 | 0.71870 (0.00005) | 0.7188 | 0.033582 (0.000006) | 0.03359 | 0.099015 (0.000006) | 0.09901 |

**The dependence between balances, each times *N***, against the exact covariances of the Remark after Proposition 2 and against Table S2 of the supplement. The products are constant in *N*, which is the rate 1/*N* of Proposition 2. Under the uniform law the balances are uncorrelated and the correlation is that of their squares, as in the paper.

| Law | *N* | *N* Cov(*B*₁, *B*₂) | Exact | *N* Cov(*H*, *B*) | Exact | *N* ρ | Table S2 |
|---|---|---|---|---|---|---|---|
| Skewed | 2 | −0.000097 (0.000001) | −0.000098 | −0.003263 (0.000001) | −0.003263 | −0.0198 (0.0002) | −0.0201 |
| Skewed | 8 | −0.000098 (0.000001) | −0.000097 | −0.003219 (0.000001) | −0.003219 | −0.0201 (0.0003) | −0.0199 |
| Skewed | 64 | −0.000095 (0.000005) | −0.000096 | −0.003202 (0.000005) | −0.003206 | −0.0196 (0.0010) | −0.0197 |
| Uniform | 2 | −0.000002 (0.000003) | 0 | −0.012654 (0.000002) | −0.012656 | −0.0031 (0.0001) | −0.0031 |
| Uniform | 8 | +0.000004 (0.000008) | 0 | −0.012654 (0.000006) | −0.012656 | −0.0031 (0.0003) | −0.0031 |
| Uniform | 64 | +0.000026 (0.000017) | 0 | −0.012661 (0.000010) | −0.012656 | −0.0029 (0.0007) | −0.0032 |

**The Gaussian case at *N* = 1024**, the non-zero balance against the half-normal law of scale 0.05 (Table S1 of the supplement, whose ratios are in the last column).

| Quantity | Simulated | Closed form | Ratio | Table S1 |
|---|---|---|---|---|
| P(*b* = 0) | 0.49998 | 0.50000 | 1.0000 | 1.0000 |
| E[*b* \| *b* > 0] | 3.9868 × 10⁻² | 3.9894 × 10⁻² | 0.9993 | 1.0000 |
| Var(*b* \| *b* > 0) | 9.1167 × 10⁻⁴ | 9.0845 × 10⁻⁴ | 1.0035 | 1.0047 |
| quantile 0.10 | 6.2699 × 10⁻³ | 6.2831 × 10⁻³ | 0.9979 | 0.9972 |
| quantile 0.50 | 3.3660 × 10⁻² | 3.3724 × 10⁻² | 0.9981 | 0.9982 |
| quantile 0.90 | 8.2262 × 10⁻² | 8.2243 × 10⁻² | 1.0002 | 1.0001 |

**The contraction of Lemma 2.** Two ledgers under the same events, one empty and one with every entry at *b*\*. The lemma bounds their mean distance after *n* events by (1 − (1 − κ₁)/*N*)ⁿ, so the measured rate times *N* is at least 1 − κ₁ and the distance never exceeds the bound. The last column is the range the paper records in its Table 3.

| Law | *N* | *N* × rate | 1 − κ₁ | Largest distance over bound | Table 3 |
|---|---|---|---|---|---|
| Gaussian | 16 | 1.020 | 0.960 | 0.939 | 0.98 to 1.08 |
| Gaussian | 256 | 0.981 | 0.960 | 0.994 | 0.98 to 1.08 |
| Uniform | 16 | 0.898 | 0.775 | 0.927 | 0.87 to 0.95 |
| Uniform | 256 | 0.872 | 0.775 | 0.982 | 0.87 to 0.95 |
| Skewed | 16 | 0.992 | 0.867 | 0.933 | 0.92 to 1.11 |
| Skewed | 256 | 0.959 | 0.867 | 0.984 | 0.92 to 1.11 |

The rate is read while the mean distance is above 10⁻⁴ of its start. Later than that the mean rests on the few chains in which some pool has not yet fired, and a run of this size does not determine it. The paper's runs read a longer window on more chains.

## What is not reproduced

The measured law and every figure that rests on it. The decoupling gap of Table S2. The runs on unequal spokes, position size and a common direction (Table S3 of the supplement). The dependence between balances above *N* = 256.

## Licence

MIT, as for the rest of the code in this repository. See [`../LICENSE`](../LICENSE).
