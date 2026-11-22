# Lean formalisation

[![Lean build](https://github.com/g4nc0r/hidden-microstructure/actions/workflows/lean.yml/badge.svg)](https://github.com/g4nc0r/hidden-microstructure/actions/workflows/lean.yml)
![Lean](https://img.shields.io/badge/Lean-4.32.2-5e81ac)
![mathlib](https://img.shields.io/badge/mathlib-pinned-5e81ac)
![Axiom checks](https://img.shields.io/badge/axiom_checks-136-2e7d32)
![sorry](https://img.shields.io/badge/sorry-none-2e7d32)

Part of [The Hidden Microstructure of Shared Balance Concentrated Liquidity](../README.md).
The fixed-point checks are in [`../foundry/`](../foundry/).

Machine-checked proofs for *The Hidden Microstructure of Shared Balance
Concentrated Liquidity*, written in Lean 4 against mathlib. The scope is the
idealised real-arithmetic model of the paper. The Foundry suite remains the
check against fixed-point pool arithmetic, and the chain record remains the
empirical check.

The library root is `MasterEquation.lean`. The V3 amount functions and the mint
linear programme of Theorem 1 live in `MasterEquation/Defs.lean`, which every
other file imports. File names follow the mathlib convention of descriptive
content names. Statements and sections are named as in the November 2026
revision of the paper. Equation numbers are not cited, since they move between
versions.

The `Lnew` and ledger-entry definitions are a copy of the corresponding surface
in the Geometric Siphon formalisation, generalised from the isolated
single-pool case to arbitrary mint inputs. That repository owns the original.
Programme convention is to share by copy, not by symlink.

This is a formalisation, meaning machine-checked proofs of mathematical
statements. It is not a check of contract code against a specification.

## Coverage at a glance

| Paper result | Section | File | What is machine-checked |
|---|---|---|---|
| Theorem 1 (Master Equation jump) | §4.1 | `MasterJump` | In full, with both boundary sub-cases and the single-pool corner |
| Proposition 1 (binding-side criterion) | §5.1 | `BindingSide` | In full: the three cases and the value of the leftover in each |
| Corollary 1 (swap-free rule) | §5.1 | `BindingSide` | In full: part (i) inside the old range and at or beyond either bound; part (ii) in its three clauses, in terms of `α(ℓ)` inside the old range and in terms of the surplus at or beyond a bound |
| Corollary 2 (swap-corrected rule) | §5.1 | `BindingSide` | In full, as an identity for every residual, with the condition under which the swap is feasible stated separately; in terms of `α(ℓ)` inside the old range and in terms of the surplus, which is then the whole withdrawn value, at or beyond a bound |
| Theorem 2 (mass conservation without a swap) | §5.2 | `Conservation` | In full, in real arithmetic |
| Lemma 1 (transfers sum to zero) | §5.2 | `Transfers` | In full, parts (i) to (iv), under the mint's budget |
| The hub-spoke kernel | §6.1 | `DirectionKernel` | Derived from Theorem 1 on the leading-order inputs, and shown equal to the paper's case form |
| Lemma 2 (stationary law) | §6.1 | `DirectionKernel` | The deterministic parts only: the `ℓ¹` identity, the invariant set, the contraction for one mark. Not the stationary law |
| Proposition 2 (propagation of chaos at rate `1/N`) | §6.1 | `DirectionKernel` | The one-register property only. Not the proposition |
| Proposition 3 (spoke marginal, exact atom and slack-side approximation) | §6.1 | `DirectionKernel`, `SpokeMarginal` | The side identity behind the atom, exactly; the value of the atom; the pointwise slack-side distance; the leading-order mixture. Not the stationary-law step |
| Remark after Proposition 3 (the Gaussian case, half-normal mixture) | §6.1 | `SpokeMarginal`, `GaussianMoment` | `q = 1/2` and the half-normal mean, for the Gaussian without conditioning to `[-K, K]` |
| Proposition 4 (unequal spokes) | §6.2 | none | Not formalised |
| Proposition 5 (a common direction) | §6.2 | none | Not formalised |
| Lemma 3 (zero indicators) | §6.2 | none | Not formalised |
| Proposition S1 of the supplement (drift of position size) | §6.3; supplement §7.4 | `DirectionKernel` | Parts (i) and (iii) in full; part (ii) as an integral over the residual law; part (iv) as an algebraic identity between conditional means |

## Coverage in detail

### Theorem 1 (Master Equation jump)

`MasterEquation/MasterJump.lean`:

- `lnew_isGreatest` - the closed form `L_new = min(x̂/g_x, ŷ/g_y)` is the
  optimum of the mint LP, stated as `IsGreatest` over the feasible set, so the
  LP formulation is part of the theorem and not an assumption.
- `dust_nonneg`, `dust_mul_eq_zero` - the new ledger entries are non-negative
  and at least one vanishes.
- `dustX_eq_zero_iff`, `dustY_eq_zero_iff` - the binding side as an exact iff
  on the supply ratio against the required ratio.
- `dust_both_zero_iff`, `exactly_one_dust_zero` - both entries vanish exactly
  on the ratio-preserving locus `x̂ g_y = ŷ g_x`, and off it exactly one
  vanishes with the other strictly positive.
- `slack_leftover_of_token0_binds`, `dust_add_eq_abs_sub` - the closed-form
  leftover, and the total leftover as the input imbalance.
- `dust_of_proportional_requirements` - when the new range takes the tokens in
  a fixed ratio `g_y = r g_x`, the entries are the positive and negative parts
  of the imbalance of the inputs. This is the form the corollaries and the
  kernel use (`r = s²` for a range centred in tick space, `r = 1` in common
  units).
- `lp_below_range`, `lp_above_range` - the boundary sub-cases (ii) and (iii) of
  the proof. These lie outside the theorem's hypothesis and are recorded for
  completeness, as they are in the paper.
- `lnew_gs_corner` - the single-pool swap-free corner reduces to the isolated
  mint minimum of the prior paper.

### Proposition 1 and Corollaries 1 and 2

`MasterEquation/BindingSide.lean`. Values are in units of token 1 at the mint
price `s`.

The criterion:

- `shareSupplied`, `shareRequired` - the shares `ω̂` and `ω'` of token 0 in the
  value supplied and in the value required.
- `share_sub`, `share_lt_iff`, `share_gt_iff`, `share_eq_iff` - the comparison
  of the two shares is the comparison of `x̂ g_y` with `ŷ g_x`.
- `criterion_leftover_token1` - if `ω̂ < ω'` the leftover is in token 1 and is
  worth `Ŵ (ω' - ω̂) / ω'`.
- `criterion_leftover_token0` - if `ω̂ > ω'` it is in token 0 and is worth
  `Ŵ (ω̂ - ω') / (1 - ω')`.
- `criterion_no_leftover` - if the shares agree nothing is left.

Ranges centred in tick space:

- `centred_requirements`, `shareRequired_centred` - a new range with
  `sa' sb' = s²` takes the two tokens in equal value, so `ω' = 1/2`.
- `withdrawn_mismatch`, `withdrawn_value` - the surplus and the value of a
  position withdrawn inside an old range with `sa sb = s₀²`.
- `alpha`, `alpha_eq_sinh` - the share `α` is defined algebraically in `s`,
  `s₀`, `sb`, and identified with the paper's `sinh|ℓ| / (e^h - cosh ℓ)` at
  `s = s₀ e^ℓ`, `sb = s₀ e^h`.
- `mismatch_eq_alpha_value_up`, `mismatch_eq_alpha_value_down` - the surplus is
  `α V`, in token 1 after an upward move and in token 0 after a downward one.

Corollary 1:

- `swapfree_rule_up`, `swapfree_rule_down` - part (i) inside the old range: the
  token left and the amount `α V`.
- `swapfree_rule_exit_above`, `swapfree_rule_exit_below` - part (i) at or
  beyond a bound: the whole withdrawn value is left.
- `swapfree_rule_up_with_balance`, `swapfree_rule_down_with_balance` - part
  (ii), first clause: a standing balance worth less than `α V` leaves the
  leftover in the same token. Only the non-negativity of the balance's part in
  the surplus token is used.
- `balance_equal_surplus_removes_token1`, `balance_equal_surplus_removes_token0`
  - second clause: a balance worth exactly the surplus, held wholly in the
  token the swap-free mint uses up, removes the leftover.
- `balance_above_surplus_reverses_token1`,
  `balance_above_surplus_reverses_token0` - third clause: a larger one moves it
  to that token.

Corollary 2:

- `swapcorrected_rule_up`, `swapcorrected_rule_down` - with a swap of value
  `Q = α V (1 + ε) / 2`, the two ledger entries are the negative and positive
  parts of `α V ε`. The leftover is in the token of Corollary 1(i) for `ε < 0`
  and in the token the swap bought for `ε > 0`.
- `swapcorrected_leftover_value` - on whichever token it falls it is worth
  `α V |ε|`.
- `swapcorrected_surplus_token1`, `swapcorrected_surplus_token0` - the same
  statement for any surplus `m` in place of `α V`. At or beyond a bound of the
  old range, where `α = 1` and the paper's example sits, the corollary is this
  form with `m = V`; the two theorems above are stated strictly inside the
  range.
- `swap_feasible_token1`, `swap_feasible_token0` - the swap leaves a
  non-negative amount of the surplus token for the mint exactly when
  `α ε ≤ 1`. See the note under Findings.

The statements with `α V` replaced by a general surplus `m` are
`swapfree_surplus_token1`, `swapcorrected_surplus_token1` and their mirrors.

### Theorem 2 (multi-pool mass conservation without a swap)

`MasterEquation/Conservation.lean`. The event is declared as a `Rebalance`
structure whose fields are the paper's hypotheses. One pool moves, its position
holds nothing outside its own pool, the mint inputs recycle the pool's standing
balance, the leftover is credited to the ledger, and entries for tokens outside
the pool are untouched.

- `Rebalance.mass_conservation` - the per-token total `M_i` is invariant across
  the event.
- `Rebalance.value_conservation` - the fixed-price aggregate inherits it.
- `impacts_add_ledger_change_eq_zero`, `mixed_sign_of_sum_zero` - two
  accounting identities over a window. The second is used for Lemma 1(ii).

### Lemma 1 (transfers sum to zero)

`MasterEquation/Transfers.lean`. Entitlements `G k ≥ 0` over a finite family of
positions; at a rebalance of position `j` the transfer is
`Ξ = (V_new - (V_j + G_j) + σ)⁺`, taken from the others in proportion to their
entitlements.

- `sum_netTransfer_eq_zero` - part (i): the net transfers of one event sum to
  zero, with or without a swap.
- `sum_entitlementAfter` - part (i): the entitlements after the event sum to
  the ledger's value after it.
- `entitlementAfter_nonneg` - entitlements stay non-negative.
- `sum_cumulative_eq_zero`, `receiver_and_giver` - part (ii): over any window
  the cumulative net transfers sum to zero, and are either all zero or include
  a net receiver and a net giver.
- `transfer_eq_zero_of_alone`, `others_eq_zero_of_subsingleton` - part (iii): a
  lone position gives and receives nothing.
- `value_change` - part (iv): `ΔV_j = ξ_j - σ - (G_j' - G_j)`.

The hypothesis beyond the definitions is the mint's budget,
`V_new ≤ V_j + ∑ G - σ`: a position cannot mint more than its own withdrawn
value and the whole ledger. `transfer_le_others` shows that under it the
transfer never exceeds what the others are owed, which is what makes the
proportional split well defined.

### The hub-spoke kernel, Lemma 2, Propositions 2 and 3, and Proposition S1

`MasterEquation/DirectionKernel.lean`. The hub token is at the token-0
position, `η ∈ {+1, -1}` is the direction, `ε` the execution residual and
`A = Lw + η (B - H)` the imbalance.

The kernel:

- `inputs_up`, `inputs_down` - the post-swap inputs in each direction, written
  as the exact swap times `1 + ε`.
- `hat_diff` - the swap routed at the spot price collapses the swap noise to one
  residual, `x̂ - ŷ = c₀ η A ε`. The file gives the residual term of the
  spoke-token input a slope `sh2` and takes `c₀ = (1 + sh2) / 2`, the form of
  the earlier versions. The paper's kernel is the case `sh2 = 1`, with both
  inputs valued in one unit and `c₀ = 1`. Every statement after
  `kernel_eq_master_jump` up to the section on position size is proved for a
  general constant `c₀` (non-negative, and positive for the two side
  identities), which is how the paper states them. The statements on position
  size take `c₀ = 1`, as Proposition S1 does.
- `kernel_eq_master_jump` - the kernel is Theorem 1's jump applied to those
  inputs, not a separately posited rule.
- `hubPost_eq_ite`, `spokePost_eq_ite` - agreement with the paper's case form:
  leftover `c₀ |A| |ε|` on the hub if `η A ε > 0`, on the spoke otherwise.
- `post_mul_eq_zero`, `leftover_magnitude` - one entry is zero and the other is
  `c₀ |A| |ε|`.

Deterministic parts of Lemma 2:

- `l1_identity`, `l1_contraction` - for two states under one mark the distance
  after the event is `c₀ |ε|` times the difference of the imbalances, hence at
  most `c₀ |ε|` times the distance before.
- `bstar_fixed`, `bstar_lt`, `post_le_bstar`, `imbalance_pos` - the set
  `[0, b*]` is invariant, and on it the imbalance is positive exactly because
  `κ < 1/2`.
- `step_l1_contraction` - the full chain for one event: the `ℓ¹` distance of
  two copies falls by at least `(1 - c₀ |ε|)` times the distance in the two
  entries rewritten.
- `step_l1_contraction_sum` - summed over the firing pool, the factor is
  `N - (1 - c₀ |ε|)`, which is `1 - (1 - c₀ |ε|) / N` per uniformly drawn pool.
- `sq_post`, `sq_drift_pointwise`, `sq_drift_integral` - the drift of the
  squared norm for a residual with `c₀² E[ε²] < 1/2`.

For Proposition 2:

- `theta`, `step_eq_theta` - on a non-negative imbalance each event is an
  affine map of the state.
- `one_register_step`, `one_register` - under the affine map a change made to
  one entry is, after any finite sequence of events, a change in exactly one
  entry, by a weight, and both the entry and the weight are functions of the
  events alone. This is the property the proof of the rate rests on.

For Proposition 3:

- `spokePost_eq_zero_iff`, `hubPost_eq_zero_iff` - on a positive imbalance the
  spoke's entry is zero after the event exactly when `η ε ≥ 0`, and the hub's
  exactly when `η ε ≤ 0`.
- `spokePost_slack`, `slack_side_bound` - the slack-side leftover is
  `c₀ A |ε|`, and with both balances in `[0, b]` it differs from `c₀ Lw |ε|` by
  at most `c₀ |ε| b`.

For Proposition S1 of the supplement (`c₀ = 1`):

- `new_liquidity_value` - the size update follows from the mint.
- `size_conservation` - part (i).
- `size_drift_integral` - part (ii), as an integral over the residual law given
  the direction.
- `own_value_change`, `hubPost_up`, `hubPost_down` - part (iii).
- `own_value_gap_drift` - part (iv), as the algebraic identity that follows
  from part (iii) once the conditional means of the residual are given.

`MasterEquation/SpokeMarginal.lean`:

- `atom_exact` - the side identity as a statement of probability: under any
  joint law of state and mark with positive imbalance, the probability that the
  spoke's entry is zero after the event is the probability that `η ε ≥ 0`. No
  independence is used.
- `atom_eq_direction_mixture` - the value of the atom,
  `q = p₊ ν₊[0, ∞) + p₋ ν₋(-∞, 0]`.
- `atom_half_of_common_law` - with one residual law for both directions, no
  atom at zero and equal directions, `q = 1/2` whatever the law.
- `spoke_marginal_mixture`, `atom_mass` - the leading-order law of the spoke's
  entry is `q δ₀ + (1 - q) ρ₊` as a measure identity, with mass exactly `q` at
  zero.
- `atom_half_of_symmetric`, `gaussian_atom`, `gaussian_spoke_atom` - the
  `q = 1/2` of the Gaussian case of Proposition 3, for any symmetric law without an atom at zero and any
  probabilities of the two directions.

`MasterEquation/GaussianMoment.lean`:

- `integral_Ioi_mul_exp_neg_mul_sq`, `integral_Ioi_gaussianReal` - the
  one-sided first moment of a mean-zero Gaussian, which mathlib does not have.
- `two_mul_oneSided_eq`, `conditional_mean_eq` - the mean of the Gaussian case,
  `β √(2/π)`, where `β` is the half-normal scale the paper writes σ_hn, with
  `c₀` written as `(1 + sh2) / 2`.

## Scope: what is not formalised

- **The stationary law (Lemma 2).** Existence, uniqueness, convergence in the
  Wasserstein distance and tightness are statements about laws of the chain.
  What is checked is every deterministic step they use. The mean of the
  contraction over the mark, which turns `c₀ |ε|` into `κ₁`, is not taken.
- **Proposition 2.** The bound in `W₁`, the fixed point `(π_H, μ)`, the exact
  covariances of the Remark and the statement that the rate is attained are not
  formalised. The proof's first step, the one-register property, is.
- **Proposition 3 beyond the kernel.** That the stationary law of a spoke's
  entry is its law after its own last event, and the `W₁` bound on the
  slack-side law, which follows from `slack_side_bound` by a coupling, are not
  formalised.
- **Propositions 4 and 5 and Lemma 3.** Not formalised. Lemma 3's premise for
  the kernel is the side identity above.
- **The conditioning in the Gaussian case.** The Gaussian here is not conditioned to
  `[-K, K]`. The atom statement holds for any symmetric law without an atom at
  zero, which includes the conditioned one; the mean is for the Gaussian
  itself.
- **The expectations of Proposition S1.** Part (iv) is checked as algebra on given
  conditional means, not as an expectation over the mark and the firing pool.
- **The `O(w)` remainder control.** Leading-order expressions are taken as
  definitions, as the file headers state: the position withdrawn at a bound is
  worth `Lw`, the new range takes equal amounts in the kernel's units, and the
  swap is the exact amount times `1 + ε`.
- **Fixed-point arithmetic** remains the Foundry suite's job. Everything here
  is over `ℝ`, so tick rounding and the integer remainders in Theorem 2's
  statement are outside the model.
- **The model and the deployed contract.** That the declared `Rebalance`
  structure and the kernel describe a deployed manager is an empirical matter,
  which the paper treats in its sections on simulation and on the chain record.

## Findings

Two points came out of the formalisation, and the paper's statements now
carry both. Neither changed a result.

- **Corollary 2 needs an upper bound on the residual.** The corollary's swap
  sells value `Q = α V (1 + ε) / 2` of the surplus token. The amount of that
  token left for the mint is non-negative exactly when `α ε ≤ 1`
  (`swap_feasible_token1`, `swap_feasible_token0`), and the paper states the
  corollary for `-1 < ε ≤ 1/α`. The identity for the leftover holds for every
  `ε`.
- **Lemma 1 uses the mint's budget.** `V_new ≤ V_j + ∑ G - σ` is what makes the
  proportional split well defined when the transfer is positive, and it is what
  makes a lone position's transfer zero. It follows from Theorem 1's
  feasibility constraint at fixed prices and is stated as a hypothesis here; the
  paper says it in the paragraph before the lemma.

## Earlier versions

The formalisation of the July 2026 version of the paper is in the repository
history, at commit `a39d5ef`, the last before this revision. It held three files
that the revision does not keep: `HubSpoke.lean`, the hub-spoke kernel as that
version printed it; `Doeblin.lean`, a note on an assumption that version made
and the revision no longer makes; and `ConnectorRule.lean`, which formalised the
statement that earlier versions gave as Proposition 1 and is replaced by
`BindingSide.lean`. None of the three is a statement of the revised paper.

## Building

Requires elan, the Lean toolchain manager. The pinned toolchain is in
`lean-toolchain`; mathlib is pinned by `lake-manifest.json`, at the same
revision as the Geometric Siphon formalisation.

```
lake exe cache get   # fetch prebuilt mathlib (several GB, one-off)
lake build
```

Axiom audit, confirming that every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`, and that none contains a `sorry`:

```
lake env lean AxiomCheck.lean
```

136 checks, all clean.

## Licence

MIT. See [`../LICENSE`](../LICENSE).
