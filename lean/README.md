# Lean formalisation

Machine-checked proofs of the theorem layer of *The Hidden Microstructure of
Shared Balance Concentrated Liquidity*, written in Lean 4 against mathlib. The
scope is the idealised real-arithmetic model of the paper. The Foundry suite
under `../foundry/` remains the check against fixed-point pool arithmetic, and
the V9 walks remain the empirical check.

The library root is `MasterEquation.lean`. The V3 amount functions of Appendix
B and the mint linear programme of Theorem 1 live in `MasterEquation/Defs.lean`,
which every other file imports. File names follow the mathlib convention of
descriptive content names; the mapping to the paper's numbering is recorded
below and in each file's doc comments. All statements refer to the July 2026
revision of the manuscript.

The `Lnew` and dust-credit definitions are a copy of the corresponding surface
in the Geometric Siphon formalisation, generalised from the isolated
single-pool case to arbitrary mint inputs. That repository owns the original.
Programme convention is to share by copy, not by symlink.

## Coverage

`MasterEquation/MasterJump.lean` - Theorem 1 (Master Equation jump), §4.1 and
Appendix A:

- `lnew_isGreatest` - the closed form `L_new = min(x̂/g_x, ŷ/g_y)` is the
  optimum of the mint LP, stated as `IsGreatest` over the feasible set of
  eq. (A.1), so the LP formulation is part of the theorem rather than an
  assumption.
- `dust_nonneg`, `dust_mul_eq_zero` - the credits are non-negative and at least
  one vanishes, which is the LP-min structure of the theorem statement.
- `dustX_eq_zero_iff`, `dustY_eq_zero_iff` - the binding side as an exact iff
  on the supply ratio against the required ratio.
- `dust_both_zero_iff`, `exactly_one_dust_zero` - the ratio-preserving locus
  `x̂ g_y = ŷ g_x` is where both credits vanish, and off it exactly one
  vanishes with the other strictly positive.
- `slack_leftover_of_token0_binds`, `dust_add_eq_abs_sub` - the closed-form
  slack-side leftover, and the total leftover as the input imbalance.
- `lp_below_range`, `lp_above_range` - Appendix A's boundary sub-cases (ii) and
  (iii). These lie outside the theorem's hypothesis and are recorded for
  completeness, as they are in the paper.
- `lnew_gs_corner` - the single-pool swap-free corner reduces to the isolated
  mint minimum of the prior paper.

`MasterEquation/Conservation.lean` - Theorem 2 (multi-pool mass conservation
under `S = 0`), §5.2 and Appendix C. The event is declared as a `Rebalance`
structure whose fields are the paper's hypotheses. One pool moves, its position
holds nothing outside its own pool, the swap-free mint inputs recycle the
pool's standing dust, the leftover is credited to the ledger, and entries for
tokens outside the pool are untouched.

- `Rebalance.mass_conservation` - the per-token total `M_i` of eq. (7) is
  invariant across the event.
- `Rebalance.value_conservation` - the fixed-price USD aggregate inherits it.
- `impacts_add_ledger_change_eq_zero` - the window accounting identity behind
  the donor/absorber remark.
- `mixed_sign_of_sum_zero` - the deterministic core of Lemma 1. Given the
  conservation constraint, any departure from the all-zero impact profile is a
  non-trivial donor/absorber partition. Lemma 1's probabilistic content, that
  the all-zero profile is not the typical one under heterogeneous arrival rates
  and ranges, is not formalised.

`MasterEquation/ConnectorRule.lean` - Proposition 1 (Connector Rule under V3
mechanics), §5.1 and Appendix B:

- `token1_binds_iff`, `token0_leaks` - Appendix B's per-rebalance binding side,
  exactly.
- `exit_above_leaks_token1`, `exit_below_leaks_token0` - the reduction of the
  binding condition to a sign condition on displacement, proved at the boundary
  trigger of (A2) where the withdrawn position is single-sided. That is the
  regime in which the sign rule is exact rather than a tendency.
- `signedDustT0_pos_of_token1_leaks`, `signedDustT0_neg_of_token0_leaks`,
  `signedDustT1_eq_neg` - signed connector-side dust carries the sign of the
  displacement at the `T0` position and the opposite sign at `T1`, which is the
  sign-by-position prediction the prior paper's `T1`-only sample could not
  test.
- `concordance_nonneg`, `concordance_nonpos_of_neg` - under the two-valued
  boundary trigger, the per-rebalance sign rule alone forces a sign-keyed
  sample covariance across the population.

`MasterEquation/HubSpoke.lean` - the homogeneous hub-spoke kernel of Appendix D:

- `hat_diff` - eq. (D.3). The routing conservation collapses the swap noise to
  the single residual `x̂ - ŷ = (Lw + b - h)(1 + s_h²) ε / 2`.
- `dust_of_symmetric_requirements`, `kernel_eq_master_jump` - eq. (8) is
  Theorem 1's jump applied to the post-swap inputs under symmetric routing,
  rather than a separately posited kernel.
- `spoke_binds_iff`, `leftover_magnitude`, `post_mul_eq_zero` - the binding
  side keyed to `sgn((Lw + b - h) ε)`, and the leftover magnitude of eq. (D.4).
- `coupled_step_lipschitz`, `coupled_step_reset` - the binding-side reset that
  anchors uniqueness of the McKean-Vlasov fixed point in Appendix D. Two
  coupled spoke chains contract per event, and the difference is annihilated
  outright on a binding event whatever the pre-event balances were.
- `lyap_post`, `foster_drift_pointwise`, `foster_drift_integral` - eq. (D.5),
  the Foster-Lyapunov drift bound, pointwise and in expectation. This is what
  both open routes to (A4) require from the model definition.

`MasterEquation/SpokeMarginal.lean` - Proposition 3 (closed-form one-spoke
marginal) and Corollary 1 (half-normal mixture), §6:

- `spokeLimit_eq_spokePost_typical_state` - the small-`w` reduction, exhibited
  as the exact hub-spoke kernel evaluated at the typical state. This is the
  paper's declared approximation step and is recorded rather than derived.
- `spoke_marginal_mixture` - Proposition 3, eq. (10), as a measure identity.
  The pushforward of `ν_ε` under the limiting update is `q δ₀ + (1 - q) ρ₊`,
  with `q = ν_ε(ε < 0)` and `ρ₊` the law of `(Lw/2)|ε|(1 + s_h²)` conditional
  on `ε ≥ 0`. In the small-`w` regime the limiting kernel is state-independent,
  so the mixture is an identity rather than a limit statement, and it holds
  under an arbitrary slippage law.
- `atom_mass` - the mass at zero is exactly `q` when `ν_ε` has no atom at the
  origin.
- `binding_prob_of_symmetric`, `gaussian_binding_prob`, `gaussian_spoke_atom` -
  Corollary 1's `q = 1/2` under symmetric slippage, instantiated at mathlib's
  `gaussianReal 0 v`.
- `leftover_scale`, `leftover_scale_symmetric` - the scale `β` and its
  reduction to `L w σ` in the homogeneous symmetric limit.

`MasterEquation/GaussianMoment.lean` - Corollary 1's second moment identity:

- `integral_Ioi_mul_exp_neg_mul_sq` - `∫₀^∞ x e^{-b x²} dx = 1/(2b)`, built
  from the fundamental theorem of calculus on `Ioi 0`. Mathlib has the
  two-sided Gaussian integral and the `Ioi` integral of `e^{-b x²}`, but not
  this one.
- `integral_Ioi_gaussianReal` - the one-sided first moment of a mean-zero
  Gaussian, which mathlib does not have in any form.
- `two_mul_oneSided_eq`, `conditional_mean_eq` - Corollary 1's
  `E[D | D > 0] = β √(2/π)`.

`MasterEquation/Doeblin.lean` - a negative result. The file was written to test
whether the binding-side reset yields assumption (A4). It does not. The
one-step statements below are correct and machine-checked; they do not compose
into (A4), and the file records why so that the attempt is not repeated.

- `Doeblin.integral_sub_le_of_atom`, `Doeblin.abs_integral_sub_le_of_atom` - a
  Doeblin minorisation at a single atom gives a Dobrushin contraction. If two
  probability measures each charge a common point with mass at least `δ`, their
  integrals of a function of oscillation `M - m` differ by at most
  `(1 - δ)(M - m)`.
- `HubSpoke.resetConst_le_hubLaw_atom` - at every hub event the hub is reset to
  zero with probability at least `δ := min(ν_ε(ε ≤ 0), ν_ε(ε ≥ 0))`. The bound
  mentions neither the pre-event spoke balance, nor the pre-event hub balance,
  nor the number of spokes, so it is uniform in the state, in the spoke
  environment and in `N`. It holds conditionally on the whole past, not merely
  on the current state.
- `HubSpoke.hub_dobrushin_step` - the resulting one-step contraction.
- `HubSpoke.resetConst_le_spokeLaw_atom`, `HubSpoke.spoke_dobrushin_step` - the
  spoke mirror.
- `HubSpoke.resetConst_pos` - `δ > 0` exactly when `ν_ε` charges both
  half-lines, which (A1')'s density-bounded-below condition supplies.
- `HubSpoke.spread_iterate` - a general iteration lemma, retained but not
  composable with `hub_dobrushin_step` to give (A4).

A Doeblin minorisation gives geometric ergodicity because coalescence at the
minorising atom is absorbing, so two coupled copies that land there share a
state and can be driven identically thereafter. That property fails here. The
chain lives on `ℝ_{≥0}^{N+1}` and each event touches two coordinates, so two
copies that both reset the hub agree in the hub coordinate and still differ in
all `N` spokes, and the next event reintroduces the difference through the
firing pool's `B_k`. The per-step bound holds and does not iterate. Working
with the full chain does not repair it, since full coalescence requires a reset
in every one of `N + 1` coordinates and the resulting rate degrades with `N`. A
union bound on whether `H_n` still depends on the initial condition branches
through `H_{n-1}` and through `B_{k_n}`, giving branching factor `2(1 - δ)`,
and `δ = min(q, 1 - q) ≤ 1/2` always, so it never contracts.

Two things do follow. The one-step minorisation is a structural property of the
kernel, uniform in `N` and conditional on the whole past, and it is the input a
Wasserstein-route argument would take, which is the shape of the Andreis-Dai
Pra-Fischer route Appendix D names as open. And on the limiting one-spoke chain
the hub is an independent draw from `π_H` with no spoke environment carrying
memory, so the reset is absorbing and the contraction does hold. That is the
paper's `ρ_B = 1 - q` anchoring uniqueness of the McKean-Vlasov fixed point,
asserted in Appendix D and checked here.

## Scope: what is not formalised

Recorded explicitly, since the paper's asymptotic section is a conditional
theorem and the formalisation does not change that status.

- **Proposition 2 (conditional propagation of chaos).** It asserts weak
  convergence of the `m`-spoke marginals of the stationary law of an
  `N`-particle chain to a product law, conditional on assumption (A4). The
  machinery it needs is absent from mathlib, namely Meyn-Tweedie stationary-law
  existence for a general chain on `ℝ_{≥0}^{N+1}`, petite-set constructions,
  and propagation-of-chaos coupling arguments. Lemma 2 (existence, uniqueness
  and tightness) is out of scope for the same reason. What is formalised is
  every deterministic ingredient the argument consumes, namely the kernel
  derivation, the binding-side reset contraction, and the Foster-Lyapunov
  drift.
- **Assumption (A4)** remains an assumption. Neither of the two open routes
  named in Appendix D, Andreis-Dai Pra-Fischer or lifting Graham-Meleard, is
  formalised. A third route was attempted in `Doeblin.lean` and does not work;
  the negative result is recorded there and above.
- **The `O(w)` remainder control.** Appendix D's leading-order expressions are
  taken as definitions, as stated in the file headers. Identifying them with
  the exact kernel at general state is the content of
  `spokeLimit_eq_spokePost_typical_state`, and nothing stronger is claimed.
- **Proposition 1's population step as stated.** The paper's conclusion is
  about a Spearman rank correlation under a reduced-form displacement
  decomposition `δ_k ≈ δ_{T*} + ε_k`, with a variance-share heuristic for the
  magnitude. Neither rank correlation nor that decomposition is formalised.
  What is proved is the sign-keyed sample covariance that the per-rebalance
  rule forces under the two-valued boundary trigger.
- **Lemma 1's probabilistic content**, as noted above.
- **Fixed-point arithmetic** remains the Foundry suite's job. Everything here
  is over `ℝ`, so tick rounding, wei-level truncation and the integer
  tick-rounding remainders in Theorem 2's statement are outside the model.
- **The model-to-process identification.** That the declared `Rebalance`
  structure and the hub-spoke kernel describe the deployed manager is an
  empirical matter settled by the V9 walks and the fork tests, not by Lean.

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

55 checks, all clean.
