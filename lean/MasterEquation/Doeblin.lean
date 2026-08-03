/-
The binding-side reset as a Doeblin minorisation.

Eq. (8) sets exactly one of the two balances to zero at every event, so the
hub is reset to zero with probability

  P((L w + b - h) ε ≥ 0)  ≥  min(ν_ε(ε ≤ 0), ν_ε(ε ≥ 0))  =:  δ,

and `δ` depends on the slippage law alone: not on the pre-event state, not on
the spoke environment, and not on `N`. That is a Doeblin minorisation at the
single atom `0`. Everything below it is a consequence of that one-step fact
and is correct as stated.

WHAT THIS DOES NOT DO. It was written to test whether the reset yields (A4),
uniform-in-`N` geometric ergodicity of the hub marginal, which Appendix D
assumes. It does not, and the reason is worth recording so the attempt is not
repeated.

A Doeblin minorisation gives geometric ergodicity because coalescence at the
minorising atom is ABSORBING: two coupled copies that land there share a state
and can be driven identically forever after. That fails here. The chain lives
on `ℝ_{≥0}^{N+1}` and each event touches two coordinates. When both copies
reset the hub, they agree in the hub coordinate and still differ in all `N`
spoke coordinates, and the very next event re-injects the difference through
the firing pool's `B_k`. So `P(H' = 0 | ℱ) ≥ δ` holds at every step, but the
events are not absorbing and `(1 - δ)^n` does not follow.

Nor does the full chain rescue it: full coalescence needs a reset in every one
of the `N + 1` coordinates, and since each event touches two, the resulting
rate degrades with `N` instead of being uniform in it. A crude union bound on
"does `H_n` still depend on the initial condition" branches through `H_{n-1}`
and through `B_{k_n}`, each surviving with probability at most `1 - δ`, so the
branching factor is `2(1 - δ)`; since `δ = min(q, 1 - q) ≤ 1/2` always, that
factor is at least one and the bound never contracts.

WHAT SURVIVES. Two things, both real.

First, the one-step minorisation holds conditionally on the whole past, not
just on the current state, and is uniform in the state, the environment and
`N`. That is a structural fact about the kernel and it is the natural
ingredient for a Wasserstein-route argument, which is the shape of the
Andreis-Dai Pra-Fischer route Appendix D already names as open.

Second, on the LIMITING one-spoke chain the hub is an independent draw from
`π_H` by construction, so there is no spoke environment carrying memory, the
reset IS absorbing, and the contraction is genuine. That is the paper's own
`ρ_B = 1 - q` anchoring uniqueness of the McKean-Vlasov fixed point, and
together with `HubSpoke.coupled_step_reset` it is here rigorously.

(A4) remains an assumption. See the README.
-/
import MasterEquation.HubSpoke

set_option linter.style.header false

namespace MasterEquation

namespace Doeblin

open MeasureTheory

/-! ## A Doeblin minorisation at a single atom gives a Dobrushin contraction -/

variable {α : Type*} [MeasurableSpace α]

/-- The integral of a bounded function over a probability measure charging a
point `x₀`, split at that point. -/
private lemma integral_split_atom {μ : Measure α} [IsProbabilityMeasure μ]
    {x₀ : α} (hx₀ : MeasurableSet ({x₀} : Set α)) {f : α → ℝ} (hf : Integrable f μ)
    {m M : ℝ} (hm : ∀ z, m ≤ f z) (hM : ∀ z, f z ≤ M) :
    (∫ z, f z ∂μ ≤ μ.real {x₀} * f x₀ + M * (1 - μ.real {x₀})) ∧
      (μ.real {x₀} * f x₀ + m * (1 - μ.real {x₀}) ≤ ∫ z, f z ∂μ) := by
  have hcompl : μ.real ({x₀} : Set α)ᶜ = 1 - μ.real {x₀} := by
    rw [measureReal_compl hx₀, probReal_univ]
  have hatom : ∫ z in ({x₀} : Set α), f z ∂μ = μ.real {x₀} * f x₀ := by
    rw [setIntegral_congr_fun hx₀ (g := fun _ => f x₀)
      (fun x hx => by rw [Set.mem_singleton_iff.mp hx]), setIntegral_const, smul_eq_mul]
  have hsplit : ∫ z in ({x₀} : Set α), f z ∂μ + ∫ z in ({x₀} : Set α)ᶜ, f z ∂μ
      = ∫ z, f z ∂μ := integral_add_compl hx₀ hf
  constructor
  · have hub : ∫ z in ({x₀} : Set α)ᶜ, f z ∂μ ≤ M * (1 - μ.real {x₀}) := by
      calc ∫ z in ({x₀} : Set α)ᶜ, f z ∂μ ≤ ∫ _ in ({x₀} : Set α)ᶜ, M ∂μ :=
            setIntegral_mono_on hf.integrableOn integrableOn_const hx₀.compl
              (fun x _ => hM x)
        _ = M * (1 - μ.real {x₀}) := by
            rw [setIntegral_const, hcompl, smul_eq_mul, mul_comm]
    linarith [hsplit, hatom, hub]
  · have hlb : m * (1 - μ.real {x₀}) ≤ ∫ z in ({x₀} : Set α)ᶜ, f z ∂μ := by
      calc m * (1 - μ.real {x₀}) = ∫ _ in ({x₀} : Set α)ᶜ, m ∂μ := by
            rw [setIntegral_const, hcompl, smul_eq_mul, mul_comm]
        _ ≤ ∫ z in ({x₀} : Set α)ᶜ, f z ∂μ :=
            setIntegral_mono_on integrableOn_const hf.integrableOn hx₀.compl
              (fun x _ => hm x)
    linarith [hsplit, hatom, hlb]

/-- **Dobrushin contraction from a Doeblin minorisation at a single atom.**
If two probability measures each charge a common point `x₀` with mass at least
`δ`, their integrals of a function bounded between `m` and `M` differ by at
most `(1 - δ) (M - m)`. -/
theorem integral_sub_le_of_atom {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {x₀ : α} (hx₀ : MeasurableSet ({x₀} : Set α))
    {δ : ℝ} (hδμ : δ ≤ μ.real {x₀}) (hδν : δ ≤ ν.real {x₀})
    {f : α → ℝ} (hμ : Integrable f μ) (hν : Integrable f ν)
    {m M : ℝ} (hm : ∀ z, m ≤ f z) (hM : ∀ z, f z ≤ M) :
    ∫ z, f z ∂μ - ∫ z, f z ∂ν ≤ (1 - δ) * (M - m) := by
  obtain ⟨hμub, -⟩ := integral_split_atom hx₀ hμ hm hM
  obtain ⟨-, hνlb⟩ := integral_split_atom hx₀ hν hm hM
  have h1 : m ≤ f x₀ := hm x₀
  have h2 : f x₀ ≤ M := hM x₀
  nlinarith [hμub, hνlb, hδμ, hδν, h1, h2]

/-- The two-sided form. -/
theorem abs_integral_sub_le_of_atom {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {x₀ : α} (hx₀ : MeasurableSet ({x₀} : Set α))
    {δ : ℝ} (hδμ : δ ≤ μ.real {x₀}) (hδν : δ ≤ ν.real {x₀})
    {f : α → ℝ} (hμ : Integrable f μ) (hν : Integrable f ν)
    {m M : ℝ} (hm : ∀ z, m ≤ f z) (hM : ∀ z, f z ≤ M) :
    |∫ z, f z ∂μ - ∫ z, f z ∂ν| ≤ (1 - δ) * (M - m) := by
  rw [abs_sub_le_iff]
  exact ⟨integral_sub_le_of_atom hx₀ hδμ hδν hμ hν hm hM,
    integral_sub_le_of_atom hx₀ hδν hδμ hν hμ hm hM⟩

end Doeblin

/-! ## The hub kernel's uniform minorisation -/

namespace HubSpoke

open MeasureTheory

variable {L w b h sh2 : ℝ}

theorem measurable_hubPost : Measurable (fun e => hubPost L w b h e sh2) := by
  unfold hubPost
  fun_prop

/-- The law of the post-event hub balance, given the pre-event state and the
slippage law. -/
noncomputable def hubLaw (νε : Measure ℝ) (L w b h sh2 : ℝ) : Measure ℝ :=
  νε.map (fun e => hubPost L w b h e sh2)

instance (νε : Measure ℝ) [IsProbabilityMeasure νε] :
    IsProbabilityMeasure (hubLaw νε L w b h sh2) :=
  Measure.isProbabilityMeasure_map measurable_hubPost.aemeasurable

/-- **The reset constant.** It depends on the slippage law alone. -/
noncomputable def resetConst (νε : Measure ℝ) : ℝ :=
  min (νε.real (Set.Iic 0)) (νε.real (Set.Ici 0))

/-- **The uniform Doeblin minorisation.** At every hub event the hub is reset
to zero with probability at least `resetConst ν_ε`, whatever the pre-event
state. The bound mentions neither `b`, nor `h`, nor the number of spokes, so
it is uniform in the state, in the spoke environment and in `N`. It does not
give (A4), because the reset is not absorbing on the `N`-particle chain; see
the file header. -/
theorem resetConst_le_hubLaw_atom (νε : Measure ℝ) [IsProbabilityMeasure νε]
    (hsh : 0 < 1 + sh2) :
    resetConst νε ≤ (hubLaw νε L w b h sh2).real {(0 : ℝ)} := by
  have hpre : ∀ e : ℝ, 0 ≤ (L * w + b - h) * e → hubPost L w b h e sh2 = 0 := by
    intro e he
    unfold hubPost
    refine max_eq_right ?_
    nlinarith
  have hmapE : (hubLaw νε L w b h sh2) {(0 : ℝ)}
      = νε ((fun e => hubPost L w b h e sh2) ⁻¹' {0}) :=
    Measure.map_apply measurable_hubPost (measurableSet_singleton 0)
  have hmap : (hubLaw νε L w b h sh2).real {(0 : ℝ)}
      = νε.real ((fun e => hubPost L w b h e sh2) ⁻¹' {0}) := by
    unfold Measure.real; rw [hmapE]
  rw [hmap]
  rcases lt_trichotomy (L * w + b - h) 0 with hd | hd | hd
  · refine le_trans (min_le_left _ _) (measureReal_mono ?_ (measure_ne_top _ _))
    intro e he
    exact hpre e (by nlinarith [Set.mem_Iic.mp he])
  · refine le_trans (min_le_left _ _) (measureReal_mono ?_ (measure_ne_top _ _))
    intro e _
    exact hpre e (by rw [hd, zero_mul])
  · refine le_trans (min_le_right _ _) (measureReal_mono ?_ (measure_ne_top _ _))
    intro e he
    exact hpre e (by nlinarith [Set.mem_Ici.mp he])

/-- **One hub event, dual form.** The value functions of two arbitrary
pre-event states differ by at most `(1 - δ)` times the oscillation of the test
function, with `δ = resetConst ν_ε` independent of both states, of the spoke
environment, and of `N`. This is a genuine one-step contraction; it does not
iterate on the `N`-particle chain, since hub coalescence leaves the spoke
coordinates unequal. See the file header. -/
theorem hub_dobrushin_step (νε : Measure ℝ) [IsProbabilityMeasure νε]
    (hsh : 0 < 1 + sh2) (b₁ h₁ b₂ h₂ : ℝ) {f : ℝ → ℝ}
    (h₁int : Integrable f (hubLaw νε L w b₁ h₁ sh2))
    (h₂int : Integrable f (hubLaw νε L w b₂ h₂ sh2))
    {m M : ℝ} (hm : ∀ z, m ≤ f z) (hM : ∀ z, f z ≤ M) :
    |(∫ z, f z ∂(hubLaw νε L w b₁ h₁ sh2)) - ∫ z, f z ∂(hubLaw νε L w b₂ h₂ sh2)|
      ≤ (1 - resetConst νε) * (M - m) :=
  Doeblin.abs_integral_sub_le_of_atom (measurableSet_singleton 0)
    (resetConst_le_hubLaw_atom νε hsh) (resetConst_le_hubLaw_atom νε hsh)
    h₁int h₂int hm hM

/-- The reset constant is strictly positive exactly when the slippage law
charges both half-lines, which is implied by (A1')'s density-bounded-below
condition at the origin. -/
theorem resetConst_pos (νε : Measure ℝ) [IsProbabilityMeasure νε]
    (hneg : 0 < νε.real (Set.Iic 0)) (hpos : 0 < νε.real (Set.Ici 0)) :
    0 < resetConst νε := lt_min hneg hpos

/-- The reset constant is a probability, so `1 - δ` is a contraction factor in
`[0, 1]`. -/
theorem resetConst_le_one (νε : Measure ℝ) [IsProbabilityMeasure νε] :
    resetConst νε ≤ 1 := by
  refine (min_le_left _ _).trans ?_
  rw [← probReal_univ (μ := νε)]
  exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)

/-! ## The spoke side

Appendix D already anchors McKean-Vlasov uniqueness on the spoke reset, at
rate `ρ_B = 1 - q`. The same minorisation statement holds there, with the same
constant, which is the symmetry the observation above turns on: eq. (8) resets
one of the two coordinates at every event, so whichever coordinate is being
tracked enjoys a state-independent reset probability. -/

theorem measurable_spokePost : Measurable (fun e => spokePost L w b h e sh2) := by
  unfold spokePost
  fun_prop

/-- The law of the post-event spoke balance. -/
noncomputable def spokeLaw (νε : Measure ℝ) (L w b h sh2 : ℝ) : Measure ℝ :=
  νε.map (fun e => spokePost L w b h e sh2)

instance (νε : Measure ℝ) [IsProbabilityMeasure νε] :
    IsProbabilityMeasure (spokeLaw νε L w b h sh2) :=
  Measure.isProbabilityMeasure_map measurable_spokePost.aemeasurable

/-- The spoke enjoys the same uniform reset bound. In the typical-state regime
`L w + b - h > 0` the spoke resets with probability `q = ν_ε(ε < 0)` and the
hub with probability `1 - q`, so `resetConst` is the smaller of the paper's
`ρ_B`-complement and its mirror. -/
theorem resetConst_le_spokeLaw_atom (νε : Measure ℝ) [IsProbabilityMeasure νε]
    (hsh : 0 < 1 + sh2) :
    resetConst νε ≤ (spokeLaw νε L w b h sh2).real {(0 : ℝ)} := by
  have hpre : ∀ e : ℝ, (L * w + b - h) * e ≤ 0 → spokePost L w b h e sh2 = 0 := by
    intro e he
    unfold spokePost
    refine max_eq_right ?_
    nlinarith
  have hmapE : (spokeLaw νε L w b h sh2) {(0 : ℝ)}
      = νε ((fun e => spokePost L w b h e sh2) ⁻¹' {0}) :=
    Measure.map_apply measurable_spokePost (measurableSet_singleton 0)
  have hmap : (spokeLaw νε L w b h sh2).real {(0 : ℝ)}
      = νε.real ((fun e => spokePost L w b h e sh2) ⁻¹' {0}) := by
    unfold Measure.real; rw [hmapE]
  rw [hmap]
  rcases lt_trichotomy (L * w + b - h) 0 with hd | hd | hd
  · refine le_trans (min_le_right _ _) (measureReal_mono ?_ (measure_ne_top _ _))
    intro e he
    exact hpre e (by nlinarith [Set.mem_Ici.mp he])
  · refine le_trans (min_le_left _ _) (measureReal_mono ?_ (measure_ne_top _ _))
    intro e _
    exact hpre e (by rw [hd, zero_mul])
  · refine le_trans (min_le_left _ _) (measureReal_mono ?_ (measure_ne_top _ _))
    intro e he
    exact hpre e (by nlinarith [Set.mem_Iic.mp he])

/-- Whichever coordinate is tracked, exactly one is reset at each event, so
both marginals contract at the same guaranteed rate. -/
theorem spoke_dobrushin_step (νε : Measure ℝ) [IsProbabilityMeasure νε]
    (hsh : 0 < 1 + sh2) (b₁ h₁ b₂ h₂ : ℝ) {f : ℝ → ℝ}
    (h₁int : Integrable f (spokeLaw νε L w b₁ h₁ sh2))
    (h₂int : Integrable f (spokeLaw νε L w b₂ h₂ sh2))
    {m M : ℝ} (hm : ∀ z, m ≤ f z) (hM : ∀ z, f z ≤ M) :
    |(∫ z, f z ∂(spokeLaw νε L w b₁ h₁ sh2)) - ∫ z, f z ∂(spokeLaw νε L w b₂ h₂ sh2)|
      ≤ (1 - resetConst νε) * (M - m) :=
  Doeblin.abs_integral_sub_le_of_atom (measurableSet_singleton 0)
    (resetConst_le_spokeLaw_atom νε hsh) (resetConst_le_spokeLaw_atom νε hsh)
    h₁int h₂int hm hM

/-! ## Iterating a contraction

Retained as a general-purpose lemma. It is NOT composable with
`hub_dobrushin_step` to give (A4): that composition would need the per-step
hypothesis to hold for the `n`-step value functions of the `N`-particle chain,
and it does not, because hub coalescence is not absorbing there. See the file
header. The lemma applies to the limiting one-spoke chain, where the hub is an
independent draw and the reset is absorbing. -/

/-- A spread that contracts by `ρ` at every step has contracted by `ρ ^ n`
after `n` steps. -/
theorem spread_iterate {D : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hstep : ∀ n, D (n + 1) ≤ ρ * D n) : ∀ n, D n ≤ ρ ^ n * D 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      calc D (k + 1) ≤ ρ * D k := hstep k
        _ ≤ ρ * (ρ ^ k * D 0) := by exact mul_le_mul_of_nonneg_left ih hρ
        _ = ρ ^ (k + 1) * D 0 := by ring

end HubSpoke

end MasterEquation
