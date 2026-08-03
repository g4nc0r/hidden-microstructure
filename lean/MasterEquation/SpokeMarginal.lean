/-
Proposition 3 (closed-form one-spoke marginal) and Corollary 1 (half-normal
mixture, symmetric Gaussian case), §6.

Proposition 2 identifies the limiting one-spoke chain; Proposition 3 then
evaluates it in the small-`w` regime, where `|L w + B - H| = L w (1 + O(σ))`
and the binding side is decided by `sgn ε` alone. In that regime the limiting
kernel no longer depends on the state, so its stationary law is simply the
pushforward of the slippage law `ν_ε` under the leftover map, and the atom
mixture of eq. (10) is an identity rather than a limit statement. That
identity is what is proved here.

The small-`w` reduction itself is the declared approximation step; it is
recorded as `spokeLimit_eq_spokePost_typical_state`, which exhibits the
limiting kernel as the exact kernel of `HubSpoke` evaluated at the typical
state `b = h = 0`. Proposition 2 (the convergence `π^N_(m) → μ^{⊗m}`) is not
formalised; see the README.
-/
import MasterEquation.HubSpoke

set_option linter.style.header false

namespace MasterEquation

open MeasureTheory ProbabilityTheory

namespace SpokeMarginal

variable {L w sh2 : ℝ}

/-- The limiting one-spoke update in the small-`w` regime: the spoke binds,
resetting to zero, when `ε < 0`, and otherwise carries the leftover
`(L w / 2) |ε| (1 + s_h²)`. -/
noncomputable def spokeLimit (L w sh2 ε : ℝ) : ℝ :=
  if ε < 0 then 0 else L * w / 2 * ε * (1 + sh2)

/-- The limiting kernel is the exact hub-spoke kernel evaluated at the typical
state, which is the content of the small-`w` reduction. -/
theorem spokeLimit_eq_spokePost_typical_state (hLw : 0 < L * w) (hsh : 0 < 1 + sh2)
    (ε : ℝ) : spokeLimit L w sh2 ε = HubSpoke.spokePost L w 0 0 ε sh2 := by
  unfold spokeLimit HubSpoke.spokePost
  have hc : 0 < L * w * (1 + sh2) / 2 := by
    have := mul_pos hLw hsh; linarith
  rw [show (L * w + 0 - 0) * ε * (1 + sh2) / 2 = L * w * (1 + sh2) / 2 * ε from by ring]
  by_cases hε : ε < 0
  · rw [if_pos hε, eq_comm,
      max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc.le hε.le)]
  · rw [if_neg hε, eq_comm, max_eq_left (mul_nonneg hc.le (not_lt.mp hε))]
    ring

theorem measurable_spokeLimit : Measurable (spokeLimit L w sh2) := by
  unfold spokeLimit
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const (by fun_prop)

/-- **Proposition 3, eq. (10).** The stationary law of the limiting one-spoke
chain is the binary atom mixture `q δ₀ + (1 - q) ρ₊`, with `q = ν_ε(ε < 0)`
the spoke-binding probability and `ρ₊` the law of `(L w / 2) |ε| (1 + s_h²)`
conditional on `ε ≥ 0`. The second summand carries total mass `1 - q`, so it
is `(1 - q) ρ₊` in the paper's normalisation. -/
theorem spoke_marginal_mixture (ν : Measure ℝ) :
    ν.map (spokeLimit L w sh2)
      = ν (Set.Iio 0) • Measure.dirac 0
        + (ν.restrict (Set.Ici 0)).map (fun e => L * w / 2 * e * (1 + sh2)) := by
  have hmeas : MeasurableSet (Set.Iio (0 : ℝ)) := measurableSet_Iio
  have hcompl : (Set.Iio (0 : ℝ))ᶜ = Set.Ici 0 := by
    ext x; simp
  have hsplit : ν.restrict (Set.Iio 0) + ν.restrict (Set.Ici 0) = ν := by
    rw [← hcompl]; exact Measure.restrict_add_restrict_compl hmeas
  calc ν.map (spokeLimit L w sh2)
      = (ν.restrict (Set.Iio 0)).map (spokeLimit L w sh2)
          + (ν.restrict (Set.Ici 0)).map (spokeLimit L w sh2) := by
        rw [← Measure.map_add _ _ measurable_spokeLimit, hsplit]
    _ = ν (Set.Iio 0) • Measure.dirac 0
          + (ν.restrict (Set.Ici 0)).map (fun e => L * w / 2 * e * (1 + sh2)) := by
        congr 1
        · have hae : spokeLimit L w sh2 =ᵐ[ν.restrict (Set.Iio 0)] fun _ => (0 : ℝ) := by
            filter_upwards [ae_restrict_mem hmeas] with x hx
            simp only [spokeLimit, if_pos (Set.mem_Iio.mp hx)]
          rw [Measure.map_congr hae, Measure.map_const, Measure.restrict_apply_univ]
        · have hae : spokeLimit L w sh2
              =ᵐ[ν.restrict (Set.Ici 0)] fun e => L * w / 2 * e * (1 + sh2) := by
            filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
            simp only [spokeLimit, if_neg (not_lt.mpr (Set.mem_Ici.mp hx))]
          rw [Measure.map_congr hae]

/-- **Proposition 3, atom mass.** When the slippage law has no atom at the
origin, the mass of the limiting spoke law at zero is exactly the binding
probability `q`. -/
theorem atom_mass (ν : Measure ℝ) (hLw : 0 < L * w) (hsh : 0 < 1 + sh2)
    (hatom : ν {(0 : ℝ)} = 0) :
    (ν.map (spokeLimit L w sh2)) {(0 : ℝ)} = ν (Set.Iio 0) := by
  have hc : 0 < L * w * (1 + sh2) / 2 := by
    have := mul_pos hLw hsh; linarith
  rw [Measure.map_apply measurable_spokeLimit (measurableSet_singleton 0)]
  have hpre : spokeLimit L w sh2 ⁻¹' {(0 : ℝ)} = Set.Iic 0 := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iic, spokeLimit]
    constructor
    · intro he
      by_contra hlt
      rw [if_neg (not_lt.mpr (not_le.mp hlt).le),
        show L * w / 2 * e * (1 + sh2) = L * w * (1 + sh2) / 2 * e from by ring] at he
      exact absurd he (ne_of_gt (mul_pos hc (not_le.mp hlt)))
    · intro he
      rcases lt_or_eq_of_le he with h | h
      · rw [if_pos h]
      · rw [h, if_neg (lt_irrefl (0:ℝ))]; ring
  rw [hpre]
  refine le_antisymm ?_ (measure_mono Set.Iio_subset_Iic_self)
  calc ν (Set.Iic 0) = ν (Set.Iio 0 ∪ {0}) := by rw [Set.Iio_union_right]
    _ ≤ ν (Set.Iio 0) + ν {0} := measure_union_le _ _
    _ = ν (Set.Iio 0) := by rw [hatom, add_zero]

/-! ## Corollary 1: the symmetric Gaussian case -/

/-- Under a symmetric mean-zero slippage law the binding probability is one
half. This is the first assertion of Corollary 1. -/
theorem binding_prob_of_symmetric (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsymm : ν.map (fun x => -x) = ν) (hatom : ν {(0 : ℝ)} = 0) :
    ν (Set.Iio 0) = 1 / 2 := by
  have hmeasneg : Measurable (fun x : ℝ => -x) := measurable_neg
  have hflip : ν (Set.Iio 0) = ν (Set.Ioi 0) := by
    conv_lhs => rw [← hsymm]
    rw [Measure.map_apply hmeasneg measurableSet_Iio]
    congr 1
    ext x
    simp
  have hunion : ν (Set.Iio 0) + ν (Set.Ici 0) = 1 := by
    have hmeas : MeasurableSet (Set.Iio (0 : ℝ)) := measurableSet_Iio
    have hcompl : (Set.Iio (0 : ℝ))ᶜ = Set.Ici 0 := by ext x; simp
    rw [← hcompl, measure_add_measure_compl hmeas, measure_univ]
  have hIci : ν (Set.Ici (0 : ℝ)) = ν (Set.Ioi 0) := by
    refine le_antisymm ?_ (measure_mono Set.Ioi_subset_Ici_self)
    calc ν (Set.Ici 0) = ν (Set.Ioi 0 ∪ {0}) := by rw [Set.Ioi_union_left]
      _ ≤ ν (Set.Ioi 0) + ν {0} := measure_union_le _ _
      _ = ν (Set.Ioi 0) := by rw [hatom, add_zero]
  rw [hIci, ← hflip] at hunion
  have h2 : (2 : ENNReal) * ν (Set.Iio 0) = 1 := by rw [two_mul]; exact hunion
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  exact h2

/-- **Corollary 1, `q = 1/2`.** For mean-zero Gaussian slippage the spoke
binds on exactly half of all events, so the limiting spoke law carries an atom
of mass one half at the origin. -/
theorem gaussian_binding_prob {v : NNReal} (hv : v ≠ 0) :
    (gaussianReal 0 v) (Set.Iio 0) = 1 / 2 := by
  have hatom : (gaussianReal 0 v) {(0 : ℝ)} = 0 :=
    (nullSingletonClass_gaussianReal hv).measure_singleton 0
  refine binding_prob_of_symmetric _ ?_ hatom
  rw [gaussianReal_map_neg, neg_zero]

/-- The atom of the limiting spoke law under Gaussian slippage. -/
theorem gaussian_spoke_atom {v : NNReal} (hv : v ≠ 0) (hLw : 0 < L * w)
    (hsh : 0 < 1 + sh2) :
    ((gaussianReal 0 v).map (spokeLimit L w sh2)) {(0 : ℝ)} = 1 / 2 := by
  rw [atom_mass _ hLw hsh ((nullSingletonClass_gaussianReal hv).measure_singleton 0)]
  exact gaussian_binding_prob hv

/-- The scale of the leftover law: `ρ₊` is the law of `|ε|` pushed through the
linear map with slope `β / σ`, so that for symmetric Gaussian slippage of
standard deviation `σ` it is half-normal with the scale `β` of Corollary 1.
-/
theorem leftover_scale (σ : ℝ) :
    L * w / 2 * σ * (1 + sh2) = L * w * σ * (1 + sh2) / 2 := by ring

/-- In the homogeneous symmetric limit `s → 1`, `d₀ = d₁`, the routing slope
`s_h²` is one and the scale reduces to `L w σ`. -/
theorem leftover_scale_symmetric (σ : ℝ) :
    L * w * σ * (1 + 1) / 2 = L * w * σ := by ring

end SpokeMarginal

end MasterEquation
