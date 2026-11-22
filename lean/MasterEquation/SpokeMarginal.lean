/-
Proposition 3 (closed-form one-spoke marginal) and its Gaussian case (the
Remark after it: half-normal mixture, symmetric Gaussian residual).

The atom of the one-spoke law rests on an identity of the kernel: on a
positive imbalance the spoke's entry is zero after an event of its own pool
exactly when `η ε ≥ 0` (`Kernel.spokePost_eq_zero_iff`). `atom_exact` lifts
that to probabilities, for any joint law of state and mark under which the
imbalance is positive, with no independence used. That the stationary law of
a spoke entry is its law after its own last event is a statement about the
chain and is not formalised here.

The rest of the file is the leading-order law. With the balances neglected
beside the position, the spoke's entry after its own event is a function of
`z = η ε` alone, zero for `z ≥ 0` and `c₀ Lw |z|` otherwise, so its law is the
pushforward of the law of `z`, and the atom mixture is an identity. The law of
`z` is `markLaw`: direction `+1` with probability `p₊` and residual law `ν₊`,
direction `-1` with probability `p₋` and residual law `ν₋`.
-/
import MasterEquation.DirectionKernel

set_option linter.style.header false

namespace MasterEquation

open MeasureTheory ProbabilityTheory

namespace SpokeMarginal

variable {c0 Lw η : ℝ}

/-! ## The atom as an identity of the kernel -/

/-- **Proposition 3, the atom.** Under any joint law of the pre-event state
and the mark for which the imbalance is positive, the probability that the
spoke's entry is zero after the event is the probability that `η ε ≥ 0`. -/
theorem atom_exact {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H B η ε : Ω → ℝ) (hc0 : 0 < c0)
    (hA : ∀ ω, 0 < Kernel.imbalance Lw (η ω) (H ω) (B ω)) :
    P {ω | Kernel.spokePost c0 Lw (η ω) (H ω) (B ω) (ε ω) = 0}
      = P {ω | 0 ≤ η ω * ε ω} := by
  congr 1
  ext ω
  exact Kernel.spokePost_eq_zero_iff hc0 (hA ω)

/-! ## The leading-order law -/

/-- The leading-order spoke entry after its own event, as a function of
`z = η ε`. -/
noncomputable def spokeLead (c0 Lw z : ℝ) : ℝ :=
  if 0 ≤ z then 0 else c0 * Lw * (-z)

/-- The leading-order update is the kernel at an empty ledger. -/
theorem spokeLead_eq_spokePost_empty (hη : η = 1 ∨ η = -1) (hc : 0 ≤ c0 * Lw)
    (ε : ℝ) : spokeLead c0 Lw (η * ε) = Kernel.spokePost c0 Lw η 0 0 ε := by
  have hη2 : η * η = 1 := by rcases hη with h | h <;> rw [h] <;> norm_num
  unfold spokeLead Kernel.spokePost Kernel.imbalance
  rw [show -(c0 * (η * (Lw + η * (0 - 0)) * ε)) = c0 * Lw * -(η * ε) by ring]
  by_cases hz : 0 ≤ η * ε
  · rw [if_pos hz, eq_comm, max_eq_right]
    exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
  · rw [if_neg hz, eq_comm, max_eq_left]
    exact mul_nonneg hc (by linarith [not_le.mp hz])

theorem measurable_spokeLead : Measurable (spokeLead c0 Lw) := by
  unfold spokeLead
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const (by fun_prop)

/-- **Proposition 3, the mixture.** The leading-order law of the spoke entry
is `q δ₀ + (1 - q) ρ₊`, with `q = ν(z ≥ 0)` and `ρ₊` the law of `c₀ Lw |z|`
given `z < 0`. The second summand carries total mass `1 - q`. -/
theorem spoke_marginal_mixture (ν : Measure ℝ) :
    ν.map (spokeLead c0 Lw)
      = ν (Set.Ici 0) • Measure.dirac 0
        + (ν.restrict (Set.Iio 0)).map (fun z => c0 * Lw * (-z)) := by
  have hmeas : MeasurableSet (Set.Ici (0 : ℝ)) := measurableSet_Ici
  have hcompl : (Set.Ici (0 : ℝ))ᶜ = Set.Iio 0 := by
    ext x; simp
  have hsplit : ν.restrict (Set.Ici 0) + ν.restrict (Set.Iio 0) = ν := by
    rw [← hcompl]; exact Measure.restrict_add_restrict_compl hmeas
  calc ν.map (spokeLead c0 Lw)
      = (ν.restrict (Set.Ici 0)).map (spokeLead c0 Lw)
          + (ν.restrict (Set.Iio 0)).map (spokeLead c0 Lw) := by
        rw [← Measure.map_add _ _ measurable_spokeLead, hsplit]
    _ = ν (Set.Ici 0) • Measure.dirac 0
          + (ν.restrict (Set.Iio 0)).map (fun z => c0 * Lw * (-z)) := by
        congr 1
        · have hae : spokeLead c0 Lw =ᵐ[ν.restrict (Set.Ici 0)] fun _ => (0 : ℝ) := by
            filter_upwards [ae_restrict_mem hmeas] with x hx
            simp only [spokeLead, if_pos (Set.mem_Ici.mp hx)]
          rw [Measure.map_congr hae, Measure.map_const, Measure.restrict_apply_univ]
        · have hae : spokeLead c0 Lw
              =ᵐ[ν.restrict (Set.Iio 0)] fun z => c0 * Lw * (-z) := by
            filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
            simp only [spokeLead, if_neg (not_le.mpr (Set.mem_Iio.mp hx))]
          rw [Measure.map_congr hae]

/-- **The atom of the leading-order law.** Its mass at zero is exactly
`q = ν(z ≥ 0)`. No condition on the law of `z` is needed: a residual of zero
leaves nothing. -/
theorem atom_mass (ν : Measure ℝ) (hc : 0 < c0 * Lw) :
    (ν.map (spokeLead c0 Lw)) {(0 : ℝ)} = ν (Set.Ici 0) := by
  rw [Measure.map_apply measurable_spokeLead (measurableSet_singleton 0)]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ici, spokeLead]
  constructor
  · intro hz
    by_contra hneg
    rw [if_neg hneg] at hz
    exact absurd hz (ne_of_gt (mul_pos hc (by linarith [not_le.mp hneg])))
  · intro hz
    rw [if_pos hz]

/-! ## The atom in terms of direction -/

/-- The law of `z = η ε`: direction `+1` with weight `p₊` and residual law
`ν₊`, direction `-1` with weight `p₋` and residual law `ν₋`. -/
noncomputable def markLaw (pp pm : ENNReal) (νp νm : Measure ℝ) : Measure ℝ :=
  pp • νp + pm • νm.map (fun e => -e)

/-- **Proposition 3, the value of the atom.**
`q = p₊ ν₊[0, ∞) + p₋ ν₋(-∞, 0]`. -/
theorem atom_eq_direction_mixture (pp pm : ENNReal) (νp νm : Measure ℝ) :
    (markLaw pp pm νp νm) (Set.Ici 0) = pp * νp (Set.Ici 0) + pm * νm (Set.Iic 0) := by
  have hpre : (fun e : ℝ => -e) ⁻¹' Set.Ici 0 = Set.Iic 0 := by
    ext e; simp
  unfold markLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_neg measurableSet_Ici, hpre, smul_eq_mul, smul_eq_mul]

/-- The two closed half-lines of a probability law with no atom at zero carry
total mass one. -/
theorem Ici_add_Iic_of_no_atom (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ν {(0 : ℝ)} = 0) : ν (Set.Ici 0) + ν (Set.Iic 0) = 1 := by
  have hIic : ν (Set.Iic (0 : ℝ)) = ν (Set.Iio 0) := by
    refine le_antisymm ?_ (measure_mono Set.Iio_subset_Iic_self)
    calc ν (Set.Iic 0) = ν (Set.Iio 0 ∪ {0}) := by rw [Set.Iio_union_right]
      _ ≤ ν (Set.Iio 0) + ν {0} := measure_union_le _ _
      _ = ν (Set.Iio 0) := by rw [hatom, add_zero]
  have hcompl : (Set.Ici (0 : ℝ))ᶜ = Set.Iio 0 := by ext x; simp
  rw [hIic, ← hcompl, measure_add_measure_compl measurableSet_Ici, measure_univ]

/-- **An atom away from one half comes only from direction.** With one
residual law for both directions, no atom at zero and directions equally
likely, `q = 1/2` whatever the law. -/
theorem atom_half_of_common_law (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ν {(0 : ℝ)} = 0) :
    (markLaw (1 / 2) (1 / 2) ν ν) (Set.Ici 0) = 1 / 2 := by
  rw [atom_eq_direction_mixture, ← mul_add, Ici_add_Iic_of_no_atom ν hatom, mul_one]

/-! ## The Gaussian case: symmetric laws -/

/-- Under a symmetric law with no atom at zero the open lower half-line has
mass one half. -/
theorem half_of_symmetric (ν : Measure ℝ) [IsProbabilityMeasure ν]
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

/-- Both closed half-lines of such a law have mass one half. -/
theorem closed_halves_of_symmetric (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsymm : ν.map (fun x => -x) = ν) (hatom : ν {(0 : ℝ)} = 0) :
    ν (Set.Ici 0) = 1 / 2 ∧ ν (Set.Iic 0) = 1 / 2 := by
  have hlow := half_of_symmetric ν hsymm hatom
  have hIic : ν (Set.Iic (0 : ℝ)) = 1 / 2 := by
    rw [← hlow]
    refine le_antisymm ?_ (measure_mono Set.Iio_subset_Iic_self)
    calc ν (Set.Iic 0) = ν (Set.Iio 0 ∪ {0}) := by rw [Set.Iio_union_right]
      _ ≤ ν (Set.Iio 0) + ν {0} := measure_union_le _ _
      _ = ν (Set.Iio 0) := by rw [hatom, add_zero]
  have hsum := Ici_add_Iic_of_no_atom ν hatom
  rw [hIic] at hsum
  have hhalf : ν (Set.Ici (0 : ℝ)) + 1 / 2 = 1 / 2 + 1 / 2 := by
    rw [hsum, ENNReal.add_halves]
  exact ⟨(ENNReal.add_left_inj (by norm_num)).mp hhalf, hIic⟩

/-- **The Gaussian case, `q = 1/2`.** For a symmetric residual law with no atom at
zero, shared by both directions, the atom is one half whatever the
probabilities of the two directions. -/
theorem atom_half_of_symmetric (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsymm : ν.map (fun x => -x) = ν) (hatom : ν {(0 : ℝ)} = 0)
    {pp pm : ENNReal} (hp : pp + pm = 1) :
    (markLaw pp pm ν ν) (Set.Ici 0) = 1 / 2 := by
  obtain ⟨h1, h2⟩ := closed_halves_of_symmetric ν hsymm hatom
  rw [atom_eq_direction_mixture, h1, h2, ← add_mul, hp, one_mul]

/-- **The atom at the Gaussian.** For mean-zero Gaussian residuals the atom
is one half. The paper conditions the Gaussian to `[-K, K]`; the statement
here is for the Gaussian itself, and for any symmetric law without an atom at
zero by `atom_half_of_symmetric`. -/
theorem gaussian_atom {v : NNReal} (hv : v ≠ 0) {pp pm : ENNReal} (hp : pp + pm = 1) :
    (markLaw pp pm (gaussianReal 0 v) (gaussianReal 0 v)) (Set.Ici 0) = 1 / 2 := by
  have hatom : (gaussianReal 0 v) {(0 : ℝ)} = 0 :=
    (nullSingletonClass_gaussianReal hv).measure_singleton 0
  refine atom_half_of_symmetric _ ?_ hatom hp
  rw [gaussianReal_map_neg, neg_zero]

/-- The atom of the leading-order spoke law under Gaussian residuals. -/
theorem gaussian_spoke_atom {v : NNReal} (hv : v ≠ 0) (hc : 0 < c0 * Lw)
    {pp pm : ENNReal} (hp : pp + pm = 1) :
    ((markLaw pp pm (gaussianReal 0 v) (gaussianReal 0 v)).map (spokeLead c0 Lw))
        {(0 : ℝ)} = 1 / 2 := by
  rw [atom_mass _ hc]
  exact gaussian_atom hv hp

/-- The scale of the slack-side law: for residuals of standard deviation `σ`
the leftover `c₀ Lw |z|` has scale `β = c₀ Lw σ`, which is `Lw σ` when the
routing slope is one. -/
theorem leftover_scale_symmetric (σ : ℝ) :
    (1 + 1) / 2 * Lw * σ = Lw * σ := by ring

end SpokeMarginal

end MasterEquation
