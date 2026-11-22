/-
The moment identity of the Gaussian case of Proposition 3 (the Remark after
it; Corollary 1 of the July 2026 version).

The Remark gives two explicit quantities of the leading-order spoke law
under symmetric Gaussian residuals. The atom `P(B_k = 0) = 1/2` is proved in
`SpokeMarginal.lean`. This file supplies the other, the mean `β √(2/π)` of
the half-normal law (the paper writes its scale σ_hn), which needs the
half-Gaussian first moment. The Gaussian here is not conditioned to
`[-K, K]` as it is in the Remark; the paper gives the relative error of
that conditioning.
Mathlib has no absolute or one-sided moment for the Gaussian, so the
underlying first-passage integral is built here from the fundamental theorem
of calculus on `Ioi 0`.
-/
import MasterEquation.SpokeMarginal

set_option linter.style.header false

namespace MasterEquation

namespace GaussianMoment

open MeasureTheory Real Filter Set
open scoped Topology ENNReal

/-! ## The first-passage integral -/

/-- `∫_0^∞ x e^{-b x²} dx = 1 / (2b)`, by the fundamental theorem of calculus
with antiderivative `-e^{-b x²} / (2b)`. Mathlib has the two-sided Gaussian
integral and the `Ioi` integral of `e^{-b x²}`, but not this one. -/
theorem integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * rexp (-b * x ^ 2) = 1 / (2 * b) := by
  have hb' : b ≠ 0 := hb.ne'
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => -rexp (-b * y ^ 2) / (2 * b))
        (x * rexp (-b * x ^ 2)) x := by
    intro x _
    have hg : HasDerivAt (fun y : ℝ => -b * y ^ 2) (-b * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-b))
    have he : HasDerivAt (fun y : ℝ => rexp (-b * y ^ 2))
        (rexp (-b * x ^ 2) * (-b * (2 * x))) x := hg.exp
    have hval : -(rexp (-b * x ^ 2) * (-b * (2 * x))) / (2 * b)
        = x * rexp (-b * x ^ 2) := by field_simp
    exact hval ▸ (he.neg.div_const (2 * b))
  have hcont : ContinuousWithinAt (fun y : ℝ => -rexp (-b * y ^ 2) / (2 * b))
      (Ici (0 : ℝ)) 0 := by
    apply Continuous.continuousWithinAt; fun_prop
  have hint : IntegrableOn (fun x : ℝ => x * rexp (-b * x ^ 2)) (Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have htend : Tendsto (fun y : ℝ => -rexp (-b * y ^ 2) / (2 * b)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => -b * x ^ 2) atTop atBot := by
      have h0 : Tendsto (fun x : ℝ => b * x ^ 2) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hb (tendsto_pow_atTop (by norm_num))
      simpa [neg_mul] using h0
    have h2 : Tendsto (fun x : ℝ => rexp (-b * x ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using (h2.neg.div_const (2 * b))
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [key]
  norm_num
  ring


/-! ## The one-sided Gaussian moment -/

open ProbabilityTheory

/-- The one-sided first moment of a mean-zero Gaussian. Mathlib has no
absolute or one-sided moment for the Gaussian; this is the missing piece of
the Gaussian case. -/
theorem integral_Ioi_gaussianReal {v : NNReal} (hv : v ≠ 0) :
    ∫ x in Ioi (0 : ℝ), x ∂(gaussianReal 0 v) = (√(2 * π * v))⁻¹ * v := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    have : (0 : NNReal) < v := pos_iff_ne_zero.mpr hv
    exact_mod_cast this
  have hb : (0 : ℝ) < 1 / (2 * (v : ℝ)) := by positivity
  rw [gaussianReal_of_var_ne_zero _ hv,
    setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top) (fun x : ℝ => x) measurableSet_Ioi]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal]
  have hrw : ∀ x : ℝ, (√(2 * π * v))⁻¹ * rexp (-(x - 0) ^ 2 / (2 * v)) * x
      = (√(2 * π * v))⁻¹ * (x * rexp (-(1 / (2 * (v : ℝ))) * x ^ 2)) := by
    intro x
    rw [show -(x - 0) ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * (v : ℝ))) * x ^ 2 by
      field_simp; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hrw x),
    integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hb]
  congr 1
  field_simp

/-! ## The half-normal mean of the Gaussian case -/

/-- The scale identity behind the mean `β √(2/π)`: doubling the one-sided
moment of a mean-zero Gaussian of standard deviation `σ` (the conditioning on
one sign divides by the mass `1/2`) gives `σ √(2/π)`. -/
theorem two_mul_oneSided_eq {σ : ℝ} (hσ : 0 < σ) :
    2 * ((√(2 * π * σ ^ 2))⁻¹ * σ ^ 2) = σ * √(2 / π) := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hs2 : √(σ ^ 2) = σ := Real.sqrt_sq hσ.le
  have hsplit : √(2 * π * σ ^ 2) = √(2 * π) * σ := by
    rw [Real.sqrt_mul (by positivity), hs2]
  have hdiv : √(2 / π) = √2 / √π := Real.sqrt_div' 2 hπ.le
  have hmul : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : √π * √π = π := Real.mul_self_sqrt hπ.le
  have h2ne : √2 ≠ 0 := by positivity
  have hpne : √π ≠ 0 := by positivity
  rw [hsplit, hdiv, hmul]
  field_simp
  nlinarith [h2, hp, hσ, Real.sqrt_nonneg 2, Real.sqrt_nonneg π]

/-- **The Gaussian case, the half-normal mean.** Under symmetric Gaussian residuals
of standard deviation `σ`, the mean of the leading-order slack-side law is
`β √(2/π)`, with `β = c₀ L w σ` the scale of the Remark, the constant `c₀`
being written here as `(1 + sh2) / 2` (one in the paper's case `sh2 = 1`). -/
theorem conditional_mean_eq {L w sh2 σ : ℝ} (hσ : 0 < σ) :
    L * w / 2 * (1 + sh2) * (2 * ((√(2 * π * σ ^ 2))⁻¹ * σ ^ 2))
      = L * w * σ * (1 + sh2) / 2 * √(2 / π) := by
  rw [two_mul_oneSided_eq hσ]
  ring

end GaussianMoment

end MasterEquation
