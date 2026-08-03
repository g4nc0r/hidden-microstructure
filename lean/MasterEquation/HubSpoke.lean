/-
The homogeneous hub-spoke kernel of Appendix D, §6.

This file derives the kernel of eq. (8) from Theorem 1 and proves the three
deterministic ingredients the propagation-of-chaos argument consumes: the
binding-side rule and leftover magnitude (eqs. D.3 and D.4), the
binding-side-reset contraction that anchors uniqueness of the McKean-Vlasov
fixed point, and the Foster-Lyapunov drift bound (eq. D.5).

Modelling conventions, all as declared in Appendix D. Leading-order-in-`w`
expressions are taken as definitions rather than derived with remainder
control: the swap is routed at spot so that the perfect-routing target is
`σ_x* = -(L w + b - h) / 2`, and the slippage residual enters multiplicatively
as `σ = σ*(1 + ε)`, giving the post-swap mint inputs below. In the pool frame
the hub occupies the `T1` position and the spoke the `T0` position.

What this file does not contain is the limit theory itself: Lemma 2
(existence and uniqueness of the stationary law, via Meyn-Tweedie), the
tightness claim, and Propositions 2 and 3's weak-convergence statements are
out of scope; see the README.
-/
import MasterEquation.MasterJump

set_option linter.style.header false

namespace MasterEquation

namespace HubSpoke

variable {L w b b' h ε sh2 g : ℝ}

/-- Post-swap token-0 mint input at the boundary trigger, to leading order in
`w` (Appendix D). -/
noncomputable def xhat (L w b h ε : ℝ) : ℝ :=
  (h + L * w + b) / 2 + (L * w + b - h) * ε / 2

/-- Post-swap token-1 mint input, carrying the swap-routing slope `s_h²`. -/
noncomputable def yhat (L w b h ε sh2 : ℝ) : ℝ :=
  (h + L * w + b) / 2 - (L * w + b - h) * ε * sh2 / 2

/-- **Eq. (D.3).** The routing conservation collapses the swap noise to a
single residual, so the input imbalance is one term. -/
theorem hat_diff : xhat L w b h ε - yhat L w b h ε sh2
    = (L * w + b - h) * ε * (1 + sh2) / 2 := by
  unfold xhat yhat; ring

/-! ## The kernel (eq. 8) -/

/-- Post-event spoke balance. -/
noncomputable def spokePost (L w b h ε sh2 : ℝ) : ℝ :=
  max ((L * w + b - h) * ε * (1 + sh2) / 2) 0

/-- Post-event hub balance. -/
noncomputable def hubPost (L w b h ε sh2 : ℝ) : ℝ :=
  max (-((L * w + b - h) * ε * (1 + sh2) / 2)) 0

/-- With symmetric leading-order routing the two per-unit-liquidity
requirements coincide, and Theorem 1's dust credits collapse to the positive
and negative parts of the input imbalance. -/
theorem dust_of_symmetric_requirements {xh yh : ℝ} (hg : 0 < g) :
    dustX xh yh g g = max (xh - yh) 0 ∧ dustY xh yh g g = max (yh - xh) 0 := by
  have hmin : Lnew xh yh g g = min xh yh / g := by
    unfold Lnew; rw [min_div_div_right hg.le]
  constructor
  · unfold dustX
    rw [hmin, div_mul_cancel₀ _ hg.ne']
    rcases le_total xh yh with hc | hc
    · rw [min_eq_left hc, sub_self, max_eq_right (by linarith)]
    · rw [min_eq_right hc, max_eq_left (by linarith)]
  · unfold dustY
    rw [hmin, div_mul_cancel₀ _ hg.ne']
    rcases le_total xh yh with hc | hc
    · rw [min_eq_left hc, max_eq_left (by linarith)]
    · rw [min_eq_right hc, sub_self, max_eq_right (by linarith)]

/-- **Eq. (8).** The hub-spoke kernel is exactly Theorem 1's jump applied to
the post-swap inputs under symmetric routing. -/
theorem kernel_eq_master_jump (hg : 0 < g) :
    dustX (xhat L w b h ε) (yhat L w b h ε sh2) g g = spokePost L w b h ε sh2 ∧
      dustY (xhat L w b h ε) (yhat L w b h ε sh2) g g = hubPost L w b h ε sh2 := by
  obtain ⟨h1, h2⟩ := dust_of_symmetric_requirements
    (xh := xhat L w b h ε) (yh := yhat L w b h ε sh2) hg
  rw [h1, h2, hat_diff]
  refine ⟨rfl, ?_⟩
  unfold hubPost
  rw [show yhat L w b h ε sh2 - xhat L w b h ε
      = -(xhat L w b h ε - yhat L w b h ε sh2) by ring, hat_diff]

/-- **Binding side, eq. (D.3).** The spoke binds, resetting to zero, exactly
when the displacement and the slippage residual have opposite signs. -/
theorem spoke_binds_iff (hsh : 0 < 1 + sh2) :
    spokePost L w b h ε sh2 = 0 ↔ (L * w + b - h) * ε ≤ 0 := by
  unfold spokePost
  rw [max_eq_right_iff]
  constructor
  · intro hle; nlinarith
  · intro hle; nlinarith

/-- **Leftover magnitude, eq. (D.4).** Exactly one of the two balances is
non-zero after the event, and its size is the input imbalance. -/
theorem leftover_magnitude : spokePost L w b h ε sh2 + hubPost L w b h ε sh2
    = |L * w + b - h| * |ε| * |1 + sh2| / 2 := by
  unfold spokePost hubPost
  rw [show |L * w + b - h| * |ε| * |1 + sh2| / 2
      = |(L * w + b - h) * ε * (1 + sh2) / 2| by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul, abs_mul]]
  rcases le_total ((L * w + b - h) * ε * (1 + sh2) / 2) 0 with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith), zero_add, abs_of_nonpos hc]
  · rw [max_eq_left hc, max_eq_right (by linarith), add_zero, abs_of_nonneg hc]

/-- Exactly one side carries dust. -/
theorem post_mul_eq_zero :
    spokePost L w b h ε sh2 * hubPost L w b h ε sh2 = 0 := by
  unfold spokePost hubPost
  rcases le_total ((L * w + b - h) * ε * (1 + sh2) / 2) 0 with hc | hc
  · rw [max_eq_right hc, zero_mul]
  · rw [max_eq_right (by linarith : -((L * w + b - h) * ε * (1 + sh2) / 2) ≤ 0),
      mul_zero]

/-! ## The binding-side-reset contraction

Uniqueness of the McKean-Vlasov fixed point in Appendix D is anchored not on
the TV-Lipschitz constant of assumption (A5), which may exceed one, but on
the reset: whenever the spoke binds, any difference between two coupled
spoke chains is annihilated outright. -/

/-- Two spoke chains coupled through shared `(δ, ε)` and a shared hub state
contract at rate `|ε| |1 + s_h²| / 2` per event. -/
theorem coupled_step_lipschitz :
    |spokePost L w b h ε sh2 - spokePost L w b' h ε sh2|
      ≤ |ε| * |1 + sh2| / 2 * |b - b'| := by
  unfold spokePost
  refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
  rw [show (L * w + b - h) * ε * (1 + sh2) / 2
        - (L * w + b' - h) * ε * (1 + sh2) / 2
      = (b - b') * (ε * (1 + sh2) / 2) by ring, abs_mul, abs_div,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
  ring

/-- The reset itself: on the binding event the difference is annihilated,
whatever the two pre-event spoke balances were. -/
theorem coupled_step_reset (hsh : 0 < 1 + sh2)
    (hb : (L * w + b - h) * ε ≤ 0) (hb' : (L * w + b' - h) * ε ≤ 0) :
    spokePost L w b h ε sh2 - spokePost L w b' h ε sh2 = 0 := by
  rw [(spoke_binds_iff hsh).mpr hb, (spoke_binds_iff hsh).mpr hb', sub_zero]

/-! ## Foster-Lyapunov drift (eq. D.5) -/

/-- The quadratic Lyapunov function of Appendix D restricted to the firing
pool's two coordinates. -/
noncomputable def lyap (h b : ℝ) : ℝ := h ^ 2 + b ^ 2

/-- The post-event Lyapunov value is the squared leftover, since one
coordinate is reset to zero. -/
theorem lyap_post :
    lyap (hubPost L w b h ε sh2) (spokePost L w b h ε sh2)
      = ((L * w + b - h) * ε * (1 + sh2) / 2) ^ 2 := by
  unfold lyap spokePost hubPost
  rcases le_total ((L * w + b - h) * ε * (1 + sh2) / 2) 0 with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith)]; ring
  · rw [max_eq_left hc, max_eq_right (by linarith)]; ring

/-- **Eq. (D.5), pointwise form.** Wherever the slippage residual is small
enough that `ε² (1 + s_h²)² ≤ 1/2`, the per-event drift of the quadratic
Lyapunov function is negative outside a compact set of size `O((Lw σ)²)`. -/
theorem foster_drift_pointwise (hε : ε ^ 2 * (1 + sh2) ^ 2 ≤ 1 / 2) :
    lyap (hubPost L w b h ε sh2) (spokePost L w b h ε sh2) - lyap h b
      ≤ -(1 / 2) * h ^ 2 - (1 / 2) * b ^ 2
        + (1 / 2) * (L * w) ^ 2 * (ε ^ 2 * (1 + sh2) ^ 2) := by
  rw [lyap_post]
  unfold lyap
  have hcnn : 0 ≤ ε ^ 2 * (1 + sh2) ^ 2 := by positivity
  have hsq : ((L * w + b - h) * ε * (1 + sh2) / 2) ^ 2
      = (L * w + b - h) ^ 2 * (ε ^ 2 * (1 + sh2) ^ 2) / 4 := by ring
  rw [hsq]
  have hexp : (L * w + b - h) ^ 2 ≤ 2 * (L * w) ^ 2 + 4 * b ^ 2 + 4 * h ^ 2 := by
    nlinarith [sq_nonneg (b + h), sq_nonneg (L * w + b - h), sq_nonneg (L * w - b + h)]
  nlinarith [mul_le_mul_of_nonneg_right hexp hcnn]

/-- **Eq. (D.5).** Integrating the pointwise bound against a slippage law
supported where the smallness condition holds gives the drift inequality of
Appendix D: the drift is negative outside a compact set whose size is
`O((L w σ_slip)²)`, which is the Foster-Lyapunov input both routes to (A4)
require from the model definition. -/
theorem foster_drift_integral (ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure ν]
    (hsmall : ∀ᵐ e ∂ν, e ^ 2 * (1 + sh2) ^ 2 ≤ 1 / 2)
    (hint : MeasureTheory.Integrable (fun e => e ^ 2) ν)
    (hpost : MeasureTheory.Integrable
      (fun e => lyap (hubPost L w b h e sh2) (spokePost L w b h e sh2)) ν) :
    (∫ e, lyap (hubPost L w b h e sh2) (spokePost L w b h e sh2) ∂ν) - lyap h b
      ≤ -(1 / 2) * h ^ 2 - (1 / 2) * b ^ 2
        + (1 / 2) * (L * w) ^ 2 * (1 + sh2) ^ 2 * (∫ e, e ^ 2 ∂ν) := by
  have hAint : MeasureTheory.Integrable
      (fun e : ℝ => (lyap h b - (1 / 2) * h ^ 2 - (1 / 2) * b ^ 2)
        + (1 / 2) * (L * w) ^ 2 * (1 + sh2) ^ 2 * e ^ 2) ν :=
    (MeasureTheory.integrable_const _).add (hint.const_mul _)
  have hbound : ∀ᵐ e ∂ν,
      lyap (hubPost L w b h e sh2) (spokePost L w b h e sh2)
        ≤ (lyap h b - (1 / 2) * h ^ 2 - (1 / 2) * b ^ 2)
          + (1 / 2) * (L * w) ^ 2 * (1 + sh2) ^ 2 * e ^ 2 := by
    filter_upwards [hsmall] with e he
    have hp := foster_drift_pointwise (L := L) (w := w) (b := b) (h := h)
      (ε := e) (sh2 := sh2) he
    rw [show (1 : ℝ) / 2 * (L * w) ^ 2 * (e ^ 2 * (1 + sh2) ^ 2)
        = (1 : ℝ) / 2 * (L * w) ^ 2 * (1 + sh2) ^ 2 * e ^ 2 from by ring] at hp
    linarith
  have hmono := MeasureTheory.integral_mono_ae hpost hAint hbound
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _)
      (hint.const_mul _), MeasureTheory.integral_const,
    MeasureTheory.integral_const_mul] at hmono
  simp only [MeasureTheory.probReal_univ, one_smul] at hmono
  linarith

end HubSpoke

end MasterEquation
