/-
Theorem 1 (Master Equation jump), §4.1, proved in Appendix A.

The mint is a one-dimensional linear programme; `Lnew` is its optimum, the
dust credits are the slack, and the LP-min structure forces at least one of
them to vanish in the swap-free regime, with exactly one vanishing off the
ratio-preserving locus.

The boundary sub-cases (ii) and (iii) of Appendix A lie outside the
theorem's hypothesis and are recorded here for completeness, as in the paper.
-/
import MasterEquation.Defs

set_option linter.style.header false

namespace MasterEquation

variable {xh yh gx gy : ℝ}

/-! ## The mint as a linear programme (Appendix A, eq. A.1) -/

/-- **Theorem 1, eq. (3).** In range (`gx, gy > 0`) the closed form
`L_new = min (x̂ / g_x) (ŷ / g_y)` is the optimum of the mint LP. -/
theorem lnew_isGreatest (hgx : 0 < gx) (hgy : 0 < gy) (hx : 0 ≤ xh) (hy : 0 ≤ yh) :
    IsGreatest (mintFeasible xh yh gx gy) (Lnew xh yh gx gy) := by
  constructor
  · refine ⟨le_min (div_nonneg hx hgx.le) (div_nonneg hy hgy.le), ?_, ?_⟩
    · calc Lnew xh yh gx gy * gx ≤ xh / gx * gx := by
            exact mul_le_mul_of_nonneg_right (min_le_left _ _) hgx.le
        _ = xh := div_mul_cancel₀ _ hgx.ne'
    · calc Lnew xh yh gx gy * gy ≤ yh / gy * gy := by
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hgy.le
        _ = yh := div_mul_cancel₀ _ hgy.ne'
  · rintro L ⟨_, hLx, hLy⟩
    exact le_min ((le_div_iff₀ hgx).mpr hLx) ((le_div_iff₀ hgy).mpr hLy)

/-! ## The dust credits (Theorem 1, eq. (4)) -/

/-- Both dust credits are non-negative: the mint never over-spends. -/
theorem dust_nonneg (hgx : 0 < gx) (hgy : 0 < gy) (hx : 0 ≤ xh) (hy : 0 ≤ yh) :
    0 ≤ dustX xh yh gx gy ∧ 0 ≤ dustY xh yh gx gy := by
  obtain ⟨⟨_, hfx, hfy⟩, _⟩ := lnew_isGreatest hgx hgy hx hy
  exact ⟨sub_nonneg.mpr hfx, sub_nonneg.mpr hfy⟩

/-- The binding side is the smaller candidate liquidity: token 0's constraint
binds exactly when `x̂ g_y ≤ ŷ g_x`, i.e. `x̂ / ŷ ≤ g_x / g_y`. -/
theorem dustX_eq_zero_iff (hgx : 0 < gx) (hgy : 0 < gy) :
    dustX xh yh gx gy = 0 ↔ xh * gy ≤ yh * gx := by
  have hkey : xh / gx ≤ yh / gy ↔ xh * gy ≤ yh * gx := by
    rw [div_le_div_iff₀ hgx hgy]
  unfold dustX Lnew
  rcases le_total (xh / gx) (yh / gy) with h | h
  · rw [min_eq_left h, div_mul_cancel₀ _ hgx.ne', sub_self]
    simp [hkey.mp h]
  · rw [min_eq_right h, sub_eq_zero]
    constructor
    · intro hEq
      have : xh / gx = yh / gy := by
        field_simp at hEq ⊢; linarith [hEq]
      exact hkey.mp this.le
    · intro hle
      have : xh / gx = yh / gy := le_antisymm (hkey.mpr hle) h
      rw [← this, div_mul_cancel₀ _ hgx.ne']

/-- Symmetric statement for token 1. -/
theorem dustY_eq_zero_iff (hgx : 0 < gx) (hgy : 0 < gy) :
    dustY xh yh gx gy = 0 ↔ yh * gx ≤ xh * gy := by
  have hkey : yh / gy ≤ xh / gx ↔ yh * gx ≤ xh * gy := by
    rw [div_le_div_iff₀ hgy hgx]
  unfold dustY Lnew
  rcases le_total (yh / gy) (xh / gx) with h | h
  · rw [min_eq_right h, div_mul_cancel₀ _ hgy.ne', sub_self]
    simp [hkey.mp h]
  · rw [min_eq_left h, sub_eq_zero]
    constructor
    · intro hEq
      have : yh / gy = xh / gx := by
        field_simp at hEq ⊢; linarith [hEq]
      exact hkey.mp this.le
    · intro hle
      have : yh / gy = xh / gx := le_antisymm (hkey.mpr hle) h
      rw [← this, div_mul_cancel₀ _ hgy.ne']

/-- **Theorem 1, LP-min structure.** At least one dust credit vanishes. -/
theorem dust_mul_eq_zero (hgx : 0 < gx) (hgy : 0 < gy) :
    dustX xh yh gx gy * dustY xh yh gx gy = 0 := by
  rcases le_total (xh * gy) (yh * gx) with h | h
  · exact mul_eq_zero_of_left ((dustX_eq_zero_iff hgx hgy).mpr h) _
  · exact mul_eq_zero_of_right _ ((dustY_eq_zero_iff hgx hgy).mpr h)

/-- **Theorem 1, ratio-preserving locus.** Both credits vanish exactly on
`x̂ / ŷ = g_x / g_y`; this is the measure-zero locus of Theorem 1 of the
prior paper, and the routing target of the swap step. -/
theorem dust_both_zero_iff (hgx : 0 < gx) (hgy : 0 < gy) :
    (dustX xh yh gx gy = 0 ∧ dustY xh yh gx gy = 0) ↔ xh * gy = yh * gx := by
  rw [dustX_eq_zero_iff hgx hgy, dustY_eq_zero_iff hgx hgy]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- **Theorem 1, exactly-one-zero.** Off the ratio-preserving locus exactly
one credit vanishes and the other is strictly positive: the surplus on the
slack-side token. -/
theorem exactly_one_dust_zero (hgx : 0 < gx) (hgy : 0 < gy) (hx : 0 ≤ xh)
    (hy : 0 ≤ yh) (hne : xh * gy ≠ yh * gx) :
    (dustX xh yh gx gy = 0 ∧ 0 < dustY xh yh gx gy) ∨
      (0 < dustX xh yh gx gy ∧ dustY xh yh gx gy = 0) := by
  obtain ⟨hnx, hny⟩ := dust_nonneg hgx hgy hx hy
  rcases lt_or_gt_of_ne hne with h | h
  · refine Or.inl ⟨(dustX_eq_zero_iff hgx hgy).mpr h.le, hny.lt_of_ne' ?_⟩
    intro hzero
    exact absurd ((dustY_eq_zero_iff hgx hgy).mp hzero) (not_le.mpr h)
  · refine Or.inr ⟨hnx.lt_of_ne' ?_, (dustY_eq_zero_iff hgx hgy).mpr h.le⟩
    intro hzero
    exact absurd ((dustX_eq_zero_iff hgx hgy).mp hzero) (not_le.mpr h)

/-- The slack-side leftover in closed form when token 0 binds
(Appendix A, sub-case (i)): `y'_dust = ŷ - x̂ (g_y / g_x)`. -/
theorem slack_leftover_of_token0_binds (hgx : 0 < gx) (hgy : 0 < gy)
    (h : xh * gy ≤ yh * gx) :
    dustY xh yh gx gy = yh - xh * (gy / gx) := by
  have hmin : Lnew xh yh gx gy = xh / gx :=
    min_eq_left ((div_le_div_iff₀ hgx hgy).mpr h)
  unfold dustY
  rw [hmin]
  field_simp

/-- The total leftover across both tokens is the input imbalance. -/
theorem dust_add_eq_abs_sub (hgx : 0 < gx) (hgy : 0 < gy) (hg : gx = gy) :
    dustX xh yh gx gy + dustY xh yh gx gy = |xh - yh| := by
  subst hg
  unfold dustX dustY Lnew
  rcases le_total xh yh with h | h
  · rw [min_eq_left (by gcongr), div_mul_cancel₀ _ hgx.ne',
      abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right (by gcongr), div_mul_cancel₀ _ hgx.ne',
      abs_of_nonneg (by linarith)]
    ring

/-! ## Boundary sub-cases (Appendix A, sub-cases (ii) and (iii)) -/

/-- Sub-case (ii), `s ≤ s_a'`: only the token-0 constraint is active, the new
position is single-sided in token 0, and the whole token-1 input is left as
dust. -/
theorem lp_below_range (hgx : 0 < gx) (hx : 0 ≤ xh) (hy : 0 ≤ yh) :
    IsGreatest (mintFeasible xh yh gx 0) (xh / gx) ∧
      xh - (xh / gx) * gx = 0 ∧ yh - (xh / gx) * 0 = yh := by
  refine ⟨⟨⟨div_nonneg hx hgx.le, le_of_eq (div_mul_cancel₀ _ hgx.ne'), by simpa⟩, ?_⟩,
    by rw [div_mul_cancel₀ _ hgx.ne', sub_self], by ring⟩
  rintro L ⟨_, hLx, -⟩
  exact (le_div_iff₀ hgx).mpr hLx

/-- Sub-case (iii), `s ≥ s_b'`: symmetric, single-sided in token 1. -/
theorem lp_above_range (hgy : 0 < gy) (hx : 0 ≤ xh) (hy : 0 ≤ yh) :
    IsGreatest (mintFeasible xh yh 0 gy) (yh / gy) ∧
      xh - (yh / gy) * 0 = xh ∧ yh - (yh / gy) * gy = 0 := by
  refine ⟨⟨⟨div_nonneg hy hgy.le, by simpa, le_of_eq (div_mul_cancel₀ _ hgy.ne')⟩, ?_⟩,
    by ring, by rw [div_mul_cancel₀ _ hgy.ne', sub_self]⟩
  rintro L ⟨-, -, hLy⟩
  exact (le_div_iff₀ hgy).mpr hLy

/-! ## The single-pool swap-free corner (§4.2) -/

/-- **Corner reduction.** With one position, no standing dust and no swap
correction, the Master Equation mint reduces to the isolated-case mint
minimum of the prior paper (Geometric Siphon, eq. 6), which is the corner in
which Theorems 1 and 3 there are recovered. -/
theorem lnew_gs_corner {L s sa sb sa' sb' : ℝ} (h1 : sa < s) (h2 : s < sb)
    (h1' : sa' < s) (h2' : s < sb') :
    Lnew (L * ax s sa sb) (L * ay s sa sb) (ax s sa' sb') (ay s sa' sb')
      = min (L * (1 / s - 1 / sb) / (1 / s - 1 / sb'))
            (L * (s - sa) / (s - sa')) := by
  rw [ax_of_mem h1 h2, ay_of_mem h1 h2, ax_of_mem h1' h2', ay_of_mem h1' h2']
  unfold Lnew
  rw [mul_div_assoc, mul_div_assoc]

end MasterEquation
