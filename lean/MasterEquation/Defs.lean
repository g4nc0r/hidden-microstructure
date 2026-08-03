/-
Shared definitions for the Lean formalisation of "The Hidden Microstructure of
Shared-Balance Concentrated Liquidity".

The V3 amount functions of Appendix B and the mint linear programme of
Theorem 1 (§4.1), used by every theorem file.

Setting: a pool with tokens `Ta` at the `T0` position and `Tb` at the `T1`
position, sqrt price `s`, new range `[sa', sb']`, per-unit-liquidity token
requirements `gx = ax s sa' sb'` and `gy = ay s sa' sb'`, and mint inputs
`xh = x_w + x_dust - σ_x`, `yh = y_w + y_dust - σ_y`.

The kernel here is a copy of the corresponding surface in the Geometric
Siphon formalisation, generalised from the isolated single-pool case to
arbitrary mint inputs; the Geometric Siphon repository owns the original.
Programme convention is to share by copy, not by symlink.
-/
import Mathlib

set_option linter.style.header false

namespace MasterEquation

/-! ## V3 amount functions (Appendix B) -/

/-- V3 token-0 amount per unit liquidity over `[sa, sb]` at sqrt price `s`. -/
noncomputable def ax (s sa sb : ℝ) : ℝ :=
  if s ≤ sa then 1 / sa - 1 / sb else if s < sb then 1 / s - 1 / sb else 0

/-- V3 token-1 amount per unit liquidity over `[sa, sb]` at sqrt price `s`. -/
noncomputable def ay (s sa sb : ℝ) : ℝ :=
  if s ≤ sa then 0 else if s < sb then s - sa else sb - sa

lemma ax_of_mem {s sa sb : ℝ} (h1 : sa < s) (h2 : s < sb) :
    ax s sa sb = 1 / s - 1 / sb := by
  unfold ax; rw [if_neg (not_le.mpr h1), if_pos h2]

lemma ay_of_mem {s sa sb : ℝ} (h1 : sa < s) (h2 : s < sb) :
    ay s sa sb = s - sa := by
  unfold ay; rw [if_neg (not_le.mpr h1), if_pos h2]

lemma ax_of_le {s sa sb : ℝ} (h : s ≤ sa) : ax s sa sb = 1 / sa - 1 / sb := by
  unfold ax; rw [if_pos h]

lemma ay_of_le {s sa sb : ℝ} (h : s ≤ sa) : ay s sa sb = 0 := by
  unfold ay; rw [if_pos h]

lemma ax_of_ge {s sa sb : ℝ} (h0 : sa < s) (h : sb ≤ s) : ax s sa sb = 0 := by
  unfold ax; rw [if_neg (not_le.mpr h0), if_neg (not_lt.mpr h)]

lemma ay_of_ge {s sa sb : ℝ} (h0 : sa < s) (h : sb ≤ s) : ay s sa sb = sb - sa := by
  unfold ay; rw [if_neg (not_le.mpr h0), if_neg (not_lt.mpr h)]

/-- Both amount coefficients are strictly positive strictly inside the range. -/
lemma amount_coeffs_pos {s sa sb : ℝ} (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb) :
    0 < ax s sa sb ∧ 0 < ay s sa sb := by
  have hs : 0 < s := h0.trans h1
  rw [ax_of_mem h1 h2, ay_of_mem h1 h2]
  exact ⟨sub_pos.mpr (one_div_lt_one_div_of_lt hs h2), sub_pos.mpr h1⟩

/-- `ay` is monotone in the sqrt price (Appendix B). -/
lemma ay_mono {sa sb : ℝ} (hab : sa ≤ sb) : Monotone (fun s => ay s sa sb) := by
  intro u v huv
  simp only [ay]
  split_ifs <;> first | rfl | linarith

/-! ## The mint linear programme (Theorem 1, §4.1) -/

/-- New liquidity from the mint LP, eq. (3): `L_new = min (x̂ / g_x) (ŷ / g_y)`. -/
noncomputable def Lnew (xh yh gx gy : ℝ) : ℝ := min (xh / gx) (yh / gy)

/-- Token-0 dust credit after the mint, eq. (4). -/
noncomputable def dustX (xh yh gx gy : ℝ) : ℝ := xh - Lnew xh yh gx gy * gx

/-- Token-1 dust credit after the mint, eq. (4). -/
noncomputable def dustY (xh yh gx gy : ℝ) : ℝ := yh - Lnew xh yh gx gy * gy

/-- The feasible set of the mint LP, eq. (A.1). -/
def mintFeasible (xh yh gx gy : ℝ) : Set ℝ :=
  {L : ℝ | 0 ≤ L ∧ L * gx ≤ xh ∧ L * gy ≤ yh}

end MasterEquation
