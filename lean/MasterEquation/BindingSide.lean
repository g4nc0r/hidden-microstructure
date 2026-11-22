/-
Proposition 1 (binding-side criterion) with Corollary 1 (swap-free rule) and
Corollary 2 (swap-corrected rule), the section "Binding-side sign rule".

The proposition is Theorem 1 written in value shares, for one rebalance of one
pool. The two corollaries read it for ranges centred in tick space: the old
range on `s₀`, so that `sa * sb = s₀²`, and the new range on the price `s`, so
that `sa' * sb' = s²` and the new range takes the two tokens in equal value,
`g_y = s² g_x`.

Values are in units of token 1 at the mint price `s`. The paper writes the
share of the withdrawn value a centred range cannot take without a swap as
`α(ℓ) = sinh|ℓ| / (e^h - cosh ℓ)`, with `ℓ = ln(s / s₀)` and `h = ln(sb / s₀)`.
Here `alpha` is defined algebraically in `s`, `s₀`, `sb`, and `alpha_eq_sinh`
identifies the two forms.

This file replaces `ConnectorRule.lean`, which formalised the statement that
earlier versions of the paper gave as Proposition 1. Nothing here concerns the
connectivity of a token.
-/
import MasterEquation.MasterJump

set_option linter.style.header false

namespace MasterEquation

variable {s s0 sa sb gx gy L xd yd xw yw xh yh : ℝ}

/-! ## The binding side of one mint -/

/-- Token 1 binds, and so token 0 is the one that can be left, exactly when
the supply ratio exceeds the required ratio. -/
theorem token1_binds_iff (hgx : 0 < gx) (hgy : 0 < gy) :
    dustY xh yh gx gy = 0 ↔ yh * gx ≤ xh * gy :=
  dustY_eq_zero_iff hgx hgy

/-- When token 1 binds strictly, token 0 carries the whole leftover. -/
theorem token0_leaks (hgx : 0 < gx) (hgy : 0 < gy) (hx : 0 ≤ xh)
    (hy : 0 ≤ yh) (h : yh * gx < xh * gy) :
    dustY xh yh gx gy = 0 ∧ 0 < dustX xh yh gx gy := by
  rcases exactly_one_dust_zero hgx hgy hx hy (ne_of_gt h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd ((dustX_eq_zero_iff hgx hgy).mp h1) (not_le.mpr h)
  · exact ⟨h2, h1⟩

/-- When token 0 binds strictly, token 1 carries the whole leftover. -/
theorem token1_leaks (hgx : 0 < gx) (hgy : 0 < gy) (hx : 0 ≤ xh)
    (hy : 0 ≤ yh) (h : xh * gy < yh * gx) :
    dustX xh yh gx gy = 0 ∧ 0 < dustY xh yh gx gy := by
  rcases exactly_one_dust_zero hgx hgy hx hy (ne_of_lt h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd ((dustY_eq_zero_iff hgx hgy).mp h2) (not_le.mpr h)

/-- The slack-side leftover in closed form when token 1 binds:
`x'_dust = x̂ - ŷ (g_x / g_y)`. -/
theorem slack_leftover_of_token1_binds (hgx : 0 < gx) (hgy : 0 < gy)
    (h : yh * gx ≤ xh * gy) :
    dustX xh yh gx gy = xh - yh * (gx / gy) := by
  have hmin : Lnew xh yh gx gy = yh / gy :=
    min_eq_right ((div_le_div_iff₀ hgy hgx).mpr h)
  unfold dustX
  rw [hmin]
  field_simp

/-! ## Proposition 1: the criterion in value shares -/

/-- Share of token 0 in the value supplied to the mint, `ω̂`. -/
noncomputable def shareSupplied (s xh yh : ℝ) : ℝ :=
  s ^ 2 * xh / (s ^ 2 * xh + yh)

/-- Share of token 0 in the value the new range requires, `ω'`. -/
noncomputable def shareRequired (s gx gy : ℝ) : ℝ :=
  s ^ 2 * gx / (s ^ 2 * gx + gy)

/-- The required share lies strictly between zero and one for a range that has
the price in its interior. -/
theorem shareRequired_mem (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy) :
    0 < shareRequired s gx gy ∧ shareRequired s gx gy < 1 := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hG : 0 < s ^ 2 * gx + gy := by positivity
  unfold shareRequired
  exact ⟨by positivity, (div_lt_one hG).mpr (by linarith)⟩

/-- The gap between the two shares has the sign of `x̂ g_y - ŷ g_x`. -/
theorem share_sub (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh) :
    shareSupplied s xh yh - shareRequired s gx gy
      = s ^ 2 * (xh * gy - yh * gx) / ((s ^ 2 * xh + yh) * (s ^ 2 * gx + gy)) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hG : s ^ 2 * gx + gy ≠ 0 := by positivity
  have hW' : s ^ 2 * xh + yh ≠ 0 := hW.ne'
  unfold shareSupplied shareRequired
  rw [div_sub_div _ _ hW' hG]
  congr 1
  ring

theorem share_lt_iff (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh) :
    shareSupplied s xh yh < shareRequired s gx gy ↔ xh * gy < yh * gx := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hG : 0 < s ^ 2 * gx + gy := by positivity
  have hden : 0 < (s ^ 2 * xh + yh) * (s ^ 2 * gx + gy) := mul_pos hW hG
  rw [← sub_neg, share_sub hs hgx hgy hW]
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have hnn : 0 ≤ s ^ 2 * (xh * gy - yh * gx) := mul_nonneg hs2.le (by linarith)
    exact absurd h (not_lt.mpr (div_nonneg hnn hden.le))
  · intro h
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs2 (by linarith)) hden

theorem share_gt_iff (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh) :
    shareRequired s gx gy < shareSupplied s xh yh ↔ yh * gx < xh * gy := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hG : 0 < s ^ 2 * gx + gy := by positivity
  have hden : 0 < (s ^ 2 * xh + yh) * (s ^ 2 * gx + gy) := mul_pos hW hG
  rw [← sub_pos, share_sub hs hgx hgy hW]
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have hnp : s ^ 2 * (xh * gy - yh * gx) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs2.le (by linarith)
    exact absurd h (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hnp hden.le))
  · intro h
    exact div_pos (mul_pos hs2 (by linarith)) hden

theorem share_eq_iff (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh) :
    shareSupplied s xh yh = shareRequired s gx gy ↔ xh * gy = yh * gx := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (ne_of_lt ((share_lt_iff hs hgx hgy hW).mpr hlt))
    · exact absurd h (ne_of_gt ((share_gt_iff hs hgx hgy hW).mpr hgt))
  · intro h
    have h1 := sub_eq_zero.mp (by
      rw [share_sub hs hgx hgy hW, h, sub_self, mul_zero, zero_div] :
      shareSupplied s xh yh - shareRequired s gx gy = 0)
    exact h1

/-- **Proposition 1, first case.** If token 0 is supplied in a smaller share
than the new range requires, it is used up and the leftover is in token 1,
worth `Ŵ (ω' - ω̂) / ω'`. -/
theorem criterion_leftover_token1 (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh)
    (h : shareSupplied s xh yh < shareRequired s gx gy) :
    dustX xh yh gx gy = 0 ∧
      dustY xh yh gx gy
        = (s ^ 2 * xh + yh) * (shareRequired s gx gy - shareSupplied s xh yh)
            / shareRequired s gx gy := by
  have hlt := (share_lt_iff hs hgx hgy hW).mp h
  have hs2 : 0 < s ^ 2 := by positivity
  have hG : 0 < s ^ 2 * gx + gy := by positivity
  refine ⟨(dustX_eq_zero_iff hgx hgy).mpr hlt.le, ?_⟩
  rw [slack_leftover_of_token0_binds hgx hgy hlt.le]
  unfold shareSupplied shareRequired
  obtain ⟨W, hWdef⟩ : ∃ W, W = s ^ 2 * xh + yh := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G, G = s ^ 2 * gx + gy := ⟨_, rfl⟩
  rw [← hWdef] at hW ⊢
  rw [← hGdef] at hG ⊢
  have hW' : W ≠ 0 := hW.ne'
  have hG' : G ≠ 0 := hG.ne'
  field_simp
  rw [hWdef, hGdef]
  ring

/-- **Proposition 1, second case.** If token 0 is supplied in a larger share
than the new range requires, token 1 is used up and the leftover is in token 0,
worth `Ŵ (ω̂ - ω') / (1 - ω')` in units of token 1. -/
theorem criterion_leftover_token0 (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh)
    (h : shareRequired s gx gy < shareSupplied s xh yh) :
    dustY xh yh gx gy = 0 ∧
      s ^ 2 * dustX xh yh gx gy
        = (s ^ 2 * xh + yh) * (shareSupplied s xh yh - shareRequired s gx gy)
            / (1 - shareRequired s gx gy) := by
  have hgt := (share_gt_iff hs hgx hgy hW).mp h
  have hs2 : 0 < s ^ 2 := by positivity
  have hG : 0 < s ^ 2 * gx + gy := by positivity
  refine ⟨(dustY_eq_zero_iff hgx hgy).mpr hgt.le, ?_⟩
  rw [slack_leftover_of_token1_binds hgx hgy hgt.le]
  have h1 : 1 - shareRequired s gx gy = gy / (s ^ 2 * gx + gy) := by
    unfold shareRequired
    rw [eq_div_iff hG.ne', sub_mul, div_mul_cancel₀ _ hG.ne']
    ring
  rw [h1]
  unfold shareSupplied shareRequired
  obtain ⟨W, hWdef⟩ : ∃ W, W = s ^ 2 * xh + yh := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G, G = s ^ 2 * gx + gy := ⟨_, rfl⟩
  rw [← hWdef] at hW ⊢
  rw [← hGdef] at hG ⊢
  have hW' : W ≠ 0 := hW.ne'
  have hG' : G ≠ 0 := hG.ne'
  field_simp
  rw [hWdef, hGdef]
  ring

/-- **Proposition 1, third case.** If the two shares agree nothing is left. -/
theorem criterion_no_leftover (hs : 0 < s) (hgx : 0 < gx) (hgy : 0 < gy)
    (hW : 0 < s ^ 2 * xh + yh)
    (h : shareSupplied s xh yh = shareRequired s gx gy) :
    dustX xh yh gx gy = 0 ∧ dustY xh yh gx gy = 0 :=
  (dust_both_zero_iff hgx hgy).mpr ((share_eq_iff hs hgx hgy hW).mp h)

/-! ## Ranges centred in tick space -/

/-- A range centred on the price in tick space, `sa' * sb' = s²`, takes the two
tokens in equal value. -/
theorem centred_requirements {sa' sb' : ℝ} (h0 : 0 < sa') (h1 : sa' < s)
    (h2 : s < sb') (hc : sa' * sb' = s ^ 2) :
    ay s sa' sb' = s ^ 2 * ax s sa' sb' := by
  have hs : 0 < s := h0.trans h1
  have hb : 0 < sb' := hs.trans h2
  have e1 : s ^ 2 * (1 / s) = s := by field_simp
  have e2 : s ^ 2 * (1 / sb') = sa' := by rw [← hc]; field_simp
  rw [ax_of_mem h1 h2, ay_of_mem h1 h2, mul_sub, e1, e2]

/-- The required share of a centred range is one half. -/
theorem shareRequired_centred (hs : 0 < s) (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) :
    shareRequired s gx gy = 1 / 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  unfold shareRequired
  rw [hg]
  field_simp
  ring

/-- The surplus of token 1 over token 0, in value, of a position withdrawn
inside an old range centred on `s₀`. It has the sign of `s - s₀`. -/
theorem withdrawn_mismatch (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) :
    L * ay s sa sb - s ^ 2 * (L * ax s sa sb) = L * (s ^ 2 - s0 ^ 2) / sb := by
  have hs : 0 < s := h0.trans h1
  have hb : 0 < sb := hs.trans h2
  rw [ax_of_mem h1 h2, ay_of_mem h1 h2, ← hc]
  field_simp
  ring

/-- The withdrawn value `V = s² x_w + y_w` of the same position. -/
theorem withdrawn_value (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) :
    s ^ 2 * (L * ax s sa sb) + L * ay s sa sb
      = L * (2 * s * sb - s ^ 2 - s0 ^ 2) / sb := by
  have hs : 0 < s := h0.trans h1
  have hb : 0 < sb := hs.trans h2
  rw [ax_of_mem h1 h2, ay_of_mem h1 h2, ← hc]
  field_simp
  ring

/-- The share `α` of the withdrawn value that a new range centred on the price
cannot take without a swap, for a price inside the old range. -/
noncomputable def alpha (s s0 sb : ℝ) : ℝ :=
  |s ^ 2 - s0 ^ 2| / (2 * s * sb - s ^ 2 - s0 ^ 2)

theorem alpha_den_pos (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) : 0 < 2 * s * sb - s ^ 2 - s0 ^ 2 := by
  have hs : 0 < s := h0.trans h1
  have hb : 0 < sb := hs.trans h2
  rw [← hc]
  nlinarith [mul_pos hs (sub_pos.mpr h2), mul_pos hb (sub_pos.mpr h1)]

theorem alpha_nonneg (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) : 0 ≤ alpha s s0 sb :=
  div_nonneg (abs_nonneg _) (alpha_den_pos h0 h1 h2 hc).le

/-- `α` in the paper's form, `sinh|ℓ| / (e^h - cosh ℓ)` with `s = s₀ e^ℓ` and
`sb = s₀ e^h`. -/
theorem alpha_eq_sinh (hs0 : 0 < s0) (ℓ h : ℝ) :
    alpha (s0 * Real.exp ℓ) s0 (s0 * Real.exp h)
      = |Real.sinh ℓ| / (Real.exp h - Real.cosh ℓ) := by
  have hE : 0 < Real.exp ℓ := Real.exp_pos ℓ
  have hc : 0 < 2 * s0 ^ 2 * Real.exp ℓ := by positivity
  have hnum : (s0 * Real.exp ℓ) ^ 2 - s0 ^ 2
      = 2 * s0 ^ 2 * Real.exp ℓ * Real.sinh ℓ := by
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp
  have hden : 2 * (s0 * Real.exp ℓ) * (s0 * Real.exp h) - (s0 * Real.exp ℓ) ^ 2 - s0 ^ 2
      = 2 * s0 ^ 2 * Real.exp ℓ * (Real.exp h - Real.cosh ℓ) := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  unfold alpha
  rw [hnum, hden, abs_mul, abs_of_pos hc, mul_div_mul_left _ _ hc.ne']

/-- After an upward move inside the old range the surplus of token 1 is the
fraction `α` of the withdrawn value. -/
theorem mismatch_eq_alpha_value_up (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hup : s0 ^ 2 ≤ s ^ 2) :
    L * ay s sa sb - s ^ 2 * (L * ax s sa sb)
      = alpha s s0 sb * (s ^ 2 * (L * ax s sa sb) + L * ay s sa sb) := by
  have hb : 0 < sb := (h0.trans h1).trans h2
  have hd := alpha_den_pos h0 h1 h2 hc
  rw [withdrawn_mismatch h0 h1 h2 hc, withdrawn_value h0 h1 h2 hc]
  unfold alpha
  rw [abs_of_nonneg (sub_nonneg.mpr hup)]
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * s * sb - s ^ 2 - s0 ^ 2 := ⟨_, rfl⟩
  rw [← hD] at hd ⊢
  have hD' : D ≠ 0 := hd.ne'
  field_simp

/-- After a downward move the surplus is in token 0, by the same fraction. -/
theorem mismatch_eq_alpha_value_down (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hdown : s ^ 2 ≤ s0 ^ 2) :
    s ^ 2 * (L * ax s sa sb) - L * ay s sa sb
      = alpha s s0 sb * (s ^ 2 * (L * ax s sa sb) + L * ay s sa sb) := by
  have hb : 0 < sb := (h0.trans h1).trans h2
  have hd := alpha_den_pos h0 h1 h2 hc
  have hm := withdrawn_mismatch (L := L) h0 h1 h2 hc
  rw [show s ^ 2 * (L * ax s sa sb) - L * ay s sa sb
      = -(L * ay s sa sb - s ^ 2 * (L * ax s sa sb)) by ring, hm,
    withdrawn_value h0 h1 h2 hc]
  unfold alpha
  rw [abs_of_nonpos (sub_nonpos.mpr hdown)]
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * s * sb - s ^ 2 - s0 ^ 2 := ⟨_, rfl⟩
  rw [← hD] at hd ⊢
  have hD' : D ≠ 0 := hd.ne'
  field_simp

/-! ## The mint into a centred range, in terms of the surplus

Throughout this section the new range is centred on the price, `g_y = s² g_x`,
and `m` denotes the surplus of one token over the other in the inputs, in
value. The statements are those of Corollaries 1 and 2 with `m` in place of
`α(ℓ) V`; the corollaries follow by `mismatch_eq_alpha_value_up` and
`mismatch_eq_alpha_value_down`. -/

/-- The two credits of a centred mint in terms of the inputs. -/
theorem dust_centred (hs : 0 < s) (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) :
    dustY xh yh gx gy = max (yh - s ^ 2 * xh) 0 ∧
      s ^ 2 * dustX xh yh gx gy = max (s ^ 2 * xh - yh) 0 :=
  dust_of_proportional_requirements hgx (by positivity) hg

/-- A credit of token 0 vanishes when its value does. -/
theorem dustX_eq_zero_of_value (hs : 0 < s) (h : s ^ 2 * dustX xh yh gx gy = 0) :
    dustX xh yh gx gy = 0 := by
  have hs2 : s ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_left hs2

/-- **Corollary 1(i), in units of the surplus.** With a surplus `m ≥ 0` of
token 1 and nothing else, the leftover is in token 1 and equals the surplus. -/
theorem swapfree_surplus_token1 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hm : 0 ≤ yw - s ^ 2 * xw) :
    dustX xw yw gx gy = 0 ∧ dustY xw yw gx gy = yw - s ^ 2 * xw := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw) (yh := yw) hs hgx hg
  refine ⟨dustX_eq_zero_of_value hs ?_, ?_⟩
  · rw [hX, max_eq_right (by linarith)]
  · rw [hY, max_eq_left hm]

/-- The mirror case, a surplus of token 0. -/
theorem swapfree_surplus_token0 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hm : 0 ≤ s ^ 2 * xw - yw) :
    dustY xw yw gx gy = 0 ∧ s ^ 2 * dustX xw yw gx gy = s ^ 2 * xw - yw := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw) (yh := yw) hs hgx hg
  exact ⟨by rw [hY, max_eq_right (by linarith)], by rw [hX, max_eq_left hm]⟩

/-- **Corollary 1(ii), first clause.** A standing balance worth less than the
surplus leaves the leftover in the same token, whatever its composition. -/
theorem balance_below_surplus_keeps_token1 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hyd : 0 ≤ yd)
    (hD : s ^ 2 * xd + yd < yw - s ^ 2 * xw) :
    dustX (xw + xd) (yw + yd) gx gy = 0 ∧ 0 < dustY (xw + xd) (yw + yd) gx gy := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw + xd) (yh := yw + yd) hs hgx hg
  have hs2 : 0 < s ^ 2 := by positivity
  have hpos : 0 < yw + yd - s ^ 2 * (xw + xd) := by nlinarith
  refine ⟨dustX_eq_zero_of_value hs ?_, ?_⟩
  · rw [hX, max_eq_right (by linarith)]
  · rw [hY, max_eq_left hpos.le]; exact hpos

theorem balance_below_surplus_keeps_token0 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hxd : 0 ≤ xd)
    (hD : s ^ 2 * xd + yd < s ^ 2 * xw - yw) :
    dustY (xw + xd) (yw + yd) gx gy = 0 ∧ 0 < dustX (xw + xd) (yw + yd) gx gy := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw + xd) (yh := yw + yd) hs hgx hg
  have hs2 : 0 < s ^ 2 := by positivity
  have hpos : 0 < s ^ 2 * (xw + xd) - (yw + yd) := by nlinarith
  refine ⟨by rw [hY, max_eq_right (by linarith)], ?_⟩
  rw [max_eq_left hpos.le] at hX
  by_contra hcon
  have : s ^ 2 * dustX (xw + xd) (yw + yd) gx gy ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs2.le (not_lt.mp hcon)
  linarith

/-- **Corollary 1(ii), second clause.** A balance worth exactly the surplus,
held wholly in the binding token, removes the leftover. -/
theorem balance_equal_surplus_removes_token1 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hxd : s ^ 2 * xd = yw - s ^ 2 * xw) :
    dustX (xw + xd) yw gx gy = 0 ∧ dustY (xw + xd) yw gx gy = 0 := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw + xd) (yh := yw) hs hgx hg
  have hz : yw - s ^ 2 * (xw + xd) = 0 := by linarith [hxd]
  refine ⟨dustX_eq_zero_of_value hs ?_, ?_⟩
  · rw [hX, max_eq_right (by linarith)]
  · rw [hY, hz, max_self]

theorem balance_equal_surplus_removes_token0 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hyd : yd = s ^ 2 * xw - yw) :
    dustX xw (yw + yd) gx gy = 0 ∧ dustY xw (yw + yd) gx gy = 0 := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw) (yh := yw + yd) hs hgx hg
  have hz : yw + yd - s ^ 2 * xw = 0 := by linarith [hyd]
  refine ⟨dustX_eq_zero_of_value hs ?_, ?_⟩
  · rw [hX, max_eq_right (by linarith)]
  · rw [hY, hz, max_self]

/-- **Corollary 1(ii), third clause.** A larger balance in the binding token
moves the leftover to the other token. -/
theorem balance_above_surplus_reverses_token1 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hxd : yw - s ^ 2 * xw < s ^ 2 * xd) :
    dustY (xw + xd) yw gx gy = 0 ∧ 0 < dustX (xw + xd) yw gx gy := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw + xd) (yh := yw) hs hgx hg
  have hs2 : 0 < s ^ 2 := by positivity
  have hpos : 0 < s ^ 2 * (xw + xd) - yw := by nlinarith
  refine ⟨by rw [hY, max_eq_right (by linarith)], ?_⟩
  rw [max_eq_left hpos.le] at hX
  by_contra hcon
  have : s ^ 2 * dustX (xw + xd) yw gx gy ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs2.le (not_lt.mp hcon)
  linarith

theorem balance_above_surplus_reverses_token0 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (hyd : s ^ 2 * xw - yw < yd) :
    dustX xw (yw + yd) gx gy = 0 ∧ 0 < dustY xw (yw + yd) gx gy := by
  obtain ⟨hY, hX⟩ := dust_centred (xh := xw) (yh := yw + yd) hs hgx hg
  have hpos : 0 < yw + yd - s ^ 2 * xw := by linarith
  refine ⟨dustX_eq_zero_of_value hs ?_, ?_⟩
  · rw [hX, max_eq_right (by linarith)]
  · rw [hY, max_eq_left hpos.le]; exact hpos

/-- **Corollary 2, in units of the surplus.** With a surplus `m` of token 1
and no standing balance, a swap that exchanges value `Q = m (1 + ε) / 2` of
token 1 for the same value of token 0 at the price `s` leaves `m |ε|`: in
token 1 if `ε < 0`, in token 0, the token the swap bought, if `ε > 0`. The
identity is algebraic and holds for every `ε`; the swap is one the position
can make only under `swap_feasible_token1`. -/
theorem swapcorrected_surplus_token1 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (ε : ℝ) :
    dustY (xw + (yw - s ^ 2 * xw) * (1 + ε) / 2 / s ^ 2)
          (yw - (yw - s ^ 2 * xw) * (1 + ε) / 2) gx gy
        = max (-((yw - s ^ 2 * xw) * ε)) 0 ∧
      s ^ 2 * dustX (xw + (yw - s ^ 2 * xw) * (1 + ε) / 2 / s ^ 2)
          (yw - (yw - s ^ 2 * xw) * (1 + ε) / 2) gx gy
        = max ((yw - s ^ 2 * xw) * ε) 0 := by
  have hs2 : s ^ 2 ≠ 0 := by positivity
  obtain ⟨hY, hX⟩ := dust_centred
    (xh := xw + (yw - s ^ 2 * xw) * (1 + ε) / 2 / s ^ 2)
    (yh := yw - (yw - s ^ 2 * xw) * (1 + ε) / 2) hs hgx hg
  have e1 : yw - (yw - s ^ 2 * xw) * (1 + ε) / 2
      - s ^ 2 * (xw + (yw - s ^ 2 * xw) * (1 + ε) / 2 / s ^ 2)
      = -((yw - s ^ 2 * xw) * ε) := by
    field_simp
    ring
  have e2 : s ^ 2 * (xw + (yw - s ^ 2 * xw) * (1 + ε) / 2 / s ^ 2)
      - (yw - (yw - s ^ 2 * xw) * (1 + ε) / 2)
      = (yw - s ^ 2 * xw) * ε := by
    field_simp
    ring
  rw [hY, hX, e1, e2]
  exact ⟨rfl, rfl⟩

/-- The mirror case: a surplus `m` of token 0, the swap selling token 0. -/
theorem swapcorrected_surplus_token0 (hs : 0 < s) (hgx : 0 < gx)
    (hg : gy = s ^ 2 * gx) (ε : ℝ) :
    dustY (xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2)
          (yw + (s ^ 2 * xw - yw) * (1 + ε) / 2) gx gy
        = max ((s ^ 2 * xw - yw) * ε) 0 ∧
      s ^ 2 * dustX (xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2)
          (yw + (s ^ 2 * xw - yw) * (1 + ε) / 2) gx gy
        = max (-((s ^ 2 * xw - yw) * ε)) 0 := by
  have hs2 : s ^ 2 ≠ 0 := by positivity
  obtain ⟨hY, hX⟩ := dust_centred
    (xh := xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2)
    (yh := yw + (s ^ 2 * xw - yw) * (1 + ε) / 2) hs hgx hg
  have e1 : yw + (s ^ 2 * xw - yw) * (1 + ε) / 2
      - s ^ 2 * (xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2)
      = (s ^ 2 * xw - yw) * ε := by
    field_simp
    ring
  have e2 : s ^ 2 * (xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2)
      - (yw + (s ^ 2 * xw - yw) * (1 + ε) / 2)
      = -((s ^ 2 * xw - yw) * ε) := by
    field_simp
    ring
  rw [hY, hX, e1, e2]
  exact ⟨rfl, rfl⟩

/-- **Feasibility of the swap of Corollary 2.** With `V = s² x_w + y_w` the
withdrawn value and `m` the surplus of token 1, the swap leaves a non-negative
amount of token 1 for the mint exactly when `m ε ≤ V`. In the corollary's
terms, `m = α(ℓ) V`, this is `α(ℓ) ε ≤ 1`: the swap cannot sell more of the
surplus token than was withdrawn. The paper states the corollary for `-1 < ε ≤ 1/α(ℓ)`. -/
theorem swap_feasible_token1 :
    0 ≤ yw - (yw - s ^ 2 * xw) * (1 + ε) / 2
      ↔ (yw - s ^ 2 * xw) * ε ≤ s ^ 2 * xw + yw := by
  constructor <;> intro h <;> nlinarith

theorem swap_feasible_token0 (hs : 0 < s) :
    0 ≤ xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2
      ↔ (s ^ 2 * xw - yw) * ε ≤ s ^ 2 * xw + yw := by
  have hs2 : 0 < s ^ 2 := by positivity
  have e : xw - (s ^ 2 * xw - yw) * (1 + ε) / 2 / s ^ 2
      = (s ^ 2 * xw + yw - (s ^ 2 * xw - yw) * ε) / (2 * s ^ 2) := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity : (0:ℝ) < 2 * s ^ 2), zero_mul]
  constructor <;> intro h <;> linarith

/-! ## Corollary 1 as stated: an old range centred on `s₀` -/

section Corollaries

variable {ε : ℝ}

/-- **Corollary 1(i), upward move inside the old range.** With no standing
balance and no swap, the leftover is in token 1 and is the fraction `α` of the
withdrawn value. -/
theorem swapfree_rule_up (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hup : s0 ^ 2 ≤ s ^ 2) (hL : 0 ≤ L)
    (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) :
    dustX (L * ax s sa sb) (L * ay s sa sb) gx gy = 0 ∧
      dustY (L * ax s sa sb) (L * ay s sa sb) gx gy
        = alpha s s0 sb * (s ^ 2 * (L * ax s sa sb) + L * ay s sa sb) := by
  have hs : 0 < s := h0.trans h1
  have hb : 0 < sb := hs.trans h2
  have hm : 0 ≤ L * ay s sa sb - s ^ 2 * (L * ax s sa sb) := by
    rw [withdrawn_mismatch h0 h1 h2 hc]
    exact div_nonneg (mul_nonneg hL (sub_nonneg.mpr hup)) hb.le
  obtain ⟨hX, hY⟩ := swapfree_surplus_token1 hs hgx hg hm
  exact ⟨hX, by rw [hY, mismatch_eq_alpha_value_up h0 h1 h2 hc hup]⟩

/-- **Corollary 1(i), downward move inside the old range.** The leftover is in
token 0, worth the fraction `α` of the withdrawn value. -/
theorem swapfree_rule_down (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hdown : s ^ 2 ≤ s0 ^ 2) (hL : 0 ≤ L)
    (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) :
    dustY (L * ax s sa sb) (L * ay s sa sb) gx gy = 0 ∧
      s ^ 2 * dustX (L * ax s sa sb) (L * ay s sa sb) gx gy
        = alpha s s0 sb * (s ^ 2 * (L * ax s sa sb) + L * ay s sa sb) := by
  have hs : 0 < s := h0.trans h1
  have hb : 0 < sb := hs.trans h2
  have hm : 0 ≤ s ^ 2 * (L * ax s sa sb) - L * ay s sa sb := by
    have := withdrawn_mismatch (L := L) h0 h1 h2 hc
    have hnn : L * (s ^ 2 - s0 ^ 2) / sb ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hL (sub_nonpos.mpr hdown)) hb.le
    linarith
  obtain ⟨hY, hX⟩ := swapfree_surplus_token0 hs hgx hg hm
  exact ⟨hY, by rw [hX, mismatch_eq_alpha_value_down h0 h1 h2 hc hdown]⟩

/-- **Corollary 1(i), at or beyond the upper bound.** The withdrawn position
holds token 1 only and the whole of it is left. -/
theorem swapfree_rule_exit_above (hab : sa < sb) (h0 : sa < s) (hsb : sb ≤ s)
    (hs : 0 < s) (hL : 0 ≤ L) (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) :
    dustX (L * ax s sa sb) (L * ay s sa sb) gx gy = 0 ∧
      dustY (L * ax s sa sb) (L * ay s sa sb) gx gy
        = s ^ 2 * (L * ax s sa sb) + L * ay s sa sb := by
  have hax : ax s sa sb = 0 := ax_of_ge h0 hsb
  have hm : 0 ≤ L * ay s sa sb - s ^ 2 * (L * ax s sa sb) := by
    rw [hax, ay_of_ge h0 hsb]
    have := mul_nonneg hL (sub_nonneg.mpr hab.le)
    linarith
  obtain ⟨hX, hY⟩ := swapfree_surplus_token1 hs hgx hg hm
  exact ⟨hX, by rw [hY, hax]; ring⟩

/-- **Corollary 1(i), at or beyond the lower bound.** The withdrawn position
holds token 0 only and the whole of it is left. -/
theorem swapfree_rule_exit_below (h0 : 0 < sa) (hab : sa < sb) (hsa : s ≤ sa)
    (hs : 0 < s) (hL : 0 ≤ L) (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) :
    dustY (L * ax s sa sb) (L * ay s sa sb) gx gy = 0 ∧
      s ^ 2 * dustX (L * ax s sa sb) (L * ay s sa sb) gx gy
        = s ^ 2 * (L * ax s sa sb) + L * ay s sa sb := by
  have hay : ay s sa sb = 0 := ay_of_le hsa
  have hs2 : 0 < s ^ 2 := by positivity
  have hm : 0 ≤ s ^ 2 * (L * ax s sa sb) - L * ay s sa sb := by
    rw [hay, ax_of_le hsa]
    have h1 : 0 ≤ 1 / sa - 1 / sb :=
      sub_nonneg.mpr (one_div_le_one_div_of_le h0 hab.le)
    have := mul_nonneg hs2.le (mul_nonneg hL h1)
    linarith
  obtain ⟨hY, hX⟩ := swapfree_surplus_token0 hs hgx hg hm
  exact ⟨hY, by rw [hX, hay]; ring⟩

/-- **Corollary 1(ii), upward move.** A standing balance worth less than
`α V` leaves the leftover in token 1, whatever its composition. -/
theorem swapfree_rule_up_with_balance (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hup : s0 ^ 2 ≤ s ^ 2)
    (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) (hyd : 0 ≤ yd)
    (hD : s ^ 2 * xd + yd
      < alpha s s0 sb * (s ^ 2 * (L * ax s sa sb) + L * ay s sa sb)) :
    dustX (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy = 0 ∧
      0 < dustY (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy := by
  have hs : 0 < s := h0.trans h1
  rw [← mismatch_eq_alpha_value_up h0 h1 h2 hc hup] at hD
  exact balance_below_surplus_keeps_token1 hs hgx hg hyd hD

/-- **Corollary 1(ii), downward move.** -/
theorem swapfree_rule_down_with_balance (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hdown : s ^ 2 ≤ s0 ^ 2)
    (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) (hxd : 0 ≤ xd)
    (hD : s ^ 2 * xd + yd
      < alpha s s0 sb * (s ^ 2 * (L * ax s sa sb) + L * ay s sa sb)) :
    dustY (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy = 0 ∧
      0 < dustX (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy := by
  have hs : 0 < s := h0.trans h1
  rw [← mismatch_eq_alpha_value_down h0 h1 h2 hc hdown] at hD
  exact balance_below_surplus_keeps_token0 hs hgx hg hxd hD

/-- **Corollary 2, upward move.** With no standing balance and a swap of value
`Q = α V (1 + ε) / 2` from token 1 into token 0, the leftover is worth
`α V |ε|`, in token 1 if `ε ≤ 0` and in token 0 if `ε ≥ 0`. -/
theorem swapcorrected_rule_up (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hup : s0 ^ 2 ≤ s ^ 2)
    (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) (ε Q V : ℝ)
    (hV : V = s ^ 2 * (L * ax s sa sb) + L * ay s sa sb)
    (hQ : Q = alpha s s0 sb * V * (1 + ε) / 2) :
    dustY (L * ax s sa sb + Q / s ^ 2) (L * ay s sa sb - Q) gx gy
        = max (-(alpha s s0 sb * V * ε)) 0 ∧
      s ^ 2 * dustX (L * ax s sa sb + Q / s ^ 2) (L * ay s sa sb - Q) gx gy
        = max (alpha s s0 sb * V * ε) 0 := by
  have hs : 0 < s := h0.trans h1
  have hm := mismatch_eq_alpha_value_up (L := L) h0 h1 h2 hc hup
  have key := swapcorrected_surplus_token1 (xw := L * ax s sa sb)
    (yw := L * ay s sa sb) hs hgx hg ε
  rw [hm, ← hV, ← hQ] at key
  exact key

/-- **Corollary 2, downward move.** The swap runs from token 0 into token 1,
and the leftover is in token 0 if `ε ≤ 0` and in token 1 if `ε ≥ 0`. -/
theorem swapcorrected_rule_down (h0 : 0 < sa) (h1 : sa < s) (h2 : s < sb)
    (hc : sa * sb = s0 ^ 2) (hdown : s ^ 2 ≤ s0 ^ 2)
    (hgx : 0 < gx) (hg : gy = s ^ 2 * gx) (ε Q V : ℝ)
    (hV : V = s ^ 2 * (L * ax s sa sb) + L * ay s sa sb)
    (hQ : Q = alpha s s0 sb * V * (1 + ε) / 2) :
    dustY (L * ax s sa sb - Q / s ^ 2) (L * ay s sa sb + Q) gx gy
        = max (alpha s s0 sb * V * ε) 0 ∧
      s ^ 2 * dustX (L * ax s sa sb - Q / s ^ 2) (L * ay s sa sb + Q) gx gy
        = max (-(alpha s s0 sb * V * ε)) 0 := by
  have hs : 0 < s := h0.trans h1
  have hm := mismatch_eq_alpha_value_down (L := L) h0 h1 h2 hc hdown
  have key := swapcorrected_surplus_token0 (xw := L * ax s sa sb)
    (yw := L * ay s sa sb) hs hgx hg ε
  rw [hm, ← hV, ← hQ] at key
  exact key

/-- The leftover of Corollary 2 is worth `α V |ε|` on whichever token it
falls. -/
theorem swapcorrected_leftover_value (m ε : ℝ) (hm : 0 ≤ m) :
    max (-(m * ε)) 0 + max (m * ε) 0 = m * |ε| := by
  rcases le_total 0 ε with h | h
  · rw [max_eq_right (by nlinarith), max_eq_left (by nlinarith), abs_of_nonneg h]
    ring
  · rw [max_eq_left (by nlinarith), max_eq_right (by nlinarith), abs_of_nonpos h]
    ring

end Corollaries

end MasterEquation
