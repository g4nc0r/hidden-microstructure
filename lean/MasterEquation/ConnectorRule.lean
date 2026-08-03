/-
Proposition 1 (Connector Rule under V3 mechanics), §5.1, proved in
Appendix B.

Appendix B's argument has two steps. The first is the per-rebalance binding
side, which Theorem 1 settles exactly and which is formalised here in full.
The second is a population-level statement about a Spearman rank correlation
under a reduced-form displacement decomposition; what is formalised of it is
the deterministic implication, namely that the per-rebalance sign rule forces
a sign-keyed sample covariance between signed displacement and signed
connector-side dust. The reduced-form decomposition itself, and the
variance-share magnitude heuristic, are not formalised; see the README.
-/
import MasterEquation.MasterJump

set_option linter.style.header false

namespace MasterEquation

open Finset

variable {s sa sb gx gy L xd yd : ℝ}

/-! ## Per-rebalance binding side (Appendix B, first subsection) -/

/-- **Appendix B, eq. (B.1).** Token 1 binds, and so token 0 leaks, exactly
when the supply ratio exceeds the required ratio. -/
theorem token1_binds_iff {xh yh : ℝ} (hgx : 0 < gx) (hgy : 0 < gy) :
    dustY xh yh gx gy = 0 ↔ yh * gx ≤ xh * gy :=
  dustY_eq_zero_iff hgx hgy

/-- Dust appears on the slack side only: when token 1 binds strictly, token 0
carries the whole leftover. -/
theorem token0_leaks {xh yh : ℝ} (hgx : 0 < gx) (hgy : 0 < gy) (hx : 0 ≤ xh)
    (hy : 0 ≤ yh) (h : yh * gx < xh * gy) :
    dustY xh yh gx gy = 0 ∧ 0 < dustX xh yh gx gy := by
  rcases exactly_one_dust_zero hgx hgy hx hy (ne_of_gt h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd ((dustX_eq_zero_iff hgx hgy).mp h1) (not_le.mpr h)
  · exact ⟨h2, h1⟩

/-! ## The boundary-trigger sign rule

The reduction of the binding condition to a sign condition on the normalised
displacement is exact at the boundary trigger of assumption (A2), where the
withdrawn position is single-sided: an exit above the old range withdraws
token 1 only, an exit below withdraws token 0 only. -/

/-- **Upward exit.** When the price has left the old range from above, the
withdrawal is single-sided in token 1, token 0 binds, and token 1 leaks. -/
theorem exit_above_leaks_token1 (hgx : 0 < gx) (hgy : 0 < gy)
    (hxd : 0 ≤ xd) (hyd : 0 ≤ yd) (hL : 0 ≤ L) (hab : sa < sb) (h0 : sa < s)
    (hs : sb ≤ s)
    (hsupply : xd * gy < (L * ay s sa sb + yd) * gx) :
    dustX (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy = 0 ∧
      0 < dustY (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy := by
  have hax : ax s sa sb = 0 := ax_of_ge h0 hs
  have hay : ay s sa sb = sb - sa := ay_of_ge h0 hs
  have hxh : L * ax s sa sb + xd = xd := by rw [hax]; ring
  have hyh : 0 ≤ L * ay s sa sb + yd := by
    rw [hay]; have := mul_nonneg hL (sub_nonneg.mpr hab.le); linarith
  rw [hxh]
  rcases exactly_one_dust_zero hgx hgy hxd hyh (ne_of_lt hsupply) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd ((dustY_eq_zero_iff hgx hgy).mp h2) (not_le.mpr hsupply)

/-- **Downward exit.** Symmetrically, an exit below the old range withdraws
token 0 only, token 1 binds, and token 0 leaks. -/
theorem exit_below_leaks_token0 (hgx : 0 < gx) (hgy : 0 < gy)
    (hxd : 0 ≤ xd) (hyd : 0 ≤ yd) (hL : 0 ≤ L) (h0 : 0 < sa) (hab : sa < sb)
    (hs : s ≤ sa)
    (hsupply : yd * gx < (L * ax s sa sb + xd) * gy) :
    dustY (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy = 0 ∧
      0 < dustX (L * ax s sa sb + xd) (L * ay s sa sb + yd) gx gy := by
  have hay : ay s sa sb = 0 := ay_of_le hs
  have hax : ax s sa sb = 1 / sa - 1 / sb := ax_of_le hs
  have hyh : L * ay s sa sb + yd = yd := by rw [hay]; ring
  have hxh : 0 ≤ L * ax s sa sb + xd := by
    rw [hax]
    have : 0 ≤ 1 / sa - 1 / sb :=
      sub_nonneg.mpr (one_div_le_one_div_of_le h0 hab.le)
    have := mul_nonneg hL this
    linarith
  rw [hyh]
  exact token0_leaks hgx hgy hxh hyd hsupply

/-! ## Sign keyed to the pool position of the connector -/

/-- Signed connector-side dust when the connector occupies the `T0` position:
the dust credited to the non-connector side minus the dust credited to the
connector's side, so that it is positive when the non-connector side leaks. -/
def signedDustT0 (dx dy : ℝ) : ℝ := dy - dx

/-- The same quantity when the connector occupies the `T1` position. -/
def signedDustT1 (dx dy : ℝ) : ℝ := dx - dy

/-- **Proposition 1, sign at the `T0` position.** With the connector at `T0`,
an upward displacement leaves the non-connector side leaking, so signed
connector-side dust is positive. -/
theorem signedDustT0_pos_of_token1_leaks {dx dy : ℝ} (hx : dx = 0)
    (hy : 0 < dy) : 0 < signedDustT0 dx dy := by
  unfold signedDustT0; rw [hx]; linarith

/-- A downward displacement leaves the connector's side leaking, so signed
connector-side dust is negative. -/
theorem signedDustT0_neg_of_token0_leaks {dx dy : ℝ} (hy : dy = 0)
    (hx : 0 < dx) : signedDustT0 dx dy < 0 := by
  unfold signedDustT0; rw [hy]; linarith

/-- **Proposition 1, sign at the `T1` position.** Moving the connector to the
`T1` position negates signed connector-side dust and hence flips the sign of
the correlation throughout. This is the prediction the prior paper's
`T1`-only sample could not test. -/
theorem signedDustT1_eq_neg (dx dy : ℝ) :
    signedDustT1 dx dy = -signedDustT0 dx dy := by
  unfold signedDustT0 signedDustT1; ring

/-! ## Population-level concordance under the boundary trigger

Under assumption (A2) the normalised displacement takes the two values
`± w / 2`, so the per-rebalance sign rule alone forces every pair of events
to be concordant. The sum below is `2 n²` times the sample covariance of
signed displacement against signed connector-side dust. -/

/-- **Proposition 1, population step.** Across a sample of rebalances whose
displacements take the two boundary-trigger values `±c` and whose signed
connector-side dust carries the sign of the displacement, the sample
covariance of the two is non-negative. -/
theorem concordance_nonneg {ι : Type*} (t : Finset ι) (δ d : ι → ℝ) {c : ℝ}
    (hc : 0 < c) (htrigger : ∀ i ∈ t, δ i = c ∨ δ i = -c)
    (hsign : ∀ i ∈ t, (0 < δ i → 0 < d i) ∧ (δ i < 0 → d i < 0)) :
    0 ≤ ∑ i ∈ t, ∑ j ∈ t, (δ i - δ j) * (d i - d j) := by
  refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
  rcases htrigger i hi with hi' | hi' <;> rcases htrigger j hj with hj' | hj'
  · rw [hi', hj']; simp
  · have hdi : 0 < d i := (hsign i hi).1 (by rw [hi']; linarith)
    have hdj : d j < 0 := (hsign j hj).2 (by rw [hj']; linarith)
    rw [hi', hj']
    have : 0 < c - -c := by linarith
    nlinarith
  · have hdi : d i < 0 := (hsign i hi).2 (by rw [hi']; linarith)
    have hdj : 0 < d j := (hsign j hj).1 (by rw [hj']; linarith)
    rw [hi', hj']
    nlinarith
  · rw [hi', hj']; simp

/-- The `T1`-position case: negating the dust column negates the sum, so the
sample covariance is non-positive. This is the sign-by-position prediction
the prior paper's `T1`-only sample could not test. -/
theorem concordance_nonpos_of_neg {ι : Type*} (t : Finset ι) (δ d : ι → ℝ)
    {c : ℝ} (hc : 0 < c) (htrigger : ∀ i ∈ t, δ i = c ∨ δ i = -c)
    (hsign : ∀ i ∈ t, (0 < δ i → 0 < d i) ∧ (δ i < 0 → d i < 0)) :
    ∑ i ∈ t, ∑ j ∈ t, (δ i - δ j) * (-d i - -d j) ≤ 0 := by
  have key := concordance_nonneg t δ d hc htrigger hsign
  have hneg : ∑ i ∈ t, ∑ j ∈ t, (δ i - δ j) * (-d i - -d j)
      = -∑ i ∈ t, ∑ j ∈ t, (δ i - δ j) * (d i - d j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hneg]
  linarith

end MasterEquation
