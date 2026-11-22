/-
The direction-resolved hub-spoke kernel of the section "A model of the ledger
and propagation of chaos", with the deterministic facts its proofs consume.

One hub token is shared by the pools, pool `k` pairing it with its own spoke
token. `H` is the hub's ledger entry, `B` the entry of the firing pool's
spoke token, `Lw` the value of the position withdrawn at a bound of its
range, `η ∈ {+1, -1}` the direction of the event (the side of the range at
which it fires: `+1` at the upper bound, where the withdrawn position holds
the spoke token only and the swap buys hub token) and `ε` the execution
residual (the swap's amount over the exact amount, less one). The hub token
is at the token-0 position. The imbalance the swap is asked to remove is

  A = Lw + η (B - H),

and the kernel puts the leftover `c₀ |A| |ε|` on the hub when `η A ε > 0` and
on the spoke otherwise, setting the other entry to zero.

Contents.
* The kernel is Theorem 1 applied to the post-swap inputs
  (`kernel_eq_master_jump`), and agrees with the paper's case form
  (`hubPost_eq_ite`, `spokePost_eq_ite`).
* The `ℓ¹` identity for two states under one mark, the invariant set
  `[0, b*]` and the positivity of the imbalance on it for `κ < 1/2`.
* The side identity behind the atom of the one-spoke law: on a positive
  imbalance the spoke's entry is zero exactly when `η ε ≥ 0`.
* The slack-side leftover and its distance from the leading-order form.
* The contraction of the full chain for one mark, pathwise and summed over
  the firing pool.
* The one-register property: under the affine form of the kernel, a change
  made to one entry is, after any sequence of events, a change in exactly one
  entry, with a weight that depends on the events alone.
* The size identities of the proposition on the drift of position size.

As in the paper, leading-order-in-`w` expressions are taken as definitions:
the position withdrawn at a bound is worth `Lw`, the new range takes the two
tokens in equal amounts in the kernel's units, and the swap enters as the
exact amount times `1 + ε`. Nothing here is a statement about laws of the
chain: the stationary law, the rate `1/N` and the propositions on unequal
spokes and a common direction are not formalised. See the README.
-/
import MasterEquation.MasterJump

set_option linter.style.header false

namespace MasterEquation

namespace Kernel

variable {Lw c0 η H B H₁ B₁ H₂ B₂ ε sh2 g κ b : ℝ}

/-! ## Imbalance and post-swap inputs -/

/-- The imbalance the swap is asked to remove. -/
def imbalance (Lw η H B : ℝ) : ℝ := Lw + η * (B - H)

/-- Post-swap hub-token (token 0) input of the mint. -/
noncomputable def xhat (Lw η H B ε : ℝ) : ℝ :=
  (H + Lw + B) / 2 + η * imbalance Lw η H B * ε / 2

/-- Post-swap spoke-token (token 1) input, with a slope `sh2` on the residual
term. The paper's kernel is the case `sh2 = 1`, both inputs in one unit. -/
noncomputable def yhat (Lw η H B ε sh2 : ℝ) : ℝ :=
  (H + Lw + B) / 2 - sh2 * (η * imbalance Lw η H B * ε) / 2

/-- At the upper bound the mint has `H` of the hub token and `Lw + B` of the
spoke token, and the swap buys hub token worth `A (1 + ε) / 2`. -/
theorem inputs_up :
    xhat Lw 1 H B ε = H + imbalance Lw 1 H B * (1 + ε) / 2 ∧
      yhat Lw 1 H B ε 1 = Lw + B - imbalance Lw 1 H B * (1 + ε) / 2 := by
  unfold xhat yhat imbalance
  constructor <;> ring

/-- At the lower bound the mint has `Lw + H` of the hub token and `B` of the
spoke token, and the swap sells hub token worth `A (1 + ε) / 2`. -/
theorem inputs_down :
    xhat Lw (-1) H B ε = Lw + H - imbalance Lw (-1) H B * (1 + ε) / 2 ∧
      yhat Lw (-1) H B ε 1 = B + imbalance Lw (-1) H B * (1 + ε) / 2 := by
  unfold xhat yhat imbalance
  constructor <;> ring

/-- The routing conservation collapses the swap noise to one residual, so the
imbalance of the inputs is one term. -/
theorem hat_diff : xhat Lw η H B ε - yhat Lw η H B ε sh2
    = (1 + sh2) / 2 * (η * imbalance Lw η H B * ε) := by
  unfold xhat yhat; ring

/-! ## The kernel -/

/-- Post-event hub entry. -/
noncomputable def hubPost (c0 Lw η H B ε : ℝ) : ℝ :=
  max (c0 * (η * imbalance Lw η H B * ε)) 0

/-- Post-event spoke entry. -/
noncomputable def spokePost (c0 Lw η H B ε : ℝ) : ℝ :=
  max (-(c0 * (η * imbalance Lw η H B * ε))) 0

/-- **The kernel from Theorem 1.** With the new range taking the two tokens in
equal amounts, the kernel is Theorem 1's jump applied to the post-swap inputs.
The hub token is token 0, and `c₀ = (1 + sh2) / 2`, which is one in the paper's
case `sh2 = 1`. -/
theorem kernel_eq_master_jump (hg : 0 < g) :
    dustX (xhat Lw η H B ε) (yhat Lw η H B ε sh2) g g
        = hubPost ((1 + sh2) / 2) Lw η H B ε ∧
      dustY (xhat Lw η H B ε) (yhat Lw η H B ε sh2) g g
        = spokePost ((1 + sh2) / 2) Lw η H B ε := by
  obtain ⟨hY, hX⟩ := dust_of_proportional_requirements
    (xh := xhat Lw η H B ε) (yh := yhat Lw η H B ε sh2) (gx := g) (gy := g)
    (r := 1) hg one_pos (one_mul g).symm
  rw [one_mul] at hX
  rw [one_mul] at hY
  rw [one_mul, hat_diff] at hX
  rw [show yhat Lw η H B ε sh2 - xhat Lw η H B ε
      = -(xhat Lw η H B ε - yhat Lw η H B ε sh2) by ring, hat_diff] at hY
  exact ⟨hX, hY⟩

private lemma abs_dir (hη : η = 1 ∨ η = -1) : |η| = 1 := by
  rcases hη with h | h <;> rw [h] <;> simp

private lemma abs_dir_mul (hη : η = 1 ∨ η = -1) (a e : ℝ) : |η * a * e| = |a| * |e| := by
  rw [abs_mul, abs_mul, abs_dir hη, one_mul]

/-- **The paper's case form, hub entry.** -/
theorem hubPost_eq_ite (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) :
    hubPost c0 Lw η H B ε
      = if 0 < η * imbalance Lw η H B * ε
          then c0 * |imbalance Lw η H B| * |ε| else 0 := by
  unfold hubPost
  split_ifs with h
  · have habs : |imbalance Lw η H B| * |ε| = η * imbalance Lw η H B * ε := by
      rw [← abs_dir_mul hη, abs_of_pos h]
    rw [max_eq_left (mul_nonneg hc0 h.le),
      show c0 * |imbalance Lw η H B| * |ε| = c0 * (|imbalance Lw η H B| * |ε|) by ring, habs]
  · exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc0 (not_lt.mp h))

/-- **The paper's case form, spoke entry.** -/
theorem spokePost_eq_ite (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) :
    spokePost c0 Lw η H B ε
      = if 0 < η * imbalance Lw η H B * ε
          then 0 else c0 * |imbalance Lw η H B| * |ε| := by
  unfold spokePost
  split_ifs with h
  · exact max_eq_right (by nlinarith [mul_nonneg hc0 h.le])
  · have hle := not_lt.mp h
    have habs : |imbalance Lw η H B| * |ε| = -(η * imbalance Lw η H B * ε) := by
      rw [← abs_dir_mul hη, abs_of_nonpos hle]
    rw [max_eq_left (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hc0 hle]),
      show c0 * |imbalance Lw η H B| * |ε| = c0 * (|imbalance Lw η H B| * |ε|) by ring, habs]
    ring

theorem hubPost_nonneg : 0 ≤ hubPost c0 Lw η H B ε := le_max_right _ _

theorem spokePost_nonneg : 0 ≤ spokePost c0 Lw η H B ε := le_max_right _ _

/-- Exactly one entry carries the leftover. -/
theorem post_mul_eq_zero :
    hubPost c0 Lw η H B ε * spokePost c0 Lw η H B ε = 0 := by
  unfold hubPost spokePost
  rcases le_total (c0 * (η * imbalance Lw η H B * ε)) 0 with hc | hc
  · rw [max_eq_right hc, zero_mul]
  · rw [max_eq_right (by linarith : -(c0 * (η * imbalance Lw η H B * ε)) ≤ 0), mul_zero]

/-- The leftover is `c₀ |A| |ε|`. -/
theorem leftover_magnitude (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) :
    hubPost c0 Lw η H B ε + spokePost c0 Lw η H B ε
      = c0 * |imbalance Lw η H B| * |ε| := by
  rw [hubPost_eq_ite hc0 hη, spokePost_eq_ite hc0 hη]
  split_ifs <;> ring

/-! ## The `ℓ¹` identity -/

/-- `|u⁺ - v⁺| + |u⁻ - v⁻| = |u - v|`. -/
theorem abs_pos_part_sub_add_abs_neg_part_sub (u v : ℝ) :
    |max u 0 - max v 0| + |max (-u) 0 - max (-v) 0| = |u - v| := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [max_eq_left hu, max_eq_left hv, max_eq_right (by linarith),
      max_eq_right (by linarith), sub_self, abs_zero, add_zero]
  · rw [max_eq_left hu, max_eq_right hv, max_eq_right (by linarith),
      max_eq_left (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonneg (by linarith)]
    ring
  · rw [max_eq_right hu, max_eq_left hv, max_eq_left (by linarith),
      max_eq_right (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_right hu, max_eq_right hv, max_eq_left (by linarith),
      max_eq_left (by linarith), sub_self, abs_zero, zero_add,
      show -u - -v = -(u - v) by ring, abs_neg]

/-- **The `ℓ¹` identity.** Two states under one mark: the distance after the
event is `c₀ |ε|` times the difference of the imbalances, also when the two
copies leave their leftover on different tokens. -/
theorem l1_identity (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) :
    |hubPost c0 Lw η H₁ B₁ ε - hubPost c0 Lw η H₂ B₂ ε|
        + |spokePost c0 Lw η H₁ B₁ ε - spokePost c0 Lw η H₂ B₂ ε|
      = c0 * |ε| * |imbalance Lw η H₁ B₁ - imbalance Lw η H₂ B₂| := by
  unfold hubPost spokePost
  rw [abs_pos_part_sub_add_abs_neg_part_sub,
    show c0 * (η * imbalance Lw η H₁ B₁ * ε) - c0 * (η * imbalance Lw η H₂ B₂ * ε)
      = c0 * (η * (imbalance Lw η H₁ B₁ - imbalance Lw η H₂ B₂) * ε) by ring,
    abs_mul, abs_dir_mul hη, abs_of_nonneg hc0]
  ring

/-- The difference of two imbalances is at most the distance of the states. -/
theorem abs_imbalance_sub_le (hη : η = 1 ∨ η = -1) :
    |imbalance Lw η H₁ B₁ - imbalance Lw η H₂ B₂| ≤ |H₁ - H₂| + |B₁ - B₂| := by
  unfold imbalance
  rw [show Lw + η * (B₁ - H₁) - (Lw + η * (B₂ - H₂)) = η * ((B₁ - B₂) - (H₁ - H₂)) by ring,
    abs_mul, abs_dir hη, one_mul]
  calc |B₁ - B₂ - (H₁ - H₂)| ≤ |B₁ - B₂| + |H₁ - H₂| := abs_sub _ _
    _ = |H₁ - H₂| + |B₁ - B₂| := add_comm _ _

/-- **The Lipschitz property that follows.** -/
theorem l1_contraction (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) :
    |hubPost c0 Lw η H₁ B₁ ε - hubPost c0 Lw η H₂ B₂ ε|
        + |spokePost c0 Lw η H₁ B₁ ε - spokePost c0 Lw η H₂ B₂ ε|
      ≤ c0 * |ε| * (|H₁ - H₂| + |B₁ - B₂|) := by
  rw [l1_identity hc0 hη]
  exact mul_le_mul_of_nonneg_left (abs_imbalance_sub_le hη)
    (mul_nonneg hc0 (abs_nonneg _))

/-! ## The invariant set -/

/-- The bound `b* = κ Lw / (1 - κ)` on the balances. -/
noncomputable def bstar (κ Lw : ℝ) : ℝ := κ * Lw / (1 - κ)

/-- `b*` is the fixed point of `c ↦ κ (Lw + c)`. -/
theorem bstar_fixed (hκ : κ < 1) : κ * (Lw + bstar κ Lw) = bstar κ Lw := by
  have h1 : (1 - κ) ≠ 0 := by linarith
  unfold bstar
  field_simp
  ring

theorem bstar_nonneg (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hLw : 0 ≤ Lw) : 0 ≤ bstar κ Lw :=
  div_nonneg (mul_nonneg hκ0 hLw) (by linarith)

/-- `b* < Lw` exactly because `κ < 1/2`. -/
theorem bstar_lt (hκ : κ < 1 / 2) (hLw : 0 < Lw) : bstar κ Lw < Lw := by
  unfold bstar
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- Bounds on the imbalance when both balances lie in `[0, b]`. -/
theorem imbalance_bounds (hη : η = 1 ∨ η = -1) (hH0 : 0 ≤ H) (hHb : H ≤ b)
    (hB0 : 0 ≤ B) (hBb : B ≤ b) :
    Lw - b ≤ imbalance Lw η H B ∧ imbalance Lw η H B ≤ Lw + b := by
  unfold imbalance
  rcases hη with h | h <;> rw [h] <;> constructor <;> linarith

/-- **Positive imbalance on the invariant set.** -/
theorem imbalance_pos (hη : η = 1 ∨ η = -1) (hκ : κ < 1 / 2) (hLw : 0 < Lw)
    (hH0 : 0 ≤ H) (hHb : H ≤ bstar κ Lw) (hB0 : 0 ≤ B) (hBb : B ≤ bstar κ Lw) :
    0 < imbalance Lw η H B := by
  have h1 := (imbalance_bounds (Lw := Lw) hη hH0 hHb hB0 hBb).1
  have h2 := bstar_lt hκ hLw
  linarith

/-- **The invariant set.** If both balances are at most `b*` before the event
and `c₀ |ε| ≤ κ < 1`, both are at most `b*` after it. -/
theorem post_le_bstar (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) (hκ0 : 0 ≤ κ)
    (hκ : κ < 1) (hLw : 0 ≤ Lw) (hε : c0 * |ε| ≤ κ)
    (hH0 : 0 ≤ H) (hHb : H ≤ bstar κ Lw) (hB0 : 0 ≤ B) (hBb : B ≤ bstar κ Lw) :
    hubPost c0 Lw η H B ε ≤ bstar κ Lw ∧ spokePost c0 Lw η H B ε ≤ bstar κ Lw := by
  have hb := bstar_nonneg hκ0 hκ hLw
  obtain ⟨hlo, hhi⟩ := imbalance_bounds (Lw := Lw) hη hH0 hHb hB0 hBb
  have hA : |imbalance Lw η H B| ≤ Lw + bstar κ Lw := abs_le.mpr ⟨by linarith, hhi⟩
  have hsum := leftover_magnitude (Lw := Lw) (H := H) (B := B) (ε := ε) hc0 hη
  have hbound : c0 * |imbalance Lw η H B| * |ε| ≤ bstar κ Lw := by
    rw [← bstar_fixed (Lw := Lw) hκ]
    calc c0 * |imbalance Lw η H B| * |ε| = (c0 * |ε|) * |imbalance Lw η H B| := by ring
      _ ≤ κ * (Lw + bstar κ Lw) :=
        mul_le_mul hε hA (abs_nonneg _) hκ0
  have h1 := hubPost_nonneg (c0 := c0) (Lw := Lw) (η := η) (H := H) (B := B) (ε := ε)
  have h2 := spokePost_nonneg (c0 := c0) (Lw := Lw) (η := η) (H := H) (B := B) (ε := ε)
  constructor <;> linarith

/-! ## The side identity, the affine form and the slack side -/

/-- **The side identity behind the atom.** On a positive imbalance the spoke's
entry is zero after the event exactly when `η ε ≥ 0`. -/
theorem spokePost_eq_zero_iff (hc0 : 0 < c0) (hA : 0 < imbalance Lw η H B) :
    spokePost c0 Lw η H B ε = 0 ↔ 0 ≤ η * ε := by
  unfold spokePost
  rw [max_eq_right_iff, neg_nonpos,
    show c0 * (η * imbalance Lw η H B * ε) = (c0 * imbalance Lw η H B) * (η * ε) by ring]
  exact mul_nonneg_iff_of_pos_left (mul_pos hc0 hA)

/-- The hub's entry is zero exactly when `η ε ≤ 0`. -/
theorem hubPost_eq_zero_iff (hc0 : 0 < c0) (hA : 0 < imbalance Lw η H B) :
    hubPost c0 Lw η H B ε = 0 ↔ η * ε ≤ 0 := by
  unfold hubPost
  rw [max_eq_right_iff,
    show c0 * (η * imbalance Lw η H B * ε) = (c0 * imbalance Lw η H B) * (η * ε) by ring]
  have hp := mul_pos hc0 hA
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos hp hcon]
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hp.le h

/-- **Affine form.** On a non-negative imbalance each event is an affine map
of the state with coefficients that depend on the mark only. -/
theorem hubPost_eq_affine (hA : 0 ≤ imbalance Lw η H B) :
    hubPost c0 Lw η H B ε = max (c0 * η * ε) 0 * imbalance Lw η H B := by
  unfold hubPost
  rw [max_mul_of_nonneg _ _ hA, zero_mul]
  congr 1
  ring

theorem spokePost_eq_affine (hA : 0 ≤ imbalance Lw η H B) :
    spokePost c0 Lw η H B ε = max (-(c0 * η * ε)) 0 * imbalance Lw η H B := by
  unfold spokePost
  rw [max_mul_of_nonneg _ _ hA, zero_mul]
  congr 1
  ring

/-- **The slack side.** When the leftover falls on the spoke it is
`c₀ A |ε|`. -/
theorem spokePost_slack (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1)
    (hA : 0 ≤ imbalance Lw η H B) (hs : η * ε < 0) :
    spokePost c0 Lw η H B ε = c0 * imbalance Lw η H B * |ε| := by
  have habs : |ε| = -(η * ε) := by
    rw [← abs_of_neg hs, abs_mul, abs_dir hη, one_mul]
  rw [spokePost_eq_affine hA, habs,
    max_eq_left (by nlinarith : 0 ≤ -(c0 * η * ε))]
  ring

/-- **Distance from the leading-order form.** With both balances in `[0, b]`,
the slack-side leftover differs from `c₀ Lw |ε|` by at most `c₀ |ε| b`. -/
theorem slack_side_bound (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1)
    (hA : 0 ≤ imbalance Lw η H B) (hs : η * ε < 0)
    (hH0 : 0 ≤ H) (hHb : H ≤ b) (hB0 : 0 ≤ B) (hBb : B ≤ b) :
    |spokePost c0 Lw η H B ε - c0 * Lw * (|ε|)| ≤ c0 * |ε| * b := by
  rw [spokePost_slack hc0 hη hA hs]
  unfold imbalance
  rw [show c0 * (Lw + η * (B - H)) * |ε| - c0 * Lw * |ε| = c0 * |ε| * (η * (B - H)) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hc0 (abs_nonneg _)), abs_mul, abs_dir hη, one_mul]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩)
    (mul_nonneg hc0 (abs_nonneg _))

/-! ## The full chain for one mark -/

section Chain

variable {ι : Type*} [DecidableEq ι]

/-- One event of pool `k` on the state `x`, a vector of ledger entries indexed
by registers, with the hub at register `o`. -/
noncomputable def step (c0 Lw : ℝ) (o k : ι) (η ε : ℝ) (x : ι → ℝ) : ι → ℝ :=
  Function.update
    (Function.update x o (hubPost c0 Lw η (x o) (x k) ε))
    k (spokePost c0 Lw η (x o) (x k) ε)

theorem step_hub {o k : ι} (hok : o ≠ k) (x : ι → ℝ) :
    step c0 Lw o k η ε x o = hubPost c0 Lw η (x o) (x k) ε := by
  unfold step
  rw [Function.update_of_ne hok, Function.update_self]

theorem step_spoke (o k : ι) (x : ι → ℝ) :
    step c0 Lw o k η ε x k = spokePost c0 Lw η (x o) (x k) ε := by
  unfold step
  rw [Function.update_self]

theorem step_other {o k i : ι} (hio : i ≠ o) (hik : i ≠ k) (x : ι → ℝ) :
    step c0 Lw o k η ε x i = x i := by
  unfold step
  rw [Function.update_of_ne hik, Function.update_of_ne hio]

/-- **Contraction of the full chain, for one event.** Two copies driven by the
same firing pool and mark: the `ℓ¹` distance falls by at least
`(1 - c₀ |ε|)` times the distance in the two entries the event rewrites. -/
theorem step_l1_contraction [Fintype ι] {o k : ι} (hok : o ≠ k) (hc0 : 0 ≤ c0)
    (hη : η = 1 ∨ η = -1) (x y : ι → ℝ) :
    ∑ i, |step c0 Lw o k η ε x i - step c0 Lw o k η ε y i|
      ≤ ∑ i, |x i - y i| - (1 - c0 * |ε|) * (|x o - y o| + |x k - y k|) := by
  have hdiff : ∑ i, (|step c0 Lw o k η ε x i - step c0 Lw o k η ε y i| - |x i - y i|)
      = (|step c0 Lw o k η ε x o - step c0 Lw o k η ε y o| - |x o - y o|)
        + (|step c0 Lw o k η ε x k - step c0 Lw o k η ε y k| - |x k - y k|) :=
    Fintype.sum_eq_add o k hok (by
      intro i hi
      rw [step_other hi.1 hi.2, step_other hi.1 hi.2, sub_self])
  rw [Finset.sum_sub_distrib, step_hub hok, step_hub hok, step_spoke, step_spoke] at hdiff
  have hl1 := l1_contraction (Lw := Lw) (H₁ := x o) (B₁ := x k) (H₂ := y o) (B₂ := y k)
    (ε := ε) hc0 hη
  linarith

/-- **Contraction summed over the firing pool.** For one mark with
`c₀ |ε| ≤ 1` and `N ≥ 1` spokes, the sum over the firing pool of the distances
after the event is at most `N - (1 - c₀ |ε|)` times the distance before.
Divided by `N` this is the factor `1 - (1 - c₀ |ε|) / N` for a uniformly drawn
pool; the paper's `1 - (1 - κ₁) / N` is its mean over the mark. -/
theorem step_l1_contraction_sum [Fintype ι] (o : ι) (hc0 : 0 ≤ c0)
    (hη : η = 1 ∨ η = -1) (hε : c0 * |ε| ≤ 1)
    (hN : 1 ≤ (Finset.univ.erase o).card) (x y : ι → ℝ) :
    ∑ k ∈ Finset.univ.erase o, ∑ i, |step c0 Lw o k η ε x i - step c0 Lw o k η ε y i|
      ≤ ((Finset.univ.erase o).card - (1 - c0 * |ε|)) * ∑ i, |x i - y i| := by
  have hD : ∑ i, |x i - y i|
      = |x o - y o| + ∑ k ∈ Finset.univ.erase o, |x k - y k| :=
    (Finset.add_sum_erase _ (fun i => |x i - y i|) (Finset.mem_univ o)).symm
  have hstep : ∀ k ∈ Finset.univ.erase o,
      ∑ i, |step c0 Lw o k η ε x i - step c0 Lw o k η ε y i|
        ≤ ∑ i, |x i - y i| - (1 - c0 * |ε|) * (|x o - y o| + |x k - y k|) :=
    fun k hk => step_l1_contraction (Finset.ne_of_mem_erase hk).symm hc0 hη x y
  have hsum := Finset.sum_le_sum hstep
  have hrhs : ∑ k ∈ Finset.univ.erase o,
        (∑ i, |x i - y i| - (1 - c0 * |ε|) * (|x o - y o| + |x k - y k|))
      = (Finset.univ.erase o).card * ∑ i, |x i - y i|
        - (1 - c0 * |ε|) * ((Finset.univ.erase o).card * |x o - y o|
          + ∑ k ∈ Finset.univ.erase o, |x k - y k|) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hrhs] at hsum
  have hN' : (1 : ℝ) ≤ ((Finset.univ.erase o).card : ℝ) := by exact_mod_cast hN
  refine hsum.trans ?_
  rw [hD]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hε) (sub_nonneg.mpr hN'))
    (abs_nonneg (x o - y o))]

/-! ## One register

On a non-negative imbalance each event is an affine map of the state. For that
affine map, a change made to one entry is after the event a change in exactly
one entry, and which entry and with what weight depends on the event and not on
the state. Iterated over any finite sequence of events this is the property
the proof of the rate `1/N` rests on. -/

/-- The affine form of one event: hub entry `ζ⁺ A`, spoke entry `ζ⁻ A`, with
`ζ = c₀ η ε`. -/
noncomputable def theta (Lw : ℝ) (o k : ι) (η ζ : ℝ) (x : ι → ℝ) : ι → ℝ :=
  Function.update
    (Function.update x o (max ζ 0 * imbalance Lw η (x o) (x k)))
    k (max (-ζ) 0 * imbalance Lw η (x o) (x k))

/-- On a non-negative imbalance the kernel is the affine map. -/
theorem step_eq_theta {o k : ι} (x : ι → ℝ)
    (hA : 0 ≤ imbalance Lw η (x o) (x k)) :
    step c0 Lw o k η ε x = theta Lw o k η (c0 * η * ε) x := by
  unfold step theta
  rw [hubPost_eq_affine hA, spokePost_eq_affine hA]

/-- The entry in which a change made to entry `r` sits after one event. -/
noncomputable def particleReg (o k : ι) (ζ : ℝ) (r : ι) : ι :=
  if r = o ∨ r = k then (if 0 < ζ then o else if ζ < 0 then k else r) else r

/-- The factor the change is multiplied by. -/
noncomputable def particleWt (o k : ι) (η ζ : ℝ) (r : ι) : ℝ :=
  if r = o then -(η * |ζ|) else if r = k then η * |ζ| else 1

/-- **One register, one event.** If two states differ in entry `r` only, then
after one event of the affine map they differ in entry `particleReg` only, by
`particleWt` times the original difference. -/
theorem one_register_step {ζ : ℝ} {o k : ι} (hok : o ≠ k) (x y : ι → ℝ) (r : ι)
    (hxy : ∀ i, i ≠ r → x i = y i) (i : ι) :
    theta Lw o k η ζ x i - theta Lw o k η ζ y i
      = if i = particleReg o k ζ r then particleWt o k η ζ r * (x r - y r) else 0 := by
  have hA : imbalance Lw η (x o) (x k) - imbalance Lw η (y o) (y k)
      = η * ((x k - y k) - (x o - y o)) := by unfold imbalance; ring
  have ho : theta Lw o k η ζ x o - theta Lw o k η ζ y o
      = max ζ 0 * (η * ((x k - y k) - (x o - y o))) := by
    unfold theta
    rw [Function.update_of_ne hok, Function.update_self, Function.update_of_ne hok,
      Function.update_self, ← mul_sub, hA]
  have hk : theta Lw o k η ζ x k - theta Lw o k η ζ y k
      = max (-ζ) 0 * (η * ((x k - y k) - (x o - y o))) := by
    unfold theta
    rw [Function.update_self, Function.update_self, ← mul_sub, hA]
  have hoth : ∀ j, j ≠ o → j ≠ k →
      theta Lw o k η ζ x j - theta Lw o k η ζ y j = x j - y j := by
    intro j h1 h2
    unfold theta
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h1]
  have hsign : (0 < ζ ∧ max ζ 0 = |ζ| ∧ max (-ζ) 0 = 0)
      ∨ (ζ < 0 ∧ max ζ 0 = 0 ∧ max (-ζ) 0 = |ζ|)
      ∨ (ζ = 0 ∧ max ζ 0 = 0 ∧ max (-ζ) 0 = 0) := by
    rcases lt_trichotomy 0 ζ with h | h | h
    · exact Or.inl ⟨h, by rw [max_eq_left h.le, abs_of_pos h], max_eq_right (by linarith)⟩
    · exact Or.inr (Or.inr ⟨h.symm, by rw [← h]; simp, by rw [← h]; simp⟩)
    · exact Or.inr (Or.inl ⟨h, max_eq_right h.le,
        by rw [max_eq_left (by linarith), abs_of_neg h]⟩)
  by_cases hro : r = o
  · -- the changed entry is the hub's
    have hxk : x k = y k := hxy k (by rw [hro]; exact hok.symm)
    have hwt : particleWt o k η ζ r = -(η * |ζ|) := by
      unfold particleWt; rw [if_pos hro]
    rw [hwt, hro]
    rcases hsign with ⟨hz, hp, hm⟩ | ⟨hz, hp, hm⟩ | ⟨hz, hp, hm⟩
    · have hreg : particleReg o k ζ o = o := by
        unfold particleReg; rw [if_pos (Or.inl rfl), if_pos hz]
      rw [hreg]
      by_cases hio : i = o
      · rw [if_pos hio, hio, ho, hp, hxk]; ring
      · rw [if_neg hio]
        by_cases hik : i = k
        · rw [hik, hk, hm]; ring
        · rw [hoth i hio hik, hxy i (by rw [hro]; exact hio), sub_self]
    · have hreg : particleReg o k ζ o = k := by
        unfold particleReg
        rw [if_pos (Or.inl rfl), if_neg (by linarith), if_pos hz]
      rw [hreg]
      by_cases hik : i = k
      · rw [if_pos hik, hik, hk, hm, hxk]; ring
      · rw [if_neg hik]
        by_cases hio : i = o
        · rw [hio, ho, hp]; ring
        · rw [hoth i hio hik, hxy i (by rw [hro]; exact hio), sub_self]
    · have hreg : particleReg o k ζ o = o := by
        unfold particleReg
        rw [if_pos (Or.inl rfl), if_neg (by linarith), if_neg (by linarith)]
      rw [hreg]
      by_cases hio : i = o
      · rw [if_pos hio, hio, ho, hp, hz]; simp
      · rw [if_neg hio]
        by_cases hik : i = k
        · rw [hik, hk, hm]; ring
        · rw [hoth i hio hik, hxy i (by rw [hro]; exact hio), sub_self]
  · by_cases hrk : r = k
    · -- the changed entry is the firing spoke's
      have hxo : x o = y o := hxy o (by rw [hrk]; exact hok)
      have hwt : particleWt o k η ζ r = η * |ζ| := by
        unfold particleWt; rw [if_neg hro, if_pos hrk]
      rw [hwt, hrk]
      rcases hsign with ⟨hz, hp, hm⟩ | ⟨hz, hp, hm⟩ | ⟨hz, hp, hm⟩
      · have hreg : particleReg o k ζ k = o := by
          unfold particleReg; rw [if_pos (Or.inr rfl), if_pos hz]
        rw [hreg]
        by_cases hio : i = o
        · rw [if_pos hio, hio, ho, hp, hxo]; ring
        · rw [if_neg hio]
          by_cases hik : i = k
          · rw [hik, hk, hm]; ring
          · rw [hoth i hio hik, hxy i (by rw [hrk]; exact hik), sub_self]
      · have hreg : particleReg o k ζ k = k := by
          unfold particleReg
          rw [if_pos (Or.inr rfl), if_neg (by linarith), if_pos hz]
        rw [hreg]
        by_cases hik : i = k
        · rw [if_pos hik, hik, hk, hm, hxo]; ring
        · rw [if_neg hik]
          by_cases hio : i = o
          · rw [hio, ho, hp]; ring
          · rw [hoth i hio hik, hxy i (by rw [hrk]; exact hik), sub_self]
      · have hreg : particleReg o k ζ k = k := by
          unfold particleReg
          rw [if_pos (Or.inr rfl), if_neg (by linarith), if_neg (by linarith)]
        rw [hreg]
        by_cases hik : i = k
        · rw [if_pos hik, hik, hk, hm, hz]; simp
        · rw [if_neg hik]
          by_cases hio : i = o
          · rw [hio, ho, hp]; ring
          · rw [hoth i hio hik, hxy i (by rw [hrk]; exact hik), sub_self]
    · -- the changed entry is not touched by the event
      have hxo : x o = y o := hxy o (Ne.symm hro)
      have hxk : x k = y k := hxy k (Ne.symm hrk)
      have hwt : particleWt o k η ζ r = 1 := by
        unfold particleWt; rw [if_neg hro, if_neg hrk]
      have hreg : particleReg o k ζ r = r := by
        unfold particleReg; rw [if_neg (not_or.mpr ⟨hro, hrk⟩)]
      rw [hwt, hreg, one_mul]
      by_cases hir : i = r
      · rw [if_pos hir, hir, hoth r hro hrk]
      · rw [if_neg hir]
        by_cases hio : i = o
        · rw [hio, ho, hxo, hxk]; ring
        · by_cases hik : i = k
          · rw [hik, hk, hxo, hxk]; ring
          · rw [hoth i hio hik, hxy i hir, sub_self]

/-- An event of the affine chain: the firing pool, the direction, and the mark
`ζ = c₀ η ε`. -/
structure Event (ι : Type*) where
  /-- the spoke register of the firing pool -/
  pool : ι
  /-- the direction `η` -/
  dir : ℝ
  /-- the mark `ζ = c₀ η ε` -/
  mark : ℝ

/-- The affine chain run over a finite sequence of events. -/
noncomputable def run (Lw : ℝ) (o : ι) : List (Event ι) → (ι → ℝ) → (ι → ℝ)
  | [], x => x
  | e :: es, x => run Lw o es (theta Lw o e.pool e.dir e.mark x)

/-- Where a change made to entry `r` sits after a sequence of events, and the
weight it carries. Both depend on the events and on `r` alone. -/
noncomputable def particle (o : ι) : List (Event ι) → ι → ι × ℝ
  | [], r => (r, 1)
  | e :: es, r =>
      ((particle o es (particleReg o e.pool e.mark r)).1,
        (particle o es (particleReg o e.pool e.mark r)).2
          * particleWt o e.pool e.dir e.mark r)

/-- **One register.** If two states differ in one entry only, then after any
finite sequence of events of the affine chain they differ in one entry only,
by a weight times the original difference, the entry and the weight being
functions of the events alone. -/
theorem one_register (o : ι) (ω : List (Event ι)) (hω : ∀ e ∈ ω, o ≠ e.pool) :
    ∀ (x y : ι → ℝ) (r : ι), (∀ i, i ≠ r → x i = y i) → ∀ i,
      run Lw o ω x i - run Lw o ω y i
        = if i = (particle o ω r).1 then (particle o ω r).2 * (x r - y r) else 0 := by
  induction ω with
  | nil =>
    intro x y r hxy i
    simp only [run, particle]
    split_ifs with h
    · rw [h, one_mul]
    · rw [hxy i h, sub_self]
  | cons e es ih =>
    intro x y r hxy i
    have he : o ≠ e.pool := hω e List.mem_cons_self
    have hes : ∀ e' ∈ es, o ≠ e'.pool := fun e' h => hω e' (List.mem_cons_of_mem _ h)
    have h1 := one_register_step (Lw := Lw) (η := e.dir) (ζ := e.mark) he x y r hxy
    have hagree : ∀ j, j ≠ particleReg o e.pool e.mark r →
        theta Lw o e.pool e.dir e.mark x j = theta Lw o e.pool e.dir e.mark y j := by
      intro j hj
      have := h1 j
      rw [if_neg hj] at this
      exact sub_eq_zero.mp this
    have hρ := h1 (particleReg o e.pool e.mark r)
    rw [if_pos rfl] at hρ
    have hrec := ih hes _ _ (particleReg o e.pool e.mark r) hagree i
    simp only [run, particle]
    rw [hrec, hρ]
    split_ifs <;> ring

end Chain

/-! ## Drift of the squared norm

The paper notes that for a residual law without bounded support the squared
norm still drifts towards a compact set when `c₀² E[ε²] < 1/2`. The statements
below are for the two entries an event rewrites and for one direction. -/

/-- After the event the two entries have squared norm `c₀² A² ε²`. -/
theorem sq_post (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1) :
    hubPost c0 Lw η H B ε ^ 2 + spokePost c0 Lw η H B ε ^ 2
      = c0 ^ 2 * imbalance Lw η H B ^ 2 * ε ^ 2 := by
  have hm := leftover_magnitude (Lw := Lw) (H := H) (B := B) (ε := ε) hc0 hη
  have hz := post_mul_eq_zero (c0 := c0) (Lw := Lw) (η := η) (H := H) (B := B) (ε := ε)
  have hsq : (hubPost c0 Lw η H B ε + spokePost c0 Lw η H B ε) ^ 2
      = c0 ^ 2 * imbalance Lw η H B ^ 2 * ε ^ 2 := by
    rw [hm, mul_pow, mul_pow, sq_abs, sq_abs]
  nlinarith

/-- `A² ≤ 2 (H² + B²) + 2 (Lw)²` for non-negative balances. -/
theorem imbalance_sq_le (hη : η = 1 ∨ η = -1) (hH : 0 ≤ H) (hB : 0 ≤ B) :
    imbalance Lw η H B ^ 2 ≤ 2 * (H ^ 2 + B ^ 2) + 2 * Lw ^ 2 := by
  unfold imbalance
  rcases hη with h | h <;> rw [h] <;>
    nlinarith [sq_nonneg (Lw - (B - H)), sq_nonneg (Lw + (B - H)), mul_nonneg hH hB]

/-- **Drift of the squared norm, pointwise.** -/
theorem sq_drift_pointwise (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1)
    (hH : 0 ≤ H) (hB : 0 ≤ B) :
    hubPost c0 Lw η H B ε ^ 2 + spokePost c0 Lw η H B ε ^ 2 - (H ^ 2 + B ^ 2)
      ≤ -(1 - 2 * (c0 ^ 2 * ε ^ 2)) * (H ^ 2 + B ^ 2) + 2 * (c0 ^ 2 * ε ^ 2) * Lw ^ 2 := by
  rw [sq_post hc0 hη]
  have hnn : 0 ≤ c0 ^ 2 * ε ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (imbalance_sq_le (Lw := Lw) hη hH hB) hnn]

/-- **Drift of the squared norm, in expectation over the residual.** With
`m₂ = c₀² E[ε²]`, the second moment about zero, the mean change of
`H² + B_k²` at an event of pool `k` is at most
`-(1 - 2 m₂)(H² + B_k²) + 2 m₂ (Lw)²`. -/
theorem sq_drift_integral (ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure ν] (hc0 : 0 ≤ c0) (hη : η = 1 ∨ η = -1)
    (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hint : MeasureTheory.Integrable (fun e : ℝ => e ^ 2) ν)
    (hpost : MeasureTheory.Integrable
      (fun e => hubPost c0 Lw η H B e ^ 2 + spokePost c0 Lw η H B e ^ 2) ν) :
    (∫ e, (hubPost c0 Lw η H B e ^ 2 + spokePost c0 Lw η H B e ^ 2) ∂ν) - (H ^ 2 + B ^ 2)
      ≤ -(1 - 2 * (c0 ^ 2 * ∫ e, e ^ 2 ∂ν)) * (H ^ 2 + B ^ 2)
        + 2 * (c0 ^ 2 * ∫ e, e ^ 2 ∂ν) * Lw ^ 2 := by
  have hAint : MeasureTheory.Integrable
      (fun e : ℝ => (2 * (H ^ 2 + B ^ 2) + 2 * Lw ^ 2) * c0 ^ 2 * e ^ 2) ν :=
    hint.const_mul _
  have hbound : ∀ e : ℝ, hubPost c0 Lw η H B e ^ 2 + spokePost c0 Lw η H B e ^ 2
      ≤ (2 * (H ^ 2 + B ^ 2) + 2 * Lw ^ 2) * c0 ^ 2 * e ^ 2 := by
    intro e
    have hp := sq_drift_pointwise (c0 := c0) (Lw := Lw) (ε := e) hc0 hη hH hB
    nlinarith
  have hmono := MeasureTheory.integral_mono hpost hAint hbound
  rw [MeasureTheory.integral_const_mul] at hmono
  nlinarith

/-! ## Position size

The kernel with the liquidity set by the mint, for `c₀ = 1` and all values in
common units, as in the proposition on the drift of position size. -/

/-- The new position's value `L' w`, by the size update of the proposition. -/
noncomputable def sizePost (Lw η H B ε : ℝ) : ℝ :=
  Lw + B + H - |imbalance Lw η H B| * |ε|

/-- **The size update from the mint.** Twice the new liquidity times the
per-token requirement is the sum of the inputs less their imbalance. -/
theorem new_liquidity_value (hg : 0 < g) (hη : η = 1 ∨ η = -1) :
    Lnew (xhat Lw η H B ε) (yhat Lw η H B ε 1) g g * (2 * g) = sizePost Lw η H B ε := by
  have hmin : Lnew (xhat Lw η H B ε) (yhat Lw η H B ε 1) g g
      = min (xhat Lw η H B ε) (yhat Lw η H B ε 1) / g := by
    unfold Lnew; rw [min_div_div_right hg.le]
  have hsum : xhat Lw η H B ε + yhat Lw η H B ε 1 = Lw + B + H := by
    unfold xhat yhat; ring
  have hdiff : xhat Lw η H B ε - yhat Lw η H B ε 1 = η * imbalance Lw η H B * ε := by
    rw [hat_diff]; ring
  have habs := abs_dir_mul hη (imbalance Lw η H B) ε
  unfold sizePost
  rw [hmin, ← habs, ← hdiff, ← hsum]
  rcases le_total (xhat Lw η H B ε) (yhat Lw η H B ε 1) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]
    field_simp
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]
    field_simp
    ring

/-- **Drift of position size, part (i).** Value is conserved at every event. -/
theorem size_conservation (hη : η = 1 ∨ η = -1) :
    sizePost Lw η H B ε + spokePost 1 Lw η H B ε + hubPost 1 Lw η H B ε = Lw + B + H := by
  have h := leftover_magnitude (c0 := 1) (Lw := Lw) (H := H) (B := B) (ε := ε) zero_le_one hη
  unfold sizePost
  linarith

/-- **Part (iii), first identity.** The own value `Z = Lw + B` of the position
changes by what the hub loses. -/
theorem own_value_change (hη : η = 1 ∨ η = -1) :
    (sizePost Lw η H B ε + spokePost 1 Lw η H B ε) - (Lw + B)
      = H - hubPost 1 Lw η H B ε := by
  have h := size_conservation (Lw := Lw) (H := H) (B := B) (ε := ε) hη
  linarith

/-- **Part (iii), after `η = +1`.** `H' = ε⁺ (Z - H)`. -/
theorem hubPost_up (hA : 0 ≤ imbalance Lw 1 H B) :
    hubPost 1 Lw 1 H B ε = max ε 0 * ((Lw + B) - H) := by
  rw [hubPost_eq_affine hA]
  unfold imbalance
  rw [show (1 : ℝ) * 1 * ε = ε by ring]
  ring

/-- **Part (iii), after `η = -1`.** `H' = ε⁻ (Z + H - 2 B)`. -/
theorem hubPost_down (hA : 0 ≤ imbalance Lw (-1) H B) :
    hubPost 1 Lw (-1) H B ε = max (-ε) 0 * ((Lw + B) + H - 2 * B) := by
  rw [hubPost_eq_affine hA]
  unfold imbalance
  rw [show (1 : ℝ) * (-1) * ε = -ε by ring]
  ring

/-- **Part (ii).** Given the pre-event state and the direction, the mean
change in size is `H + B - |A| E|ε|`. -/
theorem size_drift_integral (ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure ν]
    (hint : MeasureTheory.Integrable (fun e : ℝ => |e|) ν) :
    ∫ e, (sizePost Lw η H B e - Lw) ∂ν
      = H + B - |imbalance Lw η H B| * ∫ e, |e| ∂ν := by
  have hfun : (fun e : ℝ => sizePost Lw η H B e - Lw)
      = fun e => (H + B) - |imbalance Lw η H B| * |e| := by
    funext e; unfold sizePost; ring
  rw [hfun, MeasureTheory.integral_sub (MeasureTheory.integrable_const _)
      (hint.const_mul _), MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
  simp only [MeasureTheory.probReal_univ, one_smul]

/-- **Part (iv), the algebra.** Write `e₊ = E[ε⁺ | η = +1]` and
`e₋ = E[ε⁻ | η = -1]`. By part (iii) the mean hub entry after an event of
position `i` is `p₊ e₊ (Z_i - H) + p₋ e₋ (Z_i + H - 2 B_i)`, and its own value
changes by `H` less that; an event of another pool leaves `Z_i` unchanged.
With each pool firing with probability `1/N`, the expected own values of two
positions after one event therefore differ by
`(1 - γ₊/N)(Z_i - Z_j) + (2 c₋/N)(B_i - B_j)`, where `γ₊ = p₊ e₊ + p₋ e₋` and
`c₋ = p₋ e₋`. The conditional means enter as given numbers; the expectation
over the mark and the firing pool is not itself formalised. -/
theorem own_value_gap_drift (N pp pm ep em H Zi Zj Bi Bj : ℝ) :
    (Zi + (H - (pp * ep * (Zi - H) + pm * em * (Zi + H - 2 * Bi))) / N)
        - (Zj + (H - (pp * ep * (Zj - H) + pm * em * (Zj + H - 2 * Bj))) / N)
      = (1 - (pp * ep + pm * em) / N) * (Zi - Zj) + 2 * (pm * em) / N * (Bi - Bj) := by
  ring

end Kernel

end MasterEquation
