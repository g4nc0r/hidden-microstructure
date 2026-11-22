/-
Lemma 1 (transfers sum to zero), the paragraph "Transfers between positions"
after Theorem 2.

Each position `k` of a finite family holds an entitlement `G k ≥ 0` to the
ledger, the entitlements summing to the ledger's value. At a rebalance of
position `j`, with deployed value `Vj` before and `Vnew` after and a net value
`σ` paid into the swap, the transfer is the part of the minted value above the
position's own equity,

  Ξ = (Vnew - (Vj + G j) + σ)⁺,

taken from the other positions in proportion to their entitlements. This is
the transfer as the prior paper defines it, under its ownerless rule; the
present file checks the four parts of Lemma 1 for it.

The one hypothesis beyond the definitions is the mint's budget: a position
cannot mint more than its own withdrawn value and the whole ledger supply,
`Vnew ≤ Vj + ∑ G - σ`. At fixed reference prices that is the value form of
Theorem 1's feasibility constraint, and it is what makes the transfer no
larger than what the others are owed.
-/
import MasterEquation.Conservation

set_option linter.style.header false

namespace MasterEquation

namespace Transfers

open Finset

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The transfer at a rebalance: minted value above the position's equity net
of its swap. -/
noncomputable def transfer (Vj Gj σ Vnew : ℝ) : ℝ := max (Vnew - (Vj + Gj) + σ) 0

/-- Total entitlement of the positions other than `j`. -/
noncomputable def others (G : κ → ℝ) (j : κ) : ℝ := ∑ k ∈ univ.erase j, G k

/-- Net transfer to position `k` at a rebalance of `j` with transfer `Ξ`: the
rebalancing position receives `Ξ`, every other gives in proportion to its
entitlement. -/
noncomputable def netTransfer (G : κ → ℝ) (j : κ) (Ξ : ℝ) (k : κ) : ℝ :=
  if k = j then Ξ else -(Ξ * G k / others G j)

/-- Entitlements after the event. The rebalancing position keeps what its
equity exceeds its mint by, which is zero when the transfer is positive; the
others are reduced by what they gave. -/
noncomputable def entitlementAfter (G : κ → ℝ) (j : κ) (Vj σ Vnew : ℝ) (k : κ) : ℝ :=
  if k = j then max (Vj + G j - σ - Vnew) 0
  else G k + netTransfer G j (transfer Vj (G j) σ Vnew) k

theorem transfer_nonneg (Vj Gj σ Vnew : ℝ) : 0 ≤ transfer Vj Gj σ Vnew :=
  le_max_right _ _

theorem sum_eq_others_add (G : κ → ℝ) (j : κ) : ∑ k, G k = others G j + G j :=
  (Finset.add_sum_erase _ G (mem_univ j)).symm.trans (add_comm _ _)

/-- Under the mint's budget the transfer is at most what the others are
owed. -/
theorem transfer_le_others (G : κ → ℝ) (j : κ) {Vj σ Vnew : ℝ}
    (hG : ∀ k, 0 ≤ G k) (hbudget : Vnew ≤ Vj + ∑ k, G k - σ) :
    transfer Vj (G j) σ Vnew ≤ others G j := by
  have hsum := sum_eq_others_add G j
  have ho : 0 ≤ others G j := Finset.sum_nonneg fun k _ => hG k
  unfold transfer
  exact max_le (by linarith) ho

/-- The net transfers given by the others sum to minus the transfer. -/
theorem sum_netTransfer_others (G : κ → ℝ) (j : κ) (Ξ : ℝ)
    (h : Ξ ≠ 0 → others G j ≠ 0) :
    ∑ k ∈ univ.erase j, netTransfer G j Ξ k = -Ξ := by
  have hrw : ∀ k ∈ univ.erase j, netTransfer G j Ξ k = -(Ξ / others G j) * G k := by
    intro k hk
    unfold netTransfer
    rw [if_neg (Finset.ne_of_mem_erase hk)]
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  by_cases hΞ : Ξ = 0
  · rw [hΞ]; simp
  · have ho := h hΞ
    change -(Ξ / others G j) * others G j = -Ξ
    field_simp

/-- **Lemma 1(i), second half.** The net transfers of one event sum to zero,
with or without a swap. -/
theorem sum_netTransfer_eq_zero (G : κ → ℝ) (j : κ) (Ξ : ℝ)
    (h : Ξ ≠ 0 → others G j ≠ 0) :
    ∑ k, netTransfer G j Ξ k = 0 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ j), sum_netTransfer_others G j Ξ h]
  unfold netTransfer
  rw [if_pos rfl]
  ring

/-- **Lemma 1(i), first half.** After the event the entitlements sum to the
value of the ledger, which the event has changed by the value withdrawn, less
what the swap paid away, less the value minted. -/
theorem sum_entitlementAfter (G : κ → ℝ) (j : κ) {Vj σ Vnew : ℝ}
    (hG : ∀ k, 0 ≤ G k) (hbudget : Vnew ≤ Vj + ∑ k, G k - σ) :
    ∑ k, entitlementAfter G j Vj σ Vnew k = (∑ k, G k) + Vj - σ - Vnew := by
  have hle := transfer_le_others G j hG hbudget
  have hnn := transfer_nonneg Vj (G j) σ Vnew
  have hne : transfer Vj (G j) σ Vnew ≠ 0 → others G j ≠ 0 := by
    intro h0 hzero
    exact h0 (le_antisymm (hzero ▸ hle) hnn)
  rw [← Finset.add_sum_erase _ _ (mem_univ j)]
  have hrest : ∑ k ∈ univ.erase j, entitlementAfter G j Vj σ Vnew k
      = others G j - transfer Vj (G j) σ Vnew := by
    have hrw : ∀ k ∈ univ.erase j, entitlementAfter G j Vj σ Vnew k
        = G k + netTransfer G j (transfer Vj (G j) σ Vnew) k := by
      intro k hk
      unfold entitlementAfter
      rw [if_neg (Finset.ne_of_mem_erase hk)]
    rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib,
      sum_netTransfer_others G j _ hne]
    unfold others
    ring
  rw [hrest, sum_eq_others_add G j]
  unfold entitlementAfter transfer
  rw [if_pos rfl]
  rcases le_total (Vnew - (Vj + G j) + σ) 0 with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left hc, max_eq_right (by linarith)]
    ring

/-- Entitlements stay non-negative under the mint's budget. -/
theorem entitlementAfter_nonneg (G : κ → ℝ) (j : κ) {Vj σ Vnew : ℝ}
    (hG : ∀ k, 0 ≤ G k) (hbudget : Vnew ≤ Vj + ∑ k, G k - σ) (k : κ) :
    0 ≤ entitlementAfter G j Vj σ Vnew k := by
  have hle := transfer_le_others G j hG hbudget
  have hnn := transfer_nonneg Vj (G j) σ Vnew
  have ho : 0 ≤ others G j := Finset.sum_nonneg fun i _ => hG i
  unfold entitlementAfter
  by_cases hk : k = j
  · rw [if_pos hk]; exact le_max_right _ _
  · rw [if_neg hk]
    unfold netTransfer
    rw [if_neg hk]
    rcases ho.eq_or_lt with hz | hpos
    · rw [← hz, div_zero, neg_zero, add_zero]; exact hG k
    · have hfrac : transfer Vj (G j) σ Vnew * G k / others G j ≤ G k := by
        rw [div_le_iff₀ hpos]
        nlinarith [hG k]
      linarith

/-- **Lemma 1(iii).** A lone position gives and receives nothing: with no
other entitlement to draw on, the transfer is zero at every event. -/
theorem transfer_eq_zero_of_alone (G : κ → ℝ) (j : κ) {Vj σ Vnew : ℝ}
    (hG : ∀ k, 0 ≤ G k) (hbudget : Vnew ≤ Vj + ∑ k, G k - σ)
    (halone : others G j = 0) : transfer Vj (G j) σ Vnew = 0 :=
  le_antisymm (halone ▸ transfer_le_others G j hG hbudget) (transfer_nonneg _ _ _ _)

/-- With one position only, there are no others. -/
theorem others_eq_zero_of_subsingleton [Subsingleton κ] (G : κ → ℝ) (j : κ) :
    others G j = 0 := by
  unfold others
  refine Finset.sum_eq_zero fun k hk => ?_
  exact absurd (Subsingleton.elim k j) (Finset.ne_of_mem_erase hk)

/-- **Lemma 1(iv).** The value change of the rebalancing position is the
transfer it received, less the cost of its swap, less the change in its own
entitlement. -/
theorem value_change (G : κ → ℝ) (j : κ) (Vj σ Vnew : ℝ) :
    Vnew - Vj = netTransfer G j (transfer Vj (G j) σ Vnew) j - σ
      - (entitlementAfter G j Vj σ Vnew j - G j) := by
  unfold netTransfer entitlementAfter transfer
  rw [if_pos rfl, if_pos rfl]
  rcases le_total (Vnew - (Vj + G j) + σ) 0 with hc | hc
  · rw [max_eq_right hc, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left hc, max_eq_right (by linarith)]
    ring

omit [DecidableEq κ] in
/-- **Lemma 1(ii).** Over any window of events whose net transfers each sum to
zero, the cumulative net transfers of the positions sum to zero. -/
theorem sum_cumulative_eq_zero {τ : Type*} (T : Finset τ) (ξ : τ → κ → ℝ)
    (h : ∀ t ∈ T, ∑ k, ξ t k = 0) :
    ∑ k, ∑ t ∈ T, ξ t k = 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero h

omit [DecidableEq κ] in
/-- **Lemma 1(ii), the partition.** The cumulative net transfers are either
all zero or include a net receiver and a net giver. -/
theorem receiver_and_giver {τ : Type*} (T : Finset τ) (ξ : τ → κ → ℝ)
    (h : ∀ t ∈ T, ∑ k, ξ t k = 0) {k₁ : κ} (hne : ∑ t ∈ T, ξ t k₁ ≠ 0) :
    (∃ k, 0 < ∑ t ∈ T, ξ t k) ∧ (∃ k, ∑ t ∈ T, ξ t k < 0) := by
  obtain ⟨⟨k, _, hk⟩, ⟨k', _, hk'⟩⟩ :=
    mixed_sign_of_sum_zero (s := univ) (f := fun k => ∑ t ∈ T, ξ t k)
      (sum_cumulative_eq_zero T ξ h) (mem_univ k₁) hne
  exact ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩

end Transfers

end MasterEquation
