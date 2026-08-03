/-
Theorem 2 (multi-pool mass conservation under S = 0), §5.2, proved in
Appendix C, together with the deterministic core of the donor/absorber
remark and of Lemma 1.

The portfolio is a finite family of positions indexed by `κ` over a finite
token set `ι`. `a k i` is position `k`'s implied amount of token `i` at the
contemporaneous sqrt price, zero when `i` is not in pool `k`; `D i` is the
depositor-keyed dust ledger. A rebalance of pool `k₀` with tokens `ta, tb`
moves position `k₀` and the two ledger entries and nothing else.
-/
import MasterEquation.MasterJump

set_option linter.style.header false

namespace MasterEquation

open Finset

variable {ι κ : Type*} [Fintype κ]

/-- Per-token total across positions and the dust ledger, eq. (7). -/
noncomputable def totalMass (a : κ → ι → ℝ) (D : ι → ℝ) (i : ι) : ℝ :=
  (∑ k, a k i) + D i

/-- Fixed-price USD aggregate of the portfolio and the ledger, §5.2. -/
noncomputable def totalValue [Fintype ι] (a : κ → ι → ℝ) (D : ι → ℝ)
    (p : ι → ℝ) : ℝ :=
  ∑ i, totalMass a D i * p i

/-- The event data of a single swap-free rebalance of pool `k₀`. -/
structure Rebalance (ι κ : Type*) [Fintype κ] where
  /-- pre-event position amounts -/
  a : κ → ι → ℝ
  /-- pre-event dust ledger -/
  D : ι → ℝ
  /-- post-event position amounts -/
  a' : κ → ι → ℝ
  /-- post-event dust ledger -/
  D' : ι → ℝ
  /-- the rebalanced pool -/
  k₀ : κ
  /-- its token-0 -/
  ta : ι
  /-- its token-1 -/
  tb : ι
  /-- per-unit-liquidity token-0 requirement at the new range -/
  gx : ℝ
  /-- per-unit-liquidity token-1 requirement at the new range -/
  gy : ℝ
  ta_ne_tb : ta ≠ tb
  /-- no other position moves -/
  other_positions : ∀ k, k ≠ k₀ → a' k = a k
  /-- the rebalanced position holds nothing outside its own pool -/
  own_pool : ∀ i, i ≠ ta → i ≠ tb → a' k₀ i = a k₀ i
  /-- swap-free mint inputs recycle the pool's standing dust, eq. (2) -/
  mint_x : a' k₀ ta = Lnew (a k₀ ta + D ta) (a k₀ tb + D tb) gx gy * gx
  mint_y : a' k₀ tb = Lnew (a k₀ ta + D ta) (a k₀ tb + D tb) gx gy * gy
  /-- the leftover is credited to the ledger, eq. (4) and (5) -/
  credit_x : D' ta = dustX (a k₀ ta + D ta) (a k₀ tb + D tb) gx gy
  credit_y : D' tb = dustY (a k₀ ta + D ta) (a k₀ tb + D tb) gx gy
  /-- ledger entries for tokens outside the pool are untouched, eq. (5) -/
  ledger_other : ∀ i, i ≠ ta → i ≠ tb → D' i = D i

namespace Rebalance

variable (e : Rebalance ι κ)

/-- Splitting a position sum off the rebalanced pool. -/
private lemma sum_split [DecidableEq κ] (f : κ → ℝ) :
    ∑ k, f k = (∑ k ∈ univ.erase e.k₀, f k) + f e.k₀ :=
  (Finset.add_sum_erase _ f (mem_univ e.k₀)).symm.trans (add_comm _ _)

/-- **Theorem 2.** Under `S = 0`, the per-token total of position amounts and
the dust ledger is invariant across the rebalance, evaluated at the
contemporaneous sqrt price. -/
theorem mass_conservation (i : ι) :
    totalMass e.a' e.D' i = totalMass e.a e.D i := by
  classical
  unfold totalMass
  rw [sum_split e (fun k => e.a' k i), sum_split e (fun k => e.a k i)]
  have hrest : ∑ k ∈ univ.erase e.k₀, e.a' k i = ∑ k ∈ univ.erase e.k₀, e.a k i := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [e.other_positions k (Finset.ne_of_mem_erase hk)]
  rw [hrest]
  by_cases hta : i = e.ta
  · subst hta
    rw [e.mint_x, e.credit_x]
    unfold dustX
    ring
  · by_cases htb : i = e.tb
    · subst htb
      rw [e.mint_y, e.credit_y]
      unfold dustY
      ring
    · rw [e.own_pool i hta htb, e.ledger_other i hta htb]

/-- The fixed-price USD aggregate inherits the event-level invariance. -/
theorem value_conservation [Fintype ι] (p : ι → ℝ) :
    totalValue e.a' e.D' p = totalValue e.a e.D p := by
  unfold totalValue
  exact Finset.sum_congr rfl fun i _ => by rw [e.mass_conservation i]

end Rebalance

/-! ## Donor/absorber decomposition (remark after Theorem 2, Lemma 1) -/

/-- The accounting identity behind the donor/absorber remark: over any window,
the cumulative position impacts and the change in ledger value sum to zero. -/
theorem impacts_add_ledger_change_eq_zero [Fintype ι]
    {a₀ a₁ : κ → ι → ℝ} {D₀ D₁ : ι → ℝ} {p : ι → ℝ}
    (h : totalValue a₁ D₁ p = totalValue a₀ D₀ p) :
    (∑ k, ∑ i, (a₁ k i - a₀ k i) * p i) + (∑ i, (D₁ i - D₀ i) * p i) = 0 := by
  have expand : ∀ (a : κ → ι → ℝ) (D : ι → ℝ),
      totalValue a D p = (∑ k, ∑ i, a k i * p i) + ∑ i, D i * p i := by
    intro a D
    unfold totalValue totalMass
    have step : ∀ i : ι, ((∑ k, a k i) + D i) * p i
        = (∑ k, a k i * p i) + D i * p i := by
      intro i; rw [add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_add_distrib,
      Finset.sum_comm]
  rw [expand a₁ D₁, expand a₀ D₀] at h
  have hk : ∑ k, ∑ i, (a₁ k i - a₀ k i) * p i
      = (∑ k, ∑ i, a₁ k i * p i) - ∑ k, ∑ i, a₀ k i * p i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hd : ∑ i, (D₁ i - D₀ i) * p i = (∑ i, D₁ i * p i) - ∑ i, D₀ i * p i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hk, hd]
  linarith

/-- **Deterministic core of Lemma 1.** Once the conservation constraint forces
the cumulative impacts to sum to zero, any departure from the all-zero
profile is necessarily a non-trivial donor/absorber partition: at least one
strict donor and at least one strict absorber. What Lemma 1 adds is the
probabilistic statement that the all-zero profile is not the typical one. -/
theorem mixed_sign_of_sum_zero {α : Type*} {s : Finset α} {f : α → ℝ}
    (hsum : ∑ k ∈ s, f k = 0) {k₁ : α} (hk₁ : k₁ ∈ s) (hne : f k₁ ≠ 0) :
    (∃ k ∈ s, 0 < f k) ∧ (∃ k ∈ s, f k < 0) := by
  constructor
  · by_contra hcon
    have hle : ∀ k ∈ s, f k ≤ 0 := fun k hk => not_lt.mp fun hlt => hcon ⟨k, hk, hlt⟩
    exact hne ((Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum k₁ hk₁)
  · by_contra hcon
    have hge : ∀ k ∈ s, 0 ≤ f k := fun k hk => not_lt.mp fun hlt => hcon ⟨k, hk, hlt⟩
    exact hne ((Finset.sum_eq_zero_iff_of_nonneg hge).mp hsum k₁ hk₁)

end MasterEquation
