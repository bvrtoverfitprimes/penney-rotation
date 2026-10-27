import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace Rotation

open Finset

variable (k : ℕ) (occ : ℕ → Prop) [DecidablePred occ]

def IsChain (t : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ range (t + 1) ∧ 0 ∈ S ∧ t ∈ S ∧ (∀ s ∈ S, occ s) ∧
    ∀ s ∈ S, s ≠ 0 → ∃ r ∈ S, r < s ∧ s < r + k

open Classical in

noncomputable def chains (t : ℕ) : Finset (Finset ℕ) :=
  (range (t + 1)).powerset.filter (IsChain k occ t)

noncomputable def W (t : ℕ) : ℤ :=
  ∑ S ∈ chains k occ t, (-1 : ℤ) ^ S.card

variable {k occ}

lemma mem_chains {t : ℕ} {S : Finset ℕ} : S ∈ chains k occ t ↔ IsChain k occ t S := by
  classical
  unfold chains
  simp only [mem_filter, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma IsChain.le_of_mem {t : ℕ} {S : Finset ℕ} (h : IsChain k occ t S) {x : ℕ} (hx : x ∈ S) :
    x ≤ t := by
  have := h.1 hx
  simp only [mem_range] at this
  omega

lemma chains_zero : chains k occ 0 = if occ 0 then {{0}} else ∅ := by
  ext S
  rw [mem_chains]
  constructor
  · intro h
    have hS : S = {0} := by
      ext x
      simp only [mem_singleton]
      exact ⟨fun hx => by have := h.le_of_mem hx; omega, fun hx => hx ▸ h.2.1⟩
    simp [h.2.2.2.1 0 h.2.1, hS]
  · intro h
    split_ifs at h with h0
    · simp only [mem_singleton] at h
      subst h
      refine ⟨by simp, by simp, by simp, by simpa using h0, by simp⟩
    · simp at h

lemma W_zero : W k occ 0 = if occ 0 then -1 else 0 := by
  unfold W
  rw [chains_zero]
  split_ifs <;> simp

lemma chains_succ_eq {t : ℕ} (ht : 0 < t) (hocc : occ t) :
    chains k occ t =
      (Ico (t + 1 - k) t).biUnion (fun s => (chains k occ s).image (insert t)) := by
  ext S
  simp only [mem_biUnion, mem_image, mem_Ico, mem_chains]
  constructor
  · intro h
    obtain ⟨hsub, h0, ht', hocc', hpred⟩ := h
    have hne : (S.erase t).Nonempty := ⟨0, mem_erase.2 ⟨by omega, h0⟩⟩
    set s := (S.erase t).max' hne with hs
    have hsmem : s ∈ S.erase t := max'_mem _ _
    have hsle : ∀ x ∈ S.erase t, x ≤ s := fun x hx => le_max' _ x hx
    have hsS : s ∈ S := (mem_erase.1 hsmem).2
    have hslt : s < t := by
      have h1 : s ≤ t := by
        have := hsub hsS
        simp only [mem_range] at this
        omega
      have h2 : s ≠ t := (mem_erase.1 hsmem).1
      omega
    obtain ⟨r, hrS, hrt, htr⟩ := hpred t ht' (by omega)
    have hrs : r ≤ s := hsle r (mem_erase.2 ⟨by omega, hrS⟩)
    refine ⟨s, ⟨by omega, hslt⟩, S.erase t, ⟨?_, ?_, hsmem, ?_, ?_⟩, insert_erase ht'⟩
    · intro x hx
      simp only [mem_range]
      have := hsle x hx
      omega
    · exact mem_erase.2 ⟨by omega, h0⟩
    · intro x hx
      exact hocc' x (mem_erase.1 hx).2
    · intro x hx hx0
      have hxS := (mem_erase.1 hx).2
      have hxt : x < t := by
        have := hsub hxS
        simp only [mem_range] at this
        have := (mem_erase.1 hx).1
        omega
      obtain ⟨r, hrS, hrx, hxr⟩ := hpred x hxS hx0
      exact ⟨r, mem_erase.2 ⟨by omega, hrS⟩, hrx, hxr⟩
  · rintro ⟨s, ⟨hs1, hs2⟩, S', ⟨hsub, h0, hsS, hocc', hpred⟩, rfl⟩
    refine ⟨?_, mem_insert_of_mem h0, mem_insert_self _ _, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_range] at hx ⊢
      rcases hx with rfl | hx
      · omega
      · have := hsub hx
        simp only [mem_range] at this
        omega
    · intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact hocc
      · exact hocc' x hx
    · intro x hx hx0
      rcases mem_insert.1 hx with rfl | hx
      · exact ⟨s, mem_insert_of_mem hsS, hs2, by omega⟩
      · obtain ⟨r, hrS, hrx, hxr⟩ := hpred x hx hx0
        exact ⟨r, mem_insert_of_mem hrS, hrx, hxr⟩

theorem W_rec {t : ℕ} (ht : 0 < t) :
    W k occ t = if occ t then -∑ s ∈ Ico (t + 1 - k) t, W k occ s else 0 := by
  split_ifs with hocc
  · unfold W
    rw [chains_succ_eq ht hocc, sum_biUnion, ← sum_neg_distrib]
    · refine sum_congr rfl fun s hs => ?_
      have hst : s < t := (mem_Ico.1 hs).2
      rw [sum_image, ← sum_neg_distrib]
      · refine sum_congr rfl fun S hS => ?_
        have htS : t ∉ S := by
          intro h
          have := (mem_chains.1 hS).le_of_mem h
          omega
        rw [card_insert_of_notMem htS, pow_succ, mul_neg_one]
      · intro S hS S' hS' heq
        have h1 : t ∉ S := fun h => by have := (mem_chains.1 hS).le_of_mem h; omega
        have h2 : t ∉ S' := fun h => by have := (mem_chains.1 hS').le_of_mem h; omega
        have := congrArg (fun X => X.erase t) heq
        simpa [erase_insert h1, erase_insert h2] using this
    · intro s _ s' _ hss'
      simp only [Function.onFun]
      rw [disjoint_left]
      intro X hX hX'
      obtain ⟨S, hS, rfl⟩ := mem_image.1 hX
      obtain ⟨S', hS', heq⟩ := mem_image.1 hX'
      have hS1 := mem_chains.1 hS
      have hS2 := mem_chains.1 hS'
      have hsS' : s' ∈ insert t S := heq ▸ mem_insert_of_mem hS2.2.2.1
      have hsS : s ∈ insert t S' := heq ▸ mem_insert_of_mem hS1.2.2.1
      have hlt1 : s' < t := by
        have := (mem_Ico.1 ‹s' ∈ _›).2; exact this
      have hlt2 : s < t := by
        have := (mem_Ico.1 ‹s ∈ _›).2; exact this
      rcases mem_insert.1 hsS' with h | h
      · omega
      rcases mem_insert.1 hsS with h' | h'
      · omega
      have := hS1.le_of_mem h
      have := hS2.le_of_mem h'
      exact hss' (by omega)
  · unfold W
    have : chains k occ t = ∅ := by
      ext S
      simp only [mem_chains, Finset.notMem_empty, iff_false]
      exact fun h => hocc (h.2.2.2.1 t h.2.2.1)
    rw [this, sum_empty]

noncomputable def Q (k : ℕ) (occ : ℕ → Prop) [DecidablePred occ] (n : ℕ) : ℤ := ∑ s ∈ range n, W k occ s

theorem Q_mem (hk : 1 ≤ k) : ∀ n, Q k occ n = 0 ∨ Q k occ n = -1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | t
    · simp [Q]
    · have hstep : Q k occ (t + 1) = Q k occ t + W k occ t := by
        simp [Q, sum_range_succ]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [hstep, W_zero]
        simp only [Q, range_zero, sum_empty, zero_add]
        split_ifs <;> simp
      · rw [hstep, W_rec ht]
        split_ifs with hocc
        · have hsplit : Q k occ t =
              Q k occ (t + 1 - k) + ∑ s ∈ Ico (t + 1 - k) t, W k occ s := by
            simp only [Q]
            rw [sum_range_add_sum_Ico _ (by omega)]
          rw [hsplit]
          have := ih (t + 1 - k) (by omega)
          rcases this with h | h <;> simp [h]
        · simpa using ih t (by omega)

theorem W_mem (hk : 1 ≤ k) (t : ℕ) : W k occ t = -1 ∨ W k occ t = 0 ∨ W k occ t = 1 := by
  have h : W k occ t = Q k occ (t + 1) - Q k occ t := by
    simp [Q, sum_range_succ]
  rcases Q_mem (occ := occ) hk (t + 1) with h1 | h1 <;> rcases Q_mem (occ := occ) hk t with h2 | h2 <;>
    rw [h, h1, h2] <;> simp

theorem abs_W_le (hk : 1 ≤ k) (t : ℕ) : |W k occ t| ≤ 1 := by
  rcases W_mem (occ := occ) hk t with h | h | h <;> rw [h] <;> simp

theorem exists_chain_of_W_ne_zero {t : ℕ} (h : W k occ t ≠ 0) : ∃ S, IsChain k occ t S := by
  by_contra hne
  push Not at hne
  apply h
  unfold W
  have : chains k occ t = ∅ := by
    ext S
    simp only [mem_chains, Finset.notMem_empty, iff_false]
    exact hne S
  rw [this, sum_empty]

theorem IsChain.meets_block {t : ℕ} {S : Finset ℕ} (h : IsChain k occ t S) {a : ℕ}
    (ha : 0 < a) (hat : a + k - 2 < t) (hk : 1 ≤ k) :
    ∃ x ∈ S, a ≤ x ∧ x ≤ a + k - 2 := by
  classical
  have hne : (S.filter (fun x => a ≤ x)).Nonempty := ⟨t, mem_filter.2 ⟨h.2.2.1, by omega⟩⟩
  set x := (S.filter (fun x => a ≤ x)).min' hne
  have hx : x ∈ S.filter (fun x => a ≤ x) := min'_mem _ _
  have hxS := (mem_filter.1 hx).1
  have hax := (mem_filter.1 hx).2
  obtain ⟨r, hrS, hrx, hxr⟩ := h.2.2.2.2 x hxS (by omega)
  have hra : r < a := by
    by_contra hcon
    push Not at hcon
    have hle : x ≤ r := min'_le _ r (mem_filter.2 ⟨hrS, hcon⟩)
    omega
  exact ⟨x, hxS, hax, by omega⟩

theorem IsChain.first_crossing {t : ℕ} {S : Finset ℕ} (hS : IsChain k occ t S) {h : ℕ}
    (hh : 0 < h) (ht : h ≤ t) :
    ∃ x ∈ S, h ≤ x ∧ x ≤ h + k - 2 ∧ ∀ y ∈ S, y < h ∨ x ≤ y := by
  classical
  have hne : (S.filter (fun x => h ≤ x)).Nonempty := ⟨t, mem_filter.2 ⟨hS.2.2.1, ht⟩⟩
  set x := (S.filter (fun x => h ≤ x)).min' hne
  have hx : x ∈ S.filter (fun x => h ≤ x) := min'_mem _ _
  have hxS := (mem_filter.1 hx).1
  have hax := (mem_filter.1 hx).2
  obtain ⟨r, hrS, hrx, hxr⟩ := hS.2.2.2.2 x hxS (by omega)
  have hra : r < h := by
    by_contra hcon
    push Not at hcon
    have hle : x ≤ r := min'_le _ r (mem_filter.2 ⟨hrS, hcon⟩)
    omega
  refine ⟨x, hxS, hax, by omega, fun y hy => ?_⟩
  by_cases hyh : h ≤ y
  · have hle : x ≤ y := min'_le _ y (mem_filter.2 ⟨hy, hyh⟩)
    exact Or.inr hle
  · exact Or.inl (by omega)

end Rotation
