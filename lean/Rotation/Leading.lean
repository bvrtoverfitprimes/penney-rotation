import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Rotation.Shuffle

namespace Rotation

def SameOrder (u v : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ i j, i < m → j < m → (u i < u j ↔ v i < v j)

def shift (u : ℕ → ℕ) : ℕ → ℕ := fun i => u (i + 1)

def Incr (u : ℕ → ℕ) (k : ℕ) : Prop := ∀ i j, i < j → j < k → u i < u j

def Decr (u : ℕ → ℕ) (k : ℕ) : Prop := ∀ i j, i < j → j < k → u j < u i

lemma incr_of_adj {u : ℕ → ℕ} {k : ℕ} (h : ∀ i, i + 1 < k → u i < u (i + 1)) : Incr u k := by
  intro i j hij hjk
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
    · exact lt_trans (ih hlt (by omega)) (h j hjk)
    · subst heq; exact h i hjk

lemma decr_of_adj {u : ℕ → ℕ} {k : ℕ} (h : ∀ i, i + 1 < k → u (i + 1) < u i) : Decr u k := by
  intro i j hij hjk
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
    · exact lt_trans (h j hjk) (ih hlt (by omega))
    · subst heq; exact h i hjk

theorem monotone_of_self_overlap {u : ℕ → ℕ} {k : ℕ}
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (h : SameOrder (shift u) u (k - 1)) : Incr u k ∨ Decr u k := by

  have hprop : ∀ i, i + 1 < k → (u i < u (i + 1) ↔ u 0 < u 1) := by
    intro i hi
    induction i with
    | zero => exact Iff.rfl
    | succ i ih =>
      have := h i (i + 1) (by omega) (by omega)
      simp only [shift] at this
      rw [this]
      exact ih (by omega)
  have hne : ∀ i, i + 1 < k → u i ≠ u (i + 1) := fun i hi heq => by
    have := hinj i (i + 1) (by omega) hi heq; omega
  by_cases h01 : u 0 < u 1
  · left
    exact incr_of_adj fun i hi => (hprop i hi).2 h01
  · right
    refine decr_of_adj fun i hi => ?_
    have h1 : ¬ u i < u (i + 1) := fun h' => h01 ((hprop i hi).1 h')
    exact lt_of_le_of_ne (not_lt.1 h1) (hne i hi).symm

def unrot (B : ℕ → ℕ) (k : ℕ) : ℕ → ℕ := fun i => if i + 1 < k then B (i + 1) else B 0

theorem not_sameOrder_of_monotone {B : ℕ → ℕ} {k : ℕ} (hk : 3 ≤ k)
    (hB : Incr B k ∨ Decr B k) : ¬ SameOrder (shift (unrot B k)) B (k - 1) := by
  intro h
  have := h (k - 3) (k - 2) (by omega) (by omega)
  simp only [shift, unrot] at this
  have e1 : k - 3 + 1 + 1 < k := by omega
  have e2 : ¬ (k - 2 + 1 + 1 < k) := by omega
  rw [if_pos e1, if_neg e2] at this
  have e3 : k - 3 + 1 + 1 = k - 1 := by omega
  rw [e3] at this
  rcases hB with hB | hB
  · have a1 := hB 0 (k - 1) (by omega) (by omega)
    have a2 := hB (k - 3) (k - 2) (by omega) (by omega)
    have := this.2 a2
    omega
  · have a1 := hB 0 (k - 1) (by omega) (by omega)
    have a2 := hB (k - 3) (k - 2) (by omega) (by omega)
    have h3 : ¬ B (k - 1) < B 0 := fun h' => by
      have := this.1 h'
      omega
    omega

theorem P_disjoint_support : ∀ (as bs : List ℕ), (∀ p ∈ as.zip bs, p.1 * p.2 = 0) →
    P as bs = 1
  | [], _, _ => by simp [P]
  | _ :: _, [], _ => by simp [P]
  | a :: as, b :: bs, h => by
    have h0 := h (a, b) (by simp)
    have ih := P_disjoint_support as bs (fun p hp => h p (by simp [hp]))
    simp only [P, ih, mul_one]
    rcases Nat.mul_eq_zero.1 h0 with h1 | h1
    · simp only at h1; subst h1; simp
    · simp only at h1; subst h1; simp

theorem leading_pos (NAA NBA NAB NBB : ℤ) (hAA : 0 ≤ NAA) (hBA : NBA = 2) (hAB : NAB ≤ 1)
    (hAB0 : 0 ≤ NAB) (hBB : NBB = 0 ∨ NBB = 1) (hBBAB : NBB = 1 → NAB = 0) :
    1 ≤ NAA + NBA - NAB - NBB := by
  rcases hBB with h | h
  · omega
  · have := hBBAB h; omega

end Rotation
