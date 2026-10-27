import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Rotation

open Finset

def P : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => (a + b).choose a * P as bs
  | _, _ => 1

lemma choose_mul_choose_le_add (m n i j : ℕ) :
    m.choose i * n.choose j ≤ (m + n).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact single_le_sum (f := fun ij : ℕ × ℕ => m.choose ij.1 * n.choose ij.2)
    (fun _ _ => Nat.zero_le _) (mem_antidiagonal.2 (rfl : (i, j).1 + (i, j).2 = i + j))

lemma two_terms_le (m n i j i' j' : ℕ) (h : i + j = i' + j') (hne : i ≠ i') :
    m.choose i * n.choose j + m.choose i' * n.choose j' ≤ (m + n).choose (i + j) := by
  rw [Nat.add_choose_eq]
  have hsub : ({(i, j), (i', j')} : Finset (ℕ × ℕ)) ⊆ antidiagonal (i + j) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [mem_antidiagonal, h]
  have hpair : ((i, j) : ℕ × ℕ) ≠ (i', j') := fun h' => hne (Prod.mk.inj h').1
  calc m.choose i * n.choose j + m.choose i' * n.choose j'
      = ∑ ij ∈ ({(i, j), (i', j')} : Finset (ℕ × ℕ)), m.choose ij.1 * n.choose ij.2 := by
        rw [sum_pair hpair]
    _ ≤ _ := sum_le_sum_of_subset hsub

theorem P_le : ∀ (as bs : List ℕ), as.length = bs.length →
    P as bs ≤ (as.sum + bs.sum).choose as.sum
  | [], [], _ => by simp [P]
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [P, List.sum_cons]
    calc (a + b).choose a * P as bs
        ≤ (a + b).choose a * (as.sum + bs.sum).choose as.sum :=
          Nat.mul_le_mul_left _ (P_le as bs h)
      _ ≤ ((a + b) + (as.sum + bs.sum)).choose (a + as.sum) := choose_mul_choose_le_add _ _ _ _
      _ = _ := by congr 1; omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem two_mul_P_le : ∀ (as bs : List ℕ), as.length = bs.length → as.sum = bs.sum →
    as ≠ bs → 2 * P as bs ≤ (2 * as.sum).choose as.sum
  | [], [], _, _, hne => absurd rfl hne
  | a :: as, b :: bs, hl, hs, hne => by
    simp only [List.length_cons, add_left_inj] at hl
    simp only [P, List.sum_cons] at hs ⊢
    by_cases hab : a = b
    · subst hab
      have hs' : as.sum = bs.sum := by omega
      have hne' : as ≠ bs := fun h => hne (by rw [h])
      have ih := two_mul_P_le as bs hl hs' hne'
      calc 2 * ((a + a).choose a * P as bs)
          = (a + a).choose a * (2 * P as bs) := by ring
        _ ≤ (a + a).choose a * (2 * as.sum).choose as.sum := Nat.mul_le_mul_left _ ih
        _ ≤ ((a + a) + 2 * as.sum).choose (a + as.sum) := choose_mul_choose_le_add _ _ _ _
        _ = _ := by congr 1; ring
    · have h1 := P_le as bs hl
      have hsym1 : (a + b).choose a = (a + b).choose b := Nat.choose_symm_add
      have hsym2 : (as.sum + bs.sum).choose as.sum = (as.sum + bs.sum).choose bs.sum :=
        Nat.choose_symm_add
      calc 2 * ((a + b).choose a * P as bs)
          ≤ 2 * ((a + b).choose a * (as.sum + bs.sum).choose as.sum) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
        _ = (a + b).choose a * (as.sum + bs.sum).choose as.sum
              + (a + b).choose b * (as.sum + bs.sum).choose bs.sum := by
            rw [← hsym1, ← hsym2]; ring
        _ ≤ ((a + b) + (as.sum + bs.sum)).choose (a + as.sum) :=
            two_terms_le _ _ _ _ _ _ hs hab
        _ = _ := by congr 1; omega
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

theorem image_ne_of_injOn {X Y : Finset ℕ} (f : ℕ → ℕ) (hf : Set.InjOn f ↑(X ∪ Y))
    (h0X : 0 ∈ X) (h0Y : 0 ∉ Y) : X.image f ≠ Y.image f := by
  intro h
  have : f 0 ∈ Y.image f := h ▸ mem_image_of_mem f h0X
  obtain ⟨y, hy, hfy⟩ := mem_image.1 this
  have := hf (by simp [hy]) (by simp [h0X]) hfy
  exact h0Y (this ▸ hy)

example (k d : ℕ) (hd : d < k) : 0 ∉ Ico (k - d) k := by simp; omega

example (k d : ℕ) (hd : d < k - 1) : 0 ∉ Ico (k - d - 1) (k - 1) := by simp; omega

end Rotation
