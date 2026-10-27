import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Rotation

open Finset

lemma sum_pow_div_block (q : ℚ) (L M : ℕ) (hL : 0 < L) :
    ∑ j ∈ range (L * M), q ^ (j / L) = L * ∑ m ∈ range M, q ^ m := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show L * (M + 1) = L * M + L by ring, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    have : ∀ r ∈ range L, q ^ ((L * M + r) / L) = q ^ M := by
      intro r hr
      rw [mem_range] at hr
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hr, zero_add]
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

theorem block_sum_le (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (L : ℕ) (hL : 0 < L) (N : ℕ) :
    ∑ j ∈ range N, q ^ (j / L) ≤ L / (1 - q) := by
  have hN : N ≤ L * N := Nat.le_mul_of_pos_left N hL
  calc ∑ j ∈ range N, q ^ (j / L) ≤ ∑ j ∈ range (L * N), q ^ (j / L) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hN)
          (fun _ _ _ => pow_nonneg hq0 _)
    _ = L * ∑ m ∈ range N, q ^ m := sum_pow_div_block q L N hL
    _ ≤ L * (1 / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [le_div_iff₀ (by linarith)]
        have := geom_sum_mul q N
        have hp : 0 ≤ q ^ N := pow_nonneg hq0 N
        nlinarith
    _ = L / (1 - q) := by ring

lemma two_mul_pred_lt_factorial (k : ℕ) (hk : 3 ≤ k) : 2 * (k - 1) < k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    have h1 : k + 2 ≤ k.factorial := by omega
    nlinarith

lemma q_lt_one (k : ℕ) (hk : 3 ≤ k) : 2 * ((k : ℚ) - 1) / k.factorial < 1 := by
  have h := two_mul_pred_lt_factorial k hk
  have hk1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [div_lt_one (by positivity), ← hk1]
  exact_mod_cast h

theorem tail_closed_form (k : ℕ) (hk : 3 ≤ k) :
    (2 / (k.factorial : ℚ)) ^ 2 * (2 * (k : ℚ) - 2) / (1 - 2 * ((k : ℚ) - 1) / k.factorial) =
      8 * ((k : ℚ) - 1) / (k.factorial * (k.factorial - 2 * ((k : ℚ) - 1))) := by
  have hq := q_lt_one k hk
  have hf : (0 : ℚ) < k.factorial := by positivity
  have hden : (0 : ℚ) < k.factorial - 2 * ((k : ℚ) - 1) := by
    rw [div_lt_one hf] at hq; linarith
  have h1 : 1 - 2 * ((k : ℚ) - 1) / k.factorial =
      (k.factorial - 2 * ((k : ℚ) - 1)) / k.factorial := by
    field_simp
  rw [h1]
  field_simp
  ring

theorem refined_tail_closed_form (k : ℕ) (hk : 3 ≤ k) (r : ℚ) :
    r * (2 / (k.factorial : ℚ)) * (2 * (k : ℚ) - 2) / (1 - 2 * ((k : ℚ) - 1) / k.factorial) =
      4 * ((k : ℚ) - 1) * r / (k.factorial - 2 * ((k : ℚ) - 1)) := by
  have hq := q_lt_one k hk
  have hf : (0 : ℚ) < k.factorial := by positivity
  have hden : (0 : ℚ) < k.factorial - 2 * ((k : ℚ) - 1) := by
    rw [div_lt_one hf] at hq; linarith
  have h1 : 1 - 2 * ((k : ℚ) - 1) / k.factorial =
      (k.factorial - 2 * ((k : ℚ) - 1)) / k.factorial := by
    field_simp
  rw [h1]
  field_simp
  ring

theorem tail_partial_le (t : ℕ → ℚ) (c q : ℚ) (hc : 0 ≤ c) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (L d₀ : ℕ) (hL : 0 < L) (hb : ∀ j, |t (d₀ + j)| ≤ c * q ^ (j / L)) (N : ℕ) :
    ∑ j ∈ range N, |t (d₀ + j)| ≤ c * L / (1 - q) := by
  calc ∑ j ∈ range N, |t (d₀ + j)| ≤ ∑ j ∈ range N, c * q ^ (j / L) := sum_le_sum fun j _ => hb j
    _ = c * ∑ j ∈ range N, q ^ (j / L) := by rw [mul_sum]
    _ ≤ c * (L / (1 - q)) := mul_le_mul_of_nonneg_left (block_sum_le q hq0 hq1 L hL N) hc
    _ = c * L / (1 - q) := by ring

end Rotation
