import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Rotation

open Finset

noncomputable def f (k d : ℕ) : ℚ := (Nat.centralBinom d : ℚ) * k.factorial / (k + d).factorial

noncomputable def S (k : ℕ) : ℚ := (∑ d ∈ Ico 2 (k - 1), f k d) + 3 / 2 * f k (k - 1)

noncomputable def H (k : ℕ) : ℚ := 8 * ((k : ℚ) - 1) / ((k.factorial : ℚ) - 2 * ((k : ℚ) - 1))

def cstar : ℚ := 3106970325 / 3245660803

lemma cstar_eq : (33 : ℚ) / 35 + 3 / 10 * (4 / 11) ^ 5 + 504 / 40306 = cstar := by
  norm_num [cstar]

lemma cstar_lt_one : cstar < 1 := by norm_num [cstar]

lemma one_sub_cstar : 1 - cstar = 138690478 / 3245660803 := by norm_num [cstar]

lemma f_nonneg (k d : ℕ) : 0 ≤ f k d := by unfold f; positivity

lemma f_two (k : ℕ) : f k 2 = 6 / (((k : ℚ) + 1) * ((k : ℚ) + 2)) := by
  unfold f
  have h1 : (k + 2).factorial = (k + 2) * ((k + 1) * k.factorial) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
  rw [h1]
  have : (Nat.centralBinom 2 : ℚ) = 6 := by norm_num [Nat.centralBinom, Nat.choose]
  rw [this]
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma f_succ (k d : ℕ) :
    f k (d + 1) * (((d : ℚ) + 1) * ((k : ℚ) + d + 1)) = f k d * (2 * (2 * (d : ℚ) + 1)) := by
  unfold f
  have hc : ((d + 1 : ℕ) : ℚ) * (Nat.centralBinom (d + 1) : ℚ) =
      2 * (2 * (d : ℚ) + 1) * Nat.centralBinom d := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ d
  have hfact : ((k + (d + 1)).factorial : ℚ) = ((k : ℚ) + d + 1) * (k + d).factorial := by
    rw [show k + (d + 1) = (k + d) + 1 by ring, Nat.factorial_succ]
    push_cast; ring
  rw [hfact]
  have h1 : ((k + d).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (k : ℚ) + d + 1 ≠ 0 := by positivity
  push_cast at hc
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero h2 h1) h1]
  linear_combination ((k.factorial : ℚ) * ((k : ℚ) + d + 1) * (k + d).factorial) * hc

lemma f_succ_le (k d : ℕ) (hd : 1 ≤ d) (hk1 : 1 ≤ k) : f k (d + 1) ≤ 4 / ((k : ℚ) + 3) * f k d := by
  have h := f_succ k d
  have hpos : (0 : ℚ) < ((d : ℚ) + 1) * ((k : ℚ) + d + 1) := by positivity
  have hfd := f_nonneg k d
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hk : (1 : ℚ) ≤ k := by exact_mod_cast hk1
  have key : f k (d + 1) = f k d * (2 * (2 * (d : ℚ) + 1) / (((d : ℚ) + 1) * ((k : ℚ) + d + 1))) := by
    rw [mul_div_assoc', ← h]; field_simp
  have hratio : 2 * (2 * (d : ℚ) + 1) / (((d : ℚ) + 1) * ((k : ℚ) + d + 1)) ≤ 4 / ((k : ℚ) + 3) := by
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hd') (le_trans zero_le_one hd')]
  rw [key, mul_comm (4 / ((k : ℚ) + 3))]
  exact mul_le_mul_of_nonneg_left hratio hfd

lemma f_le_geom (k j : ℕ) (hk1 : 1 ≤ k) : f k (2 + j) ≤ f k 2 * (4 / ((k : ℚ) + 3)) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := f_succ_le k (2 + j) (by omega) hk1
    rw [show 2 + (j + 1) = 2 + j + 1 by ring, pow_succ]
    have hr : (0 : ℚ) ≤ 4 / ((k : ℚ) + 3) := by positivity
    calc f k (2 + j + 1) ≤ 4 / ((k : ℚ) + 3) * f k (2 + j) := this
      _ ≤ 4 / ((k : ℚ) + 3) * (f k 2 * (4 / ((k : ℚ) + 3)) ^ j) :=
          mul_le_mul_of_nonneg_left ih hr
      _ = _ := by ring

lemma geom_le {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ j ∈ range n, r ^ j ≤ 1 / (1 - r) := by
  rw [le_div_iff₀ (by linarith)]
  have := geom_sum_mul r n
  have hp : 0 ≤ r ^ n := pow_nonneg h0 n
  nlinarith

lemma S_le (k : ℕ) (hk : 4 ≤ k) :
    S k ≤ f k 2 / (1 - 4 / ((k : ℚ) + 3)) + 1 / 2 * (f k 2 * (4 / ((k : ℚ) + 3)) ^ (k - 3)) := by
  set r : ℚ := 4 / ((k : ℚ) + 3) with hr
  have hk' : (4 : ℚ) ≤ k := by exact_mod_cast hk
  have r0 : 0 ≤ r := by positivity
  have r1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
  have hsplit : S k = (∑ d ∈ Ico 2 k, f k d) + 1 / 2 * f k (k - 1) := by
    unfold S
    have : Ico 2 k = insert (k - 1) (Ico 2 (k - 1)) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    rw [this, sum_insert (by simp)]
    ring
  rw [hsplit]
  have hsum : ∑ d ∈ Ico 2 k, f k d = ∑ j ∈ range (k - 2), f k (2 + j) :=
    sum_Ico_eq_sum_range _ _ _
  have hlast : f k (k - 1) ≤ f k 2 * r ^ (k - 3) := by
    have := f_le_geom k (k - 3) (by omega)
    rwa [show 2 + (k - 3) = k - 1 by omega] at this
  have hgeom : ∑ j ∈ range (k - 2), f k (2 + j) ≤ f k 2 / (1 - r) := by
    calc ∑ j ∈ range (k - 2), f k (2 + j) ≤ ∑ j ∈ range (k - 2), f k 2 * r ^ j :=
          sum_le_sum fun j _ => f_le_geom k j (by omega)
      _ = f k 2 * ∑ j ∈ range (k - 2), r ^ j := by rw [mul_sum]
      _ ≤ f k 2 * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (geom_le r0 r1 _) (f_nonneg k 2)
      _ = _ := by ring
  rw [hsum]
  linarith

lemma S_bound (k : ℕ) (hk : 8 ≤ k) :
    ((k : ℚ) + 1) * S k ≤ 33 / 35 + 3 / 10 * (4 / 11) ^ 5 := by
  have hk' : (8 : ℚ) ≤ k := by exact_mod_cast hk
  have hS := S_le k (by omega)
  rw [f_two] at hS
  set r : ℚ := 4 / ((k : ℚ) + 3) with hr
  have r0 : 0 ≤ r := by positivity
  have r411 : r ≤ 4 / 11 := by
    rw [hr]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hpow : r ^ (k - 3) ≤ (4 / 11) ^ 5 := by
    calc r ^ (k - 3) ≤ r ^ 5 := pow_le_pow_of_le_one r0 (by linarith) (by omega)
      _ ≤ (4 / 11) ^ 5 := pow_le_pow_left₀ r0 r411 5

  have e1 : ((k : ℚ) + 1) * (6 / (((k : ℚ) + 1) * ((k : ℚ) + 2)) / (1 - r)) =
      6 * ((k : ℚ) + 3) / (((k : ℚ) + 2) * ((k : ℚ) - 1)) := by
    have h1r : 1 - r = ((k : ℚ) - 1) / ((k : ℚ) + 3) := by
      rw [hr]; field_simp; ring
    have : (k : ℚ) - 1 ≠ 0 := by linarith
    rw [h1r]
    field_simp
  have t1 : 6 * ((k : ℚ) + 3) / (((k : ℚ) + 2) * ((k : ℚ) - 1)) ≤ 33 / 35 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  have e2 : ((k : ℚ) + 1) * (1 / 2 * (6 / (((k : ℚ) + 1) * ((k : ℚ) + 2)) * r ^ (k - 3))) =
      3 / ((k : ℚ) + 2) * r ^ (k - 3) := by
    field_simp
    ring
  have t2 : 3 / ((k : ℚ) + 2) * r ^ (k - 3) ≤ 3 / 10 * (4 / 11) ^ 5 := by
    have : 3 / ((k : ℚ) + 2) ≤ 3 / 10 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    exact mul_le_mul this hpow (pow_nonneg r0 _) (by norm_num)
  have hk1 : (0 : ℚ) ≤ (k : ℚ) + 1 := by positivity
  calc ((k : ℚ) + 1) * S k
      ≤ ((k : ℚ) + 1) * (6 / (((k : ℚ) + 1) * ((k : ℚ) + 2)) / (1 - r)
          + 1 / 2 * (6 / (((k : ℚ) + 1) * ((k : ℚ) + 2)) * r ^ (k - 3))) :=
        mul_le_mul_of_nonneg_left hS hk1
    _ = 6 * ((k : ℚ) + 3) / (((k : ℚ) + 2) * ((k : ℚ) - 1)) + 3 / ((k : ℚ) + 2) * r ^ (k - 3) := by
        rw [mul_add, e1, e2]
    _ ≤ _ := add_le_add t1 t2

lemma fact_bound (k : ℕ) (hk : 8 ≤ k) :
    8 * 40306 * ((k : ℚ) ^ 2 - 1) + 1008 * ((k : ℚ) - 1) ≤ 504 * (k.factorial : ℚ) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    have hk' : (8 : ℚ) ≤ k := by exact_mod_cast hk
    rw [Nat.factorial_succ]
    push_cast
    nlinarith

lemma H_bound (k : ℕ) (hk : 8 ≤ k) : ((k : ℚ) + 1) * H k ≤ 504 / 40306 := by
  have hk' : (8 : ℚ) ≤ k := by exact_mod_cast hk
  have hf := fact_bound k hk
  have hden : 0 < (k.factorial : ℚ) - 2 * ((k : ℚ) - 1) := by nlinarith
  unfold H
  rw [← mul_div_assoc, div_le_div_iff₀ hden (by norm_num)]
  nlinarith

theorem uniform (k : ℕ) (hk : 8 ≤ k) : ((k : ℚ) + 1) * (S k + H k) ≤ cstar := by
  rw [mul_add, ← cstar_eq]
  have := S_bound k hk
  have := H_bound k hk
  linarith

theorem D_pos (k : ℕ) (hk : 8 ≤ k) (D : ℚ)
    (hD : (k.factorial : ℚ) * D ≥ 1 / ((k : ℚ) + 1) - S k - H k) :
    D ≥ 138690478 / (3245660803 * ((k : ℚ) + 1) * k.factorial) ∧ 0 < D := by
  have hu := uniform k hk
  have hk1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hfac : (0 : ℚ) < k.factorial := by positivity
  have h1 : S k + H k ≤ cstar / ((k : ℚ) + 1) := by
    rw [le_div_iff₀ hk1]; linarith
  have h2 : (k.factorial : ℚ) * D ≥ (1 - cstar) / ((k : ℚ) + 1) := by
    have : (1 - cstar) / ((k : ℚ) + 1) = 1 / ((k : ℚ) + 1) - cstar / ((k : ℚ) + 1) := by ring
    linarith
  rw [one_sub_cstar] at h2
  have h3 : D ≥ 138690478 / (3245660803 * ((k : ℚ) + 1) * k.factorial) := by
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    rw [ge_iff_le, div_le_iff₀ hk1] at h2
    nlinarith
  refine ⟨h3, lt_of_lt_of_le ?_ h3⟩
  positivity

lemma sum_linear (M : ℕ) (hM : 0 < M) :
    ∑ m ∈ range M, (1 - ((m : ℚ) + 1) / M) = ((M : ℚ) - 1) / 2 := by
  have key : ∀ N : ℕ, ∑ m ∈ range N, ((m : ℚ) + 1) = (N : ℚ) * (N + 1) / 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ihN => rw [sum_range_succ, ihN]; push_cast; ring
  have hM' : (M : ℚ) ≠ 0 := by positivity
  simp_rw [div_eq_mul_inv]
  rw [sum_sub_distrib, sum_const, card_range, ← sum_mul, key]
  field_simp
  ring

lemma expected_time_bound (k : ℕ) (hk : 1 ≤ k) (F : ℚ)
    (hF : F ≥ k + (((k.factorial : ℚ) / 2) - 1) / 2) : F ≥ (k.factorial : ℚ) / 4 := by
  have : (1 : ℚ) ≤ k := by exact_mod_cast hk
  linarith

theorem advantage_bound (k : ℕ) (hk : 8 ≤ k) (F D : ℚ) (hF : F ≥ (k.factorial : ℚ) / 4)
    (hD : (k.factorial : ℚ) * D ≥ 1 / ((k : ℚ) + 1) - S k - H k) :
    F * D / 2 ≥ 69345239 / (12982643212 * ((k : ℚ) + 1)) := by
  obtain ⟨h1, h2⟩ := D_pos k hk D hD
  have hfac : (0 : ℚ) < k.factorial := by positivity
  have hk1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have e : 69345239 / (12982643212 * ((k : ℚ) + 1)) =
      (k.factorial : ℚ) / 4 * (138690478 / (3245660803 * ((k : ℚ) + 1) * k.factorial)) / 2 := by
    field_simp
    ring
  rw [e]
  have hc : (0 : ℚ) ≤ 138690478 / (3245660803 * ((k : ℚ) + 1) * k.factorial) := by positivity
  have := mul_le_mul hF h1 hc (by linarith)
  linarith

end Rotation
