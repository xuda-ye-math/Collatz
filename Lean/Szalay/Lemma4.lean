import Szalay.Beukers
import Szalay.SqrtCheck

/-!
# Szalay, Lemma 4

All solutions of `0 < |2^n - x^2| < 4` in positive integers are
`(n, x) = (1,1), (2,1), (3,3), (1,2)`. Szalay's proof: Lemma 1 gives `n < 22`, and a check of
the remaining values of `n` gives the list.
-/

namespace Szalay

/-- Szalay's Lemma 1 in integer form: `2^n < 2^18 D^2`. -/
theorem two_pow_lt_of_cor2 (D : ℤ) (n : ℕ) (x : ℤ) (hD : D ≠ 0) (hDlt : |D| < 2 ^ 96)
    (h : (2 : ℤ) ^ n + D = x ^ 2) : (2 : ℤ) ^ n < 2 ^ 18 * D ^ 2 := by
  have hb := beukers_cor2 D n x hD hDlt h
  have hpos : 0 < |(D : ℝ)| := abs_pos.mpr (by exact_mod_cast hD)
  have hlt : (2 : ℝ) ^ (n : ℝ) < (2 : ℝ) ^ (18 + 2 * Real.logb 2 |(D : ℝ)|) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hb
  have hrhs : (2 : ℝ) ^ (18 + 2 * Real.logb 2 |(D : ℝ)|) = 2 ^ 18 * (D : ℝ) ^ 2 := by
    rw [Real.rpow_add (by norm_num), mul_comm (2 : ℝ) (Real.logb 2 _),
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hpos]
    norm_num
  rw [hrhs, Real.rpow_natCast] at hlt
  exact_mod_cast hlt

/-- The solutions listed in Szalay's Lemma 4. -/
def L4 : List (ℕ × ℕ) := [(1, 1), (2, 1), (3, 3), (1, 2)]

/-- The roots `x` with `(n, x) ∈ L4`. -/
def L4roots (n : ℕ) : List ℕ := (L4.filter (fun p => p.1 == n)).map Prod.snd

theorem mem_L4_of_mem_roots {n x : ℕ} (h : x ∈ L4roots n) : (n, x) ∈ L4 := by
  simp only [L4roots, List.mem_map, List.mem_filter, beq_iff_eq] at h
  obtain ⟨⟨a, b⟩, ⟨hm, ha⟩, hb⟩ := h
  simp only at ha hb
  subst ha hb
  exact hm

/-- The finite check of Szalay's Lemma 4 for `1 ≤ n ≤ 21`. -/
def lemma4Check : Bool :=
  (List.range 22).all fun n => decide (n = 0) || [1, 2, 3].all fun d =>
    sqTest (2 ^ n + d) (L4roots n) && (decide (2 ^ n ≤ d) || sqTest (2 ^ n - d) (L4roots n))

theorem lemma4Check_eq : lemma4Check = true := by decide

/-- **Szalay, Lemma 4.** -/
theorem lemma4 (n x : ℕ) (hn : 0 < n) (hx : 0 < x) (h0 : (2 : ℤ) ^ n ≠ (x : ℤ) ^ 2)
    (h4 : |(2 : ℤ) ^ n - (x : ℤ) ^ 2| < 4) : (n, x) ∈ L4 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h4
  -- Lemma 1 gives `n < 22`.
  have hn22 : n < 22 := by
    have hD : (x : ℤ) ^ 2 - 2 ^ n ≠ 0 := sub_ne_zero.mpr (Ne.symm h0)
    have habs : |(x : ℤ) ^ 2 - 2 ^ n| < 2 ^ 96 := by
      rw [abs_lt]; constructor <;> linarith
    have h2 := two_pow_lt_of_cor2 _ n x hD habs (by ring)
    have hsq : ((x : ℤ) ^ 2 - 2 ^ n) ^ 2 ≤ 9 := by nlinarith
    have h22 : (2 : ℤ) ^ n < 2 ^ 22 := by nlinarith
    have : (2 : ℕ) ^ n < 2 ^ 22 := by exact_mod_cast h22
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  -- Reduce to the cases `x^2 = 2^n + d` and `x^2 + d = 2^n` with `d ∈ {1, 2, 3}`.
  have hcases : ∃ d ∈ [1, 2, 3], x ^ 2 = 2 ^ n + d ∨ x ^ 2 + d = 2 ^ n := by
    have e1 : ((x ^ 2 : ℕ) : ℤ) = (x : ℤ) ^ 2 := by push_cast; ring
    have e2 : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
    rw [← e1, ← e2] at hlo hhi h0
    generalize x ^ 2 = b at *
    generalize 2 ^ n = a at *
    have : b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b + 1 = a ∨ b + 2 = a ∨ b + 3 = a := by
      omega
    rcases this with h | h | h | h | h | h
    · exact ⟨1, by simp, Or.inl h⟩
    · exact ⟨2, by simp, Or.inl h⟩
    · exact ⟨3, by simp, Or.inl h⟩
    · exact ⟨1, by simp, Or.inr h⟩
    · exact ⟨2, by simp, Or.inr h⟩
    · exact ⟨3, by simp, Or.inr h⟩
  obtain ⟨d, hd, hxd⟩ := hcases
  have hchk := lemma4Check_eq
  simp only [lemma4Check, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at hchk
  rcases hchk n hn22 with h | h
  · omega
  obtain ⟨hplus, hminus⟩ := h d hd
  apply mem_L4_of_mem_roots
  rcases hxd with hxd | hxd
  · exact mem_of_sqTest hplus hxd
  · rcases hminus with hm | hm
    · have : 0 < x ^ 2 := by positivity
      omega
    · exact mem_of_sqTest hm (by omega)

end Szalay
