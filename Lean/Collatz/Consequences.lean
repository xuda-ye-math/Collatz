import Collatz.Theorems

/-!
# Corollary 1 (iii), (iv) and Theorem 4 (i)

* `corollary1_iii`, `corollary1_iv`: an orbit under `Q_-` containing an odd term `2^m - 1`, or
  under `Q_+` containing an odd term `2^m + 1`, with `m ≥ 3`, tends to infinity.
* `theorem4_i`: under `Q_-`, an odd term `y > 1` that divides no `2^m + 1` (`m ≥ 1`) forces
  the orbit to infinity. The proof uses only Lemma 2 (i) of the paper (`y` divides all later
  terms) and the odd step, not Szalay's theorem.
-/

namespace Collatz

open Filter

/-- An orbit tends to infinity once a later term has an orbit that tends to infinity. -/
theorem tendsto_of_later (F : ℕ → ℕ) (x₀ i : ℕ)
    (h : Tendsto (fun n => F^[n] (F^[i] x₀)) atTop atTop) :
    Tendsto (fun n => F^[n] x₀) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat i]
  refine h.congr (fun n => ?_)
  rw [Function.iterate_add_apply]

/-- `2^m - 1 ≡ 3 (mod 4)` for `m ≥ 2`. -/
theorem pow_sub_one_mod_four (m : ℕ) (hm : 2 ≤ m) : (2 ^ m - 1) % 4 = 3 := by
  have e : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have : 1 ≤ 2 ^ (m - 2) := Nat.one_le_two_pow
  rw [e]; omega

/-- `2^m + 1 ≡ 1 (mod 4)` for `m ≥ 2`. -/
theorem pow_add_one_mod_four (m : ℕ) (hm : 2 ≤ m) : (2 ^ m + 1) % 4 = 1 := by
  have e : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  rw [e]; omega

/-- **Corollary 1 (iii).** -/
theorem corollary1_iii (x₀ i m : ℕ) (hm : 3 ≤ m) (h : Qm^[i] x₀ = 2 ^ m - 1) :
    Tendsto (fun n => Qm^[n] x₀) atTop atTop := by
  apply tendsto_of_later Qm x₀ i
  rw [h]
  apply theorem1_iii
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h4 := pow_sub_one_mod_four m (by omega)
  have hodd : (2 ^ m - 1) % 2 = 1 := by omega
  rintro (h0 | ⟨l, hl⟩ | ⟨l, m', hm', hl⟩)
  · omega
  · rw [hl] at hodd
    have := eq_zero_of_odd_two_pow_mul (y := 1) (by rw [mul_one]; exact hodd)
    subst this
    simp at hl; omega
  · rw [hl] at hodd
    have := eq_zero_of_odd_two_pow_mul hodd
    subst this
    rw [pow_zero, one_mul] at hl
    rcases (by omega : m' = 1 ∨ 2 ≤ m') with h1 | h2
    · subst h1; omega
    · have := pow_add_one_mod_four m' h2
      omega

/-- **Corollary 1 (iv).** -/
theorem corollary1_iv (x₀ i m : ℕ) (hm : 3 ≤ m) (h : Qp^[i] x₀ = 2 ^ m + 1) :
    Tendsto (fun n => Qp^[n] x₀) atTop atTop := by
  apply tendsto_of_later Qp x₀ i
  rw [h]
  apply theorem2_iv
  have h4 := pow_add_one_mod_four m (by omega)
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hodd : (2 ^ m + 1) % 2 = 1 := by omega
  rintro (h0 | ⟨l, m', hm', hl⟩ | ⟨l, hl⟩)
  · omega
  · rw [hl] at hodd
    have := eq_zero_of_odd_two_pow_mul hodd
    subst this
    rw [pow_zero, one_mul] at hl
    rcases (by omega : m' = 1 ∨ 2 ≤ m') with h1 | h2
    · subst h1; omega
    · have := pow_sub_one_mod_four m' h2
      omega
  · rw [hl, mul_comm] at hodd
    have := eq_zero_of_odd_two_pow_mul hodd
    subst this
    simp at hl; omega

/-- **Theorem 4 (i).** -/
theorem theorem4_i (x₀ i y : ℕ) (hy : y % 2 = 1) (hy1 : 1 < y) (hxy : Qm^[i] x₀ = y)
    (hndvd : ∀ m, 1 ≤ m → ¬ y ∣ 2 ^ m + 1) :
    Tendsto (fun n => Qm^[n] x₀) atTop atTop := by
  apply tendsto_of_later Qm x₀ i
  rw [hxy]
  apply tendsto_of_oddStep Qm (fun n hn => Qm_even hn) (fun z => 3 ≤ z ∧ y ∣ z)
    (fun z hz => by have := hz.1; omega) _ y 0 y (by simp) hy ⟨by omega, dvd_rfl⟩
  rintro z hz ⟨h3, hyz⟩
  obtain ⟨j, k, hj, hk, hzk⟩ := decomp_sub_one hz h3
  have hk3 : 3 ≤ k := by
    have : k ≠ 1 := by
      rintro rfl
      exact hndvd j hj (by rw [show 2 ^ j + 1 = z by rw [hzk]; ring]; exact hyz)
    omega
  exact ⟨j - 1, k * z, Qm_step z j k hj hzk, odd_mul' hk hz,
    ⟨by nlinarith, Dvd.dvd.mul_left hyz k⟩, by nlinarith⟩

/-- For `m ≥ 3`, `2^m - 1` divides no `2^m' + 1`: the residues of the powers of `2` modulo
`2^m - 1` are `2^0, …, 2^(m-1)`, and none of them is `-1`. -/
theorem not_dvd_two_pow_add_one (m m' : ℕ) (hm : 3 ≤ m) : ¬ (2 ^ m - 1) ∣ 2 ^ m' + 1 := by
  intro hd
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hmod : 2 ^ m ≡ 1 [MOD 2 ^ m - 1] :=
    ((Nat.modEq_iff_dvd' (by omega : 1 ≤ 2 ^ m)).mpr dvd_rfl).symm
  have e : 2 ^ m' = (2 ^ m) ^ (m' / m) * 2 ^ (m' % m) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hpow : 2 ^ m' ≡ 2 ^ (m' % m) [MOD 2 ^ m - 1] := by
    rw [e]; simpa using (hmod.pow (m' / m)).mul_right (2 ^ (m' % m))
  have hd' : (2 ^ m - 1) ∣ 2 ^ (m' % m) + 1 :=
    Nat.modEq_zero_iff_dvd.mp ((hpow.add_right 1).symm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  have hr : m' % m ≤ m - 1 := by have := Nat.mod_lt m' (show 0 < m by omega); omega
  have h1 : 2 ^ (m' % m) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) hr
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have := Nat.le_of_dvd (by positivity) hd'
  omega

/-- **Corollary 1 (iii), without Szalay's theorem** (the paper's Section 5): it follows from
Theorem 4 (i). -/
theorem corollary1_iii_elementary (x₀ i m : ℕ) (hm : 3 ≤ m) (h : Qm^[i] x₀ = 2 ^ m - 1) :
    Tendsto (fun n => Qm^[n] x₀) atTop atTop := by
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact theorem4_i x₀ i (2 ^ m - 1) (by have := pow_sub_one_mod_four m (by omega); omega)
    (by omega) h (fun m' _ => not_dvd_two_pow_add_one m m' hm)

end Collatz
