import Szalay.Lemma5

/-!
# Szalay, Lemmas 6 and 7

* `lemma6`: if `2 ≤ m < n` and `2^n + 2^m + 1 = x^2`, then `x = 2^(m-1) r ± 1` with `r` odd.
* `lemma7`: if `m < n < 2m - 2` and `2^n + 2^m + 1 = x^2`, then `(n, m, x) = (5, 4, 7)`.
* `no_sol_two_mul_sub_one`: `2^(2m-1) + 2^m + 1 = x^2` has no solution with `m ≥ 2`.
  Szalay derives the case `m = 2r` of this from the parametrization of the Pythagorean
  triples `(a, a + 1, c)` by Pell numbers (his Lemma 9). Here it follows from Lemma 6 and a
  size estimate, in the same way as Lemma 7.
-/

namespace Szalay

/-- If `x^2 = 2^m O + 1` with `O` odd and `m ≥ 2`, then `x = 2^(m-1) r ± 1` with `r` odd. -/
theorem sq_form (x m O : ℕ) (hm : 2 ≤ m) (hO : Odd O) (h : x ^ 2 = 2 ^ m * O + 1) :
    ∃ r, Odd r ∧ (x = 2 ^ (m - 1) * r + 1 ∨ x + 1 = 2 ^ (m - 1) * r) := by
  obtain ⟨B, rfl⟩ : ∃ B, x = 2 * B + 1 := by
    have h1 : Odd (2 ^ m * O + 1) :=
      ((Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right O).add_one
    rw [← h] at h1
    exact (Nat.odd_pow_iff (by norm_num)).mp h1
  have h4 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show m = (m - 2) + 2 by omega, pow_add]; norm_num; ring
  have key : B * (B + 1) = 2 ^ (m - 2) * O := by
    rw [h4] at h
    nlinarith
  have h12 : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rcases Nat.even_or_odd B with hBe | hBo
  · -- `B + 1` is odd, so `2^(m-2)` divides `B`.
    have hdvd : 2 ^ (m - 2) ∣ B :=
      (coprime_two_pow_of_odd hBe.add_one _).dvd_of_dvd_mul_right ⟨O, key⟩
    obtain ⟨c, hc⟩ := hdvd
    have hcO : c * (B + 1) = O := by
      have hpos : 0 < 2 ^ (m - 2) := by positivity
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [← key, hc]; ring
    refine ⟨c, ?_, Or.inl ?_⟩
    · rw [← hcO] at hO; exact (Nat.odd_mul.mp hO).1
    · rw [hc, ← h12]; ring
  · -- `B` is odd, so `2^(m-2)` divides `B + 1`.
    have hdvd : 2 ^ (m - 2) ∣ B + 1 :=
      (coprime_two_pow_of_odd hBo _).dvd_of_dvd_mul_left ⟨O, key⟩
    obtain ⟨c, hc⟩ := hdvd
    have hcO : B * c = O := by
      have hpos : 0 < 2 ^ (m - 2) := by positivity
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [← key, hc]; ring
    refine ⟨c, ?_, Or.inr ?_⟩
    · rw [← hcO] at hO; exact (Nat.odd_mul.mp hO).2
    · rw [← h12]
      calc 2 * B + 1 + 1 = 2 * (B + 1) := by ring
        _ = 2 * 2 ^ (m - 2) * c := by rw [hc]; ring

/-- **Szalay, Lemma 6.** -/
theorem lemma6 (n m x : ℕ) (hm : 2 ≤ m) (hmn : m < n) (h : 2 ^ n + 2 ^ m + 1 = x ^ 2) :
    ∃ r, Odd r ∧ (x = 2 ^ (m - 1) * r + 1 ∨ x + 1 = 2 ^ (m - 1) * r) := by
  apply sq_form x m (2 ^ (n - m) + 1) hm
  · have : Even (2 ^ (n - m)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact this.add_one
  · rw [← h, mul_add, ← pow_add, show m + (n - m) = n by omega]; ring

/-- **Szalay, Lemma 7.** -/
theorem lemma7 (n m x : ℕ) (hmn : m < n) (hn : n < 2 * m - 2)
    (h : 2 ^ n + 2 ^ m + 1 = x ^ 2) : n = 5 ∧ m = 4 ∧ x = 7 := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨r, hr, hx⟩ := lemma6 n m x (by omega) hmn h
  have hr1 : 1 ≤ r := hr.pos
  -- Notation: `P = 2^(m-3)`, so `2^(m-1) = 4P`, `2^m = 8P`, `2^n ≤ 2^(2m-3) = 8P^2`.
  set P := 2 ^ (m - 3) with hPdef
  have hP2 : 2 ≤ P := by
    rw [hPdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ (m - 1) = 4 * P := by
    rw [hPdef, show m - 1 = (m - 3) + 2 by omega, pow_add]; norm_num; ring
  have e2 : 2 ^ m = 8 * P := by
    rw [hPdef, show m = (m - 3) + 3 by omega, pow_add]; norm_num; ring
  have hQ : 2 ^ n ≤ 8 * P ^ 2 := by
    have : 2 ^ n ≤ 2 ^ (2 * (m - 3) + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add, pow_mul', ← hPdef] at this
    linarith
  rw [e2] at h
  rw [e1] at hx
  generalize hQdef : 2 ^ n = Q at h hQ
  rcases hx with hx | hx
  · -- `x = 4 P r + 1` is too large.
    exfalso
    rw [hx] at h
    have hP0 : 0 < P ^ 2 := pow_pos (by omega) 2
    have h1 : P ^ 2 * 1 ≤ P ^ 2 * r ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hr1)
    have h2 : P * 1 ≤ P * r := Nat.mul_le_mul_left _ hr1
    nlinarith
  · -- `x = 4 P r - 1` forces `r = 1` and `P = 2`.
    have hZ : (16 : ℤ) * P ^ 2 * r ^ 2 = Q + 8 * P + 8 * P * r := by
      have hx' : (x : ℤ) = 4 * P * r - 1 := by
        have : ((x + 1 : ℕ) : ℤ) = ((4 * P * r : ℕ) : ℤ) := by rw [hx]
        push_cast at this; linarith
      have h' : ((Q + 8 * P + 1 : ℕ) : ℤ) = ((x ^ 2 : ℕ) : ℤ) := by rw [h]
      push_cast at h'
      rw [hx'] at h'
      nlinarith
    have hQZ : (Q : ℤ) ≤ 8 * P ^ 2 := by exact_mod_cast hQ
    have hPZ : (2 : ℤ) ≤ P := by exact_mod_cast hP2
    have hrZ : (1 : ℤ) ≤ r := by exact_mod_cast hr1
    have hr_eq : (r : ℤ) = 1 := by
      by_contra hne
      have hr2 : (2 : ℤ) ≤ r := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr hPZ) (sub_nonneg.mpr hr2)]
    have hP_eq : (P : ℤ) = 2 := by
      rw [hr_eq] at hZ
      nlinarith
    have hr' : r = 1 := by exact_mod_cast hr_eq
    have hP' : P = 2 := by exact_mod_cast hP_eq
    have hm' : m = 4 := by
      have : 2 ^ (m - 3) = 2 ^ 1 := by rw [← hPdef, hP']; norm_num
      have := Nat.pow_right_injective (le_refl 2) this
      omega
    have hQ' : Q = 32 := by
      rw [hr_eq, hP_eq] at hZ
      have : (Q : ℤ) = 32 := by linarith
      exact_mod_cast this
    have hn' : n = 5 := by
      have : 2 ^ n = 2 ^ 5 := by rw [hQdef, hQ']; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    refine ⟨hn', hm', ?_⟩
    rw [hr', hP'] at hx
    omega

/-- `2^(2m-1) + 2^m + 1 = x^2` has no solution with `m ≥ 2`. -/
theorem no_sol_two_mul_sub_one (m x : ℕ) (hm : 2 ≤ m)
    (h : 2 ^ (2 * m - 1) + 2 ^ m + 1 = x ^ 2) : False := by
  obtain ⟨r, hr, hx⟩ := lemma6 (2 * m - 1) m x hm (by omega) h
  have hr1 : 1 ≤ r := hr.pos
  -- Notation: `P = 2^(m-2)`, so `2^(m-1) = 2P`, `2^m = 4P`, `2^(2m-1) = 8P^2`.
  set P := 2 ^ (m - 2) with hPdef
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have e1 : 2 ^ (m - 1) = 2 * P := by
    rw [hPdef, show m - 1 = (m - 2) + 1 by omega, pow_add]; ring
  have e2 : 2 ^ m = 4 * P := by
    rw [hPdef, show m = (m - 2) + 2 by omega, pow_add]; norm_num; ring
  have e3 : 2 ^ (2 * m - 1) = 8 * P ^ 2 := by
    rw [hPdef, show 2 * m - 1 = 2 * (m - 2) + 3 by omega, pow_add, pow_mul']; ring
  rw [e2, e3] at h
  rw [e1] at hx
  have hPZ : (1 : ℤ) ≤ P := by exact_mod_cast hP1
  have hrZ : (1 : ℤ) ≤ r := by exact_mod_cast hr1
  have hZ : (8 : ℤ) * P ^ 2 + 4 * P + 1 = (x : ℤ) ^ 2 := by exact_mod_cast h
  rcases hx with hx | hx
  · -- `x = 2 P r + 1`: then `P r^2 + r = 2P + 1`, impossible.
    have hx' : (x : ℤ) = 2 * P * r + 1 := by rw [hx]; push_cast; ring
    rw [hx'] at hZ
    have e : (P : ℤ) * r ^ 2 + r = 2 * P + 1 := by
      have h4P : (0 : ℤ) < 4 * P := by linarith
      have : (4 * P : ℤ) * (P * r ^ 2 + r) = (4 * P) * (2 * P + 1) := by nlinarith
      exact mul_left_cancel₀ h4P.ne' this
    rcases (by omega : (r : ℤ) = 1 ∨ 2 ≤ (r : ℤ)) with h1 | h2
    · rw [h1] at e; nlinarith
    · nlinarith
  · -- `x = 2 P r - 1`: then `P r^2 - r = 2P + 1`, impossible.
    have hx' : (x : ℤ) = 2 * P * r - 1 := by
      have : ((x + 1 : ℕ) : ℤ) = ((2 * P * r : ℕ) : ℤ) := by rw [hx]
      push_cast at this; linarith
    rw [hx'] at hZ
    have e : (P : ℤ) * r ^ 2 - r = 2 * P + 1 := by
      have h4P : (0 : ℤ) < 4 * P := by linarith
      have : (4 * P : ℤ) * (P * r ^ 2 - r) = (4 * P) * (2 * P + 1) := by nlinarith
      exact mul_left_cancel₀ h4P.ne' this
    rcases (by omega : (r : ℤ) = 1 ∨ (r : ℤ) = 2 ∨ 3 ≤ (r : ℤ)) with h1 | h2 | h3
    · rw [h1] at e; nlinarith
    · rw [h2] at e; omega
    · nlinarith

end Szalay
