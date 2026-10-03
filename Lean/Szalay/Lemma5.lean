import Mathlib

/-!
# Szalay, Lemma 5

Let `t ≥ 1`. If `x, y > 1` satisfy `y^2 - 1 = 2^(2t) (x^2 - 1)`, then `t > 1`,
`x = 2^(t-1)` and `y = 2^(2t-1) - 1`. The equation is written without subtraction as
`y^2 + 2^(2t) = 2^(2t) x^2 + 1`.

The proof follows Szalay: `y = 2A + 1`, the coprime factors `A` and `A + 1` of
`A (A + 1) = 2^(2t-2) (x^2 - 1)`, and the comparison of `x^2` with consecutive squares.
-/

namespace Szalay

/-- An odd natural number is coprime to every power of `2`. -/
theorem coprime_two_pow_of_odd {n : ℕ} (h : Odd n) (e : ℕ) : Nat.Coprime (2 ^ e) n :=
  Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr h)

/-- **Szalay, Lemma 5.** -/
theorem lemma5 (t x y : ℕ) (ht : 1 ≤ t) (hx : 1 < x) (hy : 1 < y)
    (h : y ^ 2 + 2 ^ (2 * t) = 2 ^ (2 * t) * x ^ 2 + 1) :
    2 ≤ t ∧ x = 2 ^ (t - 1) ∧ y = 2 ^ (2 * t - 1) - 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hP : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  have h4 : 2 ^ (2 * (s + 1)) = 4 * (2 ^ s) ^ 2 := by ring
  rw [h4] at h
  -- `y` is odd.
  obtain ⟨A, rfl⟩ : ∃ A, y = 2 * A + 1 := by
    have h1 : Odd (4 * (2 ^ s) ^ 2 * x ^ 2 + 1) := ⟨2 * (2 ^ s) ^ 2 * x ^ 2, by ring⟩
    rw [← h] at h1
    have h2 : Even (4 * (2 ^ s) ^ 2) := ⟨2 * (2 ^ s) ^ 2, by ring⟩
    have hy2 : Odd (y ^ 2) := (Nat.odd_add.mp h1).mpr h2
    exact (Nat.odd_pow_iff (by norm_num)).mp hy2
  have hA1 : 1 ≤ A := by omega
  -- `A (A + 1) + P^2 = P^2 x^2` with `P = 2^s`.
  have hP2 : (2 ^ s) ^ 2 = 2 ^ (2 * s) := by ring
  generalize hPdef : 2 ^ s = P at hP h hP2
  have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have key : A * (A + 1) + P ^ 2 = P ^ 2 * x ^ 2 := by nlinarith
  have hdvd : P ^ 2 ∣ A * (A + 1) := by
    refine ⟨x ^ 2 - 1, ?_⟩
    rw [Nat.mul_sub, mul_one]
    omega
  -- `P^2` divides `A` or `A + 1`.
  have hcases : P ^ 2 ∣ A ∨ P ^ 2 ∣ A + 1 := by
    rcases Nat.even_or_odd A with hAe | hAo
    · left
      have hodd : Odd (A + 1) := hAe.add_one
      rw [hP2] at hdvd ⊢
      exact (coprime_two_pow_of_odd hodd _).dvd_of_dvd_mul_right hdvd
    · right
      rw [hP2] at hdvd ⊢
      exact (coprime_two_pow_of_odd hAo _).dvd_of_dvd_mul_left hdvd
  have hPpos : 0 < P ^ 2 := pow_pos (by omega) 2
  rcases hcases with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `A = P^2 k`: then `x^2 = (P k)^2 + k + 1` lies strictly between consecutive squares.
    exfalso
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; omega
      · exact h0
    have e : P ^ 2 * (k * (P ^ 2 * k + 1) + 1) = P ^ 2 * x ^ 2 := by rw [hk] at key; nlinarith
    have e2 : x ^ 2 = (P * k) ^ 2 + k + 1 := by
      have := Nat.eq_of_mul_eq_mul_left hPpos e
      nlinarith
    have hlo : P * k < x := by
      have : (P * k) ^ 2 < x ^ 2 := by omega
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
    have hhi : x < P * k + 1 := by
      have : x ^ 2 < (P * k + 1) ^ 2 := by nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
    omega
  · -- `A + 1 = P^2 k`.
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; omega
      · exact h0
    have hAk : (A : ℤ) = (P : ℤ) ^ 2 * k - 1 := by
      have : ((A + 1 : ℕ) : ℤ) = ((P ^ 2 * k : ℕ) : ℤ) := by rw [hk]
      push_cast at this; linarith
    have keyZ : (A : ℤ) * (A + 1) + (P : ℤ) ^ 2 = (P : ℤ) ^ 2 * x ^ 2 := by exact_mod_cast key
    rw [hAk] at keyZ
    have hPpZ : (0 : ℤ) < (P : ℤ) ^ 2 := pow_pos (by exact_mod_cast (show 0 < P by omega)) 2
    have e2 : (x : ℤ) ^ 2 = ((P : ℤ) * k) ^ 2 - k + 1 := by
      have : (P : ℤ) ^ 2 * ((x : ℤ) ^ 2) = (P : ℤ) ^ 2 * (((P : ℤ) * k) ^ 2 - k + 1) := by
        nlinarith
      exact mul_left_cancel₀ hPpZ.ne' this
    rcases Nat.lt_or_ge 1 k with hk2 | hk2
    · -- `k ≥ 2`: `x^2` lies strictly between `(P k - 1)^2` and `(P k)^2`.
      exfalso
      have hPk : (1 : ℤ) ≤ (P : ℤ) * k := by
        have : (1 : ℤ) ≤ P := by exact_mod_cast hP
        have : (1 : ℤ) ≤ k := by exact_mod_cast hk1
        nlinarith
      have hlo : (P : ℤ) * k - 1 < x := by
        have : ((P : ℤ) * k - 1) ^ 2 < (x : ℤ) ^ 2 := by
          have : (2 : ℤ) ≤ P * 2 := by
            have : (1 : ℤ) ≤ P := by exact_mod_cast hP
            linarith
          have hk2' : (2 : ℤ) ≤ k := by exact_mod_cast hk2
          nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
      have hhi : (x : ℤ) < (P : ℤ) * k := by
        have : (x : ℤ) ^ 2 < ((P : ℤ) * k) ^ 2 := by
          have hk2' : (2 : ℤ) ≤ k := by exact_mod_cast hk2
          linarith
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
      omega
    · -- `k = 1`: `x = P` and `y = 2 P^2 - 1`.
      have hk1' : k = 1 := by omega
      subst hk1'
      have hxP : (x : ℤ) ^ 2 = (P : ℤ) ^ 2 := by rw [e2]; ring
      have hxP2 : x ^ 2 = P ^ 2 := by exact_mod_cast hxP
      have hxP' : x = P := Nat.pow_left_injective (by norm_num) hxP2
      have hs : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · rw [h0] at hPdef; norm_num at hPdef; omega
        · exact h0
      refine ⟨by omega, by rw [hxP', ← hPdef]; congr 1, ?_⟩
      have e3 : 2 ^ (2 * (s + 1) - 1) = 2 * P ^ 2 := by
        rw [← hPdef, show 2 * (s + 1) - 1 = 2 * s + 1 by omega]; ring
      rw [e3]
      generalize P ^ 2 = Q at hk ⊢
      omega

end Szalay
