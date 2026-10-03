import Szalay.Beukers

/-!
# Szalay's application of Lemma 2

If `x^2 = 2^(2s+1) + c` with `c > 0`, then Szalay's Lemma 2 (Beukers) gives
`2^(2s+1) < 2^425 c^10`. This is the integer form of Szalay's (58): with `p = 2^(2s+1)` and
`q = p^0.1`, Lemma 2 and `x - q^5 < c / (2 q^5)` give `2 · 2^(-43.5) q < c`.
-/

namespace Szalay

theorem two_pow_lt_of_approx (s x c : ℕ) (hc : 0 < c) (h : x ^ 2 = 2 ^ (2 * s + 1) + c) :
    2 ^ (2 * s + 1) < 2 ^ 425 * c ^ 10 := by
  set P : ℝ := (2 : ℝ) ^ (2 * s + 1) with hPdef
  have hP : 0 < P := by positivity
  set q : ℝ := P ^ (0.1 : ℝ) with hqdef
  have hq : 0 < q := Real.rpow_pos_of_pos hP _
  have hpow : ∀ n : ℕ, q ^ n = P ^ ((0.1 : ℝ) * n) := fun n => by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  have e5 : P ^ (0.5 : ℝ) = q ^ 5 := by rw [hpow]; norm_num
  have e9 : P ^ (0.9 : ℝ) = q ^ 9 := by rw [hpow]; norm_num
  have e10 : P = q ^ 10 := by rw [hpow]; norm_num
  set X : ℝ := (x : ℝ) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hX2 : X ^ 2 = q ^ 10 + c := by
    rw [← e10, hXdef, hPdef]; exact_mod_cast h
  -- `X > q^5`.
  have hXq : q ^ 5 < X := by
    have : (q ^ 5) ^ 2 < X ^ 2 := by
      rw [hX2, show (q ^ 5) ^ 2 = q ^ 10 by ring]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hX0 this
  -- Lemma 2 of Szalay.
  have hax := beukers_approx s (x : ℤ)
  rw [← hPdef, e5, e9, Int.cast_natCast, ← hXdef] at hax
  set a : ℝ := (2 : ℝ) ^ (-43.5 : ℝ) with hadef
  have ha : 0 < a := by positivity
  have hq5 : 0 < q ^ 5 := pow_pos hq 5
  have hX1 : 0 < X / q ^ 5 - 1 := by
    rw [sub_pos, one_lt_div hq5]; exact hXq
  rw [abs_of_pos hX1] at hax
  -- `X / q^5 - 1 < c / (2 q^10)`.
  have hupper : X / q ^ 5 - 1 < c / (2 * q ^ 10) := by
    have hsum : 2 * q ^ 5 < X + q ^ 5 := by linarith
    have hprod : (X - q ^ 5) * (X + q ^ 5) = c := by
      have : (X - q ^ 5) * (X + q ^ 5) = X ^ 2 - (q ^ 5) ^ 2 := by ring
      rw [this, hX2, ← pow_mul]; ring
    rw [div_sub_one hq5.ne', div_lt_div_iff₀ hq5 (by positivity)]
    have hd : 0 < X - q ^ 5 := by linarith
    have h1 : (X - q ^ 5) * (2 * q ^ 5) < (X - q ^ 5) * (X + q ^ 5) :=
      mul_lt_mul_of_pos_left hsum hd
    rw [hprod] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hq5
    have e : (X - q ^ 5) * (2 * q ^ 10) = (X - q ^ 5) * (2 * q ^ 5) * q ^ 5 := by ring
    rw [e]; exact h2
  -- Hence `2 a q < c`.
  have hkey : 2 * a * q < c := by
    have := lt_trans hax hupper
    rw [div_lt_div_iff₀ (pow_pos hq 9) (by positivity)] at this
    have h10 : q ^ 10 = q ^ 9 * q := by ring
    rw [h10] at this
    nlinarith [pow_pos hq 9]
  -- `2 a = 2^(-42.5)`, so `q < 2^42.5 c`.
  have h2a' : 2 * a = (2 : ℝ) ^ (-42.5 : ℝ) := by
    rw [hadef, show (-42.5 : ℝ) = 1 + (-43.5) by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one]
  have h2a : (2 : ℝ) ^ (42.5 : ℝ) * (2 * a) = 1 := by
    rw [h2a', ← Real.rpow_add (by norm_num)]; norm_num
  have hb : (0 : ℝ) < 2 ^ (42.5 : ℝ) := by positivity
  have hqlt : q < 2 ^ (42.5 : ℝ) * c := by
    have : q = 2 ^ (42.5 : ℝ) * (2 * a) * q := by rw [h2a, one_mul]
    rw [this, mul_assoc]
    exact mul_lt_mul_of_pos_left (by linarith) hb
  have h10 : q ^ 10 < (2 ^ (42.5 : ℝ) * c) ^ 10 := pow_lt_pow_left₀ hqlt hq.le (by norm_num)
  have h425 : ((2 : ℝ) ^ (42.5 : ℝ)) ^ 10 = 2 ^ 425 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← e10, mul_pow, h425] at h10
  rw [hPdef] at h10
  exact_mod_cast h10

end Szalay
