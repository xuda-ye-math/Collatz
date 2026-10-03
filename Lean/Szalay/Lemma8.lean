import Mathlib

/-!
# Replacement for Szalay's Lemma 8

Szalay's Lemma 8 states: if `D, k, x` are positive, `k ≥ 3` and `2^(D+8k) + 2^(4k) + 1 = x^2`,
then `D > 56k - 32`. His proof is an explicit chain of seven substitutions in case A, and
case B is only sketched. In the proof of Theorem 1, Lemma 8 is combined with Lemma 2, which
gives `D + 8k ≤ 40k + 434`, to exclude `k ≥ 20`. This file proves the statement needed there:

`no_solution_large`: if `K ≥ 80`, `2K + 1 ≤ N ≤ 10K + 434` and `x^2 = 2^N + 2^K + 1`, then
there is no such `x`.

The proof uses the truncations `s_J(T)` of the `2`-adic square root of `1 + 4T`, where
`T = 2^(K-2)`. Their squares satisfy `s_J^2 = 1 + 4T + T^(J+1) R_J(T)` (`ring` identities).
A suitable `M` with `N/2 + 2 ≤ M < N` gives `x ≡ ±s_J (mod 2^M)`, and size bounds give
`x = ±s_J`. Then `2^N = T^(J+1) R_J(T)`, which is impossible: `R_J(T) > T` is not divisible
by `T`, since `R_J(T) ≡ R_J(0) ≠ 0 (mod T)` and `|R_J(0)| < T`.
-/

namespace Szalay

/-- If `a, b` are odd and `2^(M+1) ∣ a^2 - b^2` with `M ≥ 1`, then `2^M` divides
`a - b` or `a + b`. -/
theorem dvd_sub_or_add_of_sq (a b : ℤ) (M : ℕ) (hM : 1 ≤ M) (ha : Odd a) (hb : Odd b)
    (h : (2 : ℤ) ^ (M + 1) ∣ a ^ 2 - b ^ 2) : (2 : ℤ) ^ M ∣ a - b ∨ (2 : ℤ) ^ M ∣ a + b := by
  obtain ⟨u, hu⟩ : Even (a - b) := Odd.sub_odd ha hb
  obtain ⟨v, hv⟩ : Even (a + b) := Odd.add_odd ha hb
  have huv : u + v = a := by linarith
  have hprod : a ^ 2 - b ^ 2 = 4 * (u * v) := by
    have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [this, hu, hv]; ring
  have hM1 : (2 : ℤ) ^ (M + 1) = 4 * 2 ^ (M - 1) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hM2 : (2 : ℤ) ^ M = 2 * 2 ^ (M - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hprod, hM1] at h
  have h' : (2 : ℤ) ^ (M - 1) ∣ u * v := (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h
  rcases Int.even_or_odd u with hue | huo
  · have hvo : Odd v := by
      by_contra hv'
      have hve : Even v := Int.not_odd_iff_even.mp hv'
      have : Even (u + v) := hue.add hve
      rw [huv] at this
      exact (Int.not_even_iff_odd.mpr ha) this
    left
    have hc : IsCoprime ((2 : ℤ) ^ (M - 1)) v := (Int.isCoprime_two_left.mpr hvo).pow_left
    obtain ⟨w, hw⟩ := hc.dvd_of_dvd_mul_right h'
    exact ⟨w, by rw [hu, hM2, hw]; ring⟩
  · right
    have hc : IsCoprime ((2 : ℤ) ^ (M - 1)) u := (Int.isCoprime_two_left.mpr huo).pow_left
    obtain ⟨w, hw⟩ := hc.dvd_of_dvd_mul_left h'
    exact ⟨w, by rw [hv, hM2, hw]; ring⟩

/-- The core step: under the congruence and size conditions, `x = ±s`, hence
`2^N = T^(J+1) R`. -/
theorem core (x s R T : ℤ) (N M J : ℕ) (hM : 1 ≤ M)
    (hx : x ^ 2 = 2 ^ N + 4 * T + 1) (hs : s ^ 2 = 1 + 4 * T + T ^ (J + 1) * R)
    (hxo : Odd x) (hso : Odd s)
    (hdN : (2 : ℤ) ^ (M + 1) ∣ 2 ^ N) (hdT : (2 : ℤ) ^ (M + 1) ∣ T ^ (J + 1))
    (hxb : |x| < 2 ^ (M - 1)) (hsb : |s| < 2 ^ (M - 1)) :
    (2 : ℤ) ^ N = T ^ (J + 1) * R := by
  have hd : (2 : ℤ) ^ (M + 1) ∣ x ^ 2 - s ^ 2 := by
    have : x ^ 2 - s ^ 2 = 2 ^ N - T ^ (J + 1) * R := by rw [hx, hs]; ring
    rw [this]; exact dvd_sub hdN (dvd_mul_of_dvd_left hdT R)
  have h2M : (2 : ℤ) ^ M = 2 ^ (M - 1) + 2 ^ (M - 1) := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hxb
  obtain ⟨hs1, hs2⟩ := abs_lt.mp hsb
  have hsq : x ^ 2 = s ^ 2 := by
    rcases dvd_sub_or_add_of_sq x s M hM hxo hso hd with h1 | h1
    · have : x - s = 0 :=
        Int.eq_zero_of_abs_lt_dvd h1 (abs_lt.mpr ⟨by linarith, by linarith⟩)
      have : x = s := by linarith
      rw [this]
    · have : x + s = 0 :=
        Int.eq_zero_of_abs_lt_dvd h1 (abs_lt.mpr ⟨by linarith, by linarith⟩)
      have : x = -s := by linarith
      rw [this]; ring
  linarith

/-- `2^N = T^(J+1) R` is impossible when `T = 2^e < R` and `R ≡ c (mod T)` with
`0 < |c| < T`. -/
theorem not_pow_two (T R c Q : ℤ) (N J e : ℕ) (hT : T = 2 ^ e) (hR : R = c + T * Q)
    (hc0 : c ≠ 0) (hcT : |c| < T) (hTR : T < R) (h : (2 : ℤ) ^ N = T ^ (J + 1) * R) :
    False := by
  have hTpos : 0 < T := by rw [hT]; positivity
  have hRpos : 0 < R := by linarith
  have hRdvd : R ∣ 2 ^ N := ⟨T ^ (J + 1), by rw [h]; ring⟩
  have hnat : R.natAbs ∣ 2 ^ N := by
    have := Int.natAbs_dvd_natAbs.mpr hRdvd
    rwa [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl] at this
  obtain ⟨f, -, hRf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hnat
  have hR' : R = 2 ^ f := by
    have : (R.natAbs : ℤ) = R := Int.natAbs_of_nonneg hRpos.le
    rw [← this, hRf]; push_cast; ring
  have hef : e < f := by
    rw [hT, hR'] at hTR
    have : (2 : ℕ) ^ e < 2 ^ f := by exact_mod_cast hTR
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hTdvdR : T ∣ R := by
    rw [hT, hR']; exact pow_dvd_pow 2 hef.le
  have hTdvdc : T ∣ c := by
    have : c = R - T * Q := by rw [hR]; ring
    rw [this]; exact dvd_sub hTdvdR (dvd_mul_right T Q)
  obtain ⟨w, hw⟩ := hTdvdc
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
    exact hc0 hw
  have : T ≤ |c| := by
    rw [hw, abs_mul, abs_of_pos hTpos]
    have : 1 ≤ |w| := Int.one_le_abs hw0
    nlinarith
  linarith

/-- The final contradiction, combining `core` and `not_pow_two`. -/
theorem finish (x s R c Q T : ℤ) (N M J e : ℕ) (hM : 1 ≤ M) (hT : T = 2 ^ e)
    (hx : x ^ 2 = 2 ^ N + 4 * T + 1) (hs : s ^ 2 = 1 + 4 * T + T ^ (J + 1) * R)
    (hxo : Odd x) (hso : Odd s)
    (hdN : (2 : ℤ) ^ (M + 1) ∣ 2 ^ N) (hdT : (2 : ℤ) ^ (M + 1) ∣ T ^ (J + 1))
    (hxb : |x| < 2 ^ (M - 1)) (hsb : |s| < 2 ^ (M - 1))
    (hR : R = c + T * Q) (hc0 : c ≠ 0) (hcT : |c| < T) (hTR : T < R) : False :=
  not_pow_two T R c Q N J e hT hR hc0 hcT hTR
    (core x s R T N M J hM hx hs hxo hso hdN hdT hxb hsb)

/-! ### The truncated `2`-adic square roots of `1 + 4T` -/

/-- Bounds on powers of a large `T`, used for the size estimates below. -/
theorem pow_facts (T : ℤ) (hT : 1000 ≤ T) :
    1000 ≤ T ∧ 1000 * T ≤ T ^ 2 ∧ 1000 * T ^ 2 ≤ T ^ 3 ∧ 1000 * T ^ 3 ≤ T ^ 4 ∧
      1000 * T ^ 4 ≤ T ^ 5 ∧ 1000 * T ^ 5 ≤ T ^ 6 ∧ 1000 * T ^ 6 ≤ T ^ 7 := by
  have h0 : 0 ≤ T := by linarith
  have p : ∀ i : ℕ, 1000 * T ^ i ≤ T ^ (i + 1) := fun i => by
    rw [pow_succ]; have := pow_nonneg h0 i; nlinarith
  exact ⟨hT, by simpa using p 1, p 2, p 3, p 4, p 5, p 6⟩

/-- Data for one truncation: `s^2 = 1 + 4T + T^(J+1) R`, `s` odd, `|s| < 2^24 T^J`, and
`R = c + T Q` with `0 < |c| < T < R`. -/
structure TruncData (T : ℤ) (J : ℕ) where
  s : ℤ
  R : ℤ
  c : ℤ
  Q : ℤ
  hs : s ^ 2 = 1 + 4 * T + T ^ (J + 1) * R
  hso : Odd s
  hsb : |s| < 2 ^ 24 * T ^ J
  hR : R = c + T * Q
  hc0 : c ≠ 0
  hcT : |c| < T
  hTR : T < R

theorem odd_of_even_T {T s P : ℤ} (hT : Even T) (h : s = 1 + T * P) : Odd s := by
  obtain ⟨T', rfl⟩ := hT
  exact ⟨T' * P, by rw [h]; ring⟩

/-- The truncations for `J = 2, …, 7`, valid for `T ≥ 10000` even. -/
def truncData (T : ℤ) (hT : 10000 ≤ T) (hTe : Even T) : (J : ℕ) → 2 ≤ J → J ≤ 7 → TruncData T J
  | 2, _, _ =>
    { s := 1 + 2 * T - 2 * T ^ 2, R := -8 + 4 * T, c := -8, Q := 4,
      hs := by ring,
      hso := odd_of_even_T hTe (P := 2 - 2 * T) (by ring),
      hsb := by
        obtain ⟨h1, h2, -⟩ := pow_facts T (by linarith)
        rw [abs_lt]; constructor <;> nlinarith,
      hR := by ring, hc0 := by norm_num,
      hcT := by rw [abs_lt]; constructor <;> linarith,
      hTR := by linarith }
  | 3, _, _ =>
    { s := 1 + 2 * T - 2 * T ^ 2 + 4 * T ^ 3, R := 20 - 16 * T + 16 * T ^ 2, c := 20,
      Q := -16 + 16 * T,
      hs := by ring,
      hso := odd_of_even_T hTe (P := 2 - 2 * T + 4 * T ^ 2) (by ring),
      hsb := by
        obtain ⟨h1, h2, h3, -⟩ := pow_facts T (by linarith)
        rw [abs_lt]; constructor <;> nlinarith,
      hR := by ring, hc0 := by norm_num,
      hcT := by rw [abs_lt]; constructor <;> linarith,
      hTR := by obtain ⟨h1, h2, -⟩ := pow_facts T (by linarith); nlinarith }
  | 4, _, _ =>
    { s := 1 + 2 * T - 2 * T ^ 2 + 4 * T ^ 3 - 10 * T ^ 4,
      R := -56 + 56 * T - 80 * T ^ 2 + 100 * T ^ 3, c := -56, Q := 56 - 80 * T + 100 * T ^ 2,
      hs := by ring,
      hso := odd_of_even_T hTe (P := 2 - 2 * T + 4 * T ^ 2 - 10 * T ^ 3) (by ring),
      hsb := by
        obtain ⟨h1, h2, h3, h4, -⟩ := pow_facts T (by linarith)
        rw [abs_lt]; constructor <;> nlinarith,
      hR := by ring, hc0 := by norm_num,
      hcT := by rw [abs_lt]; constructor <;> linarith,
      hTR := by obtain ⟨h1, h2, h3, -⟩ := pow_facts T (by linarith); nlinarith }
  | 5, _, _ =>
    { s := 1 + 2 * T - 2 * T ^ 2 + 4 * T ^ 3 - 10 * T ^ 4 + 28 * T ^ 5,
      R := 168 - 192 * T + 324 * T ^ 2 - 560 * T ^ 3 + 784 * T ^ 4, c := 168,
      Q := -192 + 324 * T - 560 * T ^ 2 + 784 * T ^ 3,
      hs := by ring,
      hso := odd_of_even_T hTe (P := 2 - 2 * T + 4 * T ^ 2 - 10 * T ^ 3 + 28 * T ^ 4) (by ring),
      hsb := by
        obtain ⟨h1, h2, h3, h4, h5, -⟩ := pow_facts T (by linarith)
        rw [abs_lt]; constructor <;> nlinarith,
      hR := by ring, hc0 := by norm_num,
      hcT := by rw [abs_lt]; constructor <;> linarith,
      hTR := by obtain ⟨h1, h2, h3, h4, -⟩ := pow_facts T (by linarith); nlinarith }
  | 6, _, _ =>
    { s := 1 + 2 * T - 2 * T ^ 2 + 4 * T ^ 3 - 10 * T ^ 4 + 28 * T ^ 5 - 84 * T ^ 6,
      R := -528 + 660 * T - 1232 * T ^ 2 + 2464 * T ^ 3 - 4704 * T ^ 4 + 7056 * T ^ 5,
      c := -528, Q := 660 - 1232 * T + 2464 * T ^ 2 - 4704 * T ^ 3 + 7056 * T ^ 4,
      hs := by ring,
      hso := odd_of_even_T hTe
        (P := 2 - 2 * T + 4 * T ^ 2 - 10 * T ^ 3 + 28 * T ^ 4 - 84 * T ^ 5) (by ring),
      hsb := by
        obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := pow_facts T (by linarith)
        rw [abs_lt]; constructor <;> nlinarith,
      hR := by ring, hc0 := by norm_num,
      hcT := by rw [abs_lt]; constructor <;> linarith,
      hTR := by obtain ⟨h1, h2, h3, h4, h5, -⟩ := pow_facts T (by linarith); nlinarith }
  | 7, _, _ =>
    { s := 1 + 2 * T - 2 * T ^ 2 + 4 * T ^ 3 - 10 * T ^ 4 + 28 * T ^ 5 - 84 * T ^ 6
        + 264 * T ^ 7,
      R := 1716 - 2288 * T + 4576 * T ^ 2 - 9984 * T ^ 3 + 21840 * T ^ 4 - 44352 * T ^ 5
        + 69696 * T ^ 6,
      c := 1716,
      Q := -2288 + 4576 * T - 9984 * T ^ 2 + 21840 * T ^ 3 - 44352 * T ^ 4 + 69696 * T ^ 5,
      hs := by ring,
      hso := odd_of_even_T hTe
        (P := 2 - 2 * T + 4 * T ^ 2 - 10 * T ^ 3 + 28 * T ^ 4 - 84 * T ^ 5 + 264 * T ^ 6)
        (by ring),
      hsb := by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := pow_facts T (by linarith)
        rw [abs_lt]; constructor <;> nlinarith,
      hR := by ring, hc0 := by norm_num,
      hcT := by rw [abs_lt]; constructor <;> linarith,
      hTR := by obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := pow_facts T (by linarith); nlinarith }
  | 0, h, _ => absurd h (by norm_num)
  | 1, h, _ => absurd h (by norm_num)
  | (n + 8), _, h => absurd h (by omega)

/-- **No solution for large `K`** (replacement for Szalay's Lemma 8 in the range used). -/
theorem no_solution_large (K N x : ℕ) (hK : 80 ≤ K) (hN1 : 2 * K + 1 ≤ N)
    (hN2 : N ≤ 10 * K + 434) (h : x ^ 2 = 2 ^ N + 2 ^ K + 1) : False := by
  -- Notation: `T = 2^e` with `e = K - 2`.
  set e := K - 2 with he
  have hKe : K = e + 2 := by omega
  have he78 : 78 ≤ e := by omega
  set T : ℤ := 2 ^ e with hTdef
  have hT1000 : (10000 : ℤ) ≤ T := by
    calc (10000 : ℤ) ≤ 2 ^ 14 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)
  have hTe : Even T := by
    rw [hTdef, show e = (e - 1) + 1 by omega, pow_succ]; exact even_two.mul_left _
  have hxZ : (x : ℤ) ^ 2 = 2 ^ N + 4 * T + 1 := by
    have : ((x ^ 2 : ℕ) : ℤ) = ((2 ^ N + 2 ^ K + 1 : ℕ) : ℤ) := by rw [h]
    push_cast at this
    rw [this, hKe, pow_add, hTdef]; ring
  -- `x` is odd.
  have hxo : Odd (x : ℤ) := by
    have h1 : Odd (2 ^ N + 2 ^ K + 1) := by
      have : Even (2 ^ N + 2 ^ K) :=
        (Nat.even_pow.mpr ⟨even_two, by omega⟩).add (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact this.add_one
    rw [← h] at h1
    have : Odd x := (Nat.odd_pow_iff (by norm_num)).mp h1
    exact this.natCast
  -- Choice of `J` and `M`.
  obtain ⟨A, hA⟩ : ∃ A, A = (N + 4) / 2 := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = A / e := ⟨_, rfl⟩
  have hdm : e * J + A % e = A := by rw [hJ]; exact Nat.div_add_mod A e
  have hmodlt : A % e < e := Nat.mod_lt A (by omega)
  have hJ1 : 1 ≤ J := by
    rw [hJ]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hJ7 : J ≤ 7 := by
    have : J < 8 := by rw [hJ]; exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  obtain ⟨P, hP⟩ : ∃ P, P = e * J := ⟨_, rfl⟩
  rw [← hP] at hdm
  obtain ⟨M, hMdef⟩ : ∃ M, M = max A (P + 26) := ⟨_, rfl⟩
  have hMA : A ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hMP : P + 26 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMcases : M = A ∨ M = P + 26 := by rw [hMdef]; omega
  have hM2 : M + 1 ≤ e * (J + 1) := by rw [mul_add, mul_one, ← hP]; omega
  have hM3 : M + 1 ≤ N := by omega
  have hM4 : N + 3 ≤ 2 * M := by omega
  have hM : 1 ≤ M := by omega
  -- Divisibility and size facts.
  have hdN : (2 : ℤ) ^ (M + 1) ∣ 2 ^ N := pow_dvd_pow 2 hM3
  have hdT : ∀ J' : ℕ, J' = J → (2 : ℤ) ^ (M + 1) ∣ T ^ (J' + 1) := by
    rintro J' rfl
    rw [hTdef, ← pow_mul]; exact pow_dvd_pow 2 hM2
  have hxb : |(x : ℤ)| < 2 ^ (M - 1) := by
    have hx2 : x ^ 2 < (2 ^ (M - 1)) ^ 2 := by
      rw [h, ← pow_mul]
      have h1 : 2 ^ K + 1 < 2 ^ N := by
        have : 2 ^ (K + 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        have : 1 < 2 ^ K := Nat.one_lt_two_pow (by omega)
        omega
      have h2 : 2 ^ (N + 1) ≤ 2 ^ ((M - 1) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at h2
      omega
    have : x < 2 ^ (M - 1) := lt_of_pow_lt_pow_left₀ 2 (by positivity) hx2
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast this
  have hsize : ∀ s : ℤ, |s| < 2 ^ 24 * T ^ J → |s| < 2 ^ (M - 1) := by
    intro s hs
    calc |s| < 2 ^ 24 * T ^ J := hs
      _ = 2 ^ (24 + e * J) := by rw [hTdef, ← pow_mul, pow_add]
      _ ≤ 2 ^ (M - 1) := pow_le_pow_right₀ (by norm_num) (by rw [← hP]; omega)
  -- The case `J = 1`: `2^N = 4 T^2 = 2^(2K-2)`, against `N ≥ 2K + 1`.
  rcases Nat.lt_or_ge J 2 with hJlt | hJge
  · have hJ1' : J = 1 := by omega
    have hs1 : (1 + 2 * T) ^ 2 = 1 + 4 * T + T ^ (J + 1) * 4 := by rw [hJ1']; ring
    have hso : Odd (1 + 2 * T) := ⟨T, by ring⟩
    have hsb : |1 + 2 * T| < 2 ^ (M - 1) := hsize _ (by
      rw [hJ1', abs_lt]; constructor <;> nlinarith)
    have key := core (x : ℤ) (1 + 2 * T) 4 T N M J hM hxZ hs1 hxo hso hdN (hdT J rfl) hxb hsb
    rw [hJ1', hTdef, ← pow_mul, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add] at key
    have := Nat.pow_right_injective (le_refl 2) (by exact_mod_cast key : 2 ^ N = 2 ^ (e * 2 + 2))
    omega
  · let d := truncData T hT1000 hTe J hJge hJ7
    exact finish (x : ℤ) d.s d.R d.c d.Q T N M J e hM hTdef hxZ d.hs hxo d.hso hdN
      (hdT J rfl) hxb (hsize _ d.hsb) d.hR d.hc0 d.hcT d.hTR

end Szalay
