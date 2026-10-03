import Szalay.Lemma4
import Szalay.Lemma67
import Szalay.Lemma8
import Szalay.Approx

/-!
# Szalay, Theorem 1

If the positive integers `n ≥ m` and `x` satisfy `2^n + 2^m + 1 = x^2`, then
`(n, m, x) = (2t, t + 1, 2^t + 1)` with `t ≥ 1`, or `(n, m, x) ∈ {(5,4,7), (9,4,23)}`.

The proof follows Szalay. His map `τ` pairs a solution with the solution of the family that
has the same difference `n - m`; here this is the case split on `n` against `2m - 2`:

* `n < 2m - 2`: Lemma 7 gives `(5, 4, 7)`;
* `n = 2m - 2`: the family;
* `n > 2m - 2`: with `d = n - 2m + 2`, the family solution `y = 2^(m+d-1) + 1` satisfies
  `y^2 - 1 = 2^d (x^2 - 1)`, so `d` is odd by Lemma 5. Then `m` is even (mod 3), `d = 1` is
  impossible (Szalay's (54)), and for `d ≥ 3` the residues mod 5 give `m = 4k`, so
  `2^(D+8k) + 2^(4k) + 1 = x^2` with `D = d - 2` (Szalay's (56)). Lemma 2 bounds
  `D + 8k ≤ 40k + 434`; for `k ≥ 20` this contradicts `no_solution_large`; for `k ≤ 19`
  Lemma 1 gives `D ≤ 19`, and a finite search leaves `(D, k, x) = (1, 1, 23)`.
-/

namespace Szalay

/-- The roots allowed in the final search. -/
def searchRoots (D k : ℕ) : List ℕ := if D = 1 ∧ k = 1 then [23] else []

/-- The final search of Szalay's proof: `1 ≤ D ≤ 19`, `1 ≤ k ≤ 19`. -/
def finalCheck : Bool :=
  (List.range 20).all fun D => (List.range 20).all fun k =>
    decide (D = 0) || decide (k = 0) ||
      sqTest (2 ^ (D + 8 * k) + 2 ^ (4 * k) + 1) (searchRoots D k)

theorem finalCheck_eq : finalCheck = true := by decide

/-- `2^e mod 3 = 2` for odd `e`. -/
theorem two_pow_odd_mod_three (e : ℕ) (he : Odd e) : 2 ^ e % 3 = 2 := by
  obtain ⟨j, rfl⟩ := he
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

/-- `2^e mod 5 ∈ {2, 3}` for odd `e`. -/
theorem two_pow_odd_mod_five (e : ℕ) (he : Odd e) : 2 ^ e % 5 = 2 ∨ 2 ^ e % 5 = 3 := by
  obtain ⟨j, rfl⟩ := he
  rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · left
    rw [show 2 * (i + i) + 1 = 4 * i + 1 by ring, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  · right
    rw [show 2 * (2 * i + 1) + 1 = 4 * i + 3 by ring, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem sq_mod_three (x : ℕ) : x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
  have := Nat.mod_lt x (show 3 > 0 by norm_num)
  have h : x ^ 2 % 3 = (x % 3) ^ 2 % 3 := Nat.pow_mod x 2 3
  interval_cases hx : x % 3 <;> simp [h]

theorem sq_mod_five (x : ℕ) : x ^ 2 % 5 = 0 ∨ x ^ 2 % 5 = 1 ∨ x ^ 2 % 5 = 4 := by
  have := Nat.mod_lt x (show 5 > 0 by norm_num)
  have h : x ^ 2 % 5 = (x % 5) ^ 2 % 5 := Nat.pow_mod x 2 5
  interval_cases hx : x % 5 <;> simp [h]

/-- Szalay's (56): `2^(D+8k) + 2^(4k) + 1 = x^2` with `D` odd and `k ≥ 1` forces
`(D, k, x) = (1, 1, 23)`. -/
theorem eq56 (D k x : ℕ) (hD : Odd D) (hk : 1 ≤ k)
    (h : 2 ^ (D + 8 * k) + 2 ^ (4 * k) + 1 = x ^ 2) : D = 1 ∧ k = 1 ∧ x = 23 := by
  have hD1 : 1 ≤ D := hD.pos
  -- Lemma 2: `D + 8k ≤ 40k + 434`.
  have hupper : D + 8 * k ≤ 10 * (4 * k) + 434 := by
    obtain ⟨s, hs⟩ : ∃ s, D + 8 * k = 2 * s + 1 := by
      obtain ⟨j, rfl⟩ := hD; exact ⟨j + 4 * k, by ring⟩
    have h2 := two_pow_lt_of_approx s x (2 ^ (4 * k) + 1) (by positivity)
      (by rw [← hs, ← h]; ring)
    have h3 : (2 ^ (4 * k) + 1) ^ 10 ≤ (2 ^ (4 * k + 1)) ^ 10 := by
      apply Nat.pow_le_pow_left
      rw [pow_succ]; have := Nat.one_le_two_pow (n := 4 * k); omega
    have h4 : 2 ^ (2 * s + 1) < 2 ^ (425 + (4 * k + 1) * 10) := by
      calc 2 ^ (2 * s + 1) < 2 ^ 425 * (2 ^ (4 * k) + 1) ^ 10 := h2
        _ ≤ 2 ^ 425 * (2 ^ (4 * k + 1)) ^ 10 := Nat.mul_le_mul_left _ h3
        _ = 2 ^ (425 + (4 * k + 1) * 10) := by rw [← pow_mul, ← pow_add]
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4
    omega
  -- `k ≥ 20` is impossible.
  have hk19 : k ≤ 19 := by
    by_contra hk20
    exact no_solution_large (4 * k) (D + 8 * k) x (by omega) (by omega) hupper (by rw [← h])
  -- Lemma 1: `D ≤ 19`.
  have hD19 : D ≤ 19 := by
    have hDne : ((2 : ℤ) ^ (4 * k) + 1) ≠ 0 := by positivity
    have habs : |((2 : ℤ) ^ (4 * k) + 1)| < 2 ^ 96 := by
      rw [abs_of_pos (by positivity)]
      have : (2 : ℤ) ^ (4 * k) ≤ 2 ^ 76 := pow_le_pow_right₀ (by norm_num) (by omega)
      have : (2 : ℤ) ^ 76 + 1 < 2 ^ 96 := by norm_num
      linarith
    have hZ : (2 : ℤ) ^ (D + 8 * k) + (2 ^ (4 * k) + 1) = (x : ℤ) ^ 2 := by
      have : ((2 ^ (D + 8 * k) + 2 ^ (4 * k) + 1 : ℕ) : ℤ) = ((x ^ 2 : ℕ) : ℤ) := by rw [h]
      push_cast at this; linarith
    have h1 := two_pow_lt_of_cor2 _ (D + 8 * k) x hDne habs hZ
    have h2 : ((2 : ℤ) ^ (4 * k) + 1) ^ 2 ≤ (2 ^ (4 * k + 1)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [pow_succ]; have : (1 : ℤ) ≤ 2 ^ (4 * k) := one_le_pow₀ (by norm_num); linarith
    have h3 : (2 : ℤ) ^ (D + 8 * k) < 2 ^ (18 + (4 * k + 1) * 2) := by
      calc (2 : ℤ) ^ (D + 8 * k) < 2 ^ 18 * (2 ^ (4 * k) + 1) ^ 2 := h1
        _ ≤ 2 ^ 18 * (2 ^ (4 * k + 1)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 ^ (18 + (4 * k + 1) * 2) := by rw [← pow_mul, ← pow_add]
    have h4 : (2 : ℕ) ^ (D + 8 * k) < 2 ^ (18 + (4 * k + 1) * 2) := by exact_mod_cast h3
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4
    omega
  -- The finite search.
  have hchk := finalCheck_eq
  simp only [finalCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at hchk
  rcases hchk D (by omega) k (by omega) with (h0 | h0) | htest
  · omega
  · omega
  · have hmem := mem_of_sqTest htest h.symm
    unfold searchRoots at hmem
    split_ifs at hmem with hDk
    · simp at hmem; exact ⟨hDk.1, hDk.2, hmem⟩
    · simp at hmem

/-- **Szalay, Theorem 1.** -/
theorem theorem1 (n m x : ℕ) (hm : 0 < m) (hmn : m ≤ n) (hx : 0 < x)
    (h : 2 ^ n + 2 ^ m + 1 = x ^ 2) :
    (∃ t, 1 ≤ t ∧ n = 2 * t ∧ m = t + 1 ∧ x = 2 ^ t + 1) ∨
      (n, m, x) ∈ [(5, 4, 7), (9, 4, 23)] := by
  have hZ : (2 : ℤ) ^ n + 2 ^ m + 1 = (x : ℤ) ^ 2 := by exact_mod_cast h
  rcases Nat.eq_or_lt_of_le hmn with heq | hlt
  · -- `n = m`: Lemma 4 applied to `2^(m+1) + 1 = x^2`.
    subst heq
    have hZ' : (2 : ℤ) ^ (m + 1) + 1 = (x : ℤ) ^ 2 := by rw [pow_succ]; linarith
    have hL := lemma4 (m + 1) x (by omega) hx (by intro he; linarith)
      (by rw [abs_lt]; constructor <;> linarith)
    simp only [L4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hL
    rcases hL with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · omega
    · have : m = 1 := by omega
      subst this; norm_num at h
    · have : m = 2 := by omega
      subst this
      left; exact ⟨1, le_refl _, rfl, rfl, rfl⟩
    · omega
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · -- `m = 1`: Lemma 4 applied to `2^n + 3 = x^2`.
    have hm1' : m = 1 := by omega
    subst hm1'
    have hL := lemma4 n x (by omega) hx (by intro he; norm_num at hZ; linarith)
      (by rw [abs_lt]; constructor <;> norm_num at hZ <;> linarith)
    simp only [L4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hL
    rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at h
  rcases lt_trichotomy n (2 * m - 2) with h1 | h2 | h3
  · -- `n < 2m - 2`: Lemma 7.
    obtain ⟨rfl, rfl, rfl⟩ := lemma7 n m x hlt h1 h
    right; simp
  · -- `n = 2m - 2`: the family `(2t, t + 1, 2^t + 1)`.
    left
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    have hn2 : n = 2 * t := by omega
    subst hn2
    refine ⟨t, by omega, rfl, rfl, ?_⟩
    have e : x ^ 2 = (2 ^ t + 1) ^ 2 := by rw [← h]; ring
    exact Nat.pow_left_injective (by norm_num) e
  · -- `n > 2m - 2`: write `m = a + 2` and `n = 2m - 2 + d`.
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, n = 2 * a + 2 + d := ⟨n - (2 * a + 2), by omega⟩
    have hd1 : 1 ≤ d := by omega
    have hxodd : Odd x := by
      have h1 : Odd (2 ^ (2 * a + 2 + d) + 2 ^ (a + 2) + 1) :=
        ((Nat.even_pow.mpr ⟨even_two, by omega⟩).add
          (Nat.even_pow.mpr ⟨even_two, by omega⟩)).add_one
      rw [h] at h1
      exact (Nat.odd_pow_iff (by norm_num)).mp h1
    -- `d` is odd: otherwise Lemma 5, applied to `y = 2^(m+d-1) + 1`, makes `x` even.
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with ⟨u, hu⟩ | hdo
      · exfalso
        have hu1 : 1 ≤ u := by omega
        have hy : (2 ^ (a + 1 + d) + 1) ^ 2 + 2 ^ (2 * u) = 2 ^ (2 * u) * x ^ 2 + 1 := by
          rw [← h, show 2 * u = d by omega]
          ring
        have hx1 : 1 < x := by
          have : 2 ^ 2 < x ^ 2 := by
            rw [← h]
            have : 2 ^ 2 ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have : 0 < 2 ^ (2 * a + 2 + d) := by positivity
            omega
          have : 2 < x := lt_of_pow_lt_pow_left₀ 2 (by positivity) this
          omega
        have hy1 : 1 < 2 ^ (a + 1 + d) + 1 := by
          have := Nat.one_le_two_pow (n := a + 1 + d); omega
        obtain ⟨hu2, hxe, -⟩ := lemma5 u x _ hu1 hx1 hy1 hy
        rw [hxe] at hxodd
        have : Even (2 ^ (u - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
        exact (Nat.not_even_iff_odd.mpr hxodd) this
      · exact hdo
    -- `m` is even: otherwise `x^2 ≡ 2 (mod 3)`.
    have hmeven : Even (a + 2) := by
      rcases Nat.even_or_odd (a + 2) with hme | hmo
      · exact hme
      · exfalso
        have hn_odd : Odd (2 * a + 2 + d) := by
          obtain ⟨j, rfl⟩ := hdodd; exact ⟨a + 1 + j, by ring⟩
        have h1 := two_pow_odd_mod_three _ hn_odd
        have h2 := two_pow_odd_mod_three _ hmo
        have h3 := sq_mod_three x
        rw [← h] at h3
        omega
    obtain ⟨r, hr⟩ := hmeven
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · -- `d = 1`: Szalay's (54), excluded by `no_sol_two_mul_sub_one`.
      exfalso
      have hd1' : d = 1 := by obtain ⟨j, rfl⟩ := hdodd; omega
      subst hd1'
      exact no_sol_two_mul_sub_one (a + 2) x (by omega)
        (by rw [show 2 * (a + 2) - 1 = 2 * a + 2 + 1 by omega]; exact h)
    · -- `d ≥ 3`: `D = d - 2` is odd and `n = D + 2m`.
      obtain ⟨D, rfl⟩ : ∃ D, d = D + 2 := ⟨d - 2, by omega⟩
      have hDodd : Odd D := by
        obtain ⟨j, hj⟩ := hdodd; exact ⟨j - 1, by omega⟩
      -- `m = 2r` with `r` even: otherwise `x^2 ≡ 2^D ∈ {2, 3} (mod 5)`.
      have hreven : Even r := by
        rcases Nat.even_or_odd r with hre | hro
        · exact hre
        · exfalso
          have hn : 2 * a + 2 + (D + 2) = D + 4 * r := by omega
          have hm : a + 2 = 2 * r := by omega
          rw [hn, hm] at h
          have h1 := two_pow_odd_mod_five D hDodd
          have h2 : 2 ^ (D + 4 * r) % 5 = 2 ^ D % 5 := by
            rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod (2 ^ 4)]; norm_num
          have h3 : 2 ^ (2 * r) % 5 = 4 := by
            obtain ⟨i, rfl⟩ := hro
            rw [pow_mul, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
          have h4 := sq_mod_five x
          rw [← h] at h4
          omega
      obtain ⟨k, hk⟩ := hreven
      have hk1 : 1 ≤ k := by omega
      have hn : 2 * a + 2 + (D + 2) = D + 8 * k := by omega
      have hm : a + 2 = 4 * k := by omega
      rw [hn, hm] at h
      obtain ⟨rfl, rfl, rfl⟩ := eq56 D k x hDodd hk1 h
      have ha : a = 2 := by omega
      subst ha
      right; simp

/-- The paper's Lemma 4 (i): the solutions of `2^a + 2^b + 1 = z^2` in positive integers
`a ≥ b` and `z` are `(2u, u + 1, 2^u + 1)` with `u ≥ 1`, `(5,4,7)` and `(9,4,23)`. -/
theorem lemma4_i (a b z : ℕ) (hb : 0 < b) (hab : b ≤ a) (hz : 0 < z) :
    (2 : ℤ) ^ a + 2 ^ b + 1 = (z : ℤ) ^ 2 ↔
      (∃ u, 1 ≤ u ∧ a = 2 * u ∧ b = u + 1 ∧ z = 2 ^ u + 1) ∨
        (a, b, z) ∈ [(5, 4, 7), (9, 4, 23)] := by
  constructor
  · intro h
    exact theorem1 a b z hb hab hz (by exact_mod_cast h)
  · rintro (⟨u, -, rfl, rfl, rfl⟩ | h)
    · push_cast; ring
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num

end Szalay
