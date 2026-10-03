import Szalay.Lemma4

/-!
# Szalay, Theorem 2

If the positive integers `n, m, x` satisfy `2^n - 2^m + 1 = x^2`, then
(i) `(n, m, x) = (2t, t + 1, 2^t - 1)` with `t ≥ 2`, or (ii) `(n, m, x) = (t, t, 1)`, or
(iii) `(n, m, x) ∈ {(5,3,5), (7,3,11), (15,3,181)}`.

Szalay's proof: for `m ≥ 4` use Lemma 3 with `D₂ = 2^m - 1`, for `m = 3` the Ramanujan–Nagell
row of Lemma 3, and for `m = 1, 2` Lemma 4.
-/

namespace Szalay

/-- **Szalay, Theorem 2.** -/
theorem theorem2 (n m x : ℕ) (hn : 0 < n) (hm : 0 < m) (hx : 0 < x)
    (h : (2 : ℤ) ^ n - 2 ^ m + 1 = (x : ℤ) ^ 2) :
    (∃ t, 2 ≤ t ∧ n = 2 * t ∧ m = t + 1 ∧ x = 2 ^ t - 1) ∨ (n = m ∧ x = 1) ∨
      (n, m, x) ∈ [(5, 3, 5), (7, 3, 11), (15, 3, 181)] := by
  have hx1 : (1 : ℤ) ≤ (x : ℤ) ^ 2 := by
    have : (1 : ℤ) ≤ x := by exact_mod_cast hx
    nlinarith
  rcases lt_trichotomy n m with hlt | heq | hgt
  · -- `n < m` is impossible.
    exfalso
    have : (2 : ℤ) ^ n * 2 ≤ 2 ^ m := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hlt
    have : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith
  · -- `n = m` gives `x = 1`.
    subst heq
    right; left
    refine ⟨rfl, ?_⟩
    have : (x : ℤ) ^ 2 = 1 := by linarith
    have : (x : ℤ) = 1 := by nlinarith
    exact_mod_cast this
  · -- `n > m`.
    rcases (by omega : 4 ≤ m ∨ m = 3 ∨ m = 2 ∨ m = 1) with h4 | h3 | h2 | h1
    · have hb := beukers_thm2_mersenne m n x h4 hn hx (by linarith)
      rcases hb with ⟨hnm, _⟩ | ⟨hn', hx'⟩
      · omega
      · left
        exact ⟨m - 1, by omega, by omega, by omega, by rw [hx']⟩
    · subst h3
      have hb := beukers_thm2_seven n x hn hx (by linarith)
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · omega
      · left; exact ⟨2, le_refl _, rfl, rfl, rfl⟩
      · right; right; simp
      · right; right; simp
      · right; right; simp
    · subst h2
      have hL := lemma4 n x hn hx (by intro he; linarith) (by
        rw [abs_lt]; constructor <;> linarith)
      simp only [L4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hL
      rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (revert h hgt; norm_num)
    · subst h1
      have hL := lemma4 n x hn hx (by intro he; linarith) (by
        rw [abs_lt]; constructor <;> linarith)
      simp only [L4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hL
      rcases hL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (revert h hgt; norm_num)

/-- The paper's Lemma 4 (ii): the solutions of `2^a - 2^b + 1 = z^2` in positive integers
`a > b` and `z` are `(2u, u + 1, 2^u - 1)` with `u ≥ 2`, `(5,3,5)`, `(7,3,11)`, `(15,3,181)`. -/
theorem lemma4_ii (a b z : ℕ) (hb : 0 < b) (hab : b < a) (hz : 0 < z) :
    (2 : ℤ) ^ a - 2 ^ b + 1 = (z : ℤ) ^ 2 ↔
      (∃ u, 2 ≤ u ∧ a = 2 * u ∧ b = u + 1 ∧ z = 2 ^ u - 1) ∨
        (a, b, z) ∈ [(5, 3, 5), (7, 3, 11), (15, 3, 181)] := by
  constructor
  · intro h
    rcases theorem2 a b z (by omega) hb hz h with h1 | ⟨hab', _⟩ | h3
    · exact Or.inl h1
    · omega
    · exact Or.inr h3
  · rintro (⟨u, hu, rfl, rfl, rfl⟩ | h)
    · have h1 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
      have : ((2 ^ u - 1 : ℕ) : ℤ) = 2 ^ u - 1 := by push_cast [Nat.cast_sub h1]; ring
      rw [this]; ring
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num

end Szalay
