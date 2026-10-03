import Mathlib

/-!
# Certified square checks for finite searches

`isqrt` is a Newton iteration with fuel, so the kernel can evaluate it. Its correctness is
never used: every use checks the bracket `s^2 ≤ c < (s+1)^2`, and `eq_of_bracket` then shows
that `s` is the only candidate for a square root of `c`.
-/

namespace Szalay

/-- Newton iteration for the integer square root, with fuel. -/
def isqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
    if (g + n / g) / 2 < g then isqrtIter fuel n ((g + n / g) / 2) else g

/-- A candidate for the integer square root, computable in the kernel. -/
def isqrt (n : ℕ) : ℕ := if n ≤ 1 then n else isqrtIter 400 n n

theorem eq_of_bracket {c s x : ℕ} (h1 : s ^ 2 ≤ c) (h2 : c < (s + 1) ^ 2)
    (hx : x ^ 2 = c) : x = s := by
  have hle : x ≤ s := by
    by_contra hcon
    have : (s + 1) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hge : s ≤ x := by
    by_contra hcon
    have : (x + 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  omega

/-- `sqTest c L` holds when `isqrt c` brackets `c`, and if `c` is a square then its root
lies in `L`. -/
def sqTest (c : ℕ) (L : List ℕ) : Bool :=
  decide ((isqrt c) ^ 2 ≤ c) && decide (c < (isqrt c + 1) ^ 2) &&
    (decide ((isqrt c) ^ 2 ≠ c) || decide (isqrt c ∈ L))

theorem mem_of_sqTest {c : ℕ} {L : List ℕ} (h : sqTest c L = true) {x : ℕ}
    (hx : x ^ 2 = c) : x ∈ L := by
  simp only [sqTest, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hxs := eq_of_bracket h1 h2 hx
  subst hxs
  rcases h3 with h3 | h3
  · exact absurd hx h3
  · exact h3

end Szalay
