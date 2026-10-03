import Mathlib

/-!
# The results of Beukers used by Szalay

L. Szalay, *The equations 2^N ± 2^M ± 2^L = z^2*, Indag. Math. (N.S.) 13 (2002), 131–142,
uses three results of F. Beukers, *On the generalized Ramanujan–Nagell equation I*,
Acta Arith. 38 (1981), 389–410. Their proofs rest on hypergeometric approximations and
are not formalized here. They enter as axioms, stated as in Szalay's Section 3:

* `beukers_cor2`: Szalay's Lemma 1 (Beukers, Corollary 2);
* `beukers_approx`: Szalay's Lemma 2 (Beukers);
* `beukers_thm2_mersenne`, `beukers_thm2_seven`: the rows `D₂ = 2^k - 1` and `D₂ = 7`
  of the table in Szalay's Lemma 3 (Beukers, Theorem 2). The row `D₂ = 7` is the
  Ramanujan–Nagell theorem.

Every other step of Szalay's proofs is proved in Lean.
-/

namespace Szalay

/-- Szalay, Lemma 1 (Beukers, Corollary 2). If `D ≠ 0`, `|D| < 2^96` and
`2^n + D = x^2`, then `n < 18 + 2 log₂ |D|`. -/
axiom beukers_cor2 (D : ℤ) (n : ℕ) (x : ℤ) (hD : D ≠ 0) (hDlt : |D| < 2 ^ 96)
    (h : (2 : ℤ) ^ n + D = x ^ 2) :
    (n : ℝ) < 18 + 2 * Real.logb 2 |(D : ℝ)|

/-- Szalay, Lemma 2 (Beukers). Let `p = 2^(2s+1)` be an odd power of `2`. Then for every
integer `x`, `|x / p^0.5 - 1| > 2^(-43.5) / p^0.9`. -/
axiom beukers_approx (s : ℕ) (x : ℤ) :
    (2 : ℝ) ^ (-43.5 : ℝ) / ((2 : ℝ) ^ (2 * s + 1)) ^ (0.9 : ℝ) <
      |(x : ℝ) / ((2 : ℝ) ^ (2 * s + 1)) ^ (0.5 : ℝ) - 1|

/-- Szalay, Lemma 3 (Beukers, Theorem 2), row `D₂ = 2^k - 1` with `k ≥ 4`: the solutions of
`2^n - D₂ = x^2` in positive integers are `(n, x) = (k, 1)` and `(2k - 2, 2^(k-1) - 1)`. -/
axiom beukers_thm2_mersenne (k n x : ℕ) (hk : 4 ≤ k) (hn : 0 < n) (hx : 0 < x)
    (h : (2 : ℤ) ^ n - (2 ^ k - 1) = (x : ℤ) ^ 2) :
    (n = k ∧ x = 1) ∨ (n = 2 * k - 2 ∧ x = 2 ^ (k - 1) - 1)

/-- Szalay, Lemma 3 (Beukers, Theorem 2), row `D₂ = 7` (Ramanujan–Nagell): the solutions of
`2^n - 7 = x^2` in positive integers are `(3,1), (4,3), (5,5), (7,11), (15,181)`. -/
axiom beukers_thm2_seven (n x : ℕ) (hn : 0 < n) (hx : 0 < x)
    (h : (2 : ℤ) ^ n - 7 = (x : ℤ) ^ 2) :
    (n, x) ∈ [(3, 1), (4, 3), (5, 5), (7, 11), (15, 181)]

end Szalay
