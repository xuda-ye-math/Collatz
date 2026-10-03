# Lean verification of Szalay's theorem (Lemma 4 of the paper)

Lean 4 (v4.33.1) with Mathlib v4.33.1. Build with `lake build`.

This formalizes L. Szalay, *The equations 2^N ± 2^M ± 2^L = z^2*, Indag. Math. (N.S.) 13 (2002),
131–142 (`../Szalay.pdf`), in the form used as Lemma 4 of the paper:

| Lean theorem | Statement |
|---|---|
| `Szalay.lemma4_i` | `2^a + 2^b + 1 = z^2` with `a ≥ b ≥ 1`, `z ≥ 1` iff `(a,b,z) = (2u, u+1, 2^u+1)`, `u ≥ 1`, or `(5,4,7)`, `(9,4,23)` |
| `Szalay.lemma4_ii` | `2^a - 2^b + 1 = z^2` with `a > b ≥ 1`, `z ≥ 1` iff `(a,b,z) = (2u, u+1, 2^u-1)`, `u ≥ 2`, or `(5,3,5)`, `(7,3,11)`, `(15,3,181)` |
| `Szalay.theorem1`, `Szalay.theorem2` | Szalay's Theorems 1 and 2 |

## Axioms

The results of Beukers (*On the generalized Ramanujan–Nagell equation I*, Acta Arith. 38 (1981))
that Szalay uses are stated as axioms in `Szalay/Beukers.lean`, as Szalay states them:

* `beukers_cor2`: Szalay's Lemma 1 (Beukers, Corollary 2);
* `beukers_approx`: Szalay's Lemma 2;
* `beukers_thm2_mersenne`, `beukers_thm2_seven`: the rows `D₂ = 2^k - 1` and `D₂ = 7`
  (Ramanujan–Nagell) of Szalay's Lemma 3 (Beukers, Theorem 2).

`#print axioms` gives, besides `propext`, `Classical.choice`, `Quot.sound`:
`lemma4_i` uses `beukers_cor2`, `beukers_approx`; `lemma4_ii` uses `beukers_cor2`,
`beukers_thm2_mersenne`, `beukers_thm2_seven`. There is no `sorry` and no `native_decide`;
the finite searches are checked by the kernel (`decide`).

## Departures from Szalay's text

* Lemma 8: Szalay writes out case A as a chain of substitutions and sketches case B. Theorem 1
  needs Lemma 8 only for `k ≥ 20`; `Szalay/Lemma8.lean` proves that range by a uniform argument
  with the truncated `2`-adic square roots of `1 + 4T`, `T = 2^(4k-2)`.
* Lemma 9 (Pell numbers): its single use, `2^(2m-1) + 2^m + 1 ≠ x^2`, is proved from Lemma 6
  (`no_sol_two_mul_sub_one`).
* The map `τ` in the proof of Theorem 1 is replaced by the equivalent case split of `n`
  against `2m - 2`.
* Lemma 2 is used in the integer form `2^(2s+1) < 2^425 c^10` (`Szalay/Approx.lean`), which gives
  `D < 32k + 435` instead of Szalay's `D < 32k + 430`; the conclusion `k ≤ 19` is unchanged.

# The paper's own results (library `Collatz`)

Orbits are `i ↦ F^[i] x₀`. "Enters the cycle of length `m` containing `y`" is
`(∃ i, F^[i] x₀ = y) ∧ Function.minimalPeriod F y = m`; "`x_i → ∞`" is
`Tendsto (fun i => F^[i] x₀) atTop atTop`; a bounded orbit is `BddAbove (Set.range …)`.

| Paper | Lean (`Collatz.…`) | Axioms besides `propext`, `Classical.choice`, `Quot.sound` |
|---|---|---|
| Lemma 5 | `key_solutions`, `key_minus` (i), `key_plus` (ii) | all four Beukers axioms; (i): `cor2`, `approx`; (ii): `cor2`, `thm2_mersenne`, `thm2_seven` |
| Theorem 1 (i), (ii) | `theorem1_i`, `theorem1_ii` | none |
| Theorem 1 (iii) | `theorem1_iii` | `cor2`, `approx` |
| Theorem 2 (i)–(iii) | `theorem2_i`, `theorem2_ii`, `theorem2_iii` | none |
| Theorem 2 (iv) | `theorem2_iv` | `cor2`, `thm2_mersenne`, `thm2_seven` |
| Theorem 3 (i) | `theorem3_i` | none |
| Theorem 3 (ii) | `theorem3_ii` | all four |
| Corollary 1 (i) | `corollary1_i_Qm`, `corollary1_i_Qp` | as Theorems 1 (iii), 2 (iv) |
| Corollary 1 (ii) | `corollary1_ii` | all four |
| Corollary 1 (iii), (iv) | `corollary1_iii`, `corollary1_iv` | as Theorems 1 (iii), 2 (iv) |
| Corollary 1 (iii) without Lemma 4 (Section 5) | `corollary1_iii_elementary` | none |
| Theorem 4 (i), (ii) | `theorem4_i`, `theorem4_ii` | none |
| Density `0` without Lemma 4 (Section 5) | `density_zero` | none |

The unbounded cases use one argument for the three maps (`Collatz.tendsto_of_oddStep`): an
invariant on the odd part (at least `3`, not terminal, not exceptional) is preserved, and the
odd part strictly increases at every odd term. This is the content of the paper's Lemmas 1–3.

The density proof needs `∑ 1/p = ∞` over the primes `p ≡ 7 (mod 8)` (`not_summable_recip7`).
The paper takes it from the prime number theorem for arithmetic progressions; here it is
derived from Mathlib's form of Dirichlet's theorem
(`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`).
