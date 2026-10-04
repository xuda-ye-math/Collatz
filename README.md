# Classification of the orbits of three quadratic Collatz-type maps

The paper studies three maps on the non-negative integers. Each of them halves an even number, and they send an odd `n` to `n(n-1)/2`, to `n(n+1)/2` and to `(n^2 - 1)/4`, respectively. For each map, it determines exactly the initial values with bounded orbits. The results are verified in Lean 4.

## Paper

`Paper/` contains the LaTeX source `main.tex`, the bibliography `references.bib` and the compiled `main.pdf`.

## Lean

`Lean/` contains the Lean 4 verification (Lean and Mathlib v4.33.1). Build it with `lake build` in `Lean/`. It has two libraries:

* `Szalay`: Szalay's theorem on `2^a ± 2^b + 1 = z^2`, which is Lemma 4 of the paper. The results of Beukers used by Szalay are stated as axioms.
* `Collatz`: the paper's own results (Theorems 1–4, Lemma 5, Corollary 1 and the density statement of Section 5).

There is no `sorry` and no `native_decide`. `Lean/README.md` maps each result of the paper to its Lean theorem and lists the axioms each one uses.

## Szalay

`Szalay.pdf` is L. Szalay, *The equations 2^N ± 2^M ± 2^L = z^2*, Indagationes Mathematicae (N.S.) 13 (2002), 131–142. It is the source of Lemma 4 of the paper and of the Lean library `Szalay`.
