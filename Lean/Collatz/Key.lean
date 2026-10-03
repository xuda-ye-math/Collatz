import Szalay.Theorem1
import Szalay.Theorem2

/-!
# The paper's Lemma 5: the solutions of the key equation

`k (2^j k + ε) = 2^m + δ` with `j, m ≥ 1`, `k ≥ 3` and `ε, δ ∈ {-1, 1}` has exactly the
solutions `(j, k, ε, m, δ) = (1, 3, -1, 4, -1), (2, 3, -1, 5, 1), (1, 45, 1, 12, -1)`.
As in the paper, completing the square gives `(2^(j+1) k + ε)^2 = 2^(m+j+2) + δ 2^(j+2) + 1`,
and Szalay's theorems (`Szalay.lemma4_i`, `Szalay.lemma4_ii`) list the squares of this form.
The parity of `k`, assumed in the paper, is not needed.
-/

namespace Collatz

theorem key_square (j m : ℕ) (k ε δ : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : k * (2 ^ j * k + ε) = 2 ^ m + δ) :
    (2 ^ (j + 1) * k + ε) ^ 2 = 2 ^ (m + j + 2) + δ * 2 ^ (j + 2) + 1 := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e : (2 ^ (j + 1) * k + ε) ^ 2 = 2 ^ (j + 2) * (k * (2 ^ j * k + ε)) + ε ^ 2 := by ring
  rw [e, h, hε2]; ring

/-- The paper's Lemma 5 for `δ = 1`; it uses Szalay's Theorem 1 only. -/
theorem key_solutions_plus (j m : ℕ) (k ε : ℤ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hk : 3 ≤ k)
    (hε : ε = 1 ∨ ε = -1) (h : k * (2 ^ j * k + ε) = 2 ^ m + 1) :
    (j, k, ε, m) = (2, 3, -1, 5) := by
  have hsq := key_square j m k ε 1 hε h
  have h4 : (4 : ℤ) ≤ 2 ^ (j + 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hzpos : 0 < 2 ^ (j + 1) * k + ε := by rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨zN, hzN⟩ : ∃ zN : ℕ, (zN : ℤ) = 2 ^ (j + 1) * k + ε :=
    ⟨(2 ^ (j + 1) * k + ε).toNat, Int.toNat_of_nonneg hzpos.le⟩
  have hzN0 : 0 < zN := by omega
  have hE : (2 : ℤ) ^ (m + j + 2) + 2 ^ (j + 2) + 1 = (zN : ℤ) ^ 2 := by rw [hzN, hsq]; ring
  rcases (Szalay.lemma4_i (m + j + 2) (j + 2) zN (by omega) (by omega) hzN0).mp hE with
    ⟨u, -, -, hb, hzu⟩ | hL
  · exfalso
    have hu : u = j + 1 := by omega
    subst hu
    have e : (zN : ℤ) = 2 ^ (j + 1) + 1 := by rw [hzu]; push_cast; ring
    rw [hzN] at e
    have : (2 : ℤ) ^ (j + 1) * (k - 1) = 1 - ε := by linarith
    rcases hε with rfl | rfl <;> nlinarith
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hL
    rcases hL with ⟨ha, hb, hzv⟩ | ⟨ha, hb, hzv⟩
    · exfalso
      have hj2 : j = 2 := by omega
      subst hj2
      rw [hzv] at hzN; push_cast at hzN
      rcases hε with rfl | rfl <;> omega
    · have hj2 : j = 2 := by omega
      have hm5 : m = 5 := by omega
      subst hj2 hm5
      rw [hzv] at hzN; push_cast at hzN
      rcases hε with rfl | rfl
      · omega
      · have : k = 3 := by omega
        subst this
        rfl

/-- The paper's Lemma 5 for `δ = -1`; it uses Szalay's Theorem 2 only. -/
theorem key_solutions_minus (j m : ℕ) (k ε : ℤ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hk : 3 ≤ k)
    (hε : ε = 1 ∨ ε = -1) (h : k * (2 ^ j * k + ε) = 2 ^ m + -1) :
    (j, k, ε, m) = (1, 3, -1, 4) ∨ (j, k, ε, m) = (1, 45, 1, 12) := by
  have hsq := key_square j m k ε (-1) hε h
  have h4 : (4 : ℤ) ≤ 2 ^ (j + 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hzpos : 0 < 2 ^ (j + 1) * k + ε := by rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨zN, hzN⟩ : ∃ zN : ℕ, (zN : ℤ) = 2 ^ (j + 1) * k + ε :=
    ⟨(2 ^ (j + 1) * k + ε).toNat, Int.toNat_of_nonneg hzpos.le⟩
  have hzN0 : 0 < zN := by omega
  have hE : (2 : ℤ) ^ (m + j + 2) - 2 ^ (j + 2) + 1 = (zN : ℤ) ^ 2 := by rw [hzN, hsq]; ring
  rcases (Szalay.lemma4_ii (m + j + 2) (j + 2) zN (by omega) (by omega) hzN0).mp hE with
    ⟨u, -, -, hb, hzu⟩ | hL
  · exfalso
    have hu : u = j + 1 := by omega
    subst hu
    have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    have e : (zN : ℤ) = 2 ^ (j + 1) - 1 := by rw [hzu]; push_cast [Nat.cast_sub h1]; ring
    rw [hzN] at e
    have : (2 : ℤ) ^ (j + 1) * (k - 1) = -1 - ε := by linarith
    rcases hε with rfl | rfl <;> nlinarith
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hL
    rcases hL with ⟨ha, hb, hzv⟩ | ⟨ha, hb, hzv⟩ | ⟨ha, hb, hzv⟩
    · exfalso
      have hj1 : j = 1 := by omega
      subst hj1
      rw [hzv] at hzN; push_cast at hzN
      rcases hε with rfl | rfl <;> omega
    · have hj1 : j = 1 := by omega
      have hm4 : m = 4 := by omega
      subst hj1 hm4
      rw [hzv] at hzN; push_cast at hzN
      rcases hε with rfl | rfl
      · omega
      · have : k = 3 := by omega
        subst this
        left; rfl
    · have hj1 : j = 1 := by omega
      have hm12 : m = 12 := by omega
      subst hj1 hm12
      rw [hzv] at hzN; push_cast at hzN
      rcases hε with rfl | rfl
      · have : k = 45 := by omega
        subst this
        right; rfl
      · omega


/-- **The paper's Lemma 5.** -/
theorem key_solutions (j m : ℕ) (k ε δ : ℤ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hk : 3 ≤ k)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) (h : k * (2 ^ j * k + ε) = 2 ^ m + δ) :
    (j, k, ε, m, δ) = (1, 3, -1, 4, -1) ∨ (j, k, ε, m, δ) = (2, 3, -1, 5, 1) ∨
      (j, k, ε, m, δ) = (1, 45, 1, 12, -1) := by
  rcases hδ with rfl | rfl
  · have := key_solutions_plus j m k ε hj hm hk hε h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    right; left; rfl
  · rcases key_solutions_minus j m k ε hj hm hk hε h with h1 | h1 <;>
      simp only [Prod.mk.injEq] at h1 <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    · left; rfl
    · right; right; rfl

/-- The three identities of the paper's display of solutions. -/
theorem key_solutions_hold :
    (3 : ℤ) * (2 ^ 1 * 3 + -1) = 2 ^ 4 + -1 ∧ (3 : ℤ) * (2 ^ 2 * 3 + -1) = 2 ^ 5 + 1 ∧
      (45 : ℤ) * (2 ^ 1 * 45 + 1) = 2 ^ 12 + -1 := by norm_num

/-- **The paper's Lemma 5 (i).** `k (2^j k + 1) = 2^m + 1` has no solution. -/
theorem key_minus (j m k : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hk : 3 ≤ k)
    (h : k * (2 ^ j * k + 1) = 2 ^ m + 1) : False := by
  have := key_solutions_plus j m k 1 hj hm (by exact_mod_cast hk) (Or.inl rfl)
    (by exact_mod_cast h)
  simp at this

/-- **The paper's Lemma 5 (ii).** The only solution of `k (2^j k - 1) = 2^m - 1` is
`(j, k, m) = (1, 3, 4)`. -/
theorem key_plus (j m k : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hk : 3 ≤ k)
    (h : (k : ℤ) * (2 ^ j * k - 1) = 2 ^ m - 1) : j = 1 ∧ k = 3 ∧ m = 4 := by
  have := key_solutions_minus j m k (-1) hj hm (by exact_mod_cast hk) (Or.inr rfl)
    (by rw [show (2 : ℤ) ^ j * k + -1 = 2 ^ j * k - 1 by ring,
      show (2 : ℤ) ^ m + -1 = 2 ^ m - 1 by ring]; exact h)
  simp only [Prod.mk.injEq] at this
  rcases this with ⟨h1, h2, -, h4⟩ | ⟨-, -, h3, -⟩
  · exact ⟨h1, by exact_mod_cast h2, h4⟩
  · norm_num at h3

end Collatz
