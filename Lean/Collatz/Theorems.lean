import Collatz.Maps
import Collatz.Key

/-!
# The paper's Theorems 1, 2 and 3

Orbits are `i ↦ F^[i] x₀`. "The orbit enters the cycle of length `m` that contains `y`" is
stated as `∃ i, F^[i] x₀ = y` together with `Function.minimalPeriod F y = m`, and
"`x_i → ∞`" as `Tendsto (fun i => F^[i] x₀) atTop atTop`.

The unbounded cases use `tendsto_of_oddStep`. The odd step of each map is the paper's Lemma 1;
that the next odd term is again not terminal (and, under `Q_+` and `S`, not exceptional) is the
paper's Lemma 3 combined with Lemma 5.
-/

namespace Collatz

open Filter

theorem odd_two_pow_mul_add_one (j k : ℕ) (hj : 1 ≤ j) : (2 ^ j * k + 1) % 2 = 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [pow_succ, mul_comm (2 ^ i) 2, mul_assoc]; omega

theorem odd_mul' {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) : (a * b) % 2 = 1 := by
  rw [Nat.mul_mod, ha, hb]

/-- Decomposition of an odd `y ≥ 3`: `y - 1 = 2^j k` with `j ≥ 1` and `k` odd. -/
theorem decomp_sub_one {y : ℕ} (hy : y % 2 = 1) (h3 : 3 ≤ y) :
    ∃ j k, 1 ≤ j ∧ k % 2 = 1 ∧ y = 2 ^ j * k + 1 := by
  obtain ⟨j, k, hk, hyk⟩ := Nat.exists_eq_two_pow_mul_odd (n := y - 1) (by omega)
  have hk' := Nat.odd_iff.mp hk
  refine ⟨j, k, ?_, hk', by omega⟩
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0; simp at hyk; omega
  · exact h0

/-- Decomposition of an odd `y`: `y + 1 = 2^j k` with `j ≥ 1` and `k` odd. -/
theorem decomp_add_one {y : ℕ} (hy : y % 2 = 1) :
    ∃ j k, 1 ≤ j ∧ k % 2 = 1 ∧ y + 1 = 2 ^ j * k := by
  obtain ⟨j, k, hk, hyk⟩ := Nat.exists_eq_two_pow_mul_odd (n := y + 1) (by omega)
  have hk' := Nat.odd_iff.mp hk
  refine ⟨j, k, ?_, hk', hyk⟩
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0; simp at hyk; omega
  · exact h0

/-! ### Odd steps (the paper's Lemma 1) -/

theorem Qm_step (y j k : ℕ) (hj : 1 ≤ j) (hy : y = 2 ^ j * k + 1) :
    Qm y = 2 ^ (j - 1) * (k * y) := by
  have hodd : y % 2 = 1 := by rw [hy]; exact odd_two_pow_mul_add_one j k hj
  rw [Qm_odd hodd, show y - 1 = 2 ^ j * k by omega]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show y * (2 ^ (i + 1) * k) = 2 * (2 ^ i * (k * y)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num), Nat.add_sub_cancel]

theorem Qp_step (y j k : ℕ) (hj : 1 ≤ j) (hy : y + 1 = 2 ^ j * k) (hodd : y % 2 = 1) :
    Qp y = 2 ^ (j - 1) * (k * y) := by
  rw [Qp_odd hodd, hy]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show y * (2 ^ (i + 1) * k) = 2 * (2 ^ i * (k * y)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num), Nat.add_sub_cancel]

theorem S_step_plus (y j k : ℕ) (hj : 1 ≤ j) (hy : y = 2 ^ (j + 1) * k + 1) :
    S y = 2 ^ j * (k * (2 ^ j * k + 1)) := by
  have hodd : y % 2 = 1 := by rw [hy]; exact odd_two_pow_mul_add_one (j + 1) k (by omega)
  have e : y ^ 2 = 4 * (2 ^ j * (k * (2 ^ j * k + 1))) + 1 := by rw [hy]; ring
  rw [S_odd hodd, e, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num)]

theorem S_step_minus (y j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hy : y + 1 = 2 ^ (j + 1) * k) :
    S y = 2 ^ j * (k * (2 ^ j * k - 1)) := by
  obtain ⟨w, hw⟩ : ∃ w, 2 ^ j * k = w + 1 := ⟨2 ^ j * k - 1, by
    have : 1 ≤ 2 ^ j * k := Nat.one_le_iff_ne_zero.mpr (by positivity); omega⟩
  have hy' : y = 2 * w + 1 := by
    have : 2 ^ (j + 1) * k = 2 * (2 ^ j * k) := by ring
    omega
  have hodd : y % 2 = 1 := by omega
  have e : y ^ 2 = 4 * (2 ^ j * (k * w)) + 1 := by
    rw [hy', show 2 ^ j * (k * w) = (2 ^ j * k) * w by ring, hw]; ring
  rw [S_odd hodd, e, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num), hw,
    Nat.add_sub_cancel]

/-! ### Theorem 1 (`Q_-`) -/

theorem Qm_zero : Qm 0 = 0 := by decide

/-- **Theorem 1 (i).** -/
theorem theorem1_i (x₀ : ℕ) (h : x₀ = 0 ∨ ∃ l, x₀ = 2 ^ l) :
    Function.IsFixedPt Qm 0 ∧ ∃ i, Qm^[i] x₀ = 0 := by
  refine ⟨Qm_zero, ?_⟩
  rcases h with rfl | ⟨l, rfl⟩
  · exact ⟨0, rfl⟩
  · refine ⟨l + 1, ?_⟩
    rw [Function.iterate_succ_apply', show 2 ^ l = 2 ^ l * 1 by ring,
      iterate_halve Qm (fun n hn => Qm_even hn) l 1]
    decide

/-- A point `y ≥ 1` with `F y = 2^(m-1) y`, `m ≥ 1`, lies on a cycle of length `m`. -/
theorem minimalPeriod_of_step (F : ℕ → ℕ) (hF : ∀ n, n % 2 = 0 → F n = n / 2) (y m : ℕ)
    (hm : 1 ≤ m) (hy : 1 ≤ y) (hstep : F y = 2 ^ (m - 1) * y) :
    Function.minimalPeriod F y = m := by
  have hiter : ∀ t, t ≤ m - 1 → F^[t + 1] y = 2 ^ (m - 1 - t) * y := by
    intro t ht
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le ht
    rw [Function.iterate_succ_apply, hstep, hs, pow_add, mul_assoc, iterate_halve F hF t,
      Nat.add_sub_cancel_left]
  apply minimalPeriod_eq F y m (by omega)
  · have := hiter (m - 1) le_rfl
    rwa [show m - 1 + 1 = m by omega, Nat.sub_self, pow_zero, one_mul] at this
  · intro t ht0 htm
    have := hiter (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at this
    rw [this]
    intro heq
    have h2 : 2 ≤ 2 ^ (m - 1 - (t - 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m - 1 - (t - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith

/-- **Theorem 1 (ii).** -/
theorem theorem1_ii (l m : ℕ) (hm : 1 ≤ m) :
    (∃ i, Qm^[i] (2 ^ l * (2 ^ m + 1)) = 2 ^ m + 1) ∧
      Function.minimalPeriod Qm (2 ^ m + 1) = m := by
  refine ⟨⟨l, iterate_halve Qm (fun n hn => Qm_even hn) l _⟩, ?_⟩
  apply minimalPeriod_of_step Qm (fun n hn => Qm_even hn) _ m hm (Nat.le_add_left 1 _)
  rw [Qm_step (2 ^ m + 1) m 1 hm (by ring), one_mul]

/-- The invariant of Theorem 1 (iii): odd, at least `3`, not a terminal number `2^m + 1`. -/
def PQm (y : ℕ) : Prop := 3 ≤ y ∧ ∀ m, y ≠ 2 ^ m + 1

theorem Qm_oddStep (y : ℕ) (hy : y % 2 = 1) (hP : PQm y) :
    ∃ j y', Qm y = 2 ^ j * y' ∧ y' % 2 = 1 ∧ PQm y' ∧ y < y' := by
  obtain ⟨h3, hterm⟩ := hP
  obtain ⟨j, k, hj, hk, hyk⟩ := decomp_sub_one hy h3
  have hk3 : 3 ≤ k := by
    have : k ≠ 1 := by rintro rfl; exact hterm j (by rw [hyk]; ring)
    omega
  refine ⟨j - 1, k * y, Qm_step y j k hj hyk, odd_mul' hk hy, ⟨by nlinarith, ?_⟩, by nlinarith⟩
  intro m hm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hm; nlinarith
    · exact h0
  exact key_minus j m k hj hm1 hk3 (by rw [← hyk]; exact hm)

/-- **Theorem 1 (iii).** -/
theorem theorem1_iii (x₀ : ℕ)
    (h : ¬(x₀ = 0 ∨ (∃ l, x₀ = 2 ^ l) ∨ ∃ l m, 1 ≤ m ∧ x₀ = 2 ^ l * (2 ^ m + 1))) :
    Tendsto (fun i => Qm^[i] x₀) atTop atTop := by
  push_neg at h
  obtain ⟨h0, hpow, hterm⟩ := h
  obtain ⟨l, q, hx, hq⟩ := exists_two_pow_mul_odd h0
  apply tendsto_of_oddStep Qm (fun n hn => Qm_even hn) PQm (fun y hy => by have := hy.1; omega)
    Qm_oddStep x₀ l q hx hq
  refine ⟨?_, fun m hm => ?_⟩
  · have : q ≠ 1 := by rintro rfl; exact hpow l (by rw [hx, mul_one])
    omega
  · rcases Nat.eq_zero_or_pos m with h0' | h0'
    · subst h0'; simp at hm; omega
    · exact hterm l m h0' (by rw [hx, hm])

/-! ### Theorem 2 (`Q_+`) -/

theorem Qp_zero : Qp 0 = 0 := by decide

/-- **Theorem 2 (i).** -/
theorem theorem2_i : Function.IsFixedPt Qp 0 ∧ ∀ i, Qp^[i] 0 = 0 :=
  ⟨Qp_zero, fun i => Function.iterate_fixed Qp_zero i⟩

/-- **Theorem 2 (ii).** For `m = 1` the cycle is the fixed point `1`. -/
theorem theorem2_ii (l m : ℕ) (hm : 1 ≤ m) :
    (∃ i, Qp^[i] (2 ^ l * (2 ^ m - 1)) = 2 ^ m - 1) ∧
      Function.minimalPeriod Qp (2 ^ m - 1) = m := by
  refine ⟨⟨l, iterate_halve Qp (fun n hn => Qp_even hn) l _⟩, ?_⟩
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hodd : (2 ^ m - 1) % 2 = 1 := by
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]; omega
  apply minimalPeriod_of_step Qp (fun n hn => Qp_even hn) _ m hm (by omega)
  rw [Qp_step (2 ^ m - 1) m 1 hm (by omega) hodd, one_mul]

theorem Qp_one : Function.IsFixedPt Qp 1 := by decide

/-- **Theorem 2 (iii).** -/
theorem theorem2_iii (l : ℕ) :
    (∃ i, Qp^[i] (5 * 2 ^ l) = 15) ∧ Function.minimalPeriod Qp 15 = 4 ∧
      Qp 15 = 120 ∧ Qp 120 = 60 ∧ Qp 60 = 30 ∧ Qp 30 = 15 := by
  refine ⟨⟨l + 1, ?_⟩, ?_, by decide, by decide, by decide, by decide⟩
  · rw [Function.iterate_succ_apply', mul_comm, iterate_halve Qp (fun n hn => Qp_even hn) l 5]
    decide
  · apply minimalPeriod_eq Qp 15 4 (by norm_num) (by decide)
    intro t ht0 ht4
    interval_cases t <;> decide

/-- The invariant of Theorem 2 (iv): odd, at least `3`, not `2^m - 1`, not `5`. -/
def PQp (y : ℕ) : Prop := 3 ≤ y ∧ (∀ m, y ≠ 2 ^ m - 1) ∧ y ≠ 5

theorem Qp_oddStep (y : ℕ) (hy : y % 2 = 1) (hP : PQp y) :
    ∃ j y', Qp y = 2 ^ j * y' ∧ y' % 2 = 1 ∧ PQp y' ∧ y < y' := by
  obtain ⟨h3, hterm, h5⟩ := hP
  obtain ⟨j, k, hj, hk, hyk⟩ := decomp_add_one hy
  have hk3 : 3 ≤ k := by
    have : k ≠ 1 := by rintro rfl; exact hterm j (by omega)
    omega
  refine ⟨j - 1, k * y, Qp_step y j k hj hyk hy, odd_mul' hk hy,
    ⟨by nlinarith, ?_, by nlinarith⟩, by nlinarith⟩
  intro m hm
  have h9 : 9 ≤ k * y := by nlinarith
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hm; omega
    · exact h0
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hZ : (k : ℤ) * (2 ^ j * k - 1) = 2 ^ m - 1 := by
    have e1 : ((k * y : ℕ) : ℤ) = ((2 ^ m - 1 : ℕ) : ℤ) := by rw [hm]
    have e2 : ((y + 1 : ℕ) : ℤ) = ((2 ^ j * k : ℕ) : ℤ) := by rw [hyk]
    push_cast [Nat.cast_sub h1] at e1 e2
    rw [← e1]; linear_combination (-(k : ℤ)) * e2
  obtain ⟨rfl, rfl, -⟩ := key_plus j m k hj hm1 hk3 hZ
  exact h5 (by omega)

/-- **Theorem 2 (iv).** -/
theorem theorem2_iv (x₀ : ℕ)
    (h : ¬(x₀ = 0 ∨ (∃ l m, 1 ≤ m ∧ x₀ = 2 ^ l * (2 ^ m - 1)) ∨ ∃ l, x₀ = 5 * 2 ^ l)) :
    Tendsto (fun i => Qp^[i] x₀) atTop atTop := by
  push_neg at h
  obtain ⟨h0, hterm, h5⟩ := h
  obtain ⟨l, q, hx, hq⟩ := exists_two_pow_mul_odd h0
  apply tendsto_of_oddStep Qp (fun n hn => Qp_even hn) PQp (fun y hy => by have := hy.1; omega)
    Qp_oddStep x₀ l q hx hq
  refine ⟨?_, fun m hm => ?_, ?_⟩
  · have : q ≠ 1 := by rintro rfl; exact hterm l 1 le_rfl (by rw [hx]; norm_num)
    omega
  · rcases Nat.eq_zero_or_pos m with h0' | h0'
    · subst h0'; simp at hm; omega
    · exact hterm l m h0' (by rw [hx, hm])
  · rintro rfl; exact h5 l (by rw [hx, mul_comm])

/-! ### Theorem 3 (`S`) -/

theorem S_zero : S 0 = 0 := by decide

theorem S_terminal_plus (m : ℕ) : S (2 ^ (m + 1) + 1) = 2 ^ m * (2 ^ m + 1) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; decide
  · rw [S_step_plus _ m 1 h0 (by ring)]; ring

theorem S_terminal_minus (m : ℕ) : S (2 ^ (m + 1) - 1) = 2 ^ m * (2 ^ m - 1) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; decide
  · have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    rw [S_step_minus _ m 1 h0 le_rfl (by omega)]; ring

/-- Under `S`, the orbit of every terminal number reaches `0`. -/
theorem S_terminal_reaches_zero (m : ℕ) :
    (∃ t, S^[t] (2 ^ m + 1) = 0) ∧ ∃ t, S^[t] (2 ^ m - 1) = 0 := by
  induction m with
  | zero => exact ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩
  | succ m ih =>
    obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := ih
    refine ⟨⟨t1 + m + 1, ?_⟩, ⟨t2 + m + 1, ?_⟩⟩
    · rw [Function.iterate_succ_apply, S_terminal_plus, Function.iterate_add_apply,
        iterate_halve S (fun n hn => S_even hn) m, ht1]
    · rw [Function.iterate_succ_apply, S_terminal_minus, Function.iterate_add_apply,
        iterate_halve S (fun n hn => S_even hn) m, ht2]

/-- The odd parts of `x₀` in Theorem 3 (i). -/
def BoundedS (q : ℕ) : Prop :=
  (∃ m, 1 ≤ m ∧ (q = 2 ^ m + 1 ∨ q = 2 ^ m - 1)) ∨ q = 11 ∨ q = 23 ∨ q = 181

/-- **Theorem 3 (i).** -/
theorem theorem3_i (x₀ : ℕ)
    (h : x₀ = 0 ∨ ∃ l q, x₀ = 2 ^ l * q ∧ q % 2 = 1 ∧ BoundedS q) :
    Function.IsFixedPt S 0 ∧ ∃ i, S^[i] x₀ = 0 := by
  refine ⟨S_zero, ?_⟩
  rcases h with rfl | ⟨l, q, rfl, -, hq⟩
  · exact ⟨0, rfl⟩
  · have hq0 : ∃ t, S^[t] q = 0 := by
      rcases hq with ⟨m, -, rfl | rfl⟩ | rfl | rfl | rfl
      · exact (S_terminal_reaches_zero m).1
      · exact (S_terminal_reaches_zero m).2
      · obtain ⟨t, ht⟩ := (S_terminal_reaches_zero 4).2
        exact ⟨t + 2, by rw [Function.iterate_add_apply, show S^[2] 11 = 2 ^ 4 - 1 by decide, ht]⟩
      · obtain ⟨t, ht⟩ := (S_terminal_reaches_zero 5).1
        exact ⟨t + 3, by rw [Function.iterate_add_apply, show S^[3] 23 = 2 ^ 5 + 1 by decide, ht]⟩
      · obtain ⟨t, ht⟩ := (S_terminal_reaches_zero 12).2
        exact ⟨t + 2, by
          rw [Function.iterate_add_apply, show S^[2] 181 = 2 ^ 12 - 1 by decide, ht]⟩
    obtain ⟨t, ht⟩ := hq0
    exact ⟨t + l, by rw [Function.iterate_add_apply, iterate_halve S (fun n hn => S_even hn), ht]⟩

/-- The invariant of Theorem 3 (ii): odd, at least `3`, not `2^m ± 1`, not `11, 23, 181`. -/
def PS (y : ℕ) : Prop :=
  3 ≤ y ∧ (∀ m, y ≠ 2 ^ m + 1 ∧ y ≠ 2 ^ m - 1) ∧ y ≠ 11 ∧ y ≠ 23 ∧ y ≠ 181

theorem not_prime_of_factor {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w) : ¬ (k * w).Prime :=
  Nat.not_prime_mul (by omega) (by omega)

/-- The next odd term `k w` of `S` with `k ≥ 3`, `w ≥ 2`, is not a terminal number. -/
theorem S_next_not_terminal (y j k : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hj : 1 ≤ j)
    (hk3 : 3 ≤ k) (hyZ : (y : ℤ) = 2 ^ (j + 1) * k + ε) (hy11 : y ≠ 11) (hy23 : y ≠ 23)
    (hy181 : y ≠ 181) (y' : ℕ) (h9 : 9 ≤ y') (hy'Z : (y' : ℤ) = k * (2 ^ j * k + ε)) (m : ℕ) :
    y' ≠ 2 ^ m + 1 ∧ y' ≠ 2 ^ m - 1 := by
  have hm1 : ∀ δ : ℤ, (y' : ℤ) = 2 ^ m + δ → (δ = 1 ∨ δ = -1) → 1 ≤ m := by
    intro δ hδ hδ'
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; rcases hδ' with rfl | rfl <;> norm_num at hδ <;> omega
    · exact h0
  have key : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → (y' : ℤ) ≠ 2 ^ m + δ := by
    intro δ hδ' hδ
    have := key_solutions j m k ε δ hj (hm1 δ hδ hδ') (by exact_mod_cast hk3) hε hδ'
      (by rw [← hy'Z, hδ])
    simp only [Prod.mk.injEq] at this
    rcases this with ⟨rfl, hk, rfl, -, -⟩ | ⟨rfl, hk, rfl, -, -⟩ | ⟨rfl, hk, rfl, -, -⟩
    · exact hy11 (by rw [hk] at hyZ; norm_num at hyZ; omega)
    · exact hy23 (by rw [hk] at hyZ; norm_num at hyZ; omega)
    · exact hy181 (by rw [hk] at hyZ; norm_num at hyZ; omega)
  constructor
  · intro h; exact key 1 (Or.inl rfl) (by rw [h]; push_cast; ring)
  · intro h
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact key (-1) (Or.inr rfl) (by rw [h]; push_cast [Nat.cast_sub h1]; ring)

theorem S_oddStep (y : ℕ) (hy : y % 2 = 1) (hP : PS y) :
    ∃ j y', S y = 2 ^ j * y' ∧ y' % 2 = 1 ∧ PS y' ∧ y < y' := by
  obtain ⟨h3, hterm, h11, h23, h181⟩ := hP
  have hprime : ∀ k w : ℕ, 3 ≤ k → 2 ≤ w → k * w ≠ 11 ∧ k * w ≠ 23 ∧ k * w ≠ 181 := by
    intro k w hk hw
    have hnp := not_prime_of_factor hk hw
    refine ⟨?_, ?_, ?_⟩ <;> intro he <;> rw [he] at hnp <;> exact hnp (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one (y / 2) with hq | hq
  · -- `y ≡ 1 (mod 4)`: `y = 2^(j+1) k + 1`, `S y = 2^j k (2^j k + 1)`.
    obtain ⟨J, k, hJ, hk, hyk⟩ := decomp_sub_one hy h3
    have hJ2 : 2 ≤ J := by
      by_contra hJ1
      have : J = 1 := by omega
      subst this
      omega
    obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    have hk3 : 3 ≤ k := by
      have : k ≠ 1 := by rintro rfl; exact (hterm (j + 1)).1 (by rw [hyk]; ring)
      omega
    have hw : 2 ≤ 2 ^ j * k + 1 := by
      have : 0 < 2 ^ j * k := Nat.mul_pos (by positivity) (by omega)
      omega
    have h2j : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    refine ⟨j, k * (2 ^ j * k + 1), S_step_plus y j k hj hyk,
      odd_mul' hk (odd_two_pow_mul_add_one j k hj), ⟨by nlinarith, fun m => ?_, hprime k _ hk3 hw⟩, ?_⟩
    · exact S_next_not_terminal y j k 1 (Or.inl rfl) hj hk3 (by rw [hyk]; push_cast; ring)
        h11 h23 h181 _ (by nlinarith) (by push_cast; ring) m
    · rw [hyk, pow_succ]; nlinarith
  · -- `y ≡ 3 (mod 4)`: `y + 1 = 2^(j+1) k`, `S y = 2^j k (2^j k - 1)`.
    obtain ⟨J, k, hJ, hk, hyk⟩ := decomp_add_one hy
    have hJ2 : 2 ≤ J := by
      by_contra hJ1
      have : J = 1 := by omega
      subst this
      omega
    obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    have hk3 : 3 ≤ k := by
      have : k ≠ 1 := by rintro rfl; exact (hterm (j + 1)).2 (by omega)
      omega
    have h2j : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have h6 : 6 ≤ 2 ^ j * k := by nlinarith
    have hwodd : (2 ^ j * k - 1) % 2 = 1 := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ, mul_comm (2 ^ i) 2, mul_assoc] at h6 ⊢; omega
    refine ⟨j, k * (2 ^ j * k - 1), S_step_minus y j k hj (by omega) hyk, odd_mul' hk hwodd,
      ⟨by have := Nat.mul_le_mul hk3 (show 1 ≤ 2 ^ j * k - 1 by omega); omega,
        fun m => ?_, hprime k _ hk3 (by omega)⟩, ?_⟩
    · have hc : ((2 ^ j * k - 1 : ℕ) : ℤ) = 2 ^ j * k - 1 := by
        push_cast [Nat.cast_sub (show 1 ≤ 2 ^ j * k by omega)]; ring
      exact S_next_not_terminal y j k (-1) (Or.inr rfl) hj hk3
        (by have : ((y + 1 : ℕ) : ℤ) = ((2 ^ (j + 1) * k : ℕ) : ℤ) := by rw [hyk]
            push_cast at this; linarith)
        h11 h23 h181 _ (by nlinarith) (by push_cast [hc]; ring) m
    · have e : y + 1 = 2 * (2 ^ j * k) := by rw [hyk]; ring
      have : y < k * (2 ^ j * k - 1) := by
        obtain ⟨w, hw⟩ : ∃ w, 2 ^ j * k = w + 1 := ⟨2 ^ j * k - 1, by omega⟩
        rw [hw, Nat.add_sub_cancel]
        rw [hw] at e h6
        have := Nat.mul_le_mul_right w hk3
        omega
      exact this

/-- **Theorem 3 (ii).** -/
theorem theorem3_ii (x₀ : ℕ)
    (h : ¬(x₀ = 0 ∨ ∃ l q, x₀ = 2 ^ l * q ∧ q % 2 = 1 ∧ BoundedS q)) :
    Tendsto (fun i => S^[i] x₀) atTop atTop := by
  push_neg at h
  obtain ⟨h0, hb⟩ := h
  obtain ⟨l, q, hx, hq⟩ := exists_two_pow_mul_odd h0
  have hnot := hb l q hx hq
  simp only [BoundedS, not_or, not_exists, not_and] at hnot
  obtain ⟨hterm, h11, h23, h181⟩ := hnot
  apply tendsto_of_oddStep S (fun n hn => S_even hn) PS (fun y hy => by have := hy.1; omega)
    S_oddStep x₀ l q hx hq
  refine ⟨?_, fun m => ⟨fun hm => ?_, fun hm => ?_⟩, h11, h23, h181⟩
  · have : q ≠ 1 := by rintro rfl; exact (hterm 1 le_rfl).2 (by norm_num)
    omega
  · rcases Nat.eq_zero_or_pos m with h0' | h0'
    · subst h0'; simp at hm; omega
    · exact (hterm m h0').1 hm
  · rcases Nat.eq_zero_or_pos m with h0' | h0'
    · subst h0'; simp at hm; omega
    · exact (hterm m h0').2 hm

end Collatz
