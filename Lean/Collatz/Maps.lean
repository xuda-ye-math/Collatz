import Mathlib

/-!
# The maps `Q_-`, `Q_+`, `S` and general facts on their orbits

The orbit of `x₀` under `F` is `i ↦ F^[i] x₀`.

`tendsto_of_inv` is the common form of the paper's Lemmas 1 and 2 (ii): if an invariant `Inv`
holds along the orbit, even terms are halved, and at each odd term `n` the odd part of `F n`
exceeds `n`, then the orbit tends to infinity.
-/

namespace Collatz

open Filter

/-- `Q_-(n) = n / 2` for even `n` and `n (n - 1) / 2` for odd `n`. -/
def Qm (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else n * (n - 1) / 2

/-- `Q_+(n) = n / 2` for even `n` and `n (n + 1) / 2` for odd `n`. -/
def Qp (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else n * (n + 1) / 2

/-- `S(n) = n / 2` for even `n` and `(n^2 - 1) / 4` for odd `n`. -/
def S (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (n ^ 2 - 1) / 4

theorem Qm_even {n : ℕ} (h : n % 2 = 0) : Qm n = n / 2 := by simp [Qm, h]
theorem Qp_even {n : ℕ} (h : n % 2 = 0) : Qp n = n / 2 := by simp [Qp, h]
theorem S_even {n : ℕ} (h : n % 2 = 0) : S n = n / 2 := by simp [S, h]
theorem Qm_odd {n : ℕ} (h : n % 2 = 1) : Qm n = n * (n - 1) / 2 := by simp [Qm, h]
theorem Qp_odd {n : ℕ} (h : n % 2 = 1) : Qp n = n * (n + 1) / 2 := by simp [Qp, h]
theorem S_odd {n : ℕ} (h : n % 2 = 1) : S n = (n ^ 2 - 1) / 4 := by simp [S, h]

/-- The odd part of `n`. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ n.factorization 2

theorem oddPart_le (n : ℕ) : oddPart n ≤ n := Nat.div_le_self _ _

theorem oddPart_two_pow_mul (l y : ℕ) (hy : y % 2 = 1) : oddPart (2 ^ l * y) = y := by
  have hy0 : y ≠ 0 := by omega
  have hf : (2 ^ l * y).factorization 2 = l := by
    rw [Nat.factorization_mul (by positivity) hy0, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by omega)]
    simp
  rw [oddPart, hf, Nat.mul_div_cancel_left _ (by positivity)]

/-- `l` halvings take `2^l c` to `c`. -/
theorem iterate_halve (F : ℕ → ℕ) (hF : ∀ n, n % 2 = 0 → F n = n / 2) (l c : ℕ) :
    F^[l] (2 ^ l * c) = c := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply]
    have : F (2 ^ (l + 1) * c) = 2 ^ l * c := by
      rw [hF _ (by rw [pow_succ]; simp [Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm 2]), pow_succ]
      rw [Nat.mul_comm (2 ^ l) 2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this, ih]

/-- Every `n ≥ 1` is `2^l y` with `y` odd. -/
theorem exists_two_pow_mul_odd {n : ℕ} (hn : n ≠ 0) : ∃ l y, n = 2 ^ l * y ∧ y % 2 = 1 := by
  obtain ⟨l, y, hy, h⟩ := Nat.exists_eq_two_pow_mul_odd hn
  exact ⟨l, y, h, Nat.odd_iff.mp hy⟩

/-- The odd terms are reached: from a term satisfying `Inv`, some later term is odd. -/
theorem exists_odd_iterate (F : ℕ → ℕ) (Inv : ℕ → Prop) (hInv : ∀ n, Inv n → Inv (F n))
    (hdesc : ∀ n, Inv n → n % 2 = 0 → F n < n) :
    ∀ n, Inv n → ∃ t, (F^[t] n) % 2 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · obtain ⟨t, ht⟩ := ih (F n) (hdesc n hn h0) (hInv n hn)
      exact ⟨t + 1, by rw [Function.iterate_succ_apply]; exact ht⟩
    · exact ⟨0, h1⟩

/-- **Orbits that tend to infinity.** -/
theorem tendsto_of_inv (F : ℕ → ℕ) (Inv : ℕ → Prop) (φ : ℕ → ℕ)
    (hInv : ∀ n, Inv n → Inv (F n))
    (heven : ∀ n, Inv n → n % 2 = 0 → F n < n ∧ φ (F n) = φ n)
    (hodd : ∀ n, Inv n → n % 2 = 1 → n < φ (F n))
    (hle : ∀ n, Inv n → φ n ≤ n) (x₀ : ℕ) (h₀ : Inv x₀) :
    Tendsto (fun i => F^[i] x₀) atTop atTop := by
  have hinv : ∀ i, Inv (F^[i] x₀) := by
    intro i
    induction i with
    | zero => exact h₀
    | succ i ih => rw [Function.iterate_succ_apply']; exact hInv _ ih
  have hstep : ∀ i, φ (F^[i] x₀) ≤ φ (F^[i + 1] x₀) := by
    intro i
    rw [Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (F^[i] x₀) with h0 | h1
    · exact ((heven _ (hinv i) h0).2).ge
    · exact ((hle _ (hinv i)).trans (hodd _ (hinv i) h1).le)
  have hmono : ∀ i t, φ (F^[i] x₀) ≤ φ (F^[i + t] x₀) := by
    intro i t
    induction t with
    | zero => simp
    | succ t ih => exact ih.trans (by rw [← add_assoc]; exact hstep _)
  have hunb : ∀ B, ∃ i, B ≤ φ (F^[i] x₀) := by
    intro B
    induction B with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ B ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨t, ht⟩ := exists_odd_iterate F Inv hInv (fun n hn h0 => (heven n hn h0).1)
        (F^[i] x₀) (hinv i)
      rw [← Function.iterate_add_apply, add_comm] at ht
      refine ⟨i + t + 1, ?_⟩
      have h1 := hmono i t
      have h2 := hle _ (hinv (i + t))
      have h3 := hodd _ (hinv (i + t)) ht
      rw [Function.iterate_succ_apply']
      omega
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨N, hN⟩ := hunb B
  refine ⟨N, fun a ha => ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ha
  exact (hN.trans (hmono N t)).trans (hle _ (hinv _))

/-- A point `y` with `F^[m] y = y` and `F^[t] y ≠ y` for `0 < t < m` has minimal period `m`. -/
theorem minimalPeriod_eq (F : ℕ → ℕ) (y m : ℕ) (hm : 0 < m) (hper : F^[m] y = y)
    (hne : ∀ t, 0 < t → t < m → F^[t] y ≠ y) : Function.minimalPeriod F y = m := by
  have hp : Function.IsPeriodicPt F m y := hper
  have hle := hp.minimalPeriod_le hm
  have hpos := hp.minimalPeriod_pos hm
  by_contra hne'
  exact hne _ hpos (lt_of_le_of_ne hle hne') (Function.isPeriodicPt_minimalPeriod F y)

/-- An odd number of the form `2^l y` has `l = 0`. -/
theorem eq_zero_of_odd_two_pow_mul {l y : ℕ} (h : (2 ^ l * y) % 2 = 1) : l = 0 := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have : (2 ^ (l' + 1) * y) % 2 = 0 := by
      rw [pow_succ, mul_comm (2 ^ l') 2, mul_assoc]; exact Nat.mul_mod_right 2 _
    omega

/-- One halving of `2^(l+1) y`. -/
theorem halve_two_pow_succ_mul (F : ℕ → ℕ) (hF : ∀ n, n % 2 = 0 → F n = n / 2) (l y : ℕ) :
    F (2 ^ (l + 1) * y) = 2 ^ l * y := by
  have h0 : (2 ^ (l + 1) * y) % 2 = 0 := by
    rw [pow_succ, mul_comm (2 ^ l) 2, mul_assoc]; exact Nat.mul_mod_right 2 _
  rw [hF _ h0, pow_succ, mul_comm (2 ^ l) 2, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **Orbits that tend to infinity, in terms of odd steps.** Let `P` be a property of odd
numbers `y ≥ 1`. If each odd `y` with `P y` is sent by `F` to `2^j y'` with `y'` odd, `P y'`
and `y < y'`, then the orbit of every `2^l y` with `y` odd and `P y` tends to infinity. -/
theorem tendsto_of_oddStep (F : ℕ → ℕ) (hF : ∀ n, n % 2 = 0 → F n = n / 2) (P : ℕ → Prop)
    (hP1 : ∀ y, P y → 1 ≤ y)
    (hstep : ∀ y, y % 2 = 1 → P y → ∃ j y', F y = 2 ^ j * y' ∧ y' % 2 = 1 ∧ P y' ∧ y < y')
    (x₀ l y : ℕ) (hx : x₀ = 2 ^ l * y) (hy : y % 2 = 1) (hPy : P y) :
    Tendsto (fun i => F^[i] x₀) atTop atTop := by
  have hsucc : ∀ l y, y % 2 = 1 → (2 ^ l * y) % 2 = 0 → ∃ l', l = l' + 1 := by
    intro l y hy h0
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at h0; omega
    · exact ⟨l - 1, by omega⟩
  apply tendsto_of_inv F (fun n => ∃ l y, n = 2 ^ l * y ∧ y % 2 = 1 ∧ P y) oddPart
  · rintro n ⟨l, y, rfl, hy, hP⟩
    rcases Nat.mod_two_eq_zero_or_one (2 ^ l * y) with h0 | h1
    · obtain ⟨l', rfl⟩ := hsucc l y hy h0
      exact ⟨l', y, halve_two_pow_succ_mul F hF l' y, hy, hP⟩
    · have := eq_zero_of_odd_two_pow_mul h1
      subst this
      obtain ⟨j, y', hFy, hy', hP', -⟩ := hstep y hy hP
      exact ⟨j, y', by rw [pow_zero, one_mul]; exact hFy, hy', hP'⟩
  · rintro n ⟨l, y, rfl, hy, hP⟩ h0
    obtain ⟨l', rfl⟩ := hsucc l y hy h0
    rw [halve_two_pow_succ_mul F hF l' y, oddPart_two_pow_mul _ _ hy,
      oddPart_two_pow_mul _ _ hy]
    refine ⟨?_, rfl⟩
    have := hP1 y hP
    have : 0 < 2 ^ l' := by positivity
    rw [pow_succ]
    nlinarith
  · rintro n ⟨l, y, rfl, hy, hP⟩ h1
    have := eq_zero_of_odd_two_pow_mul h1
    subst this
    obtain ⟨j, y', hFy, hy', -, hlt⟩ := hstep y hy hP
    rw [pow_zero, one_mul, hFy, oddPart_two_pow_mul _ _ hy']
    exact hlt
  · intro n _; exact oddPart_le n
  · exact ⟨l, y, hx, hy, hPy⟩

end Collatz
