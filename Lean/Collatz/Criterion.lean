import Collatz.Maps

/-!
# The paper's Theorem 4 (ii)

An odd `y > 1` divides `2^m + 1` for some `m ≥ 1` if and only if there is `s ≥ 1` with
`v₂(ord_p(2)) = s` for every prime `p` dividing `y`. Here `ord_n(2) = orderOf (2 : ZMod n)`.

The proof follows the paper: for a prime power `p^e`, `p^e ∣ 2^m + 1` if and only if
`ord_{p^e}(2)` divides `2m` and not `m`; this is `v₂(m) = v₂(ord_{p^e}(2)) - 1` together with
`odd part of ord_{p^e}(2) ∣ m`; and `v₂(ord_{p^e}(2)) = v₂(ord_p(2))`. No external result is
used.
-/

namespace Collatz

/-- `ord_n(2)`, the multiplicative order of `2` modulo `n`. -/
noncomputable def ord2 (n : ℕ) : ℕ := orderOf (2 : ZMod n)

theorem modEq_one_iff_ord2_dvd (n k : ℕ) : 2 ^ k ≡ 1 [MOD n] ↔ ord2 n ∣ k := by
  rw [ord2, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one]

theorem dvd_two_pow_sub_one_iff (n k : ℕ) : n ∣ 2 ^ k - 1 ↔ ord2 n ∣ k := by
  rw [← modEq_one_iff_ord2_dvd, Nat.ModEq.comm, Nat.modEq_iff_dvd' Nat.one_le_two_pow]

theorem ord2_pos {n : ℕ} (hn : n % 2 = 1) : 0 < ord2 n := by
  have hc : Nat.Coprime 2 n := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hn)
  have h := (modEq_one_iff_ord2_dvd n _).mp (Nat.ModEq.pow_totient hc)
  rcases Nat.eq_zero_or_pos (ord2 n) with h0 | h0
  · rw [h0, zero_dvd_iff] at h
    have := Nat.totient_pos.mpr (show 0 < n by omega)
    omega
  · exact h0

theorem coprime_pow_two_of_odd {w : ℕ} (hw : w % 2 = 1) (a : ℕ) : Nat.Coprime (2 ^ a) w :=
  Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hw))

/-- `n = 2^(v₂ n) · oddPart n`, and `oddPart n` is odd. -/
theorem decomp (n : ℕ) (hn : n ≠ 0) :
    n = 2 ^ padicValNat 2 n * oddPart n ∧ oddPart n % 2 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [oddPart, ← Nat.factorization_def n Nat.prime_two, Nat.ordProj_mul_ordCompl_eq_self]
  · exact Nat.odd_iff.mp (Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hn))

theorem two_pow_mul_dvd_iff (a c u w : ℕ) (hu : u % 2 = 1) (hw : w % 2 = 1) :
    2 ^ a * u ∣ 2 ^ c * w ↔ a ≤ c ∧ u ∣ w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : 2 ^ a ∣ 2 ^ c * w := (Dvd.intro u rfl).trans h
      have h2 : 2 ^ a ∣ 2 ^ c := (coprime_pow_two_of_odd hw a).dvd_of_dvd_mul_right h1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    · have h1 : u ∣ 2 ^ c * w := (Dvd.intro_left _ rfl).trans h
      exact (coprime_pow_two_of_odd hu c).symm.dvd_of_dvd_mul_left h1
  · rintro ⟨hac, huw⟩
    exact mul_dvd_mul (pow_dvd_pow 2 hac) huw

/-- `o ∣ 2m` and `o ∤ m` if and only if `v₂ o = v₂ m + 1` and the odd part of `o` divides `m`. -/
theorem dvd_two_mul_not_dvd_iff (o m : ℕ) (ho : 0 < o) (hm : 0 < m) :
    (o ∣ 2 * m ∧ ¬ o ∣ m) ↔ (padicValNat 2 o = padicValNat 2 m + 1 ∧ oddPart o ∣ m) := by
  obtain ⟨eo, hu⟩ := decomp o ho.ne'
  obtain ⟨em, hw⟩ := decomp m hm.ne'
  set a := padicValNat 2 o
  set b := padicValNat 2 m
  set u := oddPart o
  set w := oddPart m
  have h2m : 2 * m = 2 ^ (b + 1) * w := by rw [em, pow_succ]; ring
  have hd1 : o ∣ 2 * m ↔ a ≤ b + 1 ∧ u ∣ w := by
    rw [h2m, eo]; exact two_pow_mul_dvd_iff a (b + 1) u w hu hw
  have hd2 : o ∣ m ↔ a ≤ b ∧ u ∣ w := by
    rw [eo]; conv_lhs => rw [em]
    exact two_pow_mul_dvd_iff a b u w hu hw
  have hd3 : u ∣ m ↔ u ∣ w := by
    conv_lhs => rw [em]
    rw [← one_mul u, show (1 : ℕ) = 2 ^ 0 by norm_num, two_pow_mul_dvd_iff 0 b u w hu hw]
    simp
  rw [hd1, hd2, hd3]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by by_contra hne; exact h3 ⟨by omega, h2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, h2⟩, fun h => by omega⟩

/-- For a prime power: `p^e ∣ 2^m + 1` if and only if `ord_{p^e}(2)` divides `2m` and not `m`. -/
theorem prime_pow_dvd_iff (p e m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    p ^ e ∣ 2 ^ m + 1 ↔ ord2 (p ^ e) ∣ 2 * m ∧ ¬ ord2 (p ^ e) ∣ m := by
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hprod : 2 ^ (2 * m) - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
    rw [show 2 ^ (2 * m) = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm],
      show (2 ^ m) ^ 2 - 1 = (2 ^ m) ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq]
  have hdiff : (2 ^ m + 1) - (2 ^ m - 1) = 2 := by omega
  have hp_not2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hpe_not2 : ¬ p ^ e ∣ 2 := fun h => hp_not2 ((dvd_pow_self p (by omega)).trans h)
  constructor
  · intro h
    refine ⟨(dvd_two_pow_sub_one_iff _ _).mp (by rw [hprod]; exact Dvd.dvd.mul_right h _), ?_⟩
    intro hm
    have h1 := (dvd_two_pow_sub_one_iff _ _).mpr hm
    exact hpe_not2 (by rw [← hdiff]; exact Nat.dvd_sub h h1)
  · rintro ⟨h2m, hnm⟩
    have hq : p ^ e ∣ (2 ^ m + 1) * (2 ^ m - 1) := by
      rw [← hprod]; exact (dvd_two_pow_sub_one_iff _ _).mpr h2m
    have hq1 : ¬ p ^ e ∣ 2 ^ m - 1 := fun h => hnm ((dvd_two_pow_sub_one_iff _ _).mp h)
    by_cases hpm : p ∣ 2 ^ m - 1
    · have hp1 : ¬ p ∣ 2 ^ m + 1 := fun h => hp_not2 (by rw [← hdiff]; exact Nat.dvd_sub h hpm)
      have hc : Nat.Coprime (p ^ e) (2 ^ m + 1) :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp1)
      exact absurd (hc.dvd_of_dvd_mul_left hq) hq1
    · have hc : Nat.Coprime (p ^ e) (2 ^ m - 1) :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
      exact hc.dvd_of_dvd_mul_right hq

/-- `v₂(ord_{p^e}(2)) = v₂(ord_p(2))` for an odd prime `p`. -/
theorem padicValNat_ord2_prime_pow (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    padicValNat 2 (ord2 (p ^ e)) = padicValNat 2 (ord2 p) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpeodd : (p ^ e) % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have ho := ord2_pos hpodd
  have hO := ord2_pos hpeodd
  -- `ord_p(2)` divides `ord_{p^e}(2)`.
  have h1 : ord2 p ∣ ord2 (p ^ e) := by
    rw [← dvd_two_pow_sub_one_iff]
    exact (dvd_pow_self p (by omega)).trans ((dvd_two_pow_sub_one_iff _ _).mpr dvd_rfl)
  -- `ord_{p^e}(2)` divides `ord_p(2) p^(e-1)`.
  have h2 : ord2 (p ^ e) ∣ ord2 p * p ^ (e - 1) := by
    rw [← dvd_two_pow_sub_one_iff]
    have hpN : p ∣ 2 ^ ord2 p - 1 := (dvd_two_pow_sub_one_iff _ _).mpr dvd_rfl
    have hpZ : (p : ℤ) ∣ (2 : ℤ) ^ ord2 p - 1 := by
      have := Int.natCast_dvd_natCast.mpr hpN
      rwa [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
    have := dvd_sub_pow_of_dvd_sub (R := ℤ) (a := (2 : ℤ) ^ ord2 p) (b := 1) hpZ (e - 1)
    rw [one_pow, ← pow_mul, show e - 1 + 1 = e by omega] at this
    have h1' : 1 ≤ 2 ^ (ord2 p * p ^ (e - 1)) := Nat.one_le_two_pow
    have : ((p ^ e : ℕ) : ℤ) ∣ ((2 ^ (ord2 p * p ^ (e - 1)) - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1']; push_cast; exact this
    exact Int.natCast_dvd_natCast.mp this
  obtain ⟨c, hc⟩ := h1
  have hcdvd : c ∣ p ^ (e - 1) := by
    rw [hc] at h2; exact (Nat.mul_dvd_mul_iff_left ho).mp h2
  have hcodd : ¬ 2 ∣ c := fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow (h.trans hcdvd))).symm
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; omega
  rw [hc, padicValNat.mul ho.ne' hc0, padicValNat.eq_zero_of_not_dvd hcodd, add_zero]

/-- **Theorem 4 (ii).** -/
theorem theorem4_ii (y : ℕ) (hy : y % 2 = 1) (hy1 : 1 < y) :
    (∃ m, 1 ≤ m ∧ y ∣ 2 ^ m + 1) ↔
      ∃ s, 1 ≤ s ∧ ∀ p, p.Prime → p ∣ y → padicValNat 2 (ord2 p) = s := by
  have hp2 : ∀ p, p.Prime → p ∣ y → p ≠ 2 := by
    rintro p - hpy rfl; omega
  constructor
  · rintro ⟨m, hm, hdvd⟩
    refine ⟨padicValNat 2 m + 1, by omega, fun p hp hpy => ?_⟩
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (hp2 p hp hpy))
    have h := (prime_pow_dvd_iff p 1 m hp (hp2 p hp hpy) le_rfl).mp
      (by rw [pow_one]; exact hpy.trans hdvd)
    rw [pow_one] at h
    exact ((dvd_two_mul_not_dvd_iff _ m (ord2_pos hpodd) (by omega)).mp h).1
  · rintro ⟨s, hs, hall⟩
    set P := y.primeFactors
    let o : ℕ → ℕ := fun p => ord2 (p ^ y.factorization p)
    have hmemP : ∀ p ∈ P, p.Prime ∧ p ∣ y ∧ 1 ≤ y.factorization p := by
      intro p hpP
      have hp := Nat.prime_of_mem_primeFactors hpP
      have hpy := Nat.dvd_of_mem_primeFactors hpP
      exact ⟨hp, hpy, (hp.dvd_iff_one_le_factorization (by omega)).mp hpy⟩
    have hopos : ∀ p ∈ P, 0 < o p := by
      intro p hpP
      obtain ⟨hp, hpy, -⟩ := hmemP p hpP
      exact ord2_pos (Nat.odd_iff.mp ((hp.odd_of_ne_two (hp2 p hp hpy)).pow))
    have hov : ∀ p ∈ P, padicValNat 2 (o p) = s := by
      intro p hpP
      obtain ⟨hp, hpy, he⟩ := hmemP p hpP
      rw [padicValNat_ord2_prime_pow p _ hp (hp2 p hp hpy) he]
      exact hall p hp hpy
    set L := ∏ p ∈ P, oddPart (o p) with hL
    have hLodd : L % 2 = 1 := by
      rw [hL]
      apply Finset.prod_induction _ (fun x => x % 2 = 1)
      · intro a b ha hb; rw [Nat.mul_mod, ha, hb]
      · rfl
      · intro p hpP; exact (decomp (o p) (hopos p hpP).ne').2
    set m := 2 ^ (s - 1) * L with hm
    have hm0 : 0 < m := by rw [hm]; exact Nat.mul_pos (by positivity) (by omega)
    have hvm : padicValNat 2 m = s - 1 := by
      rw [hm, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by omega), add_zero]
    have hpe : ∀ p ∈ P, p ^ y.factorization p ∣ 2 ^ m + 1 := by
      intro p hpP
      obtain ⟨hp, hpy, he⟩ := hmemP p hpP
      apply (prime_pow_dvd_iff p _ m hp (hp2 p hp hpy) he).mpr
      apply (dvd_two_mul_not_dvd_iff _ m (hopos p hpP) hm0).mpr
      refine ⟨by rw [hov p hpP, hvm]; omega, ?_⟩
      exact (Finset.dvd_prod_of_mem (fun p => oddPart (o p)) hpP).trans (Dvd.intro_left _ rfl)
    refine ⟨m, hm0, ?_⟩
    apply (Nat.factorization_prime_le_iff_dvd (by omega) (by positivity)).mp
    intro p hp
    by_cases hpP : p ∈ P
    · exact (hp.pow_dvd_iff_le_factorization (by positivity)).mp (hpe p hpP)
    · have : ¬ p ∣ y := fun hpy => hpP (Nat.mem_primeFactors.mpr ⟨hp, hpy, by omega⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd this]
      exact Nat.zero_le _

end Collatz
