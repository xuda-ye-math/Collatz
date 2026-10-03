import Collatz.Consequences
import Collatz.Criterion
import Collatz.Counting

/-!
# Natural density `0` of the bounded orbits of `Q_-`, without Szalay's theorem

The paper (Section 5) shows, from Theorem 4 alone, that the initial values with a bounded orbit
under `Q_-` have natural density `0`:

* a prime `p ≡ 7 (mod 8)` has `ord_p(2)` odd (Euler's criterion and the supplementary law), so no
  initial value with such a prime factor has a bounded orbit (Theorem 4);
* `∑ 1/p` over the primes `p ≡ 7 (mod 8)` diverges, so the proportion of integers free of such
  primes tends to `0`.

The paper derives the divergence from the prime number theorem for arithmetic progressions.
Here it is derived from Mathlib's form of Dirichlet's theorem,
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`: a convergent `∑ 1/p` would
make `∑ Λ(n)/n^x` over the class `7 mod 8` of order `o(1/(x - 1))` as `x → 1⁺`.
-/

namespace Collatz

open Filter Topology ArithmeticFunction

/-- The reciprocals of the primes `p ≡ 7 (mod 8)`. -/
noncomputable def recip7 (n : ℕ) : ℝ := if n.Prime ∧ n % 8 = 7 then 1 / (n : ℝ) else 0

theorem recip7_nonneg (n : ℕ) : 0 ≤ recip7 n := by
  unfold recip7; split_ifs <;> positivity

theorem natCast_eq_seven_iff (n : ℕ) : ((n : ZMod 8) = 7) ↔ n % 8 = 7 := by
  rw [show (7 : ZMod 8) = ((7 : ℕ) : ZMod 8) by norm_num, ZMod.natCast_eq_natCast_iff']

/-- **Divergence of `∑ 1/p` over the primes `p ≡ 7 (mod 8)`.** -/
theorem not_summable_recip7 : ¬ Summable recip7 := by
  intro hS
  have ha : IsUnit (7 : ZMod 8) := isUnit_iff_exists_inv.mpr ⟨7, by decide⟩
  obtain ⟨C, hC⟩ := vonMangoldt.LSeries_residueClass_lower_bound (q := 8) ha
  set r : ℕ → ℝ := vonMangoldt.residueClass (7 : ZMod 8) with hr
  have hr0 : ∀ n, 0 ≤ r n := vonMangoldt.residueClass_nonneg _
  -- The three comparison series.
  set g0 : ℕ → ℝ := fun n => (if n.Prime then 0 else r n) / n with hg0
  have hg0s : Summable g0 := vonMangoldt.summable_residueClass_non_primes_div _
  have hg0n : ∀ n, 0 ≤ g0 n := fun n => by
    simp only [hg0]
    split_ifs
    · simp
    · exact div_nonneg (hr0 n) (Nat.cast_nonneg n)
  have htail := tendsto_sum_nat_add recip7
  have hc : (0 : ℝ) < ((Nat.totient 8 : ℕ) : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (by norm_num))
  set c : ℝ := ((Nat.totient 8 : ℕ) : ℝ)⁻¹ with hcdef
  obtain ⟨N, hN⟩ : ∃ N, ∑' k, recip7 (k + N) ≤ c / 2 := by
    have := (htail.eventually (ge_mem_nhds (show (0 : ℝ) < c / 2 by positivity))).exists
    exact this
  set gN : ℕ → ℝ := fun n => if n < N then r n / n else 0 with hgN
  set hT : ℕ → ℝ := fun n => if N ≤ n then recip7 n else 0 with hhT
  have hgNs : Summable gN := summable_of_ne_finset_zero (s := Finset.range N) (by
    intro n hn; simp only [hgN, Finset.mem_range] at hn ⊢; rw [if_neg hn])
  have hTs : Summable hT := hS.of_nonneg_of_le
    (fun n => by simp only [hhT]; split_ifs <;> simp [recip7_nonneg])
    (fun n => by simp only [hhT]; split_ifs <;> simp [recip7_nonneg])
  have hTval : ∑' n, hT n = ∑' k, recip7 (k + N) := by
    rw [← Summable.sum_add_tsum_nat_add N hTs]
    have h0 : ∑ i ∈ Finset.range N, hT i = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        simp only [hhT, Finset.mem_range] at hi ⊢; rw [if_neg (by omega)])
    rw [h0, zero_add]
    congr 1; ext k; simp only [hhT]; rw [if_pos (by omega)]
  -- The termwise bound for `1 < x ≤ 2`.
  have hterm : ∀ x : ℝ, 1 < x → ∀ n : ℕ,
      r n / (n : ℝ) ^ x ≤ g0 n + gN n + (x - 1)⁻¹ * hT n := by
    intro x hx n
    have hx1 : 0 < x - 1 := by linarith
    have hgNn : 0 ≤ gN n := by simp only [hgN]; split_ifs <;> [exact div_nonneg (hr0 n) (by positivity); exact le_rfl]
    have hTn : 0 ≤ hT n := by simp only [hhT]; split_ifs <;> simp [recip7_nonneg]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : r 0 = 0 := vonMangoldt.residueClass_apply_zero _
      rw [this, zero_div]
      have := hg0n 0
      positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ x := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le hn1 hx.le
    have hle_n : r n / (n : ℝ) ^ x ≤ r n / n :=
      div_le_div_of_nonneg_left (hr0 n) (by positivity) hpow
    by_cases hp : n.Prime
    · by_cases hnN : n < N
      · have : gN n = r n / n := by simp only [hgN]; rw [if_pos hnN]
        rw [this]
        have : 0 ≤ g0 n := hg0n n
        have : 0 ≤ (x - 1)⁻¹ * hT n := by positivity
        linarith
      · by_cases h7 : n % 8 = 7
        · have hrn : r n = Real.log n := by
            simp only [hr, vonMangoldt.residueClass, Set.indicator, Set.mem_ofPred_eq,
              (natCast_eq_seven_iff n).mpr h7, if_true]
            exact vonMangoldt_apply_prime hp
          have hTn' : hT n = 1 / n := by
            simp only [hhT, recip7]; rw [if_pos (by omega), if_pos ⟨hp, h7⟩]
          rw [hrn, hTn']
          have hlog := Real.log_le_rpow_div (x := n) (by positivity) hx1
          have hsplit : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
            rw [← Real.rpow_add_one (by positivity), sub_add_cancel]
          have hnx : 0 < (n : ℝ) ^ (x - 1) := by positivity
          have key : Real.log n / (n : ℝ) ^ x ≤ (x - 1)⁻¹ * (1 / n) := by
            rw [hsplit, div_le_iff₀ (by positivity)]
            calc Real.log n ≤ (n : ℝ) ^ (x - 1) / (x - 1) := hlog
              _ = (x - 1)⁻¹ * (1 / n) * ((n : ℝ) ^ (x - 1) * n) := by
                field_simp
          have : 0 ≤ g0 n := hg0n n
          linarith
        · have hrn : r n = 0 := by
            simp only [hr, vonMangoldt.residueClass, Set.indicator, Set.mem_ofPred_eq]
            rw [if_neg (by rw [natCast_eq_seven_iff]; exact h7)]
          rw [hrn, zero_div]
          have := hg0n n
          positivity
    · have : g0 n = r n / n := by simp only [hg0]; rw [if_neg hp]
      rw [this]
      have : 0 ≤ (x - 1)⁻¹ * hT n := by positivity
      linarith
  -- Summing the termwise bound.
  set K := ∑' n, g0 n
  set CN := ∑' n, gN n
  set T := ∑' n, hT n
  have hT2 : T ≤ c / 2 := by rw [hTval]; exact hN
  have hsum : ∀ x : ℝ, 1 < x → ∑' n, r n / (n : ℝ) ^ x ≤ K + CN + (x - 1)⁻¹ * T := by
    intro x hx
    have hRs : Summable fun n => g0 n + gN n + (x - 1)⁻¹ * hT n :=
      (hg0s.add hgNs).add (hTs.mul_left _)
    have hLs : Summable fun n => r n / (n : ℝ) ^ x :=
      hRs.of_nonneg_of_le (fun n => by
        have := hr0 n; positivity) (hterm x hx)
    calc ∑' n, r n / (n : ℝ) ^ x ≤ ∑' n, (g0 n + gN n + (x - 1)⁻¹ * hT n) :=
          Summable.tsum_le_tsum (hterm x hx) hLs hRs
      _ = K + CN + (x - 1)⁻¹ * T := by
          rw [Summable.tsum_add (hg0s.add hgNs) (hTs.mul_left _),
            Summable.tsum_add hg0s hgNs, tsum_mul_left]
  -- Contradiction as `x → 1⁺`.
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => by simp only [hhT]; split_ifs <;> simp [recip7_nonneg])
  set B := C + K + CN + 1 with hB
  have hBpos : 0 < B := by
    have hK : 0 ≤ K := tsum_nonneg hg0n
    have hCN : 0 ≤ CN := tsum_nonneg (fun n => by
      simp only [hgN]; split_ifs <;> [exact div_nonneg (hr0 n) (by positivity); exact le_rfl])
    have := hC (x := 2) ⟨by norm_num, le_rfl⟩
    have h2 := hsum 2 (by norm_num)
    norm_num at this h2
    nlinarith
  set t : ℝ := min 1 (c / (2 * B)) with ht
  have htpos : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htc : t ≤ c / (2 * B) := min_le_right _ _
  have hlow := hC (x := 1 + t) ⟨by linarith, by linarith⟩
  have hup := hsum (1 + t) (by linarith)
  rw [show 1 + t - 1 = t by ring] at hlow hup
  -- `c / t - C ≤ K + CN + T / t` and `T ≤ c / 2` give `c / (2t) ≤ C + K + CN < B`.
  have h1 : c / t - C ≤ K + CN + t⁻¹ * (c / 2) := by
    calc c / t - C ≤ K + CN + t⁻¹ * T := hlow.trans hup
      _ ≤ K + CN + t⁻¹ * (c / 2) := by gcongr
  have h2 : c / (2 * t) ≤ C + K + CN := by
    have : c / t - t⁻¹ * (c / 2) = c / (2 * t) := by field_simp; ring
    linarith
  have h3 : B ≤ c / (2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    calc B * (2 * t) ≤ B * (2 * (c / (2 * B))) := by gcongr
      _ = c := by field_simp
  linarith

/-- For a prime `p ≡ 7 (mod 8)`, `ord_p(2)` is odd: `2` is a square mod `p` (the supplementary
law), so `2^((p-1)/2) ≡ 1` (Euler's criterion), and `(p-1)/2` is odd. -/
theorem ord2_odd_of_seven (p : ℕ) (hp : p.Prime) (h7 : p % 8 = 7) : ord2 p % 2 = 1 := by
  haveI := Fact.mk hp
  have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inr h7)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hpow : (2 : ZMod p) ^ (p / 2) = 1 := (ZMod.euler_criterion p h2ne).mp hsq
  have hdvd : ord2 p ∣ p / 2 := orderOf_dvd_of_pow_eq_one hpow
  rcases Nat.even_or_odd (ord2 p) with he | ho
  · exfalso
    have := he.two_dvd.trans hdvd
    omega
  · exact Nat.odd_iff.mp ho

/-- A prime `p ≡ 7 (mod 8)` divides no `2^m + 1`. -/
theorem not_dvd_of_seven (p m : ℕ) (hp : p.Prime) (h7 : p % 8 = 7) : ¬ p ∣ 2 ^ m + 1 := by
  intro h
  have := (prime_pow_dvd_iff p 1 m hp (by omega) le_rfl).mp (by rwa [pow_one])
  rw [pow_one] at this
  obtain ⟨h2m, hnm⟩ := this
  have hc : Nat.Coprime (ord2 p) 2 :=
    (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (ord2_odd_of_seven p hp h7))).symm
  exact hnm (hc.dvd_of_dvd_mul_left h2m)

/-- Under `Q_-`, an initial value with a prime factor `p ≡ 7 (mod 8)` has an unbounded orbit
(Theorem 4). -/
theorem not_bdd_of_seven (x p : ℕ) (hx : 0 < x) (hp : p.Prime) (h7 : p % 8 = 7)
    (hpx : p ∣ x) : ¬ BddAbove (Set.range fun i => Qm^[i] x) := by
  obtain ⟨l, q, rfl, hq⟩ := exists_two_pow_mul_odd hx.ne'
  have hcop : Nat.Coprime p (2 ^ l) :=
    Nat.Coprime.pow_right l ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hpq : p ∣ q := hcop.dvd_of_dvd_mul_left hpx
  have hq1 : 1 < q := by
    have := Nat.le_of_dvd (by omega) hpq
    have := hp.two_le
    omega
  exact not_bddAbove_of_tendsto_atTop (theorem4_i (2 ^ l * q) l q hq hq1
    (iterate_halve Qm (fun n hn => Qm_even hn) l q)
    (fun m _ hd => not_dvd_of_seven p m hp h7 (hpq.trans hd)))

/-! ### The sieve -/

theorem card_coprime_range_mul (M K : ℕ) :
    ((Finset.range (K * M)).filter (fun x => M.Coprime x)).card = K * M.totient := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show (K + 1) * M = K * M + M by ring, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (K * M)) (Nat.le_add_right _ _),
      Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ← Finset.range_eq_Ico, ih, Nat.filter_coprime_Ico_eq_totient]
    ring

theorem card_coprime_le (M X : ℕ) (hM : 0 < M) :
    ((Finset.range (X + 1)).filter (fun x => M.Coprime x)).card ≤ (X / M + 1) * M.totient := by
  rw [← card_coprime_range_mul]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  apply Finset.range_subset_range.mpr
  have := Nat.lt_div_mul_add (a := X) hM
  rw [add_mul, one_mul]
  omega

/-- For a finite set `P` of primes and `M = ∏ P`: `φ(M) / M ≤ exp(-∑_{p ∈ P} 1/p)`. -/
theorem totient_div_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((∏ p ∈ P, p).totient : ℝ) / (∏ p ∈ P, p : ℕ) ≤ Real.exp (-∑ p ∈ P, (1 : ℝ) / p) := by
  set M := ∏ p ∈ P, p with hM
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  have hM0 : 0 < M := Finset.prod_pos hpos
  have hfac : M.primeFactors = P := Nat.primeFactors_prod hP
  have htot : M.totient = ∏ p ∈ P, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors M
    rw [hfac, ← hM, mul_comm M] at h
    exact Nat.eq_of_mul_eq_mul_right hM0 h
  have hratio : (M.totient : ℝ) / M = ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
    rw [htot, hM]
    push_cast
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hpos p hp
    rw [Nat.cast_sub (hpos p hp)]
    field_simp
    push_cast; ring
  rw [hratio, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hpos p hp
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  · intro p _
    have := Real.add_one_le_exp (-(1 / (p : ℝ)))
    linarith

/-! ### Density `0` -/

/-- **Density `0` without Szalay's theorem.** The number of initial values in `{0, …, X}` with
a bounded orbit under `Q_-` is `o(X)`. -/
theorem density_zero :
    (fun X : ℕ => ((boundedUpTo Qm X).card : ℝ)) =o[atTop] (fun X : ℕ => (X : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg recip7_nonneg).mp
    not_summable_recip7
  obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop (Real.log (2 / ε))).exists
  set P := (Finset.range N).filter (fun n => n.Prime ∧ n % 8 = 7) with hPdef
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hP7 : ∀ p ∈ P, p % 8 = 7 := fun p hp => (Finset.mem_filter.mp hp).2.2
  have hsumP : ∑ i ∈ Finset.range N, recip7 i = ∑ p ∈ P, (1 : ℝ) / p := by
    rw [hPdef, Finset.sum_filter]; rfl
  set M := ∏ p ∈ P, p with hM
  have hM0 : 0 < M := Finset.prod_pos (fun p hp => (hPprime p hp).pos)
  have hratio : (M.totient : ℝ) / M ≤ ε / 2 := by
    calc (M.totient : ℝ) / M ≤ Real.exp (-∑ p ∈ P, (1 : ℝ) / p) := totient_div_le_exp P hPprime
      _ ≤ Real.exp (-Real.log (2 / ε)) := by
          apply Real.exp_le_exp.mpr; rw [← hsumP]; linarith
      _ = ε / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  filter_upwards [eventually_ge_atTop ⌈2 * (1 + (M : ℝ)) / ε⌉₊] with X hX
  have hXε : 2 * (1 + (M : ℝ)) / ε ≤ X := Nat.ceil_le.mp hX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  -- Every `x ≥ 1` with a bounded orbit is coprime to `M`.
  have hsub : boundedUpTo Qm X ⊆
      insert 0 ((Finset.range (X + 1)).filter (fun x => M.Coprime x)) := by
    intro x hx
    obtain ⟨hxX, hbdd⟩ := mem_boundedUpTo hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, Nat.Coprime.prod_left (fun p hp => ?_)⟩
      exact (Nat.Prime.coprime_iff_not_dvd (hPprime p hp)).mpr
        (fun hpx => not_bdd_of_seven x p hx0 (hPprime p hp) (hP7 p hp) hpx hbdd)
  have hcard : (boundedUpTo Qm X).card ≤ 1 + (X / M + 1) * M.totient :=
    (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans
      (by have := card_coprime_le M X hM0; omega))
  have hcardR : ((boundedUpTo Qm X).card : ℝ) ≤ 1 + ((X / M : ℕ) + 1) * M.totient := by
    exact_mod_cast hcard
  have hdivle : ((X / M : ℕ) : ℝ) ≤ X / M := Nat.cast_div_le
  have htot : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
  have hφ : (X : ℝ) / M * M.totient ≤ X * (ε / 2) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have hX2 : 1 + (M : ℝ) ≤ ε * X / 2 := by
    rw [div_le_iff₀ hε] at hXε; linarith
  calc ((boundedUpTo Qm X).card : ℝ) ≤ 1 + ((X / M : ℕ) + 1) * M.totient := hcardR
    _ ≤ 1 + (X / M + 1) * M.totient := by gcongr
    _ = 1 + X / M * M.totient + M.totient := by ring
    _ ≤ 1 + X * (ε / 2) + M := by linarith
    _ ≤ ε * X := by linarith

end Collatz
