import Collatz.Theorems

/-!
# The paper's Corollary 1 (i), (ii): counting the bounded orbits

`boundedUpTo F X` is the set of initial values `x ≤ X` whose orbit under `F` is bounded.
By Theorems 1, 2 and 3, each such `x` belongs to an explicit family. Every member of these
families up to `X` is the value of an explicit encoding at a point of a square grid of side
`L + 1` (for `Q_±`) or `L + 3` (for `S`), with `L = ⌊log₂ X⌋`. This gives the bounds
`(log₂ X + 1)^2` and `(log₂ X + 3)^2`.
-/

namespace Collatz

open Filter Classical

/-- The initial values `x ≤ X` whose orbit under `F` is bounded. -/
noncomputable def boundedUpTo (F : ℕ → ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun x => BddAbove (Set.range fun i => F^[i] x))

theorem mem_boundedUpTo {F : ℕ → ℕ} {X x : ℕ} (h : x ∈ boundedUpTo F X) :
    x ≤ X ∧ BddAbove (Set.range fun i => F^[i] x) := by
  rw [boundedUpTo, Finset.mem_filter, Finset.mem_range] at h
  exact ⟨by omega, h.2⟩

/-- A finite set of values of `enc` on an `N × N` grid has at most `N^2` elements. -/
theorem card_le_of_grid (B : Finset ℕ) (N : ℕ) (enc : ℕ × ℕ → ℕ)
    (h : ∀ x ∈ B, ∃ a b, a < N ∧ b < N ∧ enc (a, b) = x) : B.card ≤ N ^ 2 := by
  have hsub : B ⊆ (Finset.range N ×ˢ Finset.range N).image enc := by
    intro x hx
    obtain ⟨a, b, ha, hb, rfl⟩ := h x hx
    exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩, rfl⟩
  calc B.card ≤ ((Finset.range N ×ˢ Finset.range N).image enc).card := Finset.card_le_card hsub
    _ ≤ (Finset.range N ×ˢ Finset.range N).card := Finset.card_image_le
    _ = N ^ 2 := by rw [Finset.card_product, Finset.card_range]; ring

theorem le_log_of_le {e X : ℕ} (h : 2 ^ e ≤ X) : e ≤ Nat.log 2 X :=
  Nat.le_log_of_pow_le (by norm_num) h

/-- From `card ≤ (L + c)^2` with `L = ⌊log₂ X⌋` to the real bound `(log₂ X + c)^2`. -/
theorem real_bound (n X c : ℕ) (h : n ≤ (Nat.log 2 X + c) ^ 2) :
    (n : ℝ) ≤ (Real.logb 2 X + c) ^ 2 := by
  have hL : ((Nat.log 2 X : ℕ) : ℝ) ≤ Real.logb 2 X := by
    have := Real.natLog_le_logb X 2
    rwa [Nat.cast_ofNat] at this
  calc (n : ℝ) ≤ ((Nat.log 2 X + c : ℕ) : ℝ) ^ 2 := by exact_mod_cast h
    _ ≤ (Real.logb 2 X + c) ^ 2 := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-! ### `Q_-` -/

/-- The encoding for `Q_-`: `(l, 0) ↦ 2^l`, `(l, m) ↦ 2^l (2^m + 1)` for `l + m ≤ L`,
otherwise `0`. -/
def encQm (L : ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.2 = 0 then 2 ^ p.1 else if p.1 + p.2 ≤ L then 2 ^ p.1 * (2 ^ p.2 + 1) else 0

theorem encQm_pow (L l : ℕ) : encQm L (l, 0) = 2 ^ l := by simp [encQm]
theorem encQm_term (L l m : ℕ) (hm : 1 ≤ m) (h : l + m ≤ L) :
    encQm L (l, m) = 2 ^ l * (2 ^ m + 1) := by simp only [encQm]; split_ifs <;> omega
theorem encQm_zero (L : ℕ) (hL : 1 ≤ L) : encQm L (L, L) = 0 := by
  simp only [encQm]; split_ifs <;> omega

/-- **Corollary 1 (i)** for `Q_-`. -/
theorem corollary1_i_Qm (X : ℕ) (hX : 2 ≤ X) :
    ((boundedUpTo Qm X).card : ℝ) ≤ (Real.logb 2 X + 1) ^ 2 := by
  suffices h : (boundedUpTo Qm X).card ≤ (Nat.log 2 X + 1) ^ 2 by
    have := real_bound _ X 1 h; simpa using this
  have hL : 1 ≤ Nat.log 2 X := Nat.log_pos (by norm_num) hX
  apply card_le_of_grid _ _ (encQm (Nat.log 2 X))
  intro x hx
  obtain ⟨hxX, hbdd⟩ := mem_boundedUpTo hx
  have hclass : x = 0 ∨ (∃ l, x = 2 ^ l) ∨ ∃ l m, 1 ≤ m ∧ x = 2 ^ l * (2 ^ m + 1) := by
    by_contra hc
    exact not_bddAbove_of_tendsto_atTop (theorem1_iii x hc) hbdd
  rcases hclass with rfl | ⟨l, rfl⟩ | ⟨l, m, hm, rfl⟩
  · exact ⟨Nat.log 2 X, Nat.log 2 X, by omega, by omega, encQm_zero _ hL⟩
  · exact ⟨l, 0, by have := le_log_of_le hxX; omega, by omega, encQm_pow _ _⟩
  · have h1 : 2 ^ (l + m) ≤ X := by
      calc 2 ^ (l + m) = 2 ^ l * 2 ^ m := pow_add 2 l m
        _ ≤ 2 ^ l * (2 ^ m + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ X := hxX
    have h2 := le_log_of_le h1
    exact ⟨l, m, by omega, by omega, encQm_term _ _ _ hm h2⟩

/-! ### `Q_+` -/

/-- The encoding for `Q_+`: `(l, b) ↦ 2^l (2^(b+1) - 1)` for `l + b ≤ L`,
`(l + 1, L) ↦ 5 · 2^l`, otherwise `0`. -/
def encQp (L : ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 + p.2 ≤ L then 2 ^ p.1 * (2 ^ (p.2 + 1) - 1)
  else if p.2 = L ∧ 1 ≤ p.1 ∧ p.1 + 1 ≤ L then 5 * 2 ^ (p.1 - 1) else 0

theorem encQp_term (L l b : ℕ) (h : l + b ≤ L) :
    encQp L (l, b) = 2 ^ l * (2 ^ (b + 1) - 1) := by simp only [encQp]; split_ifs <;> omega
theorem encQp_five (L l : ℕ) (h : l + 2 ≤ L) : encQp L (l + 1, L) = 5 * 2 ^ l := by
  unfold encQp
  dsimp only
  rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩, Nat.add_sub_cancel]
theorem encQp_zero (L : ℕ) (hL : 1 ≤ L) : encQp L (L, L) = 0 := by
  simp only [encQp]; split_ifs <;> omega

/-- **Corollary 1 (i)** for `Q_+`. -/
theorem corollary1_i_Qp (X : ℕ) (hX : 2 ≤ X) :
    ((boundedUpTo Qp X).card : ℝ) ≤ (Real.logb 2 X + 1) ^ 2 := by
  suffices h : (boundedUpTo Qp X).card ≤ (Nat.log 2 X + 1) ^ 2 by
    have := real_bound _ X 1 h; simpa using this
  have hL : 1 ≤ Nat.log 2 X := Nat.log_pos (by norm_num) hX
  apply card_le_of_grid _ _ (encQp (Nat.log 2 X))
  intro x hx
  obtain ⟨hxX, hbdd⟩ := mem_boundedUpTo hx
  have hclass : x = 0 ∨ (∃ l m, 1 ≤ m ∧ x = 2 ^ l * (2 ^ m - 1)) ∨ ∃ l, x = 5 * 2 ^ l := by
    by_contra hc
    exact not_bddAbove_of_tendsto_atTop (theorem2_iv x hc) hbdd
  rcases hclass with rfl | ⟨l, m, hm, rfl⟩ | ⟨l, rfl⟩
  · exact ⟨Nat.log 2 X, Nat.log 2 X, by omega, by omega, encQp_zero _ hL⟩
  · obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    have h1 : 2 ^ (l + b) ≤ X := by
      calc 2 ^ (l + b) = 2 ^ l * 2 ^ b := pow_add 2 l b
        _ ≤ 2 ^ l * (2 ^ (b + 1) - 1) := by
          apply Nat.mul_le_mul_left
          have := Nat.one_le_two_pow (n := b); rw [pow_succ]; omega
        _ ≤ X := hxX
    have h2 := le_log_of_le h1
    exact ⟨l, b, by omega, by omega, encQp_term _ _ _ h2⟩
  · have h1 : 2 ^ (l + 2) ≤ X := by
      calc 2 ^ (l + 2) = 4 * 2 ^ l := by rw [pow_add]; ring
        _ ≤ 5 * 2 ^ l := by omega
        _ ≤ X := hxX
    have h2 := le_log_of_le h1
    exact ⟨l + 1, Nat.log 2 X, by omega, by omega, encQp_five _ _ h2⟩

/-! ### `S` -/

/-- The encoding for `S` on the grid of side `L + 3`. -/
def encS (L : ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 + p.2 ≤ L then 2 ^ p.1 * (2 ^ (p.2 + 1) - 1)
  else if p.1 ≤ L ∧ p.2 ≤ L then 2 ^ (L - p.1) * (2 ^ (L + 1 - p.2) + 1)
  else if p.1 = L + 1 then 11 * 2 ^ p.2
  else if p.1 = L + 2 ∧ p.2 ≤ L then 23 * 2 ^ p.2
  else if p.2 = L + 1 then 181 * 2 ^ p.1 else 0

theorem encS_minus (L l b : ℕ) (h : l + b ≤ L) :
    encS L (l, b) = 2 ^ l * (2 ^ (b + 1) - 1) := by simp only [encS]; split_ifs <;> omega
theorem encS_plus (L l m : ℕ) (hm : 1 ≤ m) (h : l + m ≤ L) :
    encS L (L - l, L + 1 - m) = 2 ^ l * (2 ^ m + 1) := by
  have e1 : L - (L - l) = l := by omega
  have e2 : L + 1 - (L + 1 - m) = m := by omega
  simp only [encS, e1, e2]; split_ifs <;> omega
theorem encS_11 (L b : ℕ) : encS L (L + 1, b) = 11 * 2 ^ b := by
  simp only [encS]; split_ifs <;> omega
theorem encS_23 (L b : ℕ) (h : b ≤ L) : encS L (L + 2, b) = 23 * 2 ^ b := by
  unfold encS
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, h⟩]
theorem encS_181 (L a : ℕ) (h : a ≤ L) : encS L (a, L + 1) = 181 * 2 ^ a := by
  simp only [encS]; split_ifs <;> omega
theorem encS_zero (L : ℕ) : encS L (L + 2, L + 2) = 0 := by
  simp only [encS]; split_ifs <;> omega

/-- **Corollary 1 (ii).** -/
theorem corollary1_ii (X : ℕ) (hX : 2 ≤ X) :
    ((boundedUpTo S X).card : ℝ) ≤ (Real.logb 2 X + 3) ^ 2 := by
  suffices h : (boundedUpTo S X).card ≤ (Nat.log 2 X + 3) ^ 2 by
    have := real_bound _ X 3 h; simpa using this
  apply card_le_of_grid _ _ (encS (Nat.log 2 X))
  intro x hx
  obtain ⟨hxX, hbdd⟩ := mem_boundedUpTo hx
  have hclass : x = 0 ∨ ∃ l q, x = 2 ^ l * q ∧ q % 2 = 1 ∧ BoundedS q := by
    by_contra hc
    exact not_bddAbove_of_tendsto_atTop (theorem3_ii x hc) hbdd
  -- `2^e · c ≤ X` with `2^k ≤ c` bounds `e + k` by `⌊log₂ X⌋`.
  have hbound : ∀ e k c, 2 ^ k ≤ c → 2 ^ e * c ≤ X → e + k ≤ Nat.log 2 X :=
    fun e k c hkc hec =>
      le_log_of_le (by rw [pow_add]; exact (Nat.mul_le_mul_left _ hkc).trans hec)
  rcases hclass with rfl | ⟨l, q, rfl, -, hq⟩
  · exact ⟨_, _, by omega, by omega, encS_zero _⟩
  rcases hq with ⟨m, hm, rfl | rfl⟩ | rfl | rfl | rfl
  · have h1 := hbound l m _ (by omega) hxX
    exact ⟨_, _, by omega, by omega, encS_plus _ l m hm h1⟩
  · obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    have h1 := hbound l b _ (by have := Nat.one_le_two_pow (n := b); rw [pow_succ]; omega) hxX
    exact ⟨l, b, by omega, by omega, encS_minus _ _ _ h1⟩
  · have h1 := hbound l 3 11 (by norm_num) hxX
    exact ⟨_, l, by omega, by omega, (encS_11 _ l).trans (mul_comm _ _)⟩
  · have h1 := hbound l 4 23 (by norm_num) hxX
    exact ⟨_, l, by omega, by omega, (encS_23 _ l (by omega)).trans (mul_comm _ _)⟩
  · have h1 := hbound l 7 181 (by norm_num) hxX
    exact ⟨l, _, by omega, by omega, (encS_181 _ l (by omega)).trans (mul_comm _ _)⟩

end Collatz
