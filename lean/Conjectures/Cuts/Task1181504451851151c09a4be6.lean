import Mathlib

set_option maxHeartbeats 1600000

/-!
`L-goldbach-cut-1181504451851151c09a4be6` (a cut of `L-goldbach-dyadic-cell-reflected-cancellation`).

For `n = 2^m` the grid `a(i, j) = n/2 + i·2^(m - m/4) + j` sweeps the interval
`[n/2, n/2 + n/8)` exactly once, so both sums run over the same index set `t ∈ [0, n/8)`.
Since `Λ ≥ w` pointwise, each summand of the difference is nonnegative and can only be
nonzero when `a` or `n - a` is a *proper* prime power (`IsPrimePow` but not prime).  The
number of proper prime powers up to `n` is at most `#(primes ≤ √n)·m ≤ (√n + 1)·m`
(exponent uniqueness of `p^e`), and each exceptional summand is at most `(log n)²`.  For
`m ≥ 64` the total is below `n / 1000`.
-/

namespace Task118150445

open Finset Real ArithmeticFunction

noncomputable section

/-- The weight `w` of the statement: `log` on primes, `0` elsewhere. -/
def W (k : ℕ) : ℝ := if Nat.Prime k then Real.log k else 0

lemma W_eq_log_of_prime {k : ℕ} (hk : Nat.Prime k) : W k = Real.log k := by
  simp [W, hk]

lemma W_eq_zero_of_not_prime {k : ℕ} (hk : ¬Nat.Prime k) : W k = 0 := by
  simp [W, hk]

lemma W_nonneg (k : ℕ) : 0 ≤ W k := by
  by_cases hk : Nat.Prime k
  · rw [W_eq_log_of_prime hk]
    exact Real.log_nonneg (by exact_mod_cast hk.one_le)
  · rw [W_eq_zero_of_not_prime hk]

/-- `w ≤ Λ` pointwise. -/
lemma W_le_vonMangoldt (k : ℕ) : W k ≤ vonMangoldt k := by
  by_cases hk : Nat.Prime k
  · rw [W_eq_log_of_prime hk, vonMangoldt_apply_prime hk]
  · rw [W_eq_zero_of_not_prime hk]
    exact vonMangoldt_nonneg

lemma lam_le_log (k : ℕ) : vonMangoldt k ≤ Real.log k := vonMangoldt_le_log

/-- A proper prime power: a prime power that is not itself prime. -/
def Proper (k : ℕ) : Prop := IsPrimePow k ∧ ¬Nat.Prime k

lemma lam_eq_W_of_prime {k : ℕ} (hk : Nat.Prime k) : vonMangoldt k = W k := by
  rw [W_eq_log_of_prime hk, vonMangoldt_apply_prime hk]

lemma lam_eq_W_of_not_isPrimePow {k : ℕ} (hk : ¬IsPrimePow k) : vonMangoldt k = W k := by
  have hzero : vonMangoldt k = 0 := vonMangoldt_eq_zero_iff.2 hk
  have hnp : ¬Nat.Prime k := by
    intro hp
    exact hk (Nat.Prime.isPrimePow hp)
  rw [hzero, W_eq_zero_of_not_prime hnp]

lemma lam_eq_W_of_not_proper {k : ℕ} (hk : ¬Proper k) : vonMangoldt k = W k := by
  unfold Proper at hk
  by_cases hp : Nat.Prime k
  · exact lam_eq_W_of_prime hp
  · exact lam_eq_W_of_not_isPrimePow (fun hip => hk ⟨hip, hp⟩)

/-- Natural powers respect `≤` on nonnegative reals. -/
lemma rpow_nat_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have hbp : 0 ≤ b := le_trans ha hab
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg hbp k)

/-- The per-pair difference of the two summands. -/
def Dif (a b : ℕ) : ℝ := vonMangoldt a * vonMangoldt b - W a * W b

lemma Dif_nonneg (a b : ℕ) : 0 ≤ Dif a b := by
  have h : W a * W b ≤ vonMangoldt a * vonMangoldt b :=
    mul_le_mul (W_le_vonMangoldt a) (W_le_vonMangoldt b) (W_nonneg b) vonMangoldt_nonneg
  unfold Dif
  linarith

lemma Dif_eq_zero (ha : ¬Proper a) (hb : ¬Proper b) : Dif a b = 0 := by
  unfold Dif
  rw [lam_eq_W_of_not_proper ha, lam_eq_W_of_not_proper hb, sub_self]

lemma Dif_le_log_sq (a b n : ℕ) (hn : 1 ≤ n) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (ha : a ≤ n) (hb : b ≤ n) : Dif a b ≤ (Real.log n) ^ 2 := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hap : (0 : ℝ) < a := Nat.cast_pos.mpr ha1
  have hbp : (0 : ℝ) < b := Nat.cast_pos.mpr hb1
  have h0 : 0 ≤ W a * W b := mul_nonneg (W_nonneg a) (W_nonneg b)
  have h1 : vonMangoldt a ≤ Real.log a := lam_le_log a
  have h2 : vonMangoldt b ≤ Real.log b := lam_le_log b
  have h3 : Real.log a ≤ Real.log n := Real.log_le_log hap (by exact_mod_cast ha)
  have h4 : Real.log b ≤ Real.log n := Real.log_le_log hbp (by exact_mod_cast hb)
  have hprod : Real.log a * Real.log b ≤ Real.log n * Real.log n :=
    mul_le_mul h3 h4 (Real.log_nonneg (by exact_mod_cast hb1))
      (Real.log_nonneg (by exact_mod_cast hn))
  calc Dif a b
      = vonMangoldt a * vonMangoldt b - W a * W b := rfl
    _ ≤ vonMangoldt a * vonMangoldt b := by linarith
    _ ≤ Real.log a * Real.log b :=
        mul_le_mul h1 h2 vonMangoldt_nonneg (Real.log_nonneg (by exact_mod_cast ha1))
    _ ≤ Real.log n * Real.log n := hprod
    _ = (Real.log n) ^ 2 := (sq (Real.log n)).symm

/-- The set of proper prime powers in `[0, n]`. -/
def ProperSet (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun k => IsPrimePow k ∧ ¬Nat.Prime k

lemma card_ProperSet_le (n m : ℕ) (h2 : 2 ≤ m)
    (hexp : ∀ k ∈ ProperSet n, ∃ p e, Nat.Prime p ∧ 2 ≤ e ∧ p ^ e = k ∧ e ≤ m) :
    (ProperSet n).card ≤ (Nat.sqrt n + 1) * m := by
  set P : Finset ℕ := (Finset.range (Nat.sqrt n + 1)).filter Nat.Prime with hP
  have hsub : (ProperSet n) ⊆ (P ×ˢ Finset.Icc 2 m).image (fun q : ℕ × ℕ => q.1 ^ q.2) := by
    intro k hk
    have hmem := hexp k hk
    simp only [ProperSet, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hklt, hip, hnp⟩ := hk
    obtain ⟨p, e, hp, he2, hke, hem⟩ := hmem
    have hpsqrt : p * p ≤ n := by
      calc p * p = p ^ 2 := (sq p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by exact_mod_cast hp.pos) he2
        _ ≤ n := by rw [hke]; exact Nat.le_of_lt_succ hklt
    have hle : p ≤ Nat.sqrt n := Nat.le_sqrt.mpr hpsqrt
    have hpm : p ∈ P := by
      rw [hP]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hprod : (p, e) ∈ P ×ˢ Finset.Icc 2 m :=
      Finset.mk_mem_product hpm (Finset.mem_Icc.mpr ⟨he2, hem⟩)
    rw [← hke]
    exact Finset.mem_image_of_mem _ hprod
  calc (ProperSet n).card
      ≤ ((P ×ˢ Finset.Icc 2 m).image (fun q : ℕ × ℕ => q.1 ^ q.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (P ×ˢ Finset.Icc 2 m).card := Finset.card_image_le
    _ = P.card * (Finset.Icc 2 m).card := Finset.card_product _ _
    _ ≤ (Nat.sqrt n + 1) * m := by
        have h1 : P.card ≤ Nat.sqrt n + 1 := by
          have h := Finset.card_le_card
            (Finset.filter_subset Nat.Prime (Finset.range (Nat.sqrt n + 1)))
          rw [Finset.card_range] at h
          exact h
        have h2c : (Finset.Icc 2 m).card ≤ m := by
          rw [Nat.card_Icc]; omega
        exact mul_le_mul h1 h2c (by norm_num) (by omega)

/-- `4000·m³ ≤ 2^(m/2)` for all `m ≥ 64`. -/
lemma pow_half_ge (m : ℕ) (hm : 64 ≤ m) : (4000 : ℝ) * (m : ℝ) ^ 3 ≤ (2 : ℝ) ^ ((m : ℝ) / 2) := by
  have key : ∀ k : ℕ, 64 ≤ k →
      (4000 : ℝ) * (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ ((k : ℝ) / 2) →
      (4000 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 3 ≤ (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    intro k hk hS
    have hge9 : (9 : ℝ) ≤ k := le_trans (by norm_num : (9 : ℝ) ≤ 64) (by exact_mod_cast hk)
    have hsplit : (((k + 1 : ℕ) : ℝ)) / 2 = (k : ℝ) / 2 + 1 / 2 := by
      rw [Nat.cast_add, add_div]
      norm_num
    have h1 : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2) = (2 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hsplit]
      exact Real.rpow_add (x := (2 : ℝ)) (by norm_num) ((k : ℝ) / 2) ((1 : ℝ) / 2)
    have h2 : (10 : ℝ) / 9 ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      have hbase : (10 : ℝ) / 9 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      rw [Real.sqrt_eq_rpow] at hbase
      exact hbase
    have h3 : (1 : ℝ) + 1 / (k : ℝ) ≤ (10 : ℝ) / 9 := by
      have hinv : 1 / (k : ℝ) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) hge9
      linarith
    have h4 : ((k + 1 : ℕ) : ℝ) ≤ k * ((10 : ℝ) / 9) := by
      have hkid : ((k + 1 : ℕ) : ℝ) = k * (1 + 1 / (k : ℝ)) := by
        push_cast
        field_simp
      rw [hkid]
      nlinarith
    have h5 : ((k + 1 : ℕ) : ℝ) ^ 3 ≤ k ^ 3 * ((10 : ℝ) / 9) ^ 3 := by
      have hcub : ((k + 1 : ℕ) : ℝ) ^ 3 ≤ (k * ((10 : ℝ) / 9)) ^ 3 :=
        rpow_nat_le (by positivity) h4 3
      rw [mul_pow] at hcub
      exact hcub
    have hfac : ((10 : ℝ) / 9) ^ 3 ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      have hbase : ((10 : ℝ) / 9) ^ 3 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      rw [Real.sqrt_eq_rpow] at hbase
      exact hbase
    calc (4000 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 3
        ≤ (4000 : ℝ) * k ^ 3 * ((10 : ℝ) / 9) ^ 3 := by nlinarith
      _ ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * ((10 : ℝ) / 9) ^ 3 := by
          exact mul_le_mul_of_nonneg_right hS (by positivity)
      _ ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2) := h1.symm
  have h64 : (4000 : ℝ) * ((64 : ℕ) : ℝ) ^ 3 ≤ (2 : ℝ) ^ (((64 : ℕ) : ℝ) / 2) := by
    norm_num
  have hall : ∀ k : ℕ,
      (4000 : ℝ) * ((64 + k : ℕ) : ℝ) ^ 3 ≤ (2 : ℝ) ^ (((64 + k : ℕ) : ℝ) / 2) := by
    intro k
    induction k with
    | zero => simpa using h64
    | succ i ih =>
      have h64i : 64 ≤ 64 + i := by omega
      have hstep := key (64 + i) h64i ih
      have hshift : ((64 + (i + 1) : ℕ) : ℝ) = ((64 + i + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hshift]
      simpa using hstep
  have hsplit : m = 64 + (m - 64) := by omega
  rw [hsplit]
  exact hall (m - 64)

/-- Sum of a constant over a decidable predicate equals card times constant. -/
lemma sum_const_filter {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p] (c : ℝ) :
    (∑ x ∈ s, if p x then c else 0) = (s.filter p).card * c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    by_cases hpa : p a
    · rw [Finset.sum_insert ha, if_pos hpa, ih, Finset.filter_insert, if_pos hpa,
        Finset.card_insert_of_notMem (by simp [ha])]
      push_cast
      ring
    · rw [Finset.sum_insert ha, if_neg hpa, ih, Finset.filter_insert, if_neg hpa]
      simp

/-- Nested-range sums over an affine grid reindex onto a single range. -/
lemma sum_grid (f : ℕ → ℝ) (X6 X5 : ℕ) :
    (∑ i ∈ Finset.range X6, ∑ j ∈ Finset.range X5, f (i * X5 + j))
      = ∑ t ∈ Finset.range (X6 * X5), f t := by
  induction X6 with
  | zero => simp
  | succ k ih =>
    have hmul : (k + 1) * X5 = k * X5 + X5 := Nat.succ_mul k X5
    rw [hmul, Finset.sum_range_succ, ih, Finset.sum_range_add]

theorem Conjectures.Cuts.Task1181504451851151c09a4be6 : (∃ (x1 : ℕ),   ∀ x2 ≥ x1,     have x4 : ℕ := (2 : ℕ) ^ x2;     have x5 : ℕ := (2 : ℕ) ^ (x2 - x2 / (4 : ℕ));     have x6 : ℕ := (2 : ℕ) ^ (x2 / (4 : ℕ) - (3 : ℕ));     have x7 : ℕ → ℕ → ℕ := fun (x7 x8 : ℕ) => x4 / (2 : ℕ) + x7 * x5 + x8;     have x8 : ℕ → ℝ := fun (x8 : ℕ) => if Nat.Prime x8 then Real.log ↑x8 else (0 : ℝ);     ∑ x9 ∈ Finset.range x6, ∑ x10 ∈ Finset.range x5, ArithmeticFunction.vonMangoldt (x7 x9 x10) * ArithmeticFunction.vonMangoldt (x4 - x7 x9 x10) - ∑ x9 ∈ Finset.range x6, ∑ x10 ∈ Finset.range x5, x8 (x7 x9 x10) * x8 (x4 - x7 x9 x10) ≤ ↑x4 / (1000 : ℝ)) := by
  classical
  refine ⟨64, fun x2 hx2 => ?_⟩
  dsimp only
  -- name the pieces
  set n : ℕ := (2 : ℕ) ^ x2 with hndef
  set X5 : ℕ := (2 : ℕ) ^ (x2 - x2 / 4) with hX5def
  set X6 : ℕ := (2 : ℕ) ^ (x2 / 4 - 3) with hX6def
  have hx4 : 16 ≤ x2 / 4 := by omega
  have h8n : 8 ≤ n := by
    rw [hndef]
    calc (8 : ℕ) ≤ (2 : ℕ) ^ 6 := by norm_num
      _ ≤ (2 : ℕ) ^ x2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX6X5 : X6 * X5 = n / 8 := by
    rw [hX6def, hX5def, ← Nat.pow_add, hndef]
    have hexp : (x2 / 4 - 3) + (x2 - x2 / 4) = x2 - 3 := by omega
    rw [hexp]
    have h8 : (2 : ℕ) ^ x2 = (2 : ℕ) ^ (x2 - 3) * 8 := by
      have h := Nat.pow_add (2 : ℕ) (x2 - 3) 3
      rw [show (x2 - 3) + 3 = x2 from by omega, show (2 : ℕ) ^ 3 = 8 from by norm_num] at h
      exact h
    exact (Nat.div_eq_of_eq_mul_left (by norm_num) h8).symm
  -- rewrite the goal's w-summands into `W`
  have hWiff : ∀ k : ℕ, (if Nat.Prime k then Real.log (k : ℝ) else 0) = W k := fun _ => rfl
  simp only [hWiff]
  -- reindex both double sums onto `t ∈ range (n/8)`
  have hL : (∑ i ∈ Finset.range X6, ∑ j ∈ Finset.range X5,
      vonMangoldt (n / 2 + i * X5 + j) * vonMangoldt (n - (n / 2 + i * X5 + j)))
      = ∑ t ∈ Finset.range (n / 8), vonMangoldt (n / 2 + t) * vonMangoldt (n - (n / 2 + t)) := by
    rw [← hX6X5]
    simp only [add_assoc]
    exact sum_grid (fun t => vonMangoldt (n / 2 + t) * vonMangoldt (n - (n / 2 + t))) X6 X5
  have hR : (∑ i ∈ Finset.range X6, ∑ j ∈ Finset.range X5,
      W (n / 2 + i * X5 + j) * W (n - (n / 2 + i * X5 + j)))
      = ∑ t ∈ Finset.range (n / 8), W (n / 2 + t) * W (n - (n / 2 + t)) := by
    rw [← hX6X5]
    simp only [add_assoc]
    exact sum_grid (fun t => W (n / 2 + t) * W (n - (n / 2 + t))) X6 X5
  rw [hL, hR, ← Finset.sum_sub_distrib]
  have hD : (∑ t ∈ Finset.range (n / 8),
      (vonMangoldt (n / 2 + t) * vonMangoldt (n - (n / 2 + t))
        - W (n / 2 + t) * W (n - (n / 2 + t))))
      = ∑ t ∈ Finset.range (n / 8), Dif (n / 2 + t) (n - (n / 2 + t)) :=
    Finset.sum_congr rfl (fun t _ => rfl)
  rw [hD]
  -- the exceptional set and the two injective images
  set E : Finset ℕ := (Finset.range (n / 8)).filter
    (fun t => Proper (n / 2 + t) ∨ Proper (n - (n / 2 + t))) with hE
  have hA' : ∀ t ∈ Finset.range (n / 8), n / 2 + t < n := by
    intro t ht
    have ht8 : t < n / 8 := by simpa using ht
    have hkey : n / 2 + n / 8 ≤ n := by
      have h1 : (n / 2) * 2 ≤ n := Nat.div_mul_le_self n 2
      have h2 : (n / 8) * 8 ≤ n := Nat.div_mul_le_self n 8
      have h3 : 8 * (n / 2 + n / 8) ≤ 8 * n := by
        calc 8 * (n / 2 + n / 8) = 8 * (n / 2) + 8 * (n / 8) := by ring
          _ = 4 * ((n / 2) * 2) + (n / 8) * 8 := by ring
          _ ≤ 4 * n + n := by gcongr
          _ ≤ 8 * n := by omega
      exact Nat.le_of_mul_le_mul_left h3 (by norm_num)
    omega
  have hA1 : ∀ t ∈ Finset.range (n / 8), 1 ≤ n / 2 + t := by
    intro t ht; omega
  have hB1 : ∀ t ∈ Finset.range (n / 8), 1 ≤ n - (n / 2 + t) := by
    intro t ht
    have ht8 : t < n / 8 := by simpa using ht
    omega
  have hBn : ∀ t ∈ Finset.range (n / 8), n - (n / 2 + t) ≤ n := by
    intro t ht; omega
  have hstep : (∑ t ∈ Finset.range (n / 8), Dif (n / 2 + t) (n - (n / 2 + t)))
      ≤ (E.card : ℝ) * (Real.log n) ^ 2 := by
    have hid : (∑ t ∈ Finset.range (n / 8),
        (if Proper (n / 2 + t) ∨ Proper (n - (n / 2 + t)) then (Real.log n) ^ 2 else 0))
        = (E.card : ℝ) * (Real.log n) ^ 2 := by
      rw [hE]
      exact sum_const_filter _
    refine le_trans (Finset.sum_le_sum (fun t ht => ?_)) (le_of_eq hid)
    by_cases hex : Proper (n / 2 + t) ∨ Proper (n - (n / 2 + t))
    · rw [if_pos hex]
      rcases hex with h | h
      · exact Dif_le_log_sq _ _ n (by omega) (hA1 t ht) (hB1 t ht)
          (le_of_lt (hA' t ht)) (hBn t ht)
      · exact Dif_le_log_sq _ _ n (by omega) (hA1 t ht) (hB1 t ht)
          (le_of_lt (hA' t ht)) (hBn t ht)
    · rw [if_neg hex]
      have h1 : ¬Proper (n / 2 + t) := fun h => hex (Or.inl h)
      have h2 : ¬Proper (n - (n / 2 + t)) := fun h => hex (Or.inr h)
      rw [Dif_eq_zero h1 h2]
  set A : Finset ℕ := (Finset.range (n / 8)).filter (fun t => Proper (n / 2 + t)) with hAdef
  set B : Finset ℕ := (Finset.range (n / 8)).filter (fun t => Proper (n - (n / 2 + t))) with hBdef
  have hEsub : E ⊆ A ∪ B := by
    intro t ht
    simp only [hE, hAdef, hBdef, Finset.mem_union, Finset.mem_filter] at ht ⊢
    tauto
  have hcardE : E.card ≤ A.card + B.card := by
    calc E.card ≤ (A ∪ B).card := Finset.card_le_card hEsub
      _ ≤ A.card + B.card := Finset.card_union_le A B
  have hAcard : A.card ≤ (ProperSet n).card := by
    have hsub : (A.image (fun t : ℕ => n / 2 + t)) ⊆ ProperSet n := by
      intro k hk
      simp only [Finset.mem_image] at hk
      obtain ⟨t, ht1, rfl⟩ := hk
      simp only [hAdef, Finset.mem_filter, Finset.mem_range] at ht1
      obtain ⟨ht, hpr⟩ := ht1
      obtain ⟨hip, hnp⟩ := hpr
      simp only [ProperSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, ⟨hip, hnp⟩⟩
    have hcard := Finset.card_image_of_injOn
      (s := A) (f := fun t : ℕ => n / 2 + t) (fun x _ y _ h => by simpa using h)
    calc A.card = (A.image (fun t : ℕ => n / 2 + t)).card := hcard.symm
      _ ≤ (ProperSet n).card := Finset.card_le_card hsub
  have hBcard : B.card ≤ (ProperSet n).card := by
    have hinj : Set.InjOn (fun t : ℕ => n - (n / 2 + t)) (↑B : Set ℕ) := by
      intro x hx y hy h
      simp only [hBdef, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      obtain ⟨hx1, _⟩ := hx
      obtain ⟨hy1, _⟩ := hy
      simp only at h
      omega
    have hsub : (B.image (fun t : ℕ => n - (n / 2 + t))) ⊆ ProperSet n := by
      intro k hk
      simp only [Finset.mem_image] at hk
      obtain ⟨t, ht1, rfl⟩ := hk
      simp only [hBdef, Finset.mem_filter, Finset.mem_range] at ht1
      obtain ⟨ht, hpr⟩ := ht1
      obtain ⟨hip, hnp⟩ := hpr
      simp only [ProperSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, ⟨hip, hnp⟩⟩
    have hcard := Finset.card_image_of_injOn
      (s := B) (f := fun t : ℕ => n - (n / 2 + t)) hinj
    calc B.card = (B.image (fun t : ℕ => n - (n / 2 + t))).card := hcard.symm
      _ ≤ (ProperSet n).card := Finset.card_le_card hsub
  have hexp : ∀ k ∈ ProperSet n, ∃ p e, Nat.Prime p ∧ 2 ≤ e ∧ p ^ e = k ∧ e ≤ x2 := by
    intro k hk
    have hmem : k < n + 1 ∧ IsPrimePow k ∧ ¬Nat.Prime k := by
      have h := Finset.mem_filter.mp hk
      exact ⟨Finset.mem_range.mp h.1, h.2⟩
    obtain ⟨hklt, hip, hnp⟩ := hmem
    obtain ⟨p, e, hp, he0, hke⟩ := (isPrimePow_nat_iff k).mp hip
    have he2 : 2 ≤ e := by
      by_contra hc
      push_neg at hc
      have h1 : e = 1 := by omega
      rw [h1, Nat.pow_one] at hke
      subst hke
      exact hnp hp
    have hx2e : e ≤ x2 := by
      have h2e : (2 : ℕ) ^ e ≤ (2 : ℕ) ^ x2 := by
        calc (2 : ℕ) ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
          _ ≤ (2 : ℕ) ^ x2 := by rw [hke, ← hndef]; exact Nat.le_of_lt_succ hklt
      exact (Nat.pow_le_pow_iff_right (by decide)).mp h2e
    exact ⟨p, e, hp, he2, hke, hx2e⟩
  have hPS : (ProperSet n).card ≤ (Nat.sqrt n + 1) * x2 :=
    card_ProperSet_le n x2 (le_trans (by decide) hx2) hexp
  -- numeric finale
  have hsqrt : Real.sqrt n = (2 : ℝ) ^ ((x2 : ℝ) / 2) := by
    rw [hndef, Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg (2 : ℕ))]
    congr 1
    field_simp
  have hlogn : Real.log n = (x2 : ℝ) * Real.log 2 := by
    rw [hndef, Nat.cast_pow, Real.log_pow]
    norm_num
  have hlog2sq : (Real.log 2) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : Real.log 2 ≤ 1 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
        _ = 1 := by rw [Real.log_exp]
    have hsq : (Real.log 2) * (Real.log 2) ≤ 1 * 1 := mul_le_mul h1 h1 h0 (by norm_num)
    simpa [sq] using hsq
  have hchain : ((E.card : ℝ) * (Real.log n) ^ 2) ≤ (n : ℝ) / 1000 := by
    have hs1 : (1 : ℝ) ≤ Real.sqrt n :=
      Real.le_sqrt_of_sq_le (by norm_num; exact Nat.one_le_cast.mpr (le_trans (by decide) h8n))
    have hbridge : ((Nat.sqrt n : ℝ)) ≤ Real.sqrt n :=
      Real.le_sqrt_of_sq_le (by push_cast; exact_mod_cast Nat.sqrt_le' n)
    have hc1 : ((E.card : ℝ)) ≤ 4 * Real.sqrt n * (x2 : ℝ) := by
      have hAB : ((E.card : ℕ) : ℝ) ≤ ((A.card + B.card : ℕ) : ℝ) := by exact_mod_cast hcardE
      have hPS1 : ((A.card : ℕ) : ℝ) ≤ ((ProperSet n).card : ℝ) := by exact_mod_cast hAcard
      have hPS2 : ((B.card : ℕ) : ℝ) ≤ ((ProperSet n).card : ℝ) := by exact_mod_cast hBcard
      have hPSr : (((ProperSet n).card : ℕ) : ℝ)
          ≤ ((Nat.sqrt n : ℝ) + 1) * ((x2 : ℝ)) := by exact_mod_cast hPS
      calc (E.card : ℝ) ≤ ((A.card + B.card : ℕ) : ℝ) := hAB
        _ ≤ 2 * ((ProperSet n).card : ℝ) := by
            rw [Nat.cast_add]
            linarith
        _ ≤ 2 * (((Nat.sqrt n : ℝ) + 1) * ((x2 : ℝ))) := by linarith
        _ ≤ 4 * Real.sqrt n * ((x2 : ℝ)) := by
            have h2s : ((Nat.sqrt n : ℝ) + 1) ≤ 2 * Real.sqrt n := by linarith [hs1, hbridge]
            have hx0 : (0 : ℝ) ≤ (x2 : ℝ) := Nat.cast_nonneg x2
            have hstp : ((Nat.sqrt n : ℝ) + 1) * (x2 : ℝ) ≤ 2 * Real.sqrt n * (x2 : ℝ) :=
              mul_le_mul_of_nonneg_right h2s hx0
            have hstp2 : 2 * (((Nat.sqrt n : ℝ) + 1) * (x2 : ℝ))
                ≤ 2 * (2 * Real.sqrt n * (x2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hstp (by norm_num)
            calc 2 * (((Nat.sqrt n : ℝ) + 1) * ((x2 : ℝ)))
                ≤ 2 * (2 * Real.sqrt n * (x2 : ℝ)) := hstp2
              _ = 4 * Real.sqrt n * (x2 : ℝ) := by ring
    have hc2 : (Real.log n) ^ 2 ≤ ((x2 : ℝ)) ^ 2 := by
      rw [hlogn]
      have hpow : ((x2 : ℝ) * Real.log 2) ^ 2 = (x2 : ℝ) ^ 2 * (Real.log 2) ^ 2 := by ring
      rw [hpow]
      calc (x2 : ℝ) ^ 2 * (Real.log 2) ^ 2 ≤ (x2 : ℝ) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hlog2sq (by positivity)
        _ = (x2 : ℝ) ^ 2 := by ring
    have hc3 : 4 * Real.sqrt n * (x2 : ℝ) * ((x2 : ℝ)) ^ 2 ≤ (n : ℝ) / 1000 := by
      have hX2 : ((2 : ℝ) ^ ((x2 : ℝ) / 2)) ^ 2
          = (2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2) := by ring
      have hX0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((x2 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
      have hstep1 : (4000 : ℝ) * (x2 : ℝ) ^ 3 * (2 : ℝ) ^ ((x2 : ℝ) / 2)
          ≤ (2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2) :=
        mul_le_mul (pow_half_ge x2 hx2)
          (le_refl ((2 : ℝ) ^ ((x2 : ℝ) / 2))) hX0 hX0
      have hstep2 : (2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2)
          ≤ (2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2) * 1000 :=
        le_mul_of_one_le_right (mul_nonneg hX0 hX0) (by norm_num : (1 : ℝ) ≤ (1000 : ℝ))
      calc 4 * Real.sqrt n * (x2 : ℝ) * ((x2 : ℝ)) ^ 2
          = (4000 : ℝ) * (x2 : ℝ) ^ 3 * (2 : ℝ) ^ ((x2 : ℝ) / 2) / 1000 := by
            rw [hsqrt]
            field_simp
            ring
        _ ≤ ((2 : ℝ) ^ ((x2 : ℝ) / 2)) ^ 2 / 1000 := by
            rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1000), hX2]
            linarith [hstep1, hstep2, mul_nonneg hX0 hX0]
        _ = (n : ℝ) / 1000 := by
            rw [← hsqrt, Real.sq_sqrt (Nat.cast_nonneg n)]
    calc (E.card : ℝ) * (Real.log n) ^ 2
        ≤ 4 * Real.sqrt n * (x2 : ℝ) * ((x2 : ℝ)) ^ 2 :=
          mul_le_mul hc1 hc2 (sq_nonneg _) (by positivity)
      _ ≤ (n : ℝ) / 1000 := hc3
  linarith [hstep, hchain]

end

end Task118150445
