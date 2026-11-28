import Mathlib

/-!
# Cut of `L-goldbach-dyn-short-restricted-power-saving`

The frozen task asks for constants `C, δ > 0` such that in every window `[y, y + ⌊y^(13/225)⌋]`
inside `[X, 2X]` the number of even `n` with no prime pair `p + q = n` and `p` in the
square-root band `[√X, 2√X]` is at most `C (⌊y^(13/225)⌋ + 1) X^(-δ)`.  The brief names the
route: a positive singular-series main term and a uniform local mean-square error to which the
verified exception-energy lemma applies.  That lemma has the shape of the verified module
`Conjectures.Goldbach.DynExceptionEnergy`, `|{n ∈ E : r n = 0}| L^2 ≤ Σ_{n ∈ E} (r n - b n)^2`
when `L ≤ b n` on `E`, and the verified first-mass and collision-budget modules use the scale
`M X = √X / (log X)^2`.

Two independent inputs are isolated; the gluing is the exception-energy argument, carried out in
this file.

* `h₁` (band prime mass, known): the pointwise model `|P X| / log X`, with `P X` the primes of
  the band, is at least `c M X` for one `c > 0` and all large `X`.  The verified
  `DynBlockFirstMass` proves `(1/4)√X ≤ |P X| log X`, so this is the prime number theorem in
  the band.
* `h₂` (local mean-square error, open): for some `C, δ > 0`, in every window the sum over even
  `n` of `(R X n - |P X| / log X)^2` is at most `C (W y + 1) X^(-δ) (M X)^2`.

Combination: on the even `n` of the window with `R X n = 0` the error equals the model, which is
at least `L := c M X > 0`; the energy inequality gives
`|E| (c M X)^2 ≤ Σ (R X n - |P X|/log X)^2 ≤ C (W y + 1) X^(-δ) (M X)^2`, and cancelling gives
the claim with constant `C / c^2`.
-/

-- child 1 zh: 带内素数质量（已知）：存在 c>0 与阈值，使对充分大的 X，模型 |P X|/log X（P X 为 [√X,2√X] 内的素数集）至少为 c·√X/(log X)²。
-- child 1 en: Band prime mass (known): there are c>0 and a threshold such that for all large X the model |P X|/log X, with P X the primes in [sqrt X, 2 sqrt X], is at least c times sqrt X divided by (log X)^2.
-- child 2 zh: 局部均方误差（开放）：存在 C, δ>0 与阈值，使每个落在 [X,2X] 的窗 [y, y+⌊y^(13/225)⌋] 内的偶数 n 上 (R X n − |P X|/log X)² 之和至多为 C·(⌊y^(13/225)⌋+1)·X^(−δ)·(√X/(log X)²)²。
-- child 2 en: Local mean-square error (open): there are C, delta>0 and a threshold such that in every window [y, y+floor(y^(13/225))] inside [X,2X] the sum over even n of (R X n - |P X|/log X)^2 is at most C times (floor(y^(13/225))+1) times X^(-delta) times (sqrt X/(log X)^2)^2.

theorem Conjectures.Cuts.Cut042ba02e8896964e132be613
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2) ≤ (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)))
    (h₂ : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ y : ℕ, X ≤ y → y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)) ≤ 2 * X → (∑ n ∈ (Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n), (((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) - (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)))^2) ≤ C * ((Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)) : ℝ) + 1) * (X:ℝ)^(-δ) * ((Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2) :
    (let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime; let R := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → (((Finset.Icc y (y + W y)).filter (fun n => Even n ∧ R X n = 0)).card : ℝ) ≤ C * ((W y : ℝ) + 1) * (X : ℝ) ^ (-δ)) := by
  intro W P R
  dsimp only [W, P, R]
  obtain ⟨c, hc, X₁, h₁⟩ := h₁
  obtain ⟨C, δ, hC, hδ, X₂, h₂⟩ := h₂
  refine ⟨C / c^2, δ, by positivity, hδ, max (max X₁ X₂) 2, fun X hX y hy hy2 => ?_⟩
  have hX₁ : X₁ ≤ X := by omega
  have hX₂ : X₂ ≤ X := by omega
  have hX2 : (2 : ℕ) ≤ X := by omega
  have hlog : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast hX2)
  have hMpos : 0 < (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2) := by positivity
  have hL : 0 < c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2) := mul_pos hc hMpos
  have hb : c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2) ≤ (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)) := h₁ X hX₁
  have hE : ((((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n)).filter (fun n => ((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) = 0)).card : ℝ) * (c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 ≤
      ∑ n ∈ (Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n), (((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) - (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)))^2 := by
    calc ((((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n)).filter (fun n => ((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) = 0)).card : ℝ) * (c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2
        = ∑ n ∈ ((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n)).filter (fun n => ((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) = 0), (c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ ((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n)).filter (fun n => ((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) = 0), (((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) - (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)))^2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [(Finset.mem_filter.mp hn).2, zero_sub, neg_sq]
        exact pow_le_pow_left₀ (n := 2) hL.le hb
      _ ≤ ∑ n ∈ (Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n), (((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) - (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)))^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hs : (∑ n ∈ (Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n), (((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) - (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card / Real.log (X:ℝ)))^2) ≤ C * ((Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)) : ℝ) + 1) * (X:ℝ)^(-δ) * ((Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 :=
    h₂ X hX₂ y hy hy2
  have hcard : ((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n ∧ (((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card = 0)).card =
      (((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n)).filter (fun n => ((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) = 0)).card := by
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.cast_eq_zero]
    tauto
  rw [hcard]
  have key : ((((Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)))).filter (fun n => Even n)).filter (fun n => ((((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) = 0)).card : ℝ) * (c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 ≤
      C * ((Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)) : ℝ) + 1) * (X:ℝ)^(-δ) * ((Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 := le_trans hE hs
  have hsq : (0:ℝ) < (c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 := sq_pos_of_pos hL
  have hdiv := (le_div_iff₀ hsq).2 key
  rw [show C * ((Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)) : ℝ) + 1) * (X:ℝ)^(-δ) * ((Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 / (c * (Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2))^2 = C / c^2 * ((Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225)) : ℝ) + 1) * (X:ℝ)^(-δ) by
    field_simp] at hdiv
  exact hdiv
