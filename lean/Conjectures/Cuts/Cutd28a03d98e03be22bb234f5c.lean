import Mathlib

/-!
# Cut of `L-goldbach-dyadic-exception-little-o-sqrt`

The frozen task asks that in every dyadic interval `(X, 2X]` the number of even `n ≥ 4` that are
not a sum of two primes is at most `ε √X`, for every `ε > 0` and all large `X`.  The brief names
the route: exploit the sign on the actual exceptional support.  Given a uniform positive
major-arc floor of order `X`, an `o(X^(5/2))` squared deficit of the negative minor-arc part on
those targets suffices; the floor has to be proved as well.  Dyadic summation then recovers the
global `o(√X)` and hence the four-sevenths target.

Here `S(α)` is the log-weighted prime exponential sum up to `n`, `Q = (log₂ (n+2))^2`, the major
arcs are the Farey arcs with `q ≤ Q` and width `Q/(q n)`, `major n` and `minor n` are the
integrals of `S(α)^2 e(-nα)` over the major arcs and over the rest of `[0, 1]` (real part).
Three independent inputs are isolated.

* `h₁` (analytic, uniform major-arc floor): there is `c > 0` such that for all large `X` and
  every even `n ∈ (X, 2X]` the major-arc integral is at least `c n`.
* `h₂` (analytic, negative energy little-o): for every `ε > 0` the sum over even `n ∈ (X, 2X]`
  of `(max 0 (- minor n))^2` is at most `ε X² √X` for all large `X`.
* `h₃` (combinatorial, orthogonality): for every `n`, `Re(major n) + minor n` equals the
  log-weighted number of representations `k + (n - k) = n` with `k, n - k ≤ n`.  This is the
  finite additive-character orthogonality identity for the circle integral.

Combination: for an exceptional `n` the representation sum in `h₃` vanishes, so `minor n` is
the negative of the major-arc integral, hence at most `- c X` by `h₁`; squaring and summing
over the exceptional set and then over all even `n ∈ (X, 2X]` gives
`|E| (c X)^2 ≤ ε c^2 X^2 √X` by `h₂`, and cancelling `c^2 X^2 > 0` yields `|E| ≤ ε √X`.
-/

-- child 1 zh: 主弧一致下界（解析输入）：存在 c>0 与阈值，对充分大的 X 及 (X,2X] 中每个偶数 n，主弧积分实部至少为 c·n。
-- child 1 en: Uniform major-arc floor (analytic input): there are c>0 and a threshold such that for all large X and every even n in (X,2X] the real part of the major-arc integral is at least c times n.
-- child 2 zh: 负能量 little-o（解析输入）：对每个 ε>0 与充分大的 X，(X,2X] 中偶数 n 的次弧积分负部平方之和至多为 ε·X²·√X。
-- child 2 en: Negative-energy little-o (analytic input): for every epsilon>0 and all large X, the sum over even n in (X,2X] of the squared negative part of the minor-arc integral is at most epsilon times X squared times the square root of X.
-- child 3 zh: 正交恒等式（组合提取）：对每个 n，主弧积分实部与次弧积分实部之和等于对数加权表示数 Σ_k w(k)·w(n−k)。
-- child 3 en: Orthogonality identity (combinatorial extraction): for every n, the real part of the major-arc integral plus the minor-arc integral equals the log-weighted representation count sum over k of w(k) times w(n-k).

theorem Conjectures.Cuts.Cutd28a03d98e03be22bb234f5c
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ n : ℕ, X < n → n ≤ 2*X → Even n → c * (n:ℝ) ≤ ((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))}).indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume)).re)
    (h₂ : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (∑ n ∈ (Finset.Ioc X (2*X)).filter (fun n => Even n), (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2) ≤ ε * (X:ℝ)^2 * Real.sqrt (X:ℝ))
    (h₃ : ∀ n : ℕ, ((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))}).indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume)).re + ((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re) = ∑ k ∈ Finset.range (n+1), (if Nat.Prime k then Real.log (k:ℝ) else 0) * (if Nat.Prime (n-k) then Real.log ((n-k):ℝ) else 0)) :
    (let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc X (2*X))).card : ℝ) ≤ ε * Real.sqrt (X : ℝ)) := by
  intro bad
  dsimp only [bad]
  intro ε hε
  obtain ⟨c, hc, X₁, hfloor⟩ := h₁
  obtain ⟨X₂, henergy⟩ := h₂ (ε * c^2) (by positivity)
  refine ⟨max (max X₁ X₂) 1, fun X hX => ?_⟩
  have hX1 : (1 : ℕ) ≤ X := by omega
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hX₁ : X₁ ≤ X := by omega
  have hX₂ : X₂ ≤ X := by omega
  have hmem : ∀ n : ℕ, n ∈ (@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X))) ↔ (X < n ∧ n ≤ 2*X ∧ 4 ≤ n ∧ Even n ∧
      ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) := by
    intro n
    simp only [Finset.mem_filter, Finset.mem_Ioc, and_assoc]
  have key : ∀ n ∈ (@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X))), c * (X:ℝ) ≤ (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re))) := by
    intro n hn
    obtain ⟨hnX, hn2X, hn4, hnE, hnp⟩ := (hmem n).mp hn
    have h0 : ∑ k ∈ Finset.range (n+1), (if Nat.Prime k then Real.log (k:ℝ) else 0) * (if Nat.Prime (n-k) then Real.log ((n-k):ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkn : k ≤ n := by simpa using hk
      have hno : ¬ (Nat.Prime k ∧ Nat.Prime (n-k)) := by
        rintro ⟨hk1, hk2⟩
        exact hnp ⟨k, (n-k), hk1, hk2, by omega⟩
      by_cases hk1 : Nat.Prime k
      · have hk2 : ¬ Nat.Prime (n-k) := fun h => hno ⟨hk1, h⟩
        simp [hk1, hk2]
      · simp [hk1]
    have hsum := h₃ n
    rw [h0] at hsum
    have hf := hfloor X hX₁ n (by omega) (by omega) hnE
    have h1 : c * (X:ℝ) ≤ -((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re) := by
      have : (X:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : X ≤ n)
      nlinarith
    exact le_trans h1 (le_max_right 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))
  have hsub : (@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X))) ⊆ (Finset.Ioc X (2*X)).filter (fun n => Even n) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨((hmem n).mp hn).1, ((hmem n).mp hn).2.1⟩,
      ((hmem n).mp hn).2.2.2.1⟩
  have hcX : (0:ℝ) < c^2 * (X:ℝ)^2 := by positivity
  have hfinal : ((((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X)))).card : ℝ) * (c^2 * (X:ℝ)^2) ≤ (ε * Real.sqrt (X:ℝ)) * (c^2 * (X:ℝ)^2)) := by
    have hcard : ((((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X)))).card : ℝ) * (c * (X:ℝ))^2) =
        ∑ n ∈ (@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X))), (c * (X:ℝ))^2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hstep1 : ((((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X)))).card : ℝ) * (c * (X:ℝ))^2) ≤ ∑ n ∈ (@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X))), (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2 := by
      rw [hcard]
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (n := 2) (by positivity) (key n hn)
    have hstep2 : (∑ n ∈ (@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X))), (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2) ≤ ∑ n ∈ (Finset.Ioc X (2*X)).filter (fun n => Even n), (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
    have hstep3 : (∑ n ∈ (Finset.Ioc X (2*X)).filter (fun n => Even n), (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤((Nat.log 2 (n+2))^2) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0):ℂ)*(Complex.exp (((2*Real.pi*(k:ℝ)*t:ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*-(n:ℝ)*t:ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2) ≤ ε * c^2 * (X:ℝ)^2 * Real.sqrt (X:ℝ) :=
      henergy X hX₂
    have hstep4 : ((((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X)))).card : ℝ) * (c * (X:ℝ))^2) ≤ ε * c^2 * (X:ℝ)^2 * Real.sqrt (X:ℝ) :=
      le_trans (le_trans hstep1 hstep2) hstep3
    have : (((((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Finset.Ioc X (2*X)))).card : ℝ) * (c * (X:ℝ))^2) ≤ (ε * Real.sqrt (X:ℝ)) * (c^2 * (X:ℝ)^2)) := by
      convert hstep4 using 1
      ring
    rw [show (c * (X:ℝ))^2 = c^2 * (X:ℝ)^2 by ring] at this
    exact this
  exact le_of_mul_le_mul_right hfinal hcX
