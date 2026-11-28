import Mathlib

/-!
# Cut of `L-goldbach-exception-four-sevenths-negative-energy`

The frozen task asks for `C` with `Σ_{n even, X ≤ n ≤ 2X} (max 0 (- minor n))^2 ≤ C X^(18/7 + e)` for every
`e > 0` and all large `X`, where `minor n` is the real part of the integral of `S(n, t)^2 e(-n t)` over the
complement of the Farey arcs with `q ≤ Q n = (log₂ (n+2))^2`.  The brief names the obstacle: exploit the
negative-part restriction; the arc mask moves with `n`, so a fixed-mask Parseval alone does not give the claim.
The parent had no cut and no discussion thread.

The dyadic interval is split at its midpoint `3X/2`.  Two independent inputs are isolated; the gluing is done
in this file.

* `h₁` (lower half): the same bound restricted to the even `n ∈ [X, 3X/2]`.
* `h₂` (upper half): the same bound restricted to the even `n ∈ (3X/2, 2X]`.

Combination: the two halves partition the even `n` of `[X, 2X]`, so the sum over the whole interval is at most
`(C₁ + C₂) X^(18/7 + e)`.  Each half is a statement about a moving mask on a shorter interval, which is where
the localised Parseval argument of the brief has to be carried out.
-/

-- child 1 zh: 下半区（解析输入）：对每个 e>0，存在 C 与阈值，使 X ≤ n ≤ 3X/2 中的偶数 n 上次弧负部平方之和不超过 C·X^(18/7+e)。
-- child 1 en: Lower half (analytic input): for each e>0 there are C and a threshold such that the sum over even n with X at most n at most 3X/2 of the squared negative part of the minor-arc integral is at most C times X^(18/7+e).
-- child 2 zh: 上半区（解析输入）：对每个 e>0，存在 C 与阈值，使 3X/2 < n ≤ 2X 中的偶数 n 上次弧负部平方之和不超过 C·X^(18/7+e)。
-- child 2 en: Upper half (analytic input): for each e>0 there are C and a threshold such that the sum over even n with 3X/2 below n at most 2X of the squared negative part of the minor-arc integral is at most C times X^(18/7+e).

theorem Conjectures.Cuts.Cut871fc75bc28dc280f5611abc
    (h₁ : ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (Finset.sum (((Finset.Icc X (2*X)).filter Even).filter (fun n => 2*n ≤ 3*X)) (fun n => (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(((Nat.log 2 (n+2))^2 : ℕ)) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2)) ≤ C * (X:ℝ) ^ (18/7 + e))
    (h₂ : ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (Finset.sum (((Finset.Icc X (2*X)).filter Even).filter (fun n => ¬ (2*n ≤ 3*X))) (fun n => (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(((Nat.log 2 (n+2))^2 : ℕ)) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2)) ≤ C * (X:ℝ) ^ (18/7 + e)) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-minor n))^2)) ≤ C * (X:ℝ) ^ (18/7 + e)) := by
  intro w E S Q arcs f _major minor e he
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := h₁ e he
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := h₂ e he
  refine ⟨C₁ + C₂, max N₁ N₂, by positivity, fun X hX => ?_⟩
  have hs := Finset.sum_filter_add_sum_filter_not (s := ((Finset.Icc X (2*X)).filter Even)) (fun n => 2*n ≤ 3*X) (fun n => (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(((Nat.log 2 (n+2))^2 : ℕ)) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2)
  dsimp only [minor, _major, f, S, E, Q, arcs, w]
  calc (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(((Nat.log 2 (n+2))^2 : ℕ)) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2))
      = (Finset.sum (((Finset.Icc X (2*X)).filter Even).filter (fun n => 2*n ≤ 3*X)) (fun n => (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(((Nat.log 2 (n+2))^2 : ℕ)) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2)) + (Finset.sum (((Finset.Icc X (2*X)).filter Even).filter (fun n => ¬ (2*n ≤ 3*X))) (fun n => (max 0 (-((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(((Nat.log 2 (n+2))^2 : ℕ)) ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))^2)) := hs.symm
    _ ≤ C₁ * (X:ℝ) ^ (18/7 + e) + C₂ * (X:ℝ) ^ (18/7 + e) := by
        exact add_le_add (h₁ X (by omega)) (h₂ X (by omega))
    _ ≤ (C₁ + C₂) * (X:ℝ) ^ (18/7 + e) := by rw [add_mul]
