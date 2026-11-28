import Mathlib

/-!
# Cut of `L-goldbach-adaptive-minor-negative-tail`

The frozen task asks for `C > 0` such that for all large `X` there is a set `D` of size at most `C X^(4/7)` for
which every even `n ∈ [X, 2X]` outside `D` admits an arc-width profile `r` with `1/2 ≤ r q a ≤ 2` and
`T n r ≥ -(3/4) n`, where `T n r` is the real part of the integral of `S(n,t)^2 e(-n t)` over the complement of
the Farey arcs with `q ≤ Q n` widened by the factor `r q a`.  The brief names the obstacle: estimate signed
coefficients and the intersection of failures for a tractable family of boundaries; one good profile per target
suffices, and the blanket absolute fourth-moment route has a counterexample.  The parent had no cut and no
discussion thread.

The dyadic interval is split at its midpoint `3X/2`.  Two independent inputs are isolated; the gluing is done in
this file.

* `h₁` (lower half): the same statement with the even targets restricted to `[X, 3X/2]`.
* `h₂` (upper half): the same statement with the even targets restricted to `(3X/2, 2X]`.

Combination: take `D := D₁ ∪ D₂`; its size is at most `|D₁| + |D₂| ≤ (C₁ + C₂) X^(4/7)`, and a target outside
`D` lies outside both exceptional sets, so the profile from its own half applies.
-/

-- child 1 zh: 下半区（解析输入）：存在 C>0 与阈值，使对充分大的 X 有例外集 D₁，|D₁| ≤ C·X^(4/7)，且 [X, 3X/2] 中每个不属于 D₁ 的偶数 n 都有弧宽剖面 r（1/2 ≤ r ≤ 2）使 T n r ≥ −(3/4)n。
-- child 1 en: Lower half (analytic input): there are C>0 and a threshold such that for all large X some exceptional set D1 of size at most C X^(4/7) leaves every even n in [X, 3X/2] outside D1 with an arc-width profile r (1/2 at most r at most 2) and T n r at least -(3/4)n.
-- child 2 zh: 上半区（解析输入）：存在 C>0 与阈值，使对充分大的 X 有例外集 D₂，|D₂| ≤ C·X^(4/7)，且 (3X/2, 2X] 中每个不属于 D₂ 的偶数 n 都有弧宽剖面 r（1/2 ≤ r ≤ 2）使 T n r ≥ −(3/4)n。
-- child 2 en: Upper half (analytic input): there are C>0 and a threshold such that for all large X some exceptional set D2 of size at most C X^(4/7) leaves every even n in (3X/2, 2X] outside D2 with an arc-width profile r (1/2 at most r at most 2) and T n r at least -(3/4)n.

theorem Conjectures.Cuts.Cutc75d9a688daa02548eff80ac
    (h₁ : (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N, ∃ D : Finset ℕ, (D.card:ℝ) ≤ C*(X:ℝ)^((4:ℝ)/7) ∧ ∀ n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n ∧ 2*n ≤ 3*X), n ∉ D → ∃ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) ∧ -(3/4:ℝ)*(n:ℝ) ≤ ((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (((Nat.log 2 (n+2))^2 : ℕ)) ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re)))
    (h₂ : (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N, ∃ D : Finset ℕ, (D.card:ℝ) ≤ C*(X:ℝ)^((4:ℝ)/7) ∧ ∀ n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n ∧ ¬ (2*n ≤ 3*X)), n ∉ D → ∃ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) ∧ -(3/4:ℝ)*(n:ℝ) ≤ ((intervalIntegral (fun t => ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (((Nat.log 2 (n+2))^2 : ℕ)) ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * ((((Nat.log 2 (n+2))^2 : ℕ)):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ.indicator (fun t => ((Finset.sum (Finset.range (n+1)) (fun k => (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ):ℂ)*(Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))))^2*(Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I))) t) (0:ℝ) 1 MeasureTheory.volume).re))) :(let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let A := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let T := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => (intervalIntegral (fun t => (A n r)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N, ∃ D : Finset ℕ, (D.card:ℝ) ≤ C*(X:ℝ)^((4:ℝ)/7) ∧ ∀ n ∈ Finset.Icc X (2*X), Even n → n ∉ D → ∃ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) ∧ -(3/4:ℝ)*(n:ℝ) ≤ T n r) := by
  intro w E S Q f A T
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := h₂
  refine ⟨C₁ + C₂, by positivity, max N₁ N₂, fun X hX => ?_⟩
  obtain ⟨D₁, hD₁, hp₁⟩ := h₁ X (by omega)
  obtain ⟨D₂, hD₂, hp₂⟩ := h₂ X (by omega)
  dsimp only [T, A, f, S, E, Q, w]
  refine ⟨D₁ ∪ D₂, ?_, fun n hn hE hnD => ?_⟩
  · calc ((D₁ ∪ D₂).card : ℝ) ≤ ((D₁.card + D₂.card : ℕ) : ℝ) := by exact_mod_cast Finset.card_union_le _ _
    _ = (D₁.card:ℝ) + (D₂.card:ℝ) := Nat.cast_add _ _
    _ ≤ C₁*(X:ℝ)^((4:ℝ)/7) + C₂*(X:ℝ)^((4:ℝ)/7) := add_le_add hD₁ hD₂
    _ = (C₁ + C₂)*(X:ℝ)^((4:ℝ)/7) := by rw [add_mul]
  · by_cases hle : 2*n ≤ 3*X
    · have hn1 : n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n ∧ 2*n ≤ 3*X) :=
        Finset.mem_filter.mpr ⟨hn, hE, hle⟩
      have hnD1 : n ∉ D₁ := fun h => hnD (Finset.mem_union_left D₂ h)
      exact hp₁ n hn1 hnD1
    · have hn2 : n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n ∧ ¬ (2*n ≤ 3*X)) :=
        Finset.mem_filter.mpr ⟨hn, hE, hle⟩
      have hnD2 : n ∉ D₂ := fun h => hnD (Finset.mem_union_right D₁ h)
      exact hp₂ n hn2 hnD2
