import Mathlib

/-!
# Cut of `L-goldbach-shifted-prime-pair-sieve-566`

The frozen task asks for the explicit upper bound `(283/50 + eps) C0 N localFactor / (log N)^2` on the number
of primes `p ≤ N` with `p + h` prime, uniformly for every `0 < h < N`, with `C0` the twin-prime constant and
`localFactor` the product over the odd prime factors of `h`.  The brief names the obstacle: uniformity in the
moving residue `-h` while separating the large prime factors of the sieve moduli; a fixed-shift estimate
cannot be substituted.  The parent had no cut and no discussion thread.

The shift range is split at `h = sqrt N`.  Two independent inputs are isolated; the gluing is a case split.

* `h₁` (short shifts): the same bound for `0 < h <= sqrt N`.
* `h₂` (long shifts): the same bound for `sqrt N < h < N`.

Combination: every `h` with `0 < h < N` lies in exactly one of the two ranges.
-/

-- child 1 zh: 短移位（解析输入）：对每个 ε>0 与充分大的 N，所有 0 < h ≤ √N 使差为 h 的素数对计数不超过 (283/50+ε)·C₀·N·localFactor/(log N)²。
-- child 1 en: Short shifts (analytic input): for each eps>0 and all large N, every h with 0 < h at most sqrt N has its prime-pair count bounded by (283/50+eps) times C0 times N times localFactor over (log N) squared.
-- child 2 zh: 长移位（解析输入）：对每个 ε>0 与充分大的 N，所有 √N < h < N 使差为 h 的素数对计数不超过 (283/50+ε)·C₀·N·localFactor/(log N)²。
-- child 2 en: Long shifts (analytic input): for each eps>0 and all large N, every h with sqrt N below h below N has its prime-pair count bounded by (283/50+eps) times C0 times N times localFactor over (log N) squared.

theorem Conjectures.Cuts.Cutce58a9316dc530cc3485c60a
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N h : ℕ, N₀ ≤ N → 0 < h → h ≤ Nat.sqrt N → (((Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ p+h ≤ N ∧ Nat.Prime (p+h))).card : ℝ) ≤ ((283/50 : ℝ)+ε)*(∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1)*(N : ℝ)*(∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2))/(Real.log (N : ℝ))^2)
    (h₂ : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N h : ℕ, N₀ ≤ N → 0 < h → Nat.sqrt N < h → h < N → (((Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ p+h ≤ N ∧ Nat.Prime (p+h))).card : ℝ) ≤ ((283/50 : ℝ)+ε)*(∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1)*(N : ℝ)*(∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2))/(Real.log (N : ℝ))^2) :(let C₀ : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1; ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N h : ℕ, N₀ ≤ N → 0 < h → h < N → let pairs := (Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ p+h ≤ N ∧ Nat.Prime (p+h)); let localFactor : ℝ := ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2); (pairs.card : ℝ) ≤ ((283/50 : ℝ)+ε)*C₀*(N : ℝ)*localFactor/(Real.log (N : ℝ))^2) := by
  intro C₀ ε hε
  obtain ⟨N₁, h₁⟩ := h₁ ε hε
  obtain ⟨N₂, h₂⟩ := h₂ ε hε
  refine ⟨max N₁ N₂, fun N h hN h0 hhN => ?_⟩
  intro pairs localFactor
  dsimp only [pairs, localFactor, C₀]
  by_cases hq : h ≤ Nat.sqrt N
  · exact h₁ N h (by omega) h0 hq
  · exact h₂ N h (by omega) h0 (by omega) hhN
