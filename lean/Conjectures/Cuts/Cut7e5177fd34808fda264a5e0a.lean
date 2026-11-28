import Mathlib

/-!
# Cut of `L-goldbach-central-rough-chen-mass`

The frozen task asks that, for every large even `N`, the central window `N/4 ≤ p ≤ 3N/4` contains at least
`(99/50) C₀ D N / (log N)^2` primes `p` for which `N - p` is a prime or a product of two primes both above
`N^(1/6)`; `C₀` is the twin-prime constant and `D` the local factor of `N`.  The brief names the route: run
the switching sieve on the central interval, keep the full-`N` normalisation, and separate the prime-prime
count from the rough-semiprime count.  The parent had no cut and no discussion thread.

The two classes of summands are disjoint (a prime is not a product of two primes), so the Chen-type count is
the sum of the prime-prime count and the rough-semiprime count.  Two independent inputs are isolated; the
gluing is done in this file.

* `h₁` (prime-prime central mass): at least `(9/10) C₀ D N / (log N)^2` primes `p` of the window with
  `N - p` prime.
* `h₂` (rough-semiprime central mass): at least `(27/25) C₀ D N / (log N)^2` primes `p` of the window with
  `N - p` a product of two primes both above `N^(1/6)`.

Combination: `9/10 + 27/25 = 99/50`, and the two sets are disjoint, so the sizes add.
-/

-- child 1 zh: 素数加素数的中央质量（解析输入）：对充分大的每个偶数 N，中央窗 [N/4, 3N/4] 中使 N−p 为素数的素数 p 至少有 (9/10)·C₀·D·N/(log N)²。
-- child 1 en: Prime-prime central mass (analytic input): for all large even N, the primes p in the central window with N-p prime number at least nine tenths of C0 times D times N over (log N) squared.
-- child 2 zh: 粗糙半素数的中央质量（解析输入）：对充分大的每个偶数 N，中央窗 [N/4, 3N/4] 中使 N−p 为两个均大于 N^(1/6) 的素数之积的素数 p 至少有 (27/25)·C₀·D·N/(log N)²。
-- child 2 en: Rough-semiprime central mass (analytic input): for all large even N, the primes p in the central window with N-p a product of two primes both above N^(1/6) number at least 27/25 times C0 times D times N over (log N) squared.

theorem Conjectures.Cuts.Cut7e5177fd34808fda264a5e0a
    (h₁ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → (9/10 : ℝ)*((∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1)*(∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2))*(N : ℝ)/(Real.log (N : ℝ))^2) ≤ (((Finset.range (N+1)).filter (fun p => (Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ Nat.Prime (N-p)))).card : ℝ))
    (h₂ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → (27/25 : ℝ)*((∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1)*(∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2))*(N : ℝ)/(Real.log (N : ℝ))^2) ≤ (((Finset.range (N+1)).filter (fun p => (Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ ((N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac) ∧ N < (N-p).minFac^6)))).card : ℝ)) :(let C₀ : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1; ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → let S := (Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ (Nat.Prime (N-p) ∨ (N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac) ∧ N < (N-p).minFac^6)); let D : ℝ := ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2); (99/50 : ℝ)*C₀*D*(N : ℝ)/(Real.log (N : ℝ))^2 ≤ (S.card : ℝ)) := by
  intro C₀
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  refine ⟨max N₁ N₂, fun N hN hE => ?_⟩
  intro S D
  dsimp only [S, D, C₀]
  have hu : ((Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ (Nat.Prime (N-p) ∨ (N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac) ∧ N < (N-p).minFac^6))) =
      ((Finset.range (N+1)).filter (fun p => (Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ Nat.Prime (N-p)))) ∪ ((Finset.range (N+1)).filter (fun p => (Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ ((N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac) ∧ N < (N-p).minFac^6)))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hd : Disjoint ((Finset.range (N+1)).filter (fun p => (Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ Nat.Prime (N-p)))) ((Finset.range (N+1)).filter (fun p => (Nat.Prime p ∧ N ≤ 4*p ∧ 4*p ≤ 3*N ∧ ((N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac) ∧ N < (N-p).minFac^6)))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    obtain ⟨-, -, -, -, hpprime⟩ := hp1
    obtain ⟨-, -, -, -, ⟨hmf, hq, -⟩⟩ := hp2
    have hmf' : (N-p).minFac = N-p := Nat.Prime.minFac_eq hpprime
    rw [hmf'] at hq
    rw [Nat.div_self hpprime.pos] at hq
    exact Nat.not_prime_one hq
  have ha := h₁ N (by omega) hE
  have hb := h₂ N (by omega) hE
  rw [hu, Finset.card_union_of_disjoint hd, Nat.cast_add]
  convert add_le_add ha hb using 1
  ring
