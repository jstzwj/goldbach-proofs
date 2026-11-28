import Mathlib

/-!
# Cut of `L-goldbach-farey-late-positive-excess`

The frozen task bounds the aggregate positive discrepancy of the first-hit counts over the late range: for all
large even `n` (threshold at least 64), `sum over primes p in (z1, sqrt n] of max 0 (hit n p - (V n (p-1) - V n p))`
is at most `(9/20) V n (sqrt n)`, where `hit n p` counts the central candidates whose complement has least prime
factor `p` and `V n z` is the sieve model at level `z`.  The brief: first hits partition the actual total, the model
drops telescope, and this target leaves `1/20` of the terminal volume in reserve and applies to every subsum.
The parent had no cut and no discussion thread.

The late range of `p` is split at the intermediate level `z3 = floor(n^(5/12))`.  Two independent inputs are
isolated; the gluing is done in this file.

* `h₁` (lower late band): the same bound with the sum restricted to `p <= z3`, budget `9/40`.
* `h₂` (upper late band): the same bound with the sum restricted to `p > z3`, budget `9/40`.

Combination: the two bands partition the range `(z1, sqrt n]`, so the summands add and `9/40 + 9/40 = 9/20`.
-/

-- child 1 zh: 下晚段（筛法输入）：对充分大的偶数 n，p ∈ (n^(1/3), n^(5/12)] 上正部差异之和至多为 (9/40)·V n √n。
-- child 1 en: Lower late band (sieve input): for all large even n, the sum of positive discrepancies over primes p in (n^(1/3), n^(5/12)] is at most (9/40) times V n (sqrt n).
-- child 2 zh: 上晚段（筛法输入）：对充分大的偶数 n，p ∈ (n^(5/12), √n] 上正部差异之和至多为 (9/40)·V n √n。
-- child 2 en: Upper late band (sieve input): for all large even n, the sum of positive discrepancies over primes p in (n^(5/12), sqrt n] is at most (9/40) times V n (sqrt n).

theorem Conjectures.Cuts.Cuta964093e4771829eef521b1b
    (h₁ : ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → (∑ p ∈ (((((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ⌊(n:ℝ)^((1:ℝ)/3)⌋₊ < p))).filter (fun p => p ≤ ⌊(n:ℝ)^((5:ℝ)/12)⌋₊), (max 0 ((((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ (u*(n-u)).minFac = p)).card : ℝ) - ((((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (p-1)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 p).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))))))) ≤ (9/40 : ℝ)*(((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))))
    (h₂ : ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → (∑ p ∈ (((((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ⌊(n:ℝ)^((1:ℝ)/3)⌋₊ < p))).filter (fun p => ¬ (p ≤ ⌊(n:ℝ)^((5:ℝ)/12)⌋₊)), (max 0 ((((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ (u*(n-u)).minFac = p)).card : ℝ) - ((((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (p-1)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 p).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))))))) ≤ (9/40 : ℝ)*(((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ)))) :(let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Z₂ := Nat.sqrt; let hit := fun n p : ℕ => ((I n).filter (fun u => u.Coprime n ∧ (u*(n-u)).minFac = p)).card; ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → (∑ p ∈ (P (Z₂ n)).filter (fun p => Z₁ n < p), max 0 ((hit n p : ℝ) - (V n (p-1) - V n p))) ≤ (9/20 : ℝ)*V n (Z₂ n)) := by
  intro I P V Z₁ Z₂ hit
  obtain ⟨N₁, hN₁, h₁⟩ := h₁
  obtain ⟨N₂, hN₂, h₂⟩ := h₂
  refine ⟨max N₁ N₂, by omega, fun n hn hE => ?_⟩
  dsimp only [I, P, V, Z₁, Z₂, hit]
  have hs := Finset.sum_filter_add_sum_filter_not (s := ((((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ⌊(n:ℝ)^((1:ℝ)/3)⌋₊ < p))) (fun p => p ≤ ⌊(n:ℝ)^((5:ℝ)/12)⌋₊) (fun p => (max 0 ((((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ (u*(n-u)).minFac = p)).card : ℝ) - ((((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (p-1)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 p).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ)))))))
  have ha := h₁ n (by omega) hE
  have hb := h₂ n (by omega) hE
  rw [← hs]
  calc (∑ p ∈ (((((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ⌊(n:ℝ)^((1:ℝ)/3)⌋₊ < p))).filter (fun p => p ≤ ⌊(n:ℝ)^((5:ℝ)/12)⌋₊), (max 0 ((((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ (u*(n-u)).minFac = p)).card : ℝ) - ((((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (p-1)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 p).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))))))) + ∑ p ∈ (((((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ⌊(n:ℝ)^((1:ℝ)/3)⌋₊ < p))).filter (fun p => ¬ (p ≤ ⌊(n:ℝ)^((5:ℝ)/12)⌋₊)), (max 0 ((((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ (u*(n-u)).minFac = p)).card : ℝ) - ((((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (p-1)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 p).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))))))
      ≤ (9/40 : ℝ)*(((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) + (9/40 : ℝ)*(((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) := add_le_add ha hb
    _ = (9/20 : ℝ)*(((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ r ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun r => ¬ r ∣ n), (1-2/(r:ℝ))) := by ring
