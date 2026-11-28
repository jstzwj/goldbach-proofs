import Mathlib

/-!
# Cut of `L-goldbach-farey-first-hit-middle-lower`

The frozen task is a lower-bound sieve statement at the cube-root level: for all large even `n` the number of
`u` in the central window `[(n+2)/3, 2n/3]` with `u` coprime to `n` and `u (n - u)` free of prime factors at or below
`z₁ = n^(1/3)` is at least the sieve model `V n z₁` minus one eighth of the terminal error `V n √n`.  The brief
names the obstacle: the parity/level barrier HD6 at the cube-root level.  The parent had no cut and no discussion
thread.

The sieve is run in two stages with the intermediate level `z₀ = n^(1/4)`.  Two independent inputs are isolated.

* `h₁` (quarter-root level): the survivors at `z₀` are at least `V n z₀ - V n √n / 16`.
* `h₂` (Buchstab step): the number of survivors lost between `z₀` and `z₁` is at most the model's loss
  `V n z₀ - V n z₁` plus `V n √n / 16`.

Combination: `S n z₁ = S n z₀ - (S n z₀ - S n z₁) >= (V n z₀ - V n √n/16) - (V n z₀ - V n z₁ + V n √n/16) =
V n z₁ - V n √n / 8`.
-/

-- child 1 zh: 四次方根层下界（筛法输入）：对充分大的每个偶数 n，z₀ = ⌊n^(1/4)⌋ 处的幸存数至少为 V n z₀ − V n √n / 16。
-- child 1 en: Quarter-root level (sieve input): for all large even n the survivors at z0 = floor(n^(1/4)) are at least V n z0 minus V n (sqrt n) over 16.
-- child 2 zh: Buchstab 步（筛法输入）：对充分大的每个偶数 n，从 z₀ 到 z₁ = ⌊n^(1/3)⌋ 损失的幸存数至多为模型损失 V n z₀ − V n z₁ 加上 V n √n / 16。
-- child 2 en: Buchstab step (sieve input): for all large even n the survivors lost from z0 to z1 = floor(n^(1/3)) are at most the model loss V n z0 minus V n z1 plus V n (sqrt n) over 16.

theorem Conjectures.Cuts.Cutd49849ccd071653bdb2e4de0
    (h₁ : ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ p ∈ (((Finset.Icc 2 ⌊(n:ℝ)^((1:ℝ)/4)⌋₊).filter Nat.Prime)).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ p ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)))/16 ≤ (((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ ⌊(n:ℝ)^((1:ℝ)/4)⌋₊ < (u*(n-u)).minFac)).card : ℝ))
    (h₂ : ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → (((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ ⌊(n:ℝ)^((1:ℝ)/4)⌋₊ < (u*(n-u)).minFac)).card : ℝ) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ ⌊(n:ℝ)^((1:ℝ)/3)⌋₊ < (u*(n-u)).minFac)).card : ℝ) ≤ ((((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ p ∈ (((Finset.Icc 2 ⌊(n:ℝ)^((1:ℝ)/4)⌋₊).filter Nat.Prime)).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))) - (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ p ∈ (((Finset.Icc 2 ⌊(n:ℝ)^((1:ℝ)/3)⌋₊).filter Nat.Prime)).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)))) + (((Finset.Icc ((n+2)/3) ((2*n)/3)).card : ℝ)*(n.totient:ℝ)/n*∏ p ∈ (((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime)).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)))/16) :(let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let S := fun n z : ℕ => ((I n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card; let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Z₂ := Nat.sqrt; ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → V n (Z₁ n) - V n (Z₂ n)/8 ≤ (S n (Z₁ n):ℝ)) := by
  intro I P V S Z₁ Z₂
  obtain ⟨N₁, hN₁, h₁⟩ := h₁
  obtain ⟨N₂, hN₂, h₂⟩ := h₂
  refine ⟨max N₁ N₂, by omega, fun n hn hE => ?_⟩
  dsimp only [I, P, V, S, Z₁, Z₂]
  have ha := h₁ n (by omega) hE
  have hb := h₂ n (by omega) hE
  linarith
