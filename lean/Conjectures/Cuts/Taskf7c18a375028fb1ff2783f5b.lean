import Mathlib
import Conjectures.Goldbach.B13BilateralVaughanReduction

open Finset Polynomial
open scoped Polynomial
namespace PairEnergy

private lemma fiber_bound {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → β) (n : ℕ) (maps : ∀ a ∈ s, f a ∈ t)
    (fib : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ n) : s.card ≤ t.card*n := by
  by_contra! bad
  obtain ⟨b,hb,h⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to maps bad
  exact (fib b hb).not_gt h

private lemma root_count {α : Type*} (s : Finset α) (f : α → ℤ) (Q : ℤ[X])
    (hne : Q ≠ 0) (inj : Set.InjOn f s) (root : ∀ x ∈ s, Q.eval (f x) = 0) :
    s.card ≤ Q.natDegree := by
  classical
  apply le_trans (card_le_card_of_injOn f (t := Q.roots.toFinset) ?_ inj)
    ((Multiset.toFinset_card_le _).trans Q.card_roots')
  intro x hx
  exact Multiset.mem_toFinset.mpr ((mem_roots hne).mpr (root x hx))

private lemma shift_ne (P : ℤ[X]) (deg : 2 ≤ P.natDegree) (h d : ℤ) (hn : h ≠ 0) :
    taylor h P - P - C d ≠ 0 := by
  intro bad
  have step (x : ℤ) : P.eval (x+h) = P.eval x + d := by
    have eqn := congrArg (eval x) bad
    simp only [eval_sub, taylor_eval, eval_C, eval_zero] at eqn
    omega
  have along (n : ℕ) : P.eval (h * n) = P.eval 0 + d * n := by
    induction n with
    | zero => simp
    | succ n ih => push_cast; rw [mul_add, mul_one, step, ih]; ring
  have eqn : P.comp (C h * X) = C (P.eval 0) + C d * X := by
    apply eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
    rintro _ ⟨n,rfl⟩
    simpa [eval_comp] using along n
  have lower := congrArg natDegree eqn
  rw [natDegree_comp, natDegree_C_mul hn, natDegree_X, mul_one] at lower
  have upper : (C (P.eval 0) + C d * X).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le <;> compute_degree <;> norm_num
  omega

private lemma growth (P : ℤ[X]) {x M : ℕ} (hx : x ≤ M) (hm : 1 ≤ M) :
    (P.eval (x:ℤ)).natAbs ≤ (∑ i ∈ P.support, (P.coeff i).natAbs) * M ^ P.natDegree := by
  rw [eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply (Int.natAbs_sum_le ..).trans
  apply sum_le_sum
  intro i hi
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  gcongr
  exact le_natDegree_of_mem_supp _ hi

private def signedDiv (n : ℕ) : Finset ℤ :=
  n.divisors.image (fun a : ℕ => (a:ℤ)) ∪ n.divisors.image (fun a : ℕ => -(a:ℤ))

private lemma mem_signed {h d : ℤ} (hd : d ≠ 0) (dv : h ∣ d) : h ∈ signedDiv d.natAbs := by
  have habs := Int.natAbs_dvd_natAbs.mpr dv
  have hmem := Nat.mem_divisors.mpr ⟨habs, Int.natAbs_ne_zero.mpr hd⟩
  rcases Int.natAbs_eq h with eqn | eqn
  · exact mem_union_left _ (mem_image.mpr ⟨_,hmem,by omega⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨_,hmem,by omega⟩)

private lemma card_signed (n : ℕ) : (signedDiv n).card ≤ 2*n.divisors.card := by
  unfold signedDiv
  apply (card_union_le _ _).trans
  rw [two_mul]
  exact add_le_add card_image_le card_image_le

private lemma value_bound (P : ℤ[X]) (deg : 2 ≤ P.natDegree) (A : Finset ℕ) (y : ℤ) :
    (univ.filter (fun a : A => P.eval ((a:ℕ):ℤ) = y)).card ≤ P.natDegree := by
  let Q := P - C y
  have hn : Q ≠ 0 := by
    intro h
    have hh := congrArg natDegree (sub_eq_zero.mp h : P=C y)
    simp at hh
    omega
  apply (root_count _ (fun a : A => ((a:ℕ):ℤ)) Q hn (fun _ _ _ _ h => Subtype.ext (Int.ofNat_inj.mp h)) ?_).trans
    ((natDegree_sub_le _ _).trans (by simp))
  intro a ha
  simpa [Q] using sub_eq_zero.mpr (mem_filter.mp ha).2

private abbrev Config (A : Finset ℕ) := (Fin 2 → ↥A) × (Fin 2 → ↥A)

private lemma collision_count (P : ℤ[X]) (deg : 2 ≤ P.natDegree) (A : Finset ℕ) (D : ℕ)
    (major : ∀ x y : A, (P.eval ((x:ℕ):ℤ) - P.eval ((y:ℕ):ℤ)).natAbs.divisors.card ≤ D) :
    (univ.filter (fun z : Config A => (∑ i, P.eval ((z.1 i:ℕ):ℤ)) = ∑ i, P.eval ((z.2 i:ℕ):ℤ))).card
      ≤ A.card^2 * (P.natDegree^2 + 2*D*P.natDegree) := by
  classical
  let v (a : A) := P.eval ((a:ℕ):ℤ)
  let S := univ.filter (fun z : Config A => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))
  let E := S.filter (fun z => v (z.1 0) = v (z.2 0))
  let F := S.filter (fun z => v (z.1 0) ≠ v (z.2 0))
  have eqS {z : Config A} (hz : z ∈ S) :
      v (z.1 0) + v (z.1 1) = v (z.2 0) + v (z.2 1) := by
    simpa only [Fin.sum_univ_two] using (mem_filter.mp hz).2
  have bv (x : A) := value_bound P deg A (v x)
  have small : E.card ≤ A.card^2 * P.natDegree^2 := by
    let f (z : Config A) := z.1
    have b := fiber_bound E univ f (P.natDegree^2) (fun _ _ => mem_univ _) (by
      intro b _
      let V (x : A) := univ.filter (fun y : A => v y = v x)
      apply (card_le_card_of_injOn (fun z : Config A => (z.2 0,z.2 1)) (t := (V (b 0)) ×ˢ (V (b 1))) ?_ ?_).trans
      · rw [card_product, sq]
        exact Nat.mul_le_mul (bv _) (bv _)
      · intro z hz
        obtain ⟨hz,hb⟩ := mem_filter.mp hz
        obtain ⟨hs,he⟩ := mem_filter.mp hz
        change z.1 = b at hb
        have hh := eqS hs
        rw [hb] at hh he
        apply Finset.mem_product.mpr
        simp only [V,mem_filter,mem_univ,true_and]
        exact ⟨he.symm,by omega⟩
      · intro z hz w hw eqn
        apply Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)
        funext i
        fin_cases i
        · exact congrArg Prod.fst eqn
        · exact congrArg Prod.snd eqn)
    simpa [Fintype.card_fin] using b
  have large : F.card ≤ A.card^2 * (2*D*P.natDegree) := by
    let f (z : Config A) := (z.1 0,z.2 0)
    have b := fiber_bound F univ f (2*D*P.natDegree) (fun _ _ => mem_univ _) (by
      intro b _
      let d := v b.1 - v b.2
      let T := F.filter (fun z => f z = b)
      let gap (z : Config A) : ℤ := (z.2 1 : ℕ) - ((z.1 1 : ℕ):ℤ)
      have data {z : Config A} (hz : z ∈ T) : f z = b ∧ d ≠ 0 ∧ v (z.2 1) - v (z.1 1) = d := by
        obtain ⟨hz,hb⟩ := mem_filter.mp hz
        obtain ⟨hs,hn⟩ := mem_filter.mp hz
        have hh := eqS hs
        have h1 : z.1 0 = b.1 := congrArg Prod.fst hb
        have h2 : z.2 0 = b.2 := congrArg Prod.snd hb
        dsimp [d]; rw [← h1, ← h2]
        exact ⟨hb,sub_ne_zero.mpr hn,by omega⟩
      apply (fiber_bound T (signedDiv d.natAbs) gap P.natDegree ?_ ?_).trans
      · exact Nat.mul_le_mul_right _ ((card_signed _).trans (Nat.mul_le_mul_left 2 (major b.1 b.2)))
      · intro z hz
        obtain ⟨_,hd,he⟩ := data hz
        exact mem_signed hd (he ▸ sub_dvd_eval_sub ((z.2 1:ℕ):ℤ) ((z.1 1:ℕ):ℤ) P)
      · intro h _
        by_cases h0 : h = 0
        · subst h
          have empty : (T.filter (fun z => gap z = 0)) = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro z hz
            obtain ⟨hz,hz0⟩ := mem_filter.mp hz
            obtain ⟨_,hd,he⟩ := data hz
            have zz : z.2 1 = z.1 1 := Subtype.ext (Int.ofNat_inj.mp (sub_eq_zero.mp hz0))
            rw [zz,sub_self] at he
            exact hd he.symm
          simp [empty]
        let Q := taylor h P - P - C d
        apply (root_count _ (fun z : Config A => ((z.1 1 : ℕ):ℤ)) Q (shift_ne P deg h d h0) ?_ ?_).trans
        · apply (natDegree_sub_le _ _).trans
          apply max_le _ (by simp)
          exact (natDegree_sub_le _ _).trans (by simp)
        · intro z hz w hw eqn
          obtain ⟨hz,hz1⟩ := mem_filter.mp hz
          obtain ⟨hw,hw1⟩ := mem_filter.mp hw
          have hb := (data hz).1.trans (data hw).1.symm
          have h01 : z.1 1 = w.1 1 := Subtype.ext (Int.ofNat_inj.mp eqn)
          have h11 : z.2 1 = w.2 1 := by
            apply Subtype.ext; apply Int.ofNat_inj.mp
            change ((z.2 1:ℕ):ℤ) - ((z.1 1:ℕ):ℤ) = h at hz1
            change ((w.2 1:ℕ):ℤ) - ((w.1 1:ℕ):ℤ) = h at hw1
            rw [h01] at hz1
            exact sub_left_inj.mp (hz1.trans hw1.symm)
          apply Prod.ext <;> funext i <;> fin_cases i
          · exact congrArg Prod.fst hb
          · exact h01
          · exact congrArg Prod.snd hb
          · exact h11
        · intro z hz
          obtain ⟨hz,hh⟩ := mem_filter.mp hz
          have hh' : ((z.1 1 : ℕ):ℤ) + h = (z.2 1 : ℕ) := by dsimp [gap] at hh; omega
          simp only [Q, eval_sub, taylor_eval, hh',eval_C]
          exact sub_eq_zero.mpr (data hz).2.2)
    simpa [sq] using b
  change S.card ≤ _
  have part : E.card + F.card = S.card := card_filter_add_card_filter_not ..
  rw [← part, mul_add]
  exact Nat.add_le_add small large

private lemma energy (P : ℤ[X]) (deg : 2 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
    ((univ.filter (fun z : Config A => (∑ i, P.eval ((z.1 i:ℕ):ℤ)) = ∑ i, P.eval ((z.2 i:ℕ):ℤ))).card : ℝ)
      ≤ K * (M:ℝ)^ε * (A.card:ℝ)^2 := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt ((P.natDegree:ℝ)/ε)
  have kp : 0 < (k:ℝ) := (div_nonneg (Nat.cast_nonneg _) hε.le).trans_lt hk
  obtain ⟨c,hc,divs⟩ := B13BilateralVaughanReductionProof.DyadicMixedB4DivisorGrowth.divisorPower k (by exact_mod_cast kp)
  let W := ∑ i ∈ P.support, (P.coeff i).natAbs
  let L : ℝ := (1+c*(2*(W:ℝ)))^(1/(k:ℝ))
  have hc0 : 0 ≤ c := by linarith
  have hbase : 0 < 1+c*(2*(W:ℝ)) := by positivity
  have hL : 0 < L := Real.rpow_pos_of_pos hbase _
  let r : ℝ := P.natDegree
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (show 0 < P.natDegree by omega)
  refine ⟨r^2 + 2*L*r, by positivity, ?_⟩
  intro M hM A hA
  have m1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have V1 := Real.one_le_rpow m1 hε.le
  let D := ⌊L*(M:ℝ)^ε⌋₊
  have bound (x y : A) : (P.eval ((x:ℕ):ℤ) - P.eval ((y:ℕ):ℤ)).natAbs.divisors.card ≤ D := by
    let n := (P.eval ((x:ℕ):ℤ) - P.eval ((y:ℕ):ℤ)).natAbs
    change n.divisors.card ≤ D
    apply Nat.le_floor
    by_cases hn : n = 0
    · simp [hn]
      positivity
    have upper : n ≤ 2 * W * M^P.natDegree := by
      have sub := Int.natAbs_sub_le (P.eval ((x:ℕ):ℤ)) (P.eval ((y:ℕ):ℤ))
      have gx := growth P (mem_Icc.mp (hA x.property)).2 (show 1≤M by omega)
      have gy := growth P (mem_Icc.mp (hA y.property)).2 (show 1≤M by omega)
      change _ ≤ W*_ at gx gy
      dsimp [n]; rw [two_mul, add_mul]
      exact sub.trans (add_le_add gx gy)
    have nr : (n:ℝ) ≤ 2*(W:ℝ)*(M:ℝ)^P.natDegree := by exact_mod_cast upper
    have full := (divs n (Nat.pos_of_ne_zero hn)).trans (mul_le_mul_of_nonneg_left nr hc0)
    have full' : (n.divisors.card:ℝ)^k ≤ (1+c*(2*(W:ℝ)))*(M:ℝ)^P.natDegree := by
      nlinarith [show 0 ≤ (M:ℝ)^P.natDegree by positivity]
    have power := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) k) full' (by positivity : 0 ≤ 1/(k:ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      show (k:ℝ)*(1/(k:ℝ))=1 by field_simp, Real.rpow_one,
      Real.mul_rpow hbase.le (by positivity), ← Real.rpow_natCast (M:ℝ),
      ← Real.rpow_mul (Nat.cast_nonneg _)] at power
    apply power.trans
    apply mul_le_mul_of_nonneg_left _ hL.le
    apply Real.rpow_le_rpow_of_exponent_le m1
    rw [← div_eq_mul_one_div,div_le_iff₀ kp]
    linarith [(div_lt_iff₀ hε).mp hk]
  have counted := collision_count P deg A D bound
  have realCount := Nat.cast_le (α := ℝ) |>.mpr counted
  push_cast at realCount
  apply realCount.trans
  have hd : (D:ℝ) ≤ L*(M:ℝ)^ε := Nat.floor_le (by positivity)
  change _ ≤ (r^2+2*L*r)*(M:ℝ)^ε*(A.card:ℝ)^2
  change (A.card:ℝ)^2 * (r^2+2*(D:ℝ)*r) ≤ _
  rw [mul_comm ((A.card:ℝ)^2)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hd hr.le, mul_le_mul_of_nonneg_left V1 (sq_nonneg r)]

end PairEnergy

theorem Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b : (∀ (x1 : Polynomial ℤ),   (2 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (2 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (2 : ℕ) → ↥x8) => ∑ x11 : Fin (2 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : Finset ((Fin (2 : ℕ) → ↥x8) × (Fin (2 : ℕ) → ↥x8)) := Finset.univ;                   ↑{x12 ∈ x11 | x10 x12.1 = x10 x12.2}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (2 : ℕ)) := by
  exact PairEnergy.energy
