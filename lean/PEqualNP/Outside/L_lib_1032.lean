import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1032_aux

open Classical

/-- Triangle inequality: any signing of a nonnegative matrix has |det| <= permanent. -/
private lemma abs_det_signed_le_permanent {α : Type*} [Fintype α] [DecidableEq α]
    (s : α × α → Bool) (A : Matrix α α ℝ) (hnn : ∀ i j, 0 ≤ A i j) :
    |(Matrix.det (fun i j => if s (i, j) then -A i j else A i j : Matrix α α ℝ))| ≤
      A.permanent := by
  let B : Matrix α α ℝ := fun i j => if s (i, j) then -A i j else A i j
  change |B.det| ≤ A.permanent
  rw [Matrix.det_apply, Matrix.permanent]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun σ _ => ?_
  change |(Equiv.Perm.sign σ : ℤ) • (∏ i : α, B (σ i) i)| ≤ ∏ i : α, A (σ i) i
  rw [zsmul_eq_mul, abs_mul]
  have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [hsign, one_mul, Finset.abs_prod]
  refine le_of_eq (Finset.prod_congr rfl fun i _ => ?_)
  dsimp only [B]
  split_ifs
  · rw [abs_neg, abs_of_nonneg (hnn (σ i) i)]
  · rw [abs_of_nonneg (hnn (σ i) i)]

/-- For a permutation τ of Fin b × Fin 2 preserving first coordinates,
    its sign equals the product of per-block flip signs. -/
private lemma sign_block_perm {b : ℕ} (τ : Equiv.Perm (Fin b × Fin 2))
    (hpres : ∀ p : Fin b × Fin 2, (τ p).1 = p.1) :
    ((Equiv.Perm.sign τ : ℤ) : ℝ) =
      ∏ r : Fin b, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1 := by
  -- Express τ as a product of disjoint swaps on the blocks where τ (r, 0) = (r, 1)
  let S : Finset (Fin b) := Finset.univ.filter (fun r => τ (r, 0) = (r, 1))
  let sw : Fin b → Equiv.Perm (Fin b × Fin 2) := fun r => Equiv.swap (r, (0 : Fin 2)) (r, (1 : Fin 2))
  have hsw_apply : ∀ (r : Fin b) (p : Fin b × Fin 2),
      sw r p = if p.1 = r then (r, 1 - p.2) else p := by
    intro r p
    rcases p with ⟨r', c⟩
    dsimp only [sw]
    by_cases hr : r' = r
    · subst hr
      fin_cases c
      · simp [Equiv.swap_apply_left]
      · simp [Equiv.swap_apply_right]
    · rw [if_neg hr, Equiv.swap_apply_of_ne_of_ne]
      · intro h; exact hr (congrArg Prod.fst h)
      · intro h; exact hr (congrArg Prod.fst h)
  have hcomm : ∀ (r1 r2 : Fin b), Commute (sw r1) (sw r2) := by
    intro r1 r2
    show sw r1 * sw r2 = sw r2 * sw r1
    apply Equiv.ext; intro p
    simp only [Equiv.Perm.mul_apply, hsw_apply]
    by_cases h1 : p.1 = r1 <;> by_cases h2 : p.1 = r2
    · have heq : r1 = r2 := h1.symm.trans h2
      subst heq; simp [h1]
    · have hne : r1 ≠ r2 := fun h => h2 (h1.trans h)
      simp [h1, hne]
    · have hne : r2 ≠ r1 := fun h => h1 (h2.trans h)
      simp [h2, hne]
    · simp [h1, h2]
  have hpair : ∀ T : Finset (Fin b), (T : Set (Fin b)).Pairwise (Function.onFun Commute sw) :=
    fun _ a _ c _ _ => hcomm a c
  have hprod_eval : ∀ (T : Finset (Fin b)) (p : Fin b × Fin 2),
      (T.noncommProd sw (hpair T)) p =
        if p.1 ∈ T then (p.1, 1 - p.2) else p := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro p; rw [Finset.noncommProd_empty]; simp
    | insert a s ha ih =>
      intro p
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
      rw [Equiv.Perm.mul_apply, ih p, hsw_apply]
      by_cases hpa : p.1 = a
      · simp [hpa, ha]
      · by_cases hps : p.1 ∈ s
        · simp [hpa, hps]
        · simp [hpa, hps]
  have hτ_eq : τ = S.noncommProd sw (hpair S) := by
    apply Equiv.ext
    intro p
    rcases p with ⟨r, c⟩
    rw [hprod_eval S (r, c)]
    have h01 : τ (r, 0) = (r, 0) ∨ τ (r, 0) = (r, 1) := by
      have hf := hpres (r, 0)
      rcases h : τ (r, 0) with ⟨r', c'⟩
      rw [h] at hf; dsimp only at hf; subst hf
      fin_cases c'
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h10 : τ (r, 1) = (r, 0) ∨ τ (r, 1) = (r, 1) := by
      have hf := hpres (r, 1)
      rcases h : τ (r, 1) with ⟨r', c'⟩
      rw [h] at hf; dsimp only at hf; subst hf
      fin_cases c'
      · exact Or.inl rfl
      · exact Or.inr rfl
    by_cases hrS : r ∈ S
    · have hτ0 : τ (r, 0) = (r, 1) := (Finset.mem_filter.mp hrS).2
      have hτ1 : τ (r, 1) = (r, 0) := by
        rcases h10 with h | h
        · exact h
        · exfalso
          have hinj := τ.injective (h.trans hτ0.symm)
          simp at hinj
      rw [if_pos hrS]
      fin_cases c
      · exact hτ0
      · exact hτ1
    · have hτ0 : τ (r, 0) = (r, 0) := by
        rcases h01 with h | h
        · exact h
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩) hrS
      have hτ1 : τ (r, 1) = (r, 1) := by
        rcases h10 with h | h
        · exfalso
          have hinj := τ.injective (h.trans hτ0.symm)
          simp at hinj
        · exact h
      rw [if_neg hrS]
      fin_cases c
      · exact hτ0
      · exact hτ1
  have hsign_prod : ∀ (T : Finset (Fin b)),
      ((Equiv.Perm.sign (T.noncommProd sw (hpair T)) : ℤ) : ℝ) =
        (-1 : ℝ) ^ T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [Finset.noncommProd_empty]; simp
    | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, map_mul, Units.val_mul, Int.cast_mul, ih]
      have hne : ((a, (0 : Fin 2)) : Fin b × Fin 2) ≠ (a, (1 : Fin 2)) := by simp
      have hsw_sgn : ((Equiv.Perm.sign (sw a) : ℤ) : ℝ) = -1 := by
        dsimp only [sw]
        rw [Equiv.Perm.sign_swap hne]
        norm_num
      rw [hsw_sgn, Finset.card_insert_of_notMem ha, pow_succ']
  have hrhs : (∏ r : Fin b, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) = (-1 : ℝ) ^ S.card := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r : Fin b => τ (r, 0) = (r, 1))]
    have h1 : ∏ r ∈ Finset.univ.filter (fun r : Fin b => τ (r, 0) = (r, 1)),
        (if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) = (-1 : ℝ) ^ S.card := by
      have hc : ∏ r ∈ S, (if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) = ∏ _r ∈ S, (-1 : ℝ) := by
        refine Finset.prod_congr rfl fun r hr => if_pos (Finset.mem_filter.mp hr).2
      simpa only [S, Finset.prod_const] using hc
    have h2 : ∏ r ∈ Finset.univ.filter (fun r : Fin b => ¬ τ (r, 0) = (r, 1)),
        (if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) = 1 :=
      Finset.prod_eq_one fun r hr => if_neg (Finset.mem_filter.mp hr).2
    rw [h1, h2, mul_one]
  rw [hrhs]
  conv_lhs => rw [hτ_eq, hsign_prod S]

/-- Crossing cut U attains |D s_U A| = A.permanent on block-supported nonnegative A. -/
private lemma abs_det_crossing_eq_permanent {b : ℕ}
    (π : Equiv.Perm (Fin b × Fin 2)) (A : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℝ)
    (hnn : ∀ i j, 0 ≤ A i j)
    (hsupp : ∀ i j, i.1 ≠ (π j).1 → A i j = 0)
    (U : Finset (Fin b × Fin 2))
    (hcross : ∀ r : Fin b, (π.symm (r, 0) ∈ U) ≠ (π.symm (r, 1) ∈ U)) :
    |(Matrix.det (fun i j =>
      if decide (i.2.val = 1 ∧ j ∈ U) then -A i j else A i j :
        Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℝ))| = A.permanent := by
  let I := Fin b × Fin 2
  let sU : I × I → Bool := fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U)
  let B : Matrix I I ℝ := fun i j => if sU (i, j) then -A i j else A i j
  let ε : ℝ := ((Equiv.Perm.sign π : ℤ) : ℝ) *
    ∏ r : Fin b, if π.symm (r, 1) ∈ U then (-1 : ℝ) else 1
  have hε_abs : |ε| = 1 := by
    dsimp only [ε]
    rw [abs_mul, Finset.abs_prod]
    have hs : |((Equiv.Perm.sign π : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1 <;> simp [h1]
    have hp : ∏ r : Fin b, |(if π.symm (r, 1) ∈ U then (-1 : ℝ) else 1)| = 1 :=
      Finset.prod_eq_one fun r _ => by split_ifs <;> norm_num
    rw [hs, hp, mul_one]
  have hdet_eq : B.det = ε * A.permanent := by
    rw [Matrix.det_apply, Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hpres : ∀ j : I, (σ j).1 = (π j).1
    · let τ : Equiv.Perm I := σ * π.symm
      have hτ_pres : ∀ p : I, (τ p).1 = p.1 := by
        intro p
        dsimp only [τ]
        rw [Equiv.Perm.mul_apply, hpres (π.symm p), Equiv.apply_symm_apply]
      have hσ_eq : σ = τ * π := by
        apply Equiv.ext; intro p; simp [τ]
      have hsign_σ : ((Equiv.Perm.sign σ : ℤ) : ℝ) =
          ((Equiv.Perm.sign π : ℤ) : ℝ) *
          ∏ r : Fin b, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1 := by
        rw [hσ_eq, map_mul, Units.val_mul, Int.cast_mul, sign_block_perm τ hτ_pres, mul_comm]
      have hprod_B : (∏ j : I, B (σ j) j) =
          (∏ j : I, if sU (σ j, j) then (-1 : ℝ) else 1) * (∏ j : I, A (σ j) j) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        dsimp only [B]
        split_ifs <;> ring
      have hprod_sU : (∏ j : I, if sU (σ j, j) then (-1 : ℝ) else 1) =
          (∏ r : Fin b, if π.symm (r, 1) ∈ U then (-1 : ℝ) else 1) *
          (∏ r : Fin b, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) := by
        have hreidx : (∏ j : I, if sU (σ j, j) then (-1 : ℝ) else 1) =
            ∏ p : I, if sU (τ p, π.symm p) then (-1 : ℝ) else 1 := by
          refine Fintype.prod_equiv π _ _ fun j => ?_
          have h1 : σ j = τ (π j) := by rw [hσ_eq]; rfl
          rw [h1, Equiv.symm_apply_apply]
        rw [hreidx]
        rw [Fintype.prod_prod_type]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun r _ => ?_
        rw [Fin.prod_univ_two]
        have h01 : τ (r, 0) = (r, 0) ∨ τ (r, 0) = (r, 1) := by
          have hf := hτ_pres (r, 0)
          rcases h : τ (r, 0) with ⟨r', c'⟩
          rw [h] at hf; dsimp only at hf; subst hf
          fin_cases c'
          · exact Or.inl rfl
          · exact Or.inr rfl
        have h10 : τ (r, 1) = (r, 0) ∨ τ (r, 1) = (r, 1) := by
          have hf := hτ_pres (r, 1)
          rcases h : τ (r, 1) with ⟨r', c'⟩
          rw [h] at hf; dsimp only at hf; subst hf
          fin_cases c'
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hcr := hcross r
        rcases h01 with h0 | h0
        · have h1 : τ (r, 1) = (r, 1) := by
            rcases h10 with h | h
            · exfalso
              have h01' : (1 : Fin 2) = 0 := congrArg Prod.snd (τ.injective (h.trans h0.symm))
              exact absurd h01' (by decide)
            · exact h
          rw [h0, h1]
          have hne : (r, (0 : Fin 2)) ≠ (r, (1 : Fin 2)) := by simp
          rw [if_neg hne, mul_one]
          by_cases hU1 : π.symm (r, 1) ∈ U <;> simp [sU, hU1]
        · have h1 : τ (r, 1) = (r, 0) := by
            rcases h10 with h | h
            · exact h
            · exfalso
              have h01' : (1 : Fin 2) = 0 := congrArg Prod.snd (τ.injective (h.trans h0.symm))
              exact absurd h01' (by decide)
          rw [h0, h1, if_pos rfl]
          by_cases hU0 : π.symm (r, 0) ∈ U <;> by_cases hU1 : π.symm (r, 1) ∈ U
          · exact absurd (propext (iff_of_true hU0 hU1)) hcr
          · simp [sU, hU0, hU1]
          · simp [sU, hU0, hU1]
          · exact absurd (propext (iff_of_false hU0 hU1)) hcr
      change (Equiv.Perm.sign σ : ℤ) • (∏ j : I, B (σ j) j) = ε * ∏ j : I, A (σ j) j
      rw [zsmul_eq_mul, hsign_σ, hprod_B, hprod_sU]
      have hsq : (∏ r : Fin b, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) *
          (∏ r : Fin b, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) = 1 := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun r _ => by split_ifs <;> norm_num
      dsimp only [ε]
      calc (((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ r, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) *
              (((∏ r, if π.symm (r, 1) ∈ U then (-1 : ℝ) else 1) *
                ∏ r, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) * ∏ j, A (σ j) j)
          = (((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ r, if π.symm (r, 1) ∈ U then (-1 : ℝ) else 1) *
              ((∏ r, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1) *
                (∏ r, if τ (r, 0) = (r, 1) then (-1 : ℝ) else 1)) * ∏ j, A (σ j) j := by ring
        _ = (((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ r, if π.symm (r, 1) ∈ U then (-1 : ℝ) else 1) *
              ∏ j, A (σ j) j := by rw [hsq, mul_one]
    · push_neg at hpres
      rcases hpres with ⟨j0, hj0⟩
      have hA0 : A (σ j0) j0 = 0 := hsupp (σ j0) j0 hj0
      have hB0 : B (σ j0) j0 = 0 := by dsimp only [B]; rw [hA0]; split_ifs <;> simp
      have hprodA0 : ∏ j : I, A (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) hA0
      have hprodB0 : ∏ j : I, B (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) hB0
      rw [hprodA0, hprodB0, smul_zero, mul_zero]
  have hperm_nn : 0 ≤ A.permanent := by
    rw [Matrix.permanent]
    exact Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun j _ => hnn (σ j) j
  change |B.det| = A.permanent
  rw [hdet_eq, abs_mul, hε_abs, one_mul, abs_of_nonneg hperm_nn]

/-- Binary reconstruction from m low bits for any natural x < 2^m. -/
private lemma sum_testBit_pow_two :
    ∀ (m x : ℕ), x < 2 ^ m →
      ∑ bit : Fin m, (if x.testBit bit.val then 2 ^ bit.val else 0) = x := by
  intro m
  induction m with
  | zero =>
    intro x hx; simp at hx ⊢; omega
  | succ k ih =>
    intro x hx
    rw [Fin.sum_univ_succ]
    have hdiv : x / 2 < 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
      omega
    have htail : ∑ bit : Fin k, (if x.testBit bit.succ.val then 2 ^ bit.succ.val else 0) =
        2 * ∑ bit : Fin k, (if (x / 2).testBit bit.val then 2 ^ bit.val else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun bit _ => ?_
      have htb : x.testBit (bit.val + 1) = (x / 2).testBit bit.val := by
        rw [Nat.testBit_succ]
      change (if x.testBit (bit.val + 1) then 2 ^ (bit.val + 1) else 0) = _
      rw [htb, pow_succ]
      split_ifs <;> ring
    rw [htail, ih (x / 2) hdiv]
    have h0 : x.testBit 0 = decide (x % 2 = 1) := Nat.testBit_zero x
    change (if x.testBit 0 then 2 ^ 0 else 0) + 2 * (x / 2) = x
    rw [h0]
    cases Nat.mod_two_eq_zero_or_one x with
    | inl h => simp [h]; omega
    | inr h => simp [h]; omega

/-- Negating a single column j of a matrix negates its determinant. -/
private lemma det_neg_col {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℝ) (j : α) :
    (Matrix.of (fun i k => if k = j then -M i k else M i k)).det = -M.det := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hprod : (∏ k : α, (if k = j then -M (σ k) k else M (σ k) k)) =
      -(∏ k : α, M (σ k) k) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    rw [if_pos rfl, neg_mul]
    congr 2
    refine Finset.prod_congr rfl fun k hk => if_neg (Finset.ne_of_mem_erase hk)
  change (Equiv.Perm.sign σ) • (∏ k : α, if k = j then -M (σ k) k else M (σ k) k) =
    -((Equiv.Perm.sign σ) • ∏ i : α, M (σ i) i)
  rw [hprod, smul_neg]

theorem main_proof :
    ∀ b m : ℕ, 0 < b → b ≤ 2^m →
      let I := Fin b × Fin 2
      let S := I × I → Bool
      let D := fun (s : S) (A : Matrix I I ℝ) =>
        Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix I I ℝ)
      ∃ (R t : ℕ) (first : Fin R → Fin t → S)
        (second : Fin R → (Fin t → ℝ) → I × Fin m → S)
        (read : Fin R → (Fin t → ℝ) → (I × Fin m → ℝ) → Option ((I → Fin b) × ℝ)),
        0 < R ∧ 0 < t ∧ t*2^b ≤ 2*Nat.choose (2*b) b + 2^b ∧
        let run := fun (u : Fin R) (A : Matrix I I ℝ) =>
          let y := fun h : Fin t => D (first u h) A
          read u y (fun p : I × Fin m => D (second u y p) A)
        (∀ u, run u 0 = none) ∧
        ∀ (π : Equiv.Perm I) (A : Matrix I I ℝ),
          (∀ i j, 0 ≤ A i j) → (∀ i j, i.1 ≠ (π j).1 → A i j = 0) → 0 < A.permanent →
          2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter (fun u =>
            run u A = some ((fun j : I => (π j).1), A.permanent))).card := by
  intro b m hb hbm
  dsimp only
  let I := Fin b × Fin 2
  let S := I × I → Bool
  let D := fun (s : S) (A : Matrix I I ℝ) =>
    Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix I I ℝ)
  let C : ℕ := Nat.choose (2 * b) b
  have hC_pos : 0 < C := Nat.choose_pos (by omega)
  let t : ℕ := 2 * C / 2 ^ b + 1
  have ht_pos : 0 < t := Nat.succ_pos _
  have ht_ub : t * 2 ^ b ≤ 2 * C + 2 ^ b := by
    dsimp only [t]
    rw [Nat.add_mul, one_mul]
    have hle := Nat.div_mul_le_self (2 * C) (2 ^ b)
    omega
  have ht_lb : 2 * C ≤ t * 2 ^ b := by
    dsimp only [t]
    have hpos2 : 0 < 2 ^ b := pow_pos (by norm_num) b
    have hdiv := Nat.div_add_mod (2 * C) (2 ^ b)
    rw [mul_comm (2 ^ b)] at hdiv
    have hmod := Nat.mod_lt (2 * C) hpos2
    rw [Nat.add_mul, one_mul]
    omega
  let Uall : Finset (Finset I) := Finset.powersetCard b (Finset.univ : Finset I)
  have hUall_card : Uall.card = C := by
    dsimp only [Uall, C]
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, mul_comm]
  let R : ℕ := C ^ t
  have hR_pos : 0 < R := pow_pos hC_pos t
  have hcard_fn : Fintype.card (Fin t → Uall) = R := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_coe, hUall_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin, R]
  let eR : Fin R ≃ (Fin t → Uall) := (Fintype.equivFinOfCardEq hcard_fn).symm
  let first : Fin R → Fin t → S := fun u h z =>
    decide (z.1.2.val = 1 ∧ z.2 ∈ (eR u h).val)
  have hne_t : (Finset.univ : Finset (Fin t)).Nonempty :=
    ⟨⟨0, ht_pos⟩, Finset.mem_univ _⟩
  let bestH : (Fin t → ℝ) → Fin t := fun y =>
    Classical.choose (Finset.exists_max_image (Finset.univ : Finset (Fin t)) (fun h => |y h|) hne_t)
  have hbestH_max : ∀ (y : Fin t → ℝ) (h : Fin t), |y h| ≤ |y (bestH y)| := by
    intro y h
    exact (Classical.choose_spec (Finset.exists_max_image Finset.univ (fun h => |y h|) hne_t)).2 h (Finset.mem_univ h)
  let second : Fin R → (Fin t → ℝ) → I × Fin m → S := fun u y p z =>
    if z.2 = p.1 ∧ z.1.1.val.testBit p.2.val then !(first u (bestH y) z) else first u (bestH y) z
  let read : Fin R → (Fin t → ℝ) → (I × Fin m → ℝ) → Option ((I → Fin b) × ℝ) := fun _ y z =>
    let v := y (bestH y)
    if v = 0 then none
    else
      let labelVal : I → ℕ := fun j =>
        ∑ bit : Fin m, if z (j, bit) = -v then 2 ^ bit.val else 0
      if hlt : ∀ j : I, labelVal j < b then
        some (fun j => ⟨labelVal j, hlt j⟩, |v|)
      else none
  refine ⟨R, t, first, second, read, hR_pos, ht_pos, ht_ub, ?_, ?_⟩
  -- Zero matrix gives none
  · intro u
    have : Nonempty I := ⟨(⟨0, hb⟩, 0)⟩
    have hy0 : ∀ h : Fin t, D (first u h) 0 = 0 := by
      intro h
      dsimp only [D]
      have hz : (fun i j : I => if first u h (i, j) then -(0 : Matrix I I ℝ) i j else (0 : Matrix I I ℝ) i j : Matrix I I ℝ) =
          (0 : Matrix I I ℝ) := by
        ext i j; simp
      rw [hz]
      exact Matrix.det_zero
    change read u (fun h : Fin t => D (first u h) 0) (fun p => D (second u (fun h => D (first u h) 0) p) 0) = none
    dsimp only [read]
    simp only [hy0, ↓reduceIte]
  -- High-probability exact recovery on block-supported nonnegative A with 0 < A.permanent
  · intro π A hnn hsupp hperm_pos
    let GoodU : Finset (Finset I) :=
      Uall.filter (fun U => ∀ r : Fin b, (π.symm (r, 0) ∈ U) ≠ (π.symm (r, 1) ∈ U))
    have hGoodU_card : GoodU.card = 2 ^ b := by
      have hbij : GoodU.card = Fintype.card (Fin b → Bool) := by
        symm
        refine Finset.card_bij
          (fun (f : Fin b → Bool) _ =>
            Finset.univ.image (fun r : Fin b => π.symm (r, if f r then (1 : Fin 2) else 0)))
          ?_ ?_ ?_
        · intro f _
          simp only [GoodU, Uall, Finset.mem_filter, Finset.mem_powersetCard]
          have hinj_f : Function.Injective (fun r : Fin b => π.symm (r, if f r then (1 : Fin 2) else 0)) := by
            intro r1 r2 heq
            have h1 := π.symm.injective heq
            exact congrArg Prod.fst h1
          refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
          · rw [Finset.card_image_of_injective _ hinj_f, Finset.card_univ, Fintype.card_fin]
          · intro r
            have hmem0 : π.symm (r, 0) ∈ Finset.univ.image (fun r' : Fin b => π.symm (r', if f r' then (1 : Fin 2) else 0)) ↔
                f r = false := by
              simp only [Finset.mem_image, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨r', hr'⟩
                have h1 := π.symm.injective hr'
                have hr_eq : r' = r := congrArg Prod.fst h1
                subst hr_eq
                have hc := congrArg Prod.snd h1
                cases hfr : f r' <;> simp [hfr] at hc ⊢
              · intro hfr; exact ⟨r, by simp [hfr]⟩
            have hmem1 : π.symm (r, 1) ∈ Finset.univ.image (fun r' : Fin b => π.symm (r', if f r' then (1 : Fin 2) else 0)) ↔
                f r = true := by
              simp only [Finset.mem_image, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨r', hr'⟩
                have h1 := π.symm.injective hr'
                have hr_eq : r' = r := congrArg Prod.fst h1
                subst hr_eq
                have hc := congrArg Prod.snd h1
                cases hfr : f r' <;> simp [hfr] at hc ⊢
              · intro hfr; exact ⟨r, by simp [hfr]⟩
            rw [hmem0, hmem1]
            cases f r <;> simp
        · intro f1 _ f2 _ heq
          ext r
          have hmem : π.symm (r, if f1 r then (1 : Fin 2) else 0) ∈
              Finset.univ.image (fun r' : Fin b => π.symm (r', if f2 r' then (1 : Fin 2) else 0)) := by
            rw [← heq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ r)
          rcases Finset.mem_image.mp hmem with ⟨r', _, hr'⟩
          have h1 := π.symm.injective hr'
          have hr_eq : r' = r := congrArg Prod.fst h1
          subst hr_eq
          have hc := congrArg Prod.snd h1
          cases hf1 : f1 r' <;> cases hf2 : f2 r' <;> simp [hf1, hf2] at hc ⊢
        · intro U hU
          simp only [GoodU, Uall, Finset.mem_filter, Finset.mem_powersetCard] at hU
          let f : Fin b → Bool := fun r => decide (π.symm (r, 1) ∈ U)
          refine ⟨f, Finset.mem_univ f, ?_⟩
          ext x
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨r, rfl⟩
            dsimp only [f]
            by_cases h1 : π.symm (r, 1) ∈ U
            · simp [h1]
            · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
              have hcr := hU.2 r
              by_contra h0
              exact hcr (propext (iff_of_false h0 h1))
          · intro hxU
            rcases hpx : π x with ⟨r, c⟩
            have hx_eq : x = π.symm (r, c) := by rw [← hpx, Equiv.symm_apply_apply]
            refine ⟨r, ?_⟩
            rw [hx_eq] at hxU ⊢
            dsimp only [f]
            fin_cases c
            · change π.symm (r, 0) ∈ U at hxU
              have h1 : π.symm (r, 1) ∉ U := fun h1 => hU.2 r (propext (iff_of_true hxU h1))
              simp [h1]
            · change π.symm (r, 1) ∈ U at hxU
              simp [hxU]
      rw [hbij]
      simp
    -- If u has at least one crossing cut, run u A recovers (fun j => (π j).1, A.permanent)
    let GoodSeed : Finset (Fin R) :=
      Finset.univ.filter (fun u => ∃ h : Fin t, (eR u h).val ∈ GoodU)
    have hgood_ok : ∀ u ∈ GoodSeed,
        let y := fun h : Fin t => D (first u h) A
        read u y (fun p : I × Fin m => D (second u y p) A) =
          some ((fun j : I => (π j).1), A.permanent) := by
      intro u hu
      rcases (Finset.mem_filter.mp hu).2 with ⟨h0, hh0⟩
      have hcross0 := (Finset.mem_filter.mp hh0).2
      dsimp only
      let y : Fin t → ℝ := fun h => D (first u h) A
      have hy_le : ∀ h : Fin t, |y h| ≤ A.permanent :=
        fun h => abs_det_signed_le_permanent (first u h) A hnn
      have hy0_eq : |y h0| = A.permanent :=
        abs_det_crossing_eq_permanent π A hnn hsupp (eR u h0).val hcross0
      have hv_abs : |y (bestH y)| = A.permanent :=
        le_antisymm (hy_le (bestH y)) (hy0_eq ▸ hbestH_max y h0)
      have hv_ne : y (bestH y) ≠ 0 := by
        intro hzero; rw [hzero, abs_zero] at hv_abs; linarith
      have hsec_eq : ∀ (j : I) (bit : Fin m),
          D (second u y (j, bit)) A =
            if (π j).1.val.testBit bit.val then -(y (bestH y)) else y (bestH y) := by
        intro j bit
        let Mbase : Matrix I I ℝ := fun i k => if first u (bestH y) (i, k) then -A i k else A i k
        have hMbase_det : Mbase.det = y (bestH y) := rfl
        by_cases htb : (π j).1.val.testBit bit.val = true
        · rw [if_pos htb]
          dsimp only [D]
          have hmat_eq : (fun i k => if second u y (j, bit) (i, k) then -A i k else A i k : Matrix I I ℝ) =
              Matrix.of (fun i k => if k = j then -Mbase i k else Mbase i k) := by
            ext i k
            dsimp only [Mbase, Matrix.of_apply]
            by_cases hkj : k = j
            · subst hkj
              by_cases hik : i.1 = (π k).1
              · have hsec : second u y (k, bit) (i, k) = !(first u (bestH y) (i, k)) := by
                  dsimp only [second]; rw [if_pos ⟨rfl, hik ▸ htb⟩]
                rw [hsec, if_pos rfl]
                cases first u (bestH y) (i, k) <;> simp
              · have hA0 : A i k = 0 := hsupp i k hik
                simp [hA0]
            · have hsec : second u y (j, bit) (i, k) = first u (bestH y) (i, k) := by
                dsimp only [second]; rw [if_neg (fun h => hkj h.1)]
              rw [hsec, if_neg hkj]
          rw [hmat_eq, det_neg_col Mbase j, hMbase_det]
        · rw [if_neg htb]
          dsimp only [D]
          have hmat_eq : (fun i k => if second u y (j, bit) (i, k) then -A i k else A i k : Matrix I I ℝ) =
              Mbase := by
            ext i k
            dsimp only [Mbase]
            by_cases hkj : k = j
            · subst hkj
              by_cases hik : i.1 = (π k).1
              · have hsec : second u y (k, bit) (i, k) = first u (bestH y) (i, k) := by
                  dsimp only [second]; rw [if_neg (fun h => htb (hik ▸ h.2))]
                rw [hsec]
              · have hA0 : A i k = 0 := hsupp i k hik
                simp [hA0]
            · have hsec : second u y (j, bit) (i, k) = first u (bestH y) (i, k) := by
                dsimp only [second]; rw [if_neg (fun h => hkj h.1)]
              rw [hsec]
          rw [hmat_eq, hMbase_det]
      dsimp only [read]
      rw [if_neg hv_ne]
      have hlabel : ∀ j : I,
          (∑ bit : Fin m, if D (second u y (j, bit)) A = -(y (bestH y)) then 2 ^ bit.val else 0) =
            (π j).1.val := by
        intro j
        have hcongr :
            (∑ bit : Fin m, if D (second u y (j, bit)) A = -(y (bestH y)) then 2 ^ bit.val else 0) =
            (∑ bit : Fin m, if (π j).1.val.testBit bit.val then 2 ^ bit.val else 0) := by
          refine Finset.sum_congr rfl fun bit _ => ?_
          rw [hsec_eq j bit]
          by_cases htb : (π j).1.val.testBit bit.val = true
          · rw [if_pos htb, if_pos rfl, if_pos htb]
          · rw [if_neg htb, if_neg htb, if_neg]
            intro hneg
            have h2 : y (bestH y) + y (bestH y) = 0 := by linarith
            exact hv_ne (by linarith)
        rw [hcongr]
        exact sum_testBit_pow_two m (π j).1.val (lt_of_lt_of_le (π j).1.isLt hbm)
      have hlt : ∀ j : I,
          (∑ bit : Fin m, if D (second u y (j, bit)) A = -(y (bestH y)) then 2 ^ bit.val else 0) < b := by
        intro j; rw [hlabel j]; exact (π j).1.isLt
      rw [dif_pos hlt]
      congr 1
      refine Prod.ext ?_ hv_abs
      ext j
      exact hlabel j
    -- Count GoodSeed via its complement BadSeed = (Uall \ GoodU)^t
    let BadSeed : Finset (Fin R) :=
      Finset.univ.filter (fun u => ∀ h : Fin t, (eR u h).val ∉ GoodU)
    have hBad_card : BadSeed.card = (C - 2 ^ b) ^ t := by
      let BadU : Finset Uall := Finset.univ.filter (fun x : Uall => x.val ∉ GoodU)
      have hBadU_card : BadU.card = C - 2 ^ b := by
        have hsub : GoodU ⊆ Uall := Finset.filter_subset _ _
        have hbij : BadU.card = (Uall \ GoodU).card := by
          refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
          · intro x hx
            exact Finset.mem_sdiff.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
          · intro x1 _ x2 _ h; exact Subtype.ext h
          · intro U hU
            rcases Finset.mem_sdiff.mp hU with ⟨hUa, hUg⟩
            exact ⟨⟨U, hUa⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUg⟩, rfl⟩
        rw [hbij, Finset.card_sdiff_of_subset hsub, hUall_card, hGoodU_card]
      have hbij_seed : BadSeed.card = Fintype.card (Fin t → BadU) := by
        refine Finset.card_bij
          (fun u hu h => ⟨eR u h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2 h⟩⟩)
          ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro u1 _ u2 _ heq
          apply eR.injective
          funext h
          have h1 := congrFun heq h
          exact congrArg Subtype.val h1
        · intro g _
          refine ⟨eR.symm (fun h => (g h).val), ?_, ?_⟩
          · simp only [BadSeed, Finset.mem_filter, Finset.mem_univ, true_and]
            intro h
            rw [Equiv.apply_symm_apply]
            exact (Finset.mem_filter.mp (g h).property).2
          · funext h
            apply Subtype.ext
            simp
      rw [hbij_seed, Fintype.card_pi]
      simp only [Fintype.card_coe, hBadU_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hGood_plus_Bad : GoodSeed.card + BadSeed.card = R := by
      have hdisj : Disjoint GoodSeed BadSeed := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        rcases (Finset.mem_filter.mp h1).2 with ⟨h, hh⟩
        exact (Finset.mem_filter.mp h2).2 h hh
      have hunion : GoodSeed ∪ BadSeed = Finset.univ := by
        ext u
        simp only [GoodSeed, BadSeed, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          iff_true]
        by_cases h : ∃ h : Fin t, (eR u h).val ∈ GoodU
        · exact Or.inl h
        · push_neg at h; exact Or.inr h
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have h2b_le_C : 2 ^ b ≤ C := by
      rw [← hGoodU_card, ← hUall_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    -- Show 3 * (C - 2^b)^t <= C^t via (1 - x) <= exp(-x) and 3 <= 4 <= exp(2)
    have hbad_bound : 3 * BadSeed.card ≤ R := by
      rw [hBad_card]
      have hC_pos_r : (0 : ℝ) < (C : ℝ) := Nat.cast_pos.mpr hC_pos
      have hreal : (3 : ℝ) * ((C - 2 ^ b : ℕ) : ℝ) ^ t ≤ (C : ℝ) ^ t := by
        have hsub_cast : ((C - 2 ^ b : ℕ) : ℝ) = (C : ℝ) - (2 ^ b : ℝ) := by
          rw [Nat.cast_sub h2b_le_C]; push_cast; rfl
        have hfrac : ((C - 2 ^ b : ℕ) : ℝ) / (C : ℝ) = 1 - (2 ^ b : ℝ) / (C : ℝ) := by
          rw [hsub_cast, sub_div, div_self (ne_of_gt hC_pos_r)]
        have hbase_nn : (0 : ℝ) ≤ 1 - (2 ^ b : ℝ) / (C : ℝ) := by
          rw [← hfrac]; positivity
        have h1_le_exp : 1 - (2 ^ b : ℝ) / (C : ℝ) ≤ Real.exp (-((2 ^ b : ℝ) / (C : ℝ))) := by
          have h := Real.add_one_le_exp (-((2 ^ b : ℝ) / (C : ℝ)))
          linarith
        have hpow_le : (1 - (2 ^ b : ℝ) / (C : ℝ)) ^ t ≤
            Real.exp (-((t : ℝ) * (2 ^ b : ℝ) / (C : ℝ))) := by
          calc (1 - (2 ^ b : ℝ) / (C : ℝ)) ^ t
              ≤ (Real.exp (-((2 ^ b : ℝ) / (C : ℝ)))) ^ t :=
                pow_le_pow_left₀ hbase_nn h1_le_exp t
            _ = Real.exp ((t : ℝ) * (-((2 ^ b : ℝ) / (C : ℝ)))) := (Real.exp_nat_mul _ t).symm
            _ = Real.exp (-((t : ℝ) * (2 ^ b : ℝ) / (C : ℝ))) := by congr 1; ring
        have hexp_le : Real.exp (-((t : ℝ) * (2 ^ b : ℝ) / (C : ℝ))) ≤ Real.exp (-2) := by
          apply Real.exp_le_exp.mpr
          have htlb_r : (2 : ℝ) * (C : ℝ) ≤ (t : ℝ) * (2 ^ b : ℝ) := by exact_mod_cast ht_lb
          have hdiv_ge : (2 : ℝ) ≤ (t : ℝ) * (2 ^ b : ℝ) / (C : ℝ) := by
            rw [le_div_iff₀ hC_pos_r]; linarith
          linarith
        have hexp2_ge : (3 : ℝ) ≤ Real.exp 2 := by
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ); linarith
          have h2 : (4 : ℝ) ≤ Real.exp 2 := by
            calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
              _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
              _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
          linarith
        have h3exp : (3 : ℝ) * Real.exp (-2) ≤ 1 := by
          rw [Real.exp_neg]
          have hexp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
          calc (3 : ℝ) * (Real.exp 2)⁻¹ = 3 / Real.exp 2 := by ring
            _ ≤ 1 := (div_le_one hexp2_pos).mpr hexp2_ge
        have hdiv_le : (3 : ℝ) * (((C - 2 ^ b : ℕ) : ℝ) / (C : ℝ)) ^ t ≤ 1 := by
          rw [hfrac]
          calc (3 : ℝ) * (1 - (2 ^ b : ℝ) / (C : ℝ)) ^ t
              ≤ (3 : ℝ) * Real.exp (-((t : ℝ) * (2 ^ b : ℝ) / (C : ℝ))) :=
                mul_le_mul_of_nonneg_left hpow_le (by norm_num)
            _ ≤ (3 : ℝ) * Real.exp (-2) :=
                mul_le_mul_of_nonneg_left hexp_le (by norm_num)
            _ ≤ 1 := h3exp
        have hCt_pos : (0 : ℝ) < (C : ℝ) ^ t := pow_pos hC_pos_r t
        rw [div_pow] at hdiv_le
        have hmul := mul_le_mul_of_nonneg_right hdiv_le (le_of_lt hCt_pos)
        have hneCt : (C : ℝ) ^ t ≠ 0 := ne_of_gt hCt_pos
        calc (3 : ℝ) * ((C - 2 ^ b : ℕ) : ℝ) ^ t
            = (3 : ℝ) * (((C - 2 ^ b : ℕ) : ℝ) ^ t / (C : ℝ) ^ t) * (C : ℝ) ^ t := by
              field_simp [hneCt]
          _ ≤ 1 * (C : ℝ) ^ t := hmul
          _ = (C : ℝ) ^ t := one_mul _
      exact_mod_cast hreal
    have hcard_le : GoodSeed.card ≤
        ((Finset.univ : Finset (Fin R)).filter (fun u =>
          read u (fun h : Fin t => D (first u h) A)
            (fun p : I × Fin m => D (second u (fun h : Fin t => D (first u h) A) p) A) =
            some ((fun j : I => (π j).1), A.permanent))).card := by
      refine Finset.card_le_card fun u hu => ?_
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hgood_ok u hu⟩
    change 2 * R ≤ 3 *
      ((Finset.univ : Finset (Fin R)).filter (fun u =>
        read u (fun h : Fin t => D (first u h) A)
          (fun p : I × Fin m => D (second u (fun h : Fin t => D (first u h) A) p) A) =
          some ((fun j : I => (π j).1), A.permanent))).card
    omega

end PEqualNP.Outside.L_lib_1032_aux

open PEqualNP.Outside.L_lib_1032_aux in
theorem PEqualNP.Outside.L_lib_1032 :
∀ b m : ℕ, 0 < b → b ≤ 2^m →
  let I := Fin b × Fin 2
  let S := I × I → Bool
  let D := fun (s : S) (A : Matrix I I ℝ) =>
    Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix I I ℝ)
  ∃ (R t : ℕ) (first : Fin R → Fin t → S)
    (second : Fin R → (Fin t → ℝ) → I × Fin m → S)
    (read : Fin R → (Fin t → ℝ) → (I × Fin m → ℝ) → Option ((I → Fin b) × ℝ)),
    0 < R ∧ 0 < t ∧ t*2^b ≤ 2*Nat.choose (2*b) b + 2^b ∧
    let run := fun (u : Fin R) (A : Matrix I I ℝ) =>
      let y := fun h : Fin t => D (first u h) A
      read u y (fun p : I × Fin m => D (second u y p) A)
    (∀ u, run u 0 = none) ∧
    ∀ (π : Equiv.Perm I) (A : Matrix I I ℝ),
      (∀ i j, 0 ≤ A i j) → (∀ i j, i.1 ≠ (π j).1 → A i j = 0) → 0 < A.permanent →
      2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter (fun u =>
        run u A = some ((fun j : I => (π j).1), A.permanent))).card :=
  main_proof
