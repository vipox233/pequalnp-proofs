import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1031

open scoped Matrix

private def flipBit (c : Fin 2) : Fin 2 := ⟨1 - c.val, by omega⟩

private lemma flipBit_flipBit (c : Fin 2) : flipBit (flipBit c) = c := by
  fin_cases c <;> decide

private lemma flipBit_ne (c : Fin 2) : flipBit c ≠ c := by
  fin_cases c <;> decide

private def mkPerm {b : ℕ} (f : Fin b → Bool) : Equiv.Perm (Fin b × Fin 2) :=
  { toFun := fun p => (p.1, if f p.1 then flipBit p.2 else p.2)
    invFun := fun p => (p.1, if f p.1 then flipBit p.2 else p.2)
    left_inv := fun ⟨x, c⟩ => by
      by_cases hf : f x = true
      · simp [hf, flipBit_flipBit]
      · simp [hf]
    right_inv := fun ⟨x, c⟩ => by
      by_cases hf : f x = true
      · simp [hf, flipBit_flipBit]
      · simp [hf] }

private lemma sign_mkPerm {b : ℕ} (f : Fin b → Bool) :
    (Equiv.Perm.sign (mkPerm f) : ℤ) = ∏ x : Fin b, (if f x then (-1 : ℤ) else 1) := by
  classical
  have haux : ∀ S : Finset (Fin b),
      (Equiv.Perm.sign (mkPerm (fun x => decide (x ∈ S))) : ℤ) =
        ∏ x ∈ S, (-1 : ℤ) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h1 : mkPerm (fun x : Fin b => decide (x ∈ (∅ : Finset (Fin b)))) = 1 := by
        ext ⟨x, c⟩ <;> simp [mkPerm]
      rw [h1, map_one, Units.val_one, Finset.prod_empty]
    | insert a s ha ih =>
      have hmul : mkPerm (fun x : Fin b => decide (x ∈ insert a s)) =
          Equiv.swap (a, (0 : Fin 2)) (a, (1 : Fin 2)) * mkPerm (fun x : Fin b => decide (x ∈ s)) := by
        ext ⟨x, c⟩
        · simp only [mkPerm, Equiv.Perm.mul_apply, Equiv.coe_fn_mk]
          by_cases hxa : x = a
          · rw [hxa]
            have hns : a ∉ s := ha
            fin_cases c <;> simp [hns, flipBit, Equiv.swap_apply_def]
          · simp [hxa, Equiv.swap_apply_def]
        · simp only [mkPerm, Equiv.Perm.mul_apply, Equiv.coe_fn_mk]
          by_cases hxa : x = a
          · rw [hxa]
            have hns : a ∉ s := ha
            fin_cases c <;> simp [hns, flipBit, Equiv.swap_apply_def]
          · simp [hxa, Equiv.swap_apply_def]
      rw [hmul, map_mul, Units.val_mul,
        Equiv.Perm.sign_swap (fun h => by have := congrArg Prod.snd h; cases this),
        Units.val_neg, Units.val_one, ih, Finset.prod_insert ha]
  let S := Finset.univ.filter (fun x : Fin b => f x = true)
  have hf_eq : f = fun x => decide (x ∈ S) := by
    funext x
    cases h : f x <;> simp [S, h]
  rw [hf_eq, haux S]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : Fin b => x ∈ S)]
  have h1 : ∏ x ∈ Finset.univ.filter (fun x : Fin b => x ∈ S), (if decide (x ∈ S) then (-1 : ℤ) else 1) =
      ∏ x ∈ S, (-1 : ℤ) := by
    have hfilt : Finset.univ.filter (fun x : Fin b => x ∈ S) = S := by ext x; simp
    rw [hfilt]
    refine Finset.prod_congr rfl fun x hx => by simp [hx]
  have h2 : ∏ x ∈ Finset.univ.filter (fun x : Fin b => x ∉ S), (if decide (x ∈ S) then (-1 : ℤ) else 1) = 1 :=
    Finset.prod_eq_one fun x hx => by simp [(Finset.mem_filter.mp hx).2]
  rw [h1, h2, mul_one]

lemma card_filter_add_card_filter_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  by_cases hp : p x <;> simp [hp]

private lemma det_block_formula {b : ℕ} (U : Finset (Fin b × Fin 2)) (π : Equiv.Perm (Fin b × Fin 2)) :
    let M : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℤ := fun i j =>
      if i.1 = (π j).1 then (if i.2.val = 1 ∧ j ∈ U then -1 else 1) else 0
    M.det ≠ 0 ↔ ∀ x : Fin b, (π.symm (x, 0) ∈ U) ≠ (π.symm (x, 1) ∈ U) := by
  classical
  intro M
  let M' : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℤ := M.submatrix id π.symm
  have hdet_rel : M'.det = (Equiv.Perm.sign π.symm : ℤ) * M.det := by
    have h1 : M' = (Mᵀ.submatrix π.symm id)ᵀ := by
      ext i j; simp [M', Matrix.submatrix_apply, Matrix.transpose_apply]
    rw [h1, Matrix.det_transpose, Matrix.det_permute, Matrix.det_transpose]
    simp
  have hne_iff : M.det ≠ 0 ↔ M'.det ≠ 0 := by
    rw [hdet_rel]
    cases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with
    | inl h1 => rw [h1, Units.val_one, one_mul]
    | inr hneg => rw [hneg, Units.val_neg, Units.val_one, neg_one_mul, neg_ne_zero]
  rw [hne_iff]
  let s0 : Fin b → ℤ := fun x => if π.symm (x, 0) ∈ U then -1 else 1
  let s1 : Fin b → ℤ := fun x => if π.symm (x, 1) ∈ U then -1 else 1
  have hM'_det : M'.det = ∏ x : Fin b, (s1 x - s0 x) := by
    rw [Matrix.det_apply]
    let Good : Finset (Equiv.Perm (Fin b × Fin 2)) :=
      Finset.univ.filter (fun σ => ∀ i : Fin b × Fin 2, (σ i).1 = i.1)
    have hzero : ∀ σ ∈ Finset.univ \ Good,
        (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin b × Fin 2, M' (σ i) i = 0 := by
      intro σ hσ
      have hnot : ¬ ∀ i : Fin b × Fin 2, (σ i).1 = i.1 := by
        have := (Finset.mem_sdiff.mp hσ).2
        simpa [Good] using this
      push_neg at hnot
      rcases hnot with ⟨i0, hi0⟩
      have hprod0 : ∏ i : Fin b × Fin 2, M' (σ i) i = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i0)
        dsimp only [M', Matrix.submatrix_apply, id_eq]
        dsimp only [M]
        rw [Equiv.apply_symm_apply, if_neg hi0]
      rw [hprod0, mul_zero]
    have hsum_good : ∑ σ : Equiv.Perm (Fin b × Fin 2),
        Equiv.Perm.sign σ • ∏ i : Fin b × Fin 2, M' (σ i) i =
        ∑ σ ∈ Good, (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin b × Fin 2, M' (σ i) i := by
      have hsmul : ∀ σ : Equiv.Perm (Fin b × Fin 2),
          Equiv.Perm.sign σ • ∏ i : Fin b × Fin 2, M' (σ i) i =
            (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin b × Fin 2, M' (σ i) i := fun σ => by
        cases Int.units_eq_one_or (Equiv.Perm.sign σ) with
        | inl h1 => rw [h1, one_smul, Units.val_one, one_mul]
        | inr hneg => rw [hneg, Units.neg_smul, one_smul, Units.val_neg, Units.val_one, neg_one_mul]
      simp_rw [hsmul]
      rw [← Finset.sum_sdiff (Finset.subset_univ Good), Finset.sum_eq_zero hzero, zero_add]
    rw [hsum_good]
    have hbij : ∑ σ ∈ Good, (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin b × Fin 2, M' (σ i) i =
        ∑ f : Fin b → Bool, ∏ x : Fin b, (if f x then -s0 x else s1 x) := by
      symm
      refine Finset.sum_bij (fun f _ => mkPerm f) ?_ ?_ ?_ ?_
      · intro f _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => rfl⟩
      · intro f1 _ f2 _ heq
        funext x
        have h0 := congrArg (fun σ : Equiv.Perm (Fin b × Fin 2) => (σ (x, 0)).2) heq
        cases h1 : f1 x <;> cases h2 : f2 x <;> simp [mkPerm, flipBit, h1, h2] at h0 ⊢
      · intro σ hσ
        have hfix : ∀ i : Fin b × Fin 2, (σ i).1 = i.1 := (Finset.mem_filter.mp hσ).2
        let f : Fin b → Bool := fun x => decide ((σ (x, 0)).2 = 1)
        refine ⟨f, Finset.mem_univ _, ?_⟩
        ext ⟨x, c⟩
        · exact congrArg Fin.val (hfix (x, c)).symm
        · have hne : σ (x, 0) ≠ σ (x, 1) := fun h => by
            have := σ.injective h; cases this
          have hfst0 : (σ (x, 0)).1 = x := hfix (x, 0)
          have hfst1 : (σ (x, 1)).1 = x := hfix (x, 1)
          have hsnd_ne : (σ (x, 0)).2 ≠ (σ (x, 1)).2 := fun h => hne (Prod.ext (hfst0.trans hfst1.symm) h)
          fin_cases c
          · generalize h0 : (σ (x, 0)).2 = c0
            fin_cases c0 <;> simp [mkPerm, f, flipBit, h0]
          · generalize h0 : (σ (x, 0)).2 = c0 at hsnd_ne
            generalize h1 : (σ (x, 1)).2 = c1 at hsnd_ne
            fin_cases c0 <;> fin_cases c1 <;> simp [mkPerm, f, flipBit, h0, h1] at hsnd_ne ⊢
      · intro f _
        rw [sign_mkPerm]
        have hprod : ∏ i : Fin b × Fin 2, M' (mkPerm f i) i =
            ∏ x : Fin b, (if f x then s0 x else s1 x) := by
          rw [Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun x _ => ?_
          rw [Fin.prod_univ_two]
          dsimp only [M', Matrix.submatrix_apply, id_eq]
          dsimp only [M]
          cases hfx : f x <;> simp [mkPerm, flipBit, s0, s1, hfx]
        rw [hprod, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        cases f x <;> simp
    rw [hbij]
    have hps := Fintype.prod_sum (fun (x : Fin b) (c : Bool) => if c then -s0 x else s1 x)
    rw [← hps]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Fintype.sum_bool]
    simp
    ring
  rw [hM'_det, Finset.prod_ne_zero_iff]
  constructor
  · intro h x
    have hx := h x (Finset.mem_univ x)
    by_cases h0 : π.symm (x, 0) ∈ U <;> by_cases h1 : π.symm (x, 1) ∈ U <;>
      simp [s0, s1, h0, h1] at hx ⊢
  · intro h x _
    have hx := h x
    by_cases h0 : π.symm (x, 0) ∈ U <;> by_cases h1 : π.symm (x, 1) ∈ U <;>
      simp [s0, s1, h0, h1] at hx ⊢

private lemma card_balanced_cuts (b : ℕ) :
    ((Finset.univ : Finset (Finset (Fin b × Fin 2))).filter (fun U => U.card = b)).card =
      Nat.choose (2 * b) b := by
  have heq : (Finset.univ : Finset (Finset (Fin b × Fin 2))).filter (fun U => U.card = b) =
      Finset.powersetCard b (Finset.univ : Finset (Fin b × Fin 2)) := by
    ext U; simp
  rw [heq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, mul_comm]

private lemma chebyshev_count {α : Type*} [Fintype α] [DecidableEq α]
    (t h p C : ℕ) (good : α → Prop) [DecidablePred good]
    (hC : Fintype.card α = C)
    (hp : (Finset.univ.filter good).card = p)
    (hp_le : p ≤ C)
    (ht_pos : 0 < t)
    (hC_pos : 0 < C)
    (hp_pos : 0 < p)
    (hh_ge : 3 ≤ h)
    (hmu : 4 * h * C ≤ t * p) :
    let Space := Fin t → α
    let X : Space → ℕ := fun u => (Finset.univ.filter (fun r : Fin t => good (u r))).card
    27 * ((Finset.univ : Finset Space).filter (fun u => X u < h)).card ≤ 4 * Fintype.card Space := by
  classical
  intro Space X
  let R : ℕ := Fintype.card Space
  have hR_eq : R = C ^ t := by simp [R, Space, Fintype.card_fun, hC]
  let Y : Fin t → Space → ℤ := fun r u => if good (u r) then (C : ℤ) - (p : ℤ) else -(p : ℤ)
  have hsum_Y_eq : ∀ u : Space, (C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ) = ∑ r : Fin t, Y r u := by
    intro u
    have hsplit : ∑ r : Fin t, Y r u =
        (∑ r ∈ Finset.univ.filter (fun r : Fin t => good (u r)), ((C : ℤ) - (p : ℤ))) +
        (∑ r ∈ Finset.univ.filter (fun r : Fin t => ¬ good (u r)), (-(p : ℤ))) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin t => good (u r))]
      congr 1
      · refine Finset.sum_congr rfl fun r hr => by simp [Y, (Finset.mem_filter.mp hr).2]
      · refine Finset.sum_congr rfl fun r hr => by simp [Y, (Finset.mem_filter.mp hr).2]
    rw [hsplit, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hnot_card : (Finset.univ.filter (fun r : Fin t => ¬ good (u r))).card + X u = t := by
      have h1 := card_filter_add_card_filter_not (Finset.univ : Finset (Fin t))
        (fun r : Fin t => good (u r))
      rw [Finset.card_univ, Fintype.card_fin] at h1
      change X u + _ = t at h1
      omega
    have hnot_z : ((Finset.univ.filter (fun r : Fin t => ¬ good (u r))).card : ℤ) = (t : ℤ) - (X u : ℤ) := by
      omega
    rw [hnot_z]
    change (C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ) = (X u : ℤ) * ((C : ℤ) - (p : ℤ)) + ((t : ℤ) - (X u : ℤ)) * -(p : ℤ)
    ring
  have hY_single : ∀ r : Fin t, ∑ u : Space, Y r u = 0 := by
    intro r
    let Rest := {j : Fin t // j ≠ r} → α
    let eS : (α × Rest) ≃ Space :=
      { toFun := fun q j => if hj : j = r then q.1 else q.2 ⟨j, hj⟩
        invFun := fun u => (u r, fun j => u j.1)
        left_inv := fun ⟨a, f⟩ => by
          ext
          · simp
          · rename_i j; simp [j.2]
        right_inv := fun u => by
          funext j
          by_cases hj : j = r
          · subst hj; simp
          · simp [hj] }
    rw [← Fintype.sum_equiv eS _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hinner : ∀ a : α, ∑ _f : Rest, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) =
        (Fintype.card Rest : ℤ) * (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) := fun a => by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hstep : ∑ a : α, ∑ f : Rest, Y r (eS (a, f)) =
        (Fintype.card Rest : ℤ) * ∑ a : α, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : ∀ f : Rest, Y r (eS (a, f)) = if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ) :=
        fun f => by simp [Y, eS]
      simp_rw [h1]
      exact hinner a
    rw [hstep]
    have hsum_a : ∑ a : α, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) = 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ good]
      have h1 : ∑ a ∈ Finset.univ.filter good, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) =
          (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by
        have hc : ∀ a ∈ Finset.univ.filter good, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) = (C : ℤ) - (p : ℤ) :=
          fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, hp, nsmul_eq_mul]
      have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) =
          ((C : ℤ) - (p : ℤ)) * -(p : ℤ) := by
        have hc : ∀ a ∈ Finset.univ.filter (fun a => ¬ good a), (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) = -(p : ℤ) :=
          fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        have hnc : (Finset.univ.filter (fun a => ¬ good a)).card + p = C := by
          have h0 := card_filter_add_card_filter_not (Finset.univ : Finset α) good
          rw [Finset.card_univ, hC, hp] at h0; omega
        have hnz : ((Finset.univ.filter (fun a => ¬ good a)).card : ℤ) = (C : ℤ) - (p : ℤ) := by omega
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hnz]
      rw [h1, h2]; ring
    rw [hsum_a, mul_zero]
  have hY_sq : ∀ r : Fin t, ∑ u : Space, (Y r u) * (Y r u) = (R : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by
    intro r
    let Rest := {j : Fin t // j ≠ r} → α
    let eS : (α × Rest) ≃ Space :=
      { toFun := fun q j => if hj : j = r then q.1 else q.2 ⟨j, hj⟩
        invFun := fun u => (u r, fun j => u j.1)
        left_inv := fun ⟨a, f⟩ => by
          ext
          · simp
          · rename_i j; simp [j.2]
        right_inv := fun u => by
          funext j
          by_cases hj : j = r
          · subst hj; simp
          · simp [hj] }
    have hcard_Rest : Fintype.card Rest * C = R := by
      have h1 := Fintype.card_congr eS
      rw [Fintype.card_prod, hC, mul_comm] at h1
      exact h1
    rw [← Fintype.sum_equiv eS _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hstep : ∑ a : α, ∑ f : Rest, Y r (eS (a, f)) * Y r (eS (a, f)) =
        (Fintype.card Rest : ℤ) * ∑ a : α, (if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : ∀ f : Rest, Y r (eS (a, f)) * Y r (eS (a, f)) =
          if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2 := fun f => by
        by_cases hga : good a <;> simp [Y, eS, hga, sq]
      simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hstep]
    have hsum_a : ∑ a : α, (if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2) =
        (C : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ good]
      have h1 : ∑ a ∈ Finset.univ.filter good, (if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2) =
          (p : ℤ) * ((C : ℤ) - (p : ℤ)) ^ 2 := by
        have hc : ∀ a ∈ Finset.univ.filter good, (if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2) = ((C : ℤ) - (p : ℤ)) ^ 2 :=
          fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, hp, nsmul_eq_mul]
      have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), (if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2) =
          ((C : ℤ) - (p : ℤ)) * (p : ℤ) ^ 2 := by
        have hc : ∀ a ∈ Finset.univ.filter (fun a => ¬ good a), (if good a then ((C : ℤ) - (p : ℤ)) ^ 2 else (p : ℤ) ^ 2) = (p : ℤ) ^ 2 :=
          fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        have hnc : (Finset.univ.filter (fun a => ¬ good a)).card + p = C := by
          have h0 := card_filter_add_card_filter_not (Finset.univ : Finset α) good
          rw [Finset.card_univ, hC, hp] at h0; omega
        have hnz : ((Finset.univ.filter (fun a => ¬ good a)).card : ℤ) = (C : ℤ) - (p : ℤ) := by omega
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hnz]
      rw [h1, h2]; ring
    rw [hsum_a]
    have hRz : (Fintype.card Rest : ℤ) * (C : ℤ) = (R : ℤ) := by exact_mod_cast hcard_Rest
    calc (Fintype.card Rest : ℤ) * ((C : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ)))
        = ((Fintype.card Rest : ℤ) * (C : ℤ)) * (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by ring
      _ = (R : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by rw [hRz]
  have hY_cross : ∀ r1 r2 : Fin t, r1 ≠ r2 → ∑ u : Space, Y r1 u * Y r2 u = 0 := by
    intro r1 r2 hne
    let Rest := {j : Fin t // j ≠ r1 ∧ j ≠ r2} → α
    let eS : (α × α × Rest) ≃ Space :=
      { toFun := fun q j =>
          if h1 : j = r1 then q.1 else if h2 : j = r2 then q.2.1 else q.2.2 ⟨j, h1, h2⟩
        invFun := fun u => (u r1, u r2, fun j => u j.1)
        left_inv := fun ⟨a1, a2, f⟩ => by
          refine Prod.ext (by simp) (Prod.ext (by simp [hne.symm]) ?_)
          funext j; simp [j.2.1, j.2.2]
        right_inv := fun u => by
          funext j
          by_cases h1 : j = r1
          · subst h1; simp
          · by_cases h2 : j = r2
            · subst h2; simp [h1]
            · simp [h1, h2] }
    rw [← Fintype.sum_equiv eS _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hsum_a : ∑ a : α, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) = 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ good]
      have h1 : ∑ a ∈ Finset.univ.filter good, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) =
          (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by
        have hc : ∀ a ∈ Finset.univ.filter good, (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) = (C : ℤ) - (p : ℤ) :=
          fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, hp, nsmul_eq_mul]
      have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬ good a), (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) =
          ((C : ℤ) - (p : ℤ)) * -(p : ℤ) := by
        have hc : ∀ a ∈ Finset.univ.filter (fun a => ¬ good a), (if good a then (C : ℤ) - (p : ℤ) else -(p : ℤ)) = -(p : ℤ) :=
          fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        have hnc : (Finset.univ.filter (fun a => ¬ good a)).card + p = C := by
          have h0 := card_filter_add_card_filter_not (Finset.univ : Finset α) good
          rw [Finset.card_univ, hC, hp] at h0; omega
        have hnz : ((Finset.univ.filter (fun a => ¬ good a)).card : ℤ) = (C : ℤ) - (p : ℤ) := by omega
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hnz]
      rw [h1, h2]; ring
    have hinner : ∀ a1 : α, ∑ q : α × Rest, Y r1 (eS (a1, q)) * Y r2 (eS (a1, q)) = 0 := by
      intro a1
      rw [Fintype.sum_prod_type]
      have h1 : ∀ a2 : α, ∀ f : Rest, Y r1 (eS (a1, a2, f)) * Y r2 (eS (a1, a2, f)) =
          (if good a1 then (C : ℤ) - (p : ℤ) else -(p : ℤ)) *
          (if good a2 then (C : ℤ) - (p : ℤ) else -(p : ℤ)) := fun a2 f => by
        simp [Y, eS, hne.symm]
      simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      rw [hsum_a, mul_zero, mul_zero]
    exact Finset.sum_eq_zero fun a1 _ => hinner a1
  have hvar : ∑ u : Space, ((C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ)) ^ 2 =
      (t : ℤ) * (R : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ)) := by
    simp_rw [hsum_Y_eq, sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap : ∀ r1 : Fin t,
        (∑ u : Space, ∑ r2 : Fin t, Y r1 u * Y r2 u) = ∑ r2 : Fin t, ∑ u : Space, Y r1 u * Y r2 u :=
      fun _ => Finset.sum_comm
    simp_rw [hswap]
    have hdiag : ∀ r1 : Fin t, ∑ r2 : Fin t, ∑ u : Space, Y r1 u * Y r2 u =
        (R : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ)) := fun r1 => by
      rw [Finset.sum_eq_single r1]
      · exact hY_sq r1
      · intro r2 _ hne; exact hY_cross r1 r2 hne.symm
      · intro h; exact (h (Finset.mem_univ r1)).elim
    simp_rw [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  let Few := (Finset.univ : Finset Space).filter (fun u => X u < h)
  have hlow : (Few.card : ℤ) * (9 * ((t : ℤ) * (p : ℤ)) ^ 2) ≤
      16 * ∑ u : Space, ((C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ)) ^ 2 := by
    have hsub : ∑ u ∈ Few, (9 * ((t : ℤ) * (p : ℤ)) ^ 2) ≤
        ∑ u ∈ Few, 16 * ((C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ)) ^ 2 := by
      refine Finset.sum_le_sum fun u hu => ?_
      have hlt : X u < h := (Finset.mem_filter.mp hu).2
      have hCx : (C : ℤ) * (X u : ℤ) ≤ (C : ℤ) * (h : ℤ) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast le_of_lt hlt) (by omega)
      have hmu_z : 4 * (h : ℤ) * (C : ℤ) ≤ (t : ℤ) * (p : ℤ) := by exact_mod_cast hmu
      have hgap : 3 * ((t : ℤ) * (p : ℤ)) ≤ 4 * ((t : ℤ) * (p : ℤ) - (C : ℤ) * (X u : ℤ)) := by linarith
      have hnn : 0 ≤ 3 * ((t : ℤ) * (p : ℤ)) := by positivity
      have hsq := mul_self_le_mul_self hnn hgap
      nlinarith
    have hnonneg : ∑ u ∈ Few, 16 * ((C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ)) ^ 2 ≤
        ∑ u : Space, 16 * ((C : ℤ) * (X u : ℤ) - (t : ℤ) * (p : ℤ)) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun u => by positivity
    rw [Finset.sum_const, nsmul_eq_mul] at hsub
    have htot := hsub.trans hnonneg
    rwa [← Finset.mul_sum] at htot
  rw [hvar] at hlow
  have hvar_le : 16 * ((t : ℤ) * (R : ℤ) * (p : ℤ) * ((C : ℤ) - (p : ℤ))) ≤
      16 * ((t : ℤ) * (R : ℤ) * (p : ℤ) * (C : ℤ)) := by
    have hnonneg : 0 ≤ 16 * ((t : ℤ) * (R : ℤ) * (p : ℤ)) := by positivity
    have hle : (C : ℤ) - (p : ℤ) ≤ (C : ℤ) := by omega
    nlinarith
  have hcomb : (Few.card : ℤ) * (9 * ((t : ℤ) * (p : ℤ)) ^ 2) ≤
      16 * ((t : ℤ) * (R : ℤ) * (p : ℤ) * (C : ℤ)) := hlow.trans hvar_le
  have htp_pos : 0 < (t : ℤ) * (p : ℤ) := by positivity
  have hcancel1 : (Few.card : ℤ) * (9 * ((t : ℤ) * (p : ℤ))) ≤ 16 * ((R : ℤ) * (C : ℤ)) := by
    nlinarith
  have htp_ge : 12 * (C : ℤ) ≤ (t : ℤ) * (p : ℤ) := by
    have hmu_z : 4 * (h : ℤ) * (C : ℤ) ≤ (t : ℤ) * (p : ℤ) := by exact_mod_cast hmu
    have hh_z : (3 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh_ge
    nlinarith
  have h108 : (Few.card : ℤ) * (108 * (C : ℤ)) ≤ 16 * ((R : ℤ) * (C : ℤ)) := by
    have h1 : (Few.card : ℤ) * (9 * (12 * (C : ℤ))) ≤ (Few.card : ℤ) * (9 * ((t : ℤ) * (p : ℤ))) := by
      have hnn : 0 ≤ (Few.card : ℤ) * 9 := by positivity
      nlinarith
    linarith
  have hCz_pos : (0 : ℤ) < (C : ℤ) := by exact_mod_cast hC_pos
  have h27 : 27 * (Few.card : ℤ) ≤ 4 * (R : ℤ) := by nlinarith
  exact_mod_cast h27

end PEqualNP.Outside.L_lib_1031

set_option maxHeartbeats 800000 in
open PEqualNP.Outside.L_lib_1031 in
theorem PEqualNP.Outside.L_lib_1031 :
    ∀ b m : ℕ, 0 < b → b ≤ 2^m →
      let I := Fin b × Fin 2
      let P := I → I → Bool
      let pair := fun (π : Equiv.Perm I) (j k : I) => decide ((π j).1 = (π k).1)
      let D := fun (U : Finset I) (π : Equiv.Perm I) =>
        Matrix.det (fun i j => if i.1 = (π j).1 then
          (if i.2.val = 1 ∧ j ∈ U then -1 else 1) else 0 : Matrix I I ℤ)
      ∃ (R t : ℕ) (cuts : Fin R → Fin t → Finset I) (read : Fin R → (Fin t → Bool) → Option P),
        0 < R ∧ 0 < t ∧ t*2^b ≤ 4*(2*m+3)*Nat.choose (2*b) b + 2^b ∧
        (∀ u h, (cuts u h).card = b) ∧ (∀ u, read u (fun _ => false) = none) ∧
        ∀ π : Equiv.Perm I, 2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter (fun u =>
          read u (fun h => decide (D (cuts u h) π ≠ 0)) = some (pair π))).card := by
  classical
  intro b m hb hbm I P pair D
  let B : Finset (Finset I) := (Finset.univ : Finset (Finset I)).filter (fun U => U.card = b)
  have hB_card : B.card = Nat.choose (2 * b) b := card_balanced_cuts b
  have hB_pos : 0 < B.card := by
    rw [hB_card]
    exact Nat.choose_pos (by omega)
  let h : ℕ := 2 * m + 3
  let t : ℕ := (4 * h * B.card) / 2 ^ b + 1
  have ht_pos : 0 < t := Nat.succ_pos _
  have ht_le : t * 2 ^ b ≤ 4 * (2 * m + 3) * Nat.choose (2 * b) b + 2 ^ b := by
    have hdiv : ((4 * h * B.card) / 2 ^ b) * 2 ^ b ≤ 4 * h * B.card := Nat.div_mul_le_self _ _
    dsimp only [t, h]
    rw [← hB_card, Nat.add_mul, one_mul]
    exact Nat.add_le_add_right hdiv (2 ^ b)
  have hmu : 4 * h * B.card ≤ t * 2 ^ b := by
    have hpos2 : 0 < 2 ^ b := Nat.pos_of_ne_zero (by positivity)
    have hlt := Nat.lt_div_mul_add hpos2 (a := 4 * h * B.card)
    dsimp only [t]
    rw [Nat.add_mul, one_mul]
    omega
  let α := {U : Finset I // U ∈ B}
  have hα_card : Fintype.card α = B.card := Fintype.card_coe B
  let Space := Fin t → α
  let R : ℕ := Fintype.card Space
  have hR_pos : 0 < R := by
    change 0 < Fintype.card Space
    rw [Fintype.card_fun, hα_card, Fintype.card_fin]
    exact Nat.pos_of_ne_zero (pow_ne_zero t (Nat.ne_of_gt hB_pos))
  let eR : Fin R ≃ Space := (Fintype.equivFin Space).symm
  let cuts : Fin R → Fin t → Finset I := fun u r => (eR u r).1
  let read : Fin R → (Fin t → Bool) → Option P := fun u obs =>
    let H := (Finset.univ : Finset (Fin t)).filter (fun r => obs r = true)
    if H.card < h then none
    else some (fun j k => decide (j = k ∨ ∀ r ∈ H, (j ∈ cuts u r) ≠ (k ∈ cuts u r)))
  refine ⟨R, t, cuts, read, hR_pos, ht_pos, ht_le, ?_, ?_, ?_⟩
  · intro u r
    exact (Finset.mem_filter.mp (eR u r).2).2
  · intro u
    have h0 : ((Finset.univ : Finset (Fin t)).filter (fun _ => false = true)).card < h := by
      simp [h]
    simp only [read, if_pos h0]
  · intro π
    let hit : α → Prop := fun a => ∀ x : Fin b, (π.symm (x, 0) ∈ a.1) ≠ (π.symm (x, 1) ∈ a.1)
    have hD_iff : ∀ a : α, (D a.1 π ≠ 0) ↔ hit a := fun a => det_block_formula a.1 π
    let transv : (Fin b → Fin 2) → α := fun g =>
      ⟨Finset.univ.image (fun x : Fin b => π.symm (x, g x)), by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [Finset.card_image_of_injective]
        · exact Finset.card_fin b
        · intro x1 x2 heq
          have := congrArg Prod.fst (π.symm.injective heq)
          exact this⟩
    have htransv_inj : Function.Injective transv := by
      intro g1 g2 heq
      have hset : (transv g1).1 = (transv g2).1 := congrArg Subtype.val heq
      funext x
      have hmem : π.symm (x, g1 x) ∈ (transv g2).1 := by
        rw [← hset]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
      rcases Finset.mem_image.mp hmem with ⟨x', _, hx'⟩
      have hp := π.symm.injective hx'
      have hx_eq : x' = x := congrArg Prod.fst hp
      subst hx_eq
      exact (congrArg Prod.snd hp).symm
    have hhit_set : (Finset.univ : Finset α).filter hit = Finset.univ.image transv := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ha
        let g : Fin b → Fin 2 := fun x => if π.symm (x, 0) ∈ a.1 then 0 else 1
        refine ⟨g, Subtype.ext ?_⟩
        ext p
        simp only [transv, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, rfl⟩
          dsimp only [g]
          split_ifs with h0
          · exact h0
          · have h1 := ha x
            by_contra hn1
            exact h1 (propext (iff_of_false h0 hn1))
        · intro hp
          refine ⟨(π p).1, ?_⟩
          have hp_eq : π.symm (π p) = p := π.symm_apply_apply p
          have hpair : p = π.symm ((π p).1, (π p).2) := hp_eq.symm
          have hgx : g (π p).1 = (π p).2 := by
            dsimp only [g]
            have hax := ha (π p).1
            generalize hc : (π p).2 = c at hpair
            fin_cases c
            · dsimp only at hpair; rw [hpair] at hp
              have hp0 : π.symm ((π p).1, 0) ∈ a.1 := hp
              simp [hp0]
            · dsimp only at hpair; rw [hpair] at hp
              have hn0 : π.symm ((π p).1, 0) ∉ a.1 := fun h0 => hax (propext (iff_of_true h0 hp))
              simp [hn0]
          rw [hgx, ← hpair]
      · rintro ⟨g, rfl⟩ x
        have hmem_g : π.symm (x, g x) ∈ (transv g).1 :=
          Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
        have hnot_other : π.symm (x, flipBit (g x)) ∉ (transv g).1 := by
          intro hm
          rcases Finset.mem_image.mp hm with ⟨x', _, hx'⟩
          have hp := π.symm.injective hx'
          have hx_eq : x' = x := congrArg Prod.fst hp
          rw [hx_eq] at hp
          exact flipBit_ne (g x) (congrArg Prod.snd hp).symm
        generalize hgx : g x = c at hmem_g hnot_other
        fin_cases c
        · exact fun hiff => hnot_other (hiff.mp hmem_g)
        · exact fun hiff => hnot_other (hiff.mpr hmem_g)
    have hhit_card : ((Finset.univ : Finset α).filter hit).card = 2 ^ b := by
      rw [hhit_set, Finset.card_image_of_injective _ htransv_inj, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin]
    have h2b_le : 2 ^ b ≤ B.card := by
      rw [← hhit_card, ← hα_card]
      exact Finset.card_le_univ _
    let X : Space → ℕ := fun u => (Finset.univ.filter (fun r : Fin t => hit (u r))).card
    have hcheb : 27 * ((Finset.univ : Finset Space).filter (fun u => X u < h)).card ≤ 4 * R :=
      chebyshev_count t h (2 ^ b) B.card hit hα_card hhit_card h2b_le ht_pos hB_pos
        (Nat.pos_of_ne_zero (by positivity)) (by dsimp only [h]; omega) hmu
    let hitSet : Space → Finset (Fin t) := fun u => Finset.univ.filter (fun r : Fin t => hit (u r))
    let badPair : Space → Prop := fun u =>
      ∃ (x y : Fin b), x < y ∧ ∃ c : Fin 2, ∀ r ∈ hitSet u,
        (π.symm (x, 0) ∈ (u r).1) ≠ (π.symm (y, c) ∈ (u r).1)
    have hcoll_bound : 8 * ((Finset.univ : Finset Space).filter (fun u => h ≤ X u ∧ badPair u)).card ≤ R := by
      let Hgood : Finset (Finset (Fin t)) := Finset.univ.filter (fun H => h ≤ H.card)
      have hbiU_bad : (Finset.univ : Finset Space).filter (fun u => h ≤ X u ∧ badPair u) =
          Hgood.biUnion (fun H => (Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Hgood]
        constructor
        · intro ⟨hge, hbp⟩; exact ⟨hitSet u, hge, rfl, hbp⟩
        · rintro ⟨H, hge, rfl, hbp⟩; exact ⟨hge, hbp⟩
      have hbiU_all : (Finset.univ : Finset Space).filter (fun u => h ≤ X u) =
          Hgood.biUnion (fun H => (Finset.univ : Finset Space).filter (fun u => hitSet u = H)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Hgood]
        constructor
        · intro hge; exact ⟨hitSet u, hge, rfl⟩
        · rintro ⟨H, hge, rfl⟩; exact hge
      have hdisj_bad : ∀ H1 ∈ Hgood, ∀ H2 ∈ Hgood, H1 ≠ H2 →
          Disjoint ((Finset.univ : Finset Space).filter (fun u => hitSet u = H1 ∧ badPair u))
            ((Finset.univ : Finset Space).filter (fun u => hitSet u = H2 ∧ badPair u)) := by
        intro H1 _ H2 _ hne
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
      have hdisj_all : ∀ H1 ∈ Hgood, ∀ H2 ∈ Hgood, H1 ≠ H2 →
          Disjoint ((Finset.univ : Finset Space).filter (fun u => hitSet u = H1))
            ((Finset.univ : Finset Space).filter (fun u => hitSet u = H2)) := by
        intro H1 _ H2 _ hne
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hperH : ∀ H ∈ Hgood,
          8 * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card ≤
            ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card := by
        intro H hH
        have hH_ge : h ≤ H.card := (Finset.mem_filter.mp hH).2
        let Miss : Finset α := Finset.univ.filter (fun a => ¬ hit a)
        let HitA : Finset α := Finset.univ.filter hit
        let eH : ((H → HitA) × ({r : Fin t // r ∉ H} → Miss)) ≃
            {u : Space // hitSet u = H} :=
          { toFun := fun q =>
              ⟨fun r => if hr : r ∈ H then (q.1 ⟨r, hr⟩).1 else (q.2 ⟨r, hr⟩).1, by
                ext r
                simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
                by_cases hr : r ∈ H
                · simp only [dif_pos hr]
                  exact ⟨fun _ => hr, fun _ => (Finset.mem_filter.mp (q.1 ⟨r, hr⟩).2).2⟩
                · simp only [dif_neg hr]
                  exact ⟨fun hhit => ((Finset.mem_filter.mp (q.2 ⟨r, hr⟩).2).2 hhit).elim, fun h' => (hr h').elim⟩⟩
            invFun := fun u =>
              (fun r => ⟨u.1 r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                  have := Finset.ext_iff.mp u.2 r.1
                  simpa [hitSet, r.2] using this.mpr r.2⟩⟩,
               fun r => ⟨u.1 r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                  have := Finset.ext_iff.mp u.2 r.1
                  simpa [hitSet, r.2] using mt this.mp r.2⟩⟩)
            left_inv := fun ⟨q1, q2⟩ => by
              ext r
              · simp [r.2]
              · simp [r.2]
            right_inv := fun ⟨u, hu⟩ => by
              apply Subtype.ext; funext r
              by_cases hr : r ∈ H <;> simp [hr] }
        have hcard_H : ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card =
            (2 ^ b) ^ H.card * Miss.card ^ (t - H.card) := by
          have h1 : ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card =
              Fintype.card {u : Space // hitSet u = H} := by
            rw [Fintype.card_subtype]
          rw [h1, ← Fintype.card_congr eH, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
            Fintype.card_coe, Fintype.card_coe, Fintype.card_coe, hhit_card]
          congr 2
          have hcomp : Fintype.card {r : Fin t // r ∉ H} = (Finset.univ \ H).card := by
            rw [Fintype.card_subtype]
            congr 1; ext r; simp
          rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ, Fintype.card_fin]
        let Triples : Finset ((Fin b × Fin b) × Fin 2) :=
          (Finset.univ.filter (fun p : Fin b × Fin b => p.1 < p.2)).product Finset.univ
        have hTriples_card : Triples.card ≤ b * b := by
          dsimp only [Triples]
          rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
          let Slt := (Finset.univ : Finset (Fin b × Fin b)).filter (fun p => p.1 < p.2)
          let Sgt := (Finset.univ : Finset (Fin b × Fin b)).filter (fun p => p.2 < p.1)
          have hswap : Slt.card = Sgt.card :=
            Finset.card_bij (fun p _ => (p.2, p.1))
              (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
              (fun _ _ _ _ h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
              (fun p hp => ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩)
          have hdisj : Disjoint Slt Sgt := by
            rw [Finset.disjoint_left]
            intro p h1 h2
            exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
          have hle : (Slt ∪ Sgt).card ≤ b * b := by
            have := Finset.card_le_univ (Slt ∪ Sgt)
            simpa [Fintype.card_prod, Fintype.card_fin] using this
          rw [Finset.card_union_of_disjoint hdisj, ← hswap] at hle
          change Slt.card * 2 ≤ b * b
          omega
        have hsub_u : (Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u) ⊆
            Triples.biUnion (fun tr =>
              (Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧
                ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1))) := by
          intro u hu
          rcases (Finset.mem_filter.mp hu).2 with ⟨hH_eq, x, y, hxy, c, hbad⟩
          refine Finset.mem_biUnion.mpr ⟨((x, y), c), ?_, ?_⟩
          · dsimp only [Triples]
            rw [Finset.product_eq_sprod, Finset.mem_product]
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, Finset.mem_univ _⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH_eq, by simpa [hH_eq] using hbad⟩
        have hper_tr : ∀ tr ∈ Triples,
            2 ^ H.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧
              ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1))).card =
            ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card := by
          intro tr htr
          dsimp only [Triples] at htr
          rw [Finset.product_eq_sprod, Finset.mem_product] at htr
          have hxy : tr.1.1 < tr.1.2 := (Finset.mem_filter.mp htr.1).2
          have hxy_ne : tr.1.1 ≠ tr.1.2 := ne_of_lt hxy
          let GoodA : Finset α := HitA.filter (fun a =>
            (π.symm (tr.1.1, 0) ∈ a.1) ≠ (π.symm (tr.1.2, tr.2) ∈ a.1))
          have hGoodA_card : 2 * GoodA.card = 2 ^ b := by
            let flipY : (Fin b → Fin 2) → (Fin b → Fin 2) := fun g z =>
              if z = tr.1.2 then flipBit (g z) else g z
            have hflip_invol : ∀ g, flipY (flipY g) = g := fun g => by
              funext z; by_cases hz : z = tr.1.2 <;> simp [flipY, hz, flipBit_flipBit]
            let BadA : Finset α := HitA.filter (fun a =>
              ¬ ((π.symm (tr.1.1, 0) ∈ a.1) ≠ (π.symm (tr.1.2, tr.2) ∈ a.1)))
            have hmem_transv : ∀ (g : Fin b → Fin 2) (z : Fin b) (d : Fin 2),
                π.symm (z, d) ∈ (transv g).1 ↔ g z = d := fun g z d => by
              simp only [transv, Finset.mem_image, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨z', hz'⟩
                have hp := π.symm.injective hz'
                have hz_eq : z' = z := congrArg Prod.fst hp
                subst hz_eq; exact congrArg Prod.snd hp
              · intro hgd; exact ⟨z, by rw [hgd]⟩
            have hswap_ab : GoodA.card = BadA.card := by
              let fG : Finset (Fin b → Fin 2) :=
                Finset.univ.filter (fun g => (g tr.1.1 = 0) ≠ (g tr.1.2 = tr.2))
              let fB : Finset (Fin b → Fin 2) :=
                Finset.univ.filter (fun g => ¬ ((g tr.1.1 = 0) ≠ (g tr.1.2 = tr.2)))
              have hG_eq : GoodA = fG.image transv := by
                ext a
                simp only [GoodA, HitA, hhit_set, fG, Finset.mem_filter, Finset.mem_image,
                  Finset.mem_univ, true_and]
                constructor
                · rintro ⟨⟨g, rfl⟩, hcond⟩
                  refine ⟨g, ?_, rfl⟩
                  simpa [hmem_transv] using hcond
                · rintro ⟨g, hcond, rfl⟩
                  exact ⟨⟨g, rfl⟩, by simpa [hmem_transv] using hcond⟩
              have hB_eq : BadA = fB.image transv := by
                ext a
                simp only [BadA, HitA, hhit_set, fB, Finset.mem_filter, Finset.mem_image,
                  Finset.mem_univ, true_and]
                constructor
                · rintro ⟨⟨g, rfl⟩, hcond⟩
                  refine ⟨g, ?_, rfl⟩
                  simpa [hmem_transv] using hcond
                · rintro ⟨g, hcond, rfl⟩
                  exact ⟨⟨g, rfl⟩, by simpa [hmem_transv] using hcond⟩
              rw [hG_eq, hB_eq, Finset.card_image_of_injective _ htransv_inj,
                Finset.card_image_of_injective _ htransv_inj]
              refine Finset.card_bij (fun g _ => flipY g) ?_ ?_ ?_
              · intro g hg
                have hc := (Finset.mem_filter.mp hg).2
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                simp only [flipY, hxy_ne, ↓reduceIte]
                have hflip_iff : (flipBit (g tr.1.2) = tr.2) ↔ ¬ (g tr.1.2 = tr.2) := by
                  generalize h1 : g tr.1.2 = c1
                  generalize h2 : tr.2 = c2
                  fin_cases c1 <;> fin_cases c2 <;> decide
                rw [propext hflip_iff]
                intro hne
                exact hc (by tauto)
              · intro g1 _ g2 _ h
                have := congrArg flipY h
                rwa [hflip_invol, hflip_invol] at this
              · intro g hg
                have hc := (Finset.mem_filter.mp hg).2
                refine ⟨flipY g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hflip_invol g⟩
                simp only [flipY, hxy_ne, ↓reduceIte]
                have hflip_iff : (flipBit (g tr.1.2) = tr.2) ↔ ¬ (g tr.1.2 = tr.2) := by
                  generalize h1 : g tr.1.2 = c1
                  generalize h2 : tr.2 = c2
                  fin_cases c1 <;> fin_cases c2 <;> decide
                rw [propext hflip_iff]
                intro heq
                exact hc (by tauto)
            have hsum := card_filter_add_card_filter_not HitA
              (fun a => (π.symm (tr.1.1, 0) ∈ a.1) ≠ (π.symm (tr.1.2, tr.2) ∈ a.1))
            change GoodA.card + BadA.card = HitA.card at hsum
            rw [← hswap_ab] at hsum
            have hHitA : HitA.card = 2 ^ b := hhit_card
            omega
          let eTr : ((H → GoodA) × ({r : Fin t // r ∉ H} → Miss)) ≃
              {u : Space // hitSet u = H ∧
                ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1)} :=
            { toFun := fun q =>
                ⟨(eH (fun r => ⟨(q.1 r).1, (Finset.mem_filter.mp (q.1 r).2).1⟩, q.2)).1,
                  (eH (fun r => ⟨(q.1 r).1, (Finset.mem_filter.mp (q.1 r).2).1⟩, q.2)).2,
                  fun r hr => by
                    simpa [eH, hr] using (Finset.mem_filter.mp (q.1 ⟨r, hr⟩).2).2⟩
              invFun := fun u =>
                (fun r => ⟨u.1 r.1, Finset.mem_filter.mpr
                    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                      have := Finset.ext_iff.mp u.2.1 r.1
                      simpa [hitSet, r.2] using this.mpr r.2⟩,
                     u.2.2 r.1 r.2⟩⟩,
                 (eH.symm ⟨u.1, u.2.1⟩).2)
              left_inv := fun ⟨q1, q2⟩ => by
                ext r
                · simp [eH, r.2]
                · simp [eH, r.2]
              right_inv := fun ⟨u, hu1, hu2⟩ => by
                apply Subtype.ext; funext r
                by_cases hr : r ∈ H <;> simp [eH, hr] }
          have hcard_tr : ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧
              ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1))).card =
              GoodA.card ^ H.card * Miss.card ^ (t - H.card) := by
            have h1 : ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧
                ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1))).card =
                Fintype.card {u : Space // hitSet u = H ∧
                  ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1)} := by
              rw [Fintype.card_subtype]
            rw [h1, ← Fintype.card_congr eTr, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
              Fintype.card_coe, Fintype.card_coe, Fintype.card_coe]
            congr 2
            have hcomp : Fintype.card {r : Fin t // r ∉ H} = (Finset.univ \ H).card := by
              rw [Fintype.card_subtype]; congr 1; ext r; simp
            rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ, Fintype.card_fin]
          rw [hcard_tr, hcard_H, ← mul_assoc, ← Nat.mul_pow, hGoodA_card]
        have hunion_le := (Finset.card_le_card hsub_u).trans Finset.card_biUnion_le
        have hmul_le : 2 ^ H.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card ≤
            Triples.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card := by
          calc 2 ^ H.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card
              ≤ 2 ^ H.card * ∑ tr ∈ Triples, ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧
                  ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1))).card :=
                Nat.mul_le_mul_left _ hunion_le
            _ = ∑ tr ∈ Triples, 2 ^ H.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧
                  ∀ r ∈ H, (π.symm (tr.1.1, 0) ∈ (u r).1) ≠ (π.symm (tr.1.2, tr.2) ∈ (u r).1))).card :=
                Finset.mul_sum _ _ _
            _ = ∑ _tr ∈ Triples, ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card :=
                Finset.sum_congr rfl hper_tr
            _ = Triples.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card := by
                rw [Finset.sum_const, smul_eq_mul]
        have h8_le : 8 * Triples.card ≤ 2 ^ H.card := by
          have hb2 : b * b ≤ 2 ^ (2 * m) := by
            calc b * b ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul hbm hbm
              _ = 2 ^ (2 * m) := by rw [← pow_add, two_mul]
          have h2h : 8 * 2 ^ (2 * m) = 2 ^ h := by
            dsimp only [h]
            calc 8 * 2 ^ (2 * m) = 2 ^ 3 * 2 ^ (2 * m) := by norm_num
              _ = 2 ^ (2 * m + 3) := by rw [← pow_add, add_comm]
          have h2H : 2 ^ h ≤ 2 ^ H.card := Nat.pow_le_pow_right (by omega) hH_ge
          omega
        have hstep : 8 * Triples.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card ≤
            Triples.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card := by
          calc 8 * Triples.card * _
              ≤ 2 ^ H.card * _ := Nat.mul_le_mul_right _ h8_le
            _ ≤ Triples.card * _ := hmul_le
        by_cases hT0 : Triples.card = 0
        · have hEmpty : Triples = ∅ := Finset.card_eq_zero.mp hT0
          have hzero : ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card = 0 := by
            rw [hEmpty, Finset.sum_empty] at hunion_le
            omega
          omega
        · have hTpos : 0 < Triples.card := Nat.pos_of_ne_zero hT0
          have hrew : Triples.card * (8 * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card) ≤
              Triples.card * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card := by
            linarith
          exact Nat.le_of_mul_le_mul_left hrew hTpos
      rw [hbiU_bad, Finset.card_biUnion hdisj_bad, Finset.mul_sum]
      calc ∑ H ∈ Hgood, 8 * ((Finset.univ : Finset Space).filter (fun u => hitSet u = H ∧ badPair u)).card
          ≤ ∑ H ∈ Hgood, ((Finset.univ : Finset Space).filter (fun u => hitSet u = H)).card :=
            Finset.sum_le_sum hperH
        _ = ((Finset.univ : Finset Space).filter (fun u => h ≤ X u)).card := by
            rw [hbiU_all, Finset.card_biUnion hdisj_all]
        _ ≤ R := Finset.card_le_univ _
    have hgood_of_ok : ∀ u : Fin R, h ≤ X (eR u) → ¬ badPair (eR u) →
        read u (fun r => decide (D (cuts u r) π ≠ 0)) = some (pair π) := by
      intro u hge hnotb
      have hH_eq : (Finset.univ : Finset (Fin t)).filter (fun r => decide (D (cuts u r) π ≠ 0) = true) =
          hitSet (eR u) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hitSet, decide_eq_true_eq, cuts]
        exact hD_iff (eR u r)
      dsimp only [read]
      have hge' : h ≤ (hitSet (eR u)).card := hge
      rw [hH_eq, if_neg (show ¬ (hitSet (eR u)).card < h by omega)]
      congr 1
      funext j k
      simp only [pair]
      by_cases hjk_pair : (π j).1 = (π k).1
      · simp only [hjk_pair, decide_true]
        rw [decide_eq_true_iff]
        by_cases hjk : j = k
        · exact Or.inl hjk
        · right
          intro r hr
          have hhit : hit (eR u r) := (Finset.mem_filter.mp hr).2
          have hax := hhit (π j).1
          have hj_eq : j = π.symm ((π j).1, (π j).2) := (π.symm_apply_apply j).symm
          have hk_eq : k = π.symm ((π j).1, (π k).2) := by
            rw [hjk_pair]; exact (π.symm_apply_apply k).symm
          have hsnd_ne : (π j).2 ≠ (π k).2 := fun h2 => hjk (by rw [hj_eq, hk_eq, h2])
          change (j ∈ (eR u r).1) ≠ (k ∈ (eR u r).1)
          rw [hj_eq, hk_eq]
          generalize hc1 : (π j).2 = c1 at hsnd_ne
          generalize hc2 : (π k).2 = c2 at hsnd_ne
          fin_cases c1 <;> fin_cases c2
          · exact (hsnd_ne rfl).elim
          · exact hax
          · exact fun hiff => hax hiff.symm
          · exact (hsnd_ne rfl).elim
      · simp only [hjk_pair, decide_false]
        rw [decide_eq_false_iff_not]
        rintro (rfl | hall)
        · exact hjk_pair rfl
        · apply hnotb
          have hj_eq : j = π.symm ((π j).1, (π j).2) := (π.symm_apply_apply j).symm
          have hk_eq : k = π.symm ((π k).1, (π k).2) := (π.symm_apply_apply k).symm
          have hxor : ∀ (x y : Fin b) (c1 c2 : Fin 2) (r : Fin t), r ∈ hitSet (eR u) →
              ((π.symm (x, c1) ∈ (eR u r).1) ≠ (π.symm (y, c2) ∈ (eR u r).1)) →
              ((π.symm (x, 0) ∈ (eR u r).1) ≠ (π.symm (y, if c1 = 0 then c2 else flipBit c2) ∈ (eR u r).1)) := by
            intro x y c1 c2 r hr hne
            have hx := (Finset.mem_filter.mp hr).2 x
            have hy := (Finset.mem_filter.mp hr).2 y
            fin_cases c1
            · simpa using hne
            · fin_cases c2 <;> simp only [flipBit] <;>
              (by_cases hx0 : π.symm (x, 0) ∈ (eR u r).1 <;>
               by_cases hx1 : π.symm (x, 1) ∈ (eR u r).1 <;>
               by_cases hy0 : π.symm (y, 0) ∈ (eR u r).1 <;>
               by_cases hy1 : π.symm (y, 1) ∈ (eR u r).1 <;>
               simp [hx0, hx1, hy0, hy1] at hx hy hne ⊢)
          rcases lt_or_gt_of_ne hjk_pair with hlt | hgt
          · refine ⟨(π j).1, (π k).1, hlt, if (π j).2 = 0 then (π k).2 else flipBit (π k).2, fun r hr => ?_⟩
            have h1 := hall r hr
            change (j ∈ (eR u r).1) ≠ (k ∈ (eR u r).1) at h1
            rw [hj_eq, hk_eq] at h1
            exact hxor (π j).1 (π k).1 (π j).2 (π k).2 r hr h1
          · refine ⟨(π k).1, (π j).1, hgt, if (π k).2 = 0 then (π j).2 else flipBit (π j).2, fun r hr => ?_⟩
            have h1 := hall r hr
            change (j ∈ (eR u r).1) ≠ (k ∈ (eR u r).1) at h1
            rw [hj_eq, hk_eq] at h1
            exact hxor (π k).1 (π j).1 (π k).2 (π j).2 r hr (fun hiff => h1 hiff.symm)
    let GoodU := (Finset.univ : Finset (Fin R)).filter (fun u =>
      read u (fun r => decide (D (cuts u r) π ≠ 0)) = some (pair π))
    let OkSpace := (Finset.univ : Finset Space).filter (fun u => h ≤ X u ∧ ¬ badPair u)
    have hOk_le : OkSpace.card ≤ GoodU.card := by
      have hsub : OkSpace.map eR.symm.toEmbedding ⊆ GoodU := by
        intro u hu
        rcases Finset.mem_map.mp hu with ⟨v, hv, rfl⟩
        rcases (Finset.mem_filter.mp hv).2 with ⟨hge, hnb⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact hgood_of_ok (eR.symm v) (by simpa using hge) (by simpa using hnb)
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_map] at hle
    have hpart : OkSpace.card + ((Finset.univ : Finset Space).filter (fun u => X u < h)).card +
        ((Finset.univ : Finset Space).filter (fun u => h ≤ X u ∧ badPair u)).card = R := by
      have h1 := card_filter_add_card_filter_not (Finset.univ : Finset Space)
        (fun u => X u < h)
      have h2 := card_filter_add_card_filter_not
        ((Finset.univ : Finset Space).filter (fun u => ¬ X u < h))
        badPair
      have hge_eq : (Finset.univ : Finset Space).filter (fun u => ¬ X u < h) =
          (Finset.univ : Finset Space).filter (fun u => h ≤ X u) := by
        ext u; simp [not_lt]
      have hOk_eq : ((Finset.univ : Finset Space).filter (fun u => ¬ X u < h)).filter (fun u => ¬ badPair u) =
          OkSpace := by
        ext u; simp [OkSpace, not_lt]
      have hBad_eq : ((Finset.univ : Finset Space).filter (fun u => ¬ X u < h)).filter badPair =
          (Finset.univ : Finset Space).filter (fun u => h ≤ X u ∧ badPair u) := by
        ext u; simp [not_lt]
      rw [hOk_eq, hBad_eq] at h2
      have hcard_u : (Finset.univ : Finset Space).card = R := Finset.card_univ
      omega
    change 2 * R ≤ 3 * GoodU.card
    omega
