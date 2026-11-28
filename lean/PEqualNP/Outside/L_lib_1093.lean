import PEqualNP.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace PEqualNP.Outside.L_lib_1093_aux

open scoped BigOperators

def flip2 (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

lemma flip2_invol (i : Fin 2) : flip2 (flip2 i) = i := by
  fin_cases i <;> rfl

def blockPerm {b : ℕ} (σ : Fin b → Bool) : Equiv.Perm (Fin b × Fin 2) where
  toFun p := (p.1, if σ p.1 then flip2 p.2 else p.2)
  invFun p := (p.1, if σ p.1 then flip2 p.2 else p.2)
  left_inv p := by
    ext
    · rfl
    · dsimp only
      split_ifs <;> simp [flip2_invol]
  right_inv p := by
    ext
    · rfl
    · dsimp only
      split_ifs <;> simp [flip2_invol]

lemma blockPerm_injective {b : ℕ} : Function.Injective (@blockPerm b) := by
  intro σ₁ σ₂ h
  funext k
  have hk := congrArg (fun π : Equiv.Perm (Fin b × Fin 2) => (π (k, 0)).2) h
  simp only [blockPerm, Equiv.coe_fn_mk, flip2, ↓reduceIte] at hk
  cases h1 : σ₁ k <;> cases h2 : σ₂ k
  · rfl
  · simp [h1, h2] at hk
  · simp [h1, h2] at hk
  · rfl

lemma blockPerm_preserves {b : ℕ} (σ : Fin b → Bool) (j : Fin b × Fin 2) :
    (blockPerm σ j).1 = j.1 := rfl

lemma perm_eq_blockPerm_of_preserves {b : ℕ} (π : Equiv.Perm (Fin b × Fin 2))
    (h : ∀ j, (π j).1 = j.1) :
    π = blockPerm (fun k => decide (π (k, 0) = (k, 1))) := by
  refine Equiv.ext fun ⟨k, i⟩ => Prod.ext (h (k, i)) ?_
  simp only [blockPerm, Equiv.coe_fn_mk]
  have h0 : (π (k, 0)).1 = k := h (k, 0)
  have h1 : (π (k, 1)).1 = k := h (k, 1)
  have hne : (π (k, 0)).2 ≠ (π (k, 1)).2 := by
    intro heq
    have hp : π (k, 0) = π (k, 1) := Prod.ext (h0.trans h1.symm) heq
    have := π.injective hp
    simp at this
  have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
  fin_cases i
  · rcases hfin2 (π (k, 0)).2 with h00 | h01
    · have hne01 : π (k, 0) ≠ (k, 1) := by intro heq; rw [heq] at h00; simp at h00
      simp [hne01, h00]
    · have heq01 : π (k, 0) = (k, 1) := Prod.ext h0 h01
      simp [heq01, flip2]
  · rcases hfin2 (π (k, 0)).2 with h00 | h01
    · have hne01 : π (k, 0) ≠ (k, 1) := by intro heq; rw [heq] at h00; simp at h00
      have h11 : (π (k, 1)).2 = 1 := by
        rcases hfin2 (π (k, 1)).2 with h10 | h11
        · exact (hne (h00.trans h10.symm)).elim
        · exact h11
      simp [hne01, h11]
    · have heq01 : π (k, 0) = (k, 1) := Prod.ext h0 h01
      have h10 : (π (k, 1)).2 = 0 := by
        rcases hfin2 (π (k, 1)).2 with h10 | h11
        · exact h10
        · exact (hne (h01.trans h11.symm)).elim
      simp [heq01, flip2, h10]

lemma blockPerm_sign {b : ℕ} (σ : Fin b → Bool) :
    ((Equiv.Perm.sign (blockPerm σ) : ℤ) : ℂ) = ∏ k : Fin b, (if σ k then (-1 : ℂ) else 1) := by
  have hind : ∀ S : Finset (Fin b),
      ((Equiv.Perm.sign (blockPerm (fun k => decide (k ∈ S))) : ℤ) : ℂ) =
      ∏ k ∈ S, (-1 : ℂ) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h1 : blockPerm (fun k : Fin b => decide (k ∈ (∅ : Finset (Fin b)))) = 1 := by
        ext ⟨k, i⟩ <;> simp [blockPerm]
      rw [h1, map_one]
      simp
    | insert a s ha ih =>
      have hmul : blockPerm (fun k => decide (k ∈ insert a s)) =
          Equiv.swap (a, (0 : Fin 2)) (a, (1 : Fin 2)) * blockPerm (fun k => decide (k ∈ s)) := by
        ext ⟨k, i⟩
        · by_cases hka : k = a
          · subst hka; fin_cases i <;> simp [blockPerm, flip2, Equiv.swap_apply_def, ha]
          · simp [blockPerm, Equiv.swap_apply_def, hka]
        · by_cases hka : k = a
          · subst hka; fin_cases i <;> simp [blockPerm, flip2, Equiv.swap_apply_def, ha]
          · simp only [blockPerm, Equiv.Perm.mul_apply, Equiv.coe_fn_mk, Finset.mem_insert,
              hka, false_or]
            have hne0 : (k, if decide (k ∈ s) then flip2 i else i) ≠ (a, (0 : Fin 2)) :=
              fun h => hka (congrArg Prod.fst h)
            have hne1 : (k, if decide (k ∈ s) then flip2 i else i) ≠ (a, (1 : Fin 2)) :=
              fun h => hka (congrArg Prod.fst h)
            rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
      rw [hmul, map_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.sign_swap (by simp), ih,
        Finset.prod_insert ha]
      simp
  let S : Finset (Fin b) := Finset.univ.filter (fun k => σ k = true)
  have hσ : σ = fun k => decide (k ∈ S) := by
    funext k; simp [S]
  rw [hσ, hind S]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin b => k ∈ S)]
  have hS : Finset.univ.filter (fun k : Fin b => k ∈ S) = S := by ext k; simp
  rw [hS]
  have h1 : ∏ k ∈ S, (if decide (k ∈ S) = true then (-1 : ℂ) else 1) = ∏ k ∈ S, (-1 : ℂ) :=
    Finset.prod_congr rfl (fun k hk => by simp [hk])
  have h2 : ∏ k ∈ Finset.univ.filter (fun k : Fin b => k ∉ S),
      (if decide (k ∈ S) = true then (-1 : ℂ) else 1) = 1 :=
    Finset.prod_eq_one (fun k hk => by have := (Finset.mem_filter.mp hk).2; simp [this])
  rw [h1, h2, mul_one]

lemma prod_blockPerm {b : ℕ} (M : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) (σ : Fin b → Bool) :
    (∏ j : Fin b × Fin 2, M (blockPerm σ j) j) =
    ∏ k : Fin b, (if σ k then M (k, 1) (k, 0) * M (k, 0) (k, 1) else M (k, 0) (k, 0) * M (k, 1) (k, 1)) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Fin.prod_univ_two]
  cases h : σ k <;> simp [blockPerm, flip2, h]

lemma det_block_diag {b : ℕ} (M : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ)
    (hM : ∀ i j : Fin b × Fin 2, i.1 ≠ j.1 → M i j = 0) :
    Matrix.det M = ∏ k : Fin b, (M (k, 0) (k, 0) * M (k, 1) (k, 1) - M (k, 1) (k, 0) * M (k, 0) (k, 1)) := by
  rw [Matrix.det_apply]
  let P : Finset (Equiv.Perm (Fin b × Fin 2)) :=
    Finset.univ.image (blockPerm (b := b))
  have hzero : ∀ π : Equiv.Perm (Fin b × Fin 2), π ∉ P →
      (Equiv.Perm.sign π : ℂ) * ∏ j : Fin b × Fin 2, M (π j) j = 0 := by
    intro π hnot
    have hex : ∃ j : Fin b × Fin 2, (π j).1 ≠ j.1 := by
      by_contra hall
      push Not at hall
      apply hnot
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (perm_eq_blockPerm_of_preserves π hall).symm⟩
    rcases hex with ⟨j, hj⟩
    have hprod0 : (∏ i : Fin b × Fin 2, M (π i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (hM (π j) j hj)
    simp [hprod0]
  simp only [Units.smul_def, zsmul_eq_mul]
  rw [← Finset.sum_subset (Finset.subset_univ P) (fun π _ hnot => hzero π hnot)]
  rw [Finset.sum_image (fun _ _ _ _ h => blockPerm_injective h)]
  have hterm : ∀ σ : Fin b → Bool,
      ((Equiv.Perm.sign (blockPerm σ) : ℤ) : ℂ) * ∏ j : Fin b × Fin 2, M (blockPerm σ j) j =
      ∏ k : Fin b, (if σ k then -(M (k, 1) (k, 0) * M (k, 0) (k, 1)) else M (k, 0) (k, 0) * M (k, 1) (k, 1)) := by
    intro σ
    rw [blockPerm_sign, prod_blockPerm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    cases σ k <;> simp
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  have hexp : ∀ f g : Fin b → ℂ,
      (∏ k : Fin b, (f k + g k)) = ∑ σ : Fin b → Bool, ∏ k : Fin b, (if σ k then g k else f k) := by
    intro f g
    have h1 := Fintype.prod_sum (fun k (c : Bool) => if c then g k else f k)
    have h2 : (∏ k : Fin b, (f k + g k)) = ∏ k : Fin b, ∑ c : Bool, if c then g k else f k := by
      refine Finset.prod_congr rfl (fun k _ => ?_)
      simp [add_comm]
    rw [h2, h1]
  have hsub := hexp (fun k => M (k, 0) (k, 0) * M (k, 1) (k, 1))
    (fun k => -(M (k, 1) (k, 0) * M (k, 0) (k, 1)))
  simpa [sub_eq_add_neg] using hsub.symm

def mkBlock {b : ℕ} (V : Fin b → ℂ × ℂ) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ :=
  fun i j =>
    if i.1 = j.1 then
      if i.2 = 0 ∧ j.2 = 0 then (V i.1).1
      else if i.2 = 1 ∧ j.2 = 1 then 1
      else if i.2 = 1 ∧ j.2 = 0 then (V i.1).2
      else 1
    else 0

lemma mkBlock_fits {b : ℕ} (V : Fin b → ℂ × ℂ) :
    ∀ i j : Fin b × Fin 2, i.1 ≠ j.1 → mkBlock V i j = 0 := by
  intro i j hne; simp [mkBlock, hne]

lemma mkBlock_diag {b : ℕ} (V : Fin b → ℂ × ℂ) (k : Fin b) :
    mkBlock V (k, 0) (k, 0) * mkBlock V (k, 1) (k, 1) = (V k).1 := by
  simp [mkBlock]

lemma mkBlock_off {b : ℕ} (V : Fin b → ℂ × ℂ) (k : Fin b) :
    mkBlock V (k, 1) (k, 0) * mkBlock V (k, 0) (k, 1) = (V k).2 := by
  simp [mkBlock]

def tensorOf {b : ℕ} (V : Fin b → ℂ × ℂ) (σ : Fin b → Bool) : ℂ :=
  ∏ k : Fin b, (if σ k then (V k).2 else (V k).1)

lemma w_mkBlock_blockPerm {b : ℕ} (V : Fin b → ℂ × ℂ) (σ : Fin b → Bool) :
    (∏ j : Fin b × Fin 2, mkBlock V (blockPerm σ j) j) = tensorOf V σ := by
  rw [prod_blockPerm]
  unfold tensorOf
  refine Finset.prod_congr rfl (fun k _ => ?_)
  cases σ k
  · simp [mkBlock_diag]
  · simp [mkBlock_off]

def scaleBlock0 {b : ℕ} (hb : 0 < b) (c : ℂ) (V : Fin b → ℂ × ℂ) : Fin b → ℂ × ℂ :=
  fun k => if k = ⟨0, hb⟩ then (c * (V k).1, c * (V k).2) else V k

lemma tensorOf_scaleBlock0 {b : ℕ} (hb : 0 < b) (c : ℂ) (V : Fin b → ℂ × ℂ) (σ : Fin b → Bool) :
    tensorOf (scaleBlock0 hb c V) σ = c * tensorOf V σ := by
  unfold tensorOf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨0, hb⟩ : Fin b)),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨0, hb⟩ : Fin b))]
  have hrest : ∏ k ∈ Finset.univ.erase ⟨0, hb⟩,
      (if σ k then (scaleBlock0 hb c V k).2 else (scaleBlock0 hb c V k).1) =
      ∏ k ∈ Finset.univ.erase ⟨0, hb⟩, (if σ k then (V k).2 else (V k).1) :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleBlock0, (Finset.mem_erase.mp hk).1])
  rw [hrest]
  simp only [scaleBlock0, ↓reduceIte]
  cases σ ⟨0, hb⟩ <;> simp <;> ring

lemma eval_mkBlock {b : ℕ} (s : (Fin b × Fin 2) × (Fin b × Fin 2) → ℂ) (V : Fin b → ℂ × ℂ) :
    Matrix.det (fun i j => mkBlock V i j * s (i, j) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) =
    ∏ k : Fin b, ((s ((k, 0), (k, 0)) * s ((k, 1), (k, 1))) * (V k).1 -
      (s ((k, 1), (k, 0)) * s ((k, 0), (k, 1))) * (V k).2) := by
  rw [det_block_diag (fun i j => mkBlock V i j * s (i, j) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ)]
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    simp only [mkBlock, ↓reduceIte, and_self, one_ne_zero, zero_ne_one, and_false, false_and, one_mul]
    ring
  · intro i j hne; simp [mkBlock_fits V i j hne]

lemma eval_scaleBlock0 {b : ℕ} (hb : 0 < b) (c : ℂ)
    (s : (Fin b × Fin 2) × (Fin b × Fin 2) → ℂ) (V : Fin b → ℂ × ℂ) :
    Matrix.det (fun i j => mkBlock (scaleBlock0 hb c V) i j * s (i, j) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) =
    c * Matrix.det (fun i j => mkBlock V i j * s (i, j) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) := by
  rw [eval_mkBlock, eval_mkBlock]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨0, hb⟩ : Fin b)),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨0, hb⟩ : Fin b))]
  have hrest : ∏ k ∈ Finset.univ.erase ⟨0, hb⟩,
      ((s ((k, 0), (k, 0)) * s ((k, 1), (k, 1))) * (scaleBlock0 hb c V k).1 -
        (s ((k, 1), (k, 0)) * s ((k, 0), (k, 1))) * (scaleBlock0 hb c V k).2) =
      ∏ k ∈ Finset.univ.erase ⟨0, hb⟩,
      ((s ((k, 0), (k, 0)) * s ((k, 1), (k, 1))) * (V k).1 -
        (s ((k, 1), (k, 0)) * s ((k, 0), (k, 1))) * (V k).2) :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleBlock0, (Finset.mem_erase.mp hk).1])
  rw [hrest]
  simp only [scaleBlock0, ↓reduceIte]
  ring

lemma tensorOf_ne_of_nonprop {b : ℕ} (hb : 0 < b) (V₁ V₂ : Fin b → ℂ × ℂ) (k0 : Fin b)
    (hV₁ : ∀ k, V₁ k ≠ (0, 0)) (hV₂ : ∀ k, V₂ k ≠ (0, 0))
    (hnp : (V₁ k0).1 * (V₂ k0).2 ≠ (V₁ k0).2 * (V₂ k0).1)
    (c₁ c₂ : ℂ) (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    tensorOf (scaleBlock0 hb c₁ V₁) ≠ tensorOf (scaleBlock0 hb c₂ V₂) := by
  intro heq
  have hpick : ∀ k : Fin b, ∃ c : Bool, (if c then (V₁ k).2 else (V₁ k).1) ≠ 0 := by
    intro k
    by_cases h1 : (V₁ k).1 = 0
    · refine ⟨true, fun h2 => hV₁ k (Prod.ext h1 h2)⟩
    · exact ⟨false, h1⟩
  have hpick2 : ∀ k : Fin b, ∃ c : Bool, (if c then (V₂ k).2 else (V₂ k).1) ≠ 0 := by
    intro k
    by_cases h1 : (V₂ k).1 = 0
    · refine ⟨true, fun h2 => hV₂ k (Prod.ext h1 h2)⟩
    · exact ⟨false, h1⟩
  rcases hc with hc₁ | hc₂
  · choose σ₀ hσ₀ using hpick
    let σF : Fin b → Bool := Function.update σ₀ k0 false
    let σT : Fin b → Bool := Function.update σ₀ k0 true
    have hF := congrFun heq σF
    have hT := congrFun heq σT
    rw [tensorOf_scaleBlock0, tensorOf_scaleBlock0] at hF hT
    let P₁ : ℂ := ∏ k ∈ Finset.univ.erase k0, (if σ₀ k then (V₁ k).2 else (V₁ k).1)
    let P₂ : ℂ := ∏ k ∈ Finset.univ.erase k0, (if σ₀ k then (V₂ k).2 else (V₂ k).1)
    have hP₁ : P₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hσ₀ k)
    have hTF₁ : tensorOf V₁ σF = (V₁ k0).1 * P₁ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σF, Function.update_self, Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    have hTT₁ : tensorOf V₁ σT = (V₁ k0).2 * P₁ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σT, Function.update_self, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    have hTF₂ : tensorOf V₂ σF = (V₂ k0).1 * P₂ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σF, Function.update_self, Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    have hTT₂ : tensorOf V₂ σT = (V₂ k0).2 * P₂ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σT, Function.update_self, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    rw [hTF₁, hTF₂] at hF
    rw [hTT₁, hTT₂] at hT
    by_cases h2 : c₂ * P₂ = 0
    · have hf0 : c₁ * P₁ * (V₁ k0).1 = 0 := by linear_combination hF + (V₂ k0).1 * h2
      have ht0 : c₁ * P₁ * (V₁ k0).2 = 0 := by linear_combination hT + (V₂ k0).2 * h2
      have hlp : c₁ * P₁ ≠ 0 := mul_ne_zero hc₁ hP₁
      exact hV₁ k0 (Prod.ext ((mul_eq_zero.mp hf0).resolve_left hlp) ((mul_eq_zero.mp ht0).resolve_left hlp))
    · have hcross : (c₁ * P₁) * (c₂ * P₂) * ((V₁ k0).1 * (V₂ k0).2 - (V₁ k0).2 * (V₂ k0).1) = 0 := by
        linear_combination (c₂ * P₂ * (V₂ k0).2) * hF - (c₂ * P₂ * (V₂ k0).1) * hT
      have hcoef : (c₁ * P₁) * (c₂ * P₂) ≠ 0 := mul_ne_zero (mul_ne_zero hc₁ hP₁) h2
      exact hnp (sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_left hcoef))
  · choose σ₀ hσ₀ using hpick2
    let σF : Fin b → Bool := Function.update σ₀ k0 false
    let σT : Fin b → Bool := Function.update σ₀ k0 true
    have hF := congrFun heq σF
    have hT := congrFun heq σT
    rw [tensorOf_scaleBlock0, tensorOf_scaleBlock0] at hF hT
    let P₁ : ℂ := ∏ k ∈ Finset.univ.erase k0, (if σ₀ k then (V₁ k).2 else (V₁ k).1)
    let P₂ : ℂ := ∏ k ∈ Finset.univ.erase k0, (if σ₀ k then (V₂ k).2 else (V₂ k).1)
    have hP₂ : P₂ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hσ₀ k)
    have hTF₁ : tensorOf V₁ σF = (V₁ k0).1 * P₁ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σF, Function.update_self, Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    have hTT₁ : tensorOf V₁ σT = (V₁ k0).2 * P₁ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σT, Function.update_self, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    have hTF₂ : tensorOf V₂ σF = (V₂ k0).1 * P₂ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σF, Function.update_self, Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    have hTT₂ : tensorOf V₂ σT = (V₂ k0).2 * P₂ := by
      unfold tensorOf
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0)]
      simp only [σT, Function.update_self, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_erase.mp hk).1])
    rw [hTF₁, hTF₂] at hF
    rw [hTT₁, hTT₂] at hT
    by_cases h1 : c₁ * P₁ = 0
    · have hf0 : c₂ * P₂ * (V₂ k0).1 = 0 := by linear_combination -hF + (V₁ k0).1 * h1
      have ht0 : c₂ * P₂ * (V₂ k0).2 = 0 := by linear_combination -hT + (V₁ k0).2 * h1
      have hlp : c₂ * P₂ ≠ 0 := mul_ne_zero hc₂ hP₂
      exact hV₂ k0 (Prod.ext ((mul_eq_zero.mp hf0).resolve_left hlp) ((mul_eq_zero.mp ht0).resolve_left hlp))
    · have hcross : (c₁ * P₁) * (c₂ * P₂) * ((V₁ k0).1 * (V₂ k0).2 - (V₁ k0).2 * (V₂ k0).1) = 0 := by
        linear_combination (c₂ * P₂ * (V₂ k0).2) * hF - (c₂ * P₂ * (V₂ k0).1) * hT
      have hcoef : (c₁ * P₁) * (c₂ * P₂) ≠ 0 := mul_ne_zero h1 (mul_ne_zero hc₂ hP₂)
      exact hnp (sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_left hcoef))

def evalMulti {b : ℕ} (c : (Fin b → Bool) → ℂ) (x : Fin b → ℂ) : ℂ :=
  ∑ σ : Fin b → Bool, c σ * ∏ k : Fin b, (if σ k then x k else 1)

lemma evalMulti_zero_count_le :
    ∀ (b : ℕ) (S : Finset ℂ) (c : (Fin b → Bool) → ℂ), (∃ σ, c σ ≠ 0) →
    ((Finset.univ : Finset (Fin b → S)).filter (fun x => evalMulti c (fun k => (x k).val) = 0)).card ≤
    b * S.card ^ (b - 1) := by
  intro b
  induction b with
  | zero =>
    intro S c ⟨σ, hσ⟩
    have hempty : (Finset.univ : Finset (Fin 0 → S)).filter
        (fun x => evalMulti c (fun k => (x k).val) = 0) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      unfold evalMulti
      rw [Finset.sum_eq_single σ (fun τ _ hne => (hne (funext (fun k => Fin.elim0 k))).elim)
        (fun h => (h (Finset.mem_univ σ)).elim)]
      simpa using hσ
    rw [hempty, Finset.card_empty]
    omega
  | succ b ih =>
    intro S c ⟨σ0, hσ0⟩
    let c0 : (Fin b → Bool) → ℂ := fun τ => c (Fin.cons false τ)
    let c1 : (Fin b → Bool) → ℂ := fun τ => c (Fin.cons true τ)
    have hsplit : ∀ x : Fin (b + 1) → ℂ,
        evalMulti c x = evalMulti c0 (fun k => x k.succ) + x 0 * evalMulti c1 (fun k => x k.succ) := by
      intro x
      unfold evalMulti
      let e : Bool × (Fin b → Bool) ≃ (Fin (b + 1) → Bool) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun σ => (σ 0, fun k => σ k.succ)
          left_inv := fun ⟨a, τ⟩ => by ext <;> simp
          right_inv := fun σ => by
            funext k
            refine Fin.cases ?_ ?_ k <;> simp }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      rw [Fintype.sum_bool, add_comm]
      congr 1
      · refine Finset.sum_congr rfl (fun τ _ => ?_)
        simp only [e, Equiv.coe_fn_mk, c0, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          Bool.false_eq_true, ↓reduceIte, one_mul]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        simp only [e, Equiv.coe_fn_mk, c1, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          ↓reduceIte]
        ring
    let eX : S × (Fin b → S) ≃ (Fin (b + 1) → S) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun x => (x 0, fun k => x k.succ)
        left_inv := fun ⟨a, y⟩ => by ext <;> simp
        right_inv := fun x => by
          funext k
          refine Fin.cases ?_ ?_ k <;> simp }
    have hcard_eq : ((Finset.univ : Finset (Fin (b + 1) → S)).filter
        (fun x => evalMulti c (fun k => (x k).val) = 0)).card =
        ∑ y : Fin b → S, ((Finset.univ : Finset S).filter
          (fun a => evalMulti c0 (fun k => (y k).val) + a.val * evalMulti c1 (fun k => (y k).val) = 0)).card := by
      simp only [Finset.card_filter]
      rw [← Equiv.sum_comp eX, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun a _ => ?_))
      rw [hsplit]
      simp [eX]
    rw [hcard_eq]
    by_cases hc1 : ∃ τ, c1 τ ≠ 0
    · let Z1 : Finset (Fin b → S) := Finset.univ.filter (fun y => evalMulti c1 (fun k => (y k).val) = 0)
      have hZ1 : Z1.card ≤ b * S.card ^ (b - 1) := ih S c1 hc1
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : Fin b → S => y ∈ Z1)]
      have hpart1 : (∑ y ∈ Finset.univ.filter (fun y : Fin b → S => y ∈ Z1),
          ((Finset.univ : Finset S).filter
            (fun a => evalMulti c0 (fun k => (y k).val) + a.val * evalMulti c1 (fun k => (y k).val) = 0)).card) ≤
          Z1.card * S.card := by
        calc
          _ ≤ ∑ _y ∈ Finset.univ.filter (fun y : Fin b → S => y ∈ Z1), S.card :=
            Finset.sum_le_sum (fun y _ => by
              calc _ ≤ (Finset.univ : Finset S).card := Finset.card_filter_le _ _
                _ = S.card := by simp)
          _ = Z1.card * S.card := by simp [Finset.filter_mem_eq_inter]
      have hpart2 : (∑ y ∈ Finset.univ.filter (fun y : Fin b → S => y ∉ Z1),
          ((Finset.univ : Finset S).filter
            (fun a => evalMulti c0 (fun k => (y k).val) + a.val * evalMulti c1 (fun k => (y k).val) = 0)).card) ≤
          S.card ^ b := by
        have hle1 : ∀ y ∈ Finset.univ.filter (fun y : Fin b → S => y ∉ Z1),
            ((Finset.univ : Finset S).filter
              (fun a => evalMulti c0 (fun k => (y k).val) + a.val * evalMulti c1 (fun k => (y k).val) = 0)).card ≤ 1 := by
          intro y hy
          have hne0 : evalMulti c1 (fun k => (y k).val) ≠ 0 := by
            have := (Finset.mem_filter.mp hy).2
            simpa [Z1] using this
          rw [Finset.card_le_one]
          intro a1 ha1 a2 ha2
          have h1 := (Finset.mem_filter.mp ha1).2
          have h2 := (Finset.mem_filter.mp ha2).2
          have hsub : (a1.val - a2.val) * evalMulti c1 (fun k => (y k).val) = 0 := by
            linear_combination h1 - h2
          exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hne0))
        calc
          _ ≤ ∑ _y ∈ Finset.univ.filter (fun y : Fin b → S => y ∉ Z1), 1 := Finset.sum_le_sum hle1
          _ ≤ (Finset.univ : Finset (Fin b → S)).card := by
            simp only [Finset.sum_const, smul_eq_mul, mul_one]
            exact Finset.card_filter_le _ _
          _ = S.card ^ b := by simp
      have hmul : Z1.card * S.card ≤ b * S.card ^ b := by
        cases b with
        | zero => simp at hZ1; simp [hZ1]
        | succ b' =>
          calc
            Z1.card * S.card ≤ ((b' + 1) * S.card ^ b') * S.card := Nat.mul_le_mul_right S.card hZ1
            _ = (b' + 1) * S.card ^ (b' + 1) := by rw [pow_succ]; ring
      have hadd : b * S.card ^ b + S.card ^ b = (b + 1) * S.card ^ b := by ring
      simp only [Nat.add_sub_cancel]
      omega
    · push Not at hc1
      have hc0 : ∃ τ, c0 τ ≠ 0 := by
        refine ⟨fun k => σ0 k.succ, ?_⟩
        by_cases h0 : σ0 0 = true
        · exfalso
          have heq : σ0 = Fin.cons true (fun k => σ0 k.succ) := by
            funext k; refine Fin.cases ?_ ?_ k <;> simp [h0]
          exact hσ0 (heq ▸ hc1 (fun k => σ0 k.succ))
        · have h0f : σ0 0 = false := by cases h' : σ0 0 <;> simp_all
          have heq : σ0 = Fin.cons false (fun k => σ0 k.succ) := by
            funext k; refine Fin.cases ?_ ?_ k <;> simp [h0f]
          exact fun hc => hσ0 (heq ▸ hc)
      have hc1_eval : ∀ y : Fin b → S, evalMulti c1 (fun k => (y k).val) = 0 := by
        intro y; unfold evalMulti; exact Finset.sum_eq_zero (fun τ _ => by simp [hc1 τ])
      let Z0 : Finset (Fin b → S) := Finset.univ.filter (fun y => evalMulti c0 (fun k => (y k).val) = 0)
      have hZ0 : Z0.card ≤ b * S.card ^ (b - 1) := ih S c0 hc0
      have hterm : ∀ y : Fin b → S,
          ((Finset.univ : Finset S).filter
            (fun a => evalMulti c0 (fun k => (y k).val) + a.val * evalMulti c1 (fun k => (y k).val) = 0)).card =
          if y ∈ Z0 then S.card else 0 := by
        intro y
        rw [hc1_eval y]
        simp only [mul_zero, add_zero, Z0, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with h <;> simp [h]
      rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.sum_filter, Finset.sum_const,
        smul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [Nat.add_sub_cancel]
      cases b with
      | zero => simp at hZ0; simp [hZ0]
      | succ b' =>
        calc
          Z0.card * S.card ≤ ((b' + 1) * S.card ^ b') * S.card := Nat.mul_le_mul_right S.card hZ0
          _ = (b' + 1) * S.card ^ (b' + 1) := by rw [pow_succ]; ring
          _ ≤ (b' + 2) * S.card ^ (b' + 1) := Nat.mul_le_mul_right _ (by omega)

lemma multiset_perm_of_map_eq {b : ℕ} {α : Type*} (f g : Fin b → α)
    (h : (Finset.univ : Finset (Fin b)).val.map f = (Finset.univ : Finset (Fin b)).val.map g) :
    ∃ π : Equiv.Perm (Fin b), ∀ k : Fin b, f (π k) = g k := by
  have hind : ∀ (n : ℕ) (f g : Fin n → α),
      (Finset.univ : Finset (Fin n)).val.map f = (Finset.univ : Finset (Fin n)).val.map g →
      ∃ π : Equiv.Perm (Fin n), ∀ k : Fin n, f (π k) = g k := by
    intro n
    induction n with
    | zero => intro f g _; exact ⟨Equiv.refl _, fun k => Fin.elim0 k⟩
    | succ n ih =>
      intro f g hfg
      have hmem : g 0 ∈ (Finset.univ : Finset (Fin (n + 1))).val.map f := by
        rw [hfg]; exact Multiset.mem_map.mpr ⟨(0 : Fin (n + 1)), Finset.mem_univ (0 : Fin (n + 1)), rfl⟩
      rcases Multiset.mem_map.mp hmem with ⟨k0, _, hk0⟩
      let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 k0
      have hτ0 : f (τ 0) = g 0 := by simp [τ, hk0]
      let f' : Fin n → α := fun i => f (τ i.succ)
      let g' : Fin n → α := fun i => g i.succ
      have hmap_succ : ∀ hfun : Fin (n + 1) → α,
          (Finset.univ : Finset (Fin (n + 1))).val.map hfun =
          hfun 0 ::ₘ (Finset.univ : Finset (Fin n)).val.map (fun i => hfun i.succ) := by
        intro hfun
        have huniv : (Finset.univ : Finset (Fin (n + 1))) =
            insert 0 ((Finset.univ : Finset (Fin n)).map ⟨Fin.succ, Fin.succ_injective _⟩) := by
          ext k
          simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk,
            true_and, true_iff]
          refine Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨i, rfl⟩) k
        have hnot : (0 : Fin (n + 1)) ∉ (Finset.univ : Finset (Fin n)).map ⟨Fin.succ, Fin.succ_injective _⟩ := by
          simp
        rw [huniv, Finset.insert_val_of_notMem hnot, Multiset.map_cons, Finset.map_val, Multiset.map_map]
        rfl
      have hτmap : (Finset.univ : Finset (Fin (n + 1))).val.map (fun k => f (τ k)) =
          (Finset.univ : Finset (Fin (n + 1))).val.map f := by
        have : (Finset.univ : Finset (Fin (n + 1))).val.map τ = (Finset.univ : Finset (Fin (n + 1))).val := by
          have h1 : (Finset.univ : Finset (Fin (n + 1))).map τ.toEmbedding = Finset.univ := by
            ext k; simp only [Finset.mem_map, Finset.mem_univ, true_and, Equiv.coe_toEmbedding, iff_true]
            exact ⟨τ.symm k, τ.apply_symm_apply k⟩
          simpa [Finset.map_val] using congrArg Finset.val h1
        change (Finset.univ : Finset (Fin (n + 1))).val.map (f ∘ τ) = _
        rw [← Multiset.map_map, this]
      have hfg' : (Finset.univ : Finset (Fin n)).val.map f' = (Finset.univ : Finset (Fin n)).val.map g' := by
        have h1 := hτmap.trans hfg
        rw [hmap_succ (fun k => f (τ k)), hmap_succ g, hτ0] at h1
        exact Multiset.cons_inj_right _ |>.mp h1
      rcases ih f' g' hfg' with ⟨π', hπ'⟩
      let π : Equiv.Perm (Fin (n + 1)) :=
        { toFun := Fin.cases 0 (fun i => (π' i).succ)
          invFun := Fin.cases 0 (fun i => (π'.symm i).succ)
          left_inv := fun k => by refine Fin.cases ?_ ?_ k <;> simp
          right_inv := fun k => by refine Fin.cases ?_ ?_ k <;> simp }
      refine ⟨π.trans τ, fun k => ?_⟩
      refine Fin.cases ?_ ?_ k
      · simpa [π] using hτ0
      · intro i; simpa [π, f', g'] using hπ' i
  exact hind b f g h

lemma poly_linear_factor_perm {b : ℕ} (VA VB : Fin b → ℂ × ℂ)
    (hpoly : (∏ k : Fin b, (Polynomial.C (VA k).1 - Polynomial.C (VA k).2 * Polynomial.X)) =
             (∏ k : Fin b, (Polynomial.C (VB k).1 - Polynomial.C (VB k).2 * Polynomial.X)))
    (hnz : (∏ k : Fin b, (Polynomial.C (VA k).1 - Polynomial.C (VA k).2 * Polynomial.X)) ≠ 0) :
    ∃ π : Equiv.Perm (Fin b), ∀ σ : Fin b → Bool, tensorOf VB σ = tensorOf VA (σ ∘ π) := by
  have hVA_nz : ∀ k : Fin b, Polynomial.C (VA k).1 - Polynomial.C (VA k).2 * Polynomial.X ≠ 0 := by
    intro k hk
    exact hnz (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  have hVB_nz : ∀ k : Fin b, Polynomial.C (VB k).1 - Polynomial.C (VB k).2 * Polynomial.X ≠ 0 := by
    intro k hk
    rw [hpoly] at hnz
    exact hnz (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  let rootOpt : (ℂ × ℂ) → Option ℂ := fun v => if v.2 = 0 then none else some (v.1 / v.2)
  have hroots_of : ∀ (V : Fin b → ℂ × ℂ),
      (∀ k, Polynomial.C (V k).1 - Polynomial.C (V k).2 * Polynomial.X ≠ 0) →
      (∏ k : Fin b, (Polynomial.C (V k).1 - Polynomial.C (V k).2 * Polynomial.X)).roots =
      ((Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 ≠ 0)).map (fun k => (V k).1 / (V k).2) := by
    intro V hV
    have hprod_roots : ∀ S : Finset (Fin b),
        (∏ k ∈ S, (Polynomial.C (V k).1 - Polynomial.C (V k).2 * Polynomial.X)).roots =
        (S.val.filter (fun k => (V k).2 ≠ 0)).map (fun k => (V k).1 / (V k).2) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hpa : Polynomial.C (V a).1 - Polynomial.C (V a).2 * Polynomial.X ≠ 0 := hV a
        have hps : (∏ k ∈ s, (Polynomial.C (V k).1 - Polynomial.C (V k).2 * Polynomial.X)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun k _ => hV k)
        rw [Finset.prod_insert ha, Polynomial.roots_mul (mul_ne_zero hpa hps), ih,
          Finset.insert_val_of_notMem ha, Multiset.filter_cons]
        by_cases hq : (V a).2 = 0
        · simp only [hq, ne_eq, not_true_eq_false, ↓reduceIte, map_zero, zero_mul, sub_zero,
            Polynomial.roots_C, zero_add]
        · simp only [hq, ne_eq, not_false_eq_true, ↓reduceIte, Multiset.map_cons]
          have hlin : Polynomial.C (V a).1 - Polynomial.C (V a).2 * Polynomial.X =
              Polynomial.C (-(V a).2) * (Polynomial.X - Polynomial.C ((V a).1 / (V a).2)) := by
            rw [mul_sub, ← Polynomial.C_mul]
            have : -(V a).2 * ((V a).1 / (V a).2) = -(V a).1 := by field_simp
            rw [this, map_neg, map_neg]
            ring
          rw [hlin, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hq), Polynomial.roots_X_sub_C]
          simp
    exact hprod_roots Finset.univ
  have hroots_eq :
      ((Finset.univ : Finset (Fin b)).val.filter (fun k => (VA k).2 ≠ 0)).map (fun k => (VA k).1 / (VA k).2) =
      ((Finset.univ : Finset (Fin b)).val.filter (fun k => (VB k).2 ≠ 0)).map (fun k => (VB k).1 / (VB k).2) := by
    rw [← hroots_of VA hVA_nz, ← hroots_of VB hVB_nz, hpoly]
  have hopt_eq :
      (Finset.univ : Finset (Fin b)).val.map (fun k => rootOpt (VA k)) =
      (Finset.univ : Finset (Fin b)).val.map (fun k => rootOpt (VB k)) := by
    have hdecomp : ∀ V : Fin b → ℂ × ℂ,
        (Finset.univ : Finset (Fin b)).val.map (fun k => rootOpt (V k)) =
        (((Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 ≠ 0)).map (fun k => (V k).1 / (V k).2)).map some +
        Multiset.replicate ((Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 = 0)).card none := by
      intro V
      have hpart := (Multiset.filter_add_not (fun k : Fin b => (V k).2 ≠ 0) (Finset.univ : Finset (Fin b)).val).symm
      conv_lhs => rw [hpart]
      rw [Multiset.map_add]
      congr 1
      · rw [Multiset.map_map]
        refine Multiset.map_congr rfl (fun k hk => ?_)
        have hne := (Multiset.mem_filter.mp hk).2
        simp [rootOpt, hne]
      · have hfilt : (Finset.univ : Finset (Fin b)).val.filter (fun k => ¬ (V k).2 ≠ 0) =
            (Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 = 0) := by
          simp only [ne_eq, not_not]
        rw [hfilt]
        have hall : ∀ x ∈ ((Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 = 0)).map
            (fun k => rootOpt (V k)), x = none := by
          intro x hx
          rcases Multiset.mem_map.mp hx with ⟨k, hk, rfl⟩
          simp [rootOpt, (Multiset.mem_filter.mp hk).2]
        have hrep : ((Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 = 0)).map
            (fun k => rootOpt (V k)) =
            Multiset.replicate ((Finset.univ : Finset (Fin b)).val.filter (fun k => (V k).2 = 0)).card none :=
          Multiset.eq_replicate.mpr ⟨by simp, hall⟩
        rw [hrep]
    rw [hdecomp VA, hdecomp VB, hroots_eq]
    have hcard_nz : ((Finset.univ : Finset (Fin b)).val.filter (fun k => (VA k).2 ≠ 0)).card =
        ((Finset.univ : Finset (Fin b)).val.filter (fun k => (VB k).2 ≠ 0)).card := by
      have := congrArg Multiset.card hroots_eq
      simpa using this
    have hcard_zA := congrArg Multiset.card
      (Multiset.filter_add_not (fun k : Fin b => (VA k).2 ≠ 0) (Finset.univ : Finset (Fin b)).val)
    have hcard_zB := congrArg Multiset.card
      (Multiset.filter_add_not (fun k : Fin b => (VB k).2 ≠ 0) (Finset.univ : Finset (Fin b)).val)
    simp only [Multiset.card_add] at hcard_zA hcard_zB
    have hfiltA : (Finset.univ : Finset (Fin b)).val.filter (fun k => ¬ (VA k).2 ≠ 0) =
        (Finset.univ : Finset (Fin b)).val.filter (fun k => (VA k).2 = 0) := by
      simp only [ne_eq, not_not]
    have hfiltB : (Finset.univ : Finset (Fin b)).val.filter (fun k => ¬ (VB k).2 ≠ 0) =
        (Finset.univ : Finset (Fin b)).val.filter (fun k => (VB k).2 = 0) := by
      simp only [ne_eq, not_not]
    rw [hfiltA] at hcard_zA
    rw [hfiltB] at hcard_zB
    have hcard_eq : ((Finset.univ : Finset (Fin b)).val.filter (fun k => (VA k).2 = 0)).card =
        ((Finset.univ : Finset (Fin b)).val.filter (fun k => (VB k).2 = 0)).card := by omega
    rw [hcard_eq]
  rcases multiset_perm_of_map_eq (fun k => rootOpt (VB k)) (fun k => rootOpt (VA k)) hopt_eq.symm with ⟨π, hπ⟩
  have hscale : ∀ k : Fin b, ∃ c : ℂ, (VB (π k)).1 = c * (VA k).1 ∧ (VB (π k)).2 = c * (VA k).2 := by
    intro k
    have hk := hπ k
    simp only [rootOpt] at hk
    by_cases hqA : (VA k).2 = 0
    · simp only [hqA, ↓reduceIte] at hk
      have hqB : (VB (π k)).2 = 0 := by
        by_contra hne; simp [hne] at hk
      have hpA : (VA k).1 ≠ 0 := by
        intro hp0; exact hVA_nz k (by simp [hp0, hqA])
      refine ⟨(VB (π k)).1 / (VA k).1, ?_, ?_⟩
      · field_simp
      · simp [hqA, hqB]
    · simp only [hqA, ↓reduceIte] at hk
      have hqB : (VB (π k)).2 ≠ 0 := by
        intro h0; simp [h0] at hk
      simp only [hqB, ↓reduceIte, Option.some.injEq] at hk
      refine ⟨(VB (π k)).2 / (VA k).2, ?_, ?_⟩
      · have : (VB (π k)).1 / (VB (π k)).2 = (VA k).1 / (VA k).2 := hk
        field_simp at this ⊢
        linear_combination this
      · field_simp
  choose c hc1 hc2 using hscale
  have hprod_c : (∏ k : Fin b, c k) = 1 := by
    have hPB : (∏ k : Fin b, (Polynomial.C (VB k).1 - Polynomial.C (VB k).2 * Polynomial.X)) =
        Polynomial.C (∏ k : Fin b, c k) *
        (∏ k : Fin b, (Polynomial.C (VA k).1 - Polynomial.C (VA k).2 * Polynomial.X)) := by
      rw [← Equiv.prod_comp π, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      rw [hc1 k, hc2 k, map_mul, map_mul]
      ring
    rw [← hpoly] at hPB
    have h1 : (Polynomial.C (∏ k : Fin b, c k) - 1) *
        (∏ k : Fin b, (Polynomial.C (VA k).1 - Polynomial.C (VA k).2 * Polynomial.X)) = 0 := by
      linear_combination -hPB
    have hc1' : Polynomial.C (∏ k : Fin b, c k) - 1 = 0 := (mul_eq_zero.mp h1).resolve_right hnz
    have hc2' : Polynomial.C (∏ k : Fin b, c k) = Polynomial.C (1 : ℂ) := by
      simpa using sub_eq_zero.mp hc1'
    exact Polynomial.C_injective hc2'
  refine ⟨π, fun σ => ?_⟩
  unfold tensorOf
  rw [← Equiv.prod_comp π]
  have hterm : ∀ k : Fin b,
      (if σ (π k) then (VB (π k)).2 else (VB (π k)).1) =
      c k * (if σ (π k) then (VA k).2 else (VA k).1) := by
    intro k
    cases σ (π k)
    · simp [hc1 k]
    · simp [hc2 k]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib, hprod_c, one_mul]
  rfl

end PEqualNP.Outside.L_lib_1093_aux

theorem PEqualNP.Outside.L_lib_1093 :
  ∀ blockCount : ℕ, 2 ≤ blockCount →
  let I := Fin blockCount × Fin 2
  let E := I × I
  let S := E → ℂ
  let W := Equiv.Perm I → ℂ
  let fits := fun (A : Matrix I I ℂ) => ∀ i j : I, i.1 ≠ j.1 → A i j = 0
  let w := fun (A : Matrix I I ℂ) (π : Equiv.Perm I) => ∏ j : I, A (π j) j
  let eval := fun (s : S) (A : Matrix I I ℂ) =>
    Matrix.det (fun i j => A i j * s (i,j) : Matrix I I ℂ)
  (∀ ask : ℕ → List ℂ → S,
    let run := fun (A : Matrix I I ℂ) => (List.range (blockCount+1)).foldl
      (fun h j => eval (ask j h) A :: h) ([] : List ℂ)
    ∃ A B : Matrix I I ℂ, fits A ∧ fits B ∧ run A = run B ∧ w A ≠ w B) ∧
  ∀ (q : ℕ) (ζ : ℂ), blockCount < q → blockCount * Nat.choose blockCount.factorial 2 < q → IsPrimitiveRoot ζ q →
    let T := E → Fin q
    let phase := fun (t : T) (e : E) => ζ ^ (t e).val
    ∃ (front : Fin (blockCount+1) → T) (last : (Fin (blockCount+1) → ℂ) → T) (read : (Fin (blockCount+1) → ℂ) → ℂ → W),
      ∀ A : Matrix I I ℂ, fits A →
        let y := fun h : Fin (blockCount+1) => eval (phase (front h)) A
        read y (eval (phase (last y)) A) = w A := by
  intro b hb I E S W fits w eval
  have hb0 : 0 < b := by omega
  constructor
  · intro ask run
    let sR : ℕ → S := fun r => ask r (List.replicate r 0)
    have hrun_eq : ∀ A : Matrix I I ℂ,
        (∀ r : Fin b, eval (sR r.val) A = 0) →
        run A = eval (sR b) A :: List.replicate b 0 := by
      intro A hkill
      have hind : ∀ n : ℕ, n ≤ b →
          (List.range n).foldl (fun h j => eval (ask j h) A :: h) ([] : List ℂ) =
          List.replicate n 0 := by
        intro n
        induction n with
        | zero => intro _; rfl
        | succ n ih =>
          intro hle
          rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
          have h0 : eval (ask n (List.replicate n 0)) A = 0 := hkill ⟨n, by omega⟩
          rw [h0, List.replicate_succ]
      unfold run
      rw [List.range_succ, List.foldl_append, hind b (le_refl _), List.foldl_cons, List.foldl_nil]
    have hdefeat : ∀ (V₁ V₂ : Fin b → ℂ × ℂ) (k0 : Fin b),
        (∀ k, V₁ k ≠ (0, 0)) → (∀ k, V₂ k ≠ (0, 0)) →
        (V₁ k0).1 * (V₂ k0).2 ≠ (V₁ k0).2 * (V₂ k0).1 →
        (∀ r : Fin b, eval (sR r.val) (PEqualNP.Outside.L_lib_1093_aux.mkBlock V₁) = 0) →
        (∀ r : Fin b, eval (sR r.val) (PEqualNP.Outside.L_lib_1093_aux.mkBlock V₂) = 0) →
        ∃ A B : Matrix I I ℂ, fits A ∧ fits B ∧ run A = run B ∧ w A ≠ w B := by
      intro V₁ V₂ k0 hV₁ hV₂ hnp hk₁ hk₂
      set e₁ := eval (sR b) (PEqualNP.Outside.L_lib_1093_aux.mkBlock V₁)
      set e₂ := eval (sR b) (PEqualNP.Outside.L_lib_1093_aux.mkBlock V₂)
      have hex_lam : ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ * e₁ = c₂ * e₂ := by
        by_cases h1 : e₁ = 0
        · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h1]⟩
        · by_cases h2 : e₂ = 0
          · exact ⟨0, 1, Or.inr one_ne_zero, by simp [h2]⟩
          · exact ⟨e₂, e₁, Or.inl h2, mul_comm e₂ e₁⟩
      rcases hex_lam with ⟨c₁, c₂, hc, hlam_eq⟩
      let A := PEqualNP.Outside.L_lib_1093_aux.mkBlock (PEqualNP.Outside.L_lib_1093_aux.scaleBlock0 hb0 c₁ V₁)
      let B := PEqualNP.Outside.L_lib_1093_aux.mkBlock (PEqualNP.Outside.L_lib_1093_aux.scaleBlock0 hb0 c₂ V₂)
      refine ⟨A, B, PEqualNP.Outside.L_lib_1093_aux.mkBlock_fits _,
        PEqualNP.Outside.L_lib_1093_aux.mkBlock_fits _, ?_, ?_⟩
      · have hkA : ∀ r : Fin b, eval (sR r.val) A = 0 := fun r => by
          change Matrix.det (fun i j => PEqualNP.Outside.L_lib_1093_aux.mkBlock
            (PEqualNP.Outside.L_lib_1093_aux.scaleBlock0 hb0 c₁ V₁) i j * sR r.val (i, j) :
            Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) = 0
          rw [PEqualNP.Outside.L_lib_1093_aux.eval_scaleBlock0 hb0 c₁ (sR r.val) V₁]
          change c₁ * eval (sR r.val) (PEqualNP.Outside.L_lib_1093_aux.mkBlock V₁) = 0
          rw [hk₁ r, mul_zero]
        have hkB : ∀ r : Fin b, eval (sR r.val) B = 0 := fun r => by
          change Matrix.det (fun i j => PEqualNP.Outside.L_lib_1093_aux.mkBlock
            (PEqualNP.Outside.L_lib_1093_aux.scaleBlock0 hb0 c₂ V₂) i j * sR r.val (i, j) :
            Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) = 0
          rw [PEqualNP.Outside.L_lib_1093_aux.eval_scaleBlock0 hb0 c₂ (sR r.val) V₂]
          change c₂ * eval (sR r.val) (PEqualNP.Outside.L_lib_1093_aux.mkBlock V₂) = 0
          rw [hk₂ r, mul_zero]
        rw [hrun_eq A hkA, hrun_eq B hkB]
        congr 1
        change Matrix.det _ = Matrix.det _
        rw [PEqualNP.Outside.L_lib_1093_aux.eval_scaleBlock0 hb0 c₁ (sR b) V₁,
          PEqualNP.Outside.L_lib_1093_aux.eval_scaleBlock0 hb0 c₂ (sR b) V₂]
        exact hlam_eq
      · intro hw_eq
        have ht_ne := PEqualNP.Outside.L_lib_1093_aux.tensorOf_ne_of_nonprop hb0 V₁ V₂ k0 hV₁ hV₂ hnp c₁ c₂ hc
        apply ht_ne
        funext σ
        rw [← PEqualNP.Outside.L_lib_1093_aux.w_mkBlock_blockPerm,
          ← PEqualNP.Outside.L_lib_1093_aux.w_mkBlock_blockPerm]
        exact congrFun hw_eq (PEqualNP.Outside.L_lib_1093_aux.blockPerm σ)
    let α : Fin b → Fin b → ℂ := fun r k => sR r.val ((k, 0), (k, 0)) * sR r.val ((k, 1), (k, 1))
    let β : Fin b → Fin b → ℂ := fun r k => sR r.val ((k, 1), (k, 0)) * sR r.val ((k, 0), (k, 1))
    let u : Fin b → Fin b → ℂ × ℂ := fun r k =>
      if α r k = 0 ∧ β r k = 0 then (1, 0) else (β r k, α r k)
    have hu_nz : ∀ r k : Fin b, u r k ≠ (0, 0) := by
      intro r k
      simp only [u]
      split_ifs with h
      · simp
      · intro h0
        have h1 : β r k = 0 := congrArg Prod.fst h0
        have h2 : α r k = 0 := congrArg Prod.snd h0
        exact h ⟨h2, h1⟩
    have hu_kill : ∀ r k : Fin b, α r k * (u r k).1 - β r k * (u r k).2 = 0 := by
      intro r k
      simp only [u]
      split_ifs with h
      · simp [h.1, h.2]
      · ring
    by_cases hnp_ex : ∃ (k0 r1 r2 : Fin b), (u r1 k0).1 * (u r2 k0).2 ≠ (u r1 k0).2 * (u r2 k0).1
    · rcases hnp_ex with ⟨k0, r1, r2, hnp⟩
      let π₁ : Equiv.Perm (Fin b) := Equiv.swap k0 r1
      let π₂ : Equiv.Perm (Fin b) := Equiv.swap k0 r2
      let V₁ : Fin b → ℂ × ℂ := fun k => u (π₁ k) k
      let V₂ : Fin b → ℂ × ℂ := fun k => u (π₂ k) k
      have hV₁_k0 : V₁ k0 = u r1 k0 := by simp [V₁, π₁]
      have hV₂_k0 : V₂ k0 = u r2 k0 := by simp [V₂, π₂]
      refine hdefeat V₁ V₂ k0 (fun k => hu_nz _ k) (fun k => hu_nz _ k)
        (by rw [hV₁_k0, hV₂_k0]; exact hnp) ?_ ?_
      · intro r
        change Matrix.det _ = 0
        rw [PEqualNP.Outside.L_lib_1093_aux.eval_mkBlock]
        refine Finset.prod_eq_zero (Finset.mem_univ (π₁.symm r)) ?_
        simpa [V₁, α, β] using hu_kill r (π₁.symm r)
      · intro r
        change Matrix.det _ = 0
        rw [PEqualNP.Outside.L_lib_1093_aux.eval_mkBlock]
        refine Finset.prod_eq_zero (Finset.mem_univ (π₂.symm r)) ?_
        simpa [V₂, α, β] using hu_kill r (π₂.symm r)
    · push Not at hnp_ex
      let k0 : Fin b := ⟨0, hb0⟩
      let k1 : Fin b := ⟨1, by omega⟩
      have hk01 : k0 ≠ k1 := by intro h; have := congrArg Fin.val h; simp [k0, k1] at this
      have hu0_kill_all : ∀ r : Fin b, α r k0 * (u k0 k0).1 - β r k0 * (u k0 k0).2 = 0 := by
        intro r
        have hprop := hnp_ex k0 k0 r
        by_cases hz : α r k0 = 0 ∧ β r k0 = 0
        · simp [hz.1, hz.2]
        · have hur : u r k0 = (β r k0, α r k0) := by simp [u, hz]
          rw [hur] at hprop
          exact sub_eq_zero.mpr (by linear_combination hprop)
      let V₁ : Fin b → ℂ × ℂ := fun k => if k = k0 then u k0 k0 else (1, 0)
      let V₂ : Fin b → ℂ × ℂ := fun k => if k = k0 then u k0 k0 else if k = k1 then (0, 1) else (1, 0)
      have hV₁_nz : ∀ k, V₁ k ≠ (0, 0) := fun k => by
        simp only [V₁]; split_ifs
        · exact hu_nz k0 k0
        · simp
      have hV₂_nz : ∀ k, V₂ k ≠ (0, 0) := fun k => by
        simp only [V₂]; split_ifs
        · exact hu_nz k0 k0
        · simp
        · simp
      have hnp1 : (V₁ k1).1 * (V₂ k1).2 ≠ (V₁ k1).2 * (V₂ k1).1 := by
        simp [V₁, V₂, Ne.symm hk01]
      refine hdefeat V₁ V₂ k1 hV₁_nz hV₂_nz hnp1 ?_ ?_
      · intro r
        change Matrix.det _ = 0
        rw [PEqualNP.Outside.L_lib_1093_aux.eval_mkBlock]
        refine Finset.prod_eq_zero (Finset.mem_univ k0) ?_
        simpa [V₁, α, β] using hu0_kill_all r
      · intro r
        change Matrix.det _ = 0
        rw [PEqualNP.Outside.L_lib_1093_aux.eval_mkBlock]
        refine Finset.prod_eq_zero (Finset.mem_univ k0) ?_
        simpa [V₂, α, β] using hu0_kill_all r
  · intro q ζ hbq hqbound hζ T phase
    have hq0 : 0 < q := by omega
    let front : Fin (b + 1) → T := fun h e =>
      if e.1.1 = e.2.1 ∧ e.1.2 = 1 ∧ e.2.2 = 0 then ⟨h.val, by have := h.isLt; omega⟩ else ⟨0, hq0⟩
    let diagQuery : (Fin b → Fin q) → T := fun exp e =>
      if e.1.1 = e.2.1 ∧ e.1.2 = 1 ∧ e.2.2 = 0 then exp e.1.1 else ⟨0, hq0⟩
    let vecOf : Matrix I I ℂ → Fin b → ℂ × ℂ := fun A k =>
      (A (k, 0) (k, 0) * A (k, 1) (k, 1), A (k, 1) (k, 0) * A (k, 0) (k, 1))
    let polyOf : Matrix I I ℂ → Polynomial ℂ := fun A =>
      ∏ k : Fin b, (Polynomial.C (vecOf A k).1 - Polynomial.C (vecOf A k).2 * Polynomial.X)
    have hfront_eval : ∀ (A : Matrix I I ℂ), fits A → ∀ h : Fin (b + 1),
        eval (phase (front h)) A = (polyOf A).eval (ζ ^ h.val) := by
      intro A hA h
      change Matrix.det (fun i j => A i j * phase (front h) (i, j) :
        Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) = _
      rw [PEqualNP.Outside.L_lib_1093_aux.det_block_diag
        (fun i j => A i j * phase (front h) (i, j) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ)
        (fun i j hne => by simp [hA i j hne])]
      simp only [polyOf, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, vecOf]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      simp only [phase, front, true_and, and_true, one_ne_zero, zero_ne_one, and_false, false_and,
        ↓reduceIte, pow_zero, mul_one]
      ring
    have hpoly_deg : ∀ A : Matrix I I ℂ, (polyOf A).natDegree ≤ b := by
      intro A
      have h1 : ∀ k : Fin b,
          (Polynomial.C (vecOf A k).1 - Polynomial.C (vecOf A k).2 * Polynomial.X).natDegree ≤ 1 := by
        intro k
        calc
          (Polynomial.C (vecOf A k).1 - Polynomial.C (vecOf A k).2 * Polynomial.X).natDegree
            ≤ max (Polynomial.C (vecOf A k).1).natDegree (Polynomial.C (vecOf A k).2 * Polynomial.X).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ max 0 1 := max_le_max (by simp) (by
            calc
              (Polynomial.C (vecOf A k).2 * Polynomial.X).natDegree
                ≤ (Polynomial.C (vecOf A k).2).natDegree + Polynomial.X.natDegree := Polynomial.natDegree_mul_le
              _ ≤ 0 + 1 := by simp)
          _ = 1 := by simp
      have h2 : (∑ k : Fin b,
          (Polynomial.C (vecOf A k).1 - Polynomial.C (vecOf A k).2 * Polynomial.X).natDegree) ≤
          ∑ _k : Fin b, (1 : ℕ) := Finset.sum_le_sum (fun k _ => h1 k)
      have h3 : (∑ _k : Fin b, (1 : ℕ)) = b := by simp
      exact le_trans (Polynomial.natDegree_prod_le _ _) (le_trans h2 (le_of_eq h3))
    have hpoly_eq_of_front : ∀ (A B : Matrix I I ℂ), fits A → fits B →
        (∀ h : Fin (b + 1), eval (phase (front h)) A = eval (phase (front h)) B) →
        polyOf A = polyOf B := by
      intro A B hA hB heq
      by_contra hne
      have hdiff_nz : polyOf A - polyOf B ≠ 0 := sub_ne_zero.mpr hne
      have hdeg : (polyOf A - polyOf B).natDegree ≤ b :=
        le_trans (Polynomial.natDegree_sub_le _ _) (max_le (hpoly_deg A) (hpoly_deg B))
      let pts : Finset ℂ := (Finset.univ : Finset (Fin (b + 1))).image (fun h : Fin (b + 1) => ζ ^ h.val)
      have hpts_inj : Function.Injective (fun h : Fin (b + 1) => ζ ^ h.val) := by
        intro h1 h2 hh
        have := hζ.injOn_pow
          (Finset.mem_coe.mpr (Finset.mem_range.mpr (by have := h1.isLt; omega)))
          (Finset.mem_coe.mpr (Finset.mem_range.mpr (by have := h2.isLt; omega))) hh
        exact Fin.ext this
      have hpts_card : pts.card = b + 1 := by
        rw [Finset.card_image_of_injective _ hpts_inj, Finset.card_univ, Fintype.card_fin]
      have hsub : pts.val ⊆ (polyOf A - polyOf B).roots := by
        intro z hz
        have hz' : z ∈ pts := hz
        rcases Finset.mem_image.mp hz' with ⟨h, _, rfl⟩
        rw [Polynomial.mem_roots hdiff_nz, Polynomial.IsRoot.def, Polynomial.eval_sub,
          ← hfront_eval A hA h, ← hfront_eval B hB h, heq h, sub_self]
      have hcard_le : pts.card ≤ (polyOf A - polyOf B).roots.card :=
        Multiset.card_le_card (Multiset.le_iff_subset pts.nodup |>.mpr hsub)
      have hroots_le := Polynomial.card_roots' (polyOf A - polyOf B)
      omega
    have hdiag_eval : ∀ (A : Matrix I I ℂ), fits A → ∀ exp : Fin b → Fin q,
        eval (phase (diagQuery exp)) A =
        PEqualNP.Outside.L_lib_1093_aux.evalMulti
          (fun σ => (if (Finset.univ.filter (fun k => σ k = true)).card % 2 = 0 then (1 : ℂ) else -1) *
            PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf A) σ)
          (fun k => ζ ^ (exp k).val) := by
      intro A hA exp
      change Matrix.det (fun i j => A i j * phase (diagQuery exp) (i, j) :
        Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) = _
      rw [PEqualNP.Outside.L_lib_1093_aux.det_block_diag
        (fun i j => A i j * phase (diagQuery exp) (i, j) : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ)
        (fun i j hne => by simp [hA i j hne])]
      have hexp : ∀ f g : Fin b → ℂ,
          (∏ k : Fin b, (f k - g k)) =
          ∑ σ : Fin b → Bool, ∏ k : Fin b, (if σ k then -(g k) else f k) := by
        intro f g
        have h1 := Fintype.prod_sum (fun k (c : Bool) => if c then -(g k) else f k)
        have h2 : (∏ k : Fin b, (f k - g k)) = ∏ k : Fin b, ∑ c : Bool, if c then -(g k) else f k := by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          simp [sub_eq_add_neg, add_comm]
        rw [h2, h1]
      have hblk : ∀ k : Fin b,
          A (k, 0) (k, 0) * phase (diagQuery exp) ((k, 0), (k, 0)) *
            (A (k, 1) (k, 1) * phase (diagQuery exp) ((k, 1), (k, 1))) -
          A (k, 1) (k, 0) * phase (diagQuery exp) ((k, 1), (k, 0)) *
            (A (k, 0) (k, 1) * phase (diagQuery exp) ((k, 0), (k, 1))) =
          (vecOf A k).1 - (vecOf A k).2 * ζ ^ (exp k).val := by
        intro k
        simp only [phase, diagQuery, vecOf, true_and, and_true, one_ne_zero, zero_ne_one,
          and_false, false_and, ↓reduceIte, pow_zero, mul_one]
        ring
      rw [Finset.prod_congr rfl (fun k _ => hblk k), hexp]
      unfold PEqualNP.Outside.L_lib_1093_aux.evalMulti PEqualNP.Outside.L_lib_1093_aux.tensorOf
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      have hsign : (∏ k : Fin b, (if σ k then (-1 : ℂ) else 1)) =
          if (Finset.univ.filter (fun k => σ k = true)).card % 2 = 0 then (1 : ℂ) else -1 := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => σ k = true)]
        have h1 : ∏ k ∈ Finset.univ.filter (fun k => σ k = true), (if σ k then (-1 : ℂ) else 1) =
            (-1 : ℂ) ^ (Finset.univ.filter (fun k => σ k = true)).card := by
          calc
            ∏ k ∈ Finset.univ.filter (fun k => σ k = true), (if σ k then (-1 : ℂ) else 1)
              = ∏ _k ∈ Finset.univ.filter (fun k => σ k = true), (-1 : ℂ) :=
                Finset.prod_congr rfl (fun k hk => by simp [(Finset.mem_filter.mp hk).2])
            _ = (-1 : ℂ) ^ (Finset.univ.filter (fun k => σ k = true)).card := Finset.prod_const _
        have h2 : ∏ k ∈ Finset.univ.filter (fun k => ¬ σ k = true), (if σ k then (-1 : ℂ) else 1) = 1 :=
          Finset.prod_eq_one (fun k hk => by simp [(Finset.mem_filter.mp hk).2])
        rw [h1, h2, mul_one]
        rcases Nat.even_or_odd (Finset.univ.filter (fun k => σ k = true)).card with ⟨m, hm⟩ | ⟨m, hm⟩
        · rw [hm, show (m + m) % 2 = 0 by omega, show m + m = 2 * m by omega, pow_mul]
          norm_num
        · rw [hm, show (2 * m + 1) % 2 = 1 by omega, pow_succ, pow_mul]
          norm_num
      dsimp only
      rw [← hsign, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      cases σ k <;> simp [mul_comm]
    have hw_eq_iff_tensor : ∀ (A B : Matrix I I ℂ), fits A → fits B →
        (w A = w B ↔ PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf A) =
                     PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf B)) := by
      intro A B hA hB
      constructor
      · intro hw
        funext σ
        have h1 : (∏ j : Fin b × Fin 2, A (PEqualNP.Outside.L_lib_1093_aux.blockPerm σ j) j) =
            (∏ j : Fin b × Fin 2, B (PEqualNP.Outside.L_lib_1093_aux.blockPerm σ j) j) :=
          congrFun hw (PEqualNP.Outside.L_lib_1093_aux.blockPerm σ)
        rw [PEqualNP.Outside.L_lib_1093_aux.prod_blockPerm (A : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ),
          PEqualNP.Outside.L_lib_1093_aux.prod_blockPerm (B : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ)] at h1
        exact h1
      · intro ht
        funext π
        by_cases hpres : ∀ j : I, (π j).1 = j.1
        · rw [PEqualNP.Outside.L_lib_1093_aux.perm_eq_blockPerm_of_preserves π hpres]
          change (∏ j : Fin b × Fin 2, A (PEqualNP.Outside.L_lib_1093_aux.blockPerm _ j) j) =
            (∏ j : Fin b × Fin 2, B (PEqualNP.Outside.L_lib_1093_aux.blockPerm _ j) j)
          rw [PEqualNP.Outside.L_lib_1093_aux.prod_blockPerm (A : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ),
            PEqualNP.Outside.L_lib_1093_aux.prod_blockPerm (B : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ)]
          exact congrFun ht (fun k => decide (π (k, 0) = (k, 1)))
        · push Not at hpres
          rcases hpres with ⟨j, hj⟩
          have hA0' : w A π = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (hA (π j) j hj)
          have hB0' : w B π = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (hB (π j) j hj)
          exact hA0'.trans hB0'.symm
    have hex_sep : ∀ y : Fin (b + 1) → ℂ, ∃ exp : Fin b → Fin q,
        ∀ A B : Matrix I I ℂ, fits A → fits B →
          (∀ h : Fin (b + 1), eval (phase (front h)) A = y h) →
          (∀ h : Fin (b + 1), eval (phase (front h)) B = y h) →
          eval (phase (diagQuery exp)) A = eval (phase (diagQuery exp)) B →
          w A = w B := by
      intro y
      by_cases hexA : ∃ A0 : Matrix I I ℂ, fits A0 ∧ ∀ h : Fin (b + 1), eval (phase (front h)) A0 = y h
      · rcases hexA with ⟨A0, hA0, hy0⟩
        by_cases hp0 : polyOf A0 = 0
        · refine ⟨fun _ => ⟨0, hq0⟩, fun A B hA hB hyA hyB _ => ?_⟩
          have hpA : polyOf A = 0 := (hpoly_eq_of_front A A0 hA hA0 (fun h => (hyA h).trans (hy0 h).symm)).trans hp0
          have hpB : polyOf B = 0 := (hpoly_eq_of_front B A0 hB hA0 (fun h => (hyB h).trans (hy0 h).symm)).trans hp0
          have hT0 : ∀ (C : Matrix I I ℂ), polyOf C = 0 →
              PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf C) = 0 := by
            intro C hpC
            rcases Finset.prod_eq_zero_iff.mp hpC with ⟨k0, _, hk0⟩
            have h1 : (vecOf C k0).1 = 0 := by
              have := congrArg (fun p : Polynomial ℂ => p.eval 0) hk0
              simpa using this
            have h2 : (vecOf C k0).2 = 0 := by
              have := congrArg (fun p : Polynomial ℂ => p.eval 1) hk0
              simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
                mul_one, Polynomial.eval_zero, h1, zero_sub, neg_eq_zero] at this
              exact this
            funext σ
            unfold PEqualNP.Outside.L_lib_1093_aux.tensorOf
            refine Finset.prod_eq_zero (Finset.mem_univ k0) ?_
            cases σ k0 <;> simp [h1, h2]
          exact (hw_eq_iff_tensor A B hA hB).mpr ((hT0 A hpA).trans (hT0 B hpB).symm)
        · let S_pts : Finset ℂ := (Finset.univ : Finset (Fin q)).image (fun j : Fin q => ζ ^ j.val)
          have hS_inj : Function.Injective (fun j : Fin q => ζ ^ j.val) := by
            intro j1 j2 hh
            exact Fin.ext (hζ.injOn_pow
              (Finset.mem_coe.mpr (Finset.mem_range.mpr j1.isLt))
              (Finset.mem_coe.mpr (Finset.mem_range.mpr j2.isLt)) hh)
          have hS_card : S_pts.card = q := by
            rw [Finset.card_image_of_injective _ hS_inj, Finset.card_univ, Fintype.card_fin]
          let eS : Fin q ≃ S_pts :=
            Equiv.ofBijective (fun j => ⟨ζ ^ j.val, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
              ⟨fun j1 j2 h => hS_inj (congrArg Subtype.val h),
               fun ⟨z, hz⟩ => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; exact ⟨j, rfl⟩⟩
          let tA0 : (Fin b → Bool) → ℂ := PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf A0)
          let sgn : (Fin b → Bool) → ℂ := fun σ =>
            if (Finset.univ.filter (fun k => σ k = true)).card % 2 = 0 then 1 else -1
          let cand : Equiv.Perm (Fin b) → (Fin b → Bool) → ℂ := fun π σ => sgn σ * tA0 (σ ∘ π)
          let pairs : Finset (Finset (Equiv.Perm (Fin b))) :=
            (Finset.univ : Finset (Equiv.Perm (Fin b))).powersetCard 2
          have hpairs_card : pairs.card = Nat.choose b.factorial 2 := by
            simp [pairs, Fintype.card_perm]
          let badFor : Finset (Equiv.Perm (Fin b)) → Finset (Fin b → Fin q) := fun P =>
            Finset.univ.filter (fun exp =>
              ∃ π₁ ∈ P, ∃ π₂ ∈ P, cand π₁ ≠ cand π₂ ∧
                PEqualNP.Outside.L_lib_1093_aux.evalMulti (fun σ => cand π₁ σ - cand π₂ σ)
                  (fun k => ζ ^ (exp k).val) = 0)
          have hbad_pair : ∀ P ∈ pairs, (badFor P).card ≤ b * q ^ (b - 1) := by
            intro P hP
            rcases Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2 with ⟨π₁, π₂, hne, rfl⟩
            by_cases hcand : cand π₁ = cand π₂
            · have hempty : badFor {π₁, π₂} = ∅ := by
                ext exp
                simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                  Finset.mem_singleton, Finset.notMem_empty, iff_false, not_exists, not_and]
                rintro p1 (rfl | rfl) p2 (rfl | rfl) hne' _
                · exact hne' rfl
                · exact hne' hcand
                · exact hne' hcand.symm
                · exact hne' rfl
              rw [hempty, Finset.card_empty]; exact Nat.zero_le _
            · have hnz : ∃ σ, cand π₁ σ - cand π₂ σ ≠ 0 := by
                by_contra hall; push Not at hall
                exact hcand (funext (fun σ => sub_eq_zero.mp (hall σ)))
              have hsub : badFor {π₁, π₂} ⊆
                  Finset.univ.filter (fun exp : Fin b → Fin q =>
                    PEqualNP.Outside.L_lib_1093_aux.evalMulti (fun σ => cand π₁ σ - cand π₂ σ)
                      (fun k => ζ ^ (exp k).val) = 0) := by
                intro exp hexp
                simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                  Finset.mem_singleton] at hexp ⊢
                rcases hexp with ⟨p1, hp1, p2, hp2, hne', hev⟩
                rcases hp1 with hp1 | hp1 <;> rcases hp2 with hp2 | hp2
                · rw [hp1, hp2] at hne'; exact (hne' rfl).elim
                · rw [hp1, hp2] at hev; exact hev
                · rw [hp1, hp2] at hev
                  have hneg : PEqualNP.Outside.L_lib_1093_aux.evalMulti (fun σ => cand π₂ σ - cand π₁ σ)
                      (fun k => ζ ^ (exp k).val) =
                      -(PEqualNP.Outside.L_lib_1093_aux.evalMulti (fun σ => cand π₁ σ - cand π₂ σ)
                        (fun k => ζ ^ (exp k).val)) := by
                    unfold PEqualNP.Outside.L_lib_1093_aux.evalMulti
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl (fun σ _ => by ring)
                  rw [hneg] at hev; exact neg_eq_zero.mp hev
                · rw [hp1, hp2] at hne'; exact (hne' rfl).elim
              have hcard_trans : (Finset.univ.filter (fun exp : Fin b → Fin q =>
                    PEqualNP.Outside.L_lib_1093_aux.evalMulti (fun σ => cand π₁ σ - cand π₂ σ)
                      (fun k => ζ ^ (exp k).val) = 0)).card =
                  (Finset.univ.filter (fun x : Fin b → S_pts =>
                    PEqualNP.Outside.L_lib_1093_aux.evalMulti (fun σ => cand π₁ σ - cand π₂ σ)
                      (fun k => (x k).val) = 0)).card := by
                let eF : (Fin b → Fin q) ≃ (Fin b → S_pts) := Equiv.piCongrRight (fun _ => eS)
                rw [← Finset.card_map eF.toEmbedding]
                congr 1
                ext x
                simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                  Equiv.coe_toEmbedding]
                constructor
                · rintro ⟨exp, hev, rfl⟩
                  have hval : (fun k => ((eF exp k) : ℂ)) = fun k => ζ ^ (exp k).val := rfl
                  rwa [hval]
                · intro hev
                  refine ⟨eF.symm x, ?_, eF.apply_symm_apply x⟩
                  have hval : (fun k => ζ ^ (eF.symm x k).val) = fun k => (x k).val := by
                    funext k
                    exact congrArg Subtype.val (eS.apply_symm_apply (x k))
                  rwa [hval]
              calc
                (badFor {π₁, π₂}).card ≤ _ := Finset.card_le_card hsub
                _ = _ := hcard_trans
                _ ≤ b * S_pts.card ^ (b - 1) :=
                  PEqualNP.Outside.L_lib_1093_aux.evalMulti_zero_count_le b S_pts _ hnz
                _ = b * q ^ (b - 1) := by rw [hS_card]
          have hbad_union : (pairs.biUnion badFor).card < (Finset.univ : Finset (Fin b → Fin q)).card := by
            have hle : (pairs.biUnion badFor).card ≤ pairs.card * (b * q ^ (b - 1)) := by
              calc
                (pairs.biUnion badFor).card ≤ ∑ P ∈ pairs, (badFor P).card := Finset.card_biUnion_le
                _ ≤ ∑ _P ∈ pairs, (b * q ^ (b - 1)) := Finset.sum_le_sum hbad_pair
                _ = pairs.card * (b * q ^ (b - 1)) := by simp
            have htot : (Finset.univ : Finset (Fin b → Fin q)).card = q ^ b := by simp
            rw [hpairs_card] at hle
            rw [htot]
            have hqb : q ^ b = q * q ^ (b - 1) := by
              conv_lhs => rw [show b = (b - 1) + 1 by omega, pow_succ, mul_comm]
            have hlt : (b * Nat.choose b.factorial 2) * q ^ (b - 1) < q * q ^ (b - 1) :=
              Nat.mul_lt_mul_of_pos_right hqbound (pow_pos hq0 _)
            have hcomm : Nat.choose b.factorial 2 * (b * q ^ (b - 1)) =
                (b * Nat.choose b.factorial 2) * q ^ (b - 1) := by ring
            omega
          have hex_good : ∃ exp : Fin b → Fin q, exp ∉ pairs.biUnion badFor := by
            by_contra hall
            push Not at hall
            have hsub : (Finset.univ : Finset (Fin b → Fin q)) ⊆ pairs.biUnion badFor :=
              fun exp _ => hall exp
            have := Finset.card_le_card hsub
            omega
          rcases hex_good with ⟨exp, hgood⟩
          refine ⟨exp, fun A B hA hB hyA hyB hdiag => ?_⟩
          have hpA : polyOf A = polyOf A0 :=
            hpoly_eq_of_front A A0 hA hA0 (fun h => (hyA h).trans (hy0 h).symm)
          have hpB : polyOf B = polyOf A0 :=
            hpoly_eq_of_front B A0 hB hA0 (fun h => (hyB h).trans (hy0 h).symm)
          rcases PEqualNP.Outside.L_lib_1093_aux.poly_linear_factor_perm (vecOf A0) (vecOf A) hpA.symm hp0
            with ⟨π₁, hπ₁⟩
          rcases PEqualNP.Outside.L_lib_1093_aux.poly_linear_factor_perm (vecOf A0) (vecOf B) hpB.symm hp0
            with ⟨π₂, hπ₂⟩
          have hcand_eq : cand π₁ = cand π₂ := by
            by_contra hne_cand
            have hne_perm : π₁ ≠ π₂ := fun h => hne_cand (by rw [h])
            apply hgood
            refine Finset.mem_biUnion.mpr ⟨{π₁, π₂}, ?_, ?_⟩
            · rw [Finset.mem_powersetCard]
              refine ⟨Finset.subset_univ _, ?_⟩
              rw [Finset.card_insert_of_notMem (by simp [hne_perm]), Finset.card_singleton]
            · simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨π₁, by simp, π₂, by simp, hne_cand, ?_⟩
              rw [hdiag_eval A hA exp, hdiag_eval B hB exp] at hdiag
              have hA_eq : (fun σ => sgn σ * PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf A) σ) = cand π₁ := by
                funext σ; simp [cand, tA0, hπ₁ σ]
              have hB_eq : (fun σ => sgn σ * PEqualNP.Outside.L_lib_1093_aux.tensorOf (vecOf B) σ) = cand π₂ := by
                funext σ; simp [cand, tA0, hπ₂ σ]
              rw [hA_eq, hB_eq] at hdiag
              unfold PEqualNP.Outside.L_lib_1093_aux.evalMulti at hdiag ⊢
              have hsub : (∑ σ : Fin b → Bool, (cand π₁ σ - cand π₂ σ) * ∏ k : Fin b, (if σ k then ζ ^ (exp k).val else 1)) =
                  (∑ σ : Fin b → Bool, cand π₁ σ * ∏ k : Fin b, (if σ k then ζ ^ (exp k).val else 1)) -
                  (∑ σ : Fin b → Bool, cand π₂ σ * ∏ k : Fin b, (if σ k then ζ ^ (exp k).val else 1)) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl (fun σ _ => by ring)
              rw [hsub, hdiag, sub_self]
          apply (hw_eq_iff_tensor A B hA hB).mpr
          funext σ
          have h1 := congrFun hcand_eq σ
          simp only [cand, tA0] at h1
          have hsgn_nz : sgn σ ≠ 0 := by simp only [sgn]; split_ifs <;> norm_num
          rw [hπ₁ σ, hπ₂ σ]
          exact mul_left_cancel₀ hsgn_nz h1
      · refine ⟨fun _ => ⟨0, hq0⟩, fun A _ hA _ hyA _ _ => ?_⟩
        exact (hexA ⟨A, hA, hyA⟩).elim
    classical
    choose expOf hexpOf using hex_sep
    let last : (Fin (b + 1) → ℂ) → T := fun y => diagQuery (expOf y)
    let read : (Fin (b + 1) → ℂ) → ℂ → W := fun y z =>
      if h : ∃ A : Matrix I I ℂ, fits A ∧
          (∀ h : Fin (b + 1), eval (phase (front h)) A = y h) ∧
          eval (phase (last y)) A = z
      then w (Classical.choose h)
      else 0
    refine ⟨front, last, read, fun A hA => ?_⟩
    set y : Fin (b + 1) → ℂ := fun h => eval (phase (front h)) A
    have hex : ∃ B : Matrix I I ℂ, fits B ∧
        (∀ h : Fin (b + 1), eval (phase (front h)) B = y h) ∧
        eval (phase (last y)) B = eval (phase (last y)) A :=
      ⟨A, hA, fun _ => rfl, rfl⟩
    simp only [read, hex, ↓reduceDIte]
    have hch := Classical.choose_spec hex
    exact hexpOf y (Classical.choose hex) A hch.1 hA hch.2.1 (fun _ => rfl) hch.2.2
