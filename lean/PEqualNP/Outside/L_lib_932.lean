import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_932
open scoped Matrix

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_neg (x : ZMod 2) : -x = x := by
  fin_cases x <;> rfl

lemma z2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by
  rw [sub_eq_add_neg, z2_neg]

lemma z2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> [exact Or.inl rfl; exact Or.inr rfl]


lemma card_filter_compl {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    exact hx2.2 hx1.2

def IsAlt {ι : Type*} (A : Matrix ι ι (ZMod 2)) : Prop :=
  (∀ i, A i i = 0) ∧ (∀ i j, A i j = A j i)

lemma isAlt_transpose {ι : Type*} {A : Matrix ι ι (ZMod 2)} (hA : IsAlt A) : Aᵀ = A := by
  ext i j
  exact hA.2 j i

lemma sum_symm_zero_diag {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ZMod 2) (hdiag : ∀ i, f i i = 0) (hsym : ∀ i j, f i j = f j i) :
    ∑ i : ι, ∑ j : ι, f i j = 0 := by
  have hprod : ∑ i : ι, ∑ j : ι, f i j = ∑ p : ι × ι, f p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : ι × ι => f p.1 p.2)).symm
  rw [hprod]
  let Slt : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 < p.2)
  let Sgt : Finset (ι × ι) := Finset.univ.filter (fun p => p.2 < p.1)
  let Seq : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 = p.2)
  have hunion : (Finset.univ : Finset (ι × ι)) = (Slt ∪ Sgt) ∪ Seq := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, Slt, Sgt, Seq]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hd1 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Slt, Sgt, Seq] at hp1 hp2
    rcases hp1 with h | h <;> exact (ne_of_lt h) (by first | exact hp2 | exact hp2.symm)
  have hd2 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Slt, Sgt] at hp1 hp2
    exact lt_asymm hp1 hp2
  rw [hunion, Finset.sum_union hd1, Finset.sum_union hd2]
  have hseq : ∑ p ∈ Seq, f p.1 p.2 = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Seq] at hp
    rw [hp, hdiag]
  have hswap : ∑ p ∈ Sgt, f p.1 p.2 = ∑ p ∈ Slt, f p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Slt, Sgt] at hp ⊢
      exact hp
    · intro p1 _ p2 _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Slt, Sgt] at hq ⊢
      exact hq
    · intro p _
      exact hsym p.1 p.2
  rw [hseq, add_zero, hswap, z2_add_self]

lemma quad_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (ZMod 2)} (hA : IsAlt A) (v : ι → ZMod 2) :
    dotProduct v (A.mulVec v) = 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h1 : dotProduct v (A.mulVec v) = ∑ i : ι, ∑ j : ι, v i * A i j * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1]
  have h2 : ∑ i : ι, ∑ j : ι, v i * A i j * v j =
      ∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
        v (e.symm i) * A (e.symm i) (e.symm j) * v (e.symm j) := by
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => (e.symm.sum_comp _).symm
  rw [h2]
  apply sum_symm_zero_diag
  · intro i
    rw [hA.1, mul_zero, zero_mul]
  · intro i j
    rw [hA.2 (e.symm i) (e.symm j)]
    ring

lemma isAlt_conj {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (ZMod 2)} (hA : IsAlt A) (Q : Matrix ι κ (ZMod 2)) :
    IsAlt (Qᵀ * A * Q) := by
  constructor
  · intro k
    have hdiag : (Qᵀ * A * Q) k k = dotProduct (fun i => Q i k) (A.mulVec (fun i => Q i k)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hdiag]
    exact quad_eq_zero hA (fun i => Q i k)
  · intro j k
    have hT : (Qᵀ * A * Q)ᵀ = Qᵀ * A * Q := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, isAlt_transpose hA, Matrix.mul_assoc]
    have := congrArg (fun M => M j k) hT
    simpa [Matrix.transpose_apply] using this.symm

lemma isAlt_add {ι : Type*} {A B : Matrix ι ι (ZMod 2)} (hA : IsAlt A) (hB : IsAlt B) :
    IsAlt (A + B) :=
  ⟨fun i => by simp [hA.1 i, hB.1 i], fun i j => by simp [hA.2 i j, hB.2 i j]⟩

lemma isAlt_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (ZMod 2)} (hA : IsAlt A) (hdet : IsUnit A.det) :
    IsAlt A⁻¹ := by
  have hT : (A⁻¹)ᵀ = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, isAlt_transpose hA]
  have heq : A⁻¹ = (A⁻¹)ᵀ * A * A⁻¹ := by
    rw [hT, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hdet, Matrix.mul_one]
  rw [heq]
  exact isAlt_conj hA A⁻¹

def Omega {m : ℕ} (w : Fin m → ZMod 2) : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 ≠ q.2 then w p.1 else 0

lemma isAlt_Omega {m : ℕ} (w : Fin m → ZMod 2) : IsAlt (Omega w) := by
  constructor
  · intro p
    simp [Omega]
  · intro p q
    simp only [Omega, Matrix.of_apply]
    by_cases h : p.1 = q.1 ∧ p.2 ≠ q.2
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, h.1]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

lemma omega_add {m : ℕ} (u v : Fin m → ZMod 2) :
    Omega (u + v) = Omega u + Omega v := by
  ext p q
  simp only [Omega, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma exists_invertible_shift :
    ∀ (m : ℕ) (A : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2)),
      IsAlt A → ∃ a : Fin m → ZMod 2, IsUnit (A + Omega a).det
  | 0, A, _ => by
    refine ⟨fun i => i.elim0, ?_⟩
    have : IsEmpty (Fin 0 × Bool) := ⟨fun p => p.1.elim0⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  | m + 1, A, hA => by
    let e : (Fin m × Bool) ⊕ Bool ≃ Fin (m + 1) × Bool :=
      { toFun := fun s => match s with
          | Sum.inl (i, b) => (i.castSucc, b)
          | Sum.inr b => (Fin.last m, b)
        invFun := fun p =>
          Fin.lastCases (Sum.inr p.2) (fun i => Sum.inl (i, p.2)) p.1
        left_inv := fun s => by
          cases s with
          | inl ib => simp
          | inr b => simp
        right_inv := fun p => by
          rcases p with ⟨i, b⟩
          refine Fin.lastCases ?_ ?_ i
          · simp
          · intro j; simp }
    let B : Matrix ((Fin m × Bool) ⊕ Bool) ((Fin m × Bool) ⊕ Bool) (ZMod 2) := A.submatrix e e
    have hB : IsAlt B :=
      ⟨fun x => hA.1 (e x), fun x y => hA.2 (e x) (e y)⟩
    let A11 : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) := B.submatrix Sum.inl Sum.inl
    let A12 : Matrix (Fin m × Bool) Bool (ZMod 2) := B.submatrix Sum.inl Sum.inr
    let A21 : Matrix Bool (Fin m × Bool) (ZMod 2) := B.submatrix Sum.inr Sum.inl
    let A22 : Matrix Bool Bool (ZMod 2) := B.submatrix Sum.inr Sum.inr
    have hA11 : IsAlt A11 := ⟨fun x => hB.1 (Sum.inl x), fun x y => hB.2 (Sum.inl x) (Sum.inl y)⟩
    have hA22 : IsAlt A22 := ⟨fun x => hB.1 (Sum.inr x), fun x y => hB.2 (Sum.inr x) (Sum.inr y)⟩
    have hA21 : A21 = A12ᵀ := by
      ext b x
      exact hB.2 (Sum.inr b) (Sum.inl x)
    obtain ⟨a0, ha0⟩ := exists_invertible_shift m A11 hA11
    let M0 : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) := A11 + Omega a0
    have hM0_alt : IsAlt M0 := isAlt_add hA11 (isAlt_Omega a0)
    have hM0_inv_alt : IsAlt M0⁻¹ := isAlt_inv hM0_alt ha0
    let S0 : Matrix Bool Bool (ZMod 2) := A22 - A21 * M0⁻¹ * A12
    have hS0_eq : S0 = A22 + A12ᵀ * M0⁻¹ * A12 := by
      ext b1 b2
      simp only [S0, Matrix.sub_apply, Matrix.add_apply, hA21, z2_sub_eq_add]
    have hS0_alt : IsAlt S0 := by
      rw [hS0_eq]
      exact isAlt_add hA22 (isAlt_conj hM0_inv_alt A12)
    let c : ZMod 2 := S0 false true + 1
    let a : Fin (m + 1) → ZMod 2 := Fin.snoc a0 c
    let Jc : Matrix Bool Bool (ZMod 2) := Matrix.of fun b1 b2 => if b1 ≠ b2 then c else 0
    have hsub : (A + Omega a).submatrix e e = Matrix.fromBlocks M0 A12 A21 (A22 + Jc) := by
      ext x y
      cases x with
      | inl ib =>
        cases y with
        | inl jb =>
          simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.fromBlocks_apply₁₁, M0, A11, B, e, Equiv.coe_fn_mk, Omega, Matrix.of_apply]
          have h1 : ib.1.castSucc = jb.1.castSucc ↔ ib.1 = jb.1 := Fin.castSucc_inj
          simp only [h1, a]
          split_ifs with h
          · simp [Fin.snoc_castSucc]
          · rfl
        | inr b =>
          simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.fromBlocks_apply₁₂, A12, B, e, Equiv.coe_fn_mk, Omega, Matrix.of_apply]
          have hne : ib.1.castSucc ≠ Fin.last m := Fin.castSucc_ne_last ib.1
          simp [hne]
      | inr b =>
        cases y with
        | inl jb =>
          simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.fromBlocks_apply₂₁, A21, B, e, Equiv.coe_fn_mk, Omega, Matrix.of_apply]
          have hne : Fin.last m ≠ jb.1.castSucc := (Fin.castSucc_ne_last jb.1).symm
          simp [hne]
        | inr b2 =>
          simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.fromBlocks_apply₂₂, A22, B, e, Equiv.coe_fn_mk, Omega, Jc, Matrix.of_apply, a, true_and]
          split_ifs with h
          · simp [Fin.snoc_last]
          · rfl
    have hdet_eq : (A + Omega a).det = ((A + Omega a).submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self e (A + Omega a)).symm
    refine ⟨a, ?_⟩
    letI : Invertible M0 := Matrix.invertibleOfIsUnitDet M0 ha0
    rw [hdet_eq, hsub, Matrix.det_fromBlocks₁₁ M0 A12 A21 (A22 + Jc), Matrix.invOf_eq_nonsing_inv M0]
    have hschur : (A22 + Jc) - A21 * M0⁻¹ * A12 = S0 + Jc := by
      ext b1 b2
      simp only [S0, Matrix.sub_apply, Matrix.add_apply]
      ring
    rw [hschur]
    have hdet2 : (S0 + Jc).det = 1 := by
      let S2 := S0 + Jc
      have hff : S2 false false = 0 := by simp [S2, Jc, hS0_alt.1 false]
      have htt : S2 true true = 0 := by simp [S2, Jc, hS0_alt.1 true]
      have hft : S2 false true = 1 := by
        simp only [S2, Matrix.add_apply, Jc, Matrix.of_apply, ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, c]
        rw [← add_assoc, z2_add_self, zero_add]
      have htf : S2 true false = 1 := by
        simp only [S2, Matrix.add_apply, Jc, Matrix.of_apply, ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte, c]
        rw [hS0_alt.2 true false, ← add_assoc, z2_add_self, zero_add]
      have hfin : S2.det = (S2.submatrix (fun i : Fin 2 => i == 1) (fun i : Fin 2 => i == 1)).det := by
        let eb : Fin 2 ≃ Bool :=
          { toFun := fun i => i == 1
            invFun := fun b => if b then 1 else 0
            left_inv := fun i => by fin_cases i <;> decide
            right_inv := fun b => by cases b <;> decide }
        exact (Matrix.det_submatrix_equiv_self eb S2).symm
      rw [hfin, Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply]
      change S2 false false * S2 true true - S2 false true * S2 true false = 1
      rw [hff, htt, hft, htf]
      decide
    rw [hdet2, mul_one]
    exact ha0

lemma rank_Omega_le {m : ℕ} (v : Fin m → ZMod 2) :
    (Omega v).rank ≤ 2 * (Finset.univ.filter (fun t : Fin m => v t ≠ 0)).card := by
  let S : Finset (Fin m × Bool) := (Finset.univ.filter (fun t : Fin m => v t ≠ 0)) ×ˢ Finset.univ
  have hsub : LinearMap.range (Omega v).mulVecLin ≤
      Submodule.span (ZMod 2) ((S : Set (Fin m × Bool)).image (fun p => Pi.single p (1 : ZMod 2))) := by
    rintro y ⟨x, rfl⟩
    have hy : (Omega v).mulVecLin x = ∑ p ∈ S, ((Omega v).mulVecLin x p) • Pi.single p (1 : ZMod 2) := by
      ext q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hq : q ∈ S
      · rw [Finset.sum_eq_single q]
        · simp
        · intro p _ hpq; simp [hpq.symm]
        · intro h; exact (h hq).elim
      · rw [Finset.sum_eq_zero]
        · simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Omega, Matrix.of_apply]
          have hv0 : v q.1 = 0 := by
            by_contra hne
            apply hq
            simp [S, hne]
          apply Finset.sum_eq_zero
          intro r _
          split_ifs <;> simp [hv0]
        · intro p hp
          have hpq : q ≠ p := fun h => hq (h ▸ hp)
          simp [hpq]
    rw [hy]
    refine Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩)
  have h1 : (Omega v).rank ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((S : Set (Fin m × Bool)).image (fun p => Pi.single p (1 : ZMod 2)))) :=
    Submodule.finrank_mono hsub
  have h2 : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ((S : Set (Fin m × Bool)).image (fun p => Pi.single p (1 : ZMod 2)))) ≤ S.card := by
    have hfin : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (S.image (fun p : Fin m × Bool => (Pi.single p (1 : ZMod 2) : (Fin m × Bool) → ZMod 2)) : Set ((Fin m × Bool) → ZMod 2))) ≤
        (S.image (fun p : Fin m × Bool => (Pi.single p (1 : ZMod 2) : (Fin m × Bool) → ZMod 2))).card := by
      simpa using finrank_span_le_card (R := ZMod 2) (S.image (fun p : Fin m × Bool => (Pi.single p (1 : ZMod 2) : (Fin m × Bool) → ZMod 2)) : Set ((Fin m × Bool) → ZMod 2))
    rw [Finset.coe_image] at hfin
    exact hfin.trans Finset.card_image_le
  have hcard : S.card = 2 * (Finset.univ.filter (fun t : Fin m => v t ≠ 0)).card := by
    simp [S, Finset.card_product, mul_comm]
  omega

lemma rank_full_of_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (hdet : IsUnit A.det) :
    A.rank = Fintype.card ι := by
  have hsurj : LinearMap.range A.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨A⁻¹.mulVec y, ?_⟩
    simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet]
  rw [Matrix.rank, hsurj, finrank_top, Module.finrank_pi]

lemma weight_shift_sum_le (m j : ℕ) (C : (Fin j → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (a : Fin m → ZMod 2) :
    (∑ u : Fin j → ZMod 2, (1 : ℚ) / 2 ^ ((Finset.univ.filter (fun t : Fin m => (C u + a) t ≠ 0)).card)) ≤
      ∑ u : Fin j → ZMod 2, (1 : ℚ) / 2 ^ ((Finset.univ.filter (fun t : Fin m => C u t ≠ 0)).card) := by
  have hident : ∀ v : Fin m → ZMod 2,
      (2 : ℚ) ^ m * ((1 : ℚ) / 2 ^ ((Finset.univ.filter (fun t : Fin m => v t ≠ 0)).card)) =
        ∑ S : Finset (Fin m), if (∀ t ∈ S, v t = 0) then (1 : ℚ) else 0 := by
    intro v
    let Z : Finset (Fin m) := Finset.univ.filter (fun t => v t = 0)
    let N : Finset (Fin m) := Finset.univ.filter (fun t => v t ≠ 0)
    have hcompl : Z.card + N.card = m := by
      have h1 := card_filter_compl (Finset.univ : Finset (Fin m)) (fun t => v t = 0)
      simpa [Z, N] using h1
    have hrhs : (∑ S : Finset (Fin m), if (∀ t ∈ S, v t = 0) then (1 : ℚ) else 0) =
        ((Z.powerset).card : ℚ) := by
      rw [Finset.sum_boole]
      congr 1
      congr 1
      ext S
      simp [Finset.mem_powerset, Finset.subset_iff, Z]
    rw [hrhs, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (2 : ℚ) ^ m = (2 : ℚ) ^ Z.card * (2 : ℚ) ^ N.card := by
      rw [← pow_add, hcompl]
    rw [hpow]
    have hne : (2 : ℚ) ^ N.card ≠ 0 := by positivity
    rw [one_div, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hpos : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  suffices hmul :
      (2 : ℚ) ^ m * (∑ u : Fin j → ZMod 2, (1 : ℚ) / 2 ^ ((Finset.univ.filter (fun t : Fin m => (C u + a) t ≠ 0)).card)) ≤
      (2 : ℚ) ^ m * (∑ u : Fin j → ZMod 2, (1 : ℚ) / 2 ^ ((Finset.univ.filter (fun t : Fin m => C u t ≠ 0)).card)) by
    exact le_of_mul_le_mul_left hmul hpos
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [hident]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun S _ => ?_
  simp only [Finset.sum_boole, Nat.cast_le]
  let Aset := Finset.univ.filter (fun u : Fin j → ZMod 2 => ∀ t ∈ S, (C u + a) t = 0)
  let Zset := Finset.univ.filter (fun u : Fin j → ZMod 2 => ∀ t ∈ S, C u t = 0)
  change Aset.card ≤ Zset.card
  by_cases hne : Aset.Nonempty
  · obtain ⟨u0, hu0⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Aset, Pi.add_apply] at hu0
    refine Finset.card_le_card_of_injOn (fun u => u + u0) ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Aset, Zset, Pi.add_apply] at hu ⊢
      intro t ht
      have h1 := hu t ht
      have h2 := hu0 t ht
      rw [map_add, Pi.add_apply]
      have hsum : (C u t + a t) + (C u0 t + a t) = 0 := by rw [h1, h2, add_zero]
      have hre : (C u t + a t) + (C u0 t + a t) = (C u t + C u0 t) + (a t + a t) := by ring
      rw [hre, z2_add_self, add_zero] at hsum
      exact hsum
    · intro u1 _ u2 _ h
      have h' := congrArg (fun x => x + u0) h
      have hcancel : ∀ x : Fin j → ZMod 2, x + u0 + u0 = x := by
        intro x; ext k; simp [add_assoc, z2_add_self]
      simpa [hcancel] using h'
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem main : ∀ m n : ℕ,
  let F := ZMod 2
  let V := Fin n → F
  let H := Fin m → F
  let D := (Fin m × Bool) → F
  let M := Matrix (Fin n) (Fin n) F
  let basis := fun (i j : Fin n) => if i = j then (1 : F) else 0
  let wt := fun (w : H) => ((Finset.univ : Finset (Fin m)).filter (fun t => w t ≠ 0)).card
  ∀ P : V →ₗ[F] D, Function.Surjective P →
    let omega := fun (w : H) => Matrix.of (fun i j : Fin n =>
      ∑ t : Fin m, w t * (P (basis i) (t,false) * P (basis j) (t,true) +
        P (basis i) (t,true) * P (basis j) (t,false)))
    ∀ K : M, (∀ i, K i i = 0) → (∀ i j, K i j = K j i) →
      (∃ a : H, ∀ w : H, 2 * wt (w+a) ≤ (K + omega w).rank) ∧
      ∀ (j : ℕ) (C : (Fin j → F) →ₗ[F] H),
        (∑ u : Fin j → F, (1 : ℚ) / 2^((K + omega (C u)).rank / 2)) ≤
          ∑ u : Fin j → F, (1 : ℚ) / 2^(wt (C u)) := by
  intro m n F V H D M basis wt P hPsurj omega K hKdiag hKsym
  have hKalt : IsAlt K := ⟨hKdiag, hKsym⟩
  choose s hs using fun p : Fin m × Bool => hPsurj (Pi.single p (1 : ZMod 2))
  let Q : Matrix (Fin n) (Fin m × Bool) (ZMod 2) := Matrix.of fun i p => s p i
  have hP_s : ∀ p : Fin m × Bool, ∑ i : Fin n, s p i • P (basis i) = Pi.single p (1 : ZMod 2) := by
    intro p
    simp_rw [← map_smul]
    rw [← map_sum]
    have hsp : ∑ i : Fin n, s p i • basis i = s p := by
      ext k
      simp [basis, Finset.sum_apply, Pi.smul_apply]
    rw [hsp, hs p]
  have hpull_omega : ∀ w : H, Qᵀ * omega w * Q = Omega w := by
    intro w
    ext p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Q, omega, Matrix.of_apply,
      Finset.sum_mul, Finset.mul_sum]
    have hterm : ∀ t : Fin m,
        ∑ i : Fin n, ∑ j : Fin n,
          s p i * (w t * (P (basis i) (t, false) * P (basis j) (t, true) +
            P (basis i) (t, true) * P (basis j) (t, false))) * s q j =
        w t * ((∑ i : Fin n, s p i * P (basis i) (t, false)) * (∑ j : Fin n, s q j * P (basis j) (t, true)) +
          (∑ i : Fin n, s p i * P (basis i) (t, true)) * (∑ j : Fin n, s q j * P (basis j) (t, false))) := by
      intro t
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
      simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hreord :
        (∑ j : Fin n, ∑ i : Fin n, ∑ t : Fin m,
          s p i * (w t * (P (basis i) (t, false) * P (basis j) (t, true) +
            P (basis i) (t, true) * P (basis j) (t, false))) * s q j) =
        ∑ t : Fin m, ∑ i : Fin n, ∑ j : Fin n,
          s p i * (w t * (P (basis i) (t, false) * P (basis j) (t, true) +
            P (basis i) (t, true) * P (basis j) (t, false))) * s q j := by
      rw [Finset.sum_comm]
      trans (∑ i : Fin n, ∑ t : Fin m, ∑ j : Fin n,
        s p i * (w t * (P (basis i) (t, false) * P (basis j) (t, true) +
          P (basis i) (t, true) * P (basis j) (t, false))) * s q j)
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      · exact Finset.sum_comm
    rw [hreord]
    simp_rw [hterm]
    have heval : ∀ (r : Fin m × Bool) (u : Fin m × Bool),
        (∑ i : Fin n, s r i * P (basis i) u) = (Pi.single r (1 : ZMod 2) : D) u := by
      intro r u
      have h1 := congrArg (fun f : (Fin m × Bool) → ZMod 2 => f u) (hP_s r)
      have h2 : (∑ i : Fin n, s r i • P (basis i)) u = ∑ i : Fin n, s r i * P (basis i) u := by
        change (∑ i : Fin n, (fun x : Fin m × Bool => s r i * P (basis i) x)) u = _
        rw [Finset.sum_apply]
      rw [← h2, h1]
    simp_rw [heval]
    simp only [Omega, Matrix.of_apply]
    by_cases hpq : p.1 = q.1 ∧ p.2 ≠ q.2
    · rw [if_pos hpq]
      rw [Finset.sum_eq_single p.1]
      · rcases p with ⟨t0, b0⟩
        rcases q with ⟨t1, b1⟩
        simp only at hpq
        rcases hpq with ⟨rfl, hne⟩
        cases b0 <;> cases b1 <;> simp at hne ⊢
      · intro t _ ht
        have h1 : (t, false) ≠ p := fun h => ht (congrArg Prod.fst h)
        have h2 : (t, true) ≠ p := fun h => ht (congrArg Prod.fst h)
        simp [Pi.single_apply, h1, h2]
      · intro h; exact (h (Finset.mem_univ p.1)).elim
    · rw [if_neg hpq]
      apply Finset.sum_eq_zero
      intro t _
      by_cases hp1 : (t, false) = p
      · by_cases hq1 : (t, true) = q
        · exfalso; apply hpq
          rw [← hp1, ← hq1]; exact ⟨rfl, by simp⟩
        · have hp2 : (t, true) ≠ p := by rw [← hp1]; simp
          simp [Pi.single_apply, hp2, hq1]
      · by_cases hp2 : (t, true) = p
        · by_cases hq2 : (t, false) = q
          · exfalso; apply hpq
            rw [← hp2, ← hq2]; exact ⟨rfl, by simp⟩
          · simp [Pi.single_apply, hp1, hq2]
        · simp [Pi.single_apply, hp1, hp2]
  let A : Matrix (Fin m × Bool) (Fin m × Bool) (ZMod 2) := Qᵀ * K * Q
  have hAalt : IsAlt A := isAlt_conj hKalt Q
  obtain ⟨a0, ha0⟩ := exists_invertible_shift m A hAalt
  let a : H := fun t => a0 t + 1
  have hpart1 : ∀ w : H, 2 * wt (w + a) ≤ (K + omega w).rank := by
    intro w
    have hsplit : A + Omega a0 = (A + Omega w) + Omega (w + a0) := by
      rw [add_assoc, ← omega_add]
      congr 1
      congr 1
      ext t
      change a0 t = w t + (w t + a0 t)
      rw [← add_assoc, z2_add_self, zero_add]
    have hfull : (A + Omega a0).rank = 2 * m := by
      have := rank_full_of_isUnit_det (A + Omega a0) ha0
      simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm] using this
    have hsubadd : (A + Omega a0).rank ≤ (A + Omega w).rank + (Omega (w + a0)).rank := by
      rw [hsplit]
      have hsub_rng : LinearMap.range ((A + Omega w) + Omega (w + a0)).mulVecLin ≤
          LinearMap.range (A + Omega w).mulVecLin ⊔ LinearMap.range (Omega (w + a0)).mulVecLin := by
        rintro y ⟨x, rfl⟩
        change ((A + Omega w) + Omega (w + a0)).mulVec x ∈ _
        rw [Matrix.add_mulVec]
        exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range (A + Omega w).mulVecLin) (LinearMap.range (Omega (w + a0)).mulVecLin)
      have hle := Submodule.finrank_mono hsub_rng
      change Module.finrank (ZMod 2) (LinearMap.range ((A + Omega w) + Omega (w + a0)).mulVecLin) ≤
        Module.finrank (ZMod 2) (LinearMap.range (A + Omega w).mulVecLin) +
        Module.finrank (ZMod 2) (LinearMap.range (Omega (w + a0)).mulVecLin)
      omega
    have hom : (Omega (w + a0)).rank ≤ 2 * wt (w + a0) := rank_Omega_le (w + a0)
    have hcomp : wt (w + a) + wt (w + a0) = m := by
      have h1 := card_filter_compl (Finset.univ : Finset (Fin m)) (fun t => (w + a0) t ≠ 0)
      have hfeq : Finset.univ.filter (fun t : Fin m => (w + a) t ≠ 0) =
          Finset.univ.filter (fun t : Fin m => ¬ (w + a0) t ≠ 0) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        change w t + (a0 t + 1) ≠ 0 ↔ w t + a0 t = 0
        rcases z2_eq_zero_or_one (w t) with hw | hw <;>
        rcases z2_eq_zero_or_one (a0 t) with ha' | ha' <;>
        simp [hw, ha'] <;> decide
      dsimp only [wt]
      rw [hfeq]
      simpa [add_comm] using h1
    have hpull_le : (A + Omega w).rank ≤ (K + omega w).rank := by
      have hEq : A + Omega w = Qᵀ * (K + omega w) * Q := by
        rw [Matrix.mul_add, Matrix.add_mul, hpull_omega w]
      rw [hEq]
      exact (Matrix.rank_mul_le_left (Qᵀ * (K + omega w)) Q).trans (Matrix.rank_mul_le_right Qᵀ (K + omega w))
    omega
  refine ⟨⟨a, hpart1⟩, ?_⟩
  intro j C
  have hstep1 : (∑ u : Fin j → ZMod 2, (1 : ℚ) / 2 ^ ((K + omega (C u)).rank / 2)) ≤
      ∑ u : Fin j → ZMod 2, (1 : ℚ) / 2 ^ (wt (C u + a)) := by
    refine Finset.sum_le_sum fun u _ => ?_
    have hle : wt (C u + a) ≤ (K + omega (C u)).rank / 2 := by
      have := hpart1 (C u)
      omega
    have hpow : (2 : ℚ) ^ (wt (C u + a)) ≤ (2 : ℚ) ^ ((K + omega (C u)).rank / 2) :=
      pow_le_pow_right₀ (by norm_num) hle
    exact one_div_le_one_div_of_le (by positivity) hpow
  exact hstep1.trans (weight_shift_sum_le m j C a)

end PEqualNP.Outside.L_lib_932

theorem PEqualNP.Outside.L_lib_932 : (∀ m n : ℕ,
  let F := ZMod 2
  let V := Fin n → F
  let H := Fin m → F
  let D := (Fin m × Bool) → F
  let M := Matrix (Fin n) (Fin n) F
  let basis := fun (i j : Fin n) => if i = j then (1 : F) else 0
  let wt := fun (w : H) => ((Finset.univ : Finset (Fin m)).filter (fun t => w t ≠ 0)).card
  ∀ P : V →ₗ[F] D, Function.Surjective P →
    let omega := fun (w : H) => Matrix.of (fun i j : Fin n =>
      ∑ t : Fin m, w t * (P (basis i) (t,false) * P (basis j) (t,true) +
        P (basis i) (t,true) * P (basis j) (t,false)))
    ∀ K : M, (∀ i, K i i = 0) → (∀ i j, K i j = K j i) →
      (∃ a : H, ∀ w : H, 2 * wt (w+a) ≤ (K + omega w).rank) ∧
      ∀ (j : ℕ) (C : (Fin j → F) →ₗ[F] H),
        (∑ u : Fin j → F, (1 : ℚ) / 2^((K + omega (C u)).rank / 2)) ≤
          ∑ u : Fin j → F, (1 : ℚ) / 2^(wt (C u))) :=
  PEqualNP.Outside.L_lib_932.main
