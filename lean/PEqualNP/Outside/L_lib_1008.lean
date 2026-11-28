import Mathlib
import PEqualNP.Defs

-- Credit: the block rank bound two_rank_le is adapted from rankBlockBoundsAux in the merged
-- proof PEqualNP.Outside.L_lib_923 (upstream main).

namespace PEqualNP.Outside.L_lib_1008

open Matrix Module

lemma z2_one_of_ne {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

theorem pivots {X ι : Type} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    [Fintype ι] (bX : Basis ι (ZMod 2) X) (U : Submodule (ZMod 2) X) :
    ∃ N : Finset ι, N.card ≤ finrank (ZMod 2) (X ⧸ U) ∧
      ∀ x : X, ∃ u ∈ U, ∀ t, t ∉ N → bX.repr (x - u) t = 0 := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (ZMod 2) (U.mkQ ∘ bX)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have htop : Submodule.span (ZMod 2) (Set.range ((U.mkQ ∘ bX) ∘ a)) = ⊤ := by
    rw [hsp, Set.range_comp, Submodule.span_image, bX.span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ]
    exact hli.fintype_card_le_finrank
  · intro x
    have hx : U.mkQ x ∈ Submodule.span (ZMod 2) (Set.range ((U.mkQ ∘ bX) ∘ a)) := by
      rw [htop]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hx
    refine ⟨x - ∑ i, c i • bX (a i), ?_, ?_⟩
    · have h0 : U.mkQ (x - ∑ i, c i • bX (a i)) = 0 := by
        rw [map_sub, map_sum, ← hc]
        simp
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    · intro t ht
      have h : ∀ i, a i ≠ t := fun i hi => ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [sub_sub_cancel, map_sum]
      simp [h]

lemma two_rank_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι (ZMod 2)) (C : Matrix ι κ (ZMod 2)) :
    2 * C.rank ≤ (fromBlocks A C C.transpose (0 : Matrix κ κ (ZMod 2))).rank := by
  classical
  let X : Matrix (ι ⊕ κ) (ι ⊕ κ) (ZMod 2) := fromBlocks A C C.transpose 0
  change 2 * C.rank ≤ X.rank
  let L := LinearMap.range X.mulVecLin
  let R := LinearMap.range C.transpose.mulVecLin
  let U := LinearMap.range C.mulVecLin
  have hX (x : ι ⊕ κ → ZMod 2) :
      X.mulVecLin x = Sum.elim (A *ᵥ (x ∘ Sum.inl) + C *ᵥ (x ∘ Sum.inr))
        (C.transpose *ᵥ (x ∘ Sum.inl)) := by
    simp [X, Matrix.mulVecLin_apply, fromBlocks_mulVec]
  let p : L →ₗ[ZMod 2] (κ → ZMod 2) :=
    (LinearMap.funLeft (ZMod 2) (ZMod 2) Sum.inr).domRestrict L
  let φ : L →ₗ[ZMod 2] R := p.codRestrict R (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    refine ⟨x ∘ Sum.inl, ?_⟩
    funext j
    change (C.transpose *ᵥ (x ∘ Sum.inl)) j = X.mulVecLin x (Sum.inr j)
    rw [hX] <;> rfl)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    let z : ι ⊕ κ → ZMod 2 := Sum.elim x 0
    refine ⟨⟨X.mulVecLin z, LinearMap.mem_range_self _ z⟩, ?_⟩
    apply Subtype.ext
    funext j
    change X.mulVecLin z (Sum.inr j) = (C.transpose *ᵥ x) j
    rw [hX] <;> rfl
  let e : (ι → ZMod 2) →ₗ[ZMod 2] (ι ⊕ κ → ZMod 2) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := fun x y => by
        funext j
        cases j <;> simp
      map_smul' := fun s x => by
        funext j
        cases j <;> simp }
  let e' : U →ₗ[ZMod 2] L := (e.domRestrict U).codRestrict L (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    let z : ι ⊕ κ → ZMod 2 := Sum.elim 0 x
    refine ⟨z, ?_⟩
    change X.mulVecLin z = Sum.elim (C *ᵥ x) 0
    rw [hX]
    have hz : z ∘ Sum.inl = 0 := rfl
    have hz' : z ∘ Sum.inr = x := rfl
    simp [hz, hz'])
  let ι' : U →ₗ[ZMod 2] LinearMap.ker φ := e'.codRestrict _ (by
    intro u
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    rfl)
  have hι : Function.Injective ι' := by
    intro u v h
    apply Subtype.ext
    funext j
    exact congrArg (fun y : LinearMap.ker φ => y.1.1 (Sum.inl j)) h
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at hrn
  change C.transpose.rank + Module.finrank (ZMod 2) (LinearMap.ker φ) = X.rank at hrn
  rw [rank_transpose] at hrn
  have hl := LinearMap.finrank_le_finrank_of_injective hι
  change C.rank ≤ Module.finrank (ZMod 2) (LinearMap.ker φ) at hl
  omega

lemma rank_add_le' {ι : Type} [Fintype ι] (A B : Matrix ι ι (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_sum_le {ι α : Type} [Fintype ι] (s : Finset α) (f : α → Matrix ι ι (ZMod 2)) :
    (∑ j ∈ s, f j).rank ≤ ∑ j ∈ s, (f j).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' _ _).trans (by omega)

lemma rank_comb_le {ι : Type} [Fintype ι] {k t : ℕ} (R : Fin t → Matrix ι ι (ZMod 2))
    (hR : ∀ i, (R i).rank ≤ 2) (e : Fin k → Fin t) (w : Fin k → ZMod 2) :
    (∑ j, w j • R (e j)).rank ≤ 2 * (Finset.univ.filter (fun j => w j ≠ 0)).card := by
  classical
  have h : ∑ j, w j • R (e j) = ∑ j ∈ Finset.univ.filter (fun j => w j ≠ 0), R (e j) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : w j = 0
    · simp [hj]
    · simp [hj, z2_one_of_ne hj]
  rw [h]
  refine (rank_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => by simpa using hR (e j))

theorem main (n m : ℕ) (S : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (B P : Submodule (ZMod 2) (Matrix (Fin n) (Fin m) (ZMod 2))) (hBP : Disjoint B P) (t : ℕ)
    (R : Fin t → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) (ZMod 2)) (hR : ∀ i, (R i).rank ≤ 2)
    (hsp : ∀ A ∈ S, ∀ K ∈ B ⊔ P,
      fromBlocks A K K.transpose (0 : Matrix (Fin m) (Fin m) (ZMod 2)) ∈
        Submodule.span (ZMod 2) (Set.range R)) :
    finrank (ZMod 2) S + finrank (ZMod 2) B ≤ t ∧ ∃ k : ℕ,
      k = t - (finrank (ZMod 2) S + finrank (ZMod 2) B) ∧
      ∃ (e : Fin k ↪ Fin t) (a : P →ₗ[ZMod 2] S) (b : P →ₗ[ZMod 2] B)
        (c : P →ₗ[ZMod 2] (Fin k → ZMod 2)),
        Function.Injective c ∧ ∀ K : P,
          fromBlocks (a K : Matrix (Fin n) (Fin n) (ZMod 2))
              ((K : Matrix (Fin n) (Fin m) (ZMod 2)) + (b K : Matrix (Fin n) (Fin m) (ZMod 2)))
              ((K : Matrix (Fin n) (Fin m) (ZMod 2)) + (b K : Matrix (Fin n) (Fin m) (ZMod 2))).transpose
              (0 : Matrix (Fin m) (Fin m) (ZMod 2)) = ∑ j, c K j • R (e j) ∧
          ((K : Matrix (Fin n) (Fin m) (ZMod 2)) + (b K : Matrix (Fin n) (Fin m) (ZMod 2))).rank ≤
            (Finset.univ.filter (fun j => c K j ≠ 0)).card := by
  classical
  let Xl : (Matrix (Fin n) (Fin n) (ZMod 2) × Matrix (Fin n) (Fin m) (ZMod 2)) →ₗ[ZMod 2]
      Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) (ZMod 2) :=
    { toFun := fun x => fromBlocks x.1 x.2 x.2.transpose 0
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, transpose_add, fromBlocks_add, add_zero]
      map_smul' := fun r x => by
        simp only [Prod.smul_fst, Prod.smul_snd, transpose_smul, fromBlocks_smul, smul_zero,
          RingHom.id_apply] }
  have hXl : ∀ x, Xl x = fromBlocks x.1 x.2 x.2.transpose 0 := fun x => rfl
  have hXinj : ∀ x y, Xl x = Xl y → x = y := by
    intro x y h
    rw [hXl, hXl, fromBlocks_inj] at h
    exact Prod.ext h.1 h.2.1
  let E := S × ↥(B ⊔ P)
  let g : E →ₗ[ZMod 2] Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) (ZMod 2) :=
    Xl ∘ₗ (S.subtype.prodMap (B ⊔ P).subtype)
  have hg : ∀ x : E, g x = Xl ((x.1 : Matrix (Fin n) (Fin n) (ZMod 2)),
      (x.2 : Matrix (Fin n) (Fin m) (ZMod 2))) := fun x => rfl
  let φ := Fintype.linearCombination (ZMod 2) R
  have hφ : ∀ w, φ w = ∑ i, w i • R i := fun w => Fintype.linearCombination_apply _ _ w
  have hrg : ∀ x : E, g x ∈ LinearMap.range φ := by
    rintro ⟨⟨A, hA⟩, ⟨K, hK⟩⟩
    rw [Fintype.range_linearCombination]
    exact hsp A hA K hK
  obtain ⟨h, hh⟩ := Module.projective_lifting_property φ.rangeRestrict
    (g.codRestrict (LinearMap.range φ) hrg) (LinearMap.surjective_rangeRestrict φ)
  have hφh : ∀ x, φ (h x) = g x := fun x => congrArg Subtype.val (LinearMap.congr_fun hh x)
  let ι1 : (S × B) →ₗ[ZMod 2] E :=
    LinearMap.prodMap LinearMap.id (Submodule.inclusion (le_sup_left : B ≤ B ⊔ P))
  let hι := h ∘ₗ ι1
  have hinj : Function.Injective hι := by
    intro x y hxy
    have h1 : φ (h (ι1 x)) = φ (h (ι1 y)) := congrArg φ hxy
    rw [hφh, hφh, hg, hg] at h1
    have h2 := hXinj _ _ h1
    simp only [Prod.mk.injEq] at h2
    apply Prod.ext
    · exact Subtype.ext h2.1
    · exact Subtype.ext h2.2
  let C := LinearMap.range hι
  have hCdim : finrank (ZMod 2) C = finrank (ZMod 2) S + finrank (ZMod 2) B := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod]
  have hCle : finrank (ZMod 2) C ≤ t := by
    have := Submodule.finrank_le C
    rwa [Module.finrank_fin_fun] at this
  have hquot := Submodule.finrank_quotient_add_finrank C
  rw [Module.finrank_fin_fun] at hquot
  refine ⟨hCdim ▸ hCle, ?_⟩
  obtain ⟨N, hNcard, hNred⟩ := pivots (Pi.basisFun (ZMod 2) (Fin t)) C
  simp only [Pi.basisFun_repr] at hNred
  let k := N.card
  let e0 : Fin k ↪ Fin t := (N.orderEmbOfFin rfl).toEmbedding
  have he0N : ∀ j, e0 j ∈ N := fun j => N.orderEmbOfFin_mem rfl j
  have hNe0 : ∀ i ∈ N, ∃ j, e0 j = i := by
    intro i hi
    have : i ∈ Set.range (N.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hi
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj⟩
  let ext := Fintype.linearCombination (ZMod 2)
    (fun j : Fin k => (Pi.single (e0 j) (1 : ZMod 2) : Fin t → ZMod 2))
  have hext : ∀ w i, ext w i = ∑ j, w j * (Pi.single (e0 j) (1 : ZMod 2) : Fin t → ZMod 2) i := by
    intro w i
    simp [ext, Fintype.linearCombination_apply, Finset.sum_apply]
  have hφext : ∀ w, φ (ext w) = ∑ j, w j • R (e0 j) := by
    intro w
    simp only [ext, Fintype.linearCombination_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hφ]
    congr 1
    rw [Finset.sum_eq_single (e0 j)]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hsupp : ∀ y : Fin t → ZMod 2, (∀ i, i ∉ N → y i = 0) → ext (fun j => y (e0 j)) = y := by
    intro y hy
    funext i
    rw [hext]
    by_cases hi : i ∈ N
    · obtain ⟨j0, hj0⟩ := hNe0 i hi
      rw [Finset.sum_eq_single j0]
      · simp [hj0]
      · intro b _ hb
        have : e0 b ≠ i := fun h' => hb (e0.injective (h'.trans hj0.symm))
        simp [Pi.single_apply, this.symm]
      · simp
    · rw [hy i hi]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have : e0 j ≠ i := fun h' => hi (h' ▸ he0N j)
      simp [Pi.single_apply, this.symm]
  let jm := C.mkQ ∘ₗ ext
  have hjs : Function.Surjective jm := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective C z
    obtain ⟨u, hu, hxu⟩ := hNred x
    refine ⟨fun j => (x - u) (e0 j), ?_⟩
    change C.mkQ (ext _) = C.mkQ x
    have hu0 : C.mkQ u = 0 := by
      rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero C).mpr hu
    rw [hsupp _ hxu, map_sub, hu0, sub_zero]
  have hkle := LinearMap.finrank_le_finrank_of_surjective hjs
  rw [Module.finrank_fin_fun] at hkle
  have hk : k = t - (finrank (ZMod 2) S + finrank (ZMod 2) B) := by
    change N.card = _
    omega
  have hji : Function.Injective jm := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hjs
    · rw [Module.finrank_fin_fun]; change N.card = _; omega
  let rr := (LinearEquiv.ofBijective jm ⟨hji, hjs⟩).symm
  have hrr : ∀ z, jm (rr z) = z := fun z => (LinearEquiv.ofBijective jm ⟨hji, hjs⟩).apply_symm_apply z
  let ι2 : P →ₗ[ZMod 2] E :=
    LinearMap.prod 0 (Submodule.inclusion (le_sup_right : P ≤ B ⊔ P))
  let c0 : P →ₗ[ZMod 2] (Fin k → ZMod 2) := rr.toLinearMap ∘ₗ C.mkQ ∘ₗ h ∘ₗ ι2
  have hmem : ∀ K, (ext ∘ₗ c0 - h ∘ₗ ι2) K ∈ C := by
    intro K
    have h1 : C.mkQ (ext (c0 K)) = C.mkQ (h (ι2 K)) := hrr _
    simp only [Submodule.mkQ_apply] at h1
    exact (Submodule.Quotient.eq C).mp h1
  let u : P →ₗ[ZMod 2] C := (ext ∘ₗ c0 - h ∘ₗ ι2).codRestrict C hmem
  let eC := LinearEquiv.ofInjective hι hinj
  let d : P →ₗ[ZMod 2] (S × B) := eC.symm.toLinearMap ∘ₗ u
  have hd : ∀ K, hι (d K) = ext (c0 K) - h (ι2 K) := by
    intro K
    have := eC.apply_symm_apply (u K)
    exact congrArg Subtype.val this
  have hkey : ∀ K, φ (ext (c0 K)) = fromBlocks ((d K).1 : Matrix (Fin n) (Fin n) (ZMod 2))
      ((K : Matrix (Fin n) (Fin m) (ZMod 2)) + ((d K).2 : Matrix (Fin n) (Fin m) (ZMod 2)))
      ((K : Matrix (Fin n) (Fin m) (ZMod 2)) + ((d K).2 : Matrix (Fin n) (Fin m) (ZMod 2))).transpose 0 := by
    intro K
    have h1 : ext (c0 K) = h (ι1 (d K) + ι2 K) := by
      rw [map_add]; change _ = hι (d K) + _; rw [hd]; abel
    have e1 : ((ι1 (d K) + ι2 K).1 : Matrix (Fin n) (Fin n) (ZMod 2)) = (d K).1 := by
      show ((d K).1 : Matrix (Fin n) (Fin n) (ZMod 2)) + 0 = _
      exact add_zero _
    have e2 : ((ι1 (d K) + ι2 K).2 : Matrix (Fin n) (Fin m) (ZMod 2)) = (K : _) + (d K).2 := by
      show ((d K).2 : Matrix (Fin n) (Fin m) (ZMod 2)) + (K : Matrix (Fin n) (Fin m) (ZMod 2)) = _
      exact add_comm _ _
    rw [h1, hφh, hg, hXl]
    simp only [e1, e2]
  refine ⟨k, hk, e0, LinearMap.fst _ _ _ ∘ₗ d, LinearMap.snd _ _ _ ∘ₗ d, c0, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro K hK
    have h1 := hkey K
    rw [hK, map_zero, map_zero] at h1
    have h2 : Xl 0 = Xl ((d K).1, (K : Matrix (Fin n) (Fin m) (ZMod 2)) + (d K).2) := by
      rw [map_zero, hXl]; exact h1
    have h3 := congrArg Prod.snd (hXinj _ _ h2)
    simp only [Prod.snd_zero] at h3
    have hKB : (K : Matrix (Fin n) (Fin m) (ZMod 2)) ∈ B := by
      have : (K : Matrix (Fin n) (Fin m) (ZMod 2)) = -((d K).2 : Matrix (Fin n) (Fin m) (ZMod 2)) :=
        eq_neg_of_add_eq_zero_left h3.symm
      rw [this]; exact B.neg_mem (d K).2.2
    exact Subtype.ext ((Submodule.disjoint_def.mp hBP) _ hKB K.2)
  · intro K
    have h1 := hkey K
    rw [hφext] at h1
    refine ⟨?_, ?_⟩
    · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
      exact h1.symm
    · have h2 := two_rank_le ((d K).1 : Matrix (Fin n) (Fin n) (ZMod 2))
        ((K : Matrix (Fin n) (Fin m) (ZMod 2)) + ((d K).2 : Matrix (Fin n) (Fin m) (ZMod 2)))
      rw [← h1] at h2
      have h3 := rank_comb_le R hR e0 (c0 K)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply]
      omega


lemma z2_add_eq_zero {a b : ZMod 2} : a + b = 0 ↔ b = a := by
  revert a b; decide

def chi (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  revert a b; decide

lemma chi_add_one (a : ZMod 2) : chi (a + 1) = - chi a := by
  revert a; decide

lemma sum_chi {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (f : V →ₗ[ZMod 2] ZMod 2) :
    ∑ K, chi (f K) = if f = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with hf
  · subst hf; simp [chi]
  · obtain ⟨K0, hK0⟩ : ∃ K0, f K0 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hf (LinearMap.ext hcon)
    have h1 : f K0 = 1 := z2_one_of_ne hK0
    have hs : ∑ K, chi (f (K + K0)) = ∑ K, chi (f K) :=
      Fintype.sum_equiv (Equiv.addRight K0) _ _ (fun K => rfl)
    simp only [map_add, h1, chi_add_one, Finset.sum_neg_distrib] at hs
    linarith

lemma wt_chi {u : ℕ} (v : Fin u → ZMod 2) :
    ∑ j, chi (v j) = (u : ℤ) - 2 * ((Finset.univ.filter (fun j => v j ≠ 0)).card : ℤ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  have hu : (u : ℤ) = ∑ _j : Fin u, (1 : ℤ) := by simp
  rw [hu, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold chi
  by_cases h : v j = 0
  · simp [h]
  · simp [h]

theorem perm_of_wt {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {u : ℕ}
    (c c' : V →ₗ[ZMod 2] (Fin u → ZMod 2)) (hfull : ∀ j, ∃ K, c K j ≠ 0)
    (hle : ∀ K, (Finset.univ.filter (fun j => c K j ≠ 0)).card ≤
      (Finset.univ.filter (fun j => c' K j ≠ 0)).card) :
    ∃ σ : Fin u ≃ Fin u, ∀ K j, c' K (σ j) = c K j := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let cf : Fin u → (V →ₗ[ZMod 2] ZMod 2) := fun j => LinearMap.proj j ∘ₗ c
  let cf' : Fin u → (V →ₗ[ZMod 2] ZMod 2) := fun j => LinearMap.proj j ∘ₗ c'
  have hcf : ∀ j K, cf j K = c K j := fun j K => rfl
  have hcf' : ∀ j K, cf' j K = c' K j := fun j K => rfl
  have hne : ∀ j, cf j ≠ 0 := by
    intro j h0
    obtain ⟨K, hK⟩ := hfull j
    apply hK
    rw [← hcf, h0]
    rfl
  have hsum : ∀ (d : Fin u → (V →ₗ[ZMod 2] ZMod 2)) (f : V →ₗ[ZMod 2] ZMod 2),
      ∑ K, chi (f K) * ∑ j, chi (d j K) =
        (Fintype.card V : ℤ) * ((Finset.univ.filter (fun j => d j = f)).card : ℤ) := by
    intro d f
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ j, ∑ K, chi (f K) * chi (d j K) =
        if d j = f then (Fintype.card V : ℤ) else 0 := by
      intro j
      have h1 : ∀ K, chi (f K) * chi (d j K) = chi ((f + d j) K) := by
        intro K; rw [LinearMap.add_apply, chi_add]
      simp only [h1, sum_chi]
      have h2 : (f + d j = 0) ↔ (d j = f) := by
        constructor
        · intro h; ext K
          have := LinearMap.congr_fun h K
          simp only [LinearMap.add_apply, LinearMap.zero_apply] at this
          exact z2_add_eq_zero.mp this
        · intro h; ext K
          simp only [LinearMap.add_apply, LinearMap.zero_apply, h]
          exact z2_add_eq_zero.mpr rfl
      simp only [h2]
    simp only [h3]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have hz : ∀ j, ∑ K, chi (cf j K) = 0 := by
    intro j; rw [sum_chi, ite_eq_right_iff.mpr (fun h => absurd h (hne j))]
  have hnn : ∀ j, 0 ≤ ∑ K, chi (cf' j K) := by
    intro j; rw [sum_chi]; split_ifs <;> positivity
  have hterm : ∀ K, ∑ j, chi (cf' j K) - ∑ j, chi (cf j K) ≤ 0 := by
    intro K
    have h1 := wt_chi (c K)
    have h2 := wt_chi (c' K)
    have h3 := hle K
    simp only [hcf, hcf']
    rw [h1, h2]
    have : ((Finset.univ.filter (fun j => c K j ≠ 0)).card : ℤ) ≤
        ((Finset.univ.filter (fun j => c' K j ≠ 0)).card : ℤ) := by exact_mod_cast h3
    linarith
  have htot : ∑ K, (∑ j, chi (cf' j K) - ∑ j, chi (cf j K)) = 0 := by
    apply le_antisymm (Finset.sum_nonpos (fun K _ => hterm K))
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (f := fun K j => chi (cf j K))]
    simp only [hz, Finset.sum_const_zero, sub_zero]
    exact Finset.sum_nonneg (fun j _ => hnn j)
  have heq : ∀ K, ∑ j, chi (cf' j K) = ∑ j, chi (cf j K) := by
    intro K
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun K _ => hterm K)).mp htot K (Finset.mem_univ _)
    linarith
  have hcard : ∀ f : V →ₗ[ZMod 2] ZMod 2, (Finset.univ.filter (fun j => cf j = f)).card =
      (Finset.univ.filter (fun j => cf' j = f)).card := by
    intro f
    have h1 := hsum cf f
    have h2 := hsum cf' f
    simp only [heq] at h2
    rw [h1] at h2
    have hpos : (0 : ℤ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have := mul_left_cancel₀ hpos.ne' h2
    exact_mod_cast this
  let efib : ∀ f, {j // cf j = f} ≃ {j // cf' j = f} := fun f =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact hcard f)
  let σ : Fin u ≃ Fin u := Equiv.ofFiberEquiv (f := cf) (g := cf') efib
  refine ⟨σ, fun K j => ?_⟩
  have := Equiv.ofFiberEquiv_map (f := cf) (g := cf') efib j
  rw [← hcf', ← hcf]
  exact LinearMap.congr_fun this K

end PEqualNP.Outside.L_lib_1008

open PEqualNP.Outside.L_lib_1008 in
theorem PEqualNP.Outside.L_lib_1008 : let F := ZMod 2
∀ n m : ℕ,
  let T := Matrix (Fin n) (Fin n) F
  let M := Matrix (Fin n) (Fin m) F
  let J := Fin n ⊕ Fin m
  let H := Matrix J J F
  let X := fun (A : T) (K : M) =>
    Matrix.fromBlocks A K K.transpose (0 : Matrix (Fin m) (Fin m) F)
  let wt := fun {k : ℕ} (v : Fin k → F) =>
    (Finset.univ.filter (fun j => v j ≠ 0)).card
  ∀ (S : Submodule F T) (P : Submodule F M) (u : ℕ)
    (c : P →ₗ[F] (Fin u → F)),
    (∀ j, ∃ K : P, c K j ≠ 0) → (∀ K : P, wt (c K) = (K : M).rank) →
    let t := Module.finrank F S + u
    ∀ (R : Fin t → H), (∀ j, (R j).rank ≤ 2) →
      (∀ A ∈ S, ∀ K ∈ P, X A K ∈ Submodule.span F (Set.range R)) →
      ∃ (e : Fin u ↪ Fin t) (a : P →ₗ[F] S), ∀ K : P,
        X (a K : T) (K : M) = ∑ j, c K j • R (e j) := by
  intro F n m T M J H X wt S P u c hfull hwt t R hR hsp
  have hsp' : ∀ A ∈ S, ∀ K ∈ (⊥ : Submodule (ZMod 2) (Matrix (Fin n) (Fin m) (ZMod 2))) ⊔ P,
      Matrix.fromBlocks A K K.transpose (0 : Matrix (Fin m) (Fin m) (ZMod 2)) ∈
        Submodule.span (ZMod 2) (Set.range R) := by
    intro A hA K hK
    rw [bot_sup_eq] at hK
    exact hsp A hA K hK
  obtain ⟨_, k, hk, e, a, b, c', _, hK⟩ := main n m S ⊥ P disjoint_bot_left t R hR hsp'
  have ht : t = Module.finrank (ZMod 2) S + u := rfl
  have hbot : Module.finrank (ZMod 2)
      (⊥ : Submodule (ZMod 2) (Matrix (Fin n) (Fin m) (ZMod 2))) = 0 := finrank_bot _ _
  have hku : k = u := by
    rw [hk, hbot, add_zero, ht]
    exact Nat.add_sub_cancel_left _ _
  subst hku
  have hb : ∀ K, (b K : Matrix (Fin n) (Fin m) (ZMod 2)) = 0 := fun K =>
    (Submodule.mem_bot (ZMod 2)).mp (b K).2
  have hle : ∀ K, (Finset.univ.filter (fun j => c K j ≠ 0)).card ≤
      (Finset.univ.filter (fun j => c' K j ≠ 0)).card := by
    intro K
    have h1 := (hK K).2
    rw [hb, add_zero] at h1
    exact le_trans (hwt K).le h1
  obtain ⟨σ, hσ⟩ := perm_of_wt c c' hfull hle
  refine ⟨σ.toEmbedding.trans e, a, fun K => ?_⟩
  have h1 := (hK K).1
  rw [hb, add_zero] at h1
  calc X (a K : T) (K : M) = ∑ j, c' K j • R (e j) := h1
    _ = ∑ j, c' K (σ j) • R (e (σ j)) := (Equiv.sum_comp σ (fun j => c' K j • R (e j))).symm
    _ = _ := by simp [hσ]
