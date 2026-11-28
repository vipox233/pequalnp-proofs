import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_991_aux

open LinearMap Submodule

section LinearHelpers

variable {K : Type} [Field K]

lemma exists_right_inv_on_range {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (f : U →ₗ[K] W) :
    ∃ g : W →ₗ[K] U, f.comp (g.comp f) = f ∧ g.comp (f.comp g) = g := by
  have hsurj : Function.Surjective f.rangeRestrict := f.surjective_rangeRestrict
  rcases LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_eq_top.mpr hsurj) with
    ⟨s, hs⟩
  rcases Submodule.exists_isCompl (LinearMap.range f) with ⟨Q, hQ⟩
  let π : W →ₗ[K] LinearMap.range f := Submodule.projectionOnto (LinearMap.range f) Q hQ
  let g : W →ₗ[K] U := s.comp π
  have hfs : ∀ y : LinearMap.range f, f (s y) = y.1 := by
    intro y
    have h1 : f.rangeRestrict (s y) = y := congrArg (fun φ => φ y) hs
    exact congrArg Subtype.val h1
  refine ⟨g, ?_, ?_⟩
  · apply LinearMap.ext; intro x
    simp only [comp_apply, g]
    have hπ : π (f x) = ⟨f x, mem_range_self f x⟩ :=
      Submodule.projectionOnto_apply_left hQ ⟨f x, mem_range_self f x⟩
    rw [hπ, hfs]
  · apply LinearMap.ext; intro w
    simp only [comp_apply, g]
    rw [hfs (π w)]
    have hπ : π (π w).1 = π w :=
      Submodule.projectionOnto_apply_left hQ (π w)
    rw [hπ]

lemma exists_left_inv_of_inj {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (f : U →ₗ[K] W) (hinj : Function.Injective f) :
    ∃ ψ : W →ₗ[K] U, ψ.comp f = LinearMap.id := by
  rcases Submodule.exists_isCompl (LinearMap.range f) with ⟨Q, hQ⟩
  let π : W →ₗ[K] LinearMap.range f := Submodule.projectionOnto (LinearMap.range f) Q hQ
  let e : U ≃ₗ[K] LinearMap.range f := LinearEquiv.ofInjective f hinj
  refine ⟨e.symm.toLinearMap.comp π, ?_⟩
  apply LinearMap.ext; intro u
  simp only [comp_apply, LinearEquiv.coe_coe, id_apply]
  have hπ : π (f u) = ⟨f u, mem_range_self f u⟩ :=
    Submodule.projectionOnto_apply_left hQ ⟨f u, mem_range_self f u⟩
  rw [hπ]
  exact e.symm_apply_apply u

lemma exists_section_of_surj {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (f : U →ₗ[K] W) (hsurj : Function.Surjective f) :
    ∃ s : W →ₗ[K] U, f.comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hsurj)

lemma factor_through_fin {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U] [FiniteDimensional K W]
    (T : U →ₗ[K] W) (q : ℕ) (hq : Module.finrank K (LinearMap.range T) ≤ q) :
    ∃ (L : (Fin q → K) →ₗ[K] W) (R : U →ₗ[K] (Fin q → K)), L.comp R = T := by
  let b := Module.finBasis K (LinearMap.range T)
  let r := Module.finrank K (LinearMap.range T)
  let emb : (Fin r → K) →ₗ[K] (Fin q → K) :=
    { toFun := fun v j => if hj : j.val < r then v ⟨j.val, hj⟩ else 0
      map_add' := fun x y => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }
  let proj : (Fin q → K) →ₗ[K] (Fin r → K) :=
    { toFun := fun v i => v ⟨i.val, lt_of_lt_of_le i.isLt hq⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hpe : proj.comp emb = LinearMap.id := by
    apply LinearMap.ext; intro v; funext i
    simp [proj, emb, i.isLt]
  let R : U →ₗ[K] (Fin q → K) := emb.comp (b.equivFun.toLinearMap.comp T.rangeRestrict)
  let L : (Fin q → K) →ₗ[K] W := (LinearMap.range T).subtype.comp (b.equivFun.symm.toLinearMap.comp proj)
  refine ⟨L, R, ?_⟩
  apply LinearMap.ext; intro u
  simp only [L, R, comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
  have h1 : proj (emb (b.equivFun (T.rangeRestrict u))) = b.equivFun (T.rangeRestrict u) :=
    congrArg (fun φ => φ (b.equivFun (T.rangeRestrict u))) hpe
  rw [h1, b.equivFun.symm_apply_apply]
  rfl

lemma rank_comp_le_left {U V W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K U] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (g : U →ₗ[K] V) :
    Module.finrank K (LinearMap.range (f.comp g)) ≤ Module.finrank K (LinearMap.range f) := by
  apply Submodule.finrank_mono
  rintro w ⟨u, rfl⟩
  exact ⟨g u, rfl⟩

lemma rank_comp_le_right {U V W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K U] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (g : U →ₗ[K] V) :
    Module.finrank K (LinearMap.range (f.comp g)) ≤ Module.finrank K (LinearMap.range g) := by
  have h1 : LinearMap.range (f.comp g) = Submodule.map f (LinearMap.range g) :=
    LinearMap.range_comp g f
  rw [h1]
  exact Submodule.finrank_map_le f (LinearMap.range g)

lemma finrank_map_of_inj {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U] [FiniteDimensional K W]
    (f : U →ₗ[K] W) (hf : Function.Injective f) (p : Submodule K U) :
    Module.finrank K (Submodule.map f p) = Module.finrank K p := by
  let g : p →ₗ[K] W := f.comp p.subtype
  have hrg : LinearMap.range g = Submodule.map f p := by
    ext w
    simp only [LinearMap.mem_range, Submodule.mem_map, g, comp_apply, Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨u, hu⟩, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
  rw [← hrg]
  exact (LinearEquiv.ofInjective g (hf.comp Subtype.val_injective)).symm.finrank_eq

lemma rank_eq_of_equiv {U1 U2 W1 W2 : Type*}
    [AddCommGroup U1] [Module K U1] [AddCommGroup U2] [Module K U2]
    [AddCommGroup W1] [Module K W1] [AddCommGroup W2] [Module K W2]
    [FiniteDimensional K U1] [FiniteDimensional K U2]
    [FiniteDimensional K W1] [FiniteDimensional K W2]
    (eU : U1 ≃ₗ[K] U2) (eW : W1 ≃ₗ[K] W2) (f : U1 →ₗ[K] W1) :
    Module.finrank K (LinearMap.range (eW.toLinearMap.comp (f.comp eU.symm.toLinearMap))) =
      Module.finrank K (LinearMap.range f) := by
  have h1 : LinearMap.range (f.comp eU.symm.toLinearMap) = LinearMap.range f :=
    LinearMap.range_comp_of_range_eq_top f (LinearMap.range_eq_top.mpr eU.symm.surjective)
  rw [LinearMap.range_comp, h1]
  exact LinearEquiv.finrank_map_eq eW (LinearMap.range f)

lemma finrank_submodule_prod {U1 U2 : Type*} [AddCommGroup U1] [Module K U1]
    [AddCommGroup U2] [Module K U2] [FiniteDimensional K U1] [FiniteDimensional K U2]
    (P : Submodule K U1) (Q : Submodule K U2) :
    Module.finrank K (Submodule.prod P Q) = Module.finrank K P + Module.finrank K Q := by
  let e : Submodule.prod P Q ≃ₗ[K] (P × Q) :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2, p.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod]

lemma finrank_prod_direct_sum_map {U1 U2 W1 W2 : Type*}
    [AddCommGroup U1] [Module K U1] [AddCommGroup U2] [Module K U2]
    [AddCommGroup W1] [Module K W1] [AddCommGroup W2] [Module K W2]
    [FiniteDimensional K U1] [FiniteDimensional K U2]
    [FiniteDimensional K W1] [FiniteDimensional K W2]
    (f1 : U1 →ₗ[K] W1) (f2 : U2 →ₗ[K] W2) :
    Module.finrank K (LinearMap.range (LinearMap.prodMap f1 f2)) =
      Module.finrank K (LinearMap.range f1) + Module.finrank K (LinearMap.range f2) := by
  have hker : LinearMap.ker (LinearMap.prodMap f1 f2) =
      Submodule.prod (LinearMap.ker f1) (LinearMap.ker f2) := by
    ext ⟨u1, u2⟩
    simp [LinearMap.mem_ker, Submodule.mem_prod]
  have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.prodMap f1 f2)
  have hrn1 := LinearMap.finrank_range_add_finrank_ker f1
  have hrn2 := LinearMap.finrank_range_add_finrank_ker f2
  rw [hker, finrank_submodule_prod, Module.finrank_prod] at hrn
  omega

lemma zero_core_block_rank {R C I' J' : Type*}
    [AddCommGroup R] [Module K R] [AddCommGroup C] [Module K C]
    [AddCommGroup I'] [Module K I'] [AddCommGroup J'] [Module K J']
    [FiniteDimensional K R] [FiniteDimensional K C]
    [FiniteDimensional K I'] [FiniteDimensional K J']
    (B : J' →ₗ[K] R) (D : C →ₗ[K] I') (E : J' →ₗ[K] I') :
    let M : (C × J') →ₗ[K] (R × I') :=
      { toFun := fun p => (B p.2, D p.1 + E p.2)
        map_add' := fun p q => Prod.ext (map_add B p.2 q.2) (by
          change D (p.1 + q.1) + E (p.2 + q.2) = (D p.1 + E p.2) + (D q.1 + E q.2)
          rw [map_add, map_add]; abel)
        map_smul' := fun c p => Prod.ext (map_smul B c p.2) (by
          change D (c • p.1) + E (c • p.2) = c • (D p.1 + E p.2)
          rw [map_smul, map_smul, smul_add]) }
    let ρ : LinearMap.ker B →ₗ[K] (I' ⧸ LinearMap.range D) :=
      (LinearMap.range D).mkQ.comp (E.comp (LinearMap.ker B).subtype)
    Module.finrank K (LinearMap.range M) =
      Module.finrank K (LinearMap.range D) + Module.finrank K (LinearMap.range B) +
        Module.finrank K (LinearMap.range ρ) := by
  intro M ρ
  let pr2 : LinearMap.ker M →ₗ[K] LinearMap.ker ρ :=
    { toFun := fun z =>
        ⟨⟨z.1.2, by
            have hz : M z.1 = 0 := z.2
            exact congrArg Prod.fst hz⟩,
          by
            have hz : M z.1 = 0 := z.2
            have h2 : D z.1.1 + E z.1.2 = 0 := congrArg Prod.snd hz
            simp only [LinearMap.mem_ker, ρ, comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
            refine ⟨-z.1.1, ?_⟩
            rw [map_neg]
            exact (eq_neg_of_add_eq_zero_right h2).symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hpr2_surj : Function.Surjective pr2 := by
    rintro ⟨⟨y, hyB⟩, hyρ⟩
    simp only [LinearMap.mem_ker, ρ, comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hyρ
    rcases hyρ with ⟨x, hx⟩
    refine ⟨⟨(-x, y), ?_⟩, rfl⟩
    change (B y, D (-x) + E y) = (0, 0)
    rw [LinearMap.mem_ker.mp hyB, map_neg, hx, neg_add_cancel]
  have hpr2_range : LinearMap.range pr2 = ⊤ := LinearMap.range_eq_top.mpr hpr2_surj
  let eKer : LinearMap.ker D ≃ₗ[K] LinearMap.ker pr2 :=
    { toFun := fun x => ⟨⟨(x.1, 0), by
          change (B 0, D x.1 + E 0) = (0, 0)
          simp [LinearMap.mem_ker.mp x.2]⟩, rfl⟩
      invFun := fun z => ⟨z.1.1.1, by
        have h1 : z.1.1.2 = 0 := congrArg (fun t => t.1.1) z.2
        have h2 : D z.1.1.1 + E z.1.1.2 = 0 := congrArg Prod.snd z.1.2
        rw [h1, map_zero, add_zero] at h2
        exact h2⟩
      map_add' := fun _ _ => by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl (add_zero 0).symm
      map_smul' := fun c _ => by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl (smul_zero c).symm
      left_inv := fun _ => rfl
      right_inv := fun z => by
        apply Subtype.ext
        apply Subtype.ext
        have h1 : z.1.1.2 = 0 := congrArg (fun t => t.1.1) z.2
        exact Prod.ext rfl h1.symm }
  have hker_pr2 : Module.finrank K (LinearMap.ker pr2) = Module.finrank K (LinearMap.ker D) :=
    eKer.symm.finrank_eq
  have hrn_pr2 := LinearMap.finrank_range_add_finrank_ker pr2
  rw [hpr2_range, finrank_top, hker_pr2] at hrn_pr2
  have hrn_M := LinearMap.finrank_range_add_finrank_ker M
  have hrn_D := LinearMap.finrank_range_add_finrank_ker D
  have hrn_B := LinearMap.finrank_range_add_finrank_ker B
  have hrn_ρ := LinearMap.finrank_range_add_finrank_ker ρ
  rw [Module.finrank_prod] at hrn_M
  omega

lemma matrix_rank_eq_finrank_range {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α β K) :
    M.rank = Module.finrank K (LinearMap.range M.mulVecLin) := rfl

def finset_split_fun_equiv {α : Type*} [DecidableEq α] {I R : Finset α} (hRI : R ⊆ I) :
    (I → K) ≃ₗ[K] ((R → K) × ({a : α // a ∈ I \ R} → K)) :=
  { toFun := fun v => (fun x => v ⟨x.1, hRI x.2⟩, fun x => v ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩)
    invFun := fun p x => if hx : x.1 ∈ R then p.1 ⟨x.1, hx⟩ else p.2 ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun v => by funext ⟨a, ha⟩; dsimp only; split_ifs <;> rfl
    right_inv := fun ⟨v1, v2⟩ => by
      apply Prod.ext
      · funext ⟨a, ha⟩; simp [ha]
      · funext ⟨a, ha⟩; have hna : a ∉ R := (Finset.mem_sdiff.mp ha).2; simp [hna] }

lemma schur_rank_add {n m : ℕ} (A M : Matrix (Fin n) (Fin m) K)
    (R I : Finset (Fin n)) (C J : Finset (Fin m)) (hRI : R ⊆ I) (hCJ : C ⊆ J)
    (hagree : ∀ i ∈ I, ∀ j ∈ J, (i ∈ R ∨ j ∈ C) → M i j = A i j)
    (G : Matrix C R K)
    (hAGA : (A.submatrix (fun i : R => i.1) (fun j : C => j.1)) * G *
        (A.submatrix (fun i : R => i.1) (fun j : C => j.1)) =
        A.submatrix (fun i : R => i.1) (fun j : C => j.1))
    (hGAG : G * (A.submatrix (fun i : R => i.1) (fun j : C => j.1)) * G = G) :
    (M.submatrix (fun i : I => i.1) (fun j : J => j.1)).rank =
      (A.submatrix (fun i : R => i.1) (fun j : C => j.1)).rank +
        ((M - Matrix.of (fun i j => ∑ c : C, ∑ r : R, A i c.1 * G c r * A r.1 j)).submatrix
          (fun i : I => i.1) (fun j : J => j.1)).rank := by
  set M0 : Matrix (Fin n) (Fin m) K :=
    Matrix.of (fun i j => ∑ c : C, ∑ r : R, A i c.1 * G c r * A r.1 j)
  set A_RC : Matrix R C K := A.submatrix (fun i : R => i.1) (fun j : C => j.1)
  set I' := I \ R
  set J' := J \ C
  set eI := finset_split_fun_equiv (K := K) hRI
  set eJ := finset_split_fun_equiv (K := K) hCJ
  set f : (C → K) →ₗ[K] (R → K) := A_RC.mulVecLin
  set g : (R → K) →ₗ[K] (C → K) := G.mulVecLin
  have hfgf : ∀ x : C → K, f (g (f x)) = f x := by
    intro x
    change A_RC.mulVec (G.mulVec (A_RC.mulVec x)) = A_RC.mulVec x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAGA]
  have hgfg : ∀ w : R → K, g (f (g w)) = g w := by
    intro w
    change G.mulVec (A_RC.mulVec (G.mulVec w)) = G.mulVec w
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hGAG]
  set A_I'C : (C → K) →ₗ[K] (I' → K) :=
    (A.submatrix (fun i : I' => i.1) (fun j : C => j.1)).mulVecLin
  set A_RJ' : (J' → K) →ₗ[K] (R → K) :=
    (A.submatrix (fun i : R => i.1) (fun j : J' => j.1)).mulVecLin
  set M_I'J' : (J' → K) →ₗ[K] (I' → K) :=
    (M.submatrix (fun i : I' => i.1) (fun j : J' => j.1)).mulVecLin
  set S_I'C : (C → K) →ₗ[K] (I' → K) := A_I'C - A_I'C.comp (g.comp f)
  set S_RJ' : (J' → K) →ₗ[K] (R → K) := A_RJ' - f.comp (g.comp A_RJ')
  set S_I'J' : (J' → K) →ₗ[K] (I' → K) := M_I'J' - A_I'C.comp (g.comp A_RJ')
  let M_blk : ((C → K) × (J' → K)) →ₗ[K] ((R → K) × (I' → K)) :=
    eI.toLinearMap.comp ((M.submatrix (fun i : I => i.1) (fun j : J => j.1)).mulVecLin.comp eJ.symm.toLinearMap)
  have hM_blk_apply : ∀ (x : C → K) (y : J' → K),
      M_blk (x, y) = (f x + A_RJ' y, A_I'C x + M_I'J' y) := by
    intro x y
    have hsplit_sum : ∀ (i : I),
        ∑ j : J, M i.1 j.1 * (eJ.symm (x, y) j) =
          (∑ c : C, M i.1 c.1 * x c) + ∑ j' : J', M i.1 j'.1 * y j' := by
      intro i
      have hpart : (Finset.univ : Finset J) =
          (Finset.univ.filter (fun j : J => j.1 ∈ C)) ∪ (Finset.univ.filter (fun j : J => j.1 ∉ C)) := by
        ext j; simp; exact em _
      rw [hpart, Finset.sum_union (by rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h2 h1)]
      congr 1
      · refine Finset.sum_bij (fun j hj => (⟨j.1, (Finset.mem_filter.mp hj).2⟩ : C)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ h; exact Subtype.ext (congrArg (fun z : C => z.1) h)
        · intro c _; exact ⟨⟨c.1, hCJ c.2⟩, by simp [c.2], rfl⟩
        · intro j hj; have hjC : j.1 ∈ C := (Finset.mem_filter.mp hj).2; simp [eJ, finset_split_fun_equiv, hjC]
      · refine Finset.sum_bij (fun j hj => (⟨j.1, Finset.mem_sdiff.mpr ⟨j.2, (Finset.mem_filter.mp hj).2⟩⟩ : J')) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ h; exact Subtype.ext (congrArg (fun z : J' => z.1) h)
        · intro j' _; exact ⟨⟨j'.1, (Finset.mem_sdiff.mp j'.2).1⟩, by simp [(Finset.mem_sdiff.mp j'.2).2], rfl⟩
        · intro j hj; have hjC : j.1 ∉ C := (Finset.mem_filter.mp hj).2; simp [eJ, finset_split_fun_equiv, hjC]
    apply Prod.ext
    · funext r
      change ∑ j : J, M r.1 j.1 * (eJ.symm (x, y) j) = (∑ c : C, A r.1 c.1 * x c) + ∑ j' : J', A r.1 j'.1 * y j'
      rw [hsplit_sum ⟨r.1, hRI r.2⟩]
      congr 1
      · refine Finset.sum_congr rfl fun c _ => ?_; rw [hagree r.1 (hRI r.2) c.1 (hCJ c.2) (Or.inl r.2)]
      · refine Finset.sum_congr rfl fun j' _ => ?_; rw [hagree r.1 (hRI r.2) j'.1 (Finset.mem_sdiff.mp j'.2).1 (Or.inl r.2)]
    · funext i'
      change ∑ j : J, M i'.1 j.1 * (eJ.symm (x, y) j) = (∑ c : C, A i'.1 c.1 * x c) + ∑ j' : J', M i'.1 j'.1 * y j'
      rw [hsplit_sum ⟨i'.1, (Finset.mem_sdiff.mp i'.2).1⟩]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hagree i'.1 (Finset.mem_sdiff.mp i'.2).1 c.1 (hCJ c.2) (Or.inr c.2)]
  let S_blk : ((C → K) × (J' → K)) →ₗ[K] ((R → K) × (I' → K)) :=
    eI.toLinearMap.comp (((M - M0).submatrix (fun i : I => i.1) (fun j : J => j.1)).mulVecLin.comp eJ.symm.toLinearMap)
  have hS_blk_apply : ∀ (x : C → K) (y : J' → K),
      S_blk (x, y) = (S_RJ' y, S_I'C x + S_I'J' y) := by
    intro x y
    have hM0_apply : ∀ (i : I),
        ∑ j : J, M0 i.1 j.1 * (eJ.symm (x, y) j) =
          ∑ c : C, A i.1 c.1 * (g (f x + A_RJ' y) c) := by
      intro i
      have h1 : ∀ j : J, M0 i.1 j.1 * (eJ.symm (x, y) j) =
          ∑ c : C, A i.1 c.1 * (∑ r : R, G c r * (A r.1 j.1 * eJ.symm (x, y) j)) := by
        intro j
        simp only [M0, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => ?_
        ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      change ∑ r : R, ∑ j : J, G c r * (A r.1 j.1 * eJ.symm (x, y) j) = ∑ r : R, G c r * (f x r + A_RJ' y r)
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      have hM_r := congrFun (congrArg Prod.fst (hM_blk_apply x y)) r
      change (∑ j : J, M r.1 j.1 * eJ.symm (x, y) j) = f x r + A_RJ' y r at hM_r
      rw [← hM_r]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hagree r.1 (hRI r.2) j.1 j.2 (Or.inl r.2)]
    apply Prod.ext
    · funext r
      change (∑ j : J, (M r.1 j.1 - M0 r.1 j.1) * eJ.symm (x, y) j) = S_RJ' y r
      simp only [sub_mul, Finset.sum_sub_distrib]
      have hMr : (∑ j : J, M r.1 j.1 * eJ.symm (x, y) j) = f x r + A_RJ' y r :=
        congrFun (congrArg Prod.fst (hM_blk_apply x y)) r
      rw [hMr, hM0_apply ⟨r.1, hRI r.2⟩]
      have hf1 : (∑ c : C, A r.1 c.1 * g (f x + A_RJ' y) c) = f (g (f x + A_RJ' y)) r := rfl
      rw [hf1, map_add, map_add, hfgf x]
      simp [S_RJ']
    · funext i'
      change (∑ j : J, (M i'.1 j.1 - M0 i'.1 j.1) * eJ.symm (x, y) j) = S_I'C x i' + S_I'J' y i'
      simp only [sub_mul, Finset.sum_sub_distrib]
      have hMi : (∑ j : J, M i'.1 j.1 * eJ.symm (x, y) j) = A_I'C x i' + M_I'J' y i' :=
        congrFun (congrArg Prod.snd (hM_blk_apply x y)) i'
      rw [hMi, hM0_apply ⟨i'.1, (Finset.mem_sdiff.mp i'.2).1⟩]
      have ha1 : (∑ c : C, A i'.1 c.1 * g (f x + A_RJ' y) c) = A_I'C (g (f x + A_RJ' y)) i' := rfl
      rw [ha1, map_add, map_add]
      simp only [S_I'C, S_I'J', LinearMap.sub_apply, comp_apply, Pi.sub_apply, Pi.add_apply]
      ring
  let P : ((R → K) × (I' → K)) ≃ₗ[K] ((R → K) × (I' → K)) :=
    { toFun := fun p => (p.1, p.2 - A_I'C (g p.1))
      invFun := fun p => (p.1, p.2 + A_I'C (g p.1))
      map_add' := fun p q => Prod.ext rfl (by
        change p.2 + q.2 - A_I'C (g (p.1 + q.1)) = (p.2 - A_I'C (g p.1)) + (q.2 - A_I'C (g q.1))
        rw [map_add, map_add]; abel)
      map_smul' := fun c p => Prod.ext rfl (by
        change c • p.2 - A_I'C (g (c • p.1)) = c • (p.2 - A_I'C (g p.1))
        rw [map_smul, map_smul, smul_sub])
      left_inv := fun ⟨a, b⟩ => Prod.ext rfl (by simp)
      right_inv := fun ⟨a, b⟩ => Prod.ext rfl (by simp) }
  let Q : ((C → K) × (J' → K)) ≃ₗ[K] ((C → K) × (J' → K)) :=
    { toFun := fun p => (p.1 - g (A_RJ' p.2), p.2)
      invFun := fun p => (p.1 + g (A_RJ' p.2), p.2)
      map_add' := fun p q => Prod.ext (by
        change p.1 + q.1 - g (A_RJ' (p.2 + q.2)) = (p.1 - g (A_RJ' p.2)) + (q.1 - g (A_RJ' q.2))
        rw [map_add, map_add]; abel) rfl
      map_smul' := fun c p => Prod.ext (by
        change c • p.1 - g (A_RJ' (c • p.2)) = c • (p.1 - g (A_RJ' p.2))
        rw [map_smul, map_smul, smul_sub]) rfl
      left_inv := fun ⟨a, b⟩ => Prod.ext (by simp) rfl
      right_inv := fun ⟨a, b⟩ => Prod.ext (by simp) rfl }
  let T : ((C → K) × (J' → K)) →ₗ[K] ((R → K) × (I' → K)) :=
    P.toLinearMap.comp (M_blk.comp Q.toLinearMap)
  have hT_apply : ∀ (x : C → K) (y : J' → K),
      T (x, y) = (f x + S_RJ' y, S_I'C x + S_I'J' y) := by
    intro x y
    simp only [T, comp_apply, Q, P, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hM_blk_apply]
    apply Prod.ext
    · simp only [map_sub, S_RJ', LinearMap.sub_apply, comp_apply]
      abel
    · simp only [map_sub, map_add, S_I'C, S_I'J', LinearMap.sub_apply, comp_apply, hgfg]
      abel
  have hdom_compl : IsCompl (LinearMap.range g) (LinearMap.ker f) := by
    constructor
    · rw [disjoint_iff]
      ext x
      simp only [mem_inf, LinearMap.mem_range, LinearMap.mem_ker, Submodule.mem_bot]
      constructor
      · rintro ⟨⟨w, rfl⟩, hfw⟩
        have h1 := hgfg w
        rw [hfw, map_zero] at h1
        exact h1.symm
      · rintro rfl; exact ⟨⟨0, map_zero g⟩, map_zero f⟩
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hdecomp : x = g (f x) + (x - g (f x)) := by abel
      rw [hdecomp]
      apply Submodule.add_mem_sup
      · exact ⟨f x, rfl⟩
      · rw [LinearMap.mem_ker, map_sub, hfgf x, sub_self]
  have hcod_compl : IsCompl (LinearMap.range f) (LinearMap.ker (f.comp g)) := by
    constructor
    · rw [disjoint_iff]
      ext w
      simp only [mem_inf, LinearMap.mem_range, LinearMap.mem_ker, comp_apply, Submodule.mem_bot]
      constructor
      · rintro ⟨⟨x, rfl⟩, h0⟩
        rwa [hfgf x] at h0
      · rintro rfl; exact ⟨⟨0, map_zero f⟩, by simp⟩
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      have hdecomp : w = f (g w) + (w - f (g w)) := by abel
      rw [hdecomp]
      apply Submodule.add_mem_sup
      · exact ⟨g w, rfl⟩
      · simp only [LinearMap.mem_ker, comp_apply, map_sub, hgfg w, sub_self]
  let eC : (LinearMap.range g × LinearMap.ker f) ≃ₗ[K] (C → K) :=
    Submodule.prodEquivOfIsCompl (LinearMap.range g) (LinearMap.ker f) hdom_compl
  let eR : (LinearMap.range f × LinearMap.ker (f.comp g)) ≃ₗ[K] (R → K) :=
    Submodule.prodEquivOfIsCompl (LinearMap.range f) (LinearMap.ker (f.comp g)) hcod_compl
  let eDom : (LinearMap.range g × (LinearMap.ker f × (J' → K))) ≃ₗ[K] ((C → K) × (J' → K)) :=
    (LinearEquiv.prodAssoc K (LinearMap.range g) (LinearMap.ker f) (J' → K)).symm.trans
      (eC.prodCongr (LinearEquiv.refl K (J' → K)))
  let eCod : (LinearMap.range f × (LinearMap.ker (f.comp g) × (I' → K))) ≃ₗ[K] ((R → K) × (I' → K)) :=
    (LinearEquiv.prodAssoc K (LinearMap.range f) (LinearMap.ker (f.comp g)) (I' → K)).symm.trans
      (eR.prodCongr (LinearEquiv.refl K (I' → K)))
  let f_top : LinearMap.range g →ₗ[K] LinearMap.range f :=
    f.rangeRestrict.comp (LinearMap.range g).subtype
  have hf_top_bij : Function.Bijective f_top := by
    constructor
    · rintro ⟨_, ⟨w1, rfl⟩⟩ ⟨_, ⟨w2, rfl⟩⟩ heq
      apply Subtype.ext
      have h1 : f (g w1) = f (g w2) := congrArg Subtype.val heq
      have h2 := congrArg g h1
      rwa [hgfg w1, hgfg w2] at h2
    · rintro ⟨_, ⟨x, rfl⟩⟩
      refine ⟨⟨g (f x), ⟨f x, rfl⟩⟩, Subtype.ext (hfgf x)⟩
  have hS_RJ'_mem : ∀ y : J' → K, S_RJ' y ∈ LinearMap.ker (f.comp g) := by
    intro y
    simp only [LinearMap.mem_ker, comp_apply, S_RJ', LinearMap.sub_apply, map_sub, hgfg, sub_self]
  let S_bot : (LinearMap.ker f × (J' → K)) →ₗ[K] (LinearMap.ker (f.comp g) × (I' → K)) :=
    { toFun := fun p => (⟨S_RJ' p.2, hS_RJ'_mem p.2⟩, S_I'C p.1.1 + S_I'J' p.2)
      map_add' := fun p q => Prod.ext (Subtype.ext (map_add S_RJ' p.2 q.2)) (by
        change S_I'C (p.1.1 + q.1.1) + S_I'J' (p.2 + q.2) = (S_I'C p.1.1 + S_I'J' p.2) + (S_I'C q.1.1 + S_I'J' q.2)
        rw [map_add, map_add]; abel)
      map_smul' := fun c p => Prod.ext (Subtype.ext (map_smul S_RJ' c p.2)) (by
        change S_I'C (c • p.1.1) + S_I'J' (c • p.2) = c • (S_I'C p.1.1 + S_I'J' p.2)
        rw [map_smul, map_smul, smul_add]) }
  have hT_diag : eCod.symm.toLinearMap.comp (T.comp eDom.toLinearMap) = LinearMap.prodMap f_top S_bot := by
    apply LinearMap.ext
    rintro ⟨⟨_, ⟨w, rfl⟩⟩, ⟨⟨xk, hxk⟩, y⟩⟩
    apply eCod.injective
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have hdom_val : eDom (⟨g w, ⟨w, rfl⟩⟩, (⟨xk, hxk⟩, y)) = (g w + xk, y) := rfl
    rw [hdom_val, hT_apply]
    have hfxk : f xk = 0 := hxk
    have hS_gw : S_I'C (g w) = 0 := by
      simp only [S_I'C, LinearMap.sub_apply, comp_apply, hgfg w, sub_self]
    apply Prod.ext
    · change f (g w + xk) + S_RJ' y = f (g w) + S_RJ' y
      rw [map_add, hfxk, add_zero]
    · change S_I'C (g w + xk) + S_I'J' y = S_I'C xk + S_I'J' y
      rw [map_add, hS_gw, zero_add]
  have hS_diag : eCod.symm.toLinearMap.comp (S_blk.comp eDom.toLinearMap) = LinearMap.prodMap (0 : LinearMap.range g →ₗ[K] LinearMap.range f) S_bot := by
    apply LinearMap.ext
    rintro ⟨⟨_, ⟨w, rfl⟩⟩, ⟨⟨xk, hxk⟩, y⟩⟩
    apply eCod.injective
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have hdom_val : eDom (⟨g w, ⟨w, rfl⟩⟩, (⟨xk, hxk⟩, y)) = (g w + xk, y) := rfl
    rw [hdom_val, hS_blk_apply]
    have hS_gw : S_I'C (g w) = 0 := by
      simp only [S_I'C, LinearMap.sub_apply, comp_apply, hgfg w, sub_self]
    apply Prod.ext
    · change S_RJ' y = 0 + S_RJ' y; rw [zero_add]
    · change S_I'C (g w + xk) + S_I'J' y = S_I'C xk + S_I'J' y
      rw [map_add, hS_gw, zero_add]
  have hrank_M : (M.submatrix (fun i : I => i.1) (fun j : J => j.1)).rank =
      Module.finrank K (LinearMap.range T) := by
    have h1 := rank_eq_of_equiv eJ eI (M.submatrix (fun i : I => i.1) (fun j : J => j.1)).mulVecLin
    have h2 := rank_eq_of_equiv Q.symm P M_blk
    rw [matrix_rank_eq_finrank_range, ← h1, ← h2]
    rfl
  have hrank_T : Module.finrank K (LinearMap.range T) =
      Module.finrank K (LinearMap.range f_top) + Module.finrank K (LinearMap.range S_bot) := by
    have h1 := rank_eq_of_equiv eDom.symm eCod.symm T
    rw [← h1]
    change Module.finrank K (LinearMap.range (eCod.symm.toLinearMap.comp (T.comp eDom.toLinearMap))) = _
    rw [hT_diag, finrank_prod_direct_sum_map]
  have hrank_S : ((M - M0).submatrix (fun i : I => i.1) (fun j : J => j.1)).rank =
      Module.finrank K (LinearMap.range S_bot) := by
    have h1 := rank_eq_of_equiv eJ eI ((M - M0).submatrix (fun i : I => i.1) (fun j : J => j.1)).mulVecLin
    have h2 := rank_eq_of_equiv eDom.symm eCod.symm S_blk
    rw [matrix_rank_eq_finrank_range, ← h1, ← h2]
    change Module.finrank K (LinearMap.range (eCod.symm.toLinearMap.comp (S_blk.comp eDom.toLinearMap))) = _
    rw [hS_diag, finrank_prod_direct_sum_map]
    simp
  have hrank_ftop : Module.finrank K (LinearMap.range f_top) = A_RC.rank := by
    rw [LinearMap.range_eq_top.mpr hf_top_bij.2, finrank_top]
    rfl
  rw [hrank_M, hrank_T, hrank_ftop, hrank_S]

lemma zero_core_submatrix_ranks {n m : ℕ} (S : Matrix (Fin n) (Fin m) K)
    (R I : Finset (Fin n)) (C J : Finset (Fin m)) (hRI : R ⊆ I) (hCJ : C ⊆ J)
    (hzero : ∀ i ∈ R, ∀ j ∈ C, S i j = 0) :
    let I' := I \ R
    let J' := J \ C
    let D : (C → K) →ₗ[K] (I' → K) :=
      (S.submatrix (fun i : I' => i.1) (fun j : C => j.1)).mulVecLin
    let H : (J' → K) →ₗ[K] (R → K) :=
      (S.submatrix (fun i : R => i.1) (fun j : J' => j.1)).mulVecLin
    let E : (J' → K) →ₗ[K] (I' → K) :=
      (S.submatrix (fun i : I' => i.1) (fun j : J' => j.1)).mulVecLin
    let ρ : LinearMap.ker H →ₗ[K] ((I' → K) ⧸ LinearMap.range D) :=
      (LinearMap.range D).mkQ.comp (E.comp (LinearMap.ker H).subtype)
    (S.submatrix (fun i : I => i.1) (fun j : C => j.1)).rank = Module.finrank K (LinearMap.range D) ∧
    (S.submatrix (fun i : R => i.1) (fun j : J => j.1)).rank = Module.finrank K (LinearMap.range H) ∧
    (S.submatrix (fun i : I => i.1) (fun j : J => j.1)).rank =
      Module.finrank K (LinearMap.range D) + Module.finrank K (LinearMap.range H) +
        Module.finrank K (LinearMap.range ρ) := by
  intro I' J' D H E ρ
  let eI := finset_split_fun_equiv (K := K) hRI
  let eJ := finset_split_fun_equiv (K := K) hCJ
  have hsumJ : ∀ (i : Fin n) (x : C → K) (y : J' → K),
      ∑ j : J, S i j.1 * (eJ.symm (x, y) j) =
        (∑ c : C, S i c.1 * x c) + ∑ j' : J', S i j'.1 * y j' := by
    intro i x y
    have hpart : (Finset.univ : Finset J) =
        (Finset.univ.filter (fun j : J => j.1 ∈ C)) ∪ (Finset.univ.filter (fun j : J => j.1 ∉ C)) := by
      ext j; simp; exact em _
    rw [hpart, Finset.sum_union (by rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h2 h1)]
    congr 1
    · refine Finset.sum_bij (fun j hj => (⟨j.1, (Finset.mem_filter.mp hj).2⟩ : C)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Subtype.ext (congrArg (fun z : C => z.1) h)
      · intro c _; exact ⟨⟨c.1, hCJ c.2⟩, by simp [c.2], rfl⟩
      · intro j hj; have hjC : j.1 ∈ C := (Finset.mem_filter.mp hj).2; simp [eJ, finset_split_fun_equiv, hjC]
    · refine Finset.sum_bij (fun j hj => (⟨j.1, Finset.mem_sdiff.mpr ⟨j.2, (Finset.mem_filter.mp hj).2⟩⟩ : J')) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Subtype.ext (congrArg (fun z : J' => z.1) h)
      · intro j' _; exact ⟨⟨j'.1, (Finset.mem_sdiff.mp j'.2).1⟩, by simp [(Finset.mem_sdiff.mp j'.2).2], rfl⟩
      · intro j hj; have hjC : j.1 ∉ C := (Finset.mem_filter.mp hj).2; simp [eJ, finset_split_fun_equiv, hjC]
  refine ⟨?_, ?_, ?_⟩
  · have h1 := rank_eq_of_equiv (LinearEquiv.refl K (C → K)) eI
      (S.submatrix (fun i : I => i.1) (fun j : C => j.1)).mulVecLin
    rw [matrix_rank_eq_finrank_range, ← h1]
    have hmap : eI.toLinearMap.comp ((S.submatrix (fun i : I => i.1) (fun j : C => j.1)).mulVecLin.comp (LinearEquiv.refl K (C → K)).symm.toLinearMap) =
        LinearMap.prod (0 : (C → K) →ₗ[K] (R → K)) D := by
      apply LinearMap.ext; intro x
      apply Prod.ext
      · funext r
        change ∑ c : C, S r.1 c.1 * x c = 0
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [hzero r.1 r.2 c.1 c.2, zero_mul]
      · rfl
    rw [hmap]
    have hrg : LinearMap.range (LinearMap.prod (0 : (C → K) →ₗ[K] (R → K)) D) =
        Submodule.map (LinearMap.inr K (R → K) (I' → K)) (LinearMap.range D) := by
      ext ⟨r0, v⟩
      simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.prod_apply, LinearMap.coe_inr]
      constructor
      · rintro ⟨x, hx⟩
        rcases Prod.mk.inj hx with ⟨h0, hv⟩
        simp only [LinearMap.zero_apply] at h0
        exact ⟨v, ⟨x, hv⟩, Prod.ext h0 rfl⟩
      · rintro ⟨w, ⟨x, rfl⟩, heq⟩
        exact ⟨x, heq⟩
    rw [hrg]
    exact finrank_map_of_inj (LinearMap.inr K (R → K) (I' → K)) LinearMap.inr_injective _
  · have h1 := rank_eq_of_equiv eJ (LinearEquiv.refl K (R → K))
      (S.submatrix (fun i : R => i.1) (fun j : J => j.1)).mulVecLin
    rw [matrix_rank_eq_finrank_range, ← h1]
    have hmap : (LinearEquiv.refl K (R → K)).toLinearMap.comp
        ((S.submatrix (fun i : R => i.1) (fun j : J => j.1)).mulVecLin.comp eJ.symm.toLinearMap) =
        H.comp (LinearMap.snd K (C → K) (J' → K)) := by
      apply LinearMap.ext; rintro ⟨x, y⟩; funext r
      change ∑ j : J, S r.1 j.1 * (eJ.symm (x, y) j) = ∑ j' : J', S r.1 j'.1 * y j'
      rw [hsumJ r.1 x y]
      have h0 : ∑ c : C, S r.1 c.1 * x c = 0 :=
        Finset.sum_eq_zero fun c _ => by rw [hzero r.1 r.2 c.1 c.2, zero_mul]
      rw [h0, zero_add]
    rw [hmap, LinearMap.range_comp_of_range_eq_top H (LinearMap.range_eq_top.mpr Prod.snd_surjective)]
  · have h1 := rank_eq_of_equiv eJ eI
      (S.submatrix (fun i : I => i.1) (fun j : J => j.1)).mulVecLin
    rw [matrix_rank_eq_finrank_range, ← h1]
    have hblk : eI.toLinearMap.comp
        ((S.submatrix (fun i : I => i.1) (fun j : J => j.1)).mulVecLin.comp eJ.symm.toLinearMap) =
        { toFun := fun p => (H p.2, D p.1 + E p.2)
          map_add' := fun p q => Prod.ext (map_add H p.2 q.2) (by
            change D (p.1 + q.1) + E (p.2 + q.2) = (D p.1 + E p.2) + (D q.1 + E q.2)
            rw [map_add, map_add]; abel)
          map_smul' := fun c p => Prod.ext (map_smul H c p.2) (by
            change D (c • p.1) + E (c • p.2) = c • (D p.1 + E p.2)
            rw [map_smul, map_smul, smul_add]) } := by
      apply LinearMap.ext; rintro ⟨x, y⟩
      apply Prod.ext
      · funext r
        change ∑ j : J, S r.1 j.1 * (eJ.symm (x, y) j) = ∑ j' : J', S r.1 j'.1 * y j'
        rw [hsumJ r.1 x y]
        have h0 : ∑ c : C, S r.1 c.1 * x c = 0 :=
          Finset.sum_eq_zero fun c _ => by rw [hzero r.1 r.2 c.1 c.2, zero_mul]
        rw [h0, zero_add]
      · funext i'
        change ∑ j : J, S i'.1 j.1 * (eJ.symm (x, y) j) =
          (∑ c : C, S i'.1 c.1 * x c) + ∑ j' : J', S i'.1 j'.1 * y j'
        exact hsumJ i'.1 x y
    rw [hblk, zero_core_block_rank H D E]

lemma rank_submatrix_univ {n m : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    (M.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.1)
      (fun j : (Finset.univ : Finset (Fin m)) => j.1)).rank = M.rank := by
  let eI0 : (Fin n → K) ≃ₗ[K] (↑(Finset.univ : Finset (Fin n)) → K) :=
    { toFun := fun v x => v x.1
      invFun := fun v i => v ⟨i, Finset.mem_univ i⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eJ0 : (Fin m → K) ≃ₗ[K] (↑(Finset.univ : Finset (Fin m)) → K) :=
    { toFun := fun v x => v x.1
      invFun := fun v j => v ⟨j, Finset.mem_univ j⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2 := rank_eq_of_equiv eJ0 eI0 M.mulVecLin
  rw [matrix_rank_eq_finrank_range, matrix_rank_eq_finrank_range, ← h2]
  have hmap : (M.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.1)
      (fun j : (Finset.univ : Finset (Fin m)) => j.1)).mulVecLin =
      eI0.toLinearMap.comp (M.mulVecLin.comp eJ0.symm.toLinearMap) := by
    apply LinearMap.ext; intro v; funext i
    change ∑ j : Finset.univ, M i.1 j.1 * v j = ∑ j : Fin m, M i.1 j * v ⟨j, Finset.mem_univ j⟩
    exact Finset.sum_bij (fun j _ => j.1) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Subtype.ext h) (fun j _ => ⟨⟨j, Finset.mem_univ j⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  rw [hmap]

lemma zero_core_main {n m d r' : ℕ} (S : Matrix (Fin n) (Fin m) K)
    (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d))
    (hzero : ∀ i j, row i = none → col j = none → S i j = 0) :
    let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
    let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
    let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
    let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
    let rk := fun (I : Finset (Fin n)) (J : Finset (Fin m)) =>
      Matrix.rank (S.submatrix (fun i : I => i.val) (fun j : J => j.val))
    let strips := rk Finset.univ C + rk R Finset.univ
    (∃ B : Matrix (Fin n) (Fin m) K, Matrix.rank B ≤ r' ∧
      ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B i j = S i j) ↔
    strips ≤ r' ∧ ∀ a : Fin d,
      strips + rk (rows a) (cols a) ≤ r' + rk (rows a) C + rk R (cols a) := by
  intro R C rows cols rk strips
  have hzeroRC : ∀ i ∈ R, ∀ j ∈ C, S i j = 0 :=
    fun i hi j hj => hzero i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  set I' : Finset (Fin n) := Finset.univ \ R
  set J' : Finset (Fin m) := Finset.univ \ C
  set D_all : (C → K) →ₗ[K] (I' → K) :=
    (S.submatrix (fun i : I' => i.1) (fun j : C => j.1)).mulVecLin
  set H_all : (J' → K) →ₗ[K] (R → K) :=
    (S.submatrix (fun i : R => i.1) (fun j : J' => j.1)).mulVecLin
  have ⟨hrk_D_all, hrk_H_all, _⟩ :=
    zero_core_submatrix_ranks S R Finset.univ C Finset.univ (Finset.subset_univ R) (Finset.subset_univ C) hzeroRC
  have hrk_B_formula : ∀ (B : Matrix (Fin n) (Fin m) K),
      (∀ i j, (row i = none ∨ col j = none) → B i j = S i j) →
      let E_B : (J' → K) →ₗ[K] (I' → K) :=
        (B.submatrix (fun i : I' => i.1) (fun j : J' => j.1)).mulVecLin
      let ρ_B : LinearMap.ker H_all →ₗ[K] ((I' → K) ⧸ LinearMap.range D_all) :=
        (LinearMap.range D_all).mkQ.comp (E_B.comp (LinearMap.ker H_all).subtype)
      B.rank = strips + Module.finrank K (LinearMap.range ρ_B) := by
    intro B hB E_B ρ_B
    have hBz : ∀ i ∈ R, ∀ j ∈ C, B i j = 0 := fun i hi j hj => by
      rw [hB i j (Or.inl (Finset.mem_filter.mp hi).2), hzeroRC i hi j hj]
    have ⟨_, _, hBrk⟩ :=
      zero_core_submatrix_ranks B R Finset.univ C Finset.univ (Finset.subset_univ R) (Finset.subset_univ C) hBz
    have hBD : (B.submatrix (fun i : I' => i.1) (fun j : C => j.1)).mulVecLin = D_all := by
      congr 1; ext i j; exact hB i.1 j.1 (Or.inr (Finset.mem_filter.mp j.2).2)
    have hBH : (B.submatrix (fun i : R => i.1) (fun j : J' => j.1)).mulVecLin = H_all := by
      congr 1; ext i j; exact hB i.1 j.1 (Or.inl (Finset.mem_filter.mp i.2).2)
    rw [rank_submatrix_univ B] at hBrk
    rw [hBD, hBH] at hBrk
    rw [hBrk]
    dsimp only [strips, rk]
    rw [hrk_D_all, hrk_H_all]
  let Ia : Fin d → Finset (Fin n) := fun a => rows a \ R
  let Ja : Fin d → Finset (Fin m) := fun a => cols a \ C
  have hIa_mem : ∀ (a : Fin d) (i : Fin n), i ∈ Ia a ↔ row i = some a := by
    intro a i
    simp only [Ia, rows, R, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1 | h1, h2⟩; exact absurd h1 h2; exact h1
    · intro h1; exact ⟨Or.inr h1, by rw [h1]; simp⟩
  have hJa_mem : ∀ (a : Fin d) (j : Fin m), j ∈ Ja a ↔ col j = some a := by
    intro a j
    simp only [Ja, cols, C, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1 | h1, h2⟩; exact absurd h1 h2; exact h1
    · intro h1; exact ⟨Or.inr h1, by rw [h1]; simp⟩
  let Da : ∀ a : Fin d, (C → K) →ₗ[K] (Ia a → K) := fun a =>
    (S.submatrix (fun i : Ia a => i.1) (fun j : C => j.1)).mulVecLin
  let Ha : ∀ a : Fin d, (Ja a → K) →ₗ[K] (R → K) := fun a =>
    (S.submatrix (fun i : R => i.1) (fun j : Ja a => j.1)).mulVecLin
  let Ea : ∀ a : Fin d, (Ja a → K) →ₗ[K] (Ia a → K) := fun a =>
    (S.submatrix (fun i : Ia a => i.1) (fun j : Ja a => j.1)).mulVecLin
  let ρa : ∀ a : Fin d, LinearMap.ker (Ha a) →ₗ[K] ((Ia a → K) ⧸ LinearMap.range (Da a)) := fun a =>
    (LinearMap.range (Da a)).mkQ.comp ((Ea a).comp (LinearMap.ker (Ha a)).subtype)
  have hrk_a : ∀ a : Fin d,
      rk (rows a) C = Module.finrank K (LinearMap.range (Da a)) ∧
      rk R (cols a) = Module.finrank K (LinearMap.range (Ha a)) ∧
      rk (rows a) (cols a) =
        Module.finrank K (LinearMap.range (Da a)) + Module.finrank K (LinearMap.range (Ha a)) +
          Module.finrank K (LinearMap.range (ρa a)) := fun a =>
    zero_core_submatrix_ranks S R (rows a) C (cols a) Finset.subset_union_left Finset.subset_union_left hzeroRC
  constructor
  · rintro ⟨B, hBrk, hB⟩
    have hB_rc : ∀ i j, (row i = none ∨ col j = none) → B i j = S i j :=
      fun i j h => hB i j (h.elim Or.inl (fun h2 => Or.inr (Or.inl h2)))
    let E_B : (J' → K) →ₗ[K] (I' → K) :=
      (B.submatrix (fun i : I' => i.1) (fun j : J' => j.1)).mulVecLin
    let ρ_B : LinearMap.ker H_all →ₗ[K] ((I' → K) ⧸ LinearMap.range D_all) :=
      (LinearMap.range D_all).mkQ.comp (E_B.comp (LinearMap.ker H_all).subtype)
    have hB_eq : B.rank = strips + Module.finrank K (LinearMap.range ρ_B) :=
      hrk_B_formula B hB_rc
    refine ⟨by omega, fun a => ?_⟩
    have ⟨hva, hha, hra⟩ := hrk_a a
    have hJa_sub : Ja a ⊆ J' := by
      intro j hj; simp only [J', Finset.mem_sdiff, Finset.mem_univ, true_and, C, Finset.mem_filter]
      have := (hJa_mem a j).mp hj; simp [this]
    have hIa_sub : Ia a ⊆ I' := by
      intro i hi; simp only [I', Finset.mem_sdiff, Finset.mem_univ, true_and, R, Finset.mem_filter]
      have := (hIa_mem a i).mp hi; simp [this]
    let extJ : LinearMap.ker (Ha a) →ₗ[K] LinearMap.ker H_all :=
      { toFun := fun y =>
          ⟨fun j' => if hj : j'.1 ∈ Ja a then y.1 ⟨j'.1, hj⟩ else 0, by
            rw [LinearMap.mem_ker]
            funext r
            change ∑ j' : J', S r.1 j'.1 * (if hj : j'.1 ∈ Ja a then y.1 ⟨j'.1, hj⟩ else 0) = 0
            have hsum : (∑ j' : J', S r.1 j'.1 * (if hj : j'.1 ∈ Ja a then y.1 ⟨j'.1, hj⟩ else 0)) =
                ∑ j : Ja a, S r.1 j.1 * y.1 j := by
              rw [← Finset.sum_filter_of_ne (p := fun j' : J' => j'.1 ∈ Ja a)]
              · refine Finset.sum_bij (fun j' hj' => (⟨j'.1, (Finset.mem_filter.mp hj').2⟩ : Ja a)) ?_ ?_ ?_ ?_
                · intro _ _; exact Finset.mem_univ _
                · intro a1 _ b1 _ h; exact Subtype.ext (congrArg (fun z : Ja a => z.1) h)
                · intro j _; exact ⟨⟨j.1, hJa_sub j.2⟩, by simp [j.2], rfl⟩
                · intro j' hj'; have hj : j'.1 ∈ Ja a := (Finset.mem_filter.mp hj').2; simp [hj]
              · intro j' _ hne; by_contra hnot; simp [hnot] at hne
            rw [hsum]
            exact congrFun (LinearMap.mem_ker.mp y.2) r⟩
        map_add' := fun x y => by
          apply Subtype.ext; funext j'
          simp only [Pi.add_apply, Submodule.coe_add]
          split_ifs <;> simp
        map_smul' := fun c x => by
          apply Subtype.ext; funext j'
          simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> simp }
    let resI : (I' → K) →ₗ[K] (Ia a → K) :=
      { toFun := fun v i => v ⟨i.1, hIa_sub i.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let qProj : ((I' → K) ⧸ LinearMap.range D_all) →ₗ[K] ((Ia a → K) ⧸ LinearMap.range (Da a)) :=
      Submodule.liftQ (LinearMap.range D_all) ((LinearMap.range (Da a)).mkQ.comp resI) (by
        rintro _ ⟨x, rfl⟩
        simp only [LinearMap.mem_ker, comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨x, rfl⟩)
    have hcomp : ρa a = qProj.comp (ρ_B.comp extJ) := by
      apply LinearMap.ext; intro y
      simp only [ρa, ρ_B, qProj, comp_apply, Submodule.coe_subtype, Submodule.liftQ_apply, Submodule.mkQ_apply]
      congr 1
      funext i
      change ∑ j : Ja a, S i.1 j.1 * y.1 j =
        ∑ j' : J', B i.1 j'.1 * (if hj : j'.1 ∈ Ja a then y.1 ⟨j'.1, hj⟩ else 0)
      rw [← Finset.sum_filter_of_ne (p := fun j' : J' => j'.1 ∈ Ja a)]
      · symm
        refine Finset.sum_bij (fun j' hj' => (⟨j'.1, (Finset.mem_filter.mp hj').2⟩ : Ja a)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a1 _ b1 _ h; exact Subtype.ext (congrArg (fun z : Ja a => z.1) h)
        · intro j _; exact ⟨⟨j.1, hJa_sub j.2⟩, by simp [j.2], rfl⟩
        · intro j' hj'
          have hj : j'.1 ∈ Ja a := (Finset.mem_filter.mp hj').2
          simp only [hj, ↓reduceDIte]
          have hrow : row i.1 = some a := (hIa_mem a i.1).mp i.2
          have hcol : col j'.1 = some a := (hJa_mem a j'.1).mp hj
          rw [hB i.1 j'.1 (Or.inr (Or.inr (by rw [hrow, hcol])))]
      · intro j' _ hne; by_contra hnot; simp [hnot] at hne
    have hle1 : Module.finrank K (LinearMap.range (ρa a)) ≤ Module.finrank K (LinearMap.range ρ_B) := by
      rw [hcomp]
      exact (rank_comp_le_right qProj (ρ_B.comp extJ)).trans (rank_comp_le_left ρ_B extJ)
    omega
  · rintro ⟨hstrips, hloc⟩
    set q : ℕ := r' - strips
    have hρa_le : ∀ a : Fin d, Module.finrank K (LinearMap.range (ρa a)) ≤ q := by
      intro a
      have ⟨hva, hha, hra⟩ := hrk_a a
      have := hloc a
      omega
    have hdecomp_a : ∀ a : Fin d,
        ∃ (Xa : (Ja a → K) →ₗ[K] (C → K)) (Ya : (R → K) →ₗ[K] (Ia a → K))
          (La : (Fin q → K) →ₗ[K] (Ia a → K)) (Ra : (Ja a → K) →ₗ[K] (Fin q → K)),
          Ea a = (Da a).comp Xa + Ya.comp (Ha a) + La.comp Ra := by
      intro a
      rcases Submodule.exists_isCompl (LinearMap.ker (Ha a)) with ⟨Ua, hUa⟩
      let pKer : (Ja a → K) →ₗ[K] LinearMap.ker (Ha a) :=
        Submodule.projectionOnto (LinearMap.ker (Ha a)) Ua hUa
      let pU : (Ja a → K) →ₗ[K] Ua :=
        Submodule.projectionOnto Ua (LinearMap.ker (Ha a)) hUa.symm
      have hdecomp_y : ∀ y : Ja a → K, y = (pKer y).1 + (pU y).1 := by
        intro y
        have hmem : y ∈ LinearMap.ker (Ha a) ⊔ Ua := by
          rw [hUa.sup_eq_top]; trivial
        rcases Submodule.mem_sup.mp hmem with ⟨u, hu, v, hv, rfl⟩
        have h1 : pKer (u + v) = ⟨u, hu⟩ := by
          rw [map_add, Submodule.projectionOnto_apply_left hUa ⟨u, hu⟩,
            Submodule.projectionOnto_apply_right hUa ⟨v, hv⟩, add_zero]
        have h2 : pU (u + v) = ⟨v, hv⟩ := by
          rw [map_add, Submodule.projectionOnto_apply_right hUa.symm ⟨u, hu⟩,
            Submodule.projectionOnto_apply_left hUa.symm ⟨v, hv⟩, zero_add]
        rw [h1, h2]
      have hHa_inj : Function.Injective ((Ha a).comp Ua.subtype) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        rintro ⟨u, huU⟩ huK
        have huKer : u ∈ LinearMap.ker (Ha a) := huK
        have h0 : u ∈ LinearMap.ker (Ha a) ⊓ Ua := ⟨huKer, huU⟩
        rw [hUa.inf_eq_bot] at h0
        exact Subtype.ext (by simpa using h0)
      rcases exists_left_inv_of_inj ((Ha a).comp Ua.subtype) hHa_inj with ⟨ψa, hψa⟩
      let Ya : (R → K) →ₗ[K] (Ia a → K) := (Ea a).comp (Ua.subtype.comp ψa)
      have hYa_eq : ∀ y : Ja a → K, (Ea a - Ya.comp (Ha a)) y = Ea a (pKer y).1 := by
        intro y
        have hHy : Ha a y = Ha a (pU y).1 := by
          conv_lhs => rw [hdecomp_y y]
          rw [map_add, LinearMap.mem_ker.mp (pKer y).2, zero_add]
        have hψ : ψa (Ha a y) = pU y := by
          rw [hHy]
          exact congrArg (fun φ => φ (pU y)) hψa
        have hEy : Ea a y = Ea a (pKer y).1 + Ea a (pU y).1 := by
          conv_lhs => rw [hdecomp_y y]
          rw [map_add]
        simp only [LinearMap.sub_apply, comp_apply, Ya, hψ, Submodule.coe_subtype, hEy]
        abel
      rcases exists_section_of_surj (LinearMap.range (Da a)).mkQ (Submodule.mkQ_surjective _) with ⟨σa, hσa⟩
      let Ta : (Ja a → K) →ₗ[K] (Ia a → K) := σa.comp ((ρa a).comp pKer)
      have hTa_rk : Module.finrank K (LinearMap.range Ta) ≤ q :=
        ((rank_comp_le_right σa ((ρa a).comp pKer)).trans (rank_comp_le_left (ρa a) pKer)).trans (hρa_le a)
      rcases factor_through_fin Ta q hTa_rk with ⟨La, Ra, hLR⟩
      let rem : (Ja a → K) →ₗ[K] (Ia a → K) := Ea a - Ya.comp (Ha a) - Ta
      have hrem_mem : ∀ y : Ja a → K, rem y ∈ LinearMap.range (Da a) := by
        intro y
        rw [← Submodule.Quotient.mk_eq_zero]
        change (LinearMap.range (Da a)).mkQ ((Ea a - Ya.comp (Ha a)) y - Ta y) = 0
        rw [map_sub, hYa_eq y]
        have hσ : (LinearMap.range (Da a)).mkQ (Ta y) = ρa a (pKer y) :=
          congrArg (fun φ => φ (ρa a (pKer y))) hσa
        rw [hσ]
        exact sub_self _
      rcases exists_section_of_surj (Da a).rangeRestrict (Da a).surjective_rangeRestrict with ⟨φa, hφa⟩
      let rem' : (Ja a → K) →ₗ[K] LinearMap.range (Da a) := rem.codRestrict (LinearMap.range (Da a)) hrem_mem
      let Xa : (Ja a → K) →ₗ[K] (C → K) := φa.comp rem'
      have hDXa : (Da a).comp Xa = rem := by
        apply LinearMap.ext; intro y
        simp only [comp_apply, Xa]
        have h1 : (Da a).rangeRestrict (φa (rem' y)) = rem' y := congrArg (fun φ => φ (rem' y)) hφa
        exact congrArg Subtype.val h1
      refine ⟨Xa, Ya, La, Ra, ?_⟩
      rw [hDXa, hLR]
      apply LinearMap.ext; intro y
      simp only [rem, LinearMap.add_apply, LinearMap.sub_apply]
      abel
    choose Xa Ya La Ra hEa_eq using hdecomp_a
    let resJa : ∀ a : Fin d, (J' → K) →ₗ[K] (Ja a → K) := fun a =>
      { toFun := fun y j => y ⟨j.1, by
          simp only [J', Finset.mem_sdiff, Finset.mem_univ, true_and, C, Finset.mem_filter]
          have := (hJa_mem a j.1).mp j.2; simp [this]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let X_all : (J' → K) →ₗ[K] (C → K) := ∑ a : Fin d, (Xa a).comp (resJa a)
    let R_all : (J' → K) →ₗ[K] (Fin q → K) := ∑ a : Fin d, (Ra a).comp (resJa a)
    let Y_all : (R → K) →ₗ[K] (I' → K) :=
      { toFun := fun w i =>
          match h : row i.1 with
          | none => 0
          | some a => Ya a w ⟨i.1, (hIa_mem a i.1).mpr h⟩
        map_add' := fun w1 w2 => by funext i; simp only [Pi.add_apply]; split <;> simp
        map_smul' := fun c w => by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> simp }
    let L_all : (Fin q → K) →ₗ[K] (I' → K) :=
      { toFun := fun z i =>
          match h : row i.1 with
          | none => 0
          | some a => La a z ⟨i.1, (hIa_mem a i.1).mpr h⟩
        map_add' := fun z1 z2 => by funext i; simp only [Pi.add_apply]; split <;> simp
        map_smul' := fun c z => by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> simp }
    let E_full : (J' → K) →ₗ[K] (I' → K) :=
      D_all.comp X_all + Y_all.comp H_all + L_all.comp R_all
    let E_mat : Matrix I' J' K := LinearMap.toMatrix' E_full
    let B : Matrix (Fin n) (Fin m) K := fun i j =>
      if hi : i ∈ R then S i j
      else if hj : j ∈ C then S i j
      else E_mat ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩
        ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩
    have hB_rc : ∀ i j, (row i = none ∨ col j = none) → B i j = S i j := by
      intro i j h
      rcases h with hr | hc
      · have hi : i ∈ R := by simp [R, hr]
        simp [B, hi]
      · have hj : j ∈ C := by simp [C, hc]
        by_cases hi : i ∈ R <;> simp [B, hi, hj]
    have hB_sub : (B.submatrix (fun i : I' => i.1) (fun j : J' => j.1)).mulVecLin = E_full := by
      have hm : B.submatrix (fun i : I' => i.1) (fun j : J' => j.1) = E_mat := by
        funext i' j'
        have hi : i'.1 ∉ R := (Finset.mem_sdiff.mp i'.2).2
        have hj : j'.1 ∉ C := (Finset.mem_sdiff.mp j'.2).2
        change B i'.1 j'.1 = E_mat i' j'
        simp [B, hi, hj]
      rw [hm]
      exact Matrix.toLin'_toMatrix' E_full
    have hB_rk : B.rank ≤ r' := by
      rw [hrk_B_formula B hB_rc]
      have hρ_eq : (LinearMap.range D_all).mkQ.comp ((B.submatrix (fun i : I' => i.1) (fun j : J' => j.1)).mulVecLin.comp (LinearMap.ker H_all).subtype) =
          ((LinearMap.range D_all).mkQ.comp L_all).comp (R_all.comp (LinearMap.ker H_all).subtype) := by
        rw [hB_sub]
        apply LinearMap.ext; intro y
        simp only [E_full, LinearMap.add_apply, comp_apply, Submodule.coe_subtype, map_add,
          LinearMap.mem_ker.mp y.2, map_zero, add_zero]
        have hD0 : (LinearMap.range D_all).mkQ (D_all (X_all y.1)) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨X_all y.1, rfl⟩
        rw [hD0, zero_add]
      rw [hρ_eq]
      have hle : Module.finrank K (LinearMap.range (((LinearMap.range D_all).mkQ.comp L_all).comp (R_all.comp (LinearMap.ker H_all).subtype))) ≤ q := by
        have h1 := rank_comp_le_left ((LinearMap.range D_all).mkQ.comp L_all) (R_all.comp (LinearMap.ker H_all).subtype)
        have h2 : Module.finrank K (LinearMap.range ((LinearMap.range D_all).mkQ.comp L_all)) ≤ Module.finrank K (Fin q → K) :=
          LinearMap.finrank_range_le _
        rw [Module.finrank_pi, Fintype.card_fin] at h2
        omega
      omega
    refine ⟨B, hB_rk, ?_⟩
    intro i j h
    rcases h with hr | hc | hrc
    · exact hB_rc i j (Or.inl hr)
    · exact hB_rc i j (Or.inr hc)
    · by_cases hi : i ∈ R
      · exact hB_rc i j (Or.inl (Finset.mem_filter.mp hi).2)
      · by_cases hj : j ∈ C
        · exact hB_rc i j (Or.inr (Finset.mem_filter.mp hj).2)
        · have hrow_ne : row i ≠ none := by simpa [R] using hi
          cases ha : row i with
          | none => exact absurd ha hrow_ne
          | some a =>
            have hcol_a : col j = some a := by rw [← hrc, ha]
            set i' : I' := ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩
            set j' : J' := ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩
            have hBij : B i j = E_full (Pi.single j' 1) i' := by
              have h1 : B i j = E_mat i' j' := by simp [B, hi, hj, i', j']
              rw [h1]
              have h2 := congrFun (congrArg (fun φ => φ (Pi.single j' 1)) (Matrix.toLin'_toMatrix' E_full)) i'
              rw [← h2]
              change E_mat i' j' = ∑ k : J', E_mat i' k * (Pi.single j' (1 : K) : J' → K) k
              rw [Finset.sum_eq_single j']
              · simp
              · intro k _ hk; simp [Pi.single_eq_of_ne hk]
              · intro hm; exact absurd (Finset.mem_univ j') hm
            rw [hBij]
            set ja : Ja a := ⟨j, (hJa_mem a j).mpr hcol_a⟩
            set ia : Ia a := ⟨i, (hIa_mem a i).mpr ha⟩
            have hres_eq : resJa a (Pi.single j' 1) = Pi.single ja 1 := by
              funext x
              simp only [resJa, LinearMap.coe_mk, AddHom.coe_mk]
              by_cases hx : x = ja
              · subst hx; simp [ja, j']
              · have hx' : ∀ h : x.1 ∈ J', (⟨x.1, h⟩ : J') ≠ j' := by
                  intro h heq
                  exact hx (Subtype.ext (congrArg (fun z : J' => z.1) heq))
                simp [hx, hx']
            have hres_ne : ∀ b : Fin d, b ≠ a → resJa b (Pi.single j' 1) = 0 := by
              intro b hba
              funext x
              simp only [resJa, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
              have hx' : ∀ h : x.1 ∈ J', (⟨x.1, h⟩ : J') ≠ j' := by
                intro h heq
                have hval : x.1 = j := congrArg (fun z : J' => z.1) heq
                have hcb : col x.1 = some b := (hJa_mem b x.1).mp x.2
                rw [hval, hcol_a] at hcb
                exact hba (Option.some.inj hcb.symm)
              simp [hx']
            have hX_s : X_all (Pi.single j' 1) = Xa a (Pi.single ja 1) := by
              simp only [X_all, LinearMap.sum_apply, comp_apply]
              rw [Finset.sum_eq_single a]
              · rw [hres_eq]
              · intro b _ hba; rw [hres_ne b hba, map_zero]
              · intro h; exact absurd (Finset.mem_univ a) h
            have hR_s : R_all (Pi.single j' 1) = Ra a (Pi.single ja 1) := by
              simp only [R_all, LinearMap.sum_apply, comp_apply]
              rw [Finset.sum_eq_single a]
              · rw [hres_eq]
              · intro b _ hba; rw [hres_ne b hba, map_zero]
              · intro h; exact absurd (Finset.mem_univ a) h
            have hH_s : H_all (Pi.single j' 1) = Ha a (Pi.single ja 1) := by
              funext r
              change ∑ k : J', S r.1 k.1 * (Pi.single j' (1 : K) : J' → K) k =
                ∑ k : Ja a, S r.1 k.1 * (Pi.single ja (1 : K) : Ja a → K) k
              rw [Finset.sum_eq_single j', Finset.sum_eq_single ja]
              · simp [j', ja]
              · intro k _ hk; simp [Pi.single_eq_of_ne hk]
              · intro hm; exact absurd (Finset.mem_univ ja) hm
              · intro k _ hk; simp [Pi.single_eq_of_ne hk]
              · intro hm; exact absurd (Finset.mem_univ j') hm
            have hD_i : D_all (Xa a (Pi.single ja 1)) i' = Da a (Xa a (Pi.single ja 1)) ia := rfl
            have hY_i : Y_all (Ha a (Pi.single ja 1)) i' = Ya a (Ha a (Pi.single ja 1)) ia := by
              simp only [Y_all, LinearMap.coe_mk, AddHom.coe_mk, i']
              split
              · rename_i hnone; rw [ha] at hnone; cases hnone
              · rename_i b hsome; rw [ha] at hsome; cases Option.some.inj hsome; rfl
            have hL_i : L_all (Ra a (Pi.single ja 1)) i' = La a (Ra a (Pi.single ja 1)) ia := by
              simp only [L_all, LinearMap.coe_mk, AddHom.coe_mk, i']
              split
              · rename_i hnone; rw [ha] at hnone; cases hnone
              · rename_i b hsome; rw [ha] at hsome; cases Option.some.inj hsome; rfl
            simp only [E_full, LinearMap.add_apply, comp_apply, Pi.add_apply, hX_s, hR_s, hH_s, hD_i, hY_i, hL_i]
            have hE_val := congrFun (congrArg (fun φ => φ (Pi.single ja 1)) (hEa_eq a)) ia
            simp only [LinearMap.add_apply, comp_apply, Pi.add_apply] at hE_val
            rw [← hE_val]
            change ∑ k : Ja a, S ia.1 k.1 * (Pi.single ja (1 : K) : Ja a → K) k = S i j
            rw [Finset.sum_eq_single ja]
            · simp [ia, ja]
            · intro k _ hk; simp [Pi.single_eq_of_ne hk]
            · intro hm; exact absurd (Finset.mem_univ ja) hm

lemma main_991 (K : Type) [Field K] (n m d r : ℕ) (A : Matrix (Fin n) (Fin m) K)
    (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d)) :
    let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
    let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
    let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
    let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
    let rk := fun (I : Finset (Fin n)) (J : Finset (Fin m)) =>
      Matrix.rank (A.submatrix (fun i : I => i.val) (fun j : J => j.val))
    let strips := rk Finset.univ C + rk R Finset.univ
    (∃ B : Matrix (Fin n) (Fin m) K, Matrix.rank B ≤ r ∧
      ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B i j = A i j) ↔
    strips ≤ r + rk R C ∧ ∀ a : Fin d,
      strips + rk (rows a) (cols a) ≤ r + rk (rows a) C + rk R (cols a) := by
  intro R C rows cols rk strips
  set A_RC : Matrix R C K := A.submatrix (fun i : R => i.1) (fun j : C => j.1)
  rcases exists_right_inv_on_range A_RC.mulVecLin with ⟨g, hfgf, hgfg⟩
  set G : Matrix C R K := LinearMap.toMatrix' g
  have hAGA : A_RC * G * A_RC = A_RC := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, G, Matrix.toLin'_toMatrix']
    exact hfgf
  have hGAG : G * A_RC * G = G := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, G, Matrix.toLin'_toMatrix']
    exact hgfg
  set M0 : Matrix (Fin n) (Fin m) K :=
    Matrix.of (fun i j => ∑ c : C, ∑ r0 : R, A i c.1 * G c r0 * A r0.1 j)
  set S : Matrix (Fin n) (Fin m) K := A - M0
  have hS_zero : ∀ i j, row i = none → col j = none → S i j = 0 := by
    intro i j hi hj
    set ri : R := ⟨i, by simp [R, hi]⟩
    set cj : C := ⟨j, by simp [C, hj]⟩
    have hM0_eq : M0 i j = (A_RC * G * A_RC) ri cj := by
      simp only [M0, Matrix.of_apply, Matrix.mul_apply, A_RC, Matrix.submatrix_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r0 _ => ?_
      rw [Finset.sum_mul]
    change A i j - M0 i j = 0
    rw [hM0_eq, hAGA]
    simp [A_RC, ri, cj]
  set c : ℕ := rk R C
  let rkS := fun (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (S.submatrix (fun i : I => i.val) (fun j : J => j.val))
  have hrk_shift : ∀ (I : Finset (Fin n)) (J : Finset (Fin m)), R ⊆ I → C ⊆ J →
      rk I J = c + rkS I J := by
    intro I J hRI hCJ
    exact schur_rank_add A A R I C J hRI hCJ (fun _ _ _ _ _ => rfl) G hAGA hGAG
  have hrk_uC : rk Finset.univ C = c + rkS Finset.univ C :=
    hrk_shift Finset.univ C (Finset.subset_univ R) (Finset.Subset.refl C)
  have hrk_Ru : rk R Finset.univ = c + rkS R Finset.univ :=
    hrk_shift R Finset.univ (Finset.Subset.refl R) (Finset.subset_univ C)
  have hrk_aC : ∀ a : Fin d, rk (rows a) C = c + rkS (rows a) C :=
    fun a => hrk_shift (rows a) C Finset.subset_union_left (Finset.Subset.refl C)
  have hrk_Ra : ∀ a : Fin d, rk R (cols a) = c + rkS R (cols a) :=
    fun a => hrk_shift R (cols a) (Finset.Subset.refl R) Finset.subset_union_left
  have hrk_aa : ∀ a : Fin d, rk (rows a) (cols a) = c + rkS (rows a) (cols a) :=
    fun a => hrk_shift (rows a) (cols a) Finset.subset_union_left Finset.subset_union_left
  have hB_rank_shift : ∀ B : Matrix (Fin n) (Fin m) K,
      (∀ i j, (row i = none ∨ col j = none) → B i j = A i j) →
      B.rank = c + (B - M0).rank := by
    intro B hB
    have h1 := schur_rank_add A B R Finset.univ C Finset.univ (Finset.subset_univ R) (Finset.subset_univ C)
      (fun i _ j _ h => hB i j (h.elim (fun hi => Or.inl (Finset.mem_filter.mp hi).2)
        (fun hj => Or.inr (Finset.mem_filter.mp hj).2)))
      G hAGA hGAG
    change (B.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.1)
        (fun j : (Finset.univ : Finset (Fin m)) => j.1)).rank =
      c + ((B - M0).submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.1)
        (fun j : (Finset.univ : Finset (Fin m)) => j.1)).rank at h1
    rw [rank_submatrix_univ B, rank_submatrix_univ (B - M0)] at h1
    exact h1
  by_cases hcr : c ≤ r
  · have hzc : (∃ B' : Matrix (Fin n) (Fin m) K, Matrix.rank B' ≤ r - c ∧
        ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B' i j = S i j) ↔
        (rkS Finset.univ C + rkS R Finset.univ ≤ r - c ∧ ∀ a : Fin d,
          rkS Finset.univ C + rkS R Finset.univ + rkS (rows a) (cols a) ≤
            r - c + rkS (rows a) C + rkS R (cols a)) :=
      zero_core_main (r' := r - c) S row col hS_zero
    constructor
    · rintro ⟨B, hBrk, hB⟩
      have hB_rc : ∀ i j, (row i = none ∨ col j = none) → B i j = A i j :=
        fun i j h => hB i j (h.elim Or.inl (fun h2 => Or.inr (Or.inl h2)))
      have hB' : ∃ B' : Matrix (Fin n) (Fin m) K, B'.rank ≤ r - c ∧
          ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B' i j = S i j := by
        refine ⟨B - M0, ?_, fun i j h => ?_⟩
        · have := hB_rank_shift B hB_rc; omega
        · change B i j - M0 i j = A i j - M0 i j; rw [hB i j h]
      have ⟨h1, h2⟩ := hzc.mp hB'
      refine ⟨?_, fun a => ?_⟩
      · dsimp only [strips]; rw [hrk_uC, hrk_Ru]; omega
      · have h2a := h2 a
        dsimp only [strips]
        rw [hrk_uC, hrk_Ru, hrk_aa a, hrk_aC a, hrk_Ra a]
        omega
    · rintro ⟨h1, h2⟩
      have hzc_rhs :
          rkS Finset.univ C + rkS R Finset.univ ≤ r - c ∧
          ∀ a : Fin d,
            rkS Finset.univ C + rkS R Finset.univ + rkS (rows a) (cols a) ≤
              r - c + rkS (rows a) C + rkS R (cols a) := by
        refine ⟨?_, fun a => ?_⟩
        · dsimp only [strips] at h1; rw [hrk_uC, hrk_Ru] at h1; omega
        · have h2a := h2 a
          dsimp only [strips] at h2a
          rw [hrk_uC, hrk_Ru, hrk_aa a, hrk_aC a, hrk_Ra a] at h2a
          omega
      rcases hzc.mpr hzc_rhs with ⟨B', hB'rk, hB'⟩
      refine ⟨B' + M0, ?_, fun i j h => ?_⟩
      · have hB_rc : ∀ i j, (row i = none ∨ col j = none) → (B' + M0) i j = A i j := by
          intro i j h
          change B' i j + M0 i j = A i j
          rw [hB' i j (h.elim Or.inl (fun h2 => Or.inr (Or.inl h2)))]
          change A i j - M0 i j + M0 i j = A i j
          ring
        have hsh := hB_rank_shift (B' + M0) hB_rc
        rw [add_sub_cancel_right] at hsh
        omega
      · change B' i j + M0 i j = A i j
        rw [hB' i j h]
        change A i j - M0 i j + M0 i j = A i j
        ring
  · constructor
    · rintro ⟨B, hBrk, hB⟩
      have hB_rc : ∀ i j, (row i = none ∨ col j = none) → B i j = A i j :=
        fun i j h => hB i j (h.elim Or.inl (fun h2 => Or.inr (Or.inl h2)))
      have := hB_rank_shift B hB_rc
      omega
    · rintro ⟨h1, _⟩
      dsimp only [strips] at h1
      rw [hrk_uC, hrk_Ru] at h1
      omega

end LinearHelpers

end PEqualNP.Outside.L_lib_991_aux

theorem PEqualNP.Outside.L_lib_991 :
∀ (K : Type) [Field K] (n m d r : ℕ) (A : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d)),
  let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
  let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
  let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
  let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
  let rk := fun (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (A.submatrix (fun i : I => i.val) (fun j : J => j.val))
  let strips := rk Finset.univ C + rk R Finset.univ
  (∃ B : Matrix (Fin n) (Fin m) K, Matrix.rank B ≤ r ∧
    ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B i j = A i j) ↔
  strips ≤ r + rk R C ∧ ∀ a : Fin d,
    strips + rk (rows a) (cols a) ≤ r + rk (rows a) C + rk R (cols a)
:= fun K _ n m d r A row col => PEqualNP.Outside.L_lib_991_aux.main_991 K n m d r A row col
