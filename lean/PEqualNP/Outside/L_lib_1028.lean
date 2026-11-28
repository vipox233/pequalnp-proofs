import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1028_aux

private lemma mem_span_range_fintype {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι]
    (v : ι → E) {x : E} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ c : ι → K, ∑ i : ι, c i • v i = x := by
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hx with ⟨c, rfl⟩
  exact ⟨fun i => c i, (Finsupp.sum_fintype c (fun i a => a • v i) (fun _ => zero_smul K _)).symm⟩

private lemma finrank_map_add_finrank_inf_ker {K E F : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F]
    (f : E →ₗ[K] F) (A : Submodule K E) :
    Module.finrank K ↥(A.map f) + Module.finrank K ↥(A ⊓ LinearMap.ker f) = Module.finrank K ↥A := by
  let g : A →ₗ[K] F := f.comp A.subtype
  have hrange : LinearMap.range g = A.map f := by
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hker_equiv : ↥(LinearMap.ker g) ≃ₗ[K] ↥(A ⊓ LinearMap.ker f) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, LinearMap.mem_ker.mp x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, LinearMap.mem_ker.mpr x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker_equiv.finrank_eq] at hrn
  exact hrn

private lemma finrank_map_sub_le {K E F : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F]
    (f : E →ₗ[K] F) {A B : Submodule K E} (hAB : A ≤ B) :
    Module.finrank K ↥(B.map f) + Module.finrank K ↥A ≤
      Module.finrank K ↥(A.map f) + Module.finrank K ↥B := by
  have hA := finrank_map_add_finrank_inf_ker f A
  have hB := finrank_map_add_finrank_inf_ker f B
  have hker : Module.finrank K ↥(A ⊓ LinearMap.ker f) ≤ Module.finrank K ↥(B ⊓ LinearMap.ker f) :=
    Submodule.finrank_mono (inf_le_inf_right _ hAB)
  omega

private lemma exists_sub_isCompl {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E]
    {A B : Submodule K E} (hAB : A ≤ B) :
    ∃ D : Submodule K E, D ≤ B ∧ A ⊓ D = ⊥ ∧ A ⊔ D = B := by
  let A' : Submodule K ↥B := A.comap B.subtype
  obtain ⟨D', hD'⟩ := Submodule.exists_isCompl A'
  refine ⟨D'.map B.subtype, Submodule.map_subtype_le B D', ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxD⟩
    rcases Submodule.mem_map.mp hxD with ⟨⟨y, hyB⟩, hyD', rfl⟩
    have hyA' : (⟨y, hyB⟩ : ↥B) ∈ A' := hxA
    have hmem : (⟨y, hyB⟩ : ↥B) ∈ A' ⊓ D' := ⟨hyA', hyD'⟩
    rw [hD'.inf_eq_bot, Submodule.mem_bot] at hmem
    have hy0 : y = 0 := congrArg Subtype.val hmem
    rw [Submodule.mem_bot]
    exact hy0
  · apply le_antisymm
    · exact sup_le hAB (Submodule.map_subtype_le B D')
    · intro x hxB
      have hmem : (⟨x, hxB⟩ : ↥B) ∈ A' ⊔ D' := by rw [hD'.sup_eq_top]; trivial
      rcases Submodule.mem_sup.mp hmem with ⟨⟨u, huB⟩, huA', ⟨v, hvB⟩, hvD', hsum⟩
      have hx : x = u + v := (congrArg Subtype.val hsum).symm
      rw [hx]
      exact Submodule.add_mem_sup huA' (Submodule.mem_map.mpr ⟨⟨v, hvB⟩, hvD', rfl⟩)

private lemma finrank_sup_eq_of_inf_bot {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {A B : Submodule K E} (h : A ⊓ B = ⊥) :
    Module.finrank K ↥(A ⊔ B) = Module.finrank K ↥A + Module.finrank K ↥B := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [h, finrank_bot, add_zero] at h1
  exact h1

private lemma exists_surj_of_finrank_le {K E F : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (h : Module.finrank K F ≤ Module.finrank K E) :
    ∃ g : E →ₗ[K] F, Function.Surjective g := by
  let bE := Module.finBasis K E
  let bF := Module.finBasis K F
  let g : E →ₗ[K] F := bE.constr K (fun i => if hi : i.val < Module.finrank K F then bF ⟨i.val, hi⟩ else 0)
  refine ⟨g, ?_⟩
  have hrange : LinearMap.range g = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y = ∑ j : Fin (Module.finrank K F), bF.repr y j • bF j := (bF.sum_repr y).symm
    rw [hy]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_)
    refine ⟨bE ⟨j.val, lt_of_lt_of_le j.isLt h⟩, ?_⟩
    dsimp only [g]
    rw [Module.Basis.constr_basis]
    simp [j.isLt]
  exact LinearMap.range_eq_top.mp hrange

private lemma exists_surj_extension {K E F : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (U : Submodule K E) (f : ↥U →ₗ[K] F) (S : Submodule K F)
    (hfS : LinearMap.range f ≤ S)
    (hdim : Module.finrank K ↥S - Module.finrank K ↥(LinearMap.range f) ≤
      Module.finrank K E - Module.finrank K ↥U) :
    ∃ extF : E →ₗ[K] F, (∀ u : ↥U, extF u.1 = f u) ∧ LinearMap.range extF = S := by
  obtain ⟨C, hUC⟩ := Submodule.exists_isCompl U
  obtain ⟨D, hDS, hinfD, hsupD⟩ := exists_sub_isCompl hfS
  have hfinU : Module.finrank K ↥U + Module.finrank K ↥C = Module.finrank K E := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U C
    rw [hUC.sup_eq_top, hUC.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h1
    exact h1.symm
  have hfinD : Module.finrank K ↥(LinearMap.range f) + Module.finrank K ↥D = Module.finrank K ↥S := by
    have h1 := finrank_sup_eq_of_inf_bot hinfD
    rw [hsupD] at h1
    exact h1.symm
  have hDC : Module.finrank K ↥D ≤ Module.finrank K ↥C := by omega
  obtain ⟨g, hg⟩ := exists_surj_of_finrank_le hDC
  let pU : E →ₗ[K] ↥U := Submodule.projectionOnto U C hUC
  let pC : E →ₗ[K] ↥C := Submodule.projectionOnto C U hUC.symm
  let extF : E →ₗ[K] F := f.comp pU + (D.subtype.comp g).comp pC
  refine ⟨extF, ?_, ?_⟩
  · intro u
    have h1 : pU u.1 = u := Submodule.projectionOnto_apply_left hUC u
    have h2 : pC u.1 = 0 := Submodule.projectionOnto_apply_right hUC.symm u
    simp only [extF, LinearMap.add_apply, LinearMap.comp_apply, h1, h2, map_zero, add_zero]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      simp only [extF, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype]
      exact S.add_mem (hfS ⟨pU x, rfl⟩) (hDS (g (pC x)).2)
    · intro y hyS
      rw [← hsupD] at hyS
      rcases Submodule.mem_sup.mp hyS with ⟨y1, ⟨u, rfl⟩, y2, hy2D, rfl⟩
      obtain ⟨c, hc⟩ := hg ⟨y2, hy2D⟩
      refine ⟨u.1 + c.1, ?_⟩
      have hpU_u : pU u.1 = u := Submodule.projectionOnto_apply_left hUC u
      have hpU_c : pU c.1 = 0 := Submodule.projectionOnto_apply_right hUC c
      have hpC_u : pC u.1 = 0 := Submodule.projectionOnto_apply_right hUC.symm u
      have hpC_c : pC c.1 = c := Submodule.projectionOnto_apply_left hUC.symm c
      simp only [extF, LinearMap.add_apply, LinearMap.comp_apply, map_add,
        hpU_u, hpU_c, hpC_u, hpC_c, map_zero, add_zero, zero_add, hc,
        Submodule.coe_subtype]

private lemma exists_bag_lift {K V Y Z : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    (π : Y →ₗ[K] Z)
    (VR : Submodule K V)
    (Pi PR : Submodule K Y) (hPR : PR ≤ Pi)
    (φR : ↥VR →ₗ[K] Y) (hφR : LinearMap.range φR = PR)
    (Φv : V →ₗ[K] Z) (hcompat : ∀ z : ↥VR, Φv z.1 = π (φR z))
    (hPi_sub : Pi.map π ≤ LinearMap.range Φv)
    (hineq : Module.finrank K ↥VR + Module.finrank K ↥Pi + Module.finrank K ↥(LinearMap.range Φv) ≤
      Module.finrank K V + Module.finrank K ↥PR + Module.finrank K ↥(Pi.map π)) :
    ∃ (Ui : Submodule K V) (hVR : VR ≤ Ui) (ψ : ↥Ui →ₗ[K] Y),
      Module.finrank K ↥Ui + Module.finrank K ↥PR = Module.finrank K ↥VR + Module.finrank K ↥Pi ∧
      (∀ z : ↥VR, ψ ⟨z.1, hVR z.2⟩ = φR z) ∧
      (∀ z : ↥Ui, π (ψ z) = Φv z.1) ∧
      LinearMap.range ψ = Pi := by
  let QR : Submodule K Z := PR.map π
  let Qi : Submodule K Z := Pi.map π
  have hQR_le_Qi : QR ≤ Qi := Submodule.map_mono hPR
  obtain ⟨D1, hD1_le, hD1_inf, hD1_sup⟩ := exists_sub_isCompl hQR_le_Qi
  let d1 := Module.finrank K ↥D1
  let b1 : Module.Basis (Fin d1) K ↥D1 := Module.finBasis K ↥D1
  have hp1_ex : ∀ t : Fin d1, ∃ p : Y, p ∈ Pi ∧ π p = (b1 t).1 := fun t =>
    Submodule.mem_map.mp (hD1_le (b1 t).2)
  choose p1 hp1_mem hp1_pi using hp1_ex
  have hv1_ex : ∀ t : Fin d1, ∃ v : V, Φv v = (b1 t).1 := fun t =>
    LinearMap.mem_range.mp (hPi_sub (hD1_le (b1 t).2))
  choose v1 hv1_phi using hv1_ex
  let L1 : Submodule K V := Submodule.span K (Set.range v1)
  have hv1_li : LinearIndependent K v1 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hphi : Φv (∑ t : Fin d1, c t • v1 t) = 0 := by rw [hc, map_zero]
    rw [map_sum] at hphi
    have hsum : (∑ t : Fin d1, c t • b1 t) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      simpa only [map_smul, hv1_phi] using hphi
    exact Fintype.linearIndependent_iff.mp b1.linearIndependent c hsum
  have hVR_L1_inf : VR ⊓ L1 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxR, hxL1⟩
    rcases mem_span_range_fintype v1 hxL1 with ⟨c, rfl⟩
    have h1 : Φv (∑ t : Fin d1, c t • v1 t) ∈ QR := by
      rw [hcompat ⟨_, hxR⟩]
      exact Submodule.mem_map.mpr ⟨φR ⟨_, hxR⟩, hφR ▸ ⟨⟨_, hxR⟩, rfl⟩, rfl⟩
    have h2 : Φv (∑ t : Fin d1, c t • v1 t) ∈ D1 := by
      rw [map_sum]
      refine Submodule.sum_mem _ (fun t _ => ?_)
      rw [map_smul, hv1_phi]
      exact D1.smul_mem _ (b1 t).2
    have h0 : Φv (∑ t : Fin d1, c t • v1 t) = 0 := by
      have : Φv (∑ t : Fin d1, c t • v1 t) ∈ QR ⊓ D1 := ⟨h1, h2⟩
      rwa [hD1_inf, Submodule.mem_bot] at this
    have hsum : (∑ t : Fin d1, c t • b1 t) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      simpa only [map_sum, map_smul, hv1_phi] using h0
    have hc0 := Fintype.linearIndependent_iff.mp b1.linearIndependent c hsum
    simp [hc0]
  have hL1_dim : Module.finrank K ↥L1 = d1 := by
    dsimp only [L1]
    rw [finrank_span_eq_card hv1_li, Fintype.card_fin]
  have hp1_li : LinearIndependent K p1 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hpi : π (∑ t : Fin d1, c t • p1 t) = 0 := by rw [hc, map_zero]
    rw [map_sum] at hpi
    have hsum : (∑ t : Fin d1, c t • b1 t) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      simpa only [map_smul, hp1_pi] using hpi
    exact Fintype.linearIndependent_iff.mp b1.linearIndependent c hsum
  let Sp1 : Submodule K Y := Submodule.span K (Set.range p1)
  have hPR_Sp1_inf : PR ⊓ Sp1 = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyR, hy1⟩
    rcases mem_span_range_fintype p1 hy1 with ⟨c, rfl⟩
    have h1 : π (∑ t : Fin d1, c t • p1 t) ∈ QR := Submodule.mem_map_of_mem hyR
    have h2 : π (∑ t : Fin d1, c t • p1 t) ∈ D1 := by
      rw [map_sum]
      refine Submodule.sum_mem _ (fun t _ => ?_)
      rw [map_smul, hp1_pi]
      exact D1.smul_mem _ (b1 t).2
    have h0 : π (∑ t : Fin d1, c t • p1 t) = 0 := by
      have : π (∑ t : Fin d1, c t • p1 t) ∈ QR ⊓ D1 := ⟨h1, h2⟩
      rwa [hD1_inf, Submodule.mem_bot] at this
    have hsum : (∑ t : Fin d1, c t • b1 t) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      simpa only [map_sum, map_smul, hp1_pi] using h0
    have hc0 := Fintype.linearIndependent_iff.mp b1.linearIndependent c hsum
    simp [hc0]
  let P1 : Submodule K Y := PR ⊔ Sp1
  have hP1_le_Pi : P1 ≤ Pi := sup_le hPR (Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hp1_mem t))
  have hP1_dim : Module.finrank K ↥P1 = Module.finrank K ↥PR + d1 := by
    rw [finrank_sup_eq_of_inf_bot hPR_Sp1_inf, finrank_span_eq_card hp1_li, Fintype.card_fin]
  have hP1_map : P1.map π = Qi := by
    apply le_antisymm (Submodule.map_mono hP1_le_Pi)
    change Qi ≤ P1.map π
    rw [← hD1_sup]
    refine sup_le (Submodule.map_mono le_sup_left) ?_
    intro z hzD1
    have hz : (⟨z, hzD1⟩ : ↥D1) = ∑ t : Fin d1, b1.repr ⟨z, hzD1⟩ t • b1 t := (b1.sum_repr _).symm
    have hz' : z = ∑ t : Fin d1, b1.repr ⟨z, hzD1⟩ t • (b1 t).1 := by
      simpa only [Submodule.coe_sum, SetLike.val_smul] using congrArg Subtype.val hz
    refine Submodule.mem_map.mpr ⟨∑ t : Fin d1, b1.repr ⟨z, hzD1⟩ t • p1 t, ?_, ?_⟩
    · refine Submodule.mem_sup_right (Submodule.sum_mem _ (fun t _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)))
    · rw [map_sum]
      conv_rhs => rw [hz']
      refine Finset.sum_congr rfl (fun t _ => by rw [map_smul, hp1_pi])
  let KP : Submodule K Y := Pi ⊓ LinearMap.ker π
  obtain ⟨D2, hD2_le_KP, hD2_inf, hD2_sup⟩ := exists_sub_isCompl (inf_le_right : P1 ⊓ KP ≤ KP)
  have hP1_D2_inf : P1 ⊓ D2 = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    have : y ∈ (P1 ⊓ KP) ⊓ D2 := ⟨⟨hy1, hD2_le_KP hy2⟩, hy2⟩
    rwa [hD2_inf, Submodule.mem_bot] at this
  have hP1_D2_sup : P1 ⊔ D2 = Pi := by
    apply le_antisymm (sup_le hP1_le_Pi (le_trans hD2_le_KP inf_le_left))
    intro y hyPi
    have hpy : π y ∈ P1.map π := by rw [hP1_map]; exact Submodule.mem_map_of_mem hyPi
    rcases Submodule.mem_map.mp hpy with ⟨y1, hy1, hy1_pi⟩
    have hdiff_KP : y - y1 ∈ KP := ⟨Pi.sub_mem hyPi (hP1_le_Pi hy1),
      LinearMap.mem_ker.mpr (by rw [map_sub, hy1_pi, sub_self])⟩
    rw [← hD2_sup] at hdiff_KP
    rcases Submodule.mem_sup.mp hdiff_KP with ⟨a, ha, d, hd, had⟩
    have hy_eq : y = (y1 + a) + d := by
      rw [← sub_eq_zero]
      have hsub : y - ((y1 + a) + d) = (y - y1) - (a + d) := by abel
      rw [hsub, had, sub_self]
    rw [hy_eq]
    exact Submodule.add_mem_sup (P1.add_mem hy1 ha.1) hd
  let d2 := Module.finrank K ↥D2
  let b2 : Module.Basis (Fin d2) K ↥D2 := Module.finBasis K ↥D2
  have hPi_dim : Module.finrank K ↥Pi = Module.finrank K ↥PR + d1 + d2 := by
    have h1 := finrank_sup_eq_of_inf_bot hP1_D2_inf
    rw [hP1_D2_sup, hP1_dim] at h1
    exact h1
  let KV : Submodule K V := LinearMap.ker Φv
  obtain ⟨CK, hCK_le_KV, hCK_inf, hCK_sup⟩ := exists_sub_isCompl (inf_le_right : VR ⊓ KV ≤ KV)
  have hQR_dim : Module.finrank K ↥QR + d1 = Module.finrank K ↥(Pi.map π) := by
    have h1 := finrank_sup_eq_of_inf_bot hD1_inf
    rw [hD1_sup] at h1
    exact h1.symm
  have hVR_map : VR.map Φv = QR := by
    ext z
    simp only [Submodule.mem_map, QR]
    constructor
    · rintro ⟨x, hxR, rfl⟩
      rw [hcompat ⟨x, hxR⟩]
      exact ⟨φR ⟨x, hxR⟩, hφR ▸ ⟨⟨x, hxR⟩, rfl⟩, rfl⟩
    · rintro ⟨y, hyPR, rfl⟩
      rw [← hφR] at hyPR
      rcases hyPR with ⟨⟨x, hxR⟩, rfl⟩
      exact ⟨x, hxR, hcompat ⟨x, hxR⟩⟩
  have hVR_KV_dim : Module.finrank K ↥QR + Module.finrank K ↥(VR ⊓ KV) = Module.finrank K ↥VR := by
    have h1 := finrank_map_add_finrank_inf_ker Φv VR
    rw [hVR_map] at h1
    exact h1
  have hKV_dim : Module.finrank K ↥(LinearMap.range Φv) + Module.finrank K ↥KV = Module.finrank K V :=
    LinearMap.finrank_range_add_finrank_ker Φv
  have hCK_dim : Module.finrank K ↥(VR ⊓ KV) + Module.finrank K ↥CK = Module.finrank K ↥KV := by
    have h1 := finrank_sup_eq_of_inf_bot hCK_inf
    rw [hCK_sup] at h1
    exact h1.symm
  have hd2_le_CK : d2 ≤ Module.finrank K ↥CK := by omega
  let bCK : Module.Basis (Fin (Module.finrank K ↥CK)) K ↥CK := Module.finBasis K ↥CK
  let v2 : Fin d2 → V := fun t => (bCK ⟨t.val, lt_of_lt_of_le t.isLt hd2_le_CK⟩).1
  have hv2_mem_CK : ∀ t : Fin d2, v2 t ∈ CK := fun t => (bCK ⟨t.val, lt_of_lt_of_le t.isLt hd2_le_CK⟩).2
  have hv2_li : LinearIndependent K v2 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let c' : Fin (Module.finrank K ↥CK) → K := fun j =>
      if hj : j.val < d2 then c ⟨j.val, hj⟩ else 0
    have hsum : (∑ j : Fin (Module.finrank K ↥CK), c' j • bCK j) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      have hsplit : (∑ j : Fin (Module.finrank K ↥CK), c' j • (bCK j).1) =
          ∑ t : Fin d2, c t • v2 t := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun j : Fin (Module.finrank K ↥CK) => j.val < d2) Finset.univ)]
        · refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro j1 _ j2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
          · intro t _
            refine ⟨⟨t.val, lt_of_lt_of_le t.isLt hd2_le_CK⟩, ?_, Fin.ext rfl⟩
            simp [t.isLt]
          · intro j hj
            have hlt : j.val < d2 := (Finset.mem_filter.mp hj).2
            simp [c', hlt, v2]
        · intro j _ hnot
          have hge : ¬ j.val < d2 := by simpa using hnot
          simp [c', hge]
      rw [hsplit, hc]
    have hc'0 := Fintype.linearIndependent_iff.mp bCK.linearIndependent c' hsum
    intro t
    have := hc'0 ⟨t.val, lt_of_lt_of_le t.isLt hd2_le_CK⟩
    simpa [c', t.isLt] using this
  let L2 : Submodule K V := Submodule.span K (Set.range v2)
  have hL2_le_CK : L2 ≤ CK := Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hv2_mem_CK t)
  have hVRL1_L2_inf : (VR ⊔ L1) ⊓ L2 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hxCK : x ∈ CK := hL2_le_CK hx2
    have hxKV : x ∈ KV := hCK_le_KV hxCK
    have hphix : Φv x = 0 := LinearMap.mem_ker.mp hxKV
    rcases Submodule.mem_sup.mp hx1 with ⟨z, hzR, l1, hl1, rfl⟩
    rcases mem_span_range_fintype v1 hl1 with ⟨c, rfl⟩
    have hphi_l1_eq : Φv (∑ t : Fin d1, c t • v1 t) = - Φv z := by
      have := hphix
      rw [map_add] at this
      exact eq_neg_of_add_eq_zero_right this
    have hmem_QR : Φv (∑ t : Fin d1, c t • v1 t) ∈ QR := by
      rw [hphi_l1_eq]
      exact QR.neg_mem (by
        rw [hcompat ⟨z, hzR⟩]
        exact Submodule.mem_map.mpr ⟨φR ⟨z, hzR⟩, hφR ▸ ⟨⟨z, hzR⟩, rfl⟩, rfl⟩)
    have hmem_D1 : Φv (∑ t : Fin d1, c t • v1 t) ∈ D1 := by
      rw [map_sum]
      refine Submodule.sum_mem _ (fun t _ => ?_)
      rw [map_smul, hv1_phi]
      exact D1.smul_mem _ (b1 t).2
    have hphi_l1_0 : Φv (∑ t : Fin d1, c t • v1 t) = 0 := by
      have : Φv (∑ t : Fin d1, c t • v1 t) ∈ QR ⊓ D1 := ⟨hmem_QR, hmem_D1⟩
      rwa [hD1_inf, Submodule.mem_bot] at this
    have hsum : (∑ t : Fin d1, c t • b1 t) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      simpa only [map_sum, map_smul, hv1_phi] using hphi_l1_0
    have hc0 := Fintype.linearIndependent_iff.mp b1.linearIndependent c hsum
    have hl1_0 : (∑ t : Fin d1, c t • v1 t) = 0 := by simp [hc0]
    rw [hl1_0, add_zero] at hxCK hxKV ⊢
    have : z ∈ (VR ⊓ KV) ⊓ CK := ⟨⟨hzR, hxKV⟩, hxCK⟩
    rwa [hCK_inf, Submodule.mem_bot] at this
  let U1 : Submodule K V := VR ⊔ L1
  let Ui : Submodule K V := U1 ⊔ L2
  have hVR_le_Ui : VR ≤ Ui := le_trans le_sup_left le_sup_left
  have hUi_dim : Module.finrank K ↥Ui + Module.finrank K ↥PR =
      Module.finrank K ↥VR + Module.finrank K ↥Pi := by
    have h1 := finrank_sup_eq_of_inf_bot hVRL1_L2_inf
    have h2 := finrank_sup_eq_of_inf_bot hVR_L1_inf
    have hL2_dim : Module.finrank K ↥L2 = d2 := by
      dsimp only [L2]
      rw [finrank_span_eq_card hv2_li, Fintype.card_fin]
    dsimp only [Ui, U1]
    rw [h1, h2, hL1_dim, hL2_dim, hPi_dim]
    omega
  let e1 : (↥VR × ↥L1) ≃ₗ[K] ↥U1 :=
    LinearEquiv.ofBijective
      ((Submodule.inclusion (le_sup_left : VR ≤ U1)).coprod (Submodule.inclusion (le_sup_right : L1 ≤ U1)))
      ⟨fun ⟨⟨a1, ha1⟩, ⟨b1', hb1'⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2', hb2'⟩⟩ heq => by
        have hv : a1 + b1' = a2 + b2' := congrArg Subtype.val heq
        have hsub : a1 - a2 = b2' - b1' := by
          rw [sub_eq_sub_iff_add_eq_add]; exact hv.trans (add_comm _ _)
        have hmem : a1 - a2 ∈ VR ⊓ L1 := ⟨VR.sub_mem ha1 ha2, hsub ▸ L1.sub_mem hb2' hb1'⟩
        rw [hVR_L1_inf, Submodule.mem_bot] at hmem
        have ha : a1 = a2 := sub_eq_zero.mp hmem
        have hb : b1' = b2' := (sub_eq_zero.mp (hsub ▸ hmem)).symm
        exact Prod.ext (Subtype.ext ha) (Subtype.ext hb),
       fun ⟨x, hx⟩ => by
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩
  let e2 : (↥U1 × ↥L2) ≃ₗ[K] ↥Ui :=
    LinearEquiv.ofBijective
      ((Submodule.inclusion (le_sup_left : U1 ≤ Ui)).coprod (Submodule.inclusion (le_sup_right : L2 ≤ Ui)))
      ⟨fun ⟨⟨a1, ha1⟩, ⟨b1', hb1'⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2', hb2'⟩⟩ heq => by
        have hv : a1 + b1' = a2 + b2' := congrArg Subtype.val heq
        have hsub : a1 - a2 = b2' - b1' := by
          rw [sub_eq_sub_iff_add_eq_add]; exact hv.trans (add_comm _ _)
        have hmem : a1 - a2 ∈ U1 ⊓ L2 := ⟨U1.sub_mem ha1 ha2, hsub ▸ L2.sub_mem hb2' hb1'⟩
        rw [hVRL1_L2_inf, Submodule.mem_bot] at hmem
        have ha : a1 = a2 := sub_eq_zero.mp hmem
        have hb : b1' = b2' := (sub_eq_zero.mp (hsub ▸ hmem)).symm
        exact Prod.ext (Subtype.ext ha) (Subtype.ext hb),
       fun ⟨x, hx⟩ => by
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩
  let bL1 : Module.Basis (Fin d1) K ↥L1 := Module.Basis.span hv1_li
  let bL2 : Module.Basis (Fin d2) K ↥L2 := Module.Basis.span hv2_li
  let ψ1 : ↥L1 →ₗ[K] Y := bL1.constr K p1
  let ψ2 : ↥L2 →ₗ[K] Y := bL2.constr K (fun t => (b2 t).1)
  let ψU1 : ↥U1 →ₗ[K] Y := (φR.coprod ψ1).comp e1.symm.toLinearMap
  let ψ : ↥Ui →ₗ[K] Y := (ψU1.coprod ψ2).comp e2.symm.toLinearMap
  have hψ1_val : ∀ t : Fin d1, ψ1 ⟨v1 t, Submodule.subset_span ⟨t, rfl⟩⟩ = p1 t := by
    intro t
    have hb : bL1 t = ⟨v1 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv1_li t
    rw [← hb]
    exact Module.Basis.constr_basis bL1 K p1 t
  have hψ2_val : ∀ t : Fin d2, ψ2 ⟨v2 t, Submodule.subset_span ⟨t, rfl⟩⟩ = (b2 t).1 := by
    intro t
    have hb : bL2 t = ⟨v2 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv2_li t
    rw [← hb]
    exact Module.Basis.constr_basis bL2 K (fun t => (b2 t).1) t
  have hψ_VR : ∀ z : ↥VR, ψ ⟨z.1, hVR_le_Ui z.2⟩ = φR z := by
    intro z
    have h1 : e1 (z, 0) = ⟨z.1, (le_sup_left : VR ≤ U1) z.2⟩ := by
      apply Subtype.ext; change z.1 + 0 = z.1; exact add_zero z.1
    have h2 : e2 (⟨z.1, (le_sup_left : VR ≤ U1) z.2⟩, 0) = ⟨z.1, hVR_le_Ui z.2⟩ := by
      apply Subtype.ext; change z.1 + 0 = z.1; exact add_zero z.1
    dsimp only [ψ, ψU1, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h2, LinearEquiv.symm_apply_apply, LinearMap.coprod_apply, map_zero, add_zero]
    dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h1, LinearEquiv.symm_apply_apply, LinearMap.coprod_apply, map_zero, add_zero]
  have hψ_compat : ∀ z : ↥Ui, π (ψ z) = Φv z.1 := by
    intro z
    rcases e2.surjective z with ⟨⟨u1, l2⟩, rfl⟩
    rcases e1.surjective u1 with ⟨⟨r0, l1⟩, rfl⟩
    have hval : (e2 (e1 (r0, l1), l2)).1 = r0.1 + l1.1 + l2.1 := rfl
    have hψ_val : ψ (e2 (e1 (r0, l1), l2)) = φR r0 + ψ1 l1 + ψ2 l2 := by
      dsimp only [ψ, ψU1, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply, LinearMap.coprod_apply]
      dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply, LinearMap.coprod_apply]
    rw [hψ_val, hval, map_add, map_add, map_add, map_add, hcompat r0]
    have hl1_eq : π (ψ1 l1) = Φv l1.1 := by
      have hl : l1 = ∑ t : Fin d1, bL1.repr l1 t • bL1 t := (bL1.sum_repr l1).symm
      conv_lhs => rw [hl]
      have hl_val : l1.1 = ∑ t : Fin d1, bL1.repr l1 t • v1 t := by
        have h := congrArg Subtype.val hl
        rw [Submodule.coe_sum] at h
        refine h.trans (Finset.sum_congr rfl (fun t _ => ?_))
        rw [SetLike.val_smul, Module.Basis.span_apply]
      rw [hl_val, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [map_smul, map_smul, map_smul]
      congr 1
      have hb : bL1 t = ⟨v1 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv1_li t
      rw [hb, hψ1_val t, hp1_pi t, hv1_phi t]
    have hl2_eq : π (ψ2 l2) = Φv l2.1 := by
      have hphi2 : Φv l2.1 = 0 := LinearMap.mem_ker.mp (hCK_le_KV (hL2_le_CK l2.2))
      have hpi2 : π (ψ2 l2) = 0 := by
        have hl : l2 = ∑ t : Fin d2, bL2.repr l2 t • bL2 t := (bL2.sum_repr l2).symm
        rw [hl, map_sum, map_sum]
        refine Finset.sum_eq_zero (fun t _ => ?_)
        rw [map_smul, map_smul]
        have hb : bL2 t = ⟨v2 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv2_li t
        rw [hb, hψ2_val t, LinearMap.mem_ker.mp (hD2_le_KP (b2 t).2).2, smul_zero]
      rw [hpi2, hphi2]
    rw [hl1_eq, hl2_eq]
  have hψ_range : LinearMap.range ψ = Pi := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      rcases e2.surjective z with ⟨⟨u1, l2⟩, rfl⟩
      rcases e1.surjective u1 with ⟨⟨r0, l1⟩, rfl⟩
      have hψ_val : ψ (e2 (e1 (r0, l1), l2)) = φR r0 + ψ1 l1 + ψ2 l2 := by
        dsimp only [ψ, ψU1, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [LinearEquiv.symm_apply_apply, LinearMap.coprod_apply]
        dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [LinearEquiv.symm_apply_apply, LinearMap.coprod_apply]
      rw [hψ_val]
      refine Pi.add_mem (Pi.add_mem (hPR (hφR ▸ ⟨r0, rfl⟩)) ?_) ?_
      · have hl : l1 = ∑ t : Fin d1, bL1.repr l1 t • bL1 t := (bL1.sum_repr l1).symm
        rw [hl, map_sum]
        refine Submodule.sum_mem _ (fun t _ => ?_)
        rw [map_smul]
        have hb : bL1 t = ⟨v1 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv1_li t
        rw [hb, hψ1_val t]
        exact Pi.smul_mem _ (hp1_mem t)
      · have hl : l2 = ∑ t : Fin d2, bL2.repr l2 t • bL2 t := (bL2.sum_repr l2).symm
        rw [hl, map_sum]
        refine Submodule.sum_mem _ (fun t _ => ?_)
        rw [map_smul]
        have hb : bL2 t = ⟨v2 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv2_li t
        rw [hb, hψ2_val t]
        exact Pi.smul_mem _ (hD2_le_KP (b2 t).2).1
    · intro y hyPi
      rw [← hP1_D2_sup] at hyPi
      rcases Submodule.mem_sup.mp hyPi with ⟨y1, hy1, y2, hy2D2, rfl⟩
      rcases Submodule.mem_sup.mp hy1 with ⟨yr, hyr, ys, hys, rfl⟩
      rw [← hφR] at hyr
      rcases hyr with ⟨r0, rfl⟩
      rcases mem_span_range_fintype p1 hys with ⟨c1, rfl⟩
      have hy2 : (⟨y2, hy2D2⟩ : ↥D2) = ∑ t : Fin d2, b2.repr ⟨y2, hy2D2⟩ t • b2 t := (b2.sum_repr _).symm
      let l1 : ↥L1 := ∑ t : Fin d1, c1 t • bL1 t
      let l2 : ↥L2 := ∑ t : Fin d2, b2.repr ⟨y2, hy2D2⟩ t • bL2 t
      refine ⟨e2 (e1 (r0, l1), l2), ?_⟩
      dsimp only [ψ, ψU1, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply, LinearMap.coprod_apply]
      dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply, LinearMap.coprod_apply]
      congr 1
      · congr 1
        dsimp only [l1]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [map_smul]
        have hb : bL1 t = ⟨v1 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv1_li t
        rw [hb, hψ1_val t]
      · dsimp only [l2]
        rw [map_sum]
        have hy2' : y2 = ∑ t : Fin d2, b2.repr ⟨y2, hy2D2⟩ t • (b2 t).1 := by
          simpa only [Submodule.coe_sum, SetLike.val_smul] using congrArg Subtype.val hy2
        conv_rhs => rw [hy2']
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [map_smul]
        have hb : bL2 t = ⟨v2 t, Submodule.subset_span ⟨t, rfl⟩⟩ := Module.Basis.span_apply hv2_li t
        rw [hb, hψ2_val t]
  exact ⟨Ui, hVR_le_Ui, ψ, hUi_dim, hψ_VR, hψ_compat, hψ_range⟩

private lemma rank_eq_finrank_rowSpan {K : Type*} [Field K] {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J K) :
    Matrix.rank M = Module.finrank K ↥(Submodule.span K (Set.range (fun i : I => M i))) := by
  rw [← Matrix.rank_transpose]
  change Module.finrank K ↥(LinearMap.range M.transpose.mulVecLin) = _
  have hrange : LinearMap.range M.transpose.mulVecLin = Submodule.span K (Set.range (fun i : I => M i)) := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      have hsum : M.transpose.mulVecLin c = ∑ i : I, c i • M i := by
        funext j
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [hsum]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · intro hy
      rcases mem_span_range_fintype (fun i : I => M i) hy with ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      funext j
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hrange]

private lemma rowSpan_submatrix_map {K : Type*} [Field K] {n m : ℕ}
    (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) {J1 J2 : Finset (Fin m)} (hJ : J1 ⊆ J2) :
    let res : (↥J2 → K) →ₗ[K] (↥J1 → K) :=
      { toFun := fun f y => f ⟨y.val, hJ y.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    (Submodule.span K (Set.range (fun x : ↥I => fun y : ↥J2 => T x.val y.val))).map res =
      Submodule.span K (Set.range (fun x : ↥I => fun y : ↥J1 => T x.val y.val)) := by
  intro res
  rw [Submodule.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  rfl

private lemma rowSpan_mono {K : Type*} [Field K] {n m : ℕ}
    (T : Matrix (Fin n) (Fin m) K) {I1 I2 : Finset (Fin n)} (hI : I1 ⊆ I2) (J : Finset (Fin m)) :
    Submodule.span K (Set.range (fun x : ↥I1 => fun y : ↥J => T x.val y.val)) ≤
      Submodule.span K (Set.range (fun x : ↥I2 => fun y : ↥J => T x.val y.val)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  exact ⟨⟨x, hI hx⟩, rfl⟩

private lemma rank_factor_le {K : Type*} [Field K] {n m r : ℕ}
    (u : Fin n → (Fin r → K)) (w : Fin m → ((Fin r → K) →ₗ[K] K)) :
    Matrix.rank (fun x y => w y (u x) : Matrix (Fin n) (Fin m) K) ≤ r := by
  let G : Matrix (Fin n) (Fin m) K := fun x y => w y (u x)
  let U : Matrix (Fin n) (Fin r) K := fun x k => u x k
  let W : Matrix (Fin r) (Fin m) K := fun k y => w y (Pi.single k 1)
  have hGW : G = U * W := by
    ext x y
    change w y (u x) = ∑ k : Fin r, u x k * w y (Pi.single k 1)
    have hux : u x = ∑ k : Fin r, u x k • Pi.single k (1 : K) := by
      funext k0
      rw [Finset.sum_apply, Finset.sum_eq_single k0]
      · simp
      · intro k _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    conv_lhs => rw [hux]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => by rw [map_smul, smul_eq_mul])
  change Matrix.rank G ≤ r
  rw [hGW]
  calc Matrix.rank (U * W) ≤ Matrix.rank U := Matrix.rank_mul_le_left U W
    _ ≤ r := by
        have h := Matrix.rank_le_width U
        simpa [Fintype.card_fin] using h

end PEqualNP.Outside.L_lib_1028_aux

open PEqualNP.Outside.L_lib_1028_aux

theorem PEqualNP.Outside.L_lib_1028 :
    (∀ (K : Type) [Field K] (n m a b r : ℕ) (T : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin a)) (col : Fin m → Fin b) (bags : Fin a → Finset (Fin b)),
  (∀ i : Fin a, ((bags i) ∩ ((Finset.univ.filter (fun j : Fin a => j < i)).biUnion bags)).card ≤ 1) →
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let cols := fun i : Fin a => (Finset.univ : Finset (Fin m)).filter (fun y => col y ∈ bags i)
  let group := fun v : Fin b => (Finset.univ : Finset (Fin m)).filter (fun y => col y = v)
  let star := fun v : Fin b => R ∪ Finset.univ.filter
    (fun x : Fin n => ∃ i : Fin a, row x = some i ∧ v ∈ bags i)
  let rk := fun (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (T.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let base := rk R Finset.univ
  ((∃ G : Matrix (Fin n) (Fin m) K, Matrix.rank G ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ col y ∈ bags i) → G x y = T x y) ↔
    base ≤ r ∧ ∀ (i : Fin a) (v : Fin b), v ∈ bags i →
      base + rk (rows i) (cols i) + rk (star v) (group v) ≤
        r + rk R (cols i) + rk (rows i) (group v))) := by
  intro K _ n m a b r T row col bags hforest
  dsimp only
  let R : Finset (Fin n) := Finset.univ.filter (fun x => row x = none)
  let rows : Fin a → Finset (Fin n) := fun i => R ∪ Finset.univ.filter (fun x => row x = some i)
  let cols : Fin a → Finset (Fin m) := fun i => Finset.univ.filter (fun y => col y ∈ bags i)
  let group : Fin b → Finset (Fin m) := fun v => Finset.univ.filter (fun y => col y = v)
  let star : Fin b → Finset (Fin n) := fun v =>
    R ∪ Finset.univ.filter (fun x : Fin n => ∃ i : Fin a, row x = some i ∧ v ∈ bags i)
  let rk : Finset (Fin n) → Finset (Fin m) → ℕ :=
    fun I J => Matrix.rank (T.submatrix (fun x : ↥I => x.val) (fun y : ↥J => y.val))
  let base : ℕ := rk R Finset.univ
  let rowSp : Matrix (Fin n) (Fin m) K → Finset (Fin n) → (J : Finset (Fin m)) → Submodule K (↥J → K) :=
    fun M I J => Submodule.span K (Set.range (fun x : ↥I => fun y : ↥J => M x.val y.val))
  have hrk_eq : ∀ I J, rk I J = Module.finrank K ↥(rowSp T I J) := fun I J =>
    rank_eq_finrank_rowSpan (T.submatrix (fun x : ↥I => x.val) (fun y : ↥J => y.val))
  constructor
  · rintro ⟨G, hGr, hGT⟩
    have hsub_eq : ∀ (I : Finset (Fin n)) (J : Finset (Fin m)),
        (∀ x ∈ I, ∀ y ∈ J, G x y = T x y) →
        rk I J = Module.finrank K ↥(rowSp G I J) := by
      intro I J hIJ
      have hrow_eq : rowSp T I J = rowSp G I J := by
        dsimp only [rowSp]
        have hset : (fun x : ↥I => fun y : ↥J => T x.val y.val) =
            (fun x : ↥I => fun y : ↥J => G x.val y.val) := by
          funext x y; exact (hIJ x.val x.2 y.val y.2).symm
        rw [hset]
      rw [hrk_eq, hrow_eq]
    have hG_univ : Module.finrank K ↥(rowSp G Finset.univ Finset.univ) = Matrix.rank G := by
      rw [rank_eq_finrank_rowSpan G]
      let eCol : (↥(Finset.univ : Finset (Fin m)) → K) ≃ₗ[K] (Fin m → K) :=
        { toFun := fun f j => f ⟨j, Finset.mem_univ j⟩
          invFun := fun f j => f j.val
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hmap : (rowSp G Finset.univ Finset.univ).map eCol.toLinearMap =
          Submodule.span K (Set.range (fun i : Fin n => G i)) := by
        dsimp only [rowSp]
        rw [Submodule.map_span]
        congr 1
        ext f
        simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨x.val, rfl⟩
        · rintro ⟨x, rfl⟩; exact ⟨⟨x, Finset.mem_univ x⟩, rfl⟩
      rw [← hmap]
      exact (eCol.submoduleMap (rowSp G Finset.univ Finset.univ)).finrank_eq
    have hbase_le : base ≤ r := by
      have h1 : base = Module.finrank K ↥(rowSp G R Finset.univ) :=
        hsub_eq R Finset.univ (fun x hx y _ => hGT x y (Or.inl (Finset.mem_filter.mp hx).2))
      rw [h1]
      have h2 : Module.finrank K ↥(rowSp G R Finset.univ) ≤
          Module.finrank K ↥(rowSp G Finset.univ Finset.univ) :=
        Submodule.finrank_mono (rowSpan_mono G (Finset.subset_univ R) Finset.univ)
      omega
    refine ⟨hbase_le, fun i v hv => ?_⟩
    change base + rk (rows i) (cols i) + rk (star v) (group v) ≤
      r + rk R (cols i) + rk (rows i) (group v)
    have hR_le_rows : R ⊆ rows i := Finset.subset_union_left
    have hrows_le_star : rows i ⊆ star v := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxR | hxi
      · exact Finset.mem_union_left _ hxR
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, (Finset.mem_filter.mp hxi).2, hv⟩)
    let resCols : (↥(Finset.univ : Finset (Fin m)) → K) →ₗ[K] (↥(cols i) → K) :=
      { toFun := fun f y => f ⟨y.val, Finset.mem_univ _⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let resGroup : (↥(Finset.univ : Finset (Fin m)) → K) →ₗ[K] (↥(group v) → K) :=
      { toFun := fun f y => f ⟨y.val, Finset.mem_univ _⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have h1 := finrank_map_sub_le resCols (rowSpan_mono G hR_le_rows Finset.univ)
    have h2 := finrank_map_sub_le resGroup (rowSpan_mono G hrows_le_star Finset.univ)
    have hm1 : (rowSp G (rows i) Finset.univ).map resCols = rowSp G (rows i) (cols i) :=
      rowSpan_submatrix_map G (rows i) (Finset.subset_univ (cols i))
    have hm2 : (rowSp G R Finset.univ).map resCols = rowSp G R (cols i) :=
      rowSpan_submatrix_map G R (Finset.subset_univ (cols i))
    have hm3 : (rowSp G (star v) Finset.univ).map resGroup = rowSp G (star v) (group v) :=
      rowSpan_submatrix_map G (star v) (Finset.subset_univ (group v))
    have hm4 : (rowSp G (rows i) Finset.univ).map resGroup = rowSp G (rows i) (group v) :=
      rowSpan_submatrix_map G (rows i) (Finset.subset_univ (group v))
    rw [hm1, hm2] at h1
    rw [hm3, hm4] at h2
    change Module.finrank K ↥(rowSp G (rows i) (cols i)) + Module.finrank K ↥(rowSp G R Finset.univ) ≤
      Module.finrank K ↥(rowSp G R (cols i)) + Module.finrank K ↥(rowSp G (rows i) Finset.univ) at h1
    change Module.finrank K ↥(rowSp G (star v) (group v)) + Module.finrank K ↥(rowSp G (rows i) Finset.univ) ≤
      Module.finrank K ↥(rowSp G (rows i) (group v)) + Module.finrank K ↥(rowSp G (star v) Finset.univ) at h2
    have hstar_le : Module.finrank K ↥(rowSp G (star v) Finset.univ) ≤ r := by
      have ha : Module.finrank K ↥(rowSp G (star v) Finset.univ) ≤
          Module.finrank K ↥(rowSp G Finset.univ Finset.univ) :=
        Submodule.finrank_mono (rowSpan_mono G (Finset.subset_univ _) Finset.univ)
      omega
    have heq_base : base = Module.finrank K ↥(rowSp G R Finset.univ) :=
      hsub_eq R Finset.univ (fun x hx y _ => hGT x y (Or.inl (Finset.mem_filter.mp hx).2))
    have heq_Rc : rk R (cols i) = Module.finrank K ↥(rowSp G R (cols i)) :=
      hsub_eq R (cols i) (fun x hx y _ => hGT x y (Or.inl (Finset.mem_filter.mp hx).2))
    have heq_rc : rk (rows i) (cols i) = Module.finrank K ↥(rowSp G (rows i) (cols i)) :=
      hsub_eq (rows i) (cols i) (fun x hx y hy => by
        rcases Finset.mem_union.mp hx with hxR | hxi
        · exact hGT x y (Or.inl (Finset.mem_filter.mp hxR).2)
        · exact hGT x y (Or.inr ⟨i, (Finset.mem_filter.mp hxi).2, (Finset.mem_filter.mp hy).2⟩))
    have heq_rg : rk (rows i) (group v) = Module.finrank K ↥(rowSp G (rows i) (group v)) :=
      hsub_eq (rows i) (group v) (fun x hx y hy => by
        rcases Finset.mem_union.mp hx with hxR | hxi
        · exact hGT x y (Or.inl (Finset.mem_filter.mp hxR).2)
        · exact hGT x y (Or.inr ⟨i, (Finset.mem_filter.mp hxi).2, (Finset.mem_filter.mp hy).2 ▸ hv⟩))
    have heq_sg : rk (star v) (group v) = Module.finrank K ↥(rowSp G (star v) (group v)) :=
      hsub_eq (star v) (group v) (fun x hx y hy => by
        rcases Finset.mem_union.mp hx with hxR | hxs
        · exact hGT x y (Or.inl (Finset.mem_filter.mp hxR).2)
        · rcases (Finset.mem_filter.mp hxs).2 with ⟨j, hxj, hvj⟩
          exact hGT x y (Or.inr ⟨j, hxj, (Finset.mem_filter.mp hy).2 ▸ hvj⟩))
    omega
  · rintro ⟨hbase_le, hcond⟩
    change base ≤ r at hbase_le
    change ∀ (i : Fin a) (v : Fin b), v ∈ bags i →
      base + rk (rows i) (cols i) + rk (star v) (group v) ≤
        r + rk R (cols i) + rk (rows i) (group v) at hcond
    let V := Fin r → K
    have hfinV : Module.finrank K V = r := Module.finrank_fin_fun K
    let SR : Submodule K (↥(Finset.univ : Finset (Fin m)) → K) := rowSp T R Finset.univ
    have hSR_dim : Module.finrank K ↥SR = base := (hrk_eq R Finset.univ).symm
    let VR : Submodule K V :=
      Submodule.span K (Set.range (fun k : Fin base => Pi.single (⟨k.val, lt_of_lt_of_le k.isLt hbase_le⟩ : Fin r) (1 : K)))
    have hVR_li : LinearIndependent K (fun k : Fin base =>
        (Pi.single (⟨k.val, lt_of_lt_of_le k.isLt hbase_le⟩ : Fin r) (1 : K) : V)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have hk := congrFun hc ⟨k.val, lt_of_lt_of_le k.isLt hbase_le⟩
      rw [Finset.sum_apply, Finset.sum_eq_single k] at hk
      · simpa using hk
      · intro j _ hne
        have hne' : (⟨j.val, lt_of_lt_of_le j.isLt hbase_le⟩ : Fin r) ≠ ⟨k.val, lt_of_lt_of_le k.isLt hbase_le⟩ :=
          fun h => hne (Fin.ext (by simpa using congrArg Fin.val h))
        simp [Pi.single_eq_of_ne (Ne.symm hne')]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    have hVR_dim : Module.finrank K ↥VR = base := by
      dsimp only [VR]
      rw [finrank_span_eq_card hVR_li, Fintype.card_fin]
    let eR : ↥VR ≃ₗ[K] ↥SR := LinearEquiv.ofFinrankEq ↥VR ↥SR (hVR_dim.trans hSR_dim.symm)
    let φR_all : ↥VR →ₗ[K] (↥(Finset.univ : Finset (Fin m)) → K) := SR.subtype.comp eR.toLinearMap
    have hφR_all_range : LinearMap.range φR_all = SR := by
      ext f
      simp only [LinearMap.mem_range, φR_all, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨z, rfl⟩; exact (eR z).2
      · intro hf; exact ⟨eR.symm ⟨f, hf⟩, by simp⟩
    have huR_ex : ∀ x : ↥R, ∃ z : ↥VR, φR_all z = fun y : ↥(Finset.univ : Finset (Fin m)) => T x.val y.val := by
      intro x
      have hmem : (fun y : ↥(Finset.univ : Finset (Fin m)) => T x.val y.val) ∈ LinearMap.range φR_all := by
        rw [hφR_all_range]
        exact Submodule.subset_span ⟨x, rfl⟩
      exact LinearMap.mem_range.mp hmem
    choose uR huR using huR_ex
    let wR : Fin m → (↥VR →ₗ[K] K) := fun y =>
      (LinearMap.proj (⟨y, Finset.mem_univ y⟩ : ↥(Finset.univ : Finset (Fin m)))).comp φR_all
    let Seen : ℕ → Finset (Fin b) := fun k =>
      (Finset.univ.filter (fun j : Fin a => j.val < k)).biUnion bags
    have hind : ∀ k : ℕ, k ≤ a →
        ∃ (u : Fin n → V) (w : Fin m → (V →ₗ[K] K)),
          (∀ x (hx : x ∈ R), u x = (uR ⟨x, hx⟩).1) ∧
          (∀ y, col y ∈ Seen k → ∀ z : ↥VR, w y z.1 = wR y z) ∧
          (∀ j : Fin a, j.val < k → ∀ x, row x = some j → ∀ y, col y ∈ bags j → w y (u x) = T x y) ∧
          (∀ v ∈ Seen k,
            LinearMap.range
              ({ toFun := fun z (y : ↥(group v)) => w y.val z
                 map_add' := fun z1 z2 => by funext y; exact map_add (w y.val) z1 z2
                 map_smul' := fun c z => by funext y; exact map_smul (w y.val) c z } : V →ₗ[K] (↥(group v) → K)) =
              rowSp T (star v) (group v)) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨fun x => if hx : x ∈ R then (uR ⟨x, hx⟩).1 else 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
        · intro x hx; simp [hx]
        · intro y hy
          simp only [Seen, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rcases hy with ⟨j, hj, _⟩; omega
        · intro j hj; omega
        · intro v hv
          simp only [Seen, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases hv with ⟨j, hj, _⟩; omega
      | succ k ih =>
        intro hk
        obtain ⟨u0, w0, hu0R, hw0R, hw0_ok, hw0_range⟩ := ih (Nat.le_of_lt hk)
        let i : Fin a := ⟨k, hk⟩
        have hSeen_succ : Seen (k + 1) = Seen k ∪ bags i := by
          ext v
          simp only [Seen, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, hv⟩
            by_cases hjk : j.val < k
            · exact Or.inl ⟨j, hjk, hv⟩
            · have hji : j = i := Fin.ext (by dsimp only [i]; omega)
              exact Or.inr (hji ▸ hv)
          · rintro (⟨j, hj, hv⟩ | hv)
            · exact ⟨j, by omega, hv⟩
            · exact ⟨i, Nat.lt_succ_self k, hv⟩
        by_cases hBempty : bags i = ∅
        · refine ⟨u0, w0, hu0R, ?_, ?_, ?_⟩
          · intro y hy; rw [hSeen_succ, hBempty, Finset.union_empty] at hy; exact hw0R y hy
          · intro j hj x hxj y hy
            by_cases hjk : j.val < k
            · exact hw0_ok j hjk x hxj y hy
            · have hji : j = i := Fin.ext (by dsimp only [i]; omega)
              rw [hji, hBempty] at hy; exact absurd hy (Finset.notMem_empty _)
          · intro v hv; rw [hSeen_succ, hBempty, Finset.union_empty] at hv; exact hw0_range v hv
        · have hBne : (bags i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hBempty
          have hover_card : (bags i ∩ Seen k).card ≤ 1 := by
            have h1 := hforest i
            have hfilt : Finset.univ.filter (fun j : Fin a => j < i) =
                Finset.univ.filter (fun j : Fin a => j.val < k) := by
              ext j; simp [Fin.lt_def, i]
            simpa only [Seen, hfilt] using h1
          have hv_ex : ∃ v ∈ bags i, bags i ∩ Seen k ⊆ {v} := by
            by_cases hov : (bags i ∩ Seen k).Nonempty
            · have hle1 := Finset.card_le_one.mp hover_card
              rcases hov with ⟨v, hv⟩
              refine ⟨v, (Finset.mem_inter.mp hv).1, fun u hu => ?_⟩
              rw [Finset.mem_singleton]
              exact hle1 u hu v hv
            · rw [Finset.not_nonempty_iff_eq_empty] at hov
              rcases hBne with ⟨v, hv⟩
              exact ⟨v, hv, by rw [hov]; exact Finset.empty_subset _⟩
          rcases hv_ex with ⟨v0, hv0_in, hover_sub⟩
          have hv0_phi_ex : ∃ Φ0 : V →ₗ[K] (↥(group v0) → K),
              (∀ y : ↥(group v0), ∀ z : ↥VR, Φ0 z.1 y = wR y.val z) ∧
              LinearMap.range Φ0 = rowSp T (star v0) (group v0) ∧
              (v0 ∈ Seen k → ∀ y : ↥(group v0), ∀ z : V, Φ0 z y = w0 y.val z) := by
            by_cases hv0_seen : v0 ∈ Seen k
            · refine ⟨{ toFun := fun z (y : ↥(group v0)) => w0 y.val z
                        map_add' := fun z1 z2 => by funext y; exact map_add (w0 y.val) z1 z2
                        map_smul' := fun c z => by funext y; exact map_smul (w0 y.val) c z },
                ?_, hw0_range v0 hv0_seen, fun _ _ _ => rfl⟩
              intro y z
              exact hw0R y.val (by rw [(Finset.mem_filter.mp y.2).2]; exact hv0_seen) z
            · let resG0 : (↥(Finset.univ : Finset (Fin m)) → K) →ₗ[K] (↥(group v0) → K) :=
                { toFun := fun f y => f ⟨y.val, Finset.mem_univ _⟩
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              let f0 : ↥VR →ₗ[K] (↥(group v0) → K) := resG0.comp φR_all
              have hf0_range : LinearMap.range f0 = rowSp T R (group v0) := by
                have h1 : LinearMap.range f0 = (LinearMap.range φR_all).map resG0 :=
                  LinearMap.range_comp φR_all resG0
                rw [h1, hφR_all_range]
                exact rowSpan_submatrix_map T R (Finset.subset_univ (group v0))
              have hf0_le : LinearMap.range f0 ≤ rowSp T (star v0) (group v0) := by
                rw [hf0_range]; exact rowSpan_mono T Finset.subset_union_left (group v0)
              have hdim0 : Module.finrank K ↥(rowSp T (star v0) (group v0)) -
                  Module.finrank K ↥(LinearMap.range f0) ≤
                  Module.finrank K V - Module.finrank K ↥VR := by
                rw [hf0_range, hfinV, hVR_dim, ← hrk_eq, ← hrk_eq]
                have hc := hcond i v0 hv0_in
                have hsubGv : group v0 ⊆ cols i := fun y hy =>
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(Finset.mem_filter.mp hy).2]; exact hv0_in⟩
                let resGv : (↥(cols i) → K) →ₗ[K] (↥(group v0) → K) :=
                  { toFun := fun f y => f ⟨y.val, hsubGv y.2⟩
                    map_add' := fun _ _ => rfl
                    map_smul' := fun _ _ => rfl }
                have hmono := finrank_map_sub_le resGv (rowSpan_mono T (Finset.subset_union_left : R ⊆ rows i) (cols i))
                have hm1 : (rowSp T (rows i) (cols i)).map resGv = rowSp T (rows i) (group v0) :=
                  rowSpan_submatrix_map T (rows i) hsubGv
                have hm2 : (rowSp T R (cols i)).map resGv = rowSp T R (group v0) :=
                  rowSpan_submatrix_map T R hsubGv
                rw [hm1, hm2, ← hrk_eq, ← hrk_eq, ← hrk_eq, ← hrk_eq] at hmono
                change rk (rows i) (group v0) + rk R (cols i) ≤ rk R (group v0) + rk (rows i) (cols i) at hmono
                omega
              obtain ⟨Φ0, hΦ0_VR, hΦ0_range⟩ := exists_surj_extension VR f0 (rowSp T (star v0) (group v0)) hf0_le hdim0
              refine ⟨Φ0, ?_, hΦ0_range, fun h => absurd h hv0_seen⟩
              intro y z
              have h1 := congrFun (hΦ0_VR z) y
              exact h1
          rcases hv0_phi_ex with ⟨Φ0, hΦ0_VR, hΦ0_range, hΦ0_old⟩
          have hsubGv0 : group v0 ⊆ cols i := fun y hy =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(Finset.mem_filter.mp hy).2]; exact hv0_in⟩
          let π0 : (↥(cols i) → K) →ₗ[K] (↥(group v0) → K) :=
            { toFun := fun f y => f ⟨y.val, hsubGv0 y.2⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          let resCi : (↥(Finset.univ : Finset (Fin m)) → K) →ₗ[K] (↥(cols i) → K) :=
            { toFun := fun f y => f ⟨y.val, Finset.mem_univ _⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          let φRi : ↥VR →ₗ[K] (↥(cols i) → K) := resCi.comp φR_all
          have hφRi_range : LinearMap.range φRi = rowSp T R (cols i) := by
            rw [LinearMap.range_comp, hφR_all_range]
            exact rowSpan_submatrix_map T R (Finset.subset_univ (cols i))
          have hPi_map0 : (rowSp T (rows i) (cols i)).map π0 = rowSp T (rows i) (group v0) :=
            rowSpan_submatrix_map T (rows i) hsubGv0
          have hPi_sub0 : (rowSp T (rows i) (cols i)).map π0 ≤ LinearMap.range Φ0 := by
            rw [hPi_map0, hΦ0_range]
            refine rowSpan_mono T ?_ (group v0)
            intro x hx
            rcases Finset.mem_union.mp hx with hxR | hxi
            · exact Finset.mem_union_left _ hxR
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, (Finset.mem_filter.mp hxi).2, hv0_in⟩)
          have hineq0 : Module.finrank K ↥VR + Module.finrank K ↥(rowSp T (rows i) (cols i)) +
              Module.finrank K ↥(LinearMap.range Φ0) ≤
              Module.finrank K V + Module.finrank K ↥(rowSp T R (cols i)) +
              Module.finrank K ↥((rowSp T (rows i) (cols i)).map π0) := by
            rw [hVR_dim, hfinV, hΦ0_range, hPi_map0, ← hrk_eq, ← hrk_eq, ← hrk_eq, ← hrk_eq]
            exact hcond i v0 hv0_in
          obtain ⟨Ui, hVR_Ui, ψ, hUi_dim, hψ_VR, hψ_compat, hψ_range⟩ :=
            exists_bag_lift π0 VR (rowSp T (rows i) (cols i)) (rowSp T R (cols i))
              (rowSpan_mono T Finset.subset_union_left (cols i)) φRi hφRi_range Φ0
              (fun z => by funext y; exact hΦ0_VR y z) hPi_sub0 hineq0
          have hPhi_new_ex : ∀ (v : Fin b) (hv : v ∈ bags i), v ≠ v0 →
              ∃ Φv : V →ₗ[K] (↥(group v) → K),
                (∀ z : ↥Ui, ∀ y : ↥(group v), Φv z.1 y = ψ z ⟨y.val,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(Finset.mem_filter.mp y.2).2]; exact hv⟩⟩) ∧
                LinearMap.range Φv = rowSp T (star v) (group v) := by
            intro v hv hvne
            have hsubGv : group v ⊆ cols i := fun y hy =>
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(Finset.mem_filter.mp hy).2]; exact hv⟩
            let πv : (↥(cols i) → K) →ₗ[K] (↥(group v) → K) :=
              { toFun := fun f y => f ⟨y.val, hsubGv y.2⟩
                map_add' := fun _ _ => rfl
                map_smul' := fun _ _ => rfl }
            let fv : ↥Ui →ₗ[K] (↥(group v) → K) := πv.comp ψ
            have hfv_range : LinearMap.range fv = rowSp T (rows i) (group v) := by
              rw [LinearMap.range_comp, hψ_range]
              exact rowSpan_submatrix_map T (rows i) hsubGv
            have hfv_le : LinearMap.range fv ≤ rowSp T (star v) (group v) := by
              rw [hfv_range]
              refine rowSpan_mono T ?_ (group v)
              intro x hx
              rcases Finset.mem_union.mp hx with hxR | hxi
              · exact Finset.mem_union_left _ hxR
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, (Finset.mem_filter.mp hxi).2, hv⟩)
            have hdimv : Module.finrank K ↥(rowSp T (star v) (group v)) -
                Module.finrank K ↥(LinearMap.range fv) ≤
                Module.finrank K V - Module.finrank K ↥Ui := by
              rw [hfv_range, hfinV, ← hrk_eq, ← hrk_eq]
              have h1 := hUi_dim
              rw [hVR_dim, ← hrk_eq, ← hrk_eq] at h1
              have hc := hcond i v hv
              omega
            obtain ⟨Φv, hΦv_Ui, hΦv_range⟩ := exists_surj_extension Ui fv (rowSp T (star v) (group v)) hfv_le hdimv
            exact ⟨Φv, fun z y => congrFun (hΦv_Ui z) y, hΦv_range⟩
          have hui_ex : ∀ x : Fin n, row x = some i →
              ∃ z : ↥Ui, ψ z = fun y : ↥(cols i) => T x y.val := by
            intro x hxi
            have hx_mem : x ∈ rows i := Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩)
            have hmem : (fun y : ↥(cols i) => T x y.val) ∈ LinearMap.range ψ := by
              rw [hψ_range]
              exact Submodule.subset_span ⟨⟨x, hx_mem⟩, rfl⟩
            exact LinearMap.mem_range.mp hmem
          let Φnew : (v : Fin b) → v ∈ bags i → v ≠ v0 → (V →ₗ[K] (↥(group v) → K)) :=
            fun v hv hvne => (hPhi_new_ex v hv hvne).choose
          have hΦnew_Ui : ∀ v hv hvne (z : ↥Ui) (y : ↥(group v)),
              Φnew v hv hvne z.1 y = ψ z ⟨y.val,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(Finset.mem_filter.mp y.2).2]; exact hv⟩⟩ :=
            fun v hv hvne => (hPhi_new_ex v hv hvne).choose_spec.1
          have hΦnew_range : ∀ v hv hvne,
              LinearMap.range (Φnew v hv hvne) = rowSp T (star v) (group v) :=
            fun v hv hvne => (hPhi_new_ex v hv hvne).choose_spec.2
          let u1 : Fin n → V := fun x =>
            if hxi : row x = some i then (hui_ex x hxi).choose.1 else u0 x
          let w1 : Fin m → (V →ₗ[K] K) := fun y =>
            if hv : col y ∈ bags i then
              if hveq : col y = v0 then
                (LinearMap.proj (⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hveq⟩⟩ : ↥(group v0))).comp Φ0
              else
                (LinearMap.proj (⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩ : ↥(group (col y)))).comp
                  (Φnew (col y) hv hveq)
            else w0 y
          have hw1_old : ∀ y, col y ∈ Seen k → w1 y = w0 y := by
            intro y hyS
            dsimp only [w1]
            by_cases hv : col y ∈ bags i
            · simp only [hv, ↓reduceDIte]
              have hmem_ov : col y ∈ bags i ∩ Seen k := Finset.mem_inter.mpr ⟨hv, hyS⟩
              have hveq : col y = v0 := Finset.mem_singleton.mp (hover_sub hmem_ov)
              simp only [hveq, ↓reduceDIte]
              apply LinearMap.ext; intro z
              exact hΦ0_old (by rw [← hveq]; exact hyS) ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hveq⟩⟩ z
            · simp only [hv, ↓reduceDIte]
          refine ⟨u1, w1, ?_, ?_, ?_, ?_⟩
          · intro x hx
            have hxnone : row x = none := (Finset.mem_filter.mp hx).2
            have hne : row x ≠ some i := by rw [hxnone]; simp
            simp only [u1, hne, ↓reduceDIte]
            exact hu0R x hx
          · intro y hy z
            rw [hSeen_succ] at hy
            rcases Finset.mem_union.mp hy with hyS | hyB
            · rw [hw1_old y hyS]; exact hw0R y hyS z
            · dsimp only [w1]
              simp only [hyB, ↓reduceDIte]
              by_cases hveq : col y = v0
              · simp only [hveq, ↓reduceDIte, LinearMap.comp_apply, LinearMap.proj_apply]
                exact hΦ0_VR ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hveq⟩⟩ z
              · simp only [hveq, ↓reduceDIte, LinearMap.comp_apply, LinearMap.proj_apply]
                rw [hΦnew_Ui (col y) hyB hveq ⟨z.1, hVR_Ui z.2⟩
                  ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩, hψ_VR z]
                rfl
          · intro j hj x hxj y hy
            by_cases hjk : j.val < k
            · have hji : j ≠ i := fun h => by rw [h] at hjk; exact Nat.lt_irrefl k hjk
              have hne : row x ≠ some i := by rw [hxj]; intro h; exact hji (Option.some.inj h)
              have hyS : col y ∈ Seen k := by
                simp only [Seen, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨j, hjk, hy⟩
              simp only [u1, hne, ↓reduceDIte]
              rw [hw1_old y hyS]
              exact hw0_ok j hjk x hxj y hy
            · have hji : j = i := Fin.ext (by dsimp only [i]; omega)
              have hxi : row x = some i := by rw [← hji]; exact hxj
              have hyi : col y ∈ bags i := by rw [← hji]; exact hy
              simp only [u1, hxi, ↓reduceDIte]
              let zx : ↥Ui := (hui_ex x hxi).choose
              have hzx : ψ zx = fun y' : ↥(cols i) => T x y'.val := (hui_ex x hxi).choose_spec
              dsimp only [w1]
              simp only [hyi, ↓reduceDIte]
              by_cases hveq : col y = v0
              · simp only [hveq, ↓reduceDIte, LinearMap.comp_apply, LinearMap.proj_apply]
                have hc := congrFun (hψ_compat zx) ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hveq⟩⟩
                rw [← hc]
                exact congrFun hzx ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyi⟩⟩
              · simp only [hveq, ↓reduceDIte, LinearMap.comp_apply, LinearMap.proj_apply]
                rw [hΦnew_Ui (col y) hyi hveq zx ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩]
                exact congrFun hzx ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyi⟩⟩
          · intro v hv
            rw [hSeen_succ] at hv
            rcases Finset.mem_union.mp hv with hvS | hvB
            · have heq : ({ toFun := fun z (y : ↥(group v)) => w1 y.val z
                            map_add' := fun z1 z2 => by funext y; exact map_add (w1 y.val) z1 z2
                            map_smul' := fun c z => by funext y; exact map_smul (w1 y.val) c z } : V →ₗ[K] (↥(group v) → K)) =
                  { toFun := fun z (y : ↥(group v)) => w0 y.val z
                    map_add' := fun z1 z2 => by funext y; exact map_add (w0 y.val) z1 z2
                    map_smul' := fun c z => by funext y; exact map_smul (w0 y.val) c z } := by
                apply LinearMap.ext; intro z; funext y
                have hyS : col y.val ∈ Seen k := by rw [(Finset.mem_filter.mp y.2).2]; exact hvS
                exact congrFun (congrArg DFunLike.coe (hw1_old y.val hyS)) z
              rw [heq]
              exact hw0_range v hvS
            · by_cases hveq : v = v0
              · subst hveq
                have heq : ({ toFun := fun z (y : ↥(group v)) => w1 y.val z
                              map_add' := fun z1 z2 => by funext y; exact map_add (w1 y.val) z1 z2
                              map_smul' := fun c z => by funext y; exact map_smul (w1 y.val) c z } : V →ₗ[K] (↥(group v) → K)) = Φ0 := by
                  apply LinearMap.ext; intro z; funext y
                  have hyc : col y.val = v := (Finset.mem_filter.mp y.2).2
                  have hyt : col y.val ∈ bags i := by rw [hyc]; exact hvB
                  change w1 y.val z = Φ0 z y
                  dsimp only [w1]
                  simp only [hyc, hvB, ↓reduceDIte, LinearMap.comp_apply, LinearMap.proj_apply]
                rw [heq, hΦ0_range]
              · have heq : ({ toFun := fun z (y : ↥(group v)) => w1 y.val z
                              map_add' := fun z1 z2 => by funext y; exact map_add (w1 y.val) z1 z2
                              map_smul' := fun c z => by funext y; exact map_smul (w1 y.val) c z } : V →ₗ[K] (↥(group v) → K)) =
                    Φnew v hvB hveq := by
                  apply LinearMap.ext; intro z; funext y
                  have hyc : col y.val = v := (Finset.mem_filter.mp y.2).2
                  have hyt : col y.val ∈ bags i := by rw [hyc]; exact hvB
                  have hyne : col y.val ≠ v0 := by rw [hyc]; exact hveq
                  change w1 y.val z = Φnew v hvB hveq z y
                  dsimp only [w1]
                  simp only [hyt, hyne, ↓reduceDIte, LinearMap.comp_apply, LinearMap.proj_apply]
                  have hcongr : ∀ (u : Fin b) (hu : u = v) (hut : u ∈ bags i) (hune : u ≠ v0)
                      (y' : ↥(group u)), y'.val = y.val →
                      Φnew u hut hune z y' = Φnew v hvB hveq z y := by
                    rintro u rfl hut hune y' hy'
                    exact congrArg (Φnew u hvB hveq z) (Subtype.ext hy')
                  exact hcongr (col y.val) hyc hyt hyne ⟨y.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩ rfl
                rw [heq, hΦnew_range v hvB hveq]
    obtain ⟨u, wA, huR_ok, hwA_R, hwA_ok, _⟩ := hind a (le_refl a)
    obtain ⟨CR, hCR⟩ := Submodule.exists_isCompl VR
    let pVR : V →ₗ[K] ↥VR := Submodule.projectionOnto VR CR hCR
    let w : Fin m → (V →ₗ[K] K) := fun y =>
      if col y ∈ Seen a then wA y else (wR y).comp pVR
    let G : Matrix (Fin n) (Fin m) K := fun x y => w y (u x)
    refine ⟨G, rank_factor_le u w, ?_⟩
    intro x y hobs
    dsimp only [G]
    rcases hobs with hxnone | ⟨i, hxi, hybi⟩
    · have hxR : x ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxnone⟩
      rw [huR_ok x hxR]
      have hwy : w y (uR ⟨x, hxR⟩).1 = wR y (uR ⟨x, hxR⟩) := by
        dsimp only [w]
        by_cases hyS : col y ∈ Seen a
        · simp only [hyS, ↓reduceIte]; exact hwA_R y hyS (uR ⟨x, hxR⟩)
        · simp only [hyS, ↓reduceIte, LinearMap.comp_apply]
          rw [Submodule.projectionOnto_apply_left hCR]
      rw [hwy]
      dsimp only [wR, LinearMap.comp_apply, LinearMap.proj_apply]
      exact congrFun (huR ⟨x, hxR⟩) ⟨y, Finset.mem_univ y⟩
    · have hyS : col y ∈ Seen a := by
        simp only [Seen, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, i.isLt, hybi⟩
      dsimp only [w]
      simp only [hyS, ↓reduceIte]
      exact hwA_ok i i.isLt x hxi y hybi
