import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_727_aux

private abbrev K := ZMod 2
private abbrev V (k : ℕ) := Fin k → K

private lemma zmod2_add_self (x : K) : x + x = 0 := by
  revert x; decide

private lemma zmod2_vec_add_self {k : ℕ} (x : V k) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

private lemma zmod2_mat_add_self {k : ℕ} (M : Matrix (Fin k) (Fin k) K) : M + M = 0 := by
  ext i j
  exact zmod2_add_self (M i j)

private lemma zmod2_eq_zero_or_one (x : K) : x = 0 ∨ x = 1 := by
  revert x; decide

private lemma finrank_sup_le {k : ℕ} (U W : Submodule K (V k)) :
    Module.finrank K ↥(U ⊔ W) ≤ Module.finrank K ↥U + Module.finrank K ↥W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

private lemma mat_add_mulVecLin {k : ℕ} (X Y : Matrix (Fin k) (Fin k) K) (v : V k) :
    (X + Y).mulVecLin v = X.mulVecLin v + Y.mulVecLin v :=
  Matrix.add_mulVec X Y v

private lemma rank_add_le {k : ℕ} (X Y : Matrix (Fin k) (Fin k) K) :
    (X + Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  have hsub : LinearMap.range (X + Y).mulVecLin ≤
      LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [mat_add_mulVecLin]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact le_trans (Submodule.finrank_mono hsub) (finrank_sup_le _ _)

private lemma card_filter_submodule {k : ℕ} (W : Submodule K (V k)) [DecidablePred (· ∈ W)] :
    ((Finset.univ : Finset (V k)).filter (fun v => v ∈ W)).card = 2 ^ Module.finrank K ↥W := by
  have : Module.Free K ↥W := Module.Free.of_divisionRing K ↥W
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank K ↥W)) K ↥W) := ⟨Module.finBasis K ↥W⟩
  have hcard : Fintype.card ↥W = ((Finset.univ : Finset (V k)).filter (fun v => v ∈ W)).card :=
    Fintype.card_subtype _
  rw [← hcard, Fintype.card_congr b.equivFun.toEquiv, Fintype.card_pi]
  simp [ZMod.card]

private lemma finrank_map_equiv {k : ℕ} (e : V k ≃ₗ[K] V k) (U : Submodule K (V k)) :
    Module.finrank K ↥(U.map e.toLinearMap) = Module.finrank K ↥U := by
  have h := LinearMap.finrank_range_add_finrank_ker (e.toLinearMap.comp U.subtype)
  have hker0 : LinearMap.ker (e.toLinearMap.comp U.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact e.injective.comp Subtype.val_injective
  have hrange : LinearMap.range (e.toLinearMap.comp U.subtype) = U.map e.toLinearMap := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange, hker0, finrank_bot, add_zero] at h
  exact h

private lemma linearEquiv_of_rank_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) K) (hA : A.rank = k) :
    Nonempty (V k ≃ₗ[K] V k) ∧ Function.Bijective A.mulVecLin := by
  have hfin : Module.finrank K (V k) = k := by
    simp [V]
  have htop : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin]
    exact hA
  have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.1 htop
  have hinj : Function.Injective A.mulVecLin :=
    LinearMap.injective_iff_surjective.2 hsurj
  exact ⟨⟨LinearEquiv.ofBijective A.mulVecLin ⟨hinj, hsurj⟩⟩, ⟨hinj, hsurj⟩⟩

private lemma exists_disjoint_subspace {k : ℕ} (eT eIT : V k ≃ₗ[K] V k)
    (heIT : ∀ v : V k, eIT v = v + eT v) :
    ∀ m : ℕ, 2 * m ≤ k →
      ∃ U : Submodule K (V k),
        Module.finrank K ↥U = m ∧ U ⊓ U.map eT.toLinearMap = ⊥
  | 0, _ => by
      refine ⟨⊥, by simp, by simp⟩
  | m + 1, hm => by
      classical
      rcases exists_disjoint_subspace eT eIT heIT m (by omega) with ⟨U, hU_dim, hU_disj⟩
      let TU : Submodule K (V k) := U.map eT.toLinearMap
      let W : Submodule K (V k) := U ⊔ TU
      have hTU_dim : Module.finrank K ↥TU = m := by
        rw [finrank_map_equiv, hU_dim]
      have hW_dim : Module.finrank K ↥W = 2 * m := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq U TU
        rw [hU_disj, finrank_bot, add_zero, hU_dim, hTU_dim] at h
        show Module.finrank K ↥(U ⊔ TU) = 2 * m
        omega
      let Wfin : Finset (V k) := Finset.univ.filter (fun v => v ∈ W)
      have hWcard : Wfin.card = 2 ^ (2 * m) := by
        rw [card_filter_submodule W, hW_dim]
      let Bad1 : Finset (V k) := Wfin
      let Bad2 : Finset (V k) := Finset.univ.filter (fun v => eT v ∈ W)
      let Bad3 : Finset (V k) := Finset.univ.filter (fun v => eIT v ∈ W)
      have hBad2 : Bad2.card = 2 ^ (2 * m) := by
        rw [← hWcard]
        refine Finset.card_bij (fun v _ => eT v) ?_ ?_ ?_
        · intro v hv; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hv).2⟩
        · intro v1 _ v2 _ h; exact eT.injective h
        · intro w hw
          refine ⟨eT.symm w, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, eT.apply_symm_apply w⟩
          rw [eT.apply_symm_apply]
          exact (Finset.mem_filter.1 hw).2
      have hBad3 : Bad3.card = 2 ^ (2 * m) := by
        rw [← hWcard]
        refine Finset.card_bij (fun v _ => eIT v) ?_ ?_ ?_
        · intro v hv; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hv).2⟩
        · intro v1 _ v2 _ h; exact eIT.injective h
        · intro w hw
          refine ⟨eIT.symm w, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, eIT.apply_symm_apply w⟩
          rw [eIT.apply_symm_apply]
          exact (Finset.mem_filter.1 hw).2
      have hUnion_lt : (Bad1 ∪ Bad2 ∪ Bad3).card < (Finset.univ : Finset (V k)).card := by
        have h1 := Finset.card_union_le (Bad1 ∪ Bad2) Bad3
        have h2 := Finset.card_union_le Bad1 Bad2
        have huniv : (Finset.univ : Finset (V k)).card = 2 ^ k := by
          rw [Finset.card_univ, Fintype.card_pi]
          simp [ZMod.card]
        have hpow_le : 4 * 2 ^ (2 * m) ≤ 2 ^ k := by
          have : 4 * 2 ^ (2 * m) = 2 ^ (2 * m + 2) := by
            rw [pow_add]; ring
          rw [this]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        have hpos : 0 < 2 ^ (2 * m) := pow_pos (by decide) _
        rw [huniv]
        have : Bad1.card = 2 ^ (2 * m) := hWcard
        omega
      have hex_v : ∃ v : V k, v ∉ Bad1 ∪ Bad2 ∪ Bad3 := by
        by_contra hall
        push Not at hall
        have heq : Bad1 ∪ Bad2 ∪ Bad3 = Finset.univ := by
          ext v
          simp only [Finset.mem_univ, iff_true]
          exact hall v
        rw [heq] at hUnion_lt
        exact lt_irrefl _ hUnion_lt
      rcases hex_v with ⟨v, hv_not⟩
      have hv_nW : v ∉ W := fun h => hv_not
        (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨Finset.mem_univ v, h⟩)))
      have hTv_nW : eT v ∉ W := fun h => hv_not
        (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_univ v, h⟩)))
      have hITv_nW : v + eT v ∉ W := fun h => hv_not
        (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_univ v, by rw [heIT v]; exact h⟩))
      let U' : Submodule K (V k) := U ⊔ Submodule.span K {v}
      have hv_nU : v ∉ U := fun h => hv_nW (Submodule.mem_sup_left h)
      have hU'_dim : Module.finrank K ↥U' = m + 1 := by
        have hinf : U ⊓ Submodule.span K {v} = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          rcases hx with ⟨hxU, hxS⟩
          change x ∈ U at hxU
          change x ∈ Submodule.span K {v} at hxS
          rw [Submodule.mem_span_singleton] at hxS
          rcases hxS with ⟨a, rfl⟩
          rcases zmod2_eq_zero_or_one a with rfl | rfl
          · simp
          · rw [one_smul] at hxU
            exact absurd hxU hv_nU
        have hspan_dim : Module.finrank K ↥(Submodule.span K {v}) = 1 := by
          have hv0 : v ≠ 0 := fun h0 => hv_nU (h0 ▸ U.zero_mem)
          exact finrank_span_singleton hv0
        have h := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span K {v})
        rw [hinf, finrank_bot, add_zero, hU_dim, hspan_dim] at h
        exact h
      have hU'_disj : U' ⊓ U'.map eT.toLinearMap = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        rcases hx with ⟨hx1, hx2⟩
        rcases Submodule.mem_sup.1 hx1 with ⟨u1, hu1, s1, hs1, hxeq1⟩
        rw [Submodule.mem_span_singleton] at hs1
        rcases hs1 with ⟨a, rfl⟩
        rcases Submodule.mem_map.1 hx2 with ⟨y, hy, hyeq⟩
        rcases Submodule.mem_sup.1 hy with ⟨u2, hu2, s2, hs2, hyeq2⟩
        rw [Submodule.mem_span_singleton] at hs2
        rcases hs2 with ⟨b, rfl⟩
        have hx_eq : u1 + a • v = eT u2 + b • eT v := by
          rw [hxeq1, ← hyeq, ← hyeq2, map_add, map_smul]
          rfl
        have hcomb : a • v + b • eT v = u1 + eT u2 := by
          have h1 := congrArg (fun z : V k => z + u1 + b • eT v) hx_eq
          have hl : u1 + a • v + u1 + b • eT v = a • v + b • eT v := by
            calc
              u1 + a • v + u1 + b • eT v = (u1 + u1) + (a • v + b • eT v) := by abel
              _ = 0 + (a • v + b • eT v) := by rw [zmod2_vec_add_self]
              _ = a • v + b • eT v := zero_add _
          have hr : eT u2 + b • eT v + u1 + b • eT v = u1 + eT u2 := by
            calc
              eT u2 + b • eT v + u1 + b • eT v = (u1 + eT u2) + (b • eT v + b • eT v) := by abel
              _ = (u1 + eT u2) + 0 := by rw [zmod2_vec_add_self]
              _ = u1 + eT u2 := add_zero _
          rw [hl, hr] at h1
          exact h1
        have hWmem : a • v + b • eT v ∈ W := by
          rw [hcomb]
          exact Submodule.add_mem_sup hu1 ⟨u2, hu2, rfl⟩
        rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
          rcases zmod2_eq_zero_or_one b with rfl | rfl
        · simp only [zero_smul, add_zero] at hxeq1 hx_eq
          have hu1_in : u1 ∈ U ⊓ TU := ⟨hu1, by rw [hx_eq]; exact ⟨u2, hu2, rfl⟩⟩
          rw [hU_disj] at hu1_in
          rw [← hxeq1]
          exact hu1_in
        · simp only [zero_smul, one_smul, zero_add] at hWmem
          exact absurd hWmem hTv_nW
        · simp only [zero_smul, one_smul, add_zero] at hWmem
          exact absurd hWmem hv_nW
        · simp only [one_smul] at hWmem
          exact absurd hWmem hITv_nW
      exact ⟨U', hU'_dim, hU'_disj⟩

private lemma exists_witness_min_p {k p q r : ℕ} (A B : Matrix (Fin k) (Fin k) K)
    (hA : A.rank = k) (hB : B.rank = k) (hAB : (A + B).rank = k)
    (hpq : p ≤ q) (hpr : p ≤ r) (h1 : k ≤ p + q) (h2 : k ≤ p + r) :
    ∃ C : Matrix (Fin k) (Fin k) K,
      C.rank ≤ p ∧ (A + C).rank ≤ q ∧ (B + C).rank ≤ r := by
  have hbijA := (linearEquiv_of_rank_eq A hA).2
  have hbijB := (linearEquiv_of_rank_eq B hB).2
  have hbijAB := (linearEquiv_of_rank_eq (A + B) hAB).2
  let eA : V k ≃ₗ[K] V k := LinearEquiv.ofBijective A.mulVecLin hbijA
  let eB : V k ≃ₗ[K] V k := LinearEquiv.ofBijective B.mulVecLin hbijB
  let eAB : V k ≃ₗ[K] V k := LinearEquiv.ofBijective (A + B).mulVecLin hbijAB
  let eT : V k ≃ₗ[K] V k := eB.trans eA.symm
  let eIT : V k ≃ₗ[K] V k := eAB.trans eA.symm
  have heIT : ∀ v : V k, eIT v = v + eT v := by
    intro v
    apply eA.injective
    have h1' : eA (eIT v) = (A + B).mulVecLin v := by
      change eA (eA.symm (eAB v)) = _
      rw [eA.apply_symm_apply]
      rfl
    have h2' : eA (v + eT v) = A.mulVecLin v + B.mulVecLin v := by
      rw [map_add]
      have : eA (eT v) = B.mulVecLin v := by
        change eA (eA.symm (eB v)) = _
        rw [eA.apply_symm_apply]
        rfl
      rw [this]
      rfl
    rw [h1', h2', mat_add_mulVecLin]
  let d := min p (k / 2)
  have hd_le : 2 * d ≤ k := by omega
  rcases exists_disjoint_subspace eT eIT heIT d hd_le with ⟨U, hU_dim, hU_disj⟩
  let S1 : Submodule K (V k) := U.map eT.toLinearMap
  let S2 : Submodule K (V k) := U.map eIT.toLinearMap
  have hS1_dim : Module.finrank K ↥S1 = d := by
    rw [finrank_map_equiv, hU_dim]
  have hS12_disj : S1 ⊓ S2 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    rcases Submodule.mem_map.1 hx1 with ⟨u1, hu1, rfl⟩
    rcases Submodule.mem_map.1 hx2 with ⟨u2, hu2, hu2eq⟩
    have heq : eT u1 = u2 + eT u2 := by
      have : eIT u2 = eT u1 := hu2eq
      rw [← this, heIT]
    have hu2_eq : u2 = eT (u1 + u2) := by
      rw [map_add]
      have h' := congrArg (fun z : V k => z + eT u2) heq
      rw [add_assoc, zmod2_vec_add_self, add_zero] at h'
      exact h'.symm
    have hu2_in : u2 ∈ U ⊓ S1 := ⟨hu2, ⟨u1 + u2, U.add_mem hu1 hu2, hu2_eq.symm⟩⟩
    rw [hU_disj] at hu2_in
    have hu20 : u2 = 0 := hu2_in
    rw [← hu2eq, hu20, map_zero]
  rcases Submodule.exists_isCompl (S1 ⊔ S2) with ⟨R, hR⟩
  let Kker : Submodule K (V k) := S2 ⊔ R
  have hcompl : IsCompl S1 Kker := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro x hx
      rcases hx with ⟨hx1, hxK⟩
      rcases Submodule.mem_sup.1 hxK with ⟨s2, hs2, r0, hr0, hxeq⟩
      have hr0_in : r0 ∈ (S1 ⊔ S2) ⊓ R := by
        refine ⟨?_, hr0⟩
        have hr_eq : r0 = x + s2 := by
          have h' := congrArg (fun z : V k => z + s2) hxeq
          rw [add_comm s2 r0, add_assoc, zmod2_vec_add_self, add_zero] at h'
          exact h'
        rw [hr_eq]
        exact Submodule.add_mem_sup hx1 hs2
      rw [hR.inf_eq_bot] at hr0_in
      have hr00 : r0 = 0 := hr0_in
      rw [hr00, add_zero] at hxeq
      have hx12 : x ∈ S1 ⊓ S2 := ⟨hx1, hxeq ▸ hs2⟩
      rw [hS12_disj] at hx12
      exact hx12
    · rw [codisjoint_iff]
      change S1 ⊔ (S2 ⊔ R) = ⊤
      rw [← sup_assoc]
      exact hR.sup_eq_top
  let Dlin : V k →ₗ[K] V k := S1.subtype.comp (Submodule.projectionOnto S1 Kker hcompl)
  have hD_on_S1 : ∀ x ∈ S1, Dlin x = x := by
    intro x hx
    change (Submodule.projectionOnto S1 Kker hcompl x : V k) = x
    have := Submodule.projectionOnto_apply_left hcompl ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hD_on_S2 : ∀ x ∈ S2, Dlin x = 0 := by
    intro x hx
    change (Submodule.projectionOnto S1 Kker hcompl x : V k) = 0
    have hxK : x ∈ Kker := Submodule.mem_sup_left hx
    have := Submodule.projectionOnto_apply_right hcompl ⟨x, hxK⟩
    exact congrArg Subtype.val this
  let Clin : V k →ₗ[K] V k := eA.toLinearMap.comp Dlin
  let C : Matrix (Fin k) (Fin k) K := LinearMap.toMatrix' Clin
  have hC_lin : C.mulVecLin = Clin := Matrix.toLin'_toMatrix' Clin
  have hfin_V : Module.finrank K (V k) = k := by
    simp [V]
  have hrank_comp_eA : ∀ f : V k →ₗ[K] V k,
      Module.finrank K ↥(LinearMap.range (eA.toLinearMap.comp f)) =
        Module.finrank K ↥(LinearMap.range f) := by
    intro f
    rw [LinearMap.range_comp]
    exact finrank_map_equiv eA (LinearMap.range f)
  have hC_rank : C.rank ≤ p := by
    unfold Matrix.rank
    rw [hC_lin]
    change Module.finrank K ↥(LinearMap.range (eA.toLinearMap.comp Dlin)) ≤ p
    rw [hrank_comp_eA]
    have hsub : LinearMap.range Dlin ≤ S1 := by
      rintro _ ⟨v, rfl⟩
      exact (Submodule.projectionOnto S1 Kker hcompl v).2
    have hle := Submodule.finrank_mono hsub
    rw [hS1_dim] at hle
    omega
  have hAC_rank : (A + C).rank ≤ q := by
    unfold Matrix.rank
    have hlin : (A + C).mulVecLin = eA.toLinearMap.comp (LinearMap.id + Dlin) := by
      refine LinearMap.ext fun v => ?_
      rw [mat_add_mulVecLin, hC_lin]
      change eA v + eA (Dlin v) = eA (v + Dlin v)
      rw [map_add]
    rw [hlin, hrank_comp_eA]
    have hker_sub : S1 ≤ LinearMap.ker (LinearMap.id + Dlin) := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hD_on_S1 x hx]
      exact zmod2_vec_add_self x
    have hker_ge : d ≤ Module.finrank K ↥(LinearMap.ker (LinearMap.id + Dlin)) := by
      rw [← hS1_dim]
      exact Submodule.finrank_mono hker_sub
    have hrk := LinearMap.finrank_range_add_finrank_ker (LinearMap.id + Dlin)
    rw [hfin_V] at hrk
    omega
  have hBC_rank : (B + C).rank ≤ r := by
    unfold Matrix.rank
    have hlin : (B + C).mulVecLin = eA.toLinearMap.comp (eT.toLinearMap + Dlin) := by
      refine LinearMap.ext fun v => ?_
      rw [mat_add_mulVecLin, hC_lin]
      have hBeT : B.mulVecLin v = eA (eT v) := by
        change eB v = eA (eA.symm (eB v))
        rw [eA.apply_symm_apply]
      rw [hBeT]
      change eA (eT v) + eA (Dlin v) = eA (eT v + Dlin v)
      rw [map_add]
    rw [hlin, hrank_comp_eA]
    have hker_sub : U ≤ LinearMap.ker (eT.toLinearMap + Dlin) := by
      intro u hu
      rw [LinearMap.mem_ker, LinearMap.add_apply]
      have hIT_mem : u + eT u ∈ S2 := by
        rw [← heIT u]
        exact ⟨u, hu, rfl⟩
      have h0 : Dlin (u + eT u) = 0 := hD_on_S2 _ hIT_mem
      have hTu : Dlin (eT u) = eT u := hD_on_S1 _ ⟨u, hu, rfl⟩
      rw [map_add, hTu] at h0
      have hDu : Dlin u = eT u := by
        have h' := congrArg (fun z : V k => z + eT u) h0
        rw [add_assoc, zmod2_vec_add_self, add_zero, zero_add] at h'
        exact h'
      change eT u + Dlin u = 0
      rw [hDu]
      exact zmod2_vec_add_self _
    have hker_ge : d ≤ Module.finrank K ↥(LinearMap.ker (eT.toLinearMap + Dlin)) := by
      rw [← hU_dim]
      exact Submodule.finrank_mono hker_sub
    have hrk := LinearMap.finrank_range_add_finrank_ker (eT.toLinearMap + Dlin)
    rw [hfin_V] at hrk
    omega
  exact ⟨C, hC_rank, hAC_rank, hBC_rank⟩

end PEqualNP.Outside.L_lib_727_aux

theorem PEqualNP.Outside.L_lib_727 :
∀ (k p q r : ℕ) (A B : Matrix (Fin k) (Fin k) (ZMod 2)),
  A.rank = k → B.rank = k → (A+B).rank = k →
  ((∃ C : Matrix (Fin k) (Fin k) (ZMod 2),
    C.rank ≤ p ∧ (A+C).rank ≤ q ∧ (B+C).rank ≤ r) ↔
    (k ≤ p+q ∧ k ≤ p+r ∧ k ≤ q+r)) := by
  intro k p q r A B hA hB hAB
  constructor
  · rintro ⟨C, hCp, hACq, hBCr⟩
    have h1 : k ≤ p + q := by
      have heq : C + (A + C) = A := by
        calc
          C + (A + C) = A + (C + C) := by abel
          _ = A + 0 := by rw [PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self]
          _ = A := add_zero A
      have hle := PEqualNP.Outside.L_lib_727_aux.rank_add_le C (A + C)
      rw [heq, hA] at hle
      omega
    have h2 : k ≤ p + r := by
      have heq : C + (B + C) = B := by
        calc
          C + (B + C) = B + (C + C) := by abel
          _ = B + 0 := by rw [PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self]
          _ = B := add_zero B
      have hle := PEqualNP.Outside.L_lib_727_aux.rank_add_le C (B + C)
      rw [heq, hB] at hle
      omega
    have h3 : k ≤ q + r := by
      have heq : (A + C) + (B + C) = A + B := by
        calc
          (A + C) + (B + C) = (A + B) + (C + C) := by abel
          _ = (A + B) + 0 := by rw [PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self]
          _ = A + B := add_zero _
      have hle := PEqualNP.Outside.L_lib_727_aux.rank_add_le (A + C) (B + C)
      rw [heq, hAB] at hle
      omega
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hp : p ≤ q ∧ p ≤ r
    · exact PEqualNP.Outside.L_lib_727_aux.exists_witness_min_p A B hA hB hAB hp.1 hp.2 h1 h2
    · by_cases hq : q ≤ p ∧ q ≤ r
      · have hAAB : A + (A + B) = B := by
          rw [← add_assoc, PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self, zero_add]
        rcases PEqualNP.Outside.L_lib_727_aux.exists_witness_min_p A (A + B) hA hAB
          (by rw [hAAB]; exact hB) hq.1 hq.2 (by omega) h3 with ⟨C', hC'q, hAC'p, hABC'r⟩
        refine ⟨A + C', hAC'p, ?_, ?_⟩
        · rw [← add_assoc, PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self, zero_add]
          exact hC'q
        · have heq : B + (A + C') = (A + B) + C' := by abel
          rw [heq]
          exact hABC'r
      · have hr : r ≤ p ∧ r ≤ q := by omega
        have hBAB : B + (A + B) = A := by
          calc
            B + (A + B) = A + (B + B) := by abel
            _ = A + 0 := by rw [PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self]
            _ = A := add_zero A
        rcases PEqualNP.Outside.L_lib_727_aux.exists_witness_min_p B (A + B) hB hAB
          (by rw [hBAB]; exact hA) hr.1 hr.2 (by omega) (by omega) with ⟨C', hC'r, hBC'p, hABC'q⟩
        refine ⟨B + C', hBC'p, ?_, ?_⟩
        · have heq : A + (B + C') = (A + B) + C' := by abel
          rw [heq]
          exact hABC'q
        · rw [← add_assoc, PEqualNP.Outside.L_lib_727_aux.zmod2_mat_add_self, zero_add]
          exact hC'r
