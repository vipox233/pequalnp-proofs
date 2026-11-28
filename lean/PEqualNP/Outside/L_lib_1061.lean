import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1061_aux

open scoped BigOperators

abbrev F2 := ZMod 2

private def chi (x : F2) : ℤ := if x = 0 then 1 else -1

private lemma chi_zero : chi 0 = 1 := rfl

private lemma chi_one : chi 1 = -1 := by decide

private lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  revert x y; decide

private lemma sum_chi_powerset {m : ℕ} (v : Fin m → F2) :
    (∑ S : Finset (Fin m), chi (S.sum v)) = if ∀ i, v i = 0 then (2 : ℤ) ^ m else 0 := by
  classical
  have hprod : (∑ S : Finset (Fin m), chi (S.sum v)) =
      ∏ i : Fin m, (chi (v i) + 1) := by
    rw [Fintype.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [Finset.prod_const_one, mul_one]
    induction S using Finset.induction_on with
    | empty => simp [chi_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih (Finset.mem_univ s)]
  rw [hprod]
  by_cases hall : ∀ i, v i = 0
  · simp only [hall, chi_zero]
    norm_num
  · simp only [hall, ↓reduceIte]
    push Not at hall
    rcases hall with ⟨i0, hi0⟩
    have hv1 : v i0 = 1 := by revert hi0; generalize v i0 = x; revert x; decide
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    rw [hv1, chi_one]
    ring

private def orth {a : ℕ} (U : Submodule F2 (Fin a → F2)) : Submodule F2 (Fin a → F2) :=
  { carrier := {v | ∀ u ∈ U, dotProduct v u = 0},
    zero_mem' := fun u _ => by simp [dotProduct], add_mem' := fun {v w} hv hw u hu => by
      simp only [Set.mem_ofPred_eq] at hv hw ⊢
      rw [add_dotProduct, hv u hu, hw u hu, zero_add],
    smul_mem' := fun c {v} hv u hu => by
      simp only [Set.mem_ofPred_eq] at hv ⊢
      rw [smul_dotProduct, hv u hu, smul_zero] }

private lemma finrank_orth_add {a : ℕ} (U : Submodule F2 (Fin a → F2)) :
    Module.finrank F2 (orth U) + Module.finrank F2 U = a := by
  classical
  let d := Module.finrank F2 U
  let b : Module.Basis (Fin d) F2 U := Module.finBasis F2 U
  let ev : (Fin a → F2) →ₗ[F2] (Fin d → F2) :=
    { toFun := fun v j => dotProduct v (b j).1
      map_add' := fun v w => by funext j; exact add_dotProduct v w (b j).1
      map_smul' := fun c v => by funext j; exact smul_dotProduct c v (b j).1 }
  have hker : LinearMap.ker ev = orth U := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv u hu
      have hu_eq : ∑ j : Fin d, b.repr ⟨u, hu⟩ j • (b j).1 = u := by
        have h1 := congr_arg Subtype.val (b.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at h1
        exact h1
      rw [← hu_eq, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro j _
      have h0 : dotProduct v (b j).1 = 0 := congr_fun hv j
      rw [dotProduct_smul, h0, smul_zero]
    · intro hv
      funext j
      exact hv (b j).1 (b j).2
  have hsurj : Function.Surjective ev := by
    by_contra hns
    have hne : LinearMap.range ev ≠ ⊤ := fun htop => hns (LinearMap.range_eq_top.mp htop)
    have hdim_lt : Module.finrank F2 (LinearMap.range ev) < d := by
      calc Module.finrank F2 (LinearMap.range ev)
          < Module.finrank F2 (Fin d → F2) := Submodule.finrank_lt hne
        _ = d := Module.finrank_fin_fun F2
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range ev)
    have hW_pos : 0 < Module.finrank F2 W := by
      have hmod := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ev) W
      rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero,
        Module.finrank_fin_fun F2] at hmod
      omega
    have hW_ne : W ≠ ⊥ := fun hbot => by rw [hbot, finrank_bot] at hW_pos; omega
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne
    let pW : (Fin d → F2) →ₗ[F2] W := Submodule.projectionOnto W (LinearMap.range ev) hW.symm
    let bw := Module.finBasis F2 W
    have hex_i : ∃ i, bw.repr ⟨w, hwW⟩ i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hw0
      have h1 := congr_arg Subtype.val (bw.sum_repr ⟨w, hwW⟩)
      simp only [hall, zero_smul, Finset.sum_const_zero] at h1
      exact h1.symm
    rcases hex_i with ⟨i0, hi0⟩
    let φ : (Fin d → F2) →ₗ[F2] F2 := (bw.coord i0).comp pW
    let c : Fin d → F2 := fun j => φ (Pi.single j 1)
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hφw : φ w = bw.repr ⟨w, hwW⟩ i0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_left hW.symm ⟨w, hwW⟩]
        rfl
      have hφ_zero : φ w = 0 := by
        have hw_sum : w = ∑ j : Fin d, w j • Pi.single j (1 : F2) := by
          funext t; simp [Finset.sum_apply, Pi.single_apply]
        rw [hw_sum, map_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hcj : c j = 0 := congr_fun hc0 j
        rw [map_smul, show φ (Pi.single j 1) = c j from rfl, hcj, smul_zero]
      exact hi0 (hφw.symm.trans hφ_zero)
    have hcomb0 : ∑ j : Fin d, c j • (b j).1 = 0 := by
      funext t
      have hmem : ev (Pi.single t 1) ∈ LinearMap.range ev := ⟨Pi.single t 1, rfl⟩
      have hφ_ev : φ (ev (Pi.single t 1)) = 0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_right hW.symm ⟨_, hmem⟩, map_zero]
      have hev_sum : ev (Pi.single t 1) = ∑ j : Fin d, (b j).1 t • Pi.single j (1 : F2) := by
        funext j; simp [ev, dotProduct, Pi.single_apply, Finset.sum_apply]
      rw [hev_sum, map_sum] at hφ_ev
      simp only [map_smul, smul_eq_mul] at hφ_ev
      rw [Finset.sum_apply]
      calc ∑ j : Fin d, (c j • (b j).1) t
          = ∑ j : Fin d, (b j).1 t * c j :=
              Finset.sum_congr rfl fun j _ => by change c j * (b j).1 t = (b j).1 t * c j; ring
        _ = 0 := hφ_ev
    have hcombU : ∑ j : Fin d, c j • b j = 0 := by apply Subtype.ext; simpa using hcomb0
    exact hc_ne (funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hcombU))
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun F2,
    Module.finrank_fin_fun F2, hker, add_comm] at hrn
  exact hrn

private noncomputable def gaussN (u d : ℕ) : ℕ :=
  Nat.card {W : Submodule F2 (Fin u → F2) // Module.finrank F2 W = d}

private lemma gaussN_zero_right (u : ℕ) : gaussN u 0 = 1 := by
  classical
  have : Fintype (Submodule F2 (Fin u → F2)) := Fintype.ofFinite _
  simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : (Finset.univ : Finset (Submodule F2 (Fin u → F2))).filter
      (fun W : Submodule F2 (Fin u → F2) => Module.finrank F2 W = 0) = {(⊥ : Submodule F2 (Fin u → F2))} := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact Submodule.finrank_eq_zero
  rw [heq, Finset.card_singleton]

private lemma gaussN_eq_zero_of_gt {u d : ℕ} (h : u < d) : gaussN u d = 0 := by
  classical
  have : Fintype (Submodule F2 (Fin u → F2)) := Fintype.ofFinite _
  simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro W _ hW
  have hle : Module.finrank F2 W ≤ u := by
    calc Module.finrank F2 W ≤ Module.finrank F2 (Fin u → F2) := Submodule.finrank_le _
      _ = u := Module.finrank_fin_fun F2
  omega

private lemma card_submodules_eq_gaussN {V : Type} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (u d : ℕ) (hV : Module.finrank F2 V = u) :
    Nat.card {W : Submodule F2 V // Module.finrank F2 W = d} = gaussN u d := by
  classical
  let e : V ≃ₗ[F2] (Fin u → F2) :=
    (Module.finBasis F2 V).equivFun.trans (LinearEquiv.funCongrLeft F2 F2 (finCongr hV.symm))
  refine Nat.card_congr
    { toFun := fun W => ⟨W.1.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, W.2]⟩
      invFun := fun W => ⟨W.1.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, W.2]⟩
      left_inv := fun W => by
        apply Subtype.ext
        ext v
        simp only [Submodule.mem_map, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
        · intro hv; exact ⟨e v, ⟨v, hv, rfl⟩, e.symm_apply_apply v⟩
      right_inv := fun W => by
        apply Subtype.ext
        ext v
        simp only [Submodule.mem_map, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
        · intro hv; exact ⟨e.symm v, ⟨v, hv, rfl⟩, e.apply_symm_apply v⟩ }

private lemma card_submodules_le_eq_gaussN {V : Type} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (U : Submodule F2 V) (d : ℕ) :
    Nat.card {W : Submodule F2 V // W ≤ U ∧ Module.finrank F2 W = d} =
      gaussN (Module.finrank F2 U) d := by
  classical
  rw [← card_submodules_eq_gaussN (V := U) (Module.finrank F2 U) d rfl]
  refine Nat.card_congr
    { toFun := fun W =>
        ⟨W.1.comap U.subtype, by
          have hmap : (W.1.comap U.subtype).map U.subtype = W.1 := by
            rw [Submodule.map_comap_subtype, inf_eq_right.mpr W.2.1]
          have hfin := Submodule.finrank_map_subtype_eq U (W.1.comap U.subtype)
          rw [hmap, W.2.2] at hfin
          exact hfin.symm⟩
      invFun := fun W =>
        ⟨W.1.map U.subtype, by
          refine ⟨Submodule.map_subtype_le U W.1, ?_⟩
          rw [Submodule.finrank_map_subtype_eq, W.2]⟩
      left_inv := fun W => by
        apply Subtype.ext
        dsimp only
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr W.2.1]
      right_inv := fun W => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective U) W.1 }

private lemma card_submodules_ge_eq_gaussN {V : Type} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (U : Submodule F2 V) (j : ℕ) (hj : Module.finrank F2 U ≤ j) :
    Nat.card {W : Submodule F2 V // U ≤ W ∧ Module.finrank F2 W = j} =
      gaussN (Module.finrank F2 V - Module.finrank F2 U) (j - Module.finrank F2 U) := by
  classical
  have hqdim : Module.finrank F2 (V ⧸ U) = Module.finrank F2 V - Module.finrank F2 U := by
    have := Submodule.finrank_quotient_add_finrank U
    omega
  rw [← card_submodules_eq_gaussN (V := V ⧸ U) _ _ hqdim]
  refine Nat.card_congr
    { toFun := fun W =>
        ⟨W.1.map (Submodule.mkQ U), by
          let f : W.1 →ₗ[F2] (V ⧸ U) := (Submodule.mkQ U).comp W.1.subtype
          have hrg : LinearMap.range f = W.1.map (Submodule.mkQ U) := by
            ext y
            simp only [LinearMap.mem_range, f, LinearMap.comp_apply, Submodule.coe_subtype,
              Submodule.mem_map, Subtype.exists]
            constructor
            · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
            · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
          have hker_eq : Module.finrank F2 (LinearMap.ker f) = Module.finrank F2 U := by
            let e : LinearMap.ker f ≃ₗ[F2] U :=
              { toFun := fun x => ⟨x.1.1, (Submodule.Quotient.mk_eq_zero U).mp x.2⟩
                invFun := fun u => ⟨⟨u.1, W.2.1 u.2⟩, (Submodule.Quotient.mk_eq_zero U).mpr u.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl
                map_add' := fun _ _ => rfl
                map_smul' := fun _ _ => rfl }
            exact e.finrank_eq
          have hrn := LinearMap.finrank_range_add_finrank_ker f
          rw [hrg, hker_eq, W.2.2] at hrn
          omega⟩
      invFun := fun Q =>
        ⟨Q.1.comap (Submodule.mkQ U), by
          refine ⟨fun u hu => ?_, ?_⟩
          · change Submodule.mkQ U u ∈ Q.1
            rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu]
            exact Q.1.zero_mem
          · let W := Q.1.comap (Submodule.mkQ U)
            have hUW : U ≤ W := fun u hu => by
              change Submodule.mkQ U u ∈ Q.1
              rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu]
              exact Q.1.zero_mem
            let f : W →ₗ[F2] (V ⧸ U) := (Submodule.mkQ U).comp W.subtype
            have hrg : LinearMap.range f = Q.1 := by
              ext y
              simp only [LinearMap.mem_range, f, LinearMap.comp_apply, Submodule.coe_subtype,
                Subtype.exists]
              constructor
              · rintro ⟨x, hxW, rfl⟩; exact hxW
              · intro hyQ
                obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U y
                exact ⟨x, hyQ, rfl⟩
            have hker_eq : Module.finrank F2 (LinearMap.ker f) = Module.finrank F2 U := by
              let e : LinearMap.ker f ≃ₗ[F2] U :=
                { toFun := fun x => ⟨x.1.1, (Submodule.Quotient.mk_eq_zero U).mp x.2⟩
                  invFun := fun u => ⟨⟨u.1, hUW u.2⟩, (Submodule.Quotient.mk_eq_zero U).mpr u.2⟩
                  left_inv := fun _ => rfl
                  right_inv := fun _ => rfl
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              exact e.finrank_eq
            have hrn := LinearMap.finrank_range_add_finrank_ker f
            rw [hrg, hker_eq, Q.2] at hrn
            exact hrn.symm.trans (by omega)⟩
      left_inv := fun W => by
        apply Subtype.ext
        ext v
        simp only [Submodule.mem_comap, Submodule.mem_map]
        constructor
        · rintro ⟨w, hwW, hwq⟩
          have hsub : v - w ∈ U := by
            rw [← Submodule.Quotient.mk_eq_zero U]
            change Submodule.mkQ U (v - w) = 0
            rw [map_sub, hwq, sub_self]
          have hvw : v = w + (v - w) := by abel
          rw [hvw]
          exact W.1.add_mem hwW (W.2.1 hsub)
        · intro hvW
          exact ⟨v, hvW, rfl⟩
      right_inv := fun Q => by
        apply Subtype.ext
        ext y
        simp only [Submodule.mem_map, Submodule.mem_comap]
        constructor
        · rintro ⟨x, hxQ, rfl⟩; exact hxQ
        · intro hyQ
          obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U y
          exact ⟨x, hyQ, rfl⟩ }

private lemma gaussN_pascal (u d : ℕ) :
    gaussN (u + 1) (d + 1) = 2 ^ (d + 1) * gaussN u (d + 1) + gaussN u d := by
  classical
  have : Fintype (Submodule F2 (Fin (u + 1) → F2)) := Fintype.ofFinite _
  have : Fintype (Submodule F2 (Fin u → F2)) := Fintype.ofFinite _
  let e0 : Fin (u + 1) → F2 := Pi.single (Fin.last u) 1
  have he0_ne : e0 ≠ 0 := by
    intro h
    have := congr_fun h (Fin.last u)
    simp [e0] at this
  let All : Finset (Submodule F2 (Fin (u + 1) → F2)) :=
    (Finset.univ : Finset (Submodule F2 (Fin (u + 1) → F2))).filter
      (fun W : Submodule F2 (Fin (u + 1) → F2) => Module.finrank F2 W = d + 1)
  have hAll_card : All.card = gaussN (u + 1) (d + 1) := by
    simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype, All]
  let S1 := All.filter (fun W => e0 ∈ W)
  let S2 := All.filter (fun W => e0 ∉ W)
  have hsplit : S2.card + S1.card = All.card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    calc ∑ W ∈ All, ((if e0 ∉ W then 1 else 0) + (if e0 ∈ W then 1 else 0))
        = ∑ _W ∈ All, 1 := Finset.sum_congr rfl fun W _ => by by_cases h : e0 ∈ W <;> simp [h]
      _ = All.card := by simp
  have hS1_card : S1.card = gaussN u d := by
    let U0 : Submodule F2 (Fin (u + 1) → F2) := Submodule.span F2 {e0}
    have hU0_dim : Module.finrank F2 U0 = 1 := finrank_span_singleton he0_ne
    have hge := card_submodules_ge_eq_gaussN U0 (d + 1) (by omega)
    rw [Module.finrank_fin_fun F2, hU0_dim, Nat.add_sub_cancel, Nat.add_sub_cancel] at hge
    rw [← hge, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp only [S1, All, Finset.mem_filter, Finset.mem_univ, true_and, U0, Submodule.span_le,
      Set.singleton_subset_iff]
    exact and_comm
  let proj : (Fin (u + 1) → F2) →ₗ[F2] (Fin u → F2) :=
    { toFun := fun v i => v i.castSucc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker_proj : LinearMap.ker proj = Submodule.span F2 {e0} := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hv
      refine ⟨v (Fin.last u), ?_⟩
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [e0]
      · intro j
        have hj := congr_fun hv j
        simpa [e0, proj, Fin.castSucc_ne_last] using hj.symm
    · rintro ⟨c, rfl⟩
      funext j
      simp [proj, e0, Fin.castSucc_ne_last]
  let Base : Finset (Submodule F2 (Fin u → F2)) :=
    (Finset.univ : Finset (Submodule F2 (Fin u → F2))).filter
      (fun W' : Submodule F2 (Fin u → F2) => Module.finrank F2 W' = d + 1)
  have hBase_card : Base.card = gaussN u (d + 1) := by
    simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype, Base]
  have hS2_card : S2.card = 2 ^ (d + 1) * gaussN u (d + 1) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun W : Submodule F2 (Fin (u + 1) → F2) => W.map proj)
      (s := S2) (t := Base)
    have hmaps : ∀ W ∈ S2, W.map proj ∈ Base := by
      intro W hW
      simp only [S2, All, Finset.mem_filter, Finset.mem_univ, true_and] at hW
      simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and]
      let f : W →ₗ[F2] (Fin u → F2) := proj.comp W.subtype
      have hker0 : LinearMap.ker f = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxker : x.1 ∈ LinearMap.ker proj := hx
        rw [hker_proj, Submodule.mem_span_singleton] at hxker
        rcases hxker with ⟨c, hc⟩
        by_cases hc0 : c = 0
        · apply Subtype.ext; rw [← hc, hc0, zero_smul]; rfl
        · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
          rw [hc1, one_smul] at hc
          exact absurd (hc ▸ x.2) hW.2
      have hrg : LinearMap.range f = W.map proj := by
        ext y; simp [f, LinearMap.mem_range, Submodule.mem_map]
      have hrn := LinearMap.finrank_range_add_finrank_ker f
      rw [hrg, hker0, finrank_bot, add_zero, hW.1] at hrn
      exact hrn
    rw [hfib hmaps]
    have hper : ∀ W' ∈ Base, (S2.filter (fun W => W.map proj = W')).card = 2 ^ (d + 1) := by
      intro W' hW'
      simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and] at hW'
      letI : Finite (W' →ₗ[F2] F2) :=
        Finite.of_injective (fun f : W' →ₗ[F2] F2 => (f : W' → F2)) DFunLike.coe_injective
      letI : Fintype (W' →ₗ[F2] F2) := Fintype.ofFinite _
      have hdual_card : Fintype.card (W' →ₗ[F2] F2) = 2 ^ (d + 1) := by
        have hnc := Module.natCard_eq_pow_finrank (K := F2) (V := W' →ₗ[F2] F2)
        rw [Nat.card_eq_fintype_card, Nat.card_zmod, Module.finrank_linearMap,
          Module.finrank_self, mul_one, hW'] at hnc
        exact hnc
      rw [← hdual_card, ← Finset.card_univ]
      refine Finset.card_bij
        (fun W hW =>
          have hmem := (Finset.mem_filter.mp hW)
          have hW_dim := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem.1).1).2
          have hW_ne0 := (Finset.mem_filter.mp hmem.1).2
          have hW_map := hmem.2
          have hex : ∀ y : W', ∃ v : Fin (u + 1) → F2, v ∈ W ∧ proj v = y.1 := fun y => by
            have hy : y.1 ∈ W.map proj := hW_map.symm ▸ y.2
            exact Submodule.mem_map.mp hy
          have huniq : ∀ v1 v2 : Fin (u + 1) → F2, v1 ∈ W → v2 ∈ W → proj v1 = proj v2 → v1 = v2 := by
            intro v1 v2 hv1 hv2 hp
            have hdiff : v1 - v2 ∈ LinearMap.ker proj := by
              rw [LinearMap.mem_ker, map_sub, hp, sub_self]
            rw [hker_proj, Submodule.mem_span_singleton] at hdiff
            rcases hdiff with ⟨c, hc⟩
            by_cases hc0 : c = 0
            · rw [hc0, zero_smul] at hc; exact sub_eq_zero.mp hc.symm
            · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
              rw [hc1, one_smul] at hc
              exact absurd (hc ▸ W.sub_mem hv1 hv2) hW_ne0
          ({ toFun := fun y => (Classical.choose (hex y)) (Fin.last u)
             map_add' := fun y1 y2 => by
               have h1 := Classical.choose_spec (hex y1)
               have h2 := Classical.choose_spec (hex y2)
               have h12 := Classical.choose_spec (hex (y1 + y2))
               have heq := huniq _ _ h12.1 (W.add_mem h1.1 h2.1)
                 (by rw [h12.2, map_add, h1.2, h2.2]; rfl)
               exact congr_fun heq (Fin.last u)
             map_smul' := fun c y => by
               have h1 := Classical.choose_spec (hex y)
               have hc1 := Classical.choose_spec (hex (c • y))
               have heq := huniq _ _ hc1.1 (W.smul_mem c h1.1)
                 (by rw [hc1.2, map_smul, h1.2]; rfl)
               exact congr_fun heq (Fin.last u) } : W' →ₗ[F2] F2))
        ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro W1 hW1 W2 hW2 hφ
        have h1 := Finset.mem_filter.mp hW1
        have h2 := Finset.mem_filter.mp hW2
        have hW1_ne0 := (Finset.mem_filter.mp h1.1).2
        have hW2_ne0 := (Finset.mem_filter.mp h2.1).2
        have huniq1 : ∀ v1 v2 : Fin (u + 1) → F2, v1 ∈ W1 → v2 ∈ W1 → proj v1 = proj v2 → v1 = v2 := by
          intro v1 v2 hv1 hv2 hp
          have hdiff : v1 - v2 ∈ LinearMap.ker proj := by rw [LinearMap.mem_ker, map_sub, hp, sub_self]
          rw [hker_proj, Submodule.mem_span_singleton] at hdiff
          rcases hdiff with ⟨c, hc⟩
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact sub_eq_zero.mp hc.symm
          · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
            rw [hc1, one_smul] at hc; exact absurd (hc ▸ W1.sub_mem hv1 hv2) hW1_ne0
        have huniq2 : ∀ v1 v2 : Fin (u + 1) → F2, v1 ∈ W2 → v2 ∈ W2 → proj v1 = proj v2 → v1 = v2 := by
          intro v1 v2 hv1 hv2 hp
          have hdiff : v1 - v2 ∈ LinearMap.ker proj := by rw [LinearMap.mem_ker, map_sub, hp, sub_self]
          rw [hker_proj, Submodule.mem_span_singleton] at hdiff
          rcases hdiff with ⟨c, hc⟩
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact sub_eq_zero.mp hc.symm
          · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
            rw [hc1, one_smul] at hc; exact absurd (hc ▸ W2.sub_mem hv1 hv2) hW2_ne0
        ext v
        constructor
        · intro hv1
          have hpW' : proj v ∈ W' := h1.2 ▸ Submodule.mem_map_of_mem hv1
          obtain ⟨v2, hv2, hp2⟩ := Submodule.mem_map.mp (h2.2.symm ▸ hpW')
          have hlast := LinearMap.congr_fun hφ ⟨proj v, hpW'⟩
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hlast
          have hex1 : ∃ w, w ∈ W1 ∧ proj w = proj v := ⟨v, hv1, rfl⟩
          have hex2 : ∃ w, w ∈ W2 ∧ proj w = proj v := ⟨v2, hv2, hp2⟩
          have hc1_eq : Classical.choose hex1 = v :=
            huniq1 _ _ (Classical.choose_spec hex1).1 hv1 (Classical.choose_spec hex1).2
          have hc2_eq : Classical.choose hex2 = v2 :=
            huniq2 _ _ (Classical.choose_spec hex2).1 hv2 ((Classical.choose_spec hex2).2.trans hp2.symm)
          rw [hc1_eq, hc2_eq] at hlast
          have hveq : v = v2 := by
            funext i
            refine Fin.lastCases hlast (fun j => (congr_fun hp2 j).symm) i
          exact hveq ▸ hv2
        · intro hv2
          have hpW' : proj v ∈ W' := h2.2 ▸ Submodule.mem_map_of_mem hv2
          obtain ⟨v1, hv1, hp1⟩ := Submodule.mem_map.mp (h1.2.symm ▸ hpW')
          have hlast := LinearMap.congr_fun hφ ⟨proj v, hpW'⟩
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hlast
          have hex1 : ∃ w, w ∈ W1 ∧ proj w = proj v := ⟨v1, hv1, hp1⟩
          have hex2 : ∃ w, w ∈ W2 ∧ proj w = proj v := ⟨v, hv2, rfl⟩
          have hc1_eq : Classical.choose hex1 = v1 :=
            huniq1 _ _ (Classical.choose_spec hex1).1 hv1 ((Classical.choose_spec hex1).2.trans hp1.symm)
          have hc2_eq : Classical.choose hex2 = v :=
            huniq2 _ _ (Classical.choose_spec hex2).1 hv2 (Classical.choose_spec hex2).2
          rw [hc1_eq, hc2_eq] at hlast
          have hveq : v = v1 := by
            funext i
            refine Fin.lastCases hlast.symm (fun j => (congr_fun hp1 j).symm) i
          exact hveq ▸ hv1
      · intro φ _
        let lift : W' →ₗ[F2] (Fin (u + 1) → F2) :=
          { toFun := fun y => Fin.snoc y.1 (φ y)
            map_add' := fun y1 y2 => by
              funext i
              refine Fin.lastCases ?_ ?_ i
              · simp [map_add]
              · intro j; simp
            map_smul' := fun c y => by
              funext i
              refine Fin.lastCases ?_ ?_ i
              · simp [map_smul]
              · intro j; simp }
        have hlift_inj : Function.Injective lift := by
          intro y1 y2 h
          apply Subtype.ext
          funext j
          have := congr_fun h j.castSucc
          simpa [lift] using this
        let W : Submodule F2 (Fin (u + 1) → F2) := LinearMap.range lift
        have hW_dim : Module.finrank F2 W = d + 1 := by
          rw [LinearMap.finrank_range_of_inj hlift_inj, hW']
        have hW_ne0 : e0 ∉ W := by
          rintro ⟨y, hy⟩
          have hy0 : y = 0 := by
            apply Subtype.ext
            funext j
            have := congr_fun hy j.castSucc
            simpa [lift, e0, Fin.castSucc_ne_last] using this
          rw [hy0, map_zero] at hy
          exact he0_ne hy.symm
        have hW_map : W.map proj = W' := by
          ext y
          simp only [Submodule.mem_map, W, LinearMap.mem_range]
          constructor
          · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
            have : proj (lift z) = z.1 := by funext j; simp [proj, lift]
            rw [this]; exact z.2
          · intro hy
            refine ⟨lift ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
            funext j; simp [proj, lift]
        refine ⟨W, ?_, ?_⟩
        · simp only [Finset.mem_filter, S2, All, Finset.mem_univ, true_and]
          exact ⟨⟨hW_dim, hW_ne0⟩, hW_map⟩
        · ext y
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
          have hspec := Classical.choose_spec (show ∃ v, v ∈ W ∧ proj v = y.1 from
            ⟨lift y, ⟨y, rfl⟩, by funext j; simp [proj, lift]⟩)
          rcases hspec.1 with ⟨z, hz⟩
          have hzy : z = y := by
            apply Subtype.ext
            funext j
            have := congr_fun hspec.2 j
            rw [← hz] at this
            simpa [proj, lift] using this
          rw [← hz, hzy]
          simp [lift]
    rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul, hBase_card, mul_comm]
  omega

private lemma gauss_mobius (k : ℕ) :
    (∑ d ∈ Finset.range (k + 1), (-1 : ℤ) ^ d * (2 : ℤ) ^ (Nat.choose d 2) * (gaussN k d : ℤ)) =
      if k = 0 then 1 else 0 := by
  cases k with
  | zero =>
    simp [gaussN_zero_right]
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    let f : ℕ → ℤ := fun r => (-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose (r + 1) 2) * (gaussN m r : ℤ)
    have hstep : ∀ r ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (r + 1) * (2 : ℤ) ^ (Nat.choose (r + 1) 2) * (gaussN (m + 1) (r + 1) : ℤ) =
          f (r + 1) - f r := by
      intro r _
      rw [gaussN_pascal m r]
      push_cast
      have hch : Nat.choose (r + 2) 2 = Nat.choose (r + 1) 2 + (r + 1) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      simp only [f, hch, pow_add, pow_succ]
      ring
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, gaussN_zero_right, Nat.cast_one]
    rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub f (m + 1)]
    have hf0 : f 0 = 1 := by simp [f, gaussN_zero_right]
    have hfm : f (m + 1) = 0 := by simp [f, gaussN_eq_zero_of_gt (Nat.lt_succ_self m)]
    rw [hf0, hfm]
    norm_num

open Classical in
private lemma pair_sum_over_subspace {a b : ℕ} (H : Matrix (Fin a) (Fin b) F2)
    (W : Submodule F2 (Fin a → F2)) :
    (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
        (fun D => LinearMap.range D.mulVecLin ≤ W),
      chi (∑ x, ∑ y, D x y * H x y)) =
    if W ≤ orth (LinearMap.range H.mulVecLin) then
      (2 : ℤ) ^ (b * Module.finrank F2 W)
    else 0 := by
  classical
  let S := (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
    (fun D => LinearMap.range D.mulVecLin ≤ W)
  have hcol_iff : ∀ D : Matrix (Fin a) (Fin b) F2,
      LinearMap.range D.mulVecLin ≤ W ↔ ∀ y : Fin b, (fun x => D x y) ∈ W := by
    intro D
    constructor
    · intro h y
      have hmem : D.mulVecLin (Pi.single y 1) ∈ LinearMap.range D.mulVecLin := ⟨Pi.single y 1, rfl⟩
      have heq : D.mulVecLin (Pi.single y 1) = fun x => D x y := by
        funext x; simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
      exact heq ▸ h hmem
    · rintro h _ ⟨v, rfl⟩
      have hsum : D.mulVecLin v = ∑ y : Fin b, v y • (fun x => D x y) := by
        funext x
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun y _ => mul_comm _ _
      rw [hsum]
      exact Submodule.sum_mem W fun y _ => W.smul_mem (v y) (h y)
  by_cases hW : W ≤ orth (LinearMap.range H.mulVecLin)
  · simp only [hW, ↓reduceIte]
    have hall0 : ∀ D ∈ S, chi (∑ x, ∑ y, D x y * H x y) = 1 := by
      intro D hD
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hcol_iff] at hD
      have h0 : (∑ x, ∑ y, D x y * H x y) = 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro y _
        have hHy : (fun x => H x y) ∈ LinearMap.range H.mulVecLin := by
          refine ⟨Pi.single y 1, ?_⟩
          funext x; simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
        exact hW (hD y) (fun x => H x y) hHy
      rw [h0, chi_zero]
    rw [Finset.sum_congr rfl hall0, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcardS : S.card = 2 ^ (b * Module.finrank F2 W) := by
      have hbij : S.card = Fintype.card (Fin b → W) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun D hD y => ⟨fun x => D x y, (hcol_iff D).mp (Finset.mem_filter.mp hD).2 y⟩)
          ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro D1 _ D2 _ h
          ext x y
          exact congr_fun (congr_arg Subtype.val (congr_fun h y)) x
        · intro f _
          refine ⟨fun x y => (f y).1 x, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcol_iff _).mpr fun y => (f y).2⟩
          · funext y; apply Subtype.ext; rfl
      rw [hbij, Fintype.card_fun, Fintype.card_fin]
      have hWcard : Fintype.card W = 2 ^ Module.finrank F2 W := by
        have hnc := Module.natCard_eq_pow_finrank (K := F2) (V := W)
        rw [Nat.card_eq_fintype_card, Nat.card_zmod] at hnc
        exact hnc
      rw [hWcard, ← pow_mul, mul_comm]
    exact_mod_cast hcardS
  · simp only [hW, ↓reduceIte]
    have hex : ∃ w ∈ W, ∃ y0 : Fin b, dotProduct w (fun x => H x y0) = 1 := by
      by_contra hno
      push Not at hno
      apply hW
      intro w hwW u huH
      rcases huH with ⟨v, rfl⟩
      have hsum : H.mulVecLin v = ∑ y : Fin b, v y • (fun x => H x y) := by
        funext x
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun y _ => mul_comm _ _
      rw [hsum, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro y _
      have h0 : dotProduct w (fun x => H x y) = 0 := by
        have hne1 := hno w hwW y
        revert hne1; generalize dotProduct w (fun x => H x y) = z; revert z; decide
      rw [dotProduct_smul, h0, smul_zero]
    rcases hex with ⟨w, hwW, y0, hwH⟩
    let E : Matrix (Fin a) (Fin b) F2 := fun x y => if y = y0 then w x else 0
    have hES : ∀ D ∈ S, D + E ∈ S := by
      intro D hD
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hcol_iff] at hD ⊢
      intro y
      by_cases hy : y = y0
      · subst hy
        have : (fun x => (D + E) x y) = (fun x => D x y) + w := by
          funext x
          change D x y + E x y = D x y + w x
          simp [E]
        rw [this]
        exact W.add_mem (hD y) hwW
      · have : (fun x => (D + E) x y) = (fun x => D x y) := by
          funext x
          change D x y + E x y = D x y
          simp [E, hy]
        rw [this]
        exact hD y
    have hE_pair : (∑ x, ∑ y, E x y * H x y) = 1 := by
      rw [Finset.sum_comm, Finset.sum_eq_single y0]
      · simpa [E, dotProduct] using hwH
      · intro y _ hy; apply Finset.sum_eq_zero; intro x _; simp [E, hy]
      · intro h; exact absurd (Finset.mem_univ y0) h
    have hflip : ∀ D : Matrix (Fin a) (Fin b) F2,
        chi (∑ x, ∑ y, (D + E) x y * H x y) = - chi (∑ x, ∑ y, D x y * H x y) := by
      intro D
      have hadd : (∑ x, ∑ y, (D + E) x y * H x y) =
          (∑ x, ∑ y, D x y * H x y) + (∑ x, ∑ y, E x y * H x y) := by
        simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      rw [hadd, hE_pair, chi_add, chi_one]
      ring
    have hsum_neg : (∑ D ∈ S, chi (∑ x, ∑ y, D x y * H x y)) =
        -(∑ D ∈ S, chi (∑ x, ∑ y, D x y * H x y)) := by
      have hbij : (∑ D ∈ S, chi (∑ x, ∑ y, (D + E) x y * H x y)) =
          ∑ D ∈ S, chi (∑ x, ∑ y, D x y * H x y) := by
        refine Finset.sum_bij (fun D _ => D + E) hES ?_ ?_ (fun _ _ => rfl)
        · intro D1 _ D2 _ h; exact add_right_cancel h
        · intro D hD
          refine ⟨D + E, hES D hD, ?_⟩
          ext x y
          change (D x y + E x y) + E x y = D x y
          have : E x y + E x y = 0 := by generalize E x y = z; revert z; decide
          rw [add_assoc, this, add_zero]
      conv_lhs => rw [← hbij]
      simp_rw [hflip]
      rw [Finset.sum_neg_distrib]
    linarith

private lemma rank_shell_sum {a b j : ℕ} (hja : j ≤ a) (H : Matrix (Fin a) (Fin b) F2) :
    (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
      chi (∑ x, ∑ y, D x y * H x y)) =
    ∑ d ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - d) * (2 : ℤ) ^ (Nat.choose (j - d) 2) *
      (2 : ℤ) ^ (b * d) * (gaussN (a - H.rank) d : ℤ) * (gaussN (a - d) (j - d) : ℤ) := by
  classical
  haveI : Fintype (Submodule F2 (Fin a → F2)) := Fintype.ofFinite _
  let f : Submodule F2 (Fin a → F2) → ℤ := fun W =>
    ∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
        (fun D => LinearMap.range D.mulVecLin = W),
      chi (∑ x, ∑ y, D x y * H x y)
  let g : Submodule F2 (Fin a → F2) → ℤ := fun W =>
    ∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
        (fun D => LinearMap.range D.mulVecLin ≤ W),
      chi (∑ x, ∑ y, D x y * H x y)
  have hg_eq_sum_f : ∀ W : Submodule F2 (Fin a → F2),
      g W = ∑ U ∈ (Finset.univ : Finset (Submodule F2 (Fin a → F2))).filter (fun U => U ≤ W), f U := by
    intro W
    simp only [g, f]
    rw [← Finset.sum_biUnion]
    · congr 1
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hle; exact ⟨LinearMap.range D.mulVecLin, hle, rfl⟩
      · rintro ⟨U, hUW, rfl⟩; exact hUW
    · intro U1 _ U2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro D h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.symm.trans h2)
  have hmob_W : ∀ W : Submodule F2 (Fin a → F2), Module.finrank F2 W = j →
      f W = ∑ U ∈ (Finset.univ : Finset (Submodule F2 (Fin a → F2))).filter (fun U => U ≤ W),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U := by
    intro W hW
    simp_rw [hg_eq_sum_f]
    have hswap : (∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) *
          ∑ V ∈ Finset.univ.filter (fun V => V ≤ U), f V) =
        ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
          f V * ∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
            (-1 : ℤ) ^ (j - Module.finrank F2 U) *
              (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) := by
      calc ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) *
                ∑ V ∈ Finset.univ.filter (fun V => V ≤ U), f V
          = ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              ∑ V ∈ Finset.univ.filter (fun V => V ≤ U),
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * f V := by
              refine Finset.sum_congr rfl fun U _ => Finset.mul_sum _ _ _
        _ = ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
                if V ≤ U then
                  (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                    (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * f V
                else 0 := by
              refine Finset.sum_congr rfl fun U hU => ?_
              rw [← Finset.sum_filter]
              congr 1
              ext V
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
              exact ⟨fun h => ⟨le_trans h hU, h⟩, fun h => h.2⟩
        _ = ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
              ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
                if V ≤ U then
                  (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                    (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * f V
                else 0 := Finset.sum_comm
        _ = ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
              f V * ∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) := by
              refine Finset.sum_congr rfl fun V _ => ?_
              rw [Finset.mul_sum, ← Finset.sum_filter]
              refine Finset.sum_congr ?_ (fun _ _ => by ring)
              ext U
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact and_comm
    rw [hswap]
    have hinner : ∀ V ∈ Finset.univ.filter (fun V => V ≤ W),
        (∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
          (-1 : ℤ) ^ (j - Module.finrank F2 U) *
            (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2)) =
        if V = W then 1 else 0 := by
      intro V hV
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
      let k := j - Module.finrank F2 V
      have hVj : Module.finrank F2 V ≤ j := hW ▸ Submodule.finrank_mono hV
      have hfib : (∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
            (-1 : ℤ) ^ (j - Module.finrank F2 U) *
              (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2)) =
          ∑ r ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose r 2) * (gaussN k r : ℤ) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U)
          (t := Finset.range (k + 1))]
        · refine Finset.sum_congr rfl fun r hr => ?_
          have hkr : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hconst : ∑ U ∈ (Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
              (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r),
              (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) =
              ((Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
                (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r)).card *
                ((-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose r 2)) := by
            have h1 : ∀ U ∈ (Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
                (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r),
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) =
                (-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose r 2) := by
              intro U hU
              rw [(Finset.mem_filter.mp hU).2]
            rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          have hcard_r : ((Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
              (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r)).card = gaussN k r := by
            let V' : Submodule F2 W := V.comap W.subtype
            have hV'_dim : Module.finrank F2 V' = Module.finrank F2 V := by
              have h1 := Submodule.finrank_map_subtype_eq W V'
              rw [Submodule.map_comap_subtype, inf_eq_right.mpr hV] at h1
              exact h1.symm
            have hge := card_submodules_ge_eq_gaussN (V := W) V' (j - r) (by omega)
            rw [hW, hV'_dim] at hge
            have hkr_sub : j - r - Module.finrank F2 V = k - r := by omega
            have hsym : gaussN k (k - r) = gaussN k r := by
              have horth_bij : Nat.card {X : Submodule F2 (Fin k → F2) // Module.finrank F2 X = k - r} =
                  Nat.card {X : Submodule F2 (Fin k → F2) // Module.finrank F2 X = r} := by
                refine Nat.card_congr
                  { toFun := fun X => ⟨orth X.1, by have := finrank_orth_add X.1; omega⟩
                    invFun := fun X => ⟨orth X.1, by have := finrank_orth_add X.1; omega⟩
                    left_inv := fun X => Subtype.ext (by
                      dsimp only
                      symm
                      apply Submodule.eq_of_le_of_finrank_eq
                      · intro u hu v hv; rw [dotProduct_comm]; exact hv u hu
                      · have h1 := finrank_orth_add X.1
                        have h2 := finrank_orth_add (orth X.1)
                        omega)
                    right_inv := fun X => Subtype.ext (by
                      dsimp only
                      symm
                      apply Submodule.eq_of_le_of_finrank_eq
                      · intro u hu v hv; rw [dotProduct_comm]; exact hv u hu
                      · have h1 := finrank_orth_add X.1
                        have h2 := finrank_orth_add (orth X.1)
                        omega) }
              exact horth_bij
            rw [hkr_sub, hsym] at hge
            rw [← hge, Nat.card_eq_fintype_card, Fintype.card_subtype]
            refine Finset.card_bij (fun U _ => U.comap W.subtype) ?_ ?_ ?_
            · intro U hU
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
              have hUW : U ≤ W := hU.1.2
              have hVU : V ≤ U := hU.1.1
              have hU_dim : Module.finrank F2 (U.comap W.subtype) = Module.finrank F2 U := by
                have h1 := Submodule.finrank_map_subtype_eq W (U.comap W.subtype)
                rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUW] at h1
                exact h1.symm
              have hU_le : Module.finrank F2 U ≤ j := hW ▸ Submodule.finrank_mono hUW
              refine ⟨fun x hx => hVU hx, ?_⟩
              omega
            · intro U1 hU1 U2 hU2 h
              have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hU1).1).2.2
              have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hU2).1).2.2
              have hm1 : (U1.comap W.subtype).map W.subtype = U1 := by
                rw [Submodule.map_comap_subtype, inf_eq_right.mpr h1]
              have hm2 : (U2.comap W.subtype).map W.subtype = U2 := by
                rw [Submodule.map_comap_subtype, inf_eq_right.mpr h2]
              rw [← hm1, ← hm2, h]
            · intro Q hQ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
              refine ⟨Q.map W.subtype, ?_, Submodule.comap_map_eq_of_injective (Submodule.subtype_injective W) Q⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hQ_dim : Module.finrank F2 (Q.map W.subtype) = j - r := by
                rw [Submodule.finrank_map_subtype_eq, hQ.2]
              refine ⟨⟨fun v hv => ?_, Submodule.map_subtype_le W Q⟩, ?_⟩
              · exact ⟨⟨v, hV hv⟩, hQ.1 hv, rfl⟩
              · omega
          rw [hcard_r]
          ring
        · intro U hU
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
          have h1 : Module.finrank F2 V ≤ Module.finrank F2 U := Submodule.finrank_mono hU.1
          rw [Finset.mem_range]
          omega
      rw [hfib, gauss_mobius k]
      have hk0 : k = 0 ↔ V = W := by
        constructor
        · intro h0
          exact Submodule.eq_of_le_of_finrank_eq hV (by omega)
        · intro heq; subst heq; simp [k, hW]
      by_cases heq : V = W
      · simp [heq, hk0.mpr heq]
      · have hne : k ≠ 0 := fun h0 => heq (hk0.mp h0)
        simp [heq, hne]
    rw [Finset.sum_congr rfl fun V hV => by rw [hinner V hV]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hrank_split : (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
        chi (∑ x, ∑ y, D x y * H x y)) =
      ∑ W ∈ (Finset.univ : Finset (Submodule F2 (Fin a → F2))).filter
          (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
        f W := by
    simp only [f]
    rw [← Finset.sum_biUnion]
    · congr 1
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hrk; exact ⟨LinearMap.range D.mulVecLin, hrk, rfl⟩
      · rintro ⟨W, hW, hDW⟩; change Module.finrank F2 (LinearMap.range D.mulVecLin) = j; rw [hDW, hW]
    · intro W1 _ W2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro D h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.symm.trans h2)
  rw [hrank_split]
  rw [Finset.sum_congr rfl fun W hW => hmob_W W (Finset.mem_filter.mp hW).2]
  have hswap_WU : (∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
        ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
          (-1 : ℤ) ^ (j - Module.finrank F2 U) *
            (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U) =
      ∑ U ∈ Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U ≤ j),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U *
          ((Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
            U ≤ W ∧ Module.finrank F2 W = j)).card : ℤ) := by
    calc ∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
            ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U
        = ∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
            ∑ U ∈ Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U ≤ j),
              if U ≤ W then
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U
              else 0 := by
            refine Finset.sum_congr rfl fun W hW => ?_
            rw [← Finset.sum_filter]
            congr 1
            ext U
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
            exact ⟨fun h => ⟨hW ▸ Submodule.finrank_mono h, h⟩, fun h => h.2⟩
      _ = ∑ U ∈ Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U ≤ j),
            ∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
              if U ≤ W then
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U
              else 0 := Finset.sum_comm
      _ = _ := by
            refine Finset.sum_congr rfl fun U _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
            have hfilt : (Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
                Module.finrank F2 W = j)).filter (fun W => U ≤ W) =
              Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
                U ≤ W ∧ Module.finrank F2 W = j) := by
              ext W; simp [and_comm]
            rw [hfilt]
  rw [hswap_WU]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U)
    (t := Finset.range (j + 1))]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hdj : d ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hterm : ∀ U ∈ (Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) =>
        Module.finrank F2 U ≤ j)).filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U = d),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U *
          ((Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
            U ≤ W ∧ Module.finrank F2 W = j)).card : ℤ) =
        (if U ≤ orth (LinearMap.range H.mulVecLin) then
          (-1 : ℤ) ^ (j - d) * (2 : ℤ) ^ (Nat.choose (j - d) 2) *
            (2 : ℤ) ^ (b * d) * (gaussN (a - d) (j - d) : ℤ)
         else 0) := by
      intro U hU
      have hUd : Module.finrank F2 U = d := (Finset.mem_filter.mp hU).2
      have hge := card_submodules_ge_eq_gaussN U j (by omega)
      rw [Module.finrank_fin_fun F2, hUd, Nat.card_eq_fintype_card, Fintype.card_subtype] at hge
      have hgU : g U = if U ≤ orth (LinearMap.range H.mulVecLin) then (2 : ℤ) ^ (b * d) else 0 := by
        rw [← hUd]
        exact pair_sum_over_subspace H U
      rw [hUd, hgU, hge]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : (((Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) =>
        Module.finrank F2 U ≤ j)).filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U = d)).filter
        (fun U : Submodule F2 (Fin a → F2) => U ≤ orth (LinearMap.range H.mulVecLin))).card = gaussN (a - H.rank) d := by
      have hle := card_submodules_le_eq_gaussN (orth (LinearMap.range H.mulVecLin)) d
      have horth_dim : Module.finrank F2 (orth (LinearMap.range H.mulVecLin)) = a - H.rank := by
        have := finrank_orth_add (LinearMap.range H.mulVecLin)
        change Module.finrank F2 (orth (LinearMap.range H.mulVecLin)) + H.rank = a at this
        omega
      rw [horth_dim, Nat.card_eq_fintype_card, Fintype.card_subtype] at hle
      rw [← hle]
      congr 1
      ext U
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, rfl⟩, hle'⟩; exact ⟨hle', rfl⟩
      · rintro ⟨hle', rfl⟩; exact ⟨⟨hdj, rfl⟩, hle'⟩
    rw [hcard_le]
    ring
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hU)

private lemma main_proof (a b m j : ℕ) (hja : j ≤ a)
    (B : Fin m → Matrix (Fin a) (Fin b) F2) (value : Fin m → F2) :
    let gauss := fun (u d : ℕ) =>
      (Nat.card {W : Submodule F2 (Fin u → F2) // Module.finrank F2 W = d} : ℤ)
    let shell := fun (j h : ℕ) =>
      ∑ d ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - d) * 2 ^ (Nat.choose (j - d) 2) *
        2 ^ (b * d) * gauss (a - h) d * gauss (a - d) (j - d)
    let pair := fun (D H : Matrix (Fin a) (Fin b) F2) => ∑ x, ∑ y, D x y * H x y
    let count := Nat.card {D : Matrix (Fin a) (Fin b) F2 // Matrix.rank D = j ∧ ∀ i, pair D (B i) = value i}
    (2 : ℤ) ^ m * (count : ℤ) =
      ∑ S : Finset (Fin m), (if S.sum value = 0 then (1 : ℤ) else -1) *
        shell j (Matrix.rank (S.sum B)) := by
  classical
  intro gauss shell pair count
  have hcount : (2 : ℤ) ^ m * (count : ℤ) =
      ∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
        ∑ S : Finset (Fin m), chi (S.sum value + pair D (S.sum B)) := by
    have hinner : ∀ D : Matrix (Fin a) (Fin b) F2,
        (∑ S : Finset (Fin m), chi (S.sum value + pair D (S.sum B))) =
        if ∀ i, pair D (B i) = value i then (2 : ℤ) ^ m else 0 := by
      intro D
      have hlin : ∀ S : Finset (Fin m),
          S.sum value + pair D (S.sum B) = S.sum (fun i => value i + pair D (B i)) := by
        intro S
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [pair, Matrix.sum_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
      simp_rw [hlin]
      rw [sum_chi_powerset]
      congr 1
      apply propext
      refine forall_congr' fun i => ?_
      generalize value i = v
      generalize pair D (B i) = p
      revert v p; decide
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    simp only [count, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext D
    simp [Finset.mem_filter]
  rw [hcount, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hsplit : (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
      chi (S.sum value + pair D (S.sum B))) =
      chi (S.sum value) *
        ∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
          chi (pair D (S.sum B)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => chi_add _ _
  rw [hsplit]
  change (if S.sum value = 0 then (1 : ℤ) else -1) *
      (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
        chi (∑ x, ∑ y, D x y * (S.sum B) x y)) = _
  rw [rank_shell_sum hja (S.sum B)]
  rfl

end PEqualNP.Outside.L_lib_1061_aux

theorem PEqualNP.Outside.L_lib_1061 :
  ∀ (a b m j : ℕ), j ≤ a →
  let F := ZMod 2
  let M := Matrix (Fin a) (Fin b) F
  ∀ (B : Fin m → M) (value : Fin m → F),
  let gauss := fun (u d : ℕ) =>
    (Nat.card {W : Submodule F (Fin u → F) // Module.finrank F W = d} : ℤ)
  let shell := fun (j h : ℕ) =>
    ∑ d ∈ Finset.range (j+1), (-1 : ℤ)^(j-d) * 2^(Nat.choose (j-d) 2) *
      2^(b*d) * gauss (a-h) d * gauss (a-d) (j-d)
  let pair := fun (D H : M) => ∑ x, ∑ y, D x y * H x y
  let count := Nat.card {D : M // Matrix.rank D = j ∧ ∀ i, pair D (B i) = value i}
  (2 : ℤ)^m * (count : ℤ) =
    ∑ S : Finset (Fin m), (if S.sum value = 0 then (1 : ℤ) else -1) *
      shell j (Matrix.rank (S.sum B)) := by
  intro a b m j hja
  dsimp only
  intro B value
  exact PEqualNP.Outside.L_lib_1061_aux.main_proof a b m j hja B value
