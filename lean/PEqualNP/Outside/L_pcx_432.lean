import PEqualNP.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

namespace PEqualNP.Outside.L_pcx_432_aux

section Helpers

variable {K : Type} [Field K]

/-! ## Affine level sets and linear extensions -/

private def levelSet {V : Type*} [AddCommGroup V] [Module K V]
    (ℓ : V →ₗ[K] K) (α : K) : AffineSubspace K V :=
  (AffineSubspace.mk' α (⊥ : Submodule K K)).comap ℓ.toAffineMap

private lemma mem_levelSet {V : Type*} [AddCommGroup V] [Module K V]
    (ℓ : V →ₗ[K] K) (α : K) (x : V) :
    x ∈ levelSet ℓ α ↔ ℓ x = α := by
  simp [levelSet, AffineSubspace.mem_comap, AffineSubspace.mem_mk', sub_eq_zero]

private lemma mem_iInf_aff {ι : Sort*} {V : Type*} [AddCommGroup V] [Module K V]
    {s : ι → AffineSubspace K V} {x : V} : x ∈ ⨅ i, s i ↔ ∀ i, x ∈ s i := by
  change x ∈ ((⨅ i, s i : AffineSubspace K V) : Set V) ↔ _
  rw [AffineSubspace.coe_iInf, Set.mem_iInter]
  rfl

private lemma exists_linear_extension {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (S : Submodule K V) (f : S →ₗ[K] W) :
    ∃ g : V →ₗ[K] W, ∀ x : S, g x.1 = f x := by
  obtain ⟨T, hST⟩ := Submodule.exists_isCompl S
  let p : V →ₗ[K] S := S.projectionOnto T hST
  refine ⟨f.comp p, fun x => ?_⟩
  simp [p, Submodule.projectionOnto_apply_left]

private lemma exists_functional_sep_subspace {V : Type*} [AddCommGroup V] [Module K V]
    (S : Submodule K V) {v : V} (hv : v ∉ S) :
    ∃ ℓ : V →ₗ[K] K, (∀ w ∈ S, ℓ w = 0) ∧ ℓ v ≠ 0 := by
  have hne : (S.mkQ v : V ⧸ S) ≠ 0 := by
    intro h
    exact hv ((Submodule.Quotient.mk_eq_zero S).mp h)
  let L : Submodule K (V ⧸ S) := K ∙ S.mkQ v
  let eL := LinearEquiv.toSpanNonzeroSingleton K (V ⧸ S) (S.mkQ v) hne
  let f₀ : L →ₗ[K] K := eL.symm.toLinearMap
  obtain ⟨g, hg⟩ := exists_linear_extension L f₀
  refine ⟨g.comp S.mkQ, ?_, ?_⟩
  · intro w hw
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr hw, map_zero]
  · change g (S.mkQ v) ≠ 0
    have hvL : S.mkQ v ∈ L := Submodule.mem_span_singleton_self (S.mkQ v)
    rw [hg ⟨S.mkQ v, hvL⟩]
    have h1 : f₀ ⟨S.mkQ v, hvL⟩ = 1 := by
      apply eL.injective
      change eL (eL.symm ⟨S.mkQ v, hvL⟩) = eL 1
      rw [eL.apply_symm_apply]
      apply Subtype.ext
      change S.mkQ v = (1 : K) • S.mkQ v
      rw [one_smul]
    rw [h1]
    exact one_ne_zero

private lemma exists_section_ext {U V : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (f : U →ₗ[K] V) :
    ∃ σ : V →ₗ[K] U, ∀ y ∈ LinearMap.range f, f (σ y) = y := by
  let f' : U →ₗ[K] LinearMap.range f := f.rangeRestrict
  have hsurj : Function.Surjective f' := LinearMap.surjective_rangeRestrict f
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f' (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨σ, hσ⟩ := exists_linear_extension (LinearMap.range f) s
  refine ⟨σ, fun y hy => ?_⟩
  rw [hσ ⟨y, hy⟩]
  have h1 := LinearMap.congr_fun hs ⟨y, hy⟩
  exact congrArg Subtype.val h1

/-! ## Forward Separation Lemma (Cover → Non-adaptive Linear Queries) -/

private lemma forward_sep {V : Type*} [AddCommGroup V] [Module K V] :
    ∀ (g : ℕ) (_hg : 0 < g) (P : AffineSubspace K V) (_hP : (P : Set V).Nonempty)
      (E : Fin g → AffineSubspace K V)
      (_hcov : ∀ x ∈ P, ∃ j : Fin g, x ∉ E j),
      ∃ (ℓ : Fin (g - 1) → (V →ₗ[K] K)) (pick : (Fin (g - 1) → K) → Fin g),
        ∀ x ∈ P, x ∉ E (pick (fun t => ℓ t x)) := by
  classical
  intro g
  induction g with
  | zero => intro hg; omega
  | succ g ih =>
    intro _ P hP E hcov
    cases g with
    | zero =>
      refine ⟨Fin.elim0, fun _ => 0, fun x hx => ?_⟩
      obtain ⟨j, hj⟩ := hcov x hx
      have hj0 : j = 0 := Fin.ext (by omega)
      rwa [hj0] at hj
    | succ g' =>
      let g1 := g' + 1
      let U : AffineSubspace K V := P ⊓ ⨅ j : Fin g1, E j.castSucc
      let Wsub : AffineSubspace K V := P ⊓ E (Fin.last g1)
      by_cases hU : (U : Set V).Nonempty
      · by_cases hW : (Wsub : Set V).Nonempty
        · obtain ⟨u₀, hu₀⟩ := hU
          obtain ⟨v₀, hv₀⟩ := hW
          have hdisj : ∀ x : V, ¬ (x ∈ U ∧ x ∈ Wsub) := by
            intro x ⟨hxU, hxW⟩
            have hxP : x ∈ P := hxU.1
            obtain ⟨j, hj⟩ := hcov x hxP
            refine Fin.lastCases ?_ ?_ j hj
            · exact fun h => h hxW.2
            · intro j' h
              have hmem := mem_iInf_aff.mp hxU.2 j'
              exact h hmem
          have hnotmem : u₀ - v₀ ∉ U.direction ⊔ Wsub.direction := by
            intro hmem
            rw [Submodule.mem_sup] at hmem
            obtain ⟨du, hdu, dw, hdw, heq⟩ := hmem
            have hx : v₀ + dw = u₀ - du := by
              rw [← sub_eq_zero, show v₀ + dw - (u₀ - du) = (du + dw) - (u₀ - v₀) by abel,
                heq, sub_self]
            have hxW : v₀ + dw ∈ Wsub := by
              have := AffineSubspace.vadd_mem_of_mem_direction hdw hv₀
              rwa [vadd_eq_add, add_comm] at this
            have hxU : u₀ - du ∈ U := by
              have hneg : -du ∈ U.direction := Submodule.neg_mem _ hdu
              have := AffineSubspace.vadd_mem_of_mem_direction hneg hu₀
              rwa [vadd_eq_add, add_comm, ← sub_eq_add_neg] at this
            exact hdisj (v₀ + dw) ⟨hx ▸ hxU, hxW⟩
          obtain ⟨ℓ₀, hℓ₀_zero, hℓ₀_ne⟩ :=
            exists_functional_sep_subspace (U.direction ⊔ Wsub.direction) hnotmem
          let α : K := ℓ₀ v₀
          have hℓ₀_W : ∀ v ∈ Wsub, ℓ₀ v = α := by
            intro v hv
            have hdv : v -ᵥ v₀ ∈ Wsub.direction := AffineSubspace.vsub_mem_direction hv hv₀
            have hz : ℓ₀ (v - v₀) = 0 :=
              hℓ₀_zero _ (Submodule.mem_sup_right hdv)
            rw [map_sub, sub_eq_zero] at hz
            exact hz
          have hℓ₀_U : ∀ u ∈ U, ℓ₀ u ≠ α := by
            intro u hu heq
            have hdu : u -ᵥ u₀ ∈ U.direction := AffineSubspace.vsub_mem_direction hu hu₀
            have hz : ℓ₀ (u - u₀) = 0 :=
              hℓ₀_zero _ (Submodule.mem_sup_left hdu)
            rw [map_sub, sub_eq_zero] at hz
            apply hℓ₀_ne
            rw [map_sub, sub_eq_zero, ← hz, heq]
          let P' : AffineSubspace K V := P ⊓ levelSet ℓ₀ α
          have hP' : (P' : Set V).Nonempty :=
            ⟨v₀, hv₀.1, (mem_levelSet ℓ₀ α v₀).mpr rfl⟩
          have hcov' : ∀ x ∈ P', ∃ j : Fin g1, x ∉ E j.castSucc := by
            intro x ⟨hxP, hxα⟩
            by_contra hall
            push Not at hall
            have hxU : x ∈ U := ⟨hxP, mem_iInf_aff.mpr hall⟩
            exact hℓ₀_U x hxU ((mem_levelSet ℓ₀ α x).mp hxα)
          obtain ⟨ℓ', pick', hpick'⟩ := ih (Nat.succ_pos g') P' hP' (fun j => E j.castSucc) hcov'
          let ℓ_all : Fin (g' + 1) → (V →ₗ[K] K) :=
            Fin.snoc (α := fun _ => V →ₗ[K] K) ℓ' ℓ₀
          let pick_all : (Fin (g' + 1) → K) → Fin (g1 + 1) := fun y =>
            if y (Fin.last g') = α then (pick' (fun t => y t.castSucc)).castSucc
            else Fin.last g1
          refine ⟨ℓ_all, pick_all, fun x hx => ?_⟩
          have hlast : ℓ_all (Fin.last g') x = ℓ₀ x := by
            simp [ℓ_all]
          have hcast : (fun t : Fin g' => ℓ_all t.castSucc x) = (fun t => ℓ' t x) := by
            funext t; simp [ℓ_all]
          dsimp only [pick_all]
          simp only [hlast]
          by_cases hxα : ℓ₀ x = α
          · simp only [hxα, ↓reduceIte]
            have hgoal := hpick' x ⟨hx, (mem_levelSet ℓ₀ α x).mpr hxα⟩
            rwa [← hcast] at hgoal
          · simp only [hxα, ↓reduceIte]
            intro hbad
            exact hxα (hℓ₀_W x ⟨hx, hbad⟩)
        · -- Wsub is empty: E (Fin.last g1) misses P completely!
          refine ⟨fun _ => 0, fun _ => Fin.last g1, fun x hx hbad => ?_⟩
          exact hW ⟨x, hx, hbad⟩
      · -- U is empty: E 0..E (g1-1) already cover P!
        have hcov' : ∀ x ∈ P, ∃ j : Fin g1, x ∉ E j.castSucc := by
          intro x hx
          by_contra hall
          push Not at hall
          exact hU ⟨x, hx, mem_iInf_aff.mpr hall⟩
        obtain ⟨ℓ', pick', hpick'⟩ := ih (Nat.succ_pos g') P hP (fun j => E j.castSucc) hcov'
        let ℓ_all : Fin (g' + 1) → (V →ₗ[K] K) :=
          Fin.snoc (α := fun _ => V →ₗ[K] K) ℓ' 0
        let pick_all : (Fin (g' + 1) → K) → Fin (g1 + 1) :=
          fun y => (pick' (fun t => y t.castSucc)).castSucc
        refine ⟨ℓ_all, pick_all, fun x hx => ?_⟩
        dsimp only [pick_all]
        have hcast : (fun t : Fin g' => ℓ_all t.castSucc x) = (fun t => ℓ' t x) := by
          funext t; simp [ℓ_all]
        have hgoal := hpick' x hx
        rwa [← hcast] at hgoal

/-! ## Backward Separation Lemma (Linear Queries → Small Affine Cover) -/

private lemma backward_sep {V : Type*} [AddCommGroup V] [Module K V] :
    ∀ (r : ℕ) (P : AffineSubspace K V) (_hP : (P : Set V).Nonempty)
      (Φ : V →ₗ[K] (Fin r → K)) (H : (Fin r → K) → AffineSubspace K V)
      (_hH : ∀ c ∈ Φ '' (P : Set V), ∀ x ∈ P, Φ x = c → x ∉ H c),
      ∃ C : Finset (Fin r → K), C.Nonempty ∧ C.card ≤ r + 1 ∧
        (∀ c ∈ C, c ∈ Φ '' (P : Set V)) ∧
        ∀ x ∈ P, ∃ c ∈ C, x ∉ H c := by
  classical
  intro r
  induction r with
  | zero =>
    intro P hP Φ H hH
    obtain ⟨x₀, hx₀⟩ := hP
    let c₀ := Φ x₀
    refine ⟨{c₀}, Finset.singleton_nonempty c₀, by simp, ?_, ?_⟩
    · intro c hc
      rw [Finset.mem_singleton] at hc
      exact ⟨x₀, hx₀, hc.symm⟩
    · intro x hx
      refine ⟨c₀, Finset.mem_singleton_self c₀, ?_⟩
      have heq : Φ x = c₀ := Subsingleton.elim _ _
      exact hH c₀ ⟨x₀, hx₀, rfl⟩ x hx heq
  | succ r ih =>
    intro P hP Φ H hH
    obtain ⟨x₀, hx₀⟩ := hP
    let c₀ := Φ x₀
    have hc₀ : c₀ ∈ Φ '' (P : Set V) := ⟨x₀, hx₀, rfl⟩
    let P' : AffineSubspace K V := P ⊓ H c₀
    by_cases hP' : (P' : Set V).Nonempty
    · let Q' : AffineSubspace K (Fin (r + 1) → K) := P'.map Φ.toAffineMap
      obtain ⟨x₁, hx₁⟩ := hP'
      have hQ'ne : (Q' : Set (Fin (r + 1) → K)).Nonempty :=
        ⟨Φ x₁, ⟨x₁, hx₁, rfl⟩⟩
      have hc₀_nmem : c₀ ∉ Q' := by
        rintro ⟨x, hxP', hΦx⟩
        exact hH c₀ hc₀ x hxP'.1 hΦx hxP'.2
      have hdir_ne : Q'.direction ≠ ⊤ := by
        intro htop
        have hmem : c₀ - Φ x₁ ∈ Q'.direction := by rw [htop]; trivial
        have hc₀_in : c₀ ∈ Q' := by
          have := AffineSubspace.vadd_mem_of_mem_direction hmem ⟨x₁, hx₁, rfl⟩
          simpa [vadd_eq_add] using this
        exact hc₀_nmem hc₀_in
      have hfr_lt : Module.finrank K Q'.direction < r + 1 := by
        have h1 := Submodule.finrank_lt hdir_ne
        simpa [Module.finrank_fin_fun] using h1
      let d' := Module.finrank K Q'.direction
      have hd' : d' ≤ r := Nat.lt_succ_iff.mp hfr_lt
      let bDir : Module.Basis (Fin d') K Q'.direction := Module.finBasis K Q'.direction
      let pad : (Fin d' → K) →ₗ[K] (Fin r → K) :=
        { toFun := fun v i => if h : i.val < d' then v ⟨i.val, h⟩ else 0
          map_add' := fun u v => by funext i; by_cases h : i.val < d' <;> simp [h]
          map_smul' := fun a u => by funext i; by_cases h : i.val < d' <;> simp [h] }
      have hpad_inj : Function.Injective pad := by
        intro u v huv
        funext j
        have := congrFun huv ⟨j.val, lt_of_lt_of_le j.isLt hd'⟩
        simpa [pad, j.isLt] using this
      let ι : Q'.direction →ₗ[K] (Fin r → K) := pad.comp bDir.equivFun.toLinearMap
      have hι_inj : Function.Injective ι := hpad_inj.comp bDir.equivFun.injective
      obtain ⟨π, hπ⟩ := exists_linear_extension Q'.direction ι
      have hπ_inj_Q' : ∀ y₁ ∈ Q', ∀ y₂ ∈ Q', π y₁ = π y₂ → y₁ = y₂ := by
        intro y₁ hy₁ y₂ hy₂ heq
        have hsub : y₁ - y₂ ∈ Q'.direction := AffineSubspace.vsub_mem_direction hy₁ hy₂
        have hz : π (y₁ - y₂) = 0 := by rw [map_sub, heq, sub_self]
        rw [hπ ⟨y₁ - y₂, hsub⟩] at hz
        have h0 : (⟨y₁ - y₂, hsub⟩ : Q'.direction) = 0 := hι_inj (hz.trans (map_zero ι).symm)
        exact sub_eq_zero.mp (congrArg Subtype.val h0)
      let Φ' : V →ₗ[K] (Fin r → K) := π.comp Φ
      let lift : (Fin r → K) → (Fin (r + 1) → K) := fun c' =>
        if h : ∃ x ∈ P', Φ' x = c' then Φ (Classical.choose h) else c₀
      have hlift_eq : ∀ x ∈ P', lift (Φ' x) = Φ x := by
        intro x hx
        have hex : ∃ x' ∈ P', Φ' x' = Φ' x := ⟨x, hx, rfl⟩
        dsimp only [lift]
        simp only [hex, ↓reduceDIte]
        have hx' := Classical.choose_spec hex
        apply hπ_inj_Q'
        · exact ⟨Classical.choose hex, hx'.1, rfl⟩
        · exact ⟨x, hx, rfl⟩
        · exact hx'.2
      have hH' : ∀ c' ∈ Φ' '' (P' : Set V), ∀ x ∈ P', Φ' x = c' → x ∉ H (lift c') := by
        intro c' _ x hx hΦ'x
        rw [← hΦ'x, hlift_eq x hx]
        exact hH (Φ x) ⟨x, hx.1, rfl⟩ x hx.1 rfl
      obtain ⟨C', hC'ne, hC'card, hC'mem, hC'cov⟩ :=
        ih P' ⟨x₁, hx₁⟩ Φ' (fun c' => H (lift c')) hH'
      let C : Finset (Fin (r + 1) → K) := insert c₀ (C'.image lift)
      refine ⟨C, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
      · calc C.card ≤ (C'.image lift).card + 1 := Finset.card_insert_le _ _
          _ ≤ C'.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
          _ ≤ (r + 1) + 1 := Nat.add_le_add_right hC'card 1
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hmem
        · exact hc₀
        · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hmem
          obtain ⟨x, hxP', hΦ'x⟩ := hC'mem c' hc'
          rw [← hΦ'x, hlift_eq x hxP']
          exact ⟨x, hxP'.1, rfl⟩
      · intro x hx
        by_cases hxH : x ∈ H c₀
        · obtain ⟨c', hc', hxnc'⟩ := hC'cov x ⟨hx, hxH⟩
          exact ⟨lift c', Finset.mem_insert_of_mem (Finset.mem_image_of_mem lift hc'), hxnc'⟩
        · exact ⟨c₀, Finset.mem_insert_self _ _, hxH⟩
    · refine ⟨{c₀}, Finset.singleton_nonempty c₀, by simp, ?_, ?_⟩
      · intro c hc
        rw [Finset.mem_singleton] at hc
        exact hc ▸ hc₀
      · intro x hx
        refine ⟨c₀, Finset.mem_singleton_self c₀, fun hmem => hP' ⟨x, hx, hmem⟩⟩

/-! ## Unified Row-Basis Extraction Lemma -/

private lemma exists_allowed_basis {n k r : ℕ}
    (V : Submodule K (Fin k → K))
    (L : Fin r → ((Fin n → K) × (Fin k → K)) →ₗ[K] K)
    (S_allow : Set ((Fin k → K) →ₗ[K] K))
    (hleg : ∀ j, (L j).comp (LinearMap.inr K (Fin n → K) (Fin k → K)) = 0 ∨
      (L j).comp (LinearMap.inr K (Fin n → K) (Fin k → K)) ∈ S_allow) :
    let LU : V →ₗ[K] (Fin r → K) :=
      LinearMap.pi fun j => ((L j).comp (LinearMap.inr K (Fin n → K) (Fin k → K))).domRestrict V
    ∃ R : Finset ((Fin k → K) →ₗ[K] K),
      (∀ f ∈ R, f ∈ S_allow) ∧
      R.card = Module.finrank K (LinearMap.range LU) ∧
      ∀ v : V, (∀ f ∈ R, f v.1 = 0) ↔ LU v = 0 := by
  classical
  intro LU
  let row : Fin r → ((Fin k → K) →ₗ[K] K) :=
    fun j => (L j).comp (LinearMap.inr K (Fin n → K) (Fin k → K))
  let S₀ : Finset ((Fin k → K) →ₗ[K] K) :=
    (Finset.univ.image row).filter (fun f => f.domRestrict V ≠ 0)
  have hS₀_allow : ∀ f ∈ S₀, f ∈ S_allow := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_image] at hf
    obtain ⟨⟨j, _, rfl⟩, hne⟩ := hf
    rcases hleg j with hz | hmem
    · exfalso; apply hne; ext v; simp [row, hz]
    · exact hmem
  let S₀_res : Finset (V →ₗ[K] K) := S₀.image (fun f => f.domRestrict V)
  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent K (S₀_res : Set (V →ₗ[K] K))
  have ht_fin : t.Finite := Set.Finite.subset S₀_res.finite_toSet ht_sub
  let R_res : Finset (V →ₗ[K] K) := ht_fin.toFinset
  have hR_res_sub : R_res ⊆ S₀_res := by
    intro g hg
    exact ht_sub (ht_fin.mem_toFinset.mp hg)
  have hR_res_span : Submodule.span K (R_res : Set (V →ₗ[K] K)) =
      Submodule.span K (S₀_res : Set (V →ₗ[K] K)) := by
    have : (R_res : Set (V →ₗ[K] K)) = t := ht_fin.coe_toFinset
    rw [this, ht_span]
  have hR_res_ind : LinearIndependent K (fun g : R_res => (g.1 : V →ₗ[K] K)) :=
    ht_ind.comp (fun g : R_res => (⟨g.1, ht_fin.mem_toFinset.mp g.2⟩ : t))
      (fun _ _ h => Subtype.ext (congrArg (fun p : t => p.1) h))
  let pickPre : (V →ₗ[K] K) → ((Fin k → K) →ₗ[K] K) := fun g =>
    if h : ∃ f ∈ S₀, f.domRestrict V = g then Classical.choose h else 0
  have hpick_spec : ∀ g ∈ R_res, pickPre g ∈ S₀ ∧ (pickPre g).domRestrict V = g := by
    intro g hg
    have hg' : g ∈ S₀_res := hR_res_sub hg
    obtain ⟨f, hf, hfg⟩ := Finset.mem_image.mp hg'
    have hex : ∃ f ∈ S₀, f.domRestrict V = g := ⟨f, hf, hfg⟩
    dsimp only [pickPre]
    simp only [hex, ↓reduceDIte]
    exact Classical.choose_spec hex
  let R : Finset ((Fin k → K) →ₗ[K] K) := R_res.image pickPre
  have hR_allow : ∀ f ∈ R, f ∈ S_allow := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    exact hS₀_allow _ (hpick_spec g hg).1
  have hR_card : R.card = R_res.card := by
    apply Finset.card_image_of_injOn
    intro g₁ hg₁ g₂ hg₂ heq
    rw [← (hpick_spec g₁ hg₁).2, ← (hpick_spec g₂ hg₂).2, heq]
  have hR_res_eq_image : R.image (fun f => f.domRestrict V) = R_res := by
    ext g
    simp only [Finset.mem_image, R]
    constructor
    · rintro ⟨_, ⟨g', hg', rfl⟩, rfl⟩
      rw [(hpick_spec g' hg').2]
      exact hg'
    · intro hg
      exact ⟨pickPre g, ⟨g, hg, rfl⟩, (hpick_spec g hg).2⟩
  have hker : ∀ v : V, (∀ f ∈ R, f v.1 = 0) ↔ LU v = 0 := by
    intro v
    constructor
    · intro hzero
      let Kv : Submodule K (V →ₗ[K] K) :=
        { carrier := {g | g v = 0}, add_mem' := fun {a b} ha hb => by
            change (a + b) v = 0; rw [LinearMap.add_apply, ha, hb, add_zero],
          zero_mem' := rfl,
          smul_mem' := fun c {a} ha => by
            change (c • a) v = 0; rw [LinearMap.smul_apply, ha, smul_zero] }
      have hR_sub_Kv : (R_res : Set (V →ₗ[K] K)) ⊆ Kv := by
        intro g hg
        rw [← hR_res_eq_image] at hg
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
        exact hzero f hf
      have hspan_le : Submodule.span K (S₀_res : Set (V →ₗ[K] K)) ≤ Kv := by
        rw [← hR_res_span, Submodule.span_le]
        exact hR_sub_Kv
      funext j
      change (row j).domRestrict V v = 0
      by_cases hj : (row j).domRestrict V = 0
      · simp [hj]
      · have hmem : row j ∈ S₀ := by
          simp only [S₀, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨⟨j, rfl⟩, hj⟩
        have hmem_res : (row j).domRestrict V ∈ S₀_res :=
          Finset.mem_image_of_mem _ hmem
        exact hspan_le (Submodule.subset_span hmem_res)
    · intro hLU f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      have hmemS₀ := (hpick_spec g hg).1
      rw [Finset.mem_filter, Finset.mem_image] at hmemS₀
      obtain ⟨⟨j, _, hj⟩, _⟩ := hmemS₀
      rw [← hj]
      exact congrFun hLU j
  let evalR : V →ₗ[K] (R_res → K) :=
    { toFun := fun v g => g.1 v
      map_add' := fun u v => by funext g; simp
      map_smul' := fun c u => by funext g; simp }
  have hker_evalR : LinearMap.ker evalR = LinearMap.ker LU := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hker v]
    constructor
    · intro h f hf
      have hmem : f.domRestrict V ∈ R_res := by
        rw [← hR_res_eq_image]; exact Finset.mem_image_of_mem _ hf
      exact congrFun h ⟨f.domRestrict V, hmem⟩
    · intro h
      funext ⟨g, hg⟩
      change g v = 0
      rw [← (hpick_spec g hg).2]
      exact h (pickPre g) (Finset.mem_image_of_mem _ hg)
  have hevalR_surj : LinearMap.range evalR = ⊤ := by
    by_contra hne
    obtain ⟨y, hy⟩ : ∃ y : R_res → K, y ∉ LinearMap.range evalR := by
      by_contra hall
      push Not at hall
      exact hne (eq_top_iff.mpr fun y _ => hall y)
    obtain ⟨c, hc_zero, hc_ne⟩ := exists_functional_sep_subspace (LinearMap.range evalR) hy
    let coeffs : R_res → K := fun g => c (Pi.single g 1)
    have hlin : ∑ g : R_res, coeffs g • (g.1 : V →ₗ[K] K) = 0 := by
      ext v
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      have hdecomp : evalR v = ∑ g : R_res, (g.1 v) • Pi.single g (1 : K) := by
        funext g'
        simp [evalR, Finset.sum_apply, Pi.single_apply]
      have hz := hc_zero (evalR v) ⟨v, rfl⟩
      rw [hdecomp, map_sum] at hz
      simpa only [map_smul, smul_eq_mul, mul_comm, coeffs] using hz
    have hcoeff_zero := Fintype.linearIndependent_iff.mp hR_res_ind coeffs hlin
    apply hc_ne
    have hy_decomp : y = ∑ g : R_res, (y g) • Pi.single g (1 : K) := by
      funext g'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hy_decomp, map_sum]
    apply Finset.sum_eq_zero
    intro g _
    rw [map_smul, show c (Pi.single g 1) = coeffs g from rfl, hcoeff_zero g, smul_zero]
  have hcard_eq : R.card = Module.finrank K (LinearMap.range LU) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker evalR
    have h2 := LinearMap.finrank_range_add_finrank_ker LU
    rw [hker_evalR, hevalR_surj, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] at h1
    omega
  exact ⟨R, hR_allow, hcard_eq, hker⟩

end Helpers

/-! ## Main Equivalence -/

private lemma main_proof (K : Type) [Field K] [Fintype K] [DecidableEq K] (n k t m d e : ℕ) :
    let X := Fin n → K
    let U := Fin k → K
    let Y := Fin t → K
    let Z := X × U
    let W := U →ₗ[K] K
    ∀ (P : AffineSubspace K X) (bad : Fin m → AffineSubspace K X)
      (M : Fin m → U →ₗ[K] Y) (A B : Set W),
      let legal := fun (S : Set W) (f : Z →ₗ[K] K) =>
        f.comp (LinearMap.inr K X U) = 0 ∨ f.comp (LinearMap.inr K X U) ∈ S
      (∃ x : X, x ∈ P) →
      ((∃ (ask : Fin d → Z →ₗ[K] K) (next : (Fin d → K) → Fin e → Z →ₗ[K] K)
          (out : (Fin d → K) → (Fin e → K) → Fin m × Y),
        (∀ j, legal A (ask j)) ∧ (∀ z j, legal B (next z j)) ∧
        ∀ x ∈ P, ∀ u : U,
          let z := fun j => ask j (x, u)
          let a := out z (fun j => next z j (x, u))
          x ∉ bad a.1 ∧ a.2 = M a.1 u) ↔
      ∃ (g : ℕ) (Q : Finset W) (S : Fin g → Finset (Fin m)) (R : Fin g → Finset W),
        0 < g ∧ (∀ f ∈ Q, f ∈ A) ∧ Q.card + (g - 1) ≤ d ∧
        (∀ j, (S j).Nonempty ∧ (∀ f ∈ R j, f ∈ B) ∧ (R j).card + ((S j).card - 1) ≤ e ∧
          ∀ i ∈ S j, ∀ u : U, (∀ f ∈ Q, f u = 0) → (∀ f ∈ R j, f u = 0) → M i u = 0) ∧
        ∀ x ∈ P, ∃ j, ∃ i ∈ S j, x ∉ bad i) := by
  classical
  intro X U Y Z W P bad M A B legal hPne
  constructor
  · -- (⇒) Two-batch algorithm → Cover
    rintro ⟨ask, next, out, hlegA, hlegB, hgood⟩
    let L₁X : X →ₗ[K] (Fin d → K) :=
      LinearMap.pi fun j => (ask j).comp (LinearMap.inl K X U)
    let L₁U : U →ₗ[K] (Fin d → K) :=
      LinearMap.pi fun j => (ask j).comp (LinearMap.inr K X U)
    have hL₁_split : ∀ (x : X) (u : U), (fun j => ask j (x, u)) = L₁X x + L₁U u := by
      intro x u; funext j
      have hpair : (x, u) = (x, (0 : U)) + ((0 : X), u) := by simp
      rw [hpair, map_add]; rfl
    obtain ⟨Q, hQ_A, hQ_card_top, hQ_ker_top⟩ :=
      exists_allowed_basis (K := K) (⊤ : Submodule K U) ask A hlegA
    let W₁ : Submodule K (Fin d → K) := LinearMap.range L₁U
    have hQ_card : Q.card = Module.finrank K W₁ := by
      have hrange : LinearMap.range (L₁U.domRestrict (⊤ : Submodule K U)) = W₁ := by
        ext y
        simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, W₁]
        constructor
        · rintro ⟨⟨u, _⟩, hu⟩; exact ⟨u, hu⟩
        · rintro ⟨u, hu⟩; exact ⟨⟨u, trivial⟩, hu⟩
      rw [← hrange]
      exact hQ_card_top
    have hQ_le_d : Q.card ≤ d := by
      rw [hQ_card]
      calc Module.finrank K W₁ ≤ Module.finrank K (Fin d → K) := Submodule.finrank_le W₁
        _ = d := Module.finrank_fin_fun K
    let V_Q : Submodule K U := LinearMap.ker L₁U
    have hmem_VQ : ∀ u : U, u ∈ V_Q ↔ ∀ f ∈ Q, f u = 0 := by
      intro u
      rw [LinearMap.mem_ker]
      exact (hQ_ker_top ⟨u, trivial⟩).symm
    obtain ⟨σ₁, hσ₁⟩ := exists_section_ext L₁U
    let r₁ : ℕ := d - Q.card
    have hfr_quot1 : Module.finrank K ((Fin d → K) ⧸ W₁) = r₁ := by
      have h := Submodule.finrank_quotient_add_finrank W₁
      rw [Module.finrank_fin_fun K, ← hQ_card] at h
      omega
    let e₁ : ((Fin d → K) ⧸ W₁) ≃ₗ[K] (Fin r₁ → K) :=
      LinearEquiv.ofFinrankEq _ _ (by rw [hfr_quot1, Module.finrank_fin_fun K])
    let Φ₁ : X →ₗ[K] (Fin r₁ → K) := e₁.toLinearMap.comp (W₁.mkQ.comp L₁X)
    -- For every reachable Batch-1 quotient value c ∈ Φ₁ '' P, build (R_c, S_c)
    have hbatch2 : ∀ c : Fin r₁ → K, c ∈ Φ₁ '' (P : Set X) →
        ∃ (R_c : Finset W) (S_c : Finset (Fin m)),
          S_c.Nonempty ∧ (∀ f ∈ R_c, f ∈ B) ∧ R_c.card + (S_c.card - 1) ≤ e ∧
          (∀ i ∈ S_c, ∀ u : U, (∀ f ∈ Q, f u = 0) → (∀ f ∈ R_c, f u = 0) → M i u = 0) ∧
          ∀ x ∈ P, Φ₁ x = c → ∃ i ∈ S_c, x ∉ bad i := by
      intro c hc
      obtain ⟨x_c, hx_cP, hΦ₁xc⟩ := hc
      let P_c : AffineSubspace K X := P ⊓ ⨅ b : Fin r₁, levelSet ((LinearMap.proj b).comp Φ₁) (c b)
      have hmem_Pc : ∀ x : X, x ∈ P_c ↔ x ∈ P ∧ Φ₁ x = c := by
        intro x
        simp only [P_c, AffineSubspace.mem_inf_iff, mem_iInf_aff, mem_levelSet,
          LinearMap.comp_apply, LinearMap.proj_apply]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, funext h2⟩, fun ⟨h1, h2⟩ => ⟨h1, fun b => congrFun h2 b⟩⟩
      have hx_c_Pc : x_c ∈ P_c := (hmem_Pc x_c).mpr ⟨hx_cP, hΦ₁xc⟩
      let z_c : Fin d → K := L₁X x_c
      let uFun : X → U := fun x => σ₁ (z_c - L₁X x)
      have hL₁_uFun : ∀ x ∈ P_c, ∀ v ∈ V_Q, (fun j => ask j (x, uFun x + v)) = z_c := by
        intro x hx v hv
        have hΦeq : Φ₁ x = Φ₁ x_c := ((hmem_Pc x).mp hx).2.trans hΦ₁xc.symm
        have hmkQ : W₁.mkQ (L₁X x) = W₁.mkQ (L₁X x_c) := e₁.injective hΦeq
        have hsubW₁ : z_c - L₁X x ∈ W₁ :=
          (Submodule.Quotient.eq W₁).mp hmkQ.symm
        rw [hL₁_split, map_add, hσ₁ _ hsubW₁, LinearMap.mem_ker.mp hv, add_zero]
        abel
      let L₂X : X →ₗ[K] (Fin e → K) :=
        LinearMap.pi fun j => (next z_c j).comp (LinearMap.inl K X U)
      let L₂U : U →ₗ[K] (Fin e → K) :=
        LinearMap.pi fun j => (next z_c j).comp (LinearMap.inr K X U)
      have hL₂_split : ∀ (x : X) (u : U), (fun j => next z_c j (x, u)) = L₂X x + L₂U u := by
        intro x u; funext j
        have hpair : (x, u) = (x, (0 : U)) + ((0 : X), u) := by simp
        rw [hpair, map_add]; rfl
      obtain ⟨R_c, hRc_B, hRc_card, hRc_ker⟩ :=
        exists_allowed_basis (K := K) V_Q (next z_c) B (hlegB z_c)
      let W₂ : Submodule K (Fin e → K) := LinearMap.range (L₂U.domRestrict V_Q)
      have hRc_card' : R_c.card = Module.finrank K W₂ := hRc_card
      have hRc_le_e : R_c.card ≤ e := by
        rw [hRc_card']
        calc Module.finrank K W₂ ≤ Module.finrank K (Fin e → K) := Submodule.finrank_le W₂
          _ = e := Module.finrank_fin_fun K
      let r₂ : ℕ := e - R_c.card
      have hfr_quot2 : Module.finrank K ((Fin e → K) ⧸ W₂) = r₂ := by
        have h := Submodule.finrank_quotient_add_finrank W₂
        rw [Module.finrank_fin_fun K, ← hRc_card'] at h
        omega
      let e₂ : ((Fin e → K) ⧸ W₂) ≃ₗ[K] (Fin r₂ → K) :=
        LinearEquiv.ofFinrankEq _ _ (by rw [hfr_quot2, Module.finrank_fin_fun K])
      let L₂_eff : X →ₗ[K] (Fin e → K) := L₂X - L₂U.comp (σ₁.comp L₁X)
      let b₂ : Fin e → K := L₂U (σ₁ z_c)
      have hL₂_uFun : ∀ (x : X) (v : U), (fun j => next z_c j (x, uFun x + v)) = L₂_eff x + b₂ + L₂U v := by
        intro x v
        rw [hL₂_split, map_add]
        simp only [uFun, map_sub, L₂_eff, b₂, LinearMap.sub_apply, LinearMap.comp_apply]
        abel
      let Φ₂ : X →ₗ[K] (Fin r₂ → K) := e₂.toLinearMap.comp (W₂.mkQ.comp L₂_eff)
      let wOf : (Fin r₂ → K) → (Fin e → K) := fun c' =>
        if h : ∃ x ∈ P_c, Φ₂ x = c' then L₂_eff (Classical.choose h) + b₂ else 0
      let iOf : (Fin r₂ → K) → Fin m := fun c' => (out z_c (wOf c')).1
      have hiOf_prop : ∀ c' ∈ Φ₂ '' (P_c : Set X),
          (∀ x ∈ P_c, Φ₂ x = c' → x ∉ bad (iOf c')) ∧
          (∀ u : U, (∀ f ∈ Q, f u = 0) → (∀ f ∈ R_c, f u = 0) → M (iOf c') u = 0) := by
        intro c' hc'
        have hex : ∃ x ∈ P_c, Φ₂ x = c' := hc'
        let x₀ := Classical.choose hex
        have hx₀ := Classical.choose_spec hex
        have hwOf : wOf c' = L₂_eff x₀ + b₂ := by
          dsimp only [wOf]; simp only [hex, ↓reduceDIte]; rfl
        have hhit : ∀ x ∈ P_c, Φ₂ x = c' →
            ∃ v_x : V_Q, ∀ v : U, (∀ f ∈ Q, f v = 0) → (∀ f ∈ R_c, f v = 0) →
              (fun j => ask j (x, uFun x + v_x.1 + v)) = z_c ∧
              (fun j => next z_c j (x, uFun x + v_x.1 + v)) = wOf c' := by
          intro x hx hΦ₂x
          have hmkQ : W₂.mkQ (L₂_eff x) = W₂.mkQ (L₂_eff x₀) :=
            e₂.injective (hΦ₂x.trans hx₀.2.symm)
          have hsubW₂ : L₂_eff x₀ - L₂_eff x ∈ W₂ :=
            (Submodule.Quotient.eq W₂).mp hmkQ.symm
          obtain ⟨v_x, hv_x⟩ := hsubW₂
          refine ⟨v_x, fun v hvQ hvR => ?_⟩
          have hv_memQ : v ∈ V_Q := (hmem_VQ v).mpr hvQ
          have hsumQ : v_x.1 + v ∈ V_Q := Submodule.add_mem V_Q v_x.2 hv_memQ
          constructor
          · rw [add_assoc]; exact hL₁_uFun x hx (v_x.1 + v) hsumQ
          · rw [add_assoc, hL₂_uFun, map_add]
            have hL₂v : L₂U v = 0 := (hRc_ker ⟨v, hv_memQ⟩).mp hvR
            have hvx_eq : L₂U v_x.1 = L₂_eff x₀ - L₂_eff x := hv_x
            rw [hvx_eq, hL₂v, add_zero, hwOf]
            abel
        constructor
        · intro x hx hΦ₂x
          obtain ⟨v_x, hv_x⟩ := hhit x hx hΦ₂x
          have ⟨h1, h2⟩ := hv_x 0 (fun _ _ => map_zero _) (fun _ _ => map_zero _)
          have hg := hgood x ((hmem_Pc x).mp hx).1 (uFun x + v_x.1 + 0)
          dsimp only at hg
          rw [h1, h2] at hg
          exact hg.1
        · intro u huQ huR
          obtain ⟨v_x, hv_x⟩ := hhit x₀ hx₀.1 hx₀.2
          have ⟨h10, h20⟩ := hv_x 0 (fun _ _ => map_zero _) (fun _ _ => map_zero _)
          have ⟨h1u, h2u⟩ := hv_x u huQ huR
          have hg0 := hgood x₀ ((hmem_Pc x₀).mp hx₀.1).1 (uFun x₀ + v_x.1 + 0)
          have hgu := hgood x₀ ((hmem_Pc x₀).mp hx₀.1).1 (uFun x₀ + v_x.1 + u)
          dsimp only at hg0 hgu
          rw [h10, h20] at hg0
          rw [h1u, h2u] at hgu
          have hMeq : M (iOf c') (uFun x₀ + v_x.1 + 0) = M (iOf c') (uFun x₀ + v_x.1 + u) :=
            hg0.2.symm.trans hgu.2
          rw [add_zero] at hMeq
          rw [map_add (M (iOf c')) (uFun x₀ + v_x.1) u] at hMeq
          exact (add_left_cancel (a := M (iOf c') (uFun x₀ + v_x.1))
            (by rw [add_zero]; exact hMeq)).symm
      obtain ⟨C₂, hC₂ne, hC₂card, hC₂mem, hC₂cov⟩ :=
        backward_sep r₂ P_c ⟨x_c, hx_c_Pc⟩ Φ₂ (fun c' => bad (iOf c'))
          (fun c' hc' x hx hΦ => (hiOf_prop c' hc').1 x hx hΦ)
      let S_c : Finset (Fin m) := C₂.image iOf
      have hSc_ne : S_c.Nonempty := hC₂ne.image iOf
      have hSc_card : S_c.card ≤ r₂ + 1 := le_trans Finset.card_image_le hC₂card
      refine ⟨R_c, S_c, hSc_ne, hRc_B, ?_, ?_, ?_⟩
      · have h1 : 1 ≤ S_c.card := Finset.Nonempty.card_pos hSc_ne
        omega
      · intro i hi u huQ huR
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hi
        exact (hiOf_prop c' (hC₂mem c' hc')).2 u huQ huR
      · intro x hxP hΦ₁x
        obtain ⟨c', hc', hxnc'⟩ := hC₂cov x ((hmem_Pc x).mpr ⟨hxP, hΦ₁x⟩)
        exact ⟨iOf c', Finset.mem_image_of_mem iOf hc', hxnc'⟩
    let R_of : (Fin r₁ → K) → Finset W := fun c =>
      if h : c ∈ Φ₁ '' (P : Set X) then (hbatch2 c h).choose else ∅
    let S_of : (Fin r₁ → K) → Finset (Fin m) := fun c =>
      if h : c ∈ Φ₁ '' (P : Set X) then (hbatch2 c h).choose_spec.choose else ∅
    have hRS_spec : ∀ c (h : c ∈ Φ₁ '' (P : Set X)),
        (S_of c).Nonempty ∧ (∀ f ∈ R_of c, f ∈ B) ∧ (R_of c).card + ((S_of c).card - 1) ≤ e ∧
        (∀ i ∈ S_of c, ∀ u : U, (∀ f ∈ Q, f u = 0) → (∀ f ∈ R_of c, f u = 0) → M i u = 0) ∧
        ∀ x ∈ P, Φ₁ x = c → ∃ i ∈ S_of c, x ∉ bad i := by
      intro c h
      simpa only [R_of, S_of, h, ↓reduceDIte] using (hbatch2 c h).choose_spec.choose_spec
    let H₁ : (Fin r₁ → K) → AffineSubspace K X := fun c =>
      ⨅ i ∈ S_of c, bad i
    have hH₁ : ∀ c ∈ Φ₁ '' (P : Set X), ∀ x ∈ P, Φ₁ x = c → x ∉ H₁ c := by
      intro c hc x hx hΦ₁x hxH
      obtain ⟨i, hi, hxni⟩ := (hRS_spec c hc).2.2.2.2 x hx hΦ₁x
      have hxbad : x ∈ bad i :=
        mem_iInf_aff.mp (mem_iInf_aff.mp hxH i) hi
      exact hxni hxbad
    obtain ⟨C₁, hC₁ne, hC₁card, hC₁mem, hC₁cov⟩ :=
      backward_sep r₁ P hPne Φ₁ H₁ hH₁
    let g := C₁.card
    let eC₁ : Fin g ≃ C₁ := (Fintype.equivFinOfCardEq (Fintype.card_coe C₁)).symm
    refine ⟨g, Q, fun j => S_of (eC₁ j).1, fun j => R_of (eC₁ j).1,
      Finset.Nonempty.card_pos hC₁ne, hQ_A, ?_, ?_, ?_⟩
    · have h1 : 1 ≤ g := Finset.Nonempty.card_pos hC₁ne
      omega
    · intro j
      have hc := hC₁mem (eC₁ j).1 (eC₁ j).2
      have hs := hRS_spec (eC₁ j).1 hc
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    · intro x hx
      obtain ⟨c, hc, hxnc⟩ := hC₁cov x hx
      refine ⟨eC₁.symm ⟨c, hc⟩, ?_⟩
      dsimp only
      have hce : (eC₁ (eC₁.symm ⟨c, hc⟩)).1 = c := congrArg Subtype.val (eC₁.apply_symm_apply ⟨c, hc⟩)
      rw [hce]
      by_contra hall
      push Not at hall
      apply hxnc
      exact mem_iInf_aff.mpr fun i => mem_iInf_aff.mpr fun hi => hall i hi
  · -- (⇐) Cover → Two-batch algorithm
    rintro ⟨g, Q, S, R, hg, hQ_A, hQd, hS_spec, hcov⟩
    let E : Fin g → AffineSubspace K X := fun j => ⨅ i ∈ S j, bad i
    have hcovE : ∀ x ∈ P, ∃ j : Fin g, x ∉ E j := by
      intro x hx
      obtain ⟨j, i, hi, hxni⟩ := hcov x hx
      refine ⟨j, fun hxE => hxni ?_⟩
      exact mem_iInf_aff.mp (mem_iInf_aff.mp hxE i) hi
    obtain ⟨ℓ₁, pick₁, hpick₁⟩ := forward_sep g hg P hPne E hcovE
    let eQ : Fin Q.card ≃ Q := (Fintype.equivFinOfCardEq (Fintype.card_coe Q)).symm
    let ask : Fin d → (Z →ₗ[K] K) := fun idx =>
      if h1 : idx.val < Q.card then
        (eQ ⟨idx.val, h1⟩).1.comp (LinearMap.snd K X U)
      else if h2 : idx.val - Q.card < g - 1 then
        (ℓ₁ ⟨idx.val - Q.card, h2⟩).comp (LinearMap.fst K X U)
      else 0
    have hlegA : ∀ idx : Fin d, legal A (ask idx) := by
      intro idx
      dsimp only [ask, legal]
      split_ifs with h1 h2
      · right
        have hcomp : ((eQ ⟨idx.val, h1⟩).1.comp (LinearMap.snd K X U)).comp
            (LinearMap.inr K X U) = (eQ ⟨idx.val, h1⟩).1 := by
          ext u; rfl
        rw [hcomp]
        exact hQ_A _ (eQ ⟨idx.val, h1⟩).2
      · left; rw [LinearMap.comp_assoc, LinearMap.fst_comp_inr, LinearMap.comp_zero]
      · left; exact LinearMap.ext fun u => by simp
    let y₁Of : (Fin d → K) → (Fin (g - 1) → K) := fun z b =>
      z ⟨Q.card + b.val, by omega⟩
    have hy₁Of : ∀ (x : X) (u : U),
        y₁Of (fun idx => ask idx (x, u)) = fun b => ℓ₁ b x := by
      intro x u; funext b
      dsimp only [y₁Of, ask]
      have h1 : ¬ (Q.card + b.val < Q.card) := by omega
      have h2 : Q.card + b.val - Q.card < g - 1 := by omega
      simp only [h1, h2, ↓reduceDIte, LinearMap.comp_apply]
      congr 1; congr 1; apply Fin.ext; simp
    have hqOf : ∀ (x : X) (u : U) (a : Fin Q.card),
        ask ⟨a.val, by omega⟩ (x, u) = (eQ a).1 u := by
      intro x u a
      dsimp only [ask]
      simp only [a.isLt, ↓reduceDIte]
      rfl
    let PzOf : (Fin d → K) → AffineSubspace K X := fun z =>
      P ⊓ ⨅ b : Fin (g - 1), levelSet (ℓ₁ b) (y₁Of z b)
    have hmem_Pz : ∀ z x, x ∈ PzOf z ↔ x ∈ P ∧ ∀ b, ℓ₁ b x = y₁Of z b := by
      intro z x
      simp only [PzOf, AffineSubspace.mem_inf_iff, mem_iInf_aff, mem_levelSet]
    -- Default element of Fin m (exists since 0 < g and (S 0).Nonempty)
    have hm_ne : Nonempty (Fin m) := by
      obtain ⟨i₀, _⟩ := (hS_spec ⟨0, hg⟩).1
      exact ⟨i₀⟩
    let i_def : Fin m := Classical.arbitrary (Fin m)
    -- For each z with PzOf z nonempty, construct Batch 2 queries + pick₂
    have hbatch2_build : ∀ z : Fin d → K, (PzOf z : Set X).Nonempty →
        let j := pick₁ (y₁Of z)
        let eS : Fin (S j).card ≃ S j := (Fintype.equivFinOfCardEq (Fintype.card_coe (S j))).symm
        ∃ (ℓ₂ : Fin ((S j).card - 1) → (X →ₗ[K] K))
          (pick₂ : (Fin ((S j).card - 1) → K) → Fin (S j).card),
          ∀ x ∈ PzOf z, x ∉ bad (eS (pick₂ (fun c => ℓ₂ c x))).1 := by
      intro z hPzne j eS
      have hSpos : 0 < (S j).card := Finset.Nonempty.card_pos (hS_spec j).1
      have hcov2 : ∀ x ∈ PzOf z, ∃ c : Fin (S j).card, x ∉ bad (eS c).1 := by
        intro x hx
        have ⟨hxP, hxℓ⟩ := (hmem_Pz z x).mp hx
        have hnotE : x ∉ E j := by
          have h1 := hpick₁ x hxP
          have h2 : (fun b => ℓ₁ b x) = y₁Of z := funext hxℓ
          rwa [h2] at h1
        by_contra hall
        push Not at hall
        apply hnotE
        refine mem_iInf_aff.mpr fun i => mem_iInf_aff.mpr fun hi => ?_
        have := hall (eS.symm ⟨i, hi⟩)
        simpa using this
      exact forward_sep (S j).card hSpos (PzOf z) hPzne (fun c => bad (eS c).1) hcov2
    let next : (Fin d → K) → Fin e → (Z →ₗ[K] K) := fun z idx =>
      if hPz : (PzOf z : Set X).Nonempty then
        let j := pick₁ (y₁Of z)
        let eR : Fin (R j).card ≃ R j := (Fintype.equivFinOfCardEq (Fintype.card_coe (R j))).symm
        let ℓ₂ := (hbatch2_build z hPz).choose
        if h1 : idx.val < (R j).card then
          (eR ⟨idx.val, h1⟩).1.comp (LinearMap.snd K X U)
        else if h2 : idx.val - (R j).card < (S j).card - 1 then
          (ℓ₂ ⟨idx.val - (R j).card, h2⟩).comp (LinearMap.fst K X U)
        else 0
      else 0
    have hlegB : ∀ z idx, legal B (next z idx) := by
      intro z idx
      dsimp only [next, legal]
      split_ifs with hPz h1 h2
      · right
        let j := pick₁ (y₁Of z)
        let eR : Fin (R j).card ≃ R j := (Fintype.equivFinOfCardEq (Fintype.card_coe (R j))).symm
        have hcomp : ((eR ⟨idx.val, h1⟩).1.comp (LinearMap.snd K X U)).comp
            (LinearMap.inr K X U) = (eR ⟨idx.val, h1⟩).1 := by
          ext u; rfl
        rw [hcomp]
        exact (hS_spec j).2.1 _ (eR ⟨idx.val, h1⟩).2
      · left; rw [LinearMap.comp_assoc, LinearMap.fst_comp_inr, LinearMap.comp_zero]
      · left; exact LinearMap.ext fun u => by simp
      · left; ext u; simp
    let out : (Fin d → K) → (Fin e → K) → Fin m × Y := fun z w =>
      if hPz : (PzOf z : Set X).Nonempty then
        let j := pick₁ (y₁Of z)
        let eS : Fin (S j).card ≃ S j := (Fintype.equivFinOfCardEq (Fintype.card_coe (S j))).symm
        let eR : Fin (R j).card ≃ R j := (Fintype.equivFinOfCardEq (Fintype.card_coe (R j))).symm
        let pick₂ := (hbatch2_build z hPz).choose_spec.choose
        let hRe : (R j).card + ((S j).card - 1) ≤ e := (hS_spec j).2.2.1
        let y₂ : Fin ((S j).card - 1) → K := fun c => w ⟨(R j).card + c.val, by omega⟩
        let i : Fin m := (eS (pick₂ y₂)).1
        let y : Y :=
          if hU : ∃ u₀ : U,
              (∀ a : Fin Q.card, (eQ a).1 u₀ = z ⟨a.val, by omega⟩) ∧
              (∀ b : Fin (R j).card, (eR b).1 u₀ = w ⟨b.val, by omega⟩) then
            M i (Classical.choose hU)
          else 0
        (i, y)
      else (i_def, 0)
    refine ⟨ask, next, out, hlegA, hlegB, fun x hxP u => ?_⟩
    let z : Fin d → K := fun idx => ask idx (x, u)
    let w : Fin e → K := fun idx => next z idx (x, u)
    have hxPz : x ∈ PzOf z :=
      (hmem_Pz z x).mpr ⟨hxP, fun b => (congrFun (hy₁Of x u) b).symm⟩
    have hPzne' : (PzOf z : Set X).Nonempty := ⟨x, hxPz⟩
    let j := pick₁ (y₁Of z)
    let eS : Fin (S j).card ≃ S j := (Fintype.equivFinOfCardEq (Fintype.card_coe (S j))).symm
    let eR : Fin (R j).card ≃ R j := (Fintype.equivFinOfCardEq (Fintype.card_coe (R j))).symm
    let ℓ₂ := (hbatch2_build z hPzne').choose
    let pick₂ := (hbatch2_build z hPzne').choose_spec.choose
    have hpick₂_spec : ∀ x' ∈ PzOf z, x' ∉ bad (eS (pick₂ (fun c => ℓ₂ c x'))).1 :=
      (hbatch2_build z hPzne').choose_spec.choose_spec
    have hRe : (R j).card + ((S j).card - 1) ≤ e := (hS_spec j).2.2.1
    have hy₂_eq : (fun c : Fin ((S j).card - 1) => w ⟨(R j).card + c.val, by omega⟩) =
        fun c => ℓ₂ c x := by
      funext c
      have h1 : ¬ ((R (pick₁ (y₁Of z))).card + c.val < (R (pick₁ (y₁Of z))).card) := by omega
      have h2 : (R (pick₁ (y₁Of z))).card + c.val - (R (pick₁ (y₁Of z))).card <
          (S (pick₁ (y₁Of z))).card - 1 := by simp [j]
      dsimp only [w, next, j]
      simp only [hPzne', h1, h2, ↓reduceDIte, LinearMap.comp_apply]
      change ℓ₂ ⟨(R j).card + c.val - (R j).card, h2⟩ x = ℓ₂ c x
      congr 1; congr 1; apply Fin.ext; simp
    have hrOf : ∀ b : Fin (R j).card, w ⟨b.val, by omega⟩ = (eR b).1 u := by
      intro b
      have hb : b.val < (R (pick₁ (y₁Of z))).card := b.isLt
      dsimp only [w, next, j]
      simp only [hPzne', hb, ↓reduceDIte]
      rfl
    have hexU : ∃ u₀ : U,
        (∀ a : Fin Q.card, (eQ a).1 u₀ = z ⟨a.val, by omega⟩) ∧
        (∀ b : Fin (R j).card, (eR b).1 u₀ = w ⟨b.val, by omega⟩) :=
      ⟨u, fun a => (hqOf x u a).symm, fun b => (hrOf b).symm⟩
    have hout1 : (out z w).1 = (eS (pick₂ (fun c => ℓ₂ c x))).1 := by
      dsimp only [out]
      simp only [hPzne', ↓reduceDIte]
      exact congrArg (fun y => (eS (pick₂ y)).1) hy₂_eq
    have hout2 : (out z w).2 = M (eS (pick₂ (fun c => ℓ₂ c x))).1 (Classical.choose hexU) := by
      dsimp only [out]
      simp only [hPzne', ↓reduceDIte]
      change (if hU : ∃ u₀ : U,
          (∀ a : Fin Q.card, (eQ a).1 u₀ = z ⟨a.val, by omega⟩) ∧
          (∀ b : Fin (R j).card, (eR b).1 u₀ = w ⟨b.val, by omega⟩) then
        M (eS (pick₂ (fun c : Fin ((S j).card - 1) => w ⟨(R j).card + c.val, by omega⟩))).1
          (Classical.choose hU)
        else 0) = _
      simp only [hexU, ↓reduceDIte, hy₂_eq]
    change x ∉ bad (out z w).1 ∧ (out z w).2 = M (out z w).1 u
    rw [hout1, hout2]
    refine ⟨hpick₂_spec x hxPz, ?_⟩
    let u₀ := Classical.choose hexU
    have hu₀ := Classical.choose_spec hexU
    have hdiffQ : ∀ f ∈ Q, f (u₀ - u) = 0 := by
      intro f hf
      rw [map_sub, sub_eq_zero]
      have h1 := hu₀.1 (eQ.symm ⟨f, hf⟩)
      have h2 := hqOf x u (eQ.symm ⟨f, hf⟩)
      have h3 : (eQ (eQ.symm ⟨f, hf⟩)).1 = f := congrArg Subtype.val (eQ.apply_symm_apply ⟨f, hf⟩)
      rw [← h3]; exact h1.trans h2
    have hdiffR : ∀ f ∈ R j, f (u₀ - u) = 0 := by
      intro f hf
      rw [map_sub, sub_eq_zero]
      have h1 := hu₀.2 (eR.symm ⟨f, hf⟩)
      have h2 := hrOf (eR.symm ⟨f, hf⟩)
      have h3 : (eR (eR.symm ⟨f, hf⟩)).1 = f := congrArg Subtype.val (eR.apply_symm_apply ⟨f, hf⟩)
      rw [← h3]; exact h1.trans h2
    have hMz := (hS_spec j).2.2.2 _ (eS (pick₂ (fun c => ℓ₂ c x))).2 (u₀ - u) hdiffQ hdiffR
    rw [map_sub, sub_eq_zero] at hMz
    exact hMz

end PEqualNP.Outside.L_pcx_432_aux

theorem PEqualNP.Outside.L_pcx_432 :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n k t m d e : ℕ),
      let X := Fin n → K
      let U := Fin k → K
      let Y := Fin t → K
      let Z := X × U
      let W := U →ₗ[K] K
      ∀ (P : AffineSubspace K X) (bad : Fin m → AffineSubspace K X)
        (M : Fin m → U →ₗ[K] Y) (A B : Set W),
        let legal := fun (S : Set W) (f : Z →ₗ[K] K) =>
          f.comp (LinearMap.inr K X U) = 0 ∨ f.comp (LinearMap.inr K X U) ∈ S
        (∃ x : X, x ∈ P) →
        ((∃ (ask : Fin d → Z →ₗ[K] K) (next : (Fin d → K) → Fin e → Z →ₗ[K] K)
            (out : (Fin d → K) → (Fin e → K) → Fin m × Y),
          (∀ j, legal A (ask j)) ∧ (∀ z j, legal B (next z j)) ∧
          ∀ x ∈ P, ∀ u : U,
            let z := fun j => ask j (x,u)
            let a := out z (fun j => next z j (x,u))
            x ∉ bad a.1 ∧ a.2 = M a.1 u) ↔
        ∃ (g : ℕ) (Q : Finset W) (S : Fin g → Finset (Fin m)) (R : Fin g → Finset W),
          0 < g ∧ (∀ f ∈ Q, f ∈ A) ∧ Q.card + (g-1) ≤ d ∧
          (∀ j, (S j).Nonempty ∧ (∀ f ∈ R j, f ∈ B) ∧ (R j).card + ((S j).card-1) ≤ e ∧
            ∀ i ∈ S j, ∀ u : U, (∀ f ∈ Q, f u = 0) → (∀ f ∈ R j, f u = 0) → M i u = 0) ∧
          ∀ x ∈ P, ∃ j, ∃ i ∈ S j, x ∉ bad i) :=
  PEqualNP.Outside.L_pcx_432_aux.main_proof
