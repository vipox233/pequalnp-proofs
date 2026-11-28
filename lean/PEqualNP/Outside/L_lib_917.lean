import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_917

open Module

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

theorem main (k m r j : ℕ) (A : Fin m → (Fin k → ZMod 2))
    (W : Submodule (ZMod 2)
      ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2)))))
    (hW : 2*m+r+j ≤ finrank (ZMod 2) W) :
    ∃ B : (Fin j → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2), Function.Injective B ∧
      (∀ a, ∃ w ∈ W, w.1 = B a) ∧
      ∀ b c : Fin m → ZMod 2, ∃ w ∈ W, w.1 = 0 ∧
        ∀ i : Fin m, (∃ a, dotProduct (A i) (B a) ≠ 0) → w.2.1 i = b i ∧ w.2.2.1 i = c i := by
  classical
  let X := (Fin m → ZMod 2) × ((Fin m → ZMod 2) × (Fin r → ZMod 2))
  let g : W →ₗ[ZMod 2] (Fin k → ZMod 2) := (LinearMap.fst _ _ _).comp W.subtype
  let P := LinearMap.range g
  let W0 : Submodule (ZMod 2) X := W.comap (LinearMap.inr (ZMod 2) (Fin k → ZMod 2) X)
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  let ι : LinearMap.ker g →ₗ[ZMod 2] W0 :=
    { toFun := fun w => ⟨w.1.1.2, by
        have h1 : w.1.1.1 = 0 := LinearMap.mem_ker.mp w.2
        show ((0 : Fin k → ZMod 2), w.1.1.2) ∈ W
        have : ((0 : Fin k → ZMod 2), w.1.1.2) = w.1.1 := Prod.ext h1.symm rfl
        rw [this]; exact w.1.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ι := by
    intro x y h
    have h2 : x.1.1.2 = y.1.1.2 := congrArg Subtype.val h
    have hx : x.1.1.1 = 0 := LinearMap.mem_ker.mp x.2
    have hy : y.1.1.1 = 0 := LinearMap.mem_ker.mp y.2
    exact Subtype.ext (Subtype.ext (Prod.ext (hx.trans hy.symm) h2))
  have hW0 := LinearMap.finrank_le_finrank_of_injective hinj
  let bX : Basis (Fin m ⊕ (Fin m ⊕ Fin r)) (ZMod 2) X :=
    (Pi.basisFun _ _).prod ((Pi.basisFun _ _).prod (Pi.basisFun _ _))
  obtain ⟨N, hN, hNx⟩ := pivots bX W0
  have hq := W0.finrank_quotient_add_finrank
  have hX : finrank (ZMod 2) X = m + (m + r) := by simp [X]
  let T : Finset (Fin m) :=
    Finset.univ.filter (fun i => Sum.inl i ∈ N ∨ Sum.inr (Sum.inl i) ∈ N)
  have hT : T.card ≤ N.card := by
    let f : Fin m → Fin m ⊕ (Fin m ⊕ Fin r) :=
      fun i => if Sum.inl i ∈ N then Sum.inl i else Sum.inr (Sum.inl i)
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      simp only [f]
      split_ifs with h
      · exact h
      · exact hx'.resolve_left h
    · intro x _ y _ hxy
      simp only [f] at hxy
      split_ifs at hxy <;> simp_all
  let φ : (Fin k → ZMod 2) →ₗ[ZMod 2] (T → ZMod 2) :=
    Matrix.mulVecLin (Matrix.of fun (i : T) (s : Fin k) => A i.1 s)
  have hKmem : ∀ s ∈ LinearMap.ker φ, ∀ i ∈ T, dotProduct (A i) s = 0 := by
    intro s hs i hi
    have := congrFun (LinearMap.mem_ker.mp hs) ⟨i, hi⟩
    simpa [φ, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this
  have hK := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : finrank (ZMod 2) (LinearMap.range φ) ≤ T.card := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have hS : finrank (ZMod 2) (Fin k → ZMod 2) = k := Module.finrank_fin_fun _
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq P (LinearMap.ker φ)
  have hsupl := Submodule.finrank_le (P ⊔ LinearMap.ker φ)
  have a1 : finrank (ZMod 2) (LinearMap.ker g) ≤ finrank (ZMod 2) W0 := hW0
  have a2 : finrank (ZMod 2) (X ⧸ W0) + finrank (ZMod 2) W0 = m + (m + r) := hq.trans hX
  have a3 : finrank (ZMod 2) P + finrank (ZMod 2) (LinearMap.ker g) = finrank (ZMod 2) W := hrn
  have a4 : finrank (ZMod 2) (LinearMap.range φ) + finrank (ZMod 2) (LinearMap.ker φ) = k :=
    hK.trans hS
  have a5 : finrank (ZMod 2) ↥(P ⊔ LinearMap.ker φ) ≤ k := hsupl.trans hS.le
  have a6 : finrank (ZMod 2) ↥(P ⊔ LinearMap.ker φ) + finrank (ZMod 2) ↥(P ⊓ LinearMap.ker φ)
      = finrank (ZMod 2) P + finrank (ZMod 2) (LinearMap.ker φ) := hsup
  have a7 : N.card ≤ finrank (ZMod 2) (X ⧸ W0) := hN
  have hR : j ≤ finrank (ZMod 2) ↥(P ⊓ LinearMap.ker φ) := by
    omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hR
  have hf' : LinearIndependent (ZMod 2) (fun t => (f t : Fin k → ZMod 2)) :=
    hf.map' (P ⊓ LinearMap.ker φ).subtype (Submodule.ker_subtype _)
  let B : (Fin j → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun a => ∑ t, a t • (f t : Fin k → ZMod 2)
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul] }
  have hBR : ∀ a, B a ∈ P ⊓ LinearMap.ker φ := fun a => show ∑ t, a t • _ ∈ _ from
    Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (f t).2)
  refine ⟨B, ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero B).mpr ?_
    intro a ha
    funext t
    exact Fintype.linearIndependent_iff.mp hf' a ha t
  · intro a
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_inf.mp (hBR a)).1
    exact ⟨w.1, w.2, hw⟩
  · intro b c
    obtain ⟨u, hu, hu'⟩ := hNx ((b, c, 0) : X)
    refine ⟨(0, u), hu, rfl, ?_⟩
    rintro i ⟨a, ha⟩
    have hiT : i ∉ T := fun hi => ha (hKmem (B a) (Submodule.mem_inf.mp (hBR a)).2 i hi)
    have h1 : (Sum.inl i : Fin m ⊕ (Fin m ⊕ Fin r)) ∉ N := fun h => hiT (by simp [T, h])
    have h2 : (Sum.inr (Sum.inl i) : Fin m ⊕ (Fin m ⊕ Fin r)) ∉ N :=
      fun h => hiT (by simp [T, h])
    have e1 := hu' _ h1
    have e2 := hu' _ h2
    simp only [bX] at e1 e2
    exact ⟨(sub_eq_zero.mp e1).symm, (sub_eq_zero.mp e2).symm⟩

end PEqualNP.Outside.L_lib_917

open PEqualNP.Outside.L_lib_917 in
theorem PEqualNP.Outside.L_lib_917 : ∀ (k m r j : ℕ),
  let F := ZMod 2
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let V := S × (D × (D × Z))
  let J := Fin j → F
  let base := 2*m+r
  ∀ (A : Fin m → S) (W : Submodule F V), base+j ≤ Module.finrank F W →
    ∃ B : J →ₗ[F] S, Function.Injective B ∧
      (∀ a : J, ∃ w ∈ W, w.1 = B a) ∧
      ∀ b c : D, ∃ w ∈ W, w.1 = 0 ∧
        ∀ i : Fin m, (∃ a : J, dotProduct (A i) (B a) ≠ 0) →
          w.2.1 i = b i ∧ w.2.2.1 i = c i := by
  intro k m r j F S D Z V J base A W hW
  exact main k m r j A W hW
