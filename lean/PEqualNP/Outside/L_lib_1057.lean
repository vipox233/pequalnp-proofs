import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1057

open Finset

lemma rank_add_le' {ι κ : Type} [Fintype κ] (A B : Matrix ι κ (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_sum_le {ι κ α : Type} [Fintype κ] (s : Finset α) (f : α → Matrix ι κ (ZMod 2)) :
    (∑ j ∈ s, f j).rank ≤ ∑ j ∈ s, (f j).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' _ _).trans (by omega)

lemma exists_li_rows {p : ℕ} {N : Type} [Fintype N] (A : Matrix (Fin p) N (ZMod 2)) :
    ∃ g : Fin A.rank → Fin p, LinearIndependent (ZMod 2) (fun k => A.row (g k)) := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod 2) (Set.range A.row)
  have hfin : b.Finite := (Set.finite_range A.row).subset hbs
  let _ : Fintype b := hfin.fintype
  have hcard : Fintype.card b = A.rank := by
    rw [A.rank_eq_finrank_span_row, ← hspan, linearIndependent_iff_card_eq_finrank_span.mp hli,
      Subtype.range_coe]
    rfl
  let eq : Fin A.rank ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ v : b, ∃ r, A.row r = (v : N → ZMod 2) := fun v => hbs v.2
  refine ⟨fun k => (hpre (eq k)).choose, ?_⟩
  have h1 : (fun k => A.row (hpre (eq k)).choose) = (Subtype.val : b → N → ZMod 2) ∘ eq := by
    funext k
    exact (hpre (eq k)).choose_spec
  rw [h1]
  exact hli.comp _ eq.injective

end PEqualNP.Outside.L_lib_1057

open PEqualNP.Outside.L_lib_1057 Finset in
theorem PEqualNP.Outside.L_lib_1057 :
    let F := ZMod 2
    ∀ (l t : ℕ) (m n : Fin l → ℕ),
      let I := Σ i : Fin l, Fin (m i)
      let J := Σ i : Fin l, Fin (n i)
      ∀ (D : (i : Fin l) → Matrix (Fin (m i)) (Fin (n i)) F)
        (R : Fin t → Matrix I J F),
        (∑ j, R j) = Matrix.blockDiagonal' D →
        (∑ j, (R j).rank) = ∑ i, (D i).rank →
        ∃ e : (Σ j : Fin t, Fin (R j).rank) ≃ (Σ i : Fin l, Fin (D i).rank),
          ∀ x, ∃ (r : Fin (m (e x).1)) (y : J), R x.1 ⟨(e x).1,r⟩ y ≠ 0 := by
  intro F l t m n I J D R hsum hrank
  classical
  have hg : ∀ i, ∃ g : Fin (D i).rank → Fin (m i),
      LinearIndependent (ZMod 2) (fun k => (D i).row (g k)) := fun i => exists_li_rows (D i)
  choose g hg using hg
  let w : (Σ i : Fin l, Fin (D i).rank) → J → ZMod 2 :=
    fun x => (Matrix.blockDiagonal' D).row ⟨x.1, g x.1 x.2⟩
  have hw : LinearIndependent (ZMod 2) w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc x
    obtain ⟨i0, k0⟩ := x
    have hcol : ∀ col : Fin (n i0),
        ∑ k, c ⟨i0, k⟩ • (D i0).row (g i0 k) col = 0 := by
      intro col
      have := congrFun hc ⟨i0, col⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sigma, Pi.zero_apply] at this
      rw [Finset.sum_eq_single i0] at this
      · simpa [w, Matrix.row, Matrix.blockDiagonal'_apply_eq] using this
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro k _
        simp [w, Matrix.row, Matrix.blockDiagonal'_apply_ne D _ _ hi]
      · simp
    have h2 := Fintype.linearIndependent_iff.mp (hg i0) (fun k => c ⟨i0, k⟩) (by
      funext col
      simpa [Finset.sum_apply] using hcol col)
    exact h2 k0
  let tt : (Σ i : Fin l, Fin (D i).rank) → Finset (Σ j : Fin t, Fin (R j).rank) :=
    fun x => univ.filter (fun z => ∃ (r : Fin (m x.1)) (y : J), R z.1 ⟨x.1, r⟩ y ≠ 0)
  have hall : ∀ s : Finset (Σ i : Fin l, Fin (D i).rank), s.card ≤ (s.biUnion tt).card := by
    intro s
    let Js : Finset (Fin t) :=
      univ.filter (fun j => ∃ x ∈ s, ∃ (r : Fin (m x.1)) (y : J), R j ⟨x.1, r⟩ y ≠ 0)
    have hbu : s.biUnion tt = Js.sigma (fun _ => univ) := by
      ext z
      simp only [mem_biUnion, tt, Js, mem_filter, mem_univ, mem_sigma, true_and, and_true]
    have hcard : (s.biUnion tt).card = ∑ j ∈ Js, (R j).rank := by
      rw [hbu, card_sigma]
      simp
    rw [hcard]
    let ρ : s → I := fun x => ⟨x.1.1, g x.1.1 x.1.2⟩
    have hli : LinearIndependent (ZMod 2) ((Matrix.blockDiagonal' D).submatrix ρ id).row :=
      hw.comp (Subtype.val : s → _) Subtype.val_injective
    have hr := hli.rank_matrix
    rw [Fintype.card_coe] at hr
    have hsub : (Matrix.blockDiagonal' D).submatrix ρ id = ∑ j ∈ Js, (R j).submatrix ρ id := by
      have hfil : ∑ j ∈ Js, (R j).submatrix ρ id = ∑ j, (R j).submatrix ρ id := by
        refine Finset.sum_filter_of_ne (fun j _ hj => ?_)
        by_contra hcon
        apply hj
        ext a b
        by_contra hab
        exact hcon ⟨a.1, a.2, g a.1.1 a.1.2, b, by simpa [ρ] using hab⟩
      rw [hfil, ← hsum]
      ext a b
      simp [Matrix.sum_apply]
    rw [← hr, hsub]
    refine (rank_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun j _ => Matrix.rank_submatrix_le _ _ _)
  obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective tt).mp hall
  have hc : Fintype.card (Σ i : Fin l, Fin (D i).rank) =
      Fintype.card (Σ j : Fin t, Fin (R j).rank) := by
    simp [Fintype.card_sigma, hrank]
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩
  refine ⟨(Equiv.ofBijective f hb).symm, fun x => ?_⟩
  have h1 := hft ((Equiv.ofBijective f hb).symm x)
  have h2 : f ((Equiv.ofBijective f hb).symm x) = x := (Equiv.ofBijective f hb).apply_symm_apply x
  rw [h2] at h1
  simpa [tt] using h1
