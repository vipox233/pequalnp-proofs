import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_989

open Matrix

variable {K : Type} [Field K]

theorem memRow {k : ℕ} {ι : Type} [Fintype ι] (M : Matrix (Fin k) ι K) (v : ι → K) :
    v ∈ Submodule.span K (Set.range M.row) ↔ ∃ y, y ᵥ* M = v := by
  rw [← range_vecMulLinear]
  simp [LinearMap.mem_range]

theorem rowGen {k : ℕ} {ι : Type} [Fintype ι] (N : Matrix (Fin (k+1)) ι K) :
    Submodule.span K (Set.range N.row) =
      Submodule.span K (insert (N 0) (Set.range (N.submatrix Fin.succ id).row)) := by
  rw [Fin.range_fin_succ N.row]
  rfl

theorem rowIn {k : ℕ} {ι : Type} [Fintype ι] (N : Matrix (Fin (k+1)) ι K)
    (hy : ∃ y, y ᵥ* N.submatrix Fin.succ id = N 0) :
    N.rank = (N.submatrix Fin.succ id).rank := by
  rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row, rowGen,
    Submodule.span_insert_eq_span ((memRow _ _).2 hy)]

theorem rowOut {k : ℕ} {ι : Type} [Fintype ι] (N : Matrix (Fin (k+1)) ι K)
    (hy : ¬ ∃ y, y ᵥ* N.submatrix Fin.succ id = N 0) :
    N.rank = (N.submatrix Fin.succ id).rank + 1 := by
  rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row, rowGen, Submodule.span_insert]
  have hv : N 0 ∉ Submodule.span K (Set.range (N.submatrix Fin.succ id).row) :=
    fun h => hy ((memRow _ _).1 h)
  have hne : N 0 ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
  have hd := (Submodule.disjoint_span_singleton' (s := Submodule.span K
    (Set.range (N.submatrix Fin.succ id).row)) hne).2 hv
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ N 0)
    (Submodule.span K (Set.range (N.submatrix Fin.succ id).row))
  rw [inf_comm, hd.eq_bot, finrank_bot, finrank_span_singleton hne] at h1
  omega

theorem colIn {k : ℕ} {ι : Type} [Fintype ι] (N : Matrix ι (Fin (k+1)) K)
    (hz : ∃ z, N.submatrix id Fin.succ *ᵥ z = fun i => N i 0) :
    N.rank = (N.submatrix id Fin.succ).rank := by
  rw [← rank_transpose N, ← rank_transpose (N.submatrix id Fin.succ)]
  apply rowIn Nᵀ
  obtain ⟨z, hz⟩ := hz
  exact ⟨z, (Matrix.vecMul_transpose (N.submatrix id Fin.succ) z).trans hz⟩

theorem colOut {k : ℕ} {ι : Type} [Fintype ι] (N : Matrix ι (Fin (k+1)) K)
    (hz : ¬ ∃ z, N.submatrix id Fin.succ *ᵥ z = fun i => N i 0) :
    N.rank = (N.submatrix id Fin.succ).rank + 1 := by
  rw [← rank_transpose N, ← rank_transpose (N.submatrix id Fin.succ)]
  apply rowOut Nᵀ
  rintro ⟨z, hz'⟩
  exact hz ⟨z, by rw [← Matrix.vecMul_transpose]; exact hz'⟩

theorem ginv {p h : ℕ} (P : Matrix (Fin p) (Fin h) K) :
    ∃ W : Matrix (Fin h) (Fin p) K, P * W * P = P ∧ W.rank ≤ P.rank := by
  let f := Matrix.toLin' P
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  refine ⟨LinearMap.toMatrix' (g ∘ₗ π), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    have e1 : π (f v) = f.rangeRestrict v := by
      have := congrArg (fun F => F (f.rangeRestrict v)) hπ
      simpa using this
    have e2 : f (g (f.rangeRestrict v)) = f v := by
      have := congrArg (fun F => (F (f.rangeRestrict v) : Fin p → K)) hg
      simpa using this
    simp only [LinearMap.comp_apply]
    change f (g (π (f v))) = f v
    rw [e1, e2]
  · have h1 : (LinearMap.toMatrix' (g ∘ₗ π)).rank ≤ Module.finrank K (LinearMap.range f) := by
      rw [Matrix.rank, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
      exact (Submodule.finrank_mono (LinearMap.range_comp_le_range π g)).trans
        (LinearMap.finrank_range_le g)
    have h2 : P.rank = Module.finrank K (LinearMap.range f) := by
      rw [Matrix.rank, ← Matrix.toLin'_apply']
    exact h2 ▸ h1

theorem keyE {p h : ℕ} (P : Matrix (Fin p) (Fin h) K) (W : Matrix (Fin h) (Fin p) K)
    (hW : P * W * P = P) (y : Fin p → K) (z : Fin h → K) :
    (y ᵥ* P) ⬝ᵥ (W *ᵥ (P *ᵥ z)) = (y ᵥ* P) ⬝ᵥ z := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hW, Matrix.dotProduct_mulVec]

theorem border {p h : ℕ} (N : Matrix (Fin (p+1)) (Fin (h+1)) K) (W : Matrix (Fin h) (Fin p) K)
    (hW : N.submatrix Fin.succ Fin.succ * W * N.submatrix Fin.succ Fin.succ =
      N.submatrix Fin.succ Fin.succ)
    (e : K) (he : e = (fun k => N 0 k.succ) ⬝ᵥ (W *ᵥ fun l => N l.succ 0)) :
    N.rank + (N.submatrix Fin.succ Fin.succ).rank =
      (N.submatrix id Fin.succ).rank + (N.submatrix Fin.succ id).rank +
      (@ite ℕ ((N.submatrix id Fin.succ).rank = (N.submatrix Fin.succ Fin.succ).rank ∧
        (N.submatrix Fin.succ id).rank = (N.submatrix Fin.succ Fin.succ).rank ∧ N 0 0 ≠ e)
        (Classical.propDecidable _) 1 0) := by
  by_cases hr : ∃ y, y ᵥ* N.submatrix Fin.succ Fin.succ = fun k => N 0 k.succ
  · have ha : (N.submatrix id Fin.succ).rank = (N.submatrix Fin.succ Fin.succ).rank :=
      rowIn (N.submatrix id Fin.succ) hr
    by_cases hc : ∃ z, N.submatrix Fin.succ Fin.succ *ᵥ z = fun l => N l.succ 0
    · have hb : (N.submatrix Fin.succ id).rank = (N.submatrix Fin.succ Fin.succ).rank :=
        colIn (N.submatrix Fin.succ id) hc
      obtain ⟨y, hy⟩ := hr
      obtain ⟨z, hz⟩ := hc
      have hE : e = (fun k => N 0 k.succ) ⬝ᵥ z := by
        rw [he, ← hy, ← hz, keyE _ W hW]
      by_cases hx : N 0 0 = e
      · have hN : N.rank = (N.submatrix Fin.succ id).rank := by
          apply rowIn
          refine ⟨y, funext fun t => ?_⟩
          refine Fin.cases ?_ (fun k => ?_) t
          · change y ⬝ᵥ (fun l => N l.succ 0) = N 0 0
            rw [hx, hE, ← hz, Matrix.dotProduct_mulVec, hy]
          · exact congrFun hy k
        rw [if_neg (by tauto)]
        omega
      · have hN : N.rank = (N.submatrix Fin.succ id).rank + 1 := by
          apply rowOut
          rintro ⟨y', hy'⟩
          apply hx
          have hs : y' ᵥ* N.submatrix Fin.succ Fin.succ = fun k => N 0 k.succ :=
            funext fun k => congrFun hy' k.succ
          have h0 : y' ⬝ᵥ (fun l => N l.succ 0) = N 0 0 := congrFun hy' 0
          rw [← h0, hE, ← hz, Matrix.dotProduct_mulVec, hs]
        rw [if_pos ⟨ha, hb, hx⟩]
        omega
    · have hb : (N.submatrix Fin.succ id).rank = (N.submatrix Fin.succ Fin.succ).rank + 1 :=
        colOut (N.submatrix Fin.succ id) hc
      have hN : N.rank = (N.submatrix id Fin.succ).rank + 1 := by
        apply colOut
        rintro ⟨z', hz'⟩
        exact hc ⟨z', funext fun l => congrFun hz' l.succ⟩
      rw [if_neg (by omega)]
      omega
  · have ha : (N.submatrix id Fin.succ).rank = (N.submatrix Fin.succ Fin.succ).rank + 1 :=
      rowOut (N.submatrix id Fin.succ) hr
    have hN : N.rank = (N.submatrix Fin.succ id).rank + 1 := by
      apply rowOut
      rintro ⟨y', hy'⟩
      exact hr ⟨y', funext fun k => congrFun hy' k.succ⟩
    rw [if_neg (by omega)]
    omega

end PEqualNP.Outside.L_lib_989

open PEqualNP.Outside.L_lib_989 Matrix in
theorem PEqualNP.Outside.L_lib_989 : ∀ (K : Type) [Field K] (n m p h : ℕ) (A : Matrix (Fin n) (Fin m) K)
  (rows : Fin p → Fin n) (cols : Fin h → Fin m),
  let P := A.submatrix rows cols
  let q := Matrix.rank P
  ∃ W : Matrix (Fin h) (Fin p) K,
    let B := (A.submatrix id cols) * W * (A.submatrix rows id)
    Matrix.rank B = q ∧ B.submatrix rows cols = P ∧
    ∀ (i : Fin n) (j : Fin m),
      let R : Fin (p+1) → Fin n := Fin.cases i rows
      let C : Fin (h+1) → Fin m := Fin.cases j cols
      let a := Matrix.rank (A.submatrix R cols)
      let b := Matrix.rank (A.submatrix rows C)
      Matrix.rank (A.submatrix R C) + q = a+b +
        (@ite ℕ (a=q ∧ b=q ∧ A i j ≠ B i j) (Classical.propDecidable _) 1 0) := by
  intro K _ n m p h A rows cols P q
  obtain ⟨W, hW, hWr⟩ := ginv P
  refine ⟨W, ?_⟩
  intro B
  have hsub : B.submatrix rows cols = P := by
    have : B.submatrix rows cols = P * W * P := by
      ext a b
      simp [B, P, Matrix.mul_apply]
    rw [this, hW]
  refine ⟨?_, hsub, ?_⟩
  · apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hWr)
    · have := Matrix.rank_submatrix_le B rows cols
      rw [hsub] at this
      exact this
  · intro i j R C a b
    have hBij : B i j = (fun k => A i (cols k)) ⬝ᵥ (W *ᵥ fun l => A (rows l) j) := by
      simp only [B, Matrix.mul_apply, dotProduct, mulVec, Matrix.submatrix_apply, id,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    exact border (A.submatrix R C) W hW (B i j) hBij
