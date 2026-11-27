import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_772 : ∀ (F : Type) [Field F] (a b c d : ℕ) (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin c) (Fin d) F),
  (Matrix.fromBlocks A (0 : Matrix (Fin a) (Fin d) F) (0 : Matrix (Fin c) (Fin b) F) B).rank =
    A.rank + B.rank := by
  intro F _ a b c d A B
  let e1 := LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin c) F F
  let e2 := LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin d) F F
  have key : (Matrix.fromBlocks A (0 : Matrix (Fin a) (Fin d) F) (0 : Matrix (Fin c) (Fin b) F) B).mulVecLin
      = (e1.symm.toLinearMap.comp (LinearMap.prodMap A.mulVecLin B.mulVecLin)).comp e2.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext i
    rcases i with i | i <;> simp [e1, e2, Matrix.fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow] <;> rfl
  unfold Matrix.rank
  rw [key, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e2), LinearMap.range_comp,
    LinearEquiv.finrank_map_eq, LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq,
    Module.finrank_prod]
