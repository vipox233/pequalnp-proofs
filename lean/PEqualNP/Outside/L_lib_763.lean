import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic

theorem PEqualNP.Outside.L_lib_763 : (∀ (F : Type) [Field F] (a b c d : ℕ) (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin c) (Fin d) F),
  let K : Matrix (Fin a × Fin c) (Fin b × Fin d) F := fun p q => A p.1 q.1 * B p.2 q.2
  K.rank = A.rank * B.rank) := by
  classical
  intro F _ a b c d A B
  change (Matrix.kroneckerMap (· * ·) A B).rank = A.rank * B.rank
  rw [Matrix.rank_eq_finrank_range_toLin (Matrix.kroneckerMap (· * ·) A B)
    ((Pi.basisFun F (Fin a)).tensorProduct (Pi.basisFun F (Fin c)))
    ((Pi.basisFun F (Fin b)).tensorProduct (Pi.basisFun F (Fin d))),
    Matrix.toLin_kronecker]
  rw [TensorProduct.range_map, ← TensorProduct.range_mapIncl]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _)]
  rw [Module.finrank_tensorProduct]
  rw [← Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun F (Fin a))
    (Pi.basisFun F (Fin b)),
    ← Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun F (Fin c))
    (Pi.basisFun F (Fin d))]
