import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_481 : (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Fin m → ZMod 2),
  (¬ ∃ x : Fin n → ZMod 2, A.mulVec x = b) ↔
    ∃ y : Fin m → ZMod 2, A.vecMul y = 0 ∧ dotProduct y b = 1) := by
  intro m n A b
  constructor
  · intro h
    have hb : b ∉ LinearMap.range A.mulVecLin := by
      rintro ⟨x, hx⟩
      exact h ⟨x, by simpa using hx⟩
    obtain ⟨f, hfb, hf⟩ := Submodule.exists_le_ker_of_notMem hb
    have key : ∀ v : Fin m → ZMod 2, dotProduct (fun i => f (Pi.single i 1)) v = f v := by
      intro v
      conv_rhs => rw [← Finset.univ_sum_single v]
      rw [map_sum]
      unfold dotProduct
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hs : (Pi.single i (v i) : Fin m → ZMod 2) = v i • Pi.single i (1 : ZMod 2) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hs, map_smul, smul_eq_mul, mul_comm]
    refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
    · funext j
      have h1 : A.vecMul (fun i => f (Pi.single i 1)) j = f (fun i => A i j) := key (fun i => A i j)
      have hmem : (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
        refine ⟨Pi.single j 1, ?_⟩
        funext i
        simp
      rw [h1]
      simpa using hf hmem
    · rw [key]
      exact (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hfb
  · rintro ⟨y, hy, hyb⟩ ⟨x, hx⟩
    rw [← hx, Matrix.dotProduct_mulVec, hy, zero_dotProduct] at hyb
    exact zero_ne_one hyb
