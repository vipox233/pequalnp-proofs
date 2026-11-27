import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_769_aux

theorem ker_card (n m : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Nat.card (LinearMap.ker A.mulVecLin) = 2 ^ (n - A.rank) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := Module.finrank_fin_fun (ZMod 2)
  have h3 : A.rank = Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) := rfl
  have h4 : Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = n - A.rank := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h4, Nat.card_zmod]

end PEqualNP.Outside.L_lib_769_aux

theorem PEqualNP.Outside.L_lib_769 : ∀ (n m : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Fin m → ZMod 2),
  (∃ x, A.mulVec x = b) →
  (Finset.univ.filter (fun x : Fin n → ZMod 2 => A.mulVec x = b)).card = 2 ^ (n - A.rank) := by
  intro n m A b hx
  obtain ⟨x0, hx0⟩ := hx
  rw [← PEqualNP.Outside.L_lib_769_aux.ker_card n m A, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ⟨fun x => ⟨x.1 - x0, ?_⟩, fun y => ⟨y.1 + x0, ?_⟩, ?_, ?_⟩
  · have hx := x.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [LinearMap.mem_ker, Matrix.mulVec_sub, hx, hx0]
  · have hy := y.2
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    simp [Matrix.mulVec_add, hy, hx0]
  · intro x
    simp
  · intro y
    simp
