import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_449 : (∀ (n k : ℕ) (G : SimpleGraph (Fin n)), k ≤ n →
  ((∃ S : Finset (Fin n), k ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ↔
   ∃ C : Finset (Fin n), C.card ≤ n - k ∧ Gᶜ.IsVertexCover (C : Set (Fin n)))) := by
  intro n k G hk
  constructor
  · rintro ⟨S, hS, hcl⟩
    refine ⟨Sᶜ, ?_, ?_⟩
    · rw [Finset.card_compl, Fintype.card_fin]; omega
    · rw [Finset.coe_compl, SimpleGraph.isVertexCover_compl, SimpleGraph.isIndepSet_compl]
      exact hcl
  · rintro ⟨C, hC, hvc⟩
    refine ⟨Cᶜ, ?_, ?_⟩
    · rw [Finset.card_compl, Fintype.card_fin]
      have : C.card ≤ n := by simpa using C.card_le_univ
      omega
    · rw [← SimpleGraph.isIndepSet_compl, Finset.coe_compl,
        SimpleGraph.isIndepSet_compl_iff_isVertexCover]
      exact hvc
