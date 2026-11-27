import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_470 : (∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  (∃ c : Fin n → Fin k, ∀ u v, G.Adj u v → c u ≠ c v) ↔
    ∃ F : Finset (Finset (Fin n)), F.card ≤ k ∧
      (∀ v, ∃ S ∈ F, v ∈ S) ∧ ∀ S ∈ F, Gᶜ.IsClique (↑S)) := by
  intro n k G
  classical
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Finset.univ.image (fun i : Fin k => Finset.univ.filter (fun v => c v = i)), ?_, ?_, ?_⟩
    · calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    · intro v
      exact ⟨Finset.univ.filter (fun w => c w = c v),
        Finset.mem_image.2 ⟨c v, Finset.mem_univ _, rfl⟩, by simp⟩
    · intro S hS
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
      intro u hu v hv huv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu hv
      rw [SimpleGraph.compl_adj]
      exact ⟨huv, fun h => hc u v h (hu.trans hv.symm)⟩
  · rintro ⟨F, hF, hcov, hcl⟩
    choose S hSF hvS using hcov
    let idx : F → Fin k := fun T => Fin.castLE hF (F.equivFin T)
    have hidx : Function.Injective idx := fun a b h =>
      F.equivFin.injective (Fin.castLE_injective hF h)
    refine ⟨fun v => idx ⟨S v, hSF v⟩, fun u v huv heq => ?_⟩
    have hS : S u = S v := congrArg Subtype.val (hidx heq)
    have hu : u ∈ (S v : Set (Fin n)) := by
      rw [Finset.mem_coe, ← hS]
      exact hvS u
    have hv : v ∈ (S v : Set (Fin n)) := Finset.mem_coe.2 (hvS v)
    have h := hcl (S v) (hSF v) hu hv (G.ne_of_adj huv)
    rw [SimpleGraph.compl_adj] at h
    exact h.2 huv
