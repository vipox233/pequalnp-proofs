import Mathlib.Combinatorics.Hall.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_488 : (∀ (n : ℕ) (F L : Finset (PEqualNP.ProofComplexity.Clause (Fin n))) (S : Finset (Fin n)) (a : Fin n → Bool),
  (∀ C ∈ F, C ∈ L ∨ ∃ l ∈ C, l.1 ∈ S ∧ a l.1 = l.2) →
  (∀ I ⊆ L, I.card ≤ (I.biUnion (fun C => (C.image Prod.fst) \ S)).card) →
  ∃ b : Fin n → Bool, (∀ i ∈ S, b i = a i) ∧ PEqualNP.ProofComplexity.Satisfies b (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) := by
  classical
  intro n F L S a hFL hHall
  let t : ↥L → Finset (Fin n) := fun c => (c.1.image Prod.fst) \ S
  have hall : ∀ s : Finset ↥L, s.card ≤ (s.biUnion t).card := by
    intro s
    let I : Finset (PEqualNP.ProofComplexity.Clause (Fin n)) := s.image Subtype.val
    have hIL : I ⊆ L := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨c, _, rfl⟩
      exact c.2
    have hcard : I.card = s.card := Finset.card_image_of_injective s Subtype.val_injective
    have hbi : I.biUnion (fun C => (C.image Prod.fst) \ S) = s.biUnion t := by
      ext x
      simp only [I, t, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨C, ⟨c, hcs, rfl⟩, hx⟩
        exact ⟨c, hcs, hx⟩
      · rintro ⟨c, hcs, hx⟩
        exact ⟨c.1, ⟨c, hcs, rfl⟩, hx⟩
    have hle := hHall I hIL
    rw [hcard, hbi] at hle
    exact hle
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  have hex_lit : ∀ c : ↥L, ∃ l ∈ c.1, l.1 = f c := by
    intro c
    exact Finset.mem_image.mp (Finset.mem_sdiff.mp (hf_mem c)).1
  choose l hl_mem hl_fst using hex_lit
  let b : Fin n → Bool := fun i => if h : ∃ c : ↥L, f c = i then (l (Classical.choose h)).2 else a i
  have hb_S : ∀ i ∈ S, b i = a i := by
    intro i hiS
    dsimp only [b]
    split_ifs with h
    · rcases h with ⟨c, rfl⟩
      exact False.elim ((Finset.mem_sdiff.mp (hf_mem c)).2 hiS)
    · rfl
  refine ⟨b, hb_S, ?_⟩
  intro C hCF
  have hCF' : C ∈ F := Finset.mem_coe.mp hCF
  rcases hFL C hCF' with hCL | ⟨l0, hl0C, hl0S, hal0⟩
  · let c : ↥L := ⟨C, hCL⟩
    refine ⟨l c, hl_mem c, ?_⟩
    dsimp only [b]
    split_ifs with hex
    · have hchoose : Classical.choose hex = c := by
        apply hf_inj
        exact (Classical.choose_spec hex).trans (hl_fst c)
      rw [hchoose]
    · exact False.elim (hex ⟨c, (hl_fst c).symm⟩)
  · refine ⟨l0, hl0C, ?_⟩
    rw [hb_S l0.1 hl0S]
    exact hal0
