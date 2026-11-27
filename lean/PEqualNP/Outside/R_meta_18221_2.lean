import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18221_2
    (hGate0AndSinger : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
      (∀ y : Fin (26 : ℕ) → Bool, C.eval (List.ofFn y) = Bool.true ↔
        ∃ a b : Fin (13 : ℕ), a ∈ PEqualNP.HeptadCover.singerLines3 b ∧
          y (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ y (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧
      (∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates.head? = Option.some g → g.inputs.head? = Option.some (0 : ℕ)) →
      (1 : ℕ) ≤ C.size ∧
      (∃ w < (26 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).inputs = [(0 : ℕ), w]) ∧
      (∀ a b : Fin (13 : ℕ), a ∈ PEqualNP.HeptadCover.singerLines3 b ↔ ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]))
    (hWithGate0 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (1 : ℕ) ≤ C.size ∧ w < (26 : ℕ) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).inputs = [(0 : ℕ), w] ∧
      (∀ y : Fin (26 : ℕ) → Bool, C.eval (List.ofFn y) = Bool.true ↔
        ∃ a b : Fin (13 : ℕ), ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
          y (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ y (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧
      (∀ u v : Fin (26 : ℕ), u ≠ v → ∃ g ∈ C.gates, ↑u ∈ g.inputs ∧ ↑v ∉ g.inputs) →
      ∃ (v : Fin (26 : ℕ)) (S : Finset ℕ), (4 : ℕ) ≤ S.card ∧
        ∀ j ∈ S, j < C.size ∧ ∃ u < (26 : ℕ) + j, ∀ y : Fin (26 : ℕ) → Bool, y v = Bool.false →
          PEqualNP.BlindGate.wireValue C (26 : ℕ) y ((26 : ℕ) + j) = PEqualNP.BlindGate.wireValue C (26 : ℕ) y u) :
    (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     (∀ (x4 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x4) = Bool.true ↔ x1 x4) →       (∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x5 → x5.inputs.head? = Option.some (0 : ℕ)) →         (∀ (x6 x7 : Fin (26 : ℕ)), x6 ≠ x7 → ∃ x9 ∈ x2.gates, ↑x6 ∈ x9.inputs ∧ ↑x7 ∉ x9.inputs) →           ∃ (x7 : Fin (26 : ℕ)),             have x8 : Finset (Fin x2.size) := {x8 : Fin x2.size | ∃ (x9 : Fin ((26 : ℕ) + ↑x8)), ∀ (x10 : Fin (26 : ℕ) → Bool), x10 x7 = Bool.false → PEqualNP.BlindGate.wireValue x2 (26 : ℕ) x10 ((26 : ℕ) + ↑x8) = PEqualNP.BlindGate.wireValue x2 (26 : ℕ) x10 ↑x9};             (4 : ℕ) ≤ x8.card) := by
  intro x1 C hAO hSpec hHead hSep
  rcases hGate0AndSinger C ⟨hAO, hSpec, hHead⟩ with ⟨hSz1, hwEx, hSing⟩
  rcases hwEx with ⟨w, hw, hg0⟩
  have hSpec' : ∀ y : Fin (26 : ℕ) → Bool, C.eval (List.ofFn y) = Bool.true ↔
      ∃ a b : Fin (13 : ℕ), ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
        y (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ y (Fin.natAdd (13 : ℕ) b) = Bool.true := fun y =>
    (hSpec y).trans
      ⟨fun h => Exists.elim h fun a ha => Exists.elim ha fun b hb => ⟨a, b, (hSing a b).mp hb.1, hb.2.1, hb.2.2⟩,
       fun h => Exists.elim h fun a ha => Exists.elim ha fun b hb => ⟨a, b, (hSing a b).mpr hb.1, hb.2.1, hb.2.2⟩⟩
  rcases hWithGate0 C w ⟨hAO, hSz1, hw, hg0, hSpec', hSep⟩ with ⟨v, S, hCard, hS⟩
  refine ⟨v, ?_⟩
  let T : Finset (Fin C.size) := S.attach.image fun j => ⟨j.1, (hS j.1 j.2).1⟩
  have hTcard : T.card = S.card :=
    (Finset.card_image_of_injective S.attach fun a b h => Subtype.ext (congrArg Fin.val h)).trans S.card_attach
  have hSub : T ⊆ Finset.univ.filter (fun j : Fin C.size => ∃ u : Fin ((26 : ℕ) + ↑j), ∀ y : Fin (26 : ℕ) → Bool, y v = Bool.false → PEqualNP.BlindGate.wireValue C (26 : ℕ) y ((26 : ℕ) + ↑j) = PEqualNP.BlindGate.wireValue C (26 : ℕ) y ↑u) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨x, _, hx⟩
    rw [← hx]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases (hS x.1 x.2).2 with ⟨u, hu, hEq⟩
    exact ⟨⟨u, hu⟩, hEq⟩
  exact Nat.le_trans hCard (hTcard ▸ Finset.card_le_card hSub)
