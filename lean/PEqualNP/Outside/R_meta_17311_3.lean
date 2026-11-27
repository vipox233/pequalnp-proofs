import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17311_3
    (hUnusedFalse :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        x2.WellFormed →
        x2.Computes x1 →
        x2.outVars = ∅ →
        x2.size = (20 : ℕ) →
        ∀ (g : Fin x2.size),
          g ∉ x2.outGates →
          (∀ (h : Fin x2.size), g ∉ x2.leftGates h ∧ g ∉ x2.rightGates h) →
          False)
    (hUsedFalse :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        x2.WellFormed →
        x2.Computes x1 →
        x2.outVars = ∅ →
        (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →
        x2.size = (20 : ℕ) →
        have x8 : Fin (42 : ℕ) → Finset (Fin x2.size) := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9};
        (∀ (x9 : Fin (42 : ℕ)), (x8 x9).card ≤ (4 : ℕ)) →
        (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → (x8 x10 ∪ x8 x11).card ≤ (6 : ℕ)) →
        have x11 : Fin x2.size → Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x11 : Fin x2.size) (x12 x13 : Fin (42 : ℕ)) => x12 ∈ x2.leftVars x11 ∧ x13 ∈ x2.rightVars x11 ∨ x13 ∈ x2.leftVars x11 ∧ x12 ∈ x2.rightVars x11;
        ∀ (g : Fin x2.size),
          x11 g (0 : Fin (42 : ℕ)) (21 : Fin (42 : ℕ)) →
          x11 g (2 : Fin (42 : ℕ)) (23 : Fin (42 : ℕ)) →
          g ∉ x2.outGates →
          (∃ (h : Fin x2.size), g < h ∧ (g ∈ x2.leftGates h ∨ g ∈ x2.rightGates h)) →
          False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) → x2.size = (20 : ℕ) → have x8 : Fin (42 : ℕ) → Finset (Fin x2.size) := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9}; (∀ (x9 : Fin (42 : ℕ)), (x8 x9).card ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → (x8 x10 ∪ x8 x11).card ≤ (6 : ℕ)) → have x11 : Fin x2.size → Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x11 : Fin x2.size) (x12 x13 : Fin (42 : ℕ)) => x12 ∈ x2.leftVars x11 ∧ x13 ∈ x2.rightVars x11 ∨ x13 ∈ x2.leftVars x11 ∧ x12 ∈ x2.rightVars x11; (∃ (x12 : Fin x2.size), x11 x12 (0 : Fin (42 : ℕ)) (21 : Fin (42 : ℕ)) ∧ x11 x12 (2 : Fin (42 : ℕ)) (23 : Fin (42 : ℕ))) → False) := by
  classical
  intro x1 x2 hWF hComp hOut hDisj hSz x8 hDeg hPair x11 hEx
  obtain ⟨g, hg0, hg2⟩ := hEx
  have hGateFires : ∀ (a b : Fin 42), a ∈ x2.leftVars g → b ∈ x2.rightVars g →
      x2.gateVal ({a, b} : Finset (Fin 42)) g = true := by
    intro a b ha hb
    have hstep : ∀ d : ℕ, x2.gateValFuel ({a, b} : Finset (Fin 42)) (d + 1) g = true := by
      intro d
      change (decide ((∃ v ∈ x2.leftVars g, v ∈ ({a, b} : Finset (Fin 42))) ∨
               ∃ j ∈ x2.leftGates g, j < g ∧ x2.gateValFuel ({a, b} : Finset (Fin 42)) d j = true) &&
              decide ((∃ v ∈ x2.rightVars g, v ∈ ({a, b} : Finset (Fin 42))) ∨
               ∃ j ∈ x2.rightGates g, j < g ∧ x2.gateValFuel ({a, b} : Finset (Fin 42)) d j = true)) = true
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨Or.inl ⟨a, ha, Finset.mem_insert_self a {b}⟩,
             Or.inl ⟨b, hb, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩⟩
    change x2.gateValFuel ({a, b} : Finset (Fin 42)) x2.size g = true
    rw [hSz]
    exact hstep 19
  have hPairAdj : ∀ (a b : Fin 42), a ∈ x2.leftVars g → b ∈ x2.rightVars g →
      g ∈ x2.outGates → x1.Adj a b := by
    intro a b ha hb hgOut
    have hev : x2.eval ({a, b} : Finset (Fin 42)) = true := by
      unfold PEqualNP.AndCount.AndCountCircuit.eval
      rw [decide_eq_true_eq]
      exact Or.inr ⟨g, hgOut, hGateFires a b ha hb⟩
    obtain ⟨u, hu, v, hv, huv⟩ := (hComp {a, b}).mp hev
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd huv (x1.loopless.irrefl _)
    · exact huv
    · exact huv.symm
    · exact absurd huv (x1.loopless.irrefl _)
  have hNot023 : ¬x1.Adj (0 : Fin 42) (23 : Fin 42) := by
    simp [x1, SimpleGraph.fromRel_adj]
  have hNot02 : ¬x1.Adj (0 : Fin 42) (2 : Fin 42) := by
    simp [x1, SimpleGraph.fromRel_adj]
  have hgNotOut : g ∉ x2.outGates := by
    intro hgOut
    rcases hg0 with ⟨h0L, h21R⟩ | ⟨h21L, h0R⟩
    · rcases hg2 with ⟨h2L, h23R⟩ | ⟨h23L, h2R⟩
      · exact hNot023 (hPairAdj 0 23 h0L h23R hgOut)
      · exact hNot02 (hPairAdj 0 2 h0L h2R hgOut)
    · rcases hg2 with ⟨h2L, h23R⟩ | ⟨h23L, h2R⟩
      · exact hNot02 (hPairAdj 2 0 h2L h0R hgOut).symm
      · exact hNot023 (hPairAdj 23 0 h23L h0R hgOut).symm
  by_cases hUsed : ∃ (h : Fin x2.size), g ∈ x2.leftGates h ∨ g ∈ x2.rightGates h
  · obtain ⟨h, hh⟩ := hUsed
    have hlt : g < h := by
      rcases hh with hl | hr
      · exact (hWF h).1 g hl
      · exact (hWF h).2 g hr
    exact hUsedFalse x2 hWF hComp hOut hDisj hSz hDeg hPair g hg0 hg2 hgNotOut ⟨h, hlt, hh⟩
  · exact hUnusedFalse x2 hWF hComp hOut hSz g hgNotOut (fun h =>
      ⟨fun hl => hUsed ⟨h, Or.inl hl⟩, fun hr => hUsed ⟨h, Or.inr hr⟩⟩)

