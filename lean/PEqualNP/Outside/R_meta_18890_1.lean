import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18890_1
    (hPointPairs : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x1 x3 → x2 x3 → (59 : ℕ) ≤ x3.size)
    (hLinePairs : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x1 x3 → x2 x3 → (59 : ℕ) ≤ x3.size) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x1 x3 → x2 x3 → (59 : ℕ) ≤ x3.size) := by
  intro x1 x2 x3 hM h1 h2
  rcases h2 with ⟨g, a, ha, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hPointPairs x3 hM h1 ⟨g, 1, by decide, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hPointPairs x3 hM h1 ⟨g, 2, by decide, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hPointPairs x3 hM h1 ⟨g, 14, by decide, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hPointPairs x3 hM h1 ⟨g, 16, by decide, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hLinePairs x3 hM h1 ⟨g, 313, by decide, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hLinePairs x3 hM h1 ⟨g, 316, by decide, hop, hne, hev⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hLinePairs x3 hM h1 ⟨g, 339, by decide, hop, hne, hev⟩
  cases ha
