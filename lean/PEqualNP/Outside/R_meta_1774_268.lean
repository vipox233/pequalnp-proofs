import Mathlib
import PEqualNP.Defs

-- Split on the number of vertices. A positive count of AND gates owning two disjoint edges
-- needs four distinct vertices, so graphs on at most 3 vertices are proved here; graphs on
-- 4 to 6 vertices and graphs on at least 7 vertices remain.
theorem PEqualNP.Outside.R_meta_1774_268
    (small :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (4 : ℕ) ≤ x1 → x1 ≤ (6 : ℕ) →   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8)
    (large :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (7 : ℕ) ≤ x1 →   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  intro x1 x2 x3
  rcases Nat.lt_or_ge x1 4 with h | h
  · dsimp only
    intro _ _ x8 _ _ _ hpos
    exfalso
    obtain ⟨_, a, b, c, d, hab, hcd, _, _, h1, h2, h3, h4⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    have hab' : a ≠ b := hab.ne
    have hcd' : c ≠ d := hcd.ne
    have hcard : ({a, b, c, d} : Finset (Fin x1)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hab', h1, h2]),
        Finset.card_insert_of_notMem (by simp [h3, h4]),
        Finset.card_insert_of_notMem (by simp [hcd']), Finset.card_singleton]
    have := Finset.card_le_univ ({a, b, c, d} : Finset (Fin x1))
    rw [hcard, Fintype.card_fin] at this
    omega
  · rcases Nat.lt_or_ge x1 7 with h' | h'
    · exact small x1 x2 h (by omega)
    · exact large x1 x2 h'
