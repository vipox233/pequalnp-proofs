import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8219_1
    (hWireBounds :
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        have d : Fin (13 : ℕ) → List Bool := fun (p : Fin (13 : ℕ)) =>
          (List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i = p)) ++
          List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i = p);
        (∀ (p : Fin (13 : ℕ)),
          ((c.wires (d p)).getD u Bool.false && (c.wires (d p)).getD v Bool.false) = Bool.true) →
        (26 : ℕ) ≤ u ∧ u < (26 : ℕ) + c.size ∧ (26 : ℕ) ≤ v ∧ v < (26 : ℕ) + c.size)
    (hOrderedGateWires :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) =>
        (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++
        List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) =>
        (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++
        List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1);
      have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) =>
        x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ);
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),
        have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;
        ((26 : ℕ) ≤ x6 ∧ x6 < x7 ∧ x7 < (26 : ℕ) + x5.size) ∧
        (PEqualNP.MetaComplexity.Monotone2 x5 ∧
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧
         (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧
         (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧
         (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧
         ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9)) ∧
        (¬∃ (x10 : ℕ) (x11 : ℕ),
          (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11) ∧
        (13 : ℕ) ≤ List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval []) x5.gates →
        (63 : ℕ) ≤ x5.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   (PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9)) → (¬∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11) → (13 : ℕ) ≤ List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval []) x5.gates → (63 : ℕ) ≤ x5.size) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hMain hNoTwo hAnd13
  have h0 : (0 : Fin (13 : ℕ)) ∈ x1 := Finset.mem_insert_self _ _
  have hBnd := hWireBounds x5 x6 x7 (fun p => hMain.2.2.1 p p (Eq.subst (motive := fun z => z ∈ x1) (sub_self p).symm h0))
  exact Or.elim (Nat.lt_trichotomy x6 x7)
    (fun hLt => hOrderedGateWires x5 x6 x7 ⟨⟨hBnd.1, hLt, hBnd.2.2.2⟩, hMain, hNoTwo, hAnd13⟩)
    (fun hEqOrGt => Or.elim hEqOrGt
      (fun hEq => Exists.elim hMain.2.2.2.2.1 fun S hS =>
        False.elim (lt_irrefl (x8 x6 (x3 S))
          (Eq.subst (motive := fun k => x8 x6 (x3 S) < x8 k (x3 S)) hEq.symm hS.2)))
      (fun hGt => hOrderedGateWires x5 x7 x6
        ⟨⟨hBnd.2.2.1, hGt, hBnd.2.1⟩,
         ⟨hMain.1, hMain.2.1,
          (fun p l hpl => Eq.trans (Bool.and_comm _ _) (hMain.2.2.1 p l hpl)),
          (fun S hS => Eq.trans (Bool.and_comm _ _) (hMain.2.2.2.1 S hS)),
          hMain.2.2.2.2.2, hMain.2.2.2.2.1⟩,
         hNoTwo, hAnd13⟩))
