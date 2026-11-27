import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17653_2
    (hGate6And :
      have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2);
      have x2 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x2 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2 (x1 {x3} {x4}) ≠ (Bool.false, Bool.false)) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2 (x1 x3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3)) = (Bool.false, Bool.false);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → (Fin (26 : ℕ) → Bool) → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : Fin (26 : ℕ) → Bool) => x5.op.eval (List.map (fun (x7 : ℕ) => (x4.wires (List.ofFn x6)).getD x7 Bool.false) x5.inputs);
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : PEqualNP.CircuitLowerBounds.Gate) (p l : Fin (13 : ℕ)),
        have x12 : (Fin (26 : ℕ) → Bool) → Bool × Bool := fun (x12 : Fin (26 : ℕ) → Bool) => (x4 x5 x6 x12, x4 x5 x7 x12);
        (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x5.size ≤ (60 : ℕ) ∧
          PEqualNP.MetaComplexity.Monotone2 x5 ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧
          PEqualNP.MetaComplexity.Monotone2 { gates := [x6, x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧
          x2 x12 ∧
          x12 (x1 {(0 : Fin (13 : ℕ))} {(0 : Fin (13 : ℕ))}) = (Bool.true, Bool.false) ∧
          (13 : ℕ) * ↑p + ↑l ∈ [(4 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ)] ∧
          x12 (x1 {p} {l}) = (Bool.false, Bool.true)) →
        False)
    (hGate6NotAnd :
      have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2);
      have x2 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x2 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2 (x1 {x3} {x4}) ≠ (Bool.false, Bool.false)) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2 (x1 x3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3)) = (Bool.false, Bool.false);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → (Fin (26 : ℕ) → Bool) → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : Fin (26 : ℕ) → Bool) => x5.op.eval (List.map (fun (x7 : ℕ) => (x4.wires (List.ofFn x6)).getD x7 Bool.false) x5.inputs);
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : PEqualNP.CircuitLowerBounds.Gate) (p l : Fin (13 : ℕ)),
        have x12 : (Fin (26 : ℕ) → Bool) → Bool × Bool := fun (x12 : Fin (26 : ℕ) → Bool) => (x4 x5 x6 x12, x4 x5 x7 x12);
        (x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x5.size ≤ (60 : ℕ) ∧
          PEqualNP.MetaComplexity.Monotone2 x5 ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧
          PEqualNP.MetaComplexity.Monotone2 { gates := [x6, x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧
          x2 x12 ∧
          x12 (x1 {(0 : Fin (13 : ℕ))} {(0 : Fin (13 : ℕ))}) = (Bool.true, Bool.false) ∧
          (13 : ℕ) * ↑p + ↑l ∈ [(4 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ)] ∧
          x12 (x1 {p} {l}) = (Bool.false, Bool.true)) →
        False) :
    (have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); have x2 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x2 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2 (x1 {x3} {x4}) ≠ (Bool.false, Bool.false)) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2 (x1 x3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3)) = (Bool.false, Bool.false); have x3 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x3 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => x3 (x1 {(0 : Fin (13 : ℕ))} {(0 : Fin (13 : ℕ))}) = (Bool.true, Bool.false) ∧ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (13 : ℕ) * ↑x4 + ↑x5 ∈ [(4 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ)] ∧ x3 (x1 {x4} {x5}) = (Bool.false, Bool.true); have x4 : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → (Fin (26 : ℕ) → Bool) → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : Fin (26 : ℕ) → Bool) => x5.op.eval (List.map (fun (x7 : ℕ) => (x4.wires (List.ofFn x6)).getD x7 Bool.false) x5.inputs); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : PEqualNP.CircuitLowerBounds.Gate),   x5.size ≤ (60 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x5 →       PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →         PEqualNP.MetaComplexity.Monotone2 { gates := [x6, x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →           have x12 : (Fin (26 : ℕ) → Bool) → Bool × Bool := fun (x12 : Fin (26 : ℕ) → Bool) => (x4 x5 x6 x12, x4 x5 x7 x12);           x2 x12 → ¬x3 x12) :=
  fun x5 x6 x7 hSz hM5 hRB5 hM67 hx2 hx3 =>
    Exists.elim hx3.2 fun p hp =>
    Exists.elim hp fun l hl =>
      Or.elim (Classical.em (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and))
        (fun hA => hGate6And x5 x6 x7 p l ⟨hA, hSz, hM5, hRB5, hM67, hx2, hx3.1, hl.1, hl.2⟩)
        (fun hNA => hGate6NotAnd x5 x6 x7 p l ⟨hNA, hSz, hM5, hRB5, hM67, hx2, hx3.1, hl.1, hl.2⟩)
