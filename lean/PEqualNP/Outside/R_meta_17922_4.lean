import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17922_4
    (hFirstEarlier :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x11 x12 x13 x14 : ℕ),
        have x2 : List (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))];
        have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;
        have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
        have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));
        have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
        have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;
        have x15 : ℕ → Prop := fun (g : ℕ) => x5 g ∧ x4 g x9 = Bool.true ∧ x4 g x7 = Bool.false ∧ x4 g x8 = Bool.false;
        (x11 < x12 ∧ x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ g ∈ x1.gates, g.inputs.Nodup) ∧ (∀ (v : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn v) = Bool.true ↔ ∃ (a : Fin (13 : ℕ)) (b : Fin (13 : ℕ)), a - b ∈ x2 ∧ v (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ v (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧ (∃ g < x1.gates.length, x5 g ∧ ∃ (v : Fin (26 : ℕ) → Bool), x4 g v = Bool.true ∧ x1.eval (List.ofFn v) = Bool.false) ∧ ¬x3 x11 x12 ∧ ¬x3 x12 x11 ∧ x10 x11 x7 ∧ x10 x12 x8 ∧ x4 x11 x8 = Bool.false ∧ x4 x12 x7 = Bool.false ∧ x3 x13 x11 ∧ x15 x13 ∧ x3 x14 x12 ∧ x15 x14) →
        False)
    (hSecondEarlier :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x11 x12 x13 x14 : ℕ),
        have x2 : List (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))];
        have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;
        have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
        have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));
        have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
        have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;
        have x15 : ℕ → Prop := fun (g : ℕ) => x5 g ∧ x4 g x9 = Bool.true ∧ x4 g x7 = Bool.false ∧ x4 g x8 = Bool.false;
        (x12 < x11 ∧ x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ g ∈ x1.gates, g.inputs.Nodup) ∧ (∀ (v : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn v) = Bool.true ↔ ∃ (a : Fin (13 : ℕ)) (b : Fin (13 : ℕ)), a - b ∈ x2 ∧ v (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ v (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧ (∃ g < x1.gates.length, x5 g ∧ ∃ (v : Fin (26 : ℕ) → Bool), x4 g v = Bool.true ∧ x1.eval (List.ofFn v) = Bool.false) ∧ ¬x3 x11 x12 ∧ ¬x3 x12 x11 ∧ x10 x11 x7 ∧ x10 x12 x8 ∧ x4 x11 x8 = Bool.false ∧ x4 x12 x7 = Bool.false ∧ x3 x13 x11 ∧ x15 x13 ∧ x3 x14 x12 ∧ x15 x14) →
        False) :
    (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ) (x14 : ℕ), x11 ≠ x12 ∧ ¬x3 x11 x12 ∧ ¬x3 x12 x11 ∧ x10 x11 x7 ∧ x10 x12 x8 ∧ x4 x11 x8 = Bool.false ∧ x4 x12 x7 = Bool.false ∧ x3 x13 x11 ∧ x5 x13 ∧ x4 x13 x9 = Bool.true ∧ x4 x13 x7 = Bool.false ∧ x4 x13 x8 = Bool.false ∧ x3 x14 x12 ∧ x5 x14 ∧ x4 x14 x9 = Bool.true ∧ x4 x14 x7 = Bool.false ∧ x4 x14 x8 = Bool.false) :=
  fun hex =>
    hex.elim fun x1 hx =>
      have hMem : ∀ a : Fin (13 : ℕ),
          a ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ↔
          a ∈ ([(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] : List (Fin (13 : ℕ))) :=
        fun _ =>
          (Finset.mem_insert.trans (or_congr_right
            (Finset.mem_insert.trans (or_congr_right
              (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)))))).trans
          (List.mem_cons.trans (or_congr_right
            (List.mem_cons.trans (or_congr_right
              (List.mem_cons.trans (or_congr_right List.mem_singleton)))))).symm
      have hEval' : ∀ (v : Fin (26 : ℕ) → Bool),
          x1.eval (List.ofFn v) = Bool.true ↔
          ∃ (a : Fin (13 : ℕ)) (b : Fin (13 : ℕ)),
            a - b ∈ ([(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] : List (Fin (13 : ℕ))) ∧
            v (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ v (Fin.natAdd (13 : ℕ) b) = Bool.true :=
        fun v => (hx.2.2.2.1 v).trans (exists_congr fun a => exists_congr fun b => and_congr_left fun _ => hMem (a - b))
      hx.2.2.2.2.2.elim fun g1 h1 =>
      h1.elim fun g2 h2 =>
      h2.elim fun g3 h3 =>
      h3.elim fun g4 hw =>
        Or.elim (Nat.lt_or_gt_of_ne hw.1)
          (fun hLt =>
            hFirstEarlier x1 g1 g2 g3 g4
              ⟨hLt, hx.1, hx.2.1, hx.2.2.1, hEval', hx.2.2.2.2.1,
               hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1,
               hw.2.2.2.2.2.2.2.1,
               ⟨hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.1⟩,
               hw.2.2.2.2.2.2.2.2.2.2.2.2.1,
               ⟨hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩⟩)
          (fun hGt =>
            hSecondEarlier x1 g1 g2 g3 g4
              ⟨hGt, hx.1, hx.2.1, hx.2.2.1, hEval', hx.2.2.2.2.1,
               hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1,
               hw.2.2.2.2.2.2.2.1,
               ⟨hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.1⟩,
               hw.2.2.2.2.2.2.2.2.2.2.2.2.1,
               ⟨hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩⟩)
