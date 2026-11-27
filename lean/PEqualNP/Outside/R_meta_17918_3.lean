import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17918_3
    (hSubShared :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 26 x1;
        have x4 : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal 26 x1;
        have x5 : ℕ → Prop := fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x6 : ℕ → Prop := fun g => 26 + g = x1.output ∨ x3 g (x1.output - 26);
        have p : Fin 26 → Fin 26 → Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput;
        have x7 : Fin 26 → Bool := p 0 0;
        have x8 : Fin 26 → Bool := p 13 13;
        have x9 : Fin 26 → Bool := p 0 13;
        have x10 : ℕ → (Fin 26 → Bool) → Prop := fun g y =>
          x5 g ∧ x6 g ∧ x4 g x9 = true ∧ ∀ i : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 x1 (PEqualNP.TopForm.opnd x1 g i) y = false;
        x1.size ≤ 64 ∧ PEqualNP.TopForm.IsAO2 26 x1 ∧ (∀ g ∈ x1.gates, g.inputs.Nodup) ∧
        (∀ f : Fin 26 → Bool, x1.eval (List.ofFn f) = true ↔
          ∃ a b : Fin 13, a - b ∈ [(0 : Fin 13), 1, 3, 9] ∧ f (Fin.castAdd 13 a) = true ∧ f (Fin.natAdd 13 b) = true) ∧
        (∃ g < x1.gates.length, x5 g ∧ ∃ y : Fin 26 → Bool, x4 g y = true ∧ x1.eval (List.ofFn y) = false) ∧
        ∃ x11 x12 x13 x14 : ℕ,
          x11 ≠ x12 ∧ ¬x3 x11 x12 ∧ ¬x3 x12 x11 ∧ x10 x11 x7 ∧ x10 x12 x8 ∧
          x4 x11 x8 = true ∧ x4 x12 x7 = false ∧ x3 x11 x13 ∧ x5 x13 ∧ x6 x13 ∧ x4 x13 x8 = false ∧
          x3 x14 x12 ∧ x5 x14 ∧ x4 x14 x9 = true ∧ x4 x14 x7 = false ∧ x4 x14 x8 = false ∧ x3 x14 x11)
    (hSubDisjoint :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 26 x1;
        have x4 : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal 26 x1;
        have x5 : ℕ → Prop := fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x6 : ℕ → Prop := fun g => 26 + g = x1.output ∨ x3 g (x1.output - 26);
        have p : Fin 26 → Fin 26 → Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput;
        have x7 : Fin 26 → Bool := p 0 0;
        have x8 : Fin 26 → Bool := p 13 13;
        have x9 : Fin 26 → Bool := p 0 13;
        have x10 : ℕ → (Fin 26 → Bool) → Prop := fun g y =>
          x5 g ∧ x6 g ∧ x4 g x9 = true ∧ ∀ i : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 x1 (PEqualNP.TopForm.opnd x1 g i) y = false;
        x1.size ≤ 64 ∧ PEqualNP.TopForm.IsAO2 26 x1 ∧ (∀ g ∈ x1.gates, g.inputs.Nodup) ∧
        (∀ f : Fin 26 → Bool, x1.eval (List.ofFn f) = true ↔
          ∃ a b : Fin 13, a - b ∈ [(0 : Fin 13), 1, 3, 9] ∧ f (Fin.castAdd 13 a) = true ∧ f (Fin.natAdd 13 b) = true) ∧
        (∃ g < x1.gates.length, x5 g ∧ ∃ y : Fin 26 → Bool, x4 g y = true ∧ x1.eval (List.ofFn y) = false) ∧
        ∃ x11 x12 x13 x14 : ℕ,
          x11 ≠ x12 ∧ ¬x3 x11 x12 ∧ ¬x3 x12 x11 ∧ x10 x11 x7 ∧ x10 x12 x8 ∧
          x4 x11 x8 = true ∧ x4 x12 x7 = false ∧ x3 x11 x13 ∧ x5 x13 ∧ x6 x13 ∧ x4 x13 x8 = false ∧
          x3 x14 x12 ∧ x5 x14 ∧ x4 x14 x9 = true ∧ x4 x14 x7 = false ∧ x4 x14 x8 = false ∧ ¬x3 x14 x11) :
    (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ) (x14 : ℕ), x11 ≠ x12 ∧ ¬x3 x11 x12 ∧ ¬x3 x12 x11 ∧ x10 x11 x7 ∧ x10 x12 x8 ∧ x4 x11 x8 = Bool.true ∧ x4 x12 x7 = Bool.false ∧ x3 x11 x13 ∧ x5 x13 ∧ x6 x13 ∧ x4 x13 x8 = Bool.false ∧ x3 x14 x12 ∧ x5 x14 ∧ x4 x14 x9 = Bool.true ∧ x4 x14 x7 = Bool.false ∧ x4 x14 x8 = Bool.false) := by
  intro hEx
  exact Exists.elim hEx fun x1 hx1 =>
    have hmem : ∀ d : Fin 13, d ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)) ↔ d ∈ [(0 : Fin 13), 1, 3, 9] := by
      intro d; simp [Finset.mem_insert, Finset.mem_singleton]
    have hEv' : ∀ f : Fin 26 → Bool, x1.eval (List.ofFn f) = true ↔
        ∃ a b : Fin 13, a - b ∈ [(0 : Fin 13), 1, 3, 9] ∧ f (Fin.castAdd 13 a) = true ∧ f (Fin.natAdd 13 b) = true :=
      fun f => Iff.trans (hx1.2.2.2.1 f) (exists_congr fun a => exists_congr fun b => and_congr_left' (hmem (a - b)))
    Exists.elim hx1.2.2.2.2.2 fun x11 hx11 =>
    Exists.elim hx11 fun x12 hx12 =>
    Exists.elim hx12 fun x13 hx13 =>
    Exists.elim hx13 fun x14 h =>
      Or.elim (Classical.em (PEqualNP.EdgeOwnership.InCone 26 x1 x14 x11))
        (fun hSh => hSubShared ⟨x1, hx1.1, hx1.2.1, hx1.2.2.1, hEv', hx1.2.2.2.2.1,
          x11, x12, x13, x14, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
          h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hSh⟩)
        (fun hDis => hSubDisjoint ⟨x1, hx1.1, hx1.2.1, hx1.2.2.1, hEv', hx1.2.2.2.2.1,
          x11, x12, x13, x14, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
          h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hDis⟩)
