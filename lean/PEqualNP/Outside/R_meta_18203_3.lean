import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18203_3
    (hOperandsInternal :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
        ((∀ (i : ℕ) (gt : PEqualNP.CircuitLowerBounds.Gate),
            C.gates[i]? = Option.some gt →
            (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ (a b : ℕ), gt.inputs = [a, b] ∧ a ≠ b ∧ a < (26 : ℕ) + i ∧ b < (26 : ℕ) + i) ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C g (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧
         (∀ (b : Fin (2 : ℕ)),
           PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C g b) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false ∧
           PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C g b) (PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.false)) →
        g < C.size ∧ (2 : ℕ) ≤ g ∧
        (26 : ℕ) ≤ PEqualNP.TopForm.opnd C g (0 : Fin (2 : ℕ)) ∧
        PEqualNP.TopForm.opnd C g (0 : Fin (2 : ℕ)) < (26 : ℕ) + g ∧
        (26 : ℕ) ≤ PEqualNP.TopForm.opnd C g (1 : Fin (2 : ℕ)) ∧
        PEqualNP.TopForm.opnd C g (1 : Fin (2 : ℕ)) < (26 : ℕ) + g ∧
        PEqualNP.TopForm.opnd C g (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd C g (1 : Fin (2 : ℕ)))
    (hNoInternalBothFalse :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ),
        have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
        have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
        have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;
        have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;
        have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
        have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        (x1.size = (64 : ℕ) ∧
         (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 →
           (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
           ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧
         (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔
           ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)),
             (x11 - x12 = (0 : Fin (13 : ℕ)) ∨ x11 - x12 = (1 : Fin (13 : ℕ)) ∨ x11 - x12 = (3 : Fin (13 : ℕ)) ∨ x11 - x12 = (9 : Fin (13 : ℕ))) ∧
             x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧
         (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧
         x6 g ∧ g < (64 : ℕ) ∧ (2 : ℕ) ≤ g ∧
         a = PEqualNP.TopForm.opnd x1 g (0 : Fin (2 : ℕ)) ∧ b = PEqualNP.TopForm.opnd x1 g (1 : Fin (2 : ℕ)) ∧
         (26 : ℕ) ≤ a ∧ a < (26 : ℕ) + g ∧ (26 : ℕ) ≤ b ∧ b < (26 : ℕ) + g ∧ a ≠ b ∧
         ((26 : ℕ) + g = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 g (x1.output - (26 : ℕ))) ∧
         x4 g (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧
         x5 a x7 = Bool.false ∧ x5 a x8 = Bool.false ∧ x5 b x7 = Bool.false ∧ x5 b x8 = Bool.false) →
        False) :
    (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size = (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ ((26 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ))) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false) := by
  intro hEx
  exact Exists.elim hEx fun x1 h =>
    Exists.elim h.2.2.2.2 fun g hg =>
      let hI := hOperandsInternal x1 g ⟨h.2.1, hg.1, hg.2.2.1, hg.2.2.2⟩
      let hMem : ∀ a : Fin (13 : ℕ),
          a ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ↔
          a = (0 : Fin (13 : ℕ)) ∨ a = (1 : Fin (13 : ℕ)) ∨ a = (3 : Fin (13 : ℕ)) ∨ a = (9 : Fin (13 : ℕ)) :=
        fun a => Iff.trans Finset.mem_insert
          (or_congr_right (Iff.trans Finset.mem_insert
            (or_congr_right (Iff.trans Finset.mem_insert
              (or_congr_right Finset.mem_singleton)))))
      let hSpec' : ∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔
          ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)),
            (x11 - x12 = (0 : Fin (13 : ℕ)) ∨ x11 - x12 = (1 : Fin (13 : ℕ)) ∨ x11 - x12 = (3 : Fin (13 : ℕ)) ∨ x11 - x12 = (9 : Fin (13 : ℕ))) ∧
            x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true :=
        fun x10 => Iff.trans (h.2.2.1 x10)
          (Iff.intro
            (fun hex => Exists.elim hex fun p hp => Exists.elim hp fun l hl => ⟨p, l, (hMem (p - l)).mp hl.1, hl.2⟩)
            (fun hex => Exists.elim hex fun p hp => Exists.elim hp fun l hl => ⟨p, l, (hMem (p - l)).mpr hl.1, hl.2⟩))
      hNoInternalBothFalse x1 g (PEqualNP.TopForm.opnd x1 g (0 : Fin (2 : ℕ))) (PEqualNP.TopForm.opnd x1 g (1 : Fin (2 : ℕ)))
        ⟨h.1, h.2.1, hSpec', h.2.2.2.1, hg.1,
         Eq.subst (motive := fun k => g < k) h.1 hI.1,
         hI.2.1, rfl, rfl,
         hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2.1, hI.2.2.2.2.2.1, hI.2.2.2.2.2.2,
         hg.2.1, hg.2.2.1,
         (hg.2.2.2 (0 : Fin (2 : ℕ))).1, (hg.2.2.2 (0 : Fin (2 : ℕ))).2,
         (hg.2.2.2 (1 : Fin (2 : ℕ))).1, (hg.2.2.2 (1 : Fin (2 : ℕ))).2⟩
