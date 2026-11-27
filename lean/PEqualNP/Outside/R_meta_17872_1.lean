import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17872_1
    (hCircuit :
      ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 : ℕ) (x6 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x3 ∧
        x3.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧
        x4 ≠ [] ∧
        x3.size + (2 : ℕ) * x4.length ≤ (59 : ℕ) ∧
        x5 < (24 : ℕ) + x3.size ∧
        x6 < (24 : ℕ) + x3.size ∧
        (∀ x7 ∈ x4, x7.1 < (24 : ℕ) + x3.size ∧ x7.2 < (24 : ℕ) + x3.size) ∧
        ∀ (x7 : Fin (24 : ℕ) → Bool),
          ((x4.any fun (x8 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.1 && PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.2) = Bool.true ↔
            ∃ (u v : Fin (12 : ℕ)),
              (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true ∧
              x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
              x7 (Fin.natAdd (12 : ℕ) v) = Bool.true) ∧
          ((¬∃ (u v : Fin (12 : ℕ)),
              (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true ∧
              x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
              x7 (Fin.natAdd (12 : ℕ) v) = Bool.true) →
            PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x5 = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧
            PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x6 = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ)))))
    (hTableEquiv :
      ∀ (u v : Fin (12 : ℕ)),
        (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true ↔
          ((Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (24 : ℕ) → Bool) → Prop := fun (x2 : Fin (24 : ℕ) → Bool) => ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (12 : ℕ)), Fin.succAbove (9 : Fin (13 : ℕ)) x3 + Fin.succAbove (0 : Fin (13 : ℕ)) x4 ∈ x1 ∧ x2 (Fin.castAdd (12 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4 ≠ [] ∧ x3.size + (2 : ℕ) * x4.length ≤ (59 : ℕ) ∧ x5 < (24 : ℕ) + x3.size ∧ x6 < (24 : ℕ) + x3.size ∧ (∀ x7 ∈ x4, x7.1 < (24 : ℕ) + x3.size ∧ x7.2 < (24 : ℕ) + x3.size) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), ((x4.any fun (x8 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.1 && PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.2) = Bool.true ↔ x2 x7) ∧ (¬x2 x7 → PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x5 = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x6 = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))))) := by
  have hMem : ∀ s : Fin (13 : ℕ), s.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔ s ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := by decide
  obtain ⟨x3, x4, x5, x6, hM, hHead, hNE, hSz, h5, h6, hBnd, hEval⟩ := hCircuit
  refine ⟨x3, x4, x5, x6, hM, hHead, hNE, hSz, h5, h6, hBnd, ?_⟩
  intro x7
  have hEq : (∃ (u v : Fin (12 : ℕ)),
      (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true ∧
      x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
      x7 (Fin.natAdd (12 : ℕ) v) = Bool.true) ↔
    (∃ (u v : Fin (12 : ℕ)),
      Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∧
      x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
      x7 (Fin.natAdd (12 : ℕ) v) = Bool.true) :=
    exists_congr (fun u => exists_congr (fun v => and_congr_left' ((hTableEquiv u v).trans (hMem _))))
  exact ⟨(hEval x7).1.trans hEq, fun hn => (hEval x7).2 (fun h => hn (hEq.mp h))⟩
