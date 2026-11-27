import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18619_1
    (hTableEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        (([5137, 0, 0, 141, 0, 564, 1128, 2256, 4512, 833, 0, 3332, 6664] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ↔
          p ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] ∧
          l ≠ (1 : Fin (13 : ℕ)) ∧
          (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ)) ∨ p = l + (9 : Fin (13 : ℕ))))
    (hCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size ≤ (42 : ℕ) ∧
        (27 : ℕ) ≤ C.output ∧ C.output < (27 : ℕ) + C.size ∧
        PEqualNP.TopForm.IsAO2 (27 : ℕ) C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        ∀ (x : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn x ++ [x (1 : Fin (26 : ℕ)) || x (2 : Fin (26 : ℕ))]) = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)),
              (([5137, 0, 0, 141, 0, 564, 1128, 2256, 4512, 833, 0, 3332, 6664] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (42 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) :=
  Exists.elim hCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, fun x =>
      Iff.intro
        (fun h =>
          Exists.elim ((hC.2.2.2.2.2 x).mp h) fun p hp =>
            Exists.elim hp fun l hl =>
              ⟨p, l, ((hTableEquiv p l).mp hl.1).1, ((hTableEquiv p l).mp hl.1).2.1, ((hTableEquiv p l).mp hl.1).2.2, hl.2.1, hl.2.2⟩)
        (fun h =>
          Exists.elim h fun p hp =>
            Exists.elim hp fun l hl =>
              (hC.2.2.2.2.2 x).mpr
                ⟨p, l, (hTableEquiv p l).mpr ⟨hl.1, hl.2.1, hl.2.2.1⟩, hl.2.2.2.1, hl.2.2.2.2⟩)⟩
