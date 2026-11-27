import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17872_2
    (hMonoSound :
      ∀ (adj : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 x6 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x3 →
        let wv := PEqualNP.BlindGate.wireValue x3 (24 : ℕ)
        let out := fun (x7 : Fin (24 : ℕ) → Bool) => x4.any fun (p : ℕ × ℕ) => wv x7 p.1 && wv x7 p.2
        let hasE := fun (x7 : Fin (24 : ℕ) → Bool) => ∃ (u v : Fin (12 : ℕ)), adj u v ∧ x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧ x7 (Fin.natAdd (12 : ℕ) v) = Bool.true
        (∀ (u v : Fin (12 : ℕ)), adj u v → out (fun k => Decidable.decide (k = Fin.castAdd (12 : ℕ) u ∨ k = Fin.natAdd (12 : ℕ) v)) = Bool.true) →
        (∀ (k : Fin (24 : ℕ)), k.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] → wv (fun j => Decidable.decide (j = k)) x5 = Bool.true) →
        (∀ (k : Fin (24 : ℕ)), k.val ∈ [(15 : ℕ), (16 : ℕ), (18 : ℕ)] → wv (fun j => Decidable.decide (j = k)) x6 = Bool.true) →
        (∀ (x7 : Fin (24 : ℕ) → Bool), ¬hasE x7 →
          out x7 = Bool.false ∧
          (x7 (0 : Fin (24 : ℕ)) = Bool.false → x7 (1 : Fin (24 : ℕ)) = Bool.false → x7 (3 : Fin (24 : ℕ)) = Bool.false → wv x7 x5 = Bool.false) ∧
          (x7 (15 : Fin (24 : ℕ)) = Bool.false → x7 (16 : Fin (24 : ℕ)) = Bool.false → x7 (18 : Fin (24 : ℕ)) = Bool.false → wv x7 x6 = Bool.false)) →
        ∀ (x7 : Fin (24 : ℕ) → Bool),
          (out x7 = Bool.true ↔ hasE x7) ∧
          (¬hasE x7 →
            wv x7 x5 = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧
            wv x7 x6 = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ)))))
    (hEdgeTests :
      let adj : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun u v => (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]
      ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 : ℕ) (x6 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x3 ∧
        x3.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧
        x4 ≠ [] ∧
        x3.size + (2 : ℕ) * x4.length ≤ (59 : ℕ) ∧
        x5 < (24 : ℕ) + x3.size ∧
        x6 < (24 : ℕ) + x3.size ∧
        (∀ x7 ∈ x4, x7.1 < (24 : ℕ) + x3.size ∧ x7.2 < (24 : ℕ) + x3.size) ∧
        let wv := PEqualNP.BlindGate.wireValue x3 (24 : ℕ)
        let out := fun (x7 : Fin (24 : ℕ) → Bool) => x4.any fun (p : ℕ × ℕ) => wv x7 p.1 && wv x7 p.2
        let hasE := fun (x7 : Fin (24 : ℕ) → Bool) => ∃ (u v : Fin (12 : ℕ)), adj u v ∧ x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧ x7 (Fin.natAdd (12 : ℕ) v) = Bool.true
        (∀ (u v : Fin (12 : ℕ)), adj u v → out (fun k => Decidable.decide (k = Fin.castAdd (12 : ℕ) u ∨ k = Fin.natAdd (12 : ℕ) v)) = Bool.true) ∧
        (∀ (k : Fin (24 : ℕ)), k.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] → wv (fun j => Decidable.decide (j = k)) x5 = Bool.true) ∧
        (∀ (k : Fin (24 : ℕ)), k.val ∈ [(15 : ℕ), (16 : ℕ), (18 : ℕ)] → wv (fun j => Decidable.decide (j = k)) x6 = Bool.true) ∧
        (∀ (x7 : Fin (24 : ℕ) → Bool), ¬hasE x7 →
          out x7 = Bool.false ∧
          (x7 (0 : Fin (24 : ℕ)) = Bool.false → x7 (1 : Fin (24 : ℕ)) = Bool.false → x7 (3 : Fin (24 : ℕ)) = Bool.false → wv x7 x5 = Bool.false) ∧
          (x7 (15 : Fin (24 : ℕ)) = Bool.false → x7 (16 : Fin (24 : ℕ)) = Bool.false → x7 (18 : Fin (24 : ℕ)) = Bool.false → wv x7 x6 = Bool.false))) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (24 : ℕ) → Bool) → Prop := fun (x2 : Fin (24 : ℕ) → Bool) => ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (12 : ℕ)), Fin.succAbove (9 : Fin (13 : ℕ)) x3 + Fin.succAbove (0 : Fin (13 : ℕ)) x4 ∈ x1 ∧ x2 (Fin.castAdd (12 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4 ≠ [] ∧ x3.size + (2 : ℕ) * x4.length ≤ (59 : ℕ) ∧ x5 < (24 : ℕ) + x3.size ∧ x6 < (24 : ℕ) + x3.size ∧ (∀ x7 ∈ x4, x7.1 < (24 : ℕ) + x3.size ∧ x7.2 < (24 : ℕ) + x3.size) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), ((x4.any fun (x8 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.1 && PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.2) = Bool.true ↔ x2 x7) ∧ (¬x2 x7 → PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x5 = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x6 = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))))) := by
  have hMem : ∀ s : Fin (13 : ℕ), s.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔ s ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := by decide
  obtain ⟨x3, x4, x5, x6, hM, hHead, hNE, hSz, h5, h6, hBnd, hPos, hS5, hS6, hNeg⟩ := hEdgeTests
  have hEval := hMonoSound (fun u v => (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) x3 x4 x5 x6 hM hPos hS5 hS6 hNeg
  refine ⟨x3, x4, x5, x6, hM, hHead, hNE, hSz, h5, h6, hBnd, fun x7 => ?_⟩
  have hEq : (∃ (u v : Fin (12 : ℕ)),
      (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
      x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
      x7 (Fin.natAdd (12 : ℕ) v) = Bool.true) ↔
    (∃ (u v : Fin (12 : ℕ)),
      Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∧
      x7 (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
      x7 (Fin.natAdd (12 : ℕ) v) = Bool.true) :=
    exists_congr (fun u => exists_congr (fun v => and_congr_left' (hMem _)))
  exact ⟨(hEval x7).1.trans hEq, fun hn => (hEval x7).2 (fun h => hn (hEq.mp h))⟩
