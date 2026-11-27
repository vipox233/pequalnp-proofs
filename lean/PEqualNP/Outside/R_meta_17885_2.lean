import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17885_2
    (hPrependCleanEdge :
      have x2 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
        have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
        have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
        x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5];
      have x5 : ℕ → Prop := fun (x5 : ℕ) => (∃ (x6 : Fin (16 : ℕ)), x5.testBit ↑x6 = Bool.true) ∧ ∃ (x6 : Fin (24 : ℕ)), x5.testBit ((16 : ℕ) + ↑x6) = Bool.true;
      ∀ (init : List ℕ) (u v : ℕ),
        init.length = (11 : ℕ) → u < (11 : ℕ) → v < (11 : ℕ) →
        have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (List.foldl x2 init x3.gates).getD x4 (0 : ℕ);
        have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ × ℕ → ℕ := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ × ℕ) => x3 x4 x5.1 &&& x3 x4 x5.2;
        (∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)),
          PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 ∧
          x6.size + ((3 : ℕ) - PEqualNP.ReadTwo.nAnd x6) + (2 : ℕ) * x7.length ≤ (20 : ℕ) ∧
          (∀ x8 ∈ x7, x8.1 < (11 : ℕ) + x6.size ∧ x8.2 < (11 : ℕ) + x6.size) ∧
          (∀ x8 < x6.size, x5 (x3 x6 ((11 : ℕ) + x8))) ∧
          List.foldl (fun (x8 x9 : ℕ) => x8 ||| x9) (init.getD u (0 : ℕ) &&& init.getD v (0 : ℕ)) (List.map (x4 x6) x7) = (65535 : ℕ)) →
        ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)),
          PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 ∧ x7 ≠ [] ∧
          x6.size + ((3 : ℕ) - PEqualNP.ReadTwo.nAnd x6) + (2 : ℕ) * x7.length ≤ (22 : ℕ) ∧
          (∀ x8 ∈ x7, x8.1 < (11 : ℕ) + x6.size ∧ x8.2 < (11 : ℕ) + x6.size) ∧
          (∀ x8 < x6.size, x5 (x3 x6 ((11 : ℕ) + x8))) ∧
          List.foldl (fun (x8 x9 : ℕ) => x8 ||| x9) (0 : ℕ) (List.map (x4 x6) x7) = (65535 : ℕ))
    (hPeeledEdge :
      have x1 : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)];
      have x2 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
        have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
        have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
        x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5];
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (List.foldl x2 x1 x3.gates).getD x4 (0 : ℕ);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ × ℕ → ℕ := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ × ℕ) => x3 x4 x5.1 &&& x3 x4 x5.2;
      have x5 : ℕ → Prop := fun (x5 : ℕ) => (∃ (x6 : Fin (16 : ℕ)), x5.testBit ↑x6 = Bool.true) ∧ ∃ (x6 : Fin (24 : ℕ)), x5.testBit ((16 : ℕ) + ↑x6) = Bool.true;
      ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 ∧
        x6.size + ((3 : ℕ) - PEqualNP.ReadTwo.nAnd x6) + (2 : ℕ) * x7.length ≤ (20 : ℕ) ∧
        (∀ x8 ∈ x7, x8.1 < (11 : ℕ) + x6.size ∧ x8.2 < (11 : ℕ) + x6.size) ∧
        (∀ x8 < x6.size, x5 (x3 x6 ((11 : ℕ) + x8))) ∧
        List.foldl (fun (x8 x9 : ℕ) => x8 ||| x9) (32768 : ℕ) (List.map (x4 x6) x7) = (65535 : ℕ)) :
    have x1 : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]; have x2 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>   have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);   have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);   x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (List.foldl x2 x1 x3.gates).getD x4 (0 : ℕ); have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ × ℕ → ℕ := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ × ℕ) => x3 x4 x5.1 &&& x3 x4 x5.2; have x5 : ℕ → Prop := fun (x5 : ℕ) => (∃ (x6 : Fin (16 : ℕ)), x5.testBit ↑x6 = Bool.true) ∧ ∃ (x6 : Fin (24 : ℕ)), x5.testBit ((16 : ℕ) + ↑x6) = Bool.true; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 ∧ x7 ≠ [] ∧ x6.size + ((3 : ℕ) - PEqualNP.ReadTwo.nAnd x6) + (2 : ℕ) * x7.length ≤ (22 : ℕ) ∧ (∀ x8 ∈ x7, x8.1 < (11 : ℕ) + x6.size ∧ x8.2 < (11 : ℕ) + x6.size) ∧ (∀ x8 < x6.size, x5 (x3 x6 ((11 : ℕ) + x8))) ∧ List.foldl (fun (x8 x9 : ℕ) => x8 ||| x9) (0 : ℕ) (List.map (x4 x6) x7) = (65535 : ℕ) :=
  hPrependCleanEdge
    [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]
    (8 : ℕ) (9 : ℕ) rfl (by decide) (by decide) hPeeledEdge
