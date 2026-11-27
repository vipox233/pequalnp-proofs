import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17729_2
    (hBitParallelWitness :
      have cols : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)];
      have x4 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];
      have step : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (a : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
        have v0 : ℕ := a.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
        have v1 : ℕ := a.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
        a ++ [if g.op.eval [Bool.false, Bool.true] = Bool.true then v0 ||| v1 else v0 &&& v1];
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)) (x3 : Finset (Fin (11 : ℕ))),
        have wv : ℕ → ℕ := fun (w : ℕ) => (List.foldl step cols x1.gates).getD w (0 : ℕ);
        have cov : ℕ := List.foldl (fun (a : ℕ) (p : ℕ × ℕ) => a ||| (wv p.1 &&& wv p.2)) (0 : ℕ) x2;
        have uncov : List (Fin (16 : ℕ)) := List.filter (fun (i : Fin (16 : ℕ)) => !cov.testBit ↑i) (List.finRange (16 : ℕ));
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧
        x2 ≠ [] ∧
        (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧
        x1.size + (2 : ℕ) * x2.length + uncov.length + x3.card ≤ (22 : ℕ) ∧
        (∀ i ∈ uncov, ∃ x11 ∈ x3, (x4.getD ↑i (0 : ℕ)).testBit ↑x11 = Bool.true) ∧
        (∀ x9 ∈ x2, x9.1 < (11 : ℕ) + x1.size ∧ x9.2 < (11 : ℕ) + x1.size ∧ ((11 : ℕ) ≤ x9.1 ∨ (11 : ℕ) ≤ x9.2)) ∧
        (∀ x9 < x1.size, wv ((11 : ℕ) + x9) &&& (65535 : ℕ) ≠ (0 : ℕ) ∧ wv ((11 : ℕ) + x9) &&& (1099511562240 : ℕ) ≠ (0 : ℕ)) ∧
        (∀ x9 < x1.size, PEqualNP.ReadTwo.isAnd x1 x9 → ∃ x12 ∈ x2, ∃ x13 ∈ [x12.1, x12.2], x13 = (11 : ℕ) + x9 ∨ (11 : ℕ) ≤ x13 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x9 (x13 - (11 : ℕ))) ∧
        cov &&& (1099511562240 : ℕ) = (0 : ℕ))
    (hBitBridge :
      ∀ (cols x4 x5 : List ℕ) (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),
        cols.length = (11 : ℕ) →
        x4.length = (16 : ℕ) →
        x5.length = (24 : ℕ) →
        (∀ (i : Fin (11 : ℕ)) (j : Fin (40 : ℕ)), (cols.getD ↑i (0 : ℕ)).testBit ↑j = ((x4 ++ x5).getD ↑j (0 : ℕ)).testBit ↑i) →
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 →
        (∀ x9 ∈ x2, x9.1 < (11 : ℕ) + x1.size ∧ x9.2 < (11 : ℕ) + x1.size) →
        have step : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (a : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
          have v0 : ℕ := a.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
          have v1 : ℕ := a.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
          a ++ [if g.op.eval [Bool.false, Bool.true] = Bool.true then v0 ||| v1 else v0 &&& v1];
        have wv : ℕ → ℕ := fun (w : ℕ) => (List.foldl step cols x1.gates).getD w (0 : ℕ);
        have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) x7;
        have x7 : ℕ → Bool := fun (x7 : ℕ) => x2.any fun (x8 : ℕ × ℕ) => x6 x7 x8.1 && x6 x7 x8.2;
        have cov : ℕ := List.foldl (fun (a : ℕ) (p : ℕ × ℕ) => a ||| (wv p.1 &&& wv p.2)) (0 : ℕ) x2;
        (∀ x9 < x1.size, wv ((11 : ℕ) + x9) &&& (65535 : ℕ) ≠ (0 : ℕ) → (x4.any fun (x11 : ℕ) => x6 x11 ((11 : ℕ) + x9)) = Bool.true) ∧
        (∀ x9 < x1.size, wv ((11 : ℕ) + x9) &&& (1099511562240 : ℕ) ≠ (0 : ℕ) → (x5.any fun (x11 : ℕ) => x6 x11 ((11 : ℕ) + x9)) = Bool.true) ∧
        (cov &&& (1099511562240 : ℕ) = (0 : ℕ) → ∀ x9 ∈ x5, x7 x9 = Bool.false) ∧
        List.filter (fun (x8 : ℕ) => !x7 x8) x4 = List.map (fun (i : Fin (16 : ℕ)) => x4.getD ↑i (0 : ℕ)) (List.filter (fun (i : Fin (16 : ℕ)) => !cov.testBit ↑i) (List.finRange (16 : ℕ)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)) (x3 : Finset (Fin (11 : ℕ))),   have x4 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x5 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) x7;   have x7 : ℕ → Bool := fun (x7 : ℕ) => x2.any fun (x8 : ℕ × ℕ) => x6 x7 x8.1 && x6 x7 x8.2;   have x8 : List ℕ := List.filter (fun (x8 : ℕ) => !x7 x8) x4;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ x1.size + (2 : ℕ) * x2.length + x8.length + x3.card ≤ (22 : ℕ) ∧ (∀ x9 ∈ x8, ∃ x11 ∈ x3, x9.testBit ↑x11 = Bool.true) ∧ (∀ x9 ∈ x2, x9.1 < (11 : ℕ) + x1.size ∧ x9.2 < (11 : ℕ) + x1.size ∧ ((11 : ℕ) ≤ x9.1 ∨ (11 : ℕ) ≤ x9.2)) ∧ (∀ x9 < x1.size, (x4.any fun (x11 : ℕ) => x6 x11 ((11 : ℕ) + x9)) = Bool.true ∧ (x5.any fun (x11 : ℕ) => x6 x11 ((11 : ℕ) + x9)) = Bool.true) ∧ (∀ x9 < x1.size, PEqualNP.ReadTwo.isAnd x1 x9 → ∃ x12 ∈ x2, ∃ x13 ∈ [x12.1, x12.2], x13 = (11 : ℕ) + x9 ∨ (11 : ℕ) ≤ x13 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x9 (x13 - (11 : ℕ))) ∧ ∀ x9 ∈ x5, x7 x9 = Bool.false) := by
  rcases hBitParallelWitness with ⟨x1, x2, x3, hAO, hNe, hAnd, hBud, hCov, hPairs, hAct, hCone, hZero⟩
  have hB := hBitBridge [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)] [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)] x1 x2 rfl rfl rfl (by decide) hAO (fun p hp => ⟨(hPairs p hp).1, (hPairs p hp).2.1⟩)
  refine ⟨x1, x2, x3, hAO, hNe, hAnd, ?_, ?_, hPairs, ?_, hCone, hB.2.2.1 hZero⟩
  · simpa only [hB.2.2.2, List.length_map] using hBud
  · intro x9 hx9
    rw [hB.2.2.2, List.mem_map] at hx9
    rcases hx9 with ⟨i, hi, rfl⟩
    exact hCov i hi
  · intro x9 hx9
    exact ⟨hB.1 x9 hx9 (hAct x9 hx9).1, hB.2.1 x9 hx9 (hAct x9 hx9).2⟩
