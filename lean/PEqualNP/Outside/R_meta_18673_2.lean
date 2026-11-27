import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18673_2
    (hSumEquiv : ∀ (f : Fin (39 : ℕ) → ℕ),
      (∑ x4 : Fin (39 : ℕ), f x4) = ((List.finRange (39 : ℕ)).map f).sum)
    (hListWitness : have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>
        have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));
        have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));
        x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)];
      have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)];
      have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) => ((List.finRange (39 : ℕ)).map fun (x4 : Fin (39 : ℕ)) => if x3.1.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ)).sum ≤ (4 : ℕ) * x3.2;
      ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),
        x4.length ≤ (26 : ℕ) ∧
          (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate),
            x4[x7]? = Option.some x8 →
              (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x8.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + x7 ∧ x10 < (14 : ℕ) + x7) ∧
            x5 < x6 ∧ x6 < (14 : ℕ) + x4.length ∧
              have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4;
              have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ));
              have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ));
              x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 x8 ∧ x3 x9) :
    (have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]; have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) => (∑ x4 : Fin (39 : ℕ), if x3.1.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ)) ≤ (4 : ℕ) * x3.2; ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),   x4.length ≤ (26 : ℕ) ∧     (∀ (x7 : Fin x4.length),         have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.getD ↑x7 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };         (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x8.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + ↑x7 ∧ x10 < (14 : ℕ) + ↑x7) ∧       x5 < x6 ∧         x6 < (14 : ℕ) + x4.length ∧           have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4;           have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ));           have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ));           x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 x8 ∧ x3 x9) :=
  Exists.elim hListWitness fun x4 h1 =>
  Exists.elim h1 fun x5 h2 =>
  Exists.elim h2 fun x6 h =>
    ⟨x4, x5, x6, h.1,
      fun x7 => by
        have h7 := h.2.1 x7.1 x4[x7.1] (List.getElem?_eq_getElem x7.isLt)
        dsimp only; rw [List.getD_eq_getElem _ _ x7.isLt]; exact h7,
      h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      by have hW8 := h.2.2.2.2.2.2.2.1; dsimp only at hW8 ⊢; rw [hSumEquiv]; exact hW8,
      by have hW9 := h.2.2.2.2.2.2.2.2; dsimp only at hW9 ⊢; rw [hSumEquiv]; exact hW9⟩
