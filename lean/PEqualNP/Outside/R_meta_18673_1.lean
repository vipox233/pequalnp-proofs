import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18673_1
    (hBoolDAG :
      have x1 : List (ℕ × ℕ) → Bool × ℕ × ℕ → List (ℕ × ℕ) := fun (w : List (ℕ × ℕ)) (g : Bool × ℕ × ℕ) =>
        have a : ℕ × ℕ := w.getD g.2.1 ((0 : ℕ), (0 : ℕ))
        have b : ℕ × ℕ := w.getD g.2.2 ((0 : ℕ), (0 : ℕ))
        w ++ [(if g.1 = Bool.true then a.1 ||| b.1 else a.1 &&& b.1, a.2 + b.2)]
      have x2 : List (ℕ × ℕ) := List.map (fun (m : ℕ) => (m, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]
      have x3 : ℕ × ℕ → Prop := fun (p : ℕ × ℕ) => (∑ k : Fin (39 : ℕ), if p.1.testBit ((21 : ℕ) + ↑k) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑k / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑k % (15 : ℕ))) % (16 : ℕ)) ≤ (4 : ℕ) * p.2
      ∃ (p : List (Bool × ℕ × ℕ)) (i j : ℕ),
        p.length ≤ (26 : ℕ) ∧
        (∀ (k : Fin p.length),
          have g : Bool × ℕ × ℕ := p.getD ↑k (Bool.false, (0 : ℕ), (0 : ℕ))
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (14 : ℕ) + ↑k ∧ g.2.2 < (14 : ℕ) + ↑k) ∧
        i < j ∧
        j < (14 : ℕ) + p.length ∧
        have w : List (ℕ × ℕ) := List.foldl x1 x2 p
        have a : ℕ × ℕ := w.getD i ((0 : ℕ), (0 : ℕ))
        have b : ℕ × ℕ := w.getD j ((0 : ℕ), (0 : ℕ))
        a.1 &&& b.1 = (2097151 : ℕ) ∧ a.1 >>> (58 : ℕ) = (0 : ℕ) ∧ b.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 a ∧ x3 b)
    (hCompile :
      ∀ (init : List (ℕ × ℕ)) (p : List (Bool × ℕ × ℕ)),
        List.foldl (fun (w : List (ℕ × ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate) =>
          have a : ℕ × ℕ := w.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ))
          have b : ℕ × ℕ := w.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ))
          w ++ [(if g.op.eval [Bool.false, Bool.true] = Bool.true then a.1 ||| b.1 else a.1 &&& b.1, a.2 + b.2)])
          init (p.map fun (g : Bool × ℕ × ℕ) => { op := if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [g.2.1, g.2.2] : PEqualNP.CircuitLowerBounds.Gate }) =
        List.foldl (fun (w : List (ℕ × ℕ)) (g : Bool × ℕ × ℕ) =>
          have a : ℕ × ℕ := w.getD g.2.1 ((0 : ℕ), (0 : ℕ))
          have b : ℕ × ℕ := w.getD g.2.2 ((0 : ℕ), (0 : ℕ))
          w ++ [(if g.1 = Bool.true then a.1 ||| b.1 else a.1 &&& b.1, a.2 + b.2)])
          init p) :
    (have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]; have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) => (∑ x4 : Fin (39 : ℕ), if x3.1.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ)) ≤ (4 : ℕ) * x3.2; ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),   x4.length ≤ (26 : ℕ) ∧     (∀ (x7 : Fin x4.length),         have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.getD ↑x7 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };         (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x8.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + ↑x7 ∧ x10 < (14 : ℕ) + ↑x7) ∧       x5 < x6 ∧         x6 < (14 : ℕ) + x4.length ∧           have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4;           have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ));           have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ));           x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 x8 ∧ x3 x9) := by
  obtain ⟨p, i, j, hLen, hBnd, hij, hj, hAnd, hSh8, hSh9, hW8, hW9⟩ := hBoolDAG
  let toG : Bool × ℕ × ℕ → PEqualNP.CircuitLowerBounds.Gate := fun g =>
    { op := if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [g.2.1, g.2.2] }
  refine ⟨p.map toG, i, j, ?_, ?_, hij, ?_, ?_⟩
  · rw [List.length_map]; exact hLen
  · intro k
    have hk : k.val < p.length := by rw [← List.length_map toG]; exact k.isLt
    have hget : (p.map toG).getD k.val { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } = toG (p.getD k.val (Bool.false, (0 : ℕ), (0 : ℕ))) := by
      rw [List.getD_eq_getElem _ _ k.isLt, List.getD_eq_getElem _ _ hk, List.getElem_map]
    dsimp only
    rw [hget]
    refine ⟨?_, (p.getD k.val (Bool.false, (0 : ℕ), (0 : ℕ))).2.1, (p.getD k.val (Bool.false, (0 : ℕ), (0 : ℕ))).2.2, rfl, hBnd ⟨k.val, hk⟩⟩
    by_cases hg : (p.getD k.val (Bool.false, (0 : ℕ), (0 : ℕ))).1 = Bool.true
    · exact Or.inr (ite_eq_left_iff.mpr (fun h => False.elim (h hg)))
    · exact Or.inl (ite_eq_right_iff.mpr (fun h => False.elim (hg h)))
  · rw [List.length_map]; exact hj
  · dsimp only
    rw [hCompile _ p]
    exact ⟨hAnd, hSh8, hSh9, hW8, hW9⟩
