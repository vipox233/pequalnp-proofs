import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18652_1
    (hFullCircuit :
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x5 ∧
        x5.output < (17 : ℕ) + x5.size ∧
        x5.size ≤ (28 : ℕ) ∧
        ∀ (v : Fin (17 : ℕ) → Bool),
          x5.eval (List.ofFn v) = Bool.true ↔
            ∃ (p : Fin (6 : ℕ)) (q : Fin (11 : ℕ)),
              ([(71 : ℕ), (282 : ℕ), (564 : ℕ), (1128 : ℕ), (417 : ℕ), (1666 : ℕ)].getD p.val (0 : ℕ)).testBit q.val = Bool.true ∧
              v (Fin.castAdd (11 : ℕ) p) = Bool.true ∧
              v (Fin.natAdd (6 : ℕ) q) = Bool.true)
    (hOrbitSound :
      have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))];
      have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>
        have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);
        Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1);
      have x4 : List (Fin (26 : ℕ)) := List.filter (fun (x4 : Fin (26 : ℕ)) => Decidable.decide (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (11 : ℕ), (13 : ℕ), (15 : ℕ)])) (List.finRange (26 : ℕ));
      ∀ (eval : List Bool → Bool),
        (∀ (v : Fin (17 : ℕ) → Bool),
          eval (List.ofFn v) = Bool.true ↔
            ∃ (p : Fin (6 : ℕ)) (q : Fin (11 : ℕ)),
              ([(71 : ℕ), (282 : ℕ), (564 : ℕ), (1128 : ℕ), (417 : ℕ), (1666 : ℕ)].getD p.val (0 : ℕ)).testBit q.val = Bool.true ∧
              v (Fin.castAdd (11 : ℕ) p) = Bool.true ∧
              v (Fin.natAdd (6 : ℕ) q) = Bool.true) →
        (∀ (x6 x7 : Fin (13 : ℕ)),
          x6.val ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (11 : ℕ)] →
          (x6 - x7).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] →
          eval (List.map (fun (x10 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) x4) = Bool.true) ∧
        ∀ x6 ∈ x2, ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool),
          eval (List.map (x3 x6 x8 x10 x11) x4) = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); have x4 : List (Fin (26 : ℕ)) := List.filter (fun (x4 : Fin (26 : ℕ)) => Decidable.decide (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (11 : ℕ), (13 : ℕ), (15 : ℕ)])) (List.finRange (26 : ℕ)); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.output < (17 : ℕ) + x5.size ∧ x5.size ≤ (28 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∉ x1 ∪ {(2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ))} → x6 - x7 ∈ x1 → x5.eval (List.map (fun (x10 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) x4) = Bool.true) ∧ ∀ x6 ∈ x2, ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool), x5.eval (List.map (x3 x6 x8 x10 x11) x4) = Bool.false) := by
  have hPosConv : ∀ (a b : Fin (13 : ℕ)),
      a ∉ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∪ {(2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ))} →
      a - b ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) →
      a.val ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (11 : ℕ)] ∧
      (a - b).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] := by decide
  exact Exists.elim hFullCircuit fun C hC =>
    have hs := hOrbitSound C.eval hC.2.2.2
    ⟨C, hC.1, hC.2.1, hC.2.2.1,
      fun a b ha hb => hs.1 a b (hPosConv a b ha hb).1 (hPosConv a b ha hb).2,
      hs.2⟩
