import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18922_3
    (hCompile :
      ∀ (gs : List (Bool × ℕ × ℕ)) (out : ℕ),
        gs.length ≤ (32 : ℕ) →
        out < (27 : ℕ) + gs.length →
        (∀ j < gs.length,
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (27 : ℕ) + j ∧
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (27 : ℕ) + j) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) C ∧
          C.size ≤ (32 : ℕ) ∧
          C.output < (27 : ℕ) + C.size ∧
          ∀ (x : Fin (27 : ℕ) → Bool),
            PEqualNP.MetaComplexity.circuitFun (27 : ℕ) C x =
              (gs.foldl
                (fun (w : List Bool) (g : Bool × ℕ × ℕ) =>
                  w ++ [if g.1 = Bool.true then w.getD g.2.1 Bool.false && w.getD g.2.2 Bool.false else w.getD g.2.1 Bool.false || w.getD g.2.2 Bool.false])
                (List.ofFn x)).getD out Bool.false)
    (hCompiledExists :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4;
      ∃ (gs : List (Bool × ℕ × ℕ)) (out : ℕ),
        gs.length ≤ (32 : ℕ) ∧
        out < (27 : ℕ) + gs.length ∧
        (∀ j < gs.length,
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (27 : ℕ) + j ∧
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (27 : ℕ) + j) ∧
        (let evalGS : (Fin (27 : ℕ) → Bool) → Bool := fun x =>
          (gs.foldl
            (fun (w : List Bool) (g : Bool × ℕ × ℕ) =>
              w ++ [if g.1 = Bool.true then w.getD g.2.1 Bool.false && w.getD g.2.2 Bool.false else w.getD g.2.1 Bool.false || w.getD g.2.2 Bool.false])
            (List.ofFn x)).getD out Bool.false;
        (∀ (x5 x6 : Fin (13 : ℕ)), ↑x6 < (7 : ℕ) → x2 x5 x6 →
          evalGS (x3 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x5 ∨ x9 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧
        ∀ (x5 : Finset (Fin (13 : ℕ))),
          (¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) →
          (¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), (∀ x9 ∈ x5, ¬x2 x9 x8) → x2 x7 x8) →
          evalGS (x3 fun (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x5)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (Disjoint x5 (Finset.image (fun (x10 : Fin (13 : ℕ)) => x9 + x10) x1))) x8) = Bool.false)) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 ∧ x4.size ≤ (32 : ℕ) ∧ x4.output < (27 : ℕ) + x4.size ∧ (∀ (x5 x6 : Fin (13 : ℕ)), ↑x6 < (7 : ℕ) → x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x5 ∨ x9 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) → (¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), (∀ x9 ∈ x5, ¬x2 x9 x8) → x2 x7 x8) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x5)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (Disjoint x5 (Finset.image (fun (x10 : Fin (13 : ℕ)) => x9 + x10) x1))) x8) = Bool.false) := by
  rcases hCompiledExists with ⟨gs, out, hLen, hOut, hWF, hPos, hNeg⟩
  rcases hCompile gs out hLen hOut hWF with ⟨C, hMono, hRB, hSz, hCOut, hEq⟩
  refine ⟨C, hMono, hRB, hSz, hCOut, ?_, ?_⟩
  · intro x5 x6 hx6 hInc
    rw [hEq]
    exact hPos x5 x6 hx6 hInc
  · intro x5 h1 h2
    rw [hEq]
    exact hNeg x5 h1 h2
