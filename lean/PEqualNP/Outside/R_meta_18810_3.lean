import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18810_3
    (hCompile :
      ∀ (gs : List (Bool × ℕ × ℕ)) (out : ℕ),
        gs.length ≤ (62 : ℕ) →
        out < (26 : ℕ) + gs.length →
        (∀ j < gs.length,
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 ≠ (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (26 : ℕ) + j ∧
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (26 : ℕ) + j) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          C.size ≤ (62 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
          (∀ g ∈ C.gates, g.inputs.Nodup) ∧
          C.output < (26 : ℕ) + C.size ∧
          ∀ (x : List Bool),
            C.eval x =
              (gs.foldl
                (fun (w : List Bool) (g : Bool × ℕ × ℕ) =>
                  w ++ [if g.1 = Bool.true then w.getD g.2.1 Bool.false && w.getD g.2.2 Bool.false else w.getD g.2.1 Bool.false || w.getD g.2.2 Bool.false])
                x).getD out Bool.false)
    (hCompiledExists :
      have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))));
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4;
      have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      ∃ (gs : List (Bool × ℕ × ℕ)) (out : ℕ),
        gs.length ≤ (62 : ℕ) ∧
        out < (26 : ℕ) + gs.length ∧
        (∀ j < gs.length,
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 ≠ (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (26 : ℕ) + j ∧
          (gs.getD j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (26 : ℕ) + j) ∧
        (let evalGS : List Bool → Bool := fun x =>
          (gs.foldl
            (fun (w : List Bool) (g : Bool × ℕ × ℕ) =>
              w ++ [if g.1 = Bool.true then w.getD g.2.1 Bool.false && w.getD g.2.2 Bool.false else w.getD g.2.1 Bool.false || w.getD g.2.2 Bool.false])
            x).getD out Bool.false;
        (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → evalGS (x2 (x3 x5) (x3 x6)) = Bool.true) ∧
        (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) →
          evalGS (x2 x5 (x1 x5)) = Bool.false ∧
          evalGS (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧
        ∀ (x5 : Bool), evalGS (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ))) = Bool.false)) :
    (have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (62 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧ (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧ x4.output < (26 : ℕ) + x4.size ∧ ∀ (x5 : Bool), x4.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ))) = Bool.false) := by
  rcases hCompiledExists with ⟨gs, out, hLen, hOut, hWF, hPos, hNeg, hSingle⟩
  rcases hCompile gs out hLen hOut hWF with ⟨C, hSz, hAO, hNd, hCOut, hEq⟩
  refine ⟨C, hSz, hAO, hNd, ?_, ?_, hCOut, ?_⟩
  · intro x5 x6 hx
    rw [hEq]
    exact hPos x5 x6 hx
  · intro x5 hx5
    rw [hEq, hEq]
    exact hNeg x5 hx5
  · intro b
    rw [hEq]
    exact hSingle b
