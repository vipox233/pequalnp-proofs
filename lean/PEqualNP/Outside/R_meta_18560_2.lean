import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18560_2
    (hCompileFormula :
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit)
        (x6 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)),
        PEqualNP.TopForm.IsAO2 (10 : ℕ) x2 →
        x2.size ≤ (12 : ℕ) →
        x6.leaves ≤ (7 : ℕ) →
        ∃ (c : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsAO2 (10 : ℕ) c ∧ c.size ≤ (18 : ℕ) ∧
          ∀ (x8 : Fin (10 : ℕ) → Bool),
            have x9 : Fin ((10 : ℕ) + x2.size) → Bool := fun (x9 : Fin ((10 : ℕ) + x2.size)) =>
              (x2.wires (List.ofFn x8)).getD (↑x9) Bool.false
            c.eval (List.ofFn x8) =
              PEqualNP.MetaComplexity.DMFormula.rec
                (fun (x10 : Fin ((10 : ℕ) + x2.size)) (_ : Bool) => x9 x10)
                (fun (_ _ : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)) (a b : Bool) => a && b)
                (fun (_ _ : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)) (a b : Bool) => a || b)
                x6)
    (hNoCircuit18 :
      ∀ (x1 : Fin (11 : ℕ)) (c : PEqualNP.CircuitLowerBounds.Circuit),
        ↑x1 < (4 : ℕ) →
        PEqualNP.TopForm.IsAO2 (10 : ℕ) c →
        c.size ≤ (18 : ℕ) →
        ∃ (x8 : Fin (10 : ℕ) → Bool),
          c.eval (List.ofFn x8) ≠
            have x10 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x8
            [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
             (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any
              fun (x11 : ℕ) => x10 (Fin.ofNat (11 : ℕ) (x11 / (11 : ℕ))) && x10 (Fin.ofNat (11 : ℕ) (x11 % (11 : ℕ)))) :
    (∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (10 : ℕ) x2 →       x2.size ≤ (12 : ℕ) →         ∀ (x6 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)),           x6.leaves ≤ (7 : ℕ) →             ∃ (x8 : Fin (10 : ℕ) → Bool),               have x9 : Fin ((10 : ℕ) + x2.size) → Bool := fun (x9 : Fin ((10 : ℕ) + x2.size)) => (x2.wires (List.ofFn x8)).getD (↑x9) Bool.false;               PEqualNP.MetaComplexity.DMFormula.rec (fun (x10 : Fin ((10 : ℕ) + x2.size)) (x11 : Bool) => x9 x10) (fun (x10 x11 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)) (x12 x13 : Bool) => x12 && x13) (fun (x10 x11 : PEqualNP.MetaComplexity.DMFormula ((10 : ℕ) + x2.size)) (x12 x13 : Bool) => x12 || x13) x6 ≠                 have x10 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x8;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (11 : ℕ) (x11 / (11 : ℕ))) && x10 (Fin.ofNat (11 : ℕ) (x11 % (11 : ℕ)))) :=
  fun x1 x2 hLt hAO hSz x6 hL =>
    (hCompileFormula x2 x6 hAO hSz hL).elim fun c hc =>
      (hNoCircuit18 x1 c hLt hc.1 hc.2.1).elim fun x8 hx8 =>
        ⟨x8, fun hEq => hx8 ((hc.2.2 x8).trans hEq)⟩
