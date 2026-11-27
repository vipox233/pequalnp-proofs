import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18550_2
    (hLeftStarCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 ∧
        x1.size ≤ (22 : ℕ) ∧
        ∀ (x2 : Fin (13 : ℕ) → Bool),
          x1.eval (List.ofFn x2) = (x2 (0 : Fin (13 : ℕ)) && (x2 (7 : Fin (13 : ℕ)) || x2 (10 : Fin (13 : ℕ)) || x2 (12 : Fin (13 : ℕ))) ||
        x2 (1 : Fin (13 : ℕ)) && (x2 (7 : Fin (13 : ℕ)) || x2 (11 : Fin (13 : ℕ))) ||
        x2 (2 : Fin (13 : ℕ)) && (x2 (8 : Fin (13 : ℕ)) || x2 (12 : Fin (13 : ℕ))) ||
        x2 (3 : Fin (13 : ℕ)) && (x2 (7 : Fin (13 : ℕ)) || x2 (8 : Fin (13 : ℕ)) || x2 (9 : Fin (13 : ℕ))) ||
        x2 (4 : Fin (13 : ℕ)) && (x2 (9 : Fin (13 : ℕ)) || x2 (10 : Fin (13 : ℕ))) ||
        x2 (5 : Fin (13 : ℕ)) && (x2 (8 : Fin (13 : ℕ)) || x2 (10 : Fin (13 : ℕ)) || x2 (11 : Fin (13 : ℕ))) ||
        x2 (6 : Fin (13 : ℕ)) && (x2 (9 : Fin (13 : ℕ)) || x2 (11 : Fin (13 : ℕ)) || x2 (12 : Fin (13 : ℕ)))))
    (hLeftStarEquiv :
      ∀ (x2 : Fin (13 : ℕ) → Bool),
        (x2 (0 : Fin (13 : ℕ)) && (x2 (7 : Fin (13 : ℕ)) || x2 (10 : Fin (13 : ℕ)) || x2 (12 : Fin (13 : ℕ))) ||
        x2 (1 : Fin (13 : ℕ)) && (x2 (7 : Fin (13 : ℕ)) || x2 (11 : Fin (13 : ℕ))) ||
        x2 (2 : Fin (13 : ℕ)) && (x2 (8 : Fin (13 : ℕ)) || x2 (12 : Fin (13 : ℕ))) ||
        x2 (3 : Fin (13 : ℕ)) && (x2 (7 : Fin (13 : ℕ)) || x2 (8 : Fin (13 : ℕ)) || x2 (9 : Fin (13 : ℕ))) ||
        x2 (4 : Fin (13 : ℕ)) && (x2 (9 : Fin (13 : ℕ)) || x2 (10 : Fin (13 : ℕ))) ||
        x2 (5 : Fin (13 : ℕ)) && (x2 (8 : Fin (13 : ℕ)) || x2 (10 : Fin (13 : ℕ)) || x2 (11 : Fin (13 : ℕ))) ||
        x2 (6 : Fin (13 : ℕ)) && (x2 (9 : Fin (13 : ℕ)) || x2 (11 : Fin (13 : ℕ)) || x2 (12 : Fin (13 : ℕ)))) = (x2 (0 : Fin (13 : ℕ)) && x2 (7 : Fin (13 : ℕ)) || x2 (0 : Fin (13 : ℕ)) && x2 (10 : Fin (13 : ℕ)) || x2 (0 : Fin (13 : ℕ)) && x2 (12 : Fin (13 : ℕ)) || x2 (1 : Fin (13 : ℕ)) && x2 (7 : Fin (13 : ℕ)) || x2 (1 : Fin (13 : ℕ)) && x2 (11 : Fin (13 : ℕ)) || x2 (2 : Fin (13 : ℕ)) && x2 (8 : Fin (13 : ℕ)) || x2 (2 : Fin (13 : ℕ)) && x2 (12 : Fin (13 : ℕ)) || x2 (3 : Fin (13 : ℕ)) && x2 (7 : Fin (13 : ℕ)) || x2 (3 : Fin (13 : ℕ)) && x2 (8 : Fin (13 : ℕ)) || x2 (3 : Fin (13 : ℕ)) && x2 (9 : Fin (13 : ℕ)) || x2 (4 : Fin (13 : ℕ)) && x2 (9 : Fin (13 : ℕ)) || x2 (4 : Fin (13 : ℕ)) && x2 (10 : Fin (13 : ℕ)) || x2 (5 : Fin (13 : ℕ)) && x2 (8 : Fin (13 : ℕ)) || x2 (5 : Fin (13 : ℕ)) && x2 (10 : Fin (13 : ℕ)) || x2 (5 : Fin (13 : ℕ)) && x2 (11 : Fin (13 : ℕ)) || x2 (6 : Fin (13 : ℕ)) && x2 (9 : Fin (13 : ℕ)) || x2 (6 : Fin (13 : ℕ)) && x2 (11 : Fin (13 : ℕ)) || x2 (6 : Fin (13 : ℕ)) && x2 (12 : Fin (13 : ℕ)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (22 : ℕ) ∧ ∀ (x2 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (13 : ℕ)) && x2 (7 : Fin (13 : ℕ)) || x2 (0 : Fin (13 : ℕ)) && x2 (10 : Fin (13 : ℕ)) || x2 (0 : Fin (13 : ℕ)) && x2 (12 : Fin (13 : ℕ)) || x2 (1 : Fin (13 : ℕ)) && x2 (7 : Fin (13 : ℕ)) || x2 (1 : Fin (13 : ℕ)) && x2 (11 : Fin (13 : ℕ)) || x2 (2 : Fin (13 : ℕ)) && x2 (8 : Fin (13 : ℕ)) || x2 (2 : Fin (13 : ℕ)) && x2 (12 : Fin (13 : ℕ)) || x2 (3 : Fin (13 : ℕ)) && x2 (7 : Fin (13 : ℕ)) || x2 (3 : Fin (13 : ℕ)) && x2 (8 : Fin (13 : ℕ)) || x2 (3 : Fin (13 : ℕ)) && x2 (9 : Fin (13 : ℕ)) || x2 (4 : Fin (13 : ℕ)) && x2 (9 : Fin (13 : ℕ)) || x2 (4 : Fin (13 : ℕ)) && x2 (10 : Fin (13 : ℕ)) || x2 (5 : Fin (13 : ℕ)) && x2 (8 : Fin (13 : ℕ)) || x2 (5 : Fin (13 : ℕ)) && x2 (10 : Fin (13 : ℕ)) || x2 (5 : Fin (13 : ℕ)) && x2 (11 : Fin (13 : ℕ)) || x2 (6 : Fin (13 : ℕ)) && x2 (9 : Fin (13 : ℕ)) || x2 (6 : Fin (13 : ℕ)) && x2 (11 : Fin (13 : ℕ)) || x2 (6 : Fin (13 : ℕ)) && x2 (12 : Fin (13 : ℕ)))) :=
  Exists.elim hLeftStarCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, fun x => (hC.2.2 x).trans (hLeftStarEquiv x)⟩
