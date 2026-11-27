import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8407_3
    (hStarCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 : ℕ) x1 ∧
        x1.output < (21 : ℕ) + x1.size ∧
        x1.size ≤ (33 : ℕ) ∧
        ∀ (x2 : Fin (21 : ℕ) → Bool),
          x1.eval (List.ofFn x2) =
            ((x2 (0 : Fin (21 : ℕ)) && (x2 (14 : Fin (21 : ℕ)) || x2 (7 : Fin (21 : ℕ)) || x2 (8 : Fin (21 : ℕ)) || x2 (12 : Fin (21 : ℕ)))) ||
             (x2 (1 : Fin (21 : ℕ)) && (x2 (15 : Fin (21 : ℕ)) || x2 (8 : Fin (21 : ℕ)) || x2 (9 : Fin (21 : ℕ)) || x2 (13 : Fin (21 : ℕ)))) ||
             (x2 (2 : Fin (21 : ℕ)) && (x2 (16 : Fin (21 : ℕ)) || x2 (9 : Fin (21 : ℕ)) || x2 (10 : Fin (21 : ℕ)) || x2 (7 : Fin (21 : ℕ)))) ||
             (x2 (3 : Fin (21 : ℕ)) && (x2 (17 : Fin (21 : ℕ)) || x2 (10 : Fin (21 : ℕ)) || x2 (11 : Fin (21 : ℕ)) || x2 (8 : Fin (21 : ℕ)))) ||
             (x2 (4 : Fin (21 : ℕ)) && (x2 (18 : Fin (21 : ℕ)) || x2 (11 : Fin (21 : ℕ)) || x2 (12 : Fin (21 : ℕ)) || x2 (9 : Fin (21 : ℕ)))) ||
             (x2 (5 : Fin (21 : ℕ)) && (x2 (19 : Fin (21 : ℕ)) || x2 (12 : Fin (21 : ℕ)) || x2 (13 : Fin (21 : ℕ)) || x2 (10 : Fin (21 : ℕ)))) ||
             (x2 (6 : Fin (21 : ℕ)) && (x2 (20 : Fin (21 : ℕ)) || x2 (13 : Fin (21 : ℕ)) || x2 (7 : Fin (21 : ℕ)) || x2 (11 : Fin (21 : ℕ))))))
    (hStarEquiv :
      ∀ (x2 : Fin (21 : ℕ) → Bool),
        ((x2 (0 : Fin (21 : ℕ)) && (x2 (14 : Fin (21 : ℕ)) || x2 (7 : Fin (21 : ℕ)) || x2 (8 : Fin (21 : ℕ)) || x2 (12 : Fin (21 : ℕ)))) ||
         (x2 (1 : Fin (21 : ℕ)) && (x2 (15 : Fin (21 : ℕ)) || x2 (8 : Fin (21 : ℕ)) || x2 (9 : Fin (21 : ℕ)) || x2 (13 : Fin (21 : ℕ)))) ||
         (x2 (2 : Fin (21 : ℕ)) && (x2 (16 : Fin (21 : ℕ)) || x2 (9 : Fin (21 : ℕ)) || x2 (10 : Fin (21 : ℕ)) || x2 (7 : Fin (21 : ℕ)))) ||
         (x2 (3 : Fin (21 : ℕ)) && (x2 (17 : Fin (21 : ℕ)) || x2 (10 : Fin (21 : ℕ)) || x2 (11 : Fin (21 : ℕ)) || x2 (8 : Fin (21 : ℕ)))) ||
         (x2 (4 : Fin (21 : ℕ)) && (x2 (18 : Fin (21 : ℕ)) || x2 (11 : Fin (21 : ℕ)) || x2 (12 : Fin (21 : ℕ)) || x2 (9 : Fin (21 : ℕ)))) ||
         (x2 (5 : Fin (21 : ℕ)) && (x2 (19 : Fin (21 : ℕ)) || x2 (12 : Fin (21 : ℕ)) || x2 (13 : Fin (21 : ℕ)) || x2 (10 : Fin (21 : ℕ)))) ||
         (x2 (6 : Fin (21 : ℕ)) && (x2 (20 : Fin (21 : ℕ)) || x2 (13 : Fin (21 : ℕ)) || x2 (7 : Fin (21 : ℕ)) || x2 (11 : Fin (21 : ℕ))))) =
        ((List.flatMap (fun (x3 : ℕ) => List.map (fun (x4 : ℕ) => (Fin.ofNat (21 : ℕ) x3, Fin.ofNat (21 : ℕ) x4)) [(14 : ℕ) + x3, (7 : ℕ) + x3, (7 : ℕ) + (x3 + (1 : ℕ)) % (7 : ℕ), (7 : ℕ) + (x3 + (5 : ℕ)) % (7 : ℕ)]) (List.range (7 : ℕ))).any fun (x3 : Fin (21 : ℕ) × Fin (21 : ℕ)) => x2 x3.1 && x2 x3.2)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 : ℕ) x1 ∧ x1.output < (21 : ℕ) + x1.size ∧ x1.size ≤ (33 : ℕ) ∧ ∀ (x2 : Fin (21 : ℕ) → Bool), x1.eval (List.ofFn x2) = (List.flatMap (fun (x3 : ℕ) => List.map (fun (x4 : ℕ) => (Fin.ofNat (21 : ℕ) x3, Fin.ofNat (21 : ℕ) x4)) [(14 : ℕ) + x3, (7 : ℕ) + x3, (7 : ℕ) + (x3 + (1 : ℕ)) % (7 : ℕ), (7 : ℕ) + (x3 + (5 : ℕ)) % (7 : ℕ)]) (List.range (7 : ℕ))).any fun (x3 : Fin (21 : ℕ) × Fin (21 : ℕ)) => x2 x3.1 && x2 x3.2) :=
  Exists.elim hStarCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, fun x => (hC.2.2.2.2 x).trans (hStarEquiv x)⟩
