import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17361_2
    (hSmallSize :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.MetaComplexity.Monotone2 x1 ∧
          x1.size < (5 : ℕ) ∧
          (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 →
            x1.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) ∧
          (∀ (x7 x8 : Finset (Fin (13 : ℕ))),
            x1.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.true →
            PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x7 x8 = Bool.true)) →
        False)
    (hSizeGe5 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.MetaComplexity.Monotone2 x1 ∧
          (5 : ℕ) ≤ x1.size ∧
          x1.size < (64 : ℕ) ∧
          ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (1 : ℕ) ∧
          ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) ∧
          (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 →
            x1.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) ∧
          (∀ (x7 x8 : Finset (Fin (13 : ℕ))),
            x1.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.true →
            PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x7 x8 = Bool.true)) →
        ∃ (x8 : Bool) (x9 : Fin (13 : ℕ)) (x10 : (x10 : Fin (5 : ℕ)) → Fin (x1.size - ↑x10)) (x11 : Fin (5 : ℕ) → ℕ),
          have x12 : PEqualNP.CircuitLowerBounds.Circuit := List.foldl (fun (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : Fin (5 : ℕ)) => PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x12 (↑(x10 x13)) (x11 x13)) x1 (List.finRange (5 : ℕ));
          ∀ (x13 x14 : Finset (Fin (13 : ℕ))), (if x8 = Bool.true then x9 ∉ x13 else x9 ∉ x14) → x12.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = x1.eval (PEqualNP.GenericRejection.incidenceInput x13 x14)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size < (64 : ℕ) →       ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (1 : ℕ) →         ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) →           (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) →             (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x1.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x7 x8 = Bool.true) →               ∃ (x8 : Bool) (x9 : Fin (13 : ℕ)) (x10 : (x10 : Fin (5 : ℕ)) → Fin (x1.size - ↑x10)) (x11 : Fin (5 : ℕ) → ℕ),                 have x12 : PEqualNP.CircuitLowerBounds.Circuit := List.foldl (fun (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : Fin (5 : ℕ)) => PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x12 (↑(x10 x13)) (x11 x13)) x1 (List.finRange (5 : ℕ));                 ∀ (x13 x14 : Finset (Fin (13 : ℕ))), (if x8 = Bool.true then x9 ∉ x13 else x9 ∉ x14) → x12.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = x1.eval (PEqualNP.GenericRejection.incidenceInput x13 x14)) :=
  fun x1 hM hSz hD1 hD2 hPos hSound =>
    Or.elim (Nat.lt_or_ge x1.size (5 : ℕ))
      (fun hLt5 => False.elim (hSmallSize x1 ⟨hM, hLt5, hPos, hSound⟩))
      (fun hGe5 => hSizeGe5 x1 ⟨hM, hGe5, hSz, hD1, hD2, hPos, hSound⟩)
