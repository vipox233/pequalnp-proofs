import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7977_3
    (hUnpackThree :
      ∀ (P : ℕ → Prop) (s : Finset ℕ),
        s.card = (3 : ℕ) → (∀ k ∈ s, P k) →
        ∃ (g1 g2 g3 : ℕ), g1 < g2 ∧ g2 < g3 ∧ P g1 ∧ P g2 ∧ P g3)
    (hOrderedWiresAndGates :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        let x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
        let x9 : ℕ → List Bool → Prop :=
          fun (w : ℕ) (inp : List Bool) =>
            ∃ g < x1.size,
              PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 w g ∧
              (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
              PEqualNP.CircuitLowerBounds.wireValue x1 inp ((26 : ℕ) + g) = Bool.true;
        let x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
          fun (w : ℕ) (p l : Fin (13 : ℕ)) => x9 w (PEqualNP.GenericRejection.incidenceInput {p} {l});
        let isNestedAnd : ℕ → Prop :=
          fun (k : ℕ) =>
            k < x1.size ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt x1 k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            ∃ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 k).inputs,
              (26 : ℕ) ≤ u ∧
              (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (u - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        (PEqualNP.MetaComplexity.Monotone2 x1 ∧
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 ∧
         (26 : ℕ) ≤ x2 ∧ x2 < x3 ∧ x3 < (26 : ℕ) + x1.size ∧
         (∀ (p l : Fin (13 : ℕ)), p ∈ x8 l → x10 x2 p l ∨ x10 x3 p l) ∧
         (∀ (q : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 q →
           ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput q (PEqualNP.HeptadCover.missLines x8 q)) ∨
             x9 x3 (PEqualNP.GenericRejection.incidenceInput q (PEqualNP.HeptadCover.missLines x8 q)))) ∧
         (∃ (p l : Fin (13 : ℕ)), p ∈ x8 l ∧ x10 x2 p l ∧ ¬x10 x3 p l) ∧
         (∃ (p l : Fin (13 : ℕ)), p ∈ x8 l ∧ x10 x3 p l ∧ ¬x10 x2 p l) ∧
         (∃ (g1 g2 g3 : ℕ), g1 < g2 ∧ g2 < g3 ∧ isNestedAnd g1 ∧ isNestedAnd g2 ∧ isNestedAnd g3)) →
        (63 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;           have x9 : ℕ → List Bool → Prop := fun (x9 : ℕ) (x10 : List Bool) => ∃ x11 < x1.size, PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x9 x11 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.wireValue x1 x10 ((26 : ℕ) + x11) = Bool.true;           have x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 : ℕ) (x11 x12 : Fin (13 : ℕ)) => x9 x10 (PEqualNP.GenericRejection.incidenceInput {x11} {x12});           (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → x10 x2 x11 x12 ∨ x10 x3 x11 x12) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ x9 x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) → (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ x10 x2 x13 x14 ∧ ¬x10 x3 x13 x14) → (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ x10 x3 x14 x15 ∧ ¬x10 x2 x14 x15) → (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).inputs, (26 : ℕ) ≤ x18 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x18 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size) :=
  fun x1 x2 x3 hM hRB hx2 hx3 hCov hQuad hEx2 hEx3 hThree =>
    let h26_2 : (26 : ℕ) ≤ x2 :=
      Exists.elim hEx2 fun _ hp => Exists.elim hp fun _ hl =>
        Exists.elim hl.2.1 fun _ hg => hg.2.1.1
    let h26_3 : (26 : ℕ) ≤ x3 :=
      Exists.elim hEx3 fun _ hp => Exists.elim hp fun _ hl =>
        Exists.elim hl.2.1 fun _ hg => hg.2.1.1
    let hne : x2 ≠ x3 :=
      fun hEq => Exists.elim hEx2 fun _ hp => Exists.elim hp fun _ hl =>
        hl.2.2 (hEq ▸ hl.2.1)
    let hThree' :=
      Exists.elim hThree fun s hs => hUnpackThree _ s hs.1 hs.2
    Or.elim (Nat.lt_or_gt_of_ne hne)
      (fun hlt =>
        hOrderedWiresAndGates x1 x2 x3
          ⟨hM, hRB, h26_2, hlt, hx3, hCov, hQuad, hEx2, hEx3, hThree'⟩)
      (fun hgt =>
        hOrderedWiresAndGates x1 x3 x2
          ⟨hM, hRB, h26_3, hgt, hx2,
           fun p l hp => Or.symm (hCov p l hp),
           fun q hq hor => hQuad q hq (Or.symm hor),
           hEx3, hEx2, hThree'⟩)
