import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18215_2
    (hUnpackTwoJunk :
      ∀ (G : SimpleGraph (Fin (11 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (C.size ≤ (21 : ℕ) ∧ ¬C.size ≤ (20 : ℕ) ∧
         a ∈ PEqualNP.TopForm.junk G C ∧ b ∈ PEqualNP.TopForm.junk G C ∧ a < b) →
        C.size = (21 : ℕ) ∧ (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card ∧ b < (21 : ℕ) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C b).op = PEqualNP.CircuitLowerBounds.GateOp.and)
    (hSize21SplitJunk :
      let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x2 : ℕ) => (x2 / (11 : ℕ), x2 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (PEqualNP.TopForm.IsLeastAO x2 x3 ∧
         PEqualNP.TopForm.TopForm x2 x3 ∧
         x3.size = (21 : ℕ) ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x3).card ∧
         x4 ∈ PEqualNP.TopForm.junk x2 x3 ∧
         x5 ∈ PEqualNP.TopForm.junk x2 x3 ∧
         x4 < x5 ∧ x5 < (21 : ℕ) ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card ∧
         (∀ (x16 : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 x16 ((11 : ℕ) + x4) = Bool.true ↔
           ∀ (x17 : Fin (2 : ℕ)), ∃ x18 ∈ PEqualNP.TopForm.side x3 x4 x17, x16 x18 = Bool.true) ∧
         (∀ (x16 : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 x16 ((11 : ℕ) + x5) = Bool.true ↔
           ∀ (x17 : Fin (2 : ℕ)), (∃ x18 ∈ PEqualNP.TopForm.side x3 x5 x17, x16 x18 = Bool.true) ∨
             PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x5 x17) x4 ∧
             PEqualNP.ReadTwo.wval x3 x16 ((11 : ℕ) + x4) = Bool.true)) →
        ∃ (x15 : Fin (11 : ℕ)),
          ↑x15 < (4 : ℕ) ∧
            have x16 : ℕ → Prop := fun (x16 : ℕ) => ∃ x17 < (11 : ℕ) + x16, ∀ (x18 : Fin (11 : ℕ) → Bool), x18 x15 = Bool.false → PEqualNP.ReadTwo.wval x3 x18 ((11 : ℕ) + x16) = PEqualNP.ReadTwo.wval x3 x18 x17;
            ∃ (x17 : ℕ) (x18 : ℕ) (x19 : ℕ), x17 < x18 ∧ x18 < x19 ∧ x19 < x3.size ∧ x16 x17 ∧ x16 x18 ∧ x16 x19) :
    (have x1 : ℕ := (11 : ℕ); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x2 : ℕ) => (x2 / (11 : ℕ), x2 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   PEqualNP.TopForm.IsLeastAO x2 x3 →     PEqualNP.TopForm.TopForm x2 x3 →       x3.size ≤ (21 : ℕ) →         ¬x3.size ≤ (20 : ℕ) →           x4 ∈ PEqualNP.TopForm.junk x2 x3 →             x5 ∈ PEqualNP.TopForm.junk x2 x3 →               x4 < x5 →                 (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card →                   (∀ x14 ∈ [x4, x5], ∀ (x16 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x3 x16 (x1 + x14) = Bool.true ↔ ∀ (x17 : Fin (2 : ℕ)), (∃ x18 ∈ PEqualNP.TopForm.side x3 x14 x17, x16 x18 = Bool.true) ∨ x14 = x5 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x3 (PEqualNP.TopForm.opnd x3 x14 x17) x4 ∧ PEqualNP.ReadTwo.wval x3 x16 (x1 + x4) = Bool.true) →                     ∃ (x15 : Fin (11 : ℕ)),                       ↑x15 < (4 : ℕ) ∧                         have x16 : ℕ → Prop := fun (x16 : ℕ) => ∃ x17 < (11 : ℕ) + x16, ∀ (x18 : Fin (11 : ℕ) → Bool), x18 x15 = Bool.false → PEqualNP.ReadTwo.wval x3 x18 ((11 : ℕ) + x16) = PEqualNP.ReadTwo.wval x3 x18 x17;                         ∃ (x17 : ℕ) (x18 : ℕ) (x19 : ℕ), x17 < x18 ∧ x18 < x19 ∧ x19 < x3.size ∧ x16 x17 ∧ x16 x18 ∧ x16 x19) := by
  intro x1 x2 x3 x4 x5 hL hTF h21 hNot20 hx4 hx5 hlt hBnd hEval
  exact
    let hU := hUnpackTwoJunk x2 x3 x4 x5 ⟨h21, hNot20, hx4, hx5, hlt⟩
    let hE4 : ∀ (x16 : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 x16 ((11 : ℕ) + x4) = Bool.true ↔
        ∀ (x17 : Fin (2 : ℕ)), ∃ x18 ∈ PEqualNP.TopForm.side x3 x4 x17, x16 x18 = Bool.true :=
      fun x16 =>
        let h := hEval x4 List.mem_cons_self x16
        Iff.intro
          (fun ht b => Or.elim (h.mp ht b) (fun h1 => h1) (fun h2 => False.elim (Nat.ne_of_lt hlt h2.1)))
          (fun hb => h.mpr fun b => Or.inl (hb b))
    let hE5 : ∀ (x16 : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 x16 ((11 : ℕ) + x5) = Bool.true ↔
        ∀ (x17 : Fin (2 : ℕ)), (∃ x18 ∈ PEqualNP.TopForm.side x3 x5 x17, x16 x18 = Bool.true) ∨
          PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x5 x17) x4 ∧
          PEqualNP.ReadTwo.wval x3 x16 ((11 : ℕ) + x4) = Bool.true :=
      fun x16 =>
        let h := hEval x5 (List.mem_cons_of_mem x4 List.mem_cons_self) x16
        Iff.intro
          (fun ht b => Or.elim (h.mp ht b) (fun h1 => Or.inl h1) (fun h2 => Or.inr h2.2))
          (fun hb => h.mpr fun b => Or.elim (hb b) (fun h1 => Or.inl h1) (fun h2 => Or.inr ⟨rfl, h2⟩))
    hSize21SplitJunk x3 x4 x5
      ⟨hL, hTF, hU.1, hU.2.1, hx4, hx5, hlt, hU.2.2.1, hU.2.2.2.1, hU.2.2.2.2, hBnd, hE4, hE5⟩
