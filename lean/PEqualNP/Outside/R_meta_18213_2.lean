import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18213_2
    (hIndepJunk :
      let x2 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ)))
            [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
             (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (PEqualNP.TopForm.IsLeastAO x2 x3 ∧
         PEqualNP.TopForm.TopForm x2 x3 ∧
         x3.size ≤ (20 : ℕ) ∧
         x4 ∈ PEqualNP.TopForm.junk x2 x3 ∧
         x5 ∈ PEqualNP.TopForm.junk x2 x3 ∧
         x4 < x5 ∧
         (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card +
           (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card <
           (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card ∧
         (∀ (f : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + x4) = Bool.true ↔
           ∀ (b : Fin (2 : ℕ)), ∃ v ∈ PEqualNP.TopForm.side x3 x4 b, f v = Bool.true) ∧
         (∀ (f : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + x5) = Bool.true ↔
           ∀ (b : Fin (2 : ℕ)), ∃ v ∈ PEqualNP.TopForm.side x3 x5 b, f v = Bool.true)) →
        ∃ (x15 : Fin (11 : ℕ)),
          ↑x15 < (4 : ℕ) ∧
          let x16 : ℕ → Prop := fun (g : ℕ) =>
            ∃ w < (11 : ℕ) + g, ∀ (f : Fin (11 : ℕ) → Bool), f x15 = Bool.false →
              PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + g) = PEqualNP.ReadTwo.wval x3 f w;
          ∃ (g1 g2 g3 : ℕ), g1 < g2 ∧ g2 < g3 ∧ g3 < x3.size ∧ x16 g1 ∧ x16 g2 ∧ x16 g3)
    (hChainedJunk :
      let x2 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ)))
            [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
             (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (PEqualNP.TopForm.IsLeastAO x2 x3 ∧
         PEqualNP.TopForm.TopForm x2 x3 ∧
         x3.size ≤ (20 : ℕ) ∧
         x4 ∈ PEqualNP.TopForm.junk x2 x3 ∧
         x5 ∈ PEqualNP.TopForm.junk x2 x3 ∧
         x4 < x5 ∧
         (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card +
           (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card <
           (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card ∧
         (∃ (b : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x5 b) x4) ∧
         (∀ (f : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + x4) = Bool.true ↔
           ∀ (b : Fin (2 : ℕ)), ∃ v ∈ PEqualNP.TopForm.side x3 x4 b, f v = Bool.true) ∧
         (∀ (f : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + x5) = Bool.true ↔
           ∀ (b : Fin (2 : ℕ)),
             (∃ v ∈ PEqualNP.TopForm.side x3 x5 b, f v = Bool.true) ∨
             (PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x5 b) x4 ∧
              PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + x4) = Bool.true))) →
        ∃ (x15 : Fin (11 : ℕ)),
          ↑x15 < (4 : ℕ) ∧
          let x16 : ℕ → Prop := fun (g : ℕ) =>
            ∃ w < (11 : ℕ) + g, ∀ (f : Fin (11 : ℕ) → Bool), f x15 = Bool.false →
              PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + g) = PEqualNP.ReadTwo.wval x3 f w;
          ∃ (g1 g2 g3 : ℕ), g1 < g2 ∧ g2 < g3 ∧ g3 < x3.size ∧ x16 g1 ∧ x16 g2 ∧ x16 g3) :
    (have x1 : ℕ := (11 : ℕ); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x2 : ℕ) => (x2 / (11 : ℕ), x2 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   PEqualNP.TopForm.IsLeastAO x2 x3 →     PEqualNP.TopForm.TopForm x2 x3 →       x3.size ≤ (21 : ℕ) →         x3.size ≤ (20 : ℕ) →           x4 ∈ PEqualNP.TopForm.junk x2 x3 →             x5 ∈ PEqualNP.TopForm.junk x2 x3 →               x4 < x5 →                 (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card →                   (∀ x14 ∈ [x4, x5], ∀ (x16 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x3 x16 (x1 + x14) = Bool.true ↔ ∀ (x17 : Fin (2 : ℕ)), (∃ x18 ∈ PEqualNP.TopForm.side x3 x14 x17, x16 x18 = Bool.true) ∨ x14 = x5 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x3 (PEqualNP.TopForm.opnd x3 x14 x17) x4 ∧ PEqualNP.ReadTwo.wval x3 x16 (x1 + x4) = Bool.true) →                     ∃ (x15 : Fin (11 : ℕ)),                       ↑x15 < (4 : ℕ) ∧                         have x16 : ℕ → Prop := fun (x16 : ℕ) => ∃ x17 < (11 : ℕ) + x16, ∀ (x18 : Fin (11 : ℕ) → Bool), x18 x15 = Bool.false → PEqualNP.ReadTwo.wval x3 x18 ((11 : ℕ) + x16) = PEqualNP.ReadTwo.wval x3 x18 x17;                         ∃ (x17 : ℕ) (x18 : ℕ) (x19 : ℕ), x17 < x18 ∧ x18 < x19 ∧ x19 < x3.size ∧ x16 x17 ∧ x16 x18 ∧ x16 x19) :=
  fun x3 x4 x5 hL hTF _h21 h20 h4 h5 h45 hCount hWval =>
    let h4pure : ∀ (f : Fin (11 : ℕ) → Bool), PEqualNP.ReadTwo.wval x3 f ((11 : ℕ) + x4) = Bool.true ↔
        ∀ (b : Fin (2 : ℕ)), ∃ v ∈ PEqualNP.TopForm.side x3 x4 b, f v = Bool.true :=
      fun f =>
        Iff.trans (hWval x4 List.mem_cons_self f)
          (forall_congr' fun _b =>
            ⟨fun h => Or.elim h id (fun h2 => False.elim (Nat.ne_of_lt h45 h2.1)), Or.inl⟩)
    let h5raw := hWval x5 (List.mem_cons_of_mem _ List.mem_cons_self)
    Or.elim (Classical.em (∃ (b : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x5 b) x4))
      (fun hReach =>
        hChainedJunk x3 x4 x5
          ⟨hL, hTF, h20, h4, h5, h45, hCount, hReach, h4pure,
           fun f =>
             Iff.trans (h5raw f)
               (forall_congr' fun _b =>
                 ⟨fun h => Or.elim h Or.inl (fun h2 => Or.inr h2.2),
                  fun h => Or.elim h Or.inl (fun h2 => Or.inr ⟨rfl, h2⟩)⟩)⟩)
      (fun hNoReach =>
        hIndepJunk x3 x4 x5
          ⟨hL, hTF, h20, h4, h5, h45, hCount, h4pure,
           fun f =>
             Iff.trans (h5raw f)
               (forall_congr' fun b =>
                 ⟨fun h => Or.elim h id (fun h2 => False.elim (hNoReach ⟨b, h2.2.1⟩)), Or.inl⟩)⟩)
