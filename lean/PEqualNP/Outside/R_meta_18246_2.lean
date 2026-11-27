import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18246_2
    (hDeg2Essential :
      let G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ v : Fin (11 : ℕ), ↑v < (4 : ℕ) →
          (1 : ℕ) ≤ (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card ∧
          ∀ g ∈ PEqualNP.TopForm.readers (0 : ℕ) C ↑v,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hHasAndReader :
      let G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v0 : Fin (11 : ℕ)) (g0 : ℕ),
        have rd := PEqualNP.TopForm.readers (0 : ℕ) C;
        PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card ∧ C.size ≤ (21 : ℕ) ∧
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card ∧
        (∀ v : Fin (11 : ℕ), ↑v < (4 : ℕ) → (rd ↑v).card ≤ (2 : ℕ)) ∧
        (∀ v u w : Fin (11 : ℕ), ↑v < (4 : ℕ) → u ≤ w → v ≠ u → v ≠ w → ¬G.Adj u w → rd ↑v ⊆ rd ↑u ∪ rd ↑w → (121 : ℕ) * ↑v + (11 : ℕ) * ↑u + ↑w ∈ [(29 : ℕ), (30 : ℕ), (49 : ℕ), (51 : ℕ), (61 : ℕ), (74 : ℕ), (186 : ℕ), (230 : ℕ), (250 : ℕ), (295 : ℕ), (316 : ℕ), (317 : ℕ), (472 : ℕ)]) ∧
        ↑v0 < (4 : ℕ) ∧ g0 ∈ rd ↑v0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g0).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ v : Fin (11 : ℕ), ↑v < (4 : ℕ) ∧
          have col : ℕ → Prop := fun j => ∃ w < (11 : ℕ) + j, ∀ y : Fin (11 : ℕ) → Bool, y v = Bool.false → PEqualNP.ReadTwo.wval C y ((11 : ℕ) + j) = PEqualNP.ReadTwo.wval C y w;
          ∃ j1 j2 j3 : ℕ, j1 < j2 ∧ j2 < j3 ∧ j3 < C.size ∧ col j1 ∧ col j2 ∧ col j3)
    (hAllOrReaders :
      let G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        have rd := PEqualNP.TopForm.readers (0 : ℕ) C;
        PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card ∧ C.size ≤ (21 : ℕ) ∧
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card ∧
        (∀ v : Fin (11 : ℕ), ↑v < (4 : ℕ) → (1 : ℕ) ≤ (rd ↑v).card ∧ (rd ↑v).card ≤ (2 : ℕ) ∧ ∀ g ∈ rd ↑v, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (∀ v u w : Fin (11 : ℕ), ↑v < (4 : ℕ) → u ≤ w → v ≠ u → v ≠ w → ¬G.Adj u w → rd ↑v ⊆ rd ↑u ∪ rd ↑w → (121 : ℕ) * ↑v + (11 : ℕ) * ↑u + ↑w ∈ [(29 : ℕ), (30 : ℕ), (49 : ℕ), (51 : ℕ), (61 : ℕ), (74 : ℕ), (186 : ℕ), (230 : ℕ), (250 : ℕ), (295 : ℕ), (316 : ℕ), (317 : ℕ), (472 : ℕ)]) →
        ∃ v : Fin (11 : ℕ), ↑v < (4 : ℕ) ∧
          have col : ℕ → Prop := fun j => ∃ w < (11 : ℕ) + j, ∀ y : Fin (11 : ℕ) → Bool, y v = Bool.false → PEqualNP.ReadTwo.wval C y ((11 : ℕ) + j) = PEqualNP.ReadTwo.wval C y w;
          ∃ j1 j2 j3 : ℕ, j1 < j2 ∧ j2 < j3 ∧ j3 < C.size ∧ col j1 ∧ col j2 ∧ col j3) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) → (PEqualNP.TopForm.readers (0 : ℕ) x2 ↑x8).card ≤ (2 : ℕ)) →               (∀ (x9 x10 x11 : Fin (11 : ℕ)), ↑x9 < (4 : ℕ) → x10 ≤ x11 → x9 ≠ x10 → x9 ≠ x11 → ¬x1.Adj x10 x11 → PEqualNP.TopForm.readers (0 : ℕ) x2 ↑x9 ⊆ PEqualNP.TopForm.readers (0 : ℕ) x2 ↑x10 ∪ PEqualNP.TopForm.readers (0 : ℕ) x2 ↑x11 → (121 : ℕ) * ↑x9 + (11 : ℕ) * ↑x10 + ↑x11 ∈ [(29 : ℕ), (30 : ℕ), (49 : ℕ), (51 : ℕ), (61 : ℕ), (74 : ℕ), (186 : ℕ), (230 : ℕ), (250 : ℕ), (295 : ℕ), (316 : ℕ), (317 : ℕ), (472 : ℕ)]) →                 ∃ (x10 : Fin (11 : ℕ)),                   ↑x10 < (4 : ℕ) ∧                     have x11 : ℕ → Prop := fun (x11 : ℕ) => ∃ x12 < (11 : ℕ) + x11, ∀ (x13 : Fin (11 : ℕ) → Bool), x13 x10 = Bool.false → PEqualNP.ReadTwo.wval x2 x13 ((11 : ℕ) + x11) = PEqualNP.ReadTwo.wval x2 x13 x12;                     ∃ (x12 : ℕ) (x13 : ℕ) (x14 : ℕ), x12 < x13 ∧ x13 < x14 ∧ x14 < x2.size ∧ x11 x12 ∧ x11 x13 ∧ x11 x14) := by
  intro x1 C hL hTF hJ hSz hCh hDeg hTri
  have hEss := hDeg2Essential C hL
  refine Or.elim (Classical.em (∃ v : Fin (11 : ℕ), ↑v < (4 : ℕ) ∧ ∃ g ∈ PEqualNP.TopForm.readers (0 : ℕ) C ↑v, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and))
    (fun h => Exists.elim h fun v hv => Exists.elim hv.2 fun g hg =>
      hHasAndReader C v g ⟨hL, hTF, hJ, hSz, hCh, hDeg, hTri, hv.1, hg.1, hg.2⟩)
    (fun hno => hAllOrReaders C ⟨hL, hTF, hJ, hSz, hCh,
      fun v hv => ⟨(hEss v hv).1, hDeg v hv, fun g hg =>
        Or.elim ((hEss v hv).2 g hg)
          (fun hand => False.elim (hno ⟨v, hv, g, hg, hand⟩))
          (fun hor => hor)⟩, hTri⟩)
