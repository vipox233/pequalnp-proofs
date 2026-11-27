import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18207_2
    (hTransposeCore :
      have σ : ℕ → ℕ := fun w => if w < (13 : ℕ) then (13 : ℕ) + ((13 : ℕ) - w) % (13 : ℕ) else if w < (26 : ℕ) then ((26 : ℕ) - w) % (13 : ℕ) else w;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        have D : PEqualNP.CircuitLowerBounds.Circuit :=
          { gates := C.gates.map fun g => { op := g.op, inputs := g.inputs.map σ }, output := σ C.output };
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C = PEqualNP.ReadTwo.fpl (13 : ℕ) (fun (a b : Fin (13 : ℕ)) => ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        D.size = C.size ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) D = PEqualNP.ReadTwo.fpl (13 : ℕ) (fun (a b : Fin (13 : ℕ)) => ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ∧
        PEqualNP.ReadK.lineSingle D (26 : ℕ) (fun i => Decidable.decide (i = (13 : ℕ))) (0 : ℕ) (13 : ℕ) =
          PEqualNP.ReadK.lineSingle C (26 : ℕ) (fun i => Decidable.decide (i = (0 : ℕ))) (13 : ℕ) (0 : ℕ) ∧
        PEqualNP.ReadK.lineSingle D (26 : ℕ) (fun i => Decidable.decide (i = (0 : ℕ))) (13 : ℕ) (0 : ℕ) =
          PEqualNP.ReadK.lineSingle C (26 : ℕ) (fun i => Decidable.decide (i = (13 : ℕ))) (0 : ℕ) (13 : ℕ))
    (hTransposePath :
      have σ : ℕ → ℕ := fun w => if w < (13 : ℕ) then (13 : ℕ) + ((13 : ℕ) - w) % (13 : ℕ) else if w < (26 : ℕ) then ((26 : ℕ) - w) % (13 : ℕ) else w;
      have wv := @PEqualNP.ReadTwo.wval (26 : ℕ);
      have f : ℕ → Fin (26 : ℕ) → Bool := fun a i => decide (i.val = a);
      have path : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → ℕ → Prop := fun C a b j =>
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        have up : ℕ → ℕ → Prop := fun u v =>
          have g := ga (v - (26 : ℕ));
          have i0 := g.inputs.getD (0 : ℕ) (0 : ℕ);
          (26 : ℕ) ≤ v ∧ u ∈ g.inputs ∧ (g.op.eval [Bool.false, Bool.true] = Bool.false ∨ u = if wv C (fun i => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) i0 = Bool.true then i0 else g.inputs.getD (1 : ℕ) (0 : ℕ));
        have p : ℕ → Prop := fun w => wv C (f a) w = Bool.true ∧ wv C (f b) w = Bool.false;
        have step : ℕ → ℕ → Prop := fun u v => (26 : ℕ) ≤ v ∧ u ∈ (ga (v - (26 : ℕ))).inputs ∧ p u ∧ p v;
        PEqualNP.ReadTwo.isAnd C j ∧ Relation.ReflTransGen up ((26 : ℕ) + j) C.output ∧
        ∀ u ∈ (ga j).inputs, p u ∧ Relation.ReflTransGen step a u;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        have D : PEqualNP.CircuitLowerBounds.Circuit :=
          { gates := C.gates.map fun g => { op := g.op, inputs := g.inputs.map σ }, output := σ C.output };
        ∀ j, (path C (0 : ℕ) (13 : ℕ) j → path D (13 : ℕ) (0 : ℕ) j) ∧ (path C (13 : ℕ) (0 : ℕ) j → path D (0 : ℕ) (13 : ℕ) j))
    (hOrderedLB :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        have wv := @PEqualNP.ReadTwo.wval (26 : ℕ) C;
        have f : ℕ → Fin (26 : ℕ) → Bool := fun a i => decide (i.val = a);
        have up : ℕ → ℕ → Prop := fun u v =>
          have g := ga (v - (26 : ℕ));
          have i0 := g.inputs.getD (0 : ℕ) (0 : ℕ);
          (26 : ℕ) ≤ v ∧ u ∈ g.inputs ∧ (g.op.eval [Bool.false, Bool.true] = Bool.false ∨ u = if wv (fun i => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) i0 = Bool.true then i0 else g.inputs.getD (1 : ℕ) (0 : ℕ));
        have path : ℕ → ℕ → ℕ → Prop := fun a b j =>
          have p : ℕ → Prop := fun w => wv (f a) w = Bool.true ∧ wv (f b) w = Bool.false;
          have step : ℕ → ℕ → Prop := fun u v => (26 : ℕ) ≤ v ∧ u ∈ (ga (v - (26 : ℕ))).inputs ∧ p u ∧ p v;
          PEqualNP.ReadTwo.isAnd C j ∧ Relation.ReflTransGen up ((26 : ℕ) + j) C.output ∧
          ∀ u ∈ (ga j).inputs, p u ∧ Relation.ReflTransGen step a u;
        (63 : ℕ) ≤ C.size ∧ g1 < g2 ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C = PEqualNP.ReadTwo.fpl (13 : ℕ) (fun (a b : Fin (13 : ℕ)) => ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ∧
        PEqualNP.ReadK.lineSingle C (26 : ℕ) (fun i => Decidable.decide (i = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false ∧
        PEqualNP.ReadK.lineSingle C (26 : ℕ) (fun i => Decidable.decide (i = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false ∧
        path (0 : ℕ) (13 : ℕ) g1 ∧ path (13 : ℕ) (0 : ℕ) g2 → (65 : ℕ) ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 = PEqualNP.ReadTwo.fpl (13 : ℕ) fun (x5 x6 : Fin (13 : ℕ)) => ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →           have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = x7)) x6 x7;           x6 (0 : ℕ) (13 : ℕ) = Bool.false →             x6 (13 : ℕ) (0 : ℕ) = Bool.false →               have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);               have x10 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x10 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x10 - (26 : ℕ));               have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) =>                 have x13 : PEqualNP.CircuitLowerBounds.Gate := x10 x12;                 have x14 : ℕ := x13.inputs.getD (0 : ℕ) (0 : ℕ);                 (26 : ℕ) ≤ x12 ∧ x11 ∈ x13.inputs ∧ (x13.op.eval [Bool.false, Bool.true] = Bool.false ∨ x11 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x13.inputs.getD (1 : ℕ) (0 : ℕ));               have x12 : ℕ → ℕ → ℕ → Prop := fun (x12 x13 x14 : ℕ) =>                 have x15 : Set ℕ := {x15 : ℕ | x9 {x12} x15 = Bool.true ∧ x9 {x13} x15 = Bool.false};                 have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x16 ∈ (x10 x17).inputs ∧ x16 ∈ x15 ∧ x17 ∈ x15;                 PEqualNP.ReadTwo.isAnd x1 x14 ∧ Relation.ReflTransGen x11 ((26 : ℕ) + x14) x1.output ∧ ∀ x17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x14).inputs, x17 ∈ x15 ∧ Relation.ReflTransGen x16 x12 x17;               (∃ (x13 : ℕ), x12 (0 : ℕ) (13 : ℕ) x13) → (∃ (x14 : ℕ), x12 (13 : ℕ) (0 : ℕ) x14) → (65 : ℕ) ≤ x1.size) := by
  intro C hSz hAO hNodup hFun x6 hLS1 hLS2 x9 x10 x11 x12 hex1 hex2
  have h013 : PEqualNP.ReadTwo.indW (26 : ℕ) {(0 : ℕ), (13 : ℕ)} = fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ)) :=
    funext fun i => decide_eq_decide.mpr (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton))
  have h0 : PEqualNP.ReadTwo.indW (26 : ℕ) {(0 : ℕ)} = fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ)) :=
    funext fun i => decide_eq_decide.mpr Finset.mem_singleton
  have h13 : PEqualNP.ReadTwo.indW (26 : ℕ) {(13 : ℕ)} = fun i : Fin (26 : ℕ) => decide (i.val = (13 : ℕ)) :=
    funext fun i => decide_eq_decide.mpr Finset.mem_singleton
  rcases hex1 with ⟨g1, hg1⟩
  rcases hex2 with ⟨g2, hg2⟩
  have hg1' :
      have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
      have wv := @PEqualNP.ReadTwo.wval (26 : ℕ) C;
      have up : ℕ → ℕ → Prop := fun u v =>
        have g := ga (v - (26 : ℕ));
        have i0 := g.inputs.getD (0 : ℕ) (0 : ℕ);
        (26 : ℕ) ≤ v ∧ u ∈ g.inputs ∧ (g.op.eval [Bool.false, Bool.true] = Bool.false ∨ u = if wv (fun i => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) i0 = Bool.true then i0 else g.inputs.getD (1 : ℕ) (0 : ℕ));
      have p : ℕ → Prop := fun w => wv (fun i => decide (i.val = (0 : ℕ))) w = Bool.true ∧ wv (fun i => decide (i.val = (13 : ℕ))) w = Bool.false;
      have step : ℕ → ℕ → Prop := fun u v => (26 : ℕ) ≤ v ∧ u ∈ (ga (v - (26 : ℕ))).inputs ∧ p u ∧ p v;
      PEqualNP.ReadTwo.isAnd C g1 ∧ Relation.ReflTransGen up ((26 : ℕ) + g1) C.output ∧
      ∀ u ∈ (ga g1).inputs, p u ∧ Relation.ReflTransGen step (0 : ℕ) u := by
    rw [← h013, ← h0, ← h13]; exact hg1
  have hg2' :
      have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
      have wv := @PEqualNP.ReadTwo.wval (26 : ℕ) C;
      have up : ℕ → ℕ → Prop := fun u v =>
        have g := ga (v - (26 : ℕ));
        have i0 := g.inputs.getD (0 : ℕ) (0 : ℕ);
        (26 : ℕ) ≤ v ∧ u ∈ g.inputs ∧ (g.op.eval [Bool.false, Bool.true] = Bool.false ∨ u = if wv (fun i => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) i0 = Bool.true then i0 else g.inputs.getD (1 : ℕ) (0 : ℕ));
      have p : ℕ → Prop := fun w => wv (fun i => decide (i.val = (13 : ℕ))) w = Bool.true ∧ wv (fun i => decide (i.val = (0 : ℕ))) w = Bool.false;
      have step : ℕ → ℕ → Prop := fun u v => (26 : ℕ) ≤ v ∧ u ∈ (ga (v - (26 : ℕ))).inputs ∧ p u ∧ p v;
      PEqualNP.ReadTwo.isAnd C g2 ∧ Relation.ReflTransGen up ((26 : ℕ) + g2) C.output ∧
      ∀ u ∈ (ga g2).inputs, p u ∧ Relation.ReflTransGen step (13 : ℕ) u := by
    rw [← h013, ← h0, ← h13]; exact hg2
  have hne : g1 ≠ g2 := by
    intro heq
    subst heq
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs.length = (2 : ℕ) := by
      have hg : C.gates[g1]'(hg1'.1.1) ∈ C.gates := List.getElem_mem hg1'.1.1
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C g1 = C.gates[g1]'(hg1'.1.1) :=
        List.getD_eq_getElem C.gates ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ hg1'.1.1
      rw [hga]; exact hAO.2.2 _ hg
    have hneL : (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs ≠ [] := fun h => by rw [h] at hlen; exact Nat.noConfusion hlen
    have hu : (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs.head hneL ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs := List.head_mem hneL
    exact Bool.noConfusion ((hg1'.2.2 _ hu).1.1.symm.trans (hg2'.2.2 _ hu).1.2)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hOrderedLB C g1 g2 ⟨hSz, hlt, hAO, hNodup, hFun, hLS1, hLS2, hg1', hg2'⟩
  · rcases hTransposeCore C ⟨hAO, hNodup, hFun⟩ with ⟨hsz, hAO', hNodup', hFun', hLS1', hLS2'⟩
    have hP := hTransposePath C hAO
    exact hsz ▸ hOrderedLB _ g2 g1 ⟨hsz.symm ▸ hSz, hgt, hAO', hNodup', hFun', hLS1'.trans hLS2, hLS2'.trans hLS1, (hP g2).2 hg2', (hP g1).1 hg1'⟩
