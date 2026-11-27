import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18940_2
    (hTransposeSpec :
      have σ : ℕ → ℕ := fun w => if w < (13 : ℕ) then (13 : ℕ) + ((13 : ℕ) - w) % (13 : ℕ) else if w < (26 : ℕ) then ((26 : ℕ) - w) % (13 : ℕ) else w;
      have wv := @PEqualNP.ReadTwo.wval (26 : ℕ);
      have f : ℕ → Fin (26 : ℕ) → Bool := fun a i => decide (i.val = a);
      have sp : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        ∀ x : Fin (26 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
          ∃ a b : Fin (13 : ℕ), (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ∧
            x (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) b) = Bool.true;
      have gd : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun C a j =>
        PEqualNP.ReadTwo.isAnd C j ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
          wv C (fun i => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) u = Bool.true ∧ wv C (f a) u = Bool.false;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, sp C →
        have D : PEqualNP.CircuitLowerBounds.Circuit :=
          { gates := C.gates.map fun g => { op := g.op, inputs := g.inputs.map σ }, output := σ C.output };
        D.size = C.size ∧ sp D ∧
        ∀ j, (gd C (0 : ℕ) j → gd D (13 : ℕ) j) ∧ (gd C (13 : ℕ) j → gd D (0 : ℕ) j) ∧
          wv D (f (13 : ℕ)) ((26 : ℕ) + j) = wv C (f (0 : ℕ)) ((26 : ℕ) + j) ∧
          wv D (f (0 : ℕ)) ((26 : ℕ) + j) = wv C (f (13 : ℕ)) ((26 : ℕ) + j))
    (hTransposeGoal :
      have σ : ℕ → ℕ := fun w => if w < (13 : ℕ) then (13 : ℕ) + ((13 : ℕ) - w) % (13 : ℕ) else if w < (26 : ℕ) then ((26 : ℕ) - w) % (13 : ℕ) else w;
      have gl : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        ∃ v : Fin (26 : ℕ), ∃ m : ℕ → Bool, (v = (0 : Fin (26 : ℕ)) ∨ v = (13 : Fin (26 : ℕ))) ∧
          have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
          have w := PEqualNP.ReadTwo.wval C fun i : Fin (26 : ℕ) => Decidable.decide (i ≠ v);
          m C.output = Bool.true ∧
          (∀ j < C.size, m ((26 : ℕ) + j) = Bool.true → w ((26 : ℕ) + j) = Bool.true → ∀ u ∈ (ga j).inputs, w u = Bool.true → m u = Bool.true) ∧
          (List.filter (fun j => m ((26 : ℕ) + j) && (ga j).inputs.all w) (List.range C.size)).length + (6 : ℕ) ≤ C.size;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        gl { gates := C.gates.map fun g => { op := g.op, inputs := g.inputs.map σ }, output := σ C.output } → gl C)
    (hAsym :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        have wv := @PEqualNP.ReadTwo.wval (26 : ℕ) C;
        have f : ℕ → Fin (26 : ℕ) → Bool := fun a i => decide (i.val = a);
        have gd : ℕ → ℕ → Prop := fun a j =>
          PEqualNP.ReadTwo.isAnd C j ∧ ∀ u ∈ (ga j).inputs,
            wv (fun i => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) u = Bool.true ∧ wv (f a) u = Bool.false;
        (63 : ℕ) ≤ C.size ∧ C.size ≤ (64 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ x : Fin (26 : ℕ) → Bool, C.eval (List.ofFn x) = Bool.true ↔
          ∃ a b : Fin (13 : ℕ), (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ∧
            x (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧
        g1 ≠ g2 ∧ gd (0 : ℕ) g1 ∧ gd (13 : ℕ) g2 ∧
        wv (f (13 : ℕ)) ((26 : ℕ) + g1) = Bool.true ∧ wv (f (0 : ℕ)) ((26 : ℕ) + g2) = Bool.false →
        ∃ v : Fin (26 : ℕ), ∃ m : ℕ → Bool, (v = (0 : Fin (26 : ℕ)) ∨ v = (13 : Fin (26 : ℕ))) ∧
          have w := wv fun i => Decidable.decide (i ≠ v);
          m C.output = Bool.true ∧
          (∀ j < C.size, m ((26 : ℕ) + j) = Bool.true → w ((26 : ℕ) + j) = Bool.true → ∀ u ∈ (ga j).inputs, w u = Bool.true → m u = Bool.true) ∧
          (List.filter (fun j => m ((26 : ℕ) + j) && (ga j).inputs.all w) (List.range C.size)).length + (6 : ℕ) ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : Finset ℕ → ℕ → Bool := fun (x7 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x7);             have x8 : ℕ → ℕ → Prop := fun (x8 x9 : ℕ) => PEqualNP.ReadTwo.isAnd x1 x9 ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).inputs, x7 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x7 {x8} x10 = Bool.false;             (∃ (x9 : ℕ) (x10 : ℕ), x9 ≠ x10 ∧ x8 (0 : ℕ) x9 ∧ x8 (13 : ℕ) x10 ∧ x7 {(13 : ℕ)} ((26 : ℕ) + x9) ≠ x7 {(0 : ℕ)} ((26 : ℕ) + x10)) →               ∃ (x10 : Fin (26 : ℕ)) (x11 : ℕ → Bool),                 (x10 = (0 : Fin (26 : ℕ)) ∨ x10 = (13 : Fin (26 : ℕ))) ∧                   have x12 : ℕ → Bool := PEqualNP.ReadTwo.wval x1 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 ≠ x10);                   x11 x1.output = Bool.true ∧ (∀ x13 < x1.size, x11 ((26 : ℕ) + x13) = Bool.true → x12 ((26 : ℕ) + x13) = Bool.true → ∀ x17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, x12 x17 = Bool.true → x11 x17 = Bool.true) ∧ (List.filter (fun (x13 : ℕ) => x11 ((26 : ℕ) + x13) && (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs.all x12) (List.range x1.size)).length + (6 : ℕ) ≤ x1.size) := by
  intro C hge hle hAO hNodup hSpec x7 x8 hex
  have h013 : PEqualNP.ReadTwo.indW (26 : ℕ) {(0 : ℕ), (13 : ℕ)} = fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ)) :=
    funext fun i => decide_eq_decide.mpr (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton))
  have h0 : PEqualNP.ReadTwo.indW (26 : ℕ) {(0 : ℕ)} = fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ)) :=
    funext fun i => decide_eq_decide.mpr Finset.mem_singleton
  have h13 : PEqualNP.ReadTwo.indW (26 : ℕ) {(13 : ℕ)} = fun i : Fin (26 : ℕ) => decide (i.val = (13 : ℕ)) :=
    funext fun i => decide_eq_decide.mpr Finset.mem_singleton
  rcases hex with ⟨g1, g2, hne, hg1, hg2, hdiff⟩
  have hg1' : PEqualNP.ReadTwo.isAnd C g1 ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs,
      PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) u = Bool.true ∧
      PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ))) u = Bool.false := by
    rw [← h013, ← h0]; exact hg1
  have hg2' : PEqualNP.ReadTwo.isAnd C g2 ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs,
      PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ) ∨ i.val = (13 : ℕ))) u = Bool.true ∧
      PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (13 : ℕ))) u = Bool.false := by
    rw [← h013, ← h13]; exact hg2
  have hdiff' : PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (13 : ℕ))) ((26 : ℕ) + g1) ≠
      PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ))) ((26 : ℕ) + g2) := by
    rw [← h13, ← h0]; exact hdiff
  rcases Bool.eq_false_or_eq_true (PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (13 : ℕ))) ((26 : ℕ) + g1)) with hb1 | hb1
  · rcases Bool.eq_false_or_eq_true (PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ))) ((26 : ℕ) + g2)) with hb2 | hb2
    · exact False.elim (hdiff' (hb1.trans hb2.symm))
    · exact hAsym C g1 g2 ⟨hge, hle, hAO, hNodup, hSpec, hne, hg1', hg2', hb1, hb2⟩
  · rcases Bool.eq_false_or_eq_true (PEqualNP.ReadTwo.wval C (fun i : Fin (26 : ℕ) => decide (i.val = (0 : ℕ))) ((26 : ℕ) + g2)) with hb2 | hb2
    · rcases hTransposeSpec C ⟨hAO, hNodup, hSpec⟩ with ⟨hsz, hSpec', hJ⟩
      exact hTransposeGoal C (hAsym _ g2 g1 ⟨hsz.symm ▸ hge, hsz.symm ▸ hle, hSpec'.1, hSpec'.2.1, hSpec'.2.2, hne.symm, (hJ g2).2.1 hg2', (hJ g1).1 hg1', (hJ g2).2.2.1.trans hb2, (hJ g1).2.2.2.trans hb1⟩)
    · exact False.elim (hdiff' (hb1.trans hb2.symm))
