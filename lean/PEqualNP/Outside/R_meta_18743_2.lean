import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18743_2
    (hThreeJoint :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x13 x14 : ℕ),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        x13 ≠ x14 →
        PEqualNP.ReadTwo.isAnd x1 x13 →
        PEqualNP.ReadTwo.isAnd x1 x14 →
        have w : List ℕ → ℕ → Bool := fun (s : List ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s.toFinset)
        have joint : ℕ → Prop := fun (g : ℕ) => w [(0 : ℕ), (13 : ℕ)] ((26 : ℕ) + g) = Bool.true ∧ w [(0 : ℕ)] ((26 : ℕ) + g) = Bool.false ∧ w [(13 : ℕ)] ((26 : ℕ) + g) = Bool.false
        (∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, w [(0 : ℕ), (13 : ℕ)] u = Bool.true ∧ w [(0 : ℕ)] u = Bool.false) →
        (∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x14).inputs, w [(0 : ℕ), (13 : ℕ)] u = Bool.true ∧ w [(13 : ℕ)] u = Bool.false) →
        w [(13 : ℕ)] ((26 : ℕ) + x13) = Bool.false →
        w [(0 : ℕ)] ((26 : ℕ) + x14) = Bool.false →
        ∃ (g0 : ℕ), g0 < x13 ∧ g0 < x14 ∧ joint g0 ∧ joint x13 ∧ joint x14)
    (hNoThreeJoint :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size = (63 : ℕ) →
        (26 : ℕ) ≤ x1.output →
        x1.output < (26 : ℕ) + x1.size →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ g ∈ x1.gates, g.inputs.Nodup) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔
          ∃ (a b : Fin (13 : ℕ)), (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ∧
            x7 (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) b) = Bool.true) →
        PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (k : ℕ) => Decidable.decide (k = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →
        PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (k : ℕ) => Decidable.decide (k = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →
        have w : List ℕ → ℕ → Bool := fun (s : List ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s.toFinset)
        have joint : ℕ → Prop := fun (g : ℕ) => w [(0 : ℕ), (13 : ℕ)] ((26 : ℕ) + g) = Bool.true ∧ w [(0 : ℕ)] ((26 : ℕ) + g) = Bool.false ∧ w [(13 : ℕ)] ((26 : ℕ) + g) = Bool.false
        (∃ (g0 x13 x14 : ℕ), g0 < x13 ∧ g0 < x14 ∧ x13 ≠ x14 ∧
          PEqualNP.ReadTwo.isAnd x1 x13 ∧ PEqualNP.ReadTwo.isAnd x1 x14 ∧
          joint g0 ∧ joint x13 ∧ joint x14) → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size = (63 : ℕ) →     (26 : ℕ) ≤ x1.output →       x1.output < (26 : ℕ) + x1.size →         PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →           (∀ x6 ∈ x1.gates, x6.inputs.Nodup) →             (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →                 PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x9 : ℕ) => Decidable.decide (x9 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                   have x10 : Finset ℕ → ℕ → Bool := fun (x10 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x10);                   have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ) (x16 : ℕ), x1.gates[x13]? = Option.some x14 ∧ x12 = (26 : ℕ) + x13 ∧ x14.inputs = [x15, x16] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x15 ∨ x11 = x16) ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x11 = if x10 {(0 : ℕ), (13 : ℕ)} x15 = Bool.true then x15 else x16) ∧ x10 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true ∧ x10 {(0 : ℕ), (13 : ℕ)} x12 = Bool.true;                   have x12 : ℕ → ℕ → Prop := fun (x12 x13 : ℕ) => Relation.ReflTransGen x11 ((26 : ℕ) + x13) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, x10 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true ∧ x10 {x12} x14 = Bool.false;                   (∃ (x13 : ℕ) (x14 : ℕ), x13 ≠ x14 ∧ x12 (0 : ℕ) x13 ∧ x12 (13 : ℕ) x14 ∧ x10 {(13 : ℕ)} ((26 : ℕ) + x13) = Bool.false ∧ x10 {(0 : ℕ)} ((26 : ℕ) + x14) = Bool.false) → False) := by
  have h013 : ({(0 : ℕ), (13 : ℕ)} : Finset ℕ) = ([(0 : ℕ), (13 : ℕ)] : List ℕ).toFinset := by decide
  have h0 : ({(0 : ℕ)} : Finset ℕ) = ([(0 : ℕ)] : List ℕ).toFinset := by decide
  have h13 : ({(13 : ℕ)} : Finset ℕ) = ([(13 : ℕ)] : List ℕ).toFinset := by decide
  intro x1 hSz hOutLo hOutHi hAO hNd hEv hLS1 hLS2 x10 x11 x12 hEx
  obtain ⟨x13, x14, hNe, h12a, h12b, h13f, h14f⟩ := hEx
  dsimp only [x12, x10] at h12a h12b h13f h14f
  rw [h013, h0] at h12a
  rw [h013, h13] at h12b
  rw [h13] at h13f
  rw [h0] at h14f
  obtain ⟨g0, hg13, hg14, hjg0, hj13, hj14⟩ :=
    hThreeJoint x1 x13 x14 hAO hNe h12a.2.1 h12b.2.1 h12a.2.2 h12b.2.2 h13f h14f
  exact hNoThreeJoint x1 hSz hOutLo hOutHi hAO hNd hEv hLS1 hLS2
    ⟨g0, x13, x14, hg13, hg14, hNe, h12a.2.1, h12b.2.1, hjg0, hj13, hj14⟩
