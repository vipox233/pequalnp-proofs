import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17879_2
    (hMergeAtOutput :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x17 x18 x23 x24 : ℕ),
        have x8 : ℕ → ℕ → Bool := fun (x8 x9 : ℕ) => PEqualNP.ReadK.lineSingle x2 (26 : ℕ) (fun (x10 : ℕ) => Decidable.decide (x10 = x9)) x8 x9;
        have x11 : List ℕ → ℕ → Bool := fun (x11 : List ℕ) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) x11.toFinset);
        have x12 : ℕ → Bool := x11 [(0 : ℕ), (13 : ℕ)];
        have x13 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x13 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x13 - (26 : ℕ));
        have x14 : ℕ → ℕ → Prop := fun (x14 x15 : ℕ) =>
          have x16 : PEqualNP.CircuitLowerBounds.Gate := x13 x15;
          have x17 : ℕ := x16.inputs.getD (0 : ℕ) (0 : ℕ);
          (26 : ℕ) ≤ x15 ∧ x14 ∈ x16.inputs ∧ (x16.op.eval [Bool.false, Bool.true] = Bool.false ∨ x14 = if x12 x17 = Bool.true then x17 else x16.inputs.getD (1 : ℕ) (0 : ℕ));
        have x15 : ℕ → ℕ → Prop := Relation.ReflTransGen x14;
        have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x15 x17 x2.output ∧ PEqualNP.ReadTwo.isAnd x2 (x17 - (26 : ℕ)) ∧ ∀ x18 ∈ (x13 x17).inputs, x12 x18 = Bool.true ∧ x11 [x16] x18 = Bool.false;
        ((63 : ℕ) ≤ x2.size ∧ x2.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 ∧ (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.ReadTwo.fpl (13 : ℕ) x1 ∧ x8 (0 : ℕ) (13 : ℕ) = Bool.false ∧ x8 (13 : ℕ) (0 : ℕ) = Bool.false ∧ x16 (0 : ℕ) x17 ∧ x16 (13 : ℕ) x18 ∧ x11 [(13 : ℕ)] x17 = Bool.true ∧ x11 [(0 : ℕ)] x18 = Bool.true ∧ x23 ≠ x24 ∧ x15 x17 x23 ∧ x15 x18 x24 ∧ x14 x23 x2.output ∧ x14 x24 x2.output ∧ (x13 x2.output).op.eval [Bool.false, Bool.true] = Bool.false) →
        False)
    (hMergeBelowOutput :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x17 x18 x23 x24 x25 : ℕ),
        have x8 : ℕ → ℕ → Bool := fun (x8 x9 : ℕ) => PEqualNP.ReadK.lineSingle x2 (26 : ℕ) (fun (x10 : ℕ) => Decidable.decide (x10 = x9)) x8 x9;
        have x11 : List ℕ → ℕ → Bool := fun (x11 : List ℕ) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) x11.toFinset);
        have x12 : ℕ → Bool := x11 [(0 : ℕ), (13 : ℕ)];
        have x13 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x13 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x13 - (26 : ℕ));
        have x14 : ℕ → ℕ → Prop := fun (x14 x15 : ℕ) =>
          have x16 : PEqualNP.CircuitLowerBounds.Gate := x13 x15;
          have x17 : ℕ := x16.inputs.getD (0 : ℕ) (0 : ℕ);
          (26 : ℕ) ≤ x15 ∧ x14 ∈ x16.inputs ∧ (x16.op.eval [Bool.false, Bool.true] = Bool.false ∨ x14 = if x12 x17 = Bool.true then x17 else x16.inputs.getD (1 : ℕ) (0 : ℕ));
        have x15 : ℕ → ℕ → Prop := Relation.ReflTransGen x14;
        have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x15 x17 x2.output ∧ PEqualNP.ReadTwo.isAnd x2 (x17 - (26 : ℕ)) ∧ ∀ x18 ∈ (x13 x17).inputs, x12 x18 = Bool.true ∧ x11 [x16] x18 = Bool.false;
        ((63 : ℕ) ≤ x2.size ∧ x2.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 ∧ (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.ReadTwo.fpl (13 : ℕ) x1 ∧ x8 (0 : ℕ) (13 : ℕ) = Bool.false ∧ x8 (13 : ℕ) (0 : ℕ) = Bool.false ∧ x16 (0 : ℕ) x17 ∧ x16 (13 : ℕ) x18 ∧ x11 [(13 : ℕ)] x17 = Bool.true ∧ x11 [(0 : ℕ)] x18 = Bool.true ∧ x23 ≠ x24 ∧ x15 x17 x23 ∧ x15 x18 x24 ∧ x14 x23 x25 ∧ x14 x24 x25 ∧ Relation.TransGen x14 x25 x2.output ∧ (x13 x25).op.eval [Bool.false, Bool.true] = Bool.false) →
        False) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x2.size →     x2.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →         (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →           PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.ReadTwo.fpl (13 : ℕ) x1 →             have x8 : ℕ → ℕ → Bool := fun (x8 x9 : ℕ) => PEqualNP.ReadK.lineSingle x2 (26 : ℕ) (fun (x10 : ℕ) => Decidable.decide (x10 = x9)) x8 x9;             x8 (0 : ℕ) (13 : ℕ) = Bool.false →               x8 (13 : ℕ) (0 : ℕ) = Bool.false →                 have x11 : Finset ℕ → ℕ → Bool := fun (x11 : Finset ℕ) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) x11);                 have x12 : ℕ → Bool := x11 {(0 : ℕ), (13 : ℕ)};                 have x13 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x13 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x13 - (26 : ℕ));                 have x14 : ℕ → ℕ → Prop := fun (x14 x15 : ℕ) =>                   have x16 : PEqualNP.CircuitLowerBounds.Gate := x13 x15;                   have x17 : ℕ := x16.inputs.getD (0 : ℕ) (0 : ℕ);                   (26 : ℕ) ≤ x15 ∧ x14 ∈ x16.inputs ∧ (x16.op.eval [Bool.false, Bool.true] = Bool.false ∨ x14 = if x12 x17 = Bool.true then x17 else x16.inputs.getD (1 : ℕ) (0 : ℕ));                 have x15 : ℕ → ℕ → Prop := Relation.ReflTransGen x14;                 have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x15 x17 x2.output ∧ PEqualNP.ReadTwo.isAnd x2 (x17 - (26 : ℕ)) ∧ ∀ x18 ∈ (x13 x17).inputs, x12 x18 = Bool.true ∧ x11 {x16} x18 = Bool.false;                 ∀ (x17 x18 : ℕ), x16 (0 : ℕ) x17 → x16 (13 : ℕ) x18 → x11 {(13 : ℕ)} x17 = Bool.true → x11 {(0 : ℕ)} x18 = Bool.true → (∃ (x23 : ℕ) (x24 : ℕ) (x25 : ℕ), x23 ≠ x24 ∧ x15 x17 x23 ∧ x15 x18 x24 ∧ x14 x23 x25 ∧ x14 x24 x25 ∧ x15 x25 x2.output ∧ (x13 x25).op.eval [Bool.false, Bool.true] = Bool.false) → False) :=
  fun x2 h63 h64 hAO hNodup hFun hL1 hL2 x17 x18 h17 h18 hW17 hW18 hWit =>
    have hS013 : ({(0 : ℕ), (13 : ℕ)} : Finset ℕ) = [(0 : ℕ), (13 : ℕ)].toFinset :=
      Finset.ext fun _ =>
        (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).trans
        ((List.mem_cons.trans (or_congr_right List.mem_singleton)).symm.trans List.mem_toFinset.symm)
    have hSing : ∀ a : ℕ, ({a} : Finset ℕ) = [a].toFinset :=
      fun _ => Finset.ext fun _ => Finset.mem_singleton.trans (List.mem_singleton.symm.trans List.mem_toFinset.symm)
    have hW17' : PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) [(13 : ℕ)].toFinset) x17 = Bool.true :=
      (congrArg (fun s => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) x17) (hSing (13 : ℕ))).symm.trans hW17
    have hW18' : PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ)].toFinset) x18 = Bool.true :=
      (congrArg (fun s => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) x18) (hSing (0 : ℕ))).symm.trans hW18
    let rOf : Finset ℕ → ℕ → ℕ → Prop := fun s a b =>
      have g : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2 (b - (26 : ℕ))
      have i0 : ℕ := g.inputs.getD (0 : ℕ) (0 : ℕ)
      (26 : ℕ) ≤ b ∧ a ∈ g.inputs ∧ (g.op.eval [Bool.false, Bool.true] = Bool.false ∨ a = if PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) i0 = Bool.true then i0 else g.inputs.getD (1 : ℕ) (0 : ℕ))
    have h17' : (26 : ℕ) ≤ x17 ∧ Relation.ReflTransGen (rOf [(0 : ℕ), (13 : ℕ)].toFinset) x17 x2.output ∧ PEqualNP.ReadTwo.isAnd x2 (x17 - (26 : ℕ)) ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x17 - (26 : ℕ))).inputs, PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ), (13 : ℕ)].toFinset) u = Bool.true ∧ PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ)].toFinset) u = Bool.false :=
      ⟨h17.1,
       Eq.subst (motive := fun s => Relation.ReflTransGen (rOf s) x17 x2.output) hS013 h17.2.1,
       h17.2.2.1,
       fun u hu =>
         ⟨(congrArg (fun s => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) hS013).symm.trans (h17.2.2.2 u hu).1,
          (congrArg (fun s => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) (hSing (0 : ℕ))).symm.trans (h17.2.2.2 u hu).2⟩⟩
    have h18' : (26 : ℕ) ≤ x18 ∧ Relation.ReflTransGen (rOf [(0 : ℕ), (13 : ℕ)].toFinset) x18 x2.output ∧ PEqualNP.ReadTwo.isAnd x2 (x18 - (26 : ℕ)) ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x18 - (26 : ℕ))).inputs, PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ), (13 : ℕ)].toFinset) u = Bool.true ∧ PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) [(13 : ℕ)].toFinset) u = Bool.false :=
      ⟨h18.1,
       Eq.subst (motive := fun s => Relation.ReflTransGen (rOf s) x18 x2.output) hS013 h18.2.1,
       h18.2.2.1,
       fun u hu =>
         ⟨(congrArg (fun s => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) hS013).symm.trans (h18.2.2.2 u hu).1,
          (congrArg (fun s => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) (hSing (13 : ℕ))).symm.trans (h18.2.2.2 u hu).2⟩⟩
    hWit.elim fun x23 h23 => h23.elim fun x24 h24 => h24.elim fun x25 hw =>
      have hp1 : Relation.ReflTransGen (rOf [(0 : ℕ), (13 : ℕ)].toFinset) x17 x23 :=
        Eq.subst (motive := fun s => Relation.ReflTransGen (rOf s) x17 x23) hS013 hw.2.1
      have hp2 : Relation.ReflTransGen (rOf [(0 : ℕ), (13 : ℕ)].toFinset) x18 x24 :=
        Eq.subst (motive := fun s => Relation.ReflTransGen (rOf s) x18 x24) hS013 hw.2.2.1
      have hs1 : rOf [(0 : ℕ), (13 : ℕ)].toFinset x23 x25 :=
        Eq.subst (motive := fun s => rOf s x23 x25) hS013 hw.2.2.2.1
      have hs2 : rOf [(0 : ℕ), (13 : ℕ)].toFinset x24 x25 :=
        Eq.subst (motive := fun s => rOf s x24 x25) hS013 hw.2.2.2.2.1
      have hp3 : Relation.ReflTransGen (rOf [(0 : ℕ), (13 : ℕ)].toFinset) x25 x2.output :=
        Eq.subst (motive := fun s => Relation.ReflTransGen (rOf s) x25 x2.output) hS013 hw.2.2.2.2.2.1
      Or.elim (Relation.ReflTransGen.cases_head hp3)
        (fun heq =>
          hMergeAtOutput x2 x17 x18 x23 x24
            ⟨h63, h64, hAO, hNodup, hFun, hL1, hL2, h17', h18', hW17', hW18', hw.1, hp1, hp2,
              Eq.subst (motive := fun t => rOf [(0 : ℕ), (13 : ℕ)].toFinset x23 t) heq hs1,
              Eq.subst (motive := fun t => rOf [(0 : ℕ), (13 : ℕ)].toFinset x24 t) heq hs2,
              Eq.subst (motive := fun t => (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (t - (26 : ℕ))).op.eval [Bool.false, Bool.true] = Bool.false) heq hw.2.2.2.2.2.2⟩)
        (fun hex => hex.elim fun _ hz =>
          hMergeBelowOutput x2 x17 x18 x23 x24 x25
            ⟨h63, h64, hAO, hNodup, hFun, hL1, hL2, h17', h18', hW17', hW18', hw.1, hp1, hp2, hs1, hs2, Relation.TransGen.head' hz.1 hz.2, hw.2.2.2.2.2.2⟩)
