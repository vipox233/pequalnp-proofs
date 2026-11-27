import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17983_2
    (hDirectOut : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size = (64 : ℕ) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
          (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →
            have x5 : List (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))];
            have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x6);
            have x7 : List ℕ → ℕ → Bool := fun (x7 : List ℕ) (x8 : ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x7.toFinset) x8;
            (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x5 → (x6 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
            (∀ (x10 : Finset (Fin (13 : ℕ))), (x6 fun (x11 : Fin (26 : ℕ)) => if ↑x11 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x11 ∈ x10) else Decidable.decide (∀ x12 ∈ x10, x12 - Fin.ofNat (13 : ℕ) (↑x11 - (13 : ℕ)) ∉ x5)) = Bool.false) →
            PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x11 : ℕ) => Decidable.decide (x11 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →
            PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x12 : ℕ) => Decidable.decide (x12 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →
            (∃ (x13 : ℕ), (26 : ℕ) + x13 = x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, x7 [(0 : ℕ), (13 : ℕ)] x14 = Bool.true ∧ x7 [(0 : ℕ)] x14 = Bool.false ∧ x7 [(13 : ℕ)] x14 = Bool.false) → False)
    (hProperPath : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size = (64 : ℕ) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
          (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →
            have x5 : List (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))];
            have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x6);
            have x7 : List ℕ → ℕ → Bool := fun (x7 : List ℕ) (x8 : ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x7.toFinset) x8;
            have w013 : ℕ → Bool := x7 [(0 : ℕ), (13 : ℕ)];
            have x8 : ℕ → ℕ → Prop := fun (x8 x9 : ℕ) => ∃ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate) (x12 : ℕ) (x13 : ℕ), x1.gates[x10]? = Option.some x11 ∧ x9 = (26 : ℕ) + x10 ∧ x11.inputs = [x12, x13] ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x8 = x12 ∨ x8 = x13) ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x8 = if w013 x12 = Bool.true then x12 else x13) ∧ w013 x8 = Bool.true ∧ w013 x9 = Bool.true;
            (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x5 → (x6 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
            (∀ (x10 : Finset (Fin (13 : ℕ))), (x6 fun (x11 : Fin (26 : ℕ)) => if ↑x11 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x11 ∈ x10) else Decidable.decide (∀ x12 ∈ x10, x12 - Fin.ofNat (13 : ℕ) (↑x11 - (13 : ℕ)) ∉ x5)) = Bool.false) →
            PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x11 : ℕ) => Decidable.decide (x11 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →
            PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x12 : ℕ) => Decidable.decide (x12 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →
            (∃ (x13 : ℕ), Relation.TransGen x8 ((26 : ℕ) + x13) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, w013 x14 = Bool.true ∧ x7 [(0 : ℕ)] x14 = Bool.false ∧ x7 [(13 : ℕ)] x14 = Bool.false) → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size = (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         have x5 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x6);         have x7 : Finset ℕ → ℕ → Bool := fun (x7 : Finset ℕ) (x8 : ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x7) x8;         have x8 : ℕ → ℕ → Prop := fun (x8 x9 : ℕ) => ∃ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate) (x12 : ℕ) (x13 : ℕ), x1.gates[x10]? = Option.some x11 ∧ x9 = (26 : ℕ) + x10 ∧ x11.inputs = [x12, x13] ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x8 = x12 ∨ x8 = x13) ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x8 = if x7 {(0 : ℕ), (13 : ℕ)} x12 = Bool.true then x12 else x13) ∧ x7 {(0 : ℕ), (13 : ℕ)} x8 = Bool.true ∧ x7 {(0 : ℕ), (13 : ℕ)} x9 = Bool.true;         (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x5 → (x6 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) → (∀ (x10 : Finset (Fin (13 : ℕ))), (x6 fun (x11 : Fin (26 : ℕ)) => if ↑x11 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x11 ∈ x10) else Decidable.decide (∀ x12 ∈ x10, x12 - Fin.ofNat (13 : ℕ) (↑x11 - (13 : ℕ)) ∉ x5)) = Bool.false) → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x11 : ℕ) => Decidable.decide (x11 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x12 : ℕ) => Decidable.decide (x12 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false → (∃ (x13 : ℕ), Relation.ReflTransGen x8 ((26 : ℕ) + x13) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, x7 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true ∧ x7 {(0 : ℕ)} x14 = Bool.false ∧ x7 {(13 : ℕ)} x14 = Bool.false) → False) :=
  fun x1 hSz hAO hNodup hPos hNeg hL1 hL2 hWit =>
    have hMem5 : ∀ a : Fin (13 : ℕ),
        a ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ↔
        a ∈ ([(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] : List (Fin (13 : ℕ))) :=
      fun _ =>
        (Finset.mem_insert.trans (or_congr_right
          (Finset.mem_insert.trans (or_congr_right
            (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)))))).trans
        (List.mem_cons.trans (or_congr_right
          (List.mem_cons.trans (or_congr_right
            (List.mem_cons.trans (or_congr_right List.mem_singleton)))))).symm
    have hS013 : ({(0 : ℕ), (13 : ℕ)} : Finset ℕ) = [(0 : ℕ), (13 : ℕ)].toFinset :=
      Finset.ext fun _ =>
        (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).trans
        ((List.mem_cons.trans (or_congr_right List.mem_singleton)).symm.trans List.mem_toFinset.symm)
    have hS0 : ({(0 : ℕ)} : Finset ℕ) = [(0 : ℕ)].toFinset :=
      Finset.ext fun _ => Finset.mem_singleton.trans (List.mem_singleton.symm.trans List.mem_toFinset.symm)
    have hS13 : ({(13 : ℕ)} : Finset ℕ) = [(13 : ℕ)].toFinset :=
      Finset.ext fun _ => Finset.mem_singleton.trans (List.mem_singleton.symm.trans List.mem_toFinset.symm)
    have hPos' : ∀ (x9 x10 : Fin (13 : ℕ)),
        x9 - x10 ∈ ([(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] : List (Fin (13 : ℕ))) →
        x1.eval (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true :=
      fun a b hab => hPos a b ((hMem5 (a - b)).mpr hab)
    have hNeg' : ∀ (x10 : Finset (Fin (13 : ℕ))),
        x1.eval (List.ofFn fun (x11 : Fin (26 : ℕ)) => if ↑x11 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x11 ∈ x10) else Decidable.decide (∀ x12 ∈ x10, x12 - Fin.ofNat (13 : ℕ) (↑x11 - (13 : ℕ)) ∉ ([(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] : List (Fin (13 : ℕ))))) = Bool.false :=
      fun x10 =>
        Eq.trans
          (congrArg (fun fn => x1.eval (List.ofFn fn))
            (funext fun k =>
              congrArg (fun b => if ↑k < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑k ∈ x10) else b)
                (decide_eq_decide.mpr (forall_congr' fun _ => imp_congr_right fun _ => not_congr (hMem5 _).symm))))
          (hNeg x10)
    hWit.elim fun g hg =>
      have hInputs' : ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).inputs,
          PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ), (13 : ℕ)].toFinset) u = Bool.true ∧
          PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ)].toFinset) u = Bool.false ∧
          PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) [(13 : ℕ)].toFinset) u = Bool.false :=
        fun u hu =>
          ⟨(congrArg (fun s => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) hS013).symm.trans (hg.2.2 u hu).1,
           (congrArg (fun s => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) hS0).symm.trans (hg.2.2 u hu).2.1,
           (congrArg (fun s => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s) u) hS13).symm.trans (hg.2.2 u hu).2.2⟩
      have hPath' : Relation.ReflTransGen
          (fun (a b : ℕ) => ∃ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate) (x12 : ℕ) (x13 : ℕ), x1.gates[x10]? = Option.some x11 ∧ b = (26 : ℕ) + x10 ∧ x11.inputs = [x12, x13] ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (a = x12 ∨ a = x13) ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ a = if PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ), (13 : ℕ)].toFinset) x12 = Bool.true then x12 else x13) ∧ PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ), (13 : ℕ)].toFinset) a = Bool.true ∧ PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) [(0 : ℕ), (13 : ℕ)].toFinset) b = Bool.true)
          ((26 : ℕ) + g) x1.output :=
        Eq.subst
          (motive := fun s => Relation.ReflTransGen (fun (a b : ℕ) => ∃ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate) (x12 : ℕ) (x13 : ℕ), x1.gates[x10]? = Option.some x11 ∧ b = (26 : ℕ) + x10 ∧ x11.inputs = [x12, x13] ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (a = x12 ∨ a = x13) ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ a = if PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s) x12 = Bool.true then x12 else x13) ∧ PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s) a = Bool.true ∧ PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) s) b = Bool.true) ((26 : ℕ) + g) x1.output)
          hS013 hg.1
      Or.elim (Relation.ReflTransGen.cases_head hPath')
        (fun heq => hDirectOut x1 hSz hAO hNodup hPos' hNeg' hL1 hL2 ⟨g, heq, hg.2.1, hInputs'⟩)
        (fun hex => hex.elim fun _ hc => hProperPath x1 hSz hAO hNodup hPos' hNeg' hL1 hL2 ⟨g, Relation.TransGen.head' hc.1 hc.2, hg.2.1, hInputs'⟩)
