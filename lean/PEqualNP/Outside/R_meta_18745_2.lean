import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18745_2
    (hTableEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        (([(5137 : ℕ), (2083 : ℕ), (4166 : ℕ), (141 : ℕ), (282 : ℕ), (564 : ℕ), (1128 : ℕ), (2256 : ℕ), (4512 : ℕ), (833 : ℕ), (1666 : ℕ), (3332 : ℕ), (6664 : ℕ)] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ↔
          (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ)) ∨ p = l + (9 : Fin (13 : ℕ))))
    (hNoTwoAnds :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        have n : ℕ := (26 : ℕ);
        have ls : ℕ → ℕ → Bool := fun a b => PEqualNP.ReadK.lineSingle C n (fun k => Decidable.decide (k = b)) a b;
        have w : List ℕ → ℕ → Bool := fun L => PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ L));
        have w01 : ℕ → Bool := w [(0 : ℕ), (13 : ℕ)];
        C.size = (64 : ℕ) →
        n ≤ C.output →
        C.output < n + C.size →
        PEqualNP.TopForm.IsAO2 n C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ (x : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)),
              (([(5137 : ℕ), (2083 : ℕ), (4166 : ℕ), (141 : ℕ), (282 : ℕ), (564 : ℕ), (1128 : ℕ), (2256 : ℕ), (4512 : ℕ), (833 : ℕ), (1666 : ℕ), (3332 : ℕ), (6664 : ℕ)] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        ls (0 : ℕ) (13 : ℕ) = Bool.false →
        ls (13 : ℕ) (0 : ℕ) = Bool.false →
        have step : ℕ → ℕ → Prop := fun a b =>
          ∃ (idx : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u v : ℕ),
            C.gates[idx]? = Option.some g ∧ b = n + idx ∧ g.inputs = [u, v] ∧
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (a = u ∨ a = v) ∨
              g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ a = if w01 u = Bool.true then u else v) ∧
            w01 a = Bool.true ∧ w01 b = Bool.true;
        have wit : ℕ → ℕ → Prop := fun s j =>
          Relation.ReflTransGen step (n + j) C.output ∧ PEqualNP.ReadTwo.isAnd C j ∧
          ∀ q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, w01 q = Bool.true ∧ w [s] q = Bool.false;
        (∃ (j1 j2 : ℕ), j1 ≠ j2 ∧ wit (0 : ℕ) j1 ∧ wit (13 : ℕ) j2 ∧
          w [(13 : ℕ)] (n + j1) = Bool.false ∧ w [(0 : ℕ)] (n + j2) = Bool.false) →
        False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size = (64 : ℕ) →     (26 : ℕ) ≤ x1.output →       x1.output < (26 : ℕ) + x1.size →         PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →           (∀ x6 ∈ x1.gates, x6.inputs.Nodup) →             (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →                 PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x9 : ℕ) => Decidable.decide (x9 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                   have x10 : Finset ℕ → ℕ → Bool := fun (x10 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x10);                   have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ) (x16 : ℕ), x1.gates[x13]? = Option.some x14 ∧ x12 = (26 : ℕ) + x13 ∧ x14.inputs = [x15, x16] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x15 ∨ x11 = x16) ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x11 = if x10 {(0 : ℕ), (13 : ℕ)} x15 = Bool.true then x15 else x16) ∧ x10 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true ∧ x10 {(0 : ℕ), (13 : ℕ)} x12 = Bool.true;                   have x12 : ℕ → ℕ → Prop := fun (x12 x13 : ℕ) => Relation.ReflTransGen x11 ((26 : ℕ) + x13) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, x10 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true ∧ x10 {x12} x14 = Bool.false;                   (∃ (x13 : ℕ) (x14 : ℕ), x13 ≠ x14 ∧ x12 (0 : ℕ) x13 ∧ x12 (13 : ℕ) x14 ∧ x10 {(13 : ℕ)} ((26 : ℕ) + x13) = Bool.false ∧ x10 {(0 : ℕ)} ((26 : ℕ) + x14) = Bool.false) → False) := by
  intro C hSz hOut1 hOut2 hAO hNodup hEval hLS1 hLS2 x10 x11 x12 hEx
  have hEq013 : PEqualNP.ReadTwo.indW (26 : ℕ) {(0 : ℕ), (13 : ℕ)} = fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ), (13 : ℕ)]) := by
    funext k; revert k; decide
  have hEq0 : PEqualNP.ReadTwo.indW (26 : ℕ) {(0 : ℕ)} = fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ)]) := by
    funext k; revert k; decide
  have hEq13 : PEqualNP.ReadTwo.indW (26 : ℕ) {(13 : ℕ)} = fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(13 : ℕ)]) := by
    funext k; revert k; decide
  have hEval' : ∀ (x : Fin (26 : ℕ) → Bool),
      C.eval (List.ofFn x) = Bool.true ↔
        ∃ (p l : Fin (13 : ℕ)),
          (([(5137 : ℕ), (2083 : ℕ), (4166 : ℕ), (141 : ℕ), (282 : ℕ), (564 : ℕ), (1128 : ℕ), (2256 : ℕ), (4512 : ℕ), (833 : ℕ), (1666 : ℕ), (3332 : ℕ), (6664 : ℕ)] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ∧
          x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true := fun x =>
    Iff.trans (hEval x)
      (Iff.intro
        (fun h => Exists.elim h fun p hp => Exists.elim hp fun l hl => ⟨p, l, (hTableEquiv p l).mpr hl.1, hl.2.1, hl.2.2⟩)
        (fun h => Exists.elim h fun p hp => Exists.elim hp fun l hl => ⟨p, l, (hTableEquiv p l).mp hl.1, hl.2.1, hl.2.2⟩))
  refine hNoTwoAnds C hSz hOut1 hOut2 hAO hNodup hEval' hLS1 hLS2 ?_
  have hw013 : x10 {(0 : ℕ), (13 : ℕ)} = PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ), (13 : ℕ)])) :=
    congrArg (PEqualNP.ReadTwo.wval C) hEq013
  have hw0 : x10 {(0 : ℕ)} = PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ)])) :=
    congrArg (PEqualNP.ReadTwo.wval C) hEq0
  have hw13 : x10 {(13 : ℕ)} = PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(13 : ℕ)])) :=
    congrArg (PEqualNP.ReadTwo.wval C) hEq13
  have hStepEq : x11 = fun a b =>
      ∃ (idx : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u v : ℕ),
        C.gates[idx]? = Option.some g ∧ b = (26 : ℕ) + idx ∧ g.inputs = [u, v] ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (a = u ∨ a = v) ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ a = if PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ), (13 : ℕ)])) u = Bool.true then u else v) ∧
        PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ), (13 : ℕ)])) a = Bool.true ∧
        PEqualNP.ReadTwo.wval C (fun (k : Fin (26 : ℕ)) => Decidable.decide (k.val ∈ [(0 : ℕ), (13 : ℕ)])) b = Bool.true := by
    funext a b
    dsimp only [x11]
    rw [hw013]
  refine Exists.elim hEx fun j1 hj1 => Exists.elim hj1 fun j2 hj => ?_
  have h1 := hj.2.1
  have h2 := hj.2.2.1
  have h3 := hj.2.2.2.1
  have h4 := hj.2.2.2.2
  dsimp only [x12] at h1 h2
  rw [hStepEq, hw013, hw0] at h1
  rw [hStepEq, hw013, hw13] at h2
  rw [hw13] at h3
  rw [hw0] at h4
  exact ⟨j1, j2, hj.1, h1, h2, h3, h4⟩
