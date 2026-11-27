import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7792_2
    (hQuad0125 :
      PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3
        {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))})
    (hGenQuad :
      have s : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have inp : Finset (Fin (13 : ℕ)) → List Bool := fun (Q : Finset (Fin (13 : ℕ))) =>
        PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines s Q);
      have isInner : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop :=
        fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) =>
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ (k : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.InCone (26 : ℕ) C g k;
      have fires : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ)) → Prop :=
        fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (Q : Finset (Fin (13 : ℕ))) =>
          (C.wires (inp Q)).getD ((26 : ℕ) + g) Bool.false = Bool.true;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (Q0 : Finset (Fin (13 : ℕ))) (g0 : ℕ),
        PEqualNP.HeptadCover.IsQuadrangle s Q0 →
        g0 < C.size →
        isInner C g0 →
        fires C g0 Q0 →
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
        PEqualNP.GenericRejection.RightOnIncidentPairs s C →
        (∀ (Q : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle s Q → C.eval (inp Q) = Bool.false) →
        (∀ (g : ℕ), isInner C g →
          (∃ (Q : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle s Q ∧ fires C g Q) ∧
          (2 : ℕ) ≤ {e ∈ PEqualNP.HeptadCover.incidences s | { gates := C.gates.set g { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := C.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}) = Bool.false}.card) →
        (64 : ℕ) ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ)) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Finset (Fin (13 : ℕ))) => (x4.wires (x2 x6)).getD ((26 : ℕ) + x5) Bool.false = Bool.true; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → PEqualNP.GenericRejection.RightOnIncidentPairs x1 x5 → (∀ (x9 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x9 → x5.eval (x2 x9) = Bool.false) → (∀ (x10 : ℕ), x3 x5 x10 → (∃ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 ∧ x4 x5 x10 x12) ∧ (2 : ℕ) ≤ {x12 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x12.1} {x12.2}) = Bool.false}.card) → (∃ (x11 : ℕ), x3 x5 x11 ∧ x4 x5 x11 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))}) → (64 : ℕ) ≤ x5.size := by
  intro x1 x2 x3 x4 x5 hmono hrb hright hquad hinner hex
  rcases hex with ⟨x11, hx3, hx4⟩
  have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init).length =
        init.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro init
      rfl
    | cons g gs ih =>
      intro init
      change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)])
        (init ++ [g.op.eval (g.inputs.map fun i => init.getD i Bool.false)])).length =
        init.length + (gs.length + 1)
      rw [ih, List.length_append]
      change init.length + 1 + gs.length = init.length + (gs.length + 1)
      omega
  have hlen : (x5.wires (x2 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))})).length =
      26 + x5.size := by
    change (x5.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)])
      (x2 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))})).length =
      26 + x5.gates.length
    rw [hfold]
    have hinp : (x2 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))}).length = 26 := by
      change (List.ofFn (fun p : Fin 13 => decide (p ∈ ({(0 : Fin 13), 1, 2, 5} : Finset (Fin 13)))) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines x1 {(0 : Fin 13), 1, 2, 5}))).length = 26
      rw [List.length_append, List.length_ofFn, List.length_ofFn]
    rw [hinp]
  have hgetD : ∀ (ws : List Bool) (k : ℕ), ws.getD k Bool.false = Bool.true → k < ws.length := by
    intro ws
    induction ws with
    | nil =>
      intro k hk
      cases hk
    | cons b ws ih =>
      intro k hk
      cases k with
      | zero =>
        change 0 < ws.length + 1
        omega
      | succ k =>
        have hk' : ws.getD k Bool.false = Bool.true := hk
        have hlt := ih k hk'
        change k + 1 < ws.length + 1
        omega
  have hxlt_sum : 26 + x11 < (x5.wires (x2 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))})).length :=
    hgetD _ _ hx4
  rw [hlen] at hxlt_sum
  have hx11lt : x11 < x5.size := by omega
  exact hGenQuad x5 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))} x11
    hQuad0125 hx11lt hx3 hx4 hmono hrb hright hquad hinner
