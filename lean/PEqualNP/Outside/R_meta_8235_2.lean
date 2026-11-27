import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8235_2
    (hOutputInput :
      ∀ (x1 : Fin (64 : ℕ)) (x2 : Fin (90 : ℕ)) (x3 : Fin ↑x1 → Bool) (x4 x5 : Fin ↑x1 → Option (Fin (90 : ℕ))),
        ↑x2 < (26 : ℕ) →
        have x6 : PEqualNP.CircuitLowerBounds.Circuit :=
          { gates := List.ofFn fun (x6 : Fin ↑x1) =>
              { op := if x3 x6 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or,
                inputs := List.filterMap (Option.map Fin.val) [x4 x6, x5 x6] : PEqualNP.CircuitLowerBounds.Gate },
            output := ↑x2 : PEqualNP.CircuitLowerBounds.Circuit };
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 →
          x6.eval (PEqualNP.GenericRejection.incidenceInput ([x7].toFinset) ([x8].toFinset)) = Bool.true) →
        (∀ (x8 : Finset (Fin (13 : ℕ))),
          PEqualNP.GenericRejection.IsMaximalFalse PEqualNP.HeptadCover.singerLines3 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) →
          x6.eval (PEqualNP.GenericRejection.incidenceInput x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8)) = Bool.false) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x6 (1 : ℕ) ∨
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x6 (1 : ℕ))
    (hOutputGate :
      ∀ (x1 : Fin (64 : ℕ)) (x2 : Fin (90 : ℕ)) (x3 : Fin ↑x1 → Bool) (x4 x5 : Fin ↑x1 → Option (Fin (90 : ℕ))),
        (26 : ℕ) ≤ ↑x2 →
        have x6 : PEqualNP.CircuitLowerBounds.Circuit :=
          { gates := List.ofFn fun (x6 : Fin ↑x1) =>
              { op := if x3 x6 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or,
                inputs := List.filterMap (Option.map Fin.val) [x4 x6, x5 x6] : PEqualNP.CircuitLowerBounds.Gate },
            output := ↑x2 : PEqualNP.CircuitLowerBounds.Circuit };
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 →
          x6.eval (PEqualNP.GenericRejection.incidenceInput ([x7].toFinset) ([x8].toFinset)) = Bool.true) →
        (∀ (x8 : Finset (Fin (13 : ℕ))),
          PEqualNP.GenericRejection.IsMaximalFalse PEqualNP.HeptadCover.singerLines3 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) →
          x6.eval (PEqualNP.GenericRejection.incidenceInput x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8)) = Bool.false) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x6 (1 : ℕ) ∨
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x6 (1 : ℕ)) :
    (∀ (x1 : Fin (64 : ℕ)) (x2 : Fin (90 : ℕ)) (x3 : Fin ↑x1 → Bool) (x4 x5 : Fin ↑x1 → Option (Fin (90 : ℕ))),   have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x6 : Fin ↑x1) => { op := if x3 x6 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.filterMap (Option.map Fin.val) [x4 x6, x5 x6] : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x2 : PEqualNP.CircuitLowerBounds.Circuit };   (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x6.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x8}) = Bool.true) → (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse PEqualNP.HeptadCover.singerLines3 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) → x6.eval (PEqualNP.GenericRejection.incidenceInput x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8)) = Bool.false) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x6 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x6 (1 : ℕ)) := by
  intro x1 x2 x3 x4 x5 x6 hPos hNeg
  have hS : ∀ a : Fin (13 : ℕ), ([a].toFinset : Finset (Fin (13 : ℕ))) = {a} := fun a => by ext z; simp
  have hPos' : ∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 →
      x6.eval (PEqualNP.GenericRejection.incidenceInput ([x7].toFinset) ([x8].toFinset)) = Bool.true :=
    fun x7 x8 h78 => by simpa only [hS] using hPos x7 x8 h78
  exact Or.elim (Nat.lt_or_ge ↑x2 (26 : ℕ))
    (fun hlt => hOutputInput x1 x2 x3 x4 x5 hlt hPos' hNeg)
    (fun hge => hOutputGate x1 x2 x3 x4 x5 hge hPos' hNeg)
