import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18747_1
    (hCircuit :
      ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x3.size ≤ (64 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
        (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧
        (∀ (u v : Fin (13 : ℕ) → Bool),
          x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases u v x7) = Bool.true ↔
            ∃ (a b : Fin (13 : ℕ)),
              (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD b.val (0 : ℕ)).testBit a.val = Bool.true ∧
              u a = Bool.true ∧ v b = Bool.true) ∧
        ∃ (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),
          x3.output = (26 : ℕ) + x4 ∧
          x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧
          ∀ (x7 : Bool),
            have x8 : List Bool := x3.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (↑x8 = if x7 = Bool.true then (13 : ℕ) else (0 : ℕ)));
            x8.getD x5 Bool.false = Bool.false ∧ x8.getD x6 Bool.false = Bool.false)
    (hTableEquiv :
      ∀ (a b : Fin (13 : ℕ)),
        (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ↔
          (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD b.val (0 : ℕ)).testBit a.val = Bool.true)
    (hDisjoint :
      ∀ (u : Fin (13 : ℕ) → Bool) (a b : Fin (13 : ℕ)),
        (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) →
        u a = Bool.true →
        !(u b || u (b + (1 : Fin (13 : ℕ))) || u (b + (3 : Fin (13 : ℕ))) || u (b + (9 : Fin (13 : ℕ)))) = Bool.true →
        False) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∃ (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),               x3.output = (26 : ℕ) + x4 ∧                 x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧                   ∀ (x7 : Bool),                     have x8 : List Bool := x3.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (↑x8 = if x7 = Bool.true then (13 : ℕ) else (0 : ℕ)));                     x8.getD x5 Bool.false = Bool.false ∧ x8.getD x6 Bool.false = Bool.false) := by
  obtain ⟨x3, hSz, hAO, hNd, hEval, hOut⟩ := hCircuit
  refine ⟨x3, hSz, hAO, hNd, ?_, ?_, hOut⟩
  · intro a b hab
    exact (hEval _ _).mpr ⟨a, b, (hTableEquiv a b).mp hab, decide_eq_true rfl, decide_eq_true rfl⟩
  · intro u _
    refine Bool.eq_false_iff.mpr (fun he => ?_)
    obtain ⟨a, b, hBit, hua, hxb⟩ := (hEval u _).mp he
    exact hDisjoint u a b ((hTableEquiv a b).mpr hBit) hua hxb
