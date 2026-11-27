import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18707_1
    (hSub :
      ∃ (H : PEqualNP.CircuitLowerBounds.Circuit),
        H.size ≤ (58 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) H ∧
        (∀ g ∈ H.gates, g.inputs.Nodup) ∧
        (26 : ℕ) ≤ H.output ∧
        H.output < (26 : ℕ) + H.size ∧
        ∀ (x : Fin (26 : ℕ) → Bool),
          H.eval (List.ofFn x) = Bool.true ↔
            ∃ (l : Fin (13 : ℕ)), l ≠ (0 : Fin (13 : ℕ)) ∧
              x (Fin.natAdd (13 : ℕ) l) = Bool.true ∧
              (x (Fin.castAdd (13 : ℕ) l) || x (Fin.castAdd (13 : ℕ) (l + (1 : Fin (13 : ℕ)))) ||
               x (Fin.castAdd (13 : ℕ) (l + (3 : Fin (13 : ℕ)))) || x (Fin.castAdd (13 : ℕ) (l + (9 : Fin (13 : ℕ))))) = Bool.true)
    (hLift :
      ∀ (H : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) H →
        (∀ g ∈ H.gates, g.inputs.Nodup) →
        (26 : ℕ) ≤ H.output →
        H.output < (26 : ℕ) + H.size →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (k a b : ℕ),
          C.size ≤ H.size + (6 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
          (∀ g ∈ C.gates, g.inputs.Nodup) ∧
          C.output = (26 : ℕ) + k ∧
          C.gates[k]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] : PEqualNP.CircuitLowerBounds.Gate } ∧
          (∀ (x : Fin (26 : ℕ) → Bool),
            C.eval (List.ofFn x) =
              (H.eval (List.ofFn x) ||
                (x (Fin.natAdd (13 : ℕ) (0 : Fin (13 : ℕ))) &&
                  (x (Fin.castAdd (13 : ℕ) (0 : Fin (13 : ℕ))) ||
                   x (Fin.castAdd (13 : ℕ) ((0 : Fin (13 : ℕ)) + (1 : Fin (13 : ℕ)))) ||
                   x (Fin.castAdd (13 : ℕ) ((0 : Fin (13 : ℕ)) + (3 : Fin (13 : ℕ)))) ||
                   x (Fin.castAdd (13 : ℕ) ((0 : Fin (13 : ℕ)) + (9 : Fin (13 : ℕ)))))))) ∧
          (C.wires (List.ofFn fun (i : Fin (26 : ℕ)) => Decidable.decide (i = Fin.natAdd (13 : ℕ) (0 : Fin (13 : ℕ))))).getD a Bool.false = Bool.true ∧
          (C.wires (List.ofFn fun (i : Fin (26 : ℕ)) => Decidable.decide (i = Fin.castAdd (13 : ℕ) (0 : Fin (13 : ℕ))))).getD b Bool.false = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ) (x4 : ℕ), x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧ x1.output = (26 : ℕ) + x2 ∧ x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x6) = Bool.true ∧ (x5 (Fin.castAdd (13 : ℕ) x6) || x5 (Fin.castAdd (13 : ℕ) (x6 + (1 : Fin (13 : ℕ)))) || x5 (Fin.castAdd (13 : ℕ) (x6 + (3 : Fin (13 : ℕ)))) || x5 (Fin.castAdd (13 : ℕ) (x6 + (9 : Fin (13 : ℕ))))) = Bool.true) ∧ ∃ (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ)), (x1.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = x5))).getD x3 Bool.false = Bool.true ∧ (x1.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = x6))).getD x4 Bool.false = Bool.true) :=
  Exists.elim hSub (fun H hH =>
    Exists.elim (hLift H hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1) (fun C hC =>
      Exists.elim hC (fun k hk =>
        Exists.elim hk (fun a ha =>
          Exists.elim ha (fun b hb =>
            ⟨C, k, a, b,
              Nat.le_trans hb.1 (Nat.add_le_add_right hH.1 6),
              hb.2.1,
              hb.2.2.1,
              hb.2.2.2.1,
              hb.2.2.2.2.1,
              fun x =>
                Iff.intro
                  (fun hEval =>
                    Or.elim ((Bool.or_eq_true _ _).mp (Eq.trans (hb.2.2.2.2.2.1 x).symm hEval))
                      (fun hHev =>
                        Exists.elim ((hH.2.2.2.2.2 x).mp hHev) (fun l hl => ⟨l, hl.2⟩))
                      (fun h0 =>
                        ⟨0, (Bool.and_eq_true _ _).mp h0⟩))
                  (fun hEx =>
                    Exists.elim hEx (fun l hl =>
                      Eq.trans (hb.2.2.2.2.2.1 x) ((Bool.or_eq_true _ _).mpr
                        (Or.elim (Classical.em (l = 0))
                          (fun h0 => Or.inr ((Bool.and_eq_true _ _).mpr (h0 ▸ hl)))
                          (fun hne => Or.inl ((hH.2.2.2.2.2 x).mpr ⟨l, hne, hl⟩)))))),
              ⟨Fin.natAdd 13 (0 : Fin 13), Fin.castAdd 13 (0 : Fin 13), hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2⟩⟩)))))
