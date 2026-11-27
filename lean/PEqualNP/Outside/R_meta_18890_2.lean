import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18890_2
    (hRepNonEdge :
      ∀ a ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)],
        ∃ (u v : Fin (25 : ℕ)),
          u ≠ v ∧
          (∀ (x : Fin (25 : ℕ)), (↑x = a / (25 : ℕ) ∨ ↑x = a % (25 : ℕ)) ↔ (x = u ∨ x = v)) ∧
          (∀ (p : Fin (12 : ℕ)) (l : Fin (13 : ℕ)),
            p.succ ∈ PEqualNP.HeptadCover.singerLines3 l →
            ¬((Fin.castAdd (13 : ℕ) p = u ∨ Fin.castAdd (13 : ℕ) p = v) ∧
              (Fin.natAdd (12 : ℕ) l = u ∨ Fin.natAdd (12 : ℕ) l = v))))
    (hAnyNonEdgePair :
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 c →
        (∀ (x : Fin (25 : ℕ) → Bool),
          c.eval (List.ofFn x) = Bool.true ↔
            ∃ (p : Fin (12 : ℕ)) (l : Fin (13 : ℕ)),
              p.succ ∈ PEqualNP.HeptadCover.singerLines3 l ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              x (Fin.natAdd (12 : ℕ) l) = Bool.true) →
        (∃ (g : Fin c.gates.length) (u v : Fin (25 : ℕ)),
          u ≠ v ∧
          c.eval (List.ofFn fun (i : Fin (25 : ℕ)) => Decidable.decide (i = u ∨ i = v)) = Bool.false ∧
          (c.gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (25 : ℕ) + ↑g ≠ c.output ∧
          (c.wires (List.ofFn fun (i : Fin (25 : ℕ)) => Decidable.decide (i = u ∨ i = v))).getD ((25 : ℕ) + ↑g) Bool.false = Bool.true) →
        (59 : ℕ) ≤ c.size) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x1 x3 → x2 x3 → (59 : ℕ) ≤ x3.size) :=
  fun x3 hM h1 h2 =>
    Exists.elim h2 fun g hg =>
      Exists.elim hg fun a haAll =>
        Exists.elim (hRepNonEdge a haAll.1) fun u hu =>
          Exists.elim hu fun v hv =>
            hAnyNonEdgePair x3 hM h1
              ⟨g, u, v, hv.1,
                Bool.eq_false_iff.mpr fun hTrue =>
                  Exists.elim ((h1 (fun i => Decidable.decide (i = u ∨ i = v))).mp hTrue) fun p hp =>
                    Exists.elim hp fun l hl =>
                      hv.2.2 p l hl.1 ⟨of_decide_eq_true hl.2.1, of_decide_eq_true hl.2.2⟩,
                haAll.2.1,
                haAll.2.2.1,
                Eq.trans
                  (congrArg (fun f => (x3.wires (List.ofFn f)).getD ((25 : ℕ) + ↑g) Bool.false)
                    (funext fun i =>
                      (decide_eq_decide.mpr (hv.2.1 i)).symm))
                  haAll.2.2.2⟩
