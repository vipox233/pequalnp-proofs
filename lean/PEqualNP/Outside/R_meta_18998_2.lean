import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18998_2
    (hValidToAO2 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[i]? = some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (a b : Fin (26 + i)), g.inputs = [a.1, b.1] ∧ a ≠ b) ↔
        (PEqualNP.TopForm.IsAO2 26 C ∧ ∀ g ∈ C.gates, g.inputs.Nodup))
    (hDisjointOwnsShrink :
      have x1 : Fin 13 → Fin 13 → Prop := fun a b => a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9;
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        (PEqualNP.TopForm.IsAO2 26 C ∧ ∀ g ∈ C.gates, g.inputs.Nodup) ∧
        ∀ (x : Fin 26 → Bool), C.eval (List.ofFn x) = true ↔
          ∃ (p l : Fin 13), x1 p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        ok C → C.size ≤ 63 →
        ∀ (g : ℕ) (p1 l1 p2 l2 : Fin 13),
          p1 ≠ p2 → l1 ≠ l2 → x1 p1 l1 → x1 p2 l2 →
          PEqualNP.EdgeOwnership.Owns 26 C g (Fin.castAdd 13 p1) (Fin.natAdd 13 l1) →
          PEqualNP.EdgeOwnership.Owns 26 C g (Fin.castAdd 13 p2) (Fin.natAdd 13 l2) →
          ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), ok D ∧ D.size < C.size) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : Fin ((26 : ℕ) + x3)) (x7 : Fin ((26 : ℕ) + x3)), x4.inputs = [↑x6, ↑x7] ∧ x6 ≠ x7) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → x3.size ≤ (63 : ℕ) → ∀ (x6 : ℕ) (x7 x8 x9 x10 : Fin (13 : ℕ)), x7 ≠ x9 → x8 ≠ x10 → x1 x7 x8 → x1 x9 x10 → PEqualNP.EdgeOwnership.Owns (26 : ℕ) x3 x6 (Fin.castAdd (13 : ℕ) x7) (Fin.natAdd (13 : ℕ) x8) → PEqualNP.EdgeOwnership.Owns (26 : ℕ) x3 x6 (Fin.castAdd (13 : ℕ) x9) (Fin.natAdd (13 : ℕ) x10) → ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x2 x17 ∧ x17.size < x3.size) :=
  fun x3 hx2 hsz x6 x7 x8 x9 x10 h79 h80 h1 h2 ho1 ho2 =>
    Exists.elim (hDisjointOwnsShrink x3 ⟨(hValidToAO2 x3).mp hx2.1, hx2.2⟩ hsz x6 x7 x8 x9 x10 h79 h80 h1 h2 ho1 ho2) fun D hD =>
      ⟨D, ⟨(hValidToAO2 D).mpr hD.1.1, hD.1.2⟩, hD.2⟩
