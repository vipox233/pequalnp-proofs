import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17149_2
    (hElimConstWire :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (i : Fin C.gates.length), ∀ w ∈ (C.gates.get i).inputs, w < (27 : ℕ) + ↑i) →
        (∃ (v0 v1 : List Bool), v0.length = (26 : ℕ) ∧ v1.length = (26 : ℕ) ∧ C.eval (v0 ++ [b]) = Bool.false ∧ C.eval (v1 ++ [b]) = Bool.true) →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 C' ∧
          C'.size ≤ C.size ∧
          (∀ (i : Fin C'.gates.length), ∀ w ∈ (C'.gates.get i).inputs, w < (26 : ℕ) + ↑i) ∧
          (∀ (v : List Bool), v.length = (26 : ℕ) → C'.eval v = C.eval (v ++ [b])))
    (hPure26LB :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (a b : Fin (13 : ℕ)) => (List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i = a)) ++ List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i = b);
      have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (S : Finset (Fin (13 : ℕ))) => (List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i ∈ S)) ++ List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (∀ u ∈ S, u - i ∉ x1);
      have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (S : Finset (Fin (13 : ℕ))) => S.card = (4 : ℕ) ∧ ∀ (y : Fin (13 : ℕ)), {u ∈ S | u - y ∈ x1}.card ≤ (2 : ℕ);
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (i : Fin C.gates.length), ∀ w ∈ (C.gates.get i).inputs, w < (26 : ℕ) + ↑i) →
        (∀ (a b : Fin (13 : ℕ)), a - b ∈ x1 → a ≠ (0 : Fin (13 : ℕ)) ∨ b ≠ x6 → C.eval (x2 a b) = Bool.true) →
        (∀ (S : Finset (Fin (13 : ℕ))), x4 S → C.eval (x3 S) = Bool.false) →
        (63 : ℕ) ≤ C.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 → x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) → (∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (63 : ℕ) ≤ x5.size) := by
  intro x1 x2 x3 x4 x5 x6 x7 hMono hBounds hPos hNeg _
  have hLen2 : ∀ a b : Fin (13 : ℕ), (x2 a b).length = (26 : ℕ) := fun a b => by
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have hLen3 : ∀ S : Finset (Fin (13 : ℕ)), (x3 S).length = (26 : ℕ) := fun S => by
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have hOval : x4 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} := by
    decide
  have hEdge : (1 : Fin (13 : ℕ)) - (1 : Fin (13 : ℕ)) ∈ x1 := by decide
  have hNe0 : (1 : Fin (13 : ℕ)) ≠ (0 : Fin (13 : ℕ)) := by decide
  have hEx := hElimConstWire x5 x7 hMono hBounds
    ⟨x3 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))},
     x2 (1 : Fin (13 : ℕ)) (1 : Fin (13 : ℕ)),
     hLen3 _, hLen2 _ _, hNeg _ hOval, hPos _ _ hEdge (Or.inl hNe0)⟩
  exact Exists.elim hEx fun C' hC' =>
    Nat.le_trans
      (hPure26LB C' x6 hC'.1 hC'.2.2.1
        (fun a b hab hne => Eq.trans (hC'.2.2.2 (x2 a b) (hLen2 a b)) (hPos a b hab hne))
        (fun S hS => Eq.trans (hC'.2.2.2 (x3 S) (hLen3 S)) (hNeg S hS)))
      hC'.2.1
