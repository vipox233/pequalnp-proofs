import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17469_2
    (hPrependOrGate :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (xs : List ℕ),
        xs.length ≤ (2 : ℕ) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (i : Fin C.gates.length), ∀ w ∈ (C.gates.get i).inputs, w < (27 : ℕ) + ↑i) →
        (∃ (i : Fin C.gates.length), ∃ w ∈ (C.gates.get i).inputs, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ w ∧ ∃ (j : Fin C.gates.length), w = (27 : ℕ) + ↑j ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 C' ∧
          C'.size = C.size + (1 : ℕ) ∧
          (∀ (i : Fin C'.gates.length), ∀ w ∈ (C'.gates.get i).inputs, w < (26 : ℕ) + ↑i) ∧
          (∀ (v : List Bool), v.length = (26 : ℕ) → C'.eval v = C.eval (v ++ [xs.any fun w => v.getD w Bool.false])) ∧
          (∃ (i : Fin C'.gates.length), ∃ w ∈ (C'.gates.get i).inputs, (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (26 : ℕ) ≤ w ∧ ∃ (j : Fin C'.gates.length), w = (26 : ℕ) + ↑j ∧ (C'.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C' (C'.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and)
    (hPure26NestedAndLB :
      have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (a b : Fin (13 : ℕ)) => (List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i = a)) ++ List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i = b);
      have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (S : Finset (Fin (13 : ℕ))) => (List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (i ∈ S)) ++ List.ofFn fun (i : Fin (13 : ℕ)) => Decidable.decide (∀ u ∈ S, u - i ∉ x6);
      have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (S : Finset (Fin (13 : ℕ))) => S.card = (4 : ℕ) ∧ ∀ (y : Fin (13 : ℕ)), {u ∈ S | u - y ∈ x6}.card ≤ (2 : ℕ);
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (i : Fin C.gates.length), ∀ w ∈ (C.gates.get i).inputs, w < (26 : ℕ) + ↑i) →
        (∀ (a b : Fin (13 : ℕ)), a - b ∈ x6 → C.eval (x7 a b) = Bool.true) →
        (∀ (S : Finset (Fin (13 : ℕ))), x9 S → C.eval (x8 S) = Bool.false) →
        (∃ (i : Fin C.gates.length), ∃ w ∈ (C.gates.get i).inputs, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (26 : ℕ) ≤ w ∧ ∃ (j : Fin C.gates.length), w = (26 : ℕ) + ↑j ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (64 : ℕ) ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size) := by
  intro C xs hLen hMono hBounds x6 x7 x8 x9 x10 hPos hNeg hNested hTopAnd
  have hLen7 : ∀ (a b : Fin (13 : ℕ)), (x7 a b).length = (26 : ℕ) := fun _ _ => by
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have hLen8 : ∀ (S : Finset (Fin (13 : ℕ))), (x8 S).length = (26 : ℕ) := fun _ => by
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  exact Exists.elim (hPrependOrGate C xs hLen hMono hBounds hNested hTopAnd) fun C' hC' =>
    have hLB : (64 : ℕ) ≤ C'.size :=
      hPure26NestedAndLB C' hC'.1 hC'.2.2.1
        (fun a b hab => Eq.trans (hC'.2.2.2.1 (x7 a b) (hLen7 a b)) (hPos a b hab))
        (fun S hS => Eq.trans (hC'.2.2.2.1 (x8 S) (hLen8 S)) (hNeg S hS))
        hC'.2.2.2.2.1 hC'.2.2.2.2.2
    Nat.le_of_succ_le_succ (Eq.subst (motive := fun k => (64 : ℕ) ≤ k) hC'.2.1 hLB)
