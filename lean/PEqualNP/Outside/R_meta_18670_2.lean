import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18670_2
    (hFullSpec :
      have E : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (u v : Fin (12 : ℕ)) =>
        (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w0 w1 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (58 : ℕ) ∧
        C.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧
        Max.max C.output (Max.max w0 w1) < (24 : ℕ) + C.size ∧
        ∀ (x : Fin (24 : ℕ) → Bool),
          (C.eval (List.ofFn x) = Bool.true ↔
            ∃ (u v : Fin (12 : ℕ)), E u v ∧ x (Fin.castAdd (12 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (12 : ℕ) v) = Bool.true) ∧
          (C.eval (List.ofFn x) = Bool.false →
            (C.wires (List.ofFn x)).getD w0 Bool.false = (x (0 : Fin (24 : ℕ)) || x (1 : Fin (24 : ℕ)) || x (3 : Fin (24 : ℕ))) ∧
            (C.wires (List.ofFn x)).getD w1 Bool.false = (x (15 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)))))
    (hTestSound :
      have E : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (u v : Fin (12 : ℕ)) =>
        (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      have S : Bool → List ℕ := fun (b : Bool) =>
        if b = Bool.true then [(15 : ℕ), (16 : ℕ), (18 : ℕ)] else [(0 : ℕ), (1 : ℕ), (3 : ℕ)];
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w0 w1 : ℕ),
        (∀ (x : Fin (24 : ℕ) → Bool),
          (C.eval (List.ofFn x) = Bool.true ↔
            ∃ (u v : Fin (12 : ℕ)), E u v ∧ x (Fin.castAdd (12 : ℕ) u) = Bool.true ∧ x (Fin.natAdd (12 : ℕ) v) = Bool.true) ∧
          (C.eval (List.ofFn x) = Bool.false →
            (C.wires (List.ofFn x)).getD w0 Bool.false = (x (0 : Fin (24 : ℕ)) || x (1 : Fin (24 : ℕ)) || x (3 : Fin (24 : ℕ))) ∧
            (C.wires (List.ofFn x)).getD w1 Bool.false = (x (15 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ))))) →
        (∀ (u v : Fin (12 : ℕ)), E u v → C.eval (List.ofFn fun (k : Fin (24 : ℕ)) => Decidable.decide (k = Fin.castAdd (12 : ℕ) u ∨ k = Fin.natAdd (12 : ℕ) v)) = Bool.true) ∧
        (∀ (b : Bool) (k : Fin (24 : ℕ)), k.val ∈ S b → (C.wires (List.ofFn fun (j : Fin (24 : ℕ)) => Decidable.decide (j = k))).getD (if b = Bool.true then w1 else w0) Bool.false = Bool.true) ∧
        ∀ (x : Fin (24 : ℕ) → Bool),
          (∀ (u v : Fin (12 : ℕ)), E u v → x (Fin.castAdd (12 : ℕ) u) = Bool.true → x (Fin.natAdd (12 : ℕ) v) = Bool.false) →
          C.eval (List.ofFn x) = Bool.false ∧
          ∀ (b : Bool), (C.wires (List.ofFn fun (k : Fin (24 : ℕ)) => if k.val ∈ S b then Bool.false else x k)).getD (if b = Bool.true then w1 else w0) Bool.false = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (x2 x3 : Fin (12 : ℕ)) => Fin.succAbove (9 : Fin (13 : ℕ)) x2 + Fin.succAbove (0 : Fin (13 : ℕ)) x3 ∈ x1; have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x2 x5 x4 → x3 x5 = Bool.false); have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x2 x5 x6 → x4 x6 = Bool.false); have x5 : Bool → Finset (Fin (24 : ℕ)) := fun (x5 : Bool) => if x5 = Bool.true then {(15 : Fin (24 : ℕ)), (16 : Fin (24 : ℕ)), (18 : Fin (24 : ℕ))} else {(0 : Fin (24 : ℕ)), (1 : Fin (24 : ℕ)), (3 : Fin (24 : ℕ))}; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x6 ∧     x6.size ≤ (58 : ℕ) ∧       x6.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧         Max.max x6.output (Max.max x7 x8) < (24 : ℕ) + x6.size ∧           (∀ (x9 x10 : Fin (12 : ℕ)), x2 x9 x10 → x6.eval (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (12 : ℕ) x9 ∨ x12 = Fin.natAdd (12 : ℕ) x10)) = Bool.true) ∧             (∀ (x9 : Bool), ∀ x10 ∈ x5 x9, (x6.wires (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = x10))).getD (if x9 = Bool.true then x8 else x7) Bool.false = Bool.true) ∧               ∀ (x9 : Fin (12 : ℕ) → Bool),                 x4 (x3 x9) = x9 →                   have x11 : Fin (24 : ℕ) → Bool := Fin.append x9 (x3 x9);                   x6.eval (List.ofFn x11) = Bool.false ∧ ∀ (x12 : Bool), (x6.wires (List.ofFn fun (x13 : Fin (24 : ℕ)) => if x13 ∈ x5 x12 then Bool.false else x11 x13)).getD (if x12 = Bool.true then x8 else x7) Bool.false = Bool.false) := by
  intro x1 x2 x3 x4 x5
  have hMem1 : ∀ z : Fin (13 : ℕ), z.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔ z ∈ x1 := by decide
  have hMem5 : ∀ (b : Bool) (k : Fin (24 : ℕ)), k.val ∈ (if b = Bool.true then [(15 : ℕ), (16 : ℕ), (18 : ℕ)] else [(0 : ℕ), (1 : ℕ), (3 : ℕ)]) ↔ k ∈ x5 b := by decide
  refine Exists.elim hFullSpec fun C hC => ?_
  refine Exists.elim hC fun w0 hw0 => ?_
  refine Exists.elim hw0 fun w1 hw => ?_
  have hS := hTestSound C w0 w1 hw.2.2.2.2
  refine ⟨C, w0, w1, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, ?_, ?_, ?_⟩
  · exact fun u v huv => hS.1 u v ((hMem1 _).mpr huv)
  · exact fun b k hk => hS.2.1 b k ((hMem5 b k).mpr hk)
  · intro a _ha
    have hInd : ∀ (u v : Fin (12 : ℕ)),
        (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] →
        Fin.append a (x3 a) (Fin.castAdd (12 : ℕ) u) = Bool.true →
        Fin.append a (x3 a) (Fin.natAdd (12 : ℕ) v) = Bool.false := by
      intro u v huv hu
      rw [Fin.append_left] at hu
      rw [Fin.append_right]
      exact decide_eq_false fun hAll =>
        Bool.noConfusion (hu.symm.trans (hAll u ((hMem1 _).mp huv)))
    have hRes := hS.2.2 (Fin.append a (x3 a)) hInd
    refine ⟨hRes.1, fun b => ?_⟩
    have hEq : (fun (k : Fin (24 : ℕ)) => if k.val ∈ (if b = Bool.true then [(15 : ℕ), (16 : ℕ), (18 : ℕ)] else [(0 : ℕ), (1 : ℕ), (3 : ℕ)]) then Bool.false else Fin.append a (x3 a) k) =
        (fun (k : Fin (24 : ℕ)) => if k ∈ x5 b then Bool.false else Fin.append a (x3 a) k) := by
      funext k
      exact ite_congr (propext (hMem5 b k)) (fun _ => rfl) (fun _ => rfl)
    rw [← hEq]
    exact hRes.2 b
