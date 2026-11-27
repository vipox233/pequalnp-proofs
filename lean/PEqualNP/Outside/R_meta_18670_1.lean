import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18670_1
    (hTableEquiv : ∀ (u v : Fin (12 : ℕ)), (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true ↔ (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])
    (hCircuit : let x2 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (u v : Fin (12 : ℕ)) => (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true; have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (a : Fin (12 : ℕ) → Bool) (v : Fin (12 : ℕ)) => Decidable.decide (∀ (u : Fin (12 : ℕ)), x2 u v → a u = Bool.false); have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (b : Fin (12 : ℕ) → Bool) (u : Fin (12 : ℕ)) => Decidable.decide (∀ (v : Fin (12 : ℕ)), x2 u v → b v = Bool.false); have x5 : Bool → List ℕ := fun (b : Bool) => if b = Bool.true then [(15 : ℕ), (16 : ℕ), (18 : ℕ)] else [(0 : ℕ), (1 : ℕ), (3 : ℕ)]; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ (58 : ℕ) ∧ x6.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ Max.max x6.output (Max.max x7 x8) < (24 : ℕ) + x6.size ∧ (∀ (u v : Fin (12 : ℕ)), x2 u v → x6.eval (List.ofFn fun (k : Fin (24 : ℕ)) => Decidable.decide (k = Fin.castAdd (12 : ℕ) u ∨ k = Fin.natAdd (12 : ℕ) v)) = Bool.true) ∧ (∀ (b : Bool) (k : Fin (24 : ℕ)), k.val ∈ x5 b → (x6.wires (List.ofFn fun (j : Fin (24 : ℕ)) => Decidable.decide (j = k))).getD (if b = Bool.true then x8 else x7) Bool.false = Bool.true) ∧ ∀ (a : Fin (12 : ℕ) → Bool), x4 (x3 a) = a → have x11 : Fin (24 : ℕ) → Bool := Fin.append a (x3 a); x6.eval (List.ofFn x11) = Bool.false ∧ ∀ (b : Bool), (x6.wires (List.ofFn fun (k : Fin (24 : ℕ)) => if k.val ∈ x5 b then Bool.false else x11 k)).getD (if b = Bool.true then x8 else x7) Bool.false = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (x2 x3 : Fin (12 : ℕ)) => Fin.succAbove (9 : Fin (13 : ℕ)) x2 + Fin.succAbove (0 : Fin (13 : ℕ)) x3 ∈ x1; have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x2 x5 x4 → x3 x5 = Bool.false); have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x2 x5 x6 → x4 x6 = Bool.false); have x5 : Bool → Finset (Fin (24 : ℕ)) := fun (x5 : Bool) => if x5 = Bool.true then {(15 : Fin (24 : ℕ)), (16 : Fin (24 : ℕ)), (18 : Fin (24 : ℕ))} else {(0 : Fin (24 : ℕ)), (1 : Fin (24 : ℕ)), (3 : Fin (24 : ℕ))}; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x6 ∧     x6.size ≤ (58 : ℕ) ∧       x6.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧         Max.max x6.output (Max.max x7 x8) < (24 : ℕ) + x6.size ∧           (∀ (x9 x10 : Fin (12 : ℕ)), x2 x9 x10 → x6.eval (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (12 : ℕ) x9 ∨ x12 = Fin.natAdd (12 : ℕ) x10)) = Bool.true) ∧             (∀ (x9 : Bool), ∀ x10 ∈ x5 x9, (x6.wires (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = x10))).getD (if x9 = Bool.true then x8 else x7) Bool.false = Bool.true) ∧               ∀ (x9 : Fin (12 : ℕ) → Bool),                 x4 (x3 x9) = x9 →                   have x11 : Fin (24 : ℕ) → Bool := Fin.append x9 (x3 x9);                   x6.eval (List.ofFn x11) = Bool.false ∧ ∀ (x12 : Bool), (x6.wires (List.ofFn fun (x13 : Fin (24 : ℕ)) => if x13 ∈ x5 x12 then Bool.false else x11 x13)).getD (if x12 = Bool.true then x8 else x7) Bool.false = Bool.false) := by
  intro x1 x2 x3 x4 x5
  obtain ⟨x6, x7, x8, hM, hSz, hHead, hMax, hEdges, hSing, hInd⟩ := hCircuit
  have hmem1 : ∀ z : Fin (13 : ℕ), z.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔ z ∈ x1 := by
    decide
  have hx2 : ∀ u v : Fin (12 : ℕ), (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true ↔ x2 u v :=
    fun u v => (hTableEquiv u v).trans (hmem1 _)
  have hmem5 : ∀ (b : Bool) (k : Fin (24 : ℕ)), k.val ∈ (if b = Bool.true then [(15 : ℕ), (16 : ℕ), (18 : ℕ)] else [(0 : ℕ), (1 : ℕ), (3 : ℕ)]) ↔ k ∈ x5 b := by
    decide
  have hx3 : (fun (a : Fin (12 : ℕ) → Bool) (v : Fin (12 : ℕ)) => Decidable.decide (∀ (u : Fin (12 : ℕ)), (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true → a u = Bool.false)) = x3 := by
    funext a v
    rw [decide_eq_decide]
    exact ⟨fun h u hu => h u ((hx2 u v).mpr hu), fun h u hu => h u ((hx2 u v).mp hu)⟩
  have hx4 : (fun (b : Fin (12 : ℕ) → Bool) (u : Fin (12 : ℕ)) => Decidable.decide (∀ (v : Fin (12 : ℕ)), (([(261 : ℕ), (2178 : ℕ), (3137 : ℕ), (1568 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD u.val (0 : ℕ)).testBit v.val = Bool.true → b v = Bool.false)) = x4 := by
    funext b u
    rw [decide_eq_decide]
    exact ⟨fun h v hv => h v ((hx2 u v).mpr hv), fun h v hv => h v ((hx2 u v).mp hv)⟩
  refine ⟨x6, x7, x8, hM, hSz, hHead, hMax, ?_, ?_, ?_⟩
  · exact fun u v huv => hEdges u v ((hx2 u v).mpr huv)
  · exact fun b k hk => hSing b k ((hmem5 b k).mpr hk)
  · intro a ha
    have ha' := hInd a (by rw [hx3, hx4]; exact ha)
    rw [hx3] at ha'
    refine ⟨ha'.1, fun b => ?_⟩
    have hfun : (fun k : Fin (24 : ℕ) => if k.val ∈ (if b = Bool.true then [(15 : ℕ), (16 : ℕ), (18 : ℕ)] else [(0 : ℕ), (1 : ℕ), (3 : ℕ)]) then Bool.false else Fin.append a (x3 a) k) = (fun k : Fin (24 : ℕ) => if k ∈ x5 b then Bool.false else Fin.append a (x3 a) k) := by
      funext k
      by_cases hk : k ∈ x5 b
      · rw [if_pos ((hmem5 b k).mpr hk), if_pos hk]
      · rw [if_neg (fun h => hk ((hmem5 b k).mp h)), if_neg hk]
    rw [← hfun]
    exact ha'.2 b
