import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18079_2
    (hCompactCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (43 : ℕ) ∧
        C.output < (21 : ℕ) + C.size ∧
        ∀ (x : Fin (21 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)),
              (([(3137 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD i.val (0 : ℕ)).testBit j.val = Bool.true ∧
              x (Fin.castAdd (12 : ℕ) i) = Bool.true ∧
              x (Fin.natAdd (9 : ℕ) j) = Bool.true)
    (hCoordEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        (p.val ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
          (p.val + l.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ↔
        ∃ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)),
          (([(3137 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)] : List ℕ).getD i.val (0 : ℕ)).testBit j.val = Bool.true ∧
          ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)] : List ℕ).getD i.val (0 : ℕ) = p.val ∧
          j.val + (1 : ℕ) = l.val) :
    (have x1 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))]; have x2 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (↑x3 ∉ x2 ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ x2); have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) => List.map (fun (x6 : Fin (26 : ℕ)) => if ↑x6 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x6 ∈ x4) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x6 ∈ x5)) x1; ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (43 : ℕ) ∧ x5.output < (21 : ℕ) + x5.size ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x3 x6 x7 = Bool.true → x5.eval (x4 {x6} {x7}) = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x5.eval (x4 x6 {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, x3 x8 x7 = Bool.false}) = Bool.false) := by
  intro x1 x2 x3 x4
  have hLeft : ∀ (i : Fin (9 : ℕ)),
      (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val < (13 : ℕ) ∧
      (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val).val =
        ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)] : List ℕ).getD i.val (0 : ℕ) := by
    decide
  have hRight : ∀ (j : Fin (12 : ℕ)),
      ¬((x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val < (13 : ℕ)) ∧
      (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val).val = j.val + (1 : ℕ) := by
    decide
  refine Exists.elim hCompactCircuit fun C hC => ?_
  refine ⟨C, hC.1, hC.2.1, hC.2.2.1, ?_, ?_⟩
  · intro p l hpl
    have hprop := of_decide_eq_true hpl
    refine Exists.elim ((hCoordEquiv p l).mp hprop) fun i hi => ?_
    refine Exists.elim hi fun j hj => ?_
    let xVec : Fin (21 : ℕ) → Bool := fun idx =>
      have k := x1.getD idx.val (0 : Fin (26 : ℕ))
      if (k : ℕ) < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ ({p} : Finset (Fin (13 : ℕ))))
      else Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ ({l} : Finset (Fin (13 : ℕ))))
    have hMap : x4 {p} {l} = List.ofFn xVec := rfl
    rw [hMap]
    refine (hC.2.2.2 xVec).mpr ⟨i, j, hj.1, ?_, ?_⟩
    · change (if (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then
        Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val ∈ ({p} : Finset (Fin (13 : ℕ))))
        else Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val ∈ ({l} : Finset (Fin (13 : ℕ))))) = Bool.true
      rw [if_pos (hLeft i).1]
      have hpEq : Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val = p :=
        Fin.ext ((hLeft i).2.trans hj.2.1)
      rw [hpEq]
      exact decide_eq_true (Finset.mem_singleton_self p)
    · change (if (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then
        Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val ∈ ({p} : Finset (Fin (13 : ℕ))))
        else Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val ∈ ({l} : Finset (Fin (13 : ℕ))))) = Bool.true
      rw [if_neg (hRight j).1]
      have hlEq : Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val = l :=
        Fin.ext ((hRight j).2.trans hj.2.2)
      rw [hlEq]
      exact decide_eq_true (Finset.mem_singleton_self l)
  · intro S
    let T : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | ∀ x8 ∈ S, x3 x8 x7 = Bool.false}
    let xVec : Fin (21 : ℕ) → Bool := fun idx =>
      have k := x1.getD idx.val (0 : Fin (26 : ℕ))
      if (k : ℕ) < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ S)
      else Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ T)
    have hMap : x4 S T = List.ofFn xVec := rfl
    rw [hMap]
    refine Bool.eq_false_iff.mpr fun ht => ?_
    refine Exists.elim ((hC.2.2.2 xVec).mp ht) fun i hi => ?_
    refine Exists.elim hi fun j hj => ?_
    have hxi : xVec (Fin.castAdd (12 : ℕ) i) = Bool.true := hj.2.1
    have hxj : xVec (Fin.natAdd (9 : ℕ) j) = Bool.true := hj.2.2
    change (if (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then
      Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val ∈ S)
      else Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val ∈ T)) = Bool.true at hxi
    rw [if_pos (hLeft i).1] at hxi
    change (if (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then
      Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val ∈ S)
      else Decidable.decide (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val ∈ T)) = Bool.true at hxj
    rw [if_neg (hRight j).1] at hxj
    have hpS : Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val ∈ S := of_decide_eq_true hxi
    have hlT : Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val ∈ T := of_decide_eq_true hxj
    have hFalse : x3 (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val)
        (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val) = Bool.false :=
      (Finset.mem_filter.mp hlT).2 _ hpS
    have hProp := (hCoordEquiv _ _).mpr ⟨i, j, hj.1, (hLeft i).2.symm, (hRight j).2.symm⟩
    have hTrue : x3 (Fin.ofNat (13 : ℕ) (x1.getD (Fin.castAdd (12 : ℕ) i).val (0 : Fin (26 : ℕ))).val)
        (Fin.ofNat (13 : ℕ) (x1.getD (Fin.natAdd (9 : ℕ) j).val (0 : Fin (26 : ℕ))).val) = Bool.true :=
      decide_eq_true hProp
    exact Bool.noConfusion (hTrue.symm.trans hFalse)
