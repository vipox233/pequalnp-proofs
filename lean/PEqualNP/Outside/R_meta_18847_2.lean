import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18847_2
    (hCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (43 : ℕ) ∧
        C.output < (21 : ℕ) + C.size ∧
        ∀ (x : Fin (21 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
          ∃ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)),
            ([(3137 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)].getD (i : ℕ) (0 : ℕ)).testBit (j : ℕ) = Bool.true ∧
            x (Fin.castAdd (12 : ℕ) i) = Bool.true ∧
            x (Fin.natAdd (9 : ℕ) j) = Bool.true)
    (hTableEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        ((p : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
          (((p : ℕ) + (l : ℕ)) % (13 : ℕ)) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ↔
        ∃ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)),
          ([(3137 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (2092 : ℕ), (1046 : ℕ), (523 : ℕ)].getD (i : ℕ) (0 : ℕ)).testBit (j : ℕ) = Bool.true ∧
          p = Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ)) ∧
          l = Fin.ofNat (13 : ℕ) ((j : ℕ) + (1 : ℕ))) :
    (have x1 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (43 : ℕ) ∧ x4.output < (21 : ℕ) + x4.size ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x4.eval (List.map (x2 x5 x6) x1) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x3 x7 x8) := by
  dsimp only
  exact Exists.elim hCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, fun S T =>
      let f : Fin (21 : ℕ) → Bool := fun k =>
        if (k : ℕ) < (9 : ℕ) then
          Decidable.decide (Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (k : ℕ) (0 : ℕ)) ∈ S)
        else
          Decidable.decide (Fin.ofNat (13 : ℕ) ((k : ℕ) - (8 : ℕ)) ∈ T)
      have hlist : List.map (fun (x4 : Fin (26 : ℕ)) => if (x4 : ℕ) < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (x4 : ℕ) ∈ S) else Decidable.decide (Fin.ofNat (13 : ℕ) (x4 : ℕ) ∈ T))
          [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))] = List.ofFn f := rfl
      have hfL : ∀ (i : Fin (9 : ℕ)),
          f (Fin.castAdd (12 : ℕ) i) = Decidable.decide (Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ)) ∈ S) :=
        fun i => if_pos i.isLt
      have hfR : ∀ (j : Fin (12 : ℕ)),
          f (Fin.natAdd (9 : ℕ) j) = Decidable.decide (Fin.ofNat (13 : ℕ) ((j : ℕ) + (1 : ℕ)) ∈ T) := fun j =>
        Eq.trans (if_neg (Nat.not_lt.mpr (Nat.le_add_right (9 : ℕ) (j : ℕ))))
          (congrArg (fun n => Decidable.decide (Fin.ofNat (13 : ℕ) n ∈ T))
            (Eq.trans (congrArg (· - (8 : ℕ)) (Nat.add_comm (9 : ℕ) (j : ℕ)))
              (Nat.add_sub_assoc (Nat.le_succ (8 : ℕ)) (j : ℕ))))
      ⟨fun hev =>
        Exists.elim ((hC.2.2.2 f).mp (congrArg C.eval hlist ▸ hev)) fun i hi =>
          Exists.elim hi fun j hj =>
            let p := Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ))
            let l := Fin.ofNat (13 : ℕ) ((j : ℕ) + (1 : ℕ))
            let hpS : p ∈ S := of_decide_eq_true (Eq.trans (hfL i).symm hj.2.1)
            let hlT : l ∈ T := of_decide_eq_true (Eq.trans (hfR j).symm hj.2.2)
            let hpl := (hTableEquiv p l).mpr ⟨i, j, hj.1, rfl, rfl⟩
            ⟨p, hpS, hpl.1, l, hlT, hpl.2⟩,
       fun h =>
        Exists.elim h fun p hp =>
          Exists.elim hp.2.2 fun l hl =>
            Exists.elim ((hTableEquiv p l).mp ⟨hp.2.1, hl.2⟩) fun i hi =>
              Exists.elim hi fun j hj =>
                congrArg C.eval hlist.symm ▸
                  (hC.2.2.2 f).mpr
                    ⟨i, j, hj.1,
                      Eq.trans (hfL i) (decide_eq_true (hj.2.1 ▸ hp.1)),
                      Eq.trans (hfR j) (decide_eq_true (hj.2.2 ▸ hl.1))⟩⟩⟩
