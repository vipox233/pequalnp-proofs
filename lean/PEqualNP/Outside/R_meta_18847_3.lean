import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18847_3
    (hMonoSound :
      ∀ (adj : Fin (9 : ℕ) → Fin (12 : ℕ) → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)), adj i j →
          C.eval (List.ofFn fun (k : Fin (21 : ℕ)) => Decidable.decide (k = Fin.castAdd (12 : ℕ) i ∨ k = Fin.natAdd (9 : ℕ) j)) = Bool.true) →
        (∀ (a : Fin (9 : ℕ) → Bool) (b : Fin (12 : ℕ) → Bool),
          (∀ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)), adj i j → a i = Bool.false ∨ b j = Bool.false) →
          C.eval (List.ofFn (Fin.append a b)) = Bool.false) →
        ∀ (x : Fin (21 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
          ∃ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)), adj i j ∧ x (Fin.castAdd (12 : ℕ) i) = Bool.true ∧ x (Fin.natAdd (9 : ℕ) j) = Bool.true)
    (hEdgeIndep :
      let adj : Fin (9 : ℕ) → Fin (12 : ℕ) → Prop := fun i j =>
        (([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ)) + ((j : ℕ) + (1 : ℕ))) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (43 : ℕ) ∧
        C.output < (21 : ℕ) + C.size ∧
        (∀ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)), adj i j →
          C.eval (List.ofFn fun (k : Fin (21 : ℕ)) => Decidable.decide (k = Fin.castAdd (12 : ℕ) i ∨ k = Fin.natAdd (9 : ℕ) j)) = Bool.true) ∧
        (∀ (a : Fin (9 : ℕ) → Bool) (b : Fin (12 : ℕ) → Bool),
          (∀ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)), adj i j → a i = Bool.false ∨ b j = Bool.false) →
          C.eval (List.ofFn (Fin.append a b)) = Bool.false)) :
    (have x1 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (43 : ℕ) ∧ x4.output < (21 : ℕ) + x4.size ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x4.eval (List.map (x2 x5 x6) x1) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x3 x7 x8) := by
  have hCoord : ∀ (p l : Fin (13 : ℕ)),
      ((p : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
        (((p : ℕ) + (l : ℕ)) % (13 : ℕ)) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ↔
      ∃ (i : Fin (9 : ℕ)) (j : Fin (12 : ℕ)),
        (([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ)) + ((j : ℕ) + (1 : ℕ))) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
        p = Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ)) ∧
        l = Fin.ofNat (13 : ℕ) ((j : ℕ) + (1 : ℕ)) := by decide
  dsimp only
  exact Exists.elim hEdgeIndep fun C hC =>
    let hFull := hMonoSound _ C hC.1 hC.2.2.2.1 hC.2.2.2.2
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
        fun i => ite_eq_left_iff.mpr (fun h => False.elim (h i.isLt))
      have hfR : ∀ (j : Fin (12 : ℕ)),
          f (Fin.natAdd (9 : ℕ) j) = Decidable.decide (Fin.ofNat (13 : ℕ) ((j : ℕ) + (1 : ℕ)) ∈ T) := fun j =>
        Eq.trans (ite_eq_right_iff.mpr (fun h => False.elim (Nat.not_lt.mpr (Nat.le_add_right (9 : ℕ) (j : ℕ)) h)))
          (congrArg (fun n => Decidable.decide (Fin.ofNat (13 : ℕ) n ∈ T))
            (Eq.trans (congrArg (· - (8 : ℕ)) (Nat.add_comm (9 : ℕ) (j : ℕ)))
              (Nat.add_sub_assoc (Nat.le_succ (8 : ℕ)) (j : ℕ))))
      ⟨fun hev =>
        Exists.elim ((hFull f).mp (congrArg C.eval hlist ▸ hev)) fun i hi =>
          Exists.elim hi fun j hj =>
            let p := Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD (i : ℕ) (0 : ℕ))
            let l := Fin.ofNat (13 : ℕ) ((j : ℕ) + (1 : ℕ))
            let hpS : p ∈ S := of_decide_eq_true (Eq.trans (hfL i).symm hj.2.1)
            let hlT : l ∈ T := of_decide_eq_true (Eq.trans (hfR j).symm hj.2.2)
            let hpl := (hCoord p l).mpr ⟨i, j, hj.1, rfl, rfl⟩
            ⟨p, hpS, hpl.1, l, hlT, hpl.2⟩,
       fun h =>
        Exists.elim h fun p hp =>
          Exists.elim hp.2.2 fun l hl =>
            Exists.elim ((hCoord p l).mp ⟨hp.2.1, hl.2⟩) fun i hi =>
              Exists.elim hi fun j hj =>
                congrArg C.eval hlist.symm ▸
                  (hFull f).mpr
                    ⟨i, j, hj.1,
                      Eq.trans (hfL i) (decide_eq_true (hj.2.1 ▸ hp.1)),
                      Eq.trans (hfR j) (decide_eq_true (hj.2.2 ▸ hl.1))⟩⟩⟩
