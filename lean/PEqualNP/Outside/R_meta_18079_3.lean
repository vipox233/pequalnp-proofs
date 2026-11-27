import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18079_3
    (hStarCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (43 : ℕ) ∧
        C.output < (21 : ℕ) + C.size ∧
        ∀ (x : Fin (21 : ℕ) → Bool),
          C.eval (List.ofFn x) = ((x (0 : Fin (21 : ℕ)) && (x (9 : Fin (21 : ℕ)) || x (15 : Fin (21 : ℕ)) || x (19 : Fin (21 : ℕ)) || x (20 : Fin (21 : ℕ)))) || (x (1 : Fin (21 : ℕ)) && (x (13 : Fin (21 : ℕ)) || x (17 : Fin (21 : ℕ)) || x (18 : Fin (21 : ℕ)) || x (20 : Fin (21 : ℕ)))) || (x (2 : Fin (21 : ℕ)) && (x (12 : Fin (21 : ℕ)) || x (16 : Fin (21 : ℕ)) || x (17 : Fin (21 : ℕ)) || x (19 : Fin (21 : ℕ)))) || (x (3 : Fin (21 : ℕ)) && (x (11 : Fin (21 : ℕ)) || x (15 : Fin (21 : ℕ)) || x (16 : Fin (21 : ℕ)) || x (18 : Fin (21 : ℕ)))) || (x (4 : Fin (21 : ℕ)) && (x (10 : Fin (21 : ℕ)) || x (14 : Fin (21 : ℕ)) || x (15 : Fin (21 : ℕ)) || x (17 : Fin (21 : ℕ)))) || (x (5 : Fin (21 : ℕ)) && (x (9 : Fin (21 : ℕ)) || x (13 : Fin (21 : ℕ)) || x (14 : Fin (21 : ℕ)) || x (16 : Fin (21 : ℕ)))) || (x (6 : Fin (21 : ℕ)) && (x (11 : Fin (21 : ℕ)) || x (12 : Fin (21 : ℕ)) || x (14 : Fin (21 : ℕ)) || x (20 : Fin (21 : ℕ)))) || (x (7 : Fin (21 : ℕ)) && (x (10 : Fin (21 : ℕ)) || x (11 : Fin (21 : ℕ)) || x (13 : Fin (21 : ℕ)) || x (19 : Fin (21 : ℕ)))) || (x (8 : Fin (21 : ℕ)) && (x (9 : Fin (21 : ℕ)) || x (10 : Fin (21 : ℕ)) || x (12 : Fin (21 : ℕ)) || x (18 : Fin (21 : ℕ))))))
    (hStarEquiv :
      ∀ (a b : Fin (13 : ℕ) → Bool) (x : Fin (21 : ℕ) → Bool),
        (∀ idx : Fin (21 : ℕ), x idx =
          if idx.val < (9 : ℕ) then a (Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD idx.val (0 : ℕ)))
          else b (Fin.ofNat (13 : ℕ) (idx.val - (8 : ℕ)))) →
        (((x (0 : Fin (21 : ℕ)) && (x (9 : Fin (21 : ℕ)) || x (15 : Fin (21 : ℕ)) || x (19 : Fin (21 : ℕ)) || x (20 : Fin (21 : ℕ)))) || (x (1 : Fin (21 : ℕ)) && (x (13 : Fin (21 : ℕ)) || x (17 : Fin (21 : ℕ)) || x (18 : Fin (21 : ℕ)) || x (20 : Fin (21 : ℕ)))) || (x (2 : Fin (21 : ℕ)) && (x (12 : Fin (21 : ℕ)) || x (16 : Fin (21 : ℕ)) || x (17 : Fin (21 : ℕ)) || x (19 : Fin (21 : ℕ)))) || (x (3 : Fin (21 : ℕ)) && (x (11 : Fin (21 : ℕ)) || x (15 : Fin (21 : ℕ)) || x (16 : Fin (21 : ℕ)) || x (18 : Fin (21 : ℕ)))) || (x (4 : Fin (21 : ℕ)) && (x (10 : Fin (21 : ℕ)) || x (14 : Fin (21 : ℕ)) || x (15 : Fin (21 : ℕ)) || x (17 : Fin (21 : ℕ)))) || (x (5 : Fin (21 : ℕ)) && (x (9 : Fin (21 : ℕ)) || x (13 : Fin (21 : ℕ)) || x (14 : Fin (21 : ℕ)) || x (16 : Fin (21 : ℕ)))) || (x (6 : Fin (21 : ℕ)) && (x (11 : Fin (21 : ℕ)) || x (12 : Fin (21 : ℕ)) || x (14 : Fin (21 : ℕ)) || x (20 : Fin (21 : ℕ)))) || (x (7 : Fin (21 : ℕ)) && (x (10 : Fin (21 : ℕ)) || x (11 : Fin (21 : ℕ)) || x (13 : Fin (21 : ℕ)) || x (19 : Fin (21 : ℕ)))) || (x (8 : Fin (21 : ℕ)) && (x (9 : Fin (21 : ℕ)) || x (10 : Fin (21 : ℕ)) || x (12 : Fin (21 : ℕ)) || x (18 : Fin (21 : ℕ))))) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            (p.val ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (p.val + l.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ∧
            a p = Bool.true ∧ b l = Bool.true)) :
    (have x1 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))]; have x2 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (↑x3 ∉ x2 ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ x2); have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) => List.map (fun (x6 : Fin (26 : ℕ)) => if ↑x6 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x6 ∈ x4) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x6 ∈ x5)) x1; ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (43 : ℕ) ∧ x5.output < (21 : ℕ) + x5.size ∧ (∀ (x6 x7 : Fin (13 : ℕ)), x3 x6 x7 = Bool.true → x5.eval (x4 {x6} {x7}) = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x5.eval (x4 x6 {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, x3 x8 x7 = Bool.false}) = Bool.false) := by
  intro x1 x2 x3 x4
  have hIdx : ∀ idx : Fin (21 : ℕ),
      (have k : Fin (26 : ℕ) := x1.getD idx.val (0 : Fin (26 : ℕ));
        (k.val < (13 : ℕ) ↔ idx.val < (9 : ℕ)) ∧
        (idx.val < (9 : ℕ) → Fin.ofNat (13 : ℕ) k.val = Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD idx.val (0 : ℕ))) ∧
        (¬idx.val < (9 : ℕ) → Fin.ofNat (13 : ℕ) k.val = Fin.ofNat (13 : ℕ) (idx.val - (8 : ℕ)))) := by
    decide
  obtain ⟨C, hM, hSz, hOut, hEv⟩ := hStarCircuit
  refine ⟨C, hM, hSz, hOut, ?_, ?_⟩
  · intro p l hpl
    let a : Fin (13 : ℕ) → Bool := fun u => Decidable.decide (u ∈ ({p} : Finset (Fin (13 : ℕ))))
    let b : Fin (13 : ℕ) → Bool := fun v => Decidable.decide (v ∈ ({l} : Finset (Fin (13 : ℕ))))
    let xVec : Fin (21 : ℕ) → Bool := fun idx =>
      have k : Fin (26 : ℕ) := x1.getD idx.val (0 : Fin (26 : ℕ));
      if k.val < (13 : ℕ) then a (Fin.ofNat (13 : ℕ) k.val) else b (Fin.ofNat (13 : ℕ) k.val)
    have hMap : x4 {p} {l} = List.ofFn xVec := rfl
    have hxEq : ∀ idx : Fin (21 : ℕ), xVec idx =
        if idx.val < (9 : ℕ) then a (Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD idx.val (0 : ℕ)))
        else b (Fin.ofNat (13 : ℕ) (idx.val - (8 : ℕ))) := by
      intro idx
      by_cases h : idx.val < (9 : ℕ)
      · change (if (x1.getD idx.val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then a _ else b _) = _
        rw [if_pos ((hIdx idx).1.mpr h), if_pos h, (hIdx idx).2.1 h]
      · change (if (x1.getD idx.val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then a _ else b _) = _
        rw [if_neg (fun hk => h ((hIdx idx).1.mp hk)), if_neg h, (hIdx idx).2.2 h]
    rw [hMap]
    exact (hEv xVec).trans ((hStarEquiv a b xVec hxEq).mpr
      ⟨p, l, of_decide_eq_true hpl, decide_eq_true (Finset.mem_singleton_self p), decide_eq_true (Finset.mem_singleton_self l)⟩)
  · intro S
    let T : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | ∀ x8 ∈ S, x3 x8 x7 = Bool.false}
    let a : Fin (13 : ℕ) → Bool := fun u => Decidable.decide (u ∈ S)
    let b : Fin (13 : ℕ) → Bool := fun v => Decidable.decide (v ∈ T)
    let xVec : Fin (21 : ℕ) → Bool := fun idx =>
      have k : Fin (26 : ℕ) := x1.getD idx.val (0 : Fin (26 : ℕ));
      if k.val < (13 : ℕ) then a (Fin.ofNat (13 : ℕ) k.val) else b (Fin.ofNat (13 : ℕ) k.val)
    have hMap : x4 S T = List.ofFn xVec := rfl
    have hxEq : ∀ idx : Fin (21 : ℕ), xVec idx =
        if idx.val < (9 : ℕ) then a (Fin.ofNat (13 : ℕ) ([(2 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ)].getD idx.val (0 : ℕ)))
        else b (Fin.ofNat (13 : ℕ) (idx.val - (8 : ℕ))) := by
      intro idx
      by_cases h : idx.val < (9 : ℕ)
      · change (if (x1.getD idx.val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then a _ else b _) = _
        rw [if_pos ((hIdx idx).1.mpr h), if_pos h, (hIdx idx).2.1 h]
      · change (if (x1.getD idx.val (0 : Fin (26 : ℕ))).val < (13 : ℕ) then a _ else b _) = _
        rw [if_neg (fun hk => h ((hIdx idx).1.mp hk)), if_neg h, (hIdx idx).2.2 h]
    rw [hMap]
    refine Bool.eq_false_iff.mpr (fun ht => ?_)
    obtain ⟨p, l, hpl, hp, hl⟩ := (hStarEquiv a b xVec hxEq).mp ((hEv xVec).symm.trans ht)
    have hFalse := (Finset.mem_filter.mp (of_decide_eq_true hl)).2 p (of_decide_eq_true hp)
    exact Bool.noConfusion ((decide_eq_true hpl).symm.trans hFalse)
