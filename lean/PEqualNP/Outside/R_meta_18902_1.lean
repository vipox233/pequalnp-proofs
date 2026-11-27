import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18902_1
    (hCompile :
      have baseNat : List ℕ := [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)];
      have run : List (Bool × ℕ × ℕ) → List (BitVec (58 : ℕ)) := fun ops =>
        List.foldl (fun (acc : List (BitVec (58 : ℕ))) (g : Bool × ℕ × ℕ) =>
          acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : BitVec (58 : ℕ)) &&& acc.getD g.2.2 (0 : BitVec (58 : ℕ)) else acc.getD g.2.1 (0 : BitVec (58 : ℕ)) ||| acc.getD g.2.2 (0 : BitVec (58 : ℕ))])
          (baseNat.map (BitVec.ofNat (58 : ℕ))) ops;
      ∀ (ops : List (Bool × ℕ × ℕ)),
        ops.length = (25 : ℕ) →
        (∀ (i : Fin (25 : ℕ)), (ops.getD ↑i (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (14 : ℕ) + ↑i ∧ (ops.getD ↑i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑i) →
        have w : Fin (39 : ℕ) → BitVec (58 : ℕ) := fun k => (run ops).getD ↑k (0 : BitVec (58 : ℕ));
        (∀ (x2 : Fin (14 : ℕ)), (w (Fin.ofNat (39 : ℕ) ↑x2)).toNat = baseNat.getD ↑x2 (0 : ℕ)) ∧
        ∀ (x2 : Fin (25 : ℕ)), ∃ (x3 : Fin ((14 : ℕ) + ↑x2)) (x4 : Fin ((14 : ℕ) + ↑x2)),
          w (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = w (Fin.ofNat (39 : ℕ) ↑x3) ||| w (Fin.ofNat (39 : ℕ) ↑x4) ∨
          w (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = w (Fin.ofNat (39 : ℕ) ↑x3) &&& w (Fin.ofNat (39 : ℕ) ↑x4))
    (hWitness :
      have baseNat : List ℕ := [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)];
      have run : List (Bool × ℕ × ℕ) → List (BitVec (58 : ℕ)) := fun ops =>
        List.foldl (fun (acc : List (BitVec (58 : ℕ))) (g : Bool × ℕ × ℕ) =>
          acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : BitVec (58 : ℕ)) &&& acc.getD g.2.2 (0 : BitVec (58 : ℕ)) else acc.getD g.2.1 (0 : BitVec (58 : ℕ)) ||| acc.getD g.2.2 (0 : BitVec (58 : ℕ))])
          (baseNat.map (BitVec.ofNat (58 : ℕ))) ops;
      ∃ (ops : List (Bool × ℕ × ℕ)) (a : Fin (39 : ℕ)) (b : Fin (39 : ℕ)),
        ops.length = (25 : ℕ) ∧
        (∀ (i : Fin (25 : ℕ)), (ops.getD ↑i (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (14 : ℕ) + ↑i ∧ (ops.getD ↑i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑i) ∧
        have r : List (BitVec (58 : ℕ)) := run ops;
        r.getD ↑a (0 : BitVec (58 : ℕ)) ||| r.getD ↑b (0 : BitVec (58 : ℕ)) = (2097151 : BitVec (58 : ℕ)) ∨
        r.getD ↑a (0 : BitVec (58 : ℕ)) &&& r.getD ↑b (0 : BitVec (58 : ℕ)) = (2097151 : BitVec (58 : ℕ))) :
    (∃ (x1 : Fin (39 : ℕ) → BitVec (58 : ℕ)), (∀ (x2 : Fin (14 : ℕ)), (x1 (Fin.ofNat (39 : ℕ) ↑x2)).toNat = [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)].getD ↑x2 (0 : ℕ)) ∧ (∀ (x2 : Fin (25 : ℕ)), ∃ (x3 : Fin ((14 : ℕ) + ↑x2)) (x4 : Fin ((14 : ℕ) + ↑x2)), x1 (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = x1 (Fin.ofNat (39 : ℕ) ↑x3) ||| x1 (Fin.ofNat (39 : ℕ) ↑x4) ∨ x1 (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = x1 (Fin.ofNat (39 : ℕ) ↑x3) &&& x1 (Fin.ofNat (39 : ℕ) ↑x4)) ∧ ∃ (x2 : Fin (39 : ℕ)) (x3 : Fin (39 : ℕ)), x1 x2 ||| x1 x3 = (2097151 : BitVec (58 : ℕ)) ∨ x1 x2 &&& x1 x3 = (2097151 : BitVec (58 : ℕ))) :=
  Exists.elim hWitness fun ops h1 =>
    Exists.elim h1 fun a h2 =>
      Exists.elim h2 fun b h =>
        have hc := hCompile ops h.1 h.2.1
        ⟨fun k => (List.foldl (fun (acc : List (BitVec (58 : ℕ))) (g : Bool × ℕ × ℕ) =>
            acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : BitVec (58 : ℕ)) &&& acc.getD g.2.2 (0 : BitVec (58 : ℕ)) else acc.getD g.2.1 (0 : BitVec (58 : ℕ)) ||| acc.getD g.2.2 (0 : BitVec (58 : ℕ))])
            ([(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)].map (BitVec.ofNat (58 : ℕ))) ops).getD ↑k (0 : BitVec (58 : ℕ)),
          hc.1, hc.2, a, b, h.2.2⟩
