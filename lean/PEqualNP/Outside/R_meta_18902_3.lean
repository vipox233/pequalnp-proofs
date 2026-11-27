import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18902_3
    (hAppendInit :
      ∀ (inp : Fin (14 : ℕ) → BitVec (58 : ℕ)) (g : Fin (25 : ℕ) → BitVec (58 : ℕ)) (x2 : Fin (14 : ℕ)),
        Fin.append inp g (Fin.ofNat (39 : ℕ) ↑x2) = inp x2)
    (hSplitWitness :
      ∃ (inp : Fin (14 : ℕ) → BitVec (58 : ℕ)) (g : Fin (25 : ℕ) → BitVec (58 : ℕ)),
        (∀ (x2 : Fin (14 : ℕ)), (inp x2).toNat = [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)].getD ↑x2 (0 : ℕ)) ∧
        (∀ (x2 : Fin (25 : ℕ)), ∃ (x3 : Fin ((14 : ℕ) + ↑x2)) (x4 : Fin ((14 : ℕ) + ↑x2)), Fin.append inp g (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = Fin.append inp g (Fin.ofNat (39 : ℕ) ↑x3) ||| Fin.append inp g (Fin.ofNat (39 : ℕ) ↑x4) ∨ Fin.append inp g (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = Fin.append inp g (Fin.ofNat (39 : ℕ) ↑x3) &&& Fin.append inp g (Fin.ofNat (39 : ℕ) ↑x4)) ∧
        ∃ (x2 : Fin (39 : ℕ)) (x3 : Fin (39 : ℕ)), Fin.append inp g x2 ||| Fin.append inp g x3 = (2097151 : BitVec (58 : ℕ)) ∨ Fin.append inp g x2 &&& Fin.append inp g x3 = (2097151 : BitVec (58 : ℕ))) :
    (∃ (x1 : Fin (39 : ℕ) → BitVec (58 : ℕ)), (∀ (x2 : Fin (14 : ℕ)), (x1 (Fin.ofNat (39 : ℕ) ↑x2)).toNat = [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)].getD ↑x2 (0 : ℕ)) ∧ (∀ (x2 : Fin (25 : ℕ)), ∃ (x3 : Fin ((14 : ℕ) + ↑x2)) (x4 : Fin ((14 : ℕ) + ↑x2)), x1 (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = x1 (Fin.ofNat (39 : ℕ) ↑x3) ||| x1 (Fin.ofNat (39 : ℕ) ↑x4) ∨ x1 (Fin.ofNat (39 : ℕ) ((14 : ℕ) + ↑x2)) = x1 (Fin.ofNat (39 : ℕ) ↑x3) &&& x1 (Fin.ofNat (39 : ℕ) ↑x4)) ∧ ∃ (x2 : Fin (39 : ℕ)) (x3 : Fin (39 : ℕ)), x1 x2 ||| x1 x3 = (2097151 : BitVec (58 : ℕ)) ∨ x1 x2 &&& x1 x3 = (2097151 : BitVec (58 : ℕ))) :=
  Exists.elim hSplitWitness fun inp h1 =>
    Exists.elim h1 fun g hg =>
      Exists.intro (Fin.append inp g)
        (And.intro
          (fun x2 => Eq.trans (congrArg BitVec.toNat (hAppendInit inp g x2)) (hg.1 x2))
          hg.2)
