import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17885_1
    (hCompileProg :
      ∀ (x1 : List ℕ) (prog : List (Bool × ℕ × ℕ)),
        (∀ (i : ℕ), i < prog.length →
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (11 : ℕ) + i ∧
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (11 : ℕ) + i) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsAO2 (11 : ℕ) C ∧
          C.size = prog.length ∧
          PEqualNP.ReadTwo.nAnd C = (prog.filter (fun g => !g.1)).length ∧
          List.foldl
            (fun (acc : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
              have a : ℕ := acc.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
              have b : ℕ := acc.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
              acc ++ [if g.op.eval [Bool.false, Bool.true] = Bool.true then a ||| b else a &&& b])
            x1 C.gates =
          List.foldl
            (fun (acc : List ℕ) (g : Bool × ℕ × ℕ) =>
              acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ)
                      else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)])
            x1 prog)
    (hProgWitness :
      have x1 : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)];
      have step : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (acc : List ℕ) (g : Bool × ℕ × ℕ) =>
        acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ)
                else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)];
      have x5 : ℕ → Prop := fun (w : ℕ) => (∃ (i : Fin (16 : ℕ)), w.testBit ↑i = Bool.true) ∧ ∃ (j : Fin (24 : ℕ)), w.testBit ((16 : ℕ) + ↑j) = Bool.true;
      ∃ (prog : List (Bool × ℕ × ℕ)) (pairs : List (ℕ × ℕ)),
        (∀ (i : ℕ), i < prog.length →
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (11 : ℕ) + i ∧
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (11 : ℕ) + i) ∧
        pairs ≠ [] ∧
        prog.length + ((3 : ℕ) - (prog.filter (fun g => !g.1)).length) + (2 : ℕ) * pairs.length ≤ (22 : ℕ) ∧
        (∀ p ∈ pairs, p.1 < (11 : ℕ) + prog.length ∧ p.2 < (11 : ℕ) + prog.length) ∧
        (∀ (i : ℕ), i < prog.length → x5 ((List.foldl step x1 prog).getD ((11 : ℕ) + i) (0 : ℕ))) ∧
        List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ)
          (List.map (fun (p : ℕ × ℕ) => (List.foldl step x1 prog).getD p.1 (0 : ℕ) &&& (List.foldl step x1 prog).getD p.2 (0 : ℕ)) pairs) = (65535 : ℕ)) :
    (have x1 : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]; have x2 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>   have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);   have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);   x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (List.foldl x2 x1 x3.gates).getD x4 (0 : ℕ); have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ × ℕ → ℕ := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ × ℕ) => x3 x4 x5.1 &&& x3 x4 x5.2; have x5 : ℕ → Prop := fun (x5 : ℕ) => (∃ (x6 : Fin (16 : ℕ)), x5.testBit ↑x6 = Bool.true) ∧ ∃ (x6 : Fin (24 : ℕ)), x5.testBit ((16 : ℕ) + ↑x6) = Bool.true; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 ∧ x7 ≠ [] ∧ x6.size + ((3 : ℕ) - PEqualNP.ReadTwo.nAnd x6) + (2 : ℕ) * x7.length ≤ (22 : ℕ) ∧ (∀ x8 ∈ x7, x8.1 < (11 : ℕ) + x6.size ∧ x8.2 < (11 : ℕ) + x6.size) ∧ (∀ x8 < x6.size, x5 (x3 x6 ((11 : ℕ) + x8))) ∧ List.foldl (fun (x8 x9 : ℕ) => x8 ||| x9) (0 : ℕ) (List.map (x4 x6) x7) = (65535 : ℕ)) :=
  Exists.elim hProgWitness fun prog h1 =>
    Exists.elim h1 fun pairs h2 =>
      Exists.elim (hCompileProg [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] prog h2.1) fun C hC =>
        Exists.intro C
          (Exists.intro pairs
            (And.intro hC.1
              (And.intro h2.2.1
                (And.intro
                  (Eq.subst (motive := fun n => C.size + ((3 : ℕ) - n) + (2 : ℕ) * pairs.length ≤ (22 : ℕ)) hC.2.2.1.symm
                    (Eq.subst (motive := fun s => s + ((3 : ℕ) - (prog.filter (fun g => !g.1)).length) + (2 : ℕ) * pairs.length ≤ (22 : ℕ)) hC.2.1.symm h2.2.2.1))
                  (And.intro
                    (Eq.subst (motive := fun s => ∀ p ∈ pairs, p.1 < (11 : ℕ) + s ∧ p.2 < (11 : ℕ) + s) hC.2.1.symm h2.2.2.2.1)
                    (And.intro
                      (Eq.subst (motive := fun L => ∀ (i : ℕ), i < C.size → (∃ (x6 : Fin (16 : ℕ)), (L.getD ((11 : ℕ) + i) (0 : ℕ)).testBit ↑x6 = Bool.true) ∧ ∃ (x6 : Fin (24 : ℕ)), (L.getD ((11 : ℕ) + i) (0 : ℕ)).testBit ((16 : ℕ) + ↑x6) = Bool.true) hC.2.2.2.symm
                        (Eq.subst (motive := fun s => ∀ (i : ℕ), i < s → (∃ (x6 : Fin (16 : ℕ)), ((List.foldl (fun (acc : List ℕ) (g : Bool × ℕ × ℕ) => acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ) else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] prog).getD ((11 : ℕ) + i) (0 : ℕ)).testBit ↑x6 = Bool.true) ∧ ∃ (x6 : Fin (24 : ℕ)), ((List.foldl (fun (acc : List ℕ) (g : Bool × ℕ × ℕ) => acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ) else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] prog).getD ((11 : ℕ) + i) (0 : ℕ)).testBit ((16 : ℕ) + ↑x6) = Bool.true) hC.2.1.symm h2.2.2.2.2.1))
                      (Eq.subst (motive := fun L => List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ) (List.map (fun (p : ℕ × ℕ) => L.getD p.1 (0 : ℕ) &&& L.getD p.2 (0 : ℕ)) pairs) = (65535 : ℕ)) hC.2.2.2.symm h2.2.2.2.2.2)))))))
