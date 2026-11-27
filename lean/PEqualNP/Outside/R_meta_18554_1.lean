import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18554_1
    (hCompileOps :
      ∀ (W : List ℕ) (ops : List (Bool × ℕ × ℕ)) (out : ℕ),
        (∀ (k : Fin ops.length), (ops.get k).2.1 < W.length + ↑k ∧ (ops.get k).2.2 < W.length + ↑k) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          C.size = ops.length ∧
          PEqualNP.TopForm.IsAO2 W.length C ∧
          (List.foldl (fun (a : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) => have v0 : ℕ := a.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ); have v1 : ℕ := a.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ); a ++ [if g.op.eval [Bool.false, Bool.true] = Bool.true then v0 ||| v1 else v0 &&& v1]) W C.gates).getD C.output (0 : ℕ) =
            (List.foldl (fun (a : List ℕ) (op : Bool × ℕ × ℕ) => have v0 : ℕ := a.getD op.2.1 (0 : ℕ); have v1 : ℕ := a.getD op.2.2 (0 : ℕ); a ++ [if op.1 = Bool.true then v0 ||| v1 else v0 &&& v1]) W ops).getD out (0 : ℕ))
    (hOpsWitness :
      ∃ (ops : List (Bool × ℕ × ℕ)) (out : ℕ),
        ops.length ≤ (26 : ℕ) ∧
        (∀ (k : Fin ops.length), (ops.get k).2.1 < (14 : ℕ) + ↑k ∧ (ops.get k).2.2 < (14 : ℕ) + ↑k) ∧
        (List.foldl (fun (a : List ℕ) (op : Bool × ℕ × ℕ) => have v0 : ℕ := a.getD op.2.1 (0 : ℕ); have v1 : ℕ := a.getD op.2.2 (0 : ℕ); a ++ [if op.1 = Bool.true then v0 ||| v1 else v0 &&& v1]) [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)] ops).getD out (0 : ℕ) = (2097151 : ℕ)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (26 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (List.foldl               (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>                 have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                 have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                 x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5])               [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)] x1.gates).getD           x1.output (0 : ℕ) =         (2097151 : ℕ)) :=
  Exists.elim hOpsWitness fun ops h1 =>
    Exists.elim h1 fun out hP =>
      Exists.elim (hCompileOps [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)] ops out hP.2.1) fun C hC =>
        ⟨C, hC.1 ▸ hP.1, hC.2.1, hC.2.2.trans hP.2.2⟩
