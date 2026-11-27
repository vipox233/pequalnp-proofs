import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18554_2
    (hAppendStar :
      ∀ (W : List ℕ) (a b c d : Fin (14 : ℕ)) (target : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        W.length = (14 : ℕ) →
        C.size ≤ (22 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
        C.output < (14 : ℕ) + C.size →
        (List.foldl
          (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
            have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
            have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
            x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5])
          W C.gates).getD C.output (0 : ℕ) = target →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit),
          C'.size ≤ (26 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (14 : ℕ) C' ∧
          (List.foldl
            (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
              have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
              have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
              x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5])
            W C'.gates).getD C'.output (0 : ℕ) =
            target ||| (((W.getD ↑a (0 : ℕ) ||| W.getD ↑b (0 : ℕ)) ||| W.getD ↑c (0 : ℕ)) &&& W.getD ↑d (0 : ℕ)))
    (hResidual22 :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (22 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
        x1.output < (14 : ℕ) + x1.size ∧
        (List.foldl
          (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
            have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
            have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
            x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5])
          [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)] x1.gates).getD x1.output (0 : ℕ) = (262143 : ℕ)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (26 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (List.foldl               (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>                 have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                 have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                 x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5])               [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)] x1.gates).getD           x1.output (0 : ℕ) =         (2097151 : ℕ)) :=
  Exists.elim hResidual22 fun C hC =>
    Exists.elim
      (hAppendStar
        [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)]
        (0 : Fin (14 : ℕ)) (2 : Fin (14 : ℕ)) (6 : Fin (14 : ℕ)) (13 : Fin (14 : ℕ)) (262143 : ℕ) C
        rfl hC.1 hC.2.1 hC.2.2.1 hC.2.2.2)
      fun C' hC' =>
        Exists.intro C' (And.intro hC'.1 (And.intro hC'.2.1 (Eq.trans hC'.2.2 rfl)))
