import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18974_2
    (hCircuitSplit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 ∧
        x1.size ≤ (63 : ℕ) ∧
        ∀ x2 ∈ [(67117057 : ℕ), (67239937 : ℕ), (67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)],
          ∀ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],
            ∀ (x6 : Fin (13 : ℕ)),
              have x8 : Fin (13 : ℕ) → Bool := fun (x8 : Fin (13 : ℕ)) => x2.testBit ↑(x4 * x8 + x6);
              have x9 : Fin (13 : ℕ) → Bool := fun (x9 : Fin (13 : ℕ)) => x2.testBit (↑(x4 * x9 + x6) + (13 : ℕ));
              PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (Fin.append x8 x9) = x2.testBit (26 : ℕ) ∧
              PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (Fin.append (fun (x10 : Fin (13 : ℕ)) => x9 (-x10)) (fun (x10 : Fin (13 : ℕ)) => x8 (-x10))) = x2.testBit (26 : ℕ))
    (hBoolBranch :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : Fin (13 : ℕ) → Bool) (r : Bool),
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (Fin.append x8 x9) = r →
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (Fin.append (fun (x10 : Fin (13 : ℕ)) => x9 (-x10)) (fun (x10 : Fin (13 : ℕ)) => x8 (-x10))) = r →
        ∀ (x7 : Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (if x7 = Bool.true then Fin.append (fun (x10 : Fin (13 : ℕ)) => x9 (-x10)) (fun (x10 : Fin (13 : ℕ)) => x8 (-x10)) else Fin.append x8 x9) = r) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       ∀ x2 ∈ [(67117057 : ℕ), (67239937 : ℕ), (67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)],         ∀ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],           ∀ (x6 : Fin (13 : ℕ)) (x7 : Bool),             have x8 : Fin (13 : ℕ) → Bool := fun (x8 : Fin (13 : ℕ)) => x2.testBit ↑(x4 * x8 + x6);             have x9 : Fin (13 : ℕ) → Bool := fun (x9 : Fin (13 : ℕ)) => x2.testBit (↑(x4 * x9 + x6) + (13 : ℕ));             PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (if x7 = Bool.true then Fin.append (fun (x10 : Fin (13 : ℕ)) => x9 (-x10)) fun (x10 : Fin (13 : ℕ)) => x8 (-x10) else Fin.append x8 x9) = x2.testBit (26 : ℕ)) :=
  Exists.elim hCircuitSplit fun C hC =>
    ⟨C, hC.1, hC.2.1, fun x2 hx2 x4 hx4 x6 x7 =>
      hBoolBranch C _ _ (x2.testBit (26 : ℕ)) (hC.2.2 x2 hx2 x4 hx4 x6).1 (hC.2.2 x2 hx2 x4 hx4 x6).2 x7⟩
