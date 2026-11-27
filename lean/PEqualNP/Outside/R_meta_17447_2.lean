import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17447_2
    (hSpecEquiv :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ws : List ℕ),
        (∀ (x5 x6 : Finset (Fin (13 : ℕ))),
          PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : ℕ) =>
            (C.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) =>
              if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5)
              else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) ws) = Bool.true ↔
          ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        ∀ (x : Fin (26 : ℕ) → Bool),
          PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (w : ℕ) =>
            (C.wires (List.ofFn x)).getD w Bool.false) ws) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
            x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true)
    (hBoolAndLastLB :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ws : List ℕ),
        PEqualNP.MetaComplexity.Monotone2 C →
        ws.length ≤ (2 : ℕ) →
        (∀ (x : Fin (26 : ℕ) → Bool),
          PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (w : ℕ) =>
            (C.wires (List.ofFn x)).getD w Bool.false) ws) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
            x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (63 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size :=
  fun x1 x2 hM hL hS hLast => hBoolAndLastLB x1 x2 hM hL (hSpecEquiv x1 x2 hS) hLast
