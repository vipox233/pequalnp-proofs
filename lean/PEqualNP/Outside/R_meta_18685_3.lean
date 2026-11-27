import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18685_3
    (hToCircuit :
      ∀ (x1 : ℕ → ℕ) (x2 x3 : Fin (21 : ℕ)) (x6 : Fin (32 : ℕ)),
        (∀ (x4 : Fin (11 : ℕ)), x1 ↑x4 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x4 (0 : ℕ)) →
        (∀ (x5 : Fin (21 : ℕ)), ∃ (x7 : Fin ((11 : ℕ) + ↑x5)) (x8 : Fin ((11 : ℕ) + ↑x5)),
          x1 ((11 : ℕ) + ↑x5) = x1 ↑x7 ||| x1 ↑x8 ∨
          x1 ((11 : ℕ) + ↑x5) = x1 ↑x7 &&& x1 ↑x8 ∧
            (x5 = x2 ∨ x5 = x3 ∨ ∀ (x9 : Fin (24 : ℕ)), (x1 ((11 : ℕ) + ↑x5)).testBit ((16 : ℕ) + ↑x9) = Bool.false)) →
        x1 ↑x6 = (65535 : ℕ) →
        have g11 : (Fin (11 : ℕ) → Bool) → Bool := fun (f : Fin (11 : ℕ) → Bool) =>
          [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
           (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any
            fun (e : ℕ) => f (Fin.ofNat (11 : ℕ) (e / (11 : ℕ))) && f (Fin.ofNat (11 : ℕ) (e % (11 : ℕ)));
        ∃ (c : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : Fin c.size),
          PEqualNP.TopForm.IsAO2 (11 : ℕ) c ∧ c.size ≤ (21 : ℕ) ∧
          (∀ (f : Fin (11 : ℕ) → Bool), c.eval (List.ofFn f) = g11 f) ∧
          ∀ (g : Fin c.size), g ≠ g1 → g ≠ g2 →
            (PEqualNP.MetaComplexity.NestedCover.gateAt c ↑g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ (f : Fin (11 : ℕ) → Bool), g11 f = Bool.false →
              PEqualNP.EdgeOwnership.gateVal (11 : ℕ) c ↑g f = Bool.false)
    (hNoTwoDirty :
      have g11 : (Fin (11 : ℕ) → Bool) → Bool := fun (f : Fin (11 : ℕ) → Bool) =>
        [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
         (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any
          fun (e : ℕ) => f (Fin.ofNat (11 : ℕ) (e / (11 : ℕ))) && f (Fin.ofNat (11 : ℕ) (e % (11 : ℕ)));
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : Fin c.size),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) c → c.size ≤ (21 : ℕ) →
        (∀ (f : Fin (11 : ℕ) → Bool), c.eval (List.ofFn f) = g11 f) →
        (∀ (g : Fin c.size), g ≠ g1 → g ≠ g2 →
          (PEqualNP.MetaComplexity.NestedCover.gateAt c ↑g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ (f : Fin (11 : ℕ) → Bool), g11 f = Bool.false →
            PEqualNP.EdgeOwnership.gateVal (11 : ℕ) c ↑g f = Bool.false) →
        False) :
    (∀ (x1 : ℕ → ℕ) (x2 x3 : Fin (21 : ℕ)), (∀ (x4 : Fin (11 : ℕ)), x1 ↑x4 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x4 (0 : ℕ)) → (∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin ((11 : ℕ) + ↑x5)) (x7 : Fin ((11 : ℕ) + ↑x5)), x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 ||| x1 ↑x7 ∨ x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 &&& x1 ↑x7 ∧ (x5 = x2 ∨ x5 = x3 ∨ ∀ (x8 : Fin (24 : ℕ)), (x1 ((11 : ℕ) + ↑x5)).testBit ((16 : ℕ) + ↑x8) = Bool.false)) → ∀ (x6 : Fin (32 : ℕ)), x1 ↑x6 ≠ (65535 : ℕ)) :=
  fun x1 x2 x3 hInit hSteps x6 hEq =>
    (hToCircuit x1 x2 x3 x6 hInit hSteps hEq).elim fun c hc =>
      hc.elim fun g1 hg1 =>
        hg1.elim fun g2 hg2 =>
          hNoTwoDirty c g1 g2 hg2.1 hg2.2.1 hg2.2.2.1 hg2.2.2.2
