import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18211_2
    (hPrependOrGate :
      ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (c : PEqualNP.CircuitLowerBounds.Circuit),
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        g.inputs.length ≤ (2 : ℕ) →
        PEqualNP.MetaComplexity.Monotone2 c →
        ∃ (c' : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 c' ∧
          c'.size = c.size + (1 : ℕ) ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt c' (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ (xs : List Bool),
            c'.eval xs = c.eval (xs ++ [g.op.eval (List.map (fun (k : ℕ) => xs.getD k Bool.false) g.inputs)]))
    (hNoMonotone63 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ));
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool :=
        fun (x2 x3 : Finset (Fin (13 : ℕ))) =>
          Fin.append (fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
      ∀ (c' : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.MetaComplexity.Monotone2 c' ∧
         c'.size ≤ (63 : ℕ) ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt c' (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
         (∀ (p l : Fin (13 : ℕ)), x1 p l →
           c'.eval (List.ofFn fun (i : Fin (26 : ℕ)) => Decidable.decide (i = Fin.castAdd (13 : ℕ) p ∨ i = Fin.natAdd (13 : ℕ) l)) = Bool.true) ∧
         (∀ (A B : Finset (Fin (13 : ℕ))), A.card = (4 : ℕ) →
           (∀ (l : Fin (13 : ℕ)), {p ∈ A | x1 p l}.card ≤ (2 : ℕ)) →
           (∀ (l : Fin (13 : ℕ)), l ∈ B ↔ ∀ p ∈ A, ¬x1 p l) →
           c'.eval (List.ofFn (x2 A B)) = Bool.false) ∧
         (∀ (A B : Finset (Fin (13 : ℕ))), B.card = (4 : ℕ) →
           (∀ (p : Fin (13 : ℕ)), {l ∈ B | x1 p l}.card ≤ (2 : ℕ)) →
           (∀ (p : Fin (13 : ℕ)), p ∈ A ↔ ∀ l ∈ B, ¬x1 p l) →
           c'.eval (List.ofFn (x2 A B)) = Bool.false)) →
        False) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Gate → (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : Fin (26 : ℕ) → Bool) =>   have x5 : List Bool := List.ofFn x4;   x5 ++ [x3.op.eval (List.map (fun (x6 : ℕ) => x5.getD x6 Bool.false) x3.inputs)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4.inputs.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ (62 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x5.eval (x3 x4 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x1 x14 x13}.card ≤ (2 : ℕ)) → x5.eval (x3 x4 (x2 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, ¬x1 x15 x14})) = Bool.false) → (∀ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) → (∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x12 | x1 x14 x15}.card ≤ (2 : ℕ)) → x5.eval (x3 x4 (x2 {x15 : Fin (13 : ℕ) | ∀ x16 ∈ x12, ¬x1 x15 x16} x12)) = Bool.false) → False) := by
  intro x1 x2 x3 x4 x5 hOp hLen hM hSz hPos hOvP hOvL
  exact Exists.elim (hPrependOrGate x4 x5 hOp hLen hM) fun c' hc' =>
    hNoMonotone63 c'
      ⟨hc'.1,
       Eq.subst (motive := fun k => k ≤ (63 : ℕ)) hc'.2.1.symm (Nat.add_le_add_right hSz (1 : ℕ)),
       hc'.2.2.1,
       (fun p l hpl => Eq.trans (hc'.2.2.2 _) (hPos p l hpl)),
       (fun A B hA hSec hB =>
         have hBeq : B = Finset.univ.filter (fun (l : Fin (13 : ℕ)) => ∀ p ∈ A, ¬x1 p l) :=
           Finset.ext fun l => Iff.trans (hB l)
             (Iff.intro (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)
               (fun h => (Finset.mem_filter.mp h).2))
         Eq.subst (motive := fun S => c'.eval (List.ofFn (x2 A S)) = Bool.false) hBeq.symm
           (Eq.trans (hc'.2.2.2 _) (hOvP A hA hSec))),
       (fun A B hB hSec hA =>
         have hAeq : A = Finset.univ.filter (fun (p : Fin (13 : ℕ)) => ∀ l ∈ B, ¬x1 p l) :=
           Finset.ext fun p => Iff.trans (hA p)
             (Iff.intro (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩)
               (fun h => (Finset.mem_filter.mp h).2))
         Eq.subst (motive := fun S => c'.eval (List.ofFn (x2 S B)) = Bool.false) hAeq.symm
           (Eq.trans (hc'.2.2.2 _) (hOvL B hB hSec)))⟩
