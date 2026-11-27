import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18922_2
    (hDiffEquiv :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      ∀ (p l : Fin (13 : ℕ)),
        ↑(p - l) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔
          ∃ d ∈ x1, p = l + d)
    (hCircuitDiff :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ↑(x2 - x3) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4;
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x4 ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 ∧
        x4.size ≤ (32 : ℕ) ∧
        x4.output < (27 : ℕ) + x4.size ∧
        (∀ (x5 x6 : Fin (13 : ℕ)), ↑x6 < (7 : ℕ) → x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x5 ∨ x9 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧
        ∀ (x5 : Finset (Fin (13 : ℕ))),
          (¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) →
          (¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), (∀ x9 ∈ x5, ¬x2 x9 x8) → x2 x7 x8) →
          PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x5)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (Disjoint x5 (Finset.image (fun (x10 : Fin (13 : ℕ)) => x9 + x10) x1))) x8) = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 ∧ x4.size ≤ (32 : ℕ) ∧ x4.output < (27 : ℕ) + x4.size ∧ (∀ (x5 x6 : Fin (13 : ℕ)), ↑x6 < (7 : ℕ) → x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x5 ∨ x9 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) → (¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), (∀ x9 ∈ x5, ¬x2 x9 x8) → x2 x7 x8) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x5)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (Disjoint x5 (Finset.image (fun (x10 : Fin (13 : ℕ)) => x9 + x10) x1))) x8) = Bool.false) :=
  Exists.elim hCircuitDiff fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1,
      fun p l hl hpl => hC.2.2.2.2.1 p l hl ((hDiffEquiv p l).mpr hpl),
      fun S h1 h2 =>
        hC.2.2.2.2.2 S
          (fun h => Exists.elim h fun l hl => h1 ⟨l, fun p hp => (hDiffEquiv p l).mp (hl p hp)⟩)
          (fun h => Exists.elim h fun p hp => h2 ⟨p, fun l hl => (hDiffEquiv p l).mp (hp l (fun q hq hql => hl q hq ((hDiffEquiv q l).mp hql)))⟩)⟩
