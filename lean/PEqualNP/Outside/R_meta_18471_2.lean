import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18471_2
    (hElimDup : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (26 : ℕ) C → (¬∀ g ∈ C.gates, g.inputs.Nodup) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        D.size < C.size ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) D ∧
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) D = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C)
    (hNodupFalseInput :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun a b => a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ));
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ C.size ≤ (63 : ℕ) ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ a b : Fin (13 : ℕ), x1 a b → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C fun i : Fin (26 : ℕ) => Decidable.decide (i = Fin.castAdd (13 : ℕ) a ∨ i = Fin.natAdd (13 : ℕ) b)) = Bool.true) →
        ∃ (A B : Finset (Fin (13 : ℕ))),
          (∀ a ∈ A, ∀ b ∈ B, ¬x1 a b) ∧
          (∀ b : Fin (13 : ℕ), {a ∈ A | x1 a b}.card ≤ (2 : ℕ)) ∧
          (∀ a : Fin (13 : ℕ), {b ∈ B | x1 a b}.card ≤ (2 : ℕ)) ∧
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C (Fin.append (fun i => Decidable.decide (i ∈ A)) fun j => Decidable.decide (j ∈ B)) = Bool.true) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 (Fin.append (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7)) = Bool.true) := by
  intro x1 C
  exact @Nat.strongRecOn (fun n => ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = n →
      PEqualNP.TopForm.IsAO2 (26 : ℕ) D → D.size ≤ (63 : ℕ) →
      (∀ a b : Fin (13 : ℕ), x1 a b → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) D fun i => Decidable.decide (i = Fin.castAdd (13 : ℕ) a ∨ i = Fin.natAdd (13 : ℕ) b)) = Bool.true) →
      ∃ (A B : Finset (Fin (13 : ℕ))),
        (∀ a ∈ A, ∀ b ∈ B, ¬x1 a b) ∧ (∀ b : Fin (13 : ℕ), {a ∈ A | x1 a b}.card ≤ (2 : ℕ)) ∧
        (∀ a : Fin (13 : ℕ), {b ∈ B | x1 a b}.card ≤ (2 : ℕ)) ∧
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) D (Fin.append (fun i => Decidable.decide (i ∈ A)) fun j => Decidable.decide (j ∈ B)) = Bool.true)
    C.size (fun n ih D hn hAO hSz hInc =>
      Or.elim (Classical.em (∀ g ∈ D.gates, g.inputs.Nodup))
        (fun hnd => hNodupFalseInput D ⟨hAO, hSz, hnd, hInc⟩)
        (fun hdup => Exists.elim (hElimDup D hAO hdup) fun E hE =>
          hE.2.2 ▸ ih E.size (hn ▸ hE.1) E rfl hE.2.1 (Nat.le_trans (Nat.le_of_lt hE.1) hSz) (hE.2.2.symm ▸ hInc))) C rfl
