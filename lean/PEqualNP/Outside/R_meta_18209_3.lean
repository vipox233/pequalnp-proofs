import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18209_3
    (hNormalize :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ));
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ (63 : ℕ) →
        (∀ (a b : Fin (13 : ℕ)), x1 a b → C.eval (List.ofFn fun (k : Fin (26 : ℕ)) => Decidable.decide (k = Fin.castAdd (13 : ℕ) a ∨ k = Fin.natAdd (13 : ℕ) b)) = Bool.true) →
        (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) → (∀ (l : Fin (13 : ℕ)), {p ∈ Q | x1 p l}.card ≤ (2 : ℕ)) → C.eval (List.ofFn (x2 Q {l : Fin (13 : ℕ) | ∀ p ∈ Q, ¬x1 p l})) = Bool.false) →
        (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) → (∀ (p : Fin (13 : ℕ)), {l ∈ Q | x1 p l}.card ≤ (2 : ℕ)) → C.eval (List.ofFn (x2 {p : Fin (13 : ℕ) | ∀ l ∈ Q, ¬x1 p l} Q)) = Bool.false) →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 D ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) D ∧
          D.size ≤ (63 : ℕ) ∧
          (∀ (a b : Fin (13 : ℕ)), x1 a b → D.eval (List.ofFn fun (k : Fin (26 : ℕ)) => Decidable.decide (k = Fin.castAdd (13 : ℕ) a ∨ k = Fin.natAdd (13 : ℕ) b)) = Bool.true) ∧
          (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) → (∀ (l : Fin (13 : ℕ)), {p ∈ Q | x1 p l}.card ≤ (2 : ℕ)) → D.eval (List.ofFn (x2 Q {l : Fin (13 : ℕ) | ∀ p ∈ Q, ¬x1 p l})) = Bool.false) ∧
          (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) → (∀ (p : Fin (13 : ℕ)), {l ∈ Q | x1 p l}.card ≤ (2 : ℕ)) → D.eval (List.ofFn (x2 {p : Fin (13 : ℕ) | ∀ l ∈ Q, ¬x1 p l} Q)) = Bool.false))
    (hNoReadsBack63 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ));
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) D →
        D.size ≤ (63 : ℕ) →
        (∀ (a b : Fin (13 : ℕ)), x1 a b → D.eval (List.ofFn fun (k : Fin (26 : ℕ)) => Decidable.decide (k = Fin.castAdd (13 : ℕ) a ∨ k = Fin.natAdd (13 : ℕ) b)) = Bool.true) →
        (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) → (∀ (l : Fin (13 : ℕ)), {p ∈ Q | x1 p l}.card ≤ (2 : ℕ)) → D.eval (List.ofFn (x2 Q {l : Fin (13 : ℕ) | ∀ p ∈ Q, ¬x1 p l})) = Bool.false) →
        (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) → (∀ (p : Fin (13 : ℕ)), {l ∈ Q | x1 p l}.card ≤ (2 : ℕ)) → D.eval (List.ofFn (x2 {p : Fin (13 : ℕ) | ∀ l ∈ Q, ¬x1 p l} Q)) = Bool.false) →
        False) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Gate → (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : Fin (26 : ℕ) → Bool) => have x5 : List Bool := List.ofFn x4; x5 ++ [x3.op.eval (List.map (fun (x6 : ℕ) => x5.getD x6 Bool.false) x3.inputs)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4.inputs.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ (62 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x5.eval (x3 x4 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x1 x14 x13}.card ≤ (2 : ℕ)) → x5.eval (x3 x4 (x2 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, ¬x1 x15 x14})) = Bool.false) → (∀ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) → (∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x12 | x1 x14 x15}.card ≤ (2 : ℕ)) → x5.eval (x3 x4 (x2 {x15 : Fin (13 : ℕ) | ∀ x16 ∈ x12, ¬x1 x15 x16} x12)) = Bool.false) → False) := by
  intro x1 x2 x3 g C hOp hIn hM hSz hPos hNegL hNegR
  let C' : PEqualNP.CircuitLowerBounds.Circuit := { gates := g :: C.gates, output := C.output }
  have hM' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro u hu
    simp only [C', List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨by simp [hOp], hIn⟩
    · exact hM u hu
  have hSz' : C'.size ≤ 63 := by
    show (g :: C.gates).length ≤ 63
    simp only [List.length_cons]
    exact Nat.succ_le_succ hSz
  have hEv : ∀ y : Fin 26 → Bool, C'.eval (List.ofFn y) = C.eval (x3 g y) := fun _ => rfl
  obtain ⟨D, hDM, hDRB, hDSz, hDPos, hDNegL, hDNegR⟩ :=
    hNormalize C' hM' hSz'
      (fun a b hab => (hEv _).trans (hPos a b hab))
      (fun Q hQ h2 => (hEv _).trans (hNegL Q hQ h2))
      (fun Q hQ h2 => (hEv _).trans (hNegR Q hQ h2))
  exact hNoReadsBack63 D hDM hDRB hDSz hDPos hDNegL hDNegR

