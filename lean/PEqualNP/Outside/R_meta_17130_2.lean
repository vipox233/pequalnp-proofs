import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17130_2
    (hLineInter :
      ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
        (∀ (p q : Fin n), p ≠ q → ∃! l : Fin n, p ∈ S l ∧ q ∈ S l) →
        ∀ (l1 l2 : Fin n), l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ))
    (hSizeBound :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ q →
        n = q ^ (2 : ℕ) + q + (1 : ℕ) →
        q % (2 : ℕ) = (0 : ℕ) →
        (∀ (l : Fin n), (S l).card = q + (1 : ℕ)) →
        (∀ (p1 p2 : Fin n), p1 ≠ p2 → ∃! l : Fin n, p1 ∈ S l ∧ p2 ∈ S l) →
        (∀ (l1 l2 : Fin n), l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ)) →
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.GenericRejection.RightOnIncidentPairs S C →
        (∀ (X Y : Finset (Fin n)), Y.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S X Y → C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = Bool.false) →
        (2 : ℕ) * q ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.true, Bool.false]) C.gates).length →
        (100 : ℕ) * (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.true, Bool.false]) C.gates).length < n * q →
        n * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;                 (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → x1 % (2 : ℕ) = (0 : ℕ) → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => !x17.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro x1 x2 x3 x4 x5 hq hn hdeg huniq hmono htrue hfalse x13 h13 hlt heven
  let S : Fin x2 → Finset (Fin x2) := fun l => Finset.univ.filter (fun p => x3 p l)
  have hSdeg : ∀ l : Fin x2, (S l).card = x1 + (1 : ℕ) := by
    intro l
    rw [← hdeg l, Fintype.card_subtype]
  have hSuniq : ∀ p1 p2 : Fin x2, p1 ≠ p2 → ∃! l : Fin x2, p1 ∈ S l ∧ p2 ∈ S l := by
    intro p1 p2 hp
    simpa [S] using huniq p1 p2 hp
  have hSinter : ∀ l1 l2 : Fin x2, l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ) :=
    hLineInter x2 S hSuniq
  have hSright : PEqualNP.GenericRejection.RightOnIncidentPairs S x5 := by
    intro l p hp
    have hpl : x3 p l := by
      simpa [S] using hp
    have htr := htrue p l hpl
    have hlist :
        PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin x2)) ({l} : Finset (Fin x2)) =
          List.ofFn (fun i : Fin (x2 + x2) =>
            Decidable.decide (i = Fin.castAdd x2 p ∨ i = Fin.natAdd x2 l)) := by
      dsimp only [PEqualNP.GenericRejection.incidenceInput]
      refine List.ext_getElem ?_ ?_
      · simp
      · intro i hi1 hi2
        have hi : i < x2 + x2 := by
          simpa using hi2
        by_cases hix : i < x2
        · have hne : (⟨i, hi⟩ : Fin (x2 + x2)) ≠ Fin.natAdd x2 l := by
            intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_natAdd] at hval
            omega
          rw [List.getElem_append_left (by simp [hix])]
          simp only [List.getElem_ofFn, Finset.mem_singleton, hne, or_false, decide_eq_decide]
          exact ⟨fun h => Fin.ext (by simpa [Fin.ext_iff] using h),
            fun h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
        · have hne : (⟨i, hi⟩ : Fin (x2 + x2)) ≠ Fin.castAdd x2 p := by
            intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_castAdd] at hval
            omega
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_ofFn, List.getElem_ofFn, Finset.mem_singleton, hne, false_or, decide_eq_decide]
          exact ⟨fun h => Fin.ext (by
            have hv : i - x2 = l.val := congrArg Fin.val h
            simp only [Fin.val_natAdd]
            omega),
            fun h => Fin.ext (by
              have hv : i = x2 + l.val := by
                have h' := congrArg Fin.val h
                simpa only [Fin.val_natAdd] using h'
              dsimp only
              omega)⟩
    rw [hlist]
    exact htr
  have hSfalse : ∀ (X Y : Finset (Fin x2)),
      Y.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput S X Y →
      x5.eval (PEqualNP.GenericRejection.incidenceInput X Y) = Bool.false := by
    intro X Y hY hF
    let f : Fin (x2 + x2) → Bool := fun i =>
      if h : i.val < x2 then decide (⟨i.val, h⟩ ∈ X) else decide (⟨i.val - x2, by omega⟩ ∈ Y)
    have hlist : PEqualNP.GenericRejection.incidenceInput X Y = List.ofFn f := by
      dsimp only [PEqualNP.GenericRejection.incidenceInput]
      refine List.ext_getElem ?_ ?_
      · simp
      · intro i hi1 hi2
        by_cases hix : i < x2
        · rw [List.getElem_append_left (by simp [hix])]
          simp [f, hix]
        · rw [List.getElem_append_right (by simp; omega)]
          simp [f, hix]
    have hf_left : ∀ p : Fin x2, f (Fin.castAdd x2 p) = decide (p ∈ X) := by
      intro p
      simp [f, p.isLt]
    have hf_right : ∀ l : Fin x2, f (Fin.natAdd x2 l) = decide (l ∈ Y) := by
      intro l
      have hnot : ¬ (x2 + l.val < x2) := by omega
      simp only [f, Fin.val_natAdd, hnot, ↓reduceDIte, decide_eq_decide]
      have hfin : (⟨x2 + l.val - x2, by rw [Nat.add_sub_cancel_left]; exact l.isLt⟩ : Fin x2) = l :=
        Fin.ext (Nat.add_sub_cancel_left x2 l.val)
      rw [hfin]
    have hcard : Fintype.card { l : Fin x2 // f (Fin.natAdd x2 l) = Bool.true } ≤ x1 := by
      rw [Fintype.card_subtype]
      have hfilt : Finset.univ.filter (fun l : Fin x2 => f (Fin.natAdd x2 l) = Bool.true) = Y := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hf_right l]
        simp
      rw [hfilt]
      exact hY
    have hno : ¬∃ (p l : Fin x2),
        x3 p l ∧ f (Fin.castAdd x2 p) = Bool.true ∧ f (Fin.natAdd x2 l) = Bool.true := by
      rintro ⟨p, l, hpl, hp, hl⟩
      have hpX : p ∈ X := by
        rw [hf_left p] at hp
        simpa using hp
      have hlY : l ∈ Y := by
        rw [hf_right l] at hl
        simpa using hl
      have hpS : p ∈ S l := by
        simpa [S] using hpl
      exact Finset.disjoint_left.mp (hF l hlY) hpS hpX
    rw [hlist]
    exact hfalse f hcard hno
  have hlen : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      gs.length =
        (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.true, Bool.false]) gs).length +
        (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.true, Bool.false]) gs).length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases h : g.op.eval [Bool.true, Bool.false] <;> simp [h, ih] <;> omega
  have hsz : x5.size = x13 + (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => !x17.op.eval [Bool.true, Bool.false]) x5.gates).length := hlen x5.gates
  have hres := hSizeBound x1 x2 S x5 hq hn heven hSdeg hSuniq hSinter hmono hSright hSfalse h13 hlt
  rw [hsz] at hres
  omega
