import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8577_2
    (hTranspose : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (n + n) C →
      (∀ (x : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C x =
        Decidable.decide (∃ (a b : Fin n), (a, b) ∈ E ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd n b) = Bool.true)) →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size = C.size ∧ PEqualNP.TopForm.IsAO2 (n + n) C' ∧
        (∀ (x : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C' x =
          Decidable.decide (∃ (a b : Fin n), (a, b) ∈ E.image Prod.swap ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd n b) = Bool.true)))
    (hLeftDeg1 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 + (1 : ℕ) < x2.card → x1 + x1 ≤ x4.size →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      (∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) →
      x2.card + x1 ≤ x4.size + (1 : ℕ)) :
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 + (1 : ℕ) < x2.card → x1 + x1 ≤ x4.size → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ)) := by
  intro x1 x2 x3 x4 hCard hSz hC4 hPerm hAO hFun hDeg
  exact Or.elim hDeg
    (fun hL => hLeftDeg1 x1 x2 x3 x4 hCard hSz hC4 hPerm hAO hFun hL)
    (fun hR =>
      Exists.elim hR fun v hv =>
        Exists.elim (hTranspose x1 x2 x4 hAO hFun) fun C' hC' =>
          have hC'sz : C'.size = x4.size := hC'.1
          have hC'AO : PEqualNP.TopForm.IsAO2 (x1 + x1) C' := hC'.2.1
          have hC'Fun := hC'.2.2
          have hEcard : (x2.image Prod.swap).card = x2.card :=
            Finset.card_image_of_injective x2 Prod.swap_injective
          have hmem : ∀ a b : Fin x1, (a, b) ∈ x2.image Prod.swap ↔ (b, a) ∈ x2 := fun a b =>
            Iff.intro
              (fun h =>
                Exists.elim (Finset.mem_image.mp h) fun pq hpq =>
                  have h1 : pq.2 = a := congrArg Prod.fst hpq.2
                  have h2 : pq.1 = b := congrArg Prod.snd hpq.2
                  have h3 : (b, a) = pq := Prod.ext h2.symm h1.symm
                  h3 ▸ hpq.1)
              (fun h => Finset.mem_image.mpr ⟨(b, a), h, rfl⟩)
          have hC4' : ∀ (a b c d : Fin x1), a ≠ b → c ≠ d →
              ¬((a, c) ∈ x2.image Prod.swap ∧ (a, d) ∈ x2.image Prod.swap ∧
                (b, c) ∈ x2.image Prod.swap ∧ (b, d) ∈ x2.image Prod.swap) :=
            fun a b c d hab hcd h =>
              hC4 c d a b hcd hab
                ⟨(hmem a c).mp h.1, (hmem b c).mp h.2.2.1, (hmem a d).mp h.2.1, (hmem b d).mp h.2.2.2⟩
          have hPerm' : ∀ a : Fin x1, (a, x3.symm a) ∈ x2.image Prod.swap := fun a =>
            (hmem a (x3.symm a)).mpr (by simpa using hPerm (x3.symm a))
          have hL' : ∃ u : Fin x1, ∀ w : Fin x1, (u, w) ∈ x2.image Prod.swap → w = x3.symm u :=
            ⟨v, fun w hw => (Equiv.eq_symm_apply x3).mpr (hv w ((hmem v w).mp hw))⟩
          have hres := hLeftDeg1 x1 (x2.image Prod.swap) x3.symm C'
            (by omega) (by omega) hC4' hPerm' hC'AO hC'Fun hL'
          by omega)
