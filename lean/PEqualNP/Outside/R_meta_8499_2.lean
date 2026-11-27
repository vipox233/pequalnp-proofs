import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8499_2
    (hJunkFree : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a b : Fin x1), x3 a ≠ x4 b) → (∀ (a b : Fin x1), (a, b) ∈ x2 → (a, a) ∈ x2 ∧ (b, b) ∈ x2) → (∀ (a b c d : Fin x1), a ≠ b → c ≠ d → ¬((a, c) ∈ x2 ∧ (a, d) ∈ x2 ∧ (b, c) ∈ x2 ∧ (b, d) ∈ x2)) → (∃ (a b : Fin x1), a ≠ b ∧ (a, a) ∈ x2 ∧ (b, b) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → (∀ (v : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 v = Decidable.decide (∃ (a b : Fin x1), (a, b) ∈ x2 ∧ v (x3 a) = Bool.true ∧ v (x4 b) = Bool.true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), D.size ≤ x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) D ∧ (∀ (v : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) D v = PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 v) ∧ ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (v : Fin (x1 + x1) → Bool), PEqualNP.EdgeOwnership.gateVal (x1 + x1) D k v = Bool.true → ∃ (a b : Fin x1), (a, b) ∈ x2 ∧ v (x3 a) = Bool.true ∧ v (x4 b) = Bool.true)
    (hDeleteClean : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1), have x8 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : Finset (Fin x1 × Fin x1)) (x9 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x8 ∧ x10 (x3 x11) = Bool.true ∧ x10 (x4 x12) = Bool.true); have x10 : Finset (Fin x1) := {x10 : Fin x1 | x10 ≠ x6 ∧ (x10, x6) ∈ x2}; have x11 : Finset (Fin x1 × Fin x1) := {x11 ∈ x2 | x11.1 ≠ x6 ∧ x11.2 ≠ x6}; (∀ (x12 x13 : Fin x1), x3 x12 ≠ x4 x13) → (∀ (x13 x14 : Fin x1), (x13, x14) ∈ x2 → (x13, x13) ∈ x2 ∧ (x14, x14) ∈ x2) → (∀ (x14 x15 x16 x17 : Fin x1), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x2 ∧ (x14, x17) ∈ x2 ∧ (x15, x16) ∈ x2 ∧ (x15, x17) ∈ x2)) → (x6, x6) ∈ x2 → (∃ (x16 : Fin x1) (x17 : Fin x1), x16 ≠ x17 ∧ (x16, x16) ∈ x11 ∧ (x17, x17) ∈ x11) → (∀ (x17 : Fin x1), (x6, x17) ∈ x2 → x17 = x6) → (∀ x18 ∈ x10, ∀ x20 ∈ x10, (x18, x20) ∈ x2 ↔ x18 = x20) → (∀ x19 ∈ x10, ∀ x21 ∈ x10, x19 ≠ x21 → ∀ (x24 : Fin x1), x24 ≠ x6 → ¬((x19, x24) ∈ x2 ∧ (x21, x24) ∈ x2)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x8 x2 x5 → (∀ k < x5.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (v : Fin (x1 + x1) → Bool), PEqualNP.EdgeOwnership.gateVal (x1 + x1) x5 k v = Bool.true → ∃ (a b : Fin x1), (a, b) ∈ x2 ∧ v (x3 a) = Bool.true ∧ v (x4 b) = Bool.true) → ∃ (x22 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x22 ∧ x8 x11 x22 ∧ x22.size + x10.card + (2 : ℕ) ≤ x5.size) :
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1) (x7 : Bool),   have x8 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : Finset (Fin x1 × Fin x1)) (x9 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x8 ∧ x10 (x3 x11) = Bool.true ∧ x10 (x4 x12) = Bool.true);   let x9 : Fin x1 → Fin x1 → Prop := fun (x9 x10 : Fin x1) => if x7 = Bool.true then (x10, x9) ∈ x2 else (x9, x10) ∈ x2;   have x10 : Finset (Fin x1) := {x10 : Fin x1 | x10 ≠ x6 ∧ x9 x10 x6};   have x11 : Finset (Fin x1 × Fin x1) := {x11 ∈ x2 | x11.1 ≠ x6 ∧ x11.2 ≠ x6};   (∀ (x12 x13 : Fin x1), x3 x12 ≠ x4 x13) → (∀ (x13 x14 : Fin x1), (x13, x14) ∈ x2 → (x13, x13) ∈ x2 ∧ (x14, x14) ∈ x2) → (∀ (x14 x15 x16 x17 : Fin x1), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x2 ∧ (x14, x17) ∈ x2 ∧ (x15, x16) ∈ x2 ∧ (x15, x17) ∈ x2)) → (x6, x6) ∈ x2 → (∃ (x16 : Fin x1) (x17 : Fin x1), x16 ≠ x17 ∧ (x16, x16) ∈ x11 ∧ (x17, x17) ∈ x11) → (∀ (x17 : Fin x1), x9 x6 x17 → x17 = x6) → (∀ x18 ∈ x10, ∀ x20 ∈ x10, x9 x18 x20 ↔ x18 = x20) → (∀ x19 ∈ x10, ∀ x21 ∈ x10, x19 ≠ x21 → ∀ (x24 : Fin x1), x24 ≠ x6 → ¬(x9 x19 x24 ∧ x9 x21 x24)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x8 x2 x5 → ∃ (x22 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x22 ∧ x8 x11 x22 ∧ x22.size + x10.card + (2 : ℕ) ≤ x5.size) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 hDisj hDiag hC4 h6 hTwo hDeg1 hInd hDisjN hAO hFun
  by_cases hx7 : x7 = Bool.true
  · have hx9 : ∀ a b : Fin x1, x9 a b ↔ (b, a) ∈ x2 := fun a b => by
      change (if x7 = Bool.true then (b, a) ∈ x2 else (a, b) ∈ x2) ↔ (b, a) ∈ x2
      rw [if_pos hx7]
    let x2' : Finset (Fin x1 × Fin x1) := x2.image Prod.swap
    have hmem : ∀ a b : Fin x1, (a, b) ∈ x2' ↔ (b, a) ∈ x2 := by
      intro a b
      constructor
      · intro h
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
        have h1 : p.2 = a := congrArg Prod.fst heq
        have h2 : p.1 = b := congrArg Prod.snd heq
        rw [← h2, ← h1]
        exact hp
      · intro h
        exact Finset.mem_image.mpr ⟨(b, a), h, rfl⟩
    have hDisj' : ∀ a b : Fin x1, x4 a ≠ x3 b := fun a b h => hDisj b a h.symm
    have hDiag' : ∀ a b : Fin x1, (a, b) ∈ x2' → (a, a) ∈ x2' ∧ (b, b) ∈ x2' := by
      intro a b h
      have hba := (hmem a b).mp h
      exact ⟨(hmem a a).mpr (hDiag b a hba).2, (hmem b b).mpr (hDiag b a hba).1⟩
    have hC4' : ∀ a b c d : Fin x1, a ≠ b → c ≠ d → ¬((a, c) ∈ x2' ∧ (a, d) ∈ x2' ∧ (b, c) ∈ x2' ∧ (b, d) ∈ x2') := by
      intro a b c d hab hcd hq
      exact hC4 c d a b hcd hab ⟨(hmem a c).mp hq.1, (hmem b c).mp hq.2.2.1, (hmem a d).mp hq.2.1, (hmem b d).mp hq.2.2.2⟩
    have h6' : (x6, x6) ∈ x2' := (hmem x6 x6).mpr h6
    have hFun' : ∀ v : Fin (x1 + x1) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 v = Decidable.decide (∃ a b : Fin x1, (a, b) ∈ x2' ∧ v (x4 a) = Bool.true ∧ v (x3 b) = Bool.true) := by
      intro v
      rw [hFun v, decide_eq_decide]
      constructor
      · intro h
        obtain ⟨a, b, hab, ha, hb⟩ := h
        exact ⟨b, a, (hmem b a).mpr hab, hb, ha⟩
      · intro h
        obtain ⟨a, b, hab, ha, hb⟩ := h
        exact ⟨b, a, (hmem a b).mp hab, hb, ha⟩
    have hTwo2' : ∃ a b : Fin x1, a ≠ b ∧ (a, a) ∈ x2' ∧ (b, b) ∈ x2' := by
      obtain ⟨a, b, hab, ha, hb⟩ := hTwo
      exact ⟨a, b, hab, (hmem a a).mpr (Finset.mem_filter.mp ha).1, (hmem b b).mpr (Finset.mem_filter.mp hb).1⟩
    obtain ⟨D, hDsize, hDAO, hDsame, hDclean⟩ := hJunkFree x1 x2' x4 x3 x5 hDisj' hDiag' hC4' hTwo2' hAO hFun'
    have hDFun' : ∀ v : Fin (x1 + x1) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x1) D v = Decidable.decide (∃ a b : Fin x1, (a, b) ∈ x2' ∧ v (x4 a) = Bool.true ∧ v (x3 b) = Bool.true) :=
      fun v => (hDsame v).trans (hFun' v)
    have h10eq : ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)) = x10 := by
      ext y
      constructor
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hx9 y x6).mpr ((hmem y x6).mp h1.2)⟩
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hmem y x6).mpr ((hx9 y x6).mp h1.2)⟩
    have hTwo' : ∃ a b : Fin x1, a ≠ b ∧ (a, a) ∈ ({p ∈ x2' | p.1 ≠ x6 ∧ p.2 ≠ x6} : Finset (Fin x1 × Fin x1)) ∧ (b, b) ∈ ({p ∈ x2' | p.1 ≠ x6 ∧ p.2 ≠ x6} : Finset (Fin x1 × Fin x1)) := by
      obtain ⟨a, b, hab, ha, hb⟩ := hTwo
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
      exact ⟨a, b, hab, Finset.mem_filter.mpr ⟨(hmem a a).mpr ha1, ha2⟩, Finset.mem_filter.mpr ⟨(hmem b b).mpr hb1, hb2⟩⟩
    have hDeg1' : ∀ y : Fin x1, (x6, y) ∈ x2' → y = x6 :=
      fun y hy => hDeg1 y ((hx9 x6 y).mpr ((hmem x6 y).mp hy))
    have hInd' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), (a, b) ∈ x2' ↔ a = b := by
      intro a ha b hb
      rw [h10eq] at ha hb
      exact (hmem a b).trans ((hx9 a b).symm.trans (hInd a ha b hb))
    have hDisjN' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), a ≠ b → ∀ z : Fin x1, z ≠ x6 → ¬((a, z) ∈ x2' ∧ (b, z) ∈ x2') := by
      intro a ha b hb hab z hz hpair
      rw [h10eq] at ha hb
      exact hDisjN a ha b hb hab z hz ⟨(hx9 a z).mpr ((hmem a z).mp hpair.1), (hx9 b z).mpr ((hmem b z).mp hpair.2)⟩
    obtain ⟨x22, h22AO, h22Fun', h22Sz⟩ := hDeleteClean x1 x2' x4 x3 D x6 hDisj' hDiag' hC4' h6' hTwo' hDeg1' hInd' hDisjN' hDAO hDFun' hDclean
    refine ⟨x22, h22AO, ?_, ?_⟩
    · intro v
      rw [h22Fun' v, decide_eq_decide]
      constructor
      · intro h
        obtain ⟨a, b, hab, ha, hb⟩ := h
        obtain ⟨hab1, hab2⟩ := Finset.mem_filter.mp hab
        exact ⟨b, a, Finset.mem_filter.mpr ⟨(hmem a b).mp hab1, hab2.2, hab2.1⟩, hb, ha⟩
      · intro h
        obtain ⟨a, b, hab, ha, hb⟩ := h
        obtain ⟨hab1, hab2⟩ := Finset.mem_filter.mp hab
        exact ⟨b, a, Finset.mem_filter.mpr ⟨(hmem b a).mpr hab1, hab2.2, hab2.1⟩, hb, ha⟩
    · rw [h10eq] at h22Sz
      exact Nat.le_trans h22Sz hDsize
  · have hx9 : ∀ a b : Fin x1, x9 a b ↔ (a, b) ∈ x2 := fun a b => by
      change (if x7 = Bool.true then (b, a) ∈ x2 else (a, b) ∈ x2) ↔ (a, b) ∈ x2
      rw [if_neg hx7]
    have h10eq : ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)) = x10 := by
      ext y
      constructor
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hx9 y x6).mpr h1.2⟩
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hx9 y x6).mp h1.2⟩
    have hTwo2 : ∃ a b : Fin x1, a ≠ b ∧ (a, a) ∈ x2 ∧ (b, b) ∈ x2 := by
      obtain ⟨a, b, hab, ha, hb⟩ := hTwo
      exact ⟨a, b, hab, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp hb).1⟩
    obtain ⟨D, hDsize, hDAO, hDsame, hDclean⟩ := hJunkFree x1 x2 x3 x4 x5 hDisj hDiag hC4 hTwo2 hAO hFun
    have hDFun : x8 x2 D := fun v => (hDsame v).trans (hFun v)
    have hDeg1' : ∀ y : Fin x1, (x6, y) ∈ x2 → y = x6 := fun y hy => hDeg1 y ((hx9 x6 y).mpr hy)
    have hInd' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), (a, b) ∈ x2 ↔ a = b := by
      intro a ha b hb
      rw [h10eq] at ha hb
      exact (hx9 a b).symm.trans (hInd a ha b hb)
    have hDisjN' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), a ≠ b → ∀ z : Fin x1, z ≠ x6 → ¬((a, z) ∈ x2 ∧ (b, z) ∈ x2) := by
      intro a ha b hb hab z hz hpair
      rw [h10eq] at ha hb
      exact hDisjN a ha b hb hab z hz ⟨(hx9 a z).mpr hpair.1, (hx9 b z).mpr hpair.2⟩
    obtain ⟨x22, h22AO, h22Fun, h22Sz⟩ := hDeleteClean x1 x2 x3 x4 D x6 hDisj hDiag hC4 h6 hTwo hDeg1' hInd' hDisjN' hDAO hDFun hDclean
    rw [h10eq] at h22Sz
    exact ⟨x22, h22AO, h22Fun, Nat.le_trans h22Sz hDsize⟩
