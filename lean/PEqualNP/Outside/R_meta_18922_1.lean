import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18922_1
    (hTableEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit p.val = Bool.true ↔
        ∃ d : Fin (13 : ℕ), d.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ p = l + d)
    (hBitCircuit :
      let adj : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun p l =>
        (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit p.val = Bool.true
      have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (v : Fin (26 : ℕ) → Bool) (k : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (v (0 : Fin (26 : ℕ)) || v (1 : Fin (26 : ℕ))) v k
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x4 ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 ∧
        x4.size ≤ (32 : ℕ) ∧
        x4.output < (27 : ℕ) + x4.size ∧
        (∀ (p l : Fin (13 : ℕ)), ↑l < (7 : ℕ) → adj p l →
          PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (k : Fin (26 : ℕ)) => Decidable.decide (k = Fin.castAdd (13 : ℕ) p ∨ k = Fin.natAdd (13 : ℕ) l)) = Bool.true) ∧
        ∀ (a : Fin (13 : ℕ) → Bool),
          (¬∃ (l : Fin (13 : ℕ)), ∀ (p : Fin (13 : ℕ)), a p = Bool.true → adj p l) →
          (¬∃ (p : Fin (13 : ℕ)), ∀ (l : Fin (13 : ℕ)), (∀ (q : Fin (13 : ℕ)), a q = Bool.true → ¬adj q l) → adj p l) →
          PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (k : Fin (26 : ℕ)) => Fin.addCases a (fun (l : Fin (13 : ℕ)) => Decidable.decide (∀ (q : Fin (13 : ℕ)), a q = Bool.true → ¬adj q l)) k) = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 ∧ x4.size ≤ (32 : ℕ) ∧ x4.output < (27 : ℕ) + x4.size ∧ (∀ (x5 x6 : Fin (13 : ℕ)), ↑x6 < (7 : ℕ) → x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x5 ∨ x9 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) → (¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), (∀ x9 ∈ x5, ¬x2 x9 x8) → x2 x7 x8) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 fun (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x5)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (Disjoint x5 (Finset.image (fun (x10 : Fin (13 : ℕ)) => x9 + x10) x1))) x8) = Bool.false) := by
  have hMem1 : ∀ d : Fin (13 : ℕ), d.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := by decide
  have hAdj : ∀ p l : Fin (13 : ℕ),
      (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit p.val = Bool.true ↔
      ∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = l + d :=
    fun p l => (hTableEquiv p l).trans (exists_congr fun d => and_congr_left' (hMem1 d))
  obtain ⟨x4, hM, hRB, hSz, hOut, hPos, hNeg⟩ := hBitCircuit
  dsimp only
  refine ⟨x4, hM, hRB, hSz, hOut, fun p l hl hpl => hPos p l hl ((hAdj p l).mpr hpl), fun S hNoLine hNoPt => ?_⟩
  have h1 : ¬∃ l : Fin (13 : ℕ), ∀ p : Fin (13 : ℕ), Decidable.decide (p ∈ S) = Bool.true →
      (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit p.val = Bool.true :=
    fun h => Exists.elim h fun l hl => hNoLine ⟨l, fun p hp => (hAdj p l).mp (hl p (decide_eq_true hp))⟩
  have h2 : ¬∃ p : Fin (13 : ℕ), ∀ l : Fin (13 : ℕ),
      (∀ q : Fin (13 : ℕ), Decidable.decide (q ∈ S) = Bool.true →
        ¬(([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit q.val = Bool.true) →
      (([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit p.val = Bool.true :=
    fun h => Exists.elim h fun p hp => hNoPt ⟨p, fun l hl => (hAdj p l).mp (hp l (fun q hq hql => hl q (of_decide_eq_true hq) ((hAdj q l).mp hql)))⟩
  have hRight : (fun l : Fin (13 : ℕ) => Decidable.decide (∀ q : Fin (13 : ℕ), Decidable.decide (q ∈ S) = Bool.true →
      ¬(([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD l.val (0 : ℕ)).testBit q.val = Bool.true)) =
      (fun l : Fin (13 : ℕ) => Decidable.decide (Disjoint S (Finset.image (fun d : Fin (13 : ℕ) => l + d) ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))))) := by
    funext l
    rw [decide_eq_decide]
    exact ⟨fun h => Finset.disjoint_left.mpr (fun q hq hmem =>
      Exists.elim (Finset.mem_image.mp hmem) fun d hd => h q (decide_eq_true hq) ((hAdj q l).mpr ⟨d, hd.1, hd.2.symm⟩)),
      fun h q hq hql => Exists.elim ((hAdj q l).mp hql) fun d hd =>
        Finset.disjoint_left.mp h (of_decide_eq_true hq) (Finset.mem_image.mpr ⟨d, hd.1, hd.2.symm⟩)⟩
  have hRes := hNeg (fun p => Decidable.decide (p ∈ S)) h1 h2
  rw [hRight] at hRes
  exact hRes
