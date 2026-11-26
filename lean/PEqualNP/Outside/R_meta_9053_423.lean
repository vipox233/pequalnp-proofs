import PEqualNP.Defs

open PEqualNP.AndCount

theorem PEqualNP.Outside.R_meta_9053_423
    (hFloor :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42,
        C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i v, C.gateVal {v} i = false) →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
        C.size ≤ 20 →
        19 ≤ C.size ∧
        (∀ v : Fin 42, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard + 16 ≤ C.size) ∧
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨ l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard + 14 ≤ C.size))
    (hDirty19 :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42,
        C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i v, C.gateVal {v} i = false) →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
        C.size = 19 →
        (∀ v : Fin 42, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 3) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨ l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 5) →
        (∃ i : Fin C.size, i ∉ C.outGates ∧ ∃ u ∈ C.leftVars i, ∃ v ∈ C.rightVars i, ¬ G.Adj u v) →
        False)
    (hDirty20 :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42,
        C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i v, C.gateVal {v} i = false) →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) →
        C.size = 20 →
        (∀ v : Fin 42, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨ l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 6) →
        (∃ i : Fin C.size, i ∉ C.outGates ∧ ∃ u ∈ C.leftVars i, ∃ v ∈ C.rightVars i, ¬ G.Adj u v) →
        False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : Fin (3 : ℕ) → Fin (14 : ℕ) → Fin (42 : ℕ) := fun (x2 : Fin (3 : ℕ)) (x3 : Fin (14 : ℕ)) => Fin.ofNat (42 : ℕ) (if ↑x3 < (7 : ℕ) then ((9 : ℕ) * ↑x3 + ↑x2) % (21 : ℕ) else (21 : ℕ) + ((9 : ℕ) * (↑x3 - (7 : ℕ)) + ↑x2 + (5 : ℕ)) % (21 : ℕ)); ∀ (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x3.WellFormed → x3.Computes x1 → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x7 : Fin (3 : ℕ)), x6.WellFormed ∧ x6.Computes x1 ∧ x6.size ≤ x3.size ∧ (3 : ℕ) * {x8 : Fin x6.size | x6.gateVal (Finset.image (x2 x7) Finset.univ) x8 = Bool.true}.ncard ≤ x6.size := by
  classical
  intro G e D hWF hComp
  let rel : Fin 42 → Fin 42 → Prop := fun a b =>
    a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  have hAdj : ∀ a b : Fin 42, G.Adj a b ↔ a ≠ b ∧ (rel a b ∨ rel b a) := fun a b =>
    SimpleGraph.fromRel_adj rel a b
  have hSideDef : ∀ {k : ℕ} (U B : Finset (Fin 42)) (F : Finset (Fin k)) (i : Fin k)
      (val : Fin k → Bool),
      AndCountCircuit.sideTrue U B F i val =
        decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) :=
    fun _ _ _ _ _ => rfl
  have hEvalDef : ∀ (A : AndCountCircuit 42) (U : Finset (Fin 42)),
      A.eval U = decide ((∃ v ∈ A.outVars, v ∈ U) ∨ ∃ j ∈ A.outGates, A.gateVal U j = true) :=
    fun _ _ => rfl
  have hFuel0 : ∀ (A : AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin A.size),
      A.gateValFuel U 0 i = false :=
    fun _ _ _ => rfl
  have hFuelS : ∀ (A : AndCountCircuit 42) (U : Finset (Fin 42)) (d : ℕ) (i : Fin A.size),
      A.gateValFuel U (d + 1) i =
        (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateValFuel U d) &&
         AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateValFuel U d)) :=
    fun _ _ _ _ => rfl
  by_cases h21 : 21 ≤ D.size
  · let E : AndCountCircuit 42 := {
      size := 21
      leftVars := fun j => {⟨j.val, by omega⟩}
      leftGates := fun _ => ∅
      rightVars := fun j => Finset.univ.filter (fun w : Fin 42 => rel ⟨j.val, by omega⟩ w)
      rightGates := fun _ => ∅
      outVars := ∅
      outGates := Finset.univ
    }
    have hEWF : E.WellFormed := by
      intro i
      exact ⟨fun j hj => absurd hj (Finset.notMem_empty j),
        fun j hj => absurd hj (Finset.notMem_empty j)⟩
    have hEgate : ∀ (U : Finset (Fin 42)) (j : Fin 21),
        E.gateVal U j = true ↔ (⟨j.val, by omega⟩ : Fin 42) ∈ U ∧ ∃ w ∈ U, rel ⟨j.val, by omega⟩ w := by
      intro U j
      have hstep : E.gateVal U j =
          (AndCountCircuit.sideTrue U (E.leftVars j) (E.leftGates j) j (E.gateValFuel U 20) &&
           AndCountCircuit.sideTrue U (E.rightVars j) (E.rightGates j) j (E.gateValFuel U 20)) := rfl
      rw [hstep, hSideDef, hSideDef]
      simp only [Bool.and_eq_true, decide_eq_true_eq, E,
        Finset.mem_singleton, Finset.notMem_empty, false_and, exists_false, or_false,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨v, rfl, hvU⟩, ⟨w, hwrel, hwU⟩⟩
        exact ⟨hvU, w, hwU, hwrel⟩
      · rintro ⟨hjU, w, hwU, hwrel⟩
        exact ⟨⟨⟨j.val, by omega⟩, rfl, hjU⟩, ⟨w, hwrel, hwU⟩⟩
    have hEComp : E.Computes G := by
      intro U
      rw [hEvalDef]
      simp only [decide_eq_true_eq]
      have hout : (∃ v ∈ E.outVars, v ∈ U) ↔ False := by simp [E]
      rw [hout, false_or]
      constructor
      · rintro ⟨j, _, hj⟩
        have hj21 : j.val < 21 := j.isLt
        obtain ⟨hjU, w, hwU, hwrel⟩ := (hEgate U j).mp hj
        have hne : (⟨j.val, by omega⟩ : Fin 42) ≠ w := by
          intro heq
          have h1 := hwrel.1
          have h2 := hwrel.2.1
          have h3 : j.val = w.val := congrArg Fin.val heq
          omega
        exact ⟨⟨j.val, by omega⟩, hjU, w, hwU, (hAdj _ _).mpr ⟨hne, Or.inl hwrel⟩⟩
      · rintro ⟨a, haU, c, hcU, hadj⟩
        rcases ((hAdj a c).mp hadj).2 with hac | hca
        · refine ⟨⟨a.val, hac.1⟩, Finset.mem_univ _, (hEgate U ⟨a.val, hac.1⟩).mpr ⟨haU, c, hcU, hac⟩⟩
        · refine ⟨⟨c.val, hca.1⟩, Finset.mem_univ _, (hEgate U ⟨c.val, hca.1⟩).mpr ⟨hcU, a, haU, hca⟩⟩
    refine ⟨E, (0 : Fin 3), hEWF, hEComp, h21, ?_⟩
    let S0 : Finset (Fin 42) := Finset.image (e 0) Finset.univ
    have hMcard : (Finset.univ.filter (fun j : Fin 21 => j.val % 3 = 0)).card = 7 := by decide
    let M : Finset (Fin 21) := Finset.univ.filter (fun j : Fin 21 => j.val % 3 = 0)
    have hsub : {x8 : Fin 21 | E.gateVal S0 x8 = true} ⊆ (M : Set (Fin 21)) := by
      intro j hj
      change E.gateVal S0 j = true at hj
      have hjS : (⟨j.val, by omega⟩ : Fin 42) ∈ S0 := ((hEgate S0 j).mp hj).1
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hjS
      have hval : (e 0 k).val = j.val := congrArg Fin.val hk
      have hmod : j.val % 3 = 0 := by
        dsimp only [e] at hval
        by_cases hk7 : k.val < 7
        · simp only [hk7, ↓reduceIte] at hval
          have hlt : (9 * k.val + (0 : Fin 3).val) % 21 < 42 := by omega
          simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hlt] at hval
          omega
        · simp only [hk7, ↓reduceIte] at hval
          have hlt : 21 + (9 * (k.val - 7) + (0 : Fin 3).val + 5) % 21 < 42 := by omega
          simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hlt] at hval
          omega
      change j ∈ M
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmod⟩
    have hnc : {x8 : Fin 21 | E.gateVal S0 x8 = true}.ncard ≤ 7 := by
      calc {x8 : Fin 21 | E.gateVal S0 x8 = true}.ncard
          ≤ (M : Set (Fin 21)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = M.card := Set.ncard_coe_finset M
        _ = 7 := hMcard
    change 3 * {x8 : Fin 21 | E.gateVal S0 x8 = true}.ncard ≤ 21
    omega
  · exfalso
    have h20 : D.size ≤ 20 := by omega
    have hSideCongr : ∀ {k : ℕ} (U B : Finset (Fin 42)) (F : Finset (Fin k)) (i : Fin k)
        (v1 v2 : Fin k → Bool), (∀ j, j < i → v1 j = v2 j) →
        AndCountCircuit.sideTrue U B F i v1 = AndCountCircuit.sideTrue U B F i v2 := by
      intro k U B F i v1 v2 h
      rw [hSideDef, hSideDef]
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hvj⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
      · rintro (hv | ⟨j, hjF, hji, hvj⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩
    have hFuelIndep : ∀ (A : AndCountCircuit 42) (U : Finset (Fin 42)) (m : ℕ) (i : Fin A.size),
        i.val < m → ∀ d1 d2 : ℕ, i.val < d1 → i.val < d2 →
          A.gateValFuel U d1 i = A.gateValFuel U d2 i := by
      intro A U m
      induction m with
      | zero => intro i hi; omega
      | succ m ih =>
        intro i hi d1 d2 hd1 hd2
        obtain ⟨k1, rfl⟩ : ∃ k1, d1 = k1 + 1 := ⟨d1 - 1, by omega⟩
        obtain ⟨k2, rfl⟩ : ∃ k2, d2 = k2 + 1 := ⟨d2 - 1, by omega⟩
        rw [hFuelS, hFuelS]
        have hlt : ∀ j : Fin A.size, j < i → A.gateValFuel U k1 j = A.gateValFuel U k2 j := by
          intro j hji
          exact ih j (by omega) k1 k2 (by omega) (by omega)
        rw [hSideCongr U (A.leftVars i) (A.leftGates i) i _ _ hlt,
            hSideCongr U (A.rightVars i) (A.rightGates i) i _ _ hlt]
    have hUnfold : ∀ (A : AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin A.size),
        A.gateVal U i =
          (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateVal U) &&
           AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateVal U)) := by
      intro A U i
      have heq : A.gateVal U i = A.gateValFuel U (i.val + 1) i :=
        hFuelIndep A U A.size i i.isLt A.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
      rw [heq, hFuelS]
      have hlt : ∀ j : Fin A.size, j < i → A.gateValFuel U i.val j = A.gateVal U j := by
        intro j hji
        exact hFuelIndep A U A.size j j.isLt i.val A.size hji j.isLt
      rw [hSideCongr U (A.leftVars i) (A.leftGates i) i _ _ hlt,
          hSideCongr U (A.rightVars i) (A.rightGates i) i _ _ hlt]
    have hMono : ∀ (A : AndCountCircuit 42) {U W : Finset (Fin 42)}, U ⊆ W →
        ∀ (d : ℕ) (i : Fin A.size), A.gateValFuel U d i = true → A.gateValFuel W d i = true := by
      intro A U W hUW d
      induction d with
      | zero =>
        intro i hi
        rw [hFuel0] at hi
        exact absurd hi Bool.false_ne_true
      | succ d ih =>
        intro i hi
        rw [hFuelS, hSideDef, hSideDef] at hi ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hi ⊢
        refine ⟨?_, ?_⟩
        · rcases hi.1 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
          · exact Or.inl ⟨v, hvB, hUW hvU⟩
          · exact Or.inr ⟨j, hjF, hji, ih j hvj⟩
        · rcases hi.2 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
          · exact Or.inl ⟨v, hvB, hUW hvU⟩
          · exact Or.inr ⟨j, hjF, hji, ih j hvj⟩
    let sing : Fin D.size → Finset (Fin 42) := fun i =>
      Finset.univ.filter (fun v => D.gateVal {v} i = true)
    let C : AndCountCircuit 42 := {
      size := D.size
      leftVars := fun i => (D.leftVars i ∪ ((D.leftGates i).filter (fun j => j < i)).biUnion sing) \ sing i
      leftGates := D.leftGates
      rightVars := fun i => (D.rightVars i ∪ ((D.rightGates i).filter (fun j => j < i)).biUnion sing) \ sing i
      rightGates := D.rightGates
      outVars := D.outVars ∪ D.outGates.biUnion sing
      outGates := D.outGates
    }
    have hMemL : ∀ (i : Fin D.size) (v : Fin 42),
        v ∈ C.leftVars i ↔
          (v ∈ D.leftVars i ∨ ∃ j ∈ D.leftGates i, j < i ∧ D.gateVal {v} j = true) ∧
          D.gateVal {v} i ≠ true := by
      intro i v
      change v ∈ (D.leftVars i ∪ ((D.leftGates i).filter (fun j => j < i)).biUnion sing) \ sing i ↔ _
      simp only [sing, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    have hMemR : ∀ (i : Fin D.size) (v : Fin 42),
        v ∈ C.rightVars i ↔
          (v ∈ D.rightVars i ∨ ∃ j ∈ D.rightGates i, j < i ∧ D.gateVal {v} j = true) ∧
          D.gateVal {v} i ≠ true := by
      intro i v
      change v ∈ (D.rightVars i ∪ ((D.rightGates i).filter (fun j => j < i)).biUnion sing) \ sing i ↔ _
      simp only [sing, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    have hMemO : ∀ v : Fin 42,
        v ∈ C.outVars ↔ v ∈ D.outVars ∨ ∃ j ∈ D.outGates, D.gateVal {v} j = true := by
      intro v
      change v ∈ D.outVars ∪ D.outGates.biUnion sing ↔ _
      simp only [sing, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
    have hCWF : C.WellFormed := hWF
    have hCsing : ∀ (v : Fin 42) (m : ℕ) (i : Fin C.size), i.val < m → C.gateVal {v} i = false := by
      intro v m
      induction m with
      | zero => intro i hi; omega
      | succ m ih =>
        intro i hi
        rw [Bool.eq_false_iff]
        intro htrue
        rw [hUnfold C {v} i, Bool.and_eq_true] at htrue
        obtain ⟨hL, hR⟩ := htrue
        rw [hSideDef] at hL hR
        rw [decide_eq_true_eq] at hL hR
        have hLv : v ∈ C.leftVars i := by
          rcases hL with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
          · rwa [Finset.mem_singleton.mp hwv] at hw
          · rw [ih j (by omega)] at hjv
            exact absurd hjv Bool.false_ne_true
        have hRv : v ∈ C.rightVars i := by
          rcases hR with ⟨w, hw, hwv⟩ | ⟨j, _, hji, hjv⟩
          · rwa [Finset.mem_singleton.mp hwv] at hw
          · rw [ih j (by omega)] at hjv
            exact absurd hjv Bool.false_ne_true
        rw [hMemL] at hLv
        rw [hMemR] at hRv
        have hDv : D.gateVal {v} i = true := by
          rw [hUnfold D {v} i, Bool.and_eq_true]
          constructor
          · rw [hSideDef, decide_eq_true_eq]
            rcases hLv.1 with hv | ⟨j, hjF, hji, hjv⟩
            · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
            · exact Or.inr ⟨j, hjF, hji, hjv⟩
          · rw [hSideDef, decide_eq_true_eq]
            rcases hRv.1 with hv | ⟨j, hjF, hji, hjv⟩
            · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
            · exact Or.inr ⟨j, hjF, hji, hjv⟩
        exact hLv.2 hDv
    have hCdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i) := by
      intro i
      rw [Finset.disjoint_left]
      intro v hvL hvR
      have hf := hCsing v C.size i i.isLt
      have ht : C.gateVal {v} i = true := by
        rw [hUnfold C {v} i, Bool.and_eq_true]
        exact ⟨by rw [hSideDef, decide_eq_true_eq]; exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩,
               by rw [hSideDef, decide_eq_true_eq]; exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩⟩
      rw [hf] at ht
      exact Bool.false_ne_true ht
    have hCval_le : ∀ (U : Finset (Fin 42)) (m : ℕ) (i : Fin C.size), i.val < m →
        C.gateVal U i = true → D.gateVal U i = true := by
      intro U m
      induction m with
      | zero => intro i hi; omega
      | succ m ih =>
        intro i hi hval
        rw [hUnfold C U i, Bool.and_eq_true] at hval
        rw [hUnfold D U i, Bool.and_eq_true]
        obtain ⟨hL, hR⟩ := hval
        rw [hSideDef] at hL hR
        rw [hSideDef, hSideDef]
        simp only [decide_eq_true_eq] at hL hR ⊢
        refine ⟨?_, ?_⟩
        · rcases hL with ⟨v, hvL, hvU⟩ | ⟨j, hjF, hji, hjv⟩
          · rw [hMemL] at hvL
            rcases hvL.1 with hv | ⟨j, hjF, hji, hjv⟩
            · exact Or.inl ⟨v, hv, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hMono D (Finset.singleton_subset_iff.mpr hvU) D.size j hjv⟩
          · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
        · rcases hR with ⟨v, hvR, hvU⟩ | ⟨j, hjF, hji, hjv⟩
          · rw [hMemR] at hvR
            rcases hvR.1 with hv | ⟨j, hjF, hji, hjv⟩
            · exact Or.inl ⟨v, hv, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hMono D (Finset.singleton_subset_iff.mpr hvU) D.size j hjv⟩
          · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    have hCval_ge : ∀ (U : Finset (Fin 42)) (m : ℕ) (i : Fin C.size), i.val < m →
        D.gateVal U i = true → C.gateVal U i = true ∨ ∃ v ∈ U, D.gateVal {v} i = true := by
      intro U m
      induction m with
      | zero => intro i hi; omega
      | succ m ih =>
        intro i hi hval
        by_cases hsing : ∃ v ∈ U, D.gateVal {v} i = true
        · exact Or.inr hsing
        · left
          push Not at hsing
          rw [hUnfold D U i, Bool.and_eq_true] at hval
          rw [hUnfold C U i, Bool.and_eq_true]
          obtain ⟨hL, hR⟩ := hval
          rw [hSideDef] at hL hR
          rw [hSideDef, hSideDef]
          simp only [decide_eq_true_eq] at hL hR ⊢
          refine ⟨?_, ?_⟩
          · rcases hL with ⟨v, hvL, hvU⟩ | ⟨j, hjF, hji, hjv⟩
            · exact Or.inl ⟨v, (hMemL i v).mpr ⟨Or.inl hvL, hsing v hvU⟩, hvU⟩
            · rcases ih j (by omega) hjv with hCj | ⟨v, hvU, hDj⟩
              · exact Or.inr ⟨j, hjF, hji, hCj⟩
              · exact Or.inl ⟨v, (hMemL i v).mpr ⟨Or.inr ⟨j, hjF, hji, hDj⟩, hsing v hvU⟩, hvU⟩
          · rcases hR with ⟨v, hvR, hvU⟩ | ⟨j, hjF, hji, hjv⟩
            · exact Or.inl ⟨v, (hMemR i v).mpr ⟨Or.inl hvR, hsing v hvU⟩, hvU⟩
            · rcases ih j (by omega) hjv with hCj | ⟨v, hvU, hDj⟩
              · exact Or.inr ⟨j, hjF, hji, hCj⟩
              · exact Or.inl ⟨v, (hMemR i v).mpr ⟨Or.inr ⟨j, hjF, hji, hDj⟩, hsing v hvU⟩, hvU⟩
    have hCComp : C.Computes G := by
      intro U
      rw [← hComp U, hEvalDef, hEvalDef]
      simp only [decide_eq_true_eq]
      constructor
      · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
        · rw [hMemO] at hvO
          rcases hvO with hv | ⟨j, hjO, hDj⟩
          · exact Or.inl ⟨v, hv, hvU⟩
          · exact Or.inr ⟨j, hjO, hMono D (Finset.singleton_subset_iff.mpr hvU) D.size j hDj⟩
        · exact Or.inr ⟨j, hjO, hCval_le U C.size j j.isLt hjv⟩
      · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
        · exact Or.inl ⟨v, (hMemO v).mpr (Or.inl hvO), hvU⟩
        · rcases hCval_ge U C.size j j.isLt hjv with hCj | ⟨v, hvU, hDj⟩
          · exact Or.inr ⟨j, hjO, hCj⟩
          · exact Or.inl ⟨v, (hMemO v).mpr (Or.inr ⟨j, hjO, hDj⟩), hvU⟩
    have hCout : C.outVars = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      have hev : C.eval {v} = true := by
        rw [hEvalDef, decide_eq_true_eq]
        exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
      obtain ⟨a, ha, c, hc, hadj⟩ := (hCComp {v}).mp hev
      rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hc] at hadj
      exact G.ne_of_adj hadj rfl
    have hInv : ∀ d1 ∈ ([0, 5, 7, 17, 20] : List ℕ), ∀ d2 ∈ ([0, 5, 7, 17, 20] : List ℕ),
        d1 ≠ d2 →
        ([0, 0, 7, 20, 0, 5, 5, 7, 7, 5, 17, 7, 17, 20, 0, 20, 0, 17, 17, 5, 20] : List ℕ).getD
          ((d1 + 21 - d2) % 21) 0 = d1 := by decide
    have hDiffSet : ∀ d1 ∈ ([0, 5, 7, 17, 20] : List ℕ), ∀ d2 ∈ ([0, 5, 7, 17, 20] : List ℕ),
        ∀ d3 ∈ ([0, 5, 7, 17, 20] : List ℕ), ∀ d4 ∈ ([0, 5, 7, 17, 20] : List ℕ),
        (d1 + 21 - d2) % 21 = (d3 + 21 - d4) % 21 → d1 ≠ d2 → d1 = d3 := by
      intro d1 h1 d2 h2 d3 h3 d4 h4 heq hne
      have hlt : ∀ d ∈ ([0, 5, 7, 17, 20] : List ℕ), d < 21 := by decide
      have h1lt := hlt d1 h1
      have h2lt := hlt d2 h2
      have hne34 : d3 ≠ d4 := by
        intro h34
        subst h34
        have : (d3 + 21 - d3) % 21 = 0 := by omega
        omega
      have e1 := hInv d1 h1 d2 h2 hne
      have e2 := hInv d3 h3 d4 h4 hne34
      rw [← e1, heq, e2]
    have hModSub1 : ∀ a b c : ℕ, 21 ≤ a → a < 42 → 21 ≤ b → b < 42 → c < 21 →
        ((a + 21 - c) % 21 + 21 - (b + 21 - c) % 21) % 21 = (a + 21 - b) % 21 := by
      intro a b c ha1 ha2 hb1 hb2 hc
      omega
    have hModSub2 : ∀ a b c : ℕ, a < 21 → b < 21 → 21 ≤ c → c < 42 →
        ((c + 21 - a) % 21 + 21 - (c + 21 - b) % 21) % 21 = (b + 21 - a) % 21 := by
      intro a b c ha hb hc1 hc2
      omega
    have hNoC4 : ∀ u1 u2 v1 v2 : Fin 42, u1 ≠ u2 → v1 ≠ v2 →
        G.Adj u1 v1 → G.Adj u1 v2 → G.Adj u2 v1 → ¬ G.Adj u2 v2 := by
      intro u1 u2 v1 v2 hu hv h11 h12 h21 h22
      have h11' := ((hAdj u1 v1).mp h11).2
      have h12' := ((hAdj u1 v2).mp h12).2
      have h21' := ((hAdj u2 v1).mp h21).2
      have h22' := ((hAdj u2 v2).mp h22).2
      by_cases hu1 : u1.val < 21
      · have hr11 : rel u1 v1 := h11'.resolve_right (fun h => by have := h.2.1; omega)
        have hr12 : rel u1 v2 := h12'.resolve_right (fun h => by have := h.2.1; omega)
        have hv1 : 21 ≤ v1.val := hr11.2.1
        have hv2 : 21 ≤ v2.val := hr12.2.1
        have hr21 : rel u2 v1 := h21'.resolve_right (fun h => by have := h.1; omega)
        have hr22 : rel u2 v2 := h22'.resolve_right (fun h => by have := h.1; omega)
        have hEqMod : ((v1.val + 21 - u1.val) % 21 + 21 - (v2.val + 21 - u1.val) % 21) % 21 =
            ((v1.val + 21 - u2.val) % 21 + 21 - (v2.val + 21 - u2.val) % 21) % 21 := by
          rw [hModSub1 v1.val v2.val u1.val hv1 v1.isLt hv2 v2.isLt hu1,
              hModSub1 v1.val v2.val u2.val hv1 v1.isLt hv2 v2.isLt hr21.1]
        have hd : (v1.val + 21 - u1.val) % 21 = (v1.val + 21 - u2.val) % 21 :=
          hDiffSet _ hr11.2.2 _ hr12.2.2 _ hr21.2.2 _ hr22.2.2 hEqMod
            (by intro heq; apply hv; apply Fin.ext; omega)
        apply hu
        apply Fin.ext
        have := hr21.1
        omega
      · have hr11 : rel v1 u1 := h11'.resolve_left (fun h => by have := h.1; omega)
        have hr12 : rel v2 u1 := h12'.resolve_left (fun h => by have := h.1; omega)
        have hv1 : v1.val < 21 := hr11.1
        have hv2 : v2.val < 21 := hr12.1
        have hr21 : rel v1 u2 := h21'.resolve_left (fun h => by have := h.2.1; omega)
        have hr22 : rel v2 u2 := h22'.resolve_left (fun h => by have := h.2.1; omega)
        have hEqMod : ((u1.val + 21 - v1.val) % 21 + 21 - (u1.val + 21 - v2.val) % 21) % 21 =
            ((u2.val + 21 - v1.val) % 21 + 21 - (u2.val + 21 - v2.val) % 21) % 21 := by
          rw [hModSub2 v1.val v2.val u1.val hv1 hv2 hr11.2.1 u1.isLt,
              hModSub2 v1.val v2.val u2.val hv1 hv2 hr21.2.1 u2.isLt]
        have hd : (u1.val + 21 - v1.val) % 21 = (u2.val + 21 - v1.val) % 21 :=
          hDiffSet _ hr11.2.2 _ hr12.2.2 _ hr21.2.2 _ hr22.2.2 hEqMod
            (by intro heq; apply hv; apply Fin.ext; omega)
        apply hu
        apply Fin.ext
        have := hr11.2.1
        have := hr21.2.1
        omega
    have hHasDirty : ∃ i : Fin C.size, ∃ u ∈ C.leftVars i, ∃ v ∈ C.rightVars i, ¬ G.Adj u v := by
      by_contra hClean
      push Not at hClean
      have hStar : ∀ i : Fin C.size, (C.leftVars i).card ≤ 1 ∨ (C.rightVars i).card ≤ 1 := by
        intro i
        by_contra hboth
        push Not at hboth
        obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hboth.1
        obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp hboth.2
        exact hNoC4 u1 u2 v1 v2 hune hvne (hClean i u1 hu1 v1 hv1) (hClean i u1 hu1 v2 hv2)
          (hClean i u2 hu2 v1 hv1) (hClean i u2 hu2 v2 hv2)
      let T : Finset (Fin 42) := Finset.univ.biUnion (fun i : Fin C.size =>
        if (C.leftVars i).card ≤ 1 then C.leftVars i else C.rightVars i)
      have hTcard : T.card ≤ C.size := by
        calc T.card
            ≤ ∑ i : Fin C.size, (if (C.leftVars i).card ≤ 1 then C.leftVars i else C.rightVars i).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _i : Fin C.size, 1 := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hL : (C.leftVars i).card ≤ 1
              · simp only [hL, ↓reduceIte]
              · simp only [hL, ↓reduceIte]; exact (hStar i).resolve_left hL
          _ = C.size := by simp
      have hTcover : ∀ a b : Fin 42, G.Adj a b → a ∈ T ∨ b ∈ T := by
        intro a b hab
        by_contra hno
        push Not at hno
        have hfalse : ∀ (m : ℕ) (i : Fin C.size), i.val < m → C.gateVal {a, b} i = false := by
          intro m
          induction m with
          | zero => intro i hi; omega
          | succ m ih =>
            intro i hi
            rw [hUnfold C {a, b} i]
            have hside : ∀ (Vs : Finset (Fin 42)) (Gs : Finset (Fin C.size)),
                Vs ⊆ T → AndCountCircuit.sideTrue {a, b} Vs Gs i (C.gateVal {a, b}) = false := by
              intro Vs Gs hsub
              rw [hSideDef, decide_eq_false_iff_not]
              rintro (⟨w, hwV, hwab⟩ | ⟨j, _, hji, hjv⟩)
              · have hwT : w ∈ T := hsub hwV
                rcases Finset.mem_insert.mp hwab with rfl | hwb
                · exact hno.1 hwT
                · rw [Finset.mem_singleton.mp hwb] at hwT
                  exact hno.2 hwT
              · rw [ih j (by omega)] at hjv
                exact Bool.false_ne_true hjv
            by_cases hL : (C.leftVars i).card ≤ 1
            · have hsub : C.leftVars i ⊆ T := by
                intro w hw
                refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
                simp only [hL, ↓reduceIte]
                exact hw
              rw [hside (C.leftVars i) (C.leftGates i) hsub, Bool.false_and]
            · have hsub : C.rightVars i ⊆ T := by
                intro w hw
                refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
                simp only [hL, ↓reduceIte]
                exact hw
              rw [hside (C.rightVars i) (C.rightGates i) hsub, Bool.and_false]
        have hev : C.eval {a, b} = true :=
          (hCComp {a, b}).mpr ⟨a, Finset.mem_insert_self a {b}, b,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self b), hab⟩
        rw [hEvalDef, decide_eq_true_eq, hCout] at hev
        rcases hev with ⟨v, hv, _⟩ | ⟨j, _, hjv⟩
        · exact Finset.notMem_empty v hv
        · rw [hfalse C.size j j.isLt] at hjv
          exact Bool.false_ne_true hjv
      let f : Fin 21 → Fin 42 := fun p =>
        if (⟨p.val, by omega⟩ : Fin 42) ∈ T then ⟨p.val, by omega⟩ else ⟨p.val + 21, by omega⟩
      have hfT : ∀ p : Fin 21, f p ∈ T := by
        intro p
        dsimp only [f]
        by_cases hp : (⟨p.val, by omega⟩ : Fin 42) ∈ T
        · simp only [hp, ↓reduceIte]
        · simp only [hp, ↓reduceIte]
          have hadj : G.Adj ⟨p.val, by omega⟩ ⟨p.val + 21, by omega⟩ := by
            rw [hAdj]
            refine ⟨by intro heq; have h := congrArg Fin.val heq; dsimp only at h; omega, Or.inl ?_⟩
            refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
            have h0 : ((⟨p.val + 21, by omega⟩ : Fin 42).val + 21 - (⟨p.val, by omega⟩ : Fin 42).val) % 21 = 0 := by
              dsimp only; omega
            rw [h0]
            simp
          exact (hTcover _ _ hadj).resolve_left hp
      have hfinj : Function.Injective f := by
        intro p q hpq
        have hmod : (f p).val % 21 = (f q).val % 21 := congrArg (fun x : Fin 42 => x.val % 21) hpq
        have hp' : (f p).val % 21 = p.val := by
          dsimp only [f]
          split_ifs <;> (dsimp only; omega)
        have hq' : (f q).val % 21 = q.val := by
          dsimp only [f]
          split_ifs <;> (dsimp only; omega)
        apply Fin.ext
        omega
      have h21T : 21 ≤ T.card := by
        calc 21 = (Finset.univ : Finset (Fin 21)).card := by simp
          _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hfinj).symm
          _ ≤ T.card := Finset.card_le_card (by
              intro v hv
              obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
              exact hfT p)
      have hCsize : C.size = D.size := rfl
      omega
    obtain ⟨iDirty, uDirty, huDirty, vDirty, hvDirty, hnotAdj⟩ := hHasDirty
    have hiOut : iDirty ∉ C.outGates := by
      intro hin
      have hgt : C.gateVal {uDirty, vDirty} iDirty = true := by
        rw [hUnfold C {uDirty, vDirty} iDirty, Bool.and_eq_true]
        constructor
        · rw [hSideDef, decide_eq_true_eq]
          exact Or.inl ⟨uDirty, huDirty, Finset.mem_insert_self uDirty {vDirty}⟩
        · rw [hSideDef, decide_eq_true_eq]
          exact Or.inl ⟨vDirty, hvDirty, Finset.mem_insert_of_mem (Finset.mem_singleton_self vDirty)⟩
      have hev : C.eval {uDirty, vDirty} = true := by
        rw [hEvalDef, decide_eq_true_eq]
        exact Or.inr ⟨iDirty, hin, hgt⟩
      obtain ⟨a, ha, c, hc, hadj⟩ := (hCComp {uDirty, vDirty}).mp hev
      rcases Finset.mem_insert.mp ha with rfl | hau
      · rcases Finset.mem_insert.mp hc with rfl | hcv
        · exact G.ne_of_adj hadj rfl
        · rw [Finset.mem_singleton.mp hcv] at hadj
          exact hnotAdj hadj
      · rw [Finset.mem_singleton.mp hau] at hadj
        rcases Finset.mem_insert.mp hc with rfl | hcv
        · exact hnotAdj hadj.symm
        · rw [Finset.mem_singleton.mp hcv] at hadj
          exact G.ne_of_adj hadj rfl
    have hCsize : C.size = D.size := rfl
    obtain ⟨h19, hdeg, hpair⟩ := hFloor C hCWF hCComp hCout (fun i v => hCsing v C.size i i.isLt) hCdisj (by omega)
    have hcases : C.size = 19 ∨ C.size = 20 := by omega
    rcases hcases with hsz | hsz
    · exact hDirty19 C hCWF hCComp hCout (fun i v => hCsing v C.size i i.isLt) hCdisj hsz
        (fun v => by have := hdeg v; omega)
        (fun p l hp hl hn => by have := hpair p l hp hl hn; omega)
        ⟨iDirty, hiOut, uDirty, huDirty, vDirty, hvDirty, hnotAdj⟩
    · exact hDirty20 C hCWF hCComp hCout (fun i v => hCsing v C.size i i.isLt) hCdisj hsz
        (fun v => by have := hdeg v; omega)
        (fun p l hp hl hn => by have := hpair p l hp hl hn; omega)
        ⟨iDirty, hiOut, uDirty, huDirty, vDirty, hvDirty, hnotAdj⟩
