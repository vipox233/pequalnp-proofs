import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_5921_417
    (size62 : ∀ (C : Circuit), Monotone2 C → C.size ≤ 62 →
      RightOnIncidentPairs singerLines3 C →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        C.eval (incidenceInput X Y) = false) → False)
    (pureOr : ∀ (B : Circuit) (T : Finset (Finset ℕ)),
      Monotone2 B →
      (∀ g ∈ B.gates, g.op = GateOp.or) →
      13 ≤ T.card →
      B.size + 2 * T.card ≤ 64 →
      (∀ t ∈ T, t.card = 2 ∧ t ⊆ Finset.range (26 + B.size)) →
      let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
      (∀ t ∈ T, ∃ (p l : Fin 13), p ∈ singerLines3 l ∧
        fires t (incidenceInput {p} {l}) ∧
        ∀ s ∈ T, s ≠ t → ¬ fires s (incidenceInput {p} {l})) →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        ∀ t ∈ T, ¬ fires t (incidenceInput X Y)) →
      (∀ (p l : Fin 13), p ∈ singerLines3 l →
        ∃ t ∈ T, fires t (incidenceInput {p} {l})) → False)
    (allAnchored : ∀ (B : Circuit) (T : Finset (Finset ℕ)),
      Monotone2 B →
      (∃ g ∈ B.gates, g.op = GateOp.and) →
      13 ≤ T.card →
      B.size + 2 * T.card ≤ 64 →
      (∀ t ∈ T, t.card = 2 ∧ (∃ w ∈ t, w < 26) ∧ t ⊆ Finset.range (26 + B.size)) →
      let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
      (∀ t ∈ T, ∃ (p l : Fin 13), p ∈ singerLines3 l ∧
        fires t (incidenceInput {p} {l}) ∧
        ∀ s ∈ T, s ≠ t → ¬ fires s (incidenceInput {p} {l})) →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        ∀ t ∈ T, ¬ fires t (incidenceInput X Y)) →
      (∀ (p l : Fin 13), p ∈ singerLines3 l →
        ∃ t ∈ T, fires t (incidenceInput {p} {l})) → False)
    (hasPureGateTerm : ∀ (B : Circuit) (T : Finset (Finset ℕ)),
      Monotone2 B →
      (∃ g ∈ B.gates, g.op = GateOp.and) →
      2 ≤ B.size →
      13 ≤ T.card →
      B.size + 2 * T.card ≤ 64 →
      (∀ t ∈ T, t.card = 2 ∧ t ⊆ Finset.range (26 + B.size)) →
      (∃ t ∈ T, ∀ w ∈ t, 26 ≤ w) →
      let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
      (∀ t ∈ T, ∃ (p l : Fin 13), p ∈ singerLines3 l ∧
        fires t (incidenceInput {p} {l}) ∧
        ∀ s ∈ T, s ≠ t → ¬ fires s (incidenceInput {p} {l})) →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        ∀ t ∈ T, ¬ fires t (incidenceInput X Y)) →
      (∀ (p l : Fin 13), p ∈ singerLines3 l →
        ∃ t ∈ T, fires t (incidenceInput {p} {l})) → False) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => {x3 : Fin (13 : ℕ) | x3 - x2 ∈ x1}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset (Finset ℕ)),   PEqualNP.MetaComplexity.Monotone2 x3 →     x3.size ≤ (38 : ℕ) →       (13 : ℕ) ≤ x4.card →         (∀ x8 ∈ x4, x8.card ≤ (2 : ℕ) ∧ x8 ⊆ Finset.range ((26 : ℕ) + x3.size)) →           have x9 : Finset ℕ → List Bool → Prop := fun (x9 : Finset ℕ) (x10 : List Bool) => ∀ x11 ∈ x9, (x3.wires x10).getD x11 Bool.false = Bool.true;           (∀ x10 ∈ x4, ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 ∧ x9 x10 (PEqualNP.GenericRejection.incidenceInput {x12} {x13}) ∧ ∀ x14 ∈ x4, x14 ≠ x10 → ¬x9 x14 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) → (∀ (x11 x12 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x2 x11 x12 → ¬PEqualNP.GenericRejection.InNoLine x2 x11 ∨ ¬PEqualNP.GenericRejection.InNoPencil x2 x12 → ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput x11 x12)) → (∀ (x12 x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 → ∃ x15 ∈ x4, x9 x15 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) → (65 : ℕ) ≤ x3.size + (2 : ℕ) * x4.card) := by
  dsimp only
  intro B T hMono _ hTcard hTerms hWit hSafe hCover
  let x1 : Finset (Fin 13) := {0, 1, 3, 9}
  let x2 : Fin 13 → Finset (Fin 13) := fun l => {p : Fin 13 | p - l ∈ x1}
  have hSingDef : ∀ l : Fin 13, singerLines3 l =
      Finset.univ.filter fun p : Fin 13 => (p.val + 13 - l.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ) :=
    fun _ => rfl
  have hIncDef : ∀ (X Y : Finset (Fin 13)), incidenceInput X Y =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) :=
    fun _ _ => rfl
  have opAnd : ∀ xs : List Bool, GateOp.and.eval xs = xs.all id := fun _ => rfl
  have opOr : ∀ xs : List Bool, GateOp.or.eval xs = xs.any id := fun _ => rfl
  have hSizeDef : ∀ C : Circuit, C.size = C.gates.length := fun _ => rfl
  have hMemS : ∀ p l : Fin 13, p ∈ x2 l ↔ p ∈ singerLines3 l := by
    intro p l
    rw [hSingDef]
    simp only [x2, x1, Finset.mem_filter, Finset.mem_univ, true_and]
    revert p l
    decide
  have hS : (fun l : Fin 13 => ({p : Fin 13 | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))} : Finset (Fin 13))) =
      singerLines3 := by
    funext l
    ext p
    exact hMemS p l
  have hSApp : ∀ l : Fin 13, ({p : Fin 13 | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))} : Finset (Fin 13)) =
      singerLines3 l := fun l => congrFun hS l
  simp only [hSApp] at hWit hSafe hCover
  by_contra hNot65
  have hBudget : B.size + 2 * T.card ≤ 64 := by omega
  let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
  have hLenInc : ∀ (X Y : Finset (Fin 13)), (incidenceInput X Y).length = 26 := by
    intro X Y
    rw [hIncDef]
    simp
  have hWiresLen : ∀ (gs : List Gate) (x : List Bool), ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro x; rfl
    | cons g gs ih =>
      intro x
      change ((Circuit.mk gs 0).wires (x ++ [_])).length = _
      rw [ih]
      simp
      omega
  have hWiresAppend : ∀ (gs₁ gs₂ : List Gate) (x : List Bool),
      (Circuit.mk (gs₁ ++ gs₂) 0).wires x =
        (Circuit.mk gs₂ 0).wires ((Circuit.mk gs₁ 0).wires x) := by
    intro gs₁ gs₂ x
    change List.foldl _ x (gs₁ ++ gs₂) = List.foldl _ (List.foldl _ x gs₁) gs₂
    rw [List.foldl_append]
  have hWiresSnoc : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      (Circuit.mk (gs ++ [g]) 0).wires x =
        (Circuit.mk gs 0).wires x ++ [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
    intro gs g x
    rw [hWiresAppend]
    rfl
  have hGetDPrefix : ∀ (gs₁ gs₂ : List Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs₁.length →
      ((Circuit.mk (gs₁ ++ gs₂) 0).wires x).getD i false =
        ((Circuit.mk gs₁ 0).wires x).getD i false := by
    intro gs₁ gs₂ x i hi
    induction gs₂ using List.reverseRecOn with
    | nil => simp
    | append_singleton gs₂ g ih =>
      rw [← List.append_assoc, hWiresSnoc]
      have hlt : i < ((Circuit.mk (gs₁ ++ gs₂) 0).wires x).length := by
        rw [hWiresLen]
        simp
        omega
      rw [List.getD_append _ _ _ _ hlt, ih]
  have hGetDLast : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      ((Circuit.mk (gs ++ [g]) 0).wires x).getD (x.length + gs.length) false =
        g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false) := by
    intro gs g x
    rw [hWiresSnoc]
    have hlen : ((Circuit.mk gs 0).wires x).length = x.length + gs.length := hWiresLen gs x
    rw [← hlen, List.getD_eq_getElem _ _ (by simp)]
    simp
  have hGetDOther : ∀ (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ),
      i ≠ x.length + gs.length →
      ((Circuit.mk (gs ++ [g]) 0).wires x).getD i false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    intro gs g x i hi
    rw [hWiresSnoc]
    have hlen : ((Circuit.mk gs 0).wires x).length = x.length + gs.length := hWiresLen gs x
    by_cases hlt : i < ((Circuit.mk gs 0).wires x).length
    · exact List.getD_append _ _ _ _ hlt
    · have hge1 : ((Circuit.mk gs 0).wires x).length ≤ i := Nat.le_of_not_lt hlt
      let b := g.op.eval (g.inputs.map fun k => ((Circuit.mk gs 0).wires x).getD k false)
      have hge2 : (((Circuit.mk gs 0).wires x) ++ [b]).length ≤ i := by
        simp
        omega
      rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]
  have hDiag : ∀ p : Fin 13, p ∈ singerLines3 p := by
    intro p
    rw [← hMemS]
    simp [x2, x1]
  have hEmptyUnivMF : IsMaximalFalse singerLines3 ∅ Finset.univ ∧ ¬ InNoLine singerLines3 ∅ := by
    refine ⟨⟨fun l _ => Finset.disjoint_empty_right _, ?_, fun l hl => False.elim (hl (Finset.mem_univ l))⟩,
      fun h => h 0 (Finset.empty_subset _)⟩
    intro p _ hf
    exact Finset.disjoint_left.mp (hf p (Finset.mem_univ p)) (hDiag p) (Finset.mem_insert_self p ∅)
  have hRejEU : ∀ t ∈ T, ¬ fires t (incidenceInput ∅ Finset.univ) :=
    hSafe ∅ Finset.univ hEmptyUnivMF.1 (Or.inl hEmptyUnivMF.2)
  have hNonEmpty : ∀ t ∈ T, 1 ≤ t.card := by
    intro t ht
    by_contra h0
    have hcard0 : t.card = 0 := by omega
    have hte : t = ∅ := Finset.card_eq_zero.mp hcard0
    exact hRejEU t ht (by simp [fires, hte])
  have hCard12 : ∀ t ∈ T, t.card = 1 ∨ t.card = 2 := by
    intro t ht
    have h1 := hNonEmpty t ht
    have h2 := (hTerms t ht).1
    omega
  by_cases hHasOne : ∃ t ∈ T, t.card = 1
  · have hBuild : ∀ L : List (Finset ℕ), L ≠ [] →
        (∀ t ∈ L, (t.card = 1 ∨ t.card = 2) ∧ t ⊆ Finset.range (26 + B.size)) →
        ∃ (gs : List Gate) (out : ℕ),
          Monotone2 ⟨B.gates ++ gs, out⟩ ∧
          gs.length + 1 + (L.filter fun t => decide (t.card = 1)).length ≤ 2 * L.length ∧
          out < 26 + B.size + gs.length ∧
          ∀ x : List Bool, x.length = 26 →
            ((Circuit.mk (B.gates ++ gs) out).eval x = true ↔ ∃ t ∈ L, fires t x) := by
      intro L
      induction L with
      | nil => intro h; exact False.elim (h rfl)
      | cons t L' ih =>
        intro _ hL
        have htMem : t ∈ t :: L' := List.mem_cons_self
        have htInfo := hL t htMem
        have hSingleOrPair : ∀ s : Finset ℕ, s.card = 1 ∨ s.card = 2 →
            (∃ w, s = {w}) ∨ (∃ a b, a ≠ b ∧ s = {a, b}) := by
          intro s hs
          rcases hs with h1 | h2
          · left; exact Finset.card_eq_one.mp h1
          · right; exact Finset.card_eq_two.mp h2
        by_cases hL'empty : L' = []
        · subst hL'empty
          rcases hSingleOrPair t htInfo.1 with ⟨w, rfl⟩ | ⟨a, b, hab, rfl⟩
          · refine ⟨[], w, ?_, ?_, ?_, ?_⟩
            · intro g hg
              exact hMono g (by simpa using hg)
            · simp
            · have hw := Finset.mem_range.mp (htInfo.2 (Finset.mem_singleton_self w))
              simpa using hw
            · intro x _
              change ((Circuit.mk (B.gates ++ []) w).wires x).getD w false = true ↔ _
              simp only [List.append_nil]
              change (B.wires x).getD w false = true ↔ _
              simp [fires]
          · refine ⟨[⟨GateOp.and, [a, b]⟩], 26 + B.size, ?_, ?_, ?_, ?_⟩
            · intro g hg
              rcases List.mem_append.mp hg with hg | hg
              · exact hMono g hg
              · obtain rfl := List.mem_singleton.mp hg
                exact ⟨Or.inl rfl, by simp⟩
            · have hcard2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
              simp [hcard2]
            · simp
            · intro x hx
              change ((Circuit.mk (B.gates ++ [⟨GateOp.and, [a, b]⟩]) 0).wires x).getD (26 + B.size) false = true ↔ _
              rw [← hx]
              change ((Circuit.mk (B.gates ++ [⟨GateOp.and, [a, b]⟩]) 0).wires x).getD (x.length + B.gates.length) false = true ↔ _
              rw [hGetDLast, opAnd]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.and_eq_true, List.mem_singleton, exists_eq_left, fires,
                Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
              rfl
        · have hL' : ∀ s ∈ L', (s.card = 1 ∨ s.card = 2) ∧ s ⊆ Finset.range (26 + B.size) :=
            fun s hs => hL s (List.mem_cons_of_mem t hs)
          obtain ⟨gs', out', hMono', hLen', hOut', hEval'⟩ := ih hL'empty hL'
          rcases hSingleOrPair t htInfo.1 with ⟨w, rfl⟩ | ⟨a, b, hab, rfl⟩
          · refine ⟨gs' ++ [⟨GateOp.or, [w, out']⟩], 26 + B.size + gs'.length, ?_, ?_, ?_, ?_⟩
            · intro g hg
              rw [← List.append_assoc] at hg
              rcases List.mem_append.mp hg with hg | hg
              · exact hMono' g hg
              · obtain rfl := List.mem_singleton.mp hg
                exact ⟨Or.inr rfl, by simp⟩
            · simp only [List.length_append, List.length_cons, List.length_nil, List.filter_cons,
                Finset.card_singleton, decide_true, ↓reduceIte] at hLen' ⊢
              omega
            · simp
            · intro x hx
              have hw : w < x.length + B.gates.length := by
                have := Finset.mem_range.mp (htInfo.2 (Finset.mem_singleton_self w))
                rw [hx]; exact this
              change ((Circuit.mk (B.gates ++ (gs' ++ [⟨GateOp.or, [w, out']⟩])) 0).wires x).getD (26 + B.size + gs'.length) false = true ↔ _
              rw [← List.append_assoc]
              have hidx : 26 + B.size + gs'.length = x.length + (B.gates ++ gs').length := by
                rw [hSizeDef, hx, List.length_append]; omega
              rw [hidx, hGetDLast, opOr]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.or_eq_true]
              rw [hGetDPrefix B.gates gs' x w hw]
              change ((B.wires x).getD w false = true ∨
                (Circuit.mk (B.gates ++ gs') out').eval x = true) ↔ _
              rw [hEval' x hx]
              simp [fires]
          · let idx1 := 26 + B.size + gs'.length
            let g1 : Gate := ⟨GateOp.and, [a, b]⟩
            let g2 : Gate := ⟨GateOp.or, [idx1, out']⟩
            refine ⟨gs' ++ [g1, g2], idx1 + 1, ?_, ?_, ?_, ?_⟩
            · intro g hg
              have hsplit : B.gates ++ (gs' ++ [g1, g2]) = ((B.gates ++ gs') ++ [g1]) ++ [g2] := by simp
              rw [hsplit] at hg
              rcases List.mem_append.mp hg with hg | hg
              · rcases List.mem_append.mp hg with hg | hg
                · exact hMono' g hg
                · obtain rfl := List.mem_singleton.mp hg
                  exact ⟨Or.inl rfl, by simp [g1]⟩
              · obtain rfl := List.mem_singleton.mp hg
                exact ⟨Or.inr rfl, by simp [g2]⟩
            · have hcard2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
              simp only [List.length_append, List.length_cons, List.length_nil, List.filter_cons,
                hcard2, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, ↓reduceIte] at hLen' ⊢
              omega
            · dsimp [idx1]; simp; omega
            · intro x hx
              have ha : a < x.length + B.gates.length := by
                have := Finset.mem_range.mp (htInfo.2 (Finset.mem_insert_self a {b}))
                rw [hx]; exact this
              have hb : b < x.length + B.gates.length := by
                have := Finset.mem_range.mp (htInfo.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
                rw [hx]; exact this
              have hsplit : B.gates ++ (gs' ++ [g1, g2]) = ((B.gates ++ gs') ++ [g1]) ++ [g2] := by simp
              change ((Circuit.mk (B.gates ++ (gs' ++ [g1, g2])) 0).wires x).getD (idx1 + 1) false = true ↔ _
              rw [hsplit]
              have hidx2 : idx1 + 1 = x.length + ((B.gates ++ gs') ++ [g1]).length := by
                dsimp [idx1]; rw [hSizeDef, hx]; simp; omega
              have hidx1 : idx1 = x.length + (B.gates ++ gs').length := by
                dsimp [idx1]; rw [hSizeDef, hx]; simp; omega
              rw [hidx2, hGetDLast]
              dsimp only [g2]
              rw [opOr]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.or_eq_true]
              rw [hidx1, hGetDLast]
              have houtNe : out' ≠ x.length + (B.gates ++ gs').length := by
                rw [← hidx1]; dsimp [idx1]; omega
              rw [hGetDOther (B.gates ++ gs') g1 x out' houtNe]
              dsimp only [g1]
              rw [opAnd]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.and_eq_true]
              rw [hGetDPrefix B.gates gs' x a ha, hGetDPrefix B.gates gs' x b hb]
              change (((B.wires x).getD a false = true ∧ (B.wires x).getD b false = true) ∨
                (Circuit.mk (B.gates ++ gs') out').eval x = true) ↔ _
              rw [hEval' x hx]
              simp [fires]
    let L := T.toList
    obtain ⟨t1, ht1T, ht1Card⟩ := hHasOne
    have ht1L : t1 ∈ L := Finset.mem_toList.mpr ht1T
    have hLne : L ≠ [] := List.ne_nil_of_mem ht1L
    have hLinfo : ∀ t ∈ L, (t.card = 1 ∨ t.card = 2) ∧ t ⊆ Finset.range (26 + B.size) := by
      intro t ht
      have htT := Finset.mem_toList.mp ht
      exact ⟨hCard12 t htT, (hTerms t htT).2⟩
    obtain ⟨gs, out, hCmono, hClen, _, hCeval⟩ := hBuild L hLne hLinfo
    let C : Circuit := ⟨B.gates ++ gs, out⟩
    have hF1pos : 1 ≤ (L.filter fun t => decide (t.card = 1)).length := by
      have hm : t1 ∈ L.filter fun t => decide (t.card = 1) :=
        List.mem_filter.mpr ⟨ht1L, decide_eq_true ht1Card⟩
      exact List.length_pos_of_mem hm
    have hCsize : C.size ≤ 62 := by
      have hLlen : L.length = T.card := Finset.length_toList T
      have hCsz : C.size = B.size + gs.length := by
        rw [hSizeDef, hSizeDef]; exact List.length_append
      omega
    have hCRight : RightOnIncidentPairs singerLines3 C := by
      intro l p hpl
      rw [hCeval (incidenceInput {p} {l}) (hLenInc {p} {l})]
      obtain ⟨t, htT, hft⟩ := hCover p l hpl
      exact ⟨t, Finset.mem_toList.mpr htT, hft⟩
    have hCSafe : ∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        C.eval (incidenceInput X Y) = false := by
      intro X Y hmf hdeg
      refine Bool.eq_false_iff.mpr fun hval => ?_
      rw [hCeval (incidenceInput X Y) (hLenInc X Y)] at hval
      obtain ⟨t, htL, hft⟩ := hval
      exact hSafe X Y hmf hdeg t (Finset.mem_toList.mp htL) hft
    exact size62 C hCmono hCsize hCRight hCSafe
  · push Not at hHasOne
    have hAllTwo : ∀ t ∈ T, t.card = 2 := by
      intro t ht
      rcases hCard12 t ht with h1 | h2
      · exact False.elim (hHasOne t ht h1)
      · exact h2
    by_cases hHasAnd : ∃ g ∈ B.gates, g.op = GateOp.and
    · by_cases hAllAnch : ∀ t ∈ T, ∃ w ∈ t, w < 26
      · exact allAnchored B T hMono hHasAnd hTcard hBudget
          (fun t ht => ⟨hAllTwo t ht, hAllAnch t ht, (hTerms t ht).2⟩)
          hWit hSafe hCover
      · push Not at hAllAnch
        obtain ⟨tPure, htPure, hPureGe⟩ := hAllAnch
        obtain ⟨u, v, huv, htPureEq⟩ := Finset.card_eq_two.mp (hAllTwo tPure htPure)
        have huGe : 26 ≤ u := hPureGe u (by rw [htPureEq]; simp)
        have hvGe : 26 ≤ v := hPureGe v (by rw [htPureEq]; simp)
        have huLt : u < 26 + B.size := Finset.mem_range.mp ((hTerms tPure htPure).2 (by rw [htPureEq]; simp))
        have hvLt : v < 26 + B.size := Finset.mem_range.mp ((hTerms tPure htPure).2 (by rw [htPureEq]; simp))
        have hBsize2 : 2 ≤ B.size := by omega
        exact hasPureGateTerm B T hMono hHasAnd hBsize2 hTcard hBudget
          (fun t ht => ⟨hAllTwo t ht, (hTerms t ht).2⟩)
          ⟨tPure, htPure, hPureGe⟩ hWit hSafe hCover
    · push Not at hHasAnd
      have hAllOr : ∀ g ∈ B.gates, g.op = GateOp.or := by
        intro g hg
        rcases (hMono g hg).1 with ha | ho
        · exact False.elim (hHasAnd g hg ha)
        · exact ho
      exact pureOr B T hMono hAllOr hTcard hBudget
        (fun t ht => ⟨hAllTwo t ht, (hTerms t ht).2⟩)
        hWit hSafe hCover
