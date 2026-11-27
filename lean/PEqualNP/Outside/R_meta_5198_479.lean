import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_5198_479
    (hOneDirty :
      let P : Fin 13 → Finset (Fin 13) := singerLines3
      let dirty : Circuit → ℕ → Prop := fun C j =>
        j < C.size ∧ (gateAt C j).op = GateOp.and ∧
        ∃ Q : Finset (Fin 13), IsQuadrangle P Q ∧
          (C.wires (incidenceInput Q (missLines P Q))).getD (26 + j) false = true
      let aa : Circuit → ℕ → Prop := fun C j =>
        (gateAt C j).op = GateOp.and ∧
        ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i - 26)).op = GateOp.and
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → C.output < 26 + C.size →
        RightOnIncidentPairs P C →
        (∀ Q : Finset (Fin 13), IsQuadrangle P Q → C.eval (incidenceInput Q (missLines P Q)) = false) →
        (∀ j ∈ Finset.range C.size, ∀ k ∈ Finset.range C.size, aa C j → aa C k → j = k) →
        (∃ g < C.size, dirty C g ∧ ∀ g' < C.size, dirty C g' → g' = g) →
        64 ≤ C.size)
    (hTwoDirty :
      let P : Fin 13 → Finset (Fin 13) := singerLines3
      let dirty : Circuit → ℕ → Prop := fun C j =>
        j < C.size ∧ (gateAt C j).op = GateOp.and ∧
        ∃ Q : Finset (Fin 13), IsQuadrangle P Q ∧
          (C.wires (incidenceInput Q (missLines P Q))).getD (26 + j) false = true
      let aa : Circuit → ℕ → Prop := fun C j =>
        (gateAt C j).op = GateOp.and ∧
        ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i - 26)).op = GateOp.and
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → C.output < 26 + C.size →
        RightOnIncidentPairs P C →
        (∀ Q : Finset (Fin 13), IsQuadrangle P Q → C.eval (incidenceInput Q (missLines P Q)) = false) →
        (∀ j ∈ Finset.range C.size, ∀ k ∈ Finset.range C.size, aa C j → aa C k → j = k) →
        (∃ g1 g2 : ℕ, g1 < g2 ∧ g2 < C.size ∧ dirty C g1 ∧ dirty C g2) →
        64 ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) → (63 : ℕ) ≤ x7.size := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hinc_len : ∀ A B : Finset (Fin 13), (incidenceInput A B).length = 26 := by
    intro A B
    show ((List.ofFn fun i : Fin 13 => decide (i ∈ A)) ++ (List.ofFn fun i : Fin 13 => decide (i ∈ B))).length = 26
    simp
  intro x1 x2 x3 x4 x5 x6 C0 a0 b0 hMono0 hRB0 ha0 hb0 hPos0 hQuad0 _ _ hAA0
  have foldl_len : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β),
      (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
    intro α β f l
    induction l with
    | nil => intro acc; simp
    | cons a t ih => intro acc; simp only [List.foldl_cons, List.length_cons]; rw [ih, List.length_append, List.length_singleton]; omega
  have foldl_getD_lt : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β) (d : β) (k : ℕ),
      k < acc.length → (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
    intro α β f l
    induction l with
    | nil => intro acc d k _; rfl
    | cons a t ih =>
      intro acc d k hk
      simp only [List.foldl_cons]
      have hk' : k < (acc ++ [f acc a]).length := by rw [List.length_append, List.length_singleton]; omega
      rw [ih (acc ++ [f acc a]) d k hk', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have foldl_getD_gate : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β) (d : β) (j : ℕ),
      j < l.length → ∀ defaultA : α,
      (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
        f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
    intro α β f l acc d j hj defaultA
    have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
      have h1 := (List.take_append_drop j l).symm
      have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [← h2]; exact h1
    have hget : l.getD j defaultA = l[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hget]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
    have hprelen : pre.length = acc.length + j := by rw [foldl_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by rw [List.length_append, List.length_singleton, hprelen]; omega
    rw [foldl_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt, List.getD_eq_getElem?_getD, ← hprelen]
    simp
  have foldl_take_getD : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β) (d : β) (j i : ℕ),
      j ≤ l.length → i < acc.length + j →
      ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
        (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
    intro α β f l acc d j i hj hi
    have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
      rw [foldl_len, List.length_take, Nat.min_eq_left hj]
    rw [foldl_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]
  have gateAt_mem : ∀ {C : Circuit} {j : ℕ}, j < C.gates.length → gateAt C j ∈ C.gates := by
    intro C j hj
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have lt_gates_of_and : ∀ {C : Circuit} {j : ℕ}, (gateAt C j).op = GateOp.and → j < C.gates.length := by
    intro C j hop
    by_contra hge
    push Not at hge
    have hdef : gateAt C j = ⟨GateOp.or, []⟩ := by
      unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [hdef] at hop; cases hop
  have gateOp_ao : ∀ {C : Circuit}, Monotone2 C → ∀ {j : ℕ}, j < C.gates.length →
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro C hM j hj
    simpa using (hM (gateAt C j) (gateAt_mem hj)).1
  have gate_len_le : ∀ {C : Circuit}, Monotone2 C → ∀ {j : ℕ}, j < C.gates.length →
      (gateAt C j).inputs.length ≤ 2 := by
    intro C hM j hj
    exact (hM (gateAt C j) (gateAt_mem hj)).2
  have wires_len : ∀ (C : Circuit) (inp : List Bool), (C.wires inp).length = inp.length + C.gates.length :=
    fun C inp => foldl_len _ C.gates inp
  have wires_ge : ∀ (C : Circuit) (inp : List Bool) {w : ℕ}, inp.length + C.gates.length ≤ w →
      (C.wires inp).getD w false = false := by
    intro C inp w hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; exact hw)]; rfl
  have wires_in : ∀ (C : Circuit) (inp : List Bool) {w : ℕ}, w < inp.length →
      (C.wires inp).getD w false = inp.getD w false := by
    intro C inp w hw
    exact foldl_getD_lt _ C.gates inp false w hw
  have wires_gate : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ (inp : List Bool), inp.length = n →
      ∀ {j : ℕ}, j < C.gates.length →
      (C.wires inp).getD (n + j) false =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => (C.wires inp).getD w false) := by
    intro n C hRB inp hlen j hj
    unfold Circuit.wires
    have hgate := foldl_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      C.gates inp false j hj ⟨GateOp.or, []⟩
    rw [hlen] at hgate
    rw [hgate]
    change (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp).getD i false) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp).getD i false)
    congr 1
    apply List.map_congr_left
    intro i hi
    exact foldl_take_getD _ C.gates inp false j i (Nat.le_of_lt hj) (by rw [hlen]; exact hRB j hj i hi)
  have hD_size : ∀ (g : Gate), (⟨C0.gates ++ [g], 26 + C0.size⟩ : Circuit).size = C0.size + 1 := by
    intro g; show (C0.gates ++ [g]).length = C0.gates.length + 1; rw [List.length_append, List.length_singleton]
  let D0 : Circuit := ⟨C0.gates ++ [⟨GateOp.or, [a0, b0]⟩], 26 + C0.size⟩
  have hD0_size : D0.size = C0.size + 1 := hD_size ⟨GateOp.or, [a0, b0]⟩
  have hD0_gate_lt : ∀ j < C0.size, gateAt D0 j = gateAt C0 j := by
    intro j hj
    have hj' : j < C0.gates.length := hj
    unfold gateAt; dsimp only [D0]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
  have hD0_gate_last : gateAt D0 C0.size = ⟨GateOp.or, [a0, b0]⟩ := by
    unfold gateAt; dsimp only [D0, Circuit.size]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
  have hD0_mono : Monotone2 D0 := by
    intro g hg
    simp only [D0, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hMono0 g hg
    · simp
  have hD0_rb : ReadsBack 26 D0 := by
    intro j hj i hi
    have hj' : j < C0.size + 1 := by have : j < D0.size := hj; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
    · rw [hD0_gate_lt j hlt] at hi; exact hRB0 j hlt i hi
    · rw [hD0_gate_last] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
  have hD0_wires : ∀ inp : List Bool, D0.wires inp =
      C0.wires inp ++ [(C0.wires inp).getD a0 false || (C0.wires inp).getD b0 false] := by
    intro inp
    have e : D0.wires inp = C0.wires inp ++ [([a0, b0].map fun i => (C0.wires inp).getD i false).any id] := by
      show List.foldl _ inp (C0.gates ++ [⟨GateOp.or, [a0, b0]⟩]) = _
      rw [List.foldl_append]; rfl
    rw [e, List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil, id_eq, id_eq, Bool.or_false]
  have hD0_eval : ∀ inp : List Bool, inp.length = 26 →
      D0.eval inp = ((C0.wires inp).getD a0 false || (C0.wires inp).getD b0 false) := by
    intro inp hlen
    show (D0.wires inp).getD (26 + C0.gates.length) false = _
    rw [hD0_wires, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [wires_len, hlen])]
    simp [wires_len, hlen]
  have hD0_pos : RightOnIncidentPairs singerLines3 D0 := by
    intro l p hp
    rw [hD0_eval _ (hinc_len _ _)]
    rcases hPos0 p l hp with h | h
    · change (C0.wires (incidenceInput {p} {l})).getD a0 false = true at h
      rw [h, Bool.true_or]
    · change (C0.wires (incidenceInput {p} {l})).getD b0 false = true at h
      rw [h, Bool.or_true]
  have hD0_quad : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      D0.eval (incidenceInput Q (missLines singerLines3 Q)) = false := by
    intro Q hQ
    rw [hD0_eval _ (hinc_len _ _)]
    obtain ⟨h1, h2⟩ := hQuad0 Q hQ
    change (C0.wires (incidenceInput Q (missLines singerLines3 Q))).getD a0 false = false at h1
    change (C0.wires (incidenceInput Q (missLines singerLines3 Q))).getD b0 false = false at h2
    rw [h1, h2]; rfl
  have hD0_aa : ∀ j ∈ Finset.range D0.size, ∀ k ∈ Finset.range D0.size,
      ((gateAt D0 j).op = GateOp.and ∧ ∃ i ∈ (gateAt D0 j).inputs, 26 ≤ i ∧ (gateAt D0 (i - 26)).op = GateOp.and) →
      ((gateAt D0 k).op = GateOp.and ∧ ∃ i ∈ (gateAt D0 k).inputs, 26 ≤ i ∧ (gateAt D0 (i - 26)).op = GateOp.and) →
      j = k := by
    have toC0 : ∀ j < D0.size,
        ((gateAt D0 j).op = GateOp.and ∧ ∃ i ∈ (gateAt D0 j).inputs, 26 ≤ i ∧ (gateAt D0 (i - 26)).op = GateOp.and) →
        j < C0.size ∧ x6 C0 j := by
      intro j hj h; rcases h with ⟨hop, i, hi, hi26, hiop⟩
      have hjlt : j < C0.size := by
        by_contra hge
        have hjeq : j = C0.size := by omega
        subst hjeq; rw [hD0_gate_last] at hop; cases hop
      rw [hD0_gate_lt j hjlt] at hop hi
      have hilt : i < 26 + j := hRB0 j hjlt i hi
      rw [hD0_gate_lt (i - 26) (by omega)] at hiop
      exact ⟨hjlt, hop, i, hi, hi26, hiop⟩
    intro j hj k hk h1 h2
    obtain ⟨hj', h1'⟩ := toC0 j (Finset.mem_range.mp hj) h1
    obtain ⟨hk', h2'⟩ := toC0 k (Finset.mem_range.mp hk) h2
    exact hAA0 j (Finset.mem_range.mpr hj') k (Finset.mem_range.mpr hk') h1' h2'
  have hD0_out : D0.output < 26 + D0.size := by show 26 + C0.size < 26 + D0.size; omega
  let dirtyPred : Circuit → ℕ → Prop := fun C j =>
    j < C.size ∧ (gateAt C j).op = GateOp.and ∧
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + j) false = true
  by_cases hHasDirty : ∃ g < D0.size, dirtyPred D0 g
  · obtain ⟨g, hg, hdg⟩ := hHasDirty
    by_cases hSecond : ∃ g' < D0.size, g' ≠ g ∧ dirtyPred D0 g'
    · obtain ⟨g', hg', hne, hdg'⟩ := hSecond
      have h64 : 64 ≤ D0.size := by
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hTwoDirty D0 hD0_mono hD0_rb hD0_out hD0_pos hD0_quad hD0_aa ⟨g', g, hlt, hg, hdg', hdg⟩
        · exact hTwoDirty D0 hD0_mono hD0_rb hD0_out hD0_pos hD0_quad hD0_aa ⟨g, g', hlt, hg', hdg, hdg'⟩
      omega
    · have h64 : 64 ≤ D0.size := hOneDirty D0 hD0_mono hD0_rb hD0_out hD0_pos hD0_quad hD0_aa
        ⟨g, hg, hdg, fun g' hg' hdg' => by_contra fun hne => hSecond ⟨g', hg', hne, hdg'⟩⟩
      omega
  · have hD0_clean : ∀ g < D0.size, (gateAt D0 g).op = GateOp.and →
        ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
          (D0.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false := by
      intro g hg hop Q hQ
      cases hv : (D0.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false
      · rfl
      · exact False.elim (hHasDirty ⟨g, hg, hg, hop, Q, hQ, hv⟩)
    have orSets_len : ∀ (n : ℕ) (C : Circuit), (orSets n C).length = C.gates.length := by
      intro n C; unfold orSets orStep; rw [foldl_len]; simp
    have orSets_ge : ∀ (n : ℕ) (C : Circuit) {j : ℕ}, C.gates.length ≤ j → (orSets n C).getD j [] = [] := by
      intro n C j hj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_len]; exact hj)]; rfl
    have orSets_lt_or : ∀ (n : ℕ) (C : Circuit) {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.or →
        (orSets n C).getD j [] = j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (orSets n C).getD (w - n) []) := by
      intro n C j hj hop
      unfold orSets orStep
      have h := foldl_getD_gate (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap (fun w => cs.getD (w - n) []) else []))
        C.gates [] [] j hj ⟨GateOp.or, []⟩
      simp only [List.length_nil, Nat.zero_add] at h
      rw [h]
      set pre := (C.gates.take j).foldl (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap (fun w => cs.getD (w - n) []) else [])]) []
      have hprelen : pre.length = j := by rw [foldl_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      change pre.length :: (if (gateAt C j).op = GateOp.or then
        ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap (fun w => pre.getD (w - n) []) else []) = _
      rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
      congr 1
      apply List.flatMap_congr
      intro w hw
      rw [List.mem_filter, decide_eq_true_eq] at hw
      exact foldl_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) (by simp; omega)
    have orSets_lt_not_or : ∀ (n : ℕ) (C : Circuit) {j : ℕ}, j < C.gates.length → (gateAt C j).op ≠ GateOp.or →
        (orSets n C).getD j [] = [j] := by
      intro n C j hj hop
      unfold orSets orStep
      have h := foldl_getD_gate (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap (fun w => cs.getD (w - n) []) else []))
        C.gates [] [] j hj ⟨GateOp.or, []⟩
      simp only [List.length_nil, Nat.zero_add] at h
      rw [h]
      set pre := (C.gates.take j).foldl (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap (fun w => cs.getD (w - n) []) else [])]) []
      have hprelen : pre.length = j := by rw [foldl_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      change pre.length :: (if (gateAt C j).op = GateOp.or then
        ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap (fun w => pre.getD (w - n) []) else []) = [j]
      rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]
    have orReaches_iff : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ w g : ℕ,
        OrReaches n C w g ↔ ∃ j < C.gates.length, w = n + j ∧
          (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ u ∈ (gateAt C j).inputs, OrReaches n C u g)) := by
      intro n C hRB w g
      constructor
      · rintro ⟨hnw, hmem⟩
        have hlt : w - n < C.gates.length := by
          by_contra hge; push Not at hge; rw [orSets_ge n C hge] at hmem; simp at hmem
        refine ⟨w - n, hlt, by omega, ?_⟩
        by_cases hop : (gateAt C (w - n)).op = GateOp.or
        · rw [orSets_lt_or n C hlt hop, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inl rfl
          · right
            rw [List.mem_flatMap] at hmem
            rcases hmem with ⟨u, hu, hgu⟩
            rw [List.mem_filter, decide_eq_true_eq] at hu
            exact ⟨hop, u, hu.1, hu.2.1, hgu⟩
        · rw [orSets_lt_not_or n C hlt hop, List.mem_singleton] at hmem; exact Or.inl hmem
      · rintro ⟨j, hj, rfl, hcase⟩
        refine ⟨Nat.le_add_right n j, ?_⟩
        rw [Nat.add_sub_cancel_left]
        rcases hcase with rfl | ⟨hop, u, hu, hnu, hgu⟩
        · by_cases hop : (gateAt C g).op = GateOp.or
          · rw [orSets_lt_or n C hj hop]; exact List.mem_cons_self
          · rw [orSets_lt_not_or n C hj hop]; exact List.mem_singleton_self g
        · rw [orSets_lt_or n C hj hop, List.mem_cons]; right; rw [List.mem_flatMap]
          refine ⟨u, ?_, hgu⟩; rw [List.mem_filter, decide_eq_true_eq]; exact ⟨hu, hnu, hRB j hj u hu⟩
    have orReaches_self : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ {j : ℕ}, j < C.gates.length → OrReaches n C (n + j) j := by
      intro n C hRB j hj
      exact (orReaches_iff hRB _ _).mpr ⟨j, hj, rfl, Or.inl rfl⟩
    have orReaches_le : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
      intro n C hRB w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro g hwg
        rw [orReaches_iff hRB] at hwg
        rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, u, hu, hug⟩⟩
        · exact ⟨le_rfl, hj⟩
        · have hult := hRB j hj u hu
          have hrec := ih u hult g hug
          exact ⟨by have := hrec.1; omega, hrec.2⟩
    have orReaches_trans : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C →
        ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
      intro n C hRB w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro g h hwg hgh
        rw [orReaches_iff hRB] at hwg
        rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
        · exact hgh
        · exact (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, ih _ (hRB j hj u hu) g h hug hgh⟩⟩
    have orReaches_parent : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C →
        ∀ w g : ℕ, OrReaches n C w g → w = n + g ∨
          ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧ n + g ∈ (gateAt C h).inputs := by
      intro n C hRB w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro g hwg
        rw [orReaches_iff hRB] at hwg
        rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
        · exact Or.inl rfl
        · right
          rcases ih _ (hRB j hj u hu) g hug with rfl | ⟨h, hh, hhop, hreach, hmem⟩
          · exact ⟨j, hj, hop, orReaches_self hRB hj, hu⟩
          · exact ⟨h, hh, hhop, (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hreach⟩⟩, hmem⟩
    have wires_true_of_orReaches : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C →
        ∀ (inp : List Bool), inp.length = n → ∀ w g : ℕ, OrReaches n C w g →
        (C.wires inp).getD (n + g) false = true → (C.wires inp).getD w false = true := by
      intro n C hRB inp hlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro g hwg hg
        rw [orReaches_iff hRB] at hwg
        rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
        · exact hg
        · have hut := ih u (hRB j hj u hu) g hug hg
          rw [wires_gate hRB inp hlen hj, hop]
          simp only [eval_or, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
          exact ⟨u, hu, hut⟩
    have cones_len : ∀ (n : ℕ) (C : Circuit), (cones n C).length = C.gates.length := by
      intro n C; unfold cones coneStep; rw [foldl_len]; simp
    have cones_ge : ∀ (n : ℕ) (C : Circuit) {j : ℕ}, C.gates.length ≤ j → (cones n C).getD j [] = [] := by
      intro n C j hj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_len]; exact hj)]; rfl
    have cones_lt : ∀ (n : ℕ) (C : Circuit) {j : ℕ}, j < C.gates.length →
        (cones n C).getD j [] = ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
      intro n C j hj
      unfold cones coneStep
      have h := foldl_getD_gate (fun cs (g : Gate) =>
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap (fun w => (w - n) :: cs.getD (w - n) []))
        C.gates [] [] j hj ⟨GateOp.or, []⟩
      simp only [List.length_nil, Nat.zero_add] at h
      rw [h]
      set pre := (C.gates.take j).foldl (fun cs (g : Gate) => cs ++
        [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap (fun w => (w - n) :: cs.getD (w - n) [])]) []
      have hprelen : pre.length = j := by rw [foldl_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      change ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap (fun w => (w - n) :: pre.getD (w - n) []) = _
      rw [hprelen]
      apply List.flatMap_congr
      intro w hw
      rw [List.mem_filter, decide_eq_true_eq] at hw
      congr 1
      exact foldl_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) (by simp; omega)
    have inCone_iff : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ i j : ℕ,
        InCone n C i j ↔ j < C.gates.length ∧ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (i = w - n ∨ InCone n C i (w - n)) := by
      intro n C hRB i j
      unfold InCone
      constructor
      · intro hmem
        have hj : j < C.gates.length := by by_contra hge; push Not at hge; rw [cones_ge n C hge] at hmem; simp at hmem
        refine ⟨hj, ?_⟩
        rw [cones_lt n C hj, List.mem_flatMap] at hmem
        rcases hmem with ⟨w, hw, hiw⟩
        rw [List.mem_filter, decide_eq_true_eq] at hw
        rw [List.mem_cons] at hiw
        exact ⟨w, hw.1, hw.2.1, hiw⟩
      · rintro ⟨hj, w, hw, hnw, hiw⟩
        rw [cones_lt n C hj, List.mem_flatMap]
        refine ⟨w, ?_, ?_⟩
        · rw [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, hnw, hRB j hj w hw⟩
        · rw [List.mem_cons]; exact hiw
    have inCone_lt : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ j i : ℕ, InCone n C i j → i < j ∧ j < C.gates.length := by
      intro n C hRB j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro i hij
        rw [inCone_iff hRB] at hij
        rcases hij with ⟨hj, w, hw, hnw, rfl | hrec⟩
        · have := hRB j hj w hw; exact ⟨by omega, hj⟩
        · have := hRB j hj w hw; have hsub := ih (w - n) (by omega) i hrec; exact ⟨by omega, hj⟩
    have inCone_trans : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ c a b : ℕ, InCone n C a b → InCone n C b c → InCone n C a c := by
      intro n C hRB c
      induction c using Nat.strong_induction_on with
      | ind c ih =>
        intro a b hab hbc
        rw [inCone_iff hRB] at hbc
        rcases hbc with ⟨hc, w, hw, hnw, rfl | hrec⟩
        · exact (inCone_iff hRB a c).mpr ⟨hc, w, hw, hnw, Or.inr hab⟩
        · have := hRB c hc w hw; exact (inCone_iff hRB a c).mpr ⟨hc, w, hw, hnw, Or.inr (ih (w - n) (by omega) a b hab hrec)⟩
    have inCone_has_reader : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ j i : ℕ, InCone n C i j →
        ∃ k < C.gates.length, i < k ∧ n + i ∈ (gateAt C k).inputs := by
      intro n C hRB j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro i hij
        rw [inCone_iff hRB] at hij
        rcases hij with ⟨hj, w, hw, hnw, hEq | hrec⟩
        · have hwi : n + i = w := by omega
          have hwlt := hRB j hj w hw
          exact ⟨j, hj, by omega, hwi ▸ hw⟩
        · have hwlt := hRB j hj w hw
          exact ih (w - n) (by omega) i hrec
    let killG (w : ℕ) (g : Gate) : Gate :=
      if g.op = GateOp.and ∧ w ∈ g.inputs then ⟨GateOp.or, []⟩
      else ⟨g.op, g.inputs.filter (· ≠ w)⟩
    let shiftW (c w : ℕ) : ℕ := if c < w then w - 1 else w
    let aliasW (c u w : ℕ) : ℕ := if w = c then u else if c < w then w - 1 else w
    let origIdx (k m : ℕ) : ℕ := if m < k then m else m + 1
    have topform_step : ∀ D : Circuit, Monotone2 D → ReadsBack 26 D → D.output < 26 + D.size →
        RightOnIncidentPairs singerLines3 D →
        (∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q → D.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
        (∀ g < D.size, (gateAt D g).op = GateOp.and → ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
          (D.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false) →
        0 < andPairs 26 D →
        ∃ E : Circuit, E.size ≤ D.size ∧ Monotone2 E ∧ ReadsBack 26 E ∧ E.output < 26 + E.size ∧
          RightOnIncidentPairs singerLines3 E ∧
          (∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q → E.eval (incidenceInput Q (missLines singerLines3 Q)) = false) ∧
          (∀ g < E.size, (gateAt E g).op = GateOp.and → ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
            (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false) ∧
          andPairs 26 E < andPairs 26 D := by
      intro D hM hRB hOut hPos hQuad hClean hAP
      have hOut' : D.output < 26 + D.gates.length := hOut
      unfold andPairs at hAP
      obtain ⟨⟨i0, j0⟩, hij0⟩ := Finset.card_pos.mp hAP
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hij0
      obtain ⟨⟨hi0, hj0⟩, hi0op, hj0op, hij0cone⟩ := hij0
      obtain ⟨k, hk, hik, hkread⟩ := inCone_has_reader hRB j0 i0 hij0cone
      let D1 : Circuit := ⟨D.gates.map (killG (26 + i0)), D.output⟩
      have hD1_len : D1.gates.length = D.gates.length := by simp [D1]
      have hD1_gate : ∀ m < D.gates.length, gateAt D1 m = killG (26 + i0) (gateAt D m) := by
        intro m hm
        have hm1 : m < D1.gates.length := by rw [hD1_len]; exact hm
        show D1.gates.getD m ⟨GateOp.or, []⟩ = killG (26 + i0) (D.gates.getD m ⟨GateOp.or, []⟩)
        rw [List.getD_eq_getElem _ _ hm1, List.getD_eq_getElem _ _ hm]
        simp [D1]
      have hD1_mono : Monotone2 D1 := by
        intro g hg
        simp only [D1, List.mem_map] at hg
        rcases hg with ⟨g0, hg0, rfl⟩
        dsimp only [killG]
        split_ifs
        · simp
        · refine ⟨(hM g0 hg0).1, le_trans (List.length_filter_le _ _) (hM g0 hg0).2⟩
      have hD1_rb : ReadsBack 26 D1 := by
        intro m hm u hu
        have hm0 : m < D.gates.length := by rw [← hD1_len]; exact hm
        rw [hD1_gate m hm0] at hu
        dsimp only [killG] at hu
        split_ifs at hu
        · simp at hu
        · rw [List.mem_filter] at hu
          exact hRB m hm0 u hu.1
      have hD1_no_i0 : ∀ m < D1.gates.length, 26 + i0 ∉ (gateAt D1 m).inputs := by
        intro m hm hmem
        have hm0 : m < D.gates.length := by rw [← hD1_len]; exact hm
        rw [hD1_gate m hm0] at hmem
        dsimp only [killG] at hmem
        split_ifs at hmem
        · simp at hmem
        · simp [List.mem_filter] at hmem
      have hD1_and_imp : ∀ m < D.gates.length, (gateAt D1 m).op = GateOp.and →
          (gateAt D m).op = GateOp.and ∧ (gateAt D1 m).inputs = (gateAt D m).inputs := by
        intro m hm hop
        rw [hD1_gate m hm] at hop ⊢
        dsimp only [killG] at hop ⊢
        by_cases h : (gateAt D m).op = GateOp.and ∧ 26 + i0 ∈ (gateAt D m).inputs
        · rw [if_pos h] at hop; cases hop
        · rw [if_neg h] at hop ⊢
          have hni : 26 + i0 ∉ (gateAt D m).inputs := fun hmem => h ⟨hop, hmem⟩
          refine ⟨hop, ?_⟩
          apply List.filter_eq_self.mpr
          intro u hu
          simp only [decide_eq_true_eq]
          intro heq; subst heq; exact hni hu
      have hD1_inp_sub : ∀ m < D.gates.length, ∀ u ∈ (gateAt D1 m).inputs, u ∈ (gateAt D m).inputs := by
        intro m hm u hu
        rw [hD1_gate m hm] at hu
        dsimp only [killG] at hu
        split_ifs at hu
        · simp at hu
        · exact (List.mem_filter.mp hu).1
      have hD1_le : ∀ (inp : List Bool), inp.length = 26 → ∀ w < 26 + D.gates.length,
          (D1.wires inp).getD w false = true → (D.wires inp).getD w false = true := by
        intro inp hlen w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw h1
          by_cases hlt : w < 26
          · rwa [wires_in D1 inp (by omega), ← wires_in D inp (by omega)] at h1
          · set m := w - 26
            have hwm : w = 26 + m := by omega
            have hm : m < D.gates.length := by omega
            rw [hwm] at h1 ⊢
            rw [wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm)] at h1
            rw [wires_gate hRB inp hlen hm]
            rw [hD1_gate m hm] at h1
            dsimp only [killG] at h1
            split_ifs at h1 with h
            · rw [eval_or] at h1; simp at h1
            · rcases gateOp_ao hM hm with hop | hop
              · rw [hop] at h1 ⊢
                have hni : 26 + i0 ∉ (gateAt D m).inputs := fun hmem => h ⟨hop, hmem⟩
                have hfilt : (gateAt D m).inputs.filter (· ≠ 26 + i0) = (gateAt D m).inputs :=
                  List.filter_eq_self.mpr fun u hu => by simp only [decide_eq_true_eq]; intro heq; subst heq; exact hni hu
                rw [hfilt] at h1
                simp only [eval_and, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h1 ⊢
                intro u hu
                have hult := hRB m hm u hu
                exact ih u (by omega) (by omega) (h1 u hu)
              · rw [hop] at h1 ⊢
                simp only [eval_or, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at h1 ⊢
                rcases h1 with ⟨u, hu, hut⟩
                rw [List.mem_filter] at hu
                have hult := hRB m hm u hu.1
                exact ⟨u, hu.1, ih u (by omega) (by omega) hut⟩
      have hD1_eq_prefix : ∀ (inp : List Bool), inp.length = 26 → ∀ w ≤ 26 + i0,
          (D1.wires inp).getD w false = (D.wires inp).getD w false := by
        intro inp hlen w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hlt : w < 26
          · rw [wires_in D1 inp (by omega), wires_in D inp (by omega)]
          · set m := w - 26
            have hwm : w = 26 + m := by omega
            have hm : m < D.gates.length := by omega
            rw [hwm, wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm), wires_gate hRB inp hlen hm, hD1_gate m hm]
            have hni : 26 + i0 ∉ (gateAt D m).inputs := fun hmem => by have := hRB m hm _ hmem; omega
            have hkg : killG (26 + i0) (gateAt D m) = gateAt D m := by
              dsimp only [killG]
              rw [if_neg (fun h => hni h.2)]
              cases hg : gateAt D m with
              | mk op inps =>
                simp only
                congr 1
                rw [hg] at hni
                exact List.filter_eq_self.mpr fun u hu => by simp only [decide_eq_true_eq]; intro heq; subst heq; exact hni hu
            rw [hkg]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hRB m hm u hu
            exact ih u (by omega) (by omega)
      have hD1_eq_when_false : ∀ (inp : List Bool), inp.length = 26 →
          (D.wires inp).getD (26 + i0) false = false →
          ∀ w < 26 + D.gates.length, (D1.wires inp).getD w false = (D.wires inp).getD w false := by
        intro inp hlen hfi w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hlt : w < 26
          · rw [wires_in D1 inp (by omega), wires_in D inp (by omega)]
          · set m := w - 26
            have hwm : w = 26 + m := by omega
            have hm : m < D.gates.length := by omega
            rw [hwm, wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm), wires_gate hRB inp hlen hm, hD1_gate m hm]
            dsimp only [killG]
            split_ifs with h
            · rw [h.1]
              symm
              simp only [eval_or, eval_and, List.map_nil, List.any_nil, List.all_eq_false, List.mem_map, id_eq, Bool.not_eq_true]
              exact ⟨false, ⟨26 + i0, h.2, hfi⟩, rfl⟩
            · rcases gateOp_ao hM hm with hop | hop
              · rw [hop]
                have hni : 26 + i0 ∉ (gateAt D m).inputs := fun hmem => h ⟨hop, hmem⟩
                have hfilt : (gateAt D m).inputs.filter (· ≠ 26 + i0) = (gateAt D m).inputs :=
                  List.filter_eq_self.mpr fun u hu => by simp only [decide_eq_true_eq]; intro heq; subst heq; exact hni hu
                rw [hfilt]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult := hRB m hm u hu
                exact ih u (by omega) (by omega)
              · rw [hop]
                apply Bool.eq_iff_iff.mpr
                simp only [eval_or, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and, List.mem_filter, decide_eq_true_eq]
                constructor
                · rintro ⟨u, ⟨hu, _⟩, hut⟩
                  have hult := hRB m hm u hu
                  rw [ih u (by omega) (by omega)] at hut
                  exact ⟨u, hu, hut⟩
                · rintro ⟨u, hu, hut⟩
                  have hult := hRB m hm u hu
                  have hne : u ≠ 26 + i0 := fun heq => by rw [heq, hfi] at hut; cases hut
                  exact ⟨u, ⟨hu, hne⟩, by rw [ih u (by omega) (by omega)]; exact hut⟩
      have hk_d1 : (gateAt D1 k).op = GateOp.or ∧ (gateAt D1 k).inputs.length ≤ 1 := by
        rw [hD1_gate k hk]
        dsimp only [killG]
        split_ifs with h
        · simp
        · have hop : (gateAt D k).op = GateOp.or := (gateOp_ao hM hk).resolve_left fun ha => h ⟨ha, hkread⟩
          refine ⟨hop, ?_⟩
          have hlen2 := gate_len_le hM hk
          have hlt_len : ((gateAt D k).inputs.filter (· ≠ 26 + i0)).length < (gateAt D k).inputs.length := by
            have hle := List.length_filter_le (fun x => decide (x ≠ 26 + i0)) (gateAt D k).inputs
            by_contra hge
            have heq : ((gateAt D k).inputs.filter (· ≠ 26 + i0)).length = (gateAt D k).inputs.length := by omega
            have hall := List.length_filter_eq_length_iff.mp heq
            have := hall (26 + i0) hkread
            simp at this
          show ((gateAt D k).inputs.filter (· ≠ 26 + i0)).length ≤ 1
          omega
      rcases hk_inps : (gateAt D1 k).inputs with _ | ⟨u0, _ | _⟩
      · let D2 : Circuit := ⟨(List.range (D.gates.length - 1)).map fun m =>
          if m < k then gateAt D1 m
          else
            let g' := killG (26 + k) (gateAt D1 (m + 1))
            ⟨g'.op, g'.inputs.map (shiftW (26 + k))⟩,
          shiftW (26 + k) D.output⟩
        have hD2_len : D2.gates.length = D.gates.length - 1 := by simp [D2]
        have hD2_gate : ∀ m < D.gates.length - 1, gateAt D2 m =
            if m < k then gateAt D1 m
            else let g' := killG (26 + k) (gateAt D1 (m + 1)); ⟨g'.op, g'.inputs.map (shiftW (26 + k))⟩ := by
          intro m hm
          have hm2 : m < D2.gates.length := by rw [hD2_len]; exact hm
          show D2.gates.getD m ⟨GateOp.or, []⟩ = _
          rw [List.getD_eq_getElem _ _ hm2]; simp [D2]
        have hD2_mono : Monotone2 D2 := by
          intro g hg
          simp only [D2, List.mem_map, List.mem_range] at hg
          rcases hg with ⟨m, hm, rfl⟩
          split_ifs with hmk
          · exact hD1_mono _ (gateAt_mem (by rw [hD1_len]; omega))
          · dsimp only [killG]
            split_ifs
            · simp
            · refine ⟨(hD1_mono _ (gateAt_mem (by rw [hD1_len]; omega))).1, ?_⟩
              rw [List.length_map]
              exact le_trans (List.length_filter_le _ _) (hD1_mono _ (gateAt_mem (by rw [hD1_len]; omega))).2
        have hD2_rb : ReadsBack 26 D2 := by
          intro m hm w hw
          have hm' : m < D.gates.length - 1 := by rw [← hD2_len]; exact hm
          rw [hD2_gate m hm'] at hw
          split_ifs at hw with hmk
          · exact hD1_rb m (by rw [hD1_len]; omega) w hw
          · simp only [List.mem_map] at hw
            rcases hw with ⟨v, hv, rfl⟩
            dsimp only [killG] at hv
            split_ifs at hv
            · simp at hv
            · rw [List.mem_filter, decide_eq_true_eq] at hv
              have hvlt := hD1_rb (m + 1) (by rw [hD1_len]; omega) v hv.1
              dsimp only [shiftW]; split_ifs <;> omega
        have hD2_no_i0 : ∀ m < D2.gates.length, 26 + i0 ∉ (gateAt D2 m).inputs := by
          intro m hm hmem
          have hm' : m < D.gates.length - 1 := by rw [← hD2_len]; exact hm
          rw [hD2_gate m hm'] at hmem
          split_ifs at hmem with hmk
          · exact hD1_no_i0 m (by rw [hD1_len]; omega) hmem
          · simp only [List.mem_map] at hmem
            rcases hmem with ⟨v, hv, hveq⟩
            dsimp only [killG] at hv
            split_ifs at hv
            · simp at hv
            · rw [List.mem_filter, decide_eq_true_eq] at hv
              have hv_eq : v = 26 + i0 := by dsimp only [shiftW] at hveq; split_ifs at hveq <;> omega
              subst hv_eq
              exact hD1_no_i0 (m + 1) (by rw [hD1_len]; omega) hv.1
        have hD2_val : ∀ (inp : List Bool), inp.length = 26 → ∀ w < 26 + D.gates.length, w ≠ 26 + k →
            (D2.wires inp).getD (shiftW (26 + k) w) false = (D1.wires inp).getD w false := by
          intro inp hlen w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw hne
            by_cases hlt : w < 26
            · have hsw : shiftW (26 + k) w = w := by dsimp only [shiftW]; rw [if_neg (by omega)]
              rw [hsw, wires_in D2 inp (by omega), wires_in D1 inp (by omega)]
            · set m := w - 26
              have hwm : w = 26 + m := by omega
              have hm : m < D.gates.length := by omega
              have hmne : m ≠ k := by omega
              have hkval : (D1.wires inp).getD (26 + k) false = false := by
                rw [wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hk), hk_d1.1, hk_inps]; rfl
              by_cases hmk : m < k
              · have hsw : shiftW (26 + k) w = 26 + m := by dsimp only [shiftW]; rw [if_neg (by omega)]; exact hwm
                rw [hsw, hwm, wires_gate hD2_rb inp hlen (by rw [hD2_len]; omega), hD2_gate m (by omega), if_pos hmk,
                  wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm)]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult := hD1_rb m (by rw [hD1_len]; exact hm) u hu
                have hsu : shiftW (26 + k) u = u := by dsimp only [shiftW]; rw [if_neg (by omega)]
                simpa [hsu] using ih u (by omega) (by omega) (by omega)
              · have hm1 : m - 1 < D.gates.length - 1 := by omega
                have hmeq : m - 1 + 1 = m := by omega
                have hsw : shiftW (26 + k) w = 26 + (m - 1) := by dsimp only [shiftW]; rw [if_pos (by omega)]; omega
                rw [hsw, hwm, wires_gate hD2_rb inp hlen (by rw [hD2_len]; exact hm1), hD2_gate (m - 1) hm1,
                  if_neg (by omega), hmeq, wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm)]
                dsimp only [killG]
                split_ifs with h
                · rw [h.1]
                  symm
                  simp only [eval_or, eval_and, List.map_nil, List.any_nil, List.all_eq_false, List.mem_map, id_eq, Bool.not_eq_true]
                  exact ⟨false, ⟨26 + k, h.2, hkval⟩, rfl⟩
                · rcases gateOp_ao hD1_mono (by rw [hD1_len]; exact hm) with hop | hop
                  · rw [hop]
                    have hnk : 26 + k ∉ (gateAt D1 m).inputs := fun hmem => h ⟨hop, hmem⟩
                    have hfilt : (gateAt D1 m).inputs.filter (· ≠ 26 + k) = (gateAt D1 m).inputs :=
                      List.filter_eq_self.mpr fun u hu => by simp only [decide_eq_true_eq]; intro heq; subst heq; exact hnk hu
                    rw [hfilt, List.map_map]
                    congr 1
                    apply List.map_congr_left
                    intro u hu
                    have hult := hD1_rb m (by rw [hD1_len]; exact hm) u hu
                    have hune : u ≠ 26 + k := fun heq => hnk (heq ▸ hu)
                    exact ih u (by omega) (by omega) hune
                  · rw [hop]
                    apply Bool.eq_iff_iff.mpr
                    rw [List.map_map]
                    simp only [eval_or, List.any_eq_true, List.mem_map, Function.comp_apply, id_eq, exists_exists_and_eq_and, List.mem_filter, decide_eq_true_eq]
                    constructor
                    · rintro ⟨u, ⟨hu, hune⟩, hut⟩
                      have hult := hD1_rb m (by rw [hD1_len]; exact hm) u hu
                      rw [ih u (by omega) (by omega) hune] at hut
                      exact ⟨u, hu, hut⟩
                    · rintro ⟨u, hu, hut⟩
                      have hult := hD1_rb m (by rw [hD1_len]; exact hm) u hu
                      have hune : u ≠ 26 + k := fun heq => by rw [heq, hkval] at hut; cases hut
                      exact ⟨u, ⟨hu, hune⟩, by rw [ih u (by omega) (by omega) hune]; exact hut⟩
        have hD2_and_orig : ∀ m < D2.gates.length, (gateAt D2 m).op = GateOp.and → (gateAt D (origIdx k m)).op = GateOp.and := by
          intro m hm hop
          have hm' : m < D.gates.length - 1 := by rw [← hD2_len]; exact hm
          rw [hD2_gate m hm'] at hop
          dsimp only [origIdx]
          by_cases hmk : m < k
          · rw [if_pos hmk] at hop ⊢
            exact (hD1_and_imp m (by omega) hop).1
          · rw [if_neg hmk] at hop ⊢
            dsimp only [killG] at hop
            by_cases h : (gateAt D1 (m + 1)).op = GateOp.and ∧ 26 + k ∈ (gateAt D1 (m + 1)).inputs
            · rw [if_pos h] at hop; cases hop
            · rw [if_neg h] at hop
              exact (hD1_and_imp (m + 1) (by omega) hop).1
        have hD2_cone_orig : ∀ b < D2.gates.length, ∀ a, InCone 26 D2 a b → InCone 26 D (origIdx k a) (origIdx k b) := by
          intro b
          induction b using Nat.strong_induction_on with
          | ind b ih =>
            intro hb a hab
            have hb' : b < D.gates.length - 1 := by rw [← hD2_len]; exact hb
            rw [inCone_iff hD2_rb] at hab
            rcases hab with ⟨_, w, hw, hw26, hEq | hrec⟩
            · have hwlt := hD2_rb b hb w hw
              have hwin : 26 + origIdx k (w - 26) ∈ (gateAt D (origIdx k b)).inputs := by
                rw [hD2_gate b hb'] at hw
                dsimp only [origIdx]
                by_cases hbk : b < k
                · rw [if_pos hbk] at hw ⊢
                  have h1 := hD1_inp_sub b (by omega) w hw
                  have hwlt' : w - 26 < k := by omega
                  rw [if_pos hwlt']; convert h1 using 1; omega
                · rw [if_neg hbk] at hw ⊢
                  simp only [List.mem_map] at hw
                  rcases hw with ⟨v, hv, hveq⟩
                  dsimp only [killG] at hv
                  split_ifs at hv
                  · simp at hv
                  · rw [List.mem_filter, decide_eq_true_eq] at hv
                    have h1 := hD1_inp_sub (b + 1) (by omega) v hv.1
                    have hve : 26 + (if w - 26 < k then w - 26 else w - 26 + 1) = v := by
                      dsimp only [shiftW] at hveq; split_ifs at hveq ⊢ <;> omega
                    rwa [hve]
              rw [hEq]
              exact (inCone_iff hRB _ _).mpr ⟨by dsimp only [origIdx]; split_ifs <;> omega,
                26 + origIdx k (w - 26), hwin, by omega, Or.inl (by omega)⟩
            · have hwlt := hD2_rb b hb w hw
              have hsub := ih (w - 26) (by omega) (by omega) a hrec
              have hwin : 26 + origIdx k (w - 26) ∈ (gateAt D (origIdx k b)).inputs := by
                rw [hD2_gate b hb'] at hw
                dsimp only [origIdx]
                by_cases hbk : b < k
                · rw [if_pos hbk] at hw ⊢
                  have h1 := hD1_inp_sub b (by omega) w hw
                  have hwlt' : w - 26 < k := by omega
                  rw [if_pos hwlt']; convert h1 using 1; omega
                · rw [if_neg hbk] at hw ⊢
                  simp only [List.mem_map] at hw
                  rcases hw with ⟨v, hv, hveq⟩
                  dsimp only [killG] at hv
                  split_ifs at hv
                  · simp at hv
                  · rw [List.mem_filter, decide_eq_true_eq] at hv
                    have h1 := hD1_inp_sub (b + 1) (by omega) v hv.1
                    have hve : 26 + (if w - 26 < k then w - 26 else w - 26 + 1) = v := by
                      dsimp only [shiftW] at hveq; split_ifs at hveq ⊢ <;> omega
                    rwa [hve]
              exact (inCone_iff hRB _ _).mpr ⟨by dsimp only [origIdx]; split_ifs <;> omega,
                26 + origIdx k (w - 26), hwin, by omega, Or.inr (by rwa [Nat.add_sub_cancel_left])⟩
        have hD2_no_cone_i0 : ∀ b, ¬ InCone 26 D2 i0 b := by
          intro b
          induction b using Nat.strong_induction_on with
          | ind b ih =>
            intro hc
            rw [inCone_iff hD2_rb] at hc
            rcases hc with ⟨hb, w, hw, hw26, hEq | hrec⟩
            · have : w = 26 + i0 := by omega
              subst this; exact hD2_no_i0 b hb hw
            · have hwlt := hD2_rb b hb w hw
              exact ih (w - 26) (by omega) hrec
        have hD2_ap_lt : andPairs 26 D2 < andPairs 26 D := by
          unfold andPairs
          set S2 := (Finset.range D2.gates.length ×ˢ Finset.range D2.gates.length).filter fun p =>
            (gateAt D2 p.1).op = GateOp.and ∧ (gateAt D2 p.2).op = GateOp.and ∧ InCone 26 D2 p.1 p.2
          set S0 := (Finset.range D.gates.length ×ˢ Finset.range D.gates.length).filter fun p =>
            (gateAt D p.1).op = GateOp.and ∧ (gateAt D p.2).op = GateOp.and ∧ InCone 26 D p.1 p.2
          let φ : ℕ × ℕ → ℕ × ℕ := fun p => (origIdx k p.1, origIdx k p.2)
          have hφ_inj : Function.Injective φ := by
            rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
            simp only [φ, Prod.mk.injEq, origIdx] at h
            apply Prod.ext <;> split_ifs at h <;> omega
          have hsub : S2.image φ ⊆ S0 := by
            intro q hq
            rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
            simp only [S2, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
            simp only [S0, φ, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            refine ⟨⟨by dsimp only [origIdx]; split_ifs <;> omega, by dsimp only [origIdx]; split_ifs <;> omega⟩,
              hD2_and_orig a hab.1.1 hab.2.1, hD2_and_orig b hab.1.2 hab.2.2.1,
              hD2_cone_orig b hab.1.2 a hab.2.2.2⟩
          have hmem0 : (i0, j0) ∈ S0 := by
            simp only [S0, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨hi0, hj0⟩, hi0op, hj0op, hij0cone⟩
          have hnotmem : (i0, j0) ∉ S2.image φ := by
            intro h
            rcases Finset.mem_image.mp h with ⟨⟨a, b⟩, hab, heq⟩
            simp only [S2, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
            simp only [φ, Prod.mk.injEq] at heq
            have hai : a = i0 := by dsimp only [origIdx] at heq; split_ifs at heq <;> omega
            subst hai
            exact hD2_no_cone_i0 b hab.2.2.2
          have hss : S2.image φ ⊂ S0 := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hnotmem (h ▸ hmem0)⟩
          rw [← Finset.card_image_of_injective S2 hφ_inj]
          exact Finset.card_lt_card hss
        by_cases houtk : D.output = 26 + k
        · let E : Circuit := ⟨D2.gates, 26 + i0⟩
          have hE_clean : ∀ g < E.size, (gateAt E g).op = GateOp.and → ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
              (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false := by
            intro g hg hop Q hQ
            have hg2 : g < D2.gates.length := hg
            cases hv : (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false
            · rfl
            · exfalso
              have hsw : shiftW (26 + k) (26 + origIdx k g) = 26 + g := by
                dsimp only [shiftW, origIdx]; split_ifs <;> omega
              have hv2 : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (shiftW (26 + k) (26 + origIdx k g)) false = true := by
                rw [hsw]; exact hv
              rw [hD2_val _ (hinc_len _ _) _ (by dsimp only [origIdx]; split_ifs <;> omega)
                (by dsimp only [origIdx]; split_ifs <;> omega)] at hv2
              have hvD := hD1_le _ (hinc_len _ _) _ (by dsimp only [origIdx]; split_ifs <;> omega) hv2
              have hcl := hClean (origIdx k g) (by show origIdx k g < D.gates.length; dsimp only [origIdx]; split_ifs <;> omega) (hD2_and_orig g hg2 hop) Q hQ
              rw [hvD] at hcl; cases hcl
          refine ⟨E, by show D2.gates.length ≤ D.gates.length; rw [hD2_len]; omega,
            hD2_mono, hD2_rb, by show 26 + i0 < 26 + D2.gates.length; rw [hD2_len]; omega,
            ?_, ?_, hE_clean, hD2_ap_lt⟩
          · intro l p hp
            have hsw : shiftW (26 + k) (26 + i0) = 26 + i0 := by dsimp only [shiftW]; rw [if_neg (by omega)]
            show (D2.wires (incidenceInput {p} {l})).getD (26 + i0) false = true
            rw [← hsw, hD2_val _ (hinc_len _ _) (26 + i0) (by omega) (by omega),
              hD1_eq_prefix _ (hinc_len _ _) (26 + i0) le_rfl]
            by_contra hf
            have hfi : (D.wires (incidenceInput {p} {l})).getD (26 + i0) false = false := by
              cases h : (D.wires (incidenceInput {p} {l})).getD (26 + i0) false
              · rfl
              · exact absurd h hf
            have hkp := hD1_eq_when_false _ (hinc_len _ _) hfi (26 + k) (by omega)
            have hkfalse : (D1.wires (incidenceInput {p} {l})).getD (26 + k) false = false := by
              rw [wires_gate hD1_rb _ (hinc_len _ _) (by rw [hD1_len]; exact hk), hk_d1.1, hk_inps]; rfl
            have hdt : (D.wires (incidenceInput {p} {l})).getD (26 + k) false = true := by
              rw [← houtk]; exact hPos l p hp
            rw [hkfalse, hdt] at hkp; cases hkp
          · intro Q hQ
            have hsw : shiftW (26 + k) (26 + i0) = 26 + i0 := by dsimp only [shiftW]; rw [if_neg (by omega)]
            show (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + i0) false = false
            rw [← hsw, hD2_val _ (hinc_len _ _) (26 + i0) (by omega) (by omega),
              hD1_eq_prefix _ (hinc_len _ _) (26 + i0) le_rfl]
            exact hClean i0 hi0 hi0op Q hQ
        · let o2 := shiftW (26 + k) D.output
          have ho2_lt : o2 < 26 + D2.gates.length := by
            rw [hD2_len]; dsimp only [o2, shiftW]; split_ifs <;> omega
          let E : Circuit := ⟨D2.gates ++ [⟨GateOp.or, [o2, 26 + i0]⟩], 26 + D2.gates.length⟩
          have hE_len : E.gates.length = D.gates.length := by simp [E, hD2_len]; omega
          have hE_gate_lt : ∀ m < D2.gates.length, gateAt E m = gateAt D2 m := by
            intro m hm
            unfold gateAt; dsimp only [E]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
          have hE_gate_last : gateAt E D2.gates.length = ⟨GateOp.or, [o2, 26 + i0]⟩ := by
            unfold gateAt; dsimp only [E]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
          have hE_mono : Monotone2 E := by
            intro g hg; simp only [E, List.mem_append, List.mem_singleton] at hg
            rcases hg with hg | rfl
            · exact hD2_mono g hg
            · simp
          have hE_rb : ReadsBack 26 E := by
            intro m hm u hu
            have hm' : m < D2.gates.length + 1 := by simpa [E] using hm
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | rfl
            · rw [hE_gate_lt m hlt] at hu; exact hD2_rb m hlt u hu
            · rw [hE_gate_last] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact ho2_lt
              · rw [hD2_len]; omega
          have hE_wires : ∀ inp : List Bool, E.wires inp =
              D2.wires inp ++ [(D2.wires inp).getD o2 false || (D2.wires inp).getD (26 + i0) false] := by
            intro inp
            have e : E.wires inp = D2.wires inp ++ [([o2, 26 + i0].map fun u => (D2.wires inp).getD u false).any id] := by
              show List.foldl _ inp (D2.gates ++ [⟨GateOp.or, [o2, 26 + i0]⟩]) = _; rw [List.foldl_append]; rfl
            rw [e, List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil, id_eq, id_eq, Bool.or_false]
          have hE_eval : ∀ inp : List Bool, inp.length = 26 →
              E.eval inp = ((D2.wires inp).getD o2 false || (D2.wires inp).getD (26 + i0) false) := by
            intro inp hlen
            show (E.wires inp).getD (26 + D2.gates.length) false = _
            rw [hE_wires, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [wires_len, hlen])]
            simp [wires_len, hlen]
          have hE_cone_lt : ∀ m < D2.gates.length, ∀ a, InCone 26 E a m → InCone 26 D2 a m := by
            intro m
            induction m using Nat.strong_induction_on with
            | ind m ih =>
              intro hm a ham
              rw [inCone_iff hE_rb] at ham
              rcases ham with ⟨_, w, hw, hw26, hEq | hrec⟩
              · rw [hE_gate_lt m hm] at hw
                exact (inCone_iff hD2_rb a m).mpr ⟨hm, w, hw, hw26, Or.inl hEq⟩
              · rw [hE_gate_lt m hm] at hw
                have hwlt := hD2_rb m hm w hw
                exact (inCone_iff hD2_rb a m).mpr ⟨hm, w, hw, hw26, Or.inr (ih (w - 26) (by omega) (by omega) a hrec)⟩
          have hE_ap : andPairs 26 E ≤ andPairs 26 D2 := by
            unfold andPairs
            apply Finset.card_le_card
            intro p hab; rcases p with ⟨a, b⟩
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab ⊢
            have ha2 : a < D2.gates.length := by
              by_contra hge
              have ha1 : a < D2.gates.length + 1 := by simpa [E] using hab.1.1
              have hle : a = D2.gates.length := by omega
              subst hle; rw [hE_gate_last] at hab; cases hab.2.1
            have hb2 : b < D2.gates.length := by
              by_contra hge
              have hb1 : b < D2.gates.length + 1 := by simpa [E] using hab.1.2
              have hle : b = D2.gates.length := by omega
              subst hle; rw [hE_gate_last] at hab; cases hab.2.2.1
            rw [hE_gate_lt a ha2, hE_gate_lt b hb2] at hab
            exact ⟨⟨ha2, hb2⟩, hab.2.1, hab.2.2.1, hE_cone_lt b hb2 a hab.2.2.2⟩
          have hE_clean : ∀ g < E.size, (gateAt E g).op = GateOp.and → ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
              (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false := by
            intro g hg hop Q hQ
            have hg1 : g < D2.gates.length + 1 := by have : g < E.gates.length := hg; simpa [E] using this
            have hg2 : g < D2.gates.length := by
              by_contra hge
              have hge' : g = D2.gates.length := by omega
              subst hge'; rw [hE_gate_last] at hop; cases hop
            rw [hE_gate_lt g hg2] at hop
            have hget : (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false =
                (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false := by
              rw [hE_wires, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (by rw [wires_len, hinc_len]; omega),
                ← List.getD_eq_getElem?_getD]
            rw [hget]
            cases hv : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false
            · rfl
            · exfalso
              have hsw : shiftW (26 + k) (26 + origIdx k g) = 26 + g := by dsimp only [shiftW, origIdx]; split_ifs <;> omega
              have hv2 : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (shiftW (26 + k) (26 + origIdx k g)) false = true := by
                rw [hsw]; exact hv
              rw [hD2_val _ (hinc_len _ _) _ (by dsimp only [origIdx]; split_ifs <;> omega)
                (by dsimp only [origIdx]; split_ifs <;> omega)] at hv2
              have hvD := hD1_le _ (hinc_len _ _) _ (by dsimp only [origIdx]; split_ifs <;> omega) hv2
              have hcl := hClean (origIdx k g) (by show origIdx k g < D.gates.length; dsimp only [origIdx]; split_ifs <;> omega) (hD2_and_orig g hg2 hop) Q hQ
              rw [hvD] at hcl; cases hcl
          refine ⟨E, by show E.gates.length ≤ D.gates.length; omega, hE_mono, hE_rb,
            by show 26 + D2.gates.length < 26 + E.gates.length; omega, ?_, ?_, hE_clean, lt_of_le_of_lt hE_ap hD2_ap_lt⟩
          · intro l p hp
            rw [hE_eval _ (hinc_len _ _)]
            have hswi : shiftW (26 + k) (26 + i0) = 26 + i0 := by dsimp only [shiftW]; rw [if_neg (by omega)]
            cases hvi : (D.wires (incidenceInput {p} {l})).getD (26 + i0) false
            · have h1 := hD2_val (incidenceInput {p} {l}) (hinc_len _ _) D.output hOut' houtk
              have h2 := hD1_eq_when_false (incidenceInput {p} {l}) (hinc_len _ _) hvi D.output hOut'
              have h3 : (D.wires (incidenceInput {p} {l})).getD D.output false = true := hPos l p hp
              dsimp only [o2]; rw [h1, h2, h3, Bool.true_or]
            · have h1 : (D2.wires (incidenceInput {p} {l})).getD (26 + i0) false = true := by
                rw [← hswi, hD2_val _ (hinc_len _ _) (26 + i0) (by omega) (by omega),
                  hD1_eq_prefix _ (hinc_len _ _) (26 + i0) le_rfl, hvi]
              rw [h1, Bool.or_true]
          · intro Q hQ
            rw [hE_eval _ (hinc_len _ _)]
            have hswi : shiftW (26 + k) (26 + i0) = 26 + i0 := by dsimp only [shiftW]; rw [if_neg (by omega)]
            have hfi : (D.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + i0) false = false :=
              hClean i0 hi0 hi0op Q hQ
            have h1 := hD2_val (incidenceInput Q (missLines singerLines3 Q)) (hinc_len _ _) D.output hOut' houtk
            have h2 := hD1_eq_when_false (incidenceInput Q (missLines singerLines3 Q)) (hinc_len _ _) hfi D.output hOut'
            have h3 : (D.wires (incidenceInput Q (missLines singerLines3 Q))).getD D.output false = false := hQuad Q hQ
            have h4 : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + i0) false = false := by
              rw [← hswi, hD2_val _ (hinc_len _ _) (26 + i0) (by omega) (by omega),
                hD1_eq_prefix _ (hinc_len _ _) (26 + i0) le_rfl, hfi]
            dsimp only [o2]; rw [h1, h2, h3, h4]; rfl
      · have hu0_mem : u0 ∈ (gateAt D1 k).inputs := by rw [hk_inps]; exact List.mem_singleton_self _
        have hu0_lt : u0 < 26 + k := hD1_rb k (by rw [hD1_len]; exact hk) u0 hu0_mem
        have hu0_ne_i0 : u0 ≠ 26 + i0 := fun h => hD1_no_i0 k (by rw [hD1_len]; exact hk) (h ▸ hu0_mem)
        have hu0_inD : u0 ∈ (gateAt D k).inputs := hD1_inp_sub k hk u0 hu0_mem
        let D2 : Circuit := ⟨(List.range (D.gates.length - 1)).map fun m =>
          if m < k then gateAt D1 m
          else ⟨(gateAt D1 (m + 1)).op, (gateAt D1 (m + 1)).inputs.map (aliasW (26 + k) u0)⟩,
          aliasW (26 + k) u0 D.output⟩
        have hD2_len : D2.gates.length = D.gates.length - 1 := by simp [D2]
        have hD2_gate : ∀ m < D.gates.length - 1, gateAt D2 m =
            if m < k then gateAt D1 m
            else ⟨(gateAt D1 (m + 1)).op, (gateAt D1 (m + 1)).inputs.map (aliasW (26 + k) u0)⟩ := by
          intro m hm
          have hm2 : m < D2.gates.length := by rw [hD2_len]; exact hm
          show D2.gates.getD m ⟨GateOp.or, []⟩ = _
          rw [List.getD_eq_getElem _ _ hm2]; simp [D2]
        have hD2_mono : Monotone2 D2 := by
          intro g hg
          simp only [D2, List.mem_map, List.mem_range] at hg
          rcases hg with ⟨m, hm, rfl⟩
          split_ifs with hmk
          · exact hD1_mono _ (gateAt_mem (by rw [hD1_len]; omega))
          · refine ⟨(hD1_mono _ (gateAt_mem (by rw [hD1_len]; omega))).1, ?_⟩
            rw [List.length_map]; exact (hD1_mono _ (gateAt_mem (by rw [hD1_len]; omega))).2
        have hD2_rb : ReadsBack 26 D2 := by
          intro m hm w hw
          have hm' : m < D.gates.length - 1 := by rw [← hD2_len]; exact hm
          rw [hD2_gate m hm'] at hw
          split_ifs at hw with hmk
          · exact hD1_rb m (by rw [hD1_len]; omega) w hw
          · simp only [List.mem_map] at hw
            rcases hw with ⟨v, hv, rfl⟩
            have hvlt := hD1_rb (m + 1) (by rw [hD1_len]; omega) v hv
            dsimp only [aliasW]; split_ifs <;> omega
        have hD2_no_i0 : ∀ m < D2.gates.length, 26 + i0 ∉ (gateAt D2 m).inputs := by
          intro m hm hmem
          have hm' : m < D.gates.length - 1 := by rw [← hD2_len]; exact hm
          rw [hD2_gate m hm'] at hmem
          split_ifs at hmem with hmk
          · exact hD1_no_i0 m (by rw [hD1_len]; omega) hmem
          · simp only [List.mem_map] at hmem
            rcases hmem with ⟨v, hv, hveq⟩
            dsimp only [aliasW] at hveq
            split_ifs at hveq with h1 h2
            · exact hu0_ne_i0 hveq
            · omega
            · subst hveq; exact hD1_no_i0 (m + 1) (by rw [hD1_len]; omega) hv
        have hD2_val : ∀ (inp : List Bool), inp.length = 26 → ∀ w < 26 + D.gates.length,
            (D2.wires inp).getD (aliasW (26 + k) u0 w) false = (D1.wires inp).getD w false := by
          intro inp hlen w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hlt : w < 26
            · have haw : aliasW (26 + k) u0 w = w := by dsimp only [aliasW]; rw [if_neg (by omega), if_neg (by omega)]
              rw [haw, wires_in D2 inp (by omega), wires_in D1 inp (by omega)]
            · set m := w - 26
              have hwm : w = 26 + m := by omega
              have hm : m < D.gates.length := by omega
              by_cases hmk : m < k
              · have haw : aliasW (26 + k) u0 w = 26 + m := by
                  dsimp only [aliasW]; rw [if_neg (by omega), if_neg (by omega)]; exact hwm
                rw [haw, hwm, wires_gate hD2_rb inp hlen (by rw [hD2_len]; omega), hD2_gate m (by omega), if_pos hmk,
                  wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm)]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult := hD1_rb m (by rw [hD1_len]; exact hm) u hu
                have hau : aliasW (26 + k) u0 u = u := by dsimp only [aliasW]; rw [if_neg (by omega), if_neg (by omega)]
                simpa [hau] using ih u (by omega) (by omega)
              · by_cases hmeq : m = k
                · rw [hmeq] at hwm
                  have haw : aliasW (26 + k) u0 w = u0 := by dsimp only [aliasW]; rw [if_pos hwm]
                  have hau0 : aliasW (26 + k) u0 u0 = u0 := by dsimp only [aliasW]; rw [if_neg (by omega), if_neg (by omega)]
                  rw [haw, hwm, wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hk), hk_d1.1, hk_inps]
                  simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  simpa [hau0] using ih u0 (by omega) (by omega)
                · have hm1 : m - 1 < D.gates.length - 1 := by omega
                  have hm1eq : m - 1 + 1 = m := by omega
                  have haw : aliasW (26 + k) u0 w = 26 + (m - 1) := by
                    dsimp only [aliasW]; rw [if_neg (by omega), if_pos (by omega)]; omega
                  rw [haw, hwm, wires_gate hD2_rb inp hlen (by rw [hD2_len]; exact hm1), hD2_gate (m - 1) hm1,
                    if_neg (by omega), hm1eq, wires_gate hD1_rb inp hlen (by rw [hD1_len]; exact hm), List.map_map]
                  congr 1
                  apply List.map_congr_left
                  intro u hu
                  have hult := hD1_rb m (by rw [hD1_len]; exact hm) u hu
                  exact ih u (by omega) (by omega)
        have hD2_and_orig : ∀ m < D2.gates.length, (gateAt D2 m).op = GateOp.and → (gateAt D (origIdx k m)).op = GateOp.and := by
          intro m hm hop
          have hm' : m < D.gates.length - 1 := by rw [← hD2_len]; exact hm
          rw [hD2_gate m hm'] at hop
          dsimp only [origIdx]
          split_ifs at hop ⊢ with hmk
          · exact (hD1_and_imp m (by omega) hop).1
          · exact (hD1_and_imp (m + 1) (by omega) hop).1
        have hD2_cone_orig : ∀ b < D2.gates.length, ∀ a, InCone 26 D2 a b → InCone 26 D (origIdx k a) (origIdx k b) := by
          intro b
          induction b using Nat.strong_induction_on with
          | ind b ih =>
            intro hb a hab
            have hb' : b < D.gates.length - 1 := by rw [← hD2_len]; exact hb
            rw [inCone_iff hD2_rb] at hab
            rcases hab with ⟨_, w, hw, hw26, hEq | hrec⟩
            · have hwlt := hD2_rb b hb w hw
              rw [hD2_gate b hb'] at hw
              split_ifs at hw with hbk
              · have h1 := hD1_inp_sub b (by omega) w hw
                have hwb : origIdx k b = b := by dsimp only [origIdx]; rw [if_pos hbk]
                have hwa : origIdx k a = w - 26 := by dsimp only [origIdx]; rw [hEq, if_pos (by omega)]
                rw [hwb, hwa]
                exact (inCone_iff hRB _ _).mpr ⟨by omega, w, h1, hw26, Or.inl rfl⟩
              · simp only [List.mem_map] at hw
                rcases hw with ⟨v, hv, hveq⟩
                have h1 := hD1_inp_sub (b + 1) (by omega) v hv
                have hwb : origIdx k b = b + 1 := by dsimp only [origIdx]; rw [if_neg hbk]
                rw [hwb]
                dsimp only [aliasW] at hveq
                split_ifs at hveq with hvk1 hvk2
                · subst hvk1; subst hveq
                  have hwa : origIdx k a = u0 - 26 := by dsimp only [origIdx]; rw [hEq, if_pos (by omega)]
                  rw [hwa]
                  have hcu : InCone 26 D (u0 - 26) k := (inCone_iff hRB _ _).mpr ⟨hk, u0, hu0_inD, hw26, Or.inl rfl⟩
                  exact (inCone_iff hRB _ _).mpr ⟨by omega, 26 + k, h1, by omega, Or.inr (by rwa [Nat.add_sub_cancel_left])⟩
                · have hwa : origIdx k a = v - 26 := by dsimp only [origIdx]; rw [hEq, if_neg (by omega)]; omega
                  rw [hwa]
                  exact (inCone_iff hRB _ _).mpr ⟨by omega, v, h1, by omega, Or.inl rfl⟩
                · have hwa : origIdx k a = v - 26 := by dsimp only [origIdx]; rw [hEq, ← hveq, if_pos (by omega)]
                  rw [hwa]
                  exact (inCone_iff hRB _ _).mpr ⟨by omega, v, h1, by omega, Or.inl rfl⟩
            · have hwlt := hD2_rb b hb w hw
              have hsub := ih (w - 26) (by omega) (by omega) a hrec
              rw [hD2_gate b hb'] at hw
              split_ifs at hw with hbk
              · have h1 := hD1_inp_sub b (by omega) w hw
                have hwb : origIdx k b = b := by dsimp only [origIdx]; rw [if_pos hbk]
                have hww : origIdx k (w - 26) = w - 26 := by dsimp only [origIdx]; rw [if_pos (by omega)]
                rw [hww] at hsub
                rw [hwb]
                exact (inCone_iff hRB _ _).mpr ⟨by omega, w, h1, hw26, Or.inr hsub⟩
              · simp only [List.mem_map] at hw
                rcases hw with ⟨v, hv, hveq⟩
                have h1 := hD1_inp_sub (b + 1) (by omega) v hv
                have hwb : origIdx k b = b + 1 := by dsimp only [origIdx]; rw [if_neg hbk]
                rw [hwb]
                dsimp only [aliasW] at hveq
                split_ifs at hveq with hvk1 hvk2
                · subst hvk1; subst hveq
                  have hww : origIdx k (u0 - 26) = u0 - 26 := by dsimp only [origIdx]; rw [if_pos (by omega)]
                  rw [hww] at hsub
                  have hck : InCone 26 D (origIdx k a) k := (inCone_iff hRB _ _).mpr ⟨hk, u0, hu0_inD, hw26, Or.inr hsub⟩
                  exact (inCone_iff hRB _ _).mpr ⟨by omega, 26 + k, h1, by omega, Or.inr (by rwa [Nat.add_sub_cancel_left])⟩
                · have hww : origIdx k (w - 26) = v - 26 := by dsimp only [origIdx]; rw [if_neg (by omega)]; omega
                  rw [hww] at hsub
                  exact (inCone_iff hRB _ _).mpr ⟨by omega, v, h1, by omega, Or.inr hsub⟩
                · have hww : origIdx k (w - 26) = v - 26 := by dsimp only [origIdx]; rw [← hveq, if_pos (by omega)]
                  rw [hww] at hsub
                  exact (inCone_iff hRB _ _).mpr ⟨by omega, v, h1, by omega, Or.inr hsub⟩
        have hD2_no_cone_i0 : ∀ b, ¬ InCone 26 D2 i0 b := by
          intro b
          induction b using Nat.strong_induction_on with
          | ind b ih =>
            intro hc
            rw [inCone_iff hD2_rb] at hc
            rcases hc with ⟨hb, w, hw, hw26, hEq | hrec⟩
            · have : w = 26 + i0 := by omega
              subst this; exact hD2_no_i0 b hb hw
            · have hwlt := hD2_rb b hb w hw; exact ih (w - 26) (by omega) hrec
        have hD2_ap_lt : andPairs 26 D2 < andPairs 26 D := by
          unfold andPairs
          set S2 := (Finset.range D2.gates.length ×ˢ Finset.range D2.gates.length).filter fun p =>
            (gateAt D2 p.1).op = GateOp.and ∧ (gateAt D2 p.2).op = GateOp.and ∧ InCone 26 D2 p.1 p.2
          set S0 := (Finset.range D.gates.length ×ˢ Finset.range D.gates.length).filter fun p =>
            (gateAt D p.1).op = GateOp.and ∧ (gateAt D p.2).op = GateOp.and ∧ InCone 26 D p.1 p.2
          let φ : ℕ × ℕ → ℕ × ℕ := fun p => (origIdx k p.1, origIdx k p.2)
          have hφ_inj : Function.Injective φ := by
            rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
            simp only [φ, Prod.mk.injEq, origIdx] at h
            apply Prod.ext <;> split_ifs at h <;> omega
          have hsub : S2.image φ ⊆ S0 := by
            intro q hq
            rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
            simp only [S2, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
            simp only [S0, φ, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            refine ⟨⟨by dsimp only [origIdx]; split_ifs <;> omega, by dsimp only [origIdx]; split_ifs <;> omega⟩,
              hD2_and_orig a hab.1.1 hab.2.1, hD2_and_orig b hab.1.2 hab.2.2.1,
              hD2_cone_orig b hab.1.2 a hab.2.2.2⟩
          have hmem0 : (i0, j0) ∈ S0 := by
            simp only [S0, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨hi0, hj0⟩, hi0op, hj0op, hij0cone⟩
          have hnotmem : (i0, j0) ∉ S2.image φ := by
            intro h
            rcases Finset.mem_image.mp h with ⟨⟨a, b⟩, hab, heq⟩
            simp only [S2, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
            simp only [φ, Prod.mk.injEq] at heq
            have hai : a = i0 := by dsimp only [origIdx] at heq; split_ifs at heq <;> omega
            subst hai
            exact hD2_no_cone_i0 b hab.2.2.2
          have hss : S2.image φ ⊂ S0 := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hnotmem (h ▸ hmem0)⟩
          rw [← Finset.card_image_of_injective S2 hφ_inj]
          exact Finset.card_lt_card hss
        let o2 := aliasW (26 + k) u0 D.output
        have ho2_lt : o2 < 26 + D2.gates.length := by
          rw [hD2_len]; dsimp only [o2, aliasW]; split_ifs <;> omega
        let E : Circuit := ⟨D2.gates ++ [⟨GateOp.or, [o2, 26 + i0]⟩], 26 + D2.gates.length⟩
        have hE_len : E.gates.length = D.gates.length := by simp [E, hD2_len]; omega
        have hE_gate_lt : ∀ m < D2.gates.length, gateAt E m = gateAt D2 m := by
          intro m hm
          unfold gateAt; dsimp only [E]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
        have hE_gate_last : gateAt E D2.gates.length = ⟨GateOp.or, [o2, 26 + i0]⟩ := by
          unfold gateAt; dsimp only [E]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
        have hE_mono : Monotone2 E := by
          intro g hg; simp only [E, List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · exact hD2_mono g hg
          · simp
        have hE_rb : ReadsBack 26 E := by
          intro m hm u hu
          have hm' : m < D2.gates.length + 1 := by simpa [E] using hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | rfl
          · rw [hE_gate_lt m hlt] at hu; exact hD2_rb m hlt u hu
          · rw [hE_gate_last] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact ho2_lt
            · rw [hD2_len]; omega
        have hE_wires : ∀ inp : List Bool, E.wires inp =
            D2.wires inp ++ [(D2.wires inp).getD o2 false || (D2.wires inp).getD (26 + i0) false] := by
          intro inp
          have e : E.wires inp = D2.wires inp ++ [([o2, 26 + i0].map fun u => (D2.wires inp).getD u false).any id] := by
            show List.foldl _ inp (D2.gates ++ [⟨GateOp.or, [o2, 26 + i0]⟩]) = _; rw [List.foldl_append]; rfl
          rw [e, List.map_cons, List.map_cons, List.map_nil, List.any_cons, List.any_cons, List.any_nil, id_eq, id_eq, Bool.or_false]
        have hE_eval : ∀ inp : List Bool, inp.length = 26 →
            E.eval inp = ((D2.wires inp).getD o2 false || (D2.wires inp).getD (26 + i0) false) := by
          intro inp hlen
          show (E.wires inp).getD (26 + D2.gates.length) false = _
          rw [hE_wires, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [wires_len, hlen])]
          simp [wires_len, hlen]
        have hE_cone_lt : ∀ m < D2.gates.length, ∀ a, InCone 26 E a m → InCone 26 D2 a m := by
          intro m
          induction m using Nat.strong_induction_on with
          | ind m ih =>
            intro hm a ham
            rw [inCone_iff hE_rb] at ham
            rcases ham with ⟨_, w, hw, hw26, hEq | hrec⟩
            · rw [hE_gate_lt m hm] at hw
              exact (inCone_iff hD2_rb a m).mpr ⟨hm, w, hw, hw26, Or.inl hEq⟩
            · rw [hE_gate_lt m hm] at hw
              have hwlt := hD2_rb m hm w hw
              exact (inCone_iff hD2_rb a m).mpr ⟨hm, w, hw, hw26, Or.inr (ih (w - 26) (by omega) (by omega) a hrec)⟩
        have hE_ap : andPairs 26 E ≤ andPairs 26 D2 := by
          unfold andPairs
          apply Finset.card_le_card
          intro p hab; rcases p with ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab ⊢
          have ha2 : a < D2.gates.length := by
            by_contra hge
            have ha1 : a < D2.gates.length + 1 := by simpa [E] using hab.1.1
            have hle : a = D2.gates.length := by omega
            subst hle; rw [hE_gate_last] at hab; cases hab.2.1
          have hb2 : b < D2.gates.length := by
            by_contra hge
            have hb1 : b < D2.gates.length + 1 := by simpa [E] using hab.1.2
            have hle : b = D2.gates.length := by omega
            subst hle; rw [hE_gate_last] at hab; cases hab.2.2.1
          rw [hE_gate_lt a ha2, hE_gate_lt b hb2] at hab
          exact ⟨⟨ha2, hb2⟩, hab.2.1, hab.2.2.1, hE_cone_lt b hb2 a hab.2.2.2⟩
        have hE_clean : ∀ g < E.size, (gateAt E g).op = GateOp.and → ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
            (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false := by
          intro g hg hop Q hQ
          have hg1 : g < D2.gates.length + 1 := by have : g < E.gates.length := hg; simpa [E] using this
          have hg2 : g < D2.gates.length := by
            by_contra hge
            have hge' : g = D2.gates.length := by omega
            subst hge'; rw [hE_gate_last] at hop; cases hop
          rw [hE_gate_lt g hg2] at hop
          have hget : (E.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false =
              (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false := by
            rw [hE_wires, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by rw [wires_len, hinc_len]; omega),
              ← List.getD_eq_getElem?_getD]
          rw [hget]
          cases hv : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false
          · rfl
          · exfalso
            have haw : aliasW (26 + k) u0 (26 + origIdx k g) = 26 + g := by dsimp only [aliasW, origIdx]; split_ifs <;> omega
            have hv2 : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (aliasW (26 + k) u0 (26 + origIdx k g)) false = true := by
              rw [haw]; exact hv
            rw [hD2_val _ (hinc_len _ _) _ (by dsimp only [origIdx]; split_ifs <;> omega)] at hv2
            have hvD := hD1_le _ (hinc_len _ _) _ (by dsimp only [origIdx]; split_ifs <;> omega) hv2
            have hcl := hClean (origIdx k g) (by show origIdx k g < D.gates.length; dsimp only [origIdx]; split_ifs <;> omega) (hD2_and_orig g hg2 hop) Q hQ
            rw [hvD] at hcl; cases hcl
        refine ⟨E, by show E.gates.length ≤ D.gates.length; omega, hE_mono, hE_rb,
          by show 26 + D2.gates.length < 26 + E.gates.length; omega, ?_, ?_, hE_clean, lt_of_le_of_lt hE_ap hD2_ap_lt⟩
        · intro l p hp
          rw [hE_eval _ (hinc_len _ _)]
          have hawi : aliasW (26 + k) u0 (26 + i0) = 26 + i0 := by dsimp only [aliasW]; rw [if_neg (by omega), if_neg (by omega)]
          cases hvi : (D.wires (incidenceInput {p} {l})).getD (26 + i0) false
          · have h1 := hD2_val (incidenceInput {p} {l}) (hinc_len _ _) D.output hOut'
            have h2 := hD1_eq_when_false (incidenceInput {p} {l}) (hinc_len _ _) hvi D.output hOut'
            have h3 : (D.wires (incidenceInput {p} {l})).getD D.output false = true := hPos l p hp
            dsimp only [o2]; rw [h1, h2, h3, Bool.true_or]
          · have h1 : (D2.wires (incidenceInput {p} {l})).getD (26 + i0) false = true := by
              rw [← hawi, hD2_val _ (hinc_len _ _) (26 + i0) (by omega),
                hD1_eq_prefix _ (hinc_len _ _) (26 + i0) le_rfl, hvi]
            rw [h1, Bool.or_true]
        · intro Q hQ
          rw [hE_eval _ (hinc_len _ _)]
          have hawi : aliasW (26 + k) u0 (26 + i0) = 26 + i0 := by dsimp only [aliasW]; rw [if_neg (by omega), if_neg (by omega)]
          have hfi : (D.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + i0) false = false :=
            hClean i0 hi0 hi0op Q hQ
          have h1 := hD2_val (incidenceInput Q (missLines singerLines3 Q)) (hinc_len _ _) D.output hOut'
          have h2 := hD1_eq_when_false (incidenceInput Q (missLines singerLines3 Q)) (hinc_len _ _) hfi D.output hOut'
          have h3 : (D.wires (incidenceInput Q (missLines singerLines3 Q))).getD D.output false = false := hQuad Q hQ
          have h4 : (D2.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + i0) false = false := by
            rw [← hawi, hD2_val _ (hinc_len _ _) (26 + i0) (by omega),
              hD1_eq_prefix _ (hinc_len _ _) (26 + i0) le_rfl, hfi]
          dsimp only [o2]; rw [h1, h2, h3, h4]; rfl
      · have := hk_d1.2; rw [hk_inps] at this; simp at this
    have normalize : ∀ k : ℕ, ∀ D : Circuit, andPairs 26 D = k →
        Monotone2 D → ReadsBack 26 D → D.output < 26 + D.size →
        RightOnIncidentPairs singerLines3 D →
        (∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q → D.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
        (∀ g < D.size, (gateAt D g).op = GateOp.and → ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
          (D.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + g) false = false) →
        ∃ E : Circuit, E.size ≤ D.size ∧ Monotone2 E ∧ ReadsBack 26 E ∧
          RightOnIncidentPairs singerLines3 E ∧
          (∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q → E.eval (incidenceInput Q (missLines singerLines3 Q)) = false) ∧
          ¬ ∃ i j : ℕ, (gateAt E i).op = GateOp.and ∧ (gateAt E j).op = GateOp.and ∧ InCone 26 E i j := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro D hk hM hRB hOut hPos hQuad hClean
        by_cases hz : k = 0
        · refine ⟨D, le_rfl, hM, hRB, hPos, hQuad, ?_⟩
          rintro ⟨i, j, hiop, hjop, hcone⟩
          have hpos : 0 < andPairs 26 D := Finset.card_pos.mpr ⟨(i, j), by
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨lt_gates_of_and hiop, lt_gates_of_and hjop⟩, hiop, hjop, hcone⟩⟩
          omega
        · obtain ⟨E1, hsz1, hM1, hRB1, hOut1, hPos1, hQuad1, hClean1, hlt1⟩ :=
            topform_step D hM hRB hOut hPos hQuad hClean (by omega)
          obtain ⟨E, hsz2, hME, hRBE, hPosE, hQuadE, hNoE⟩ :=
            ih (andPairs 26 E1) (by omega) E1 rfl hM1 hRB1 hOut1 hPos1 hQuad1 hClean1
          exact ⟨E, le_trans hsz2 hsz1, hME, hRBE, hPosE, hQuadE, hNoE⟩
    obtain ⟨E, hEsz, hEMono, hERB, hEPos, hEQuad, hENoAnd⟩ :=
      normalize (andPairs 26 D0) D0 rfl hD0_mono hD0_rb hD0_out hD0_pos hD0_quad hD0_clean
    let pgD : Finset (Fin 13) := {0, 1, 3, 9}
    let pgPair (p l : Fin 13) : List Bool :=
      (List.ofFn fun x : Fin 13 => decide (x = p)) ++ List.ofFn fun x : Fin 13 => decide (x = l)
    let pgQuad (Q : Finset (Fin 13)) : List Bool :=
      (List.ofFn fun x : Fin 13 => decide (x ∈ Q)) ++ List.ofFn fun x : Fin 13 => decide (∀ q ∈ Q, q - x ∉ pgD)
    let isQuad (Q : Finset (Fin 13)) : Prop := Q.card = 4 ∧ ∀ l : Fin 13, {q ∈ Q | q - l ∈ pgD}.card ≤ 2
    let missesL (Q : Finset (Fin 13)) (l : Fin 13) : Prop := ∀ q ∈ Q, q - l ∉ pgD
    let shiftQ (t : Fin 13) (Q : Finset (Fin 13)) : Finset (Fin 13) := Q.image (· + t)
    let baseQ : Fin 6 → Finset (Fin 13) := fun b =>
      if b = 0 then {0, 1, 4, 6} else if b = 1 then {0, 1, 2, 5} else if b = 2 then {0, 1, 2, 6}
      else if b = 3 then {0, 1, 4, 8} else if b = 4 then {0, 2, 3, 4} else {0, 3, 5, 6}
    have mem_s3 : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ pgD := by decide
    have pg_edges_52 : (Finset.univ.filter fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ pgD).card = 52 := by decide
    have pg_no_c4 : ∀ p1 p2 l1 l2 : Fin 13, p1 ≠ p2 → l1 ≠ l2 →
        ¬ (p1 - l1 ∈ pgD ∧ p1 - l2 ∈ pgD ∧ p2 - l1 ∈ pgD ∧ p2 - l2 ∈ pgD) := by decide
    have pg_zero_D : (0 : Fin 13) ∈ pgD := by decide
    have bq_quad : ∀ b : Fin 6, isQuad (baseQ b) := by decide
    have bq_zero : ∀ b : Fin 6, (0 : Fin 13) ∈ baseQ b := by decide
    have bq_miss2 : missesL (baseQ 0) 2 := by decide
    have bq_pt_diff : ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ a ∈ baseQ b, a + d ∈ baseQ b := by decide
    have bq_ln_diff : ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ l : Fin 13, missesL (baseQ b) l ∧ missesL (baseQ b) (l + d) := by decide
    have bq_noninc : ∀ d : Fin 13, (0 - d) ∉ pgD → ∃ b : Fin 6, missesL (baseQ b) d := by decide
    have isQuad_shift : ∀ (t : Fin 13) {Q : Finset (Fin 13)}, isQuad Q → isQuad (shiftQ t Q) := by
      intro t Q hQ; rcases hQ with ⟨hc, hl⟩
      have hinj : Function.Injective (fun x : Fin 13 => x + t) := fun a b h => add_right_cancel h
      refine ⟨by rw [Finset.card_image_of_injective Q hinj]; exact hc, fun l => ?_⟩
      have heq : {q ∈ shiftQ t Q | q - l ∈ pgD} = ({q ∈ Q | q - (l - t) ∈ pgD}).image (· + t) := by
        ext x; simp only [shiftQ, Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hinc⟩; exact ⟨a, ⟨ha, by convert hinc using 1; abel⟩, rfl⟩
        · rintro ⟨a, ⟨ha, hinc⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, by convert hinc using 1; abel⟩
      rw [heq, Finset.card_image_of_injective _ hinj]; exact hl (l - t)
    have missesL_shift : ∀ (t : Fin 13) {Q : Finset (Fin 13)} {l : Fin 13}, missesL Q l → missesL (shiftQ t Q) (l + t) := by
      intro t Q l hm q hq
      rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
      have heq : (a + t) - (l + t) = a - l := by abel
      rw [heq]; exact hm a ha
    have quad_pt : ∀ p : Fin 13, ∃ Q, isQuad Q ∧ p ∈ Q := fun p =>
      ⟨shiftQ p (baseQ 0), isQuad_shift p (bq_quad 0), Finset.mem_image.mpr ⟨0, bq_zero 0, zero_add p⟩⟩
    have quad_ln : ∀ l : Fin 13, ∃ Q, isQuad Q ∧ missesL Q l := fun l =>
      ⟨shiftQ (l - 2) (baseQ 0), isQuad_shift (l - 2) (bq_quad 0), by
        have h := missesL_shift (l - 2) bq_miss2; rwa [show (2 : Fin 13) + (l - 2) = l by abel] at h⟩
    have quad_2pt : ∀ {p1 p2 : Fin 13}, p1 ≠ p2 → ∃ Q, isQuad Q ∧ p1 ∈ Q ∧ p2 ∈ Q := by
      intro p1 p2 hne
      obtain ⟨b, a, ha, had⟩ := bq_pt_diff (p2 - p1) (sub_ne_zero.mpr hne.symm)
      refine ⟨shiftQ (p1 - a) (baseQ b), isQuad_shift (p1 - a) (bq_quad b),
        Finset.mem_image.mpr ⟨a, ha, by abel⟩, Finset.mem_image.mpr ⟨a + (p2 - p1), had, by abel⟩⟩
    have quad_2ln : ∀ {l1 l2 : Fin 13}, l1 ≠ l2 → ∃ Q, isQuad Q ∧ missesL Q l1 ∧ missesL Q l2 := by
      intro l1 l2 hne
      obtain ⟨b, l, hl, hld⟩ := bq_ln_diff (l2 - l1) (sub_ne_zero.mpr hne.symm)
      refine ⟨shiftQ (l1 - l) (baseQ b), isQuad_shift (l1 - l) (bq_quad b), ?_, ?_⟩
      · have h := missesL_shift (l1 - l) hl; rwa [show l + (l1 - l) = l1 by abel] at h
      · have h := missesL_shift (l1 - l) hld; rwa [show l + (l2 - l1) + (l1 - l) = l2 by abel] at h
    have quad_ni : ∀ {p l : Fin 13}, p - l ∉ pgD → ∃ Q, isQuad Q ∧ p ∈ Q ∧ missesL Q l := by
      intro p l hni
      obtain ⟨b, hm⟩ := bq_noninc (l - p) (by convert hni using 1; abel)
      refine ⟨shiftQ p (baseQ b), isQuad_shift p (bq_quad b), Finset.mem_image.mpr ⟨0, bq_zero b, zero_add p⟩, ?_⟩
      have h := missesL_shift p hm; rwa [show (l - p) + p = l by abel] at h
    have pgPair_len : ∀ p l : Fin 13, (pgPair p l).length = 26 := fun _ _ => by simp [pgPair]
    have pgQuad_len : ∀ Q : Finset (Fin 13), (pgQuad Q).length = 26 := fun _ => by simp [pgQuad]
    have pgPair_pt : ∀ p l x : Fin 13, (pgPair p l).getD x.val false = decide (x = p) := by
      intro p l x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [x.isLt]), List.getElem?_ofFn]
      simp [x.isLt]
    have pgPair_ln : ∀ p l x : Fin 13, (pgPair p l).getD (13 + x.val) false = decide (x = l) := by
      intro p l x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
        Nat.add_sub_cancel_left, List.getElem?_ofFn]
      simp [x.isLt]
    have pgQuad_pt : ∀ (Q : Finset (Fin 13)) (x : Fin 13), (pgQuad Q).getD x.val false = decide (x ∈ Q) := by
      intro Q x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [x.isLt]), List.getElem?_ofFn]
      simp [x.isLt]
    have pgQuad_ln : ∀ (Q : Finset (Fin 13)) (x : Fin 13), (pgQuad Q).getD (13 + x.val) false = decide (missesL Q x) := by
      intro Q x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
        Nat.add_sub_cancel_left, List.getElem?_ofFn]
      simp [x.isLt, missesL]
    have quad_bit : ∀ i : Fin 26, ∃ Q, isQuad Q ∧ (pgQuad Q).getD i.val false = true := by
      intro i
      by_cases h : i.val < 13
      · obtain ⟨Q, hQ, hm⟩ := quad_pt ⟨i.val, h⟩
        exact ⟨Q, hQ, by rw [pgQuad_pt Q ⟨i.val, h⟩]; exact decide_eq_true hm⟩
      · obtain ⟨Q, hQ, hm⟩ := quad_ln ⟨i.val - 13, by omega⟩
        have heq : 13 + (i.val - 13) = i.val := by omega
        exact ⟨Q, hQ, by rw [← heq, pgQuad_ln Q ⟨i.val - 13, by omega⟩]; exact decide_eq_true hm⟩
    have hEQuad' : ∀ Q : Finset (Fin 13), isQuad Q → E.eval (pgQuad Q) = false := by
      intro Q hQ
      have hQ' : IsQuadrangle singerLines3 Q := ⟨hQ.1, fun l => by
        have : Q ∩ singerLines3 l = {q ∈ Q | q - l ∈ pgD} := by ext q; simp [mem_s3]
        rw [this]; exact hQ.2 l⟩
      have heq : incidenceInput Q (missLines singerLines3 Q) = pgQuad Q := by
        show (List.ofFn fun x : Fin 13 => decide (x ∈ Q)) ++ (List.ofFn fun x : Fin 13 => decide (x ∈ missLines singerLines3 Q)) =
          (List.ofFn fun x : Fin 13 => decide (x ∈ Q)) ++ List.ofFn fun x : Fin 13 => decide (∀ q ∈ Q, q - x ∉ pgD)
        congr 1
        apply congrArg List.ofFn; funext x; apply decide_eq_decide.mpr
        change x ∈ Finset.univ.filter (fun l => Disjoint (singerLines3 l) Q) ↔ _
        simp [Finset.disjoint_right, mem_s3]
      rw [← heq]; exact hEQuad Q hQ'
    have hEPos' : ∀ p l : Fin 13, p - l ∈ pgD → E.eval (pgPair p l) = true := by
      intro p l hinc
      have heq : incidenceInput {p} {l} = pgPair p l := by
        show (List.ofFn fun x : Fin 13 => decide (x ∈ ({p} : Finset (Fin 13)))) ++ (List.ofFn fun x : Fin 13 => decide (x ∈ ({l} : Finset (Fin 13)))) =
          (List.ofFn fun x : Fin 13 => decide (x = p)) ++ List.ofFn fun x : Fin 13 => decide (x = l)
        simp
      rw [← heq]; exact hEPos l p ((mem_s3 p l).mpr hinc)
    let toPt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
    let toLn (l : Fin 13) : Fin 26 := Fin.natAdd 13 l
    let adj26 (u v : Fin 26) : Prop :=
      ∃ p l : Fin 13, p - l ∈ pgD ∧ ((u = toPt p ∧ v = toLn l) ∨ (u = toLn l ∧ v = toPt p))
    have toPt_val : ∀ p : Fin 13, (toPt p).val = p.val := fun _ => rfl
    have toLn_val : ∀ l : Fin 13, (toLn l).val = 13 + l.val := fun l => by simp [toLn]; omega
    have toPt_ne_toLn : ∀ p l : Fin 13, toPt p ≠ toLn l := fun p l h => by
      have := congrArg Fin.val h; rw [toPt_val, toLn_val] at this; omega
    have toPt_inj : ∀ {p1 p2 : Fin 13}, toPt p1 = toPt p2 → p1 = p2 := by
      intro p1 p2 h; exact Fin.ext (by simpa [toPt] using congrArg Fin.val h)
    have toLn_inj : ∀ {l1 l2 : Fin 13}, toLn l1 = toLn l2 → l1 = l2 := by
      intro l1 l2 h; have hv := congrArg Fin.val h; rw [toLn_val, toLn_val] at hv; exact Fin.ext (by omega)
    have adj26_no_c4 : ∀ {c1 c2 u1 u2 : Fin 26}, c1 ≠ c2 → u1 ≠ u2 →
        adj26 c1 u1 → adj26 c1 u2 → adj26 c2 u1 → adj26 c2 u2 → False := by
      intro c1 c2 u1 u2 hc hu h11 h12 h21 h22
      rcases h11 with ⟨p1, l1, d11, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rcases h12 with ⟨p1', l2, d12, ⟨e1, rfl⟩ | ⟨e1, _⟩⟩
        · rcases toPt_inj e1 with rfl
          rcases h21 with ⟨p2, l1', d21, ⟨rfl, e2⟩ | ⟨_, e2⟩⟩
          · rcases toLn_inj e2 with rfl
            rcases h22 with ⟨p2', l2', d22, ⟨e3, e4⟩ | ⟨e3, _⟩⟩
            · rcases toPt_inj e3 with rfl; rcases toLn_inj e4 with rfl
              exact pg_no_c4 p1 p2 l1 l2 (fun h => hc (by rw [h])) (fun h => hu (by rw [h])) ⟨d11, d12, d21, d22⟩
            · exact toPt_ne_toLn p2 l2' e3
          · exact toPt_ne_toLn p2 l1 e2.symm
        · exact toPt_ne_toLn p1 l2 e1
      · rcases h12 with ⟨p2, l1', d12, ⟨e1, _⟩ | ⟨e1, rfl⟩⟩
        · exact toPt_ne_toLn p2 l1 e1.symm
        · rcases toLn_inj e1 with rfl
          rcases h21 with ⟨p1', l2, d21, ⟨_, e2⟩ | ⟨rfl, e2⟩⟩
          · exact toPt_ne_toLn p1 l2 e2
          · rcases toPt_inj e2 with rfl
            rcases h22 with ⟨p2', l2', d22, ⟨e3, _⟩ | ⟨e3, e4⟩⟩
            · exact toPt_ne_toLn p2' l2 e3.symm
            · rcases toLn_inj e3 with rfl; rcases toPt_inj e4 with rfl
              exact pg_no_c4 p1 p2 l1 l2 (fun h => hu (by rw [h])) (fun h => hc (by rw [h])) ⟨d11, d21, d12, d22⟩
    let mkEdge (c u : Fin 26) : Fin 13 × Fin 13 :=
      if c.val < 13 then (⟨c.val % 13, Nat.mod_lt _ (by decide)⟩, ⟨(u.val - 13) % 13, Nat.mod_lt _ (by decide)⟩)
      else (⟨u.val % 13, Nat.mod_lt _ (by decide)⟩, ⟨(c.val - 13) % 13, Nat.mod_lt _ (by decide)⟩)
    have mkEdge_pt_ln : ∀ p l : Fin 13, mkEdge (toPt p) (toLn l) = (p, l) := by
      intro p l; dsimp only [mkEdge]; rw [toPt_val, toLn_val, if_pos p.isLt]
      apply Prod.ext <;> apply Fin.ext <;> simp [Nat.mod_eq_of_lt p.isLt, Nat.mod_eq_of_lt l.isLt]
    have mkEdge_ln_pt : ∀ l p : Fin 13, mkEdge (toLn l) (toPt p) = (p, l) := by
      intro l p; dsimp only [mkEdge]; rw [toPt_val, toLn_val, if_neg (by omega)]
      apply Prod.ext <;> apply Fin.ext <;> simp [Nat.mod_eq_of_lt p.isLt, Nat.mod_eq_of_lt l.isLt]
    have orIn_in : ∀ {n : ℕ} {C : Circuit} (i : Fin n), orIn n C i.val = {i} := by
      intro n C i; ext u; unfold orIn; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro (hu | ⟨_, _, ⟨hni, _⟩, _, _⟩)
        · exact Fin.ext hu
        · omega
      · rintro rfl; exact Or.inl rfl
    have orIn_ge : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ {w : ℕ}, n + C.gates.length ≤ w → orIn n C w = ∅ := by
      intro n C hRB w hw; ext u; unfold orIn; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro (hu | ⟨k, _, hwk, _, _⟩)
      · omega
      · rw [orReaches_iff hRB] at hwk; rcases hwk with ⟨j, hj, rfl, _⟩; omega
    have orIn_and : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.and → orIn n C (n + j) = ∅ := by
      intro n C hRB j hj hop; ext u; unfold orIn; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro (hu | ⟨k, _, hjk, hkop, _⟩)
      · omega
      · rw [orReaches_iff hRB] at hjk; rcases hjk with ⟨j', _, heq, hcase⟩
        have hjeq : j' = j := by omega
        subst hjeq
        rcases hcase with rfl | ⟨hor, _⟩
        · rw [hop] at hkop; cases hkop
        · rw [hop] at hor; cases hor
    have mem_orIn_or : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.or →
        ∀ u : Fin n, u ∈ orIn n C (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, u ∈ orIn n C w := by
      intro n C hRB j hj hop u; unfold orIn; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
        · omega
        · rw [orReaches_iff hRB] at hjk; rcases hjk with ⟨j', _, heq, hcase⟩
          have hjeq : j' = j := by omega
          subst hjeq
          rcases hcase with rfl | ⟨_, w, hw, hwk⟩
          · exact ⟨u.val, huk, Or.inl rfl⟩
          · exact ⟨w, hw, Or.inr ⟨k, hk, hwk, hkop, huk⟩⟩
      · rintro ⟨w, hw, hEq | ⟨k, hk, hwk, hkop, huk⟩⟩
        · exact Or.inr ⟨j, hj, orReaches_self hRB hj, hop, hEq ▸ hw⟩
        · exact Or.inr ⟨k, hk, (orReaches_iff hRB (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, w, hw, hwk⟩⟩, hkop, huk⟩
    have orIn_sub : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ {w g : ℕ}, OrReaches n C w g → orIn n C (n + g) ⊆ orIn n C w := by
      intro n C hRB w g hwg u hu; unfold orIn at hu ⊢; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
      · omega
      · exact Or.inr ⟨k, hk, orReaches_trans hRB w g k hwg hgk, hkop, huk⟩
    have wires_true_orIn : ∀ {n : ℕ} {C : Circuit}, ReadsBack n C → ∀ (inp : List Bool), inp.length = n →
        ∀ {w : ℕ} {i : Fin n}, i ∈ orIn n C w → inp.getD i.val false = true → (C.wires inp).getD w false = true := by
      intro n C hRB inp hlen w i hi hit; unfold orIn at hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with rfl | ⟨k, hk, hwk, hkop, hik⟩
      · rw [wires_in C inp (hlen.symm ▸ i.isLt)]; exact hit
      · apply wires_true_of_orReaches hRB inp hlen w k hwk
        rw [wires_gate hRB inp hlen hk, hkop]
        simp only [eval_or, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
        exact ⟨i.val, hik, by rw [wires_in C inp (hlen.symm ▸ i.isLt)]; exact hit⟩
    have wires_decomp : ∀ {n : ℕ} {C : Circuit}, Monotone2 C → ReadsBack n C → ∀ (inp : List Bool), inp.length = n →
        ∀ w : ℕ, (C.wires inp).getD w false = true →
          (∃ i ∈ orIn n C w, inp.getD i.val false = true) ∨
          (∃ g : ℕ, (gateAt C g).op = GateOp.and ∧ OrReaches n C w g ∧ (C.wires inp).getD (n + g) false = true) := by
      intro n C hM hRB inp hlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwt
        by_cases hlt : w < n
        · exact Or.inl ⟨⟨w, hlt⟩, by rw [orIn_in ⟨w, hlt⟩]; exact Finset.mem_singleton_self _, by rwa [wires_in C inp (by omega)] at hwt⟩
        · by_cases hge : n + C.gates.length ≤ w
          · rw [wires_ge C inp (by omega)] at hwt; cases hwt
          · set j := w - n
            have hwj : w = n + j := by omega
            have hj : j < C.gates.length := by omega
            rw [hwj] at hwt ⊢
            rcases gateOp_ao hM hj with hand | hor
            · exact Or.inr ⟨j, hand, orReaches_self hRB hj, hwt⟩
            · rw [wires_gate hRB inp hlen hj, hor] at hwt
              simp only [eval_or, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at hwt
              rcases hwt with ⟨u, hu, hut⟩
              have hult := hRB j hj u hu
              rcases ih u (by omega) hut with ⟨i, hi, hit⟩ | ⟨g, hgop, hug, hgt⟩
              · exact Or.inl ⟨i, (mem_orIn_or hRB hj hor i).mpr ⟨u, hu, hi⟩, hit⟩
              · exact Or.inr ⟨g, hgop, (orReaches_iff hRB (n + j) g).mpr ⟨j, hj, rfl, Or.inr ⟨hor, u, hu, hug⟩⟩, hgt⟩
    have wires_iff_cone : ∀ {g : ℕ}, (gateAt E g).op = GateOp.and → ∀ (inp : List Bool), inp.length = 26 →
        ∀ w : ℕ, (w < 26 ∨ (26 ≤ w ∧ InCone 26 E (w - 26) g)) →
        ((E.wires inp).getD w false = true ↔ ∃ i ∈ orIn 26 E w, inp.getD i.val false = true) := by
      intro g hgop inp hlen w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        rcases hw with hlt | ⟨hnw, hcone⟩
        · rw [wires_in E inp (by omega), orIn_in ⟨w, hlt⟩]; simp
        · set k := w - 26; have hwk : w = 26 + k := by omega
          have hkt := inCone_lt hERB g k hcone; have hk : k < E.gates.length := by omega
          have hkop : (gateAt E k).op = GateOp.or := (gateOp_ao hEMono hk).resolve_left fun ha => hENoAnd ⟨k, g, ha, hgop, hcone⟩
          rw [hwk, wires_gate hERB inp hlen hk, hkop]
          simp only [eval_or, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
          constructor
          · rintro ⟨u, hu, hut⟩
            have hult := hERB k hk u hu
            have huc : u < 26 ∨ (26 ≤ u ∧ InCone 26 E (u - 26) g) := by
              by_cases h1 : u < 26
              · exact Or.inl h1
              · exact Or.inr ⟨by omega, inCone_trans hERB g (u - 26) k ((inCone_iff hERB _ _).mpr ⟨hk, u, hu, by omega, Or.inl rfl⟩) hcone⟩
            rcases (ih u (by omega) huc).mp hut with ⟨i, hi, hit⟩
            exact ⟨i, (mem_orIn_or hERB hk hkop i).mpr ⟨u, hu, hi⟩, hit⟩
          · rintro ⟨i, hi, hit⟩
            rcases (mem_orIn_or hERB hk hkop i).mp hi with ⟨u, hu, hui⟩
            have hult := hERB k hk u hu
            have huc : u < 26 ∨ (26 ≤ u ∧ InCone 26 E (u - 26) g) := by
              by_cases h1 : u < 26
              · exact Or.inl h1
              · exact Or.inr ⟨by omega, inCone_trans hERB g (u - 26) k ((inCone_iff hERB _ _).mpr ⟨hk, u, hu, by omega, Or.inl rfl⟩) hcone⟩
            exact ⟨u, hu, (ih u (by omega) huc).mpr ⟨i, hui, hit⟩⟩
    have and_eval_iff : ∀ {g : ℕ}, (gateAt E g).op = GateOp.and → ∀ (inp : List Bool), inp.length = 26 →
        ((E.wires inp).getD (26 + g) false = true ↔ ∀ w ∈ (gateAt E g).inputs, ∃ i ∈ orIn 26 E w, inp.getD i.val false = true) := by
      intro g hgop inp hlen
      have hg := lt_gates_of_and hgop
      rw [wires_gate hERB inp hlen hg, hgop]
      simp only [eval_and, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      have hwc : ∀ w ∈ (gateAt E g).inputs, w < 26 ∨ (26 ≤ w ∧ InCone 26 E (w - 26) g) := by
        intro w hw
        by_cases h1 : w < 26
        · exact Or.inl h1
        · exact Or.inr ⟨by omega, (inCone_iff hERB _ _).mpr ⟨hg, w, hw, by omega, Or.inl rfl⟩⟩
      constructor
      · intro h w hw; exact (wires_iff_cone hgop inp hlen w (hwc w hw)).mp (h w hw)
      · intro h w hw; exact (wires_iff_cone hgop inp hlen w (hwc w hw)).mpr (h w hw)
    have inCone_or_ne : ∀ j i : ℕ, OrReaches 26 E (26 + j) i → i ≠ j → InCone 26 E i j := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro i hji hne
        rw [orReaches_iff hERB] at hji
        rcases hji with ⟨j', hj', heq, rfl | ⟨_, u, hu, hui⟩⟩
        · exact absurd (by omega) hne
        · have hjeq : j = j' := by omega
          rcases hjeq with rfl
          have hnu := hui.1; have hult := hERB j hj' u hu
          by_cases hiu : i = u - 26
          · exact (inCone_iff hERB i j).mpr ⟨hj', u, hu, hnu, Or.inl hiu⟩
          · have hui' : OrReaches 26 E (26 + (u - 26)) i := by rwa [show 26 + (u - 26) = u by omega]
            exact (inCone_iff hERB i j).mpr ⟨hj', u, hu, hnu, Or.inr (ih (u - 26) (by omega) i hui' hiu)⟩
    have inCone_inp_or : ∀ {j w i : ℕ}, j < E.gates.length → w ∈ (gateAt E j).inputs → OrReaches 26 E w i → InCone 26 E i j := by
      intro j w i hj hw hwi
      have hnw := hwi.1
      by_cases hiw : i = w - 26
      · exact (inCone_iff hERB i j).mpr ⟨hj, w, hw, hnw, Or.inl hiw⟩
      · have hwi' : OrReaches 26 E (26 + (w - 26)) i := by rwa [show 26 + (w - 26) = w by omega]
        exact (inCone_iff hERB i j).mpr ⟨hj, w, hw, hnw, Or.inr (inCone_or_ne (w - 26) i hwi' hiw)⟩
    let bigOr (W : Finset ℕ) : Finset ℕ :=
      (Finset.range E.gates.length).filter fun g =>
        (gateAt E g).op = GateOp.or ∧ 2 ≤ (orIn 26 E (26 + g)).card ∧ ∃ w ∈ W, OrReaches 26 E w g
    have leaf_bound : ∀ k : ℕ, ∀ W : Finset ℕ, (bigOr W).card = k → (W.biUnion (orIn 26 E)).card ≤ W.card + k := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro W hk
        by_cases hne : (bigOr W).Nonempty
        · set M := bigOr W; set m := M.max' hne
          have hMc : M.card = k := hk
          have hmM : m ∈ M := Finset.max'_mem M hne
          have hmp : m < E.gates.length ∧ (gateAt E m).op = GateOp.or ∧ 2 ≤ (orIn 26 E (26 + m)).card ∧ ∃ w ∈ W, OrReaches 26 E w m := by
            simpa [M, bigOr, Finset.mem_filter, Finset.mem_range] using hmM
          have hmax_u : ∀ w ∈ W, OrReaches 26 E w m → w = 26 + m := by
            intro w hw hwm
            rw [orReaches_iff hERB] at hwm
            rcases hwm with ⟨j, hj, rfl, hcase⟩
            by_contra hne_w
            rcases hcase with hEq | ⟨hjop, u, hu, hug⟩
            · exact hne_w (by omega)
            · have hjM : j ∈ M := by
                simp only [M, bigOr, Finset.mem_filter, Finset.mem_range]
                refine ⟨hj, hjop, le_trans hmp.2.2.1 (Finset.card_le_card (orIn_sub hERB
                  ((orReaches_iff hERB (26 + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, u, hu, hug⟩⟩))),
                  26 + j, hw, orReaches_self hERB hj⟩
              have := Finset.le_max' M j hjM
              have := (orReaches_le hERB _ _ hug).1; have := hERB j hj u hu; omega
          have hnmW : 26 + m ∈ W := by rcases hmp.2.2.2 with ⟨w, hw, hwm⟩; rwa [hmax_u w hw hwm] at hw
          set W' := (gateAt E m).inputs.toFinset ∪ (W.erase (26 + m))
          have hbi : W.biUnion (orIn 26 E) ⊆ W'.biUnion (orIn 26 E) := by
            intro u hu; rw [Finset.mem_biUnion] at hu ⊢; rcases hu with ⟨w, hw, huw⟩
            by_cases hwm : w = 26 + m
            · subst hwm; rcases (mem_orIn_or hERB hmp.1 hmp.2.1 u).mp huw with ⟨v, hv, huv⟩
              exact ⟨v, Finset.mem_union_left _ (List.mem_toFinset.mpr hv), huv⟩
            · exact ⟨w, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), huw⟩
          have hW'c : W'.card ≤ W.card + 1 := by
            have h1 : W'.card ≤ (gateAt E m).inputs.toFinset.card + (W.erase (26 + m)).card := Finset.card_union_le _ _
            have h2 := List.toFinset_card_le (gateAt E m).inputs
            have h3 := gate_len_le hEMono hmp.1
            have h4 := Finset.card_erase_add_one hnmW; omega
          have hM'sub : bigOr W' ⊆ M.erase m := by
            intro g hg; simp only [bigOr, Finset.mem_filter, Finset.mem_range] at hg
            rcases hg with ⟨hglt, hgop, hgc, w', hw', hw'g⟩
            rw [Finset.mem_erase]
            have hgM : g ∈ M := by
              simp only [M, bigOr, Finset.mem_filter, Finset.mem_range]
              refine ⟨hglt, hgop, hgc, ?_⟩
              rcases Finset.mem_union.mp hw' with hmem | herase
              · exact ⟨26 + m, hnmW, (orReaches_iff hERB (26 + m) g).mpr ⟨m, hmp.1, rfl, Or.inr ⟨hmp.2.1, w', List.mem_toFinset.mp hmem, hw'g⟩⟩⟩
              · exact ⟨w', (Finset.mem_erase.mp herase).2, hw'g⟩
            refine ⟨?_, hgM⟩
            rintro rfl
            rcases Finset.mem_union.mp hw' with hmem | herase
            · have := (orReaches_le hERB _ _ hw'g).1; have := hERB m hmp.1 w' (List.mem_toFinset.mp hmem); omega
            · exact (Finset.mem_erase.mp herase).1 (hmax_u w' (Finset.mem_erase.mp herase).2 hw'g)
          have hMer := Finset.card_erase_add_one hmM
          have hM'le : (bigOr W').card ≤ (M.erase m).card := Finset.card_le_card hM'sub
          have hrec := ih _ (by omega) W' rfl
          have := Finset.card_le_card hbi; omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          have hle1 : ∀ w ∈ W, (orIn 26 E w).card ≤ 1 := by
            intro w hw; by_contra hgt; push Not at hgt
            by_cases hlt : w < 26
            · rw [orIn_in ⟨w, hlt⟩, Finset.card_singleton] at hgt; omega
            · by_cases hge : 26 + E.gates.length ≤ w
              · rw [orIn_ge hERB hge, Finset.card_empty] at hgt; omega
              · set j := w - 26
                have hwEq : w = 26 + j := by omega
                have hj : j < E.gates.length := by omega
                rw [hwEq] at hgt hw
                rcases gateOp_ao hEMono hj with hop | hop
                · rw [orIn_and hERB hj hop, Finset.card_empty] at hgt; omega
                · have hjM : j ∈ bigOr W := by
                    simp only [bigOr, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hop, hgt, 26 + j, hw, orReaches_self hERB hj⟩
                  rw [hne] at hjM; simp at hjM
          have h1 : (W.biUnion (orIn 26 E)).card ≤ ∑ w ∈ W, (orIn 26 E w).card := Finset.card_biUnion_le
          have h2 : ∑ w ∈ W, (orIn 26 E w).card ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum hle1
          simp only [Finset.sum_const, smul_eq_mul, mul_one] at h2; omega
    have hNoOrIn : ∀ i : Fin 26, i ∉ orIn 26 E E.output := by
      intro i hi
      rcases quad_bit i with ⟨Q, hQ, hQi⟩
      have ht : E.eval (pgQuad Q) = true := wires_true_orIn hERB (pgQuad Q) (pgQuad_len Q) hi hQi
      rw [hEQuad' Q hQ] at ht; cases ht
    have hCov : ∀ p l : Fin 13, p - l ∈ pgD → ∃ g : ℕ,
        ((gateAt E g).op = GateOp.and ∧ OrReaches 26 E E.output g ∧
          ∀ Q : Finset (Fin 13), isQuad Q → (E.wires (pgQuad Q)).getD (26 + g) false = false) ∧
        (E.wires (pgPair p l)).getD (26 + g) false = true := by
      intro p l hinc
      rcases wires_decomp hEMono hERB (pgPair p l) (pgPair_len p l) E.output (hEPos' p l hinc) with
        ⟨i, hi, _⟩ | ⟨g, hgop, hreach, hgt⟩
      · exact False.elim (hNoOrIn i hi)
      · refine ⟨g, ⟨hgop, hreach, fun Q hQ => ?_⟩, hgt⟩
        cases hv : (E.wires (pgQuad Q)).getD (26 + g) false
        · rfl
        · exfalso
          have ht : E.eval (pgQuad Q) = true := wires_true_of_orReaches hERB (pgQuad Q) (pgQuad_len Q) E.output g hreach hv
          rw [hEQuad' Q hQ] at ht; cases ht
    let good (g : ℕ) : Prop := (gateAt E g).op = GateOp.and ∧ OrReaches 26 E E.output g ∧
      (∀ Q : Finset (Fin 13), isQuad Q → (E.wires (pgQuad Q)).getD (26 + g) false = false) ∧
      (∃ p l : Fin 13, p - l ∈ pgD ∧ (E.wires (pgPair p l)).getD (26 + g) false = true)
    let A : Finset ℕ := (Finset.range E.gates.length).filter good
    let OrTop : Finset ℕ := (Finset.range E.gates.length).filter fun h =>
      (gateAt E h).op = GateOp.or ∧ OrReaches 26 E E.output h ∧ ∃ g ∈ A, OrReaches 26 E (26 + h) g
    let OrBot : Finset ℕ := (Finset.range E.gates.length).filter fun h =>
      (gateAt E h).op = GateOp.or ∧ ∃ g ∈ A, InCone 26 E h g
    have hA_prop : ∀ g ∈ A, g < E.gates.length ∧ good g := fun g hg => by simpa [A, Finset.mem_filter, Finset.mem_range] using hg
    have hA_struct : ∀ g ∈ A, ∃ (c : Fin 26) (w : ℕ), w ∈ (gateAt E g).inputs ∧
        (∀ u ∈ orIn 26 E w, adj26 c u) ∧
        (∀ p l : Fin 13, (E.wires (pgPair p l)).getD (26 + g) false = true →
          (c = toPt p ∧ toLn l ∈ orIn 26 E w) ∨ (c = toLn l ∧ toPt p ∈ orIn 26 E w)) := by
      intro g hgA
      rcases hA_prop g hgA with ⟨hg, hgop, _, hquad, hpos⟩
      have hlen := gate_len_le hEMono hg
      have eval_qf : ∀ Q, isQuad Q → ¬ ∀ w ∈ (gateAt E g).inputs, ∃ i ∈ orIn 26 E w, (pgQuad Q).getD i.val false = true := by
        intro Q hQ hall; have ht := (and_eval_iff hgop (pgQuad Q) (pgQuad_len Q)).mpr hall
        rw [hquad Q hQ] at ht; cases ht
      rcases h : (gateAt E g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · exact False.elim (eval_qf (baseQ 0) (bq_quad 0) fun w hw => by rw [h] at hw; cases hw)
      · rcases hpos with ⟨p0, l0, _, hpt⟩
        have ha := (and_eval_iff hgop (pgPair p0 l0) (pgPair_len p0 l0)).mp hpt
        rw [h] at ha; rcases ha a (List.mem_singleton_self a) with ⟨i, hi, _⟩
        rcases quad_bit i with ⟨Q, hQ, hQi⟩
        exact False.elim (eval_qf Q hQ fun w hw => by rw [h, List.mem_singleton] at hw; subst hw; exact ⟨i, hi, hQi⟩)
      · have hpair_ab : ∀ p l : Fin 13, (E.wires (pgPair p l)).getD (26 + g) false = true ↔
            (∃ i ∈ orIn 26 E a, (pgPair p l).getD i.val false = true) ∧
            (∃ j ∈ orIn 26 E b, (pgPair p l).getD j.val false = true) := by
          intro p l; rw [and_eval_iff hgop (pgPair p l) (pgPair_len p l), h]; simp
        have hquad_ab : ∀ Q, isQuad Q → ¬ ((∃ i ∈ orIn 26 E a, (pgQuad Q).getD i.val false = true) ∧
            (∃ j ∈ orIn 26 E b, (pgQuad Q).getD j.val false = true)) := by
          intro Q hQ hqab; rcases hqab with ⟨hi, hj⟩; apply eval_qf Q hQ; intro w hw; rw [h] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> assumption
        have hne : (orIn 26 E a).Nonempty ∧ (orIn 26 E b).Nonempty := by
          rcases hpos with ⟨p0, l0, _, hpt⟩; rcases (hpair_ab p0 l0).mp hpt with ⟨⟨i, hi, _⟩, ⟨j, hj, _⟩⟩; exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        have hno_2pt : ∀ p1 p2 : Fin 13, toPt p1 ∈ orIn 26 E a → toPt p2 ∈ orIn 26 E b → False := by
          intro p1 p2 hp1 hp2
          by_cases heq : p1 = p2
          · subst heq; rcases quad_pt p1 with ⟨Q, hQ, hm⟩
            have hv : (pgQuad Q).getD (toPt p1).val false = true := by rw [toPt_val, pgQuad_pt]; exact decide_eq_true hm
            exact hquad_ab Q hQ ⟨⟨toPt p1, hp1, hv⟩, ⟨toPt p1, hp2, hv⟩⟩
          · rcases quad_2pt heq with ⟨Q, hQ, hm1, hm2⟩
            have hv1 : (pgQuad Q).getD (toPt p1).val false = true := by rw [toPt_val, pgQuad_pt]; exact decide_eq_true hm1
            have hv2 : (pgQuad Q).getD (toPt p2).val false = true := by rw [toPt_val, pgQuad_pt]; exact decide_eq_true hm2
            exact hquad_ab Q hQ ⟨⟨toPt p1, hp1, hv1⟩, ⟨toPt p2, hp2, hv2⟩⟩
        have hno_2ln : ∀ l1 l2 : Fin 13, toLn l1 ∈ orIn 26 E a → toLn l2 ∈ orIn 26 E b → False := by
          intro l1 l2 hl1 hl2
          by_cases heq : l1 = l2
          · subst heq; rcases quad_ln l1 with ⟨Q, hQ, hm⟩
            have hv : (pgQuad Q).getD (toLn l1).val false = true := by rw [toLn_val, pgQuad_ln]; exact decide_eq_true hm
            exact hquad_ab Q hQ ⟨⟨toLn l1, hl1, hv⟩, ⟨toLn l1, hl2, hv⟩⟩
          · rcases quad_2ln heq with ⟨Q, hQ, hm1, hm2⟩
            have hv1 : (pgQuad Q).getD (toLn l1).val false = true := by rw [toLn_val, pgQuad_ln]; exact decide_eq_true hm1
            have hv2 : (pgQuad Q).getD (toLn l2).val false = true := by rw [toLn_val, pgQuad_ln]; exact decide_eq_true hm2
            exact hquad_ab Q hQ ⟨⟨toLn l1, hl1, hv1⟩, ⟨toLn l2, hl2, hv2⟩⟩
        have hcross : ∀ i ∈ orIn 26 E a, ∀ j ∈ orIn 26 E b, adj26 i j := by
          intro i hi j hj
          by_cases h1 : i.val < 13
          · have hiEq : i = toPt ⟨i.val, h1⟩ := Fin.ext rfl; rw [hiEq] at hi ⊢
            by_cases h2 : j.val < 13
            · have hjEq : j = toPt ⟨j.val, h2⟩ := Fin.ext rfl
              exact False.elim (hno_2pt _ _ hi (hjEq ▸ hj))
            · have hjEq : j = toLn ⟨j.val - 13, by omega⟩ := Fin.ext (by rw [toLn_val]; dsimp; omega)
              rw [hjEq] at hj ⊢
              have hinc : ⟨i.val, h1⟩ - ⟨j.val - 13, by omega⟩ ∈ pgD := by
                by_contra hni; rcases quad_ni hni with ⟨Q, hQ, hm1, hm2⟩
                exact hquad_ab Q hQ ⟨⟨toPt ⟨i.val, h1⟩, hi, by rw [toPt_val, pgQuad_pt]; exact decide_eq_true hm1⟩,
                  ⟨toLn ⟨j.val - 13, by omega⟩, hj, by rw [toLn_val, pgQuad_ln]; exact decide_eq_true hm2⟩⟩
              exact ⟨⟨i.val, h1⟩, ⟨j.val - 13, by omega⟩, hinc, Or.inl ⟨rfl, rfl⟩⟩
          · have hiEq : i = toLn ⟨i.val - 13, by omega⟩ := Fin.ext (by rw [toLn_val]; dsimp; omega)
            rw [hiEq] at hi ⊢
            by_cases h2 : j.val < 13
            · have hjEq : j = toPt ⟨j.val, h2⟩ := Fin.ext rfl; rw [hjEq] at hj ⊢
              have hinc : ⟨j.val, h2⟩ - ⟨i.val - 13, by omega⟩ ∈ pgD := by
                by_contra hni; rcases quad_ni hni with ⟨Q, hQ, hm1, hm2⟩
                exact hquad_ab Q hQ ⟨⟨toLn ⟨i.val - 13, by omega⟩, hi, by rw [toLn_val, pgQuad_ln]; exact decide_eq_true hm2⟩,
                  ⟨toPt ⟨j.val, h2⟩, hj, by rw [toPt_val, pgQuad_pt]; exact decide_eq_true hm1⟩⟩
              exact ⟨⟨j.val, h2⟩, ⟨i.val - 13, by omega⟩, hinc, Or.inr ⟨rfl, rfl⟩⟩
            · have hjEq : j = toLn ⟨j.val - 13, by omega⟩ := Fin.ext (by rw [toLn_val]; dsimp; omega)
              rw [hjEq] at hj; exact False.elim (hno_2ln _ _ hi hj)
        have hcard1 : (orIn 26 E a).card = 1 ∨ (orIn 26 E b).card = 1 := by
          by_contra hboth; push Not at hboth
          have h1a : 1 < (orIn 26 E a).card := by have := Finset.card_pos.mpr hne.1; omega
          have h1b : 1 < (orIn 26 E b).card := by have := Finset.card_pos.mpr hne.2; omega
          rcases Finset.one_lt_card.mp h1a with ⟨u1, hu1, u2, hu2, hune⟩
          rcases Finset.one_lt_card.mp h1b with ⟨v1, hv1, v2, hv2, hvne⟩
          exact adj26_no_c4 hune hvne (hcross u1 hu1 v1 hv1) (hcross u1 hu1 v2 hv2) (hcross u2 hu2 v1 hv1) (hcross u2 hu2 v2 hv2)
        have hpair_get : ∀ (p l : Fin 13) (i : Fin 26), (pgPair p l).getD i.val false = true → i = toPt p ∨ i = toLn l := by
          intro p l i hi
          by_cases hlt : i.val < 13
          · left; have hg0 := pgPair_pt p l ⟨i.val, hlt⟩; rw [hi] at hg0
            exact Fin.ext (congrArg Fin.val (of_decide_eq_true hg0.symm))
          · right; have hg0 := pgPair_ln p l ⟨i.val - 13, by omega⟩
            rw [show 13 + (i.val - 13) = i.val by omega, hi] at hg0
            have hv := congrArg Fin.val (of_decide_eq_true hg0.symm); dsimp at hv
            exact Fin.ext (by rw [toLn_val]; omega)
        rcases hcard1 with ha1 | hb1
        · rcases Finset.card_eq_one.mp ha1 with ⟨c, hc⟩
          refine ⟨c, b, by simp, fun u hu => hcross c (by rw [hc]; simp) u hu, fun p l hpl => ?_⟩
          rcases (hpair_ab p l).mp hpl with ⟨⟨i, hi, hit⟩, ⟨j, hj, hjt⟩⟩
          rw [hc, Finset.mem_singleton] at hi; rcases hi with rfl
          rcases hpair_get p l i hit with hpt | hln <;> rcases hpair_get p l j hjt with rfl | rfl
          · exact False.elim (hno_2pt p p (by rw [hc, hpt]; simp) hj)
          · exact Or.inl ⟨hpt, hj⟩
          · exact Or.inr ⟨hln, hj⟩
          · exact False.elim (hno_2ln l l (by rw [hc, hln]; simp) hj)
        · rcases Finset.card_eq_one.mp hb1 with ⟨c, hc⟩
          refine ⟨c, a, by simp, fun u hu => ?_, fun p l hpl => ?_⟩
          · rcases hcross u hu c (by rw [hc]; simp) with ⟨p, l, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · exact ⟨p, l, hd, Or.inr ⟨rfl, rfl⟩⟩
            · exact ⟨p, l, hd, Or.inl ⟨rfl, rfl⟩⟩
          · rcases (hpair_ab p l).mp hpl with ⟨⟨i, hi, hit⟩, ⟨j, hj, hjt⟩⟩
            rw [hc, Finset.mem_singleton] at hj; rcases hj with rfl
            rcases hpair_get p l j hjt with hpt | hln <;> rcases hpair_get p l i hit with rfl | rfl
            · exact False.elim (hno_2pt p p hi (by rw [hc, hpt]; simp))
            · exact Or.inl ⟨hpt, hi⟩
            · exact Or.inr ⟨hln, hi⟩
            · exact False.elim (hno_2ln l l hi (by rw [hc, hln]; simp))
      · simp [h] at hlen
    let ctr (g : ℕ) : Fin 26 := if h : g ∈ A then (hA_struct g h).choose else 0
    let leafOpnd (g : ℕ) : ℕ := if h : g ∈ A then (hA_struct g h).choose_spec.choose else 0
    have hspec : ∀ g (hg : g ∈ A), leafOpnd g ∈ (gateAt E g).inputs ∧
        (∀ u ∈ orIn 26 E (leafOpnd g), adj26 (ctr g) u) ∧
        (∀ p l : Fin 13, (E.wires (pgPair p l)).getD (26 + g) false = true →
          (ctr g = toPt p ∧ toLn l ∈ orIn 26 E (leafOpnd g)) ∨
          (ctr g = toLn l ∧ toPt p ∈ orIn 26 E (leafOpnd g))) := fun g hg => by
      simpa [ctr, leafOpnd, hg] using (hA_struct g hg).choose_spec.choose_spec
    have hdisj_AT : Disjoint A OrTop := Finset.disjoint_left.mpr fun g hg1 hg2 => by
      have h1 := (hA_prop g hg1).2.1; have h2 := (Finset.mem_filter.mp hg2).2.1; rw [h1] at h2; cases h2
    have hdisj_AB : Disjoint A OrBot := Finset.disjoint_left.mpr fun g hg1 hg2 => by
      have h1 := (hA_prop g hg1).2.1; have h2 := (Finset.mem_filter.mp hg2).2.1; rw [h1] at h2; cases h2
    have hdisj_TB : Disjoint OrTop OrBot := Finset.disjoint_left.mpr fun h h1 h2 => by
      have ht := (Finset.mem_filter.mp h1).2; have hb := (Finset.mem_filter.mp h2).2
      rcases ht.2.2 with ⟨g1, hg1, hr1⟩; rcases hb.2 with ⟨g2, hg2, hc2⟩
      have hne : g1 ≠ h := fun heq => by subst heq; rw [(hA_prop g1 hg1).2.1] at ht; cases ht.1
      exact hENoAnd ⟨g1, g2, (hA_prop g1 hg1).2.1, (hA_prop g2 hg2).2.1, inCone_trans hERB g2 g1 h (inCone_or_ne h g1 hr1 hne) hc2⟩
    have htotal : A.card + OrTop.card + OrBot.card ≤ E.gates.length := by
      rw [← Finset.card_union_of_disjoint hdisj_AT,
        ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_AB, hdisj_TB⟩)]
      calc (A ∪ OrTop ∪ OrBot).card ≤ (Finset.range E.gates.length).card := Finset.card_le_card fun x hx => by
            simp only [Finset.mem_union] at hx; rcases hx with (hx | hx) | hx <;> exact (Finset.mem_filter.mp hx).1
        _ = E.gates.length := Finset.card_range _
    have h13_A : 13 ≤ A.card := by
      let S := A.image ctr
      have hcov : ∀ i : Fin 13, toPt i ∈ S ∨ toLn i ∈ S := by
        intro i
        rcases hCov i i (by simp [pg_zero_D]) with ⟨g, ⟨hgop, hreach, hquad⟩, hval⟩
        have hgA : g ∈ A := by
          simp only [A, good, Finset.mem_filter, Finset.mem_range]
          exact ⟨lt_gates_of_and hgop, hgop, hreach, hquad, ⟨i, i, by simp [pg_zero_D], hval⟩⟩
        rcases (hspec g hgA).2.2 i i hval with ⟨hc, _⟩ | ⟨hc, _⟩
        · exact Or.inl (Finset.mem_image.mpr ⟨g, hgA, hc⟩)
        · exact Or.inr (Finset.mem_image.mpr ⟨g, hgA, hc⟩)
      let f : Fin 13 → Fin 26 := fun i => if toPt i ∈ S then toPt i else toLn i
      have hfinj : Function.Injective f := by
        intro i j hij; dsimp only [f] at hij; split_ifs at hij
        · exact toPt_inj hij
        · exact False.elim (toPt_ne_toLn i j hij)
        · exact False.elim (toPt_ne_toLn j i hij.symm)
        · exact toLn_inj hij
      have hfmem : (Finset.univ : Finset (Fin 13)).image f ⊆ S := by
        intro x hx; rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        dsimp only [f]
        split_ifs with h1
        · exact h1
        · exact (hcov i).resolve_left h1
      calc 13 = (Finset.univ : Finset (Fin 13)).card := by simp
        _ = ((Finset.univ : Finset (Fin 13)).image f).card := (Finset.card_image_of_injective _ hfinj).symm
        _ ≤ S.card := Finset.card_le_card hfmem
        _ ≤ A.card := Finset.card_image_le
    have hA_Top : A.card ≤ OrTop.card + 1 := by
      let U := (A ∪ OrTop).image (fun j => 26 + j)
      let U' := U.erase E.output
      have hUc : U.card = A.card + OrTop.card := by
        rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_union_of_disjoint hdisj_AT]
      have hU'c : U.card ≤ U'.card + 1 := by
        by_cases hm : E.output ∈ U
        · rw [Finset.card_erase_add_one hm]
        · simp only [U', Finset.erase_eq_of_notMem hm]; omega
      have hU'sub : U' ⊆ OrTop.biUnion fun h => (gateAt E h).inputs.toFinset := by
        intro u hu
        rcases Finset.mem_erase.mp hu with ⟨huOut, huU⟩
        rcases Finset.mem_image.mp huU with ⟨j, hj, rfl⟩
        have hrt : OrReaches 26 E E.output j := by
          rcases Finset.mem_union.mp hj with hjA | hjT
          · exact (hA_prop j hjA).2.2.1
          · exact (Finset.mem_filter.mp hjT).2.2.1
        have hrA : ∃ g ∈ A, OrReaches 26 E (26 + j) g := by
          rcases Finset.mem_union.mp hj with hjA | hjT
          · exact ⟨j, hjA, orReaches_self hERB (hA_prop j hjA).1⟩
          · exact (Finset.mem_filter.mp hjT).2.2.2
        rcases hrA with ⟨g, hgA, hjg⟩
        rcases orReaches_parent hERB E.output j hrt with hEq | ⟨h, hh, hhop, hrh, hmem⟩
        · exact absurd hEq.symm huOut
        · rw [Finset.mem_biUnion]
          refine ⟨h, ?_, List.mem_toFinset.mpr hmem⟩
          simp only [OrTop, Finset.mem_filter, Finset.mem_range]
          exact ⟨hh, hhop, hrh, g, hgA, (orReaches_iff hERB (26 + h) g).mpr ⟨h, hh, rfl, Or.inr ⟨hhop, 26 + j, hmem, hjg⟩⟩⟩
      have hU'le : U'.card ≤ 2 * OrTop.card := calc U'.card
          ≤ (OrTop.biUnion fun h => (gateAt E h).inputs.toFinset).card := Finset.card_le_card hU'sub
        _ ≤ ∑ h ∈ OrTop, (gateAt E h).inputs.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ h ∈ OrTop, (gateAt E h).inputs.length := Finset.sum_le_sum fun h _ => List.toFinset_card_le _
        _ ≤ ∑ _h ∈ OrTop, 2 := Finset.sum_le_sum fun h hh => gate_len_le hEMono (Finset.mem_range.mp (Finset.mem_filter.mp hh).1)
        _ = 2 * OrTop.card := by simp [Nat.mul_comm]
      omega
    have h52_AB : 52 ≤ A.card + OrBot.card := by
      let Kc (c : Fin 26) : Finset ℕ := A.filter fun g => ctr g = c
      let Wc (c : Fin 26) : Finset ℕ := (Kc c).image leafOpnd
      let Lc (c : Fin 26) : Finset (Fin 26) := (Wc c).biUnion (orIn 26 E)
      let Mc (c : Fin 26) : Finset ℕ := bigOr (Wc c)
      let Eall : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun e => e.1 - e.2 ∈ pgD
      let F : Finset (Fin 13 × Fin 13) := (Finset.univ : Finset (Fin 26)).biUnion fun c => (Lc c).image (mkEdge c)
      have hEF : Eall ⊆ F := by
        intro e he
        have hinc := (Finset.mem_filter.mp he).2
        rcases hCov e.1 e.2 hinc with ⟨g, ⟨hgop, hreach, hquad⟩, hval⟩
        have hgA : g ∈ A := by
          simp only [A, good, Finset.mem_filter, Finset.mem_range]
          exact ⟨lt_gates_of_and hgop, hgop, hreach, hquad, ⟨e.1, e.2, hinc, hval⟩⟩
        have hwW : leafOpnd g ∈ Wc (ctr g) := Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hgA, rfl⟩, rfl⟩
        rcases (hspec g hgA).2.2 e.1 e.2 hval with ⟨hc, hl⟩ | ⟨hc, hl⟩
        · exact Finset.mem_biUnion.mpr ⟨ctr g, Finset.mem_univ _, Finset.mem_image.mpr ⟨toLn e.2, Finset.mem_biUnion.mpr ⟨leafOpnd g, hwW, hl⟩, by rw [hc, mkEdge_pt_ln]⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨ctr g, Finset.mem_univ _, Finset.mem_image.mpr ⟨toPt e.1, Finset.mem_biUnion.mpr ⟨leafOpnd g, hwW, hl⟩, by rw [hc, mkEdge_ln_pt]⟩⟩
      have h52_F : 52 ≤ F.card := pg_edges_52 ▸ Finset.card_le_card hEF
      have hF_le : F.card ≤ ∑ c : Fin 26, (Lc c).card :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
      have hsum_L : ∑ c : Fin 26, (Lc c).card ≤ (∑ c : Fin 26, (Kc c).card) + ∑ c : Fin 26, (Mc c).card := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun c _ => le_trans (leaf_bound (Mc c).card (Wc c) rfl) (Nat.add_le_add_right Finset.card_image_le _)
      have hK_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Kc := fun c1 _ c2 _ hcne =>
        Finset.disjoint_left.mpr fun g hg1 hg2 => hcne ((Finset.mem_filter.mp hg1).2.symm.trans (Finset.mem_filter.mp hg2).2)
      have hsum_K : ∑ c : Fin 26, (Kc c).card ≤ A.card := by
        rw [← Finset.card_biUnion (fun a _ b _ hab => hK_disj (by simp) (by simp) hab)]
        exact Finset.card_le_card fun g hg => by rcases Finset.mem_biUnion.mp hg with ⟨c, _, hgc⟩; exact (Finset.mem_filter.mp hgc).1
      have hM_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Mc := fun c1 _ c2 _ hcne =>
        Finset.disjoint_left.mpr fun h hh1 hh2 => by
          simp only [Mc, bigOr, Finset.mem_filter, Finset.mem_range] at hh1 hh2
          rcases hh1 with ⟨_, _, hhcard, w1, hw1, hw1h⟩
          rcases hh2 with ⟨_, _, _, w2, hw2, hw2h⟩
          rcases Finset.mem_image.mp hw1 with ⟨g1, hg1, rfl⟩
          rcases Finset.mem_image.mp hw2 with ⟨g2, hg2, rfl⟩
          rcases Finset.mem_filter.mp hg1 with ⟨hg1A, hctr1⟩
          rcases Finset.mem_filter.mp hg2 with ⟨hg2A, hctr2⟩
          rcases Finset.one_lt_card.mp (by omega : 1 < (orIn 26 E (26 + h)).card) with ⟨u1, hu1, u2, hu2, hune⟩
          have ha11 := (hspec g1 hg1A).2.1 u1 (orIn_sub hERB hw1h hu1)
          have ha12 := (hspec g1 hg1A).2.1 u2 (orIn_sub hERB hw1h hu2)
          have ha21 := (hspec g2 hg2A).2.1 u1 (orIn_sub hERB hw2h hu1)
          have ha22 := (hspec g2 hg2A).2.1 u2 (orIn_sub hERB hw2h hu2)
          rw [hctr1] at ha11 ha12; rw [hctr2] at ha21 ha22
          exact adj26_no_c4 hcne hune ha11 ha12 ha21 ha22
      have hsum_M : ∑ c : Fin 26, (Mc c).card ≤ OrBot.card := by
        rw [← Finset.card_biUnion (fun a _ b _ hab => hM_disj (by simp) (by simp) hab)]
        exact Finset.card_le_card fun h hh => by
          rcases Finset.mem_biUnion.mp hh with ⟨c, _, hhc⟩
          simp only [Mc, bigOr, Finset.mem_filter, Finset.mem_range] at hhc
          rcases hhc with ⟨hhlt, hhop, _, w, hw, hwh⟩
          rcases Finset.mem_image.mp hw with ⟨g, hg, rfl⟩
          rcases Finset.mem_filter.mp hg with ⟨hgA, _⟩
          simp only [OrBot, Finset.mem_filter, Finset.mem_range]
          exact ⟨hhlt, hhop, g, hgA, inCone_inp_or (hA_prop g hgA).1 (hspec g hgA).1 hwh⟩
      omega
    have h64E : 64 ≤ E.size := by show 64 ≤ E.gates.length; omega
    omega
