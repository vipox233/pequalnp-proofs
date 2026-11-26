import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.TopForm

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_19026_2
    (degreeOne :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x1 →
        (∀ (x4 : Finset (Fin (13 : ℕ))),
          PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x4 →
          x1.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) →
        (64 : ℕ) ≤ x1.size)
    (exactTwoAO2 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ g ∈ x1.gates, g.inputs.Nodup) →
        PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 →
        x1.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) = (2 : ℕ) →
        x1.output + (1 : ℕ) = (26 : ℕ) + x1.size →
        (64 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 →
      PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) →
      (64 : ℕ) ≤ x1.size := by
  let run {α : Type} (step : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
    gs.foldl (fun acc g => acc ++ [step acc g]) init
  let evalStep (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)
  let degStep (d : List ℕ) (g : Gate) : ℕ :=
    g.lineDegree d
  let degInit : List ℕ :=
    (List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0
  have list_split_at : ∀ {α : Type} (l : List α) (j : ℕ) (hj : j < l.length),
      l = l.take j ++ l[j] :: l.drop (j + 1) := by
    intro α l j
    induction j generalizing l with
    | zero =>
      intro hj
      cases l with
      | nil => simp at hj
      | cons a t => simp
    | succ j ih =>
      intro hj
      cases l with
      | nil => simp at hj
      | cons a t =>
        simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.cons_append]
        congr 1
        exact ih t (by simp at hj; omega)
  have run_length : ∀ {α : Type} (step : List α → Gate → α) (gs : List Gate) (init : List α),
      (run step gs init).length = init.length + gs.length := by
    intro α step gs
    induction gs with
    | nil =>
      intro init
      simp [run]
    | cons g gs ih =>
      intro init
      simp only [run, List.foldl_cons, List.length_cons]
      rw [show (gs.foldl (fun acc g => acc ++ [step acc g]) (init ++ [step init g])).length =
        (run step gs (init ++ [step init g])).length from rfl, ih, List.length_append, List.length_singleton]
      omega
  have run_prefix : ∀ {α : Type} (step : List α → Gate → α) (gs : List Gate) (init : List α),
      ∃ t, run step gs init = init ++ t := by
    intro α step gs
    induction gs with
    | nil =>
      intro init
      exact ⟨[], by simp [run]⟩
    | cons g gs ih =>
      intro init
      obtain ⟨t, ht⟩ := ih (init ++ [step init g])
      refine ⟨step init g :: t, ?_⟩
      simpa [run, List.foldl_cons, List.append_assoc] using ht
  have run_getD_lt : ∀ {α : Type} (d : α) (step : List α → Gate → α) (gs : List Gate)
      (init : List α) (i : ℕ), i < init.length →
      (run step gs init).getD i d = init.getD i d := by
    intro α d step gs init i hi
    obtain ⟨t, ht⟩ := run_prefix step gs init
    rw [ht]
    exact List.getD_append init t d i hi
  have run_append : ∀ {α : Type} (step : List α → Gate → α) (gs1 gs2 : List Gate) (init : List α),
      run step (gs1 ++ gs2) init = run step gs2 (run step gs1 init) := by
    intro α step gs1 gs2 init
    simp [run, List.foldl_append]
  have wires_eq : ∀ (C : Circuit) (x : List Bool), C.wires x = run evalStep C.gates x := by
    intro C x
    rfl
  have lineDegrees_eq : ∀ (C : Circuit),
      C.lineDegrees 26 (Finset.Ico 13 26) = run degStep C.gates degInit := by
    intro C
    rfl
  have degInit_length : degInit.length = 26 := by
    simp [degInit]
  have degInit_getD_le : ∀ i : ℕ, degInit.getD i 0 ≤ 1 := by
    intro i
    by_cases hi : i < 26
    · simp [degInit, hi]
      split_ifs <;> omega
    · rw [List.getD_eq_default]
      · omega
      · simp [degInit]; omega
  have sum_map_le : ∀ {α : Type} (l : List α) (f g : α → ℕ),
      (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum := by
    intro α l f g hfg
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha : f a ≤ g a := hfg a List.mem_cons_self
      have hl : (l.map f).sum ≤ (l.map g).sum := ih (fun x hx => hfg x (List.mem_cons_of_mem a hx))
      omega
  have sum_filter_le : ∀ {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ),
      ((l.filter p).map f).sum ≤ (l.map f).sum := by
    intro α l p f
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filter_cons]
      cases hp : p a
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
        omega
      · simp only [↓reduceIte, List.map_cons, List.sum_cons]
        omega
  have max_map_le : ∀ {α : Type} (l : List α) (f g : α → ℕ),
      (∀ a ∈ l, f a ≤ g a) → (l.map f).foldr max 0 ≤ (l.map g).foldr max 0 := by
    intro α l f g hfg
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.foldr_cons]
      have ha : f a ≤ g a := hfg a List.mem_cons_self
      have hl : (l.map f).foldr max 0 ≤ (l.map g).foldr max 0 :=
        ih (fun x hx => hfg x (List.mem_cons_of_mem a hx))
      exact Nat.max_le.mpr ⟨le_trans ha (Nat.le_max_left _ _), le_trans hl (Nat.le_max_right _ _)⟩
  have max_filter_le : ∀ {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ),
      ((l.filter p).map f).foldr max 0 ≤ (l.map f).foldr max 0 := by
    intro α l p f
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filter_cons]
      cases hp : p a
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.foldr_cons]
        exact le_trans ih (Nat.le_max_right _ _)
      · simp only [↓reduceIte, List.map_cons, List.foldr_cons]
        exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, le_trans ih (Nat.le_max_right _ _)⟩
  have all_eq_false_of_mem : ∀ (l : List Bool), false ∈ l → l.all id = false := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons a l ih =>
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp
      · simp [ih hl]
  have any_eq_true_of_mem : ∀ (l : List Bool), true ∈ l → l.any id = true := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons a l ih =>
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp
      · simp [ih hl]
  have all_filter_eq : ∀ {α : Type} (l : List α) (p : α → Bool) (f : α → Bool),
      (∀ a ∈ l, p a = false → f a = true) →
      ((l.filter p).map f).all id = (l.map f).all id := by
    intro α l p f htrue
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filter_cons]
      have ihl := ih (fun x hx hpx => htrue x (List.mem_cons_of_mem a hx) hpx)
      cases hp : p a
      · have ha : f a = true := htrue a List.mem_cons_self hp
        simp [ha, ihl]
      · simp [ihl]
  have any_filter_eq : ∀ {α : Type} (l : List α) (p : α → Bool) (f : α → Bool),
      (∀ a ∈ l, p a = false → f a = false) →
      ((l.filter p).map f).any id = (l.map f).any id := by
    intro α l p f hfalse
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filter_cons]
      have ihl := ih (fun x hx hpx => hfalse x (List.mem_cons_of_mem a hx) hpx)
      cases hp : p a
      · have ha : f a = false := hfalse a List.mem_cons_self hp
        simp [ha, ihl]
      · simp [ihl]
  have ld_and : ∀ (inputs : List ℕ) (d : List ℕ),
      (Gate.mk GateOp.and inputs).lineDegree d = (inputs.map fun i => d.getD i 0).sum := by
    intro inputs d
    rfl
  have ld_or : ∀ (inputs : List ℕ) (d : List ℕ),
      (Gate.mk GateOp.or inputs).lineDegree d = (inputs.map fun i => d.getD i 0).foldr max 0 := by
    intro inputs d
    rfl
  have inc_len : ∀ (X Y : Finset (Fin 13)), (incidenceInput X Y).length = 26 := by
    intro X Y
    unfold incidenceInput
    simp
  have not_const : ∀ (C : Circuit), ComputesIncidence singerLines3 C → ∀ b : Bool,
      ¬ (∀ X Y : Finset (Fin 13), C.eval (incidenceInput X Y) = b) := by
    intro C hc b hconst
    have h0 : C.eval (incidenceInput (∅ : Finset (Fin 13)) (∅ : Finset (Fin 13))) = false := by
      rw [hc]
      unfold incidenceFun
      simp
    have h1 : C.eval (incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) ({(0 : Fin 13)} : Finset (Fin 13))) = true := by
      rw [hc]
      unfold incidenceFun
      apply decide_eq_true
      refine ⟨0, Finset.mem_singleton_self 0, 0, Finset.mem_singleton_self 0, ?_⟩
      decide
    have hb0 := hconst ∅ ∅
    have hb1 := hconst {0} {0}
    rw [h0] at hb0
    rw [h1] at hb1
    cases b <;> simp_all
  have from_deg1 : ∀ (C : Circuit), Monotone2 C → ComputesIncidence singerLines3 C →
      HasLineDegree 26 (Finset.Ico 13 26) C 1 → 64 ≤ C.size := by
    intro C hm hc hd
    refine degreeOne C hm ?_ ?_ hd
    · intro l p hp
      rw [hc {p} {l}]
      unfold incidenceFun
      apply decide_eq_true
      exact ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, hp⟩
    · intro Q _
      rw [hc Q (missLines singerLines3 Q)]
      unfold incidenceFun
      apply decide_eq_false
      rintro ⟨p, hp, l, hl, hpl⟩
      exact Finset.disjoint_left.mp (Finset.mem_filter.mp hl).2 hpl hp
  have eval_and : ∀ (w : List Bool) (ins : List ℕ),
      evalStep w ⟨GateOp.and, ins⟩ = (ins.map fun i => w.getD i false).all id := fun _ _ => rfl
  have eval_or : ∀ (w : List Bool) (ins : List ℕ),
      evalStep w ⟨GateOp.or, ins⟩ = (ins.map fun i => w.getD i false).any id := fun _ _ => rfl
  have gate_eq : ∀ (g : Gate) (op : GateOp) (ins : List ℕ),
      g.op = op → g.inputs = ins → g = ⟨op, ins⟩ := by
    rintro ⟨_, _⟩ _ _ rfl rfl
    rfl
  have delConst : ∀ (C : Circuit), Monotone2 C → ComputesIncidence singerLines3 C →
      ∀ (j : ℕ), j < C.gates.length → ∀ (b0 : Bool),
      (∀ x : List Bool, x.length = 26 → (C.wires x).getD (26 + j) false = b0) →
      ∃ C' : Circuit, C'.size < C.size ∧ Monotone2 C' ∧ ComputesIncidence singerLines3 C' ∧
        C'.lineDeg 26 (Finset.Ico 13 26) ≤ C.lineDeg 26 (Finset.Ico 13 26) := by
    intro C hm hc j hj b0 hconst
    let w0 : ℕ := 26 + j
    let shift : ℕ → ℕ := fun w => if w < w0 then w else w - 1
    have shift_lt : ∀ w, w < w0 → shift w = w := fun w hw => by dsimp only [shift]; split_ifs; rfl
    have shift_gt : ∀ w, ¬ w < w0 → shift w = w - 1 := fun w hw => by dsimp only [shift]; split_ifs; rfl
    let rwConst (b : Bool) (g : Gate) : Gate :=
      GateOp.casesOn g.op
        (Bool.casesOn b
          (if w0 ∈ g.inputs then ⟨GateOp.or, []⟩
           else ⟨GateOp.and, g.inputs.map shift⟩)
          ⟨GateOp.and, (g.inputs.filter fun w => decide (w ≠ w0)).map shift⟩)
        (Bool.casesOn b
          ⟨GateOp.or, (g.inputs.filter fun w => decide (w ≠ w0)).map shift⟩
          (if w0 ∈ g.inputs then ⟨GateOp.and, []⟩
           else ⟨GateOp.or, g.inputs.map shift⟩))
        ⟨GateOp.not, g.inputs.map shift⟩
        (fun m => ⟨GateOp.mod m, g.inputs.map shift⟩)
        ⟨GateOp.maj, g.inputs.map shift⟩
    let pre := C.gates.take j
    let post := C.gates.drop (j + 1)
    let C' : Circuit := ⟨pre ++ post.map (rwConst b0), shift C.output⟩
    have hsplit : C.gates = pre ++ C.gates[j] :: post := list_split_at C.gates j hj
    have hlen_pre : pre.length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hpost_op : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      simpa using (hm g (List.mem_of_mem_drop hg)).1
    have hC'_size : C'.size < C.size := by
      show (pre ++ post.map (rwConst b0)).length < C.gates.length
      rw [hsplit]
      simp [List.length_append, List.length_map]
    have hC'_mono : Monotone2 C' := by
      intro g hg
      simp only [C', List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g0, hg0, rfl⟩
      · exact hm g (List.mem_of_mem_take hg)
      · have hg0_in : g0 ∈ C.gates := List.mem_of_mem_drop hg0
        have hm0 := hm g0 hg0_in
        have hop : g0.op = GateOp.and ∨ g0.op = GateOp.or := by simpa using hm0.1
        have hlen0 : g0.inputs.length ≤ 2 := hm0.2
        rcases hop with hop | hop <;> cases hb0 : b0
        · dsimp only [rwConst]; rw [hop]
          split_ifs
          · exact ⟨by simp, by simp⟩
          · exact ⟨by simp, by simpa using hlen0⟩
        · dsimp only [rwConst]; rw [hop]
          exact ⟨by simp, le_trans (by simp [List.length_filter_le]) hlen0⟩
        · dsimp only [rwConst]; rw [hop]
          exact ⟨by simp, le_trans (by simp [List.length_filter_le]) hlen0⟩
        · dsimp only [rwConst]; rw [hop]
          split_ifs
          · exact ⟨by simp, by simp⟩
          · exact ⟨by simp, by simpa using hlen0⟩
    have hOutNe : C.output ≠ w0 := by
      intro heq
      apply not_const C hc b0
      intro X Y
      change (C.wires (incidenceInput X Y)).getD C.output false = b0
      rw [heq]
      exact hconst (incidenceInput X Y) (inc_len X Y)
    have hC'_eval : ComputesIncidence singerLines3 C' := by
      intro X Y
      rw [← hc X Y]
      let x := incidenceInput X Y
      have hxlen : x.length = 26 := inc_len X Y
      let accPre := run evalStep pre x
      have haccPre_len : accPre.length = w0 := by
        dsimp [accPre]
        rw [run_length, hxlen, hlen_pre]
      let accMid := run evalStep (pre ++ [C.gates[j]]) x
      have haccMid_eq : accMid = accPre ++ [evalStep accPre C.gates[j]] := by
        dsimp [accMid, accPre]
        rw [run_append]
        rfl
      have haccMid_len : accMid.length = accPre.length + 1 := by
        rw [haccMid_eq, List.length_append, List.length_singleton]
      have hw0_lt_mid : w0 < accMid.length := by omega
      have h_full_wires : C.wires x = run evalStep post accMid := by
        rw [wires_eq, hsplit]
        rw [show pre ++ C.gates[j] :: post = (pre ++ [C.gates[j]]) ++ post by simp [List.append_assoc]]
        rw [run_append]
      have h_C'_wires : C'.wires x = run evalStep (post.map (rwConst b0)) accPre := by
        rw [wires_eq]
        change run evalStep (pre ++ post.map (rwConst b0)) x = _
        rw [run_append]
      have haccMid_w0 : accMid.getD w0 false = b0 := by
        have h1 : (C.wires x).getD w0 false = accMid.getD w0 false := by
          rw [h_full_wires]
          exact run_getD_lt false evalStep post accMid w0 hw0_lt_mid
        rw [← h1]
        exact hconst x hxlen
      have h_init_rel : ∀ w, w ≠ w0 → accPre.getD (shift w) false = accMid.getD w false := by
        intro w hwne
        by_cases hlt : w < w0
        · rw [shift_lt w hlt, haccMid_eq]
          exact (List.getD_append accPre [evalStep accPre C.gates[j]] false w (by omega)).symm
        · have hgt : w0 < w := by omega
          rw [shift_gt w hlt, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have h_tail : ∀ (gs : List Gate),
          (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
          ∀ (acc acc' : List Bool),
          acc.length = acc'.length + 1 →
          w0 < acc.length →
          acc.getD w0 false = b0 →
          (∀ w, w ≠ w0 → acc'.getD (shift w) false = acc.getD w false) →
          ∀ w, w ≠ w0 →
            (run evalStep (gs.map (rwConst b0)) acc').getD (shift w) false =
            (run evalStep gs acc).getD w false := by
        intro gs
        induction gs with
        | nil =>
          intro _ acc acc' _ _ _ hrel w hwne
          simpa [run] using hrel w hwne
        | cons g gs ih =>
          intro hgs acc acc' hlen hw0lt hw0val hrel w hwne
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g List.mem_cons_self
          have hgsop : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
            fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
          simp only [List.map_cons, run, List.foldl_cons]
          have hstep : evalStep acc' (rwConst b0 g) = evalStep acc g := by
            have hmap : ∀ (l : List ℕ), (∀ a ∈ l, a ≠ w0) →
                l.map (fun a => acc'.getD (shift a) false) = l.map (fun a => acc.getD a false) := by
              intro l hl
              apply List.map_congr_left
              intro a ha
              exact hrel a (hl a ha)
            rcases hgop with hop | hop <;> cases hb0 : b0
            · dsimp only [rwConst]; rw [hop]
              split_ifs with hmem
              · rw [eval_or, gate_eq g GateOp.and g.inputs hop rfl, eval_and]
                simp only [List.map_nil, List.any_nil]
                symm
                apply all_eq_false_of_mem
                rw [List.mem_map]
                exact ⟨w0, hmem, by rw [hb0] at hw0val; exact hw0val⟩
              · rw [eval_and]
                conv_rhs => rw [gate_eq g GateOp.and g.inputs hop rfl, eval_and]
                rw [List.map_map, Function.comp_def]
                congr 1
                exact hmap g.inputs (fun a ha heq => hmem (heq ▸ ha))
            · dsimp only [rwConst]; rw [hop]
              rw [eval_and]
              conv_rhs => rw [gate_eq g GateOp.and g.inputs hop rfl, eval_and]
              rw [List.map_map, Function.comp_def]
              have hm1 : (g.inputs.filter (fun w => decide (w ≠ w0))).map
                  (fun x => acc'.getD (shift x) false) =
                  (g.inputs.filter (fun w => decide (w ≠ w0))).map
                  (fun x => acc.getD x false) := by
                apply hmap
                intro a ha
                exact of_decide_eq_true (List.mem_filter.mp ha).2
              refine (congrArg (fun l => l.all id) hm1).trans ?_
              apply all_filter_eq
              intro a _ hpa
              have haeq : a = w0 := by
                by_contra hne
                exact Bool.false_ne_true (hpa.symm.trans (decide_eq_true hne))
              rw [haeq, hw0val, hb0]
            · dsimp only [rwConst]; rw [hop]
              rw [eval_or]
              conv_rhs => rw [gate_eq g GateOp.or g.inputs hop rfl, eval_or]
              rw [List.map_map, Function.comp_def]
              have hm1 : (g.inputs.filter (fun w => decide (w ≠ w0))).map
                  (fun x => acc'.getD (shift x) false) =
                  (g.inputs.filter (fun w => decide (w ≠ w0))).map
                  (fun x => acc.getD x false) := by
                apply hmap
                intro a ha
                exact of_decide_eq_true (List.mem_filter.mp ha).2
              refine (congrArg (fun l => l.any id) hm1).trans ?_
              apply any_filter_eq
              intro a _ hpa
              have haeq : a = w0 := by
                by_contra hne
                exact Bool.false_ne_true (hpa.symm.trans (decide_eq_true hne))
              rw [haeq, hw0val, hb0]
            · dsimp only [rwConst]; rw [hop]
              split_ifs with hmem
              · rw [eval_and, gate_eq g GateOp.or g.inputs hop rfl, eval_or]
                simp only [List.map_nil, List.all_nil]
                symm
                apply any_eq_true_of_mem
                rw [List.mem_map]
                exact ⟨w0, hmem, by rw [hb0] at hw0val; exact hw0val⟩
              · rw [eval_or]
                conv_rhs => rw [gate_eq g GateOp.or g.inputs hop rfl, eval_or]
                rw [List.map_map, Function.comp_def]
                congr 1
                exact hmap g.inputs (fun a ha heq => hmem (heq ▸ ha))
          change (run evalStep (gs.map (rwConst b0)) (acc' ++ [evalStep acc' (rwConst b0 g)])).getD (shift w) false =
            (run evalStep gs (acc ++ [evalStep acc g])).getD w false
          rw [hstep]
          apply ih hgsop (acc ++ [evalStep acc g]) (acc' ++ [evalStep acc g])
          · simp [List.length_append, hlen]
          · simp [List.length_append]; omega
          · rw [List.getD_append _ _ _ _ hw0lt, hw0val]
          · intro u hune
            by_cases hult : u < w0
            · have hrel_u := hrel u hune
              rw [shift_lt u hult] at hrel_u ⊢
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact hrel_u
            · have hugt : w0 < u := by omega
              rw [shift_gt u hult]
              by_cases hu_lt : u < acc.length
              · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hu_lt]
                have hrel_u := hrel u hune
                rwa [shift_gt u hult] at hrel_u
              · by_cases hu_eq : u = acc.length
                · have h1 : (acc' ++ [evalStep acc g]).getD (u - 1) false = evalStep acc g := by
                    rw [List.getD_append_right _ _ _ _ (by omega)]
                    have hsub : u - 1 - acc'.length = 0 := by omega
                    rw [hsub]
                    rfl
                  have h2 : (acc ++ [evalStep acc g]).getD u false = evalStep acc g := by
                    rw [List.getD_append_right _ _ _ _ (by omega)]
                    have hsub : u - acc.length = 0 := by omega
                    rw [hsub]
                    rfl
                  rw [h1, h2]
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          · exact hwne
      change (C'.wires x).getD (shift C.output) false = (C.wires x).getD C.output false
      rw [h_C'_wires, h_full_wires]
      exact h_tail post hpost_op accMid accPre haccMid_len hw0_lt_mid haccMid_w0 h_init_rel C.output hOutNe
    have hC'_deg : C'.lineDeg 26 (Finset.Ico 13 26) ≤ C.lineDeg 26 (Finset.Ico 13 26) := by
      let dPre := run degStep pre degInit
      have hdPre_len : dPre.length = w0 := by
        dsimp [dPre]
        rw [run_length, degInit_length, hlen_pre]
      let dMid := run degStep (pre ++ [C.gates[j]]) degInit
      have hdMid_eq : dMid = dPre ++ [degStep dPre C.gates[j]] := by
        dsimp [dMid, dPre]
        rw [run_append]
        rfl
      have hdMid_len : dMid.length = dPre.length + 1 := by
        rw [hdMid_eq, List.length_append, List.length_singleton]
      have hw0_lt_dmid : w0 < dMid.length := by omega
      have h_full_deg : C.lineDegrees 26 (Finset.Ico 13 26) = run degStep post dMid := by
        rw [lineDegrees_eq, hsplit]
        rw [show pre ++ C.gates[j] :: post = (pre ++ [C.gates[j]]) ++ post by simp [List.append_assoc]]
        rw [run_append]
      have h_C'_deg : C'.lineDegrees 26 (Finset.Ico 13 26) = run degStep (post.map (rwConst b0)) dPre := by
        rw [lineDegrees_eq]
        change run degStep (pre ++ post.map (rwConst b0)) degInit = _
        rw [run_append]
      have h_init_deg : ∀ w, w ≠ w0 → dPre.getD (shift w) 0 ≤ dMid.getD w 0 := by
        intro w hwne
        by_cases hlt : w < w0
        · rw [shift_lt w hlt, hdMid_eq, List.getD_append _ _ _ _ (by omega)]
        · have hgt : w0 < w := by omega
          rw [shift_gt w hlt, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have h_tail_deg : ∀ (gs : List Gate),
          (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
          ∀ (d d' : List ℕ),
          d.length = d'.length + 1 →
          w0 < d.length →
          (∀ w, w ≠ w0 → d'.getD (shift w) 0 ≤ d.getD w 0) →
          ∀ w, w ≠ w0 →
            (run degStep (gs.map (rwConst b0)) d').getD (shift w) 0 ≤
            (run degStep gs d).getD w 0 := by
        intro gs
        induction gs with
        | nil =>
          intro _ d d' _ _ hrel w hwne
          simpa [run] using hrel w hwne
        | cons g gs ih =>
          intro hgs d d' hlen hw0lt hrel w hwne
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g List.mem_cons_self
          have hgsop : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
            fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
          simp only [List.map_cons, run, List.foldl_cons]
          have hstep : degStep d' (rwConst b0 g) ≤ degStep d g := by
            rcases hgop with hop | hop <;> cases hb0 : b0
            · dsimp only [rwConst]; rw [hop]
              split_ifs with hmem
              · dsimp [degStep]
                rw [ld_or]
                simp
              · dsimp [degStep]
                have hg_eq : g = Gate.mk GateOp.and g.inputs := by cases g; simp at hop; subst hop; rfl
                rw [ld_and]
                conv_rhs => rw [hg_eq, ld_and]
                rw [List.map_map]
                apply sum_map_le
                intro a ha
                exact hrel a (fun heq => hmem (heq ▸ ha))
            · dsimp only [rwConst]; rw [hop]
              dsimp [degStep]
              have hg_eq : g = Gate.mk GateOp.and g.inputs := by cases g; simp at hop; subst hop; rfl
              rw [ld_and]
              conv_rhs => rw [hg_eq, ld_and]
              rw [List.map_map]
              refine le_trans (sum_map_le _ _ (fun a => d.getD a 0) ?_) (sum_filter_le _ _ _)
              intro a ha
              exact hrel a (of_decide_eq_true (List.mem_filter.mp ha).2)
            · dsimp only [rwConst]; rw [hop]
              dsimp [degStep]
              have hg_eq : g = Gate.mk GateOp.or g.inputs := by cases g; simp at hop; subst hop; rfl
              rw [ld_or]
              conv_rhs => rw [hg_eq, ld_or]
              rw [List.map_map]
              refine le_trans (max_map_le _ _ (fun a => d.getD a 0) ?_) (max_filter_le _ _ _)
              intro a ha
              exact hrel a (of_decide_eq_true (List.mem_filter.mp ha).2)
            · dsimp only [rwConst]; rw [hop]
              split_ifs with hmem
              · dsimp [degStep]
                rw [ld_and]
                simp
              · dsimp [degStep]
                have hg_eq : g = Gate.mk GateOp.or g.inputs := by cases g; simp at hop; subst hop; rfl
                rw [ld_or]
                conv_rhs => rw [hg_eq, ld_or]
                rw [List.map_map]
                apply max_map_le
                intro a ha
                exact hrel a (fun heq => hmem (heq ▸ ha))
          change (run degStep (gs.map (rwConst b0)) (d' ++ [degStep d' (rwConst b0 g)])).getD (shift w) 0 ≤
            (run degStep gs (d ++ [degStep d g])).getD w 0
          apply ih hgsop (d ++ [degStep d g]) (d' ++ [degStep d' (rwConst b0 g)])
          · simp [List.length_append, hlen]
          · simp [List.length_append]; omega
          · intro u hune
            by_cases hult : u < w0
            · have hrel_u := hrel u hune
              rw [shift_lt u hult] at hrel_u ⊢
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact hrel_u
            · have hugt : w0 < u := by omega
              rw [shift_gt u hult]
              by_cases hu_lt : u < d.length
              · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hu_lt]
                have hrel_u := hrel u hune
                rwa [shift_gt u hult] at hrel_u
              · by_cases hu_eq : u = d.length
                · have h1 : (d' ++ [degStep d' (rwConst b0 g)]).getD (u - 1) 0 = degStep d' (rwConst b0 g) := by
                    rw [List.getD_append_right _ _ _ _ (by omega)]
                    have hsub : u - 1 - d'.length = 0 := by omega
                    rw [hsub]
                    rfl
                  have h2 : (d ++ [degStep d g]).getD u 0 = degStep d g := by
                    rw [List.getD_append_right _ _ _ _ (by omega)]
                    have hsub : u - d.length = 0 := by omega
                    rw [hsub]
                    rfl
                  rw [h1, h2]
                  exact hstep
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          · exact hwne
      change (C'.lineDegrees 26 (Finset.Ico 13 26)).getD (shift C.output) 0 ≤
        (C.lineDegrees 26 (Finset.Ico 13 26)).getD C.output 0
      rw [h_C'_deg, h_full_deg]
      exact h_tail_deg post hpost_op dMid dPre hdMid_len hw0_lt_dmid h_init_deg C.output hOutNe
    exact ⟨C', hC'_size, hC'_mono, hC'_eval, hC'_deg⟩
  have delAlias : ∀ (C : Circuit), Monotone2 C → ComputesIncidence singerLines3 C →
      ∀ (j : ℕ), j < C.gates.length → ∀ (u : ℕ), u < 26 + j →
      (∀ x : List Bool, x.length = 26 → (C.wires x).getD (26 + j) false = (C.wires x).getD u false) →
      (C.lineDegrees 26 (Finset.Ico 13 26)).getD u 0 ≤ (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 →
      ∃ C' : Circuit, C'.size < C.size ∧ Monotone2 C' ∧ ComputesIncidence singerLines3 C' ∧
        C'.lineDeg 26 (Finset.Ico 13 26) ≤ C.lineDeg 26 (Finset.Ico 13 26) := by
    intro C hm hc j hj u hu halias hdeg_le
    let w0 : ℕ := 26 + j
    let remap : ℕ → ℕ := fun w => if w < w0 then w else if w = w0 then u else w - 1
    have remap_lt : ∀ w, w < w0 → remap w = w := fun w hw => by dsimp only [remap]; split_ifs; rfl
    have remap_eq : remap w0 = u := by dsimp only [remap]; split_ifs <;> omega
    have remap_gt : ∀ w, w0 < w → remap w = w - 1 := fun w hw => by dsimp only [remap]; split_ifs <;> omega
    let rwAlias (g : Gate) : Gate := ⟨g.op, g.inputs.map remap⟩
    let pre := C.gates.take j
    let post := C.gates.drop (j + 1)
    let C' : Circuit := ⟨pre ++ post.map rwAlias, remap C.output⟩
    have hsplit : C.gates = pre ++ C.gates[j] :: post := list_split_at C.gates j hj
    have hlen_pre : pre.length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hpost_op : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      simpa using (hm g (List.mem_of_mem_drop hg)).1
    have hC'_size : C'.size < C.size := by
      show (pre ++ post.map rwAlias).length < C.gates.length
      rw [hsplit]
      simp [List.length_append, List.length_map]
    have hC'_mono : Monotone2 C' := by
      intro g hg
      simp only [C', List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g0, hg0, rfl⟩
      · exact hm g (List.mem_of_mem_take hg)
      · have hm0 := hm g0 (List.mem_of_mem_drop hg0)
        exact ⟨hm0.1, by simpa [rwAlias] using hm0.2⟩
    have hC'_eval : ComputesIncidence singerLines3 C' := by
      intro X Y
      rw [← hc X Y]
      let x := incidenceInput X Y
      have hxlen : x.length = 26 := inc_len X Y
      let accPre := run evalStep pre x
      have haccPre_len : accPre.length = w0 := by
        dsimp [accPre]
        rw [run_length, hxlen, hlen_pre]
      let accMid := run evalStep (pre ++ [C.gates[j]]) x
      have haccMid_eq : accMid = accPre ++ [evalStep accPre C.gates[j]] := by
        dsimp [accMid, accPre]
        rw [run_append]
        rfl
      have haccMid_len : accMid.length = accPre.length + 1 := by
        rw [haccMid_eq, List.length_append, List.length_singleton]
      have hw0_lt_mid : w0 < accMid.length := by omega
      have h_full_wires : C.wires x = run evalStep post accMid := by
        rw [wires_eq, hsplit]
        rw [show pre ++ C.gates[j] :: post = (pre ++ [C.gates[j]]) ++ post by simp [List.append_assoc]]
        rw [run_append]
      have h_C'_wires : C'.wires x = run evalStep (post.map rwAlias) accPre := by
        rw [wires_eq]
        change run evalStep (pre ++ post.map rwAlias) x = _
        rw [run_append]
      have h_init_rel : ∀ w, accPre.getD (remap w) false = accMid.getD w false := by
        intro w
        by_cases hlt : w < w0
        · rw [remap_lt w hlt, haccMid_eq, List.getD_append _ _ _ _ (by omega)]
        · by_cases heq : w = w0
          · subst heq
            rw [remap_eq]
            have h1 : accPre.getD u false = accMid.getD u false := by
              rw [haccMid_eq, List.getD_append _ _ _ _ (by omega)]
            have h2 : (C.wires x).getD u false = accMid.getD u false := by
              rw [h_full_wires]
              exact run_getD_lt false evalStep post accMid u (by omega)
            have h3 : (C.wires x).getD w0 false = accMid.getD w0 false := by
              rw [h_full_wires]
              exact run_getD_lt false evalStep post accMid w0 hw0_lt_mid
            rw [h1, ← h2, ← h3]
            exact (halias x hxlen).symm
          · have hgt : w0 < w := by omega
            rw [remap_gt w hgt, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have h_tail : ∀ (gs : List Gate) (acc acc' : List Bool),
          acc.length = acc'.length + 1 →
          w0 < acc.length →
          (∀ w, acc'.getD (remap w) false = acc.getD w false) →
          ∀ w,
            (run evalStep (gs.map rwAlias) acc').getD (remap w) false =
            (run evalStep gs acc).getD w false := by
        intro gs
        induction gs with
        | nil =>
          intro acc acc' _ _ hrel w
          simpa [run] using hrel w
        | cons g gs ih =>
          intro acc acc' hlen hw0lt hrel w
          simp only [List.map_cons, run, List.foldl_cons]
          have hstep : evalStep acc' (rwAlias g) = evalStep acc g := by
            dsimp [evalStep, rwAlias]
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro a _
            exact hrel a
          change (run evalStep (gs.map rwAlias) (acc' ++ [evalStep acc' (rwAlias g)])).getD (remap w) false =
            (run evalStep gs (acc ++ [evalStep acc g])).getD w false
          rw [hstep]
          apply ih (acc ++ [evalStep acc g]) (acc' ++ [evalStep acc g])
          · simp [List.length_append, hlen]
          · simp [List.length_append]; omega
          · intro z
            by_cases hzlt : z < w0
            · have hz := hrel z
              rw [remap_lt z hzlt] at hz ⊢
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact hz
            · by_cases hzeq : z = w0
              · subst hzeq
                have hz := hrel w0
                rw [remap_eq] at hz ⊢
                rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hw0lt]
                exact hz
              · have hzgt : w0 < z := by omega
                rw [remap_gt z hzgt]
                by_cases hz_lt : z < acc.length
                · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hz_lt]
                  have hz := hrel z
                  rwa [remap_gt z hzgt] at hz
                · by_cases hz_eq : z = acc.length
                  · have h1 : (acc' ++ [evalStep acc g]).getD (z - 1) false = evalStep acc g := by
                      rw [List.getD_append_right _ _ _ _ (by omega)]
                      have hsub : z - 1 - acc'.length = 0 := by omega
                      rw [hsub]
                      rfl
                    have h2 : (acc ++ [evalStep acc g]).getD z false = evalStep acc g := by
                      rw [List.getD_append_right _ _ _ _ (by omega)]
                      have hsub : z - acc.length = 0 := by omega
                      rw [hsub]
                      rfl
                    rw [h1, h2]
                  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      change (C'.wires x).getD (remap C.output) false = (C.wires x).getD C.output false
      rw [h_C'_wires, h_full_wires]
      exact h_tail post accMid accPre haccMid_len hw0_lt_mid h_init_rel C.output
    have hC'_deg : C'.lineDeg 26 (Finset.Ico 13 26) ≤ C.lineDeg 26 (Finset.Ico 13 26) := by
      let dPre := run degStep pre degInit
      have hdPre_len : dPre.length = w0 := by
        dsimp [dPre]
        rw [run_length, degInit_length, hlen_pre]
      let dMid := run degStep (pre ++ [C.gates[j]]) degInit
      have hdMid_eq : dMid = dPre ++ [degStep dPre C.gates[j]] := by
        dsimp [dMid, dPre]
        rw [run_append]
        rfl
      have hdMid_len : dMid.length = dPre.length + 1 := by
        rw [hdMid_eq, List.length_append, List.length_singleton]
      have hw0_lt_dmid : w0 < dMid.length := by omega
      have h_full_deg : C.lineDegrees 26 (Finset.Ico 13 26) = run degStep post dMid := by
        rw [lineDegrees_eq, hsplit]
        rw [show pre ++ C.gates[j] :: post = (pre ++ [C.gates[j]]) ++ post by simp [List.append_assoc]]
        rw [run_append]
      have h_C'_deg : C'.lineDegrees 26 (Finset.Ico 13 26) = run degStep (post.map rwAlias) dPre := by
        rw [lineDegrees_eq]
        change run degStep (pre ++ post.map rwAlias) degInit = _
        rw [run_append]
      have h_init_deg : ∀ w, dPre.getD (remap w) 0 ≤ dMid.getD w 0 := by
        intro w
        by_cases hlt : w < w0
        · rw [remap_lt w hlt, hdMid_eq, List.getD_append _ _ _ _ (by omega)]
        · by_cases heq : w = w0
          · subst heq
            rw [remap_eq]
            have h1 : dPre.getD u 0 = dMid.getD u 0 := by
              rw [hdMid_eq, List.getD_append _ _ _ _ (by omega)]
            have h2 : (C.lineDegrees 26 (Finset.Ico 13 26)).getD u 0 = dMid.getD u 0 := by
              rw [h_full_deg]
              exact run_getD_lt 0 degStep post dMid u (by omega)
            have h3 : (C.lineDegrees 26 (Finset.Ico 13 26)).getD w0 0 = dMid.getD w0 0 := by
              rw [h_full_deg]
              exact run_getD_lt 0 degStep post dMid w0 hw0_lt_dmid
            rw [h1, ← h2, ← h3]
            exact hdeg_le
          · have hgt : w0 < w := by omega
            rw [remap_gt w hgt, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have h_tail_deg : ∀ (gs : List Gate),
          (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
          ∀ (d d' : List ℕ),
          d.length = d'.length + 1 →
          w0 < d.length →
          (∀ w, d'.getD (remap w) 0 ≤ d.getD w 0) →
          ∀ w,
            (run degStep (gs.map rwAlias) d').getD (remap w) 0 ≤
            (run degStep gs d).getD w 0 := by
        intro gs
        induction gs with
        | nil =>
          intro _ d d' _ _ hrel w
          simpa [run] using hrel w
        | cons g gs ih =>
          intro hgs d d' hlen hw0lt hrel w
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g List.mem_cons_self
          have hgsop : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
            fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
          simp only [List.map_cons, run, List.foldl_cons]
          have hstep : degStep d' (rwAlias g) ≤ degStep d g := by
            rcases hgop with hop | hop
            · have hg_eq : g = Gate.mk GateOp.and g.inputs := by cases g; simp at hop; subst hop; rfl
              dsimp [degStep, rwAlias]
              rw [hop, ld_and]
              conv_rhs => rw [hg_eq, ld_and]
              rw [List.map_map]
              apply sum_map_le
              intro a _
              exact hrel a
            · have hg_eq : g = Gate.mk GateOp.or g.inputs := by cases g; simp at hop; subst hop; rfl
              dsimp [degStep, rwAlias]
              rw [hop, ld_or]
              conv_rhs => rw [hg_eq, ld_or]
              rw [List.map_map]
              apply max_map_le
              intro a _
              exact hrel a
          change (run degStep (gs.map rwAlias) (d' ++ [degStep d' (rwAlias g)])).getD (remap w) 0 ≤
            (run degStep gs (d ++ [degStep d g])).getD w 0
          apply ih hgsop (d ++ [degStep d g]) (d' ++ [degStep d' (rwAlias g)])
          · simp [List.length_append, hlen]
          · simp [List.length_append]; omega
          · intro z
            by_cases hzlt : z < w0
            · have hz := hrel z
              rw [remap_lt z hzlt] at hz ⊢
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact hz
            · by_cases hzeq : z = w0
              · subst hzeq
                have hz := hrel w0
                rw [remap_eq] at hz ⊢
                rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hw0lt]
                exact hz
              · have hzgt : w0 < z := by omega
                rw [remap_gt z hzgt]
                by_cases hz_lt : z < d.length
                · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hz_lt]
                  have hz := hrel z
                  rwa [remap_gt z hzgt] at hz
                · by_cases hz_eq : z = d.length
                  · have h1 : (d' ++ [degStep d' (rwAlias g)]).getD (z - 1) 0 = degStep d' (rwAlias g) := by
                      rw [List.getD_append_right _ _ _ _ (by omega)]
                      have hsub : z - 1 - d'.length = 0 := by omega
                      rw [hsub]
                      rfl
                    have h2 : (d ++ [degStep d g]).getD z 0 = degStep d g := by
                      rw [List.getD_append_right _ _ _ _ (by omega)]
                      have hsub : z - d.length = 0 := by omega
                      rw [hsub]
                      rfl
                    rw [h1, h2]
                    exact hstep
                  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      change (C'.lineDegrees 26 (Finset.Ico 13 26)).getD (remap C.output) 0 ≤
        (C.lineDegrees 26 (Finset.Ico 13 26)).getD C.output 0
      rw [h_C'_deg, h_full_deg]
      exact h_tail_deg post hpost_op dMid dPre hdMid_len hw0_lt_dmid h_init_deg C.output
    exact ⟨C', hC'_size, hC'_mono, hC'_eval, hC'_deg⟩
  have main_ind : ∀ (n : ℕ) (C : Circuit), C.size = n →
      Monotone2 C → ComputesIncidence singerLines3 C →
      HasLineDegree 26 (Finset.Ico 13 26) C 2 → 64 ≤ C.size := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro C hCsz hm hc hd
      by_cases h1 : C.lineDeg 26 (Finset.Ico 13 26) ≤ 1
      · exact from_deg1 C hm hc h1
      · have hd2 : C.lineDeg 26 (Finset.Ico 13 26) = 2 := by
          change C.lineDeg 26 (Finset.Ico 13 26) ≤ 2 at hd
          omega
        by_cases hclean : ReadsBack 26 C ∧ (∀ g ∈ C.gates, g.inputs.length = 2) ∧
            (∀ g ∈ C.gates, g.inputs.Nodup)
        · obtain ⟨hRB, hLen2, hNodup⟩ := hclean
          have hAO2 : IsAO2 26 C := by
            refine ⟨?_, hRB, hLen2⟩
            intro g hg
            simpa using (hm g hg).1
          have hOutGe : 26 ≤ C.output := by
            by_contra hlt
            have hlt' : C.output < 26 := Nat.lt_of_not_ge hlt
            have hdeg_le : C.lineDeg 26 (Finset.Ico 13 26) ≤ 1 := by
              change (run degStep C.gates degInit).getD C.output 0 ≤ 1
              rw [run_getD_lt 0 degStep C.gates degInit C.output (by rw [degInit_length]; exact hlt')]
              exact degInit_getD_le C.output
            omega
          have hOutLt : C.output < 26 + C.size := by
            by_contra hge
            have hge' : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
            have hdeg0 : C.lineDeg 26 (Finset.Ico 13 26) = 0 := by
              change (run degStep C.gates degInit).getD C.output 0 = 0
              apply List.getD_eq_default
              rw [run_length, degInit_length]
              exact hge'
            omega
          by_cases hlast : C.output + 1 = 26 + C.size
          · exact exactTwoAO2 C hAO2 hNodup hc hd2 hlast
          · have hk_lt : C.output - 26 + 1 < C.size := by omega
            let k := C.output - 26 + 1
            let D : Circuit := ⟨C.gates.take k, C.output⟩
            have hDsz : D.size = k := by
              change (C.gates.take k).length = k
              exact List.length_take_of_le (Nat.le_of_lt hk_lt)
            have hDlt : D.size < n := by rw [← hCsz, hDsz]; exact hk_lt
            have hDmono : Monotone2 D := by
              intro g hg
              exact hm g (List.mem_of_mem_take hg)
            have hsplit : C.gates = C.gates.take k ++ C.gates.drop k :=
              (List.take_append_drop k C.gates).symm
            have hDeval : ComputesIncidence singerLines3 D := by
              intro X Y
              rw [← hc X Y]
              let x := incidenceInput X Y
              have hxlen : x.length = 26 := inc_len X Y
              have hlenD : (D.wires x).length = 26 + k := by
                rw [wires_eq]
                change (run evalStep (C.gates.take k) x).length = 26 + k
                rw [run_length, hxlen, List.length_take_of_le (Nat.le_of_lt hk_lt)]
              have hCeq : C.wires x = run evalStep (C.gates.drop k) (D.wires x) := by
                rw [wires_eq, wires_eq]
                conv_lhs => rw [hsplit]
                rw [run_append]
              change (D.wires x).getD C.output false = (C.wires x).getD C.output false
              rw [hCeq]
              exact (run_getD_lt false evalStep (C.gates.drop k) (D.wires x) C.output (by omega)).symm
            have hDdeg : HasLineDegree 26 (Finset.Ico 13 26) D 2 := by
              change (D.lineDegrees 26 (Finset.Ico 13 26)).getD C.output 0 ≤ 2
              have hlenDd : (D.lineDegrees 26 (Finset.Ico 13 26)).length = 26 + k := by
                rw [lineDegrees_eq]
                change (run degStep (C.gates.take k) degInit).length = 26 + k
                rw [run_length, degInit_length, List.length_take_of_le (Nat.le_of_lt hk_lt)]
              have hCdeq : C.lineDegrees 26 (Finset.Ico 13 26) =
                  run degStep (C.gates.drop k) (D.lineDegrees 26 (Finset.Ico 13 26)) := by
                rw [lineDegrees_eq, lineDegrees_eq]
                conv_lhs => rw [hsplit]
                rw [run_append]
              have heq : (D.lineDegrees 26 (Finset.Ico 13 26)).getD C.output 0 =
                  (C.lineDegrees 26 (Finset.Ico 13 26)).getD C.output 0 := by
                rw [hCdeq]
                exact (run_getD_lt 0 degStep (C.gates.drop k) (D.lineDegrees 26 (Finset.Ico 13 26))
                  C.output (by omega)).symm
              rw [heq]
              exact hd
            have h64 : 64 ≤ D.size := ih D.size hDlt D rfl hDmono hDeval hDdeg
            omega
        · have hbad : ∃ j : ℕ, ∃ hj : j < C.gates.length,
              ¬ (∀ i ∈ C.gates[j].inputs, i < 26 + j) ∨
              C.gates[j].inputs.length ≠ 2 ∨ ¬ C.gates[j].inputs.Nodup := by
            by_cases h1rb : ReadsBack 26 C
            · by_cases h2len : ∀ g ∈ C.gates, g.inputs.length = 2
              · have h3nd : ¬ ∀ g ∈ C.gates, g.inputs.Nodup := fun h => hclean ⟨h1rb, h2len, h⟩
                push Not at h3nd
                obtain ⟨g, hg, hnd⟩ := h3nd
                obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
                exact ⟨j, hj, Or.inr (Or.inr hnd)⟩
              · push Not at h2len
                obtain ⟨g, hg, hne⟩ := h2len
                obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
                exact ⟨j, hj, Or.inr (Or.inl hne)⟩
            · unfold ReadsBack at h1rb
              push Not at h1rb
              obtain ⟨j, hj, i, hi, hij⟩ := h1rb
              have hgate : gateAt C j = C.gates[j] := by
                unfold gateAt
                exact List.getD_eq_getElem _ _ hj
              rw [hgate] at hi
              exact ⟨j, hj, Or.inl (fun h => absurd (h i hi) (Nat.not_lt.mpr hij))⟩
          obtain ⟨j, hj, hbadj⟩ := hbad
          let g0 := C.gates[j]
          have hm0 := hm g0 (List.getElem_mem hj)
          have hop : g0.op = GateOp.and ∨ g0.op = GateOp.or := by simpa using hm0.1
          have hlen0 : g0.inputs.length ≤ 2 := hm0.2
          have hsplit : C.gates = C.gates.take j ++ g0 :: C.gates.drop (j + 1) :=
            list_split_at C.gates j hj
          have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
          have hwire_j : ∀ (x : List Bool), x.length = 26 →
              let accPre := run evalStep (C.gates.take j) x
              accPre.length = 26 + j ∧
              (C.wires x).getD (26 + j) false = evalStep accPre g0 ∧
              (∀ u < 26 + j, (C.wires x).getD u false = accPre.getD u false) := by
            intro x hxlen
            let accPre := run evalStep (C.gates.take j) x
            have hlen_pre : accPre.length = 26 + j := by
              dsimp [accPre]
              rw [run_length, hxlen, htake_len]
            let accMid := accPre ++ [evalStep accPre g0]
            have hlen_mid : accMid.length = 26 + j + 1 := by
              simp [accMid, hlen_pre]
            have hfull : C.wires x = run evalStep (C.gates.drop (j + 1)) accMid := by
              rw [wires_eq]
              conv_lhs => rw [hsplit]
              rw [show C.gates.take j ++ g0 :: C.gates.drop (j + 1) =
                (C.gates.take j ++ [g0]) ++ C.gates.drop (j + 1) by simp [List.append_assoc]]
              rw [run_append]
              have hmid_eq : run evalStep (C.gates.take j ++ [g0]) x = accMid := by
                rw [run_append]
                rfl
              rw [hmid_eq]
            refine ⟨hlen_pre, ?_, ?_⟩
            · rw [hfull, run_getD_lt false evalStep _ accMid (26 + j) (by omega)]
              dsimp [accMid]
              rw [List.getD_append_right _ _ _ _ (by omega)]
              have hsub : 26 + j - accPre.length = 0 := by omega
              rw [hsub]
              rfl
            · intro u hu
              rw [hfull, run_getD_lt false evalStep _ accMid u (by omega)]
              dsimp [accMid]
              exact List.getD_append _ _ _ _ (by omega)
          have hdeg_j :
              let dPre := run degStep (C.gates.take j) degInit
              dPre.length = 26 + j ∧
              (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 = degStep dPre g0 ∧
              (∀ u < 26 + j, (C.lineDegrees 26 (Finset.Ico 13 26)).getD u 0 = dPre.getD u 0) := by
            let dPre := run degStep (C.gates.take j) degInit
            have hlen_pre : dPre.length = 26 + j := by
              dsimp [dPre]
              rw [run_length, degInit_length, htake_len]
            let dMid := dPre ++ [degStep dPre g0]
            have hfull : C.lineDegrees 26 (Finset.Ico 13 26) =
                run degStep (C.gates.drop (j + 1)) dMid := by
              rw [lineDegrees_eq]
              conv_lhs => rw [hsplit]
              rw [show C.gates.take j ++ g0 :: C.gates.drop (j + 1) =
                (C.gates.take j ++ [g0]) ++ C.gates.drop (j + 1) by simp [List.append_assoc]]
              rw [run_append]
              have hmid_eq : run degStep (C.gates.take j ++ [g0]) degInit = dMid := by
                rw [run_append]
                rfl
              rw [hmid_eq]
            refine ⟨hlen_pre, ?_, ?_⟩
            · rw [hfull, run_getD_lt 0 degStep _ dMid (26 + j) (by simp [dMid, hlen_pre])]
              dsimp [dMid]
              rw [List.getD_append_right _ _ _ _ (by omega)]
              have hsub : 26 + j - dPre.length = 0 := by omega
              rw [hsub]
              rfl
            · intro u hu
              rw [hfull, run_getD_lt 0 degStep _ dMid u (by simp [dMid, hlen_pre]; omega)]
              dsimp [dMid]
              exact List.getD_append _ _ _ _ (by omega)
          have finish_const : ∀ b0 : Bool,
              (∀ x : List Bool, x.length = 26 → (C.wires x).getD (26 + j) false = b0) →
              64 ≤ C.size := by
            intro b0 hconst
            obtain ⟨C', hC'sz, hC'm, hC'e, hC'd⟩ := delConst C hm hc j hj b0 hconst
            have hC'hd : HasLineDegree 26 (Finset.Ico 13 26) C' 2 := by
              change C'.lineDeg 26 (Finset.Ico 13 26) ≤ 2
              omega
            have h64 := ih C'.size (by rw [← hCsz]; exact hC'sz) C' rfl hC'm hC'e hC'hd
            omega
          have finish_alias : ∀ u : ℕ, u < 26 + j →
              (∀ x : List Bool, x.length = 26 → (C.wires x).getD (26 + j) false = (C.wires x).getD u false) →
              (C.lineDegrees 26 (Finset.Ico 13 26)).getD u 0 ≤
                (C.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + j) 0 →
              64 ≤ C.size := by
            intro u hu halias hdu
            obtain ⟨C', hC'sz, hC'm, hC'e, hC'd⟩ := delAlias C hm hc j hj u hu halias hdu
            have hC'hd : HasLineDegree 26 (Finset.Ico 13 26) C' 2 := by
              change C'.lineDeg 26 (Finset.Ico 13 26) ≤ 2
              omega
            have h64 := ih C'.size (by rw [← hCsz]; exact hC'sz) C' rfl hC'm hC'e hC'hd
            omega
          cases hin : g0.inputs with
          | nil =>
            rcases hop with hop | hop
            · refine finish_const true (fun x hx => ?_)
              obtain ⟨_, hw, _⟩ := hwire_j x hx
              rw [hw, gate_eq g0 GateOp.and [] hop hin, eval_and]
              rfl
            · refine finish_const false (fun x hx => ?_)
              obtain ⟨_, hw, _⟩ := hwire_j x hx
              rw [hw, gate_eq g0 GateOp.or [] hop hin, eval_or]
              rfl
          | cons a rest =>
            cases rest with
            | nil =>
              by_cases ha : a < 26 + j
              · refine finish_alias a ha (fun x hx => ?_) ?_
                · obtain ⟨_, hw, hu⟩ := hwire_j x hx
                  rw [hw, hu a ha]
                  rcases hop with hop | hop
                  · rw [gate_eq g0 GateOp.and [a] hop hin, eval_and]; simp
                  · rw [gate_eq g0 GateOp.or [a] hop hin, eval_or]; simp
                · obtain ⟨_, hdw, hdu⟩ := hdeg_j
                  rw [hdw, hdu a ha]
                  dsimp [degStep]
                  rcases hop with hop | hop
                  · rw [gate_eq g0 GateOp.and [a] hop hin, ld_and]
                    simp
                  · rw [gate_eq g0 GateOp.or [a] hop hin, ld_or]
                    simp
              · refine finish_const false (fun x hx => ?_)
                obtain ⟨hlen_pre, hw, _⟩ := hwire_j x hx
                rw [hw]
                have hdef : (run evalStep (C.gates.take j) x).getD a false = false :=
                  List.getD_eq_default _ _ (by omega)
                rcases hop with hop | hop
                · rw [gate_eq g0 GateOp.and [a] hop hin, eval_and]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
                  rw [hdef]
                  rfl
                · rw [gate_eq g0 GateOp.or [a] hop hin, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
                  rw [hdef]
                  rfl
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                by_cases ha : a < 26 + j
                · by_cases hb : b < 26 + j
                  · have hab : a = b := by
                      rcases hbadj with hrb | hlen2 | hnd
                      · exfalso
                        apply hrb
                        intro i hi
                        rw [hin] at hi
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl <;> assumption
                      · exfalso
                        apply hlen2
                        rw [hin]
                        rfl
                      · rw [hin] at hnd
                        simpa using hnd
                    subst hab
                    refine finish_alias a ha (fun x hx => ?_) ?_
                    · obtain ⟨_, hw, hu⟩ := hwire_j x hx
                      rw [hw, hu a ha]
                      rcases hop with hop | hop
                      · rw [gate_eq g0 GateOp.and [a, a] hop hin, eval_and]
                        simp
                      · rw [gate_eq g0 GateOp.or [a, a] hop hin, eval_or]
                        simp
                    · obtain ⟨_, hdw, hdu⟩ := hdeg_j
                      rw [hdw, hdu a ha]
                      dsimp [degStep]
                      rcases hop with hop | hop
                      · rw [gate_eq g0 GateOp.and [a, a] hop hin, ld_and]
                        simp
                      · rw [gate_eq g0 GateOp.or [a, a] hop hin, ld_or]
                        simp
                  · rcases hop with hop | hop
                    · refine finish_const false (fun x hx => ?_)
                      obtain ⟨hlen_pre, hw, _⟩ := hwire_j x hx
                      rw [hw]
                      have hdef : (run evalStep (C.gates.take j) x).getD b false = false :=
                        List.getD_eq_default _ _ (by omega)
                      rw [gate_eq g0 GateOp.and [a, b] hop hin, eval_and]
                      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
                      rw [hdef]
                      simp
                    · refine finish_alias a ha (fun x hx => ?_) ?_
                      · obtain ⟨hlen_pre, hw, hu⟩ := hwire_j x hx
                        rw [hw, hu a ha]
                        have hdef : (run evalStep (C.gates.take j) x).getD b false = false :=
                          List.getD_eq_default _ _ (by omega)
                        rw [gate_eq g0 GateOp.or [a, b] hop hin, eval_or]
                        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
                        rw [hdef]
                        simp
                      · obtain ⟨_, hdw, hdu⟩ := hdeg_j
                        rw [hdw, hdu a ha]
                        dsimp [degStep]
                        rw [gate_eq g0 GateOp.or [a, b] hop hin, ld_or]
                        simp
                · rcases hop with hop | hop
                  · refine finish_const false (fun x hx => ?_)
                    obtain ⟨hlen_pre, hw, _⟩ := hwire_j x hx
                    rw [hw]
                    have hdef : (run evalStep (C.gates.take j) x).getD a false = false :=
                      List.getD_eq_default _ _ (by omega)
                    rw [gate_eq g0 GateOp.and [a, b] hop hin, eval_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
                    rw [hdef]
                    simp
                  · by_cases hb : b < 26 + j
                    · refine finish_alias b hb (fun x hx => ?_) ?_
                      · obtain ⟨hlen_pre, hw, hu⟩ := hwire_j x hx
                        rw [hw, hu b hb]
                        have hdef : (run evalStep (C.gates.take j) x).getD a false = false :=
                          List.getD_eq_default _ _ (by omega)
                        rw [gate_eq g0 GateOp.or [a, b] hop hin, eval_or]
                        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
                        rw [hdef]
                        simp
                      · obtain ⟨_, hdw, hdu⟩ := hdeg_j
                        rw [hdw, hdu b hb]
                        dsimp [degStep]
                        rw [gate_eq g0 GateOp.or [a, b] hop hin, ld_or]
                        simp
                    · refine finish_const false (fun x hx => ?_)
                      obtain ⟨hlen_pre, hw, _⟩ := hwire_j x hx
                      rw [hw]
                      have hdefa : (run evalStep (C.gates.take j) x).getD a false = false :=
                        List.getD_eq_default _ _ (by omega)
                      have hdefb : (run evalStep (C.gates.take j) x).getD b false = false :=
                        List.getD_eq_default _ _ (by omega)
                      rw [gate_eq g0 GateOp.or [a, b] hop hin, eval_or]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
                      rw [hdefa, hdefb]
                      rfl
              | cons c rest3 =>
                exfalso
                rw [hin] at hlen0
                simp at hlen0
  intro x1 hm hc hd
  exact main_ind x1.size x1 rfl hm hc hd
