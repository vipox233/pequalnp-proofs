import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27479

open PEqualNP.CircuitLowerBounds

private def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

-- The rows for wires 1 and 3 also set the other input of the initial OR.
private def base (v : ℕ) : List ℕ :=
  [[4, 8], [3, 5, 6], [3, 7], [1, 2, 7], [0, 8],
   [0, 7], [1, 5], [0, 5], [0, 4]].getD v []

private def row (v : ℕ) (b : Bool) (i : Fin 9) : Bool :=
  (b && (i.val == v)) || (base v).contains i.val

private lemma matching_rows (v : Fin 9) :
    matching (row v false) = false ∧ matching (row v true) = true := by
  revert v
  decide +kernel

private lemma or_rows (v : Fin 9) : (row v false 1 || row v false 3) =
    (row v true 1 || row v true 3) := by
  revert v
  decide +kernel

private lemma row_eq {v : ℕ} {i : Fin 9} (h : i.val ≠ v) :
    row v false i = row v true i := by
  simp [row, h]

private lemma readInput {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i false = x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.getD_some]

private lemma read_rows_eq (v k : ℕ) (hk : k ≠ v) :
    (List.ofFn (row v false)).getD k false = (List.ofFn (row v true)).getD k false := by
  by_cases h : k < 9
  · rw [readInput (row v false) ⟨k, h⟩, readInput (row v true) ⟨k, h⟩]
    exact row_eq hk
  · have hd (b : Bool) : (List.ofFn (row v b)).getD k false = false :=
      List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt h)
    rw [hd false, hd true]

private def first : Gate := ⟨.not, [0]⟩
private def second : Gate := ⟨.or, [1, 3]⟩

private def addWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma prefixWires (x : Fin 9 → Bool) :
    [first, second].foldl addWire (List.ofFn x) =
      List.ofFn x ++ [!(x 0), x 1 || x 3] := by
  simp [addWire, first, second, GateOp.eval, List.ofFn_succ]

private lemma eval_rest (gs : List Gate) (o : ℕ) (x : Fin 9 → Bool) :
    (⟨first :: second :: gs, o⟩ : Circuit).eval (List.ofFn x) =
      (gs.foldl addWire (List.ofFn x ++ [!(x 0), x 1 || x 3])).getD o false := by
  change (gs.foldl addWire ([first, second].foldl addWire (List.ofFn x))).getD o false = _
  rw [prefixWires]

private def AgreeExcept (v : ℕ) (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ ∀ k, k ≠ v → xs.getD k false = ys.getD k false

private lemma agree_append {v : ℕ} {xs ys : List Bool} (h : AgreeExcept v xs ys)
    (zs : List Bool) : AgreeExcept v (xs ++ zs) (ys ++ zs) := by
  refine ⟨by simp [h.1], ?_⟩
  intro k hk
  by_cases hlt : k < xs.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (h.1 ▸ hlt)]
    exact h.2 k hk
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hlt),
      List.getD_append_right _ _ _ _ (h.1 ▸ Nat.le_of_not_gt hlt), h.1]

private lemma agree_fold (gs : List Gate) {v : ℕ} {xs ys : List Bool}
    (hMissing : v ∉ gs.flatMap Gate.inputs) (h : AgreeExcept v xs ys) :
    AgreeExcept v (gs.foldl addWire xs) (gs.foldl addWire ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    rw [List.flatMap_cons, List.mem_append, not_or] at hMissing
    have hm : g.inputs.map (fun k => xs.getD k false) =
        g.inputs.map (fun k => ys.getD k false) :=
      List.map_congr_left (fun k hk => h.2 k (fun e => hMissing.1 (e ▸ hk)))
    simp only [List.foldl_cons, addWire, hm]
    exact ih hMissing.2 (agree_append h _)

private def Normal (gs : List Gate) : Prop :=
  ∀ j : Fin gs.length,
    ((gs.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (gs.get j).inputs = [a]) ∨
    (((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (gs.get j).inputs = [a, b])

private def Live (gs : List Gate) : Prop :=
  ∀ j : Fin gs.length, j.val + 1 < gs.length →
    ∃ k : Fin gs.length, j.val < k.val ∧ 9 + j.val ∈ (gs.get k).inputs

private lemma normal_gate {gs : List Gate} (h : Normal gs) {g : Gate} (hg : g ∈ gs) :
    (g.op = .not ∧ g.inputs.length = 1) ∨
    ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
  rcases h j with ⟨hop, a, _, hinput⟩ | ⟨hop, a, b, _, _, hinput⟩
  · exact Or.inl ⟨hop, congrArg List.length hinput⟩
  · exact Or.inr ⟨hop, congrArg List.length hinput⟩

private lemma slots_bound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    have hs := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private lemma full_slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hfull : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    have hs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
      fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have hb := slots_bound gs hs
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at hfull
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · omega
    · exact ih hs (by omega) g' hg'

private lemma input_used (gs : List Gate) {o v : ℕ} (hv : v < 9)
    (hv0 : 0 < v) (hout : v < o)
    (hmatch : ∀ x : Fin 9 → Bool,
      (⟨first :: second :: gs, o⟩ : Circuit).eval (List.ofFn x) = matching x) :
    v ∈ gs.flatMap Gate.inputs := by
  by_contra hMissing
  have ha : AgreeExcept v (List.ofFn (row v false)) (List.ofFn (row v true)) :=
    ⟨by simp, read_rows_eq v⟩
  have hnot : row v false 0 = row v true 0 := row_eq (by simpa using Nat.ne_of_lt hv0)
  have hor := or_rows ⟨v, hv⟩
  have hinit : AgreeExcept v
      (List.ofFn (row v false) ++ [!(row v false 0), row v false 1 || row v false 3])
      (List.ofFn (row v true) ++ [!(row v true 0), row v true 1 || row v true 3]) := by
    rw [← hnot, ← hor]
    exact agree_append ha _
  have heq := (agree_fold gs hMissing hinit).2 o (Nat.ne_of_gt hout)
  rw [← eval_rest, ← eval_rest, hmatch, hmatch] at heq
  have hm := matching_rows ⟨v, hv⟩
  rw [hm.1, hm.2] at heq
  contradiction

private lemma internal_used (gs : List Gate) (hlive : Live (first :: second :: gs))
    {v : ℕ} (hv : 9 ≤ v) (hlast : v + 1 < 9 + (first :: second :: gs).length) :
    v ∈ gs.flatMap Gate.inputs := by
  simp only [List.length_cons] at hlast
  let j : Fin (first :: second :: gs).length := ⟨v - 9, by simp only [List.length_cons]; omega⟩
  obtain ⟨k, _, hk⟩ := hlive j (by dsimp [j]; omega)
  have hk' : v ∈ ((first :: second :: gs).get k).inputs := by
    have he : 9 + j.val = v := by dsimp [j]; omega
    rwa [he] at hk
  have hmem : (first :: second :: gs).get k ∈ first :: second :: gs :=
    List.mem_iff_get.mpr ⟨k, rfl⟩
  rcases List.mem_cons.mp hmem with he | hmem
  · rw [he] at hk'
    simp [first] at hk'
    omega
  rcases List.mem_cons.mp hmem with he | hmem
  · rw [he] at hk'
    simp [second] at hk'
    omega
  exact List.mem_flatMap.mpr ⟨_, hmem, hk'⟩

private lemma tail_constraints (C : Circuit)
    (hsize : C.size ≤ 11)
    (hmatch : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x)
    (hout : C.output + 1 = 9 + C.size)
    (hnorm : Normal C.gates)
    (hlive : Live C.gates)
    (hfirst : C.gates.head? = some first)
    (hsecond : C.gates.tail.head? = some second) :
    ∃ gs : List Gate, C.gates = first :: second :: gs ∧ C.size = 11 ∧
      ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ 0 ∉ g.inputs := by
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hfirst
  rw [htail, List.tail_cons] at hsecond
  obtain ⟨gs, hgs⟩ := List.head?_eq_some_iff.mp hsecond
  subst tail
  rcases C with ⟨gates, o⟩
  change gates = first :: second :: gs at htail
  subst gates
  simp only [Circuit.size, List.length_cons] at hsize hout ⊢
  change Normal (first :: second :: gs) at hnorm
  change Live (first :: second :: gs) at hlive
  have harity (g : Gate) (hg : g ∈ gs) :=
    normal_gate hnorm (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
  have hle (g : Gate) (hg : g ∈ gs) : g.inputs.length ≤ 2 := by
    rcases harity g hg with h | h
    · rw [h.2]
      decide
    · rw [h.2]
  have hupper := slots_bound gs hle
  -- The tail must read input wires 1 through 8 and all gate wires before the output.
  let needed := List.range' 1 (gs.length + 9)
  have hn : needed.Nodup := List.nodup_range'
  have hneeded : needed ⊆ gs.flatMap Gate.inputs := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hv
    by_cases h : 1 + 1 * i < 9
    · exact input_used gs h (by omega) (by omega) hmatch
    · apply internal_used gs hlive (by omega)
      simp only [List.length_cons]
      omega
  have hlower := hn.length_le_of_subset hneeded
  change (List.range' 1 (gs.length + 9)).length ≤ _ at hlower
  rw [List.length_range'] at hlower
  have hfull : (gs.flatMap Gate.inputs).length = 2 * gs.length := by omega
  have hz : 0 ∉ gs.flatMap Gate.inputs := by
    intro h
    have hd : (0 :: needed).Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨?_, hn⟩
      intro hh
      obtain ⟨i, _, hi⟩ := List.mem_range'.mp hh
      omega
    have hsub : 0 :: needed ⊆ gs.flatMap Gate.inputs := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact h
      · exact hneeded hk
    have hc := hd.length_le_of_subset hsub
    simp only [List.length_cons, needed, List.length_range'] at hc
    omega
  refine ⟨gs, rfl, by omega, ?_⟩
  intro g hg
  refine ⟨?_, fun h => hz (List.mem_flatMap.mpr ⟨g, hg, h⟩)⟩
  rcases harity g hg with h | h
  · have he := full_slots gs hle hfull g hg
    omega
  · exact h.1

private theorem appendWire_le_except {x y : List Bool} {i : Nat} {a b : Bool}
    (hlen : x.length = y.length)
    (hxy : ∀ k, k ≠ i → x.getD k false ≤ y.getD k false)
    (hab : a ≤ b) :
    ∀ k, k ≠ i → (x ++ [a]).getD k false ≤ (y ++ [b]).getD k false := by
  intro k hk
  by_cases h : k < x.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hxy k hk
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h),
      List.getD_append_right _ _ _ _ (hlen ▸ Nat.le_of_not_gt h), ← hlen]
    cases k - x.length with
    | zero => exact hab
    | succ d => simp

private theorem gateEval_le_except {x y : List Bool} {i : Nat} {g : Gate}
    (hxy : ∀ k, k ≠ i → x.getD k false ≤ y.getD k false)
    (hlegal : (g.op = .and ∨ g.op = .or) ∧ i ∉ g.inputs) :
    g.op.eval (g.inputs.map fun k => x.getD k false) ≤
      g.op.eval (g.inputs.map fun k => y.getD k false) := by
  obtain ⟨hop, hi⟩ := hlegal
  apply Bool.le_iff_imp.mpr
  rcases hop with h | h
  · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true]
    intro hx k hk
    have hne : k ≠ i := by
      rintro rfl
      exact hi hk
    exact Bool.le_iff_imp.mp (hxy k hne) (hx k hk)
  · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
    rintro ⟨k, hk, hx⟩
    have hne : k ≠ i := by
      rintro rfl
      exact hi hk
    exact ⟨k, hk, Bool.le_iff_imp.mp (hxy k hne) hx⟩

private theorem foldGates_le_except (gs : List Gate) {x y : List Bool} {i : Nat}
    (hlegal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ i ∉ g.inputs)
    (hlen : x.length = y.length)
    (hxy : ∀ k, k ≠ i → x.getD k false ≤ y.getD k false) :
    ∀ k, k ≠ i → (gs.foldl addWire x).getD k false ≤ (gs.foldl addWire y).getD k false := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih (fun h hh => hlegal h (List.mem_cons_of_mem _ hh)) ?_ ?_
    · simp [addWire, hlen]
    · exact appendWire_le_except hlen hxy (gateEval_le_except hxy (hlegal g List.mem_cons_self))

private theorem eval_notHead_le {C : Circuit} {gs : List Gate} {x y : List Bool} {i : Nat}
    (hhead : C.gates = ⟨.not, [i]⟩ :: gs)
    (hlegal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ i ∉ g.inputs)
    (hout : C.output ≠ i)
    (hlen : x.length = y.length)
    (hx : x.getD i false = true)
    (hy : y.getD i false = false)
    (hxy : ∀ k, k ≠ i → x.getD k false = y.getD k false) :
    C.eval x ≤ C.eval y := by
  unfold Circuit.eval Circuit.wires
  rw [hhead, List.foldl_cons]
  change (gs.foldl addWire (x ++ [!(x.getD i false)])).getD C.output false ≤
    (gs.foldl addWire (y ++ [!(y.getD i false)])).getD C.output false
  rw [hx, hy]
  have hxy' (k : Nat) (hk : k ≠ i) : x.getD k false ≤ y.getD k false :=
    le_of_eq (hxy k hk)
  exact foldGates_le_except gs hlegal (by simp [hlen])
    (appendWire_le_except hlen hxy' (by decide)) C.output hout

end PEqualNP.Outside.L_meta_27479

open PEqualNP.Outside.L_meta_27479

theorem PEqualNP.Outside.L_meta_27479 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩) := by
  intro ⟨C, _, hsize, hmatch, hout, hnorm, _, hlive, hfirst, hsecond⟩
  obtain ⟨gs, hgates, _, hlegal⟩ :=
    tail_constraints C hsize hmatch hout hnorm hlive hfirst hsecond
  have htail : ∀ g ∈ second :: gs, (g.op = .and ∨ g.op = .or) ∧ 0 ∉ g.inputs := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr rfl, by decide⟩
    · exact hlegal g hg
  have hout0 : C.output ≠ 0 := by omega
  have hle := eval_notHead_le (x := List.ofFn (row 0 true)) (y := List.ofFn (row 0 false))
    hgates htail hout0 (by simp) (by rfl) (by rfl) (fun k hk => (read_rows_eq 0 k hk).symm)
  rw [hmatch, hmatch] at hle
  change matching (row 0 true) ≤ matching (row 0 false) at hle
  rw [(matching_rows ⟨0, by decide⟩).2, (matching_rows ⟨0, by decide⟩).1] at hle
  exact (by decide : ¬ (true ≤ false)) hle
