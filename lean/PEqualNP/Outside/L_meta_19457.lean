import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19457_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp [stepW]; omega

private def effInputs (N : ℕ) (C : Circuit) (k : ℕ) : List ℕ :=
  let g := C.gates.getD k ⟨GateOp.or, []⟩
  let raw := match g.op with
    | GateOp.not => g.inputs.take 1
    | _ => g.inputs
  raw.filter fun i => decide (i < N + k)

private lemma effInputs_lt (N : ℕ) (C : Circuit) (k i : ℕ) (hi : i ∈ effInputs N C k) :
    i < N + k := by
  simp only [effInputs, List.mem_filter, decide_eq_true_eq] at hi
  exact hi.2

private def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma effInputs_len (N : ℕ) (C : Circuit) (hF : FanInTwo C) (k : ℕ) (hk : k < C.gates.length) :
    (effInputs N C k).length ≤ if isNot C.gates[k].op then 1 else 2 := by
  have hg : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
  have hlen : C.gates[k].inputs.length ≤ 2 := (hF _ (List.getElem_mem hk)).2
  simp only [effInputs, hg]
  cases hop : C.gates[k].op <;> simp only [isNot, Bool.false_eq_true, ↓reduceIte]
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) hlen

private def reachAux (N : ℕ) (C : Circuit) : ℕ → Finset ℕ → Finset ℕ
  | 0, acc => acc
  | m + 1, acc =>
    let acc' :=
      if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    reachAux N C m acc'

private lemma reachAux_sub (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) :
    acc ⊆ reachAux N C m acc := by
  induction m generalizing acc with
  | zero => exact Finset.Subset.rfl
  | succ m ih =>
    dsimp [reachAux]
    split_ifs
    · exact Finset.Subset.trans Finset.subset_union_left (ih _)
    · exact ih _

private lemma reachAux_le (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) (M : ℕ)
    (hacc : ∀ w ∈ acc, w ≤ M) : ∀ w ∈ reachAux N C m acc, w ≤ M := by
  induction m generalizing acc with
  | zero => exact hacc
  | succ m ih =>
    dsimp [reachAux]
    apply ih
    intro w hw
    split_ifs at hw with h
    · rcases Finset.mem_union.mp hw with ha | hi
      · exact hacc w ha
      · have hlt := effInputs_lt N C m w (List.mem_toFinset.mp hi)
        have hle := hacc (N + m) h.2
        omega
    · exact hacc w hw

private lemma reachAux_closed (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ)
    (hhi : ∀ k, m ≤ k → k < C.gates.length → N + k ∈ acc → ∀ i ∈ effInputs N C k, i ∈ acc) :
    ∀ k, k < C.gates.length → N + k ∈ reachAux N C m acc → ∀ i ∈ effInputs N C k, i ∈ reachAux N C m acc := by
  induction m generalizing acc with
  | zero =>
    intro k hk hmem i hi
    exact hhi k (Nat.zero_le k) hk hmem i hi
  | succ m ih =>
    let acc' := if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    have hstep : reachAux N C (m + 1) acc = reachAux N C m acc' := rfl
    rw [hstep]
    apply ih acc'
    intro k hmk hk hmem i hi
    by_cases heq : k = m
    · subst heq
      have hmem_acc : N + k ∈ acc := by
        dsimp [acc'] at hmem
        split_ifs at hmem with h
        · exact h.2
        · exact hmem
      have hsub : (effInputs N C k).toFinset ⊆ acc' := by
        dsimp [acc']
        simp only [hk, hmem_acc, and_self, ↓reduceIte]
        exact Finset.subset_union_right
      exact hsub (List.mem_toFinset.mpr hi)
    · have hlt : m + 1 ≤ k := by omega
      have hmem_acc : N + k ∈ acc := by
        dsimp [acc'] at hmem
        split_ifs at hmem with h
        · rcases Finset.mem_union.mp hmem with ha | hin
          · exact ha
          · have := effInputs_lt N C m (N + k) (List.mem_toFinset.mp hin)
            omega
        · exact hmem
      have hsub : acc ⊆ acc' := by
        dsimp [acc']; split_ifs
        · exact Finset.subset_union_left
        · exact Finset.Subset.rfl
      exact hsub (hhi k hlt hk hmem_acc i hi)

private lemma reachAux_bound (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) :
    reachAux N C m acc ⊆ acc ∪
      ((Finset.range m).filter fun k => k < C.gates.length ∧ N + k ∈ reachAux N C m acc).biUnion
        (fun k => (effInputs N C k).toFinset) := by
  induction m generalizing acc with
  | zero => dsimp [reachAux]; exact Finset.subset_union_left
  | succ m ih =>
    let acc' := if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    have hstep : reachAux N C (m + 1) acc = reachAux N C m acc' := rfl
    intro w hw
    have h1 := ih acc' (hstep ▸ hw)
    rcases Finset.mem_union.mp h1 with hacc' | hbi
    · dsimp [acc'] at hacc'
      split_ifs at hacc' with h
      · rcases Finset.mem_union.mp hacc' with ha | hin
        · exact Finset.mem_union_left _ ha
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          refine ⟨m, ?_, hin⟩
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_self m, h.1, ?_⟩
          rw [hstep]
          apply reachAux_sub
          dsimp [acc']
          simp only [h.1, h.2, and_self, ↓reduceIte]
          exact Finset.mem_union_left _ h.2
      · exact Finset.mem_union_left _ hacc'
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion] at hbi ⊢
      obtain ⟨k, hk, hwk⟩ := hbi
      rw [Finset.mem_filter, Finset.mem_range] at hk
      refine ⟨k, ?_, hwk⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_lt hk.1, hk.2.1, hstep.symm ▸ hk.2.2⟩

private def subW (N : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  reachAux N C C.gates.length {w}

private lemma self_mem_subW (N : ℕ) (C : Circuit) (w : ℕ) : w ∈ subW N C w :=
  reachAux_sub N C C.gates.length {w} (Finset.mem_singleton_self w)

private lemma subW_le (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ subW N C w) : u ≤ w :=
  reachAux_le N C C.gates.length {w} w (fun z hz => by rw [Finset.mem_singleton.mp hz]) u hu

private lemma subW_closed (N : ℕ) (C : Circuit) (w k : ℕ) (hk : k < C.gates.length)
    (hmem : N + k ∈ subW N C w) (i : ℕ) (hi : i ∈ effInputs N C k) : i ∈ subW N C w :=
  reachAux_closed N C C.gates.length {w} (fun _ h1 h2 => by omega) k hk hmem i hi

private lemma subW_sub_of_mem (N : ℕ) (C : Circuit) (w1 w2 : ℕ) (h : w1 ∈ subW N C w2) :
    subW N C w1 ⊆ subW N C w2 := by
  have haux : ∀ m (acc : Finset ℕ), acc ⊆ subW N C w2 → reachAux N C m acc ⊆ subW N C w2 := by
    intro m
    induction m with
    | zero => intro acc hacc; exact hacc
    | succ m ih =>
      intro acc hacc
      dsimp [reachAux]
      apply ih
      split_ifs with hm
      · refine Finset.union_subset hacc ?_
        intro i hi
        exact subW_closed N C w2 m hm.1 (hacc hm.2) i (List.mem_toFinset.mp hi)
      · exact hacc
  exact haux C.gates.length {w1} (Finset.singleton_subset_iff.mpr h)

private lemma subW_parent (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ subW N C w) (hne : u ≠ w) :
    ∃ k < C.gates.length, N + k ∈ subW N C w ∧ u ∈ effInputs N C k := by
  have hb := reachAux_bound N C C.gates.length {w} hu
  rcases Finset.mem_union.mp hb with hsing | hbi
  · exact absurd (Finset.mem_singleton.mp hsing) hne
  · obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hbi
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k, hk.2.1, hk.2.2, List.mem_toFinset.mp huk⟩

private lemma wire_getD_input (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (i : ℕ) (hi : i < N) :
    (C.wires x).getD i false = x.getD i false := by
  change (C.gates.foldl stepW x).getD i false = x.getD i false
  exact foldl_getD_lt C.gates x i (by omega)

private lemma wire_getD_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (N + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => if i < N + k then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  change (C.gates.foldl stepW x).getD (N + k) false = _
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen1 : ((C.gates.take k).foldl stepW x).length = N + k := by
    rw [foldl_len, hx, List.length_take]; omega
  have hlt : N + k < (stepW ((C.gates.take k).foldl stepW x) C.gates[k]).length := by
    simp only [stepW, List.length_append, List.length_singleton, hlen1]; omega
  rw [foldl_getD_lt _ _ _ hlt]
  simp only [stepW]
  have hget : ((C.gates.take k).foldl stepW x ++
      [C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl stepW x).getD i false)]).getD (N + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl stepW x).getD i false) := by
    rw [← hlen1]
    simp [List.getD_eq_getElem?_getD]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < N + k
  · simp only [hi, ↓reduceIte]
    have hsplit2 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    change ((C.gates.take k).foldl stepW x).getD i false = (C.gates.foldl stepW x).getD i false
    conv_rhs => rw [hsplit2]
    rw [List.foldl_append]
    exact (foldl_getD_lt _ _ i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

private lemma eval_gate_eff (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.gates[k].op = GateOp.and → (C.wires x).getD (N + k) false =
      (if C.gates[k].inputs.all (fun i => decide (i < N + k)) then (effInputs N C k).all (fun i => (C.wires x).getD i false) else false)) ∧
    (C.gates[k].op = GateOp.or → (C.wires x).getD (N + k) false = (effInputs N C k).any (fun i => (C.wires x).getD i false)) ∧
    (C.gates[k].op = GateOp.not → (C.wires x).getD (N + k) false =
      match effInputs N C k with | a :: _ => !((C.wires x).getD a false) | [] => true) := by
  have hgk : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
  refine ⟨?_, ?_, ?_⟩
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval, List.all_map]
    by_cases hall : C.gates[k].inputs.all (fun i => decide (i < N + k)) = true
    · simp only [hall, ↓reduceIte]
      have hfilt : C.gates[k].inputs.filter (fun i => decide (i < N + k)) = C.gates[k].inputs :=
        List.filter_eq_self.mpr (fun i hi => List.all_eq_true.mp hall i hi)
      rw [hfilt]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp_apply, id_eq]
      constructor
      · intro h i hi
        have hlt : i < N + k := decide_eq_true_eq.mp (List.all_eq_true.mp hall i hi)
        simpa [hlt] using h i hi
      · intro h i hi
        have hlt : i < N + k := decide_eq_true_eq.mp (List.all_eq_true.mp hall i hi)
        simpa [hlt] using h i hi
    · simp only [hall, Bool.false_eq_true, ↓reduceIte]
      have hex : ∃ i ∈ C.gates[k].inputs, ¬ i < N + k := by
        by_contra hno
        push Not at hno
        exact hall (List.all_eq_true.mpr (fun i hi => decide_eq_true (hno i hi)))
      obtain ⟨i, hi, hnot⟩ := hex
      rw [Bool.eq_false_iff]
      intro ht
      have := List.all_eq_true.mp ht i hi
      simp [hnot] at this
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval, List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, hv⟩
      by_cases hlt : i < N + k
      · simp only [hlt, ↓reduceIte] at hv
        exact ⟨i, ⟨hi, hlt⟩, hv⟩
      · simp [hlt] at hv
    · rintro ⟨i, ⟨hi, hlt⟩, hv⟩
      exact ⟨i, hi, by simp only [hlt, ↓reduceIte]; exact hv⟩
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval]
    cases hin : C.gates[k].inputs with
    | nil => rfl
    | cons a rest =>
      simp only [List.take_succ_cons, List.take_zero, List.filter_cons, List.filter_nil, List.map_cons, List.headD_cons]
      by_cases ha : a < N + k
      · simp [ha]
      · simp [ha]

private lemma wires_agree_of_subW (N : ℕ) (C : Circuit) (hF : FanInTwo C) (w0 : ℕ)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i < N → i ∈ subW N C w0 → x.getD i false = y.getD i false) :
    ∀ w, w ∈ subW N C w0 → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < N
    · rw [wire_getD_input N C x hx w hwn, wire_getD_input N C y hy w hwn]
      exact hxy w hwn hw
    · by_cases hwg : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hweq : w = N + (w - N) := by omega
        rw [hweq] at hw ⊢
        obtain ⟨hand, hor, hnot⟩ := eval_gate_eff N C x hx (w - N) hk
        obtain ⟨hand', hor', hnot'⟩ := eval_gate_eff N C y hy (w - N) hk
        have hop := (hF _ (List.getElem_mem hk)).1
        have hrec : ∀ i ∈ effInputs N C (w - N), (C.wires x).getD i false = (C.wires y).getD i false := by
          intro i hi
          have hilt := effInputs_lt N C (w - N) i hi
          exact ih i (by omega) (subW_closed N C w0 (w - N) hk hw i hi)
        rcases Set.mem_insert_iff.mp hop with h1 | h2
        · rw [hand h1, hand' h1]
          split_ifs
          · apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
            constructor <;> intro h i hi
            · rw [← hrec i hi]; exact h i hi
            · rw [hrec i hi]; exact h i hi
          · rfl
        · rcases Set.mem_insert_iff.mp h2 with h2 | h3
          · rw [hor h2, hor' h2]
            apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
            constructor <;> rintro ⟨i, hi, hv⟩
            · exact ⟨i, hi, hrec i hi ▸ hv⟩
            · exact ⟨i, hi, (hrec i hi).symm ▸ hv⟩
          · have h3' : C.gates[w - N].op = GateOp.not := Set.mem_singleton_iff.mp h3
            rw [hnot h3', hnot' h3']
            cases heff : effInputs N C (w - N) with
            | nil => rfl
            | cons a rest =>
              have ha : a ∈ effInputs N C (w - N) := by rw [heff]; simp
              dsimp only
              rw [hrec a ha]
      · have hlx : (C.wires x).length = N + C.gates.length := by
          change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
        have hly : (C.wires y).length = N + C.gates.length := by
          change (C.gates.foldl stepW y).length = N + C.gates.length; rw [foldl_len, hy]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma mono_of_no_not (N : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hnonot : ∀ k, (hk : k < C.gates.length) → N + k ∈ subW N C C.output → C.gates[k].op ≠ GateOp.not)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i < N → i ∈ subW N C C.output → x.getD i false = true → y.getD i false = true) :
    ∀ w, w ∈ subW N C C.output → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hvx
    by_cases hwn : w < N
    · rw [wire_getD_input N C x hx w hwn] at hvx
      rw [wire_getD_input N C y hy w hwn]
      exact hxy w hwn hw hvx
    · by_cases hwg : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hweq : w = N + (w - N) := by omega
        rw [hweq] at hw hvx ⊢
        obtain ⟨hand, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
        obtain ⟨hand', hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
        have hop := (hF _ (List.getElem_mem hk)).1
        have hrec : ∀ i ∈ effInputs N C (w - N), (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
          intro i hi
          have hilt := effInputs_lt N C (w - N) i hi
          exact ih i (by omega) (subW_closed N C C.output (w - N) hk hw i hi)
        rcases Set.mem_insert_iff.mp hop with h1 | h2
        · rw [hand h1] at hvx; rw [hand' h1]
          split_ifs at hvx ⊢
          · rw [List.all_eq_true] at hvx ⊢
            intro i hi; exact hrec i hi (hvx i hi)
        · rcases Set.mem_insert_iff.mp h2 with h2 | h3
          · rw [hor h2] at hvx; rw [hor' h2]
            rw [List.any_eq_true] at hvx ⊢
            obtain ⟨i, hi, hv⟩ := hvx
            exact ⟨i, hi, hrec i hi hv⟩
          · exact absurd (Set.mem_singleton_iff.mp h3) (hnonot (w - N) hk hw)
      · have hlx : (C.wires x).length = N + C.gates.length := by
          change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
        rw [List.getD_eq_default _ _ (by omega)] at hvx
        exact Bool.noConfusion hvx

private lemma tree_disjoint_subW (N : ℕ) (C : Circuit)
    (W : Finset ℕ) (hW : W = subW N C C.output)
    (R : Finset ℕ) (hR : R = (Finset.range C.gates.length).filter fun k => N + k ∈ W)
    (htree : ∀ u ∈ W, (∑ k ∈ R, (effInputs N C k).count u) ≤ 1)
    (k : ℕ) (hk : k < C.gates.length) (hkW : N + k ∈ W)
    (a b : ℕ) (hab_in : effInputs N C k = [a, b]) :
    Disjoint (subW N C a) (subW N C b) := by
  have hkR : k ∈ R := by rw [hR, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hkW⟩
  have ha_mem : a ∈ effInputs N C k := by rw [hab_in]; simp
  have hb_mem : b ∈ effInputs N C k := by rw [hab_in]; simp
  have haW : a ∈ W := hW ▸ subW_closed N C C.output k hk (hW ▸ hkW) a ha_mem
  have hbW : b ∈ W := hW ▸ subW_closed N C C.output k hk (hW ▸ hkW) b hb_mem
  have hsubA : subW N C a ⊆ W := hW ▸ subW_sub_of_mem N C a C.output (hW ▸ haW)
  have hsubB : subW N C b ⊆ W := hW ▸ subW_sub_of_mem N C b C.output (hW ▸ hbW)
  have hne_ab : a ≠ b := by
    intro heq
    subst heq
    have hcnt : 2 ≤ (effInputs N C k).count a := by rw [hab_in]; simp
    have hsum : (effInputs N C k).count a ≤ ∑ j ∈ R, (effInputs N C j).count a :=
      Finset.single_le_sum (f := fun j => (effInputs N C j).count a) (fun _ _ => Nat.zero_le _) hkR
    have hle := htree a haW
    omega
  rw [Finset.disjoint_left]
  intro z hza hzb
  let I : Finset ℕ := subW N C a ∩ subW N C b
  have hIne : I.Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hza, hzb⟩⟩
  let u : ℕ := I.max' hIne
  have huI : u ∈ I := Finset.max'_mem I hIne
  have hua : u ∈ subW N C a := (Finset.mem_inter.mp huI).1
  have hub : u ∈ subW N C b := (Finset.mem_inter.mp huI).2
  have huW : u ∈ W := hsubA hua
  have hdeg := htree u huW
  by_cases hu_eq_a : u = a
  · have hne_ub : u ≠ b := hu_eq_a ▸ hne_ab
    obtain ⟨k2, hk2, hk2b, huk2⟩ := subW_parent N C b u hub hne_ub
    have hk2_lt : k2 < k := by
      have h1 : N + k2 ≤ b := subW_le N C b (N + k2) hk2b
      have h2 : b < N + k := effInputs_lt N C k b hb_mem
      omega
    have hk2R : k2 ∈ R := by rw [hR, Finset.mem_filter, Finset.mem_range]; exact ⟨hk2, hsubB hk2b⟩
    have h1 : 1 ≤ (effInputs N C k).count u := List.count_pos_iff.mpr (hu_eq_a ▸ ha_mem)
    have h2 : 1 ≤ (effInputs N C k2).count u := List.count_pos_iff.mpr huk2
    have hpair : (effInputs N C k).count u + (effInputs N C k2).count u ≤ ∑ j ∈ R, (effInputs N C j).count u := by
      have hsub : ({k, k2} : Finset ℕ) ⊆ R := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption
      calc (effInputs N C k).count u + (effInputs N C k2).count u
          = ∑ j ∈ ({k, k2} : Finset ℕ), (effInputs N C j).count u := by rw [Finset.sum_pair (by omega)]
        _ ≤ ∑ j ∈ R, (effInputs N C j).count u := Finset.sum_le_sum_of_subset hsub
    omega
  · by_cases hu_eq_b : u = b
    · obtain ⟨k1, hk1, hk1a, huk1⟩ := subW_parent N C a u hua hu_eq_a
      have hk1_lt : k1 < k := by
        have h1 : N + k1 ≤ a := subW_le N C a (N + k1) hk1a
        have h2 : a < N + k := effInputs_lt N C k a ha_mem
        omega
      have hk1R : k1 ∈ R := by rw [hR, Finset.mem_filter, Finset.mem_range]; exact ⟨hk1, hsubA hk1a⟩
      have h1 : 1 ≤ (effInputs N C k).count u := List.count_pos_iff.mpr (hu_eq_b ▸ hb_mem)
      have h2 : 1 ≤ (effInputs N C k1).count u := List.count_pos_iff.mpr huk1
      have hpair : (effInputs N C k).count u + (effInputs N C k1).count u ≤ ∑ j ∈ R, (effInputs N C j).count u := by
        have hsub : ({k, k1} : Finset ℕ) ⊆ R := by
          intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> assumption
        calc (effInputs N C k).count u + (effInputs N C k1).count u
            = ∑ j ∈ ({k, k1} : Finset ℕ), (effInputs N C j).count u := by rw [Finset.sum_pair (by omega)]
          _ ≤ ∑ j ∈ R, (effInputs N C j).count u := Finset.sum_le_sum_of_subset hsub
      omega
    · obtain ⟨k1, hk1, hk1a, huk1⟩ := subW_parent N C a u hua hu_eq_a
      obtain ⟨k2, hk2, hk2b, huk2⟩ := subW_parent N C b u hub hu_eq_b
      by_cases hkeq : k1 = k2
      · subst hkeq
        have hmemI : N + k1 ∈ I := Finset.mem_inter.mpr ⟨hk1a, hk2b⟩
        have hle : N + k1 ≤ u := Finset.le_max' I (N + k1) hmemI
        have hlt : u < N + k1 := effInputs_lt N C k1 u huk1
        omega
      · have hk1R : k1 ∈ R := by rw [hR, Finset.mem_filter, Finset.mem_range]; exact ⟨hk1, hsubA hk1a⟩
        have hk2R : k2 ∈ R := by rw [hR, Finset.mem_filter, Finset.mem_range]; exact ⟨hk2, hsubB hk2b⟩
        have h1 : 1 ≤ (effInputs N C k1).count u := List.count_pos_iff.mpr huk1
        have h2 : 1 ≤ (effInputs N C k2).count u := List.count_pos_iff.mpr huk2
        have hpair : (effInputs N C k1).count u + (effInputs N C k2).count u ≤ ∑ j ∈ R, (effInputs N C j).count u := by
          have hsub : ({k1, k2} : Finset ℕ) ⊆ R := by
            intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl <;> assumption
          calc (effInputs N C k1).count u + (effInputs N C k2).count u
              = ∑ j ∈ ({k1, k2} : Finset ℕ), (effInputs N C j).count u := by rw [Finset.sum_pair hkeq]
            _ ≤ ∑ j ∈ R, (effInputs N C j).count u := Finset.sum_le_sum_of_subset hsub
        omega

private lemma bool_imp_and1 {p : Bool} {a1 a2 b : Bool}
    (ha : if p then a2 = true → a1 = true else a1 = true → a2 = true) :
    if p then (a2 && b) = true → (a1 && b) = true else (a1 && b) = true → (a2 && b) = true := by
  cases p <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.and_eq_true] at ha ⊢
  · rintro ⟨h1, h2⟩; exact ⟨ha h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨ha h1, h2⟩

private lemma bool_imp_and2 {p : Bool} {a b1 b2 : Bool}
    (hb : if p then b2 = true → b1 = true else b1 = true → b2 = true) :
    if p then (a && b2) = true → (a && b1) = true else (a && b1) = true → (a && b2) = true := by
  cases p <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.and_eq_true] at hb ⊢
  · rintro ⟨h1, h2⟩; exact ⟨h1, hb h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, hb h2⟩

private lemma bool_imp_or1 {p : Bool} {a1 a2 b : Bool}
    (ha : if p then a2 = true → a1 = true else a1 = true → a2 = true) :
    if p then (a2 || b) = true → (a1 || b) = true else (a1 || b) = true → (a2 || b) = true := by
  cases p <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.or_eq_true] at ha ⊢
  · rintro (h1 | h2); exact Or.inl (ha h1); exact Or.inr h2
  · rintro (h1 | h2); exact Or.inl (ha h1); exact Or.inr h2

private lemma bool_imp_or2 {p : Bool} {a b1 b2 : Bool}
    (hb : if p then b2 = true → b1 = true else b1 = true → b2 = true) :
    if p then (a || b2) = true → (a || b1) = true else (a || b1) = true → (a || b2) = true := by
  cases p <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.or_eq_true] at hb ⊢
  · rintro (h1 | h2); exact Or.inl h1; exact Or.inr (hb h2)
  · rintro (h1 | h2); exact Or.inl h1; exact Or.inr (hb h2)

private lemma tree_unate (N : ℕ) (C : Circuit) (hF : FanInTwo C)
    (W : Finset ℕ) (hW : W = subW N C C.output)
    (R : Finset ℕ) (hR : R = (Finset.range C.gates.length).filter fun k => N + k ∈ W)
    (htree : ∀ u ∈ W, (∑ k ∈ R, (effInputs N C k).count u) ≤ 1)
    (i0 : ℕ) (hi0 : i0 < N) :
    ∀ w, w ∈ W →
      ∃ p : Bool, ∀ (x y : List Bool), x.length = N → y.length = N →
        (∀ i, i < N → i ∈ subW N C w → i ≠ i0 → x.getD i false = y.getD i false) →
        x.getD i0 false = false → y.getD i0 false = true →
        (if p then (C.wires y).getD w false = true → (C.wires x).getD w false = true
         else (C.wires x).getD w false = true → (C.wires y).getD w false = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hdep : i0 ∈ subW N C w
    · by_cases hwn : w < N
      · have hweq : w = i0 := by
          by_cases hne : i0 = w
          · exact hne.symm
          · obtain ⟨k, _, hkW, _⟩ := subW_parent N C w i0 hdep hne
            have := subW_le N C w (N + k) hkW
            omega
        subst hweq
        refine ⟨false, fun x y hx hy _ hxi0 _ hvx => ?_⟩
        rw [wire_getD_input N C x hx w hwn, hxi0] at hvx
        exact Bool.noConfusion hvx
      · by_cases hwg : w < N + C.gates.length
        · have hk : w - N < C.gates.length := by omega
          have hweq : w = N + (w - N) := by omega
          rw [hweq] at hw hdep ⊢
          have hop := (hF _ (List.getElem_mem hk)).1
          have hcl : ∀ i ∈ effInputs N C (w - N), i ∈ W ∧ i < N + (w - N) ∧ subW N C i ⊆ subW N C (N + (w - N)) := by
            intro i hi
            have hilt := effInputs_lt N C (w - N) i hi
            have hiw : i ∈ subW N C (N + (w - N)) := subW_closed N C (N + (w - N)) (w - N) hk (self_mem_subW N C _) i hi
            have hiW : i ∈ W := hW ▸ subW_closed N C C.output (w - N) hk (hW ▸ hw) i hi
            exact ⟨hiW, hilt, subW_sub_of_mem N C i (N + (w - N)) hiw⟩
          rcases Set.mem_insert_iff.mp hop with h1 | h2
          · have hlen : (effInputs N C (w - N)).length ≤ 2 := by
              have := effInputs_len N C hF (w - N) hk; rw [h1] at this; simpa [isNot] using this
            cases heff : effInputs N C (w - N) with
            | nil =>
              refine ⟨false, fun x y hx hy _ _ _ hvx => ?_⟩
              obtain ⟨hand, _, _⟩ := eval_gate_eff N C x hx (w - N) hk
              obtain ⟨hand', _, _⟩ := eval_gate_eff N C y hy (w - N) hk
              rw [hand h1, heff] at hvx; rw [hand' h1, heff]; exact hvx
            | cons a rest =>
              cases rest with
              | nil =>
                have ha_in : a ∈ effInputs N C (w - N) := by rw [heff]; simp
                obtain ⟨haW, halt, hasub⟩ := hcl a ha_in
                obtain ⟨pa, hpa⟩ := ih a (by omega) haW
                refine ⟨pa, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                have ha_step := hpa x y hx hy (fun i hin hisub => hxy i hin (hasub hisub)) hxi0 hyi0
                obtain ⟨hand, _, _⟩ := eval_gate_eff N C x hx (w - N) hk
                obtain ⟨hand', _, _⟩ := eval_gate_eff N C y hy (w - N) hk
                rw [hand h1, hand' h1, heff]
                by_cases hall : C.gates[w - N].inputs.all (fun i => decide (i < N + (w - N))) = true
                · simp only [hall, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
                  exact ha_step
                · simp only [hall, Bool.false_eq_true, ↓reduceIte]
                  cases pa <;> simp
              | cons b rest2 =>
                cases rest2 with
                | nil =>
                  have ha_in : a ∈ effInputs N C (w - N) := by rw [heff]; simp
                  have hb_in : b ∈ effInputs N C (w - N) := by rw [heff]; simp
                  obtain ⟨haW, halt, hasub⟩ := hcl a ha_in
                  obtain ⟨hbW, hblt, hbsub⟩ := hcl b hb_in
                  have hdisj := tree_disjoint_subW N C W hW R hR htree (w - N) hk hw a b heff
                  by_cases ha_dep : i0 ∈ subW N C a
                  · have hb_ndep : i0 ∉ subW N C b := Finset.disjoint_left.mp hdisj ha_dep
                    obtain ⟨pa, hpa⟩ := ih a (by omega) haW
                    refine ⟨pa, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                    have ha_step := hpa x y hx hy (fun i hin hisub => hxy i hin (hasub hisub)) hxi0 hyi0
                    have hb_eq : (C.wires x).getD b false = (C.wires y).getD b false :=
                      wires_agree_of_subW N C hF b x y hx hy
                        (fun i hin hisub => hxy i hin (hbsub hisub) (fun heq => hb_ndep (heq ▸ hisub))) b (self_mem_subW N C b)
                    obtain ⟨hand, _, _⟩ := eval_gate_eff N C x hx (w - N) hk
                    obtain ⟨hand', _, _⟩ := eval_gate_eff N C y hy (w - N) hk
                    rw [hand h1, hand' h1, heff]
                    by_cases hall : C.gates[w - N].inputs.all (fun i => decide (i < N + (w - N))) = true
                    · simp only [hall, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
                      rw [hb_eq]
                      exact bool_imp_and1 ha_step
                    · simp only [hall, Bool.false_eq_true, ↓reduceIte]
                      cases pa <;> simp
                  · obtain ⟨pb, hpb⟩ := ih b (by omega) hbW
                    refine ⟨pb, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                    have hb_step := hpb x y hx hy (fun i hin hisub => hxy i hin (hbsub hisub)) hxi0 hyi0
                    have ha_eq : (C.wires x).getD a false = (C.wires y).getD a false :=
                      wires_agree_of_subW N C hF a x y hx hy
                        (fun i hin hisub => hxy i hin (hasub hisub) (fun heq => ha_dep (heq ▸ hisub))) a (self_mem_subW N C a)
                    obtain ⟨hand, _, _⟩ := eval_gate_eff N C x hx (w - N) hk
                    obtain ⟨hand', _, _⟩ := eval_gate_eff N C y hy (w - N) hk
                    rw [hand h1, hand' h1, heff]
                    by_cases hall : C.gates[w - N].inputs.all (fun i => decide (i < N + (w - N))) = true
                    · simp only [hall, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
                      rw [ha_eq]
                      exact bool_imp_and2 hb_step
                    · simp only [hall, Bool.false_eq_true, ↓reduceIte]
                      cases pb <;> simp
                | cons c rest3 =>
                  rw [heff] at hlen; simp at hlen
          · rcases Set.mem_insert_iff.mp h2 with h2 | h3
            · have hlen : (effInputs N C (w - N)).length ≤ 2 := by
                have := effInputs_len N C hF (w - N) hk; rw [h2] at this; simpa [isNot] using this
              cases heff : effInputs N C (w - N) with
              | nil =>
                refine ⟨false, fun x y hx hy _ _ _ hvx => ?_⟩
                obtain ⟨_, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
                obtain ⟨_, hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
                rw [hor h2, heff] at hvx; rw [hor' h2, heff]; exact hvx
              | cons a rest =>
                cases rest with
                | nil =>
                  have ha_in : a ∈ effInputs N C (w - N) := by rw [heff]; simp
                  obtain ⟨haW, halt, hasub⟩ := hcl a ha_in
                  obtain ⟨pa, hpa⟩ := ih a (by omega) haW
                  refine ⟨pa, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                  have ha_step := hpa x y hx hy (fun i hin hisub => hxy i hin (hasub hisub)) hxi0 hyi0
                  obtain ⟨_, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
                  obtain ⟨_, hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
                  rw [hor h2, hor' h2, heff]
                  simp only [List.any_cons, List.any_nil, Bool.or_false]
                  exact ha_step
                | cons b rest2 =>
                  cases rest2 with
                  | nil =>
                    have ha_in : a ∈ effInputs N C (w - N) := by rw [heff]; simp
                    have hb_in : b ∈ effInputs N C (w - N) := by rw [heff]; simp
                    obtain ⟨haW, halt, hasub⟩ := hcl a ha_in
                    obtain ⟨hbW, hblt, hbsub⟩ := hcl b hb_in
                    have hdisj := tree_disjoint_subW N C W hW R hR htree (w - N) hk hw a b heff
                    by_cases ha_dep : i0 ∈ subW N C a
                    · have hb_ndep : i0 ∉ subW N C b := Finset.disjoint_left.mp hdisj ha_dep
                      obtain ⟨pa, hpa⟩ := ih a (by omega) haW
                      refine ⟨pa, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                      have ha_step := hpa x y hx hy (fun i hin hisub => hxy i hin (hasub hisub)) hxi0 hyi0
                      have hb_eq : (C.wires x).getD b false = (C.wires y).getD b false :=
                        wires_agree_of_subW N C hF b x y hx hy
                          (fun i hin hisub => hxy i hin (hbsub hisub) (fun heq => hb_ndep (heq ▸ hisub))) b (self_mem_subW N C b)
                      obtain ⟨_, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
                      obtain ⟨_, hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
                      rw [hor h2, hor' h2, heff]
                      simp only [List.any_cons, List.any_nil, Bool.or_false]
                      rw [hb_eq]
                      exact bool_imp_or1 ha_step
                    · obtain ⟨pb, hpb⟩ := ih b (by omega) hbW
                      refine ⟨pb, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                      have hb_step := hpb x y hx hy (fun i hin hisub => hxy i hin (hbsub hisub)) hxi0 hyi0
                      have ha_eq : (C.wires x).getD a false = (C.wires y).getD a false :=
                        wires_agree_of_subW N C hF a x y hx hy
                          (fun i hin hisub => hxy i hin (hasub hisub) (fun heq => ha_dep (heq ▸ hisub))) a (self_mem_subW N C a)
                      obtain ⟨_, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
                      obtain ⟨_, hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
                      rw [hor h2, hor' h2, heff]
                      simp only [List.any_cons, List.any_nil, Bool.or_false]
                      rw [ha_eq]
                      exact bool_imp_or2 hb_step
                  | cons c rest3 =>
                    rw [heff] at hlen; simp at hlen
            · have h3' : C.gates[w - N].op = GateOp.not := Set.mem_singleton_iff.mp h3
              cases heff : effInputs N C (w - N) with
              | nil =>
                refine ⟨false, fun x y hx hy _ _ _ hvx => ?_⟩
                obtain ⟨_, _, hnot⟩ := eval_gate_eff N C x hx (w - N) hk
                obtain ⟨_, _, hnot'⟩ := eval_gate_eff N C y hy (w - N) hk
                rw [hnot h3', heff] at hvx; rw [hnot' h3', heff]
              | cons a rest =>
                have ha_in : a ∈ effInputs N C (w - N) := by rw [heff]; simp
                obtain ⟨haW, halt, hasub⟩ := hcl a ha_in
                obtain ⟨pa, hpa⟩ := ih a (by omega) haW
                refine ⟨!pa, fun x y hx hy hxy hxi0 hyi0 => ?_⟩
                have ha_step := hpa x y hx hy (fun i hin hisub => hxy i hin (hasub hisub)) hxi0 hyi0
                obtain ⟨_, _, hnot⟩ := eval_gate_eff N C x hx (w - N) hk
                obtain ⟨_, _, hnot'⟩ := eval_gate_eff N C y hy (w - N) hk
                rw [hnot h3', hnot' h3', heff]
                cases pa <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.not_eq_true'] at ha_step ⊢
                · intro hya
                  cases hxa : (C.wires x).getD a false
                  · rfl
                  · rw [ha_step hxa] at hya; exact Bool.noConfusion hya
                · intro hxa
                  cases hya : (C.wires y).getD a false
                  · rfl
                  · rw [ha_step hya] at hxa; exact Bool.noConfusion hxa
        · refine ⟨false, fun x y hx hy _ _ _ hvx => ?_⟩
          have hlx : (C.wires x).length = N + C.gates.length := by
            change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
          rw [List.getD_eq_default _ _ (by omega)] at hvx
          exact Bool.noConfusion hvx
    · refine ⟨false, fun x y hx hy hxy _ _ hvx => ?_⟩
      have heq := wires_agree_of_subW N C hF w x y hx hy
        (fun i hin hisub => hxy i hin hisub (fun heq => hdep (heq ▸ hisub))) w (self_mem_subW N C w)
      exact heq ▸ hvx

private lemma repInput_len {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma repInput_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (oneEach u v).getD i false =
      if h : i < n then decide (⟨i, h⟩ = u) else decide (⟨i - n, by omega⟩ = v) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
    simp [h]
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_ofFn]
    simp [show i - n < m by omega]

theorem rep_fanin2_lb {n m s minR minC compR compC clsR clsC : ℕ} (A : Fin n → Fin m → Bool)
    (hminR : (Finset.univ.filter fun u : Fin n => ∀ u' v, A u v = true → A u' v = true).card ≤ minR)
    (hminC : (Finset.univ.filter fun v : Fin m => ∀ v' u, A u v = true → A u v' = true).card ≤ minC)
    (hcompR : (Finset.univ.filter fun u : Fin n => ∀ u', (∀ v, A u v = true → A u' v = true) ∨ (∀ v, A u' v = true → A u v = true)).card ≤ compR)
    (hcompC : (Finset.univ.filter fun v : Fin m => ∀ v', (∀ u, A u v = true → A u v' = true) ∨ (∀ u, A u v' = true → A u v = true)).card ≤ compC)
    (hclsR : ∀ u0 : Fin n, (Finset.univ.filter fun u : Fin n => ∀ v, A u v = A u0 v).card ≤ clsR)
    (hclsC : ∀ v0 : Fin m, (Finset.univ.filter fun v : Fin m => ∀ u, A u v = A u v0).card ≤ clsC)
    (hBmono : s + 1 < (n - minR) + (m - minC))
    (hBtree : s < (n - compR) + (m - compC))
    (hBshared : s < (n - clsR) + (m - clsC) + 1) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C := by
  classical
  rintro ⟨C, hF, hsz, hRep⟩
  let N := n + m
  let W : Finset ℕ := subW N C C.output
  let R : Finset ℕ := (Finset.range C.gates.length).filter fun k => N + k ∈ W
  let Rnot : Finset ℕ := R.filter fun k => (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.not
  let Win : Finset ℕ := W.filter fun i => i < N
  let Wgate : Finset ℕ := R.image fun k => N + k
  have hRle : R.card ≤ C.size := by
    calc R.card ≤ (Finset.range C.gates.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = C.size := Finset.card_range _
  have hdisj : Disjoint Win Wgate := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hw1 : w < N := (Finset.mem_filter.mp h1).2
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h2
    omega
  have hsubW : Win ∪ Wgate ⊆ W := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h2
      exact (Finset.mem_filter.mp hk).2
  have hWgate_card : Wgate.card = R.card := Finset.card_image_of_injective R (fun a b h => by omega)
  have hWcard : Win.card + R.card ≤ W.card := by
    calc Win.card + R.card = Win.card + Wgate.card := by rw [hWgate_card]
      _ = (Win ∪ Wgate).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ W.card := Finset.card_le_card hsubW
  let inDeg : ℕ → ℕ := fun u => ∑ k ∈ R, (effInputs N C k).count u
  have htotal_eq : ∑ u ∈ W, inDeg u = ∑ k ∈ R, (effInputs N C k).length := by
    dsimp [inDeg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hkW : N + k ∈ W := (Finset.mem_filter.mp hk).2
    have hsub : (effInputs N C k).toFinset ⊆ W := fun i hi =>
      subW_closed N C C.output k hklt hkW i (List.mem_toFinset.mp hi)
    have hlen : ∀ l : List ℕ, l.toFinset ⊆ W → ∑ u ∈ W, l.count u = l.length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a tl ih =>
        intro htl
        have haW : a ∈ W := htl (by simp)
        have htlW : tl.toFinset ⊆ W := fun i hi => htl (by simp [List.mem_toFinset.mp hi])
        simp only [List.count_cons, List.length_cons]
        rw [Finset.sum_add_distrib, ih htlW]
        have h1 : ∑ u ∈ W, (if a == u then 1 else 0) = 1 := by
          simp [beq_iff_eq, haW]
        omega
    exact hlen (effInputs N C k) hsub
  have htotal_le : ∑ k ∈ R, (effInputs N C k).length + Rnot.card ≤ 2 * R.card := by
    have hsplit : ∑ k ∈ R, ((effInputs N C k).length + if (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.not then 1 else 0) ≤
        ∑ _k ∈ R, 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hgk : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hklt
      have hlen := effInputs_len N C hF k hklt
      rw [hgk]
      cases hop : C.gates[k].op <;> simp only [hop, isNot, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hlen ⊢ <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsplit
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] at hsplit
    exact hsplit
  have hdeg_pos : ∀ u ∈ W.erase C.output, 1 ≤ inDeg u := by
    intro u hu
    have hne : u ≠ C.output := (Finset.mem_erase.mp hu).1
    have huW : u ∈ W := (Finset.mem_erase.mp hu).2
    obtain ⟨k, hk, hkW, huk⟩ := subW_parent N C C.output u huW hne
    have hkR : k ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkW⟩
    exact le_trans (List.count_pos_iff.mpr huk)
      (Finset.single_le_sum (f := fun j => (effInputs N C j).count u) (fun _ _ => Nat.zero_le _) hkR)
  have houtW : C.output ∈ W := self_mem_subW N C C.output
  have herase_card : (W.erase C.output).card + 1 = W.card := by
    rw [Finset.card_erase_of_mem houtW]
    have := Finset.card_pos.mpr ⟨C.output, houtW⟩
    omega
  let Ur : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.val ∉ W
  let Uc : Finset (Fin m) := Finset.univ.filter fun v : Fin m => n + v.val ∉ W
  have hWin_card : (n - Ur.card) + (m - Uc.card) ≤ Win.card := by
    let Rw : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.val ∈ W
    let Cw : Finset (Fin m) := Finset.univ.filter fun v : Fin m => n + v.val ∈ W
    have hRsum : Rw.card + Ur.card = n := by
      simpa [Rw, Ur] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun u : Fin n => u.val ∈ W)
    have hCsum : Cw.card + Uc.card = m := by
      simpa [Cw, Uc] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun v : Fin m => n + v.val ∈ W)
    let Sr : Finset ℕ := Rw.image Fin.val
    let Sc : Finset ℕ := Cw.image (fun v : Fin m => n + v.val)
    have hdisjRC : Disjoint Sr Sc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h2
      omega
    have hsubRC : Sr ∪ Sc ⊆ Win := by
      intro w hw
      rcases Finset.mem_union.mp hw with h1 | h2
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, by omega⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, by omega⟩
    have hSr : Sr.card = Rw.card := Finset.card_image_of_injective _ Fin.val_injective
    have hSc : Sc.card = Cw.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
    have hle : Rw.card + Cw.card ≤ Win.card := by
      calc Rw.card + Cw.card = Sr.card + Sc.card := by rw [hSr, hSc]
        _ = (Sr ∪ Sc).card := (Finset.card_union_of_disjoint hdisjRC).symm
        _ ≤ Win.card := Finset.card_le_card hsubRC
    omega
  by_cases hRnot0 : Rnot.card = 0
  · have hnonot : ∀ k, (hk : k < C.gates.length) → N + k ∈ W → C.gates[k].op ≠ GateOp.not := by
      intro k hk hkW hop
      have hmem : k ∈ Rnot := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkW⟩, ?_⟩
        rwa [List.getD_eq_getElem _ _ hk]
      have := Finset.card_pos.mpr ⟨k, hmem⟩
      omega
    have hUr_le : Ur.card ≤ minR := by
      refine le_trans (Finset.card_le_card ?_) hminR
      intro u hu
      have huW : u.val ∉ W := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u' v hAuv => ?_⟩
      rw [← hRep u v] at hAuv; rw [← hRep u' v]
      apply mono_of_no_not N C hF hnonot _ _ (repInput_len u v) (repInput_len u' v) _ C.output houtW hAuv
      intro i hi hiW hx
      rw [repInput_getD u v i hi] at hx
      rw [repInput_getD u' v i hi]
      split_ifs at hx ⊢ with h1
      · have heq : (⟨i, h1⟩ : Fin n) = u := decide_eq_true_eq.mp hx
        exact absurd (congrArg Fin.val heq ▸ hiW) huW
      · exact hx
    have hUc_le : Uc.card ≤ minC := by
      refine le_trans (Finset.card_le_card ?_) hminC
      intro v hv
      have hvW : n + v.val ∉ W := (Finset.mem_filter.mp hv).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v' u hAuv => ?_⟩
      rw [← hRep u v] at hAuv; rw [← hRep u v']
      apply mono_of_no_not N C hF hnonot _ _ (repInput_len u v) (repInput_len u v') _ C.output houtW hAuv
      intro i hi hiW hx
      rw [repInput_getD u v i hi] at hx
      rw [repInput_getD u v' i hi]
      split_ifs at hx ⊢ with h1
      · exact hx
      · have heq : (⟨i - n, by omega⟩ : Fin m) = v := decide_eq_true_eq.mp hx
        have hi_eq : i = n + v.val := by have := congrArg Fin.val heq; dsimp at this; omega
        exact absurd (hi_eq ▸ hiW) hvW
    have hsum_ge : W.card - 1 ≤ ∑ u ∈ W, inDeg u := by
      calc W.card - 1 = (W.erase C.output).card := by omega
        _ = ∑ _u ∈ W.erase C.output, 1 := by simp
        _ ≤ ∑ u ∈ W.erase C.output, inDeg u := Finset.sum_le_sum hdeg_pos
        _ ≤ ∑ u ∈ W, inDeg u := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    omega
  · have hRnot1 : 1 ≤ Rnot.card := Nat.pos_of_ne_zero hRnot0
    by_cases htree : ∀ u ∈ W, inDeg u ≤ 1
    · have hUr_le : Ur.card ≤ compR := by
        refine le_trans (Finset.card_le_card ?_) hcompR
        intro u hu
        have huW : u.val ∉ W := (Finset.mem_filter.mp hu).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u' => ?_⟩
        obtain ⟨p, hp⟩ := tree_unate N C hF W rfl R rfl htree u'.val (by omega) C.output houtW
        by_cases heq : u' = u
        · subst heq; exact Or.inl (fun _ h => h)
        · cases p
          · left
            intro v hAuv
            rw [← hRep u v] at hAuv; rw [← hRep u' v]
            have hstep := hp (oneEach u v) (oneEach u' v) (repInput_len u v) (repInput_len u' v)
              (fun i hi hiW hne => by
                rw [repInput_getD u v i hi, repInput_getD u' v i hi]
                split_ifs with h1
                · have hne1 : (⟨i, h1⟩ : Fin n) ≠ u := fun h => huW (congrArg Fin.val h ▸ hiW)
                  have hne2 : (⟨i, h1⟩ : Fin n) ≠ u' := fun h => hne (congrArg Fin.val h)
                  simp [hne1, hne2]
                · rfl)
              (by rw [repInput_getD u v u'.val (by omega)]; simp [u'.isLt, heq])
              (by rw [repInput_getD u' v u'.val (by omega)]; simp [u'.isLt])
            simp only [Bool.false_eq_true, ↓reduceIte] at hstep
            exact hstep hAuv
          · right
            intro v hAu'v
            rw [← hRep u' v] at hAu'v; rw [← hRep u v]
            have hstep := hp (oneEach u v) (oneEach u' v) (repInput_len u v) (repInput_len u' v)
              (fun i hi hiW hne => by
                rw [repInput_getD u v i hi, repInput_getD u' v i hi]
                split_ifs with h1
                · have hne1 : (⟨i, h1⟩ : Fin n) ≠ u := fun h => huW (congrArg Fin.val h ▸ hiW)
                  have hne2 : (⟨i, h1⟩ : Fin n) ≠ u' := fun h => hne (congrArg Fin.val h)
                  simp [hne1, hne2]
                · rfl)
              (by rw [repInput_getD u v u'.val (by omega)]; simp [u'.isLt, heq])
              (by rw [repInput_getD u' v u'.val (by omega)]; simp [u'.isLt])
            simp only [↓reduceIte] at hstep
            exact hstep hAu'v
      have hUc_le : Uc.card ≤ compC := by
        refine le_trans (Finset.card_le_card ?_) hcompC
        intro v hv
        have hvW : n + v.val ∉ W := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v' => ?_⟩
        obtain ⟨p, hp⟩ := tree_unate N C hF W rfl R rfl htree (n + v'.val) (by omega) C.output houtW
        by_cases heq : v' = v
        · subst heq; exact Or.inl (fun _ h => h)
        · cases p
          · left
            intro u hAuv
            rw [← hRep u v] at hAuv; rw [← hRep u v']
            have hstep := hp (oneEach u v) (oneEach u v') (repInput_len u v) (repInput_len u v')
              (fun i hi hiW hne => by
                rw [repInput_getD u v i hi, repInput_getD u v' i hi]
                split_ifs with h1
                · rfl
                · have hne1 : (⟨i - n, by omega⟩ : Fin m) ≠ v := fun h => hvW (by have := congrArg Fin.val h; dsimp at this; rw [show n + v.val = i by omega]; exact hiW)
                  have hne2 : (⟨i - n, by omega⟩ : Fin m) ≠ v' := fun h => hne (by have := congrArg Fin.val h; dsimp at this; omega)
                  simp [hne1, hne2])
              (by rw [repInput_getD u v (n + v'.val) (by omega)]; simp [show ¬ n + v'.val < n by omega, heq])
              (by rw [repInput_getD u v' (n + v'.val) (by omega)]; simp [show ¬ n + v'.val < n by omega])
            simp only [Bool.false_eq_true, ↓reduceIte] at hstep
            exact hstep hAuv
          · right
            intro u hAuv'
            rw [← hRep u v'] at hAuv'; rw [← hRep u v]
            have hstep := hp (oneEach u v) (oneEach u v') (repInput_len u v) (repInput_len u v')
              (fun i hi hiW hne => by
                rw [repInput_getD u v i hi, repInput_getD u v' i hi]
                split_ifs with h1
                · rfl
                · have hne1 : (⟨i - n, by omega⟩ : Fin m) ≠ v := fun h => hvW (by have := congrArg Fin.val h; dsimp at this; rw [show n + v.val = i by omega]; exact hiW)
                  have hne2 : (⟨i - n, by omega⟩ : Fin m) ≠ v' := fun h => hne (by have := congrArg Fin.val h; dsimp at this; omega)
                  simp [hne1, hne2])
              (by rw [repInput_getD u v (n + v'.val) (by omega)]; simp [show ¬ n + v'.val < n by omega, heq])
              (by rw [repInput_getD u v' (n + v'.val) (by omega)]; simp [show ¬ n + v'.val < n by omega])
            simp only [↓reduceIte] at hstep
            exact hstep hAuv'
      have hsum_ge : W.card - 1 ≤ ∑ u ∈ W, inDeg u := by
        calc W.card - 1 = (W.erase C.output).card := by omega
          _ = ∑ _u ∈ W.erase C.output, 1 := by simp
          _ ≤ ∑ u ∈ W.erase C.output, inDeg u := Finset.sum_le_sum hdeg_pos
          _ ≤ ∑ u ∈ W, inDeg u := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      omega
    · push Not at htree
      obtain ⟨u0, hu0W, hu0deg⟩ := htree
      have hsum_ge : W.card ≤ ∑ u ∈ W, inDeg u := by
        by_cases hu0out : u0 = C.output
        · subst hu0out
          have h1 := Finset.add_sum_erase W inDeg houtW
          have h2 : (W.erase C.output).card ≤ ∑ u ∈ W.erase C.output, inDeg u := by
            calc (W.erase C.output).card = ∑ _u ∈ W.erase C.output, 1 := by simp
              _ ≤ ∑ u ∈ W.erase C.output, inDeg u := Finset.sum_le_sum hdeg_pos
          omega
        · have hu0e : u0 ∈ W.erase C.output := Finset.mem_erase.mpr ⟨hu0out, hu0W⟩
          have h1 := Finset.add_sum_erase (W.erase C.output) inDeg hu0e
          have h2 : ((W.erase C.output).erase u0).card ≤ ∑ u ∈ (W.erase C.output).erase u0, inDeg u := by
            calc ((W.erase C.output).erase u0).card = ∑ _u ∈ (W.erase C.output).erase u0, 1 := by simp
              _ ≤ ∑ u ∈ (W.erase C.output).erase u0, inDeg u := Finset.sum_le_sum (fun u hu => hdeg_pos u (Finset.mem_of_mem_erase hu))
          have h3 : ((W.erase C.output).erase u0).card + 1 = (W.erase C.output).card := by
            rw [Finset.card_erase_of_mem hu0e]
            have := Finset.card_pos.mpr ⟨u0, hu0e⟩
            omega
          have h4 : ∑ u ∈ W.erase C.output, inDeg u ≤ ∑ u ∈ W, inDeg u :=
            Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
          omega
      have hUr_le : Ur.card ≤ clsR := by
        by_cases hne : Ur.Nonempty
        · obtain ⟨u0, hu0⟩ := hne
          have hu0W : u0.val ∉ W := (Finset.mem_filter.mp hu0).2
          refine le_trans (Finset.card_le_card ?_) (hclsR u0)
          intro u hu
          have huW : u.val ∉ W := (Finset.mem_filter.mp hu).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => ?_⟩
          rw [← hRep u v, ← hRep u0 v]
          exact wires_agree_of_subW N C hF C.output _ _ (repInput_len u v) (repInput_len u0 v)
            (fun i hi hiW => by
              rw [repInput_getD u v i hi, repInput_getD u0 v i hi]
              split_ifs with h1
              · have hne1 : (⟨i, h1⟩ : Fin n) ≠ u := fun h => huW (congrArg Fin.val h ▸ hiW)
                have hne2 : (⟨i, h1⟩ : Fin n) ≠ u0 := fun h => hu0W (congrArg Fin.val h ▸ hiW)
                simp [hne1, hne2]
              · rfl) C.output houtW
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
      have hUc_le : Uc.card ≤ clsC := by
        by_cases hne : Uc.Nonempty
        · obtain ⟨v0, hv0⟩ := hne
          have hv0W : n + v0.val ∉ W := (Finset.mem_filter.mp hv0).2
          refine le_trans (Finset.card_le_card ?_) (hclsC v0)
          intro v hv
          have hvW : n + v.val ∉ W := (Finset.mem_filter.mp hv).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u => ?_⟩
          rw [← hRep u v, ← hRep u v0]
          exact wires_agree_of_subW N C hF C.output _ _ (repInput_len u v) (repInput_len u v0)
            (fun i hi hiW => by
              rw [repInput_getD u v i hi, repInput_getD u v0 i hi]
              split_ifs with h1
              · rfl
              · have hne1 : (⟨i - n, by omega⟩ : Fin m) ≠ v := fun h => hvW (by have := congrArg Fin.val h; dsimp at this; rw [show n + v.val = i by omega]; exact hiW)
                have hne2 : (⟨i - n, by omega⟩ : Fin m) ≠ v0 := fun h => hv0W (by have := congrArg Fin.val h; dsimp at this; rw [show n + v0.val = i by omega]; exact hiW)
                simp [hne1, hne2]) C.output houtW
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
      omega

end PEqualNP.Outside.L_meta_19457_aux

theorem PEqualNP.Outside.L_meta_19457 : (¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (61 : ℕ).testBit (4 * u.val + v.val)) C)  := by
  exact PEqualNP.Outside.L_meta_19457_aux.rep_fanin2_lb (minR := 2) (minC := 0) (compR := 2) (compC := 1) (clsR := 2) (clsC := 2) _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) (by omega) (by omega)
