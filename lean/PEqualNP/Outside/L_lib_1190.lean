import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1190_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

private lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [stepWire]
    omega

private lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, List.foldl_append]

private lemma wiresOf_prefix (gs : List Gate) (x : List Bool) :
    ∃ t : List Bool, wiresOf gs x = x ++ t := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [wiresOf]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stepWire x g)
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, ?_⟩
    simp only [wiresOf, List.foldl_cons] at ht ⊢
    rw [ht]
    simp [stepWire, List.append_assoc]

private lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wiresOf gs x).getD w false = x.getD w false := by
  obtain ⟨t, ht⟩ := wiresOf_prefix gs x
  rw [ht, List.getD_append _ _ _ _ hw]

private lemma wiresOf_getD_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresOf gs x).getD (x.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (wiresOf (gs.take j) x).getD i false) := by
  have hsplit : gs = gs.take j ++ (gs[j]'hj) :: gs.drop (j + 1) := by
    have := (List.take_append_drop j gs).symm
    rw [List.drop_eq_getElem_cons hj] at this
    exact this
  conv_lhs => rw [hsplit, wiresOf_append]
  change (wiresOf (gs.drop (j + 1)) (stepWire (wiresOf (gs.take j) x) (gs[j]'hj))).getD (x.length + j) false = _
  have hlen : (wiresOf (gs.take j) x).length = x.length + j := by
    rw [wiresOf_length, List.length_take]
    omega
  rw [wiresOf_getD_lt (gs.drop (j + 1)) (stepWire (wiresOf (gs.take j) x) (gs[j]'hj)) (x.length + j)
    (by simp [stepWire, hlen])]
  simp [stepWire, hlen]

private lemma wiresOf_getD_gate_rb (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]'hj).inputs, i < x.length + j) :
    (wiresOf gs x).getD (x.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_getD_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := hrb i hi
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  have hlen : (wiresOf (gs.take j) x).length = x.length + j := by
    rw [wiresOf_length, List.length_take]
    omega
  conv_rhs => rw [hsplit, wiresOf_append]
  rw [wiresOf_getD_lt (gs.drop j) (wiresOf (gs.take j) x) i (by omega)]

private def inVec {n : ℕ} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ [false, true]

private lemma inVec_length {n : ℕ} (x : Fin n → Bool) : (inVec x).length = n + 2 := by
  simp [inVec]

private def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (inVec x)).getD w false

private lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wval C x i.val = x i := by
  unfold wval Circuit.wires
  change (wiresOf C.gates (inVec x)).getD i.val false = x i
  rw [wiresOf_getD_lt C.gates (inVec x) i.val (by rw [inVec_length]; omega)]
  unfold inVec
  rw [List.getD_append _ _ _ _ (by simp [i.isLt])]
  simp

private lemma wval_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    wval C x n = false := by
  unfold wval Circuit.wires
  change (wiresOf C.gates (inVec x)).getD n false = false
  rw [wiresOf_getD_lt C.gates (inVec x) n (by rw [inVec_length]; omega)]
  unfold inVec
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private lemma wval_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    wval C x (n + 1) = true := by
  unfold wval Circuit.wires
  change (wiresOf C.gates (inVec x)).getD (n + 1) false = true
  rw [wiresOf_getD_lt C.gates (inVec x) (n + 1) (by rw [inVec_length]; omega)]
  unfold inVec
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j]'hj := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

private lemma wval_gate {n : ℕ} (C : Circuit) (hrb : ReadsBack (n + 2) C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wval C x (n + 2 + j) =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => wval C x i) := by
  unfold wval Circuit.wires
  change (wiresOf C.gates (inVec x)).getD (n + 2 + j) false = _
  rw [← inVec_length x]
  refine wiresOf_getD_gate_rb C.gates (inVec x) j hj ?_
  intro i hi
  rw [inVec_length]
  have := hrb j hj i
  rw [gateAt_eq_getElem C j hj] at this
  exact this hi

private lemma op_eval_mono (op : GateOp) (hop : op = .and ∨ op = .or)
    (l1 l2 : List Bool) (hle : List.Forall₂ (· ≤ ·) l1 l2) :
    op.eval l1 ≤ op.eval l2 := by
  rcases hop with rfl | rfl
  · induction hle with
    | nil => simp [GateOp.eval]
    | @cons a b _ _ hab _ ih =>
      simp only [GateOp.eval, List.all_cons, id_eq] at ih ⊢
      cases a <;> cases b
      · simp
      · simp
      · exact False.elim (Bool.false_ne_true (hab rfl))
      · simpa using ih
  · induction hle with
    | nil => simp [GateOp.eval]
    | @cons a b _ _ hab _ ih =>
      simp only [GateOp.eval, List.any_cons, id_eq] at ih ⊢
      cases a <;> cases b
      · simpa using ih
      · simp
      · exact False.elim (Bool.false_ne_true (hab rfl))
      · simp

private lemma forall₂_map_le {α : Type*} (l : List α) (f1 f2 : α → Bool)
    (h : ∀ a ∈ l, f1 a ≤ f2 a) : List.Forall₂ (· ≤ ·) (l.map f1) (l.map f2) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private lemma wval_mono_before {n : ℕ} (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (k : ℕ) (hnoNot : ∀ j, j < k → (hj : j < C.gates.length) → (C.gates[j]'hj).op ≠ .not)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i ≤ y i) :
    ∀ w < n + 2 + k, w < n + 2 + C.gates.length → wval C x w ≤ wval C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwk hwlen
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      change wval C x i.val ≤ wval C y i.val
      rw [wval_input, wval_input]
      exact hxy i
    · by_cases h0 : w = n
      · subst h0; rw [wval_false, wval_false]
      · by_cases h1 : w = n + 1
        · subst h1; rw [wval_true, wval_true]
        · let j := w - (n + 2)
          have hjw : w = n + 2 + j := by omega
          have hjk : j < k := by omega
          have hjlen : j < C.gates.length := by omega
          rw [hjw, wval_gate C hrb x j hjlen, wval_gate C hrb y j hjlen]
          have hmem : C.gates[j]'hjlen ∈ C.gates := List.getElem_mem hjlen
          have hop3 := (hfan _ hmem).1
          have hnn := hnoNot j hjk hjlen
          have hop2 : (C.gates[j]'hjlen).op = .and ∨ (C.gates[j]'hjlen).op = .or := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop3
            rcases hop3 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact False.elim (hnn h)
          apply op_eval_mono _ hop2
          apply forall₂_map_le
          intro u hu
          have hult : u < n + 2 + j := by
            have := hrb j hjlen u
            rw [gateAt_eq_getElem C j hjlen] at this
            exact this hu
          exact ih u (by omega) (by omega) (by omega)

private lemma wval_mono_with_fixed_not {n : ℕ} (C : Circuit) (hfan : FanInTwo C)
    (hrb : ReadsBack (n + 2) C) (q : ℕ) (hq : q < C.gates.length)
    (hother : ∀ j (hj : j < C.gates.length), j ≠ q → (C.gates[j]'hj).op ≠ .not)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i ≤ y i)
    (hnotEq : wval C x (n + 2 + q) ≤ wval C y (n + 2 + q)) :
    ∀ w < n + 2 + C.gates.length, wval C x w ≤ wval C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwlen
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      change wval C x i.val ≤ wval C y i.val
      rw [wval_input, wval_input]
      exact hxy i
    · by_cases h0 : w = n
      · subst h0; rw [wval_false, wval_false]
      · by_cases h1 : w = n + 1
        · subst h1; rw [wval_true, wval_true]
        · let j := w - (n + 2)
          have hjw : w = n + 2 + j := by omega
          have hjlen : j < C.gates.length := by omega
          by_cases hjq : j = q
          · rw [hjw, hjq]; exact hnotEq
          · rw [hjw, wval_gate C hrb x j hjlen, wval_gate C hrb y j hjlen]
            have hmem : C.gates[j]'hjlen ∈ C.gates := List.getElem_mem hjlen
            have hop3 := (hfan _ hmem).1
            have hnn := hother j hjlen hjq
            have hop2 : (C.gates[j]'hjlen).op = .and ∨ (C.gates[j]'hjlen).op = .or := by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop3
              rcases hop3 with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact False.elim (hnn h)
            apply op_eval_mono _ hop2
            apply forall₂_map_le
            intro u hu
            have hult : u < n + 2 + j := by
              have := hrb j hjlen u
              rw [gateAt_eq_getElem C j hjlen] at this
              exact this hu
            exact ih u (by omega) (by omega)

private def allTrue (n : ℕ) : Fin n → Bool := fun _ => true
private def drop1 {n : ℕ} (a : Fin n) : Fin n → Bool := fun i => decide (i ≠ a)
private def drop2 {n : ℕ} (a b : Fin n) : Fin n → Bool := fun i => decide (i ≠ a ∧ i ≠ b)

private lemma drop1_le_allTrue {n : ℕ} (a : Fin n) (i : Fin n) : drop1 a i ≤ allTrue n i := by
  simp [allTrue]

private lemma drop2_le_drop1 {n : ℕ} (a b : Fin n) (i : Fin n) : drop2 a b i ≤ drop1 b i := by
  by_cases h : i = b <;> simp [drop2, drop1, h]

private lemma allTrue_vc {n : ℕ} (G : Finset (Fin n × Fin n)) :
    ∀ e ∈ G, allTrue n e.1 = true ∨ allTrue n e.2 = true := fun _ _ => Or.inl rfl

private lemma drop1_vc {n : ℕ} (G : Finset (Fin n × Fin n)) (hord : ∀ e ∈ G, e.1 < e.2)
    (a : Fin n) : ∀ e ∈ G, drop1 a e.1 = true ∨ drop1 a e.2 = true := by
  intro e he
  have hlt := hord e he
  by_cases h1 : e.1 = a
  · right; simp [drop1]; intro h2; exact ne_of_lt hlt (h1.trans h2.symm)
  · left; simp [drop1, h1]

private lemma drop2_vc {n : ℕ} (G : Finset (Fin n × Fin n)) (hord : ∀ e ∈ G, e.1 < e.2)
    (a b : Fin n) (hnadj : ¬ ((a, b) ∈ G ∨ (b, a) ∈ G)) :
    ∀ e ∈ G, drop2 a b e.1 = true ∨ drop2 a b e.2 = true := by
  intro e he
  have hne : e.1 ≠ e.2 := ne_of_lt (hord e he)
  by_cases h1 : e.1 = a ∨ e.1 = b
  · right
    simp only [drop2, decide_eq_true_eq]
    rcases h1 with h1a | h1b
    · refine ⟨fun h2a => hne (h1a.trans h2a.symm), fun h2b => hnadj (Or.inl ?_)⟩
      have : e = (a, b) := Prod.ext h1a h2b
      exact this ▸ he
    · refine ⟨fun h2a => hnadj (Or.inr ?_), fun h2b => hne (h1b.trans h2b.symm)⟩
      have : e = (b, a) := Prod.ext h1b h2a
      exact this ▸ he
  · left
    push Not at h1
    simp [drop2, h1.1, h1.2]

private lemma xor_allTrue {n : ℕ} (e : Fin n × Fin n) :
    xor (allTrue n e.1) (allTrue n e.2) = false := rfl

private lemma xor_drop1 {n : ℕ} (e : Fin n × Fin n) (hne : e.1 ≠ e.2) (a : Fin n) :
    xor (drop1 a e.1) (drop1 a e.2) = decide (a = e.1 ∨ a = e.2) := by
  by_cases h1 : a = e.1
  · subst h1
    simp [drop1, hne.symm]
  · by_cases h2 : a = e.2
    · subst h2
      simp [drop1, hne]
    · simp [drop1, Ne.symm h1, Ne.symm h2, h1, h2]

private def isNotGate (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

private lemma isNotGate_eq_true_iff (g : Gate) : isNotGate g = true ↔ g.op = .not := by
  cases g with
  | mk op ins => cases op <;> simp [isNotGate]

private lemma notCount_eq_filter_isNotGate (C : Circuit) :
    notCount C = (C.gates.filter isNotGate).length := by
  unfold notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g with
  | mk op ins => cases op <;> rfl

private lemma notCount_eq_zero_iff (C : Circuit) :
    notCount C = 0 ↔ ∀ j (hj : j < C.gates.length), (C.gates[j]'hj).op ≠ .not := by
  rw [notCount_eq_filter_isNotGate, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h j hj hop
    have := h (C.gates[j]'hj) (List.getElem_mem hj)
    rw [(isNotGate_eq_true_iff _).mpr hop] at this
    exact this rfl
  · intro h g hg hnot
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact h j hj ((isNotGate_eq_true_iff _).mp hnot)

private lemma exists_unique_not (C : Circuit) (h1 : notCount C ≤ 1) (hpos : notCount C ≠ 0) :
    ∃ (q : ℕ) (hq : q < C.gates.length), (C.gates[q]'hq).op = .not ∧
      ∀ j (hj : j < C.gates.length), j ≠ q → (C.gates[j]'hj).op ≠ .not := by
  rw [notCount_eq_filter_isNotGate] at h1 hpos
  have hge1 : 0 < (C.gates.filter isNotGate).length := Nat.pos_of_ne_zero hpos
  obtain ⟨g, hg⟩ := List.exists_mem_of_length_pos hge1
  obtain ⟨hgmem, hgop⟩ := List.mem_filter.mp hg
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hgmem
  refine ⟨q, hq, (isNotGate_eq_true_iff _).mp hgop, ?_⟩
  intro j hj hjq hjop
  let idx := (List.range C.gates.length).filter (fun i => isNotGate (C.gates.getD i ⟨.or, []⟩))
  have hlen_eq : (C.gates.filter isNotGate).length = idx.length := by
    have hzip : C.gates = (List.range C.gates.length).map (fun i => C.gates.getD i ⟨.or, []⟩) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp [List.getD_eq_getElem?_getD, hi1]
    conv_lhs => rw [hzip, List.filter_map]
    rw [List.length_map]
    rfl
  have hnd : idx.Nodup := List.Nodup.filter _ List.nodup_range
  have hq_in : q ∈ idx := List.mem_filter.mpr ⟨List.mem_range.mpr hq, by
    simpa [List.getD_eq_getElem?_getD, hq] using hgop⟩
  have hj_in : j ∈ idx := List.mem_filter.mpr ⟨List.mem_range.mpr hj, by
    simp [List.getD_eq_getElem?_getD, hj, isNotGate_eq_true_iff, hjop]⟩
  have hsub : ({q, j} : Finset ℕ) ⊆ idx.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair (Ne.symm hjq), List.toFinset_card_of_nodup hnd] at hc
  omega

private def Zset {n : ℕ} (U : Finset (Fin n)) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  U.filter (fun a => wval C (drop1 a) w = false)

private def S1 {n : ℕ} (U : Finset (Fin n)) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  U.filter (fun a => wval C (drop1 a) w = true)

private lemma Zset_input_card_le_one {n : ℕ} (U : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (hw : w < n + 2) (ht : wval C (allTrue n) w = true) : (Zset U C w).card ≤ 1 := by
  by_cases hin : w < n
  · let i : Fin n := ⟨w, hin⟩
    have hsub : Zset U C w ⊆ {i} := by
      intro a ha
      have hfa := (Finset.mem_filter.mp ha).2
      change wval C (drop1 a) i.val = false at hfa
      rw [wval_input] at hfa
      simp only [drop1, decide_eq_false_iff_not, ne_eq, not_not] at hfa
      exact Finset.mem_singleton.mpr hfa.symm
    exact (Finset.card_le_card hsub).trans (by simp)
  · by_cases h0 : w = n
    · subst h0
      rw [wval_false] at ht
      exact False.elim (Bool.false_ne_true ht)
    · have h1 : w = n + 1 := by omega
      subst h1
      have hemp : Zset U C (n + 1) = ∅ := by
        ext a; simp [Zset, wval_true]
      simp [hemp]

private lemma card_le_one_laminar {α : Type*} [DecidableEq α] (A B : Finset α)
    (hA : A.card ≤ 1) (hB : B.card ≤ 1) : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  by_cases hdisj : Disjoint A B
  · exact Or.inr (Or.inr hdisj)
  · rw [Finset.not_disjoint_iff] at hdisj
    obtain ⟨x, hxA, hxB⟩ := hdisj
    have hAx : A = {x} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hxA, fun y hy => ?_⟩
      exact Finset.card_le_one.mp hA y hy x hxA
    have hBx : B = {x} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hxB, fun y hy => ?_⟩
      exact Finset.card_le_one.mp hB y hy x hxB
    rw [hAx, hBx]
    exact Or.inl (Finset.Subset.refl _)

private lemma gate_before_Z {n : ℕ} (U : Finset (Fin n)) (C : Circuit)
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (k : ℕ) (hk : k < C.gates.length) (hnn : (C.gates[k]'hk).op ≠ .not)
    (ht : wval C (allTrue n) (n + 2 + k) = true) :
    (Zset U C (n + 2 + k) = ∅) ∨
    (∃ u < n + 2 + k, wval C (allTrue n) u = true ∧ Zset U C (n + 2 + k) ⊆ Zset U C u) ∨
    ((C.gates[k]'hk).op = .and ∧ ∃ u v, u < n + 2 + k ∧ v < n + 2 + k ∧
      wval C (allTrue n) u = true ∧ wval C (allTrue n) v = true ∧
      Zset U C (n + 2 + k) = Zset U C u ∪ Zset U C v) := by
  have hmem : C.gates[k]'hk ∈ C.gates := List.getElem_mem hk
  have hop3 := (hfan _ hmem).1
  have hlen := (hfan _ hmem).2
  have hback : ∀ i ∈ (C.gates[k]'hk).inputs, i < n + 2 + k := by
    intro i hi
    have := hrb k hk i
    rw [gateAt_eq_getElem C k hk] at this
    exact this hi
  have hop2 : (C.gates[k]'hk).op = .and ∨ (C.gates[k]'hk).op = .or := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop3
    rcases hop3 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnn h)
  rcases hgi : (C.gates[k]'hk).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨c, l⟩⟩⟩
  · rcases hop2 with hop | hop
    · left
      ext a
      simp only [Zset, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _
      rw [wval_gate C hrb (drop1 a) k hk, hop, hgi]
      simp [GateOp.eval]
    · rw [wval_gate C hrb (allTrue n) k hk, hop, hgi] at ht
      simp [GateOp.eval] at ht
  · have hu : u < n + 2 + k := hback u (by rw [hgi]; simp)
    right; left
    refine ⟨u, hu, ?_, ?_⟩
    · rw [wval_gate C hrb (allTrue n) k hk, hgi] at ht
      rcases hop2 with hop | hop <;> simp [hop, GateOp.eval] at ht <;> exact ht
    · intro a ha
      simp only [Zset, Finset.mem_filter] at ha ⊢
      refine ⟨ha.1, ?_⟩
      have hfa := ha.2
      rw [wval_gate C hrb (drop1 a) k hk, hgi] at hfa
      rcases hop2 with hop | hop <;> simp [hop, GateOp.eval] at hfa <;> exact hfa
  · have hu : u < n + 2 + k := hback u (by rw [hgi]; simp)
    have hv : v < n + 2 + k := hback v (by rw [hgi]; simp)
    rcases hop2 with hop | hop
    · right; right
      rw [wval_gate C hrb (allTrue n) k hk, hop, hgi] at ht
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, Bool.and_eq_true] at ht
      refine ⟨hop, u, v, hu, hv, ht.1, ht.2, ?_⟩
      ext a
      simp only [Zset, Finset.mem_filter, Finset.mem_union]
      rw [wval_gate C hrb (drop1 a) k hk, hop, hgi]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, Bool.and_eq_false_iff]
      tauto
    · right; left
      rw [wval_gate C hrb (allTrue n) k hk, hop, hgi] at ht
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, Bool.or_eq_true] at ht
      rcases ht with htu | htv
      · refine ⟨u, hu, htu, fun a ha => ?_⟩
        simp only [Zset, Finset.mem_filter] at ha ⊢
        have hfa := ha.2
        rw [wval_gate C hrb (drop1 a) k hk, hop, hgi] at hfa
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, Bool.or_eq_false_iff] at hfa
        exact ⟨ha.1, hfa.1⟩
      · refine ⟨v, hv, htv, fun a ha => ?_⟩
        simp only [Zset, Finset.mem_filter] at ha ⊢
        have hfa := ha.2
        rw [wval_gate C hrb (drop1 a) k hk, hop, hgi] at hfa
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, Bool.or_eq_false_iff] at hfa
        exact ⟨ha.1, hfa.2⟩
  · rw [hgi] at hlen; simp at hlen

private lemma peel_le {n : ℕ} (U : Finset (Fin n)) (C : Circuit)
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (q : ℕ) (hq : q ≤ C.gates.length)
    (hnoNot : ∀ j (hj : j < q), (C.gates[j]'(by omega)).op ≠ .not) :
    ∀ k ≤ q, ∀ S : Finset ℕ,
      (∀ w ∈ S, w < n + 2 + k ∧ wval C (allTrue n) w = true) →
      (S.biUnion (Zset U C)).card ≤ S.card + k := by
  intro k
  induction k with
  | zero =>
    intro _ S hS
    calc (S.biUnion (Zset U C)).card
        ≤ ∑ w ∈ S, (Zset U C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ S, 1 := Finset.sum_le_sum fun w hw =>
          Zset_input_card_le_one U C w (by have := (hS w hw).1; omega) (hS w hw).2
      _ = S.card + 0 := by simp
  | succ k ih =>
    intro hkq S hS
    let W := n + 2 + k
    by_cases hW : W ∈ S
    · have hWt : wval C (allTrue n) W = true := (hS W hW).2
      have hkl : k < C.gates.length := by omega
      have hnn : (C.gates[k]'hkl).op ≠ .not := hnoNot k (by omega)
      have hSerase : ∀ w ∈ S.erase W, w < n + 2 + k ∧ wval C (allTrue n) w = true := by
        intro w hw
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
        have h1 := hS w hmem
        exact ⟨by omega, h1.2⟩
      have hcardE : (S.erase W).card + 1 = S.card := Finset.card_erase_add_one hW
      rcases gate_before_Z U C hfan hrb k hkl hnn hWt with hemp | ⟨u, hu, hut, hsub⟩ | ⟨_, u, v, hu, hv, hut, hvt, heq⟩
      · have hbi : S.biUnion (Zset U C) ⊆ (S.erase W).biUnion (Zset U C) := by
          intro a ha
          obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwW : w = W
          · subst hwW; rw [hemp] at haw; simp at haw
          · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwW, hwS⟩, haw⟩
        have h1 := Finset.card_le_card hbi
        have h2 := ih (by omega) (S.erase W) hSerase
        omega
      · let S' := insert u (S.erase W)
        have hS' : ∀ w ∈ S', w < n + 2 + k ∧ wval C (allTrue n) w = true := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact ⟨hu, hut⟩
          · exact hSerase w hw'
        have hbi : S.biUnion (Zset U C) ⊆ S'.biUnion (Zset U C) := by
          intro a ha
          obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwW : w = W
          · subst hwW; exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_insert_self _ _, hsub haw⟩
          · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwW, hwS⟩), haw⟩
        have h1 := Finset.card_le_card hbi
        have h2 := ih (by omega) S' hS'
        have h3 : S'.card ≤ (S.erase W).card + 1 := Finset.card_insert_le u (S.erase W)
        omega
      · let S' := insert u (insert v (S.erase W))
        have hS' : ∀ w ∈ S', w < n + 2 + k ∧ wval C (allTrue n) w = true := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact ⟨hu, hut⟩
          · rcases Finset.mem_insert.mp hw' with rfl | hw''
            · exact ⟨hv, hvt⟩
            · exact hSerase w hw''
        have hbi : S.biUnion (Zset U C) ⊆ S'.biUnion (Zset U C) := by
          intro a ha
          obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwW : w = W
          · subst hwW
            rw [heq] at haw
            rcases Finset.mem_union.mp haw with hau | hav
            · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_insert_self _ _, hau⟩
            · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hav⟩
          · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwW, hwS⟩)), haw⟩
        have h1 := Finset.card_le_card hbi
        have h2 := ih (by omega) S' hS'
        have h3 : S'.card ≤ (insert v (S.erase W)).card + 1 := Finset.card_insert_le u (insert v (S.erase W))
        have h4 : (insert v (S.erase W)).card ≤ (S.erase W).card + 1 := Finset.card_insert_le v (S.erase W)
        omega
    · have hS' : ∀ w ∈ S, w < n + 2 + k ∧ wval C (allTrue n) w = true := by
        intro w hw
        have h1 := hS w hw
        have hne : w ≠ W := fun h => hW (h ▸ hw)
        exact ⟨by omega, h1.2⟩
      have h2 := ih (by omega) S hS'
      omega

private lemma peel_eq {n : ℕ} (U : Finset (Fin n)) (C : Circuit)
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (q : ℕ) (hq : q ≤ C.gates.length)
    (hnoNot : ∀ j (hj : j < q), (C.gates[j]'(by omega)).op ≠ .not) :
    ∀ k ≤ q, ∀ S : Finset ℕ,
      (∀ w ∈ S, w < n + 2 + k ∧ wval C (allTrue n) w = true) →
      S.biUnion (Zset U C) = U →
      U.card = S.card + k →
      (∀ w ∈ S, (Zset U C w).Nonempty) ∧
      (∀ w1 ∈ S, ∀ w2 ∈ S, w1 ≠ w2 → Disjoint (Zset U C w1) (Zset U C w2)) ∧
      (∀ w1 < n + 2 + k, wval C (allTrue n) w1 = true →
        (∃ w ∈ S, Zset U C w1 ⊆ Zset U C w) ∨ Zset U C w1 = ∅) ∧
      (∀ w1 < n + 2 + k, wval C (allTrue n) w1 = true →
        ∀ w2 < n + 2 + k, wval C (allTrue n) w2 = true →
        Zset U C w1 ⊆ Zset U C w2 ∨ Zset U C w2 ⊆ Zset U C w1 ∨ Disjoint (Zset U C w1) (Zset U C w2)) := by
  intro k
  induction k with
  | zero =>
    intro _ S hS hcov hcard
    have hle1 : ∀ w ∈ S, (Zset U C w).card ≤ 1 := fun w hw =>
      Zset_input_card_le_one U C w (by have := (hS w hw).1; omega) (hS w hw).2
    have hsum_eq : ∑ w ∈ S, (Zset U C w).card = S.card := by
      have h1 : (S.biUnion (Zset U C)).card ≤ ∑ w ∈ S, (Zset U C w).card := Finset.card_biUnion_le
      have h2 : ∑ w ∈ S, (Zset U C w).card ≤ ∑ _w ∈ S, 1 := Finset.sum_le_sum hle1
      rw [Finset.sum_const, smul_eq_mul, mul_one] at h2
      rw [hcov] at h1
      omega
    have hcard1 : ∀ w ∈ S, (Zset U C w).card = 1 := by
      intro w hw
      by_contra hne
      have hlt : (Zset U C w).card < 1 := lt_of_le_of_ne (hle1 w hw) hne
      have hsum_lt : ∑ x ∈ S, (Zset U C x).card < ∑ _x ∈ S, 1 :=
        Finset.sum_lt_sum hle1 ⟨w, hw, hlt⟩
      rw [Finset.sum_const, smul_eq_mul, mul_one] at hsum_lt
      omega
    have hne : ∀ w ∈ S, (Zset U C w).Nonempty := fun w hw =>
      Finset.card_pos.mp (by rw [hcard1 w hw]; omega)
    have hdisj : ∀ w1 ∈ S, ∀ w2 ∈ S, w1 ≠ w2 → Disjoint (Zset U C w1) (Zset U C w2) := by
      intro w1 hw1 w2 hw2 h12
      by_contra hnd
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨a, ha1, ha2⟩ := hnd
      have heq1 : Zset U C w1 = {a} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨ha1, fun b hb => Finset.card_le_one.mp (hle1 w1 hw1) b hb a ha1⟩
      have heq2 : Zset U C w2 = {a} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨ha2, fun b hb => Finset.card_le_one.mp (hle1 w2 hw2) b hb a ha2⟩
      have hsub : S.biUnion (Zset U C) ⊆ (S.erase w1).biUnion (Zset U C) := by
        intro x hx
        obtain ⟨w, hwS, hxw⟩ := Finset.mem_biUnion.mp hx
        by_cases hww1 : w = w1
        · subst hww1
          rw [heq1] at hxw
          exact Finset.mem_biUnion.mpr ⟨w2, Finset.mem_erase.mpr ⟨h12.symm, hw2⟩, heq2.symm ▸ hxw⟩
        · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hww1, hwS⟩, hxw⟩
      have hc1 := Finset.card_le_card hsub
      have hc2 : ((S.erase w1).biUnion (Zset U C)).card ≤ (S.erase w1).card := by
        calc ((S.erase w1).biUnion (Zset U C)).card
            ≤ ∑ w ∈ S.erase w1, (Zset U C w).card := Finset.card_biUnion_le
          _ ≤ ∑ _w ∈ S.erase w1, 1 := Finset.sum_le_sum fun w hw => hle1 w (Finset.mem_of_mem_erase hw)
          _ = (S.erase w1).card := by simp
      have hc3 := Finset.card_erase_add_one hw1
      rw [hcov] at hc1
      omega
    refine ⟨hne, hdisj, ?_, ?_⟩
    · intro w1 hw1 ht1
      by_cases hemp : Zset U C w1 = ∅
      · exact Or.inr hemp
      · left
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have haU : a ∈ U := (Finset.mem_filter.mp ha).1
        rw [← hcov] at haU
        obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp haU
        have h1 : (Zset U C w1).card ≤ 1 := Zset_input_card_le_one U C w1 (by omega) ht1
        refine ⟨w, hwS, fun b hb => ?_⟩
        have hba : b = a := Finset.card_le_one.mp h1 b hb a ha
        exact hba ▸ haw
    · intro w1 hw1 ht1 w2 hw2 ht2
      exact card_le_one_laminar _ _
        (Zset_input_card_le_one U C w1 (by omega) ht1)
        (Zset_input_card_le_one U C w2 (by omega) ht2)
  | succ k ih =>
    intro hkq S hS hcov hcard
    let W := n + 2 + k
    have hW : W ∈ S := by
      by_contra hnot
      have hS' : ∀ w ∈ S, w < n + 2 + k ∧ wval C (allTrue n) w = true := by
        intro w hw
        have h1 := hS w hw
        have hne : w ≠ W := fun h => hnot (h ▸ hw)
        exact ⟨by omega, h1.2⟩
      have hle := peel_le U C hfan hrb q hq hnoNot k (by omega) S hS'
      rw [hcov] at hle
      omega
    have hWt : wval C (allTrue n) W = true := (hS W hW).2
    have hkl : k < C.gates.length := by omega
    have hnn : (C.gates[k]'hkl).op ≠ .not := hnoNot k (by omega)
    have hSerase : ∀ w ∈ S.erase W, w < n + 2 + k ∧ wval C (allTrue n) w = true := by
      intro w hw
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have h1 := hS w hmem
      exact ⟨by omega, h1.2⟩
    have hcardE : (S.erase W).card + 1 = S.card := Finset.card_erase_add_one hW
    have hgt : ∃ u v, u < n + 2 + k ∧ v < n + 2 + k ∧
        wval C (allTrue n) u = true ∧ wval C (allTrue n) v = true ∧
        Zset U C W = Zset U C u ∪ Zset U C v := by
      rcases gate_before_Z U C hfan hrb k hkl hnn hWt with hemp | ⟨u, hu, hut, hsub⟩ | ⟨_, u, v, hu, hv, hut, hvt, heq⟩
      · exfalso
        have hbi : U ⊆ (S.erase W).biUnion (Zset U C) := by
          intro a ha
          rw [← hcov] at ha
          obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwW : w = W
          · subst hwW; rw [hemp] at haw; simp at haw
          · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwW, hwS⟩, haw⟩
        have h1 := Finset.card_le_card hbi
        have h2 := peel_le U C hfan hrb q hq hnoNot k (by omega) (S.erase W) hSerase
        omega
      · exfalso
        let S' := insert u (S.erase W)
        have hS' : ∀ w ∈ S', w < n + 2 + k ∧ wval C (allTrue n) w = true := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact ⟨hu, hut⟩
          · exact hSerase w hw'
        have hbi : U ⊆ S'.biUnion (Zset U C) := by
          intro a ha
          rw [← hcov] at ha
          obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwW : w = W
          · subst hwW; exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_insert_self _ _, hsub haw⟩
          · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwW, hwS⟩), haw⟩
        have h1 := Finset.card_le_card hbi
        have h2 := peel_le U C hfan hrb q hq hnoNot k (by omega) S' hS'
        have h3 : S'.card ≤ (S.erase W).card + 1 := Finset.card_insert_le u (S.erase W)
        omega
      · exact ⟨u, v, hu, hv, hut, hvt, heq⟩
    obtain ⟨u, v, hu, hv, hut, hvt, heq⟩ := hgt
    let S' := insert u (insert v (S.erase W))
    have hS' : ∀ w ∈ S', w < n + 2 + k ∧ wval C (allTrue n) w = true := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact ⟨hu, hut⟩
      · rcases Finset.mem_insert.mp hw' with rfl | hw''
        · exact ⟨hv, hvt⟩
        · exact hSerase w hw''
    have hcov' : S'.biUnion (Zset U C) = U := by
      apply Finset.Subset.antisymm
      · intro a ha
        obtain ⟨w, _, haw⟩ := Finset.mem_biUnion.mp ha
        exact (Finset.mem_filter.mp haw).1
      · intro a ha
        rw [← hcov] at ha
        obtain ⟨w, hwS, haw⟩ := Finset.mem_biUnion.mp ha
        by_cases hwW : w = W
        · subst hwW
          rw [heq] at haw
          rcases Finset.mem_union.mp haw with hau | hav
          · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_insert_self _ _, hau⟩
          · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hav⟩
        · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwW, hwS⟩)), haw⟩
    have hle' := peel_le U C hfan hrb q hq hnoNot k (by omega) S' hS'
    rw [hcov'] at hle'
    have hci1 : S'.card ≤ (insert v (S.erase W)).card + 1 := Finset.card_insert_le u (insert v (S.erase W))
    have hci2 : (insert v (S.erase W)).card ≤ (S.erase W).card + 1 := Finset.card_insert_le v (S.erase W)
    have hcardS' : S'.card = S.card + 1 := by omega
    have hu_not : u ∉ S.erase W := by
      intro h
      have : S' = insert v (S.erase W) := by
        ext x; simp only [S', Finset.mem_insert]
        constructor
        · rintro (rfl | rfl | hx)
          · exact Or.inr h
          · exact Or.inl rfl
          · exact Or.inr hx
        · rintro (rfl | hx)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hx)
      have hc := Finset.card_insert_le v (S.erase W)
      rw [← this] at hc
      omega
    have hv_not : v ∉ S.erase W := by
      intro h
      have : S' = insert u (S.erase W) := by
        ext x; simp only [S', Finset.mem_insert]
        constructor
        · rintro (rfl | rfl | hx)
          · exact Or.inl rfl
          · exact Or.inr h
          · exact Or.inr hx
        · rintro (rfl | hx)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hx)
      have hc := Finset.card_insert_le u (S.erase W)
      rw [← this] at hc
      omega
    obtain ⟨hne', hdisj', hbelow', hlam'⟩ := ih (by omega) S' hS' hcov' (by omega)
    have huS' : u ∈ S' := Finset.mem_insert_self _ _
    have hvS' : v ∈ S' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hne : ∀ w ∈ S, (Zset U C w).Nonempty := by
      intro w hw
      by_cases hwW : w = W
      · subst hwW
        rw [heq]
        exact (hne' u huS').mono Finset.subset_union_left
      · exact hne' w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwW, hw⟩)))
    have hdisj : ∀ w1 ∈ S, ∀ w2 ∈ S, w1 ≠ w2 → Disjoint (Zset U C w1) (Zset U C w2) := by
      intro w1 hw1 w2 hw2 h12
      by_cases h1W : w1 = W
      · subst h1W
        have hw2e : w2 ∈ S.erase W := Finset.mem_erase.mpr ⟨h12.symm, hw2⟩
        have hw2S' : w2 ∈ S' := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw2e)
        have hdu := hdisj' u huS' w2 hw2S' (fun h => hu_not (h ▸ hw2e))
        have hdv := hdisj' v hvS' w2 hw2S' (fun h => hv_not (h ▸ hw2e))
        rw [heq]
        exact Finset.disjoint_union_left.mpr ⟨hdu, hdv⟩
      · by_cases h2W : w2 = W
        · subst h2W
          have hw1e : w1 ∈ S.erase W := Finset.mem_erase.mpr ⟨h12, hw1⟩
          have hw1S' : w1 ∈ S' := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw1e)
          have hdu := hdisj' w1 hw1S' u huS' (fun h => hu_not (h.symm ▸ hw1e))
          have hdv := hdisj' w1 hw1S' v hvS' (fun h => hv_not (h.symm ▸ hw1e))
          rw [heq]
          exact Finset.disjoint_union_right.mpr ⟨hdu, hdv⟩
        · exact hdisj' w1
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h1W, hw1⟩)))
            w2
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h2W, hw2⟩)))
            h12
    have hbelow : ∀ w1 < n + 2 + (k + 1), wval C (allTrue n) w1 = true →
        (∃ w ∈ S, Zset U C w1 ⊆ Zset U C w) ∨ Zset U C w1 = ∅ := by
      intro w1 hw1 ht1
      by_cases h1W : w1 = W
      · subst h1W; exact Or.inl ⟨W, hW, Finset.Subset.refl _⟩
      · rcases hbelow' w1 (by omega) ht1 with ⟨w', hw', hsub'⟩ | hemp
        · left
          rcases Finset.mem_insert.mp hw' with rfl | hw''
          · exact ⟨W, hW, hsub'.trans (heq ▸ Finset.subset_union_left)⟩
          · rcases Finset.mem_insert.mp hw'' with rfl | hw'''
            · exact ⟨W, hW, hsub'.trans (heq ▸ Finset.subset_union_right)⟩
            · exact ⟨w', Finset.mem_of_mem_erase hw''', hsub'⟩
        · exact Or.inr hemp
    have hlam : ∀ w1 < n + 2 + (k + 1), wval C (allTrue n) w1 = true →
        ∀ w2 < n + 2 + (k + 1), wval C (allTrue n) w2 = true →
        Zset U C w1 ⊆ Zset U C w2 ∨ Zset U C w2 ⊆ Zset U C w1 ∨ Disjoint (Zset U C w1) (Zset U C w2) := by
      intro w1 hw1 ht1 w2 hw2 ht2
      by_cases h1W : w1 = W
      · subst h1W
        by_cases h2W : w2 = W
        · subst h2W; exact Or.inl (Finset.Subset.refl _)
        · rcases hbelow' w2 (by omega) ht2 with ⟨w', hw', hsub'⟩ | hemp
          · rcases Finset.mem_insert.mp hw' with rfl | hw''
            · exact Or.inr (Or.inl (hsub'.trans (heq ▸ Finset.subset_union_left)))
            · rcases Finset.mem_insert.mp hw'' with rfl | hw'''
              · exact Or.inr (Or.inl (hsub'.trans (heq ▸ Finset.subset_union_right)))
              · right; right
                have hdu := hdisj' u huS' w' hw' (fun h => hu_not (h ▸ hw'''))
                have hdv := hdisj' v hvS' w' hw' (fun h => hv_not (h ▸ hw'''))
                rw [heq]
                exact (Finset.disjoint_union_left.mpr ⟨hdu, hdv⟩).mono_right hsub'
          · rw [hemp]; exact Or.inr (Or.inl (Finset.empty_subset _))
      · by_cases h2W : w2 = W
        · subst h2W
          rcases hbelow' w1 (by omega) ht1 with ⟨w', hw', hsub'⟩ | hemp
          · rcases Finset.mem_insert.mp hw' with rfl | hw''
            · exact Or.inl (hsub'.trans (heq ▸ Finset.subset_union_left))
            · rcases Finset.mem_insert.mp hw'' with rfl | hw'''
              · exact Or.inl (hsub'.trans (heq ▸ Finset.subset_union_right))
              · right; right
                have hdu := hdisj' w' hw' u huS' (fun h => hu_not (h.symm ▸ hw'''))
                have hdv := hdisj' w' hw' v hvS' (fun h => hv_not (h.symm ▸ hw'''))
                rw [heq]
                exact (Finset.disjoint_union_right.mpr ⟨hdu, hdv⟩).mono_left hsub'
          · rw [hemp]; exact Or.inl (Finset.empty_subset _)
        · exact hlam' w1 (by omega) ht1 w2 (by omega) ht2
    exact ⟨hne, hdisj, hbelow, hlam⟩

private lemma extract_not_guard {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hord : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (U : Finset (Fin n)) (hUdef : U = H.image Prod.fst ∪ H.image Prod.snd)
    (hU3 : 3 ≤ U.card)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C) (hnot1 : notCount C ≤ 1)
    (hcomp : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      ∀ e : ↥H, wval C x (tap e).val = xor (x e.val.1) (x e.val.2)) :
    ∃ (q : ℕ) (hq : q < C.gates.length), (C.gates[q]'hq).op = .not ∧
      (∀ j (hj : j < C.gates.length), j ≠ q → (C.gates[j]'hj).op ≠ .not) ∧
      (wval C (allTrue n) (n + 2 + q) = false) ∧
      (∀ a ∈ U, wval C (drop1 a) (n + 2 + q) = true) ∧
      ∃ h_in < n + 2 + q, wval C (allTrue n) h_in = true ∧ Zset U C h_in = U ∧
        (∀ x : Fin n → Bool, wval C x (n + 2 + q) = !(wval C x h_in)) := by
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hnotPos : notCount C ≠ 0 := by
    intro h0
    have hnn := (notCount_eq_zero_iff C).mp h0
    obtain ⟨a, ha⟩ := hUne
    rw [hUdef, Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha
    have hexE : ∃ e ∈ H, a = e.1 ∨ a = e.2 := by
      rcases ha with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact ⟨e, he, Or.inl rfl⟩
      · exact ⟨e, he, Or.inr rfl⟩
    obtain ⟨e, he, hae⟩ := hexE
    have hle := wval_mono_before C hfan hrb C.gates.length (fun j _ hj => hnn j hj)
      (drop1 a) (allTrue n) (drop1_le_allTrue a) (tap ⟨e, he⟩).val
      (by simpa [Circuit.size] using (tap ⟨e, he⟩).isLt)
      (by simpa [Circuit.size] using (tap ⟨e, he⟩).isLt)
    rw [hcomp (drop1 a) (drop1_vc G hord a) ⟨e, he⟩,
        hcomp (allTrue n) (allTrue_vc G) ⟨e, he⟩,
        xor_drop1 e (ne_of_lt (hord e (hHG he))) a, xor_allTrue e] at hle
    simp only [hae, decide_true] at hle
    exact Bool.false_ne_true (hle rfl)
  obtain ⟨q, hq, hqop, hother⟩ := exists_unique_not C hnot1 hnotPos
  have hnotVal_drop : ∀ a ∈ U, wval C (drop1 a) (n + 2 + q) = true ∧ wval C (allTrue n) (n + 2 + q) = false := by
    intro a ha
    rw [hUdef, Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha
    have hexE : ∃ e ∈ H, a = e.1 ∨ a = e.2 := by
      rcases ha with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact ⟨e, he, Or.inl rfl⟩
      · exact ⟨e, he, Or.inr rfl⟩
    obtain ⟨e, he, hae⟩ := hexE
    have hgt : ¬ (wval C (drop1 a) (n + 2 + q) ≤ wval C (allTrue n) (n + 2 + q)) := by
      intro hleNot
      have hle := wval_mono_with_fixed_not C hfan hrb q hq hother
        (drop1 a) (allTrue n) (drop1_le_allTrue a) hleNot (tap ⟨e, he⟩).val
        (by simpa [Circuit.size] using (tap ⟨e, he⟩).isLt)
      rw [hcomp (drop1 a) (drop1_vc G hord a) ⟨e, he⟩,
          hcomp (allTrue n) (allTrue_vc G) ⟨e, he⟩,
          xor_drop1 e (ne_of_lt (hord e (hHG he))) a, xor_allTrue e] at hle
      simp only [hae, decide_true] at hle
      exact Bool.false_ne_true (hle rfl)
    cases h1 : wval C (drop1 a) (n + 2 + q) <;> cases h2 : wval C (allTrue n) (n + 2 + q) <;> simp_all
  obtain ⟨a0, ha0⟩ := hUne
  have hnotAll : wval C (allTrue n) (n + 2 + q) = false := (hnotVal_drop a0 ha0).2
  have hnotDrop : ∀ a ∈ U, wval C (drop1 a) (n + 2 + q) = true := fun a ha => (hnotVal_drop a ha).1
  rcases hqi : (C.gates[q]'hq).inputs with _ | ⟨h_in, rest⟩
  · exfalso
    have h := wval_gate C hrb (allTrue n) q hq
    rw [hqop, hqi] at h
    simp [GateOp.eval] at h
    rw [h] at hnotAll
    exact Bool.false_ne_true hnotAll.symm
  · have h_in_lt : h_in < n + 2 + q := by
      have := hrb q hq h_in
      rw [gateAt_eq_getElem C q hq, hqi] at this
      exact this List.mem_cons_self
    have hnot_eq : ∀ x : Fin n → Bool, wval C x (n + 2 + q) = !(wval C x h_in) := by
      intro x
      rw [wval_gate C hrb x q hq, hqop, hqi]
      simp [GateOp.eval]
    have h_in_all : wval C (allTrue n) h_in = true := by
      have h := hnot_eq (allTrue n)
      rw [hnotAll] at h
      cases hh : wval C (allTrue n) h_in
      · rw [hh] at h; cases h
      · rfl
    have hZ : Zset U C h_in = U := by
      ext a
      simp only [Zset, Finset.mem_filter, and_iff_left_iff_imp]
      intro ha
      have h := hnot_eq (drop1 a)
      rw [hnotDrop a ha] at h
      cases hh : wval C (drop1 a) h_in
      · rfl
      · rw [hh] at h; cases h
    exact ⟨q, hq, hqop, hother, hnotAll, hnotDrop, h_in, h_in_lt, h_in_all, hZ, hnot_eq⟩

private lemma taps_after_and_inj {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hord : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (U : Finset (Fin n)) (hU3 : 3 ≤ U.card)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (q : ℕ) (hq : q < C.gates.length)
    (hother : ∀ j (hj : j < C.gates.length), j ≠ q → (C.gates[j]'hj).op ≠ .not)
    (hnotDrop : ∀ a ∈ U, wval C (drop1 a) (n + 2 + q) = true)
    (hcomp : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      ∀ e : ↥H, wval C x (tap e).val = xor (x e.val.1) (x e.val.2)) :
    (∀ e : ↥H, n + 2 + q < (tap e).val) ∧ Function.Injective tap := by
  have hafter : ∀ e : ↥H, n + 2 + q < (tap e).val := by
    intro e
    have hlt_e : e.val.1 < e.val.2 := hord e.val (hHG e.property)
    have hne_e : e.val.1 ≠ e.val.2 := ne_of_lt hlt_e
    have h1 : ¬ ((tap e).val < n + 2 + q) := by
      intro hlt
      have hle := wval_mono_before C hfan hrb q (fun j hj hjlen => hother j hjlen (by omega))
        (drop1 e.val.1) (allTrue n) (drop1_le_allTrue e.val.1) (tap e).val hlt
        (by simpa [Circuit.size] using (tap e).isLt)
      rw [hcomp (drop1 e.val.1) (drop1_vc G hord e.val.1) e,
          hcomp (allTrue n) (allTrue_vc G) e,
          xor_drop1 e.val hne_e e.val.1, xor_allTrue e.val] at hle
      simp only [true_or, decide_true] at hle
      exact Bool.false_ne_true (hle rfl)
    have h2 : (tap e).val ≠ n + 2 + q := by
      intro heq
      have hcard_lt : ({e.val.1, e.val.2} : Finset (Fin n)).card < U.card := by
        have hp := Finset.card_le_two (a := e.val.1) (b := e.val.2)
        omega
      obtain ⟨c, hcU, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
      have hv := hcomp (drop1 c) (drop1_vc G hord c) e
      rw [heq, hnotDrop c hcU, xor_drop1 e.val hne_e c] at hv
      simp [hcn.1, hcn.2] at hv
    omega
  have hinj : Function.Injective tap := by
    intro e f hef
    have hne_e := ne_of_lt (hord e.val (hHG e.property))
    have hne_f := ne_of_lt (hord f.val (hHG f.property))
    have h1 : e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 := by
      have hve := hcomp (drop1 e.val.1) (drop1_vc G hord e.val.1) e
      have hvf := hcomp (drop1 e.val.1) (drop1_vc G hord e.val.1) f
      rw [hef] at hve
      have heq := hve.symm.trans hvf
      rw [xor_drop1 e.val hne_e e.val.1, xor_drop1 f.val hne_f e.val.1] at heq
      simpa using heq.symm
    have h2 : e.val.2 = f.val.1 ∨ e.val.2 = f.val.2 := by
      have hve := hcomp (drop1 e.val.2) (drop1_vc G hord e.val.2) e
      have hvf := hcomp (drop1 e.val.2) (drop1_vc G hord e.val.2) f
      rw [hef] at hve
      have heq := hve.symm.trans hvf
      rw [xor_drop1 e.val hne_e e.val.2, xor_drop1 f.val hne_f e.val.2] at heq
      simpa using heq.symm
    have hlt_e := hord e.val (hHG e.property)
    have hlt_f := hord f.val (hHG f.property)
    apply Subtype.ext
    apply Prod.ext
    · rcases h1 with h1a | h1b
      · exact h1a
      · rcases h2 with h2a | h2b
        · exfalso; exact lt_asymm hlt_e (h1b.symm ▸ h2a.symm ▸ hlt_f)
        · exfalso; exact hne_e (h1b.trans h2b.symm)
    · rcases h2 with h2a | h2b
      · rcases h1 with h1a | h1b
        · exfalso; exact hne_e (h1a.trans h2a.symm)
        · exfalso; exact lt_asymm hlt_e (h1b.symm ▸ h2a.symm ▸ hlt_f)
      · exact h2b
  exact ⟨hafter, hinj⟩

private lemma lower_bound_and_clique {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hord : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (U : Finset (Fin n)) (hUdef : U = H.image Prod.fst ∪ H.image Prod.snd)
    (hU3 : 3 ≤ U.card)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C) (hnot1 : notCount C ≤ 1)
    (hcomp : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      ∀ e : ↥H, wval C x (tap e).val = xor (x e.val.1) (x e.val.2)) :
    U.card + H.card ≤ C.size ∧
    (∀ a ∈ U, ∀ b ∈ U, a ≠ b → (a, b) ∈ G ∨ (b, a) ∈ G) := by
  obtain ⟨q, hq, hqop, hother, hnotAll, hnotDrop, h_in, h_in_lt, h_in_all, hZ, hnot_eq⟩ :=
    extract_not_guard G H hord hHG U hUdef hU3 C tap hfan hrb hnot1 hcomp
  have hpeel := peel_le U C hfan hrb q (le_of_lt hq) (fun j hj => hother j (by omega) (by omega))
    q le_rfl {h_in} (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact ⟨h_in_lt, h_in_all⟩)
  rw [Finset.singleton_biUnion, hZ, Finset.card_singleton] at hpeel
  obtain ⟨hafter, hinj⟩ := taps_after_and_inj G H hord hHG U hU3 C tap hfan hrb q hq hother hnotDrop hcomp
  have hHle : H.card ≤ C.size - (q + 1) := by
    have hsub : Finset.univ.image (fun e : ↥H => (tap e).val) ⊆ Finset.Ico (n + 2 + q + 1) (n + 2 + C.size) := by
      intro w hw
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
      have h1 := hafter e
      have h2 := (tap e).isLt
      exact Finset.mem_Ico.mpr ⟨by omega, h2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun e f h => hinj (Fin.ext h)),
        Finset.card_univ, Fintype.card_coe, Nat.card_Ico] at hc
    omega
  have hsz : U.card + H.card ≤ C.size := by
    change U.card + H.card ≤ C.gates.length
    change H.card ≤ C.gates.length - (q + 1) at hHle
    omega
  have hclique : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → (a, b) ∈ G ∨ (b, a) ∈ G := by
    intro a ha b hb hab
    by_contra hnadj
    have hvc2 := drop2_vc G hord a b hnadj
    have ha' := ha
    rw [hUdef, Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha'
    have hexE : ∃ e ∈ H, a = e.1 ∨ a = e.2 := by
      rcases ha' with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · exact ⟨e, he, Or.inl rfl⟩
      · exact ⟨e, he, Or.inr rfl⟩
    obtain ⟨e, he, hae⟩ := hexE
    have hnot_le_in : wval C (drop2 a b) h_in ≤ wval C (drop1 b) h_in :=
      wval_mono_before C hfan hrb q (fun j hj hjlen => hother j hjlen (by omega))
        (drop2 a b) (drop1 b) (drop2_le_drop1 a b) h_in h_in_lt (by omega)
    have h_in_b : wval C (drop1 b) h_in = false := by
      have := hnot_eq (drop1 b)
      rw [hnotDrop b hb] at this
      cases hh : wval C (drop1 b) h_in
      · rfl
      · rw [hh] at this; cases this
    rw [h_in_b] at hnot_le_in
    have h_in_ab : wval C (drop2 a b) h_in = false := Bool.eq_false_of_le_false hnot_le_in
    have hnot_ab_le : wval C (drop2 a b) (n + 2 + q) ≤ wval C (drop1 b) (n + 2 + q) := by
      rw [hnot_eq, hnot_eq, h_in_ab, h_in_b]
    have hmono := wval_mono_with_fixed_not C hfan hrb q hq hother
      (drop2 a b) (drop1 b) (drop2_le_drop1 a b) hnot_ab_le (tap ⟨e, he⟩).val
      (by simpa [Circuit.size] using (tap ⟨e, he⟩).isLt)
    rw [hcomp (drop2 a b) hvc2 ⟨e, he⟩, hcomp (drop1 b) (drop1_vc G hord b) ⟨e, he⟩] at hmono
    have hne_b1 : e.1 ≠ b := by
      intro h
      rcases hae with h1 | h2
      · exact hab (h1.trans h)
      · exact hnadj (Or.inr (by have : e = (b, a) := Prod.ext h h2.symm; exact this ▸ hHG he))
    have hne_b2 : e.2 ≠ b := by
      intro h
      rcases hae with h1 | h2
      · exact hnadj (Or.inl (by have : e = (a, b) := Prod.ext h1.symm h; exact this ▸ hHG he))
      · exact hab (h2.trans h)
    have hne_e : e.1 ≠ e.2 := ne_of_lt (hord e (hHG he))
    have hdrop1_val : xor (drop1 b e.1) (drop1 b e.2) = false := by
      simp [drop1, hne_b1, hne_b2]
    have hdrop2_val : xor (drop2 a b e.1) (drop2 a b e.2) = true := by
      rcases hae with h1 | h2
      · have hne_a2 : e.2 ≠ a := fun h => hne_e (h1.symm.trans h.symm)
        simp [drop2, h1.symm, hne_a2, hne_b2]
      · have hne_a1 : e.1 ≠ a := fun h => hne_e (h.trans h2)
        simp [drop2, h2.symm, hne_a1, hne_b1]
    rw [hdrop1_val, hdrop2_val] at hmono
    exact Bool.false_ne_true (hmono rfl)
  exact ⟨hsz, hclique⟩

private lemma S1_tap {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hord : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (U : Finset (Fin n)) (hUdef : U = H.image Prod.fst ∪ H.image Prod.snd)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hcomp : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      ∀ e : ↥H, wval C x (tap e).val = xor (x e.val.1) (x e.val.2))
    (e : ↥H) : S1 U C (tap e).val = {e.val.1, e.val.2} := by
  have he1 : e.val.1 ∈ U := by
    rw [hUdef]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
  have he2 : e.val.2 ∈ U := by
    rw [hUdef]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt (hord e.val (hHG e.property))
  ext a
  simp only [S1, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  rw [hcomp (drop1 a) (drop1_vc G hord a) e, xor_drop1 e.val hne a]
  simp only [decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · rintro (rfl | rfl)
    · exact ⟨he1, Or.inl rfl⟩
    · exact ⟨he2, Or.inr rfl⟩

private lemma pair_eq_of_subset {n : ℕ} {e f : Fin n × Fin n}
    (he : e.1 < e.2) (hf : f.1 < f.2)
    (hsub : ({e.1, e.2} : Finset (Fin n)) ⊆ {f.1, f.2}) : e = f := by
  have h1 : e.1 = f.1 ∨ e.1 = f.2 := by
    have := hsub (Finset.mem_insert_self e.1 {e.2})
    simpa using this
  have h2 : e.2 = f.1 ∨ e.2 = f.2 := by
    have := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self e.2))
    simpa using this
  apply Prod.ext
  · rcases h1 with h1a | h1b
    · exact h1a
    · rcases h2 with h2a | h2b
      · exfalso; exact lt_asymm he (h1b.symm ▸ h2a.symm ▸ hf)
      · exfalso; exact ne_of_lt he (h1b.trans h2b.symm)
  · rcases h2 with h2a | h2b
    · rcases h1 with h1a | h1b
      · exfalso; exact ne_of_lt he (h1a.trans h2a.symm)
      · exfalso; exact lt_asymm he (h1b.symm ▸ h2a.symm ▸ hf)
    · exact h2b

private lemma forward_laminar {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hord : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (U : Finset (Fin n)) (hUdef : U = H.image Prod.fst ∪ H.image Prod.snd)
    (hU3 : 3 ≤ U.card)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C) (hnot1 : notCount C ≤ 1)
    (hsz : C.size ≤ U.card + H.card)
    (hcomp : ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      ∀ e : ↥H, wval C x (tap e).val = xor (x e.val.1) (x e.val.2)) :
    ∀ e ∈ H, ∀ f ∈ H,
      (U.erase e.1 |>.erase e.2) ⊆ (U.erase f.1 |>.erase f.2) ∨
      (U.erase f.1 |>.erase f.2) ⊆ (U.erase e.1 |>.erase e.2) ∨
      Disjoint (U.erase e.1 |>.erase e.2) (U.erase f.1 |>.erase f.2) := by
  obtain ⟨q, hq, hqop, hother, hnotAll, hnotDrop, h_in, h_in_lt, h_in_all, hZ, hnot_eq⟩ :=
    extract_not_guard G H hord hHG U hUdef hU3 C tap hfan hrb hnot1 hcomp
  have hpeel_le := peel_le U C hfan hrb q (le_of_lt hq) (fun j hj => hother j (by omega) (by omega))
    q le_rfl {h_in} (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact ⟨h_in_lt, h_in_all⟩)
  rw [Finset.singleton_biUnion, hZ, Finset.card_singleton] at hpeel_le
  obtain ⟨hafter, hinj⟩ := taps_after_and_inj G H hord hHG U hU3 C tap hfan hrb q hq hother hnotDrop hcomp
  have hsub_img : Finset.univ.image (fun e : ↥H => (tap e).val) ⊆ Finset.Ico (n + 2 + q + 1) (n + 2 + C.size) := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_Ico.mpr ⟨by have := hafter e; omega, (tap e).isLt⟩
  have hcard_img : (Finset.univ.image (fun e : ↥H => (tap e).val)).card = H.card := by
    rw [Finset.card_image_of_injective _ (fun e f h => hinj (Fin.ext h)), Finset.card_univ, Fintype.card_coe]
  have hcard_ico : (Finset.Ico (n + 2 + q + 1) (n + 2 + C.size)).card = C.size - (q + 1) := by
    rw [Nat.card_Ico]; omega
  have hHle : H.card ≤ C.size - (q + 1) := by
    have := Finset.card_le_card hsub_img
    rw [hcard_img, hcard_ico] at this
    exact this
  have hq_eq : U.card = 1 + q := by
    change C.gates.length ≤ U.card + H.card at hsz
    change H.card ≤ C.gates.length - (q + 1) at hHle
    omega
  have himg_eq : Finset.univ.image (fun e : ↥H => (tap e).val) = Finset.Ico (n + 2 + q + 1) (n + 2 + C.size) := by
    apply Finset.eq_of_subset_of_card_le hsub_img
    rw [hcard_img, hcard_ico]
    change C.gates.length ≤ U.card + H.card at hsz
    change C.gates.length - (q + 1) ≤ H.card
    omega
  have hsurj : ∀ w, n + 2 + q < w → w < n + 2 + C.size → ∃ f : ↥H, (tap f).val = w := by
    intro w h1 h2
    have hm : w ∈ Finset.univ.image (fun e : ↥H => (tap e).val) := by
      rw [himg_eq]; exact Finset.mem_Ico.mpr ⟨by omega, h2⟩
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hm
    exact ⟨f, hf⟩
  have hlam_all := (peel_eq U C hfan hrb q (le_of_lt hq) (fun j hj => hother j (by omega) (by omega))
    q le_rfl {h_in} (by intro w hw; rw [Finset.mem_singleton.mp hw]; exact ⟨h_in_lt, h_in_all⟩)
    (by rw [Finset.singleton_biUnion, hZ]) (by rw [Finset.card_singleton]; exact hq_eq)).2.2.2
  have hexW : ∀ e : ↥H, ∃ w < n + 2 + q, wval C (allTrue n) w = true ∧
      Zset U C w = (U.erase e.val.1 |>.erase e.val.2) := by
    intro e
    have hgt : n + 2 + q < (tap e).val := hafter e
    have hlt_sz : (tap e).val < n + 2 + C.gates.length := (tap e).isLt
    let j := (tap e).val - (n + 2)
    have hjw : (tap e).val = n + 2 + j := by omega
    have hjq : q < j := by omega
    have hjlen : j < C.gates.length := by omega
    have hmem : C.gates[j]'hjlen ∈ C.gates := List.getElem_mem hjlen
    have hop3 := (hfan _ hmem).1
    have hlen := (hfan _ hmem).2
    have hnn := hother j hjlen (by omega)
    have hop2 : (C.gates[j]'hjlen).op = .and ∨ (C.gates[j]'hjlen).op = .or := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop3
      rcases hop3 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hnn h)
    have hback : ∀ i ∈ (C.gates[j]'hjlen).inputs, i < (tap e).val := by
      intro i hi
      have := hrb j hjlen i
      rw [gateAt_eq_getElem C j hjlen] at this
      have := this hi
      omega
    have hS1e : S1 U C (tap e).val = {e.val.1, e.val.2} := S1_tap G H hord hHG U hUdef C tap hcomp e
    have hAll_e : wval C (allTrue n) (tap e).val = false := by
      rw [hcomp (allTrue n) (allTrue_vc G) e, xor_allTrue]
    have hS1not : S1 U C (n + 2 + q) = U := by
      ext a; simp only [S1, Finset.mem_filter, and_iff_left_iff_imp]; exact hnotDrop a
    have hno_sub_f : ∀ w, n + 2 + q < w → w < (tap e).val →
        ¬ (S1 U C w ⊆ {e.val.1, e.val.2}) ∧ ¬ ({e.val.1, e.val.2} ⊆ S1 U C w) := by
      intro w hw1 hw2
      obtain ⟨f, rfl⟩ := hsurj w hw1 (by omega)
      have hne_ef : e ≠ f := fun h => by rw [h] at hw2; exact lt_irrefl _ hw2
      rw [S1_tap G H hord hHG U hUdef C tap hcomp f]
      constructor
      · intro hsub
        exact hne_ef (Subtype.ext (pair_eq_of_subset (hord f.val (hHG f.property)) (hord e.val (hHG e.property)) hsub)).symm
      · intro hsub
        exact hne_ef (Subtype.ext (pair_eq_of_subset (hord e.val (hHG e.property)) (hord f.val (hHG f.property)) hsub))
    have hnot_sub_e : ¬ (U ⊆ {e.val.1, e.val.2}) := by
      intro hsub
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_le_two (a := e.val.1) (b := e.val.2)
      omega
    have hS1_false_before : ∀ w < n + 2 + q, wval C (allTrue n) w = false → S1 U C w = ∅ := by
      intro w hw hwf
      ext a
      simp only [S1, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _
      have hle := wval_mono_before C hfan hrb q (fun i hi hilen => hother i hilen (by omega))
        (drop1 a) (allTrue n) (drop1_le_allTrue a) w hw (by omega)
      rw [hwf] at hle
      simp [Bool.eq_false_of_le_false hle]
    rcases hgi : (C.gates[j]'hjlen).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨c, l⟩⟩⟩
    · exfalso
      rcases hop2 with hop | hop
      · have h := wval_gate C hrb (allTrue n) j hjlen
        rw [← hjw, hAll_e, hop, hgi] at h
        simp [GateOp.eval] at h
      · have he1U : e.val.1 ∈ {e.val.1, e.val.2} := Finset.mem_insert_self _ _
        rw [← hS1e] at he1U
        have ht := (Finset.mem_filter.mp he1U).2
        rw [hjw, wval_gate C hrb (drop1 e.val.1) j hjlen, hop, hgi] at ht
        simp [GateOp.eval] at ht
    · exfalso
      have hu : u < (tap e).val := hback u (by rw [hgi]; simp)
      have hS1u : S1 U C u = {e.val.1, e.val.2} := by
        rw [← hS1e]
        ext a
        simp only [S1, Finset.mem_filter]
        rw [hjw, wval_gate C hrb (drop1 a) j hjlen, hgi]
        rcases hop2 with hop | hop <;> simp [hop, GateOp.eval]
      have hAllu : wval C (allTrue n) u = false := by
        have h := wval_gate C hrb (allTrue n) j hjlen
        rw [← hjw, hAll_e, hgi] at h
        rcases hop2 with hop | hop <;> simp [hop, GateOp.eval] at h <;> exact h
      by_cases h1 : u < n + 2 + q
      · rw [hS1_false_before u h1 hAllu] at hS1u
        have : e.val.1 ∈ (∅ : Finset (Fin n)) := hS1u.symm ▸ Finset.mem_insert_self _ _
        simp at this
      · by_cases h2 : u = n + 2 + q
        · subst h2; rw [hS1not] at hS1u; exact hnot_sub_e (hS1u ▸ Finset.Subset.refl _)
        · exact (hno_sub_f u (by omega) hu).1 (hS1u ▸ Finset.Subset.refl _)
    · have hu : u < (tap e).val := hback u (by rw [hgi]; simp)
      have hv : v < (tap e).val := hback v (by rw [hgi]; simp)
      rcases hop2 with hop | hop
      · have hS1_inter : S1 U C u ∩ S1 U C v = {e.val.1, e.val.2} := by
          rw [← hS1e]
          ext a
          simp only [S1, Finset.mem_inter, Finset.mem_filter]
          rw [hjw, wval_gate C hrb (drop1 a) j hjlen, hop, hgi]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true]
          tauto
        have hsub_u : {e.val.1, e.val.2} ⊆ S1 U C u := hS1_inter ▸ Finset.inter_subset_left
        have hsub_v : {e.val.1, e.val.2} ⊆ S1 U C v := hS1_inter ▸ Finset.inter_subset_right
        have hu_le : u ≤ n + 2 + q := by
          by_contra hgtu
          exact (hno_sub_f u (by omega) hu).2 hsub_u
        have hv_le : v ≤ n + 2 + q := by
          by_contra hgtv
          exact (hno_sub_f v (by omega) hv).2 hsub_v
        have hnot_both_lt : ¬ (u < n + 2 + q ∧ v < n + 2 + q) := by
          rintro ⟨hult, hvlt⟩
          have hAll_uv : wval C (allTrue n) u = false ∨ wval C (allTrue n) v = false := by
            have h := wval_gate C hrb (allTrue n) j hjlen
            rw [← hjw, hAll_e, hop, hgi] at h
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true] at h
            exact Bool.and_eq_false_iff.mp h.symm
          rcases hAll_uv with huf | hvf
          · rw [hS1_false_before u hult huf] at hsub_u
            have : e.val.1 ∈ (∅ : Finset (Fin n)) := hsub_u (Finset.mem_insert_self _ _)
            simp at this
          · rw [hS1_false_before v hvlt hvf] at hsub_v
            have : e.val.1 ∈ (∅ : Finset (Fin n)) := hsub_v (Finset.mem_insert_self _ _)
            simp at this
        have hnot_both_eq : ¬ (u = n + 2 + q ∧ v = n + 2 + q) := by
          rintro ⟨rfl, rfl⟩
          rw [hS1not, Finset.inter_self] at hS1_inter
          exact hnot_sub_e (hS1_inter ▸ Finset.Subset.refl _)
        have hfinish : ∀ w < n + 2 + q, S1 U C w = {e.val.1, e.val.2} →
            ∃ w' < n + 2 + q, wval C (allTrue n) w' = true ∧ Zset U C w' = (U.erase e.val.1 |>.erase e.val.2) := by
          intro w hw hS1w
          have hwt : wval C (allTrue n) w = true := by
            cases hwf : wval C (allTrue n) w with
            | true => rfl
            | false =>
              rw [hS1_false_before w hw hwf] at hS1w
              have : e.val.1 ∈ (∅ : Finset (Fin n)) := hS1w.symm ▸ Finset.mem_insert_self _ _
              simp at this
          refine ⟨w, hw, hwt, ?_⟩
          ext a
          simp only [Zset, Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨haU, haf⟩
            refine ⟨fun ha2 => ?_, fun ha1 => ?_, haU⟩
            · have hm : a ∈ S1 U C w := hS1w.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ha2)
              have htr := (Finset.mem_filter.mp hm).2
              rw [haf] at htr; exact Bool.false_ne_true htr
            · have hm : a ∈ S1 U C w := by
                rw [hS1w, ha1]; exact Finset.mem_insert_self _ _
              have htr := (Finset.mem_filter.mp hm).2
              rw [haf] at htr; exact Bool.false_ne_true htr
          · rintro ⟨ha2, ha1, haU⟩
            refine ⟨haU, ?_⟩
            cases hwa : wval C (drop1 a) w with
            | false => rfl
            | true =>
              have : a ∈ S1 U C w := Finset.mem_filter.mpr ⟨haU, hwa⟩
              rw [hS1w] at this
              simp [ha1, ha2] at this
        by_cases huq : u = n + 2 + q
        · have hvlt : v < n + 2 + q := by omega
          have hsubU : S1 U C v ⊆ U := Finset.filter_subset _ _
          rw [huq, hS1not, Finset.inter_eq_right.mpr hsubU] at hS1_inter
          exact hfinish v hvlt hS1_inter
        · have hult : u < n + 2 + q := by omega
          have hvq : v = n + 2 + q := by omega
          have hsubU : S1 U C u ⊆ U := Finset.filter_subset _ _
          rw [hvq, hS1not, Finset.inter_eq_left.mpr hsubU] at hS1_inter
          exact hfinish u hult hS1_inter
      · exfalso
        have hAll_uv : wval C (allTrue n) u = false ∧ wval C (allTrue n) v = false := by
          have h := wval_gate C hrb (allTrue n) j hjlen
          rw [← hjw, hAll_e, hop, hgi] at h
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false] at h
          exact Bool.or_eq_false_iff.mp h.symm
        have hS1_union : S1 U C u ∪ S1 U C v = {e.val.1, e.val.2} := by
          rw [← hS1e]
          ext a
          simp only [S1, Finset.mem_union, Finset.mem_filter]
          rw [hjw, wval_gate C hrb (drop1 a) j hjlen, hop, hgi]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_eq_true]
          tauto
        have hsub_u : S1 U C u ⊆ {e.val.1, e.val.2} := hS1_union ▸ Finset.subset_union_left
        have hsub_v : S1 U C v ⊆ {e.val.1, e.val.2} := hS1_union ▸ Finset.subset_union_right
        have hlt_u : u < n + 2 + q := by
          by_contra hge
          by_cases heq : u = n + 2 + q
          · rw [heq, hS1not] at hsub_u; exact hnot_sub_e hsub_u
          · exact (hno_sub_f u (by omega) hu).1 hsub_u
        have hlt_v : v < n + 2 + q := by
          by_contra hge
          by_cases heq : v = n + 2 + q
          · rw [heq, hS1not] at hsub_v; exact hnot_sub_e hsub_v
          · exact (hno_sub_f v (by omega) hv).1 hsub_v
        rw [hS1_false_before u hlt_u hAll_uv.1, hS1_false_before v hlt_v hAll_uv.2, Finset.union_empty] at hS1_union
        have : e.val.1 ∈ (∅ : Finset (Fin n)) := hS1_union.symm ▸ Finset.mem_insert_self _ _
        simp at this
    · rw [hgi] at hlen; simp at hlen
  intro e he f hf
  obtain ⟨we, hwe_lt, hwe_t, hwe_eq⟩ := hexW ⟨e, he⟩
  obtain ⟨wf, hwf_lt, hwf_t, hwf_eq⟩ := hexW ⟨f, hf⟩
  rw [← hwe_eq, ← hwf_eq]
  exact hlam_all we hwe_lt hwe_t wf hwf_lt hwf_t

private lemma build_and_tree {n : ℕ} (F : Finset (Finset (Fin n)))
    (hFne : ∀ A ∈ F, A.Nonempty)
    (hFlam : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) :
    ∀ (m : ℕ) (V : Finset (Fin n)), V.card = m → 1 ≤ m →
    ∀ (pre : List Gate),
      ∃ (ext : List Gate) (root : ℕ),
        ext.length = m - 1 ∧
        (∀ g ∈ ext, g.op = .and ∧ g.inputs.length = 2) ∧
        (∀ j (hj : j < ext.length), ∀ i ∈ (ext[j]'hj).inputs, i < n + 2 + pre.length + j) ∧
        root < n + 2 + (pre ++ ext).length ∧
        (∀ x : Fin n → Bool,
          (wiresOf (pre ++ ext) (inVec x)).getD root false = decide (∀ a ∈ V, x a = true)) ∧
        (∀ A ∈ F, A ⊆ V → ∃ w < n + 2 + (pre ++ ext).length,
          ∀ x : Fin n → Bool,
            (wiresOf (pre ++ ext) (inVec x)).getD w false = decide (∀ a ∈ A, x a = true)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V hVcard hm pre
    by_cases hm1 : m = 1
    · subst hm1
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hVcard
      refine ⟨[], a.val, rfl, (fun _ h => by cases h), (fun _ hj => by simp at hj),
        (by simp; omega), ?_, ?_⟩
      · intro x
        simp only [List.append_nil]
        rw [wiresOf_getD_lt pre (inVec x) a.val (by rw [inVec_length]; omega)]
        unfold inVec
        rw [List.getD_append _ _ _ _ (by simp [a.isLt])]
        simp
      · intro A hAF hAV
        have hAe : A = {a} := by
          obtain ⟨b, hb⟩ := hFne A hAF
          have hba : b = a := Finset.mem_singleton.mp (hAV hb)
          apply Finset.Subset.antisymm hAV
          rw [Finset.singleton_subset_iff]
          exact hba ▸ hb
        refine ⟨a.val, by simp; omega, fun x => ?_⟩
        simp only [List.append_nil, hAe]
        rw [wiresOf_getD_lt pre (inVec x) a.val (by rw [inVec_length]; omega)]
        unfold inVec
        rw [List.getD_append _ _ _ _ (by simp [a.isLt])]
        simp
    · let M := F.filter (fun A => A ⊂ V)
      have hsplit : ∃ A1 A2 : Finset (Fin n),
          A1.Nonempty ∧ A2.Nonempty ∧ Disjoint A1 A2 ∧ A1 ∪ A2 = V ∧
          ∀ B ∈ F, B ⊂ V → B ⊆ A1 ∨ B ⊆ A2 := by
        by_cases hM : M.Nonempty
        · obtain ⟨A0, hA0M, hA0max⟩ := Finset.exists_max_image M Finset.card hM
          obtain ⟨hA0F, hA0ss⟩ := Finset.mem_filter.mp hA0M
          have hA0ne : A0.Nonempty := hFne A0 hA0F
          have hA2ne : (V \ A0).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hA0ss.2 h)
          refine ⟨A0, V \ A0, hA0ne, hA2ne, disjoint_sdiff_self_right,
            Finset.union_sdiff_of_subset hA0ss.1, ?_⟩
          intro B hBF hBss
          rcases hFlam A0 hA0F B hBF with hAB | hBA | hdisj
          · have hBM : B ∈ M := Finset.mem_filter.mpr ⟨hBF, hBss⟩
            have hle := hA0max B hBM
            have heq : A0 = B := Finset.eq_of_subset_of_card_le hAB hle
            exact Or.inl (heq ▸ Finset.Subset.refl _)
          · exact Or.inl hBA
          · right
            exact Finset.subset_sdiff.mpr ⟨hBss.1, hdisj.symm⟩
        · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
          have h2ne : (V.erase a).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
          refine ⟨{a}, V.erase a, Finset.singleton_nonempty a, h2ne,
            Finset.disjoint_singleton_left.mpr (Finset.notMem_erase a V),
            by rw [Finset.singleton_union, Finset.insert_erase ha], ?_⟩
          intro B hBF hBss
          exact False.elim (hM ⟨B, Finset.mem_filter.mpr ⟨hBF, hBss⟩⟩)
      obtain ⟨A1, A2, h1ne, h2ne, hdisj, hunion, hBs⟩ := hsplit
      have hc1 : 1 ≤ A1.card := Finset.card_pos.mpr h1ne
      have hc2 : 1 ≤ A2.card := Finset.card_pos.mpr h2ne
      have hcsum : A1.card + A2.card = m := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, hVcard]
      obtain ⟨ext1, r1, hlen1, hand1, hrb1, hr1_lt, hr1_ev, hF1⟩ :=
        ih A1.card (by omega) A1 rfl hc1 pre
      obtain ⟨ext2, r2, hlen2, hand2, hrb2, hr2_lt, hr2_ev, hF2⟩ :=
        ih A2.card (by omega) A2 rfl hc2 (pre ++ ext1)
      let top : Gate := ⟨.and, [r1, r2]⟩
      let ext := ext1 ++ ext2 ++ [top]
      let root := n + 2 + pre.length + (ext1.length + ext2.length)
      have hlen_ext : ext.length = m - 1 := by
        simp only [ext, List.length_append, List.length_singleton, hlen1, hlen2]
        omega
      have hpre_ext : pre ++ ext = ((pre ++ ext1) ++ ext2) ++ [top] := by
        simp [ext, List.append_assoc]
      have hlen_all : (pre ++ ext).length = pre.length + ext1.length + ext2.length + 1 := by
        simp [ext, List.length_append]
        omega
      have hpres1 : ∀ w < n + 2 + (pre ++ ext1).length, ∀ x : Fin n → Bool,
          (wiresOf (pre ++ ext) (inVec x)).getD w false =
          (wiresOf (pre ++ ext1) (inVec x)).getD w false := by
        intro w hw x
        rw [hpre_ext, wiresOf_append, wiresOf_append]
        have hl1 : (wiresOf (pre ++ ext1) (inVec x)).length = n + 2 + (pre ++ ext1).length := by
          rw [wiresOf_length, inVec_length]
        have hl2 : (wiresOf ext2 (wiresOf (pre ++ ext1) (inVec x))).length =
            n + 2 + (pre ++ ext1).length + ext2.length := by
          rw [wiresOf_length, hl1]
        rw [wiresOf_getD_lt [top] _ w (by omega), wiresOf_getD_lt ext2 _ w (by omega)]
      have hpres2 : ∀ w < n + 2 + ((pre ++ ext1) ++ ext2).length, ∀ x : Fin n → Bool,
          (wiresOf (pre ++ ext) (inVec x)).getD w false =
          (wiresOf ((pre ++ ext1) ++ ext2) (inVec x)).getD w false := by
        intro w hw x
        rw [hpre_ext, wiresOf_append]
        have hl2 : (wiresOf ((pre ++ ext1) ++ ext2) (inVec x)).length =
            n + 2 + ((pre ++ ext1) ++ ext2).length := by
          rw [wiresOf_length, inVec_length]
        rw [wiresOf_getD_lt [top] _ w (by omega)]
      have hroot_ev : ∀ x : Fin n → Bool,
          (wiresOf (pre ++ ext) (inVec x)).getD root false = decide (∀ a ∈ V, x a = true) := by
        intro x
        rw [hpre_ext, wiresOf_append]
        have hl2 : (wiresOf ((pre ++ ext1) ++ ext2) (inVec x)).length = root := by
          rw [wiresOf_length, inVec_length]
          simp [root, List.length_append]
          omega
        change (stepWire (wiresOf ((pre ++ ext1) ++ ext2) (inVec x)) top).getD root false = _
        unfold stepWire
        rw [← hl2, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero, top, GateOp.eval, List.map_cons,
          List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hv1 : (wiresOf ((pre ++ ext1) ++ ext2) (inVec x)).getD r1 false =
            decide (∀ a ∈ A1, x a = true) := by
          rw [wiresOf_append, wiresOf_getD_lt ext2 _ r1 (by rw [wiresOf_length, inVec_length]; exact hr1_lt)]
          exact hr1_ev x
        have hv2 : (wiresOf ((pre ++ ext1) ++ ext2) (inVec x)).getD r2 false =
            decide (∀ a ∈ A2, x a = true) := hr2_ev x
        rw [hv1, hv2, ← hunion]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2⟩ a (ha1 | ha2)
          · exact h1 a ha1
          · exact h2 a ha2
        · intro h
          exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
      refine ⟨ext, root, hlen_ext, ?_, ?_, (by rw [hlen_all]; dsimp [root]; omega), hroot_ev, ?_⟩
      · intro g hg
        simp only [ext, List.mem_append, List.mem_singleton] at hg
        rcases hg with (h1 | h2) | rfl
        · exact hand1 g h1
        · exact hand2 g h2
        · exact ⟨rfl, rfl⟩
      · intro j hj i hi
        by_cases hj1 : j < ext1.length
        · have heq : ext[j]'hj = ext1[j]'hj1 := by
            simp only [ext, List.getElem_append_left (by simp; omega : j < (ext1 ++ ext2).length),
              List.getElem_append_left hj1]
          rw [heq] at hi
          exact hrb1 j hj1 i hi
        · by_cases hj2 : j < ext1.length + ext2.length
          · have hlt2 : j - ext1.length < ext2.length := by omega
            have heq : ext[j]'hj = ext2[j - ext1.length]'hlt2 := by
              simp only [ext, List.getElem_append_left (by simp; omega : j < (ext1 ++ ext2).length),
                List.getElem_append_right (by omega : ext1.length ≤ j)]
            rw [heq] at hi
            have := hrb2 (j - ext1.length) hlt2 i hi
            rw [List.length_append] at this
            omega
          · have hjeq : j = ext1.length + ext2.length := by
              simp only [ext, List.length_append, List.length_singleton] at hj
              omega
            have heq : ext[j]'hj = top := by
              simp only [ext, List.getElem_append_right (by simp; omega : (ext1 ++ ext2).length ≤ j)]
              simp
            rw [heq] at hi
            simp only [top, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · rw [List.length_append] at hr1_lt; omega
            · rw [List.length_append, List.length_append] at hr2_lt; omega
      · intro A hAF hAV
        by_cases hAeq : A = V
        · subst hAeq
          exact ⟨root, by rw [hlen_all]; dsimp [root]; omega, hroot_ev⟩
        · have hAss : A ⊂ V := ssubset_iff_subset_ne.mpr ⟨hAV, hAeq⟩
          rcases hBs A hAF hAss with hA1 | hA2
          · obtain ⟨w, hwlt, hwev⟩ := hF1 A hAF hA1
            refine ⟨w, by rw [hlen_all]; rw [List.length_append] at hwlt; omega, fun x => ?_⟩
            rw [hpres1 w hwlt x, hwev x]
          · obtain ⟨w, hwlt, hwev⟩ := hF2 A hAF hA2
            refine ⟨w, by rw [hlen_all]; rw [List.length_append, List.length_append] at hwlt; omega, fun x => ?_⟩
            rw [hpres2 w hwlt x, hwev x]

private lemma backward_fits {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hord : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (U : Finset (Fin n)) (hUdef : U = H.image Prod.fst ∪ H.image Prod.snd)
    (hU3 : 3 ≤ U.card)
    (hclique : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → (a, b) ∈ G ∨ (b, a) ∈ G)
    (hlam : ∀ e ∈ H, ∀ f ∈ H,
      (U.erase e.1 |>.erase e.2) ⊆ (U.erase f.1 |>.erase f.2) ∨
      (U.erase f.1 |>.erase f.2) ⊆ (U.erase e.1 |>.erase e.2) ∨
      Disjoint (U.erase e.1 |>.erase e.2) (U.erase f.1 |>.erase f.2)) :
    ∃ (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size)),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      C.size ≤ U.card + H.card ∧ notCount C ≤ 1 ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e : ↥H, wval C x (tap e).val = xor (x e.val.1) (x e.val.2) := by
  let other : Fin n × Fin n → Finset (Fin n) := fun e => U.erase e.1 |>.erase e.2
  let F : Finset (Finset (Fin n)) := H.image other
  have hFne : ∀ A ∈ F, A.Nonempty := by
    intro A hA
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
    have h1 : (U.erase e.1).card ≥ U.card - 1 := by
      by_cases hm : e.1 ∈ U
      · rw [Finset.card_erase_of_mem hm]
      · rw [Finset.erase_eq_of_notMem hm]; omega
    have h2 : (other e).card ≥ (U.erase e.1).card - 1 := by
      dsimp [other]
      by_cases hm : e.2 ∈ U.erase e.1
      · rw [Finset.card_erase_of_mem hm]
      · rw [Finset.erase_eq_of_notMem hm]; omega
    exact Finset.card_pos.mp (by omega)
  have hFlam : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    intro A hA B hB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hB
    exact hlam e he f hf
  obtain ⟨tree, rootU, htree_len, htree_and, htree_rb, hroot_lt, hroot_ev, hF_wires⟩ :=
    build_and_tree F hFne hFlam U.card U rfl (by omega) []
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at htree_rb hroot_lt hroot_ev hF_wires
  have hother_wire : ∀ e : ↥H, ∃ w < n + 2 + tree.length,
      ∀ x : Fin n → Bool, (wiresOf tree (inVec x)).getD w false = decide (∀ a ∈ other e.val, x a = true) := by
    intro e
    have hmem : other e.val ∈ F := Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩
    have hsub : other e.val ⊆ U := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    exact hF_wires (other e.val) hmem hsub
  choose wireOf hwire_lt hwire_ev using hother_wire
  let wNot : ℕ := n + 2 + tree.length
  let gNot : Gate := ⟨.not, [rootU]⟩
  let hlist : List (Fin n × Fin n) := H.toList
  have hhlist_len : hlist.length = H.card := Finset.length_toList H
  let mkTapGate : Fin n × Fin n → Gate := fun e =>
    if h : e ∈ H then ⟨.and, [wNot, wireOf ⟨e, h⟩]⟩ else ⟨.and, [n, n]⟩
  let tapGates : List Gate := hlist.map mkTapGate
  let gs : List Gate := tree ++ [gNot] ++ tapGates
  let C : Circuit := ⟨gs, 0⟩
  have hCsize : C.size = U.card + H.card := by
    show gs.length = U.card + H.card
    simp only [gs, tapGates, List.length_append, List.length_singleton, List.length_map,
      htree_len, hhlist_len]
    omega
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, gs, List.mem_append, List.mem_singleton] at hg
    rcases hg with (ht | rfl) | htg
    · obtain ⟨hop, hlen⟩ := htree_and g ht
      exact ⟨by rw [hop]; simp, by omega⟩
    · exact ⟨by simp [gNot], by simp [gNot]⟩
    · obtain ⟨e, _, rfl⟩ := List.mem_map.mp htg
      dsimp only [mkTapGate]
      split_ifs <;> exact ⟨by simp, by simp⟩
  have hrb : ReadsBack (n + 2) C := by
    intro j hj i hi
    rw [gateAt_eq_getElem C j hj] at hi
    change i ∈ (gs[j]'hj).inputs at hi
    by_cases hj1 : j < tree.length
    · have hge : gs[j]'hj = tree[j]'hj1 := by
        simp only [gs, List.getElem_append_left (by simp; omega : j < (tree ++ [gNot]).length),
          List.getElem_append_left hj1]
      rw [hge] at hi
      exact htree_rb j hj1 i hi
    · by_cases hj2 : j = tree.length
      · have hge : gs[j]'hj = gNot := by
          subst hj2
          have h1 : tree.length < (tree ++ [gNot]).length := by simp
          calc gs[tree.length]'hj
              = (tree ++ [gNot])[tree.length]'h1 := by
                simp only [gs, List.getElem_append_left h1]
            _ = ([gNot])[tree.length - tree.length]'(by simp) :=
                List.getElem_append_right le_rfl
            _ = gNot := by simp
        rw [hge] at hi
        simp only [gNot, List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi
        omega
      · have hj' : j < gs.length := hj
        have hge : gs[j]'hj' = tapGates[j - (tree.length + 1)]'(by
            simp only [gs, List.length_append, List.length_singleton] at hj'; omega) := by
          simp only [gs, List.getElem_append_right (by simp; omega : (tree ++ [gNot]).length ≤ j),
            List.length_append, List.length_singleton]
        rw [hge, List.getElem_map] at hi
        dsimp only [mkTapGate] at hi
        split_ifs at hi with heH
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · dsimp [wNot]; omega
          · have := hwire_lt ⟨_, heH⟩; omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
  have hnotC : notCount C ≤ 1 := by
    rw [notCount_eq_filter_isNotGate]
    change ((tree ++ [gNot] ++ tapGates).filter isNotGate).length ≤ 1
    rw [List.filter_append, List.filter_append, List.length_append, List.length_append]
    have h1 : tree.filter isNotGate = [] := by
      rw [List.filter_eq_nil_iff]
      intro g hg
      rw [isNotGate_eq_true_iff, (htree_and g hg).1]
      intro h; cases h
    have h2 : tapGates.filter isNotGate = [] := by
      rw [List.filter_eq_nil_iff]
      intro g hg
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hg
      dsimp only [mkTapGate]
      split_ifs <;> simp [isNotGate]
    have h3 : [gNot].filter isNotGate = [gNot] := rfl
    rw [h1, h2, h3]
    simp
  let idxOf : ↥H → ℕ := fun e => hlist.idxOf e.val
  have hidx_lt : ∀ e : ↥H, idxOf e < H.card := by
    intro e
    have hmem : e.val ∈ hlist := Finset.mem_toList.mpr e.property
    rw [← hhlist_len]
    exact List.idxOf_lt_length_iff.mpr hmem
  let tap : ↥H → Fin (n + 2 + C.size) := fun e =>
    ⟨n + 2 + tree.length + 1 + idxOf e, by rw [hCsize, htree_len]; have := hidx_lt e; omega⟩
  refine ⟨C, tap, hfan, hrb, (by simp [C]), (by omega), hnotC, ?_⟩
  intro x hvc e
  have htree_pres : ∀ w < n + 2 + tree.length,
      wval C x w = (wiresOf tree (inVec x)).getD w false := by
    intro w hw
    unfold wval Circuit.wires
    change (wiresOf (tree ++ [gNot] ++ tapGates) (inVec x)).getD w false = _
    rw [wiresOf_append, wiresOf_append]
    have hl1 : (wiresOf tree (inVec x)).length = n + 2 + tree.length := by
      rw [wiresOf_length, inVec_length]
    have hl2 : (wiresOf [gNot] (wiresOf tree (inVec x))).length = n + 2 + tree.length + 1 := by
      rw [wiresOf_length, hl1]; simp
    rw [wiresOf_getD_lt tapGates _ w (by omega), wiresOf_getD_lt [gNot] _ w (by omega)]
  have hwNot_ev : wval C x wNot = !(decide (∀ a ∈ U, x a = true)) := by
    have hjlt : tree.length < C.gates.length := by
      change tree.length < gs.length; simp [gs]
    have hge : C.gates[tree.length]'hjlt = gNot := by
      change gs[tree.length]'hjlt = gNot
      simp only [gs, List.getElem_append_left (by simp : tree.length < (tree ++ [gNot]).length),
        List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
    change wval C x (n + 2 + tree.length) = _
    rw [wval_gate C hrb x tree.length hjlt, hge]
    simp only [gNot, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    rw [htree_pres rootU hroot_lt, hroot_ev x]
  have htap_ev : wval C x (tap e).val =
      (!(decide (∀ a ∈ U, x a = true)) && decide (∀ a ∈ other e.val, x a = true)) := by
    let k := idxOf e
    have hklt : k < hlist.length := by rw [hhlist_len]; exact hidx_lt e
    have hjlt : tree.length + 1 + k < C.gates.length := by
      change tree.length + 1 + k < gs.length
      simp only [gs, tapGates, List.length_append, List.length_singleton, List.length_map]
      omega
    have hge : C.gates[tree.length + 1 + k]'hjlt = ⟨.and, [wNot, wireOf e]⟩ := by
      change gs[tree.length + 1 + k]'hjlt = _
      simp only [gs, List.getElem_append_right (by simp : (tree ++ [gNot]).length ≤ tree.length + 1 + k),
        List.length_append, List.length_singleton]
      have hsub0 : tree.length + 1 + k - (tree.length + 1) = k := by omega
      simp only [hsub0, tapGates, List.getElem_map]
      have hget : hlist[k]'hklt = e.val := List.getElem_idxOf hklt
      rw [hget]
      dsimp only [mkTapGate]
      rw [dif_pos e.property]
    have htap_eq : (tap e).val = n + 2 + (tree.length + 1 + k) := by
      dsimp [tap, k]; omega
    rw [htap_eq, wval_gate C hrb x (tree.length + 1 + k) hjlt, hge]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [hwNot_ev, htree_pres (wireOf e) (hwire_lt e), hwire_ev e x]
  rw [htap_ev]
  have he1U : e.val.1 ∈ U := by
    rw [hUdef]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
  have he2U : e.val.2 ∈ U := by
    rw [hUdef]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
  have hne_e : e.val.1 ≠ e.val.2 := ne_of_lt (hord e.val (hHG e.property))
  have hatMostOneFalse : ∀ a ∈ U, ∀ b ∈ U, x a = false → x b = false → a = b := by
    intro a ha b hb hxa hxb
    by_contra hab
    rcases hclique a ha b hb hab with h1 | h2
    · rcases hvc (a, b) h1 with h | h
      · exact Bool.false_ne_true (hxa.symm.trans h)
      · exact Bool.false_ne_true (hxb.symm.trans h)
    · rcases hvc (b, a) h2 with h | h
      · exact Bool.false_ne_true (hxb.symm.trans h)
      · exact Bool.false_ne_true (hxa.symm.trans h)
  by_cases hall : ∀ a ∈ U, x a = true
  · rw [decide_eq_true hall, hall e.val.1 he1U, hall e.val.2 he2U]
    rfl
  · have hnotAll : decide (∀ a ∈ U, x a = true) = false := decide_eq_false hall
    rw [hnotAll]
    push Not at hall
    obtain ⟨a, haU, hxa⟩ := hall
    have hxaf : x a = false := Bool.eq_false_iff.mpr hxa
    have hotherTrue : ∀ b ∈ U, b ≠ a → x b = true := by
      intro b hb hba
      cases hxb : x b with
      | true => rfl
      | false => exact False.elim (hba (hatMostOneFalse b hb a haU hxb hxaf))
    by_cases ha1 : a = e.val.1
    · subst ha1
      have h2t : x e.val.2 = true := hotherTrue e.val.2 he2U hne_e.symm
      have hoth : ∀ b ∈ other e.val, x b = true := by
        intro b hb
        simp only [other, Finset.mem_erase] at hb
        exact hotherTrue b hb.2.2 hb.2.1
      rw [decide_eq_true hoth, hxaf, h2t]
      rfl
    · by_cases ha2 : a = e.val.2
      · subst ha2
        have h1t : x e.val.1 = true := hotherTrue e.val.1 he1U hne_e
        have hoth : ∀ b ∈ other e.val, x b = true := by
          intro b hb
          simp only [other, Finset.mem_erase] at hb
          exact hotherTrue b hb.2.2 hb.1
        rw [decide_eq_true hoth, hxaf, h1t]
        rfl
      · have h1t : x e.val.1 = true := hotherTrue e.val.1 he1U (Ne.symm ha1)
        have h2t : x e.val.2 = true := hotherTrue e.val.2 he2U (Ne.symm ha2)
        have haOth : a ∈ other e.val := by
          simp only [other, Finset.mem_erase]
          exact ⟨ha2, ha1, haU⟩
        have hnotOth : ¬ (∀ b ∈ other e.val, x b = true) := fun h => by
          rw [h a haOth] at hxaf; exact Bool.false_ne_true hxaf.symm
        rw [decide_eq_false hnotOth, h1t, h2t]
        rfl

end PEqualNP.Outside.L_lib_1190_aux

theorem PEqualNP.Outside.L_lib_1190 : (∀ (n : Nat) (G H : Finset (Fin n × Fin n)), (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
  let U := H.image Prod.fst ∪ H.image Prod.snd
  let adj := fun (a b : Fin n) => (a,b) ∈ G ∨ (b,a) ∈ G
  let other := fun (e : Fin n × Fin n) => U.erase e.1 |>.erase e.2
  let fits := fun (s : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : ↥H → Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
      C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e, (C.wires (List.ofFn x ++ [false,true])).getD (tap e).val false =
          xor (x e.val.1) (x e.val.2)
  3 ≤ U.card →
    (∀ s, fits s → U.card + H.card ≤ s) ∧
    (fits (U.card + H.card) ↔
      (∀ a ∈ U, ∀ b ∈ U, a ≠ b → adj a b) ∧
      ∀ e ∈ H, ∀ f ∈ H,
        other e ⊆ other f ∨ other f ⊆ other e ∨ Disjoint (other e) (other f))) := by
  intro n G H hord hHG U adj other fits hU3
  constructor
  · intro s ⟨C, tap, hfan, hrb, _, hsz, hnot1, hcomp⟩
    have h := (PEqualNP.Outside.L_lib_1190_aux.lower_bound_and_clique G H hord hHG U rfl hU3 C tap hfan hrb hnot1 hcomp).1
    omega
  · constructor
    · rintro ⟨C, tap, hfan, hrb, _, hsz, hnot1, hcomp⟩
      exact ⟨
        (PEqualNP.Outside.L_lib_1190_aux.lower_bound_and_clique G H hord hHG U rfl hU3 C tap hfan hrb hnot1 hcomp).2,
        PEqualNP.Outside.L_lib_1190_aux.forward_laminar G H hord hHG U rfl hU3 C tap hfan hrb hnot1 hsz hcomp⟩
    · rintro ⟨hclique, hlam⟩
      exact PEqualNP.Outside.L_lib_1190_aux.backward_fits G H hord hHG U rfl hU3 hclique hlam
