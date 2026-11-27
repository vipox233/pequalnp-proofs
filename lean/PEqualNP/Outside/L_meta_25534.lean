import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepReads

namespace PEqualNP.Outside.L_meta_25534_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.RepReads

private def val (C : Circuit) (x : List Bool) (k : ℕ) : Bool :=
  (wiresFrom C.gates x).getD k false

private def WellFormed (L : ℕ) (C : Circuit) : Prop :=
  (∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < L + j) ∧
  C.output < L + C.gates.length

private def rowInput {m : ℕ} (base : Fin m → List Bool) (r : ℕ) (c : Fin m) : List Bool :=
  (base c).set r true

private theorem length_rowInput {m : ℕ} (base : Fin m → List Bool) (r : ℕ) (c : Fin m) :
    (rowInput base r c).length = (base c).length := by
  simp [rowInput]

private theorem getD_set_true (l : List Bool) (r i : ℕ) (hr : r < l.length) :
    (l.set r true).getD i false = if i = r then true else l.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i = r
  · subst h
    simp [hr]
  · rw [List.getElem?_set_ne (Ne.symm h)]
    simp [h]

private theorem rowInput_getD {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (r : ℕ) (hr : r < L) (c : Fin m) (i : ℕ) :
    (rowInput base r c).getD i false = if i = r then true else (base c).getD i false :=
  getD_set_true (base c) r i (by rw [hlen c]; exact hr)

private theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false :=
  getD_wiresFrom C.gates x i hi

private theorem val_eq_eval (C : Circuit) (x : List Bool) :
    val C x C.output = C.eval x := rfl

private theorem val_out_of_bounds (C : Circuit) (x : List Bool) (k : ℕ)
    (hk : x.length + C.gates.length ≤ k) :
    val C x k = false := by
  unfold val
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact hk)

private theorem val_gate_take (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (x.length + j) =
      (C.gates[j]).op.eval
        ((C.gates[j]).inputs.map fun i => (wiresFrom (C.gates.take j) x).getD i false) := by
  unfold val
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  conv_lhs => rw [hsplit, wiresFrom_append]
  have hlen1 : (wiresFrom (C.gates.take j ++ [C.gates[j]]) x).length = x.length + j + 1 := by
    rw [length_wiresFrom, List.length_append, List.length_take_of_le (Nat.le_of_lt hj),
      List.length_singleton]
    omega
  rw [getD_wiresFrom _ _ _ (by omega), wiresFrom_snoc, getD_snoc, length_wiresFrom,
    List.length_take_of_le (Nat.le_of_lt hj)]
  simp

private theorem val_take_eq (C : Circuit) (x : List Bool) (j i : ℕ) (hj : j ≤ C.gates.length)
    (hi : i < x.length + j) :
    (wiresFrom (C.gates.take j) x).getD i false = val C x i := by
  unfold val
  have hlen : (wiresFrom (C.gates.take j) x).length = x.length + j := by
    rw [length_wiresFrom, List.length_take_of_le hj]
  conv_rhs =>
    rw [← List.take_append_drop j C.gates, wiresFrom_append, getD_wiresFrom _ _ _ (by omega)]

private theorem val_gate_wf {L : ℕ} (C : Circuit) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (j : ℕ) (hj : j < C.gates.length) :
    val C x (L + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map (val C x)) := by
  rw [← hx, val_gate_take C x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := by rw [hx]; exact hW.1 j hj i hi
  exact val_take_eq C x j i (Nat.le_of_lt hj) hilt

private theorem op_mono_mem (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i ∈ g.inputs, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i hi (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hi hv⟩

private theorem val_le_of_exceptions (L : ℕ) (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (x y : List Bool) (hx : x.length = L) (hy : y.length = L)
    (E : Set ℕ)
    (hIn : ∀ i < L, i ∉ E → x.getD i false = true → y.getD i false = true)
    (hGate : ∀ j (hj : j < C.gates.length), L + j ∉ E →
      (val C x (L + j) = true → val C y (L + j) = true) ∨
      (∀ i ∈ (C.gates[j]).inputs, i ∉ E)) :
    ∀ k, k ∉ E → val C x k = true → val C y k = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkE hval
    by_cases hkL : k < L
    · rw [val_input C x k (by omega)] at hval
      rw [val_input C y k (by omega)]
      exact hIn k hkL hkE hval
    · by_cases hkB : k < L + C.gates.length
      · set j := k - L
        have hj : j < C.gates.length := by omega
        have hkj : k = L + j := by omega
        rw [hkj] at hkE hval ⊢
        rcases hGate j hj hkE with hdir | hclean
        · exact hdir hval
        · rw [val_gate_wf C hW x hx j hj] at hval
          rw [val_gate_wf C hW y hy j hj]
          have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
          refine op_mono_mem (C.gates[j]) (hM _ hmem).1 (val C x) (val C y) ?_ hval
          intro i hi hxi
          have hilt : i < k := by
            have := hW.1 j hj i hi
            omega
          exact ih i hilt (hclean i hi) hxi
      · have hfalse := val_out_of_bounds C x k (by omega)
        rw [hfalse] at hval
        exact Bool.noConfusion hval

private def cleanGate (cur : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => decide (i < cur))⟩
  | GateOp.and => if g.inputs.all (fun i => decide (i < cur)) then g else ⟨GateOp.or, []⟩
  | _ => g

private def cleanGates (cur : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => cleanGate cur g :: cleanGates (cur + 1) gs

private theorem cleanGates_length (cur : ℕ) (gs : List Gate) :
    (cleanGates cur gs).length = gs.length := by
  induction gs generalizing cur with
  | nil => rfl
  | cons g gs ih => simp [cleanGates, ih]

private theorem cleanGate_mono2 (cur : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (cleanGate cur g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (cleanGate cur g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · rw [cleanGate, hop]
    split_ifs
    · exact ⟨by simp [hop], hlen⟩
    · exact ⟨by simp, by simp⟩
  · rw [cleanGate, hop]
    refine ⟨by simp, ?_⟩
    exact le_trans (List.length_filter_le _ _) hlen

private theorem cleanGates_mono2 (cur : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ cleanGates cur gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing cur with
  | nil => intro g hg; simp [cleanGates] at hg
  | cons g gs ih =>
    intro g' hg'
    simp only [cleanGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact cleanGate_mono2 cur g (hgs g (by simp))
    · exact ih (cur + 1) (fun g'' h => hgs g'' (by simp [h])) g' hg'

private theorem cleanGate_wf (cur : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ i ∈ (cleanGate cur g).inputs, i < cur := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · rw [cleanGate, hop]
    split_ifs with hall
    · intro i hi
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      exact hall i hi
    · intro i hi; simp at hi
  · rw [cleanGate, hop]
    intro i hi
    simp only [List.mem_filter, decide_eq_true_eq] at hi
    exact hi.2

private theorem cleanGates_wf (cur : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ j (hj : j < (cleanGates cur gs).length), ∀ i ∈ ((cleanGates cur gs)[j]).inputs, i < cur + j := by
  induction gs generalizing cur with
  | nil => intro j hj; simp [cleanGates] at hj
  | cons g gs ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [cleanGates, List.getElem_cons_zero, Nat.add_zero]
      exact cleanGate_wf cur g (hgs g (by simp))
    | succ j =>
      simp only [cleanGates, List.getElem_cons_succ]
      intro i hi
      have h1 := ih (cur + 1) (fun g' h => hgs g' (by simp [h])) j (by simpa [cleanGates] using hj) i hi
      omega

private theorem cleanGate_eval (w : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    (cleanGate w.length g).op.eval ((cleanGate w.length g).inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · by_cases hall : (g.inputs.all fun i => decide (i < w.length)) = true
    · simp only [cleanGate, hop, if_pos hall]
    · simp only [cleanGate, hop, if_neg hall, GateOp.eval, List.map_nil, List.any_nil,
        List.all_map, Function.comp_apply, id]
      symm
      rw [Bool.eq_false_iff]
      intro htrue
      rw [List.all_eq_true] at htrue
      simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hall
      obtain ⟨i, hi, hge⟩ := hall
      have h1 : w.getD i false = true := by simpa using htrue i hi
      have h2 := List.getD_eq_default w false (Nat.not_lt.1 hge)
      rw [h2] at h1
      exact Bool.noConfusion h1
  · simp only [cleanGate, hop, GateOp.eval, List.any_map, Function.comp_apply, id]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, ⟨hi, _⟩, hwi⟩
      exact ⟨i, hi, hwi⟩
    · rintro ⟨i, hi, hwi⟩
      refine ⟨i, ⟨hi, ?_⟩, hwi⟩
      by_contra hge
      have h2 := List.getD_eq_default w false (Nat.not_lt.1 hge)
      rw [h2] at hwi
      exact Bool.noConfusion hwi

private theorem wiresFrom_cleanGates (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ w : List Bool, wiresFrom (cleanGates w.length gs) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    change wiresFrom (cleanGates (w.length + 1) gs)
      (w ++ [(cleanGate w.length g).op.eval ((cleanGate w.length g).inputs.map (fun i => w.getD i false))]) =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
    rw [cleanGate_eval w g (hgs g (by simp))]
    set w' := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have hw' : w.length + 1 = w'.length := by simp [w']
    rw [hw']
    exact ih (fun g' h => hgs g' (by simp [h])) w'

private theorem normalize_circuit (L : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hout : C.output < L + C.gates.length) :
    ∃ C' : Circuit, Monotone2 C' ∧ WellFormed L C' ∧ C'.size = C.size ∧
      ∀ x : List Bool, x.length = L → C'.eval x = C.eval x := by
  refine ⟨⟨cleanGates L C.gates, C.output⟩, ?_, ?_, ?_, ?_⟩
  · exact cleanGates_mono2 L C.gates hM
  · refine ⟨cleanGates_wf L C.gates (fun g hg => (hM g hg).1), ?_⟩
    rw [cleanGates_length]
    exact hout
  · simp [Circuit.size, cleanGates_length]
  · intro x hx
    simp only [Circuit.eval, wires_eq]
    rw [← hx, wiresFrom_cleanGates C.gates (fun g hg => (hM g hg).1) x]

private def elimLoop (oldCur newCur : ℕ) (env : ℕ → Option ℕ) :
    List Gate → List Gate × (ℕ → Option ℕ)
  | [] => ([], env)
  | g :: gs =>
    match g.op with
    | GateOp.and =>
      if (g.inputs.map env).any Option.isNone then
        elimLoop (oldCur + 1) newCur (fun i => if i = oldCur then none else env i) gs
      else
        let g' : Gate := ⟨GateOp.and, g.inputs.filterMap env⟩
        let env' := fun i => if i = oldCur then some newCur else env i
        let res := elimLoop (oldCur + 1) (newCur + 1) env' gs
        (g' :: res.1, res.2)
    | GateOp.or =>
      let live := g.inputs.filterMap env
      match live with
      | [] =>
        elimLoop (oldCur + 1) newCur (fun i => if i = oldCur then none else env i) gs
      | [w'] =>
        elimLoop (oldCur + 1) newCur (fun i => if i = oldCur then some w' else env i) gs
      | _ =>
        let g' : Gate := ⟨GateOp.or, live⟩
        let env' := fun i => if i = oldCur then some newCur else env i
        let res := elimLoop (oldCur + 1) (newCur + 1) env' gs
        (g' :: res.1, res.2)
    | _ =>
      elimLoop (oldCur + 1) newCur (fun i => if i = oldCur then none else env i) gs

private theorem length_filterMap_le {α β : Type*} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : f a <;> simp [List.filterMap, h] <;> omega

private theorem length_filterMap_lt_of_none {α β : Type*} (f : α → Option β) (l : List α)
    (a : α) (ha : a ∈ l) (hf : f a = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [List.filterMap, hf, List.length_cons]
      exact Nat.lt_succ_of_le (length_filterMap_le f l)
    · cases hb : f b with
      | none =>
        simp only [List.filterMap, hb, List.length_cons]
        exact Nat.lt_succ_of_le (le_of_lt (ih ha))
      | some v =>
        simp only [List.filterMap, hb, List.length_cons]
        exact Nat.succ_lt_succ (ih ha)

private theorem elimLoop_length_le (oldCur newCur : ℕ) (env : ℕ → Option ℕ) (gs : List Gate) :
    (elimLoop oldCur newCur env gs).1.length ≤ gs.length := by
  induction gs generalizing oldCur newCur env with
  | nil => simp [elimLoop]
  | cons g gs ih =>
    simp only [elimLoop]
    cases h : g.op with
    | and =>
      split_ifs
      · exact le_trans (ih _ _ _) (Nat.le_succ _)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _ _ _)
    | or =>
      cases hl : g.inputs.filterMap env with
      | nil => exact le_trans (ih _ _ _) (Nat.le_succ _)
      | cons a t =>
        cases t with
        | nil => exact le_trans (ih _ _ _) (Nat.le_succ _)
        | cons b t' =>
          simp only [List.length_cons]
          exact Nat.succ_le_succ (ih _ _ _)
    | not => exact le_trans (ih _ _ _) (Nat.le_succ _)
    | mod _ => exact le_trans (ih _ _ _) (Nat.le_succ _)
    | maj => exact le_trans (ih _ _ _) (Nat.le_succ _)

private theorem elimLoop_mono2 (oldCur newCur : ℕ) (env : ℕ → Option ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (elimLoop oldCur newCur env gs).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing oldCur newCur env with
  | nil => intro g hg; simp [elimLoop] at hg
  | cons g gs ih =>
    have hgt := hM g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hM g' (by simp [h])
    simp only [elimLoop]
    cases hop : g.op with
    | and =>
      split_ifs
      · exact ih _ _ _ hgs
      · intro g' hg'
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact ⟨by simp, le_trans (length_filterMap_le env g.inputs) hgt.2⟩
        · exact ih _ _ _ hgs g' hg'
    | or =>
      cases hl : g.inputs.filterMap env with
      | nil => exact ih _ _ _ hgs
      | cons a t =>
        cases t with
        | nil => exact ih _ _ _ hgs
        | cons b t' =>
          intro g' hg'
          simp only [List.mem_cons] at hg'
          rcases hg' with rfl | hg'
          · refine ⟨by simp, ?_⟩
            have h1 := length_filterMap_le env g.inputs
            rw [hl] at h1
            exact le_trans h1 hgt.2
          · exact ih _ _ _ hgs g' hg'
    | not => exact ih _ _ _ hgs
    | mod _ => exact ih _ _ _ hgs
    | maj => exact ih _ _ _ hgs

private theorem elimLoop_drop_one (oldCur newCur : ℕ) (env : ℕ → Option ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ) (hrlt : r < oldCur) (hr : env r = none)
    (j : ℕ) (hj : j < gs.length) (hmem : r ∈ (gs[j]).inputs) :
    (elimLoop oldCur newCur env gs).1.length + 1 ≤ gs.length := by
  induction gs generalizing oldCur newCur env j with
  | nil => simp at hj
  | cons g gs ih =>
    have hgt := hM g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hM g' (by simp [h])
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hmem
      simp only [elimLoop]
      cases hop : g.op with
      | and =>
        have hany : (g.inputs.map env).any Option.isNone = true := by
          rw [List.any_eq_true]
          exact ⟨none, List.mem_map.2 ⟨r, hmem, hr⟩, rfl⟩
        rw [if_pos hany]
        have := elimLoop_length_le (oldCur + 1) newCur
          (fun i => if i = oldCur then none else env i) gs
        simp only [List.length_cons]
        omega
      | or =>
        have hlenlt := length_filterMap_lt_of_none env g.inputs r hmem hr
        have hlen2 := hgt.2
        cases hl : g.inputs.filterMap env with
        | nil =>
          have := elimLoop_length_le (oldCur + 1) newCur
            (fun i => if i = oldCur then none else env i) gs
          simp only [List.length_cons]
          omega
        | cons a t =>
          cases t with
          | nil =>
            have := elimLoop_length_le (oldCur + 1) newCur
              (fun i => if i = oldCur then some a else env i) gs
            simp only [List.length_cons]
            omega
          | cons b t' =>
            rw [hl] at hlenlt
            simp only [List.length_cons] at hlenlt
            omega
      | not =>
        have := elimLoop_length_le (oldCur + 1) newCur
          (fun i => if i = oldCur then none else env i) gs
        simp only [List.length_cons]
        omega
      | mod _ =>
        have := elimLoop_length_le (oldCur + 1) newCur
          (fun i => if i = oldCur then none else env i) gs
        simp only [List.length_cons]
        omega
      | maj =>
        have := elimLoop_length_le (oldCur + 1) newCur
          (fun i => if i = oldCur then none else env i) gs
        simp only [List.length_cons]
        omega
    | succ j =>
      simp only [List.getElem_cons_succ] at hmem
      have hj' : j < gs.length := by simpa using hj
      have hrne : r ≠ oldCur := Nat.ne_of_lt hrlt
      simp only [elimLoop]
      cases hop : g.op with
      | and =>
        split_ifs
        · have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j hj' hmem
          simp only [List.length_cons]
          omega
        · have h1 := ih (oldCur + 1) (newCur + 1) (fun i => if i = oldCur then some newCur else env i)
            hgs (by omega) (by simp [hrne, hr]) j hj' hmem
          simp only [List.length_cons]
          omega
      | or =>
        cases hl : g.inputs.filterMap env with
        | nil =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j hj' hmem
          simp only [List.length_cons]
          omega
        | cons a t =>
          cases t with
          | nil =>
            have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then some a else env i)
              hgs (by omega) (by simp [hrne, hr]) j hj' hmem
            simp only [List.length_cons]
            omega
          | cons b t' =>
            have h1 := ih (oldCur + 1) (newCur + 1) (fun i => if i = oldCur then some newCur else env i)
              hgs (by omega) (by simp [hrne, hr]) j hj' hmem
            simp only [List.length_cons]
            omega
      | not =>
        have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
          hgs (by omega) (by simp [hrne, hr]) j hj' hmem
        simp only [List.length_cons]
        omega
      | mod _ =>
        have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
          hgs (by omega) (by simp [hrne, hr]) j hj' hmem
        simp only [List.length_cons]
        omega
      | maj =>
        have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
          hgs (by omega) (by simp [hrne, hr]) j hj' hmem
        simp only [List.length_cons]
        omega

private theorem elimLoop_drop_two_same (oldCur newCur : ℕ) (env : ℕ → Option ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ) (hrlt : r < oldCur) (hr : env r = none)
    (j₁ j₂ : ℕ) (hlt : j₁ < j₂) (hj₂ : j₂ < gs.length)
    (hm₁ : r ∈ (gs[j₁]).inputs) (hm₂ : r ∈ (gs[j₂]).inputs) :
    (elimLoop oldCur newCur env gs).1.length + 2 ≤ gs.length := by
  induction gs generalizing oldCur newCur env j₁ j₂ with
  | nil => simp at hj₂
  | cons g gs ih =>
    have hgt := hM g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hM g' (by simp [h])
    have hrne : r ≠ oldCur := Nat.ne_of_lt hrlt
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [List.getElem_cons_zero] at hm₁
        simp only [List.getElem_cons_succ] at hm₂
        have hj₂' : j₂ < gs.length := by simpa using hj₂
        simp only [elimLoop]
        cases hop : g.op with
        | and =>
          have hany : (g.inputs.map env).any Option.isNone = true := by
            rw [List.any_eq_true]
            exact ⟨none, List.mem_map.2 ⟨r, hm₁, hr⟩, rfl⟩
          rw [if_pos hany]
          have h1 := elimLoop_drop_one (oldCur + 1) newCur
            (fun i => if i = oldCur then none else env i) gs hgs r (by omega)
            (by simp [hrne, hr]) j₂ hj₂' hm₂
          simp only [List.length_cons]
          omega
        | or =>
          have hlenlt := length_filterMap_lt_of_none env g.inputs r hm₁ hr
          have hlen2 := hgt.2
          cases hl : g.inputs.filterMap env with
          | nil =>
            have h1 := elimLoop_drop_one (oldCur + 1) newCur
              (fun i => if i = oldCur then none else env i) gs hgs r (by omega)
              (by simp [hrne, hr]) j₂ hj₂' hm₂
            simp only [List.length_cons]
            omega
          | cons a t =>
            cases t with
            | nil =>
              have h1 := elimLoop_drop_one (oldCur + 1) newCur
                (fun i => if i = oldCur then some a else env i) gs hgs r (by omega)
                (by simp [hrne, hr]) j₂ hj₂' hm₂
              simp only [List.length_cons]
              omega
            | cons b t' =>
              rw [hl] at hlenlt
              simp only [List.length_cons] at hlenlt
              omega
        | not =>
          have h1 := elimLoop_drop_one (oldCur + 1) newCur
            (fun i => if i = oldCur then none else env i) gs hgs r (by omega)
            (by simp [hrne, hr]) j₂ hj₂' hm₂
          simp only [List.length_cons]
          omega
        | mod _ =>
          have h1 := elimLoop_drop_one (oldCur + 1) newCur
            (fun i => if i = oldCur then none else env i) gs hgs r (by omega)
            (by simp [hrne, hr]) j₂ hj₂' hm₂
          simp only [List.length_cons]
          omega
        | maj =>
          have h1 := elimLoop_drop_one (oldCur + 1) newCur
            (fun i => if i = oldCur then none else env i) gs hgs r (by omega)
            (by simp [hrne, hr]) j₂ hj₂' hm₂
          simp only [List.length_cons]
          omega
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [List.getElem_cons_succ] at hm₁ hm₂
        have hj₂' : j₂ < gs.length := by simpa using hj₂
        have hlt' : j₁ < j₂ := by omega
        simp only [elimLoop]
        cases hop : g.op with
        | and =>
          split_ifs
          · have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
              hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
            simp only [List.length_cons]
            omega
          · have h1 := ih (oldCur + 1) (newCur + 1)
              (fun i => if i = oldCur then some newCur else env i)
              hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
            simp only [List.length_cons]
            omega
        | or =>
          cases hl : g.inputs.filterMap env with
          | nil =>
            have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
              hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
            simp only [List.length_cons]
            omega
          | cons a t =>
            cases t with
            | nil =>
              have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then some a else env i)
                hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
              simp only [List.length_cons]
              omega
            | cons b t' =>
              have h1 := ih (oldCur + 1) (newCur + 1)
                (fun i => if i = oldCur then some newCur else env i)
                hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
              simp only [List.length_cons]
              omega
        | not =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
          simp only [List.length_cons]
          omega
        | mod _ =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
          simp only [List.length_cons]
          omega
        | maj =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hm₁ hm₂
          simp only [List.length_cons]
          omega

private theorem elimLoop_drop_and_chain (oldCur newCur : ℕ) (env : ℕ → Option ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ) (hrlt : r < oldCur) (hr : env r = none)
    (j₁ j₂ : ℕ) (hlt : j₁ < j₂) (hj₂ : j₂ < gs.length)
    (hop₁ : (gs[j₁]).op = GateOp.and)
    (hm₁ : r ∈ (gs[j₁]).inputs) (hm₂ : oldCur + j₁ ∈ (gs[j₂]).inputs) :
    (elimLoop oldCur newCur env gs).1.length + 2 ≤ gs.length := by
  induction gs generalizing oldCur newCur env j₁ j₂ with
  | nil => simp at hj₂
  | cons g gs ih =>
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hM g' (by simp [h])
    have hrne : r ≠ oldCur := Nat.ne_of_lt hrlt
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [List.getElem_cons_zero, Nat.add_zero] at hop₁ hm₁ hm₂
        simp only [List.getElem_cons_succ] at hm₂
        have hj₂' : j₂ < gs.length := by simpa using hj₂
        simp only [elimLoop, hop₁]
        have hany : (g.inputs.map env).any Option.isNone = true := by
          rw [List.any_eq_true]
          exact ⟨none, List.mem_map.2 ⟨r, hm₁, hr⟩, rfl⟩
        rw [if_pos hany]
        have h1 := elimLoop_drop_one (oldCur + 1) newCur
          (fun i => if i = oldCur then none else env i) gs hgs oldCur (by omega)
          (by simp) j₂ hj₂' hm₂
        simp only [List.length_cons]
        omega
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [List.getElem_cons_succ] at hop₁ hm₁ hm₂
        have hj₂' : j₂ < gs.length := by simpa using hj₂
        have hlt' : j₁ < j₂ := by omega
        have hm₂' : (oldCur + 1) + j₁ ∈ (gs[j₂]).inputs := by
          have : (oldCur + 1) + j₁ = oldCur + (j₁ + 1) := by omega
          rw [this]
          exact hm₂
        simp only [elimLoop]
        cases hop : g.op with
        | and =>
          split_ifs
          · have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
              hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
            simp only [List.length_cons]
            omega
          · have h1 := ih (oldCur + 1) (newCur + 1)
              (fun i => if i = oldCur then some newCur else env i)
              hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
            simp only [List.length_cons]
            omega
        | or =>
          cases hl : g.inputs.filterMap env with
          | nil =>
            have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
              hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
            simp only [List.length_cons]
            omega
          | cons a t =>
            cases t with
            | nil =>
              have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then some a else env i)
                hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
              simp only [List.length_cons]
              omega
            | cons b t' =>
              have h1 := ih (oldCur + 1) (newCur + 1)
                (fun i => if i = oldCur then some newCur else env i)
                hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
              simp only [List.length_cons]
              omega
        | not =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
          simp only [List.length_cons]
          omega
        | mod _ =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
          simp only [List.length_cons]
          omega
        | maj =>
          have h1 := ih (oldCur + 1) newCur (fun i => if i = oldCur then none else env i)
            hgs (by omega) (by simp [hrne, hr]) j₁ j₂ hlt' hj₂' hop₁ hm₁ hm₂'
          simp only [List.length_cons]
          omega

private theorem eval_or_filterMap (env : ℕ → Option ℕ) (wOld wNew : List Bool)
    (l : List ℕ)
    (hEq : ∀ i ∈ l, wOld.getD i false =
      match env i with | none => false | some j => wNew.getD j false) :
    (l.map fun i => wOld.getD i false).any id =
      ((l.filterMap env).map fun j => wNew.getD j false).any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := hEq a (by simp)
    have hl := ih (fun i hi => hEq i (by simp [hi]))
    cases he : env a with
    | none =>
      rw [he] at ha
      dsimp only at ha
      simp only [List.map_cons, List.any_cons, List.filterMap, he, id_eq, ha, Bool.false_or]
      exact hl
    | some j =>
      rw [he] at ha
      dsimp only at ha
      simp only [List.map_cons, List.any_cons, List.filterMap, he, id_eq, ha]
      rw [hl]

private theorem eval_and_filterMap (env : ℕ → Option ℕ) (wOld wNew : List Bool)
    (l : List ℕ)
    (hNoNone : (l.map env).any Option.isNone = false)
    (hEq : ∀ i ∈ l, wOld.getD i false =
      match env i with | none => false | some j => wNew.getD j false) :
    (l.map fun i => wOld.getD i false).all id =
      ((l.filterMap env).map fun j => wNew.getD j false).all id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := hEq a (by simp)
    simp only [List.map_cons, List.any_cons, Bool.or_eq_false_iff] at hNoNone
    cases he : env a with
    | none =>
      rw [he] at hNoNone
      simp at hNoNone
    | some j =>
      rw [he] at ha
      dsimp only at ha
      have hl := ih hNoNone.2 (fun i hi => hEq i (by simp [hi]))
      simp only [List.map_cons, List.all_cons, List.filterMap, he, id_eq, ha]
      rw [hl]

private theorem elimLoop_correct (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (oldCur newCur : ℕ) (env : ℕ → Option ℕ) (wOld wNew : List Bool),
      wOld.length = oldCur →
      wNew.length = newCur →
      (∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < oldCur + j) →
      (∀ i < oldCur, ∀ k, env i = some k → k < newCur) →
      (∀ i < oldCur, wOld.getD i false =
        match env i with | none => false | some k => wNew.getD k false) →
      let res := elimLoop oldCur newCur env gs
      (∀ i < oldCur + gs.length, ∀ k, res.2 i = some k → k < newCur + res.1.length) ∧
      (∀ i < oldCur + gs.length, (wiresFrom gs wOld).getD i false =
        match res.2 i with | none => false | some k => (wiresFrom res.1 wNew).getD k false) := by
  induction gs with
  | nil =>
    intro oldCur newCur env wOld wNew _ _ _ hBnd hEq
    exact ⟨by simpa [elimLoop] using hBnd, by simpa [elimLoop, wiresFrom] using hEq⟩
  | cons g gs ih =>
    intro oldCur newCur env wOld wNew hlOld hlNew hWf hBnd hEq
    have hgt := hM g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hM g' (by simp [h])
    have hgWf : ∀ i ∈ g.inputs, i < oldCur := by
      have h0 := hWf 0 (by simp)
      simpa only [List.getElem_cons_zero, Nat.add_zero] using h0
    have hgsWf : ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < (oldCur + 1) + j := by
      intro j hj i hi
      have h1 := hWf (j + 1) (by simpa using hj) i (by simpa using hi)
      omega
    set v := g.op.eval (g.inputs.map fun i => wOld.getD i false)
    set wOld' := wOld ++ [v]
    have hlOld' : wOld'.length = oldCur + 1 := by simp [wOld', hlOld]
    have hop := hgt.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop
    · by_cases hany : (g.inputs.map env).any Option.isNone = true
      · have hv : v = false := by
          simp only [v, hop, GateOp.eval, List.all_map, Function.comp_apply, id]
          rw [Bool.eq_false_iff]
          intro hall
          rw [List.all_eq_true] at hall
          rw [List.any_eq_true] at hany
          obtain ⟨o, ho, his⟩ := hany
          obtain ⟨i, hi, hei⟩ := List.mem_map.1 ho
          have hnone : env i = none := by
            cases h' : env i with
            | none => rfl
            | some _ => rw [h'] at hei; rw [← hei] at his; simp at his
          have h1 : wOld.getD i false = true := by simpa using hall i hi
          have h2 := hEq i (hgWf i hi)
          rw [hnone] at h2
          dsimp only at h2
          rw [h2] at h1
          exact Bool.noConfusion h1
        set env' := fun i => if i = oldCur then none else env i
        have hBnd' : ∀ i < oldCur + 1, ∀ k, env' i = some k → k < newCur := by
          intro i hi k hk
          by_cases heq : i = oldCur
          · simp [env', heq] at hk
          · simp [env', heq] at hk
            exact hBnd i (by omega) k hk
        have hEq' : ∀ i < oldCur + 1, wOld'.getD i false =
            match env' i with | none => false | some k => wNew.getD k false := by
          intro i hi
          rw [show wOld' = wOld ++ [v] from rfl, getD_snoc, hlOld]
          by_cases heq : i = oldCur
          · simp [env', heq, hv]
          · simp only [if_neg heq, env']
            exact hEq i (by omega)
        have hstep := ih hgs (oldCur + 1) newCur env' wOld' wNew hlOld' hlNew hgsWf hBnd' hEq'
        have hres : elimLoop oldCur newCur env (g :: gs) =
            elimLoop (oldCur + 1) newCur env' gs := by
          simp [elimLoop, hop, hany, env']
        rw [hres]
        refine ⟨?_, ?_⟩
        · intro i hi k hk
          exact hstep.1 i (by simp only [List.length_cons] at hi; omega) k hk
        · intro i hi
          exact hstep.2 i (by simp only [List.length_cons] at hi; omega)
      · have hanyF : (g.inputs.map env).any Option.isNone = false :=
          Bool.eq_false_iff.2 hany
        set g' : Gate := ⟨GateOp.and, g.inputs.filterMap env⟩
        set v' := g'.op.eval (g'.inputs.map fun k => wNew.getD k false)
        have hvv' : v = v' := by
          simp only [v, v', g', hop, GateOp.eval]
          exact eval_and_filterMap env wOld wNew g.inputs hanyF (fun i hi => hEq i (hgWf i hi))
        set wNew' := wNew ++ [v']
        have hlNew' : wNew'.length = newCur + 1 := by simp [wNew', hlNew]
        set env' := fun i => if i = oldCur then some newCur else env i
        have hBnd' : ∀ i < oldCur + 1, ∀ k, env' i = some k → k < newCur + 1 := by
          intro i hi k hk
          by_cases heq : i = oldCur
          · simp [env', heq] at hk; omega
          · simp [env', heq] at hk
            have := hBnd i (by omega) k hk
            omega
        have hEq' : ∀ i < oldCur + 1, wOld'.getD i false =
            match env' i with | none => false | some k => wNew'.getD k false := by
          intro i hi
          rw [show wOld' = wOld ++ [v] from rfl, getD_snoc, hlOld]
          by_cases heq : i = oldCur
          · simp only [if_pos heq, env', wNew', getD_snoc, hlNew, ↓reduceIte, hvv']
          · simp only [if_neg heq, env']
            rw [hEq i (by omega)]
            cases hk : env i with
            | none => rfl
            | some k =>
              have hklt := hBnd i (by omega) k hk
              dsimp only
              rw [show wNew' = wNew ++ [v'] from rfl, getD_snoc, hlNew, if_neg (Nat.ne_of_lt hklt)]
        have hstep := ih hgs (oldCur + 1) (newCur + 1) env' wOld' wNew' hlOld' hlNew' hgsWf hBnd' hEq'
        have hres : elimLoop oldCur newCur env (g :: gs) =
            (g' :: (elimLoop (oldCur + 1) (newCur + 1) env' gs).1,
              (elimLoop (oldCur + 1) (newCur + 1) env' gs).2) := by
          simp [elimLoop, hop, hany, g', env']
        rw [hres]
        refine ⟨?_, ?_⟩
        · intro i hi k hk
          have hi' : i < oldCur + 1 + gs.length := by simp only [List.length_cons] at hi; omega
          have h1 := hstep.1 i hi' k hk
          simp only [List.length_cons]
          omega
        · intro i hi
          have hi' : i < oldCur + 1 + gs.length := by simp only [List.length_cons] at hi; omega
          exact hstep.2 i hi'
    · have hor := eval_or_filterMap env wOld wNew g.inputs (fun i hi => hEq i (hgWf i hi))
      cases hlive : g.inputs.filterMap env with
      | nil =>
        have hv : v = false := by
          simp only [v, hop, GateOp.eval, hor, hlive, List.map_nil, List.any_nil]
        set env' := fun i => if i = oldCur then none else env i
        have hBnd' : ∀ i < oldCur + 1, ∀ k, env' i = some k → k < newCur := by
          intro i hi k hk
          by_cases heq : i = oldCur
          · simp [env', heq] at hk
          · simp [env', heq] at hk
            exact hBnd i (by omega) k hk
        have hEq' : ∀ i < oldCur + 1, wOld'.getD i false =
            match env' i with | none => false | some k => wNew.getD k false := by
          intro i hi
          rw [show wOld' = wOld ++ [v] from rfl, getD_snoc, hlOld]
          by_cases heq : i = oldCur
          · simp [env', heq, hv]
          · simp only [if_neg heq, env']
            exact hEq i (by omega)
        have hstep := ih hgs (oldCur + 1) newCur env' wOld' wNew hlOld' hlNew hgsWf hBnd' hEq'
        have hres : elimLoop oldCur newCur env (g :: gs) =
            elimLoop (oldCur + 1) newCur env' gs := by
          simp [elimLoop, hop, hlive, env']
        rw [hres]
        refine ⟨?_, ?_⟩
        · intro i hi k hk
          exact hstep.1 i (by simp only [List.length_cons] at hi; omega) k hk
        · intro i hi
          exact hstep.2 i (by simp only [List.length_cons] at hi; omega)
      | cons a t =>
        cases t with
        | nil =>
          have haMem : a ∈ g.inputs.filterMap env := by simp [hlive]
          obtain ⟨i0, hi0, hei0⟩ := List.mem_filterMap.1 haMem
          have halt : a < newCur := hBnd i0 (hgWf i0 hi0) a hei0
          have hv : v = wNew.getD a false := by
            simp only [v, hop, GateOp.eval, hor, hlive, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id, Bool.or_false]
          set env' := fun i => if i = oldCur then some a else env i
          have hBnd' : ∀ i < oldCur + 1, ∀ k, env' i = some k → k < newCur := by
            intro i hi k hk
            by_cases heq : i = oldCur
            · simp [env', heq] at hk; subst hk; exact halt
            · simp [env', heq] at hk
              exact hBnd i (by omega) k hk
          have hEq' : ∀ i < oldCur + 1, wOld'.getD i false =
              match env' i with | none => false | some k => wNew.getD k false := by
            intro i hi
            rw [show wOld' = wOld ++ [v] from rfl, getD_snoc, hlOld]
            by_cases heq : i = oldCur
            · simp [env', heq, hv]
            · simp only [if_neg heq, env']
              exact hEq i (by omega)
          have hstep := ih hgs (oldCur + 1) newCur env' wOld' wNew hlOld' hlNew hgsWf hBnd' hEq'
          have hres : elimLoop oldCur newCur env (g :: gs) =
              elimLoop (oldCur + 1) newCur env' gs := by
            simp [elimLoop, hop, hlive, env']
          rw [hres]
          refine ⟨?_, ?_⟩
          · intro i hi k hk
            exact hstep.1 i (by simp only [List.length_cons] at hi; omega) k hk
          · intro i hi
            exact hstep.2 i (by simp only [List.length_cons] at hi; omega)
        | cons b t' =>
          set g' : Gate := ⟨GateOp.or, a :: b :: t'⟩
          set v' := g'.op.eval (g'.inputs.map fun k => wNew.getD k false)
          have hvv' : v = v' := by
            simp only [v, v', g', hop, GateOp.eval, hor, hlive]
          set wNew' := wNew ++ [v']
          have hlNew' : wNew'.length = newCur + 1 := by simp [wNew', hlNew]
          set env' := fun i => if i = oldCur then some newCur else env i
          have hBnd' : ∀ i < oldCur + 1, ∀ k, env' i = some k → k < newCur + 1 := by
            intro i hi k hk
            by_cases heq : i = oldCur
            · simp [env', heq] at hk; omega
            · simp [env', heq] at hk
              have := hBnd i (by omega) k hk
              omega
          have hEq' : ∀ i < oldCur + 1, wOld'.getD i false =
              match env' i with | none => false | some k => wNew'.getD k false := by
            intro i hi
            rw [show wOld' = wOld ++ [v] from rfl, getD_snoc, hlOld]
            by_cases heq : i = oldCur
            · simp only [if_pos heq, env', wNew', getD_snoc, hlNew, ↓reduceIte, hvv']
            · simp only [if_neg heq, env']
              rw [hEq i (by omega)]
              cases hk : env i with
              | none => rfl
              | some k =>
                have hklt := hBnd i (by omega) k hk
                dsimp only
                rw [show wNew' = wNew ++ [v'] from rfl, getD_snoc, hlNew, if_neg (Nat.ne_of_lt hklt)]
          have hstep := ih hgs (oldCur + 1) (newCur + 1) env' wOld' wNew' hlOld' hlNew' hgsWf hBnd' hEq'
          have hres : elimLoop oldCur newCur env (g :: gs) =
              (g' :: (elimLoop (oldCur + 1) (newCur + 1) env' gs).1,
                (elimLoop (oldCur + 1) (newCur + 1) env' gs).2) := by
            simp [elimLoop, hop, hlive, g', env']
          rw [hres]
          refine ⟨?_, ?_⟩
          · intro i hi k hk
            have hi' : i < oldCur + 1 + gs.length := by simp only [List.length_cons] at hi; omega
            have h1 := hstep.1 i hi' k hk
            simp only [List.length_cons]
            omega
          · intro i hi
            have hi' : i < oldCur + 1 + gs.length := by simp only [List.length_cons] at hi; omega
            exact hstep.2 i hi'

private def elimFalse (L r : ℕ) (C : Circuit) : Circuit :=
  let res := elimLoop L L (fun i => if i = r then none else some i) C.gates
  let out := match res.2 C.output with
    | none => L + res.1.length
    | some k => k
  ⟨res.1, out⟩

private theorem elimFalse_mono2 (L r : ℕ) (C : Circuit) (hM : Monotone2 C) :
    Monotone2 (elimFalse L r C) :=
  elimLoop_mono2 L L (fun i => if i = r then none else some i) C.gates hM

private theorem elimFalse_eval (L r : ℕ) (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (hxr : x.getD r false = false) :
    (elimFalse L r C).eval x = C.eval x := by
  have hBnd : ∀ i < L, ∀ k, (if i = r then none else some i) = some k → k < L := by
    intro i hi k hk
    by_cases heq : i = r
    · simp [heq] at hk
    · simp only [if_neg heq, Option.some.injEq] at hk
      subst hk
      exact hi
  have hEq : ∀ i < L, x.getD i false =
      match (if i = r then none else some i) with | none => false | some k => x.getD k false := by
    intro i _
    split_ifs with heq
    · subst heq; exact hxr
    · rfl
  have hcorr := elimLoop_correct C.gates hM L L (fun i => if i = r then none else some i)
    x x hx hx hW.1 hBnd hEq
  have hout := hcorr.2 C.output hW.2
  simp only [elimFalse, Circuit.eval, wires_eq]
  rw [hout]
  cases ho : (elimLoop L L (fun i => if i = r then none else some i) C.gates).2 C.output with
  | none =>
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom, hx])
  | some k => rfl

private theorem elimFalse_size_drop_two_same (L r : ℕ) (hr : r < L) (C : Circuit) (hM : Monotone2 C)
    (j₁ j₂ : ℕ) (hlt : j₁ < j₂) (hj₂ : j₂ < C.gates.length)
    (hm₁ : r ∈ (C.gates[j₁]).inputs) (hm₂ : r ∈ (C.gates[j₂]).inputs) :
    (elimFalse L r C).size + 2 ≤ C.size :=
  elimLoop_drop_two_same L L (fun i => if i = r then none else some i) C.gates hM r hr
    (by simp) j₁ j₂ hlt hj₂ hm₁ hm₂

private theorem elimFalse_size_drop_and_chain (L r : ℕ) (hr : r < L) (C : Circuit) (hM : Monotone2 C)
    (j₁ j₂ : ℕ) (hlt : j₁ < j₂) (hj₂ : j₂ < C.gates.length)
    (hop₁ : (C.gates[j₁]).op = GateOp.and)
    (hm₁ : r ∈ (C.gates[j₁]).inputs) (hm₂ : L + j₁ ∈ (C.gates[j₂]).inputs) :
    (elimFalse L r C).size + 2 ≤ C.size :=
  elimLoop_drop_and_chain L L (fun i => if i = r then none else some i) C.gates hM r hr
    (by simp) j₁ j₂ hlt hj₂ hop₁ hm₁ hm₂

private theorem sum_count_le_length (l : List ℕ) (S : Finset ℕ) (f : ℕ → ℕ)
    (hinj : Set.InjOn f S) :
    ∑ v ∈ S, l.count (f v) ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hsplit : ∀ v, (a :: l).count (f v) = (if f v = a then 1 else 0) + l.count (f v) := by
      intro v
      rw [List.count_cons]
      by_cases h : f v = a
      · simp [h]; omega
      · simp [h, Ne.symm h]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 : ∑ v ∈ S, (if f v = a then 1 else 0) ≤ 1 := by
      rw [Finset.sum_boole]
      have hcard : (S.filter fun v => f v = a).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        exact hinj hx.1 hy.1 (hx.2.trans hy.2.symm)
      simpa using hcard
    simp only [List.length_cons]
    omega

private theorem val_gate_or_true {L : ℕ} (C : Circuit) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (j : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.or) (i : ℕ) (hi : i ∈ (C.gates[j]).inputs)
    (hvi : val C x i = true) :
    val C x (L + j) = true := by
  rw [val_gate_wf C hW x hx j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, hvi⟩

private theorem val_gate_and_false {L : ℕ} (C : Circuit) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (j : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.and) (i : ℕ) (hi : i ∈ (C.gates[j]).inputs)
    (hvi : val C x i = false) :
    val C x (L + j) = false := by
  rw [val_gate_wf C hW x hx j hj, hop]
  simp only [GateOp.eval, List.all_map, Function.comp_apply, id]
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  have h1 : val C x i = true := by simpa using hall i hi
  rw [hvi] at h1
  exact Bool.noConfusion h1

private theorem exists_ne_in (R : Finset ℕ) (h : 2 ≤ R.card) (r : ℕ) :
    ∃ r' ∈ R, r' ≠ r := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < R.card)
  by_cases h1 : a = r
  · exact ⟨b, hb, fun h2 => hab (h1.trans h2.symm)⟩
  · exact ⟨a, ha, h1⟩

private theorem list_len_le_two_mem_two {α : Type*} (l : List α) (a b : α)
    (hab : a ≠ b) (hlen : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l) :
    l = [a, b] ∨ l = [b, a] := by
  cases l with
  | nil => simp at ha
  | cons x l =>
    cases l with
    | nil =>
      simp at ha hb
      exact False.elim (hab (ha.trans hb.symm))
    | cons y l =>
      cases l with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact False.elim (hab rfl)
      | cons z l =>
        simp at hlen

private theorem no_row_output {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ) (hRL : ∀ r ∈ R, r < L)
    (G : ℕ → Fin m → Bool) (hcard : 2 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (C : Circuit) (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (r : ℕ) (hr : r ∈ R) :
    C.output ≠ r := by
  intro heq
  obtain ⟨r', hr', hne⟩ := exists_ne_in R hcard r
  obtain ⟨c, _, hGr⟩ := hPair r' hr' r hr hne
  have hv := hEval r hr c
  rw [← val_eq_eval, heq, val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
    rowInput_getD base hlen r (hRL r hr) c r, if_pos rfl] at hv
  rw [hGr] at hv
  exact Bool.noConfusion hv

private theorem no_gate_output_reads_row {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ)
    (hRL : ∀ r ∈ R, r < L) (hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false)
    (G : ℕ → Fin m → Bool) (hcard : 2 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (r : ℕ) (hr : r ∈ R) (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output = L + j) :
    r ∉ (C.gates[j]).inputs := by
  intro hmem
  obtain ⟨r', hr', hne⟩ := exists_ne_in R hcard r
  have hop := (hM (C.gates[j]) (List.getElem_mem hj)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · obtain ⟨c, hGr', _⟩ := hPair r' hr' r hr hne
    have hvr : val C (rowInput base r' c) r = false := by
      rw [val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
        rowInput_getD base hlen r' (hRL r' hr') c r, if_neg (Ne.symm hne), hR0 r hr c]
    have hgf := val_gate_and_false C hW (rowInput base r' c) (by rw [length_rowInput, hlen])
      j hj hop r hmem hvr
    have hev := hEval r' hr' c
    rw [← val_eq_eval, hout, hgf, hGr'] at hev
    exact Bool.noConfusion hev
  · obtain ⟨c, _, hGr⟩ := hPair r' hr' r hr hne
    have hvr : val C (rowInput base r c) r = true := by
      rw [val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
        rowInput_getD base hlen r (hRL r hr) c r, if_pos rfl]
    have hgt := val_gate_or_true C hW (rowInput base r c) (by rw [length_rowInput, hlen])
      j hj hop r hmem hvr
    have hev := hEval r hr c
    rw [← val_eq_eval, hout, hgt, hGr] at hev
    exact Bool.noConfusion hev

private theorem row_must_be_read {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ)
    (hRL : ∀ r ∈ R, r < L) (hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false)
    (G : ℕ → Fin m → Bool) (hcard : 2 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (r : ℕ) (hr : r ∈ R) :
    ∃ j : ℕ, ∃ _ : j < C.gates.length, r ∈ (C.gates[j]).inputs := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨r', hr', hne⟩ := exists_ne_in R hcard r
  obtain ⟨c, hGr, hGr'⟩ := hPair r hr r' hr' (Ne.symm hne)
  have hle := val_le_of_exceptions L C hM hW (rowInput base r c) (rowInput base r' c)
    (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {r}
    (by
      intro i _ hi hx
      have hir : i ≠ r := by simpa using hi
      rw [rowInput_getD base hlen r (hRL r hr) c i, if_neg hir] at hx
      rw [rowInput_getD base hlen r' (hRL r' hr') c i]
      split_ifs
      · rfl
      · exact hx)
    (by
      intro j hj _
      right
      intro i hi hmem
      have hir : i = r := by simpa using hmem
      subst hir
      exact hnone j hj hi)
  have hout : C.output ∉ ({r} : Set ℕ) := by
    simpa using no_row_output base hlen R hRL G hcard hPair C hEval r hr
  have htrue : val C (rowInput base r c) C.output = true := by
    rw [val_eq_eval, hEval r hr c, hGr]
  have hres := hle C.output hout htrue
  rw [val_eq_eval, hEval r' hr' c, hGr'] at hres
  exact Bool.noConfusion hres

private theorem base_case_two {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ)
    (hRL : ∀ r ∈ R, r < L) (hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false)
    (G : ℕ → Fin m → Bool) (hcard : 2 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c) :
    3 ≤ C.size := by
  by_contra hlt
  have hsize : C.gates.length ≤ 2 := by
    change ¬ (3 ≤ C.gates.length) at hlt
    omega
  obtain ⟨r₀, hr₀, r₁, hr₁, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < R.card)
  have hno_out_r₀ := no_row_output base hlen R hRL G hcard hPair C hEval r₀ hr₀
  have hno_out_r₁ := no_row_output base hlen R hRL G hcard hPair C hEval r₁ hr₁
  obtain ⟨c, hG₀, hG₁⟩ := hPair r₀ hr₀ r₁ hr₁ hne
  by_cases houtL : C.output < L
  · have e0 := hEval r₀ hr₀ c
    have e1 := hEval r₁ hr₁ c
    rw [← val_eq_eval, val_input C _ _ (by rw [length_rowInput, hlen]; exact houtL),
      rowInput_getD base hlen r₀ (hRL r₀ hr₀) c C.output, if_neg hno_out_r₀] at e0
    rw [← val_eq_eval, val_input C _ _ (by rw [length_rowInput, hlen]; exact houtL),
      rowInput_getD base hlen r₁ (hRL r₁ hr₁) c C.output, if_neg hno_out_r₁] at e1
    rw [hG₀] at e0
    rw [hG₁] at e1
    rw [e0] at e1
    exact Bool.noConfusion e1
  · by_cases hout0 : C.output = L
    · have hj0 : 0 < C.gates.length := by have := hW.2; omega
      have h0r₀ := no_gate_output_reads_row base hlen R hRL hR0 G hcard hPair C hM hW hEval
        r₀ hr₀ 0 hj0 (by omega)
      have h0r₁ := no_gate_output_reads_row base hlen R hRL hR0 G hcard hPair C hM hW hEval
        r₁ hr₁ 0 hj0 (by omega)
      have heq0 : val C (rowInput base r₀ c) (L + 0) = val C (rowInput base r₁ c) (L + 0) := by
        rw [val_gate_wf C hW (rowInput base r₀ c) (by rw [length_rowInput, hlen]) 0 hj0,
          val_gate_wf C hW (rowInput base r₁ c) (by rw [length_rowInput, hlen]) 0 hj0]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hilt : i < L := by simpa using hW.1 0 hj0 i hi
        have hne0 : i ≠ r₀ := fun h => h0r₀ (h ▸ hi)
        have hne1 : i ≠ r₁ := fun h => h0r₁ (h ▸ hi)
        rw [val_input C _ _ (by rw [length_rowInput, hlen]; exact hilt),
          val_input C _ _ (by rw [length_rowInput, hlen]; exact hilt),
          rowInput_getD base hlen r₀ (hRL r₀ hr₀) c i, if_neg hne0,
          rowInput_getD base hlen r₁ (hRL r₁ hr₁) c i, if_neg hne1]
      have e0 := hEval r₀ hr₀ c
      have e1 := hEval r₁ hr₁ c
      rw [← val_eq_eval, hout0] at e0 e1
      have heq0' : val C (rowInput base r₀ c) L = val C (rowInput base r₁ c) L := by simpa using heq0
      rw [heq0', e1, hG₁] at e0
      rw [hG₀] at e0
      exact Bool.noConfusion e0
    · have hout1 : C.output = L + 1 := by have := hW.2; omega
      have hlen2 : C.gates.length = 2 := by have := hW.2; omega
      have hj0 : 0 < C.gates.length := by omega
      have hj1 : 1 < C.gates.length := by omega
      have h1r₀ := no_gate_output_reads_row base hlen R hRL hR0 G hcard hPair C hM hW hEval
        r₀ hr₀ 1 hj1 hout1
      have h1r₁ := no_gate_output_reads_row base hlen R hRL hR0 G hcard hPair C hM hW hEval
        r₁ hr₁ 1 hj1 hout1
      obtain ⟨j₀, hj₀, hm₀⟩ := row_must_be_read base hlen R hRL hR0 G hcard hPair C hM hW hEval r₀ hr₀
      obtain ⟨j₁, hj₁, hm₁⟩ := row_must_be_read base hlen R hRL hR0 G hcard hPair C hM hW hEval r₁ hr₁
      have hj₀_zero : j₀ = 0 := by
        by_contra hne0
        have hjeq1 : j₀ = 1 := by omega
        subst hjeq1
        exact h1r₀ hm₀
      have hj₁_zero : j₁ = 0 := by
        by_contra hne1
        have hjeq1 : j₁ = 1 := by omega
        subst hjeq1
        exact h1r₁ hm₁
      subst hj₀_zero
      subst hj₁_zero
      have hg₀_eq : val C (rowInput base r₀ c) (L + 0) = val C (rowInput base r₁ c) (L + 0) := by
        have hgt := hM (C.gates[0]) (List.getElem_mem hj0)
        have htwo := list_len_le_two_mem_two (C.gates[0]).inputs r₀ r₁ hne hgt.2 hm₀ hm₁
        rw [val_gate_wf C hW (rowInput base r₀ c) (by rw [length_rowInput, hlen]) 0 hj0,
          val_gate_wf C hW (rowInput base r₁ c) (by rw [length_rowInput, hlen]) 0 hj0]
        have vr00 : val C (rowInput base r₀ c) r₀ = true := by
          rw [val_input C _ _ (by rw [length_rowInput, hlen]; exact hRL r₀ hr₀),
            rowInput_getD base hlen r₀ (hRL r₀ hr₀) c r₀, if_pos rfl]
        have vr01 : val C (rowInput base r₀ c) r₁ = false := by
          rw [val_input C _ _ (by rw [length_rowInput, hlen]; exact hRL r₁ hr₁),
            rowInput_getD base hlen r₀ (hRL r₀ hr₀) c r₁, if_neg (Ne.symm hne), hR0 r₁ hr₁ c]
        have vr10 : val C (rowInput base r₁ c) r₀ = false := by
          rw [val_input C _ _ (by rw [length_rowInput, hlen]; exact hRL r₀ hr₀),
            rowInput_getD base hlen r₁ (hRL r₁ hr₁) c r₀, if_neg hne, hR0 r₀ hr₀ c]
        have vr11 : val C (rowInput base r₁ c) r₁ = true := by
          rw [val_input C _ _ (by rw [length_rowInput, hlen]; exact hRL r₁ hr₁),
            rowInput_getD base hlen r₁ (hRL r₁ hr₁) c r₁, if_pos rfl]
        have hop := hgt.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases htwo with htwo | htwo <;> rw [htwo] <;>
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, vr00, vr01, vr10, vr11]
      have hle := val_le_of_exceptions L C hM hW (rowInput base r₀ c) (rowInput base r₁ c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {r₀, r₁}
        (by
          intro i _ hi hx
          have hne0 : i ≠ r₀ := fun h => hi (Or.inl h)
          have hne1 : i ≠ r₁ := fun h => hi (Or.inr h)
          rw [rowInput_getD base hlen r₀ (hRL r₀ hr₀) c i, if_neg hne0] at hx
          rw [rowInput_getD base hlen r₁ (hRL r₁ hr₁) c i, if_neg hne1]
          exact hx)
        (by
          intro j hj _
          cases j with
          | zero =>
            left
            intro hv
            rw [← hg₀_eq]
            exact hv
          | succ j =>
            have hjeq0 : j = 0 := by omega
            subst hjeq0
            right
            intro i hi hmem
            rcases hmem with h | h
            · rw [h] at hi; exact h1r₀ hi
            · simp only [Set.mem_singleton_iff] at h
              rw [h] at hi; exact h1r₁ hi)
      have houtE : C.output ∉ ({r₀, r₁} : Set ℕ) := by
        intro h
        rcases h with h | h
        · exact hno_out_r₀ h
        · exact hno_out_r₁ h
      have htrue : val C (rowInput base r₀ c) C.output = true := by
        rw [val_eq_eval, hEval r₀ hr₀ c, hG₀]
      have hres := hle C.output houtE htrue
      rw [val_eq_eval, hEval r₁ hr₁ c, hG₁] at hres
      exact Bool.noConfusion hres

private theorem case_private_row_ors {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ)
    (hRL : ∀ r ∈ R, r < L) (hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false)
    (G : ℕ → Fin m → Bool) (hcard3 : 3 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (hTriple : ∀ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false)
    (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (g : ℕ → ℕ)
    (hg_lt : ∀ r ∈ R, g r < C.gates.length)
    (hg_read : ∀ r (hr : r ∈ R), r ∈ (C.gates[g r]'(hg_lt r hr)).inputs)
    (hg_sole : ∀ r ∈ R, ∀ j (hj : j < C.gates.length), r ∈ (C.gates[j]).inputs → j = g r)
    (hg_or : ∀ r (hr : r ∈ R), (C.gates[g r]'(hg_lt r hr)).op = GateOp.or) :
    2 * R.card ≤ C.size := by
  have hcard2 : 2 ≤ R.card := by omega
  have hval_gu : ∀ r (hr : r ∈ R) (c : Fin m), val C (rowInput base r c) (L + g r) = true := by
    intro r hr c
    have hvr : val C (rowInput base r c) r = true := by
      rw [val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
        rowInput_getD base hlen r (hRL r hr) c r, if_pos rfl]
    exact val_gate_or_true C hW (rowInput base r c) (by rw [length_rowInput, hlen])
      (g r) (hg_lt r hr) (hg_or r hr) r (hg_read r hr) hvr
  have hg_not_out : ∀ r ∈ R, C.output ≠ L + g r := by
    intro r hr hout
    exact no_gate_output_reads_row base hlen R hRL hR0 G hcard2 hPair C hM hW hEval
      r hr (g r) (hg_lt r hr) hout (hg_read r hr)
  have hg_inj : Set.InjOn g R := by
    intro u hu v hv heq
    by_contra hne
    obtain ⟨c, hGu, hGv⟩ := hPair u hu v hv hne
    have hle := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base v c)
      (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, v}
      (by
        intro i _ hi hx
        have hiu : i ≠ u := fun h => hi (Or.inl h)
        have hiv : i ≠ v := fun h => hi (Or.inr h)
        rw [rowInput_getD base hlen u (hRL u hu) c i, if_neg hiu] at hx
        rw [rowInput_getD base hlen v (hRL v hv) c i, if_neg hiv]
        exact hx)
      (by
        intro j hj _
        by_cases hjg : j = g u
        · left
          intro _
          rw [hjg, heq]
          exact hval_gu v hv c
        · right
          intro i hi hmem
          rcases hmem with h | h
          · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
          · simp only [Set.mem_singleton_iff] at h
            rw [h] at hi; exact hjg ((hg_sole v hv j hj hi).trans heq.symm))
    have houtE : C.output ∉ ({u, v} : Set ℕ) := by
      intro h
      rcases h with h | h
      · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
      · exact no_row_output base hlen R hRL G hcard2 hPair C hEval v hv h
    have hres := hle C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
    rw [val_eq_eval, hEval v hv c, hGv] at hres
    exact Bool.noConfusion hres
  have hg_no_feed_U : ∀ u (hu : u ∈ R) v (hv : v ∈ R),
      L + g u ∉ (C.gates[g v]'(hg_lt v hv)).inputs := by
    intro u hu v hv hmem
    by_cases huv : u = v
    · subst huv
      have h1 := hW.1 (g u) (hg_lt u hu) (L + g u) hmem
      omega
    · obtain ⟨c, hGv, hGu⟩ := hPair v hv u hu (Ne.symm huv)
      have hle := val_le_of_exceptions L C hM hW (rowInput base v c) (rowInput base u c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {v}
        (by
          intro i _ hi hx
          have hiv : i ≠ v := by simpa using hi
          rw [rowInput_getD base hlen v (hRL v hv) c i, if_neg hiv] at hx
          rw [rowInput_getD base hlen u (hRL u hu) c i]
          split_ifs
          · rfl
          · exact hx)
        (by
          intro j hj _
          by_cases hjv : j = g v
          · left
            intro _
            rw [hjv]
            exact val_gate_or_true C hW (rowInput base u c) (by rw [length_rowInput, hlen])
              (g v) (hg_lt v hv) (hg_or v hv) (L + g u) hmem (hval_gu u hu c)
          · right
            intro i hi hmv
            have hiv : i = v := by simpa using hmv
            rw [hiv] at hi
            exact hjv (hg_sole v hv j hj hi))
      have houtE : C.output ∉ ({v} : Set ℕ) := by
        simpa using no_row_output base hlen R hRL G hcard2 hPair C hEval v hv
      have hres := hle C.output houtE (by rw [val_eq_eval, hEval v hv c, hGv])
      rw [val_eq_eval, hEval u hu c, hGu] at hres
      exact Bool.noConfusion hres
  have hg_has_reader : ∀ u ∈ R, ∃ j : ℕ, ∃ _ : j < C.gates.length, L + g u ∈ (C.gates[j]).inputs := by
    intro u hu
    by_contra hnone
    push_neg at hnone
    obtain ⟨v, hv, hne⟩ := exists_ne_in R hcard2 u
    obtain ⟨c, hGu, hGv⟩ := hPair u hu v hv (Ne.symm hne)
    have hle := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base v c)
      (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, L + g u}
      (by
        intro i hiL hiE hx
        have hiu : i ≠ u := fun h => hiE (Or.inl h)
        rw [rowInput_getD base hlen u (hRL u hu) c i, if_neg hiu] at hx
        rw [rowInput_getD base hlen v (hRL v hv) c i]
        split_ifs
        · rfl
        · exact hx)
      (by
        intro j hj hjE
        have hjg : j ≠ g u := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
        right
        intro i hi hmem
        rcases hmem with h | h
        · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
        · simp only [Set.mem_singleton_iff] at h
          rw [h] at hi
          exact hnone j hj hi)
    have houtE : C.output ∉ ({u, L + g u} : Set ℕ) := by
      intro h
      rcases h with h | h
      · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
      · exact hg_not_out u hu h
    have hres := hle C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
    rw [val_eq_eval, hEval v hv c, hGv] at hres
    exact Bool.noConfusion hres
  have hmiracle : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∀ q (hq : q < C.gates.length),
      (∀ j (hj : j < C.gates.length), L + g u ∈ (C.gates[j]).inputs → j = q) →
      L + g v ∉ (C.gates[q]).inputs := by
    intro u hu v hv huv q hq hq_sole hgv_in
    have hq_op := (hM (C.gates[q]) (List.getElem_mem hq)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq_op
    rcases hq_op with hq_and | hq_or
    · have hcard_er : 0 < ((R.erase u).erase v).card := by
        have h1 : (R.erase u).card = R.card - 1 := Finset.card_erase_of_mem hu
        have hv1 : v ∈ R.erase u := Finset.mem_erase.2 ⟨Ne.symm huv, hv⟩
        have h2 : ((R.erase u).erase v).card = (R.erase u).card - 1 := Finset.card_erase_of_mem hv1
        omega
      obtain ⟨w, hw_er⟩ := Finset.card_pos.1 hcard_er
      have hwv : w ≠ v := (Finset.mem_erase.1 hw_er).1
      have hw_er1 := (Finset.mem_erase.1 hw_er).2
      have hwu : w ≠ u := (Finset.mem_erase.1 hw_er1).1
      have hw : w ∈ R := (Finset.mem_erase.1 hw_er1).2
      obtain ⟨c, hGu, hGv, hGw⟩ := hTriple u hu v hv w hw huv (Ne.symm hwu) (Ne.symm hwv)
      have hwgv : val C (rowInput base w c) (L + g v) = true := by
        by_contra hfalse
        have hwgvF : val C (rowInput base w c) (L + g v) = false := Bool.eq_false_iff.2 hfalse
        have hle1 := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base w c)
          (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen])
          ({u, L + g u} ∪ {k : ℕ | L + q ≤ k})
          (by
            intro i hiL hiE hx
            have hiu : i ≠ u := fun h => hiE (Or.inl (Or.inl h))
            rw [rowInput_getD base hlen u (hRL u hu) c i, if_neg hiu] at hx
            rw [rowInput_getD base hlen w (hRL w hw) c i]
            split_ifs
            · rfl
            · exact hx)
          (by
            intro j hj hjE
            have hjg : j ≠ g u := fun h => hjE (Or.inl (Set.mem_insert_of_mem _ (by simp [h])))
            have hjq : j < q := by
              have hnotge : ¬ (L + q ≤ L + j) := fun h => hjE (Or.inr h)
              omega
            right
            intro i hi hmem
            rcases hmem with (h | h) | hge
            · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
            · simp only [Set.mem_singleton_iff] at h
              rw [h] at hi
              exact (Nat.ne_of_lt hjq) (hq_sole j hj hi)
            · have hilt := hW.1 j hj i hi
              change L + q ≤ i at hge
              omega)
        have hgv_lt_q : L + g v < L + q := hW.1 q hq (L + g v) hgv_in
        have hgv_notE : L + g v ∉ ({u, L + g u} ∪ {k : ℕ | L + q ≤ k} : Set ℕ) := by
          intro h
          rcases h with (h | h) | h
          · have := hRL u hu; omega
          · simp only [Set.mem_singleton_iff] at h
            exact huv (hg_inj hu hv (by omega))
          · exact Nat.not_le_of_lt hgv_lt_q h
        have hugvF : val C (rowInput base u c) (L + g v) = false := by
          by_contra hnt
          have ht : val C (rowInput base u c) (L + g v) = true := Bool.eq_true_of_not_eq_false hnt
          have := hle1 (L + g v) hgv_notE ht
          rw [hwgvF] at this
          exact Bool.noConfusion this
        have huqF : val C (rowInput base u c) (L + q) = false :=
          val_gate_and_false C hW (rowInput base u c) (by rw [length_rowInput, hlen])
            q hq hq_and (L + g v) hgv_in hugvF
        have hle2 := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base w c)
          (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, L + g u}
          (by
            intro i _ hiE hx
            have hiu : i ≠ u := fun h => hiE (Or.inl h)
            rw [rowInput_getD base hlen u (hRL u hu) c i, if_neg hiu] at hx
            rw [rowInput_getD base hlen w (hRL w hw) c i]
            split_ifs
            · rfl
            · exact hx)
          (by
            intro j hj hjE
            have hjg : j ≠ g u := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
            by_cases hjq : j = q
            · left
              intro hqT
              rw [hjq, huqF] at hqT
              exact Bool.noConfusion hqT
            · right
              intro i hi hmem
              rcases hmem with h | h
              · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
              · simp only [Set.mem_singleton_iff] at h
                rw [h] at hi
                exact hjq (hq_sole j hj hi))
        have houtE : C.output ∉ ({u, L + g u} : Set ℕ) := by
          intro h
          rcases h with h | h
          · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
          · exact hg_not_out u hu h
        have hres := hle2 C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
        rw [val_eq_eval, hEval w hw c, hGw] at hres
        exact Bool.noConfusion hres
      have hle3 := val_le_of_exceptions L C hM hW (rowInput base v c) (rowInput base w c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {v}
        (by
          intro i _ hiE hx
          have hiv : i ≠ v := by simpa using hiE
          rw [rowInput_getD base hlen v (hRL v hv) c i, if_neg hiv] at hx
          rw [rowInput_getD base hlen w (hRL w hw) c i]
          split_ifs
          · rfl
          · exact hx)
        (by
          intro j hj _
          by_cases hjv : j = g v
          · left
            intro _
            rw [hjv]
            exact hwgv
          · right
            intro i hi hmem
            have hiv : i = v := by simpa using hmem
            rw [hiv] at hi
            exact hjv (hg_sole v hv j hj hi))
      have houtE : C.output ∉ ({v} : Set ℕ) := by
        simpa using no_row_output base hlen R hRL G hcard2 hPair C hEval v hv
      have hres := hle3 C.output houtE (by rw [val_eq_eval, hEval v hv c, hGv])
      rw [val_eq_eval, hEval w hw c, hGw] at hres
      exact Bool.noConfusion hres
    · obtain ⟨c, hGu, hGv⟩ := hPair u hu v hv huv
      have hle := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base v c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, L + g u}
        (by
          intro i _ hiE hx
          have hiu : i ≠ u := fun h => hiE (Or.inl h)
          rw [rowInput_getD base hlen u (hRL u hu) c i, if_neg hiu] at hx
          rw [rowInput_getD base hlen v (hRL v hv) c i]
          split_ifs
          · rfl
          · exact hx)
        (by
          intro j hj hjE
          have hjg : j ≠ g u := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
          by_cases hjq : j = q
          · left
            intro _
            rw [hjq]
            exact val_gate_or_true C hW (rowInput base v c) (by rw [length_rowInput, hlen])
              q hq hq_or (L + g v) hgv_in (hval_gu v hv c)
          · right
            intro i hi hmem
            rcases hmem with h | h
            · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
            · simp only [Set.mem_singleton_iff] at h
              rw [h] at hi
              exact hjq (hq_sole j hj hi))
      have houtE : C.output ∉ ({u, L + g u} : Set ℕ) := by
        intro h
        rcases h with h | h
        · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
        · exact hg_not_out u hu h
      have hres := hle C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
      rw [val_eq_eval, hEval v hv c, hGv] at hres
      exact Bool.noConfusion hres
  set U : Finset ℕ := R.image g
  have hU_sub : U ⊆ Finset.range C.gates.length := by
    intro j hj
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (hg_lt r hr)
  have hU_card : U.card = R.card := Finset.card_image_of_injOn hg_inj
  set Q : Finset ℕ := Finset.range C.gates.length \ U
  have hQ_card : Q.card + U.card = C.gates.length := by
    have := Finset.card_sdiff_add_card_eq_card hU_sub
    simpa [Q] using this
  let inputsOf : ℕ → List ℕ := fun j => (C.gates.getD j ⟨GateOp.or, []⟩).inputs
  have hinputsOf : ∀ j (hj : j < C.gates.length), inputsOf j = (C.gates[j]).inputs := by
    intro j hj
    simp [inputsOf, List.getD_eq_getElem?_getD, hj]
  let slotCount : ℕ → ℕ := fun r => ∑ j ∈ Q, (inputsOf j).count (L + g r)
  have hslot_pos : ∀ r ∈ R, 1 ≤ slotCount r := by
    intro r hr
    obtain ⟨j, hj, hmem⟩ := hg_has_reader r hr
    have hjQ : j ∈ Q := by
      rw [Finset.mem_sdiff, Finset.mem_range]
      refine ⟨hj, ?_⟩
      intro hjU
      obtain ⟨v, hv, hgv⟩ := Finset.mem_image.1 hjU
      subst hgv
      exact hg_no_feed_U r hr v hv hmem
    have hcnt : 1 ≤ (inputsOf j).count (L + g r) := by
      rw [hinputsOf j hj]
      exact List.count_pos_iff.2 hmem
    exact le_trans hcnt
      (Finset.single_le_sum (f := fun k => (inputsOf k).count (L + g r)) (fun _ _ => Nat.zero_le _) hjQ)
  set B : Finset ℕ := R.filter fun r => slotCount r = 1
  set A : Finset ℕ := R.filter fun r => 2 ≤ slotCount r
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro r hA hB
    simp only [A, B, Finset.mem_filter] at hA hB
    omega
  have hAB_union : A ∪ B = R := by
    ext r
    simp only [Finset.mem_union, A, B, Finset.mem_filter]
    constructor
    · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
    · intro hr
      have hpos := hslot_pos r hr
      by_cases h1 : slotCount r = 1
      · exact Or.inr ⟨hr, h1⟩
      · exact Or.inl ⟨hr, by omega⟩
  have hAB_card : A.card + B.card = R.card := by
    rw [← Finset.card_union_of_disjoint hAB_disj, hAB_union]
  have hB_exists : ∀ r ∈ B, ∃ q ∈ Q, (inputsOf q).count (L + g r) = 1 ∧
      ∀ j ∈ Q, j ≠ q → (inputsOf j).count (L + g r) = 0 := by
    intro r hr
    have hsc : ∑ j ∈ Q, (inputsOf j).count (L + g r) = 1 := (Finset.mem_filter.1 hr).2
    have hpos : 0 < ∑ j ∈ Q, (inputsOf j).count (L + g r) := by omega
    obtain ⟨q, hqQ, hqpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
    have hq_le : (inputsOf q).count (L + g r) ≤ 1 := by
      have := Finset.single_le_sum (f := fun k => (inputsOf k).count (L + g r))
        (fun _ _ => Nat.zero_le _) hqQ
      exact le_trans this (le_of_eq hsc)
    have hq1 : (inputsOf q).count (L + g r) = 1 := by omega
    refine ⟨q, hqQ, hq1, ?_⟩
    intro j hjQ hjne
    have hsum2 := Finset.add_sum_erase Q (fun k => (inputsOf k).count (L + g r)) hqQ
    have hrest0 : ∑ k ∈ Q.erase q, (inputsOf k).count (L + g r) = 0 := by omega
    have hj_er : j ∈ Q.erase q := Finset.mem_erase.2 ⟨hjne, hjQ⟩
    have := Finset.single_le_sum (f := fun k => (inputsOf k).count (L + g r))
      (fun _ _ => Nat.zero_le _) hj_er
    omega
  classical
  let qOf : ℕ → ℕ := fun r => if hr : r ∈ B then Classical.choose (hB_exists r hr) else 0
  have hqOf_mem : ∀ r ∈ B, qOf r ∈ Q := by
    intro r hr
    simp only [qOf, dif_pos hr]
    exact (Classical.choose_spec (hB_exists r hr)).1
  have hqOf_lt : ∀ r ∈ B, qOf r < C.gates.length := by
    intro r hr
    exact Finset.mem_range.1 (Finset.mem_sdiff.1 (hqOf_mem r hr)).1
  have hqOf_in : ∀ r (hr : r ∈ B), L + g r ∈ (C.gates[qOf r]'(hqOf_lt r hr)).inputs := by
    intro r hr
    have h1 : (inputsOf (qOf r)).count (L + g r) = 1 := by
      simp only [qOf, dif_pos hr]
      exact (Classical.choose_spec (hB_exists r hr)).2.1
    rw [hinputsOf (qOf r) (hqOf_lt r hr)] at h1
    exact List.count_pos_iff.1 (by omega)
  have hqOf_sole : ∀ r ∈ B, ∀ j (hj : j < C.gates.length),
      L + g r ∈ (C.gates[j]).inputs → j = qOf r := by
    intro r hr j hj hmem
    have hrR : r ∈ R := (Finset.mem_filter.1 hr).1
    have hjQ : j ∈ Q := by
      rw [Finset.mem_sdiff, Finset.mem_range]
      refine ⟨hj, ?_⟩
      intro hjU
      obtain ⟨v, hv, hgv⟩ := Finset.mem_image.1 hjU
      subst hgv
      exact hg_no_feed_U r hrR v hv hmem
    by_contra hjne
    have h0 : (inputsOf j).count (L + g r) = 0 := by
      have hspec := Classical.choose_spec (hB_exists r hr)
      have hqeq : qOf r = Classical.choose (hB_exists r hr) := by simp [qOf, dif_pos hr]
      rw [hqeq] at hjne
      exact hspec.2.2 j hjQ hjne
    rw [hinputsOf j hj] at h0
    have hpos := List.count_pos_iff.2 hmem
    omega
  have hqOf_no_other : ∀ r (hr : r ∈ B) v (hv : v ∈ R), r ≠ v →
      L + g v ∉ (C.gates[qOf r]'(hqOf_lt r hr)).inputs := by
    intro r hr v hv hrv
    exact hmiracle r (Finset.mem_filter.1 hr).1 v hv hrv (qOf r) (hqOf_lt r hr) (hqOf_sole r hr)
  have hqOf_inj : Set.InjOn qOf B := by
    intro u hu v hv heq
    by_contra hne
    have hv_in := hqOf_in v hv
    have hvR : v ∈ R := (Finset.mem_filter.1 hv).1
    have hno := hqOf_no_other u hu v hvR hne
    have hv_in' : L + g v ∈ (C.gates[qOf u]'(hqOf_lt u hu)).inputs := by
      simpa [heq] using hv_in
    exact hno hv_in'
  set QB : Finset ℕ := B.image qOf
  have hQB_sub : QB ⊆ Q := by
    intro j hj
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hj
    exact hqOf_mem r hr
  have hQB_card : QB.card = B.card := Finset.card_image_of_injOn hqOf_inj
  set QA : Finset ℕ := Q \ QB
  have hQA_card : QA.card + B.card = Q.card := by
    have := Finset.card_sdiff_add_card_eq_card hQB_sub
    rw [hQB_card] at this
    exact this
  have hA_in_QA : ∀ v ∈ A, 2 ≤ ∑ j ∈ QA, (inputsOf j).count (L + g v) := by
    intro v hvA
    have hvR : v ∈ R := (Finset.mem_filter.1 hvA).1
    have hsc : 2 ≤ slotCount v := (Finset.mem_filter.1 hvA).2
    have hzero : ∀ j ∈ QB, (inputsOf j).count (L + g v) = 0 := by
      intro j hjQB
      obtain ⟨r, hrB, rfl⟩ := Finset.mem_image.1 hjQB
      have hrv : r ≠ v := by
        intro heq
        subst heq
        exact Finset.disjoint_left.1 hAB_disj hvA hrB
      rw [hinputsOf (qOf r) (hqOf_lt r hrB)]
      exact List.count_eq_zero.2 (hqOf_no_other r hrB v hvR hrv)
    have hsplit : ∑ j ∈ QA, (inputsOf j).count (L + g v) +
        ∑ j ∈ QB, (inputsOf j).count (L + g v) = slotCount v := by
      simpa [QA, slotCount] using Finset.sum_sdiff hQB_sub (f := fun j => (inputsOf j).count (L + g v))
    have hsum0 : ∑ j ∈ QB, (inputsOf j).count (L + g v) = 0 :=
      Finset.sum_eq_zero hzero
    omega
  have hlow : 2 * A.card ≤ ∑ v ∈ A, ∑ j ∈ QA, (inputsOf j).count (L + g v) := by
    have h1 := Finset.sum_le_sum hA_in_QA
    simpa [mul_comm] using h1
  have hup : ∑ j ∈ QA, ∑ v ∈ A, (inputsOf j).count (L + g v) ≤ 2 * QA.card := by
    have h1 : ∀ j ∈ QA, ∑ v ∈ A, (inputsOf j).count (L + g v) ≤ 2 := by
      intro j hjQA
      have hjlt : j < C.gates.length :=
        Finset.mem_range.1 (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hjQA).1).1
      have hinjA : Set.InjOn (fun v => L + g v) A := by
        intro x hx y hy hxy
        dsimp only at hxy
        exact hg_inj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 (by omega)
      have hle := sum_count_le_length (inputsOf j) A (fun v => L + g v) hinjA
      have hlen2 : (inputsOf j).length ≤ 2 := by
        rw [hinputsOf j hjlt]
        exact (hM (C.gates[j]) (List.getElem_mem hjlt)).2
      exact le_trans hle hlen2
    have h2 := Finset.sum_le_sum h1
    simpa [mul_comm] using h2
  rw [Finset.sum_comm] at hlow
  have hleA : A.card ≤ QA.card := by omega
  change 2 * R.card ≤ C.gates.length
  omega

private theorem main_ind {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) :
    ∀ k : ℕ, 2 ≤ k → ∀ (R : Finset ℕ), R.card = k →
      (∀ r ∈ R, r < L) →
      (∀ r ∈ R, ∀ c, (base c).getD r false = false) →
      ∀ (G : ℕ → Fin m → Bool),
      (∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false) →
      (∀ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, u ≠ v → u ≠ w → v ≠ w →
        ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
      ∀ (C : Circuit), Monotone2 C →
      (∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c) →
      2 * k - 1 ≤ C.size := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk R hcard hRL hR0 G hPair hTriple C hM hEval
    have hout : C.output < L + C.gates.length := by
      by_contra hge
      obtain ⟨r₀, hr₀, r₁, hr₁, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < R.card)
      obtain ⟨c, hG₀, _⟩ := hPair r₀ hr₀ r₁ hr₁ hne
      have h0 := val_out_of_bounds C (rowInput base r₀ c) C.output
        (by rw [length_rowInput, hlen]; omega)
      rw [val_eq_eval, hEval r₀ hr₀ c, hG₀] at h0
      exact Bool.noConfusion h0
    obtain ⟨C', hM', hW', hsz', hEv'⟩ := normalize_circuit L C hM hout
    rw [← hsz']
    have hEval' : ∀ u ∈ R, ∀ c : Fin m, C'.eval (rowInput base u c) = G u c := by
      intro u hu c
      rw [hEv' (rowInput base u c) (by rw [length_rowInput, hlen]), hEval u hu c]
    by_cases hk2 : k + 1 = 2
    · have h3 := base_case_two base hlen R hRL hR0 G (by omega) hPair C' hM' hW' hEval'
      omega
    · have hk3 : 3 ≤ k + 1 := by omega
      have hih : 2 ≤ k := by omega
      by_cases htwo : ∃ r ∈ R, ∃ j₁ j₂ : ℕ, ∃ hlt : j₁ < j₂, ∃ hj₂ : j₂ < C'.gates.length,
          r ∈ (C'.gates[j₁]'(Nat.lt_trans hlt hj₂)).inputs ∧ r ∈ (C'.gates[j₂]'hj₂).inputs
      · obtain ⟨r, hr, j₁, j₂, hlt, hj₂, hm₁, hm₂⟩ := htwo
        set C'' := elimFalse L r C'
        have hM'' := elimFalse_mono2 L r C' hM'
        have hdrop : C''.size + 2 ≤ C'.size :=
          elimFalse_size_drop_two_same L r (hRL r hr) C' hM' j₁ j₂ hlt hj₂ hm₁ hm₂
        set R' := R.erase r
        have hR'card : R'.card = k := by
          have h1 : R'.card = R.card - 1 := Finset.card_erase_of_mem hr
          omega
        have hEval'' : ∀ u ∈ R', ∀ c : Fin m, C''.eval (rowInput base u c) = G u c := by
          intro u hu c
          have hne : u ≠ r := (Finset.mem_erase.1 hu).1
          have huR : u ∈ R := (Finset.mem_erase.1 hu).2
          have hxr : (rowInput base u c).getD r false = false := by
            rw [rowInput_getD base hlen u (hRL u huR) c r, if_neg (Ne.symm hne), hR0 r hr c]
          rw [elimFalse_eval L r C' hM' hW' (rowInput base u c)
            (by rw [length_rowInput, hlen]) hxr, hEval' u huR c]
        have hsub := ih hih R' hR'card
          (fun u hu => hRL u (Finset.mem_erase.1 hu).2)
          (fun u hu => hR0 u (Finset.mem_erase.1 hu).2)
          G
          (fun u hu v hv => hPair u (Finset.mem_erase.1 hu).2 v (Finset.mem_erase.1 hv).2)
          (fun u hu v hv w hw =>
            hTriple u (Finset.mem_erase.1 hu).2 v (Finset.mem_erase.1 hv).2 w (Finset.mem_erase.1 hw).2)
          C'' hM'' hEval''
        omega
      · push_neg at htwo
        have huniq : ∀ r ∈ R, ∃ j : ℕ, ∃ _ : j < C'.gates.length,
            r ∈ (C'.gates[j]).inputs ∧
            ∀ j' (hj' : j' < C'.gates.length), r ∈ (C'.gates[j']).inputs → j' = j := by
          intro r hr
          obtain ⟨j, hj, hm⟩ := row_must_be_read base hlen R hRL hR0 G (by omega) hPair C' hM' hW' hEval' r hr
          refine ⟨j, hj, hm, ?_⟩
          intro j' hj' hm'
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · exact htwo r hr j' j hlt hj hm' hm
          · exact htwo r hr j j' hlt hj' hm hm'
        classical
        let g : ℕ → ℕ := fun r => if hr : r ∈ R then Classical.choose (huniq r hr) else 0
        have hg_lt : ∀ r ∈ R, g r < C'.gates.length := by
          intro r hr
          simp only [g, dif_pos hr]
          exact (Classical.choose_spec (huniq r hr)).1
        have hg_read : ∀ r (hr : r ∈ R), r ∈ (C'.gates[g r]'(hg_lt r hr)).inputs := by
          intro r hr
          simp only [g, dif_pos hr]
          exact (Classical.choose_spec (huniq r hr)).2.1
        have hg_sole : ∀ r ∈ R, ∀ j (hj : j < C'.gates.length),
            r ∈ (C'.gates[j]).inputs → j = g r := by
          intro r hr j hj hm
          simp only [g, dif_pos hr]
          exact (Classical.choose_spec (huniq r hr)).2.2 j hj hm
        by_cases hand : ∃ r, ∃ hr : r ∈ R, (C'.gates[g r]'(hg_lt r hr)).op = GateOp.and
        · obtain ⟨r, hr, hop⟩ := hand
          have hread : ∃ j₂ : ℕ, ∃ _ : j₂ < C'.gates.length, L + g r ∈ (C'.gates[j₂]).inputs := by
            by_contra hnone
            push_neg at hnone
            obtain ⟨r', hr', hne⟩ := exists_ne_in R (by omega) r
            obtain ⟨c, hGr, hGr'⟩ := hPair r hr r' hr' (Ne.symm hne)
            have hle := val_le_of_exceptions L C' hM' hW' (rowInput base r c) (rowInput base r' c)
              (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {r, L + g r}
              (by
                intro i _ hiE hx
                have hir : i ≠ r := fun h => hiE (Or.inl h)
                rw [rowInput_getD base hlen r (hRL r hr) c i, if_neg hir] at hx
                rw [rowInput_getD base hlen r' (hRL r' hr') c i]
                split_ifs
                · rfl
                · exact hx)
              (by
                intro j hj hjE
                have hjg : j ≠ g r := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
                right
                intro i hi hmem
                rcases hmem with h | h
                · rw [h] at hi; exact hjg (hg_sole r hr j hj hi)
                · simp only [Set.mem_singleton_iff] at h
                  rw [h] at hi
                  exact hnone j hj hi)
            have houtE : C'.output ∉ ({r, L + g r} : Set ℕ) := by
              intro h
              rcases h with h | h
              · exact no_row_output base hlen R hRL G (by omega) hPair C' hEval' r hr h
              · exact no_gate_output_reads_row base hlen R hRL hR0 G (by omega) hPair C' hM' hW' hEval'
                  r hr (g r) (hg_lt r hr) h (hg_read r hr)
            have hres := hle C'.output houtE (by rw [val_eq_eval, hEval' r hr c, hGr])
            rw [val_eq_eval, hEval' r' hr' c, hGr'] at hres
            exact Bool.noConfusion hres
          obtain ⟨j₂, hj₂, hm₂⟩ := hread
          have hlt : g r < j₂ := by
            have := hW'.1 j₂ hj₂ (L + g r) hm₂
            omega
          set C'' := elimFalse L r C'
          have hM'' := elimFalse_mono2 L r C' hM'
          have hdrop : C''.size + 2 ≤ C'.size :=
            elimFalse_size_drop_and_chain L r (hRL r hr) C' hM' (g r) j₂ hlt hj₂
              hop (hg_read r hr) hm₂
          set R' := R.erase r
          have hR'card : R'.card = k := by
            have h1 : R'.card = R.card - 1 := Finset.card_erase_of_mem hr
            omega
          have hEval'' : ∀ u ∈ R', ∀ c : Fin m, C''.eval (rowInput base u c) = G u c := by
            intro u hu c
            have hne : u ≠ r := (Finset.mem_erase.1 hu).1
            have huR : u ∈ R := (Finset.mem_erase.1 hu).2
            have hxr : (rowInput base u c).getD r false = false := by
              rw [rowInput_getD base hlen u (hRL u huR) c r, if_neg (Ne.symm hne), hR0 r hr c]
            rw [elimFalse_eval L r C' hM' hW' (rowInput base u c)
              (by rw [length_rowInput, hlen]) hxr, hEval' u huR c]
          have hsub := ih hih R' hR'card
            (fun u hu => hRL u (Finset.mem_erase.1 hu).2)
            (fun u hu => hR0 u (Finset.mem_erase.1 hu).2)
            G
            (fun u hu v hv => hPair u (Finset.mem_erase.1 hu).2 v (Finset.mem_erase.1 hv).2)
            (fun u hu v hv w hw =>
              hTriple u (Finset.mem_erase.1 hu).2 v (Finset.mem_erase.1 hv).2 w (Finset.mem_erase.1 hw).2)
            C'' hM'' hEval''
          omega
        · push_neg at hand
          have hg_or : ∀ r (hr : r ∈ R), (C'.gates[g r]'(hg_lt r hr)).op = GateOp.or := by
            intro r hr
            have hop := (hM' (C'.gates[g r]'(hg_lt r hr)) (List.getElem_mem (hg_lt r hr))).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with h1 | h2
            · exact False.elim (hand r hr h1)
            · exact h2
          have h2n := case_private_row_ors base hlen R hRL hR0 G (by omega) hPair hTriple
            C' hM' hW' hEval' g hg_lt hg_read hg_sole hg_or
          omega

private theorem rowInput_eq_oneHot {n m p : ℕ} (code : Fin m → Fin p → Bool)
    (u : Fin n) (c : Fin m) :
    rowInput (fun c' => List.replicate n false ++ List.ofFn (code c')) u.val c =
      List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c) := by
  apply List.ext_getElem
  · simp [rowInput]
  · intro i h1 h2
    have hl1 : (List.replicate n false ++ List.ofFn (code c)).length = n + p := by simp
    have hi : i < n + p := by simpa [rowInput] using h1
    have hget : (rowInput (fun c' => List.replicate n false ++ List.ofFn (code c')) u.val c)[i] =
        (rowInput (fun c' => List.replicate n false ++ List.ofFn (code c')) u.val c).getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    have hget2 : (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c))[i] =
        (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c)).getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [hget, hget2, rowInput_getD (L := n + p) _ (fun _ => by simp) u.val (by omega) c i]
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by simpa using hin),
        List.getD_append _ _ _ _ (by simpa using hin)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hin, ↓reduceIte,
        Option.getD_some, List.getElem?_ofFn, Fin.ext_iff]
      by_cases hiu : i = u.val <;> simp [hiu]
    · have hiu : i ≠ u.val := by omega
      rw [if_neg hiu, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp; omega),
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.length_ofFn]

end PEqualNP.Outside.L_meta_25534_aux

theorem PEqualNP.Outside.L_meta_25534 : (∀ (n m p : Nat) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ n →
  (∀ u v : Fin n, u ≠ v →
    ∃ c : Fin m, G u c = true ∧ G v c = false) →
  (∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
    ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  (∀ (u : Fin n) (c : Fin m),
    C.eval (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c)) = G u c) →
  2 * n - 1 ≤ C.size) := by
  intro n m p G code C hn hPair hTriple hM hEval
  let base : Fin m → List Bool := fun c => List.replicate n false ++ List.ofFn (code c)
  have hlen : ∀ c, (base c).length = n + p := by intro c; simp [base]
  let R : Finset ℕ := Finset.range n
  have hRL : ∀ r ∈ R, r < n + p := by
    intro r hr
    have := Finset.mem_range.1 hr
    omega
  have hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false := by
    intro r hr c
    have hlt : r < n := Finset.mem_range.1 hr
    simp only [base]
    rw [List.getD_append _ _ _ _ (by simpa using hlt)]
    simp [List.getD_eq_getElem?_getD, hlt]
  let G' : ℕ → Fin m → Bool := fun r c => if h : r < n then G ⟨r, h⟩ c else false
  have hPair' : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G' u c = true ∧ G' v c = false := by
    intro u hu v hv huv
    have hun : u < n := Finset.mem_range.1 hu
    have hvn : v < n := Finset.mem_range.1 hv
    have hne : (⟨u, hun⟩ : Fin n) ≠ ⟨v, hvn⟩ := fun h => huv (congrArg Fin.val h)
    obtain ⟨c, h1, h2⟩ := hPair ⟨u, hun⟩ ⟨v, hvn⟩ hne
    exact ⟨c, by simp [G', hun, h1], by simp [G', hvn, h2]⟩
  have hTriple' : ∀ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G' u c = true ∧ G' v c = true ∧ G' w c = false := by
    intro u hu v hv w hw huv huw hvw
    have hun : u < n := Finset.mem_range.1 hu
    have hvn : v < n := Finset.mem_range.1 hv
    have hwn : w < n := Finset.mem_range.1 hw
    obtain ⟨c, h1, h2, h3⟩ := hTriple ⟨u, hun⟩ ⟨v, hvn⟩ ⟨w, hwn⟩
      (fun h => huv (congrArg Fin.val h))
      (fun h => huw (congrArg Fin.val h))
      (fun h => hvw (congrArg Fin.val h))
    exact ⟨c, by simp [G', hun, h1], by simp [G', hvn, h2], by simp [G', hwn, h3]⟩
  have hEval' : ∀ u ∈ R, ∀ c : Fin m,
      C.eval (PEqualNP.Outside.L_meta_25534_aux.rowInput base u c) = G' u c := by
    intro u hu c
    have hun : u < n := Finset.mem_range.1 hu
    simp only [G', dif_pos hun]
    rw [show PEqualNP.Outside.L_meta_25534_aux.rowInput base u c =
        PEqualNP.Outside.L_meta_25534_aux.rowInput base (⟨u, hun⟩ : Fin n).val c from rfl,
      PEqualNP.Outside.L_meta_25534_aux.rowInput_eq_oneHot code ⟨u, hun⟩ c]
    exact hEval ⟨u, hun⟩ c
  exact PEqualNP.Outside.L_meta_25534_aux.main_ind base hlen n hn R (Finset.card_range n)
    hRL hR0 G' hPair' hTriple' C hM hEval'
