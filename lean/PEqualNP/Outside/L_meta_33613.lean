import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_5465

namespace PEqualNP.Outside.L_meta_33613

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_meta_5465

private theorem oneEach_len {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by simp [oneEach]

private theorem oneEach_read {n m : ℕ} (i : Fin n) (j : Fin m) (k : ℕ) :
    (oneEach i j).getD k false = decide (k = i.val ∨ k = n + j.val) := by
  by_cases hkn : k < n
  · rw [oneEach, getD_app_lt _ _ _ (by simpa using hkn), ofFn_getD _ _ hkn]
    have hne : k ≠ n + j.val := by omega
    simp [hne, Fin.ext_iff]
  · rw [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using (show n ≤ k by omega))]
    simp only [List.length_ofFn]
    rw [← List.getD_eq_getElem?_getD]
    have hne : k ≠ i.val := by omega
    by_cases h : k - n < m
    · rw [ofFn_getD _ _ h]
      simp only [Fin.ext_iff, hne, false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · rw [ofFn_getD_ge _ _ (by omega)]
      simp only [hne, false_or]
      symm
      apply decide_eq_false
      omega

private theorem read_set_false (x : List Bool) (k u : ℕ) (hk : k < x.length) :
    (x.set k false).getD u false = if u = k then false else x.getD u false := by
  by_cases h : u = k
  · subst u
    simp [List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, h, Ne.symm h]

private theorem list_of_reads (x : List Bool) {N : ℕ} (hx : x.length = N) :
    (List.ofFn fun i : Fin N => x.getD i.val false) = x := by
  subst N
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

private theorem eval_mono {N : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : List Bool}
    (hx : x.length = N) (hy : y.length = N)
    (hle : ∀ k : ℕ, x.getD k false = true → y.getD k false = true) :
    C.eval x = true → C.eval y = true := by
  intro h
  have hh : ∀ i : Fin N, x.getD i.val false = true → y.getD i.val false = true := fun i => hle i.val
  have h' : val C (List.ofFn fun i : Fin N => x.getD i.val false) C.output = true := by
    simpa only [list_of_reads x hx, ← eval_eq_val] using h
  simpa only [list_of_reads y hy, ← eval_eq_val] using
    mono N C (andOrOnly_of_monotone2 hC) _ _ hh C.output h'

private def pullWire {N M : ℕ} (f : Fin N → Option (Fin M)) (B k : ℕ) : ℕ :=
  if h : k < N then ((f ⟨k,h⟩).map Fin.val).getD (M+B) else M+(k-N)

private def pullGate {N M : ℕ} (f : Fin N → Option (Fin M)) (B : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (pullWire f B)⟩

private def pullCircuit {N M : ℕ} (f : Fin N → Option (Fin M)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (pullGate f C.size), pullWire f C.size C.output⟩

private theorem pull_mono {N M : ℕ} (f : Fin N → Option (Fin M)) {C : Circuit}
    (h : Monotone2 C) : Monotone2 (pullCircuit f C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa [pullGate] using h a ha

private theorem pull_size {N M : ℕ} (f : Fin N → Option (Fin M)) (C : Circuit) :
    (pullCircuit f C).size = C.size := by simp [pullCircuit, Circuit.size]

private theorem pull_run {N M : ℕ} (f : Fin N → Option (Fin M)) (B : ℕ) (gs : List Gate)
    (a b : List Bool) (j : ℕ) (hj : j + gs.length ≤ B) (ha : a.length = N+j) (hb : b.length = M+j)
    (hread : ∀ k, b.getD (pullWire f B k) false = a.getD k false) :
    ∀ k, (W (gs.map (pullGate f B)) b).getD (pullWire f B k) false = (W gs a).getD k false := by
  induction gs generalizing a b j with
  | nil => exact hread
  | cons g gs ih =>
    simp only [List.map_cons, W_cons]
    apply ih _ _ (j+1) (by simp at hj; omega) (by rw [step_len, ha]; omega)
      (by rw [step_len, hb]; omega)
    have hv : (pullGate f B g).op.eval ((pullGate f B g).inputs.map fun k => b.getD k false) =
        g.op.eval (g.inputs.map fun k => a.getD k false) := by
      simp only [pullGate, List.map_map, Function.comp_def, hread]
    intro k
    by_cases hk : k < N
    · rw [step_lt a g k (by omega)]
      unfold pullWire
      rw [dite_eq_left hk]
      cases hfk : f ⟨k,hk⟩ with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        have hz : M+B ≥ (step b (pullGate f B g)).length := by rw [step_len, hb]; simp at hj; omega
        have hz' : M+B ≥ b.length := by simp at hj; omega
        rw [getD_ge _ _ hz]
        simpa only [pullWire, dite_eq_left hk, hfk, Option.map_none, Option.getD_none, getD_ge _ _ hz'] using hread k
      | some i =>
        simp only [Option.map_some, Option.getD_some]
        rw [step_lt _ _ _ (by have := i.isLt; omega)]
        simpa only [pullWire, dite_eq_left hk, hfk, Option.map_some, Option.getD_some] using hread k
    · have ew : pullWire f B k = M+(k-N) := dite_eq_right hk
      by_cases hkl : k < a.length
      · rw [step_lt _ _ _ hkl, step_lt _ _ _ (by rw [ew]; omega)]
        exact hread k
      · by_cases he : k = a.length
        · rw [step_last _ _ _ he, step_last _ _ _ (by rw [ew]; omega), hv]
        · have hza : (step a g).length ≤ k := by rw [step_len]; omega
          have hzb : (step b (pullGate f B g)).length ≤ pullWire f B k := by rw [step_len, ew]; omega
          rw [getD_ge _ _ hza, getD_ge _ _ hzb]

private theorem pull_eval {N M : ℕ} (f : Fin N → Option (Fin M)) (C : Circuit)
    (x : List Bool) (hx : x.length = M) :
    (pullCircuit f C).eval x = C.eval (List.ofFn fun i => (f i).elim false fun j => x.getD j.val false) := by
  simp only [eval_W, pullCircuit]
  apply pull_run f C.size C.gates _ x 0 (by simp [Circuit.size]) (by simp) (by simpa using hx)
  intro k
  by_cases hk : k < N
  · rw [ofFn_getD _ _ hk]
    unfold pullWire
    rw [dite_eq_left hk]
    cases f ⟨k,hk⟩ with
    | none => exact getD_ge _ _ (by simp [hx])
    | some i => rfl
  · rw [ofFn_getD_ge _ _ (by omega)]
    exact getD_ge _ _ (by rw [pullWire, dite_eq_right hk, hx]; omega)

private def wire (k : ℕ) : Circuit := ⟨[], k⟩

private def addGate (N : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a,b]⟩], N+C.size⟩

private theorem wire_size (k : ℕ) : (wire k).size = 0 := rfl

private theorem wire_mono (k : ℕ) : Monotone2 (wire k) := by simp [wire, Monotone2]

private theorem wire_read (k : ℕ) (x : List Bool) : val (wire k) x k = x.getD k false := rfl

private theorem add_size (N : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate N C op a b).size = C.size+1 := by simp [addGate, Circuit.size]

private theorem add_mono {N : ℕ} {C : Circuit} (a b : ℕ) (h : Monotone2 C) (op : GateOp)
    (ho : op = .and ∨ op = .or) : Monotone2 (addGate N C op a b) := by
  intro g hg
  simp only [addGate, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · simpa using ho

private theorem add_read {N : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool)
    (hx : x.length = N) :
    val (addGate N C op a b) x (N+C.size) = op.eval [val C x a, val C x b] := by
  have hidx : N+C.size = x.length+C.gates.length := by rw [hx]; rfl
  change (W (C.gates ++ [⟨op, [a,b]⟩]) x).getD (N+C.size) false = _
  rw [hidx, W_snoc_getD, if_pos rfl]
  rfl

private theorem add_preserve {N : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool)
    (hx : x.length = N) (u : ℕ) (hu : u < N+C.size) :
    val (addGate N C op a b) x u = val C x u := by
  change (W (C.gates ++ [⟨op, [a,b]⟩]) x).getD u false = _
  rw [W_snoc_getD, ite_eq_right (by change u ≠ x.length + C.size; omega)]
  rfl

private def orStep (N : ℕ) (C : Circuit) (u : ℕ) : Circuit := addGate N C .or C.output u

private def orFrom (N : ℕ) (C : Circuit) (k : ℕ) (l : List ℕ) : Circuit :=
  l.foldl (orStep N) { C with output := k }

private theorem orFrom_size (N : ℕ) (C : Circuit) (k : ℕ) (l : List ℕ) :
    (orFrom N C k l).size = C.size + l.length := by
  induction l generalizing C k with
  | nil => simp [orFrom, Circuit.size]
  | cons u l ih =>
    change (orFrom N (orStep N { C with output := k } u) (N+C.size) l).size = _
    rw [ih, orStep, add_size]
    simp only [List.length_cons]
    change C.size + 1 + l.length = _
    omega

private theorem orFrom_mono {N : ℕ} {C : Circuit} (k : ℕ) (l : List ℕ) (h : Monotone2 C) :
    Monotone2 (orFrom N C k l) := by
  induction l generalizing C k with
  | nil => exact h
  | cons u l ih =>
    change Monotone2 (orFrom N (orStep N { C with output := k } u) (N+C.size) l)
    exact ih _ (add_mono _ _ h _ (Or.inr rfl))

private theorem orFrom_preserve {N : ℕ} (C : Circuit) (k : ℕ) (l : List ℕ) (x : List Bool)
    (hx : x.length = N) (u : ℕ) (hu : u < N+C.size) : val (orFrom N C k l) x u = val C x u := by
  induction l generalizing C k with
  | nil => rfl
  | cons v l ih =>
    change val (orFrom N (orStep N { C with output := k } v) (N+C.size) l) x u = _
    rw [ih _ _ (by rw [orStep, add_size]; change u < N+(C.size+1); omega)]
    exact add_preserve _ _ _ _ _ hx _ hu

private theorem orFrom_bound {N : ℕ} (C : Circuit) (k : ℕ) (l : List ℕ) (hk : k < N+C.size) :
    (orFrom N C k l).output < N+(orFrom N C k l).size := by
  induction l generalizing C k with
  | nil => exact hk
  | cons v l ih =>
    change (orFrom N (orStep N { C with output := k } v) (N+C.size) l).output < _
    apply ih
    rw [orStep, add_size]
    change N+C.size < N+(C.size+1)
    omega

private theorem orFrom_read {N : ℕ} (C : Circuit) (k : ℕ) (l : List ℕ) (x : List Bool)
    (hx : x.length = N) (hl : ∀ u ∈ l, u < N) :
    (orFrom N C k l).eval x = (val C x k || l.any (fun u => x.getD u false)) := by
  induction l generalizing C k with
  | nil => simp [orFrom, eval_eq_val]; rfl
  | cons v l ih =>
    change (orFrom N (orStep N { C with output := k } v) (N+C.size) l).eval x = _
    rw [ih _ _ (fun u hu => hl u (by simp [hu]))]
    have he := (add_read ({ C with output := k }) .or k v x hx).trans (eval_or2 _ _)
    change val (orStep N { C with output := k } v) x (N+C.size) =
      ((val C x k) || (val C x v)) at he
    rw [he, val_input hx (hl v (by simp))]
    exact Bool.or_assoc _ _ _

private theorem output_valid {N : ℕ} (C : Circuit) (x : List Bool) (hx : x.length = N)
    (he : C.eval x = true) : C.output < N+C.size := by
  by_contra h
  rw [eval_eq_val, val_ge hx (by change N+C.size ≤ C.output; omega)] at he
  cases he

-- Adapted from the elimination pass in lean/PEqualNP/Outside/L_meta_10806.lean
-- at 3e77241c5aa7d773f9ef3c591880460c720c6b3b. The input width stays fixed,
-- and only false is propagated: even a nullary AND retains its original gate.
private theorem delGetDSnocNe {α : Type} (l : List α) (v d : α) (i : ℕ)
    (hi : i ≠ l.length) : (l ++ [v]).getD i d = l.getD i d := by
  by_cases h : i < l.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem delGetDSnocEq {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by simp

private theorem delGetDSetNe (x : List Bool) {i k : ℕ} (h : i ≠ k) :
    (x.set k false).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h.symm]

private theorem delGetDSetSame (x : List Bool) {k : ℕ} (h : k < x.length) :
    (x.set k false).getD k false = false := by
  simp [List.getD_eq_getElem?_getD, h]

private def delValid (m : ℕ) : Option ℕ → Prop
  | none => True
  | some j => j < m

private def delVal (w : List Bool) : Option ℕ → Bool
  | none => false
  | some j => w.getD j false

private def delGate (op : GateOp) (m : ℕ) : List (Option ℕ) → Option Gate × Option ℕ
  | [] => (some ⟨op, []⟩, some m)
  | [a] => (none, a)
  | [some a, some b] => (some ⟨op, [a, b]⟩, some m)
  | [none, b] => (none, match op with | .or => b | _ => none)
  | [some a, none] => (none, match op with | .or => some a | _ => none)
  | _ => (none, none)

private def DelGateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem delGate_ok (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (m : ℕ) (ins : List (Option ℕ)) {g : Gate}
    (hg : g ∈ (delGate op m ins).1.toList) : DelGateOK g := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · have h : (⟨op, []⟩ : Gate) = g := by
      simpa only [delGate, Prod.fst, Option.mem_toList, Option.some.injEq] using hg
    subst g
    simpa [DelGateOK] using hop
  · simp [delGate] at hg
  · cases a <;> cases b <;> simp [delGate] at hg
    subst g
    simpa [DelGateOK] using hop
  · simp [delGate] at hg

private theorem delGate_none (op : GateOp) (m : ℕ) (ins : List (Option ℕ))
    (h : none ∈ ins) : (delGate op m ins).1 = none := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at h
  · simp [delGate]
  · cases a <;> cases b <;> simp_all [delGate]
  · simp [delGate]

private theorem delKeep_sound (w : List Bool) (op : GateOp) (js : List ℕ) :
    delValid (w.length + (some (⟨op, js⟩ : Gate)).toList.length) (some w.length) ∧
      delVal (W (some (⟨op, js⟩ : Gate)).toList w) (some w.length) =
        op.eval ((js.map some).map (delVal w)) := by
  refine ⟨by simp [delValid], ?_⟩
  simpa [W_single, delVal, List.map_map, Function.comp_def] using
    step_last w ⟨op, js⟩ w.length rfl

private theorem delGate_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List (Option ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ a ∈ ins, delValid w.length a) :
    delValid (w.length + (delGate op w.length ins).1.toList.length) (delGate op w.length ins).2 ∧
      delVal (W (delGate op w.length ins).1.toList w) (delGate op w.length ins).2 =
        op.eval (ins.map (delVal w)) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact delKeep_sound w op []
  · have ha := hv a (by simp)
    rcases hop with rfl | rfl <;> simpa [delGate, W_nil, eval_and1, eval_or1] using ha
  · cases a with
    | none =>
      have hb := hv b (by simp)
      rcases hop with rfl | rfl <;>
        simp [delGate, W_nil, delVal, delValid, eval_and2, eval_or2]
      exact hb
    | some j =>
      cases b with
      | none =>
        have ha := hv (some j) (by simp)
        rcases hop with rfl | rfl <;>
          simp [delGate, W_nil, delVal, delValid, eval_and2, eval_or2] at ha ⊢
        exact ha
      | some k => exact delKeep_sound w op [j, k]
  · simp at hlen

private def delStep (N : ℕ) (a : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  let r := delGate g.op (N + a.2.length) (g.inputs.map fun i => a.1.getD i none)
  (a.1 ++ [r.2], a.2 ++ r.1.toList)

private def delRun (N : ℕ) (gs : List Gate) (a : List (Option ℕ) × List Gate) :
    List (Option ℕ) × List Gate := gs.foldl (delStep N) a

private theorem delRun_cons (N : ℕ) (g : Gate) (gs : List Gate)
    (a : List (Option ℕ) × List Gate) :
    delRun N (g :: gs) a = delRun N gs (delStep N a g) := rfl

private theorem delStep_le (N : ℕ) (a : List (Option ℕ) × List Gate) (g : Gate) :
    (delStep N a g).2.length ≤ a.2.length + 1 := by
  simp only [delStep, List.length_append]
  cases (delGate g.op (N + a.2.length) (g.inputs.map fun i => a.1.getD i none)).1 <;> simp

private theorem delRun_le (N : ℕ) (gs : List Gate) : ∀ a : List (Option ℕ) × List Gate,
    (delRun N gs a).2.length ≤ a.2.length + gs.length := by
  induction gs with
  | nil => intro a; simp [delRun]
  | cons g gs ih =>
    intro a
    rw [delRun_cons, List.length_cons]
    have := ih (delStep N a g)
    have := delStep_le N a g
    omega

private theorem delRun_lt (N k : ℕ) (gs : List Gate) : ∀ a : List (Option ℕ) × List Gate,
    k < a.1.length → a.1.getD k none = none → (∃ g ∈ gs, k ∈ g.inputs) →
      (delRun N gs a).2.length < a.2.length + gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro a hk hnone hread
    rw [delRun_cons, List.length_cons]
    by_cases hg : k ∈ g.inputs
    · have hskip : (delStep N a g).2.length = a.2.length := by
        have hmem : none ∈ g.inputs.map (fun i => a.1.getD i none) :=
          List.mem_map.2 ⟨k, hg, hnone⟩
        change (a.2 ++ (delGate g.op (N + a.2.length)
          (g.inputs.map fun i => a.1.getD i none)).1.toList).length = a.2.length
        rw [delGate_none _ _ _ hmem]
        simp
      have := delRun_le N gs (delStep N a g)
      omega
    · have htail : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hread
        rcases List.mem_cons.1 hg' with rfl | hmem
        · exact (hg hk').elim
        · exact ⟨g', hmem, hk'⟩
      have hnext : k < (delStep N a g).1.length := by simp [delStep]; omega
      have hget : (delStep N a g).1.getD k none = none := by
        simpa only [delStep, List.getD_append _ _ _ _ hk] using hnone
      have := ih (delStep N a g) hnext hget htail
      have := delStep_le N a g
      omega

private theorem delRun_ok (N : ℕ) (gs : List Gate) : ∀ a : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, DelGateOK g) → (∀ g ∈ a.2, DelGateOK g) →
      ∀ g ∈ (delRun N gs a).2, DelGateOK g := by
  induction gs with
  | nil => intro a _ h; exact h
  | cons g gs ih =>
    intro a hgs ha
    rw [delRun_cons]
    apply ih _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    change g' ∈ a.2 ++ (delGate g.op (N + a.2.length)
      (g.inputs.map fun i => a.1.getD i none)).1.toList at hg'
    rcases List.mem_append.1 hg' with h | h
    · exact ha g' h
    · exact delGate_ok _ (hgs g List.mem_cons_self).1 _ _ h

private theorem delVal_prefix (w : List Bool) (gs : List Gate) (s : Option ℕ)
    (h : delValid w.length s) : delVal (W gs w) s = delVal w s := by
  cases s with
  | none => rfl
  | some i => exact W_prefix gs w i h

private theorem delValid_mono {m m' : ℕ} (h : m ≤ m') (s : Option ℕ)
    (hs : delValid m s) : delValid m' s := by
  cases s with
  | none => trivial
  | some j => exact lt_of_lt_of_le hs h

private def DelInv (N : ℕ) (x w : List Bool) (a : List (Option ℕ) × List Gate) : Prop :=
  a.1.length = w.length ∧ ∀ i : ℕ,
    delValid (N + a.2.length) (a.1.getD i none) ∧
      delVal (W a.2 x) (a.1.getD i none) = w.getD i false

private theorem delRun_inv (N : ℕ) (x : List Bool) (hx : x.length = N) (gs : List Gate) :
    ∀ (w : List Bool) (a : List (Option ℕ) × List Gate),
      (∀ g ∈ gs, DelGateOK g) → DelInv N x w a → DelInv N x (W gs w) (delRun N gs a) := by
  induction gs with
  | nil => intro w a _ h; exact h
  | cons g gs ih =>
    intro w a hgs ha
    rw [W_cons, delRun_cons]
    apply ih _ _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := ha
    set w' := W a.2 x with hw'
    have hwlen : w'.length = N + a.2.length := by rw [hw', W_length, hx]
    let ins := g.inputs.map (fun i => a.1.getD i none)
    have hg := hgs g List.mem_cons_self
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
    have hs := delGate_sound g.op hop w' ins (by simpa [ins] using hg.2) (by
      intro s hs
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hs
      rw [hwlen]
      exact (hi j).1)
    rw [hwlen] at hs
    let r := delGate g.op (N + a.2.length) ins
    have hvals : ins.map (delVal w') = g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun j _ => (hi j).2)
    refine ⟨by simp [delStep, step, hl], ?_⟩
    intro i
    change delValid (N + (a.2 ++ r.1.toList).length) ((a.1 ++ [r.2]).getD i none) ∧
      delVal (W (a.2 ++ r.1.toList) x) ((a.1 ++ [r.2]).getD i none) =
        (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD i false
    rw [W_append, List.length_append, ← Nat.add_assoc]
    by_cases h : i = a.1.length
    · rw [h, delGetDSnocEq, hl, delGetDSnocEq]
      exact ⟨hs.1, hs.2.trans (congrArg g.op.eval hvals)⟩
    · rw [delGetDSnocNe _ _ _ _ h, delGetDSnocNe _ _ _ _ (by omega)]
      refine ⟨delValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [delVal_prefix _ _ _ (by rw [hwlen]; exact (hi i).1)]
      exact (hi i).2

private def delInit (N k : ℕ) : List (Option ℕ) :=
  List.ofFn fun i : Fin N => if i.val = k then none else some i.val

private theorem delInit_at {N k i : ℕ} (hi : i < N) :
    (delInit N k).getD i none = if i = k then none else some i := by
  simp [delInit, List.getD_eq_getElem?_getD, hi]

private theorem delInit_inv (N k : ℕ) (x : List Bool) (hx : x.length = N) :
    DelInv N x (x.set k false) (delInit N k, []) := by
  refine ⟨by simp [delInit, hx], ?_⟩
  intro i
  change delValid (N + 0) ((delInit N k).getD i none) ∧
    delVal x ((delInit N k).getD i none) = (x.set k false).getD i false
  by_cases hi : i < N
  · rw [delInit_at hi]
    by_cases hik : i = k
    · subst i
      rw [ite_eq_left rfl]
      exact ⟨trivial, (delGetDSetSame x (by omega)).symm⟩
    · rw [ite_eq_right hik]
      exact ⟨by simpa [delValid] using hi, (delGetDSetNe x hik).symm⟩
  · have hd : (delInit N k).getD i none = none :=
      List.getD_eq_default _ _ (by simpa [delInit] using Nat.le_of_not_lt hi)
    have he : (x.set k false).getD i false = false :=
      List.getD_eq_default _ _ (by simpa [hx] using Nat.le_of_not_lt hi)
    exact ⟨by rw [hd]; trivial, by rw [hd, he]; rfl⟩

private theorem delNoRead (k : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ (w v : List Bool), w.length = v.length →
      (∀ i, i ≠ k → w.getD i false = v.getD i false) →
      ∀ i, i ≠ k → (W gs w).getD i false = (W gs v).getD i false := by
  induction gs with
  | nil => intro w v _ he; exact he
  | cons g gs ih =>
    intro w v hl he
    simp only [W_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (step w g) (step v g) (by rw [step_len, step_len, hl])
    intro i hi
    by_cases h : i = w.length
    · have hvals : g.inputs.map (fun j => w.getD j false) =
          g.inputs.map (fun j => v.getD j false) := by
        apply List.map_congr_left
        intro j hj
        exact he j (fun e => hg g List.mem_cons_self (e ▸ hj))
      rw [step_last _ _ _ h, step_last _ _ _ (h.trans hl), hvals]
    · simp only [step]
      rw [delGetDSnocNe _ _ _ _ h, delGetDSnocNe _ _ _ _ (by omega), he i hi]

private theorem deleteInput {N k : ℕ} {C : Circuit} (hC : Monotone2 C) (hk : k < N)
    (hdep : ∃ x : List Bool, x.length = N ∧ C.eval x ≠ C.eval (x.set k false))
    (htrue : ∃ x : List Bool, x.length = N ∧ C.eval (x.set k false) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : List Bool, x.length = N → D.eval x = C.eval (x.set k false) := by
  obtain ⟨y, hy, hyt⟩ := htrue
  have hout : C.output ≠ k := by
    intro h
    rw [eval_W, h, W_prefix _ _ _ (by simpa [hy] using hk),
      delGetDSetSame y (by omega)] at hyt
    cases hyt
  have hread : ∃ g ∈ C.gates, k ∈ g.inputs := by
    by_contra hn
    obtain ⟨x, hx, hd⟩ := hdep
    apply hd
    simp only [eval_W]
    exact delNoRead k C.gates (fun g hg hkg => hn ⟨g, hg, hkg⟩)
      x (x.set k false) (by simp) (fun i hi => (delGetDSetNe x hi).symm) C.output hout
  let a := delRun N C.gates (delInit N k, [])
  have hsim (x : List Bool) (hx : x.length = N) :
      delVal (W a.2 x) (a.1.getD C.output none) = C.eval (x.set k false) :=
    ((delRun_inv N x hx C.gates (x.set k false) (delInit N k, []) hC
      (delInit_inv N k x hx)).2 C.output).2
  have hlen : a.2.length < C.gates.length := by
    simpa using delRun_lt N k C.gates (delInit N k, [])
      (by simpa [delInit] using hk) (by
        change (delInit N k).getD k none = none
        rw [delInit_at hk, ite_eq_left rfl]) hread
  cases ho : a.1.getD C.output none with
  | none =>
    have h := hsim y hy
    rw [ho, delVal, hyt] at h
    cases h
  | some j =>
    refine ⟨⟨a.2, j⟩, delRun_ok N C.gates (delInit N k, []) hC (by simp), hlen, ?_⟩
    intro x hx
    have h := hsim x hx
    rw [ho] at h
    exact h

-- Truth-table abstraction and bounded search adapted from lean/PEqualNP/Outside/L_meta_203.lean
-- at 3e77241c5aa7d773f9ef3c591880460c720c6b3b, using the nine one-hot pairs
-- instead of the full cube and retaining only AND, OR, copies and constants.
private abbrev SmallFloorTable := BitVec 9

private def smallFloor_inputs : List SmallFloorTable := [7, 56, 448, 73, 146, 292]

private def smallFloor_read (p : Nat) (t : SmallFloorTable) : Bool := t.getLsbD p

private theorem smallFloor_getD (p : Nat) (ws : List SmallFloorTable) (i : Nat) :
    (ws.map (smallFloor_read p)).getD i false = smallFloor_read p (ws.getD i 0) := by
  rw [show false = smallFloor_read p 0 by simp [smallFloor_read], List.getD_map]

private def smallFloor_gate (ws : List SmallFloorTable) (g : Gate) : SmallFloorTable :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | _, _ => 0

private theorem smallFloor_readGate (p : Nat) (hp : p < 9) (ws : List SmallFloorTable) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (smallFloor_read p)).getD i false) =
      smallFloor_read p (smallFloor_gate ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have hop' : op = GateOp.and ∨ op = GateOp.or := by simpa using hop
  simp only [smallFloor_getD]
  rcases hop' with rfl | rfl
  · match ins, hlen with
    | [], _ =>
      change true = (~~~(0 : SmallFloorTable)).getLsbD p
      have hz : (0 : SmallFloorTable).getLsbD p = false := by simp
      rw [BitVec.getLsbD_not, decide_eq_true hp, Bool.true_and, hz, Bool.not_false]
    | [i], _ => simp [smallFloor_gate, GateOp.eval]
    | [i, j], _ => simp [smallFloor_gate, GateOp.eval, smallFloor_read, BitVec.getLsbD_and]
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => simp [smallFloor_gate, GateOp.eval, smallFloor_read]
    | [i], _ => simp [smallFloor_gate, GateOp.eval]
    | [i, j], _ => simp [smallFloor_gate, GateOp.eval, smallFloor_read, BitVec.getLsbD_or]
    | _ :: _ :: _ :: _, h => simp at h

private def smallFloor_wires (gs : List Gate) (ws : List SmallFloorTable) : List SmallFloorTable :=
  gs.foldl (fun vs g => vs ++ [smallFloor_gate vs g]) ws

private theorem smallFloor_readWires (p : Nat) (hp : p < 9) (gs : List Gate) (ws : List SmallFloorTable)
    (h : Monotone2 ⟨gs, 0⟩) :
    W gs (ws.map (smallFloor_read p)) = (smallFloor_wires gs ws).map (smallFloor_read p) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := smallFloor_readGate p hp ws g (h g List.mem_cons_self)
    change W gs (ws.map (smallFloor_read p) ++ [g.op.eval (g.inputs.map fun i =>
        (ws.map (smallFloor_read p)).getD i false)]) =
      (smallFloor_wires gs (ws ++ [smallFloor_gate ws g])).map (smallFloor_read p)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private def smallFloor_pairs : List SmallFloorTable → List SmallFloorTable
  | [] => []
  | a :: ws => (ws.flatMap fun b => [a &&& b, a ||| b]) ++ smallFloor_pairs ws

private def smallFloor_choices (ws : List SmallFloorTable) : List SmallFloorTable :=
  ~~~0 :: (ws ++ smallFloor_pairs ws)

private theorem smallFloor_available (ws : List SmallFloorTable) (i : Nat) :
    ws.getD i 0 ∈ 0 :: ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_cons_self

private theorem smallFloor_copyChoice (ws : List SmallFloorTable) (a : SmallFloorTable)
    (ha : a ∈ ws) : a ∈ smallFloor_choices ws := by
  exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)

private theorem smallFloor_pairAvailable (ws : List SmallFloorTable) (a b : SmallFloorTable)
    (ha : a ∈ ws) (hb : b ∈ ws) :
    a = b ∨ (a &&& b ∈ smallFloor_pairs ws ∧ a ||| b ∈ smallFloor_pairs ws) := by
  induction ws with
  | nil => simp at ha
  | cons c ws ih =>
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩)⟩
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩)⟩
      · rw [BitVec.and_comm]; simp
      · rw [BitVec.or_comm]; simp
    · rcases ih ha' hb' with h | ⟨hAnd, hOr⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_right _ hAnd, List.mem_append_right _ hOr⟩

private theorem smallFloor_binaryChoice (ws : List SmallFloorTable) (a b c : SmallFloorTable)
    (ha : a ∈ ws) (hb : b ∈ ws) (hc : c ∈ [a &&& b, a ||| b]) :
    c ∈ smallFloor_choices ws := by
  rcases smallFloor_pairAvailable ws a b ha hb with rfl | ⟨hAnd, hOr⟩
  · have h : c = a := by simpa using hc
    exact h ▸ smallFloor_copyChoice ws a ha
  · apply List.mem_cons_of_mem
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hAnd
    · exact hOr

private theorem smallFloor_gateChoice (ws : List SmallFloorTable) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    smallFloor_gate ws g ∈ smallFloor_choices (0 :: ws) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have hop' : op = GateOp.and ∨ op = GateOp.or := by simpa using hop
  rcases hop' with rfl | rfl
  · match ins, hlen with
    | [], _ => exact List.mem_cons_self
    | [i], _ => exact smallFloor_copyChoice _ _ (smallFloor_available ws i)
    | [i, j], _ =>
      exact smallFloor_binaryChoice _ _ _ _ (smallFloor_available ws i)
        (smallFloor_available ws j) (by simp [smallFloor_gate])
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => exact smallFloor_copyChoice _ 0 List.mem_cons_self
    | [i], _ => exact smallFloor_copyChoice _ _ (smallFloor_available ws i)
    | [i, j], _ =>
      exact smallFloor_binaryChoice _ _ _ _ (smallFloor_available ws i)
        (smallFloor_available ws j) (by simp [smallFloor_gate])
    | _ :: _ :: _ :: _, h => simp at h

private def smallFloor_reachable (target : SmallFloorTable) : Nat → List SmallFloorTable → Bool
  | 0, ws => (0 :: ws).contains target
  | 1, ws => (smallFloor_choices (0 :: ws)).contains target
  | fuel + 2, ws =>
      (smallFloor_choices (0 :: ws)).eraseDups.any
        (fun c => smallFloor_reachable target (fuel + 1) (ws ++ [c]))

private theorem smallFloor_reachableOfAvailable (target : SmallFloorTable) (fuel : Nat)
    (ws : List SmallFloorTable) (h : target ∈ 0 :: ws) :
    smallFloor_reachable target fuel ws = true := by
  induction fuel generalizing ws with
  | zero => exact List.contains_iff_mem.2 h
  | succ n ih =>
    cases n with
    | zero => exact List.contains_iff_mem.2 (smallFloor_copyChoice _ _ h)
    | succ n =>
      exact List.any_eq_true.2 ⟨0, List.mem_eraseDups.2 (smallFloor_copyChoice _ _ List.mem_cons_self),
        ih (ws ++ [0]) (List.mem_append_left [0] h)⟩

private theorem smallFloor_reachableOfCircuit (gs : List Gate) (ws : List SmallFloorTable)
    (fuel o : Nat) (h : Monotone2 ⟨gs, o⟩) (hsize : gs.length ≤ fuel) :
    smallFloor_reachable ((smallFloor_wires gs ws).getD o 0) fuel ws = true := by
  induction gs generalizing ws fuel with
  | nil => exact smallFloor_reachableOfAvailable _ _ _ (smallFloor_available ws o)
  | cons g gs ih =>
    let c := smallFloor_gate ws g
    have hc : c ∈ smallFloor_choices (0 :: ws) := smallFloor_gateChoice ws g (h g List.mem_cons_self)
    cases fuel with
    | zero => simp at hsize
    | succ n =>
      cases n with
      | zero =>
        have htail : gs.length ≤ 0 := Nat.le_of_succ_le_succ hsize
        obtain rfl : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp htail)
        let t := (ws ++ [c]).getD o 0
        have ht : t ∈ (0 :: ws) ++ [c] := smallFloor_available (ws ++ [c]) o
        change (smallFloor_choices (0 :: ws)).contains t = true
        apply List.contains_iff_mem.2
        rcases List.mem_append.1 ht with ht | ht
        · exact smallFloor_copyChoice _ _ ht
        · rwa [List.mem_singleton.1 ht]
      | succ n =>
        exact List.any_eq_true.2 ⟨c, List.mem_eraseDups.2 hc,
          ih (ws ++ [c]) (n + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (by
            simpa using hsize)⟩

private theorem smallFloor_firstChoices : (smallFloor_choices (0 :: smallFloor_inputs)).eraseDups =
    [511, 0, 7, 56, 448, 73, 146, 292, 63, 455, 1, 79, 2, 151, 4, 295,
     504, 8, 121, 16, 186, 32, 316, 64, 457, 128, 466, 256, 484, 219, 365, 438] := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem smallFloor_search : smallFloor_reachable 11 3 smallFloor_inputs = false := by
  apply Bool.eq_false_iff.2
  intro h
  obtain ⟨c, hc, hreach⟩ := List.any_eq_true.mp h
  rw [smallFloor_firstChoices] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change smallFloor_reachable 11 2 (smallFloor_inputs ++ [_]) = true at hreach
    exact (Bool.eq_false_iff.mp (show _ = false by decide +kernel)) hreach

private theorem smallFloor_points : ∀ p : Fin 9,
    let i : Fin 3 := ⟨p.val / 3, by have := p.isLt; omega⟩
    let j : Fin 3 := ⟨p.val % 3, by omega⟩
    oneEach i j = smallFloor_inputs.map (smallFloor_read p.val) ∧
      decide (i.val < 2 ∧ j.val < 2 ∧ (i.val = 0 ∨ j.val = 0)) = smallFloor_read p.val 11 := by
  decide +kernel

private theorem smallFloor : ∀ (C : Circuit), Monotone2 C →
    Represents (fun (i j : Fin 3) => decide (i.val < 2 ∧ j.val < 2 ∧ (i.val = 0 ∨ j.val = 0))) C →
    4 ≤ C.size := by
  intro C hmono hrep
  by_contra! hsmall
  have hcode : (smallFloor_wires C.gates smallFloor_inputs).getD C.output 0 = 11 := by
    apply BitVec.eq_of_getLsbD_eq
    intro p hp
    let k : Fin 9 := ⟨p, hp⟩
    let i : Fin 3 := ⟨p / 3, by omega⟩
    let j : Fin 3 := ⟨p % 3, by omega⟩
    have hpt := smallFloor_points k
    change oneEach i j = smallFloor_inputs.map (smallFloor_read p) ∧
      decide (i.val < 2 ∧ j.val < 2 ∧ (i.val = 0 ∨ j.val = 0)) = smallFloor_read p 11 at hpt
    change smallFloor_read p ((smallFloor_wires C.gates smallFloor_inputs).getD C.output 0) =
      smallFloor_read p 11
    rw [← smallFloor_getD, ← smallFloor_readWires p hp C.gates smallFloor_inputs hmono,
      ← hpt.1, ← eval_W, hrep i j]
    exact hpt.2
  have hreach := smallFloor_reachableOfCircuit C.gates smallFloor_inputs 3 C.output hmono
    (by unfold Circuit.size at hsmall; omega)
  rw [hcode, smallFloor_search] at hreach
  cases hreach

section CrossBounds

-- These parameters are the preceding private lemmas when the fragment is assembled.
variable (oneEach_read : ∀ {r c : ℕ} (i : Fin r) (j : Fin c) (k : ℕ),
  (oneEach i j).getD k false = decide (k = i.val ∨ k = r + j.val))
variable (oneEach_len : ∀ {r c : ℕ} (i : Fin r) (j : Fin c),
  (oneEach i j).length = r + c)
variable (read_set_false : ∀ (x : List Bool) (k u : ℕ), k < x.length →
  (x.set k false).getD u false = if u = k then false else x.getD u false)
variable (eval_mono : ∀ {N : ℕ} {C : Circuit}, Monotone2 C →
  ∀ {x y : List Bool}, x.length = N → y.length = N →
  (∀ k : ℕ, x.getD k false = true → y.getD k false = true) →
  C.eval x = true → C.eval y = true)
variable (deleteInput : ∀ {N k : ℕ} {C : Circuit}, Monotone2 C → k < N →
  (∃ x : List Bool, x.length = N ∧ C.eval x ≠ C.eval (x.set k false)) →
  (∃ x : List Bool, x.length = N ∧ C.eval (x.set k false) = true) →
  ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
    ∀ x : List Bool, x.length = N → D.eval x = C.eval (x.set k false))
variable (pullCircuit : ∀ {N M : ℕ}, (Fin N → Option (Fin M)) → Circuit → Circuit)
variable (pull_mono : ∀ {N M : ℕ} (f : Fin N → Option (Fin M)) {C : Circuit},
  Monotone2 C → Monotone2 (pullCircuit f C))
variable (pull_size : ∀ {N M : ℕ} (f : Fin N → Option (Fin M)) (C : Circuit),
  (pullCircuit f C).size = C.size)
variable (pull_eval : ∀ {N M : ℕ} (f : Fin N → Option (Fin M)) (C : Circuit)
    (x : List Bool), x.length = M →
    (pullCircuit f C).eval x = C.eval
      (List.ofFn fun i => (f i).elim false fun j => x.getD j.val false))
variable (smallFloor : ∀ (C : Circuit), Monotone2 C →
  Represents (fun (i j : Fin 3) =>
    decide (i.val < 2 ∧ j.val < 2 ∧ (i.val = 0 ∨ j.val = 0))) C → 4 ≤ C.size)

private def crossMatrix {r c : ℕ} (n m : ℕ) (i : Fin r) (j : Fin c) : Bool :=
  decide (i.val < n ∧ j.val < m ∧ (i.val = 0 ∨ j.val = 0))

include oneEach_read oneEach_len read_set_false in
private theorem crossSetOther {r c : ℕ} (i : Fin r) (j : Fin c) {k : ℕ}
    (hk : k < r + c) (hi : k ≠ i.val) (hj : k ≠ r + j.val) :
    (oneEach i j).set k false = oneEach i j := by
  have hl := oneEach_len i j
  apply List.ext_getElem (by simp)
  intro u hu hv
  have h := read_set_false (oneEach i j) k u (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some] at h
  rw [h]
  split
  · subst u
    have hr := oneEach_read i j k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some] at hr
    simpa [hi, hj] using hr.symm
  · rfl

include oneEach_read oneEach_len read_set_false eval_mono in
private theorem crossEraseFalse {r c : ℕ} {C : Circuit} (hC : Monotone2 C)
    (i : Fin r) (j : Fin c) (i' : Fin r) (j' : Fin c) {k : ℕ}
    (hk : k < r + c) (hkeep : ∀ u : ℕ,
      u ≠ k → (u = i.val ∨ u = r + j.val) → u = i'.val ∨ u = r + j'.val)
    (hz : C.eval (oneEach i' j') = false) :
    C.eval ((oneEach i j).set k false) = false := by
  have hl := oneEach_len i j
  cases h : C.eval ((oneEach i j).set k false) with
  | false => rfl
  | true =>
    have hh := eval_mono hC (x := (oneEach i j).set k false) (y := oneEach i' j')
      (by simpa using hl) (oneEach_len i' j') (by
        intro u hu
        rw [read_set_false _ _ _ (by omega), oneEach_read] at hu
        by_cases he : u = k
        · simp [he] at hu
        · simp only [he, ite_false, decide_eq_true_eq] at hu
          rw [oneEach_read, decide_eq_true_eq]
          exact hkeep u he hu) h
    simp [hz] at hh

include oneEach_read oneEach_len read_set_false eval_mono deleteInput in
private theorem crossDropRow {r c n m : ℕ} {C : Circuit} (hC : Monotone2 C)
    (hn : 1 < n) (hm : 0 < m) (hr : n < r) (hc : m < c)
    (hrep : Represents (crossMatrix (r := r) (c := c) n m) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      Represents (crossMatrix (r := r) (c := c) (n-1) m) D := by
  let i0 : Fin r := ⟨0, by omega⟩
  let j0 : Fin c := ⟨0, by omega⟩
  let idrop : Fin r := ⟨n-1, by omega⟩
  let iblank : Fin r := ⟨n, hr⟩
  have hk : n-1 < r+c := by omega
  have hz (j : Fin c) : C.eval (oneEach iblank j) = false := by
    simpa [crossMatrix, iblank] using hrep iblank j
  have hon (j : Fin c) (i : Fin r) (hi : i.val = n-1) :
      C.eval ((oneEach i j).set (n-1) false) = false := by
    apply crossEraseFalse oneEach_read oneEach_len read_set_false eval_mono
      hC i j iblank j hk _ (hz j)
    intro u hu h
    omega
  have hone : C.eval (oneEach idrop j0) = true := by
    rw [hrep idrop j0, crossMatrix, decide_eq_true_eq]
    exact ⟨by dsimp [idrop]; omega, hm, Or.inr rfl⟩
  have hzero : C.eval ((oneEach i0 j0).set (n-1) false) = true := by
    rw [crossSetOther oneEach_read oneEach_len read_set_false i0 j0 hk
      (by dsimp [i0]; omega) (by dsimp [j0]; omega), hrep i0 j0, crossMatrix,
      decide_eq_true_eq]
    exact ⟨by dsimp [i0]; omega, hm, Or.inl rfl⟩
  obtain ⟨D, hD, hs, he⟩ := deleteInput hC hk
    ⟨oneEach idrop j0, oneEach_len idrop j0, by rw [hone, hon j0 idrop rfl]; decide⟩
    ⟨oneEach i0 j0, oneEach_len i0 j0, hzero⟩
  refine ⟨D, hD, hs, ?_⟩
  intro i j
  rw [he _ (oneEach_len i j)]
  by_cases hi : i.val = n-1
  · rw [hon j i hi]
    simp [crossMatrix, hi]
  · rw [crossSetOther oneEach_read oneEach_len read_set_false i j hk (Ne.symm hi)
      (by omega), hrep i j]
    unfold crossMatrix
    exact decide_eq_decide.mpr (by omega)

include oneEach_read oneEach_len read_set_false eval_mono deleteInput in
private theorem crossDropCol {r c n m : ℕ} {C : Circuit} (hC : Monotone2 C)
    (hn : 0 < n) (hm : 1 < m) (hr : n < r) (hc : m < c)
    (hrep : Represents (crossMatrix (r := r) (c := c) n m) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      Represents (crossMatrix (r := r) (c := c) n (m-1)) D := by
  let i0 : Fin r := ⟨0, by omega⟩
  let j0 : Fin c := ⟨0, by omega⟩
  let jdrop : Fin c := ⟨m-1, by omega⟩
  let jblank : Fin c := ⟨m, hc⟩
  have hk : r+(m-1) < r+c := by omega
  have hz (i : Fin r) : C.eval (oneEach i jblank) = false := by
    simpa [crossMatrix, jblank] using hrep i jblank
  have hon (i : Fin r) (j : Fin c) (hj : j.val = m-1) :
      C.eval ((oneEach i j).set (r+(m-1)) false) = false := by
    apply crossEraseFalse oneEach_read oneEach_len read_set_false eval_mono
      hC i j i jblank hk _ (hz i)
    intro u hu h
    omega
  have hone : C.eval (oneEach i0 jdrop) = true := by
    rw [hrep i0 jdrop, crossMatrix, decide_eq_true_eq]
    exact ⟨hn, by dsimp [jdrop]; omega, Or.inl rfl⟩
  have hzero : C.eval ((oneEach i0 j0).set (r+(m-1)) false) = true := by
    rw [crossSetOther oneEach_read oneEach_len read_set_false i0 j0 hk
      (by dsimp [i0]; omega) (by dsimp [j0]; omega), hrep i0 j0, crossMatrix,
      decide_eq_true_eq]
    exact ⟨hn, by dsimp [j0]; omega, Or.inr rfl⟩
  obtain ⟨D, hD, hs, he⟩ := deleteInput hC hk
    ⟨oneEach i0 jdrop, oneEach_len i0 jdrop, by rw [hone, hon i0 jdrop rfl]; decide⟩
    ⟨oneEach i0 j0, oneEach_len i0 j0, hzero⟩
  refine ⟨D, hD, hs, ?_⟩
  intro i j
  rw [he _ (oneEach_len i j)]
  by_cases hj : j.val = m-1
  · rw [hon i j hj]
    simp [crossMatrix, hj]
  · have hi := i.isLt
    rw [crossSetOther oneEach_read oneEach_len read_set_false i j hk
      (by omega) (by omega), hrep i j]
    unfold crossMatrix
    exact decide_eq_decide.mpr (by omega)

include oneEach_read in
private theorem crossNoRaw {r c : ℕ} {C : Circuit}
    (i₀ i₁ : Fin r) (j₀ j₁ : Fin c)
    (ht : C.eval (oneEach i₀ j₀) = true)
    (hrow : C.eval (oneEach i₀ j₁) = false)
    (hcol : C.eval (oneEach i₁ j₀) = false) : 1 ≤ C.size := by
  by_contra h
  have hg : C.gates = [] := by
    apply List.length_eq_zero_iff.mp
    unfold Circuit.size at h
    omega
  simp only [Circuit.eval, Circuit.wires, hg, List.foldl_nil, oneEach_read,
    decide_eq_true_eq, decide_eq_false_iff_not] at ht hrow hcol
  omega

include oneEach_read in
private theorem crossSingletonFloor {r c : ℕ} {C : Circuit} (hr : 1 < r) (hc : 1 < c)
    (hrep : Represents (crossMatrix (r := r) (c := c) 1 1) C) : 1 ≤ C.size := by
  apply crossNoRaw oneEach_read ⟨0, by omega⟩ ⟨1, hr⟩ ⟨0, by omega⟩ ⟨1, hc⟩
  all_goals rw [hrep]; rfl

include oneEach_read in
private theorem unpaddedCrossLower {n m s : ℕ} (hn : 1 < n) (hm : 1 < m)
    (h : RepSizeAtMost (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)) s) :
    1 ≤ s := by
  obtain ⟨C, _, hs, hrep⟩ := h
  have hh : 1 ≤ C.size := by
    by_contra hzero
    have hg : C.gates = [] := by
      apply List.length_eq_zero_iff.mp
      unfold Circuit.size at hzero
      omega
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, hn⟩
    let j0 : Fin m := ⟨0, by omega⟩
    let j1 : Fin m := ⟨1, hm⟩
    have h01 := hrep i0 j1
    have h10 := hrep i1 j0
    have h11 := hrep i1 j1
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl_nil, oneEach_read,
      i0, i1, j0, j1, Nat.add_zero] at h01 h10 h11
    simp at h01 h10 h11
    omega
  omega

include oneEach_read oneEach_len pullCircuit pull_mono pull_size pull_eval smallFloor in
private theorem crossTwoFloor {r c : ℕ} {C : Circuit} (hr : 2 < r) (hc : 2 < c)
    (hC : Monotone2 C)
    (hrep : Represents (crossMatrix (r := r) (c := c) 2 2) C) : 4 ≤ C.size := by
  let f : Fin (r+c) → Option (Fin (3+3)) := fun u =>
    if hu : u.val < 3 then some ⟨u.val, by omega⟩
    else if hv : r ≤ u.val ∧ u.val < r+3 then some ⟨3+(u.val-r), by omega⟩
    else none
  rw [← pull_size f C]
  apply smallFloor _ (pull_mono f hC)
  intro i j
  let i' : Fin r := ⟨i.val, by have := i.isLt; omega⟩
  let j' : Fin c := ⟨j.val, by have := j.isLt; omega⟩
  have he : (List.ofFn fun u => (f u).elim false fun v =>
      (oneEach i j).getD v.val false) = oneEach i' j' := by
    apply List.ext_getElem (by simp [oneEach_len])
    intro u hu hv
    have h₁ := i.isLt
    have h₂ := j.isLt
    rw [List.getElem_ofFn]
    have hh := oneEach_read i' j' u
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some] at hh
    rw [hh]
    dsimp [f, i', j']
    split
    · simp only [Option.elim_some, oneEach_read]
      exact decide_eq_decide.mpr (by omega)
    · split
      · simp only [Option.elim_some, oneEach_read]
        exact decide_eq_decide.mpr (by omega)
      · change false = decide (_ ∨ _)
        symm
        rw [decide_eq_false_iff_not]
        omega
  rw [pull_eval f C _ (oneEach_len i j), he, hrep i' j']
  rfl

include oneEach_read oneEach_len read_set_false eval_mono deleteInput
  pullCircuit pull_mono pull_size pull_eval smallFloor in
private theorem crossActiveLower {r c n m : ℕ} {C : Circuit}
    (hn : 0 < n) (hm : 0 < m) (hr : n < r) (hc : m < c) (hC : Monotone2 C)
    (hrep : Represents (crossMatrix (r := r) (c := c) n m) C) :
    (if n = 1 ∨ m = 1 then 0 else 1) + (n+m-1) ≤ C.size := by
  generalize he : n+m = total
  induction total using Nat.strong_induction_on generalizing n m C with
  | ind total ih =>
    rw [← he]
    by_cases hrow : n = 1
    · subst n
      by_cases hcol : m = 1
      · subst m
        simpa using crossSingletonFloor oneEach_read hr hc hrep
      · obtain ⟨D, hD, hs, hDr⟩ := crossDropCol oneEach_read oneEach_len read_set_false
          eval_mono deleteInput hC hn (by omega) hr hc hrep
        have hb := @ih (1+(m-1)) (by omega) 1 (m-1) D
          hn (by omega) hr (by omega) hD hDr rfl
        simp at hb ⊢
        omega
    · by_cases hcol : m = 1
      · subst m
        obtain ⟨D, hD, hs, hDr⟩ := crossDropRow oneEach_read oneEach_len read_set_false
          eval_mono deleteInput hC (by omega) hm hr hc hrep
        have hb := @ih ((n-1)+1) (by omega) (n-1) 1 D
          (by omega) hm (by omega) hc hD hDr rfl
        simp at hb ⊢
        omega
      · by_cases hlarge : 2 < n
        · obtain ⟨D, hD, hs, hDr⟩ := crossDropRow oneEach_read oneEach_len read_set_false
            eval_mono deleteInput hC (by omega) hm hr hc hrep
          have hb := @ih ((n-1)+m) (by omega) (n-1) m D
            (by omega) hm (by omega) hc hD hDr rfl
          have hne : n-1 ≠ 1 := by omega
          simp [hrow, hcol, hne] at hb ⊢
          omega
        · by_cases hlarge' : 2 < m
          · obtain ⟨D, hD, hs, hDr⟩ := crossDropCol oneEach_read oneEach_len read_set_false
              eval_mono deleteInput hC hn (by omega) hr hc hrep
            have hb := @ih (n+(m-1)) (by omega) n (m-1) D
              hn (by omega) hr (by omega) hD hDr rfl
            have hne : m-1 ≠ 1 := by omega
            simp [hrow, hcol, hne] at hb ⊢
            omega
          · have hn' : n = 2 := by omega
            have hm' : m = 2 := by omega
            subst n
            subst m
            simpa using crossTwoFloor oneEach_read oneEach_len pullCircuit pull_mono
              pull_size pull_eval smallFloor hr hc hC hrep

include oneEach_read oneEach_len read_set_false eval_mono deleteInput
  pullCircuit pull_mono pull_size pull_eval smallFloor in
private theorem paddedCrossLower {n m p q s : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hp : 0 < p) (hq : 0 < q)
    (h : RepSizeAtMost (fun (i : Fin (n+p)) (j : Fin (m+q)) =>
      decide (i.val < n ∧ j.val < m ∧ (i.val = 0 ∨ j.val = 0))) s) :
    (if n = 1 ∨ m = 1 then 0 else 1) + (n+m-1) ≤ s := by
  obtain ⟨C, hC, hs, hrep⟩ := h
  exact (crossActiveLower oneEach_read oneEach_len read_set_false eval_mono deleteInput
    pullCircuit pull_mono pull_size pull_eval smallFloor hn hm (by omega) (by omega)
    hC hrep).trans hs

end CrossBounds

private def bits (N : ℕ) (S : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide (i.val ∈ S)

private theorem bits_len (N : ℕ) (S : Finset ℕ) : (bits N S).length = N := by simp [bits]

private theorem bits_read {N : ℕ} {S : Finset ℕ} (hS : ∀ k ∈ S, k < N) (k : ℕ) :
    (bits N S).getD k false = decide (k ∈ S) := by
  by_cases hk : k < N
  · exact ofFn_getD _ _ hk
  · rw [getD_ge _ _ (by rw [bits_len]; omega)]
    exact (decide_eq_false (fun h => hk (hS k h))).symm

private theorem reads_ext (x y : List Bool) (hxy : x.length = y.length)
    (h : ∀ k, x.getD k false = y.getD k false) : x = y := by
  apply List.ext_getElem hxy
  intro k hx hy
  simpa [List.getD_eq_getElem, hx, hy] using h k

private def mask (x : List Bool) (T : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin x.length => if i.val ∈ T then false else x.getD i.val false

private theorem mask_len (x : List Bool) (T : Finset ℕ) : (mask x T).length = x.length := by simp [mask]

private theorem mask_read (x : List Bool) (T : Finset ℕ) (k : ℕ) :
    (mask x T).getD k false = if k ∈ T then false else x.getD k false := by
  by_cases hk : k < x.length
  · exact ofFn_getD _ _ hk
  · rw [show mask x T = List.ofFn _ from rfl, ofFn_getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    split <;> rfl

private def place {n m p q : ℕ} (k : Fin (n+m)) : Fin ((n+p)+(m+q)) :=
  if h : k.val < n then ⟨k.val, by omega⟩ else ⟨n+p+(k.val-n), by have := k.isLt; omega⟩

private def paddedInput (n m : ℕ) {p q : ℕ} (i : Fin (n+p)) (j : Fin (m+q)) : List Bool :=
  bits (n+m) ((if i.val < n then {i.val} else ∅) ∪ (if j.val < m then {n+j.val} else ∅))

private theorem padded_len (n m : ℕ) {p q : ℕ} (i : Fin (n+p)) (j : Fin (m+q)) :
    (paddedInput n m i j).length = n+m := bits_len _ _

private theorem padded_read (n m : ℕ) {p q : ℕ} (i : Fin (n+p)) (j : Fin (m+q)) (k : ℕ) :
    (paddedInput n m i j).getD k false =
      decide ((i.val < n ∧ k = i.val) ∨ (j.val < m ∧ k = n+j.val)) := by
  rw [paddedInput, bits_read]
  · by_cases hi : i.val < n <;> by_cases hj : j.val < m <;> simp [hi, hj]
  · intro w hw
    by_cases hi : i.val < n <;> by_cases hj : j.val < m <;> simp [hi, hj] at hw <;> omega

private theorem padded_original (n m : ℕ) {p q : ℕ} (i : Fin (n+p)) (j : Fin (m+q))
    (hi : i.val < n) (hj : j.val < m) : paddedInput n m i j = oneEach (⟨i.val,hi⟩ : Fin n) (⟨j.val,hj⟩ : Fin m) := by
  apply reads_ext _ _ (by simp [padded_len, oneEach_len])
  intro k
  rw [padded_read, oneEach_read]
  simp [hi, hj]

private theorem pull_padded {n m p q : ℕ} (T : Finset ℕ) (C : Circuit)
    (i : Fin (n+p)) (j : Fin (m+q)) :
    (pullCircuit (fun k : Fin (n+m) => if k.val ∈ T then none else some (place (p := p) (q := q) k)) C).eval
        (oneEach i j) = C.eval (mask (paddedInput n m i j) T) := by
  rw [pull_eval _ _ _ (oneEach_len i j)]
  congr 1
  apply reads_ext _ _ (by simp [mask_len, padded_len])
  intro k
  by_cases hk : k < n+m
  · rw [ofFn_getD _ _ hk, mask_read]
    by_cases hT : k ∈ T
    · simp [hT]
    · simp only [hT, if_false, Option.elim, padded_read, oneEach_read]
      have hi := i.isLt
      have hj := j.isLt
      by_cases hn : k < n
      · simp only [place, hn, dite_true]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      · simp only [place, hn, dite_false]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
  · rw [ofFn_getD_ge _ _ (by omega), getD_ge _ _ (by rw [mask_len, padded_len]; omega)]

private def group (N : ℕ) (C : Circuit) (l : List ℕ) : Circuit :=
  orFrom N C (l.headD 0) l.tail

private theorem group_size (N : ℕ) (C : Circuit) (l : List ℕ) :
    (group N C l).size = C.size + (l.length-1) := by simp [group, orFrom_size]

private theorem group_mono {N : ℕ} {C : Circuit} (l : List ℕ) (hC : Monotone2 C) :
    Monotone2 (group N C l) := orFrom_mono _ _ hC

private theorem group_preserve {N : ℕ} (C : Circuit) (l : List ℕ) (x : List Bool)
    (hx : x.length = N) (u : ℕ) (hu : u < N+C.size) : val (group N C l) x u = val C x u :=
  orFrom_preserve C _ _ x hx u hu

private theorem group_valid {N : ℕ} (C : Circuit) (l : List ℕ) (hn : l ≠ [])
    (hl : ∀ k ∈ l, k < N) : (group N C l).output < N+(group N C l).size := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons v l =>
    apply orFrom_bound
    change v < N+C.size
    have := hl v (by simp)
    omega

private theorem group_eval {N : ℕ} (C : Circuit) (l : List ℕ) (hn : l ≠ [])
    (hl : ∀ k ∈ l, k < N) (x : List Bool) (hx : x.length = N) :
    (group N C l).eval x = l.any (fun k => x.getD k false) := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons v l =>
    change (orFrom N C v l).eval x = _
    rw [orFrom_read C v l x hx (fun k hk => hl k (by simp [hk])), val_input hx (hl v (by simp))]
    rfl

private noncomputable def names {d : ℕ} (offset : ℕ) (S : Finset (Fin d)) : List ℕ :=
  S.toList.map fun i => offset+i.val

private theorem names_len {d : ℕ} (offset : ℕ) (S : Finset (Fin d)) :
    (names offset S).length = S.card := by simp [names]

private theorem names_ne {d : ℕ} (offset : ℕ) {S : Finset (Fin d)} (h : S.Nonempty) : names offset S ≠ [] := by
  intro he
  have h1 := names_len offset S
  rw [he] at h1
  exact (Nat.ne_of_gt (Finset.card_pos.mpr h)) h1.symm

private theorem names_bound {d : ℕ} (offset : ℕ) (S : Finset (Fin d)) (k : ℕ) (hk : k ∈ names offset S) :
    k < offset+d := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
  have := i.isLt
  omega

private theorem names_rows {n m p q : ℕ} (S : Finset (Fin n)) (i : Fin (n+p)) (j : Fin (m+q)) :
    (names 0 S).any (fun k => (oneEach i j).getD k false) =
      decide (∃ a ∈ S, a.val = i.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, names, List.mem_map, Finset.mem_toList, oneEach_read, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hh⟩
    refine ⟨a, ha, ?_⟩
    have := a.isLt
    omega
  · rintro ⟨a, ha, h⟩
    exact ⟨0+a.val, ⟨a, ha, rfl⟩, Or.inl (by simpa using h)⟩

private theorem names_cols {n m p q : ℕ} (S : Finset (Fin m)) (i : Fin (n+p)) (j : Fin (m+q)) :
    (names (n+p) S).any (fun k => (oneEach i j).getD k false) =
      decide (∃ a ∈ S, a.val = j.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, names, List.mem_map, Finset.mem_toList, oneEach_read, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hh⟩
    refine ⟨a, ha, ?_⟩
    have := i.isLt
    omega
  · rintro ⟨a, ha, h⟩
    exact ⟨n+p+a.val, ⟨a, ha, rfl⟩, Or.inr (by rw [h])⟩

private theorem add_eval {N : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool)
    (hx : x.length = N) : (addGate N C op a b).eval x = op.eval [val C x a, val C x b] := by
  exact add_read C op a b x hx

private theorem add_valid (N : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate N C op a b).output < N+(addGate N C op a b).size := by
  rw [add_size]
  change N+C.size < N+(C.size+1)
  omega

private def rectangle (N : ℕ) (C : Circuit) (L R : List ℕ) : Circuit :=
  let C₁ := group N C L
  let C₂ := group N C₁ R
  addGate N C₂ .and C₁.output C₂.output

private theorem rect_size (N : ℕ) (C : Circuit) (L R : List ℕ) :
    (rectangle N C L R).size = C.size+(L.length-1)+(R.length-1)+1 := by
  simp only [rectangle, add_size, group_size]

private theorem rect_mono {N : ℕ} {C : Circuit} (L R : List ℕ) (h : Monotone2 C) :
    Monotone2 (rectangle N C L R) := by
  exact add_mono _ _ (group_mono _ (group_mono _ h)) _ (Or.inl rfl)

private theorem rect_valid (N : ℕ) (C : Circuit) (L R : List ℕ) :
    (rectangle N C L R).output < N+(rectangle N C L R).size := add_valid _ _ _ _ _

private theorem rect_preserve {N : ℕ} (C : Circuit) (L R : List ℕ) (x : List Bool)
    (hx : x.length = N) (k : ℕ) (hk : k < N+C.size) : val (rectangle N C L R) x k = val C x k := by
  unfold rectangle
  have h₁ : k < N+(group N C L).size := by rw [group_size]; omega
  have h₂ : k < N+(group N (group N C L) R).size := by simp only [group_size]; omega
  rw [add_preserve _ _ _ _ _ hx _ h₂, group_preserve _ _ _ hx _ h₁, group_preserve _ _ _ hx _ hk]

private theorem rect_eval {N : ℕ} (C : Circuit) (L R : List ℕ) (hL : L ≠ []) (hR : R ≠ [])
    (hLb : ∀ k ∈ L, k < N) (hRb : ∀ k ∈ R, k < N) (x : List Bool) (hx : x.length = N) :
    (rectangle N C L R).eval x = (L.any (fun k => x.getD k false) && R.any (fun k => x.getD k false)) := by
  unfold rectangle
  dsimp only
  rw [add_eval _ _ _ _ _ hx, eval_and2, group_preserve _ _ _ hx _ (group_valid C L hL hLb),
    ← eval_eq_val, ← eval_eq_val, group_eval C L hL hLb x hx,
    group_eval (group N C L) R hR hRb x hx]

private def padded {n m : ℕ} (p q : ℕ) (A : Fin n → Fin m → Bool) (i : Fin (n+p)) (j : Fin (m+q)) : Bool :=
  if hi : i.val < n then if hj : j.val < m then A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else false else false

private def fullRows {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j, A i j = true

private theorem mem_fullRows {n m : ℕ} {A : Fin n → Fin m → Bool} {i : Fin n} :
    i ∈ fullRows A ↔ ∀ j, A i j = true := by simp [fullRows]

private theorem exists_name_iff {d large : ℕ} (S : Finset (Fin d)) (i : Fin large) :
    (∃ a ∈ S, a.val = i.val) ↔ ∃ h : i.val < d, (⟨i.val,h⟩ : Fin d) ∈ S := by
  constructor
  · rintro ⟨a, ha, he⟩
    have h : i.val < d := he ▸ a.isLt
    refine ⟨h, ?_⟩
    simpa only [show a = (⟨i.val,h⟩ : Fin d) from Fin.ext he] using ha
  · rintro ⟨h, hm⟩
    exact ⟨_, hm, rfl⟩

private theorem names_all {d large : ℕ} (i : Fin large) :
    (∃ a ∈ (Finset.univ : Finset (Fin d)), a.val = i.val) ↔ i.val < d := by
  rw [exists_name_iff]
  exact ⟨fun ⟨h,_⟩ => h, fun h => ⟨h, Finset.mem_univ _⟩⟩

private theorem no_name {d large : ℕ} (S : Finset (Fin d)) (u : Fin large) (hu : ¬ u.val < d) :
    ¬ ∃ a ∈ S, a.val = u.val := fun h => hu ((exists_name_iff S u).mp h |>.choose)

private theorem no_edge_row {n m p q : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hC : Monotone2 C) (hrep : Represents A C) (i : Fin (n+p)) (j : Fin (m+q))
    (hi : ¬ i.val < n) (hv : ∀ v : Fin m, ∃ u : Fin n, A u v = false)
    (u₀ : Fin n) (v₀ : Fin m) (h₀ : A u₀ v₀ = false) : C.eval (paddedInput n m i j) = false := by
  by_contra h
  have hp : C.eval (paddedInput n m i j) = true := by simpa using h
  by_cases hj : j.val < m
  · obtain ⟨u, hu⟩ := hv ⟨j.val,hj⟩
    have ht := eval_mono hC (padded_len n m i j) (oneEach_len u ⟨j.val,hj⟩)
      (fun k hk => by
        rw [padded_read] at hk
        have hh : k = n+j.val := by simpa [hi, hj] using hk
        rw [oneEach_read]
        exact decide_eq_true (Or.inr hh)) hp
    rw [hrep, hu] at ht
    contradiction
  · have ht := eval_mono hC (padded_len n m i j) (oneEach_len u₀ v₀)
      (fun k hk => by rw [padded_read] at hk; simp [hi, hj] at hk) hp
    rw [hrep, h₀] at ht
    contradiction

private theorem no_edge_col {n m p q : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hC : Monotone2 C) (hrep : Represents A C) (i : Fin (n+p)) (j : Fin (m+q))
    (hj : ¬ j.val < m) (hv : ∀ u : Fin n, ∃ v : Fin m, A u v = false)
    (u₀ : Fin n) (v₀ : Fin m) (h₀ : A u₀ v₀ = false) : C.eval (paddedInput n m i j) = false := by
  by_contra h
  have hp : C.eval (paddedInput n m i j) = true := by simpa using h
  by_cases hi : i.val < n
  · obtain ⟨v, hv'⟩ := hv ⟨i.val,hi⟩
    have ht := eval_mono hC (padded_len n m i j) (oneEach_len ⟨i.val,hi⟩ v)
      (fun k hk => by
        rw [padded_read] at hk
        have hh : k = i.val := by simpa [hi, hj] using hk
        rw [oneEach_read]
        exact decide_eq_true (Or.inl hh)) hp
    rw [hrep, hv'] at ht
    contradiction
  · have ht := eval_mono hC (padded_len n m i j) (oneEach_len u₀ v₀)
      (fun k hk => by rw [padded_read] at hk; simp [hi, hj] at hk) hp
    rw [hrep, h₀] at ht
    contradiction

private def guarded (N : ℕ) (C : Circuit) (L : List ℕ) : Circuit :=
  let G := group N C L
  addGate N G .and C.output G.output

private theorem guarded_size (N : ℕ) (C : Circuit) (L : List ℕ) :
    (guarded N C L).size = C.size+(L.length-1)+1 := by simp [guarded, group_size, add_size]

private theorem guarded_mono {N : ℕ} {C : Circuit} (L : List ℕ) (h : Monotone2 C) :
    Monotone2 (guarded N C L) := add_mono _ _ (group_mono _ h) _ (Or.inl rfl)

private theorem guarded_eval {N : ℕ} (C : Circuit) (L : List ℕ) (hL : L ≠ []) (hB : ∀ k ∈ L, k < N)
    (x : List Bool) (hx : x.length = N) (ho : C.output < N+C.size) :
    (guarded N C L).eval x = (C.eval x && L.any (fun k => x.getD k false)) := by
  unfold guarded
  dsimp only
  rw [add_eval _ _ _ _ _ hx, eval_and2, group_preserve _ _ _ hx _ ho,
    ← eval_eq_val, ← eval_eq_val, group_eval C L hL hB x hx]

private def joined (N : ℕ) (C : Circuit) (L R T : List ℕ) : Circuit :=
  let rect := rectangle N C L R
  let g := group N rect T
  let inter := addGate N g .and C.output g.output
  addGate N inter .or rect.output inter.output

private theorem joined_size (N : ℕ) (C : Circuit) (L R T : List ℕ) :
    (joined N C L R T).size = C.size + (L.length-1)+(R.length-1)+1 + (T.length-1)+2 := by
  simp only [joined, add_size, group_size, rect_size]

private theorem joined_mono {N : ℕ} {C : Circuit} (L R T : List ℕ) (h : Monotone2 C) :
    Monotone2 (joined N C L R T) := by
  exact add_mono _ _ (add_mono _ _ (group_mono _ (rect_mono L R h)) _ (Or.inl rfl)) _ (Or.inr rfl)

private theorem joined_eval {N : ℕ} (C : Circuit) (L R T : List ℕ) (hL : L ≠ []) (hR : R ≠ []) (hT : T ≠ [])
    (hLb : ∀ k ∈ L, k < N) (hRb : ∀ k ∈ R, k < N) (hTb : ∀ k ∈ T, k < N)
    (x : List Bool) (hx : x.length = N) (ho : C.output < N+C.size) :
    (joined N C L R T).eval x =
      ((L.any (fun k => x.getD k false) && R.any (fun k => x.getD k false)) ||
        (C.eval x && T.any (fun k => x.getD k false))) := by
  let rect := rectangle N C L R
  let g := group N rect T
  let inter := addGate N g .and C.output g.output
  change (addGate N inter .or rect.output inter.output).eval x = _
  have hrec : rect.output < N+rect.size := rect_valid _ _ _ _
  have hg : rect.output < N+g.size := by dsimp [g]; rw [group_size]; omega
  have hc : C.output < N+rect.size := by dsimp [rect]; rw [rect_size]; omega
  rw [add_eval _ _ _ _ _ hx, eval_or2,
    show val inter x rect.output = val g x rect.output from add_preserve _ _ _ _ _ hx _ hg,
    group_preserve _ _ _ hx _ hrec, ← eval_eq_val,
    show rect.eval x = _ from rect_eval C L R hL hR hLb hRb x hx, ← eval_eq_val]
  rw [show inter.eval x = _ from add_eval g .and C.output g.output x hx, eval_and2,
    group_preserve _ _ _ hx _ hc, rect_preserve _ _ _ _ hx _ ho, ← eval_eq_val,
    ← eval_eq_val, group_eval rect T hT hTb x hx]

private theorem mask_nil (x : List Bool) : mask x ∅ = x := by
  apply reads_ext _ _ (mask_len x ∅)
  intro k
  rw [mask_read]
  simp

private theorem set_irrelevant (x : List Bool) (k : ℕ) (hk : k < x.length)
    (hr : x.getD k false = false) : x.set k false = x := by
  apply reads_ext _ _ (by simp)
  intro w
  rw [read_set_false x k w hk]
  by_cases he : w = k
  · subst w
    rw [ite_eq_left rfl, hr]
  · rw [ite_eq_right he]

-- A blank side contributes no input bit. A false cell dominates the remaining
-- input whenever its selected line is not full.
private theorem padding_upper {n m p q s : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Fin n → Fin m → Bool) (hA : RepSizeAtMost A s) : RepSizeAtMost (padded p q A) (s+(n+m-1)) := by
  classical
  obtain ⟨C, hC, hsize, hrep⟩ := hA
  let N := (n+p)+(m+q)
  let allL := names 0 (Finset.univ : Finset (Fin n))
  let allR := names (n+p) (Finset.univ : Finset (Fin m))
  have hL : allL ≠ [] := names_ne 0 ⟨⟨0,hn⟩, Finset.mem_univ _⟩
  have hR : allR ≠ [] := names_ne (n+p) ⟨⟨0,hm⟩, Finset.mem_univ _⟩
  have hLb : ∀ k ∈ allL, k < N := fun k hk => by have := names_bound _ _ k hk; dsimp [N]; omega
  have hRb : ∀ k ∈ allR, k < N := fun k hk => by have := names_bound _ _ k hk; dsimp [N]; omega
  have hl : allL.length = n := by simp [allL, names_len]
  have hr : allR.length = m := by simp [allR, names_len]
  have left (i : Fin (n+p)) (j : Fin (m+q)) :
      allL.any (fun k => (oneEach i j).getD k false) = decide (i.val < n) := by
    rw [names_rows]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using names_all i)
  have right (i : Fin (n+p)) (j : Fin (m+q)) :
      allR.any (fun k => (oneEach i j).getD k false) = decide (j.val < m) := by
    rw [names_cols]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using names_all j)
  by_cases hzero : ∀ i j, A i j = false
  · refine ⟨wire N, wire_mono _, by simp [wire_size], ?_⟩
    intro i j
    rw [eval_eq_val]
    change val (wire N) (oneEach i j) N = _
    rw [wire_read, getD_ge _ _ (by simp [N, oneEach_len])]
    by_cases hi : i.val < n <;> by_cases hj : j.val < m <;> simp [padded, hi, hj, hzero]
  push_neg at hzero
  obtain ⟨u₁,v₁,h₁⟩ := hzero
  have hpos : A u₁ v₁ = true := by simpa using h₁
  by_cases hone : ∀ i j, A i j = true
  · refine ⟨rectangle N (wire 0) allL allR, rect_mono _ _ (wire_mono _), ?_, ?_⟩
    · rw [rect_size, wire_size, hl, hr]; omega
    · intro i j
      rw [rect_eval _ _ _ hL hR hLb hRb _ (oneEach_len i j), left, right]
      by_cases hi : i.val < n <;> by_cases hj : j.val < m <;> simp [padded, hi, hj, hone]
  push_neg at hone
  obtain ⟨u₀,v₀,h₀⟩ := hone
  have hneg : A u₀ v₀ = false := by simpa using h₀
  let embed := fun k : Fin (n+m) => some (place (p := p) (q := q) k)
  let G := pullCircuit embed C
  have eg (i : Fin (n+p)) (j : Fin (m+q)) : G.eval (oneEach i j) = C.eval (paddedInput n m i j) := by
    simpa only [Finset.notMem_empty, if_false, mask_nil] using pull_padded (∅ : Finset ℕ) C i j
  have hg : Monotone2 G := pull_mono _ hC
  have hgs : G.size = C.size := pull_size _ _
  have hgo : G.output < N+G.size := by
    let u : Fin (n+p) := ⟨u₁.val, by have := u₁.isLt; omega⟩
    let v : Fin (m+q) := ⟨v₁.val, by have := v₁.isLt; omega⟩
    apply output_valid G (oneEach u v) (oneEach_len u v)
    rw [eg, padded_original _ _ _ _ (by exact u₁.isLt) (by exact v₁.isLt), hrep]
    exact hpos
  by_cases hcol : ∀ v : Fin m, ∃ u : Fin n, A u v = false
  · refine ⟨guarded N G allR, guarded_mono _ hg, ?_, ?_⟩
    · rw [guarded_size, hgs, hr]; omega
    · intro i j
      rw [guarded_eval _ _ hR hRb _ (oneEach_len i j) hgo, eg, right]
      by_cases hj : j.val < m
      · by_cases hi : i.val < n
        · rw [padded_original _ _ _ _ hi hj, hrep]; simp [padded, hi, hj]
        · rw [no_edge_row hC hrep i j hi hcol u₀ v₀ hneg]; simp [padded, hi]
      · by_cases hi : i.val < n <;> simp [padded, hi, hj]
  by_cases hrow : ∀ u : Fin n, ∃ v : Fin m, A u v = false
  · refine ⟨guarded N G allL, guarded_mono _ hg, ?_, ?_⟩
    · rw [guarded_size, hgs, hl]; omega
    · intro i j
      rw [guarded_eval _ _ hL hLb _ (oneEach_len i j) hgo, eg, left]
      by_cases hi : i.val < n
      · by_cases hj : j.val < m
        · rw [padded_original _ _ _ _ hi hj, hrep]; simp [padded, hi, hj]
        · rw [no_edge_col hC hrep i j hj hrow u₀ v₀ hneg]; simp [padded, hi, hj]
      · simp [padded, hi]
  push_neg at hcol hrow
  obtain ⟨vF,hvF'⟩ := hcol
  obtain ⟨uF,huF'⟩ := hrow
  have hvF (u : Fin n) : A u vF = true := by simpa using hvF' u
  -- Both sides have full lines, but a false cell leaves a nonfull row and column.
  -- Clear one essential full-row bit to pay for the two-branch construction.
  have huF (v : Fin m) : A uF v = true := by simpa using huF' v
  have hfne : uF.val ≠ u₀.val := by
    intro h
    have h' := huF v₀
    rw [Fin.ext h, hneg] at h'
    contradiction
  have hcut : uF.val < n+m := by have := uF.isLt; omega
  have hdep : ∃ x : List Bool, x.length = n+m ∧ C.eval x ≠ C.eval (x.set uF.val false) := by
    refine ⟨oneEach uF v₀, oneEach_len _ _, ?_⟩
    rw [hrep, huF]
    intro h
    have he := eval_mono hC (show ((oneEach uF v₀).set uF.val false).length = n+m by simp [oneEach_len])
      (oneEach_len u₀ v₀) (fun k hk => by
        rw [read_set_false _ _ _ (by simpa [oneEach_len] using hcut)] at hk
        by_cases hk' : k = uF.val
        · simp [hk'] at hk
        · rw [ite_eq_right hk', oneEach_read, decide_eq_true_eq] at hk
          rw [oneEach_read]
          exact decide_eq_true (Or.inr (hk.resolve_left hk'))) h.symm
    rw [hrep, hneg] at he
    contradiction
  have hstay : (oneEach u₀ vF).set uF.val false = oneEach u₀ vF := by
    apply set_irrelevant _ _ (by simpa [oneEach_len] using hcut)
    rw [oneEach_read]
    apply decide_eq_false
    have := uF.isLt
    omega
  obtain ⟨D, hD, hDsz, hDe⟩ := deleteInput hC hcut hdep
    ⟨oneEach u₀ vF, oneEach_len _ _, by rw [hstay, hrep, hvF]⟩
  let F := fullRows A
  let B := F.image Fin.val
  have hFu : uF ∈ F := mem_fullRows.mpr huF
  have hnFu : u₀ ∈ Fᶜ := by
    simp only [Finset.mem_compl, F, mem_fullRows]
    intro h
    exact Bool.false_ne_true (hneg ▸ h v₀)
  have hf (k : ℕ) : k ∈ B ↔ ∃ a ∈ F, a.val = k := Finset.mem_image
  have hfcut : uF.val ∈ B := (hf _).mpr ⟨uF,hFu,rfl⟩
  let E := pullCircuit (fun k : Fin (n+m) => if k.val ∈ B then none else some (place (p := p) (q := q) k)) D
  have hEval (i : Fin (n+p)) (j : Fin (m+q)) : E.eval (oneEach i j) = C.eval (mask (paddedInput n m i j) B) := by
    rw [pull_padded, hDe _ (by simp [mask_len, padded_len])]
    rw [set_irrelevant _ _ (by simpa [mask_len, padded_len] using hcut)
      (by rw [mask_read, ite_eq_left hfcut])]
  have hE : Monotone2 E := pull_mono _ hD
  have hEs : E.size = D.size := pull_size _ _
  have sameInput (i : Fin (n+p)) (j : Fin (m+q)) (hi : i.val < n)
      (hnF : ¬ (⟨i.val, hi⟩ : Fin n) ∈ F) : mask (paddedInput n m i j) B = paddedInput n m i j := by
    have hnBi : i.val ∉ B := by
      rw [hf, exists_name_iff]
      rintro ⟨_, h⟩
      exact hnF h
    apply reads_ext _ _ (mask_len _ _)
    intro k
    rw [mask_read]
    by_cases hkb : k ∈ B
    · obtain ⟨a,_,he⟩ := (hf _).mp hkb
      simp only [hkb, if_true, padded_read]
      symm
      apply decide_eq_false
      have ha := a.isLt
      intro h
      rcases h with h | h
      · exact hnBi (h.2 ▸ hkb)
      · omega
    · simp [hkb]
  have hEo : E.output < N+E.size := by
    let u : Fin (n+p) := ⟨u₀.val, by have := u₀.isLt; omega⟩
    let v : Fin (m+q) := ⟨vF.val, by have := vF.isLt; omega⟩
    have hnF : u₀ ∉ F := Finset.mem_compl.mp hnFu
    apply output_valid E (oneEach u v) (oneEach_len u v)
    rw [hEval, sameInput _ _ (by exact u₀.isLt) hnF,
      padded_original _ _ _ _ (by exact u₀.isLt) (by exact vF.isLt), hrep]
    exact hvF u₀
  let fullL := names 0 F
  let nonL := names 0 Fᶜ
  have hfull : fullL ≠ [] := names_ne _ ⟨uF,hFu⟩
  have hnon : nonL ≠ [] := names_ne _ ⟨u₀,hnFu⟩
  have hfullb : ∀ k ∈ fullL, k < N := fun k hk => by have := names_bound _ _ k hk; dsimp [N]; omega
  have hnonb : ∀ k ∈ nonL, k < N := fun k hk => by have := names_bound _ _ k hk; dsimp [N]; omega
  have hcard : fullL.length+nonL.length = n := by
    simp only [fullL, nonL, names_len, Finset.card_add_card_compl, Fintype.card_fin]
  have hfullp : 0 < fullL.length := List.length_pos_iff.mpr hfull
  have hnonp : 0 < nonL.length := List.length_pos_iff.mpr hnon
  refine ⟨joined N E fullL allR nonL, joined_mono _ _ _ hE, ?_, ?_⟩
  · rw [joined_size, hEs, hr]; omega
  · intro i j
    rw [joined_eval _ _ _ _ hfull hR hnon hfullb hRb hnonb _ (oneEach_len i j) hEo,
      names_rows, names_rows, right, hEval]
    by_cases hi : i.val < n
    · let u : Fin n := ⟨i.val,hi⟩
      have hff : (∃ a ∈ F, a.val = i.val) ↔ u ∈ F := by rw [exists_name_iff]; simp [hi, u]
      have hnn : (∃ a ∈ Fᶜ, a.val = i.val) ↔ u ∉ F := by rw [exists_name_iff]; simp [hi, u]
      have dff : decide (∃ a ∈ F, a.val = i.val) = decide (u ∈ F) :=
        Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hff)
      have dnn : decide (∃ a ∈ Fᶜ, a.val = i.val) = decide (u ∉ F) :=
        Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hnn)
      rw [dff, dnn]
      by_cases hfu : u ∈ F
      · by_cases hj : j.val < m
        · have htrue := mem_fullRows.mp hfu (⟨j.val,hj⟩ : Fin m)
          simp [padded, hi, hj, hfu, htrue, u]
        · simp [padded, hi, hj, hfu]
      · rw [sameInput i j hi hfu]
        by_cases hj : j.val < m
        · rw [padded_original _ _ _ _ hi hj, hrep]; simp [padded, hi, hj, hfu]
        · have hd : ∃ v : Fin m, A u v = false := by
            simp only [F, mem_fullRows] at hfu
            push_neg at hfu
            obtain ⟨v,hv⟩ := hfu
            exact ⟨v, by simpa using hv⟩
          obtain ⟨v,hv⟩ := hd
          have he : C.eval (paddedInput n m i j) = false := by
            by_contra h
            have ht : C.eval (paddedInput n m i j) = true := by simpa using h
            have hcontra := eval_mono hC (padded_len n m i j) (oneEach_len u v)
              (fun k hk => by
                rw [padded_read] at hk
                have hk' : k = u.val := by simpa [hi, hj, u] using hk
                rw [oneEach_read]
                exact decide_eq_true (Or.inl hk')) ht
            rw [hrep, hv] at hcontra
            contradiction
          simp [padded, hi, hj, hfu, he]
    · have h1 := decide_eq_false (no_name F i hi)
      have h2 := decide_eq_false (no_name Fᶜ i hi)
      rw [h1, h2]
      simp [padded, hi]

private theorem crossUpper {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    RepSizeAtMost (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0))
      (if n = 1 ∨ m = 1 then 0 else 1) := by
  by_cases hn1 : n = 1
  · refine ⟨wire 0, wire_mono _, by simp [wire_size], ?_⟩
    intro i j
    have h : i.val = 0 := by have := i.isLt; omega
    rw [eval_eq_val]
    change val (wire 0) (oneEach i j) 0 = _
    rw [wire_read, oneEach_read]
    simp [h]
  by_cases hm1 : m = 1
  · refine ⟨wire n, wire_mono _, by simp [wire_size], ?_⟩
    intro i j
    have h : j.val = 0 := by have := j.isLt; omega
    rw [eval_eq_val]
    change val (wire n) (oneEach i j) n = _
    rw [wire_read, oneEach_read]
    simp [h]
  · refine ⟨addGate (n+m) (wire 0) .or 0 n, add_mono _ _ (wire_mono _) _ (Or.inr rfl), ?_, ?_⟩
    · simp [add_size, wire_size, hn1, hm1]
    · intro i j
      rw [add_eval _ _ _ _ _ (oneEach_len i j), eval_or2, val_input (oneEach_len i j) (by omega),
        val_input (oneEach_len i j) (by omega), oneEach_read, oneEach_read]
      have hi : n ≠ i.val := by have := i.isLt; omega
      have h0 : 0 ≠ n+j.val := by omega
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega

private theorem rep_mono {n m a b : ℕ} {A : Fin n → Fin m → Bool} (hab : a ≤ b)
    (h : RepSizeAtMost A a) : RepSizeAtMost A b := by
  obtain ⟨C,hC,hsize,heval⟩ := h
  exact ⟨C,hC,hsize.trans hab,heval⟩

private theorem padded_cross_eq {n m p q : ℕ} :
    padded p q (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)) =
      (fun (i : Fin (n+p)) (j : Fin (m+q)) => decide (i.val < n ∧ j.val < m ∧ (i.val = 0 ∨ j.val = 0))) := by
  funext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < m <;> simp [padded, hi, hj]

end PEqualNP.Outside.L_meta_33613

open PEqualNP.Outside.L_meta_33613

theorem PEqualNP.Outside.L_meta_33613 :
    ∀ (n m p q : Nat), 0 < n → 0 < m → 0 < p → 0 < q →
      let extend := fun (A : Fin n → Fin m → Bool) (i : Fin (n+p)) (j : Fin (m+q)) =>
        if hi : i.val < n then if hj : j.val < m then A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else false else false
      let cross := fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)
      let base := if n = 1 ∨ m = 1 then 0 else 1
      (∀ (A : Fin n → Fin m → Bool) (s : Nat), PEqualNP.Represents.RepSizeAtMost A s →
        PEqualNP.Represents.RepSizeAtMost (extend A) (s+(n+m-1))) ∧
      (∀ s : Nat, PEqualNP.Represents.RepSizeAtMost cross s ↔ base ≤ s) ∧
      (∀ s : Nat, PEqualNP.Represents.RepSizeAtMost (extend cross) s ↔ base+(n+m-1) ≤ s) := by
  intro n m p q hn hm hp hq
  dsimp only
  refine ⟨fun A s h => padding_upper (p := p) (q := q) hn hm A h, ?_, ?_⟩
  · intro s
    constructor
    · intro h
      by_cases hb : n = 1 ∨ m = 1
      · simp [hb]
      · simp only [hb, if_false]
        exact unpaddedCrossLower oneEach_read (by omega) (by omega) h
    · intro h
      exact rep_mono h (crossUpper hn hm)
  · intro s
    constructor
    · intro h
      change PEqualNP.Represents.RepSizeAtMost
        (padded p q (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0))) s at h
      rw [padded_cross_eq] at h
      exact paddedCrossLower oneEach_read oneEach_len read_set_false eval_mono deleteInput
        pullCircuit pull_mono pull_size pull_eval smallFloor hn hm hp hq h
    · intro h
      exact rep_mono h (padding_upper (p := p) (q := q) hn hm _ (crossUpper hn hm))
