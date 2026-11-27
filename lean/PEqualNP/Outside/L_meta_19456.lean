import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- 1. Basic wire evaluation helpers

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWires x := rfl

theorem foldl_length (gs : List Gate) (x : List Bool) :
    (gs.foldl stepWires x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepWires x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWires x g).length := by simp [stepWires]; omega
    rw [ih (stepWires x g) hi']
    simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_append (gs1 gs2 : List Gate) (x : List Bool) :
    (gs1 ++ gs2).foldl stepWires x = gs2.foldl stepWires (gs1.foldl stepWires x) :=
  List.foldl_append

theorem wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_getD_lt C.gates x i hi

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  foldl_length C.gates x

theorem wires_getD_ge (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.size ≤ w) :
    (C.wires x).getD w false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by rw [wires_length]; omega)]
  rfl

theorem wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl stepWires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← hdrop]; exact this.symm
  rw [wires_eq_foldl]
  conv_lhs => rw [hsplit]
  rw [foldl_append, List.foldl_cons]
  set wj := (C.gates.take j).foldl stepWires x
  have hlen : wj.length = x.length + j := by
    rw [foldl_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : x.length + j < (stepWires wj C.gates[j]).length := by
    simp [stepWires, hlen]
  rw [foldl_getD_lt _ _ _ hlt]
  simp only [stepWires, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  rfl

theorem wires_getD_gate_full (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  rw [wires_getD_gate C x j hj]
  congr 1
  apply List.map_congr_left
  intro i _
  set wj := (C.gates.take j).foldl stepWires x
  have hlen : wj.length = x.length + j := by
    rw [foldl_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  by_cases hi : i < x.length + j
  · simp only [hi, ite_true]
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    rw [wires_eq_foldl]
    conv_rhs => rw [hsplit]
    rw [foldl_append]
    exact (foldl_getD_lt _ _ _ (by omega)).symm
  · simp only [hi, ite_false]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

-- 2. Monotonicity (general and with exceptions)

theorem bool_le_all {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ k (h1 : k < l1.length) (h2 : k < l2.length), l1[k] = true → l2[k] = true) :
    l1.all id = true → l2.all id = true := by
  intro h1
  rw [List.all_eq_true] at h1 ⊢
  intro b hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hk1 : k < l1.length := by omega
  have : l1[k] = true := h1 l1[k] (List.getElem_mem hk1)
  exact hle k hk1 hk this

theorem bool_le_any {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ k (h1 : k < l1.length) (h2 : k < l2.length), l1[k] = true → l2[k] = true) :
    l1.any id = true → l2.any id = true := by
  intro h1
  rw [List.any_eq_true] at h1 ⊢
  obtain ⟨b, hb, hbt⟩ := h1
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hk2 : k < l2.length := by omega
  exact ⟨l2[k], List.getElem_mem hk2, hle k hk hk2 hbt⟩

theorem wires_mono_except (C : Circuit) (hM : Monotone2 C) (x y : List Bool)
    (hlen : x.length = y.length)
    (exc : ℕ → Prop)
    (hle_in : ∀ i < x.length, ¬ exc i → x.getD i false = true → y.getD i false = true)
    (hle_exc : ∀ j (hj : j < C.gates.length),
      (∃ i ∈ (C.gates[j]).inputs, exc i) →
      (C.wires x).getD (x.length + j) false = true → (C.wires y).getD (y.length + j) false = true) :
    ∀ w, ¬ exc w → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hne hw
    by_cases hlt : w < x.length
    · rw [wires_getD_input C x w hlt] at hw
      rw [wires_getD_input C y w (by omega)]
      exact hle_in w hlt hne hw
    · by_cases hge : x.length + C.size ≤ w
      · exfalso; rw [wires_getD_ge C x w hge] at hw; cases hw
      · have hj : w - x.length < C.gates.length := by simp [Circuit.size] at hge; omega
        have hw_eq : w = x.length + (w - x.length) := by omega
        have hw_eq_y : w = y.length + (w - x.length) := by omega
        by_cases hex : ∃ i ∈ (C.gates[w - x.length]).inputs, exc i
        · rw [hw_eq] at hw; rw [hw_eq_y]
          exact hle_exc (w - x.length) hj hex hw
        · rw [hw_eq] at hw
          rw [wires_getD_gate_full C x (w - x.length) hj] at hw
          rw [hw_eq_y, wires_getD_gate_full C y (w - x.length) hj]
          set g := C.gates[w - x.length]
          have hgM := hM g (List.getElem_mem hj)
          have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgM.1
          have hstep : ∀ k (h1 : k < (g.inputs.map fun i => if i < x.length + (w - x.length) then (C.wires x).getD i false else false).length)
              (h2 : k < (g.inputs.map fun i => if i < y.length + (w - x.length) then (C.wires y).getD i false else false).length),
              (g.inputs.map fun i => if i < x.length + (w - x.length) then (C.wires x).getD i false else false)[k] = true →
              (g.inputs.map fun i => if i < y.length + (w - x.length) then (C.wires y).getD i false else false)[k] = true := by
            intro k h1 h2 hk
            have hk' : k < g.inputs.length := by simpa using h1
            simp only [List.getElem_map] at hk ⊢
            split at hk
            · rename_i hilt
              simp only [show g.inputs[k]'hk' < y.length + (w - x.length) by omega, ite_true]
              have hne_i : ¬ exc (g.inputs[k]'hk') := fun h => hex ⟨g.inputs[k]'hk', List.getElem_mem hk', h⟩
              exact ih (g.inputs[k]'hk') (by omega) hne_i hk
            · cases hk
          rcases hop with hand | hor
          · simp only [hand, GateOp.eval] at hw ⊢
            exact bool_le_all (by simp) hstep hw
          · simp only [hor, GateOp.eval] at hw ⊢
            exact bool_le_any (by simp) hstep hw

theorem wires_mono (C : Circuit) (hM : Monotone2 C) (x y : List Bool)
    (hlen : x.length = y.length)
    (hle : ∀ i < x.length, x.getD i false = true → y.getD i false = true) :
    ∀ w, (C.wires x).getD w false = true → (C.wires y).getD w false = true :=
  fun w => wires_mono_except C hM x y hlen (fun _ => False) (fun i hi _ => hle i hi) (fun _ _ ⟨_, _, h⟩ => h.elim) w id

-- 3. Single-gate elimination (no ReadsBack needed)

def remapElim (N j dead : ℕ) (rep : Option ℕ) (w : ℕ) : ℕ :=
  if w < N + j then w
  else if w = N + j then rep.getD dead
  else w - 1

def elimGate (N : ℕ) (C : Circuit) (j : ℕ) (rep : Option ℕ) : Circuit :=
  let dead := N + C.size
  let f := remapElim N j dead rep
  let gs := C.gates.take j ++ (C.gates.drop (j + 1)).map (fun g => ⟨g.op, g.inputs.map f⟩)
  ⟨gs, f C.output⟩

theorem elimGate_size (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (rep : Option ℕ) :
    (elimGate N C j rep).size = C.size - 1 := by
  simp [elimGate, Circuit.size, List.length_append, List.length_take, List.length_drop]
  omega

theorem elimGate_mono (N : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (rep : Option ℕ) :
    Monotone2 (elimGate N C j rep) := by
  intro g hg
  simp only [elimGate, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, hg0, rfl⟩
  · exact hM g (List.mem_of_mem_take h1)
  · have := hM g0 (List.mem_of_mem_drop hg0)
    exact ⟨this.1, by simp [this.2]⟩

theorem elimGate_wires (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (rep : Option ℕ) (hrep : ∀ r, rep = some r → r < N + j)
    (x : List Bool) (hx : x.length = N)
    (hval : (C.wires x).getD (N + j) false =
      match rep with | none => false | some r => (C.wires x).getD r false) :
    ∀ w < N + C.size, w ≠ N + j →
      ((elimGate N C j rep).wires x).getD (if w < N + j then w else w - 1) false =
        (C.wires x).getD w false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hne
    set C' := elimGate N C j rep
    have hsz' : C'.size = C.size - 1 := elimGate_size N C j hj rep
    by_cases hltj : w < N + j
    · simp only [hltj, ite_true]
      have hlen_take : ((C.gates.take j).foldl stepWires x).length = N + j := by
        rw [foldl_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have h1 : (C'.wires x).getD w false = ((C.gates.take j).foldl stepWires x).getD w false := by
        rw [wires_eq_foldl]
        change ((C.gates.take j ++ (C.gates.drop (j + 1)).map _).foldl stepWires x).getD w false = _
        rw [foldl_append]
        exact foldl_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD w false = ((C.gates.take j).foldl stepWires x).getD w false := by
        rw [wires_eq_foldl]
        conv_lhs => rw [← List.take_append_drop j C.gates]
        rw [foldl_append]
        exact foldl_getD_lt _ _ _ (by omega)
      rw [h1, h2]
    · simp only [hltj, ite_false]
      have hw_gt : N + j < w := by omega
      have hk : w - N < C.gates.length := by simp [Circuit.size] at hw; omega
      have hk' : w - 1 - N < C'.gates.length := by simp [Circuit.size] at hsz' ⊢; omega
      have heq1 : w - 1 = x.length + (w - 1 - N) := by omega
      have heq2 : w = x.length + (w - N) := by omega
      conv_lhs => rw [heq1]
      conv_rhs => rw [heq2]
      rw [wires_getD_gate_full C' x (w - 1 - N) hk', wires_getD_gate_full C x (w - N) hk]
      have hg' : C'.gates[w - 1 - N]'hk' =
          ⟨(C.gates[w - N]'hk).op, (C.gates[w - N]'hk).inputs.map (remapElim N j (N + C.size) rep)⟩ := by
        have hlt_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
        have hle : (C.gates.take j).length ≤ w - 1 - N := by omega
        simp only [C', elimGate, List.getElem_append_right hle, hlt_take, List.getElem_map, List.getElem_drop]
        congr 1
        · congr 1; congr 1; omega
        · congr 1; congr 1; congr 1; omega
      rw [hg']
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, remapElim]
      by_cases hi : i < N + (w - N)
      · simp only [hx, show i < N + (w - N) from hi, ite_true]
        by_cases h1 : i < N + j
        · simp only [h1, ite_true, show i < N + (w - 1 - N) by omega]
          have := ih i (by omega) (by omega) (by omega)
          simpa [h1] using this
        · by_cases h2 : i = N + j
          · subst h2
            simp only [h1, ite_false, ite_true]
            cases rep with
            | none =>
              simp only [Option.getD_none, show ¬ N + C.size < N + (w - 1 - N) by omega, ite_false]
              exact hval.symm
            | some r =>
              have hr : r < N + j := hrep r rfl
              simp only [Option.getD_some, show r < N + (w - 1 - N) by omega, ite_true]
              have hrw := ih r (by omega) (by omega) (by omega)
              simp only [hr, ite_true] at hrw
              rw [hrw]
              exact hval.symm
          · simp only [h1, h2, ite_false, show i - 1 < N + (w - 1 - N) by omega, ite_true]
            have := ih i (by omega) (by omega) h2
            simpa [h1] using this
      · simp only [hx, hi, ite_false]
        have h1 : ¬ i < N + j := by omega
        have h2 : i ≠ N + j := by omega
        simp only [h1, h2, ite_false, show ¬ i - 1 < N + (w - 1 - N) by omega, ite_false]

theorem elimGate_eval (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (rep : Option ℕ) (hrep : ∀ r, rep = some r → r < N + j)
    (x : List Bool) (hx : x.length = N)
    (hval : (C.wires x).getD (N + j) false =
      match rep with | none => false | some r => (C.wires x).getD r false) :
    (elimGate N C j rep).eval x = C.eval x := by
  unfold Circuit.eval
  set C' := elimGate N C j rep
  have hsz' : C'.size = C.size - 1 := elimGate_size N C j hj rep
  change (C'.wires x).getD (remapElim N j (N + C.size) rep C.output) false = (C.wires x).getD C.output false
  unfold remapElim
  by_cases h1 : C.output < N + j
  · simp only [h1, ite_true]
    have := elimGate_wires N C j hj rep hrep x hx hval C.output (by simp [Circuit.size]; omega) (by omega)
    simpa [h1] using this
  · by_cases h2 : C.output = N + j
    · rw [h2]
      simp only [lt_irrefl, ite_false, ite_true]
      cases rep with
      | none =>
        simp only [Option.getD_none]
        rw [wires_getD_ge C' x (N + C.size) (by omega)]
        exact hval.symm
      | some r =>
        have hr : r < N + j := hrep r rfl
        simp only [Option.getD_some]
        have hrw := elimGate_wires N C j hj (some r) hrep x hx hval r (by simp [Circuit.size]; omega) (by omega)
        simp only [hr, ite_true] at hrw
        rw [hrw]
        exact hval.symm
    · simp only [h1, h2, ite_false]
      by_cases hlt : C.output < N + C.size
      · have := elimGate_wires N C j hj rep hrep x hx hval C.output hlt h2
        simpa [h1] using this
      · rw [wires_getD_ge C' x (C.output - 1) (by omega), wires_getD_ge C x C.output (by omega)]

-- 4. Unified constant-propagation and simplification engine (simpCircuit)

inductive WVal where
  | vfalse
  | vtrue
  | vwire (w : ℕ)

inductive WStatus where
  | cfalse
  | ctrue
  | wref (w : ℕ)
  | kept (newWire : ℕ)

def WStatus.isKept : WStatus → Bool
  | .kept _ => true
  | _ => false

def resolveWire (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (i : ℕ) : WVal :=
  if i < N then
    if Z i then .vfalse else .vwire i
  else
    match st[i - N]? with
    | none => .vfalse
    | some .cfalse => .vfalse
    | some .ctrue => .vtrue
    | some (.wref w) => .vwire w
    | some (.kept nw) => .vwire nw

def evalWVal (nw : List Bool) : WVal → Bool
  | .vfalse => false
  | .vtrue => true
  | .vwire w => nw.getD w false

def simpStep (N : ℕ) (Z : ℕ → Bool) (acc : List WStatus × List Gate) (g : Gate) :
    List WStatus × List Gate :=
  let (st, keptGates) := acc
  match g.op with
  | GateOp.and =>
    match g.inputs with
    | [] => (st ++ [.ctrue], keptGates)
    | [a] =>
      match resolveWire N Z st a with
      | .vfalse => (st ++ [.cfalse], keptGates)
      | .vtrue => (st ++ [.ctrue], keptGates)
      | .vwire ra => (st ++ [.wref ra], keptGates)
    | [a, b] =>
      match resolveWire N Z st a, resolveWire N Z st b with
      | .vfalse, _ => (st ++ [.cfalse], keptGates)
      | _, .vfalse => (st ++ [.cfalse], keptGates)
      | .vtrue, .vtrue => (st ++ [.ctrue], keptGates)
      | .vtrue, .vwire rb => (st ++ [.wref rb], keptGates)
      | .vwire ra, .vtrue => (st ++ [.wref ra], keptGates)
      | .vwire ra, .vwire rb =>
        if ra = rb then (st ++ [.wref ra], keptGates)
        else (st ++ [.kept (N + keptGates.length)], keptGates ++ [⟨.and, [ra, rb]⟩])
    | _ => (st ++ [.cfalse], keptGates)
  | GateOp.or =>
    match g.inputs with
    | [] => (st ++ [.cfalse], keptGates)
    | [a] =>
      match resolveWire N Z st a with
      | .vfalse => (st ++ [.cfalse], keptGates)
      | .vtrue => (st ++ [.ctrue], keptGates)
      | .vwire ra => (st ++ [.wref ra], keptGates)
    | [a, b] =>
      match resolveWire N Z st a, resolveWire N Z st b with
      | .vtrue, _ => (st ++ [.ctrue], keptGates)
      | _, .vtrue => (st ++ [.ctrue], keptGates)
      | .vfalse, .vfalse => (st ++ [.cfalse], keptGates)
      | .vfalse, .vwire rb => (st ++ [.wref rb], keptGates)
      | .vwire ra, .vfalse => (st ++ [.wref ra], keptGates)
      | .vwire ra, .vwire rb =>
        if ra = rb then (st ++ [.wref ra], keptGates)
        else (st ++ [.kept (N + keptGates.length)], keptGates ++ [⟨.or, [ra, rb]⟩])
    | _ => (st ++ [.cfalse], keptGates)
  | _ => (st ++ [.cfalse], keptGates)

def simpRes (N : ℕ) (Z : ℕ → Bool) (C : Circuit) : List WStatus × List Gate :=
  C.gates.foldl (simpStep N Z) ([], [])

def simpCircuit (N : ℕ) (Z : ℕ → Bool) (C : Circuit) : Circuit :=
  let res := simpRes N Z C
  match resolveWire N Z res.1 C.output with
  | .vfalse => ⟨res.2, N + res.2.length + 1⟩
  | .vtrue => ⟨res.2 ++ [⟨.and, []⟩], N + res.2.length⟩
  | .vwire w => ⟨res.2, w⟩

def SimpShape (N : ℕ) (st : List WStatus) (kept : List Gate) : Prop :=
  (∀ g ∈ kept, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ s ∈ st, match s with
    | .cfalse => True
    | .ctrue => True
    | .wref w => w < N + kept.length
    | .kept nw => nw < N + kept.length) ∧
  kept.length = st.countP WStatus.isKept

theorem resolveWire_lt (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (kept : List Gate)
    (hS : SimpShape N st kept) (i w : ℕ) (h : resolveWire N Z st i = .vwire w) :
    w < N + kept.length := by
  unfold resolveWire at h
  split at h
  · split at h
    · cases h
    · cases h; omega
  · cases hget : st[i - N]? with
    | none => rw [hget] at h; cases h
    | some s =>
      rw [hget] at h
      have hs := hS.2.1 s (List.mem_of_getElem? hget)
      cases s with
      | cfalse => cases h
      | ctrue => cases h
      | wref u => cases h; exact hs
      | kept nw => cases h; exact hs

theorem simpStep_shape (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (kept : List Gate)
    (hS : SimpShape N st kept) (g : Gate) :
    SimpShape N (simpStep N Z (st, kept) g).1 (simpStep N Z (st, kept) g).2 := by
  have hpush_del : ∀ s : WStatus, s.isKept = false →
      (match s with | .cfalse => True | .ctrue => True | .wref w => w < N + kept.length | .kept nw => nw < N + kept.length) →
      SimpShape N (st ++ [s]) kept := by
    intro s hsk hsb
    refine ⟨hS.1, ?_, ?_⟩
    · intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hS.2.1 x hx
      · exact hsb
    · rw [List.countP_append, List.countP_singleton, hsk]; simp [hS.2.2]
  have hpush_keep : ∀ (op : GateOp) (ra rb : ℕ), (op = .and ∨ op = .or) →
      SimpShape N (st ++ [.kept (N + kept.length)]) (kept ++ [⟨op, [ra, rb]⟩]) := by
    intro op ra rb hop
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hS.1 x hx
      · exact ⟨hop, rfl⟩
    · intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have h := hS.2.1 x hx
        cases x <;> simp_all <;> omega
      · simp
    · rw [List.length_append, List.length_singleton, List.countP_append, List.countP_singleton]
      simp [WStatus.isKept, hS.2.2]
  unfold simpStep
  cases g.op with
  | and =>
    cases g.inputs with
    | nil => exact hpush_del .ctrue rfl trivial
    | cons a t =>
      cases t with
      | nil =>
        cases hr : resolveWire N Z st a with
        | vfalse => simp only [hr]; exact hpush_del .cfalse rfl trivial
        | vtrue => simp only [hr]; exact hpush_del .ctrue rfl trivial
        | vwire ra => simp only [hr]; exact hpush_del (.wref ra) rfl (resolveWire_lt N Z st kept hS a ra hr)
      | cons b t2 =>
        cases t2 with
        | nil =>
          cases hra : resolveWire N Z st a <;> cases hrb : resolveWire N Z st b <;> simp only [hra, hrb]
          · exact hpush_del .cfalse rfl trivial
          · exact hpush_del .cfalse rfl trivial
          · exact hpush_del .cfalse rfl trivial
          · exact hpush_del .cfalse rfl trivial
          · exact hpush_del .ctrue rfl trivial
          · exact hpush_del (.wref _) rfl (resolveWire_lt N Z st kept hS b _ hrb)
          · exact hpush_del .cfalse rfl trivial
          · exact hpush_del (.wref _) rfl (resolveWire_lt N Z st kept hS a _ hra)
          · split
            · exact hpush_del (.wref _) rfl (resolveWire_lt N Z st kept hS a _ hra)
            · exact hpush_keep .and _ _ (Or.inl rfl)
        | cons _ _ => exact hpush_del .cfalse rfl trivial
  | or =>
    cases g.inputs with
    | nil => exact hpush_del .cfalse rfl trivial
    | cons a t =>
      cases t with
      | nil =>
        cases hr : resolveWire N Z st a with
        | vfalse => simp only [hr]; exact hpush_del .cfalse rfl trivial
        | vtrue => simp only [hr]; exact hpush_del .ctrue rfl trivial
        | vwire ra => simp only [hr]; exact hpush_del (.wref ra) rfl (resolveWire_lt N Z st kept hS a ra hr)
      | cons b t2 =>
        cases t2 with
        | nil =>
          cases hra : resolveWire N Z st a <;> cases hrb : resolveWire N Z st b <;> simp only [hra, hrb]
          · exact hpush_del .cfalse rfl trivial
          · exact hpush_del .ctrue rfl trivial
          · exact hpush_del (.wref _) rfl (resolveWire_lt N Z st kept hS b _ hrb)
          · exact hpush_del .ctrue rfl trivial
          · exact hpush_del .ctrue rfl trivial
          · exact hpush_del .ctrue rfl trivial
          · exact hpush_del (.wref _) rfl (resolveWire_lt N Z st kept hS a _ hra)
          · exact hpush_del .ctrue rfl trivial
          · split
            · exact hpush_del (.wref _) rfl (resolveWire_lt N Z st kept hS a _ hra)
            · exact hpush_keep .or _ _ (Or.inr rfl)
        | cons _ _ => exact hpush_del .cfalse rfl trivial
  | not => exact hpush_del .cfalse rfl trivial
  | mod _ => exact hpush_del .cfalse rfl trivial
  | maj => exact hpush_del .cfalse rfl trivial

-- Evaluation invariant of simpStep
def SimpEval (N : ℕ) (Z : ℕ → Bool) (x : List Bool) (ow : List Bool) (st : List WStatus) (kept : List Gate) : Prop :=
  ow.length = N + st.length ∧
  ∀ i, evalWVal (kept.foldl stepWires x) (resolveWire N Z st i) = ow.getD i false

theorem resolveWire_append_lt (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (s : WStatus) (i : ℕ)
    (hi : i < N + st.length) :
    resolveWire N Z (st ++ [s]) i = resolveWire N Z st i := by
  unfold resolveWire
  split
  · rfl
  · rw [List.getElem?_append_left (by omega)]

theorem resolveWire_append_eq (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (s : WStatus) :
    resolveWire N Z (st ++ [s]) (N + st.length) =
      match s with
      | .cfalse => .vfalse
      | .ctrue => .vtrue
      | .wref w => .vwire w
      | .kept nw => .vwire nw := by
  unfold resolveWire
  simp only [show ¬ N + st.length < N by omega, ite_false, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  cases s <;> rfl

theorem resolveWire_ge (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (i : ℕ) (hi : N + st.length ≤ i) :
    resolveWire N Z st i = .vfalse := by
  unfold resolveWire
  simp only [show ¬ i < N by omega, ite_false]
  rw [List.getElem?_eq_none (by omega)]

theorem simpStep_eval (N : ℕ) (Z : ℕ → Bool) (x : List Bool) (hx : x.length = N)
    (ow : List Bool) (st : List WStatus) (kept : List Gate)
    (hS : SimpShape N st kept) (hE : SimpEval N Z x ow st kept)
    (g : Gate) (hgM : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    SimpEval N Z x (stepWires ow g) (simpStep N Z (st, kept) g).1 (simpStep N Z (st, kept) g).2 := by
  set nw := kept.foldl stepWires x
  have hnw_len : nw.length = N + kept.length := by rw [foldl_length, hx]
  have hstep_del : ∀ s : WStatus,
      evalWVal nw (match s with | .cfalse => .vfalse | .ctrue => .vtrue | .wref w => .vwire w | .kept w => .vwire w) =
        g.op.eval (g.inputs.map fun i => ow.getD i false) →
      SimpEval N Z x (stepWires ow g) (st ++ [s]) kept := by
    intro s hs
    refine ⟨by simp [stepWires, hE.1]; omega, fun i => ?_⟩
    by_cases hi : i < N + st.length
    · rw [resolveWire_append_lt N Z st s i hi, hE.2 i]
      simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hE.1]; omega)]
    · by_cases heq : i = N + st.length
      · rw [heq, resolveWire_append_eq N Z st s, hs]
        simp only [stepWires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (Nat.le_of_eq hE.1), hE.1, Nat.sub_self]; rfl
      · rw [resolveWire_ge N Z (st ++ [s]) i (by simp; omega)]
        simp only [evalWVal, stepWires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp [hE.1]; omega)]; rfl
  have hstep_keep : ∀ (op : GateOp) (ra rb : ℕ),
      op.eval [nw.getD ra false, nw.getD rb false] = g.op.eval (g.inputs.map fun i => ow.getD i false) →
      SimpEval N Z x (stepWires ow g) (st ++ [.kept (N + kept.length)]) (kept ++ [({ op := op, inputs := [ra, rb] } : Gate)]) := by
    intro op ra rb hop
    have hfold : (kept ++ [({ op := op, inputs := [ra, rb] } : Gate)]).foldl stepWires x = stepWires nw ⟨op, [ra, rb]⟩ := by
      rw [foldl_append]; rfl
    refine ⟨by simp [stepWires, hE.1]; omega, fun i => ?_⟩
    rw [hfold]
    by_cases hi : i < N + st.length
    · rw [resolveWire_append_lt N Z st _ i hi]
      have hprev := hE.2 i
      have hpres : evalWVal (stepWires nw ⟨op, [ra, rb]⟩) (resolveWire N Z st i) = evalWVal nw (resolveWire N Z st i) := by
        cases hrv : resolveWire N Z st i with
        | vfalse => rfl
        | vtrue => rfl
        | vwire w =>
          have hw := resolveWire_lt N Z st kept hS i w hrv
          simp only [evalWVal, stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hnw_len]; omega)]
      rw [hpres, hprev]
      simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hE.1]; omega)]
    · by_cases heq : i = N + st.length
      · rw [heq, resolveWire_append_eq N Z st _]
        simp only [evalWVal, stepWires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (Nat.le_of_eq hnw_len), hnw_len, Nat.sub_self]
        rw [List.getElem?_append_right (Nat.le_of_eq hE.1), hE.1, Nat.sub_self]
        simpa [List.map, List.getD_eq_getElem?_getD] using hop
      · rw [resolveWire_ge N Z (st ++ [_]) i (by simp; omega)]
        simp only [evalWVal, stepWires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp [hE.1]; omega)]; rfl
  have hop : g.op = .and ∨ g.op = .or := by simpa using hgM.1
  have hlen := hgM.2
  unfold simpStep
  rcases hop with hand | hor
  · rw [hand]
    cases hgi : g.inputs with
    | nil => apply hstep_del .ctrue; simp only [hand, hgi, List.map_nil, GateOp.eval, evalWVal, List.all_nil]
    | cons a t =>
      cases ht : t with
      | nil =>
        have ha : ow.getD a false = evalWVal nw (resolveWire N Z st a) := (hE.2 a).symm
        cases hra : resolveWire N Z st a <;> simp only [hra, evalWVal] at ha ⊢
        · apply hstep_del .cfalse; simp only [hand, hgi, ht, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        · apply hstep_del .ctrue; simp only [hand, hgi, ht, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        · apply hstep_del (.wref _); simp only [hand, hgi, ht, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      | cons b t2 =>
        cases ht2 : t2 with
        | nil =>
          have ha : ow.getD a false = evalWVal nw (resolveWire N Z st a) := (hE.2 a).symm
          have hb : ow.getD b false = evalWVal nw (resolveWire N Z st b) := (hE.2 b).symm
          cases hra : resolveWire N Z st a <;> cases hrb : resolveWire N Z st b <;> simp only [hra, hrb, evalWVal] at ha hb ⊢
          · apply hstep_del .cfalse; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.false_and]
          · apply hstep_del .cfalse; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.false_and]
          · apply hstep_del .cfalse; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.false_and]
          · apply hstep_del .cfalse; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.true_and]
          · apply hstep_del .ctrue; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          · apply hstep_del (.wref _); simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_true]
          · apply hstep_del .cfalse; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.and_false, Bool.false_and]
          · apply hstep_del (.wref _); simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          · split
            · rename_i heq; subst heq
              apply hstep_del (.wref _); simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
            · apply hstep_keep .and; simp only [hand, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, ha, hb]
        | cons _ _ => simp [hgi, ht, ht2] at hlen
  · rw [hor]
    cases hgi : g.inputs with
    | nil => apply hstep_del .cfalse; simp only [hor, hgi, List.map_nil, GateOp.eval, evalWVal, List.any_nil]
    | cons a t =>
      cases ht : t with
      | nil =>
        have ha : ow.getD a false = evalWVal nw (resolveWire N Z st a) := (hE.2 a).symm
        cases hra : resolveWire N Z st a <;> simp only [hra, evalWVal] at ha ⊢
        · apply hstep_del .cfalse; simp only [hor, hgi, ht, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        · apply hstep_del .ctrue; simp only [hor, hgi, ht, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        · apply hstep_del (.wref _); simp only [hor, hgi, ht, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      | cons b t2 =>
        cases ht2 : t2 with
        | nil =>
          have ha : ow.getD a false = evalWVal nw (resolveWire N Z st a) := (hE.2 a).symm
          have hb : ow.getD b false = evalWVal nw (resolveWire N Z st b) := (hE.2 b).symm
          cases hra : resolveWire N Z st a <;> cases hrb : resolveWire N Z st b <;> simp only [hra, hrb, evalWVal] at ha hb ⊢
          · apply hstep_del .cfalse; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · apply hstep_del .ctrue; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.true_or]
          · apply hstep_del (.wref _); simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
          · apply hstep_del .ctrue; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.true_or]
          · apply hstep_del .ctrue; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.true_or]
          · apply hstep_del .ctrue; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.true_or]
          · apply hstep_del (.wref _); simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · apply hstep_del .ctrue; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.or_true, Bool.true_or]
          · split
            · rename_i heq; subst heq
              apply hstep_del (.wref _); simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, evalWVal, ha, hb, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
            · apply hstep_keep .or; simp only [hor, hgi, ht, ht2, List.map_cons, List.map_nil, GateOp.eval, ha, hb]
        | cons _ _ => simp [hgi, ht, ht2] at hlen

-- Fold properties of simpRes
theorem simpRes_props (N : ℕ) (Z : ℕ → Bool) (C : Circuit) (hM : Monotone2 C) :
    (simpRes N Z C).1.length = C.size ∧
    SimpShape N (simpRes N Z C).1 (simpRes N Z C).2 ∧
    ∀ (x : List Bool), x.length = N → (∀ i < N, Z i = true → x.getD i false = false) →
      SimpEval N Z x (C.wires x) (simpRes N Z C).1 (simpRes N Z C).2 := by
  have hgen : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (st : List WStatus) (kept : List Gate), SimpShape N st kept →
      let res := gs.foldl (simpStep N Z) (st, kept)
      res.1.length = st.length + gs.length ∧
      SimpShape N res.1 res.2 ∧
      ∀ (x ow : List Bool), x.length = N → SimpEval N Z x ow st kept →
        SimpEval N Z x (gs.foldl stepWires ow) res.1 res.2 := by
    intro gs
    induction gs with
    | nil =>
      intro _ st kept hS
      exact ⟨by simp, hS, fun _ _ _ hE => hE⟩
    | cons g gs ih =>
      intro hMg st kept hS
      have hgM := hMg g (List.mem_cons_self ..)
      have hS1 := simpStep_shape N Z st kept hS g
      have hlen1 : (simpStep N Z (st, kept) g).1.length = st.length + 1 := by
        unfold simpStep; dsimp only
        rcases (show g.op = .and ∨ g.op = .or by simpa using hgM.1) with h | h <;> rw [h]
        · cases g.inputs with
          | nil => simp
          | cons a t =>
            cases t with
            | nil => cases ha : resolveWire N Z st a <;> simp [ha]
            | cons b t2 =>
              cases t2 with
              | nil => cases ha : resolveWire N Z st a <;> cases hb : resolveWire N Z st b <;> simp only [ha, hb] <;> (try split) <;> simp
              | cons _ _ => simp
        · cases g.inputs with
          | nil => simp
          | cons a t =>
            cases t with
            | nil => cases ha : resolveWire N Z st a <;> simp [ha]
            | cons b t2 =>
              cases t2 with
              | nil => cases ha : resolveWire N Z st a <;> cases hb : resolveWire N Z st b <;> simp only [ha, hb] <;> (try split) <;> simp
              | cons _ _ => simp
      have hrec := ih (fun g' hg' => hMg g' (List.mem_cons_of_mem _ hg')) _ _ hS1
      refine ⟨by simp [List.foldl_cons, hrec.1, hlen1]; omega, hrec.2.1, ?_⟩
      intro x ow hx hE
      exact hrec.2.2 x (stepWires ow g) hx (simpStep_eval N Z x hx ow st kept hS hE g hgM)
  have hS0 : SimpShape N [] [] := ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), rfl⟩
  have h := hgen C.gates hM [] [] hS0
  refine ⟨by simpa [simpRes, Circuit.size] using h.1, h.2.1, fun x hx hZ => ?_⟩
  apply h.2.2 x x hx
  refine ⟨by simpa using hx, fun i => ?_⟩
  unfold resolveWire
  by_cases hi : i < N
  · simp only [hi, ite_true]
    by_cases hzi : Z i = true
    · simp only [hzi, ite_true, evalWVal]
      exact (hZ i hi hzi).symm
    · simp only [hzi, Bool.false_eq_true, ite_false, evalWVal, List.foldl_nil]
  · simp only [hi, ite_false, List.getElem?_nil, evalWVal, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]; rfl

theorem simpCircuit_mono (N : ℕ) (Z : ℕ → Bool) (C : Circuit) (hM : Monotone2 C) :
    Monotone2 (simpCircuit N Z C) := by
  have hS := (simpRes_props N Z C hM).2.1
  unfold simpCircuit
  dsimp only
  cases resolveWire N Z (simpRes N Z C).1 C.output with
  | vfalse =>
    intro g hg; have := hS.1 g hg; exact ⟨by simpa using this.1, by omega⟩
  | vtrue =>
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · have := hS.1 g hg; exact ⟨by simpa using this.1, by omega⟩
    · exact ⟨by simp, by simp⟩
  | vwire w =>
    intro g hg; have := hS.1 g hg; exact ⟨by simpa using this.1, by omega⟩

theorem simpCircuit_eval (N : ℕ) (Z : ℕ → Bool) (C : Circuit) (hM : Monotone2 C)
    (x : List Bool) (hx : x.length = N) (hZ : ∀ i < N, Z i = true → x.getD i false = false) :
    (simpCircuit N Z C).eval x = C.eval x := by
  have hE := (simpRes_props N Z C hM).2.2 x hx hZ
  have hout := hE.2 C.output
  unfold simpCircuit Circuit.eval
  dsimp only
  cases hrv : resolveWire N Z (simpRes N Z C).1 C.output with
  | vfalse =>
    rw [hrv] at hout
    rw [wires_getD_ge ⟨(simpRes N Z C).2, N + (simpRes N Z C).2.length + 1⟩ x _ (by simp [Circuit.size, hx])]
    exact hout
  | vtrue =>
    rw [hrv] at hout
    set ks := (simpRes N Z C).2
    have hlen : (ks.foldl stepWires x).length = N + ks.length := by rw [foldl_length, hx]
    rw [wires_eq_foldl]
    change ((ks ++ [({ op := .and, inputs := [] } : Gate)]).foldl stepWires x).getD (N + ks.length) false = _
    rw [foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, stepWires, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    simpa [evalWVal, GateOp.eval] using hout
  | vwire w =>
    rw [hrv] at hout
    exact hout

theorem simpCircuit_size_of_not_vtrue (N : ℕ) (Z : ℕ → Bool) (C : Circuit) (hM : Monotone2 C)
    (hnt : resolveWire N Z (simpRes N Z C).1 C.output ≠ .vtrue) :
    (simpCircuit N Z C).size = (simpRes N Z C).1.countP WStatus.isKept := by
  have hS := (simpRes_props N Z C hM).2.1
  unfold simpCircuit
  dsimp only
  cases hrv : resolveWire N Z (simpRes N Z C).1 C.output with
  | vfalse => exact hS.2.2
  | vtrue => exact (hnt hrv).elim
  | vwire w => exact hS.2.2

-- 5. Simplification inspection, counting, unread wires, and extra elimGate lemmas

theorem simpStep_push (N : ℕ) (Z : ℕ → Bool) (st : List WStatus) (kept : List Gate) (g : Gate) :
    ∃ s, (simpStep N Z (st, kept) g).1 = st ++ [s] := by
  unfold simpStep; dsimp only
  cases g.op <;> (try exact ⟨.cfalse, rfl⟩)
  · cases g.inputs with
    | nil => exact ⟨.ctrue, rfl⟩
    | cons a t =>
      cases t with
      | nil => cases ha : resolveWire N Z st a <;> simp only [ha] <;> exact ⟨_, rfl⟩
      | cons b t2 =>
        cases t2 with
        | nil =>
          cases ha : resolveWire N Z st a <;> cases hb : resolveWire N Z st b <;> simp only [ha, hb] <;>
            (try split) <;> exact ⟨_, rfl⟩
        | cons _ _ => exact ⟨.cfalse, rfl⟩
  · cases g.inputs with
    | nil => exact ⟨.cfalse, rfl⟩
    | cons a t =>
      cases t with
      | nil => cases ha : resolveWire N Z st a <;> simp only [ha] <;> exact ⟨_, rfl⟩
      | cons b t2 =>
        cases t2 with
        | nil =>
          cases ha : resolveWire N Z st a <;> cases hb : resolveWire N Z st b <;> simp only [ha, hb] <;>
            (try split) <;> exact ⟨_, rfl⟩
        | cons _ _ => exact ⟨.cfalse, rfl⟩

theorem foldl_simpStep_ext (N : ℕ) (Z : ℕ → Bool) (gs : List Gate) (st : List WStatus) (kept : List Gate) :
    ∃ ext, ext.length = gs.length ∧ (gs.foldl (simpStep N Z) (st, kept)).1 = st ++ ext := by
  induction gs generalizing st kept with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    rcases simpStep_push N Z st kept g with ⟨s, hs⟩
    rcases ih (simpStep N Z (st, kept) g).1 (simpStep N Z (st, kept) g).2 with ⟨ext, hlen, heq⟩
    refine ⟨s :: ext, by simp [hlen], ?_⟩
    simp only [List.foldl_cons, heq, hs, List.append_assoc, List.singleton_append]

theorem resolveWire_append_ext (N : ℕ) (Z : ℕ → Bool) (st ext : List WStatus) (i : ℕ) (hi : i < N + st.length) :
    resolveWire N Z (st ++ ext) i = resolveWire N Z st i := by
  unfold resolveWire
  split
  · rfl
  · rw [List.getElem?_append_left (by omega)]

theorem simpRes_at_j (N : ℕ) (Z : ℕ → Bool) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    let prev := (C.gates.take j).foldl (simpStep N Z) ([], [])
    prev.1.length = j ∧
    (∀ i < j, (simpRes N Z C).1[i]? = prev.1[i]?) ∧
    (∀ w < N + j, resolveWire N Z (simpRes N Z C).1 w = resolveWire N Z prev.1 w) ∧
    (simpRes N Z C).1[j]? = (simpStep N Z prev (C.gates[j]'hj)).1[j]? := by
  intro prev
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  rcases foldl_simpStep_ext N Z (C.gates.take j) [] [] with ⟨e1, he1_len, he1⟩
  have hprev_len : prev.1.length = j := by rw [he1, List.nil_append, he1_len, htake_len]
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]'hj] ++ C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj]
    simp [List.append_assoc]
  have hres_eq : simpRes N Z C = (C.gates.drop (j + 1)).foldl (simpStep N Z) (simpStep N Z prev (C.gates[j]'hj)) := by
    unfold simpRes
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rcases simpStep_push N Z prev.1 prev.2 (C.gates[j]'hj) with ⟨sj, hsj⟩
  rcases foldl_simpStep_ext N Z (C.gates.drop (j + 1)) (simpStep N Z prev (C.gates[j]'hj)).1 (simpStep N Z prev (C.gates[j]'hj)).2 with ⟨e2, _, he2⟩
  have hst_eq : (simpRes N Z C).1 = prev.1 ++ ([sj] ++ e2) := by
    rw [hres_eq, he2, hsj, List.append_assoc]
  refine ⟨hprev_len, ?_, ?_, ?_⟩
  · intro i hi
    rw [hst_eq, List.getElem?_append_left (by omega)]
  · intro w hw
    rw [hst_eq, resolveWire_append_ext N Z prev.1 _ w (by omega)]
  · rw [hres_eq, he2, List.getElem?_append_left (by rw [hsj]; simp [hprev_len])]

theorem simpRes_not_kept_of_vfalse (N : ℕ) (Z : ℕ → Bool) (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hop : (C.gates[j]'hj).op = .and ∨ (C.gates[j]'hj).op = .or)
    (hin : (C.gates[j]'hj).inputs = [a, b])
    (ha : a < N + j) (hb : b < N + j)
    (hf : resolveWire N Z (simpRes N Z C).1 a = .vfalse ∨ resolveWire N Z (simpRes N Z C).1 b = .vfalse) :
    ∃ s, (simpRes N Z C).1[j]? = some s ∧ s.isKept = false := by
  have hat := simpRes_at_j N Z C j hj
  dsimp only at hat
  rcases hprev : (C.gates.take j).foldl (simpStep N Z) ([], []) with ⟨pst, pkept⟩
  rw [hprev] at hat
  have hplen : pst.length = j := hat.1
  have hra : resolveWire N Z pst a = resolveWire N Z (simpRes N Z C).1 a := (hat.2.2.1 a ha).symm
  have hrb : resolveWire N Z pst b = resolveWire N Z (simpRes N Z C).1 b := (hat.2.2.1 b hb).symm
  rw [hat.2.2.2]
  unfold simpStep; dsimp only
  rcases hop with hand | hor
  · rw [hand, hin]; dsimp only
    rcases hf with hfa | hfb
    · rw [hra, hfa]; simp [hplen, WStatus.isKept]
    · rw [hrb, hfb]; cases h1 : resolveWire N Z pst a <;> simp [h1, hplen, WStatus.isKept]
  · rw [hor, hin]; dsimp only
    rcases hf with hfa | hfb
    · rw [hra, hfa]; cases h2 : resolveWire N Z pst b <;> simp [h2, hplen, WStatus.isKept]
    · rw [hrb, hfb]; cases h1 : resolveWire N Z pst a <;> simp [h1, hplen, WStatus.isKept]

theorem simpRes_cfalse_of_and_vfalse (N : ℕ) (Z : ℕ → Bool) (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hop : (C.gates[j]'hj).op = .and) (hin : (C.gates[j]'hj).inputs = [a, b])
    (ha : a < N + j) (hb : b < N + j)
    (hf : resolveWire N Z (simpRes N Z C).1 a = .vfalse ∨ resolveWire N Z (simpRes N Z C).1 b = .vfalse) :
    resolveWire N Z (simpRes N Z C).1 (N + j) = .vfalse := by
  have hat := simpRes_at_j N Z C j hj
  dsimp only at hat
  rcases hprev : (C.gates.take j).foldl (simpStep N Z) ([], []) with ⟨pst, pkept⟩
  rw [hprev] at hat
  have hplen : pst.length = j := hat.1
  have hra : resolveWire N Z pst a = resolveWire N Z (simpRes N Z C).1 a := (hat.2.2.1 a ha).symm
  have hrb : resolveWire N Z pst b = resolveWire N Z (simpRes N Z C).1 b := (hat.2.2.1 b hb).symm
  have hstj : (simpRes N Z C).1[j]? = some .cfalse := by
    rw [hat.2.2.2]; unfold simpStep; dsimp only; rw [hop, hin]; dsimp only
    rcases hf with hfa | hfb
    · rw [hra, hfa]; simp [hplen]
    · rw [hrb, hfb]; cases h1 : resolveWire N Z pst a <;> simp [h1, hplen]
  unfold resolveWire
  simp only [show ¬ N + j < N by omega, ite_false, Nat.add_sub_cancel_left, hstj]

theorem simpRes_cfalse_of_both_vfalse (N : ℕ) (Z : ℕ → Bool) (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hop : (C.gates[j]'hj).op = .and ∨ (C.gates[j]'hj).op = .or)
    (hin : (C.gates[j]'hj).inputs = [a, b])
    (ha : a < N + j) (hb : b < N + j)
    (hfa : resolveWire N Z (simpRes N Z C).1 a = .vfalse)
    (hfb : resolveWire N Z (simpRes N Z C).1 b = .vfalse) :
    resolveWire N Z (simpRes N Z C).1 (N + j) = .vfalse := by
  have hat := simpRes_at_j N Z C j hj
  dsimp only at hat
  rcases hprev : (C.gates.take j).foldl (simpStep N Z) ([], []) with ⟨pst, pkept⟩
  rw [hprev] at hat
  have hplen : pst.length = j := hat.1
  have hra : resolveWire N Z pst a = .vfalse := (hat.2.2.1 a ha).symm.trans hfa
  have hrb : resolveWire N Z pst b = .vfalse := (hat.2.2.1 b hb).symm.trans hfb
  have hstj : (simpRes N Z C).1[j]? = some .cfalse := by
    rw [hat.2.2.2]; unfold simpStep; dsimp only
    rcases hop with hand | hor
    · rw [hand, hin]; dsimp only; rw [hra]; simp [hplen]
    · rw [hor, hin]; dsimp only; rw [hra, hrb]; simp [hplen]
  unfold resolveWire
  simp only [show ¬ N + j < N by omega, ite_false, Nat.add_sub_cancel_left, hstj]

theorem countP_add_card_false {α : Type*} (l : List α) (p : α → Bool) (S : Finset ℕ)
    (hS : ∀ j ∈ S, ∃ a, l[j]? = some a ∧ p a = false) :
    l.countP p + S.card ≤ l.length := by
  have hcount : l.countP p = ((Finset.range l.length).filter (fun i => (l[i]?.map p).getD false)).card := by
    clear hS
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.countP_cons, List.length_cons]
      rw [ih]
      have hrange : Finset.range (xs.length + 1) = insert 0 ((Finset.range xs.length).image Nat.succ) := by
        ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
        cases i with
        | zero => simp
        | succ k => simp
      rw [hrange, Finset.filter_insert]
      have himg : ((Finset.range xs.length).image Nat.succ).filter (fun i => ((x :: xs)[i]?.map p).getD false) =
          ((Finset.range xs.length).filter (fun i => (xs[i]?.map p).getD false)).image Nat.succ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨k, hk, rfl⟩, hp⟩; exact ⟨k, ⟨hk, hp⟩, rfl⟩
        · rintro ⟨k, ⟨hk, hp⟩, rfl⟩; exact ⟨⟨k, hk, rfl⟩, hp⟩
      rw [himg]
      cases hpx : p x with
      | true =>
        simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some, hpx, ite_true]
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ Nat.succ_injective]
      | false =>
        simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some, hpx, Bool.false_eq_true, ite_false]
        rw [Finset.card_image_of_injective _ Nat.succ_injective]; simp
  rw [hcount]
  set T := (Finset.range l.length).filter (fun i => (l[i]?.map p).getD false)
  have hdisj : Disjoint T S := by
    rw [Finset.disjoint_left]
    intro i hiT hiS
    rcases hS i hiS with ⟨a, ha, hpa⟩
    simp only [T, Finset.mem_filter, ha, Option.map_some, Option.getD_some, hpa] at hiT
    exact Bool.false_ne_true hiT.2
  have hsub : T ∪ S ⊆ Finset.range l.length := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiT | hiS
    · exact (Finset.mem_filter.mp hiT).1
    · rcases hS i hiS with ⟨a, ha, _⟩
      exact Finset.mem_range.mpr (by
        by_contra hge
        have : l[i]? = none := List.getElem?_eq_none (by omega)
        rw [this] at ha; cases ha)
  calc T.card + S.card = (T ∪ S).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (Finset.range l.length).card := Finset.card_le_card hsub
    _ = l.length := Finset.card_range l.length

theorem simpRes_all_kept_shape (N : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hall : ∀ j (hj : j < C.gates.length), ∃ nw, (simpRes N (fun _ => false) C).1[j]? = some (.kept nw)) :
    (∀ j (hj : j < C.gates.length),
      ∃ a b, ((C.gates[j]'hj).op = .and ∨ (C.gates[j]'hj).op = .or) ∧
        (C.gates[j]'hj).inputs = [a, b] ∧ a < N + j ∧ b < N + j ∧ a ≠ b) := by
  have hres_id : ∀ j (hj : j ≤ C.gates.length), ∀ w < N + j,
      resolveWire N (fun _ => false) ((C.gates.take j).foldl (simpStep N (fun _ => false)) ([], [])).1 w = .vwire w := by
    intro j
    induction j with
    | zero =>
      intro _ w hw
      have hw' : w < N := by omega
      simp only [List.take_zero, List.foldl_nil, resolveWire, hw', ite_true, Bool.false_eq_true, ite_false]
    | succ k ih =>
      intro hk w hw
      have hk_lt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hk_lt] := List.take_succ_eq_append_getElem hk_lt
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hat := simpRes_at_j N (fun _ => false) C k hk_lt
      dsimp only at hat
      rcases hprev : (C.gates.take k).foldl (simpStep N (fun _ => false)) ([], []) with ⟨pst, pkept⟩
      rw [hprev] at hat
      have hplen : pst.length = k := hat.1
      rcases hall k hk_lt with ⟨nw, hnw⟩
      have hstep_k : (simpStep N (fun _ => false) (pst, pkept) (C.gates[k]'hk_lt)).1[k]? = some (.kept nw) := by
        rw [← hat.2.2.2, hnw]
      rcases simpStep_push N (fun _ => false) pst pkept (C.gates[k]'hk_lt) with ⟨sk, hsk⟩
      have hsk_eq : sk = .kept nw := by
        rw [hsk, List.getElem?_append_right (by omega), hplen, Nat.sub_self] at hstep_k
        simpa using hstep_k
      have hkept_len : pkept.length = k := by
        have hSprev : SimpShape N pst pkept := by
          have hMtake : Monotone2 ⟨C.gates.take k, 0⟩ := fun g hg => hM g (List.mem_of_mem_take hg)
          have hS := (simpRes_props N (fun _ => false) ⟨C.gates.take k, 0⟩ hMtake).2.1
          simpa [simpRes, hprev] using hS
        rw [hSprev.2.2]
        have hct : pst.countP WStatus.isKept = pst.length := by
          rw [List.countP_eq_length]
          intro s hs
          rcases List.mem_iff_getElem?.mp hs with ⟨i, hi⟩
          have hi_lt : i < k := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hi; cases hi
          have heqi := hat.2.1 i hi_lt
          rcases hall i (by omega) with ⟨nwi, hnwi⟩
          rw [hnwi, hi] at heqi
          cases heqi; rfl
        omega
      have hnw_val : nw = N + k := by
        rw [hsk_eq] at hsk
        have hlast : ∀ (s1 s2 : WStatus), pst ++ [s1] = pst ++ [s2] → s1 = s2 := fun s1 s2 h => by
          have := List.append_cancel_left h; simpa using this
        unfold simpStep at hsk; dsimp only at hsk
        cases hop : (C.gates[k]'hk_lt).op <;> simp only [hop] at hsk <;> (try (have := hlast _ _ hsk; cases this))
        · cases hgi : (C.gates[k]'hk_lt).inputs with
          | nil => simp only [hgi] at hsk; have := hlast _ _ hsk; cases this
          | cons a t => cases ht : t with
            | nil =>
              simp only [hgi, ht] at hsk
              cases ha : resolveWire N (fun _ => false) pst a <;> simp only [ha] at hsk <;> (have := hlast _ _ hsk; cases this)
            | cons b t2 => cases ht2 : t2 with
              | nil =>
                simp only [hgi, ht, ht2] at hsk
                cases ha : resolveWire N (fun _ => false) pst a <;> cases hb : resolveWire N (fun _ => false) pst b <;>
                  simp only [ha, hb] at hsk <;> (try (have := hlast _ _ hsk; cases this))
                split at hsk
                · have := hlast _ _ hsk; cases this
                · have := hlast _ _ hsk; cases this; omega
              | cons _ _ => simp only [hgi, ht, ht2] at hsk; have := hlast _ _ hsk; cases this
        · cases hgi : (C.gates[k]'hk_lt).inputs with
          | nil => simp only [hgi] at hsk; have := hlast _ _ hsk; cases this
          | cons a t => cases ht : t with
            | nil =>
              simp only [hgi, ht] at hsk
              cases ha : resolveWire N (fun _ => false) pst a <;> simp only [ha] at hsk <;> (have := hlast _ _ hsk; cases this)
            | cons b t2 => cases ht2 : t2 with
              | nil =>
                simp only [hgi, ht, ht2] at hsk
                cases ha : resolveWire N (fun _ => false) pst a <;> cases hb : resolveWire N (fun _ => false) pst b <;>
                  simp only [ha, hb] at hsk <;> (try (have := hlast _ _ hsk; cases this))
                split at hsk
                · have := hlast _ _ hsk; cases this
                · have := hlast _ _ hsk; cases this; omega
              | cons _ _ => simp only [hgi, ht, ht2] at hsk; have := hlast _ _ hsk; cases this
      by_cases hwlt : w < N + k
      · rw [hsk, resolveWire_append_lt N (fun _ => false) pst sk w (by omega)]
        have := ih (by omega) w hwlt
        simpa [hprev] using this
      · have hweq : w = N + k := by omega
        subst hweq
        rw [hsk, hsk_eq, hnw_val]
        have := resolveWire_append_eq N (fun _ => false) pst (.kept (N + k))
        simpa [hplen] using this
  intro j hj
  have hat := simpRes_at_j N (fun _ => false) C j hj
  dsimp only at hat
  rcases hprev : (C.gates.take j).foldl (simpStep N (fun _ => false)) ([], []) with ⟨pst, pkept⟩
  rw [hprev] at hat
  have hplen : pst.length = j := hat.1
  rcases hall j hj with ⟨nw, hnw⟩
  rw [hat.2.2.2] at hnw
  have hgj := hM (C.gates[j]'hj) (List.getElem_mem hj)
  have hop : (C.gates[j]'hj).op = .and ∨ (C.gates[j]'hj).op = .or := by simpa using hgj.1
  have hres_prev : ∀ w, resolveWire N (fun _ => false) pst w = if w < N + j then .vwire w else .vfalse := by
    intro w
    split
    · next hw =>
      have := hres_id j (Nat.le_of_lt hj) w hw
      simpa [hprev] using this
    · next hw => exact resolveWire_ge N (fun _ => false) pst w (by omega)
  unfold simpStep at hnw; dsimp only at hnw
  rcases hop with hand | hor
  · rw [hand] at hnw; dsimp only at hnw
    cases hgi : (C.gates[j]'hj).inputs with
    | nil => rw [hgi] at hnw; simp [hplen] at hnw
    | cons a t =>
      cases ht : t with
      | nil =>
        rw [hgi, ht] at hnw; dsimp only at hnw
        cases ha : resolveWire N (fun _ => false) pst a <;> simp [ha, hplen] at hnw
      | cons b t2 =>
        cases ht2 : t2 with
        | nil =>
          rw [hgi, ht, ht2] at hnw; dsimp only at hnw
          rw [hres_prev a, hres_prev b] at hnw
          by_cases ha : a < N + j
          · by_cases hb : b < N + j
            · simp only [ha, hb, ite_true] at hnw
              by_cases hab : a = b
              · simp only [hab, ite_true] at hnw; simp [hplen] at hnw
              · exact ⟨a, b, Or.inl hand, rfl, ha, hb, hab⟩
            · simp only [ha, hb, ite_true, ite_false] at hnw; simp [hplen] at hnw
          · simp only [ha, ite_false] at hnw; simp [hplen] at hnw
        | cons _ _ => rw [hgi, ht, ht2] at hnw; simp [hplen] at hnw
  · rw [hor] at hnw; dsimp only at hnw
    cases hgi : (C.gates[j]'hj).inputs with
    | nil => rw [hgi] at hnw; simp [hplen] at hnw
    | cons a t =>
      cases ht : t with
      | nil =>
        rw [hgi, ht] at hnw; dsimp only at hnw
        cases ha : resolveWire N (fun _ => false) pst a <;> simp [ha, hplen] at hnw
      | cons b t2 =>
        cases ht2 : t2 with
        | nil =>
          rw [hgi, ht, ht2] at hnw; dsimp only at hnw
          rw [hres_prev a, hres_prev b] at hnw
          by_cases ha : a < N + j
          · by_cases hb : b < N + j
            · simp only [ha, hb, ite_true] at hnw
              by_cases hab : a = b
              · simp only [hab, ite_true] at hnw; simp [hplen] at hnw
              · exact ⟨a, b, Or.inr hor, rfl, ha, hb, hab⟩
            · simp only [ha, hb, ite_true, ite_false] at hnw; simp [hplen] at hnw
          · by_cases hb : b < N + j
            · simp only [ha, hb, ite_true, ite_false] at hnw; simp [hplen] at hnw
            · simp only [ha, hb, ite_false] at hnw; simp [hplen] at hnw
        | cons _ _ => rw [hgi, ht, ht2] at hnw; simp [hplen] at hnw

theorem wires_eq_of_unread (N : ℕ) (C : Circuit) (U : ℕ → Prop)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i < N, ¬ U i → x.getD i false = y.getD i false)
    (k : ℕ) (hk : k ≤ C.gates.length)
    (hno : ∀ j (hj : j < k), ∀ w ∈ (C.gates[j]'(by omega)).inputs, ¬ U w) :
    ∀ w < N + k, ¬ U w → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnw
    by_cases hlt : w < N
    · rw [wires_getD_input C x w (by omega), wires_getD_input C y w (by omega)]
      exact hxy w hlt hnw
    · have hj : w - N < C.gates.length := by omega
      have heq1 : w = x.length + (w - N) := by omega
      have heq2 : w = y.length + (w - N) := by omega
      conv_lhs => rw [heq1]
      conv_rhs => rw [heq2]
      rw [wires_getD_gate_full C x (w - N) hj, wires_getD_gate_full C y (w - N) hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases hil : i < N + (w - N)
      · simp only [hx, hy, hil, ite_true]
        exact ih i (by omega) (by omega) (hno (w - N) (by omega) i hi)
      · simp only [hx, hy, hil, ite_false]

theorem elimGate_unused_wires (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hunused : ∀ j' (hj' : j' < C.gates.length), j < j' → N + j ∉ (C.gates[j']'hj').inputs)
    (x : List Bool) (hx : x.length = N) :
    ∀ w < N + C.size, w ≠ N + j →
      ((elimGate N C j none).wires x).getD (if w < N + j then w else w - 1) false = (C.wires x).getD w false := by
  set C' := elimGate N C j none
  have hsz' : C'.size = C.size - 1 := elimGate_size N C j hj none
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    by_cases hltj : w < N + j
    · simp only [hltj, ite_true]
      have htake : ((C.gates.take j).foldl stepWires x).length = N + j := by
        rw [foldl_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have h1 : (C'.wires x).getD w false = ((C.gates.take j).foldl stepWires x).getD w false := by
        rw [wires_eq_foldl]
        change ((C.gates.take j ++ (C.gates.drop (j + 1)).map _).foldl stepWires x).getD w false = _
        rw [foldl_append]; exact foldl_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD w false = ((C.gates.take j).foldl stepWires x).getD w false := by
        rw [wires_eq_foldl]
        conv_lhs => rw [← List.take_append_drop j C.gates]
        rw [foldl_append]; exact foldl_getD_lt _ _ _ (by omega)
      rw [h1, h2]
    · simp only [hltj, ite_false]
      have hk : w - N < C.gates.length := by simp [Circuit.size] at hw; omega
      have hk' : w - 1 - N < C'.gates.length := by simp [Circuit.size] at hsz' ⊢; omega
      have heq1 : w - 1 = x.length + (w - 1 - N) := by omega
      have heq2 : w = x.length + (w - N) := by omega
      conv_lhs => rw [heq1]
      conv_rhs => rw [heq2]
      rw [wires_getD_gate_full C' x (w - 1 - N) hk', wires_getD_gate_full C x (w - N) hk]
      have hg' : C'.gates[w - 1 - N]'hk' =
          ⟨(C.gates[w - N]'hk).op, (C.gates[w - N]'hk).inputs.map (remapElim N j (N + C.size) none)⟩ := by
        have hlt_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
        have hle : (C.gates.take j).length ≤ w - 1 - N := by omega
        simp only [C', elimGate, List.getElem_append_right hle, hlt_take, List.getElem_map, List.getElem_drop]
        congr 1
        · congr 1; congr 1; omega
        · congr 1; congr 1; congr 1; omega
      rw [hg', List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi_mem
      have hine : i ≠ N + j := fun h => hunused (w - N) hk (by omega) (h ▸ hi_mem)
      simp only [Function.comp_apply, remapElim]
      by_cases hi : i < N + (w - N)
      · simp only [hx, hi, ite_true]
        by_cases h1 : i < N + j
        · simp only [h1, ite_true, show i < N + (w - 1 - N) by omega]
          simpa [h1] using ih i (by omega) (by omega) hine
        · simp only [h1, hine, ite_false, show i - 1 < N + (w - 1 - N) by omega, ite_true]
          simpa [h1] using ih i (by omega) (by omega) hine
      · simp only [hx, hi, ite_false]
        have h1 : ¬ i < N + j := by omega
        simp only [h1, hine, ite_false, show ¬ i - 1 < N + (w - 1 - N) by omega, ite_false]

theorem elimGate_unused_eval (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hunused : ∀ j' (hj' : j' < C.gates.length), j < j' → N + j ∉ (C.gates[j']'hj').inputs)
    (hout : C.output ≠ N + j) (x : List Bool) (hx : x.length = N) :
    (elimGate N C j none).eval x = C.eval x := by
  unfold Circuit.eval
  set C' := elimGate N C j none
  have hsz' : C'.size = C.size - 1 := elimGate_size N C j hj none
  change (C'.wires x).getD (remapElim N j (N + C.size) none C.output) false = (C.wires x).getD C.output false
  unfold remapElim
  by_cases h1 : C.output < N + j
  · simp only [h1, ite_true]
    simpa [h1] using elimGate_unused_wires N C j hj hunused x hx C.output (by simp [Circuit.size]; omega) hout
  · simp only [h1, hout, ite_false]
    by_cases hlt : C.output < N + C.size
    · simpa [h1] using elimGate_unused_wires N C j hj hunused x hx C.output hlt hout
    · rw [wires_getD_ge C' x (C.output - 1) (by omega), wires_getD_ge C x C.output (by omega)]

theorem elimGate_mono_le_wires (N : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (r : ℕ) (hr : r < N + j) (x : List Bool) (hx : x.length = N)
    (hle : (C.wires x).getD r false ≤ (C.wires x).getD (N + j) false) :
    ∀ w < N + C.size, w ≠ N + j →
      ((elimGate N C j (some r)).wires x).getD (if w < N + j then w else w - 1) false ≤ (C.wires x).getD w false := by
  set C' := elimGate N C j (some r)
  have hsz' : C'.size = C.size - 1 := elimGate_size N C j hj (some r)
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    by_cases hltj : w < N + j
    · simp only [hltj, ite_true]
      have htake : ((C.gates.take j).foldl stepWires x).length = N + j := by
        rw [foldl_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have h1 : (C'.wires x).getD w false = ((C.gates.take j).foldl stepWires x).getD w false := by
        rw [wires_eq_foldl]
        change ((C.gates.take j ++ (C.gates.drop (j + 1)).map _).foldl stepWires x).getD w false = _
        rw [foldl_append]; exact foldl_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD w false = ((C.gates.take j).foldl stepWires x).getD w false := by
        rw [wires_eq_foldl]
        conv_lhs => rw [← List.take_append_drop j C.gates]
        rw [foldl_append]; exact foldl_getD_lt _ _ _ (by omega)
      rw [h1, h2]
    · simp only [hltj, ite_false]
      have hk : w - N < C.gates.length := by simp [Circuit.size] at hw; omega
      have hk' : w - 1 - N < C'.gates.length := by simp [Circuit.size] at hsz' ⊢; omega
      have heq1 : w - 1 = x.length + (w - 1 - N) := by omega
      have heq2 : w = x.length + (w - N) := by omega
      conv_lhs => rw [heq1]
      conv_rhs => rw [heq2]
      rw [wires_getD_gate_full C' x (w - 1 - N) hk', wires_getD_gate_full C x (w - N) hk]
      have hg' : C'.gates[w - 1 - N]'hk' =
          ⟨(C.gates[w - N]'hk).op, (C.gates[w - N]'hk).inputs.map (remapElim N j (N + C.size) (some r))⟩ := by
        have hlt_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
        have hle' : (C.gates.take j).length ≤ w - 1 - N := by omega
        simp only [C', elimGate, List.getElem_append_right hle', hlt_take, List.getElem_map, List.getElem_drop]
        congr 1
        · congr 1; congr 1; omega
        · congr 1; congr 1; congr 1; omega
      rw [hg', List.map_map]
      have hpoint : ∀ idx (hidx : idx < (C.gates[w - N]'hk).inputs.length),
          (if remapElim N j (N + C.size) (some r) ((C.gates[w - N]'hk).inputs[idx]'hidx) < x.length + (w - 1 - N)
           then (C'.wires x).getD (remapElim N j (N + C.size) (some r) ((C.gates[w - N]'hk).inputs[idx]'hidx)) false else false) = true →
          (if (C.gates[w - N]'hk).inputs[idx]'hidx < x.length + (w - N)
           then (C.wires x).getD ((C.gates[w - N]'hk).inputs[idx]'hidx) false else false) = true := by
        intro idx hidx htr
        set i := (C.gates[w - N]'hk).inputs[idx]'hidx
        simp only [remapElim] at htr
        by_cases hi : i < N + (w - N)
        · simp only [hx, hi, ite_true]
          by_cases h1 : i < N + j
          · simp only [h1, ite_true, hx, show i < N + (w - 1 - N) by omega] at htr
            have hle_i := ih i (by omega) (by omega) (by omega)
            simp only [h1, ite_true] at hle_i
            exact (Bool.le_iff_imp.mp hle_i) htr
          · by_cases h2 : i = N + j
            · rw [h2] at htr ⊢
              simp only [show ¬ N + j < N + j by omega, ite_false, ite_true, Option.getD_some, hx, show r < N + (w - 1 - N) by omega] at htr
              have hrw := ih r (by omega) (by omega) (by omega)
              simp only [hr, ite_true] at hrw
              exact (Bool.le_iff_imp.mp (le_trans hrw hle)) htr
            · simp only [h1, h2, ite_false, hx, show i - 1 < N + (w - 1 - N) by omega, ite_true] at htr
              have hle_i := ih i (by omega) (by omega) h2
              simp only [h1, ite_false] at hle_i
              exact (Bool.le_iff_imp.mp hle_i) htr
        · exfalso
          have h1 : ¬ i < N + j := by omega
          have h2 : i ≠ N + j := by omega
          simp only [hx, h1, h2, ite_false, show ¬ i - 1 < N + (w - 1 - N) by omega] at htr
          cases htr
      have hop : (C.gates[w - N]'hk).op = .and ∨ (C.gates[w - N]'hk).op = .or := by
        simpa using (hM (C.gates[w - N]'hk) (List.getElem_mem hk)).1
      rcases hop with hand | hor
      · rw [hand]; simp only [GateOp.eval]
        rw [Bool.le_iff_imp]
        exact bool_le_all (by simp) (fun idx h1 h2 htr => by
          simp only [List.length_map] at h1
          simp only [List.getElem_map, Function.comp_apply] at htr ⊢
          exact hpoint idx h1 htr)
      · rw [hor]; simp only [GateOp.eval]
        rw [Bool.le_iff_imp]
        exact bool_le_any (by simp) (fun idx h1 h2 htr => by
          simp only [List.length_map] at h1
          simp only [List.getElem_map, Function.comp_apply] at htr ⊢
          exact hpoint idx h1 htr)

theorem elimGate_mono_le_eval (N : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (r : ℕ) (hr : r < N + j) (x : List Bool) (hx : x.length = N)
    (hle : (C.wires x).getD r false ≤ (C.wires x).getD (N + j) false) :
    (elimGate N C j (some r)).eval x ≤ C.eval x := by
  unfold Circuit.eval
  set C' := elimGate N C j (some r)
  have hsz' : C'.size = C.size - 1 := elimGate_size N C j hj (some r)
  change (C'.wires x).getD (remapElim N j (N + C.size) (some r) C.output) false ≤ (C.wires x).getD C.output false
  unfold remapElim
  by_cases h1 : C.output < N + j
  · simp only [h1, ite_true]
    simpa [h1] using elimGate_mono_le_wires N C hM j hj r hr x hx hle C.output (by simp [Circuit.size]; omega) (by omega)
  · by_cases h2 : C.output = N + j
    · rw [h2]; simp only [lt_irrefl, ite_false, ite_true, Option.getD_some]
      have hrw := elimGate_mono_le_wires N C hM j hj r hr x hx hle r (by simp [Circuit.size]; omega) (by omega)
      simp only [hr, ite_true] at hrw
      exact le_trans hrw hle
    · simp only [h1, h2, ite_false]
      by_cases hlt : C.output < N + C.size
      · simpa [h1] using elimGate_mono_le_wires N C hM j hj r hr x hx hle C.output hlt h2
      · rw [wires_getD_ge C' x (C.output - 1) (by omega), wires_getD_ge C x C.output (by omega)]

-- 6. Inner_m problem, re-indexing, and minimal circuit properties

def innerInput (m : ℕ) (u v : Fin (m + 1)) : List Bool :=
  (List.range (2 * m)).map fun w =>
    if w < m then decide (u.val = w + 1) else decide (v.val = w - m)

theorem innerInput_length (m : ℕ) (u v : Fin (m + 1)) : (innerInput m u v).length = 2 * m := by
  simp [innerInput]

theorem innerInput_getD_x (m : ℕ) (u v : Fin (m + 1)) (r : ℕ) (hr : r < m) :
    (innerInput m u v).getD r false = decide (u.val = r + 1) := by
  simp [innerInput, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : r < 2 * m), hr]

theorem innerInput_getD_y (m : ℕ) (u v : Fin (m + 1)) (c : ℕ) (hc : c < m) :
    (innerInput m u v).getD (m + c) false = decide (v.val = c) := by
  simp [innerInput, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : m + c < 2 * m),
    show ¬ m + c < m by omega, Nat.add_sub_cancel_left]

def ComputesInner (m : ℕ) (C : Circuit) : Prop :=
  ∀ u v : Fin (m + 1), C.eval (innerInput m u v) = decide (v.val < u.val)

def drop2Map (m r sz w : ℕ) : ℕ :=
  if w = r ∨ w = m + r then 2 * (m - 1) + sz
  else if w < r then w
  else if w < m + r then w - 1
  else w - 2

def drop2Circuit (m r : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (drop2Map m r C.size)⟩, drop2Map m r C.size C.output⟩

theorem drop2Circuit_size (m r : ℕ) (C : Circuit) : (drop2Circuit m r C).size = C.size := by
  simp [drop2Circuit, Circuit.size]

theorem drop2Circuit_mono (m r : ℕ) (C : Circuit) (hM : Monotone2 C) : Monotone2 (drop2Circuit m r C) := by
  intro g hg
  simp only [drop2Circuit, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  exact ⟨(hM g0 hg0).1, by simp [(hM g0 hg0).2]⟩

def embedU (m r : ℕ) (hm : 2 ≤ m) (u' : Fin (m - 1 + 1)) : Fin (m + 1) :=
  ⟨if u'.val ≤ r then u'.val else u'.val + 1, by split <;> omega⟩

def embedV (m r : ℕ) (hm : 2 ≤ m) (v' : Fin (m - 1 + 1)) : Fin (m + 1) :=
  ⟨if v'.val < r then v'.val else v'.val + 1, by split <;> omega⟩

theorem embed_lt_iff (m r : ℕ) (hm : 2 ≤ m) (u' v' : Fin (m - 1 + 1)) :
    ((embedV m r hm v').val < (embedU m r hm u').val) ↔ (v'.val < u'.val) := by
  simp only [embedU, embedV]
  split <;> split <;> omega

theorem drop2Circuit_wires (m r : ℕ) (hm : 2 ≤ m) (hr : r < m) (C : Circuit) (u' v' : Fin (m - 1 + 1)) :
    let x' := innerInput (m - 1) u' v'
    let x := innerInput m (embedU m r hm u') (embedV m r hm v')
    ∀ w < 2 * m + C.size,
      ((drop2Circuit m r C).wires x').getD (drop2Map m r C.size w) false = (C.wires x).getD w false := by
  intro x' x w
  have hx' : x'.length = 2 * (m - 1) := innerInput_length (m - 1) u' v'
  have hx : x.length = 2 * m := innerInput_length m (embedU m r hm u') (embedV m r hm v')
  set C' := drop2Circuit m r C
  have hsz' : C'.size = C.size := drop2Circuit_size m r C
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < 2 * m
    · rw [wires_getD_input C x w (by omega)]
      by_cases hdead : w = r ∨ w = m + r
      · simp only [drop2Map, hdead, ite_true]
        rw [wires_getD_ge C' x' (2 * (m - 1) + C.size) (by omega)]
        rcases hdead with heq | heq
        · rw [heq, innerInput_getD_x m _ _ r hr]
          symm; rw [decide_eq_false_iff_not]; simp only [embedU]; split <;> omega
        · rw [heq, innerInput_getD_y m _ _ r hr]
          symm; rw [decide_eq_false_iff_not]; simp only [embedV]; split <;> omega
      · have hne1 : w ≠ r := fun h => hdead (Or.inl h)
        have hne2 : w ≠ m + r := fun h => hdead (Or.inr h)
        have hdm_lt : drop2Map m r C.size w < 2 * (m - 1) := by
          unfold drop2Map; simp only [hdead, ite_false]; split <;> (try split) <;> omega
        rw [wires_getD_input C' x' _ (by omega)]
        by_cases hwm : w < m
        · rw [innerInput_getD_x m _ _ w hwm]
          by_cases hwr : w < r
          · have hdm : drop2Map m r C.size w = w := by unfold drop2Map; simp [hdead, hwr]
            rw [hdm, innerInput_getD_x (m - 1) u' v' w (by omega)]
            simp only [embedU]; split <;> simp <;> omega
          · have hdm : drop2Map m r C.size w = w - 1 := by
              unfold drop2Map; simp only [hdead, hwr, ite_false, show w < m + r by omega, ite_true]
            rw [hdm, innerInput_getD_x (m - 1) u' v' (w - 1) (by omega)]
            simp only [embedU]; split <;> simp <;> omega
        · have hc : w - m < m := by omega
          have hw_eq : w = m + (w - m) := by omega
          rw [hw_eq, innerInput_getD_y m _ _ (w - m) hc]
          by_cases hcr : w - m < r
          · have hdm : drop2Map m r C.size (m + (w - m)) = (m - 1) + (w - m) := by
              unfold drop2Map
              simp only [show ¬ (m + (w - m) = r ∨ m + (w - m) = m + r) by omega,
                show ¬ m + (w - m) < r by omega, show m + (w - m) < m + r by omega, ite_false, ite_true]
              omega
            rw [hdm, innerInput_getD_y (m - 1) u' v' (w - m) (by omega)]
            simp only [embedV]; split <;> simp <;> omega
          · have hdm : drop2Map m r C.size (m + (w - m)) = (m - 1) + (w - m - 1) := by
              unfold drop2Map
              simp only [show ¬ (m + (w - m) = r ∨ m + (w - m) = m + r) by omega,
                show ¬ m + (w - m) < r by omega, show ¬ m + (w - m) < m + r by omega, ite_false]
              omega
            rw [hdm, innerInput_getD_y (m - 1) u' v' (w - m - 1) (by omega)]
            simp only [embedV]; split <;> simp <;> omega
    · have hdm : drop2Map m r C.size w = w - 2 := by
        unfold drop2Map
        simp only [show ¬ (w = r ∨ w = m + r) by omega, show ¬ w < r by omega,
          show ¬ w < m + r by omega, ite_false]
      rw [hdm]
      have hj : w - 2 * m < C.gates.length := by simp [Circuit.size] at hw; omega
      have hj' : w - 2 * m < C'.gates.length := by simp [C', drop2Circuit]; exact hj
      have heq1 : w - 2 = x'.length + (w - 2 * m) := by omega
      have heq2 : w = x.length + (w - 2 * m) := by omega
      conv_lhs => rw [heq1]
      conv_rhs => rw [heq2]
      rw [wires_getD_gate_full C' x' (w - 2 * m) hj', wires_getD_gate_full C x (w - 2 * m) hj]
      simp only [C', drop2Circuit, List.getElem_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < 2 * m + (w - 2 * m)
      · simp only [hx, hi, ite_true]
        by_cases hdead : i = r ∨ i = m + r
        · have hdm_i : drop2Map m r C.size i = 2 * (m - 1) + C.size := by simp [drop2Map, hdead]
          rw [hdm_i]
          simp only [hx', show ¬ 2 * (m - 1) + C.size < 2 * (m - 1) + (w - 2 * m) by omega, ite_false]
          rw [wires_getD_input C x i (by omega)]
          rcases hdead with heq | heq
          · rw [heq, innerInput_getD_x m _ _ r hr]
            symm; rw [decide_eq_false_iff_not]; simp only [embedU]; split <;> omega
          · rw [heq, innerInput_getD_y m _ _ r hr]
            symm; rw [decide_eq_false_iff_not]; simp only [embedV]; split <;> omega
        · have hdm_lt : drop2Map m r C.size i < 2 * (m - 1) + (w - 2 * m) := by
            unfold drop2Map; simp only [hdead, ite_false]; split <;> (try split) <;> omega
          simp only [hx', hdm_lt, ite_true]
          exact ih i (by omega) (by omega)
      · simp only [hx, hi, ite_false]
        have hdm_ge : ¬ drop2Map m r C.size i < 2 * (m - 1) + (w - 2 * m) := by
          unfold drop2Map
          simp only [show ¬ (i = r ∨ i = m + r) by omega, show ¬ i < r by omega,
            show ¬ i < m + r by omega, ite_false]; omega
        simp only [hx', hdm_ge, ite_false]

theorem drop2Circuit_computes (m r : ℕ) (hm : 2 ≤ m) (hr : r < m) (C : Circuit)
    (hC : ∀ u' v' : Fin (m - 1 + 1), C.eval (innerInput m (embedU m r hm u') (embedV m r hm v')) = decide (v'.val < u'.val)) :
    ComputesInner (m - 1) (drop2Circuit m r C) := by
  intro u' v'
  rw [← hC u' v']
  unfold Circuit.eval
  set C' := drop2Circuit m r C
  have hsz' : C'.size = C.size := drop2Circuit_size m r C
  have hx' := innerInput_length (m - 1) u' v'
  have hx := innerInput_length m (embedU m r hm u') (embedV m r hm v')
  by_cases hout : C.output < 2 * m + C.size
  · exact drop2Circuit_wires m r hm hr C u' v' C.output hout
  · change (C'.wires _).getD (drop2Map m r C.size C.output) false = (C.wires _).getD C.output false
    have hdm_ge : 2 * (m - 1) + C'.size ≤ drop2Map m r C.size C.output := by
      unfold drop2Map
      simp only [show ¬ (C.output = r ∨ C.output = m + r) by omega, show ¬ C.output < r by omega,
        show ¬ C.output < m + r by omega, ite_false]; omega
    rw [wires_getD_ge C' _ _ (by rw [hx']; exact hdm_ge), wires_getD_ge C _ _ (by rw [hx]; omega)]

-- Minimal Inner_m circuit structural properties
theorem min_inner_props (m : ℕ) (hm : 1 ≤ m) (C : Circuit) (hM : Monotone2 C) (hC : ComputesInner m C)
    (hmin : ∀ C', Monotone2 C' → ComputesInner m C' → C.size ≤ C'.size) :
    (∀ (j : ℕ) (hj : j < C.gates.length),
      ∃ a b, ((C.gates[j]'hj).op = .and ∨ (C.gates[j]'hj).op = .or) ∧
        (C.gates[j]'hj).inputs = [a, b] ∧ a < 2 * m + j ∧ b < 2 * m + j ∧ a ≠ b) ∧
    (2 * m ≤ C.output ∧ C.output < 2 * m + C.size ∧ 1 ≤ C.size) ∧
    (∀ w < 2 * m, ∃ (j : ℕ) (hj : j < C.gates.length), w ∈ (C.gates[j]'hj).inputs) ∧
    (∀ (j : ℕ) (hj : j < C.gates.length), 2 * m + j ≠ C.output →
      ∃ (j' : ℕ) (hj' : j' < C.gates.length), j < j' ∧ 2 * m + j ∈ (C.gates[j']'hj').inputs) ∧
    (∀ (j1 : ℕ) (hj1 : j1 < C.gates.length) (j2 : ℕ) (hj2 : j2 < C.gates.length), j1 < j2 →
      ∀ w ∈ (C.gates[j1]'hj1).inputs,
      ¬ (2 * m + j1 ∈ (C.gates[j2]'hj2).inputs ∧ w ∈ (C.gates[j2]'hj2).inputs)) := by
  have hall_kept : ∀ j (hj : j < C.gates.length),
      ∃ nw, (simpRes (2 * m) (fun _ => false) C).1[j]? = some (.kept nw) := by
    have hnt : resolveWire (2 * m) (fun _ => false) (simpRes (2 * m) (fun _ => false) C).1 C.output ≠ .vtrue := by
      intro hvt
      have hE := (simpRes_props (2 * m) (fun _ => false) C hM).2.2 (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
        (innerInput_length m _ _) (fun _ _ h => by cases h)
      have hout := hE.2 C.output
      rw [hvt] at hout
      have h0 := hC ⟨0, by omega⟩ ⟨m, by omega⟩
      unfold Circuit.eval at h0
      rw [h0] at hout
      simp [evalWVal] at hout
    have hle := hmin (simpCircuit (2 * m) (fun _ => false) C) (simpCircuit_mono _ _ C hM) (fun u v => by
      rw [simpCircuit_eval (2 * m) (fun _ => false) C hM _ (innerInput_length m u v) (fun _ _ h => by cases h)]
      exact hC u v)
    rw [simpCircuit_size_of_not_vtrue (2 * m) (fun _ => false) C hM hnt] at hle
    have hlen := (simpRes_props (2 * m) (fun _ => false) C hM).1
    intro j hj
    have hj' : j < (simpRes (2 * m) (fun _ => false) C).1.length := by simp [Circuit.size] at hlen; omega
    set s := (simpRes (2 * m) (fun _ => false) C).1[j]'hj'
    have hs : (simpRes (2 * m) (fun _ => false) C).1[j]? = some s := List.getElem?_eq_getElem hj'
    by_cases hsk : s.isKept = true
    · cases hs_eq : s with
      | cfalse => rw [hs_eq] at hsk; cases hsk
      | ctrue => rw [hs_eq] at hsk; cases hsk
      | wref _ => rw [hs_eq] at hsk; cases hsk
      | kept nw => rw [hs_eq] at hs; exact ⟨nw, hs⟩
    · have hsf : s.isKept = false := Bool.eq_false_iff.mpr hsk
      have hbd := countP_add_card_false (simpRes (2 * m) (fun _ => false) C).1 WStatus.isKept {j}
        (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact ⟨s, hs, hsf⟩)
      simp only [Finset.card_singleton] at hbd
      omega
  have hshape := simpRes_all_kept_shape (2 * m) C hM hall_kept
  have hout_ge : 2 * m ≤ C.output := by
    by_contra hlt; push Not at hlt
    by_cases hwm : C.output < m
    · have h1 := hC ⟨C.output + 1, by omega⟩ ⟨m, by omega⟩
      unfold Circuit.eval at h1
      rw [wires_getD_input C _ C.output (by rw [innerInput_length]; omega),
          innerInput_getD_x m _ _ C.output hwm] at h1
      simp at h1; omega
    · have h1 := hC ⟨0, by omega⟩ ⟨C.output - m, by omega⟩
      unfold Circuit.eval at h1
      rw [wires_getD_input C _ C.output (by rw [innerInput_length]; omega)] at h1
      have h1' := innerInput_getD_y m ⟨0, by omega⟩ ⟨C.output - m, by omega⟩ (C.output - m) (by omega)
      have heq : m + (C.output - m) = C.output := by omega
      rw [heq] at h1'
      rw [h1'] at h1
      simp at h1
  have hout_lt : C.output < 2 * m + C.size := by
    by_contra hge; push Not at hge
    have h1 := hC ⟨1, by omega⟩ ⟨0, by omega⟩
    unfold Circuit.eval at h1
    rw [wires_getD_ge C _ C.output (by rw [innerInput_length]; omega)] at h1
    simp at h1
  have hsz_pos : 1 ≤ C.size := by omega
  have hin_fan : ∀ w < 2 * m, ∃ (j : ℕ) (hj : j < C.gates.length), w ∈ (C.gates[j]'hj).inputs := by
    intro w hw
    by_contra hno; push Not at hno
    by_cases hwm : w < m
    · have heq := wires_eq_of_unread (2 * m) C (fun i => i = w)
        (innerInput m ⟨w + 1, by omega⟩ ⟨w, by omega⟩)
        (innerInput m ⟨0, by omega⟩ ⟨w, by omega⟩)
        (innerInput_length m _ _) (innerInput_length m _ _)
        (fun i hi hne => by
          by_cases him : i < m
          · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
            simp only [decide_eq_decide]; omega
          · have heqi : m + (i - m) = i := by omega
            have ha := innerInput_getD_y m ⟨w + 1, by omega⟩ ⟨w, by omega⟩ (i - m) (by omega)
            have hb := innerInput_getD_y m ⟨0, by omega⟩ ⟨w, by omega⟩ (i - m) (by omega)
            rw [heqi] at ha hb; rw [ha, hb])
        C.gates.length (le_refl _) (fun j hj u hu hequ => hno j hj (hequ ▸ hu))
        C.output hout_lt (by omega)
      have h1 := hC ⟨w + 1, by omega⟩ ⟨w, by omega⟩
      have h2 := hC ⟨0, by omega⟩ ⟨w, by omega⟩
      unfold Circuit.eval at h1 h2; rw [heq, h2] at h1; simp at h1
    · set c := w - m
      have hc : c < m := by omega
      have heq := wires_eq_of_unread (2 * m) C (fun i => i = w)
        (innerInput m ⟨c + 1, by omega⟩ ⟨c, by omega⟩)
        (innerInput m ⟨c + 1, by omega⟩ ⟨m, by omega⟩)
        (innerInput_length m _ _) (innerInput_length m _ _)
        (fun i hi hne => by
          by_cases him : i < m
          · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
          · have heqi : m + (i - m) = i := by omega
            have ha := innerInput_getD_y m ⟨c + 1, by omega⟩ ⟨c, by omega⟩ (i - m) (by omega)
            have hb := innerInput_getD_y m ⟨c + 1, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
            rw [heqi] at ha hb; rw [ha, hb]
            simp only [decide_eq_decide]; omega)
        C.gates.length (le_refl _) (fun j hj u hu hequ => hno j hj (hequ ▸ hu))
        C.output hout_lt (by omega)
      have h1 := hC ⟨c + 1, by omega⟩ ⟨c, by omega⟩
      have h2 := hC ⟨c + 1, by omega⟩ ⟨m, by omega⟩
      unfold Circuit.eval at h1 h2; rw [heq, h2] at h1; simp at h1; omega
  have hgate_fan : ∀ (j : ℕ) (hj : j < C.gates.length), 2 * m + j ≠ C.output →
      ∃ (j' : ℕ) (hj' : j' < C.gates.length), j < j' ∧ 2 * m + j ∈ (C.gates[j']'hj').inputs := by
    intro j hj hne
    by_contra hno; push Not at hno
    have hle := hmin (elimGate (2 * m) C j none) (elimGate_mono (2 * m) C hM j none) (fun u v => by
      rw [elimGate_unused_eval (2 * m) C j hj (fun j' hj' hlt => hno j' hj' hlt) hne.symm _ (innerInput_length m u v)]
      exact hC u v)
    have hsz := elimGate_size (2 * m) C j hj none
    simp [Circuit.size] at hle hsz; omega
  have hno_abs : ∀ (j1 : ℕ) (hj1 : j1 < C.gates.length) (j2 : ℕ) (hj2 : j2 < C.gates.length), j1 < j2 →
      ∀ w ∈ (C.gates[j1]'hj1).inputs,
      ¬ (2 * m + j1 ∈ (C.gates[j2]'hj2).inputs ∧ w ∈ (C.gates[j2]'hj2).inputs) := by
    intro j1 hj1 j2 hj2 h12 w hw1 ⟨hm1, hmw⟩
    rcases hshape j1 hj1 with ⟨a1, b1, hop1, hin1, ha1, hb1, hab1⟩
    rcases hshape j2 hj2 with ⟨a2, b2, hop2, hin2, ha2, hb2, hab2⟩
    have hw_lt : w < 2 * m + j1 := by
      rw [hin1] at hw1; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1
      rcases hw1 with rfl | rfl <;> omega
    have hw_eq : (w = a1 ∨ w = b1) := by
      rw [hin1] at hw1; simpa using hw1
    have hpair : (a2 = 2 * m + j1 ∧ b2 = w) ∨ (a2 = w ∧ b2 = 2 * m + j1) := by
      rw [hin2] at hm1 hmw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1 hmw
      rcases hm1 with h1 | h1 <;> rcases hmw with h2 | h2
      · omega
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
      · omega
    have hgate_val : ∀ (x : List Bool), x.length = 2 * m →
        (C.wires x).getD (2 * m + j1) false =
          (match (C.gates[j1]'hj1).op with
           | .and => (C.wires x).getD a1 false && (C.wires x).getD b1 false
           | _ => (C.wires x).getD a1 false || (C.wires x).getD b1 false) ∧
        (C.wires x).getD (2 * m + j2) false =
          (match (C.gates[j2]'hj2).op with
           | .and => (C.wires x).getD a2 false && (C.wires x).getD b2 false
           | _ => (C.wires x).getD a2 false || (C.wires x).getD b2 false) := by
      intro x hx
      constructor
      · conv_lhs => rw [show 2 * m + j1 = x.length + j1 by omega]
        rw [wires_getD_gate_full C x j1 hj1, hin1]
        rcases hop1 with h | h <;> simp [h, GateOp.eval, hx, ha1, hb1]
      · conv_lhs => rw [show 2 * m + j2 = x.length + j2 by omega]
        rw [wires_getD_gate_full C x j2 hj2, hin2]
        rcases hop2 with h | h <;> simp [h, GateOp.eval, hx, ha2, hb2]
    have hrep_ex : ∃ rep < 2 * m + j2, ∀ (x : List Bool), x.length = 2 * m →
        (C.wires x).getD (2 * m + j2) false = (C.wires x).getD rep false := by
      rcases hop1 with h1 | h1 <;> rcases hop2 with h2 | h2
      · refine ⟨2 * m + j1, by omega, fun x hx => ?_⟩
        have ⟨hv1, hv2⟩ := hgate_val x hx
        rw [h1] at hv1; rw [h2] at hv2; dsimp only at hv1 hv2
        rcases hpair with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> rcases hw_eq with h1w | h1w <;>
          rw [hv2, h2a, h2b, hv1, h1w] <;> cases (C.wires x).getD a1 false <;> cases (C.wires x).getD b1 false <;> rfl
      · refine ⟨w, by omega, fun x hx => ?_⟩
        have ⟨hv1, hv2⟩ := hgate_val x hx
        rw [h1] at hv1; rw [h2] at hv2; dsimp only at hv1 hv2
        rcases hpair with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> rcases hw_eq with h1w | h1w <;>
          rw [hv2, h2a, h2b, hv1, h1w] <;> cases (C.wires x).getD a1 false <;> cases (C.wires x).getD b1 false <;> rfl
      · refine ⟨w, by omega, fun x hx => ?_⟩
        have ⟨hv1, hv2⟩ := hgate_val x hx
        rw [h1] at hv1; rw [h2] at hv2; dsimp only at hv1 hv2
        rcases hpair with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> rcases hw_eq with h1w | h1w <;>
          rw [hv2, h2a, h2b, hv1, h1w] <;> cases (C.wires x).getD a1 false <;> cases (C.wires x).getD b1 false <;> rfl
      · refine ⟨2 * m + j1, by omega, fun x hx => ?_⟩
        have ⟨hv1, hv2⟩ := hgate_val x hx
        rw [h1] at hv1; rw [h2] at hv2; dsimp only at hv1 hv2
        rcases hpair with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> rcases hw_eq with h1w | h1w <;>
          rw [hv2, h2a, h2b, hv1, h1w] <;> cases (C.wires x).getD a1 false <;> cases (C.wires x).getD b1 false <;> rfl
    rcases hrep_ex with ⟨rep, hrep_lt, hrep_eq⟩
    have hle := hmin (elimGate (2 * m) C j2 (some rep)) (elimGate_mono (2 * m) C hM j2 (some rep)) (fun u v => by
      rw [elimGate_eval (2 * m) C j2 hj2 (some rep) (fun _ hr => by cases hr; exact hrep_lt)
        _ (innerInput_length m u v) (hrep_eq _ (innerInput_length m u v))]
      exact hC u v)
    have hsz := elimGate_size (2 * m) C j2 hj2 (some rep)
    simp [Circuit.size] at hle hsz; omega
  exact ⟨hshape, ⟨hout_ge, hout_lt, hsz_pos⟩, hin_fan, hgate_fan, hno_abs⟩

-- 7. Stage 3b: Inner_m >= 3m - 2 (Case 1 + Case 2 + Induction)

theorem gate_val_and (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hop : (C.gates[j]'hj).op = .and) (hin : (C.gates[j]'hj).inputs = [a, b])
    (x : List Bool) (ha : a < x.length + j) (hb : b < x.length + j) :
    (C.wires x).getD (x.length + j) false = ((C.wires x).getD a false && (C.wires x).getD b false) := by
  rw [wires_getD_gate_full C x j hj, hop, hin]
  simp [GateOp.eval, ha, hb]

theorem gate_val_or (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hop : (C.gates[j]'hj).op = .or) (hin : (C.gates[j]'hj).inputs = [a, b])
    (x : List Bool) (ha : a < x.length + j) (hb : b < x.length + j) :
    (C.wires x).getD (x.length + j) false = ((C.wires x).getD a false || (C.wires x).getD b false) := by
  rw [wires_getD_gate_full C x j hj, hop, hin]
  simp [GateOp.eval, ha, hb]

theorem case1_three_deleted (m : ℕ) (hm : 2 ≤ m) (C : Circuit) (hM : Monotone2 C) (hC : ComputesInner m C)
    (hmin : ∀ C', Monotone2 C' → ComputesInner m C' → C.size ≤ C'.size)
    (r : ℕ) (hr : r < m) (w1 w2 : ℕ) (hw12 : (w1 = r ∧ w2 = m + r) ∨ (w1 = m + r ∧ w2 = r))
    (hcase : (∃ (j1 : ℕ) (hj1 : j1 < C.gates.length) (j2 : ℕ) (hj2 : j2 < C.gates.length),
        j1 ≠ j2 ∧ w1 ∈ (C.gates[j1]'hj1).inputs ∧ w1 ∈ (C.gates[j2]'hj2).inputs) ∨
      (∃ (j1 : ℕ) (hj1 : j1 < C.gates.length),
        (C.gates[j1]'hj1).op = .and ∧ w1 ∈ (C.gates[j1]'hj1).inputs)) :
    let Z : ℕ → Bool := fun w => decide (w = r ∨ w = m + r)
    (simpCircuit (2 * m) Z C).size + 3 ≤ C.size := by
  intro Z
  have ⟨hshape, ⟨hout_ge, hout_lt, hsz_pos⟩, hin_fan, hgate_fan, hno_abs⟩ := min_inner_props m (by omega) C hM hC hmin
  have hst_len : (simpRes (2 * m) Z C).1.length = C.size := (simpRes_props (2 * m) Z C hM).1
  have hnt : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 C.output ≠ .vtrue := by
    intro hvt
    have hE := (simpRes_props (2 * m) Z C hM).2.2 (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
      (innerInput_length m _ _) (fun i hi hzi => by
        by_cases him : i < m
        · rw [innerInput_getD_x m _ _ i him]; simp
        · have heqi : m + (i - m) = i := by omega
          have hy := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
          rw [heqi] at hy; rw [hy]; simp; omega)
    have hout := hE.2 C.output
    rw [hvt] at hout
    have h0 := hC ⟨0, by omega⟩ ⟨m, by omega⟩
    unfold Circuit.eval at h0; rw [h0] at hout; simp [evalWVal] at hout
  rw [simpCircuit_size_of_not_vtrue (2 * m) Z C hM hnt]
  have hw1_lt : w1 < 2 * m := by rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hw2_lt : w2 < 2 * m := by rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hw1_ne_w2 : w1 ≠ w2 := by rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hrv1 : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 w1 = .vfalse := by
    unfold resolveWire; simp only [hw1_lt, ite_true]
    have : Z w1 = true := by rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Z]
    simp [this]
  have hrv2 : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 w2 = .vfalse := by
    unfold resolveWire; simp only [hw2_lt, ite_true]
    have : Z w2 = true := by rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Z]
    simp [this]
  have hdel_of_in : ∀ (j : ℕ) (hj : j < C.gates.length) (w : ℕ),
      w ∈ (C.gates[j]'hj).inputs → resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 w = .vfalse →
      ∃ s, (simpRes (2 * m) Z C).1[j]? = some s ∧ s.isKept = false := by
    intro j hj w hw hrv
    rcases hshape j hj with ⟨a, b, hop, hin, ha, hb, _⟩
    rw [hin] at hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    apply simpRes_not_kept_of_vfalse (2 * m) Z C j hj a b hop hin ha hb
    rcases hw with rfl | rfl
    · exact Or.inl hrv
    · exact Or.inr hrv
  have hboth_not_out : ∀ (j : ℕ) (hj : j < C.gates.length),
      w1 ∈ (C.gates[j]'hj).inputs → w2 ∈ (C.gates[j]'hj).inputs → 2 * m + j ≠ C.output := by
    intro j hj h1 h2 hout
    rcases hshape j hj with ⟨a, b, hop, hin, ha, hb, hab⟩
    set r' := if r = 0 then 1 else 0
    have hr'_lt : r' < m := by simp only [r']; split <;> omega
    have hr'_ne : r' ≠ r := by simp only [r']; split <;> omega
    have hx := innerInput_length m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩
    have hval0 : ∀ w, (w = r ∨ w = m + r) → (C.wires (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩)).getD w false = false := by
      intro w hw
      rw [wires_getD_input C _ w (by rw [hx]; rcases hw with hwr | hwr <;> omega)]
      rcases hw with hwr | hwr
      · rw [hwr, innerInput_getD_x m _ _ r hr]; simp; omega
      · rw [hwr, innerInput_getD_y m _ _ r hr]; simp; omega
    have hpair : (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1) := by
      rw [hin] at h1 h2; simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · omega
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
      · omega
    have hga : (C.wires (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩)).getD a false = false := by
      apply hval0; rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have hgb : (C.wires (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩)).getD b false = false := by
      apply hval0; rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have hev := hC ⟨r' + 1, by omega⟩ ⟨r', by omega⟩
    unfold Circuit.eval at hev
    rw [← hout, show 2 * m + j = (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩).length + j by omega] at hev
    rcases hop with h | h
    · rw [gate_val_and C j hj a b h hin _ (by omega) (by omega), hga, hgb] at hev; simp at hev
    · rw [gate_val_or C j hj a b h hin _ (by omega) (by omega), hga, hgb] at hev; simp at hev
  have hgoal_of_3 : ∀ (k1 k2 k3 : ℕ), k1 ≠ k2 → k1 ≠ k3 → k2 ≠ k3 →
      (∃ s, (simpRes (2 * m) Z C).1[k1]? = some s ∧ s.isKept = false) →
      (∃ s, (simpRes (2 * m) Z C).1[k2]? = some s ∧ s.isKept = false) →
      (∃ s, (simpRes (2 * m) Z C).1[k3]? = some s ∧ s.isKept = false) →
      (simpRes (2 * m) Z C).1.countP WStatus.isKept + 3 ≤ C.size := by
    intro k1 k2 k3 h12 h13 h23 hd1 hd2 hd3
    have hcard : ({k1, k2, k3} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
    have hbd := countP_add_card_false (simpRes (2 * m) Z C).1 WStatus.isKept {k1, k2, k3} (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact hd1
      · exact hd2
      · exact hd3)
    omega
  rcases hin_fan w2 hw2_lt with ⟨gy, hgy, hwy⟩
  rcases hcase with ⟨g1, hg1, g2, hg2, hne12, hw1_g1, hw1_g2⟩ | ⟨g1, hg1, hand1, hw1_g1⟩
  · -- Subcase 1a: w1 read by two distinct gates g1, g2
    have hdel1 := hdel_of_in g1 hg1 w1 hw1_g1 hrv1
    have hdel2 := hdel_of_in g2 hg2 w1 hw1_g2 hrv1
    have hdely := hdel_of_in gy hgy w2 hwy hrv2
    by_cases hgy1 : gy = g1
    · subst hgy1
      rcases hshape gy hg1 with ⟨a, b, hop, hin, ha, hb, _⟩
      have hrv_g : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 (2 * m + gy) = .vfalse := by
        have hpair : (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1) := by
          rw [hin] at hw1_g1 hwy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g1 hwy
          rcases hw1_g1 with h1 | h1 <;> rcases hwy with h2 | h2
          · omega
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h2.symm, h1.symm⟩
          · omega
        apply simpRes_cfalse_of_both_vfalse (2 * m) Z C gy hg1 a b hop hin ha hb
        · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv1; exact hrv2
        · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv2; exact hrv1
      have hne_out := hboth_not_out gy hg1 hw1_g1 hwy
      rcases hgate_fan gy hg1 hne_out with ⟨h1, hh1, hlt1, hmg1⟩
      have hdel_h1 := hdel_of_in h1 hh1 (2 * m + gy) hmg1 hrv_g
      by_cases hh1g2 : h1 = g2
      · subst hh1g2; exact (hno_abs gy hg1 h1 hh1 hlt1 w1 hw1_g1 ⟨hmg1, hw1_g2⟩).elim
      · exact hgoal_of_3 gy g2 h1 hne12 (by omega) (Ne.symm hh1g2) hdel1 hdel2 hdel_h1
    · by_cases hgy2 : gy = g2
      · subst hgy2
        rcases hshape gy hg2 with ⟨a, b, hop, hin, ha, hb, _⟩
        have hrv_g : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 (2 * m + gy) = .vfalse := by
          have hpair : (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1) := by
            rw [hin] at hw1_g2 hwy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g2 hwy
            rcases hw1_g2 with h1 | h1 <;> rcases hwy with h2 | h2
            · omega
            · exact Or.inl ⟨h1.symm, h2.symm⟩
            · exact Or.inr ⟨h2.symm, h1.symm⟩
            · omega
          apply simpRes_cfalse_of_both_vfalse (2 * m) Z C gy hg2 a b hop hin ha hb
          · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv1; exact hrv2
          · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv2; exact hrv1
        have hne_out := hboth_not_out gy hg2 hw1_g2 hwy
        rcases hgate_fan gy hg2 hne_out with ⟨h1, hh1, hlt1, hmg1⟩
        have hdel_h1 := hdel_of_in h1 hh1 (2 * m + gy) hmg1 hrv_g
        by_cases hh1g1 : h1 = g1
        · subst hh1g1; exact (hno_abs gy hg2 h1 hh1 hlt1 w1 hw1_g2 ⟨hmg1, hw1_g1⟩).elim
        · exact hgoal_of_3 g1 gy h1 hne12 (Ne.symm hh1g1) (by omega) hdel1 hdel2 hdel_h1
      · exact hgoal_of_3 g1 g2 gy hne12 (Ne.symm hgy1) (Ne.symm hgy2) hdel1 hdel2 hdely
  · -- Subcase 1b: w1 feeds AND gate g1
    by_cases hfan2 : ∃ (g2 : ℕ) (hg2 : g2 < C.gates.length), g2 ≠ g1 ∧ w1 ∈ (C.gates[g2]'hg2).inputs
    · -- Already handled by Subcase 1a; reuse directly via a helper or repeat cleanly
      rcases hfan2 with ⟨g2, hg2, hne21, hw1_g2⟩
      have hdel1 := hdel_of_in g1 hg1 w1 hw1_g1 hrv1
      have hdel2 := hdel_of_in g2 hg2 w1 hw1_g2 hrv1
      have hdely := hdel_of_in gy hgy w2 hwy hrv2
      by_cases hgy1 : gy = g1
      · subst hgy1
        rcases hshape gy hg1 with ⟨a, b, hop, hin, ha, hb, _⟩
        have hrv_g : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 (2 * m + gy) = .vfalse := by
          apply simpRes_cfalse_of_and_vfalse (2 * m) Z C gy hg1 a b hand1 hin ha hb
          rw [hin] at hw1_g1; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g1
          rcases hw1_g1 with rfl | rfl; exact Or.inl hrv1; exact Or.inr hrv1
        rcases hgate_fan gy hg1 (hboth_not_out gy hg1 hw1_g1 hwy) with ⟨h1, hh1, hlt1, hmg1⟩
        have hdel_h1 := hdel_of_in h1 hh1 (2 * m + gy) hmg1 hrv_g
        by_cases hh1g2 : h1 = g2
        · subst hh1g2; exact (hno_abs gy hg1 h1 hh1 hlt1 w1 hw1_g1 ⟨hmg1, hw1_g2⟩).elim
        · exact hgoal_of_3 gy g2 h1 (Ne.symm hne21) (by omega) (Ne.symm hh1g2) hdel1 hdel2 hdel_h1
      · by_cases hgy2 : gy = g2
        · subst hgy2
          rcases hshape gy hg2 with ⟨a, b, hop, hin, ha, hb, _⟩
          have hrv_g : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 (2 * m + gy) = .vfalse := by
            have hpair : (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1) := by
              rw [hin] at hw1_g2 hwy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g2 hwy
              rcases hw1_g2 with h1 | h1 <;> rcases hwy with h2 | h2
              · omega
              · exact Or.inl ⟨h1.symm, h2.symm⟩
              · exact Or.inr ⟨h2.symm, h1.symm⟩
              · omega
            apply simpRes_cfalse_of_both_vfalse (2 * m) Z C gy hg2 a b hop hin ha hb
            · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv1; exact hrv2
            · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv2; exact hrv1
          rcases hgate_fan gy hg2 (hboth_not_out gy hg2 hw1_g2 hwy) with ⟨h1, hh1, hlt1, hmg1⟩
          have hdel_h1 := hdel_of_in h1 hh1 (2 * m + gy) hmg1 hrv_g
          by_cases hh1g1 : h1 = g1
          · subst hh1g1; exact (hno_abs gy hg2 h1 hh1 hlt1 w1 hw1_g2 ⟨hmg1, hw1_g1⟩).elim
          · exact hgoal_of_3 g1 gy h1 (Ne.symm hne21) (Ne.symm hh1g1) (by omega) hdel1 hdel2 hdel_h1
        · exact hgoal_of_3 g1 g2 gy (Ne.symm hne21) (Ne.symm hgy1) (Ne.symm hgy2) hdel1 hdel2 hdely
    · push Not at hfan2
      rcases hshape g1 hg1 with ⟨a1, b1, _, hin1, ha1, hb1, _⟩
      have hdel1 := hdel_of_in g1 hg1 w1 hw1_g1 hrv1
      have hrv_g1 : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 (2 * m + g1) = .vfalse := by
        apply simpRes_cfalse_of_and_vfalse (2 * m) Z C g1 hg1 a1 b1 hand1 hin1 ha1 hb1
        rw [hin1] at hw1_g1; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g1
        rcases hw1_g1 with rfl | rfl; exact Or.inl hrv1; exact Or.inr hrv1
      have hg1_ne_out : 2 * m + g1 ≠ C.output := by
        intro hout
        set r' := if r = 0 then 1 else 0
        have hr'_lt : r' < m := by simp only [r']; split <;> omega
        have hr'_ne : r' ≠ r := by simp only [r']; split <;> omega
        have hx := innerInput_length m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩
        have hw1_f : (C.wires (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩)).getD w1 false = false := by
          rw [wires_getD_input C _ w1 (by rw [hx]; omega)]
          rcases hw12 with ⟨hw1r, _⟩ | ⟨hw1r, _⟩
          · rw [hw1r, innerInput_getD_x m _ _ r hr]; simp; omega
          · rw [hw1r, innerInput_getD_y m _ _ r hr]; simp; omega
        have hev := hC ⟨r' + 1, by omega⟩ ⟨r', by omega⟩
        unfold Circuit.eval at hev
        rw [← hout, show 2 * m + g1 = (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩).length + g1 by omega,
            gate_val_and C g1 hg1 a1 b1 hand1 hin1 _ (by omega) (by omega)] at hev
        rw [hin1] at hw1_g1; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g1
        rcases hw1_g1 with rfl | rfl <;> (rw [hw1_f] at hev; simp at hev)
      rcases hgate_fan g1 hg1 hg1_ne_out with ⟨h1, hh1, hlt_g1_h1, hmg1⟩
      have hdel_h1 := hdel_of_in h1 hh1 (2 * m + g1) hmg1 hrv_g1
      have hdely := hdel_of_in gy hgy w2 hwy hrv2
      by_cases hgy1 : gy = g1
      · subst hgy1
        -- g1 = w1 && w2; prove w2 is read by some g' != g1
        have hex_g' : ∃ (g' : ℕ) (hg' : g' < C.gates.length), g' ≠ gy ∧ w2 ∈ (C.gates[g']'hg').inputs := by
          by_contra hno; push Not at hno
          have hno_both : ∀ (j : ℕ) (hj : j < C.gates.length), j ≠ gy →
              r ∉ (C.gates[j]'hj).inputs ∧ m + r ∉ (C.gates[j]'hj).inputs := by
            intro j hj hne
            rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨hfan2 j hj hne, hno j hj hne⟩
            · exact ⟨hno j hj hne, hfan2 j hj hne⟩
          have hpair : (a1 = r ∧ b1 = m + r) ∨ (a1 = m + r ∧ b1 = r) := by
            rw [hin1] at hw1_g1 hwy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1_g1 hwy
            rcases hw12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw1_g1 with h1 | h1 <;> rcases hwy with h2 | h2 <;>
              (try omega) <;> simp [h1, h2]
          by_cases hrm1 : r < m - 1
          · -- Compare (m, r) vs (m, m): x_r = false at both, so g1 = false at both
            set x1 := innerInput m ⟨m, by omega⟩ ⟨r, by omega⟩
            set x2 := innerInput m ⟨m, by omega⟩ ⟨m, by omega⟩
            have hx1_len : x1.length = 2 * m := innerInput_length m _ _
            have hle := wires_mono_except C hM x1 x2 (by simp [x1, x2, innerInput_length])
              (fun w => w = r ∨ w = m + r)
              (fun i hi hne htr => by
                have hi2 : i < 2 * m := by omega
                by_cases him : i < m
                · rw [innerInput_getD_x m _ _ i him] at htr ⊢; exact htr
                · have heqi : m + (i - m) = i := by omega
                  have ha := innerInput_getD_y m ⟨m, by omega⟩ ⟨r, by omega⟩ (i - m) (by omega)
                  rw [heqi] at ha; rw [ha] at htr; simp at htr; omega)
              (fun j hj ⟨i, hi, hexi⟩ htr => by
                by_cases hjg : j = gy
                · rw [hjg] at htr
                  rw [gate_val_and C gy hg1 a1 b1 hand1 hin1 x1 (by omega) (by omega)] at htr
                  have hxr : (C.wires x1).getD r false = false := by
                    rw [wires_getD_input C x1 r (by omega), innerInput_getD_x m _ _ r hr]
                    simp; omega
                  rcases hpair with ⟨ha1r, hb1r⟩ | ⟨ha1r, hb1r⟩
                  · rw [ha1r, hxr] at htr; simp at htr
                  · rw [hb1r, hxr] at htr; simp at htr
                · exfalso; rcases hexi with hir | hir
                  · exact (hno_both j hj hjg).1 (hir ▸ hi)
                  · exact (hno_both j hj hjg).2 (hir ▸ hi))
              C.output (by omega) (by
                have h1 := hC ⟨m, by omega⟩ ⟨r, by omega⟩; unfold Circuit.eval at h1; simpa [x1, hr] using h1)
            have h2 := hC ⟨m, by omega⟩ ⟨m, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2
          · -- r = m - 1 >= 1: compare (m, 0) vs (0, 0), y_r = false at both
            set x1 := innerInput m ⟨m, by omega⟩ ⟨0, by omega⟩
            set x2 := innerInput m ⟨0, by omega⟩ ⟨0, by omega⟩
            have hx1_len : x1.length = 2 * m := innerInput_length m _ _
            have hle := wires_mono_except C hM x1 x2 (by simp [x1, x2, innerInput_length])
              (fun w => w = r ∨ w = m + r)
              (fun i hi hne htr => by
                have hi2 : i < 2 * m := by omega
                by_cases him : i < m
                · rw [innerInput_getD_x m _ _ i him] at htr ⊢; simp at htr; omega
                · have heqi : m + (i - m) = i := by omega
                  have ha := innerInput_getD_y m ⟨m, by omega⟩ ⟨0, by omega⟩ (i - m) (by omega)
                  have hb := innerInput_getD_y m ⟨0, by omega⟩ ⟨0, by omega⟩ (i - m) (by omega)
                  rw [heqi] at ha hb; rw [ha] at htr; rw [hb]; exact htr)
              (fun j hj ⟨i, hi, hexi⟩ htr => by
                by_cases hjg : j = gy
                · rw [hjg] at htr
                  rw [gate_val_and C gy hg1 a1 b1 hand1 hin1 x1 (by omega) (by omega)] at htr
                  have hyr : (C.wires x1).getD (m + r) false = false := by
                    rw [wires_getD_input C x1 (m + r) (by omega), innerInput_getD_y m _ _ r hr]
                    simp; omega
                  rcases hpair with ⟨ha1r, hb1r⟩ | ⟨ha1r, hb1r⟩
                  · rw [hb1r, hyr] at htr; simp at htr
                  · rw [ha1r, hyr] at htr; simp at htr
                · exfalso; rcases hexi with hir | hir
                  · exact (hno_both j hj hjg).1 (hir ▸ hi)
                  · exact (hno_both j hj hjg).2 (hir ▸ hi))
              C.output (by omega) (by
                have h1 := hC ⟨m, by omega⟩ ⟨0, by omega⟩; unfold Circuit.eval at h1; simpa [x1, show 0 < m by omega] using h1)
            have h2 := hC ⟨0, by omega⟩ ⟨0, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2
        rcases hex_g' with ⟨g', hg', hne_g', hw2_g'⟩
        have hdel_g' := hdel_of_in g' hg' w2 hw2_g' hrv2
        by_cases hg'h1 : g' = h1
        · subst hg'h1; exact (hno_abs gy hg1 g' hh1 hlt_g1_h1 w2 hwy ⟨hmg1, hw2_g'⟩).elim
        · exact hgoal_of_3 gy h1 g' (by omega) (Ne.symm hne_g') (Ne.symm hg'h1) hdel1 hdel_h1 hdel_g'
      · by_cases hgyh1 : gy = h1
        · subst hgyh1
          -- h1 reads 2*m + g1 (.vfalse) and w2 (.vfalse) -> h1 becomes .cfalse
          rcases hshape gy hh1 with ⟨ah, bh, hoph, hinh, hah, hbh, _⟩
          have hpairh : (ah = 2 * m + g1 ∧ bh = w2) ∨ (ah = w2 ∧ bh = 2 * m + g1) := by
            rw [hinh] at hmg1 hwy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmg1 hwy
            rcases hmg1 with h1 | h1 <;> rcases hwy with h2 | h2
            · omega
            · exact Or.inl ⟨h1.symm, h2.symm⟩
            · exact Or.inr ⟨h2.symm, h1.symm⟩
            · omega
          have hrv_h1 : resolveWire (2 * m) Z (simpRes (2 * m) Z C).1 (2 * m + gy) = .vfalse := by
            apply simpRes_cfalse_of_both_vfalse (2 * m) Z C gy hh1 ah bh hoph hinh hah hbh
            · rcases hpairh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv_g1; exact hrv2
            · rcases hpairh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrv2; exact hrv_g1
          have hh1_ne_out : 2 * m + gy ≠ C.output := by
            intro hout
            rcases hoph with handh | horh
            · set r' := if r = 0 then 1 else 0
              have hr'_lt : r' < m := by simp only [r']; split <;> omega
              have hr'_ne : r' ≠ r := by simp only [r']; split <;> omega
              have hx := innerInput_length m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩
              have hw2_f : (C.wires (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩)).getD w2 false = false := by
                rw [wires_getD_input C _ w2 (by rw [hx]; omega)]
                rcases hw12 with ⟨_, hw2r⟩ | ⟨_, hw2r⟩
                · rw [hw2r, innerInput_getD_y m _ _ r hr]; simp; omega
                · rw [hw2r, innerInput_getD_x m _ _ r hr]; simp; omega
              have hev := hC ⟨r' + 1, by omega⟩ ⟨r', by omega⟩
              unfold Circuit.eval at hev
              rw [← hout, show 2 * m + gy = (innerInput m ⟨r' + 1, by omega⟩ ⟨r', by omega⟩).length + gy by omega,
                  gate_val_and C gy hh1 ah bh handh hinh _ (by omega) (by omega)] at hev
              rcases hpairh with ⟨_, hbw⟩ | ⟨haw, _⟩
              · rw [hbw, hw2_f] at hev; simp at hev
              · rw [haw, hw2_f] at hev; simp at hev
            · rcases hw12 with ⟨_, hw2r⟩ | ⟨_, hw2r⟩
              · -- w2 = m + r -> at (0, r), w2 = true, Inner = false
                have hx := innerInput_length m ⟨0, by omega⟩ ⟨r, by omega⟩
                have hw2_t : (C.wires (innerInput m ⟨0, by omega⟩ ⟨r, by omega⟩)).getD w2 false = true := by
                  have hget := congrArg (fun k => (C.wires (innerInput m ⟨0, by omega⟩ ⟨r, by omega⟩)).getD k false) hw2r
                  rw [hget, wires_getD_input C _ (m + r) (by rw [hx]; omega), innerInput_getD_y m _ _ r hr]; simp
                have hev := hC ⟨0, by omega⟩ ⟨r, by omega⟩
                unfold Circuit.eval at hev
                rw [← hout, show 2 * m + gy = (innerInput m ⟨0, by omega⟩ ⟨r, by omega⟩).length + gy by omega,
                    gate_val_or C gy hh1 ah bh horh hinh _ (by omega) (by omega)] at hev
                rcases hpairh with ⟨_, hbw⟩ | ⟨haw, _⟩
                · rw [hbw, hw2_t] at hev; simp at hev
                · rw [haw, hw2_t] at hev; simp at hev
              · -- w2 = r -> at (r + 1, m), w2 = true, Inner = false
                have hx := innerInput_length m ⟨r + 1, by omega⟩ ⟨m, by omega⟩
                have hw2_t : (C.wires (innerInput m ⟨r + 1, by omega⟩ ⟨m, by omega⟩)).getD w2 false = true := by
                  have hget := congrArg (fun k => (C.wires (innerInput m ⟨r + 1, by omega⟩ ⟨m, by omega⟩)).getD k false) hw2r
                  rw [hget, wires_getD_input C _ r (by rw [hx]; omega), innerInput_getD_x m _ _ r hr]; simp
                have hev := hC ⟨r + 1, by omega⟩ ⟨m, by omega⟩
                unfold Circuit.eval at hev
                rw [← hout, show 2 * m + gy = (innerInput m ⟨r + 1, by omega⟩ ⟨m, by omega⟩).length + gy by omega,
                    gate_val_or C gy hh1 ah bh horh hinh _ (by omega) (by omega)] at hev
                rcases hpairh with ⟨_, hbw⟩ | ⟨haw, _⟩
                · rw [hbw, hw2_t] at hev; simp at hev; omega
                · rw [haw, hw2_t] at hev; simp at hev; omega
          rcases hgate_fan gy hh1 hh1_ne_out with ⟨h2, hh2, hlt_h1_h2, hmh1⟩
          have hdel_h2 := hdel_of_in h2 hh2 (2 * m + gy) hmh1 hrv_h1
          exact hgoal_of_3 g1 gy h2 (by omega) (by omega) (by omega) hdel1 hdel_h1 hdel_h2
        · exact hgoal_of_3 g1 h1 gy (by omega) (Ne.symm hgy1) (Ne.symm hgyh1) hdel1 hdel_h1 hdely

theorem case2_contradiction (m : ℕ) (hm : 2 ≤ m) (C : Circuit) (hM : Monotone2 C) (hC : ComputesInner m C)
    (hmin : ∀ C', Monotone2 C' → ComputesInner m C' → C.size ≤ C'.size)
    (hfan1 : ∀ w < 2 * m, ∀ (j1 : ℕ) (hj1 : j1 < C.gates.length) (j2 : ℕ) (hj2 : j2 < C.gates.length),
      w ∈ (C.gates[j1]'hj1).inputs → w ∈ (C.gates[j2]'hj2).inputs → j1 = j2)
    (hor_only : ∀ w < 2 * m, ∀ (j : ℕ) (hj : j < C.gates.length),
      w ∈ (C.gates[j]'hj).inputs → (C.gates[j]'hj).op = .or) : False := by
  have ⟨hshape, ⟨hout_ge, hout_lt, hsz_pos⟩, hin_fan, _, _⟩ := min_inner_props m (by omega) C hM hC hmin
  -- Unique parent gate index and other input for each input wire w < 2*m
  have hpar_ex : ∀ w < 2 * m, ∃ (j : ℕ), j < C.gates.length ∧
      ∃ (o : ℕ), o < 2 * m + j ∧ o ≠ w ∧
      (∀ x : List Bool, x.length = 2 * m →
        (C.wires x).getD (2 * m + j) false = ((C.wires x).getD w false || (C.wires x).getD o false)) ∧
      (∀ (j' : ℕ) (hj' : j' < C.gates.length), w ∈ (C.gates[j']'hj').inputs ↔ j' = j) := by
    intro w hw
    rcases hin_fan w hw with ⟨j, hj, hwin⟩
    rcases hshape j hj with ⟨a, b, _, hin, ha, hb, hab⟩
    have hor := hor_only w hw j hj hwin
    rw [hin] at hwin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
    rcases hwin with rfl | rfl
    · refine ⟨j, hj, b, hb, hab.symm, fun x hx => ?_, fun j' hj' => ⟨fun h => hfan1 w hw j' hj' j hj h (by simp [hin]), fun h => by subst h; simp [hin]⟩⟩
      conv_lhs => rw [show 2 * m + j = x.length + j by omega]
      exact gate_val_or C j hj w b hor hin x (by omega) (by omega)
    · refine ⟨j, hj, a, ha, hab, fun x hx => ?_, fun j' hj' => ⟨fun h => hfan1 w hw j' hj' j hj h (by simp [hin]), fun h => by subst h; simp [hin]⟩⟩
      conv_lhs => rw [show 2 * m + j = x.length + j by omega]
      rw [gate_val_or C j hj a w hor hin x (by omega) (by omega), Bool.or_comm]
  let pg : ℕ → ℕ := fun w => if hw : w < 2 * m then Classical.choose (hpar_ex w hw) else 0
  have hpg_lt : ∀ w < 2 * m, pg w < C.gates.length := fun w hw => by
    simp only [pg, hw, dite_true]; exact (Classical.choose_spec (hpar_ex w hw)).1
  have hpg_spec : ∀ w (hw : w < 2 * m), ∃ o < 2 * m + pg w, o ≠ w ∧
      (∀ x : List Bool, x.length = 2 * m →
        (C.wires x).getD (2 * m + pg w) false = ((C.wires x).getD w false || (C.wires x).getD o false)) ∧
      (∀ (j' : ℕ) (hj' : j' < C.gates.length), w ∈ (C.gates[j']'hj').inputs ↔ j' = pg w) := fun w hw => by
    simp only [pg, hw, dite_true]; exact (Classical.choose_spec (hpar_ex w hw)).2
  let oth : ℕ → ℕ := fun w => if hw : w < 2 * m then Classical.choose (hpg_spec w hw) else 0
  have hoth_lt : ∀ w < 2 * m, oth w < 2 * m + pg w := fun w hw => by
    simp only [oth, hw, dite_true]; exact (Classical.choose_spec (hpg_spec w hw)).1
  have hoth_ne : ∀ w < 2 * m, oth w ≠ w := fun w hw => by
    simp only [oth, hw, dite_true]; exact (Classical.choose_spec (hpg_spec w hw)).2.1
  have hpg_val : ∀ w < 2 * m, ∀ x : List Bool, x.length = 2 * m →
      (C.wires x).getD (2 * m + pg w) false = ((C.wires x).getD w false || (C.wires x).getD (oth w) false) := fun w hw => by
    simp only [oth, hw, dite_true]; exact (Classical.choose_spec (hpg_spec w hw)).2.2.1
  have hpg_uniq : ∀ w < 2 * m, ∀ (j' : ℕ) (hj' : j' < C.gates.length),
      w ∈ (C.gates[j']'hj').inputs ↔ j' = pg w := fun w hw =>
    (Classical.choose_spec (hpg_spec w hw)).2.2.2
  -- Monotonicity helper on innerInput
  have hmono_x : ∀ (w : ℕ) (u v : Fin (m + 1)),
      (C.wires (innerInput m ⟨0, by omega⟩ v)).getD w false = true →
      (C.wires (innerInput m u v)).getD w false = true := by
    intro w u v htr
    exact wires_mono_except C hM _ _ (by simp [innerInput_length]) (fun _ => False)
      (fun i hi _ h => by
        rw [innerInput_length] at hi
        by_cases him : i < m
        · rw [innerInput_getD_x m _ _ i him] at h; simp at h
        · have heqi : m + (i - m) = i := by omega
          have ha := innerInput_getD_y m ⟨0, by omega⟩ v (i - m) (by omega)
          have hb := innerInput_getD_y m u v (i - m) (by omega)
          rw [heqi] at ha hb; rw [ha] at h; rw [hb]; exact h)
      (fun _ _ ⟨_, _, hf⟩ => hf.elim) w (fun h => h) htr
  have hmono_y : ∀ (w : ℕ) (u v : Fin (m + 1)),
      (C.wires (innerInput m u ⟨m, by omega⟩)).getD w false = true →
      (C.wires (innerInput m u v)).getD w false = true := by
    intro w u v htr
    exact wires_mono_except C hM _ _ (by simp [innerInput_length]) (fun _ => False)
      (fun i hi _ h => by
        rw [innerInput_length] at hi
        by_cases him : i < m
        · rw [innerInput_getD_x m _ _ i him] at h ⊢; exact h
        · have heqi : m + (i - m) = i := by omega
          have ha := innerInput_getD_y m u ⟨m, by omega⟩ (i - m) (by omega)
          rw [heqi] at ha; rw [ha] at h; simp at h; omega)
      (fun _ _ ⟨_, _, hf⟩ => hf.elim) w (fun h => h) htr
  -- Claim 1: for r < m, w_r := oth r
  have hC1_y : ∀ (r : ℕ) (hr : r < m) (v : ℕ) (hv : v ≤ r),
      (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (oth r) false = false := by
    intro r hr v hv
    by_contra hne
    have htr : (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (oth r) false = true := Bool.eq_true_of_not_eq_false hne
    have hle := wires_mono_except C hM
      (innerInput m ⟨r + 1, by omega⟩ ⟨v, by omega⟩)
      (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)
      (by simp [innerInput_length]) (fun w => w = r)
      (fun i hi hner h => by
        rw [innerInput_length] at hi
        by_cases him : i < m
        · rw [innerInput_getD_x m _ _ i him] at h; simp at h; omega
        · have heqi : m + (i - m) = i := by omega
          have ha := innerInput_getD_y m ⟨r + 1, by omega⟩ ⟨v, by omega⟩ (i - m) (by omega)
          have hb := innerInput_getD_y m ⟨0, by omega⟩ ⟨v, by omega⟩ (i - m) (by omega)
          rw [heqi] at ha hb; rw [ha] at h; rw [hb]; exact h)
      (fun j hj ⟨i, hi, hexi⟩ _ => by
        rw [hexi] at hi
        have hj_eq : j = pg r := (hpg_uniq r (by omega) j hj).mp hi
        rw [hj_eq, innerInput_length, hpg_val r (by omega) _ (innerInput_length m _ _), htr]; simp)
      C.output (by omega) (by
        have h1 := hC ⟨r + 1, by omega⟩ ⟨v, by omega⟩; unfold Circuit.eval at h1; simpa [show v < r + 1 by omega] using h1)
    have h2 := hC ⟨0, by omega⟩ ⟨v, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2
  have hC1_x : ∀ (r : ℕ) (hr : r < m) (u : ℕ) (hu : u ≤ r),
      (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (oth r) false = false := by
    intro r hr u hu
    by_cases hur : u = r
    · subst hur
      -- oth r does not depend on input r (since oth r < 2*m + pg r and no gate < pg r reads r)
      have heq := wires_eq_of_unread (2 * m) C (fun i => i = u)
        (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)
        (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
        (innerInput_length m _ _) (innerInput_length m _ _)
        (fun i hi hne => by
          by_cases him : i < m
          · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]; simp only [decide_eq_decide]; omega
          · have heqi : m + (i - m) = i := by omega
            have ha := innerInput_getD_y m ⟨u + 1, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
            have hb := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
            rw [heqi] at ha hb; rw [ha, hb])
        (pg u) (Nat.le_of_lt (hpg_lt u (by omega)))
        (fun j hj i hi heqi => by
          rw [heqi] at hi
          have hj_lt : j < C.gates.length := lt_trans hj (hpg_lt u (by omega))
          have := (hpg_uniq u (by omega) j hj_lt).mp hi; omega)
        (oth u) (hoth_lt u (by omega)) (hoth_ne u (by omega))
      rw [heq]
      by_contra hne
      have htr := Bool.eq_true_of_not_eq_false hne
      have htr2 := hmono_y (oth u) ⟨0, by omega⟩ ⟨u, by omega⟩ htr
      rw [hC1_y u hr u (le_refl u)] at htr2; cases htr2
    · by_contra hne
      have htr := Bool.eq_true_of_not_eq_false hne
      have htr_r := hmono_y (oth r) ⟨u + 1, by omega⟩ ⟨r, by omega⟩ htr
      have hle := wires_mono_except C hM
        (innerInput m ⟨r + 1, by omega⟩ ⟨r, by omega⟩)
        (innerInput m ⟨u + 1, by omega⟩ ⟨r, by omega⟩)
        (by simp [innerInput_length]) (fun w => w = r)
        (fun i hi hner h => by
          rw [innerInput_length] at hi
          by_cases him : i < m
          · rw [innerInput_getD_x m _ _ i him] at h; simp at h; omega
          · have heqi : m + (i - m) = i := by omega
            have ha := innerInput_getD_y m ⟨r + 1, by omega⟩ ⟨r, by omega⟩ (i - m) (by omega)
            have hb := innerInput_getD_y m ⟨u + 1, by omega⟩ ⟨r, by omega⟩ (i - m) (by omega)
            rw [heqi] at ha hb; rw [ha] at h; rw [hb]; exact h)
        (fun j hj ⟨i, hi, hexi⟩ _ => by
          rw [hexi] at hi
          have hj_eq : j = pg r := (hpg_uniq r (by omega) j hj).mp hi
          rw [hj_eq, innerInput_length, hpg_val r (by omega) _ (innerInput_length m _ _), htr_r]; simp)
        C.output (by omega) (by
          have h1 := hC ⟨r + 1, by omega⟩ ⟨r, by omega⟩; unfold Circuit.eval at h1; simpa using h1)
      have h2 := hC ⟨u + 1, by omega⟩ ⟨r, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2; omega
  -- Claim 2: for c < m, w'_c := oth (m + c)
  have hC2_x : ∀ (c : ℕ) (hc : c < m) (u : ℕ) (hu : u < m) (hcu : c ≤ u),
      (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (oth (m + c)) false = false := by
    intro c hc u hu hcu
    by_contra hne
    have htr := Bool.eq_true_of_not_eq_false hne
    have hle := wires_mono_except C hM
      (innerInput m ⟨u + 1, by omega⟩ ⟨c, by omega⟩)
      (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)
      (by simp [innerInput_length]) (fun w => w = m + c)
      (fun i hi hnec h => by
        rw [innerInput_length] at hi
        by_cases him : i < m
        · rw [innerInput_getD_x m _ _ i him] at h ⊢; exact h
        · have heqi : m + (i - m) = i := by omega
          have ha := innerInput_getD_y m ⟨u + 1, by omega⟩ ⟨c, by omega⟩ (i - m) (by omega)
          rw [heqi] at ha; rw [ha] at h; simp at h; omega)
      (fun j hj ⟨i, hi, hexi⟩ _ => by
        rw [hexi] at hi
        have hj_eq : j = pg (m + c) := (hpg_uniq (m + c) (by omega) j hj).mp hi
        rw [hj_eq, innerInput_length, hpg_val (m + c) (by omega) _ (innerInput_length m _ _), htr]; simp)
      C.output (by omega) (by
        have h1 := hC ⟨u + 1, by omega⟩ ⟨c, by omega⟩; unfold Circuit.eval at h1; simpa [show c < u + 1 by omega] using h1)
    have h2 := hC ⟨u + 1, by omega⟩ ⟨m, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2; omega
  have hC2_y : ∀ (c : ℕ) (hc : c < m) (v : ℕ) (hv : v < m) (hcv : c ≤ v),
      (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (oth (m + c)) false = false := by
    intro c hc v hv hcv
    by_cases hvc : v = c
    · subst hvc
      have heq := wires_eq_of_unread (2 * m) C (fun i => i = m + v)
        (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)
        (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
        (innerInput_length m _ _) (innerInput_length m _ _)
        (fun i hi hne => by
          by_cases him : i < m
          · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
          · have heqi : m + (i - m) = i := by omega
            have ha := innerInput_getD_y m ⟨0, by omega⟩ ⟨v, by omega⟩ (i - m) (by omega)
            have hb := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
            rw [heqi] at ha hb; rw [ha, hb]; simp only [decide_eq_decide]; omega)
        (pg (m + v)) (Nat.le_of_lt (hpg_lt (m + v) (by omega)))
        (fun j hj i hi heqi => by
          rw [heqi] at hi
          have hj_lt : j < C.gates.length := lt_trans hj (hpg_lt (m + v) (by omega))
          have := (hpg_uniq (m + v) (by omega) j hj_lt).mp hi; omega)
        (oth (m + v)) (hoth_lt (m + v) (by omega)) (hoth_ne (m + v) (by omega))
      rw [heq]
      by_contra hne
      have htr := Bool.eq_true_of_not_eq_false hne
      have htr2 := hmono_x (oth (m + v)) ⟨v + 1, by omega⟩ ⟨m, by omega⟩ htr
      rw [hC2_x v hv v hv (le_refl v)] at htr2; cases htr2
    · by_contra hne
      have htr := Bool.eq_true_of_not_eq_false hne
      have htr_c := hmono_x (oth (m + c)) ⟨c + 1, by omega⟩ ⟨v, by omega⟩ htr
      have hle := wires_mono_except C hM
        (innerInput m ⟨c + 1, by omega⟩ ⟨c, by omega⟩)
        (innerInput m ⟨c + 1, by omega⟩ ⟨v, by omega⟩)
        (by simp [innerInput_length]) (fun w => w = m + c)
        (fun i hi hnec h => by
          rw [innerInput_length] at hi
          by_cases him : i < m
          · rw [innerInput_getD_x m _ _ i him] at h ⊢; exact h
          · have heqi : m + (i - m) = i := by omega
            have ha := innerInput_getD_y m ⟨c + 1, by omega⟩ ⟨c, by omega⟩ (i - m) (by omega)
            rw [heqi] at ha; rw [ha] at h; simp at h; omega)
        (fun j hj ⟨i, hi, hexi⟩ _ => by
          rw [hexi] at hi
          have hj_eq : j = pg (m + c) := (hpg_uniq (m + c) (by omega) j hj).mp hi
          rw [hj_eq, innerInput_length, hpg_val (m + c) (by omega) _ (innerInput_length m _ _), htr_c]; simp)
        C.output (by omega) (by
          have h1 := hC ⟨c + 1, by omega⟩ ⟨c, by omega⟩; unfold Circuit.eval at h1; simpa using h1)
      have h2 := hC ⟨c + 1, by omega⟩ ⟨v, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2; omega
  -- Claim 3: Separation
  have hC3 : ∀ (a : ℕ) (ha : a < m) (b : ℕ) (hb : b < m), b ≤ a →
      ¬ ((∃ (v : ℕ) (hv : v < m), (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (2 * m + pg a) false = true) ∧
         (∃ (u : ℕ) (hu : u < m), (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (2 * m + pg (m + b)) false = true)) := by
    intro a ha b hb hba ⟨⟨v, hv, hpa⟩, ⟨u, hu, hqb⟩⟩
    have hva : a < v := by
      by_contra hle; push Not at hle
      rw [hpg_val a (by omega) _ (innerInput_length m _ _),
          wires_getD_input C _ a (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ a ha,
          hC1_y a ha v hle] at hpa
      simp at hpa
    have hub : u < b := by
      by_contra hle; push Not at hle
      rw [hpg_val (m + b) (by omega) _ (innerInput_length m _ _),
          wires_getD_input C _ (m + b) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ b hb,
          hC2_x b hb u hu hle] at hqb
      simp at hqb; omega
    have hpa' := hmono_x (2 * m + pg a) ⟨u + 1, by omega⟩ ⟨v, by omega⟩ hpa
    have hqb' := hmono_y (2 * m + pg (m + b)) ⟨u + 1, by omega⟩ ⟨v, by omega⟩ hqb
    have hle := wires_mono_except C hM
      (innerInput m ⟨a + 1, by omega⟩ ⟨b, by omega⟩)
      (innerInput m ⟨u + 1, by omega⟩ ⟨v, by omega⟩)
      (by simp [innerInput_length]) (fun w => w = a ∨ w = m + b)
      (fun i hi hne h => by
        rw [innerInput_length] at hi
        by_cases him : i < m
        · rw [innerInput_getD_x m _ _ i him] at h; simp at h; omega
        · have heqi : m + (i - m) = i := by omega
          have h1 := innerInput_getD_y m ⟨a + 1, by omega⟩ ⟨b, by omega⟩ (i - m) (by omega)
          rw [heqi] at h1; rw [h1] at h; simp at h; omega)
      (fun j hj ⟨i, hi, hexi⟩ _ => by
        rcases hexi with hia | hib
        · rw [hia] at hi
          have hj_eq : j = pg a := (hpg_uniq a (by omega) j hj).mp hi
          rw [hj_eq, innerInput_length]; exact hpa'
        · rw [hib] at hi
          have hj_eq : j = pg (m + b) := (hpg_uniq (m + b) (by omega) j hj).mp hi
          rw [hj_eq, innerInput_length]; exact hqb')
      C.output (by omega) (by
        have h1 := hC ⟨a + 1, by omega⟩ ⟨b, by omega⟩; unfold Circuit.eval at h1; simpa [show b < a + 1 by omega] using h1)
    have h2 := hC ⟨u + 1, by omega⟩ ⟨v, by omega⟩; unfold Circuit.eval at h2; rw [hle] at h2; simp at h2; omega
  -- Claim 4: Gate 0 gives non-empty A and B
  have h0_lt : 0 < C.gates.length := by simp [Circuit.size] at hsz_pos; omega
  rcases hshape 0 h0_lt with ⟨a0, b0, _, hin0, ha0, hb0, hab0⟩
  have hpg_a0 : pg a0 = 0 := ((hpg_uniq a0 (by omega) 0 h0_lt).mp (by simp [hin0])).symm
  have hpg_b0 : pg b0 = 0 := ((hpg_uniq b0 (by omega) 0 h0_lt).mp (by simp [hin0])).symm
  have h0_or : (C.gates[0]'h0_lt).op = .or := hor_only a0 (by omega) 0 h0_lt (by simp [hin0])
  have h0_eval : ∀ x : List Bool, x.length = 2 * m →
      (C.wires x).getD (2 * m + 0) false = ((C.wires x).getD a0 false || (C.wires x).getD b0 false) := fun x hx => by
    conv_lhs => rw [show 2 * m + 0 = x.length + 0 by omega]
    exact gate_val_or C 0 h0_lt a0 b0 h0_or hin0 x (by omega) (by omega)
  have hoth_a0 : ∀ x : List Bool, x.length = 2 * m → (C.wires x).getD a0 false = false →
      (C.wires x).getD (oth a0) false = (C.wires x).getD b0 false := fun x hx hfa => by
    have h1 := hpg_val a0 (by omega) x hx
    rw [hpg_a0, h0_eval x hx, hfa, Bool.false_or, Bool.false_or] at h1
    exact h1.symm
  have hoth_b0 : ∀ x : List Bool, x.length = 2 * m → (C.wires x).getD b0 false = false →
      (C.wires x).getD (oth b0) false = (C.wires x).getD a0 false := fun x hx hfb => by
    have h1 := hpg_val b0 (by omega) x hx
    rw [hpg_b0, h0_eval x hx, hfb, Bool.or_false, Bool.false_or] at h1
    exact h1.symm
  have hAB_ex : ∃ (r0 : ℕ) (hr0 : r0 < m) (c0 : ℕ) (hc0 : c0 < m), r0 < c0 ∧
      (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD (2 * m + pg r0) false = true ∧
      (C.wires (innerInput m ⟨r0 + 1, by omega⟩ ⟨m, by omega⟩)).getD (2 * m + pg (m + c0)) false = true := by
    by_cases ha0m : a0 < m
    · by_cases hb0m : b0 < m
      · exfalso -- both x_a0, x_b0: pick larger index
        by_cases hlt : a0 < b0
        · have h1 := hC1_x b0 hb0m a0 (Nat.le_of_lt hlt)
          have hfb : (C.wires (innerInput m ⟨a0 + 1, by omega⟩ ⟨m, by omega⟩)).getD b0 false = false := by
            rw [wires_getD_input C _ b0 (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ b0 hb0m]; simp; omega
          rw [hoth_b0 _ (innerInput_length m _ _) hfb, wires_getD_input C _ a0 (by rw [innerInput_length]; omega),
              innerInput_getD_x m _ _ a0 ha0m] at h1; simp at h1
        · have h1 := hC1_x a0 ha0m b0 (by omega)
          have hfa : (C.wires (innerInput m ⟨b0 + 1, by omega⟩ ⟨m, by omega⟩)).getD a0 false = false := by
            rw [wires_getD_input C _ a0 (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ a0 ha0m]; simp; omega
          rw [hoth_a0 _ (innerInput_length m _ _) hfa, wires_getD_input C _ b0 (by rw [innerInput_length]; omega),
              innerInput_getD_x m _ _ b0 hb0m] at h1; simp at h1
      · set c0 := b0 - m
        have hc0 : c0 < m := by omega
        have hb0_eq : b0 = m + c0 := by omega
        have hrc : a0 < c0 := by
          by_contra hle; push Not at hle
          have h1 := hC1_y a0 ha0m c0 hle
          have hfa : (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD a0 false = false := by
            rw [wires_getD_input C _ a0 (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ a0 ha0m]; simp
          have hget : (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD b0 false =
              (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD (m + c0) false :=
            congrArg (fun k => (C.wires _).getD k false) hb0_eq
          rw [hoth_a0 _ (innerInput_length m _ _) hfa, hget, wires_getD_input C _ (m + c0) (by rw [innerInput_length]; omega),
              innerInput_getD_y m _ _ c0 hc0] at h1; simp at h1
        refine ⟨a0, ha0m, c0, hc0, hrc, ?_, ?_⟩
        · have hget : (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD b0 false =
              (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD (m + c0) false :=
            congrArg (fun k => (C.wires _).getD k false) hb0_eq
          rw [hpg_a0, h0_eval _ (innerInput_length m _ _), hget,
              wires_getD_input C _ (m + c0) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ c0 hc0]; simp
        · have hpg_mc : pg (m + c0) = 0 := hb0_eq ▸ hpg_b0
          rw [hpg_mc, h0_eval _ (innerInput_length m _ _),
              wires_getD_input C _ a0 (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ a0 ha0m]; simp
    · by_cases hb0m : b0 < m
      · set c0 := a0 - m
        have hc0 : c0 < m := by omega
        have ha0_eq : a0 = m + c0 := by omega
        have hrc : b0 < c0 := by
          by_contra hle; push Not at hle
          have h1 := hC1_y b0 hb0m c0 hle
          have hfb : (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD b0 false = false := by
            rw [wires_getD_input C _ b0 (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ b0 hb0m]; simp
          have hget : (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD a0 false =
              (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD (m + c0) false :=
            congrArg (fun k => (C.wires _).getD k false) ha0_eq
          rw [hoth_b0 _ (innerInput_length m _ _) hfb, hget, wires_getD_input C _ (m + c0) (by rw [innerInput_length]; omega),
              innerInput_getD_y m _ _ c0 hc0] at h1; simp at h1
        refine ⟨b0, hb0m, c0, hc0, hrc, ?_, ?_⟩
        · have hget : (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD a0 false =
              (C.wires (innerInput m ⟨0, by omega⟩ ⟨c0, by omega⟩)).getD (m + c0) false :=
            congrArg (fun k => (C.wires _).getD k false) ha0_eq
          rw [hpg_b0, h0_eval _ (innerInput_length m _ _), hget,
              wires_getD_input C _ (m + c0) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ c0 hc0]; simp
        · have hpg_mc : pg (m + c0) = 0 := ha0_eq ▸ hpg_a0
          rw [hpg_mc, h0_eval _ (innerInput_length m _ _),
              wires_getD_input C _ b0 (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ b0 hb0m]; simp
      · exfalso -- both y_ca, y_cb: pick smaller index
        set ca := a0 - m
        set cb := b0 - m
        have hca : ca < m := by omega
        have hcb : cb < m := by omega
        have ha0_eq : a0 = m + ca := by omega
        have hb0_eq : b0 = m + cb := by omega
        by_cases hlt : ca < cb
        · have h1 := hC2_y ca hca cb hcb (Nat.le_of_lt hlt)
          have hfa : (C.wires (innerInput m ⟨0, by omega⟩ ⟨cb, by omega⟩)).getD a0 false = false := by
            have hget : (C.wires (innerInput m ⟨0, by omega⟩ ⟨cb, by omega⟩)).getD a0 false =
                (C.wires (innerInput m ⟨0, by omega⟩ ⟨cb, by omega⟩)).getD (m + ca) false :=
              congrArg (fun k => (C.wires _).getD k false) ha0_eq
            rw [hget, wires_getD_input C _ (m + ca) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ ca hca]; simp; omega
          have hoth_eq : oth (m + ca) = oth a0 := congrArg oth ha0_eq.symm
          have hgetb : (C.wires (innerInput m ⟨0, by omega⟩ ⟨cb, by omega⟩)).getD b0 false =
              (C.wires (innerInput m ⟨0, by omega⟩ ⟨cb, by omega⟩)).getD (m + cb) false :=
            congrArg (fun k => (C.wires _).getD k false) hb0_eq
          rw [hoth_eq, hoth_a0 _ (innerInput_length m _ _) hfa, hgetb,
              wires_getD_input C _ (m + cb) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ cb hcb] at h1; simp at h1
        · have h1 := hC2_y cb hcb ca hca (by omega)
          have hfb : (C.wires (innerInput m ⟨0, by omega⟩ ⟨ca, by omega⟩)).getD b0 false = false := by
            have hget : (C.wires (innerInput m ⟨0, by omega⟩ ⟨ca, by omega⟩)).getD b0 false =
                (C.wires (innerInput m ⟨0, by omega⟩ ⟨ca, by omega⟩)).getD (m + cb) false :=
              congrArg (fun k => (C.wires _).getD k false) hb0_eq
            rw [hget, wires_getD_input C _ (m + cb) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ cb hcb]; simp; omega
          have hoth_eq : oth (m + cb) = oth b0 := congrArg oth hb0_eq.symm
          have hgeta : (C.wires (innerInput m ⟨0, by omega⟩ ⟨ca, by omega⟩)).getD a0 false =
              (C.wires (innerInput m ⟨0, by omega⟩ ⟨ca, by omega⟩)).getD (m + ca) false :=
            congrArg (fun k => (C.wires _).getD k false) ha0_eq
          rw [hoth_eq, hoth_b0 _ (innerInput_length m _ _) hfb, hgeta,
              wires_getD_input C _ (m + ca) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ ca hca] at h1; simp at h1
  -- Claim 5: Cut s = max A and minimum gate in G
  rcases hAB_ex with ⟨r0, hr0, c0, hc0, hr0c0, hpr0, hqc0⟩
  let Aset : Finset ℕ := (Finset.range m).filter fun a =>
    ∃ (v : ℕ) (hv : v < m), (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (2 * m + pg a) false = true
  have hr0A : r0 ∈ Aset := by
    simp only [Aset, Finset.mem_filter, Finset.mem_range]; exact ⟨hr0, c0, hc0, hpr0⟩
  have hAne : Aset.Nonempty := ⟨r0, hr0A⟩
  set s := Aset.max' hAne
  have hsA : s ∈ Aset := Finset.max'_mem Aset hAne
  have hs_lt_m : s < m := Finset.mem_range.mp (Finset.mem_filter.mp hsA).1
  have hs_ex : ∃ (v : ℕ) (hv : v < m), (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (2 * m + pg s) false = true :=
    (Finset.mem_filter.mp hsA).2
  have hs_lt_c0 : s < c0 := by
    by_contra hle; push Not at hle
    exact hC3 s hs_lt_m c0 hc0 hle ⟨hs_ex, r0, hr0, hqc0⟩
  have hgt_s_SY : ∀ (a : ℕ) (ha : a < m), s < a → ∀ (v : ℕ) (hv : v < m),
      (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (2 * m + pg a) false = false := by
    intro a ha hsa v hv
    by_contra hne
    have htr := Bool.eq_true_of_not_eq_false hne
    have haA : a ∈ Aset := by simp only [Aset, Finset.mem_filter, Finset.mem_range]; exact ⟨ha, v, hv, htr⟩
    have : a ≤ s := Finset.le_max' Aset a haA
    omega
  have hle_s_SX : ∀ (b : ℕ) (hb : b < m), b ≤ s → ∀ (u : ℕ) (hu : u < m),
      (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (2 * m + pg (m + b)) false = false := by
    intro b hb hbs u hu
    by_contra hne
    have htr := Bool.eq_true_of_not_eq_false hne
    exact hC3 s hs_lt_m b hb hbs ⟨hs_ex, u, hu, htr⟩
  let Gset : Finset ℕ :=
    ((Finset.range m).filter (fun a => s < a)).image (fun a => pg a) ∪
    ((Finset.range m).filter (fun b => b ≤ s)).image (fun b => pg (m + b))
  have hGne : Gset.Nonempty := ⟨pg (m + 0), Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0, by simp; omega, rfl⟩)⟩
  set gmin := Gset.min' hGne
  have hgmin_mem : gmin ∈ Gset := Finset.min'_mem Gset hGne
  let U : ℕ → Prop := fun w => (s < w ∧ w < m) ∨ (m ≤ w ∧ w - m ≤ s)
  have hgmin_lt : gmin < C.gates.length := by
    rcases Finset.mem_union.mp hgmin_mem with hL | hR
    · rcases Finset.mem_image.mp hL with ⟨a, ha, hga⟩
      rw [← hga]; exact hpg_lt a (by simp at ha; omega)
    · rcases Finset.mem_image.mp hR with ⟨b, hb, hgb⟩
      rw [← hgb]; exact hpg_lt (m + b) (by simp at hb; omega)
  have hno_U_lt : ∀ (j : ℕ) (hj : j < gmin), ∀ w ∈ (C.gates[j]'(lt_trans hj hgmin_lt)).inputs, ¬ U w := by
    intro j hj w hw hUw
    have hj_lt : j < C.gates.length := lt_trans hj hgmin_lt
    rcases hUw with ⟨hsw, hwm⟩ | ⟨hmw, hws⟩
    · have hj_eq : j = pg w := (hpg_uniq w (by omega) j hj_lt).mp hw
      have hmem : pg w ∈ Gset := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, by simp; omega, rfl⟩)
      have := Finset.min'_le Gset (pg w) hmem; omega
    · set b := w - m
      have hb : b < m := by omega
      have hw_eq : w = m + b := by omega
      have hj_eq : j = pg (m + b) := (hpg_uniq (m + b) (by omega) j hj_lt).mp (hw_eq ▸ hw)
      have hmem : pg (m + b) ∈ Gset := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, by simp; omega, rfl⟩)
      have := Finset.min'_le Gset (pg (m + b)) hmem; omega
  rcases Finset.mem_union.mp hgmin_mem with hL | hR
  · -- Subcase A: gmin = pg a with s < a < m
    rcases Finset.mem_image.mp hL with ⟨a, ha_mem, hga⟩
    simp only [Finset.mem_filter, Finset.mem_range] at ha_mem
    rcases ha_mem with ⟨ha_lt, hsa⟩
    have hnotU : ¬ U (oth a) := by
      rintro (⟨hsw, hwm⟩ | ⟨hmw, hws⟩)
      · have hne : oth a ≠ a := hoth_ne a (by omega)
        by_cases hlt : oth a < a
        · have h1 := hC1_x a ha_lt (oth a) (Nat.le_of_lt hlt)
          rw [wires_getD_input C _ (oth a) (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ (oth a) hwm] at h1
          simp at h1
        · -- a < oth a < m, and oth a is input to pg a, so pg (oth a) = pg a
          have hpg_eq : pg (oth a) = pg a := by
            have hin_mem : oth a ∈ (C.gates[pg a]'(hpg_lt a (by omega))).inputs := by
              by_contra hnot
              have this_val := hpg_val a (by omega) (innerInput m ⟨oth a + 1, by omega⟩ ⟨m, by omega⟩) (innerInput_length m _ _)
              rw [wires_getD_input C _ (oth a) (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ (oth a) hwm] at this_val
              simp only [decide_true, Bool.or_true] at this_val
              have heq_p := wires_eq_of_unread (2 * m) C (fun i => i = oth a)
                (innerInput m ⟨oth a + 1, by omega⟩ ⟨m, by omega⟩)
                (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
                (innerInput_length m _ _) (innerInput_length m _ _)
                (fun i hi hnei => by
                  by_cases him : i < m
                  · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]; simp only [decide_eq_decide]; omega
                  · have heqi : m + (i - m) = i := by omega
                    have ha1 := innerInput_getD_y m ⟨oth a + 1, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
                    have hb1 := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
                    rw [heqi] at ha1 hb1; rw [ha1, hb1])
                (pg a + 1) (by have := hpg_lt a (by omega); omega)
                (fun j hj u hu hequ => by
                  subst hequ
                  by_cases hjlt : j < pg a
                  · exact hno_U_lt j (by omega) (oth a) hu (Or.inl ⟨hsw, hwm⟩)
                  · have : j = pg a := by omega
                    subst this; exact hnot hu)
                (2 * m + pg a) (by omega) (by omega)
              rw [this_val] at heq_p
              have h0 := hpg_val a (by omega) (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩) (innerInput_length m _ _)
              rw [← heq_p] at h0
              have ha0f : (C.wires (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)).getD a false = false := by
                rw [wires_getD_input C _ a (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ a ha_lt]; simp
              have hoth0f : (C.wires (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)).getD (oth a) false = false := by
                rw [wires_getD_input C _ (oth a) (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ (oth a) hwm]; simp
              rw [ha0f, hoth0f] at h0; simp at h0
            exact ((hpg_uniq (oth a) (by omega) (pg a) (hpg_lt a (by omega))).mp hin_mem).symm
          have h1 := hpg_val (oth a) (by omega) (innerInput m ⟨a + 1, by omega⟩ ⟨m, by omega⟩) (innerInput_length m _ _)
          have h2 := hpg_val a (by omega) (innerInput m ⟨a + 1, by omega⟩ ⟨m, by omega⟩) (innerInput_length m _ _)
          rw [hpg_eq, h2, wires_getD_input C _ a (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ a ha_lt,
              wires_getD_input C _ (oth a) (by rw [innerInput_length]; omega), innerInput_getD_x m _ _ (oth a) hwm,
              hC1_x (oth a) hwm a (by omega)] at h1
          simp at h1; omega
      · set b := oth a - m
        have hb : b ≤ s := hws
        have h1 := hC1_y a ha_lt b (by omega)
        have heq : m + b = oth a := by omega
        rw [← heq, wires_getD_input C _ (m + b) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ b (by omega)] at h1
        simp at h1
    have hwa_x : ∀ (u : ℕ) (hu : u < m), (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (oth a) false = false := by
      intro u hu
      by_cases hua : u ≤ a
      · exact hC1_x a ha_lt u hua
      · have heq := wires_eq_of_unread (2 * m) C U
          (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)
          (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
          (innerInput_length m _ _) (innerInput_length m _ _)
          (fun i hi hnU => by
            by_cases him : i < m
            · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
              have : i ≠ u := fun h => hnU (Or.inl ⟨by omega, by omega⟩)
              simp only [decide_eq_decide]; omega
            · have heqi : m + (i - m) = i := by omega
              have ha1 := innerInput_getD_y m ⟨u + 1, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
              have hb1 := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
              rw [heqi] at ha1 hb1; rw [ha1, hb1])
          (pg a) (Nat.le_of_lt (hpg_lt a (by omega)))
          (fun j hj w hw => hno_U_lt j (by omega) w hw)
          (oth a) (hoth_lt a (by omega)) hnotU
        rw [heq]
        by_contra hne
        have htr := hmono_y (oth a) ⟨0, by omega⟩ ⟨a, by omega⟩ (Bool.eq_true_of_not_eq_false hne)
        rw [hC1_y a ha_lt a (le_refl a)] at htr; cases htr
    have hwa_y : ∀ (v : ℕ) (hv : v < m), (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (oth a) false = false := by
      intro v hv
      have h1 := hgt_s_SY a ha_lt hsa v hv
      rw [hpg_val a (by omega) _ (innerInput_length m _ _)] at h1
      cases h : (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (oth a) false
      · rfl
      · rw [h] at h1; simp at h1
    have hwa_true : ∀ u v : Fin (m + 1), v.val < u.val →
        (C.wires (innerInput m u v)).getD (oth a) false = false := by
      intro u v hvu
      by_cases hus : u.val ≤ s + 1
      · have heq := wires_eq_of_unread (2 * m) C U
          (innerInput m u v) (innerInput m u ⟨m, by omega⟩)
          (innerInput_length m _ _) (innerInput_length m _ _)
          (fun i hi hnU => by
            by_cases him : i < m
            · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
            · have heqi : m + (i - m) = i := by omega
              have ha1 := innerInput_getD_y m u v (i - m) (by omega)
              have hb1 := innerInput_getD_y m u ⟨m, by omega⟩ (i - m) (by omega)
              rw [heqi] at ha1 hb1; rw [ha1, hb1]
              have : i - m ≠ v.val := fun h => hnU (Or.inr ⟨by omega, by omega⟩)
              simp only [decide_eq_decide]; omega)
          (pg a) (Nat.le_of_lt (hpg_lt a (by omega)))
          (fun j hj w hw => hno_U_lt j (by omega) w hw)
          (oth a) (hoth_lt a (by omega)) hnotU
        rw [heq]
        have hu1 : u.val - 1 < m := by omega
        have hueq : (⟨(u.val - 1) + 1, by omega⟩ : Fin (m + 1)) = u := Fin.ext (by dsimp; omega)
        simpa [hueq] using hwa_x (u.val - 1) hu1
      · have heq := wires_eq_of_unread (2 * m) C U
          (innerInput m u v) (innerInput m ⟨0, by omega⟩ v)
          (innerInput_length m _ _) (innerInput_length m _ _)
          (fun i hi hnU => by
            by_cases him : i < m
            · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
              have : i ≠ u.val - 1 := fun h => hnU (Or.inl ⟨by omega, by omega⟩)
              simp only [decide_eq_decide]; omega
            · have heqi : m + (i - m) = i := by omega
              have ha1 := innerInput_getD_y m u v (i - m) (by omega)
              have hb1 := innerInput_getD_y m ⟨0, by omega⟩ v (i - m) (by omega)
              rw [heqi] at ha1 hb1; rw [ha1, hb1])
          (pg a) (Nat.le_of_lt (hpg_lt a (by omega)))
          (fun j hj w hw => hno_U_lt j (by omega) w hw)
          (oth a) (hoth_lt a (by omega)) hnotU
        rw [heq]
        have hv1 : v.val < m := by omega
        have hveq : (⟨v.val, by omega⟩ : Fin (m + 1)) = v := Fin.ext rfl
        simpa [hveq] using hwa_y v.val hv1
    have hC'_comp : ComputesInner m (elimGate (2 * m) C (pg a) (some a)) := by
      intro u v
      by_cases hvu : v.val < u.val
      · rw [elimGate_eval (2 * m) C (pg a) (hpg_lt a (by omega)) (some a) (fun _ h => by cases h; omega)
            (innerInput m u v) (innerInput_length m u v) (by
              rw [hpg_val a (by omega) _ (innerInput_length m u v), hwa_true u v hvu, Bool.or_false])]
        exact hC u v
      · have hle := elimGate_mono_le_eval (2 * m) C hM (pg a) (hpg_lt a (by omega)) a (by omega)
          (innerInput m u v) (innerInput_length m u v) (by
            rw [hpg_val a (by omega) _ (innerInput_length m u v)]
            cases (C.wires (innerInput m u v)).getD a false <;> simp)
        rw [hC u v] at hle
        simp only [decide_eq_false hvu] at hle ⊢
        cases h : (elimGate (2 * m) C (pg a) (some a)).eval (innerInput m u v) with
        | false => rfl
        | true => rw [h] at hle; exact (Bool.le_iff_imp.mp hle rfl).symm
    have hle := hmin _ (elimGate_mono (2 * m) C hM (pg a) (some a)) hC'_comp
    have hsz := elimGate_size (2 * m) C (pg a) (hpg_lt a (by omega)) (some a)
    simp [Circuit.size] at hle hsz; omega
  · -- Subcase B: gmin = pg (m + b) with b <= s
    rcases Finset.mem_image.mp hR with ⟨b, hb_mem, hgb⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hb_mem
    rcases hb_mem with ⟨hb_lt, hbs⟩
    have hnotU : ¬ U (oth (m + b)) := by
      rintro (⟨hsw, hwm⟩ | ⟨hmw, hws⟩)
      · have h1 := hC2_x b hb_lt (oth (m + b)) hwm (by omega)
        rw [wires_getD_input C _ (oth (m + b)) (by rw [innerInput_length]; omega),
            innerInput_getD_x m _ _ (oth (m + b)) hwm] at h1
        simp at h1
      · set b' := oth (m + b) - m
        have hb'_lt : b' < m := by omega
        have heq_b' : m + b' = oth (m + b) := by omega
        have hne : b' ≠ b := fun h => hoth_ne (m + b) (by omega) (by omega)
        by_cases hlt : b < b'
        · have h1 := hC2_y b hb_lt b' hb'_lt (Nat.le_of_lt hlt)
          rw [← heq_b', wires_getD_input C _ (m + b') (by rw [innerInput_length]; omega),
              innerInput_getD_y m _ _ b' hb'_lt] at h1
          simp at h1
        · have hpg_eq : pg (m + b') = pg (m + b) := by
            have hin_mem : m + b' ∈ (C.gates[pg (m + b)]'(hpg_lt (m + b) (by omega))).inputs := by
              by_contra hnot
              have this_val := hpg_val (m + b) (by omega) (innerInput m ⟨0, by omega⟩ ⟨b', by omega⟩) (innerInput_length m _ _)
              rw [← heq_b', wires_getD_input C _ (m + b') (by rw [innerInput_length]; omega),
                  innerInput_getD_y m _ _ b' hb'_lt] at this_val
              simp only [decide_true, Bool.or_true] at this_val
              have heq_p := wires_eq_of_unread (2 * m) C (fun i => i = m + b')
                (innerInput m ⟨0, by omega⟩ ⟨b', by omega⟩)
                (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
                (innerInput_length m _ _) (innerInput_length m _ _)
                (fun i hi hnei => by
                  by_cases him : i < m
                  · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
                  · have heqi : m + (i - m) = i := by omega
                    have ha1 := innerInput_getD_y m ⟨0, by omega⟩ ⟨b', by omega⟩ (i - m) (by omega)
                    have hb1 := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
                    rw [heqi] at ha1 hb1; rw [ha1, hb1]; simp only [decide_eq_decide]; omega)
                (pg (m + b) + 1) (by have := hpg_lt (m + b) (by omega); omega)
                (fun j hj u hu hequ => by
                  subst hequ
                  by_cases hjlt : j < pg (m + b)
                  · exact hno_U_lt j (by omega) (m + b') hu (Or.inr ⟨by omega, by omega⟩)
                  · have : j = pg (m + b) := by omega
                    subst this; exact hnot hu)
                (2 * m + pg (m + b)) (by omega) (by omega)
              rw [this_val] at heq_p
              have h0 := hpg_val (m + b) (by omega) (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩) (innerInput_length m _ _)
              rw [← heq_p] at h0
              have hb0f : (C.wires (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)).getD (m + b) false = false := by
                rw [wires_getD_input C _ (m + b) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ b hb_lt]; simp; omega
              have hoth0f : (C.wires (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)).getD (oth (m + b)) false = false := by
                rw [← heq_b', wires_getD_input C _ (m + b') (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ b' hb'_lt]; simp; omega
              rw [hb0f, hoth0f] at h0; simp at h0
            exact ((hpg_uniq (m + b') (by omega) (pg (m + b)) (hpg_lt (m + b) (by omega))).mp hin_mem).symm
          have h1 := hpg_val (m + b') (by omega) (innerInput m ⟨0, by omega⟩ ⟨b, by omega⟩) (innerInput_length m _ _)
          have h2 := hpg_val (m + b) (by omega) (innerInput m ⟨0, by omega⟩ ⟨b, by omega⟩) (innerInput_length m _ _)
          rw [hpg_eq, h2, wires_getD_input C _ (m + b) (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ b hb_lt,
              wires_getD_input C _ (m + b') (by rw [innerInput_length]; omega), innerInput_getD_y m _ _ b' hb'_lt,
              hC2_y b' hb'_lt b hb_lt (by omega)] at h1
          simp at h1; omega
    have hwb_x : ∀ (u : ℕ) (hu : u < m), (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (oth (m + b)) false = false := by
      intro u hu
      have h1 := hle_s_SX b hb_lt hbs u hu
      rw [hpg_val (m + b) (by omega) _ (innerInput_length m _ _)] at h1
      cases h : (C.wires (innerInput m ⟨u + 1, by omega⟩ ⟨m, by omega⟩)).getD (oth (m + b)) false
      · rfl
      · rw [h] at h1; simp at h1
    have hwb_y : ∀ (v : ℕ) (hv : v < m), (C.wires (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)).getD (oth (m + b)) false = false := by
      intro v hv
      by_cases hbv : b ≤ v
      · exact hC2_y b hb_lt v hv hbv
      · have heq := wires_eq_of_unread (2 * m) C U
          (innerInput m ⟨0, by omega⟩ ⟨v, by omega⟩)
          (innerInput m ⟨0, by omega⟩ ⟨m, by omega⟩)
          (innerInput_length m _ _) (innerInput_length m _ _)
          (fun i hi hnU => by
            by_cases him : i < m
            · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
            · have heqi : m + (i - m) = i := by omega
              have ha1 := innerInput_getD_y m ⟨0, by omega⟩ ⟨v, by omega⟩ (i - m) (by omega)
              have hb1 := innerInput_getD_y m ⟨0, by omega⟩ ⟨m, by omega⟩ (i - m) (by omega)
              rw [heqi] at ha1 hb1; rw [ha1, hb1]
              have : i - m ≠ v := fun h => hnU (Or.inr ⟨by omega, by omega⟩)
              simp only [decide_eq_decide]; omega)
          (pg (m + b)) (Nat.le_of_lt (hpg_lt (m + b) (by omega)))
          (fun j hj w hw => hno_U_lt j (by omega) w hw)
          (oth (m + b)) (hoth_lt (m + b) (by omega)) hnotU
        rw [heq]
        by_contra hne
        have htr := hmono_x (oth (m + b)) ⟨b + 1, by omega⟩ ⟨m, by omega⟩ (Bool.eq_true_of_not_eq_false hne)
        rw [hC2_x b hb_lt b hb_lt (le_refl b)] at htr; cases htr
    have hwb_true : ∀ u v : Fin (m + 1), v.val < u.val →
        (C.wires (innerInput m u v)).getD (oth (m + b)) false = false := by
      intro u v hvu
      by_cases hus : u.val ≤ s + 1
      · have heq := wires_eq_of_unread (2 * m) C U
          (innerInput m u v) (innerInput m u ⟨m, by omega⟩)
          (innerInput_length m _ _) (innerInput_length m _ _)
          (fun i hi hnU => by
            by_cases him : i < m
            · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
            · have heqi : m + (i - m) = i := by omega
              have ha1 := innerInput_getD_y m u v (i - m) (by omega)
              have hb1 := innerInput_getD_y m u ⟨m, by omega⟩ (i - m) (by omega)
              rw [heqi] at ha1 hb1; rw [ha1, hb1]
              have : i - m ≠ v.val := fun h => hnU (Or.inr ⟨by omega, by omega⟩)
              simp only [decide_eq_decide]; omega)
          (pg (m + b)) (Nat.le_of_lt (hpg_lt (m + b) (by omega)))
          (fun j hj w hw => hno_U_lt j (by omega) w hw)
          (oth (m + b)) (hoth_lt (m + b) (by omega)) hnotU
        rw [heq]
        have hu1 : u.val - 1 < m := by omega
        have hueq : (⟨(u.val - 1) + 1, by omega⟩ : Fin (m + 1)) = u := Fin.ext (by dsimp; omega)
        simpa [hueq] using hwb_x (u.val - 1) hu1
      · have heq := wires_eq_of_unread (2 * m) C U
          (innerInput m u v) (innerInput m ⟨0, by omega⟩ v)
          (innerInput_length m _ _) (innerInput_length m _ _)
          (fun i hi hnU => by
            by_cases him : i < m
            · rw [innerInput_getD_x m _ _ i him, innerInput_getD_x m _ _ i him]
              have : i ≠ u.val - 1 := fun h => hnU (Or.inl ⟨by omega, by omega⟩)
              simp only [decide_eq_decide]; omega
            · have heqi : m + (i - m) = i := by omega
              have ha1 := innerInput_getD_y m u v (i - m) (by omega)
              have hb1 := innerInput_getD_y m ⟨0, by omega⟩ v (i - m) (by omega)
              rw [heqi] at ha1 hb1; rw [ha1, hb1])
          (pg (m + b)) (Nat.le_of_lt (hpg_lt (m + b) (by omega)))
          (fun j hj w hw => hno_U_lt j (by omega) w hw)
          (oth (m + b)) (hoth_lt (m + b) (by omega)) hnotU
        rw [heq]
        have hv1 : v.val < m := by omega
        have hveq : (⟨v.val, by omega⟩ : Fin (m + 1)) = v := Fin.ext rfl
        simpa [hveq] using hwb_y v.val hv1
    have hC'_comp : ComputesInner m (elimGate (2 * m) C (pg (m + b)) (some (m + b))) := by
      intro u v
      by_cases hvu : v.val < u.val
      · rw [elimGate_eval (2 * m) C (pg (m + b)) (hpg_lt (m + b) (by omega)) (some (m + b)) (fun _ h => by cases h; omega)
            (innerInput m u v) (innerInput_length m u v) (by
              rw [hpg_val (m + b) (by omega) _ (innerInput_length m u v), hwb_true u v hvu, Bool.or_false])]
        exact hC u v
      · have hle := elimGate_mono_le_eval (2 * m) C hM (pg (m + b)) (hpg_lt (m + b) (by omega)) (m + b) (by omega)
          (innerInput m u v) (innerInput_length m u v) (by
            rw [hpg_val (m + b) (by omega) _ (innerInput_length m u v)]
            cases (C.wires (innerInput m u v)).getD (m + b) false <;> simp)
        rw [hC u v] at hle
        simp only [decide_eq_false hvu] at hle ⊢
        cases h : (elimGate (2 * m) C (pg (m + b)) (some (m + b))).eval (innerInput m u v) with
        | false => rfl
        | true => rw [h] at hle; exact (Bool.le_iff_imp.mp hle rfl).symm
    have hle := hmin _ (elimGate_mono (2 * m) C hM (pg (m + b)) (some (m + b))) hC'_comp
    have hsz := elimGate_size (2 * m) C (pg (m + b)) (hpg_lt (m + b) (by omega)) (some (m + b))
    simp [Circuit.size] at hle hsz; omega

theorem inner_lower_bound : ∀ m : ℕ, 1 ≤ m → ∀ C : Circuit, Monotone2 C → ComputesInner m C → 3 * m - 2 ≤ C.size := by
  classical
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m' ih =>
    intro _ C hM hC
    have hex : ∃ s, ∃ C0, Monotone2 C0 ∧ ComputesInner (m' + 1) C0 ∧ C0.size = s := ⟨C.size, C, hM, hC, rfl⟩
    set s0 := Nat.find hex
    have hs0_le : s0 ≤ C.size := Nat.find_min' hex ⟨C, hM, hC, rfl⟩
    rcases Nat.find_spec hex with ⟨C0, hM0, hC0, hsz0⟩
    have hmin : ∀ C', Monotone2 C' → ComputesInner (m' + 1) C' → C0.size ≤ C'.size := fun C' h1 h2 =>
      hsz0 ▸ Nat.find_min' hex ⟨C', h1, h2, rfl⟩
    cases m' with
    | zero =>
      have ⟨_, ⟨_, _, hpos⟩, _, _, _⟩ := min_inner_props 1 (le_refl 1) C0 hM0 hC0 hmin
      omega
    | succ m'' =>
      set m := m'' + 2
      have hm : 2 ≤ m := by omega
      by_cases hcase1 : ∃ w < 2 * m,
          (∃ (j1 : ℕ) (hj1 : j1 < C0.gates.length) (j2 : ℕ) (hj2 : j2 < C0.gates.length),
            j1 ≠ j2 ∧ w ∈ (C0.gates[j1]'hj1).inputs ∧ w ∈ (C0.gates[j2]'hj2).inputs) ∨
          (∃ (j1 : ℕ) (hj1 : j1 < C0.gates.length),
            (C0.gates[j1]'hj1).op = .and ∧ w ∈ (C0.gates[j1]'hj1).inputs)
      · rcases hcase1 with ⟨w, hw, hcond⟩
        set r := if w < m then w else w - m
        have hr : r < m := by simp only [r]; split <;> omega
        set w2 := if w < m then m + r else r
        have hw12 : (w = r ∧ w2 = m + r) ∨ (w = m + r ∧ w2 = r) := by
          simp only [r, w2]; split <;> (try exact Or.inl ⟨rfl, rfl⟩)
          exact Or.inr ⟨by omega, rfl⟩
        have hdel := case1_three_deleted m hm C0 hM0 hC0 hmin r hr w w2 hw12 hcond
        let Z : ℕ → Bool := fun i => decide (i = r ∨ i = m + r)
        set Cs := simpCircuit (2 * m) Z C0
        set C1 := drop2Circuit m r Cs
        have hC1_mono : Monotone2 C1 := drop2Circuit_mono m r Cs (simpCircuit_mono (2 * m) Z C0 hM0)
        have hC1_comp : ComputesInner (m - 1) C1 := by
          apply drop2Circuit_computes m r hm hr Cs
          intro u' v'
          rw [simpCircuit_eval (2 * m) Z C0 hM0 _ (innerInput_length m _ _) (fun i hi hzi => by
            simp only [Z, decide_eq_true_eq] at hzi
            rcases hzi with rfl | rfl
            · rw [innerInput_getD_x m _ _ r hr, decide_eq_false_iff_not]; simp only [embedU]; split <;> omega
            · rw [innerInput_getD_y m _ _ r hr, decide_eq_false_iff_not]; simp only [embedV]; split <;> omega)]
          rw [hC0, decide_eq_decide]
          exact embed_lt_iff m r hm u' v'
        have hih := ih (by omega) C1 hC1_mono hC1_comp
        have hsz1 : C1.size = Cs.size := drop2Circuit_size m r Cs
        have hdel' : Cs.size + 3 ≤ C0.size := hdel
        have hm_eq : m = m'' + 2 := rfl
        omega
      · exfalso
        push Not at hcase1
        have hfan1 : ∀ w < 2 * m, ∀ (j1 : ℕ) (hj1 : j1 < C0.gates.length) (j2 : ℕ) (hj2 : j2 < C0.gates.length),
            w ∈ (C0.gates[j1]'hj1).inputs → w ∈ (C0.gates[j2]'hj2).inputs → j1 = j2 := by
          intro w hw j1 hj1 j2 hj2 h1 h2
          by_contra hne
          exact (hcase1 w hw).1 j1 hj1 j2 hj2 hne h1 h2
        have hor_only : ∀ w < 2 * m, ∀ (j : ℕ) (hj : j < C0.gates.length),
            w ∈ (C0.gates[j]'hj).inputs → (C0.gates[j]'hj).op = .or := by
          intro w hw j hj h1
          have hgj := (hM0 (C0.gates[j]'hj) (List.getElem_mem hj)).1
          have hop : (C0.gates[j]'hj).op = .and ∨ (C0.gates[j]'hj).op = .or := by simpa using hgj
          rcases hop with hand | hor
          · exact ((hcase1 w hw).2 j hj hand h1).elim
          · exact hor
        exact case2_contradiction m hm C0 hM0 hC0 hmin hfan1 hor_only

-- 8. Stage 4: Reduction from chain graph L-meta-19456 to Inner_{k - 2}

theorem oneEach_length {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_u {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact hi),
      List.getElem?_ofFn, dif_pos hi]
  simp [Fin.ext_iff]

theorem oneEach_getD_v {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
      List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos hj]
  simp [Fin.ext_iff]

-- Re-index a circuit on 2n wires down to 2m wires by mapping kept wires to 0..2m-1 and all others to dead wire
noncomputable def pullMap (n m : ℕ) (selU selV : Fin m → Fin n) (sz w : ℕ) : ℕ :=
  if w < 2 * n then
    if h : ∃ r : Fin m, (selU r).val = w then (Classical.choose h).val
    else if h2 : ∃ c : Fin m, n + (selV c).val = w then m + (Classical.choose h2).val
    else 2 * m + sz
  else 2 * m + (w - 2 * n)

noncomputable def pullCircuit (n m : ℕ) (selU selV : Fin m → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (pullMap n m selU selV C.size)⟩,
   pullMap n m selU selV C.size C.output⟩

theorem pullCircuit_size (n m : ℕ) (selU selV : Fin m → Fin n) (C : Circuit) :
    (pullCircuit n m selU selV C).size = C.size := by
  simp [pullCircuit, Circuit.size]

theorem pullCircuit_mono (n m : ℕ) (selU selV : Fin m → Fin n) (C : Circuit) (hM : Monotone2 C) :
    Monotone2 (pullCircuit n m selU selV C) := by
  intro g hg
  simp only [pullCircuit, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  exact ⟨(hM g0 hg0).1, by simp [(hM g0 hg0).2]⟩

theorem pullCircuit_wires_eq (n m : ℕ) (selU selV : Fin m → Fin n)
    (hinjU : Function.Injective selU) (hinjV : Function.Injective selV)
    (C : Circuit) (u' v' : Fin (m + 1)) (x : List Bool) (hx : x.length = 2 * n)
    (hmatch_u : ∀ r : Fin m, x.getD (selU r).val false = decide (u'.val = r.val + 1))
    (hmatch_v : ∀ c : Fin m, x.getD (n + (selV c).val) false = decide (v'.val = c.val))
    (hzero : ∀ w < 2 * n, (∀ r : Fin m, (selU r).val ≠ w) → (∀ c : Fin m, n + (selV c).val ≠ w) →
      x.getD w false = false) :
    ∀ w < 2 * n + C.size,
      ((pullCircuit n m selU selV C).wires (innerInput m u' v')).getD (pullMap n m selU selV C.size w) false =
      (C.wires x).getD w false := by
  classical
  set C' := pullCircuit n m selU selV C
  have hsz' : C'.size = C.size := pullCircuit_size n m selU selV C
  have hx' : (innerInput m u' v').length = 2 * m := innerInput_length m u' v'
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < 2 * n
    · rw [wires_getD_input C x w (by omega)]
      by_cases h1 : ∃ r : Fin m, (selU r).val = w
      · have hpm : pullMap n m selU selV C.size w = (Classical.choose h1).val := by
          unfold pullMap; simp only [hlt, ite_true, h1, dite_true]
        set r := Classical.choose h1
        have hr_eq : (selU r).val = w := Classical.choose_spec h1
        rw [hpm, wires_getD_input C' _ r.val (by omega), innerInput_getD_x m u' v' r.val r.isLt, ← hr_eq, hmatch_u r]
      · by_cases h2 : ∃ c : Fin m, n + (selV c).val = w
        · have hpm : pullMap n m selU selV C.size w = m + (Classical.choose h2).val := by
            unfold pullMap; simp only [hlt, ite_true, h1, h2, dite_true, dite_false]
          set c := Classical.choose h2
          have hc_eq : n + (selV c).val = w := Classical.choose_spec h2
          rw [hpm, wires_getD_input C' _ (m + c.val) (by omega), innerInput_getD_y m u' v' c.val c.isLt, ← hc_eq, hmatch_v c]
        · have hpm : pullMap n m selU selV C.size w = 2 * m + C.size := by
            unfold pullMap; simp only [hlt, ite_true, h1, h2, dite_false]
          rw [hpm, wires_getD_ge C' _ (2 * m + C.size) (by omega)]
          push Not at h1 h2
          exact (hzero w hlt h1 h2).symm
    · have hpm : pullMap n m selU selV C.size w = 2 * m + (w - 2 * n) := by
        unfold pullMap; simp only [hlt, ite_false]
      rw [hpm]
      have hj : w - 2 * n < C.gates.length := by simp [Circuit.size] at hw; omega
      have hj' : w - 2 * n < C'.gates.length := by simp [C', pullCircuit]; exact hj
      have heq1 : 2 * m + (w - 2 * n) = (innerInput m u' v').length + (w - 2 * n) := by omega
      have heq2 : w = x.length + (w - 2 * n) := by omega
      conv_lhs => rw [heq1]
      conv_rhs => rw [heq2]
      rw [wires_getD_gate_full C' _ (w - 2 * n) hj', wires_getD_gate_full C x (w - 2 * n) hj]
      simp only [C', pullCircuit, List.getElem_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < 2 * n + (w - 2 * n)
      · simp only [hx, hi, ite_true]
        by_cases hilt : i < 2 * n
        · by_cases h1 : ∃ r : Fin m, (selU r).val = i
          · have hpm_i : pullMap n m selU selV C.size i < 2 * m + (w - 2 * n) := by
              unfold pullMap; simp only [hilt, ite_true, h1, dite_true]; have := (Classical.choose h1).isLt; omega
            simp only [hx', hpm_i, ite_true]; exact ih i (by omega) (by omega)
          · by_cases h2 : ∃ c : Fin m, n + (selV c).val = i
            · have hpm_i : pullMap n m selU selV C.size i < 2 * m + (w - 2 * n) := by
                unfold pullMap; simp only [hilt, ite_true, h1, h2, dite_true, dite_false]; have := (Classical.choose h2).isLt; omega
              simp only [hx', hpm_i, ite_true]; exact ih i (by omega) (by omega)
            · have hpm_i : pullMap n m selU selV C.size i = 2 * m + C.size := by
                unfold pullMap; simp only [hilt, ite_true, h1, h2, dite_false]
              rw [hpm_i]
              simp only [show ¬ 2 * m + C.size < (innerInput m u' v').length + (w - 2 * n) by omega, ite_false]
              rw [wires_getD_input C x i (by omega)]
              push Not at h1 h2; exact (hzero i hilt h1 h2).symm
        · have hpm_i : pullMap n m selU selV C.size i = 2 * m + (i - 2 * n) := by
            unfold pullMap; simp only [hilt, ite_false]
          have hpm_lt : pullMap n m selU selV C.size i < (innerInput m u' v').length + (w - 2 * n) := by omega
          simp only [hpm_lt, ite_true]; exact ih i (by omega) (by omega)
      · simp only [hx, hi, ite_false]
        have hpm_ge : ¬ pullMap n m selU selV C.size i < (innerInput m u' v').length + (w - 2 * n) := by
          unfold pullMap; simp only [show ¬ i < 2 * n by omega, ite_false]; omega
        simp only [hpm_ge, ite_false]

theorem chain_graph_lower_bound (n k a b : ℕ) (hk : 3 ≤ k) (t : Fin n → ℕ)
    (ht_range : ∀ u, 1 ≤ t u ∧ t u ≤ n) (ht_max : ∃ u, t u = n)
    (hcard : (Finset.univ.image t).card = k)
    (ha : (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a)
    (hb : (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n,
      (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
      (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b)
    (s : ℕ) (hrep : RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s) :
    2 * n + k - 4 - a - b ≤ s := by
  classical
  rcases hrep with ⟨Cinit, hMinit, hSinit, hRinit⟩
  set S := Finset.univ.image t
  let emb : Fin k ↪o ℕ := S.orderEmbOfFin hcard
  let vals : Fin k → ℕ := fun i => emb i
  have hvals_mem : ∀ i : Fin k, vals i ∈ S := fun i => Finset.orderEmbOfFin_mem S hcard i
  have hvals_mono : ∀ i j : Fin k, i < j → vals i < vals j := fun i j hij => emb.strictMono hij
  have hvals_le : ∀ i j : Fin k, i ≤ j → vals i ≤ vals j := fun i j hij => emb.monotone hij
  have hvals_pos : ∀ i : Fin k, 1 ≤ vals i := fun i => by
    rcases Finset.mem_image.mp (hvals_mem i) with ⟨u, _, hu⟩
    rw [← hu]; exact (ht_range u).1
  have hvals_le_n : ∀ i : Fin k, vals i ≤ n := fun i => by
    rcases Finset.mem_image.mp (hvals_mem i) with ⟨u, _, hu⟩
    rw [← hu]; exact (ht_range u).2
  have hvals_mem_ex : ∀ x ∈ S, ∃ j : Fin k, vals j = x := by
    intro x hx
    have hrange : Set.range emb = (S : Set ℕ) := Finset.range_orderEmbOfFin S hcard
    have hx' : x ∈ Set.range emb := by rw [hrange]; exact hx
    exact Set.mem_range.mp hx'
  have hvals_last : vals ⟨k - 1, by omega⟩ = n := by
    rcases ht_max with ⟨umax, humax⟩
    have hn_mem : n ∈ S := Finset.mem_image.mpr ⟨umax, Finset.mem_univ _, humax⟩
    rcases hvals_mem_ex n hn_mem with ⟨j, hj⟩
    have hle1 : vals j ≤ vals ⟨k - 1, by omega⟩ := hvals_le j ⟨k - 1, by omega⟩ (by simp [Fin.le_def]; omega)
    have hle2 : vals ⟨k - 1, by omega⟩ ≤ n := hvals_le_n ⟨k - 1, by omega⟩
    omega
  have hvals_first_le : ∀ u : Fin n, vals ⟨0, by omega⟩ ≤ t u := by
    intro u
    have hmem : t u ∈ S := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    rcases hvals_mem_ex (t u) hmem with ⟨j, hj⟩
    rw [← hj]; exact hvals_le ⟨0, by omega⟩ j (by simp [Fin.le_def])
  -- Choose representative row repU i with t (repU i) = vals i
  have hrepU_ex : ∀ i : Fin k, ∃ u : Fin n, t u = vals i := fun i => by
    rcases Finset.mem_image.mp (hvals_mem i) with ⟨u, _, hu⟩; exact ⟨u, hu⟩
  let repU : Fin k → Fin n := fun i => Classical.choose (hrepU_ex i)
  have hrepU_spec : ∀ i : Fin k, t (repU i) = vals i := fun i => Classical.choose_spec (hrepU_ex i)
  -- Explicit representative column repV j: j = 0 -> 0, j >= 1 -> vals (j - 1)
  have hn_pos : 0 < n := by have := hvals_pos ⟨0, by omega⟩; have := hvals_le_n ⟨0, by omega⟩; omega
  let repV : Fin k → Fin n := fun j =>
    if hj : j.val = 0 then ⟨0, hn_pos⟩
    else ⟨vals ⟨j.val - 1, by omega⟩, by
      have hlt := hvals_mono ⟨j.val - 1, by omega⟩ ⟨k - 1, by omega⟩ (by simp [Fin.lt_def]; omega)
      omega⟩
  have hrepV_lt_iff : ∀ (i j : Fin k), ((repV j).val < t (repU i)) ↔ (j.val ≤ i.val) := by
    intro i j
    rw [hrepU_spec i]
    by_cases hj : j.val = 0
    · simp only [repV, hj, dite_true]
      have := hvals_pos i; omega
    · simp only [repV, hj, dite_false]
      constructor
      · intro hlt
        by_contra hgt; push Not at hgt
        have := hvals_le i ⟨j.val - 1, by omega⟩ (by simp [Fin.le_def]; omega)
        omega
      · intro hle
        exact hvals_mono ⟨j.val - 1, by omega⟩ i (by simp [Fin.lt_def]; omega)
  -- Row class a characterization
  have ha_eq : (Finset.univ.filter (fun u : Fin n => t u = vals ⟨0, by omega⟩)).card = a := by
    rw [← ha]; congr 1; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h u'; rw [h]; exact hvals_first_le u'
    · intro h
      have h1 := h (repU ⟨0, by omega⟩); rw [hrepU_spec] at h1
      have h2 := hvals_first_le u; omega
  -- Col class b characterization: minimal degree iff vals (k - 2) <= v
  have hb_eq : (Finset.univ.filter (fun v : Fin n => vals ⟨k - 2, by omega⟩ ≤ v.val)).card = b := by
    rw [← hb]; congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hdeg_ge : ∀ v : Fin n, vals ⟨k - 2, by omega⟩ ≤ v.val →
        Finset.univ.filter (fun u : Fin n => v.val < t u) = Finset.univ.filter (fun u : Fin n => t u = n) := by
      intro v hv; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hlt
        have hmem : t u ∈ S := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
        rcases hvals_mem_ex (t u) hmem with ⟨j, hj⟩
        by_cases hjk : j.val = k - 1
        · have : j = ⟨k - 1, by omega⟩ := Fin.ext hjk
          rw [← hj, this]; exact hvals_last
        · have := hvals_le j ⟨k - 2, by omega⟩ (by simp [Fin.le_def]; omega)
          omega
      · intro hn; rw [hn]; exact v.isLt
    have hdeg_sub : ∀ v' : Fin n,
        Finset.univ.filter (fun u : Fin n => t u = n) ⊆ Finset.univ.filter (fun u : Fin n => v'.val < t u) := by
      intro v' u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [hu]; exact v'.isLt
    constructor
    · intro hv v'
      rw [hdeg_ge v hv]
      exact Finset.card_le_card (hdeg_sub v')
    · intro hmin_v
      by_contra hlt; push Not at hlt
      have hv_max := hmin_v (repV ⟨k - 1, by omega⟩)
      have hrv_ge : vals ⟨k - 2, by omega⟩ ≤ (repV ⟨k - 1, by omega⟩).val := by
        simp only [repV, show ¬ k - 1 = 0 by omega, dite_false]; exact le_refl _
      rw [hdeg_ge (repV ⟨k - 1, by omega⟩) hrv_ge] at hv_max
      have hssub : Finset.univ.filter (fun u : Fin n => t u = n) ⊂ Finset.univ.filter (fun u : Fin n => v.val < t u) := by
        rw [Finset.ssubset_iff_of_subset (hdeg_sub v)]
        refine ⟨repU ⟨k - 2, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrepU_spec]; exact hlt
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrepU_spec]
          have := hvals_mono ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ (by simp [Fin.lt_def]; omega)
          omega
      have := Finset.card_lt_card hssub; omega
  -- Define kept inner wires and kill set K
  set m := k - 2
  have hm : 1 ≤ m := by omega
  let selU : Fin m → Fin n := fun r => repU ⟨r.val + 1, by omega⟩
  let selV : Fin m → Fin n := fun c => repV ⟨c.val + 1, by omega⟩
  have hselU_inj : Function.Injective selU := by
    intro r1 r2 h
    have ht : t (selU r1) = t (selU r2) := congrArg t h
    simp only [selU, hrepU_spec] at ht
    have heq := emb.injective ht
    exact Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
  have hselV_val : ∀ c : Fin m, (selV c).val = vals ⟨c.val, by omega⟩ := by
    intro c
    simp only [selV, repV, show ¬ (⟨c.val + 1, by omega⟩ : Fin k).val = 0 by simp, dite_false, Nat.add_sub_cancel]
  have hselV_inj : Function.Injective selV := by
    intro c1 c2 h
    have hv : (selV c1).val = (selV c2).val := congrArg Fin.val h
    rw [hselV_val c1, hselV_val c2] at hv
    have heq := emb.injective hv
    exact Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
  let AliveU : Finset (Fin n) := Finset.univ.filter fun u => u = repU ⟨0, by omega⟩ ∨ ∃ r : Fin m, u = selU r
  let AliveV : Finset (Fin n) := Finset.univ.filter fun v => v = repV ⟨k - 1, by omega⟩ ∨ ∃ c : Fin m, v = selV c
  let KillU : Finset (Fin n) := (Finset.univ.filter fun u => t u ≠ vals ⟨0, by omega⟩) \ (Finset.univ.image selU)
  let KillV : Finset (Fin n) := (Finset.univ.filter fun v : Fin n => v.val < vals ⟨k - 2, by omega⟩) \ (Finset.univ.image selV)
  have hKillU_card : KillU.card = n - a - m := by
    have hsub : Finset.univ.image selU ⊆ Finset.univ.filter (fun u : Fin n => t u ≠ vals ⟨0, by omega⟩) := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨r, _, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, selU, hrepU_spec]
      have := hvals_mono ⟨0, by omega⟩ ⟨r.val + 1, by omega⟩ (by simp [Fin.lt_def])
      omega
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_image_of_injective _ hselU_inj, Finset.card_univ, Fintype.card_fin]
    have hcomp : (Finset.univ.filter fun u : Fin n => t u ≠ vals ⟨0, by omega⟩).card +
        (Finset.univ.filter fun u : Fin n => t u = vals ⟨0, by omega⟩).card = n := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun u => t u = vals ⟨0, by omega⟩)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      change (Finset.univ.filter fun u : Fin n => t u = vals ⟨0, by omega⟩).card +
          (Finset.univ.filter fun u : Fin n => t u ≠ vals ⟨0, by omega⟩).card = n at this
      omega
    omega
  have hKillV_card : KillV.card = n - b - m := by
    have hsub : Finset.univ.image selV ⊆ Finset.univ.filter (fun v : Fin n => v.val < vals ⟨k - 2, by omega⟩) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨c, _, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hselV_val]
      exact hvals_mono ⟨c.val, by omega⟩ ⟨k - 2, by omega⟩ (by simp [Fin.lt_def]; omega)
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_image_of_injective _ hselV_inj, Finset.card_univ, Fintype.card_fin]
    have hcomp : (Finset.univ.filter fun v : Fin n => v.val < vals ⟨k - 2, by omega⟩).card +
        (Finset.univ.filter fun v : Fin n => vals ⟨k - 2, by omega⟩ ≤ v.val).card = n := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun v : Fin n => vals ⟨k - 2, by omega⟩ ≤ v.val)
      simp only [Finset.card_univ, Fintype.card_fin, not_le] at this
      omega
    omega
  -- Check a + k - 1 <= n and b + k - 1 <= n (no Nat subtraction underflow)
  have hna_ge : k - 1 ≤ n - a := by
    have hsub : (Finset.univ.filter (fun i : Fin k => 0 < i.val)).image repU ⊆
        Finset.univ.filter (fun u : Fin n => t u ≠ vals ⟨0, by omega⟩) := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hrepU_spec i]
      have := hvals_mono ⟨0, by omega⟩ i (by simp [Fin.lt_def]; omega)
      omega
    have hinj : Function.Injective repU := fun i j h => emb.injective (by
      change vals i = vals j; rw [← hrepU_spec i, ← hrepU_spec j, h])
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hc1
    have hfil : (Finset.univ.filter (fun i : Fin k => 0 < i.val)).card = k - 1 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k))) (p := fun i : Fin k => i.val = 0)
      have h0 : (Finset.univ.filter (fun i : Fin k => i.val = 0)).card = 1 := by
        have : Finset.univ.filter (fun i : Fin k => i.val = 0) = {⟨0, by omega⟩} := by
          ext i; simp [Fin.ext_iff]
        rw [this, Finset.card_singleton]
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have heq : Finset.univ.filter (fun i : Fin k => 0 < i.val) = Finset.univ.filter (fun i : Fin k => ¬ i.val = 0) := by
        ext i; simp; omega
      rw [heq]; omega
    have hcomp : (Finset.univ.filter fun u : Fin n => t u ≠ vals ⟨0, by omega⟩).card + a = n := by
      rw [← ha_eq]
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun u => t u = vals ⟨0, by omega⟩)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      change (Finset.univ.filter fun u : Fin n => t u = vals ⟨0, by omega⟩).card +
          (Finset.univ.filter fun u : Fin n => t u ≠ vals ⟨0, by omega⟩).card = n at this
      omega
    omega
  have hnb_ge : k - 1 ≤ n - b := by
    have hsub : (Finset.univ.filter (fun j : Fin k => j.val < k - 1)).image repV ⊆
        Finset.univ.filter (fun v : Fin n => v.val < vals ⟨k - 2, by omega⟩) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_cases hj0 : j.val = 0
      · simp only [repV, hj0, dite_true]; have := hvals_pos ⟨k - 2, by omega⟩; omega
      · simp only [repV, hj0, dite_false]
        exact hvals_mono ⟨j.val - 1, by omega⟩ ⟨k - 2, by omega⟩ (by simp [Fin.lt_def]; omega)
    have hinj : Function.Injective repV := by
      intro j1 j2 h
      have hv := congrArg Fin.val h
      by_cases h1 : j1.val = 0 <;> by_cases h2 : j2.val = 0
      · exact Fin.ext (by omega)
      · simp only [repV, h1, h2, dite_true, dite_false] at hv
        have := hvals_pos ⟨j2.val - 1, by omega⟩; omega
      · simp only [repV, h1, h2, dite_true, dite_false] at hv
        have := hvals_pos ⟨j1.val - 1, by omega⟩; omega
      · simp only [repV, h1, h2, dite_false] at hv
        have heq := emb.injective hv
        exact Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hc1
    have hfil : (Finset.univ.filter (fun j : Fin k => j.val < k - 1)).card = k - 1 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k))) (p := fun j : Fin k => j.val = k - 1)
      have h0 : (Finset.univ.filter (fun j : Fin k => j.val = k - 1)).card = 1 := by
        have : Finset.univ.filter (fun j : Fin k => j.val = k - 1) = {⟨k - 1, by omega⟩} := by
          ext j; simp [Fin.ext_iff]
        rw [this, Finset.card_singleton]
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have heq : Finset.univ.filter (fun j : Fin k => j.val < k - 1) = Finset.univ.filter (fun j : Fin k => ¬ j.val = k - 1) := by
        ext j; simp; omega
      rw [heq]; omega
    have hcomp : (Finset.univ.filter fun v : Fin n => v.val < vals ⟨k - 2, by omega⟩).card + b = n := by
      rw [← hb_eq]
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun v : Fin n => vals ⟨k - 2, by omega⟩ ≤ v.val)
      simp only [Finset.card_univ, Fintype.card_fin, not_le] at this; omega
    omega
  -- Inductive elimination over subsets KU <= KillU, KV <= KillV
  have hind : ∀ (sz : ℕ) (KU : Finset (Fin n)) (KV : Finset (Fin n)),
      KU ⊆ KillU → KV ⊆ KillV → KU.card + KV.card = sz →
      ∀ C : Circuit, Monotone2 C →
      (∀ u ∈ AliveU ∪ KU, ∀ v ∈ AliveV ∪ KV, C.eval (oneEach u v) = decide (v.val < t u)) →
      sz + (3 * m - 2) ≤ C.size := by
    intro sz
    induction sz with
    | zero =>
      intro KU KV _ _ hcard0 C hM hRep
      -- Base: C represents AliveU x AliveV; pull back to Inner_m
      let C' := pullCircuit n m selU selV C
      have hM' : Monotone2 C' := pullCircuit_mono n m selU selV C hM
      have hComp' : ComputesInner m C' := by
        intro u' v'
        set u : Fin n := if hu : u'.val = 0 then repU ⟨0, by omega⟩ else selU ⟨u'.val - 1, by omega⟩
        set v : Fin n := if hv : v'.val = m then repV ⟨k - 1, by omega⟩ else selV ⟨v'.val, by omega⟩
        have hu_mem : u ∈ AliveU ∪ KU := Finset.mem_union_left _ (by
          simp only [AliveU, Finset.mem_filter, Finset.mem_univ, true_and, u]
          split
          · exact Or.inl rfl
          · exact Or.inr ⟨⟨u'.val - 1, by omega⟩, rfl⟩)
        have hv_mem : v ∈ AliveV ∪ KV := Finset.mem_union_left _ (by
          simp only [AliveV, Finset.mem_filter, Finset.mem_univ, true_and, v]
          split
          · exact Or.inl rfl
          · exact Or.inr ⟨⟨v'.val, by omega⟩, rfl⟩)
        have hA_eq : decide (v.val < t u) = decide (v'.val < u'.val) := by
          have hu_rep : u = repU ⟨u'.val, by omega⟩ := by
            simp only [u, selU]; split
            · next h => congr 1; exact Fin.ext (by simp [h])
            · next h => congr 1; exact Fin.ext (by simp; omega)
          have hv_rep : v = repV ⟨v'.val + 1, by omega⟩ := by
            simp only [v, selV]; split
            · next h => congr 1; exact Fin.ext (by simp; omega)
            · next h => rfl
          rw [hu_rep, hv_rep, decide_eq_decide, hrepV_lt_iff]; simp
        have hC_uv : C.eval (oneEach u v) = decide (v'.val < u'.val) := (hRep u hu_mem v hv_mem).trans hA_eq
        -- Construct x0 := oneEach u v with repU 0 and repV (k-1) zeroed out
        let x0 : List Bool := (List.range (2 * n)).map fun w =>
          if (∃ r : Fin m, (selU r).val = w) ∨ (∃ c : Fin m, n + (selV c).val = w) then (oneEach u v).getD w false else false
        have hx0_len : x0.length = 2 * n := by simp [x0]
        have hx0_getD : ∀ w < 2 * n, x0.getD w false =
            if (∃ r : Fin m, (selU r).val = w) ∨ (∃ c : Fin m, n + (selV c).val = w) then (oneEach u v).getD w false else false := by
          intro w hw
          simp [x0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
        have hpull_eq : C'.eval (innerInput m u' v') = C.eval x0 := by
          unfold Circuit.eval
          have hsz' : C'.size = C.size := pullCircuit_size n m selU selV C
          have hx' : (innerInput m u' v').length = 2 * m := innerInput_length m u' v'
          have hmu : ∀ r : Fin m, x0.getD (selU r).val false = decide (u'.val = r.val + 1) := by
            intro r
            rw [hx0_getD (selU r).val (by have := (selU r).isLt; omega)]
            simp only [show (∃ r0 : Fin m, (selU r0).val = (selU r).val) ∨ (∃ c : Fin m, n + (selV c).val = (selU r).val) from Or.inl ⟨r, rfl⟩,
              ite_true, oneEach_getD_u u v (selU r).val (selU r).isLt]
            simp only [u]; split
            · next hu0 =>
              simp only [decide_eq_decide]
              constructor
              · intro heq; have ht := congrArg t (Fin.ext heq)
                simp only [selU, hrepU_spec] at ht
                have := hvals_mono ⟨0, by omega⟩ ⟨r.val + 1, by omega⟩ (by simp [Fin.lt_def]); omega
              · intro h; omega
            · next hu0 =>
              simp only [decide_eq_decide]
              constructor
              · intro heq; have := hselU_inj (Fin.ext heq); have := congrArg Fin.val this; simp at this; omega
              · intro heq; have : r = ⟨u'.val - 1, by omega⟩ := Fin.ext (by simp; omega); rw [this]
          have hmv : ∀ c : Fin m, x0.getD (n + (selV c).val) false = decide (v'.val = c.val) := by
            intro c
            rw [hx0_getD (n + (selV c).val) (by have := (selV c).isLt; omega)]
            simp only [show (∃ r0 : Fin m, (selU r0).val = n + (selV c).val) ∨ (∃ c0 : Fin m, n + (selV c0).val = n + (selV c).val) from Or.inr ⟨c, rfl⟩,
              ite_true, oneEach_getD_v u v (selV c).val (selV c).isLt]
            simp only [v]; split
            · next hvm =>
              simp only [decide_eq_decide]
              constructor
              · intro heq
                have hv_lt : (selV c).val < vals ⟨k - 2, by omega⟩ := by
                  rw [hselV_val c]
                  exact hvals_mono ⟨c.val, by omega⟩ ⟨k - 2, by omega⟩ (by simp [Fin.lt_def]; omega)
                have hv_ge : vals ⟨k - 2, by omega⟩ ≤ (repV ⟨k - 1, by omega⟩).val := by
                  simp only [repV, show ¬ k - 1 = 0 by omega, dite_false]
                  have hidx : (⟨k - 1 - 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by simp; omega)
                  rw [hidx]
                omega
              · intro h; have := c.isLt; omega
            · next hvm =>
              simp only [decide_eq_decide]
              constructor
              · intro heq; have := hselV_inj (Fin.ext heq); have := congrArg Fin.val this; simp at this; omega
              · intro heq; have : c = ⟨v'.val, by omega⟩ := Fin.ext heq.symm; rw [this]
          have hzr : ∀ w < 2 * n, (∀ r : Fin m, (selU r).val ≠ w) → (∀ c : Fin m, n + (selV c).val ≠ w) →
              x0.getD w false = false := by
            intro w hw h1 h2; rw [hx0_getD w hw]
            simp only [show ¬ ((∃ r : Fin m, (selU r).val = w) ∨ (∃ c : Fin m, n + (selV c).val = w)) by
              rintro (⟨r, hr⟩ | ⟨c, hc⟩); exact h1 r hr; exact h2 c hc, ite_false]
          by_cases hout : C.output < 2 * n + C.size
          · exact pullCircuit_wires_eq n m selU selV hselU_inj hselV_inj C u' v' x0 hx0_len hmu hmv hzr C.output hout
          · change (C'.wires (innerInput m u' v')).getD (pullMap n m selU selV C.size C.output) false = (C.wires x0).getD C.output false
            have hpm_ge : 2 * m + C'.size ≤ pullMap n m selU selV C.size C.output := by
              unfold pullMap; simp only [show ¬ C.output < 2 * n by omega, ite_false]; omega
            rw [wires_getD_ge C' _ _ (by omega), wires_getD_ge C _ _ (by omega)]
        rw [hpull_eq]
        by_cases hvu : v'.val < u'.val
        · -- Both u' != 0 and v' != m, so x0 = oneEach u v!
          have hx0_eq : x0 = oneEach u v := by
            apply List.ext_getElem (by rw [hx0_len, oneEach_length])
            intro i h1 h2
            have hi : i < 2 * n := by omega
            have hg1 : x0.getD i false = x0[i]'h1 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
            have hg2 : (oneEach u v).getD i false = (oneEach u v)[i]'h2 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
            rw [← hg1, ← hg2, hx0_getD i hi]
            split
            · rfl
            · next hnot =>
              symm; by_cases hin : i < n
              · rw [oneEach_getD_u u v i hin, decide_eq_false_iff_not]
                intro heq; apply hnot; left
                refine ⟨⟨u'.val - 1, by omega⟩, ?_⟩
                simp only [u, show ¬ u'.val = 0 by omega, dite_false] at heq; exact heq.symm
              · have hc : i - n < n := by omega
                have heqi : n + (i - n) = i := by omega
                rw [← heqi, oneEach_getD_v u v (i - n) hc, decide_eq_false_iff_not]
                intro heq; apply hnot; right
                refine ⟨⟨v'.val, by omega⟩, ?_⟩
                simp only [v, show ¬ v'.val = m by omega, dite_false] at heq; omega
          rw [hx0_eq, hC_uv]
        · -- x0 <= oneEach u v pointwise, so C.eval x0 <= C.eval (oneEach u v) = false
          rw [decide_eq_false hvu] at hC_uv ⊢
          have hle := wires_mono_except C hM x0 (oneEach u v) (by rw [hx0_len, oneEach_length]) (fun _ => False)
            (fun i hi _ htr => by
              rw [hx0_len] at hi; rw [hx0_getD i hi] at htr; split at htr; exact htr; cases htr)
            (fun _ _ ⟨_, _, hf⟩ => hf.elim) C.output (fun h => h)
          cases h : C.eval x0 with
          | false => rfl
          | true => unfold Circuit.eval at h hC_uv; rw [hle h] at hC_uv; cases hC_uv
      have hlb := inner_lower_bound m hm C' hM' hComp'
      have hsz' : C'.size = C.size := pullCircuit_size n m selU selV C
      omega
    | succ sz' ih =>
      intro KU KV hKU hKV hcard_sz C hM hRep
      -- Take minimal circuit C0 for (AliveU U KU) x (AliveV U KV)
      have hex : ∃ s0, ∃ C0, Monotone2 C0 ∧
          (∀ u ∈ AliveU ∪ KU, ∀ v ∈ AliveV ∪ KV, C0.eval (oneEach u v) = decide (v.val < t u)) ∧
          C0.size = s0 := ⟨C.size, C, hM, hRep, rfl⟩
      set s0 := Nat.find hex
      have hs0_le : s0 ≤ C.size := Nat.find_min' hex ⟨C, hM, hRep, rfl⟩
      rcases Nat.find_spec hex with ⟨C0, hM0, hRep0, hsz0⟩
      have hmin0 : ∀ C', Monotone2 C' →
          (∀ u ∈ AliveU ∪ KU, ∀ v ∈ AliveV ∪ KV, C'.eval (oneEach u v) = decide (v.val < t u)) →
          C0.size ≤ C'.size := fun C' h1 h2 => hsz0 ▸ Nat.find_min' hex ⟨C', h1, h2, rfl⟩
      have hu0_mem : repU ⟨0, by omega⟩ ∈ AliveU ∪ KU :=
        Finset.mem_union_left _ (by simp [AliveU])
      have hvlast_mem : repV ⟨k - 1, by omega⟩ ∈ AliveV ∪ KV :=
        Finset.mem_union_left _ (by simp [AliveV])
      have hu1_mem : selU ⟨0, by omega⟩ ∈ AliveU ∪ KU :=
        Finset.mem_union_left _ (by simp only [AliveU, Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inr ⟨⟨0, by omega⟩, rfl⟩)
      have hv1_mem : selV ⟨0, by omega⟩ ∈ AliveV ∪ KV :=
        Finset.mem_union_left _ (by simp only [AliveV, Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inr ⟨⟨0, by omega⟩, rfl⟩)
      have hC0_zero : C0.eval (oneEach (repU ⟨0, by omega⟩) (repV ⟨k - 1, by omega⟩)) = false := by
        rw [hRep0 _ hu0_mem _ hvlast_mem, decide_eq_false_iff_not, hrepV_lt_iff]; simp; omega
      have hC0_one : C0.eval (oneEach (selU ⟨0, by omega⟩) (selV ⟨0, by omega⟩)) = true := by
        rw [hRep0 _ hu1_mem _ hv1_mem, decide_eq_true_eq]
        exact (hrepV_lt_iff ⟨1, by omega⟩ ⟨1, by omega⟩).mpr (le_refl _)
      -- All gates of C0 are kept under simpRes (2*n) (fun _ => false)
      have hall_kept : ∀ j (hj : j < C0.gates.length),
          ∃ nw, (simpRes (2 * n) (fun _ => false) C0).1[j]? = some (.kept nw) := by
        have hnt : resolveWire (2 * n) (fun _ => false) (simpRes (2 * n) (fun _ => false) C0).1 C0.output ≠ .vtrue := by
          intro hvt
          have hE := (simpRes_props (2 * n) (fun _ => false) C0 hM0).2.2
            (oneEach (repU ⟨0, by omega⟩) (repV ⟨k - 1, by omega⟩)) (oneEach_length _ _) (fun _ _ h => by cases h)
          have hout := hE.2 C0.output; rw [hvt] at hout
          unfold Circuit.eval at hC0_zero; rw [hC0_zero] at hout; simp [evalWVal] at hout
        have hle := hmin0 (simpCircuit (2 * n) (fun _ => false) C0) (simpCircuit_mono _ _ C0 hM0) (fun u hu v hv => by
          rw [simpCircuit_eval (2 * n) (fun _ => false) C0 hM0 _ (oneEach_length u v) (fun _ _ h => by cases h)]
          exact hRep0 u hu v hv)
        rw [simpCircuit_size_of_not_vtrue (2 * n) (fun _ => false) C0 hM0 hnt] at hle
        have hlen := (simpRes_props (2 * n) (fun _ => false) C0 hM0).1
        intro j hj
        have hj' : j < (simpRes (2 * n) (fun _ => false) C0).1.length := by simp [Circuit.size] at hlen; omega
        set stj := (simpRes (2 * n) (fun _ => false) C0).1[j]'hj'
        have hs : (simpRes (2 * n) (fun _ => false) C0).1[j]? = some stj := List.getElem?_eq_getElem hj'
        by_cases hsk : stj.isKept = true
        · cases hs_eq : stj with
          | cfalse => rw [hs_eq] at hsk; cases hsk
          | ctrue => rw [hs_eq] at hsk; cases hsk
          | wref _ => rw [hs_eq] at hsk; cases hsk
          | kept nw => rw [hs_eq] at hs; exact ⟨nw, hs⟩
        · have hsf : stj.isKept = false := Bool.eq_false_iff.mpr hsk
          have hbd := countP_add_card_false (simpRes (2 * n) (fun _ => false) C0).1 WStatus.isKept {j}
            (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact ⟨stj, hs, hsf⟩)
          simp only [Finset.card_singleton] at hbd; omega
      have hshape0 := simpRes_all_kept_shape (2 * n) C0 hM0 hall_kept
      have hout_lt : C0.output < 2 * n + C0.size := by
        by_contra hge; push Not at hge
        unfold Circuit.eval at hC0_one
        rw [wires_getD_ge C0 _ C0.output (by rw [oneEach_length]; omega)] at hC0_one; cases hC0_one
      -- Helper: if w < 2*n is read by some gate, setting Z w = true deletes >= 1 gate
      have hkill_one : ∀ (w : ℕ), w < 2 * n →
          (w ≠ (repU ⟨0, by omega⟩).val ∧ w ≠ n + (repV ⟨k - 1, by omega⟩).val) →
          (∃ (j : ℕ) (hj : j < C0.gates.length), w ∈ (C0.gates[j]'hj).inputs) →
          (simpCircuit (2 * n) (fun i => decide (i = w)) C0).size + 1 ≤ C0.size := by
        intro w hw hne hread
        rcases hne with ⟨hne0, hnel⟩
        rcases hread with ⟨j, hj, hwin⟩
        let Zw : ℕ → Bool := fun i => decide (i = w)
        have hnt : resolveWire (2 * n) Zw (simpRes (2 * n) Zw C0).1 C0.output ≠ .vtrue := by
          intro hvt
          have hE := (simpRes_props (2 * n) Zw C0 hM0).2.2
            (oneEach (repU ⟨0, by omega⟩) (repV ⟨k - 1, by omega⟩)) (oneEach_length _ _) (fun i hi hzi => by
              simp only [Zw, decide_eq_true_eq] at hzi; rw [hzi]
              by_cases hin : w < n
              · rw [oneEach_getD_u _ _ w hin]; simp [hne0]
              · have hc : w - n < n := by omega
                have heqw : n + (w - n) = w := by omega
                have hget := oneEach_getD_v (repU ⟨0, by omega⟩) (repV ⟨k - 1, by omega⟩) (w - n) hc
                rw [heqw] at hget; rw [hget]; simp; omega)
          have hout := hE.2 C0.output; rw [hvt] at hout
          unfold Circuit.eval at hC0_zero; rw [hC0_zero] at hout; simp [evalWVal] at hout
        rw [simpCircuit_size_of_not_vtrue (2 * n) Zw C0 hM0 hnt]
        have hrv : resolveWire (2 * n) Zw (simpRes (2 * n) Zw C0).1 w = .vfalse := by
          unfold resolveWire; simp [hw, Zw]
        rcases hshape0 j hj with ⟨a1, b1, hop1, hin1, ha1, hb1, _⟩
        rw [hin1] at hwin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
        have hdel := simpRes_not_kept_of_vfalse (2 * n) Zw C0 j hj a1 b1 hop1 hin1 ha1 hb1
          (by rcases hwin with rfl | rfl; exact Or.inl hrv; exact Or.inr hrv)
        have hbd := countP_add_card_false (simpRes (2 * n) Zw C0).1 WStatus.isKept {j}
          (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hdel)
        have hlen := (simpRes_props (2 * n) Zw C0 hM0).1
        simp only [Finset.card_singleton] at hbd; omega
      by_cases hKUne : KU.Nonempty
      · -- Pick u in KU and kill wire u.val
        rcases hKUne with ⟨u, huKU⟩
        have huKill : u ∈ KillU := hKU huKU
        have hu_tne : t u ≠ vals ⟨0, by omega⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp huKill).1).2
        have hu_not_sel : ∀ r : Fin m, selU r ≠ u := fun r h => (Finset.mem_sdiff.mp huKill).2 (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, h⟩)
        have hu_ne_u0 : u ≠ repU ⟨0, by omega⟩ := fun h => hu_tne (by rw [h, hrepU_spec])
        -- Find witness v in AliveV with A u v = true and A (repU 0) v = false
        have hwit_v : ∃ v ∈ AliveV ∪ KV, decide (v.val < t u) = true ∧ decide (v.val < t (repU ⟨0, by omega⟩)) = false := by
          have hmem : t u ∈ S := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
          rcases hvals_mem_ex (t u) hmem with ⟨j, hj⟩
          have hj_pos : 0 < j.val := by
            by_contra h0; push Not at h0
            have : j = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [this] at hj; exact hu_tne hj.symm
          refine ⟨repV j, ?_, ?_, ?_⟩
          · apply Finset.mem_union_left
            simp only [AliveV, Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hjk : j.val = k - 1
            · exact Or.inl (congrArg repV (Fin.ext hjk))
            · exact Or.inr ⟨⟨j.val - 1, by omega⟩, by simp only [selV]; congr 1; exact Fin.ext (by simp; omega)⟩
          · rw [decide_eq_true_eq]
            have : t u = t (repU j) := by rw [hrepU_spec j]; exact hj.symm
            rw [this]; exact (hrepV_lt_iff j j).mpr (le_refl _)
          · rw [decide_eq_false_iff_not, hrepV_lt_iff]; simp; omega
        rcases hwit_v with ⟨vw, hvw_mem, hA_u, hA_u0⟩
        -- u.val is read by some gate of C0 (and C0.output != u.val)
        have hout_ne_u : C0.output ≠ u.val := by
          intro hout
          have h1 := hC0_one; unfold Circuit.eval at h1
          rw [hout, wires_getD_input C0 _ u.val (by rw [oneEach_length]; omega), oneEach_getD_u _ _ u.val u.isLt] at h1
          simp at h1; exact hu_not_sel ⟨0, by omega⟩ (Fin.ext h1.symm)
        have hu_read : ∃ (j : ℕ) (hj : j < C0.gates.length), u.val ∈ (C0.gates[j]'hj).inputs := by
          by_contra hno; push Not at hno
          have hle := wires_mono_except C0 hM0 (oneEach u vw) (oneEach (repU ⟨0, by omega⟩) vw)
            (by simp [oneEach_length]) (fun w => w = u.val)
            (fun i hi hne htr => by
              rw [oneEach_length] at hi
              by_cases hin : i < n
              · rw [oneEach_getD_u u vw i hin] at htr; simp at htr; omega
              · have hc : i - n < n := by omega
                have heqi : n + (i - n) = i := by omega
                rw [← heqi, oneEach_getD_v u vw (i - n) hc] at htr
                rw [← heqi, oneEach_getD_v _ vw (i - n) hc]; exact htr)
            (fun j hj ⟨i, hi, hexi⟩ _ => (hno j hj (hexi ▸ hi)).elim)
            C0.output hout_ne_u (by
              have h1 := hRep0 u (Finset.mem_union_right _ huKU) vw hvw_mem
              unfold Circuit.eval at h1; rw [hA_u] at h1; exact h1)
          have h2 := hRep0 (repU ⟨0, by omega⟩) hu0_mem vw hvw_mem
          unfold Circuit.eval at h2; rw [hle, hA_u0] at h2; cases h2
        have hdel := hkill_one u.val (by omega) ⟨Fin.val_ne_of_ne hu_ne_u0, by omega⟩ hu_read
        set C1 := simpCircuit (2 * n) (fun i => decide (i = u.val)) C0
        have hM1 : Monotone2 C1 := simpCircuit_mono (2 * n) _ C0 hM0
        have hRep1 : ∀ u' ∈ AliveU ∪ KU.erase u, ∀ v' ∈ AliveV ∪ KV, C1.eval (oneEach u' v') = decide (v'.val < t u') := by
          intro u' hu' v' hv'
          have hu'_ne : u' ≠ u := by
            rcases Finset.mem_union.mp hu' with hA | hK
            · simp only [AliveU, Finset.mem_filter, Finset.mem_univ, true_and] at hA
              rcases hA with rfl | ⟨r, rfl⟩
              · exact hu_ne_u0.symm
              · exact hu_not_sel r
            · exact (Finset.mem_erase.mp hK).1
          rw [simpCircuit_eval (2 * n) _ C0 hM0 (oneEach u' v') (oneEach_length u' v') (fun i hi hzi => by
            simp only [decide_eq_true_eq] at hzi; rw [hzi]
            rw [oneEach_getD_u u' v' u.val u.isLt, decide_eq_false_iff_not]
            exact Fin.val_ne_of_ne hu'_ne.symm)]
          exact hRep0 u' (by
            rcases Finset.mem_union.mp hu' with hA | hK
            · exact Finset.mem_union_left _ hA
            · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hK)) v' hv'
        have hcard_er : (KU.erase u).card + KV.card = sz' := by
          have := Finset.card_erase_of_mem huKU
          have hpos : 1 ≤ KU.card := Finset.card_pos.mpr ⟨u, huKU⟩
          omega
        have hih := ih (KU.erase u) KV (Finset.Subset.trans (Finset.erase_subset u KU) hKU) hKV hcard_er C1 hM1 hRep1
        omega
      · -- KU is empty, so KV is nonempty; pick v in KV and kill wire n + v.val
        have hKU_emp : KU = ∅ := Finset.not_nonempty_iff_eq_empty.mp hKUne
        have hKVne : KV.Nonempty := Finset.card_pos.mp (by rw [hKU_emp, Finset.card_empty] at hcard_sz; omega)
        rcases hKVne with ⟨v, hvKV⟩
        have hvKill : v ∈ KillV := hKV hvKV
        have hv_lt : v.val < vals ⟨k - 2, by omega⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvKill).1).2
        have hv_not_sel : ∀ c : Fin m, selV c ≠ v := fun c h => (Finset.mem_sdiff.mp hvKill).2 (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, h⟩)
        have hv_ne_vl : v ≠ repV ⟨k - 1, by omega⟩ := by
          intro h
          have hge : vals ⟨k - 2, by omega⟩ ≤ (repV ⟨k - 1, by omega⟩).val := by
            simp only [repV, show ¬ k - 1 = 0 by omega, dite_false]
            have hidx : (⟨k - 1 - 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by simp; omega)
            rw [hidx]
          rw [h] at hv_lt; omega
        -- Find witness u in AliveU with A u v = true and A u (repV (k-1)) = false
        have hwit_u : ∃ u ∈ AliveU ∪ KU, decide (v.val < t u) = true ∧ decide ((repV ⟨k - 1, by omega⟩).val < t u) = false := by
          refine ⟨selU ⟨m - 1, by omega⟩, Finset.mem_union_left _ (by
            simp only [AliveU, Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inr ⟨⟨m - 1, by omega⟩, rfl⟩), ?_, ?_⟩
          · rw [decide_eq_true_eq]; simp only [selU, hrepU_spec]
            have : (⟨m - 1 + 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by simp; omega)
            rw [this]; exact hv_lt
          · rw [decide_eq_false_iff_not]; simp only [selU, hrepU_spec, repV, show ¬ k - 1 = 0 by omega, dite_false]
            have h1 : (⟨m - 1 + 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by simp; omega)
            have h2 : (⟨k - 1 - 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by simp; omega)
            rw [h1, h2]; omega
        rcases hwit_u with ⟨uw, huw_mem, hA_v, hA_vl⟩
        have hout_ne_v : C0.output ≠ n + v.val := by
          intro hout
          have h1 := hC0_one; unfold Circuit.eval at h1
          rw [hout, wires_getD_input C0 _ (n + v.val) (by rw [oneEach_length]; omega), oneEach_getD_v _ _ v.val v.isLt] at h1
          simp at h1; exact hv_not_sel ⟨0, by omega⟩ (Fin.ext h1.symm)
        have hv_read : ∃ (j : ℕ) (hj : j < C0.gates.length), n + v.val ∈ (C0.gates[j]'hj).inputs := by
          by_contra hno; push Not at hno
          have hle := wires_mono_except C0 hM0 (oneEach uw v) (oneEach uw (repV ⟨k - 1, by omega⟩))
            (by simp [oneEach_length]) (fun w => w = n + v.val)
            (fun i hi hne htr => by
              rw [oneEach_length] at hi
              by_cases hin : i < n
              · rw [oneEach_getD_u uw v i hin] at htr
                rw [oneEach_getD_u uw _ i hin]; exact htr
              · have hc : i - n < n := by omega
                have heqi : n + (i - n) = i := by omega
                rw [← heqi, oneEach_getD_v uw v (i - n) hc] at htr; simp at htr; omega)
            (fun j hj ⟨i, hi, hexi⟩ _ => (hno j hj (hexi ▸ hi)).elim)
            C0.output hout_ne_v (by
              have h1 := hRep0 uw huw_mem v (Finset.mem_union_right _ hvKV)
              unfold Circuit.eval at h1; rw [hA_v] at h1; exact h1)
          have h2 := hRep0 uw huw_mem (repV ⟨k - 1, by omega⟩) hvlast_mem
          unfold Circuit.eval at h2; rw [hle, hA_vl] at h2; cases h2
        have hdel := hkill_one (n + v.val) (by omega) ⟨by omega, by intro h; exact hv_ne_vl (Fin.ext (by omega))⟩ hv_read
        set C1 := simpCircuit (2 * n) (fun i => decide (i = n + v.val)) C0
        have hM1 : Monotone2 C1 := simpCircuit_mono (2 * n) _ C0 hM0
        have hRep1 : ∀ u' ∈ AliveU ∪ KU, ∀ v' ∈ AliveV ∪ KV.erase v, C1.eval (oneEach u' v') = decide (v'.val < t u') := by
          intro u' hu' v' hv'
          have hv'_ne : v' ≠ v := by
            rcases Finset.mem_union.mp hv' with hA | hK
            · simp only [AliveV, Finset.mem_filter, Finset.mem_univ, true_and] at hA
              rcases hA with rfl | ⟨c, rfl⟩
              · exact hv_ne_vl.symm
              · exact hv_not_sel c
            · exact (Finset.mem_erase.mp hK).1
          rw [simpCircuit_eval (2 * n) _ C0 hM0 (oneEach u' v') (oneEach_length u' v') (fun i hi hzi => by
            simp only [decide_eq_true_eq] at hzi; rw [hzi]
            rw [oneEach_getD_v u' v' v.val v.isLt, decide_eq_false_iff_not]
            exact Fin.val_ne_of_ne hv'_ne.symm)]
          exact hRep0 u' hu' v' (by
            rcases Finset.mem_union.mp hv' with hA | hK
            · exact Finset.mem_union_left _ hA
            · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hK))
        have hcard_er : KU.card + (KV.erase v).card = sz' := by
          have := Finset.card_erase_of_mem hvKV
          have hpos : 1 ≤ KV.card := Finset.card_pos.mpr ⟨v, hvKV⟩
          omega
        have hih := ih KU (KV.erase v) hKU (Finset.Subset.trans (Finset.erase_subset v KV) hKV) hcard_er C1 hM1 hRep1
        omega
  have hmain := hind (KillU.card + KillV.card) KillU KillV (Finset.Subset.refl _) (Finset.Subset.refl _) rfl
    Cinit hMinit (fun u _ v _ => hRinit u v)
  omega

end PEqualNP.Outside.L_meta_19456

theorem PEqualNP.Outside.L_meta_19456 :
    ∀ n k a b : ℕ, 3 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s := by
  intro n k a b hk t ht_range ht_max hcard ha hb s hrep
  exact PEqualNP.Outside.L_meta_19456.chain_graph_lower_bound n k a b hk t ht_range ht_max hcard ha hb s hrep
