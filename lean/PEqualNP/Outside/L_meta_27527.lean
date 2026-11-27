import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27527

open PEqualNP.CircuitLowerBounds

def pack8 (f : Fin 8 → Bool) : Nat := (BitVec.ofBoolListLE (List.ofFn f)).toNat

theorem pack8_bit (f : Fin 8 → Bool) (i : Nat) :
    (pack8 f).testBit i = (List.ofFn f).getD i false := by
  exact BitVec.getLsbD_ofBoolListLE

private theorem pack8_value (f : Fin 8 → Bool) (i : Nat) :
    (pack8 f).testBit i = (if h : i < 8 then f ⟨i, h⟩ else false) := by
  by_cases hi : i < 8
  · simp only [pack8_bit, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi,
      Option.getD_some]
  · simp only [pack8_bit, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi,
      Option.getD_none]

theorem pack8_and (f g : Fin 8 → Bool) :
    pack8 (fun r => f r && g r) = pack8 f &&& pack8 g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 8
  · simp only [pack8_value, dite_eq_left hi]
  · simp only [pack8_value, dite_eq_right hi, Bool.false_and]

theorem pack8_or (f g : Fin 8 → Bool) :
    pack8 (fun r => f r || g r) = pack8 f ||| pack8 g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 8
  · simp only [pack8_value, dite_eq_left hi]
  · simp only [pack8_value, dite_eq_right hi, Bool.false_or]

private def cheapColumns : List Nat :=
  [0x00, 0xFF, 0xAA, 0xCC, 0xF0, 0x88, 0xA0, 0xC0, 0xEE, 0xFA, 0xFC,
   0x80, 0xFE, 0xEA, 0xEC, 0xF8, 0xA8, 0xC8, 0xE0]

def weight (x : Nat) : Nat :=
  if x ∈ cheapColumns then
    if x ∈ [0x00, 0xFF] then 0 else
    if x ∈ [0xAA, 0xCC, 0xF0] then 1 else
    if x ∈ [0x88, 0xA0, 0xC0, 0xEE, 0xFA, 0xFC] then 2 else 3
  else 5

theorem weight_bound (x : Nat) : weight x ≤ 5 := by
  unfold weight
  split
  · split
    · decide
    · split
      · decide
      · split <;> decide
  · decide

private def tested (op : Nat → Nat → Nat) : Bool :=
  cheapColumns.all fun x => cheapColumns.all fun y =>
    decide (weight (op x y) ≤ weight x + weight y)

set_option maxHeartbeats 2000000 in
private theorem and_table : tested (fun x y => x &&& y) = true := by decide

set_option maxHeartbeats 2000000 in
private theorem or_table : tested (fun x y => x ||| y) = true := by decide

private theorem lift_table (op : Nat → Nat → Nat) (ok : tested op = true) (x y : Nat) :
    weight (op x y) ≤ weight x + weight y := by
  have hb := weight_bound (op x y)
  by_cases hx : x ∈ cheapColumns
  · by_cases hy : y ∈ cheapColumns
    · unfold tested at ok
      have row := List.all_eq_true.mp ok x hx
      exact of_decide_eq_true (List.all_eq_true.mp row y hy)
    · have h5 : weight y = 5 := by simp only [weight, ite_eq_right hy]
      omega
  · have h5 : weight x = 5 := by simp only [weight, ite_eq_right hx]
    omega

theorem weight_and (x y : Nat) : weight (x &&& y) ≤ weight x + weight y :=
  lift_table _ and_table x y

theorem weight_or (x y : Nat) : weight (x ||| y) ≤ weight x + weight y :=
  lift_table _ or_table x y

theorem weight_target : weight 0xE8 = 5 := by decide

def seedColumns : List Nat :=
  [0xFF, 0xFF, 0xFF, 0x00, 0xF0, 0xAA, 0xCC, 0xF0, 0x00, 0xFF, 0xFF]

theorem raw_budget : (seedColumns.map weight).sum = 4 := by decide

theorem gate_budget {α : Type} (gates : List α) (out : α → Nat) (ins : α → List Nat)
    (w : Nat → Nat)
    (localBound : ∀ g ∈ gates, w (out g) ≤ ((ins g).map w).sum) :
    ((gates.map out).map w).sum ≤ ((gates.flatMap ins).map w).sum := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    have hfirst := localBound g (by simp)
    have hrest := ih (fun k hk => localBound k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append_nat]
    omega

theorem wire_budget {α : Type} (gates : List α) (out : α → Nat) (ins : α → List Nat)
    (w : Nat → Nat) (sources middles : List Nat) (last : Nat)
    (outputs : gates.map out = middles ++ [last])
    (reads : (gates.flatMap ins).Perm (sources ++ middles))
    (localBound : ∀ g ∈ gates, w (out g) ≤ ((ins g).map w).sum) :
    w last ≤ (sources.map w).sum := by
  have ht := gate_budget gates out ins w localBound
  have hperm := (reads.map w).sum_nat
  rw [outputs, hperm] at ht
  simp only [List.map_append, List.sum_append_nat, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero] at ht
  omega


open PEqualNP.CircuitLowerBounds

def pmSensitivity (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
  (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def sensStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def sensStart (x : Fin 9 → Bool) : List Bool :=
  sensStep (sensStep (List.ofFn x) ⟨.or, [0, 1]⟩) ⟨.and, [2, 9]⟩

def sensRow (i : Fin 9) (b : Bool) (j : Fin 9) : Bool :=
  if i = j then b else
    Nat.testBit (([274, 265, 136, 258, 257, 129, 34, 33, 17] : List Nat).getD i.val 0) j.val

set_option maxRecDepth 4096 in
theorem sensCert : ∀ i : Fin 9,
    pmSensitivity (sensRow i false) ≠ pmSensitivity (sensRow i true) ∧
    ∀ k : Fin 11, k.val ≠ i.val →
      (sensStart (sensRow i false)).getD k.val false =
      (sensStart (sensRow i true)).getD k.val false := by
  decide +kernel

theorem sensAppend (i : Nat) (w v : List Bool) (b : Bool)
    (hlen : w.length = v.length)
    (agree : ∀ k, k ≠ i → w.getD k false = v.getD k false) :
    ∀ k, k ≠ i → (w ++ [b]).getD k false = (v ++ [b]).getD k false := by
  intro k hk
  by_cases h : k < w.length
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen, ite_eq_left h]
      using (agree k hk)
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen, ite_eq_right h]

theorem sensFold (gs : List Gate) (i : Nat) (w v : List Bool)
    (unused : i ∉ gs.flatMap Gate.inputs) (hlen : w.length = v.length)
    (agree : ∀ k, k ≠ i → w.getD k false = v.getD k false) :
    ∀ k, k ≠ i → (gs.foldl sensStep w).getD k false =
                   (gs.foldl sensStep v).getD k false := by
  induction gs generalizing w v with
  | nil => exact agree
  | cons g gs ih =>
    have parts : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by
      simpa only [List.flatMap_cons, List.mem_append, not_or] using unused
    have inputsEq : (g.inputs.map fun k => w.getD k false) =
                    (g.inputs.map fun k => v.getD k false) := by
      apply List.map_congr_left
      intro k hk
      apply agree k
      intro hki
      exact parts.1 (hki ▸ hk)
    have outputEq := congrArg g.op.eval inputsEq
    apply ih (w := sensStep w g) (v := sensStep v g) parts.2
    · simp [sensStep, hlen]
    · unfold sensStep
      rw [outputEq]
      exact sensAppend i w v _ hlen agree

theorem suffixReadsInputs (C : Circuit) (tail : List Gate)
    (hg : C.gates = ⟨.or, [0, 1]⟩ :: ⟨.and, [2, 9]⟩ :: tail)
    (hout : C.output + 1 = 9 + C.size)
    (hcalc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmSensitivity x)
    (i : Fin 9) : i.val ∈ tail.flatMap Gate.inputs := by
  apply Decidable.byContradiction
  intro unused
  have cert := sensCert i
  have startLen (x : Fin 9 → Bool) : (sensStart x).length = 11 := by
    simp [sensStart, sensStep]
  have base : ∀ k, k ≠ i.val →
      (sensStart (sensRow i false)).getD k false =
      (sensStart (sensRow i true)).getD k false := by
    intro k hk
    by_cases small : k < 11
    · exact cert.2 ⟨k, small⟩ hk
    · have hfalse : (sensStart (sensRow i false)).length ≤ k := by rw [startLen]; omega
      have htrue : (sensStart (sensRow i true)).length ≤ k := by rw [startLen]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hfalse,
        List.getElem?_eq_none htrue]
  have stable := sensFold tail i.val _ _ unused ((startLen _).trans (startLen _).symm) base
  have hne : C.output ≠ i.val := by
    have hi := i.isLt
    simp only [Circuit.size, hg, List.length_cons] at hout
    omega
  have heval (x : Fin 9 → Bool) : C.eval (List.ofFn x) =
      (tail.foldl sensStep (sensStart x)).getD C.output false := by
    change (C.gates.foldl sensStep (List.ofFn x)).getD C.output false = _
    simp only [hg, List.foldl_cons, sensStart]
  apply cert.1
  calc
    pmSensitivity (sensRow i false) = C.eval (List.ofFn (sensRow i false)) := (hcalc _).symm
    _ = (tail.foldl sensStep (sensStart (sensRow i false))).getD C.output false := heval _
    _ = (tail.foldl sensStep (sensStart (sensRow i true))).getD C.output false := stable _ hne
    _ = C.eval (List.ofFn (sensRow i true)) := (heval _).symm
    _ = pmSensitivity (sensRow i true) := hcalc _


open PEqualNP.CircuitLowerBounds

def GateSlotForm (bound : Nat) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, a < bound ∧ g.inputs = [a]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, a < b ∧ b < bound ∧ g.inputs = [a, b])

theorem suffix_gateForm (g0 g1 : Gate) (gs : List Gate)
    (hfull : ∀ j : Fin (g0 :: g1 :: gs).length,
      GateSlotForm (9 + j.val) ((g0 :: g1 :: gs).get j)) (j : Fin gs.length) :
    GateSlotForm (11 + j.val) (gs.get j) := by
  have h := hfull j.succ.succ
  change GateSlotForm (9 + (j.val + 1 + 1)) (gs.get j) at h
  have heq : 9 + (j.val + 1 + 1) = 11 + j.val := by omega
  rwa [heq] at h

theorem suffix_arity (gs : List Gate)
    (hform : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j)) :
    ∀ g ∈ gs, g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.get_of_mem hg
  rcases hform j with ⟨_, a, _, h⟩ | ⟨_, a, b, _, _, h⟩
  · rw [h]
    exact (by decide : (1 : Nat) ≤ 2)
  · rw [h] <;> exact Nat.le_refl 2

theorem suffix_binary (gs : List Gate)
    (hform : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j))
    (hall : ∀ g ∈ gs, g.inputs.length = 2) (j : Fin gs.length) :
    ((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 11 + j.val ∧ (gs.get j).inputs = [a, b] := by
  rcases hform j with ⟨_, a, _, h⟩ | h
  · have hlen := hall (gs.get j) (List.get_mem gs j)
    rw [h] at hlen
    change 1 = 2 at hlen
    omega
  · exact h

theorem suffix_live (g0 g1 : Gate) (gs : List Gate)
    (hfull : ∀ j : Fin (g0 :: g1 :: gs).length,
      j.val + 1 < (g0 :: g1 :: gs).length →
      ∃ k : Fin (g0 :: g1 :: gs).length,
        j.val < k.val ∧ 9 + j.val ∈ ((g0 :: g1 :: gs).get k).inputs) :
    ∀ j < gs.length, 10 + j ∈ gs.flatMap Gate.inputs := by
  intro j hj
  have hstart : j + 1 < (g0 :: g1 :: gs).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨⟨k, hk⟩, hlt, hread⟩ := hfull ⟨j + 1, hstart⟩ (by
    change j + 1 + 1 < (g0 :: g1 :: gs).length
    simp only [List.length_cons]
    omega)
  change j + 1 < k at hlt
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ t =>
      simp only [List.length_cons] at hk
      have ht : t < gs.length := by omega
      refine List.mem_flatMap.mpr ⟨gs.get ⟨t, ht⟩, List.get_mem _ _, ?_⟩
      change 9 + (j + 1) ∈ (gs.get ⟨t, ht⟩).inputs at hread
      have heq : 9 + (j + 1) = 10 + j := by omega
      rwa [heq] at hread




open PEqualNP.CircuitLowerBounds

theorem slotLengthBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length ∧
      (2 * gs.length ≤ (gs.flatMap Gate.inputs).length →
        ∀ g ∈ gs, g.inputs.length = 2) := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    have hg : g.inputs.length ≤ 2 := h g (by simp)
    obtain ⟨hbound, hfull⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    constructor
    · omega
    · intro heq z hz
      rcases List.mem_cons.mp hz with he | ht
      · subst z
        omega
      · exact hfull (by omega) z ht

theorem slotPermOfCover (rows slots : List Nat) (hn : rows.Nodup)
    (hsub : rows ⊆ slots) (hlen : slots.length ≤ rows.length) : rows.Perm slots := by
  induction rows generalizing slots with
  | nil =>
    cases slots with
    | nil => exact List.Perm.nil
    | cons x xs => simp at hlen
  | cons a t ih =>
    obtain ⟨hnot, hnt⟩ := List.nodup_cons.mp hn
    have ha : a ∈ slots := hsub List.mem_cons_self
    have hsub' : t ⊆ slots.erase a := by
      intro x hx
      have hxa : x ≠ a := fun e => hnot (e ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub (List.mem_cons_of_mem a hx))
    have hlen' : (slots.erase a).length ≤ t.length := by
      rw [List.length_erase_of_mem ha]
      simp only [List.length_cons] at hlen
      omega
    exact ((ih (slots.erase a) hnt hsub' hlen').cons a).trans (List.perm_cons_erase ha).symm

theorem incidence_saturation (gs : List Gate) (hbudget : gs.length ≤ 9)
    (harity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hraw : ∀ i < 9, i ∈ gs.flatMap Gate.inputs)
    (hlive : ∀ j < gs.length, 10 + j ∈ gs.flatMap Gate.inputs) :
    gs.length = 9 ∧ (∀ g ∈ gs, g.inputs.length = 2) ∧
      (gs.flatMap Gate.inputs).Nodup ∧
      (∀ i ∈ gs.flatMap Gate.inputs, i < 9 ∨ (10 ≤ i ∧ i < 10 + gs.length)) := by
  let slots := gs.flatMap Gate.inputs
  let required := (List.range (10 + gs.length)).erase 9
  have hr : (List.range (10 + gs.length)).Nodup := List.nodup_range
  have hnd : required.Nodup := List.Nodup.erase 9 hr
  have hclass (i : Nat) : i ∈ required ↔ i < 9 ∨ (10 ≤ i ∧ i < 10 + gs.length) := by
    simp only [required, hr.mem_erase_iff, List.mem_range]
    omega
  have hsub : required ⊆ slots := by
    intro i hi
    rcases (hclass i).mp hi with h | ⟨hl, hu⟩
    · exact hraw i h
    · have hw := hlive (i - 10) (by omega)
      have hi' : 10 + (i - 10) = i := by omega
      rwa [hi'] at hw
  have hnine : 9 ∈ List.range (10 + gs.length) := List.mem_range.mpr (by omega)
  have hcard : required.length = 9 + gs.length := by
    rw [show required = (List.range (10 + gs.length)).erase 9 from rfl,
      List.length_erase_of_mem hnine, List.length_range]
    omega
  have hlo := hnd.length_le_of_subset hsub
  obtain ⟨hupper, hfull⟩ := slotLengthBound gs harity
  change slots.length ≤ 2 * gs.length at hupper
  have hs : gs.length = 9 := by omega
  have hp := slotPermOfCover required slots hnd hsub (by omega)
  refine ⟨hs, hfull ?_, hp.nodup hnd, ?_⟩
  · change 2 * gs.length ≤ slots.length
    omega
  · intro i hi
    exact (hclass i).mp (hp.symm.subset hi)


open PEqualNP.CircuitLowerBounds

abbrev column := pack8

def assigned (row : Fin 8) (k : Fin 9) : Bool :=
  match k.val with
  | 0 | 1 | 2 => true
  | 4 | 7 => row.val.testBit 2
  | 5 => row.val.testBit 0
  | 6 => row.val.testBit 1
  | _ => false

def wireCol (C : Circuit) (k : Nat) : Nat :=
  column (fun row => (C.wires (List.ofFn (assigned row))).getD k false)

theorem colStepOld (w : List Bool) (g : Gate) (k : Nat) (hk : k < w.length) :
    (sensStep w g).getD k false = w.getD k false := by
  simp only [sensStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem colStepNew (w : List Bool) (g : Gate) :
    (sensStep w g).getD w.length false = g.op.eval (g.inputs.map fun k => w.getD k false) := by
  simp [sensStep, List.getD_eq_getElem?_getD]

theorem colStable (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
    (gs.foldl sensStep w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hb : k < (sensStep w g).length := by
      simp only [sensStep, List.length_append, List.length_cons, List.length_nil]
      omega
    exact (ih (w := sensStep w g) hb).trans (colStepOld w g k hk)

theorem colFoldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl sensStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [sensStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem colGateValue (C : Circuit) (j : Fin C.gates.length) (x : Fin 9 → Bool)
    (valid : ∀ k ∈ (C.gates.get j).inputs, k < 9+j.val) :
    (C.wires (List.ofFn x)).getD (9+j.val) false =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k =>
      (C.wires (List.ofFn x)).getD k false) := by
  let g := C.gates.get j
  let pre := C.gates.take j.val
  let post := C.gates.drop (j.val+1)
  let w := pre.foldl sensStep (List.ofFn x)
  have hsplit : C.gates = pre ++ g :: post := by
    dsimp only [pre, g, post]
    rw [List.get_eq_getElem, ← List.drop_eq_getElem_cons j.isLt, List.take_append_drop]
  have len : w.length = 9+j.val := by
    simp only [w, pre, colFoldLength, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt j.isLt)]
  have after : C.wires (List.ofFn x) = post.foldl sensStep (sensStep w g) := by
    change C.gates.foldl sensStep (List.ofFn x) = _
    have eqFold := congrArg (fun gs : List Gate => gs.foldl sensStep (List.ofFn x)) hsplit
    simpa only [List.foldl_append, List.foldl_cons, w] using eqFold
  have old (k : Nat) (hk : k < 9+j.val) :
      (C.wires (List.ofFn x)).getD k false = w.getD k false := by
    have hkw : k < w.length := by omega
    have hkn : k < (sensStep w g).length := by
      simp only [sensStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [after]
    exact (colStable post _ k hkn).trans (colStepOld w g k hkw)
  have fresh : (C.wires (List.ofFn x)).getD (9+j.val) false =
      g.op.eval (g.inputs.map fun k => w.getD k false) := by
    rw [after, ← len]
    apply (colStable post _ _ ?_).trans (colStepNew w g)
    simp [sensStep]
  rw [fresh]
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro k hk
  exact (old k (valid k hk)).symm

theorem colInputsValid (C : Circuit) (j : Fin C.gates.length) (a b : Nat)
    (hins : (C.gates.get j).inputs = [a,b]) (ha : a < 9+j.val) (hb : b < 9+j.val) :
    ∀ k ∈ (C.gates.get j).inputs, k < 9+j.val := by
  intro k hk
  simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> assumption

theorem wireCol_gate_and (C : Circuit) (j : Fin C.gates.length) (a b : Nat)
    (hop : (C.gates.get j).op = .and) (hins : (C.gates.get j).inputs = [a,b])
    (ha : a < 9+j.val) (hb : b < 9+j.val) :
    wireCol C (9+j.val) = (wireCol C a &&& wireCol C b) := by
  unfold wireCol
  rw [← pack8_and]
  apply congrArg column
  funext row
  rw [colGateValue C j (assigned row) (colInputsValid C j a b hins ha hb)]
  rw [hop, hins] <;> simp [GateOp.eval]

theorem wireCol_gate_or (C : Circuit) (j : Fin C.gates.length) (a b : Nat)
    (hop : (C.gates.get j).op = .or) (hins : (C.gates.get j).inputs = [a,b])
    (ha : a < 9+j.val) (hb : b < 9+j.val) :
    wireCol C (9+j.val) = (wireCol C a ||| wireCol C b) := by
  unfold wireCol
  rw [← pack8_or]
  apply congrArg column
  funext row
  rw [colGateValue C j (assigned row) (colInputsValid C j a b hins ha hb)]
  rw [hop, hins] <;> simp [GateOp.eval]

theorem colSeedTable : ∀ k : Fin 11,
    column (fun row => (sensStart (assigned row)).getD k.val false) = seedColumns.getD k.val 0 := by
  decide +kernel

theorem wireCol_seed (C : Circuit) (tail : List Gate)
    (hg : C.gates = ⟨.or,[0,1]⟩ :: ⟨.and,[2,9]⟩ :: tail) (k : Fin 11) :
    wireCol C k.val = seedColumns.getD k.val 0 := by
  rw [← colSeedTable k]
  unfold wireCol
  apply congrArg column
  funext row
  change (C.gates.foldl sensStep (List.ofFn (assigned row))).getD k.val false = _
  rw [hg]
  apply colStable tail (sensStart (assigned row)) k.val
  simp [sensStart, sensStep]

theorem wireCol_target (C : Circuit)
    (hcalc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmSensitivity x) :
    wireCol C C.output = 0xE8 := by
  have eqRows : (fun row => (C.wires (List.ofFn (assigned row))).getD C.output false) =
                (fun row => pmSensitivity (assigned row)) := by
    funext row
    exact hcalc (assigned row)
  unfold wireCol
  rw [eqRows]
  decide +kernel

theorem suffixImpossible (C : Circuit) (gs : List Gate)
    (hg : C.gates = ⟨.or, [0, 1]⟩ :: ⟨.and, [2, 9]⟩ :: gs)
    (hsize : C.size ≤ 11)
    (hcalc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmSensitivity x)
    (hout : C.output + 1 = 9 + C.size)
    (hform : ∀ j : Fin C.gates.length, GateSlotForm (9 + j.val) (C.gates.get j))
    (huse : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) :
    False := by
  have hbudget : gs.length ≤ 9 := by
    simp only [Circuit.size, hg, List.length_cons] at hsize
    omega
  rw [hg] at hform huse
  have form := suffix_gateForm _ _ gs hform
  have live := suffix_live _ _ gs huse
  have raw (i : Nat) (hi : i < 9) := suffixReadsInputs C gs hg hout hcalc ⟨i, hi⟩
  obtain ⟨hlen, hbinary, hnodup, hclass⟩ :=
    incidence_saturation gs hbudget (suffix_arity gs form) raw live
  have hfinal : C.output = 19 := by
    simp only [Circuit.size, hg, List.length_cons, hlen] at hout
    omega
  let idxs := List.finRange 9
  let gateAt (j : Fin 9) := gs.get ⟨j.val, by rw [hlen]; exact j.isLt⟩
  have gateList : idxs.map gateAt = gs := by
    apply List.ext_getElem
    · simp [idxs, hlen]
    · intro i h1 h2
      simp [idxs, gateAt, List.get_eq_getElem]
  let src : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]
  let mid : List Nat := [11, 12, 13, 14, 15, 16, 17, 18]
  let w (i : Nat) := weight (wireCol C i)
  have targetMem (i : Nat) : i ∈ src ++ mid ↔ i < 9 ∨ (10 ≤ i ∧ i < 19) := by
    simp only [src, mid, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hflat : idxs.flatMap (fun j => (gateAt j).inputs) = gs.flatMap Gate.inputs := by
    calc
      _ = (idxs.map gateAt).flatMap Gate.inputs := by simp [List.flatMap_map]
      _ = _ := congrArg (List.flatMap Gate.inputs) gateList
  have perm : (idxs.flatMap fun j => (gateAt j).inputs).Perm (src ++ mid) := by
    rw [hflat]
    apply (List.perm_ext_iff_of_nodup hnodup (by decide : (src ++ mid).Nodup)).mpr
    intro i
    rw [targetMem]
    constructor
    · simpa only [hlen] using hclass i
    · rintro (lo | ⟨low, high⟩)
      · exact raw i lo
      · have hu : i - 10 < gs.length := by omega
        have hr := live (i - 10) hu
        rwa [show 10 + (i - 10) = i by omega] at hr
  have liftGate : ∀ j : Fin gs.length, ∃ k : Fin C.gates.length,
      k.val = j.val + 2 ∧ C.gates.get k = gs.get j := by
    rw [hg]
    intro j
    exact ⟨j.succ.succ, rfl, rfl⟩
  have bound (j : Fin 9) (_ : j ∈ idxs) :
      w (11 + j.val) ≤ (((gateAt j).inputs).map w).sum := by
    let i : Fin gs.length := ⟨j.val, by rw [hlen]; exact j.isLt⟩
    obtain ⟨k, hk, heq⟩ := liftGate i
    obtain ⟨hop, a, b, hab, hb, hin⟩ := suffix_binary gs form hbinary i
    have hid : 9 + k.val = 11 + j.val := by change k.val = j.val + 2 at hk; omega
    have ha' : a < 9 + k.val := by rw [hid]; change b < 11 + j.val at hb; omega
    have hb' : b < 9 + k.val := by rw [hid]; exact hb
    have hinputs : (C.gates.get k).inputs = [a,b] := by rw [heq]; exact hin
    change weight (wireCol C (11 + j.val)) ≤ (((gs.get i).inputs).map w).sum
    rw [hin]
    change weight (wireCol C (11 + j.val)) ≤ weight (wireCol C a) + (weight (wireCol C b) + 0)
    rw [Nat.add_zero, ← hid]
    rcases hop with hand | hor
    · rw [wireCol_gate_and C k a b (by rw [heq]; exact hand) hinputs ha' hb']
      exact weight_and _ _
    · rw [wireCol_gate_or C k a b (by rw [heq]; exact hor) hinputs ha' hb']
      exact weight_or _ _
  have houtputs : idxs.map (fun j => 11 + j.val) = mid ++ [19] := by decide
  have finalBound := wire_budget idxs (fun j => 11 + j.val) (fun j => (gateAt j).inputs)
    w src mid 19 houtputs perm bound
  have srcCols : src.map (wireCol C) = src.map (fun k => seedColumns.getD k 0) := by
    apply List.map_congr_left
    intro k hk
    have hk' : k < 11 := by
      simp only [src, List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact wireCol_seed C gs hg ⟨k, hk'⟩
  have seeds : (src.map w).sum = 4 := by
    calc
      _ = ((src.map (wireCol C)).map weight).sum := by simp [w, List.map_map, Function.comp_def]
      _ = _ := by rw [srcCols]; decide
  have finalWt : w 19 = 5 := by
    change weight (wireCol C 19) = 5
    rw [← hfinal, wireCol_target C hcalc, weight_target]
  omega

end PEqualNP.Outside.L_meta_27527

theorem PEqualNP.Outside.L_meta_27527 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩)) := by
  intro witness
  obtain ⟨C, _, hsize, hcalc, hout, hform, _, huse, hfirst, hsecond⟩ := witness
  obtain ⟨gs, hg⟩ : ∃ gs, C.gates =
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ::
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩ :: gs := by
    cases ht : C.gates with
    | nil => simp [ht] at hfirst
    | cons g0 remain =>
      cases remain with
      | nil => simp [ht] at hsecond
      | cons g1 gs =>
        have h0 : g0 = _ := Option.some.inj (by simpa only [ht, List.head?_cons] using hfirst)
        have h1 : g1 = _ := Option.some.inj (by simpa only [ht, List.tail_cons, List.head?_cons] using hsecond)
        exact ⟨gs, by rw [h0, h1]⟩
  exact PEqualNP.Outside.L_meta_27527.suffixImpossible C gs hg hsize hcalc hout hform huse
