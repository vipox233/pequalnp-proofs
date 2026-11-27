import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27577_aux.Support

open PEqualNP.CircuitLowerBounds

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def witnessMask : Fin 9 → ℕ := ![273, 266, 140, 266, 273, 161, 98, 161, 273]

theorem essential (i : Fin 9) : ∃ x y : Fin 9 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ target x = true ∧ target y = false := by
  let x (j : Fin 9) := (witnessMask i).testBit j.val
  let y (j : Fin 9) := if j = i then false else x j
  refine ⟨x, y, fun j h => (ite_eq_right h).symm, ?_, ?_⟩ <;>
    fin_cases i <;> decide +kernel

private def agreeOutside (hole : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j, j ≠ hole → a.getD j false = b.getD j false

private theorem agree_append {hole : ℕ} {a b : List Bool} (same : agreeOutside hole a b) (bit : Bool) :
    agreeOutside hole (a ++ [bit]) (b ++ [bit]) := by
  obtain ⟨lengths, values⟩ := same
  refine ⟨by simp [lengths], fun j hj => ?_⟩
  by_cases left : j < a.length
  · have right : j < b.length := lengths ▸ left
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left left,
      List.getElem?_append_left right] using values j hj
  · have right : b.length ≤ j := lengths ▸ Nat.le_of_not_gt left
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt left),
      List.getElem?_append_right right, lengths]

private def tick (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem ignore_fold (hole : ℕ) (gates : List Gate)
    (avoids : ∀ g ∈ gates, hole ∉ g.inputs) {a b : List Bool} (same : agreeOutside hole a b) :
    agreeOutside hole (gates.foldl tick a) (gates.foldl tick b) := by
  induction gates generalizing a b with
  | nil => exact same
  | cons g tail ih =>
    have reads : (g.inputs.map fun i => a.getD i false) = (g.inputs.map fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i member
      exact same.2 i (fun eq => avoids g (by simp) (eq ▸ member))
    change agreeOutside hole (tail.foldl tick (tick a g)) (tail.foldl tick (tick b g))
    apply ih (fun h member => avoids h (List.mem_cons_of_mem _ member))
    unfold tick
    rw [reads]
    exact agree_append same _

private theorem agree_inputs {i : Fin 9} {x y : Fin 9 → Bool} (same : ∀ j, j ≠ i → x j = y j) :
    agreeOutside i.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun j hj => ?_⟩
  by_cases in_bounds : j < 9
  · have different : (⟨j, in_bounds⟩ : Fin 9) ≠ i := fun eq => hj (congrArg Fin.val eq)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left in_bounds, Option.getD_some]
    exact same ⟨j, in_bounds⟩ different
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right in_bounds]

theorem input_is_read (C : Circuit) (comp : ∀ row : Fin 9 → Bool, C.eval (List.ofFn row) = target row)
    (output_gate : 9 ≤ C.output) (i : Fin 9) : i.val ∈ C.gates.flatMap Gate.inputs := by
  by_contra absent
  have avoids (g : Gate) (member : g ∈ C.gates) : i.val ∉ g.inputs :=
    fun has => absent (List.mem_flatMap_of_mem member has)
  obtain ⟨x, y, agree, yes, no⟩ := essential i
  have same := ignore_fold i.val C.gates avoids (agree_inputs agree)
  have equal : C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
    same.2 C.output (by have := i.isLt; omega)
  rw [comp x, comp y, yes, no] at equal
  contradiction

def binary (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

end PEqualNP.Outside.L_meta_27577_aux.Support

namespace PEqualNP.Outside.L_meta_27577_aux

open PEqualNP.Outside.L_meta_27577_aux.Support (target)

abbrev Row := Fin 9 → Bool
abbrev Restriction := Fin 3

def bothTrue : Restriction := 0
def clearFive : Restriction := 1
def clearEight : Restriction := 2

def fixed (c : Restriction) (i : Fin 9) : Option Bool :=
  if i = 0 ∨ i = 1 then some true
  else if (c = clearFive ∧ i = 5) ∨ (c = clearEight ∧ i = 8) then some false
  else none

def Fits (c : Restriction) (x : Row) : Prop :=
  ∀ (i : Fin 9) (v : Bool), fixed c i = some v → x i = v

instance (c : Restriction) (x : Row) : Decidable (Fits c x) := by
  unfold Fits
  infer_instance

def Sensitive (c : Restriction) (i j : Fin 9) (bit : Bool) : Prop :=
  ∃ x y : Row, Fits c x ∧ Fits c y ∧ (∀ k, k ≠ i → x k = y k) ∧ x j = bit ∧ y j = bit ∧ target x ≠ target y

private def witness_masks (c : Restriction) : List Nat :=

  if c = bothTrue then [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 87, 0, 87, 0, 87, 87, 95, 143, 87, 87, 0, 143, 87, 87, 143, 87, 0,
    0, 143, 0, 143, 267, 143, 0, 143, 143, 159, 143, 299, 143, 207, 267, 143, 143, 267,
    0, 87, 0, 87, 275, 87, 87, 95, 0, 87, 87, 307, 275, 87, 87, 215, 87, 275,
    0, 99, 0, 99, 99, 103, 99, 107, 99, 115, 0, 99, 163, 99, 99, 163, 99, 355,
    0, 87, 0, 87, 99, 87, 87, 95, 99, 87, 87, 99, 0, 87, 87, 215, 87, 355,
    0, 143, 0, 143, 163, 143, 163, 143, 143, 159, 143, 163, 143, 207, 0, 143, 143, 419,
    0, 267, 0, 267, 267, 271, 275, 267, 267, 275, 267, 299, 267, 331, 267, 395, 0, 267]
  else if c = clearFive then [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 87, 0, 87, 0, 87, 87, 95, 143, 87, 87, 0, 143, 87, 87, 143, 87, 0,
    0, 143, 0, 143, 267, 143, 0, 143, 143, 159, 143, 0, 143, 207, 267, 143, 143, 267,
    0, 87, 0, 87, 275, 87, 87, 95, 0, 87, 87, 0, 275, 87, 87, 215, 87, 275,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 87, 0, 87, 0, 87, 87, 95, 0, 87, 87, 0, 0, 87, 87, 215, 87, 0,
    0, 143, 0, 143, 0, 143, 0, 143, 143, 159, 143, 0, 143, 207, 0, 143, 143, 0,
    0, 267, 0, 267, 267, 271, 275, 267, 267, 275, 267, 0, 267, 331, 267, 395, 0, 267]
  else [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 87, 0, 87, 0, 87, 87, 95, 143, 87, 87, 0, 143, 87, 87, 143, 87, 0,
    0, 143, 0, 143, 0, 143, 0, 143, 143, 159, 143, 0, 143, 207, 0, 143, 143, 0,
    0, 87, 0, 87, 0, 87, 87, 95, 0, 87, 87, 0, 0, 87, 87, 215, 87, 0,
    0, 99, 0, 99, 99, 103, 99, 107, 99, 115, 0, 99, 163, 99, 99, 163, 99, 0,
    0, 87, 0, 87, 99, 87, 87, 95, 99, 87, 87, 99, 0, 87, 87, 215, 87, 0,
    0, 143, 0, 143, 163, 143, 163, 143, 143, 159, 143, 163, 143, 207, 0, 143, 143, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def witness (c : Restriction) (i j : Fin 9) (bit : Bool) : Row :=
  fun k => ((witness_masks c).getD (18 * i.val + 2 * j.val + bit.toNat) 0).testBit k.val

private def clear (x : Row) (i : Fin 9) : Row := fun k => if k = i then false else x k

private def ValidWitness (c : Restriction) (i j : Fin 9) (bit : Bool) : Prop :=
  let x := witness c i j bit
  let y := clear x i
  Fits c x ∧ Fits c y ∧ x j = bit ∧ y j = bit ∧ target x ≠ target y

private instance (c : Restriction) (i j : Fin 9) (bit : Bool) : Decidable (ValidWitness c i j bit) := by
  unfold ValidWitness
  infer_instance

private theorem sensitive_of_witness {c : Restriction} {i j : Fin 9} {bit : Bool}
    (h : ValidWitness c i j bit) : Sensitive c i j bit := by
  rcases h with ⟨hx, hy, atx, aty, differs⟩
  exact ⟨witness c i j bit, clear (witness c i j bit) i, hx, hy,
    fun k hk => (ite_eq_right hk).symm, atx, aty, differs⟩

private theorem both_true_table : ∀ (i j : Fin 9) (bit : Bool), i ≠ j →
    fixed bothTrue i = none → fixed bothTrue j = none →
    ¬ (i = 2 ∧ (j = 5 ∨ j = 8) ∧ bit = true) → ValidWitness bothTrue i j bit := by
  decide +kernel

theorem both_true_sensitive {i j : Fin 9} {bit : Bool} (distinct : i ≠ j)
    (fi : fixed bothTrue i = none) (fj : fixed bothTrue j = none)
    (not_exception : ¬ (i = 2 ∧ (j = 5 ∨ j = 8) ∧ bit = true)) : Sensitive bothTrue i j bit :=
  sensitive_of_witness (both_true_table i j bit distinct fi fj not_exception)

private theorem reduced_pair_table : ∀ (c : Restriction) (i j : Fin 9) (bi bj : Bool),
    c ≠ bothTrue → i ≠ j → fixed c i = none → fixed c j = none →
    ValidWitness c i j bj ∨ ValidWitness c j i bi := by
  decide +kernel

theorem reduced_pair_sensitive {c : Restriction} {i j : Fin 9} {bi bj : Bool}
    (reduced : c ≠ bothTrue) (distinct : i ≠ j) (fi : fixed c i = none) (fj : fixed c j = none) :
    Sensitive c i j bj ∨ Sensitive c j i bi :=
  (reduced_pair_table c i j bi bj reduced distinct fi fj).imp sensitive_of_witness sensitive_of_witness

private theorem two_inputs_table : ∀ c : Restriction, ValidWitness c 3 4 false ∧ ValidWitness c 4 3 false := by
  decide +kernel

theorem two_inputs_sensitive (c : Restriction) : Sensitive c 3 4 false ∧ Sensitive c 4 3 false :=
  (two_inputs_table c).imp sensitive_of_witness sensitive_of_witness

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_27577_aux.Support (binary)

def Shape (C : Circuit) : Prop := ∀ j : Fin C.gates.length,
  ((C.gates.get j).op = .not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
  (((C.gates.get j).op = .and ∨ (C.gates.get j).op = .or) ∧
    ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])

def Live (C : Circuit) : Prop := ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
  ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs

def firstGate : Gate := ⟨.or, [0, 1]⟩
def secondGate : Gate := ⟨.and, [0, 1]⟩

theorem opening {C : Circuit} (first : C.gates.head? = some firstGate)
    (second : C.gates.tail.head? = some secondGate) : ∃ suffix, C.gates = firstGate :: secondGate :: suffix := by
  cases C with
  | mk gates output =>
    cases gates with
    | nil => simp at first
    | cons g gs =>
      have h : g = firstGate := Option.some.inj first
      subst g
      cases gs with
      | nil => simp at second
      | cons g gs =>
        have h : g = secondGate := Option.some.inj second
        exact ⟨gs, by rw [h]⟩

theorem reads_backward {C : Circuit} (shape : Shape C) (j : Fin C.gates.length)
    {w : ℕ} (read : w ∈ (C.gates.get j).inputs) : w < 9 + j.val := by
  rcases shape j with ⟨_, a, ah, inputs⟩ | ⟨_, a, b, ab, bh, inputs⟩
  · rw [inputs] at read
    simp only [List.mem_singleton] at read
    rwa [read]
  · rw [inputs] at read
    simp only [List.mem_cons, List.not_mem_nil, or_false] at read
    rcases read with rfl | rfl <;> omega

def signal (C : Circuit) (w : ℕ) (x : Row) : Bool := (C.wires (List.ofFn x)).getD w false

def evalGate (g : Gate) (v : ℕ → Bool) : Bool := g.op.eval (g.inputs.map v)

def tick (w : List Bool) (g : Gate) : List Bool := w ++ [evalGate g (fun i => w.getD i false)]

theorem gate_congr (g : Gate) {x y : ℕ → Bool} (same : ∀ w ∈ g.inputs, x w = y w) :
    evalGate g x = evalGate g y := by
  exact congrArg g.op.eval (List.map_congr_left same)

@[simp] theorem tick_length (w : List Bool) (g : Gate) : (tick w g).length = w.length + 1 := by simp [tick]

theorem tick_prefix (w : List Bool) (g : Gate) {n : ℕ} (hn : n < w.length) :
    (tick w g).getD n false = w.getD n false := by
  simp only [tick, List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

theorem tick_last (w : List Bool) (g : Gate) :
    (tick w g).getD w.length false = evalGate g (fun i => w.getD i false) := by
  simp [tick, List.getD_eq_getElem?_getD]

theorem fold_prefix (gates : List Gate) (w : List Bool) {n : ℕ} (hn : n < w.length) :
    (gates.foldl tick w).getD n false = w.getD n false := by
  induction gates generalizing w with
  | nil => rfl
  | cons g rest ih =>
    change (rest.foldl tick (tick w g)).getD n false = w.getD n false
    rw [ih (tick w g) (by simp; omega), tick_prefix w g hn]

private theorem fold_gate (gates : List Gate) (w : List Bool) (j : Fin gates.length)
    (back : ∀ i ∈ (gates.get j).inputs, i < w.length + j.val) :
    (gates.foldl tick w).getD (w.length + j.val) false =
      evalGate (gates.get j) (fun i => (gates.foldl tick w).getD i false) := by
  induction gates generalizing w with
  | nil => exact Fin.elim0 j
  | cons g rest ih =>
    cases j using Fin.cases with
    | zero =>
      have lower : ∀ i ∈ g.inputs, i < w.length := by simpa using back
      change (rest.foldl tick (tick w g)).getD (w.length + 0) false =
        evalGate g (fun i => (rest.foldl tick (tick w g)).getD i false)
      rw [Nat.add_zero, fold_prefix rest (tick w g) (by simp), tick_last]
      apply gate_congr
      intro i hi
      rw [fold_prefix rest (tick w g) (by simp; have := lower i hi; omega), tick_prefix w g (lower i hi)]
    | succ j =>
      have lower : ∀ i ∈ (rest.get j).inputs, i < (tick w g).length + j.val := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using back
      simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (tick w g) j lower

theorem input_signal (C : Circuit) (i : Fin 9) (x : Row) : signal C i.val x = x i := by
  change (C.gates.foldl tick (List.ofFn x)).getD i.val false = x i
  rw [fold_prefix C.gates (List.ofFn x) (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

theorem gate_signal (C : Circuit) (shape : Shape C) (j : Fin C.gates.length) (x : Row) :
    signal C (9 + j.val) x = evalGate (C.gates.get j) (fun w => signal C w x) := by
  have back : ∀ i ∈ (C.gates.get j).inputs, i < (List.ofFn x).length + j.val := by
    intro i hi
    simpa only [List.length_ofFn] using reads_backward shape j hi
  change (C.gates.foldl tick (List.ofFn x)).getD (9 + j.val) false =
    evalGate (C.gates.get j) (fun w => (C.gates.foldl tick (List.ofFn x)).getD w false)
  simpa only [List.length_ofFn] using fold_gate C.gates (List.ofFn x) j back

theorem arity_budget (C : Circuit) (shape : Shape C) :
    (C.gates.flatMap Gate.inputs).length = C.gates.length + C.gates.countP binary := by
  have each (g : Gate) (mem : g ∈ C.gates) : g.inputs.length = if binary g then 2 else 1 := by
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp mem
    rcases shape j with ⟨op, a, _, inputs⟩ | ⟨op, a, b, _, _, inputs⟩
    · unfold binary
      rw [inputs, op]
      rfl
    · rcases op with h | h <;> (unfold binary; rw [inputs, h]; rfl)
  generalize eq : C.gates = gates at each ⊢
  clear eq shape C
  induction gates with
  | nil => rfl
  | cons g tail ih =>
    have tailArity := fun h m => each h (List.mem_cons_of_mem g m)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.countP_cons, ih tailArity, each g (by simp)]
    split <;> omega

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_27577_aux.Support (binary input_is_read target)

private def SameExceptOpening (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, w ≠ 0 → w ≠ 1 → x.getD w false = y.getD w false

private theorem tick_same {x y : List Bool} (agree : SameExceptOpening x y) (g : Gate)
    (zero : 0 ∉ g.inputs) (one : 1 ∉ g.inputs) : SameExceptOpening (tick x g) (tick y g) := by
  rcases agree with ⟨len, agree⟩
  have gate_eq := gate_congr g fun i mem => agree i (fun eq => zero (eq ▸ mem)) (fun eq => one (eq ▸ mem))
  change SameExceptOpening (x ++ [evalGate g (fun i => x.getD i false)])
    (y ++ [evalGate g (fun i => y.getD i false)])
  rw [gate_eq]
  refine ⟨by simp [len], fun j j0 j1 => ?_⟩
  by_cases h : j < x.length
  · have hy : j < y.length := len ▸ h
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getElem?_append_left hy] using agree j j0 j1
  · have hy : y.length ≤ j := len ▸ Nat.le_of_not_gt h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt h),
      List.getElem?_append_right hy, len]

private theorem fold_same (gs : List Gate) (avoid : ∀ g ∈ gs, 0 ∉ g.inputs ∧ 1 ∉ g.inputs)
    {x y : List Bool} (same : SameExceptOpening x y) : SameExceptOpening (gs.foldl tick x) (gs.foldl tick y) := by
  induction gs generalizing x y with
  | nil => exact same
  | cons g rest ih =>
    have head := avoid g (by simp)
    exact ih (fun g hg => avoid g (List.mem_cons_of_mem _ hg)) (tick_same same g head.1 head.2)

private def leftRow : Row := fun i => (273 : ℕ).testBit i.val
private def rightRow : Row := fun i => (274 : ℕ).testBit i.val
private def front (row : Row) : List Bool := tick (tick (List.ofFn row) firstGate) secondGate

private theorem front_agreement : SameExceptOpening (front leftRow) (front rightRow) := by
  have leftSize : (front leftRow).length = 11 := by simp [front]
  have rightSize : (front rightRow).length = 11 := by simp [front]
  refine ⟨leftSize.trans rightSize.symm, fun j h0 h1 => ?_⟩
  by_cases h : j < 11
  · have finite : ∀ n : Fin 11, n.val ≠ 0 → n.val ≠ 1 →
      (front leftRow).getD n.val false = (front rightRow).getD n.val false := by decide +kernel
    exact finite ⟨j, h⟩ h0 h1
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (front leftRow).length ≤ j),
      List.getElem?_eq_none (by omega : (front rightRow).length ≤ j)]

theorem one_input_read_again {C : Circuit} {suffix : List Gate} (opened : C.gates = firstGate :: secondGate :: suffix)
    (output_gate : 9 ≤ C.output) (correct : ∀ x, C.eval (List.ofFn x) = target x) :
    0 ∈ suffix.flatMap Gate.inputs ∨ 1 ∈ suffix.flatMap Gate.inputs := by
  by_contra absent
  have avoid (g : Gate) (member : g ∈ suffix) : 0 ∉ g.inputs ∧ 1 ∉ g.inputs := by
    exact ⟨fun read => absent (Or.inl (List.mem_flatMap_of_mem member read)),
      fun read => absent (Or.inr (List.mem_flatMap_of_mem member read))⟩
  have same := fold_same suffix avoid front_agreement
  have output : C.eval (List.ofFn leftRow) = C.eval (List.ofFn rightRow) := by
    change (C.gates.foldl tick (List.ofFn leftRow)).getD C.output false =
      (C.gates.foldl tick (List.ofFn rightRow)).getD C.output false
    rw [opened]
    exact same.2 C.output (by omega) (by omega)
  have detects : target leftRow ≠ target rightRow := by decide +kernel
  exact detects ((correct leftRow).symm.trans (output.trans (correct rightRow)))

theorem required_suffix_reads {C : Circuit} {suffix : List Gate} (opened : C.gates = firstGate :: secondGate :: suffix)
    (output_gate : 9 ≤ C.output) (correct : ∀ x, C.eval (List.ofFn x) = target x) (live : Live C) :
    C.gates.length + 7 ≤ (suffix.flatMap Gate.inputs).toFinset.card := by
  obtain ⟨t, ht, read⟩ : ∃ t : ℕ, t < 2 ∧ t ∈ suffix.flatMap Gate.inputs := by
    rcases one_input_read_again opened output_gate correct with z | o
    · exact ⟨0, by decide, z⟩
    · exact ⟨1, by decide, o⟩
  let source (i : ℕ) := if i = 0 then t else i + 1
  have distinct : Function.Injective source := by
    intro i j h
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [source, hi, hj] at h ⊢ <;> omega
  have contained : (Finset.range (C.gates.length + 7)).image source ⊆ (suffix.flatMap Gate.inputs).toFinset := by
    intro w hw
    obtain ⟨i, atRange, rfl⟩ := Finset.mem_image.mp hw
    have hi := Finset.mem_range.mp atRange
    apply List.mem_toFinset.mpr
    by_cases zero : i = 0
    · simpa [source, zero] using read
    · have whole : i + 1 ∈ C.gates.flatMap Gate.inputs := by
        by_cases raw : i + 1 < 9
        · exact input_is_read C correct output_gate ⟨i + 1, raw⟩
        · let j : Fin C.gates.length := ⟨i + 1 - 9, by omega⟩
          have beforeLast : j.val + 1 < C.gates.length := by dsimp [j]; omega
          obtain ⟨k, _, used⟩ := live j beforeLast
          have wire : 9 + j.val = i + 1 := by dsimp [j]; omega
          rw [wire] at used
          exact List.mem_flatMap_of_mem (List.get_mem C.gates k) used
      have member : i + 1 ∈ suffix.flatMap Gate.inputs := by
        simpa [opened, firstGate, secondGate, zero] using whole
      simpa [source, zero] using member
  simpa only [Finset.card_image_of_injective _ distinct, Finset.card_range] using Finset.card_le_card contained

theorem unique_repeat {xs : List ℕ} (short : xs.length ≤ xs.toFinset.card + 1)
    {x y : ℕ} (repeatX : 2 ≤ xs.count x) (repeatY : 2 ≤ xs.count y) : x = y := by
  by_contra different
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have hy : y ∈ xs.erase x := List.count_pos_iff.mp (by rw [List.count_erase_of_ne (Ne.symm different)]; omega)
  let rest := (xs.erase x).erase y
  have same : xs.toFinset ⊆ rest.toFinset := by
    intro w hw
    have present : w ∈ xs := List.mem_toFinset.mp hw
    apply List.mem_toFinset.mpr
    rcases eq_or_ne w x with rfl | neX
    · apply List.count_pos_iff.mp
      simp only [rest, List.count_erase_of_ne different, List.count_erase_self]
      omega
    · rcases eq_or_ne w y with rfl | neY
      · apply List.count_pos_iff.mp
        simp only [rest, List.count_erase_self, List.count_erase_of_ne neX]
        omega
      · exact (List.mem_erase_of_ne neY).mpr ((List.mem_erase_of_ne neX).mpr present)
  have lower := (Finset.card_le_card same).trans (List.toFinset_card_le rest)
  have length : rest.length = xs.length - 1 - 1 := by
    dsimp [rest]
    rw [List.length_erase_of_mem hy, List.length_erase_of_mem hx]
  have long : 2 ≤ xs.length := repeatX.trans List.count_le_length
  omega

theorem suffix_repeat_unique {C : Circuit} {suffix : List Gate}
    (opened : C.gates = firstGate :: secondGate :: suffix) (output_gate : 9 ≤ C.output)
    (correct : ∀ row, C.eval (List.ofFn row) = target row) (shape : Shape C) (live : Live C)
    (size : C.gates.length ≤ 12) {i j : ℕ}
    (ri : 2 ≤ (suffix.flatMap Gate.inputs).count i) (rj : 2 ≤ (suffix.flatMap Gate.inputs).count j) : i = j := by
  let reads := suffix.flatMap Gate.inputs
  have distinct := required_suffix_reads opened output_gate correct live
  change C.gates.length + 7 ≤ reads.toFinset.card at distinct
  have readCount := arity_budget C shape
  have binaryUpper := List.countP_le_length (p := binary) (l := C.gates)
  have whole : (C.gates.flatMap Gate.inputs).length = 4 + reads.length := by
    simp [opened, firstGate, secondGate, reads]
    omega
  exact unique_repeat (by omega : reads.length ≤ reads.toFinset.card + 1) ri rj

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_27577_aux.Support (target)

inductive Primitive (c : Restriction) (f : Row → Bool) : Prop where
  | constant (b : Bool) (sound : ∀ x, Fits c x → f x = b)
  | unary (i : Fin 9) (free : fixed c i = none) (u : Bool → Bool) (sound : ∀ x, Fits c x → f x = u (x i))

theorem Primitive.map {c : Restriction} {f g : Row → Bool} (simple : Primitive c f) (h : Bool → Bool)
    (sound : ∀ x, Fits c x → g x = h (f x)) : Primitive c g := by
  cases simple with
  | constant b p => exact .constant (h b) (fun x hx => (sound x hx).trans (congrArg h (p x hx)))
  | unary i free u p => exact .unary i free (h ∘ u) (fun x hx => (sound x hx).trans (congrArg h (p x hx)))

theorem Primitive.eq_of_agrees {c : Restriction} {f : Row → Bool} (simple : Primitive c f)
    {x y : Row} (hx : Fits c x) (hy : Fits c y) (sound : ∀ (i : Fin 9), fixed c i = none → x i = y i) :
    f x = f y := by
  cases simple with
  | constant b p => exact (p x hx).trans (p y hy).symm
  | unary i free u p => exact (p x hx).trans ((congrArg u (sound i free)).trans (p y hy).symm)

theorem target_nonprimitive (c : Restriction) : ¬ Primitive c target := by
  intro simple
  obtain ⟨s3, s4⟩ := two_inputs_sensitive c
  cases simple with
  | constant b sound =>
    obtain ⟨x, y, hx, hy, _, _, _, differs⟩ := s3
    exact differs ((sound x hx).trans (sound y hy).symm)
  | unary ip free u sound =>
    have refute (i j : Fin 9) (bit : Bool) (s : Sensitive c i j bit) (away : ip ≠ i) : False := by
      obtain ⟨x, y, hx, hy, agree, _, _, differs⟩ := s
      exact differs ((sound x hx).trans ((congrArg u (agree ip away)).trans (sound y hy).symm))
    by_cases h : ip = 3
    · exact refute 4 3 false s4 (fun eq => (by decide : (3 : Fin 9) ≠ 4) (h.symm.trans eq))
    · exact refute 3 4 false s3 h

theorem raw_primitive (C : Circuit) (c : Restriction) (i : Fin 9) : Primitive c (signal C i.val) := by
  cases fix : fixed c i with
  | none => exact .unary i fix id (fun x _ => input_signal C i x)
  | some v => exact .constant v (fun x hx => (input_signal C i x).trans (hx i v fix))

theorem opening_primitive (C : Circuit) (c : Restriction) (shape : Shape C) {suffix : List Gate}
    (opened : C.gates = firstGate :: secondGate :: suffix) {k : ℕ} (small : k < 2) :
    Primitive c (signal C (9 + k)) := by
  have long : 2 ≤ C.gates.length := by simp [opened]
  let j : Fin C.gates.length := ⟨k, by omega⟩
  have a (x : Row) (hx : Fits c x) : signal C 0 x = true :=
    (input_signal C (0 : Fin 9) x).trans (hx 0 true (by simp [fixed]))
  have b (x : Row) (hx : Fits c x) : signal C 1 x = true :=
    (input_signal C (1 : Fin 9) x).trans (hx 1 true (by simp [fixed]))
  refine .constant true fun x hx => ?_
  have eq := gate_signal C shape j x
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · have head : C.gates.get j = firstGate := by simp [opened, j]
    rw [head] at eq
    simpa [j, evalGate, firstGate, GateOp.eval, a x hx, b x hx] using eq
  · have head : C.gates.get j = secondGate := by simp [opened, j]
    rw [head] at eq
    simpa [j, evalGate, secondGate, GateOp.eval, a x hx, b x hx] using eq

def combine (isOr a b : Bool) : Bool := if isOr then a || b else a && b

theorem combine_absorbs_right (kind x : Bool) : combine kind x kind = kind := by cases kind <;> cases x <;> rfl
theorem combine_absorbs_left (kind x : Bool) : combine kind kind x = kind := by cases kind <;> cases x <;> rfl

theorem choose_mask {f : Bool → Bool} (nonconstant : f false ≠ f true) (v : Bool) : ∃ b, f b = v := by
  by_cases h : f false = v
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    cases v <;> cases Zero : f false <;> cases One : f true <;> simp_all

structure Merge (C : Circuit) (c : Restriction) where
  gate : Fin C.gates.length
  afterOpening : 2 ≤ gate.val
  lhs : ℕ
  rhs : ℕ
  readsL : lhs ∈ (C.gates.get gate).inputs
  readsR : rhs ∈ (C.gates.get gate).inputs
  leftVar : Fin 9
  rightVar : Fin 9
  distinct : leftVar ≠ rightVar
  freeL : fixed c leftVar = none
  freeR : fixed c rightVar = none
  u : Bool → Bool
  v : Bool → Bool
  variesL : u false ≠ u true
  variesR : v false ≠ v true
  leftEq : ∀ x, Fits c x → signal C lhs x = u (x leftVar)
  rightEq : ∀ x, Fits c x → signal C rhs x = v (x rightVar)
  isOr : Bool
  valueEq : ∀ x, Fits c x → signal C (9 + gate.val) x = combine isOr (signal C lhs x) (signal C rhs x)
  earlier : ∀ n < 9 + gate.val, Primitive c (signal C n)

theorem first_merge (C : Circuit) (c : Restriction) (shape : Shape C) {suffix : List Gate}
    (opened : C.gates = firstGate :: secondGate :: suffix) (last : C.output + 1 = 9 + C.gates.length)
    (correct : ∀ row, C.eval (List.ofFn row) = target row) : Nonempty (Merge C c) := by
  classical
  have hasGate : ∃ k : ℕ, k < C.gates.length ∧ ¬ Primitive c (signal C (9 + k)) := by
    have long : 2 ≤ C.gates.length := by simp [opened]
    refine ⟨C.gates.length - 1, by omega, fun simple => ?_⟩
    have equation : 9 + (C.gates.length - 1) = C.output := by omega
    rw [equation] at simple
    exact target_nonprimitive c (simple.map id (fun x _ => (correct x).symm))
  let k := Nat.find hasGate
  have minimal : k < C.gates.length ∧ ¬ Primitive c (signal C (9 + k)) := Nat.find_spec hasGate
  let g : Fin C.gates.length := ⟨k, minimal.1⟩
  have after : 2 ≤ k := by
    by_contra before
    exact minimal.2 (opening_primitive C c shape opened (by omega))
  have early (w : ℕ) (low : w < 9 + k) : Primitive c (signal C w) := by
    by_cases raw : w < 9
    · exact raw_primitive C c ⟨w, raw⟩
    · have wire : w = 9 + (w - 9) := by omega
      rw [wire]
      by_contra failure
      exact (Nat.find_min hasGate (show w - 9 < k by omega)) ⟨by omega, failure⟩
  rcases shape g with ⟨op, a, bound, reads⟩ | ⟨op, a, b, ab, bound, reads⟩
  · exfalso
    exact minimal.2 ((early a bound).map (! ·) (fun x _ => by
      have e := gate_signal C shape g x
      rw [evalGate, op, reads] at e
      simpa [GateOp.eval] using e))
  · obtain ⟨isOr, opEq⟩ : ∃ bit : Bool, (C.gates.get g).op = if bit then .or else .and := by
      rcases op with andOp | orOp
      · exact ⟨false, andOp⟩
      · exact ⟨true, orOp⟩
    have boundB : b < 9 + k := bound
    have boundA : a < 9 + k := ab.trans boundB
    have value (x : Row) : signal C (9 + k) x = combine isOr (signal C a x) (signal C b x) := by
      have e := gate_signal C shape g x
      rw [evalGate, reads, opEq] at e
      cases isOr <;> simpa [combine, GateOp.eval] using e
    have variesA : ¬ ∃ v, ∀ row, Fits c row → signal C a row = v := by
      rintro ⟨v, fixedA⟩
      exact minimal.2 ((early b boundB).map (combine isOr v) (fun row hr => by rw [value row, fixedA row hr]))
    have variesB : ¬ ∃ v, ∀ row, Fits c row → signal C b row = v := by
      rintro ⟨v, fixedB⟩
      exact minimal.2 ((early a boundA).map (fun x => combine isOr x v) (fun row hr => by rw [value row, fixedB row hr]))
    rcases early a boundA with ⟨vA, constA⟩ | ⟨i, fi, u, left⟩
    · exact False.elim (variesA ⟨vA, constA⟩)
    · rcases early b boundB with ⟨vB, constB⟩ | ⟨j, fj, v, right⟩
      · exact False.elim (variesB ⟨vB, constB⟩)
      · have different : i ≠ j := by
          intro eq
          subst j
          exact minimal.2 (.unary i fi (fun bit => combine isOr (u bit) (v bit))
            (fun x hx => by rw [value x, left x hx, right x hx]))
        have ncA : u false ≠ u true := by
          intro no
          exact variesA ⟨u false, fun x hx => by rw [left x hx]; cases h : x i <;> simp [no]⟩
        have ncB : v false ≠ v true := by
          intro no
          exact variesB ⟨v false, fun x hx => by rw [right x hx]; cases h : x j <;> simp [no]⟩
        refine ⟨g, after, a, b, ?_, ?_, i, j, different, fi, fj, u, v, ncA, ncB, left, right,
          isOr, fun x _ => value x, early⟩
        · rw [reads]; simp
        · rw [reads]; simp

open PEqualNP.CircuitLowerBounds

private theorem count_head_tail (g : Gate) (gs : List Gate) (w : ℕ)
    (head : w ∈ g.inputs) (later : w ∈ gs.flatMap Gate.inputs) : 2 ≤ ((g :: gs).flatMap Gate.inputs).count w := by
  have a := List.count_pos_iff.mpr head
  have b := List.count_pos_iff.mpr later
  simp only [List.flatMap_cons, List.count_append]
  omega

private theorem two_readers (gs : List Gate) (w : ℕ) {i j : Fin gs.length}
    (distinct : i ≠ j) (one : w ∈ (gs.get i).inputs) (two : w ∈ (gs.get j).inputs) :
    2 ≤ (gs.flatMap Gate.inputs).count w := by
  induction gs with
  | nil => exact Fin.elim0 i
  | cons g tail ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (distinct rfl)
      | succ j =>
        exact count_head_tail g tail w one (List.mem_flatMap_of_mem (List.get_mem tail j) two)
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        exact count_head_tail g tail w two (List.mem_flatMap_of_mem (List.get_mem tail i) one)
      | succ j =>
        have lower := ih (fun eq => distinct (congrArg Fin.succ eq)) one two
        simp only [List.flatMap_cons, List.count_append]
        omega

theorem duplicate_of_many_readers {C : Circuit} {suffix : List Gate}
    (opening : C.gates = firstGate :: secondGate :: suffix) (wires readers : Finset ℕ)
    (more : wires.card < readers.card) (other : ∀ w ∈ wires, 2 ≤ w)
    (uses : ∀ k ∈ readers, ∃ h : k < C.gates.length, ∃ w ∈ wires, w ∈ (C.gates.get ⟨k, h⟩).inputs) :
    ∃ w ∈ wires, 2 ≤ (suffix.flatMap Gate.inputs).count w := by
  classical
  by_contra noRepeat
  have choices (k : readers) : ∃ h : k.val < C.gates.length, ∃ w ∈ wires, w ∈ (C.gates.get ⟨k.val, h⟩).inputs :=
    uses k.val k.property
  choose less read member input using choices
  let select (k : readers) : wires := ⟨read k, member k⟩
  have injective : Function.Injective select := by
    intro a b same
    by_contra distinct
    have eq : read a = read b := congrArg Subtype.val same
    let i : Fin C.gates.length := ⟨a.val, less a⟩
    let j : Fin C.gates.length := ⟨b.val, less b⟩
    have positions : i ≠ j := fun e => distinct (Subtype.ext (congrArg Fin.val e))
    have both : 2 ≤ (C.gates.flatMap Gate.inputs).count (read a) :=
      two_readers C.gates (read a) positions (input a) (by rw [eq]; exact input b)
    have lower : 2 ≤ read a := other _ (member a)
    have same_count : (C.gates.flatMap Gate.inputs).count (read a) = (suffix.flatMap Gate.inputs).count (read a) := by
      simp [opening, firstGate, secondGate, show 0 ≠ read a by omega,
        show 1 ≠ read a by omega]
    exact noRepeat ⟨read a, member a, same_count ▸ both⟩
  have upper := Fintype.card_le_of_injective select injective
  simp only [Fintype.card_coe] at upper
  omega

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_27577_aux.Support (target)

private theorem some_operand_differs (C : Circuit) (shape : Shape C) (j : Fin C.gates.length)
    (x y : Row) (out : signal C (9 + j.val) x ≠ signal C (9 + j.val) y) :
    ∃ w ∈ (C.gates.get j).inputs, signal C w x ≠ signal C w y := by
  by_contra disagree
  apply out
  rw [gate_signal C shape j x, gate_signal C shape j y]
  apply gate_congr
  intro w hw
  by_contra differs
  exact disagree ⟨w, hw, differs⟩

private theorem Primitive.agrees_at {c : Restriction} {f : Row → Bool} (simple : Primitive c f)
    (i : Fin 9) {x y : Row} (hx : Fits c x) (hy : Fits c y) (outside : ∀ k, k ≠ i → x k = y k)
    (changed : f x ≠ f y) : ∀ a b, Fits c a → Fits c b → a i = b i → f a = f b := by
  cases simple with
  | constant v eq => exact False.elim (changed ((eq x hx).trans (eq y hy).symm))
  | unary k free u eq =>
    have ki : k = i := by
      by_contra h
      exact changed ((eq x hx).trans ((congrArg u (outside k h)).trans (eq y hy).symm))
    subst k
    exact fun a b ha hb agrees => (eq a ha).trans ((congrArg u agrees).trans (eq b hb).symm)

def RepeatedWith (C : Circuit) (suffix : List Gate) (c : Restriction) (i : Fin 9) : Prop :=
  ∃ w, 2 ≤ (suffix.flatMap Gate.inputs).count w ∧
    (∃ x y, Fits c x ∧ Fits c y ∧ (∀ k, k ≠ i → x k = y k) ∧ signal C w x ≠ signal C w y) ∧
    ∀ x y, Fits c x → Fits c y → x i = y i → signal C w x = signal C w y

private theorem repeat_from_probe {C : Circuit} {c : Restriction} {suffix : List Gate}
    (shape : Shape C) (opened : C.gates = firstGate :: secondGate :: suffix)
    (last : C.output + 1 = 9 + C.gates.length) (m : Merge C c) (i : Fin 9)
    {x y : Row} (hx : Fits c x) (hy : Fits c y) (other : ∀ j, j ≠ i → x j = y j) (changed : x i ≠ y i)
    (out : signal C C.output x ≠ signal C C.output y) (masked : signal C (9 + m.gate.val) x = signal C (9 + m.gate.val) y)
    (read : ∃ w ∈ (C.gates.get m.gate).inputs, signal C w x ≠ signal C w y) : RepeatedWith C suffix c i := by
  classical
  let differs (w : ℕ) := signal C w x ≠ signal C w y
  let after (j : ℕ) := j < C.gates.length ∧ m.gate.val < j ∧ differs (9 + j)
  have later : ∃ j, after j := by
    have inside := m.gate.isLt
    have afterGate : m.gate.val < C.gates.length - 1 := by
      by_contra h
      have outAtMerge : C.output = 9 + m.gate.val := by omega
      exact out (by rwa [outAtMerge])
    refine ⟨C.gates.length - 1, by omega, afterGate, ?_⟩
    have atEnd : 9 + (C.gates.length - 1) = C.output := by omega
    rw [atEnd]
    exact out
  let q := Nat.find later
  have qSpec : q < C.gates.length ∧ m.gate.val < q ∧ differs (9 + q) := Nat.find_spec later
  let earlier := (Finset.range m.gate.val).filter fun k => differs (9 + k)
  let wires := insert i.val (earlier.image fun k => 9 + k)
  let readers := insert m.gate.val (insert q earlier)
  have freshRaw : i.val ∉ earlier.image (fun k => 9 + k) := by
    intro h
    obtain ⟨k, _, eq⟩ := Finset.mem_image.mp h
    have := i.isLt
    omega
  have freshLater : q ∉ earlier := by
    intro h
    have low := Finset.mem_range.mp (Finset.mem_filter.mp h).1
    omega
  have freshMerge : m.gate.val ∉ insert q earlier := by
    intro h
    rcases Finset.mem_insert.mp h with eq | old
    · omega
    · have low := Finset.mem_range.mp (Finset.mem_filter.mp old).1
      omega
  have more : wires.card < readers.card := by
    dsimp [wires, readers]
    rw [Finset.card_insert_of_notMem freshRaw, Finset.card_insert_of_notMem freshMerge,
      Finset.card_insert_of_notMem freshLater, Finset.card_image_of_injective _ (fun a b h => by omega)]
    omega
  have wire_i_differs : differs i.val := by
    simpa only [differs, input_signal C i x, input_signal C i y] using changed
  have before (w : ℕ) (hw : w ∈ wires) : w < 9 + m.gate.val ∧ differs w := by
    rcases Finset.mem_insert.mp hw with rfl | rest
    · exact ⟨by have := i.isLt; omega, wire_i_differs⟩
    · obtain ⟨k, good, rfl⟩ := Finset.mem_image.mp rest
      exact ⟨by have := Finset.mem_range.mp (Finset.mem_filter.mp good).1; omega, (Finset.mem_filter.mp good).2⟩
  have listed (w : ℕ) (early : w < 9 + m.gate.val) (diff : differs w) : w ∈ wires := by
    by_cases raw : w < 9
    · let j : Fin 9 := ⟨w, raw⟩
      have equal : j = i := by
        by_contra ne
        apply diff
        exact (input_signal C j x).trans ((other j ne).trans (input_signal C j y).symm)
      exact Finset.mem_insert.mpr (Or.inl (congrArg Fin.val equal))
    · have eq : 9 + (w - 9) = w := by omega
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨w - 9,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), eq.symm ▸ diff⟩, eq⟩))
  have otherWire (w : ℕ) (mem : w ∈ wires) : 2 ≤ w := by
    have diff := (before w mem).2
    have all (j : Fin 9) (fj : fixed c j = some true) : signal C j.val x = signal C j.val y := by
      rw [input_signal C j x, input_signal C j y, hx j true fj, hy j true fj]
    by_contra small
    rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
    · exact diff (all 0 (by simp [fixed]))
    · exact diff (all 1 (by simp [fixed]))
  have uses (k : ℕ) (hk : k ∈ readers) :
      ∃ h : k < C.gates.length, ∃ w ∈ wires, w ∈ (C.gates.get ⟨k, h⟩).inputs := by
    rcases Finset.mem_insert.mp hk with rfl | rest
    · obtain ⟨w, uses, diff⟩ := read
      exact ⟨m.gate.isLt, w, listed w (reads_backward shape m.gate uses) diff, uses⟩
    · rcases Finset.mem_insert.mp rest with rfl | early
      · let j : Fin C.gates.length := ⟨q, qSpec.1⟩
        obtain ⟨w, used, diff⟩ := some_operand_differs C shape j x y qSpec.2.2
        have low := reads_backward shape j used
        have early : w < 9 + m.gate.val := by
          by_contra no
          by_cases eq : w = 9 + m.gate.val
          · exact diff (eq.symm ▸ masked)
          · have atGate : 9 + (w - 9) = w := by omega
            have earlier : w - 9 < q := by change w < 9 + q at low; omega
            exact (Nat.find_min later earlier) ⟨by omega, by omega, atGate.symm ▸ diff⟩
        exact ⟨qSpec.1, w, listed w early diff, used⟩
      · have old := Finset.mem_filter.mp early
        have low := Finset.mem_range.mp old.1
        let j : Fin C.gates.length := ⟨k, low.trans m.gate.isLt⟩
        obtain ⟨w, used, diff⟩ := some_operand_differs C shape j x y old.2
        have wb : w < 9 + k := reads_backward shape j used
        exact ⟨j.isLt, w, listed w (by omega) diff, used⟩
  obtain ⟨w, member, repeated⟩ := duplicate_of_many_readers opened wires readers more otherWire uses
  obtain ⟨early, diff⟩ := before w member
  exact ⟨w, repeated, ⟨x, y, hx, hy, other, diff⟩, (m.earlier w early).agrees_at i hx hy other diff⟩

private theorem changed_bit {x y : Row} {i : Fin 9} (agrees : ∀ k, k ≠ i → x k = y k)
    (detects : target x ≠ target y) : x i ≠ y i := by
  intro h
  apply detects
  congr 1
  funext j
  by_cases here : j = i
  · simpa [here] using h
  · exact agrees j here

private theorem distinguishes {u : Bool → Bool} (vary : u false ≠ u true) {a b : Bool} (changed : a ≠ b) :
    u a ≠ u b := by cases a <;> cases b <;> simp_all [ne_comm]

theorem repeat_left {C : Circuit} {c : Restriction} {suffix : List Gate}
    (shape : Shape C) (opened : C.gates = firstGate :: secondGate :: suffix)
    (last : C.output + 1 = 9 + C.gates.length) (correct : ∀ row, C.eval (List.ofFn row) = target row)
    (m : Merge C c) {bit : Bool} (mask : m.v bit = m.isOr) (sensitivity : Sensitive c m.leftVar m.rightVar bit) :
    RepeatedWith C suffix c m.leftVar := by
  obtain ⟨x, y, hx, hy, agrees, bx, by', detects⟩ := sensitivity
  have changed := changed_bit agrees detects
  have out : signal C C.output x ≠ signal C C.output y := by
    change C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)
    rwa [correct x, correct y]
  have masked (r : Row) (hr : Fits c r) (b : r m.rightVar = bit) : signal C (9 + m.gate.val) r = m.isOr := by
    rw [m.valueEq r hr, m.rightEq r hr, b, mask, combine_absorbs_right]
  apply repeat_from_probe shape opened last m m.leftVar hx hy agrees changed out
    ((masked x hx bx).trans (masked y hy by').symm)
  exact ⟨m.lhs, m.readsL, by rw [m.leftEq x hx, m.leftEq y hy]; exact distinguishes m.variesL changed⟩

theorem repeat_right {C : Circuit} {c : Restriction} {suffix : List Gate}
    (shape : Shape C) (opened : C.gates = firstGate :: secondGate :: suffix)
    (last : C.output + 1 = 9 + C.gates.length) (correct : ∀ row, C.eval (List.ofFn row) = target row)
    (m : Merge C c) {bit : Bool} (mask : m.u bit = m.isOr) (sensitivity : Sensitive c m.rightVar m.leftVar bit) :
    RepeatedWith C suffix c m.rightVar := by
  obtain ⟨x, y, hx, hy, agrees, bx, by', detects⟩ := sensitivity
  have changed := changed_bit agrees detects
  have out : signal C C.output x ≠ signal C C.output y := by
    change C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)
    rwa [correct x, correct y]
  have masked (r : Row) (hr : Fits c r) (b : r m.leftVar = bit) : signal C (9 + m.gate.val) r = m.isOr := by
    rw [m.valueEq r hr, m.leftEq r hr, b, mask, combine_absorbs_left]
  apply repeat_from_probe shape opened last m m.rightVar hx hy agrees changed out
    ((masked x hx bx).trans (masked y hy by').symm)
  exact ⟨m.rhs, m.readsR, by rw [m.rightEq x hx, m.rightEq y hy]; exact distinguishes m.variesR changed⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_27577_aux.Support (target)

private theorem base_restriction : ∀ (c : Restriction) (i : Fin 9) (v : Bool),
    fixed bothTrue i = some v → fixed c i = some v := by
  decide +kernel

private theorem can_clear {i : Fin 9} (h : i = 5 ∨ i = 8) :
    ∃ c, c ≠ bothTrue ∧ fixed c i = some false := by
  rcases h with rfl | rfl
  · exact ⟨clearFive, by decide, by decide⟩
  · exact ⟨clearEight, by decide, by decide⟩

private theorem impossible_repeated_pair {C : Circuit} {suffix : List Gate} {c : Restriction}
    {i j : Fin 9} (distinct : i ≠ j) (left : RepeatedWith C suffix c i) (right : RepeatedWith C suffix c j)
    (unique : ∀ {v w}, 2 ≤ (suffix.flatMap Gate.inputs).count v → 2 ≤ (suffix.flatMap Gate.inputs).count w → v = w) :
    False := by
  obtain ⟨v, repeatsV, ⟨x, y, hx, hy, agrees, detects⟩, _⟩ := left
  obtain ⟨w, repeatsW, _, controlled⟩ := right
  have same := unique repeatsV repeatsW
  rw [same] at detects
  exact detects (controlled x y hx hy (agrees j (Ne.symm distinct)))

private theorem impossible_clear_repeat {C : Circuit} {suffix : List Gate} {i : Fin 9}
    (shape : Shape C) (opened : C.gates = firstGate :: secondGate :: suffix)
    (last : C.output + 1 = 9 + C.gates.length) (correct : ∀ row, C.eval (List.ofFn row) = target row)
    (unique : ∀ {v w}, 2 ≤ (suffix.flatMap Gate.inputs).count v → 2 ≤ (suffix.flatMap Gate.inputs).count w → v = w)
    (clearable : i = 5 ∨ i = 8) (base : RepeatedWith C suffix bothTrue i) : False := by
  obtain ⟨c, reduced, fixedBit⟩ := can_clear clearable
  obtain ⟨m⟩ := first_merge C c shape opened last correct
  obtain ⟨bl, masksLeft⟩ := choose_mask m.variesL m.isOr
  obtain ⟨br, masksRight⟩ := choose_mask m.variesR m.isOr
  obtain ⟨j, another⟩ : ∃ j, RepeatedWith C suffix c j := by
    rcases reduced_pair_sensitive (bi := bl) (bj := br) reduced m.distinct m.freeL m.freeR with left | right
    · exact ⟨_, repeat_left shape opened last correct m masksRight left⟩
    · exact ⟨_, repeat_right shape opened last correct m masksLeft right⟩
  obtain ⟨w, count, _, controls⟩ := base
  obtain ⟨v, count', ⟨x, y, hx, hy, _, detects⟩, _⟩ := another
  have sameWire := unique count' count
  rw [sameWire] at detects
  have hb (row : Row) (fits : Fits c row) : Fits bothTrue row :=
    fun k value fixedAt => fits k value (base_restriction c k value fixedAt)
  exact detects (controls x y (hb x hx) (hb y hy) ((hx i false fixedBit).trans (hy i false fixedBit).symm))

theorem no_matching_same_pair (C : Circuit) {suffix : List Gate}
    (opened : C.gates = firstGate :: secondGate :: suffix) (last : C.output + 1 = 9 + C.gates.length)
    (correct : ∀ row, C.eval (List.ofFn row) = target row) (shape : Shape C) (live : Live C)
    (size : C.gates.length ≤ 12) : False := by
  have long : 2 ≤ C.gates.length := by simp [opened]
  have out : 9 ≤ C.output := by omega
  have unique {v w} (rv : 2 ≤ (suffix.flatMap Gate.inputs).count v) (rw : 2 ≤ (suffix.flatMap Gate.inputs).count w) : v = w :=
    suffix_repeat_unique opened out correct shape live size rv rw
  obtain ⟨m⟩ := first_merge C bothTrue shape opened last correct
  obtain ⟨bl, masksLeft⟩ := choose_mask m.variesL m.isOr
  obtain ⟨br, masksRight⟩ := choose_mask m.variesR m.isOr
  by_cases failsLeft : m.leftVar = 2 ∧ (m.rightVar = 5 ∨ m.rightVar = 8) ∧ br = true
  · have goodRight : ¬ (m.rightVar = 2 ∧ (m.leftVar = 5 ∨ m.leftVar = 8) ∧ bl = true) := by
      intro bad
      rcases failsLeft.2.1 with five | eight
      · exact (by decide : (5 : Fin 9) ≠ 2) (five.symm.trans bad.1)
      · exact (by decide : (8 : Fin 9) ≠ 2) (eight.symm.trans bad.1)
    have repeats := repeat_right shape opened last correct m masksLeft
      (both_true_sensitive m.distinct.symm m.freeR m.freeL goodRight)
    exact impossible_clear_repeat shape opened last correct (fun a b => unique a b) failsLeft.2.1 repeats
  · have repeatsLeft := repeat_left shape opened last correct m masksRight
      (both_true_sensitive m.distinct m.freeL m.freeR failsLeft)
    by_cases failsRight : m.rightVar = 2 ∧ (m.leftVar = 5 ∨ m.leftVar = 8) ∧ bl = true
    · exact impossible_clear_repeat shape opened last correct (fun a b => unique a b) failsRight.2.1 repeatsLeft
    · have repeatsRight := repeat_right shape opened last correct m masksLeft
        (both_true_sensitive m.distinct.symm m.freeR m.freeL failsRight)
      exact impossible_repeated_pair m.distinct repeatsLeft repeatsRight (fun a b => unique a b)

end PEqualNP.Outside.L_meta_27577_aux

open PEqualNP.Outside.L_meta_27577_aux

theorem PEqualNP.Outside.L_meta_27577 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩)) := by
  rintro ⟨C, _, small, correct, last, shape, _, live, first, second⟩
  obtain ⟨suffix, opened⟩ := opening first second
  exact no_matching_same_pair C opened last correct shape live small
