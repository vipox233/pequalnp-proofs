import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1344_aux

-- Grade and circuit primitives adapted from the accepted proof at pin
-- 1adcd7757ae90df113b64e1e1c0794b4eb2fb1b8, lean/PEqualNP/Outside/L_lib_1294.lean.
-- The grade is generalized to direct lists; the circuit operations build a scalar decoder.
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

def appendNot (C : Circuit) (a : Nat) : Circuit := appendGate C ⟨.not, [a]⟩

def withOutput (C : Circuit) (o : Nat) : Circuit := ⟨C.gates, o⟩

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl gateStep x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons,ih]
    simp [gateStep] <;> omega

private theorem fold_value (gates : List Gate) (x : List Bool) {i : Nat} (valid : i < x.length) :
    (gates.foldl gateStep x).getD i false = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have available : i < (gateStep x g).length := by simp [gateStep]; omega
    rw [List.foldl_cons,ih _ available]
    exact List.getD_append _ _ _ _ valid

@[local simp] theorem emptyCircuit_size : emptyCircuit.size = 0 := rfl

@[local simp] theorem emptyCircuit_notCount : notCount emptyCircuit = 0 := rfl

theorem emptyCircuit_fanInTwo : FanInTwo emptyCircuit := by
  simp [FanInTwo,emptyCircuit]

theorem emptyCircuit_readsBack (n : Nat) : ReadsBack n emptyCircuit := by
  simp [ReadsBack,emptyCircuit]

@[local simp] theorem withOutput_size (C : Circuit) (o : Nat) : (withOutput C o).size = C.size := rfl

@[local simp] theorem withOutput_output (C : Circuit) (o : Nat) : (withOutput C o).output = o := rfl

@[local simp] theorem withOutput_notCount (C : Circuit) (o : Nat) :
    notCount (withOutput C o) = notCount C := rfl

@[local simp] theorem withOutput_fanInTwo (C : Circuit) (o : Nat) :
    FanInTwo (withOutput C o) ↔ FanInTwo C := Iff.rfl

@[local simp] theorem withOutput_readsBack (n : Nat) (C : Circuit) (o : Nat) :
    ReadsBack n (withOutput C o) ↔ ReadsBack n C := Iff.rfl

@[local simp] theorem withOutput_value (C : Circuit) (o : Nat) (x : List Bool) (i : Nat) :
    value (withOutput C o) x i = value C x i := rfl

@[local simp] theorem withOutput_eval (C : Circuit) (o : Nat) (x : List Bool) :
    (withOutput C o).eval x = value C x o := rfl

@[local simp] theorem appendGate_size (C : Circuit) (g : Gate) :
    (appendGate C g).size = C.size + 1 := by
  simp [appendGate,Circuit.size]

@[local simp] theorem appendGate_output (C : Circuit) (g : Gate) :
    (appendGate C g).output = C.output := rfl

theorem appendGate_prefix (C : Circuit) (g : Gate) : C.gates <+: (appendGate C g).gates :=
  ⟨[g],rfl⟩

@[local simp] theorem appendGate_notCount (C : Circuit) (g : Gate) :
    notCount (appendGate C g) = notCount C + (@ite ℕ (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not) 1 0) := by
  by_cases inv : g.op = .not <;> simp [notCount,appendGate,inv]

@[local simp] theorem nextWire_appendGate (n : Nat) (C : Circuit) (g : Gate) :
    nextWire n (appendGate C g) = nextWire n C + 1 := by
  simp [nextWire,Nat.add_assoc]

theorem appendGate_fanInTwo {C : Circuit} {g : Gate} (basis : FanInTwo C)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : FanInTwo (appendGate C g) := by
  intro k hk
  rcases List.mem_append.mp hk with old | new
  · exact basis k old
  · have same : k = g := List.mem_singleton.mp new
    subst k
    exact ⟨op,arity⟩

theorem appendGate_readsBack {n : Nat} {C : Circuit} {g : Gate} (valid : ReadsBack n C)
    (inputs : ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old] at hi
    exact valid j old i hi
  · change j < (C.gates ++ [g]).length at hj
    have same : j = C.gates.length := by simp at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    exact inputs i (by simpa using hi)

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = nextWire x.length C := by
  rw [wires_eq]
  exact fold_length C.gates x

theorem value_input (C : Circuit) (x : List Bool) {i : Nat} (valid : i < x.length) :
    value C x i = x.getD i false := by
  rw [value,wires_eq]
  exact fold_value C.gates x valid

theorem nextWire_le_of_prefix {n : Nat} {C D : Circuit} (extension : C.gates <+: D.gates) :
    nextWire n C ≤ nextWire n D := Nat.add_le_add_left extension.length_le n

theorem value_of_prefix {C D : Circuit} (extension : C.gates <+: D.gates) {x : List Bool}
    {i : Nat} (valid : i < nextWire x.length C) : value D x i = value C x i := by
  obtain ⟨rest,appended⟩ := extension
  simp only [value,wires_eq,← appended,List.foldl_append]
  apply fold_value
  rw [fold_length]
  exact valid

theorem appendGate_wires (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => value C x i)] := by
  simp [appendGate,wires_eq,gateStep,value]

theorem appendGate_old {C : Circuit} {g : Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGate C g) x i = value C x i :=
  value_of_prefix (appendGate_prefix C g) valid

theorem appendGate_new (C : Circuit) (g : Gate) (x : List Bool) :
    value (appendGate C g) x (nextWire x.length C) =
      g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value,appendGate_wires,← wires_length]
  simp [List.getD_eq_getElem?_getD]

@[local simp] theorem appendNot_size (C : Circuit) (a : Nat) :
    (appendNot C a).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendNot_notCount (C : Circuit) (a : Nat) :
    notCount (appendNot C a) = notCount C + 1 := by simp [appendNot]

theorem appendNot_fanInTwo {C : Circuit} {a : Nat} (basis : FanInTwo C) :
    FanInTwo (appendNot C a) := appendGate_fanInTwo (g := ⟨.not,[a]⟩) basis (by simp) (by simp)

theorem appendNot_readsBack {n : Nat} {C : Circuit} {a : Nat} (valid : ReadsBack n C)
    (input : a < nextWire n C) : ReadsBack n (appendNot C a) := by
  apply appendGate_readsBack (g := ⟨.not,[a]⟩) valid
  intro i member
  have same : i = a := List.mem_singleton.mp member
  subst i
  exact input

theorem appendNot_new (C : Circuit) (x : List Bool) (a : Nat) :
    value (appendNot C a) x (nextWire x.length C) = !value C x a := by
  exact appendGate_new C ⟨.not,[a]⟩ x
def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendGates (C : Circuit) (gates : List Gate) : Circuit := ⟨C.gates ++ gates, C.output⟩

def appendFamily {k : Nat} (C : Circuit) (gate : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn gate)

private theorem appendGates_cons (C : Circuit) (g : Gate) (rest : List Gate) :
    appendGates C (g :: rest) = appendGates (appendGate C g) rest := by
  simp [appendGates,appendGate,List.append_assoc]

theorem appendGates_prefix (C : Circuit) (gates : List Gate) : C.gates <+: (appendGates C gates).gates :=
  ⟨gates,rfl⟩

@[local simp] theorem appendGates_size (C : Circuit) (gates : List Gate) :
    (appendGates C gates).size = C.size + gates.length := by
  simp [appendGates,Circuit.size]

@[local simp] theorem appendGates_nextWire (n : Nat) (C : Circuit) (gates : List Gate) :
    nextWire n (appendGates C gates) = nextWire n C + gates.length := by
  simp [nextWire,Nat.add_assoc]

@[local simp] theorem appendGates_output (C : Circuit) (gates : List Gate) :
    (appendGates C gates).output = C.output := rfl

theorem appendGates_notCount (C : Circuit) (gates : List Gate) :
    notCount (appendGates C gates) =
      notCount C + (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length := by
  simp [notCount,appendGates]

theorem appendGates_notCount_eq {C : Circuit} {gates : List Gate}
    (noNot : ∀ g ∈ gates, g.op ≠ .not) : notCount (appendGates C gates) = notCount C := by
  have empty : (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.filter_eq_nil_iff.mpr fun g member => by simp [noNot g member]
  simp [appendGates_notCount,empty]

private abbrev GateShape (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem appendGates_fanInTwo {C : Circuit} {gates : List Gate} (basis : FanInTwo C)
    (shape : ∀ g ∈ gates, GateShape g) : FanInTwo (appendGates C gates) := by
  intro g member
  rcases List.mem_append.mp member with old | added
  · exact basis g old
  · exact shape g added

theorem appendGates_readsBack {n : Nat} {C : Circuit} {gates : List Gate} (valid : ReadsBack n C)
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGates C gates) := by
  induction gates generalizing C with
  | nil => simpa [appendGates] using valid
  | cons g rest ih =>
    rw [appendGates_cons]
    have fits : ∀ i ∈ g.inputs, i < nextWire n C := reads g (List.mem_cons_self ..)
    apply ih (appendGate_readsBack valid fits)
    intro h member i input
    exact Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
      (nextWire_le_of_prefix (appendGate_prefix C g))

theorem appendGates_old {C : Circuit} {gates : List Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGates C gates) x i = value C x i :=
  value_of_prefix (appendGates_prefix C gates) valid

private def readGate (C : Circuit) (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (value C x))

private theorem appendGates_wires {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) :
    (appendGates C gates).wires x = C.wires x ++ gates.map (readGate C x) := by
  induction gates generalizing C with
  | nil => simp [appendGates]
  | cons g rest ih =>
    have restReads : ∀ h ∈ rest, ∀ i ∈ h.inputs, i < nextWire x.length (appendGate C g) :=
      fun h member i input => Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
        (nextWire_le_of_prefix (appendGate_prefix C g))
    have tail : rest.map (readGate (appendGate C g) x) = rest.map (readGate C x) := by
      apply List.map_congr_left
      intro h member
      unfold readGate
      apply congrArg h.op.eval
      apply List.map_congr_left
      intro i input
      exact appendGate_old (g := g) (reads h (List.mem_cons_of_mem _ member) i input)
    rw [appendGates_cons,ih restReads,tail,appendGate_wires]
    simp [List.append_assoc,readGate]

theorem appendGates_new {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) (j : Fin gates.length) :
    value (appendGates C gates) x (nextWire x.length C + j.val) =
      gates[j].op.eval (gates[j].inputs.map (value C x)) := by
  change ((appendGates C gates).wires x).getD (nextWire x.length C + j.val) false = _
  rw [appendGates_wires (x := x) reads]
  have within : (C.wires x).length ≤ nextWire x.length C + j.val := by rw [wires_length]; omega
  have index : nextWire x.length C + j.val - nextWire x.length C = j.val := by omega
  rw [List.getD_append_right _ _ _ _ within,wires_length,index]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,readGate]

theorem appendFamily_prefix {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    C.gates <+: (appendFamily C gate).gates := appendGates_prefix C _

@[local simp] theorem appendFamily_size {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).size = C.size + k := by simp [appendFamily]

@[local simp] theorem appendFamily_nextWire {k : Nat} (n : Nat) (C : Circuit) (gate : Fin k → Gate) :
    nextWire n (appendFamily C gate) = nextWire n C + k := by simp [appendFamily]

theorem appendFamily_notCount_eq {k : Nat} {C : Circuit} {gate : Fin k → Gate}
    (noNot : ∀ j, (gate j).op ≠ .not) : notCount (appendFamily C gate) = notCount C := by
  apply appendGates_notCount_eq
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact noNot j

theorem appendFamily_fanInTwo {k : Nat} {C : Circuit} {gate : Fin k → Gate} (basis : FanInTwo C)
    (shape : ∀ j, GateShape (gate j)) : FanInTwo (appendFamily C gate) := by
  apply appendGates_fanInTwo basis
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact shape j

theorem appendFamily_readsBack {k n : Nat} {C : Circuit} {gate : Fin k → Gate}
    (valid : ReadsBack n C) (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C) :
    ReadsBack n (appendFamily C gate) := by
  apply appendGates_readsBack valid
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact reads j

theorem appendFamily_new {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire x.length C) (j : Fin k) :
    value (appendFamily C gate) x (nextWire x.length C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have readsList : ∀ g ∈ List.ofFn gate, ∀ i ∈ g.inputs, i < nextWire x.length C := by
    intro g member
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp member
    exact reads t
  let t : Fin (List.ofFn gate).length := ⟨j.val,by simpa using j.isLt⟩
  simpa [appendFamily,t] using appendGates_new readsList t
private theorem old_value {n : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates)
    {x : List Bool} (length : x.length = n) {w : ℕ} (live : w < nextWire n C) :
    value D x w = value C x w :=
  value_of_prefix ext (by simpa only [length] using live)

private theorem family_value {k n : ℕ} {C : Circuit} {gate : Fin k → Gate}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C)
    (x : List Bool) (length : x.length = n) (j : Fin k) :
    value (appendFamily C gate) x (nextWire n C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have valid : ∀ a b, b ∈ (gate a).inputs → b < nextWire x.length C := by
    rw [length]
    exact reads
  simpa only [length] using appendFamily_new (C := C) (gate := gate) (x := x) valid j


private def Good (P : Nat → Prop) (N : Nat) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack N C ∧ ∀ g ∈ C.gates, ∀ w ∈ g.inputs, P w

private def Live (P : Nat → Prop) (N : Nat) (C : Circuit) (w : Nat) : Prop :=
  w < nextWire N C ∧ P w

private theorem live_extend {P : Nat → Prop} {N w : Nat} {C D : Circuit}
    (ext : C.gates <+: D.gates) (h : Live P N C w) : Live P N D w :=
  ⟨h.1.trans_le (nextWire_le_of_prefix ext), h.2⟩

private theorem live_new {P : Nat → Prop} {N k : Nat} {C : Circuit} (g : Fin k → Gate)
    (fresh : ∀ w, N ≤ w → P w) (i : Fin k) :
    Live P N (appendFamily C g) (nextWire N C + i.val) := by
  have hi := i.isLt
  constructor
  · rw [appendFamily_nextWire]; omega
  · apply fresh; unfold nextWire; omega

private theorem family_good {P : Nat → Prop} {N k : Nat} {C : Circuit} {g : Fin k → Gate}
    (h : Good P N C) (shape : ∀ i, GateShape (g i))
    (used : ∀ i w, w ∈ (g i).inputs → Live P N C w) : Good P N (appendFamily C g) := by
  refine ⟨appendFamily_fanInTwo h.1 shape, appendFamily_readsBack h.2.1 (fun i w hw => (used i w hw).1), ?_⟩
  intro g' hg w hw
  rcases List.mem_append.mp hg with old | added
  · exact h.2.2 g' old w hw
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp added
    exact (used i w hw).2

private theorem emit_not {X : Type*} {P : Nat → Prop} {N : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (good : Good P N C) {a : Nat} (ha : Live P N C a) :
    ∃ D b, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D b ∧
      D.size = C.size+1 ∧ notCount D = notCount C+1 ∧
      ∀ x, value D (input x) b = !value C (input x) a := by
  let D := appendNot C a
  have ext : C.gates <+: D.gates := appendGate_prefix C _
  refine ⟨D, nextWire N C, ⟨appendNot_fanInTwo good.1, appendNot_readsBack good.2.1 ha.1, ?_⟩,
    ext, ⟨by simp [D, appendNot], fresh _ (by simp [nextWire])⟩,
    appendNot_size .., appendNot_notCount .., ?_⟩
  · intro g hg w hw
    rcases List.mem_append.mp hg with old | added
    · exact good.2.2 g old w hw
    · have eq := List.mem_singleton.mp added
      subst g
      have eq' : w = a := List.mem_singleton.mp hw
      simpa [eq'] using ha.2
  · intro x
    simpa only [len] using appendNot_new C (input x) a

private theorem emit_family {X : Type*} {P : Nat → Prop} {N k : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (good : Good P N C) (conj : Bool)
    (a b : Fin k → Nat) (ha : ∀ i, Live P N C (a i)) (hb : ∀ i, Live P N C (b i)) :
    ∃ D, ∃ w : Fin k → Nat, Good P N D ∧ C.gates <+: D.gates ∧ (∀ i, Live P N D (w i)) ∧
      D.size = C.size+k ∧ notCount D = notCount C ∧
      ∀ x i, value D (input x) (w i) = binaryValue conj (value C (input x) (a i)) (value C (input x) (b i)) := by
  let g (i : Fin k) : Gate := ⟨if conj then .and else .or, [a i,b i]⟩
  have used (i : Fin k) (w : Nat) (hw : w ∈ (g i).inputs) : Live P N C w := by
    change w ∈ [a i,b i] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact ha i
    · exact hb i
  have shape (i : Fin k) : GateShape (g i) := by cases conj <;> simp [GateShape,g]
  refine ⟨appendFamily C g, fun i => nextWire N C + i.val, family_good good shape used,
    appendFamily_prefix .., live_new g fresh, appendFamily_size .., ?_, ?_⟩
  · apply appendFamily_notCount_eq
    intro i
    cases conj <;> simp [g]
  · intro x i
    rw [family_value (fun i w hw => (used i w hw).1) (input x) (len x) i]
    cases conj <;> simp [g,binaryValue,GateOp.eval]

private theorem emit_binary {X : Type*} {P : Nat → Prop} {N : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (good : Good P N C) (conj : Bool)
    {a b : Nat} (ha : Live P N C a) (hb : Live P N C b) :
    ∃ D w, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D w ∧
      D.size = C.size+1 ∧ notCount D = notCount C ∧
      ∀ x, value D (input x) w = binaryValue conj (value C (input x) a) (value C (input x) b) := by
  obtain ⟨D,w,h,e,l,s,c,v⟩ := emit_family input len fresh good (k := 1) conj
    (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
  exact ⟨D,w 0,h,e,l 0,s,c,fun x => v x 0⟩

private theorem mod_half {k j : Nat} (low : k ≤ j) (high : j < 2*k) : j % k = j-k := by
  have e : j = j-k+k := by omega
  calc
    j % k = (j-k+k) % k := congrArg (· % k) e
    _ = j-k := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem fold_level {k j i : Nat} (hk : 0 < k) (hi : i < k-1) (hj : j < 2*k) :
    ((decide (i < j) && !decide (k-1 < j)) || decide (k+i < j)) = decide (i < j % k) := by
  by_cases small : j < k
  · have hp : ¬k-1 < j := by omega
    have hu : ¬k+i < j := by omega
    simp [hp,hu,Nat.mod_eq_of_lt small]
  · have hp : k-1 < j := by omega
    have cmp : (k+i < j) ↔ (i < j-k) := by omega
    simp [hp,mod_half (by omega : k ≤ j) hj,cmp]

private theorem select_level {k j i : Nat} (hk : 0 < k) (hi : i < 2*k) (hj : j < 2*k) :
    (decide (i % k = j % k) &&
      (if i < k then !decide (k-1 < j) else decide (k-1 < j))) = decide (i = j) := by
  by_cases il : i < k <;> by_cases jl : j < k
  · simp [il, Nat.mod_eq_of_lt il, Nat.mod_eq_of_lt jl, show ¬k-1 < j by omega]
  · simp [il, show k-1 < j by omega, show i ≠ j by omega]
  · simp [il, show ¬k-1 < j by omega, show i ≠ j by omega]
  · simp [il, show k-1 < j by omega, mod_half (by omega : k ≤ i) hi,
      mod_half (by omega : k ≤ j) hj, show i-k = j-k ↔ i = j by omega]
 
-- The pulse bank uses one recursive folded thermometer, not two recursive circuits.
set_option maxHeartbeats 700000 in
private theorem oneHot {X : Type*} {P : Nat → Prop} {N : Nat}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (r : Nat) :
    ∀ {C : Circuit} {t : Nat} (good : Good P N C) (ht : Live P N C t)
      (on : ∀ x, value C (input x) t = true)
      (tap : Nat → Nat) (live : ∀ i < 2^r-1, Live P N C (tap i))
      (j : X → Nat) (bound : ∀ x, j x < 2^r)
      (thermo : ∀ x i, i < 2^r-1 → value C (input x) (tap i) = decide (i < j x)),
    ∃ D, ∃ w : Fin (2^r) → Nat, ∃ b v, Good P N D ∧ C.gates <+: D.gates ∧ (∀ i, Live P N D (w i)) ∧
      D.size = C.size+b+v ∧ notCount D = notCount C+v ∧ b ≤ 4*2^r-4 ∧ v ≤ r ∧
      ∀ x (i : Fin (2^r)), value D (input x) (w i) = decide (i.val = j x) := by
  induction r with
  | zero =>
    intro C t good ht on tap live j bound thermo
    refine ⟨C,fun _ => t,0,0,good,List.prefix_refl _,fun _ => ht,by simp,by simp,by decide,le_rfl,?_⟩
    intro x i
    have hi := i.isLt
    have hj := bound x
    rw [on x, decide_eq_true (show i.val = j x by omega)]
  | succ r ih =>
    intro C t good ht on tap live j bound thermo
    let k := 2^r
    have hk : 0 < k := Nat.two_pow_pos _
    have hpow : 2^(r+1) = 2*k := by simp [k,pow_succ,Nat.mul_comm]
    have hp : k-1 < 2^(r+1)-1 := by omega
    obtain ⟨A,np,ga,ea,npl,sa,na,ap⟩ := emit_not input len fresh good (live (k-1) hp)
    have left (i : Fin (k-1)) : Live P N A (tap i.val) :=
      live_extend ea (live _ (by have := i.isLt; omega))
    obtain ⟨B,lo,gb,eb,lol,sb,nb,bp⟩ := emit_family input len fresh ga true
      (fun i : Fin (k-1) => tap i.val) (fun _ => np) left (fun _ => npl)
    have right (i : Fin (k-1)) : Live P N B (tap (k+i.val)) :=
      live_extend (ea.trans eb) (live _ (by have := i.isLt; omega))
    obtain ⟨F,fw,gf,ef,fwl,sf,nf,fp⟩ := emit_family input len fresh gb false lo
      (fun i : Fin (k-1) => tap (k+i.val)) lol right
    have ef0 := ea.trans (eb.trans ef)
    let ft (i : Nat) : Nat := if h : i < k-1 then fw ⟨i,h⟩ else t
    have ftl (i : Nat) (hi : i < k-1) : Live P N F (ft i) := by
      simpa only [ft,dif_pos hi] using fwl ⟨i,hi⟩
    have jbound (x : X) : j x < 2*k := hpow ▸ bound x
    have folded (x : X) (i : Nat) (hi : i < k-1) :
        value F (input x) (ft i) = decide (i < j x % k) := by
      simp only [ft,dite_eq_left hi]
      rw [fp,bp,ap,
        old_value ea (len x) (live i (by omega)).1,
        old_value (ea.trans eb) (len x) (live (k+i) (by omega)).1]
      simp only [thermo x i (by omega), thermo x (k-1) hp, thermo x (k+i) (by omega),binaryValue,ite_true,ite_false,Bool.false_eq_true]
      exact fold_level hk hi (jbound x)
    obtain ⟨R,pulse,b,v,gr,er,pl,sr,nr,br,vr,rp⟩ := ih gf (live_extend ef0 ht)
      (fun x => (old_value ef0 (len x) ht.1).trans (on x)) ft ftl (fun x => j x % k)
      (fun x => Nat.mod_lt _ hk) folded
    have er0 := ef0.trans er
    have ear := eb.trans (ef.trans er)
    let side (i : Fin (2^(r+1))) := if i.val < k then np else tap (k-1)
    let sub (i : Fin (2^(r+1))) : Fin k := ⟨i.val % k, Nat.mod_lt _ hk⟩
    have sideLive (i : Fin (2^(r+1))) : Live P N R (side i) := by
      by_cases hi : i.val < k
      · simpa only [side,if_pos hi] using live_extend ear npl
      · simpa only [side,if_neg hi] using live_extend er0 (live _ hp)
    have sideEval (x : X) (i : Fin (2^(r+1))) :
        value R (input x) (side i) =
          (if i.val < k then !decide (k-1 < j x) else decide (k-1 < j x)) := by
      by_cases hi : i.val < k
      · simp only [side,ite_eq_left hi]
        rw [old_value ear (len x) npl.1,ap,thermo x (k-1) hp]
      · simp only [side,ite_eq_right hi]
        rw [old_value er0 (len x) (live _ hp).1,thermo x (k-1) hp]
    obtain ⟨D,w,gd,ed,wl,sd,nd,dp⟩ := emit_family input len fresh gr true
      (fun i => pulse (sub i)) side (fun i => pl (sub i)) sideLive
    refine ⟨D,w,b+(k-1)+(k-1)+2^(r+1),v+1,gd,er0.trans ed,wl,?_,?_,?_,by omega,?_⟩
    · omega
    · omega
    · change b ≤ 4*k-4 at br
      omega
    · intro x i
      rw [dp,rp,sideEval]
      exact select_level hk (hpow ▸ i.isLt) (jbound x)


private def raw {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool) : List Bool :=
  List.ofFn (fun a : Fin n => decide (a ∈ M)) ++
  List.ofFn (fun g : Fin q => decide (g.val < j.val)) ++ List.ofFn x ++ [false,true]

private theorem raw_len {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
    (raw M j x).length = n+q+(q+1)+2 := by simp [raw,Nat.add_assoc]

private theorem getD_ofFn {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt]

private theorem raw_opt {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Fin n) : (raw M j x).getD i.val false = decide (i ∈ M) := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact getD_ofFn _ i

private theorem raw_mark {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Fin q) : (raw M j x).getD (n+i.val) false = decide (i.val < j.val) := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact getD_ofFn _ i

private theorem raw_data {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Fin (q+1)) : (raw M j x).getD (n+q+i.val) false = x i := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,
    show n+q+i.val-n = q+i.val by omega,
    List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact getD_ofFn _ i

private theorem raw_end {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Nat) : (raw M j x).getD (n+q+(q+1)+i) false = [false,true].getD i false := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,
    show n+q+(q+1)+i-n = q+(q+1)+i by omega,
    List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,
    show q+(q+1)+i-q = q+1+i by omega,
    List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left]

private theorem raw_order {n q : Nat} (M : Finset (Fin n)) {j k : Fin (q+1)}
    {x y : Fin (q+1) → Bool} (jk : j.val ≤ k.val) (xy : x ≤ y) :
    bitOrder (raw M j x) (raw M k y) := by
  refine ⟨by simp [raw_len],?_⟩
  intro i
  by_cases h0 : i < n
  · exact le_of_eq ((raw_opt M j x ⟨i,h0⟩).trans (raw_opt M k y ⟨i,h0⟩).symm)
  by_cases h1 : i < n+q
  · let a : Fin q := ⟨i-n,by omega⟩
    have eq : i = n+a.val := by dsimp [a]; omega
    rw [eq,raw_mark,raw_mark,bool_order]
    simpa only [decide_eq_true_eq] using (fun h : a.val < j.val => h.trans_le jk)
  by_cases h2 : i < n+q+(q+1)
  · let a : Fin (q+1) := ⟨i-(n+q),by omega⟩
    have eq : i = n+q+a.val := by dsimp [a]; omega
    rw [eq,raw_data,raw_data]
    exact xy a
  · have eq : i = n+q+(q+1)+(i-(n+q+(q+1))) := by omega
    conv_lhs => rw [eq,raw_end]
    conv_rhs => rw [eq,raw_end]

private theorem fold_agree (gs : List Gate) (w v : List Bool) (o : Nat) (len : w.length = v.length)
    (agree : ∀ i, (i = o ∨ ∃ g ∈ gs, i ∈ g.inputs) → w.getD i false = v.getD i false) :
    (gs.foldl gateStep w).getD o false = (gs.foldl gateStep v).getD o false := by
  induction gs generalizing w v with
  | nil => exact agree o (Or.inl rfl)
  | cons g gs ih =>
    have same : g.op.eval (g.inputs.map (fun i => w.getD i false)) =
        g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      exact fun i hi => agree i (Or.inr ⟨g,List.mem_cons_self ..,hi⟩)
    simp only [List.foldl_cons]
    apply ih _ _ (by simp [gateStep,len])
    intro i hi
    unfold gateStep
    rw [same]
    by_cases h : i < w.length
    · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (len ▸ h)]
      apply agree
      rcases hi with left | ⟨a,ha,ia⟩
      · exact Or.inl left
      · exact Or.inr ⟨a,List.mem_cons_of_mem _ ha,ia⟩
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]

private def Respects {n : Nat} (S : Finset (Fin n)) (C : Circuit) : Prop :=
  ∀ a : Fin n, (C.output = a.val ∨ ∃ g ∈ C.gates, a.val ∈ g.inputs) → a ∈ S

private theorem erase_missed {n q : Nat} {S M : Finset (Fin n)} {C : Circuit}
    (respects : Respects S C) (miss : ¬(M ∩ S).Nonempty) (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
    C.eval (raw M j x) = C.eval (raw (∅ : Finset (Fin n)) j x) := by
  change (C.wires (raw M j x)).getD C.output false = (C.wires (raw ∅ j x)).getD C.output false
  rw [wires_eq,wires_eq]
  apply fold_agree _ _ _ _ (by simp [raw_len])
  intro i hi
  by_cases h : i < n
  · let a : Fin n := ⟨i,h⟩
    have hs : a ∈ S := respects a (hi.imp Eq.symm id)
    have hm : a ∉ M := fun m => miss ⟨a,Finset.mem_inter.mpr ⟨m,hs⟩⟩
    change (raw M j x).getD a.val false = (raw ∅ j x).getD a.val false
    rw [raw_opt,raw_opt]
    simp [hm]
  · have hm : (List.ofFn (fun a : Fin n => decide (a ∈ M))).length ≤ i :=
      by simpa using Nat.le_of_not_gt h
    have he : (List.ofFn (fun a : Fin n => decide (a ∈ (∅ : Finset (Fin n))))).length ≤ i :=
      by simpa using Nat.le_of_not_gt h
    simp only [raw,List.append_assoc,List.getD_append_right _ _ _ _ hm,
      List.getD_append_right _ _ _ _ he,List.length_ofFn]

private def grade (C : Circuit) (x : List Bool) : Nat := (C.gates.foldl advance (x,0)).2

private theorem grade_bound (C : Circuit) (x : List Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using run_bounded C.gates (x,0) 0 (by change 0 < (1 : Nat); decide)

private theorem grade_order {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → C.eval x ≤ C.eval y) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by simpa [Allowed] using (basis g mem).1
  have initial : consistent (x,0) (y,0) := ⟨le_rfl,fun _ => xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order C.output

private theorem fall {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y)
    (up : C.eval x = true) (down : C.eval y = false) : grade C x < grade C y := by
  obtain ⟨le,eq⟩ := grade_order basis xy
  refine lt_of_le_of_ne le (fun h => ?_)
  have bad := eq h
  rw [up,down] at bad
  exact (by decide : ¬(true ≤ false)) bad

private def Fits {n q : Nat} (E : Finset (Finset (Fin n))) (S : Finset (Fin n)) (b : Nat)
    (cost : Nat → Prop) : Prop :=
  ∃ C : Circuit,
    FanInTwo C ∧ ReadsBack (n+q+(q+1)+2) C ∧
    C.output < n+q+(q+1)+2+C.size ∧ notCount C ≤ b ∧
    cost (C.size - notCount C) ∧ Respects S C ∧
    (∀ M ∈ E, ∀ x, C.eval (raw (q := q) M 0 x) = x 0) ∧
    ∀ (h : Fin q) x, C.eval (raw (∅ : Finset (Fin n)) h.succ x) = x h.succ

private theorem necessity {n r : Nat} {E : Finset (Finset (Fin n))} {S : Finset (Fin n)}
    (fit : Fits (q := 2^r) E S r (fun _ => True)) : ∀ M ∈ E, (M ∩ S).Nonempty := by
  intro M hM
  by_contra miss
  obtain ⟨C,fan,_,_,budget,_,respects,base,ordinary⟩ := fit
  let q := 2^r
  let bits (j : Nat) (i : Fin (q+1)) : Bool := decide (i.val ≤ j)
  have bits_le {i j : Nat} (ij : i ≤ j) : bits i ≤ bits j := by
    intro a
    rw [bool_order]
    simpa only [bits,decide_eq_true_eq] using (fun h : a.val ≤ i => h.trans ij)
  have correct (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
      C.eval (raw (∅ : Finset (Fin n)) j x) = x j := by
    refine Fin.cases ?_ (fun h => ordinary h x) j
    exact (erase_missed respects miss 0 x).symm.trans (base M hM x)
  let g (j : Fin (q+1)) := grade C (raw (∅ : Finset (Fin n)) j (bits j.val))
  have step (j : Fin q) : g j.castSucc < g j.succ := by
    have up : C.eval (raw (∅ : Finset (Fin n)) j.castSucc (bits j.val)) = true := by
      simp [correct,bits]
    have down : C.eval (raw (∅ : Finset (Fin n)) j.succ (bits j.val)) = false := by
      simp [correct,bits]
    have drop := fall fan (raw_order ∅ (show j.castSucc.val ≤ j.succ.val by simp) le_rfl) up down
    have rise := (grade_order fan (raw_order (∅ : Finset (Fin n)) (j := j.succ) (k := j.succ)
      le_rfl (bits_le (show j.val ≤ j.succ.val by simp)))).1
    exact drop.trans_le rise
  have lower (j : Nat) : ∀ hj : j < q+1, j ≤ g ⟨j,hj⟩ := by
    induction j with
    | zero => intro; omega
    | succ j ih =>
      intro hj
      have a : j < q := by omega
      have old := ih (by omega)
      have inc := step ⟨j,a⟩
      change g ⟨j,by omega⟩ < g ⟨j+1,hj⟩ at inc
      omega
  have hi : q < q+1 := by omega
  have upper := (grade_bound C (raw (∅ : Finset (Fin n)) (⟨q,hi⟩ : Fin (q+1)) (bits q))).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) budget)
  exact (Nat.not_lt_of_ge (lower q hi)) upper

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b :=
  le_antisymm ((bool_order _ _).mpr h.mp) ((bool_order _ _).mpr h.mpr)

private theorem emit_any {X : Type*} {P : Nat → Prop} {N : Nat}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (ws : List Nat) :
    ∀ {C : Circuit} {a : Nat} (good : Good P N C) (ha : Live P N C a)
      (hw : ∀ w ∈ ws, Live P N C w),
      ∃ D b, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D b ∧
        D.size = C.size+ws.length ∧ notCount D = notCount C ∧
        ∀ x, value D (input x) b = (value C (input x) a || ws.any (value C (input x))) := by
  induction ws with
  | nil => intro C a good ha hw; exact ⟨C,a,good,List.prefix_refl _,ha,by simp,rfl,by simp⟩
  | cons w ws ih =>
    intro C a good ha hw
    have h := hw w (List.mem_cons_self ..)
    obtain ⟨A,b,g,e,l,s,c,p⟩ := emit_binary input len fresh good false ha h
    obtain ⟨D,d,gd,ed,dl,sd,nd,dp⟩ := ih g l
      (fun i hi => live_extend e (hw i (List.mem_cons_of_mem _ hi)))
    refine ⟨D,d,gd,e.trans ed,dl,by simp [sd,s,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm],nd.trans c,?_⟩
    intro x
    have eq : ws.any (value A (input x)) = ws.any (value C (input x)) := by
      apply bool_ext
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨i,hi,truth⟩
      · exact ⟨i,hi,(old_value e (len x) (hw i (List.mem_cons_of_mem _ hi)).1).symm.trans truth⟩
      · exact ⟨i,hi,(old_value e (len x) (hw i (List.mem_cons_of_mem _ hi)).1).trans truth⟩
    rw [dp,p,eq]
    simp [binaryValue,Bool.or_assoc]

-- Demultiplex the thermometer into pulses, then route the matching data wire.
set_option maxHeartbeats 700000 in
private theorem ordinaryBank {X : Type*} {P : Nat → Prop} {N : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (r : Nat) (good : Good P N C)
    {t f : Nat} (ht : Live P N C t) (hf : Live P N C f)
    (on : ∀ x, value C (input x) t = true) (off : ∀ x, value C (input x) f = false)
    (tap : Nat → Nat) (live : ∀ i < 2^r-1, Live P N C (tap i))
    (j : X → Fin (2^r))
    (thermo : ∀ x i, i < 2^r-1 → value C (input x) (tap i) = decide (i < (j x).val))
    (data : Fin (2^r) → Nat) (dl : ∀ i, Live P N C (data i)) :
    ∃ D w b v, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D w ∧
      D.size = C.size+b+v ∧ notCount D = notCount C+v ∧ b ≤ 6*2^r-4 ∧ v ≤ r ∧
      ∀ x, value D (input x) w = value C (input x) (data (j x)) := by
  obtain ⟨A,p,b,v,ga,ea,pl,sa,na,ba,va,pa⟩ := oneHot input len fresh r good ht on tap live
    (fun x => (j x).val) (fun x => (j x).isLt) thermo
  obtain ⟨B,term,gb,eb,tl,sb,nb,bp⟩ := emit_family input len fresh ga true p data pl
    (fun i => live_extend ea (dl i))
  let ws := List.ofFn term
  obtain ⟨D,out,gd,ed,ol,sd,nd,dp⟩ := emit_any input len fresh ws gb (live_extend (ea.trans eb) hf)
    (fun i hi => by obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hi; exact tl a)
  refine ⟨D,out,b+2*2^r,v,gd,ea.trans (eb.trans ed),ol,?_,by omega,by omega,va,?_⟩
  · have lenW : ws.length = 2^r := List.length_ofFn
    omega
  · intro x
    rw [dp,old_value (ea.trans eb) (len x) hf.1,off x,Bool.false_or]
    have formula (i : Fin (2^r)) : value B (input x) (term i) =
        (decide (i.val = (j x).val) && value C (input x) (data i)) := by
      rw [bp,pa,old_value ea (len x) (dl i).1]
      rfl
    apply bool_ext
    rw [List.any_eq_true]
    constructor
    · rintro ⟨w,hw,truth⟩
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      rw [formula,Bool.and_eq_true,decide_eq_true_eq] at truth
      obtain ⟨h,hit⟩ := truth
      rwa [Fin.ext h] at hit
    · intro hit
      refine ⟨term (j x),List.mem_ofFn.mpr ⟨j x,rfl⟩,?_⟩
      simp [formula,hit]

-- On the promised inputs, the extra branch is either detected by a hit or by one extra NOT.
set_option maxHeartbeats 1000000 in
private theorem sufficiency {n r : Nat} (E : Finset (Finset (Fin n))) (S : Finset (Fin n))
    (extraNot : Bool) (hits : extraNot = false → ∀ M ∈ E, (M ∩ S).Nonempty) :
    Fits (q := 2^r) E S (r+extraNot.toNat) (fun p => p ≤ S.card+6*2^r) := by
  let q := 2^r
  have hq : 0 < q := Nat.two_pow_pos _
  let K := n+q+(q+1)
  let N := K+2
  let X := {p : Finset (Fin n) × Fin (q+1) × (Fin (q+1) → Bool) //
    (p.2.1.val = 0 ∧ p.1 ∈ E) ∨ (0 < p.2.1.val ∧ p.1 = ∅)}
  let input (z : X) := raw z.val.1 z.val.2.1 z.val.2.2
  have len (z : X) : (input z).length = N := raw_len ..
  let P (w : Nat) := ∀ a : Fin n, w = a.val → a ∈ S
  have safe (w : Nat) (h : n ≤ w) : P w := by
    intro a eq
    have := a.isLt
    omega
  have fresh (w : Nat) (h : N ≤ w) : P w := safe w (by dsimp [N,K] at h; omega)
  have wire (C : Circuit) (w : Nat) (lo : n ≤ w) (hi : w < N) : Live P N C w := by
    refine ⟨?_, safe w lo⟩
    unfold nextWire
    omega
  have on (C : Circuit) (z : X) : value C (input z) (K+1) = true := by
    rw [value_input C _ (by rw [len]; dsimp [N]; omega)]
    exact raw_end _ _ _ 1
  have off (C : Circuit) (z : X) : value C (input z) K = false := by
    rw [value_input C _ (by rw [len]; dsimp [N]; omega)]
    exact raw_end _ _ _ 0
  have mark (C : Circuit) (z : X) (i : Fin q) :
      value C (input z) (n+i.val) = decide (i.val < z.val.2.1.val) := by
    rw [value_input C _ (by rw [len]; have := i.isLt; dsimp [N,K]; omega)]
    exact raw_mark _ _ _ _
  have data (C : Circuit) (z : X) (i : Fin (q+1)) : value C (input z) (n+q+i.val) = z.val.2.2 i := by
    rw [value_input C _ (by rw [len]; have := i.isLt; dsimp [N,K]; omega)]
    exact raw_data _ _ _ _
  have opt (C : Circuit) (z : X) (a : Fin n) : value C (input z) a.val = decide (a ∈ z.val.1) := by
    rw [value_input C _ (by rw [len]; have := a.isLt; dsimp [N,K]; omega)]
    exact raw_opt _ _ _ _
  have fLive (C : Circuit) : Live P N C K := wire C K (by dsimp [K]; omega) (by dsimp [N]; omega)
  have tLive (C : Circuit) : Live P N C (K+1) := wire C _ (by dsimp [K]; omega) (by dsimp [N]; omega)
  have firstLive (C : Circuit) : Live P N C n := wire C _ le_rfl (by dsimp [N,K]; omega)
  have first (C : Circuit) (z : X) : value C (input z) n = decide (0 < z.val.2.1.val) :=
    mark C z ⟨0,hq⟩
  have start : Good P N emptyCircuit := ⟨emptyCircuit_fanInTwo,emptyCircuit_readsBack N,by simp [emptyCircuit]⟩
  have extra : ∃ C w m v, Good P N C ∧ Live P N C w ∧
      C.size = m+v ∧ notCount C = v ∧ m ≤ S.card ∧ v ≤ extraNot.toNat ∧
      ∀ z, value C (input z) w = decide (z.val.2.1.val = 0) := by
    cases h : extraNot
    · let ws := S.toList.map Fin.val
      have used (w : Nat) (hw : w ∈ ws) : Live P N emptyCircuit w := by
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
        refine ⟨?_,?_⟩
        · have := a.isLt
          simp [nextWire]; dsimp [N,K]; omega
        · intro b eq
          rwa [← Fin.ext eq,← Finset.mem_toList]
      obtain ⟨C,w,g,_,l,s,c,e⟩ := emit_any input len fresh ws start (fLive _) used
      have card : ws.length = S.card := by simp [ws]
      refine ⟨C,w,S.card,0,g,l,by simpa [card] using s,by simpa using c,le_rfl,Nat.zero_le _,?_⟩
      intro z
      rw [e,off,Bool.false_or]
      apply bool_ext
      simp only [List.any_eq_true,decide_eq_true_eq]
      constructor
      · rintro ⟨i,hi,truth⟩
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
        rw [opt,decide_eq_true_eq] at truth
        rcases z.property with ⟨zero,_⟩ | ⟨_,empty⟩
        · exact zero
        · simp [empty] at truth
      · intro zero
        have mem : z.val.1 ∈ E := by
          rcases z.property with ⟨_,mem⟩ | ⟨pos,_⟩
          · exact mem
          · omega
        obtain ⟨a,ha⟩ := hits h z.val.1 mem
        obtain ⟨am,as⟩ := Finset.mem_inter.mp ha
        exact ⟨a.val,List.mem_map.mpr ⟨a,Finset.mem_toList.mpr as,rfl⟩,by simp [opt,am]⟩
    · obtain ⟨C,w,g,_,l,s,c,e⟩ := emit_not input len fresh start (firstLive _)
      refine ⟨C,w,0,1,g,l,by simpa using s,by simpa using c,Nat.zero_le _,by decide,?_⟩
      intro z
      rw [e,first]
      by_cases zero : z.val.2.1.val = 0
      · simp [zero]
      · simp [zero,show 0 < z.val.2.1.val by omega]
  obtain ⟨C,extraW,m,v,gc,extraL,sc,nc,mc,vc,ec⟩ := extra
  let j (z : X) : Fin q := ⟨z.val.2.1.val-1,by have := z.val.2.1.isLt; omega⟩
  let tap (i : Nat) := n+(i+1)
  have tapLive (i : Nat) (hi : i < q-1) : Live P N C (tap i) :=
    wire C _ (by dsimp [tap]; omega) (by dsimp [tap,N,K]; omega)
  have thermo (z : X) (i : Nat) (hi : i < q-1) :
      value C (input z) (tap i) = decide (i < (j z).val) := by
    have hm := mark C z ⟨i+1,by omega⟩
    change value C (input z) (tap i) = decide (i+1 < z.val.2.1.val) at hm
    rw [hm]
    have e : (i+1 < z.val.2.1.val) ↔ (i < (j z).val) := by dsimp [j]; omega
    simp only [e]
  let dw (i : Fin q) := n+q+i.succ.val
  have dwl (i : Fin q) : Live P N C (dw i) := by
    have hi := i.succ.isLt
    exact wire C _ (by dsimp [dw]; omega) (by dsimp [dw,N,K]; omega)
  obtain ⟨B,bank,b,u,gb,eb,bl,sb,nb,bb,ub,be⟩ := ordinaryBank input len fresh r gc
    (tLive C) (fLive C) (on C) (off C) tap tapLive j thermo dw dwl
  let d0 := n+q+0
  have d0l : Live P N B d0 := wire B _ (by dsimp [d0]; omega) (by dsimp [d0,N,K]; omega)
  obtain ⟨H,hit,gh,eh,hl,sh,nh,he⟩ := emit_binary input len fresh gb true (live_extend eb extraL) d0l
  obtain ⟨A,ordinary,ga,ea,al,sa,na,ae⟩ := emit_binary input len fresh gh true (live_extend eh bl) (firstLive H)
  obtain ⟨D,out,gd,_,ol,sd,nd,de⟩ := emit_binary input len fresh ga false al (live_extend ea hl)
  have computes (z : X) : value D (input z) out = z.val.2.2 z.val.2.1 := by
    have dz : value B (input z) d0 = z.val.2.2 0 := data B z 0
    have bz : value B (input z) bank = z.val.2.2 (j z).succ := (be z).trans (data C z (j z).succ)
    rw [de,ae,old_value ea (len z) hl.1,he,old_value eb (len z) extraL.1,ec,dz,
      old_value eh (len z) bl.1,bz,first]
    by_cases zero : z.val.2.1.val = 0
    · have eq : z.val.2.1 = 0 := Fin.ext zero
      simp [binaryValue,zero,eq]
    · have pos : 0 < z.val.2.1.val := by omega
      have eq : (j z).succ = z.val.2.1 := by
        apply Fin.ext
        change z.val.2.1.val-1+1 = z.val.2.1.val
        omega
      simp [binaryValue,zero,pos,eq]
  refine ⟨withOutput D out,gd.1,gd.2.1,ol.1,?_,?_,?_,?_,?_⟩
  · change notCount D ≤ r+extraNot.toNat
    omega
  · change D.size - notCount D ≤ S.card+6*q
    change b ≤ 6*q-4 at bb
    omega
  · intro a used
    rcases used with outEq | ⟨g,hg,inG⟩
    · exact ol.2 a outEq
    · exact gd.2.2 g hg a.val inG a rfl
  · intro M hM x
    exact computes ⟨(M,0,x),Or.inl ⟨rfl,hM⟩⟩
  · intro h x
    exact computes ⟨(∅,h.succ,x),Or.inr ⟨Nat.succ_pos _,rfl⟩⟩

private theorem relax {n q : Nat} {E : Finset (Finset (Fin n))} {S : Finset (Fin n)} {b : Nat}
    {cost weaker : Nat → Prop} (imp : ∀ p, cost p → weaker p) (fit : Fits (q := q) E S b cost) :
    Fits (q := q) E S b weaker := by
  obtain ⟨C,fan,back,out,neg,pos,use,zero,others⟩ := fit
  exact ⟨C,fan,back,out,neg,imp _ pos,use,zero,others⟩

private theorem solve (n r : Nat) (E : Finset (Finset (Fin n))) :
    (∀ S : Finset (Fin n),
      let hits := ∀ M ∈ E, (M ∩ S).Nonempty
      (Fits (q := 2^r) E S r (fun _ => True) ↔ hits) ∧
      (hits → Fits (q := 2^r) E S r (fun p => p ≤ S.card+6*2^r))) ∧
    Fits (q := 2^r) E ∅ (r+1) (fun p => p ≤ 10*2^r) := by
  constructor
  · intro S
    have build (h : ∀ M ∈ E, (M ∩ S).Nonempty) :
        Fits (q := 2^r) E S r (fun p => p ≤ S.card+6*2^r) := sufficiency E S false (fun _ => h)
    exact ⟨⟨necessity,fun h => relax (fun _ _ => trivial) (build h)⟩,build⟩
  · apply relax
    · intro p (hp : p ≤ (∅ : Finset (Fin n)).card+6*2^r)
      simp only [Finset.card_empty,Nat.zero_add] at hp
      omega
    · exact sufficiency E ∅ true (fun h => Bool.noConfusion h)

private theorem raw_compatible {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
    (List.ofFn (fun a : Fin n => @decide (a ∈ M) (Classical.propDecidable _)) ++
      List.ofFn (fun g : Fin q => @decide (g.val < j.val) (Classical.propDecidable _)) ++
      List.ofFn x ++ [false,true]) = raw M j x := by
  have dec (p : Prop) (a b : Decidable p) : @decide p a = @decide p b :=
    congrArg (fun d => @decide p d) (Subsingleton.elim _ _)
  simp only [raw,List.append_assoc]
  apply congrArg₂ List.append
  · apply congrArg List.ofFn
    funext a
    apply dec
  · apply congrArg (fun l => l ++ (List.ofFn x ++ [false,true]))
    apply congrArg List.ofFn
    funext g
    apply dec

private theorem inter_compatible {n : Nat} (M S : Finset (Fin n)) :
    @min _ (@Finset.instMin (Fin n) (fun a b => Classical.propDecidable (a = b))) M S = M ∩ S := by
  have eq : (fun (a b : Fin n) => Classical.propDecidable (a = b)) = instDecidableEqFin n := by
    funext a b
    exact Subsingleton.elim _ _
  rw [eq]

end PEqualNP.Outside.L_lib_1344_aux

open PEqualNP.Outside.L_lib_1344_aux

theorem PEqualNP.Outside.L_lib_1344 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n r : Nat) (E : Finset (Finset (Fin n))),
      let q := 2^r
      let N := n+q+(q+1)
      let raw := fun (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool) =>
        List.ofFn (fun a : Fin n => decide (a ∈ M)) ++
        List.ofFn (fun g : Fin q => decide (g.val < j.val)) ++ List.ofFn x ++ [false,true]
      let fits := fun (S : Finset (Fin n)) (b : Nat) (cost : Nat → Prop) =>
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+2) C ∧
          C.output < N+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
          cost (C.size - PEqualNP.NotBracket.notCount C) ∧
          (∀ a : Fin n, (C.output = a.val ∨ ∃ g ∈ C.gates, a.val ∈ g.inputs) → a ∈ S) ∧
          (∀ M ∈ E, ∀ x, C.eval (raw M 0 x) = x 0) ∧
          ∀ (h : Fin q) x, C.eval (raw ∅ h.succ x) = x h.succ
      (∀ S : Finset (Fin n),
        let hits := ∀ M ∈ E, (M ∩ S).Nonempty
        (fits S r (fun _ => True) ↔ hits) ∧
          (hits → fits S r (fun p => p ≤ S.card + 6*q))) ∧
      fits ∅ (r+1) (fun p => p ≤ 10*q) := by
  intro n r E
  simpa only [Fits,Respects,← raw_compatible,inter_compatible] using solve n r E
