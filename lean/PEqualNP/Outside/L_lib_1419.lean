import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1419_aux

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

private def M_run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private def M_tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def M_code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := M_tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: M_code gs a
    | _ => M_code gs a

private def M_mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

private theorem M_code_len (gs : List Gate) (w : List Bool) :
    (M_code gs w).length = (gs.filter M_mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [M_code,h,M_mark,List.filter_cons,ih]

private def M_ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

private theorem M_extend_order {x y : List Bool} (w : M_ordered x y) {a b : Bool}
    (ab : a=true → b=true) : M_ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

private theorem M_output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : M_ordered x y) (same : M_code gs x=M_code gs y) :
    M_ordered (M_run gs x) (M_run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change M_ordered (M_run gs (M_tick x g)) (M_run gs (M_tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (M_extend_order w ?_) (by simpa only [M_code,M_tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (M_extend_order w ?_) (by simpa only [M_code,M_tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [M_code,h,List.cons.injEq] at same
      apply ih rest (M_extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

private theorem M_input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    M_ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
private def M_driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + M_driverNumber bs

private theorem M_driver_bound (l : List Bool) : M_driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [M_driverNumber,pow_succ] <;> omega

private theorem M_driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : M_driverNumber a=M_driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := M_driver_bound xs
      have h₂ := M_driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [M_driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

private theorem M_driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : M_ordered a b) :
    M_driverNumber (M_code gs a) ≤ M_driverNumber (M_code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : M_code [g] a=M_code [g] b) : M_ordered (M_tick a g) (M_tick b g) :=
      M_output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [M_code,eq]
      exact ih tailops (growth (by simp [M_code,eq]))
    · simp only [M_code,eq]
      exact ih tailops (growth (by simp [M_code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (M_code gs (M_tick a g)).length=(M_code gs (M_tick b g)).length := by simp [M_code_len]
      change M_driverNumber (M_code (g::gs) a) ≤ M_driverNumber (M_code (g::gs) b)
      simp only [M_code,eq]
      rw [←eq]
      change M_driverNumber (out a :: M_code gs (M_tick a g)) ≤ M_driverNumber (out b :: M_code gs (M_tick b g))
      by_cases same : out a=out b
      · have next : M_ordered (M_tick a g) (M_tick b g) := M_extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [M_driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(M_code gs (M_tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := M_driver_bound (M_code gs (M_tick a g))
        rw [len] at bound
        simp only [M_driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem M_circuit_rank {n : Nat} (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ h : (Fin n → Bool) → Nat, Monotone h ∧ (∀ x, h x < 2^PEqualNP.NotBracket.notCount C) ∧
      ∀ x y, x ≤ y → h x = h y → ∀ w,
        (C.wires (List.ofFn x ++ [false,true])).getD w false=true →
        (C.wires (List.ofFn y ++ [false,true])).getD w false=true := by
  let raw (x : Fin n → Bool) := List.ofFn x ++ [false,true]
  let h (x : Fin n → Bool) := M_driverNumber (M_code C.gates (raw x))
  have ops (g : Gate) (mem : g ∈ C.gates) := (fan g mem).1
  have order {x y : Fin n → Bool} (xy : x ≤ y) : M_ordered (raw x) (raw y) := by
    apply M_input_order
    intro i hi
    have v := xy i
    rw [hi] at v
    exact le_antisymm (by cases y i <;> decide) v
  have size : (C.gates.filter M_mark).length = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases eq : g.op <;> simp [M_mark,eq]
  refine ⟨h,fun x y xy => M_driver_mono _ ops (order xy),?_,?_⟩
  · intro x
    simpa only [h,M_code_len,size] using M_driver_bound (M_code C.gates (raw x))
  · intro x y xy eq w
    have same : M_code C.gates (raw x)=M_code C.gates (raw y) := M_driver_injective (by simp [M_code_len]) eq
    exact (M_output_order ops (order xy) same).2 w

private theorem card_close_inter {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A \ B).card + (A ∩ B).card = A.card := by
  have h : A ∩ B ⊆ A := Finset.inter_subset_left
  have eq : A \ (A ∩ B) = A \ B := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  simpa only [eq] using Finset.card_sdiff_add_card_eq_card h

private theorem same_projection {α : Type*} [DecidableEq α] (A B V carrier : Finset α)
    (ab : A⊆B) (carrierB : B⊆carrier) (a f : Nat)
    (sm : ((B \ A) ∩ V).card≤a+f) :
    ∃ Y Z : Finset α, Y⊆carrier ∧ Z⊆carrier ∧
      (A \ Y).card≤a ∧ (Y \ A).card≤f ∧ (B \ Z).card≤a ∧ (Z \ B).card≤f ∧
      Y ∩ V=Z ∩ V := by
  let E := (B \ A) ∩ V
  obtain ⟨F, Fsub, Fc⟩ := Finset.exists_subset_card_eq (min_le_right f E.card)
  let Y := A ∪ F
  let Z := B \ (E \ F)
  have EB : E⊆B := Finset.inter_subset_left.trans Finset.sdiff_subset
  have FB : F⊆B := Fsub.trans EB
  have clear (x : α) : x∈E ↔ (x∈B ∧ x∉A) ∧ x∈V := by
    simp only [E,Finset.mem_inter,Finset.mem_sdiff]
  have cover (x : α) : x∈A → x∈B := fun h => ab h
  have coverF (x : α) : x∈F → x∈E := fun h => Fsub h
  have overlap : Y∩V=Z∩V := by
    ext x
    have ev := clear x
    have aa := cover x
    have ff := coverF x
    simp only [Y,Z,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff]
    tauto
  have adds : Y \ A=F := by
    ext x
    have ff (h : x∈F) := (clear x).mp (Fsub h)
    simp only [Y,Finset.mem_sdiff,Finset.mem_union]
    tauto
  have dels : B \ Z=E \ F := by
    rw [Finset.sdiff_sdiff_eq_self (Finset.sdiff_subset.trans EB)]
  have ysup : A⊆Y := Finset.subset_union_left
  have zsub : Z⊆B := Finset.sdiff_subset
  refine ⟨Y,Z, (Finset.union_subset ab FB).trans carrierB,zsub.trans carrierB,
    ?_,?_,?_,?_,overlap⟩
  · simp [Finset.sdiff_eq_empty_iff_subset.mpr ysup]
  · rw [adds,Fc]; exact min_le_left _ _
  · rw [dels,Finset.card_sdiff_of_subset Fsub,Fc]
    change E.card≤a+f at sm
    omega
  · simp [Finset.sdiff_eq_empty_iff_subset.mpr zsub]

private theorem distinct_blocks {h : Nat} [DecidableEq Nat]
    (W : Fin (h+1) → Finset Nat) (V : Finset Nat) (mono : Monotone W) (w : Nat)
    (wide : ∀ i : Fin h, w≤((W i.succ \ W i.castSucc) ∩ V).card) :
    ∃ X : Fin h → Finset Nat, (∀ i, X i⊆(W i.succ \ W i.castSucc) ∩ V ∧ (X i).card=w) ∧
      (∀ i j, i≠j → Disjoint (X i) (X j)) ∧
      (Finset.univ.biUnion X).card=h*w ∧ Finset.univ.biUnion X⊆V := by
  have choose_i (i : Fin h) := Finset.exists_subset_card_eq (wide i)
  choose X sub card using choose_i
  have apart {i j : Fin h} (ij : i<j) : Disjoint (X i) (X j) := by
    apply Finset.disjoint_left.mpr
    intro t ti tj
    have inI := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (sub i ti)).1).1
    have outJ := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (sub j tj)).1).2
    exact outJ (mono (show i.val+1≤j.val from ij) inI)
  have dis (i j : Fin h) (ne : i≠j) : Disjoint (X i) (X j) := by
    rcases lt_or_gt_of_ne ne with h | h
    · exact apart h
    · exact (apart h).symm
  refine ⟨X,fun i => ⟨sub i,card i⟩,dis,?_,?_⟩
  · rw [Finset.card_biUnion (fun i _ j _ ne => dis i j ne)]
    simp [card]
  · intro x hx
    obtain ⟨i,_,xi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp (sub i xi)).2

noncomputable def observedBits (r : Nat) (Y : Finset Nat) : List Bool :=
  List.ofFn (fun j : Fin r => @decide (j.val∈Y) (Classical.propDecidable _)) ++ [false,true]

theorem certified_nested_chain {r h : Nat} [DecidableEq Nat]
    (W : Fin (h+1) → Finset Nat) (V : Finset Nat) (mono : Monotone W)
    (b : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (h+1) → Nat)
    (fan : PEqualNP.MetaComplexity.FanInTwo D) (cap : PEqualNP.NotBracket.notCount D≤b)
    (observes : ∀ i j, (D.wires (observedBits r (W i∩V))).getD (out j) false=
      @decide (i=j) (Classical.propDecidable _)) :
    h+1≤2^b := by
  classical
  obtain ⟨score,score_mono,score_bound,score_eq⟩ := M_circuit_rank (n := r) D fan
  let word (i : Fin (h+1)) (p : Fin r) := @decide (p.val ∈ W i∩V) (Classical.propDecidable _)
  have word_true (i : Fin (h+1)) (p : Fin r) : word i p=true ↔ p.val∈W i∩V := by
    simp only [word,decide_eq_true_eq]
  have word_mono : Monotone word := by
    intro i j ij p
    change word i p ≤ word j p
    by_cases hi : p.val ∈ W i∩V
    · have hj : p.val ∈ W j∩V := (Finset.inter_subset_inter_right (mono ij)) hi
      rw [(word_true i p).mpr hi,(word_true j p).mpr hj]
    · have no : word i p=false := by
        cases e : word i p
        · rfl
        · exact (hi ((word_true i p).mp e)).elim
      rw [no]
      cases word j p <;> decide
  have grade_lt (i j : Fin (h+1)) (ij : i<j) : score (word i)<score (word j) := by
    apply lt_of_le_of_ne (score_mono (word_mono ij.le))
    intro eq
    have yes : (D.wires (List.ofFn (word i)++[false,true])).getD (out i) false=true := by
      simpa [observedBits,word] using observes i i
    have no : (D.wires (List.ofFn (word j)++[false,true])).getD (out i) false=false := by
      simpa [observedBits,word,ij.ne.symm] using observes j i
    have flip := score_eq (word i) (word j) (word_mono ij.le) eq (out i) yes
    rw [no] at flip
    contradiction
  let grade (i : Fin (h+1)) : Fin (2^b) := ⟨score (word i),
    (score_bound _).trans_le (Nat.pow_le_pow_right (by decide) cap)⟩
  have grade_mono : StrictMono grade := fun _ _ ij => grade_lt _ _ ij
  simpa using Fintype.card_le_of_injective grade grade_mono.injective

def cntSignal (positive : Bool) (count k : Nat) : Bool :=
  if positive then decide (k≤count) else decide (count<k)

theorem cnt_zero (positive : Bool) (count : Nat) : cntSignal positive count 0=positive := by
  cases positive <;> simp [cntSignal]

theorem cnt_base (positive : Bool) (k : Nat) : cntSignal positive 0 (k+1)=(! positive) := by
  cases positive <;> simp [cntSignal]

theorem cnt_next (positive x : Bool) (c k : Nat) :
    binaryValue (!positive) (binaryValue positive x (cntSignal positive c k))
      (cntSignal positive c (k+1)) =
    cntSignal positive (c+(if x=positive then 1 else 0)) (k+1) := by
  rw [Bool.eq_iff_iff]
  cases positive <;> cases x <;> simp [binaryValue,cntSignal] <;> omega

theorem counter_bank {X : Type*} {N w : Nat} (input : X → List Bool) (len : ∀ x, (input x).length=N)
    (positive : Bool) (on off : Nat) (ins : List Nat) :
    ∀ (C : Circuit), Good (fun _ => True) N C →
      Live (fun _ => True) N C on → Live (fun _ => True) N C off →
      (∀ x, value C (input x) on=true ∧ value C (input x) off=false) →
      (∀ a∈ins, Live (fun _ => True) N C a) →
      ∃ D, ∃ output : Fin w → Nat,
        Good (fun _ => True) N D ∧ C.gates <+: D.gates ∧
        (∀ j, Live (fun _ => True) N D (output j)) ∧
        D.size=C.size+2*w*ins.length ∧ notCount D=notCount C ∧
        ∀ x j, value D (input x) (output j) =
          cntSignal positive (ins.countP (fun a => value C (input x) a==positive)) (j.val+1) := by
  induction ins with
  | nil =>
    intro C good lon loff vals _
    refine ⟨C,fun _ => if positive then off else on,good,List.prefix_refl _,
      fun j => ?_,by simp,rfl,?_⟩
    · cases positive <;> assumption
    · intro x j
      rw [List.countP_nil,cnt_base]
      cases positive <;> simp [vals x]
  | cons a rest ih =>
    intro C good lon loff vals live
    have la := live a (List.mem_cons_self ..)
    obtain ⟨D,prev,gd,cd,lp,sd,nd,sem⟩ := ih C good lon loff vals
      (fun a ha => live a (List.mem_cons_of_mem _ ha))
    let earlier (j : Fin w) := if hj : j.val=0 then (if positive then on else off)
      else prev ⟨j.val-1,by have := j.isLt; omega⟩
    have earlier_live (j : Fin w) : Live (fun _ => True) N D (earlier j) := by
      dsimp [earlier]
      split_ifs <;> first | exact lp _ | exact live_extend cd lon | exact live_extend cd loff
    have fresh (z : Nat) (_ : N≤z) : True := trivial
    obtain ⟨A,mid,ga,da,lm,sa,na,mid_val⟩ :=
      emit_family input len fresh gd positive (fun _ : Fin w => a) earlier
        (fun _ => live_extend cd la) earlier_live
    obtain ⟨B,out,gb,ab,lb,sb,nb,eq⟩ :=
      emit_family input len fresh ga (! positive) mid prev lm (fun j => live_extend da (lp j))
    have cost : B.size=C.size+2*w*(a::rest).length := by simp [sb,sa,sd,Nat.mul_succ]; omega
    refine ⟨B,out,gb,cd.trans (da.trans ab),lb,cost,nb.trans (na.trans nd),?_⟩
    intro x j
    have past : value D (input x) (earlier j) =
        cntSignal positive (rest.countP (fun a => value C (input x) a==positive)) j.val := by
      dsimp only [earlier]
      split_ifs with hj hp
      · rw [hj,cnt_zero]
        exact (old_value cd (len x) lon.1).trans ((vals x).1.trans hp.symm)
      · rw [hj,cnt_zero]
        have eq : positive=false := by cases positive; rfl; exact (hp rfl).elim
        exact (old_value cd (len x) loff.1).trans ((vals x).2.trans eq.symm)
      · rw [sem]
        congr 1
        dsimp
        omega
    rw [eq,mid_val,old_value da (len x) (lp j).1,old_value cd (len x) la.1,past,sem]
    have update :
        (a::rest).countP (fun a => value C (input x) a==positive) =
          rest.countP (fun a => value C (input x) a==positive) +
            (if value C (input x) a=positive then 1 else 0) := by
      simp [List.countP_cons,apply_ite]
    rw [update]
    exact cnt_next _ _ _ _

theorem threshold_family {X : Type*} {N w p : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length=N) (positive : Bool) (on off : Nat) :
    ∀ (h : Nat) (ins : Fin h → List Nat), (∀ i, (ins i).length=w) →
    ∀ (C : Circuit), Good (fun _ => True) N C →
      Live (fun _ => True) N C on → Live (fun _ => True) N C off →
      (∀ x, value C (input x) on=true ∧ value C (input x) off=false) →
      (∀ i a, a∈ins i → Live (fun _ => True) N C a) →
    ∃ D, ∃ output : Fin h → Nat,
      Good (fun _ => True) N D ∧ C.gates <+: D.gates ∧
      (∀ i, Live (fun _ => True) N D (output i)) ∧
      D.size=C.size+2*(p+1)*w*h ∧ notCount D=notCount C ∧
      ∀ x i, value D (input x) (output i) =
        cntSignal positive ((ins i).countP (fun a => value C (input x) a==positive)) (p+1) := by
  intro h
  induction h with
  | zero =>
    intro ins cards C good lon loff vals live
    exact ⟨C,Fin.elim0,good,List.prefix_refl _,fun i => Fin.elim0 i,by simp,rfl,fun _ i => Fin.elim0 i⟩
  | succ h ih =>
    intro ins cards C good lon loff vals live
    obtain ⟨A,head,ag,ca,liveA,sizeA,notA,valA⟩ :=
      counter_bank (w := p+1) input len positive on off (ins 0) C good lon loff vals (live 0)
    have valsA (x : X) : value A (input x) on=true ∧ value A (input x) off=false :=
      ⟨(old_value ca (len x) lon.1).trans (vals x).1,
        (old_value ca (len x) loff.1).trans (vals x).2⟩
    obtain ⟨B,rest,bg,ab,liveB,sizeB,notB,valB⟩ :=
      ih (fun i => ins i.succ) (fun i => cards i.succ) A ag
        (live_extend ca lon) (live_extend ca loff) valsA
        (fun i a ha => live_extend ca (live i.succ a ha))
    let ht := head (Fin.last p)
    have size : B.size=C.size+2*(p+1)*w*(h+1) := by
      rw [sizeB,sizeA,cards 0]
      ring
    refine ⟨B,Fin.cases ht rest,bg,ca.trans ab,?_ ,size,notB.trans notA,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact live_extend ab (liveA (Fin.last p))
      · exact liveB j
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value B (input x) ht = _
        rw [old_value ab (len x) (liveA (Fin.last p)).1]
        exact valA x (Fin.last p)
      · change value B (input x) (rest j) = _
        rw [valB]
        have es : (ins j.succ).countP (fun a => value A (input x) a==positive) =
            (ins j.succ).countP (fun a => value C (input x) a==positive) := by
          apply List.countP_congr
          intro a ha
          rw [old_value ca (len x) (live j.succ a ha).1]
        rw [es]

theorem unary_decode_bank {X : Type*} {N h : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length=N) (b : Nat) (budget : h+1≤2^b)
    (C : Circuit) (good : Good (fun _ => True) N C) (t f : Nat)
    (on : Live (fun _ => True) N C t) (off : Live (fun _ => True) N C f)
    (const : ∀ x, value C (input x) t=true ∧ value C (input x) f=false)
    (rank : X → Fin (h+1)) (tap : Fin h → Nat)
    (live : ∀ i, Live (fun _ => True) N C (tap i))
    (levels : ∀ x i, value C (input x) (tap i)=decide (i.val<(rank x).val)) :
    ∃ D, ∃ out : Fin (h+1) → Nat, Good (fun _ => True) N D ∧ (∀ i, Live (fun _ => True) N D (out i)) ∧
      notCount D≤notCount C+b ∧ D.size-notCount D≤C.size-notCount C+8*(h+1) ∧
      ∀ x i, value D (input x) (out i)=decide (i=rank x) := by
  let ex : ∃ j, h+1≤2^j := ⟨b,budget⟩
  let j := Nat.find ex
  have bound : h+1≤2^j := Nat.find_spec ex
  have jb : j≤b := Nat.find_min' ex budget
  have width : 2^j≤2*(h+1) := by
    cases eq : j with
    | zero => simp <;> omega
    | succ k =>
      have less : 2^k<h+1 := lt_of_not_ge
        (Nat.find_min ex (show k<Nat.find ex from by change k<j; omega))
      rw [pow_succ]
      omega
  let taps (i : Nat) := if hi : i<h then tap ⟨i,hi⟩ else f
  have live_all (i : Nat) (_ : i<2^j-1) : Live (fun _ => True) N C (taps i) := by
    dsimp [taps]
    split_ifs <;> first | exact live _ | exact off
  have observes (x : X) (i : Nat) (_ : i<2^j-1) :
      value C (input x) (taps i)=decide (i<(rank x).val) := by
    dsimp [taps]
    split_ifs with hi
    · exact levels x ⟨i,hi⟩
    · have no : ¬i<(rank x).val := by have := (rank x).isLt; omega
      simpa [no] using (const x).2
  obtain ⟨D,slots,a,v,gd,_,ld,sd,nd,ca,cv,result⟩ :=
    oneHot input len (fun _ _ => trivial) j good on (fun x => (const x).1) taps live_all
      (fun x => (rank x).val) (fun x => (rank x).isLt.trans_le bound) observes
  let idx (i : Fin (h+1)) : Fin (2^j) := ⟨i.val,i.isLt.trans_le bound⟩
  refine ⟨D,slots ∘ idx,gd,fun i => ld _,by omega,?_,?_⟩
  · have leak : a≤8*(h+1) := by omega
    rw [sd,nd]
    omega
  · intro x i
    rw [Function.comp_apply,result]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq,Fin.val_inj,idx])

theorem observed_length (r : Nat) (Y : Finset Nat) : (observedBits r Y).length=r+2 := by
  simp [observedBits]

theorem observed_at (r : Nat) (Y : Finset Nat) (j : Nat) (hj : j<r) :
    (observedBits r Y).getD j false=true ↔ j∈Y := by
  unfold observedBits
  rw [List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD,hj]

theorem observed_true (r : Nat) (Y : Finset Nat) :
    (observedBits r Y).getD (r+1) false=true := by
  unfold observedBits
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem observed_false (r : Nat) (Y : Finset Nat) :
    (observedBits r Y).getD r false=false := by
  unfold observedBits
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem boolean_card (F : Finset Nat) (x : Nat → Bool) (b : Bool) :
    F.toList.countP (fun v => x v==b) = (F.filter (fun v => x v=b)).card := by
  rw [List.countP_eq_length_filter,←List.toFinset_card_of_nodup ((Finset.nodup_toList F).filter _)]
  congr 1
  ext j
  simp

theorem blocks_decode [DecidableEq Nat] {r h a f b : Nat} (W : Fin (h+1) → Finset Nat)
    (mono : Monotone W) (valid : ∀ i, W i⊆Finset.range r) (Pins : Finset Nat)
    (B : Fin h → Finset Nat) (blocks : ∀ i, B i⊆(W i.succ \ W i.castSucc) ∩ Pins)
    (cards : ∀ i, (B i).card=a+f+1) (budget : h+1≤2^b) :
    ∃ D : Circuit, FanInTwo D ∧ ReadsBack (r+2) D ∧ D.output<r+2+D.size ∧
      ∃ out : Fin (h+1) → Nat, (∀ i, out i<r+2+D.size) ∧ notCount D≤b ∧
        D.size-notCount D≤16*(h+1)*((a+f+1)*(min a f+1)+1) ∧
        ∀ i (Y : Finset Nat), Y⊆Finset.range r → (W i \ Y).card≤a → (Y \ W i).card≤f →
          ∀ j, value D (observedBits r (Y∩Pins)) (out j)=
            @decide (i=j) (Classical.propDecidable _) := by
  classical
  let width := a+f+1
  let cut := min a f
  let pos := decide (f≤a)
  let Sample := {p : Fin (h+1) × Finset Nat //
    p.2⊆Finset.range r ∧ (W p.1 \ p.2).card≤a ∧ (p.2 \ W p.1).card≤f}
  let Y (s : Sample) := s.val.2
  let rank (s : Sample) := s.val.1
  let input (s : Sample) := observedBits r (Y s∩Pins)
  have len (s : Sample) : (input s).length=r+2 := observed_length .. 
  have good : Good (fun _=>True) (r+2) emptyCircuit :=
    ⟨emptyCircuit_fanInTwo,emptyCircuit_readsBack _,by simp [emptyCircuit]⟩
  have on : Live (fun _=>True) (r+2) emptyCircuit (r+1) := ⟨by simp [nextWire,emptyCircuit,Circuit.size], trivial⟩
  have off : Live (fun _=>True) (r+2) emptyCircuit r := ⟨by simp [nextWire,emptyCircuit,Circuit.size], trivial⟩
  have const (s : Sample) : value emptyCircuit (input s) (r+1)=true ∧ value emptyCircuit (input s) r=false := by
    rw [value_input _ _ (by rw [len]; omega),value_input _ _ (by rw [len]; omega)]
    exact ⟨observed_true ..,observed_false ..⟩
  have inBounds (i : Fin h) (v : Nat) (hB : v∈B i) : v<r ∧ v∈Pins :=
    ⟨Finset.mem_range.mp (valid _ (Finset.mem_sdiff.mp (Finset.mem_inter.mp (blocks i hB)).1).1),
      (Finset.mem_inter.mp (blocks i hB)).2⟩
  have initial (i : Fin h) (v : Nat) (hv : v∈(B i).toList) :
      Live (fun _=>True) (r+2) emptyCircuit v := by
    have lo := (inBounds i v (Finset.mem_toList.mp hv)).1
    exact ⟨by simp [nextWire,emptyCircuit,Circuit.size]; omega,trivial⟩
  obtain ⟨C,tap,gc,ex,live,cs,cn,sem⟩ :=
    threshold_family (w := width) (p := cut) input len pos (r+1) r h
      (fun i => (B i).toList) (by simp [cards,width]) emptyCircuit good on off const initial
  have lc (s : Sample) : value C (input s) (r+1)=true ∧ value C (input s) r=false :=
    ⟨(old_value ex (len s) on.1).trans (const s).1,
      (old_value ex (len s) off.1).trans (const s).2⟩
  have threshold (s : Sample) (i : Fin h) : value C (input s) (tap i)=decide (i.val<(rank s).val) := by
    let state (v : Nat) := value emptyCircuit (input s) v
    have seen (v : Nat) (hv : v∈B i) : state v=true ↔ v∈Y s := by
      have wb := inBounds i v hv
      rw [show state v=(input s).getD v false from value_input _ _ (by rw [len]; omega)]
      rw [observed_at r (Y s∩Pins) v wb.1]
      simp [wb.2]
    have yes : ((B i).filter (fun v => state v=true))=B i∩Y s := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_inter]
      constructor <;> rintro ⟨hv,bv⟩
      · exact ⟨hv,(seen v hv).mp bv⟩
      · exact ⟨hv,(seen v hv).mpr bv⟩
    have no : ((B i).filter (fun v => state v=false))=B i \ Y s := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_sdiff]
      by_cases hv : v∈B i
      · simp only [hv,true_and]
        cases e : state v <;> simp [←(seen v hv),e]
      · simp [hv]
    have exact_card := card_close_inter (B i) (Y s)
    rw [cards] at exact_card
    have criterion : f+1≤(B i∩Y s).card ↔ i.val<(rank s).val := by
      by_cases left : i.val<(rank s).val
      · have relation : i.succ≤rank s := left
        have sub : B i \ Y s ⊆ W (rank s) \ Y s := by
          apply Finset.sdiff_subset_sdiff ?_ (le_refl _)
          intro v hv
          exact mono relation (Finset.mem_sdiff.mp (Finset.mem_inter.mp (blocks i hv)).1).1
        have gone := (Finset.card_le_card sub).trans s.property.2.1
        simp only [left,iff_true]
        omega
      · have relation : rank s ≤ i.castSucc := Nat.le_of_not_gt left
        have sub : B i∩Y s ⊆ Y s \ W (rank s) := by
          intro v hv
          obtain ⟨vb,vy⟩ := Finset.mem_inter.mp hv
          exact Finset.mem_sdiff.mpr ⟨vy,fun vr =>
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp (blocks i vb)).1).2 (mono relation vr)⟩
        have small := (Finset.card_le_card sub).trans s.property.2.2
        simp only [left,iff_false]
        omega
    rw [sem,boolean_card]
    change cntSignal pos (((B i).filter (fun v => state v=pos)).card) (cut+1)=_
    rw [Bool.eq_iff_iff]
    by_cases fwd : f≤a
    · have positive : pos=true := by simp [pos,fwd]
      simp only [positive,yes,cntSignal,ite_true,decide_eq_true_eq,cut,min_eq_right fwd]
      exact criterion
    · have negative : pos=false := by simp [pos,fwd]
      have cmp : a≤f := (Nat.lt_of_not_ge fwd).le
      simp only [negative,no,cntSignal,Bool.false_eq_true,ite_false,decide_eq_true_eq,cut,min_eq_left cmp]
      rw [←criterion]
      omega
  obtain ⟨D,out,gd,taps,neg,cost,read⟩ :=
    unary_decode_bank input len b budget C gc (r+1) r (live_extend ex on) (live_extend ex off)
      lc rank tap live threshold
  let E := withOutput D 0
  have old_neg : notCount C=0 := by rw [cn]; rfl
  have notCost : notCount E≤b := by change notCount D≤b; simpa [old_neg] using neg
  have mainCost : E.size-notCount E≤16*(h+1)*(width*(cut+1)+1) := by
    change D.size-notCount D≤_
    have baseCost : C.size=2*(cut+1)*width*h := by simpa [emptyCircuit,Circuit.size] using cs
    have growing : (cut+1)*width*h≤(cut+1)*width*(h+1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
    have arithmetic : 2*(cut+1)*width*h+8*(h+1) ≤16*(h+1)*(width*(cut+1)+1) := by
      calc
        _ ≤ 2*((cut+1)*width*(h+1))+8*(h+1) := by rw [Nat.mul_assoc 2,Nat.mul_assoc 2]; exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 growing) _
        _ ≤ 16*((cut+1)*width*(h+1))+16*(h+1) := by gcongr <;> decide
        _ = _ := by ring
    exact (cost.trans (by rw [baseCost,old_neg,Nat.sub_zero]; exact arithmetic))
  refine ⟨E,gd.1,gd.2.1,by change 0<r+2+D.size; omega,out,fun i => (taps i).1,notCost,mainCost,?_⟩
  intro i Z small dZ aZ j
  let sample : Sample := ⟨(i,Z),small,dZ,aZ⟩
  have res := read sample j
  change value E (observedBits r (Z∩Pins)) (out j)=_
  have sem : value E (observedBits r (Z∩Pins)) (out j)=value D (input sample) (out j) := rfl
  rw [sem,res]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,rank,sample]
  exact ⟨fun h => h.symm,fun h => h.symm⟩

end PEqualNP.Outside.L_lib_1419_aux

open PEqualNP.Outside.L_lib_1419_aux

theorem PEqualNP.Outside.L_lib_1419 :
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
  let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true]
  let valid := fun (r : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧ D.output < r+2+D.size
  let fit := fun {m : Nat} (W : Fin m → Finset Nat) (r a f b p : Nat) (V : Finset Nat) =>
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
      (∀ i, out i < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ p ∧
      ∀ i Y, Y ⊆ Finset.range r → near a f (W i) Y →
        ∀ j, (D.wires (bits r (Y ∩ V))).getD (out j) false = decide (i=j)
  ∀ (r h a f b : Nat) (W : Fin (h+1) → Finset Nat) (V : Finset Nat),
    (∀ i, W i ⊆ Finset.range r) → Monotone W → V ⊆ Finset.range r →
    let w := a+f+1
    let cost := 16*(h+1)*(w*(min a f+1)+1)
    ((∃ p, fit W r a f b p V) ↔ h+1 ≤ 2^b ∧
      ∀ i : Fin h, w ≤ ((W i.succ \ W i.castSucc) ∩ V).card) ∧
    ((∃ p, fit W r a f b p V) → h*w ≤ V.card ∧
      ∃ S ⊆ V, S.card=h*w ∧ fit W r a f b cost S) := by
  classical
  intro near bits valid fit r h a f b W V inside mono visible w cost
  letI : DecidableEq Nat := fun x y => Classical.propDecidable (x=y)
  let test := h+1≤2^b ∧ ∀ i : Fin h, w≤((W i.succ \ W i.castSucc)∩V).card
  have needed : (∃ p, fit W r a f b p V) → test := by
    rintro ⟨p,D,out,vD,wires,neg,gates,read⟩
    refine ⟨?_,?_⟩
    · apply certified_nested_chain W V mono b D out vD.1 neg
      intro i j
      exact read i (W i) (inside i) (by simp [near]) j
    · intro i
      by_contra! short
      have few : ((W i.succ \ W i.castSucc)∩V).card≤a+f := by
        change ((W i.succ \ W i.castSucc)∩V).card<a+f+1 at short
        omega
      have adjacent : i.castSucc ≤ i.succ := Nat.le_succ _
      obtain ⟨Y,Z,Yr,Zr,loY,hiY,loZ,hiZ,same⟩ :=
        same_projection (W i.castSucc) (W i.succ) V (Finset.range r)
          (mono adjacent) (inside i.succ) a f few
      have lower := read i.castSucc Y Yr ⟨loY,hiY⟩ i.castSucc
      have upper := read i.succ Z Zr ⟨loZ,hiZ⟩ i.castSucc
      have distinct : i.succ≠i.castSucc := by
        intro e
        have v := congrArg Fin.val e
        simp at v
      change value D (observedBits r (Y∩V)) (out i.castSucc)=_ at lower
      change value D (observedBits r (Z∩V)) (out i.castSucc)=_ at upper
      rw [same] at lower
      have eqTrue : @decide (i.castSucc=i.castSucc) (Classical.propDecidable _)=true :=
        Eq.mpr (@decide_eq_true_eq _ (Classical.propDecidable _)) rfl
      have eq : @decide (i.succ=i.castSucc) (Classical.propDecidable _)=false :=
        (@decide_eq_false_iff_not _ (Classical.propDecidable _)).2 distinct
      rw [eq,lower,eqTrue] at upper
      cases upper
  have decode (Pins : Finset Nat) (X : Fin h → Finset Nat)
      (sub : ∀ i, X i⊆(W i.succ\W i.castSucc)∩Pins)
      (card : ∀ i, (X i).card=w) (capacity : h+1≤2^b) :
      fit W r a f b cost Pins := by
    obtain ⟨D,fan,back,outValid,out,live,neg,gates,value⟩ :=
      blocks_decode W mono inside Pins X sub card capacity
    exact ⟨D,out,⟨fan,back,outValid⟩,live,neg,gates,
      fun i Y Yr nY j => value i Y Yr nY.1 nY.2 j⟩
  constructor
  · refine ⟨needed,?_⟩
    rintro ⟨capacity,wide⟩
    obtain ⟨X,sub,_,_,_⟩ := distinct_blocks W V mono w wide
    exact ⟨cost,decode V X (fun i => (sub i).1) (fun i => (sub i).2) capacity⟩
  · intro solution
    obtain ⟨capacity,wide⟩ := needed solution
    obtain ⟨X,sub,apart,size,cover⟩ := distinct_blocks W V mono w wide
    let S := Finset.univ.biUnion X
    have insideS (i : Fin h) : X i⊆(W i.succ\W i.castSucc)∩S := by
      intro t ht
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ((sub i).1 ht)).1,
        Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩⟩
    have room : h*w≤V.card := size ▸ Finset.card_le_card cover
    exact ⟨room,S,cover,size,
      decode S X insideS (fun i => (sub i).2) capacity⟩
