import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1454_aux

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

private theorem inputs_order {n : ℕ} {x y : Fin n → Bool} (xy : x ≤ y) :
    bitOrder (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  have first : bitOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases inside : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside] using xy ⟨i,inside⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside]
  simpa only [List.append_assoc,List.singleton_append] using
    order_append (order_append first (a := false) (b := false) le_rfl)
      (a := true) (b := true) le_rfl

def grade {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ :=
  (C.gates.foldl advance (List.ofFn x ++ [false,true],0)).2

theorem grade_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using
    run_bounded C.gates (List.ofFn x ++ [false,true],0) 0 (by change 0 < 1; decide)

theorem grade_order {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool} (xy : x ≤ y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i,
      (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
        (C.wires (List.ofFn y ++ [false,true])).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (List.ofFn x ++ [false,true],0) (List.ofFn y ++ [false,true],0) :=
    ⟨le_rfl,fun _ => inputs_order xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order

theorem grade_fall {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool}
    (xy : x ≤ y) (i : ℕ)
    (before : (C.wires (List.ofFn x ++ [false,true])).getD i false = true)
    (after : (C.wires (List.ofFn y ++ [false,true])).getD i false = false) :
    grade C x < grade C y := by
  obtain ⟨order,read⟩ := grade_order basis xy
  refine lt_of_le_of_ne order ?_
  intro eq
  have impossible := read eq i
  rw [before,after] at impossible
  exact (by decide : ¬ (true ≤ false)) impossible

abbrev Reach {n m : ℕ} (P N : (Fin n → Bool) → Fin m → Prop) :
    ℕ → (Fin n → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin n → Bool) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)

theorem no_packing_of_taps {n m r : ℕ} {P N : (Fin n → Bool) → Fin m → Prop}
    {C : Circuit} (tap : Fin m → ℕ) (basis : FanInTwo C) (budget : notCount C ≤ r)
    (fits : ∀ x j,
      let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j) false
      (P x j → w = true) ∧ (N x j → w = false)) :
    ∀ x, ¬ Reach P N (2^r) x := by
  have lower : ∀ k x, Reach P N k x → k ≤ grade C x := by
    intro k
    induction k with
    | zero => intro x _; exact Nat.zero_le _
    | succ k ih =>
      intro x reached
      obtain ⟨u,v,j,history,uv,vx,positive,negative⟩ := reached
      have old := ih u history
      have middle := grade_fall basis uv (tap j) ((fits u j).1 positive) ((fits v j).2 negative)
      have last := (grade_order basis vx).1
      omega
  intro x found
  have high := lower _ x found
  have low := (grade_bound C x).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) budget)
  omega

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

def appendAnd (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.and, [a,b]⟩

def appendOr (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.or, [a,b]⟩

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

theorem withOutput_valid {n : Nat} {C : Circuit} {o : Nat} (valid : o < nextWire n C) :
    (withOutput C o).output < n + (withOutput C o).size := valid

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

@[local simp] theorem appendAnd_size (C : Circuit) (a b : Nat) :
    (appendAnd C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendOr_size (C : Circuit) (a b : Nat) :
    (appendOr C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendNot_size (C : Circuit) (a : Nat) :
    (appendNot C a).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendAnd_notCount (C : Circuit) (a b : Nat) :
    notCount (appendAnd C a b) = notCount C := by simp [appendAnd]

@[local simp] theorem appendOr_notCount (C : Circuit) (a b : Nat) :
    notCount (appendOr C a b) = notCount C := by simp [appendOr]

@[local simp] theorem appendNot_notCount (C : Circuit) (a : Nat) :
    notCount (appendNot C a) = notCount C + 1 := by simp [appendNot]

theorem appendAnd_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendAnd C a b) := appendGate_fanInTwo (g := ⟨.and,[a,b]⟩) basis (by simp) (by simp)

theorem appendOr_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendOr C a b) := appendGate_fanInTwo (g := ⟨.or,[a,b]⟩) basis (by simp) (by simp)

theorem appendNot_fanInTwo {C : Circuit} {a : Nat} (basis : FanInTwo C) :
    FanInTwo (appendNot C a) := appendGate_fanInTwo (g := ⟨.not,[a]⟩) basis (by simp) (by simp)

theorem appendAnd_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendAnd C a b) := by
  apply appendGate_readsBack (g := ⟨.and,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendOr_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendOr C a b) := by
  apply appendGate_readsBack (g := ⟨.or,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendNot_readsBack {n : Nat} {C : Circuit} {a : Nat} (valid : ReadsBack n C)
    (input : a < nextWire n C) : ReadsBack n (appendNot C a) := by
  apply appendGate_readsBack (g := ⟨.not,[a]⟩) valid
  intro i member
  have same : i = a := List.mem_singleton.mp member
  subst i
  exact input

theorem appendAnd_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendAnd C a b) x (nextWire x.length C) = (value C x a && value C x b) := by
  simpa [appendAnd,GateOp.eval] using appendGate_new C ⟨.and,[a,b]⟩ x

theorem appendOr_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendOr C a b) x (nextWire x.length C) = (value C x a || value C x b) := by
  simpa [appendOr,GateOp.eval] using appendGate_new C ⟨.or,[a,b]⟩ x

theorem appendNot_new (C : Circuit) (x : List Bool) (a : Nat) :
    value (appendNot C a) x (nextWire x.length C) = !value C x a := by
  exact appendGate_new C ⟨.not,[a]⟩ x

section Fold

variable {α : Type}

def sfold (F : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun W g => W ++ [F W g]) init

theorem sfold_length (F : List α → Gate → α) (init : List α) (gs : List Gate) :
    (sfold F init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [sfold]
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem sfold_old (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : j < init.length) : (sfold F init gs).getD j d = init.getD j d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih (init ++ [F init g]) (by simp; omega)]
    exact List.getD_append _ _ _ _ hj

theorem sfold_append (F : List α → Gate → α) (init : List α) (gs1 gs2 : List Gate) :
    sfold F init (gs1 ++ gs2) = sfold F (sfold F init gs1) gs2 := by
  simp [sfold, List.foldl_append]

theorem sfold_at (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) (m : ℕ)
    (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init (gs.take m)) gs[m] := by
  have hsplit : gs.take m ++ (gs[m] :: gs.drop (m+1)) = gs := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hlen := sfold_length F init (gs.take m)
  rw [List.length_take, min_eq_left hm.le] at hlen
  conv_lhs => rw [← hsplit]
  rw [sfold_append]
  show (sfold F (sfold F init (gs.take m) ++ [F (sfold F init (gs.take m)) gs[m]])
    (gs.drop (m+1))).getD (init.length + m) d = _
  rw [sfold_old _ _ _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
  simp [hlen]

theorem sfold_gate (F : List α → Gate → α) (d : α)
    (hloc : ∀ W1 W2 g, (∀ j ∈ g.inputs, W1.getD j d = W2.getD j d) → F W1 g = F W2 g)
    (init : List α) (gs : List Gate)
    (hreads : ∀ m (hm : m < gs.length), ∀ j ∈ gs[m].inputs, j < init.length + m)
    (m : ℕ) (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init gs) gs[m] := by
  rw [sfold_at F init gs d m hm]
  apply hloc
  intro j hj
  have hjl := hreads m hm j hj
  have hfull : sfold F init gs = sfold F (sfold F init (gs.take m)) (gs.drop m) := by
    rw [← sfold_append, List.take_append_drop]
  rw [hfull]
  exact (sfold_old F (sfold F init (gs.take m)) (gs.drop m) d
    (by rw [sfold_length, List.length_take, min_eq_left hm.le]; exact hjl)).symm

theorem sfold_beyond (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : init.length + gs.length ≤ j) : (sfold F init gs).getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sfold_length]; exact hj)]
  rfl

end Fold

def Fval (W : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => W.getD i false)

theorem Fval_loc (W1 W2 : List Bool) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j false = W2.getD j false) :
    Fval W1 g = Fval W2 g := by
  unfold Fval
  congr 1
  exact List.map_congr_left h

theorem wires_sfold (C : Circuit) (x : List Bool) : C.wires x = sfold Fval x C.gates := rfl

theorem mem_foldl_union {β : Type} {inst : DecidableEq β} (W : List (Finset β)) (l : List ℕ) (base : Finset β) (z : β) :
    z ∈ l.foldl (fun acc j => acc ∪ W.getD j ∅) base ↔ z ∈ base ∨ ∃ j ∈ l, z ∈ W.getD j ∅ := by
  induction l generalizing base with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, Finset.mem_union]
    constructor
    · rintro ((h | h) | ⟨j', hj', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h⟩
    · rintro (h | ⟨j', hj', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hj' with rfl | h2
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨j', h2, h⟩

noncomputable def Fpath (W : List (Finset (ℕ × ℕ))) (g : Gate) : Finset (ℕ × ℕ) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  (g.inputs.foldl (fun acc j => acc ∪ W.getD j ∅) ∅).image
    (fun z => if g.op = GateOp.and then (z.1+1,z.2) else (z.1,z.2+1))

noncomputable def seedsX {k : ℕ} (i : Fin k) : List (Finset (ℕ × ℕ)) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  List.ofFn (fun j : Fin k => if j=i then ({(0,0)} : Finset (ℕ × ℕ)) else ∅) ++ [∅,∅]

noncomputable def pathsX {k : ℕ} (i : Fin k) (D : Circuit) : Finset (ℕ × ℕ) :=
  (sfold Fpath (seedsX i) D.gates).getD D.output ∅

theorem Fpath_loc (W1 W2 : List (Finset (ℕ × ℕ))) (g : Gate)
    (h : ∀ j ∈ g.inputs, W1.getD j ∅ = W2.getD j ∅) : Fpath W1 g = Fpath W2 g := by
  unfold Fpath
  congr 1
  apply Finset.ext
  intro z
  rw [mem_foldl_union, mem_foldl_union]
  constructor
  · rintro (h1 | ⟨j, hj, h1⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, by rw [← h j hj]; exact h1⟩
  · rintro (h1 | ⟨j, hj, h1⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, by rw [h j hj]; exact h1⟩

theorem mem_Fpath_and (W : List (Finset (ℕ × ℕ))) (g : Gate) (hop : g.op = GateOp.and) (z : ℕ × ℕ) :
    z ∈ Fpath W g ↔ ∃ j ∈ g.inputs, ∃ z' ∈ W.getD j ∅, z = (z'.1+1, z'.2) := by
  unfold Fpath
  simp only [Finset.mem_image, mem_foldl_union, hop, if_true]
  constructor
  · rintro ⟨z', (h | ⟨j, hj, h⟩), rfl⟩
    · simp at h
    · exact ⟨j, hj, z', h, rfl⟩
  · rintro ⟨j, hj, z', h, rfl⟩
    exact ⟨z', Or.inr ⟨j, hj, h⟩, rfl⟩

theorem mem_Fpath_other (W : List (Finset (ℕ × ℕ))) (g : Gate) (hop : g.op ≠ GateOp.and) (z : ℕ × ℕ) :
    z ∈ Fpath W g ↔ ∃ j ∈ g.inputs, ∃ z' ∈ W.getD j ∅, z = (z'.1, z'.2+1) := by
  unfold Fpath
  simp only [Finset.mem_image, mem_foldl_union, hop, if_false]
  constructor
  · rintro ⟨z', (h | ⟨j, hj, h⟩), rfl⟩
    · simp at h
    · exact ⟨j, hj, z', h, rfl⟩
  · rintro ⟨j, hj, z', h, rfl⟩
    exact ⟨z', Or.inr ⟨j, hj, h⟩, rfl⟩

theorem seedsX_length {k : ℕ} (i : Fin k) : (seedsX i).length = k + 2 := by
  simp [seedsX]

theorem seedsX_self {k : ℕ} (i : Fin k) : ((0,0) : ℕ × ℕ) ∈ (seedsX i).getD i.val ∅ := by
  simp [seedsX, List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]

theorem seedsX_mem {k : ℕ} (i : Fin k) (j : ℕ) (z : ℕ × ℕ) (h : z ∈ (seedsX i).getD j ∅) :
    z = (0,0) := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hc : (seedsX i)[j]? with
  | none =>
    rw [hc] at h
    simp at h
  | some S =>
    rw [hc] at h
    have hS : S ∈ seedsX i := List.mem_of_getElem? hc
    simp only [Option.getD_some] at h
    unfold seedsX at hS
    simp only [List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with ⟨j', rfl⟩ | rfl | rfl
    · split_ifs at h <;> simp_all
    · simp at h
    · simp at h

noncomputable def Ftime (c e : ℕ) (W : List ℕ) (g : Gate) : ℕ :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  if g.op = GateOp.not then ((g.inputs.head?.map (fun j => W.getD j 0)).getD 0)
    else g.inputs.foldl (fun v j => max v (W.getD j 0)) 0 + (if g.op = GateOp.and then c else e)

noncomputable def delayX (k c e : ℕ) (D : Circuit) : ℕ :=
  (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates).getD D.output 0

theorem foldl_max_loc (W1 W2 : List ℕ) (l : List ℕ) (h : ∀ j ∈ l, W1.getD j 0 = W2.getD j 0) (b : ℕ) :
    l.foldl (fun v j => max v (W1.getD j 0)) b = l.foldl (fun v j => max v (W2.getD j 0)) b := by
  induction l generalizing b with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    rw [h j (List.mem_cons_self ..)]
    exact ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')) _

theorem le_foldl_max (W : List ℕ) (l : List ℕ) (b : ℕ) :
    b ≤ l.foldl (fun v j => max v (W.getD j 0)) b ∧
      ∀ j ∈ l, W.getD j 0 ≤ l.foldl (fun v j => max v (W.getD j 0)) b := by
  induction l generalizing b with
  | nil => simp
  | cons j rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max b (W.getD j 0))
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | h3
    · exact le_trans (le_max_right _ _) h1
    · exact h2 j' h3

theorem Ftime_loc (c e : ℕ) (W1 W2 : List ℕ) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j 0 = W2.getD j 0) :
    Ftime c e W1 g = Ftime c e W2 g := by
  unfold Ftime
  rw [foldl_max_loc W1 W2 g.inputs h]
  congr 1
  cases hg : g.inputs with
  | nil => rfl
  | cons j rest =>
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact h j (by rw [hg]; exact List.mem_cons_self ..)

theorem Ftime_and (c e : ℕ) (W : List ℕ) (g : Gate) (hop : g.op = GateOp.and) :
    Ftime c e W g = g.inputs.foldl (fun v j => max v (W.getD j 0)) 0 + c := by
  unfold Ftime
  simp [hop]

theorem Ftime_or (c e : ℕ) (W : List ℕ) (g : Gate) (hop : g.op = GateOp.or) :
    Ftime c e W g = g.inputs.foldl (fun v j => max v (W.getD j 0)) 0 + e := by
  unfold Ftime
  simp [hop]

theorem prefix_mono {n : ℕ} {C : Circuit} (basis : FanInTwo C) (hn : notCount C = 0)
    {x y : Fin n → Bool} (hxy : x ≤ y) (i : ℕ) :
    (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
      (C.wires (List.ofFn y ++ [false,true])).getD i false := by
  have h1 := grade_bound C x
  have h2 := grade_bound C y
  rw [hn] at h1 h2
  simp only [pow_zero, Nat.lt_one_iff] at h1 h2
  exact (grade_order basis hxy).2 (by rw [h1, h2]) i

theorem bool_le_false {b : Bool} (h : b ≤ false) : b = false := by
  cases b
  · rfl
  · exact absurd ((bool_order _ _).1 h rfl) (by decide)

theorem bool_true_le {b : Bool} (h : true ≤ b) : b = true := (bool_order _ _).1 h rfl

theorem no_not_gate {D : Circuit} (hn : notCount D = 0) : ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
  intro g hg hop
  have h0 : (D.gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.eq_nil_of_length_eq_zero hn
  have := List.filter_eq_nil_iff.1 h0 g hg
  simp [hop] at this

theorem reads_get {n : ℕ} {D : Circuit} (hr : ReadsBack n D) :
    ∀ m (hm : m < D.gates.length), ∀ j ∈ D.gates[m].inputs, j < n + m := by
  intro m hm j hj
  apply hr m hm j
  show j ∈ (D.gates.getD m ⟨GateOp.or, []⟩).inputs
  rw [List.getD_eq_getElem _ _ hm]
  exact hj

section Core

variable {k : ℕ} [dk : DecidableEq (Fin k)]

def inpX (Y : Finset (Fin k)) : List Bool := List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true]

theorem inpX_length (Y : Finset (Fin k)) : (inpX Y).length = k + 2 := by simp [inpX]

theorem inpX_lt (Y : Finset (Fin k)) (w : ℕ) (h : w < k) :
    (inpX Y).getD w false = decide ((⟨w, h⟩ : Fin k) ∈ Y) := by
  have inside : w < (List.ofFn (fun j : Fin k => decide (j ∈ Y))).length := by simpa using h
  simp only [inpX, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
  simp [List.getElem?_ofFn, h]

theorem inpX_k (Y : Finset (Fin k)) : (inpX Y).getD k false = false := by
  simp [inpX, List.getD_eq_getElem?_getD]

theorem inpX_k1 (Y : Finset (Fin k)) : (inpX Y).getD (k+1) false = true := by
  have outside : (List.ofFn (fun j : Fin k => decide (j ∈ Y))).length ≤ k+1 := by simp
  simp [inpX, List.getD_eq_getElem?_getD, List.getElem?_append_right outside]

def valX (D : Circuit) (w : ℕ) (Y : Finset (Fin k)) : Bool := (D.wires (inpX Y)).getD w false

theorem valX_mono {D : Circuit} (hf : FanInTwo D) (hn : notCount D = 0) (w : ℕ) {Y Y' : Finset (Fin k)}
    (h : Y ⊆ Y') : valX D w Y ≤ valX D w Y' := by
  apply prefix_mono hf hn (x := fun j => decide (j ∈ Y)) (y := fun j => decide (j ∈ Y'))
  intro j
  apply (bool_order _ _).2
  intro hy
  simp only [decide_eq_true_eq] at hy ⊢
  exact h hy

theorem card_union_sdiff_le (Y1 Y2 A : Finset (Fin k)) :
    ((Y1 ∪ Y2) \ A).card ≤ (Y1 \ A).card + (Y2 \ A).card := by
  have hsub : (Y1 ∪ Y2) \ A ⊆ (Y1 \ A) ∪ (Y2 \ A) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem card_sdiff_inter_le (B Y1 Y2 : Finset (Fin k)) :
    (B \ (Y1 ∩ Y2)).card ≤ (B \ Y1).card + (B \ Y2).card := by
  have hsub : B \ (Y1 ∩ Y2) ⊆ (B \ Y1) ∪ (B \ Y2) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem core (A B : Finset (Fin k)) (hAB : A ⊆ B) (D : Circuit) (hf : FanInTwo D)
    (hr : ReadsBack (k+2) D) (hn : notCount D = 0) :
    ∀ w, w < k + 2 + D.size → ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
      (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < P → valX D w Y = false) →
      (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < Q → valX D w Y = true) →
      ∃ i ∈ B \ A, ∃ uv ∈ (sfold Fpath (seedsX i) D.gates).getD w ∅,
        P ≤ 2^uv.1 ∧ Q ≤ 2^uv.2 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw P Q hP hQ hfalse htrue
  have hAA : (A \ A).card < P := by simp; omega
  have hBB : (B \ B).card < Q := by simp; omega
  by_cases hwk : w < k
  · let j : Fin k := ⟨w, hwk⟩
    have hval : ∀ Y : Finset (Fin k), valX D w Y = decide (j ∈ Y) := by
      intro Y
      unfold valX
      rw [wires_sfold, sfold_old _ _ _ _ (by rw [inpX_length]; omega), inpX_lt Y w hwk]
    have hjB : j ∈ B := by
      by_contra hjB
      have := htrue B hAB (subset_refl _) hBB
      rw [hval] at this
      exact hjB (of_decide_eq_true this)
    have hjA : j ∉ A := by
      intro hjA
      have := hfalse A (subset_refl _) hAB hAA
      rw [hval] at this
      exact absurd hjA (of_decide_eq_false this)
    have hP1 : P ≤ 1 := by
      by_contra hP1
      have hs : insert j A \ A = {j} := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h1 h2
        · rintro rfl
          exact ⟨Or.inl rfl, hjA⟩
      have := hfalse (insert j A) (Finset.subset_insert _ _) (Finset.insert_subset hjB hAB)
        (by rw [hs, Finset.card_singleton]; omega)
      rw [hval] at this
      exact absurd (Finset.mem_insert_self j A) (of_decide_eq_false this)
    have hQ1 : Q ≤ 1 := by
      by_contra hQ1
      have hs : B \ B.erase j = {j} := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩
          by_contra h3
          exact h2 ⟨h3, h1⟩
        · rintro rfl
          exact ⟨hjB, fun h => h.1 rfl⟩
      have hAe : A ⊆ B.erase j := by
        intro x hx
        exact Finset.mem_erase.2 ⟨fun h => hjA (h ▸ hx), hAB hx⟩
      have := htrue (B.erase j) hAe (Finset.erase_subset _ _) (by rw [hs, Finset.card_singleton]; omega)
      rw [hval] at this
      exact absurd (of_decide_eq_true this) (Finset.notMem_erase j B)
    refine ⟨j, Finset.mem_sdiff.2 ⟨hjB, hjA⟩, (0,0), ?_, by simpa using hP1, by simpa using hQ1⟩
    rw [sfold_old _ _ _ _ (by rw [seedsX_length]; omega)]
    exact seedsX_self j
  by_cases hwk2 : w < k + 2
  · exfalso
    have hval : ∀ Y : Finset (Fin k), valX D w Y = (inpX Y).getD w false := by
      intro Y
      unfold valX
      rw [wires_sfold, sfold_old _ _ _ _ (by rw [inpX_length]; omega)]
    by_cases h1 : w = k + 1
    · have := hfalse A (subset_refl _) hAB hAA
      rw [hval, h1, inpX_k1] at this
      exact absurd this (by decide)
    · have h2 : w = k := by omega
      have := htrue B hAB (subset_refl _) hBB
      rw [hval, h2, inpX_k] at this
      exact absurd this (by decide)
  obtain ⟨m, rfl⟩ : ∃ m, w = k + 2 + m := ⟨w - (k+2), by omega⟩
  have hm : m < D.gates.length := by
    have : D.size = D.gates.length := rfl
    omega
  have hreads := reads_get hr
  have hgin : ∀ j ∈ D.gates[m].inputs, j < k + 2 + m := hreads m hm
  have hgval : ∀ Y : Finset (Fin k), valX D (k+2+m) Y = Fval (D.wires (inpX Y)) D.gates[m] := by
    intro Y
    unfold valX
    rw [wires_sfold]
    have := sfold_gate Fval false Fval_loc (inpX Y) D.gates
      (fun m' hm' j hj => by rw [inpX_length]; exact hreads m' hm' j hj) m hm
    rw [inpX_length] at this
    exact this
  have hgpath : ∀ i : Fin k, (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅ =
      Fpath (sfold Fpath (seedsX i) D.gates) D.gates[m] := by
    intro i
    have := sfold_gate Fpath ∅ Fpath_loc (seedsX i) D.gates
      (fun m' hm' j hj => by rw [seedsX_length]; exact hreads m' hm' j hj) m hm
    rw [seedsX_length] at this
    exact this
  have hgshape := hf D.gates[m] (List.getElem_mem hm)
  have hgnot := no_not_gate hn D.gates[m] (List.getElem_mem hm)
  obtain ⟨hop, hlen⟩ := hgshape
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hop2 : D.gates[m].op = GateOp.and ∨ D.gates[m].op = GateOp.or := by
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hgnot
  have hvY : ∀ j ∈ D.gates[m].inputs, ∀ Y : Finset (Fin k), (D.wires (inpX Y)).getD j false = valX D j Y :=
    fun _ _ _ => rfl
  have hPh : 1 ≤ (P+1)/2 := by omega
  have hQh : 1 ≤ (Q+1)/2 := by omega
  rcases hop2 with hand | hor
  ·
    have hev : ∀ Y : Finset (Fin k), valX D (k+2+m) Y = (D.gates[m].inputs.map fun j => valX D j Y).all id := by
      intro Y
      rw [hgval, Fval, hand]
      rfl
    have hpath : ∀ (i : Fin k) (u : ℕ), u ∈ D.gates[m].inputs → ∀ z ∈ (sfold Fpath (seedsX i) D.gates).getD u ∅,
        (z.1+1, z.2) ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅ := by
      intro i u hu z hz
      rw [hgpath, mem_Fpath_and _ _ hand]
      exact ⟨u, hu, z, hz, rfl⟩
    have hT : ∀ u ∈ D.gates[m].inputs, ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < Q → valX D u Y = true := by
      intro u hu Y h1 h2 h3
      have := htrue Y h1 h2 h3
      rw [hev, List.all_eq_true] at this
      exact this _ (List.mem_map.2 ⟨u, hu, rfl⟩)
    have lift : ∀ u ∈ D.gates[m].inputs, ∀ P', 1 ≤ P' → P ≤ 2*P' →
        (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < P' → valX D u Y = false) →
        ∃ i ∈ B \ A, ∃ uv ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅,
          P ≤ 2^uv.1 ∧ Q ≤ 2^uv.2 := by
      intro u hu P' hP' hPP hF
      obtain ⟨i, hi, z, hz, h1, h2⟩ := ih u (hgin u hu) (by have := hgin u hu; omega) P' Q hP' hQ hF (hT u hu)
      refine ⟨i, hi, (z.1+1, z.2), hpath i u hu z hz, ?_, h2⟩
      rw [pow_succ]
      omega
    match hgi : D.gates[m].inputs, hlen with
    | [], _ =>
      exfalso
      have := hfalse A (subset_refl _) hAB hAA
      rw [hev, hgi] at this
      simp at this
    | [u], _ =>
      have hu : u ∈ D.gates[m].inputs := by rw [hgi]; simp
      apply lift u hu P hP (by omega)
      intro Y h1 h2 h3
      have := hfalse Y h1 h2 h3
      rw [hev, hgi] at this
      simpa using this
    | [u1, u2], _ =>
      have hu1 : u1 ∈ D.gates[m].inputs := by rw [hgi]; simp
      have hu2 : u2 ∈ D.gates[m].inputs := by rw [hgi]; simp
      by_cases hc1 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < (P+1)/2 → valX D u1 Y = false
      · exact lift u1 hu1 _ hPh (by omega) hc1
      by_cases hc2 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < (P+1)/2 → valX D u2 Y = false
      · exact lift u2 hu2 _ hPh (by omega) hc2
      exfalso
      push_neg at hc1 hc2
      obtain ⟨Y1, a1, b1, c1, d1⟩ := hc1
      obtain ⟨Y2, a2, b2, c2, d2⟩ := hc2
      have hY : ((Y1 ∪ Y2) \ A).card < P := by
        have := card_union_sdiff_le Y1 Y2 A
        omega
      have := hfalse (Y1 ∪ Y2) (a1.trans Finset.subset_union_left) (Finset.union_subset b1 b2) hY
      rw [hev, hgi] at this
      have e1 := bool_true_le ((show true = valX D u1 Y1 by simpa using d1.symm) ▸
        valX_mono hf hn u1 (Finset.subset_union_left (s₂ := Y2)))
      have e2 := bool_true_le ((show true = valX D u2 Y2 by simpa using d2.symm) ▸
        valX_mono hf hn u2 (Finset.subset_union_right (s₁ := Y1)))
      simp [e1, e2] at this
    | _ :: _ :: _ :: _, hl =>
      simp at hl
  ·
    have hand' : D.gates[m].op ≠ GateOp.and := by rw [hor]; intro h; cases h
    have hev : ∀ Y : Finset (Fin k), valX D (k+2+m) Y = (D.gates[m].inputs.map fun j => valX D j Y).any id := by
      intro Y
      rw [hgval, Fval, hor]
      rfl
    have hpath : ∀ (i : Fin k) (u : ℕ), u ∈ D.gates[m].inputs → ∀ z ∈ (sfold Fpath (seedsX i) D.gates).getD u ∅,
        (z.1, z.2+1) ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅ := by
      intro i u hu z hz
      rw [hgpath, mem_Fpath_other _ _ hand']
      exact ⟨u, hu, z, hz, rfl⟩
    have hF : ∀ u ∈ D.gates[m].inputs, ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < P → valX D u Y = false := by
      intro u hu Y h1 h2 h3
      have := hfalse Y h1 h2 h3
      rw [hev] at this
      have h4 := List.any_eq_false.1 this
      have h5 := h4 _ (List.mem_map.2 ⟨u, hu, rfl⟩)
      simpa using h5
    have lift : ∀ u ∈ D.gates[m].inputs, ∀ Q', 1 ≤ Q' → Q ≤ 2*Q' →
        (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < Q' → valX D u Y = true) →
        ∃ i ∈ B \ A, ∃ uv ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅,
          P ≤ 2^uv.1 ∧ Q ≤ 2^uv.2 := by
      intro u hu Q' hQ' hQQ hT
      obtain ⟨i, hi, z, hz, h1, h2⟩ := ih u (hgin u hu) (by have := hgin u hu; omega) P Q' hP hQ' (hF u hu) hT
      refine ⟨i, hi, (z.1, z.2+1), hpath i u hu z hz, h1, ?_⟩
      show Q ≤ 2^(z.2+1)
      rw [pow_succ]
      omega
    match hgi : D.gates[m].inputs, hlen with
    | [], _ =>
      exfalso
      have := htrue B hAB (subset_refl _) hBB
      rw [hev, hgi] at this
      simp at this
    | [u], _ =>
      have hu : u ∈ D.gates[m].inputs := by rw [hgi]; simp
      apply lift u hu Q hQ (by omega)
      intro Y h1 h2 h3
      have := htrue Y h1 h2 h3
      rw [hev, hgi] at this
      simpa using this
    | [u1, u2], _ =>
      have hu1 : u1 ∈ D.gates[m].inputs := by rw [hgi]; simp
      have hu2 : u2 ∈ D.gates[m].inputs := by rw [hgi]; simp
      by_cases hc1 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < (Q+1)/2 → valX D u1 Y = true
      · exact lift u1 hu1 _ hQh (by omega) hc1
      by_cases hc2 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < (Q+1)/2 → valX D u2 Y = true
      · exact lift u2 hu2 _ hQh (by omega) hc2
      exfalso
      push_neg at hc1 hc2
      obtain ⟨Y1, a1, b1, c1, d1⟩ := hc1
      obtain ⟨Y2, a2, b2, c2, d2⟩ := hc2
      have hY : (B \ (Y1 ∩ Y2)).card < Q := by
        have := card_sdiff_inter_le B Y1 Y2
        omega
      have := htrue (Y1 ∩ Y2) (Finset.subset_inter a1 a2) (Finset.inter_subset_left.trans b1) hY
      rw [hev, hgi] at this
      have e1 := bool_le_false ((show valX D u1 Y1 = false by simpa using d1) ▸
        valX_mono hf hn u1 (Finset.inter_subset_left (s₂ := Y2)))
      have e2 := bool_le_false ((show valX D u2 Y2 = false by simpa using d2) ▸
        valX_mono hf hn u2 (Finset.inter_subset_right (s₁ := Y1)))
      simp [e1, e2] at this
    | _ :: _ :: _ :: _, hl =>
      simp at hl

theorem delay_ge (D : Circuit) (hr : ReadsBack (k+2) D) (hn : notCount D = 0) (hf : FanInTwo D)
    (c e : ℕ) (i : Fin k) : ∀ w, ∀ z ∈ (sfold Fpath (seedsX i) D.gates).getD w ∅,
      c*z.1 + e*z.2 ≤ (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates).getD w 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro z hz
  by_cases hw : w < k + 2
  · rw [sfold_old _ _ _ _ (by rw [seedsX_length]; exact hw)] at hz
    have := seedsX_mem i w z hz
    subst this
    simp
  by_cases hw2 : w < k + 2 + D.gates.length
  · obtain ⟨m, rfl⟩ : ∃ m, w = k + 2 + m := ⟨w - (k+2), by omega⟩
    have hm : m < D.gates.length := by omega
    have hreads := reads_get hr
    have hgp := sfold_gate Fpath ∅ Fpath_loc (seedsX i) D.gates
      (fun m' hm' j hj => by rw [seedsX_length]; exact hreads m' hm' j hj) m hm
    rw [seedsX_length] at hgp
    have hgt := sfold_gate (Ftime c e) 0 (Ftime_loc c e) (List.replicate (k+2) 0) D.gates
      (fun m' hm' j hj => by rw [List.length_replicate]; exact hreads m' hm' j hj) m hm
    rw [List.length_replicate] at hgt
    rw [hgt]
    rw [hgp] at hz
    obtain ⟨hop, _⟩ := hf D.gates[m] (List.getElem_mem hm)
    have hgnot := no_not_gate hn D.gates[m] (List.getElem_mem hm)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor | hnot
    · rw [mem_Fpath_and _ _ hand] at hz
      obtain ⟨j, hj, z', hz', rfl⟩ := hz
      have h1 := ih j (by have := hreads m hm j hj; omega) z' hz'
      have h2 := (le_foldl_max (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates) D.gates[m].inputs 0).2 j hj
      rw [Ftime_and _ _ _ _ hand]
      nlinarith
    · rw [mem_Fpath_other _ _ (by rw [hor]; intro h; cases h)] at hz
      obtain ⟨j, hj, z', hz', rfl⟩ := hz
      have h1 := ih j (by have := hreads m hm j hj; omega) z' hz'
      have h2 := (le_foldl_max (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates) D.gates[m].inputs 0).2 j hj
      rw [Ftime_or _ _ _ _ hor]
      nlinarith
    · exact absurd hnot hgnot
  · rw [sfold_beyond _ _ _ _ (by rw [seedsX_length]; omega)] at hz
    simp at hz

end Core

section Build

variable {α : Type}

def semC (F : List α → Gate → α) (init : List α) (d : α) (C : Circuit) (w : ℕ) : α :=
  (sfold F init C.gates).getD w d

theorem semC_prefix (F : List α → Gate → α) (init : List α) (d : α) {C C' : Circuit}
    (hp : C.gates <+: C'.gates) {w : ℕ} (hw : w < init.length + C.size) :
    semC F init d C' w = semC F init d C w := by
  obtain ⟨rest, hr⟩ := hp
  unfold semC
  rw [← hr, sfold_append]
  exact sfold_old _ _ _ _ (by rw [sfold_length]; exact hw)

theorem semC_append (F : List α → Gate → α) (init : List α) (d : α) (C : Circuit) (g : Gate) :
    semC F init d (appendGate C g) (init.length + C.size) = F (sfold F init C.gates) g := by
  unfold semC appendGate
  simp only
  rw [sfold_append]
  have hl : init.length + C.size = (sfold F init C.gates).length := by
    rw [sfold_length]; rfl
  rw [hl]
  simp [sfold, List.getD_eq_getElem?_getD]

theorem semC_empty (F : List α → Gate → α) (init : List α) (d : α) (w : ℕ) :
    semC F init d emptyCircuit w = init.getD w d := rfl

def tfold (f : α → α → α) (v : ℕ → α) : ℕ → List ℕ → α
  | 0, L => v (L.headD 0)
  | h+1, L => if L.length ≤ 2^h then tfold f v h L else
      f (tfold f v h (L.take (2^h))) (tfold f v h (L.drop (2^h)))

theorem headD_mem {L : List ℕ} (h : L ≠ []) : L.headD 0 ∈ L := by
  cases L with
  | nil => exact absurd rfl h
  | cons x rest => simp

theorem split_ne {L : List ℕ} (h : ℕ) (hl : ¬ L.length ≤ 2^h) :
    L.take (2^h) ≠ [] ∧ L.drop (2^h) ≠ [] := by
  have hp : 0 < 2^h := pow_pos (by norm_num) h
  constructor
  · intro he
    rw [List.take_eq_nil_iff] at he
    rcases he with he | he
    · omega
    · rw [he] at hl; simp at hl
  · intro he
    rw [List.drop_eq_nil_iff] at he
    exact hl he

theorem split_len {L : List ℕ} (h : ℕ) (hl : L.length ≤ 2^(h+1)) :
    (L.take (2^h)).length ≤ 2^h ∧ (L.drop (2^h)).length ≤ 2^h := by
  rw [pow_succ] at hl
  simp only [List.length_take, List.length_drop]
  constructor
  · exact min_le_left _ _
  · omega

theorem tfold_congr (f : α → α → α) (h : ℕ) : ∀ (L : List ℕ) (v v' : ℕ → α), L ≠ [] →
    (∀ j ∈ L, v j = v' j) → tfold f v h L = tfold f v' h L := by
  induction h with
  | zero =>
    intro L v v' hne hv
    exact hv _ (headD_mem hne)
  | succ h ih =>
    intro L v v' hne hv
    unfold tfold
    split_ifs with hl
    · exact ih L v v' hne hv
    · obtain ⟨h1, h2⟩ := split_ne h hl
      rw [ih _ v v' h1 (fun j hj => hv j (List.mem_of_mem_take hj)),
        ih _ v v' h2 (fun j hj => hv j (List.mem_of_mem_drop hj))]

theorem tfold_le (c : ℕ) (h : ℕ) : ∀ (L : List ℕ) (v : ℕ → ℕ) (M : ℕ), L ≠ [] →
    (∀ j ∈ L, v j ≤ M) → tfold (fun x y => max x y + c) v h L ≤ M + h * c := by
  induction h with
  | zero =>
    intro L v M hne hv
    simpa [tfold] using hv _ (headD_mem hne)
  | succ h ih =>
    intro L v M hne hv
    unfold tfold
    split_ifs with hl
    · have := ih L v M hne hv
      nlinarith
    · obtain ⟨h1, h2⟩ := split_ne h hl
      have a1 := ih _ v M h1 (fun j hj => hv j (List.mem_of_mem_take hj))
      have a2 := ih _ v M h2 (fun j hj => hv j (List.mem_of_mem_drop hj))
      have : max (tfold (fun x y => max x y + c) v h (L.take (2^h)))
          (tfold (fun x y => max x y + c) v h (L.drop (2^h))) ≤ M + h * c := max_le a1 a2
      nlinarith

theorem tfold_all (h : ℕ) : ∀ (L : List ℕ) (v : ℕ → Bool), L ≠ [] → L.length ≤ 2^h →
    tfold (fun x y => x && y) v h L = L.all v := by
  induction h with
  | zero =>
    intro L v hne hl
    match L, hne, hl with
    | [x], _, _ => simp [tfold]
    | [], hne, _ => exact absurd rfl hne
    | _ :: _ :: _, _, hl => simp at hl
  | succ h ih =>
    intro L v hne hl
    unfold tfold
    split_ifs with hl2
    · exact ih L v hne hl2
    · obtain ⟨h1, h2⟩ := split_ne h hl2
      obtain ⟨l1, l2⟩ := split_len h hl
      rw [ih _ v h1 l1, ih _ v h2 l2]
      conv_rhs => rw [← List.take_append_drop (2^h) L]
      rw [List.all_append]

theorem tfold_any (h : ℕ) : ∀ (L : List ℕ) (v : ℕ → Bool), L ≠ [] → L.length ≤ 2^h →
    tfold (fun x y => x || y) v h L = L.any v := by
  induction h with
  | zero =>
    intro L v hne hl
    match L, hne, hl with
    | [x], _, _ => simp [tfold]
    | [], hne, _ => exact absurd rfl hne
    | _ :: _ :: _, _, hl => simp at hl
  | succ h ih =>
    intro L v hne hl
    unfold tfold
    split_ifs with hl2
    · exact ih L v hne hl2
    · obtain ⟨h1, h2⟩ := split_ne h hl2
      obtain ⟨l1, l2⟩ := split_len h hl
      rw [ih _ v h1 l1, ih _ v h2 l2]
      conv_rhs => rw [← List.take_append_drop (2^h) L]
      rw [List.any_append]

def bt (op : GateOp) (n : ℕ) : ℕ → Circuit → List ℕ → Circuit × ℕ
  | 0, C, L => (C, L.headD 0)
  | h+1, C, L => if L.length ≤ 2^h then bt op n h C L else
      ((appendGate (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1
        ⟨op, [(bt op n h C (L.take (2^h))).2, (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).2]⟩),
        n + (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1.size)

def BinForm (op : GateOp) (F : List α → Gate → α) (d : α) (f : α → α → α) : Prop :=
  ∀ W a b, F W ⟨op, [a, b]⟩ = f (W.getD a d) (W.getD b d)

theorem bt_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (n : ℕ) (h : ℕ) :
    ∀ (C : Circuit) (L : List ℕ), L ≠ [] → L.length ≤ 2^h → (∀ j ∈ L, j < n + C.size) →
      C.gates <+: (bt op n h C L).1.gates ∧ (bt op n h C L).1.output = C.output ∧
      (bt op n h C L).2 < n + (bt op n h C L).1.size ∧
      (FanInTwo C → FanInTwo (bt op n h C L).1) ∧ (ReadsBack n C → ReadsBack n (bt op n h C L).1) ∧
      notCount (bt op n h C L).1 = notCount C ∧
      (∀ (β : Type) (F : List β → Gate → β) (init : List β) (d : β) (f : β → β → β),
        init.length = n → BinForm op F d f →
        semC F init d (bt op n h C L).1 (bt op n h C L).2 = tfold f (semC F init d C) h L) := by
  induction h with
  | zero =>
    intro C L hne hl hj
    refine ⟨List.prefix_refl _, rfl, hj _ (headD_mem hne), id, id, rfl, ?_⟩
    intro β F init d f _ _
    rfl
  | succ h ih =>
    intro C L hne hl hj
    by_cases hl2 : L.length ≤ 2^h
    · have e : bt op n (h+1) C L = bt op n h C L := by
        simp only [bt, if_pos hl2]
      rw [e]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih C L hne hl2 hj
      refine ⟨a1, a2, a3, a4, a5, a6, ?_⟩
      intro β F init d f hi hb
      rw [a7 β F init d f hi hb]
      simp only [tfold, if_pos hl2]
    · have e : bt op n (h+1) C L = ((appendGate (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1
        ⟨op, [(bt op n h C (L.take (2^h))).2, (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).2]⟩),
        n + (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1.size) := by
        simp only [bt, if_neg hl2]
      rw [e]
      obtain ⟨h1, h2⟩ := split_ne h hl2
      obtain ⟨l1, l2⟩ := split_len h hl
      obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := ih C (L.take (2^h)) h1 l1
        (fun j hj' => hj j (List.mem_of_mem_take hj'))
      set C1 := (bt op n h C (L.take (2^h))).1 with hC1
      set w1 := (bt op n h C (L.take (2^h))).2 with hw1
      have hs1 : C.size ≤ C1.size := b1.length_le
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := ih C1 (L.drop (2^h)) h2 l2
        (fun j hj' => by have := hj j (List.mem_of_mem_drop hj'); omega)
      set C2 := (bt op n h C1 (L.drop (2^h))).1 with hC2
      set w2 := (bt op n h C1 (L.drop (2^h))).2 with hw2
      have hs2 : C1.size ≤ C2.size := c1.length_le
      have hopset : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
        rcases hop with rfl | rfl <;> simp
      have hnot : op ≠ GateOp.not := by
        rcases hop with rfl | rfl <;> (intro hh; cases hh)
      refine ⟨b1.trans (c1.trans (appendGate_prefix _ _)), by rw [appendGate_output, c2, b2], ?_,
        fun hf => appendGate_fanInTwo (c4 (b4 hf)) hopset (by simp), ?_, ?_, ?_⟩
      · rw [appendGate_size]; omega
      · intro hr
        apply appendGate_readsBack (c5 (b5 hr))
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        unfold nextWire
        rcases hi with rfl | rfl
        · omega
        · exact c3
      · rw [appendGate_notCount, c6, b6]
        simp [hnot]
      · intro β F init d f hi hb
        have := semC_append F init d C2 ⟨op, [w1, w2]⟩
        rw [hi] at this
        rw [this, hb]
        show f (semC F init d C2 w1) (semC F init d C2 w2) = _
        rw [semC_prefix F init d c1 (by rw [hi]; exact b3), b7 β F init d f hi hb,
          c7 β F init d f hi hb,
          tfold_congr f h _ (semC F init d C1) (semC F init d C) h2
            (fun j hj' => semC_prefix F init d b1 (by rw [hi]; exact hj j (List.mem_of_mem_drop hj')))]
        simp only [tfold, if_neg hl2]

def seqB (n hf : ℕ) : Circuit → List (List ℕ) → Circuit × List ℕ
  | C, [] => (C, [])
  | C, G :: Gs => ((seqB n hf (bt GateOp.and n hf C G).1 Gs).1,
      (bt GateOp.and n hf C G).2 :: (seqB n hf (bt GateOp.and n hf C G).1 Gs).2)

theorem seqB_spec (n hf : ℕ) : ∀ (Gs : List (List ℕ)) (C : Circuit),
    (∀ G ∈ Gs, G ≠ [] ∧ G.length ≤ 2^hf ∧ ∀ j ∈ G, j < n + C.size) →
      C.gates <+: (seqB n hf C Gs).1.gates ∧ (seqB n hf C Gs).1.output = C.output ∧
      (seqB n hf C Gs).2.length = Gs.length ∧
      (∀ o ∈ (seqB n hf C Gs).2, o < n + (seqB n hf C Gs).1.size) ∧
      (FanInTwo C → FanInTwo (seqB n hf C Gs).1) ∧ (ReadsBack n C → ReadsBack n (seqB n hf C Gs).1) ∧
      notCount (seqB n hf C Gs).1 = notCount C ∧
      (∀ (β : Type) (F : List β → Gate → β) (init : List β) (d : β) (f : β → β → β),
        init.length = n → BinForm GateOp.and F d f →
        (∀ o ∈ (seqB n hf C Gs).2, ∃ G ∈ Gs, semC F init d (seqB n hf C Gs).1 o = tfold f (semC F init d C) hf G) ∧
        (∀ G ∈ Gs, ∃ o ∈ (seqB n hf C Gs).2, semC F init d (seqB n hf C Gs).1 o = tfold f (semC F init d C) hf G)) := by
  intro Gs
  induction Gs with
  | nil =>
    intro C _
    refine ⟨List.prefix_refl _, rfl, rfl, by simp [seqB], id, id, rfl, ?_⟩
    intro β F init d f _ _
    simp [seqB]
  | cons G Gs ih =>
    intro C hG
    obtain ⟨g1, g2, g3⟩ := hG G (List.mem_cons_self ..)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bt_spec GateOp.and (Or.inl rfl) n hf C G g1 g2 g3
    set C1 := (bt GateOp.and n hf C G).1 with hC1
    set w1 := (bt GateOp.and n hf C G).2 with hw1
    have hs1 : C.size ≤ C1.size := b1.length_le
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ih C1 (fun G' hG' => by
      obtain ⟨x1, x2, x3⟩ := hG G' (List.mem_cons_of_mem _ hG')
      exact ⟨x1, x2, fun j hj => by have := x3 j hj; omega⟩)
    have e : seqB n hf C (G :: Gs) = ((seqB n hf C1 Gs).1, w1 :: (seqB n hf C1 Gs).2) := rfl
    rw [e]
    have hs2 : C1.size ≤ (seqB n hf C1 Gs).1.size := c1.length_le
    refine ⟨b1.trans c1, by rw [c2, b2], by simp [c3], ?_, fun hf' => c5 (b4 hf'), fun hr => c6 (b5 hr),
      by rw [c7, b6], ?_⟩
    · intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · show w1 < n + (seqB n hf C1 Gs).1.size
        omega
      · exact c4 o ho
    · intro β F init d f hi hb
      obtain ⟨d1, d2⟩ := c8 β F init d f hi hb
      have conv : ∀ G' ∈ Gs, tfold f (semC F init d C1) hf G' = tfold f (semC F init d C) hf G' := by
        intro G' hG'
        obtain ⟨x1, _, x3⟩ := hG G' (List.mem_cons_of_mem _ hG')
        exact tfold_congr f hf G' _ _ x1 (fun j hj => semC_prefix F init d b1 (by rw [hi]; exact x3 j hj))
      have first : semC F init d (seqB n hf C1 Gs).1 w1 = tfold f (semC F init d C) hf G := by
        rw [semC_prefix F init d c1 (by rw [hi]; exact b3), b7 β F init d f hi hb]
      constructor
      · intro o ho
        simp only [List.mem_cons] at ho
        rcases ho with rfl | ho
        · exact ⟨G, List.mem_cons_self .., first⟩
        · obtain ⟨G', hG', e'⟩ := d1 o ho
          exact ⟨G', List.mem_cons_of_mem _ hG', by rw [e', conv G' hG']⟩
      · intro G' hG'
        simp only [List.mem_cons] at hG'
        rcases hG' with rfl | hG'
        · exact ⟨w1, List.mem_cons_self .., first⟩
        · obtain ⟨o, ho, e'⟩ := d2 G' hG'
          exact ⟨o, List.mem_cons_of_mem _ ho, by rw [e', conv G' hG']⟩

end Build

theorem inpX_fin {k : ℕ} [DecidableEq (Fin k)] (Y : Finset (Fin k)) (x : Fin k) :
    (inpX Y).getD x.val false = decide (x ∈ Y) := inpX_lt Y x.val x.isLt

section Final

variable {k : ℕ}

def grp (lt : List (Fin k)) (f i : ℕ) : List (Fin k) := (lt.drop (i*(f+1))).take (f+1)

theorem idx_inj {i i' t t' f : ℕ} (ht : t < f+1) (ht' : t' < f+1) (h : i*(f+1)+t = i'*(f+1)+t') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have h1 : (i+1)*(f+1) ≤ i'*(f+1) := Nat.mul_le_mul (by omega) (le_refl _)
    have h2 : (i+1)*(f+1) = i*(f+1) + (f+1) := by ring
    omega
  · exact heq
  · have h1 : (i'+1)*(f+1) ≤ i*(f+1) := Nat.mul_le_mul (by omega) (le_refl _)
    have h2 : (i'+1)*(f+1) = i'*(f+1) + (f+1) := by ring
    omega

theorem grp_length {lt : List (Fin k)} {a f i : ℕ} (hlen : (a+1)*(f+1) ≤ lt.length) (hi : i < a+1) :
    (grp lt f i).length = f+1 := by
  unfold grp
  rw [List.length_take, List.length_drop]
  have h1 : (i+1)*(f+1) ≤ (a+1)*(f+1) := Nat.mul_le_mul (by omega) (le_refl _)
  have h2 : (i+1)*(f+1) = i*(f+1) + (f+1) := by ring
  omega

theorem grp_nodup {lt : List (Fin k)} (hnd : lt.Nodup) (f i : ℕ) : (grp lt f i).Nodup :=
  hnd.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))

theorem grp_sub {lt : List (Fin k)} {f i : ℕ} {x : Fin k} (hx : x ∈ grp lt f i) : x ∈ lt :=
  List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem grp_index {lt : List (Fin k)} {f i : ℕ} {x : Fin k} (hx : x ∈ grp lt f i) :
    ∃ t, t < f+1 ∧ ∃ hh : i*(f+1)+t < lt.length, lt[i*(f+1)+t] = x := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
  have ht' := ht
  simp only [grp, List.length_take, List.length_drop] at ht'
  have h1 : t < f+1 := by omega
  have h2 : i*(f+1)+t < lt.length := by omega
  refine ⟨t, h1, h2, ?_⟩
  simp [grp]

theorem grp_disj {lt : List (Fin k)} (hnd : lt.Nodup) {f i i' : ℕ} {x : Fin k} (hx : x ∈ grp lt f i)
    (hx' : x ∈ grp lt f i') : i = i' := by
  obtain ⟨t, ht, hh, rfl⟩ := grp_index hx
  obtain ⟨t', ht', hh', he⟩ := grp_index hx'
  have := (List.Nodup.getElem_inj_iff hnd).1 he
  exact (idx_inj ht' ht this).symm

theorem comb_false [dk : DecidableEq (Fin k)] {lt : List (Fin k)} {A B Y : Finset (Fin k)} {a f : ℕ}
    (hnd : lt.Nodup) (hH : ∀ x ∈ lt, x ∈ B \ A) (hlen : (a+1)*(f+1) ≤ lt.length)
    (hcard : (Y \ A).card ≤ f) {i : ℕ} (hi : i < a+1) : ∃ x ∈ grp lt f i, x ∉ Y := by
  by_contra hc
  push_neg at hc
  have hsub : (grp lt f i).toFinset ⊆ Y \ A := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_sdiff.2 ⟨hc x hx, (Finset.mem_sdiff.1 (hH x (grp_sub hx))).2⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (grp_nodup hnd f i), grp_length hlen hi] at this
  omega

theorem comb_true [dk : DecidableEq (Fin k)] {lt : List (Fin k)} {A B Y : Finset (Fin k)} {a f : ℕ}
    (hnd : lt.Nodup) (hH : ∀ x ∈ lt, x ∈ B \ A) (hlen : (a+1)*(f+1) ≤ lt.length)
    (hcard : (B \ Y).card ≤ a) : ∃ i, i < a+1 ∧ ∀ x ∈ grp lt f i, x ∈ Y := by
  by_contra hc
  push_neg at hc
  have hpos : 0 < lt.length := by
    have : 0 < (a+1)*(f+1) := Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos f)
    omega
  haveI : Inhabited (Fin k) := ⟨lt[0]⟩
  choose! φ hφ1 hφ2 using hc
  have := Finset.card_le_card_of_injOn (s := Finset.range (a+1)) (t := B \ Y) φ
    (by
      intro i hi
      have hi' : i < a+1 := by simpa using hi
      have hm := hH _ (grp_sub (hφ1 i hi'))
      exact Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hm).1, hφ2 i hi'⟩)
    (by
      intro i hi i' hi' he
      have h1 : i < a+1 := by simpa using hi
      have h2 : i' < a+1 := by simpa using hi'
      have hx := hφ1 i h1
      have hx' := hφ1 i' h2
      rw [he] at hx
      exact grp_disj hnd hx hx')
  rw [Finset.card_range] at this
  omega

def groupsN (lt : List (Fin k)) (a f : ℕ) : List (List ℕ) :=
  (List.range (a+1)).map (fun i => (grp lt f i).map Fin.val)

def mainC (lt : List (Fin k)) (a f : ℕ) : Circuit :=
  withOutput (bt GateOp.or (k+2) (Nat.clog 2 (a+1))
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).1
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).2).1
    (bt GateOp.or (k+2) (Nat.clog 2 (a+1))
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).1
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).2).2

theorem mainC_spec [dk : DecidableEq (Fin k)] {lt : List (Fin k)} {a f : ℕ}
    (hlen : (a+1)*(f+1) ≤ lt.length) (c e : ℕ) :
    FanInTwo (mainC lt a f) ∧ ReadsBack (k+2) (mainC lt a f) ∧
    (mainC lt a f).output < k+2+(mainC lt a f).size ∧ notCount (mainC lt a f) = 0 ∧
    (∀ Y : Finset (Fin k), valX (mainC lt a f) (mainC lt a f).output Y = true ↔
      ∃ i, i < a+1 ∧ ∀ x ∈ grp lt f i, x ∈ Y) ∧
    delayX k c e (mainC lt a f) ≤ c * Nat.clog 2 (f+1) + e * Nat.clog 2 (a+1) := by
  have hb : (1:ℕ) < 2 := by norm_num
  have hG : ∀ G ∈ groupsN lt a f, G ≠ [] ∧ G.length ≤ 2^(Nat.clog 2 (f+1)) ∧
      ∀ j ∈ G, j < (k+2) + emptyCircuit.size := by
    intro G hG
    simp only [groupsN, List.mem_map, List.mem_range] at hG
    obtain ⟨i, hi, rfl⟩ := hG
    have hl := grp_length hlen hi
    refine ⟨?_, ?_, ?_⟩
    · intro he
      have := congrArg List.length he
      simp [hl] at this
    · rw [List.length_map, hl]
      exact Nat.le_pow_clog hb _
    · intro j hj
      simp only [List.mem_map] at hj
      obtain ⟨x, _, rfl⟩ := hj
      have := x.isLt
      show x.val < k + 2 + 0
      omega
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ :=
    seqB_spec (k+2) (Nat.clog 2 (f+1)) (groupsN lt a f) emptyCircuit hG
  unfold mainC
  set S := seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f) with hS
  have hlenS : S.2.length = a+1 := by rw [m3]; simp [groupsN]
  have hneS : S.2 ≠ [] := by
    intro he
    rw [he] at hlenS
    simp at hlenS
  have hle2 : S.2.length ≤ 2^(Nat.clog 2 (a+1)) := by rw [hlenS]; exact Nat.le_pow_clog hb _
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    bt_spec GateOp.or (Or.inr rfl) (k+2) (Nat.clog 2 (a+1)) S.1 S.2 hneS hle2 m4
  set T := bt GateOp.or (k+2) (Nat.clog 2 (a+1)) S.1 S.2 with hT
  refine ⟨t4 (m5 emptyCircuit_fanInTwo), t5 (m6 (emptyCircuit_readsBack _)), t3, ?_, ?_, ?_⟩
  · show notCount T.1 = 0
    rw [t6, m7]
    rfl
  · intro Y
    have bo : BinForm GateOp.or Fval false (fun x y => x || y) := by
      unfold BinForm
      intro W a b
      simp [Fval, GateOp.eval]
    have ba : BinForm GateOp.and Fval false (fun x y => x && y) := by
      unfold BinForm
      intro W a b
      simp [Fval, GateOp.eval]
    have e1 : valX (withOutput T.1 T.2) (withOutput T.1 T.2).output Y =
        semC Fval (inpX Y) false T.1 T.2 := rfl
    rw [e1, t7 Bool Fval (inpX Y) false _ (inpX_length Y) bo, tfold_any _ _ _ hneS hle2,
      List.any_eq_true]
    obtain ⟨d1, d2⟩ := m8 Bool Fval (inpX Y) false _ (inpX_length Y) ba
    have hgrp : ∀ G ∈ groupsN lt a f, tfold (fun x y => x && y) (semC Fval (inpX Y) false emptyCircuit)
        (Nat.clog 2 (f+1)) G = G.all (fun j => (inpX Y).getD j false) := by
      intro G hG'
      obtain ⟨x1, x2, _⟩ := hG G hG'
      rw [tfold_all _ _ _ x1 x2]
      rfl
    constructor
    · rintro ⟨o, ho, hv⟩
      obtain ⟨G, hG', he⟩ := d1 o ho
      rw [he, hgrp G hG'] at hv
      simp only [groupsN, List.mem_map, List.mem_range] at hG'
      obtain ⟨i, hi, rfl⟩ := hG'
      refine ⟨i, hi, ?_⟩
      intro x hx
      have h5 : (inpX Y).getD x.val false = true := List.all_eq_true.1 hv x.val (List.mem_map.2 ⟨x, hx, rfl⟩)
      rw [inpX_fin] at h5
      exact of_decide_eq_true h5
    · rintro ⟨i, hi, hall⟩
      have hG' : (grp lt f i).map Fin.val ∈ groupsN lt a f := by
        simp only [groupsN, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩
      obtain ⟨o, ho, he⟩ := d2 _ hG'
      refine ⟨o, ho, ?_⟩
      rw [he, hgrp _ hG', List.all_eq_true]
      intro j hj
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
      show (inpX Y).getD x.val false = true
      rw [inpX_fin]
      exact decide_eq_true (hall x hx)
  · have bat : BinForm GateOp.and (Ftime c e) 0 (fun x y => max x y + c) := by
      unfold BinForm
      intro W a b
      rw [Ftime_and _ _ _ _ rfl]
      simp
    have bot : BinForm GateOp.or (Ftime c e) 0 (fun x y => max x y + e) := by
      unfold BinForm
      intro W a b
      rw [Ftime_or _ _ _ _ rfl]
      simp
    have e1 : delayX k c e (withOutput T.1 T.2) = semC (Ftime c e) (List.replicate (k+2) 0) 0 T.1 T.2 := rfl
    rw [e1, t7 ℕ (Ftime c e) _ 0 _ (by simp) bot]
    obtain ⟨d1, _⟩ := m8 ℕ (Ftime c e) (List.replicate (k+2) 0) 0 _ (by simp) bat
    have hb1 : ∀ o ∈ S.2, semC (Ftime c e) (List.replicate (k+2) 0) 0 S.1 o ≤ Nat.clog 2 (f+1) * c := by
      intro o ho
      obtain ⟨G, hG', he⟩ := d1 o ho
      rw [he]
      obtain ⟨x1, _, _⟩ := hG G hG'
      have := tfold_le c (Nat.clog 2 (f+1)) G (semC (Ftime c e) (List.replicate (k+2) 0) 0 emptyCircuit) 0 x1
        (fun j _ => by
          rw [semC_empty, List.getD_eq_getElem?_getD, List.getElem?_replicate]
          split_ifs <;> simp)
      simpa using this
    have h3 := tfold_le e (Nat.clog 2 (a+1)) S.2 _ _ hneS hb1
    have h4 : Nat.clog 2 (f+1) * c + Nat.clog 2 (a+1) * e = c * Nat.clog 2 (f+1) + e * Nat.clog 2 (a+1) := by
      ring
    omega

end Final

end PEqualNP.Outside.L_lib_1454_aux

theorem PEqualNP.Outside.L_lib_1454 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
  ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
let delay := fun (k c e : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let times := D.gates.foldl (fun (ts : List Nat) g =>
    let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
    ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((g.inputs.head?.map (fun j => ts.getD j 0)).getD 0)
      else mx+(if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then c else e)]) (List.replicate (k+2) 0)
  times.getD D.output 0
let paths := fun {k : Nat} (i : Fin k) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let seeds := List.ofFn (fun j : Fin k => if j=i then ({(0,0)} : Finset (Nat × Nat)) else ∅) ++ [∅,∅]
  let ws := D.gates.foldl (fun (zs : List (Finset (Nat × Nat))) g =>
    let ps := g.inputs.foldl (fun acc j => acc ∪ zs.getD j ∅) ∅
    zs ++ [ps.image (fun z => if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (z.1+1,z.2) else (z.1,z.2+1))]) seeds
  ws.getD D.output ∅
∀ (k a f : Nat) (A B : Finset (Fin k)), A ⊆ B →
  let H := B \ A
  let ok := fun (D : PEqualNP.CircuitLowerBounds.Circuit) => valid k D ∧ PEqualNP.NotBracket.notCount D=0 ∧
    ∀ Y, A ⊆ Y → Y ⊆ B → (((Y \ A).card ≤ f → run D Y=false) ∧ ((B \ Y).card ≤ a → run D Y=true))
  (∀ D, ok D → ∃ i ∈ H, ∃ uv ∈ paths i D, f+1 ≤ 2^uv.1 ∧ a+1 ≤ 2^uv.2) ∧
  ((a+1)*(f+1) ≤ H.card → ∀ c e T : Nat,
    (∃ D, ok D ∧ delay k c e D ≤ T) ↔ c*Nat.clog 2 (f+1)+e*Nat.clog 2 (a+1) ≤ T)) := by
  intro valid run delay paths k a f A B hAB H ok
  have hrun : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)), run D Y =
      @PEqualNP.Outside.L_lib_1454_aux.valX k (fun x y => Classical.propDecidable (x = y)) D D.output Y := by
    intro D Y
    simp only [run, PEqualNP.Outside.L_lib_1454_aux.valX, PEqualNP.Outside.L_lib_1454_aux.inpX]
    congr
    funext j
    exact decide_eq_decide.mpr Iff.rfl
  have part1 : ∀ D, ok D → ∃ i ∈ H, ∃ uv ∈ paths i D, f+1 ≤ 2^uv.1 ∧ a+1 ≤ 2^uv.2 := by
    intro D hD
    obtain ⟨⟨hfan, hrb, hout⟩, hnc, hspec⟩ := hD
    exact PEqualNP.Outside.L_lib_1454_aux.core (dk := fun x y => Classical.propDecidable (x = y)) A B hAB D hfan hrb hnc
      D.output hout (f+1) (a+1) (by omega) (by omega)
      (fun Y h1 h2 h3 => by rw [← hrun]; exact (hspec Y h1 h2).1 (by omega))
      (fun Y h1 h2 h3 => by rw [← hrun]; exact (hspec Y h1 h2).2 (by omega))
  refine ⟨part1, ?_⟩
  intro hcard c e T
  constructor
  · rintro ⟨D, hD, hT⟩
    obtain ⟨i, hi, uv, huv, h1, h2⟩ := part1 D hD
    obtain ⟨⟨hfan, hrb, hout⟩, hnc, _⟩ := hD
    have hd := PEqualNP.Outside.L_lib_1454_aux.delay_ge D hrb hnc hfan c e i D.output uv huv
    have hc1 := Nat.clog_le_of_le_pow h1
    have hc2 := Nat.clog_le_of_le_pow h2
    have hT' : c*uv.1 + e*uv.2 ≤ T := le_trans hd hT
    have m1 := Nat.mul_le_mul_left c hc1
    have m2 := Nat.mul_le_mul_left e hc2
    omega
  · intro hT
    have hnd : H.toList.Nodup := Finset.nodup_toList H
    have hH : ∀ x ∈ H.toList, x ∈ H := fun x hx => Finset.mem_toList.1 hx
    have hlen : (a+1)*(f+1) ≤ H.toList.length := by rw [Finset.length_toList]; exact hcard
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ :=
      PEqualNP.Outside.L_lib_1454_aux.mainC_spec (dk := fun x y => Classical.propDecidable (x = y)) hlen c e
    refine ⟨PEqualNP.Outside.L_lib_1454_aux.mainC H.toList a f, ⟨⟨s1, s2, s3⟩, s4, ?_⟩, le_trans s6 hT⟩
    intro Y h1 h2
    constructor
    · intro h3
      rw [hrun]
      cases hv : @PEqualNP.Outside.L_lib_1454_aux.valX k (fun x y => Classical.propDecidable (x = y))
          (PEqualNP.Outside.L_lib_1454_aux.mainC H.toList a f) (PEqualNP.Outside.L_lib_1454_aux.mainC H.toList a f).output Y with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨i, hi, hall⟩ := (s5 Y).1 hv
        obtain ⟨x, hx, hxY⟩ := PEqualNP.Outside.L_lib_1454_aux.comb_false (dk := fun x y => Classical.propDecidable (x = y))
          hnd hH hlen h3 hi
        exact hxY (hall x hx)
    · intro h3
      rw [hrun]
      exact (s5 Y).2 (PEqualNP.Outside.L_lib_1454_aux.comb_true (dk := fun x y => Classical.propDecidable (x = y)) hnd hH hlen h3)
