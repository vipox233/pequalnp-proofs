import PEqualNP.Defs


namespace PEqualNP.Outside.L_lib_1401_aux.Source

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

abbrev Input (n : ℕ) := Fin n → Bool

variable {n m : ℕ} (P N : Input n → Fin m → Prop)

theorem reach_zero (x : Input n) : Reach P N 0 x := trivial

theorem reach_succ (k : ℕ) (x : Input n) : Reach P N (k+1) x ↔
    ∃ u v j, Reach P N k u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j := Iff.rfl

theorem reach_mono (k : ℕ) : Monotone (Reach P N k) := by
  intro x y xy active
  cases k with
  | zero => exact reach_zero P N y
  | succ k =>
    obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
    exact (reach_succ P N k y).mpr ⟨u,v,j,prior,uv,vx.trans xy,pu,nv⟩

theorem reach_pred {k : ℕ} {x : Input n} (active : Reach P N (k+1) x) : Reach P N k x := by
  obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
  exact reach_mono P N k (uv.trans vx) prior

theorem reach_of_le {k l : ℕ} {x : Input n} (bound : k ≤ l) (active : Reach P N l x) :
    Reach P N k x := by
  induction bound with
  | refl => exact active
  | step _ ih => exact ih (reach_pred P N active)

noncomputable def support : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ j, P x j ∨ N x j)

theorem mem_support (x : Input n) : x ∈ support P N ↔ ∃ j, P x j ∨ N x j := by
  classical
  simp [support]

theorem cone_iff (u x : Input n) : u ≤ x ↔ ∀ i, u i = true → x i = true := by
  constructor
  · intro below i active
    exact Bool.le_iff_imp.mp (below i) active
  · intro on i
    exact Bool.le_iff_imp.mpr (on i)

theorem reach_support {k : ℕ} (positive : 0 < k) (x : Input n) : Reach P N k x ↔
    ∃ v ∈ support P N, v ≤ x ∧ Reach P N k v := by
  constructor
  · intro active
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
      refine ⟨v,(mem_support P N v).mpr ⟨j,Or.inr nv⟩,vx,?_⟩
      exact (reach_succ P N k v).mpr ⟨u,v,j,prior,uv,le_rfl,pu,nv⟩
  · rintro ⟨v,_,vx,active⟩
    exact reach_mono P N k vx active

private noncomputable def levels (d : ℕ) (x : Input n) : Finset ℕ := by
  classical
  exact (Finset.range (d+1)).filter (fun k => Reach P N k x)

private theorem mem_levels (d : ℕ) (x : Input n) (k : ℕ) :
    k ∈ levels P N d x ↔ k ≤ d ∧ Reach P N k x := by
  classical
  simp [levels,Nat.lt_succ_iff]

private theorem levels_nonempty (d : ℕ) (x : Input n) : (levels P N d x).Nonempty :=
  ⟨0,(mem_levels P N d x 0).mpr ⟨Nat.zero_le _,reach_zero P N x⟩⟩

noncomputable def rank (d : ℕ) (x : Input n) : ℕ :=
  (levels P N d x).max' (levels_nonempty P N d x)

theorem rank_bound (d : ℕ) (x : Input n) : rank P N d x ≤ d :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).1

theorem rank_reaches (d : ℕ) (x : Input n) : Reach P N (rank P N d x) x :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).2

theorem level_le_rank {d k : ℕ} {x : Input n} (small : k ≤ d) (active : Reach P N k x) :
    k ≤ rank P N d x :=
  Finset.le_max' (levels P N d x) k ((mem_levels P N d x k).mpr ⟨small,active⟩)

theorem rank_mono (d : ℕ) : Monotone (rank P N d) := by
  intro x y xy
  exact level_le_rank P N (rank_bound P N d x) (reach_mono P N _ xy (rank_reaches P N d x))

theorem rank_threshold_iff {d k : ℕ} {x : Input n} (small : k ≤ d) :
    k ≤ rank P N d x ↔ Reach P N k x :=
  ⟨fun below => reach_of_le P N below (rank_reaches P N d x), level_le_rank P N small⟩

theorem rank_grows {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {u v : Input n} {j : Fin m} (uv : u ≤ v) (pu : P u j) (nv : N v j) :
    rank P N d u < rank P N d v := by
  have next : Reach P N (rank P N d u + 1) v :=
    (reach_succ P N _ v).mpr ⟨u,v,j,rank_reaches P N d u,uv,le_rfl,pu,nv⟩
  have room : rank P N d u + 1 ≤ d := by
    by_contra notRoom
    exact bounded v (reach_of_le P N (by omega : d+1 ≤ rank P N d u+1) next)
  exact Nat.lt_of_succ_le (level_le_rank P N room next)

theorem threshold_support (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ v ∈ support P N, v ≤ x ∧ k ≤ rank P N d v := by
  constructor
  · intro high
    have small : k ≤ d := high.trans (rank_bound P N d x)
    obtain ⟨v,mem,vx,active⟩ := (reach_support P N positive x).mp
      ((rank_threshold_iff P N small).mp high)
    exact ⟨v,mem,vx,level_le_rank P N small active⟩
  · rintro ⟨v,_,vx,high⟩
    exact high.trans (rank_mono P N d vx)

noncomputable def rankBucket (d k : ℕ) : Finset (Input n) := by
  classical
  exact (support P N).filter (fun x => rank P N d x = k)

theorem mem_rankBucket (d k : ℕ) (x : Input n) :
    x ∈ rankBucket P N d k ↔ x ∈ support P N ∧ rank P N d x = k := by
  classical
  simp [rankBucket]

theorem rank_bucket_count (d : ℕ) :
    (∑ k ∈ Finset.range (d+1), (rankBucket P N d k).card) = (support P N).card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (s := support P N) (t := Finset.range (d+1))
    (f := rank P N d) (by
      intro x _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (rank_bound P N d x)))).symm

theorem threshold_buckets (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ l, k ≤ l ∧ l ≤ d ∧ ∃ v ∈ rankBucket P N d l, v ≤ x := by
  constructor
  · intro on
    obtain ⟨v,mem,vx,below⟩ := (threshold_support P N d positive x).mp on
    exact ⟨rank P N d v,below,rank_bound P N d v,v,(mem_rankBucket P N d _ _).mpr ⟨mem,rfl⟩,vx⟩
  · rintro ⟨l,kl,_,v,mem,vx⟩
    obtain ⟨supportV,level⟩ := (mem_rankBucket P N d l v).mp mem
    exact (threshold_support P N d positive x).mpr ⟨v,supportV,vx,level.symm ▸ kl⟩

noncomputable def positiveInputs (j : Fin m) : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => P x j)

noncomputable def positivePairs : Finset (Input n × Fin m) := by
  classical
  exact Finset.univ.filter (fun z => P z.1 z.2)

theorem mem_positiveInputs (j : Fin m) (x : Input n) : x ∈ positiveInputs P j ↔ P x j := by
  classical
  simp [positiveInputs]

theorem mem_positivePairs (z : Input n × Fin m) : z ∈ positivePairs P ↔ P z.1 z.2 := by
  classical
  simp [positivePairs]

theorem positive_input_support {j : Fin m} {x : Input n} (positive : x ∈ positiveInputs P j) :
    x ∈ support P N :=
  (mem_support P N x).mpr ⟨j,Or.inl ((mem_positiveInputs P j x).mp positive)⟩

theorem positive_incidence_count :
    (∑ j : Fin m, (positiveInputs P j).card) = (positivePairs P).card := by
  classical
  calc
    _ = ∑ j : Fin m, ((positivePairs P).filter (fun z => z.2 = j)).card := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.card_nbij' (fun x : Input n => (x,j)) Prod.fst
      · intro x present
        exact Finset.mem_filter.mpr ⟨(mem_positivePairs P _).mpr ((mem_positiveInputs P _ _).mp present),rfl⟩
      · intro z present
        obtain ⟨member,eq⟩ := Finset.mem_filter.mp present
        exact (mem_positiveInputs P _ _).mpr (eq ▸ (mem_positivePairs P z).mp member)
      · intro x _
        rfl
      · intro z present
        exact Prod.ext rfl (Finset.mem_filter.mp present).2.symm
    _ = _ := (Finset.card_eq_sum_card_fiberwise (s := positivePairs P) (t := Finset.univ)
      (f := Prod.snd) (by
        intro j _
        exact Finset.mem_univ _)).symm

def guardedCone (d : ℕ) (u x : Input n) : Prop :=
  u ≤ x ∧ ¬ rank P N d u + 1 ≤ rank P N d x

def tapAccepts (d : ℕ) (x : Input n) (j : Fin m) : Prop :=
  ∃ u ∈ positiveInputs P j, guardedCone P N d u x

theorem tap_accepts_positive (d : ℕ) {x : Input n} {j : Fin m} (positive : P x j) :
    tapAccepts P N d x j := by
  refine ⟨x,(mem_positiveInputs P j x).mpr positive,le_rfl,?_⟩
  omega

theorem tap_rejects_negative {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {x : Input n} {j : Fin m} (negative : N x j) : ¬ tapAccepts P N d x j := by
  rintro ⟨u,mem,ux,below⟩
  have grows := rank_grows P N bounded ux ((mem_positiveInputs P j u).mp mem) negative
  exact below (Nat.succ_le_of_lt grows)

namespace Thermometer

abbrev Word (d : ℕ) := Fin d → Bool

def half (d : ℕ) : ℕ := d / 2

def middle (d : ℕ) : ℕ := (d - 1) / 2

theorem half_le (d : ℕ) : half d ≤ d := by
  unfold half
  omega

theorem middle_le_half (d : ℕ) : middle d ≤ half d := by
  unfold middle half
  omega

theorem split_length {d : ℕ} (positive : 0 < d) :
    middle d + 1 + half d = d := by
  unfold middle half
  omega

theorem half_lt_pow {r d : ℕ} (bound : d < 2^(r+1)) : half d < 2^r := by
  rw [Nat.pow_succ] at bound
  unfold half
  omega

def pivot {d : ℕ} (positive : 0 < d) : Fin d :=
  ⟨middle d,by have eq := split_length positive; omega⟩

def lowerSource {d : ℕ} (i : Fin (half d)) : Fin d :=
  ⟨i.val,i.isLt.trans_le (half_le d)⟩

def upperSource {d : ℕ} (positive : 0 < d) (i : Fin (half d)) : Fin d :=
  ⟨middle d + 1 + i.val,by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerSlot {d : ℕ} (i : Fin d) (before : i.val < middle d) : Fin (half d) :=
  ⟨i.val,before.trans_le (middle_le_half d)⟩

def upperSlot {d : ℕ} (positive : 0 < d) (i : Fin d) (after : middle d < i.val) : Fin (half d) :=
  ⟨i.val - (middle d + 1),by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerWord {d : ℕ} (w : Word d) : Word (half d) :=
  fun i => if i.val < middle d then w (lowerSource i) else false

def upperWord {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => w (upperSource positive i)

def folded {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => (!w (pivot positive) && lowerWord w i) || upperWord positive w i

private theorem lower_antitone {d : ℕ} {w : Word d} (ordered : Antitone w) :
    Antitone (lowerWord w) := by
  intro i j compare
  by_cases before : j.val < middle d
  · have earlier : i.val < middle d := lt_of_le_of_lt compare before
    simp only [lowerWord,ite_eq_left before,ite_eq_left earlier]
    exact ordered (show lowerSource i ≤ lowerSource j from compare)
  · simp only [lowerWord,ite_eq_right before]
    exact Bool.false_le _

private theorem upper_antitone {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w) :
    Antitone (upperWord positive w) := by
  intro i j compare
  apply ordered
  change middle d + 1 + i.val ≤ middle d + 1 + j.val
  exact Nat.add_le_add_left compare _

theorem folded_eq_lower {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    (off : w (pivot positive) = false) (i : Fin (half d)) :
    folded positive w i = lowerWord w i := by
  have after : pivot positive ≤ upperSource positive i := by
    change middle d ≤ middle d + 1 + i.val
    omega
  have upperOff : upperWord positive w i = false :=
    Bool.eq_false_of_le_false (by simpa only [off,upperWord] using ordered after)
  simp [folded,off,upperOff]

theorem folded_eq_upper {d : ℕ} (positive : 0 < d) {w : Word d}
    (on : w (pivot positive) = true) (i : Fin (half d)) :
    folded positive w i = upperWord positive w i := by
  simp [folded,on]

theorem folded_antitone {d : ℕ} (positive : 0 < d) {w : Word d}
    (ordered : Antitone w) : Antitone (folded positive w) := by
  cases bit : w (pivot positive)
  · rw [funext (folded_eq_lower positive ordered bit)]
    exact lower_antitone ordered
  · rw [funext (folded_eq_upper positive bit)]
    exact upper_antitone positive ordered

def decoded {d : ℕ} (positive : 0 < d) (notPivot : Bool)
    (notHalf : Word (half d)) (i : Fin d) : Bool :=
  if before : i.val < middle d then notPivot && notHalf (lowerSlot i before)
  else if atPivot : i.val = middle d then notPivot
  else notPivot || notHalf (upperSlot positive i (by omega))

theorem decoded_lower {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (before : i.val < middle d) :
    decoded positive b z i = (b && z (lowerSlot i before)) := by
  simp only [decoded,dite_eq_left before]

theorem decoded_pivot {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (atPivot : i.val = middle d) : decoded positive b z i = b := by
  have notBefore : ¬ i.val < middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_left atPivot]

theorem decoded_upper {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (after : middle d < i.val) :
    decoded positive b z i = (b || z (upperSlot positive i after)) := by
  have notBefore : ¬ i.val < middle d := by omega
  have notPivot : i.val ≠ middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_right notPivot]

private theorem lower_at_slot {d : ℕ} (w : Word d) (i : Fin d)
    (before : i.val < middle d) : lowerWord w (lowerSlot i before) = w i := by
  have same : lowerSource (lowerSlot i before) = i := Fin.ext rfl
  change (if i.val < middle d then w (lowerSource (lowerSlot i before)) else false) = w i
  rw [ite_eq_left before,same]

private theorem upper_at_slot {d : ℕ} (positive : 0 < d) (w : Word d) (i : Fin d)
    (after : middle d < i.val) : upperWord positive w (upperSlot positive i after) = w i := by
  apply congrArg w
  apply Fin.ext
  change middle d + 1 + (i.val - (middle d + 1)) = i.val
  omega

theorem decoded_correct {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    {z : Word (half d)} (tail : ∀ j, z j = !(folded positive w j)) (i : Fin d) :
    decoded positive (!w (pivot positive)) z i = !w i := by
  rcases lt_trichotomy i.val (middle d) with before | atPivot | after
  · rw [decoded_lower positive _ _ _ before]
    cases bit : w (pivot positive)
    · simp [bit,tail,folded_eq_lower positive ordered bit,lower_at_slot w i before]
    · have earlier : i ≤ pivot positive := by
        change i.val ≤ middle d
        omega
      have on : w i = true := Bool.eq_true_of_true_le (by simpa only [bit] using ordered earlier)
      simp [bit,on]
  · have same : pivot positive = i := Fin.ext atPivot.symm
    rw [decoded_pivot positive _ _ _ atPivot,same]
  · rw [decoded_upper positive _ _ _ after]
    cases bit : w (pivot positive)
    · have later : pivot positive ≤ i := by
        change middle d ≤ i.val
        omega
      have off : w i = false := Bool.eq_false_of_le_false (by simpa only [bit] using ordered later)
      simp [bit,off]
    · simp [bit,tail,folded_eq_upper positive bit,upper_at_slot positive w i after]

def inverted : (r d : ℕ) → Word d → Word d
  | 0, _, w => w
  | r+1, d, w =>
    if positive : 0 < d then
      decoded positive (!w (pivot positive)) (inverted r (half d) (folded positive w))
    else w

theorem inverted_correct {r d : ℕ} (bound : d < 2^r) (w : Word d) (ordered : Antitone w) :
    inverted r d w = fun i => !w i := by
  induction r generalizing d with
  | zero =>
    funext i
    have existsIndex := i.isLt
    simp at bound
    omega
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inverted,dite_eq_left positive]
      funext i
      have complement := ih (half_lt_pow bound) (folded positive w)
        (folded_antitone positive ordered)
      exact decoded_correct positive ordered (congrFun complement) i
    · funext i
      have existsIndex := i.isLt
      omega

def stepBinary (d : ℕ) : ℕ := 2 * half d + (d - 1)

theorem step_binary_bound (d : ℕ) : stepBinary d + 4 * half d ≤ 4*d := by
  unfold stepBinary half
  omega

def inversionBinary : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then stepBinary d + inversionBinary r (half d) else 0

def inversionNot : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then 1 + inversionNot r (half d) else 0

theorem inversion_binary_bound (r d : ℕ) : inversionBinary r d ≤ 4*d := by
  induction r generalizing d with
  | zero => simp [inversionBinary]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionBinary,ite_eq_left positive]
      exact Nat.le_trans (Nat.add_le_add_left (ih (half d)) _) (step_binary_bound d)
    · simp [inversionBinary,positive]

theorem inversion_not_bound (r d : ℕ) : inversionNot r d ≤ r := by
  induction r generalizing d with
  | zero => simp [inversionNot]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionNot,ite_eq_left positive]
      have count := ih (half d)
      omega
    · simp [inversionNot,positive]

end Thermometer

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendBinary (conjunction : Bool) (C : Circuit) (left right : ℕ) : Circuit :=
  if conjunction then appendAnd C left right else appendOr C left right

def foldBinary (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) :
    List ℕ → Circuit × ℕ
  | [] => (C,base)
  | i :: rest => foldBinary n conjunction (appendBinary conjunction C base i) (nextWire n C) rest

private theorem fold_values (conjunction : Bool) (indices : List ℕ) (a b : ℕ → Bool)
    (same : ∀ i ∈ indices, a i = b i) (base : Bool) :
    indices.foldl (fun acc i => binaryValue conjunction acc (a i)) base =
      indices.foldl (fun acc i => binaryValue conjunction acc (b i)) base := by
  induction indices generalizing base with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons,same i (List.mem_cons_self ..)]
    exact ih (fun j hj => same j (List.mem_cons_of_mem _ hj)) _

theorem foldBinary_spec (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) (basis : FanInTwo C) (reads : ReadsBack n C)
    (baseValid : base < nextWire n C) (valid : ∀ i ∈ indices, i < nextWire n C) :
    let result := foldBinary n conjunction C base indices
    FanInTwo result.1 ∧ ReadsBack n result.1 ∧ result.2 < nextWire n result.1 ∧
      result.1.size = C.size + indices.length ∧ notCount result.1 = notCount C ∧
      ∀ (x : List Bool), x.length = n →
        (∀ i < nextWire n C, value result.1 x i = value C x i) ∧
        value result.1 x result.2 =
          indices.foldl (fun acc i => binaryValue conjunction acc (value C x i)) (value C x base) := by
  induction indices generalizing C base with
  | nil => exact ⟨basis,reads,baseValid,by simp [foldBinary],rfl,fun _ _ => ⟨fun _ _ => rfl,rfl⟩⟩
  | cons i rest ih =>
    let D := appendBinary conjunction C base i
    have iValid := valid i (List.mem_cons_self ..)
    have size : D.size = C.size+1 := by cases conjunction <;> simp [D,appendBinary]
    have nots : notCount D = notCount C := by cases conjunction <;> simp [D,appendBinary]
    have growth : nextWire n D = nextWire n C+1 := by simp [nextWire,size,Nat.add_assoc]
    have forms : FanInTwo D := by
      cases conjunction
      · exact appendOr_fanInTwo basis
      · exact appendAnd_fanInTwo basis
    have previous : ReadsBack n D := by
      cases conjunction
      · exact appendOr_readsBack reads baseValid iValid
      · exact appendAnd_readsBack reads baseValid iValid
    have persist (x : List Bool) (length : x.length = n) (j : ℕ) (earlier : j < nextWire n C) :
        value D x j = value C x j := by
      rw [← length] at earlier
      cases conjunction
      · exact appendGate_old (g := ⟨.or,[base,i]⟩) earlier
      · exact appendGate_old (g := ⟨.and,[base,i]⟩) earlier
    have evaluated (x : List Bool) (length : x.length = n) :
        value D x (nextWire n C) = binaryValue conjunction (value C x base) (value C x i) := by
      rw [← length]
      cases conjunction
      · exact appendOr_new C x base i
      · exact appendAnd_new C x base i
    obtain ⟨hasBasis,hasReads,output,finalSize,finalNot,wires⟩ :=
      ih D (nextWire n C) forms previous (by rw [growth]; omega)
        (fun j hj => (valid j (List.mem_cons_of_mem _ hj)).trans (by rw [growth]; omega))
    refine ⟨hasBasis,hasReads,output,?_,finalNot.trans nots,?_⟩
    · change (foldBinary n conjunction D (nextWire n C) rest).1.size = C.size + (i :: rest).length
      rw [finalSize,size,List.length_cons]
      omega
    · intro x length
      obtain ⟨old,current⟩ := wires x length
      refine ⟨fun j hj => (old j (hj.trans (by rw [growth]; omega))).trans (persist x length j hj),?_⟩
      change value (foldBinary n conjunction D (nextWire n C) rest).1 x
        (foldBinary n conjunction D (nextWire n C) rest).2 =
        (i :: rest).foldl (fun acc j => binaryValue conjunction acc (value C x j)) (value C x base)
      rw [List.foldl_cons,current,evaluated x length]
      exact fold_values conjunction rest (value D x) (value C x)
        (fun j hj => persist x length j (valid j (List.mem_cons_of_mem _ hj))) _

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def withConstants {n : ℕ} (x : Input n) : List Bool := List.ofFn x ++ [false,true]

@[local simp] theorem withConstants_length {n : ℕ} (x : Input n) :
    (withConstants x).length = n+2 := by simp [withConstants]

theorem input_value {n : ℕ} (C : Circuit) (x : Input n) (i : Fin n) :
    value C (withConstants x) i.val = x i := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have inside : i.val < (List.ofFn x).length := by simpa using i.isLt
  simp only [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_left inside]
  simp [List.getElem?_ofFn,i.isLt]

theorem false_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) n = false := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  simp [withConstants,List.getD_eq_getElem?_getD]

theorem true_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) (n+1) = true := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have outside : (List.ofFn x).length ≤ n+1 := by simp
  simp [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_right outside]

def coneIndices {n : ℕ} (u : Input n) : List ℕ :=
  ((List.finRange n).filter u).map (fun i => i.val)

theorem coneIndices_length {n : ℕ} (u : Input n) : (coneIndices u).length ≤ n := by
  simpa [coneIndices] using List.length_filter_le (p := u) (l := List.finRange n)

private theorem fold_and_true (inputs : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    inputs.foldl (fun b i => b && bits i) base = true ↔
      base = true ∧ ∀ i ∈ inputs, bits i = true := by
  induction inputs generalizing base with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons,ih,Bool.and_eq_true,List.mem_cons,forall_eq_or_imp,and_assoc]

def emitCone {n : ℕ} (C : Circuit) (u : Input n) : Circuit × ℕ :=
  foldBinary (n+2) true C (n+1) (coneIndices u)

theorem emitCone_spec {n : ℕ} (C : Circuit) (u : Input n)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCone C u
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ result.2 < nextWire (n+2) result.1 ∧
      C.size ≤ result.1.size ∧ result.1.size ≤ C.size+n ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      ∀ x : Input n, value result.1 (withConstants x) result.2 = true ↔ u ≤ x := by
  have validBase : n+1 < nextWire (n+2) C := by unfold nextWire; omega
  have valid : ∀ i ∈ coneIndices u, i < nextWire (n+2) C := by
    intro i hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    unfold nextWire
    omega
  obtain ⟨newBasis,newReads,output,size,neg,sem⟩ :=
    foldBinary_spec (n+2) true C (n+1) (coneIndices u) basis reads validBase valid
  refine ⟨newBasis,newReads,output,(Nat.le_add_right _ _).trans size.ge,size.le.trans
    (Nat.add_le_add_left (coneIndices_length u) _),neg,?_,?_⟩
  · intro x i hi
    exact (sem (withConstants x) (withConstants_length x)).1 i hi
  · intro x
    have evaluated := (sem (withConstants x) (withConstants_length x)).2
    change value (foldBinary (n+2) true C (n+1) (coneIndices u)).1 (withConstants x)
        (foldBinary (n+2) true C (n+1) (coneIndices u)).2 = true ↔ u ≤ x
    rw [evaluated,true_value]
    simp only [binaryValue,ite_true,fold_and_true,true_and]
    rw [cone_iff]
    constructor
    · intro every i active
      have mem : i.val ∈ coneIndices u := List.mem_map.mpr
        ⟨i,List.mem_filter.mpr ⟨List.mem_finRange _,active⟩,rfl⟩
      exact (input_value C x i).symm.trans (every i.val mem)
    · intro above i mem
      obtain ⟨j,selected,rfl⟩ := List.mem_map.mp mem
      exact (input_value C x j).trans (above j (List.mem_filter.mp selected).2)

def emitCones {n : ℕ} (C : Circuit) : List (Input n) → Circuit × List ℕ
  | [] => (C,[])
  | u :: rest =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    (later.1,first.2 :: later.2)

theorem emitCones_spec {n : ℕ} (C : Circuit) (words : List (Input n))
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCones C words
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ C.size ≤ result.1.size ∧
      result.1.size ≤ C.size+n*words.length ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      List.Forall₂ (fun u i => i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u ≤ x) words result.2 := by
  induction words generalizing C with
  | nil => exact ⟨basis,reads,le_rfl,by simp [emitCones],rfl,fun _ _ _ => rfl,.nil⟩
  | cons u rest ih =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    obtain ⟨headBasis,headReads,headWire,growth,headCost,headNot,headOld,headValue⟩ :=
      emitCone_spec C u basis reads
    obtain ⟨tailBasis,tailReads,tailGrowth,tailCost,tailNot,tailOld,tailValues⟩ :=
      ih first.1 headBasis headReads
    have headValid : first.2 < nextWire (n+2) later.1 := by
      exact headWire.trans_le (Nat.add_le_add_left tailGrowth (n+2))
    refine ⟨tailBasis,tailReads,growth.trans tailGrowth,?_,tailNot.trans headNot,?_,?_⟩
    · change later.1.size ≤ C.size + n * (u :: rest).length
      rw [List.length_cons,Nat.mul_succ]
      change later.1.size ≤ first.1.size + n*rest.length at tailCost
      change first.1.size ≤ C.size+n at headCost
      omega
    · intro x i hi
      have through : i < nextWire (n+2) first.1 :=
        hi.trans_le (Nat.add_le_add_left growth (n+2))
      exact (tailOld x i through).trans (headOld x i hi)
    · refine .cons ⟨headValid,?_⟩ tailValues
      intro x
      change value later.1 (withConstants x) first.2 = true ↔ u ≤ x
      rw [tailOld x first.2 headWire]
      exact headValue x

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

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

@[local simp] theorem appendFamily_output {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).output = C.output := rfl

theorem appendFamily_notCount {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    notCount (appendFamily C gate) = notCount C +
      ((List.ofFn gate).filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length :=
  appendGates_notCount C _

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

theorem appendFamily_old {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendFamily C gate) x i = value C x i :=
  appendGates_old valid

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

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem appendBinary_prefix (conjunction : Bool) (C : Circuit) (a b : ℕ) :
    C.gates <+: (appendBinary conjunction C a b).gates := by
  cases conjunction
  · exact appendGate_prefix C ⟨.or,[a,b]⟩
  · exact appendGate_prefix C ⟨.and,[a,b]⟩

theorem foldBinary_prefix (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) (indices : List ℕ) :
    C.gates <+: (foldBinary n conjunction C base indices).1.gates := by
  induction indices generalizing C base with
  | nil => exact List.prefix_refl _
  | cons i rest ih =>
    exact (appendBinary_prefix conjunction C base i).trans (ih _ _)

theorem foldBinary_size_exact (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) : (foldBinary n conjunction C base indices).1.size = C.size + indices.length := by
  induction indices generalizing C base with
  | nil => simp [foldBinary]
  | cons i rest ih =>
    have step : (appendBinary conjunction C base i).size = C.size + 1 := by
      cases conjunction <;> simp [appendBinary]
    rw [foldBinary,ih,step,List.length_cons]
    omega

theorem emitCone_prefix {n : ℕ} (C : Circuit) (u : Input n) :
    C.gates <+: (emitCone C u).1.gates := foldBinary_prefix _ _ _ _ _

theorem emitCone_size_exact {n : ℕ} (C : Circuit) (u : Input n) :
    (emitCone C u).1.size = C.size + (coneIndices u).length := foldBinary_size_exact _ _ _ _ _

theorem emitCones_prefix {n : ℕ} (C : Circuit) (words : List (Input n)) :
    C.gates <+: (emitCones C words).1.gates := by
  induction words generalizing C with
  | nil => exact List.prefix_refl _
  | cons u rest ih => exact (emitCone_prefix C u).trans (ih (emitCone C u).1)

theorem emitCones_size_exact {n : ℕ} (C : Circuit) (words : List (Input n)) :
    (emitCones C words).1.size = C.size + (words.map (fun u => (coneIndices u).length)).sum := by
  induction words generalizing C with
  | nil => simp [emitCones]
  | cons u rest ih =>
    change (emitCones (emitCone C u).1 rest).1.size = C.size + _
    rw [ih,emitCone_size_exact,List.map_cons,List.sum_cons]
    omega

theorem supportConeTable {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : {u : Input n // u ∈ support P N} → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      ∀ u, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u.val ≤ x := by
  classical
  let words := (support P N).toList
  let result := emitCones C words
  obtain ⟨newBasis,newReads,_,cost,neg,_,paired⟩ := emitCones_spec C words basis reads
  have available (u : {u : Input n // u ∈ support P N}) :
      ∃ i, i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u.val ≤ x := by
    have member : u.val ∈ words := Finset.mem_toList.mpr u.property
    obtain ⟨j,point⟩ := List.mem_iff_get.mp member
    let k : Fin result.2.length := ⟨j.val,by rw [← paired.length_eq]; exact j.isLt⟩
    refine ⟨result.2.get k,?_⟩
    have atIndex := paired.get j.isLt k.isLt
    change result.2.get k < nextWire (n+2) result.1 ∧
      (∀ x : Input n, value result.1 (withConstants x) (result.2.get k) = true ↔ words.get j ≤ x) at atIndex
    simpa only [point] using atIndex
  refine ⟨result.1,fun u => (available u).choose,emitCones_prefix C words,newBasis,newReads,?_,neg,?_⟩
  · simpa only [words,Finset.length_toList] using cost
  · intro u
    exact (available u).choose_spec

theorem supportConeTable_total {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : Input n → ℕ), C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  classical
  obtain ⟨D,w,extension,newBasis,newReads,cost,neg,semantic⟩ := supportConeTable P N C basis reads
  let wire (u : Input n) : ℕ := if h : u ∈ support P N then w ⟨u,h⟩ else n
  refine ⟨D,wire,extension,newBasis,newReads,cost,neg,?_,?_⟩
  · intro u member
    simpa [wire,member] using semantic ⟨u,member⟩
  · intro u absent
    simp [wire,absent]

theorem supportConeTable_empty {n m : ℕ} (P N : Input n → Fin m → Prop) :
    ∃ (D : Circuit) (wire : Input n → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ n*(support P N).card ∧ notCount D = 0 ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  obtain ⟨D,w,_,basis,reads,cost,neg,semantic,defaultWire⟩ :=
    supportConeTable_total P N emptyCircuit emptyCircuit_fanInTwo (emptyCircuit_readsBack (n+2))
  exact ⟨D,w,basis,reads,by simpa using cost,by simpa using neg,semantic,defaultWire⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem fold_or_true (indices : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    indices.foldl (fun b i => b || bits i) base = true ↔
      base = true ∨ ∃ i ∈ indices, bits i = true := by
  induction indices generalizing base with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons,ih,Bool.or_eq_true_iff]
    constructor
    · rintro ((on | on) | ⟨j,mem,on⟩)
      · exact Or.inl on
      · exact Or.inr ⟨i,List.mem_cons_self ..,on⟩
      · exact Or.inr ⟨j,List.mem_cons_of_mem _ mem,on⟩
    · rintro (on | ⟨j,mem,on⟩)
      · exact Or.inl (Or.inl on)
      · rcases List.mem_cons.mp mem with rfl | restMem
        · exact Or.inl (Or.inr on)
        · exact Or.inr ⟨j,restMem,on⟩

theorem append_or_rows {n k : ℕ} (C : Circuit) (rows : Fin k → List ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (rowValid : ∀ i a, a ∈ rows i → a < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size + (∑ i : Fin k, (rows i).length) ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ a ∈ rows i, value C (withConstants x) a = true := by
  induction k generalizing C with
  | zero =>
    exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    let first := foldBinary (n+2) false C n (rows 0)
    have zeroLive : n < nextWire (n+2) C := by unfold nextWire; omega
    obtain ⟨hBasis,hReads,hLive,hSize,hNot,hEval⟩ :=
      foldBinary_spec (n+2) false C n (rows 0) basis reads zeroLive (rowValid 0)
    have firstPrefix : C.gates <+: first.1.gates := by
      unfold first
      apply foldBinary_prefix
    have tailValid (i : Fin k) (a : ℕ) (ha : a ∈ rows i.succ) :
        a < nextWire (n+2) first.1 :=
      (rowValid i.succ a ha).trans_le (nextWire_le_of_prefix firstPrefix)
    obtain ⟨D,tail,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
      ih first.1 (fun i => rows i.succ) hBasis hReads tailValid
    let out : Fin (k+1) → ℕ := Fin.cases first.2 tail
    refine ⟨D,out,dBasis,dReads,firstPrefix.trans dPrefix,dNot.trans hNot,?_,?_,?_⟩
    · rw [dSize,Fin.sum_univ_succ]
      change first.1.size = C.size + (rows 0).length at hSize
      rw [hSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => dLive j) i
      exact hLive.trans_le (nextWire_le_of_prefix dPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) first.2 = true ↔ _
        have live : first.2 < nextWire (withConstants x).length first.1 := by
          simpa only [withConstants_length] using hLive
        rw [value_of_prefix dPrefix live]
        change value (foldBinary (n+2) false C n (rows 0)).1 (withConstants x)
          (foldBinary (n+2) false C n (rows 0)).2 = true ↔ _
        rw [(hEval (withConstants x) (withConstants_length x)).2,false_value]
        simp only [binaryValue,Bool.false_eq_true,ite_false,fold_or_true,false_or]
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [dEval x j]
        constructor <;> rintro ⟨a,mem,on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).symm.trans on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).trans on⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem value_prefix_input {n : ℕ} {C D : Circuit}
    (extension : C.gates <+: D.gates) (x : Input n) {i : ℕ} (live : i < nextWire (n+2) C) :
    value D (withConstants x) i = value C (withConstants x) i :=
  value_of_prefix extension (by simpa only [withConstants_length] using live)

theorem append_suffix_or {n k : ℕ} (C : Circuit) (bucket : Fin k → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) (live : ∀ i, bucket i < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size+k ∧ (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ j : Fin k, i ≤ j ∧ value C (withConstants x) (bucket j) = true := by
  induction k generalizing C with
  | zero => exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨B,tail,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
      ih C (fun j => bucket j.succ) basis reads (fun j => live j.succ)
    let lower := if reaches : 0 < k then tail ⟨0,reaches⟩ else n
    have lowerLive : lower < nextWire (n+2) B := by
      unfold lower
      split
      · exact bLive _
      · unfold nextWire
        omega
    have lowerEval (x : Input n) : value B (withConstants x) lower = true ↔
        ∃ j : Fin k, value C (withConstants x) (bucket j.succ) = true := by
      unfold lower
      split
      · rename_i positive
        rw [bEval x ⟨0,positive⟩]
        constructor
        · rintro ⟨j,_,on⟩
          exact ⟨j,on⟩
        · rintro ⟨j,on⟩
          exact ⟨j,show (0 : ℕ) ≤ j.val from Nat.zero_le _,on⟩
      · rename_i empty
        rw [false_value]
        constructor
        · intro impossible
          contradiction
        · rintro ⟨j,_⟩
          exact (empty (Nat.zero_lt_of_lt j.isLt)).elim
    let D := appendOr B (bucket 0) lower
    let out : Fin (k+1) → ℕ := Fin.cases (nextWire (n+2) B) tail
    have headLive := (live 0).trans_le (nextWire_le_of_prefix bPrefix)
    have lastPrefix : B.gates <+: D.gates := appendGate_prefix _ _
    have wireGrowth : nextWire (n+2) D = nextWire (n+2) B + 1 := nextWire_appendGate _ _ _
    refine ⟨D,out,appendOr_fanInTwo bBasis,appendOr_readsBack bReads headLive lowerLive,
      bPrefix.trans lastPrefix,(appendOr_notCount _ _ _).trans bNot,?_,?_,?_⟩
    · change (appendOr B (bucket 0) lower).size = C.size + (k+1)
      rw [appendOr_size,bSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change nextWire (n+2) B < nextWire (n+2) D
        omega
      · exact (bLive j).trans_le (nextWire_le_of_prefix lastPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) (nextWire (n+2) B) = true ↔
          ∃ j : Fin (k+1), 0 ≤ j ∧ value C (withConstants x) (bucket j) = true
        have evaluated := appendOr_new B (withConstants x) (bucket 0) lower
        simp only [withConstants_length] at evaluated
        rw [show value D (withConstants x) (nextWire (n+2) B) = _ from evaluated,
          Bool.or_eq_true_iff,value_prefix_input bPrefix x (live 0),lowerEval x]
        constructor
        · rintro (head | ⟨j,tailOn⟩)
          · exact ⟨0,le_rfl,head⟩
          · exact ⟨j.succ,show (0 : ℕ) ≤ j.succ.val from Nat.zero_le _,tailOn⟩
        · rintro ⟨j,_,on⟩
          refine Fin.cases ?_ (fun q => ?_) j on
          · exact Or.inl
          · intro tailOn
            exact Or.inr ⟨q,tailOn⟩
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [value_prefix_input lastPrefix x (bLive j),bEval x j]
        constructor
        · rintro ⟨i,order,on⟩
          exact ⟨i.succ,Fin.succ_le_succ_iff.mpr order,on⟩
        · rintro ⟨i,order,on⟩
          refine Fin.cases ?_ (fun q => ?_) i order on
          · intro incompatible _
            change j.val+1 ≤ 0 at incompatible
            omega
          · intro comparable active
            exact ⟨q,Fin.succ_le_succ_iff.mp comparable,active⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def bucketRows {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) (i : Fin d) : List ℕ :=
  (rankBucket P N d (i.val+1)).toList.map cone

private theorem positive_bucket_cost {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) :
    (∑ i : Fin d, (bucketRows P N d cone i).length) ≤ (support P N).card := by
  have total : (∑ i : Fin (d+1), (rankBucket P N d i.val).card) = (support P N).card :=
    (Fin.sum_univ_eq_sum_range (fun k => (rankBucket P N d k).card) (d+1)).trans (rank_bucket_count P N d)
  rw [Fin.sum_univ_succ] at total
  have bound : (∑ i : Fin d, (rankBucket P N d (i.val+1)).card) ≤ (support P N).card :=
    (Nat.le_add_left _ _).trans total.le
  simpa [bucketRows] using bound

theorem append_thresholds {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ) (C : Circuit)
    (cone : Input n → ℕ) (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneLive : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n,
      value C (withConstants x) (cone u) = true ↔ u ≤ x) :
    ∃ (D : Circuit) (out : Fin d → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+d ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x := by
  let rows := bucketRows P N d cone
  have liveRows (i : Fin d) (a : ℕ) (hm : a ∈ rows i) : a < nextWire (n+2) C := by
    obtain ⟨u,mem,rfl⟩ := List.mem_map.mp hm
    exact coneLive u ((mem_rankBucket P N d (i.val+1) u).mp (Finset.mem_toList.mp mem)).1
  obtain ⟨B,bucket,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
    append_or_rows C rows basis reads liveRows
  have bucketEval (x : Input n) (i : Fin d) :
      value B (withConstants x) (bucket i) = true ↔ ∃ u ∈ rankBucket P N d (i.val+1), u ≤ x := by
    rw [bEval x i]
    constructor
    · rintro ⟨a,found,on⟩
      obtain ⟨u,mem,rfl⟩ := List.mem_map.mp found
      have occurrence := Finset.mem_toList.mp mem
      have original := ((mem_rankBucket P N d (i.val+1) u).mp occurrence).1
      exact ⟨u,occurrence,(coneValue u original x).mp on⟩
    · rintro ⟨u,mem,ux⟩
      have original := ((mem_rankBucket P N d (i.val+1) u).mp mem).1
      exact ⟨cone u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr mem,rfl⟩,
        (coneValue u original x).mpr ux⟩
  obtain ⟨D,out,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
    append_suffix_or B bucket bBasis bReads bLive
  refine ⟨D,out,dBasis,dReads,bPrefix.trans dPrefix,dNot.trans bNot,?_,dLive,?_⟩
  · have budget : (∑ i : Fin d, (rows i).length) ≤ (support P N).card :=
      positive_bucket_cost P N d cone
    rw [dSize,bSize]
    omega
  · intro x i
    rw [dEval x i,threshold_buckets P N d (by omega : 0 < i.val+1) x]
    constructor
    · rintro ⟨j,ij,on⟩
      have below : i.val ≤ j.val := ij
      obtain ⟨u,mem,ux⟩ := (bucketEval x j).mp on
      exact ⟨j.val+1,by omega,by omega,u,mem,ux⟩
    · rintro ⟨k,ik,kd,u,mem,ux⟩
      let j : Fin d := ⟨k-1,by omega⟩
      have level : j.val+1 = k := by dsimp [j]; omega
      refine ⟨j,show i.val ≤ j.val from by omega,(bucketEval x j).mpr ?_⟩
      rw [level]
      exact ⟨u,mem,ux⟩

theorem threshold_antitone {n m d : ℕ} {P N : Input n → Fin m → Prop} {D : Circuit}
    {out : Fin d → ℕ}
    (sem : ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x)
    (x : Input n) : Antitone (fun i => value D (withConstants x) (out i)) := by
  intro i j ij
  change value D (withConstants x) (out j) ≤ value D (withConstants x) (out i)
  have below : i.val ≤ j.val := ij
  cases high : value D (withConstants x) (out j)
  · simp
  · have low : value D (withConstants x) (out i) = true :=
      (sem x i).mpr (by have reach := (sem x j).mp high; omega)
    rw [low]

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)
open Thermometer (half middle pivot lowerSource upperSource lowerSlot upperSlot
  lowerWord upperWord folded folded_antitone decoded decoded_lower decoded_pivot decoded_upper
  decoded_correct half_lt_pow)

private theorem old_value {n : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates)
    {x : List Bool} (length : x.length = n) {w : ℕ} (live : w < nextWire n C) :
    value D x w = value C x w :=
  value_of_prefix ext (by simpa only [length] using live)

private theorem pair_reads {n : ℕ} {C : Circuit} {a b : ℕ}
    (la : a < nextWire n C) (lb : b < nextWire n C) :
    ∀ i ∈ [a,b], i < nextWire n C := by
  intro i member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact la
  · exact lb

private theorem family_value {k n : ℕ} {C : Circuit} {gate : Fin k → Gate}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C)
    (x : List Bool) (length : x.length = n) (j : Fin k) :
    value (appendFamily C gate) x (nextWire n C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have valid : ∀ a b, b ∈ (gate a).inputs → b < nextWire x.length C := by
    rw [length]
    exact reads
  simpa only [length] using appendFamily_new (C := C) (gate := gate) (x := x) valid j

set_option maxHeartbeats 1700000 in
private theorem fold_taps {X : Type*} (input : X → List Bool) {n d : ℕ}
    (length : ∀ x, (input x).length = n) (positive : 0 < d) {C : Circuit}
    (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C) :
    ∃ (D : Circuit) (pivotWire : ℕ) (wires : Fin (half d) → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D ∧
      pivotWire < nextWire n D ∧ (∀ i, wires i < nextWire n D) ∧
      (∀ x, value D (input x) pivotWire = !value C (input x) (taps (pivot positive))) ∧
      (∀ x i, value D (input x) (wires i) =
        folded positive (fun j => value C (input x) (taps j)) i) ∧
      D.size = C.size + 1 + 2 * half d ∧ notCount D = notCount C + 1 := by
  let C0 := appendNot C (taps (pivot positive))
  let b := nextWire n C
  let low (i : Fin (half d)) := if i.val < middle d then taps (lowerSource i) else falseWire
  let ands (i : Fin (half d)) : Gate := ⟨.and,[b,low i]⟩
  let C1 := appendFamily C0 ands
  let mask (i : Fin (half d)) := nextWire n C0 + i.val
  let ors (i : Fin (half d)) : Gate := ⟨.or,[mask i,taps (upperSource positive i)]⟩
  let C2 := appendFamily C1 ors
  let output (i : Fin (half d)) := nextWire n C1 + i.val
  have e0 : C.gates <+: C0.gates := appendGate_prefix C _
  have e1 : C0.gates <+: C1.gates := appendFamily_prefix C0 ands
  have e2 : C1.gates <+: C2.gates := appendFamily_prefix C1 ors
  have e01 := e0.trans e1
  have e012 := e01.trans e2
  have bLive : b < nextWire n C0 := by
    simp [b,C0,appendNot]
  have lowLive (i : Fin (half d)) : low i < nextWire n C0 := by
    apply Nat.lt_of_lt_of_le _ (nextWire_le_of_prefix e0)
    unfold low
    split
    · exact live _
    · exact falseLive
  have andReads : ∀ j i, i ∈ (ands j).inputs → i < nextWire n C0 :=
    fun j => pair_reads bLive (lowLive j)
  have maskLive (i : Fin (half d)) : mask i < nextWire n C1 := by
    simpa only [mask,C1,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  have orReads : ∀ j i, i ∈ (ors j).inputs → i < nextWire n C1 :=
    fun j => pair_reads (maskLive j) ((live _).trans_le (nextWire_le_of_prefix e01))
  have f0 : FanInTwo C0 := appendNot_fanInTwo fan
  have f1 : FanInTwo C1 := appendFamily_fanInTwo (gate := ands) f0 (by
    intro j
    change GateOp.and ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([b,low j] : List ℕ).length ≤ 2
    simp)
  have f2 : FanInTwo C2 := appendFamily_fanInTwo (gate := ors) f1 (by
    intro j
    change GateOp.or ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([mask j,taps (upperSource positive j)] : List ℕ).length ≤ 2
    simp)
  have r0 : ReadsBack n C0 := appendNot_readsBack back (live (pivot positive))
  have r1 : ReadsBack n C1 := appendFamily_readsBack r0 andReads
  have r2 : ReadsBack n C2 := appendFamily_readsBack r1 orReads
  have atPivot (x : X) : value C0 (input x) b = !value C (input x) (taps (pivot positive)) := by
    simpa only [C0,b,length x] using appendNot_new C (input x) (taps (pivot positive))
  have foldOn (x : X) (i : Fin (half d)) : value C2 (input x) (output i) =
      folded positive (fun j => value C (input x) (taps j)) i := by
    let w : Fin d → Bool := fun j => value C (input x) (taps j)
    have lowOn : value C0 (input x) (low i) = lowerWord w i := by
      by_cases before : i.val < middle d
      · simp only [low,lowerWord,ite_eq_left before]
        exact old_value e0 (length x) (live (lowerSource i))
      · simp only [low,lowerWord,ite_eq_right before]
        exact (old_value e0 (length x) falseLive).trans (falseValue x)
    have maskOn : value C1 (input x) (mask i) = (!w (pivot positive) && lowerWord w i) := by
      have eq := family_value (gate := ands) andReads (input x) (length x) i
      simpa [C1,mask,ands,GateOp.eval,atPivot x,lowOn,w] using eq
    have upperOn : value C1 (input x) (taps (upperSource positive i)) = upperWord positive w i :=
      old_value e01 (length x) (live (upperSource positive i))
    have eq := family_value (gate := ors) orReads (input x) (length x) i
    simpa [C2,output,ors,GateOp.eval,maskOn,upperOn,folded,w] using eq
  refine ⟨C2,b,output,e012,f2,r2,bLive.trans_le (nextWire_le_of_prefix (e1.trans e2)),
    ?_,?_,foldOn,?_,?_⟩
  · intro i
    simpa only [output,C2,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  · intro x
    exact (old_value (e1.trans e2) (length x) bLive).trans (atPivot x)
  · dsimp only [C2,C1,C0]
    simp only [appendFamily_size,appendNot_size]
    omega
  · rw [show C2 = appendFamily C1 ors from rfl,
      appendFamily_notCount_eq (gate := ors) (by intro j; simp [ors]),
      show C1 = appendFamily C0 ands from rfl,
      appendFamily_notCount_eq (gate := ands) (by intro j; simp [ands])]
    simp [C0]

private def decoderGates {d : ℕ} (positive : 0 < d) (b falseWire : ℕ)
    (tail : Fin (half d) → ℕ) (i : Fin d) : Gate :=
  if before : i.val < middle d then ⟨.and,[b,tail (lowerSlot i before)]⟩
  else if eq : i.val = middle d then ⟨.or,[b,falseWire]⟩
  else ⟨.or,[b,tail (upperSlot positive i (by omega))]⟩

private theorem decoder_reads {n d : ℕ} (positive : 0 < d) {C : Circuit} {b f : ℕ}
    {tail : Fin (half d) → ℕ} (liveB : b < nextWire n C) (liveF : f < nextWire n C)
    (liveTail : ∀ j, tail j < nextWire n C) :
    ∀ j i, i ∈ (decoderGates positive b f tail j).inputs → i < nextWire n C := by
  intro j i member
  unfold decoderGates at member
  split at member
  · exact pair_reads liveB (liveTail _) i member
  · split at member
    · exact pair_reads liveB liveF i member
    · exact pair_reads liveB (liveTail _) i member

private theorem decoder_value {d : ℕ} (positive : 0 < d) (C : Circuit) (x : List Bool)
    (b f : ℕ) (tail : Fin (half d) → ℕ) (off : value C x f = false) (i : Fin d) :
    let g := decoderGates positive b f tail i
    g.op.eval (g.inputs.map (value C x)) =
      decoded positive (value C x b) (fun j => value C x (tail j)) i := by
  rcases lt_trichotomy i.val (middle d) with before | eq | after
  · rw [decoded_lower positive _ _ _ before]
    simp [decoderGates,before,GateOp.eval]
  · rw [decoded_pivot positive _ _ _ eq]
    simp [decoderGates,eq,off,GateOp.eval]
  · have lower : ¬ i.val < middle d := by omega
    have other : i.val ≠ middle d := by omega
    rw [decoded_upper positive _ _ _ after]
    simp [decoderGates,lower,other,GateOp.eval]

def InversionResult {X : Type*} (input : X → List Bool) (n r : ℕ)
    (C : Circuit) {d : ℕ} (taps : Fin d → ℕ) :=
  {data : Circuit × (Fin d → ℕ) × ℕ × ℕ //
    let D := data.1
    let output := data.2.1
    let binary := data.2.2.1
    let inversions := data.2.2.2
    (C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D) ∧
    (∀ i, output i < nextWire n D) ∧
    (binary ≤ 4*d ∧ inversions ≤ r) ∧
    (D.size = C.size + binary + inversions ∧ notCount D = notCount C + inversions) ∧
    ∀ x i, value D (input x) (output i) = !value C (input x) (taps i)}

namespace InversionResult

variable {X : Type*} {input : X → List Bool} {n r d : ℕ}
  {C : Circuit} {taps : Fin d → ℕ}

abbrev circuit (R : InversionResult input n r C taps) : Circuit := R.val.1

abbrev wires (R : InversionResult input n r C taps) : Fin d → ℕ := R.val.2.1

abbrev binary (R : InversionResult input n r C taps) : ℕ := R.val.2.2.1

abbrev inversions (R : InversionResult input n r C taps) : ℕ := R.val.2.2.2

theorem extension (R : InversionResult input n r C taps) : C.gates <+: R.circuit.gates :=
  R.property.1.1

theorem fanInTwo (R : InversionResult input n r C taps) : FanInTwo R.circuit :=
  R.property.1.2.1

theorem readsBack (R : InversionResult input n r C taps) : ReadsBack n R.circuit :=
  R.property.1.2.2

theorem valid (R : InversionResult input n r C taps) : ∀ i, R.wires i < nextWire n R.circuit :=
  R.property.2.1

theorem binaryBound (R : InversionResult input n r C taps) : R.binary ≤ 4*d :=
  R.property.2.2.1.1

theorem inversionsBound (R : InversionResult input n r C taps) : R.inversions ≤ r :=
  R.property.2.2.1.2

theorem size_eq (R : InversionResult input n r C taps) :
    R.circuit.size = C.size + R.binary + R.inversions := R.property.2.2.2.1.1

theorem count_eq (R : InversionResult input n r C taps) :
    notCount R.circuit = notCount C + R.inversions := R.property.2.2.2.1.2

theorem computes (R : InversionResult input n r C taps) :
    ∀ x i, value R.circuit (input x) (R.wires i) = !value C (input x) (taps i) :=
  R.property.2.2.2.2

end InversionResult

theorem InversionResult.nonnot_eq {X : Type*} {input : X → List Bool} {n r d : ℕ}
    {C : Circuit} {taps : Fin d → ℕ} (R : InversionResult input n r C taps) :
    R.circuit.size - notCount R.circuit = C.size - notCount C + R.binary := by
  have fits : notCount C ≤ C.size := List.length_filter_le _ _
  rw [R.size_eq,R.count_eq]
  omega

private theorem empty_inversion {X : Type*} (input : X → List Bool) {n r : ℕ}
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C) (taps : Fin 0 → ℕ) :
    Nonempty (InversionResult input n r C taps) := by
  exact ⟨⟨⟨C,taps,0,0⟩,⟨⟨List.prefix_rfl,fan,back⟩,fun i => Fin.elim0 i,
    ⟨by simp,by simp⟩,⟨rfl,rfl⟩,fun _ i => Fin.elim0 i⟩⟩⟩

set_option maxHeartbeats 2000000 in

theorem invert_taps {X : Type*} (input : X → List Bool) {n : ℕ}
    (length : ∀ x, (input x).length = n) {r d : ℕ} (bound : d < 2^r)
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C)
    (ordered : ∀ x, Antitone (fun i => value C (input x) (taps i))) :
    Nonempty (InversionResult input n r C taps) := by
  induction r generalizing d C with
  | zero =>
    have empty : d = 0 := by simpa using bound
    subst d
    exact empty_inversion input fan back taps
  | succ r ih =>
    by_cases positive : 0 < d
    · obtain ⟨F,pivotWire,foldWires,fExt,fFan,fBack,pivotValid,fValid,pivotValue,foldValue,fSize,fCount⟩ :=
        fold_taps input length positive fan back falseWire falseLive falseValue taps live
      have falseF := falseLive.trans_le (nextWire_le_of_prefix (n := n) fExt)
      have offF (x : X) : value F (input x) falseWire = false :=
        (old_value fExt (length x) falseLive).trans (falseValue x)
      have foldOrdered (x : X) : Antitone (fun i => value F (input x) (foldWires i)) := by
        rw [funext (foldValue x)]
        exact folded_antitone positive (ordered x)
      obtain ⟨R⟩ := ih (half_lt_pow bound) fFan fBack falseF offF foldWires fValid foldOrdered
      let gates := decoderGates positive pivotWire falseWire R.wires
      let D := appendFamily R.circuit gates
      let output (i : Fin d) := nextWire n R.circuit + i.val
      have step := appendFamily_prefix R.circuit gates
      have preserve := nextWire_le_of_prefix (n := n) R.extension
      have reads := decoder_reads positive (pivotValid.trans_le preserve)
        (falseF.trans_le preserve) R.valid
      have noNot : ∀ j, (gates j).op ≠ .not := by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ≠ .not
        unfold decoderGates
        split
        · simp
        · split <;> simp
      have basis : FanInTwo D := appendFamily_fanInTwo (gate := gates) R.fanInTwo (by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ∈
          ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
          (decoderGates positive pivotWire falseWire R.wires j).inputs.length ≤ 2
        unfold decoderGates
        split
        · simp
        · split <;> simp)
      refine ⟨⟨⟨D,output,2*half d+R.binary+d,1+R.inversions⟩,
        ⟨⟨fExt.trans (R.extension.trans step),basis,appendFamily_readsBack R.readsBack reads⟩,
          ?_,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩⟩⟩
      · intro i
        simpa only [D,output,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
      · change 2*half d + R.binary + d ≤ 4*d
        have rhs := R.binaryBound
        have halfBound : 2*half d ≤ d := by unfold half; omega
        omega
      · change 1 + R.inversions ≤ r + 1
        have rhs := R.inversionsBound
        omega
      · change D.size = C.size + (2*half d + R.binary + d) + (1 + R.inversions)
        rw [show D.size = R.circuit.size + d from appendFamily_size _ _, R.size_eq,fSize]
        omega
      · change notCount D = notCount C + (1 + R.inversions)
        rw [show notCount D = notCount R.circuit from appendFamily_notCount_eq noNot,R.count_eq,fCount]
        omega
      · intro x i
        have pivotOn : value R.circuit (input x) pivotWire =
            !value C (input x) (taps (pivot positive)) :=
          (old_value R.extension (length x) pivotValid).trans (pivotValue x)
        have off : value R.circuit (input x) falseWire = false :=
          (old_value R.extension (length x) falseF).trans (offF x)
        have tailOn (j : Fin (half d)) : value R.circuit (input x) (R.wires j) =
            !(folded positive (fun k => value C (input x) (taps k)) j) := by
          rw [R.computes,foldValue]
        have bits := family_value (gate := gates) reads (input x) (length x) i
        change value D (input x) (output i) = _ at bits
        rw [bits,decoder_value positive _ _ _ _ _ off,pivotOn]
        exact decoded_correct positive (ordered x) tailOn i
    · have empty : d = 0 := by omega
      subst d
      exact empty_inversion input fan back taps

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def ceilingWire {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (complement : Fin d → ℕ) (u : Input n) : ℕ :=
  if below : rank P N d u < d then complement ⟨rank P N d u,below⟩ else n+1

private theorem ceilingWire_valid {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ) (u : Input n)
    (valid : ∀ i, complement i < nextWire (n+2) C) :
    ceilingWire P N complement u < nextWire (n+2) C := by
  unfold ceilingWire
  split
  · exact valid _
  · unfold nextWire
    omega

private theorem ceilingWire_value {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ)
    (sem : ∀ (i : Fin d) (x : Input n), value C (withConstants x) (complement i) = true ↔
      ¬ i.val+1 ≤ rank P N d x) (u x : Input n) :
    value C (withConstants x) (ceilingWire P N complement u) = true ↔
      ¬ rank P N d u+1 ≤ rank P N d x := by
  unfold ceilingWire
  split
  · exact sem _ x
  · rename_i notBelow
    have atTop : rank P N d u = d := by
      have cap := rank_bound P N d u
      omega
    have noHigher : ¬ rank P N d u+1 ≤ rank P N d x := by
      rw [atTop]
      have cap := rank_bound P N d x
      omega
    exact ⟨fun _ => noHigher,fun _ => true_value C x⟩

set_option maxHeartbeats 1400000 in

theorem append_taps {n m d : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (cone : Input n → ℕ) (complement : Fin d → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneValid : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n, value C (withConstants x) (cone u) = true ↔ u ≤ x)
    (complementValid : ∀ i, complement i < nextWire (n+2) C)
    (complementValue : ∀ (i : Fin d) (x : Input n),
      value C (withConstants x) (complement i) = true ↔ ¬ i.val+1 ≤ rank P N d x)
    (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    ∃ (D : Circuit) (tap : Fin m → Fin (n+2+D.size)),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+(positivePairs P).card ∧
      ∀ (x : Input n) (j : Fin m),
        (P x j → value D (withConstants x) (tap j).val = true) ∧
        (N x j → value D (withConstants x) (tap j).val = false) := by
  classical
  let words := (support P N).toList
  let gate (i : Fin words.length) : Gate := ⟨.and,[cone words[i],ceilingWire P N complement words[i]]⟩
  let guarded := appendFamily C gate
  let term (u : Input n) : ℕ := nextWire (n+2) C + words.idxOf u
  have gateReads (i : Fin words.length) (wire : ℕ) (used : wire ∈ (gate i).inputs) :
      wire < nextWire (n+2) C := by
    have present : words[i] ∈ support P N := Finset.mem_toList.mp (List.getElem_mem i.isLt)
    change wire ∈ [cone words[i],ceilingWire P N complement words[i]] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl | rfl
    · exact coneValid _ present
    · exact ceilingWire_valid P N C complement _ complementValid
  have guardedBasis : FanInTwo guarded := by
    apply appendFamily_fanInTwo basis
    intro i
    change GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (2 : ℕ) ≤ 2
    simp
  have guardedReads : ReadsBack (n+2) guarded := appendFamily_readsBack (gate := gate) reads gateReads
  have guardedCost : guarded.size = C.size+(support P N).card := by simp [guarded,words]
  have guardedNot : notCount guarded = notCount C := by
    apply appendFamily_notCount_eq
    intro i
    simp [gate]
  have termValid (u : Input n) (present : u ∈ support P N) : term u < nextWire (n+2) guarded := by
    have found : words.idxOf u < words.length := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)
    change nextWire (n+2) C + words.idxOf u < nextWire (n+2) (appendFamily C gate)
    rw [appendFamily_nextWire]
    exact Nat.add_lt_add_left found _
  have termValue (u : Input n) (present : u ∈ support P N) (x : Input n) :
      value guarded (withConstants x) (term u) = true ↔ guardedCone P N d u x := by
    let i : Fin words.length := ⟨words.idxOf u,List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)⟩
    have point : words[i] = u := List.getElem_idxOf i.isLt
    have evaluated := appendFamily_new (C := C) (gate := gate) (x := withConstants x)
      (by simpa only [withConstants_length] using gateReads) i
    rw [withConstants_length] at evaluated
    have equation : value guarded (withConstants x) (term u) =
      (value C (withConstants x) (cone words[i]) &&
        value C (withConstants x) (ceilingWire P N complement words[i])) := by
      simpa [guarded,term,i,gate,GateOp.eval] using evaluated
    rw [point] at equation
    change value guarded (withConstants x) (term u) = true ↔
      u ≤ x ∧ ¬ rank P N d u+1 ≤ rank P N d x
    rw [equation,Bool.and_eq_true,coneValue u present x,
      ceilingWire_value P N C complement complementValue u x]
  let rows (j : Fin m) : List ℕ := (positiveInputs P j).toList.map term
  have validRows : ∀ (j : Fin m) a, a ∈ rows j → a < nextWire (n+2) guarded := by
    intro j a member
    obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
    exact termValid u (positive_input_support P N (Finset.mem_toList.mp present))
  obtain ⟨D,out,finalBasis,finalReads,finalPrefix,finalNot,finalSize,outValid,outValue⟩ :=
    append_or_rows guarded rows guardedBasis guardedReads validRows
  have rowCost : (∑ j : Fin m, (rows j).length) = (positivePairs P).card := by
    simpa [rows] using positive_incidence_count P
  have realized (x : Input n) (j : Fin m) :
      value D (withConstants x) (out j) = true ↔ tapAccepts P N d x j := by
    rw [outValue]
    constructor
    · rintro ⟨a,member,active⟩
      obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
      have positive := Finset.mem_toList.mp present
      exact ⟨u,positive,(termValue u (positive_input_support P N positive) x).mp active⟩
    · rintro ⟨u,positive,active⟩
      exact ⟨term u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr positive,rfl⟩,
        (termValue u (positive_input_support P N positive) x).mpr active⟩
  let taps (j : Fin m) : Fin (n+2+(withOutput D 0).size) := ⟨out j,outValid j⟩
  refine ⟨withOutput D 0,taps,finalBasis,finalReads,?_,
    (appendFamily_prefix C gate).trans finalPrefix,finalNot.trans guardedNot,?_,?_⟩
  · simp only [withOutput_output,withOutput_size]
    omega
  · rw [withOutput_size,finalSize,guardedCost,rowCost]
  · intro x j
    change (P x j → value D (withConstants x) (out j) = true) ∧
      (N x j → value D (withConstants x) (out j) = false)
    refine ⟨fun positive => (realized x j).mpr (tap_accepts_positive P N d positive),?_⟩
    intro negative
    exact Bool.eq_false_iff.mpr fun active =>
      tap_rejects_negative P N bounded negative ((realized x j).mp active)

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def Fits {n m : ℕ} (P N : Input n → Fin m → Prop) (r : ℕ) (cost : ℕ → Prop) : Prop :=
  ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
    FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧ notCount C ≤ r ∧
    cost (C.size-notCount C) ∧ ∀ (x : Input n) (j : Fin m),
      (P x j → value C (withConstants x) (tap j).val = true) ∧
      (N x j → value C (withConstants x) (tap j).val = false)

theorem upper_fits {n m r d : ℕ} (P N : Input n → Fin m → Prop)
    (bound : d < 2^r) (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  obtain ⟨A,cone,aBasis,aReads,aSize,aNot,aSem,_⟩ := supportConeTable_empty P N
  obtain ⟨B,thresholds,bBasis,bReads,bExtends,bNot,bSize,bLive,bSem⟩ :=
    append_thresholds P N d A cone aBasis aReads
      (fun u hu => (aSem u hu).1) (fun u hu => (aSem u hu).2)
  have falseLive : n < nextWire (n+2) B := by unfold nextWire; omega
  obtain ⟨I⟩ := invert_taps (withConstants (n := n)) withConstants_length bound
    bBasis bReads n falseLive (false_value B) thresholds bLive (threshold_antitone bSem)
  have extension : A.gates <+: I.circuit.gates := bExtends.trans I.extension
  have coneLive (u : Input n) (hu : u ∈ support P N) :
      cone u < nextWire (n+2) I.circuit :=
    (aSem u hu).1.trans_le (nextWire_le_of_prefix extension)
  have coneValue (u : Input n) (hu : u ∈ support P N) (x : Input n) :
      value I.circuit (withConstants x) (cone u) = true ↔ u ≤ x := by
    have live : cone u < nextWire (withConstants x).length A := by
      rw [withConstants_length]
      exact (aSem u hu).1
    rw [value_of_prefix extension live]
    exact (aSem u hu).2 x
  have complementValue (i : Fin d) (x : Input n) :
      value I.circuit (withConstants x) (I.wires i) = true ↔ ¬ i.val+1 ≤ rank P N d x := by
    rw [I.computes, ← bSem x i]
    cases value B (withConstants x) (thresholds i) <;> decide
  obtain ⟨C,tap,cBasis,cReads,cOut,_,cNot,cSize,labels⟩ :=
    append_taps P N I.circuit cone I.wires I.fanInTwo I.readsBack
      coneLive coneValue I.valid complementValue bounded
  have bZero : notCount B = 0 := bNot.trans aNot
  have cInversions : notCount C = I.inversions := by
    rw [cNot,I.count_eq,bZero,Nat.zero_add]
  have cBinary : C.size-notCount C ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d := by
    have inversionSize := I.size_eq
    have binaryBudget := I.binaryBound
    rw [cInversions,Nat.add_mul]
    omega
  exact ⟨C,tap,cBasis,cReads,cOut,cInversions.le.trans I.inversionsBound,cBinary,labels⟩

theorem solve_fall_1228 (n m r : ℕ) (P N : Input n → Fin m → Prop) :
    (Fits P N r (fun _ => True) ↔ ∀ x, ¬ Reach P N (2^r) x) ∧
    ∀ d : ℕ, d < 2^r → (∀ x, ¬ Reach P N (d+1) x) →
      Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  constructor
  · constructor
    · rintro ⟨C,tap,basis,_,_,budget,_,labels⟩
      exact no_packing_of_taps (fun j => (tap j).val) basis budget labels
    · intro bounded
      have positive : 0 < (2:ℕ)^r := Nat.pow_pos (by decide)
      have below : (2:ℕ)^r-1 < 2^r := by omega
      have successor : (2:ℕ)^r-1+1 = 2^r := by omega
      have bounded' : ∀ x, ¬ Reach P N ((2:ℕ)^r-1+1) x := by simpa only [successor] using bounded
      obtain ⟨C,tap,basis,reads,output,budget,_,labels⟩ := upper_fits P N below bounded'
      exact ⟨C,tap,basis,reads,output,budget,True.intro,labels⟩
  · intro d bound bounded
    exact upper_fits P N bound bounded

theorem crit1228 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m r : Nat) (P N : (Fin n → Bool) → Fin m → Prop),
  let X := Fin n → Bool
  let reach := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)
  let S := (Finset.univ.filter (fun x : X => ∃ j, P x j ∨ N x j)).card
  let L := (Finset.univ.filter (fun z : X × Fin m => P z.1 z.2)).card
  let fits := fun (cost : Nat → Prop) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      cost (C.size-PEqualNP.NotBracket.notCount C) ∧ ∀ (x : X) (j : Fin m),
        let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j).val false
        (P x j → w=true) ∧ (N x j → w=false)
  (fits (fun _ => True) ↔ ∀ x, ¬ reach (2^r) x) ∧
    ∀ d : Nat, d < 2^r → (∀ x, ¬ reach (d+1) x) →
      fits (fun b => b ≤ (n+2)*S + L + 5*d)) := by
  intro n m r P N
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  have support_eq : (Finset.univ.filter (fun x : Fin n → Bool => ∃ j, P x j ∨ N x j)) =
      PEqualNP.Outside.L_lib_1401_aux.Source.support P N := by
    ext x
    simp [PEqualNP.Outside.L_lib_1401_aux.Source.mem_support]
  have pairs_eq : (Finset.univ.filter (fun z : (Fin n → Bool) × Fin m => P z.1 z.2)) =
      PEqualNP.Outside.L_lib_1401_aux.Source.positivePairs P := by
    ext z
    simp [PEqualNP.Outside.L_lib_1401_aux.Source.mem_positivePairs]
  dsimp only
  rw [support_eq, pairs_eq]
  exact PEqualNP.Outside.L_lib_1401_aux.Source.solve_fall_1228 n m r P N

end PEqualNP.Outside.L_lib_1401_aux.Source

namespace PEqualNP.Outside.L_lib_1401_aux.Source

def R94 {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) : Nat → (Fin d → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin d → Bool) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)

theorem r94_succ {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) (k : Nat) (x : Fin d → Bool) :
    R94 P N (k+1) x ↔ ∃ u v j, R94 P N k u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j := Iff.rfl

theorem r94_zero {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) (x : Fin d → Bool) :
    R94 P N 0 x := trivial

theorem r94_mono {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) :
    ∀ k (x y : Fin d → Bool), R94 P N k x → x ≤ y → R94 P N k y
  | 0, _, y, _, _ => r94_zero P N y
  | k+1, x, y, h, hxy => by
    obtain ⟨u, v, j, h1, h2, h3, h4, h5⟩ := (r94_succ P N k x).1 h
    exact (r94_succ P N k y).2 ⟨u, v, j, h1, h2, le_trans h3 hxy, h4, h5⟩

theorem chain_reach {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (ys : A → Fin t → Bool) (K : Nat)
    (a b : Fin K → A)
    (h1 : ∀ i, xs (a i) ≤ xs (b i) ∧ ∃ j, ys (a i) j=true ∧ ys (b i) j=false)
    (h2 : ∀ i j : Fin K, i.val+1=j.val → xs (b i) ≤ xs (a j)) :
    ∀ k (hk : k < K), R94 (fun u j => ∃ i, xs i = u ∧ ys i j = true)
      (fun u j => ∃ i, xs i = u ∧ ys i j = false) (k+1) (xs (b ⟨k,hk⟩))
  | 0, hk => by
    obtain ⟨hle, j, hj1, hj2⟩ := h1 ⟨0,hk⟩
    exact (r94_succ _ _ 0 _).2 ⟨xs (a ⟨0,hk⟩), xs (b ⟨0,hk⟩), j, r94_zero _ _ _, hle, le_refl _,
      ⟨_, rfl, hj1⟩, ⟨_, rfl, hj2⟩⟩
  | k+1, hk => by
    have ih := chain_reach xs ys K a b h1 h2 k (by omega)
    obtain ⟨hle, j, hj1, hj2⟩ := h1 ⟨k+1,hk⟩
    exact (r94_succ _ _ (k+1) _).2 ⟨xs (a ⟨k+1,hk⟩), xs (b ⟨k+1,hk⟩), j,
      r94_mono _ _ _ _ _ ih (h2 ⟨k, by omega⟩ ⟨k+1,hk⟩ rfl), hle, le_refl _,
      ⟨_, rfl, hj1⟩, ⟨_, rfl, hj2⟩⟩

theorem reach_chain {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (ys : A → Fin t → Bool) :
    ∀ k x, R94 (fun u j => ∃ i, xs i = u ∧ ys i j = true)
      (fun u j => ∃ i, xs i = u ∧ ys i j = false) k x →
    ∃ a b : Fin k → A, (∀ i, xs (a i) ≤ xs (b i) ∧ ∃ j, ys (a i) j=true ∧ ys (b i) j=false) ∧
      (∀ i j : Fin k, i.val+1=j.val → xs (b i) ≤ xs (a j)) ∧ ∀ i, xs (b i) ≤ x
  | 0, x, _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | k+1, x, h => by
    obtain ⟨u, v, j, hr, huv, hvx, ⟨i1, hi1, hj1⟩, ⟨i2, hi2, hj2⟩⟩ := (r94_succ _ _ k x).1 h
    obtain ⟨a, b, ha, hab, hb⟩ := reach_chain xs ys k u hr
    subst hi1; subst hi2
    refine ⟨fun i => if hi : i.val < k then a ⟨i, hi⟩ else i1,
      fun i => if hi : i.val < k then b ⟨i, hi⟩ else i2, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < k
      · simp only [dif_pos hi]; exact ha _
      · simp only [dif_neg hi]; exact ⟨huv, j, hj1, hj2⟩
    · intro i i' hii'
      have := i'.isLt
      have hi : i.val < k := by omega
      by_cases hi' : i'.val < k
      · simp only [dif_pos hi, dif_pos hi']; exact hab _ _ hii'
      · simp only [dif_pos hi, dif_neg hi']; exact hb _
    · intro i
      by_cases hi : i.val < k
      · simp only [dif_pos hi]; exact le_trans (hb _) (le_trans huv hvx)
      · simp only [dif_neg hi]; exact hvx

theorem fits_iff {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (ys : A → Fin t → Bool) (r : Nat) :
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Fin (d+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
      C.output < d+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ i j, (C.wires (List.ofFn (xs i) ++ [false,true])).getD (p j).val false=ys i j) ↔
    ¬ ∃ a b : Fin (2^r) → A, (∀ i, xs (a i) ≤ xs (b i) ∧
      ∃ j, ys (a i) j=true ∧ ys (b i) j=false) ∧
      ∀ i j : Fin (2^r), i.val+1=j.val → xs (b i) ≤ xs (a j) := by
  have H := (crit1228 d t r (fun u j => ∃ i, xs i = u ∧ ys i j = true)
      (fun u j => ∃ i, xs i = u ∧ ys i j = false)).1
  constructor
  · intro hf hp
    obtain ⟨C, p, h1, h2, h3, h4, h5⟩ := hf
    have hn := H.1 ⟨C, p, h1, h2, h3, h4, trivial, fun x j =>
      ⟨fun ⟨i, hi, hj⟩ => by subst hi; rw [h5, hj], fun ⟨i, hi, hj⟩ => by subst hi; rw [h5, hj]⟩⟩
    obtain ⟨a, b, ha, hab⟩ := hp
    have hpos : 0 < 2^r := Nat.two_pow_pos r
    have hh := chain_reach xs ys _ a b ha hab (2^r-1) (by omega)
    have e : 2^r-1+1 = 2^r := by omega
    rw [e] at hh
    exact hn _ hh
  · intro hnp
    have hnr : ∀ x, ¬ R94 (fun u j => ∃ i, xs i = u ∧ ys i j = true)
        (fun u j => ∃ i, xs i = u ∧ ys i j = false) (2^r) x := by
      intro x hx
      obtain ⟨a, b, ha, hab, -⟩ := reach_chain xs ys _ x hx
      exact hnp ⟨a, b, ha, hab⟩
    obtain ⟨C, p, h1, h2, h3, h4, -, h5⟩ := H.2 hnr
    refine ⟨C, p, h1, h2, h3, h4, fun i j => ?_⟩
    cases hy : ys i j
    · exact (h5 (xs i) j).2 ⟨i, rfl, hy⟩
    · exact (h5 (xs i) j).1 ⟨i, rfl, hy⟩

theorem ble {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  revert h ha; cases a <;> cases b <;> decide
theorem ble2 {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  revert h; cases a <;> cases b <;> decide

end PEqualNP.Outside.L_lib_1401_aux.Source

namespace PEqualNP.Outside.L_lib_1401_aux

namespace Lib1401Packing

noncomputable def drops {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (fun i => ¬ W i.castSucc ⊆ W i.succ)

theorem drop_between {h r : Nat} (W : Fin (h+1) → Finset (Fin r))
    (i j : Fin (h+1)) (hij : i ≤ j) (hbad : ¬ W i ⊆ W j) :
    ∃ l : Fin h, i.val ≤ l.val ∧ l.val < j.val ∧ l ∈ drops W := by
  classical
  by_contra H
  push_neg at H
  let idx (k : Fin (j.val-i.val+1)) : Fin (h+1) :=
    ⟨i.val+k.val,by have := k.isLt;have := j.isLt;omega⟩
  have hm : Monotone (fun k => W (idx k)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    let l : Fin h := ⟨i.val+k.val,by have := k.isLt;have := j.isLt;omega⟩
    have hn := H l (by dsimp [l];omega) (by dsimp [l];have := k.isLt;omega)
    have hs : W l.castSucc ⊆ W l.succ := by
      simpa only [drops,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
    exact hs
  have he0 : idx 0 = i := Fin.ext (by simp [idx])
  have he1 : idx (Fin.last (j.val-i.val)) = j := Fin.ext (by
    simp only [idx,Fin.val_last]
    have H : i.val ≤ j.val := hij
    omega)
  apply hbad
  simpa only [he0,he1] using hm (show (0 : Fin (j.val-i.val+1)) ≤ Fin.last _ from Fin.zero_le _)

theorem prefix_order {h : Nat} (i j : Fin (h+1)) :
    (fun k : Fin h => decide (k.val < i.val)) ≤ (fun k : Fin h => decide (k.val < j.val)) ↔ i ≤ j := by
  constructor
  · intro H
    by_contra hn
    have hi : j.val < i.val := by omega
    let k : Fin h := ⟨j.val,by have := i.isLt;omega⟩
    have hk : decide (k.val < i.val)=true := by simp [k,hi]
    have hh := H k hk
    simp [k] at hh
  · intro H k hk
    have hi : k.val < i.val := of_decide_eq_true hk
    have hj : k.val < j.val := lt_of_lt_of_le hi H
    exact decide_eq_true hj

theorem onehot_fall {h : Nat} (i j : Fin (h+1)) :
    (∃ k : Fin (h+1), decide (i=k)=true ∧ decide (j=k)=false) ↔ i ≠ j := by
  constructor
  · rintro ⟨k,hi,hj⟩ hij
    subst j
    rw [hi] at hj
    contradiction
  · intro hij
    exact ⟨i,by simp,by simp [Ne.symm hij]⟩

end Lib1401Packing

namespace Lib1401Packing

def IntervalPacking {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) (k : Nat) : Prop :=
  ∃ a b : Fin k → Fin (h+1),
    (∀ i, a i ≤ b i ∧ ¬ W (a i) ⊆ W (b i)) ∧
    ∀ i j, i.val+1=j.val → b i ≤ a j

theorem interval_count_le {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (H : IntervalPacking W k) : k ≤ (drops W).card := by
  classical
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    obtain ⟨a,b,hab,hnext⟩ := H
    have hh : ∀ i,∃ l : Fin h, (a i).val ≤ l.val ∧ l.val < (b i).val ∧ l ∈ drops W :=
      fun i => drop_between W (a i) (b i) (hab i).1 (hab i).2
    choose f hfa hfb hfm using hh
    have hf : StrictMono f := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have H := hnext i.castSucc i.succ (by simp)
      have H' : (b i.castSucc).val ≤ (a i.succ).val := H
      change (f i.castSucc).val < (f i.succ).val
      have := hfb i.castSucc
      have := hfa i.succ
      omega
    let g : Fin (k+1) → (drops W) := fun i => ⟨f i,hfm i⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact hf.injective (congrArg Subtype.val hij)
    have Hcard := Fintype.card_le_of_injective g hg
    simpa only [Fintype.card_fin,Fintype.card_coe] using Hcard

theorem interval_of_count {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (hk : k ≤ (drops W).card) : IntervalPacking W k := by
  classical
  let e := (drops W).orderIsoOfFin rfl
  let f : Fin k → Fin h := fun i => (e ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).val
  have hf : StrictMono f := by
    intro i j hij
    have H := e.strictMono (show (⟨i.val,lt_of_lt_of_le i.isLt hk⟩ : Fin (drops W).card) <
      ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ from hij)
    exact H
  refine ⟨(fun i=>(f i).castSucc),(fun i=>(f i).succ),?_,?_⟩
  · intro i
    refine ⟨Fin.castSucc_le_succ _,?_⟩
    have H : f i ∈ drops W := (e ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).property
    simpa only [drops,Finset.mem_filter,Finset.mem_univ,true_and] using H
  · intro i j hij
    have H := hf (show i < j from by change i.val < j.val; omega)
    change (f i).val+1 ≤ (f j).val
    exact H

theorem interval_count_iff {h r k : Nat} (W : Fin (h+1) → Finset (Fin r)) :
    IntervalPacking W k ↔ k ≤ (drops W).card :=
  ⟨interval_count_le W,interval_of_count W⟩

end Lib1401Packing
namespace Lib1401Encoder
open PEqualNP.Outside.L_lib_1401_aux.Source Lib1401Packing

abbrev prefixInput {h : Nat} (i : Fin (h+1)) : Fin h → Bool :=
  fun j => decide (j.val < i.val)

abbrev wordBits {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) (i : Fin (h+1)) :
    Fin r → Bool := fun j => decide (j ∈ W i)

def Pos {A : Type} {n t : Nat} (xs : A → Input n) (ys : A → Fin t → Bool)
    (u : Input n) (j : Fin t) : Prop := ∃ a,xs a=u ∧ ys a j=true

def Neg {A : Type} {n t : Nat} (xs : A → Input n) (ys : A → Fin t → Bool)
    (u : Input n) (j : Fin t) : Prop := ∃ a,xs a=u ∧ ys a j=false

theorem support_sample {A : Type} [Fintype A] {n t : Nat}
    (xs : A → Input n) (ys : A → Fin t → Bool) :
    (support (Pos xs ys) (Neg xs ys)).card ≤ Fintype.card A := by
  classical
  have hs : support (Pos xs ys) (Neg xs ys) ⊆ Finset.univ.image xs := by
    intro u hu
    obtain ⟨j,hj⟩ := (mem_support _ _ _).mp hu
    rcases hj with ⟨a,rfl,ha⟩ | ⟨a,rfl,ha⟩ <;> exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem positives_sample {A : Type} [Fintype A] {n t : Nat}
    (xs : A → Input n) (ys : A → Fin t → Bool) :
    (positivePairs (Pos xs ys)).card ≤ Fintype.card A*t := by
  classical
  have hs : positivePairs (Pos xs ys) ⊆
      (Finset.univ : Finset (A × Fin t)).image (fun z=>(xs z.1,z.2)) := by
    intro z hz
    obtain ⟨a,ha,hb⟩ := (mem_positivePairs _ _).mp hz
    exact Finset.mem_image.mpr ⟨(a,z.2),Finset.mem_univ _,Prod.ext ha rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem bits_fall {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) (i j : Fin (h+1)) :
    (∃ l, wordBits W i l=true ∧ wordBits W j l=false) ↔ ¬ W i ⊆ W j := by
  classical
  simp only [wordBits,decide_eq_true_eq,decide_eq_false_iff_not,Finset.not_subset]

theorem prefix_packing {h r k : Nat} (W : Fin (h+1) → Finset (Fin r)) :
    (∃ a b : Fin k → Fin (h+1),
      (∀ i,prefixInput (a i) ≤ prefixInput (b i) ∧
        ∃ j,wordBits W (a i) j=true ∧ wordBits W (b i) j=false) ∧
      ∀ i j,i.val+1=j.val → prefixInput (b i) ≤ prefixInput (a j)) ↔
      k ≤ (drops W).card := by
  rw [←interval_count_iff]
  unfold IntervalPacking
  simp only [prefixInput,prefix_order,bits_fall]

theorem no_reach_drops {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) :
    ∀ z,¬ Reach (Pos prefixInput (wordBits W)) (Neg prefixInput (wordBits W))
      ((drops W).card+1) z := by
  intro z hz
  obtain ⟨a,b,hab,hnext,_⟩ := reach_chain prefixInput (wordBits W) ((drops W).card+1) z hz
  have H := (prefix_packing W).mp ⟨a,b,hab,hnext⟩
  omega

theorem prefix_fits_iff {h r b : Nat} (W : Fin (h+1) → Finset (Fin r)) :
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin r → Fin (h+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
      C.output < h+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ i j,(C.wires (List.ofFn (prefixInput i) ++ [false,true])).getD (p j).val false=
        wordBits W i j) ↔ (drops W).card < 2^b := by
  rw [fits_iff,prefix_packing]
  omega

end Lib1401Encoder
namespace Lib1401FromCones
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket PEqualNP.Outside.L_lib_1401_aux.Source

theorem upper_from_cones {n m r d : Nat} (P N : Input n → Fin m → Prop)
    (bound : d < 2^r) (bounded : ∀ x, ¬ Reach P N (d+1) x)
    (A : Circuit) (cone : Input n → Nat) (aBasis : FanInTwo A)
    (aReads : ReadsBack (n+2) A) (aNot : notCount A=0)
    (aLive : ∀ u ∈ support P N, cone u < nextWire (n+2) A)
    (aValue : ∀ u ∈ support P N, ∀ x,
      value A (withConstants x) (cone u)=true ↔ u≤x) :
    Fits P N r (fun cost => cost ≤
      A.size+2*(support P N).card+(positivePairs P).card+5*d) := by
  obtain ⟨B,thresholds,bBasis,bReads,bExtends,bNot,bSize,bLive,bSem⟩ :=
    append_thresholds P N d A cone aBasis aReads
      aLive aValue
  have falseLive : n < nextWire (n+2) B := by unfold nextWire; omega
  obtain ⟨I⟩ := invert_taps (withConstants (n := n)) withConstants_length bound
    bBasis bReads n falseLive (false_value B) thresholds bLive (threshold_antitone bSem)
  have extension : A.gates <+: I.circuit.gates := bExtends.trans I.extension
  have coneLive (u : Input n) (hu : u ∈ support P N) :
      cone u < nextWire (n+2) I.circuit :=
    (aLive u hu).trans_le (nextWire_le_of_prefix extension)
  have coneValue (u : Input n) (hu : u ∈ support P N) (x : Input n) :
      value I.circuit (withConstants x) (cone u) = true ↔ u ≤ x := by
    have live : cone u < nextWire (withConstants x).length A := by
      rw [withConstants_length]
      exact aLive u hu
    rw [value_of_prefix extension live]
    exact aValue u hu x
  have complementValue (i : Fin d) (x : Input n) :
      value I.circuit (withConstants x) (I.wires i) = true ↔ ¬ i.val+1 ≤ rank P N d x := by
    rw [I.computes, ← bSem x i]
    cases value B (withConstants x) (thresholds i) <;> decide
  obtain ⟨C,tap,cBasis,cReads,cOut,_,cNot,cSize,labels⟩ :=
    append_taps P N I.circuit cone I.wires I.fanInTwo I.readsBack
      coneLive coneValue I.valid complementValue bounded
  have bZero : notCount B = 0 := bNot.trans aNot
  have cInversions : notCount C = I.inversions := by
    rw [cNot,I.count_eq,bZero,Nat.zero_add]
  have cBinary : C.size-notCount C ≤ A.size+2*(support P N).card+(positivePairs P).card+5*d := by
    have inversionSize := I.size_eq
    have binaryBudget := I.binaryBound
    rw [cInversions]
    omega
  exact ⟨C,tap,cBasis,cReads,cOut,cInversions.le.trans I.inversionsBound,cBinary,labels⟩

end Lib1401FromCones
namespace Lib1401Prefix
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)
open PEqualNP.Outside.L_lib_1401_aux.Source

def tap (h : Nat) : Nat → Nat
  | 0 => h + 1
  | k + 1 => h + 2 + k

def build (h : Nat) : Nat → Circuit
  | 0 => emptyCircuit
  | k + 1 => appendGate (build h k) ⟨.and, [tap h k, k]⟩

theorem size_build (h k : Nat) : (build h k).size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [build, appendGate_size, ih]

theorem output_build (h k : Nat) : (build h k).output = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem notCount_build (h k : Nat) : notCount (build h k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [build, appendGate_notCount, ih]

theorem fanInTwo_build (h k : Nat) : FanInTwo (build h k) := by
  induction k with
  | zero => exact emptyCircuit_fanInTwo
  | succ k ih => exact appendGate_fanInTwo ih (by simp) (by simp)

theorem tap_lt (h k i : Nat) (hi : i ≤ k) : tap h i < h + 2 + k := by
  cases i <;> simp only [tap] <;> omega

theorem readsBack_build (h k : Nat) (hk : k ≤ h) : ReadsBack (h+2) (build h k) := by
  induction k with
  | zero => exact emptyCircuit_readsBack _
  | succ k ih =>
    apply appendGate_readsBack (ih (by omega))
    intro j hj
    have hj' : j = tap h k ∨ j = k := by simpa using hj
    rcases hj' with rfl | rfl
    · simpa only [nextWire, size_build] using tap_lt h k k (le_refl k)
    · simp only [nextWire, size_build]
      omega

theorem values_build (h k : Nat) (hk : k ≤ h) (x : Fin h → Bool) :
    ∀ i ≤ k, value (build h k) (withConstants x) (tap h i) = true ↔
      ∀ j : Fin h, j.val < i → x j = true := by
  induction k with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [tap, true_value]
  | succ k ih =>
    have ih' := ih (by omega)
    intro i hi
    by_cases last : i = k+1
    · subst i
      have index : tap h (k+1) = nextWire (withConstants x).length (build h k) := by
        simp only [tap, nextWire, withConstants_length, size_build]
      rw [index]
      change value (appendGate (build h k) ⟨.and,[tap h k,k]⟩)
        (withConstants x) (nextWire (withConstants x).length (build h k)) = true ↔ _
      rw [appendGate_new]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true]
      change (value (build h k) (withConstants x) (tap h k) &&
        value (build h k) (withConstants x) k) = true ↔ _
      have input : value (build h k) (withConstants x) k = x ⟨k,by omega⟩ :=
        input_value (build h k) x ⟨k,by omega⟩
      rw [input, Bool.and_eq_true, ih' k (le_refl k)]
      constructor
      · rintro ⟨before,atK⟩ j hj
        by_cases earlier : j.val < k
        · exact before j earlier
        · have eq : j = (⟨k,by omega⟩ : Fin h) := by
            apply Fin.ext
            change j.val = k
            omega
          simpa only [eq] using atK
      · intro all
        exact ⟨fun j hj => all j (by omega), all ⟨k,by omega⟩ (by simp)⟩
    · have earlier : i ≤ k := by omega
      have bounded : tap h i < nextWire (withConstants x).length (build h k) := by
        simpa only [nextWire, withConstants_length, size_build] using tap_lt h k i earlier
      change value (appendGate (build h k) ⟨.and,[tap h k,k]⟩)
        (withConstants x) (tap h i) = true ↔ _
      rw [appendGate_old bounded]
      exact ih' i earlier

theorem prefixAnd (h : Nat) :
    ∃ (A : Circuit) (cone : Fin (h+1) → Fin (h+2+A.size)),
      FanInTwo A ∧ ReadsBack (h+2) A ∧ A.output < h+2+A.size ∧
      notCount A = 0 ∧ A.size ≤ h ∧
      ∀ (x : Fin h → Bool) (i : Fin (h+1)),
        (A.wires (List.ofFn x ++ [false,true])).getD (cone i).val false = true ↔
          ∀ j : Fin h, j.val < i.val → x j = true := by
  let A := build h h
  let cone : Fin (h+1) → Fin (h+2+A.size) := fun i =>
    ⟨tap h i.val,by simpa only [A, size_build] using tap_lt h h i.val (by omega)⟩
  refine ⟨A, cone, fanInTwo_build h h, readsBack_build h h (le_refl h), ?_,
    notCount_build h h, ?_, ?_⟩
  · simp only [A, output_build, size_build]
    omega
  · exact le_of_eq (size_build h h)
  · intro x i
    exact values_build h h (le_refl h) x i.val (by omega)
end Lib1401Prefix
namespace Lib1401Encoder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket PEqualNP.Outside.L_lib_1401_aux.Source Lib1401Packing

theorem prefix_le_iff {h : Nat} (i : Fin (h+1)) (x : Input h) :
    prefixInput i ≤ x ↔ ∀ j : Fin h, j.val < i.val → x j=true := by
  constructor
  · intro H j hj
    have H' := H j
    exact ble H' (by simp [prefixInput,hj])
  · intro H j
    by_cases hj : j.val < i.val
    · simp [prefixInput,hj,H j hj]
    · simp [prefixInput,hj]

set_option maxHeartbeats 800000 in
theorem encoder_prefix {h r b : Nat} (W : Fin (h+1) → Finset (Fin r))
    (hb : (drops W).card < 2^b) :
    ∃ (C : Circuit) (tap : Fin r → Fin (h+2+C.size)),
      FanInTwo C ∧ ReadsBack (h+2) C ∧ C.output < h+2+C.size ∧
      notCount C ≤ b ∧ C.size-notCount C ≤ (r+8)*(h+1) ∧
      ∀ i j,(C.wires (List.ofFn (prefixInput i)++[false,true])).getD (tap j).val false =
        wordBits W i j := by
  classical
  let P := Pos prefixInput (wordBits W)
  let N := Neg prefixInput (wordBits W)
  obtain ⟨A,ctap,haf,har,hao,han,has,hav⟩ := Lib1401Prefix.prefixAnd h
  let pick (u : Input h) : Nat :=
    if hu : ∃ i : Fin (h+1),prefixInput i=u then (ctap (Classical.choose hu)).val else 0
  have occurrence (u : Input h) (hu : u∈support P N) :
      ∃ i : Fin (h+1),prefixInput i=u := by
    obtain ⟨j,hj⟩ := (mem_support P N u).mp hu
    rcases hj with ⟨i,hi,_⟩ | ⟨i,hi,_⟩ <;> exact ⟨i,hi⟩
  have live (u : Input h) (hu : u∈support P N) : pick u < nextWire (h+2) A := by
    dsimp only [pick]
    rw [dif_pos (occurrence u hu)]
    exact (ctap _).isLt
  have sem (u : Input h) (hu : u∈support P N) (x : Input h) :
      value A (withConstants x) (pick u)=true ↔ u≤x := by
    dsimp only [pick]
    rw [dif_pos (occurrence u hu)]
    calc
      _ ↔ prefixInput (Classical.choose (occurrence u hu)) ≤ x :=
        (hav x _).trans (prefix_le_iff _ x).symm
      _ ↔ u ≤ x := by rw [Classical.choose_spec (occurrence u hu)]
  obtain ⟨C,tap,hf,hr,ho,hn,hcost,hval⟩ :=
    Lib1401FromCones.upper_from_cones P N hb (no_reach_drops W)
      A pick haf har han live sem
  have hs : (support P N).card ≤ h+1 := by
    simpa only [Fintype.card_fin] using support_sample prefixInput (wordBits W)
  have hp : (positivePairs P).card ≤ (h+1)*r := by
    simpa only [Fintype.card_fin] using positives_sample prefixInput (wordBits W)
  have hd : (drops W).card ≤ h := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (drops W)
  refine ⟨C,tap,hf,hr,ho,hn,?_,?_⟩
  · nlinarith
  · intro i j
    cases H : wordBits W i j with
    | false => exact (hval (prefixInput i) j).2 ⟨i,rfl,H⟩
    | true => exact (hval (prefixInput i) j).1 ⟨i,rfl,H⟩

end Lib1401Encoder

namespace Lib1401Decoder

def Packed {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) (k : Nat) : Prop :=
  ∃ a b : Fin k → Fin (h+1),
    (∀ i, W (a i) ⊆ W (b i) ∧ a i ≠ b i) ∧
    ∀ i j, i.val+1=j.val → W (b i) ⊆ W (a j)

def HeightAtMost {r : Nat} (S : Finset (Finset (Fin r))) (p : Nat) : Prop :=
  ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ p

def Chain {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) (k : Nat) : Prop :=
  ∃ f : Fin (k+1) → Finset (Fin r), StrictMono f ∧
    ∀ i, f i ∈ Finset.univ.image W

theorem packed_chain {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (inj : Function.Injective W) (hp : Packed W k) : Chain W k := by
  classical
  cases k with
  | zero =>
    refine ⟨fun _ => W 0, ?_, ?_⟩
    · intro i j hij
      have := i.isLt
      have := j.isLt
      omega
    · intro i
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  | succ k =>
    obtain ⟨a,b,hab,hnext⟩ := hp
    have strict (i : Fin (k+1)) : W (a i) < W (b i) := by
      exact lt_iff_le_and_ne.mpr ⟨(hab i).1, fun e => (hab i).2 (inj e)⟩
    let f : Fin (k+2) → Finset (Fin r) := Fin.cons (W (a 0)) (fun i => W (b i))
    refine ⟨f, ?_, ?_⟩
    · apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [f] using strict 0
      · have H := lt_of_le_of_lt (hnext j.castSucc j.succ (by simp)) (strict j.succ)
        simpa [f] using H
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Finset.mem_image.mpr ⟨a 0, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨b j, Finset.mem_univ _, rfl⟩

theorem chain_packed {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (hc : Chain W k) : Packed W k := by
  classical
  obtain ⟨f,hf,hm⟩ := hc
  have H : ∀ i, ∃ j : Fin (h+1), W j = f i := by
    intro i
    obtain ⟨j,-,hj⟩ := Finset.mem_image.mp (hm i)
    exact ⟨j,hj⟩
  choose g hg using H
  refine ⟨(fun i=>g i.castSucc),(fun i=>g i.succ),?_,?_⟩
  · intro i
    have hi := hf (show i.castSucc < i.succ from by change i.val < i.val+1; omega)
    refine ⟨?_,?_⟩
    · simpa only [hg] using hi.le
    · intro e
      have eq := congrArg W e
      rw [hg,hg] at eq
      exact hi.ne eq
  · intro i j hij
    have eq : i.succ = j.castSucc := Fin.ext (by simpa using hij)
    rw [hg,hg,eq]

theorem chain_height_lower {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (hc : Chain W k) : ∃ U ⊆ Finset.univ.image W,
      (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) ∧ U.card = k+1 := by
  classical
  obtain ⟨f,hf,hm⟩ := hc
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hx
    exact hm i
  · intro x hx y hy
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,-,rfl⟩ := Finset.mem_image.mp hy
    rcases le_total i j with h | h
    · exact Or.inl (hf.monotone h)
    · exact Or.inr (hf.monotone h)
  · rw [Finset.card_image_of_injective _ hf.injective]
    simp

theorem height_chain {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (U : Finset (Finset (Fin r))) (sub : U ⊆ Finset.univ.image W)
    (chain : ∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x)
    (hk : k+1 ≤ U.card) : Chain W k := by
  classical
  have cardinj : Function.Injective (fun x : U => x.val.card) := by
    intro x y eq
    change x.val.card = y.val.card at eq
    apply Subtype.ext
    rcases chain x x.property y y.property with hxy | hyx
    · exact Finset.eq_of_subset_of_card_le hxy eq.symm.le
    · exact (Finset.eq_of_subset_of_card_le hyx eq.le).symm
  let order : LinearOrder U := LinearOrder.lift' (fun x : U => x.val.card) cardinj
  letI : LinearOrder U := order
  letI : PartialOrder U := order.toPartialOrder
  letI : Preorder U := order.toPreorder
  letI : LE U := order.toLE
  letI : LT U := order.toLT
  let e := Fintype.orderIsoFinOfCardEq U (k := U.card) (by simp)
  let f : Fin (k+1) → Finset (Fin r) := fun i => (e ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).val
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    have H := e.strictMono (show (⟨i.val,lt_of_lt_of_le i.isLt hk⟩ : Fin U.card) <
      ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ from hij)
    have cards : (f i).card < (f j).card := by
      change (f i).card < (f j).card at H
      exact H
    have hi : f i ∈ U := (e ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).property
    have hj : f j ∈ U := (e ⟨j.val,lt_of_lt_of_le j.isLt hk⟩).property
    rcases chain _ hi _ hj with hsub | hsub
    · exact lt_iff_le_and_ne.mpr ⟨hsub, fun he => by rw [he] at cards; omega⟩
    · have := Finset.card_le_card hsub
      omega
  · intro i
    exact sub (e ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).property

theorem not_packed_iff_height {h r p : Nat} (W : Fin (h+1) → Finset (Fin r))
    (inj : Function.Injective W) :
    ¬ Packed W p ↔ HeightAtMost (Finset.univ.image W) p := by
  classical
  constructor
  · intro hn U hsub hc
    by_contra bad
    have big : p+1 ≤ U.card := by omega
    exact hn (chain_packed W (height_chain W U hsub hc big))
  · intro ht hp
    obtain ⟨U,hsub,hc,hcard⟩ := chain_height_lower W (packed_chain W inj hp)
    have := ht U hsub hc
    omega
theorem packed_le {h r k : Nat} (W : Fin (h+1) → Finset (Fin r))
    (inj : Function.Injective W) (hp : Packed W k) : k ≤ h := by
  classical
  obtain ⟨U,hsub,-,hcard⟩ := chain_height_lower W (packed_chain W inj hp)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin (h+1)))) (f := W)
  have h3 : (Finset.univ : Finset (Fin (h+1))).card = h+1 := by simp
  omega
end Lib1401Decoder

namespace Lib1401DecoderBuild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket PEqualNP.Outside.L_lib_1401_aux.Source
open Lib1401Packing Lib1401Encoder Lib1401Decoder

abbrev onehot {h : Nat} (i : Fin (h+1)) : Fin (h+1) → Bool := fun j=>decide (i=j)

theorem bits_le_iff {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) (i j : Fin (h+1)) :
    wordBits W i ≤ wordBits W j ↔ W i ⊆ W j := by
  classical
  constructor
  · intro H a ha
    have H' := ble (H a) (by simp [wordBits,ha])
    simpa only [wordBits,decide_eq_true_eq] using H'
  · intro H a
    by_cases ha : a∈W i
    · simp [wordBits,ha,H ha]
    · simp [wordBits,ha]

theorem packing_iff {h r k : Nat} (W : Fin (h+1) → Finset (Fin r)) :
    (∃a b : Fin k → Fin (h+1),
      (∀i,wordBits W (a i) ≤ wordBits W (b i) ∧
        ∃j,onehot (a i) j=true ∧ onehot (b i) j=false) ∧
      ∀i j,i.val+1=j.val→wordBits W (b i)≤wordBits W (a j)) ↔ Packed W k := by
  unfold Packed
  simp only [bits_le_iff,onehot,onehot_fall]

theorem positives_onehot {h r : Nat} (W : Fin (h+1) → Finset (Fin r)) :
    (positivePairs (Pos (wordBits W) onehot)).card ≤ h+1 := by
  classical
  have hs : positivePairs (Pos (wordBits W) onehot) ⊆
      Finset.univ.image (fun i : Fin (h+1)=>(wordBits W i,i)) := by
    intro z hz
    obtain ⟨i,hi,hj⟩ := (mem_positivePairs _ _).mp hz
    have he : i=z.2 := of_decide_eq_true hj
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,Prod.ext hi he⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem decoder_fits_iff {h r c : Nat} (W : Fin (h+1) → Finset (Fin r))
    (inj : Function.Injective W) :
    (∃ (D : Circuit) (tap : Fin (h+1) → Fin (r+2+D.size)),
      FanInTwo D ∧ ReadsBack (r+2) D ∧ D.output  <  r+2+D.size ∧ notCount D ≤ c ∧
      ∀i j,(D.wires (List.ofFn (wordBits W i)++[false,true])).getD (tap j).val false =
        onehot i j) ↔ HeightAtMost (Finset.univ.image W) (2^c) := by
  rw [fits_iff,packing_iff,not_packed_iff_height W inj]

set_option maxHeartbeats 800000 in
theorem decoder_upper {h r c : Nat} (W : Fin (h+1) → Finset (Fin r))
    (inj : Function.Injective W) (ht : HeightAtMost (Finset.univ.image W) (2^c)) :
    ∃ (D : Circuit) (tap : Fin (h+1) → Fin (r+2+D.size)),
      FanInTwo D ∧ ReadsBack (r+2) D ∧ D.output  <  r+2+D.size ∧
      notCount D ≤ c ∧ D.size-notCount D ≤ (r+8)*(h+1) ∧
      ∀i j,(D.wires (List.ofFn (wordBits W i)++[false,true])).getD (tap j).val false =
        onehot i j := by
  classical
  let d := min h (2^c-1)
  have powpos : 0  <  (2:Nat)^c := Nat.pow_pos (by decide)
  have dh : d≤h := Nat.min_le_left _ _
  have dc : d < 2^c := lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
  let P := Pos (wordBits W) onehot
  let N := Neg (wordBits W) onehot
  have bounded : ∀z,¬Reach P N (d+1) z := by
    intro z hz
    obtain ⟨a,b,hab,hnext,_⟩ := reach_chain (wordBits W) onehot (d+1) z hz
    have hp : Packed W (d+1) := (packing_iff W).mp ⟨a,b,hab,hnext⟩
    by_cases H : h≤2^c-1
    · have de : d=h := Nat.min_eq_left H
      have := packed_le W inj hp
      omega
    · have de : d=2^c-1 := Nat.min_eq_right (by omega)
      have de' : d+1=2^c := by omega
      rw [de'] at hp
      exact (not_packed_iff_height W inj).mpr ht hp
  obtain ⟨D,tap,hf,hr,ho,hn,hcost,hval⟩ := upper_fits P N dc bounded
  have hs : (support P N).card ≤ h+1 := by
    simpa only [Fintype.card_fin] using support_sample (wordBits W) onehot
  have hs' := Nat.mul_le_mul_left (r+2) hs
  have hp : (positivePairs P).card ≤ h+1 := positives_onehot W
  refine ⟨D,tap,hf,hr,ho,hn,?_,?_⟩
  · nlinarith
  · intro i j
    cases H : onehot i j with
    | false => exact (hval (wordBits W i) j).2 ⟨i,rfl,H⟩
    | true => exact (hval (wordBits W i) j).1 ⟨i,rfl,H⟩

end Lib1401DecoderBuild

namespace Lib1401Suffix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma circuit_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append, wiresFrom_cons]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  rw [wiresFrom_getD_lt _ _ (w.length + j) (by simp [hlen])]
  rw [getD_append_right _ _ (w.length + j) false (by omega)]
  simp [hlen]

lemma wiresFrom_getD_gate_readsBack (gs : List Gate) (w : List Bool)
    (hrb : ReadsBack w.length ⟨gs, 0⟩) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom gs w).getD i false) := by
  rw [wiresFrom_getD_gate gs w j hj]
  congr 1
  refine List.map_congr_left (fun i hi => ?_)
  have hi_lt : i < w.length + j := by
    have h := hrb j hj
    rw [gateAt_eq_getElem _ j hj] at h
    exact h i hi
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hsplit, wiresFrom_append]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  symm
  exact wiresFrom_getD_lt (gs.drop j) (wiresFrom (gs.take j) w) i (by omega)

lemma fanInTwo_map_inputs {gs : List Gate} {φ : ℕ → ℕ} {o : ℕ}
    (h : FanInTwo ⟨gs, 0⟩) :
    FanInTwo ⟨gs.map (fun g => ⟨g.op, g.inputs.map φ⟩), o⟩ := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
  have h0 := h g0 hg0
  exact ⟨h0.1, by simpa using h0.2⟩

lemma wiresFrom_remap_full (gs : List Gate) (w1 W0 : List Bool) (φ : ℕ → ℕ)
    (hrb : ReadsBack w1.length ⟨gs, 0⟩)
    (hφ_lt : ∀ k < w1.length, φ k < W0.length)
    (hφ_gate : ∀ j < gs.length, φ (w1.length + j) = W0.length + j)
    (hφ_val : ∀ k < w1.length, W0.getD (φ k) false = w1.getD k false) :
    let gs' := gs.map (fun g => ⟨g.op, g.inputs.map φ⟩)
    ReadsBack W0.length ⟨gs', 0⟩ ∧
    ∀ t < w1.length + gs.length,
      (wiresFrom gs' W0).getD (φ t) false = (wiresFrom gs w1).getD t false := by
  intro gs'
  have hrb' : ReadsBack W0.length ⟨gs', 0⟩ := by
    intro j hj i hi
    have hj0 : j < gs.length := by simpa [gs'] using hj
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [gs', List.getElem_map, List.mem_map] at hi
    rcases hi with ⟨k, hk, rfl⟩
    have hk_lt : k < w1.length + j := by
      have h := hrb j hj0
      rw [gateAt_eq_getElem _ j hj0] at h
      exact h k hk
    by_cases hkw : k < w1.length
    · exact lt_of_lt_of_le (hφ_lt k hkw) (Nat.le_add_right _ _)
    · have hj' : k - w1.length < gs.length := by omega
      have hkeq : k = w1.length + (k - w1.length) := by omega
      rw [hkeq, hφ_gate (k - w1.length) hj']
      omega
  refine ⟨hrb', ?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htw : t < w1.length
    · rw [wiresFrom_getD_lt gs' W0 (φ t) (hφ_lt t htw)]
      rw [wiresFrom_getD_lt gs w1 t htw]
      exact hφ_val t htw
    · let j := t - w1.length
      have hj : j < gs.length := by omega
      have hteq : t = w1.length + j := by omega
      rw [hteq, hφ_gate j hj]
      have hj' : j < gs'.length := by simpa [gs'] using hj
      rw [wiresFrom_getD_gate_readsBack gs' W0 hrb' j hj']
      rw [wiresFrom_getD_gate_readsBack gs w1 hrb j hj]
      simp only [gs', List.getElem_map, List.map_map]
      congr 1
      refine List.map_congr_left (fun k hk => ?_)
      have hk_lt : k < w1.length + j := by
        have h := hrb j hj
        rw [gateAt_eq_getElem _ j hj] at h
        exact h k hk
      exact ih k (by omega) (by omega)

def inputs {n : Nat} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ [false, true]

@[simp] theorem inputs_length {n : Nat} (x : Fin n → Bool) :
    (inputs x).length = n + 2 := by simp [inputs]

@[simp] theorem inputs_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (inputs x).getD i.val false = x i := by
  rw [inputs, getD_append_left _ _ _ _ (by simp)]
  simp

@[simp] theorem inputs_false {n : Nat} (x : Fin n → Bool) :
    (inputs x).getD n false = false := by
  rw [inputs, getD_append_right _ _ _ _ (by simp)]
  simp

@[simp] theorem inputs_true {n : Nat} (x : Fin n → Bool) :
    (inputs x).getD (n + 1) false = true := by
  rw [inputs, getD_append_right _ _ _ _ (by simp)]
  simp

lemma bool_ext (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

def suffixAt {h : Nat} (x : Fin h → Bool) (i : Nat) : Bool :=
  decide (∃ j : Fin h, i ≤ j.val ∧ x j = true)

def suffix {h : Nat} (x : Fin h → Bool) (i : Fin h) : Bool := suffixAt x i.val

lemma suffixAt_end {h : Nat} (x : Fin h → Bool) : suffixAt x h = false := by
  simp only [suffixAt, decide_eq_false_iff_not, not_exists, not_and]
  intro j hj
  omega

lemma suffixAt_step {h : Nat} (x : Fin h → Bool) (i : Fin h) :
    suffixAt x i.val = (x i || suffixAt x (i.val+1)) := by
  apply bool_ext
  simp only [suffixAt, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hij, hj⟩
    by_cases he : j = i
    · exact Or.inl (he ▸ hj)
    · have hne : j.val ≠ i.val := fun hv => he (Fin.ext hv)
      exact Or.inr ⟨j, by omega, hj⟩
  · rintro (hi | ⟨j, hij, hj⟩)
    · exact ⟨i, le_rfl, hi⟩
    · exact ⟨j, by omega, hj⟩

theorem suffix_rank {h : Nat} (A : Finset (Fin h)) (i : Fin (h+1))
    (hr : A.sup (fun j => j.val+1) = i.val) :
    suffix (fun j => decide (j ∈ A)) = fun j => decide (j.val < i.val) := by
  funext j
  apply bool_ext
  simp only [suffix, suffixAt, decide_eq_true_eq]
  rw [← hr, Finset.lt_sup_iff]
  constructor
  · rintro ⟨k, hjk, hk⟩
    exact ⟨k, hk, by omega⟩
  · rintro ⟨k, hk, hjk⟩
    exact ⟨k, by omega, hk⟩

def preGate (h : Nat) (j : Fin h) : Gate :=
  ⟨.or, [h-1-j.val, if j.val = 0 then h else h+1+j.val]⟩

def pre (h : Nat) : Circuit := ⟨List.ofFn (preGate h), h⟩

@[simp] theorem pre_size (h : Nat) : (pre h).size = h := by
  simp [pre, Circuit.size]

theorem pre_fan (h : Nat) : FanInTwo (pre h) := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  simp [preGate]

theorem pre_back (h : Nat) : ReadsBack (h+2) (pre h) := by
  intro j hj k hk
  have hjh : j < h := by simpa [pre] using hj
  rw [gateAt_eq_getElem _ j hj] at hk
  simp only [pre, List.getElem_ofFn, preGate, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · omega
  · split_ifs <;> omega

theorem pre_not (h : Nat) : notCount (pre h) = 0 := by
  unfold notCount
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  simp [preGate]

theorem pre_gate_value {h : Nat} (x : Fin h → Bool) (j : Nat) (hj : j < h) :
    ((pre h).wires (inputs x)).getD (h+2+j) false = suffixAt x (h-1-j) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hjg : j < (pre h).gates.length := by simpa [pre] using hj
    have hb : ReadsBack (inputs x).length (pre h) := by simpa using pre_back h
    have he := wiresFrom_getD_gate_readsBack (pre h).gates (inputs x) hb j hjg
    simp only [inputs_length] at he
    rw [circuit_wires_eq, he]
    simp only [pre, List.getElem_ofFn, preGate, GateOp.eval,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    change
      ((wiresFrom (pre h).gates (inputs x)).getD (h-1-j) false ||
       (wiresFrom (pre h).gates (inputs x)).getD (if j = 0 then h else h+1+j) false)
      = suffixAt x (h-1-j)
    have hi : h-1-j < h := by omega
    have hv : (wiresFrom (pre h).gates (inputs x)).getD (h-1-j) false =
        x ⟨h-1-j, hi⟩ := by
      rw [wiresFrom_getD_lt _ _ _ (by simp; omega)]
      exact inputs_bit x ⟨h-1-j, hi⟩
    rw [hv, suffixAt_step x ⟨h-1-j, hi⟩]
    congr 1
    by_cases hz : j = 0
    · subst j
      change (wiresFrom (pre h).gates (inputs x)).getD h false = suffixAt x (h-1-0+1)
      rw [wiresFrom_getD_lt _ _ _ (by simp), inputs_false]
      have hi : h-1-0+1 = h := by omega
      rw [hi, suffixAt_end]
    · rw [if_neg hz]
      have hm : j-1 < j := by omega
      have hp : j-1 < h := by omega
      have ht : h+1+j = h+2+(j-1) := by omega
      rw [ht]
      change ((pre h).wires (inputs x)).getD (h+2+(j-1)) false = _
      rw [ih (j-1) hm hp]
      congr 1
      change h-1-(j-1) = h-1-j+1
      omega

def phi (h t : Nat) : Nat :=
  if t < h then h+2+(h-1-t) else if t < h+2 then t else t+h

theorem phi_input_lt (h t : Nat) (ht : t < h+2) : phi h t < h+2+h := by
  unfold phi
  split_ifs <;> omega

theorem phi_gate (h j : Nat) : phi h (h+2+j) = h+2+h+j := by
  simp only [phi, if_neg (show ¬ h+2+j < h by omega),
    if_neg (show ¬ h+2+j < h+2 by omega)]
  omega

theorem phi_lt (h s t : Nat) (ht : t < h+2+s) : phi h t < h+2+(s+h) := by
  by_cases hi : t < h+2
  · have := phi_input_lt h t hi
    omega
  · have he : t = h+2+(t-(h+2)) := by omega
    rw [he, phi_gate]
    omega

theorem phi_value {h : Nat} (x : Fin h → Bool) (t : Nat) (ht : t < h+2) :
    ((pre h).wires (inputs x)).getD (phi h t) false = (inputs (suffix x)).getD t false := by
  by_cases hi : t < h
  · simp only [phi, if_pos hi]
    rw [pre_gate_value x (h-1-t) (by omega)]
    have he : h-1-(h-1-t) = t := by omega
    rw [he]
    exact (inputs_bit (suffix x) ⟨t, hi⟩).symm
  · have he : t = h ∨ t = h+1 := by omega
    have hp : phi h t = t := by simp [phi, hi, ht]
    rw [hp, circuit_wires_eq, wiresFrom_getD_lt _ _ _ (by simpa using ht)]
    rcases he with rfl | rfl
    · rw [inputs_false, inputs_false]
    · rw [inputs_true, inputs_true]

lemma readsBack_append {m : Nat} (a b : List Gate)
    (ha : ReadsBack m ⟨a,0⟩) (hb : ReadsBack (m+a.length) ⟨b,0⟩) :
    ReadsBack m ⟨a++b,0⟩ := by
  intro j hj i hi
  change i ∈ ((a++b).getD j ⟨.or,[]⟩).inputs at hi
  by_cases hja : j < a.length
  · rw [getD_append_left _ _ _ _ hja] at hi
    exact ha j hja i hi
  · rw [getD_append_right _ _ _ _ (by omega)] at hi
    have hjb : j-a.length < b.length := by simp only [List.length_append] at hj; omega
    have := hb (j-a.length) hjb i hi
    omega

set_option maxHeartbeats 800000 in
theorem normalize {h : Nat} (C : Circuit) (hfan : FanInTwo C)
    (hrb : ReadsBack (h+2) C) (hout : C.output < h+2+C.size) :
    ∃ (B : Circuit) (rho : Fin (h+2+C.size) → Fin (h+2+B.size)),
      FanInTwo B ∧ ReadsBack (h+2) B ∧ B.output < h+2+B.size ∧
      B.size = C.size+h ∧ notCount B = notCount C ∧
      ∀ (x : Fin h → Bool) (t : Fin (h+2+C.size)),
        (B.wires (inputs x)).getD (rho t).val false =
          (C.wires (inputs (suffix x))).getD t.val false := by
  classical
  let gs := C.gates.map (fun g => (⟨g.op, g.inputs.map (phi h)⟩ : Gate))
  let B : Circuit := ⟨(pre h).gates ++ gs, phi h C.output⟩
  have hsize : B.size = C.size+h := by simp [B, gs, pre, Circuit.size, Nat.add_comm]
  have hphi : ∀ t, t < h+2+C.size → phi h t < h+2+B.size := by
    intro t ht
    rw [hsize]
    exact phi_lt h C.size t ht
  let rho : Fin (h+2+C.size) → Fin (h+2+B.size) := fun t => ⟨phi h t.val, hphi _ t.isLt⟩
  have hsim (x : Fin h → Bool) :=
    wiresFrom_remap_full C.gates (inputs (suffix x)) ((pre h).wires (inputs x)) (phi h)
      (by simpa only [inputs_length, ReadsBack, gateAt, Circuit.size] using hrb)
      (by intro t ht; simpa [circuit_wires_eq, wiresFrom_length, pre] using phi_input_lt h t (by simpa using ht))
      (by intro j hj; simpa [circuit_wires_eq, wiresFrom_length, pre] using phi_gate h j)
      (by intro t ht; exact phi_value x t (by simpa using ht))
  have hgs : FanInTwo ⟨gs,0⟩ := fanInTwo_map_inputs hfan
  have hf : FanInTwo B := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact pre_fan h g hg
    · exact hgs g hg
  have hb : ReadsBack (h+2) B := by
    apply readsBack_append
    · exact pre_back h
    · simpa only [circuit_wires_eq, wiresFrom_length, inputs_length] using (hsim (fun _ => false)).1
  have hn : notCount B = notCount C := by
    simp only [notCount, B, List.filter_append, List.length_append]
    have hz := pre_not h
    unfold notCount at hz
    rw [hz, Nat.zero_add]
    simp only [gs, List.filter_map, List.length_map] <;> rfl
  refine ⟨B, rho, hf, hb, hphi _ hout, hsize, hn, ?_⟩
  intro x t
  have hv := (hsim x).2 t.val (by simpa [Circuit.size] using t.isLt)
  simpa only [B, rho, circuit_wires_eq, wiresFrom_append] using hv

end Lib1401Suffix
namespace Lib1401Full
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket PEqualNP.Outside.L_lib_1401_aux.Source
open Lib1401Packing Lib1401Encoder Lib1401Decoder Lib1401DecoderBuild

noncomputable def prefixSet {h : Nat} (i : Fin (h+1)) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (fun j=>j.val < i.val)

theorem prefixSet_bits {h : Nat} (i : Fin (h+1)) :
    (fun j : Fin h=>decide (j∈prefixSet i)) = prefixInput i := by
  classical
  funext j
  simp [prefixSet,prefixInput]

theorem prefixSet_sup {h : Nat} (i : Fin (h+1)) :
    (prefixSet i).sup (fun j=>j.val+1)=i.val := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have : j.val < i.val := (Finset.mem_filter.mp hj).2
    omega
  · by_cases hi : i.val=0
    · omega
    · let j : Fin h := ⟨i.val-1,by omega⟩
      have hj : j∈prefixSet i := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ j,?_⟩
        change i.val-1 < i.val
        omega
      have H := Finset.le_sup (f:=fun j : Fin h=>j.val+1) hj
      dsimp only [j] at H
      omega

noncomputable def Fit (h r b c z : Nat) (W : Fin (h+1) → Finset (Fin r)) : Prop :=
  ∃ (C D : Circuit) (wire : Fin r → Nat) (out : Fin (h+1) → Nat),
    FanInTwo C ∧ ReadsBack (h+2) C ∧ FanInTwo D ∧ ReadsBack (r+2) D ∧
    C.output < h+2+C.size ∧ D.output < r+2+D.size ∧
    (∀j,wire j < h+2+C.size) ∧ (∀j,out j < r+2+D.size) ∧
    notCount C≤b ∧ notCount D≤c ∧ (C.size-notCount C)+(D.size-notCount D)≤z ∧
    ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j=>j.val+1)=i.val →
      let v:=C.wires (List.ofFn (fun j=>decide (j∈A))++[false,true])
      let msg:=Finset.univ.filter (fun j=>v.getD (wire j) false=true)
      let w:=D.wires (List.ofFn (fun j=>decide (j∈msg))++[false,true])
      msg=W i ∧ ∀j,w.getD (out j) false=decide (i=j)

set_option maxHeartbeats 800000 in
theorem necessary {h r b c z : Nat} (W : Fin (h+1) → Finset (Fin r))
    (H : Fit h r b c z W) :
    Function.Injective W ∧ (drops W).card < 2^b ∧
      HeightAtMost (Finset.univ.image W) (2^c) := by
  classical
  obtain ⟨C,D,wire,out,hcf,hcr,hdf,hdr,hco,hdo,hw,ho,hcn,hdn,hcost,hsem⟩ := H
  let cp : Fin r → Fin (h+2+C.size) := fun j=>⟨wire j,hw j⟩
  let dp : Fin (h+1) → Fin (r+2+D.size) := fun j=>⟨out j,ho j⟩
  have enc : ∀i j,(C.wires (List.ofFn (prefixInput i)++[false,true])).getD (cp j).val false=
      wordBits W i j := by
    intro i j
    have hi := (hsem (prefixSet i) i (prefixSet_sup i)).1
    rw [prefixSet_bits] at hi
    have hm : j∈Finset.univ.filter (fun j : Fin r=>
        (C.wires (List.ofFn (prefixInput i)++[false,true])).getD (wire j) false=true) ↔
        j∈W i := by rw [hi]
    apply Lib1401Suffix.bool_ext
    simpa only [cp,wordBits,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq] using hm
  have dec : ∀i j,(D.wires (List.ofFn (wordBits W i)++[false,true])).getD (dp j).val false=
      onehot i j := by
    intro i j
    have hi := hsem (prefixSet i) i (prefixSet_sup i)
    change _ = W i ∧ _ at hi
    have hv := hi.2 j
    rw [hi.1] at hv
    exact hv
  have inj : Function.Injective W := by
    intro i j hij
    have he : wordBits W i = wordBits W j := by funext a; simp only [wordBits,hij]
    have hi := dec i i
    have hj := dec j i
    rw [he] at hi
    have : onehot j i=true := hj.symm.trans (by simpa only [onehot,decide_true] using hi)
    exact (of_decide_eq_true this).symm
  refine ⟨inj,?_,?_⟩
  · exact (prefix_fits_iff W).mp ⟨C,cp,hcf,hcr,hco,hcn,enc⟩
  · exact (decoder_fits_iff W inj).mp ⟨D,dp,hdf,hdr,hdo,hdn,dec⟩

set_option maxHeartbeats 800000 in
theorem sufficient {h r b c : Nat} (W : Fin (h+1) → Finset (Fin r))
    (inj : Function.Injective W) (hb : (drops W).card < 2^b)
    (hc : HeightAtMost (Finset.univ.image W) (2^c)) :
    Fit h r b c (64*(r+1)*(h+1)) W := by
  classical
  obtain ⟨C,tap,hcf,hcr,hco,hcn,hcc,hcv⟩ := encoder_prefix W hb
  obtain ⟨B,rho,hbf,hbr,hbo,hbs,hbn,hbv⟩ := Lib1401Suffix.normalize C hcf hcr hco
  obtain ⟨D,out,hdf,hdr,hdo,hdn,hdc,hdv⟩ := decoder_upper W inj hc
  refine ⟨B,D,(fun j=>(rho (tap j)).val),(fun j=>(out j).val),
    hbf,hbr,hdf,hdr,hbo,hdo,(fun j=>(rho (tap j)).isLt),(fun j=>(out j).isLt),
    ?_,hdn,?_,?_⟩
  · omega
  · have hbc : B.size-notCount B≤C.size-notCount C+h := by omega
    nlinarith [Nat.zero_le (r*h)]
  · intro A i hi
    have hv (j : Fin r) :
        (B.wires (List.ofFn (fun j=>decide (j∈A))++[false,true])).getD (rho (tap j)).val false=
        wordBits W i j := by
      have H := hbv (fun j=>decide (j∈A)) (tap j)
      rw [Lib1401Suffix.suffix_rank A i hi] at H
      exact H.trans (hcv i j)
    have hm : Finset.univ.filter (fun j : Fin r=>
        (B.wires (List.ofFn (fun j=>decide (j∈A))++[false,true])).getD (rho (tap j)).val false=true)=W i := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hv,wordBits,decide_eq_true_eq]
    refine ⟨hm,?_⟩
    intro j
    change (D.wires (List.ofFn (fun j : Fin r=>decide (j∈_))++[false,true])).getD (out j).val false=decide (i=j)
    rw [hm]
    exact hdv i j

end Lib1401Full
end PEqualNP.Outside.L_lib_1401_aux

open PEqualNP.Outside.L_lib_1401_aux

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_lib_1401 :
  let fit := fun (h r b c z : Nat)
      (ok : Fin (h+1) → Finset (Fin r) → Prop) =>
    ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (wire : Fin r → Nat) (out : Fin (h+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
      C.output < h+2+C.size ∧ D.output < r+2+D.size ∧
      (∀ j, wire j < h+2+C.size) ∧ (∀ j, out j < r+2+D.size) ∧
      PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D ≤ c ∧
      (C.size - PEqualNP.NotBracket.notCount C) + (D.size - PEqualNP.NotBracket.notCount D) ≤ z ∧
      ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1) = i.val →
        let v := C.wires (List.ofFn (fun j : Fin h => decide (j ∈ A)) ++ [false,true])
        let msg := Finset.univ.filter (fun j : Fin r => v.getD (wire j) false = true)
        let w := D.wires (List.ofFn (fun j : Fin r => decide (j ∈ msg)) ++ [false,true])
        ok i msg ∧ ∀ j, w.getD (out j) false = decide (i = j)
  let heightAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (p : Nat) =>
    ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ p
  ∀ (h r b c : Nat) (W : Fin (h+1) → Finset (Fin r)),
    let ok := fun i u => u = W i
    let falls := (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card
    let test := Function.Injective W ∧ falls < 2^b ∧ heightAtMost (Finset.univ.image W) (2^c)
    ((∃ z, fit h r b c z ok) ↔ test) ∧ (test → fit h r b c (64*(r+1)*(h+1)) ok) := by
  classical
  dsimp only
  intro h r b c W
  change ((∃z,Lib1401Full.Fit h r b c z W) ↔
    Function.Injective W ∧ (Lib1401Packing.drops W).card < 2^b ∧
      Lib1401Decoder.HeightAtMost (Finset.univ.image W) (2^c)) ∧
    ((Function.Injective W ∧ (Lib1401Packing.drops W).card < 2^b ∧
      Lib1401Decoder.HeightAtMost (Finset.univ.image W) (2^c)) →
      Lib1401Full.Fit h r b c (64*(r+1)*(h+1)) W)
  refine ⟨⟨?_,?_⟩,?_⟩
  · rintro ⟨z,hz⟩
    exact Lib1401Full.necessary W hz
  · rintro ⟨hi,hb,hc⟩
    exact ⟨_,Lib1401Full.sufficient W hi hb hc⟩
  · rintro ⟨hi,hb,hc⟩
    exact Lib1401Full.sufficient W hi hb hc
