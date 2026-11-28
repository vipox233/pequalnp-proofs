import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1440
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

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

theorem emptyCircuit_fanInTwo : FanInTwo emptyCircuit := by
  simp [FanInTwo,emptyCircuit]

theorem emptyCircuit_readsBack (n : Nat) : ReadsBack n emptyCircuit := by
  simp [ReadsBack,emptyCircuit]

theorem appendGate_prefix (C : Circuit) (g : Gate) : C.gates <+: (appendGate C g).gates :=
  ⟨[g],rfl⟩

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

def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendGates (C : Circuit) (gates : List Gate) : Circuit := ⟨C.gates ++ gates, C.output⟩

def appendFamily {k : Nat} (C : Circuit) (gate : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn gate)

private theorem appendGates_cons (C : Circuit) (g : Gate) (rest : List Gate) :
    appendGates C (g :: rest) = appendGates (appendGate C g) rest := by
  simp [appendGates,appendGate,List.append_assoc]

theorem appendGates_prefix (C : Circuit) (gates : List Gate) : C.gates <+: (appendGates C gates).gates :=
  ⟨gates,rfl⟩

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
    (appendFamily C gate).size = C.size + k := by simp [appendFamily,appendGates,Circuit.size]

@[local simp] theorem appendFamily_nextWire {k : Nat} (n : Nat) (C : Circuit) (gate : Fin k → Gate) :
    nextWire n (appendFamily C gate) = nextWire n C + k := by simp [nextWire,Nat.add_assoc]

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

private abbrev Sound (n : Nat) := Good (fun _ => True) n
private abbrev Tap (n : Nat) := Live (fun _ => True) n

private theorem many {X : Type*} {n cost : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length = n) (base : Circuit) :
    ∀ (rows : Nat) (pred : Fin rows → X → Prop),
    (∀ i C, base.gates <+: C.gates → Sound n C →
      ∃ D w, Sound n D ∧ C.gates <+: D.gates ∧ Tap n D w ∧
        D.size ≤ C.size + cost ∧ notCount D = notCount C ∧
        ∀ x, value D (input x) w = true ↔ pred i x) →
    ∀ C, base.gates <+: C.gates → Sound n C →
      ∃ D, ∃ out : Fin rows → Nat, Sound n D ∧ C.gates <+: D.gates ∧
        (∀ i, Tap n D (out i)) ∧ D.size ≤ C.size + rows * cost ∧
        notCount D = notCount C ∧ ∀ i x, value D (input x) (out i) = true ↔ pred i x := by
  intro rows
  induction rows with
  | zero =>
    intro pred emit C ext good
    exact ⟨C, Fin.elim0, good, List.prefix_refl _, fun i => i.elim0, by simp, rfl, fun i => i.elim0⟩
  | succ rows ih =>
    intro pred emit C ext good
    obtain ⟨mid, first, gm, cm, lm, sm, nm, vm⟩ := emit 0 C ext good
    obtain ⟨D, rest, gd, md, ld, sd, nd, vd⟩ := ih (fun i => pred i.succ)
      (fun i => emit i.succ) mid (ext.trans cm) gm
    refine ⟨D, Fin.cases first rest, gd, cm.trans md, ?_, ?_, nd.trans nm, ?_⟩
    · exact Fin.cases (live_extend md lm) ld
    · rw [Nat.succ_mul]; omega
    · exact Fin.cases (fun x => (old_value md (len x) lm.1) ▸ vm x) vd

private def inputs {r : Nat} (x : Finset (Fin r)) :=
  List.ofFn (fun j : Fin r => decide (j ∈ x)) ++ [false,true]

private theorem input_len {r : Nat} (x : Finset (Fin r)) : (inputs x).length = r+2 := by
  simp [inputs]

private theorem input_at {r : Nat} (C : Circuit) (x : Finset (Fin r)) (j : Fin r) :
    value C (inputs x) j.val = decide (j ∈ x) := by
  rw [value_input _ _ (by rw [input_len]; omega)]
  simp [inputs, List.getD_eq_getElem?_getD, List.getElem?_append, j.isLt]

private theorem input_const {r : Nat} (C : Circuit) (x : Finset (Fin r)) :
    value C (inputs x) (r+1) = true ∧ value C (inputs x) r = false := by
  rw [value_input _ _ (by rw [input_len]; omega),value_input _ _ (by rw [input_len]; omega)]
  simp [inputs,List.getD_eq_getElem?_getD,List.getElem?_append]

private def rowsMap {m r k : Nat} (rows : Fin m → Finset (Fin r))
    (budget : Fin m → Nat) (out : Fin m → Finset (Fin k)) (x : Finset (Fin r)) : Finset (Fin k) :=
  Finset.univ.filter fun j => ∃ i, j ∈ out i ∧ (rows i \ x).card ≤ budget i

private theorem rows_mem {m r k : Nat} {rows : Fin m → Finset (Fin r)}
    {budget : Fin m → Nat} {out : Fin m → Finset (Fin k)} {x : Finset (Fin r)} {j : Fin k} :
    j ∈ rowsMap rows budget out x ↔ ∃ i, j ∈ out i ∧ (rows i \ x).card ≤ budget i := by
  simp [rowsMap]

private theorem rows_mono {m r k : Nat} (rows : Fin m → Finset (Fin r))
    (budget : Fin m → Nat) (out : Fin m → Finset (Fin k)) : Monotone (rowsMap rows budget out) := by
  intro x y h j hj
  obtain ⟨i, mem, card⟩ := rows_mem.mp hj
  exact rows_mem.mpr ⟨i,mem,(Finset.card_le_card (Finset.sdiff_subset_sdiff_right _ h)).trans card⟩

private def Built {r k : Nat} (bound : Nat) (g : Finset (Fin r) → Finset (Fin k)) :=
  ∃ (D : Circuit) (out : Fin k → Nat), (FanInTwo D ∧ ReadsBack (r+2) D ∧ D.output < r+2+D.size) ∧
    notCount D=0 ∧ D.size ≤ bound ∧ (∀ j, out j < r+2+D.size) ∧ ∀ X,
    Finset.univ.filter (fun j => value D (inputs X) (out j) = true) = g X

private theorem build_rows {m r k width : Nat} (rows : Fin m → Finset (Fin r))
    (budget : Fin m → Nat) (out : Fin m → Finset (Fin k))
    (small : ∀ i, min (budget i) r < width) :
    Built (m*(2*width*r)+k*(2*m)) (rowsMap rows budget out) := by
  classical
  let good : Sound (r+2) emptyCircuit := ⟨emptyCircuit_fanInTwo,emptyCircuit_readsBack _,by simp [emptyCircuit]⟩
  have raw (C : Circuit) (w : Nat) (hw : w < r+2) : Tap (r+2) C w :=
    ⟨by unfold nextWire; omega, trivial⟩
  have row (i : Fin m) (C : Circuit) (_ : emptyCircuit.gates <+: C.gates) (gc : Sound (r+2) C) :=
    counter_bank (w := width) inputs (@input_len r) false (r+1) r ((rows i).toList.map Fin.val)
      C gc (raw C _ (by omega)) (raw C _ (by omega)) (input_const C)
      (by intro w hw; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw; exact raw C _ (by omega))
  obtain ⟨A, taps, ga, _, la, sa, na, va⟩ := many (cost := 2*width*r) inputs (@input_len r)
    emptyCircuit m (fun i x => (rows i \ x).card ≤ budget i) (by
      intro i C ext gc
      obtain ⟨D, wires, gd, cd, ld, sd, nd, vd⟩ := row i C ext gc
      let j : Fin width := ⟨_,small i⟩
      refine ⟨D,wires j,gd,cd,ld j,?_,nd,?_⟩
      · rw [sd,List.length_map,Finset.length_toList]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (card_finset_fin_le _)) _
      · intro x
        have count : (((rows i).toList.map Fin.val).countP fun a => value C (inputs x) a == false) = (rows i \ x).card := by
          rw [List.countP_map]
          have eq : (fun z : Fin r => (value C (inputs x) z.val == false)) = (fun z => decide (z ∉ x)) := by
            funext z; simp [input_at]
          change ((rows i).toList.countP (fun z => value C (inputs x) z.val == false)) = _
          rw [eq, ← (rows i).nodup_toList.card_eq_countP (P := fun z => z ∉ x)]
          congr 1
          ext z; simp
        rw [vd,count]
        simp only [cntSignal, Bool.false_eq_true, if_false,decide_eq_true_eq]
        have := card_finset_fin_le (rows i \ x)
        dsimp [j]; omega) emptyCircuit (List.prefix_refl _) good
  obtain ⟨D, wires, gd, _, ld, sd, nd, vd⟩ := many (cost := 2*m) inputs (@input_len r) A k
    (fun j x => j ∈ rowsMap rows budget out x) (by
      intro j C ext gc
      let sel := Finset.univ.filter (fun i => j ∈ out i)
      obtain ⟨D,w,gd,cd,ld,sd,nd,vd⟩ := counter_bank (w := 1) inputs (@input_len r) true
        (r+1) r (sel.toList.map taps) C gc (raw C _ (by omega)) (raw C _ (by omega)) (input_const C)
        (by intro w hw; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw; exact live_extend ext (la i))
      refine ⟨D,w 0,gd,cd,ld 0,?_,nd,?_⟩
      · rw [sd,List.length_map,Finset.length_toList]
        have := card_finset_fin_le sel; omega
      · intro x
        rw [vd,rows_mem]
        simp only [cntSignal,if_true,Fin.val_zero,zero_add,decide_eq_true_eq]
        change 0 < List.countP _ _ ↔ _
        rw [List.countP_pos_iff]
        simp [sel, old_value ext (input_len x) (la _).1, va, and_comm, and_left_comm, and_assoc])
    A (List.prefix_refl _) ga
  refine ⟨withOutput D 0,wires,⟨gd.1,gd.2.1,by change 0 < r+2+D.size; omega⟩,nd.trans na,?_,fun j => (ld j).1,?_⟩
  · change D.size ≤ _
    change A.size ≤ 0 + _ at sa
    omega
  · intro x
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact vd j x

private abbrev Cover {m r k : Nat} (A B : Fin m → Finset (Fin r))
    (a f : Fin m → Nat) (P N : Fin m → Finset (Fin k)) :=
  ∀ i j, (A i ⊆ B j → Disjoint (P i) (N j)) ∧ (¬ A i ⊆ B j → a i+f j < ((P i) ∩ (N j)).card)

private theorem necessary {m r k : Nat} {A B : Fin m → Finset (Fin r)} {a f : Fin m → Nat}
    (boxes : ∀ i, A i ⊆ B i) (g : Finset (Fin r) → Finset (Fin k))
    (h : Finset (Fin k) → Finset (Fin r)) (gm : Monotone g) (hm : Monotone h)
    (recovers : ∀ i X Y, A i ⊆ X → X ⊆ B i → (g X \ Y).card ≤ a i → (Y \ g X).card ≤ f i →
      A i ⊆ h Y ∧ h Y ⊆ B i) : Cover A B a f (fun i => g (A i)) (fun j => (g (B j))ᶜ) := by
  classical
  intro i j
  let L := g (A i)
  let U := g (B j)
  change (A i ⊆ B j → Disjoint L Uᶜ) ∧ (¬ A i ⊆ B j → a i + f j < (L ∩ Uᶜ).card)
  constructor
  · intro compatible
    exact Finset.disjoint_left.mpr fun x hx hn => (Finset.mem_compl.mp hn) (gm compatible hx)
  · intro incompatible
    by_contra! few
    have diff : L ∩ Uᶜ = L \ U := by ext x; simp
    rw [diff] at few
    obtain ⟨T, sub, size⟩ := Finset.exists_subset_card_eq (min_le_right (f j) (L \ U).card)
    let Y := U ∪ T
    have losses : (L \ (L ∩ Y)).card ≤ a i := by
      have eq : L \ (L ∩ Y) = (L \ U) \ T := by ext x; simp [Y]; tauto
      rw [eq,Finset.card_sdiff_of_subset sub,size]; omega
    have gains : (Y \ U).card ≤ f j := by
      have sub' : Y \ U ⊆ T := by
        intro x hx
        obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp hx
        exact (Finset.mem_union.mp hu).resolve_left hn
      exact (Finset.card_le_card sub').trans (size.trans_le (min_le_left ..))
    have incl : L ∩ Y ⊆ Y := Finset.inter_subset_right
    have low := (recovers i (A i) (L ∩ Y) (Finset.Subset.refl _) (boxes i) losses (by
      change ((L ∩ Y) \ L).card ≤ _
      simp [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.inter_subset_left : L ∩ Y ⊆ L)])).1
    have high := (recovers j (B j) Y (boxes j) (Finset.Subset.refl _) (by
      change (U \ (U ∪ T)).card ≤ _
      simp [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_union_left : U ⊆ U ∪ T)]) gains).2
    exact incompatible (low.trans ((hm incl).trans high))

private theorem properties {m r k : Nat} {A B : Fin m → Finset (Fin r)} {a f : Fin m → Nat}
    {P N : Fin m → Finset (Fin k)} (cov : Cover A B a f P N) :
    (∀ i X, A i ⊆ X → X ⊆ B i → P i ⊆ rowsMap A (fun _ => 0) P X ∧ Disjoint (N i) (rowsMap A (fun _ => 0) P X)) ∧
    ∀ i Y, (P i \ Y).card ≤ a i → ((N i) ∩ Y).card ≤ f i →
      A i ⊆ rowsMap P a A Y ∧ rowsMap P a A Y ⊆ B i := by
  classical
  constructor
  · intro i X lo hi
    constructor
    · exact fun j hj => rows_mem.mpr ⟨i,hj,by simp [Finset.sdiff_eq_empty_iff_subset.mpr lo]⟩
    · apply Finset.disjoint_left.mpr
      intro j neg pos
      obtain ⟨t,ht,missing⟩ := rows_mem.mp pos
      have sub : A t ⊆ X := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp (by omega))
      exact Finset.disjoint_left.mp ((cov t i).1 (sub.trans hi)) ht neg
  · intro i Y lost gained
    constructor
    · exact fun j hj => rows_mem.mpr ⟨i,hj,lost⟩
    · intro j hj
      obtain ⟨t,mem,cap⟩ := rows_mem.mp hj
      by_contra no
      have bound := (cov t i).2 (fun incl => no (incl mem))
      have incl : P t ∩ N i ⊆ (P t \ Y) ∪ (N i ∩ Y) := by
        intro z hz; simp at hz ⊢; tauto
      have := (Finset.card_le_card incl).trans (Finset.card_union_le ..)
      omega

end PEqualNP.Outside.L_lib_1440

open PEqualNP.Outside.L_lib_1440

theorem PEqualNP.Outside.L_lib_1440 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let bits := fun {r : Nat} (X : Finset (Fin r)) => List.ofFn (fun j : Fin r => decide (j ∈ X)) ++ [false,true]
let valid := fun (r : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧ D.output < r+2+D.size
let bank := fun {r k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin k → Nat) (X : Finset (Fin r)) =>
  Finset.univ.filter (fun j : Fin k => (D.wires (bits X)).getD (out j) false = true)
let build := fun {r k : Nat} (s : Nat) (g : Finset (Fin r) → Finset (Fin k)) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin k → Nat), valid r D ∧ PEqualNP.NotBracket.notCount D=0 ∧
    D.size ≤ s ∧ (∀ j, o j < r+2+D.size) ∧ ∀ X, bank D o X=g X
let cover := fun {m r k : Nat} (A B : Fin m → Finset (Fin r)) (a f : Fin m → Nat) (P N : Fin m → Finset (Fin k)) =>
  ∀ i j, (A i ⊆ B j → Disjoint (P i) (N j)) ∧ (¬ A i ⊆ B j → a i+f j < ((P i) ∩ (N j)).card)
∀ (m r k : Nat) (A B : Fin m → Finset (Fin r)) (a f : Fin m → Nat), (∀ i, A i ⊆ B i) →
  let possible := ∃ (g : Finset (Fin r) → Finset (Fin k)) (h : Finset (Fin k) → Finset (Fin r)),
    Monotone g ∧ Monotone h ∧ ∀ i X Y, A i ⊆ X → X ⊆ B i →
      (g X \ Y).card ≤ a i → (Y \ g X).card ≤ f i → A i ⊆ h Y ∧ h Y ⊆ B i
  (possible ↔ ∃ P N : Fin m → Finset (Fin k), cover A B a f P N) ∧
  ∀ P N : Fin m → Finset (Fin k), cover A B a f P N →
    ∃ (g : Finset (Fin r) → Finset (Fin k)) (h : Finset (Fin k) → Finset (Fin r)),
      build (4*(m+1)*(r+k+1)) g ∧ build (8*(m+1)*((k+1)^2+r+1)) h ∧
      (∀ i X, A i ⊆ X → X ⊆ B i → P i ⊆ g X ∧ Disjoint (N i) (g X)) ∧
      ∀ i Y, (P i \ Y).card ≤ a i → ((N i) ∩ Y).card ≤ f i → A i ⊆ h Y ∧ h Y ⊆ B i) := by
  classical
  dsimp only
  intro m r k A B a f boxes
  have eqFin (n : Nat) : (fun i j : Fin n => Classical.propDecidable (i = j)) = instDecidableEqFin n := Subsingleton.elim ..
  have sameBits {n : Nat} (X : Finset (Fin n)) : (List.ofFn (fun j : Fin n => @decide (j ∈ X) (Classical.propDecidable _)) ++ [false,true]) = inputs X := by
    unfold inputs
    congr 1
    apply congrArg List.ofFn
    funext j
    congr 1
  rw [eqFin k]
  constructor
  · constructor
    · rintro ⟨g,h,gm,hm,rec⟩
      exact ⟨_,_,necessary boxes g h gm hm rec⟩
    · rintro ⟨P,N,cov⟩
      obtain ⟨enc,dec⟩ := properties (show Cover A B a f P N from cov)
      refine ⟨rowsMap A (fun _ => 0) P,rowsMap P a A,rows_mono ..,rows_mono ..,?_⟩
      intro i X Y lo hi lost gained
      obtain ⟨pos,neg⟩ := enc i X lo hi
      apply dec i Y
      · exact (Finset.card_le_card (Finset.sdiff_subset_sdiff_left _ pos)).trans lost
      · apply LE.le.trans (Finset.card_le_card _) gained
        intro z hz
        obtain ⟨hn,hy⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_sdiff.mpr ⟨hy,Finset.disjoint_left.mp neg hn⟩
  · intro P N cov
    obtain ⟨enc,dec⟩ := properties (show Cover A B a f P N from cov)
    refine ⟨_,_,?_,?_,enc,dec⟩
    · obtain ⟨D,o,v,n,s,live,sem⟩ := build_rows (width := 1) A (fun _ => 0) P (by simp)
      refine ⟨D,o,v,n,by apply s.trans; nlinarith,live,?_⟩
      intro X
      rw [← sem X]
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,value,sameBits]
      exact ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,fun h => (Finset.mem_filter.mp h).2⟩
    · obtain ⟨D,o,v,n,s,live,sem⟩ := build_rows (width := k+1) P a A (fun i => by omega)
      refine ⟨D,o,v,n,by apply s.trans; nlinarith,live,?_⟩
      intro X
      rw [← sem X]
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,value,sameBits]
      exact ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,fun h => (Finset.mem_filter.mp h).2⟩
