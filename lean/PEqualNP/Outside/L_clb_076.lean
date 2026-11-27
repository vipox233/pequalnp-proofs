import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_076_aux

open PEqualNP.CircuitLowerBounds

def gates46 : List Gate := [
  ⟨GateOp.and, [0, 6]⟩,
  ⟨GateOp.and, [12, 9]⟩,
  ⟨GateOp.and, [8, 2]⟩,
  ⟨GateOp.and, [14, 5]⟩,
  ⟨GateOp.or, [13, 15]⟩,
  ⟨GateOp.and, [9, 7]⟩,
  ⟨GateOp.and, [17, 2]⟩,
  ⟨GateOp.and, [4, 0]⟩,
  ⟨GateOp.and, [19, 8]⟩,
  ⟨GateOp.or, [18, 20]⟩,
  ⟨GateOp.and, [16, 21]⟩,
  ⟨GateOp.and, [22, 1]⟩,
  ⟨GateOp.or, [16, 21]⟩,
  ⟨GateOp.and, [24, 6]⟩,
  ⟨GateOp.and, [25, 1]⟩,
  ⟨GateOp.or, [23, 26]⟩,
  ⟨GateOp.and, [10, 27]⟩,
  ⟨GateOp.and, [4, 28]⟩,
  ⟨GateOp.and, [18, 20]⟩,
  ⟨GateOp.and, [13, 15]⟩,
  ⟨GateOp.or, [30, 31]⟩,
  ⟨GateOp.or, [29, 32]⟩,
  ⟨GateOp.and, [31, 30]⟩,
  ⟨GateOp.and, [11, 23]⟩,
  ⟨GateOp.and, [26, 35]⟩,
  ⟨GateOp.or, [34, 36]⟩,
  ⟨GateOp.and, [33, 37]⟩,
  ⟨GateOp.and, [32, 29]⟩,
  ⟨GateOp.and, [5, 7]⟩,
  ⟨GateOp.and, [40, 38]⟩,
  ⟨GateOp.or, [39, 41]⟩,
  ⟨GateOp.not, [42]⟩,
  ⟨GateOp.or, [34, 43]⟩,
  ⟨GateOp.and, [38, 44]⟩,
  ⟨GateOp.and, [44, 40]⟩,
  ⟨GateOp.and, [10, 46]⟩,
  ⟨GateOp.or, [45, 47]⟩,
  ⟨GateOp.or, [36, 33]⟩,
  ⟨GateOp.and, [48, 49]⟩,
  ⟨GateOp.not, [50]⟩,
  ⟨GateOp.or, [51, 43]⟩,
  ⟨GateOp.and, [44, 51]⟩,
  ⟨GateOp.or, [46, 53]⟩,
  ⟨GateOp.and, [7, 53]⟩,
  ⟨GateOp.or, [41, 55]⟩,
  ⟨GateOp.or, [45, 56]⟩
]

def circuit46 : Circuit := ⟨gates46, 52⟩

def outBit46 : Fin 3 → Fin (12 + circuit46.size)
  | ⟨0, _⟩ => ⟨52, by decide⟩
  | ⟨1, _⟩ => ⟨54, by decide⟩
  | ⟨2, _⟩ => ⟨57, by decide⟩

def isGoodGate (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | GateOp.or, [_, _] => true
  | GateOp.not, [_] => true
  | _, _ => false

theorem hgood_gates46 : gates46.all isGoodGate = true := by decide

theorem hfan46 : PEqualNP.MetaComplexity.FanInTwo circuit46 := by
  intro g hg
  have h1 : isGoodGate g = true := List.all_eq_true.mp hgood_gates46 g hg
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp [isGoodGate] at h1 ⊢
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp [isGoodGate] at h1 ⊢
  | not =>
    rcases ins with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [isGoodGate] at h1 ⊢
  | mod m => simp [isGoodGate] at h1
  | maj => simp [isGoodGate] at h1

theorem hreads46_bool :
    (List.range gates46.length).all (fun j =>
      (gates46.getD j ⟨GateOp.or, []⟩).inputs.all (fun i => decide (i < 12 + j))) = true := by
  decide

theorem hreads46 : PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 circuit46 := by
  intro j hj i hi
  have h1 := List.all_eq_true.mp hreads46_bool j (List.mem_range.mpr hj)
  have h2 := List.all_eq_true.mp h1 i hi
  exact of_decide_eq_true h2

theorem hsize46 : circuit46.size ≤ 46 := by decide

theorem hnot46 : PEqualNP.NotBracket.notCount circuit46 ≤ 2 := by decide

def evalGateFast (w : List Bool) (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => w.getD a false && w.getD b false
  | GateOp.or, [a, b] => w.getD a false || w.getD b false
  | GateOp.not, [a] => !(w.getD a false)
  | _, _ => false

def evalWiresFast (xs : List Bool) : List Bool :=
  gates46.foldl (fun w g => w ++ [evalGateFast w g]) xs

theorem evalGateFast_eq (g : Gate) (hg : isGoodGate g = true) (w : List Bool) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = evalGateFast w g := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp [isGoodGate, evalGateFast, GateOp.eval] at hg ⊢
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp [isGoodGate, evalGateFast, GateOp.eval] at hg ⊢
  | not =>
    rcases ins with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [isGoodGate, evalGateFast, GateOp.eval] at hg ⊢
  | mod m => simp [isGoodGate] at hg
  | maj => simp [isGoodGate] at hg

theorem foldl_evalGateFast_eq (gs : List Gate) (hgs : gs.all isGoodGate = true) :
    ∀ xs : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]) xs =
      gs.foldl (fun w g => w ++ [evalGateFast w g]) xs := by
  induction gs with
  | nil => intro xs; rfl
  | cons g rest ih =>
    intro xs
    simp only [List.all_cons, Bool.and_eq_true] at hgs
    simp only [List.foldl_cons, evalGateFast_eq g hgs.1 xs]
    exact ih hgs.2 _

theorem wires_eq_fast (xs : List Bool) : circuit46.wires xs = evalWiresFast xs :=
  foldl_evalGateFast_eq gates46 hgood_gates46 xs

def specBool (v0 v1 v2 v3 v4 v5 v6 v7 : Bool) : Bool × Bool × Bool × Bool :=
  let a1 := v0 || v1
  let a2 := v0 && v1
  let b1 := v2 || v3
  let b2 := v2 && v3
  let oab := a2 || b2
  let pab := a1 && b1
  let h3 := a2 && b2
  let t3 := oab && pab
  let t2 := oab || pab
  let t1 := a1 || b1
  let h4 := h3 || (t3 && v4)
  let u3 := t3 || (t2 && v4)
  let u2 := t2 || (t1 && v4)
  let u1 := t1 || v4
  let h5 := h4 || (u3 && v5)
  let w3 := u3 || (u2 && v5)
  let w2 := u2 || (u1 && v5)
  let h6 := h5 || (w3 && v6)
  let y3 := w3 || (w2 && v6)
  let h7 := h6 || (y3 && v7)
  let e0 := !h3
  let e1 := h3 || !h5
  let e2 := h3 || (h5 && !h4) || !h6
  (h7, e0, e1, e2)

def checkFast (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Bool) : Bool :=
  let v0 := x0 && x4 && x8
  let v1 := x0 && x6 && x9
  let v2 := x2 && x5 && x8
  let v3 := x2 && x7 && x9
  let v4 := x1 && x4 && x10
  let v5 := x1 && x6 && x11
  let v6 := x3 && x5 && x10
  let v7 := x3 && x7 && x11
  let sp := specBool v0 v1 v2 v3 v4 v5 v6 v7
  if sp.1 then
    let w := evalWiresFast [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]
    (w.getD 52 false == sp.2.1) &&
    (w.getD 54 false == sp.2.2.1) &&
    (w.getD 57 false == sp.2.2.2)
  else
    true

def allB (f : Bool → Bool) : Bool := f false && f true

theorem allB_spec {f : Bool → Bool} (h : allB f = true) (b : Bool) : f b = true := by
  simp only [allB, Bool.and_eq_true] at h
  cases b
  · exact h.1
  · exact h.2

def checkSlice (x0 x1 x2 x3 : Bool) : Bool :=
  allB fun x4 => allB fun x5 => allB fun x6 => allB fun x7 =>
  allB fun x8 => allB fun x9 => allB fun x10 => allB fun x11 =>
  checkFast x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11

theorem hcheck_0000 : checkSlice false false false false = true := rfl
theorem hcheck_0001 : checkSlice false false false true = true := rfl
theorem hcheck_0010 : checkSlice false false true false = true := rfl
theorem hcheck_0011 : checkSlice false false true true = true := rfl
theorem hcheck_0100 : checkSlice false true false false = true := rfl
theorem hcheck_0101 : checkSlice false true false true = true := rfl
theorem hcheck_0110 : checkSlice false true true false = true := rfl
theorem hcheck_0111 : checkSlice false true true true = true := rfl
theorem hcheck_1000 : checkSlice true false false false = true := rfl
theorem hcheck_1001 : checkSlice true false false true = true := rfl
theorem hcheck_1010 : checkSlice true false true false = true := rfl
theorem hcheck_1011 : checkSlice true false true true = true := rfl
theorem hcheck_1100 : checkSlice true true false false = true := rfl
theorem hcheck_1101 : checkSlice true true false true = true := rfl
theorem hcheck_1110 : checkSlice true true true false = true := rfl
theorem hcheck_1111 : checkSlice true true true true = true := rfl

theorem checkSlice_spec {x0 x1 x2 x3 : Bool} (h : checkSlice x0 x1 x2 x3 = true)
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    checkFast x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = true := by
  have h := allB_spec h x4
  have h := allB_spec h x5
  have h := allB_spec h x6
  have h := allB_spec h x7
  have h := allB_spec h x8
  have h := allB_spec h x9
  have h := allB_spec h x10
  exact allB_spec h x11

theorem checkFast_true (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    checkFast x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = true := by
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3
  · exact checkSlice_spec hcheck_0000 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0001 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0010 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0011 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0100 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0101 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0110 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_0111 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1000 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1001 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1010 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1011 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1100 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1101 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1110 x4 x5 x6 x7 x8 x9 x10 x11
  · exact checkSlice_spec hcheck_1111 x4 x5 x6 x7 x8 x9 x10 x11

theorem checkFast_extract (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (sp : Bool × Bool × Bool × Bool) (w : List Bool)
    (hsp : specBool (x0 && x4 && x8) (x0 && x6 && x9) (x2 && x5 && x8) (x2 && x7 && x9)
      (x1 && x4 && x10) (x1 && x6 && x11) (x3 && x5 && x10) (x3 && x7 && x11) = sp)
    (hw : evalWiresFast [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] = w)
    (hsp1 : sp.1 = true) :
    w.getD 52 false = sp.2.1 ∧ w.getD 54 false = sp.2.2.1 ∧ w.getD 57 false = sp.2.2.2 := by
  have hchk := checkFast_true x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
  dsimp only [checkFast] at hchk
  rw [hsp, hsp1] at hchk
  simp only [↓reduceIte, hw, Bool.and_eq_true, beq_iff_eq] at hchk
  exact ⟨hchk.1.1, hchk.1.2, hchk.2⟩

theorem specBool_correct (v0 v1 v2 v3 v4 v5 v6 v7 : Bool) :
    let vs : List Bool := [v0, v1, v2, v3, v4, v5, v6, v7]
    let sols : List (Fin 8) := (List.finRange 8).filter (fun z => vs.getD z.val false)
    let sp := specBool v0 v1 v2 v3 v4 v5 v6 v7
    sp.1 = decide (3 < sols.length) ∧
    (3 < sols.length →
      let z := sols.getD 3 ⟨0, by decide⟩
      sp.2.1 = z.val.testBit 2 ∧ sp.2.2.1 = z.val.testBit 1 ∧ sp.2.2.2 = z.val.testBit 0) := by
  cases v0 <;> cases v1 <;> cases v2 <;> cases v3 <;>
  cases v4 <;> cases v5 <;> cases v6 <;> cases v7 <;> decide

theorem finRange_pairwise_lt (n : Nat) : (List.finRange n).Pairwise (fun a b : Fin n => a.val < b.val) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp [hij]

theorem filter_lt_of_pairwise_get {n : Nat} {l : List (Fin n)}
    (hp : l.Pairwise (fun a b : Fin n => a.val < b.val)) {k : Nat} (hk : k < l.length) :
    (l.filter (fun y => decide (y.val < (l[k]).val))).length = k := by
  have hfeq : l.filter (fun y => decide (y.val < (l[k]).val)) = l.take k := by
    induction l generalizing k with
    | nil => simp at hk
    | cons a tl ih =>
      rw [List.pairwise_cons] at hp
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, List.take_zero, List.filter_cons, lt_irrefl, decide_false]
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        have hlt := hp.1 y hy
        simp [show ¬ y.val < a.val by omega]
      | succ k' =>
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.filter_cons]
        have hlt : a.val < (tl[k']'(by simp at hk; omega)).val := hp.1 _ (List.getElem_mem _)
        simp only [hlt, decide_true, ↓reduceIte, List.cons.injEq, true_and]
        exact ih hp.2 (by simp at hk; omega)
  rw [hfeq, List.length_take]
  omega

theorem viable_iff_table (table : Fin 3 → Bool → Bool → Bool) (z : Fin 8) :
    let v0 := table 0 false false && table 1 false false && table 2 false false
    let v1 := table 0 false false && table 1 false true && table 2 true false
    let v2 := table 0 false true && table 1 true false && table 2 false false
    let v3 := table 0 false true && table 1 true true && table 2 true false
    let v4 := table 0 true false && table 1 false false && table 2 false true
    let v5 := table 0 true false && table 1 false true && table 2 true true
    let v6 := table 0 true true && table 1 true false && table 2 false true
    let v7 := table 0 true true && table 1 true true && table 2 true true
    ([v0, v1, v2, v3, v4, v5, v6, v7].getD z.val false = true) ↔
      ∀ i : Fin 3, table i (z.val.testBit (2 - i.val)) (z.val.testBit (2 - ((i.val + 1) % 3))) = true := by
  intro v0 v1 v2 v3 v4 v5 v6 v7
  have h3 : ∀ (a b c : Bool) (P : Fin 3 → Bool),
      P 0 = a → P 1 = b → P 2 = c → ((a && b && c) = true ↔ ∀ i : Fin 3, P i = true) := by
    intro a b c P h0 h1 h2
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc⟩ i
      fin_cases i
      · exact h0.trans ha
      · exact h1.trans hb
      · exact h2.trans hc
    · intro h
      exact ⟨⟨h0.symm.trans (h 0), h1.symm.trans (h 1)⟩, h2.symm.trans (h 2)⟩
  fin_cases z
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl
  · exact h3 _ _ _ _ rfl rfl rfl

theorem outBit46_match (w : List Bool) (z : Fin 8)
    (h0 : w.getD 52 false = z.val.testBit 2)
    (h1 : w.getD 54 false = z.val.testBit 1)
    (h2 : w.getD 57 false = z.val.testBit 0) :
    ∀ pos : Fin 3, w.getD (outBit46 pos).val false = z.val.testBit (2 - pos.val) := by
  intro pos
  fin_cases pos
  · exact h0
  · exact h1
  · exact h2

theorem main_proof : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin 3 → Fin (12 + C.size)),
  PEqualNP.MetaComplexity.FanInTwo C ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 C ∧
  C.size ≤ 46 ∧ PEqualNP.NotBracket.notCount C ≤ 2 ∧
  ∀ table : Fin 3 → Bool → Bool → Bool,
    let inputs := (List.ofFn (fun i : Fin 3 =>
      [table i false false, table i true false, table i false true, table i true true])).flatten
    let sols := (Finset.univ : Finset (Fin 8)).filter (fun z => ∀ i : Fin 3,
      table i (z.val.testBit (2 - i.val)) (z.val.testBit (2 - ((i.val + 1) % 3))) = true)
    3 < sols.card → ∃ z ∈ sols, (sols.filter (fun y => y.val < z.val)).card = 3 ∧
      ∀ pos : Fin 3, (C.wires inputs).getD (outBit pos).val false = z.val.testBit (2 - pos.val) := by
  refine ⟨circuit46, outBit46, hfan46, hreads46, hsize46, hnot46, ?_⟩
  intro table inputs sols hcard
  let x0 := table 0 false false
  let x1 := table 0 true false
  let x2 := table 0 false true
  let x3 := table 0 true true
  let x4 := table 1 false false
  let x5 := table 1 true false
  let x6 := table 1 false true
  let x7 := table 1 true true
  let x8 := table 2 false false
  let x9 := table 2 true false
  let x10 := table 2 false true
  let x11 := table 2 true true
  have hin_eq : inputs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
    dsimp only [inputs, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]
    simp [List.ofFn_succ]
  let v0 := x0 && x4 && x8
  let v1 := x0 && x6 && x9
  let v2 := x2 && x5 && x8
  let v3 := x2 && x7 && x9
  let v4 := x1 && x4 && x10
  let v5 := x1 && x6 && x11
  let v6 := x3 && x5 && x10
  let v7 := x3 && x7 && x11
  let vs : List Bool := [v0, v1, v2, v3, v4, v5, v6, v7]
  let solsL : List (Fin 8) := (List.finRange 8).filter (fun z => vs.getD z.val false)
  have hsols_eq : solsL.toFinset = sols := by
    ext z
    simp only [List.mem_toFinset, solsL, List.mem_filter, List.mem_finRange, true_and,
      sols, Finset.mem_filter, Finset.mem_univ]
    exact viable_iff_table table z
  have hpw : solsL.Pairwise (fun a b : Fin 8 => a.val < b.val) :=
    (finRange_pairwise_lt 8).filter _
  have hnodup : solsL.Nodup :=
    hpw.imp (fun {a b} h => fun heq => by subst heq; omega)
  have hcard_eq : sols.card = solsL.length := by
    rw [← hsols_eq, List.toFinset_card_of_nodup hnodup]
  have hlen_gt3 : 3 < solsL.length := by omega
  let z : Fin 8 := solsL[3]'hlen_gt3
  have hz_mem : z ∈ sols := by
    rw [← hsols_eq, List.mem_toFinset]
    exact List.getElem_mem hlen_gt3
  have hrank : (sols.filter (fun y => y.val < z.val)).card = 3 := by
    have hfeq : sols.filter (fun y => y.val < z.val) =
        (solsL.filter (fun y => decide (y.val < z.val))).toFinset := by
      ext y
      simp only [Finset.mem_filter, ← hsols_eq, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    rw [hfeq, List.toFinset_card_of_nodup (hnodup.filter _)]
    exact filter_lt_of_pairwise_get hpw hlen_gt3
  have hsb := specBool_correct v0 v1 v2 v3 v4 v5 v6 v7
  generalize hsp : specBool v0 v1 v2 v3 v4 v5 v6 v7 = sp at hsb
  have hsp1 : sp.1 = true := by
    rw [hsb.1]; exact decide_eq_true hlen_gt3
  have hsb_outs := hsb.2 hlen_gt3
  have hz_getD : solsL.getD 3 ⟨0, by decide⟩ = z := by
    simp [z, List.getD_eq_getElem?_getD, hlen_gt3]
  rw [hz_getD] at hsb_outs
  have hw_eq : circuit46.wires inputs = evalWiresFast [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
    rw [hin_eq, wires_eq_fast]
  generalize hw : evalWiresFast [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] = w at hw_eq
  have hchk := checkFast_extract x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 sp w hsp hw hsp1
  refine ⟨z, hz_mem, hrank, ?_⟩
  rw [hw_eq]
  exact outBit46_match w z (hchk.1.trans hsb_outs.1) (hchk.2.1.trans hsb_outs.2.1) (hchk.2.2.trans hsb_outs.2.2)

end PEqualNP.Outside.L_clb_076_aux

theorem PEqualNP.Outside.L_clb_076 : (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin 3 → Fin (12 + C.size)),
  PEqualNP.MetaComplexity.FanInTwo C ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack 12 C ∧
  C.size ≤ 46 ∧ PEqualNP.NotBracket.notCount C ≤ 2 ∧
  ∀ table : Fin 3 → Bool → Bool → Bool,
    let inputs := (List.ofFn (fun i : Fin 3 =>
      [table i false false, table i true false, table i false true, table i true true])).flatten
    let sols := (Finset.univ : Finset (Fin 8)).filter (fun z => ∀ i : Fin 3,
      table i (z.val.testBit (2 - i.val)) (z.val.testBit (2 - ((i.val + 1) % 3))) = true)
    3 < sols.card → ∃ z ∈ sols, (sols.filter (fun y => y.val < z.val)).card = 3 ∧
      ∀ pos : Fin 3, (C.wires inputs).getD (outBit pos).val false = z.val.testBit (2 - pos.val)) :=
  PEqualNP.Outside.L_clb_076_aux.main_proof
