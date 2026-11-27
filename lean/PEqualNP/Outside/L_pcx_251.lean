import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_251_aux

namespace WordCircuit
open PEqualNP.CircuitLowerBounds

theorem testBit_two_mul_add_bool (h : Nat) (c : Bool) (r : Nat) :
    (2 * h + c.toNat).testBit r = if r = 0 then c else h.testBit (r - 1) := by
  cases r with
  | zero =>
    rw [Nat.testBit_zero]
    cases c <;> simp
  | succ r =>
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.testBit_succ]
    have hdiv : (2 * h + c.toNat) / 2 = h := by cases c <;> (simp only [Bool.toNat_false, Bool.toNat_true]; omega)
    rw [hdiv]

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalW (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl stepWire x

def wireVal (x : List Bool) (gs : List Gate) (idx : Nat) : Bool :=
  (evalW x gs).getD idx false

def GoodGates (inputs : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < inputs + j)

def Extends (gs gs' : List Gate) : Prop :=
  ∃ ext, gs' = gs ++ ext

theorem Extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], by simp⟩

theorem Extends_trans {a b c : List Gate} (h1 : Extends a b) (h2 : Extends b c) :
    Extends a c := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

theorem Extends_len {a b : List Gate} (h : Extends a b) : a.length ≤ b.length := by
  rcases h with ⟨e, rfl⟩
  simp

theorem evalW_len (x : List Bool) (gs : List Gate) :
    (evalW x gs).length = x.length + gs.length := by
  unfold evalW
  induction gs generalizing x with
  | nil => simp
  | cons g tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWire x g)]
    simp [stepWire]
    omega

theorem evalW_append (x : List Bool) (gs1 gs2 : List Gate) :
    evalW x (gs1 ++ gs2) = evalW (evalW x gs1) gs2 := by
  unfold evalW
  rw [List.foldl_append]

theorem stepWire_getD_lt (w : List Bool) (g : Gate) {i : Nat} (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem stepWire_getD_self (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

theorem wireVal_extends {x : List Bool} {gs1 gs2 : List Gate} {idx : Nat}
    (hext : Extends gs1 gs2) (hidx : idx < x.length + gs1.length) :
    wireVal x gs2 idx = wireVal x gs1 idx := by
  rcases hext with ⟨ext, rfl⟩
  unfold wireVal
  rw [evalW_append]
  have hlen : idx < (evalW x gs1).length := by rw [evalW_len]; exact hidx
  generalize evalW x gs1 = w at hlen ⊢
  unfold evalW
  induction ext generalizing w with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.foldl_cons]
    have hlen' : idx < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlen', stepWire_getD_lt w g hlen]

theorem wireVal_snoc_self (x : List Bool) (gs : List Gate) (g : Gate) :
    wireVal x (gs ++ [g]) (x.length + gs.length) =
      g.op.eval (g.inputs.map (wireVal x gs)) := by
  unfold wireVal
  rw [evalW_append]
  unfold evalW
  simp only [List.foldl_cons, List.foldl_nil]
  have hlen : x.length + gs.length = (gs.foldl stepWire x).length := (evalW_len x gs).symm
  rw [hlen, stepWire_getD_self]

theorem GoodGates_snoc {inputs : Nat} {gs : List Gate} {g : Gate}
    (hg : GoodGates inputs gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < inputs + gs.length) :
    GoodGates inputs (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hg.1 g' h1
    · rw [List.mem_singleton.mp h2]
      exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hg.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hback i hi

def addAnd (inputs : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  (gs ++ [⟨.and, [a, b]⟩], inputs + gs.length)

def addNot (inputs : Nat) (gs : List Gate) (a : Nat) : List Gate × Nat :=
  (gs ++ [⟨.not, [a]⟩], inputs + gs.length)

theorem addAnd_spec {inputs : Nat} {gs : List Gate} {a b : Nat}
    (hg : GoodGates inputs gs) (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let r := addAnd inputs gs a b
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = (wireVal x gs a && wireVal x gs b) := by
  refine ⟨⟨[⟨.and, [a, b]⟩], rfl⟩, by simp [addAnd],
    GoodGates_snoc hg (by simp) (by simp) (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega),
    by simp [addAnd], ?_⟩
  intro x hx
  dsimp only [addAnd]
  rw [← hx, wireVal_snoc_self]
  simp [GateOp.eval]

theorem addNot_spec {inputs : Nat} {gs : List Gate} {a : Nat}
    (hg : GoodGates inputs gs) (ha : a < inputs + gs.length) :
    let r := addNot inputs gs a
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = !(wireVal x gs a) := by
  refine ⟨⟨[⟨.not, [a]⟩], rfl⟩, by simp [addNot],
    GoodGates_snoc hg (by simp) (by simp) (fun i hi => by simp at hi; subst hi; exact ha),
    by simp [addNot], ?_⟩
  intro x hx
  dsimp only [addNot]
  rw [← hx, wireVal_snoc_self]
  simp [GateOp.eval]

def addFullAdder (inputs : Nat) (gs : List Gate) (a b cin : Nat) :
    List Gate × Nat × Nat :=
  let p := inputs + gs.length
  let g1 := gs ++ [⟨.or, [a, b]⟩]
  let g2 := g1 ++ [⟨.and, [a, b]⟩]
  let g3 := g2 ++ [⟨.not, [p + 1]⟩]
  let g4 := g3 ++ [⟨.and, [p, p + 2]⟩]
  let g5 := g4 ++ [⟨.or, [p + 3, cin]⟩]
  let g6 := g5 ++ [⟨.and, [p + 3, cin]⟩]
  let g7 := g6 ++ [⟨.not, [p + 5]⟩]
  let g8 := g7 ++ [⟨.and, [p + 4, p + 6]⟩]
  let g9 := g8 ++ [⟨.or, [p + 1, p + 5]⟩]
  (g9, p + 7, p + 8)

theorem fullAdder_bool (a b c : Bool) :
    let s1 := (a || b) && !(a && b)
    let sum := (s1 || c) && !(s1 && c)
    let cout := (a && b) || (s1 && c)
    a.toNat + b.toNat + c.toNat = sum.toNat + 2 * cout.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem addFullAdder_spec {inputs : Nat} {gs : List Gate} {a b cin : Nat}
    (hg : GoodGates inputs gs)
    (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) (hc : cin < inputs + gs.length) :
    let r := addFullAdder inputs gs a b cin
    Extends gs r.1 ∧ r.1.length = gs.length + 9 ∧ GoodGates inputs r.1 ∧
    r.2.1 < inputs + r.1.length ∧ r.2.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      (wireVal x gs a).toNat + (wireVal x gs b).toNat + (wireVal x gs cin).toNat =
        (wireVal x r.1 r.2.1).toNat + 2 * (wireVal x r.1 r.2.2).toNat := by
  unfold addFullAdder
  set p := inputs + gs.length
  set g1 := gs ++ [⟨.or, [a, b]⟩]
  set g2 := g1 ++ [⟨.and, [a, b]⟩]
  set g3 := g2 ++ [⟨.not, [p + 1]⟩]
  set g4 := g3 ++ [⟨.and, [p, p + 2]⟩]
  set g5 := g4 ++ [⟨.or, [p + 3, cin]⟩]
  set g6 := g5 ++ [⟨.and, [p + 3, cin]⟩]
  set g7 := g6 ++ [⟨.not, [p + 5]⟩]
  set g8 := g7 ++ [⟨.and, [p + 4, p + 6]⟩]
  set g9 := g8 ++ [⟨.or, [p + 1, p + 5]⟩]
  have hl1 : g1.length = gs.length + 1 := by simp [g1]
  have hl2 : g2.length = gs.length + 2 := by simp [g2, hl1]
  have hl3 : g3.length = gs.length + 3 := by simp [g3, hl2]
  have hl4 : g4.length = gs.length + 4 := by simp [g4, hl3]
  have hl5 : g5.length = gs.length + 5 := by simp [g5, hl4]
  have hl6 : g6.length = gs.length + 6 := by simp [g6, hl5]
  have hl7 : g7.length = gs.length + 7 := by simp [g7, hl6]
  have hl8 : g8.length = gs.length + 8 := by simp [g8, hl7]
  have hl9 : g9.length = gs.length + 9 := by simp [g9, hl8]
  have he1 : Extends gs g1 := ⟨_, rfl⟩
  have he2 : Extends g1 g2 := ⟨_, rfl⟩
  have he3 : Extends g2 g3 := ⟨_, rfl⟩
  have he4 : Extends g3 g4 := ⟨_, rfl⟩
  have he5 : Extends g4 g5 := ⟨_, rfl⟩
  have he6 : Extends g5 g6 := ⟨_, rfl⟩
  have he7 : Extends g6 g7 := ⟨_, rfl⟩
  have he8 : Extends g7 g8 := ⟨_, rfl⟩
  have he9 : Extends g8 g9 := ⟨_, rfl⟩
  have hg1 : GoodGates inputs g1 := GoodGates_snoc hg (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg2 : GoodGates inputs g2 := GoodGates_snoc hg1 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg3 : GoodGates inputs g3 := GoodGates_snoc hg2 (by simp) (by simp) (by intro i hi; simp at hi; subst hi; omega)
  have hg4 : GoodGates inputs g4 := GoodGates_snoc hg3 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg5 : GoodGates inputs g5 := GoodGates_snoc hg4 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg6 : GoodGates inputs g6 := GoodGates_snoc hg5 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg7 : GoodGates inputs g7 := GoodGates_snoc hg6 (by simp) (by simp) (by intro i hi; simp at hi; subst hi; omega)
  have hg8 : GoodGates inputs g8 := GoodGates_snoc hg7 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have hg9 : GoodGates inputs g9 := GoodGates_snoc hg8 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  refine ⟨Extends_trans he1 (Extends_trans he2 (Extends_trans he3 (Extends_trans he4
    (Extends_trans he5 (Extends_trans he6 (Extends_trans he7 (Extends_trans he8 he9))))))),
    hl9, hg9, by change p + 7 < inputs + g9.length; omega, by change p + 8 < inputs + g9.length; omega, ?_⟩
  intro x hx
  set va := wireVal x gs a
  set vb := wireVal x gs b
  set vc := wireVal x gs cin
  have hp : x.length + gs.length = p := by omega
  have w0 : wireVal x g1 p = (va || vb) := by
    rw [← hp]; change wireVal x (gs ++ [⟨.or, [a, b]⟩]) (x.length + gs.length) = _
    rw [wireVal_snoc_self]; simp [GateOp.eval, va, vb]
  have w1 : wireVal x g2 (p + 1) = (va && vb) := by
    have hq : x.length + g1.length = p + 1 := by omega
    rw [← hq]; change wireVal x (g1 ++ [⟨.and, [a, b]⟩]) (x.length + g1.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends he1 (by omega), wireVal_extends he1 (by omega)]
  have w2 : wireVal x g3 (p + 2) = !(va && vb) := by
    have hq : x.length + g2.length = p + 2 := by omega
    rw [← hq]; change wireVal x (g2 ++ [⟨.not, [p + 1]⟩]) (x.length + g2.length) = _
    rw [wireVal_snoc_self]; simp [GateOp.eval, w1]
  have w3 : wireVal x g4 (p + 3) = ((va || vb) && !(va && vb)) := by
    have hq : x.length + g3.length = p + 3 := by omega
    rw [← hq]; change wireVal x (g3 ++ [⟨.and, [p, p + 2]⟩]) (x.length + g3.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends (Extends_trans he2 he3) (by omega), w0, w2]
  have w4 : wireVal x g5 (p + 4) = (((va || vb) && !(va && vb)) || vc) := by
    have hq : x.length + g4.length = p + 4 := by omega
    rw [← hq]; change wireVal x (g4 ++ [⟨.or, [p + 3, cin]⟩]) (x.length + g4.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [w3, wireVal_extends (Extends_trans he1 (Extends_trans he2 (Extends_trans he3 he4))) (by omega)]
  have w5 : wireVal x g6 (p + 5) = (((va || vb) && !(va && vb)) && vc) := by
    have hq : x.length + g5.length = p + 5 := by omega
    rw [← hq]; change wireVal x (g5 ++ [⟨.and, [p + 3, cin]⟩]) (x.length + g5.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends he5 (by omega), w3,
        wireVal_extends (Extends_trans he1 (Extends_trans he2 (Extends_trans he3 (Extends_trans he4 he5)))) (by omega)]
  have w6 : wireVal x g7 (p + 6) = !(((va || vb) && !(va && vb)) && vc) := by
    have hq : x.length + g6.length = p + 6 := by omega
    rw [← hq]; change wireVal x (g6 ++ [⟨.not, [p + 5]⟩]) (x.length + g6.length) = _
    rw [wireVal_snoc_self]; simp [GateOp.eval, w5]
  have w7 : wireVal x g8 (p + 7) =
      ((((va || vb) && !(va && vb)) || vc) && !(((va || vb) && !(va && vb)) && vc)) := by
    have hq : x.length + g7.length = p + 7 := by omega
    rw [← hq]; change wireVal x (g7 ++ [⟨.and, [p + 4, p + 6]⟩]) (x.length + g7.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_extends (Extends_trans he6 he7) (by omega), w4, w6]
  have w8 : wireVal x g9 (p + 8) = ((va && vb) || (((va || vb) && !(va && vb)) && vc)) := by
    have hq : x.length + g8.length = p + 8 := by omega
    rw [← hq]; change wireVal x (g8 ++ [⟨.or, [p + 1, p + 5]⟩]) (x.length + g8.length) = _
    rw [wireVal_snoc_self]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [wireVal_extends (Extends_trans he3 (Extends_trans he4 (Extends_trans he5 (Extends_trans he6 (Extends_trans he7 he8))))) (by omega),
        w1, wireVal_extends (Extends_trans he7 he8) (by omega), w5]
  have w7' : wireVal x g9 (p + 7) =
      ((((va || vb) && !(va && vb)) || vc) && !(((va || vb) && !(va && vb)) && vc)) := by
    rw [wireVal_extends he9 (by omega), w7]
  rw [w7', w8]
  exact fullAdder_bool va vb vc

def decodeNum (x : List Bool) (gs : List Gate) : List Nat → Nat
  | [] => 0
  | w :: ws => (wireVal x gs w).toNat + 2 * decodeNum x gs ws

theorem decodeNum_extends {x : List Bool} {gs1 gs2 : List Gate} {ws : List Nat}
    (hext : Extends gs1 gs2) (hws : ∀ w ∈ ws, w < x.length + gs1.length) :
    decodeNum x gs2 ws = decodeNum x gs1 ws := by
  induction ws with
  | nil => rfl
  | cons w tl ih =>
    simp only [decodeNum]
    rw [wireVal_extends hext (hws w (List.mem_cons_self ..)),
        ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))]

theorem decodeNum_testBit (x : List Bool) (gs : List Gate) (ws : List Nat) (b : Nat) :
    (decodeNum x gs ws).testBit b = if b < ws.length then wireVal x gs (ws.getD b 0) else false := by
  induction ws generalizing b with
  | nil => simp [decodeNum]
  | cons w tl ih =>
    simp only [decodeNum, List.length_cons]
    have hcomm : (wireVal x gs w).toNat + 2 * decodeNum x gs tl =
        2 * decodeNum x gs tl + (wireVal x gs w).toNat := by omega
    rw [hcomm, testBit_two_mul_add_bool]
    cases b with
    | zero => simp
    | succ b =>
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih b]
      have hiff : (b + 1 < tl.length + 1) ↔ (b < tl.length) := by omega
      simp [hiff]

def emitAddAux (inputs : Nat) (gs : List Gate) (cin : Nat) :
    List Nat → List Nat → List Gate × List Nat
  | [], _ => (gs, [])
  | _, [] => (gs, [])
  | a :: as, b :: bs =>
    let r1 := addFullAdder inputs gs a b cin
    let r2 := emitAddAux inputs r1.1 r1.2.2 as bs
    (r2.1, r1.2.1 :: r2.2)

theorem emitAddAux_spec {inputs : Nat} {gs : List Gate} {cin : Nat} {as bs : List Nat}
    (hg : GoodGates inputs gs) (hcin : cin < inputs + gs.length)
    (hlen : as.length = bs.length)
    (has : ∀ w ∈ as, w < inputs + gs.length) (hbs : ∀ w ∈ bs, w < inputs + gs.length) :
    let r := emitAddAux inputs gs cin as bs
    Extends gs r.1 ∧ r.1.length = gs.length + 9 * as.length ∧ GoodGates inputs r.1 ∧
    r.2.length = as.length ∧ (∀ w ∈ r.2, w < inputs + r.1.length) ∧
    ∀ x : List Bool, x.length = inputs →
      decodeNum x r.1 r.2 =
        (decodeNum x gs as + decodeNum x gs bs + (wireVal x gs cin).toNat) % 2 ^ as.length := by
  induction as generalizing gs cin bs with
  | nil =>
    cases bs with
    | nil =>
      refine ⟨Extends_refl gs, by simp [emitAddAux], hg, by simp [emitAddAux],
        fun _ h => by simp [emitAddAux] at h, fun x _ => by simp [emitAddAux, decodeNum, Nat.mod_one]⟩
    | cons _ _ => simp at hlen
  | cons a atl ih =>
    cases bs with
    | nil => simp at hlen
    | cons b btl =>
      simp only [List.length_cons] at hlen
      simp only [emitAddAux]
      have h1 := addFullAdder_spec hg (has a (List.mem_cons_self ..)) (hbs b (List.mem_cons_self ..)) hcin
      rcases h1 with ⟨he1, hl1, hg1, hws1, hwc1, hv1⟩
      have has1 : ∀ u ∈ atl, u < inputs + (addFullAdder inputs gs a b cin).1.length := fun u hu => by
        have := has u (List.mem_cons_of_mem _ hu); omega
      have hbs1 : ∀ u ∈ btl, u < inputs + (addFullAdder inputs gs a b cin).1.length := fun u hu => by
        have := hbs u (List.mem_cons_of_mem _ hu); omega
      have h2 := ih hg1 hwc1 (by omega) has1 hbs1
      rcases h2 with ⟨he2, hl2, hg2, hlen2, hws2, hv2⟩
      refine ⟨Extends_trans he1 he2, by simp; omega, hg2, by simp [hlen2], ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu2
        · have := Extends_len he2; omega
        · exact hws2 u hu2
      · intro x hx
        simp only [decodeNum, List.length_cons]
        rw [wireVal_extends he2 (by omega), hv2 x hx,
            decodeNum_extends he1 (fun u hu => by have := has u (List.mem_cons_of_mem _ hu); omega),
            decodeNum_extends he1 (fun u hu => by have := hbs u (List.mem_cons_of_mem _ hu); omega)]
        have hfa := hv1 x hx
        set sv := (wireVal x (addFullAdder inputs gs a b cin).1 (addFullAdder inputs gs a b cin).2.1).toNat
        set cv := (wireVal x (addFullAdder inputs gs a b cin).1 (addFullAdder inputs gs a b cin).2.2).toNat
        set da := decodeNum x gs atl
        set db := decodeNum x gs btl
        have hsv : sv < 2 := by
          dsimp only [sv]
          cases wireVal x (addFullAdder inputs gs a b cin).1 (addFullAdder inputs gs a b cin).2.1 <;> decide
        have htot : (wireVal x gs a).toNat + 2 * da + ((wireVal x gs b).toNat + 2 * db) +
            (wireVal x gs cin).toNat = sv + 2 * (da + db + cv) := by omega
        rw [htot, Nat.pow_succ', mul_comm 2 (2 ^ atl.length)]
        have hmod : (sv + 2 * (da + db + cv)) % (2 ^ atl.length * 2) =
            sv + 2 * ((da + db + cv) % 2 ^ atl.length) := by
          set q := (da + db + cv) / 2 ^ atl.length
          set rem := (da + db + cv) % 2 ^ atl.length
          have hdiv := Nat.div_add_mod (da + db + cv) (2 ^ atl.length)
          have hrem : rem < 2 ^ atl.length := Nat.mod_lt _ (Nat.two_pow_pos _)
          have heq : sv + 2 * (da + db + cv) = (sv + 2 * rem) + (2 ^ atl.length * 2) * q := by
            have : da + db + cv = 2 ^ atl.length * q + rem := hdiv.symm
            nlinarith
          rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        exact hmod.symm

def emitAdd (inputs : Nat) (gs : List Gate) (wFalse : Nat) (as bs : List Nat) :
    List Gate × List Nat :=
  emitAddAux inputs gs wFalse as bs

theorem emitAdd_spec {inputs : Nat} {gs : List Gate} {wFalse : Nat} {as bs : List Nat}
    (hg : GoodGates inputs gs) (hf : wFalse < inputs + gs.length)
    (hlen : as.length = bs.length)
    (has : ∀ w ∈ as, w < inputs + gs.length) (hbs : ∀ w ∈ bs, w < inputs + gs.length) :
    let r := emitAdd inputs gs wFalse as bs
    Extends gs r.1 ∧ r.1.length = gs.length + 9 * as.length ∧ GoodGates inputs r.1 ∧
    r.2.length = as.length ∧ (∀ w ∈ r.2, w < inputs + r.1.length) ∧
    ∀ x : List Bool, x.length = inputs → wireVal x gs wFalse = false →
      decodeNum x r.1 r.2 = (decodeNum x gs as + decodeNum x gs bs) % 2 ^ as.length := by
  unfold emitAdd
  have h := emitAddAux_spec hg hf hlen has hbs
  rcases h with ⟨he, hl, hgg, hrl, hws, hv⟩
  refine ⟨he, hl, hgg, hrl, hws, fun x hx hwf => by simpa [hwf] using hv x hx⟩
def Legal (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

def Exact (gs : List Gate) : Prop := ∀ g ∈ gs, Legal g

theorem fullAdder_exact (n : ℕ) (gs : List Gate) (a b c : ℕ) (ok : Exact gs) :
    Exact (addFullAdder n gs a b c).1 := by
  simp [Exact,Legal,addFullAdder,List.mem_append] at ok ⊢
  intro g hg
  rcases hg with hg | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok g hg
  all_goals simp

theorem add_exact (n : ℕ) (gs : List Gate) (c : ℕ) (as bs : List ℕ) (ok : Exact gs) :
    Exact (emitAddAux n gs c as bs).1 := by
  induction as generalizing bs gs c with
  | nil => exact ok
  | cons a as ih =>
    cases bs with
    | nil => exact ok
    | cons b bs => exact ih _ _ _ (fullAdder_exact n gs a b c ok)

end WordCircuit

namespace WordCircuit
open PEqualNP.CircuitLowerBounds

def pop (x : List Bool) (gs : List Gate) (ws : List ℕ) : ℕ :=
  (ws.map fun w => (wireVal x gs w).toNat).sum

def InRange (n : ℕ) (gs : List Gate) (ws : List ℕ) := ∀ w ∈ ws, w<n+gs.length

theorem pop_extends {n} {x : List Bool} {g h : List Gate} {ws : List ℕ}
    (ex : Extends g h) (good : InRange n g ws) (hx : x.length=n) :
    pop x h ws = pop x g ws := by
  unfold pop
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [wireVal_extends ex (by rw [hx]; exact good w hw)]

theorem column (n : ℕ) (gs : List Gate) (z : ℕ) (ws : List ℕ)
    (gg : GoodGates n gs) (ok : Exact gs) (hz : z<n+gs.length) (hw : InRange n gs ws) :
    ∃ (h : List Gate) (bit : ℕ) (carries : List ℕ),
      Extends gs h ∧ GoodGates n h ∧ Exact h ∧ bit<n+h.length ∧ InRange n h carries ∧
      h.length + 9*carries.length ≤ gs.length + 9*ws.length ∧
      ∀ x : List Bool, x.length=n → wireVal x gs z=false →
        pop x gs ws = (wireVal x h bit).toNat + 2*pop x h carries := by
  cases eqws : ws with
  | nil =>
    exact ⟨gs,z,[],Extends_refl _,gg,ok,hz,by simp [InRange],by simp,by
      intro x hx hfalse; simp [pop,hfalse]⟩
  | cons a tail =>
    have ha := hw a (by simp [eqws])
    cases eqtail : tail with
    | nil => exact ⟨gs,a,[],Extends_refl _,gg,ok,ha,by simp [InRange],by simp,
        by intro x _ _; simp [pop]⟩
    | cons b rest =>
      have hb := hw b (by simp [eqws,eqtail])
      cases eqrest : rest with
      | nil =>
        let r := addFullAdder n gs a b z
        obtain ⟨he,hl,hg,hs,hc,hv⟩ := addFullAdder_spec gg ha hb hz
        refine ⟨r.1,r.2.1,[r.2.2],he,hg,fullAdder_exact _ _ _ _ _ ok,hs,?_,?_,?_⟩
        · simpa [InRange] using hc
        · change (addFullAdder n gs a b z).1.length + 9*1 ≤ gs.length+9*2
          omega
        · intro x hx h0
          simpa [pop,h0,add_assoc] using hv x hx
      | cons c more =>
        have hc := hw c (by simp [eqws,eqtail,eqrest])
        let r := addFullAdder n gs a b c
        obtain ⟨he,hl,hg,hs,hcarry,hv⟩ := addFullAdder_spec gg ha hb hc
        have len : r.1.length=gs.length+9 := hl
        have original : InRange n gs more := fun w h => hw w (by simp [eqws,eqtail,eqrest,h])
        have next : InRange n r.1 (r.2.1::more) := by
          intro w hm
          rcases List.mem_cons.mp hm with rfl | h
          · exact hs
          · have := original w h; omega
        obtain ⟨h,bit,cs,ext,good,legal,hbit,hcs,cost,value⟩ :=
          column n r.1 z (r.2.1::more) hg (fullAdder_exact _ _ _ _ _ ok)
            (by omega) next
        have grows := Extends_len ext
        refine ⟨h,bit,r.2.2::cs,Extends_trans he ext,good,legal,hbit,?_,?_,?_⟩
        · intro w hm
          rcases List.mem_cons.mp hm with rfl | hmem
          · change r.2.2<n+r.1.length at hcarry
            omega
          · exact hcs _ hmem
        · simp only [List.length_cons] at cost ⊢
          omega
        · intro x hx h0
          have hz' : wireVal x r.1 z=false := by
            rw [wireVal_extends he (by omega)]; exact h0
          have hc' : wireVal x h r.2.2 = wireVal x r.1 r.2.2 :=
            wireVal_extends ext (by rw [hx]; exact hcarry)
          have restEq : pop x r.1 more = pop x gs more := pop_extends he original hx
          have val := value x hx hz'
          have sum := hv x hx
          change (wireVal x gs a).toNat + (wireVal x gs b).toNat + (wireVal x gs c).toNat =
            (wireVal x r.1 r.2.1).toNat + 2*(wireVal x r.1 r.2.2).toNat at sum
          have cons_pop (g : List Gate) (w : ℕ) (l : List ℕ) :
              pop x g (w::l) = (wireVal x g w).toNat + pop x g l := by simp [pop]
          simp only [cons_pop,hc'] at val ⊢
          rw [restEq] at val
          omega
termination_by ws.length
decreasing_by simp_all only [List.length_cons]; omega

end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds

def weighted (x : List Bool) (gs : List Gate) : List (List ℕ) → ℕ
  | [] => 0
  | c::r => pop x gs c + 2*weighted x gs r

theorem weighted_extends {n} {x : List Bool} {gs h : List Gate} {cols : List (List ℕ)}
    (ex : Extends gs h) (valid : ∀ c∈cols, InRange n gs c) (hx : x.length=n) :
    weighted x h cols = weighted x gs cols := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    rw [weighted,weighted,pop_extends ex (valid c (by simp)) hx,
      ih (fun d hd => valid d (by simp [hd]))]

theorem carry_mod (v q m : ℕ) (hv : v<2) (hm : 0<m) :
    (v+2*q)%(2*m) = v+2*(q%m) := by
  have ht : v+2*(q%m)<2*m := by have := Nat.mod_lt q hm; omega
  have e : v+2*q = (v+2*(q%m)) + (2*m)*(q/m) := by
    calc v+2*q = v+2*(m*(q/m)+q%m) := by rw [Nat.div_add_mod]
         _ = _ := by ring
  rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ht]

theorem sum_columns (n : ℕ) (cols : List (List ℕ)) (gs : List Gate) (z : ℕ) (cs : List ℕ)
    (gg : GoodGates n gs) (ok : Exact gs) (hz : z<n+gs.length) (hc : InRange n gs cs)
    (hw : ∀ c ∈ cols, InRange n gs c) :
    ∃ (h : List Gate) (out : List ℕ),
      Extends gs h ∧ GoodGates n h ∧ Exact h ∧ InRange n h out ∧ out.length=cols.length ∧
      h.length ≤ gs.length + 9*(cs.length+(cols.map List.length).sum) ∧
      ∀ x : List Bool, x.length=n → wireVal x gs z=false →
        decodeNum x h out = (pop x gs cs + weighted x gs cols) % 2^cols.length := by
  induction cols generalizing gs cs with
  | nil =>
    exact ⟨gs,[],Extends_refl _,gg,ok,by simp [InRange],rfl,by simp,
      by intro x hx h0; exact (Nat.mod_one _).symm⟩
  | cons c cols ih =>
    have hcur := hw c (by simp)
    have hrest (d) (hd : d ∈ cols) := hw d (by simp [hd])
    have both : InRange n gs (cs++c) := by
      intro w h; rcases List.mem_append.mp h with hx | hx
      · exact hc w hx
      · exact hcur w hx
    obtain ⟨g,l,carry,eg,gg',ok',hl,hcarry,cost,sem⟩ := column n gs z (cs++c) gg ok hz both
    have len := Extends_len eg
    obtain ⟨h,out,he,hg,ho,hout,hsize,hcost,hsem⟩ := ih g carry gg' ok' (by omega) hcarry
      (fun d hd w hm => by have := hrest d hd w hm; omega)
    have lh := Extends_len he
    refine ⟨h,l::out,Extends_trans eg he,hg,ho,?_,by simp [hsize],?_,?_⟩
    · intro w hmem; rcases List.mem_cons.mp hmem with rfl | hmem
      · omega
      · exact hout _ hmem
    · simp only [List.length_append] at cost
      simp only [List.map_cons,List.sum_cons]
      omega
    · intro x hx h0
      have h0' : wireVal x g z=false := by rw [wireVal_extends eg (by omega)]; exact h0
      have hv := sem x hx h0
      have va := hsem x hx h0'
      have hl' : wireVal x h l = wireVal x g l := wireVal_extends he (by omega)
      have hw' := weighted_extends eg hrest hx
      have pv : pop x gs (cs++c) = pop x gs cs + pop x gs c := by simp [pop]
      have identity : pop x gs cs + weighted x gs (c::cols) =
          (wireVal x g l).toNat + 2*(pop x g carry + weighted x g cols) := by
        rw [pv] at hv
        simp only [weighted]
        omega
      rw [identity, List.length_cons, pow_succ, Nat.mul_comm (2^cols.length) 2,
        carry_mod _ _ _ (by cases wireVal x g l <;> decide) (by positivity)]
      change (wireVal x h l).toNat + 2*decodeNum x h out = _
      rw [hl',va]

end WordCircuit

namespace WordCircuit
open PEqualNP.CircuitLowerBounds

def place (w : ℕ) : ℕ → List (List ℕ) → List (List ℕ)
  | _, [] => []
  | 0,c::cs => (w::c)::cs
  | i+1,c::cs => c::place w i cs

theorem place_length (w i : ℕ) (cs : List (List ℕ)) : (place w i cs).length=cs.length := by
  induction cs generalizing i with
  | nil => cases i <;> rfl
  | cons c cs ih => cases i <;> simp [place,ih]

theorem place_count (w i : ℕ) (cs : List (List ℕ)) :
    ((place w i cs).map List.length).sum ≤ (cs.map List.length).sum+1 := by
  induction cs generalizing i with
  | nil => cases i <;> simp [place]
  | cons c cs ih =>
    cases i with
    | zero => simp [place]; omega
    | succ i => have := ih i; simp [place]; omega

theorem place_range {n gs w} (hw : w<n+List.length gs) (i : ℕ) (cs : List (List ℕ))
    (hc : ∀ c ∈ cs, InRange n gs c) : ∀ c ∈ place w i cs, InRange n gs c := by
  induction cs generalizing i with
  | nil => cases i <;> simp [place]
  | cons a cs ih =>
    have tail (c : List ℕ) (h : c ∈ cs) : InRange n gs c := hc c (by simp [h])
    have head := hc a (by simp)
    cases i with
    | zero =>
      intro c hm
      rcases List.mem_cons.mp hm with rfl | h
      · intro q hq; rcases List.mem_cons.mp hq with rfl | hq
        · exact hw
        · exact head _ hq
      · exact tail _ h
    | succ i =>
      intro c hm; rcases List.mem_cons.mp hm with rfl | h
      · exact head
      · exact ih i tail c h

theorem place_value {x : List Bool} {g : List Gate} (w i : ℕ) (cs : List (List ℕ)) (hi : i<cs.length) :
    weighted x g (place w i cs) = (wireVal x g w).toNat*2^i + weighted x g cs := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp [place,weighted,pop,add_assoc]
    | succ i =>
      have h := ih i (by simpa using hi)
      simp only [place,weighted,h,pow_succ]
      ring

def scatter (k : ℕ) : List (ℕ × ℕ) → List (List ℕ)
  | [] => List.replicate k []
  | (i,w)::xs => place w i (scatter k xs)

def termVal (x : List Bool) (gs : List Gate) (ts : List (ℕ × ℕ)) :=
  (ts.map fun (i,w) => (wireVal x gs w).toNat * 2^i).sum

theorem scattered {n gs k} (ts : List (ℕ × ℕ))
    (good : ∀ p ∈ ts, p.1<k ∧ p.2<n+List.length gs) :
    (scatter k ts).length=k ∧ ((scatter k ts).map List.length).sum ≤ ts.length ∧
    (∀ c ∈ scatter k ts, InRange n gs c) ∧
    ∀ x, weighted x gs (scatter k ts) = termVal x gs ts := by
  induction ts with
  | nil =>
    refine ⟨by simp [scatter],?_,?_,?_⟩
    · simp [scatter]
    · intro c hc; have : c=[] := (List.eq_of_mem_replicate hc)
      simp [this,InRange]
    · intro x
      change weighted x gs (List.replicate k []) = 0
      induction k with
      | zero => rfl
      | succ j ih => simp [List.replicate_succ,weighted,pop,ih]
  | cons p ts ih =>
    obtain ⟨s,c,r,v⟩ := ih (fun u h => good u (by simp [h]))
    obtain ⟨hi,hw⟩ := good p (by simp)
    rcases p with ⟨i,w⟩
    refine ⟨(place_length _ _ _).trans s,?_,place_range hw i _ r,?_⟩
    · have := place_count w i (scatter k ts)
      change _ ≤ ts.length+1
      exact this.trans (by omega)
    · intro x
      change weighted x gs (place w i (scatter k ts)) = _
      rw [place_value _ _ _ (by rwa [s]),v]
      rfl
end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds

theorem termVal_extends {n : ℕ} {x : List Bool} {g h : List Gate} {ts : List (ℕ × ℕ)}
    (eg : Extends g h) (hx : x.length=n) (good : ∀ p ∈ ts, p.2<n+g.length) :
    termVal x h ts = termVal x g ts := by
  unfold termVal
  congr 1
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨i,w⟩
  dsimp
  rw [wireVal_extends eg (by rw [hx]; exact good _ hp)]

def monomialVal (x : List Bool) (gs : List Gate) (ps : List (ℕ × ℕ × ℕ)) : ℕ :=
  (ps.map fun (i,a,b) => ((wireVal x gs a && wireVal x gs b).toNat) * 2^i).sum

theorem build_products {n k : ℕ} (g : List Gate) (ps : List (ℕ × ℕ × ℕ))
    (hg : GoodGates n g) (exactG : Exact g)
    (bounds : ∀ p ∈ ps, p.1 < k ∧ p.2.1 < n+g.length ∧ p.2.2 < n+g.length) :
    ∃ (h : List Gate) (ts : List (ℕ × ℕ)), Extends g h ∧ GoodGates n h ∧ Exact h ∧
      h.length=g.length+ps.length ∧ ts.length=ps.length ∧
      (∀ p ∈ ts, p.1<k ∧ p.2<n+h.length) ∧
      ∀ x : List Bool, x.length=n → termVal x h ts = monomialVal x g ps := by
  induction ps with
  | nil => exact ⟨g,[],Extends_refl _,hg,exactG,by simp,rfl,by simp,by simp [termVal,monomialVal]⟩
  | cons p ps ih =>
    rcases p with ⟨i,a,b⟩
    obtain ⟨hi,ha,hb⟩ := bounds (i,a,b) (by simp)
    obtain ⟨g',ts,eg,good,exactG',len,cnt,valid,sem⟩ := ih (fun q h => bounds q (by simp [h]))
    have len' := Extends_len eg
    have wa : a < n+g'.length := lt_of_lt_of_le ha (Nat.add_le_add_left len' n)
    have wb : b < n+g'.length := lt_of_lt_of_le hb (Nat.add_le_add_left len' n)
    let r := addAnd n g' a b
    obtain ⟨ext,sz,gg,hw,hv⟩ := addAnd_spec good wa wb
    have legal : Exact r.1 := by
      intro gate mem
      rcases List.mem_append.mp mem with old | new
      · exact exactG' _ old
      · simp only [List.mem_singleton] at new
        subst gate
        simp [Legal]
    refine ⟨r.1,(i,r.2)::ts,Extends_trans eg ext,gg,legal,?_,by simp [cnt],?_,?_⟩
    · change (addAnd n g' a b).1.length = _
      rw [sz,len,List.length_cons]; omega
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hi,hw⟩
      · have h := valid _ hq
        exact ⟨h.1, lt_of_lt_of_le h.2 (Nat.add_le_add_left (Extends_len ext) n)⟩
    · intro x hx
      have tail := termVal_extends ext hx (fun q hq => (valid q hq).2)
      change (wireVal x r.1 r.2).toNat * 2^i + termVal x r.1 ts =
        (wireVal x g a && wireVal x g b).toNat * 2^i + monomialVal x g ps
      rw [tail,sem x hx]
      change (wireVal x (addAnd n g' a b).1 (addAnd n g' a b).2).toNat*_ + _ = _
      rw [hv x hx,wireVal_extends eg (by simpa [hx] using ha),
          wireVal_extends eg (by simpa [hx] using hb)]

end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds

theorem sum_monomials {n k : ℕ} (g : List Gate) (ps : List (ℕ × ℕ × ℕ)) (zeroWire : ℕ)
    (hg : GoodGates n g) (exactG : Exact g) (hz : zeroWire<n+g.length)
    (bounds : ∀ p ∈ ps, p.1 < k ∧ p.2.1 < n+g.length ∧ p.2.2 < n+g.length) :
    ∃ (h : List Gate) (out : List ℕ),
      Extends g h ∧ GoodGates n h ∧ Exact h ∧ InRange n h out ∧ out.length=k ∧
      h.length ≤ g.length+10*ps.length ∧
      ∀ x : List Bool, x.length=n → wireVal x g zeroWire=false →
        decodeNum x h out = monomialVal x g ps % 2^k := by
  obtain ⟨g₁,ws,e₁,good₁,legal₁,sz₁,nws,valid,sem₁⟩ := build_products g ps hg exactG bounds
  obtain ⟨ncols,count,range,sem⟩ := scattered ws valid
  have wz : zeroWire<n+g₁.length := lt_of_lt_of_le hz (Nat.add_le_add_left (Extends_len e₁) n)
  obtain ⟨h,out,e₂,good₂,legal₂,bound,outLen,sz₂,sem₂⟩ :=
    sum_columns n (scatter k ws) g₁ zeroWire [] good₁ legal₁ wz (by simp [InRange]) range
  refine ⟨h,out,Extends_trans e₁ e₂,good₂,legal₂,bound,outLen.trans ncols,?_,?_⟩
  · simp only [List.length_nil,zero_add] at sz₂
    omega
  · intro x hx hfalse
    have hz₁ := (wireVal_extends e₁ (by rw [hx]; exact hz)).trans hfalse
    simpa only [pop,List.map_nil,List.sum_nil,zero_add,sem x,sem₁ x hx,ncols] using sem₂ x hx hz₁

end WordCircuit

namespace WordCircuit
open Finset

theorem packed_polynomial (t b : ℕ) (v : Fin t → Fin b → Bool) :
    let digit := fun i => ∑ j : Fin b, (v i j).toNat * 2^j.val
    (∑ i : Fin t, digit i * 2^((b+1)*i.val)) +
      2^(t*(b+1)) * (∑ i : Fin t, (digit i)^2) =
    (∑ i : Fin t, ∑ j : Fin b, (v i j).toNat * 2^((b+1)*i.val+j.val)) +
    ∑ i : Fin t, ∑ j : Fin b, ∑ l : Fin b,
      (v i j && v i l).toNat * 2^(t*(b+1)+j.val+l.val) := by
  dsimp only
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    have hand (a b : Bool) : (a && b).toNat = a.toNat*b.toNat := by cases a <;> cases b <;> rfl
    rw [hand, pow_add, pow_add]; ring

end WordCircuit

namespace WordCircuit
open PEqualNP.CircuitLowerBounds Finset

def blocks {α : Type*} {d : ℕ} (f : Fin d → List α) : List α := (List.ofFn f).flatten

theorem blocks_len {α : Type*} {d : ℕ} (f : Fin d → List α) :
    (blocks f).length = ∑ j, (f j).length := by
  simp [blocks,List.length_flatten,List.map_ofFn,List.sum_ofFn]

theorem mem_blocks {α : Type*} {d : ℕ} {f : Fin d → List α} {v : α} :
    v ∈ blocks f ↔ ∃ j, v ∈ f j := by
  simp [blocks,List.mem_flatten,List.mem_ofFn]

theorem monomial_append (x : List Bool) (gs : List Gate) (a b : List (ℕ × ℕ × ℕ)) :
    monomialVal x gs (a++b) = monomialVal x gs a + monomialVal x gs b := by
  simp [monomialVal]

theorem monomial_blocks (x : List Bool) (gs : List Gate) {d : ℕ} (f : Fin d → List (ℕ × ℕ × ℕ)) :
    monomialVal x gs (blocks f) = ∑ j, monomialVal x gs (f j) := by
  unfold blocks
  have fold (ss : List (List (ℕ × ℕ × ℕ))) :
      monomialVal x gs ss.flatten = (ss.map (monomialVal x gs)).sum := by
    induction ss with
    | nil => rfl
    | cons l ls ih => simp [monomial_append,ih]
  rw [fold, List.map_ofFn, List.sum_ofFn]
  rfl

def src (b k : ℕ) {t : ℕ} (i : Fin t) (j : Fin b) := k+i.val*b+j.val

def linearCells (t b k : ℕ) := blocks fun i : Fin t => blocks fun j : Fin b =>
  [((b+1)*i.val+j.val, src b k i j, src b k i j)]

def squareCells (t b k : ℕ) := blocks fun i : Fin t => blocks fun j : Fin b =>
  blocks fun l : Fin b => [(t*(b+1)+j.val+l.val, src b k i j, src b k i l)]

def cells (t b k : ℕ) := linearCells t b k ++ squareCells t b k

theorem cells_length (t b k : ℕ) : (cells t b k).length = t*b+t*b*b := by
  simp [cells,linearCells,squareCells,blocks_len]
  ring

theorem src_bound {t b : ℕ} (k : ℕ) (i : Fin t) (j : Fin b) :
    src b k i j < k+t*b := by
  have h := Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt)
  simp only [src, Nat.succ_mul] at *
  omega

theorem cells_bound {t b k : ℕ} (hk : t*(b+1)+2*b+Nat.clog 2 t+1 ≤ k) :
    ∀ p ∈ cells t b k, p.1<k ∧ p.2.1<k+t*b ∧ p.2.2<k+t*b := by
  intro p hp
  rcases List.mem_append.mp hp with lin | quad
  · rcases mem_blocks.mp lin with ⟨i,ih⟩
    rcases mem_blocks.mp ih with ⟨j,jh⟩
    simp only [List.mem_singleton] at jh
    subst p
    refine ⟨?_,src_bound k i j,src_bound k i j⟩
    have h := Nat.mul_le_mul_left (b+1) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ, Nat.mul_comm (b+1) t] at h
    change (b+1)*i.val+j.val<k
    omega
  · rcases mem_blocks.mp quad with ⟨i,ih⟩
    rcases mem_blocks.mp ih with ⟨j,jh⟩
    rcases mem_blocks.mp jh with ⟨l,lh⟩
    simp only [List.mem_singleton] at lh
    subst p
    exact ⟨by dsimp; omega, src_bound k i j, src_bound k i l⟩

theorem cells_value (x : List Bool) (gs : List Gate) (t b k : ℕ) :
    let bits := fun i : Fin t => fun j : Fin b => wireVal x gs (src b k i j)
    let digit := fun i : Fin t => ∑ j : Fin b, (bits i j).toNat * 2^j.val
    monomialVal x gs (cells t b k) =
      (∑ i : Fin t, digit i * 2^((b+1)*i.val)) + 2^(t*(b+1)) * ∑ i : Fin t, (digit i)^2 := by
  intro bits digit
  rw [packed_polynomial t b bits]
  simp only [cells,linearCells,squareCells,monomial_append,monomial_blocks]
  simp [monomialVal,bits]
end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds Finset

theorem zero_seed {n : ℕ} (hn : 0<n) :
    ∃ (g : List Gate) (z : ℕ), GoodGates n g ∧ Exact g ∧ g.length=2 ∧
      z<n+g.length ∧ ∀ x : List Bool, x.length=n → wireVal x g z=false := by
  have empty : GoodGates n [] := by simp [GoodGates]
  let neg := addNot n [] 0
  obtain ⟨e,l,gneg,bneg,vneg⟩ := addNot_spec (gs:=[]) (a:=0) empty (by simpa using hn)
  let both := addAnd n neg.1 0 neg.2
  have left : 0<n+neg.1.length := by omega
  obtain ⟨eb,sz,hg,hz,sem⟩ := addAnd_spec gneg left bneg
  refine ⟨both.1,both.2,hg,?_,?_,hz,?_⟩
  · simp [both,neg,addNot,addAnd,Exact,Legal]
  · rfl
  · intro x hx
    change wireVal x (addAnd n neg.1 0 neg.2).1 (addAnd n neg.1 0 neg.2).2=false
    rw [sem x hx,wireVal_extends e (by simp [hx,hn]),vneg x hx]
    simp

theorem input_wire {x : List Bool} (g : List Gate) {i : ℕ} (hi : i<x.length) :
    wireVal x g i = x.getD i false := by
  have ext : Extends [] g := ⟨g,by simp⟩
  exact wireVal_extends ext (by simpa using hi)

def packedLift (t b k : ℕ) (x : List Bool) :=
  let digit := fun i : Fin t => ∑ j : Fin b, (x.getD (src b k i j) false).toNat*2^j.val
  (∑ i : Fin t, digit i*2^((b+1)*i.val)) + 2^(t*(b+1))*∑ i : Fin t, (digit i)^2

theorem lift_circuit {t b k : ℕ} (hk : t*(b+1)+2*b+Nat.clog 2 t+1 ≤ k) :
    ∃ (gs : List Gate) (z : ℕ) (out : List ℕ),
      GoodGates (k+t*b) gs ∧ Exact gs ∧ InRange (k+t*b) gs out ∧ out.length=k ∧
      gs.length ≤ 2+10*(t*b+t*b*b) ∧ z<k+t*b+gs.length ∧
      ∀ x : List Bool, x.length=k+t*b → wireVal x gs z=false ∧
        decodeNum x gs out=packedLift t b k x % 2^k := by
  obtain ⟨g,z,gg,legal,sz,hz,zero⟩ := zero_seed (n:=k+t*b) (by omega)
  have range (p) (hp : p ∈ cells t b k) := cells_bound hk p hp
  obtain ⟨gs,out,ext,good,exactG,outRange,len,cost,sem⟩ :=
    sum_monomials g (cells t b k) z gg legal hz
      (fun p hp => ⟨(range p hp).1,by have := (range p hp).2.1; omega,
                        by have := (range p hp).2.2; omega⟩)
  refine ⟨gs,z,out,good,exactG,outRange,len,?_,?_,?_⟩
  · simpa only [sz,cells_length] using cost
  · exact lt_of_lt_of_le hz (Nat.add_le_add_left (Extends_len ext) _)
  · intro x hx
    refine ⟨(wireVal_extends ext (by rwa [hx])).trans (zero x hx),?_⟩
    rw [sem x hx (zero x hx),cells_value]
    have inp (i : Fin t) (j : Fin b) := input_wire (x:=x) g (i:=src b k i j) (by rw [hx]; exact src_bound k i j)
    simp only [inp,packedLift]
end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds

theorem encoder_banks {t b k : ℕ} (hb : 0<b) (hk : t*(b+1)+2*b+Nat.clog 2 t+1 ≤ k) :
    ∃ (h : List Gate) (one two : List ℕ),
      GoodGates (k+t*b) h ∧ Exact h ∧ h.length ≤ 1024*(k+t*b*b+1) ∧
      one.length=k ∧ two.length=k ∧ InRange (k+t*b) h one ∧ InRange (k+t*b) h two ∧
      ∀ x : List Bool, x.length=k+t*b →
        let a := decodeNum x [] (List.range k)
        let d := packedLift t b k x
        decodeNum x h one=(a+d)%2^k ∧ decodeNum x h two=(a+2*d)%2^k := by
  let n := k+t*b
  obtain ⟨g,z,d,good,legal,valid,dsz,cost,hz,sem⟩ := lift_circuit hk
  let base := List.range k
  have blen : base.length=k := List.length_range
  have base_valid : InRange n g base := by
    intro w hw; have hw' := List.mem_range.mp hw
    dsimp [n]; omega
  let u := emitAdd n g z base d
  obtain ⟨eu,su,gu,lu,ru,vu⟩ := emitAdd_spec (as:=base) (bs:=d) good hz (blen.trans dsz.symm) base_valid valid
  have ou : Exact u.1 := add_exact n g z base d legal
  have zu : z<n+u.1.length := lt_of_lt_of_le hz (Nat.add_le_add_left (Extends_len eu) n)
  have du : InRange n u.1 d := fun w hw =>
    lt_of_lt_of_le (valid w hw) (Nat.add_le_add_left (Extends_len eu) n)
  let v := emitAdd n u.1 z u.2 d
  obtain ⟨ev,sv,gv,lv,rv,vv⟩ := emitAdd_spec (as:=u.2) (bs:=d) gu zu (lu.trans (blen.trans dsz.symm)) ru du
  refine ⟨v.1,u.2,v.2,gv,add_exact n u.1 z u.2 d ou,?_,lu.trans blen,lv.trans (lu.trans blen),?_,rv,?_⟩
  · have ub : u.1.length=g.length+9*k := su.trans (by rw [blen])
    have vb : v.1.length=u.1.length+9*k := sv.trans (by rw [lu,blen])
    have tb : t*b ≤ t*b*b := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (t*b) (Nat.succ_le_of_lt hb)
    omega
  · intro w hw
    exact lt_of_lt_of_le (ru w hw) (Nat.add_le_add_left (Extends_len ev) n)
  · intro x hx
    obtain ⟨zero,payload⟩ := sem x hx
    have ex0 : Extends [] g := ⟨g,by simp⟩
    have aeq : decodeNum x g base = decodeNum x [] base := by
      apply decodeNum_extends ex0
      intro w hw; have := List.mem_range.mp hw; simp [hx]; omega
    have eone : decodeNum x u.1 u.2 = (decodeNum x [] base + packedLift t b k x)%2^k := by
      rw [vu x hx zero, aeq,payload,blen,Nat.add_mod_mod]
    have szero : wireVal x u.1 z=false := (wireVal_extends eu (by rwa [hx])).trans zero
    have sameD : decodeNum x u.1 d = decodeNum x g d :=
      decodeNum_extends eu (fun w hw => by rw [hx]; exact valid w hw)
    have sameU : decodeNum x v.1 u.2=decodeNum x u.1 u.2 :=
      decodeNum_extends ev (fun w hw => by rw [hx]; exact ru w hw)
    refine ⟨sameU.trans eone,?_⟩
    change decodeNum x v.1 v.2 = (decodeNum x [] base + 2*packedLift t b k x)%2^k
    rw [vv x hx szero,eone,sameD,payload,lu,blen,Nat.mod_add_mod,Nat.add_mod_mod]
    congr 1; omega
end WordCircuit

namespace WordCircuit
open PEqualNP.CircuitLowerBounds Finset

theorem exp_ofFn (x : List Bool) (gs : List Gate) {k : ℕ} (w : Fin k → ℕ) :
    decodeNum x gs (List.ofFn w) = ∑ j : Fin k, (wireVal x gs (w j)).toNat * 2^j.val := by
  induction k with
  | zero => simp [decodeNum]
  | succ k ih =>
    rw [List.ofFn_succ,decodeNum,Fin.sum_univ_succ,ih,Finset.mul_sum]
    simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring

theorem decode_start (x : List Bool) (k : ℕ) :
    decodeNum x [] (List.range k) = ∑ j : Fin k, if x.getD j.val false then 2^j.val else 0 := by
  have listEq : List.ofFn (fun j : Fin k => j.val) = List.range k := by
    apply List.ext_getElem <;> simp
  rw [←listEq,exp_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  change (x.getD j.val false).toNat * 2^j.val = _
  cases x.getD j.val false <;> simp

theorem bank_bit {n k : ℕ} {g : List Gate} {bank : List ℕ}
    (len : bank.length=k) (bounds : InRange n g bank) :
    ∃ output : Fin k → Fin (n+g.length), ∀ (x : List Bool) (j : Fin k),
      wireVal x g (output j).val = (decodeNum x g bank).testBit j.val := by
  let h (j : Fin k) : j.val<bank.length := len ▸ j.isLt
  let out (j : Fin k) : Fin (n+g.length) := ⟨bank[j.val]'(h j),bounds _ (List.getElem_mem _)⟩
  refine ⟨out,fun x j => ?_⟩
  rw [decodeNum_testBit,if_pos (h j)]
  simp [out,List.getD_eq_getElem?_getD,h j]

theorem toNat_weight (v : Bool) (a : ℕ) : v.toNat*a = if v then a else 0 := by cases v <;> simp

theorem official_encoder : (∀ (t b : ℕ), 0 < t → 0 < b →
  let m := t*b
  let X := Fin m → Bool
  let low := t*(b+1)
  let h := low + 2*b + Nat.clog 2 t + 1
  let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
    if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
  let lift := fun payload : X =>
    (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
  ∀ k : ℕ, h ≤ k →
    let n := k+m
    let Word := Fin n → Bool
    let start := fun word : Word => ∑ j : Fin k, if (List.ofFn word).getD j.val false then 2^j.val else 0
    let tailWord := fun (word : Word) (j : Fin m) => (List.ofFn word).getD (k+j.val) false
    let code := fun (word : Word) (e : Fin 3) (bit : Fin k) =>
      (start word + e.val * lift (tailWord word)).testBit bit.val
    let valid := fun (len : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack len C ∧
      ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)
    (∃ (enc : PEqualNP.CircuitLowerBounds.Circuit) (send : Fin 3 → Fin k → Fin (n+enc.size)),
      valid n enc ∧ enc.size ≤ 1024*(k+t*b*b+1) ∧
      ∀ (u : Word) (edge : Fin 3) (j : Fin k),
        (enc.wires (List.ofFn u)).getD (send edge j).val false = code u edge j)) := by
  intro t b ht hb m X low h dig lifted k hk n Word st tail code valid
  obtain ⟨g,one,two,good,legal,cost,len1,len2,range1,range2,sem⟩ :=
    encoder_banks (t:=t) (k:=k) hb hk
  let C : Circuit := ⟨g,0⟩
  have r0 : InRange n g (List.range k) := by
    intro w hw; have := List.mem_range.mp hw
    dsimp [n,m]; omega
  obtain ⟨s0,h0⟩ := bank_bit (n:=n) (k:=k) List.length_range r0
  obtain ⟨s1,h1⟩ := bank_bit len1 range1
  obtain ⟨s2,h2⟩ := bank_bit len2 range2
  let send (e : Fin 3) (j : Fin k) : Fin (n+C.size) :=
    if e.val=0 then s0 j else if e.val=1 then s1 j else s2 j
  refine ⟨C,send,⟨good.2,legal⟩,cost,?_⟩
  intro u e j
  let x := List.ofFn u
  have hx : x.length=n := List.length_ofFn
  have result := sem x hx
  have sameStart : decodeNum x [] (List.range k) = st u := decode_start _ _
  have ext : Extends [] g := ⟨g,by simp⟩
  have sameZero : decodeNum x g (List.range k) = st u := by
    rw [← sameStart]
    apply decodeNum_extends ext
    intro w hw; have := List.mem_range.mp hw
    simp only [List.length_nil,Nat.add_zero,hx]; dsimp [n,m]; omega
  have payload : packedLift t b k x = lifted (tail u) := by
    have digit_eq (i : Fin t) :
        (∑ j : Fin b, (x.getD (src b k i j) false).toNat*2^j.val) = dig (tail u) i := by
      apply Finset.sum_congr rfl
      intro j _
      have bound := src_bound 0 i j
      have pos : i.val*b+j.val<m := by simpa [src,m] using bound
      simp [tail,List.getD_eq_getElem?_getD,pos,src,x,toNat_weight,Nat.add_assoc]
    change (∑ i : Fin t, _ * 2^((b+1)*i.val)) + 2^(t*(b+1)) * ∑ i : Fin t, _^2 = _
    simp only [digit_eq]
    rfl
  change wireVal x g (send e j).val = (st u+e.val*lifted (tail u)).testBit j.val
  obtain ⟨first,second⟩ := result
  fin_cases e
  · change wireVal x g (s0 j).val = _
    rw [h0,sameZero]; simp
  · change wireVal x g (s1 j).val = _
    rw [h1,first,sameStart,payload]
    simp [Nat.testBit_mod_two_pow,j.isLt]
  · change wireVal x g (s2 j).val = _
    rw [h2,second,sameStart,payload]
    simp [Nat.testBit_mod_two_pow,j.isLt]
end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds

theorem negate_word {n : ℕ} (g : List Gate) (ws : List ℕ)
    (good : GoodGates n g) (legal : Exact g) (valid : InRange n g ws) :
    ∃ (h : List Gate) (out : List ℕ), Extends g h ∧ GoodGates n h ∧ Exact h ∧
      InRange n h out ∧ out.length=ws.length ∧ h.length=g.length+ws.length ∧
      ∀ x : List Bool, x.length=n →
        decodeNum x h out + decodeNum x g ws + 1 = 2^ws.length := by
  induction ws with
  | nil => exact ⟨g,[],Extends_refl _,good,legal,by simp [InRange],rfl,by simp,by simp [decodeNum]⟩
  | cons a ws ih =>
    obtain ⟨g',us,eg,gg,ok,ru,len,cost,sem⟩ := ih (fun w hw => valid w (by simp [hw]))
    have ba := valid a (by simp)
    have ha : a<n+g'.length := lt_of_lt_of_le ba (Nat.add_le_add_left (Extends_len eg) n)
    let r := addNot n g' a
    obtain ⟨er,sz,gr,bw,hv⟩ := addNot_spec gg ha
    have legalR : Exact r.1 := by
      intro gate mem
      rcases List.mem_append.mp mem with old | new
      · exact ok _ old
      · simp only [List.mem_singleton] at new; subst gate; simp [Legal]
    refine ⟨r.1,r.2::us,Extends_trans eg er,gr,legalR,?_,by simp [len],?_,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact bw
      · exact lt_of_lt_of_le (ru w hw) (Nat.add_le_add_left (Extends_len er) n)
    · change (addNot n g' a).1.length = _
      rw [sz,cost,List.length_cons]; omega
    · intro x hx
      have same := decodeNum_extends (x:=x) er (ws:=us) (fun w hw => by rw [hx]; exact ru w hw)
      have prev := wireVal_extends (x:=x) (idx:=a) eg (by rwa [hx])
      simp only [decodeNum,List.length_cons,pow_succ]
      change (wireVal x (addNot n g' a).1 (addNot n g' a).2).toNat + _ + _ + 1 = _
      rw [hv x hx,prev,same]
      have := sem x hx
      cases wireVal x g a <;> simp <;> omega

theorem minus_word {n k : ℕ} (g : List Gate) (one : ℕ) (a b : List ℕ)
    (good : GoodGates n g) (legal : Exact g) (w1 : one<n+g.length)
    (ra : InRange n g a) (rb : InRange n g b) (la : a.length=k) (lb : b.length=k) :
    ∃ (h : List Gate) (out : List ℕ), Extends g h ∧ GoodGates n h ∧ Exact h ∧
      InRange n h out ∧ out.length=k ∧ h.length=g.length+10*k ∧
      ∀ x : List Bool, x.length=n → wireVal x g one=true →
        decodeNum x h out=(decodeNum x g a + 2^k - decodeNum x g b)%2^k := by
  obtain ⟨u,v,eu,gu,ok,rv,lv,cost,sem⟩ := negate_word g b good legal rb
  have w1u := lt_of_lt_of_le w1 (Nat.add_le_add_left (Extends_len eu) n)
  have rau : InRange n u a := fun w hw => lt_of_lt_of_le (ra w hw) (Nat.add_le_add_left (Extends_len eu) n)
  obtain ⟨eh,sz,gh,oh,rh,val⟩ := emitAddAux_spec (gs:=u) (as:=a) (bs:=v) gu w1u
    (la.trans (lv.trans lb).symm) rau rv
  let r := emitAddAux n u one a v
  refine ⟨r.1,r.2,Extends_trans eu eh,gh,add_exact n u one a v ok,rh,oh.trans la,?_,?_⟩
  · change (emitAddAux n u one a v).1.length = _
    rw [sz,cost,lb,la]; omega
  · intro x hx on
    have sameA := decodeNum_extends eu (ws:=a) (x:=x) (fun w hw => by rw [hx]; exact ra w hw)
    have sameOne : wireVal x u one = true := (wireVal_extends eu (by rwa [hx])).trans on
    have comp := sem x hx
    rw [lb] at comp
    change decodeNum x (emitAddAux n u one a v).1 (emitAddAux n u one a v).2 = _
    rw [val x hx,sameA,sameOne,la]
    congr 1; simp; omega
end WordCircuit

namespace ChannelRecovery
def diff (M a b : ℕ) := (a+M-b)%M

theorem diff_exact {M a b d : ℕ} (hb : b<M) (hd : d<M) (corr : a ≡ b+d [MOD M]) :
    diff M a b = d := by
  have same : a+M-b+b = a+M := Nat.sub_add_cancel (by omega)
  have added : a+M-b+b ≡ d+b [MOD M] := by
    rw [same,Nat.add_modulus_modEq_iff,Nat.add_comm d b]
    exact corr
  have cancel := Nat.ModEq.add_right_cancel' b added
  apply ((Nat.mod_modEq _ _).trans cancel).eq_of_lt_of_lt (Nat.mod_lt _ (by omega)) hd

theorem recover_three {M a d : ℕ} (ha : a<M) (hd : 2*d<M) :
    let c1 := (a+d)%M
    let c2 := (a+2*d)%M
    diff M c1 a = d ∧ diff M c2 c1 = d ∧ diff M c1 d = a ∧
      diff M c2 a = 2*d := by
  intro c1 c2
  have h1 : c1 ≡ a+d [MOD M] := Nat.mod_modEq _ _
  have h2 : c2 ≡ a+2*d [MOD M] := Nat.mod_modEq _ _
  have one : c1<M := Nat.mod_lt _ (by omega)
  have dc : d<M := by omega
  refine ⟨diff_exact ha dc h1,diff_exact one dc ?_,diff_exact dc ha ?_,diff_exact ha hd h2⟩
  · apply h2.trans
    calc a+2*d = (a+d)+d := by omega
         _ ≡ c1+d [MOD M] := h1.symm.add_right d
  · simpa [Nat.add_comm] using h1

end ChannelRecovery

namespace WordCircuit
open PEqualNP.CircuitLowerBounds

theorem decode_stable {n : ℕ} {a b : List Gate} {ws : List ℕ} {x : List Bool}
    (e : Extends a b) (v : InRange n a ws) (hx : x.length=n) :
    decodeNum x b ws = decodeNum x a ws := decodeNum_extends e (fun w hw => by rw [hx]; exact v w hw)

theorem stable_range {n : ℕ} {a b : List Gate} {ws : List ℕ}
    (e : Extends a b) (v : InRange n a ws) : InRange n b ws := fun w h =>
  lt_of_lt_of_le (v _ h) (Nat.add_le_add_left (Extends_len e) _)

theorem seed_one {n : ℕ} (hn : 0<n) :
    ∃ (g : List Gate) (w : ℕ), GoodGates n g ∧ Exact g ∧ g.length=3 ∧
      w<n+g.length ∧ ∀ x : List Bool, x.length=n → wireVal x g w=true := by
  obtain ⟨gs,z,good,legal,sz,bnd,sem⟩ := zero_seed hn
  obtain ⟨_,c,h,v,s⟩ := addNot_spec good bnd
  refine ⟨(addNot n gs z).1,(addNot n gs z).2,h,?_,by omega,v,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with old | new
    · exact legal _ old
    · simp only [List.mem_singleton] at new; subst g; simp [Legal]
  · intro x hx; rw [s x hx,sem x hx]; rfl

def rawBank (k offset : ℕ) := List.ofFn (fun j : Fin k => offset+j.val)

theorem raw_valid (k off : ℕ) (g : List Gate) (h : off≤k) : InRange (2*k) g (rawBank k off) := by
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  omega

theorem difference_banks (k : ℕ) (hk : 0<k) :
    ∃ (g : List Gate) (u v w : List ℕ),
      GoodGates (2*k) g ∧ Exact g ∧ g.length=3+30*k ∧
      InRange (2*k) g u ∧ InRange (2*k) g v ∧ InRange (2*k) g w ∧
      u.length=k ∧ v.length=k ∧ w.length=k ∧
      ∀ x : List Bool, x.length=2*k →
        let a := decodeNum x [] (rawBank k 0)
        let b := decodeNum x [] (rawBank k k)
        let d := ChannelRecovery.diff (2^k) b a
        decodeNum x g u=d ∧ decodeNum x g v=ChannelRecovery.diff (2^k) a d ∧
          decodeNum x g w=ChannelRecovery.diff (2^k) a b := by
  let n := 2*k
  let A := rawBank k 0
  let B := rawBank k k
  have la : A.length=k := List.length_ofFn
  have lb : B.length=k := List.length_ofFn
  obtain ⟨g0,one,gg,og,sz,zv,zone⟩ := seed_one (n:=n) (by dsimp [n]; omega)
  have ea : Extends [] g0 := ⟨g0,by simp⟩
  have ra := raw_valid k 0 g0 (Nat.zero_le _)
  have rb := raw_valid k k g0 le_rfl
  obtain ⟨g1,u,e1,gg1,ok1,ru,lu,s1,f1⟩ := minus_word g0 one B A gg og zv rb ra lb la
  have zv1 := lt_of_lt_of_le zv (Nat.add_le_add_left (Extends_len e1) n)
  obtain ⟨g2,v,e2,gg2,ok2,rv,lv,s2,f2⟩ := minus_word g1 one A u gg1 ok1 zv1 (stable_range e1 ra) ru la lu
  have e12 := Extends_trans e1 e2
  have zv2 := lt_of_lt_of_le zv (Nat.add_le_add_left (Extends_len e12) n)
  obtain ⟨g3,w,e3,gg3,ok3,rw',lw,s3,f3⟩ := minus_word g2 one A B gg2 ok2 zv2 (stable_range e12 ra) (stable_range e12 rb) la lb
  have e23 := Extends_trans e2 e3
  refine ⟨g3,u,v,w,gg3,ok3,by omega,stable_range e23 ru,stable_range e3 rv,rw',lu,lv,lw,?_⟩
  intro x hx
  have origA : decodeNum x g0 A = decodeNum x [] A := decode_stable ea (raw_valid k 0 [] (by omega)) hx
  have origB : decodeNum x g0 B = decodeNum x [] B := decode_stable ea (raw_valid k k [] le_rfl) hx
  have true0 := zone x hx
  have true1 : wireVal x g1 one=true := (wireVal_extends e1 (by rw [hx];exact zv)).trans true0
  have true2 : wireVal x g2 one=true := (wireVal_extends e12 (by rw [hx];exact zv)).trans true0
  have h1 := f1 x hx true0
  have h2 := f2 x hx true1
  have h3 := f3 x hx true2
  rw [origA,origB] at h1
  rw [decode_stable e1 ra hx,origA,h1] at h2
  rw [decode_stable e12 ra hx,decode_stable e12 rb hx,origA,origB] at h3
  exact ⟨(decode_stable e23 ru hx).trans h1,(decode_stable e3 rv hx).trans h2,h3⟩

end WordCircuit

namespace WordCircuit
open PEqualNP.CircuitLowerBounds

def bitsOf (k a : ℕ) := List.ofFn fun j : Fin k => a.testBit j.val

theorem incoming (k a b : ℕ) :
    let input := bitsOf k a ++ bitsOf k b
    decodeNum input [] (rawBank k 0) = a%2^k ∧ decodeNum input [] (rawBank k k) = b%2^k := by
  intro inp
  constructor
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [decodeNum_testBit,Nat.testBit_mod_two_pow]
    by_cases hj : j<k
    · have hlt : j<(bitsOf k a).length := by simpa [bitsOf] using hj
      simp [rawBank,hj,wireVal,evalW,inp,List.getD_eq_getElem?_getD,List.getElem?_append,bitsOf]
    · simp [rawBank,hj]
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [decodeNum_testBit,Nat.testBit_mod_two_pow]
    by_cases hj : j<k
    · have hle : (bitsOf k a).length≤k+j := by simp [bitsOf]
      simp [rawBank,hj,wireVal,evalW,inp,List.getD_eq_getElem?_getD,List.getElem?_append_right hle,bitsOf]
    · simp [rawBank,hj]

end WordCircuit
namespace WordCircuit
open PEqualNP.CircuitLowerBounds

def inputsFor (k a d : ℕ) (e : Fin 3) :=
  bitsOf k (a+e.val*d) ++ bitsOf k (a+(e+1).val*d)

theorem decoder_numeric (k : ℕ) (hk : 0<k) (e : Fin 3) :
    ∃ (g : List Gate) (start payload : List ℕ),
      GoodGates (2*k) g ∧ Exact g ∧ g.length ≤ 256*(k+1) ∧
      InRange (2*k) g start ∧ InRange (2*k) g payload ∧ start.length=k ∧ payload.length=k ∧
      ∀ a d : ℕ, a<2^k → 2*d<2^k →
        let x := inputsFor k a d e
        decodeNum x g start=a ∧ decodeNum x g payload = if e.val=2 then 2*d else d := by
  obtain ⟨g,u,v,w,good,legal,size,ru,rv,rw',lu,lv,lw,sem⟩ := difference_banks k hk
  have size' : g.length≤256*(k+1) := by omega
  let A := rawBank k 0
  let B := rawBank k k
  have ra : InRange (2*k) g A := raw_valid _ _ _ (by omega)
  have rb : InRange (2*k) g B := raw_valid _ _ _ le_rfl
  have lA : A.length=k := List.length_ofFn
  have lB : B.length=k := List.length_ofFn
  have ext : Extends [] g := ⟨g,by simp⟩
  have facts (a b : ℕ) :
      let x := bitsOf k a ++ bitsOf k b
      let d := ChannelRecovery.diff (2^k) (b%2^k) (a%2^k)
      decodeNum x g A=a%2^k ∧ decodeNum x g B=b%2^k ∧
      decodeNum x g u=d ∧ decodeNum x g v=ChannelRecovery.diff (2^k) (a%2^k) d ∧
      decodeNum x g w=ChannelRecovery.diff (2^k) (a%2^k) (b%2^k) := by
    intro x d
    have hx : x.length=2*k := by simp [x,bitsOf]; omega
    obtain ⟨xa,xb⟩ := incoming k a b
    have num := sem x hx
    change decodeNum x [] A=a%2^k at xa
    change decodeNum x [] B=b%2^k at xb
    change decodeNum x g u=_ ∧ decodeNum x g v=_ ∧ decodeNum x g w=_ at num
    change decodeNum x g u=ChannelRecovery.diff (2^k) (decodeNum x [] B) (decodeNum x [] A) ∧
      decodeNum x g v=ChannelRecovery.diff (2^k) (decodeNum x [] A)
        (ChannelRecovery.diff (2^k) (decodeNum x [] B) (decodeNum x [] A)) ∧
      decodeNum x g w=ChannelRecovery.diff (2^k) (decodeNum x [] A) (decodeNum x [] B) at num
    rw [xa,xb] at num
    exact ⟨(decode_stable ext (raw_valid k 0 [] (by omega)) hx).trans xa,
      (decode_stable ext (raw_valid k k [] le_rfl) hx).trans xb,num⟩
  fin_cases e
  · refine ⟨g,A,u,good,legal,size',ra,ru,lA,lu,?_⟩
    intro a d ha hd
    obtain ⟨d0,_,_,_⟩ := ChannelRecovery.recover_three ha hd
    have h := facts a (a+d)
    have start := h.1
    have delta := h.2.2.1
    rw [Nat.mod_eq_of_lt ha] at start delta
    simpa [inputsFor] using And.intro start (delta.trans d0)
  · refine ⟨g,v,u,good,legal,size',rv,ru,lv,lu,?_⟩
    intro a d ha hd
    obtain ⟨_,d1,a1,_⟩ := ChannelRecovery.recover_three ha hd
    have h := facts (a+d) (a+2*d)
    have start := h.2.2.2.1
    have delta := h.2.2.1
    rw [d1] at start delta
    simpa [inputsFor] using And.intro (start.trans a1) delta
  · refine ⟨g,B,w,good,legal,size',rb,rw',lB,lw,?_⟩
    intro a d ha hd
    obtain ⟨_,_,_,d2⟩ := ChannelRecovery.recover_three ha hd
    have h := facts (a+2*d) a
    have start := h.2.1
    have delta := h.2.2.2.2
    rw [Nat.mod_eq_of_lt ha] at start delta
    simpa [inputsFor] using And.intro start (delta.trans d2)

end WordCircuit

namespace PackedProgression

theorem pack_lt {B n : ℕ} (_hB : 0 < B) (x : Fin n → ℕ) (hx : ∀ i, x i < B) :
    Behrend.map B x < B^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Behrend.map_succ', pow_succ]
    have limit := ih (x ∘ Fin.succ) (fun i => hx i.succ)
    have hs := Nat.mul_le_mul_right B (Nat.succ_le_of_lt limit)
    rw [Nat.succ_mul] at hs
    have hz := hx 0
    omega

def lift {n : ℕ} (B : ℕ) (x : Fin n → ℕ) : ℕ :=
  Behrend.map B x + B^n * ∑ i, (x i)^2

theorem lift_rigid {n d : ℕ} (hd : 0 < d) (x y z : Fin n → ℕ)
    (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) (hz : ∀ i, z i < d)
    (eq : lift (2*d) x + lift (2*d) y = lift (2*d) z + lift (2*d) z) :
    x=z ∧ y=z := by
  let B := 2*d
  let L := B^n
  have hB : 0 < B := by dsimp [B]; omega
  have hL : 0 < L := pow_pos hB _
  have hxy (i) : (x+y) i < B := by have := hx i; have := hy i; change x i+y i<2*d; omega
  have hzz (i) : (z+z) i < B := by have := hz i; change z i+z i<2*d; omega
  have H : Behrend.map B (x+y) + L*((∑ i, (x i)^2)+(∑ i, (y i)^2)) =
      Behrend.map B (z+z) + L*((∑ i, (z i)^2)+(∑ i, (z i)^2)) := by
    simpa only [map_add,Nat.mul_add, lift, B, L, add_assoc,add_left_comm,add_comm] using eq
  have low := congrArg (fun v => v%L) H
  simp only [Nat.add_mul_mod_self_left] at low
  rw [Nat.mod_eq_of_lt (show Behrend.map B (x+y) < L from pack_lt hB _ hxy),
    Nat.mod_eq_of_lt (show Behrend.map B (z+z) < L from pack_lt hB _ hzz)] at low
  have coords : x+y = z+z := Behrend.map_injOn hxy hzz low
  rw [low, Nat.add_left_cancel_iff, Nat.mul_right_inj (Nat.ne_of_gt hL)] at H
  have hnorm : (∑ i, (x i : ℤ)^2) + (∑ i, (y i : ℤ)^2) =
      (∑ i, (z i : ℤ)^2) + (∑ i, (z i : ℤ)^2) := by exact_mod_cast H
  have delta (i) : ((x i : ℤ)-z i)^2 + ((y i : ℤ)-z i)^2 =
      (x i : ℤ)^2 + (y i : ℤ)^2 - ((z i : ℤ)^2 + (z i : ℤ)^2) := by
    have hc : (x i : ℤ)+y i=z i+z i := by exact_mod_cast (congrFun coords i)
    linear_combination (-2*(z i : ℤ))*hc
  have zero : ∑ i, (((x i : ℤ)-z i)^2 + ((y i : ℤ)-z i)^2) = 0 := by
    simp_rw [delta,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    omega
  have each := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    by exact add_nonneg (sq_nonneg ((x i : ℤ)-z i)) (sq_nonneg ((y i : ℤ)-z i)))).mp zero
  constructor <;> funext i <;> have hi := each i (Finset.mem_univ i)
  · have : (x i : ℤ) = z i := by nlinarith [sq_nonneg ((y i : ℤ)-z i),sq_nonneg ((x i : ℤ)-z i)]
    exact_mod_cast this
  · have : (y i : ℤ) = z i := by nlinarith [sq_nonneg ((x i : ℤ)-z i),sq_nonneg ((y i : ℤ)-z i)]
    exact_mod_cast this

end PackedProgression

namespace PackedProgression

theorem half_range {t b k : ℕ} (ht : 0<t)
    (hk : t*(b+1)+2*b+Nat.clog 2 t+1 ≤ k)
    (x : Fin t → ℕ) (hx : ∀ i, x i < 2^b) :
    lift (2*2^b) x + lift (2*2^b) x < 2^k := by
  let B := 2 * 2^b
  have hB : 0 < B := by dsimp [B]; positivity
  have pack : Behrend.map B x < B^t := pack_lt hB _ fun i => by
    have := hx i; dsimp [B]; omega
  let : Nonempty (Fin t) := ⟨⟨0,ht⟩⟩
  have sq : (∑ i, (x i)^2) < t*(2^b)^2 := by
    calc _ < ∑ _ : Fin t, (2^b)^2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun i _ => Nat.pow_lt_pow_left (hx i) (by decide))
         _ = _ := by simp
  have cap := Nat.mul_le_mul_left (B^t) (Nat.succ_le_of_lt sq)
  rw [Nat.mul_succ] at cap
  have lim : lift B x < B^t*(t*(2^b)^2) := by
    dsimp [lift]
    omega
  have pB : B = 2^(b+1) := by simp [B,pow_succ,Nat.mul_comm]
  have pows : B^t * (2^b)^2 * 2^Nat.clog 2 t * 2 ≤ 2^k := by
    rw [pB, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_succ]
    apply Nat.pow_le_pow_right (by decide)
    simpa [Nat.mul_comm] using hk
  have tbound := Nat.le_pow_clog (by decide : 1 < 2) t
  have scale := Nat.mul_le_mul_left (B^t*(2^b)^2) tbound
  have : B^t*(t*(2^b)^2) = (B^t*(2^b)^2)*t := by ring
  rw [this] at lim
  change lift B x + lift B x < _
  omega

def binval {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i, if x i then 2^i.val else 0

theorem binval_pack {n : ℕ} (x : Fin n → Bool) :
    binval x = Behrend.map 2 (fun i => (x i).toNat) := by
  unfold binval
  change _ = ∑ i, (x i).toNat * 2^i.val
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

theorem binval_lt {n : ℕ} (x : Fin n → Bool) : binval x < 2^n := by
  rw [binval_pack]
  apply pack_lt (by decide)
  intro i
  cases x i <;> decide

theorem binval_inj {n : ℕ} : Function.Injective (@binval n) := by
  intro x y h
  rw [binval_pack,binval_pack] at h
  have binary (u : Fin n → Bool) (i : Fin n) : (u i).toNat < 2 := by cases u i <;> decide
  have he := Behrend.map_injOn (binary x) (binary y) h
  funext i
  have hv := congrFun he i
  change (x i).toNat = (y i).toNat at hv
  cases ex : x i <;> cases ey : y i <;> simp_all

end PackedProgression

namespace ChannelArithmetic

theorem code_to_mod {k x y : ℕ} (h : ∀ i : Fin k, x.testBit i.val = y.testBit i.val) :
    x ≡ y [MOD 2^k] := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<k
  · simpa [Nat.testBit_mod_two_pow,hi] using h ⟨i,hi⟩
  · simp [Nat.testBit_mod_two_pow,hi]

theorem cyclic_elimination {M u v w D E F : ℕ}
    (d : D+D < M) (e : E+E < M) (f : F+F < M)
    (s0 : u ≡ v [MOD M]) (s1 : v+E ≡ w+F [MOD M])
    (s2 : w+2*F ≡ u+2*D [MOD M]) : E+F = D+D := by
  have q0 := (ZMod.natCast_eq_natCast_iff u v M).2 s0
  have q1 := (ZMod.natCast_eq_natCast_iff (v+E) (w+F) M).2 s1
  have q2 := (ZMod.natCast_eq_natCast_iff (w+2*F) (u+2*D) M).2 s2
  push_cast at q1 q2
  have h : ((E+F : ℕ) : ZMod M) = ((D+D : ℕ) : ZMod M) := by
    push_cast
    linear_combination q0+q1+q2
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).1 h
  exact hm.eq_of_lt_of_lt (by omega) d

end ChannelArithmetic

namespace PackedWords
open PackedProgression ChannelArithmetic

def readBit {n : ℕ} (w : Fin n → Bool) (i : ℕ) := (List.ofFn w).getD i false

theorem read_lt {n : ℕ} (w : Fin n → Bool) (i : ℕ) (hi : i<n) : readBit w i = w ⟨i,hi⟩ := by
  simp [readBit,List.getD_eq_getElem?_getD,hi]

def digit {t b : ℕ} (w : Fin (t*b) → Bool) (i : Fin t) :=
  binval (fun j : Fin b => readBit w (i.val*b+j.val))

theorem digit_inj {t b : ℕ} (hb : 0<b) : Function.Injective (@digit t b) := by
  intro x y h
  funext j
  let i : Fin t := ⟨j.val/b,(Nat.div_lt_iff_lt_mul hb).mpr j.isLt⟩
  let v : Fin b := ⟨j.val % b,Nat.mod_lt _ hb⟩
  have bits := binval_inj (congrFun h i)
  have spot := congrFun bits v
  have idx : i.val*b+v.val = j.val := by
    change (j.val/b)*b+j.val % b=j.val
    simpa [Nat.mul_comm] using Nat.div_add_mod j.val b
  change readBit x (i.val*b+v.val) = readBit y (i.val*b+v.val) at spot
  simpa only [idx,read_lt _ _ j.isLt] using spot

def start {k m : ℕ} (w : Fin (k+m) → Bool) := binval (fun j : Fin k => readBit w j.val)
def tailWord {k m : ℕ} (w : Fin (k+m) → Bool) (j : Fin m) := readBit w (k+j.val)

theorem word_ext {k m : ℕ} (x y : Fin (k+m) → Bool)
    (a : start (k:=k) (m:=m) x = start y) (b : tailWord (k:=k) (m:=m) x = tailWord y) :
    x=y := by
  funext j
  by_cases hj : j.val<k
  · have bits := binval_inj a
    have h := congrFun bits (⟨j.val,hj⟩ : Fin k)
    change readBit x j.val = readBit y j.val at h
    simpa only [read_lt _ _ j.isLt] using h
  · have jm := j.isLt
    have h := congrFun b (⟨j.val-k,by omega⟩ : Fin m)
    change readBit x (k+(j.val-k)) = readBit y (k+(j.val-k)) at h
    have eq : k+(j.val-k)=j.val := by omega
    simpa only [eq,read_lt _ _ j.isLt] using h

theorem lift_formula {t b : ℕ} (w : Fin (t*b) → Bool) :
    (∑ i : Fin t, digit w i * 2^((b+1)*i.val)) +
      2^(t*(b+1)) * ∑ i : Fin t, (digit w i)^2 = lift (2*2^b) (digit w) := by
  have B : 2*2^b = 2^(b+1) := by simp [pow_succ,Nat.mul_comm]
  simp only [lift,Behrend.map_apply,B,← pow_mul,Nat.mul_comm (b+1) t]

end PackedWords

namespace PackedWords
open PackedProgression ChannelArithmetic

theorem cycle {t b k : ℕ} (ht : 0<t) (hb : 0<b)
    (hk : t*(b+1)+2*b+Nat.clog 2 t+1 ≤ k)
    (v : Fin 3 → Fin (k+t*b) → Bool) :
    let A := fun i => start (k:=k) (m:=t*b) (v i)
    let P := fun i => digit (t:=t) (b:=b) (tailWord (k:=k) (m:=t*b) (v i))
    let D := fun i => lift (2*2^b) (P i)
    (∀ i : Fin 3, ∀ j : Fin k, (A i + i.val*D i).testBit j.val =
      (A (i+1) + i.val*D (i+1)).testBit j.val) → ∀ i, v i=v 0 := by
  intro A P D matchbits
  have rangeD (i) : D i+D i < 2^k := half_range ht hk (P i)
    (fun j => binval_lt _)
  have rangeA (i) : A i < 2^k := binval_lt _
  have e0 : A 0 ≡ A 1 [MOD 2^k] := by
    have h := code_to_mod (k:=k) (matchbits 0)
    simpa only [Fin.val_zero,Nat.zero_mul,Nat.add_zero,zero_add] using h
  have e1 : A 1+D 1 ≡ A 2+D 2 [MOD 2^k] := by
    have h := code_to_mod (k:=k) (matchbits 1)
    change A 1+1*D 1 ≡ A 2+1*D 2 [MOD 2^k] at h
    simpa using h
  have e2 : A 2+2*D 2 ≡ A 0+2*D 0 [MOD 2^k] := code_to_mod (k:=k) (matchbits 2)
  have prog := cyclic_elimination (rangeD 0) (rangeD 1) (rangeD 2) e0 e1 e2
  obtain ⟨p1,p2⟩ := lift_rigid (by positivity) (P 1) (P 2) (P 0)
    (fun j => binval_lt _) (fun j => binval_lt _) (fun j => binval_lt _) prog
  have d12 : D 1=D 2 := congrArg (lift (2*2^b)) (p1.trans p2.symm)
  have a01 := e0.eq_of_lt_of_lt (rangeA 0) (rangeA 1)
  have a12 : A 1=A 2 := by
    rw [d12] at e1
    exact (Nat.ModEq.add_right_cancel' _ e1).eq_of_lt_of_lt (rangeA 1) (rangeA 2)
  intro i
  fin_cases i
  · rfl
  · exact word_ext _ _ a01.symm (digit_inj hb p1)
  · exact word_ext _ _ (a01.trans a12).symm (digit_inj hb p2)

end PackedWords

namespace PackedWords
theorem official_agreement : (∀ (t b : ℕ), 0 < t → 0 < b →
  let m := t*b
  let X := Fin m → Bool
  let low := t*(b+1)
  let h := low + 2*b + Nat.clog 2 t + 1
  let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
    if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
  let lift := fun payload : X =>
    (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
  ∀ k : ℕ, h ≤ k →
    let n := k+m
    let Word := Fin n → Bool
    let start := fun word : Word => ∑ j : Fin k, if (List.ofFn word).getD j.val false then 2^j.val else 0
    let tailWord := fun (word : Word) (j : Fin m) => (List.ofFn word).getD (k+j.val) false
    let code := fun (word : Word) (e : Fin 3) (bit : Fin k) =>
      (start word + e.val * lift (tailWord word)).testBit bit.val
    (∀ v : Fin 3 → Word, (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) →
      ∀ party : Fin 3, v party = v 0)
) := by

  intro t b ht hb m X low h dig lifted k hk n Word st tail code v agree party
  apply cycle ht hb hk v _ party
  intro i j
  have hh := congrFun (agree i) j
  have hl (x : X) : lifted x = PackedProgression.lift (2*2^b) (digit (t:=t) (b:=b) x) :=
    lift_formula x
  change (st (v i) + i.val * lifted (tail (v i))).testBit j.val =
    (st (v (i+1)) + i.val * lifted (tail (v (i+1)))).testBit j.val at hh
  have st_eq (w : Word) : st w = @PackedWords.start k m w := rfl
  have tail_eq (w : Word) : tail w = @PackedWords.tailWord k m w := by funext l; rfl
  simp only [hl,st_eq,tail_eq] at hh
  exact hh

end PackedWords
namespace PackedProgression
theorem bank_extract {n w : ℕ} (x : Fin n → ℕ) (hx : ∀ i, x i < 2^w) (i : Fin n) {j : ℕ} (hj : j<w) :
    (Behrend.map (2^w) x).testBit (w*i.val+j) = (x i).testBit j := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [Behrend.map_succ',Nat.add_comm,Nat.mul_comm _ (2^w),
      Nat.testBit_two_pow_mul_add _ (hx 0)]
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [hj]
    · have eq : w*(l.val+1)+j = (w*l.val+j)+w := by ring
      simp only [Fin.val_succ,eq]
      rw [if_neg (by omega),Nat.add_sub_cancel]
      exact ih (x ∘ Fin.succ) (fun a => hx _) l

theorem binval_read {n : ℕ} (x : Fin n → Bool) (j : Fin n) :
    (binval x).testBit j.val = x j := by
  rw [binval_pack]
  have h := bank_extract (w:=1) (fun i => (x i).toNat)
    (fun i => by cases x i <;> decide) j (j:=0) (by decide)
  simpa using h.trans (by cases x j <;> rfl)

theorem lift_bit {t b : ℕ} (x : Fin t → ℕ) (hx : ∀ i, x i < 2^b)
    (i : Fin t) (j : Fin b) :
    (lift (2*2^b) x).testBit ((b+1)*i.val+j.val) = (x i).testBit j.val := by
  have base : 2*2^b = 2^(b+1) := by simp [pow_succ,Nat.mul_comm]
  have each (l : Fin t) : x l < 2^(b+1) := (hx l).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have lim := pack_lt (Nat.two_pow_pos (b+1)) x each
  have sz : (2^(b+1))^t=2^((b+1)*t) := (pow_mul _ _ _).symm
  rw [sz] at lim
  have ix : (b+1)*i.val+j.val < (b+1)*t := by
    have h := Nat.mul_le_mul_left (b+1) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at h
    omega
  rw [lift,base,sz,Nat.add_comm,Nat.testBit_two_pow_mul_add _ lim,if_pos ix]
  exact bank_extract x each i (by omega)
end PackedProgression

namespace WordCircuit
open PEqualNP.CircuitLowerBounds
theorem official_decoder : (∀ (t b : ℕ), 0 < t → 0 < b →
  let m := t*b
  let X := Fin m → Bool
  let low := t*(b+1)
  let h := low + 2*b + Nat.clog 2 t + 1
  let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
    if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
  let lift := fun payload : X =>
    (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
  ∀ k : ℕ, h ≤ k →
    let n := k+m
    let Word := Fin n → Bool
    let start := fun word : Word => ∑ j : Fin k, if (List.ofFn word).getD j.val false then 2^j.val else 0
    let tailWord := fun (word : Word) (j : Fin m) => (List.ofFn word).getD (k+j.val) false
    let code := fun (word : Word) (e : Fin 3) (bit : Fin k) =>
      (start word + e.val * lift (tailWord word)).testBit bit.val
    let valid := fun (len : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack len C ∧
      ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)
    ∀ channel : Fin 3,
      ∃ (dec : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin n → Fin (2*k+dec.size)),
        valid (2*k) dec ∧ dec.size ≤ 256*(k+1) ∧
        ∀ (u : Word) (j : Fin n),
          (dec.wires (List.ofFn (code u channel) ++ List.ofFn (code u (channel+1)))).getD
            (out j).val false = u j) := by
  intro t b ht hb m X low h dig lifted k hk n Word st tail code valid e
  have hk0 : 0<k := by dsimp [h,low] at hk; omega
  obtain ⟨g,as,ds,good,legal,size,ars,drs,asz,dsz,sem⟩ := decoder_numeric k hk0 e
  let C : Circuit := ⟨g,0⟩
  obtain ⟨getA,bitA⟩ := bank_bit asz ars
  obtain ⟨getD,bitD⟩ := bank_bit dsz drs
  let idx (q : Fin m) : Fin t := ⟨q.val/b,(Nat.div_lt_iff_lt_mul hb).mpr q.isLt⟩
  let off (q : Fin m) : Fin b := ⟨q.val % b,Nat.mod_lt _ hb⟩
  let slot (q : Fin m) := (b+1)*(idx q).val+(off q).val
  have slotLt (q : Fin m) : slot q<low := by
    have lim := Nat.mul_le_mul_left (b+1) (Nat.succ_le_of_lt (idx q).isLt)
    rw [Nat.mul_succ,Nat.mul_comm (b+1) t] at lim
    have := (off q).isLt
    dsimp only [slot,low]; omega
  let shift := if e.val=2 then 1 else 0
  have can (q : Fin m) : slot q+shift<k := by
    have := slotLt q
    dsimp only [h] at hk
    dsimp [shift]; split <;> omega
  let rest (j : Fin n) (hjk : ¬ j.val<k) : Fin m := ⟨j.val-k,by have := j.isLt; dsimp [n] at *; omega⟩
  let output (j : Fin n) : Fin (2*k+g.length) :=
    if hjk : j.val<k then getA ⟨j.val,hjk⟩ else
      getD ⟨slot (rest j hjk)+shift,can _⟩
  refine ⟨C,output,⟨good.2,legal⟩,size,?_⟩
  intro u j
  let a := st u
  let d := lifted (tail u)
  let input := inputsFor k a d e
  have startEq : a = @PackedWords.start k m u := rfl
  have dEq : d = PackedProgression.lift (2*2^b) (PackedWords.digit (t:=t) (b:=b) (tail u)) :=
    PackedWords.lift_formula _
  have boundA : a<2^k := PackedProgression.binval_lt _
  have boundD : 2*d<2^k := by
    rw [dEq,two_mul]
    exact PackedProgression.half_range ht hk _ (fun i => PackedProgression.binval_lt _)
  obtain ⟨decodeA,decodeD⟩ := sem a d boundA boundD
  change wireVal input g (output j).val = u j
  by_cases hjk : j.val<k
  · let bit : Fin k := ⟨j.val,hjk⟩
    change wireVal input g (if h : j.val<k then getA ⟨j.val,h⟩ else getD ⟨_,can _⟩).val = _
    rw [dif_pos hjk,bitA,decodeA]
    change (PackedProgression.binval (fun l : Fin k => PackedWords.readBit u l.val)).testBit bit.val = _
    rw [PackedProgression.binval_read,PackedWords.read_lt _ _ j.isLt]
  · let q := rest j hjk
    let i := idx q
    let l := off q
    have qi : i.val*b+l.val=q.val := by
      change q.val/b*b+q.val % b=q.val
      simpa only [Nat.mul_comm (q.val/b) b] using Nat.div_add_mod q.val b
    have orig : k+q.val=j.val := by dsimp [q,rest]; omega
    have extract : d.testBit (slot q) = u j := by
      rw [dEq]
      change (PackedProgression.lift _ _).testBit ((b+1)*i.val+l.val) = _
      rw [PackedProgression.lift_bit (PackedWords.digit (t:=t) (b:=b) (tail u)) (fun i => PackedProgression.binval_lt _) i l]
      change (PackedProgression.binval (fun j' : Fin b => PackedWords.readBit (tail u) (i.val*b+j'.val))).testBit l.val = _
      rw [PackedProgression.binval_read,qi,PackedWords.read_lt _ _ q.isLt]
      change PackedWords.readBit u (k+q.val)=u j
      rw [orig,PackedWords.read_lt _ _ j.isLt]
    simp only [output,dif_neg hjk]
    rw [bitD,decodeD]
    change (if e.val=2 then 2*d else d).testBit (slot q+shift) = _
    by_cases he : e.val=2
    · simp only [he,if_pos,shift,reduceCtorEq,↓reduceIte]
      simpa only [show 2*d=d*2 by omega,Nat.testBit_succ,Nat.mul_div_cancel _ (by decide : 0<2)] using extract
    · simpa [he,shift] using extract

end WordCircuit

end PEqualNP.Outside.L_pcx_251_aux

open PEqualNP.Outside.L_pcx_251_aux in
theorem PEqualNP.Outside.L_pcx_251 : (∀ (t b : ℕ), 0 < t → 0 < b →
  let m := t*b
  let X := Fin m → Bool
  let low := t*(b+1)
  let h := low + 2*b + Nat.clog 2 t + 1
  let digit := fun (raw : X) (i : Fin t) => ∑ j : Fin b,
    if (List.ofFn raw).getD (i.val*b+j.val) false then 2^j.val else 0
  let lift := fun payload : X =>
    (∑ i : Fin t, digit payload i * 2^((b+1)*i.val)) + 2^low * ∑ i : Fin t, (digit payload i)^2
  ∀ k : ℕ, h ≤ k →
    let n := k+m
    let Word := Fin n → Bool
    let start := fun word : Word => ∑ j : Fin k, if (List.ofFn word).getD j.val false then 2^j.val else 0
    let tailWord := fun (word : Word) (j : Fin m) => (List.ofFn word).getD (k+j.val) false
    let code := fun (word : Word) (e : Fin 3) (bit : Fin k) =>
      (start word + e.val * lift (tailWord word)).testBit bit.val
    let valid := fun (len : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack len C ∧
      ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)
    (∀ v : Fin 3 → Word, (∀ i : Fin 3, code (v i) i = code (v (i+1)) i) →
      ∀ party : Fin 3, v party = v 0) ∧
    (∃ (enc : PEqualNP.CircuitLowerBounds.Circuit) (send : Fin 3 → Fin k → Fin (n+enc.size)),
      valid n enc ∧ enc.size ≤ 1024*(k+t*b*b+1) ∧
      ∀ (u : Word) (edge : Fin 3) (j : Fin k),
        (enc.wires (List.ofFn u)).getD (send edge j).val false = code u edge j) ∧
    ∀ channel : Fin 3,
      ∃ (dec : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin n → Fin (2*k+dec.size)),
        valid (2*k) dec ∧ dec.size ≤ 256*(k+1) ∧
        ∀ (u : Word) (j : Fin n),
          (dec.wires (List.ofFn (code u channel) ++ List.ofFn (code u (channel+1)))).getD
            (out j).val false = u j) := by
  intro t b ht hb m X low h dig lifted k hk n Word st tail code valid
  exact ⟨PackedWords.official_agreement t b ht hb k hk,
    WordCircuit.official_encoder t b ht hb k hk, WordCircuit.official_decoder t b ht hb k hk⟩
