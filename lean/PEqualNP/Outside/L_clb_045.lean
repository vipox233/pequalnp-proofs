import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_045

open PEqualNP.CircuitLowerBounds

-- Bitwise helpers

private theorem testBit_false_of_ge {a k j : Nat} (ha : a < 2 ^ k) (hj : k ≤ j) :
    a.testBit j = false := by
  have hpow : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  have hlt : a < 2 ^ j := Nat.lt_of_lt_of_le ha hpow
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt hlt]
  rfl

private theorem testBit_one_shiftLeft (p j : Nat) :
    (1 <<< p).testBit j = decide (j = p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : p ≤ j
  · simp only [decide_eq_true hle, Bool.true_and]
    by_cases heq : j = p
    · subst heq; simp
    · simp only [decide_eq_false heq]
      exact testBit_false_of_ge (k := 1) (by omega) (by omega)
  · have hne : j ≠ p := by omega
    simp [hle, hne]

private theorem testBit_bool_shiftLeft (b : Bool) (p j : Nat) :
    (b.toNat <<< p).testBit j = (decide (j = p) && b) := by
  cases b
  · simp
  · simp only [Bool.toNat_true, Bool.and_true]
    exact testBit_one_shiftLeft p j

private def packBits (len : Nat) (f : Nat → Bool) : Nat :=
  (List.range len).foldl (fun acc j => acc ||| ((f j).toNat <<< j)) 0

private theorem packBits_testBit (len : Nat) (f : Nat → Bool) (j : Nat) :
    (packBits len f).testBit j = if j < len then f j else false := by
  induction len with
  | zero => simp [packBits]
  | succ len ih =>
    unfold packBits at ih ⊢
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih, testBit_bool_shiftLeft]
    by_cases hlt : j < len
    · have hne : j ≠ len := by omega
      have hlt2 : j < len + 1 := by omega
      simp [hlt, hne, hlt2]
    · by_cases heq : j = len
      · subst heq; simp
      · have hlt2 : ¬ j < len + 1 := by omega
        simp [hlt, heq, hlt2]

private theorem packBits_lt (len : Nat) (f : Nat → Bool) : packBits len f < 2 ^ len := by
  have hmod : packBits len f % 2 ^ len < 2 ^ len := Nat.mod_lt _ (Nat.two_pow_pos len)
  suffices heq : packBits len f = packBits len f % 2 ^ len by omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, packBits_testBit]
  by_cases h : j < len <;> simp [h]

private theorem testBit_two_mul_add_bool (h : Nat) (c : Bool) (r : Nat) :
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

private theorem testBit_add_bool_mul_pow {z t : Nat} (hz : z < 2 ^ t) (b : Bool) (j : Nat) :
    (z + b.toNat * 2 ^ t).testBit j =
      if j < t then z.testBit j else if j = t then b else false := by
  by_cases hlt : j < t
  · simp only [hlt, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ t = 2 ^ j * (2 * 2 ^ (t - j - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
    rw [hpow, ← mul_assoc, mul_comm b.toNat (2 ^ j), mul_assoc,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
    have hmod : (z / 2 ^ j + b.toNat * (2 * 2 ^ (t - j - 1))) % 2 = (z / 2 ^ j) % 2 := by
      have : b.toNat * (2 * 2 ^ (t - j - 1)) = 2 * (b.toNat * 2 ^ (t - j - 1)) := by ring
      rw [this, Nat.add_mul_mod_self_left]
    rw [hmod]
  · simp only [hlt, ↓reduceIte]
    by_cases heq : j = t
    · subst heq
      simp only [↓reduceIte]
      rw [Nat.testBit_eq_decide_div_mod_eq, mul_comm b.toNat (2 ^ j),
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hz, Nat.zero_add]
      cases b <;> rfl
    · simp only [heq, ↓reduceIte]
      apply testBit_false_of_ge (k := t + 1) _ (by omega)
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      have : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega
      nlinarith

-- Plain List Gate circuit builder

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def evalW (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl stepWire x

private def wireVal (x : List Bool) (gs : List Gate) (idx : Nat) : Bool :=
  (evalW x gs).getD idx false

private def GoodGates (inputs : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < inputs + j)

private def Extends (gs gs' : List Gate) : Prop :=
  ∃ ext, gs' = gs ++ ext

private theorem Extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], by simp⟩

private theorem Extends_trans {a b c : List Gate} (h1 : Extends a b) (h2 : Extends b c) :
    Extends a c := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

private theorem Extends_len {a b : List Gate} (h : Extends a b) : a.length ≤ b.length := by
  rcases h with ⟨e, rfl⟩
  simp

private theorem evalW_len (x : List Bool) (gs : List Gate) :
    (evalW x gs).length = x.length + gs.length := by
  unfold evalW
  induction gs generalizing x with
  | nil => simp
  | cons g tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWire x g)]
    simp [stepWire]
    omega

private theorem evalW_append (x : List Bool) (gs1 gs2 : List Gate) :
    evalW x (gs1 ++ gs2) = evalW (evalW x gs1) gs2 := by
  unfold evalW
  rw [List.foldl_append]

private theorem stepWire_getD_lt (w : List Bool) (g : Gate) {i : Nat} (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem stepWire_getD_self (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

private theorem wireVal_extends {x : List Bool} {gs1 gs2 : List Gate} {idx : Nat}
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

private theorem wireVal_snoc_self (x : List Bool) (gs : List Gate) (g : Gate) :
    wireVal x (gs ++ [g]) (x.length + gs.length) =
      g.op.eval (g.inputs.map (wireVal x gs)) := by
  unfold wireVal
  rw [evalW_append]
  unfold evalW
  simp only [List.foldl_cons, List.foldl_nil]
  have hlen : x.length + gs.length = (gs.foldl stepWire x).length := (evalW_len x gs).symm
  rw [hlen, stepWire_getD_self]

private theorem GoodGates_nil (inputs : Nat) : GoodGates inputs [] :=
  ⟨fun _ h => (by cases h), fun _ h => (by simp at h)⟩

private theorem GoodGates_snoc {inputs : Nat} {gs : List Gate} {g : Gate}
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

-- Gate primitives

private def addFalse (inputs : Nat) (gs : List Gate) : List Gate × Nat :=
  (gs ++ [⟨.or, []⟩], inputs + gs.length)

private def addTrue (inputs : Nat) (gs : List Gate) : List Gate × Nat :=
  (gs ++ [⟨.and, []⟩], inputs + gs.length)

private def addAnd (inputs : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  (gs ++ [⟨.and, [a, b]⟩], inputs + gs.length)

private def addOr (inputs : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  (gs ++ [⟨.or, [a, b]⟩], inputs + gs.length)

private def addNot (inputs : Nat) (gs : List Gate) (a : Nat) : List Gate × Nat :=
  (gs ++ [⟨.not, [a]⟩], inputs + gs.length)

private theorem addFalse_spec {inputs : Nat} {gs : List Gate} (hg : GoodGates inputs gs) :
    let r := addFalse inputs gs
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireVal x r.1 r.2 = false := by
  refine ⟨⟨[⟨.or, []⟩], rfl⟩, by simp [addFalse],
    GoodGates_snoc hg (by simp) (by simp) (fun _ h => by simp at h),
    by simp [addFalse], ?_⟩
  intro x hx
  dsimp only [addFalse]
  rw [← hx, wireVal_snoc_self]
  rfl

private theorem addTrue_spec {inputs : Nat} {gs : List Gate} (hg : GoodGates inputs gs) :
    let r := addTrue inputs gs
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireVal x r.1 r.2 = true := by
  refine ⟨⟨[⟨.and, []⟩], rfl⟩, by simp [addTrue],
    GoodGates_snoc hg (by simp) (by simp) (fun _ h => by simp at h),
    by simp [addTrue], ?_⟩
  intro x hx
  dsimp only [addTrue]
  rw [← hx, wireVal_snoc_self]
  rfl

private theorem addAnd_spec {inputs : Nat} {gs : List Gate} {a b : Nat}
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

private theorem addOr_spec {inputs : Nat} {gs : List Gate} {a b : Nat}
    (hg : GoodGates inputs gs) (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let r := addOr inputs gs a b
    Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ GoodGates inputs r.1 ∧ r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = (wireVal x gs a || wireVal x gs b) := by
  refine ⟨⟨[⟨.or, [a, b]⟩], rfl⟩, by simp [addOr],
    GoodGates_snoc hg (by simp) (by simp) (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega),
    by simp [addOr], ?_⟩
  intro x hx
  dsimp only [addOr]
  rw [← hx, wireVal_snoc_self]
  simp [GateOp.eval]

private theorem addNot_spec {inputs : Nat} {gs : List Gate} {a : Nat}
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

-- 9-gate full adder via direct snoc chain

private def addFullAdder (inputs : Nat) (gs : List Gate) (a b cin : Nat) :
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

private theorem fullAdder_bool (a b c : Bool) :
    let s1 := (a || b) && !(a && b)
    let sum := (s1 || c) && !(s1 && c)
    let cout := (a && b) || (s1 && c)
    a.toNat + b.toNat + c.toNat = sum.toNat + 2 * cout.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem addFullAdder_spec {inputs : Nat} {gs : List Gate} {a b cin : Nat}
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

-- Multi-bit counter encoding and operations

private def decodeNum (x : List Bool) (gs : List Gate) : List Nat → Nat
  | [] => 0
  | w :: ws => (wireVal x gs w).toNat + 2 * decodeNum x gs ws

private theorem decodeNum_extends {x : List Bool} {gs1 gs2 : List Gate} {ws : List Nat}
    (hext : Extends gs1 gs2) (hws : ∀ w ∈ ws, w < x.length + gs1.length) :
    decodeNum x gs2 ws = decodeNum x gs1 ws := by
  induction ws with
  | nil => rfl
  | cons w tl ih =>
    simp only [decodeNum]
    rw [wireVal_extends hext (hws w (List.mem_cons_self ..)),
        ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))]

private theorem decodeNum_testBit (x : List Bool) (gs : List Gate) (ws : List Nat) (b : Nat) :
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

private theorem decodeNum_replicate_false {x : List Bool} {gs : List Gate} {wFalse : Nat}
    (hf : wireVal x gs wFalse = false) (len : Nat) :
    decodeNum x gs (List.replicate len wFalse) = 0 := by
  induction len with
  | zero => rfl
  | succ len ih =>
    simp [List.replicate_succ, decodeNum, hf, ih]

private def emitAndList (inputs : Nat) (gs : List Gate) (acc : Nat) : List Nat → List Gate × Nat
  | [] => (gs, acc)
  | w :: ws =>
    let r := addAnd inputs gs acc w
    emitAndList inputs r.1 r.2 ws

private theorem emitAndList_spec {inputs : Nat} {gs : List Gate} {acc : Nat} {ws : List Nat}
    (hg : GoodGates inputs gs) (hacc : acc < inputs + gs.length)
    (hws : ∀ w ∈ ws, w < inputs + gs.length) :
    let r := emitAndList inputs gs acc ws
    Extends gs r.1 ∧ r.1.length = gs.length + ws.length ∧ GoodGates inputs r.1 ∧
    r.2 < inputs + r.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireVal x r.1 r.2 = (wireVal x gs acc && ws.all (wireVal x gs)) := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨Extends_refl gs, by simp [emitAndList], hg, hacc, fun x _ => by simp [emitAndList]⟩
  | cons w tl ih =>
    simp only [emitAndList]
    have h1 := addAnd_spec hg hacc (hws w (List.mem_cons_self ..))
    rcases h1 with ⟨he1, hl1, hg1, hw1, hv1⟩
    have htl : ∀ u ∈ tl, u < inputs + (addAnd inputs gs acc w).1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem _ hu); omega
    have h2 := ih hg1 hw1 htl
    rcases h2 with ⟨he2, hl2, hg2, hw2, hv2⟩
    refine ⟨Extends_trans he1 he2, by simp [hl2, hl1]; omega, hg2, hw2, ?_⟩
    intro x hx
    rw [hv2 x hx, hv1 x hx]
    have hall : tl.all (wireVal x (addAnd inputs gs acc w).1) = tl.all (wireVal x gs) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact ⟨fun h u hu => by
          have hu_lt := hws u (List.mem_cons_of_mem _ hu)
          rw [← wireVal_extends he1 (by omega)]; exact h u hu,
        fun h u hu => by
          have hu_lt := hws u (List.mem_cons_of_mem _ hu)
          rw [wireVal_extends he1 (by omega)]; exact h u hu⟩
    rw [hall, List.all_cons, Bool.and_assoc]

private def emitMask (inputs : Nat) (gs : List Gate) (flag : Nat) : List Nat → List Gate × List Nat
  | [] => (gs, [])
  | w :: ws =>
    let r1 := addAnd inputs gs flag w
    let r2 := emitMask inputs r1.1 flag ws
    (r2.1, r1.2 :: r2.2)

private theorem emitMask_spec {inputs : Nat} {gs : List Gate} {flag : Nat} {ws : List Nat}
    (hg : GoodGates inputs gs) (hflag : flag < inputs + gs.length)
    (hws : ∀ w ∈ ws, w < inputs + gs.length) :
    let r := emitMask inputs gs flag ws
    Extends gs r.1 ∧ r.1.length = gs.length + ws.length ∧ GoodGates inputs r.1 ∧
    r.2.length = ws.length ∧ (∀ w ∈ r.2, w < inputs + r.1.length) ∧
    ∀ x : List Bool, x.length = inputs →
      decodeNum x r.1 r.2 = if wireVal x gs flag then decodeNum x gs ws else 0 := by
  induction ws generalizing gs with
  | nil =>
    refine ⟨Extends_refl gs, by simp [emitMask], hg, by simp [emitMask],
      fun _ h => by simp [emitMask] at h, fun x _ => by simp [emitMask, decodeNum]⟩
  | cons w tl ih =>
    simp only [emitMask]
    have h1 := addAnd_spec hg hflag (hws w (List.mem_cons_self ..))
    rcases h1 with ⟨he1, hl1, hg1, hw1, hv1⟩
    have htl : ∀ u ∈ tl, u < inputs + (addAnd inputs gs flag w).1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem _ hu); omega
    have h2 := ih hg1 (by omega) htl
    rcases h2 with ⟨he2, hl2, hg2, hlen2, hws2, hv2⟩
    refine ⟨Extends_trans he1 he2, by simp [hl2, hl1]; omega, hg2, by simp [hlen2], ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu2
      · have := Extends_len he2; omega
      · exact hws2 u hu2
    · intro x hx
      simp only [decodeNum]
      rw [wireVal_extends he2 (by omega), hv1 x hx, hv2 x hx,
          wireVal_extends he1 (by omega),
          decodeNum_extends he1 (fun u hu => by have := hws u (List.mem_cons_of_mem _ hu); omega)]
      cases wireVal x gs flag <;> simp

private def emitAddAux (inputs : Nat) (gs : List Gate) (cin : Nat) :
    List Nat → List Nat → List Gate × List Nat
  | [], _ => (gs, [])
  | _, [] => (gs, [])
  | a :: as, b :: bs =>
    let r1 := addFullAdder inputs gs a b cin
    let r2 := emitAddAux inputs r1.1 r1.2.2 as bs
    (r2.1, r1.2.1 :: r2.2)

private theorem emitAddAux_spec {inputs : Nat} {gs : List Gate} {cin : Nat} {as bs : List Nat}
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

private def emitAdd (inputs : Nat) (gs : List Gate) (wFalse : Nat) (as bs : List Nat) :
    List Gate × List Nat :=
  emitAddAux inputs gs wFalse as bs

private theorem emitAdd_spec {inputs : Nat} {gs : List Gate} {wFalse : Nat} {as bs : List Nat}
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

private def emitMaskAdd (inputs : Nat) (gs : List Gate) (wFalse f0 : Nat) (a : List Nat)
    (f1 : Nat) (b : List Nat) : List Gate × List Nat :=
  let r1 := emitMask inputs gs f0 a
  let r2 := emitMask inputs r1.1 f1 b
  emitAdd inputs r2.1 wFalse r1.2 r2.2

private theorem emitMaskAdd_spec {inputs : Nat} {gs : List Gate} {wFalse f0 f1 : Nat} {a b : List Nat}
    (hg : GoodGates inputs gs) (hwf : wFalse < inputs + gs.length)
    (hf0 : f0 < inputs + gs.length) (hf1 : f1 < inputs + gs.length)
    (hlen : a.length = b.length)
    (ha : ∀ w ∈ a, w < inputs + gs.length) (hb : ∀ w ∈ b, w < inputs + gs.length) :
    let r := emitMaskAdd inputs gs wFalse f0 a f1 b
    Extends gs r.1 ∧ r.1.length = gs.length + 11 * a.length ∧ GoodGates inputs r.1 ∧
    r.2.length = a.length ∧ (∀ w ∈ r.2, w < inputs + r.1.length) ∧
    ∀ x : List Bool, x.length = inputs → wireVal x gs wFalse = false →
      decodeNum x r.1 r.2 =
        ((if wireVal x gs f0 then decodeNum x gs a else 0) +
         (if wireVal x gs f1 then decodeNum x gs b else 0)) % 2 ^ a.length := by
  unfold emitMaskAdd
  have h1 := emitMask_spec hg hf0 ha
  rcases h1 with ⟨he1, hl1, hg1, hlen1, hws1, hv1⟩
  have hb1 : ∀ w ∈ b, w < inputs + (emitMask inputs gs f0 a).1.length := fun w hw => by
    have := hb w hw; omega
  have h2 := emitMask_spec (flag := f1) hg1 (by have := Extends_len he1; omega) hb1
  rcases h2 with ⟨he2, hl2, hg2, hlen2, hws2, hv2⟩
  have hws1' : ∀ w ∈ (emitMask inputs gs f0 a).2, w < inputs + (emitMask inputs (emitMask inputs gs f0 a).1 f1 b).1.length :=
    fun w hw => by have := hws1 w hw; have := Extends_len he2; omega
  have h3 := emitAdd_spec (wFalse := wFalse) hg2 (by have := Extends_len he1; have := Extends_len he2; omega) (by rw [hlen1, hlen2, hlen]) hws1' hws2
  rcases h3 with ⟨he3, hl3, hg3, hlen3, hws3, hv3⟩
  refine ⟨Extends_trans he1 (Extends_trans he2 he3), by rw [hl3, hl2, hl1, hlen1, hlen]; omega, hg3, by rw [hlen3, hlen1], hws3, ?_⟩
  intro x hx hwf_val
  have hwf2 : wireVal x (emitMask inputs (emitMask inputs gs f0 a).1 f1 b).1 wFalse = false := by
    rw [wireVal_extends (Extends_trans he1 he2) (by omega), hwf_val]
  rw [hv3 x hx hwf2, hlen1,
      decodeNum_extends he2 (fun w hw => by have := hws1 w hw; omega),
      hv1 x hx, hv2 x hx,
      wireVal_extends he1 (by omega),
      decodeNum_extends he1 (fun w hw => by have := hb w hw; omega)]

private def emitSumList (inputs bits : Nat) (gs : List Gate) (wFalse : Nat) :
    List (List Nat) → List Gate × List Nat
  | [] => (gs, List.replicate bits wFalse)
  | num :: rest =>
    let r1 := emitSumList inputs bits gs wFalse rest
    emitAdd inputs r1.1 wFalse num r1.2

private theorem emitSumList_spec {inputs bits : Nat} {gs : List Gate} {wFalse : Nat}
    {nums : List (List Nat)}
    (hg : GoodGates inputs gs) (hwf : wFalse < inputs + gs.length)
    (hnums : ∀ num ∈ nums, num.length = bits ∧ ∀ w ∈ num, w < inputs + gs.length) :
    let r := emitSumList inputs bits gs wFalse nums
    Extends gs r.1 ∧ r.1.length = gs.length + 9 * bits * nums.length ∧ GoodGates inputs r.1 ∧
    r.2.length = bits ∧ (∀ w ∈ r.2, w < inputs + r.1.length) ∧
    ∀ x : List Bool, x.length = inputs → wireVal x gs wFalse = false →
      decodeNum x r.1 r.2 = (nums.map (decodeNum x gs)).sum % 2 ^ bits := by
  induction nums generalizing gs with
  | nil =>
    refine ⟨Extends_refl gs, by simp [emitSumList], hg, by simp [emitSumList],
      fun w hw => by simp [emitSumList] at hw; exact hw.2 ▸ hwf,
      fun x _ hwf_v => by simp [emitSumList, decodeNum_replicate_false hwf_v]⟩
  | cons num rest ih =>
    simp only [emitSumList]
    have hrest : ∀ u ∈ rest, u.length = bits ∧ ∀ w ∈ u, w < inputs + gs.length :=
      fun u hu => hnums u (List.mem_cons_of_mem _ hu)
    have h1 := ih hg hwf hrest
    rcases h1 with ⟨he1, hl1, hg1, hlen1, hws1, hv1⟩
    have hnum := hnums num (List.mem_cons_self ..)
    have hnum1 : ∀ w ∈ num, w < inputs + (emitSumList inputs bits gs wFalse rest).1.length :=
      fun w hw => by have := hnum.2 w hw; have := Extends_len he1; omega
    have h2 := emitAdd_spec (wFalse := wFalse) hg1 (by have := Extends_len he1; omega) (by rw [hnum.1, hlen1]) hnum1 hws1
    rcases h2 with ⟨he2, hl2, hg2, hlen2, hws2, hv2⟩
    refine ⟨Extends_trans he1 he2, by simp only [List.length_cons]; rw [hl2, hl1, hnum.1]; ring,
      hg2, by omega, hws2, ?_⟩
    intro x hx hwf_v
    have hwf1 : wireVal x (emitSumList inputs bits gs wFalse rest).1 wFalse = false := by
      rw [wireVal_extends he1 (by omega), hwf_v]
    rw [hv2 x hx hwf1, hnum.1, hv1 x hx hwf_v,
        decodeNum_extends he1 (fun w hw => by have := hnum.2 w hw; omega)]
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

-- Wire indices into wiresIn

private def tableWire (w i pat : Nat) : Nat :=
  i * 2 ^ (w + 1) + pat

private def allowWire (m w j : Nat) (b : Bool) : Nat :=
  m * 2 ^ (w + 1) + 2 * j + b.toNat

private theorem tableWire_lt {n m w i pat : Nat} (hi : i < m) (hp : pat < 2 ^ (w + 1)) :
    tableWire w i pat < m * 2 ^ (w + 1) + 2 * n := by
  unfold tableWire
  have hmul : i * 2 ^ (w + 1) + 2 ^ (w + 1) ≤ m * 2 ^ (w + 1) := by
    have : i + 1 ≤ m := hi
    calc i * 2 ^ (w + 1) + 2 ^ (w + 1) = (i + 1) * 2 ^ (w + 1) := by ring
      _ ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ this
  omega

private theorem allowWire_lt {n m w j : Nat} (hj : j < n) (b : Bool) :
    allowWire m w j b < m * 2 ^ (w + 1) + 2 * n := by
  unfold allowWire
  cases b <;> simp <;> omega

private theorem wireVal_tableWire {n m w i pat : Nat} (hn : 0 < n) (hm : 0 < m)
    (hi : i < m) (hp : pat < 2 ^ (w + 1))
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool)
    (gs : List Gate) :
    let tableInputs := m * 2 ^ (w + 1)
    let inputs := tableInputs + 2 * n
    let wiresIn := List.ofFn (fun a : Fin inputs =>
      if a.val < tableInputs then
        table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
          (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
      else
        let t := a.val - tableInputs
        allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
    wireVal wiresIn gs (tableWire w i pat) = table ⟨i, hi⟩ (fun b => pat.testBit b.val) := by
  intro tableInputs inputs wiresIn
  have hlt_ti : tableWire w i pat < tableInputs := by
    unfold tableWire tableInputs
    have : (i + 1) * 2 ^ (w + 1) ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ hi
    nlinarith
  have hlt_in : tableWire w i pat < wiresIn.length := by
    simp only [wiresIn, List.length_ofFn, inputs]; omega
  have hext : Extends [] gs := ⟨gs, by simp⟩
  rw [wireVal_extends hext (by simpa using hlt_in)]
  unfold wireVal evalW
  simp only [List.foldl_nil, wiresIn, List.getD_eq_getElem?_getD]
  have hidx : tableWire w i pat < inputs := by omega
  rw [List.getElem?_eq_getElem (by simp [List.length_ofFn]; exact hidx)]
  simp only [Option.getD_some, List.getElem_ofFn, hlt_ti, ↓reduceIte]
  have hdiv : tableWire w i pat / 2 ^ (w + 1) = i := by
    unfold tableWire
    rw [mul_comm i (2 ^ (w + 1)), add_comm,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos (w + 1)),
        Nat.div_eq_of_lt hp, Nat.zero_add]
  have hmod : tableWire w i pat % 2 ^ (w + 1) = pat := by
    unfold tableWire
    rw [mul_comm i (2 ^ (w + 1)), add_comm,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  simp only [hdiv, hmod, Nat.mod_eq_of_lt hi]

private theorem wireVal_allowWire {n m w j : Nat} (hn : 0 < n) (hm : 0 < m)
    (hj : j < n) (b : Bool)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool)
    (gs : List Gate) :
    let tableInputs := m * 2 ^ (w + 1)
    let inputs := tableInputs + 2 * n
    let wiresIn := List.ofFn (fun a : Fin inputs =>
      if a.val < tableInputs then
        table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
          (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
      else
        let t := a.val - tableInputs
        allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
    wireVal wiresIn gs (allowWire m w j b) = allow ⟨j, hj⟩ b := by
  intro tableInputs inputs wiresIn
  have hge_ti : ¬ allowWire m w j b < tableInputs := by unfold allowWire tableInputs; omega
  have hlt_in : allowWire m w j b < wiresIn.length := by
    simp only [wiresIn, List.length_ofFn, inputs]
    exact allowWire_lt hj b
  have hext : Extends [] gs := ⟨gs, by simp⟩
  rw [wireVal_extends hext (by simpa using hlt_in)]
  unfold wireVal evalW
  simp only [List.foldl_nil, wiresIn, List.getD_eq_getElem?_getD]
  have hidx : allowWire m w j b < inputs := allowWire_lt hj b
  rw [List.getElem?_eq_getElem (by simp [List.length_ofFn]; exact hidx)]
  simp only [Option.getD_some, List.getElem_ofFn, hge_ti, ↓reduceIte]
  have hsub : allowWire m w j b - tableInputs = 2 * j + b.toNat := by unfold allowWire tableInputs; omega
  have hdiv : (2 * j + b.toNat) / 2 = j := by cases b <;> (simp only [Bool.toNat_false, Bool.toNat_true]; omega)
  have hdec : decide ((2 * j + b.toNat) % 2 = 1) = b := by cases b <;> simp
  simp only [hsub, hdiv, hdec, Nat.mod_eq_of_lt hj]

-- Case 1: d = 0 (w = 0 or n = 1)

private def buildD0Step (inputs m w : Nat) (wFalse : Nat) (t : Nat)
    (st : List Gate × List Nat) : List Gate × List Nat :=
  let (gs, cnt) := st
  if t < m then
    let pat0 := packBits (w + 1) (fun _ => false)
    let pat1 := packBits (w + 1) (fun _ => true)
    let r0 := addAnd inputs gs (allowWire m w t false) (tableWire w t pat0)
    let r1 := addAnd inputs r0.1 (allowWire m w t true) (tableWire w t pat1)
    emitMaskAdd inputs r1.1 wFalse r0.2 cnt r1.2 cnt
  else
    emitMaskAdd inputs gs wFalse (allowWire m w t false) cnt (allowWire m w t true) cnt

private def buildD0 (n m w : Nat) : List Gate × List Nat :=
  let inputs := m * 2 ^ (w + 1) + 2 * n
  let rF := addFalse inputs []
  let rT := addTrue inputs rF.1
  let initCnt := rT.2 :: List.replicate n rF.2
  (List.range n).foldl (fun st t => buildD0Step inputs m w rF.2 t st) (rT.1, initCnt)

-- Case 2: d > 0 (1 <= d <= n - 1)

private def dpWindowPat (n w h' : Nat) (c : Bool) : Nat :=
  packBits (w + 1) (fun p => (2 * h' + c.toNat).testBit (p % n))

private def dpWrapPat (n w d α h i : Nat) : Nat :=
  packBits (w + 1) (fun p =>
    let q := (i + p) % n
    if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q)

private def buildInitFlags (inputs m w d : Nat) (wTrue : Nat) :
    List Gate → Nat → List Gate × (Nat → Nat)
  | gs, 0 => (gs, fun _ => wTrue)
  | gs, h + 1 =>
    let rPrev := buildInitFlags inputs m w d wTrue gs h
    let ws := (List.range d).map (fun j => allowWire m w j (h.testBit j))
    let rNow := emitAndList inputs rPrev.1 wTrue ws
    (rNow.1, fun x => if x = h then rNow.2 else rPrev.2 x)

private def buildDPStepLoop (inputs n m w d : Nat) (wFalse : Nat) (t : Nat)
    (prevCnt : Nat → Nat → List Nat) :
    List Gate → List (Nat × Nat) → List Gate × (Nat → Nat → List Nat)
  | gs, [] => (gs, fun _ _ => [])
  | gs, (α, h') :: rest =>
    let b := h'.testBit (d - 1)
    let h0 := (2 * h') % 2 ^ d
    let h1 := h0 + 1
    let rFlags : List Gate × Nat × Nat :=
      if t - d < m then
        let r0 := addAnd inputs gs (allowWire m w t b) (tableWire w (t - d) (dpWindowPat n w h' false))
        let r1 := addAnd inputs r0.1 (allowWire m w t b) (tableWire w (t - d) (dpWindowPat n w h' true))
        (r1.1, r0.2, r1.2)
      else
        (gs, allowWire m w t b, allowWire m w t b)
    let rAdd := emitMaskAdd inputs rFlags.1 wFalse rFlags.2.1 (prevCnt α h0) rFlags.2.2 (prevCnt α h1)
    let rRest := buildDPStepLoop inputs n m w d wFalse t prevCnt rAdd.1 rest
    (rRest.1, fun α' h'' => if α' = α ∧ h'' = h' then rAdd.2 else rRest.2 α' h'')

private def allPairs (e d : Nat) : List (Nat × Nat) :=
  (List.range (2 ^ e)).flatMap (fun α => (List.range (2 ^ d)).map (fun h => (α, h)))

private def buildWrapLoop (inputs n m w d e : Nat) (wTrue : Nat)
    (finalCnt : Nat → Nat → List Nat) :
    List Gate → List (Nat × Nat) → List Gate × List (List Nat)
  | gs, [] => (gs, [])
  | gs, (α, h) :: rest =>
    let ws := (List.range e).map (fun k => tableWire w (n - d + k) (dpWrapPat n w d α h (n - d + k)))
    let rFlag := emitAndList inputs gs wTrue ws
    let rMask := emitMask inputs rFlag.1 rFlag.2 (finalCnt α h)
    let rRest := buildWrapLoop inputs n m w d e wTrue finalCnt rMask.1 rest
    (rRest.1, rMask.2 :: rRest.2)

private def buildDPos (n m w : Nat) : List Gate × List Nat :=
  let inputs := m * 2 ^ (w + 1) + 2 * n
  let d := min w (n - 1)
  let e := m + d - n
  let rF := addFalse inputs []
  let rT := addTrue inputs rF.1
  let rInit := buildInitFlags inputs m w d rT.2 rT.1 (2 ^ d)
  let zeroCnt := List.replicate (n + 1) rF.2
  let initTable : Nat → Nat → List Nat := fun α h =>
    if h % 2 ^ e = α then rInit.2 h :: List.replicate n rF.2 else zeroCnt
  let pairs := allPairs e d
  let rDP := (List.range (n - d)).foldl
    (fun (st : List Gate × (Nat → Nat → List Nat)) stepIdx =>
      buildDPStepLoop inputs n m w d rF.2 (d + stepIdx) st.2 st.1 pairs)
    (rInit.1, initTable)
  let rWrap := buildWrapLoop inputs n m w d e rT.2 rDP.2 rDP.1 pairs
  emitSumList inputs (n + 1) rWrap.1 rF.2 rWrap.2

-- Combinatorial specifications for Case 1 (d = 0) and Case 2 (d > 0)

private theorem allPairs_len (e d : Nat) : (allPairs e d).length = 2 ^ (d + e) := by
  unfold allPairs
  rw [List.length_flatMap]
  have hmap : ((List.range (2 ^ e)).map (fun α => ((List.range (2 ^ d)).map (fun h => (α, h))).length)) =
      List.replicate (2 ^ e) (2 ^ d) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp
  rw [hmap, List.sum_replicate, smul_eq_mul, Nat.pow_add]
  ring

private theorem allPairs_mem {e d α h : Nat} :
    (α, h) ∈ allPairs e d ↔ α < 2 ^ e ∧ h < 2 ^ d := by
  unfold allPairs
  simp

private theorem allPairs_nodup (e d : Nat) : (allPairs e d).Nodup := by
  unfold allPairs
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro α _
    exact List.Nodup.map (fun a b hab => by injection hab) List.nodup_range
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    intro p hp1 hp2
    simp only [List.mem_map] at hp1 hp2
    rcases hp1 with ⟨_, _, rfl⟩
    rcases hp2 with ⟨_, _, heq⟩
    have : j = i := by injection heq
    omega

private theorem buildD0_spec {n m w : Nat} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (hd0 : min w (n - 1) = 0) :
    let tableInputs := m * 2 ^ (w + 1)
    let inputs := tableInputs + 2 * n
    let r := buildD0 n m w
    GoodGates inputs r.1 ∧
    r.1.length ≤ 16 * (n + 1) ^ 2 * 2 ^ (0 + (m + 0 - n)) + 2 ∧
    r.2.length = n + 1 ∧ (∀ w' ∈ r.2, w' < inputs + r.1.length) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      decodeNum wiresIn r.1 r.2 = sols.card := by
  intro tableInputs inputs
  have hinputs : inputs = m * 2 ^ (w + 1) + 2 * n := rfl
  let rF := addFalse inputs []
  let rT := addTrue inputs rF.1
  let initCnt := rT.2 :: List.replicate n rF.2
  have hF := addFalse_spec (GoodGates_nil inputs)
  have hT := addTrue_spec hF.2.2.1
  have hFLen : rF.1.length = 1 := hF.2.1
  have hTLen : rT.1.length = 2 := by rw [show rT.1.length = rF.1.length + 1 from hT.2.1, hFLen]
  have hFT : Extends rF.1 rT.1 := hT.1
  have hwf_F : rF.2 < inputs + rF.1.length := hF.2.2.2.1
  have hwf_lt : rF.2 < inputs + rT.1.length := by omega
  have hwt_lt : rT.2 < inputs + rT.1.length := hT.2.2.2.1
  -- Inductive invariant over t <= n steps
  have hloop : ∀ t, t ≤ n →
      let st := (List.range t).foldl (fun st j => buildD0Step inputs m w rF.2 j st) (rT.1, initCnt)
      Extends rT.1 st.1 ∧
      st.1.length ≤ 2 + t * (2 + 11 * (n + 1)) ∧
      GoodGates inputs st.1 ∧
      st.2.length = n + 1 ∧
      (∀ u ∈ st.2, u < inputs + st.1.length) ∧
      ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        decodeNum wiresIn st.1 st.2 =
          (Finset.univ.filter (fun z : Fin (2 ^ t) =>
            (∀ j : Fin n, j.val < t → allow j (z.val.testBit j.val) = true) ∧
            ∀ i : Fin m, i.val < t → table i (fun _ => z.val.testBit i.val) = true)).card := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨Extends_refl rT.1, by simp [hTLen], hT.2.2.1, by simp [initCnt], ?_, ?_⟩
      · intro u hu
        simp only [List.range_zero, List.foldl_nil, initCnt, List.mem_cons, List.mem_replicate] at hu ⊢
        rcases hu with rfl | ⟨_, rfl⟩ <;> omega
      · intro table allow wiresIn
        have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
        have hwf_v : wireVal wiresIn rT.1 rF.2 = false := by
          rw [wireVal_extends hFT (by omega), hF.2.2.2.2 wiresIn hlen_x]
        have hwt_v : wireVal wiresIn rT.1 rT.2 = true := hT.2.2.2.2 wiresIn hlen_x
        simp only [List.range_zero, List.foldl_nil, initCnt, decodeNum, hwt_v,
          decodeNum_replicate_false hwf_v]
        have hcard : (Finset.univ.filter (fun z : Fin (2 ^ 0) =>
            (∀ j : Fin n, j.val < 0 → allow j (z.val.testBit j.val) = true) ∧
            ∀ i : Fin m, i.val < 0 → table i (fun _ => z.val.testBit i.val) = true)).card = 1 := by
          have : (Finset.univ.filter (fun z : Fin (2 ^ 0) =>
              (∀ j : Fin n, j.val < 0 → allow j (z.val.testBit j.val) = true) ∧
              ∀ i : Fin m, i.val < 0 → table i (fun _ => z.val.testBit i.val) = true)) = Finset.univ := by
            ext z; simp
          rw [this, Finset.card_univ, Fintype.card_fin]; rfl
        exact hcard.symm
    | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨hext, hlen_g, hgg, hlen_c, hws_c, hval⟩
      set st := (List.range t).foldl (fun st j => buildD0Step inputs m w rF.2 j st) (rT.1, initCnt)
      have hfold : (List.range (t + 1)).foldl (fun st j => buildD0Step inputs m w rF.2 j st) (rT.1, initCnt) =
          buildD0Step inputs m w rF.2 t st := by
        rw [List.range_succ, List.foldl_append]; rfl
      rw [hfold]
      have hwf_st : rF.2 < inputs + st.1.length := by have := Extends_len hext; omega
      -- Combinatorial step: card at t+1 = (if ok false then card t else 0) + (if ok true then card t else 0)
      have hstep_comb : ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
          let ok : Bool → Bool := fun b =>
            if htm : t < m then allow ⟨t, by omega⟩ b && table ⟨t, htm⟩ (fun _ => b)
            else allow ⟨t, by omega⟩ b
          let cardT := (Finset.univ.filter (fun z : Fin (2 ^ t) =>
            (∀ j : Fin n, j.val < t → allow j (z.val.testBit j.val) = true) ∧
            ∀ i : Fin m, i.val < t → table i (fun _ => z.val.testBit i.val) = true)).card
          (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) =>
            (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
            ∀ i : Fin m, i.val < t + 1 → table i (fun _ => z.val.testBit i.val) = true)).card =
          (if ok false then cardT else 0) + (if ok true then cardT else 0) := by
        intro table allow ok cardT
        let P : Fin (2 ^ (t + 1)) → Prop := fun z =>
          (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
          ∀ i : Fin m, i.val < t + 1 → table i (fun _ => z.val.testBit i.val) = true
        let Q : Fin (2 ^ t) → Prop := fun z =>
          (∀ j : Fin n, j.val < t → allow j (z.val.testBit j.val) = true) ∧
          ∀ i : Fin m, i.val < t → table i (fun _ => z.val.testBit i.val) = true
        have hpart : (Finset.univ.filter P).card =
            (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) => P z ∧ z.val.testBit t = false)).card +
            (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) => P z ∧ z.val.testBit t = true)).card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1; ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            cases z.val.testBit t <;> simp
          · rw [Finset.disjoint_left]; intro z hz1 hz2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
            rw [hz1.2] at hz2; cases hz2.2
        have hbranch : ∀ b : Bool,
            (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) => P z ∧ z.val.testBit t = b)).card =
              if ok b then cardT else 0 := by
          intro b
          cases hok : ok b
          · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_eq_zero]
            rw [Finset.eq_empty_iff_forall_notMem]
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
            rcases hz with ⟨⟨h1, h2⟩, hbt⟩
            have ha := h1 ⟨t, by omega⟩ (Nat.lt_succ_self t)
            rw [hbt] at ha
            by_cases htm : t < m
            · have htb := h2 ⟨t, htm⟩ (Nat.lt_succ_self t)
              simp only [hbt] at htb
              simp [ok, htm, ha, htb] at hok
            · simp [ok, htm, ha] at hok
          · simp only [↓reduceIte]
            apply Finset.card_bij (fun z _ => ⟨z.val % 2 ^ t, Nat.mod_lt _ (Nat.two_pow_pos t)⟩)
            · intro z hz
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
              refine ⟨fun j hj => ?_, fun i hi => ?_⟩
              · have := hz.1.1 j (by omega)
                rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]; exact this
              · have := hz.1.2 i (by omega)
                have hfeq : (fun _ : Fin (w + 1) => (z.val % 2 ^ t).testBit i.val) =
                    (fun _ : Fin (w + 1) => z.val.testBit i.val) := by
                  funext _; rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
                rw [hfeq]; exact this
            · intro z1 hz1 z2 hz2 heq
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
              have hmod : z1.val % 2 ^ t = z2.val % 2 ^ t := congrArg Fin.val heq
              apply Fin.ext
              apply Nat.eq_of_testBit_eq
              intro j
              by_cases hj : j < t
              · have h1 := congrArg (fun x => x.testBit j) hmod
                simpa [Nat.testBit_mod_two_pow, hj] using h1
              · by_cases hj2 : j = t
                · subst hj2; rw [hz1.2, hz2.2]
                · rw [testBit_false_of_ge z1.isLt (by omega), testBit_false_of_ge z2.isLt (by omega)]
            · intro z0 hz0
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz0
              have hz_lt : z0.val + b.toNat * 2 ^ t < 2 ^ (t + 1) := by
                have hb : b.toNat ≤ 1 := by cases b <;> simp
                have : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega
                have := z0.isLt; nlinarith
              refine ⟨⟨z0.val + b.toNat * 2 ^ t, hz_lt⟩, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                have htb : (z0.val + b.toNat * 2 ^ t).testBit t = b := by
                  rw [testBit_add_bool_mul_pow z0.isLt b t]; simp
                refine ⟨⟨fun j hj => ?_, fun i hi => ?_⟩, htb⟩
                · rw [testBit_add_bool_mul_pow z0.isLt b j.val]
                  by_cases hlt : j.val < t
                  · simp only [hlt, ↓reduceIte]; exact hz0.1 j hlt
                  · have hjeq : j.val = t := by omega
                    have hjfin : j = ⟨t, by omega⟩ := Fin.ext hjeq
                    simp only [hlt, ↓reduceIte]
                    simp only [hjeq, ↓reduceIte]
                    rw [hjfin]
                    by_cases htm : t < m
                    · simp [ok, htm] at hok; exact hok.1
                    · simp [ok, htm] at hok; exact hok
                · by_cases hlt : i.val < t
                  · have hfeq : (fun _ : Fin (w + 1) => (z0.val + b.toNat * 2 ^ t).testBit i.val) =
                        (fun _ : Fin (w + 1) => z0.val.testBit i.val) := by
                      funext _; rw [testBit_add_bool_mul_pow z0.isLt b i.val]; simp [hlt]
                    rw [hfeq]; exact hz0.2 i hlt
                  · have hieq : i.val = t := by omega
                    have htm : t < m := by omega
                    have hifin : i = ⟨t, htm⟩ := Fin.ext hieq
                    have hfeq : (fun _ : Fin (w + 1) => (z0.val + b.toNat * 2 ^ t).testBit i.val) =
                        (fun _ : Fin (w + 1) => b) := by
                      funext _; rw [hieq, htb]
                    rw [hfeq, hifin]
                    simp [ok, htm] at hok
                    exact hok.2
              · apply Fin.ext
                dsimp only
                rw [mul_comm b.toNat (2 ^ t), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z0.isLt]
        rw [hpart, hbranch false, hbranch true]
      unfold buildD0Step
      by_cases htm : t < m
      · simp only [htm, ↓reduceIte]
        have ha0 : allowWire m w t false < inputs + st.1.length := by
          have := allowWire_lt (n := n) (m := m) (w := w) (j := t) (by omega) false; rw [hinputs]; omega
        have ha1 : allowWire m w t true < inputs + st.1.length := by
          have := allowWire_lt (n := n) (m := m) (w := w) (j := t) (by omega) true; rw [hinputs]; omega
        have ht0 : tableWire w t (packBits (w + 1) (fun _ => false)) < inputs + st.1.length := by
          have := tableWire_lt (n := n) (m := m) (w := w) (i := t) htm (packBits_lt (w + 1) (fun _ => false)); rw [hinputs]; omega
        have ht1 : tableWire w t (packBits (w + 1) (fun _ => true)) < inputs + st.1.length := by
          have := tableWire_lt (n := n) (m := m) (w := w) (i := t) htm (packBits_lt (w + 1) (fun _ => true)); rw [hinputs]; omega
        have hr0 := addAnd_spec hgg ha0 ht0
        set r0 := addAnd inputs st.1 (allowWire m w t false) (tableWire w t (packBits (w + 1) (fun _ => false)))
        rcases hr0 with ⟨he0, hl0, hg0, hw0, hv0⟩
        have hr1 := addAnd_spec (a := allowWire m w t true) (b := tableWire w t (packBits (w + 1) (fun _ => true))) hg0 (by omega) (by omega)
        set r1 := addAnd inputs r0.1 (allowWire m w t true) (tableWire w t (packBits (w + 1) (fun _ => true)))
        rcases hr1 with ⟨he1, hl1, hg1, hw1, hv1⟩
        have hws_c1 : ∀ u ∈ st.2, u < inputs + r1.1.length :=
          fun u hu => by have := hws_c u hu; have := Extends_len he0; have := Extends_len he1; omega
        have hma := emitMaskAdd_spec (wFalse := rF.2) (f0 := r0.2) (f1 := r1.2) hg1
          (by have := Extends_len he0; have := Extends_len he1; omega)
          (by have := Extends_len he1; omega) hw1 rfl hws_c1 hws_c1
        rcases hma with ⟨hema, hlma, hgma, hlenc, hwsc, hvma⟩
        refine ⟨Extends_trans hext (Extends_trans he0 (Extends_trans he1 hema)),
          by rw [hlma, hl1, hl0, hlen_c]; nlinarith, hgma, by omega, hwsc, ?_⟩
        intro table allow
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
        have hwf_v : wireVal wiresIn r1.1 rF.2 = false := by
          rw [wireVal_extends (Extends_trans hFT (Extends_trans hext (Extends_trans he0 he1))) (by omega),
              hF.2.2.2.2 wiresIn hlen_x]
        rw [hvma wiresIn hlen_x hwf_v, hlen_c,
            wireVal_extends he1 (by omega), hv0 wiresIn hlen_x, hv1 wiresIn hlen_x,
            wireVal_allowWire hn hm (by omega) false table allow,
            wireVal_allowWire hn hm (by omega) true table allow,
            wireVal_tableWire hn hm htm (packBits_lt _ _) table allow,
            wireVal_tableWire hn hm htm (packBits_lt _ _) table allow,
            decodeNum_extends (Extends_trans he0 he1) (fun u hu => by have := hws_c u hu; omega),
            hval table allow]
        have hp0 : (fun b : Fin (w + 1) => (packBits (w + 1) (fun _ => false)).testBit b.val) = (fun _ => false) := by
          funext b; rw [packBits_testBit]; simp [b.isLt]
        have hp1 : (fun b : Fin (w + 1) => (packBits (w + 1) (fun _ => true)).testBit b.val) = (fun _ => true) := by
          funext b; rw [packBits_testBit]; simp [b.isLt]
        rw [hp0, hp1]
        have hcomb := hstep_comb table allow
        simp only [htm, ↓reduceDIte] at hcomb
        rw [← hcomb]
        apply Nat.mod_eq_of_lt
        have hcard_le : (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) =>
            (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
            ∀ i : Fin m, i.val < t + 1 → table i (fun _ => z.val.testBit i.val) = true)).card ≤ 2 ^ (t + 1) := by
          have := Finset.card_filter_le (Finset.univ : Finset (Fin (2 ^ (t + 1))))
            (fun z => (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
              ∀ i : Fin m, i.val < t + 1 → table i (fun _ => z.val.testBit i.val) = true)
          simpa using this
        have hpow_le : 2 ^ (t + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) ht
        have hlt2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      · simp only [htm, ↓reduceIte]
        have ha0 : allowWire m w t false < inputs + st.1.length := by
          have := allowWire_lt (n := n) (m := m) (w := w) (j := t) (by omega) false; rw [hinputs]; omega
        have ha1 : allowWire m w t true < inputs + st.1.length := by
          have := allowWire_lt (n := n) (m := m) (w := w) (j := t) (by omega) true; rw [hinputs]; omega
        have hma := emitMaskAdd_spec hgg hwf_st ha0 ha1 rfl hws_c hws_c
        rcases hma with ⟨hema, hlma, hgma, hlenc, hwsc, hvma⟩
        refine ⟨Extends_trans hext hema, by rw [hlma, hlen_c]; nlinarith, hgma, by omega, hwsc, ?_⟩
        intro table allow
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
        have hwf_v : wireVal wiresIn st.1 rF.2 = false := by
          rw [wireVal_extends (Extends_trans hFT hext) (by omega),
              hF.2.2.2.2 wiresIn hlen_x]
        rw [hvma wiresIn hlen_x hwf_v, hlen_c,
            wireVal_allowWire hn hm (by omega) false table allow,
            wireVal_allowWire hn hm (by omega) true table allow,
            hval table allow]
        have hcomb := hstep_comb table allow
        simp only [htm, ↓reduceDIte] at hcomb
        rw [← hcomb]
        apply Nat.mod_eq_of_lt
        have hcard_le : (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) =>
            (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
            ∀ i : Fin m, i.val < t + 1 → table i (fun _ => z.val.testBit i.val) = true)).card ≤ 2 ^ (t + 1) := by
          have := Finset.card_filter_le (Finset.univ : Finset (Fin (2 ^ (t + 1))))
            (fun z => (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
              ∀ i : Fin m, i.val < t + 1 → table i (fun _ => z.val.testBit i.val) = true)
          simpa using this
        have hpow_le : 2 ^ (t + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) ht
        have hlt2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
  rcases hloop n (le_refl n) with ⟨_, hlen_g, hgg, hlen_c, hws_c, hval⟩
  have he0 : 0 + (m + 0 - n) = 0 := by omega
  dsimp only [buildD0]
  refine ⟨hgg, ?_, hlen_c, hws_c, ?_⟩
  · rw [he0]; simp only [Nat.pow_zero, mul_one]; nlinarith
  · intro table allow
    rw [hval table allow]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hmod_eq : ∀ (i : Fin m) (p : Fin (w + 1)), (i.val + p.val) % n = i.val := by
      intro i p
      have hw_or : w = 0 ∨ n = 1 := by omega
      rcases hw_or with hw0 | hn1
      · have hp0 : p.val = 0 := by omega
        rw [hp0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
      · have hi0 : i.val = 0 := by omega
        rw [hn1, hi0]; simp [Nat.mod_one]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => h1 j j.isLt, fun i => ?_⟩
      have hfeq : (fun p : Fin (w + 1) => z.val.testBit ((i.val + p.val) % n)) =
          (fun _ => z.val.testBit i.val) := by
        funext p; rw [hmod_eq i p]
      rw [hfeq]; exact h2 i (by omega)
    · rintro ⟨h1, h2⟩
      refine ⟨fun j _ => h1 j, fun i _ => ?_⟩
      have hfeq : (fun _ : Fin (w + 1) => z.val.testBit i.val) =
          (fun p : Fin (w + 1) => z.val.testBit ((i.val + p.val) % n)) := by
        funext p; rw [hmod_eq i p]
      rw [hfeq]; exact h2 i

-- Helper specs for Case 2 (d > 0)

private theorem buildInitFlags_spec {n m w d : Nat} (hn : 0 < n) (hm : 0 < m) (hd : d < n)
    {gs : List Gate} {wTrue : Nat}
    (hg : GoodGates (m * 2 ^ (w + 1) + 2 * n) gs)
    (hwt : wTrue < m * 2 ^ (w + 1) + 2 * n + gs.length) (K : Nat) :
    let inputs := m * 2 ^ (w + 1) + 2 * n
    let r := buildInitFlags inputs m w d wTrue gs K
    Extends gs r.1 ∧ r.1.length = gs.length + K * d ∧ GoodGates inputs r.1 ∧
    (∀ h < K, r.2 h < inputs + r.1.length) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let tableInputs := m * 2 ^ (w + 1)
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      wireVal wiresIn gs wTrue = true →
      ∀ h < K, wireVal wiresIn r.1 (r.2 h) = true ↔
        ∀ j : Fin n, j.val < d → allow j (h.testBit j.val) = true := by
  let inputs := m * 2 ^ (w + 1) + 2 * n
  induction K with
  | zero =>
    refine ⟨Extends_refl gs, by simp [buildInitFlags], hg, fun _ h => by omega,
      fun _ _ _ _ h => by omega⟩
  | succ K ih =>
    rcases ih with ⟨he1, hl1, hg1, hw1, hv1⟩
    simp only [buildInitFlags]
    let ws := (List.range d).map (fun j => allowWire m w j (K.testBit j))
    have hws_lt : ∀ u ∈ ws, u < inputs + (buildInitFlags inputs m w d wTrue gs K).1.length := by
      intro u hu
      simp only [ws, List.mem_map, List.mem_range] at hu
      rcases hu with ⟨j, hj, rfl⟩
      have := allowWire_lt (n := n) (m := m) (w := w) (j := j) (by omega) (K.testBit j)
      dsimp only [inputs]; omega
    have h2 := emitAndList_spec (acc := wTrue) hg1 (by have := Extends_len he1; omega) hws_lt
    rcases h2 with ⟨he2, hl2, hg2, hw2, hv2⟩
    refine ⟨Extends_trans he1 he2, by rw [hl2, hl1]; simp [ws]; ring, hg2, ?_, ?_⟩
    · intro h hh
      by_cases heq : h = K
      · subst heq; simp only [↓reduceIte]; exact hw2
      · simp only [heq, ↓reduceIte]
        exact Nat.lt_of_lt_of_le (hw1 h (by omega)) (Nat.add_le_add_left (Extends_len he2) _)
    · intro table allow hwt_v h hh
      let tableInputs := m * 2 ^ (w + 1)
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
      by_cases heq : h = K
      · subst heq
        simp only [↓reduceIte]
        have hwt1 : wireVal wiresIn (buildInitFlags inputs m w d wTrue gs h).1 wTrue = true := by
          rw [wireVal_extends he1 (by rw [List.length_ofFn]; exact hwt), hwt_v]
        rw [hv2 wiresIn hlen_x, hwt1, Bool.true_and, List.all_eq_true]
        constructor
        · intro hall j hj
          have hmem : allowWire m w j.val (h.testBit j.val) ∈ ws := by
            simp only [ws, List.mem_map, List.mem_range]; exact ⟨j.val, hj, rfl⟩
          have hv := hall _ hmem
          rw [wireVal_allowWire hn hm j.isLt (h.testBit j.val) table allow] at hv
          exact hv
        · intro hall u hu
          simp only [ws, List.mem_map, List.mem_range] at hu
          rcases hu with ⟨j, hj, rfl⟩
          rw [wireVal_allowWire hn hm (by omega) (h.testBit j) table allow]
          exact hall ⟨j, by omega⟩ hj
      · simp only [heq, ↓reduceIte]
        have hw_prev := hw1 h (by omega)
        rw [wireVal_extends he2 (by rw [List.length_ofFn]; exact hw_prev)]
        exact hv1 table allow hwt_v h (by omega)

private def prefCount (n m w d e : Nat)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (allow : Fin n → Bool → Bool) (t α h : Nat) : Nat :=
  (Finset.univ.filter (fun z : Fin (2 ^ t) =>
    (∀ j < e, z.val.testBit j = α.testBit j) ∧
    (∀ j < d, z.val.testBit (t - d + j) = h.testBit j) ∧
    (∀ j : Fin n, j.val < t → allow j (z.val.testBit j.val) = true) ∧
    (∀ i : Fin m, i.val + d < t →
      table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true))).card

private theorem dp_step_comb {n m w d e t α h' : Nat}
    (hn : 0 < n) (hd_pos : 0 < d) (hd_eq : d = min w (n - 1))
    (he_le_d : e ≤ d) (ht1 : d ≤ t) (ht2 : t < n)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool) :
    let b := h'.testBit (d - 1)
    let h0 := (2 * h') % 2 ^ d
    let h1 := h0 + 1
    prefCount n m w d e table allow (t + 1) α h' =
      (if (if htm : t - d < m then allow ⟨t, ht2⟩ b && table ⟨t - d, htm⟩ (fun p => (2 * h' + false.toNat).testBit (p.val % n))
           else allow ⟨t, ht2⟩ b) then prefCount n m w d e table allow t α h0 else 0) +
      (if (if htm : t - d < m then allow ⟨t, ht2⟩ b && table ⟨t - d, htm⟩ (fun p => (2 * h' + true.toNat).testBit (p.val % n))
           else allow ⟨t, ht2⟩ b) then prefCount n m w d e table allow t α h1 else 0) := by
  intro b h0 h1
  have hwin_idx : ∀ p : Fin (w + 1),
      p.val % n ≤ d ∧ ((t - d) + p.val) % n = (t - d) + (p.val % n) := by
    intro p
    by_cases hwn : w ≤ n - 1
    · have hdw : d = w := by omega
      have hpn : p.val < n := by omega
      rw [Nat.mod_eq_of_lt hpn, Nat.mod_eq_of_lt (by omega)]
      exact ⟨by omega, rfl⟩
    · have hdn : d = n - 1 := by omega
      have htd : t - d = 0 := by omega
      rw [htd, Nat.zero_add, Nat.zero_add]
      have hlt := Nat.mod_lt p.val hn
      exact ⟨by omega, rfl⟩
  let P1 : Fin (2 ^ (t + 1)) → Prop := fun z =>
    (∀ j < e, z.val.testBit j = α.testBit j) ∧
    (∀ j < d, z.val.testBit (t + 1 - d + j) = h'.testBit j) ∧
    (∀ j : Fin n, j.val < t + 1 → allow j (z.val.testBit j.val) = true) ∧
    (∀ i : Fin m, i.val + d < t + 1 → table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
  let ok : Bool → Bool := fun c =>
    if htm : t - d < m then allow ⟨t, ht2⟩ b && table ⟨t - d, htm⟩ (fun p => (2 * h' + c.toNat).testBit (p.val % n))
    else allow ⟨t, ht2⟩ b
  have hpart : prefCount n m w d e table allow (t + 1) α h' =
      (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) => P1 z ∧ z.val.testBit (t - d) = false)).card +
      (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) => P1 z ∧ z.val.testBit (t - d) = true)).card := by
    rw [← Finset.card_union_of_disjoint]
    · unfold prefCount; congr 1; ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, P1]
      cases z.val.testBit (t - d) <;> simp
    · rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
      rw [hz1.2] at hz2; cases hz2.2
  have hhc_bit : ∀ (c : Bool) (j : Nat), j < d →
      ((2 * h') % 2 ^ d + c.toNat).testBit j = if j = 0 then c else h'.testBit (j - 1) := by
    intro c j hj
    have hmod_eq : ((2 * h') % 2 ^ d + c.toNat) = (2 * h' + c.toNat) % 2 ^ d := by
      have h2d : 2 ∣ 2 ^ d := by
        have : d = (d - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; exact dvd_mul_left 2 _
      have hev : (2 * h') % 2 ^ d % 2 = 0 := by
        rcases h2d with ⟨q, hq⟩
        have hmul : 2 * (q * (2 * h' / 2 ^ d)) + (2 * h') % 2 ^ d = 2 * h' := by
          rw [← mul_assoc, ← hq]; exact Nat.div_add_mod (2 * h') (2 ^ d)
        omega
      have hlt : (2 * h') % 2 ^ d + c.toNat < 2 ^ d := by
        have := Nat.mod_lt (2 * h') (Nat.two_pow_pos d)
        cases c <;> (simp only [Bool.toNat_false, Bool.toNat_true]; omega)
      rw [← Nat.mod_eq_of_lt hlt, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [hmod_eq, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, testBit_two_mul_add_bool]
  have hbr : ∀ c : Bool,
      (Finset.univ.filter (fun z : Fin (2 ^ (t + 1)) => P1 z ∧ z.val.testBit (t - d) = c)).card =
        if ok c then prefCount n m w d e table allow t α (h0 + c.toNat) else 0 := by
    intro c
    have hwin_z : ∀ z : Fin (2 ^ (t + 1)), P1 z → z.val.testBit (t - d) = c →
        ∀ p : Fin (w + 1), z.val.testBit (((t - d) + p.val) % n) = (2 * h' + c.toNat).testBit (p.val % n) := by
      intro z hz hzc p
      have hw := hwin_idx p
      rw [hw.2, testBit_two_mul_add_bool]
      by_cases hr0 : p.val % n = 0
      · simp [hr0, hzc]
      · simp only [hr0, ↓reduceIte]
        have hidx : t - d + p.val % n = t + 1 - d + (p.val % n - 1) := by omega
        rw [hidx, hz.2.1 (p.val % n - 1) (by omega)]
    cases hok : ok c
    · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_eq_zero]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rcases hz with ⟨hz, hzc⟩
      have hzt : z.val.testBit t = b := by
        have := hz.2.1 (d - 1) (by omega)
        have hidx : t + 1 - d + (d - 1) = t := by omega
        rw [hidx] at this; exact this
      have ha := hz.2.2.1 ⟨t, ht2⟩ (Nat.lt_succ_self t)
      rw [hzt] at ha
      by_cases htm : t - d < m
      · have htb := hz.2.2.2 ⟨t - d, htm⟩ (by dsimp; omega)
        have hfeq : (fun p : Fin (w + 1) => z.val.testBit ((t - d + p.val) % n)) =
            (fun p => (2 * h' + c.toNat).testBit (p.val % n)) := funext (hwin_z z hz hzc)
        rw [hfeq] at htb
        simp [ok, htm, ha, htb] at hok
      · simp [ok, htm, ha] at hok
    · simp only [↓reduceIte]
      unfold prefCount
      apply Finset.card_bij (fun z _ => ⟨z.val % 2 ^ t, Nat.mod_lt _ (Nat.two_pow_pos t)⟩)
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
        · rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and]; exact hz.1.1 j hj
        · rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and, hhc_bit c j hj]
          by_cases hj0 : j = 0
          · subst hj0; simpa using hz.2
          · simp only [hj0, ↓reduceIte]
            have hidx : t - d + j = t + 1 - d + (j - 1) := by omega
            rw [hidx]; exact hz.1.2.1 (j - 1) (by omega)
        · rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]; exact hz.1.2.2.1 j (by omega)
        · have hfeq : (fun p : Fin (w + 1) => (z.val % 2 ^ t).testBit ((i.val + p.val) % n)) =
              (fun p => z.val.testBit ((i.val + p.val) % n)) := by
            funext p
            have hlt_t : (i.val + p.val) % n < t := by
              by_cases hwn : w ≤ n - 1
              · have : d = w := by omega
                rw [Nat.mod_eq_of_lt (by omega)]; omega
              · omega
            rw [Nat.testBit_mod_two_pow, decide_eq_true hlt_t, Bool.true_and]
          rw [hfeq]; exact hz.1.2.2.2 i (by omega)
      · intro z1 hz1 z2 hz2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
        have hmod : z1.val % 2 ^ t = z2.val % 2 ^ t := congrArg Fin.val heq
        apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
        by_cases hj : j < t
        · have h1 := congrArg (fun x => x.testBit j) hmod
          simpa [Nat.testBit_mod_two_pow, hj] using h1
        · by_cases hj2 : j = t
          · rw [hj2]
            have h1 := hz1.1.2.1 (d - 1) (by omega)
            have h2 := hz2.1.2.1 (d - 1) (by omega)
            have hidx : t + 1 - d + (d - 1) = t := by omega
            rw [hidx] at h1 h2; rw [h1, h2]
          · rw [testBit_false_of_ge z1.isLt (by omega), testBit_false_of_ge z2.isLt (by omega)]
      · intro z0 hz0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz0
        have hz_lt : z0.val + b.toNat * 2 ^ t < 2 ^ (t + 1) := by
          have hb : b.toNat ≤ 1 := by cases b <;> simp
          have : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega
          have := z0.isLt; nlinarith
        refine ⟨⟨z0.val + b.toNat * 2 ^ t, hz_lt⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hz_c : (z0.val + b.toNat * 2 ^ t).testBit (t - d) = c := by
            have hlt_td : t - d < t := by omega
            rw [testBit_add_bool_mul_pow z0.isLt b (t - d)]
            simp only [hlt_td, ↓reduceIte]
            have h0b := hz0.2.1 0 (by omega)
            rw [Nat.add_zero, hhc_bit c 0 (by omega)] at h0b
            simpa using h0b
          have hz_h' : ∀ j < d, (z0.val + b.toNat * 2 ^ t).testBit (t + 1 - d + j) = h'.testBit j := by
            intro j hj
            rw [testBit_add_bool_mul_pow z0.isLt b (t + 1 - d + j)]
            by_cases hlt : t + 1 - d + j < t
            · simp only [hlt, ↓reduceIte]
              have hidx : t + 1 - d + j = t - d + (j + 1) := by omega
              rw [hidx, hz0.2.1 (j + 1) (by omega), hhc_bit c (j + 1) (by omega)]
              simp
            · have hjeq : j = d - 1 := by omega
              have hteq : t + 1 - d + j = t := by omega
              simp only [hlt, ↓reduceIte]
              simp only [hteq, ↓reduceIte]
              rw [hjeq]
          refine ⟨⟨fun j hj => ?_, hz_h', fun j hj => ?_, fun i hi => ?_⟩, hz_c⟩
          · have hj_t : j < t := by omega
            rw [testBit_add_bool_mul_pow z0.isLt b j]; simp only [hj_t, ↓reduceIte]; exact hz0.1 j hj
          · rw [testBit_add_bool_mul_pow z0.isLt b j.val]
            by_cases hlt : j.val < t
            · simp only [hlt, ↓reduceIte]; exact hz0.2.2.1 j hlt
            · have hjeq : j.val = t := by omega
              have hjfin : j = ⟨t, ht2⟩ := Fin.ext hjeq
              simp only [hlt, ↓reduceIte]
              simp only [hjeq, ↓reduceIte]
              rw [hjfin]
              by_cases htm : t - d < m
              · simp [ok, htm] at hok; exact hok.1
              · simp [ok, htm] at hok; exact hok
          · by_cases hlt : i.val + d < t
            · have hfeq : (fun p : Fin (w + 1) => (z0.val + b.toNat * 2 ^ t).testBit ((i.val + p.val) % n)) =
                  (fun p => z0.val.testBit ((i.val + p.val) % n)) := by
                funext p
                have hlt_t : (i.val + p.val) % n < t := by
                  by_cases hwn : w ≤ n - 1
                  · have : d = w := by omega
                    rw [Nat.mod_eq_of_lt (by omega)]; omega
                  · omega
                rw [testBit_add_bool_mul_pow z0.isLt b ((i.val + p.val) % n)]
                simp only [hlt_t, ↓reduceIte]
              rw [hfeq]; exact hz0.2.2.2 i hlt
            · have hieq : i.val = t - d := by omega
              have htm : t - d < m := by omega
              have hifin : i = ⟨t - d, htm⟩ := Fin.ext hieq
              have hfeq : (fun p : Fin (w + 1) => (z0.val + b.toNat * 2 ^ t).testBit ((i.val + p.val) % n)) =
                  (fun p => (2 * h' + c.toNat).testBit (p.val % n)) := by
                funext p
                have hw := hwin_idx p
                rw [hieq, hw.2, testBit_two_mul_add_bool]
                by_cases hr0 : p.val % n = 0
                · simp [hr0, hz_c]
                · simp only [hr0, ↓reduceIte]
                  have hidx : t - d + p.val % n = t + 1 - d + (p.val % n - 1) := by omega
                  rw [hidx, hz_h' (p.val % n - 1) (by omega)]
              rw [hfeq, hifin]
              simp [ok, htm] at hok; exact hok.2
        · apply Fin.ext; dsimp only
          rw [mul_comm b.toNat (2 ^ t), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z0.isLt]
  have h0c : h0 + false.toNat = h0 := rfl
  have h1c : h0 + true.toNat = h1 := rfl
  rw [hpart, hbr false, hbr true, h0c, h1c]

private theorem dpos_size_coeff (n : Nat) :
    n + n * (2 + 11 * (n + 1)) + (2 * n + 1) + 9 * (n + 1) ≤ 16 * (n + 1) ^ 2 := by
  nlinarith

private theorem buildDPos_spec {n m w : Nat} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (hd_pos : 0 < min w (n - 1)) :
    let tableInputs := m * 2 ^ (w + 1)
    let inputs := tableInputs + 2 * n
    let d := min w (n - 1)
    let r := buildDPos n m w
    GoodGates inputs r.1 ∧
    r.1.length ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
    r.2.length = n + 1 ∧ (∀ w' ∈ r.2, w' < inputs + r.1.length) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      decodeNum wiresIn r.1 r.2 = sols.card := by
  intro tableInputs inputs d
  have hinputs : inputs = m * 2 ^ (w + 1) + 2 * n := rfl
  set e := m + d - n
  have hd_lt_n : d < n := by omega
  have he_le_d : e ≤ d := by omega
  have he_le_n : e ≤ n := by omega
  let rF := addFalse inputs []
  let rT := addTrue inputs rF.1
  have hF := addFalse_spec (GoodGates_nil inputs)
  have hT := addTrue_spec hF.2.2.1
  have hFLen : rF.1.length = 1 := hF.2.1
  have hTLen : rT.1.length = 2 := by rw [show rT.1.length = rF.1.length + 1 from hT.2.1, hFLen]
  have hFT : Extends rF.1 rT.1 := hT.1
  have hwf_F : rF.2 < inputs + rF.1.length := hF.2.2.2.1
  have hwt_T : rT.2 < inputs + rT.1.length := hT.2.2.2.1
  have hInit := buildInitFlags_spec hn hm hd_lt_n hT.2.2.1 hT.2.2.2.1 (2 ^ d)
  set rInit := buildInitFlags inputs m w d rT.2 rT.1 (2 ^ d)
  have hInitLen : rInit.1.length = 2 + 2 ^ d * d := by rw [hInit.2.1, hTLen]
  let zeroCnt := List.replicate (n + 1) rF.2
  let initTable : Nat → Nat → List Nat := fun α h =>
    if h % 2 ^ e = α then rInit.2 h :: List.replicate n rF.2 else zeroCnt
  let pairs := allPairs e d
  have hpairs_len : pairs.length = 2 ^ (d + e) := allPairs_len e d
  have h2d_le : 2 ^ d ≤ 2 ^ (d + e) := Nat.pow_le_pow_right (by omega) (by omega)
  -- Prefix solution count function (bound to top-level prefCount)
  let prefCount' := prefCount n m w d e
  -- DP step loop spec
  have hstepLoop_spec : ∀ (t : Nat), d ≤ t → t < n →
      ∀ (gs : List Gate) (prevCnt : Nat → Nat → List Nat),
        Extends rInit.1 gs → GoodGates inputs gs →
        (∀ α < 2 ^ e, ∀ h < 2 ^ d, (prevCnt α h).length = n + 1 ∧ ∀ u ∈ prevCnt α h, u < inputs + gs.length) →
        ∀ (L : List (Nat × Nat)), L.Nodup → (∀ p ∈ L, p.1 < 2 ^ e ∧ p.2 < 2 ^ d) →
          let res := buildDPStepLoop inputs n m w d rF.2 t prevCnt gs L
          Extends gs res.1 ∧
          res.1.length ≤ gs.length + L.length * (2 + 11 * (n + 1)) ∧
          GoodGates inputs res.1 ∧
          (∀ p ∈ L, (res.2 p.1 p.2).length = n + 1 ∧ ∀ u ∈ res.2 p.1 p.2, u < inputs + res.1.length) ∧
          ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
            let wiresIn := List.ofFn (fun a : Fin inputs =>
              if a.val < tableInputs then
                table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
                  (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
              else
                let t' := a.val - tableInputs
                allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
            (∀ α < 2 ^ e, ∀ h < 2 ^ d, decodeNum wiresIn gs (prevCnt α h) = prefCount' table allow t α h) →
            ∀ p ∈ L, decodeNum wiresIn res.1 (res.2 p.1 p.2) = prefCount' table allow (t + 1) p.1 p.2 := by
    intro t ht1 ht2 gs prevCnt hExtInit hgg hprev L
    induction L generalizing gs with
    | nil =>
      intro _ _
      refine ⟨Extends_refl gs, by simp [buildDPStepLoop], hgg, fun _ h => (by cases h),
        fun _ _ _ _ h => (by cases h)⟩
    | cons p rest ih =>
      intro hnd hmem
      rcases p with ⟨α, h'⟩
      rw [List.nodup_cons] at hnd
      have hp_b := hmem (α, h') (List.mem_cons_self ..)
      dsimp only at hp_b
      have hrest_b : ∀ q ∈ rest, q.1 < 2 ^ e ∧ q.2 < 2 ^ d := fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      simp only [buildDPStepLoop]
      set b := h'.testBit (d - 1)
      set h0 := (2 * h') % 2 ^ d
      set h1 := h0 + 1
      have hh0_lt : h0 < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
      have hh1_lt : h1 < 2 ^ d := by
        have h2d : 2 ∣ 2 ^ d := by
          have : d = (d - 1) + 1 := by omega
          rw [this, Nat.pow_succ]; exact dvd_mul_left 2 _
        have heven : h0 % 2 = 0 := by
          rcases h2d with ⟨q, hq⟩
          have hdiv := Nat.div_add_mod (2 * h') (2 ^ d)
          have hmul : 2 * (q * (2 * h' / 2 ^ d)) + h0 = 2 * h' := by
            dsimp only [h0]; rw [← mul_assoc, ← hq]; exact hdiv
          omega
        omega
      have hwf_gs : rF.2 < inputs + gs.length := by
        have := Extends_len hFT; have := Extends_len hInit.1; have := Extends_len hExtInit; omega
      -- Emit flags (0 or 2 gates)
      have hFlags :
          let rFls : List Gate × Nat × Nat :=
            if t - d < m then
              let r0 := addAnd inputs gs (allowWire m w t b) (tableWire w (t - d) (dpWindowPat n w h' false))
              let r1 := addAnd inputs r0.1 (allowWire m w t b) (tableWire w (t - d) (dpWindowPat n w h' true))
              (r1.1, r0.2, r1.2)
            else
              (gs, allowWire m w t b, allowWire m w t b)
          Extends gs rFls.1 ∧ rFls.1.length ≤ gs.length + 2 ∧ GoodGates inputs rFls.1 ∧
          rFls.2.1 < inputs + rFls.1.length ∧ rFls.2.2 < inputs + rFls.1.length ∧
          ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
            let wiresIn := List.ofFn (fun a : Fin inputs =>
              if a.val < tableInputs then
                table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
                  (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
              else
                let t' := a.val - tableInputs
                allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
            wireVal wiresIn rFls.1 rFls.2.1 =
              (if htm : t - d < m then allow ⟨t, ht2⟩ b && table ⟨t - d, htm⟩ (fun p => (2 * h' + false.toNat).testBit (p.val % n))
               else allow ⟨t, ht2⟩ b) ∧
            wireVal wiresIn rFls.1 rFls.2.2 =
              (if htm : t - d < m then allow ⟨t, ht2⟩ b && table ⟨t - d, htm⟩ (fun p => (2 * h' + true.toNat).testBit (p.val % n))
               else allow ⟨t, ht2⟩ b) := by
        by_cases htm : t - d < m
        · simp only [htm, ↓reduceIte, ↓reduceDIte]
          have ha_lt : allowWire m w t b < inputs + gs.length := by
            have := allowWire_lt (n := n) (m := m) (w := w) (j := t) ht2 b; rw [hinputs]; omega
          have ht0_lt : tableWire w (t - d) (dpWindowPat n w h' false) < inputs + gs.length := by
            have := tableWire_lt (n := n) (m := m) (w := w) (i := t - d) (pat := dpWindowPat n w h' false) htm (packBits_lt (w + 1) _); rw [hinputs]; omega
          have ht1_lt : tableWire w (t - d) (dpWindowPat n w h' true) < inputs + gs.length := by
            have := tableWire_lt (n := n) (m := m) (w := w) (i := t - d) (pat := dpWindowPat n w h' true) htm (packBits_lt (w + 1) _); rw [hinputs]; omega
          have hr0 := addAnd_spec hgg ha_lt ht0_lt
          rcases hr0 with ⟨he0, hl0, hg0, hw0, hv0⟩
          have hr1 := addAnd_spec (a := allowWire m w t b) (b := tableWire w (t - d) (dpWindowPat n w h' true))
            hg0 (by omega) (by omega)
          rcases hr1 with ⟨he1, hl1, hg1, hw1, hv1⟩
          refine ⟨Extends_trans he0 he1, by omega, hg1, by omega, hw1, ?_⟩
          intro table allow
          let wiresIn := List.ofFn (fun a : Fin inputs =>
            if a.val < tableInputs then
              table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
                (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
            else
              let t' := a.val - tableInputs
              allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
          have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
          have hp0 : (fun p : Fin (w + 1) => (dpWindowPat n w h' false).testBit p.val) =
              (fun p => (2 * h' + false.toNat).testBit (p.val % n)) := by
            funext p; unfold dpWindowPat; rw [packBits_testBit]; simp [p.isLt]
          have hp1 : (fun p : Fin (w + 1) => (dpWindowPat n w h' true).testBit p.val) =
              (fun p => (2 * h' + true.toNat).testBit (p.val % n)) := by
            funext p; unfold dpWindowPat; rw [packBits_testBit]; simp [p.isLt]
          constructor
          · rw [wireVal_extends he1 (by rw [List.length_ofFn]; exact hw0), hv0 wiresIn hlen_x,
                wireVal_allowWire hn hm ht2 b table allow,
                wireVal_tableWire hn hm htm (pat := dpWindowPat n w h' false) (packBits_lt (w + 1) _) table allow, hp0]
          · rw [hv1 wiresIn hlen_x,
                wireVal_allowWire hn hm ht2 b table allow,
                wireVal_tableWire hn hm htm (pat := dpWindowPat n w h' true) (packBits_lt (w + 1) _) table allow, hp1]
        · simp only [htm, ↓reduceIte, ↓reduceDIte]
          have ha_lt : allowWire m w t b < inputs + gs.length := by
            have := allowWire_lt (n := n) (m := m) (w := w) (j := t) ht2 b; rw [hinputs]; omega
          refine ⟨Extends_refl gs, by omega, hgg, ha_lt, ha_lt, ?_⟩
          intro table allow
          exact ⟨wireVal_allowWire hn hm ht2 b table allow gs, wireVal_allowWire hn hm ht2 b table allow gs⟩
      set rFls : List Gate × Nat × Nat :=
        if t - d < m then
          let r0 := addAnd inputs gs (allowWire m w t b) (tableWire w (t - d) (dpWindowPat n w h' false))
          let r1 := addAnd inputs r0.1 (allowWire m w t b) (tableWire w (t - d) (dpWindowPat n w h' true))
          (r1.1, r0.2, r1.2)
        else
          (gs, allowWire m w t b, allowWire m w t b)
      rcases hFlags with ⟨heF, hlF, hgF, hf0_lt, hf1_lt, hvF⟩
      have hcnt0 := hprev α hp_b.1 h0 hh0_lt
      have hcnt1 := hprev α hp_b.1 h1 hh1_lt
      have hcnt0' : ∀ u ∈ prevCnt α h0, u < inputs + rFls.1.length := fun u hu => by
        have := hcnt0.2 u hu; have := Extends_len heF; omega
      have hcnt1' : ∀ u ∈ prevCnt α h1, u < inputs + rFls.1.length := fun u hu => by
        have := hcnt1.2 u hu; have := Extends_len heF; omega
      have hwf_F : rF.2 < inputs + rFls.1.length := by have := Extends_len heF; omega
      have hMA := emitMaskAdd_spec hgF hwf_F hf0_lt hf1_lt (by omega) hcnt0' hcnt1'
      set rAdd := emitMaskAdd inputs rFls.1 rF.2 rFls.2.1 (prevCnt α h0) rFls.2.2 (prevCnt α h1)
      rcases hMA with ⟨heMA, hlMA, hgMA, hlenMA, hwsMA, hvMA⟩
      have hprev_ext : ∀ α' < 2 ^ e, ∀ h'' < 2 ^ d,
          (prevCnt α' h'').length = n + 1 ∧ ∀ u ∈ prevCnt α' h'', u < inputs + rAdd.1.length := by
        intro α' hα' h'' hh''
        have hp := hprev α' hα' h'' hh''
        exact ⟨hp.1, fun u hu => by have := hp.2 u hu; have := Extends_len heF; have := Extends_len heMA; omega⟩
      have hRest := ih rAdd.1 (Extends_trans hExtInit (Extends_trans heF heMA)) hgMA hprev_ext hnd.2 hrest_b
      set rRest := buildDPStepLoop inputs n m w d rF.2 t prevCnt rAdd.1 rest
      rcases hRest with ⟨heR, hlR, hgR, hrestW, hrestV⟩
      refine ⟨Extends_trans heF (Extends_trans heMA heR),
        by simp only [List.length_cons]; rw [hcnt0.1] at hlMA; nlinarith, hgR, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hqr
        · simp only [and_self, ↓reduceIte]
          exact ⟨by omega, fun u hu => by have := hwsMA u hu; have := Extends_len heR; omega⟩
        · have hne : ¬ (q.1 = α ∧ q.2 = h') := by
            rintro ⟨h1q, h2q⟩
            apply hnd.1
            have : q = (α, h') := Prod.ext h1q h2q
            rwa [← this]
          simp only [hne, ↓reduceIte]
          exact hrestW q hqr
      · intro table allow hprev_val q hq
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
        rcases List.mem_cons.mp hq with rfl | hqr
        · simp only [and_self, ↓reduceIte]
          rw [decodeNum_extends heR (fun u hu => by rw [List.length_ofFn]; exact hwsMA u hu)]
          have hwf_v : wireVal wiresIn rFls.1 rF.2 = false := by
            rw [wireVal_extends (Extends_trans hFT (Extends_trans hInit.1 (Extends_trans hExtInit heF)))
              (by omega), hF.2.2.2.2 wiresIn hlen_x]
          rw [hvMA wiresIn hlen_x hwf_v, hcnt0.1,
              decodeNum_extends heF (fun u hu => by rw [List.length_ofFn]; exact hcnt0.2 u hu),
              decodeNum_extends heF (fun u hu => by rw [List.length_ofFn]; exact hcnt1.2 u hu),
              hprev_val α hp_b.1 h0 hh0_lt, hprev_val α hp_b.1 h1 hh1_lt,
              (hvF table allow).1, (hvF table allow).2]
          have hcomb := dp_step_comb (d := d) (e := e) (α := α) (h' := h') hn hd_pos rfl he_le_d ht1 ht2 table allow
          dsimp only [prefCount'] at hcomb ⊢
          rw [← hcomb]
          apply Nat.mod_eq_of_lt
          have hcard_le : prefCount n m w d e table allow (t + 1) α h' ≤ 2 ^ (t + 1) := by
            unfold prefCount
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          have hpow_le : 2 ^ (t + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
          have hlt2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
          omega
        · have hne : ¬ (q.1 = α ∧ q.2 = h') := by
            rintro ⟨h1q, h2q⟩; apply hnd.1; have : q = (α, h') := Prod.ext h1q h2q; rwa [← this]
          simp only [hne, ↓reduceIte]
          apply hrestV table allow
          · intro α' hα' h'' hh''
            rw [decodeNum_extends (Extends_trans heF heMA)
              (fun u hu => by rw [List.length_ofFn]; exact (hprev α' hα' h'' hh'').2 u hu)]
            exact hprev_val α' hα' h'' hh''
          · exact hqr
  -- Induction over stepIdx <= n - d
  have hDP_ind : ∀ s, s ≤ n - d →
      let st := (List.range s).foldl
        (fun (st : List Gate × (Nat → Nat → List Nat)) stepIdx =>
          buildDPStepLoop inputs n m w d rF.2 (d + stepIdx) st.2 st.1 pairs)
        (rInit.1, initTable)
      Extends rInit.1 st.1 ∧
      st.1.length ≤ rInit.1.length + s * pairs.length * (2 + 11 * (n + 1)) ∧
      GoodGates inputs st.1 ∧
      (∀ α < 2 ^ e, ∀ h < 2 ^ d, (st.2 α h).length = n + 1 ∧ ∀ u ∈ st.2 α h, u < inputs + st.1.length) ∧
      ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        ∀ α < 2 ^ e, ∀ h < 2 ^ d, decodeNum wiresIn st.1 (st.2 α h) = prefCount' table allow (d + s) α h := by
    intro s
    induction s with
    | zero =>
      intro _
      have hwf_init : rF.2 < inputs + rInit.1.length := by
        have := Extends_len hFT; have := Extends_len hInit.1; omega
      refine ⟨Extends_refl rInit.1, by simp, hInit.2.2.1, ?_, ?_⟩
      · intro α _ h hh
        simp only [List.range_zero, List.foldl_nil, initTable]
        split
        · refine ⟨by simp, fun u hu => ?_⟩
          simp only [List.mem_cons, List.mem_replicate] at hu
          rcases hu with rfl | ⟨_, rfl⟩
          · exact hInit.2.2.2.1 h hh
          · exact hwf_init
        · exact ⟨by simp [zeroCnt], fun u hu => by simp [zeroCnt] at hu; subst hu; exact hwf_init⟩
      · intro table allow wiresIn α hα h hh
        have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
        have hwf_v : wireVal wiresIn rInit.1 rF.2 = false := by
          rw [wireVal_extends (Extends_trans hFT hInit.1) (by omega),
              hF.2.2.2.2 wiresIn hlen_x]
        have hwt_v : wireVal wiresIn rT.1 rT.2 = true := hT.2.2.2.2 wiresIn hlen_x
        simp only [List.range_zero, List.foldl_nil, Nat.add_zero, initTable]
        -- Compute prefCount at t = d
        have hpc_d : prefCount' table allow d α h =
            if h % 2 ^ e = α then (wireVal wiresIn rInit.1 (rInit.2 h)).toNat else 0 := by
          unfold prefCount' prefCount
          have hiff := hInit.2.2.2.2 table allow hwt_v h hh
          by_cases hmod : h % 2 ^ e = α
          · simp only [hmod, ↓reduceIte]
            cases hv : wireVal wiresIn rInit.1 (rInit.2 h)
            · simp only [Bool.toNat_false, Finset.card_eq_zero]
              rw [Finset.eq_empty_iff_forall_notMem]
              intro z hz
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
              rcases hz with ⟨_, hz_h, hz_a, _⟩
              have hzeq : z.val = h := by
                apply Nat.eq_of_testBit_eq; intro j
                by_cases hj : j < d
                · have := hz_h j hj; simpa using this
                · rw [testBit_false_of_ge z.isLt (by omega), testBit_false_of_ge hh (by omega)]
              have hall : ∀ j : Fin n, j.val < d → allow j (h.testBit j.val) = true := by
                intro j hj; rw [← hzeq]; exact hz_a j hj
              have := hiff.mpr hall
              rw [hv] at this; cases this
            · simp only [Bool.toNat_true]
              have hall := hiff.mp hv
              have hsing : Finset.univ.filter (fun z : Fin (2 ^ d) =>
                  (∀ j < e, z.val.testBit j = α.testBit j) ∧
                  (∀ j < d, z.val.testBit (d - d + j) = h.testBit j) ∧
                  (∀ j : Fin n, j.val < d → allow j (z.val.testBit j.val) = true) ∧
                  (∀ i : Fin m, i.val + d < d → table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)) =
                  {⟨h, hh⟩} := by
                ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                constructor
                · rintro ⟨_, hz_h, _, _⟩
                  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
                  by_cases hj : j < d
                  · have := hz_h j hj; simpa using this
                  · rw [testBit_false_of_ge z.isLt (by omega), testBit_false_of_ge hh (by omega)]
                · intro hzeq; subst hzeq
                  refine ⟨fun j hj => ?_, fun j _ => by simp, fun j hj => hall j hj, fun i hi => by omega⟩
                  rw [← hmod, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
              rw [hsing, Finset.card_singleton]
          · simp only [hmod, ↓reduceIte, Finset.card_eq_zero]
            rw [Finset.eq_empty_iff_forall_notMem]
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
            rcases hz with ⟨hz_α, hz_h, _, _⟩
            apply hmod
            apply Nat.eq_of_testBit_eq; intro j
            rw [Nat.testBit_mod_two_pow]
            by_cases hj : j < e
            · simp only [decide_eq_true hj, Bool.true_and]
              have h1 := hz_α j hj
              have h2 := hz_h j (by omega)
              simp only [Nat.sub_self, Nat.zero_add] at h2
              rw [← h2, h1]
            · simp only [decide_eq_false hj, Bool.false_and]
              exact (testBit_false_of_ge hα (by omega)).symm
        rw [hpc_d]
        by_cases hmod : h % 2 ^ e = α
        · simp [hmod, decodeNum, decodeNum_replicate_false hwf_v]
        · simp [hmod, zeroCnt, decodeNum_replicate_false hwf_v]
    | succ s ih =>
      intro hs
      rcases ih (by omega) with ⟨hext, hlen_g, hgg, hcnt, hval⟩
      set st := (List.range s).foldl
        (fun (st : List Gate × (Nat → Nat → List Nat)) stepIdx =>
          buildDPStepLoop inputs n m w d rF.2 (d + stepIdx) st.2 st.1 pairs)
        (rInit.1, initTable)
      have hfold : (List.range (s + 1)).foldl
          (fun (st : List Gate × (Nat → Nat → List Nat)) stepIdx =>
            buildDPStepLoop inputs n m w d rF.2 (d + stepIdx) st.2 st.1 pairs)
          (rInit.1, initTable) = buildDPStepLoop inputs n m w d rF.2 (d + s) st.2 st.1 pairs := by
        rw [List.range_succ, List.foldl_append]; rfl
      rw [hfold]
      have hstep := hstepLoop_spec (d + s) (by omega) (by omega) st.1 st.2 hext hgg hcnt pairs
        (allPairs_nodup e d) (fun p hp => allPairs_mem.mp hp)
      rcases hstep with ⟨heS, hlS, hgS, hcntS, hvalS⟩
      refine ⟨Extends_trans hext heS, by nlinarith, hgS,
        fun α hα h hh => hcntS (α, h) (allPairs_mem.mpr ⟨hα, hh⟩), ?_⟩
      intro table allow wiresIn α hα h hh
      have hidx : d + (s + 1) = (d + s) + 1 := by omega
      rw [hidx]
      exact hvalS table allow (hval table allow) (α, h) (allPairs_mem.mpr ⟨hα, hh⟩)
  -- Wrap loop spec
  rcases hDP_ind (n - d) (le_refl _) with ⟨heDP, hlDP, hgDP, hcntDP, hvalDP⟩
  set rDP := (List.range (n - d)).foldl
    (fun (st : List Gate × (Nat → Nat → List Nat)) stepIdx =>
      buildDPStepLoop inputs n m w d rF.2 (d + stepIdx) st.2 st.1 pairs)
    (rInit.1, initTable)
  have hdn_eq : d + (n - d) = n := by omega
  have hwrap_spec : ∀ (gs : List Gate) (L : List (Nat × Nat)),
      Extends rDP.1 gs → GoodGates inputs gs →
      (∀ p ∈ L, p.1 < 2 ^ e ∧ p.2 < 2 ^ d) →
      let res := buildWrapLoop inputs n m w d e rT.2 rDP.2 gs L
      Extends gs res.1 ∧
      res.1.length = gs.length + L.length * (e + (n + 1)) ∧
      GoodGates inputs res.1 ∧
      res.2.length = L.length ∧
      (∀ num ∈ res.2, num.length = n + 1 ∧ ∀ u ∈ num, u < inputs + res.1.length) ∧
      ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        res.2.map (decodeNum wiresIn res.1) = L.map (fun p =>
          if (List.range e).all (fun k =>
            if hk : k < e then
              table ⟨n - d + k, by omega⟩ (fun b =>
                let q := (n - d + k + b.val) % n
                if n - d ≤ q then p.2.testBit (q - (n - d)) else p.1.testBit q)
            else true)
          then prefCount' table allow n p.1 p.2 else 0) := by
    intro gs L
    induction L generalizing gs with
    | nil =>
      intro _ hgg _
      refine ⟨Extends_refl gs, by simp [buildWrapLoop], hgg, by simp [buildWrapLoop],
        fun _ h => (by cases h), fun _ _ => rfl⟩
    | cons p rest ih =>
      intro hext hgg hmem
      rcases p with ⟨α, h⟩
      have hp_b := hmem (α, h) (List.mem_cons_self ..)
      dsimp only at hp_b
      have hrest_b : ∀ q ∈ rest, q.1 < 2 ^ e ∧ q.2 < 2 ^ d := fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      simp only [buildWrapLoop]
      let ws := (List.range e).map (fun k => tableWire w (n - d + k) (dpWrapPat n w d α h (n - d + k)))
      have hwt_gs : rT.2 < inputs + gs.length := by
        have := Extends_len hInit.1; have := Extends_len heDP; have := Extends_len hext; omega
      have hws_lt : ∀ u ∈ ws, u < inputs + gs.length := by
        intro u hu
        simp only [ws, List.mem_map, List.mem_range] at hu
        rcases hu with ⟨k, hk, rfl⟩
        have := tableWire_lt (n := n) (m := m) (w := w) (i := n - d + k) (pat := dpWrapPat n w d α h (n - d + k)) (by omega) (packBits_lt (w + 1) _)
        rw [hinputs]; omega
      have hFl := emitAndList_spec (acc := rT.2) hgg hwt_gs hws_lt
      set rFl := emitAndList inputs gs rT.2 ws
      rcases hFl with ⟨heFl, hlFl, hgFl, hwFl, hvFl⟩
      have hcnt_p := hcntDP α hp_b.1 h hp_b.2
      have hcnt_lt : ∀ u ∈ rDP.2 α h, u < inputs + rFl.1.length := fun u hu => by
        have := hcnt_p.2 u hu; have := Extends_len hext; have := Extends_len heFl; omega
      have hMk := emitMask_spec (flag := rFl.2) hgFl hwFl hcnt_lt
      set rMk := emitMask inputs rFl.1 rFl.2 (rDP.2 α h)
      rcases hMk with ⟨heMk, hlMk, hgMk, hlenMk, hwsMk, hvMk⟩
      have hR := ih rMk.1 (Extends_trans hext (Extends_trans heFl heMk)) hgMk hrest_b
      set rR := buildWrapLoop inputs n m w d e rT.2 rDP.2 rMk.1 rest
      rcases hR with ⟨heR, hlR, hgR, hlenR, hwsR, hvR⟩
      refine ⟨Extends_trans heFl (Extends_trans heMk heR),
        by simp only [List.length_cons]; rw [hlR, hlMk, hlFl, hcnt_p.1]; simp [ws]; ring,
        hgR, by simp [hlenR], ?_, ?_⟩
      · intro num hnum
        rcases List.mem_cons.mp hnum with rfl | hnr
        · exact ⟨by omega, fun u hu => by have := hwsMk u hu; have := Extends_len heR; omega⟩
        · exact hwsR num hnr
      · intro table allow
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t' := a.val - tableInputs
            allow ⟨(t' / 2) % n, Nat.mod_lt _ hn⟩ (decide (t' % 2 = 1)))
        have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
        simp only [List.map_cons]
        congr 1
        · rw [decodeNum_extends heR (fun u hu => by rw [List.length_ofFn]; exact hwsMk u hu),
              hvMk wiresIn hlen_x, hvFl wiresIn hlen_x,
              wireVal_extends (Extends_trans hInit.1 (Extends_trans heDP hext)) (by rw [List.length_ofFn]; exact hwt_T),
              hT.2.2.2.2 wiresIn hlen_x, Bool.true_and,
              decodeNum_extends (Extends_trans hext heFl) (fun u hu => by rw [List.length_ofFn]; exact hcnt_p.2 u hu),
              hvalDP table allow α hp_b.1 h hp_b.2, hdn_eq]
          have hall_eq : ws.all (wireVal wiresIn gs) =
              (List.range e).all (fun k =>
                if hk : k < e then
                  table ⟨n - d + k, by omega⟩ (fun b =>
                    let q := (n - d + k + b.val) % n
                    if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q)
                else true) := by
            simp only [ws, List.all_map]
            rw [Bool.eq_iff_iff]
            simp only [List.all_eq_true, List.mem_range]
            constructor
            · intro hall k hk
              have hv := hall k hk
              dsimp only [Function.comp] at hv
              rw [wireVal_tableWire hn hm (by omega : n - d + k < m) (pat := dpWrapPat n w d α h (n - d + k)) (packBits_lt (w + 1) _) table allow] at hv
              simp only [hk, ↓reduceDIte]
              have hfeq : (fun b : Fin (w + 1) => (dpWrapPat n w d α h (n - d + k)).testBit b.val) =
                  (fun b : Fin (w + 1) =>
                    let q := (n - d + k + b.val) % n
                    if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q) := by
                funext b; unfold dpWrapPat; rw [packBits_testBit]; simp [b.isLt]
              rw [← hfeq]; exact hv
            · intro hall k hk
              have hv := hall k hk
              simp only [hk, ↓reduceDIte] at hv
              dsimp only [Function.comp]
              rw [wireVal_tableWire hn hm (by omega : n - d + k < m) (pat := dpWrapPat n w d α h (n - d + k)) (packBits_lt (w + 1) _) table allow]
              have hfeq : (fun b : Fin (w + 1) => (dpWrapPat n w d α h (n - d + k)).testBit b.val) =
                  (fun b : Fin (w + 1) =>
                    let q := (n - d + k + b.val) % n
                    if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q) := by
                funext b; unfold dpWrapPat; rw [packBits_testBit]; simp [b.isLt]
              rw [hfeq]; exact hv
          rw [hall_eq]
        · exact hvR table allow
  -- Final sum over all pairs
  have hW := hwrap_spec rDP.1 pairs (Extends_refl _) hgDP (fun p hp => allPairs_mem.mp hp)
  set rWrap := buildWrapLoop inputs n m w d e rT.2 rDP.2 rDP.1 pairs
  rcases hW with ⟨heW, hlW, hgW, hlenW, hwsW, hvW⟩
  have hwf_W : rF.2 < inputs + rWrap.1.length := by
    have := Extends_len hFT; have := Extends_len hInit.1; have := Extends_len heDP; have := Extends_len heW
    omega
  have hSum := emitSumList_spec (wFalse := rF.2) hgW hwf_W hwsW
  rcases hSum with ⟨heS, hlS, hgS, hlenS, hwsS, hvS⟩
  dsimp only [buildDPos]
  refine ⟨hgS, ?_, hlenS, hwsS, ?_⟩
  · -- Gate size bound: <= 16 * (n + 1)^2 * 2^(d + e) + 2
    have hlen_tot : (emitSumList inputs (n + 1) rWrap.1 rF.2 rWrap.2).1.length ≤
        2 + 2 ^ d * d + (n - d) * 2 ^ (d + e) * (2 + 11 * (n + 1)) +
        2 ^ (d + e) * (e + (n + 1)) + 9 * (n + 1) * 2 ^ (d + e) := by
      rw [hlS, hlW, hlenW, hpairs_len]
      rw [hpairs_len, hInitLen] at hlDP
      omega
    have h1 : 2 ^ d * d ≤ n * 2 ^ (d + e) := by
      calc 2 ^ d * d ≤ 2 ^ (d + e) * n := Nat.mul_le_mul h2d_le (by omega)
        _ = n * 2 ^ (d + e) := mul_comm _ _
    have h2 : (n - d) * 2 ^ (d + e) * (2 + 11 * (n + 1)) ≤ n * (2 + 11 * (n + 1)) * 2 ^ (d + e) := by
      have hnd : n - d ≤ n := by omega
      calc (n - d) * 2 ^ (d + e) * (2 + 11 * (n + 1))
          = (n - d) * (2 + 11 * (n + 1)) * 2 ^ (d + e) := by ring
        _ ≤ n * (2 + 11 * (n + 1)) * 2 ^ (d + e) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hnd)
    have h3 : 2 ^ (d + e) * (e + (n + 1)) ≤ (2 * n + 1) * 2 ^ (d + e) := by
      calc 2 ^ (d + e) * (e + (n + 1)) ≤ 2 ^ (d + e) * (2 * n + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (2 * n + 1) * 2 ^ (d + e) := mul_comm _ _
    have hcomb : n * 2 ^ (d + e) + n * (2 + 11 * (n + 1)) * 2 ^ (d + e) +
        (2 * n + 1) * 2 ^ (d + e) + 9 * (n + 1) * 2 ^ (d + e) ≤
        16 * (n + 1) ^ 2 * 2 ^ (d + e) := by
      calc n * 2 ^ (d + e) + n * (2 + 11 * (n + 1)) * 2 ^ (d + e) +
            (2 * n + 1) * 2 ^ (d + e) + 9 * (n + 1) * 2 ^ (d + e)
          = (n + n * (2 + 11 * (n + 1)) + (2 * n + 1) + 9 * (n + 1)) * 2 ^ (d + e) := by ring
        _ ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) := Nat.mul_le_mul_right (2 ^ (d + e)) (dpos_size_coeff n)
    change (emitSumList inputs (n + 1) rWrap.1 rF.2 rWrap.2).1.length ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) + 2
    omega
  · -- Semantics: sum over all (α, h) equals sols.card
    intro table allow
    let wiresIn := List.ofFn (fun a : Fin inputs =>
      if a.val < tableInputs then
        table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
          (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
      else
        let t := a.val - tableInputs
        allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
    let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
      (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
      ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
    have hlen_x : wiresIn.length = inputs := by simp [wiresIn]
    have hwf_v : wireVal wiresIn rWrap.1 rF.2 = false := by
      rw [wireVal_extends (Extends_trans hFT (Extends_trans hInit.1 (Extends_trans heDP heW)))
        (by omega), hF.2.2.2.2 wiresIn hlen_x]
    rw [hvS wiresIn hlen_x hwf_v, hvW table allow]
    -- Show the list sum equals sols.card
    have hsum_eq : (pairs.map (fun p =>
        if (List.range e).all (fun k =>
          if hk : k < e then
            table ⟨n - d + k, by omega⟩ (fun b =>
              let q := (n - d + k + b.val) % n
              if n - d ≤ q then p.2.testBit (q - (n - d)) else p.1.testBit q)
          else true)
        then prefCount' table allow n p.1 p.2 else 0)).sum = sols.card := by
      -- Partition sols by (z % 2^e, z >>> (n - d))
      let keyOf : Fin (2 ^ n) → Nat × Nat := fun z => (z.val % 2 ^ e, z.val >>> (n - d))
      have hkey_mem : ∀ z : Fin (2 ^ n), keyOf z ∈ pairs.toFinset := by
        intro z
        rw [List.mem_toFinset, allPairs_mem]
        refine ⟨Nat.mod_lt _ (Nat.two_pow_pos e), ?_⟩
        rw [Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ n = 2 ^ (n - d) * 2 ^ d := by rw [← Nat.pow_add]; congr 1; omega
        have hz : z.val < 2 ^ (n - d) * 2 ^ d := by rw [← hpow]; exact z.isLt
        exact Nat.div_lt_of_lt_mul hz
      have hfib : ∀ p ∈ pairs,
          (sols.filter (fun z => keyOf z = p)).card =
          if (List.range e).all (fun k =>
            if hk : k < e then
              table ⟨n - d + k, by omega⟩ (fun b =>
                let q := (n - d + k + b.val) % n
                if n - d ≤ q then p.2.testBit (q - (n - d)) else p.1.testBit q)
            else true)
          then prefCount' table allow n p.1 p.2 else 0 := by
        intro p hp
        rcases p with ⟨α, h⟩
        have hpb := allPairs_mem.mp hp
        have hkey_iff : ∀ z : Fin (2 ^ n), keyOf z = (α, h) ↔
            (∀ j < e, z.val.testBit j = α.testBit j) ∧
            (∀ j < d, z.val.testBit (n - d + j) = h.testBit j) := by
          intro z
          constructor
          · intro hkeq
            have h1 : z.val % 2 ^ e = α := congrArg Prod.fst hkeq
            have h2 : z.val >>> (n - d) = h := congrArg Prod.snd hkeq
            refine ⟨fun j hj => ?_, fun j hj => ?_⟩
            · rw [← h1, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
            · rw [← h2, Nat.testBit_shiftRight]
          · rintro ⟨h1, h2⟩
            apply Prod.ext
            · apply Nat.eq_of_testBit_eq; intro j
              rw [Nat.testBit_mod_two_pow]
              by_cases hj : j < e
              · simp only [decide_eq_true hj, Bool.true_and]; exact h1 j hj
              · simp only [decide_eq_false hj, Bool.false_and]
                exact (testBit_false_of_ge hpb.1 (by omega)).symm
            · apply Nat.eq_of_testBit_eq; intro j
              rw [Nat.testBit_shiftRight]
              by_cases hj : j < d
              · exact h2 j hj
              · rw [testBit_false_of_ge z.isLt (by omega), testBit_false_of_ge hpb.2 (by omega)]
        have hwrap_bit : ∀ z : Fin (2 ^ n), keyOf z = (α, h) →
            ∀ k < e, ∀ b : Fin (w + 1),
              z.val.testBit ((n - d + k + b.val) % n) =
                (let q := (n - d + k + b.val) % n
                 if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q) := by
          intro z hz k hk b
          have hbits := (hkey_iff z).mp hz
          set q := (n - d + k + b.val) % n
          have hq_lt : q < n := Nat.mod_lt _ hn
          by_cases hge : n - d ≤ q
          · simp only [hge, ↓reduceIte]
            have hidx : n - d + (q - (n - d)) = q := by omega
            have := hbits.2 (q - (n - d)) (by omega)
            rw [hidx] at this; exact this
          · simp only [hge, ↓reduceIte]
            -- Must have q < e!
            have hbn : b.val % n ≤ d := by
              by_cases hwn : w ≤ n - 1
              · have : b.val < n := by omega
                rw [Nat.mod_eq_of_lt this]; omega
              · have := Nat.mod_lt b.val hn; omega
            have hq_eq : q = (n - d + k + b.val % n) % n := by
              dsimp only [q]
              symm
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hq_lt_e : q < e := by
              have hsum_ge : n ≤ n - d + k + b.val % n := by
                by_contra hlt
                have : q = n - d + k + b.val % n := by rw [hq_eq, Nat.mod_eq_of_lt (by omega)]
                omega
              have hsum_lt : n - d + k + b.val % n < n + e := by omega
              have hsub : n - d + k + b.val % n = (n - d + k + b.val % n - n) + n := by omega
              rw [hq_eq, hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              omega
            exact hbits.1 q hq_lt_e
        split
        · rename_i hwrap_ok
          rw [List.all_eq_true] at hwrap_ok
          unfold prefCount' prefCount
          congr 1; ext z
          simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hkey_iff z]
          constructor
          · rintro ⟨⟨ha, ht⟩, ⟨h1, h2⟩⟩
            exact ⟨h1, h2, fun j _ => ha j, fun i _ => ht i⟩
          · rintro ⟨h1, h2, ha, ht⟩
            refine ⟨⟨fun j => ha j j.isLt, fun i => ?_⟩, h1, h2⟩
            by_cases hi : i.val + d < n
            · exact ht i hi
            · have hk_lt : i.val - (n - d) < e := by omega
              have hok := hwrap_ok (i.val - (n - d)) (List.mem_range.mpr hk_lt)
              simp only [hk_lt, ↓reduceDIte] at hok
              have hi_eq : n - d + (i.val - (n - d)) = i.val := by omega
              have hfin : (⟨n - d + (i.val - (n - d)), by omega⟩ : Fin m) = i := Fin.ext hi_eq
              rw [hfin] at hok
              have hfeq : (fun b : Fin (w + 1) => z.val.testBit ((i.val + b.val) % n)) =
                  (fun b : Fin (w + 1) =>
                    let q := (n - d + (i.val - (n - d)) + b.val) % n
                    if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q) := by
                funext b
                conv_lhs => rw [← hi_eq]
                exact hwrap_bit z ((hkey_iff z).mpr ⟨h1, h2⟩) (i.val - (n - d)) hk_lt b
              rw [hfeq]; exact hok
        · rename_i hwrap_bad
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro z hz
          simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          rcases hz with ⟨⟨_, ht⟩, hkz⟩
          apply hwrap_bad
          rw [List.all_eq_true]
          intro k hk
          rw [List.mem_range] at hk
          simp only [hk, ↓reduceDIte]
          have hti := ht ⟨n - d + k, by omega⟩
          have hfeq : (fun b : Fin (w + 1) =>
              let q := (n - d + k + b.val) % n
              if n - d ≤ q then h.testBit (q - (n - d)) else α.testBit q) =
              (fun b : Fin (w + 1) => z.val.testBit ((n - d + k + b.val) % n)) := by
            funext b; exact (hwrap_bit z hkz k hk b).symm
          rw [hfeq]; exact hti
      have hlist_finset : (pairs.map (fun p =>
          if (List.range e).all (fun k =>
            if hk : k < e then
              table ⟨n - d + k, by omega⟩ (fun b =>
                let q := (n - d + k + b.val) % n
                if n - d ≤ q then p.2.testBit (q - (n - d)) else p.1.testBit q)
            else true)
          then prefCount' table allow n p.1 p.2 else 0)).sum =
          ∑ p ∈ pairs.toFinset, (sols.filter (fun z => keyOf z = p)).card := by
        rw [← List.sum_toFinset _ (allPairs_nodup e d)]
        apply Finset.sum_congr rfl
        intro p hp
        exact (hfib p (List.mem_toFinset.mp hp)).symm
      rw [hlist_finset]
      have hpart_sols : sols.card = ∑ p ∈ pairs.toFinset, (sols.filter (fun z => keyOf z = p)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext z; simp only [Finset.mem_biUnion, Finset.mem_filter]
          exact ⟨fun hz => ⟨keyOf z, hkey_mem z, hz, rfl⟩, fun ⟨_, _, hz, _⟩ => hz⟩
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]; intro z hz1 hz2
          simp only [Finset.mem_filter] at hz1 hz2
          exact hne (hz1.2.symm.trans hz2.2)
      exact hpart_sols.symm
    rw [hsum_eq]
    apply Nat.mod_eq_of_lt
    have hcard_le : sols.card ≤ 2 ^ n := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have hlt2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

-- Main theorem packaged inside namespace

private theorem main_thm (n m w : Nat) (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) :
    let tableInputs := m * 2 ^ (w + 1)
    let inputs := tableInputs + 2 * n
    let d := min w (n - 1)
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin (n + 1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
      C.output = outBit 0 ∧ (∀ j, outBit j < inputs + C.size) ∧
      ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t := a.val - tableInputs
            allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
        let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
          (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
          ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
        ∀ b : Fin (n + 1), (C.wires wiresIn).getD (outBit b) false = sols.card.testBit b.val := by
  intro tableInputs inputs d
  have hbuild : ∃ (gs : List Gate) (cnt : List Nat),
      GoodGates inputs gs ∧
      gs.length ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
      cnt.length = n + 1 ∧ (∀ u ∈ cnt, u < inputs + gs.length) ∧
      ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
        let wiresIn := List.ofFn (fun a : Fin inputs =>
          if a.val < tableInputs then
            table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
              (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
          else
            let t := a.val - tableInputs
            allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
        let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
          (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
          ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
        decodeNum wiresIn gs cnt = sols.card := by
    by_cases hd0 : d = 0
    · refine ⟨(buildD0 n m w).1, (buildD0 n m w).2, ?_⟩
      simpa [hd0] using buildD0_spec hn hm hmn hd0
    · refine ⟨(buildDPos n m w).1, (buildDPos n m w).2, ?_⟩
      exact buildDPos_spec hn hm hmn (by omega)
  rcases hbuild with ⟨gs, cnt, hgg, hlen_g, hlen_c, hws_c, hval⟩
  let outBit : Fin (n + 1) → Nat := fun b => cnt.getD b.val 0
  let C : Circuit := ⟨gs, outBit 0⟩
  refine ⟨C, outBit, hgg.1, hgg.2, hlen_g, rfl, ?_, ?_⟩
  · intro j
    have hmem : cnt.getD j.val 0 ∈ cnt := by
      have hlt : j.val < cnt.length := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.getElem_mem hlt
    exact hws_c _ hmem
  · intro table allow wiresIn sols b
    have hd := decodeNum_testBit wiresIn gs cnt b.val
    rw [hval table allow] at hd
    have hlt : b.val < cnt.length := by omega
    simp only [hlt, ↓reduceIte] at hd
    exact hd.symm

end PEqualNP.Outside.L_clb_045

theorem PEqualNP.Outside.L_clb_045 : ∀ (n m w : Nat) (hn : 0 < n) (hm : 0 < m), m ≤ n →
  let tableInputs := m * 2 ^ (w + 1)
  let inputs := tableInputs + 2 * n
  let d := min w (n - 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin (n + 1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
    C.output = outBit 0 ∧ (∀ j, outBit j < inputs + C.size) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      ∀ b : Fin (n + 1), (C.wires wiresIn).getD (outBit b) false = sols.card.testBit b.val :=
  PEqualNP.Outside.L_clb_045.main_thm
