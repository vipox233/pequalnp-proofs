import PEqualNP.Defs
import PEqualNP.Library.Helpers.MarkedInversionRank

namespace PEqualNP.Outside.L_meta_53175_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket PEqualNP.MarkedInversionRank

-- 1. Straight-line circuit builder with NOT-count tracking

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

structure Builder where
  nIn : ℕ
  gatesRev : List Gate

def Builder.gates (b : Builder) : List Gate := b.gatesRev.reverse
def Builder.nextWire (b : Builder) : ℕ := b.nIn + b.gatesRev.length
def Builder.toCircuit (b : Builder) (out : ℕ) : Circuit := ⟨b.gates, out⟩
def Builder.wireVal (b : Builder) (x : List Bool) (w : ℕ) : Bool :=
  ((b.toCircuit 0).wires x).getD w false

def Builder.Valid (b : Builder) : Prop :=
  FanInTwo (b.toCircuit 0) ∧ ReadsBack b.nIn (b.toCircuit 0)

def Builder.init (nIn : ℕ) : Builder := ⟨nIn, []⟩

lemma Builder.init_valid (nIn : ℕ) : (Builder.init nIn).Valid := by
  refine ⟨?_, ?_⟩ <;> intro g hg <;> simp [Builder.init, Builder.toCircuit, Builder.gates] at hg

lemma Builder.init_notCount (nIn : ℕ) : notCount ((Builder.init nIn).toCircuit 0) = 0 := by
  simp [Builder.init, Builder.toCircuit, Builder.gates, notCount]

lemma Builder.init_wireVal (nIn : ℕ) (x : List Bool) (w : ℕ) :
    (Builder.init nIn).wireVal x w = x.getD w false := by
  simp [Builder.wireVal, Builder.toCircuit, Builder.gates, Builder.init, Circuit.wires]

lemma Builder.wires_length (b : Builder) (x : List Bool) :
    ((b.toCircuit 0).wires x).length = x.length + b.gatesRev.length := by
  have h : ∀ gs : List Gate, ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => simp [Circuit.wires]
    | append_singleton gs g ih =>
      simp [Circuit.wires, List.foldl_append] at ih ⊢
      omega
  simpa [Builder.toCircuit, Builder.gates] using h b.gates

def Builder.emit (b : Builder) (op : GateOp) (inputs : List ℕ) : ℕ × Builder :=
  (b.nextWire, ⟨b.nIn, ⟨op, inputs⟩ :: b.gatesRev⟩)

lemma Builder.emit_valid (b : Builder) (hv : b.Valid) (op : GateOp) (inputs : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : inputs.length ≤ 2) (hrb : ∀ i ∈ inputs, i < b.nextWire) :
    (b.emit op inputs).2.Valid := by
  rcases hv with ⟨hf, hr⟩
  have hgates : (b.emit op inputs).2.gates = b.gates ++ [⟨op, inputs⟩] := by
    simp [Builder.emit, Builder.gates]
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [Builder.toCircuit, hgates, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hf g hg
    · simp at hg; subst hg; exact ⟨hop, hlen⟩
  · intro j hj i hi
    rw [Builder.toCircuit, hgates, List.length_append] at hj
    simp only [List.length_singleton] at hj
    rw [Builder.toCircuit, hgates] at hi
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
    · have hget : gateAt ⟨b.gates ++ [⟨op, inputs⟩], 0⟩ j = gateAt (b.toCircuit 0) j := by
        simp only [gateAt, Builder.toCircuit]
        exact getD_append_left b.gates [⟨op, inputs⟩] j _ hj_lt
      rw [hget] at hi
      exact hr j hj_lt i hi
    · have hget : gateAt ⟨b.gates ++ [⟨op, inputs⟩], 0⟩ b.gates.length = ⟨op, inputs⟩ := by
        simp only [gateAt]
        rw [getD_append_right b.gates [⟨op, inputs⟩] b.gates.length _ le_rfl, Nat.sub_self]
        rfl
      rw [hget] at hi
      have := hrb i hi
      simpa [Builder.emit, Builder.nextWire, Builder.gates] using this

lemma Builder.emit_notCount (b : Builder) (op : GateOp) (inputs : List ℕ) :
    notCount ((b.emit op inputs).2.toCircuit 0) =
      notCount (b.toCircuit 0) + (match op with | .not => 1 | _ => 0) := by
  have hgates : (b.emit op inputs).2.gates = b.gates ++ [⟨op, inputs⟩] := by
    simp [Builder.emit, Builder.gates]
  simp only [notCount, Builder.toCircuit, hgates, List.filter_append, List.length_append]
  cases op <;> simp

lemma Builder.emit_wires (b : Builder) (op : GateOp) (inputs : List ℕ) (x : List Bool) :
    ((b.emit op inputs).2.toCircuit 0).wires x =
      ((b.toCircuit 0).wires x) ++ [op.eval (inputs.map (b.wireVal x))] := by
  have hgates : (b.emit op inputs).2.gates = b.gates ++ [⟨op, inputs⟩] := by
    simp [Builder.emit, Builder.gates]
  simp only [Builder.toCircuit, hgates, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rfl

lemma Builder.emit_wireVal_old (b : Builder) (op : GateOp) (inputs : List ℕ) (x : List Bool)
    (hx : x.length = b.nIn) {w : ℕ} (hw : w < b.nextWire) :
    (b.emit op inputs).2.wireVal x w = b.wireVal x w := by
  have hlen : ((b.toCircuit 0).wires x).length = b.nextWire := by
    rw [b.wires_length, hx, Builder.nextWire]
  unfold Builder.wireVal
  rw [b.emit_wires]
  exact getD_append_left _ _ w false (by omega)

lemma Builder.emit_wireVal_new (b : Builder) (op : GateOp) (inputs : List ℕ) (x : List Bool)
    (hx : x.length = b.nIn) :
    (b.emit op inputs).2.wireVal x b.nextWire = op.eval (inputs.map (b.wireVal x)) := by
  have hlen : ((b.toCircuit 0).wires x).length = b.nextWire := by
    rw [b.wires_length, hx, Builder.nextWire]
  unfold Builder.wireVal
  rw [b.emit_wires, getD_append_right _ _ b.nextWire false (by omega), hlen, Nat.sub_self]
  rfl

def mkNot (b : Builder) (a : ℕ) : ℕ × Builder := b.emit .not [a]
def mkAnd (b : Builder) (a c : ℕ) : ℕ × Builder := b.emit .and [a, c]
def mkOr (b : Builder) (a c : ℕ) : ℕ × Builder := b.emit .or [a, c]

def mkAndListAux (b : Builder) (acc : ℕ) : List ℕ → ℕ × Builder
  | [] => (acc, b)
  | w :: ws => let r := mkAnd b acc w; mkAndListAux r.2 r.1 ws

def mkAndList (b : Builder) (initTrue : ℕ) (ws : List ℕ) : ℕ × Builder :=
  mkAndListAux b initTrue ws

def mkOrListAux (b : Builder) (acc : ℕ) : List ℕ → ℕ × Builder
  | [] => (acc, b)
  | w :: ws => let r := mkOr b acc w; mkOrListAux r.2 r.1 ws

def mkOrList (b : Builder) (initFalse : ℕ) (ws : List ℕ) : ℕ × Builder :=
  mkOrListAux b initFalse ws

lemma mkNot_spec (b : Builder) (hv : b.Valid) (a : ℕ) (ha : a < b.nextWire)
    (x : List Bool) (hx : x.length = b.nIn) :
    (mkNot b a).2.Valid ∧ (mkNot b a).1 = b.nextWire ∧ (mkNot b a).2.nextWire = b.nextWire + 1 ∧
    (mkNot b a).2.nIn = b.nIn ∧
    notCount ((mkNot b a).2.toCircuit 0) = notCount (b.toCircuit 0) + 1 ∧
    (∀ i < b.nextWire, (mkNot b a).2.wireVal x i = b.wireVal x i) ∧
    (mkNot b a).2.wireVal x (mkNot b a).1 = !(b.wireVal x a) := by
  refine ⟨b.emit_valid hv .not [a] (by simp) (by simp) (by simpa using ha),
    rfl, by simp [mkNot, Builder.emit, Builder.nextWire]; omega, rfl,
    by simpa [mkNot] using b.emit_notCount .not [a],
    fun i hi => b.emit_wireVal_old .not [a] x hx hi, ?_⟩
  simpa [mkNot, Builder.emit, GateOp.eval] using b.emit_wireVal_new .not [a] x hx

lemma mkAnd_spec (b : Builder) (hv : b.Valid) (a c : ℕ)
    (ha : a < b.nextWire) (hc : c < b.nextWire)
    (x : List Bool) (hx : x.length = b.nIn) :
    (mkAnd b a c).2.Valid ∧ (mkAnd b a c).1 = b.nextWire ∧ (mkAnd b a c).2.nextWire = b.nextWire + 1 ∧
    (mkAnd b a c).2.nIn = b.nIn ∧
    notCount ((mkAnd b a c).2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ i < b.nextWire, (mkAnd b a c).2.wireVal x i = b.wireVal x i) ∧
    (mkAnd b a c).2.wireVal x (mkAnd b a c).1 = (b.wireVal x a && b.wireVal x c) := by
  refine ⟨b.emit_valid hv .and [a, c] (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    rfl, by simp [mkAnd, Builder.emit, Builder.nextWire]; omega, rfl,
    by simpa [mkAnd] using b.emit_notCount .and [a, c],
    fun i hi => b.emit_wireVal_old .and [a, c] x hx hi, ?_⟩
  simpa [mkAnd, Builder.emit, GateOp.eval] using b.emit_wireVal_new .and [a, c] x hx

lemma mkOr_spec (b : Builder) (hv : b.Valid) (a c : ℕ)
    (ha : a < b.nextWire) (hc : c < b.nextWire)
    (x : List Bool) (hx : x.length = b.nIn) :
    (mkOr b a c).2.Valid ∧ (mkOr b a c).1 = b.nextWire ∧ (mkOr b a c).2.nextWire = b.nextWire + 1 ∧
    (mkOr b a c).2.nIn = b.nIn ∧
    notCount ((mkOr b a c).2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ i < b.nextWire, (mkOr b a c).2.wireVal x i = b.wireVal x i) ∧
    (mkOr b a c).2.wireVal x (mkOr b a c).1 = (b.wireVal x a || b.wireVal x c) := by
  refine ⟨b.emit_valid hv .or [a, c] (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    rfl, by simp [mkOr, Builder.emit, Builder.nextWire]; omega, rfl,
    by simpa [mkOr] using b.emit_notCount .or [a, c],
    fun i hi => b.emit_wireVal_old .or [a, c] x hx hi, ?_⟩
  simpa [mkOr, Builder.emit, GateOp.eval] using b.emit_wireVal_new .or [a, c] x hx

lemma list_all_congr {α : Type*} (l : List α) {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma list_any_congr {α : Type*} (l : List α) {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma mkAndListAux_spec (b : Builder) (hv : b.Valid) (acc : ℕ) (hacc : acc < b.nextWire)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < b.nextWire) (x : List Bool) (hx : x.length = b.nIn) :
    (mkAndListAux b acc ws).2.Valid ∧
    (mkAndListAux b acc ws).1 < (mkAndListAux b acc ws).2.nextWire ∧
    b.nextWire ≤ (mkAndListAux b acc ws).2.nextWire ∧
    (mkAndListAux b acc ws).2.nIn = b.nIn ∧
    notCount ((mkAndListAux b acc ws).2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ i < b.nextWire, (mkAndListAux b acc ws).2.wireVal x i = b.wireVal x i) ∧
    (mkAndListAux b acc ws).2.wireVal x (mkAndListAux b acc ws).1 =
      (b.wireVal x acc && ws.all (b.wireVal x)) := by
  induction ws generalizing b acc with
  | nil => exact ⟨hv, hacc, le_rfl, rfl, rfl, fun _ _ => rfl, by simp [mkAndListAux]⟩
  | cons w ws ih =>
    dsimp only [mkAndListAux]
    have hw : w < b.nextWire := hws w (by simp)
    obtain ⟨hv1, _, hn1, hni1, hnc1, ho1, hw1⟩ := mkAnd_spec b hv acc w hacc hw x hx
    obtain ⟨hv2, hw2_lt, hn2, hni2, hnc2, ho2, hw2⟩ :=
      ih (mkAnd b acc w).2 hv1 (mkAnd b acc w).1 (by omega)
        (fun u hu => by have := hws u (by simp [hu]); omega) (by rw [hni1]; exact hx)
    refine ⟨hv2, hw2_lt, by omega, by rw [hni2, hni1], by rw [hnc2, hnc1],
      fun i hi => by rw [ho2 _ (by omega), ho1 _ hi], ?_⟩
    rw [hw2, hw1]
    have hall : ws.all ((mkAnd b acc w).2.wireVal x) = ws.all (b.wireVal x) :=
      list_all_congr ws (fun u hu => ho1 _ (by have := hws u (by simp [hu]); omega))
    rw [hall]; simp [Bool.and_assoc]

lemma mkOrListAux_spec (b : Builder) (hv : b.Valid) (acc : ℕ) (hacc : acc < b.nextWire)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < b.nextWire) (x : List Bool) (hx : x.length = b.nIn) :
    (mkOrListAux b acc ws).2.Valid ∧
    (mkOrListAux b acc ws).1 < (mkOrListAux b acc ws).2.nextWire ∧
    b.nextWire ≤ (mkOrListAux b acc ws).2.nextWire ∧
    (mkOrListAux b acc ws).2.nIn = b.nIn ∧
    notCount ((mkOrListAux b acc ws).2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ i < b.nextWire, (mkOrListAux b acc ws).2.wireVal x i = b.wireVal x i) ∧
    (mkOrListAux b acc ws).2.wireVal x (mkOrListAux b acc ws).1 =
      (b.wireVal x acc || ws.any (b.wireVal x)) := by
  induction ws generalizing b acc with
  | nil => exact ⟨hv, hacc, le_rfl, rfl, rfl, fun _ _ => rfl, by simp [mkOrListAux]⟩
  | cons w ws ih =>
    dsimp only [mkOrListAux]
    have hw : w < b.nextWire := hws w (by simp)
    obtain ⟨hv1, _, hn1, hni1, hnc1, ho1, hw1⟩ := mkOr_spec b hv acc w hacc hw x hx
    obtain ⟨hv2, hw2_lt, hn2, hni2, hnc2, ho2, hw2⟩ :=
      ih (mkOr b acc w).2 hv1 (mkOr b acc w).1 (by omega)
        (fun u hu => by have := hws u (by simp [hu]); omega) (by rw [hni1]; exact hx)
    refine ⟨hv2, hw2_lt, by omega, by rw [hni2, hni1], by rw [hnc2, hnc1],
      fun i hi => by rw [ho2 _ (by omega), ho1 _ hi], ?_⟩
    rw [hw2, hw1]
    have hany : ws.any ((mkOr b acc w).2.wireVal x) = ws.any (b.wireVal x) :=
      list_any_congr ws (fun u hu => ho1 _ (by have := hws u (by simp [hu]); omega))
    rw [hany]; simp [Bool.or_assoc]

-- 2. Schedule-to-circuit compiler and equivalence fit <-> HasSchedule

def HasSchedule (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) : Prop :=
  ∃ (rk : Fin (n + 1) → ℕ) (wd : Fin (n + 1) → (Fin a → Bool)),
    (∀ t, rk t < 2 ^ b) ∧
    Monotone rk ∧
    (∀ t t', t ≤ t' → rk t = rk t' → wd t ≤ wd t') ∧
    T.sum (fun t => cost t (wd t)) ≤ e

def chainInput (n : ℕ) (u : Fin (n + 1)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j.val < u.val)) ++ [false, true]

lemma chainInput_length (n : ℕ) (u : Fin (n + 1)) : (chainInput n u).length = n + 2 := by
  simp [chainInput]

def threshWire (n m : ℕ) : ℕ :=
  if m = 0 then n + 1 else if m ≤ n then m - 1 else n

lemma threshWire_lt (n m : ℕ) : threshWire n m < n + 2 := by
  unfold threshWire
  split_ifs <;> omega

lemma chainInput_getD_thresh (n m : ℕ) (u : Fin (n + 1)) :
    (chainInput n u).getD (threshWire n m) false = decide (m ≤ u.val) := by
  unfold chainInput threshWire
  split_ifs with hm0 hmn
  · subst hm0
    rw [getD_append_right _ _ (n + 1) false (by simp)]
    simp
  · rw [getD_append_left _ _ (m - 1) false (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hm1 : m - 1 < n := by omega
    simp [hm1]
    omega
  · rw [getD_append_right _ _ n false (by simp)]
    simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
    symm
    simp only [decide_eq_false_iff_not]
    omega

def bitMatchWires : List (ℕ × ℕ) → ℕ → List ℕ
  | [], _ => []
  | (pos, neg) :: rest, r => (if r % 2 = 1 then pos else neg) :: bitMatchWires rest (r / 2)

lemma bitMatchWires_mem (bits : List (ℕ × ℕ)) (r w : ℕ) (hw : w ∈ bitMatchWires bits r) :
    ∃ p ∈ bits, w = p.1 ∨ w = p.2 := by
  induction bits generalizing r with
  | nil => simp [bitMatchWires] at hw
  | cons p rest ih =>
    simp only [bitMatchWires, List.mem_cons] at hw
    rcases hw with rfl | hw
    · refine ⟨p, by simp, ?_⟩
      split_ifs <;> simp
    · obtain ⟨q, hq, hqw⟩ := ih (r / 2) hw
      exact ⟨q, by simp [hq], hqw⟩

lemma bitMatchWires_all (bits : List (ℕ × ℕ)) (val : ℕ → Bool) (v r : ℕ)
    (hv : v < 2 ^ bits.length) (hr : r < 2 ^ bits.length)
    (hbits : ∀ (j : ℕ) (hj : j < bits.length),
      val (bits[j]'hj).1 = decide ((v / 2 ^ j) % 2 = 1) ∧
      val (bits[j]'hj).2 = !decide ((v / 2 ^ j) % 2 = 1)) :
    (bitMatchWires bits r).all val = decide (v = r) := by
  induction bits generalizing v r with
  | nil =>
    simp only [List.length_nil, pow_zero] at hv hr
    have hv0 : v = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hv0 hr0
    simp [bitMatchWires]
  | cons p rest ih =>
    simp only [List.length_cons, pow_succ'] at hv hr
    have h0 := hbits 0 (by simp)
    simp only [pow_zero, Nat.div_one, List.getElem_cons_zero] at h0
    have hrest : ∀ (j : ℕ) (hj : j < rest.length),
        val (rest[j]'hj).1 = decide (((v / 2) / 2 ^ j) % 2 = 1) ∧
        val (rest[j]'hj).2 = !decide (((v / 2) / 2 ^ j) % 2 = 1) := by
      intro j hj
      have hj1 := hbits (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, pow_succ] at hj1
      have hdiv : v / 2 / 2 ^ j = v / (2 ^ j * 2) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
      rwa [hdiv]
    have ih' := ih (v / 2) (r / 2) (by omega) (by omega) hrest
    simp only [bitMatchWires, List.all_cons, ih']
    by_cases hv1 : v % 2 = 1 <;> by_cases hr1 : r % 2 = 1 <;>
      simp [h0.1, h0.2, hv1, hr1] <;> omega

def firstGe (n : ℕ) (f : Fin (n + 1) → ℕ) (val : ℕ) : ℕ :=
  ((List.finRange (n + 1)).find? (fun u => decide (val ≤ f u))).elim (n + 1) Fin.val

lemma firstGe_le_iff (n : ℕ) (f : Fin (n + 1) → ℕ) (hf : Monotone f) (val : ℕ) (u : Fin (n + 1)) :
    firstGe n f val ≤ u.val ↔ val ≤ f u := by
  unfold firstGe
  cases hfind : (List.finRange (n + 1)).find? (fun x => decide (val ≤ f x)) with
  | none =>
    simp only [Option.elim_none]
    have hu : ¬ (n + 1 ≤ u.val) := by omega
    have hnone := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp only [decide_eq_true_eq] at hnone
    exact ⟨fun h => absurd h hu, fun h => absurd h hnone⟩
  | some u0 =>
    simp only [Option.elim_some]
    have hu0_sat : decide (val ≤ f u0) = true :=
      List.find?_some (p := fun x => decide (val ≤ f x)) hfind
    simp only [decide_eq_true_eq] at hu0_sat
    constructor
    · intro hle
      have : u0 ≤ u := hle
      exact le_trans hu0_sat (hf this)
    · intro hval
      by_contra hlt
      have hlt' : u.val < u0.val := by omega
      have hu_not : decide (val ≤ f u) = false := by
        obtain ⟨_, k, hk, hget, hprev⟩ := List.find?_eq_some_iff_getElem.mp hfind
        have hku0 : u0.val = k := by
          have := List.getElem_finRange (n := n + 1) hk
          rw [← hget, this]
          rfl
        have huk : u.val < k := by omega
        have := hprev u.val huk
        simp only [List.getElem_finRange, Bool.not_eq_true'] at this
        exact this
      simp only [decide_eq_false_iff_not] at hu_not
      exact hu_not hval

def firstEqTrue (n : ℕ) (rk : Fin (n + 1) → ℕ) (r : ℕ) (g : Fin (n + 1) → Bool) : ℕ :=
  ((List.finRange (n + 1)).find? (fun u => decide (rk u = r) && g u)).elim (n + 1) Fin.val

lemma firstEqTrue_le_iff (n : ℕ) (rk : Fin (n + 1) → ℕ) (r : ℕ) (g : Fin (n + 1) → Bool)
    (hg : ∀ t t', t ≤ t' → rk t = rk t' → g t = true → g t' = true)
    (u : Fin (n + 1)) (hr : rk u = r) :
    firstEqTrue n rk r g ≤ u.val ↔ g u = true := by
  unfold firstEqTrue
  cases hfind : (List.finRange (n + 1)).find? (fun x => decide (rk x = r) && g x) with
  | none =>
    simp only [Option.elim_none]
    have hu : ¬ (n + 1 ≤ u.val) := by omega
    have hnone := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hnone
    exact ⟨fun h => absurd h hu, fun h => absurd h (by simp [hnone hr])⟩
  | some u0 =>
    simp only [Option.elim_some]
    have hu0_sat : (decide (rk u0 = r) && g u0) = true :=
      List.find?_some (p := fun x => decide (rk x = r) && g x) hfind
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hu0_sat
    constructor
    · intro hle
      exact hg u0 u hle (by rw [hu0_sat.1, hr]) hu0_sat.2
    · intro hgu
      by_contra hlt
      have hlt' : u.val < u0.val := by omega
      have hu_not : (decide (rk u = r) && g u) = false := by
        obtain ⟨_, k, hk, hget, hprev⟩ := List.find?_eq_some_iff_getElem.mp hfind
        have hku0 : u0.val = k := by
          have := List.getElem_finRange (n := n + 1) hk
          rw [← hget, this]
          rfl
        have huk : u.val < k := by omega
        have := hprev u.val huk
        simp only [List.getElem_finRange, Bool.not_eq_true'] at this
        exact this
      simp [hr, hgu] at hu_not

def compileRankBranches (n : ℕ) (rk : Fin (n + 1) → ℕ) (hiBits : List (ℕ × ℕ))
    (b : Builder) : List ℕ → List ℕ × Builder
  | [] => ([], b)
  | r :: rs =>
    let (isHi, b1) := mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)
    let (br, b2) := mkAnd b1 isHi (threshWire n (firstGe n rk (2 * r + 1)))
    let (rest, b3) := compileRankBranches n rk hiBits b2 rs
    (br :: rest, b3)

lemma compileRankBranches_spec (n : ℕ) (rk : Fin (n + 1) → ℕ) (hmono : Monotone rk)
    (hiBits : List (ℕ × ℕ)) (b : Builder) (hv : b.Valid) (hn : b.nIn = n + 2)
    (hnext : n + 2 ≤ b.nextWire)
    (hhi_lt : ∀ p ∈ hiBits, p.1 < b.nextWire ∧ p.2 < b.nextWire)
    (hhi_val : ∀ u : Fin (n + 1), ∀ (j : ℕ) (hj : j < hiBits.length),
      b.wireVal (chainInput n u) (hiBits[j]'hj).1 = decide (((rk u / 2) / 2 ^ j) % 2 = 1) ∧
      b.wireVal (chainInput n u) (hiBits[j]'hj).2 = !decide (((rk u / 2) / 2 ^ j) % 2 = 1))
    (hhi_bound : ∀ u : Fin (n + 1), rk u / 2 < 2 ^ hiBits.length)
    (hpre : ∀ u : Fin (n + 1), ∀ w < n + 2, b.wireVal (chainInput n u) w = (chainInput n u).getD w false)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, r < 2 ^ hiBits.length) :
    let res := compileRankBranches n rk hiBits b rs
    res.2.Valid ∧
    b.nextWire ≤ res.2.nextWire ∧
    res.2.nIn = n + 2 ∧
    notCount (res.2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ w ∈ res.1, w < res.2.nextWire) ∧
    (∀ u : Fin (n + 1), ∀ i < b.nextWire,
      res.2.wireVal (chainInput n u) i = b.wireVal (chainInput n u) i) ∧
    (∀ u : Fin (n + 1), res.1.any (res.2.wireVal (chainInput n u)) =
      rs.any (fun r => decide (rk u / 2 = r ∧ 2 * r + 1 ≤ rk u))) := by
  induction rs generalizing b with
  | nil =>
    refine ⟨hv, le_rfl, hn, rfl, fun w hw => by simp [compileRankBranches] at hw,
      fun _ _ _ => rfl, fun _ => by simp [compileRankBranches]⟩
  | cons r rs ih =>
    dsimp only [compileRankBranches]
    have hr : r < 2 ^ hiBits.length := hrs r (by simp)
    have hmatch_lt : ∀ w ∈ bitMatchWires hiBits r, w < b.nextWire := by
      intro w hw
      obtain ⟨p, hp, rfl | rfl⟩ := bitMatchWires_mem hiBits r w hw
      · exact (hhi_lt p hp).1
      · exact (hhi_lt p hp).2
    have h0_lt : threshWire n 0 < b.nextWire := lt_of_lt_of_le (threshWire_lt n 0) hnext
    have h1_lt : ∀ u : Fin (n + 1),
        (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.Valid ∧
        (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).1 <
          (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.nextWire ∧
        b.nextWire ≤ (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.nextWire ∧
        (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.nIn = n + 2 ∧
        notCount ((mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.toCircuit 0) =
          notCount (b.toCircuit 0) ∧
        (∀ i < b.nextWire, (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.wireVal (chainInput n u) i =
          b.wireVal (chainInput n u) i) ∧
        (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2.wireVal (chainInput n u)
          (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).1 =
          decide (rk u / 2 = r) := by
      intro u
      obtain ⟨hv1, his_lt, hnx1, hni1, hnc1, hold1, hval1⟩ :=
        mkAndListAux_spec b hv (threshWire n 0) h0_lt (bitMatchWires hiBits r) hmatch_lt
          (chainInput n u) (by rw [hn]; exact chainInput_length n u)
      refine ⟨hv1, his_lt, hnx1, by rw [hni1, hn], hnc1, hold1, ?_⟩
      rw [hval1, hpre u (threshWire n 0) (threshWire_lt n 0), chainInput_getD_thresh]
      simp only [Nat.zero_le, decide_true, Bool.true_and]
      exact bitMatchWires_all hiBits (b.wireVal (chainInput n u)) (rk u / 2) r
        (hhi_bound u) hr (hhi_val u)
    set b1 := (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).2
    set isHi := (mkAndListAux b (threshWire n 0) (bitMatchWires hiBits r)).1
    have h0' := h1_lt ⟨0, Nat.zero_lt_succ n⟩
    have hv1 := h0'.1
    have his_lt := h0'.2.1
    have hnx1 := h0'.2.2.1
    have hni1 := h0'.2.2.2.1
    have hnc1 := h0'.2.2.2.2.1
    have hold1 : ∀ u i, i < b.nextWire → b1.wireVal (chainInput n u) i = b.wireVal (chainInput n u) i :=
      fun u => (h1_lt u).2.2.2.2.2.1
    have hval1 : ∀ u, b1.wireVal (chainInput n u) isHi = decide (rk u / 2 = r) :=
      fun u => (h1_lt u).2.2.2.2.2.2
    have hth_lt : threshWire n (firstGe n rk (2 * r + 1)) < b1.nextWire :=
      lt_of_lt_of_le (threshWire_lt n _) (le_trans hnext hnx1)
    set b2 := (mkAnd b1 isHi (threshWire n (firstGe n rk (2 * r + 1)))).2
    set br := (mkAnd b1 isHi (threshWire n (firstGe n rk (2 * r + 1)))).1
    have h2_lt : ∀ u : Fin (n + 1),
        b2.Valid ∧ br = b1.nextWire ∧ b2.nextWire = b1.nextWire + 1 ∧ b2.nIn = n + 2 ∧
        notCount (b2.toCircuit 0) = notCount (b1.toCircuit 0) ∧
        (∀ i < b1.nextWire, b2.wireVal (chainInput n u) i = b1.wireVal (chainInput n u) i) ∧
        b2.wireVal (chainInput n u) br = decide (rk u / 2 = r ∧ 2 * r + 1 ≤ rk u) := by
      intro u
      obtain ⟨hv2, hbr, hnx2, hni2, hnc2, hold2, hval2⟩ :=
        mkAnd_spec b1 hv1 isHi (threshWire n (firstGe n rk (2 * r + 1))) his_lt hth_lt
          (chainInput n u) (by rw [hni1]; exact chainInput_length n u)
      refine ⟨hv2, hbr, hnx2, by rw [hni2, hni1], hnc2, hold2, ?_⟩
      rw [hval2, hval1 u, hold1 u (threshWire n (firstGe n rk (2 * r + 1))) (lt_of_lt_of_le (threshWire_lt n _) hnext),
        hpre u _ (threshWire_lt n _), chainInput_getD_thresh]
      simp [firstGe_le_iff n rk hmono, Bool.decide_and]
    have h2_0 := h2_lt ⟨0, Nat.zero_lt_succ n⟩
    have hv2 := h2_0.1
    have hbr_eq := h2_0.2.1
    have hnx2 := h2_0.2.2.1
    have hni2 := h2_0.2.2.2.1
    have hnc2 := h2_0.2.2.2.2.1
    have hold2 : ∀ u i, i < b1.nextWire → b2.wireVal (chainInput n u) i = b1.wireVal (chainInput n u) i :=
      fun u => (h2_lt u).2.2.2.2.2.1
    have hval2 : ∀ u, b2.wireVal (chainInput n u) br = decide (rk u / 2 = r ∧ 2 * r + 1 ≤ rk u) :=
      fun u => (h2_lt u).2.2.2.2.2.2
    obtain ⟨hv3, hnx3, hni3, hnc3, hmem3, hold3, hany3⟩ :=
      ih b2 hv2 hni2 (by omega)
        (fun p hp => ⟨by have := (hhi_lt p hp).1; omega, by have := (hhi_lt p hp).2; omega⟩)
        (fun u j hj => by
          have := hhi_val u j hj
          have hp1 := (hhi_lt _ (List.getElem_mem hj)).1
          have hp2 := (hhi_lt _ (List.getElem_mem hj)).2
          rw [hold2 u _ (by omega), hold1 u _ hp1, hold2 u _ (by omega), hold1 u _ hp2]
          exact this)
        (fun u w hw => by
          rw [hold2 u w (by omega), hold1 u w (lt_of_lt_of_le hw hnext), hpre u w hw])
        (fun x hx => hrs x (by simp [hx]))
    refine ⟨hv3, by omega, hni3, by rw [hnc3, hnc2, hnc1], ?_, ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hmem3 w hw
    · intro u i hi
      rw [hold3 u i (by omega), hold2 u i (by omega), hold1 u i hi]
    · intro u
      simp only [List.any_cons, hany3 u]
      rw [hold3 u br (by omega), hval2 u]

def compileRankBits (n : ℕ) (rk : Fin (n + 1) → ℕ) : ℕ → Builder → List (ℕ × ℕ) × Builder
  | 0, b => ([], b)
  | k + 1, b =>
    let (hiBits, b1) := compileRankBits n (fun u => rk u / 2) k b
    let (branches, b2) := compileRankBranches n rk hiBits b1 (List.range (2 ^ k))
    let (lo, b3) := mkOrListAux b2 (threshWire n (n + 1)) branches
    let (nlo, b4) := mkNot b3 lo
    ((lo, nlo) :: hiBits, b4)

lemma compileRankBits_spec (n : ℕ) (rk : Fin (n + 1) → ℕ) (hmono : Monotone rk)
    (k : ℕ) (hk : ∀ u : Fin (n + 1), rk u < 2 ^ k)
    (b : Builder) (hv : b.Valid) (hn : b.nIn = n + 2) (hnext : n + 2 ≤ b.nextWire)
    (hpre : ∀ u : Fin (n + 1), ∀ w < n + 2, b.wireVal (chainInput n u) w = (chainInput n u).getD w false) :
    let res := compileRankBits n rk k b
    res.2.Valid ∧
    res.1.length = k ∧
    b.nextWire ≤ res.2.nextWire ∧
    res.2.nIn = n + 2 ∧
    notCount (res.2.toCircuit 0) = notCount (b.toCircuit 0) + k ∧
    (∀ p ∈ res.1, p.1 < res.2.nextWire ∧ p.2 < res.2.nextWire) ∧
    (∀ u : Fin (n + 1), ∀ i < b.nextWire,
      res.2.wireVal (chainInput n u) i = b.wireVal (chainInput n u) i) ∧
    (∀ u : Fin (n + 1), ∀ (j : ℕ) (hj : j < res.1.length),
      res.2.wireVal (chainInput n u) (res.1[j]'hj).1 = decide ((rk u / 2 ^ j) % 2 = 1) ∧
      res.2.wireVal (chainInput n u) (res.1[j]'hj).2 = !decide ((rk u / 2 ^ j) % 2 = 1)) := by
  induction k generalizing rk b with
  | zero =>
    refine ⟨hv, rfl, le_rfl, hn, rfl, fun p hp => by simp [compileRankBits] at hp,
      fun _ _ _ => rfl, fun _ j hj => by simp [compileRankBits] at hj⟩
  | succ k ih =>
    dsimp only [compileRankBits]
    have hmono_div : Monotone (fun u => rk u / 2) := fun u v huv => Nat.div_le_div_right (hmono huv)
    have hk_div : ∀ u : Fin (n + 1), rk u / 2 < 2 ^ k := by
      intro u
      have := hk u
      rw [pow_succ'] at this
      omega
    obtain ⟨hv1, hlen1, hnx1, hni1, hnc1, hlt1, hold1, hval1⟩ :=
      ih (fun u => rk u / 2) hmono_div hk_div b hv hn hnext hpre
    set hiBits := (compileRankBits n (fun u => rk u / 2) k b).1
    set b1 := (compileRankBits n (fun u => rk u / 2) k b).2
    have hpre1 : ∀ u : Fin (n + 1), ∀ w < n + 2, b1.wireVal (chainInput n u) w = (chainInput n u).getD w false :=
      fun u w hw => by rw [hold1 u w (lt_of_lt_of_le hw hnext), hpre u w hw]
    obtain ⟨hv2, hnx2, hni2, hnc2, hbr_lt, hold2, hany2⟩ :=
      compileRankBranches_spec n rk hmono hiBits b1 hv1 hni1 (by omega) hlt1 hval1
        (fun u => by rw [hlen1]; exact hk_div u) hpre1 (List.range (2 ^ k))
        (fun r hr => by rw [hlen1]; simpa using hr)
    set branches := (compileRankBranches n rk hiBits b1 (List.range (2 ^ k))).1
    set b2 := (compileRankBranches n rk hiBits b1 (List.range (2 ^ k))).2
    have hfalse_lt : threshWire n (n + 1) < b2.nextWire := lt_of_lt_of_le (threshWire_lt n _) (by omega)
    have h3 : ∀ u : Fin (n + 1),
        (mkOrListAux b2 (threshWire n (n + 1)) branches).2.Valid ∧
        (mkOrListAux b2 (threshWire n (n + 1)) branches).1 <
          (mkOrListAux b2 (threshWire n (n + 1)) branches).2.nextWire ∧
        b2.nextWire ≤ (mkOrListAux b2 (threshWire n (n + 1)) branches).2.nextWire ∧
        (mkOrListAux b2 (threshWire n (n + 1)) branches).2.nIn = n + 2 ∧
        notCount ((mkOrListAux b2 (threshWire n (n + 1)) branches).2.toCircuit 0) =
          notCount (b2.toCircuit 0) ∧
        (∀ i < b2.nextWire, (mkOrListAux b2 (threshWire n (n + 1)) branches).2.wireVal (chainInput n u) i =
          b2.wireVal (chainInput n u) i) ∧
        (mkOrListAux b2 (threshWire n (n + 1)) branches).2.wireVal (chainInput n u)
          (mkOrListAux b2 (threshWire n (n + 1)) branches).1 =
          decide (rk u % 2 = 1) := by
      intro u
      obtain ⟨hv3, hlo_lt, hnx3, hni3, hnc3, hold3, hval3⟩ :=
        mkOrListAux_spec b2 hv2 (threshWire n (n + 1)) hfalse_lt branches hbr_lt
          (chainInput n u) (by rw [hni2]; exact chainInput_length n u)
      refine ⟨hv3, hlo_lt, hnx3, by rw [hni3, hni2], hnc3, hold3, ?_⟩
      rw [hval3, hold2 u _ (lt_of_lt_of_le (threshWire_lt n _) (by omega)),
        hpre1 u _ (threshWire_lt n _), chainInput_getD_thresh]
      have hnot_false : ¬ (n + 1 ≤ u.val) := by omega
      simp only [hnot_false, decide_false, Bool.false_or, hany2 u]
      have hdiv_lt : rk u / 2 < 2 ^ k := hk_div u
      by_cases hmod : rk u % 2 = 1
      · simp only [hmod, decide_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
        exact ⟨rk u / 2, hdiv_lt, rfl, by omega⟩
      · have hmod0 : rk u % 2 = 0 := by omega
        simp only [hmod, decide_false, Bool.false_eq_true, List.any_eq_false, List.mem_range,
          decide_eq_true_eq, not_and]
        intro r _ hr
        omega
    set lo := (mkOrListAux b2 (threshWire n (n + 1)) branches).1
    set b3 := (mkOrListAux b2 (threshWire n (n + 1)) branches).2
    have h3_0 := h3 ⟨0, Nat.zero_lt_succ n⟩
    have hv3 := h3_0.1
    have hlo_lt := h3_0.2.1
    have hnx3 := h3_0.2.2.1
    have hni3 := h3_0.2.2.2.1
    have hnc3 := h3_0.2.2.2.2.1
    have hold3 : ∀ u i, i < b2.nextWire → b3.wireVal (chainInput n u) i = b2.wireVal (chainInput n u) i :=
      fun u => (h3 u).2.2.2.2.2.1
    have hval3 : ∀ u, b3.wireVal (chainInput n u) lo = decide (rk u % 2 = 1) :=
      fun u => (h3 u).2.2.2.2.2.2
    set nlo := (mkNot b3 lo).1
    set b4 := (mkNot b3 lo).2
    have h4 : ∀ u : Fin (n + 1),
        b4.Valid ∧ nlo = b3.nextWire ∧ b4.nextWire = b3.nextWire + 1 ∧ b4.nIn = n + 2 ∧
        notCount (b4.toCircuit 0) = notCount (b3.toCircuit 0) + 1 ∧
        (∀ i < b3.nextWire, b4.wireVal (chainInput n u) i = b3.wireVal (chainInput n u) i) ∧
        b4.wireVal (chainInput n u) nlo = !decide (rk u % 2 = 1) := by
      intro u
      obtain ⟨hv4, hnlo, hnx4, hni4, hnc4, hold4, hval4⟩ :=
        mkNot_spec b3 hv3 lo hlo_lt (chainInput n u) (by rw [hni3]; exact chainInput_length n u)
      refine ⟨hv4, hnlo, hnx4, by rw [hni4, hni3], hnc4, hold4, ?_⟩
      rw [hval4, hval3 u]
    have h4_0 := h4 ⟨0, Nat.zero_lt_succ n⟩
    have hv4 := h4_0.1
    have hnlo_eq := h4_0.2.1
    have hnx4 := h4_0.2.2.1
    have hni4 := h4_0.2.2.2.1
    have hnc4 := h4_0.2.2.2.2.1
    have hold4 : ∀ u i, i < b3.nextWire → b4.wireVal (chainInput n u) i = b3.wireVal (chainInput n u) i :=
      fun u => (h4 u).2.2.2.2.2.1
    have hval4 : ∀ u, b4.wireVal (chainInput n u) nlo = !decide (rk u % 2 = 1) :=
      fun u => (h4 u).2.2.2.2.2.2
    refine ⟨hv4, by simp [hiBits, hlen1], by omega, hni4, by omega, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨by omega, by omega⟩
      · exact ⟨by have := (hlt1 p hp).1; omega, by have := (hlt1 p hp).2; omega⟩
    · intro u i hi
      rw [hold4 u i (by omega), hold3 u i (by omega), hold2 u i (by omega), hold1 u i hi]
    · intro u j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, pow_zero, Nat.div_one]
        exact ⟨by rw [hold4 u lo (by omega), hval3 u], hval4 u⟩
      | succ j =>
        simp only [List.getElem_cons_succ, pow_succ]
        have hdiv : rk u / 2 / 2 ^ j = rk u / (2 ^ j * 2) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
        have hj' : j < hiBits.length := by simpa using hj
        have h1 := hval1 u j hj'
        have hp1 := (hlt1 _ (List.getElem_mem hj')).1
        have hp2 := (hlt1 _ (List.getElem_mem hj')).2
        constructor
        · rw [hold4 u _ (by omega), hold3 u _ (by omega), hold2 u _ hp1, h1.1, hdiv]
        · rw [hold4 u _ (by omega), hold3 u _ (by omega), hold2 u _ hp2, h1.2, hdiv]

def compileValBranches (n : ℕ) (rk : Fin (n + 1) → ℕ) (g : Fin (n + 1) → Bool)
    (bits : List (ℕ × ℕ)) (b : Builder) : List ℕ → List ℕ × Builder
  | [] => ([], b)
  | r :: rs =>
    let (isEq, b1) := mkAndListAux b (threshWire n 0) (bitMatchWires bits r)
    let (br, b2) := mkAnd b1 isEq (threshWire n (firstEqTrue n rk r g))
    let (rest, b3) := compileValBranches n rk g bits b2 rs
    (br :: rest, b3)

lemma compileValBranches_spec (n : ℕ) (rk : Fin (n + 1) → ℕ) (g : Fin (n + 1) → Bool)
    (hg : ∀ t t', t ≤ t' → rk t = rk t' → g t = true → g t' = true)
    (bits : List (ℕ × ℕ)) (b : Builder) (hv : b.Valid) (hn : b.nIn = n + 2)
    (hnext : n + 2 ≤ b.nextWire)
    (hbits_lt : ∀ p ∈ bits, p.1 < b.nextWire ∧ p.2 < b.nextWire)
    (hbits_val : ∀ u : Fin (n + 1), ∀ (j : ℕ) (hj : j < bits.length),
      b.wireVal (chainInput n u) (bits[j]'hj).1 = decide ((rk u / 2 ^ j) % 2 = 1) ∧
      b.wireVal (chainInput n u) (bits[j]'hj).2 = !decide ((rk u / 2 ^ j) % 2 = 1))
    (hbits_bound : ∀ u : Fin (n + 1), rk u < 2 ^ bits.length)
    (hpre : ∀ u : Fin (n + 1), ∀ w < n + 2, b.wireVal (chainInput n u) w = (chainInput n u).getD w false)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, r < 2 ^ bits.length) :
    let res := compileValBranches n rk g bits b rs
    res.2.Valid ∧
    b.nextWire ≤ res.2.nextWire ∧
    res.2.nIn = n + 2 ∧
    notCount (res.2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ w ∈ res.1, w < res.2.nextWire) ∧
    (∀ u : Fin (n + 1), ∀ i < b.nextWire,
      res.2.wireVal (chainInput n u) i = b.wireVal (chainInput n u) i) ∧
    (∀ u : Fin (n + 1), res.1.any (res.2.wireVal (chainInput n u)) =
      rs.any (fun r => decide (rk u = r ∧ g u = true))) := by
  induction rs generalizing b with
  | nil =>
    refine ⟨hv, le_rfl, hn, rfl, fun w hw => by simp [compileValBranches] at hw,
      fun _ _ _ => rfl, fun _ => by simp [compileValBranches]⟩
  | cons r rs ih =>
    dsimp only [compileValBranches]
    have hr : r < 2 ^ bits.length := hrs r (by simp)
    have hmatch_lt : ∀ w ∈ bitMatchWires bits r, w < b.nextWire := by
      intro w hw
      obtain ⟨p, hp, rfl | rfl⟩ := bitMatchWires_mem bits r w hw
      · exact (hbits_lt p hp).1
      · exact (hbits_lt p hp).2
    have h0_lt : threshWire n 0 < b.nextWire := lt_of_lt_of_le (threshWire_lt n 0) hnext
    have h1_lt : ∀ u : Fin (n + 1),
        (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.Valid ∧
        (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).1 <
          (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.nextWire ∧
        b.nextWire ≤ (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.nextWire ∧
        (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.nIn = n + 2 ∧
        notCount ((mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.toCircuit 0) =
          notCount (b.toCircuit 0) ∧
        (∀ i < b.nextWire, (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.wireVal (chainInput n u) i =
          b.wireVal (chainInput n u) i) ∧
        (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2.wireVal (chainInput n u)
          (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).1 =
          decide (rk u = r) := by
      intro u
      obtain ⟨hv1, his_lt, hnx1, hni1, hnc1, hold1, hval1⟩ :=
        mkAndListAux_spec b hv (threshWire n 0) h0_lt (bitMatchWires bits r) hmatch_lt
          (chainInput n u) (by rw [hn]; exact chainInput_length n u)
      refine ⟨hv1, his_lt, hnx1, by rw [hni1, hn], hnc1, hold1, ?_⟩
      rw [hval1, hpre u (threshWire n 0) (threshWire_lt n 0), chainInput_getD_thresh]
      simp only [Nat.zero_le, decide_true, Bool.true_and]
      exact bitMatchWires_all bits (b.wireVal (chainInput n u)) (rk u) r
        (hbits_bound u) hr (hbits_val u)
    set b1 := (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).2
    set isEq := (mkAndListAux b (threshWire n 0) (bitMatchWires bits r)).1
    have h0' := h1_lt ⟨0, Nat.zero_lt_succ n⟩
    have hv1 := h0'.1
    have his_lt := h0'.2.1
    have hnx1 := h0'.2.2.1
    have hni1 := h0'.2.2.2.1
    have hnc1 := h0'.2.2.2.2.1
    have hold1 : ∀ u i, i < b.nextWire → b1.wireVal (chainInput n u) i = b.wireVal (chainInput n u) i :=
      fun u => (h1_lt u).2.2.2.2.2.1
    have hval1 : ∀ u, b1.wireVal (chainInput n u) isEq = decide (rk u = r) :=
      fun u => (h1_lt u).2.2.2.2.2.2
    have hth_lt : threshWire n (firstEqTrue n rk r g) < b1.nextWire :=
      lt_of_lt_of_le (threshWire_lt n _) (le_trans hnext hnx1)
    set b2 := (mkAnd b1 isEq (threshWire n (firstEqTrue n rk r g))).2
    set br := (mkAnd b1 isEq (threshWire n (firstEqTrue n rk r g))).1
    have h2_lt : ∀ u : Fin (n + 1),
        b2.Valid ∧ br = b1.nextWire ∧ b2.nextWire = b1.nextWire + 1 ∧ b2.nIn = n + 2 ∧
        notCount (b2.toCircuit 0) = notCount (b1.toCircuit 0) ∧
        (∀ i < b1.nextWire, b2.wireVal (chainInput n u) i = b1.wireVal (chainInput n u) i) ∧
        b2.wireVal (chainInput n u) br = decide (rk u = r ∧ g u = true) := by
      intro u
      obtain ⟨hv2, hbr, hnx2, hni2, hnc2, hold2, hval2⟩ :=
        mkAnd_spec b1 hv1 isEq (threshWire n (firstEqTrue n rk r g)) his_lt hth_lt
          (chainInput n u) (by rw [hni1]; exact chainInput_length n u)
      refine ⟨hv2, hbr, hnx2, by rw [hni2, hni1], hnc2, hold2, ?_⟩
      rw [hval2, hval1 u, hold1 u (threshWire n (firstEqTrue n rk r g)) (lt_of_lt_of_le (threshWire_lt n _) hnext),
        hpre u _ (threshWire_lt n _), chainInput_getD_thresh]
      by_cases hrk : rk u = r
      · simp [hrk, firstEqTrue_le_iff n rk r g hg u hrk]
      · simp [hrk]
    have h2_0 := h2_lt ⟨0, Nat.zero_lt_succ n⟩
    have hv2 := h2_0.1
    have hnx2 := h2_0.2.2.1
    have hni2 := h2_0.2.2.2.1
    have hnc2 := h2_0.2.2.2.2.1
    have hold2 : ∀ u i, i < b1.nextWire → b2.wireVal (chainInput n u) i = b1.wireVal (chainInput n u) i :=
      fun u => (h2_lt u).2.2.2.2.2.1
    have hval2 : ∀ u, b2.wireVal (chainInput n u) br = decide (rk u = r ∧ g u = true) :=
      fun u => (h2_lt u).2.2.2.2.2.2
    obtain ⟨hv3, hnx3, hni3, hnc3, hmem3, hold3, hany3⟩ :=
      ih b2 hv2 hni2 (by omega)
        (fun p hp => ⟨by have := (hbits_lt p hp).1; omega, by have := (hbits_lt p hp).2; omega⟩)
        (fun u j hj => by
          have := hbits_val u j hj
          have hp1 := (hbits_lt _ (List.getElem_mem hj)).1
          have hp2 := (hbits_lt _ (List.getElem_mem hj)).2
          rw [hold2 u _ (by omega), hold1 u _ hp1, hold2 u _ (by omega), hold1 u _ hp2]
          exact this)
        (fun u w hw => by
          rw [hold2 u w (by omega), hold1 u w (lt_of_lt_of_le hw hnext), hpre u w hw])
        (fun x hx => hrs x (by simp [hx]))
    refine ⟨hv3, by omega, hni3, by rw [hnc3, hnc2, hnc1], ?_, ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hmem3 w hw
    · intro u i hi
      rw [hold3 u i (by omega), hold2 u i (by omega), hold1 u i hi]
    · intro u
      simp only [List.any_cons, hany3 u]
      rw [hold3 u br (by omega), hval2 u]

def compileTapsList (n : ℕ) (rk : Fin (n + 1) → ℕ) (wd : Fin (n + 1) → ℕ → Bool)
    (bits : List (ℕ × ℕ)) (b : Builder) : List ℕ → List ℕ × Builder
  | [] => ([], b)
  | i :: is =>
    let (branches, b1) := compileValBranches n rk (fun u => wd u i) bits b (List.range (2 ^ bits.length))
    let (tap, b2) := mkOrListAux b1 (threshWire n (n + 1)) branches
    let (rest, b3) := compileTapsList n rk wd bits b2 is
    (tap :: rest, b3)

lemma compileTapsList_spec (n : ℕ) (rk : Fin (n + 1) → ℕ) (wd : Fin (n + 1) → ℕ → Bool)
    (hwd : ∀ i t t', t ≤ t' → rk t = rk t' → wd t i = true → wd t' i = true)
    (bits : List (ℕ × ℕ)) (b : Builder) (hv : b.Valid) (hn : b.nIn = n + 2)
    (hnext : n + 2 ≤ b.nextWire)
    (hbits_lt : ∀ p ∈ bits, p.1 < b.nextWire ∧ p.2 < b.nextWire)
    (hbits_val : ∀ u : Fin (n + 1), ∀ (j : ℕ) (hj : j < bits.length),
      b.wireVal (chainInput n u) (bits[j]'hj).1 = decide ((rk u / 2 ^ j) % 2 = 1) ∧
      b.wireVal (chainInput n u) (bits[j]'hj).2 = !decide ((rk u / 2 ^ j) % 2 = 1))
    (hbits_bound : ∀ u : Fin (n + 1), rk u < 2 ^ bits.length)
    (hpre : ∀ u : Fin (n + 1), ∀ w < n + 2, b.wireVal (chainInput n u) w = (chainInput n u).getD w false)
    (is : List ℕ) :
    let res := compileTapsList n rk wd bits b is
    res.2.Valid ∧
    res.1.length = is.length ∧
    b.nextWire ≤ res.2.nextWire ∧
    res.2.nIn = n + 2 ∧
    notCount (res.2.toCircuit 0) = notCount (b.toCircuit 0) ∧
    (∀ w ∈ res.1, w < res.2.nextWire) ∧
    (∀ (u : Fin (n + 1)) (w : ℕ), w < b.nextWire →
      res.2.wireVal (chainInput n u) w = b.wireVal (chainInput n u) w) ∧
    (∀ (u : Fin (n + 1)) (k : ℕ) (hk : k < is.length),
      res.2.wireVal (chainInput n u) (res.1.getD k 0) = wd u (is[k]'hk)) := by
  induction is generalizing b with
  | nil =>
    refine ⟨hv, rfl, le_rfl, hn, rfl, fun w hw => by simp [compileTapsList] at hw,
      fun _ _ _ => rfl, fun _ _ hk => by simp at hk⟩
  | cons i is ih =>
    dsimp only [compileTapsList]
    obtain ⟨hv1, hnx1, hni1, hnc1, hbr_lt, hold1, hany1⟩ :=
      compileValBranches_spec n rk (fun u => wd u i) (hwd i) bits b hv hn hnext hbits_lt
        hbits_val hbits_bound hpre (List.range (2 ^ bits.length)) (fun r hr => by simpa using hr)
    set branches := (compileValBranches n rk (fun u => wd u i) bits b (List.range (2 ^ bits.length))).1
    set b1 := (compileValBranches n rk (fun u => wd u i) bits b (List.range (2 ^ bits.length))).2
    have hfalse_lt : threshWire n (n + 1) < b1.nextWire := lt_of_lt_of_le (threshWire_lt n _) (by omega)
    have h2 : ∀ u : Fin (n + 1),
        (mkOrListAux b1 (threshWire n (n + 1)) branches).2.Valid ∧
        (mkOrListAux b1 (threshWire n (n + 1)) branches).1 <
          (mkOrListAux b1 (threshWire n (n + 1)) branches).2.nextWire ∧
        b1.nextWire ≤ (mkOrListAux b1 (threshWire n (n + 1)) branches).2.nextWire ∧
        (mkOrListAux b1 (threshWire n (n + 1)) branches).2.nIn = n + 2 ∧
        notCount ((mkOrListAux b1 (threshWire n (n + 1)) branches).2.toCircuit 0) =
          notCount (b1.toCircuit 0) ∧
        (∀ w < b1.nextWire, (mkOrListAux b1 (threshWire n (n + 1)) branches).2.wireVal (chainInput n u) w =
          b1.wireVal (chainInput n u) w) ∧
        (mkOrListAux b1 (threshWire n (n + 1)) branches).2.wireVal (chainInput n u)
          (mkOrListAux b1 (threshWire n (n + 1)) branches).1 = wd u i := by
      intro u
      obtain ⟨hv2, htap_lt, hnx2, hni2, hnc2, hold2, hval2⟩ :=
        mkOrListAux_spec b1 hv1 (threshWire n (n + 1)) hfalse_lt branches hbr_lt
          (chainInput n u) (by rw [hni1]; exact chainInput_length n u)
      refine ⟨hv2, htap_lt, hnx2, by rw [hni2, hni1], hnc2, hold2, ?_⟩
      rw [hval2, hold1 u _ (lt_of_lt_of_le (threshWire_lt n _) hnext), hpre u _ (threshWire_lt n _),
        chainInput_getD_thresh]
      have hnot_false : ¬ (n + 1 ≤ u.val) := by omega
      simp only [hnot_false, decide_false, Bool.false_or, hany1 u]
      cases hwd_val : wd u i
      · simp [List.any_eq_false]
      · simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
        exact ⟨rk u, hbits_bound u, rfl, trivial⟩
    set tap := (mkOrListAux b1 (threshWire n (n + 1)) branches).1
    set b2 := (mkOrListAux b1 (threshWire n (n + 1)) branches).2
    have h2_0 := h2 ⟨0, Nat.zero_lt_succ n⟩
    have hv2 := h2_0.1
    have htap_lt := h2_0.2.1
    have hnx2 := h2_0.2.2.1
    have hni2 := h2_0.2.2.2.1
    have hnc2 := h2_0.2.2.2.2.1
    have hold2 : ∀ u w, w < b1.nextWire → b2.wireVal (chainInput n u) w = b1.wireVal (chainInput n u) w :=
      fun u => (h2 u).2.2.2.2.2.1
    have hval2 : ∀ u, b2.wireVal (chainInput n u) tap = wd u i :=
      fun u => (h2 u).2.2.2.2.2.2
    obtain ⟨hv3, hlen3, hnx3, hni3, hnc3, hmem3, hold3, hget3⟩ :=
      ih b2 hv2 hni2 (by omega)
        (fun p hp => ⟨by have := (hbits_lt p hp).1; omega, by have := (hbits_lt p hp).2; omega⟩)
        (fun u j hj => by
          have := hbits_val u j hj
          have hp1 := (hbits_lt _ (List.getElem_mem hj)).1
          have hp2 := (hbits_lt _ (List.getElem_mem hj)).2
          rw [hold2 u _ (by omega), hold1 u _ hp1, hold2 u _ (by omega), hold1 u _ hp2]
          exact this)
        (fun u w hw => by
          rw [hold2 u w (by omega), hold1 u w (lt_of_lt_of_le hw hnext), hpre u w hw])
    refine ⟨hv3, by simp [hlen3], by omega, hni3, by rw [hnc3, hnc2, hnc1], ?_, ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hmem3 w hw
    · intro u w hw
      rw [hold3 u w (by omega), hold2 u w (by omega), hold1 u w hw]
    · intro u k hk
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hold3 u tap htap_lt, hval2 u]
      | succ k =>
        simpa using hget3 u k (by simpa using hk)

lemma fit_iff_schedule (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) :
    (∃ (C : Circuit) (tap : Fin a → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ notCount C ≤ b ∧ C.output < n + 2 + C.size ∧
      (∀ i, tap i < n + 2 + C.size) ∧
      T.sum (fun t => cost t (fun i => (C.wires (chainInput n t)).getD (tap i) false)) ≤ e) ↔
    HasSchedule a n b e cost T := by
  constructor
  · rintro ⟨C, tap, hfan, _, hnot, _, _, hsum⟩
    obtain ⟨h, hmono, hbound, hstep⟩ := circuit_rank (n := n) C hfan
    refine ⟨fun t => h (fun j => decide (j.val < t.val)),
      fun t i => (C.wires (chainInput n t)).getD (tap i) false, ?_, ?_, ?_, hsum⟩
    · intro t
      exact lt_of_lt_of_le (hbound _) (Nat.pow_le_pow_right (by omega) hnot)
    · intro t t' htt'
      apply hmono
      intro j
      simp only [Bool.le_iff_imp, decide_eq_true_eq]
      omega
    · intro t t' htt' hrk i
      have hxle : (fun j : Fin n => decide (j.val < t.val)) ≤
          (fun j : Fin n => decide (j.val < t'.val)) := by
        intro j
        simp only [Bool.le_iff_imp, decide_eq_true_eq]
        omega
      have hw := hstep _ _ hxle hrk (tap i)
      simp only [Bool.le_iff_imp]
      exact hw
  · rintro ⟨rk, wd, hrk_lt, hrk_mono, hwd_mono, hsum⟩
    let b0 := Builder.init (n + 2)
    have hv0 : b0.Valid := Builder.init_valid (n + 2)
    have hn0 : b0.nIn = n + 2 := rfl
    have hnext0 : n + 2 ≤ b0.nextWire := by simp [b0, Builder.init, Builder.nextWire]
    have hpre0 : ∀ u : Fin (n + 1), ∀ w < n + 2,
        b0.wireVal (chainInput n u) w = (chainInput n u).getD w false :=
      fun u w _ => Builder.init_wireVal (n + 2) (chainInput n u) w
    obtain ⟨hv1, hlen1, hnx1, hni1, hnc1, hlt1, hold1, hval1⟩ :=
      compileRankBits_spec n rk hrk_mono b hrk_lt b0 hv0 hn0 hnext0 hpre0
    set bits := (compileRankBits n rk b b0).1
    set b1 := (compileRankBits n rk b b0).2
    let wdN : Fin (n + 1) → ℕ → Bool := fun u i => if h : i < a then wd u ⟨i, h⟩ else false
    have hwdN : ∀ i t t', t ≤ t' → rk t = rk t' → wdN t i = true → wdN t' i = true := by
      intro i t t' htt' hrk ht
      dsimp only [wdN] at ht ⊢
      split_ifs at ht ⊢ with hi
      · have := hwd_mono t t' htt' hrk ⟨i, hi⟩
        simp only [Bool.le_iff_imp] at this
        exact this ht
    have hpre1 : ∀ u : Fin (n + 1), ∀ w < n + 2,
        b1.wireVal (chainInput n u) w = (chainInput n u).getD w false :=
      fun u w hw => by rw [hold1 u w (lt_of_lt_of_le hw hnext0), hpre0 u w hw]
    obtain ⟨hv2, hlen2, hnx2, hni2, hnc2, hmem2, _, hget2⟩ :=
      compileTapsList_spec n rk wdN hwdN bits b1 hv1 hni1 (by omega) hlt1 hval1
        (fun u => by rw [hlen1]; exact hrk_lt u) hpre1 (List.range a)
    set taps := (compileTapsList n rk wdN bits b1 (List.range a)).1
    set b2 := (compileTapsList n rk wdN bits b1 (List.range a)).2
    refine ⟨b2.toCircuit 0, fun i => taps.getD i.val 0, hv2.1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hni2] using hv2.2
    · have hnc0 : notCount (b0.toCircuit 0) = 0 := Builder.init_notCount (n + 2)
      omega
    · have hsz : (b2.toCircuit 0).size = b2.gatesRev.length := by
        simp [Builder.toCircuit, Circuit.size, Builder.gates]
      have hnw : b2.nextWire = n + 2 + (b2.toCircuit 0).size := by
        rw [hsz, Builder.nextWire, hni2]
      simp only [Builder.toCircuit]
      omega
    · intro i
      have hsz : (b2.toCircuit 0).size = b2.gatesRev.length := by
        simp [Builder.toCircuit, Circuit.size, Builder.gates]
      have hnw : b2.nextWire = n + 2 + (b2.toCircuit 0).size := by
        rw [hsz, Builder.nextWire, hni2]
      rw [← hnw]
      have hi : i.val < taps.length := by rw [hlen2, List.length_range]; exact i.isLt
      have hmem : taps.getD i.val 0 ∈ taps := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact List.getElem_mem hi
      exact hmem2 _ hmem
    · have hfun : ∀ t : Fin (n + 1),
          (fun i : Fin a => ((b2.toCircuit 0).wires (chainInput n t)).getD (taps.getD i.val 0) false) = wd t := by
        intro t
        ext i
        have hi : i.val < (List.range a).length := by simp
        have h := hget2 t i.val hi
        simp only [List.getElem_range, wdN, i.isLt, dite_true] at h
        exact h
      simpa only [hfun] using hsum

-- 3. DP, critical thresholds q, and sparse witness subset S

def dp (a n : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (T : Finset (Fin (n + 1))) :
    ℕ → ℕ → (Fin a → Bool) → ℕ
  | 0, _, _ => 0
  | t + 1, r, w =>
    if ht : t < n + 1 then
      let tFin : Fin (n + 1) := ⟨t, ht⟩
      if tFin ∈ T then
        let cands := (Finset.range (r + 1)).biUnion (fun r' =>
          (Finset.univ.filter (fun w' : Fin a → Bool => r' < r ∨ ∀ i : Fin a, w' i ≤ w i)).image
            (fun w' => dp a n cost T t r' w' + cost tFin w'))
        cands.min' (by
          refine ⟨_, Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (Nat.lt_succ_self r),
            Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inr (fun _ => le_rfl)⟩, rfl⟩⟩⟩)
      else dp a n cost T t r w
    else dp a n cost T t r w

lemma dp_le_step {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    {T : Finset (Fin (n + 1))} {t : ℕ} (ht : t < n + 1) (hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T)
    {r r' : ℕ} {w w' : Fin a → Bool} (hrr' : r' ≤ r) (hww' : r' = r → w' ≤ w) :
    dp a n cost T (t + 1) r w ≤ dp a n cost T t r' w' + cost ⟨t, ht⟩ w' := by
  simp only [dp, dif_pos ht, if_pos hmem]
  apply Finset.min'_le
  refine Finset.mem_biUnion.mpr ⟨r', Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨w', Finset.mem_filter.mpr ⟨Finset.mem_univ w', ?_⟩, rfl⟩⟩
  by_cases heq : r' = r
  · exact Or.inr (fun i => hww' heq i)
  · exact Or.inl (by omega)

lemma dp_step_exists {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    {T : Finset (Fin (n + 1))} {t : ℕ} (ht : t < n + 1) (hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T)
    (r : ℕ) (w : Fin a → Bool) :
    ∃ r' ≤ r, ∃ w' : Fin a → Bool, (r' = r → w' ≤ w) ∧
      dp a n cost T (t + 1) r w = dp a n cost T t r' w' + cost ⟨t, ht⟩ w' := by
  simp only [dp, dif_pos ht, if_pos hmem]
  set cands := (Finset.range (r + 1)).biUnion (fun r' =>
    (Finset.univ.filter (fun w' : Fin a → Bool => r' < r ∨ ∀ i : Fin a, w' i ≤ w i)).image
      (fun w' => dp a n cost T t r' w' + cost ⟨t, ht⟩ w'))
  have hne : cands.Nonempty :=
    ⟨_, Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (Nat.lt_succ_self r),
      Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, Or.inr (fun _ => le_rfl)⟩, rfl⟩⟩⟩
  obtain ⟨r', hr', hmem'⟩ := Finset.mem_biUnion.mp (Finset.min'_mem cands hne)
  obtain ⟨w', hw', heq⟩ := Finset.mem_image.mp hmem'
  simp only [Finset.mem_range] at hr'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw'
  refine ⟨r', by omega, w', fun heqr => ?_, heq.symm⟩
  rcases hw' with hlt | hle
  · omega
  · exact hle

lemma dp_mono {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    (T : Finset (Fin (n + 1))) (t : ℕ) :
    ∀ {r₁ r₂ : ℕ} {w₁ w₂ : Fin a → Bool}, r₁ ≤ r₂ → (r₁ = r₂ → w₁ ≤ w₂) →
      dp a n cost T t r₂ w₂ ≤ dp a n cost T t r₁ w₁ := by
  induction t with
  | zero => intro _ _ _ _ _ _; simp [dp]
  | succ t ih =>
    intro r₁ r₂ w₁ w₂ hr hw
    by_cases ht : t < n + 1
    · by_cases hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T
      · obtain ⟨r', hr', w', hw', heq⟩ := dp_step_exists ht hmem r₁ w₁
        rw [heq]
        apply dp_le_step ht hmem (le_trans hr' hr)
        intro heq2
        have heq1 : r' = r₁ := by omega
        have heqr : r₁ = r₂ := by omega
        exact le_trans (hw' heq1) (hw heqr)
      · simp only [dp, dif_pos ht, if_neg hmem]
        exact ih hr hw
    · simp only [dp, dif_neg ht]
      exact ih hr hw

lemma dp_succ_ge {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    (T : Finset (Fin (n + 1))) (t r : ℕ) (w : Fin a → Bool) :
    dp a n cost T t r w ≤ dp a n cost T (t + 1) r w := by
  by_cases ht : t < n + 1
  · by_cases hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T
    · obtain ⟨r', hr', w', hw', heq⟩ := dp_step_exists ht hmem r w
      rw [heq]
      exact le_trans (dp_mono T t hr' hw') (Nat.le_add_right _ _)
    · simp [dp, ht, hmem]
  · simp [dp, ht]

lemma dp_zero_eq {n : ℕ} {cost : Fin (n + 1) → (Fin 0 → Bool) → ℕ}
    (T : Finset (Fin (n + 1))) (t r : ℕ) (w : Fin 0 → Bool) :
    dp 0 n cost T t r w = dp 0 n cost T t 0 w := by
  induction t generalizing r w with
  | zero => simp [dp]
  | succ t ih =>
    by_cases ht : t < n + 1
    · by_cases hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T
      · apply le_antisymm
        · exact dp_mono T (t + 1) (Nat.zero_le r) (fun _ i => Fin.elim0 i)
        · obtain ⟨r', _, w', _, heq⟩ := dp_step_exists ht hmem r w
          rw [heq, ih r' w']
          exact dp_le_step ht hmem (Nat.zero_le 0) (fun _ i => Fin.elim0 i)
      · simp only [dp, dif_pos ht, if_neg hmem]
        exact ih r w
    · simp only [dp, dif_neg ht]
      exact ih r w

lemma dp_filter_lt {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    (S : Finset (Fin (n + 1))) (k : ℕ) (hk : k ≤ n + 1) (r : ℕ) (w : Fin a → Bool) :
    dp a n cost (S.filter (fun t => t.val < k)) (n + 1) r w = dp a n cost S k r w := by
  have hge : ∀ t, k ≤ t → dp a n cost (S.filter (fun u => u.val < k)) t r w =
      dp a n cost (S.filter (fun u => u.val < k)) k r w := by
    intro t ht
    induction t with
    | zero => rcases Nat.eq_zero_of_le_zero ht with rfl; rfl
    | succ t ih =>
      by_cases htk : k ≤ t
      · rw [← ih htk]
        by_cases htn : t < n + 1
        · have hnot : (⟨t, htn⟩ : Fin (n + 1)) ∉ S.filter (fun u => u.val < k) := by
            simp only [Finset.mem_filter, not_and]; intro _; omega
          simp [dp, htn, hnot]
        · simp [dp, htn]
      · have : t + 1 = k := by omega
        rw [this]
  have hle : ∀ t, t ≤ k → ∀ (r : ℕ) (w : Fin a → Bool),
      dp a n cost (S.filter (fun u => u.val < k)) t r w = dp a n cost S t r w := by
    intro t
    induction t with
    | zero => intro _ _ _; simp [dp]
    | succ t ih =>
      intro ht r w
      have htn : t < n + 1 := by omega
      have htk : t < k := by omega
      have hiff : (⟨t, htn⟩ : Fin (n + 1)) ∈ S.filter (fun u => u.val < k) ↔
          (⟨t, htn⟩ : Fin (n + 1)) ∈ S := by
        simp [Finset.mem_filter, htk]
      by_cases hmem : (⟨t, htn⟩ : Fin (n + 1)) ∈ S
      · have hmem' : (⟨t, htn⟩ : Fin (n + 1)) ∈ S.filter (fun u => u.val < k) := hiff.mpr hmem
        apply le_antisymm
        · obtain ⟨r', hr', w', hw', heq⟩ := dp_step_exists htn hmem r w
          rw [heq, ← ih (by omega) r' w']
          exact dp_le_step htn hmem' hr' hw'
        · obtain ⟨r', hr', w', hw', heq⟩ := dp_step_exists htn hmem' r w
          rw [heq, ih (by omega) r' w']
          exact dp_le_step htn hmem hr' hw'
      · have hmem' : (⟨t, htn⟩ : Fin (n + 1)) ∉ S.filter (fun u => u.val < k) := by
          rw [hiff]; exact hmem
        simp only [dp, dif_pos htn, if_neg hmem, if_neg hmem']
        exact ih (by omega) r w
  rw [hge (n + 1) hk, hle k le_rfl r w]

lemma dp_le_of_schedule {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    {T : Finset (Fin (n + 1))} {rk : Fin (n + 1) → ℕ} {wd : Fin (n + 1) → (Fin a → Bool)}
    (hrk : Monotone rk) (hwd : ∀ t t', t ≤ t' → rk t = rk t' → wd t ≤ wd t') :
    ∀ (t : ℕ), t ≤ n + 1 → ∀ (r : ℕ) (w : Fin a → Bool),
      (∀ u : Fin (n + 1), u.val < t → rk u ≤ r ∧ (rk u = r → wd u ≤ w)) →
      dp a n cost T t r w ≤ (T.filter (fun u => u.val < t)).sum (fun u => cost u (wd u)) := by
  intro t
  induction t with
  | zero => intro _ _ _ _; simp [dp]
  | succ t ih =>
    intro htn r w hbound
    have ht : t < n + 1 := by omega
    have hsplit : (T.filter (fun u => u.val < t + 1)).sum (fun u => cost u (wd u)) =
        (T.filter (fun u => u.val < t)).sum (fun u => cost u (wd u)) +
        if (⟨t, ht⟩ : Fin (n + 1)) ∈ T then cost ⟨t, ht⟩ (wd ⟨t, ht⟩) else 0 := by
      have hsub : T.filter (fun u => u.val < t + 1) =
          if (⟨t, ht⟩ : Fin (n + 1)) ∈ T then insert ⟨t, ht⟩ (T.filter (fun u => u.val < t))
          else T.filter (fun u => u.val < t) := by
        ext u
        split_ifs with hmem
        · simp only [Finset.mem_insert, Finset.mem_filter, Fin.ext_iff]
          constructor
          · rintro ⟨huT, hut⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hut with hlt | heq
            · exact Or.inr ⟨huT, hlt⟩
            · exact Or.inl heq
          · rintro (heq | ⟨huT, hlt⟩)
            · have : u = ⟨t, ht⟩ := Fin.ext heq
              subst this
              exact ⟨hmem, by omega⟩
            · exact ⟨huT, by omega⟩
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨huT, hut⟩
            refine ⟨huT, ?_⟩
            by_contra hnot
            have : u = ⟨t, ht⟩ := Fin.ext (by dsimp; omega)
            subst this
            exact hmem huT
          · rintro ⟨huT, hut⟩
            exact ⟨huT, by omega⟩
      rw [hsub]
      split_ifs with hmem
      · rw [Finset.sum_insert (by simp), Nat.add_comm]
      · simp
    rw [hsplit]
    have hbt := hbound ⟨t, ht⟩ (by simp)
    by_cases hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T
    · rw [if_pos hmem]
      calc dp a n cost T (t + 1) r w
          ≤ dp a n cost T t (rk ⟨t, ht⟩) (wd ⟨t, ht⟩) + cost ⟨t, ht⟩ (wd ⟨t, ht⟩) :=
            dp_le_step ht hmem hbt.1 hbt.2
        _ ≤ (T.filter (fun u => u.val < t)).sum (fun u => cost u (wd u)) + cost ⟨t, ht⟩ (wd ⟨t, ht⟩) := by
            apply Nat.add_le_add_right
            apply ih (by omega) (rk ⟨t, ht⟩) (wd ⟨t, ht⟩)
            intro u hu
            have hut : u ≤ ⟨t, ht⟩ := Nat.le_of_lt hu
            exact ⟨hrk hut, fun heq => hwd u ⟨t, ht⟩ hut heq⟩
    · rw [if_neg hmem, Nat.add_zero]
      simp only [dp, dif_pos ht, if_neg hmem]
      apply ih (by omega) r w
      intro u hu
      exact hbound u (by omega)

lemma schedule_of_dp_le {a n : ℕ} {cost : Fin (n + 1) → (Fin a → Bool) → ℕ}
    {T : Finset (Fin (n + 1))} :
    ∀ (t : ℕ), t ≤ n + 1 → ∀ (r : ℕ) (w : Fin a → Bool),
      ∃ (rk : Fin (n + 1) → ℕ) (wd : Fin (n + 1) → (Fin a → Bool)),
        (∀ u, rk u ≤ r) ∧
        (∀ u, rk u = r → wd u ≤ w) ∧
        Monotone rk ∧
        (∀ u v, u ≤ v → rk u = rk v → wd u ≤ wd v) ∧
        (T.filter (fun u => u.val < t)).sum (fun u => cost u (wd u)) ≤ dp a n cost T t r w := by
  intro t
  induction t with
  | zero =>
    intro _ r w
    refine ⟨fun _ => r, fun _ => w, fun _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => le_rfl, fun _ _ _ _ => le_rfl, by simp [dp]⟩
  | succ t ih =>
    intro htn r w
    have ht : t < n + 1 := by omega
    by_cases hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ T
    · obtain ⟨r', hr', w', hw', heq⟩ := dp_step_exists ht hmem r w
      obtain ⟨rk', wd', hrk', hwd', hmono', hstep', hsum'⟩ := ih (by omega) r' w'
      let rk : Fin (n + 1) → ℕ := fun u => if u.val < t then rk' u else if u.val = t then r' else r
      let wd : Fin (n + 1) → (Fin a → Bool) := fun u => if u.val < t then wd' u else if u.val = t then w' else w
      refine ⟨rk, wd, ?_, ?_, ?_, ?_, ?_⟩
      · intro u; dsimp only [rk]; split_ifs <;> [exact le_trans (hrk' u) hr'; exact hr'; exact le_rfl]
      · intro u hu; dsimp only [rk, wd] at hu ⊢
        split_ifs at hu ⊢
        · have := hrk' u; have : rk' u = r' := by omega
          exact le_trans (hwd' u this) (hw' (by omega))
        · exact hw' hu
        · exact le_rfl
      · intro u v huv
        dsimp only [rk]
        split_ifs with hu1 hv1 hv2 hu2 hv3 hv4
        · exact hmono' huv
        · exact hrk' u
        · exact le_trans (hrk' u) hr'
        · omega
        · exact le_rfl
        · exact hr'
        · omega
        · omega
        · exact le_rfl
      · intro u v huv heq_uv
        have huv' : u.val ≤ v.val := huv
        dsimp only [rk, wd] at heq_uv ⊢
        split_ifs at heq_uv ⊢ with hu1 hv1 hv2 hu2 hv3 hv4
        · exact hstep' u v huv heq_uv
        · exact hwd' u heq_uv
        · have := hrk' u; have : rk' u = r' := by omega
          exact le_trans (hwd' u this) (hw' (by omega))
        · omega
        · exact le_rfl
        · exact hw' heq_uv
        · omega
        · omega
        · exact le_rfl
      · rw [heq]
        have hsub : T.filter (fun u => u.val < t + 1) = insert (⟨t, ht⟩ : Fin (n + 1)) (T.filter (fun u => u.val < t)) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
          constructor
          · rintro ⟨huT, hut⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hut with hlt | heq
            · exact Or.inr ⟨huT, hlt⟩
            · exact Or.inl heq
          · rintro (heq | ⟨huT, hlt⟩)
            · have : u = ⟨t, ht⟩ := Fin.ext heq
              subst this
              exact ⟨hmem, by omega⟩
            · exact ⟨huT, by omega⟩
        rw [hsub, Finset.sum_insert (by simp), Nat.add_comm]
        have hsum_eq : (T.filter (fun u => u.val < t)).sum (fun u => cost u (wd u)) =
            (T.filter (fun u => u.val < t)).sum (fun u => cost u (wd' u)) := by
          apply Finset.sum_congr rfl
          intro u hu
          simp only [Finset.mem_filter] at hu
          simp [wd, hu.2]
        rw [hsum_eq]
        have hwt : wd ⟨t, ht⟩ = w' := by simp [wd]
        rw [hwt]
        exact Nat.add_le_add_right hsum' _
    · obtain ⟨rk', wd', hrk', hwd', hmono', hstep', hsum'⟩ := ih (by omega) r w
      refine ⟨rk', wd', hrk', hwd', hmono', hstep', ?_⟩
      simp only [dp, dif_pos ht, if_neg hmem]
      have hsub : T.filter (fun u => u.val < t + 1) = T.filter (fun u => u.val < t) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨huT, hut⟩
          refine ⟨huT, ?_⟩
          by_contra hnot
          have : u = ⟨t, ht⟩ := Fin.ext (by dsimp; omega)
          subst this
          exact hmem huT
        · rintro ⟨huT, hut⟩; exact ⟨huT, by omega⟩
      rw [hsub]
      exact hsum'

lemma hasSchedule_iff_dp (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) :
    HasSchedule a n b e cost T ↔ ∃ r < 2 ^ b, ∃ w : Fin a → Bool, dp a n cost T (n + 1) r w ≤ e := by
  constructor
  · rintro ⟨rk, wd, hrk_lt, hrk_mono, hwd_mono, hsum⟩
    let rMax := rk ⟨n, Nat.lt_succ_self n⟩
    let wMax := wd ⟨n, Nat.lt_succ_self n⟩
    refine ⟨rMax, hrk_lt _, wMax, ?_⟩
    have hle := dp_le_of_schedule (cost := cost) (T := T) hrk_mono hwd_mono (n + 1) le_rfl rMax wMax (fun u _ =>
      ⟨hrk_mono (Nat.le_of_lt_succ u.isLt), fun heq => hwd_mono u ⟨n, Nat.lt_succ_self n⟩ (Nat.le_of_lt_succ u.isLt) heq⟩)
    have hT : T.filter (fun u : Fin (n + 1) => u.val < n + 1) = T := by
      ext u; simp [Finset.mem_filter]; omega
    rw [hT] at hle
    exact le_trans hle hsum
  · rintro ⟨r, hr, w, hdp⟩
    obtain ⟨rk, wd, hrk_le, _, hmono, hstep, hsum⟩ := schedule_of_dp_le (a := a) (n := n) (cost := cost) (T := T) (n + 1) le_rfl r w
    refine ⟨rk, wd, fun u => lt_of_le_of_lt (hrk_le u) hr, hmono, hstep, ?_⟩
    have hT : T.filter (fun u : Fin (n + 1) => u.val < n + 1) = T := by
      ext u; simp [Finset.mem_filter]; omega
    rw [hT] at hsum
    exact le_trans hsum hdp

def band : ℕ → ℕ
  | 0 => 0
  | r + 1 => band ((r + 1) / 2) + 1

lemma band_lt_pow (r : ℕ) : r < 2 ^ band r := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    cases r with
    | zero => simp [band]
    | succ r =>
      have hlt : (r + 1) / 2 < r + 1 := Nat.div_lt_self (Nat.succ_pos r) (by omega)
      have ih' := ih ((r + 1) / 2) hlt
      simp only [band, pow_succ]
      omega

lemma band_le_pow (r : ℕ) (hr : 0 < r) : 2 ^ (band r - 1) ≤ r := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    cases r with
    | zero => omega
    | succ r =>
      by_cases h1 : (r + 1) / 2 = 0
      · have : r = 0 := by omega
        subst this
        simp [band]
      · have hlt : (r + 1) / 2 < r + 1 := Nat.div_lt_self (Nat.succ_pos r) (by omega)
        have ih' := ih ((r + 1) / 2) hlt (by omega)
        simp only [band, Nat.add_sub_cancel]
        have hb : 1 ≤ band ((r + 1) / 2) := by
          cases hdiv : (r + 1) / 2
          · exact absurd hdiv h1
          · simp [band]
        have hpow : band ((r + 1) / 2) = (band ((r + 1) / 2) - 1) + 1 := by omega
        conv_lhs => rw [hpow, pow_succ]
        have hdiv_pow : 2 ^ (band ((r + 1) / 2) - 1) * 2 ≤ ((r + 1) / 2) * 2 := Nat.mul_le_mul_right 2 ih'
        exact le_trans hdiv_pow (Nat.div_mul_le_self (r + 1) 2)

lemma band_le_of_lt_pow {r B : ℕ} (h : r < 2 ^ B) : band r ≤ B := by
  cases r with
  | zero => simp [band]
  | succ r =>
    by_contra hgt
    have h1 : B ≤ band (r + 1) - 1 := by omega
    have h2 : 2 ^ B ≤ 2 ^ (band (r + 1) - 1) := Nat.pow_le_pow_right (by omega) h1
    have h3 := band_le_pow (r + 1) (Nat.succ_pos r)
    omega

lemma band_eq_iff_Ico (r j : ℕ) : band r = j + 1 ↔ 2 ^ j ≤ r ∧ r < 2 ^ (j + 1) := by
  constructor
  · intro h
    have hr : 0 < r := by
      cases r with
      | zero => simp [band] at h
      | succ _ => exact Nat.succ_pos _
    have h1 := band_le_pow r hr
    have h2 := band_lt_pow r
    rw [h] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hle : band r ≤ j + 1 := band_le_of_lt_pow h2
    have hge : j + 1 ≤ band r := by
      by_contra hlt
      have : 2 ^ band r ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      have := band_lt_pow r
      omega
    omega

lemma card_filter_mono_lt {n M : ℕ} (f : ℕ → ℕ) (hf : ∀ t, f t ≤ f (t + 1)) :
    (Finset.univ.filter (fun t : Fin (n + 1) => f t.val < f (t.val + 1) ∧ f t.val < M)).card ≤ M := by
  have hmono : Monotone f := monotone_nat_of_le_succ hf
  conv_rhs => rw [← Finset.card_range M]
  apply Finset.card_le_card_of_injOn (fun t : Fin (n + 1) => f t.val)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Finset.mem_range] at ht ⊢
    exact ht.2
  · intro t₁ ht₁ t₂ ht₂ heq
    dsimp only at heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at ht₁ ht₂
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have : f (t₁.val + 1) ≤ f t₂.val := hmono hlt
      omega
    · have : f (t₂.val + 1) ≤ f t₁.val := hmono hlt
      omega

def minDp (a n : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (b : ℕ) : ℕ :=
  ((Finset.range (2 ^ b)).biUnion (fun r =>
    Finset.univ.image (fun w : Fin a → Bool => dp a n cost Finset.univ (n + 1) r w))).min'
    (⟨_, Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by positivity),
      Finset.mem_image.mpr ⟨default, Finset.mem_univ _, rfl⟩⟩⟩)

lemma minDp_le_iff (a n : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (b e : ℕ) :
    minDp a n cost b ≤ e ↔ ∃ r < 2 ^ b, ∃ w : Fin a → Bool, dp a n cost Finset.univ (n + 1) r w ≤ e := by
  unfold minDp
  set s := (Finset.range (2 ^ b)).biUnion (fun r =>
    Finset.univ.image (fun w : Fin a → Bool => dp a n cost Finset.univ (n + 1) r w))
  have hne : s.Nonempty :=
    ⟨_, Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by positivity),
      Finset.mem_image.mpr ⟨default, Finset.mem_univ _, rfl⟩⟩⟩
  constructor
  · intro h
    obtain ⟨r, hr, hw⟩ := Finset.mem_biUnion.mp (Finset.min'_mem s hne)
    obtain ⟨w, _, heq⟩ := Finset.mem_image.mp hw
    simp only [Finset.mem_range] at hr
    exact ⟨r, hr, w, le_trans (le_of_eq heq) h⟩
  · rintro ⟨r, hr, w, hle⟩
    have hmem : dp a n cost Finset.univ (n + 1) r w ∈ s :=
      Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr,
        Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩⟩
    exact le_trans (Finset.min'_le s _ hmem) hle

lemma minDp_antitone (a n : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    minDp a n cost b₂ ≤ minDp a n cost b₁ := by
  rw [minDp_le_iff]
  obtain ⟨r, hr, w, hle⟩ := (minDp_le_iff a n cost b₁ (minDp a n cost b₁)).mp le_rfl
  exact ⟨r, lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) h), w, hle⟩

end PEqualNP.Outside.L_meta_53175_aux

open PEqualNP.Outside.L_meta_53175_aux

theorem PEqualNP.Outside.L_meta_53175 :
  let fit := fun (a n b e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
      (S : Finset (Fin (n+1))) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
      S.sum (fun t => cost t (fun i => (C.wires
        (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e
  ∀ (n a B E : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat),
    ∃ (q : Nat → Nat) (S : Finset (Fin (n+1))),
      S.card ≤ (if a = 0 then q 0 else 2^a *
        (q 0 + (Finset.range B).sum (fun j => 2^j * q (j+1)))) ∧
      ∀ b ≤ B, q b ≤ E+1 ∧ ∀ e ≤ E,
        (fit a n b e cost Finset.univ ↔ q b ≤ e) ∧
        ∀ k : Nat, fit a n b e cost (Finset.univ.filter (fun t => t.val < k)) ↔
          fit a n b e cost (S.filter (fun t => t.val < k)) := by
  intro fit n a B E cost
  let q : ℕ → ℕ := fun b => min (minDp a n cost b) (E + 1)
  have hq_anti : ∀ {b₁ b₂ : ℕ}, b₁ ≤ b₂ → q b₂ ≤ q b₁ := fun h =>
    min_le_min (minDp_antitone a n cost h) le_rfl
  let Rlim : ℕ := if a = 0 then 1 else 2 ^ B
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun t =>
    ∃ r < Rlim, ∃ w : Fin a → Bool,
      dp a n cost Finset.univ t.val r w < dp a n cost Finset.univ (t.val + 1) r w ∧
      dp a n cost Finset.univ t.val r w < q (band r))
  refine ⟨q, S, ?_, ?_⟩
  · have hS_sub : S ⊆ (Finset.range Rlim).biUnion (fun r =>
        Finset.univ.biUnion (fun w : Fin a → Bool =>
          Finset.univ.filter (fun t : Fin (n + 1) =>
            dp a n cost Finset.univ t.val r w < dp a n cost Finset.univ (t.val + 1) r w ∧
            dp a n cost Finset.univ t.val r w < q (band r)))) := by
      intro t ht
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨r, hr, w, h1, h2⟩ := ht
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr,
        Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w,
          Finset.mem_filter.mpr ⟨Finset.mem_univ t, h1, h2⟩⟩⟩
    have hcard_le : S.card ≤ (Finset.range Rlim).sum (fun r =>
        (Finset.univ : Finset (Fin a → Bool)).sum (fun _ => q (band r))) := by
      calc S.card
          ≤ ((Finset.range Rlim).biUnion (fun r =>
              Finset.univ.biUnion (fun w : Fin a → Bool =>
                Finset.univ.filter (fun t : Fin (n + 1) =>
                  dp a n cost Finset.univ t.val r w < dp a n cost Finset.univ (t.val + 1) r w ∧
                  dp a n cost Finset.univ t.val r w < q (band r))))).card := Finset.card_le_card hS_sub
        _ ≤ (Finset.range Rlim).sum (fun r =>
              (Finset.univ.biUnion (fun w : Fin a → Bool =>
                Finset.univ.filter (fun t : Fin (n + 1) =>
                  dp a n cost Finset.univ t.val r w < dp a n cost Finset.univ (t.val + 1) r w ∧
                  dp a n cost Finset.univ t.val r w < q (band r)))).card) := Finset.card_biUnion_le
        _ ≤ (Finset.range Rlim).sum (fun r =>
              (Finset.univ : Finset (Fin a → Bool)).sum (fun w =>
                (Finset.univ.filter (fun t : Fin (n + 1) =>
                  dp a n cost Finset.univ t.val r w < dp a n cost Finset.univ (t.val + 1) r w ∧
                  dp a n cost Finset.univ t.val r w < q (band r))).card)) := by
              apply Finset.sum_le_sum
              intro r _
              exact Finset.card_biUnion_le
        _ ≤ (Finset.range Rlim).sum (fun r =>
              (Finset.univ : Finset (Fin a → Bool)).sum (fun _ => q (band r))) := by
              apply Finset.sum_le_sum; intro r _
              apply Finset.sum_le_sum; intro w _
              exact card_filter_mono_lt (fun t => dp a n cost Finset.univ t r w)
                (fun t => dp_succ_ge Finset.univ t r w)
    have hsum_w : ∀ r, (Finset.univ : Finset (Fin a → Bool)).sum (fun _ => q (band r)) =
        2 ^ a * q (band r) := by
      intro r
      simp [Finset.sum_const, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp_rw [hsum_w] at hcard_le
    by_cases ha : a = 0
    · subst ha
      simp only [Rlim, ↓reduceIte, Finset.range_one, Finset.sum_singleton, band, pow_zero, Nat.one_mul] at hcard_le ⊢
      exact hcard_le
    · simp only [Rlim, if_neg ha, if_neg ha] at hcard_le ⊢
      rw [← Finset.mul_sum] at hcard_le
      refine le_trans hcard_le (Nat.mul_le_mul_left (2 ^ a) ?_)
      have hpart : Finset.range (2 ^ B) =
          insert 0 ((Finset.range B).biUnion (fun j => Finset.Ico (2 ^ j) (2 ^ (j + 1)))) := by
        ext r
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Ico]
        constructor
        · intro hr
          by_cases hr0 : r = 0
          · exact Or.inl hr0
          · right
            refine ⟨band r - 1, ?_, ?_, ?_⟩
            · have hb := band_le_of_lt_pow hr
              cases hb0 : band r with
              | zero =>
                have := band_lt_pow r
                rw [hb0] at this
                omega
              | succ m => omega
            · exact band_le_pow r (by omega)
            · have : band r - 1 + 1 = band r := by
                cases hb0 : band r with
                | zero => have := band_lt_pow r; rw [hb0] at this; omega
                | succ m => omega
              rw [this]
              exact band_lt_pow r
        · rintro (rfl | ⟨j, hjB, _, hr⟩)
          · positivity
          · exact lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hjB)
      rw [hpart, Finset.sum_insert (by simp)]
      simp only [band]
      apply Nat.add_le_add_left
      rw [Finset.sum_biUnion]
      · apply Finset.sum_le_sum
        intro j _
        have hcongr : (Finset.Ico (2 ^ j) (2 ^ (j + 1))).sum (fun r => q (band r)) =
            (Finset.Ico (2 ^ j) (2 ^ (j + 1))).sum (fun _ => q (j + 1)) := by
          apply Finset.sum_congr rfl
          intro r hr
          simp only [Finset.mem_Ico] at hr
          rw [(band_eq_iff_Ico r j).mpr hr]
        rw [hcongr, Finset.sum_const, Nat.card_Ico]
        have hcard_ico : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
        rw [hcard_ico, smul_eq_mul]
      · intro j₁ _ j₂ _ hne
        simp only [Finset.disjoint_left, Finset.mem_Ico]
        intro r h1 h2
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have : 2 ^ (j₁ + 1) ≤ 2 ^ j₂ := Nat.pow_le_pow_right (by omega) hlt
          omega
        · have : 2 ^ (j₂ + 1) ≤ 2 ^ j₁ := Nat.pow_le_pow_right (by omega) hlt
          omega
  · intro b hbB
    refine ⟨min_le_right _ _, fun e heE => ?_⟩
    have hfit_iff : ∀ T, fit a n b e cost T ↔ HasSchedule a n b e cost T := fun T => by
      simpa only [fit, chainInput] using fit_iff_schedule a n b e cost T
    refine ⟨?_, ?_⟩
    · rw [hfit_iff, hasSchedule_iff_dp, ← minDp_le_iff]
      simp only [q, min_le_iff]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h); exact h; omega
    · intro k
      constructor
      · intro hfit
        rw [hfit_iff] at hfit ⊢
        obtain ⟨rk, wd, h1, h2, h3, h4⟩ := hfit
        refine ⟨rk, wd, h1, h2, h3, le_trans (Finset.sum_le_sum_of_subset ?_) h4⟩
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact ht.2
      · intro hfit
        by_cases hqe : q b ≤ e
        · have hfit_univ : fit a n b e cost Finset.univ := by
            rw [hfit_iff, hasSchedule_iff_dp, ← minDp_le_iff]
            have : q b ≤ e := hqe
            simp only [q, min_le_iff] at this
            rcases this with h | h; exact h; omega
          rw [hfit_iff] at hfit_univ ⊢
          obtain ⟨rk, wd, h1, h2, h3, h4⟩ := hfit_univ
          exact ⟨rk, wd, h1, h2, h3, le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) h4⟩
        · have heq_lt : e < q b := by omega
          have hprefix : ∀ t ≤ n + 1, ∀ r < 2 ^ b, ∀ w : Fin a → Bool,
              min (dp a n cost Finset.univ t r w) (q b) ≤ dp a n cost S t r w := by
            intro t
            induction t with
            | zero => intro _ _ _ _; simp [dp]
            | succ t ih =>
              intro htn r' hr' w'
              have ht : t < n + 1 := by omega
              by_cases hmem : (⟨t, ht⟩ : Fin (n + 1)) ∈ S
              · obtain ⟨r'', hr'', w'', _, heq⟩ := dp_step_exists ht hmem r' w'
                rw [heq]
                have h1 : dp a n cost Finset.univ (t + 1) r' w' ≤
                    dp a n cost Finset.univ t r'' w'' + cost ⟨t, ht⟩ w'' :=
                  dp_le_step ht (Finset.mem_univ _) hr'' (by assumption)
                have h2 := ih (by omega) r'' (lt_of_le_of_lt hr'' hr') w''
                omega
              · conv_rhs => simp only [dp, dif_pos ht, if_neg hmem]
                have ih' := ih (by omega) r' hr' w'
                by_cases ha0 : a = 0
                · subst ha0
                  have hnotS : ¬ (dp 0 n cost Finset.univ t 0 w' < dp 0 n cost Finset.univ (t + 1) 0 w' ∧
                      dp 0 n cost Finset.univ t 0 w' < q (band 0)) := by
                    intro hbad
                    apply hmem
                    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨0, by simp [Rlim], w', hbad.1, hbad.2⟩
                  rw [dp_zero_eq Finset.univ (t + 1) r' w']
                  have hqb0 : q b ≤ q (band 0) := hq_anti (by simp [band])
                  have hle_succ := dp_succ_ge (cost := cost) Finset.univ t 0 w'
                  rw [dp_zero_eq Finset.univ t r' w'] at ih'
                  omega
                · have hnotS : ¬ (dp a n cost Finset.univ t r' w' < dp a n cost Finset.univ (t + 1) r' w' ∧
                      dp a n cost Finset.univ t r' w' < q (band r')) := by
                    intro hbad
                    apply hmem
                    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                    have hrB : r' < Rlim := by
                      simp only [Rlim, if_neg ha0]
                      exact lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by omega) hbB)
                    exact ⟨r', hrB, w', hbad.1, hbad.2⟩
                  have hqb : q b ≤ q (band r') := hq_anti (band_le_of_lt_pow hr')
                  have hle_succ := dp_succ_ge (cost := cost) Finset.univ t r' w'
                  omega
          by_cases hk : k ≤ n + 1
          · rw [hfit_iff, hasSchedule_iff_dp] at hfit
            simp_rw [dp_filter_lt S k hk] at hfit
            obtain ⟨r, hr, w, hdpS⟩ := hfit
            have hmin := hprefix k hk r hr w
            have hdp_univ : dp a n cost Finset.univ k r w ≤ e := by omega
            rw [hfit_iff, hasSchedule_iff_dp]
            simp_rw [dp_filter_lt Finset.univ k hk]
            exact ⟨r, hr, w, hdp_univ⟩
          · have hk_gt : n + 1 ≤ k := by omega
            have hS_eq : S.filter (fun t => t.val < k) = S := by
              ext t; simp only [Finset.mem_filter]; constructor; exact And.left; intro ht; exact ⟨ht, lt_of_lt_of_le t.isLt hk_gt⟩
            have hU_eq : (Finset.univ : Finset (Fin (n + 1))).filter (fun t => t.val < k) = Finset.univ := by
              ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact iff_true_intro (lt_of_lt_of_le t.isLt hk_gt)
            rw [hS_eq] at hfit
            rw [hU_eq]
            rw [hfit_iff] at hfit ⊢
            obtain ⟨rk, wd, h1, h2, h3, h4⟩ := hfit
            have hdp : ∃ r < 2 ^ b, ∃ w : Fin a → Bool, dp a n cost S (n + 1) r w ≤ e :=
              (hasSchedule_iff_dp a n b e cost S).mp ⟨rk, wd, h1, h2, h3, h4⟩
            obtain ⟨r, hr, w, hdpS⟩ := hdp
            have hmin := hprefix (n + 1) le_rfl r hr w
            have hdp_univ : dp a n cost Finset.univ (n + 1) r w ≤ e := by omega
            exact (hasSchedule_iff_dp a n b e cost Finset.univ).mpr ⟨r, hr, w, hdp_univ⟩
