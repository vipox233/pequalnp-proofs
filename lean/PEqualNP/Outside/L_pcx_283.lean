import Mathlib
import PEqualNP.Defs

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_pcx_283_aux

def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: tl => b.toNat + 2 * bitsVal tl

def msbVal : List Bool → ℕ
  | [] => 0
  | b :: tl => b.toNat * 2 ^ tl.length + msbVal tl

lemma bitsVal_nil : bitsVal [] = 0 := rfl

lemma bitsVal_cons (b : Bool) (tl : List Bool) :
    bitsVal (b :: tl) = b.toNat + 2 * bitsVal tl := rfl

lemma bitsVal_append (l1 l2 : List Bool) :
    bitsVal (l1 ++ l2) = bitsVal l1 + 2 ^ l1.length * bitsVal l2 := by
  induction l1 with
  | nil => simp [bitsVal]
  | cons b tl ih =>
    simp only [List.cons_append, bitsVal, List.length_cons, pow_succ, ih]
    ring

lemma bitsVal_lt (l : List Bool) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal]
  | cons b tl ih =>
    simp only [bitsVal, List.length_cons, pow_succ]
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    omega

lemma bitsVal_replicate_false (n : ℕ) : bitsVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bitsVal, ih]

lemma bitsVal_testBit (l : List Bool) (i : ℕ) :
    (bitsVal l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [bitsVal]
  | cons b tl ih =>
    cases i with
    | zero =>
      simp only [bitsVal, List.getD_cons_zero]
      cases b <;> simp [Nat.testBit_zero]
    | succ j =>
      simp only [bitsVal, List.getD_cons_succ]
      rw [Nat.testBit_succ]
      have hdiv : (b.toNat + 2 * bitsVal tl) / 2 = bitsVal tl := by
        cases b
        · simp
        · simp; omega
      rw [hdiv, ih j]

lemma bitsVal_take_of_lt (l : List Bool) (n : ℕ) (h : bitsVal l < 2 ^ n) :
    bitsVal (l.take n) = bitsVal l := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsVal_testBit, bitsVal_testBit]
  by_cases hi : i < n
  · by_cases hl : i < l.length
    · have hlt : i < (l.take n).length := by simp [hi, hl]
      rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hl, List.getElem_take]
    · have hge1 : (l.take n).length ≤ i := by
        have : (l.take n).length ≤ l.length := by simp
        omega
      rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ (by omega)]
  · have hge1 : (l.take n).length ≤ i := by
      have : (l.take n).length ≤ n := List.length_take_le n l
      omega
    rw [List.getD_eq_default _ _ hge1]
    have hfalse : (bitsVal l).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
    rw [← bitsVal_testBit, hfalse]

lemma msbVal_reverse (l : List Bool) : msbVal l.reverse = bitsVal l := by
  induction l with
  | nil => rfl
  | cons b tl ih =>
    have happ : ∀ (a : List Bool) (x : Bool),
        msbVal (a ++ [x]) = 2 * msbVal a + x.toNat := by
      intro a x
      induction a with
      | nil => simp [msbVal]
      | cons c cs ihc =>
        simp only [List.cons_append, msbVal, List.length_append, List.length_singleton, ihc, pow_succ]
        ring
    rw [List.reverse_cons, happ, ih, bitsVal]
    ring

lemma bitsVal_map_not (l : List Bool) :
    bitsVal (l.map (!·)) + bitsVal l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal]
  | cons b tl ih =>
    simp only [List.map_cons, bitsVal, List.length_cons, pow_succ]
    have hb : (!b).toNat + b.toNat = 1 := by cases b <;> decide
    omega

lemma bitsVal_ofFn_eq_sum {n : ℕ} (f : Fin n → Bool) :
    bitsVal (List.ofFn f) = ∑ j : Fin n, if f j then 2 ^ j.val else 0 := by
  induction n with
  | zero => simp [bitsVal]
  | succ n ih =>
    rw [List.ofFn_succ, bitsVal, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, Finset.mul_sum]
    have h0 : (f 0).toNat = if f 0 then 1 else 0 := by cases f 0 <;> decide
    rw [h0]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring

lemma bitsVal_ofFn_testBit (n x : ℕ) (hx : x < 2 ^ n) :
    bitsVal (List.ofFn (fun i : Fin n => x.testBit i.val)) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitsVal_testBit]
  by_cases hj : j < n
  · have hlt : j < (List.ofFn (fun i : Fin n => x.testBit i.val)).length := by simp [hj]
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  · have hge : (List.ofFn (fun i : Fin n => x.testBit i.val)).length ≤ j := by simp; omega
    rw [List.getD_eq_default _ _ hge]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))).symm

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g tl ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, List.foldl_append]

lemma wiresOf_getD_prefix (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g tl ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    have hi' : i < (x ++ [g.op.eval (g.inputs.map fun k => x.getD k false)]).length := by
      simp; omega
    rw [ih _ hi', List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi,
      List.getElem_append_left hi]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
    g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_length gs x
  simp only [wiresOf, List.foldl_cons, List.foldl_nil]
  have hlt : x.length + gs.length < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
    simp [hlen]
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by omega)]
  simp [hlen]

abbrev FanIn2 (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

structure CB (n : ℕ) where
  gates : List Gate
  hback : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨.or, []⟩).inputs, i < n + j
  hfan : ∀ g ∈ gates, FanIn2 g

def CB.size {n : ℕ} (c : CB n) : ℕ := c.gates.length

def CB.toCircuit {n : ℕ} (c : CB n) : Circuit := ⟨c.gates, 0⟩

def CB.eval {n : ℕ} (c : CB n) (x : List Bool) (w : ℕ) : Bool :=
  (wiresOf c.gates x).getD w false

lemma CB.valid {n budget : ℕ} (c : CB n) (hsz : c.size ≤ budget) :
    ReadsBack n c.toCircuit ∧ c.toCircuit.size ≤ budget ∧
    ∀ g ∈ c.toCircuit.gates,
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1) :=
  ⟨c.hback, hsz, c.hfan⟩

lemma CB.eval_input {n : ℕ} (c : CB n) {x : List Bool} (hx : x.length = n) {i : ℕ} (hi : i < n) :
    c.eval x i = x.getD i false :=
  wiresOf_getD_prefix c.gates x (by omega)

def CB.Extends {n : ℕ} (c1 c2 : CB n) : Prop :=
  ∃ extra : List Gate, c2.gates = c1.gates ++ extra

lemma CB.Extends.refl {n : ℕ} (c : CB n) : c.Extends c :=
  ⟨[], by simp⟩

lemma CB.Extends.trans {n : ℕ} {c1 c2 c3 : CB n}
    (h1 : c1.Extends c2) (h2 : c2.Extends c3) : c1.Extends c3 := by
  rcases h1 with ⟨e1, he1⟩
  rcases h2 with ⟨e2, he2⟩
  exact ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩

lemma CB.Extends.size_le {n : ℕ} {c1 c2 : CB n} (h : c1.Extends c2) : c1.size ≤ c2.size := by
  rcases h with ⟨e, he⟩
  dsimp only [CB.size]
  rw [he, List.length_append]
  omega

lemma CB.Extends.eval_eq {n : ℕ} {c1 c2 : CB n} (h : c1.Extends c2)
    {x : List Bool} (hx : x.length = n) {w : ℕ} (hw : w < n + c1.size) :
    c2.eval x w = c1.eval x w := by
  rcases h with ⟨e, he⟩
  dsimp only [CB.eval]
  rw [he, wiresOf_append]
  have hlen : (wiresOf c1.gates x).length = n + c1.size := by
    rw [wiresOf_length, hx]
    rfl
  exact wiresOf_getD_prefix e (wiresOf c1.gates x) (by omega)

def CB.empty (n : ℕ) : CB n :=
  ⟨[], fun _ h => by simp at h, fun _ h => by simp at h⟩

def ValidWires {n : ℕ} (c : CB n) (ws : List ℕ) : Prop :=
  ∀ w ∈ ws, w < n + c.size

lemma ValidWires.mono {n : ℕ} {c1 c2 : CB n} {ws : List ℕ}
    (h : c1.Extends c2) (hv : ValidWires c1 ws) : ValidWires c2 ws :=
  fun w hw => lt_of_lt_of_le (hv w hw) (Nat.add_le_add_left h.size_le n)

lemma ValidWires.map_eval_eq {n : ℕ} {c1 c2 : CB n} {ws : List ℕ}
    (h : c1.Extends c2) (hv : ValidWires c1 ws) {x : List Bool} (hx : x.length = n) :
    ws.map (c2.eval x) = ws.map (c1.eval x) :=
  List.map_congr_left (fun w hw => h.eval_eq hx (hv w hw))

lemma ValidWires.append {n : ℕ} {c : CB n} {ws1 ws2 : List ℕ}
    (h1 : ValidWires c ws1) (h2 : ValidWires c ws2) : ValidWires c (ws1 ++ ws2) := by
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with hw1 | hw2
  · exact h1 w hw1
  · exact h2 w hw2

lemma ValidWires.replicate {n : ℕ} {c : CB n} {k w : ℕ} (hw : w < n + c.size) :
    ValidWires c (List.replicate k w) := by
  intro u hu
  rw [List.mem_replicate] at hu
  rw [hu.2]
  exact hw

lemma ValidWires.take {n : ℕ} {c : CB n} {ws : List ℕ} (h : ValidWires c ws) (k : ℕ) :
    ValidWires c (ws.take k) :=
  fun w hw => h w (List.mem_of_mem_take hw)

lemma ValidWires.reverse {n : ℕ} {c : CB n} {ws : List ℕ} (h : ValidWires c ws) :
    ValidWires c ws.reverse :=
  fun w hw => h w (List.mem_reverse.mp hw)

def CB.pushGate {n : ℕ} (c : CB n) (g : Gate)
    (hin : ∀ i ∈ g.inputs, i < n + c.size) (hf : FanIn2 g) : CB n × ℕ :=
  (⟨c.gates ++ [g], by
    intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < c.gates.length
    · have hgd : (c.gates ++ [g]).getD j ⟨.or, []⟩ = c.gates.getD j ⟨.or, []⟩ := by
        have hlt2 : j < (c.gates ++ [g]).length := by simp; omega
        rw [List.getD_eq_getElem _ _ hlt2, List.getD_eq_getElem _ _ hlt, List.getElem_append_left hlt]
      rw [hgd] at hi
      exact c.hback j hlt i hi
    · have hj_eq : j = c.gates.length := by omega
      subst hj_eq
      have hlt2 : c.gates.length < (c.gates ++ [g]).length := by simp
      have hgd : (c.gates ++ [g]).getD c.gates.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem _ _ hlt2, List.getElem_append_right le_rfl]
        simp
      rw [hgd] at hi
      exact hin i hi,
    by
      intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with h1 | rfl
      · exact c.hfan g' h1
      · exact hf⟩,
   n + c.size)

lemma CB.pushGate_extends {n : ℕ} (c : CB n) (g : Gate)
    (hin : ∀ i ∈ g.inputs, i < n + c.size) (hf : FanIn2 g) :
    c.Extends (c.pushGate g hin hf).1 :=
  ⟨[g], rfl⟩

lemma CB.pushGate_size {n : ℕ} (c : CB n) (g : Gate)
    (hin : ∀ i ∈ g.inputs, i < n + c.size) (hf : FanIn2 g) :
    (c.pushGate g hin hf).1.size = c.size + 1 := by
  simp [CB.pushGate, CB.size]

lemma CB.pushGate_wire {n : ℕ} (c : CB n) (g : Gate)
    (hin : ∀ i ∈ g.inputs, i < n + c.size) (hf : FanIn2 g) :
    (c.pushGate g hin hf).2 = n + c.size := rfl

lemma CB.pushGate_eval {n : ℕ} (c : CB n) (g : Gate)
    (hin : ∀ i ∈ g.inputs, i < n + c.size) (hf : FanIn2 g)
    {x : List Bool} (hx : x.length = n) :
    (c.pushGate g hin hf).1.eval x (c.pushGate g hin hf).2 =
    g.op.eval (g.inputs.map (c.eval x)) := by
  dsimp only [CB.pushGate, CB.eval, CB.size]
  have h := wiresOf_snoc_last c.gates g x
  rw [hx] at h
  exact h

def mkNot {n : ℕ} (c : CB n) (a : ℕ) (ha : a < n + c.size) : CB n × ℕ :=
  c.pushGate ⟨.not, [a]⟩ (by intro i hi; simp at hi; subst hi; exact ha)
    (Or.inr ⟨rfl, rfl⟩)

def mkAnd {n : ℕ} (c : CB n) (a b : ℕ) (ha : a < n + c.size) (hb : b < n + c.size) : CB n × ℕ :=
  c.pushGate ⟨.and, [a, b]⟩ (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
    (Or.inl ⟨Or.inl rfl, rfl⟩)

def mkOr {n : ℕ} (c : CB n) (a b : ℕ) (ha : a < n + c.size) (hb : b < n + c.size) : CB n × ℕ :=
  c.pushGate ⟨.or, [a, b]⟩ (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
    (Or.inl ⟨Or.inr rfl, rfl⟩)

lemma mkNot_spec {n : ℕ} (c : CB n) (a : ℕ) (ha : a < n + c.size) :
    let res := mkNot c a ha
    c.Extends res.1 ∧ res.1.size = c.size + 1 ∧ res.2 < n + res.1.size ∧
    ∀ x, x.length = n → res.1.eval x res.2 = !(c.eval x a) := by
  dsimp only [mkNot]
  refine ⟨CB.pushGate_extends _ _ _ _, CB.pushGate_size _ _ _ _, ?_, ?_⟩
  · rw [CB.pushGate_wire, CB.pushGate_size]; omega
  · intro x hx
    rw [CB.pushGate_eval _ _ _ _ hx]
    rfl

lemma mkAnd_spec {n : ℕ} (c : CB n) (a b : ℕ) (ha : a < n + c.size) (hb : b < n + c.size) :
    let res := mkAnd c a b ha hb
    c.Extends res.1 ∧ res.1.size = c.size + 1 ∧ res.2 < n + res.1.size ∧
    ∀ x, x.length = n → res.1.eval x res.2 = (c.eval x a && c.eval x b) := by
  dsimp only [mkAnd]
  refine ⟨CB.pushGate_extends _ _ _ _, CB.pushGate_size _ _ _ _, ?_, ?_⟩
  · rw [CB.pushGate_wire, CB.pushGate_size]; omega
  · intro x hx
    rw [CB.pushGate_eval _ _ _ _ hx]
    simp [GateOp.eval]

lemma mkOr_spec {n : ℕ} (c : CB n) (a b : ℕ) (ha : a < n + c.size) (hb : b < n + c.size) :
    let res := mkOr c a b ha hb
    c.Extends res.1 ∧ res.1.size = c.size + 1 ∧ res.2 < n + res.1.size ∧
    ∀ x, x.length = n → res.1.eval x res.2 = (c.eval x a || c.eval x b) := by
  dsimp only [mkOr]
  refine ⟨CB.pushGate_extends _ _ _ _, CB.pushGate_size _ _ _ _, ?_, ?_⟩
  · rw [CB.pushGate_wire, CB.pushGate_size]; omega
  · intro x hx
    rw [CB.pushGate_eval _ _ _ _ hx]
    simp [GateOp.eval]

def mkConsts {n : ℕ} (c : CB n) (hn : 0 < n) : CB n × ℕ × ℕ :=
  let r1 := mkNot c 0 (by omega)
  let r2 := mkAnd r1.1 0 r1.2 (by have := (mkNot_spec c 0 (by omega)).2.1; omega)
    (mkNot_spec c 0 (by omega)).2.2.1
  let r3 := mkNot r2.1 r2.2 (mkAnd_spec _ _ _ _ _).2.2.1
  (r3.1, r2.2, r3.2)

lemma mkConsts_spec {n : ℕ} (c : CB n) (hn : 0 < n) :
    let res := mkConsts c hn
    c.Extends res.1 ∧ res.1.size = c.size + 3 ∧
    res.2.1 < n + res.1.size ∧ res.2.2 < n + res.1.size ∧
    ∀ x, x.length = n → res.1.eval x res.2.1 = false ∧ res.1.eval x res.2.2 = true := by
  dsimp only [mkConsts]
  have s1 := mkNot_spec c 0 (by omega)
  set r1 := mkNot c 0 (by omega)
  have s2 := mkAnd_spec r1.1 0 r1.2 (by omega) s1.2.2.1
  set r2 := mkAnd r1.1 0 r1.2 (by omega) s1.2.2.1
  have s3 := mkNot_spec r2.1 r2.2 s2.2.2.1
  set r3 := mkNot r2.1 r2.2 s2.2.2.1
  refine ⟨s1.1.trans (s2.1.trans s3.1), by rw [s3.2.1, s2.2.1, s1.2.1],
    lt_of_lt_of_le s2.2.2.1 (Nat.add_le_add_left s3.1.size_le n), s3.2.2.1, ?_⟩
  intro x hx
  have hf : r2.1.eval x r2.2 = false := by
    rw [s2.2.2.2 x hx, s1.1.eval_eq hx (by omega), s1.2.2.2 x hx]
    cases c.eval x 0 <;> rfl
  refine ⟨by rw [s3.1.eval_eq hx s2.2.2.1, hf], by rw [s3.2.2.2 x hx, hf]; rfl⟩

def mkXor {n : ℕ} (c : CB n) (a b : ℕ) (ha : a < n + c.size) (hb : b < n + c.size) : CB n × ℕ :=
  let r1 := mkOr c a b ha hb
  let r2 := mkAnd r1.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left (mkOr_spec c a b ha hb).1.size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (mkOr_spec c a b ha hb).1.size_le n))
  let r3 := mkNot r2.1 r2.2 (mkAnd_spec _ _ _ _ _).2.2.1
  mkAnd r3.1 r1.2 r3.2
    (lt_of_lt_of_le (mkOr_spec c a b ha hb).2.2.1
      (Nat.add_le_add_left ((mkAnd_spec _ _ _ _ _).1.trans (mkNot_spec _ _ _).1).size_le n))
    (mkNot_spec _ _ _).2.2.1

lemma mkXor_spec {n : ℕ} (c : CB n) (a b : ℕ) (ha : a < n + c.size) (hb : b < n + c.size) :
    let res := mkXor c a b ha hb
    c.Extends res.1 ∧ res.1.size = c.size + 4 ∧ res.2 < n + res.1.size ∧
    ∀ x, x.length = n → res.1.eval x res.2 = xor (c.eval x a) (c.eval x b) := by
  dsimp only [mkXor]
  have s1 := mkOr_spec c a b ha hb
  set r1 := mkOr c a b ha hb
  have s2 := mkAnd_spec r1.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left s1.1.size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left s1.1.size_le n))
  set r2 := mkAnd r1.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left s1.1.size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left s1.1.size_le n))
  have s3 := mkNot_spec r2.1 r2.2 s2.2.2.1
  set r3 := mkNot r2.1 r2.2 s2.2.2.1
  have s4 := mkAnd_spec r3.1 r1.2 r3.2
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left (s2.1.trans s3.1).size_le n)) s3.2.2.1
  refine ⟨s1.1.trans (s2.1.trans (s3.1.trans s4.1)), by rw [s4.2.1, s3.2.1, s2.2.1, s1.2.1], s4.2.2.1, ?_⟩
  intro x hx
  rw [s4.2.2.2 x hx, (s2.1.trans s3.1).eval_eq hx s1.2.2.1, s1.2.2.2 x hx,
    s3.2.2.2 x hx, s2.2.2.2 x hx, s1.1.eval_eq hx ha, s1.1.eval_eq hx hb]
  cases c.eval x a <;> cases c.eval x b <;> rfl

def mkMux {n : ℕ} (c : CB n) (sel a b : ℕ)
    (hs : sel < n + c.size) (ha : a < n + c.size) (hb : b < n + c.size) : CB n × ℕ :=
  let r1 := mkNot c sel hs
  let r2 := mkAnd r1.1 sel a
    (lt_of_lt_of_le hs (Nat.add_le_add_left (mkNot_spec c sel hs).1.size_le n))
    (lt_of_lt_of_le ha (Nat.add_le_add_left (mkNot_spec c sel hs).1.size_le n))
  let r3 := mkAnd r2.1 r1.2 b
    (lt_of_lt_of_le (mkNot_spec c sel hs).2.2.1 (Nat.add_le_add_left (mkAnd_spec _ _ _ _ _).1.size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left ((mkNot_spec c sel hs).1.trans (mkAnd_spec _ _ _ _ _).1).size_le n))
  mkOr r3.1 r2.2 r3.2
    (lt_of_lt_of_le (mkAnd_spec _ _ _ _ _).2.2.1 (Nat.add_le_add_left (mkAnd_spec _ _ _ _ _).1.size_le n))
    (mkAnd_spec _ _ _ _ _).2.2.1

lemma mkMux_spec {n : ℕ} (c : CB n) (sel a b : ℕ)
    (hs : sel < n + c.size) (ha : a < n + c.size) (hb : b < n + c.size) :
    let res := mkMux c sel a b hs ha hb
    c.Extends res.1 ∧ res.1.size = c.size + 4 ∧ res.2 < n + res.1.size ∧
    ∀ x, x.length = n → res.1.eval x res.2 = if c.eval x sel then c.eval x a else c.eval x b := by
  dsimp only [mkMux]
  have s1 := mkNot_spec c sel hs
  set r1 := mkNot c sel hs
  have s2 := mkAnd_spec r1.1 sel a
    (lt_of_lt_of_le hs (Nat.add_le_add_left s1.1.size_le n))
    (lt_of_lt_of_le ha (Nat.add_le_add_left s1.1.size_le n))
  set r2 := mkAnd r1.1 sel a
    (lt_of_lt_of_le hs (Nat.add_le_add_left s1.1.size_le n))
    (lt_of_lt_of_le ha (Nat.add_le_add_left s1.1.size_le n))
  have s3 := mkAnd_spec r2.1 r1.2 b
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
  set r3 := mkAnd r2.1 r1.2 b
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
  have s4 := mkOr_spec r3.1 r2.2 r3.2
    (lt_of_lt_of_le s2.2.2.1 (Nat.add_le_add_left s3.1.size_le n)) s3.2.2.1
  refine ⟨s1.1.trans (s2.1.trans (s3.1.trans s4.1)), by rw [s4.2.1, s3.2.1, s2.2.1, s1.2.1], s4.2.2.1, ?_⟩
  intro x hx
  rw [s4.2.2.2 x hx, s3.1.eval_eq hx s2.2.2.1, s2.2.2.2 x hx, s1.1.eval_eq hx hs,
    s1.1.eval_eq hx ha, s3.2.2.2 x hx, s2.1.eval_eq hx s1.2.2.1, s1.2.2.2 x hx,
    (s1.1.trans s2.1).eval_eq hx hb]
  cases c.eval x sel <;> cases c.eval x a <;> cases c.eval x b <;> rfl

def mkFullAdder {n : ℕ} (c : CB n) (a b cin : ℕ)
    (ha : a < n + c.size) (hb : b < n + c.size) (hc : cin < n + c.size) : CB n × ℕ × ℕ :=
  let r1 := mkXor c a b ha hb
  let s1 := mkXor_spec c a b ha hb
  let r2 := mkXor r1.1 r1.2 cin s1.2.2.1 (lt_of_lt_of_le hc (Nat.add_le_add_left s1.1.size_le n))
  let s2 := mkXor_spec r1.1 r1.2 cin s1.2.2.1 (lt_of_lt_of_le hc (Nat.add_le_add_left s1.1.size_le n))
  let r3 := mkAnd r2.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
  let s3 := mkAnd_spec r2.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
  let r4 := mkAnd r3.1 r1.2 cin
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left (s2.1.trans s3.1).size_le n))
    (lt_of_lt_of_le hc (Nat.add_le_add_left (s1.1.trans (s2.1.trans s3.1)).size_le n))
  let s4 := mkAnd_spec r3.1 r1.2 cin
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left (s2.1.trans s3.1).size_le n))
    (lt_of_lt_of_le hc (Nat.add_le_add_left (s1.1.trans (s2.1.trans s3.1)).size_le n))
  let r5 := mkOr r4.1 r3.2 r4.2
    (lt_of_lt_of_le s3.2.2.1 (Nat.add_le_add_left s4.1.size_le n)) s4.2.2.1
  (r5.1, r2.2, r5.2)

lemma mkFullAdder_spec {n : ℕ} (c : CB n) (a b cin : ℕ)
    (ha : a < n + c.size) (hb : b < n + c.size) (hc : cin < n + c.size) :
    let res := mkFullAdder c a b cin ha hb hc
    c.Extends res.1 ∧ res.1.size = c.size + 11 ∧
    res.2.1 < n + res.1.size ∧ res.2.2 < n + res.1.size ∧
    ∀ x, x.length = n →
      (res.1.eval x res.2.1).toNat + 2 * (res.1.eval x res.2.2).toNat =
      (c.eval x a).toNat + (c.eval x b).toNat + (c.eval x cin).toNat := by
  dsimp only [mkFullAdder]
  have s1 := mkXor_spec c a b ha hb
  set r1 := mkXor c a b ha hb
  have s2 := mkXor_spec r1.1 r1.2 cin s1.2.2.1 (lt_of_lt_of_le hc (Nat.add_le_add_left s1.1.size_le n))
  set r2 := mkXor r1.1 r1.2 cin s1.2.2.1 (lt_of_lt_of_le hc (Nat.add_le_add_left s1.1.size_le n))
  have s3 := mkAnd_spec r2.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
  set r3 := mkAnd r2.1 a b
    (lt_of_lt_of_le ha (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
    (lt_of_lt_of_le hb (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
  have s4 := mkAnd_spec r3.1 r1.2 cin
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left (s2.1.trans s3.1).size_le n))
    (lt_of_lt_of_le hc (Nat.add_le_add_left (s1.1.trans (s2.1.trans s3.1)).size_le n))
  set r4 := mkAnd r3.1 r1.2 cin
    (lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left (s2.1.trans s3.1).size_le n))
    (lt_of_lt_of_le hc (Nat.add_le_add_left (s1.1.trans (s2.1.trans s3.1)).size_le n))
  have s5 := mkOr_spec r4.1 r3.2 r4.2
    (lt_of_lt_of_le s3.2.2.1 (Nat.add_le_add_left s4.1.size_le n)) s4.2.2.1
  set r5 := mkOr r4.1 r3.2 r4.2
    (lt_of_lt_of_le s3.2.2.1 (Nat.add_le_add_left s4.1.size_le n)) s4.2.2.1
  have hext : c.Extends r5.1 := s1.1.trans (s2.1.trans (s3.1.trans (s4.1.trans s5.1)))
  refine ⟨hext, by omega, lt_of_lt_of_le s2.2.2.1 (Nat.add_le_add_left (s3.1.trans (s4.1.trans s5.1)).size_le n),
    s5.2.2.1, ?_⟩
  intro x hx
  have hsum : r5.1.eval x r2.2 = xor (xor (c.eval x a) (c.eval x b)) (c.eval x cin) := by
    rw [(s3.1.trans (s4.1.trans s5.1)).eval_eq hx s2.2.2.1, s2.2.2.2 x hx,
      s1.2.2.2 x hx, s1.1.eval_eq hx hc]
  have hcout : r5.1.eval x r5.2 =
      ((c.eval x a && c.eval x b) || (xor (c.eval x a) (c.eval x b) && c.eval x cin)) := by
    rw [s5.2.2.2 x hx, s4.1.eval_eq hx s3.2.2.1, s3.2.2.2 x hx,
      (s1.1.trans s2.1).eval_eq hx ha, (s1.1.trans s2.1).eval_eq hx hb,
      s4.2.2.2 x hx, (s2.1.trans s3.1).eval_eq hx s1.2.2.1, s1.2.2.2 x hx,
      (s1.1.trans (s2.1.trans s3.1)).eval_eq hx hc]
  rw [hsum, hcout]
  cases c.eval x a <;> cases c.eval x b <;> cases c.eval x cin <;> decide

def mkNotVec {n : ℕ} (c : CB n) : (ws : List ℕ) → ValidWires c ws → CB n × List ℕ
  | [], _ => (c, [])
  | a :: tl, hv =>
    let r1 := mkNot c a (hv a (by simp))
    let s1 := mkNot_spec c a (hv a (by simp))
    let r2 := mkNotVec r1.1 tl (ValidWires.mono s1.1 (fun w hw => hv w (by simp [hw])))
    (r2.1, r1.2 :: r2.2)

lemma mkNotVec_spec {n : ℕ} (ws : List ℕ) :
    ∀ (c : CB n) (hv : ValidWires c ws),
      let res := mkNotVec c ws hv
      c.Extends res.1 ∧ res.1.size = c.size + ws.length ∧
      res.2.length = ws.length ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n → res.2.map (res.1.eval x) = (ws.map (c.eval x)).map (!·) := by
  induction ws with
  | nil =>
    intro c _
    exact ⟨CB.Extends.refl c, by simp [mkNotVec], rfl, fun _ h => by simp [mkNotVec] at h,
      fun _ _ => rfl⟩
  | cons a tl ih =>
    intro c hv
    dsimp only [mkNotVec]
    have s1 := mkNot_spec c a (hv a (by simp))
    set r1 := mkNot c a (hv a (by simp))
    have hvtl : ValidWires r1.1 tl := ValidWires.mono s1.1 (fun w hw => hv w (by simp [hw]))
    have s2 := ih r1.1 hvtl
    set r2 := mkNotVec r1.1 tl hvtl
    refine ⟨s1.1.trans s2.1, by simp; omega, by simp [s2.2.2.1], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | htl
      · exact lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n)
      · exact s2.2.2.2.1 w htl
    · intro x hx
      simp only [List.map_cons]
      rw [s2.1.eval_eq hx s1.2.2.1, s1.2.2.2 x hx, s2.2.2.2.2 x hx,
        ValidWires.map_eval_eq s1.1 (fun w hw => hv w (by simp [hw])) hx]

def mkMuxVec {n : ℕ} (c : CB n) (sel : ℕ) (hs : sel < n + c.size) :
    (as bs : List ℕ) → as.length = bs.length → ValidWires c as → ValidWires c bs → CB n × List ℕ
  | [], [], _, _, _ => (c, [])
  | a :: atl, b :: btl, hlen, hva, hvb =>
    let r1 := mkMux c sel a b hs (hva a (by simp)) (hvb b (by simp))
    let s1 := mkMux_spec c sel a b hs (hva a (by simp)) (hvb b (by simp))
    let r2 := mkMuxVec r1.1 sel (lt_of_lt_of_le hs (Nat.add_le_add_left s1.1.size_le n))
      atl btl (by simp at hlen; exact hlen)
      (ValidWires.mono s1.1 (fun w hw => hva w (by simp [hw])))
      (ValidWires.mono s1.1 (fun w hw => hvb w (by simp [hw])))
    (r2.1, r1.2 :: r2.2)

lemma mkMuxVec_spec {n : ℕ} (as : List ℕ) :
    ∀ (bs : List ℕ) (hlen : as.length = bs.length) (c : CB n) (sel : ℕ)
      (hs : sel < n + c.size) (hva : ValidWires c as) (hvb : ValidWires c bs),
      let res := mkMuxVec c sel hs as bs hlen hva hvb
      c.Extends res.1 ∧ res.1.size = c.size + 4 * as.length ∧
      res.2.length = as.length ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n →
        res.2.map (res.1.eval x) = if c.eval x sel then as.map (c.eval x) else bs.map (c.eval x) := by
  induction as with
  | nil =>
    intro bs hlen c sel hs hva hvb
    cases bs with
    | nil =>
      refine ⟨CB.Extends.refl c, by simp [mkMuxVec], rfl, fun _ h => by simp [mkMuxVec] at h, ?_⟩
      intro x _; simp [mkMuxVec]
    | cons _ _ => simp at hlen
  | cons a atl ih =>
    intro bs hlen c sel hs hva hvb
    cases bs with
    | nil => simp at hlen
    | cons b btl =>
      dsimp only [mkMuxVec]
      have s1 := mkMux_spec c sel a b hs (hva a (by simp)) (hvb b (by simp))
      set r1 := mkMux c sel a b hs (hva a (by simp)) (hvb b (by simp))
      have hs1 : sel < n + r1.1.size := lt_of_lt_of_le hs (Nat.add_le_add_left s1.1.size_le n)
      have hva1 : ValidWires r1.1 atl := ValidWires.mono s1.1 (fun w hw => hva w (by simp [hw]))
      have hvb1 : ValidWires r1.1 btl := ValidWires.mono s1.1 (fun w hw => hvb w (by simp [hw]))
      have hlen' : atl.length = btl.length := by simp at hlen; exact hlen
      have s2 := ih btl hlen' r1.1 sel hs1 hva1 hvb1
      set r2 := mkMuxVec r1.1 sel hs1 atl btl hlen' hva1 hvb1
      refine ⟨s1.1.trans s2.1, by simp; omega, by simp [s2.2.2.1], ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | htl
        · exact lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n)
        · exact s2.2.2.2.1 w htl
      · intro x hx
        simp only [List.map_cons]
        rw [s2.1.eval_eq hx s1.2.2.1, s1.2.2.2 x hx, s2.2.2.2.2 x hx,
          s1.1.eval_eq hx hs,
          ValidWires.map_eval_eq s1.1 (fun w hw => hva w (by simp [hw])) hx,
          ValidWires.map_eval_eq s1.1 (fun w hw => hvb w (by simp [hw])) hx]
        cases c.eval x sel <;> rfl

def mkAddWithCin {n : ℕ} (c : CB n) (cin : ℕ) (hc : cin < n + c.size) :
    (as bs : List ℕ) → as.length = bs.length → ValidWires c as → ValidWires c bs → CB n × List ℕ × ℕ
  | [], [], _, _, _ => (c, [], cin)
  | a :: atl, b :: btl, hlen, hva, hvb =>
    let r1 := mkFullAdder c a b cin (hva a (by simp)) (hvb b (by simp)) hc
    let s1 := mkFullAdder_spec c a b cin (hva a (by simp)) (hvb b (by simp)) hc
    let r2 := mkAddWithCin r1.1 r1.2.2 s1.2.2.2.1
      atl btl (by simp at hlen; exact hlen)
      (ValidWires.mono s1.1 (fun w hw => hva w (by simp [hw])))
      (ValidWires.mono s1.1 (fun w hw => hvb w (by simp [hw])))
    (r2.1, r1.2.1 :: r2.2.1, r2.2.2)

lemma mkAddWithCin_spec {n : ℕ} (as : List ℕ) :
    ∀ (bs : List ℕ) (hlen : as.length = bs.length) (c : CB n) (cin : ℕ)
      (hc : cin < n + c.size) (hva : ValidWires c as) (hvb : ValidWires c bs),
      let res := mkAddWithCin c cin hc as bs hlen hva hvb
      c.Extends res.1 ∧ res.1.size = c.size + 11 * as.length ∧
      res.2.1.length = as.length ∧ ValidWires res.1 res.2.1 ∧ res.2.2 < n + res.1.size ∧
      ∀ x, x.length = n →
        bitsVal (res.2.1.map (res.1.eval x)) + 2 ^ as.length * (res.1.eval x res.2.2).toNat =
        bitsVal (as.map (c.eval x)) + bitsVal (bs.map (c.eval x)) + (c.eval x cin).toNat := by
  induction as with
  | nil =>
    intro bs hlen c cin hc hva hvb
    cases bs with
    | nil =>
      refine ⟨CB.Extends.refl c, by simp [mkAddWithCin], rfl,
        fun _ h => by simp [mkAddWithCin] at h, hc, ?_⟩
      intro x _; simp [mkAddWithCin, bitsVal]
    | cons _ _ => simp at hlen
  | cons a atl ih =>
    intro bs hlen c cin hc hva hvb
    cases bs with
    | nil => simp at hlen
    | cons b btl =>
      dsimp only [mkAddWithCin]
      have s1 := mkFullAdder_spec c a b cin (hva a (by simp)) (hvb b (by simp)) hc
      set r1 := mkFullAdder c a b cin (hva a (by simp)) (hvb b (by simp)) hc
      have hva1 : ValidWires r1.1 atl := ValidWires.mono s1.1 (fun w hw => hva w (by simp [hw]))
      have hvb1 : ValidWires r1.1 btl := ValidWires.mono s1.1 (fun w hw => hvb w (by simp [hw]))
      have hlen' : atl.length = btl.length := by simp at hlen; exact hlen
      have s2 := ih btl hlen' r1.1 r1.2.2 s1.2.2.2.1 hva1 hvb1
      set r2 := mkAddWithCin r1.1 r1.2.2 s1.2.2.2.1 atl btl hlen' hva1 hvb1
      refine ⟨s1.1.trans s2.1, by simp; omega, by simp [s2.2.2.1], ?_, s2.2.2.2.2.1, ?_⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | htl
        · exact lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n)
        · exact s2.2.2.2.1 w htl
      · intro x hx
        simp only [List.map_cons, bitsVal, List.length_cons, pow_succ]
        have hfa := s1.2.2.2.2 x hx
        have hrec := s2.2.2.2.2.2 x hx
        rw [ValidWires.map_eval_eq s1.1 (fun w hw => hva w (by simp [hw])) hx,
            ValidWires.map_eval_eq s1.1 (fun w hw => hvb w (by simp [hw])) hx] at hrec
        rw [s2.1.eval_eq hx s1.2.2.1]
        linarith

def mkSubGe {n : ℕ} (c : CB n) (wTrue : ℕ) (ht : wTrue < n + c.size)
    (as bs : List ℕ) (hlen : as.length = bs.length)
    (hva : ValidWires c as) (hvb : ValidWires c bs) : CB n × List ℕ × ℕ :=
  let r1 := mkNotVec c bs hvb
  let s1 := mkNotVec_spec bs c hvb
  mkAddWithCin r1.1 wTrue (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n))
    as r1.2 (by rw [hlen, s1.2.2.1]) (ValidWires.mono s1.1 hva) s1.2.2.2.1

lemma mkSubGe_spec {n : ℕ} (c : CB n) (wTrue : ℕ) (ht : wTrue < n + c.size)
    (as bs : List ℕ) (hlen : as.length = bs.length)
    (hva : ValidWires c as) (hvb : ValidWires c bs) :
    let res := mkSubGe c wTrue ht as bs hlen hva hvb
    c.Extends res.1 ∧ res.1.size = c.size + 12 * as.length ∧
    res.2.1.length = as.length ∧ ValidWires res.1 res.2.1 ∧ res.2.2 < n + res.1.size ∧
    ∀ x, x.length = n → c.eval x wTrue = true →
      (res.1.eval x res.2.2 = decide (bitsVal (bs.map (c.eval x)) ≤ bitsVal (as.map (c.eval x)))) ∧
      (bitsVal (bs.map (c.eval x)) ≤ bitsVal (as.map (c.eval x)) →
        bitsVal (res.2.1.map (res.1.eval x)) = bitsVal (as.map (c.eval x)) - bitsVal (bs.map (c.eval x))) := by
  dsimp only [mkSubGe]
  have s1 := mkNotVec_spec bs c hvb
  set r1 := mkNotVec c bs hvb
  have s2 := mkAddWithCin_spec as r1.2 (by rw [hlen, s1.2.2.1]) r1.1 wTrue
    (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n)) (ValidWires.mono s1.1 hva) s1.2.2.2.1
  set r2 := mkAddWithCin r1.1 wTrue (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n))
    as r1.2 (by rw [hlen, s1.2.2.1]) (ValidWires.mono s1.1 hva) s1.2.2.2.1
  refine ⟨s1.1.trans s2.1, by omega, s2.2.2.1, s2.2.2.2.1, s2.2.2.2.2.1, ?_⟩
  intro x hx hwt
  have hadd := s2.2.2.2.2.2 x hx
  rw [ValidWires.map_eval_eq s1.1 hva hx, s1.2.2.2.2 x hx, s1.1.eval_eq hx ht, hwt] at hadd
  have hnot := bitsVal_map_not (bs.map (c.eval x))
  have hlen_b : (bs.map (c.eval x)).length = as.length := by simp [hlen]
  rw [hlen_b] at hnot
  have hlt_a : bitsVal (as.map (c.eval x)) < 2 ^ as.length := by
    have := bitsVal_lt (as.map (c.eval x))
    simpa using this
  have hlt_b : bitsVal (bs.map (c.eval x)) < 2 ^ as.length := by
    have := bitsVal_lt (bs.map (c.eval x))
    simpa [hlen] using this
  have hlt_r : bitsVal (r2.2.1.map (r2.1.eval x)) < 2 ^ as.length := by
    have := bitsVal_lt (r2.2.1.map (r2.1.eval x))
    simpa [s2.2.2.1] using this
  have hkey : bitsVal (r2.2.1.map (r2.1.eval x)) + 2 ^ as.length * (r2.1.eval x r2.2.2).toNat +
      bitsVal (bs.map (c.eval x)) = bitsVal (as.map (c.eval x)) + 2 ^ as.length := by
    have ht1 : true.toNat = 1 := rfl
    rw [ht1] at hadd
    omega
  constructor
  · cases hge : r2.1.eval x r2.2.2
    · simp only [hge, Bool.toNat_false, mul_zero, add_zero] at hkey
      exact (decide_eq_false (by omega)).symm
    · simp only [hge, Bool.toNat_true, mul_one] at hkey
      exact (decide_eq_true (by omega)).symm
  · intro hle
    have hge : r2.1.eval x r2.2.2 = true := by
      cases h : r2.1.eval x r2.2.2
      · simp only [h, Bool.toNat_false, mul_zero, add_zero] at hkey; omega
      · rfl
    simp only [hge, Bool.toNat_true, mul_one] at hkey
    omega

def mkDist {n : ℕ} (c : CB n) (wTrue : ℕ) (ht : wTrue < n + c.size)
    (as bs : List ℕ) (hlen : as.length = bs.length)
    (hva : ValidWires c as) (hvb : ValidWires c bs) : CB n × List ℕ :=
  let r1 := mkSubGe c wTrue ht as bs hlen hva hvb
  let s1 := mkSubGe_spec c wTrue ht as bs hlen hva hvb
  let r2 := mkSubGe r1.1 wTrue (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n))
    bs as hlen.symm (ValidWires.mono s1.1 hvb) (ValidWires.mono s1.1 hva)
  let s2 := mkSubGe_spec r1.1 wTrue (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n))
    bs as hlen.symm (ValidWires.mono s1.1 hvb) (ValidWires.mono s1.1 hva)
  mkMuxVec r2.1 r1.2.2 (lt_of_lt_of_le s1.2.2.2.2.1 (Nat.add_le_add_left s2.1.size_le n))
    r1.2.1 r2.2.1 (by rw [s1.2.2.1, s2.2.2.1, hlen])
    (ValidWires.mono s2.1 s1.2.2.2.1) s2.2.2.2.1

lemma mkDist_spec {n : ℕ} (c : CB n) (wTrue : ℕ) (ht : wTrue < n + c.size)
    (as bs : List ℕ) (hlen : as.length = bs.length)
    (hva : ValidWires c as) (hvb : ValidWires c bs) :
    let res := mkDist c wTrue ht as bs hlen hva hvb
    c.Extends res.1 ∧ res.1.size = c.size + 28 * as.length ∧
    res.2.length = as.length ∧ ValidWires res.1 res.2 ∧
    ∀ x, x.length = n → c.eval x wTrue = true →
      bitsVal (res.2.map (res.1.eval x)) =
      Nat.dist (bitsVal (as.map (c.eval x))) (bitsVal (bs.map (c.eval x))) := by
  dsimp only [mkDist]
  have s1 := mkSubGe_spec c wTrue ht as bs hlen hva hvb
  set r1 := mkSubGe c wTrue ht as bs hlen hva hvb
  have s2 := mkSubGe_spec r1.1 wTrue (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n))
    bs as hlen.symm (ValidWires.mono s1.1 hvb) (ValidWires.mono s1.1 hva)
  set r2 := mkSubGe r1.1 wTrue (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n))
    bs as hlen.symm (ValidWires.mono s1.1 hvb) (ValidWires.mono s1.1 hva)
  have s3 := mkMuxVec_spec r1.2.1 r2.2.1 (by rw [s1.2.2.1, s2.2.2.1, hlen]) r2.1 r1.2.2
    (lt_of_lt_of_le s1.2.2.2.2.1 (Nat.add_le_add_left s2.1.size_le n))
    (ValidWires.mono s2.1 s1.2.2.2.1) s2.2.2.2.1
  set r3 := mkMuxVec r2.1 r1.2.2 (lt_of_lt_of_le s1.2.2.2.2.1 (Nat.add_le_add_left s2.1.size_le n))
    r1.2.1 r2.2.1 (by rw [s1.2.2.1, s2.2.2.1, hlen])
    (ValidWires.mono s2.1 s1.2.2.2.1) s2.2.2.2.1
  refine ⟨s1.1.trans (s2.1.trans s3.1), by omega, by rw [s3.2.2.1, s1.2.2.1], s3.2.2.2.1, ?_⟩
  intro x hx hwt
  rw [s3.2.2.2.2 x hx, s2.1.eval_eq hx s1.2.2.2.2.1, (s1.2.2.2.2.2 x hx hwt).1,
    ValidWires.map_eval_eq s2.1 s1.2.2.2.1 hx]
  have hwt1 : r1.1.eval x wTrue = true := by rw [s1.1.eval_eq hx ht, hwt]
  have h2 := s2.2.2.2.2.2 x hx hwt1
  rw [ValidWires.map_eval_eq s1.1 hva hx, ValidWires.map_eval_eq s1.1 hvb hx] at h2
  by_cases hle : bitsVal (bs.map (c.eval x)) ≤ bitsVal (as.map (c.eval x))
  · simp only [decide_eq_true hle, ↓reduceIte, (s1.2.2.2.2.2 x hx hwt).2 hle, Nat.dist]
    have h0 : bitsVal (bs.map (c.eval x)) - bitsVal (as.map (c.eval x)) = 0 := by omega
    omega
  · simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte, h2.2 (by omega), Nat.dist]
    have h0 : bitsVal (as.map (c.eval x)) - bitsVal (bs.map (c.eval x)) = 0 := by omega
    omega

def mkAndConstVec {n : ℕ} (c : CB n) (sel : ℕ) (hs : sel < n + c.size) :
    (as : List ℕ) → ValidWires c as → CB n × List ℕ
  | [], _ => (c, [])
  | a :: atl, hv =>
    let r1 := mkAnd c sel a hs (hv a (by simp))
    let s1 := mkAnd_spec c sel a hs (hv a (by simp))
    let r2 := mkAndConstVec r1.1 sel (lt_of_lt_of_le hs (Nat.add_le_add_left s1.1.size_le n))
      atl (ValidWires.mono s1.1 (fun w hw => hv w (by simp [hw])))
    (r2.1, r1.2 :: r2.2)

lemma mkAndConstVec_spec {n : ℕ} (as : List ℕ) :
    ∀ (c : CB n) (sel : ℕ) (hs : sel < n + c.size) (hv : ValidWires c as),
      let res := mkAndConstVec c sel hs as hv
      c.Extends res.1 ∧ res.1.size = c.size + as.length ∧
      res.2.length = as.length ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n →
        bitsVal (res.2.map (res.1.eval x)) =
        if c.eval x sel then bitsVal (as.map (c.eval x)) else 0 := by
  induction as with
  | nil =>
    intro c sel _ _
    exact ⟨CB.Extends.refl c, by simp [mkAndConstVec], rfl,
      fun _ h => by simp [mkAndConstVec] at h, fun _ _ => by simp [mkAndConstVec, bitsVal]⟩
  | cons a atl ih =>
    intro c sel hs hv
    dsimp only [mkAndConstVec]
    have s1 := mkAnd_spec c sel a hs (hv a (by simp))
    set r1 := mkAnd c sel a hs (hv a (by simp))
    have hs1 : sel < n + r1.1.size := lt_of_lt_of_le hs (Nat.add_le_add_left s1.1.size_le n)
    have hv1 : ValidWires r1.1 atl := ValidWires.mono s1.1 (fun w hw => hv w (by simp [hw]))
    have s2 := ih r1.1 sel hs1 hv1
    set r2 := mkAndConstVec r1.1 sel hs1 atl hv1
    refine ⟨s1.1.trans s2.1, by simp; omega, by simp [s2.2.2.1], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | htl
      · exact lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n)
      · exact s2.2.2.2.1 w htl
    · intro x hx
      simp only [List.map_cons, bitsVal]
      rw [s2.1.eval_eq hx s1.2.2.1, s1.2.2.2 x hx, s2.2.2.2.2 x hx, s1.1.eval_eq hx hs,
        ValidWires.map_eval_eq s1.1 (fun w hw => hv w (by simp [hw])) hx]
      cases c.eval x sel <;> simp

def mkMulAcc {n : ℕ} (W : ℕ) (c : CB n) (wFalse : ℕ) (hf : wFalse < n + c.size)
    (as : List ℕ) (hva : ValidWires c as) :
    (bs : List ℕ) → (shift : ℕ) → (hfit : shift + as.length + bs.length ≤ W) →
    (acc : List ℕ) → acc.length = W → ValidWires c acc → ValidWires c bs → CB n × List ℕ
  | [], _, _, acc, _, _, _ => (c, acc)
  | b :: btl, shift, hfit, acc, hacc_len, hvacc, hvb =>
    let padded : List ℕ :=
      List.replicate shift wFalse ++ as ++ List.replicate (W - shift - as.length) wFalse
    have hp_len : padded.length = W := by
      simp [padded]; omega
    have hp_val : ValidWires c padded :=
      ValidWires.append (ValidWires.append (ValidWires.replicate hf) hva) (ValidWires.replicate hf)
    let r1 := mkAndConstVec c b (hvb b (by simp)) padded hp_val
    let s1 := mkAndConstVec_spec padded c b (hvb b (by simp)) hp_val
    let r2 := mkAddWithCin r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      acc r1.2 (by rw [hacc_len, s1.2.2.1, hp_len])
      (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    let s2 := mkAddWithCin_spec acc r1.2 (by rw [hacc_len, s1.2.2.1, hp_len])
      r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    mkMulAcc W r2.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      as (ValidWires.mono (s1.1.trans s2.1) hva) btl (shift + 1) (by simp at hfit; omega)
      r2.2.1 (by rw [s2.2.2.1, hacc_len]) s2.2.2.2.1
      (ValidWires.mono (s1.1.trans s2.1) (fun w hw => hvb w (by simp [hw])))

lemma mkMulAcc_spec {n : ℕ} (W : ℕ) (bs : List ℕ) :
    ∀ (c : CB n) (wFalse : ℕ) (hf : wFalse < n + c.size) (as : List ℕ) (hva : ValidWires c as)
      (shift : ℕ) (hfit : shift + as.length + bs.length ≤ W)
      (acc : List ℕ) (hacc_len : acc.length = W) (hvacc : ValidWires c acc) (hvb : ValidWires c bs),
      let res := mkMulAcc W c wFalse hf as hva bs shift hfit acc hacc_len hvacc hvb
      c.Extends res.1 ∧ res.1.size = c.size + 12 * W * bs.length ∧
      res.2.length = W ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n → c.eval x wFalse = false →
        bitsVal (acc.map (c.eval x)) + 2 ^ shift * bitsVal (as.map (c.eval x)) * bitsVal (bs.map (c.eval x)) < 2 ^ W →
        bitsVal (res.2.map (res.1.eval x)) =
        bitsVal (acc.map (c.eval x)) + 2 ^ shift * bitsVal (as.map (c.eval x)) * bitsVal (bs.map (c.eval x)) := by
  induction bs with
  | nil =>
    intro c wFalse hf as hva shift hfit acc hacc_len hvacc hvb
    refine ⟨CB.Extends.refl c, by simp [mkMulAcc], hacc_len, hvacc, ?_⟩
    intro x _ _ _
    simp [mkMulAcc, bitsVal]
  | cons b btl ih =>
    intro c wFalse hf as hva shift hfit acc hacc_len hvacc hvb
    dsimp only [mkMulAcc]
    let padded : List ℕ :=
      List.replicate shift wFalse ++ as ++ List.replicate (W - shift - as.length) wFalse
    have hp_len : padded.length = W := by simp [padded]; omega
    have hp_val : ValidWires c padded :=
      ValidWires.append (ValidWires.append (ValidWires.replicate hf) hva) (ValidWires.replicate hf)
    have s1 := mkAndConstVec_spec padded c b (hvb b (by simp)) hp_val
    set r1 := mkAndConstVec c b (hvb b (by simp)) padded hp_val
    have s2 := mkAddWithCin_spec acc r1.2 (by rw [hacc_len, s1.2.2.1, hp_len])
      r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    set r2 := mkAddWithCin r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      acc r1.2 (by rw [hacc_len, s1.2.2.1, hp_len])
      (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    have s3 := ih r2.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      as (ValidWires.mono (s1.1.trans s2.1) hva) (shift + 1) (by simp at hfit; omega)
      r2.2.1 (by rw [s2.2.2.1, hacc_len]) s2.2.2.2.1
      (ValidWires.mono (s1.1.trans s2.1) (fun w hw => hvb w (by simp [hw])))
    refine ⟨s1.1.trans (s2.1.trans s3.1), ?_, s3.2.2.1, s3.2.2.2.1, ?_⟩
    · have h1 : r1.1.size = c.size + W := by rw [s1.2.1, hp_len]
      have h2 : r2.1.size = r1.1.size + 11 * W := by rw [s2.2.1, hacc_len]
      have h3 : (mkMulAcc W r2.1 _ _ _ _ _ _ _ _ _ _ _).1.size = r2.1.size + 12 * W * btl.length := s3.2.1
      simp only [List.length_cons]
      linarith
    · intro x hx hwf hbound
      have hpad_val : bitsVal (padded.map (c.eval x)) = 2 ^ shift * bitsVal (as.map (c.eval x)) := by
        dsimp only [padded]
        simp only [List.map_append, List.map_replicate, hwf, bitsVal_append, bitsVal_replicate_false,
          List.length_replicate, zero_add, mul_zero, add_zero]
      have hr1_val : bitsVal (r1.2.map (r1.1.eval x)) =
          (c.eval x b).toNat * (2 ^ shift * bitsVal (as.map (c.eval x))) := by
        rw [s1.2.2.2.2 x hx, hpad_val]
        cases c.eval x b <;> simp
      have hr2_add := s2.2.2.2.2.2 x hx
      rw [ValidWires.map_eval_eq s1.1 hvacc hx, hr1_val, s1.1.eval_eq hx hf, hwf, hacc_len] at hr2_add
      have hsum_eq : bitsVal (acc.map (c.eval x)) +
          2 ^ shift * bitsVal (as.map (c.eval x)) * bitsVal ((b :: btl).map (c.eval x)) =
          (bitsVal (acc.map (c.eval x)) + (c.eval x b).toNat * (2 ^ shift * bitsVal (as.map (c.eval x)))) +
          2 ^ (shift + 1) * bitsVal (as.map (c.eval x)) * bitsVal (btl.map (c.eval x)) := by
        simp only [List.map_cons, bitsVal, pow_succ]
        ring
      have hlt_cur : bitsVal (acc.map (c.eval x)) +
          (c.eval x b).toNat * (2 ^ shift * bitsVal (as.map (c.eval x))) < 2 ^ W := by
        omega
      have hcout0 : (r2.1.eval x r2.2.2).toNat = 0 := by
        have hfalse : false.toNat = 0 := rfl
        rw [hfalse, add_zero] at hr2_add
        by_contra hne
        have h1 : 1 ≤ (r2.1.eval x r2.2.2).toNat := by omega
        have hmul : 2 ^ W ≤ 2 ^ W * (r2.1.eval x r2.2.2).toNat := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have hr2_val : bitsVal (r2.2.1.map (r2.1.eval x)) =
          bitsVal (acc.map (c.eval x)) + (c.eval x b).toNat * (2 ^ shift * bitsVal (as.map (c.eval x))) := by
        rw [hcout0, mul_zero, add_zero] at hr2_add
        have hfalse : false.toNat = 0 := rfl
        rw [hfalse, add_zero] at hr2_add
        exact hr2_add
      have hwf2 : r2.1.eval x wFalse = false := by
        rw [(s1.1.trans s2.1).eval_eq hx hf, hwf]
      have hrec := s3.2.2.2.2 x hx hwf2
      rw [ValidWires.map_eval_eq (ws := as) (s1.1.trans s2.1) hva hx,
          ValidWires.map_eval_eq (ws := btl) (s1.1.trans s2.1) (fun w hw => hvb w (by simp [hw])) hx,
          hr2_val] at hrec
      rw [hsum_eq] at hbound ⊢
      exact hrec hbound

def constBits (W val wFalse wTrue : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin W => if val.testBit i.val then wTrue else wFalse)

lemma constBits_length (W val wFalse wTrue : ℕ) :
    (constBits W val wFalse wTrue).length = W := by
  simp [constBits]

lemma constBits_valid {n : ℕ} {c : CB n} (W val wFalse wTrue : ℕ)
    (hf : wFalse < n + c.size) (ht : wTrue < n + c.size) :
    ValidWires c (constBits W val wFalse wTrue) := by
  intro w hw
  simp only [constBits, List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩
  split_ifs <;> assumption

lemma constBits_val {n : ℕ} {c : CB n} {x : List Bool} (W val wFalse wTrue : ℕ)
    (hval : val < 2 ^ W) (hf : c.eval x wFalse = false) (ht : c.eval x wTrue = true) :
    bitsVal ((constBits W val wFalse wTrue).map (c.eval x)) = val := by
  have hmap : (constBits W val wFalse wTrue).map (c.eval x) =
      List.ofFn (fun i : Fin W => val.testBit i.val) := by
    dsimp only [constBits]
    rw [List.map_ofFn]
    congr 1
    ext i
    cases h : val.testBit i.val <;> simp [h, hf, ht]
  rw [hmap]
  exact bitsVal_ofFn_testBit W val hval

def mkDivLoop {n : ℕ} (W width : ℕ) (c : CB n) (wFalse wTrue : ℕ)
    (hf : wFalse < n + c.size) (ht : wTrue < n + c.size) :
    (msb : List ℕ) → (rem : List ℕ) → rem.length = W →
    ValidWires c msb → ValidWires c rem → CB n × List ℕ × List ℕ
  | [], rem, _, _, _ => (c, [], rem)
  | d :: tl, rem, hrem_len, hvmsb, hvrem =>
    let cur : List ℕ := d :: rem
    let wBits : List ℕ := constBits (W + 1) width wFalse wTrue
    have hcur_len : cur.length = wBits.length := by simp [cur, wBits, hrem_len, constBits_length]
    have hcur_val : ValidWires c cur := by
      intro w hw
      simp only [cur, List.mem_cons] at hw
      rcases hw with rfl | hr
      · exact hvmsb w (by simp)
      · exact hvrem w hr
    have hw_val : ValidWires c wBits := constBits_valid (W + 1) width wFalse wTrue hf ht
    let r1 := mkSubGe c wTrue ht cur wBits hcur_len hcur_val hw_val
    let s1 := mkSubGe_spec c wTrue ht cur wBits hcur_len hcur_val hw_val
    let r2 := mkMuxVec r1.1 r1.2.2 s1.2.2.2.2.1 r1.2.1 cur (by rw [s1.2.2.1])
      s1.2.2.2.1 (ValidWires.mono s1.1 hcur_val)
    let s2 := mkMuxVec_spec r1.2.1 cur (by rw [s1.2.2.1]) r1.1 r1.2.2 s1.2.2.2.2.1
      s1.2.2.2.1 (ValidWires.mono s1.1 hcur_val)
    let rem' : List ℕ := r2.2.take W
    have hrem'_len : rem'.length = W := by
      dsimp only [rem']
      rw [List.length_take, s2.2.2.1, s1.2.2.1]
      simp [cur, hrem_len]
    let r3 := mkDivLoop W width r2.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      tl rem' hrem'_len
      (ValidWires.mono (s1.1.trans s2.1) (fun w hw => hvmsb w (by simp [hw])))
      (ValidWires.take s2.2.2.2.1 W)
    (r3.1, r3.2.1 ++ [r1.2.2], r3.2.2)

lemma mkDivLoop_spec {n : ℕ} (W width : ℕ) (hwp : 0 < width) (hwlt : width < 2 ^ W) (msb : List ℕ) :
    ∀ (c : CB n) (wFalse wTrue : ℕ) (hf : wFalse < n + c.size) (ht : wTrue < n + c.size)
      (rem : List ℕ) (hrem_len : rem.length = W) (hvmsb : ValidWires c msb) (hvrem : ValidWires c rem),
      let res := mkDivLoop W width c wFalse wTrue hf ht msb rem hrem_len hvmsb hvrem
      c.Extends res.1 ∧ res.1.size = c.size + 16 * (W + 1) * msb.length ∧
      res.2.1.length = msb.length ∧ res.2.2.length = W ∧
      ValidWires res.1 res.2.1 ∧ ValidWires res.1 res.2.2 ∧
      ∀ x, x.length = n → c.eval x wFalse = false → c.eval x wTrue = true →
        bitsVal (rem.map (c.eval x)) < width →
        bitsVal (rem.map (c.eval x)) * 2 ^ msb.length + msbVal (msb.map (c.eval x)) =
          bitsVal (res.2.1.map (res.1.eval x)) * width + bitsVal (res.2.2.map (res.1.eval x)) ∧
        bitsVal (res.2.2.map (res.1.eval x)) < width := by
  induction msb with
  | nil =>
    intro c wFalse wTrue hf ht rem hrem_len hvmsb hvrem
    refine ⟨CB.Extends.refl c, by simp [mkDivLoop], rfl, hrem_len,
      fun _ h => by simp [mkDivLoop] at h, hvrem, ?_⟩
    intro x _ _ _ hlt
    simp [mkDivLoop, msbVal, bitsVal, hlt]
  | cons d tl ih =>
    intro c wFalse wTrue hf ht rem hrem_len hvmsb hvrem
    dsimp only [mkDivLoop]
    let cur : List ℕ := d :: rem
    let wBits : List ℕ := constBits (W + 1) width wFalse wTrue
    have hcur_len : cur.length = wBits.length := by simp [cur, wBits, hrem_len, constBits_length]
    have hcur_val : ValidWires c cur := by
      intro w hw
      simp only [cur, List.mem_cons] at hw
      rcases hw with rfl | hr
      · exact hvmsb w (by simp)
      · exact hvrem w hr
    have hw_val : ValidWires c wBits := constBits_valid (W + 1) width wFalse wTrue hf ht
    have s1 := mkSubGe_spec c wTrue ht cur wBits hcur_len hcur_val hw_val
    set r1 := mkSubGe c wTrue ht cur wBits hcur_len hcur_val hw_val
    have s2 := mkMuxVec_spec r1.2.1 cur (by rw [s1.2.2.1]) r1.1 r1.2.2 s1.2.2.2.2.1
      s1.2.2.2.1 (ValidWires.mono s1.1 hcur_val)
    set r2 := mkMuxVec r1.1 r1.2.2 s1.2.2.2.2.1 r1.2.1 cur (by rw [s1.2.2.1])
      s1.2.2.2.1 (ValidWires.mono s1.1 hcur_val)
    let rem' : List ℕ := r2.2.take W
    have hrem'_len : rem'.length = W := by
      dsimp only [rem']
      rw [List.length_take, s2.2.2.1, s1.2.2.1]
      simp [cur, hrem_len]
    have s3 := ih r2.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      rem' hrem'_len
      (ValidWires.mono (s1.1.trans s2.1) (fun w hw => hvmsb w (by simp [hw])))
      (ValidWires.take s2.2.2.2.1 W)
    set r3 := mkDivLoop W width r2.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      tl rem' hrem'_len
      (ValidWires.mono (s1.1.trans s2.1) (fun w hw => hvmsb w (by simp [hw])))
      (ValidWires.take s2.2.2.2.1 W)
    have hcur_l : cur.length = W + 1 := by simp [cur, hrem_len]
    refine ⟨s1.1.trans (s2.1.trans s3.1), ?_, ?_, s3.2.2.2.1, ?_, s3.2.2.2.2.2.1, ?_⟩
    · have h1 : r1.1.size = c.size + 12 * (W + 1) := by rw [s1.2.1, hcur_l]
      have h2 : r2.1.size = r1.1.size + 4 * (W + 1) := by rw [s2.2.1, s1.2.2.1, hcur_l]
      have h3 : r3.1.size = r2.1.size + 16 * (W + 1) * tl.length := s3.2.1
      simp only [List.length_cons]
      linarith
    · simp [s3.2.2.1]
    · apply ValidWires.append s3.2.2.2.2.1
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact lt_of_lt_of_le s1.2.2.2.2.1 (Nat.add_le_add_left (s2.1.trans s3.1).size_le n)
    · intro x hx hwf hwt hrem_lt
      have hw_lt2 : width < 2 ^ (W + 1) := by rw [pow_succ]; omega
      have hw_eval : bitsVal (wBits.map (c.eval x)) = width :=
        constBits_val (W + 1) width wFalse wTrue hw_lt2 hwf hwt
      have hcur_eval : bitsVal (cur.map (c.eval x)) =
          (c.eval x d).toNat + 2 * bitsVal (rem.map (c.eval x)) := rfl
      have hsub := s1.2.2.2.2.2 x hx hwt
      rw [hw_eval] at hsub
      have hmux := s2.2.2.2.2 x hx
      rw [ValidWires.map_eval_eq s1.1 hcur_val hx] at hmux
      have hrem'_eval : bitsVal (rem'.map (r2.1.eval x)) =
          if width ≤ bitsVal (cur.map (c.eval x)) then
            bitsVal (cur.map (c.eval x)) - width
          else bitsVal (cur.map (c.eval x)) := by
        have hmap_take : rem'.map (r2.1.eval x) = (r2.2.map (r2.1.eval x)).take W := by
          dsimp only [rem']
          rw [List.map_take]
        have hlt_mux : bitsVal (r2.2.map (r2.1.eval x)) < width := by
          rw [hmux, hsub.1]
          have hd_le : (c.eval x d).toNat ≤ 1 := by cases c.eval x d <;> decide
          by_cases hle : width ≤ bitsVal (cur.map (c.eval x))
          · simp only [decide_eq_true hle, ↓reduceIte, hsub.2 hle]
            omega
          · simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte]
            omega
        rw [hmap_take, bitsVal_take_of_lt _ W (lt_trans hlt_mux hwlt), hmux, hsub.1]
        by_cases hle : width ≤ bitsVal (cur.map (c.eval x))
        · simp [hle, hsub.2 hle]
        · simp [hle]
      have hrem'_lt : bitsVal (rem'.map (r2.1.eval x)) < width := by
        rw [hrem'_eval]
        have hd_le : (c.eval x d).toNat ≤ 1 := by cases c.eval x d <;> decide
        split_ifs <;> omega
      have hwf2 : r2.1.eval x wFalse = false := by rw [(s1.1.trans s2.1).eval_eq hx hf, hwf]
      have hwt2 : r2.1.eval x wTrue = true := by rw [(s1.1.trans s2.1).eval_eq hx ht, hwt]
      have hrec := s3.2.2.2.2.2.2 x hx hwf2 hwt2 hrem'_lt
      rw [ValidWires.map_eval_eq (ws := tl) (s1.1.trans s2.1) (fun w hw => hvmsb w (by simp [hw])) hx] at hrec
      refine ⟨?_, hrec.2⟩
      have hge_eval : r3.1.eval x r1.2.2 = decide (width ≤ bitsVal (cur.map (c.eval x))) := by
        rw [(s2.1.trans s3.1).eval_eq hx s1.2.2.2.2.1, hsub.1]
      have hq_val : bitsVal ((r3.2.1 ++ [r1.2.2]).map (r3.1.eval x)) =
          bitsVal (r3.2.1.map (r3.1.eval x)) +
          2 ^ tl.length * (decide (width ≤ bitsVal (cur.map (c.eval x)))).toNat := by
        simp only [List.map_append, List.map_singleton, bitsVal_append, bitsVal,
          List.length_map, s3.2.2.1, hge_eval, mul_zero, add_zero]
      have hdiv_step : bitsVal (cur.map (c.eval x)) =
          (decide (width ≤ bitsVal (cur.map (c.eval x)))).toNat * width +
          bitsVal (rem'.map (r2.1.eval x)) := by
        rw [hrem'_eval]
        by_cases hle : width ≤ bitsVal (cur.map (c.eval x))
        · simp [hle]
        · simp [hle]
      rw [hq_val]
      simp only [List.map_cons, msbVal, List.length_cons, List.length_map, pow_succ]
      have h1 := congrArg (· * 2 ^ tl.length) hcur_eval
      have h2 := congrArg (· * 2 ^ tl.length) hdiv_step
      have h3 := hrec.1
      ring_nf at h1 h2 h3 ⊢
      linarith

def mkParityRow {n : ℕ} (c : CB n) (acc : ℕ) (hacc : acc < n + c.size) :
    (ws : List ℕ) → (mask : List Bool) → ValidWires c ws → CB n × ℕ
  | [], _, _ => (c, acc)
  | _, [], _ => (c, acc)
  | w :: wtl, m :: mtl, hvw =>
    if m then
      let r1 := mkXor c acc w hacc (hvw w (by simp))
      let s1 := mkXor_spec c acc w hacc (hvw w (by simp))
      mkParityRow r1.1 r1.2 s1.2.2.1 wtl mtl
        (ValidWires.mono s1.1 (fun u hu => hvw u (by simp [hu])))
    else
      mkParityRow c acc hacc wtl mtl (fun u hu => hvw u (by simp [hu]))

def listXor : List Bool → List Bool → Bool
  | [], _ => false
  | _, [] => false
  | a :: atl, b :: btl => xor (a && b) (listXor atl btl)

lemma mkParityRow_spec {n : ℕ} (ws : List ℕ) :
    ∀ (mask : List Bool) (c : CB n) (acc : ℕ) (hacc : acc < n + c.size) (hvw : ValidWires c ws),
      let res := mkParityRow c acc hacc ws mask hvw
      c.Extends res.1 ∧ res.1.size ≤ c.size + 4 * ws.length ∧ res.2 < n + res.1.size ∧
      ∀ x, x.length = n → res.1.eval x res.2 = xor (c.eval x acc) (listXor (ws.map (c.eval x)) mask) := by
  induction ws with
  | nil =>
    intro mask c acc hacc hvw
    refine ⟨CB.Extends.refl c, by simp [mkParityRow], hacc, ?_⟩
    intro x _
    simp [mkParityRow, listXor]
  | cons w wtl ih =>
    intro mask c acc hacc hvw
    cases mask with
    | nil =>
      refine ⟨CB.Extends.refl c, by simp [mkParityRow], hacc, ?_⟩
      intro x _
      simp [mkParityRow, listXor]
    | cons m mtl =>
      dsimp only [mkParityRow]
      cases m
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have s := ih mtl c acc hacc (fun u hu => hvw u (by simp [hu]))
        refine ⟨s.1, by simp; omega, s.2.2.1, ?_⟩
        intro x hx
        rw [s.2.2.2 x hx]
        simp [listXor]
      · simp only [↓reduceIte]
        have s1 := mkXor_spec c acc w hacc (hvw w (by simp))
        set r1 := mkXor c acc w hacc (hvw w (by simp))
        have s2 := ih mtl r1.1 r1.2 s1.2.2.1
          (ValidWires.mono s1.1 (fun u hu => hvw u (by simp [hu])))
        refine ⟨s1.1.trans s2.1, ?_, s2.2.2.1, ?_⟩
        · exact le_trans s2.2.1 (by rw [s1.2.1]; simp only [List.length_cons]; omega)
        intro x hx
        rw [s2.2.2.2 x hx, s1.2.2.2 x hx,
          ValidWires.map_eval_eq s1.1 (fun u hu => hvw u (by simp [hu])) hx]
        simp only [List.map_cons, listXor, Bool.and_true]
        cases c.eval x acc <;> cases c.eval x w <;> cases listXor (wtl.map (c.eval x)) mtl <;> rfl

def mkParityMat {n : ℕ} (c : CB n) (wFalse : ℕ) (hf : wFalse < n + c.size)
    (ws : List ℕ) (hvw : ValidWires c ws) : List (List Bool) → CB n × List ℕ
  | [] => (c, [])
  | row :: rows =>
    let r1 := mkParityRow c wFalse hf ws row hvw
    let s1 := mkParityRow_spec ws row c wFalse hf hvw
    let r2 := mkParityMat r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      ws (ValidWires.mono s1.1 hvw) rows
    (r2.1, r1.2 :: r2.2)

lemma mkParityMat_spec {n : ℕ} (rows : List (List Bool)) :
    ∀ (c : CB n) (wFalse : ℕ) (hf : wFalse < n + c.size) (ws : List ℕ) (hvw : ValidWires c ws),
      let res := mkParityMat c wFalse hf ws hvw rows
      c.Extends res.1 ∧ res.1.size ≤ c.size + 4 * ws.length * rows.length ∧
      res.2.length = rows.length ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n → c.eval x wFalse = false →
        res.2.map (res.1.eval x) = rows.map (fun row => listXor (ws.map (c.eval x)) row) := by
  induction rows with
  | nil =>
    intro c wFalse hf ws hvw
    exact ⟨CB.Extends.refl c, by simp [mkParityMat], rfl,
      fun _ h => by simp [mkParityMat] at h, fun _ _ _ => rfl⟩
  | cons row tl ih =>
    intro c wFalse hf ws hvw
    dsimp only [mkParityMat]
    have s1 := mkParityRow_spec ws row c wFalse hf hvw
    set r1 := mkParityRow c wFalse hf ws row hvw
    have s2 := ih r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      ws (ValidWires.mono s1.1 hvw)
    set r2 := mkParityMat r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      ws (ValidWires.mono s1.1 hvw) tl
    refine ⟨s1.1.trans s2.1, ?_, by simp [s2.2.2.1], ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith [s1.2.1, s2.2.1]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | htl
      · exact lt_of_lt_of_le s1.2.2.1 (Nat.add_le_add_left s2.1.size_le n)
      · exact s2.2.2.2.1 w htl
    · intro x hx hwf
      simp only [List.map_cons]
      have hwf1 : r1.1.eval x wFalse = false := by rw [s1.1.eval_eq hx hf, hwf]
      rw [s2.1.eval_eq hx s1.2.2.1, s1.2.2.2 x hx, hwf, Bool.false_xor,
        s2.2.2.2.2 x hx hwf1, ValidWires.map_eval_eq s1.1 hvw hx]

def mkDigitSums {n : ℕ} (c : CB n) (wFalse : ℕ) (hf : wFalse < n + c.size) (b : ℕ) :
    (pairs : List (List ℕ × List ℕ)) →
    (∀ p ∈ pairs, p.1.length = b ∧ p.2.length = b ∧ ValidWires c p.1 ∧ ValidWires c p.2) →
    CB n × List ℕ
  | [], _ => (c, [])
  | (xs, zs) :: tl, hps =>
    let hp0 := hps (xs, zs) (by simp)
    let r1 := mkAddWithCin c wFalse hf xs zs (by rw [hp0.1, hp0.2.1]) hp0.2.2.1 hp0.2.2.2
    let s1 := mkAddWithCin_spec xs zs (by rw [hp0.1, hp0.2.1]) c wFalse hf hp0.2.2.1 hp0.2.2.2
    let r2 := mkDigitSums r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n)) b tl
      (fun p hp =>
        let h := hps p (by simp [hp])
        ⟨h.1, h.2.1, ValidWires.mono s1.1 h.2.2.1, ValidWires.mono s1.1 h.2.2.2⟩)
    (r2.1, (r1.2.1 ++ [r1.2.2]) ++ r2.2)

lemma mkDigitSums_spec {n : ℕ} (b : ℕ) (pairs : List (List ℕ × List ℕ)) :
    ∀ (c : CB n) (wFalse : ℕ) (hf : wFalse < n + c.size)
      (hps : ∀ p ∈ pairs, p.1.length = b ∧ p.2.length = b ∧ ValidWires c p.1 ∧ ValidWires c p.2),
      let res := mkDigitSums c wFalse hf b pairs hps
      c.Extends res.1 ∧ res.1.size = c.size + 11 * b * pairs.length ∧
      res.2.length = pairs.length * (b + 1) ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n → c.eval x wFalse = false →
        res.2.map (res.1.eval x) =
        pairs.flatMap (fun p =>
          List.ofFn (fun j : Fin (b + 1) =>
            (bitsVal (p.1.map (c.eval x)) + bitsVal (p.2.map (c.eval x))).testBit j.val)) := by
  induction pairs with
  | nil =>
    intro c wFalse hf hps
    exact ⟨CB.Extends.refl c, by simp [mkDigitSums], by simp [mkDigitSums],
      fun _ h => by simp [mkDigitSums] at h, fun _ _ _ => rfl⟩
  | cons p tl ih =>
    rcases p with ⟨xs, zs⟩
    intro c wFalse hf hps
    dsimp only [mkDigitSums]
    have hp0 := hps (xs, zs) (by simp)
    have s1 := mkAddWithCin_spec xs zs (by rw [hp0.1, hp0.2.1]) c wFalse hf hp0.2.2.1 hp0.2.2.2
    set r1 := mkAddWithCin c wFalse hf xs zs (by rw [hp0.1, hp0.2.1]) hp0.2.2.1 hp0.2.2.2
    have htl : ∀ q ∈ tl, q.1.length = b ∧ q.2.length = b ∧ ValidWires r1.1 q.1 ∧ ValidWires r1.1 q.2 :=
      fun q hq =>
        let h := hps q (by simp [hq])
        ⟨h.1, h.2.1, ValidWires.mono s1.1 h.2.2.1, ValidWires.mono s1.1 h.2.2.2⟩
    have s2 := ih r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n)) htl
    set r2 := mkDigitSums r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n)) b tl htl
    refine ⟨s1.1.trans s2.1, ?_, ?_, ?_, ?_⟩
    · have h1 : r1.1.size = c.size + 11 * b := by rw [s1.2.1, hp0.1]
      have h2 : r2.1.size = r1.1.size + 11 * b * tl.length := s2.2.1
      simp only [List.length_cons]
      linarith
    · rw [List.length_append, List.length_append, List.length_singleton, s1.2.2.1, hp0.1, s2.2.2.1, List.length_cons]
      ring
    · apply ValidWires.append
      · apply ValidWires.append (ValidWires.mono s2.1 s1.2.2.2.1)
        intro w hw
        simp only [List.mem_singleton] at hw
        subst hw
        exact lt_of_lt_of_le s1.2.2.2.2.1 (Nat.add_le_add_left s2.1.size_le n)
      · exact s2.2.2.2.1
    · intro x hx hwf
      have hwf1 : r1.1.eval x wFalse = false := by rw [s1.1.eval_eq hx hf, hwf]
      simp only [List.map_append, List.map_singleton, List.flatMap_cons]
      have hpart1 : r1.2.1.map (r2.1.eval x) ++ [r2.1.eval x r1.2.2] =
          List.ofFn (fun j : Fin (b + 1) =>
            (bitsVal (xs.map (c.eval x)) + bitsVal (zs.map (c.eval x))).testBit j.val) := by
        rw [ValidWires.map_eval_eq s2.1 s1.2.2.2.1 hx, s2.1.eval_eq hx s1.2.2.2.2.1]
        have hadd := s1.2.2.2.2.2 x hx
        rw [hwf, hp0.1] at hadd
        have hval : bitsVal (r1.2.1.map (r1.1.eval x) ++ [r1.1.eval x r1.2.2]) =
            bitsVal (xs.map (c.eval x)) + bitsVal (zs.map (c.eval x)) := by
          rw [bitsVal_append, List.length_map, s1.2.2.1, hp0.1, bitsVal, bitsVal, mul_zero, add_zero]
          have hf0 : false.toNat = 0 := rfl
          rw [hf0, add_zero] at hadd
          exact hadd
        apply List.ext_getElem
        · simp [s1.2.2.1, hp0.1]
        · intro j hj1 hj2
          have hget : (r1.2.1.map (r1.1.eval x) ++ [r1.1.eval x r1.2.2])[j]'hj1 =
              (r1.2.1.map (r1.1.eval x) ++ [r1.1.eval x r1.2.2]).getD j false :=
            (List.getD_eq_getElem _ _ hj1).symm
          rw [hget, ← bitsVal_testBit, hval, List.getElem_ofFn]
      have hpart2 : r2.2.map (r2.1.eval x) =
          tl.flatMap (fun p =>
            List.ofFn (fun j : Fin (b + 1) =>
              (bitsVal (p.1.map (c.eval x)) + bitsVal (p.2.map (c.eval x))).testBit j.val)) := by
        rw [s2.2.2.2.2 x hx hwf1]
        refine List.flatMap_congr (fun q hq => ?_)
        have hq0 := hps q (by simp [hq])
        rw [ValidWires.map_eval_eq s1.1 hq0.2.2.1 hx, ValidWires.map_eval_eq s1.1 hq0.2.2.2 hx]
      rw [hpart1, hpart2]

def mkSumSq {n : ℕ} (W b : ℕ) (hbW : 2 * b ≤ W) (c : CB n) (wFalse wTrue : ℕ)
    (hf : wFalse < n + c.size) (ht : wTrue < n + c.size) :
    (pairs : List (List ℕ × List ℕ)) →
    (acc : List ℕ) → acc.length = W → ValidWires c acc →
    (∀ p ∈ pairs, p.1.length = b ∧ p.2.length = b ∧ ValidWires c p.1 ∧ ValidWires c p.2) →
    CB n × List ℕ
  | [], acc, _, _, _ => (c, acc)
  | (xs, zs) :: tl, acc, hacc_len, hvacc, hps =>
    let hp0 := hps (xs, zs) (by simp)
    let r1 := mkDist c wTrue ht xs zs (by rw [hp0.1, hp0.2.1]) hp0.2.2.1 hp0.2.2.2
    let s1 := mkDist_spec c wTrue ht xs zs (by rw [hp0.1, hp0.2.1]) hp0.2.2.1 hp0.2.2.2
    let r2 := mkMulAcc W r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      r1.2 s1.2.2.2.1 r1.2 0 (by have h1 : r1.2.length = xs.length := s1.2.2.1; have h2 : xs.length = b := hp0.1; omega)
      acc hacc_len (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    let s2 := mkMulAcc_spec W r1.2 r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      r1.2 s1.2.2.2.1 0 (by have h1 : r1.2.length = xs.length := s1.2.2.1; have h2 : xs.length = b := hp0.1; omega)
      acc hacc_len (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    mkSumSq W b hbW r2.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      tl r2.2 s2.2.2.1 s2.2.2.2.1
      (fun p hp =>
        let h := hps p (by simp [hp])
        ⟨h.1, h.2.1, ValidWires.mono (s1.1.trans s2.1) h.2.2.1, ValidWires.mono (s1.1.trans s2.1) h.2.2.2⟩)

lemma mkSumSq_spec {n : ℕ} (W b : ℕ) (hbW : 2 * b ≤ W) (pairs : List (List ℕ × List ℕ)) :
    ∀ (c : CB n) (wFalse wTrue : ℕ) (hf : wFalse < n + c.size) (ht : wTrue < n + c.size)
      (acc : List ℕ) (hacc_len : acc.length = W) (hvacc : ValidWires c acc)
      (hps : ∀ p ∈ pairs, p.1.length = b ∧ p.2.length = b ∧ ValidWires c p.1 ∧ ValidWires c p.2),
      let res := mkSumSq W b hbW c wFalse wTrue hf ht pairs acc hacc_len hvacc hps
      c.Extends res.1 ∧ res.1.size = c.size + (28 * b + 12 * W * b) * pairs.length ∧
      res.2.length = W ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n → c.eval x wFalse = false → c.eval x wTrue = true →
        bitsVal (acc.map (c.eval x)) +
          (pairs.map (fun p => (Nat.dist (bitsVal (p.1.map (c.eval x))) (bitsVal (p.2.map (c.eval x)))) ^ 2)).sum < 2 ^ W →
        bitsVal (res.2.map (res.1.eval x)) =
        bitsVal (acc.map (c.eval x)) +
          (pairs.map (fun p => (Nat.dist (bitsVal (p.1.map (c.eval x))) (bitsVal (p.2.map (c.eval x)))) ^ 2)).sum := by
  induction pairs with
  | nil =>
    intro c wFalse wTrue hf ht acc hacc_len hvacc hps
    refine ⟨CB.Extends.refl c, by simp [mkSumSq], hacc_len, hvacc, ?_⟩
    intro x _ _ _ _
    simp [mkSumSq]
  | cons p tl ih =>
    rcases p with ⟨xs, zs⟩
    intro c wFalse wTrue hf ht acc hacc_len hvacc hps
    dsimp only [mkSumSq]
    have hp0 := hps (xs, zs) (by simp)
    have s1 := mkDist_spec c wTrue ht xs zs (by rw [hp0.1, hp0.2.1]) hp0.2.2.1 hp0.2.2.2
    set r1 := mkDist c wTrue ht xs zs (by rw [hp0.1, hp0.2.1]) hp0.2.2.1 hp0.2.2.2
    have s2 := mkMulAcc_spec W r1.2 r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      r1.2 s1.2.2.2.1 0 (by have h1 : r1.2.length = xs.length := s1.2.2.1; have h2 : xs.length = b := hp0.1; omega)
      acc hacc_len (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    set r2 := mkMulAcc W r1.1 wFalse (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      r1.2 s1.2.2.2.1 r1.2 0 (by have h1 : r1.2.length = xs.length := s1.2.2.1; have h2 : xs.length = b := hp0.1; omega)
      acc hacc_len (ValidWires.mono s1.1 hvacc) s1.2.2.2.1
    have htl : ∀ q ∈ tl, q.1.length = b ∧ q.2.length = b ∧
        ValidWires r2.1 q.1 ∧ ValidWires r2.1 q.2 :=
      fun q hq =>
        let h := hps q (by simp [hq])
        ⟨h.1, h.2.1, ValidWires.mono (s1.1.trans s2.1) h.2.2.1, ValidWires.mono (s1.1.trans s2.1) h.2.2.2⟩
    have s3 := ih r2.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left (s1.1.trans s2.1).size_le n))
      r2.2 s2.2.2.1 s2.2.2.2.1 htl
    refine ⟨s1.1.trans (s2.1.trans s3.1), ?_, s3.2.2.1, s3.2.2.2.1, ?_⟩
    · have h1 : r1.1.size = c.size + 28 * b := by rw [s1.2.1, hp0.1]
      have h2 : r2.1.size = r1.1.size + 12 * W * b := by rw [s2.2.1, s1.2.2.1, hp0.1]
      have h3 : (mkSumSq W b hbW r2.1 _ _ _ _ _ _ _ _ _).1.size =
          r2.1.size + (28 * b + 12 * W * b) * tl.length := s3.2.1
      simp only [List.length_cons]
      linarith
    · intro x hx hwf hwt hbound
      have hwf1 : r1.1.eval x wFalse = false := by rw [s1.1.eval_eq hx hf, hwf]
      have hwf2 : r2.1.eval x wFalse = false := by rw [(s1.1.trans s2.1).eval_eq hx hf, hwf]
      have hwt2 : r2.1.eval x wTrue = true := by rw [(s1.1.trans s2.1).eval_eq hx ht, hwt]
      have hdist := s1.2.2.2.2 x hx hwt
      have hsq_eq : 2 ^ 0 * bitsVal (r1.2.map (r1.1.eval x)) * bitsVal (r1.2.map (r1.1.eval x)) =
          (Nat.dist (bitsVal (xs.map (c.eval x))) (bitsVal (zs.map (c.eval x)))) ^ 2 := by
        rw [pow_zero, one_mul, hdist, sq]
      simp only [List.map_cons, List.sum_cons] at hbound ⊢
      have hbound1 : bitsVal (acc.map (r1.1.eval x)) +
          2 ^ 0 * bitsVal (r1.2.map (r1.1.eval x)) * bitsVal (r1.2.map (r1.1.eval x)) < 2 ^ W := by
        rw [ValidWires.map_eval_eq s1.1 hvacc hx, hsq_eq]
        omega
      have hr2_val := s2.2.2.2.2 x hx hwf1 hbound1
      rw [ValidWires.map_eval_eq s1.1 hvacc hx, hsq_eq] at hr2_val
      have htl_map : tl.map (fun q => (Nat.dist (bitsVal (q.1.map (r2.1.eval x)))
          (bitsVal (q.2.map (r2.1.eval x)))) ^ 2) =
          tl.map (fun q => (Nat.dist (bitsVal (q.1.map (c.eval x)))
          (bitsVal (q.2.map (c.eval x)))) ^ 2) := by
        refine List.map_congr_left (fun q hq => ?_)
        have hq0 := hps q (by simp [hq])
        rw [ValidWires.map_eval_eq (s1.1.trans s2.1) hq0.2.2.1 hx,
            ValidWires.map_eval_eq (s1.1.trans s2.1) hq0.2.2.2 hx]
      have hrec := s3.2.2.2.2 x hx hwf2 hwt2
      rw [hr2_val, htl_map] at hrec
      have hbound2 : bitsVal (acc.map (c.eval x)) +
          (Nat.dist (bitsVal (xs.map (c.eval x))) (bitsVal (zs.map (c.eval x)))) ^ 2 +
          (tl.map (fun q => (Nat.dist (bitsVal (q.1.map (c.eval x)))
            (bitsVal (q.2.map (c.eval x)))) ^ 2)).sum < 2 ^ W := by
        omega
      rw [hrec hbound2]
      omega

def mkSubDigits {n : ℕ} (c : CB n) (wFalse wTrue : ℕ)
    (hf : wFalse < n + c.size) (ht : wTrue < n + c.size) (b : ℕ) :
    (pairs : List (List ℕ × List ℕ)) →
    (∀ p ∈ pairs, p.1.length = b + 1 ∧ p.2.length = b ∧ ValidWires c p.1 ∧ ValidWires c p.2) →
    CB n × List ℕ
  | [], _ => (c, [])
  | (ss, ys) :: tl, hps =>
    let hp0 := hps (ss, ys) (by simp)
    let ysExt := ys ++ [wFalse]
    have hye_len : ss.length = ysExt.length := by simp [ysExt, hp0.1, hp0.2.1]
    have hye_val : ValidWires c ysExt :=
      ValidWires.append hp0.2.2.2 (fun w hw => by simp at hw; subst hw; exact hf)
    let r1 := mkSubGe c wTrue ht ss ysExt hye_len hp0.2.2.1 hye_val
    let s1 := mkSubGe_spec c wTrue ht ss ysExt hye_len hp0.2.2.1 hye_val
    let r2 := mkSubDigits r1.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n)) b tl
      (fun p hp =>
        let h := hps p (by simp [hp])
        ⟨h.1, h.2.1, ValidWires.mono s1.1 h.2.2.1, ValidWires.mono s1.1 h.2.2.2⟩)
    (r2.1, r1.2.1.take b ++ r2.2)

lemma mkSubDigits_spec {n : ℕ} (b : ℕ) (pairs : List (List ℕ × List ℕ)) :
    ∀ (c : CB n) (wFalse wTrue : ℕ) (hf : wFalse < n + c.size) (ht : wTrue < n + c.size)
      (hps : ∀ p ∈ pairs, p.1.length = b + 1 ∧ p.2.length = b ∧ ValidWires c p.1 ∧ ValidWires c p.2),
      let res := mkSubDigits c wFalse wTrue hf ht b pairs hps
      c.Extends res.1 ∧ res.1.size = c.size + 12 * (b + 1) * pairs.length ∧
      res.2.length = pairs.length * b ∧ ValidWires res.1 res.2 ∧
      ∀ x, x.length = n → c.eval x wFalse = false → c.eval x wTrue = true →
        (∀ p ∈ pairs, bitsVal (p.2.map (c.eval x)) ≤ bitsVal (p.1.map (c.eval x)) ∧
          bitsVal (p.1.map (c.eval x)) - bitsVal (p.2.map (c.eval x)) < 2 ^ b) →
        res.2.map (res.1.eval x) =
        pairs.flatMap (fun p =>
          List.ofFn (fun j : Fin b =>
            (bitsVal (p.1.map (c.eval x)) - bitsVal (p.2.map (c.eval x))).testBit j.val)) := by
  induction pairs with
  | nil =>
    intro c wFalse wTrue hf ht hps
    exact ⟨CB.Extends.refl c, by simp [mkSubDigits], by simp [mkSubDigits],
      fun _ h => by simp [mkSubDigits] at h, fun _ _ _ _ _ => rfl⟩
  | cons p tl ih =>
    rcases p with ⟨ss, ys⟩
    intro c wFalse wTrue hf ht hps
    dsimp only [mkSubDigits]
    have hp0 := hps (ss, ys) (by simp)
    let ysExt := ys ++ [wFalse]
    have hye_len : ss.length = ysExt.length := by simp [ysExt, hp0.1, hp0.2.1]
    have hye_val : ValidWires c ysExt :=
      ValidWires.append hp0.2.2.2 (fun w hw => by simp at hw; subst hw; exact hf)
    have s1 := mkSubGe_spec c wTrue ht ss ysExt hye_len hp0.2.2.1 hye_val
    set r1 := mkSubGe c wTrue ht ss ysExt hye_len hp0.2.2.1 hye_val
    have htl : ∀ q ∈ tl, q.1.length = b + 1 ∧ q.2.length = b ∧
        ValidWires r1.1 q.1 ∧ ValidWires r1.1 q.2 :=
      fun q hq =>
        let h := hps q (by simp [hq])
        ⟨h.1, h.2.1, ValidWires.mono s1.1 h.2.2.1, ValidWires.mono s1.1 h.2.2.2⟩
    have s2 := ih r1.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n)) htl
    set r2 := mkSubDigits r1.1 wFalse wTrue
      (lt_of_lt_of_le hf (Nat.add_le_add_left s1.1.size_le n))
      (lt_of_lt_of_le ht (Nat.add_le_add_left s1.1.size_le n)) b tl htl
    refine ⟨s1.1.trans s2.1, ?_, ?_, ?_, ?_⟩
    · have h1 : r1.1.size = c.size + 12 * (b + 1) := by rw [s1.2.1, hp0.1]
      have h2 : r2.1.size = r1.1.size + 12 * (b + 1) * tl.length := s2.2.1
      simp only [List.length_cons]
      linarith
    · rw [List.length_append, List.length_take, s1.2.2.1, hp0.1, s2.2.2.1, List.length_cons,
        Nat.min_eq_left (by omega)]
      ring
    · exact ValidWires.append (ValidWires.mono s2.1 (ValidWires.take s1.2.2.2.1 b)) s2.2.2.2.1
    · intro x hx hwf hwt hcond
      have hwf1 : r1.1.eval x wFalse = false := by rw [s1.1.eval_eq hx hf, hwf]
      have hwt1 : r1.1.eval x wTrue = true := by rw [s1.1.eval_eq hx ht, hwt]
      have h0 := hcond (ss, ys) (by simp)
      have hye_eval : bitsVal (ysExt.map (c.eval x)) = bitsVal (ys.map (c.eval x)) := by
        simp [ysExt, bitsVal_append, bitsVal, hwf]
      have hsub := (s1.2.2.2.2.2 x hx hwt).2 (by rw [hye_eval]; exact h0.1)
      rw [hye_eval] at hsub
      simp only [List.map_append, List.flatMap_cons]
      have hpart1 : (r1.2.1.take b).map (r2.1.eval x) =
          List.ofFn (fun j : Fin b =>
            (bitsVal (ss.map (c.eval x)) - bitsVal (ys.map (c.eval x))).testBit j.val) := by
        rw [ValidWires.map_eval_eq s2.1 (ValidWires.take s1.2.2.2.1 b) hx, List.map_take]
        have hval_take : bitsVal ((r1.2.1.map (r1.1.eval x)).take b) =
            bitsVal (ss.map (c.eval x)) - bitsVal (ys.map (c.eval x)) := by
          rw [bitsVal_take_of_lt _ b (by rw [hsub]; exact h0.2), hsub]
        apply List.ext_getElem
        · simp [s1.2.2.1, hp0.1]
        · intro j hj1 hj2
          have hget : ((r1.2.1.map (r1.1.eval x)).take b)[j]'hj1 =
              ((r1.2.1.map (r1.1.eval x)).take b).getD j false :=
            (List.getD_eq_getElem _ _ hj1).symm
          rw [hget, ← bitsVal_testBit, hval_take, List.getElem_ofFn]
      have hpart2 : r2.2.map (r2.1.eval x) =
          tl.flatMap (fun p =>
            List.ofFn (fun j : Fin b =>
              (bitsVal (p.1.map (c.eval x)) - bitsVal (p.2.map (c.eval x))).testBit j.val)) := by
        have hcond_tl : ∀ q ∈ tl, bitsVal (q.2.map (r1.1.eval x)) ≤ bitsVal (q.1.map (r1.1.eval x)) ∧
            bitsVal (q.1.map (r1.1.eval x)) - bitsVal (q.2.map (r1.1.eval x)) < 2 ^ b := by
          intro q hq
          have hq0 := hps q (by simp [hq])
          rw [ValidWires.map_eval_eq s1.1 hq0.2.2.1 hx, ValidWires.map_eval_eq s1.1 hq0.2.2.2 hx]
          exact hcond q (by simp [hq])
        rw [s2.2.2.2.2 x hx hwf1 hwt1 hcond_tl]
        refine List.flatMap_congr (fun q hq => ?_)
        have hq0 := hps q (by simp [hq])
        rw [ValidWires.map_eval_eq s1.1 hq0.2.2.1 hx, ValidWires.map_eval_eq s1.1 hq0.2.2.2 hx]
      rw [hpart1, hpart2]

lemma listXor_ofFn {N : ℕ} (u v : Fin N → Bool) :
    listXor (List.ofFn u) (List.ofFn v) =
    decide ((∑ i : Fin N, if u i && v i then (1 : ZMod 2) else 0) = 1) := by
  induction N with
  | zero =>
    simp [listXor]
  | succ N ih =>
    rw [List.ofFn_succ, List.ofFn_succ, listXor, ih, Fin.sum_univ_succ]
    generalize (∑ i : Fin N, if u i.succ && v i.succ then (1 : ZMod 2) else 0) = s
    cases u 0 <;> cases v 0 <;> revert s <;> decide

lemma exists_sparse_parity_matrix (m b t : ℕ) (htb : t * b ≤ m) :
    ∃ H : Fin (2 * m + 1) → Fin (m * b) → Bool,
      ∀ e : Fin (m * b) → Bool,
        e ≠ (fun _ => false) →
        (Finset.univ.filter (fun i : Fin m =>
          ∃ j : Fin b, e ⟨i.val * b + j.val, by
            have := Nat.mul_le_mul_right b (Nat.le_of_lt_succ (show i.val + 1 < m + 1 by omega))
            nlinarith [i.isLt, j.isLt]⟩ = true)).card ≤ t →
        ∃ r : Fin (2 * m + 1),
          listXor (List.ofFn e) (List.ofFn (H r)) = true := by
  classical
  let s := 2 * m + 1
  let N := m * b
  let blockOf : Fin m → Fin b → Fin N := fun i j =>
    ⟨i.val * b + j.val, by dsimp only [N]; nlinarith [i.isLt, j.isLt]⟩
  let Bad : Finset (Fin N → Bool) := Finset.univ.filter (fun e =>
    e ≠ (fun _ => false) ∧
    (Finset.univ.filter (fun i : Fin m => ∃ j : Fin b, e (blockOf i j) = true)).card ≤ t)
  have hBad_card : Bad.card ≤ 2 ^ (2 * m) := by
    let suppOf : (Fin N → Bool) → Finset (Fin m) := fun e =>
      Finset.univ.filter (fun i : Fin m => ∃ j : Fin b, e (blockOf i j) = true)
    let SmallSets : Finset (Finset (Fin m)) := Finset.univ.filter (fun S => S.card ≤ t)
    have hsub : Bad ⊆ SmallSets.biUnion (fun S =>
        Finset.univ.filter (fun e : Fin N → Bool => ∀ i : Fin m, i ∉ S → ∀ j : Fin b, e (blockOf i j) = false)) := by
      intro e he
      have hmem := (Finset.mem_filter.mp he).2
      refine Finset.mem_biUnion.mpr ⟨suppOf e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.2⟩, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro i hi j
      by_contra htrue
      have htr : e (blockOf i j) = true := by cases h : e (blockOf i j) <;> simp_all
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨j, htr⟩⟩)
    have hfiber : ∀ S ∈ SmallSets,
        (Finset.univ.filter (fun e : Fin N → Bool =>
          ∀ i : Fin m, i ∉ S → ∀ j : Fin b, e (blockOf i j) = false)).card ≤ 2 ^ m := by
      intro S hS
      have hScard : S.card ≤ t := (Finset.mem_filter.mp hS).2
      let A := Finset.univ.filter (fun e : Fin N → Bool =>
        ∀ i : Fin m, i ∉ S → ∀ j : Fin b, e (blockOf i j) = false)
      let f : (Fin N → Bool) → (S × Fin b → Bool) := fun e p => e (blockOf p.1.1 p.2)
      have hinj : Set.InjOn f A := by
        intro e1 he1 e2 he2 hfe
        have h1 := (Finset.mem_filter.mp he1).2
        have h2 := (Finset.mem_filter.mp he2).2
        ext idx
        have hbpos : 0 < b := by
          by_contra hb0
          have : b = 0 := by omega
          have hlt := idx.isLt
          simp [N, this] at hlt
        let i0 : Fin m := ⟨idx.val / b, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact idx.isLt)⟩
        let j0 : Fin b := ⟨idx.val % b, Nat.mod_lt _ hbpos⟩
        have hidx : idx = blockOf i0 j0 := by
          ext
          dsimp only [blockOf, i0, j0]
          linarith [Nat.div_add_mod idx.val b]
        rw [hidx]
        by_cases hiS : i0 ∈ S
        · exact congrFun hfe (⟨i0, hiS⟩, j0)
        · rw [h1 i0 hiS j0, h2 i0 hiS j0]
      have hle1 : A.card ≤ (Finset.univ : Finset (S × Fin b → Bool)).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
      have hcard_rhs : (Finset.univ : Finset (S × Fin b → Bool)).card = 2 ^ (S.card * b) := by
        simp [Fintype.card_fun, Fintype.card_prod]
      rw [hcard_rhs] at hle1
      have hexp : S.card * b ≤ m := (Nat.mul_le_mul_right b hScard).trans htb
      exact hle1.trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hexp)
    calc
      Bad.card ≤ (SmallSets.biUnion (fun S =>
          Finset.univ.filter (fun e : Fin N → Bool =>
            ∀ i : Fin m, i ∉ S → ∀ j : Fin b, e (blockOf i j) = false))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ S ∈ SmallSets, (Finset.univ.filter (fun e : Fin N → Bool =>
            ∀ i : Fin m, i ∉ S → ∀ j : Fin b, e (blockOf i j) = false)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ SmallSets, 2 ^ m := Finset.sum_le_sum hfiber
      _ = SmallSets.card * 2 ^ m := by simp
      _ ≤ (Finset.univ : Finset (Finset (Fin m))).card * 2 ^ m :=
        Nat.mul_le_mul_right _ (Finset.card_le_univ SmallSets)
      _ = 2 ^ (2 * m) := by
        simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, ← pow_add]
        congr 1
        omega
  have hsingle : ∀ e ∈ Bad,
      (Finset.univ.filter (fun H : Fin s → Fin N → Bool =>
        ∀ r : Fin s, listXor (List.ofFn e) (List.ofFn (H r)) = false)).card =
      2 ^ (s * (N - 1)) := by
    intro e he
    have hne : e ≠ (fun _ => false) := (Finset.mem_filter.mp he).2.1
    have hex : ∃ j0 : Fin N, e j0 = true := by
      by_contra hall
      apply hne
      ext j
      cases h : e j
      · rfl
      · exact absurd ⟨j, h⟩ hall
    rcases hex with ⟨j0, hj0⟩
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j0.isLt
    let Other := {j : Fin N // j ≠ j0}
    let f : (Fin s → Fin N → Bool) → (Fin s → Other → Bool) := fun H r j => H r j.1
    let A := Finset.univ.filter (fun H : Fin s → Fin N → Bool =>
      ∀ r : Fin s, listXor (List.ofFn e) (List.ofFn (H r)) = false)
    have hcard_bij : A.card = Fintype.card (Fin s → Other → Bool) := by
      refine Finset.card_bij (fun H _ => f H) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro H1 hH1 H2 hH2 hfe
        have ha1 := (Finset.mem_filter.mp hH1).2
        have ha2 := (Finset.mem_filter.mp hH2).2
        ext r j
        by_cases hj : j = j0
        · subst j
          have h1 := ha1 r
          have h2 := ha2 r
          rw [listXor_ofFn] at h1 h2
          have hs1 : (∑ i : Fin N, if e i && H1 r i then (1 : ZMod 2) else 0) = 0 := by
            generalize (∑ i : Fin N, if e i && H1 r i then (1 : ZMod 2) else 0) = v at h1 ⊢
            revert v h1; decide
          have hs2 : (∑ i : Fin N, if e i && H2 r i then (1 : ZMod 2) else 0) = 0 := by
            generalize (∑ i : Fin N, if e i && H2 r i then (1 : ZMod 2) else 0) = v at h2 ⊢
            revert v h2; decide
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)] at hs1 hs2
          have hrest : (∑ i ∈ Finset.univ.erase j0, if e i && H1 r i then (1 : ZMod 2) else 0) =
              ∑ i ∈ Finset.univ.erase j0, if e i && H2 r i then (1 : ZMod 2) else 0 := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have hne' : i ≠ j0 := (Finset.mem_erase.mp hi).1
            have heq := congrFun (congrFun hfe r) ⟨i, hne'⟩
            dsimp only [f] at heq
            rw [heq]
          rw [hrest, hj0, Bool.true_and] at hs1
          rw [hj0, Bool.true_and] at hs2
          have hbit : (if H1 r j0 then (1 : ZMod 2) else 0) = if H2 r j0 then (1 : ZMod 2) else 0 := by
            linear_combination hs1 - hs2
          cases h1' : H1 r j0 <;> cases h2' : H2 r j0 <;> simp_all
        · exact congrFun (congrFun hfe r) ⟨j, hj⟩
      · intro g _
        have hH_alt : ∃ H0 : Fin s → Fin N → Bool, H0 ∈ A ∧ f H0 = g := by
          let rowSum : Fin s → ZMod 2 := fun r =>
            ∑ i : Fin N, if h : i = j0 then 0 else if e i && g r ⟨i, h⟩ then 1 else 0
          let H0 : Fin s → Fin N → Bool := fun r j =>
            if hj : j = j0 then decide (rowSum r = 1) else g r ⟨j, hj⟩
          refine ⟨H0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · intro r
            rw [listXor_ofFn]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
            have hsum_er : (∑ i ∈ Finset.univ.erase j0, if e i && H0 r i then (1 : ZMod 2) else 0) = rowSum r := by
              dsimp only [rowSum]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
              simp only [↓reduceDIte, zero_add]
              refine Finset.sum_congr rfl (fun i hi => ?_)
              have hne' : i ≠ j0 := (Finset.mem_erase.mp hi).1
              simp [H0, hne']
            rw [hsum_er]
            have hj0_val : H0 r j0 = decide (rowSum r = 1) := by simp [H0]
            rw [hj0, Bool.true_and, hj0_val]
            generalize rowSum r = v
            revert v
            decide
          · ext r ⟨j, hj⟩
            simp [f, H0, hj]
        rcases hH_alt with ⟨H0, hH0, hf0⟩
        exact ⟨H0, hH0, hf0⟩
    rw [hcard_bij]
    have hcard_other : Fintype.card Other = N - 1 := by
      have h1 : Fintype.card Other = (Finset.univ.erase j0).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext j
        simp
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
    simp [Fintype.card_fun, hcard_other, pow_mul, mul_comm]
  let Fail : Finset (Fin s → Fin N → Bool) :=
    Bad.biUnion (fun e => Finset.univ.filter (fun H : Fin s → Fin N → Bool =>
      ∀ r : Fin s, listXor (List.ofFn e) (List.ofFn (H r)) = false))
  have hFail_lt : Fail.card < (Finset.univ : Finset (Fin s → Fin N → Bool)).card := by
    have h1 : Fail.card ≤ ∑ e ∈ Bad, (Finset.univ.filter (fun H : Fin s → Fin N → Bool =>
        ∀ r : Fin s, listXor (List.ofFn e) (List.ofFn (H r)) = false)).card :=
      Finset.card_biUnion_le
    have h2 : (∑ e ∈ Bad, (Finset.univ.filter (fun H : Fin s → Fin N → Bool =>
        ∀ r : Fin s, listXor (List.ofFn e) (List.ofFn (H r)) = false)).card) =
        Bad.card * 2 ^ (s * (N - 1)) := by
      rw [Finset.sum_congr rfl hsingle, Finset.sum_const, smul_eq_mul]
    have htot : (Finset.univ : Finset (Fin s → Fin N → Bool)).card = 2 ^ (s * N) := by
      simp [Fintype.card_fun, pow_mul, mul_comm]
    by_cases hN0 : N = 0
    · have hBad0 : Bad = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        have hne := (Finset.mem_filter.mp he).2.1
        apply hne
        ext j
        have := j.isLt
        omega
      have hF0 : Fail.card = 0 := by simp [Fail, hBad0]
      rw [hF0, htot]
      positivity
    · have hpow_split : 2 ^ (s * N) = 2 ^ s * 2 ^ (s * (N - 1)) := by
        rw [← pow_add]
        congr 1
        have h1' : N = (N - 1) + 1 := by omega
        calc
          s * N = s * ((N - 1) + 1) := by rw [← h1']
          _ = s + s * (N - 1) := by ring
      have hlt_s : 2 ^ (2 * m) < 2 ^ s :=
        Nat.pow_lt_pow_right (by omega : 1 < 2) (by dsimp only [s]; omega)
      have hlt_b : Bad.card < 2 ^ s := lt_of_le_of_lt hBad_card hlt_s
      rw [htot, hpow_split]
      calc
        Fail.card ≤ Bad.card * 2 ^ (s * (N - 1)) := by rw [← h2]; exact h1
        _ < 2 ^ s * 2 ^ (s * (N - 1)) := Nat.mul_lt_mul_of_pos_right hlt_b (by positivity)
  have hne : (Finset.univ \ Fail).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Finset.univ ⊆ Fail := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle := Finset.card_le_card hsub
    omega
  rcases hne with ⟨H, hH⟩
  have hnotF : H ∉ Fail := (Finset.mem_sdiff.mp hH).2
  refine ⟨H, ?_⟩
  intro e hne hcard
  have heBad : e ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_univ e, hne, hcard⟩
  by_contra hall
  push Not at hall
  have hmemF : H ∈ Fail := Finset.mem_biUnion.mpr ⟨e, heBad,
    Finset.mem_filter.mpr ⟨Finset.mem_univ H, fun r => by
      cases hr : listXor (List.ofFn e) (List.ofFn (H r))
      · rfl
      · exact absurd hr (hall r)⟩⟩
  exact hnotF hmemF

lemma dist_sq_parallelogram (x z x' z' : ℕ) (hsum : x + z = x' + z') :
    ((Nat.dist x z : ℤ) ^ 2 + (Nat.dist x' z' : ℤ) ^ 2 - 2 * (Nat.dist x z' : ℤ) ^ 2) =
    2 * ((x' : ℤ) - (x : ℤ)) ^ 2 := by
  have hsq : ∀ a b : ℕ, ((Nat.dist a b : ℤ)) ^ 2 = ((a : ℤ) - (b : ℤ)) ^ 2 := by
    intro a b
    dsimp only [Nat.dist]
    by_cases h : a ≤ b
    · have h1 : a - b = 0 := Nat.sub_eq_zero_of_le h
      rw [h1, zero_add, Nat.cast_sub h]
      ring
    · have hle : b ≤ a := by omega
      have h1 : b - a = 0 := Nat.sub_eq_zero_of_le hle
      rw [h1, add_zero, Nat.cast_sub hle]
  rw [hsq x z, hsq x' z', hsq x z']
  have hsumZ : (x : ℤ) + (z : ℤ) = (x' : ℤ) + (z' : ℤ) := by exact_mod_cast hsum
  have hz : (z : ℤ) = (x' : ℤ) + (z' : ℤ) - (x : ℤ) := by omega
  rw [hz]
  ring

lemma nat_dist_sq_sum_bound {m : ℕ} (x z x' z' : Fin m → ℕ)
    (hsum : ∀ i : Fin m, x i + z i = x' i + z' i)
    {width : ℕ} (hw : 0 < width)
    (hb1 : (∑ i : Fin m, (Nat.dist (x i) (z i)) ^ 2) / width =
           (∑ i : Fin m, (Nat.dist (x i) (z' i)) ^ 2) / width)
    (hb2 : (∑ i : Fin m, (Nat.dist (x' i) (z' i)) ^ 2) / width =
           (∑ i : Fin m, (Nat.dist (x i) (z' i)) ^ 2) / width) :
    (Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card ≤ width - 1 := by
  set Da := ∑ i : Fin m, (Nat.dist (x i) (z i)) ^ 2
  set Db := ∑ i : Fin m, (Nat.dist (x i) (z' i)) ^ 2
  set Dt := ∑ i : Fin m, (Nat.dist (x' i) (z' i)) ^ 2
  have hpar : (Da : ℤ) + (Dt : ℤ) - 2 * (Db : ℤ) = 2 * ∑ i : Fin m, ((x' i : ℤ) - (x i : ℤ)) ^ 2 := by
    dsimp only [Da, Db, Dt]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => dist_sq_parallelogram (x i) (z i) (x' i) (z' i) (hsum i))
  have hda : (Da : ℤ) - (Db : ℤ) ≤ (width - 1 : ℤ) := by
    have h1 := Nat.div_add_mod Da width
    have h2 := Nat.div_add_mod Db width
    have hm1 : Da % width < width := Nat.mod_lt Da hw
    rw [hb1] at h1
    omega
  have hdt : (Dt : ℤ) - (Db : ℤ) ≤ (width - 1 : ℤ) := by
    have h1 := Nat.div_add_mod Dt width
    have h2 := Nat.div_add_mod Db width
    have hm1 : Dt % width < width := Nat.mod_lt Dt hw
    rw [hb2] at h1
    omega
  have hsum_le : (∑ i : Fin m, ((x' i : ℤ) - (x i : ℤ)) ^ 2) ≤ (width - 1 : ℤ) := by
    linarith
  have hcard_le : ((Finset.univ.filter (fun i : Fin m => x i ≠ x' i)).card : ℤ) ≤
      ∑ i : Fin m, ((x' i : ℤ) - (x i : ℤ)) ^ 2 := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hne : x i ≠ x' i
    · rw [if_pos hne]
      have hneZ : (x' i : ℤ) - (x i : ℤ) ≠ 0 := by omega
      have h1 : 1 ≤ |((x' i : ℤ) - (x i : ℤ))| := by
        have := abs_pos.mpr hneZ
        omega
      nlinarith [sq_abs ((x' i : ℤ) - (x i : ℤ))]
    · rw [if_neg hne]
      exact sq_nonneg _
  omega

lemma tag_budget_ok (k h : ℕ) (hh : 8 ≤ h) (hk : 2 * h ≤ k) :
    let b := h / 4
    let m := (k - h) / b
    h + m * (b + 1) + (2 * m + 1) + (k - m * b) + ((k - h) - m * b) ≤ k + 32 * (k / h + h + 1) := by
  intro b m
  have hb2 : 2 ≤ b := by dsimp only [b]; omega
  have h6b : h ≤ 6 * b := by dsimp only [b]; omega
  have hm_le : m ≤ 6 * (k / h + 1) := by
    have hk_lt : k < h * (k / h + 1) := by
      have h1 := Nat.div_add_mod k h
      have h2 := Nat.mod_lt k (by omega : 0 < h)
      nlinarith
    have hk_le : k - h < b * (6 * (k / h + 1)) := by
      have : k - h ≤ k := Nat.sub_le k h
      nlinarith
    have hdiv : (k - h) / b < 6 * (k / h + 1) :=
      Nat.div_lt_of_lt_mul hk_le
    dsimp only [m]
    omega
  have hmb_le : m * b ≤ k - h := Nat.div_mul_le_self (k - h) b
  have hrem_lt : (k - h) - m * b < b := by
    have h1 := Nat.div_add_mod (k - h) b
    have h2 := Nat.mod_lt (k - h) (by omega : 0 < b)
    have hcomm : b * m = m * b := mul_comm b m
    dsimp only [m] at hcomm ⊢
    omega
  have hb_le_h : b ≤ h := by dsimp only [b]; omega
  have hm_exp : m * (b + 1) = m * b + m := by ring
  omega

lemma size_bound_poly6 (k h : ℕ) (hh : 8 ≤ h) (hk : 2 * h ≤ k) :
    let b := h / 4
    let m := (k - h) / b
    3 + 11 * b * m + 4 * (m * b) * (2 * m + 1) + (28 * b + 12 * (2 * k) * b) * m +
      16 * (2 * k + 1) * (2 * k) ≤ (k + 1) ^ 6 := by
  intro b m
  have hk16 : 16 ≤ k := by omega
  have hb_le : b ≤ k := by dsimp only [b]; omega
  have hm_le : m ≤ k := by
    have hb1 : 1 ≤ b := by dsimp only [b]; omega
    exact (Nat.div_le_self (k - h) b).trans (Nat.sub_le k h)
  have hmb_le : m * b ≤ k := (Nat.div_mul_le_self (k - h) b).trans (Nat.sub_le k h)
  have h1 : 11 * b * m ≤ 11 * k := by nlinarith
  have h2 : 4 * (m * b) * (2 * m + 1) ≤ 12 * k ^ 2 := by nlinarith
  have h3 : (28 * b + 12 * (2 * k) * b) * m ≤ 52 * k ^ 2 := by nlinarith
  have h4 : 16 * (2 * k + 1) * (2 * k) ≤ 96 * k ^ 2 := by nlinarith
  have hsum : 3 + 11 * b * m + 4 * (m * b) * (2 * m + 1) + (28 * b + 12 * (2 * k) * b) * m +
      16 * (2 * k + 1) * (2 * k) ≤ 174 * (k + 1) ^ 2 := by
    nlinarith
  have hk2 : 174 ≤ (k + 1) ^ 4 := by
    have : 17 ≤ k + 1 := by omega
    nlinarith
  calc
    3 + 11 * b * m + 4 * (m * b) * (2 * m + 1) + (28 * b + 12 * (2 * k) * b) * m +
        16 * (2 * k + 1) * (2 * k) ≤ 174 * (k + 1) ^ 2 := hsum
    _ ≤ (k + 1) ^ 4 * (k + 1) ^ 2 := Nat.mul_le_mul_right _ hk2
    _ = (k + 1) ^ 6 := by ring

lemma width_bound_ok (k h : ℕ) (hh : 8 ≤ h) (hk : 2 * h ≤ k) :
    let b := h / 4
    let m := (k - h) / b
    let Q := 2 ^ b
    let width := m * Q ^ 2 / 2 ^ h + 1
    (width - 1) * b ≤ m ∧ width < 2 ^ (2 * k) ∧ m * Q ^ 2 < 2 ^ (2 * k) := by
  intro b m Q width
  have hb2 : 2 ≤ b := by dsimp only [b]; omega
  have h4b : 4 * b ≤ h := by dsimp only [b]; omega
  have hQ4 : Q ^ 2 * Q ^ 2 ≤ 2 ^ h := by
    dsimp only [Q]
    have h1 : (2 ^ b) ^ 2 * (2 ^ b) ^ 2 = 2 ^ (4 * b) := by
      rw [← pow_mul, ← pow_add]
      congr 1; ring
    rw [h1]
    exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) h4b
  have hQ2_pos : 0 < Q ^ 2 := by dsimp only [Q]; positivity
  have hdiv1 : m * Q ^ 2 / 2 ^ h ≤ m / Q ^ 2 := by
    have h1 : m * Q ^ 2 / 2 ^ h ≤ m * Q ^ 2 / (Q ^ 2 * Q ^ 2) :=
      Nat.div_le_div_left hQ4 (by positivity)
    have h2 : m * Q ^ 2 / (Q ^ 2 * Q ^ 2) = m / Q ^ 2 := by
      rw [mul_comm m (Q ^ 2), Nat.mul_div_mul_left m (Q ^ 2) hQ2_pos]
    omega
  have hbQ : b ≤ Q ^ 2 := by
    dsimp only [Q]
    have h1 : b < 2 ^ b := Nat.lt_two_pow_self
    have h2 : 2 ^ b ≤ (2 ^ b) ^ 2 := by nlinarith
    omega
  have hpart1 : (width - 1) * b ≤ m := by
    have hw1 : width - 1 = m * Q ^ 2 / 2 ^ h := Nat.add_sub_cancel _ 1
    rw [hw1]
    calc
      (m * Q ^ 2 / 2 ^ h) * b ≤ (m / Q ^ 2) * b := Nat.mul_le_mul_right b hdiv1
      _ ≤ (m / Q ^ 2) * Q ^ 2 := Nat.mul_le_mul_left _ hbQ
      _ ≤ m := Nat.div_mul_le_self m (Q ^ 2)
  have hm_lt : m < 2 ^ k := by
    have hm_le : m ≤ k := (Nat.div_le_self (k - h) b).trans (Nat.sub_le k h)
    exact lt_of_le_of_lt hm_le Nat.lt_two_pow_self
  have hQ2_le : Q ^ 2 ≤ 2 ^ k := by
    dsimp only [Q]
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)
  have hpart3 : m * Q ^ 2 < 2 ^ (2 * k) := by
    have h2k : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [← pow_add]; congr 1; omega
    rw [h2k]
    calc
      m * Q ^ 2 ≤ m * 2 ^ k := Nat.mul_le_mul_left m hQ2_le
      _ < 2 ^ k * 2 ^ k := Nat.mul_lt_mul_of_pos_right hm_lt (by positivity)
  have hpart2 : width < 2 ^ (2 * k) := by
    have hw_le : m * Q ^ 2 / 2 ^ h ≤ m := by
      exact hdiv1.trans (Nat.div_le_self m (Q ^ 2))
    have h2k_gt : m + 1 < 2 ^ (2 * k) := by
      have hm_le : m ≤ k := (Nat.div_le_self (k - h) b).trans (Nat.sub_le k h)
      have h1 : k + 1 < 2 ^ (2 * k) := by
        have := @Nat.lt_two_pow_self (2 * k)
        omega
      omega
    dsimp only [width]
    omega
  exact ⟨hpart1, hpart2, hpart3⟩

lemma dec_size_poly6 (k h : ℕ) (hh : 8 ≤ h) (hk : 2 * h ≤ k) :
    3 + 12 * (h / 4 + 1) * ((k - h) / (h / 4)) ≤ (k + 1) ^ 6 := by
  set b := h / 4
  set m := (k - h) / b
  have hm_le : m ≤ k := (Nat.div_le_self (k - h) b).trans (Nat.sub_le k h)
  have hmb_le : m * b ≤ k := (Nat.div_mul_le_self (k - h) b).trans (Nat.sub_le k h)
  have hlin : 3 + 12 * (b + 1) * m ≤ 27 * k := by nlinarith
  have hk16 : 16 ≤ k := by omega
  have hsq : 17 * (k + 1) ≤ (k + 1) ^ 2 := by nlinarith
  have h1 : 27 * k ≤ (k + 1) * (k + 1) ^ 2 := by nlinarith
  have hcube : (k + 1) * (k + 1) ^ 2 = (k + 1) ^ 3 := by ring
  have h2 : (k + 1) ^ 3 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

lemma mul_add_lt_mul {m b : ℕ} (i : Fin m) (j : Fin b) : i.val * b + j.val < m * b := by
  nlinarith [i.isLt, j.isLt]

lemma list_flatMap_eq {α β : Type} (f : α → List β) (l : List α) :
    l.flatMap f = (l.map f).flatten := by
  induction l with
  | nil => rfl
  | cons a tl ih => simp [ih]

lemma getD_append_bool (A B : List Bool) (idx : ℕ) :
    (A ++ B).getD idx false = if idx < A.length then A.getD idx false else B.getD (idx - A.length) false := by
  by_cases hlt : idx < A.length
  · have hlt2 : idx < (A ++ B).length := by simp; omega
    simp only [hlt, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ hlt2, List.getD_eq_getElem _ _ hlt, List.getElem_append_left hlt]
  · simp only [hlt, ↓reduceIte]
    by_cases hlt2 : idx < (A ++ B).length
    · have hltB : idx - A.length < B.length := by simp at hlt2; omega
      rw [List.getD_eq_getElem _ _ hlt2, List.getD_eq_getElem _ _ hltB,
        List.getElem_append_right (by omega)]
    · have hgeB : B.length ≤ idx - A.length := by simp at hlt2; omega
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ hgeB]

lemma flatten_ofFn_getD (n d : ℕ) (f : Fin n → Fin d → Bool) (i0 : Fin n) (j0 : Fin d) :
    ((List.ofFn (fun a : Fin n => List.ofFn (f a))).flatten).getD (i0.val * d + j0.val) false =
    f i0 j0 := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, getD_append_bool]
    simp only [List.length_ofFn]
    cases i0 using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, zero_mul, zero_add, j0.isLt, ↓reduceIte]
      have hlt : j0.val < (List.ofFn (f 0)).length := by rw [List.length_ofFn]; exact j0.isLt
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
    | succ i' =>
      have hnot : ¬((i'.val + 1) * d + j0.val < d) := by nlinarith
      simp only [Fin.val_succ, hnot, ↓reduceIte]
      have hsub : (i'.val + 1) * d + j0.val - d = i'.val * d + j0.val := by ring_nf; omega
      rw [hsub]
      exact ih (fun a => f a.succ) i'

lemma xor_and_zmod2 (x y z : Bool) :
    (if xor x y && z then (1 : ZMod 2) else 0) =
    (if x && z then (1 : ZMod 2) else 0) + (if y && z then (1 : ZMod 2) else 0) := by
  cases x <;> cases y <;> cases z <;> decide

end PEqualNP.Outside.L_pcx_283_aux

open PEqualNP.Outside.L_pcx_283_aux

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_pcx_283 :
∃ A : ℕ, 0 < A ∧ ∀ k h : ℕ, 8 ≤ h → 2*h ≤ k →
  let c := k+32*(k/h+h+1)
  let X := Fin k → Bool
  let Z := Fin (k-h) → Bool
  let Word := X × Z
  let raw := fun w : Word => List.ofFn w.1 ++ List.ofFn w.2
  let b := h/4
  let m := (k-h)/b
  let Q := 2^b
  let digit := fun (v : List Bool) (i : Fin m) =>
    ∑ j : Fin b, if v.getD (i.val*b+j.val) false then 2^j.val else 0
  let width := m*Q^2 / 2^h + 1
  let flag := fun (w : Word) (i : Fin h) =>
    let D := ∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j))^2
    (D/width).testBit i.val
  let valid := fun (inputs budget : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧ C.size ≤ budget ∧
    ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)
  ∃ (tag : Word → Fin c → Bool) (enc : PEqualNP.CircuitLowerBounds.Circuit)
    (tw : Fin c → Fin (k+(k-h)+enc.size)) (cw : Fin h → Fin (k+(k-h)+enc.size)),
    valid (k+(k-h)) ((k+1)^A) enc ∧
    (∀ w : Word, (∀ j, (enc.wires (raw w)).getD (tw j).val false = tag w j) ∧
      ∀ j, (enc.wires (raw w)).getD (cw j).val false = flag w j) ∧
    (∀ a b t : Word, a.1 = b.1 → b.2 = t.2 → flag b = flag t → tag t = tag a → a = b ∧ b = t) ∧
    (∀ e : Fin 3,
      let port := fun (i : Fin 3) (w : Word) =>
        if i = 0 then List.ofFn w.1 else if i = 1 then List.ofFn w.2 ++ List.ofFn (flag w)
        else List.ofFn (tag w)
      let len := fun i : Fin 3 => if i = 2 then c else k
      let inputs := len e + len (e+1)
      ∃ (dec : PEqualNP.CircuitLowerBounds.Circuit) (dw : Fin (k+(k-h)) → Fin (inputs+dec.size)),
        valid inputs ((k+1)^A) dec ∧ ∀ (w : Word) (j : Fin (k+(k-h))),
          (dec.wires (port e w ++ port (e+1) w)).getD (dw j).val false = (raw w).getD j.val false) := by
  refine ⟨6, by omega, ?_⟩
  intro k h hh hk c X Z Word raw b m Q digit width flag valid
  have hb_ge2 : 2 ≤ b := by dsimp only [b]; omega
  have hmb_le : m * b ≤ k - h := Nat.div_mul_le_self (k - h) b
  have hm_ge4 : 4 ≤ m := by
    have h4b : 4 * b ≤ k - h := by dsimp only [b]; omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < b)).mpr h4b
  have hwb : (width - 1) * b ≤ m ∧ width < 2 ^ (2 * k) ∧ m * Q ^ 2 < 2 ^ (2 * k) :=
    width_bound_ok k h hh hk
  have hbud : h + m * (b + 1) + (2 * m + 1) + (k - m * b) + ((k - h) - m * b) ≤ c :=
    tag_budget_ok k h hh hk
  have hpoly : 3 + 11 * b * m + 4 * (m * b) * (2 * m + 1) + (28 * b + 12 * (2 * k) * b) * m +
      16 * (2 * k + 1) * (2 * k) ≤ (k + 1) ^ 6 :=
    size_bound_poly6 k h hh hk
  rcases exists_sparse_parity_matrix m b (width - 1) hwb.1 with ⟨H, hH⟩
  let s := 2 * m + 1
  let rem1 := k - m * b
  let rem2 := (k - h) - m * b
  let tagList : Word → List Bool := fun w =>
    List.ofFn (flag w) ++
    (List.ofFn (fun i : Fin m =>
      List.ofFn (fun j : Fin (b + 1) =>
        (digit (List.ofFn w.1) i + digit (List.ofFn w.2) i).testBit j.val))).flatten ++
    List.ofFn (fun r : Fin s =>
      listXor (List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩)) (List.ofFn (H r))) ++
    List.ofFn (fun j : Fin rem1 => w.1 ⟨m * b + j.val, by dsimp only [rem1]; omega⟩) ++
    List.ofFn (fun j : Fin rem2 => w.2 ⟨m * b + j.val, by dsimp only [rem2]; omega⟩)
  have htagList_len : ∀ w : Word, (tagList w).length = h + m * (b + 1) + s + rem1 + rem2 := by
    intro w
    dsimp only [tagList]
    simp only [List.length_append, List.length_ofFn, List.length_flatten, List.map_ofFn,
      Function.comp_def]
    have hsum : (List.ofFn (fun _ : Fin m => b + 1)).sum = m * (b + 1) := by
      simp
    rw [hsum]
  let tag : Word → Fin c → Bool := fun w j => (tagList w).getD j.val false
  let nEnc := k + (k - h)
  have hnEnc_pos : 0 < nEnc := by dsimp only [nEnc]; omega
  let rC := mkConsts (CB.empty nEnc) hnEnc_pos
  have sC := mkConsts_spec (CB.empty nEnc) hnEnc_pos
  let c0 := rC.1
  let wF := rC.2.1
  let wT := rC.2.2
  have hwF_v : wF < nEnc + c0.size := sC.2.2.1
  have hwT_v : wT < nEnc + c0.size := sC.2.2.2.1
  let xDigWires : Fin m → List ℕ := fun i => List.ofFn (fun j : Fin b => i.val * b + j.val)
  let zDigWires : Fin m → List ℕ := fun i => List.ofFn (fun j : Fin b => k + i.val * b + j.val)
  let pairsWires : List (List ℕ × List ℕ) := List.ofFn (fun i : Fin m => (xDigWires i, zDigWires i))
  have hpairs_valid : ∀ p ∈ pairsWires,
      p.1.length = b ∧ p.2.length = b ∧ ValidWires c0 p.1 ∧ ValidWires c0 p.2 := by
    intro p hp
    simp only [pairsWires, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    refine ⟨by simp [xDigWires], by simp [zDigWires], ?_, ?_⟩
    · intro u hu
      simp only [xDigWires, List.mem_ofFn] at hu
      rcases hu with ⟨j, rfl⟩
      have hlt : i.val * b + j.val < m * b := by nlinarith [i.isLt, j.isLt]
      dsimp only [nEnc]
      omega
    · intro u hu
      simp only [zDigWires, List.mem_ofFn] at hu
      rcases hu with ⟨j, rfl⟩
      have hlt : i.val * b + j.val < m * b := by nlinarith [i.isLt, j.isLt]
      dsimp only [nEnc]
      omega
  let rSums := mkDigitSums c0 wF hwF_v b pairsWires hpairs_valid
  have sSums := mkDigitSums_spec b pairsWires c0 wF hwF_v hpairs_valid
  let xCoreWires : List ℕ := List.ofFn (fun idx : Fin (m * b) => idx.val)
  have hxCore_v : ValidWires rSums.1 xCoreWires := by
    intro u hu
    simp only [xCoreWires, List.mem_ofFn] at hu
    rcases hu with ⟨idx, rfl⟩
    dsimp only [nEnc]
    omega
  let Hrows : List (List Bool) := List.ofFn (fun r : Fin s => List.ofFn (H r))
  let rSyn := mkParityMat rSums.1 wF (lt_of_lt_of_le hwF_v (Nat.add_le_add_left sSums.1.size_le nEnc))
    xCoreWires hxCore_v Hrows
  have sSyn := mkParityMat_spec Hrows rSums.1 wF
    (lt_of_lt_of_le hwF_v (Nat.add_le_add_left sSums.1.size_le nEnc)) xCoreWires hxCore_v
  let W := 2 * k
  have hbW : 2 * b ≤ W := by dsimp only [W, b]; omega
  let zeroAcc : List ℕ := List.replicate W wF
  have hext02 : c0.Extends rSyn.1 := sSums.1.trans sSyn.1
  let rSumSq := mkSumSq W b hbW rSyn.1 wF wT
    (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext02.size_le nEnc))
    (lt_of_lt_of_le hwT_v (Nat.add_le_add_left hext02.size_le nEnc))
    pairsWires zeroAcc (by simp [zeroAcc])
    (ValidWires.replicate (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext02.size_le nEnc)))
    (fun p hp =>
      let h := hpairs_valid p hp
      ⟨h.1, h.2.1, ValidWires.mono hext02 h.2.2.1, ValidWires.mono hext02 h.2.2.2⟩)
  have sSumSq := mkSumSq_spec W b hbW pairsWires rSyn.1 wF wT
    (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext02.size_le nEnc))
    (lt_of_lt_of_le hwT_v (Nat.add_le_add_left hext02.size_le nEnc))
    zeroAcc (by simp [zeroAcc])
    (ValidWires.replicate (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext02.size_le nEnc)))
    (fun p hp =>
      let h := hpairs_valid p hp
      ⟨h.1, h.2.1, ValidWires.mono hext02 h.2.2.1, ValidWires.mono hext02 h.2.2.2⟩)
  have hext03 : c0.Extends rSumSq.1 := hext02.trans sSumSq.1
  have hwidth_pos : 0 < width := Nat.succ_pos _
  let rDiv := mkDivLoop W width rSumSq.1 wF wT
    (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext03.size_le nEnc))
    (lt_of_lt_of_le hwT_v (Nat.add_le_add_left hext03.size_le nEnc))
    rSumSq.2.reverse zeroAcc (by simp [zeroAcc])
    (ValidWires.reverse sSumSq.2.2.2.1)
    (ValidWires.replicate (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext03.size_le nEnc)))
  have sDiv := mkDivLoop_spec W width hwidth_pos hwb.2.1 rSumSq.2.reverse rSumSq.1 wF wT
    (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext03.size_le nEnc))
    (lt_of_lt_of_le hwT_v (Nat.add_le_add_left hext03.size_le nEnc))
    zeroAcc (by simp [zeroAcc])
    (ValidWires.reverse sSumSq.2.2.2.1)
    (ValidWires.replicate (lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext03.size_le nEnc)))
  let encCB := rDiv.1
  have hext04 : c0.Extends encCB := hext03.trans sDiv.1
  let flagWires : List ℕ := rDiv.2.1.take h
  have hflagW_len : flagWires.length = h := by
    have h1 : rDiv.2.1.length = rSumSq.2.reverse.length := sDiv.2.2.1
    have h2 : rSumSq.2.length = W := sSumSq.2.2.1
    dsimp only [flagWires]
    rw [List.length_take, h1, List.length_reverse, h2]
    dsimp only [W]
    omega
  have hflagW_v : ValidWires encCB flagWires := ValidWires.take sDiv.2.2.2.2.1 h
  let tail1Wires : List ℕ := List.ofFn (fun j : Fin rem1 => m * b + j.val)
  let tail2Wires : List ℕ := List.ofFn (fun j : Fin rem2 => k + m * b + j.val)
  let tagWires : List ℕ := flagWires ++ rSums.2 ++ rSyn.2 ++ tail1Wires ++ tail2Wires
  have htagW_v : ValidWires encCB tagWires := by
    refine ValidWires.append (ValidWires.append (ValidWires.append (ValidWires.append hflagW_v ?_) ?_) ?_) ?_
    · exact ValidWires.mono (sSyn.1.trans (sSumSq.1.trans sDiv.1)) sSums.2.2.2.1
    · exact ValidWires.mono (sSumSq.1.trans sDiv.1) sSyn.2.2.2.1
    · intro u hu
      simp only [tail1Wires, List.mem_ofFn] at hu
      rcases hu with ⟨j, rfl⟩
      dsimp only [rem1, nEnc] at *
      omega
    · intro u hu
      simp only [tail2Wires, List.mem_ofFn] at hu
      rcases hu with ⟨j, rfl⟩
      dsimp only [rem2, nEnc] at *
      omega
  have hwF_end : wF < nEnc + encCB.size := lt_of_lt_of_le hwF_v (Nat.add_le_add_left hext04.size_le nEnc)
  let tw : Fin c → Fin (nEnc + encCB.toCircuit.size) := fun j =>
    ⟨tagWires.getD j.val wF, by
      by_cases hlt : j.val < tagWires.length
      · rw [List.getD_eq_getElem _ _ hlt]
        exact htagW_v _ (List.getElem_mem hlt)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact hwF_end⟩
  let cw : Fin h → Fin (nEnc + encCB.toCircuit.size) := fun j =>
    ⟨flagWires.getD j.val wF, by
      have hlt : j.val < flagWires.length := by rw [hflagW_len]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      exact hflagW_v _ (List.getElem_mem hlt)⟩
  have henc_size : encCB.size ≤ (k + 1) ^ 6 := by
    have h0 : c0.size = 3 := by
      have h := sC.2.1
      simpa [c0, rC, CB.empty, CB.size] using h
    have h1 : rSums.1.size = c0.size + 11 * b * m := by
      have h := sSums.2.1
      simpa [rSums, pairsWires] using h
    have h2 : rSyn.1.size ≤ rSums.1.size + 4 * (m * b) * s := by
      have h := sSyn.2.1
      simp only [xCoreWires, Hrows, List.length_ofFn] at h
      exact h
    have h3 : rSumSq.1.size = rSyn.1.size + (28 * b + 12 * W * b) * m := by
      have h := sSumSq.2.1
      simpa [rSumSq, pairsWires] using h
    have h4 : encCB.size = rSumSq.1.size + 16 * (W + 1) * W :=
      calc
        encCB.size = rSumSq.1.size + 16 * (W + 1) * rSumSq.2.reverse.length := sDiv.2.1
        _ = rSumSq.1.size + 16 * (W + 1) * W := by rw [List.length_reverse, sSumSq.2.2.1]
    dsimp only [s, W] at h2 h3 h4
    omega
  have henc_eval : ∀ w : Word,
      (∀ j, (encCB.toCircuit.wires (raw w)).getD (tw j).val false = tag w j) ∧
      ∀ j, (encCB.toCircuit.wires (raw w)).getD (cw j).val false = flag w j := by
    intro w
    have hraw_len : (raw w).length = nEnc := by simp [raw, nEnc]
    have hraw_x : ∀ i : ℕ, i < k → (raw w).getD i false = (List.ofFn w.1).getD i false := by
      intro i hi
      have h1 : i < (raw w).length := by simp [raw]; omega
      have h2 : i < (List.ofFn w.1).length := by simp [hi]
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getElem_append_left h2]
    have hraw_z : ∀ i : ℕ, i < k - h → (raw w).getD (k + i) false = (List.ofFn w.2).getD i false := by
      intro i hi
      have h1 : k + i < (raw w).length := by simp [raw]; omega
      have h2 : i < (List.ofFn w.2).length := by simp [hi]
      have hlen1 : (List.ofFn w.1).length = k := by simp
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2,
        List.getElem_append_right (by omega)]
      simp [hlen1]
    have hwf0 : c0.eval (raw w) wF = false := (sC.2.2.2.2 (raw w) hraw_len).1
    have hwt0 : c0.eval (raw w) wT = true := (sC.2.2.2.2 (raw w) hraw_len).2
    have hxdig : ∀ i : Fin m, bitsVal ((xDigWires i).map (c0.eval (raw w))) = digit (List.ofFn w.1) i := by
      intro i
      dsimp only [xDigWires, digit]
      rw [List.map_ofFn, bitsVal_ofFn_eq_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hlt : i.val * b + j.val < k := by
        have : i.val * b + j.val < m * b := by nlinarith [i.isLt, j.isLt]
        omega
      rw [Function.comp_apply, c0.eval_input hraw_len (by dsimp only [nEnc]; omega), hraw_x _ hlt]
    have hzdig : ∀ i : Fin m, bitsVal ((zDigWires i).map (c0.eval (raw w))) = digit (List.ofFn w.2) i := by
      intro i
      dsimp only [zDigWires, digit]
      rw [List.map_ofFn, bitsVal_ofFn_eq_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hlt : i.val * b + j.val < k - h := by
        have : i.val * b + j.val < m * b := by nlinarith [i.isLt, j.isLt]
        omega
      rw [Function.comp_apply, c0.eval_input hraw_len (by dsimp only [nEnc]; omega)]
      have hidx : k + i.val * b + j.val = k + (i.val * b + j.val) := by omega
      rw [hidx, hraw_z _ hlt]
    have hD_lt_mQ2 : (∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2) <
        m * Q ^ 2 := by
      have heach : ∀ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2 < Q ^ 2 := by
        intro j
        have h1 : digit (List.ofFn w.1) j < Q := by
          rw [← hxdig j]
          have := bitsVal_lt ((xDigWires j).map (c0.eval (raw w)))
          simpa [xDigWires, Q] using this
        have h2 : digit (List.ofFn w.2) j < Q := by
          rw [← hzdig j]
          have := bitsVal_lt ((zDigWires j).map (c0.eval (raw w)))
          simpa [zDigWires, Q] using this
        have hd : Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j) < Q := by
          dsimp only [Nat.dist]; omega
        exact Nat.pow_lt_pow_left hd (by decide)
      calc
        (∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2)
            < ∑ _j : Fin m, Q ^ 2 :=
          Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun j _ => heach j)
        _ = m * Q ^ 2 := by simp
    have hSumSq_val : bitsVal (rSumSq.2.map (rSumSq.1.eval (raw w))) =
        ∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2 := by
      have hwf2 : rSyn.1.eval (raw w) wF = false := by rw [hext02.eval_eq hraw_len hwF_v, hwf0]
      have hwt2 : rSyn.1.eval (raw w) wT = true := by rw [hext02.eval_eq hraw_len hwT_v, hwt0]
      have hacc0 : bitsVal (zeroAcc.map (rSyn.1.eval (raw w))) = 0 := by
        simp [zeroAcc, hwf2, bitsVal_replicate_false]
      have hmap_eq : (pairsWires.map (fun p =>
          (Nat.dist (bitsVal (p.1.map (rSyn.1.eval (raw w))))
            (bitsVal (p.2.map (rSyn.1.eval (raw w))))) ^ 2)).sum =
          ∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2 := by
        dsimp only [pairsWires]
        rw [List.map_ofFn, List.sum_ofFn]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hp := hpairs_valid (xDigWires i, zDigWires i) (by simp only [pairsWires, List.mem_ofFn]; exact ⟨i, rfl⟩)
        rw [Function.comp_apply, ValidWires.map_eval_eq hext02 hp.2.2.1 hraw_len,
          ValidWires.map_eval_eq hext02 hp.2.2.2 hraw_len, hxdig i, hzdig i]
      have hbd : bitsVal (zeroAcc.map (rSyn.1.eval (raw w))) +
          (pairsWires.map (fun p => (Nat.dist (bitsVal (p.1.map (rSyn.1.eval (raw w))))
            (bitsVal (p.2.map (rSyn.1.eval (raw w))))) ^ 2)).sum < 2 ^ W := by
        rw [hacc0, zero_add, hmap_eq]
        exact lt_trans hD_lt_mQ2 hwb.2.2
      rw [sSumSq.2.2.2.2 (raw w) hraw_len hwf2 hwt2 hbd, hacc0, zero_add, hmap_eq]
    have hDiv_val : bitsVal (rDiv.2.1.map (encCB.eval (raw w))) =
        (∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2) / width := by
      have hwf3 : rSumSq.1.eval (raw w) wF = false := by rw [hext03.eval_eq hraw_len hwF_v, hwf0]
      have hwt3 : rSumSq.1.eval (raw w) wT = true := by rw [hext03.eval_eq hraw_len hwT_v, hwt0]
      have hacc0 : bitsVal (zeroAcc.map (rSumSq.1.eval (raw w))) = 0 := by
        simp [zeroAcc, hwf3, bitsVal_replicate_false]
      have hdiv := sDiv.2.2.2.2.2.2 (raw w) hraw_len hwf3 hwt3 (by rw [hacc0]; exact hwidth_pos)
      rw [hacc0, zero_mul, zero_add, List.map_reverse, msbVal_reverse, hSumSq_val] at hdiv
      have hq := congrArg (· / width) hdiv.1
      rw [mul_comm, Nat.mul_add_div hwidth_pos, Nat.div_eq_of_lt hdiv.2, add_zero] at hq
      exact hq.symm
    have hflag_map : flagWires.map (encCB.eval (raw w)) = List.ofFn (flag w) := by
      apply List.ext_getElem
      · simp [hflagW_len]
      · intro j hj1 hj2
        simp only [List.length_ofFn] at hj2
        have hlt_q : j < rDiv.2.1.length := by
          have h1 : rDiv.2.1.length = rSumSq.2.reverse.length := sDiv.2.2.1
          have h2 : rSumSq.2.length = W := sSumSq.2.2.1
          rw [h1, List.length_reverse, h2]
          dsimp only [W]
          omega
        simp only [flagWires, List.getElem_map, List.getElem_take, List.getElem_ofFn]
        have hget : encCB.eval (raw w) rDiv.2.1[j] = (rDiv.2.1.map (encCB.eval (raw w))).getD j false := by
          have hj' : j < (rDiv.2.1.map (encCB.eval (raw w))).length := by simp [hlt_q]
          rw [List.getD_eq_getElem _ _ hj', List.getElem_map]
        rw [hget, ← bitsVal_testBit, hDiv_val]
    have htag_map : tagWires.map (encCB.eval (raw w)) = tagList w := by
      dsimp only [tagWires, tagList]
      simp only [List.map_append, hflag_map]
      congr 1
      · congr 1
        · congr 1
          · congr 1
            · rw [ValidWires.map_eval_eq (sSyn.1.trans (sSumSq.1.trans sDiv.1)) sSums.2.2.2.1 hraw_len,
                sSums.2.2.2.2 (raw w) hraw_len hwf0]
              dsimp only [pairsWires]
              rw [list_flatMap_eq, List.map_ofFn]
              congr 1
              congr 1
              ext i
              simp only [Function.comp_apply, hxdig i, hzdig i]
          · rw [ValidWires.map_eval_eq (sSumSq.1.trans sDiv.1) sSyn.2.2.2.1 hraw_len,
              sSyn.2.2.2.2 (raw w) hraw_len (by rw [sSums.1.eval_eq hraw_len hwF_v, hwf0])]
            dsimp only [Hrows]
            rw [List.map_ofFn]
            congr 1
            ext r
            simp only [Function.comp_apply]
            have hxcore : xCoreWires.map (rSums.1.eval (raw w)) =
                List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩) := by
              dsimp only [xCoreWires]
              rw [List.map_ofFn]
              congr 1
              ext idx
              rw [Function.comp_apply, rSums.1.eval_input hraw_len (by dsimp only [nEnc]; omega),
                hraw_x idx.val (by omega)]
              have hlt : idx.val < (List.ofFn w.1).length := by simp; omega
              rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
            rw [hxcore]
        · dsimp only [tail1Wires]
          rw [List.map_ofFn]
          congr 1
          ext j
          rw [Function.comp_apply, encCB.eval_input hraw_len (by dsimp only [rem1, nEnc] at *; omega),
            hraw_x _ (by dsimp only [rem1] at *; omega)]
          have hlt : m * b + j.val < (List.ofFn w.1).length := by simp; dsimp only [rem1] at *; omega
          rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
      · dsimp only [tail2Wires]
        rw [List.map_ofFn]
        congr 1
        ext j
        rw [Function.comp_apply, encCB.eval_input hraw_len (by dsimp only [rem2, nEnc] at *; omega)]
        have hidx : k + m * b + j.val = k + (m * b + j.val) := by omega
        rw [hidx, hraw_z _ (by dsimp only [rem2] at *; omega)]
        have hlt : m * b + j.val < (List.ofFn w.2).length := by simp; dsimp only [rem2] at *; omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
    constructor
    · intro j
      change encCB.eval (raw w) (tw j).val = tag w j
      dsimp only [tw, tag]
      by_cases hlt : j.val < tagWires.length
      · rw [List.getD_eq_getElem _ _ hlt]
        have h1 : encCB.eval (raw w) tagWires[j.val] =
            (tagWires.map (encCB.eval (raw w)))[j.val]'(by simp [hlt]) :=
          (List.getElem_map _).symm
        have hj1 : j.val < (tagWires.map (encCB.eval (raw w))).length := by simp [hlt]
        rw [h1, ← List.getD_eq_getElem _ _ hj1, htag_map]
      · have hge2 : (tagList w).length ≤ j.val := by
          rw [← htag_map, List.length_map]; omega
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ hge2,
          hext04.eval_eq hraw_len hwF_v, hwf0]
    · intro j
      change encCB.eval (raw w) (cw j).val = flag w j
      dsimp only [cw]
      have hlt : j.val < flagWires.length := by rw [hflagW_len]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      have h1 : encCB.eval (raw w) flagWires[j.val] = (flagWires.map (encCB.eval (raw w)))[j.val]'(by simp [hlt]) := by
        rw [List.getElem_map]
      rw [h1]
      have h2 : (flagWires.map (encCB.eval (raw w))).getD j.val false = (List.ofFn (flag w)).getD j.val false := by
        rw [hflag_map]
      have hj1 : j.val < (flagWires.map (encCB.eval (raw w))).length := by simp [hlt]
      have hj2 : j.val < (List.ofFn (flag w)).length := by simp
      rw [← List.getD_eq_getElem _ _ hj1, h2, List.getD_eq_getElem _ _ hj2, List.getElem_ofFn]
  have htag_slices : ∀ w : Word,
      (∀ i : Fin h, tag w ⟨i.val, by dsimp only [c]; omega⟩ = flag w i) ∧
      (∀ (i : Fin m) (j : Fin (b + 1)),
        tag w ⟨h + i.val * (b + 1) + j.val, by
          have : i.val * (b + 1) + j.val < m * (b + 1) := by nlinarith [i.isLt, j.isLt]
          dsimp only [c, s, rem1, rem2] at hbud ⊢; omega⟩ =
        (digit (List.ofFn w.1) i + digit (List.ofFn w.2) i).testBit j.val) ∧
      (∀ r : Fin s,
        tag w ⟨h + m * (b + 1) + r.val, by dsimp only [c, s, rem1, rem2] at hbud ⊢; omega⟩ =
        listXor (List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩)) (List.ofFn (H r))) ∧
      (∀ j : Fin rem1,
        tag w ⟨h + m * (b + 1) + s + j.val, by dsimp only [c, s, rem1, rem2] at hbud ⊢; omega⟩ =
        w.1 ⟨m * b + j.val, by dsimp only [rem1] at *; omega⟩) ∧
      (∀ j : Fin rem2,
        tag w ⟨h + m * (b + 1) + s + rem1 + j.val, by dsimp only [c, s, rem1, rem2] at hbud ⊢; omega⟩ =
        w.2 ⟨m * b + j.val, by dsimp only [rem2] at *; omega⟩) := by
    intro w
    let L0 := List.ofFn (flag w)
    let L1 := (List.ofFn (fun i : Fin m =>
      List.ofFn (fun j : Fin (b + 1) =>
        (digit (List.ofFn w.1) i + digit (List.ofFn w.2) i).testBit j.val))).flatten
    let L2 := List.ofFn (fun r : Fin s =>
      listXor (List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩)) (List.ofFn (H r)))
    let L3 := List.ofFn (fun j : Fin rem1 => w.1 ⟨m * b + j.val, by dsimp only [rem1]; omega⟩)
    let L4 := List.ofFn (fun j : Fin rem2 => w.2 ⟨m * b + j.val, by dsimp only [rem2]; omega⟩)
    have hL0 : L0.length = h := by simp [L0]
    have hL1 : L1.length = m * (b + 1) := by
      dsimp only [L1]
      rw [List.length_flatten, List.map_ofFn]
      simp [List.sum_ofFn]
    have hL2 : L2.length = s := by simp [L2, s]
    have hL3 : L3.length = rem1 := by simp [L3]
    have hL4 : L4.length = rem2 := by simp [L4]
    have hL1_elem : ∀ (i : Fin m) (j : Fin (b + 1)),
        L1.getD (i.val * (b + 1) + j.val) false =
        (digit (List.ofFn w.1) i + digit (List.ofFn w.2) i).testBit j.val :=
      fun i j => flatten_ofFn_getD m (b + 1) _ i j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      change (L0 ++ L1 ++ L2 ++ L3 ++ L4).getD i.val false = flag w i
      rw [getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2, hL3]; omega),
          getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2]; omega),
          getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1]; omega),
          getD_append_bool, if_pos (by rw [hL0]; exact i.isLt)]
      have hlt : i.val < L0.length := by rw [hL0]; exact i.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      dsimp only [L0]
      rw [List.getElem_ofFn]
    · intro i j
      have hlt1 : i.val * (b + 1) + j.val < m * (b + 1) := by nlinarith [i.isLt, j.isLt]
      change (L0 ++ L1 ++ L2 ++ L3 ++ L4).getD (h + i.val * (b + 1) + j.val) false = _
      rw [getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2, hL3]; omega),
          getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2]; omega),
          getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1]; omega),
          getD_append_bool, if_neg (by rw [hL0]; omega)]
      have hsub : h + i.val * (b + 1) + j.val - L0.length = i.val * (b + 1) + j.val := by rw [hL0]; omega
      rw [hsub]
      exact hL1_elem i j
    · intro r
      change (L0 ++ L1 ++ L2 ++ L3 ++ L4).getD (h + m * (b + 1) + r.val) false = _
      rw [getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2, hL3]; omega),
          getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2]; omega),
          getD_append_bool, if_neg (by rw [List.length_append, hL0, hL1]; omega)]
      have hsub : h + m * (b + 1) + r.val - (L0 ++ L1).length = r.val := by
        rw [List.length_append, hL0, hL1]; omega
      rw [hsub]
      have hlt : r.val < L2.length := by rw [hL2]; exact r.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      dsimp only [L2]
      rw [List.getElem_ofFn]
    · intro j
      change (L0 ++ L1 ++ L2 ++ L3 ++ L4).getD (h + m * (b + 1) + s + j.val) false = _
      rw [getD_append_bool, if_pos (by simp only [List.length_append, hL0, hL1, hL2, hL3]; omega),
          getD_append_bool, if_neg (by simp only [List.length_append, hL0, hL1, hL2]; omega)]
      have hsub : h + m * (b + 1) + s + j.val - (L0 ++ L1 ++ L2).length = j.val := by
        simp only [List.length_append, hL0, hL1, hL2]; omega
      rw [hsub]
      have hlt : j.val < L3.length := by rw [hL3]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      dsimp only [L3]
      rw [List.getElem_ofFn]
    · intro j
      change (L0 ++ L1 ++ L2 ++ L3 ++ L4).getD (h + m * (b + 1) + s + rem1 + j.val) false = _
      rw [getD_append_bool, if_neg (by simp only [List.length_append, hL0, hL1, hL2, hL3]; omega)]
      have hsub : h + m * (b + 1) + s + rem1 + j.val - (L0 ++ L1 ++ L2 ++ L3).length = j.val := by
        simp only [List.length_append, hL0, hL1, hL2, hL3]; omega
      rw [hsub]
      have hlt : j.val < L4.length := by rw [hL4]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      dsimp only [L4]
      rw [List.getElem_ofFn]
  refine ⟨tag, encCB.toCircuit, tw, cw, encCB.valid henc_size, henc_eval, ?_, ?_⟩
  · intro a bW t hab hbt hfl htg
    have hfl_ta : flag t = flag a := by
      ext i
      have h1 := (htag_slices t).1 i
      have h2 := (htag_slices a).1 i
      rw [htg] at h1
      rw [← h1, h2]
    have hfl_ba : flag bW = flag a := hfl.trans hfl_ta
    have hD_lt : ∀ w : Word,
        (∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2) / width < 2 ^ h := by
      intro w
      have heach : ∀ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2 < Q ^ 2 := by
        intro j
        have h1 : digit (List.ofFn w.1) j < Q := by
          dsimp only [digit, Q]
          rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.1).getD (j.val * b + u.val) false)]
          simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.1).getD (j.val * b + u.val) false))
        have h2 : digit (List.ofFn w.2) j < Q := by
          dsimp only [digit, Q]
          rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.2).getD (j.val * b + u.val) false)]
          simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.2).getD (j.val * b + u.val) false))
        exact Nat.pow_lt_pow_left (by dsimp only [Nat.dist]; omega) (by decide)
      have hDlt : (∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2) < m * Q ^ 2 :=
        calc
          (∑ j : Fin m, (Nat.dist (digit (List.ofFn w.1) j) (digit (List.ofFn w.2) j)) ^ 2)
              < ∑ _j : Fin m, Q ^ 2 :=
            Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun j _ => heach j)
          _ = m * Q ^ 2 := by simp
      have hwm : m * Q ^ 2 < width * 2 ^ h := by
        have h1 := Nat.div_add_mod (m * Q ^ 2) (2 ^ h)
        have h2 := Nat.mod_lt (m * Q ^ 2) (by positivity : 0 < 2 ^ h)
        dsimp only [width]
        nlinarith
      exact Nat.div_lt_of_lt_mul (lt_trans hDlt hwm)
    have hbucket_eq : ∀ w1 w2 : Word, flag w1 = flag w2 →
        (∑ j : Fin m, (Nat.dist (digit (List.ofFn w1.1) j) (digit (List.ofFn w1.2) j)) ^ 2) / width =
        (∑ j : Fin m, (Nat.dist (digit (List.ofFn w2.1) j) (digit (List.ofFn w2.2) j)) ^ 2) / width := by
      intro w1 w2 hf
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < h
      · exact congrFun hf ⟨i, hi⟩
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hD_lt w1) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hD_lt w2) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]
    have hsum_eq : ∀ i : Fin m,
        digit (List.ofFn a.1) i + digit (List.ofFn a.2) i =
        digit (List.ofFn t.1) i + digit (List.ofFn t.2) i := by
      intro i
      have hlt : ∀ w : Word, digit (List.ofFn w.1) i + digit (List.ofFn w.2) i < 2 ^ (b + 1) := by
        intro w
        have h1 : digit (List.ofFn w.1) i < 2 ^ b := by
          dsimp only [digit]
          rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false)]
          simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false))
        have h2 : digit (List.ofFn w.2) i < 2 ^ b := by
          dsimp only [digit]
          rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false)]
          simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false))
        rw [pow_succ]; omega
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < b + 1
      · have h1 := (htag_slices t).2.1 i ⟨j, hj⟩
        have h2 := (htag_slices a).2.1 i ⟨j, hj⟩
        rw [htg] at h1
        rw [← h2, h1]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt a) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt t) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]
    have hb1 := hbucket_eq a bW hfl_ba.symm
    have hb2 := hbucket_eq t bW hfl.symm
    rw [← hab, hbt] at hb1 hb2
    have hcard_diff := nat_dist_sq_sum_bound
      (digit (List.ofFn a.1)) (digit (List.ofFn a.2))
      (digit (List.ofFn t.1)) (digit (List.ofFn t.2))
      hsum_eq hwidth_pos hb1 hb2
    let e : Fin (m * b) → Bool := fun idx =>
      xor (a.1 ⟨idx.val, by omega⟩) (t.1 ⟨idx.val, by omega⟩)
    have he_blocks : (Finset.univ.filter (fun i : Fin m =>
        ∃ j : Fin b, e ⟨i.val * b + j.val, by nlinarith [i.isLt, j.isLt]⟩ = true)).card ≤ width - 1 := by
      refine (Finset.card_le_card ?_).trans hcard_diff
      intro i hi
      rcases (Finset.mem_filter.mp hi).2 with ⟨j, hj⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      intro hdig_eq
      have htb : (digit (List.ofFn a.1) i).testBit j.val = (digit (List.ofFn t.1) i).testBit j.val := by
        rw [hdig_eq]
      have hd_tb : ∀ (v : Fin k → Bool), (digit (List.ofFn v) i).testBit j.val =
          v ⟨i.val * b + j.val, by have hmb : i.val * b + j.val < m * b := (by nlinarith [i.isLt, j.isLt]); omega⟩ := by
        intro v
        dsimp only [digit]
        rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn v).getD (i.val * b + u.val) false),
          bitsVal_testBit]
        have hlt1 : j.val < (List.ofFn (fun u : Fin b => (List.ofFn v).getD (i.val * b + u.val) false)).length := by
          rw [List.length_ofFn]; exact j.isLt
        rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn]
        have hlt2 : i.val * b + j.val < (List.ofFn v).length := by
          rw [List.length_ofFn]
          have hmb : i.val * b + j.val < m * b := (by nlinarith [i.isLt, j.isLt])
          omega
        rw [List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
      rw [hd_tb a.1, hd_tb t.1] at htb
      dsimp only [e] at hj
      rw [htb, Bool.xor_self] at hj
      exact Bool.noConfusion hj
    have he_syn : ∀ r : Fin s, listXor (List.ofFn e) (List.ofFn (H r)) = false := by
      intro r
      have h1 := (htag_slices t).2.2.1 r
      have h2 := (htag_slices a).2.2.1 r
      rw [htg] at h1
      have heq : listXor (List.ofFn (fun idx : Fin (m * b) => a.1 ⟨idx.val, by omega⟩)) (List.ofFn (H r)) =
          listXor (List.ofFn (fun idx : Fin (m * b) => t.1 ⟨idx.val, by omega⟩)) (List.ofFn (H r)) := by
        rw [← h2, h1]
      rw [listXor_ofFn, listXor_ofFn] at heq
      rw [listXor_ofFn]
      have hsum_e : (∑ idx : Fin (m * b), if e idx && H r idx then (1 : ZMod 2) else 0) =
          (∑ idx : Fin (m * b), if a.1 ⟨idx.val, by omega⟩ && H r idx then (1 : ZMod 2) else 0) +
          (∑ idx : Fin (m * b), if t.1 ⟨idx.val, by omega⟩ && H r idx then (1 : ZMod 2) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun idx _ => xor_and_zmod2 _ _ _)
      rw [hsum_e]
      generalize (∑ idx : Fin (m * b), if a.1 ⟨idx.val, by omega⟩ && H r idx then (1 : ZMod 2) else 0) = va at heq ⊢
      generalize (∑ idx : Fin (m * b), if t.1 ⟨idx.val, by omega⟩ && H r idx then (1 : ZMod 2) else 0) = vt at heq ⊢
      revert va vt heq
      decide
    have he0 : e = (fun _ => false) := by
      by_contra hne
      rcases hH e hne he_blocks with ⟨r, hr⟩
      rw [he_syn r] at hr
      exact Bool.noConfusion hr
    have ha1_t1 : a.1 = t.1 := by
      ext idx
      by_cases hlt : idx.val < m * b
      · have h0 := congrFun he0 ⟨idx.val, hlt⟩
        dsimp only [e] at h0
        cases h1 : a.1 idx <;> cases h2 : t.1 idx <;> simp_all
      · have hj : idx.val - m * b < rem1 := by dsimp only [rem1]; omega
        have h1 := (htag_slices t).2.2.2.1 ⟨idx.val - m * b, hj⟩
        have h2 := (htag_slices a).2.2.2.1 ⟨idx.val - m * b, hj⟩
        rw [htg] at h1
        have hidx : (⟨m * b + (idx.val - m * b), by dsimp only [rem1] at *; omega⟩ : Fin k) = idx := by
          ext; dsimp; omega
        rw [hidx] at h1 h2
        rw [← h2, h1]
    have ha2_t2 : a.2 = t.2 := by
      ext idx
      by_cases hlt : idx.val < m * b
      · let i0 : Fin m := ⟨idx.val / b, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt)⟩
        let j0 : Fin b := ⟨idx.val % b, Nat.mod_lt _ (by omega)⟩
        have hdig_z : digit (List.ofFn a.2) i0 = digit (List.ofFn t.2) i0 := by
          have hs := hsum_eq i0
          rw [ha1_t1] at hs
          omega
        have htb : (digit (List.ofFn a.2) i0).testBit j0.val = (digit (List.ofFn t.2) i0).testBit j0.val := by
          rw [hdig_z]
        have hd_tb : ∀ (v : Fin (k - h) → Bool), (digit (List.ofFn v) i0).testBit j0.val = v idx := by
          intro v
          dsimp only [digit]
          rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn v).getD (i0.val * b + u.val) false),
            bitsVal_testBit]
          have hlt1 : j0.val < (List.ofFn (fun u : Fin b => (List.ofFn v).getD (i0.val * b + u.val) false)).length := by
            simp
          rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn]
          have heq_idx : i0.val * b + j0.val = idx.val := by
            dsimp only [i0, j0]
            linarith [Nat.div_add_mod idx.val b]
          have hlt2 : idx.val < (List.ofFn v).length := by simp
          rw [heq_idx, List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
        rw [hd_tb a.2, hd_tb t.2] at htb
        exact htb
      · have hj : idx.val - m * b < rem2 := by dsimp only [rem2]; omega
        have h1 := (htag_slices t).2.2.2.2 ⟨idx.val - m * b, hj⟩
        have h2 := (htag_slices a).2.2.2.2 ⟨idx.val - m * b, hj⟩
        rw [htg] at h1
        have hidx : (⟨m * b + (idx.val - m * b), by dsimp only [rem2] at *; omega⟩ : Fin (k - h)) = idx := by
          ext; dsimp; omega
        rw [hidx] at h1 h2
        rw [← h2, h1]
    have hat : a = t := Prod.ext ha1_t1 ha2_t2
    have hbt' : bW = t := Prod.ext (hab.symm.trans ha1_t1) hbt
    exact ⟨hat.trans hbt'.symm, hbt'⟩
  · intro e port len inputs
    fin_cases e
    · have hin_eq : inputs = k + k := rfl
      let decCB : CB inputs := CB.empty inputs
      let dw : Fin (k + (k - h)) → Fin (inputs + decCB.toCircuit.size) := fun j =>
        ⟨j.val, by dsimp only [decCB, CB.toCircuit, Circuit.size, CB.empty]; omega⟩
      refine ⟨decCB.toCircuit, dw, decCB.valid (by simp [decCB, CB.size, CB.empty]), ?_⟩
      intro w j
      have hplen : (port 0 w ++ port 1 w).length = inputs := by
        simp [port, inputs, len]; omega
      change decCB.eval (port 0 w ++ port 1 w) j.val = (raw w).getD j.val false
      rw [decCB.eval_input hplen (by omega)]
      dsimp only [port, raw]
      simp only [↓reduceIte, Fin.isValue, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
      have hassoc : List.ofFn w.1 ++ (List.ofFn w.2 ++ List.ofFn (flag w)) =
          (List.ofFn w.1 ++ List.ofFn w.2) ++ List.ofFn (flag w) := by
        rw [List.append_assoc]
      rw [hassoc]
      have hlt : j.val < (List.ofFn w.1 ++ List.ofFn w.2).length := by simp
      have hlt2 : j.val < ((List.ofFn w.1 ++ List.ofFn w.2) ++ List.ofFn (flag w)).length := by
        simp; omega
      rw [List.getD_eq_getElem _ _ hlt2, List.getD_eq_getElem _ _ hlt, List.getElem_append_left hlt]
    · have hin_eq : inputs = k + c := rfl
      have hin_pos : 0 < inputs := by omega
      let rC1 := mkConsts (CB.empty inputs) hin_pos
      have sC1 := mkConsts_spec (CB.empty inputs) hin_pos
      let c1 := rC1.1
      let f1 := rC1.2.1
      let t1 := rC1.2.2
      let subPairs1 : List (List ℕ × List ℕ) := List.ofFn (fun i : Fin m =>
        (List.ofFn (fun j : Fin (b + 1) => k + h + i.val * (b + 1) + j.val),
         List.ofFn (fun j : Fin b => i.val * b + j.val)))
      have hsp1_v : ∀ p ∈ subPairs1,
          p.1.length = b + 1 ∧ p.2.length = b ∧ ValidWires c1 p.1 ∧ ValidWires c1 p.2 := by
        intro p hp
        simp only [subPairs1, List.mem_ofFn] at hp
        rcases hp with ⟨i, rfl⟩
        refine ⟨by simp, by simp, ?_, ?_⟩
        · intro u hu
          simp only [List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          have hlt : i.val * (b + 1) + j.val < m * (b + 1) := mul_add_lt_mul i j
          omega
        · intro u hu
          simp only [List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          have hlt : i.val * b + j.val < m * b := mul_add_lt_mul i j
          omega
      let rSub1 := mkSubDigits c1 f1 t1 sC1.2.2.1 sC1.2.2.2.1 b subPairs1 hsp1_v
      have sSub1 := mkSubDigits_spec b subPairs1 c1 f1 t1 sC1.2.2.1 sC1.2.2.2.1 hsp1_v
      let dec1 := rSub1.1
      let xTail1 : List ℕ := List.ofFn (fun j : Fin rem1 => k + h + m * (b + 1) + s + j.val)
      let zAll1 : List ℕ := List.ofFn (fun j : Fin (k - h) => j.val)
      let outWires1 : List ℕ := rSub1.2 ++ xTail1 ++ zAll1
      have hout1_len : outWires1.length = k + (k - h) := by
        have hsub_len : rSub1.2.length = m * b := by
          have hlen := sSub1.2.2.1
          simpa [rSub1, subPairs1] using hlen
        dsimp only [outWires1, xTail1, zAll1, rem1]
        rw [List.length_append, List.length_append, hsub_len, List.length_ofFn, List.length_ofFn]
        omega
      have hout1_v : ValidWires dec1 outWires1 := by
        refine ValidWires.append (ValidWires.append sSub1.2.2.2.1 ?_) ?_
        · intro u hu
          simp only [xTail1, List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          dsimp only [s, rem1]
          omega
        · intro u hu
          simp only [zAll1, List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          omega
      have hsz1 : dec1.size ≤ (k + 1) ^ 6 := by
        have h0 : c1.size = 3 := by
          have hsz := sC1.2.1
          simpa [c1, rC1, CB.empty, CB.size] using hsz
        have h1 : dec1.size = 3 + 12 * (b + 1) * m :=
          calc
            dec1.size = c1.size + 12 * (b + 1) * subPairs1.length := sSub1.2.1
            _ = 3 + 12 * (b + 1) * m := by rw [h0]; simp [subPairs1]
        rw [h1]
        exact dec_size_poly6 k h hh hk
      let dw1 : Fin (k + (k - h)) → Fin (inputs + dec1.toCircuit.size) := fun j =>
        ⟨outWires1[j.val]'(by rw [hout1_len]; exact j.isLt),
         hout1_v _ (List.getElem_mem (by rw [hout1_len]; exact j.isLt))⟩
      refine ⟨dec1.toCircuit, dw1, dec1.valid hsz1, ?_⟩
      intro w j
      let inp := (List.ofFn w.2 ++ List.ofFn (flag w)) ++ List.ofFn (tag w)
      have hinp_len : inp.length = inputs := by
        dsimp only [inp]
        simp only [List.length_append, List.length_ofFn]
        omega
      have hinp_z : ∀ idx : ℕ, idx < k - h → inp.getD idx false = (List.ofFn w.2).getD idx false := by
        intro idx hi
        dsimp only [inp]
        have h1 : idx < (List.ofFn w.2).length := by rw [List.length_ofFn]; exact hi
        have h2 : idx < (List.ofFn w.2 ++ List.ofFn (flag w)).length := by
          rw [List.length_append, List.length_ofFn, List.length_ofFn]; omega
        have h3 : idx < ((List.ofFn w.2 ++ List.ofFn (flag w)) ++ List.ofFn (tag w)).length := by
          rw [List.length_append, List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn]; omega
        rw [List.getD_eq_getElem _ _ h3, List.getD_eq_getElem _ _ h1,
          List.getElem_append_left h2, List.getElem_append_left h1]
      have hinp_tag : ∀ (idx : ℕ) (hi : idx < c), inp.getD (k + idx) false = tag w ⟨idx, hi⟩ := by
        intro idx hi
        dsimp only [inp]
        have hlen1 : (List.ofFn w.2 ++ List.ofFn (flag w)).length = k := by
          rw [List.length_append, List.length_ofFn, List.length_ofFn]; omega
        have h1 : k + idx < ((List.ofFn w.2 ++ List.ofFn (flag w)) ++ List.ofFn (tag w)).length := by
          rw [List.length_append, hlen1, List.length_ofFn]; omega
        rw [List.getD_eq_getElem _ _ h1, List.getElem_append_right (by omega)]
        have hsub : k + idx - (List.ofFn w.2 ++ List.ofFn (flag w)).length = idx := by omega
        simp only [hsub, List.getElem_ofFn]
      have hwf1 : c1.eval inp f1 = false := (sC1.2.2.2.2 inp hinp_len).1
      have hwt1 : c1.eval inp t1 = true := (sC1.2.2.2.2 inp hinp_len).2
      have hpair_eval : ∀ i : Fin m,
          bitsVal ((List.ofFn (fun u : Fin (b + 1) => k + h + i.val * (b + 1) + u.val)).map (c1.eval inp)) =
            digit (List.ofFn w.1) i + digit (List.ofFn w.2) i ∧
          bitsVal ((List.ofFn (fun u : Fin b => i.val * b + u.val)).map (c1.eval inp)) =
            digit (List.ofFn w.2) i := by
        intro i
        constructor
        · rw [List.map_ofFn]
          have hlt_sum : digit (List.ofFn w.1) i + digit (List.ofFn w.2) i < 2 ^ (b + 1) := by
            have h1 : digit (List.ofFn w.1) i < 2 ^ b := by
              dsimp only [digit]
              rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false)]
              simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false))
            have h2 : digit (List.ofFn w.2) i < 2 ^ b := by
              dsimp only [digit]
              rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false)]
              simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false))
            rw [pow_succ]; omega
          have heq_fn : ((c1.eval inp) ∘ (fun u : Fin (b + 1) => k + h + i.val * (b + 1) + u.val)) =
              fun u : Fin (b + 1) => (digit (List.ofFn w.1) i + digit (List.ofFn w.2) i).testBit u.val := by
            ext u
            have hlt : i.val * (b + 1) + u.val < m * (b + 1) := mul_add_lt_mul i u
            have hlt_c : h + i.val * (b + 1) + u.val < c := by omega
            rw [Function.comp_apply, c1.eval_input hinp_len (by omega)]
            have hidx : k + h + i.val * (b + 1) + u.val = k + (h + i.val * (b + 1) + u.val) := by omega
            rw [hidx, hinp_tag _ hlt_c]
            exact (htag_slices w).2.1 i u
          rw [heq_fn]
          exact bitsVal_ofFn_testBit (b + 1) _ hlt_sum
        · rw [List.map_ofFn, bitsVal_ofFn_eq_sum]
          dsimp only [digit]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          have hlt : i.val * b + u.val < k - h := lt_of_lt_of_le (mul_add_lt_mul i u) hmb_le
          rw [Function.comp_apply, c1.eval_input hinp_len (by omega), hinp_z _ hlt]
      have hout_eq : outWires1.map (dec1.eval inp) = raw w := by
        have hcond1 : ∀ p ∈ subPairs1,
            bitsVal (p.2.map (c1.eval inp)) ≤ bitsVal (p.1.map (c1.eval inp)) ∧
            bitsVal (p.1.map (c1.eval inp)) - bitsVal (p.2.map (c1.eval inp)) < 2 ^ b := by
          intro p hp
          simp only [subPairs1, List.mem_ofFn] at hp
          rcases hp with ⟨i, rfl⟩
          rw [(hpair_eval i).1, (hpair_eval i).2]
          have h1 : digit (List.ofFn w.1) i < 2 ^ b := by
            dsimp only [digit]
            rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false)]
            simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false))
          omega
        have hrsub_eq : rSub1.2.map (dec1.eval inp) = List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩) := by
          rw [sSub1.2.2.2.2 inp hinp_len hwf1 hwt1 hcond1]
          dsimp only [subPairs1]
          rw [list_flatMap_eq, List.map_ofFn]
          apply List.ext_getElem
          · simp only [List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn]
            simp
          · intro idx hi1 hi2
            rw [List.length_ofFn] at hi2
            let i0 : Fin m := ⟨idx / b, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi2)⟩
            let j0 : Fin b := ⟨idx % b, Nat.mod_lt _ (by omega)⟩
            have hidx_eq : i0.val * b + j0.val = idx := by
              dsimp only [i0, j0]; linarith [Nat.div_add_mod idx b]
            have hgd1 := (List.getD_eq_getElem _ false hi1).symm
            rw [hgd1]
            conv_lhs => rw [← hidx_eq]
            dsimp only [Function.comp_def]
            rw [flatten_ofFn_getD m b _ i0 j0]
            simp only [(hpair_eval i0).1, (hpair_eval i0).2, Nat.add_sub_cancel, List.getElem_ofFn]
            dsimp only [digit]
            rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.1).getD (i0.val * b + u.val) false),
              bitsVal_testBit]
            have hlt1 : j0.val < (List.ofFn (fun u : Fin b => (List.ofFn w.1).getD (i0.val * b + u.val) false)).length := by
              rw [List.length_ofFn]; exact j0.isLt
            have hlt2 : idx < (List.ofFn w.1).length := by rw [List.length_ofFn]; omega
            rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn, hidx_eq,
              List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
        have hxt_eq : xTail1.map (dec1.eval inp) =
            List.ofFn (fun u : Fin rem1 => w.1 ⟨m * b + u.val, by dsimp only [rem1]; omega⟩) := by
          dsimp only [xTail1]
          rw [List.map_ofFn]
          congr 1
          ext u
          have hlt_c : h + m * (b + 1) + s + u.val < c := by dsimp only [s, rem1]; omega
          rw [Function.comp_apply, dec1.eval_input hinp_len (by omega)]
          have hidx : k + h + m * (b + 1) + s + u.val = k + (h + m * (b + 1) + s + u.val) := by omega
          rw [hidx, hinp_tag _ hlt_c]
          exact (htag_slices w).2.2.2.1 u
        have hz_eq : zAll1.map (dec1.eval inp) = List.ofFn w.2 := by
          dsimp only [zAll1]
          rw [List.map_ofFn]
          congr 1
          ext u
          rw [Function.comp_apply, dec1.eval_input hinp_len (by omega), hinp_z u.val u.isLt]
          have hlt : u.val < (List.ofFn w.2).length := by rw [List.length_ofFn]; exact u.isLt
          rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        have hx_full : List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩) ++
            List.ofFn (fun u : Fin rem1 => w.1 ⟨m * b + u.val, by dsimp only [rem1]; omega⟩) = List.ofFn w.1 := by
          apply List.ext_getElem
          · simp [rem1]; omega
          · intro idx hi1 hi2
            by_cases hlt : idx < m * b
            · have h1 : idx < (List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩)).length := by simp [hlt]
              rw [List.getElem_append_left h1, List.getElem_ofFn, List.getElem_ofFn]
            · have h1 : (List.ofFn (fun idx : Fin (m * b) => w.1 ⟨idx.val, by omega⟩)).length ≤ idx := by simp; omega
              rw [List.getElem_append_right h1, List.getElem_ofFn, List.getElem_ofFn]
              apply congrArg w.1; ext; simp; omega
        dsimp only [outWires1, raw]
        rw [List.map_append, List.map_append, hrsub_eq, hxt_eq, hz_eq, hx_full]
      change dec1.eval inp (dw1 j).val = (raw w).getD j.val false
      dsimp only [dw1]
      have hjw : j.val < outWires1.length := by rw [hout1_len]; exact j.isLt
      have h1 : dec1.eval inp (outWires1[j.val]'hjw) =
          (outWires1.map (dec1.eval inp))[j.val]'(by rw [List.length_map]; exact hjw) :=
        (List.getElem_map _).symm
      rw [h1]
      have hj1 : j.val < (outWires1.map (dec1.eval inp)).length := by rw [List.length_map]; exact hjw
      rw [← List.getD_eq_getElem _ _ hj1, hout_eq]
    · have hin_eq : inputs = c + k := rfl
      have hin_pos : 0 < inputs := by omega
      let rC2 := mkConsts (CB.empty inputs) hin_pos
      have sC2 := mkConsts_spec (CB.empty inputs) hin_pos
      let c2 := rC2.1
      let f2 := rC2.2.1
      let t2 := rC2.2.2
      let subPairs2 : List (List ℕ × List ℕ) := List.ofFn (fun i : Fin m =>
        (List.ofFn (fun j : Fin (b + 1) => h + i.val * (b + 1) + j.val),
         List.ofFn (fun j : Fin b => c + i.val * b + j.val)))
      have hsp2_v : ∀ p ∈ subPairs2,
          p.1.length = b + 1 ∧ p.2.length = b ∧ ValidWires c2 p.1 ∧ ValidWires c2 p.2 := by
        intro p hp
        simp only [subPairs2, List.mem_ofFn] at hp
        rcases hp with ⟨i, rfl⟩
        refine ⟨by simp, by simp, ?_, ?_⟩
        · intro u hu
          simp only [List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          have hlt : i.val * (b + 1) + j.val < m * (b + 1) := mul_add_lt_mul i j
          omega
        · intro u hu
          simp only [List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          have hlt : i.val * b + j.val < m * b := mul_add_lt_mul i j
          omega
      let rSub2 := mkSubDigits c2 f2 t2 sC2.2.2.1 sC2.2.2.2.1 b subPairs2 hsp2_v
      have sSub2 := mkSubDigits_spec b subPairs2 c2 f2 t2 sC2.2.2.1 sC2.2.2.2.1 hsp2_v
      let dec2 := rSub2.1
      let xAll2 : List ℕ := List.ofFn (fun j : Fin k => c + j.val)
      let zTail2 : List ℕ := List.ofFn (fun j : Fin rem2 => h + m * (b + 1) + s + rem1 + j.val)
      let outWires2 : List ℕ := xAll2 ++ rSub2.2 ++ zTail2
      have hout2_len : outWires2.length = k + (k - h) := by
        have hsub_len : rSub2.2.length = m * b := by
          have hlen := sSub2.2.2.1
          simpa [rSub2, subPairs2] using hlen
        dsimp only [outWires2, xAll2, zTail2, rem2]
        rw [List.length_append, List.length_append, hsub_len, List.length_ofFn, List.length_ofFn]
        omega
      have hout2_v : ValidWires dec2 outWires2 := by
        refine ValidWires.append (ValidWires.append ?_ sSub2.2.2.2.1) ?_
        · intro u hu
          simp only [xAll2, List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          omega
        · intro u hu
          simp only [zTail2, List.mem_ofFn] at hu
          rcases hu with ⟨j, rfl⟩
          dsimp only [s, rem1, rem2]
          omega
      have hsz2 : dec2.size ≤ (k + 1) ^ 6 := by
        have h0 : c2.size = 3 := by
          have hsz := sC2.2.1
          simpa [c2, rC2, CB.empty, CB.size] using hsz
        have h1 : dec2.size = 3 + 12 * (b + 1) * m :=
          calc
            dec2.size = c2.size + 12 * (b + 1) * subPairs2.length := sSub2.2.1
            _ = 3 + 12 * (b + 1) * m := by rw [h0]; simp [subPairs2]
        rw [h1]
        exact dec_size_poly6 k h hh hk
      let dw2 : Fin (k + (k - h)) → Fin (inputs + dec2.toCircuit.size) := fun j =>
        ⟨outWires2[j.val]'(by rw [hout2_len]; exact j.isLt),
         hout2_v _ (List.getElem_mem (by rw [hout2_len]; exact j.isLt))⟩
      refine ⟨dec2.toCircuit, dw2, dec2.valid hsz2, ?_⟩
      intro w j
      let inp := List.ofFn (tag w) ++ List.ofFn w.1
      have hinp_len : inp.length = inputs := by
        dsimp only [inp]
        simp only [List.length_append, List.length_ofFn]
        omega
      have hinp_tag : ∀ (idx : ℕ) (hi : idx < c), inp.getD idx false = tag w ⟨idx, hi⟩ := by
        intro idx hi
        dsimp only [inp]
        have h1 : idx < (List.ofFn (tag w)).length := by rw [List.length_ofFn]; exact hi
        have h2 : idx < (List.ofFn (tag w) ++ List.ofFn w.1).length := by
          rw [List.length_append, List.length_ofFn, List.length_ofFn]; omega
        rw [List.getD_eq_getElem _ _ h2, List.getElem_append_left h1, List.getElem_ofFn]
      have hinp_x : ∀ idx : ℕ, idx < k → inp.getD (c + idx) false = (List.ofFn w.1).getD idx false := by
        intro idx hi
        dsimp only [inp]
        have hlen1 : (List.ofFn (tag w)).length = c := List.length_ofFn
        have h1 : c + idx < (List.ofFn (tag w) ++ List.ofFn w.1).length := by
          rw [List.length_append, hlen1, List.length_ofFn]; omega
        have h2 : idx < (List.ofFn w.1).length := by rw [List.length_ofFn]; exact hi
        rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getElem_append_right (by omega)]
        have hsub : c + idx - (List.ofFn (tag w)).length = idx := by omega
        simp only [hsub]
      have hwf2 : c2.eval inp f2 = false := (sC2.2.2.2.2 inp hinp_len).1
      have hwt2 : c2.eval inp t2 = true := (sC2.2.2.2.2 inp hinp_len).2
      have hpair_eval : ∀ i : Fin m,
          bitsVal ((List.ofFn (fun u : Fin (b + 1) => h + i.val * (b + 1) + u.val)).map (c2.eval inp)) =
            digit (List.ofFn w.1) i + digit (List.ofFn w.2) i ∧
          bitsVal ((List.ofFn (fun u : Fin b => c + i.val * b + u.val)).map (c2.eval inp)) =
            digit (List.ofFn w.1) i := by
        intro i
        constructor
        · rw [List.map_ofFn]
          have hlt_sum : digit (List.ofFn w.1) i + digit (List.ofFn w.2) i < 2 ^ (b + 1) := by
            have h1 : digit (List.ofFn w.1) i < 2 ^ b := by
              dsimp only [digit]
              rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false)]
              simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.1).getD (i.val * b + u.val) false))
            have h2 : digit (List.ofFn w.2) i < 2 ^ b := by
              dsimp only [digit]
              rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false)]
              simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false))
            rw [pow_succ]; omega
          have heq_fn : ((c2.eval inp) ∘ (fun u : Fin (b + 1) => h + i.val * (b + 1) + u.val)) =
              fun u : Fin (b + 1) => (digit (List.ofFn w.1) i + digit (List.ofFn w.2) i).testBit u.val := by
            ext u
            have hlt : i.val * (b + 1) + u.val < m * (b + 1) := mul_add_lt_mul i u
            have hlt_c : h + i.val * (b + 1) + u.val < c := by omega
            rw [Function.comp_apply, c2.eval_input hinp_len (by omega), hinp_tag _ hlt_c]
            exact (htag_slices w).2.1 i u
          rw [heq_fn]
          exact bitsVal_ofFn_testBit (b + 1) _ hlt_sum
        · rw [List.map_ofFn, bitsVal_ofFn_eq_sum]
          dsimp only [digit]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          have hlt : i.val * b + u.val < k := lt_of_lt_of_le (lt_of_lt_of_le (mul_add_lt_mul i u) hmb_le) (Nat.sub_le k h)
          rw [Function.comp_apply, c2.eval_input hinp_len (by omega)]
          have hidx : c + i.val * b + u.val = c + (i.val * b + u.val) := by omega
          rw [hidx, hinp_x _ hlt]
      have hout_eq : outWires2.map (dec2.eval inp) = raw w := by
        have hcond2 : ∀ p ∈ subPairs2,
            bitsVal (p.2.map (c2.eval inp)) ≤ bitsVal (p.1.map (c2.eval inp)) ∧
            bitsVal (p.1.map (c2.eval inp)) - bitsVal (p.2.map (c2.eval inp)) < 2 ^ b := by
          intro p hp
          simp only [subPairs2, List.mem_ofFn] at hp
          rcases hp with ⟨i, rfl⟩
          rw [(hpair_eval i).1, (hpair_eval i).2]
          have h2 : digit (List.ofFn w.2) i < 2 ^ b := by
            dsimp only [digit]
            rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false)]
            simpa using bitsVal_lt (List.ofFn (fun u : Fin b => (List.ofFn w.2).getD (i.val * b + u.val) false))
          omega
        have hrsub_eq : rSub2.2.map (dec2.eval inp) = List.ofFn (fun idx : Fin (m * b) => w.2 ⟨idx.val, by omega⟩) := by
          rw [sSub2.2.2.2.2 inp hinp_len hwf2 hwt2 hcond2]
          dsimp only [subPairs2]
          rw [list_flatMap_eq, List.map_ofFn]
          apply List.ext_getElem
          · simp only [List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn]
            simp
          · intro idx hi1 hi2
            rw [List.length_ofFn] at hi2
            let i0 : Fin m := ⟨idx / b, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi2)⟩
            let j0 : Fin b := ⟨idx % b, Nat.mod_lt _ (by omega)⟩
            have hidx_eq : i0.val * b + j0.val = idx := by
              dsimp only [i0, j0]; linarith [Nat.div_add_mod idx b]
            have hgd1 := (List.getD_eq_getElem _ false hi1).symm
            rw [hgd1]
            conv_lhs => rw [← hidx_eq]
            dsimp only [Function.comp_def]
            rw [flatten_ofFn_getD m b _ i0 j0]
            simp only [(hpair_eval i0).1, (hpair_eval i0).2, Nat.add_sub_cancel_left, List.getElem_ofFn]
            dsimp only [digit]
            rw [← bitsVal_ofFn_eq_sum (fun u : Fin b => (List.ofFn w.2).getD (i0.val * b + u.val) false),
              bitsVal_testBit]
            have hlt1 : j0.val < (List.ofFn (fun u : Fin b => (List.ofFn w.2).getD (i0.val * b + u.val) false)).length := by
              rw [List.length_ofFn]; exact j0.isLt
            have hlt2 : idx < (List.ofFn w.2).length := by rw [List.length_ofFn]; omega
            rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn, hidx_eq,
              List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
        have hzt_eq : zTail2.map (dec2.eval inp) =
            List.ofFn (fun u : Fin rem2 => w.2 ⟨m * b + u.val, by dsimp only [rem2]; omega⟩) := by
          dsimp only [zTail2]
          rw [List.map_ofFn]
          congr 1
          ext u
          have hlt_c : h + m * (b + 1) + s + rem1 + u.val < c := by dsimp only [s, rem1, rem2]; omega
          rw [Function.comp_apply, dec2.eval_input hinp_len (by omega), hinp_tag _ hlt_c]
          exact (htag_slices w).2.2.2.2 u
        have hx_eq : xAll2.map (dec2.eval inp) = List.ofFn w.1 := by
          dsimp only [xAll2]
          rw [List.map_ofFn]
          congr 1
          ext u
          rw [Function.comp_apply, dec2.eval_input hinp_len (by omega), hinp_x u.val u.isLt]
          have hlt : u.val < (List.ofFn w.1).length := by rw [List.length_ofFn]; exact u.isLt
          rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        have hz_full : List.ofFn (fun idx : Fin (m * b) => w.2 ⟨idx.val, by omega⟩) ++
            List.ofFn (fun u : Fin rem2 => w.2 ⟨m * b + u.val, by dsimp only [rem2]; omega⟩) = List.ofFn w.2 := by
          apply List.ext_getElem
          · simp [rem2]; omega
          · intro idx hi1 hi2
            by_cases hlt : idx < m * b
            · have h1 : idx < (List.ofFn (fun idx : Fin (m * b) => w.2 ⟨idx.val, by omega⟩)).length := by simp [hlt]
              rw [List.getElem_append_left h1, List.getElem_ofFn, List.getElem_ofFn]
            · have h1 : (List.ofFn (fun idx : Fin (m * b) => w.2 ⟨idx.val, by omega⟩)).length ≤ idx := by simp; omega
              rw [List.getElem_append_right h1, List.getElem_ofFn, List.getElem_ofFn]
              apply congrArg w.2; ext; simp; omega
        dsimp only [outWires2, raw]
        rw [List.map_append, List.map_append, hx_eq, hrsub_eq, hzt_eq, List.append_assoc, hz_full]
      change dec2.eval inp (dw2 j).val = (raw w).getD j.val false
      dsimp only [dw2]
      have hjw : j.val < outWires2.length := by rw [hout2_len]; exact j.isLt
      have h1 : dec2.eval inp (outWires2[j.val]'hjw) =
          (outWires2.map (dec2.eval inp))[j.val]'(by rw [List.length_map]; exact hjw) :=
        (List.getElem_map _).symm
      rw [h1]
      have hj1 : j.val < (outWires2.map (dec2.eval inp)).length := by rw [List.length_map]; exact hjw
      rw [← List.getD_eq_getElem _ _ hj1, hout_eq]
