import PEqualNP.Defs
import PEqualNP.Outside.L_clb_049

namespace PEqualNP.Outside.L_clb_050_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def bitsVal (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bitsVal f k + (f k).toNat * 2 ^ k

lemma bitsVal_lt (f : ℕ → Bool) : ∀ k, bitsVal f k < 2 ^ k
  | 0 => by simp [bitsVal]
  | k + 1 => by
    have ih := bitsVal_lt f k
    simp only [bitsVal]
    cases f k <;> simp [Nat.pow_succ] <;> omega

lemma bitsVal_congr (f g : ℕ → Bool) : ∀ k, (∀ j < k, f j = g j) → bitsVal f k = bitsVal g k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [bitsVal, bitsVal_congr f g k (fun j hj => h j (by omega)), h k (by omega)]

lemma bitsVal_testBit (f : ℕ → Bool) : ∀ k j, (bitsVal f k).testBit j = if j < k then f j else false
  | 0, j => by simp [bitsVal]
  | k + 1, j => by
    have ih := bitsVal_testBit f k j
    have hlt := bitsVal_lt f k
    simp only [bitsVal]
    cases hfk : f k
    · simp only [Bool.toNat_false, zero_mul, add_zero]
      rw [ih]
      by_cases hjk : j < k
      · have h1 : j < k + 1 := by omega
        simp [hjk, h1]
      · by_cases hje : j = k
        · subst hje; simp [hfk]
        · have h1 : ¬ (j < k + 1) := by omega
          simp [hjk, h1]
    · simp only [Bool.toNat_true, one_mul]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      by_cases hjk : j < k
      · have h1 : j < k + 1 := by omega
        have hdiv : (bitsVal f k + 2 ^ k) / 2 ^ j = bitsVal f k / 2 ^ j + 2 ^ (k - j) := by
          have heq : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
          rw [heq, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega : 0 < 2))]
        have heven : 2 ^ (k - j) % 2 = 0 := by
          have hk1 : k - j = (k - j - 1) + 1 := by omega
          rw [hk1, Nat.pow_succ]; omega
        rw [hdiv]
        have hmod : (bitsVal f k / 2 ^ j + 2 ^ (k - j)) % 2 = (bitsVal f k / 2 ^ j) % 2 := by omega
        rw [hmod, ← Nat.testBit_eq_decide_div_mod_eq, ih]
        simp [hjk, h1]
      · by_cases hje : j = k
        · subst hje
          have hdiv : (bitsVal f j + 2 ^ j) / 2 ^ j = 1 := by
            rw [Nat.add_div_right _ (Nat.pow_pos (by omega : 0 < 2)), Nat.div_eq_of_lt hlt]
          rw [hdiv]
          simp [hfk]
        · have h1 : ¬ (j < k + 1) := by omega
          have hpow : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
          have hdiv : (bitsVal f k + 2 ^ k) / 2 ^ j = 0 :=
            Nat.div_eq_of_lt (by rw [Nat.pow_succ] at hpow; omega)
          rw [hdiv]
          simp [h1]

lemma bitsVal_eq_of_testBit (v k : ℕ) (hv : v < 2 ^ k) : bitsVal (fun j => v.testBit j) k = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitsVal_testBit]
  by_cases hj : j < k
  · simp [hj]
  · simp only [hj, ↓reduceIte]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))).symm

lemma flatten_ofFn_length {m W : ℕ} (f : Fin m → Fin W → Bool) :
    (List.ofFn (fun i : Fin m => List.ofFn (f i))).flatten.length = m * W := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
        ih (fun i => f i.succ)]
    ring

lemma flatten_ofFn_getD {m W : ℕ} (f : Fin m → Fin W → Bool) (i : Fin m) (p : Fin W) :
    (List.ofFn (fun r : Fin m => List.ofFn (f r))).flatten.getD (i.val * W + p.val) false = f i p := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getD_append _ _ _ _ (by simp [p.isLt])]
      rw [List.getD_eq_getElem _ _ (by simp [p.isLt]), List.getElem_ofFn]
    · intro i'
      have hge : (List.ofFn (f 0)).length ≤ i'.succ.val * W + p.val := by
        simp only [List.length_ofFn, Fin.val_succ, Nat.add_mul, one_mul]; omega
      rw [List.getD_append_right _ _ _ _ hge]
      have hidx : i'.succ.val * W + p.val - (List.ofFn (f 0)).length = i'.val * W + p.val := by
        simp only [List.length_ofFn, Fin.val_succ, Nat.add_mul, one_mul]; omega
      rw [hidx]
      exact ih (fun r => f r.succ) i'

def evalWire (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  ((Circuit.mk gs 0).wires x).getD w false

lemma wires_length (gs : List Gate) (x : List Bool) :
    ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
    x.length + gs.length
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_append (gs1 gs2 : List Gate) (x : List Bool) :
    (Circuit.mk (gs1 ++ gs2) 0).wires x =
      (Circuit.mk gs2 0).wires ((Circuit.mk gs1 0).wires x) := by
  simp only [Circuit.wires, List.foldl_append]

lemma wires_prefix_getD (gs : List Gate) (w0 : List Bool) (idx : ℕ) (hidx : idx < w0.length) :
    ((Circuit.mk gs 0).wires w0).getD idx false = w0.getD idx false := by
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD idx false =
    w0.getD idx false
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    rw [List.getD_append _ _ _ _ hidx]

lemma evalWire_append_left (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    evalWire (gs1 ++ gs2) x w = evalWire gs1 x w := by
  unfold evalWire
  rw [wires_append]
  exact wires_prefix_getD gs2 _ w (by rw [wires_length]; exact hw)

structure Builder (I : ℕ) where
  gates : List Gate
  hFan : FanInTwo ⟨gates, 0⟩
  hRB : ReadsBack I ⟨gates, 0⟩

def Builder.size {I : ℕ} (b : Builder I) : ℕ := b.gates.length

def Builder.empty (I : ℕ) : Builder I :=
  ⟨[], by simp [FanInTwo], by simp [ReadsBack]⟩

def Extends {I : ℕ} (b1 b2 : Builder I) : Prop :=
  ∃ extra : List Gate, b2.gates = b1.gates ++ extra

lemma Extends.refl {I : ℕ} (b : Builder I) : Extends b b := ⟨[], by simp⟩

lemma Extends.trans {I : ℕ} {b1 b2 b3 : Builder I}
    (h1 : Extends b1 b2) (h2 : Extends b2 b3) : Extends b1 b3 := by
  rcases h1 with ⟨e1, he1⟩
  rcases h2 with ⟨e2, he2⟩
  exact ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩

lemma Extends.size_le {I : ℕ} {b1 b2 : Builder I} (h : Extends b1 b2) :
    b1.size ≤ b2.size := by
  rcases h with ⟨e, he⟩
  simp only [Builder.size, he, List.length_append]
  omega

lemma Extends.bound {I : ℕ} {b1 b2 : Builder I} (h : Extends b1 b2) {w : ℕ}
    (hw : w < I + b1.size) : w < I + b2.size :=
  lt_of_lt_of_le hw (Nat.add_le_add_left h.size_le I)

lemma Extends.eval_eq {I : ℕ} {b1 b2 : Builder I} (h : Extends b1 b2)
    (x : List Bool) (hx : x.length = I) {w : ℕ} (hw : w < I + b1.size) :
    evalWire b2.gates x w = evalWire b1.gates x w := by
  rcases h with ⟨e, he⟩
  rw [he]
  exact evalWire_append_left b1.gates e x w (by rw [hx]; exact hw)

def addGate {I : ℕ} (b : Builder I) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2)
    (hins : ∀ w ∈ ins, w < I + b.size) : Builder I × ℕ :=
  let g : Gate := ⟨op, ins⟩
  let b' : Builder I :=
    { gates := b.gates ++ [g]
      hFan := by
        intro g' hg'
        rcases List.mem_append.mp hg' with hg' | hg'
        · exact b.hFan g' hg'
        · rw [List.mem_singleton.mp hg']; exact ⟨hop, hlen⟩
      hRB := by
        intro j hj i hi
        change j < (b.gates ++ [g]).length at hj
        change i ∈ ((b.gates ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
        by_cases hj' : j < b.gates.length
        · rw [List.getD_append _ _ _ _ hj'] at hi
          exact b.hRB j hj' i hi
        · have heq : j = b.gates.length := by
            simp only [List.length_append, List.length_singleton] at hj; omega
          subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl] at hi
          simp only [Nat.sub_self, List.getD_cons_zero] at hi
          exact hins i hi }
  (b', I + b.size)

lemma addGate_extends {I : ℕ} (b : Builder I) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ w ∈ ins, w < I + b.size) :
    Extends b (addGate b op ins hop hlen hins).1 :=
  ⟨[⟨op, ins⟩], rfl⟩

lemma addGate_size {I : ℕ} (b : Builder I) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ w ∈ ins, w < I + b.size) :
    (addGate b op ins hop hlen hins).1.size = b.size + 1 := by
  simp [addGate, Builder.size]

lemma addGate_bound {I : ℕ} (b : Builder I) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ w ∈ ins, w < I + b.size) :
    (addGate b op ins hop hlen hins).2 < I + (addGate b op ins hop hlen hins).1.size := by
  rw [addGate_size]; dsimp only [addGate]; omega

lemma addGate_eval {I : ℕ} (b : Builder I) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ w ∈ ins, w < I + b.size)
    (x : List Bool) (hx : x.length = I) :
    evalWire (addGate b op ins hop hlen hins).1.gates x (addGate b op ins hop hlen hins).2 =
      op.eval (ins.map (evalWire b.gates x)) := by
  dsimp only [addGate, evalWire]
  rw [wires_append]
  have hfold : (Circuit.mk [⟨op, ins⟩] 0).wires ((Circuit.mk b.gates 0).wires x) =
      (Circuit.mk b.gates 0).wires x ++ [op.eval (ins.map (evalWire b.gates x))] := by
    rfl
  rw [hfold]
  have hlenW : ((Circuit.mk b.gates 0).wires x).length = I + b.size := by
    rw [wires_length, hx]; rfl
  rw [List.getD_append_right _ _ _ _ (by rw [hlenW])]
  simp [hlenW]

def mkFalse {I : ℕ} (b : Builder I) : Builder I × ℕ :=
  addGate b GateOp.or [] (by simp) (by simp) (by simp)

def mkTrue {I : ℕ} (b : Builder I) : Builder I × ℕ :=
  addGate b GateOp.and [] (by simp) (by simp) (by simp)

def mkNot {I : ℕ} (b : Builder I) (w : ℕ) (hw : w < I + b.size) : Builder I × ℕ :=
  addGate b GateOp.not [w] (by simp) (by simp) (by intro u hu; simp at hu; subst hu; exact hw)

def mkAnd {I : ℕ} (b : Builder I) (u v : ℕ) (hu : u < I + b.size) (hv : v < I + b.size) : Builder I × ℕ :=
  addGate b GateOp.and [u, v] (by simp) (by simp) (by
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)

def mkOr {I : ℕ} (b : Builder I) (u v : ℕ) (hu : u < I + b.size) (hv : v < I + b.size) : Builder I × ℕ :=
  addGate b GateOp.or [u, v] (by simp) (by simp) (by
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)

lemma mkFalse_spec {I : ℕ} (b : Builder I) :
    let r := mkFalse b
    Extends b r.1 ∧ r.1.size = b.size + 1 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 = false := by
  refine ⟨addGate_extends .., addGate_size .., addGate_bound .., fun x hx => ?_⟩
  rw [mkFalse, addGate_eval _ _ _ _ _ _ x hx]; rfl

lemma mkTrue_spec {I : ℕ} (b : Builder I) :
    let r := mkTrue b
    Extends b r.1 ∧ r.1.size = b.size + 1 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 = true := by
  refine ⟨addGate_extends .., addGate_size .., addGate_bound .., fun x hx => ?_⟩
  rw [mkTrue, addGate_eval _ _ _ _ _ _ x hx]; rfl

lemma mkNot_spec {I : ℕ} (b : Builder I) (w : ℕ) (hw : w < I + b.size) :
    let r := mkNot b w hw
    Extends b r.1 ∧ r.1.size = b.size + 1 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 = !(evalWire b.gates x w) := by
  refine ⟨addGate_extends .., addGate_size .., addGate_bound .., fun x hx => ?_⟩
  rw [mkNot, addGate_eval _ _ _ _ _ _ x hx]; rfl

lemma mkAnd_spec {I : ℕ} (b : Builder I) (u v : ℕ) (hu : u < I + b.size) (hv : v < I + b.size) :
    let r := mkAnd b u v hu hv
    Extends b r.1 ∧ r.1.size = b.size + 1 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 = (evalWire b.gates x u && evalWire b.gates x v) := by
  refine ⟨addGate_extends .., addGate_size .., addGate_bound .., fun x hx => ?_⟩
  rw [mkAnd, addGate_eval _ _ _ _ _ _ x hx]; simp [GateOp.eval]

lemma mkOr_spec {I : ℕ} (b : Builder I) (u v : ℕ) (hu : u < I + b.size) (hv : v < I + b.size) :
    let r := mkOr b u v hu hv
    Extends b r.1 ∧ r.1.size = b.size + 1 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 = (evalWire b.gates x u || evalWire b.gates x v) := by
  refine ⟨addGate_extends .., addGate_size .., addGate_bound .., fun x hx => ?_⟩
  rw [mkOr, addGate_eval _ _ _ _ _ _ x hx]; simp [GateOp.eval]

def mkXor {I : ℕ} (b : Builder I) (u v : ℕ) (hu : u < I + b.size) (hv : v < I + b.size) : Builder I × ℕ :=
  let r1 := mkOr b u v hu hv
  have h1 : Extends b r1.1 := (mkOr_spec b u v hu hv).1
  let r2 := mkAnd r1.1 u v (h1.bound hu) (h1.bound hv)
  have h2 : Extends r1.1 r2.1 := (mkAnd_spec ..).1
  let r3 := mkNot r2.1 r2.2 (mkAnd_spec ..).2.2.1
  have h3 : Extends r2.1 r3.1 := (mkNot_spec ..).1
  mkAnd r3.1 r1.2 r3.2 ((h2.trans h3).bound (mkOr_spec ..).2.2.1) (mkNot_spec ..).2.2.1

lemma mkXor_spec {I : ℕ} (b : Builder I) (u v : ℕ) (hu : u < I + b.size) (hv : v < I + b.size) :
    let r := mkXor b u v hu hv
    Extends b r.1 ∧ r.1.size = b.size + 4 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 = Bool.xor (evalWire b.gates x u) (evalWire b.gates x v) := by
  dsimp only [mkXor]
  have s1 := mkOr_spec b u v hu hv
  have s2 := mkAnd_spec (mkOr b u v hu hv).1 u v (s1.1.bound hu) (s1.1.bound hv)
  have s3 := mkNot_spec (mkAnd (mkOr b u v hu hv).1 u v (s1.1.bound hu) (s1.1.bound hv)).1
    (mkAnd (mkOr b u v hu hv).1 u v (s1.1.bound hu) (s1.1.bound hv)).2 s2.2.2.1
  have s4 := mkAnd_spec _ (mkOr b u v hu hv).2 _ ((s2.1.trans s3.1).bound s1.2.2.1) s3.2.2.1
  refine ⟨s1.1.trans (s2.1.trans (s3.1.trans s4.1)), ?_, s4.2.2.1, fun x hx => ?_⟩
  · omega
  · rw [s4.2.2.2 x hx, (s2.1.trans s3.1).eval_eq x hx s1.2.2.1, s1.2.2.2 x hx,
        s3.2.2.2 x hx, s2.2.2.2 x hx, s1.1.eval_eq x hx hu, s1.1.eval_eq x hx hv]
    cases evalWire b.gates x u <;> cases evalWire b.gates x v <;> rfl

def mkMux {I : ℕ} (b : Builder I) (sel t f : ℕ)
    (hs : sel < I + b.size) (ht : t < I + b.size) (hf : f < I + b.size) : Builder I × ℕ :=
  let r1 := mkNot b sel hs
  have h1 : Extends b r1.1 := (mkNot_spec ..).1
  let r2 := mkAnd r1.1 sel t (h1.bound hs) (h1.bound ht)
  have h2 : Extends r1.1 r2.1 := (mkAnd_spec ..).1
  let r3 := mkAnd r2.1 r1.2 f (h2.bound (mkNot_spec ..).2.2.1) ((h1.trans h2).bound hf)
  have h3 : Extends r2.1 r3.1 := (mkAnd_spec ..).1
  mkOr r3.1 r2.2 r3.2 (h3.bound (mkAnd_spec ..).2.2.1) (mkAnd_spec ..).2.2.1

lemma mkMux_spec {I : ℕ} (b : Builder I) (sel t f : ℕ)
    (hs : sel < I + b.size) (ht : t < I + b.size) (hf : f < I + b.size) :
    let r := mkMux b sel t f hs ht hf
    Extends b r.1 ∧ r.1.size = b.size + 4 ∧ r.2 < I + r.1.size ∧
      ∀ x, x.length = I → evalWire r.1.gates x r.2 =
        if evalWire b.gates x sel then evalWire b.gates x t else evalWire b.gates x f := by
  dsimp only [mkMux]
  have s1 := mkNot_spec b sel hs
  have s2 := mkAnd_spec _ sel t (s1.1.bound hs) (s1.1.bound ht)
  have s3 := mkAnd_spec _ _ f (s2.1.bound s1.2.2.1) ((s1.1.trans s2.1).bound hf)
  have s4 := mkOr_spec _ _ _ (s3.1.bound s2.2.2.1) s3.2.2.1
  refine ⟨s1.1.trans (s2.1.trans (s3.1.trans s4.1)), ?_, s4.2.2.1, fun x hx => ?_⟩
  · omega
  · rw [s4.2.2.2 x hx, s3.1.eval_eq x hx s2.2.2.1, s2.2.2.2 x hx,
        s1.1.eval_eq x hx hs, s1.1.eval_eq x hx ht,
        s3.2.2.2 x hx, s2.1.eval_eq x hx s1.2.2.1, s1.2.2.2 x hx,
        (s1.1.trans s2.1).eval_eq x hx hf]
    cases evalWire b.gates x sel <;> cases evalWire b.gates x t <;> cases evalWire b.gates x f <;> rfl

lemma mkFullAdd_exists {I : ℕ} (b : Builder I) (u v cin : ℕ)
    (hu : u < I + b.size) (hv : v < I + b.size) (hc : cin < I + b.size) :
    ∃ (b' : Builder I) (sumW coutW : ℕ),
      Extends b b' ∧ b'.size = b.size + 12 ∧
      sumW < I + b'.size ∧ coutW < I + b'.size ∧
      ∀ x, x.length = I →
        (evalWire b'.gates x sumW).toNat + 2 * (evalWire b'.gates x coutW).toNat =
          (evalWire b.gates x u).toNat + (evalWire b.gates x v).toNat + (evalWire b.gates x cin).toNat := by
  have s1 := mkXor_spec b u v hu hv
  rcases h1 : mkXor b u v hu hv with ⟨b1, w1⟩
  rw [h1] at s1
  have s2 := mkXor_spec b1 w1 cin s1.2.2.1 (s1.1.bound hc)
  rcases h2 : mkXor b1 w1 cin s1.2.2.1 (s1.1.bound hc) with ⟨b2, w2⟩
  rw [h2] at s2
  have s3 := mkAnd_spec b2 u v ((s1.1.trans s2.1).bound hu) ((s1.1.trans s2.1).bound hv)
  rcases h3 : mkAnd b2 u v ((s1.1.trans s2.1).bound hu) ((s1.1.trans s2.1).bound hv) with ⟨b3, w3⟩
  rw [h3] at s3
  have s4 := mkOr_spec b3 u v ((s1.1.trans (s2.1.trans s3.1)).bound hu) ((s1.1.trans (s2.1.trans s3.1)).bound hv)
  rcases h4 : mkOr b3 u v ((s1.1.trans (s2.1.trans s3.1)).bound hu) ((s1.1.trans (s2.1.trans s3.1)).bound hv) with ⟨b4, w4⟩
  rw [h4] at s4
  have s5 := mkAnd_spec b4 cin w4 ((s1.1.trans (s2.1.trans (s3.1.trans s4.1))).bound hc) s4.2.2.1
  rcases h5 : mkAnd b4 cin w4 ((s1.1.trans (s2.1.trans (s3.1.trans s4.1))).bound hc) s4.2.2.1 with ⟨b5, w5⟩
  rw [h5] at s5
  have s6 := mkOr_spec b5 w3 w5 ((s4.1.trans s5.1).bound s3.2.2.1) s5.2.2.1
  rcases h6 : mkOr b5 w3 w5 ((s4.1.trans s5.1).bound s3.2.2.1) s5.2.2.1 with ⟨b6, w6⟩
  rw [h6] at s6
  have h26 : Extends b2 b6 := s3.1.trans (s4.1.trans (s5.1.trans s6.1))
  dsimp only at s1 s2 s3 s4 s5 s6
  refine ⟨b6, w2, w6, s1.1.trans (s2.1.trans h26), by omega, h26.bound s2.2.2.1, s6.2.2.1, fun x hx => ?_⟩
  rw [h26.eval_eq x hx s2.2.2.1, s2.2.2.2 x hx, s1.2.2.2 x hx, s1.1.eval_eq x hx hc,
      s6.2.2.2 x hx, (s4.1.trans s5.1).eval_eq x hx s3.2.2.1, s3.2.2.2 x hx,
      (s1.1.trans s2.1).eval_eq x hx hu, (s1.1.trans s2.1).eval_eq x hx hv,
      s5.2.2.2 x hx, (s1.1.trans (s2.1.trans (s3.1.trans s4.1))).eval_eq x hx hc,
      s4.2.2.2 x hx, (s1.1.trans (s2.1.trans s3.1)).eval_eq x hx hu,
      (s1.1.trans (s2.1.trans s3.1)).eval_eq x hx hv]
  cases evalWire b.gates x u <;> cases evalWire b.gates x v <;> cases evalWire b.gates x cin <;> decide

lemma mkFullSub_exists {I : ℕ} (b : Builder I) (u v bin : ℕ)
    (hu : u < I + b.size) (hv : v < I + b.size) (hb : bin < I + b.size) :
    ∃ (b' : Builder I) (diffW boutW : ℕ),
      Extends b b' ∧ b'.size = b.size + 13 ∧
      diffW < I + b'.size ∧ boutW < I + b'.size ∧
      ∀ x, x.length = I →
        (evalWire b.gates x u).toNat + 2 * (evalWire b'.gates x boutW).toNat =
          (evalWire b'.gates x diffW).toNat + (evalWire b.gates x v).toNat + (evalWire b.gates x bin).toNat := by
  have s1 := mkXor_spec b u v hu hv
  rcases h1 : mkXor b u v hu hv with ⟨b1, w1⟩
  rw [h1] at s1
  have s2 := mkXor_spec b1 w1 bin s1.2.2.1 (s1.1.bound hb)
  rcases h2 : mkXor b1 w1 bin s1.2.2.1 (s1.1.bound hb) with ⟨b2, w2⟩
  rw [h2] at s2
  have s3 := mkNot_spec b2 u ((s1.1.trans s2.1).bound hu)
  rcases h3 : mkNot b2 u ((s1.1.trans s2.1).bound hu) with ⟨b3, w3⟩
  rw [h3] at s3
  have s4 := mkAnd_spec b3 w3 v s3.2.2.1 ((s1.1.trans (s2.1.trans s3.1)).bound hv)
  rcases h4 : mkAnd b3 w3 v s3.2.2.1 ((s1.1.trans (s2.1.trans s3.1)).bound hv) with ⟨b4, w4⟩
  rw [h4] at s4
  have s5 := mkOr_spec b4 w3 v (s4.1.bound s3.2.2.1) ((s1.1.trans (s2.1.trans (s3.1.trans s4.1))).bound hv)
  rcases h5 : mkOr b4 w3 v (s4.1.bound s3.2.2.1) ((s1.1.trans (s2.1.trans (s3.1.trans s4.1))).bound hv) with ⟨b5, w5⟩
  rw [h5] at s5
  have s6 := mkAnd_spec b5 w5 bin s5.2.2.1 ((s1.1.trans (s2.1.trans (s3.1.trans (s4.1.trans s5.1)))).bound hb)
  rcases h6 : mkAnd b5 w5 bin s5.2.2.1 ((s1.1.trans (s2.1.trans (s3.1.trans (s4.1.trans s5.1)))).bound hb) with ⟨b6, w6⟩
  rw [h6] at s6
  have s7 := mkOr_spec b6 w4 w6 ((s5.1.trans s6.1).bound s4.2.2.1) s6.2.2.1
  rcases h7 : mkOr b6 w4 w6 ((s5.1.trans s6.1).bound s4.2.2.1) s6.2.2.1 with ⟨b7, w7⟩
  rw [h7] at s7
  have h27 : Extends b2 b7 := s3.1.trans (s4.1.trans (s5.1.trans (s6.1.trans s7.1)))
  dsimp only at s1 s2 s3 s4 s5 s6 s7
  refine ⟨b7, w2, w7, s1.1.trans (s2.1.trans h27), by omega, h27.bound s2.2.2.1, s7.2.2.1, fun x hx => ?_⟩
  rw [h27.eval_eq x hx s2.2.2.1, s2.2.2.2 x hx, s1.2.2.2 x hx, s1.1.eval_eq x hx hb,
      s7.2.2.2 x hx, (s5.1.trans s6.1).eval_eq x hx s4.2.2.1, s4.2.2.2 x hx,
      s3.2.2.2 x hx, (s1.1.trans s2.1).eval_eq x hx hu,
      (s1.1.trans (s2.1.trans s3.1)).eval_eq x hx hv,
      s6.2.2.2 x hx, s5.2.2.2 x hx, s4.1.eval_eq x hx s3.2.2.1, s3.2.2.2 x hx,
      (s1.1.trans s2.1).eval_eq x hx hu,
      (s1.1.trans (s2.1.trans (s3.1.trans s4.1))).eval_eq x hx hv,
      (s1.1.trans (s2.1.trans (s3.1.trans (s4.1.trans s5.1)))).eval_eq x hx hb]
  cases evalWire b.gates x u <;> cases evalWire b.gates x v <;> cases evalWire b.gates x bin <;> decide

lemma mkAddVec_exists {I B : ℕ} (b : Builder I) (cFalse : ℕ) (hcF : cFalse < I + b.size)
    (u v : Fin B → ℕ) (hu : ∀ j, u j < I + b.size) (hv : ∀ j, v j < I + b.size) :
    ∃ (b' : Builder I) (out : Fin B → ℕ) (cout : ℕ),
      Extends b b' ∧ b'.size = b.size + 12 * B ∧
      (∀ j, out j < I + b'.size) ∧ cout < I + b'.size ∧
      ∀ x, x.length = I → evalWire b.gates x cFalse = false →
        bitsVal (fun j => if h : j < B then evalWire b'.gates x (out ⟨j, h⟩) else false) B +
          (evalWire b'.gates x cout).toNat * 2 ^ B =
        bitsVal (fun j => if h : j < B then evalWire b.gates x (u ⟨j, h⟩) else false) B +
          bitsVal (fun j => if h : j < B then evalWire b.gates x (v ⟨j, h⟩) else false) B := by
  induction B generalizing b with
  | zero =>
    refine ⟨b, fun j => Fin.elim0 j, cFalse, Extends.refl b, by simp,
            fun j => Fin.elim0 j, hcF, fun x _ hF => by simp [bitsVal, hF]⟩
  | succ B ih =>
    obtain ⟨b1, out1, c1, h1, hs1, ho1, hc1, hev1⟩ :=
      ih b hcF (fun j => u j.castSucc) (fun j => v j.castSucc)
        (fun j => hu j.castSucc) (fun j => hv j.castSucc)
    obtain ⟨b2, sumW, coutW, hfa, hszfa, hsum_bnd, hcout_bnd, hfa_ev⟩ :=
      mkFullAdd_exists b1 (u (Fin.last B)) (v (Fin.last B)) c1
        (h1.bound (hu (Fin.last B))) (h1.bound (hv (Fin.last B))) hc1
    let out : Fin (B + 1) → ℕ := fun j =>
      if h : j.val < B then out1 ⟨j.val, h⟩ else sumW
    refine ⟨b2, out, coutW, h1.trans hfa, by omega, ?_, hcout_bnd, ?_⟩
    · intro j
      dsimp only [out]
      by_cases hj : j.val < B
      · simp only [hj, ↓reduceDIte]; exact hfa.bound (ho1 ⟨j.val, hj⟩)
      · simp only [hj, ↓reduceDIte]; exact hsum_bnd
    · intro x hx hF
      have h1_ev := hev1 x hx hF
      have hfa_x := hfa_ev x hx
      rw [h1.eval_eq x hx (hu (Fin.last B)), h1.eval_eq x hx (hv (Fin.last B))] at hfa_x
      have hlow_out : bitsVal (fun j => if h : j < B + 1 then evalWire b2.gates x (out ⟨j, h⟩) else false) B =
          bitsVal (fun j => if h : j < B then evalWire b1.gates x (out1 ⟨j, h⟩) else false) B := by
        apply bitsVal_congr; intro j hj
        have hj1 : j < B + 1 := by omega
        simp only [hj, hj1, ↓reduceDIte, out]
        exact hfa.eval_eq x hx (ho1 ⟨j, hj⟩)
      have hlow_u : bitsVal (fun j => if h : j < B + 1 then evalWire b.gates x (u ⟨j, h⟩) else false) B =
          bitsVal (fun j => if h : j < B then evalWire b.gates x (u (⟨j, h⟩ : Fin B).castSucc) else false) B := by
        apply bitsVal_congr; intro j hj
        have hj1 : j < B + 1 := by omega
        simp only [hj, hj1, ↓reduceDIte]; rfl
      have hlow_v : bitsVal (fun j => if h : j < B + 1 then evalWire b.gates x (v ⟨j, h⟩) else false) B =
          bitsVal (fun j => if h : j < B then evalWire b.gates x (v (⟨j, h⟩ : Fin B).castSucc) else false) B := by
        apply bitsVal_congr; intro j hj
        have hj1 : j < B + 1 := by omega
        simp only [hj, hj1, ↓reduceDIte]; rfl
      have htop_out : (if h : B < B + 1 then evalWire b2.gates x (out ⟨B, h⟩) else false) =
          evalWire b2.gates x sumW := by
        simp [out]
      have htop_u : (if h : B < B + 1 then evalWire b.gates x (u ⟨B, h⟩) else false) =
          evalWire b.gates x (u (Fin.last B)) := by
        simp [Fin.last]
      have htop_v : (if h : B < B + 1 then evalWire b.gates x (v ⟨B, h⟩) else false) =
          evalWire b.gates x (v (Fin.last B)) := by
        simp [Fin.last]
      simp only [bitsVal, hlow_out, hlow_u, hlow_v, htop_out, htop_u, htop_v, Nat.pow_succ]
      have hm := congrArg (· * 2 ^ B) hfa_x
      linarith

lemma mkSubLtVec_exists {I B : ℕ} (b : Builder I) (cFalse : ℕ) (hcF : cFalse < I + b.size)
    (u v : Fin B → ℕ) (hu : ∀ j, u j < I + b.size) (hv : ∀ j, v j < I + b.size) :
    ∃ (b' : Builder I) (diff : Fin B → ℕ) (ltW : ℕ),
      Extends b b' ∧ b'.size = b.size + 13 * B ∧
      (∀ j, diff j < I + b'.size) ∧ ltW < I + b'.size ∧
      ∀ x, x.length = I → evalWire b.gates x cFalse = false →
        let uVal := bitsVal (fun j => if h : j < B then evalWire b.gates x (u ⟨j, h⟩) else false) B
        let vVal := bitsVal (fun j => if h : j < B then evalWire b.gates x (v ⟨j, h⟩) else false) B
        let dVal := bitsVal (fun j => if h : j < B then evalWire b'.gates x (diff ⟨j, h⟩) else false) B
        uVal + (evalWire b'.gates x ltW).toNat * 2 ^ B = dVal + vVal := by
  induction B generalizing b with
  | zero =>
    refine ⟨b, fun j => Fin.elim0 j, cFalse, Extends.refl b, by simp,
            fun j => Fin.elim0 j, hcF, fun x _ hF => by simp [bitsVal, hF]⟩
  | succ B ih =>
    obtain ⟨b1, diff1, br1, h1, hs1, hd1, hbr1, hev1⟩ :=
      ih b hcF (fun j => u j.castSucc) (fun j => v j.castSucc)
        (fun j => hu j.castSucc) (fun j => hv j.castSucc)
    obtain ⟨b2, diffW, boutW, hfs, hszfs, hdiff_bnd, hbout_bnd, hfs_ev⟩ :=
      mkFullSub_exists b1 (u (Fin.last B)) (v (Fin.last B)) br1
        (h1.bound (hu (Fin.last B))) (h1.bound (hv (Fin.last B))) hbr1
    let diff : Fin (B + 1) → ℕ := fun j =>
      if h : j.val < B then diff1 ⟨j.val, h⟩ else diffW
    refine ⟨b2, diff, boutW, h1.trans hfs, by omega, ?_, hbout_bnd, ?_⟩
    · intro j
      dsimp only [diff]
      by_cases hj : j.val < B
      · simp only [hj, ↓reduceDIte]; exact hfs.bound (hd1 ⟨j.val, hj⟩)
      · simp only [hj, ↓reduceDIte]; exact hdiff_bnd
    · intro x hx hF
      dsimp only
      have h1_ev := hev1 x hx hF
      dsimp only at h1_ev
      have hfs_x := hfs_ev x hx
      rw [h1.eval_eq x hx (hu (Fin.last B)), h1.eval_eq x hx (hv (Fin.last B))] at hfs_x
      have hlow_d : bitsVal (fun j => if h : j < B + 1 then evalWire b2.gates x (diff ⟨j, h⟩) else false) B =
          bitsVal (fun j => if h : j < B then evalWire b1.gates x (diff1 ⟨j, h⟩) else false) B := by
        apply bitsVal_congr; intro j hj
        have hj1 : j < B + 1 := by omega
        simp only [hj, hj1, ↓reduceDIte, diff]
        exact hfs.eval_eq x hx (hd1 ⟨j, hj⟩)
      have hlow_u : bitsVal (fun j => if h : j < B + 1 then evalWire b.gates x (u ⟨j, h⟩) else false) B =
          bitsVal (fun j => if h : j < B then evalWire b.gates x (u (⟨j, h⟩ : Fin B).castSucc) else false) B := by
        apply bitsVal_congr; intro j hj
        have hj1 : j < B + 1 := by omega
        simp only [hj, hj1, ↓reduceDIte]; rfl
      have hlow_v : bitsVal (fun j => if h : j < B + 1 then evalWire b.gates x (v ⟨j, h⟩) else false) B =
          bitsVal (fun j => if h : j < B then evalWire b.gates x (v (⟨j, h⟩ : Fin B).castSucc) else false) B := by
        apply bitsVal_congr; intro j hj
        have hj1 : j < B + 1 := by omega
        simp only [hj, hj1, ↓reduceDIte]; rfl
      have htop_d : (if h : B < B + 1 then evalWire b2.gates x (diff ⟨B, h⟩) else false) =
          evalWire b2.gates x diffW := by
        simp [diff]
      have htop_u : (if h : B < B + 1 then evalWire b.gates x (u ⟨B, h⟩) else false) =
          evalWire b.gates x (u (Fin.last B)) := by
        simp [Fin.last]
      have htop_v : (if h : B < B + 1 then evalWire b.gates x (v ⟨B, h⟩) else false) =
          evalWire b.gates x (v (Fin.last B)) := by
        simp [Fin.last]
      simp only [bitsVal, hlow_d, hlow_u, hlow_v, htop_d, htop_u, htop_v, Nat.pow_succ]
      have hm := congrArg (· * 2 ^ B) hfs_x
      linarith

lemma subLt_decode {B uVal vVal dVal : ℕ} {ltB : Bool}
    (_hu : uVal < 2 ^ B) (_hv : vVal < 2 ^ B) (hd : dVal < 2 ^ B)
    (heq : uVal + ltB.toNat * 2 ^ B = dVal + vVal) :
    (ltB = true ↔ uVal < vVal) ∧ (vVal ≤ uVal → dVal = uVal - vVal) := by
  cases ltB
  · simp only [Bool.toNat_false, zero_mul, add_zero, Bool.false_eq_true, false_iff, not_lt] at heq ⊢
    exact ⟨by omega, fun _ => by omega⟩
  · simp only [Bool.toNat_true, one_mul, true_iff] at heq ⊢
    exact ⟨by omega, fun hle => by omega⟩

lemma mkAndList_exists {I : ℕ} (b : Builder I) (cTrue : ℕ) (hcT : cTrue < I + b.size)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < I + b.size) :
    ∃ (b' : Builder I) (out : ℕ),
      Extends b b' ∧ b'.size = b.size + ws.length ∧ out < I + b'.size ∧
      ∀ x, x.length = I → evalWire b.gates x cTrue = true →
        (evalWire b'.gates x out = true ↔ ∀ w ∈ ws, evalWire b.gates x w = true) := by
  induction ws generalizing b with
  | nil =>
    refine ⟨b, cTrue, Extends.refl b, by simp, hcT, fun x _ hT => by simp [hT]⟩
  | cons w ws ih =>
    obtain ⟨b1, out1, h1, hs1, ho1, hev1⟩ :=
      ih b hcT (fun u hu => hws u (List.mem_cons_of_mem w hu))
    let r := mkAnd b1 out1 w ho1 (h1.bound (hws w List.mem_cons_self))
    have sr := mkAnd_spec b1 out1 w ho1 (h1.bound (hws w List.mem_cons_self))
    refine ⟨r.1, r.2, h1.trans sr.1, ?_, sr.2.2.1, fun x hx hT => ?_⟩
    · simp only [List.length_cons]; have hr : r.1.size = b1.size + 1 := sr.2.1; omega
    · rw [sr.2.2.2 x hx, h1.eval_eq x hx (hws w List.mem_cons_self),
          Bool.and_eq_true, hev1 x hx hT]
      constructor
      · rintro ⟨hrest, hw⟩ u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hw
        · exact hrest u hu'
      · intro hall
        exact ⟨fun u hu => hall u (List.mem_cons_of_mem w hu), hall w List.mem_cons_self⟩

lemma mkOrVec_exists {I B : ℕ} (b : Builder I) (cFalse : ℕ) (hcF : cFalse < I + b.size)
    (ws : Fin B → ℕ) (hws : ∀ j, ws j < I + b.size) :
    ∃ (b' : Builder I) (out : ℕ),
      Extends b b' ∧ b'.size = b.size + B ∧ out < I + b'.size ∧
      ∀ x, x.length = I → evalWire b.gates x cFalse = false →
        (evalWire b'.gates x out = true ↔ ∃ j : Fin B, evalWire b.gates x (ws j) = true) := by
  induction B generalizing b with
  | zero =>
    refine ⟨b, cFalse, Extends.refl b, by simp, hcF, fun x _ hF => by simp [hF]⟩
  | succ B ih =>
    obtain ⟨b1, out1, h1, hs1, ho1, hev1⟩ :=
      ih b hcF (fun j => ws j.castSucc) (fun j => hws j.castSucc)
    let r := mkOr b1 out1 (ws (Fin.last B)) ho1 (h1.bound (hws (Fin.last B)))
    have sr := mkOr_spec b1 out1 (ws (Fin.last B)) ho1 (h1.bound (hws (Fin.last B)))
    refine ⟨r.1, r.2, h1.trans sr.1, ?_, sr.2.2.1, fun x hx hF => ?_⟩
    · have hr : r.1.size = b1.size + 1 := sr.2.1; omega
    · rw [sr.2.2.2 x hx, h1.eval_eq x hx (hws (Fin.last B)), Bool.or_eq_true, hev1 x hx hF]
      constructor
      · rintro (⟨j, hj⟩ | hlast)
        · exact ⟨j.castSucc, hj⟩
        · exact ⟨Fin.last B, hlast⟩
      · rintro ⟨j, hj⟩
        refine Fin.lastCases ?_ ?_ j hj
        · intro hl; exact Or.inr hl
        · intro j' hj'; exact Or.inl ⟨j', hj'⟩

lemma mkMaskVec_exists {I B : ℕ} (b : Builder I) (en : ℕ) (hen : en < I + b.size)
    (ws : Fin B → ℕ) (hws : ∀ j, ws j < I + b.size) :
    ∃ (b' : Builder I) (out : Fin B → ℕ),
      Extends b b' ∧ b'.size = b.size + B ∧ (∀ j, out j < I + b'.size) ∧
      ∀ x, x.length = I → ∀ j : Fin B,
        evalWire b'.gates x (out j) = (evalWire b.gates x en && evalWire b.gates x (ws j)) := by
  induction B generalizing b with
  | zero =>
    refine ⟨b, fun j => Fin.elim0 j, Extends.refl b, by simp,
            fun j => Fin.elim0 j, fun _ _ j => Fin.elim0 j⟩
  | succ B ih =>
    obtain ⟨b1, out1, h1, hs1, ho1, hev1⟩ :=
      ih b hen (fun j => ws j.castSucc) (fun j => hws j.castSucc)
    let r := mkAnd b1 en (ws (Fin.last B)) (h1.bound hen) (h1.bound (hws (Fin.last B)))
    have sr := mkAnd_spec b1 en (ws (Fin.last B)) (h1.bound hen) (h1.bound (hws (Fin.last B)))
    let out : Fin (B + 1) → ℕ := fun j =>
      if h : j.val < B then out1 ⟨j.val, h⟩ else r.2
    refine ⟨r.1, out, h1.trans sr.1, ?_, ?_, fun x hx j => ?_⟩
    · have hr : r.1.size = b1.size + 1 := sr.2.1; omega
    · intro j; dsimp only [out]
      by_cases hj : j.val < B
      · simp only [hj, ↓reduceDIte]; exact sr.1.bound (ho1 ⟨j.val, hj⟩)
      · simp only [hj, ↓reduceDIte]; exact sr.2.2.1
    · dsimp only [out]
      by_cases hj : j.val < B
      · simp only [hj, ↓reduceDIte]
        rw [sr.1.eval_eq x hx (ho1 ⟨j.val, hj⟩), hev1 x hx ⟨j.val, hj⟩]
        rfl
      · simp only [hj, ↓reduceDIte]
        rw [sr.2.2.2 x hx, h1.eval_eq x hx hen, h1.eval_eq x hx (hws (Fin.last B))]
        have hjeq : j = Fin.last B := Fin.ext (by simp [Fin.last]; omega)
        rw [hjeq]

lemma mkMuxVec_exists {I B : ℕ} (b : Builder I) (sel : ℕ) (hsel : sel < I + b.size)
    (tVec fVec : Fin B → ℕ) (ht : ∀ j, tVec j < I + b.size) (hf : ∀ j, fVec j < I + b.size) :
    ∃ (b' : Builder I) (out : Fin B → ℕ),
      Extends b b' ∧ b'.size = b.size + 4 * B ∧ (∀ j, out j < I + b'.size) ∧
      ∀ x, x.length = I → ∀ j : Fin B,
        evalWire b'.gates x (out j) =
          if evalWire b.gates x sel then evalWire b.gates x (tVec j) else evalWire b.gates x (fVec j) := by
  induction B generalizing b with
  | zero =>
    refine ⟨b, fun j => Fin.elim0 j, Extends.refl b, by simp,
            fun j => Fin.elim0 j, fun _ _ j => Fin.elim0 j⟩
  | succ B ih =>
    obtain ⟨b1, out1, h1, hs1, ho1, hev1⟩ :=
      ih b hsel (fun j => tVec j.castSucc) (fun j => fVec j.castSucc)
        (fun j => ht j.castSucc) (fun j => hf j.castSucc)
    let r := mkMux b1 sel (tVec (Fin.last B)) (fVec (Fin.last B))
      (h1.bound hsel) (h1.bound (ht (Fin.last B))) (h1.bound (hf (Fin.last B)))
    have sr := mkMux_spec b1 sel (tVec (Fin.last B)) (fVec (Fin.last B))
      (h1.bound hsel) (h1.bound (ht (Fin.last B))) (h1.bound (hf (Fin.last B)))
    let out : Fin (B + 1) → ℕ := fun j =>
      if h : j.val < B then out1 ⟨j.val, h⟩ else r.2
    refine ⟨r.1, out, h1.trans sr.1, ?_, ?_, fun x hx j => ?_⟩
    · have hr : r.1.size = b1.size + 4 := sr.2.1; omega
    · intro j; dsimp only [out]
      by_cases hj : j.val < B
      · simp only [hj, ↓reduceDIte]; exact sr.1.bound (ho1 ⟨j.val, hj⟩)
      · simp only [hj, ↓reduceDIte]; exact sr.2.2.1
    · dsimp only [out]
      by_cases hj : j.val < B
      · simp only [hj, ↓reduceDIte]
        rw [sr.1.eval_eq x hx (ho1 ⟨j.val, hj⟩), hev1 x hx ⟨j.val, hj⟩]
        rfl
      · simp only [hj, ↓reduceDIte]
        rw [sr.2.2.2 x hx, h1.eval_eq x hx hsel, h1.eval_eq x hx (ht (Fin.last B)),
            h1.eval_eq x hx (hf (Fin.last B))]
        have hjeq : j = Fin.last B := Fin.ext (by simp [Fin.last]; omega)
        rw [hjeq]

lemma spliceSub_exists {I Isub : ℕ} (b : Builder I) (sub : Circuit)
    (hFan : FanInTwo sub) (hRB : ReadsBack Isub sub)
    (inpMap : Fin Isub → ℕ) (hinp : ∀ k, inpMap k < I + b.size) :
    ∃ b' : Builder I,
      Extends b b' ∧ b'.size = b.size + sub.size ∧
      ∀ (x : List Bool), x.length = I →
        ∀ (w : ℕ), w < Isub + sub.size →
          let w' := if h : w < Isub then inpMap ⟨w, h⟩ else (I + b.size) + (w - Isub)
          w' < I + b'.size ∧
          evalWire b'.gates x w' =
            (sub.wires (List.ofFn (fun k : Fin Isub => evalWire b.gates x (inpMap k)))).getD w false := by
  let base := I + b.size
  let remap : ℕ → ℕ := fun w => if h : w < Isub then inpMap ⟨w, h⟩ else base + (w - Isub)
  let remapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map remap⟩
  let extra : List Gate := sub.gates.map remapGate
  have hFan' : FanInTwo ⟨b.gates ++ extra, 0⟩ := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact b.hFan g hg
    · rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
      rcases hFan g0 hg0 with ⟨hop, hlen⟩
      exact ⟨hop, by simp [remapGate, hlen]⟩
  have hRB' : ReadsBack I ⟨b.gates ++ extra, 0⟩ := by
    intro j hj i hi
    change j < (b.gates ++ extra).length at hj
    change i ∈ ((b.gates ++ extra).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < b.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact b.hRB j hj' i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have hj2 : j - b.gates.length < sub.gates.length := by
        simp only [List.length_append, extra, List.length_map] at hj; omega
      have hget : extra.getD (j - b.gates.length) ⟨GateOp.or, []⟩ =
          remapGate (gateAt sub (j - b.gates.length)) := by
        dsimp only [extra, gateAt]
        rw [List.getD_eq_getElem _ _ (by simp [hj2]),
            List.getD_eq_getElem _ _ hj2, List.getElem_map]
      rw [hget] at hi
      rcases List.mem_map.mp hi with ⟨w0, hw0, rfl⟩
      have hw0_lt : w0 < Isub + (j - b.gates.length) := hRB (j - b.gates.length) hj2 w0 hw0
      dsimp only [remap]
      by_cases hw : w0 < Isub
      · simp only [hw, ↓reduceDIte]
        have := hinp ⟨w0, hw⟩
        dsimp only [Builder.size] at this
        omega
      · simp only [hw, ↓reduceDIte]
        dsimp only [base, Builder.size]
        omega
  let b' : Builder I := ⟨b.gates ++ extra, hFan', hRB'⟩
  refine ⟨b', ⟨extra, rfl⟩, by simp [b', extra, Builder.size, Circuit.size], ?_⟩
  intro x hx
  let xSub : List Bool := List.ofFn (fun k : Fin Isub => evalWire b.gates x (inpMap k))
  have hstep : ∀ (gs : List Gate),
      (∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, w < Isub + j) →
      ∀ (w : ℕ), w < Isub + gs.length →
        evalWire (b.gates ++ gs.map remapGate) x (remap w) =
          ((Circuit.mk gs 0).wires xSub).getD w false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ w hw
      simp only [List.length_nil, add_zero] at hw
      simp only [List.map_nil, List.append_nil, remap, hw, ↓reduceDIte,
                 Circuit.wires, List.foldl_nil, xSub]
      rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
    | append_singleton gs g ih =>
      intro hrb w hw
      have hrb_pre : ∀ j < gs.length, ∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, u < Isub + j := by
        intro j hj u hu
        have h1 := hrb j (by simp only [List.length_append, List.length_singleton]; omega) u
        rw [List.getD_append _ _ _ _ hj] at h1
        exact h1 hu
      have hrb_last : ∀ u ∈ g.inputs, u < Isub + gs.length := by
        intro u hu
        have h1 := hrb gs.length (by simp) u
        rw [List.getD_append_right _ _ _ _ le_rfl] at h1
        simp only [Nat.sub_self, List.getD_cons_zero] at h1
        exact h1 hu
      have happ : b.gates ++ (gs ++ [g]).map remapGate =
          (b.gates ++ gs.map remapGate) ++ [remapGate g] := by
        simp [List.map_append, List.append_assoc]
      rw [happ]
      by_cases hw_pre : w < Isub + gs.length
      · have hrm_lt : remap w < x.length + (b.gates ++ gs.map remapGate).length := by
          dsimp only [remap, base, Builder.size]
          by_cases hwi : w < Isub
          · simp only [hwi, ↓reduceDIte]
            have := hinp ⟨w, hwi⟩
            simp only [List.length_append, List.length_map, Builder.size] at this ⊢
            omega
          · simp only [hwi, ↓reduceDIte]
            simp only [List.length_append, List.length_map]
            omega
        rw [evalWire_append_left _ _ x _ hrm_lt, ih hrb_pre w hw_pre]
        rw [wires_append]
        exact (wires_prefix_getD [g] _ w (by rw [wires_length]; simp only [xSub, List.length_ofFn]; exact hw_pre)).symm
      · have hw_eq : w = Isub + gs.length := by
          simp only [List.length_append, List.length_singleton] at hw; omega
        subst hw_eq
        have hrm_eq : remap (Isub + gs.length) = x.length + (b.gates ++ gs.map remapGate).length := by
          dsimp only [remap, base, Builder.size]
          have hnot : ¬ (Isub + gs.length < Isub) := by omega
          simp only [hnot, ↓reduceDIte, List.length_append, List.length_map, hx]
          omega
        unfold evalWire
        conv_lhs => rw [wires_append]
        conv_rhs => rw [wires_append]
        have hfoldL : (Circuit.mk [remapGate g] 0).wires ((Circuit.mk (b.gates ++ gs.map remapGate) 0).wires x) =
            (Circuit.mk (b.gates ++ gs.map remapGate) 0).wires x ++
            [g.op.eval ((g.inputs.map remap).map (evalWire (b.gates ++ gs.map remapGate) x))] := rfl
        have hfoldR : (Circuit.mk [g] 0).wires ((Circuit.mk gs 0).wires xSub) =
            (Circuit.mk gs 0).wires xSub ++
            [g.op.eval (g.inputs.map (fun u => ((Circuit.mk gs 0).wires xSub).getD u false))] := rfl
        rw [hfoldL, hfoldR]
        have hlenL : ((Circuit.mk (b.gates ++ gs.map remapGate) 0).wires x).length =
            x.length + (b.gates ++ gs.map remapGate).length := wires_length _ _
        have hlenR : ((Circuit.mk gs 0).wires xSub).length = Isub + gs.length := by
          rw [wires_length]; simp [xSub]
        rw [List.getD_append_right _ _ _ _ (by rw [hlenL, hrm_eq])]
        rw [List.getD_append_right _ _ _ _ (by rw [hlenR])]
        simp only [hlenL, hrm_eq, Nat.sub_self, List.getD_cons_zero, hlenR, List.map_map]
        congr 1
        refine List.map_congr_left (fun u hu => ?_)
        exact ih hrb_pre u (hrb_last u hu)
  intro w hw
  refine ⟨?_, hstep sub.gates hRB w hw⟩
  dsimp only [b', extra, Builder.size, Circuit.size] at hw ⊢
  by_cases hwi : w < Isub
  · simp only [hwi, ↓reduceDIte]
    have := hinp ⟨w, hwi⟩
    simp only [List.length_append, List.length_map, Builder.size] at this ⊢
    omega
  · simp only [hwi, ↓reduceDIte]
    simp only [List.length_append, List.length_map]
    omega

abbrev dOf (n w : ℕ) : ℕ := min w (n - 1)
abbrev eOf (n m w : ℕ) : ℕ := m + dOf n w - n
abbrev aOf (n m w : ℕ) : ℕ := dOf n w + eOf n m w

abbrev wordBit (n : ℕ) (z : Fin (2 ^ n)) (pos : ℕ) : Bool :=
  z.val.testBit (n - 1 - pos)

def nextStateBit (d pos : ℕ) (sb : ℕ → Bool) (bit : Bool) (k : ℕ) : Bool :=
  if k < d then
    if k = 0 then bit else sb (k - 1)
  else
    if k = d + pos then bit else sb k

def nextState (d e pos : ℕ) (s : Fin (2 ^ (d + e))) (bit : Bool) : Fin (2 ^ (d + e)) :=
  ⟨bitsVal (nextStateBit d pos (fun k => s.val.testBit k) bit) (d + e), bitsVal_lt _ _⟩

lemma nextState_testBit (d e pos : ℕ) (s : Fin (2 ^ (d + e))) (bit : Bool) (k : ℕ)
    (hk : k < d + e) :
    (nextState d e pos s bit).val.testBit k = nextStateBit d pos (fun r => s.val.testBit r) bit k := by
  dsimp only [nextState]
  rw [bitsVal_testBit]
  simp [hk]

def trajPrefix (d e : ℕ) : ℕ → ℕ → Fin (2 ^ (d + e))
  | 0, _ => ⟨0, Nat.pow_pos (by omega : 0 < 2)⟩
  | pos + 1, pref => nextState d e pos (trajPrefix d e pos (pref / 2)) (decide (pref % 2 = 1))

lemma trajPrefix_step (d e pos pref : ℕ) (bit : Bool) :
    trajPrefix d e (pos + 1) (2 * pref + bit.toNat) =
      nextState d e pos (trajPrefix d e pos pref) bit := by
  simp only [trajPrefix]
  have h1 : (2 * pref + bit.toNat) / 2 = pref := by cases bit <;> simp <;> omega
  have h2 : decide ((2 * pref + bit.toNat) % 2 = 1) = bit := by cases bit <;> simp <;> omega
  rw [h1, h2]

lemma div_pow_succ_step {n pos : ℕ} (z : Fin (2 ^ n)) (hpos : pos < n) :
    z.val / 2 ^ (n - (pos + 1)) = 2 * (z.val / 2 ^ (n - pos)) + (wordBit n z pos).toNat := by
  have hsub : n - pos = (n - (pos + 1)) + 1 := by omega
  have hdiv : z.val / 2 ^ (n - pos) = (z.val / 2 ^ (n - (pos + 1))) / 2 := by
    rw [hsub, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have htb : (wordBit n z pos).toNat = (z.val / 2 ^ (n - (pos + 1))) % 2 := by
    have hidx : n - 1 - pos = n - (pos + 1) := by omega
    unfold wordBit
    rw [hidx, Nat.testBit_eq_decide_div_mod_eq]
    have hmod := Nat.mod_lt (z.val / 2 ^ (n - (pos + 1))) (by omega : 0 < 2)
    by_cases h1 : (z.val / 2 ^ (n - (pos + 1))) % 2 = 1
    · simp [h1]
    · have h0 : (z.val / 2 ^ (n - (pos + 1))) % 2 = 0 := by omega
      simp [h0]
  rw [hdiv, htb]
  have hdm := Nat.div_add_mod (z.val / 2 ^ (n - (pos + 1))) 2
  omega

lemma trajPrefix_word_succ (d e n pos : ℕ) (z : Fin (2 ^ n)) (hpos : pos < n) :
    trajPrefix d e (pos + 1) (z.val / 2 ^ (n - (pos + 1))) =
      nextState d e pos (trajPrefix d e pos (z.val / 2 ^ (n - pos))) (wordBit n z pos) := by
  rw [div_pow_succ_step z hpos, trajPrefix_step]

lemma trajPrefix_word_bits (d e n : ℕ) (z : Fin (2 ^ n)) :
    ∀ pos ≤ n,
      (∀ k < d, (trajPrefix d e pos (z.val / 2 ^ (n - pos))).val.testBit k =
        if k < pos then wordBit n z (pos - 1 - k) else false) ∧
      (∀ r < e, (trajPrefix d e pos (z.val / 2 ^ (n - pos))).val.testBit (d + r) =
        if r < pos then wordBit n z r else false) := by
  intro pos
  induction pos with
  | zero =>
    intro _
    constructor
    · intro k _; simp [trajPrefix]
    · intro r _; simp [trajPrefix]
  | succ pos ih =>
    intro hle
    have hpos : pos < n := by omega
    rcases ih (by omega) with ⟨ihD, ihE⟩
    rw [trajPrefix_word_succ d e n pos z hpos]
    constructor
    · intro k hk
      rw [nextState_testBit d e pos _ _ k (by omega)]
      simp only [nextStateBit, hk, ↓reduceIte]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp only [hk0, ↓reduceIte]
        rw [ihD (k - 1) (by omega)]
        by_cases hkp : k < pos + 1
        · have h1 : k - 1 < pos := by omega
          have h2 : pos - 1 - (k - 1) = pos - k := by omega
          simp [hkp, h1, h2]
        · have h1 : ¬ (k - 1 < pos) := by omega
          simp [hkp, h1]
    · intro r hr
      rw [nextState_testBit d e pos _ _ (d + r) (by omega)]
      have hnot : ¬ (d + r < d) := by omega
      simp only [nextStateBit, hnot, ↓reduceIte]
      by_cases hrp : r = pos
      · subst hrp; simp
      · have hne : d + r ≠ d + pos := by omega
        simp only [hne, ↓reduceIte]
        rw [ihE r hr]
        by_cases hlt : r < pos
        · have hlt1 : r < pos + 1 := by omega
          simp [hlt, hlt1]
        · have hlt1 : ¬ (r < pos + 1) := by omega
          simp [hlt, hlt1]

def transList (n m w pos : ℕ) : List (Fin m) :=
  (List.finRange m).filter (fun i => if w < n then decide (i.val + w = pos) else decide (pos = n - 1))

def termList (n m w : ℕ) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (w < n ∧ n ≤ i.val + w))

lemma mem_transList (n m w pos : ℕ) (i : Fin m) :
    i ∈ transList n m w pos ↔ (if w < n then i.val + w = pos else pos = n - 1) := by
  simp only [transList, List.mem_filter, List.mem_finRange, true_and]
  by_cases h : w < n <;> simp [h]

lemma mem_termList (n m w : ℕ) (i : Fin m) :
    i ∈ termList n m w ↔ (w < n ∧ n ≤ i.val + w) := by
  simp only [termList, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

lemma sum_trans_term_len (n m w : ℕ) (hn : 0 < n) :
    (∑ pos : Fin n, (transList n m w pos.val).length) + (termList n m w).length = m := by
  have hgen : ∀ L : List (Fin m),
      (∑ pos : Fin n, (L.filter (fun i => if w < n then decide (i.val + w = pos.val) else decide (pos.val = n - 1))).length) +
      (L.filter (fun i => decide (w < n ∧ n ≤ i.val + w))).length = L.length := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.filter_cons, List.length_cons]
      have hsplit : (∑ pos : Fin n,
          (if (if w < n then decide (a.val + w = pos.val) else decide (pos.val = n - 1)) = true
           then (L.filter (fun i => if w < n then decide (i.val + w = pos.val) else decide (pos.val = n - 1))).length + 1
           else (L.filter (fun i => if w < n then decide (i.val + w = pos.val) else decide (pos.val = n - 1))).length)) =
        (∑ pos : Fin n, (L.filter (fun i => if w < n then decide (i.val + w = pos.val) else decide (pos.val = n - 1))).length) +
        (∑ pos : Fin n, if (if w < n then decide (a.val + w = pos.val) else decide (pos.val = n - 1)) = true then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun pos _ => ?_)
        split_ifs <;> omega
      have hones : (∑ pos : Fin n, if (if w < n then decide (a.val + w = pos.val) else decide (pos.val = n - 1)) = true then 1 else 0) +
          (if decide (w < n ∧ n ≤ a.val + w) = true then 1 else 0) = 1 := by
        by_cases hwn : w < n
        · by_cases hlt : a.val + w < n
          · have hnot : ¬ (w < n ∧ n ≤ a.val + w) := by omega
            simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
            simp only [hwn, ↓reduceIte]
            rw [Finset.sum_eq_single ⟨a.val + w, hlt⟩]
            · simp
            · intro pos _ hne
              have hval : a.val + w ≠ pos.val := fun h => hne (Fin.ext h.symm)
              simp [hval]
            · intro h; exact False.elim (h (Finset.mem_univ _))
          · have hyes : w < n ∧ n ≤ a.val + w := ⟨hwn, by omega⟩
            simp only [hyes, ↓reduceIte]
            have hz : (∑ pos : Fin n, if decide (a.val + w = pos.val) = true then 1 else 0) = 0 := by
              refine Finset.sum_eq_zero (fun pos _ => ?_)
              have hne : a.val + w ≠ pos.val := by have := pos.isLt; omega
              simp [hne]
            rw [hz]
            simp
        · have hnot : ¬ (w < n ∧ n ≤ a.val + w) := fun h => hwn h.1
          simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
          simp only [hwn, ↓reduceIte]
          rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
          · simp
          · intro pos _ hne
            have hval : pos.val ≠ n - 1 := fun h => hne (Fin.ext h)
            simp [hval]
          · intro h; exact False.elim (h (Finset.mem_univ _))
      have hterm : (if decide (w < n ∧ n ≤ a.val + w) = true then
          (L.filter (fun i => decide (w < n ∧ n ≤ i.val + w))).length + 1
          else (L.filter (fun i => decide (w < n ∧ n ≤ i.val + w))).length) =
          (L.filter (fun i => decide (w < n ∧ n ≤ i.val + w))).length +
          (if decide (w < n ∧ n ≤ a.val + w) = true then 1 else 0) := by
        split_ifs <;> omega
      have hlen_cons : ∀ (b : Bool) (xs : List (Fin m)),
          (if b = true then a :: xs else xs).length = if b = true then xs.length + 1 else xs.length := by
        intro b xs; cases b <;> simp
      simp_rw [hlen_cons]
      rw [hsplit, hterm]
      omega
  simpa [transList, termList, List.length_finRange] using hgen (List.finRange m)

def transPat (n m w pos : ℕ) (s : Fin (2 ^ aOf n m w)) (bit : Bool) (i : Fin m) (j : Fin (w + 1)) : Bool :=
  if w < n then
    if j.val < w then s.val.testBit (w - 1 - j.val) else bit
  else
    let r := (i.val + j.val) % n
    if r < n - 1 then s.val.testBit (n - 2 - r) else bit

def termPat (n m w : ℕ) (s : Fin (2 ^ aOf n m w)) (i : Fin m) (j : Fin (w + 1)) : Bool :=
  if i.val + j.val < n then s.val.testBit (n - 1 - (i.val + j.val))
  else s.val.testBit (dOf n w + (i.val + j.val - n))

def patCode (w : ℕ) (pat : Fin (w + 1) → Bool) : Fin (2 ^ (w + 1)) :=
  ⟨bitsVal (fun j => if h : j < w + 1 then pat ⟨j, h⟩ else false) (w + 1), bitsVal_lt _ _⟩

lemma patCode_testBit (w : ℕ) (pat : Fin (w + 1) → Bool) (j : Fin (w + 1)) :
    (patCode w pat).val.testBit j.val = pat j := by
  dsimp only [patCode]
  rw [bitsVal_testBit]
  simp [j.isLt]

def transOK (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (pos : ℕ) (s : Fin (2 ^ aOf n m w)) (bit : Bool) : Bool :=
  (transList n m w pos).all (fun i => table i (transPat n m w pos s bit i))

def termOK (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (s : Fin (2 ^ aOf n m w)) : Bool :=
  (termList n m w).all (fun i => table i (termPat n m w s i))

lemma transPat_eq_word (n m w pos : ℕ) (hn : 0 < n) (hpos : pos < n)
    (z : Fin (2 ^ n)) (i : Fin m) (hi : i ∈ transList n m w pos) :
    transPat n m w pos (trajPrefix (dOf n w) (eOf n m w) pos (z.val / 2 ^ (n - pos))) (wordBit n z pos) i =
      (fun j : Fin (w + 1) => wordBit n z ((i.val + j.val) % n)) := by
  have hmem := (mem_transList n m w pos i).mp hi
  have hbits := (trajPrefix_word_bits (dOf n w) (eOf n m w) n z pos (by omega)).1
  funext j
  dsimp only [transPat]
  by_cases hwn : w < n
  · simp only [hwn, ↓reduceIte] at hmem ⊢
    have hd : dOf n w = w := by dsimp only [dOf]; omega
    have hlt_n : i.val + j.val < n := by have := j.isLt; omega
    rw [Nat.mod_eq_of_lt hlt_n]
    by_cases hjw : j.val < w
    · simp only [hjw, ↓reduceIte]
      rw [hbits (w - 1 - j.val) (by omega)]
      have h1 : w - 1 - j.val < pos := by omega
      have h2 : pos - 1 - (w - 1 - j.val) = i.val + j.val := by omega
      simp [h1, h2]
    · have hj_eq : j.val = w := by have := j.isLt; omega
      simp only [hjw, ↓reduceIte]
      rw [hj_eq, hmem]
  · simp only [hwn, ↓reduceIte] at hmem ⊢
    have hd : dOf n w = n - 1 := by dsimp only [dOf]; omega
    set r := (i.val + j.val) % n
    have hr_lt : r < n := Nat.mod_lt _ hn
    by_cases hr : r < n - 1
    · simp only [hr, ↓reduceIte]
      rw [hbits (n - 2 - r) (by omega)]
      have h1 : n - 2 - r < pos := by omega
      have h2 : pos - 1 - (n - 2 - r) = r := by omega
      simp [h1, h2]
    · have hr_eq : r = pos := by omega
      simp only [hr, ↓reduceIte, ← hr_eq]

lemma termPat_eq_word (n m w : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (z : Fin (2 ^ n)) (i : Fin m) (hi : i ∈ termList n m w) :
    termPat n m w (trajPrefix (dOf n w) (eOf n m w) n z.val) i =
      (fun j : Fin (w + 1) => wordBit n z ((i.val + j.val) % n)) := by
  have hmem := (mem_termList n m w i).mp hi
  have hbits := trajPrefix_word_bits (dOf n w) (eOf n m w) n z n le_rfl
  have hzdiv : z.val / 2 ^ (n - n) = z.val := by simp
  rw [hzdiv] at hbits
  have hd : dOf n w = w := by dsimp only [dOf]; omega
  funext j
  dsimp only [termPat]
  by_cases hlt : i.val + j.val < n
  · simp only [hlt, ↓reduceIte]
    rw [Nat.mod_eq_of_lt hlt, hbits.1 (n - 1 - (i.val + j.val)) (by omega)]
    have h1 : n - 1 - (i.val + j.val) < n := by omega
    have h2 : n - 1 - (n - 1 - (i.val + j.val)) = i.val + j.val := by omega
    simp [h1, h2]
  · simp only [hlt, ↓reduceIte]
    have hlt2n : i.val + j.val < 2 * n := by have := i.isLt; have := j.isLt; omega
    have hmod : (i.val + j.val) % n = i.val + j.val - n := by
      have hsub : i.val + j.val = n + (i.val + j.val - n) := by omega
      conv_lhs => rw [hsub]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hr_lt : i.val + j.val - n < eOf n m w := by
      dsimp only [eOf]; have := i.isLt; have := j.isLt; omega
    rw [hmod, hbits.2 (i.val + j.val - n) hr_lt]
    have h1 : i.val + j.val - n < n := by omega
    simp [h1]

lemma sols_iff_dp (n m w : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (z : Fin (2 ^ n)) :
    (∀ i : Fin m, table i (fun j => wordBit n z ((i.val + j.val) % n)) = true) ↔
      (∀ pos < n, transOK n m w table pos
        (trajPrefix (dOf n w) (eOf n m w) pos (z.val / 2 ^ (n - pos))) (wordBit n z pos) = true) ∧
      termOK n m w table (trajPrefix (dOf n w) (eOf n m w) n z.val) = true := by
  constructor
  · intro hall
    constructor
    · intro pos hpos
      rw [transOK, List.all_eq_true]
      intro i hi
      rw [transPat_eq_word n m w pos hn hpos z i hi]
      exact hall i
    · rw [termOK, List.all_eq_true]
      intro i hi
      rw [termPat_eq_word n m w hn hmn z i hi]
      exact hall i
  · rintro ⟨htr, htm⟩ i
    by_cases hwn : w < n
    · by_cases hlt : i.val + w < n
      · have hi : i ∈ transList n m w (i.val + w) := (mem_transList n m w (i.val + w) i).mpr (by simp [hwn])
        have h1 := List.all_eq_true.mp (htr (i.val + w) hlt) i hi
        rwa [transPat_eq_word n m w (i.val + w) hn hlt z i hi] at h1
      · have hi : i ∈ termList n m w := (mem_termList n m w i).mpr ⟨hwn, by omega⟩
        have h1 := List.all_eq_true.mp htm i hi
        rwa [termPat_eq_word n m w hn hmn z i hi] at h1
    · have hi : i ∈ transList n m w (n - 1) := (mem_transList n m w (n - 1) i).mpr (by simp [hwn])
      have h1 := List.all_eq_true.mp (htr (n - 1) (by omega)) i hi
      rwa [transPat_eq_word n m w (n - 1) hn (by omega) z i hi] at h1

def cntRec (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) :
    ℕ → Fin (2 ^ aOf n m w) → ℕ
  | 0, s => if termOK n m w table s then 1 else 0
  | rem + 1, s =>
    let pos := n - (rem + 1)
    let c0 := if transOK n m w table pos s false
      then cntRec n m w table rem (nextState (dOf n w) (eOf n m w) pos s false) else 0
    let c1 := if transOK n m w table pos s true
      then cntRec n m w table rem (nextState (dOf n w) (eOf n m w) pos s true) else 0
    c0 + c1

def cnt0At (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (pos : ℕ) (s : Fin (2 ^ aOf n m w)) : ℕ :=
  if transOK n m w table pos s false
  then cntRec n m w table (n - (pos + 1)) (nextState (dOf n w) (eOf n m w) pos s false)
  else 0

def cnt1At (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (pos : ℕ) (s : Fin (2 ^ aOf n m w)) : ℕ :=
  if transOK n m w table pos s true
  then cntRec n m w table (n - (pos + 1)) (nextState (dOf n w) (eOf n m w) pos s true)
  else 0

lemma cntRec_le_two_pow (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) :
    ∀ (rem : ℕ) (s : Fin (2 ^ aOf n m w)), cntRec n m w table rem s ≤ 2 ^ rem
  | 0, s => by dsimp only [cntRec]; split_ifs <;> simp
  | rem + 1, s => by
    dsimp only [cntRec]
    have h0 := cntRec_le_two_pow n m w table rem (nextState (dOf n w) (eOf n m w) (n - (rem + 1)) s false)
    have h1 := cntRec_le_two_pow n m w table rem (nextState (dOf n w) (eOf n m w) (n - (rem + 1)) s true)
    rw [Nat.pow_succ]
    split_ifs <;> omega

lemma cntRec_step_eq (n m w pos : ℕ) (hpos : pos < n)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (s : Fin (2 ^ aOf n m w)) :
    cntRec n m w table (n - pos) s = cnt0At n m w table pos s + cnt1At n m w table pos s := by
  have hsub : n - pos = (n - (pos + 1)) + 1 := by omega
  have hpos_eq : n - ((n - (pos + 1)) + 1) = pos := by omega
  rw [hsub]
  dsimp only [cntRec, cnt0At, cnt1At]
  rw [hpos_eq]

def validSuffix (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (pos pref : ℕ) : Finset (Fin (2 ^ n)) :=
  (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
    z.val / 2 ^ (n - pos) = pref ∧
    (∀ p, pos ≤ p → p < n → transOK n m w table p
      (trajPrefix (dOf n w) (eOf n m w) p (z.val / 2 ^ (n - p))) (wordBit n z p) = true) ∧
    termOK n m w table (trajPrefix (dOf n w) (eOf n m w) n z.val) = true)

lemma card_validSuffix (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) :
    ∀ (rem : ℕ), rem ≤ n → ∀ (pref : ℕ), pref < 2 ^ (n - rem) →
      (validSuffix n m w table (n - rem) pref).card =
        cntRec n m w table rem (trajPrefix (dOf n w) (eOf n m w) (n - rem) pref) := by
  intro rem
  induction rem with
  | zero =>
    intro _ pref hpref
    simp only [Nat.sub_zero] at hpref ⊢
    dsimp only [cntRec]
    let z0 : Fin (2 ^ n) := ⟨pref, hpref⟩
    by_cases htm : termOK n m w table (trajPrefix (dOf n w) (eOf n m w) n pref) = true
    · simp only [htm, ↓reduceIte]
      have hsing : validSuffix n m w table n pref = {z0} := by
        ext z
        simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
                   Nat.sub_self, pow_zero, Nat.div_one, Finset.mem_singleton]
        constructor
        · rintro ⟨hz, _, _⟩; exact Fin.ext hz
        · rintro rfl; exact ⟨rfl, fun p hp1 hp2 => by omega, htm⟩
      rw [hsing, Finset.card_singleton]
    · simp only [htm, Bool.false_eq_true, ↓reduceIte]
      have hemp : validSuffix n m w table n pref = ∅ := by
        ext z
        simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
                   Nat.sub_self, pow_zero, Nat.div_one, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, _, h⟩; exact htm h
      rw [hemp, Finset.card_empty]
  | succ rem ih =>
    intro hrem pref hpref
    let pos := n - (rem + 1)
    have hpos : pos < n := by dsimp only [pos]; omega
    have hpos1 : pos + 1 = n - rem := by dsimp only [pos]; omega
    let s := trajPrefix (dOf n w) (eOf n m w) pos pref
    let S0 := (validSuffix n m w table pos pref).filter (fun z => wordBit n z pos = false)
    let S1 := (validSuffix n m w table pos pref).filter (fun z => wordBit n z pos = true)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]; intro z h0 h1
      simp only [S0, S1, Finset.mem_filter] at h0 h1
      rw [h0.2] at h1; cases h1.2
    have hun : S0 ∪ S1 = validSuffix n m w table pos pref := by
      ext z; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      cases wordBit n z pos <;> simp
    have hS0 : S0.card = if transOK n m w table pos s false = true
        then cntRec n m w table rem (nextState (dOf n w) (eOf n m w) pos s false) else 0 := by
      by_cases hok : transOK n m w table pos s false = true
      · simp only [hok, ↓reduceIte]
        have heq : S0 = validSuffix n m w table (n - rem) (2 * pref) := by
          ext z
          simp only [S0, validSuffix, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨hdiv, htr, htm⟩, hbit⟩
            have hdiv1 : z.val / 2 ^ (n - (n - rem)) = 2 * pref := by
              rw [← hpos1, div_pow_succ_step z hpos, hdiv, hbit]; simp
            exact ⟨hdiv1, fun p hp1 hp2 => htr p (by omega) hp2, htm⟩
          · rintro ⟨hdiv1, htr1, htm⟩
            have hdiv_step := div_pow_succ_step z hpos
            rw [hpos1, hdiv1] at hdiv_step
            have hdiv : z.val / 2 ^ (n - pos) = pref := by
              cases hb : wordBit n z pos <;> simp [hb] at hdiv_step <;> omega
            have hbit : wordBit n z pos = false := by
              cases hb : wordBit n z pos <;> simp [hb] at hdiv_step ⊢ <;> omega
            refine ⟨⟨hdiv, ?_, htm⟩, hbit⟩
            intro p hp1 hp2
            by_cases hpe : p = pos
            · subst hpe; rw [hdiv, hbit]; exact hok
            · exact htr1 p (by omega) hp2
        have h2pref : 2 * pref < 2 ^ (n - rem) := by
          rw [← hpos1, Nat.pow_succ]; dsimp only [pos] at hpref ⊢; omega
        rw [heq, ih (by omega) (2 * pref) h2pref]
        have hst : trajPrefix (dOf n w) (eOf n m w) (n - rem) (2 * pref) =
            nextState (dOf n w) (eOf n m w) pos s false := by
          rw [← hpos1]
          simpa using trajPrefix_step (dOf n w) (eOf n m w) pos pref false
        rw [hst]
      · simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hemp : S0 = ∅ := by
          ext z; simp only [S0, validSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
                            Finset.notMem_empty, iff_false]
          rintro ⟨⟨hdiv, htr, _⟩, hbit⟩
          have h1 := htr pos le_rfl hpos
          rw [hdiv, hbit] at h1
          exact hok h1
        rw [hemp, Finset.card_empty]
    have hS1 : S1.card = if transOK n m w table pos s true = true
        then cntRec n m w table rem (nextState (dOf n w) (eOf n m w) pos s true) else 0 := by
      by_cases hok : transOK n m w table pos s true = true
      · simp only [hok, ↓reduceIte]
        have heq : S1 = validSuffix n m w table (n - rem) (2 * pref + 1) := by
          ext z
          simp only [S1, validSuffix, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨hdiv, htr, htm⟩, hbit⟩
            have hdiv1 : z.val / 2 ^ (n - (n - rem)) = 2 * pref + 1 := by
              rw [← hpos1, div_pow_succ_step z hpos, hdiv, hbit]; simp
            exact ⟨hdiv1, fun p hp1 hp2 => htr p (by omega) hp2, htm⟩
          · rintro ⟨hdiv1, htr1, htm⟩
            have hdiv_step := div_pow_succ_step z hpos
            rw [hpos1, hdiv1] at hdiv_step
            have hdiv : z.val / 2 ^ (n - pos) = pref := by
              cases hb : wordBit n z pos <;> simp [hb] at hdiv_step <;> omega
            have hbit : wordBit n z pos = true := by
              cases hb : wordBit n z pos <;> simp [hb] at hdiv_step ⊢ <;> omega
            refine ⟨⟨hdiv, ?_, htm⟩, hbit⟩
            intro p hp1 hp2
            by_cases hpe : p = pos
            · subst hpe; rw [hdiv, hbit]; exact hok
            · exact htr1 p (by omega) hp2
        have h2pref1 : 2 * pref + 1 < 2 ^ (n - rem) := by
          rw [← hpos1, Nat.pow_succ]; dsimp only [pos] at hpref ⊢; omega
        rw [heq, ih (by omega) (2 * pref + 1) h2pref1]
        have hst : trajPrefix (dOf n w) (eOf n m w) (n - rem) (2 * pref + 1) =
            nextState (dOf n w) (eOf n m w) pos s true := by
          rw [← hpos1]
          simpa using trajPrefix_step (dOf n w) (eOf n m w) pos pref true
        rw [hst]
      · simp only [hok, Bool.false_eq_true, ↓reduceIte]
        have hemp : S1 = ∅ := by
          ext z; simp only [S1, validSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
                            Finset.notMem_empty, iff_false]
          rintro ⟨⟨hdiv, htr, _⟩, hbit⟩
          have h1 := htr pos le_rfl hpos
          rw [hdiv, hbit] at h1
          exact hok h1
        rw [hemp, Finset.card_empty]
    rw [← hun, Finset.card_union_of_disjoint hdisj, hS0, hS1]
    rfl

def unrankState (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) (rank : ℕ) :
    ℕ → ℕ × ℕ × Fin (2 ^ aOf n m w)
  | 0 => (0, rank, ⟨0, Nat.pow_pos (by omega : 0 < 2)⟩)
  | pos + 1 =>
    let cur := unrankState n m w table rank pos
    let pref := cur.1
    let rem := cur.2.1
    let st := cur.2.2
    let zc := cnt0At n m w table pos st
    let bit := decide (zc ≤ rem)
    (2 * pref + bit.toNat, if bit then rem - zc else rem, nextState (dOf n w) (eOf n m w) pos st bit)

def unrankBit (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) (rank pos : ℕ) : Bool :=
  let cur := unrankState n m w table rank pos
  decide (cnt0At n m w table pos cur.2.2 ≤ cur.2.1)

lemma unrank_invariant (n m w : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (rank : ℕ)
    (hrank : rank < ((Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
      ∀ i : Fin m, table i (fun j => wordBit n z ((i.val + j.val) % n)) = true)).card) :
    let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
      ∀ i : Fin m, table i (fun j => wordBit n z ((i.val + j.val) % n)) = true)
    ∀ pos ≤ n,
      let cur := unrankState n m w table rank pos
      let pref := cur.1
      let rem := cur.2.1
      let st := cur.2.2
      pref < 2 ^ pos ∧
      st = trajPrefix (dOf n w) (eOf n m w) pos pref ∧
      (∀ z : Fin (2 ^ n), z.val / 2 ^ (n - pos) = pref →
        (z ∈ sols ↔ z ∈ validSuffix n m w table pos pref)) ∧
      rem < cntRec n m w table (n - pos) st ∧
      (sols.filter (fun y => y.val / 2 ^ (n - pos) < pref)).card + rem = rank := by
  intro sols
  have hsols0 : validSuffix n m w table 0 0 = sols := by
    ext z
    simp only [validSuffix, sols, Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_zero,
               Nat.div_eq_of_lt z.isLt]
    rw [sols_iff_dp n m w hn hmn table z]
    constructor
    · rintro ⟨htr, htm⟩; exact ⟨fun p hp => htr p (Nat.zero_le p) hp, htm⟩
    · rintro ⟨htr, htm⟩; exact ⟨fun p _ hp => htr p hp, htm⟩
  intro pos
  induction pos with
  | zero =>
    intro _
    dsimp only [unrankState]
    refine ⟨by simp, rfl, fun z _ => by rw [hsols0], ?_, ?_⟩
    · have hc := card_validSuffix n m w table n le_rfl 0 (by simp)
      simp only [Nat.sub_self, hsols0, trajPrefix] at hc
      rw [Nat.sub_zero, ← hc]
      exact hrank
    · have hemp : sols.filter (fun y => y.val / 2 ^ (n - 0) < 0) = ∅ := by
        ext y; simp
      rw [hemp, Finset.card_empty, zero_add]
  | succ pos ih =>
    intro hle
    have hpos : pos < n := by omega
    rcases ih (by omega) with ⟨hpref_lt, hst_eq, hmatch, hrem_lt, hsum_rank⟩
    let cur := unrankState n m w table rank pos
    let pref := cur.1
    let rem := cur.2.1
    let st := cur.2.2
    let zc := cnt0At n m w table pos st
    let c1 := cnt1At n m w table pos st
    have hcnt_split : cntRec n m w table (n - pos) st = zc + c1 :=
      cntRec_step_eq n m w pos hpos table st
    change rem < cntRec n m w table (n - pos) st at hrem_lt
    rw [hcnt_split] at hrem_lt
    have hS0_eq : sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) = 2 * pref) =
        if transOK n m w table pos st false = true
        then validSuffix n m w table (pos + 1) (2 * pref) else ∅ := by
      ext y
      by_cases hok : transOK n m w table pos st false = true
      · simp only [hok, ↓reduceIte, Finset.mem_filter, validSuffix, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hyS, hdiv1⟩
          have hdiv_step := div_pow_succ_step y hpos
          rw [hdiv1] at hdiv_step
          have hdiv : y.val / 2 ^ (n - pos) = pref := by
            cases hb : wordBit n y pos <;> simp [hb] at hdiv_step <;> omega
          have hvs := (hmatch y hdiv).mp hyS
          simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and] at hvs
          exact ⟨hdiv1, fun p hp1 hp2 => hvs.2.1 p (by omega) hp2, hvs.2.2⟩
        · rintro ⟨hdiv1, htr1, htm⟩
          have hdiv_step := div_pow_succ_step y hpos
          rw [hdiv1] at hdiv_step
          have hdiv : y.val / 2 ^ (n - pos) = pref := by
            cases hb : wordBit n y pos <;> simp [hb] at hdiv_step <;> omega
          have hbit : wordBit n y pos = false := by
            cases hb : wordBit n y pos <;> simp [hb] at hdiv_step ⊢ <;> omega
          refine ⟨(hmatch y hdiv).mpr ?_, hdiv1⟩
          simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hdiv, fun p hp1 hp2 => ?_, htm⟩
          by_cases hpe : p = pos
          · subst hpe; rw [hdiv, hbit, ← hst_eq]; exact hok
          · exact htr1 p (by omega) hp2
      · simp only [hok, Bool.false_eq_true, ↓reduceIte, Finset.notMem_empty, iff_false]
        intro hmem
        rcases Finset.mem_filter.mp hmem with ⟨hyS, hdiv1⟩
        have hdiv_step := div_pow_succ_step y hpos
        rw [hdiv1] at hdiv_step
        have hdiv : y.val / 2 ^ (n - pos) = pref := by
          cases hb : wordBit n y pos <;> simp [hb] at hdiv_step <;> omega
        have hbit : wordBit n y pos = false := by
          cases hb : wordBit n y pos <;> simp [hb] at hdiv_step ⊢ <;> omega
        have hvs := (hmatch y hdiv).mp hyS
        simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and] at hvs
        have h1 := hvs.2.1 pos le_rfl hpos
        rw [hdiv, hbit, ← hst_eq] at h1
        exact hok h1
    have hS0_card : (sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) = 2 * pref)).card = zc := by
      rw [hS0_eq]
      dsimp only [zc, cnt0At]
      by_cases hok : transOK n m w table pos st false = true
      · simp only [hok, ↓reduceIte]
        have hsub : n - (n - (pos + 1)) = pos + 1 := by omega
        have h2pref : 2 * pref < 2 ^ (n - (n - (pos + 1))) := by
          rw [hsub, Nat.pow_succ]; dsimp only [pref, cur] at hpref_lt ⊢; omega
        have hc := card_validSuffix n m w table (n - (pos + 1)) (by omega) (2 * pref) h2pref
        rw [hsub] at hc
        rw [hc]
        have htr : trajPrefix (dOf n w) (eOf n m w) (pos + 1) (2 * pref) =
            nextState (dOf n w) (eOf n m w) pos st false := by
          change st = trajPrefix (dOf n w) (eOf n m w) pos pref at hst_eq
          rw [hst_eq]
          simpa using trajPrefix_step (dOf n w) (eOf n m w) pos pref false
        rw [htr]
      · simp [hok]
    have hlt_eq : sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) < 2 * pref) =
        sols.filter (fun y => y.val / 2 ^ (n - pos) < pref) := by
      ext y
      simp only [Finset.mem_filter]
      have hdiv_step := div_pow_succ_step y hpos
      constructor <;> rintro ⟨hy, hlt⟩ <;> refine ⟨hy, ?_⟩
      · cases hb : wordBit n y pos <;> simp [hb] at hdiv_step <;> omega
      · cases hb : wordBit n y pos <;> simp [hb] at hdiv_step <;> omega
    dsimp only [unrankState]
    change let p1 := 2 * pref + (decide (zc ≤ rem)).toNat
      let r1 := if decide (zc ≤ rem) then rem - zc else rem
      let s1 := nextState (dOf n w) (eOf n m w) pos st (decide (zc ≤ rem))
      p1 < 2 ^ (pos + 1) ∧ s1 = trajPrefix (dOf n w) (eOf n m w) (pos + 1) p1 ∧
      (∀ z : Fin (2 ^ n), z.val / 2 ^ (n - (pos + 1)) = p1 →
        (z ∈ sols ↔ z ∈ validSuffix n m w table (pos + 1) p1)) ∧
      r1 < cntRec n m w table (n - (pos + 1)) s1 ∧
      (sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) < p1)).card + r1 = rank
    dsimp only
    by_cases hbit : zc ≤ rem
    · have hc1_pos : 0 < c1 := by omega
      have hok1 : transOK n m w table pos st true = true := by
        dsimp only [c1, cnt1At] at hc1_pos
        by_contra hno
        simp [hno] at hc1_pos
      have hc1_eq : c1 = cntRec n m w table (n - (pos + 1)) (nextState (dOf n w) (eOf n m w) pos st true) := by
        dsimp only [c1, cnt1At]; simp [hok1]
      simp only [hbit, decide_true, Bool.toNat_true, ↓reduceIte]
      refine ⟨by rw [Nat.pow_succ]; dsimp only [pref, cur] at hpref_lt ⊢; omega, ?_, ?_, by omega, ?_⟩
      · change st = trajPrefix (dOf n w) (eOf n m w) pos pref at hst_eq
        rw [hst_eq]
        simpa using (trajPrefix_step (dOf n w) (eOf n m w) pos pref true).symm
      · intro z hdiv1
        have hdiv_step := div_pow_succ_step z hpos
        rw [hdiv1] at hdiv_step
        have hdiv : z.val / 2 ^ (n - pos) = pref := by
          cases hb : wordBit n z pos <;> simp [hb] at hdiv_step <;> omega
        have hzb : wordBit n z pos = true := by
          cases hb : wordBit n z pos <;> simp [hb] at hdiv_step ⊢ <;> omega
        rw [hmatch z hdiv]
        simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, htr, htm⟩; exact ⟨hdiv1, fun p hp1 hp2 => htr p (by omega) hp2, htm⟩
        · rintro ⟨_, htr1, htm⟩
          refine ⟨hdiv, fun p hp1 hp2 => ?_, htm⟩
          by_cases hpe : p = pos
          · subst hpe; rw [hdiv, hzb, ← hst_eq]; exact hok1
          · exact htr1 p (by omega) hp2
      · have hsplit_lt : sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) < 2 * pref + 1) =
            sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) < 2 * pref) ∪
            sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) = 2 * pref) := by
          ext y; simp only [Finset.mem_union, Finset.mem_filter]; constructor
          · rintro ⟨hy, hlt⟩
            by_cases hlt' : y.val / 2 ^ (n - (pos + 1)) < 2 * pref
            · exact Or.inl ⟨hy, hlt'⟩
            · exact Or.inr ⟨hy, by omega⟩
          · rintro (⟨hy, h⟩ | ⟨hy, h⟩) <;> exact ⟨hy, by omega⟩
        have hdisj_lt : Disjoint
            (sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) < 2 * pref))
            (sols.filter (fun y => y.val / 2 ^ (n - (pos + 1)) = 2 * pref)) := by
          rw [Finset.disjoint_left]; intro y h1 h2
          simp only [Finset.mem_filter] at h1 h2; omega
        rw [hsplit_lt, Finset.card_union_of_disjoint hdisj_lt, hlt_eq, hS0_card]
        change (sols.filter (fun y => y.val / 2 ^ (n - pos) < pref)).card + rem = rank at hsum_rank
        omega
    · have hzc_pos : 0 < zc := by omega
      have hok0 : transOK n m w table pos st false = true := by
        dsimp only [zc, cnt0At] at hzc_pos
        by_contra hno
        simp [hno] at hzc_pos
      have hzc_eq : zc = cntRec n m w table (n - (pos + 1)) (nextState (dOf n w) (eOf n m w) pos st false) := by
        dsimp only [zc, cnt0At]; simp [hok0]
      simp only [hbit, decide_false, Bool.toNat_false, add_zero, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by rw [Nat.pow_succ]; dsimp only [pref, cur] at hpref_lt ⊢; omega, ?_, ?_, by omega, ?_⟩
      · change st = trajPrefix (dOf n w) (eOf n m w) pos pref at hst_eq
        rw [hst_eq]
        simpa using (trajPrefix_step (dOf n w) (eOf n m w) pos pref false).symm
      · intro z hdiv1
        have hdiv_step := div_pow_succ_step z hpos
        rw [hdiv1] at hdiv_step
        have hdiv : z.val / 2 ^ (n - pos) = pref := by
          cases hb : wordBit n z pos <;> simp [hb] at hdiv_step <;> omega
        have hzb : wordBit n z pos = false := by
          cases hb : wordBit n z pos <;> simp [hb] at hdiv_step ⊢ <;> omega
        rw [hmatch z hdiv]
        simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, htr, htm⟩; exact ⟨hdiv1, fun p hp1 hp2 => htr p (by omega) hp2, htm⟩
        · rintro ⟨_, htr1, htm⟩
          refine ⟨hdiv, fun p hp1 hp2 => ?_, htm⟩
          by_cases hpe : p = pos
          · subst hpe; rw [hdiv, hzb, ← hst_eq]; exact hok0
          · exact htr1 p (by omega) hp2
      · rw [hlt_eq]
        exact hsum_rank

lemma unrank_pref_div (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) (rank : ℕ) :
    ∀ pos k, (unrankState n m w table rank (pos + k)).1 / 2 ^ k = (unrankState n m w table rank pos).1 := by
  intro pos k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (unrankState n m w table rank (pos + (k + 1))).1 =
        2 * (unrankState n m w table rank (pos + k)).1 + (unrankBit n m w table rank (pos + k)).toNat := by
      rw [← Nat.add_assoc]; rfl
    rw [hstep, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    have hd2 : (2 * (unrankState n m w table rank (pos + k)).1 +
        (unrankBit n m w table rank (pos + k)).toNat) / 2 =
        (unrankState n m w table rank (pos + k)).1 := by
      cases unrankBit n m w table rank (pos + k) <;> simp <;> omega
    rw [hd2, ih]

lemma unrank_spec (n m w : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (table : Fin m → (Fin (w + 1) → Bool) → Bool) (rank : ℕ)
    (hrank : rank < ((Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
      ∀ i : Fin m, table i (fun j => wordBit n z ((i.val + j.val) % n)) = true)).card) :
    let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
      ∀ i : Fin m, table i (fun j => wordBit n z ((i.val + j.val) % n)) = true)
    ∃ z ∈ sols,
      (sols.filter (fun y => y.val < z.val)).card = rank ∧
      ∀ j : Fin n, unrankBit n m w table rank j.val = z.val.testBit (n - 1 - j.val) := by
  intro sols
  have hinv := unrank_invariant n m w hn hmn table rank hrank n le_rfl
  rcases hinv with ⟨hpref_lt, hst_eq, hmatch, hrem_lt, hsum_rank⟩
  let prefN := (unrankState n m w table rank n).1
  let z : Fin (2 ^ n) := ⟨prefN, hpref_lt⟩
  have hcnt_le1 : cntRec n m w table (n - n) (unrankState n m w table rank n).2.2 ≤ 1 := by
    simpa using cntRec_le_two_pow n m w table 0 (unrankState n m w table rank n).2.2
  have hrem0 : (unrankState n m w table rank n).2.1 = 0 := by omega
  have htm_ok : termOK n m w table (unrankState n m w table rank n).2.2 = true := by
    simp only [Nat.sub_self, cntRec] at hrem_lt
    by_contra hno
    simp [hno] at hrem_lt
  have hz_mem : z ∈ sols := by
    rw [hmatch z (by simp [z, pow_zero, Nat.div_one]; rfl)]
    simp only [validSuffix, Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_self,
               pow_zero, Nat.div_one]
    refine ⟨rfl, fun p hp1 hp2 => by omega, ?_⟩
    rw [← hst_eq]
    exact htm_ok
  refine ⟨z, hz_mem, ?_, ?_⟩
  · simp only [Nat.sub_self, pow_zero, Nat.div_one, hrem0, add_zero] at hsum_rank
    exact hsum_rank
  · intro j
    have hdiv1 : z.val / 2 ^ (n - (j.val + 1)) = (unrankState n m w table rank (j.val + 1)).1 := by
      have heq : (j.val + 1) + (n - (j.val + 1)) = n := by omega
      have hd := unrank_pref_div n m w table rank (j.val + 1) (n - (j.val + 1))
      rw [heq] at hd
      exact hd
    have hdiv0 : z.val / 2 ^ (n - j.val) = (unrankState n m w table rank j.val).1 := by
      have heq : j.val + (n - j.val) = n := by omega
      have hd := unrank_pref_div n m w table rank j.val (n - j.val)
      rw [heq] at hd
      exact hd
    have hstep := div_pow_succ_step z j.isLt
    rw [hdiv1, hdiv0] at hstep
    have hrstep : (unrankState n m w table rank (j.val + 1)).1 =
        2 * (unrankState n m w table rank j.val).1 + (unrankBit n m w table rank j.val).toNat := rfl
    rw [hrstep] at hstep
    cases hb1 : unrankBit n m w table rank j.val <;>
      cases hb2 : wordBit n z j.val <;> simp [hb1, hb2] at hstep ⊢

lemma unrankState_rem_le (n m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) (rank : ℕ) :
    ∀ pos, (unrankState n m w table rank pos).2.1 ≤ rank
  | 0 => le_rfl
  | pos + 1 => by
    have ih := unrankState_rem_le n m w table rank pos
    dsimp only [unrankState]
    split_ifs <;> omega

lemma buildFinLoop {I N : ℕ} {Out : Fin N → Type} {cost : Fin N → ℕ}
    {P : ∀ k : Fin N, Builder I → Out k → Prop}
    (hP_ext : ∀ k b1 b2 o, Extends b1 b2 → P k b1 o → P k b2 o)
    (step : ∀ (k : Fin N) (b : Builder I),
      ∃ (b' : Builder I) (o : Out k), Extends b b' ∧ b'.size ≤ b.size + cost k ∧ P k b' o)
    (b0 : Builder I) :
    ∃ (b' : Builder I) (outs : ∀ k : Fin N, Out k),
      Extends b0 b' ∧ b'.size ≤ b0.size + ∑ k : Fin N, cost k ∧ ∀ k, P k b' (outs k) := by
  induction N generalizing b0 with
  | zero =>
    refine ⟨b0, fun k => Fin.elim0 k, Extends.refl b0, by simp, fun k => Fin.elim0 k⟩
  | succ N ih =>
    obtain ⟨b1, outs1, h1, hs1, hP1⟩ :=
      @ih (fun k => Out k.castSucc) (fun k => cost k.castSucc)
        (fun k => P k.castSucc) (fun k => hP_ext k.castSucc) (fun k => step k.castSucc) b0
    obtain ⟨b2, oLast, h2, hs2, hPLast⟩ := step (Fin.last N) b1
    let outs : ∀ k : Fin (N + 1), Out k := fun k =>
      Fin.lastCases oLast outs1 k
    refine ⟨b2, outs, h1.trans h2, ?_, ?_⟩
    · rw [Fin.sum_univ_castSucc]; omega
    · intro k
      refine Fin.lastCases ?_ ?_ k
      · simpa [outs] using hPLast
      · intro k'
        simpa [outs] using hP_ext k'.castSucc b1 b2 (outs1 k') h2 (hP1 k')

def xOf (m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) : List Bool :=
  (List.ofFn (fun i : Fin m => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
    table i (fun j => p.val.testBit j.val)))).flatten

lemma xOf_length (m w : ℕ) (table : Fin m → (Fin (w + 1) → Bool) → Bool) :
    (xOf m w table).length = m * 2 ^ (w + 1) :=
  flatten_ofFn_length _

lemma xOf_evalWire_pat {m w : ℕ} (b : Builder (m * 2 ^ (w + 1)))
    (table : Fin m → (Fin (w + 1) → Bool) → Bool)
    (i : Fin m) (pat : Fin (w + 1) → Bool) :
    evalWire b.gates (xOf m w table) (i.val * 2 ^ (w + 1) + (patCode w pat).val) = table i pat := by
  have hlt : i.val * 2 ^ (w + 1) + (patCode w pat).val < (xOf m w table).length := by
    rw [xOf_length]
    have h1 := i.isLt
    have h2 := (patCode w pat).isLt
    have hmul : (i.val + 1) * 2 ^ (w + 1) ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, one_mul] at hmul
    omega
  unfold evalWire
  rw [wires_prefix_getD b.gates (xOf m w table) _ hlt]
  unfold xOf
  rw [flatten_ofFn_getD]
  congr 1
  funext j
  exact patCode_testBit w pat j

lemma patWire_lt {m w : ℕ} (i : Fin m) (pat : Fin (w + 1) → Bool) :
    i.val * 2 ^ (w + 1) + (patCode w pat).val < m * 2 ^ (w + 1) := by
  have h1 := i.isLt
  have h2 := (patCode w pat).isLt
  have hmul : (i.val + 1) * 2 ^ (w + 1) ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, one_mul] at hmul
  omega

lemma buildLookup049 {I a B q : ℕ} (b : Builder I)
    (tableW : Fin (2 ^ a) → Fin B → ℕ) (htab : ∀ s j, tableW s j < I + b.size)
    (addrW : Fin q → Fin a → ℕ) (haddr : ∀ r i, addrW r i < I + b.size) :
    ∃ (b' : Builder I) (outW : Fin q → Fin B → ℕ),
      Extends b b' ∧
      b'.size ≤ b.size + 128 * (2 ^ a + q) * (a + B + Nat.log2 (q + 1) + 3) ^ 3 ∧
      (∀ r j, outW r j < I + b'.size) ∧
      ∀ (x : List Bool), x.length = I →
        ∀ (r : Fin q) (j : Fin B),
          let addr : Fin (2 ^ a) :=
            ⟨bitsVal (fun i => if h : i < a then evalWire b.gates x (addrW r ⟨i, h⟩) else false) a,
             bitsVal_lt _ _⟩
          evalWire b'.gates x (outW r j) = evalWire b.gates x (tableW addr j) := by
  obtain ⟨sub, outBit, hFan, hRB, _, hSize, hSpec⟩ := PEqualNP.Outside.L_clb_049 a B q
  let words := 2 ^ a
  let Isub := words * B + q * a
  let inpMap : Fin Isub → ℕ := fun k =>
    if h : k.val < words * B then
      have hB : 0 < B := by
        by_contra h0; simp only [not_lt, Nat.le_zero] at h0; rw [h0, mul_zero] at h; omega
      tableW ⟨k.val / B, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h)⟩ ⟨k.val % B, Nat.mod_lt _ hB⟩
    else
      have ha : 0 < a := by
        by_contra h0; simp only [not_lt, Nat.le_zero] at h0
        have hk := k.isLt; dsimp only [Isub] at hk; simp [h0] at hk; omega
      let rem := k.val - words * B
      have hrem : rem < q * a := by have hk := k.isLt; dsimp only [Isub] at hk; omega
      addrW ⟨rem / a, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hrem)⟩ ⟨rem % a, Nat.mod_lt _ ha⟩
  have hinp : ∀ k : Fin Isub, inpMap k < I + b.size := by
    intro k; dsimp only [inpMap]
    by_cases h : k.val < words * B
    · simp only [h, ↓reduceDIte]; exact htab _ _
    · simp only [h, ↓reduceDIte]; exact haddr _ _
  obtain ⟨b', hext, hsize, hsplice⟩ := spliceSub_exists b sub hFan hRB inpMap hinp
  let outW : Fin q → Fin B → ℕ := fun r j =>
    let w := (outBit r j).val
    if h : w < Isub then inpMap ⟨w, h⟩ else (I + b.size) + (w - Isub)
  refine ⟨b', outW, hext, by omega, ?_, ?_⟩
  · intro r j
    dsimp only [outW]
    have hsp := hsplice (List.replicate I false) (by simp) (outBit r j).val (outBit r j).isLt
    exact hsp.1
  · intro x hx r j
    dsimp only
    let tabFn : Fin words → Fin B → Bool := fun s i => evalWire b.gates x (tableW s i)
    let addrFn : Fin q → Fin words := fun r' =>
      ⟨bitsVal (fun i => if h : i < a then evalWire b.gates x (addrW r' ⟨i, h⟩) else false) a,
       bitsVal_lt _ _⟩
    let xL := (List.ofFn (fun s : Fin words => List.ofFn (tabFn s))).flatten ++
      (List.ofFn (fun r' : Fin q =>
        List.ofFn (fun i : Fin a => (addrFn r').val.testBit i.val))).flatten
    have hx_eq : List.ofFn (fun k : Fin Isub => evalWire b.gates x (inpMap k)) = xL := by
      have hlenR : xL.length = Isub := by
        dsimp only [xL, Isub]
        rw [List.length_append, flatten_ofFn_length, flatten_ofFn_length]
      apply List.ext_getElem (by rw [List.length_ofFn, hlenR])
      intro idx h1 h2
      rw [List.getElem_ofFn]
      have hidx : idx < Isub := by simpa using h1
      dsimp only [inpMap]
      by_cases hlt : idx < words * B
      · simp only [hlt, ↓reduceDIte]
        have hB : 0 < B := by
          by_contra h0; simp only [not_lt, Nat.le_zero] at h0; rw [h0, mul_zero] at hlt; omega
        have hget : xL[idx] = xL.getD idx false := (List.getD_eq_getElem xL false h2).symm
        rw [hget]
        dsimp only [xL]
        rw [List.getD_append _ _ _ _ (by rw [flatten_ofFn_length]; exact hlt)]
        have hdm : (idx / B) * B + idx % B = idx := by
          have := Nat.div_add_mod idx B; rw [mul_comm] at this; exact this
        have hfd := flatten_ofFn_getD tabFn
          ⟨idx / B, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt)⟩
          ⟨idx % B, Nat.mod_lt _ hB⟩
        simpa only [hdm] using hfd.symm
      · simp only [hlt, ↓reduceDIte]
        have ha : 0 < a := by
          by_contra h0; simp only [not_lt, Nat.le_zero] at h0
          dsimp only [Isub] at hidx; rw [h0, mul_zero, add_zero] at hidx; omega
        have hget : xL[idx] = xL.getD idx false := (List.getD_eq_getElem xL false h2).symm
        rw [hget]
        dsimp only [xL]
        rw [List.getD_append_right _ _ _ _ (by rw [flatten_ofFn_length]; omega)]
        rw [flatten_ofFn_length]
        let rem := idx - words * B
        have hrem : rem < q * a := by dsimp only [Isub] at hidx; omega
        have hdm : (rem / a) * a + rem % a = rem := by
          have := Nat.div_add_mod rem a; rw [mul_comm] at this; exact this
        have hfd := flatten_ofFn_getD
          (fun r' : Fin q => fun i : Fin a => (addrFn r').val.testBit i.val)
          ⟨rem / a, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hrem)⟩
          ⟨rem % a, Nat.mod_lt _ ha⟩
        dsimp only [rem] at hdm hfd
        rw [hdm] at hfd
        rw [hfd]
        dsimp only [addrFn]
        rw [bitsVal_testBit]
        simp [Nat.mod_lt (idx - words * B) ha]
    have hsp := (hsplice x hx (outBit r j).val (outBit r j).isLt).2
    rw [hx_eq] at hsp
    change evalWire b'.gates x (outW r j) = tabFn (addrFn r) j
    rw [hsp]
    exact hSpec tabFn addrFn r j

lemma buildConstraints {n m w : ℕ} (hn : 0 < n) (b0 : Builder (m * 2 ^ (w + 1)))
    (cTrue : ℕ) (hcT : cTrue < m * 2 ^ (w + 1) + b0.size)
    (hcT_val : ∀ table, evalWire b0.gates (xOf m w table) cTrue = true) :
    let I := m * 2 ^ (w + 1)
    let a := aOf n m w
    ∃ (b' : Builder I)
      (transW : Fin n → Fin (2 ^ a) → Bool → ℕ)
      (termW : Fin (2 ^ a) → ℕ),
      Extends b0 b' ∧
      b'.size ≤ b0.size + 2 * m * 2 ^ a ∧
      (∀ pos s bit, transW pos s bit < I + b'.size) ∧
      (∀ s, termW s < I + b'.size) ∧
      ∀ table,
        (∀ pos s bit, evalWire b'.gates (xOf m w table) (transW pos s bit) =
          transOK n m w table pos.val s bit) ∧
        (∀ s, evalWire b'.gates (xOf m w table) (termW s) = termOK n m w table s) := by
  intro I a
  have htrans_all : ∃ (b1 : Builder I) (transW : Fin n → Fin (2 ^ a) → Bool → ℕ),
      Extends b0 b1 ∧
      b1.size ≤ b0.size + ∑ pos : Fin n, 2 ^ a * (2 * (transList n m w pos.val).length) ∧
      (∀ pos s bit, transW pos s bit < I + b1.size) ∧
      (∀ table pos s bit, evalWire b1.gates (xOf m w table) (transW pos s bit) =
        transOK n m w table pos.val s bit) := by
    let P_pos : Fin n → Builder I → (Fin (2 ^ a) → Bool → ℕ) → Prop := fun pos b f =>
      (∀ s bit, f s bit < I + b.size) ∧
      ∀ table s bit, evalWire b.gates (xOf m w table) (f s bit) = transOK n m w table pos.val s bit
    have hP_ext : ∀ pos b1 b2 f, Extends b1 b2 → P_pos pos b1 f → P_pos pos b2 f := by
      intro pos b1 b2 f hext ⟨hbnd, hev⟩
      exact ⟨fun s bit => hext.bound (hbnd s bit), fun table s bit => by
        rw [hext.eval_eq (xOf m w table) (xOf_length m w table) (hbnd s bit), hev]⟩
    have hstep_pos : ∀ (pos : Fin n) (b : Builder I),
        Extends b0 b →
        ∃ (b' : Builder I) (f : Fin (2 ^ a) → Bool → ℕ),
          Extends b b' ∧ b'.size ≤ b.size + 2 ^ a * (2 * (transList n m w pos.val).length) ∧
          P_pos pos b' f := by
      intro pos b hb0
      let P_s : Fin (2 ^ a) → Builder I → (Bool → ℕ) → Prop := fun s b' f =>
        (∀ bit, f bit < I + b'.size) ∧
        ∀ table bit, evalWire b'.gates (xOf m w table) (f bit) = transOK n m w table pos.val s bit
      have hPs_ext : ∀ s b1 b2 f, Extends b1 b2 → P_s s b1 f → P_s s b2 f := by
        intro s b1 b2 f hext ⟨hbnd, hev⟩
        exact ⟨fun bit => hext.bound (hbnd bit), fun table bit => by
          rw [hext.eval_eq (xOf m w table) (xOf_length m w table) (hbnd bit), hev]⟩
      have hstep_s : ∀ (s : Fin (2 ^ a)) (bs : Builder I),
          Extends b0 bs →
          ∃ (bs' : Builder I) (f : Bool → ℕ),
            Extends bs bs' ∧ bs'.size ≤ bs.size + 2 * (transList n m w pos.val).length ∧ P_s s bs' f := by
        intro s bs hbs0
        let wsF := (transList n m w pos.val).map (fun i => i.val * 2 ^ (w + 1) + (patCode w (transPat n m w pos.val s false i)).val)
        have hwsF : ∀ u ∈ wsF, u < I + bs.size := by
          intro u hu; rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
          exact lt_of_lt_of_le (patWire_lt i _) (Nat.le_add_right _ _)
        obtain ⟨bs1, wF, h1, hs1, hwF, hevF⟩ := mkAndList_exists bs cTrue (hbs0.bound hcT) wsF hwsF
        let wsT := (transList n m w pos.val).map (fun i => i.val * 2 ^ (w + 1) + (patCode w (transPat n m w pos.val s true i)).val)
        have hwsT : ∀ u ∈ wsT, u < I + bs1.size := by
          intro u hu; rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
          exact lt_of_lt_of_le (patWire_lt i _) (Nat.le_add_right _ _)
        obtain ⟨bs2, wT, h2, hs2, hwT, hevT⟩ := mkAndList_exists bs1 cTrue ((hbs0.trans h1).bound hcT) wsT hwsT
        refine ⟨bs2, fun bit => if bit then wT else wF, h1.trans h2, ?_, ?_, ?_⟩
        · have hlf : wsF.length = (transList n m w pos.val).length := List.length_map _
          have hlt : wsT.length = (transList n m w pos.val).length := List.length_map _
          omega
        · intro bit; cases bit
          · exact h2.bound hwF
          · exact hwT
        · intro table bit
          have hcT_bs : evalWire bs.gates (xOf m w table) cTrue = true := by
            rw [hbs0.eval_eq (xOf m w table) (xOf_length m w table) hcT]; exact hcT_val table
          have hcT_bs1 : evalWire bs1.gates (xOf m w table) cTrue = true := by
            rw [(hbs0.trans h1).eval_eq (xOf m w table) (xOf_length m w table) hcT]; exact hcT_val table
          cases bit
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [h2.eval_eq (xOf m w table) (xOf_length m w table) hwF]
            apply Bool.eq_iff_iff.mpr
            rw [hevF (xOf m w table) (xOf_length m w table) hcT_bs, transOK, List.all_eq_true]
            constructor
            · intro h i hi
              have h1 := h _ (List.mem_map_of_mem hi)
              rwa [xOf_evalWire_pat] at h1
            · intro h u hu
              rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
              rw [xOf_evalWire_pat]; exact h i hi
          · simp only [↓reduceIte]
            apply Bool.eq_iff_iff.mpr
            rw [hevT (xOf m w table) (xOf_length m w table) hcT_bs1, transOK, List.all_eq_true]
            constructor
            · intro h i hi
              have h1 := h _ (List.mem_map_of_mem hi)
              rwa [xOf_evalWire_pat] at h1
            · intro h u hu
              rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
              rw [xOf_evalWire_pat]; exact h i hi

      let P_s' : Fin (2 ^ a) → Builder I → (Bool → ℕ) → Prop := fun s b' f =>
        Extends b0 b' ∧ P_s s b' f

      have hloop : ∀ (N : ℕ) (hN : N ≤ 2 ^ a),
          ∃ (b' : Builder I) (f : Fin N → Bool → ℕ),
            Extends b b' ∧ b'.size ≤ b.size + N * (2 * (transList n m w pos.val).length) ∧
            ∀ (s : Fin N), P_s ⟨s.val, lt_of_lt_of_le s.isLt hN⟩ b' (f s) := by
        intro N
        induction N with
        | zero =>
          intro _
          exact ⟨b, fun s => Fin.elim0 s, Extends.refl b, by simp, fun s => Fin.elim0 s⟩
        | succ N ih =>
          intro hN
          obtain ⟨b1, f1, h1, hs1, hP1⟩ := ih (by omega)
          obtain ⟨b2, fLast, h2, hs2, hPLast⟩ :=
            hstep_s ⟨N, hN⟩ b1 (hb0.trans h1)
          refine ⟨b2, fun s => Fin.lastCases fLast f1 s, h1.trans h2, ?_, ?_⟩
          · rw [Nat.add_mul, one_mul]; omega
          · intro s
            refine Fin.lastCases ?_ ?_ s
            · simpa using hPLast
            · intro s'
              simpa using hPs_ext ⟨s'.val, by omega⟩ b1 b2 (f1 s') h2 (hP1 s')
      obtain ⟨b', f, hext, hsize, hP⟩ := hloop (2 ^ a) le_rfl
      exact ⟨b', f, hext, hsize, fun s bit => (hP s).1 bit, fun table s bit => (hP s).2 table bit⟩
    have hloop_pos : ∀ (N : ℕ) (hN : N ≤ n),
        ∃ (b1 : Builder I) (f : Fin N → Fin (2 ^ a) → Bool → ℕ),
          Extends b0 b1 ∧
          b1.size ≤ b0.size + ∑ pos : Fin N, 2 ^ a * (2 * (transList n m w pos.val).length) ∧
          ∀ pos : Fin N, P_pos ⟨pos.val, lt_of_lt_of_le pos.isLt hN⟩ b1 (f pos) := by
      intro N
      induction N with
      | zero =>
        intro _
        exact ⟨b0, fun pos => Fin.elim0 pos, Extends.refl b0, by simp, fun pos => Fin.elim0 pos⟩
      | succ N ih =>
        intro hN
        obtain ⟨b1, f1, h1, hs1, hP1⟩ := ih (by omega)
        obtain ⟨b2, fLast, h2, hs2, hPLast⟩ := hstep_pos ⟨N, hN⟩ b1 h1
        refine ⟨b2, fun pos => Fin.lastCases fLast f1 pos, h1.trans h2, ?_, ?_⟩
        · rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
          dsimp only at hs2; omega
        · intro pos
          refine Fin.lastCases ?_ ?_ pos
          · simpa using hPLast
          · intro pos'
            simpa using hP_ext ⟨pos'.val, by omega⟩ b1 b2 (f1 pos') h2 (hP1 pos')
    obtain ⟨b1, f, h1, hs1, hP1⟩ := hloop_pos n le_rfl
    exact ⟨b1, f, h1, hs1, fun pos s bit => (hP1 pos).1 s bit, fun table pos s bit => (hP1 pos).2 table s bit⟩
  obtain ⟨b1, transW, h01, hs1, htr_bnd, htr_ev⟩ := htrans_all
  have hterm_all : ∃ (b2 : Builder I) (termW : Fin (2 ^ a) → ℕ),
      Extends b1 b2 ∧
      b2.size ≤ b1.size + 2 ^ a * (termList n m w).length ∧
      (∀ s, termW s < I + b2.size) ∧
      (∀ table s, evalWire b2.gates (xOf m w table) (termW s) = termOK n m w table s) := by
    let P_t : Fin (2 ^ a) → Builder I → ℕ → Prop := fun s b w' =>
      w' < I + b.size ∧ ∀ table, evalWire b.gates (xOf m w table) w' = termOK n m w table s
    have hPt_ext : ∀ s ba bb w', Extends ba bb → P_t s ba w' → P_t s bb w' := by
      intro s ba bb w' hext ⟨hbnd, hev⟩
      exact ⟨hext.bound hbnd, fun table => by
        rw [hext.eval_eq (xOf m w table) (xOf_length m w table) hbnd, hev]⟩
    have hloop : ∀ (N : ℕ) (hN : N ≤ 2 ^ a),
        ∃ (b2 : Builder I) (f : Fin N → ℕ),
          Extends b1 b2 ∧ b2.size ≤ b1.size + N * (termList n m w).length ∧
          ∀ s : Fin N, P_t ⟨s.val, lt_of_lt_of_le s.isLt hN⟩ b2 (f s) := by
      intro N
      induction N with
      | zero =>
        intro _
        exact ⟨b1, fun s => Fin.elim0 s, Extends.refl b1, by simp, fun s => Fin.elim0 s⟩
      | succ N ih =>
        intro hN
        obtain ⟨ba, fa, ha, hsa, hPa⟩ := ih (by omega)
        let s : Fin (2 ^ a) := ⟨N, hN⟩
        let ws := (termList n m w).map (fun i => i.val * 2 ^ (w + 1) + (patCode w (termPat n m w s i)).val)
        have hws : ∀ u ∈ ws, u < I + ba.size := by
          intro u hu; rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
          exact lt_of_lt_of_le (patWire_lt i _) (Nat.le_add_right _ _)
        obtain ⟨bb, wLast, hb, hsb, hwLast, hevLast⟩ :=
          mkAndList_exists ba cTrue ((h01.trans ha).bound hcT) ws hws
        refine ⟨bb, fun k => Fin.lastCases wLast fa k, ha.trans hb, ?_, ?_⟩
        · have hl : ws.length = (termList n m w).length := List.length_map _
          rw [Nat.add_mul, one_mul]; omega
        · intro k
          refine Fin.lastCases ?_ ?_ k
          · refine ⟨by simpa using hwLast, fun table => ?_⟩
            have hcT_ba : evalWire ba.gates (xOf m w table) cTrue = true := by
              rw [(h01.trans ha).eval_eq (xOf m w table) (xOf_length m w table) hcT]; exact hcT_val table
            apply Bool.eq_iff_iff.mpr
            simpa only [Fin.lastCases_last] using (by
              rw [hevLast (xOf m w table) (xOf_length m w table) hcT_ba, termOK, List.all_eq_true]
              constructor
              · intro h i hi
                have h1 := h _ (List.mem_map_of_mem hi)
                rwa [xOf_evalWire_pat] at h1
              · intro h u hu
                rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
                rw [xOf_evalWire_pat]; exact h i hi)
          · intro k'
            simpa using hPt_ext ⟨k'.val, by omega⟩ ba bb (fa k') hb (hPa k')
    obtain ⟨b2, f, h2, hs2, hP2⟩ := hloop (2 ^ a) le_rfl
    exact ⟨b2, f, h2, hs2, fun s => (hP2 s).1, fun table s => (hP2 s).2 table⟩
  obtain ⟨b2, termW, h12, hs2, htm_bnd, htm_ev⟩ := hterm_all
  refine ⟨b2, transW, termW, h01.trans h12, ?_, fun pos s bit => h12.bound (htr_bnd pos s bit), htm_bnd, ?_⟩
  · have hsum_m := sum_trans_term_len n m w hn
    have hfac : (∑ pos : Fin n, 2 ^ a * (2 * (transList n m w pos.val).length)) +
        2 ^ a * (termList n m w).length =
        2 ^ a * (2 * (∑ pos : Fin n, (transList n m w pos.val).length) + (termList n m w).length) := by
      rw [Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    have hle_2m : 2 ^ a * (2 * (∑ pos : Fin n, (transList n m w pos.val).length) + (termList n m w).length) ≤
        2 * m * 2 ^ a := by
      have h1 : 2 * (∑ pos : Fin n, (transList n m w pos.val).length) + (termList n m w).length ≤ 2 * m := by omega
      calc 2 ^ a * (2 * (∑ pos : Fin n, (transList n m w pos.val).length) + (termList n m w).length)
          ≤ 2 ^ a * (2 * m) := Nat.mul_le_mul_left _ h1
        _ = 2 * m * 2 ^ a := by ring
    omega
  · intro table
    refine ⟨fun pos s bit => ?_, fun s => htm_ev table s⟩
    rw [h12.eval_eq (xOf m w table) (xOf_length m w table) (htr_bnd pos s bit)]
    exact htr_ev table pos s bit

lemma buildDp {n m w : ℕ} (b0 : Builder (m * 2 ^ (w + 1)))
    (cFalse : ℕ) (hcF : cFalse < m * 2 ^ (w + 1) + b0.size)
    (hcF_val : ∀ table, evalWire b0.gates (xOf m w table) cFalse = false)
    (transW : Fin n → Fin (2 ^ aOf n m w) → Bool → ℕ)
    (htr_bnd : ∀ pos s bit, transW pos s bit < m * 2 ^ (w + 1) + b0.size)
    (htr_ev : ∀ table pos s bit, evalWire b0.gates (xOf m w table) (transW pos s bit) =
      transOK n m w table pos.val s bit)
    (termW : Fin (2 ^ aOf n m w) → ℕ)
    (htm_bnd : ∀ s, termW s < m * 2 ^ (w + 1) + b0.size)
    (htm_ev : ∀ table s, evalWire b0.gates (xOf m w table) (termW s) = termOK n m w table s) :
    let I := m * 2 ^ (w + 1)
    let a := aOf n m w
    ∀ (rem : ℕ), rem ≤ n →
      ∃ (b' : Builder I)
        (cntW : Fin (2 ^ a) → Fin (n + 1) → ℕ)
        (c0W : Fin rem → Fin (2 ^ a) → Fin (n + 1) → ℕ),
        Extends b0 b' ∧
        b'.size ≤ b0.size + rem * (14 * (n + 1) * 2 ^ a) ∧
        (∀ s j, cntW s j < I + b'.size) ∧
        (∀ r s j, c0W r s j < I + b'.size) ∧
        ∀ table,
          (∀ s j, evalWire b'.gates (xOf m w table) (cntW s j) =
            (cntRec n m w table rem s).testBit j.val) ∧
          (∀ (r : Fin rem) s j, evalWire b'.gates (xOf m w table) (c0W r s j) =
            (cnt0At n m w table (n - (r.val + 1)) s).testBit j.val) := by
  intro I a rem
  induction rem with
  | zero =>
    intro _
    let cntW : Fin (2 ^ a) → Fin (n + 1) → ℕ := fun s j => if j.val = 0 then termW s else cFalse
    refine ⟨b0, cntW, fun r => Fin.elim0 r, Extends.refl b0, by simp, ?_, fun r => Fin.elim0 r, ?_⟩
    · intro s j; dsimp only [cntW]; split_ifs
      · exact htm_bnd s
      · exact hcF
    · intro table
      refine ⟨fun s j => ?_, fun r => Fin.elim0 r⟩
      dsimp only [cntW, cntRec]
      rw [← htm_ev table s]
      cases htv : evalWire b0.gates (xOf m w table) (termW s)
      · by_cases hj0 : j.val = 0
        · simp [hj0, htv]
        · simp [hj0, hcF_val table]
      · by_cases hj0 : j.val = 0
        · simp [hj0, htv]
        · simp only [hj0, ↓reduceIte, hcF_val table]
          have hgt : 1 ≤ j.val := by omega
          exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
            (Nat.pow_le_pow_right (by omega) hgt))).symm
  | succ rem ih =>
    intro hrem
    obtain ⟨b1, cnt1, c0_1, h01, hs1, hcnt1_bnd, hc01_bnd, hspec1⟩ := ih (by omega)
    let pos : Fin n := ⟨n - (rem + 1), by omega⟩
    let P_s : Fin (2 ^ a) → Builder I → ((Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ)) → Prop :=
      fun s b' pair =>
        (∀ j, pair.1 j < I + b'.size) ∧ (∀ j, pair.2 j < I + b'.size) ∧
        ∀ table j,
          evalWire b'.gates (xOf m w table) (pair.1 j) = (cntRec n m w table (rem + 1) s).testBit j.val ∧
          evalWire b'.gates (xOf m w table) (pair.2 j) = (cnt0At n m w table pos.val s).testBit j.val
    have hPs_ext : ∀ s ba bb pair, Extends ba bb → P_s s ba pair → P_s s bb pair := by
      intro s ba bb pair hext ⟨h1, h2, hev⟩
      refine ⟨fun j => hext.bound (h1 j), fun j => hext.bound (h2 j), fun table j => ?_⟩
      rw [hext.eval_eq (xOf m w table) (xOf_length m w table) (h1 j),
          hext.eval_eq (xOf m w table) (xOf_length m w table) (h2 j)]
      exact hev table j
    have hstep_s : ∀ (s : Fin (2 ^ a)) (bs : Builder I),
        Extends b1 bs →
        ∃ (bs' : Builder I) (pair : (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ)),
          Extends bs bs' ∧ bs'.size ≤ bs.size + 14 * (n + 1) ∧ P_s s bs' pair := by
      intro s bs h1s
      let s0 := nextState (dOf n w) (eOf n m w) pos.val s false
      let s1 := nextState (dOf n w) (eOf n m w) pos.val s true
      obtain ⟨bs1, w0, hs01, hsz1, hw0_bnd, hw0_ev⟩ :=
        mkMaskVec_exists bs (transW pos s false) ((h01.trans h1s).bound (htr_bnd pos s false))
          (cnt1 s0) (fun j => h1s.bound (hcnt1_bnd s0 j))
      obtain ⟨bs2, w1, hs12, hsz2, hw1_bnd, hw1_ev⟩ :=
        mkMaskVec_exists bs1 (transW pos s true) ((h01.trans (h1s.trans hs01)).bound (htr_bnd pos s true))
          (cnt1 s1) (fun j => (h1s.trans hs01).bound (hcnt1_bnd s1 j))
      obtain ⟨bs3, wSum, coutW, hs23, hsz3, hwSum_bnd, _, hwSum_ev⟩ :=
        mkAddVec_exists bs2 cFalse ((h01.trans (h1s.trans (hs01.trans hs12))).bound hcF)
          w0 w1 (fun j => hs12.bound (hw0_bnd j)) hw1_bnd
      refine ⟨bs3, (wSum, w0), hs01.trans (hs12.trans hs23), by omega,
              hwSum_bnd, fun j => (hs12.trans hs23).bound (hw0_bnd j), fun table j => ?_⟩
      have hc0_eq : ∀ r : Fin (n + 1),
          evalWire bs2.gates (xOf m w table) (w0 r) = (cnt0At n m w table pos.val s).testBit r.val := by
        intro r
        rw [hs12.eval_eq (xOf m w table) (xOf_length m w table) (hw0_bnd r),
            hw0_ev (xOf m w table) (xOf_length m w table) r,
            (h01.trans h1s).eval_eq (xOf m w table) (xOf_length m w table) (htr_bnd pos s false),
            h1s.eval_eq (xOf m w table) (xOf_length m w table) (hcnt1_bnd s0 r),
            htr_ev table pos s false, (hspec1 table).1 s0 r]
        dsimp only [cnt0At, s0]
        have hsub : n - (pos.val + 1) = rem := by dsimp only [pos]; omega
        rw [hsub]
        cases transOK n m w table pos.val s false <;> simp
      have hc1_eq : ∀ r : Fin (n + 1),
          evalWire bs2.gates (xOf m w table) (w1 r) = (cnt1At n m w table pos.val s).testBit r.val := by
        intro r
        rw [hw1_ev (xOf m w table) (xOf_length m w table) r,
            (h01.trans (h1s.trans hs01)).eval_eq (xOf m w table) (xOf_length m w table) (htr_bnd pos s true),
            (h1s.trans hs01).eval_eq (xOf m w table) (xOf_length m w table) (hcnt1_bnd s1 r),
            htr_ev table pos s true, (hspec1 table).1 s1 r]
        dsimp only [cnt1At, s1]
        have hsub : n - (pos.val + 1) = rem := by dsimp only [pos]; omega
        rw [hsub]
        cases transOK n m w table pos.val s true <;> simp
      have hc0_lt : cnt0At n m w table pos.val s < 2 ^ (n + 1) := by
        have h1 : cnt0At n m w table pos.val s ≤ 2 ^ rem := by
          dsimp only [cnt0At]
          have hsub : n - (pos.val + 1) = rem := by dsimp only [pos]; omega
          rw [hsub]
          split_ifs
          · exact cntRec_le_two_pow n m w table rem s0
          · exact Nat.zero_le _
        have h2 : 2 ^ rem < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      have hc1_lt : cnt1At n m w table pos.val s < 2 ^ (n + 1) := by
        have h1 : cnt1At n m w table pos.val s ≤ 2 ^ rem := by
          dsimp only [cnt1At]
          have hsub : n - (pos.val + 1) = rem := by dsimp only [pos]; omega
          rw [hsub]
          split_ifs
          · exact cntRec_le_two_pow n m w table rem s1
          · exact Nat.zero_le _
        have h2 : 2 ^ rem < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      have hsum_val_eq : cntRec n m w table (rem + 1) s =
          cnt0At n m w table pos.val s + cnt1At n m w table pos.val s := by
        have hsub : n - (pos.val + 1) = rem := by dsimp only [pos]; omega
        dsimp only [cntRec, cnt0At, cnt1At]
        rw [hsub]
      have hsum_lt : cntRec n m w table (rem + 1) s < 2 ^ (n + 1) :=
        lt_of_le_of_lt (cntRec_le_two_pow n m w table (rem + 1) s)
          (Nat.pow_lt_pow_right (by omega) (by omega))
      have hadd := hwSum_ev (xOf m w table) (xOf_length m w table) (by
        rw [(h01.trans (h1s.trans (hs01.trans hs12))).eval_eq (xOf m w table) (xOf_length m w table) hcF]
        exact hcF_val table)
      have hb0 : bitsVal (fun r => if h : r < n + 1 then evalWire bs2.gates (xOf m w table) (w0 ⟨r, h⟩) else false) (n + 1) =
          cnt0At n m w table pos.val s := by
        rw [bitsVal_congr _ (fun r => (cnt0At n m w table pos.val s).testBit r) (n + 1)
            (fun r hr => by simp only [hr, ↓reduceDIte]; exact hc0_eq ⟨r, hr⟩)]
        exact bitsVal_eq_of_testBit _ _ hc0_lt
      have hb1 : bitsVal (fun r => if h : r < n + 1 then evalWire bs2.gates (xOf m w table) (w1 ⟨r, h⟩) else false) (n + 1) =
          cnt1At n m w table pos.val s := by
        rw [bitsVal_congr _ (fun r => (cnt1At n m w table pos.val s).testBit r) (n + 1)
            (fun r hr => by simp only [hr, ↓reduceDIte]; exact hc1_eq ⟨r, hr⟩)]
        exact bitsVal_eq_of_testBit _ _ hc1_lt
      rw [hb0, hb1, ← hsum_val_eq] at hadd
      have hbsum_eq : bitsVal (fun r => if h : r < n + 1 then evalWire bs3.gates (xOf m w table) (wSum ⟨r, h⟩) else false) (n + 1) =
          cntRec n m w table (rem + 1) s := by
        have hlt_s := bitsVal_lt (fun r => if h : r < n + 1 then evalWire bs3.gates (xOf m w table) (wSum ⟨r, h⟩) else false) (n + 1)
        cases hco : evalWire bs3.gates (xOf m w table) coutW
        · simp only [hco, Bool.toNat_false, zero_mul, add_zero] at hadd; exact hadd
        · simp only [hco, Bool.toNat_true, one_mul] at hadd; omega
      constructor
      · have htb := congrArg (fun v => v.testBit j.val) hbsum_eq
        rw [bitsVal_testBit] at htb
        simpa [j.isLt] using htb
      · rw [hs23.eval_eq (xOf m w table) (xOf_length m w table) (hs12.bound (hw0_bnd j))]
        exact hc0_eq j
    have hloop : ∀ (N : ℕ) (hN : N ≤ 2 ^ a),
        ∃ (b2 : Builder I) (f : Fin N → (Fin (n + 1) → ℕ) × (Fin (n + 1) → ℕ)),
          Extends b1 b2 ∧ b2.size ≤ b1.size + N * (14 * (n + 1)) ∧
          ∀ s : Fin N, P_s ⟨s.val, lt_of_lt_of_le s.isLt hN⟩ b2 (f s) := by
      intro N
      induction N with
      | zero =>
        intro _
        exact ⟨b1, fun s => Fin.elim0 s, Extends.refl b1, by simp, fun s => Fin.elim0 s⟩
      | succ N ih =>
        intro hN
        obtain ⟨ba, fa, ha, hsa, hPa⟩ := ih (by omega)
        obtain ⟨bb, pair, hb, hsb, hPb⟩ := hstep_s ⟨N, hN⟩ ba ha
        refine ⟨bb, fun s => Fin.lastCases pair fa s, ha.trans hb, ?_, ?_⟩
        · rw [Nat.add_mul, one_mul]; omega
        · intro s
          refine Fin.lastCases ?_ ?_ s
          · simpa using hPb
          · intro s'
            simpa using hPs_ext ⟨s'.val, by omega⟩ ba bb (fa s') hb (hPa s')
    obtain ⟨b2, f, h12, hs12, hP2⟩ := hloop (2 ^ a) le_rfl
    let cnt2 : Fin (2 ^ a) → Fin (n + 1) → ℕ := fun s => (f s).1
    let c0_2 : Fin (rem + 1) → Fin (2 ^ a) → Fin (n + 1) → ℕ := fun r =>
      Fin.lastCases (fun s => (f s).2) c0_1 r
    refine ⟨b2, cnt2, c0_2, h01.trans h12, ?_, fun s j => (hP2 s).1 j, ?_, ?_⟩
    · have hmul : 2 ^ a * (14 * (n + 1)) = 14 * (n + 1) * 2 ^ a := by ring
      rw [Nat.add_mul, one_mul]; omega
    · intro r s j
      refine Fin.lastCases ?_ ?_ r
      · simpa [c0_2] using (hP2 s).2.1 j
      · intro r'; simpa [c0_2] using h12.bound (hc01_bnd r' s j)
    · intro table
      refine ⟨fun s j => ((hP2 s).2.2 table j).1, fun r s j => ?_⟩
      refine Fin.lastCases ?_ ?_ r
      · simpa [c0_2, pos] using ((hP2 s).2.2 table j).2
      · intro r'
        simpa [c0_2] using (by
          rw [h12.eval_eq (xOf m w table) (xOf_length m w table) (hc01_bnd r' s j)]
          exact (hspec1 table).2 r' s j)

def nextStateWires (d e pos : ℕ) (ws : Fin (d + e) → ℕ) (bw : ℕ) : Fin (d + e) → ℕ :=
  fun k =>
    if h1 : k.val < d then
      if k.val = 0 then bw else ws ⟨k.val - 1, by omega⟩
    else
      if k.val = d + pos then bw else ws k

lemma nextStateWires_bound {I d e pos : ℕ} {b : Builder I}
    {ws : Fin (d + e) → ℕ} {bw : ℕ}
    (hws : ∀ k, ws k < I + b.size) (hbw : bw < I + b.size) :
    ∀ k, nextStateWires d e pos ws bw k < I + b.size := by
  intro k; dsimp only [nextStateWires]
  split_ifs
  · exact hbw
  · exact hws _
  · exact hbw
  · exact hws _

lemma nextStateWires_eval {I d e pos : ℕ} (b : Builder I) (x : List Bool)
    (ws : Fin (d + e) → ℕ) (bw : ℕ) (s : Fin (2 ^ (d + e))) (bit : Bool)
    (hws : ∀ k : Fin (d + e), evalWire b.gates x (ws k) = s.val.testBit k.val)
    (hbw : evalWire b.gates x bw = bit) :
    ∀ k : Fin (d + e),
      evalWire b.gates x (nextStateWires d e pos ws bw k) = (nextState d e pos s bit).val.testBit k.val := by
  intro k
  rw [nextState_testBit d e pos s bit k.val k.isLt]
  dsimp only [nextStateWires, nextStateBit]
  by_cases h1 : k.val < d
  · simp only [h1, ↓reduceDIte, ↓reduceIte]
    by_cases h0 : k.val = 0
    · simp [h0, hbw]
    · simp only [h0, ↓reduceIte]; exact hws ⟨k.val - 1, by omega⟩
  · simp only [h1, ↓reduceDIte, ↓reduceIte]
    by_cases hp : k.val = d + pos
    · simp [hp, hbw]
    · simp only [hp, ↓reduceIte]; exact hws k

lemma log2_le_of_le_two_pow {slots n : ℕ} (hn : 0 < n) (hsl : slots ≤ 2 ^ n) :
    Nat.log2 (slots + 1) ≤ n := by
  by_cases h0 : slots + 1 = 0
  · omega
  · have hlt : slots + 1 < 2 ^ (n + 1) := by
      have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      rw [Nat.pow_succ]; omega
    by_contra hgt
    have hge : n + 1 ≤ Nat.log2 (slots + 1) := by omega
    have hpow : 2 ^ (n + 1) ≤ 2 ^ Nat.log2 (slots + 1) := Nat.pow_le_pow_right (by omega) hge
    have hlog := Nat.log2_self_le h0
    omega

lemma buildUnrank {n m w slots : ℕ} (hn : 0 < n) (hmn : m ≤ n) (hsl : slots ≤ 2 ^ n)
    (b0 : Builder (m * 2 ^ (w + 1)))
    (cFalse cTrue : ℕ)
    (hcF : cFalse < m * 2 ^ (w + 1) + b0.size)
    (hcT : cTrue < m * 2 ^ (w + 1) + b0.size)
    (hcF_val : ∀ table, evalWire b0.gates (xOf m w table) cFalse = false)
    (hcT_val : ∀ table, evalWire b0.gates (xOf m w table) cTrue = true)
    (c0W : Fin n → Fin (2 ^ aOf n m w) → Fin (n + 1) → ℕ)
    (hc0_bnd : ∀ pos s j, c0W pos s j < m * 2 ^ (w + 1) + b0.size)
    (hc0_ev : ∀ table (pos : Fin n) s j,
      evalWire b0.gates (xOf m w table) (c0W pos s j) = (cnt0At n m w table pos.val s).testBit j.val) :
    let I := m * 2 ^ (w + 1)
    let a := aOf n m w
    ∀ (pos : ℕ), pos ≤ n →
      ∃ (b' : Builder I)
        (remW : Fin slots → Fin (n + 1) → ℕ)
        (stW : Fin slots → Fin a → ℕ)
        (bitsW : Fin slots → Fin pos → ℕ),
        Extends b0 b' ∧
        b'.size ≤ b0.size + pos * (8192 * (n + 1) ^ 3 * (2 ^ a + slots) + (17 * (n + 1) + 1) * slots) ∧
        (∀ t j, remW t j < I + b'.size) ∧
        (∀ t k, stW t k < I + b'.size) ∧
        (∀ t j, bitsW t j < I + b'.size) ∧
        ∀ table,
          (∀ t j, evalWire b'.gates (xOf m w table) (remW t j) =
            (unrankState n m w table t.val pos).2.1.testBit j.val) ∧
          (∀ t k, evalWire b'.gates (xOf m w table) (stW t k) =
            (unrankState n m w table t.val pos).2.2.val.testBit k.val) ∧
          (∀ t j, evalWire b'.gates (xOf m w table) (bitsW t j) =
            unrankBit n m w table t.val j.val) := by
  intro I a pos
  induction pos with
  | zero =>
    intro _
    let remW : Fin slots → Fin (n + 1) → ℕ := fun t j => if t.val.testBit j.val then cTrue else cFalse
    let stW : Fin slots → Fin a → ℕ := fun _ _ => cFalse
    refine ⟨b0, remW, stW, fun _ j => Fin.elim0 j, Extends.refl b0, by simp, ?_, ?_,
            fun _ j => Fin.elim0 j, ?_⟩
    · intro t j; dsimp only [remW]; split_ifs <;> assumption
    · intro _ _; exact hcF
    · intro table
      refine ⟨fun t j => ?_, fun t k => ?_, fun _ j => Fin.elim0 j⟩
      · dsimp only [remW, unrankState]
        cases htb : t.val.testBit j.val
        · simp [hcF_val table]
        · simp [hcT_val table]
      · dsimp only [stW, unrankState]
        simp [hcF_val table]
  | succ pos ih =>
    intro hpos
    obtain ⟨b1, rem1, st1, bits1, h01, hs1, hrem1_bnd, hst1_bnd, hbits1_bnd, hspec1⟩ := ih (by omega)
    let posFin : Fin n := ⟨pos, by omega⟩
    obtain ⟨b2, zcW, h12, hs12, hzc_bnd, hzc_ev⟩ :=
      buildLookup049 b1 (c0W posFin) (fun s j => h01.bound (hc0_bnd posFin s j)) st1 hst1_bnd
    have hlookup_le : 128 * (2 ^ a + slots) * (a + (n + 1) + Nat.log2 (slots + 1) + 3) ^ 3 ≤
        8192 * (n + 1) ^ 3 * (2 ^ a + slots) := by
      have ha_le : a ≤ 2 * n := by dsimp only [a, aOf, dOf, eOf]; omega
      have hlog_le : Nat.log2 (slots + 1) ≤ n := log2_le_of_le_two_pow hn hsl
      have hlin : a + (n + 1) + Nat.log2 (slots + 1) + 3 ≤ 4 * (n + 1) := by omega
      have hcub : (a + (n + 1) + Nat.log2 (slots + 1) + 3) ^ 3 ≤ (4 * (n + 1)) ^ 3 :=
        Nat.pow_le_pow_left hlin 3
      calc 128 * (2 ^ a + slots) * (a + (n + 1) + Nat.log2 (slots + 1) + 3) ^ 3
          ≤ 128 * (2 ^ a + slots) * (4 * (n + 1)) ^ 3 := Nat.mul_le_mul_left _ hcub
        _ = 8192 * (n + 1) ^ 3 * (2 ^ a + slots) := by ring
    let P_t : Fin slots → Builder I → ((Fin (n + 1) → ℕ) × (Fin a → ℕ) × ℕ) → Prop :=
      fun t b' tup =>
        (∀ j, tup.1 j < I + b'.size) ∧ (∀ k, tup.2.1 k < I + b'.size) ∧ tup.2.2 < I + b'.size ∧
        ∀ table,
          (∀ j, evalWire b'.gates (xOf m w table) (tup.1 j) =
            (unrankState n m w table t.val (pos + 1)).2.1.testBit j.val) ∧
          (∀ k, evalWire b'.gates (xOf m w table) (tup.2.1 k) =
            (unrankState n m w table t.val (pos + 1)).2.2.val.testBit k.val) ∧
          evalWire b'.gates (xOf m w table) tup.2.2 = unrankBit n m w table t.val pos
    have hPt_ext : ∀ t ba bb tup, Extends ba bb → P_t t ba tup → P_t t bb tup := by
      intro t ba bb tup hext ⟨h1, h2, h3, hev⟩
      refine ⟨fun j => hext.bound (h1 j), fun k => hext.bound (h2 k), hext.bound h3, fun table => ?_⟩
      refine ⟨fun j => ?_, fun k => ?_, ?_⟩
      · rw [hext.eval_eq (xOf m w table) (xOf_length m w table) (h1 j)]; exact (hev table).1 j
      · rw [hext.eval_eq (xOf m w table) (xOf_length m w table) (h2 k)]; exact (hev table).2.1 k
      · rw [hext.eval_eq (xOf m w table) (xOf_length m w table) h3]; exact (hev table).2.2
    have hstep_t : ∀ (t : Fin slots) (bt : Builder I),
        Extends b2 bt →
        ∃ (bt' : Builder I) (tup : (Fin (n + 1) → ℕ) × (Fin a → ℕ) × ℕ),
          Extends bt bt' ∧ bt'.size ≤ bt.size + (17 * (n + 1) + 1) ∧ P_t t bt' tup := by
      intro t bt h2t
      obtain ⟨bt1, diffW, ltW, ht01, hsz1, hdiff_bnd, hlt_bnd, hsub_ev⟩ :=
        mkSubLtVec_exists bt cFalse ((h01.trans (h12.trans h2t)).bound hcF)
          (rem1 t) (zcW t)
          (fun j => (h12.trans h2t).bound (hrem1_bnd t j))
          (fun j => h2t.bound (hzc_bnd t j))
      let rBit := mkNot bt1 ltW hlt_bnd
      have sBit := mkNot_spec bt1 ltW hlt_bnd
      obtain ⟨bt3, remNew, ht23, hsz3, hremNew_bnd, hmux_ev⟩ :=
        mkMuxVec_exists rBit.1 rBit.2 sBit.2.2.1 diffW (rem1 t)
          (fun j => sBit.1.bound (hdiff_bnd j))
          (fun j => (h12.trans (h2t.trans (ht01.trans sBit.1))).bound (hrem1_bnd t j))
      let stNew := nextStateWires (dOf n w) (eOf n m w) pos (st1 t) rBit.2
      have hstNew_bnd : ∀ k, stNew k < I + bt3.size :=
        nextStateWires_bound
          (fun k => (h12.trans (h2t.trans (ht01.trans (sBit.1.trans ht23)))).bound (hst1_bnd t k))
          (ht23.bound sBit.2.2.1)
      refine ⟨bt3, (remNew, stNew, rBit.2), ht01.trans (sBit.1.trans ht23), ?_,
              hremNew_bnd, hstNew_bnd, ht23.bound sBit.2.2.1, fun table => ?_⟩
      · have hsB : rBit.1.size = bt1.size + 1 := sBit.2.1
        omega
      · let x := xOf m w table
        have hx : x.length = I := xOf_length m w table
        let cur := unrankState n m w table t.val pos
        let remVal := cur.2.1
        let stVal := cur.2.2
        let zcVal := cnt0At n m w table pos stVal
        have hrem_lt : remVal < 2 ^ (n + 1) := by
          have h1 : remVal ≤ t.val := unrankState_rem_le n m w table t.val pos
          have h2 : t.val < 2 ^ n := lt_of_lt_of_le t.isLt hsl
          have h3 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
          omega
        have hzc_lt : zcVal < 2 ^ (n + 1) := by
          have h1 : zcVal ≤ 2 ^ (n - (pos + 1)) := by
            dsimp only [zcVal, cnt0At]
            split_ifs
            · exact cntRec_le_two_pow n m w table (n - (pos + 1)) _
            · exact Nat.zero_le _
          have h2 : 2 ^ (n - (pos + 1)) < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
          omega
        have hzc_wire : ∀ j : Fin (n + 1), evalWire bt.gates x (zcW t j) = zcVal.testBit j.val := by
          intro j
          rw [h2t.eval_eq x hx (hzc_bnd t j), hzc_ev x hx t j]
          have haddr_eq : (⟨bitsVal (fun i => if h : i < a then evalWire b1.gates x (st1 t ⟨i, h⟩) else false) a,
              bitsVal_lt _ _⟩ : Fin (2 ^ a)) = stVal := by
            apply Fin.ext
            dsimp only
            rw [bitsVal_congr _ (fun i => stVal.val.testBit i) a
                (fun i hi => by simp only [hi, ↓reduceDIte]; exact (hspec1 table).2.1 t ⟨i, hi⟩)]
            exact bitsVal_eq_of_testBit stVal.val a stVal.isLt
          rw [haddr_eq, h01.eval_eq x hx (hc0_bnd posFin stVal j)]
          exact hc0_ev table posFin stVal j
        have hrem_wire : ∀ j : Fin (n + 1), evalWire bt.gates x (rem1 t j) = remVal.testBit j.val := by
          intro j
          rw [(h12.trans h2t).eval_eq x hx (hrem1_bnd t j)]
          exact (hspec1 table).1 t j
        have hsub := hsub_ev x hx (by
          rw [(h01.trans (h12.trans h2t)).eval_eq x hx hcF]; exact hcF_val table)
        dsimp only at hsub
        have hu_eq : bitsVal (fun j => if h : j < n + 1 then evalWire bt.gates x (rem1 t ⟨j, h⟩) else false) (n + 1) =
            remVal := by
          rw [bitsVal_congr _ (fun j => remVal.testBit j) (n + 1)
              (fun j hj => by simp only [hj, ↓reduceDIte]; exact hrem_wire ⟨j, hj⟩)]
          exact bitsVal_eq_of_testBit remVal (n + 1) hrem_lt
        have hv_eq : bitsVal (fun j => if h : j < n + 1 then evalWire bt.gates x (zcW t ⟨j, h⟩) else false) (n + 1) =
            zcVal := by
          rw [bitsVal_congr _ (fun j => zcVal.testBit j) (n + 1)
              (fun j hj => by simp only [hj, ↓reduceDIte]; exact hzc_wire ⟨j, hj⟩)]
          exact bitsVal_eq_of_testBit zcVal (n + 1) hzc_lt
        rw [hu_eq, hv_eq] at hsub
        have hdec := subLt_decode hrem_lt hzc_lt
          (bitsVal_lt (fun j => if h : j < n + 1 then evalWire bt1.gates x (diffW ⟨j, h⟩) else false) (n + 1)) hsub
        have hlt_eq : evalWire bt1.gates x ltW = decide (remVal < zcVal) := by
          apply Bool.eq_iff_iff.mpr; rw [hdec.1, decide_eq_true_eq]
        have hbit_eq : evalWire rBit.1.gates x rBit.2 = unrankBit n m w table t.val pos := by
          rw [sBit.2.2.2 x hx, hlt_eq]
          change (!decide (remVal < zcVal)) = decide (zcVal ≤ remVal)
          by_cases hle : zcVal ≤ remVal
          · have hnot : ¬ (remVal < zcVal) := by omega
            simp [hle, hnot]
          · have hlt : remVal < zcVal := by omega
            simp [hle, hlt]
        have hbit_bt3 : evalWire bt3.gates x rBit.2 = unrankBit n m w table t.val pos := by
          rw [ht23.eval_eq x hx sBit.2.2.1]; exact hbit_eq
        refine ⟨fun j => ?_, fun k => ?_, hbit_bt3⟩
        · rw [hmux_ev x hx j, hbit_eq, sBit.1.eval_eq x hx (hdiff_bnd j),
              (h12.trans (h2t.trans (ht01.trans sBit.1))).eval_eq x hx (hrem1_bnd t j),
              (hspec1 table).1 t j]
          change (if decide (zcVal ≤ remVal) then evalWire bt1.gates x (diffW j) else remVal.testBit j.val) =
            (if decide (zcVal ≤ remVal) then remVal - zcVal else remVal).testBit j.val
          by_cases hle : zcVal ≤ remVal
          · simp only [hle, decide_true, ↓reduceIte]
            have hdv := hdec.2 hle
            have htb := congrArg (fun v => v.testBit j.val) hdv
            rw [bitsVal_testBit] at htb
            simpa [j.isLt] using htb
          · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
        · have hst1_bt3 : ∀ r : Fin a, evalWire bt3.gates x (st1 t r) = stVal.val.testBit r.val := by
            intro r
            rw [(h12.trans (h2t.trans (ht01.trans (sBit.1.trans ht23)))).eval_eq x hx (hst1_bnd t r)]
            exact (hspec1 table).2.1 t r
          exact nextStateWires_eval bt3 x (st1 t) rBit.2 stVal (unrankBit n m w table t.val pos)
            hst1_bt3 hbit_bt3 k
    have hloop : ∀ (N : ℕ) (hN : N ≤ slots),
        ∃ (b3 : Builder I) (f : Fin N → (Fin (n + 1) → ℕ) × (Fin a → ℕ) × ℕ),
          Extends b2 b3 ∧ b3.size ≤ b2.size + N * (17 * (n + 1) + 1) ∧
          ∀ t : Fin N, P_t ⟨t.val, lt_of_lt_of_le t.isLt hN⟩ b3 (f t) := by
      intro N
      induction N with
      | zero =>
        intro _
        exact ⟨b2, fun t => Fin.elim0 t, Extends.refl b2, by simp, fun t => Fin.elim0 t⟩
      | succ N ih =>
        intro hN
        obtain ⟨ba, fa, ha, hsa, hPa⟩ := ih (by omega)
        obtain ⟨bb, tup, hb, hsb, hPb⟩ := hstep_t ⟨N, hN⟩ ba ha
        refine ⟨bb, fun t => Fin.lastCases tup fa t, ha.trans hb, ?_, ?_⟩
        · rw [Nat.add_mul, one_mul]; omega
        · intro t
          refine Fin.lastCases ?_ ?_ t
          · simpa using hPb
          · intro t'
            simpa using hPt_ext ⟨t'.val, by omega⟩ ba bb (fa t') hb (hPa t')
    obtain ⟨b3, f, h23, hs23, hP3⟩ := hloop slots le_rfl
    let remNew : Fin slots → Fin (n + 1) → ℕ := fun t => (f t).1
    let stNew : Fin slots → Fin a → ℕ := fun t => (f t).2.1
    let bitsNew : Fin slots → Fin (pos + 1) → ℕ := fun t j =>
      Fin.lastCases (f t).2.2 (bits1 t) j
    refine ⟨b3, remNew, stNew, bitsNew, h01.trans (h12.trans h23), ?_,
            fun t j => (hP3 t).1 j, fun t k => (hP3 t).2.1 k, ?_, ?_⟩
    · have hcomm : slots * (17 * (n + 1) + 1) = (17 * (n + 1) + 1) * slots := Nat.mul_comm _ _
      have hs12' : b2.size ≤ b1.size + 8192 * (n + 1) ^ 3 * (2 ^ a + slots) := by
        change b2.size ≤ b1.size + 128 * (2 ^ a + slots) * (a + (n + 1) + Nat.log2 (slots + 1) + 3) ^ 3 at hs12
        omega
      rw [Nat.add_mul, one_mul]
      omega
    · intro t j
      refine Fin.lastCases ?_ ?_ j
      · simpa [bitsNew] using (hP3 t).2.2.1
      · intro j'; simpa [bitsNew] using (h12.trans h23).bound (hbits1_bnd t j')
    · intro table
      refine ⟨fun t j => ((hP3 t).2.2.2 table).1 j, fun t k => ((hP3 t).2.2.2 table).2.1 k, fun t j => ?_⟩
      refine Fin.lastCases ?_ ?_ j
      · simpa [bitsNew] using ((hP3 t).2.2.2 table).2.2
      · intro j'
        simpa [bitsNew] using (by
          rw [(h12.trans h23).eval_eq (xOf m w table) (xOf_length m w table) (hbits1_bnd t j')]
          exact (hspec1 table).2.2 t j')

lemma size_budget_bound (n m states slots : ℕ) (hmn : m ≤ n) (hst : 1 ≤ states) :
    2 + 2 * m * states + n * (14 * (n + 1) * states) + (n + 1) + slots * (13 * (n + 1)) +
      n * (8192 * (n + 1) ^ 3 * (states + slots) + (17 * (n + 1) + 1) * slots) ≤
    65536 * (n + 1) ^ 4 * (states + slots) := by
  have hn1 : 1 ≤ n + 1 := by omega
  have hpow2 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hpow3 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by nlinarith
  have hpow4 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := by nlinarith
  have h1 : 2 + 2 * m * states ≤ 4 * (n + 1) * states := by nlinarith
  have h2 : n * (14 * (n + 1) * states) ≤ 14 * (n + 1) ^ 2 * states := by nlinarith
  have h3 : n + 1 ≤ (n + 1) * states := by nlinarith
  have h4 : slots * (13 * (n + 1)) ≤ 13 * (n + 1) * slots := by nlinarith
  have h5 : n * (8192 * (n + 1) ^ 3 * (states + slots) + (17 * (n + 1) + 1) * slots) ≤
      8210 * (n + 1) ^ 4 * (states + slots) := by
    have ha : n * (8192 * (n + 1) ^ 3 * (states + slots)) ≤ 8192 * (n + 1) ^ 4 * (states + slots) := by nlinarith
    have hb : (17 * (n + 1) + 1) * slots ≤ 18 * (n + 1) ^ 3 * (states + slots) := by nlinarith
    have hc : n * ((17 * (n + 1) + 1) * slots) ≤ 18 * (n + 1) ^ 4 * (states + slots) := by nlinarith
    rw [Nat.mul_add]
    linarith
  have h6 : 4 * (n + 1) * states ≤ 4 * (n + 1) ^ 4 * (states + slots) := by nlinarith
  have h7 : 14 * (n + 1) ^ 2 * states ≤ 14 * (n + 1) ^ 4 * (states + slots) := by nlinarith
  have h8 : (n + 1) * states ≤ (n + 1) ^ 4 * (states + slots) := by nlinarith
  have h9 : 13 * (n + 1) * slots ≤ 13 * (n + 1) ^ 4 * (states + slots) := by nlinarith
  linarith

lemma solve_050 (n m w slots : ℕ) (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (hsl : slots ≤ 2 ^ n) :
    let I := m * 2 ^ (w + 1)
    let d := min w (n - 1)
    let states := 2 ^ (d + (m + d - n))
    ∃ (C : Circuit)
      (valid : Fin slots → Fin (I + C.size)) (outBit : Fin slots → Fin n → Fin (I + C.size)),
      FanInTwo C ∧
      ReadsBack I C ∧ C.output < I + C.size ∧
      C.size ≤ 65536 * (n + 1) ^ 4 * (states + slots) ∧
      ∀ table : Fin m → (Fin (w + 1) → Bool) → Bool,
        let x := xOf m w table
        let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
          ∀ i : Fin m,
            table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
        (C.eval x = true ↔ sols.Nonempty) ∧
        ∀ t : Fin slots,
          ((C.wires x).getD (valid t).val false = true ↔ t.val < sols.card) ∧
          (t.val < sols.card → ∃ z ∈ sols,
            (sols.filter (fun y => y.val < z.val)).card = t.val ∧
            ∀ j : Fin n, (C.wires x).getD (outBit t j).val false =
              z.val.testBit (n - 1 - j.val)) := by
  intro I d states
  let bInit := Builder.empty I
  let rF := mkFalse bInit
  have sF := mkFalse_spec bInit
  let rT := mkTrue rF.1
  have sT := mkTrue_spec rF.1
  let b0 := rT.1
  let cFalse := rF.2
  let cTrue := rT.2
  have hcF : cFalse < I + b0.size := sT.1.bound sF.2.2.1
  have hcT : cTrue < I + b0.size := sT.2.2.1
  have hb0_sz : b0.size = 2 := by
    have h1 : rF.1.size = 1 := by simpa [rF, bInit, Builder.empty, Builder.size] using sF.2.1
    have h2 : b0.size = rF.1.size + 1 := sT.2.1
    omega
  have hcF_val : ∀ table, evalWire b0.gates (xOf m w table) cFalse = false := by
    intro table
    rw [sT.1.eval_eq (xOf m w table) (xOf_length m w table) sF.2.2.1]
    exact sF.2.2.2 (xOf m w table) (xOf_length m w table)
  have hcT_val : ∀ table, evalWire b0.gates (xOf m w table) cTrue = true := by
    intro table
    exact sT.2.2.2 (xOf m w table) (xOf_length m w table)
  obtain ⟨b1, transW, termW, h01, hs1, htr_bnd, htm_bnd, hspec1⟩ :=
    buildConstraints hn b0 cTrue hcT hcT_val
  obtain ⟨b2, cntW, c0W_rev, h12, hs2, hcnt_bnd, hc0_bnd, hspec2⟩ :=
    buildDp b1 cFalse (h01.bound hcF)
      (fun table => by rw [h01.eval_eq _ (xOf_length m w table) hcF]; exact hcF_val table)
      transW htr_bnd (fun table pos s bit => (hspec1 table).1 pos s bit)
      termW htm_bnd (fun table s => (hspec1 table).2 s) n le_rfl
  let rootZero : Fin (2 ^ aOf n m w) := ⟨0, Nat.pow_pos (by omega : 0 < 2)⟩
  obtain ⟨b3, outW, h23, hs3, hout_bnd, hout_ev⟩ :=
    mkOrVec_exists b2 cFalse ((h01.trans h12).bound hcF) (cntW rootZero) (fun j => hcnt_bnd rootZero j)

  have hvalid_all : ∃ (b4 : Builder I) (validW : Fin slots → ℕ),
      Extends b3 b4 ∧ b4.size ≤ b3.size + slots * (13 * (n + 1)) ∧
      (∀ t, validW t < I + b4.size) ∧
      ∀ table (t : Fin slots),
        evalWire b4.gates (xOf m w table) (validW t) = true ↔
          t.val < cntRec n m w table n rootZero := by
    let P_v : Fin slots → Builder I → ℕ → Prop := fun t b' wv =>
      wv < I + b'.size ∧
      ∀ table, evalWire b'.gates (xOf m w table) wv = true ↔ t.val < cntRec n m w table n rootZero
    have hPv_ext : ∀ t ba bb wv, Extends ba bb → P_v t ba wv → P_v t bb wv := by
      intro t ba bb wv hext ⟨hbnd, hev⟩
      exact ⟨hext.bound hbnd, fun table => by
        rw [hext.eval_eq (xOf m w table) (xOf_length m w table) hbnd]; exact hev table⟩
    have hloop : ∀ (N : ℕ) (hN : N ≤ slots),
        ∃ (b4 : Builder I) (f : Fin N → ℕ),
          Extends b3 b4 ∧ b4.size ≤ b3.size + N * (13 * (n + 1)) ∧
          ∀ t : Fin N, P_v ⟨t.val, lt_of_lt_of_le t.isLt hN⟩ b4 (f t) := by
      intro N
      induction N with
      | zero =>
        intro _
        exact ⟨b3, fun t => Fin.elim0 t, Extends.refl b3, by simp, fun t => Fin.elim0 t⟩
      | succ N ih =>
        intro hN
        obtain ⟨ba, fa, ha, hsa, hPa⟩ := ih (by omega)
        let tBits : Fin (n + 1) → ℕ := fun j => if N.testBit j.val then cTrue else cFalse
        have htBits_bnd : ∀ j, tBits j < I + ba.size := by
          intro j; dsimp only [tBits]; split_ifs
          · exact (h01.trans (h12.trans (h23.trans ha))).bound hcT
          · exact (h01.trans (h12.trans (h23.trans ha))).bound hcF
        obtain ⟨bb, _, ltW, hb, hsb, _, hlt_bnd, hsub_ev⟩ :=
          mkSubLtVec_exists ba cFalse ((h01.trans (h12.trans (h23.trans ha))).bound hcF)
            tBits (cntW rootZero) htBits_bnd (fun j => (h23.trans ha).bound (hcnt_bnd rootZero j))
        refine ⟨bb, fun k => Fin.lastCases ltW fa k, ha.trans hb, ?_, ?_⟩
        · rw [Nat.add_mul, one_mul]; omega
        · intro k
          refine Fin.lastCases ?_ ?_ k
          · refine ⟨by simpa using hlt_bnd, fun table => ?_⟩
            simpa only [Fin.lastCases_last] using (by
              let x := xOf m w table
              have hx := xOf_length m w table
              have hsub := hsub_ev x hx (by
                rw [(h01.trans (h12.trans (h23.trans ha))).eval_eq x hx hcF]; exact hcF_val table)
              dsimp only at hsub
              have hN_lt : N < 2 ^ (n + 1) := by
                have h1 : N < 2 ^ n := lt_of_lt_of_le hN hsl
                have h2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
                omega
              have hcnt_lt : cntRec n m w table n rootZero < 2 ^ (n + 1) :=
                lt_of_le_of_lt (cntRec_le_two_pow n m w table n rootZero)
                  (Nat.pow_lt_pow_right (by omega) (by omega))
              have hu_eq : bitsVal (fun j => if h : j < n + 1 then evalWire ba.gates x (tBits ⟨j, h⟩) else false) (n + 1) = N := by
                rw [bitsVal_congr _ (fun j => N.testBit j) (n + 1) (fun j hj => by
                  simp only [hj, ↓reduceDIte, tBits]
                  cases htb : N.testBit j
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [(h01.trans (h12.trans (h23.trans ha))).eval_eq x hx hcF]; exact hcF_val table
                  · simp only [↓reduceIte]
                    rw [(h01.trans (h12.trans (h23.trans ha))).eval_eq x hx hcT]; exact hcT_val table)]
                exact bitsVal_eq_of_testBit N (n + 1) hN_lt
              have hv_eq : bitsVal (fun j => if h : j < n + 1 then evalWire ba.gates x (cntW rootZero ⟨j, h⟩) else false) (n + 1) =
                  cntRec n m w table n rootZero := by
                rw [bitsVal_congr _ (fun j => (cntRec n m w table n rootZero).testBit j) (n + 1) (fun j hj => by
                  simp only [hj, ↓reduceDIte]
                  rw [(h23.trans ha).eval_eq x hx (hcnt_bnd rootZero ⟨j, hj⟩)]
                  exact (hspec2 table).1 rootZero ⟨j, hj⟩)]
                exact bitsVal_eq_of_testBit _ (n + 1) hcnt_lt
              rw [hu_eq, hv_eq] at hsub
              exact (subLt_decode hN_lt hcnt_lt (bitsVal_lt _ _) hsub).1)
          · intro k'
            simpa using hPv_ext ⟨k'.val, by omega⟩ ba bb (fa k') hb (hPa k')
    obtain ⟨b4, f, h34, hs4, hP4⟩ := hloop slots le_rfl
    exact ⟨b4, f, h34, hs4, fun t => (hP4 t).1, fun table t => (hP4 t).2 table⟩
  obtain ⟨b4, validW, h34, hs4, hval_bnd, hval_ev⟩ := hvalid_all
  let c0W : Fin n → Fin (2 ^ aOf n m w) → Fin (n + 1) → ℕ :=
    fun pos => c0W_rev ⟨n - 1 - pos.val, by omega⟩
  have hc0W_bnd : ∀ pos s j, c0W pos s j < I + b4.size :=
    fun pos s j => (h23.trans h34).bound (hc0_bnd ⟨n - 1 - pos.val, by omega⟩ s j)
  have hc0W_ev : ∀ table (pos : Fin n) s j,
      evalWire b4.gates (xOf m w table) (c0W pos s j) = (cnt0At n m w table pos.val s).testBit j.val := by
    intro table pos s j
    dsimp only [c0W]
    rw [(h23.trans h34).eval_eq (xOf m w table) (xOf_length m w table)
        (hc0_bnd ⟨n - 1 - pos.val, by omega⟩ s j)]
    have heq : n - (n - 1 - pos.val + 1) = pos.val := by omega
    simpa only [heq] using (hspec2 table).2 ⟨n - 1 - pos.val, by omega⟩ s j
  obtain ⟨b5, _, _, bitsW, h45, hs5, _, _, hbits_bnd, hspec5⟩ :=
    buildUnrank hn hmn hsl b4 cFalse cTrue
      ((h01.trans (h12.trans (h23.trans h34))).bound hcF)
      ((h01.trans (h12.trans (h23.trans h34))).bound hcT)
      (fun table => by rw [(h01.trans (h12.trans (h23.trans h34))).eval_eq _ (xOf_length m w table) hcF]; exact hcF_val table)
      (fun table => by rw [(h01.trans (h12.trans (h23.trans h34))).eval_eq _ (xOf_length m w table) hcT]; exact hcT_val table)
      c0W hc0W_bnd hc0W_ev n le_rfl
  let C : Circuit := ⟨b5.gates, outW⟩
  have hC_size : C.size = b5.size := rfl
  let valid : Fin slots → Fin (I + C.size) := fun t => ⟨validW t, h45.bound (hval_bnd t)⟩
  let outBit : Fin slots → Fin n → Fin (I + C.size) := fun t j => ⟨bitsW t j, hbits_bnd t j⟩
  refine ⟨C, valid, outBit, b5.hFan, b5.hRB, (h34.trans h45).bound hout_bnd, ?_, ?_⟩
  · have hstates : states = 2 ^ aOf n m w := rfl
    have hpos_st : 1 ≤ states := Nat.pow_pos (by omega : 0 < 2)
    have htot : C.size ≤
        2 + 2 * m * states + n * (14 * (n + 1) * states) + (n + 1) + slots * (13 * (n + 1)) +
        n * (8192 * (n + 1) ^ 3 * (states + slots) + (17 * (n + 1) + 1) * slots) := by
      change b5.size ≤ _
      rw [hstates]
      omega
    exact Nat.le_trans htot (size_budget_bound n m states slots hmn hpos_st)
  · intro table
    let x := xOf m w table
    let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
      ∀ i : Fin m, table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
    have hsols_card : sols.card = cntRec n m w table n rootZero := by
      have hsols0 : validSuffix n m w table 0 0 = sols := by
        ext z
        simp only [validSuffix, sols, Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_zero,
                   Nat.div_eq_of_lt z.isLt]
        rw [sols_iff_dp n m w hn hmn table z]
        constructor
        · rintro ⟨htr, htm⟩; exact ⟨fun p hp => htr p (Nat.zero_le p) hp, htm⟩
        · rintro ⟨htr, htm⟩; exact ⟨fun p _ hp => htr p hp, htm⟩
      have hc := card_validSuffix n m w table n le_rfl 0 (by simp)
      simp only [Nat.sub_self, hsols0] at hc
      exact hc
    constructor
    · change evalWire b5.gates x outW = true ↔ sols.Nonempty
      rw [(h34.trans h45).eval_eq x (xOf_length m w table) hout_bnd,
          hout_ev x (xOf_length m w table) (by
            rw [(h01.trans h12).eval_eq x (xOf_length m w table) hcF]; exact hcF_val table)]
      rw [← Finset.card_pos, hsols_card]
      constructor
      · rintro ⟨j, hj⟩
        rw [(hspec2 table).1 rootZero j] at hj
        by_contra h0
        simp only [not_lt, Nat.le_zero] at h0
        rw [h0] at hj; simp at hj
      · intro hpos
        have hlt : cntRec n m w table n rootZero < 2 ^ (n + 1) :=
          lt_of_le_of_lt (cntRec_le_two_pow n m w table n rootZero)
            (Nat.pow_lt_pow_right (by omega) (by omega))
        by_contra hnone
        have hzero : cntRec n m w table n rootZero = 0 := by
          rw [← bitsVal_eq_of_testBit (cntRec n m w table n rootZero) (n + 1) hlt]
          have hall0 : ∀ j < n + 1, (cntRec n m w table n rootZero).testBit j = false := by
            intro j hj
            by_contra htrue
            have ht : (cntRec n m w table n rootZero).testBit j = true := by
              cases h : (cntRec n m w table n rootZero).testBit j <;> simp_all
            apply hnone
            refine ⟨⟨j, hj⟩, ?_⟩
            rw [(hspec2 table).1 rootZero ⟨j, hj⟩]; exact ht
          rw [bitsVal_congr _ (fun _ => false) (n + 1) hall0]
          clear hall0 hlt hnone hpos hsols_card
          induction (n + 1) with
          | zero => rfl
          | succ k ih => simp [bitsVal, ih]
        omega
    · intro t
      constructor
      · change evalWire b5.gates x (validW t) = true ↔ t.val < sols.card
        rw [h45.eval_eq x (xOf_length m w table) (hval_bnd t), hval_ev table t, hsols_card]
      · intro ht
        obtain ⟨z, hz_mem, hz_rank, hz_bits⟩ := unrank_spec n m w hn hmn table t.val ht
        refine ⟨z, hz_mem, hz_rank, fun j => ?_⟩
        change evalWire b5.gates x (bitsW t j) = z.val.testBit (n - 1 - j.val)
        rw [(hspec5 table).2.2 t j]
        exact hz_bits j

end PEqualNP.Outside.L_clb_050_aux

theorem PEqualNP.Outside.L_clb_050 : (∀ (n m w slots : ℕ) (hn : 0 < n), 0 < m → m ≤ n → slots ≤ 2 ^ n →
  let I := m * 2 ^ (w + 1)
  let d := min w (n - 1)
  let states := 2 ^ (d + (m + d - n))
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (valid : Fin slots → Fin (I + C.size)) (outBit : Fin slots → Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 65536 * (n + 1) ^ 4 * (states + slots) ∧
    ∀ table : Fin m → (Fin (w + 1) → Bool) → Bool,
      let x := (List.ofFn (fun i : Fin m => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
        table i (fun j => p.val.testBit j.val)))).flatten
      let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z =>
        ∀ i : Fin m,
          table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
      (C.eval x = true ↔ sols.Nonempty) ∧
      ∀ t : Fin slots,
        ((C.wires x).getD (valid t).val false = true ↔ t.val < sols.card) ∧
        (t.val < sols.card → ∃ z ∈ sols,
          (sols.filter (fun y => y.val < z.val)).card = t.val ∧
          ∀ j : Fin n, (C.wires x).getD (outBit t j).val false =
            z.val.testBit (n - 1 - j.val))) := by
  intro n m w slots hn hm hmn hsl
  exact PEqualNP.Outside.L_clb_050_aux.solve_050 n m w slots hn hm hmn hsl
