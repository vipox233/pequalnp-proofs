import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29941_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def isAONB : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def mask (n : ℕ) : ℕ := 2 ^ (2 ^ n) - 1

theorem testBit_mask {n k : ℕ} (hk : k < 2 ^ n) : (mask n).testBit k = true := by
  simp [mask, Nat.testBit_two_pow_sub_one, hk]

def gateCol (n : ℕ) (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => cs.getD a 0).foldr (· &&& ·) (mask n)
  | GateOp.or => (g.inputs.map fun a => cs.getD a 0).foldr (· ||| ·) 0
  | GateOp.not => mask n ^^^ (g.inputs.map fun a => cs.getD a 0).headD 0
  | _ => 0

def aonB (C : Circuit) : Bool :=
  C.gates.all fun g => isAONB g.op

def Agree (k : ℕ) (cs : List ℕ) (w : List Bool) : Prop :=
  cs.length = w.length ∧ ∀ j, (cs.getD j 0).testBit k = w.getD j false

theorem agree_snoc {k : ℕ} {cs : List ℕ} {w : List Bool} {c : ℕ} {v : Bool}
    (h : Agree k cs w) (hv : c.testBit k = v) : Agree k (cs ++ [c]) (w ++ [v]) := by
  refine ⟨by simp [h.1], fun j => ?_⟩
  rcases lt_trichotomy j cs.length with hj | hj | hj
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (h.1 ▸ hj)]
    exact h.2 j
  · subst hj
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ h.1.symm.le]
    simp [h.1, hv]
  · have hl := h.1
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem testBit_foldr_and {k : ℕ} {n : ℕ} (hk : k < 2 ^ n) (l : List ℕ) :
    (l.foldr (· &&& ·) (mask n)).testBit k = (l.map fun c => c.testBit k).all id := by
  induction l with
  | nil => simp [testBit_mask hk]
  | cons c l ih => simp [ih]

theorem testBit_foldr_or {k : ℕ} (l : List ℕ) :
    (l.foldr (· ||| ·) 0).testBit k = (l.map fun c => c.testBit k).any id := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

theorem gateCol_spec {n k : ℕ} (hk : k < 2 ^ n) {cs : List ℕ} {w : List Bool}
    (h : Agree k cs w) (g : Gate) (hg : isAONB g.op = true) :
    (gateCol n g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hmap : ((g.inputs.map fun a => cs.getD a 0).map fun c => c.testBit k)
      = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]; exact List.map_congr_left (fun a _ => h.2 a)
  cases hop : g.op with
  | and => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_and hk, hmap]
  | or => simp only [gateCol, hop, GateOp.eval]; rw [testBit_foldr_or, hmap]
  | not =>
    simp only [gateCol, hop, GateOp.eval]
    rw [Nat.testBit_xor, testBit_mask hk, ← hmap]
    cases g.inputs <;> simp
  | mod m => rw [hop] at hg; simp [isAONB] at hg
  | maj => rw [hop] at hg; simp [isAONB] at hg

theorem agree_foldl {n k : ℕ} (hk : k < 2 ^ n) :
    ∀ (gs : List Gate) (cs : List ℕ) (w : List Bool), (∀ g ∈ gs, isAONB g.op = true) →
      Agree k cs w →
      Agree k (gs.foldl (fun cs g => cs ++ [gateCol n g cs]) cs)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil => intro cs w _ h; exact h
  | cons g gs ih =>
    intro cs w hg h
    exact ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (agree_snoc h (gateCol_spec hk h g (hg g List.mem_cons_self)))

def lcol (m : ℕ) : ℕ → ℕ
  | 0 => 2 ^ m - 1
  | j + 1 => 2 ^ m * lcol m j

def rcol (m v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ v + 2 ^ m * rcol m v k

def tcol (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + 2 ^ m * tcol m rs

def inCols (n m : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => lcol m i) ++ List.ofFn (fun j : Fin m => rcol m j n)

def pcols (N : ℕ) (C : Circuit) (n m : ℕ) : List ℕ :=
  C.gates.foldl (fun cs g => cs ++ [gateCol N g cs]) (inCols n m)

theorem lt_two_pow_of_lt {a b c : ℕ} (h : a < 2 ^ b) (hbc : b ≤ c) : a < 2 ^ c :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hbc)

theorem bit_lcol {m v : ℕ} (hv : v < m) : ∀ (j u : ℕ), (lcol m j).testBit (u * m + v) = decide (u = j) := by
  intro j
  induction j with
  | zero =>
    intro u
    cases u with
    | zero => simp [lcol, hv]
    | succ u =>
      simp only [lcol, Nat.testBit_two_pow_sub_one]
      have : m ≤ (u + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos u)
      simp; omega
  | succ j ih =>
    intro u
    rw [lcol, Nat.testBit_two_pow_mul]
    cases u with
    | zero => simp; omega
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      simp only [ge_iff_le, g, decide_true, Bool.true_and, e, ih u]
      simp

theorem bit_rcol {m v v' : ℕ} (hv : v < m) (hv' : v' < m) :
    ∀ (n u : ℕ), (rcol m v n).testBit (u * m + v') = decide (u < n ∧ v' = v) := by
  intro n
  induction n with
  | zero => intro u; simp [rcol]
  | succ n ih =>
    intro u
    have hlt : 2 ^ v < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hv
    rw [rcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v' ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      by_cases h : v' = v
      · subst h; simp
      · simp only [Nat.succ_pos, true_and, h, decide_false]
        exact decide_eq_false (fun e => h e.symm)
    | succ u =>
      have e : (u + 1) * m + v' - m = u * m + v' := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v' ≥ m := by rw [Nat.succ_mul]; omega
      have ne : v ≠ (u + 1) * m + v' := by rw [Nat.succ_mul]; omega
      simp only [g, decide_true, Bool.true_and, e, ih u, ne, decide_false, Bool.or_false]
      simp

theorem bit_tcol {m v : ℕ} (hv : v < m) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ m) → ∀ u : ℕ,
      (tcol m rows).testBit (u * m + v) = (rows.getD u 0).testBit v := by
  intro rows
  induction rows with
  | nil => intro _ u; simp [tcol]
  | cons r rs ih =>
    intro hr u
    have hr0 : r < 2 ^ m := hr r List.mem_cons_self
    rw [tcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hr0, Nat.testBit_or, Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      simp
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      have hz : r.testBit ((u + 1) * m + v) = false :=
        Nat.testBit_lt_two_pow (lt_two_pow_of_lt hr0 (by rw [Nat.succ_mul]; omega))
      simp only [g, decide_true, Bool.true_and, e, ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) u, hz,
        Bool.or_false, List.getD_cons_succ]

theorem agree_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) :
    Agree (u.val * m + v.val) (inCols n m) (oneEach u v) := by
  refine ⟨by simp [inCols, oneEach], fun j => ?_⟩
  by_cases hj : j < n
  · rw [inCols, oneEach, List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    rw [bit_lcol v.isLt j u.val]
    simp [Fin.ext_iff, eq_comm]
  · by_cases hj2 : j < n + m
    · have h1 : (List.ofFn (fun i : Fin n => lcol m i)).length ≤ j := by simp; omega
      have h2 : (List.ofFn (fun i : Fin n => decide (i = u))).length ≤ j := by simp; omega
      rw [inCols, oneEach, List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      rw [bit_rcol (by omega) v.isLt n u.val]
      simp only [u.isLt, true_and]
      simp [Fin.ext_iff]; omega
    · rw [List.getD_eq_default _ _ (by simp [inCols]; omega), List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp

theorem represents_of_pcols {n m N : ℕ} (hN : n * m ≤ 2 ^ N) (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ m) (hg : aonB C = true)
    (h : ((pcols N C n m).getD C.output 0 == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  intro u v
  have hk : u.val * m + v.val < 2 ^ N := by
    have : u.val * m + v.val < (u.val + 1) * m := by rw [Nat.succ_mul]; omega
    have : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    omega
  have hg' : ∀ g ∈ C.gates, isAONB g.op = true := fun g hg2 => List.all_eq_true.mp hg g hg2
  have hA := agree_foldl hk C.gates _ _ hg' (agree_oneEach u v)
  have := hA.2 C.output
  rw [show C.gates.foldl _ (inCols n m) = pcols N C n m from rfl, beq_iff_eq.mp h,
    bit_tcol v.isLt rows hrows u.val] at this
  exact this.symm

inductive BT where
  | leaf (v : ℕ)
  | node (l r : BT)

def BT.get : ℕ → BT → ℕ → ℕ
  | _, BT.leaf v, _ => v
  | 0, BT.node _ _, _ => 0
  | d + 1, BT.node l r, i => if i % 2 = 0 then BT.get d l (i / 2) else BT.get d r (i / 2)

def BT.set : ℕ → BT → ℕ → ℕ → BT
  | _, BT.leaf _, _, v => BT.leaf v
  | 0, BT.node l r, _, _ => BT.node l r
  | d + 1, BT.node l r, i, v => if i % 2 = 0 then BT.node (BT.set d l (i / 2) v) r else BT.node l (BT.set d r (i / 2) v)

def BT.zeros : ℕ → BT
  | 0 => BT.leaf 0
  | d + 1 => BT.node (BT.zeros d) (BT.zeros d)

def BT.WF : ℕ → BT → Prop
  | 0, BT.leaf _ => True
  | 0, BT.node _ _ => False
  | _ + 1, BT.leaf _ => False
  | d + 1, BT.node l r => BT.WF d l ∧ BT.WF d r

def BT.rd (d : ℕ) (t : BT) (i : ℕ) : ℕ := if i < 2 ^ d then t.get d i else 0

theorem wf_zeros : ∀ d, BT.WF d (BT.zeros d)
  | 0 => trivial
  | d + 1 => ⟨wf_zeros d, wf_zeros d⟩

theorem get_zeros : ∀ d i, (BT.zeros d).get d i = 0
  | 0, _ => rfl
  | d + 1, i => by simp only [BT.zeros, BT.get]; split <;> exact get_zeros d _

theorem wf_set : ∀ d t i v, BT.WF d t → BT.WF d (BT.set d t i v)
  | 0, BT.leaf _, _, _, _ => trivial
  | 0, BT.node _ _, _, _, h => h.elim
  | _ + 1, BT.leaf _, _, _, h => h.elim
  | d + 1, BT.node l r, i, v, h => by
    simp only [BT.set]; split
    · exact ⟨wf_set d l _ v h.1, h.2⟩
    · exact ⟨h.1, wf_set d r _ v h.2⟩

theorem get_set : ∀ d t i j v, BT.WF d t → i < 2 ^ d → j < 2 ^ d →
    (BT.set d t i v).get d j = if i = j then v else t.get d j
  | 0, BT.leaf _, i, j, v, _, hi, hj => by
    have : i = 0 := by simpa using hi
    have : j = 0 := by simpa using hj
    subst_vars; simp [BT.set, BT.get]
  | 0, BT.node _ _, _, _, _, h, _, _ => h.elim
  | _ + 1, BT.leaf _, _, _, _, h, _, _ => h.elim
  | d + 1, BT.node l r, i, j, v, h, hi, hj => by
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    by_cases hpi : i % 2 = 0 <;> by_cases hpj : j % 2 = 0
    · simp only [BT.set, hpi, if_true, BT.get, hpj, get_set d l _ _ v h.1 hi2 hj2]
      by_cases e : i = j
      · simp [e]
      · have : i / 2 ≠ j / 2 := by omega
        simp [e, this]
    · simp only [BT.set, hpi, if_true, BT.get, hpj, if_false]
      have : i ≠ j := by omega
      simp [this]
    · simp only [BT.set, hpi, if_false, BT.get, hpj, if_true]
      have : i ≠ j := by omega
      simp [this]
    · simp only [BT.set, hpi, if_false, BT.get, hpj, get_set d r _ _ v h.2 hi2 hj2]
      by_cases e : i = j
      · simp [e]
      · have : i / 2 ≠ j / 2 := by omega
        simp [e, this]

def push (D : ℕ) (st : BT × ℕ) (c : ℕ) : BT × ℕ := (st.1.set D st.2 c, st.2 + 1)

def gateColT (N D : ℕ) (g : Gate) (t : BT) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => t.rd D a).foldr (· &&& ·) (mask N)
  | GateOp.or => (g.inputs.map fun a => t.rd D a).foldr (· ||| ·) 0
  | GateOp.not => mask N ^^^ (g.inputs.map fun a => t.rd D a).headD 0
  | _ => 0

def tcols (N D : ℕ) (C : Circuit) (n m : ℕ) : BT × ℕ :=
  C.gates.foldl (fun st g => push D st (gateColT N D g st.1)) ((inCols n m).foldl (push D) (BT.zeros D, 0))

def Inv (D : ℕ) (st : BT × ℕ) (cs : List ℕ) : Prop :=
  BT.WF D st.1 ∧ st.2 = cs.length ∧ ∀ j, st.1.rd D j = cs.getD j 0

theorem inv_push {D : ℕ} {st : BT × ℕ} {cs : List ℕ} (h : Inv D st cs) (c : ℕ) (hl : cs.length < 2 ^ D) :
    Inv D (push D st c) (cs ++ [c]) := by
  obtain ⟨hw, hn, hr⟩ := h
  refine ⟨wf_set D _ _ _ hw, by simp [push, hn], fun j => ?_⟩
  simp only [push, BT.rd]
  by_cases hj : j < 2 ^ D
  · rw [if_pos hj, get_set D _ _ _ _ hw (hn ▸ hl) hj]
    rcases lt_trichotomy j cs.length with h1 | h1 | h1
    · have : st.2 ≠ j := by omega
      rw [if_neg this, List.getD_append _ _ _ _ h1]
      have := hr j; simp only [BT.rd, if_pos hj] at this; exact this
    · subst h1; rw [if_pos hn]; simp
    · have : st.2 ≠ j := by omega
      rw [if_neg this, List.getD_eq_default _ _ (by simp; omega)]
      have := hr j; simp only [BT.rd, if_pos hj] at this
      rw [this, List.getD_eq_default _ _ (by omega)]
  · rw [if_neg hj, List.getD_eq_default _ _ (by simp; omega)]

theorem inv_inputs {D : ℕ} : ∀ (l : List ℕ) (st : BT × ℕ) (cs : List ℕ), Inv D st cs → cs.length + l.length ≤ 2 ^ D →
    Inv D (l.foldl (push D) st) (cs ++ l) := by
  intro l
  induction l with
  | nil => intro st cs h _; simpa using h
  | cons c l ih =>
    intro st cs h hl
    have := ih (push D st c) (cs ++ [c]) (inv_push h c (by simp at hl; omega)) (by simp at hl ⊢; omega)
    simpa using this

theorem gateColT_eq {N D : ℕ} {st : BT × ℕ} {cs : List ℕ} (h : Inv D st cs) (g : Gate) :
    gateColT N D g st.1 = gateCol N g cs := by
  have e : (g.inputs.map fun a => st.1.rd D a) = (g.inputs.map fun a => cs.getD a 0) :=
    List.map_congr_left (fun a _ => h.2.2 a)
  unfold gateColT gateCol; rw [e] <;> cases g.op <;> rfl

theorem inv_gates {N D : ℕ} : ∀ (gs : List Gate) (st : BT × ℕ) (cs : List ℕ), Inv D st cs →
    cs.length + gs.length ≤ 2 ^ D →
    Inv D (gs.foldl (fun st g => push D st (gateColT N D g st.1)) st)
      (gs.foldl (fun cs g => cs ++ [gateCol N g cs]) cs) := by
  intro gs
  induction gs with
  | nil => intro st cs h _; exact h
  | cons g gs ih =>
    intro st cs h hl
    simp only [List.foldl_cons]
    rw [gateColT_eq h g]
    exact ih _ _ (inv_push h _ (by simp at hl; omega)) (by simp at hl ⊢; omega)

theorem tcols_eq_pcols {N D n m : ℕ} (C : Circuit) (hsz : n + m + C.gates.length ≤ 2 ^ D) (o : ℕ) :
    (tcols N D C n m).1.rd D o = (pcols N C n m).getD o 0 := by
  have h0 : Inv D (BT.zeros D, 0) [] := ⟨wf_zeros D, rfl, fun j => by simp [BT.rd, get_zeros]⟩
  have hin := inv_inputs (inCols n m) _ [] h0 (by simp [inCols]; omega)
  simp only [List.nil_append] at hin
  have := inv_gates (N := N) C.gates _ _ hin (by simp [inCols]; omega)
  exact this.2.2 o

theorem represents_of_tcols {n m N D : ℕ} (hN : n * m ≤ 2 ^ N) (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ m) (hg : aonB C = true) (hsz : n + m + C.gates.length ≤ 2 ^ D)
    (h : ((tcols N D C n m).1.rd D C.output == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  rw [tcols_eq_pcols C hsz] at h
  exact represents_of_pcols hN C rows hrows hg h

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1,t.2.2]⟩

set_option maxRecDepth 100000 in
def codes : List (Bool × Nat × Nat) := [
(true,2,240),(true,256,22),(true,257,33),(true,64,157),(true,38,259),(true,260,133),(true,258,261),(true,262,44),(true,75,209),(true,263,264),(true,265,115),(true,266,139),
(true,156,208),(true,267,268),(true,269,237),(true,26,136),(true,271,188),(true,13,272),(true,49,163),(true,273,274),(true,275,57),(true,77,187),(true,276,277),(true,114,238),
(true,87,279),(true,280,143),(true,278,281),(true,282,96),(true,182,218),(true,283,284),(false,270,285),(true,3,227),(true,35,214),(true,287,288),(true,62,217),(true,289,290),
(true,50,167),(true,89,164),(true,292,293),(true,291,294),(true,92,187),(true,296,145),(true,295,297),(true,93,131),(true,298,299),(true,300,106),(true,8,201),(true,2,302),
(true,88,138),(true,38,304),(true,303,305),(true,306,68),(true,96,196),(true,308,233),(true,307,309),(true,310,118),(true,72,176),(true,311,312),(true,179,234),(true,313,314),
(true,315,222),(false,301,316),(true,108,197),(true,4,318),(true,18,166),(true,320,60),(true,321,230),(true,319,322),(true,62,237),(true,323,324),(true,73,108),(true,326,198),
(true,325,327),(true,107,234),(true,328,329),(true,330,112),(true,331,130),(true,332,249),(true,29,183),(true,32,186),(true,335,205),(true,334,336),(true,50,187),(true,337,338),
(true,16,53),(true,339,340),(true,16,106),(true,342,144),(true,341,343),(true,27,128),(true,344,345),(true,88,185),(true,347,193),(true,346,348),(false,333,349),(true,10,241),
(true,351,149),(true,4,352),(true,353,17),(true,354,42),(true,46,156),(true,356,161),(true,355,357),(true,358,51),(true,81,213),(true,359,360),(true,361,84),(true,362,162),
(true,363,170),(true,364,255),(true,69,192),(true,16,366),(true,58,93),(true,367,368),(true,67,228),(true,370,141),(true,371,206),(true,369,372),(true,373,82),(true,374,86),
(true,375,126),(true,175,208),(true,376,377),(true,177,189),(true,378,379),(false,365,380),(true,6,216),(true,11,18),(true,383,85),(true,382,384),(true,385,259),(true,386,80),
(true,101,253),(true,388,110),(true,387,389),(true,390,196),(true,202,244),(true,392,252),(true,391,393),(true,394,234),(true,66,69),(true,126,231),(true,76,397),(true,398,82),
(true,396,399),(true,111,190),(true,401,211),(true,400,402),(true,123,209),(true,271,404),(true,403,405),(true,186,188),(true,406,407),(true,408,220),(false,395,409),(true,7,368),
(true,61,110),(true,411,412),(true,264,151),(true,413,414),(true,415,121),(true,127,129),(true,417,145),(true,418,210),(true,416,419),(true,420,130),(true,421,185),(true,93,199),
(true,422,423),(true,14,243),(true,32,51),(true,425,426),(true,33,246),(true,427,428),(true,429,63),(true,82,176),(true,430,431),(true,432,102),(true,433,318),(true,434,128),
(true,435,140),(true,436,202),(true,437,225),(false,424,438),(true,7,340),(true,440,48),(true,51,131),(true,441,442),(true,443,71),(true,74,147),(true,445,250),(true,446,160),
(true,444,447),(true,448,92),(true,142,223),(true,449,450),(true,451,268),(true,11,141),(true,453,227),(true,4,454),(true,23,153),(true,455,456),(true,44,96),(true,457,458),
(true,459,69),(true,113,215),(true,460,461),(true,121,235),(true,462,463),(true,464,135),(true,465,159),(true,466,163),(false,452,467),(true,3,259),(true,469,9),(true,30,53),
(true,470,471),(true,83,138),(true,472,473),(true,84,404),(true,475,237),(true,474,476),(true,477,204),(true,207,255),(true,478,479),(true,480,248),(true,10,217),(true,482,25),
(true,12,66),(true,483,484),(true,320,137),(true,485,486),(true,487,368),(true,212,251),(true,71,489),(true,488,490),(true,140,143),(true,492,208),(true,491,493),(false,481,494),
(true,14,138),(true,28,35),(true,496,497),(true,39,235),(true,498,499),(true,500,62),(true,501,66),(true,155,181),(true,86,503),(true,502,504),(true,505,104),(true,506,192),
(true,205,210),(true,508,208),(true,507,509),(true,17,219),(true,382,511),(true,19,87),(true,513,47),(true,514,255),(true,512,515),(true,70,163),(true,517,96),(true,516,518),
(true,97,141),(true,519,520),(true,521,164),(true,522,167),(true,523,185),(false,510,524),(true,111,181),(true,2,526),(true,527,15),(true,91,253),(true,73,529),(true,528,530),
(true,531,121),(true,124,230),(true,533,171),(true,532,534),(true,125,211),(true,536,164),(true,537,200),(true,535,538),(true,539,208),(true,1,89),(true,541,135),(true,542,9),
(true,26,130),(true,543,544),(true,545,27),(true,68,245),(true,546,547),(true,72,166),(true,548,549),(true,173,229),(true,550,551),(true,552,232),(true,36,239),(true,553,554),
(false,540,555),(true,16,220),(true,557,182),(true,558,18),(true,559,20),(true,47,131),(true,561,126),(true,560,562),(true,563,77),(true,564,105),(true,565,463),(true,130,175),
(true,566,567),(true,161,228),(true,568,569),(true,8,192),(true,571,61),(true,12,45),(true,573,167),(true,572,574),(true,65,132),(true,575,576),(true,95,144),(true,81,578),
(true,577,579),(true,103,227),(true,580,581),(true,582,148),(true,583,162),(true,584,184),(false,570,585),(true,41,52),(true,587,118),(true,557,588),(true,42,110),(true,590,224),
(true,591,216),(true,589,592),(true,116,197),(true,593,594),(true,122,238),(true,595,596),(true,597,130),(true,598,137),(true,599,152),(true,320,147),(true,0,601),(true,28,180),
(true,602,603),(true,604,428),(true,605,50),(true,66,165),(true,606,607),(true,608,93),(true,609,94),(true,156,173),(true,610,611),(true,612,242),(false,600,613),(true,511,31),
(true,41,177),(true,616,170),(true,615,617),(true,73,139),(true,618,619),(true,13,80),(true,621,138),(true,620,622),(true,97,221),(true,623,624),(true,102,146),(true,625,626),
(true,627,165),(true,558,515),(true,35,174),(true,630,186),(true,629,631),(true,632,91),(true,633,461),(true,634,117),(true,128,181),(true,635,636),(false,628,637),(true,0,145),
(true,639,3),(true,640,212),(true,641,527),(true,642,17),(true,87,194),(true,643,644),(true,119,172),(true,645,646),(true,647,404),(true,648,551),(true,59,103),(true,650,159),
(true,24,651),(true,72,82),(true,652,653),(true,83,105),(true,654,655),(true,85,185),(true,657,202),(true,656,658),(true,659,132),(true,660,151),(true,175,232),(true,661,662),
(true,663,183),(false,649,664),(true,12,17),(true,15,249),(true,666,667),(true,1,668),(true,669,336),(true,670,33),(true,101,133),(true,671,672),(true,105,192),(true,673,674),
(true,675,163),(true,676,214),(true,677,222),(true,39,194),(true,5,679),(true,680,158),(true,2,681),(true,682,56),(true,683,308),(true,98,195),(true,97,685),(true,684,686),
(true,626,246),(true,687,688),(true,198,218),(true,689,690),(false,678,691),(true,456,554),(true,38,151),(true,693,694),(true,695,50),(true,696,412),(true,697,85),(true,698,120),
(true,699,493),(true,700,149),(true,701,191),(true,33,46),(true,8,703),(true,704,343),(true,705,271),(true,75,158),(true,706,707),(true,708,102),(true,709,148),(true,199,221),
(true,710,711),(true,216,245),(true,712,713),(false,702,714),(true,24,144),(true,160,218),(true,716,717),(true,30,100),(true,719,255),(true,718,720),(true,721,694),(true,722,607),
(true,70,71),(true,723,724),(true,725,91),(true,726,137),(true,727,227),(true,36,135),(true,729,123),(true,21,730),(true,731,54),(true,56,173),(true,732,733),(true,734,281),
(true,134,213),(true,735,736),(true,57,185),(true,738,176),(true,737,739),(false,728,740),(true,76,128),(true,742,211),(true,5,743),(true,744,24),(true,30,252),(true,745,746),
(true,75,103),(true,747,748),(true,293,237),(true,749,750),(true,751,379),(true,57,201),(true,752,753),(true,603,202),(true,6,755),(true,756,82),(true,757,668),(true,758,653),
(true,111,238),(true,760,241),(true,759,761),(true,762,137),(true,763,207),(true,764,224),(false,754,765),(true,117,244),(true,8,767),(true,768,252),(true,31,149),(true,769,770),
(true,43,208),(true,772,74),(true,773,67),(true,771,774),(true,55,259),(true,775,776),(true,777,690),(true,778,226),(true,23,52),(true,780,651),(true,94,203),(true,781,782),
(true,40,97),(true,784,190),(true,783,785),(true,99,212),(true,787,224),(true,786,788),(true,789,140),(true,790,189),(true,791,253),(false,779,792),(true,27,230),(true,601,794),
(true,795,770),(true,796,35),(true,797,274),(true,71,253),(true,798,799),(true,800,626),(true,801,125),(true,802,210),(true,4,25),(true,804,32),(true,43,153),(true,806,196),
(true,807,152),(true,805,808),(true,809,46),(true,87,155),(true,810,811),(true,92,168),(true,812,813),(true,112,246),(true,814,815),(true,816,489),(false,803,817),(true,426,412),
(true,819,619),(true,820,707),(true,821,79),(true,822,402),(true,823,228),(true,824,761),(true,111,247),(true,825,826),(true,22,55),(true,828,188),(true,829,38),(true,830,43),
(true,831,562),(true,832,94),(true,124,159),(true,833,834),(true,835,636),(true,220,254),(true,836,837),(true,838,223),(false,827,839),(true,37,89),(true,841,772),(true,842,338),
(true,843,742),(true,844,513),(true,123,225),(true,845,846),(true,847,147),(true,848,180),(true,849,218),(true,19,245),(true,850,851),(true,15,63),(true,29,80),(true,854,171),
(true,174,251),(true,855,856),(true,853,857),(true,58,178),(true,47,859),(true,858,860),(true,60,206),(true,861,862),(true,122,131),(true,863,864),(true,865,190),(true,866,227),
(false,852,867),(true,0,63),(true,869,156),(true,870,841),(true,871,74),(true,872,815),(true,873,120),(true,169,211),(true,874,875),(true,876,172),(true,877,181),(true,878,226),
(true,879,667),(true,29,244),(true,6,881),(true,13,221),(true,882,883),(true,36,174),(true,885,190),(true,886,218),(true,884,887),(true,888,518),(true,889,581),(true,44,143),
(true,890,891),(false,880,892),(true,41,859),(true,29,894),(true,53,79),(true,895,896),(true,95,254),(true,897,898),(true,150,237),(true,899,900),(true,901,171),(true,90,184),
(true,902,903),(true,904,215),(true,101,228),(true,905,906),(true,10,168),(true,36,127),(true,908,909),(true,61,248),(true,911,154),(true,912,96),(true,913,772),(true,910,914),
(true,915,49),(true,916,93),(true,917,875),(true,918,479),(false,907,919),(true,883,405),(true,40,182),(true,921,922),(true,42,200),(true,923,924),(true,72,201),(true,926,242),
(true,925,927),(true,928,112),(true,929,127),(true,930,161),(true,828,166),(true,497,254),(true,932,933),(true,934,46),(true,85,155),(true,935,936),(true,937,162),(true,61,236),
(true,938,939),(true,940,911),(true,941,776),(false,931,942),(true,320,172),(true,944,156),(true,945,24),(true,946,891),(true,947,357),(true,77,219),(true,948,949),(true,950,431),
(true,951,299),(true,952,114),(true,48,55),(true,954,59),(true,65,183),(true,955,956),(true,957,84),(true,13,110),(true,959,206),(true,958,960),(true,120,209),(true,962,215),
(true,961,963),(true,195,221),(true,964,965),(true,966,233),(true,967,243),(false,953,968),(true,14,48),(true,970,201),(true,21,164),(true,972,129),(true,971,973),(true,27,104),
(true,974,975),(true,60,188),(true,977,250),(true,976,978),(true,78,245),(true,979,980),(true,981,456),(true,982,236),(true,738,189),(true,454,984),(true,985,911),(true,986,95),
(true,987,674),(true,988,109),(true,112,252),(true,989,990),(true,991,122),(true,992,243),(false,983,993),(true,29,114),(true,995,229),(true,996,40),(true,997,954),(true,998,811),
(true,999,782),(true,115,143),(true,1000,1001),(true,146,184),(true,1002,1003),(true,1004,163),(true,1005,174),(true,11,145),(true,1007,71),(true,1008,251),(true,351,1009),(true,1010,959),
(true,1011,927),(true,1012,348),(true,1013,97),(true,1014,220),(false,1006,1015),(true,39,259),(true,1017,191),(true,471,1018),(true,1019,61),(true,63,179),(true,1020,1021),(true,80,128),
(true,1022,1023),(true,1024,534),(true,141,212),(true,1025,1026),(true,23,104),(true,40,103),(true,1028,1029),(true,1030,616),(true,1031,54),(true,1032,447),(true,1033,473),(true,1034,106),
(true,1035,161),(true,1036,837),(false,1027,1037),(true,57,177),(true,54,1039),(true,554,1040),(true,78,124),(true,1042,240),(true,1041,1043),(true,1044,431),(true,91,98),(true,1045,1046),
(true,1047,1026),(true,1048,711),(true,1,242),(true,1050,484),(true,1051,746),(true,356,200),(true,1052,1053),(true,108,214),(true,85,1055),(true,1054,1056),(true,1057,116),(true,1058,1003),
(true,1059,248),(false,1049,1060),(true,15,562),(true,56,165),(true,1062,1063),(true,79,662),(true,1064,1065),(true,279,197),(true,1066,1067),(true,1068,124),(true,125,155),(true,1069,1070),
(true,1071,875),(true,34,58),(true,1073,261),(true,181,188),(true,1018,1075),(true,1074,1076),(true,61,244),(true,1077,1078),(true,91,171),(true,1079,1080),(true,1081,334),(false,1072,1082),
(true,322,617),(true,1084,504),(true,1085,1056),(true,1086,113),(true,1087,279),(true,542,34),(true,1089,372),(true,1090,445),(true,1091,121),(true,1092,407),(true,1093,624),(false,1088,1094),
(true,12,152),(true,20,36),(true,1096,1097),(true,1098,1039),(true,259,134),(true,1099,1100),(true,1101,86),(true,1102,106),(true,1103,963),(true,1104,173),(true,1105,249),(true,145,171),
(true,50,1107),(true,975,1108),(true,1109,576),(true,1110,724),(true,74,239),(true,1111,1112),(true,1113,1070),(true,1114,135),(true,1115,284),(false,1106,1116),(true,542,1063),(true,77,156),
(true,1119,233),(true,1118,1120),(true,1121,579),(true,1122,83),(true,1123,419),(true,482,119),(true,1125,117),(true,1126,476),(true,1127,389),(true,1128,826),(true,1129,736),(true,1130,142),
(false,1124,1131),(true,45,95),(true,1133,1112),(true,304,162),(true,1134,1135),(true,1136,297),(true,1137,686),(true,1138,1001),(true,1139,216),(true,57,213),(true,1141,252),(true,869,1142),
(true,1143,327),(true,1144,399),(true,1145,150),(true,1146,159),(true,219,230),(true,1147,1148),(false,1140,1149),(true,20,21),(true,1151,147),(true,1152,718),(true,1153,80),(true,1154,520),
(true,1155,909),(true,1156,245),(true,1157,246),(true,1158,898),(true,45,244),(true,773,1160),(true,1161,309),(true,1162,99),(true,106,191),(true,1164,114),(true,1163,1165),(true,1166,596),
(true,1167,509),(false,1159,1168),(true,22,200),(true,513,1170),(true,1171,984),(true,1172,549),(true,1173,720),(true,159,202),(true,1174,1175),(true,1176,903),(true,77,117),(true,1178,145),
(true,425,1179),(true,1180,672),(true,1181,626),(true,1182,122),(true,1183,161),(true,1184,908),(true,646,217),(true,1185,1186),(false,1177,1187),(true,65,105),(true,739,1189),(true,1190,78),
(true,97,536),(true,1191,1192),(true,1193,100),(true,118,163),(true,1194,1195),(true,1196,1107),(true,150,217),(true,1197,1198),(true,1152,288),(true,1200,69),(true,1201,936),(true,1202,88),
(true,110,203),(true,1203,1204),(true,1205,126),(true,1206,140),(true,1207,179),(true,1208,242),(true,1209,247),(false,1199,1210),(true,88,178),(true,26,1212),(true,1213,1165),(true,1214,329),
(true,1215,115),(true,1216,123),(true,1217,1070),(true,169,199),(true,1218,1219),(true,173,226),(true,1220,1221),(true,352,1096),(true,52,176),(true,1224,210),(true,1225,108),(true,1223,1226),
(true,1227,896),(true,1228,99),(true,1229,132),(true,1230,926),(true,1231,223),(false,1222,1232),(true,302,13),(true,1234,973),(true,1235,1192),(true,1236,107),(true,1237,111),(true,1238,417),
(true,139,173),(true,1239,1240),(true,1241,144),(true,1242,180),(true,3,60),(true,1244,799),(true,1245,1179),(true,1246,1043),(true,1247,397),(true,1248,169),(true,1249,713),(true,1250,241),
(false,1243,1251),(true,384,21),(true,1253,30),(true,1254,912),(true,115,152),(true,1255,1256),(true,1257,417),(true,165,201),(true,1259,249),(true,1258,1260),(true,1261,194),(true,933,806),
(true,1263,58),(true,1264,59),(true,72,203),(true,1265,1266),(true,1267,296),(true,1268,401),(true,1269,133),(true,1270,1240),(false,1262,1271),(true,1,1161),(true,1273,914),(true,1274,611),
(true,181,217),(true,1275,1276),(true,29,117),(true,1277,1278),(true,5,588),(true,1280,607),(true,78,243),(true,1281,1282),(true,1283,1164),(true,1284,461),(true,1285,139),(true,1286,148),
(true,1287,176),(true,1288,253),(false,1279,1289),(true,4,895),(true,1291,1078),(true,1292,102),(true,1293,1067),(true,1294,533),(true,1295,144),(true,1296,1219),(true,256,121),(true,1298,165),
(true,1299,47),(true,1300,13),(true,40,247),(true,1301,1302),(true,1303,52),(true,89,97),(true,1305,150),(true,1306,196),(true,1304,1307),(true,1308,450),(true,1309,214),(false,1297,1310),
(true,704,20),(true,1312,857),(true,1313,490),(true,1314,1120),(true,1315,172),(true,1316,238),(true,733,91),(true,11,1318),(true,1319,601),(true,30,90),(true,1320,1321),(true,1322,617),
(true,43,154),(true,1323,1324),(true,1325,143),(true,1326,204),(false,1317,1327),(true,0,486),(true,1329,851),(true,1330,932),(true,1331,746),(true,1332,31),(true,1333,120),(true,1334,135),
(true,1335,393),(true,1336,237),(true,27,88),(true,12,1338),(true,1339,1028),(true,78,205),(true,1341,249),(true,1340,1342),(true,1343,360),(true,111,226),(true,1344,1345),(true,1346,215),
(true,1347,1148),(true,1348,225),(false,1337,1349),(true,1073,681),(true,1351,1053),(true,1352,744),(true,1353,86),(true,1354,1345),(true,1355,223),(true,1009,971),(true,28,259),(true,1357,1358),
(true,1359,423),(true,1360,113),(true,1361,717),(true,1362,225),(false,1356,1363),(true,319,960),(true,1365,35),(true,1366,81),(true,1367,1135),(true,1368,533),(true,1369,136),(true,1370,569),
(true,1050,499),(true,1372,956),(true,1373,1342),(true,1374,855),(true,1375,96),(true,1376,996),(true,1377,253),(false,1371,1378),(true,1319,367),(true,1380,1040),(true,1381,1021),(true,131,150),
(true,1382,1383),(true,1384,1063),(true,1385,224),(true,544,679),(true,1387,859),(true,1388,398),(true,1389,1065),(true,1390,990),(true,120,178),(true,1391,1392),(true,1393,210),(false,1386,1394),
(true,471,924),(true,1396,370),(true,115,138),(true,1397,1398),(true,1399,116),(true,1400,117),(true,1401,900),(true,1402,168),(true,1212,205),(true,1403,1404),(true,1300,8),(true,1406,23),
(true,1407,887),(true,1408,54),(true,1409,401),(true,1410,203),(true,1411,217),(true,1412,234),(false,1405,1413),(true,7,978),(true,66,87),(true,1416,225),(true,1415,1417),(true,366,74),
(true,1418,1419),(true,1420,788),(true,1421,119),(true,1422,252),(true,20,89),(true,1339,1424),(true,1425,922),(true,1426,80),(true,1427,1080),(true,1428,1135),(true,1429,154),(true,1430,377),
(true,1431,186),(false,1423,1432),(true,882,841),(true,1434,694),(true,1435,53),(true,1436,738),(true,1437,64),(true,1438,293),(true,1439,965),(true,1440,247),(true,1441,253),(true,25,197),
(true,1096,1443),(true,1444,774),(true,1445,1046),(true,1446,1392),(true,1447,1175),(true,1448,196),(true,1449,203),(false,1442,1450),(true,639,302),(true,1452,35),(true,1453,592),(true,1454,360),
(true,1455,141),(true,1456,883),(true,1457,939),(true,3,1189),(true,1459,238),(true,1460,603),(true,1461,860),(true,1462,1186),(true,1463,834),(true,1464,162),(true,1465,197),(true,1466,250),
(false,1458,1467),(true,829,290),(true,1469,264),(true,1470,655),(true,1471,906),(true,1472,1260),(true,15,195),(true,1473,1474),(true,287,769),(true,1476,603),(true,1477,785),(true,1478,576),
(true,1479,846),(true,1480,200),(false,1475,1481),(true,1278,1133),(true,1483,1063),(true,1484,547),(true,90,101),(true,1485,1486),(true,1487,154),(true,160,198),(true,1489,209),(true,1488,1490),
(true,1491,182),(true,1492,255),(true,1076,98),(true,1494,99),(true,1495,748),(true,1256,119),(true,1497,158),(true,1496,1498),(true,1499,1198),(false,1493,1500),(true,574,1100),(true,1502,1419),
(true,1503,949),(true,1504,594),(true,1505,179),(true,1506,846),(true,1007,19),(true,1508,922),(true,1509,442),(true,1510,414),(true,1511,1023),(true,113,119),(true,1513,248),(true,1512,1514),
(true,1515,241),(false,1507,1516),(true,483,679),(true,1518,274),(true,1519,1417),(true,1520,750),(true,1521,116),(true,1522,154),(true,1523,219),(true,26,126),(true,1525,171),(true,12,1526),
(true,1527,862),(true,69,181),(true,1529,212),(true,1528,1530),(true,1531,658),(true,1532,93),(true,1533,112),(true,1534,139),(true,1535,153),(false,1524,1536),(true,42,1530),(true,1538,1282),
(true,1539,90),(true,1540,92),(true,1541,98),(true,1542,688),(true,149,193),(true,1543,1544),(true,1545,401),(true,1170,28),(true,1547,39),(true,1112,81),(true,1548,1549),(true,1550,1067),
(true,1551,1498),(true,1552,1221),(false,1546,1553),(true,622,631),(true,1555,561),(true,1556,724),(true,1557,1266),(true,1558,84),(true,1559,314),(true,1560,240),(true,945,27),(true,1562,753),
(true,1563,1549),(true,1564,92),(true,1565,318),(true,1566,767),(true,1567,235),(false,1561,1568),(true,1460,496),(true,1570,939),(true,1571,530),(true,1572,1055),(true,1573,168),(true,1574,186),
(true,1575,218),(true,571,1526),(true,1577,1302),(true,1578,259),(true,1579,518),(true,1580,980),(true,1581,856),(false,1576,1582),(true,7,47),(true,1584,776),(true,1585,324),(true,1586,77),
(true,81,190),(true,1587,1588),(true,1589,1404),(true,1590,142),(true,1591,184),(true,1592,212),(true,6,730),(true,1594,1282),(true,1595,864),(true,1596,1307),(true,1597,538),(false,1593,1598),
(true,5,484),(true,1600,1324),(true,1601,292),(true,1602,738),(true,1603,813),(true,1604,1204),(true,1605,1383),(true,34,78),(true,1607,517),(true,572,1608),(true,1609,91),(true,1610,1514),
(true,1611,1490),(true,1612,239),(true,1613,1282),(false,1606,1614),(true,11,22),(true,1616,854),(true,1617,808),(true,1618,1142),(true,1619,1195),(true,1620,169),(true,1621,1588),(true,469,1443),
(true,1623,1108),(true,1624,1226),(true,1625,1341),(true,1626,685),(false,1622,1627),(true,870,305),(true,1629,549),(true,1630,277),(true,1631,113),(true,1632,186),(true,1633,1474),(true,1634,212),
(true,1635,252),(true,5,345),(true,1637,34),(true,1638,729),(true,1639,294),(true,1640,1225),(true,1641,55),(true,1642,188),(true,1643,224),(false,1636,1644),(true,15,1424),(true,1646,1608),
(true,1647,312),(true,1648,1398),(true,1649,1544),(true,1650,229),(true,1651,246),(true,1652,250),(true,641,757),(true,1654,9),(true,1655,98),(true,123,219),(true,1656,1657),(true,1658,160),
(true,1659,174),(true,1660,228),(false,1653,1661),(true,286,317),(true,1663,350),(true,1664,381),(true,1665,410),(true,1666,439),(true,1667,468),(true,1668,495),(true,1669,525),(true,1670,556),
(true,1671,586),(true,1672,614),(true,1673,638),(true,1674,665),(true,1675,692),(true,1676,715),(true,1677,741),(true,1678,766),(true,1679,793),(true,1680,818),(true,1681,840),(true,1682,868),
(true,1683,893),(true,1684,920),(true,1685,943),(true,1686,969),(true,1687,994),(true,1688,1016),(true,1689,1038),(true,1690,1061),(true,1691,1083),(true,1692,1095),(true,1693,1117),(true,1694,1132),
(true,1695,1150),(true,1696,1169),(true,1697,1188),(true,1698,1211),(true,1699,1233),(true,1700,1252),(true,1701,1272),(true,1702,1290),(true,1703,1311),(true,1704,1328),(true,1705,1350),(true,1706,1364),
(true,1707,1379),(true,1708,1395),(true,1709,1414),(true,1710,1433),(true,1711,1451),(true,1712,1468),(true,1713,1482),(true,1714,1501),(true,1715,1517),(true,1716,1537),(true,1717,1554),(true,1718,1569),
(true,1719,1583),(true,1720,1599),(true,1721,1615),(true,1722,1628),(true,1723,1645),(true,1724,1662)]

def circuit : Circuit := ⟨codes.map asGate, 1725⟩
def rows : List ℕ := ([0x0650c16f3fa4242a5a95d09c81a28695, 0x20c9e05026fb41fc80230c7648146d40, 0x0230e178464025a11ec4a3d880c385bc, 0x1ee01731633b061b5299ea78a3a3be12, 0x26850870804560132e828869106d6009, 0x1b1ac0034653a6c90c30204934020620, 0x164028a4101f2e3375271218b9204501, 0x0048080a008905300441881c86403489, 0x2623f89917533b28fe56b7f686ea940c, 0x2c400060021901020021085800209600, 0xc10026340097dd81a326ea68ba47ac82, 0x5c2053a6981f2b2d5d0df8997a0ec96f, 0xb5fbac173e1a96ddb247aa5b6c86269d, 0xe777f8e41b8b2aa005f55a4eb8078829, 0x99a8000c890e0585230048d8f0822007, 0x1070a13b2c1d075cf8b368d9600e80b5, 0x9246adc828a500658116a4ee92bdbc94, 0x90402910148d665d26e2c010c8842411, 0xcb4966df39baf83b5f8879843b192fbd, 0x0a08084e2aa56021402e5da228060c68, 0x1410c21b0e1d341193536ccd0c5b8090, 0xf13b4288070d2811ea012a2902c32a20, 0x12de405e2ebe232a5871190a60268930, 0x1538205ca51125c1a20c094170796789, 0x021a422120b7e41c82b13000000282c0, 0xb19020402036d41842200a5823ac0c00, 0x7113f4438f4f0715842b297c3fe09c38, 0x3f79244b009b0d793e2a69503b0026cc, 0x974c7035bb3a032e726300ba55262707, 0xabef655696cdfe7a9a37bf66fd5acd0d, 0x4e0bc6473eb1ac804a137963120ebee0, 0xaa40004718b02810646041008b001001, 0x62402440940600fc12200048c0ae000f, 0x0040c001150710fc9a42244847ae9306, 0x180041520c580ea80e32c7e13c420408, 0xaf54ce206b1a233402df1dfe9f462d02, 0xf374e25c25dd2198cd641b7178d74790, 0x0810000824014c304004480881008008, 0x00a24119276d0cb05a45a2b8c91389c9, 0xce6841535d5a66e3466aaabf2e6e2d28, 0x7f1650571e5302eb960c0be428232441, 0x89d54250b2d9c01094787b6034486081, 0x4545d414060149216016f064f9082000, 0x6bfae259249e6a6de3055879f5ff380a, 0x06484204a48b400818e012091008c108, 0x716a08d01ea2004090618023e1db280d, 0x280d825224975389a0c3a44b26aeb100, 0x00baf85b2d2d23b1d9b61ff4785f2cb9, 0x190e080c988803072201104ad202a089, 0x4841201000934410032409003b400820, 0x1b28e64971b242f94c0f6a497311074c, 0x4000081a988740a1322a8088a28220cf, 0x11544444063100f8cc3422683f290400, 0xcf012c4c16998cf0c006636b8f08b684, 0x910421d804542104810c892130c52605, 0x3a9e405f38ba2b1a6e511052d0429d98, 0xba9063884676200594a4d82971c14264, 0x97aff5890747af7d1d5dd93fbb8f9ebe, 0x8beb7103a56b96b5081ba7273d6a740b, 0x131000240c130244002130623522800a, 0x1128201a2e0962073ed0a81c04092c83, 0x6ced7912b3ca0fb1db77fbbfee595d2f, 0x9018060a490823124e99009800412499, 0x5430818b3507008c5a17c09f008a8487, 0xfd2ed185b67b0f747c468b7bdfca9799, 0x0aa418513be24a29104bf86e390ab54c, 0xb119e4013b33d4f10663a89d3700aec4, 0xa0934441267008086222447698a01000, 0x20000048024901009820089061420008, 0xb512e5868b2f05340645ac1f75ea440d, 0x2250d8140cff2e21063373c13d4284c8, 0x8b50e82c80ba9b3403137558ff0dacc3, 0x7318bc7d0a5f0fa4b9377bff3d0680ab, 0xc8a081209180200b1ee0684ca003848d, 0x73fb4cc92cf3084ae66bec7dafffbcc9, 0xd27ac00b9c038561d87900a9a6a09359, 0x3a12c40b0500c699481e682520428608, 0xa18b220922af571933d324d4b4dbc8fb, 0x31bcf05c0e796f31673c63df7f4f7f8a, 0xc11004059009808190ae2b20ac400029, 0xd430cad31c9f7239dc7b7cc7340a8541, 0x36fd6c30123f6d3b64ffd856a06666cc, 0xb55ea62021fe479e2ba3341e30a68407, 0x3890206a02330104c03838402002f251, 0x08108a100a154221200390621003b28a, 0x4025a0b23b1a4b845e63381a465b29a0, 0x880280122d20428016400c9f382a2090, 0xa80f29483e17660346e6dd6fbeaf0e38, 0x363f2ceb8e7c2f715b8148f88966829d, 0x3e92665b6e7befb95f3f4e59bb03ce48, 0x8908c2040219812090207b0275460020, 0x3db4c3a3287c092d1307fff83cc48ccc, 0x3309cecc48a60b7504096069c76c248a, 0xc14a6617fbaad73c018d0c1e75601605, 0x18964015150902624200000061220a04, 0xb5b07ad01a2fa25090608312e740404e, 0x6669785cc6cf60218d251bbf385b6d28, 0xb2b76af45ff72af9d56e4668a86fd421, 0xb7f4c0e46862217b47412239d7e40420, 0xd0700404040300c08444aa252c292400, 0x008c40000260080002093102080e90e0, 0x9150028a160f855cf7300360f5470192, 0x8ac1c004d0d725b1a7606168cbe2d027, 0x92724875141b84448078ba233422220d, 0x9338204809920401a20a28d8210022c1, 0x1cf4102b25720b5d5138789c6a1f3012, 0x4372a640c6150270806928413fabb495, 0x20230080810422020e81020001230011, 0x3aa58c342136689bde8f6a0c2b8ba48f, 0x04201000000002001000001002000002, 0x676ccaa2bb0e2ce157b5786fd85f918b, 0x7b33e7b6950c27b432a6a371f5c3069f, 0x6530304b2e0422075e8a607c2e6d800b, 0x05100017aa0d4925162b25b1744c6cc9, 0xc8ff2258b4d7423ad6a1082731ef6fb0, 0xd86f44d09e360e425a71602987668930, 0x0147840026124c8042736860128a2809, 0xa20906112e9e0f08f73b6470f1571c8a, 0x01d4000802452828083928f03c0a1008, 0x8068130329370f6367e889e5b4e724da, 0x22b0804f2da02089424b787a58d38198, 0x0478e17a804125a1012727c51859549d, 0xc4643002041127007b142071b2096003, 0xff5237388717661a53c5c86db9a3d69b, 0x77b7d931b1682310d1b22873704f6ca6, 0x2af7a1a081d62a10d1af2b402b2a50f4, 0xb092f41b0f68061ddfbb2dbe74738c3a, 0x61fb729203a72c30c9052a442a425861] : List ℕ)

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem good : PEqualNP.Represents.Represents
    (fun u v : Fin 128 => (rows.getD u.val 0).testBit v.val) circuit := by
  apply represents_of_tcols (N := 14) (D := 11) (by decide) circuit rows
  · have hh : rows.all (fun x => decide (x < 2 ^ 128)) = true := by decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hh x hx)
  · decide +kernel
  · decide +kernel
  · decide +kernel


end PEqualNP.Outside.L_meta_29941_aux

open PEqualNP.Outside.L_meta_29941_aux
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_29941 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 128 => (([0x0650c16f3fa4242a5a95d09c81a28695, 0x20c9e05026fb41fc80230c7648146d40, 0x0230e178464025a11ec4a3d880c385bc, 0x1ee01731633b061b5299ea78a3a3be12, 0x26850870804560132e828869106d6009, 0x1b1ac0034653a6c90c30204934020620, 0x164028a4101f2e3375271218b9204501, 0x0048080a008905300441881c86403489, 0x2623f89917533b28fe56b7f686ea940c, 0x2c400060021901020021085800209600, 0xc10026340097dd81a326ea68ba47ac82, 0x5c2053a6981f2b2d5d0df8997a0ec96f, 0xb5fbac173e1a96ddb247aa5b6c86269d, 0xe777f8e41b8b2aa005f55a4eb8078829, 0x99a8000c890e0585230048d8f0822007, 0x1070a13b2c1d075cf8b368d9600e80b5, 0x9246adc828a500658116a4ee92bdbc94, 0x90402910148d665d26e2c010c8842411, 0xcb4966df39baf83b5f8879843b192fbd, 0x0a08084e2aa56021402e5da228060c68, 0x1410c21b0e1d341193536ccd0c5b8090, 0xf13b4288070d2811ea012a2902c32a20, 0x12de405e2ebe232a5871190a60268930, 0x1538205ca51125c1a20c094170796789, 0x021a422120b7e41c82b13000000282c0, 0xb19020402036d41842200a5823ac0c00, 0x7113f4438f4f0715842b297c3fe09c38, 0x3f79244b009b0d793e2a69503b0026cc, 0x974c7035bb3a032e726300ba55262707, 0xabef655696cdfe7a9a37bf66fd5acd0d, 0x4e0bc6473eb1ac804a137963120ebee0, 0xaa40004718b02810646041008b001001, 0x62402440940600fc12200048c0ae000f, 0x0040c001150710fc9a42244847ae9306, 0x180041520c580ea80e32c7e13c420408, 0xaf54ce206b1a233402df1dfe9f462d02, 0xf374e25c25dd2198cd641b7178d74790, 0x0810000824014c304004480881008008, 0x00a24119276d0cb05a45a2b8c91389c9, 0xce6841535d5a66e3466aaabf2e6e2d28, 0x7f1650571e5302eb960c0be428232441, 0x89d54250b2d9c01094787b6034486081, 0x4545d414060149216016f064f9082000, 0x6bfae259249e6a6de3055879f5ff380a, 0x06484204a48b400818e012091008c108, 0x716a08d01ea2004090618023e1db280d, 0x280d825224975389a0c3a44b26aeb100, 0x00baf85b2d2d23b1d9b61ff4785f2cb9, 0x190e080c988803072201104ad202a089, 0x4841201000934410032409003b400820, 0x1b28e64971b242f94c0f6a497311074c, 0x4000081a988740a1322a8088a28220cf, 0x11544444063100f8cc3422683f290400, 0xcf012c4c16998cf0c006636b8f08b684, 0x910421d804542104810c892130c52605, 0x3a9e405f38ba2b1a6e511052d0429d98, 0xba9063884676200594a4d82971c14264, 0x97aff5890747af7d1d5dd93fbb8f9ebe, 0x8beb7103a56b96b5081ba7273d6a740b, 0x131000240c130244002130623522800a, 0x1128201a2e0962073ed0a81c04092c83, 0x6ced7912b3ca0fb1db77fbbfee595d2f, 0x9018060a490823124e99009800412499, 0x5430818b3507008c5a17c09f008a8487, 0xfd2ed185b67b0f747c468b7bdfca9799, 0x0aa418513be24a29104bf86e390ab54c, 0xb119e4013b33d4f10663a89d3700aec4, 0xa0934441267008086222447698a01000, 0x20000048024901009820089061420008, 0xb512e5868b2f05340645ac1f75ea440d, 0x2250d8140cff2e21063373c13d4284c8, 0x8b50e82c80ba9b3403137558ff0dacc3, 0x7318bc7d0a5f0fa4b9377bff3d0680ab, 0xc8a081209180200b1ee0684ca003848d, 0x73fb4cc92cf3084ae66bec7dafffbcc9, 0xd27ac00b9c038561d87900a9a6a09359, 0x3a12c40b0500c699481e682520428608, 0xa18b220922af571933d324d4b4dbc8fb, 0x31bcf05c0e796f31673c63df7f4f7f8a, 0xc11004059009808190ae2b20ac400029, 0xd430cad31c9f7239dc7b7cc7340a8541, 0x36fd6c30123f6d3b64ffd856a06666cc, 0xb55ea62021fe479e2ba3341e30a68407, 0x3890206a02330104c03838402002f251, 0x08108a100a154221200390621003b28a, 0x4025a0b23b1a4b845e63381a465b29a0, 0x880280122d20428016400c9f382a2090, 0xa80f29483e17660346e6dd6fbeaf0e38, 0x363f2ceb8e7c2f715b8148f88966829d, 0x3e92665b6e7befb95f3f4e59bb03ce48, 0x8908c2040219812090207b0275460020, 0x3db4c3a3287c092d1307fff83cc48ccc, 0x3309cecc48a60b7504096069c76c248a, 0xc14a6617fbaad73c018d0c1e75601605, 0x18964015150902624200000061220a04, 0xb5b07ad01a2fa25090608312e740404e, 0x6669785cc6cf60218d251bbf385b6d28, 0xb2b76af45ff72af9d56e4668a86fd421, 0xb7f4c0e46862217b47412239d7e40420, 0xd0700404040300c08444aa252c292400, 0x008c40000260080002093102080e90e0, 0x9150028a160f855cf7300360f5470192, 0x8ac1c004d0d725b1a7606168cbe2d027, 0x92724875141b84448078ba233422220d, 0x9338204809920401a20a28d8210022c1, 0x1cf4102b25720b5d5138789c6a1f3012, 0x4372a640c6150270806928413fabb495, 0x20230080810422020e81020001230011, 0x3aa58c342136689bde8f6a0c2b8ba48f, 0x04201000000002001000001002000002, 0x676ccaa2bb0e2ce157b5786fd85f918b, 0x7b33e7b6950c27b432a6a371f5c3069f, 0x6530304b2e0422075e8a607c2e6d800b, 0x05100017aa0d4925162b25b1744c6cc9, 0xc8ff2258b4d7423ad6a1082731ef6fb0, 0xd86f44d09e360e425a71602987668930, 0x0147840026124c8042736860128a2809, 0xa20906112e9e0f08f73b6470f1571c8a, 0x01d4000802452828083928f03c0a1008, 0x8068130329370f6367e889e5b4e724da, 0x22b0804f2da02089424b787a58d38198, 0x0478e17a804125a1012727c51859549d, 0xc4643002041127007b142071b2096003, 0xff5237388717661a53c5c86db9a3d69b, 0x77b7d931b1682310d1b22873704f6ca6, 0x2af7a1a081d62a10d1af2b402b2a50f4, 0xb092f41b0f68061ddfbb2dbe74738c3a, 0x61fb729203a72c30c9052a442a425861] : List ℕ).getD u.val 0).testBit v.val) 1477) := by
  exact ⟨circuit, mono, by decide +kernel, good⟩
