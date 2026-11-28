import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs
import PEqualNP.Outside.L_clb_073

namespace PEqualNP.Outside.L_clb_111_aux.FlatInput

def pair {m n : ℕ} (i : Fin m) (j : Fin n) : Fin (m * n) :=
  ⟨i.val * n + j.val, calc
    _ < i.val * n + n := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * n := by rw [Nat.add_one_mul]
    _ ≤ _ := Nat.mul_le_mul_right n i.isLt⟩

def rows {m : ℕ} (f : Fin m → List α) := (List.ofFn f).flatten

theorem rows_length {m n : ℕ} (f : Fin m → List α) (hf : ∀ i, (f i).length = n) :
    (rows f).length = m * n := by
  induction m with
  | zero => simp [rows]
  | succ m ih =>
    rw [rows, List.ofFn_succ, List.flatten_cons, List.length_append, hf,
      ← rows, ih (fun i => f i.succ) (fun i => hf i.succ)]
    rw [Nat.add_one_mul, Nat.add_comm]

theorem rows_getD {m n : ℕ} (f : Fin m → List α) (hf : ∀ i, (f i).length = n)
    (i : Fin m) (j : Fin n) (z : α) :
    (rows f).getD (pair i j).val z = (f i).getD j.val z := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun a => ?_) i
    · simp only [rows, List.ofFn_succ, List.flatten_cons, pair, Fin.val_zero, Nat.zero_mul,
        Nat.zero_add, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [hf]; exact j.isLt)]
    · simp only [rows, List.ofFn_succ, List.flatten_cons, pair, Fin.val_succ,
        Nat.add_one_mul, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [hf]; omega), hf]
      have e : a.val * n + n + j.val - n = a.val * n + j.val := by omega
      rw [e]
      exact ih (fun i => f i.succ) (fun i => hf i.succ) a

def bits (d u : ℕ) (k : Fin d) := u.testBit (d - 1 - k.val)

abbrev Dst (d b t : ℕ) := Fin t → (Fin d → Bool) → (Fin b → Bool) → Fin d → Bool

def input {d b t} (dst : Dst d b t) :=
  rows (fun h => rows (fun a : Fin (2^d) => rows (fun l : Fin (2^b) =>
    List.ofFn (dst h (bits d a.val) (bits b l.val)))))

theorem input_length {d b t} (dst : Dst d b t) :
    (input dst).length = t * 2^d * 2^b * d := by
  unfold input
  rw [rows_length (n := 2^d * (2^b * d)) _ (fun _ =>
    rows_length _ (fun _ => rows_length _ (fun _ => List.length_ofFn)))]
  simp [Nat.mul_assoc]

def physical {d b t} (h : Fin t) (a : Fin (2^d)) (l : Fin (2^b)) (k : Fin d) :
    Fin (t * 2^d * 2^b * d) := pair (pair (pair h a) l) k

theorem get_physical {d b t} (dst : Dst d b t) (h : Fin t) (a : Fin (2^d))
    (l : Fin (2^b)) (k : Fin d) :
    (input dst).getD (physical h a l k).val false = dst h (bits d a.val) (bits b l.val) k := by
  have idx : (physical h a l k).val = (pair h (pair a (pair l k))).val := by
    simp [physical, pair, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  rw [idx, input, rows_getD _ (fun _ => rows_length _ (fun _ =>
    rows_length _ (fun _ => List.length_ofFn))), rows_getD _ (fun _ =>
    rows_length _ (fun _ => List.length_ofFn)), rows_getD _ (fun _ => List.length_ofFn)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def high {d b : ℕ} (a : Fin (2^(d+b))) : Fin (2^d) :=
  ⟨a.val / 2^b, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).2 (by simpa [pow_add] using a.isLt)⟩

def low {d b : ℕ} (a : Fin (2^(d+b))) : Fin (2^b) :=
  ⟨a.val % 2^b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩

def wideDst {d b t} (dst : Dst d b t) (h : Fin t) (z : Fin (d+b) → Bool) : Fin (d+b) → Bool :=
  Fin.append (dst h (fun i => z (Fin.castAdd b i)) (fun j => z (Fin.natAdd d j))) (fun _ => false)

def inputIndex {d b t} (h : Fin t) (k : Fin (2^(d+b)*(d+b))) : Option (Fin (t*2^d*2^b*d)) :=
  let a : Fin (2^(d+b)) := k.divNat
  let j : Fin (d+b) := k.modNat
  if hj : j.val < d then some (physical h (high a) (low a) ⟨j.val,hj⟩) else none

theorem split_high {d b : ℕ} (a : Fin (2^(d+b))) :
    (fun i : Fin d => bits (d+b) a.val (Fin.castAdd b i)) = bits d (high a).val := by
  funext i
  simp only [bits, high, Fin.val_castAdd, Nat.testBit_div_two_pow]
  congr 1
  omega

theorem split_low {d b : ℕ} (a : Fin (2^(d+b))) :
    (fun j : Fin b => bits (d+b) a.val (Fin.natAdd d j)) = bits b (low a).val := by
  funext j
  simp only [bits, low, Fin.val_natAdd, Nat.testBit_mod_two_pow]
  have h : b - 1 - j.val < b := by omega
  simp [h, show d + b - 1 - (d + j.val) = b - 1 - j.val by omega]

theorem div_pair {m n : ℕ} (a : Fin m) (j : Fin n) : (pair a j).divNat = a := by
  apply Fin.ext
  change (a.val * n + j.val) / n = a.val
  rw [Nat.mul_comm a.val n, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt),
    Nat.div_eq_of_lt j.isLt, Nat.add_zero]

theorem mod_pair {m n : ℕ} (a : Fin m) (j : Fin n) : (pair a j).modNat = j := by
  apply Fin.ext
  change (a.val * n + j.val) % n = j.val
  simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

theorem remap_input {d b t} (dst : Dst d b t) (h : Fin t) :
    List.ofFn (fun k => ((inputIndex (d := d) (b := b) h k).map
      (fun r => (input dst).getD r.val false)).getD false) =
      (List.ofFn (fun a : Fin (2^(d+b)) => List.ofFn (wideDst dst h (bits (d+b) a.val)))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext j
  change ((inputIndex h (pair a j)).map _).getD false = _
  unfold inputIndex
  simp only [div_pair, mod_pair, wideDst, split_high, split_low]
  refine Fin.addCases (fun i => ?_) (fun l => ?_) j
  · simp only [Fin.val_castAdd, i.isLt, dite_true, Option.map_some, Option.getD_some, Fin.append_left]
    exact get_physical dst h (high a) (low a) i
  · simp [show ¬ d + l.val < d by omega]

end PEqualNP.Outside.L_clb_111_aux.FlatInput

namespace PEqualNP.Outside.L_clb_111_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

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

theorem spliceMany_exists {I Isub : Nat} (k : Nat) (b : Builder I) (sub : Circuit)
    (hFan : FanInTwo sub) (hRB : ReadsBack Isub sub)
    (inpMap : Fin k → Fin Isub → Nat) (hinp : ∀ h i, inpMap h i < I + b.size) :
    ∃ (b' : Builder I) (out : Fin k → Fin (Isub + sub.size) → Nat),
      Extends b b' ∧ b'.size = b.size + k * sub.size ∧
      (∀ h w, out h w < I + b'.size) ∧
      ∀ (x : List Bool), x.length = I → ∀ h w,
        evalWire b'.gates x (out h w) =
          (sub.wires (List.ofFn (fun i => evalWire b.gates x (inpMap h i)))).getD w.val false := by
  induction k generalizing b with
  | zero =>
      refine ⟨b, fun h => Fin.elim0 h, Extends.refl b, by simp, ?_, ?_⟩
      · intro h; exact Fin.elim0 h
      · intro x hx h; exact Fin.elim0 h
  | succ k ih =>
      obtain ⟨b1, hb1, hs1, he1⟩ := spliceSub_exists b sub hFan hRB (inpMap 0) (hinp 0)
      let first : Fin (Isub + sub.size) → Nat := fun w =>
        if h : w.val < Isub then inpMap 0 ⟨w.val, h⟩ else I + b.size + (w.val - Isub)
      have hfbound (w : Fin (Isub + sub.size)) : first w < I + b1.size := by
        have he := he1 (List.replicate I false) (by simp) w.val w.isLt
        exact he.1
      obtain ⟨b2, outs, hb2, hs2, ho2, he2⟩ := ih b1
        (fun h => inpMap h.succ) (fun h i => hb1.bound (hinp h.succ i))
      let out : Fin (k+1) → Fin (Isub + sub.size) → Nat := Fin.cases first outs
      refine ⟨b2, out, hb1.trans hb2, ?_, ?_, ?_⟩
      · rw [hs2, hs1, Nat.succ_mul]
        omega
      · intro h w
        refine Fin.cases ?_ (fun j => ?_) h
        · exact hb2.bound (hfbound w)
        · exact ho2 j w
      · intro x hx h w
        refine Fin.cases ?_ (fun j => ?_) h
        · change evalWire b2.gates x (first w) = _
          rw [hb2.eval_eq x hx (hfbound w)]
          exact (he1 x hx w.val w.isLt).2
        · change evalWire b2.gates x (outs j w) = _
          rw [he2 x hx j w]
          congr 2
          apply congrArg List.ofFn
          funext i
          exact hb1.eval_eq x hx (hinp j.succ i)

theorem complementMany_exists {I : Nat} (b : Builder I) :
    ∃ (b' : Builder I) (neg : Fin (I + b.size) → Nat),
      Extends b b' ∧ b'.size = b.size + (I + b.size) ∧
      (∀ w, neg w < I + b'.size) ∧
      ∀ (x : List Bool), x.length = I → ∀ w,
        evalWire b'.gates x (neg w) = !(evalWire b.gates x w.val) := by
  let sub : Circuit := ⟨[⟨GateOp.not, [0]⟩], 0⟩
  have hFan : FanInTwo sub := by simp [FanInTwo, sub]
  have hRB : ReadsBack 1 sub := by
    intro j hj i hi
    have hj0 : j = 0 := by change j < 1 at hj; omega
    subst j
    have hi0 : i = 0 := by simpa [sub, gateAt] using hi
    subst i
    decide
  obtain ⟨b', outs, hb, hs, ho, he⟩ := spliceMany_exists (I + b.size) b sub hFan hRB
    (fun w _ => w.val) (fun w _ => w.isLt)
  let neg : Fin (I + b.size) → Nat := fun w => outs w ⟨1, by simp [sub, Circuit.size]⟩
  refine ⟨b', neg, hb, ?_, ?_, ?_⟩
  · simpa [sub, Circuit.size] using hs
  · intro w; exact ho w _
  · intro x hx w
    have h := he x hx w ⟨1, by simp [sub, Circuit.size]⟩
    simpa [neg, sub, Circuit.wires, GateOp.eval, List.ofFn_succ] using h

theorem compileCopies {I Isub : Nat} (t : Nat) (sub : Circuit)
    (hFan : FanInTwo sub) (hRB : ReadsBack Isub sub)
    (inputs : Fin t → Fin Isub → Option (Fin I)) :
    ∃ (C : Circuit) (constant : Bool → Fin (I + C.size))
      (out : Fin t → Fin (Isub + sub.size) → Bool → Fin (I + C.size)),
      FanInTwo C ∧ ReadsBack I C ∧ C.output < I + C.size ∧
      C.size = I + 4 + 2 * t * sub.size ∧
      ∀ x : List Bool, x.length = I →
        (∀ b, (C.wires x).getD (constant b).val false = b) ∧
        ∀ h w b, (C.wires x).getD (out h w b).val false =
          if b then (sub.wires (List.ofFn (fun k =>
            ((inputs h k).map (fun i => x.getD i.val false)).getD false))).getD w.val false
          else !((sub.wires (List.ofFn (fun k =>
            ((inputs h k).map (fun i => x.getD i.val false)).getD false))).getD w.val false) := by
  let bF := mkFalse (Builder.empty I)
  obtain ⟨hFe, hFs, hFw, hFv⟩ := mkFalse_spec (Builder.empty I)
  let bT := mkTrue bF.1
  obtain ⟨hTe, hTs, hTw, hTv⟩ := mkTrue_spec bF.1
  have hsize : bT.1.size = 2 := by
    simp [bT, bF, mkTrue, mkFalse, addGate, Builder.size, Builder.empty]
  have hfalse : bF.2 < I + bT.1.size := hTe.bound hFw
  let inpMap : Fin t → Fin Isub → Nat := fun h k =>
    ((inputs h k).map Fin.val).getD bF.2
  have hinp : ∀ h k, inpMap h k < I + bT.1.size := by
    intro h k
    cases he : inputs h k with
    | none => simpa [inpMap, he] using hfalse
    | some i => simpa [inpMap, he] using (lt_of_lt_of_le i.isLt (Nat.le_add_right I _))
  have inp_eval (x : List Bool) (hx : x.length = I) (h : Fin t) (k : Fin Isub) :
      evalWire bT.1.gates x (inpMap h k) =
        ((inputs h k).map (fun i => x.getD i.val false)).getD false := by
    cases he : inputs h k with
    | none =>
        simp only [inpMap, he, Option.map_none, Option.getD_none]
        rw [hTe.eval_eq x hx hFw]
        exact hFv x hx
    | some i =>
        simp only [inpMap, he, Option.map_some, Option.getD_some]
        exact wires_prefix_getD bT.1.gates x i.val (by simp [hx])
  obtain ⟨b, outputs, hb, hs, how, hev⟩ :=
    spliceMany_exists t bT.1 sub hFan hRB inpMap hinp
  obtain ⟨b', neg, hn, hns, hnw, hnv⟩ := complementMany_exists b
  have hTb : Extends bT.1 b' := hb.trans hn
  have hcfalse : bF.2 < I + b'.size := hTb.bound hfalse
  have hctrue : bT.2 < I + b'.size := hTb.bound hTw
  let C : Circuit := ⟨b'.gates, bF.2⟩
  let constant : Bool → Fin (I + C.size) := fun v =>
    if v then ⟨bT.2, hctrue⟩ else ⟨bF.2, hcfalse⟩
  let out : Fin t → Fin (Isub + sub.size) → Bool → Fin (I + C.size) := fun h w v =>
    if v then ⟨outputs h w, hn.bound (how h w)⟩ else ⟨neg ⟨outputs h w, how h w⟩, hnw _⟩
  refine ⟨C, constant, out, b'.hFan, b'.hRB, hcfalse, ?_, ?_⟩
  · change b'.size = I + 4 + 2 * t * sub.size
    rw [hns, hs, hsize]
    simp only [Nat.mul_assoc]
    omega
  · intro x hx
    constructor
    · intro v
      cases v
      · change evalWire b'.gates x bF.2 = false
        rw [hTb.eval_eq x hx hfalse, hTe.eval_eq x hx hFw]
        exact hFv x hx
      · change evalWire b'.gates x bT.2 = true
        rw [hTb.eval_eq x hx hTw]
        exact hTv x hx
    · intro h w v
      have he := hev x hx h w
      have hinputs : List.ofFn (fun k => evalWire bT.1.gates x (inpMap h k)) =
          List.ofFn (fun k => ((inputs h k).map (fun i => x.getD i.val false)).getD false) := by
        apply congrArg List.ofFn
        funext k
        exact inp_eval x hx h k
      rw [hinputs] at he
      cases v
      · change evalWire b'.gates x (neg ⟨outputs h w, how h w⟩) = _
        rw [hnv x hx, he]
        rfl
      · change evalWire b'.gates x (outputs h w) = _
        rw [hn.eval_eq x hx (how h w), he]
        rfl

end PEqualNP.Outside.L_clb_111_aux

namespace PEqualNP.Outside.L_clb_111_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def feedbackPack {d b : Nat} (v : Fin d → Bool) (l : Fin b → Bool) : Fin (d+b+1+1) → Bool :=
  Fin.cons false (Fin.cons false (Fin.append v l))

theorem compiledFeedback (d b t : Nat) :
    let p := d+b+1
    let w := p+1
    let rows := w*(p+2)^2
    let I := t*2^d*2^b*d
    ∃ (C : Circuit) (constant : Bool → Fin (I+C.size))
      (out : Fin t → Fin rows → (Fin w → Bool) → Bool → Fin (I+C.size))
      (fb : FlatInput.Dst d b t → Fin t → Fin rows → (Fin w → Bool) → Bool)
      (cost : Nat),
      FanInTwo C ∧ ReadsBack I C ∧ C.output < I+C.size ∧
      C.size = I+4+2*t*cost ∧ cost ≤ 128*2^p*(p+2)^3 ∧
      ∀ dst,
        (∀ z, (C.wires (FlatInput.input dst)).getD (constant z).val false = z) ∧
        (∀ h r s z, (C.wires (FlatInput.input dst)).getD (out h r s z).val false =
          if z then fb dst h r s else !(fb dst h r s)) ∧
        ∀ h v l,
          (List.finRange rows).foldl (fun (s : Fin w → Bool) r =>
            Fin.snoc (fun j : Fin p => s j.succ) (fb dst h r s)) (feedbackPack v l) =
            feedbackPack (dst h v l) (fun _ => false) := by
  intro p w rows I
  obtain ⟨sub, subout, hFan, hRB, hOutput, hSize, hRun⟩ := PEqualNP.Outside.L_clb_073 (d+b)
  obtain ⟨C, constant, outputs, hC, hCR, hCO, hCS, hCE⟩ :=
    compileCopies t sub hFan hRB (FlatInput.inputIndex (d := d) (b := b))
  let fb : FlatInput.Dst d b t → Fin t → Fin rows → (Fin w → Bool) → Bool :=
    fun dst h r s =>
      (sub.wires ((List.ofFn (fun a : Fin (2^(d+b)) =>
        List.ofFn (FlatInput.wideDst dst h (FlatInput.bits (d+b) a.val))))).flatten).getD
        (subout r s).val false
  let out : Fin t → Fin rows → (Fin w → Bool) → Bool → Fin (I+C.size) :=
    fun h r s z => outputs h (subout r s) z
  refine ⟨C, constant, out, fb, sub.size, hC, hCR, hCO, hCS, hSize, ?_⟩
  intro dst
  have he := hCE (FlatInput.input dst) (FlatInput.input_length dst)
  refine ⟨he.1, ?_, ?_⟩
  · intro h r s z
    have hr := he.2 h (subout r s) z
    rw [FlatInput.remap_input] at hr
    exact hr
  · intro h v l
    have hr := hRun (FlatInput.wideDst dst h) (Fin.append v l)
    have hf : FlatInput.wideDst dst h (Fin.append v l) =
        Fin.append (dst h v l) (fun _ : Fin b => false) := by
      simp only [FlatInput.wideDst, Fin.append_left, Fin.append_right]
    rw [hf] at hr
    exact hr

end PEqualNP.Outside.L_clb_111_aux

namespace PEqualNP.Outside.L_clb_111.Ports

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Width (d b : ℕ) := d+b+1+1
abbrev Test (w : ℕ) := Fin w → Word (w+1) → Bool

def splice {w : ℕ} (a b : Word w) (i : Fin w) : Word (w+1) := fun j =>
  if h : i.val+j.val < w then a ⟨i.val+j.val,h⟩
  else b ⟨i.val+j.val-w,by have := i.isLt; have := j.isLt; omega⟩

lemma splice_head {w : ℕ} (a b : Word w) (i : Fin w) : splice a b i 0 = a i := by
  simp [splice, i.isLt]

lemma splice_last {w : ℕ} (a b : Word w) (i : Fin w) : splice a b i (Fin.last w) = b i := by
  simp [splice, show ¬ i.val+w < w by omega]

lemma splice_zero {w : ℕ} (a b : Word (w+1)) :
    splice a b 0 = Fin.snoc a (b 0) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [splice_last, Fin.snoc_last]
  · simp [splice, Fin.snoc_castSucc, j.isLt]

def pack {d b : ℕ} (v : Word d) (l : Word b) : Word (Width d b) :=
  Fin.cons false (Fin.cons false (Fin.append v l))

def label {d b : ℕ} (a : Word (Width d b)) : Word b := fun j =>
  a (Fin.natAdd d j).succ.succ

lemma pack_label {d b : ℕ} (v : Word d) (l : Word b) : label (pack v l) = l := by
  funext j
  simp [label, pack]

def portPat {d b : ℕ} (v : Word d) (l : Word b) : Word (Width d b+1) :=
  Fin.snoc (pack v l) false

theorem portPat_inj {d b : ℕ} {v v' : Word d} {l l' : Word b}
    (h : portPat v l = portPat v' l') : v=v' ∧ l=l' := by
  have hpack : pack v l = pack v' l' := by
    simpa only [portPat, Fin.init_snoc] using congrArg Fin.init h
  constructor
  · funext j
    have H := congrFun hpack ((Fin.castAdd b j).succ.succ)
    simpa [portPat, pack] using H
  · funext j
    have H := congrFun hpack ((Fin.natAdd d j).succ.succ)
    simpa [portPat, pack] using H

lemma pack_inj {d b : ℕ} :
    Function.Injective (fun q : Word d × Word b => pack q.1 q.2) := by
  rintro ⟨v,l⟩ ⟨v',l'⟩ h
  apply Prod.ext
  · funext j
    simpa [pack] using congrFun h (Fin.castAdd b j).succ.succ
  · funext j
    simpa [pack] using congrFun h (Fin.natAdd d j).succ.succ

noncomputable def setupTest (d b : ℕ) : Test (Width d b) := by
  classical
  exact fun i pat => decide (
    (i.val = 0 → ∃ v : Word d, Fin.init pat = pack v (fun _ : Fin b => false)) ∧
    (i.val < d+2 → pat (Fin.last (Width d b)) = pat 0))

def portTest (d b : ℕ) : Test (Width d b) := fun i pat =>
  decide (i.val ≠ 0 ∧ pat (Fin.last (Width d b)) = pat 0)

lemma port_off {d b : ℕ} (pat : Word (Width d b + 1)) : portTest d b 0 pat = false := by
  simp [portTest]

lemma setup_iff {d b : ℕ} (a z : Word (Width d b)) :
    (∀ i, setupTest d b i (splice a z i) = true) ↔
    ∃ v : Word d, ∃ l : Word b, a = pack v (fun _ => false) ∧ z = pack v l := by
  classical
  constructor
  · intro h
    have H (i : Fin (Width d b)) := of_decide_eq_true (h i)
    obtain ⟨v,hv⟩ := (H 0).1 rfl
    rw [splice_zero, Fin.init_snoc] at hv
    refine ⟨v,label z,hv,?_⟩
    have keep (i : Fin (Width d b)) (hi : i.val < d+2) : z i = a i := by
      simpa [splice_last, splice_head] using (H i).2 hi
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [hv,pack] using keep 0 (by simp)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hv,pack] using keep (0 : Fin (d+b+1)).succ (by simp)
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hlt : ((Fin.castAdd b j).succ.succ).val < d+2 := by
        simp only [Fin.val_succ, Fin.val_castAdd]; omega
      simpa [hv,pack] using keep (Fin.castAdd b j).succ.succ hlt
    · simp [pack,label]
  · rintro ⟨v,l,rfl,rfl⟩ i
    apply decide_eq_true
    constructor
    · intro hi
      have e : i = 0 := Fin.ext hi
      subst i
      exact ⟨v,by rw [splice_zero,Fin.init_snoc]⟩
    · intro hi
      rw [splice_head,splice_last]
      revert hi
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [pack]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pack]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [pack]
      · simp [pack]

lemma port_iff {d b : ℕ} (a z : Word (Width d b)) (allowed : Word d → Word b → Prop) :
    (∀ i, portTest d b i (splice a z i) = true ∨
      (i.val=0 ∧ ∃ v l, allowed v l ∧ splice a z i = portPat v l)) ↔
    ∃ v l, allowed v l ∧ a=pack v l ∧ z=a := by
  classical
  constructor
  · intro H
    have atZero := H 0
    simp only [portTest, Fin.val_zero, ne_eq, not_true_eq_false, false_and, decide_false,
      Bool.false_eq_true, false_or, true_and] at atZero
    obtain ⟨v,l,ok,eq⟩ := atZero
    rw [splice_zero] at eq
    have ha := congrArg Fin.init eq
    have hlast := congrFun eq (Fin.last (Width d b))
    simp only [portPat, Fin.init_snoc] at ha
    simp only [portPat, Fin.snoc_last] at hlast
    refine ⟨v,l,ok,ha,?_⟩
    funext i
    by_cases h : i.val=0
    · have e : i = 0 := Fin.ext h
      subst i
      simpa [ha,pack] using hlast
    · rcases H i with yes | ⟨bad,_⟩
      · exact (splice_last a z i).symm.trans ((of_decide_eq_true yes).2.trans (splice_head a z i))
      · exact False.elim (h bad)
  · rintro ⟨v,l,ok,rfl,rfl⟩ i
    by_cases h : i.val=0
    · right
      have e : i = 0 := Fin.ext h
      subst i
      exact ⟨rfl,v,l,ok,by rw [splice_zero]; rfl⟩
    · left
      apply decide_eq_true
      exact ⟨h, (splice_last _ _ _).trans (splice_head _ _ _).symm⟩

def shiftStep (p : ℕ) (s : Fin (p + 1) → Bool) (b : Bool) : Fin (p + 1) → Bool :=
  Fin.snoc (α := fun _ : Fin (p + 1) => Bool) (fun j : Fin p => s j.succ) b

def rotState (p : ℕ) (s0 s1 : Fin (p + 1) → Bool) (k : ℕ) : Fin (p + 1) → Bool :=
  fun i =>
    if h : i.val < (p + 1) - k then s0 ⟨i.val + k, by omega⟩
    else s1 ⟨i.val - ((p + 1) - k), by omega⟩

lemma shiftStep_rotState (p : ℕ) (s0 s1 : Fin (p + 1) → Bool) (t : Fin (p + 1)) :
    shiftStep p (rotState p s0 s1 t.val) (s1 t) = rotState p s0 s1 (t.val + 1) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · unfold shiftStep rotState
    rw [Fin.snoc_last]
    have hnot : ¬ ((Fin.last p).val < (p + 1) - (t.val + 1)) := by simp
    simp only [hnot, ↓reduceDIte]
    congr 1; ext; simp; omega
  · intro j
    unfold shiftStep rotState
    rw [Fin.snoc_castSucc]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases h1 : j.val < (p + 1) - (t.val + 1)
    · have h2 : j.val + 1 < (p + 1) - t.val := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 1; ext; simp; omega
    · have h2 : ¬ (j.val + 1 < (p + 1) - t.val) := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 1; ext; simp; omega

lemma runSweep_eq {p : ℕ} (stepBit : Fin (p + 1) → (Fin (p + 1) → Bool) → Bool)
    (s0 s1 : Fin (p + 1) → Bool)
    (hstep : ∀ (t : Fin (p + 1)), stepBit t (rotState p s0 s1 t.val) = s1 t) :
    (List.finRange (p + 1)).foldl (fun s t => shiftStep p s (stepBit t s)) s0 = s1 := by
  have hgen : ∀ (k : ℕ) (hk : k ≤ p + 1),
      ((List.finRange (p + 1)).take k).foldl (fun s t => shiftStep p s (stepBit t s)) s0 =
        rotState p s0 s1 k := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, List.foldl_nil]
      funext i
      unfold rotState
      simp [i.isLt]
    | succ k ih =>
      have hlt : k < (List.finRange (p + 1)).length := by simp; omega
      rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      have hget : (List.finRange (p + 1))[k]'hlt = ⟨k, by omega⟩ := by simp
      rw [hget, hstep ⟨k, by omega⟩]
      exact shiftStep_rotState p s0 s1 ⟨k, by omega⟩
  have hfull := hgen (p + 1) (le_refl _)
  rw [List.take_of_length_le (by simp)] at hfull
  rw [hfull]
  funext i
  unfold rotState
  simp

lemma splice_init (p : ℕ) (a z : Word (p+1)) (i : Fin (p+1)) :
    Fin.init (splice a z i) = rotState p a z i.val := by
  funext j
  change splice a z i j.castSucc = _
  simp only [splice, Fin.val_castSucc, rotState]
  split_ifs with h1 h2 h3 <;> first | omega | (congr 1; apply Fin.ext; simp; omega)

def sweepEval {p : ℕ} (stepBit : Fin (p+1) → Word (p+1) → Bool) (a : Word (p+1)) :=
  (List.finRange (p+1)).foldl (fun s t => shiftStep p s (stepBit t s)) a

theorem deterministic_sweep {p : ℕ} (stepBit : Fin (p+1) → Word (p+1) → Bool)
    (a z : Word (p+1)) :
    (∀ i, stepBit i (Fin.init (splice a z i)) = splice a z i (Fin.last (p+1))) ↔
    sweepEval stepBit a = z := by
  simp only [splice_init, splice_last]
  constructor
  · exact runSweep_eq stepBit a z
  · intro h
    let advance := fun (s : Word (p+1)) (t : Fin (p+1)) => shiftStep p s (stepBit t s)
    let trace := fun k => ((List.finRange (p+1)).take k).foldl advance a
    let output : Word (p+1) := fun i => stepBit i (trace i.val)
    have state : ∀ k, k ≤ p+1 → trace k = rotState p a output k := by
      intro k hk
      induction k with
      | zero =>
        funext j
        simp [trace,rotState,j.isLt]
      | succ k ih =>
        have hlt : k < (List.finRange (p+1)).length := by simp; omega
        let i : Fin (p+1) := ⟨k,by omega⟩
        have hget : (List.finRange (p+1))[k]'hlt = i := by simp [i]
        have e : trace (k+1) = shiftStep p (trace k) (output i) := by
          simp only [trace, List.take_succ_eq_append_getElem hlt, List.foldl_append,
            List.foldl_cons, List.foldl_nil, hget, advance, output, i]
        rw [e, ih (by omega)]
        exact shiftStep_rotState p a output i
    have emission (i : Fin (p+1)) : stepBit i (rotState p a output i.val) = output i := by
      change _ = stepBit i (trace i.val)
      rw [state _ (by omega)]
    have he : sweepEval stepBit a = output := runSweep_eq stepBit a output emission
    rw [h] at he
    rw [he]
    exact emission

end PEqualNP.Outside.L_clb_111.Ports

namespace PEqualNP.Outside.L_clb_111.Counting

open Classical

theorem transport_count {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q]
    (ok : ∀ a, P a ↔ Q (e a)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (ok a).mp (Finset.mem_filter.mp ha).2
  · intro a _ a' _ he
    exact e.injective he
  · intro b hb
    refine ⟨e.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ok _).mpr ?_⟩, e.apply_symm_apply b⟩
    simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hb).2

theorem count_blocks {H B S V L : Type*} [Fintype H] [DecidableEq H] [Fintype B] [Fintype V] [Fintype L]
    (next : H → H) (start : B → S) (pack : V → S) (pack_inj : Function.Injective pack)
    (write : H → V × L → B) (write_inj : ∀ h, Function.Injective (write h))
    (starts : ∀ h q, start (write h q) = pack q.1)
    (dst : H → V → L → V) (enabled : H → V → L → Prop) (ok : H → B → B → Prop)
    (local_ok : ∀ h z z', ok h z z' ↔ ∃ q : V × L, z = write h q ∧
      enabled h q.1 q.2 ∧ start z' = pack (dst h q.1 q.2)) :
    (Finset.univ.filter (fun z : H → B => ∀ h, ok h (z h) (z (next h)))).card =
      (Finset.univ.filter (fun q : (H → V) × (H → L) =>
        ∀ h, enabled h (q.1 h) (q.2 h) ∧ dst h (q.1 h) (q.2 h) = q.1 (next h))).card := by
  symm
  apply Finset.card_bij (fun (q : (H → V) × (H → L)) _ h => write h (q.1 h, q.2 h))
  · intro q hq
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun h => (local_ok _ _ _).mpr ?_⟩
    exact ⟨(q.1 h, q.2 h), rfl, (hp h).1, (starts _ _).trans (congrArg pack (hp h).2.symm)⟩
  · intro q _ r _ eq
    have same (h : H) : (q.1 h, q.2 h) = (r.1 h, r.2 h) := write_inj h (congrFun eq h)
    exact Prod.ext (funext fun h => congrArg Prod.fst (same h)) (funext fun h => congrArg Prod.snd (same h))
  · intro z hz
    have avail (h : H) := (local_ok _ _ _).mp ((Finset.mem_filter.mp hz).2 h)
    let q (h : H) := (avail h).choose
    have qok (h : H) : z h = write h (q h) ∧ enabled h (q h).1 (q h).2 ∧
        start (z (next h)) = pack (dst h (q h).1 (q h).2) := (avail h).choose_spec
    refine ⟨(fun h => (q h).1, fun h => (q h).2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro h
      refine ⟨(qok h).2.1, pack_inj ?_⟩
      exact (qok h).2.2.symm.trans ((congrArg start (qok (next h)).1).trans (starts _ _))
    · exact funext fun h => (qok h).1.symm

abbrev Word (n : Nat) := Fin n → Bool
def splice {w : Nat} (a b : Word w) (i : Fin w) : Word (w + 1) := fun j =>
  if h : i.val + j.val < w then a ⟨i.val + j.val, h⟩ else
    b ⟨i.val + j.val - w, by have := i.isLt; have := j.isLt; omega⟩

def linearPos {m w : Nat} (i : Fin m) (j : Fin w) : Fin (m * w) :=
  ⟨i.val * w + j.val, by
    have := Nat.mul_le_mul_right w (show i.val + 1 ≤ m from i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at this
    have := j.isLt; omega⟩

def regroup {m w P : Nat} (hw : 0 < w) (eq : P = m * w) : (Word P) ≃ (Fin m → Word w) where
  toFun x i j := x ⟨(linearPos i j).val, eq ▸ (linearPos i j).isLt⟩
  invFun y i := y ⟨i.val / w, (Nat.div_lt_iff_lt_mul hw).mpr (eq ▸ i.isLt)⟩
    ⟨i.val % w, Nat.mod_lt _ hw⟩
  left_inv x := by
    funext j; apply congrArg x; apply Fin.ext; change j.val / w * w + j.val % w = j.val
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div j.val w
  right_inv f := by
    funext i j
    change f ⟨(i.val * w + j.val) / w, _⟩ ⟨(i.val * w + j.val) % w, _⟩ = f i j
    congr 1
    · apply Fin.ext; simp [Nat.add_comm _ j.val, Nat.add_mul_div_right, Nat.div_eq_of_lt j.isLt, hw]
    · apply Fin.ext; simp [Nat.mod_eq_of_lt j.isLt]

lemma cyclic_window_eq_splice {w m n : Nat} (hw : 0 < w) (hm : 0 < m) (eq : n = m * w)
    (word : Word n) (t : Fin m) (i : Fin w) :
    (fun j : Fin (w + 1) => word ⟨((t.val * w + i.val) + j.val) % n, Nat.mod_lt _ (by rw [eq]; exact Nat.mul_pos hm hw)⟩) =
    splice (regroup hw eq word t) (regroup hw eq word ⟨(t.val + 1) % m, Nat.mod_lt _ hm⟩) i := by
  have hnpos : 0 < n := by rw [eq]; exact Nat.mul_pos hm hw
  funext j
  unfold splice
  split
  · rename_i hlt
    have hlt_n : t.val * w + i.val + j.val < n := by
      have h1 : (t.val + 1) * w ≤ m * w := Nat.mul_le_mul_right w t.isLt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    dsimp only [regroup, linearPos]
    congr 1
    apply Fin.ext
    dsimp only
    rw [Nat.mod_eq_of_lt hlt_n]
    omega
  · rename_i hge
    dsimp only [regroup, linearPos]
    congr 1
    apply Fin.ext
    dsimp only
    by_cases ht1 : t.val + 1 < m
    · have hlt_n : t.val * w + i.val + j.val < n := by
        have h1 : (t.val + 2) * w ≤ m * w := Nat.mul_le_mul_right w ht1
        have h2 : (t.val + 2) * w = t.val * w + w + w := by
          have : t.val + 2 = t.val + 1 + 1 := rfl
          rw [this, Nat.add_mul, Nat.add_mul, Nat.one_mul]
        have hj := j.isLt
        omega
      rw [Nat.mod_eq_of_lt hlt_n, Nat.mod_eq_of_lt ht1, Nat.add_mul, Nat.one_mul]
      omega
    · have hteq : t.val + 1 = m := by omega
      have hmod_m : (t.val + 1) % m = 0 := by rw [hteq, Nat.mod_self]
      rw [hmod_m, Nat.zero_mul, Nat.zero_add]
      have h1 : t.val * w + i.val + j.val = n + (i.val + j.val - w) := by
        have hmw : m * w = t.val * w + w := by
          calc m * w = (t.val + 1) * w := by rw [hteq]
            _ = t.val * w + w := by rw [Nat.add_mul, Nat.one_mul]
        omega
      have h2 : i.val + j.val - w < n := by
        have h1w : w ≤ n := by
          have : 1 * w ≤ m * w := Nat.mul_le_mul_right w hm
          omega
        have hi := i.isLt
        have hj := j.isLt
        omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h2]

def chunks {t m : Nat} {A : Type*} (hm : 0 < m) :
    (Fin (t*m) → A) ≃ (Fin t → Fin m → A) where
  toFun x h j := x (linearPos h j)
  invFun x i := x ⟨i.val / m, (Nat.div_lt_iff_lt_mul hm).mpr i.isLt⟩ ⟨i.val % m, Nat.mod_lt _ hm⟩
  left_inv x := by
    funext i; apply congrArg x; apply Fin.ext
    change i.val / m * m + i.val % m = i.val
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div i.val m
  right_inv x := by
    funext h j
    change x ⟨(h.val * m + j.val) / m, _⟩ ⟨(h.val * m + j.val) % m, _⟩ = x h j
    congr 1
    · apply Fin.ext; simp [Nat.add_comm _ j.val, Nat.add_mul_div_right, Nat.div_eq_of_lt j.isLt, hm]
    · apply Fin.ext; simp [Nat.mod_eq_of_lt j.isLt]

def nextLayer {t : Nat} (ht : 0 < t) (h : Fin t) : Fin t :=
  ⟨(h.val + 1) % t, Nat.mod_lt _ ht⟩

def nextSweep {t m : Nat} (ht : 0 < t) (hm : 0 < m) (h : Fin t) (j : Fin m) :
    Fin t × Fin m :=
  if hj : j.val + 1 < m then (h, ⟨j.val + 1,hj⟩) else (nextLayer ht h, ⟨0,hm⟩)

theorem next_sweep_flat {t m : Nat} (ht : 0 < t) (hm : 0 < m) (h : Fin t) (j : Fin m) :
    (⟨((linearPos h j).val + 1) % (t*m), Nat.mod_lt _ (Nat.mul_pos ht hm)⟩ : Fin (t*m)) =
       linearPos (nextSweep ht hm h j).1 (nextSweep ht hm h j).2 := by
  apply Fin.ext
  unfold nextSweep
  by_cases hj : j.val + 1 < m
  · simp only [hj, dite_true]
    change (h.val*m+j.val+1)%(t*m) = h.val*m+(j.val+1)
    have hcap := Nat.mul_le_mul_right m (show h.val+1 ≤ t from h.isLt)
    rw [Nat.add_mul, Nat.one_mul] at hcap
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [hj, dite_false]
    change (h.val*m+j.val+1)%(t*m) = ((h.val+1)%t)*m+0
    have hlast : j.val+1=m := by have := j.isLt; omega
    rw [Nat.add_assoc, hlast, ← Nat.succ_mul, Nat.add_zero]
    by_cases hh : h.val+1<t
    · rw [Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right hh hm)]
    · have eh : h.val+1=t := by have := h.isLt; omega
      change (h.val + 1) * m % (t * m) = ((h.val + 1) % t) * m
      rw [eh, Nat.mod_self, Nat.mod_self, Nat.zero_mul]

def groups {t m w n : Nat} (hm : 0 < m) (hw : 0 < w) (hn : n = t*m*w) :
    Word n ≃ (Fin t → Fin m → Word w) :=
  (regroup hw hn).trans (chunks hm)

def nextState {m w : Nat} (hm : 0 < m) (now later : Fin m → Word w) (j : Fin m) : Word w :=
  if hj : j.val+1<m then now ⟨j.val+1,hj⟩ else later ⟨0,hm⟩

theorem grouped_window {t m w n : Nat} (ht : 0<t) (hm : 0<m) (hw : 0<w)
    (hn : n=t*m*w) (x : Word n) (h : Fin t) (j : Fin m) (i : Fin w) :
    (fun k : Fin (w+1) => x ⟨((h.val*m+j.val)*w+i.val+k.val)%n,
      Nat.mod_lt _ (hn ▸ Nat.mul_pos (Nat.mul_pos ht hm) hw)⟩) =
    splice (groups hm hw hn x h j)
      (nextState hm (groups hm hw hn x h) (groups hm hw hn x (nextLayer ht h)) j) i := by
  have old := cyclic_window_eq_splice hw (Nat.mul_pos ht hm) hn x (linearPos h j) i
  rw [next_sweep_flat ht hm h j] at old
  by_cases hs : j.val+1<m <;> simpa [groups, chunks, nextSweep, nextState, hs, linearPos] using old

def row {t m w n : Nat} (hn : n=t*m*w) (h : Fin t) (j : Fin m) (i : Fin w) : Fin n :=
  Fin.cast hn.symm (linearPos (linearPos h j) i)

theorem rows_cover {t m w n : Nat} (hm : 0<m) (hw : 0<w) (hn : n=t*m*w) (k : Fin n) :
    ∃ h j i, row hn h j i = k := by
  let a := k.val / w
  have ha : a < t*m := (Nat.div_lt_iff_lt_mul hw).mpr (hn ▸ k.isLt)
  let h : Fin t := ⟨a/m, (Nat.div_lt_iff_lt_mul hm).mpr ha⟩
  let j : Fin m := ⟨a % m, Nat.mod_lt _ hm⟩
  let i : Fin w := ⟨k.val % w, Nat.mod_lt _ hw⟩
  refine ⟨h,j,i,?_⟩
  apply Fin.ext
  change (a / m * m + a % m) * w + k.val % w = k.val
  rw [show a / m * m + a % m = a by simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div a m]
  simpa [a,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div k.val w

def blockOK {t m w n : Nat} (hm : 0<m) (hn : n=t*m*w)
    (P : Fin n → Word (w+1) → Prop) (h : Fin t) (now later : Fin m → Word w) : Prop :=
  ∀ j i, P (row hn h j i) (splice (now j) (nextState hm now later j) i)

theorem cyclic_block_count {t m w n : Nat} (ht : 0<t) (hm : 0<m) (hw : 0<w)
    (hn : n=t*m*w) (P : Fin n → Word (w+1) → Prop) :
    (Finset.univ.filter (fun x : Word n => ∀ k : Fin n, P k (fun b : Fin (w+1) =>
      x ⟨(k.val+b.val)%n, Nat.mod_lt _ (hn ▸ Nat.mul_pos (Nat.mul_pos ht hm) hw)⟩))).card =
    (Finset.univ.filter (fun z : Fin t → Fin m → Word w =>
      ∀ h, blockOK hm hn P h (z h) (z (nextLayer ht h)))).card := by
  refine transport_count (groups hm hw hn) _ _ ?_
  intro x
  constructor
  · intro hx h j i
    rw [← grouped_window ht hm hw hn x h j i]
    exact hx (row hn h j i)
  · intro hz k
    obtain ⟨h,j,i,rfl⟩ := rows_cover hm hw hn k
    have loc := hz h j i
    rw [← grouped_window ht hm hw hn x h j i] at loc
    exact loc

theorem cyclic_path_count {V L S : Type*} [Fintype V] [Fintype L]
    {t m w n : Nat} (ht : 0<t) (hm : 0<m) (hw : 0<w) (hn : n=t*m*w)
    (P : Fin n → Word (w+1) → Prop) (start : (Fin m → Word w) → S)
    (pack : V → S) (pack_inj : Function.Injective pack)
    (write : Fin t → V × L → Fin m → Word w) (write_inj : ∀ h, Function.Injective (write h))
    (starts : ∀ h q, start (write h q) = pack q.1)
    (dst : Fin t → V → L → V) (enabled : Fin t → V → L → Prop)
    (local_ok : ∀ h z z', blockOK hm hn P h z z' ↔ ∃ q : V × L, z = write h q ∧
      enabled h q.1 q.2 ∧ start z' = pack (dst h q.1 q.2)) :
    (Finset.univ.filter (fun x : Word n => ∀ k : Fin n, P k (fun b : Fin (w+1) =>
      x ⟨(k.val+b.val)%n, Nat.mod_lt _ (hn ▸ Nat.mul_pos (Nat.mul_pos ht hm) hw)⟩))).card =
    (Finset.univ.filter (fun q : (Fin t → V) × (Fin t → L) => ∀ h,
      enabled h (q.1 h) (q.2 h) ∧ dst h (q.1 h) (q.2 h) = q.1 (nextLayer ht h))).card := by
  have blocks := count_blocks (nextLayer ht) start pack pack_inj write write_inj starts dst enabled
    (blockOK hm hn P) local_ok
  refine (cyclic_block_count ht hm hw hn P).trans (Eq.trans ?_ (blocks.trans ?_))
  all_goals
    apply congrArg Finset.card
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end PEqualNP.Outside.L_clb_111.Counting

namespace PEqualNP.Outside.L_clb_111.BlockEncoding

def trace {X : Type*} {k : ℕ} (step : Fin k → X → X) (x : X) (j : ℕ) : X :=
  ((List.finRange k).take j).foldl (fun a idx => step idx a) x

theorem trace_zero {X : Type*} {k : ℕ} (step : Fin k → X → X) (x : X) :
    trace step x 0 = x := by simp [trace]

theorem trace_succ {X : Type*} {k : ℕ} (step : Fin k → X → X) (x : X) (j : Fin k) :
    trace step x (j.val+1) = step j (trace step x j.val) := by
  have h : j.val < (List.finRange k).length := by simp
  simp [trace, List.take_succ_eq_append_getElem h]

theorem trace_all {X : Type*} {k : ℕ} (step : Fin k → X → X) (x : X) :
    trace step x k = (List.finRange k).foldl (fun a i => step i a) x := by
  unfold trace
  rw [List.take_of_length_le (by simp)]

theorem chain {X : Type*} {k : ℕ} (step : Fin k → X → X) (states : Fin (k+1) → X)
    (h : ∀ j : Fin k, states j.succ = step j (states j.castSucc)) :
    ∀ j : Fin (k+1), states j = trace step (states 0) j.val := by
  intro j
  induction j using Fin.induction with
  | zero => simp [trace]
  | succ j ih =>
    rw [h j, Fin.val_succ, trace_succ]
    exact congrArg (step j) ih

def write {V L X : Type*} {k : ℕ} (init : V → X) (mid : V → L → X)
    (step : Fin k → X → X) (q : V × L) : Fin (k+2) → X :=
  Fin.cons (init q.1) (Fin.cons (mid q.1 q.2) (fun i => trace step (mid q.1 q.2) i.val))

theorem write_inj {V L X : Type*} {k : ℕ} (init : V → X) (mid : V → L → X)
    (step : Fin k → X → X) (hinj : Function.Injective (fun q : V × L => mid q.1 q.2)) :
    Function.Injective (write init mid step) := by
  intro q r h
  apply hinj
  simpa [write] using congrFun h (0 : Fin (k+1)).succ

theorem write_start {V L X : Type*} {k : ℕ} (init : V → X) (mid : V → L → X)
    (step : Fin k → X → X) (q : V × L) : write init mid step q 0 = init q.1 := rfl

def boundaries {X : Type*} {k : ℕ} (z : Fin (k+2) → X) (last : X) : Fin (k+3) → X :=
  Fin.snoc z last

def Legal {V L X : Type*} {k : ℕ} (init : V → X) (mid : V → L → X)
    (step : Fin k → X → X) (allowed : V → L → Prop) (z : Fin (k+2) → X) (last : X) : Prop :=
  let e := boundaries z last
  (∃ v l, e 0 = init v ∧ e (0 : Fin (k+2)).succ = mid v l) ∧
  (∃ v l, allowed v l ∧ e (0 : Fin (k+2)).succ = mid v l ∧
      e (0 : Fin (k+1)).succ.succ = e (0 : Fin (k+2)).succ) ∧
  (∀ j : Fin k, e j.succ.succ.succ = step j (e j.castSucc.succ.succ))

theorem legal_iff {V L X : Type*} {k : ℕ} (init : V → X) (mid : V → L → X)
    (step : Fin k → X → X) (allowed : V → L → Prop)
    (hinj : Function.Injective (fun q : V × L => mid q.1 q.2))
    (z : Fin (k+2) → X) (last : X) :
    Legal init mid step allowed z last ↔
    ∃ q : V × L, z = write init mid step q ∧ allowed q.1 q.2 ∧
      last = trace step (mid q.1 q.2) k := by
  let e := boundaries z last
  have inside (j : Fin (k+2)) : e j.castSucc = z j := Fin.snoc_castSucc _ _ _
  have final : e (Fin.last (k+2)) = last := Fin.snoc_last _ _
  constructor
  · rintro ⟨⟨v,l,A,B⟩,⟨v',l',allow,B',C⟩,run⟩
    have pairs : (v,l) = (v',l') := hinj (B.symm.trans B')
    cases pairs
    have tr := chain step (fun j : Fin (k+1) => e j.succ.succ) run
    have c : e (0 : Fin (k+1)).succ.succ = mid v l := C.trans B
    rw [c] at tr
    refine ⟨(v,l),?_,allow,?_⟩
    · funext j
      rw [←inside]
      refine Fin.cases ?_ (fun j => ?_) j
      · exact A
      refine Fin.cases ?_ (fun j => ?_) j
      · exact B
      · exact tr j.castSucc
    · rw [←final]
      exact tr (Fin.last k)
  · rintro ⟨⟨v,l⟩,rfl,allow,rfl⟩
    have data (j : Fin (k+1)) : boundaries (write init mid step (v,l)) (trace step (mid v l) k)
        j.succ.succ = trace step (mid v l) j.val := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact Fin.snoc_last _ _
      · exact Fin.snoc_castSucc _ _ i.succ.succ
    refine ⟨⟨v,l,?_,?_⟩,⟨v,l,allow,?_,?_⟩,?_⟩
    · exact Fin.snoc_castSucc _ _ 0
    · exact Fin.snoc_castSucc _ _ (0 : Fin (k+1)).succ
    · exact Fin.snoc_castSucc _ _ (0 : Fin (k+1)).succ
    · rw [data 0,Fin.val_zero,trace_zero]
      symm
      exact Fin.snoc_castSucc _ _ (0 : Fin (k+1)).succ
    · intro j
      rw [data j.succ,data j.castSucc,Fin.val_succ,Fin.val_castSucc,trace_succ]

end PEqualNP.Outside.L_clb_111.BlockEncoding

namespace PEqualNP.Outside.L_clb_111.SweepBridge

open Ports (Word Width pack)

def feedIndex {w k : ℕ} (s : Fin k) (i : Fin w) : Fin (w*k) :=
  ⟨s.val*w+i.val, calc
    _ < s.val*w+w := Nat.add_lt_add_left i.isLt _
    _ = (s.val+1)*w := (Nat.succ_mul ..).symm
    _ ≤ k*w := Nat.mul_le_mul_right _ s.isLt
    _ = _ := Nat.mul_comm ..⟩

def sweepStep {w k : ℕ} (bit : Fin ((w+1)*k) → Word (w+1) → Bool)
    (s : Fin k) : Word (w+1) → Word (w+1) :=
  Ports.sweepEval (fun i => bit (feedIndex s i))

theorem flatten_trace {w k : ℕ} (bit : Fin ((w+1)*k) → Word (w+1) → Bool)
    (a : Word (w+1)) :
    BlockEncoding.trace (sweepStep bit) a k =
    (List.finRange ((w+1)*k)).foldl (fun z j => Ports.shiftStep w z (bit j z)) a := by
  rw [BlockEncoding.trace_all]
  simpa only [sweepStep, Ports.sweepEval, feedIndex] using
    (PEqualNP.Outside.L_clb_073.foldl_finRange_mul (w+1) k
      (fun z j => Ports.shiftStep w z (bit j z)) a).symm

def panel {d b k : ℕ} (bit : Fin ((Width d b)*k) → Word (Width d b) → Bool)
    (allowed : Word d → Word b → Prop) (j : Fin (k+2))
    (i : Fin (Width d b)) (pat : Word (Width d b+1)) : Prop :=
  Fin.cases (Ports.setupTest d b i pat = true)
    (Fin.cases (Ports.portTest d b i pat = true ∨ i.val=0 ∧
      ∃ v l, allowed v l ∧ pat = Ports.portPat v l)
      (fun s => bit (feedIndex s i) (Fin.init pat) = pat (Fin.last (Width d b)))) j

theorem panel_iff {d b k : ℕ} (bit : Fin ((Width d b)*k) → Word (Width d b) → Bool)
    (allowed : Word d → Word b → Prop) (now : Fin (k+2) → Word (Width d b))
    (last : Word (Width d b)) :
    (∀ j i, panel bit allowed j i
      (Ports.splice (BlockEncoding.boundaries now last j.castSucc)
        (BlockEncoding.boundaries now last j.succ) i)) ↔
    BlockEncoding.Legal (fun v => pack v (fun _ => false)) pack (sweepStep bit) allowed now last := by
  constructor
  · intro h
    constructor
    · exact (Ports.setup_iff _ _).mp (h 0)
    constructor
    · exact (Ports.port_iff _ _ _).mp (h (0 : Fin (k+1)).succ)
    · intro j
      exact ((Ports.deterministic_sweep _ _ _).mp (h j.succ.succ)).symm
  · rintro ⟨s,p,rest⟩ j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (Ports.setup_iff _ _).mpr s
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (Ports.port_iff _ _ _).mpr p
    · exact (Ports.deterministic_sweep _ _ _).mpr (rest j).symm

theorem next_bound {k w : ℕ} (now later : Fin (k+2) → Word w) (j : Fin (k+2)) :
    Counting.nextState (by omega) now later j =
      BlockEncoding.boundaries now (later 0) j.succ := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Counting.nextState, BlockEncoding.boundaries, Fin.snoc]
  · have hi : i.val+1 < k+2 := by omega
    unfold Counting.nextState
    rw [dite_eq_left (by exact hi), Fin.succ_castSucc]
    unfold BlockEncoding.boundaries
    rw [Fin.snoc_castSucc]
    exact congrArg now (Fin.ext rfl)

theorem blockOK_iff_legal {t d b k n : ℕ} (hn : n = t*(k+2)*Width d b)
    (P : Fin n → Word (Width d b+1) → Prop) (h : Fin t)
    (bit : Fin ((Width d b)*k) → Word (Width d b) → Bool)
    (allowed : Word d → Word b → Prop)
    (row_spec : ∀ j i pat, P (Counting.row hn h j i) pat ↔ panel bit allowed j i pat)
    (now later : Fin (k+2) → Word (Width d b)) :
    Counting.blockOK (by omega) hn P h now later ↔
    BlockEncoding.Legal (fun v => pack v (fun _ => false)) pack (sweepStep bit) allowed now (later 0) := by
  rw [←panel_iff]
  apply forall_congr' ; intro j
  apply forall_congr' ; intro i
  rw [next_bound,show BlockEncoding.boundaries now (later 0) j.castSucc = now j from Fin.snoc_castSucc _ _ _]
  exact row_spec j i _

end PEqualNP.Outside.L_clb_111.SweepBridge

namespace PEqualNP.Outside.L_clb_111.PortRows

open Counting Classical

private theorem linear_injective {t m : Nat} :
    Function.Injective (fun q : Fin t × Fin m => linearPos q.1 q.2) := by
  intro a b eq
  apply finProdFinEquiv.injective
  apply Fin.ext
  change a.2.val + m*a.1.val = b.2.val + m*b.1.val
  have he := congrArg Fin.val eq
  change a.1.val*m+a.2.val = b.1.val*m+b.2.val at he
  calc a.2.val + m*a.1.val = a.1.val*m+a.2.val := by ac_rfl
       _ = b.1.val*m+b.2.val := he
       _ = b.2.val + m*b.1.val := by ac_rfl

theorem row_eq {t m w n : Nat} (hn : n=t*m*w) {h h' : Fin t} {j j' : Fin m}
    {i i' : Fin w} (eq : row hn h j i = row hn h' j' i') : h=h' ∧ j=j' ∧ i=i' := by
  have outer : (linearPos h j, i) = (linearPos h' j', i') := by
    apply linear_injective
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) eq
  have inner : (h,j)=(h',j') := by
    apply linear_injective
    exact congrArg Prod.fst outer
  exact ⟨congrArg Prod.fst inner, congrArg Prod.snd inner, congrArg Prod.snd outer⟩

def port {t m w n : Nat} {V L Pat : Type*} (hn : n=t*m*w) (hm : 1<m) (hw : 0<w)
    (pat : V × L → Pat) (e : Fin t × V × L) : Fin n × Pat :=
  (row hn e.1 ⟨1,hm⟩ ⟨0,hw⟩, pat e.2)

theorem port_row {t m w n : Nat} {V L Pat : Type*} (hn : n=t*m*w) (hm : 1<m) (hw : 0<w)
    (pat : V × L → Pat) (e : Fin t × V × L) :
    (port hn hm hw pat e).1.val = e.1.val*(w*m)+w := by
  change (e.1.val*m+1)*w+0 = e.1.val*(w*m)+w
  rw [Nat.add_mul, Nat.one_mul, Nat.add_zero, Nat.mul_assoc, Nat.mul_comm m w]

theorem port_injective {t m w n : Nat} {V L Pat : Type*} (hn : n=t*m*w) (hm : 1<m) (hw : 0<w)
    (pat : V × L → Pat) (hpat : Function.Injective pat) : Function.Injective (port hn hm hw pat) := by
  intro a b eq
  exact Prod.ext (row_eq hn (congrArg Prod.fst eq)).1 (hpat (congrArg Prod.snd eq))

theorem mem_image {t m w n : Nat} {V L Pat : Type*} [DecidableEq (Fin n × Pat)]
    (hn : n=t*m*w) (hm : 1<m) (hw : 0<w)
    (pat : V × L → Pat) (enabled : Finset (Fin t × V × L))
    (h : Fin t) (j : Fin m) (i : Fin w) (pattern : Pat) :
    (row hn h j i, pattern) ∈ enabled.image (port hn hm hw pat) ↔
      j.val=1 ∧ i.val=0 ∧ ∃ q : V × L, (h,q) ∈ enabled ∧ pat q=pattern := by
  constructor
  · rintro he
    obtain ⟨⟨h',q⟩,hq,eq⟩ := Finset.mem_image.mp he
    obtain ⟨hh,hj,hi⟩ := row_eq hn (congrArg Prod.fst eq)
    change h'=h at hh
    subst h'
    exact ⟨(congrArg Fin.val hj).symm, (congrArg Fin.val hi).symm, q, hq, congrArg Prod.snd eq⟩
  · rintro ⟨hj,hi,q,hq,hpat⟩
    have ej : j = ⟨1,hm⟩ := Fin.ext hj
    have ei : i = ⟨0,hw⟩ := Fin.ext hi
    subst j; subst i
    exact Finset.mem_image.mpr ⟨(h,q),hq,Prod.ext rfl hpat⟩

abbrev physical {d b t m n : Nat} (hn : n=t*m*Ports.Width d b) (hm : 1<m) :
    Fin t × Ports.Word d × Ports.Word b → Fin n × Ports.Word (Ports.Width d b+1) :=
  port hn hm (Nat.succ_pos _) (fun q => Ports.portPat q.1 q.2)

theorem physical_injective {d b t m n : Nat} (hn : n=t*m*Ports.Width d b) (hm : 1<m) :
    Function.Injective (physical hn hm) := by
  apply port_injective
  intro q r eq
  exact Prod.ext (Ports.portPat_inj eq).1 (Ports.portPat_inj eq).2

theorem physical_row {d b t m n : Nat} (hn : n=t*m*Ports.Width d b) (hm : 1<m)
    (e : Fin t × Ports.Word d × Ports.Word b) :
    (physical hn hm e).1.val = e.1.val*(Ports.Width d b*m)+Ports.Width d b :=
  port_row hn hm _ _ e

theorem physical_mem {d b t m n : Nat} (hn : n=t*m*Ports.Width d b) (hm : 1<m)
    (enabled : Finset (Fin t × Ports.Word d × Ports.Word b)) (h : Fin t) (j : Fin m)
    (i : Fin (Ports.Width d b)) (p : Ports.Word (Ports.Width d b+1)) :
    (row hn h j i, p) ∈ enabled.image (physical hn hm) ↔
      j.val=1 ∧ i.val=0 ∧ ∃ q : Ports.Word d × Ports.Word b,
        (h,q) ∈ enabled ∧ Ports.portPat q.1 q.2=p :=
  mem_image hn hm _ _ enabled h j i p

end PEqualNP.Outside.L_clb_111.PortRows

namespace PEqualNP.Outside.L_clb_111_aux.RowOutput

abbrev Word (w : ℕ) := Fin w → Bool

def flattenIndex {m w : ℕ} (i : Fin m) (j : Fin w) : Fin (m*w) :=
  ⟨i.val*w+j.val, calc
    _ < i.val*w+w := Nat.add_lt_add_left j.isLt _
    _ = (i.val+1)*w := (Nat.add_one_mul ..).symm
    _ ≤ m*w := Nat.mul_le_mul_right w i.isLt⟩

theorem splitIndex {m w : ℕ} (i : Fin m) (j : Fin w) :
    (flattenIndex i j).divNat = i ∧ (flattenIndex i j).modNat = j := by
  constructor <;> apply Fin.ext
  · change (i.val*w+j.val)/w = i.val
    rw [Nat.mul_comm i.val w, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt),
      Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  · change (i.val*w+j.val)%w = j.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

def unrow {t m w n : ℕ} (hn : n = t*m*w) (f : Fin t → Fin m → Fin w → α) (x : Fin n) : α :=
  let k : Fin (t*m*w) := Fin.cast hn x
  f k.divNat.divNat k.divNat.modNat k.modNat

theorem unrow_at {t m w n : ℕ} (hn : n = t*m*w) (f : Fin t → Fin m → Fin w → α)
    (h : Fin t) (j : Fin m) (i : Fin w) :
    unrow hn f (Fin.cast hn.symm (flattenIndex (flattenIndex h j) i)) = f h j i := by
  subst n
  simp only [unrow, Fin.cast_refl, id_eq, (splitIndex (flattenIndex h j) i).1,
    (splitIndex (flattenIndex h j) i).2, (splitIndex h j).1, (splitIndex h j).2]

def feedbackRow {r w : ℕ} (j : Fin (r+2)) (hj : 2 ≤ j.val) (i : Fin w) :
    Fin (w*r) :=
  ⟨(j.val-2)*w+i.val, by
    have h : j.val-2+1 ≤ r := by have := j.isLt; omega
    have bound := Nat.mul_le_mul_right w h
    rw [Nat.add_one_mul] at bound
    rw [Nat.mul_comm w r]
    have := i.isLt
    omega⟩

def chooseWire {t r w N : ℕ}
    (constant : Bool → Fin N) (copy : Fin t → Fin (w*r) → Word w → Bool → Fin N)
    (setup port : Fin w → Word (w+1) → Bool)
    (h : Fin t) (j : Fin (r+2)) (i : Fin w) (pat : Word (w+1)) : Fin N :=
  if j.val = 0 then constant (setup i pat)
  else if hj : j.val < 2 then constant (port i pat)
  else copy h (feedbackRow j (by omega) i) (Fin.init pat) (pat (Fin.last w))

theorem evaluate {t r w N : ℕ}
    (constant : Bool → Fin N) (copy : Fin t → Fin (w*r) → Word w → Bool → Fin N)
    (setup port : Fin w → Word (w+1) → Bool)
    (read : Fin N → Bool) (readSub : Fin t → Fin (w*r) → Word w → Bool)
    (hconst : ∀ b, read (constant b) = b)
    (hcopy : ∀ h k s b, read (copy h k s b) = if b then readSub h k s else !(readSub h k s))
    (h : Fin t) (j : Fin (r+2)) (i : Fin w) (pat : Word (w+1)) :
    read (chooseWire constant copy setup port h j i pat) = true ↔
      if j.val = 0 then setup i pat = true
      else if hj : j.val < 2 then port i pat = true
      else readSub h (feedbackRow j (by omega) i) (Fin.init pat) = pat (Fin.last w) := by
  unfold chooseWire
  split
  · simp [hconst]
  split
  · simp [hconst]
  · rw [hcopy]
    cases pat (Fin.last w) <;> simp

theorem size_bound (d b t gates : ℕ) (ht : 0 < t)
    (hg : gates ≤ 128 * 2^(d+b+1) * (d+b+1+2)^3) :
    t*2^d*2^b*d + 4 + 2*t*gates ≤ 512*t*2^(d+b+1)*(d+b+1+2)^3 := by
  let z := 2^(d+b+1)
  let k := d+b+1+2
  have hz : 0 < z := Nat.two_pow_pos _
  have hk : 0 < k := by dsimp [k]; omega
  have hd : d ≤ k^3 := calc
    d ≤ k := by dsimp [k]; omega
    _ ≤ k*k := by simpa using Nat.mul_le_mul_left k hk
    _ ≤ k^3 := by simpa [pow_succ] using Nat.mul_le_mul_left (k*k) hk
  have hp : 2^d * 2^b ≤ z := by
    dsimp [z]
    rw [pow_succ, pow_add]
    omega
  have hi : t*2^d*2^b*d ≤ t*z*k^3 := by
    rw [Nat.mul_assoc t]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left t hp) hd
  have hs := Nat.mul_le_mul_left (2*t) hg
  have eq : 2*t*(128*2^(d+b+1)*(d+b+1+2)^3) = 256*(t*z*k^3) := by dsimp [z,k]; ring
  rw [eq] at hs
  have hpos : 0 < t*z*k^3 := Nat.mul_pos (Nat.mul_pos ht hz) (Nat.pow_pos hk)
  have goalEq : 512*t*2^(d+b+1)*(d+b+1+2)^3 = 512*(t*z*k^3) := by dsimp [z,k]; ring
  rw [goalEq]
  omega

end PEqualNP.Outside.L_clb_111_aux.RowOutput

namespace PEqualNP.Outside.L_clb_111.OutputBridge

open PEqualNP.Outside.L_clb_111_aux.RowOutput (chooseWire unrow unrow_at evaluate feedbackRow)
open Ports (Word Width)
open Classical

noncomputable def output {d b t k n N : ℕ} (hn : n=t*(k+2)*Width d b)
    (constant : Bool → Fin N)
    (copy : Fin t → Fin (Width d b*k) → Word (Width d b) → Bool → Fin N)
    (cell : Fin n × Word (Width d b+1)) : Fin N :=
  unrow hn (fun h j i => chooseWire constant copy (Ports.setupTest d b) (Ports.portTest d b)
    h j i cell.2) cell.1

theorem output_at {d b t k n N : ℕ} (hn : n=t*(k+2)*Width d b)
    (constant : Bool → Fin N)
    (copy : Fin t → Fin (Width d b*k) → Word (Width d b) → Bool → Fin N)
    (h : Fin t) (j : Fin (k+2)) (i : Fin (Width d b)) (pat : Word (Width d b+1)) :
    output hn constant copy (Counting.row hn h j i,pat) =
    chooseWire constant copy (Ports.setupTest d b) (Ports.portTest d b) h j i pat :=
  unrow_at hn _ h j i

theorem disabled {d b t k n N : ℕ} (hn : n=t*(k+2)*Width d b)
    (constant : Bool → Fin N)
    (copy : Fin t → Fin (Width d b*k) → Word (Width d b) → Bool → Fin N)
    (read : Fin N → Bool) (hc : ∀ z, read (constant z) = z)
    (e : Fin t × Word d × Word b) :
    read (output hn constant copy (PortRows.physical hn (by omega) e)) = false := by
  unfold PortRows.physical PortRows.port
  rw [output_at]
  simpa [chooseWire, Ports.portTest] using hc (Ports.portTest d b 0 (Ports.portPat e.2.1 e.2.2))

theorem panel_at {d b t k n N : ℕ} (hn : n=t*(k+2)*Width d b)
    (constant : Bool → Fin N)
    (copy : Fin t → Fin (Width d b*k) → Word (Width d b) → Bool → Fin N)
    (read : Fin N → Bool) (hc : ∀ z, read (constant z) = z)
    (bit : Fin t → Fin (Width d b*k) → Word (Width d b) → Bool)
    (hcopy : ∀ h r s z, read (copy h r s z) = if z then bit h r s else !(bit h r s))
    (enabled : Finset (Fin t × Word d × Word b))
    (h : Fin t) (j : Fin (k+2)) (i : Fin (Width d b)) (pat : Word (Width d b+1)) :
    (read (output hn constant copy (Counting.row hn h j i, pat)) = true ∨
      (Counting.row hn h j i, pat) ∈ enabled.image (PortRows.physical hn (by omega))) ↔
    SweepBridge.panel (bit h) (fun v l => (h,v,l) ∈ enabled) j i pat := by
  rw [output_at, evaluate _ _ _ _ _ _ hc hcopy, PortRows.physical_mem]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [SweepBridge.panel]
  refine Fin.cases ?_ (fun s => ?_) j
  · simp only [SweepBridge.panel, Fin.cases_succ, Fin.cases_zero]
    simp [Prod.exists, eq_comm (a := pat)]
  · simp [SweepBridge.panel, feedbackRow, SweepBridge.feedIndex]

end PEqualNP.Outside.L_clb_111.OutputBridge

namespace PEqualNP.Outside.L_clb_111.AssembleCount

open Ports (Word Width pack)
open Classical

theorem paths {d b k t n : ℕ} (ht : 0 < t) (hn : n=t*(k+2)*Width d b)
    (dst : Fin t → Word d → Word b → Word d)
    (allowed : Fin t → Word d → Word b → Prop)
    (bit : Fin t → Fin (Width d b*k) → Word (Width d b) → Bool)
    (run : ∀ h v l, (List.finRange (Width d b*k)).foldl (fun s i =>
      Ports.shiftStep (d+b+1) s (bit h i s)) (pack v l) = pack (dst h v l) (fun _ => false))
    (P : Fin n → Word (Width d b+1) → Prop)
    (rows : ∀ h j i pat, P (Counting.row hn h j i) pat ↔ SweepBridge.panel (bit h) (allowed h) j i pat) :
    (Finset.univ.filter (fun x : Word n => ∀ u : Fin n,
      P u (fun off : Fin (Width d b+1) => x ⟨(u.val+off.val)%n,
        Nat.mod_lt _ (hn ▸ Nat.mul_pos (Nat.mul_pos ht (by omega)) (Nat.zero_lt_succ _))⟩))).card =
    (Finset.univ.filter (fun q : (Fin t → Word d) × (Fin t → Word b) => ∀ h,
      allowed h (q.1 h) (q.2 h) ∧ dst h (q.1 h) (q.2 h) = q.1 (Counting.nextLayer ht h))).card := by
  classical
  let init : Word d → Word (Width d b) := fun v => pack v (fun _ => false)
  have inj : Function.Injective init := by
    intro v u eq
    have e : (v,fun _ : Fin b => false) = (u,fun _ : Fin b => false) := Ports.pack_inj eq
    exact congrArg Prod.fst e
  have result := Counting.cyclic_path_count ht (by omega) (Nat.zero_lt_succ _) hn P
    (fun z => z 0) init inj
    (fun h => BlockEncoding.write init pack (SweepBridge.sweepStep (bit h)))
    (fun _ => BlockEncoding.write_inj _ _ _ Ports.pack_inj) (fun _ _ => rfl) dst allowed (by
      intro h now later
      rw [SweepBridge.blockOK_iff_legal hn P h (bit h) (allowed h) (rows h),
        BlockEncoding.legal_iff _ _ _ _ Ports.pack_inj]
      apply exists_congr
      rintro ⟨v,l⟩
      rw [SweepBridge.flatten_trace, run])
  refine Eq.trans ?_ (result.trans ?_)
  all_goals
    apply congrArg Finset.card
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end PEqualNP.Outside.L_clb_111.AssembleCount

open PEqualNP.Outside.L_clb_111

theorem PEqualNP.Outside.L_clb_111 : (∀ (d b t : ℕ) (ht : 0 < t),
  let p := d + b + 1
  let w := p + 1
  let block := w * ((p + 2)^2 + 2)
  let n := t * block
  let I := t * 2^d * 2^b * d
  let V := Fin d → Bool
  let Lab := Fin b → Bool
  let E := Fin t × V × Lab
  let S := Fin n × (Fin (w+1) → Bool)
  let pos := fun (k : ℕ) => (⟨k % n, Nat.mod_lt _ (Nat.mul_pos ht (Nat.mul_pos (Nat.succ_pos p) (Nat.lt_of_lt_of_le Nat.zero_lt_two (Nat.le_add_left 2 _))))⟩ : Fin n)
  let succ := fun (layer : Fin t) => (⟨(layer.val + 1) % t, Nat.mod_lt _ ht⟩ : Fin t)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : S → Fin (I + C.size)) (port : E → S),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 512 * t * 2^p * (p+2)^3 ∧
    Function.Injective port ∧ (∀ e, (port e).1.val = e.1.val * block + w) ∧
    ∀ dst : Fin t → V → Lab → V,
      let inp := (List.ofFn (fun h : Fin t => (List.ofFn (fun addr : Fin (2^d) =>
        (List.ofFn (fun j : Fin (2^b) => List.ofFn
          (dst h (fun u => addr.val.testBit (d-1-u.val)) (fun v => j.val.testBit (b-1-v.val))))).flatten)).flatten)).flatten
      let base := fun s : S => (C.wires inp).getD (out s).val false
      (∀ e, base (port e) = false) ∧ ∀ enabled : Finset E,
        (Finset.univ.filter (fun x : Fin n → Bool => ∀ row : Fin n,
          let cell : S := (row, fun off => x (pos (row.val + off.val)))
          base cell = true ∨ cell ∈ enabled.image port)).card =
        (Finset.univ.filter (fun q : (Fin t → V) × (Fin t → Lab) => ∀ h : Fin t,
          (h, q.1 h, q.2 h) ∈ enabled ∧ dst h (q.1 h) (q.2 h) = q.1 (succ h))).card) := by
  classical
  intro d b t ht p w block n I V Lab E S pos succ
  let k := (p+2)^2
  have hn : n=t*(k+2)*Ports.Width d b := by
    change t * (w * (k+2)) = t * (k+2) * w
    rw [Nat.mul_comm w, Nat.mul_assoc]
  obtain ⟨C, constant, copy, bit, cost, hfan, hback, hout, hsize, hcost, heval⟩ :=
    PEqualNP.Outside.L_clb_111_aux.compiledFeedback d b t
  let out := OutputBridge.output hn constant copy
  let port := PortRows.physical (d := d) (b := b) hn (by omega)
  refine ⟨C, out, port, hfan, hback, hout, ?_, PortRows.physical_injective hn _, PortRows.physical_row hn _, ?_⟩
  · rw [hsize]
    exact PEqualNP.Outside.L_clb_111_aux.RowOutput.size_bound d b t cost ht hcost
  intro dst
  let read : Fin (I+C.size) → Bool := fun r =>
    (C.wires (PEqualNP.Outside.L_clb_111_aux.FlatInput.input dst)).getD r.val false
  obtain ⟨hc, hwires, hrun⟩ := heval dst
  refine ⟨OutputBridge.disabled hn constant copy read hc, ?_⟩
  intro enabled
  let P : Fin n → Ports.Word (w+1) → Prop := fun r pat =>
    read (out (r,pat)) = true ∨ (r,pat) ∈ enabled.image port
  have he := AssembleCount.paths ht hn dst (fun h v l => (h,v,l) ∈ enabled) (bit dst)
    hrun P (OutputBridge.panel_at hn constant copy read hc (bit dst) hwires enabled)
  refine Eq.trans ?_ (he.trans ?_)
  all_goals
    apply congrArg Finset.card
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

