import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25874

namespace S25873

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bw (gs : List BinaryGate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w

theorem bw_append (a b : List BinaryGate) (w : List Bool) :
    bw (a ++ b) w = bw b (bw a w) := by simp [bw, List.foldl_append]

theorem bw_length (gs : List BinaryGate) (w : List Bool) :
    (bw gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [bw]
  | cons g gs ih =>
    simpa [bw, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (w ++ [g.op (w.getD g.left false) (w.getD g.right false)])

theorem get_snoc (w : List α) (v d : α) (i : Nat) :
    (w ++ [v]).getD i d = if i < w.length then w.getD i d
      else if i = w.length then v else d := by
  by_cases h : i < w.length
  · simp [List.getD, List.getElem?_append_left h, h]
  · by_cases e : i = w.length
    · simp [e]
    · have : w.length < i := by omega
      rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [h, e]

theorem bw_old (gs : List BinaryGate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (bw gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (bw gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), get_snoc, if_pos h]

abbrev Stat := Bool ⊕ (Nat × Bool)
def sv (w : List Bool) : Stat → Bool
  | .inl b => b
  | .inr (i, b) => xor (w.getD i false) b
def valid (m : Nat) : Stat → Prop
  | .inl _ => True
  | .inr (i, _) => i < m

def good (m : Nat) (g : BinaryGate) : Prop :=
  g.left < m ∧ g.right < m ∧ g.left ≠ g.right ∧
    (∃ y, g.op true y ≠ g.op false y) ∧
    (∃ z, g.op z true ≠ g.op z false)

def unary (f : Bool → Bool) (i : Nat) : Option BinaryGate × Stat :=
  if f false = f true then (none, .inl (f false))
  else (none, .inr (i, f false))

theorem unary_none (f : Bool → Bool) (i : Nat) : (unary f i).1 = none := by
  unfold unary; split <;> rfl

theorem unary_sound (f : Bool → Bool) (w : List Bool) (i : Nat) (h : i < w.length) :
    valid w.length (unary f i).2 ∧ sv w (unary f i).2 = f (w.getD i false) := by
  unfold unary
  split
  · rename_i he
    constructor
    · trivial
    · simp only [sv]; cases w.getD i false <;> simp_all
  · rename_i he
    constructor
    · exact h
    · simp only [sv]
      cases w.getD i false <;> cases h0 : f false <;> cases h1 : f true <;> simp_all

def simplify (op : Bool → Bool → Bool) (m : Nat) (a b : Stat) :
    Option BinaryGate × Stat :=
  match a, b with
  | .inl x, .inl y => (none, .inl (op x y))
  | .inl x, .inr (j, t) => unary (fun y => op x (xor y t)) j
  | .inr (i, s), .inl y => unary (fun x => op (xor x s) y) i
  | .inr (i, s), .inr (j, t) =>
    let f := fun x y => op (xor x s) (xor y t)
    if i = j then unary (fun x => f x x) i
    else if ∀ y, f true y = f false y then unary (f false) j
    else if ∀ x, f x true = f x false then unary (fun x => f x false) i
    else (some ⟨f, i, j⟩, .inr (m, false))

theorem simplify_right_const (op : Bool → Bool → Bool) (m : Nat) (a : Stat) (b : Bool) :
    (simplify op m a (.inl b)).1 = none := by
  cases a with
  | inl a => rfl
  | inr a => exact unary_none _ _

theorem simplify_good (op : Bool → Bool → Bool) (m : Nat) (a b : Stat)
    (ha : valid m a) (hb : valid m b) (g : BinaryGate)
    (hg : (simplify op m a b).1 = some g) : good m g := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [simplify] at hg
    | inr b => simp [simplify, unary_none] at hg
  | inr a =>
    rcases a with ⟨i, s⟩
    cases b with
    | inl b => simp [simplify, unary_none] at hg
    | inr b =>
      rcases b with ⟨j, t⟩
      simp only [simplify] at hg
      split at hg
      · simp [unary_none] at hg
      · rename_i hij
        split at hg
        · simp [unary_none] at hg
        · rename_i hl
          split at hg
          · simp [unary_none] at hg
          · rename_i hr
            cases Option.some.inj hg
            exact ⟨ha, hb, hij, not_forall.mp hl, not_forall.mp hr⟩

theorem simplify_sound (op : Bool → Bool → Bool) (w : List Bool) (a b : Stat)
    (ha : valid w.length a) (hb : valid w.length b) :
    valid (w.length + (simplify op w.length a b).1.toList.length)
      (simplify op w.length a b).2 ∧
    sv (bw (simplify op w.length a b).1.toList w) (simplify op w.length a b).2 =
      op (sv w a) (sv w b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [simplify, valid, sv, bw]
    | inr b =>
      rcases b with ⟨j, t⟩
      simpa [simplify, unary_none, bw, sv] using
        unary_sound (fun y => op a (xor y t)) w j hb
  | inr a =>
    rcases a with ⟨i, s⟩
    cases b with
    | inl b =>
      simpa [simplify, unary_none, bw, sv] using
        unary_sound (fun x => op (xor x s) b) w i ha
    | inr b =>
      rcases b with ⟨j, t⟩
      simp only [simplify]
      split
      · rename_i hij
        subst j
        simpa [unary_none, bw, sv] using
          unary_sound (fun x => op (xor x s) (xor x t)) w i ha
      · split
        · rename_i hl
          have h := unary_sound (fun y => op (xor false s) (xor y t)) w j hb
          simp only [unary_none, Option.toList_none, List.length_nil, Nat.add_zero] at *
          refine ⟨h.1, h.2.trans ?_⟩
          simp only [sv]
          cases w.getD i false
          · rfl
          · exact (hl (w.getD j false)).symm
        · split
          · rename_i hr
            have h := unary_sound (fun x => op (xor x s) (xor false t)) w i ha
            simp only [unary_none, Option.toList_none, List.length_nil, Nat.add_zero] at *
            refine ⟨h.1, h.2.trans ?_⟩
            simp only [sv]
            cases w.getD j false
            · rfl
            · exact (hr (w.getD i false)).symm
          · simp [valid, sv, bw]

def Good (n : Nat) (gs : List BinaryGate) : Prop :=
  ∀ i (hi : i < gs.length), good (n+i) gs[i]

theorem Good_append_one {n : Nat} {gs : List BinaryGate} (h : Good n gs)
    (g : BinaryGate) (hg : good (n+gs.length) g) : Good n (gs ++ [g]) := by
  intro i hi
  by_cases e : i < gs.length
  · simpa only [List.getElem_append_left e] using h i e
  · have : i = gs.length := by simp at hi; omega
    subst i
    simpa using hg

structure Inst where
  op : Bool → Bool → Bool
  left : Nat
  right : Nat
  binary : Bool

def iv (g : Inst) (w : List Bool) : Bool :=
  g.op (w.getD g.left false) (if g.binary then w.getD g.right false else false)

def iw (gs : List Inst) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [iv g w]) w

def localStep (B : Nat → Bool) (m : Nat) (st : List Stat) (gs : List BinaryGate)
    (g : Inst) : Option BinaryGate × Stat :=
  if B st.length then (none, .inl false)
  else simplify g.op (m+gs.length) (st.getD g.left (.inl false))
    (if g.binary then st.getD g.right (.inl false) else .inl false)

def step (B : Nat → Bool) (m : Nat) (acc : List Stat × List BinaryGate) (g : Inst) :
    List Stat × List BinaryGate :=
  let r := localStep B m acc.1 acc.2 g
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def pass (B : Nat → Bool) (m : Nat) (gs : List Inst)
    (acc : List Stat × List BinaryGate) : List Stat × List BinaryGate :=
  gs.foldl (step B m) acc

theorem local_len (B : Nat → Bool) (m : Nat) (st : List Stat) (gs : List BinaryGate)
    (g : Inst) : (localStep B m st gs g).1.toList.length ≤ if g.binary then 1 else 0 := by
  unfold localStep
  split
  · simp
  · cases h : g.binary
    · simp [h, simplify_right_const]
    · simp only [h, Bool.true_eq, ite_true]
      cases (simplify g.op (m+gs.length) (st.getD g.left (.inl false))
        (st.getD g.right (.inl false))).1 <;> simp

theorem pass_len (B : Nat → Bool) (m : Nat) (gs : List Inst)
    (acc : List Stat × List BinaryGate) :
    (pass B m gs acc).2.length ≤ acc.2.length + gs.countP Inst.binary := by
  induction gs generalizing acc with
  | nil => simp [pass]
  | cons g gs ih =>
    have hl := local_len B m acc.1 acc.2 g
    have h := ih (step B m acc g)
    change (pass B m gs (step B m acc g)).2.length ≤
      acc.2.length + (g::gs).countP Inst.binary
    change (pass B m gs (step B m acc g)).2.length ≤
      (acc.2 ++ (localStep B m acc.1 acc.2 g).1.toList).length + gs.countP Inst.binary at h
    rw [List.length_append] at h
    calc
      _ ≤ acc.2.length + (localStep B m acc.1 acc.2 g).1.toList.length +
          gs.countP Inst.binary := h
      _ ≤ acc.2.length + (if g.binary then 1 else 0) + gs.countP Inst.binary :=
        Nat.add_le_add_right (Nat.add_le_add_left hl _) _
      _ = _ := by cases hb : g.binary <;> simp [List.countP_cons, hb] <;> omega

theorem pass_lt (B : Nat → Bool) (m : Nat) (gs : List Inst)
    (acc : List Stat × List BinaryGate) (p : Nat) (hp : p < gs.length)
    (skip : B (acc.1.length+p) = true) :
    (pass B m gs acc).2.length < acc.2.length + gs.length := by
  induction gs generalizing acc p with
  | nil => simp at hp
  | cons g gs ih =>
    cases p with
    | zero =>
      have h := pass_len B m gs (step B m acc g)
      have hc : gs.countP Inst.binary ≤ gs.length := List.countP_le_length
      simp only [Nat.add_zero] at skip
      have hs : (step B m acc g).2.length = acc.2.length := by simp [step, localStep, skip]
      rw [hs] at h
      change (pass B m gs (step B m acc g)).2.length < _
      simpa [step, localStep, skip] using (show
        (pass B m gs (step B m acc g)).2.length < acc.2.length + (g::gs).length by
          simp only [List.length_cons]; omega)
    | succ p =>
      have h := ih (step B m acc g) p (by simpa using hp)
        (by simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using skip)
      have hl := local_len B m acc.1 acc.2 g
      change (pass B m gs (step B m acc g)).2.length < _
      change (pass B m gs (step B m acc g)).2.length <
        (acc.2 ++ (localStep B m acc.1 acc.2 g).1.toList).length + gs.length at h
      rw [List.length_append] at h
      simp only [List.length_cons]
      split at hl <;> omega

def Inv (B : Nat → Bool) (m : Nat) (input old : List Bool)
    (acc : List Stat × List BinaryGate) : Prop :=
  input.length = m ∧ acc.1.length = old.length ∧
    (∀ i, valid (m+acc.2.length) (acc.1.getD i (.inl false))) ∧
    ∀ i, B i = false →
      sv (bw acc.2 input) (acc.1.getD i (.inl false)) = old.getD i false

theorem step_inv (B : Nat → Bool) (m : Nat) (input old : List Bool)
    (acc : List Stat × List BinaryGate) (g : Inst)
    (hl : B g.left = false) (hr : g.binary = true → B g.right = false)
    (h : Inv B m input old acc) :
    Inv B m input (old ++ [iv g old]) (step B m acc g) := by
  obtain ⟨hlen, hold, hv, he⟩ := h
  have hw : (bw acc.2 input).length = m+acc.2.length := by rw [bw_length, hlen]
  have hh : valid (m+acc.2.length+(localStep B m acc.1 acc.2 g).1.toList.length)
      (localStep B m acc.1 acc.2 g).2 ∧
      (B acc.1.length = false →
        sv (bw (localStep B m acc.1 acc.2 g).1.toList (bw acc.2 input))
          (localStep B m acc.1 acc.2 g).2 = iv g old) := by
    unfold localStep
    split
    · rename_i hb
      exact ⟨trivial, by simp_all⟩
    · rename_i hb
      have hs := simplify_sound g.op (bw acc.2 input)
        (acc.1.getD g.left (.inl false))
        (if g.binary then acc.1.getD g.right (.inl false) else .inl false)
        (by rw [hw]; exact hv _)
        (by rw [hw]; split <;> first | exact hv _ | trivial)
      rw [hw] at hs
      refine ⟨hs.1, fun _ => hs.2.trans ?_⟩
      simp only [iv, he _ hl]
      cases hb : g.binary
      · rfl
      · simp only [hb, Bool.true_eq, ite_true]
        rw [he _ (hr hb)]
  refine ⟨hlen, by simp [step, hold], ?_, ?_⟩
  · intro i
    simp only [step, List.length_append, get_snoc]
    split
    · have := hv i
      cases hst : acc.1.getD i (.inl false) <;> simp_all [valid] <;> omega
    · split
      · simpa [Nat.add_assoc] using hh.1
      · trivial
  · intro i hi
    simp only [step, get_snoc, bw_append]
    by_cases hlt : i < acc.1.length
    · have hltold : i < old.length := by omega
      simp only [hlt, hltold, ite_true]
      have hs := hv i
      have hx := he i hi
      cases ht : acc.1.getD i (.inl false) with
      | inl b => rw [ht] at hx; exact hx
      | inr p =>
        rcases p with ⟨j, b⟩
        rw [ht] at hs hx
        simp only [sv]
        rw [bw_old _ _ _ (by rw [hw]; exact hs)]
        exact hx
    · have hltold : ¬ i < old.length := by omega
      simp only [hlt, hltold, ite_false]
      by_cases eq : i = acc.1.length
      · have eqold : i = old.length := by omega
        simp only [eq, eqold, hold, ite_true]
        exact hh.2 (eq ▸ hi)
      · have eqold : i ≠ old.length := by omega
        simp only [eq, eqold, ite_false]
        rfl

theorem step_good (B : Nat → Bool) (m : Nat) (input old : List Bool)
    (acc : List Stat × List BinaryGate) (g : Inst) (h : Inv B m input old acc)
    (hg : Good m acc.2) : Good m (step B m acc g).2 := by
  have hs : ∀ node, (localStep B m acc.1 acc.2 g).1 = some node →
      good (m+acc.2.length) node := by
    intro node hn
    unfold localStep at hn
    split at hn
    · simp at hn
    · apply simplify_good _ _ _ _ (h.2.2.1 _) ?_ node hn
      split <;> first | exact h.2.2.1 _ | trivial
  simp only [step]
  cases he : (localStep B m acc.1 acc.2 g).1 with
  | none => simpa using hg
  | some node => exact Good_append_one hg node (hs node he)

theorem pass_inv (B : Nat → Bool) (m : Nat) (input : List Bool) (gs : List Inst)
    (old : List Bool) (acc : List Stat × List BinaryGate)
    (hread : ∀ g ∈ gs, B g.left = false ∧ (g.binary = true → B g.right = false))
    (h : Inv B m input old acc) (hg : Good m acc.2) :
    Inv B m input (iw gs old) (pass B m gs acc) ∧ Good m (pass B m gs acc).2 := by
  induction gs generalizing old acc with
  | nil => exact ⟨h, hg⟩
  | cons g gs ih =>
    obtain ⟨hl, hr⟩ := hread g List.mem_cons_self
    exact ih (old ++ [iv g old]) (step B m acc g)
      (fun g hg => hread g (List.mem_cons_of_mem _ hg))
      (step_inv B m input old acc g hl hr h) (step_good B m input old acc g h hg)

def init (n : Nat) : List Stat := List.ofFn (fun i : Fin n => .inr (i.val, false))

theorem init_inv (B : Nat → Bool) (n : Nat) (x : Fin n → Bool) :
    Inv B n (List.ofFn x) (List.ofFn x) (init n, []) := by
  refine ⟨List.length_ofFn, by simp [init], ?_, ?_⟩
  · intro i
    change valid n ((List.ofFn (fun i : Fin n => (Sum.inr (i.val, false) : Stat))).getD i (.inl false))
    by_cases h : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa [init] using h), List.getElem_ofFn]
      exact h
    · rw [List.getD_eq_default _ _ (by simp [init]; omega)]
      trivial
  · intro i hi
    change sv (List.ofFn x)
      ((List.ofFn (fun i : Fin n => (Sum.inr (i.val, false) : Stat))).getD i (.inl false)) =
      (List.ofFn x).getD i false
    by_cases h : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa [init] using h), List.getElem_ofFn]
      simp [sv, bw]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      rfl

def encode (g : Gate) : Inst :=
  match g.inputs with
  | [] => ⟨fun _ _ => g.op.eval [], 0, 0, false⟩
  | [i] => ⟨fun a _ => g.op.eval [a], i, 0, false⟩
  | i :: j :: _ => ⟨fun a b => g.op.eval [a,b], i, j, true⟩

theorem encode_eval (g : Gate) (h : g.inputs.length ≤ 2) (w : List Bool) :
    iv (encode g) w = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩⟩ <;> first | rfl | simp at h

theorem encode_count (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.map encode).countP Inst.binary = gs.countP (fun g => g.inputs.length == 2) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    have ht := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [List.map_cons, List.countP_cons, ht]
    rcases g with ⟨op, _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩⟩ <;>
      first | rfl | simp at hg

theorem encode_run (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List Bool) :
    iw (gs.map encode) w = (Circuit.mk gs 0).wires w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change iw (gs.map encode) (w ++ [iv (encode g) w]) = _
    rw [encode_eval g (h g List.mem_cons_self)]
    exact ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) _

def Rep (n : Nat) (f : (Fin n → Bool) → Bool) (gs : List BinaryGate) : Prop :=
  Good n gs ∧ ∃ st, valid (n+gs.length) st ∧
    ∀ x : Fin n → Bool, sv (bw gs (List.ofFn x)) st = f x

theorem source_rep (n : Nat) (C : Circuit)
    (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ gs, gs.length ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      Rep n (fun x => C.eval (List.ofFn x)) gs := by
  let acc := pass (fun _ => false) n (C.gates.map encode) (init n, [])
  have hx (x : Fin n → Bool) := pass_inv (fun _ => false) n (List.ofFn x)
    (C.gates.map encode) (List.ofFn x) (init n, [])
    (by simp) (init_inv _ _ x) (by intro i hi; simp at hi)
  refine ⟨acc.2, ?_, (hx (fun _ => false)).2, acc.1.getD C.output (.inl false),
    (hx (fun _ => false)).1.2.2.1 _, ?_⟩
  · have hh := pass_len (fun _ => false) n (C.gates.map encode) (init n, [])
    simpa [encode_count C.gates h] using hh
  · intro x
    have he := (hx x).1.2.2.2 C.output rfl
    rw [encode_run C.gates h] at he
    exact he

def toggle (st : Stat) (b : Bool) : Stat :=
  match st with
  | .inl c => .inl (xor c b)
  | .inr (i,c) => .inr (i, xor c b)

theorem toggle_valid (st : Stat) (b : Bool) (m : Nat) :
    valid m (toggle st b) = valid m st := by cases st <;> rfl

theorem toggle_value (st : Stat) (b : Bool) (w : List Bool) :
    sv w (toggle st b) = xor (sv w st) b := by
  cases st with
  | inl c => rfl
  | inr p => exact (Bool.xor_assoc _ _ _).symm

def binaryInst (g : BinaryGate) : Inst := ⟨g.op, g.left, g.right, true⟩

theorem binary_run (gs : List BinaryGate) (w : List Bool) :
    iw (gs.map binaryInst) w = bw gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem delete_unused (n : Nat) (f : (Fin n → Bool) → Bool) (gs : List BinaryGate)
    (q : Nat) (b : Bool) (he : ∀ x, sv (bw gs (List.ofFn x)) (.inr (q,b)) = f x)
    (p : Nat) (hp : p < gs.length) (hq : q ≠ n+p)
    (hread : ∀ g ∈ gs, g.left ≠ n+p ∧ g.right ≠ n+p) :
    ∃ gs', gs'.length < gs.length ∧ Rep n f gs' := by
  let B := fun i => decide (i = n+p)
  let acc := pass B n (gs.map binaryInst) (init n, [])
  have read : ∀ g ∈ gs.map binaryInst,
      B g.left = false ∧ (g.binary = true → B g.right = false) := by
    intro g hg
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hg
    obtain ⟨hl, hr⟩ := hread a ha
    subst g
    simpa [B, binaryInst] using And.intro hl (fun _ : True => hr)
  have hx (x : Fin n → Bool) := pass_inv B n (List.ofFn x) (gs.map binaryInst)
    (List.ofFn x) (init n, []) read (init_inv _ _ x) (by intro i hi; simp at hi)
  refine ⟨acc.2, ?_, (hx (fun _ => false)).2,
    toggle (acc.1.getD q (.inl false)) b, ?_, ?_⟩
  · have hh := pass_lt B n (gs.map binaryInst) (init n, []) p (by simpa using hp)
      (by simp [B, init])
    simpa using hh
  · rw [toggle_valid]
    exact (hx (fun _ => false)).1.2.2.1 _
  · intro x
    rw [toggle_value]
    have hh := (hx x).1.2.2.2 q (by simp [B, hq])
    rw [binary_run] at hh
    rw [hh]
    exact he x

def Trivial (n : Nat) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ b, ∀ x, f x = b) ∨ ∃ (i : Fin n) (b : Bool), ∀ x, f x = xor (x i) b

theorem nonsimple (n : Nat) (f : (Fin n → Bool) → Bool) (gs : List BinaryGate)
    (st : Stat) (hv : valid (n+gs.length) st)
    (he : ∀ x, sv (bw gs (List.ofFn x)) st = f x) (hn : ¬ Trivial n f) :
    ∃ q b, st = .inr (q,b) ∧ n ≤ q ∧ q < n+gs.length := by
  cases st with
  | inl b =>
    exact False.elim (hn (Or.inl ⟨b, fun x => (he x).symm⟩))
  | inr p =>
    rcases p with ⟨q,b⟩
    by_cases hq : q < n
    · apply False.elim
      apply hn
      refine Or.inr ⟨⟨q,hq⟩, b, ?_⟩
      intro x
      rw [← he x]
      simp only [sv]
      rw [bw_old _ _ _ (by simpa using hq),
        List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_ofFn]
    · exact ⟨q,b,rfl,by omega,hv⟩

theorem minimal_live (n : Nat) (f : (Fin n → Bool) → Bool) (gs : List BinaryGate)
    (hg : Good n gs)
    (hmin : ∀ es, Rep n f es → gs.length ≤ es.length)
    (q : Nat) (b : Bool) (hqn : n ≤ q) (hqv : q < n+gs.length)
    (he : ∀ x, sv (bw gs (List.ofFn x)) (.inr (q,b)) = f x) :
    q+1 = n+gs.length ∧
    ∀ j : Fin gs.length, j.val+1 < gs.length →
      ∃ r : Fin gs.length, j.val < r.val ∧
        ((gs.get r).left = n+j.val ∨ (gs.get r).right = n+j.val) := by
  have hpos : 0 < gs.length := by omega
  have last : q+1 = n+gs.length := by
    by_contra hn
    have hp : gs.length-1 < gs.length := by omega
    have read : ∀ g ∈ gs, g.left ≠ n+(gs.length-1) ∧ g.right ≠ n+(gs.length-1) := by
      intro g hm
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
      have hh := hg i.val i.isLt
      change good (n+i.val) (gs.get i) at hh
      have hi := i.isLt
      exact ⟨by have := hh.1; omega, by have := hh.2.1; omega⟩
    obtain ⟨es, hs, hr⟩ := delete_unused n f gs q b he (gs.length-1) hp
      (by omega) read
    have := hmin es hr
    omega
  refine ⟨last, ?_⟩
  intro j hj
  by_contra hn
  have read : ∀ g ∈ gs, g.left ≠ n+j.val ∧ g.right ≠ n+j.val := by
    intro g hm
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
    by_cases hij : j.val < i.val
    · exact ⟨fun heq => hn ⟨i, hij, Or.inl heq⟩, fun heq => hn ⟨i,hij,Or.inr heq⟩⟩
    · have hh := hg i.val i.isLt
      change good (n+i.val) (gs.get i) at hh
      exact ⟨by have := hh.1; omega, by have := hh.2.1; omega⟩
  obtain ⟨es, hs, hr⟩ := delete_unused n f gs q b he j.val j.isLt (by omega) read
  have := hmin es hr
  omega

def lastToggle (gs : List BinaryGate) (b : Bool) : List BinaryGate :=
  gs.mapIdx fun i g =>
    if i+1 = gs.length then ⟨fun a c => xor (g.op a c) b, g.left, g.right⟩ else g

theorem lastToggle_length (gs : List BinaryGate) (b : Bool) :
    (lastToggle gs b).length = gs.length := by simp [lastToggle]

theorem lastToggle_wires (gs : List BinaryGate) (b : Bool) (i : Nat)
    (h : i < gs.length) :
    ((lastToggle gs b)[i]'(by rw [lastToggle_length]; exact h)).left = gs[i].left ∧
    ((lastToggle gs b)[i]'(by rw [lastToggle_length]; exact h)).right = gs[i].right := by
  simp only [lastToggle, List.getElem_mapIdx]
  split <;> exact ⟨rfl,rfl⟩

theorem lastToggle_good (n : Nat) (gs : List BinaryGate) (b : Bool) (hg : Good n gs) :
    Good n (lastToggle gs b) := by
  intro i hi
  have hi' : i < gs.length := by simpa [lastToggle] using hi
  have hh := hg i hi'
  simp only [lastToggle, List.getElem_mapIdx]
  split
  · obtain ⟨hl,hr,hne,⟨y,hy⟩,⟨z,hz⟩⟩ := hh
    refine ⟨hl,hr,hne,⟨y,?_⟩,⟨z,?_⟩⟩
    · cases b <;> simpa using hy
    · cases b <;> simpa using hz
  · exact hh

theorem lastToggle_eval (gs : List BinaryGate) (b : Bool) (w : List Bool)
    (hp : 0 < gs.length) :
    (bw (lastToggle gs b) w).getD (w.length+gs.length-1) false =
      xor ((bw gs w).getD (w.length+gs.length-1) false) b := by
  induction gs using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton pre g ih =>
    have hm : lastToggle (pre ++ [g]) b =
        pre ++ [⟨fun a c => xor (g.op a c) b, g.left, g.right⟩] := by
      apply List.ext_getElem
      · simp [lastToggle]
      · intro i hi hi'
        simp only [lastToggle, List.getElem_mapIdx]
        by_cases hit : i < pre.length
        · rw [List.getElem_append_left hit, List.getElem_append_left hit]
          rw [if_neg (by simp; omega)]
        · have hie : i = pre.length := by
            have hilen : i < pre.length+1 := by simpa [lastToggle] using hi
            omega
          subst i
          simp
    rw [hm, bw_append, bw_append]
    have hl := bw_length pre w
    have hi : w.length+(pre++[g]).length-1 = (bw pre w).length := by simp at *; omega
    rw [hi]
    simp [bw, List.getD]

theorem normalized (n : Nat) (C : Circuit)
    (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Trivial n (fun x => C.eval (List.ofFn x)) ∨
    ∃ D : BinaryCircuit,
      0 < D.size ∧ D.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      D.output+1 = n+D.size ∧
      (∀ j : Fin D.gates.length,
        good (n+j.val) (D.gates.get j) ∧
        (j.val+1 < D.size → ∃ r : Fin D.gates.length, j.val < r.val ∧
          ((D.gates.get r).left = n+j.val ∨ (D.gates.get r).right = n+j.val))) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  classical
  let f := fun x : Fin n → Bool => C.eval (List.ofFn x)
  by_cases ht : Trivial n f
  · exact Or.inl ht
  · apply Or.inr
    obtain ⟨original, hbound, hrep⟩ := source_rep n C h
    have ex : ∃ k, ∃ gs, gs.length = k ∧ Rep n f gs :=
      ⟨original.length, original, rfl, hrep⟩
    obtain ⟨gs, hlen, hg, st, hv, he⟩ := Nat.find_spec ex
    have hmin (es) (hr : Rep n f es) : gs.length ≤ es.length := by
      rw [hlen]
      exact Nat.find_min' ex ⟨es,rfl,hr⟩
    have hb : gs.length ≤ C.gates.countP (fun g => g.inputs.length == 2) :=
      (hmin original hrep).trans hbound
    obtain ⟨q,b,rfl,hqn,hqv⟩ := nonsimple n f gs st hv he ht
    obtain ⟨hq,hlive⟩ := minimal_live n f gs hg hmin q b hqn hqv he
    let D : BinaryCircuit := ⟨lastToggle gs b,q⟩
    have hsize : D.size = gs.length := lastToggle_length gs b
    have hpos : 0 < gs.length := by omega
    refine ⟨D, by omega, by omega, by change q+1 = n+D.size; omega, ?_, ?_⟩
    · intro j
      have hj : j.val < gs.length := by simpa [D, lastToggle] using j.isLt
      refine ⟨lastToggle_good n gs b hg j.val j.isLt, ?_⟩
      intro hn
      obtain ⟨r,hr,heq⟩ := hlive ⟨j.val,hj⟩ (by simpa [hsize] using hn)
      let r' : Fin D.gates.length := ⟨r.val, by simpa [D, lastToggle] using r.isLt⟩
      refine ⟨r',hr,?_⟩
      have hw := lastToggle_wires gs b r.val r.isLt
      change ((lastToggle gs b)[r.val]'r'.isLt).left = n+j.val ∨
        ((lastToggle gs b)[r.val]'r'.isLt).right = n+j.val
      rw [hw.1, hw.2]
      exact heq
    · intro x
      change (bw (lastToggle gs b) (List.ofFn x)).getD q false = f x
      have hq' : q = (List.ofFn x).length+gs.length-1 := by simp; omega
      rw [hq',lastToggle_eval gs b (List.ofFn x) hpos,←hq']
      exact he x


theorem thm : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
  let val := fun x : Fin n → Bool => C.eval (List.ofFn x)
  (∃ b : Bool, ∀ x, val x = b) ∨
  (∃ (i : Fin n) (flip : Bool), ∀ x, val x = Bool.xor (x i) flip) ∨
  ∃ D : PEqualNP.MetaComplexity.BinaryCircuit,
    0 < D.size ∧ D.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
    D.output + 1 = n + D.size ∧
    (∀ j : Fin D.gates.length,
      let node := D.gates.get j
      node.left < n + j.val ∧ node.right < n + j.val ∧ node.left ≠ node.right ∧
      (∃ y : Bool, node.op true y ≠ node.op false y) ∧
      (∃ z : Bool, node.op z true ≠ node.op z false) ∧
      (j.val + 1 < D.size → ∃ reader : Fin D.gates.length, j.val < reader.val ∧
        ((D.gates.get reader).left = n + j.val ∨ (D.gates.get reader).right = n + j.val))) ∧
    ∀ input : Fin n → Bool, D.eval (List.ofFn input) = val input) := by
  intro n C h
  rcases normalized n C h with ht | ⟨D,hp,hb,ho,hg,he⟩
  · rcases ht with hc | hi
    · exact Or.inl hc
    · exact Or.inr (Or.inl hi)
  · refine Or.inr (Or.inr ⟨D,hp,hb,ho,?_,he⟩)
    intro j
    obtain ⟨⟨hl,hr,hne,hy,hz⟩,hlive⟩ := hg j
    exact ⟨hl,hr,hne,hy,hz,hlive⟩

end S25873

namespace S25872

def step (w : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

lemma getD_append_left (l1 l2 : List Bool) (u : ℕ) (h : u < l1.length) :
    (l1 ++ l2).getD u false = l1.getD u false := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right (l1 l2 : List Bool) (u : ℕ) (h : l1.length ≤ u) :
    (l1 ++ l2).getD u false = l2.getD (u - l1.length) false := by
  simp [List.getD, List.getElem?_append_right h]

lemma getD_eq_false_of_le (l : List Bool) (u : ℕ) (h : l.length ≤ u) :
    l.getD u false = false := by
  simp [List.getD, List.getElem?_eq_none h]

lemma getD_replicate_false (k u : ℕ) :
    (List.replicate k false).getD u false = false := by
  by_cases h : u < k
  · have hlen : u < (List.replicate k false).length := by simpa using h
    simp [List.getD, List.getElem?_eq_getElem hlen]
  · have hlen : (List.replicate k false).length ≤ u := by simp; omega
    exact getD_eq_false_of_le _ _ hlen

lemma getD_one (k : ℕ) (label : Fin k) (u : ℕ) (h : u < k) :
    (List.ofFn (fun v : Fin k => decide (v = label))).getD u false = decide (u = label.val) := by
  simp [List.getD, h, Fin.ext_iff]

lemma foldl_length (gs : List PEqualNP.MetaComplexity.BinaryGate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g tl ih =>
    simp only [List.foldl, List.length_cons]
    rw [ih]
    simp [step]
    omega

lemma foldl_getD_lt (gs : List PEqualNP.MetaComplexity.BinaryGate) (x : List Bool) (u : ℕ)
    (hu : u < x.length) :
    (gs.foldl step x).getD u false = x.getD u false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.foldl]
    have hu' : u < (step x g).length := by
      simp [step]
      omega
    rw [ih (step x g) hu']
    exact getD_append_left x _ u hu

lemma foldl_getD_gate (gs : List PEqualNP.MetaComplexity.BinaryGate) (x : List Bool)
    (k : ℕ) (hk : k < gs.length)
    (hl : (gs.get ⟨k, hk⟩).left < x.length + k)
    (hr : (gs.get ⟨k, hk⟩).right < x.length + k) :
    (gs.foldl step x).getD (x.length + k) false =
      (gs.get ⟨k, hk⟩).op
        ((gs.foldl step x).getD (gs.get ⟨k, hk⟩).left false)
        ((gs.foldl step x).getD (gs.get ⟨k, hk⟩).right false) := by
  induction gs generalizing x k with
  | nil => cases hk
  | cons g tl ih =>
    cases k with
    | zero =>
      simp only [List.foldl, Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero] at hl hr ⊢
      have hlen : x.length < (step x g).length := by simp [step]
      rw [foldl_getD_lt tl (step x g) x.length hlen]
      rw [foldl_getD_lt tl (step x g) g.left (by simp [step]; omega)]
      rw [foldl_getD_lt tl (step x g) g.right (by simp [step]; omega)]
      simp only [step]
      rw [getD_append_left x _ g.left hl, getD_append_left x _ g.right hr]
      rw [getD_append_right x _ x.length (Nat.le_refl _)]
      simp
    | succ k' =>
      have hk' : k' < tl.length := by
        simp only [List.length_cons] at hk
        omega
      have hlen : (step x g).length = x.length + 1 := by simp [step]
      have hidx : x.length + (k' + 1) = (step x g).length + k' := by omega
      have hget : (g :: tl).get ⟨k' + 1, hk⟩ = tl.get ⟨k', hk'⟩ := rfl
      rw [hget] at hl hr ⊢
      simp only [List.foldl]
      rw [hidx]
      exact ih (step x g) k' hk' (by omega) (by omega)

lemma wires_getD_input (D : PEqualNP.MetaComplexity.BinaryCircuit) (x : List Bool)
    (raw w : ℕ) (hx : x.length = raw) (hw : w < raw) :
    (D.wires x).getD w false = x.getD w false := by
  exact foldl_getD_lt D.gates x w (by omega)

lemma wires_getD_gate (D : PEqualNP.MetaComplexity.BinaryCircuit) (x : List Bool)
    (raw g : ℕ) (hx : x.length = raw) (hg : g < D.gates.length)
    (hl : (D.gates.get ⟨g, hg⟩).left < raw + g)
    (hr : (D.gates.get ⟨g, hg⟩).right < raw + g) :
    (D.wires x).getD (raw + g) false =
      (D.gates.get ⟨g, hg⟩).op
        ((D.wires x).getD (D.gates.get ⟨g, hg⟩).left false)
        ((D.wires x).getD (D.gates.get ⟨g, hg⟩).right false) := by
  have h := foldl_getD_gate D.gates x g hg (by omega) (by omega)
  rw [hx] at h
  exact h

lemma wires_getD_ge (D : PEqualNP.MetaComplexity.BinaryCircuit) (x : List Bool)
    (raw w : ℕ) (hx : x.length = raw) (hw : raw + D.gates.length ≤ w) :
    (D.wires x).getD w false = false := by
  apply getD_eq_false_of_le
  have hlen : (D.wires x).length = x.length + D.gates.length :=
    foldl_length D.gates x
  omega

lemma bool_xor_factor (f : Bool → Bool) (a b : Bool) :
    (f a != f b) = ((f true != f false) && (a != b)) := by
  cases a <;> cases b <;> cases f false <;> cases f true <;> rfl

def regEval (D : PEqualNP.MetaComplexity.BinaryCircuit) (raw : ℕ)
    (sources entry : Finset ℕ) (src : ℕ → Bool) (ent : ↥entry → Bool) (w : ℕ) : Bool :=
  if w ∈ sources then src w
  else if he : w ∈ entry then ent ⟨w, he⟩
  else if h : raw ≤ w ∧ w - raw < D.gates.length then
    let node := D.gates.get ⟨w - raw, h.2⟩
    if _hl : node.left < w then
      if _hr : node.right < w then
        node.op (regEval D raw sources entry src ent node.left)
                (regEval D raw sources entry src ent node.right)
      else false
    else false
  else false
termination_by w

def extEval (D : PEqualNP.MetaComplexity.BinaryCircuit) (raw top : ℕ)
    (xbase : List Bool) (b : Bool) (w : ℕ) : Bool :=
  if w = raw + top then b
  else if w < raw then xbase.getD w false
  else if h : raw ≤ w ∧ w - raw < D.gates.length then
    let node := D.gates.get ⟨w - raw, h.2⟩
    if _hl : node.left < w then
      if _hr : node.right < w then
        node.op (extEval D raw top xbase b node.left)
                (extEval D raw top xbase b node.right)
      else false
    else false
  else false
termination_by w

lemma wires_eq_before_top (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hreg : region ⊆ Finset.range D.size)
    (htop : top ∈ region)
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (x y : List Bool) (hx : x.length = raw) (hy : y.length = raw)
    (hagree : ∀ u < raw, u ∉ sources → x.getD u false = y.getD u false)
    (w : ℕ) (hlt : w < raw + top) (hns : w ∉ sources) (hni : ¬(raw ≤ w ∧ w - raw ∈ region)) :
    (D.wires x).getD w false = (D.wires y).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwr : w < raw
    · rw [wires_getD_input D x raw w hx hwr, wires_getD_input D y raw w hy hwr]
      exact hagree w hwr hns
    · have htop_lt : top < D.gates.length := Finset.mem_range.mp (hreg htop)
      have hge : raw ≤ w := by omega
      have hglen : w - raw < D.gates.length := by omega
      have hnr : w - raw ∉ region := fun hr => hni ⟨hge, hr⟩
      let g : Fin D.gates.length := ⟨w - raw, hglen⟩
      have hgl := hgates g (D.gates.get g).left (Finset.mem_insert_self _ _)
      have hgr := hgates g (D.gates.get g).right (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hleft_lt : (D.gates.get g).left < w := by
        have := hgl.1
        change (D.gates.get g).left < raw + (w - raw) at this
        omega
      have hright_lt : (D.gates.get g).right < w := by
        have := hgr.1
        change (D.gates.get g).right < raw + (w - raw) at this
        omega
      have hleft_out := hgl.2.2 hnr
      have hright_out := hgr.2.2 hnr
      have hw_eq : raw + (w - raw) = w := by omega
      have hl_eq := ih (D.gates.get g).left hleft_lt (by omega) hleft_out.1
        (fun hin => by have := hleft_out.2 hin; omega)
      have hr_eq := ih (D.gates.get g).right hright_lt (by omega) hright_out.1
        (fun hin => by have := hright_out.2 hin; omega)
      have hgx := wires_getD_gate D x raw (w - raw) hx hglen hgl.1 hgr.1
      have hgy := wires_getD_gate D y raw (w - raw) hy hglen hgl.1 hgr.1
      rw [hw_eq] at hgx hgy
      rw [hgx, hgy]
      exact congrArg₂ (D.gates.get g).op hl_eq hr_eq

lemma wires_eq_regEval (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hsources_lt : ∀ s ∈ sources, s < raw)
    (hreg : region ⊆ Finset.range D.size)
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (x : List Bool) (hx : x.length = raw)
    (src : ℕ → Bool) (ent : ↥entry → Bool)
    (hsrc : ∀ s ∈ sources, x.getD s false = src s)
    (hent : ∀ e : ↥entry, (D.wires x).getD e.val false = ent e)
    (w : ℕ) (hw : w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) :
    (D.wires x).getD w false = regEval D raw sources entry src ent w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [regEval]
    by_cases hws : w ∈ sources
    · simp only [hws, ↓reduceIte]
      rw [wires_getD_input D x raw w hx (hsources_lt w hws)]
      exact hsrc w hws
    · by_cases hwe : w ∈ entry
      · simp only [hws, hwe, ↓reduceIte]
        exact hent ⟨w, hwe⟩
      · simp only [hws, hwe, ↓reduceIte]
        have hin : raw ≤ w ∧ w - raw ∈ region := by
          rcases hw with h1 | h2 | h3
          · exact absurd h1 hws
          · exact h2
          · exact absurd h3 hwe
        have hglen : w - raw < D.gates.length := Finset.mem_range.mp (hreg hin.2)
        have hcond : raw ≤ w ∧ w - raw < D.gates.length := ⟨hin.1, hglen⟩
        simp only [hcond, ↓reduceDIte]
        let g : Fin D.gates.length := ⟨w - raw, hglen⟩
        have hgl := hgates g (D.gates.get g).left (Finset.mem_insert_self _ _)
        have hgr := hgates g (D.gates.get g).right (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hw_eq : raw + (w - raw) = w := by omega
        have hl_lt : (D.gates.get g).left < w := by
          have := hgl.1
          change (D.gates.get g).left < raw + (w - raw) at this
          omega
        have hr_lt : (D.gates.get g).right < w := by
          have := hgr.1
          change (D.gates.get g).right < raw + (w - raw) at this
          omega
        simp only [g, hl_lt, hr_lt, ↓reduceDIte]
        have hl_eq := ih (D.gates.get g).left hl_lt (hgl.2.1 hin.2)
        have hr_eq := ih (D.gates.get g).right hr_lt (hgr.2.1 hin.2)
        have hgate := wires_getD_gate D x raw (w - raw) hx hglen hgl.1 hgr.1
        rw [hw_eq] at hgate
        rw [hgate]
        exact congrArg₂ (D.gates.get g).op hl_eq hr_eq

lemma wires_eq_extEval (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (x xbase : List Bool) (hx : x.length = raw)
    (hagree : ∀ u < raw, u ∉ sources → x.getD u false = xbase.getD u false)
    (w : ℕ) (hns : w ∉ sources) (hin : (raw ≤ w ∧ w - raw ∈ region) → w = raw + top) :
    (D.wires x).getD w false =
      extEval D raw top xbase ((D.wires x).getD (raw + top) false) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [extEval]
    by_cases ht : w = raw + top
    · simp [ht]
    · by_cases hwr : w < raw
      · simp only [ht, hwr, ↓reduceIte]
        rw [wires_getD_input D x raw w hx hwr]
        exact hagree w hwr hns
      · by_cases hcond : raw ≤ w ∧ w - raw < D.gates.length
        · simp only [ht, hwr, hcond, ↓reduceIte, ↓reduceDIte]
          have hnr : w - raw ∉ region := fun hr => ht (hin ⟨hcond.1, hr⟩)
          let g : Fin D.gates.length := ⟨w - raw, hcond.2⟩
          have hgl := hgates g (D.gates.get g).left (Finset.mem_insert_self _ _)
          have hgr := hgates g (D.gates.get g).right (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          have hw_eq : raw + (w - raw) = w := by omega
          have hl_lt : (D.gates.get g).left < w := by
            have := hgl.1
            change (D.gates.get g).left < raw + (w - raw) at this
            omega
          have hr_lt : (D.gates.get g).right < w := by
            have := hgr.1
            change (D.gates.get g).right < raw + (w - raw) at this
            omega
          simp only [g, hl_lt, hr_lt, ↓reduceDIte]
          have hlo := hgl.2.2 hnr
          have hro := hgr.2.2 hnr
          have hl_eq := ih (D.gates.get g).left hl_lt hlo.1 hlo.2
          have hr_eq := ih (D.gates.get g).right hr_lt hro.1 hro.2
          have hgate := wires_getD_gate D x raw (w - raw) hx hcond.2 hgl.1 hgr.1
          rw [hw_eq] at hgate
          rw [hgate]
          exact congrArg₂ (D.gates.get g).op hl_eq hr_eq
        · simp only [ht, hwr, hcond, ↓reduceIte, ↓reduceDIte]
          exact wires_getD_ge D x raw w hx (by omega)

lemma factor_bank (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hsources_lt : ∀ s ∈ sources, s < raw)
    (hreg : region ⊆ Finset.range D.size)
    (htop : top ∈ region)
    (hentry : ∀ e ∈ entry, e < raw + top ∧ e ∉ sources ∧ ¬(raw ≤ e ∧ e - raw ∈ region))
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (hout_ns : D.output ∉ sources)
    (hout_in : (raw ≤ D.output ∧ D.output - raw ∈ region) → D.output = raw + top)
    (x_on x_off : List Bool) (hon_len : x_on.length = raw) (hoff_len : x_off.length = raw)
    (target : ℕ)
    (hagree : ∀ u < raw, u ∉ sources → x_on.getD u false = x_off.getD u false)
    (hoff_src : ∀ s ∈ sources, x_off.getD s false = false)
    (hon_src : ∀ s ∈ sources, x_on.getD s false = decide (s = target)) :
    (D.eval x_on != D.eval x_off) =
      ((extEval D raw top x_off true D.output != extEval D raw top x_off false D.output) &&
       (regEval D raw sources entry (fun s => decide (s = target))
          (fun e => (D.wires x_off).getD e.val false) (raw + top) !=
        regEval D raw sources entry (fun _ => false)
          (fun e => (D.wires x_off).getD e.val false) (raw + top))) := by
  have heval_on : D.eval x_on =
      extEval D raw top x_off ((D.wires x_on).getD (raw + top) false) D.output :=
    wires_eq_extEval D raw top sources region entry hgates x_on x_off hon_len hagree
      D.output hout_ns hout_in
  have heval_off : D.eval x_off =
      extEval D raw top x_off ((D.wires x_off).getD (raw + top) false) D.output :=
    wires_eq_extEval D raw top sources region entry hgates x_off x_off hoff_len
      (fun _ _ _ => rfl) D.output hout_ns hout_in
  rw [heval_on, heval_off]
  rw [bool_xor_factor (fun b => extEval D raw top x_off b D.output)]
  have hent_on : ∀ e : ↥entry,
      (D.wires x_on).getD e.val false = (D.wires x_off).getD e.val false := by
    intro e
    have he := hentry e.val e.property
    exact wires_eq_before_top D raw top sources region entry hreg htop hgates
      x_on x_off hon_len hoff_len hagree e.val he.1 he.2.1 he.2.2
  have htop_in : raw + top ∈ sources ∨ (raw ≤ raw + top ∧ raw + top - raw ∈ region) ∨ raw + top ∈ entry :=
    Or.inr (Or.inl ⟨Nat.le_add_right raw top, by simpa using htop⟩)
  have htop_on : (D.wires x_on).getD (raw + top) false =
      regEval D raw sources entry (fun s => decide (s = target))
        (fun e => (D.wires x_off).getD e.val false) (raw + top) :=
    wires_eq_regEval D raw top sources region entry hsources_lt hreg hgates
      x_on hon_len (fun s => decide (s = target))
      (fun e => (D.wires x_off).getD e.val false) hon_src hent_on (raw + top) htop_in
  have htop_off : (D.wires x_off).getD (raw + top) false =
      regEval D raw sources entry (fun _ => false)
        (fun e => (D.wires x_off).getD e.val false) (raw + top) :=
    wires_eq_regEval D raw top sources region entry hsources_lt hreg hgates
      x_off hoff_len (fun _ => false)
      (fun e => (D.wires x_off).getD e.val false) hoff_src (fun _ => rfl) (raw + top) htop_in
  rw [htop_on, htop_off]


theorem thm : ∀ (n m : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n+m
  let sources := R.image (fun i => i.val) ∪ B.image (fun j => n+j.val)
  let inside := fun w : ℕ => raw ≤ w ∧ w-raw ∈ region
  let one := fun (k : ℕ) (label : Fin k) => List.ofFn (fun v : Fin k => decide (v = label))
  let rowOff := fun j : Fin m => List.replicate n false ++ one m j
  let colOff := fun i : Fin n => one n i ++ List.replicate m false
  let value := fun (i : Fin n) (j : Fin m) => D.eval (one n i ++ one m j)
  region ⊆ Finset.range D.size → top ∈ region →
  (∀ e ∈ entry, e < raw+top ∧ e ∉ sources ∧ ¬inside e) →
  (∀ g : Fin D.gates.length,
    let node := D.gates.get g
    ∀ w ∈ ({node.left, node.right} : Finset ℕ),
      w < raw+g.val ∧
      (g.val ∈ region → w ∈ sources ∨ inside w ∨ w ∈ entry) ∧
      (g.val ∉ region → w ∉ sources ∧ (inside w → w = raw+top))) →
  D.output ∉ sources → (inside D.output → D.output = raw+top) →
    (∃ (mask : Fin m → Bool) (response : Fin n → (↥entry → Bool) → Bool),
      ∀ i ∈ R, ∀ j ∉ B,
        (value i j != D.eval (rowOff j)) =
        (mask j && response i (fun e => (D.wires (rowOff j)).getD e.val false))) ∧
    (∃ (mask : Fin n → Bool) (response : Fin m → (↥entry → Bool) → Bool),
      ∀ j ∈ B, ∀ i ∉ R,
        (value i j != D.eval (colOff i)) =
        (mask i && response j (fun e => (D.wires (colOff i)).getD e.val false))) := by
  intro n m D R B region entry top raw sources inside one rowOff colOff value
    hreg htop hentry hgates hout_ns hout_in
  have hsources_lt : ∀ s ∈ sources, s < raw := by
    intro s hs
    rcases Finset.mem_union.mp hs with hR | hB
    · rcases Finset.mem_image.mp hR with ⟨i, _, rfl⟩
      omega
    · rcases Finset.mem_image.mp hB with ⟨j, _, rfl⟩
      omega
  constructor
  · refine ⟨fun j =>
        extEval D raw top (rowOff j) true D.output !=
        extEval D raw top (rowOff j) false D.output,
      fun i ent =>
        regEval D raw sources entry
          (fun s => decide (s = i.val)) ent (raw + top) !=
        regEval D raw sources entry
          (fun _ => false) ent (raw + top),
      ?_⟩
    intro i hiR j hjB
    have hon_len : (one n i ++ one m j).length = raw := by
      simp [one, raw]
    have hoff_len : (rowOff j).length = raw := by
      simp [rowOff, one, raw]
    have hagree : ∀ u < raw, u ∉ sources →
        (one n i ++ one m j).getD u false = (rowOff j).getD u false := by
      intro u hu huns
      by_cases hun : u < n
      · have h1 : (one n i ++ one m j).getD u false = (one n i).getD u false :=
          getD_append_left _ _ u (by simp [one, hun])
        have h2 : (rowOff j).getD u false = (List.replicate n false).getD u false :=
          getD_append_left _ _ u (by simp [hun])
        rw [h1, h2, getD_one n i u hun,
          getD_replicate_false]
        have hne : u ≠ i.val := by
          intro heq
          apply huns
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiR, heq.symm⟩)
        simp [hne]
      · have hge : n ≤ u := by omega
        have h1 : (one n i ++ one m j).getD u false = (one m j).getD (u - n) false := by
          rw [getD_append_right (one n i) (one m j) u (by simp [one, hge])]
          simp [one]
        have h2 : (rowOff j).getD u false = (one m j).getD (u - n) false := by
          rw [getD_append_right (List.replicate n false) (one m j) u (by simp [hge])]
          simp
        rw [h1, h2]
    have hoff_src : ∀ s ∈ sources, (rowOff j).getD s false = false := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', _, rfl⟩
        rw [getD_append_left _ _ i'.val (by simp)]
        exact getD_replicate_false n i'.val
      · rcases Finset.mem_image.mp hB with ⟨j', hj'B, rfl⟩
        have h2 : (rowOff j).getD (n + j'.val) false = (one m j).getD j'.val false := by
          rw [getD_append_right
            (List.replicate n false) (one m j) (n + j'.val) (by simp)]
          simp
        rw [h2, getD_one m j j'.val j'.isLt]
        have hne : j'.val ≠ j.val := fun heq => hjB (Fin.ext heq ▸ hj'B)
        simp [hne]
    have hon_src : ∀ s ∈ sources, (one n i ++ one m j).getD s false = decide (s = i.val) := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', _, rfl⟩
        rw [getD_append_left _ _ i'.val (by simp [one])]
        exact getD_one n i i'.val i'.isLt
      · rcases Finset.mem_image.mp hB with ⟨j', hj'B, rfl⟩
        have h1 : (one n i ++ one m j).getD (n + j'.val) false = (one m j).getD j'.val false := by
          rw [getD_append_right
            (one n i) (one m j) (n + j'.val) (by simp [one])]
          simp [one]
        rw [h1, getD_one m j j'.val j'.isLt]
        have hne1 : j'.val ≠ j.val := fun heq => hjB (Fin.ext heq ▸ hj'B)
        have hne2 : n + j'.val ≠ i.val := by omega
        simp [hne1, hne2]
    exact factor_bank D raw top sources region entry
      hsources_lt hreg htop hentry hgates hout_ns hout_in
      (one n i ++ one m j) (rowOff j) hon_len hoff_len i.val hagree hoff_src hon_src
  · refine ⟨fun i =>
        extEval D raw top (colOff i) true D.output !=
        extEval D raw top (colOff i) false D.output,
      fun j ent =>
        regEval D raw sources entry
          (fun s => decide (s = n + j.val)) ent (raw + top) !=
        regEval D raw sources entry
          (fun _ => false) ent (raw + top),
      ?_⟩
    intro j hjB i hiR
    have hon_len : (one n i ++ one m j).length = raw := by
      simp [one, raw]
    have hoff_len : (colOff i).length = raw := by
      simp [colOff, one, raw]
    have hagree : ∀ u < raw, u ∉ sources →
        (one n i ++ one m j).getD u false = (colOff i).getD u false := by
      intro u hu huns
      by_cases hun : u < n
      · have h1 : (one n i ++ one m j).getD u false = (one n i).getD u false :=
          getD_append_left _ _ u (by simp [one, hun])
        have h2 : (colOff i).getD u false = (one n i).getD u false :=
          getD_append_left _ _ u (by simp [one, hun])
        rw [h1, h2]
      · have hge : n ≤ u := by omega
        have hltm : u - n < m := by omega
        have h1 : (one n i ++ one m j).getD u false = (one m j).getD (u - n) false := by
          rw [getD_append_right (one n i) (one m j) u (by simp [one, hge])]
          simp [one]
        have h2 : (colOff i).getD u false = (List.replicate m false).getD (u - n) false := by
          rw [getD_append_right (one n i) (List.replicate m false) u (by simp [one, hge])]
          simp [one]
        rw [h1, h2, getD_one m j (u - n) hltm,
          getD_replicate_false]
        have hne : u - n ≠ j.val := by
          intro heq
          apply huns
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hjB, by omega⟩)
        simp [hne]
    have hoff_src : ∀ s ∈ sources, (colOff i).getD s false = false := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', hi'R, rfl⟩
        rw [getD_append_left _ _ i'.val (by simp [one])]
        rw [getD_one n i i'.val i'.isLt]
        have hne : i'.val ≠ i.val := fun heq => hiR (Fin.ext heq ▸ hi'R)
        simp [hne]
      · rcases Finset.mem_image.mp hB with ⟨j', _, rfl⟩
        have h2 : (colOff i).getD (n + j'.val) false = (List.replicate m false).getD j'.val false := by
          rw [getD_append_right
            (one n i) (List.replicate m false) (n + j'.val) (by simp [one])]
          simp [one]
        rw [h2]
        exact getD_replicate_false m j'.val
    have hon_src : ∀ s ∈ sources, (one n i ++ one m j).getD s false = decide (s = n + j.val) := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', hi'R, rfl⟩
        rw [getD_append_left _ _ i'.val (by simp [one])]
        rw [getD_one n i i'.val i'.isLt]
        have hne1 : i'.val ≠ i.val := fun heq => hiR (Fin.ext heq ▸ hi'R)
        have hne2 : i'.val ≠ n + j.val := by omega
        simp [hne1, hne2]
      · rcases Finset.mem_image.mp hB with ⟨j', _, rfl⟩
        have h1 : (one n i ++ one m j).getD (n + j'.val) false = (one m j).getD j'.val false := by
          rw [getD_append_right
            (one n i) (one m j) (n + j'.val) (by simp [one])]
          simp [one]
        rw [h1, getD_one m j j'.val j'.isLt]
        simp
    exact factor_bank D raw top sources region entry
      hsources_lt hreg htop hentry hgates hout_ns hout_in
      (one n i ++ one m j) (colOff i) hon_len hoff_len (n + j.val) hagree hoff_src hon_src

end S25872

namespace S25644

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

abbrev gatesOf (C : Circuit) : Finset ℕ := Finset.range C.size
abbrev readsOf (C : Circuit) (w : ℕ) : ℕ := readsIn C (Finset.range C.size) w
def isBinOp (op : GateOp) : Prop := op = GateOp.and ∨ op = GateOp.or

theorem readsIn_empty (C : Circuit) (w : ℕ) : readsIn C ∅ w = 0 := by
  simp [readsIn]

theorem readsIn_insert (C : Circuit) (G : Finset ℕ) (j w : ℕ) (hj : j ∉ G) :
    readsIn C (insert j G) w = (gateAt C j).inputs.count w + readsIn C G w := by
  unfold readsIn
  exact Finset.sum_insert hj

theorem readsIn_union (C : Circuit) (G1 G2 : Finset ℕ) (w : ℕ) (h : Disjoint G1 G2) :
    readsIn C (G1 ∪ G2) w = readsIn C G1 w + readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_union h

theorem readsIn_mono (C : Circuit) {G1 G2 : Finset ℕ} (h : G1 ⊆ G2) (w : ℕ) :
    readsIn C G1 w ≤ readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset h

theorem readsIn_eq_zero_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    readsIn C G w = 0 ↔ ∀ j ∈ G, w ∉ (gateAt C j).inputs := by
  unfold readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj hw
    have hp : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hz := h j hj
    omega
  · intro h j hj
    exact List.count_eq_zero.mpr (h j hj)

theorem readsIn_pos_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    0 < readsIn C G w ↔ ∃ j ∈ G, w ∈ (gateAt C j).inputs := by
  constructor
  · intro hp
    by_contra h
    have hz : readsIn C G w = 0 := (readsIn_eq_zero_iff C G w).2 (fun j hj hw => h ⟨j, hj, hw⟩)
    omega
  · rintro ⟨j, hj, hw⟩
    have hc : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn
    omega

theorem readsIn_ge_of_mem (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ G) (hw : w ∈ (gateAt C j).inputs) : 1 ≤ readsIn C G w :=
  (readsIn_pos_iff C G w).2 ⟨j, hj, hw⟩

theorem readsIn_eq_one_unique (C : Circuit) (G : Finset ℕ) (w : ℕ) (h : readsIn C G w = 1) :
    ∃ j ∈ G, w ∈ (gateAt C j).inputs ∧ (gateAt C j).inputs.count w = 1 ∧
      ∀ j' ∈ G, w ∈ (gateAt C j').inputs → j' = j := by
  obtain ⟨j, hj, hw⟩ := (readsIn_pos_iff C G w).1 (by omega)
  have hcpos : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
  have hcle : (gateAt C j).inputs.count w ≤ 1 := by
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn at h
    omega
  refine ⟨j, hj, hw, by omega, ?_⟩
  intro j' hj' hw'
  by_contra hne
  have hc' : 0 < (gateAt C j').inputs.count w := List.count_pos_iff.mpr hw'
  have hsub : ({j, j'} : Finset ℕ) ⊆ G := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun i => (gateAt C i).inputs.count w) hsub
  rw [Finset.sum_pair (Ne.symm hne)] at hle
  unfold readsIn at h
  omega

theorem readsIn_disjoint_zero (C : Circuit) {G1 G2 : Finset ℕ} {w : ℕ}
    (h1 : G1 ⊆ gatesOf C) (h2 : G2 ⊆ gatesOf C) (hdisj : Disjoint G1 G2)
    (hr : readsOf C w = 1) (h1r : readsIn C G1 w = 1) : readsIn C G2 w = 0 := by
  have hsub : G1 ∪ G2 ⊆ gatesOf C := Finset.union_subset h1 h2
  have hle := readsIn_mono C hsub w
  rw [readsIn_union C G1 G2 w hdisj] at hle
  change readsIn C (gatesOf C) w = 1 at hr
  omega

theorem readsIn_zero_of_count_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ gatesOf C) (hG : G ⊆ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (hc : (gateAt C j).inputs.count w = 1) : readsIn C G w = 0 := by
  refine readsIn_disjoint_zero C (G1 := {j}) (G2 := G)
    (Finset.singleton_subset_iff.2 hj) hG (Finset.disjoint_singleton_left.2 hn) hr ?_
  simpa [readsIn] using hc

theorem count_zero_of_readsIn_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hG : G ⊆ gatesOf C) (hj : j ∈ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (h1 : readsIn C G w = 1) : (gateAt C j).inputs.count w = 0 := by
  have hz := readsIn_disjoint_zero C (G1 := G) (G2 := {j})
    hG (Finset.singleton_subset_iff.2 hj) (Finset.disjoint_singleton_right.2 hn) hr h1
  simpa [readsIn] using hz

theorem readsIn_ge_bound_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    {G : Finset ℕ} (hG : G ⊆ gatesOf C) {r : ℕ} (hbound : ∀ j ∈ G, n + j ≤ r) :
    readsIn C G r = 0 := by
  rw [readsIn_eq_zero_iff]
  intro j hj hr
  have hjlt : j < C.gates.length := Finset.mem_range.1 (hG hj)
  have hlt := hback j hjlt r hr
  have hle := hbound j hj
  omega

theorem reads_output_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) : readsOf C C.output = 0 := by
  refine readsIn_ge_bound_zero n C hback (Finset.Subset.refl _) ?_
  intro j hj
  have hjlt : j < C.size := Finset.mem_range.1 hj
  omega

theorem ne_output_of_reads_pos (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {w : ℕ} (hw : 0 < readsOf C w) : C.output ≠ w := by
  rintro rfl
  have hz := reads_output_zero n C hback hout
  omega

theorem gateAt_mem_gates (C : Circuit) {j : ℕ} (hj : j < C.size) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  have hlen : j < C.gates.length := hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

theorem list_len2_eq (l : List ℕ) (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at h ⊢

theorem list_len1_eq (l : List ℕ) (h : l.length = 1) :
    l = [l.getD 0 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h ⊢

theorem count_pair_eq_one_left {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count a = 1 := by
  simp [h]

theorem count_pair_eq_one_right {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count b = 1 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

theorem count_pair_eq_two {a : ℕ} : ([a, a] : List ℕ).count a = 2 := by
  simp

theorem count_pair_eq_zero {a b x : ℕ} (ha : x ≠ a) (hb : x ≠ b) :
    ([a, b] : List ℕ).count x = 0 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

inductive BTree
  | priv (w : ℕ) : BTree
  | mark (w : ℕ) : BTree
  | node (j : ℕ) (l r : BTree) : BTree

def BTree.root (n : ℕ) : BTree → ℕ
  | BTree.priv w => w
  | BTree.mark w => w
  | BTree.node j _ _ => n + j

def BTree.marks : BTree → ℕ
  | BTree.priv _ => 0
  | BTree.mark _ => 1
  | BTree.node _ l r => l.marks + r.marks

def BTree.privs : BTree → Finset ℕ
  | BTree.priv w => {w}
  | BTree.mark _ => ∅
  | BTree.node _ l r => l.privs ∪ r.privs

def BTree.gates : BTree → Finset ℕ
  | BTree.priv _ => ∅
  | BTree.mark _ => ∅
  | BTree.node j l r => insert j (l.gates ∪ r.gates)

def BTree.wires (n : ℕ) (t : BTree) : Finset ℕ :=
  t.privs ∪ t.gates.image (fun k => n + k)

def BTree.nonMark : BTree → Prop
  | BTree.mark _ => False
  | _ => True

def GoodTree (n : ℕ) (C : Circuit) : BTree → Prop
  | BTree.priv w => w < n ∧ readsOf C w = 1
  | BTree.mark _ => True
  | BTree.node j l r =>
      j < C.size ∧ isBinOp (gateAt C j).op ∧
      (gateAt C j).inputs = [l.root n, r.root n] ∧
      GoodTree n C l ∧ GoodTree n C r ∧
      (l.nonMark → readsOf C (l.root n) = 1) ∧
      (r.nonMark → readsOf C (r.root n) = 1)

theorem BTree.wires_node (n j : ℕ) (l r : BTree) :
    (BTree.node j l r).wires n = insert (n + j) (l.wires n ∪ r.wires n) := by
  ext w
  simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_insert, Finset.image_union,
    Finset.mem_union, Finset.mem_insert]
  tauto

theorem BTree.root_mem_wires (n : ℕ) {t : BTree} (ht : t.nonMark) : t.root n ∈ t.wires n := by
  cases t with
  | priv w => simp [BTree.wires, BTree.privs, BTree.root]
  | mark w => exact False.elim ht
  | node j l r =>
    rw [BTree.wires_node, BTree.root]
    exact Finset.mem_insert_self _ _

theorem BTree.nonMark_of_marks_zero {t : BTree} (h : t.marks = 0) : t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.marks] at h
  | node _ _ _ => trivial

theorem BTree.nonMark_of_wires_nonempty (n : ℕ) {t : BTree} {w : ℕ} (hw : w ∈ t.wires n) :
    t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.wires, BTree.privs, BTree.gates] at hw
  | node _ _ _ => trivial

theorem good_gates_sub {n : ℕ} {C : Circuit} {t : BTree} (ht : GoodTree n C t) :
    t.gates ⊆ gatesOf C := by
  induction t with
  | priv _ => simp [BTree.gates]
  | mark _ => simp [BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, _, hgl, hgr, _, _⟩
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · exact Finset.mem_range.2 hj
    · exact ihl hgl hkl
    · exact ihr hgr hkr

theorem good_wires_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ w ∈ t.wires n, w ≤ t.root n := by
  induction t with
  | priv w =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu ⊢
    omega
  | mark _ =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
    have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
    have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
    intro w hw
    rw [BTree.wires_node] at hw
    rw [BTree.root]
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihl hgl w hwl) hl_lt)
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihr hgr w hwr) hr_lt)

theorem good_gates_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ k ∈ t.gates, n + k ≤ t.root n := by
  intro k hk
  refine good_wires_le hback ht (n + k) ?_
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk, rfl⟩)

theorem good_readsIn_top_zero {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : readsIn C t.gates (t.root n) = 0 :=
  readsIn_ge_bound_zero n C hback (good_gates_sub ht) (good_gates_le hback ht)

theorem good_node_not_mem_sub {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {j : ℕ} {l r : BTree}
    (ht : GoodTree n C (BTree.node j l r)) : j ∉ l.gates ∧ j ∉ r.gates := by
  rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
  have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
  have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
  constructor
  · intro hjl
    have := good_gates_le hback hgl j hjl
    omega
  · intro hjr
    have := good_gates_le hback hgr j hjr
    omega

theorem good_internal_reads {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree} (ht : GoodTree n C t) :
    (∀ w ∈ t.wires n, w ≠ t.root n → readsIn C t.gates w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) ∧
    (∀ j l r, t = BTree.node j l r → Disjoint (l.wires n) (r.wires n)) := by
  induction t with
  | priv w =>
    refine ⟨fun u hu hne => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu hne
    exact absurd hu hne
  | mark _ =>
    refine ⟨fun u hu => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    obtain ⟨ihl_int, _⟩ := ihl hgl
    obtain ⟨ihr_int, _⟩ := ihr hgr
    have hnot : j ∉ l.gates ∧ j ∉ r.gates :=
      good_node_not_mem_sub hback ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
    have hl_sub : l.gates ⊆ gatesOf C := good_gates_sub hgl
    have hr_sub : r.gates ⊆ gatesOf C := good_gates_sub hgr
    have hdisj_wires : Disjoint (l.wires n) (r.wires n) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hne
      have hnon : (l.wires n ∩ r.wires n).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
      let w := (l.wires n ∩ r.wires n).max' hnon
      have hw_mem : w ∈ l.wires n ∩ r.wires n := Finset.max'_mem _ hnon
      have hwl : w ∈ l.wires n := (Finset.mem_inter.1 hw_mem).1
      have hwr : w ∈ r.wires n := (Finset.mem_inter.1 hw_mem).2
      have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      by_cases h1 : w = l.root n
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hcnt : (gateAt C j).inputs.count w = 2 := by
            rw [hinp, ← h1, ← h2]
            exact count_pair_eq_two
          have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hjG
          change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count w = 1 at hrw
          omega
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hrr : readsIn C r.gates w = 1 := (ihr_int w hwr h2).1
          have hdisj_j : Disjoint r.gates {j} := by simp [hnot.2]
          have hsub_rj : r.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hr_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_rj w
          rw [readsIn_union C r.gates {j} w hdisj_j] at hle
          have hjr : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h1]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h2 ▸ hr1 hrnm
          have hrl : readsIn C l.gates w = 1 := (ihl_int w hwl h1).1
          have hdisj_j : Disjoint l.gates {j} := by simp [hnot.1]
          have hsub_lj : l.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hl_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_lj w
          rw [readsIn_union C l.gates {j} w hdisj_j] at hle
          have hjl : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h2]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
        · have hrl := ihl_int w hwl h1
          have hrr := ihr_int w hwr h2
          obtain ⟨p, hpG, hpw, _, hpuniq⟩ := readsIn_eq_one_unique C (gatesOf C) w hrl.2.1
          obtain ⟨pl, hpl, hplw⟩ := (readsIn_pos_iff C l.gates w).1 (by omega)
          obtain ⟨pr, hpr, hprw⟩ := (readsIn_pos_iff C r.gates w).1 (by omega)
          have hpl_eq : pl = p := hpuniq pl (hl_sub hpl) hplw
          have hpr_eq : pr = p := hpuniq pr (hr_sub hpr) hprw
          subst hpl_eq
          have hpr' : pl ∈ r.gates := by rwa [← hpr_eq]
          have hmem_inter : n + pl ∈ l.wires n ∩ r.wires n := Finset.mem_inter.2
            ⟨Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpl, rfl⟩),
             Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpr', rfl⟩)⟩
          have hle_max : n + pl ≤ w := Finset.le_max' _ _ hmem_inter
          have hlt := hback pl (Finset.mem_range.1 (hl_sub hpl)) w hplw
          omega
    have hdisj_gates : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_wires
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hj_not_u : j ∉ l.gates ∪ r.gates := by
      simp [hnot.1, hnot.2]
    refine ⟨?_, fun j' l' r' heq => by cases heq; exact hdisj_wires⟩
    intro w hw hne
    rw [BTree.wires_node] at hw
    rw [BTree.root] at hne
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact absurd rfl hne
    · have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1l : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 2 := by
          rw [hinp, ← heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (l.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (l.root n) = 1 at hr1l
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = l.root n
      · subst hwr_eq
        have hrw : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_left hlr_ne
        have hrl0 : readsIn C l.gates (l.root n) = 0 := good_readsIn_top_zero hback hgl
        have hrr0 : readsIn C r.gates (l.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hr_sub hnot.2 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihl_int w hwl hwr_eq
        have hrr0 : readsIn C r.gates w = 0 :=
          readsIn_disjoint_zero C hl_sub hr_sub hdisj_gates hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hl_sub hjG hnot.1 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩
    · have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1r : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 2 := by
          rw [hinp, heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (r.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (r.root n) = 1 at hr1r
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = r.root n
      · subst hwr_eq
        have hrw : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_right hlr_ne
        have hrr0 : readsIn C r.gates (r.root n) = 0 := good_readsIn_top_zero hback hgr
        have hrl0 : readsIn C l.gates (r.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hl_sub hnot.1 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihr_int w hwr hwr_eq
        have hrl0 : readsIn C l.gates w = 0 :=
          readsIn_disjoint_zero C hr_sub hl_sub hdisj_gates.symm hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hr_sub hjG hnot.2 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩

theorem good_markFree_inputs {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) :
    ∀ j ∈ t.gates, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ t.wires n := by
  induction t with
  | priv _ =>
    intro j hj
    simp [BTree.gates] at hj
  | mark _ =>
    simp [BTree.marks] at hm
  | node j l r ihl ihr =>
    rcases ht with ⟨_, hop, hinp, hgl, hgr, _, _⟩
    simp only [BTree.marks] at hm
    have hml : l.marks = 0 := by omega
    have hmr : r.marks = 0 := by omega
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · refine ⟨hop, by rw [hinp]; rfl, fun w hw => ?_⟩
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rw [BTree.wires_node]
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hml)))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmr)))
    · obtain ⟨ho, hl2, hwin⟩ := ihl hgl hml k hkl
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · obtain ⟨ho, hl2, hwin⟩ := ihr hgr hmr k hkr
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hwin w hw))

def IsTree (n : ℕ) (C : Circuit) (S E : Finset ℕ) : Prop :=
  ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := readsIn C region
    region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

theorem good_markFree_isTree {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) : IsTree n C t.privs ∅ := by
  refine ⟨t.gates, t.root n, good_gates_sub ht,
    BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hm),
    good_readsIn_top_zero hback ht, fun _ hb => absurd hb (Finset.notMem_empty _), ?_,
    (good_internal_reads hback hout ht).1⟩
  intro j hj
  obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs ht hm j hj
  exact ⟨ho, hl, fun w hw => Or.inl (hwin w hw)⟩

def IsTopStretch (n : ℕ) (C : Circuit) (t : BTree) (reg priv : Finset ℕ) (b : ℕ) : Prop :=
  reg ⊆ t.gates ∧ priv ⊆ t.privs ∧ b ≤ t.root n ∧
  ((reg = ∅ ∧ priv = ∅ ∧ b = t.root n) ∨
   (let wires := priv ∪ reg.image (fun k => n + k)
    t.root n ∈ wires ∧ b ∉ wires ∧ b < t.root n ∧ readsIn C reg b = 1 ∧
    (∀ j ∈ reg, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ t.root n → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w)))

theorem isTree_of_topStretch {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) {reg priv : Finset ℕ} {b : ℕ}
    (hs : IsTopStretch n C t reg priv b) (hnp : priv.Nonempty) : IsTree n C priv {b} := by
  rcases hs with ⟨hreg, _, _, ⟨_, hpe, _⟩ | ⟨hrm, hbn, hblt, hbr, hgj, hwint⟩⟩
  · rw [hpe] at hnp
    exact absurd hnp Finset.not_nonempty_empty
  · refine ⟨reg, t.root n, hreg.trans (good_gates_sub ht), hrm,
      readsIn_ge_bound_zero n C hback (hreg.trans (good_gates_sub ht))
        (fun k hk => good_gates_le hback ht k (hreg hk)),
      fun b' hb' => by
        rw [Finset.mem_singleton.1 hb']
        exact ⟨hbn, hblt, hbr⟩,
      fun j hj => by
        obtain ⟨ho, hl, hwin⟩ := hgj j hj
        exact ⟨ho, hl, fun w hw => (hwin w hw).imp id (fun h => Finset.mem_singleton.2 h)⟩,
      hwint⟩

theorem extend_stretch_aux {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {j : ℕ} {mf mk : BTree}
    (hj : j < C.size) (hop : isBinOp (gateAt C j).op)
    (hinp : (gateAt C j).inputs = [mf.root n, mk.root n] ∨
      (gateAt C j).inputs = [mk.root n, mf.root n])
    (hgf : GoodTree n C mf) (hgk : GoodTree n C mk)
    (hmf : mf.marks = 0)
    (hrf1 : readsOf C (mf.root n) = 1)
    (hrk1 : mk.nonMark → readsOf C (mk.root n) = 1)
    (hdisj_w : Disjoint (mf.wires n) (mk.wires n))
    (hdisj_g : Disjoint mf.gates mk.gates)
    (hj_mf : j ∉ mf.gates) (hj_mk : j ∉ mk.gates)
    {reg_k priv_k : Finset ℕ} {b : ℕ}
    (hsk : IsTopStretch n C mk reg_k priv_k b) :
    let reg := insert j (mf.gates ∪ reg_k)
    let priv := mf.privs ∪ priv_k
    let wires := priv ∪ reg.image (fun k => n + k)
    (n + j) ∈ wires ∧ b ∉ wires ∧ b < n + j ∧ readsIn C reg b = 1 ∧
    (∀ k ∈ reg, isBinOp (gateAt C k).op ∧ (gateAt C k).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ n + j → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) := by
  intro reg priv wires
  have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
  have hmf_sub : mf.gates ⊆ gatesOf C := good_gates_sub hgf
  have hmk_sub : mk.gates ⊆ gatesOf C := good_gates_sub hgk
  have hmf_int := (good_internal_reads hback hout hgf).1
  have hmf_lt : mf.root n < n + j := hback j hj (mf.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmk_lt : mk.root n < n + j := hback j hj (mk.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmf_ne_mk : mf.root n ≠ mk.root n := by
    intro heq
    have hcnt : (gateAt C j).inputs.count (mf.root n) = 2 := by
      rcases hinp with h | h <;> rw [h, heq] <;> exact count_pair_eq_two
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (mf.root n))) hjG
    change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (mf.root n) = 1 at hrf1
    omega
  have hcnt_mf : (gateAt C j).inputs.count (mf.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_left hmf_ne_mk
    · exact count_pair_eq_one_right hmf_ne_mk.symm
  have hcnt_mk : (gateAt C j).inputs.count (mk.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_right hmf_ne_mk
    · exact count_pair_eq_one_left hmf_ne_mk.symm
  rcases hsk with ⟨hreg_k, hpriv_k, hb_le, hcase⟩
  have hdisj_rk : Disjoint mf.gates reg_k := Disjoint.mono_right hreg_k hdisj_g
  have hj_not_u : j ∉ mf.gates ∪ reg_k := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hj_mf, fun h => hj_mk (hreg_k h)⟩
  have hwires_eq : wires = insert (n + j) (mf.wires n ∪ (priv_k ∪ reg_k.image (fun k => n + k))) := by
    ext w
    simp only [wires, priv, reg, BTree.wires, Finset.image_insert, Finset.image_union,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h1 | h2) | (h3 | h4 | h5))
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inl h3
      · exact Or.inr (Or.inl (Or.inr h4))
      · exact Or.inr (Or.inr (Or.inr h5))
    · rintro (h1 | (h2 | h3) | (h4 | h5))
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inr (Or.inr h5))
  have hwk_sub : priv_k ∪ reg_k.image (fun k => n + k) ⊆ mk.wires n := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_image] at hw
    rcases hw with hp | ⟨k, hk, rfl⟩
    · exact Finset.mem_union_left _ (hpriv_k hp)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hreg_k hk, rfl⟩)
  have hmf_reads_sub : ∀ w ∈ mf.wires n, readsIn C reg_k w = 0 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · subst hwr
      exact readsIn_zero_of_count_one C hjG (hreg_k.trans hmk_sub) (fun h => hj_mk (hreg_k h)) hrf1 hcnt_mf
    · have hi := hmf_int w hw hwr
      exact readsIn_disjoint_zero C hmf_sub (hreg_k.trans hmk_sub) hdisj_rk hi.2.1 hi.1
  have hmf_all_reads1 : ∀ w ∈ mf.wires n, readsOf C w = 1 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · exact hwr ▸ hrf1
    · exact (hmf_int w hw hwr).2.1
  have hb_not_mf : b ∉ mf.wires n := by
    intro hbm
    have hrb1 : readsOf C b = 1 := hmf_all_reads1 b hbm
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, _, hbr1, _, _⟩
    · subst hbeq
      have hne_root : mk.root n ≠ mf.root n := hmf_ne_mk.symm
      have hi := hmf_int (mk.root n) hbm hne_root
      have h0 := count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
      omega
    · have h0 := hmf_reads_sub b hbm
      omega
  have hmf_reads_b : readsIn C mf.gates b = 0 := by
    rw [readsIn_eq_zero_iff]
    intro k hk hbk
    have hwin := (good_markFree_inputs hgf hmf k hk).2.2 b hbk
    exact hb_not_mf hwin
  have hroot_mem : n + j ∈ wires := by
    rw [hwires_eq]
    exact Finset.mem_insert_self _ _
  have hb_lt : b < n + j := Nat.lt_of_le_of_lt hb_le hmk_lt
  have hb_not_w : b ∉ wires := by
    rw [hwires_eq]
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨by omega, hb_not_mf, ?_⟩
    rcases hcase with ⟨hre, hpe, _⟩ | ⟨_, hbn, _, _, _, _⟩
    · simp [hre, hpe]
    · simpa [Finset.mem_union, not_or] using hbn
  have hb_reads : readsIn C reg b = 1 := by
    rw [readsIn_insert C _ j b hj_not_u, readsIn_union C mf.gates reg_k b hdisj_rk, hmf_reads_b]
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, hblt_k, hbr1, _, _⟩
    · subst hbeq
      rw [hre, readsIn_empty, hcnt_mk]
    · have hcj0 : (gateAt C j).inputs.count b = 0 := by
        have hbn1 : b ≠ mf.root n := fun heq =>
          hb_not_mf (heq ▸ BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf))
        have hbn2 : b ≠ mk.root n := by omega
        rcases hinp with h | h <;> rw [h]
        · exact count_pair_eq_zero hbn1 hbn2
        · exact count_pair_eq_zero hbn2 hbn1
      rw [hcj0, hbr1]
  refine ⟨hroot_mem, hb_not_w, hb_lt, hb_reads, ?_, ?_⟩
  · intro k hk
    simp only [reg, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkm | hkk
    · refine ⟨hop, by rcases hinp with h | h <;> rw [h] <;> rfl, fun w hw => ?_⟩
      have hwf : w = mf.root n ∨ w = mk.root n := by
        rcases hinp with h | h <;> rw [h] at hw <;> simp at hw <;> tauto
      rcases hwf with rfl | rfl
      · left
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf)))
      · rcases hcase with ⟨_, _, hbeq⟩ | ⟨hrm, _, _, _, _, _⟩
        · exact Or.inr hbeq.symm
        · left
          rw [hwires_eq]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hrm)
    · obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs hgf hmf k hkm
      refine ⟨ho, hl, fun w hw => Or.inl ?_⟩
      rw [hwires_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · rcases hcase with ⟨hre, _, _⟩ | ⟨_, _, _, _, hgj, _⟩
      · rw [hre] at hkk
        exact absurd hkk (Finset.notMem_empty _)
      · obtain ⟨ho, hl, hwin⟩ := hgj k hkk
        refine ⟨ho, hl, fun w hw => (hwin w hw).imp (fun h => ?_) id⟩
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
  · intro w hw hne
    rw [hwires_eq] at hw
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwm | hwk
    · exact absurd rfl hne
    · rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk,
        hmf_reads_sub w hwm]
      by_cases hwr : w = mf.root n
      · subst hwr
        rw [hcnt_mf, good_readsIn_top_zero hback hgf]
        exact ⟨by omega, hrf1, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := hmf_int w hwm hwr
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
        rw [hcj0, hi.1]
        exact ⟨by omega, hi.2.1, hi.2.2⟩
    · rcases hcase with ⟨hre, hpe, _⟩ | ⟨hrm, _, _, _, _, hwint⟩
      · simp [hre, hpe] at hwk
      · have hw_in_mk : w ∈ mk.wires n := hwk_sub (Finset.mem_union.2 hwk)
        have hmknm : mk.nonMark := BTree.nonMark_of_wires_nonempty n hw_in_mk
        rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk]
        by_cases hwr : w = mk.root n
        · subst hwr
          have hrk := hrk1 hmknm
          have hrl0 : readsIn C mf.gates (mk.root n) = 0 :=
            readsIn_zero_of_count_one C hjG hmf_sub hj_mf hrk hcnt_mk
          have hrr0 : readsIn C reg_k (mk.root n) = 0 :=
            readsIn_ge_bound_zero n C hback (hreg_k.trans hmk_sub)
              (fun k hk => good_gates_le hback hgk k (hreg_k hk))
          rw [hcnt_mk, hrl0, hrr0]
          exact ⟨by omega, hrk, ne_output_of_reads_pos n C hback hout (by omega)⟩
        · have hi := hwint w (Finset.mem_union.2 hwk) hwr
          have hrl0 : readsIn C mf.gates w = 0 :=
            readsIn_disjoint_zero C (hreg_k.trans hmk_sub) hmf_sub hdisj_rk.symm hi.2.1 hi.1
          have hcj0 : (gateAt C j).inputs.count w = 0 :=
            count_zero_of_readsIn_one C (hreg_k.trans hmk_sub) hjG (fun h => hj_mk (hreg_k h)) hi.2.1 hi.1
          rw [hcj0, hrl0, hi.1]
          exact ⟨by omega, hi.2.1, hi.2.2⟩

theorem decomp_marked {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ (reg_top priv_top : Finset ℕ) (b_top : ℕ) (rest : List (Finset ℕ)),
      IsTopStretch n C t reg_top priv_top b_top ∧
      rest.length + 2 ≤ 2 * t.marks ∧
      (∀ S ∈ rest, S.Nonempty ∧ S ⊆ t.privs ∧ Disjoint S priv_top ∧ ∃ b, IsTree n C S {b}) ∧
      rest.Pairwise Disjoint ∧
      priv_top ∪ rest.toFinset.biUnion (fun S => S) = t.privs := by
  induction t with
  | priv _ =>
    simp [BTree.marks] at hm
  | mark w =>
    refine ⟨∅, ∅, w, [], ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _,
      Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [BTree.marks], fun _ h => by simp at h, List.Pairwise.nil,
      by simp [BTree.privs]⟩
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hgt_node : GoodTree n C (BTree.node j l r) := ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hdisj_w : Disjoint (l.wires n) (r.wires n) :=
      (good_internal_reads hback hout hgt_node).2 j l r rfl
    have hdisj_g : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_w
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hdisj_p : Disjoint l.privs r.privs :=
      Disjoint.mono (Finset.subset_union_left) (Finset.subset_union_left) hdisj_w
    have hnot := good_node_not_mem_sub hback hgt_node
    simp only [BTree.marks] at hm
    by_cases hml : l.marks = 0
    · have hmr : 1 ≤ r.marks := by omega
      obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr
      have hrf1 : readsOf C (l.root n) = 1 := hl1 (BTree.nonMark_of_marks_zero hml)
      have hext := extend_stretch_aux hback hout hj hop (Or.inl hinp) hgl hgr hml hrf1 hr1
        hdisj_w hdisj_g hnot.1 hnot.2 hsr
      refine ⟨insert j (l.gates ∪ reg_r), l.privs ∪ priv_r, b_r, rest_r, ?_, ?_, ?_, hpw_r, ?_⟩
      · refine ⟨Finset.insert_subset_insert j (Finset.union_subset_union_right hsr.1),
          Finset.union_subset_union_right hsr.2.1, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
      · simp only [BTree.marks]
        omega
      · intro S hS
        obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_r S hS
        refine ⟨hnp, hsub.trans Finset.subset_union_right, ?_, htr⟩
        rw [Finset.disjoint_union_right]
        exact ⟨Disjoint.mono_left hsub hdisj_p.symm, hdp⟩
      · simp only [BTree.privs]
        rw [Finset.union_assoc, hcov_r]
    · by_cases hmr : r.marks = 0
      · have hml1 : 1 ≤ l.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        have hrf1 : readsOf C (r.root n) = 1 := hr1 (BTree.nonMark_of_marks_zero hmr)
        have hext := extend_stretch_aux hback hout hj hop (Or.inr hinp) hgr hgl hmr hrf1 hl1
          hdisj_w.symm hdisj_g.symm hnot.2 hnot.1 hsl
        refine ⟨insert j (r.gates ∪ reg_l), r.privs ∪ priv_l, b_l, rest_l, ?_, ?_, ?_, hpw_l, ?_⟩
        · refine ⟨?_, ?_, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
          · intro k hk
            simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk ⊢
            rcases hk with rfl | h1 | h2
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h1)
            · exact Or.inr (Or.inl (hsl.1 h2))
          · intro w hw
            simp only [BTree.privs, Finset.mem_union] at hw ⊢
            rcases hw with h1 | h2
            · exact Or.inr h1
            · exact Or.inl (hsl.2.1 h2)
        · simp only [BTree.marks]
          omega
        · intro S hS
          obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_l S hS
          refine ⟨hnp, hsub.trans Finset.subset_union_left, ?_, htr⟩
          rw [Finset.disjoint_union_right]
          exact ⟨Disjoint.mono_left hsub hdisj_p, hdp⟩
        · simp only [BTree.privs]
          rw [Finset.union_assoc, hcov_l, Finset.union_comm]
      · have hml1 : 1 ≤ l.marks := by omega
        have hmr1 : 1 ≤ r.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr1
        let Ll : List (Finset ℕ) := if priv_l.Nonempty then priv_l :: rest_l else rest_l
        let Lr : List (Finset ℕ) := if priv_r.Nonempty then priv_r :: rest_r else rest_r
        have hLl_len : Ll.length ≤ rest_l.length + 1 := by
          dsimp only [Ll]
          split_ifs <;> simp
        have hLr_len : Lr.length ≤ rest_r.length + 1 := by
          dsimp only [Lr]
          split_ifs <;> simp
        have hLl_prop : ∀ S ∈ Ll, S.Nonempty ∧ S ⊆ l.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Ll] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsl.2.1, b_l, isTree_of_topStretch hback hgl hsl hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_l S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_l S hS
            exact ⟨a, b, c⟩
        have hLr_prop : ∀ S ∈ Lr, S.Nonempty ∧ S ⊆ r.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Lr] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsr.2.1, b_r, isTree_of_topStretch hback hgr hsr hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_r S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_r S hS
            exact ⟨a, b, c⟩
        have hLl_pw : Ll.Pairwise Disjoint := by
          dsimp only [Ll]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_l S hS).2.2.1.symm, hpw_l⟩
          · exact hpw_l
        have hLr_pw : Lr.Pairwise Disjoint := by
          dsimp only [Lr]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_r S hS).2.2.1.symm, hpw_r⟩
          · exact hpw_r
        have hLl_cov : Ll.toFinset.biUnion (fun S => S) = l.privs := by
          dsimp only [Ll]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_l]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_l
            exact hcov_l
        have hLr_cov : Lr.toFinset.biUnion (fun S => S) = r.privs := by
          dsimp only [Lr]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_r]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_r
            exact hcov_r
        refine ⟨∅, ∅, n + j, Ll ++ Lr,
          ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, BTree.marks]
          omega
        · intro S hS
          rcases List.mem_append.1 hS with h1 | h2
          · obtain ⟨a, b, c⟩ := hLl_prop S h1
            exact ⟨a, b.trans Finset.subset_union_left, Finset.disjoint_empty_right S, c⟩
          · obtain ⟨a, b, c⟩ := hLr_prop S h2
            exact ⟨a, b.trans Finset.subset_union_right, Finset.disjoint_empty_right S, c⟩
        · rw [List.pairwise_append]
          refine ⟨hLl_pw, hLr_pw, fun S1 h1 S2 h2 => ?_⟩
          exact Disjoint.mono (hLl_prop S1 h1).2.1 (hLr_prop S2 h2).2.1 hdisj_p
        · rw [Finset.empty_union, List.toFinset_append, Finset.union_biUnion, hLl_cov, hLr_cov]
          rfl

theorem marked_tree_chains {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ L : List (Finset ℕ),
      L.length + 1 ≤ 2 * t.marks ∧
      (∀ S ∈ L, S.Nonempty ∧ S ⊆ t.privs ∧ ∃ b, IsTree n C S {b}) ∧
      L.Pairwise Disjoint ∧
      L.toFinset.biUnion (fun S => S) = t.privs := by
  obtain ⟨reg, priv, b, rest, hs, hlen, hrest, hpw, hcov⟩ := decomp_marked hback hout ht hm
  by_cases hnp : priv.Nonempty
  · refine ⟨priv :: rest, by simp; omega, ?_, ?_, ?_⟩
    · intro S hS
      rcases List.mem_cons.1 hS with rfl | hSr
      · exact ⟨hnp, hs.2.1, b, isTree_of_topStretch hback ht hs hnp⟩
      · obtain ⟨a, b', _, c⟩ := hrest S hSr
        exact ⟨a, b', c⟩
    · exact List.pairwise_cons.2 ⟨fun S hS => (hrest S hS).2.2.1.symm, hpw⟩
    · rw [List.toFinset_cons, Finset.biUnion_insert, hcov]
  · refine ⟨rest, by omega, fun S hS => ?_, hpw, ?_⟩
    · obtain ⟨a, b', _, c⟩ := hrest S hS
      exact ⟨a, b', c⟩
    · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov
      exact hcov

def isInternalChild (n : ℕ) (C : Circuit) (u : ℕ) : Prop :=
  readsOf C u = 1 ∧ ¬ (n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not)

open Classical in
noncomputable def buildTree (n : ℕ) (C : Circuit) (r : ℕ) : BTree :=
  if h : n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not then
    let j := r - n
    let u0 := (gateAt C j).inputs.getD 0 0
    let u1 := (gateAt C j).inputs.getD 1 0
    let child : ℕ → BTree := fun u =>
      if hu : u < r ∧ isInternalChild n C u then
        if u < n then BTree.priv u else buildTree n C u
      else BTree.mark u
    BTree.node j (child u0) (child u1)
  else if r < n ∧ readsOf C r = 1 then
    BTree.priv r
  else
    BTree.mark r
termination_by r

theorem buildTree_root (n : ℕ) (C : Circuit) (r : ℕ) : (buildTree n C r).root n = r := by
  rw [buildTree]
  split_ifs with h1 h2
  · simp [BTree.root]
    omega
  · rfl
  · rfl

theorem buildTree_good (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C) : ∀ r : ℕ, GoodTree n C (buildTree n C r) := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    rw [buildTree]
    split_ifs with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨ho, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      classical
      have hchild_prop : ∀ u : ℕ, u < r →
          let ch := if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u
          ch.root n = u ∧ GoodTree n C ch ∧ (ch.nonMark → readsOf C u = 1) := by
        intro u hult
        dsimp only
        split_ifs with hu hun
        · refine ⟨rfl, ⟨hun, hu.2.1⟩, fun _ => hu.2.1⟩
        · refine ⟨buildTree_root n C u, ih u hult, fun _ => hu.2.1⟩
        · refine ⟨rfl, trivial, fun h => False.elim h⟩
      have hc0 := hchild_prop _ hu0_lt
      have hc1 := hchild_prop _ hu1_lt
      refine ⟨hj, hbin.1, ?_, hc0.2.1, hc1.2.1, ?_, ?_⟩
      · rw [hc0.1, hc1.1]
        exact hinp
      · rw [hc0.1]
        exact hc0.2.2
      · rw [hc1.1]
        exact hc1.2.2
    · exact h2
    · trivial

open Classical in
noncomputable def parentGate (C : Circuit) (w : ℕ) : ℕ :=
  if h : ∃ j ∈ gatesOf C, w ∈ (gateAt C j).inputs then Classical.choose h else 0

theorem parentGate_spec (C : Circuit) {w : ℕ} (h : readsOf C w = 1) :
    parentGate C w ∈ gatesOf C ∧ w ∈ (gateAt C (parentGate C w)).inputs ∧
    ∀ j ∈ gatesOf C, w ∈ (gateAt C j).inputs → j = parentGate C w := by
  obtain ⟨j, hj, hw, _, huniq⟩ := readsIn_eq_one_unique C (gatesOf C) w h
  have hex : ∃ j' ∈ gatesOf C, w ∈ (gateAt C j').inputs := ⟨j, hj, hw⟩
  have hdef : parentGate C w = Classical.choose hex := by
    unfold parentGate
    exact dif_pos hex
  rw [hdef]
  have hch := Classical.choose_spec hex
  have heq : Classical.choose hex = j := huniq _ hch.1 hch.2
  rw [heq]
  exact ⟨hj, hw, huniq⟩

open Classical in
noncomputable def owner (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  if h : w < n + C.size ∧ readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not ∧
      w < n + parentGate C w then
    owner n C (n + parentGate C w)
  else w
termination_by n + C.size - w

open Classical in
theorem owner_step (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {w : ℕ}
    (hw1 : readsOf C w = 1) (hnot : (gateAt C (parentGate C w)).op ≠ GateOp.not) :
    owner n C w = owner n C (n + parentGate C w) := by
  obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hw1
  have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
  have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
  have hcond : w < n + C.size ∧ readsOf C w = 1 ∧
      (gateAt C (parentGate C w)).op ≠ GateOp.not ∧ w < n + parentGate C w :=
    ⟨by omega, hw1, hnot, hwlt⟩
  rw [owner]
  exact dif_pos hcond

theorem owner_fixed (n : ℕ) (C : Circuit) {w : ℕ}
    (h : ¬ (readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not)) :
    owner n C w = w := by
  rw [owner]
  split_ifs with h1
  · exact absurd ⟨h1.2.1, h1.2.2.1⟩ h
  · rfl

theorem owner_of_good_child (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {j u : ℕ}
    (hj : j < C.size) (hop : (gateAt C j).op ≠ GateOp.not)
    (hu : u ∈ (gateAt C j).inputs) (hr1 : readsOf C u = 1) :
    owner n C u = owner n C (n + j) := by
  obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
  have hpeq : j = parentGate C u := huniq j (Finset.mem_range.2 hj) hu
  rw [owner_step n C hback hr1 (by rwa [← hpeq]), ← hpeq]

open Classical in
theorem owner_eq_of_mem_wires (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ), ∀ w ∈ (buildTree n C r).wires n, owner n C w = owner n C r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro w hw
    rw [buildTree] at hw
    split_ifs at hw with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨ho, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      have hchild : ∀ (u : ℕ), u ∈ (gateAt C (r - n)).inputs →
          w ∈ (if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u : BTree).wires n → owner n C w = owner n C r := by
        intro u hu hwu
        split_ifs at hwu with huc hun
        · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
            Finset.union_empty, Finset.mem_singleton] at hwu
          subst hwu
          rw [owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · rw [ih u huc.1 w hwu, owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · simp [BTree.wires, BTree.privs, BTree.gates] at hwu
      rw [BTree.wires_node] at hw
      simp only [Finset.mem_insert, Finset.mem_union] at hw
      rcases hw with rfl | hwl | hwr
      · rw [hnj]
      · exact hchild _ (by rw [hinp]; simp) hwl
      · exact hchild _ (by rw [hinp]; simp) hwr
    · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
        Finset.mem_singleton] at hw
      rw [hw]
    · simp [BTree.wires, BTree.privs, BTree.gates] at hw

open Classical in
theorem mem_wires_buildTree_owner (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (w : ℕ),
      ((w < n ∧ readsOf C w = 1) ∨
        (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not)) →
      w ∈ (buildTree n C (owner n C w)).wires n := by
  intro w
  induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
  | ind d ih =>
    intro hw
    by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
    · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
      have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
      have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
      have hown : owner n C w = owner n C (n + parentGate C w) :=
        owner_step n C hback hstep.1 hstep.2
      have hnp_in : n + parentGate C w ∈ (buildTree n C (owner n C (n + parentGate C w))).wires n :=
        ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      rw [hown]
      have hrec : ∀ (r : ℕ), n + parentGate C w ∈ (buildTree n C r).wires n →
          w ∈ (buildTree n C r).wires n := by
        intro r
        induction r using Nat.strong_induction_on with
        | ind r ihr =>
          intro hrw
          rw [buildTree] at hrw ⊢
          split_ifs at hrw ⊢ with h1 h2
          · have hj : r - n < C.size := h1.2.1
            have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
            have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
              rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
              · exact ⟨ho, hl⟩
              · exact absurd hn h1.2.2
            have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
            have hnj : n + (r - n) = r := by omega
            rw [BTree.wires_node] at hrw ⊢
            simp only [Finset.mem_insert, Finset.mem_union] at hrw ⊢
            rcases hrw with hreq | hwl | hwr
            · have hpeq : r - n = parentGate C w := by omega
              have hwin_r : w ∈ (gateAt C (r - n)).inputs := by rwa [hpeq]
              rw [hinp] at hwin_r
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin_r
              have hint_w : isInternalChild n C w := by
                refine ⟨hstep.1, ?_⟩
                rintro ⟨hle, _, hnot⟩
                rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
                · omega
                · exact hne hnot
              have hw_in_child : ∀ u : ℕ, w = u →
                  w ∈ (if hu : u < r ∧ isInternalChild n C u then
                    if u < n then BTree.priv u else buildTree n C u
                  else BTree.mark u : BTree).wires n := by
                intro u hu
                subst hu
                have hcond : w < r ∧ isInternalChild n C w := ⟨by omega, hint_w⟩
                rw [dif_pos hcond]
                by_cases hwn : w < n
                · rw [if_pos hwn]
                  simp [BTree.wires, BTree.privs]
                · rw [if_neg hwn, buildTree]
                  have hwb : n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not := by
                    rcases hw with ⟨hlt, _⟩ | hgood
                    · omega
                    · exact hgood
                  rw [dif_pos hwb, BTree.wires_node]
                  have : n + (w - n) = w := by omega
                  rw [this]
                  exact Finset.mem_insert_self _ _
              rcases hwin_r with h0 | h1'
              · exact Or.inr (Or.inl (hw_in_child _ h0))
              · exact Or.inr (Or.inr (hw_in_child _ h1'))
            · refine Or.inr (Or.inl ?_)
              split_ifs at hwl ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwl
                omega
              · exact ihr _ huc.1 hwl
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwl
            · refine Or.inr (Or.inr ?_)
              split_ifs at hwr ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwr
                omega
              · exact ihr _ huc.1 hwr
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwr
          · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
              Finset.mem_singleton] at hrw
            omega
          · simp [BTree.wires, BTree.privs, BTree.gates] at hrw
      exact hrec _ hnp_in
    · rw [owner_fixed n C hstep, buildTree]
      rcases hw with ⟨hlt, hr1⟩ | hbin
      · have hnotb : ¬ (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not) := by omega
        rw [dif_neg hnotb, if_pos ⟨hlt, hr1⟩]
        simp [BTree.wires, BTree.privs, BTree.gates]
      · rw [dif_pos hbin, BTree.wires_node]
        have : n + (w - n) = w := by omega
        rw [this]
        exact Finset.mem_insert_self _ _

theorem mem_privs_iff_lt (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ w, w ∈ t.privs ↔ w ∈ t.wires n ∧ w < n := by
  induction t with
  | priv u =>
    intro w
    simp only [BTree.privs, BTree.wires, BTree.gates, Finset.image_empty, Finset.union_empty,
      Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, ht.1⟩
    · exact fun h => h.1
  | mark _ =>
    intro w
    simp [BTree.privs, BTree.wires, BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro w
    rw [BTree.wires_node]
    simp only [BTree.privs, Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · have := (ihl hgl w).1 h
        exact ⟨Or.inr (Or.inl this.1), this.2⟩
      · have := (ihr hgr w).1 h
        exact ⟨Or.inr (Or.inr this.1), this.2⟩
    · rintro ⟨rfl | h | h, hlt⟩
      · omega
      · exact Or.inl ((ihl hgl w).2 ⟨h, hlt⟩)
      · exact Or.inr ((ihr hgr w).2 ⟨h, hlt⟩)

theorem mem_gates_iff_ge (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ k, k ∈ t.gates ↔ n + k ∈ t.wires n := by
  induction t with
  | priv u =>
    intro k
    have hu : u < n := ht.1
    simp only [BTree.gates, BTree.wires, BTree.privs, Finset.image_empty, Finset.union_empty,
      Finset.notMem_empty, Finset.mem_singleton, false_iff]
    omega
  | mark _ =>
    intro k
    simp [BTree.gates, BTree.wires, BTree.privs]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro k
    rw [BTree.wires_node]
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union]
    rw [ihl hgl k, ihr hgr k]
    constructor
    · rintro (rfl | h | h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (heq | h | h)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

open Classical in
theorem buildTree_marks_eq_sum (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ),
      ((r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)) →
      (buildTree n C r).marks =
        ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hgt := buildTree_good n C hshape hback r
    have hdisj_from_good := (good_internal_reads hback hout hgt).2
    have hnot_from_good : ∀ j l r', buildTree n C r = BTree.node j l r' → j ∉ l.gates ∧ j ∉ r'.gates := by
      intro j l r' heq
      rw [heq] at hgt
      exact good_node_not_mem_sub hback hgt
    rw [buildTree] at hgt hdisj_from_good hnot_from_good ⊢
    split_ifs at hgt hdisj_from_good hnot_from_good ⊢ with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨ho, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      set ch : ℕ → BTree := fun u =>
        if hu : u < r ∧ isInternalChild n C u then
          if u < n then BTree.priv u else buildTree n C u
        else BTree.mark u
      have hnot := good_node_not_mem_sub hback hgt
      have hdisjw := hdisj_from_good (r - n) _ _ rfl
      have hdisjg : Disjoint (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates := by
        rw [Finset.disjoint_left]
        intro k hkl hkr
        exact Finset.disjoint_left.1 hdisjw
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
      have hj_not_u : r - n ∉ (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates ∪
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates :=
        Finset.notMem_union.2 hnot
      simp only [BTree.marks, BTree.gates]
      rw [Finset.sum_insert hj_not_u, Finset.sum_union hdisjg]
      have hch_eq : ∀ u : ℕ, u < r →
          (ch u).marks =
            (if ¬ isInternalChild n C u then 1 else 0) +
            ∑ j ∈ (ch u).gates,
              @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
                (gateAt C j).inputs := by
        intro u hult
        dsimp only [ch]
        by_cases huc : u < r ∧ isInternalChild n C u
        · rw [dif_pos huc, if_neg (not_not.2 huc.2), zero_add]
          by_cases hun : u < n
          · rw [if_pos hun]
            simp [BTree.marks, BTree.gates]
          · rw [if_neg hun]
            have hvalid : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op ≠ GateOp.not :=
              ⟨by omega, by omega, fun hnot => huc.2.2 ⟨by omega, by omega, hnot⟩⟩
            exact ih u hult (Or.inr hvalid)
        · rw [dif_neg huc]
          have hni : ¬ isInternalChild n C u := fun hi => huc ⟨hult, hi⟩
          rw [if_pos hni]
          simp [BTree.marks, BTree.gates]
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      rw [hch_eq _ hu0_lt, hch_eq _ hu1_lt]
      have hcnt_pair :
          @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
            (gateAt C (r - n)).inputs =
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 0 0) then 1 else 0) +
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 1 0) then 1 else 0) := by
        conv_lhs => rw [hinp]
        simp only [List.countP_cons, List.countP_nil]
        have hdec : ∀ (P : Prop),
            (if (@decide P (Classical.propDecidable P)) = true then 1 else 0) =
            if P then 1 else 0 := by
          intro P
          by_cases hP : P
          · rw [@decide_eq_true P (Classical.propDecidable P) hP, if_pos rfl, if_pos hP]
          · rw [@decide_eq_false P (Classical.propDecidable P) hP, if_neg Bool.false_ne_true, if_neg hP]
        rw [hdec, hdec, Nat.zero_add, Nat.add_comm]
        congr 1
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
      rw [hcnt_pair]
      omega
    · simp [BTree.marks, BTree.gates]
    · rcases hr with h | h
      · exact absurd h h2
      · exact absurd h h1

theorem list_countP_le_sum_count (l : List ℕ) (S : Finset ℕ) :
    @List.countP ℕ (fun u => @decide (u ∈ S) (Classical.propDecidable _)) l =
      ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a ls ih =>
    simp only [List.countP_cons, List.count_cons, Finset.sum_add_distrib, ih]
    have h1 : (∑ w ∈ S, if a == w then 1 else 0) = if a ∈ S then 1 else 0 := by
      by_cases ha : a ∈ S
      · rw [if_pos ha, Finset.sum_eq_single a]
        · simp
        · intro w _ hwa
          simp [beq_eq_false_iff_ne.2 (Ne.symm hwa)]
        · intro h
          exact absurd ha h
      · rw [if_neg ha, Finset.sum_eq_zero]
        intro w hw
        have hne : a ≠ w := fun h => ha (h ▸ hw)
        simp [beq_eq_false_iff_ne.2 hne]
    rw [h1]
    by_cases ha : a ∈ S <;> simp [ha] <;> omega

theorem list_flatMap_collect {α : Type*} [DecidableEq α] (L : List α) (f : α → List (Finset ℕ))
    (g : α → Finset ℕ)
    (hnd : L.Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (g a) (g b))
    (hf_sub : ∀ a ∈ L, ∀ S ∈ f a, S ⊆ g a)
    (hf_pw : ∀ a ∈ L, (f a).Pairwise Disjoint)
    (hf_cov : ∀ a ∈ L, (f a).toFinset.biUnion (fun S => S) = g a) :
    (L.flatMap f).Pairwise Disjoint ∧
    (L.flatMap f).toFinset.biUnion (fun S => S) = L.toFinset.biUnion g ∧
    (L.flatMap f).length = ∑ a ∈ L.toFinset, (f a).length := by
  induction L with
  | nil => simp
  | cons a ls ih =>
    rw [List.nodup_cons] at hnd
    have hrec := ih hnd.2
      (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hf_sub x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_pw x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_cov x (List.mem_cons_of_mem a hx))
    have hfa_sub : ∀ S ∈ f a, S ⊆ g a := hf_sub a (List.mem_cons_self ..)
    have hfa_pw : (f a).Pairwise Disjoint := hf_pw a (List.mem_cons_self ..)
    have hfa_cov : (f a).toFinset.biUnion (fun S => S) = g a := hf_cov a (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨hfa_pw, hrec.1, fun S1 h1 S2 h2 => ?_⟩
      obtain ⟨b, hb, hS2⟩ := List.mem_flatMap.1 h2
      have hab : a ≠ b := fun h => hnd.1 (h ▸ hb)
      exact Disjoint.mono (hfa_sub S1 h1) (hf_sub b (List.mem_cons_of_mem a hb) S2 hS2)
        (hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb) hab)
    · simp only [List.flatMap_cons, List.toFinset_append, Finset.union_biUnion, hfa_cov, hrec.2.1,
        List.toFinset_cons, Finset.biUnion_insert]
    · simp only [List.flatMap_cons, List.length_append, hrec.2.2, List.toFinset_cons]
      rw [Finset.sum_insert (mt List.mem_toFinset.1 hnd.1)]

theorem main (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C)
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size → 0 < readsIn C (Finset.range C.size) (n + j)) :
    let gates := Finset.range C.size
    let gate := gateAt C
    let reads := readsIn C gates
    let neg := @Finset.filter ℕ (fun k => (gate k).op = GateOp.not)
      (fun k => Classical.propDecidable ((gate k).op = GateOp.not)) gates
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
      pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
      chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
      (0 < markedReads + neg.card → 0 < markedComponents) ∧
      (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
      (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
      (∀ S ∈ pure, S.Nonempty ∧ IsTree n C S ∅) ∧
      (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, IsTree n C S {b}) := by
  classical
  intro gates gate reads neg shared sharedGates markedReads once
  let validRoot : ℕ → Prop := fun r =>
    (r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)
  let Rout : Finset ℕ := if (gateAt C (C.size - 1)).op ≠ GateOp.not then {C.output} else ∅
  let Rsh : Finset ℕ :=
    (sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not)).image (fun k => n + k)
  let Rneg : Finset ℕ :=
    (neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0))).image
      (fun j => (gateAt C j).inputs.getD 0 0)
  let Roots : Finset ℕ := Rout ∪ Rsh ∪ Rneg
  have hRout_card : Rout.card ≤ 1 := by
    dsimp only [Rout]
    split_ifs <;> simp
  have hRsh_card : Rsh.card ≤ sharedGates.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRneg_card : Rneg.card ≤ neg.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRoots_le3 : Roots.card ≤ Rout.card + Rsh.card + Rneg.card :=
    (Finset.card_union_le (Rout ∪ Rsh) Rneg).trans
      (Nat.add_le_add_right (Finset.card_union_le Rout Rsh) _)
  have hRoots_card : Roots.card ≤ sharedGates.card + neg.card + 1 := by
    omega
  have hRoots_valid : ∀ r ∈ Roots, validRoot r := by
    intro r hr
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        exact Or.inr ⟨by omega, by omega, by rwa [show C.output - n = C.size - 1 by omega]⟩
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates, gates, Finset.mem_range] at hk
      exact Or.inr ⟨by omega, by omega, by simpa using hk.2⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      have hlt : (gateAt C j).inputs.getD 0 0 < n + j := hback j hj.1.1 _ hmem0
      by_cases hlt_n : (gateAt C j).inputs.getD 0 0 < n
      · exact Or.inl ⟨hlt_n, hj.2.1⟩
      · exact Or.inr ⟨by omega, by omega, fun hnot => hj.2.2 ⟨by omega, by omega, hnot⟩⟩
  have hRoots_fixed : ∀ r ∈ Roots, owner n C r = r := by
    intro r hr
    refine owner_fixed n C ?_
    rintro ⟨hr1, hnot⟩
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        have hz := reads_output_zero n C hback hout
        omega
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates] at hk
      have h2r : 2 ≤ readsOf C (n + k) := hk.1.2
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
      have hpeq : j = parentGate C ((gateAt C j).inputs.getD 0 0) :=
        huniq j (Finset.mem_range.2 hj.1.1) hmem0
      rw [← hpeq] at hnot
      exact hnot hj.1.2
  have howner_mem : ∀ w : ℕ, validRoot w → owner n C w ∈ Roots := by
    intro w
    induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
    | ind d ih =>
      intro hw
      by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
      · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
        have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
        have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
        rw [owner_step n C hback hstep.1 hstep.2]
        exact ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      · rw [owner_fixed n C hstep]
        by_cases hr1 : readsOf C w = 1
        · have hpnot : (gateAt C (parentGate C w)).op = GateOp.not := by
            by_contra hne
            exact hstep ⟨hr1, hne⟩
          obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hr1
          have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
          have hgs := hshape (gateAt C (parentGate C w)) (gateAt_mem_gates C hplt)
          have hlen1 : (gateAt C (parentGate C w)).inputs.length = 1 := by
            rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
            · rcases ho with ho | ho <;> rw [hpnot] at ho <;> cases ho
            · exact hl
          have hweq : (gateAt C (parentGate C w)).inputs.getD 0 0 = w := by
            rw [list_len1_eq _ hlen1] at hpw
            simp only [List.mem_singleton] at hpw
            exact hpw.symm
          have hint : isInternalChild n C w := by
            refine ⟨hr1, ?_⟩
            rintro ⟨hle, _, hnot⟩
            rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
            · omega
            · exact hne hnot
          refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨parentGate C w, ?_, hweq⟩)
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.2 ⟨hpG, hpnot⟩, by rwa [hweq]⟩
        · rcases hw with ⟨_, hr1'⟩ | ⟨hle, hlt, hne⟩
          · exact absurd hr1' hr1
          · by_cases hlast : w - n = C.size - 1
            · have hwout : w = C.output := by omega
              subst hwout
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              dsimp only [Rout]
              have hop : (gateAt C (C.size - 1)).op ≠ GateOp.not := by
                rwa [← hlast]
              simp [hop]
            · have hpos := hused (w - n) hlt (by omega)
              have hge2 : 2 ≤ readsOf C (n + (w - n)) := by
                have heq : n + (w - n) = w := by omega
                rw [heq] at hpos ⊢
                change 0 < readsOf C w at hpos
                omega
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              refine Finset.mem_image.2 ⟨w - n, ?_, by omega⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hge2⟩, hne⟩
  have hpriv_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).privs (buildTree n C r2).privs := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 w (Finset.mem_union_left _ hw1)
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 w (Finset.mem_union_left _ hw2)
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hgates_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).gates (buildTree n C r2).gates := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk1, rfl⟩))
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk2, rfl⟩))
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hpriv_cov : Roots.biUnion (fun r => (buildTree n C r).privs) = once := by
    ext w
    simp only [Finset.mem_biUnion, once, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨r, hr, hwp⟩
      have hgt := buildTree_good n C hshape hback r
      have hlt := ((mem_privs_iff_lt n C hgt w).1 hwp).2
      have hwr : readsOf C w = 1 := by
        by_cases hweq : w = r
        · subst hweq
          rcases hRoots_valid w hr with ⟨_, hr1⟩ | ⟨hle, _, _⟩
          · exact hr1
          · omega
        · have hroot : (buildTree n C r).root n = r := buildTree_root n C r
          exact ((good_internal_reads hback hout hgt).1 w (Finset.mem_union_left _ hwp)
            (by rwa [hroot])).2.1
      exact ⟨hlt, hwr⟩
    · rintro ⟨hlt, hr1⟩
      have hmemR : owner n C w ∈ Roots := howner_mem w (Or.inl ⟨hlt, hr1⟩)
      refine ⟨owner n C w, hmemR, ?_⟩
      have hw := mem_wires_buildTree_owner n C hback hshape w (Or.inl ⟨hlt, hr1⟩)
      exact (mem_privs_iff_lt n C (buildTree_good n C hshape hback _) w).2 ⟨hw, hlt⟩
  have hsum_marks : ∑ r ∈ Roots, (buildTree n C r).marks ≤ markedReads + neg.card := by
    have h1 : ∑ r ∈ Roots, (buildTree n C r).marks =
        ∑ r ∈ Roots, ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_congr rfl (fun r hr => buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hr))
    rw [h1, ← Finset.sum_biUnion (fun r1 hr1 r2 hr2 hne => hgates_disj r1 hr1 r2 hr2 hne)]
    have hsub_g : Roots.biUnion (fun r => (buildTree n C r).gates) ⊆ gates := by
      intro j hj
      obtain ⟨r, _, hjr⟩ := Finset.mem_biUnion.1 hj
      exact good_gates_sub (buildTree_good n C hshape hback r) hjr
    have hle1 :
        ∑ j ∈ Roots.biUnion (fun r => (buildTree n C r).gates),
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_le_sum_of_subset hsub_g
    let negOnly : Finset ℕ := (neg.filter (fun k => readsOf C (n + k) = 1)).image (fun k => n + k)
    have hterm_le : ∀ j ∈ gates,
        @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
          (gateAt C j).inputs ≤
        @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
          (gateAt C j).inputs +
        @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
          (gateAt C j).inputs := by
      intro j hj
      have hjlt : j < C.size := Finset.mem_range.1 hj
      have hgen : ∀ (l : List ℕ), (∀ u ∈ l, u < n + j) →
          (∀ u ∈ l, 1 ≤ readsOf C u) →
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _)) l ≤
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _)) l +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _)) l := by
        intro l
        induction l with
        | nil => intros; simp
        | cons u ls ih =>
          intro hlt_l hpos_l
          simp only [List.countP_cons]
          have ih' := ih (fun v hv => hlt_l v (List.mem_cons_of_mem u hv))
            (fun v hv => hpos_l v (List.mem_cons_of_mem u hv))
          have hult : u < n + j := hlt_l u (List.mem_cons_self ..)
          have hupos : 1 ≤ readsOf C u := hpos_l u (List.mem_cons_self ..)
          by_cases hni : ¬ isInternalChild n C u
          · have hor : u ∈ shared ∨ u ∈ negOnly := by
              by_cases hr2 : 2 ≤ readsOf C u
              · left
                exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hr2⟩
              · right
                have hr1 : readsOf C u = 1 := by omega
                have hnotg : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not := by
                  by_contra h
                  exact hni ⟨hr1, h⟩
                refine Finset.mem_image.2 ⟨u - n, ?_, by omega⟩
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hnotg.2.1, hnotg.2.2⟩, ?_⟩
                have : n + (u - n) = u := by omega
                rwa [this]
            have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = true :=
              @decide_eq_true _ (Classical.propDecidable _) hni
            rw [hd1, if_pos rfl]
            rcases hor with hsh | hno
            · have hd2 : (@decide (u ∈ shared) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hsh
              rw [hd2, if_pos rfl]
              split_ifs <;> omega
            · have hd3 : (@decide (u ∈ negOnly) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hno
              rw [hd3, if_pos rfl]
              split_ifs <;> omega
          · have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = false :=
              @decide_eq_false _ (Classical.propDecidable _) hni
            rw [hd1]
            simp only [Bool.false_eq_true, ↓reduceIte]
            split_ifs <;> omega
      exact hgen (gateAt C j).inputs (fun u hu => hback j hjlt u hu)
        (fun u hu => readsIn_ge_of_mem C hj hu)
    have hle2 :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          (@List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs) :=
      Finset.sum_le_sum hterm_le
    rw [Finset.sum_add_distrib] at hle2
    have hsum_sh :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs = markedReads := by
      simp_rw [list_countP_le_sum_count _ shared]
      rw [Finset.sum_comm]
      rfl
    have hsum_no :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs ≤ neg.card := by
      simp_rw [list_countP_le_sum_count _ negOnly]
      rw [Finset.sum_comm]
      calc ∑ w ∈ negOnly, readsOf C w
          = ∑ _w ∈ negOnly, 1 := by
            refine Finset.sum_congr rfl (fun w hw => ?_)
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
            exact (Finset.mem_filter.1 hk).2
        _ = negOnly.card := by simp
        _ ≤ neg.card := (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    omega
  let Rpure : Finset ℕ := Roots.filter (fun r => (buildTree n C r).marks = 0)
  let Rmark : Finset ℕ := Roots.filter (fun r => 1 ≤ (buildTree n C r).marks)
  have hpart_card : Rpure.card + Rmark.card = Roots.card := by
    have hdisj : Disjoint Rpure Rmark := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      simp only [Rpure, Rmark, Finset.mem_filter] at hr1 hr2
      omega
    have hunion : Rpure ∪ Rmark = Roots := by
      ext r
      simp only [Rpure, Rmark, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hm : (buildTree n C r).marks = 0
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hroots_strict : 0 < markedReads + neg.card → Rmark.card = 0 →
      Roots.card ≤ sharedGates.card + neg.card := by
    intro hpos hR0
    have hall0 : ∀ r ∈ Roots, (buildTree n C r).marks = 0 := by
      intro r hr
      by_contra hne
      have hmem : r ∈ Rmark := Finset.mem_filter.2 ⟨hr, by omega⟩
      have hcp : 0 < Rmark.card := Finset.card_pos.2 ⟨r, hmem⟩
      omega
    by_cases hneg : neg.Nonempty
    · obtain ⟨j0, hj0⟩ := hneg
      have hj0lt : j0 < C.size := Finset.mem_range.1 (Finset.mem_filter.1 hj0).1
      have hj0not : (gateAt C j0).op = GateOp.not := (Finset.mem_filter.1 hj0).2
      by_cases hlast : j0 = C.size - 1
      · have hRout0 : Rout.card = 0 := by
          dsimp only [Rout]
          rw [← hlast, if_neg (not_not.2 hj0not)]
          simp
        omega
      · by_cases hsh : j0 ∈ sharedGates
        · have hRsh_lt : Rsh.card < sharedGates.card := by
            have hss : sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not) ⊂ sharedGates := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
              have hmem : j0 ∈ sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not) := by
                rwa [heq]
              exact (Finset.mem_filter.1 hmem).2 hj0not
            exact Nat.lt_of_le_of_lt Finset.card_image_le (Finset.card_lt_card hss)
          omega
        · have hposj := hused j0 hj0lt (by omega)
          have hr1j : readsOf C (n + j0) = 1 := by
            change 0 < readsOf C (n + j0) at hposj
            by_contra hne1
            have hge2 : 2 ≤ readsOf C (n + j0) := by omega
            exact hsh (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj0lt, hge2⟩)
          obtain ⟨q, hqG, hqin, _, _⟩ := readsIn_eq_one_unique C (gatesOf C) (n + j0) hr1j
          have hqlt : q < C.size := Finset.mem_range.1 hqG
          by_cases hqnot : (gateAt C q).op = GateOp.not
          · have hqneg : q ∈ neg := Finset.mem_filter.2 ⟨hqG, hqnot⟩
            have hgs := hshape (gateAt C q) (gateAt_mem_gates C hqlt)
            have hlen1 : (gateAt C q).inputs.length = 1 := by
              rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
              · rcases ho with ho | ho <;> rw [hqnot] at ho <;> cases ho
              · exact hl
            have hq0 : (gateAt C q).inputs.getD 0 0 = n + j0 := by
              rw [list_len1_eq _ hlen1] at hqin
              simp only [List.mem_singleton] at hqin
              exact hqin.symm
            have hq_out : ¬ isInternalChild n C ((gateAt C q).inputs.getD 0 0) := by
              rw [hq0]
              rintro ⟨_, h⟩
              exact h ⟨by omega, by omega, by simpa using hj0not⟩
            have hRneg_lt : Rneg.card < neg.card := by
              have hss : neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0)) ⊂ neg := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
                have hmem : q ∈ neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0)) := by
                  rwa [heq]
                exact hq_out (Finset.mem_filter.1 hmem).2
              exact Nat.lt_of_le_of_lt Finset.card_image_le (Finset.card_lt_card hss)
            omega
          · exfalso
            have hvq : validRoot (n + q) := Or.inr ⟨by omega, by omega, by simpa using hqnot⟩
            let r := owner n C (n + q)
            have hrR : r ∈ Roots := howner_mem (n + q) hvq
            have hqw : n + q ∈ (buildTree n C r).wires n :=
              mem_wires_buildTree_owner n C hback hshape (n + q) hvq
            have hqg : q ∈ (buildTree n C r).gates :=
              (mem_gates_iff_ge n C (buildTree_good n C hshape hback r) q).2 hqw
            have hm0 := hall0 r hrR
            rw [buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hrR)] at hm0
            have hcnt0 : @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
                (Classical.propDecidable _)) (gateAt C q).inputs = 0 :=
              Finset.sum_eq_zero_iff.1 hm0 q hqg
            have hni : ¬ isInternalChild n C (n + j0) := by
              rintro ⟨_, h⟩
              exact h ⟨by omega, by omega, by simpa using hj0not⟩
            have hcp : 0 < @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
                (Classical.propDecidable _)) (gateAt C q).inputs :=
              List.countP_pos_iff.2 ⟨n + j0, hqin, by simp [hni]⟩
            omega
    · exfalso
      have hneg0 : neg.card = 0 := Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hneg)
      have hmkpos : 0 < markedReads := by omega
      have hsh_non : shared.Nonempty := by
        by_contra h
        dsimp only [markedReads] at hmkpos
        rw [Finset.not_nonempty_iff_eq_empty.1 h] at hmkpos
        simp at hmkpos
      obtain ⟨w0, hw0⟩ := hsh_non
      have hr2 : 2 ≤ readsIn C (gatesOf C) w0 := (Finset.mem_filter.1 hw0).2
      obtain ⟨q, hqG, hqin⟩ := (readsIn_pos_iff C (gatesOf C) w0).1 (by omega)
      have hqlt : q < C.size := Finset.mem_range.1 hqG
      have hqnot : (gateAt C q).op ≠ GateOp.not := by
        intro h
        exact hneg ⟨q, Finset.mem_filter.2 ⟨hqG, h⟩⟩
      have hvq : validRoot (n + q) := Or.inr ⟨by omega, by omega, by simpa using hqnot⟩
      let r := owner n C (n + q)
      have hrR : r ∈ Roots := howner_mem (n + q) hvq
      have hqw : n + q ∈ (buildTree n C r).wires n :=
        mem_wires_buildTree_owner n C hback hshape (n + q) hvq
      have hqg : q ∈ (buildTree n C r).gates :=
        (mem_gates_iff_ge n C (buildTree_good n C hshape hback r) q).2 hqw
      have hm0 := hall0 r hrR
      rw [buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hrR)] at hm0
      have hcnt0 : @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
          (Classical.propDecidable _)) (gateAt C q).inputs = 0 :=
        Finset.sum_eq_zero_iff.1 hm0 q hqg
      have hni : ¬ isInternalChild n C w0 := by
        rintro ⟨hr1, _⟩
        change readsIn C (gatesOf C) w0 = 1 at hr1
        omega
      have hcp : 0 < @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u)
          (Classical.propDecidable _)) (gateAt C q).inputs :=
        List.countP_pos_iff.2 ⟨w0, hqin, by simp [hni]⟩
      omega
  let pureFun : ℕ → List (Finset ℕ) := fun r =>
    if (buildTree n C r).privs.Nonempty then [(buildTree n C r).privs] else []
  let pure : List (Finset ℕ) := Rpure.toList.flatMap pureFun
  have hpure_col := list_flatMap_collect Rpure.toList pureFun (fun r => (buildTree n C r).privs)
    (Finset.nodup_toList Rpure)
    (fun r1 h1 r2 h2 hne => hpriv_disj r1 (Finset.mem_filter.1 (Finset.mem_toList.1 h1)).1
      r2 (Finset.mem_filter.1 (Finset.mem_toList.1 h2)).1 hne)
    (fun r _ S hS => by
      dsimp only [pureFun] at hS
      split_ifs at hS
      · rw [List.mem_singleton.1 hS]
      · simp at hS)
    (fun r _ => by
      dsimp only [pureFun]
      split_ifs <;> simp)
    (fun r _ => by
      dsimp only [pureFun]
      split_ifs with hnp
      · simp
      · simp [Finset.not_nonempty_iff_eq_empty.1 hnp])
  have hpure_len : pure.length ≤ Rpure.card := by
    rw [hpure_col.2.2, Finset.toList_toFinset]
    calc ∑ r ∈ Rpure, (pureFun r).length
        ≤ ∑ _r ∈ Rpure, 1 := Finset.sum_le_sum (fun r _ => by dsimp only [pureFun]; split_ifs <;> simp)
      _ = Rpure.card := by simp
  have hpure_prop : ∀ S ∈ pure, S.Nonempty ∧ IsTree n C S ∅ := by
    intro S hS
    obtain ⟨r, hr, hSr⟩ := List.mem_flatMap.1 hS
    have hr' := Finset.mem_filter.1 (Finset.mem_toList.1 hr)
    dsimp only [pureFun] at hSr
    split_ifs at hSr with hnp
    · rw [List.mem_singleton.1 hSr]
      exact ⟨hnp, good_markFree_isTree hback hout (buildTree_good n C hshape hback r) hr'.2⟩
    · simp at hSr
  let chainFun : ℕ → List (Finset ℕ) := fun r =>
    if h : 1 ≤ (buildTree n C r).marks then
      Classical.choose (marked_tree_chains hback hout (buildTree_good n C hshape hback r) h)
    else []
  have hchain_spec : ∀ r ∈ Rmark,
      (chainFun r).length + 1 ≤ 2 * (buildTree n C r).marks ∧
      (∀ S ∈ chainFun r, S.Nonempty ∧ S ⊆ (buildTree n C r).privs ∧ ∃ b, IsTree n C S {b}) ∧
      (chainFun r).Pairwise Disjoint ∧
      (chainFun r).toFinset.biUnion (fun S => S) = (buildTree n C r).privs := by
    intro r hr
    have hm : 1 ≤ (buildTree n C r).marks := (Finset.mem_filter.1 hr).2
    have hdef : chainFun r =
        Classical.choose (marked_tree_chains hback hout (buildTree_good n C hshape hback r) hm) := by
      dsimp only [chainFun]
      simp only [hm, ↓reduceDIte]
    rw [hdef]
    exact Classical.choose_spec (marked_tree_chains hback hout (buildTree_good n C hshape hback r) hm)
  let chains : List (Finset ℕ) := Rmark.toList.flatMap chainFun
  have hchains_col := list_flatMap_collect Rmark.toList chainFun (fun r => (buildTree n C r).privs)
    (Finset.nodup_toList Rmark)
    (fun r1 h1 r2 h2 hne => hpriv_disj r1 (Finset.mem_filter.1 (Finset.mem_toList.1 h1)).1
      r2 (Finset.mem_filter.1 (Finset.mem_toList.1 h2)).1 hne)
    (fun r hr S hS => (hchain_spec r (Finset.mem_toList.1 hr)).2.1 S hS |>.2.1)
    (fun r hr => (hchain_spec r (Finset.mem_toList.1 hr)).2.2.1)
    (fun r hr => (hchain_spec r (Finset.mem_toList.1 hr)).2.2.2)
  have hchains_len : chains.length + Rmark.card ≤ 2 * (markedReads + neg.card) := by
    rw [hchains_col.2.2, Finset.toList_toFinset]
    have h1 : (∑ r ∈ Rmark, (chainFun r).length) + Rmark.card =
        ∑ r ∈ Rmark, ((chainFun r).length + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [h1]
    calc ∑ r ∈ Rmark, ((chainFun r).length + 1)
        ≤ ∑ r ∈ Rmark, 2 * (buildTree n C r).marks :=
          Finset.sum_le_sum (fun r hr => (hchain_spec r hr).1)
      _ = 2 * ∑ r ∈ Rmark, (buildTree n C r).marks := by rw [← Finset.mul_sum]
      _ ≤ 2 * ∑ r ∈ Roots, (buildTree n C r).marks :=
          Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ ≤ 2 * (markedReads + neg.card) := Nat.mul_le_mul_left 2 hsum_marks
  have hchains_prop : ∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, IsTree n C S {b} := by
    intro S hS
    obtain ⟨r, hr, hSr⟩ := List.mem_flatMap.1 hS
    have hs := (hchain_spec r (Finset.mem_toList.1 hr)).2.1 S hSr
    exact ⟨hs.1, hs.2.2⟩
  let markedComponents : ℕ := if 0 < markedReads + neg.card ∧ Rmark.card = 0 then 1 else Rmark.card
  refine ⟨pure, chains, markedComponents, ?_, ?_, ?_, ?_, ?_, hpure_prop, hchains_prop⟩
  · dsimp only [markedComponents]
    split_ifs with h
    · have hst := hroots_strict h.1 h.2
      omega
    · omega
  · dsimp only [markedComponents]
    split_ifs with h
    · have hR0 : Rmark = ∅ := Finset.card_eq_zero.1 h.2
      have hc0 : chains.length = 0 := by
        simp [chains, hR0]
      omega
    · exact hchains_len
  · intro hpos
    dsimp only [markedComponents]
    split_ifs with h
    · omega
    · by_contra hle
      exact h ⟨hpos, by omega⟩
  · rw [List.pairwise_append]
    refine ⟨hpure_col.1, hchains_col.1, fun S1 h1 S2 h2 => ?_⟩
    obtain ⟨r1, hr1, hS1⟩ := List.mem_flatMap.1 h1
    obtain ⟨r2, hr2, hS2⟩ := List.mem_flatMap.1 h2
    have hr1' := Finset.mem_filter.1 (Finset.mem_toList.1 hr1)
    have hr2' := Finset.mem_filter.1 (Finset.mem_toList.1 hr2)
    have hne : r1 ≠ r2 := by
      intro heq
      rw [heq] at hr1'
      omega
    have hsub1 : S1 ⊆ (buildTree n C r1).privs := by
      dsimp only [pureFun] at hS1
      split_ifs at hS1
      · rw [List.mem_singleton.1 hS1]
      · simp at hS1
    have hsub2 : S2 ⊆ (buildTree n C r2).privs :=
      ((hchain_spec r2 (Finset.mem_toList.1 hr2)).2.1 S2 hS2).2.1
    exact Disjoint.mono hsub1 hsub2 (hpriv_disj r1 hr1'.1 r2 hr2'.1 hne)
  · rw [List.toFinset_append, Finset.union_biUnion, hpure_col.2.1, hchains_col.2.1,
      Finset.toList_toFinset, Finset.toList_toFinset, ← Finset.union_biUnion]
    have hunion : Rpure ∪ Rmark = Roots := by
      ext r
      simp only [Rpure, Rmark, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hm : (buildTree n C r).marks = 0
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [hunion, hpriv_cov]


theorem thm :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
    pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
    chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
    (0 < markedReads + neg.card → 0 < markedComponents) ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b}) := by
  intro n C gates gate reads neg shared sharedGates markedReads once tree hshape hback hsz hout hused
  exact main n C hshape hback hsz hout hused

end S25644

namespace Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Finset

def Rich (v w : ℕ) (T : Fin v → Fin w → Bool) : Prop :=
  ∀ (i j k : Fin v), i ≠ j → i ≠ k → j ≠ k →
    ∀ (x y : Bool), (x = true ∨ y = true) →
      5 ≤ (Finset.univ.filter (fun col =>
        (T j col != T i col) = x ∧ (T k col != T i col) = y)).card

def Bounded (v w : ℕ) (T : Fin v → Fin w → Bool) (h : ℕ) : Prop :=
  ∀ (off : Fin w → Bool) (F : Finset (Fin v × Fin v)),
    (∀ e ∈ F, e.1 ≠ e.2 ∧ ∃ side : Bool,
      (Finset.univ.filter (fun col =>
        (T e.1 col != T e.2 col) = side ∧ T e.1 col ≠ off col)).card ≤ 2) →
    (∀ e ∈ F, ∀ f ∈ F, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) → F.card ≤ h

def skel (D : BinaryCircuit) : Circuit :=
  ⟨D.gates.map (fun g => ⟨GateOp.and, [g.left, g.right]⟩), D.output⟩

lemma skel_size (D : BinaryCircuit) : (skel D).size = D.size := by
  simp [skel, Circuit.size, BinaryCircuit.size]

lemma skel_gateAt (D : BinaryCircuit) (j : ℕ) (hj : j < D.gates.length) :
    gateAt (skel D) j = ⟨GateOp.and, [(D.gates.get ⟨j, hj⟩).left, (D.gates.get ⟨j, hj⟩).right]⟩ := by
  unfold gateAt skel
  rw [List.getD_eq_getElem _ _ (by simp [hj])]
  simp

def bankR (n : ℕ) (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val ∈ S)

def bankC (n m : ℕ) (S : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j : Fin m => n + j.val ∈ S)

lemma bankR_image_union_bankC_image (n m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range (n + m)) :
    (bankR n S).image (fun i : Fin n => i.val) ∪ (bankC n m S).image (fun j : Fin m => n + j.val) = S := by
  ext w
  simp only [Finset.mem_union, Finset.mem_image, bankR, bankC, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact hi
    · exact hj
  · intro hw
    have hlt : w < n + m := Finset.mem_range.mp (hS hw)
    by_cases hwn : w < n
    · left
      exact ⟨⟨w, hwn⟩, hw, rfl⟩
    · right
      refine ⟨⟨w - n, by omega⟩, ?_, by dsimp; omega⟩
      have heq : n + (w - n) = w := by omega
      simpa [heq] using hw

lemma card_eq_bankR_add_bankC (n m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range (n + m)) :
    S.card = (bankR n S).card + (bankC n m S).card := by
  have hun := bankR_image_union_bankC_image n m S hS
  have hdisj : Disjoint ((bankR n S).image (fun i : Fin n => i.val))
      ((bankC n m S).image (fun j : Fin m => n + j.val)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
    omega
  conv_lhs => rw [← hun]
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h))]

def oneEachFn {n m : ℕ} (u : Fin n) (v : Fin m) : Fin (n + m) → Bool :=
  fun k => if k.val < n then decide (k.val = u.val) else decide (k.val - n = v.val)

lemma ofFn_oneEachFn {n m : ℕ} (u : Fin n) (v : Fin m) :
    List.ofFn (oneEachFn u v) = PEqualNP.Represents.oneEach u v := by
  apply List.ext_getElem
  · simp [PEqualNP.Represents.oneEach]
  · intro k h1 h2
    simp only [List.getElem_ofFn, oneEachFn, PEqualNP.Represents.oneEach]
    by_cases hkn : k < n
    · rw [List.getElem_append_left (by simp [hkn])]
      simp [hkn, Fin.ext_iff]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn, hkn, ↓reduceIte, Fin.ext_iff]

lemma rich_sep {v w : ℕ} {T : Fin v → Fin w → Bool} (hv : 3 ≤ v) (hr : Rich v w T)
    (a b : Fin v) (hab : a ≠ b) : ∃ col : Fin w, T a col ≠ T b col := by
  have hlt : ({a, b} : Finset (Fin v)).card < (Finset.univ : Finset (Fin v)).card := by
    simp [hab]
    omega
  obtain ⟨c, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hcn : c ≠ a ∧ c ≠ b := by
    have h2 := hc.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
    exact h2
  have h5 := hr a b c hab (Ne.symm hcn.1) (Ne.symm hcn.2) true false (Or.inl rfl)
  have hpos : 0 < (Finset.univ.filter (fun col =>
      (T b col != T a col) = true ∧ (T c col != T a col) = false)).card := by omega
  obtain ⟨col, hcol⟩ := Finset.card_pos.mp hpos
  have hcol' := (Finset.mem_filter.mp hcol).2.1
  refine ⟨col, ?_⟩
  intro heq
  rw [heq] at hcol'
  simp at hcol'

lemma three_funcs_miss (a b c : Bool → Bool) :
    ∃ x y : Bool, (x = true ∨ y = true) ∧
      ∀ (m t : Bool), ¬ (((m && b t) != (m && a t)) = x ∧ ((m && c t) != (m && a t)) = y) := by
  revert a b c
  decide

lemma two_funcs_affordable (ra rb : Bool → Bool) :
    (∃ side : Bool, ∀ (m t ga gb off : Bool),
      (ga != off) = (m && ra t) → (gb != off) = (m && rb t) →
      ¬ ((ga != gb) = side ∧ ga ≠ off)) ∨
    (∃ side : Bool, ∀ (m t ga gb off : Bool),
      (ga != off) = (m && ra t) → (gb != off) = (m && rb t) →
      ¬ ((gb != ga) = side ∧ gb ≠ off)) := by
  revert ra rb
  decide

lemma collapse_card_le_one {E : Finset ℕ} (hE : E.card ≤ 1) :
    ∃ (f : (↥E → Bool) → Bool) (g : Bool → (↥E → Bool)), ∀ h, g (f h) = h := by
  by_cases h0 : E = ∅
  · refine ⟨fun _ => false, fun _ e => False.elim (by rw [h0] at e; exact Finset.notMem_empty e.val e.property), ?_⟩
    intro h
    funext e
    rw [h0] at e
    exact False.elim (Finset.notMem_empty e.val e.property)
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have huniq : ∀ e : ↥E, e = ⟨e0, he0⟩ := by
      intro e
      apply Subtype.ext
      exact Finset.card_le_one.mp hE e.val e.property e0 he0
    refine ⟨fun h => h ⟨e0, he0⟩, fun b _ => b, ?_⟩
    intro h
    funext e
    rw [huniq e]

lemma unread_wires_eq {N : ℕ} (D : BinaryCircuit)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (w0 : ℕ) (hr0 : readsIn (skel D) (Finset.range D.size) w0 = 0)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hagree : ∀ u < N, u ≠ w0 → x.getD u false = y.getD u false)
    (w : ℕ) (hw : w < N + D.size) (hne : w ≠ w0) :
    (D.wires x).getD w false = (D.wires y).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hltN : w < N
    · rw [S25872.wires_getD_input D x N w hx hltN, S25872.wires_getD_input D y N w hy hltN]
      exact hagree w hltN hne
    · have hgeN : N ≤ w := by omega
      have hjlt : w - N < D.gates.length := by
        simp [BinaryCircuit.size] at hw
        omega
      let j : Fin D.gates.length := ⟨w - N, hjlt⟩
      have hjmem : w - N ∈ Finset.range D.size := Finset.mem_range.mpr (by
        change w - N < D.gates.length
        exact hjlt)
      have hcnt0 : (gateAt (skel D) (w - N)).inputs.count w0 = 0 := by
        have hle := Finset.single_le_sum (f := fun k => (gateAt (skel D) k).inputs.count w0)
          (fun _ _ => Nat.zero_le _) hjmem
        change (gateAt (skel D) (w - N)).inputs.count w0 ≤ readsIn (skel D) (Finset.range D.size) w0 at hle
        omega
      rw [skel_gateAt D (w - N) hjlt] at hcnt0
      have hnotmem : w0 ∉ [(D.gates.get j).left, (D.gates.get j).right] :=
        List.count_eq_zero.mp hcnt0
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnotmem
      have hl_ne : (D.gates.get j).left ≠ w0 := Ne.symm hnotmem.1
      have hr_ne : (D.gates.get j).right ≠ w0 := Ne.symm hnotmem.2
      have hjb := hback j
      have hw_eq : N + (w - N) = w := by omega
      have hll : (D.gates.get j).left < w := by
        have := hjb.1
        change (D.gates.get j).left < N + (w - N) at this
        omega
      have hrl : (D.gates.get j).right < w := by
        have := hjb.2
        change (D.gates.get j).right < N + (w - N) at this
        omega
      have hl_eq := ih _ hll (by omega) hl_ne
      have hr_eq := ih _ hrl (by omega) hr_ne
      have hx_g := S25872.wires_getD_gate D x N (w - N) hx hjlt hjb.1 hjb.2
      have hy_g := S25872.wires_getD_gate D y N (w - N) hy hjlt hjb.1 hjb.2
      rw [hw_eq] at hx_g hy_g
      rw [hx_g, hy_g]
      exact congrArg₂ (D.gates.get j).op hl_eq hr_eq

lemma unread_row_eq {n m : ℕ} (D : BinaryCircuit)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val)
    (hout : D.output + 1 = (n + m) + D.size) (hpos : 0 < D.size)
    (i : Fin n) (hr0 : readsIn (skel D) (Finset.range D.size) i.val = 0) (j : Fin m) :
    D.eval (PEqualNP.Represents.oneEach i j) =
      D.eval (List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))) := by
  have h1 : (PEqualNP.Represents.oneEach i j).length = n + m := by
    simp [PEqualNP.Represents.oneEach]
  have h2 : (List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))).length = n + m := by
    simp
  apply unread_wires_eq D hback i.val hr0 _ _ h1 h2 _ D.output (by omega) (by omega)
  intro u hu hne
  by_cases hun : u < n
  · rw [PEqualNP.Represents.oneEach, S25872.getD_append_left _ _ u (by simp [hun]),
      S25872.getD_append_left _ _ u (by simp [hun]),
      S25872.getD_one n i u hun, S25872.getD_replicate_false]
    simp [hne]
  · have hge : n ≤ u := by omega
    rw [PEqualNP.Represents.oneEach, S25872.getD_append_right _ _ u (by simp [hge]),
      S25872.getD_append_right _ _ u (by simp [hge])]
    simp

lemma unread_col_eq {n m : ℕ} (D : BinaryCircuit)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val)
    (hout : D.output + 1 = (n + m) + D.size) (hpos : 0 < D.size)
    (j : Fin m) (hr0 : readsIn (skel D) (Finset.range D.size) (n + j.val) = 0) (i : Fin n) :
    D.eval (PEqualNP.Represents.oneEach i j) =
      D.eval (List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false) := by
  have h1 : (PEqualNP.Represents.oneEach i j).length = n + m := by
    simp [PEqualNP.Represents.oneEach]
  have h2 : (List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false).length = n + m := by
    simp
  apply unread_wires_eq D hback (n + j.val) hr0 _ _ h1 h2 _ D.output (by omega) (by omega)
  intro u hu hne
  by_cases hun : u < n
  · rw [PEqualNP.Represents.oneEach, S25872.getD_append_left _ _ u (by simp [hun]),
      S25872.getD_append_left _ _ u (by simp [hun])]
  · have hge : n ≤ u := by omega
    have hltm : u - n < m := by omega
    rw [PEqualNP.Represents.oneEach, S25872.getD_append_right _ _ u (by simp [hge]),
      S25872.getD_append_right _ _ u (by simp [hge])]
    simp only [List.length_ofFn]
    rw [S25872.getD_one m j (u - n) hltm, S25872.getD_replicate_false]
    have hne' : u - n ≠ j.val := by omega
    simp [hne']

def IsTreeAt (N : ℕ) (C : Circuit) (S E region : Finset ℕ) (root : ℕ) : Prop :=
  let wires := S ∪ region.image (fun k => N + k)
  let localReads := readsIn C region
  region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
  (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
  (∀ j ∈ region,
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ E) ∧
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

def subWires (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ) (w : ℕ) : Finset ℕ :=
  if h : N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region then
    if _hl : (D.gates.get ⟨w - N, h.2.1⟩).left < w then
      if _hr : (D.gates.get ⟨w - N, h.2.1⟩).right < w then
        insert w (subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).left ∪
                  subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).right)
      else {w}
    else {w}
  else {w}
termination_by w

lemma subWires_unfold_gate (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (j : ℕ) (hj : j < D.gates.length) (hjr : j ∈ region) :
    subWires N D region (N + j) =
      insert (N + j) (subWires N D region (D.gates.get ⟨j, hj⟩).left ∪
                      subWires N D region (D.gates.get ⟨j, hj⟩).right) := by
  conv_lhs => rw [subWires]
  have hcond : N ≤ N + j ∧ (N + j) - N < D.gates.length ∧ (N + j) - N ∈ region :=
    ⟨Nat.le_add_right _ _, by simpa using hj, by simpa using hjr⟩
  have hidx : (⟨(N + j) - N, hcond.2.1⟩ : Fin D.gates.length) = ⟨j, hj⟩ := by
    apply Fin.ext; simp
  have hl : (D.gates.get ⟨(N + j) - N, hcond.2.1⟩).left < N + j := by
    rw [hidx]; exact (hback ⟨j, hj⟩).1
  have hr : (D.gates.get ⟨(N + j) - N, hcond.2.1⟩).right < N + j := by
    rw [hidx]; exact (hback ⟨j, hj⟩).2
  rw [dif_pos hcond, dif_pos hl, dif_pos hr, hidx]

lemma subWires_unfold_leaf (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ)
    (w : ℕ) (hnot : ¬ (N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region)) :
    subWires N D region w = {w} := by
  rw [subWires, dif_neg hnot]

lemma subWires_self (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ) (w : ℕ) :
    w ∈ subWires N D region w := by
  rw [subWires]
  by_cases h : N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region
  · rw [dif_pos h]
    by_cases hl : (D.gates.get ⟨w - N, h.2.1⟩).left < w
    · rw [dif_pos hl]
      by_cases hr : (D.gates.get ⟨w - N, h.2.1⟩).right < w
      · rw [dif_pos hr]; exact Finset.mem_insert_self _ _
      · rw [dif_neg hr]; exact Finset.mem_singleton_self _
    · rw [dif_neg hl]; exact Finset.mem_singleton_self _
  · rw [dif_neg h]; exact Finset.mem_singleton_self _

lemma subWires_le (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ) (w : ℕ) :
    ∀ v ∈ subWires N D region w, v ≤ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [subWires] at hv
    by_cases h : N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region
    · rw [dif_pos h] at hv
      by_cases hl : (D.gates.get ⟨w - N, h.2.1⟩).left < w
      · rw [dif_pos hl] at hv
        by_cases hr : (D.gates.get ⟨w - N, h.2.1⟩).right < w
        · rw [dif_pos hr] at hv
          rcases Finset.mem_insert.mp hv with rfl | hu
          · exact le_rfl
          · rcases Finset.mem_union.mp hu with h1 | h2
            · exact le_trans (ih _ hl _ h1) (Nat.le_of_lt hl)
            · exact le_trans (ih _ hr _ h2) (Nat.le_of_lt hr)
        · rw [dif_neg hr] at hv; rw [Finset.mem_singleton.mp hv]
      · rw [dif_neg hl] at hv; rw [Finset.mem_singleton.mp hv]
    · rw [dif_neg h] at hv; rw [Finset.mem_singleton.mp hv]

lemma subWires_closed (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (w : ℕ) :
    ∀ (k : ℕ) (hk : k < D.gates.length), k ∈ region → N + k ∈ subWires N D region w →
      (D.gates.get ⟨k, hk⟩).left ∈ subWires N D region w ∧
      (D.gates.get ⟨k, hk⟩).right ∈ subWires N D region w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk hkr hmem
    by_cases hcond : N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region
    · have hw_eq : w = N + (w - N) := by omega
      have hsw : subWires N D region w =
          insert w (subWires N D region (D.gates.get ⟨w - N, hcond.2.1⟩).left ∪
                    subWires N D region (D.gates.get ⟨w - N, hcond.2.1⟩).right) := by
        conv_lhs => rw [hw_eq]
        rw [subWires_unfold_gate N D region hback (w - N) hcond.2.1 hcond.2.2, ← hw_eq]
      have hl : (D.gates.get ⟨w - N, hcond.2.1⟩).left < w := by
        have h1 := (hback ⟨w - N, hcond.2.1⟩).1
        change (D.gates.get ⟨w - N, hcond.2.1⟩).left < N + (w - N) at h1
        omega
      have hr : (D.gates.get ⟨w - N, hcond.2.1⟩).right < w := by
        have h2 := (hback ⟨w - N, hcond.2.1⟩).2
        change (D.gates.get ⟨w - N, hcond.2.1⟩).right < N + (w - N) at h2
        omega
      rw [hsw] at hmem ⊢
      rcases Finset.mem_insert.mp hmem with heq | hu
      · have hk_eq : k = w - N := by omega
        subst hk_eq
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (subWires_self _ _ _ _)),
               Finset.mem_insert_of_mem (Finset.mem_union_right _ (subWires_self _ _ _ _))⟩
      · rcases Finset.mem_union.mp hu with h1 | h2
        · obtain ⟨a, b⟩ := ih _ hl k hk hkr h1
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ a),
                 Finset.mem_insert_of_mem (Finset.mem_union_left _ b)⟩
        · obtain ⟨a, b⟩ := ih _ hr k hk hkr h2
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ a),
                 Finset.mem_insert_of_mem (Finset.mem_union_right _ b)⟩
    · rw [subWires_unfold_leaf N D region w hcond] at hmem
      have heq := Finset.mem_singleton.mp hmem
      exfalso
      apply hcond
      rw [← heq]
      exact ⟨Nat.le_add_right _ _, by simpa using hk, by simpa using hkr⟩

lemma subWires_sub (N : ℕ) (D : BinaryCircuit) (S E region : Finset ℕ) (root : ℕ)
    (ht : IsTreeAt N (skel D) S E region root)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (w : ℕ) (hw : w ∈ (S ∪ region.image (fun k => N + k)) ∪ E) :
    subWires N D region w ⊆ (S ∪ region.image (fun k => N + k)) ∪ E := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    by_cases h : N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region
    · have hw_eq : w = N + (w - N) := by omega
      have hsw : subWires N D region w =
          insert w (subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).left ∪
                    subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).right) := by
        conv_lhs => rw [hw_eq]
        rw [subWires_unfold_gate N D region hback (w - N) h.2.1 h.2.2, ← hw_eq]
      have hl : (D.gates.get ⟨w - N, h.2.1⟩).left < w := by
        have h1 := (hback ⟨w - N, h.2.1⟩).1
        change (D.gates.get ⟨w - N, h.2.1⟩).left < N + (w - N) at h1
        omega
      have hr : (D.gates.get ⟨w - N, h.2.1⟩).right < w := by
        have h2 := (hback ⟨w - N, h.2.1⟩).2
        change (D.gates.get ⟨w - N, h.2.1⟩).right < N + (w - N) at h2
        omega
      rw [hsw] at hv
      rcases Finset.mem_insert.mp hv with rfl | hu
      · exact hw
      · have hgate := (ht.2.2.2.2.1 (w - N) h.2.2).2.2
        rw [skel_gateAt D (w - N) h.2.1] at hgate
        have hl_mem : (D.gates.get ⟨w - N, h.2.1⟩).left ∈ (S ∪ region.image (fun k => N + k)) ∪ E := by
          rcases hgate (D.gates.get ⟨w - N, h.2.1⟩).left (by simp) with h1 | h2
          · exact Finset.mem_union_left _ h1
          · exact Finset.mem_union_right _ h2
        have hr_mem : (D.gates.get ⟨w - N, h.2.1⟩).right ∈ (S ∪ region.image (fun k => N + k)) ∪ E := by
          rcases hgate (D.gates.get ⟨w - N, h.2.1⟩).right (by simp) with h1 | h2
          · exact Finset.mem_union_left _ h1
          · exact Finset.mem_union_right _ h2
        rcases Finset.mem_union.mp hu with h1 | h2
        · exact ih _ hl hl_mem h1
        · exact ih _ hr hr_mem h2
    · rw [subWires_unfold_leaf N D region w h] at hv
      rw [Finset.mem_singleton.mp hv]; exact hw

lemma subWires_read (N : ℕ) (D : BinaryCircuit) (region : Finset ℕ)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (w : ℕ) (v : ℕ) (hv : v ∈ subWires N D region w) (hne : v ≠ w) :
    ∃ k ∈ region.filter (fun k => N + k ∈ subWires N D region w),
      v ∈ (gateAt (skel D) k).inputs := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : N ≤ w ∧ w - N < D.gates.length ∧ w - N ∈ region
    · have hw_eq : w = N + (w - N) := by omega
      have hsw : subWires N D region w =
          insert w (subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).left ∪
                    subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).right) := by
        conv_lhs => rw [hw_eq]
        rw [subWires_unfold_gate N D region hback (w - N) h.2.1 h.2.2, ← hw_eq]
      have hl : (D.gates.get ⟨w - N, h.2.1⟩).left < w := by
        have h1 := (hback ⟨w - N, h.2.1⟩).1
        change (D.gates.get ⟨w - N, h.2.1⟩).left < N + (w - N) at h1
        omega
      have hr : (D.gates.get ⟨w - N, h.2.1⟩).right < w := by
        have h2 := (hback ⟨w - N, h.2.1⟩).2
        change (D.gates.get ⟨w - N, h.2.1⟩).right < N + (w - N) at h2
        omega
      have hv' := hv
      rw [hsw] at hv'
      rcases Finset.mem_insert.mp hv' with rfl | hu
      · exact absurd rfl hne
      · have hsub_l : subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).left ⊆ subWires N D region w := by
          intro x hx; rw [hsw]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
        have hsub_r : subWires N D region (D.gates.get ⟨w - N, h.2.1⟩).right ⊆ subWires N D region w := by
          intro x hx; rw [hsw]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
        rcases Finset.mem_union.mp hu with h1 | h2
        · by_cases hvl : v = (D.gates.get ⟨w - N, h.2.1⟩).left
          · refine ⟨w - N, Finset.mem_filter.mpr ⟨h.2.2, by rw [← hw_eq]; exact subWires_self _ _ _ _⟩, ?_⟩
            rw [skel_gateAt D (w - N) h.2.1, hvl]; simp
          · obtain ⟨k, hk, hkin⟩ := ih _ hl h1 hvl
            have hkf := Finset.mem_filter.mp hk
            exact ⟨k, Finset.mem_filter.mpr ⟨hkf.1, hsub_l hkf.2⟩, hkin⟩
        · by_cases hvr : v = (D.gates.get ⟨w - N, h.2.1⟩).right
          · refine ⟨w - N, Finset.mem_filter.mpr ⟨h.2.2, by rw [← hw_eq]; exact subWires_self _ _ _ _⟩, ?_⟩
            rw [skel_gateAt D (w - N) h.2.1, hvr]; simp
          · obtain ⟨k, hk, hkin⟩ := ih _ hr h2 hvr
            have hkf := Finset.mem_filter.mp hk
            exact ⟨k, Finset.mem_filter.mpr ⟨hkf.1, hsub_r hkf.2⟩, hkin⟩
    · rw [subWires_unfold_leaf N D region w h] at hv
      exact absurd (Finset.mem_singleton.mp hv) hne

lemma subWires_top_eq (N : ℕ) (D : BinaryCircuit) (S E region : Finset ℕ) (root : ℕ)
    (ht : IsTreeAt N (skel D) S E region root)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val) :
    subWires N D region root = (S ∪ region.image (fun k => N + k)) ∪ E := by
  apply Finset.Subset.antisymm
  · exact subWires_sub N D S E region root ht hback root (Finset.mem_union_left _ ht.2.1)
  · by_contra hnsub
    have hne : (((S ∪ region.image (fun k => N + k)) ∪ E) \ subWires N D region root).Nonempty :=
      Finset.sdiff_nonempty.mpr hnsub
    set v := (((S ∪ region.image (fun k => N + k)) ∪ E) \ subWires N D region root).max' hne with hv_def
    have hv_mem : v ∈ ((S ∪ region.image (fun k => N + k)) ∪ E) \ subWires N D region root :=
      Finset.max'_mem _ hne
    obtain ⟨hv_in, hv_not⟩ := Finset.mem_sdiff.mp hv_mem
    have hv_ne_root : v ≠ root := by
      intro heq
      rw [heq] at hv_not
      exact hv_not (subWires_self N D region root)
    have hloc1 : readsIn (skel D) region v = 1 := by
      rcases Finset.mem_union.mp hv_in with hw | he
      · exact (ht.2.2.2.2.2 v hw hv_ne_root).1
      · exact (ht.2.2.2.1 v he).2.2
    obtain ⟨k, hkr, hkcnt, _⟩ := S25644.readsIn_eq_one_unique (skel D) region v hloc1
    have hklt : k < D.gates.length := by
      have := Finset.mem_range.mp (ht.1 hkr)
      simpa [skel_size, BinaryCircuit.size] using this
    rw [skel_gateAt D k hklt] at hkcnt
    have hvin : v = (D.gates.get ⟨k, hklt⟩).left ∨ v = (D.gates.get ⟨k, hklt⟩).right := by
      simpa using hkcnt
    have hv_lt : v < N + k := by
      rcases hvin with h1 | h2
      · rw [h1]; exact (hback ⟨k, hklt⟩).1
      · rw [h2]; exact (hback ⟨k, hklt⟩).2
    have hNk_in : N + k ∈ (S ∪ region.image (fun j => N + j)) ∪ E :=
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkr))
    have hNk_sub : N + k ∈ subWires N D region root := by
      by_contra hnot
      have hle := Finset.le_max' _ (N + k) (Finset.mem_sdiff.mpr ⟨hNk_in, hnot⟩)
      omega
    have hcl := subWires_closed N D region hback root k hklt hkr hNk_sub
    rcases hvin with h1 | h2
    · rw [h1] at hv_not; exact hv_not hcl.1
    · rw [h2] at hv_not; exact hv_not hcl.2

lemma root_is_gate (N : ℕ) (D : BinaryCircuit) (S E region : Finset ℕ) (root : ℕ)
    (ht : IsTreeAt N (skel D) S E region root) (hS : S ⊆ Finset.range N)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (hcard : 2 ≤ S.card) :
    ∃ j ∈ region, root = N + j := by
  rcases Finset.mem_union.mp ht.2.1 with hrootS | hrootG
  · exfalso
    have hS_ne : (S.erase root).Nonempty := by
      have hc : 1 ≤ (S.erase root).card := by
        rw [Finset.card_erase_of_mem hrootS]
        omega
      exact Finset.card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hS_ne
    obtain ⟨hwne, hwS⟩ := Finset.mem_erase.mp hw
    have hloc := (ht.2.2.2.2.2 w (Finset.mem_union_left _ hwS) hwne).1
    obtain ⟨k0, hk0r, _, _⟩ := S25644.readsIn_eq_one_unique (skel D) region w hloc
    have hreg_ne : region.Nonempty := ⟨k0, hk0r⟩
    set jmax := region.max' hreg_ne
    have hjmax_r : jmax ∈ region := Finset.max'_mem _ hreg_ne
    have hroot_lt : root < N := Finset.mem_range.mp (hS hrootS)
    have hne_max : N + jmax ≠ root := by omega
    have hloc_max := (ht.2.2.2.2.2 (N + jmax)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hjmax_r)) hne_max).1
    obtain ⟨k1, hk1r, hk1c, _⟩ := S25644.readsIn_eq_one_unique (skel D) region (N + jmax) hloc_max
    have hk1lt : k1 < D.gates.length := by
      have := Finset.mem_range.mp (ht.1 hk1r)
      simpa [skel_size, BinaryCircuit.size] using this
    rw [skel_gateAt D k1 hk1lt] at hk1c
    have hmem : N + jmax ∈ [(D.gates.get ⟨k1, hk1lt⟩).left, (D.gates.get ⟨k1, hk1lt⟩).right] := hk1c
    have hjb := hback ⟨k1, hk1lt⟩
    dsimp at hjb
    have hlt : N + jmax < N + k1 := by
      rcases by simpa using hmem with h1 | h2
      · rw [h1]; exact hjb.1
      · rw [h2]; exact hjb.2
    have hle : k1 ≤ jmax := Finset.le_max' region k1 hk1r
    omega
  · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hrootG
    exact ⟨j, hj, heq.symm⟩

lemma subWires_isTreeAt (N : ℕ) (D : BinaryCircuit) (S E region : Finset ℕ) (root : ℕ)
    (ht : IsTreeAt N (skel D) S E region root) (hS : S ⊆ Finset.range N)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val)
    (ju : ℕ) (hju : ju ∈ region) :
    let u := N + ju
    let S' := (subWires N D region u).filter (· ∈ S)
    let E' := (subWires N D region u).filter (· ∈ E)
    let R' := region.filter (fun k => N + k ∈ subWires N D region u)
    IsTreeAt N (skel D) S' E' R' u := by
  intro u S' E' R'
  have hu_mem : u ∈ S ∪ region.image (fun k => N + k) :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hju)
  have hsub_u : subWires N D region u ⊆ (S ∪ region.image (fun k => N + k)) ∪ E :=
    subWires_sub N D S E region root ht hback u (Finset.mem_union_left _ hu_mem)
  have hR'_sub : R' ⊆ region := Finset.filter_subset _ _
  have hwires_eq : S' ∪ R'.image (fun k => N + k) = (subWires N D region u).filter (· ∉ E) := by
    ext v
    simp only [S', R', Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro (⟨hv, hvS⟩ | ⟨k, ⟨hkr, hvk⟩, rfl⟩)
      · refine ⟨hv, fun hvE => (ht.2.2.2.1 v hvE).1 (Finset.mem_union_left _ hvS)⟩
      · refine ⟨hvk, fun hvE => (ht.2.2.2.1 (N + k) hvE).1
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkr))⟩
    · rintro ⟨hv, hvE⟩
      rcases Finset.mem_union.mp (hsub_u hv) with hw | he
      · rcases Finset.mem_union.mp hw with hvS | hvG
        · exact Or.inl ⟨hv, hvS⟩
        · obtain ⟨k, hkr, rfl⟩ := Finset.mem_image.mp hvG
          exact Or.inr ⟨k, ⟨hkr, hv⟩, rfl⟩
      · exact absurd he hvE
  have hu_le_root : u ≤ root := by
    have hru := subWires_top_eq N D S E region root ht hback
    have hu_in_root : u ∈ subWires N D region root := by
      rw [hru]; exact Finset.mem_union_left _ hu_mem
    exact subWires_le N D region root u hu_in_root
  refine ⟨hR'_sub.trans ht.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨hju, subWires_self _ _ _ _⟩))
  · apply (S25644.readsIn_eq_zero_iff (skel D) R' u).mpr
    intro k hk
    obtain ⟨hkr, hNk⟩ := Finset.mem_filter.mp hk
    have hklt : k < D.gates.length := by
      have := Finset.mem_range.mp (ht.1 hkr)
      simpa [skel_size, BinaryCircuit.size] using this
    have hle : N + k ≤ u := subWires_le N D region u (N + k) hNk
    rw [skel_gateAt D k hklt]
    have hjb := hback ⟨k, hklt⟩
    change (D.gates.get ⟨k, hklt⟩).left < N + k ∧ (D.gates.get ⟨k, hklt⟩).right < N + k at hjb
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by omega, by omega⟩
  · intro b hb
    obtain ⟨hb_sw, hbE⟩ := Finset.mem_filter.mp hb
    have hbe := ht.2.2.2.1 b hbE
    have hb_ne : b ≠ u := fun heq => hbe.1 (heq ▸ hu_mem)
    have hb_le : b ≤ u := subWires_le N D region u b hb_sw
    refine ⟨?_, by omega, ?_⟩
    · rw [hwires_eq]; simp [hbE]
    · obtain ⟨k, hk, hkin⟩ := subWires_read N D region hback u b hb_sw hb_ne
      have hge : 1 ≤ readsIn (skel D) R' b := by
        have h1 : 1 ≤ (gateAt (skel D) k).inputs.count b := List.count_pos_iff.mpr hkin
        have h2 := Finset.single_le_sum (f := fun j => (gateAt (skel D) j).inputs.count b)
          (fun _ _ => Nat.zero_le _) hk
        change (gateAt (skel D) k).inputs.count b ≤ readsIn (skel D) R' b at h2
        omega
      have hle' : readsIn (skel D) R' b ≤ readsIn (skel D) region b :=
        S25644.readsIn_mono (skel D) hR'_sub b
      omega
  · intro k hk
    obtain ⟨hkr, hNk⟩ := Finset.mem_filter.mp hk
    have hklt : k < D.gates.length := by
      have := Finset.mem_range.mp (ht.1 hkr)
      simpa [skel_size, BinaryCircuit.size] using this
    have hkg := ht.2.2.2.2.1 k hkr
    refine ⟨hkg.1, hkg.2.1, ?_⟩
    intro v hv
    rw [skel_gateAt D k hklt] at hv
    have hcl := subWires_closed N D region hback u k hklt hkr hNk
    have hv_sw : v ∈ subWires N D region u := by
      rcases by simpa using hv with rfl | rfl
      · exact hcl.1
      · exact hcl.2
    by_cases hvE : v ∈ E
    · exact Or.inr (Finset.mem_filter.mpr ⟨hv_sw, hvE⟩)
    · left; rw [hwires_eq]; exact Finset.mem_filter.mpr ⟨hv_sw, hvE⟩
  · intro v hv hvne
    rw [hwires_eq] at hv
    obtain ⟨hv_sw, hvE⟩ := Finset.mem_filter.mp hv
    have hv_w : v ∈ S ∪ region.image (fun k => N + k) := by
      rcases Finset.mem_union.mp (hsub_u hv_sw) with h1 | h2
      · exact h1
      · exact absurd h2 hvE
    have hv_lt_u : v < u := lt_of_le_of_ne (subWires_le N D region u v hv_sw) hvne
    have hv_ne_root : v ≠ root := by omega
    have hbig := ht.2.2.2.2.2 v hv_w hv_ne_root
    obtain ⟨k, hk, hkin⟩ := subWires_read N D region hback u v hv_sw hvne
    have hge : 1 ≤ readsIn (skel D) R' v := by
      have h1 : 1 ≤ (gateAt (skel D) k).inputs.count v := List.count_pos_iff.mpr hkin
      have h2 := Finset.single_le_sum (f := fun j => (gateAt (skel D) j).inputs.count v)
        (fun _ _ => Nat.zero_le _) hk
      change (gateAt (skel D) k).inputs.count v ≤ readsIn (skel D) R' v at h2
      omega
    have hle' : readsIn (skel D) R' v ≤ readsIn (skel D) region v :=
      S25644.readsIn_mono (skel D) hR'_sub v
    exact ⟨by omega, hbig.2.1, hbig.2.2⟩

lemma apply_25872 {n m : ℕ} (D : BinaryCircuit) (G : Fin n → Fin m → Bool)
    (hev : ∀ u v, D.eval (PEqualNP.Represents.oneEach u v) = G u v)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val)
    (hout : D.output + 1 = (n + m) + D.size) (hpos : 0 < D.size)
    (S E region : Finset ℕ) (jroot : ℕ)
    (hS : S ⊆ Finset.range (n + m))
    (hjroot : jroot ∈ region)
    (ht : IsTreeAt (n + m) (skel D) S E region ((n + m) + jroot)) :
    let R := bankR n S
    let B := bankC n m S
    let rowOff := fun j : Fin m => List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))
    let colOff := fun i : Fin n => List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false
    (∃ (mask : Fin m → Bool) (response : Fin n → (↥E → Bool) → Bool),
      ∀ i ∈ R, ∀ j ∉ B,
        (G i j != D.eval (rowOff j)) =
        (mask j && response i (fun e => (D.wires (rowOff j)).getD e.val false))) ∧
    (∃ (mask : Fin n → Bool) (response : Fin m → (↥E → Bool) → Bool),
      ∀ j ∈ B, ∀ i ∉ R,
        (G i j != D.eval (colOff i)) =
        (mask i && response j (fun e => (D.wires (colOff i)).getD e.val false))) := by
  intro R B rowOff colOff
  have hsrc : R.image (fun i : Fin n => i.val) ∪ B.image (fun j : Fin m => n + j.val) = S :=
    bankR_image_union_bankC_image n m S hS
  have hreg : region ⊆ Finset.range D.size := by
    simpa [skel_size] using ht.1
  have hentry : ∀ e ∈ E, e < (n + m) + jroot ∧ e ∉ S ∧ ¬(n + m ≤ e ∧ e - (n + m) ∈ region) := by
    intro e he
    have hbe := ht.2.2.2.1 e he
    refine ⟨hbe.2.1, fun h1 => hbe.1 (Finset.mem_union_left _ h1), ?_⟩
    rintro ⟨hle, hmem⟩
    apply hbe.1
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e - (n + m), hmem, by omega⟩)
  have hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < (n + m) + g.val ∧
        (g.val ∈ region → w ∈ S ∨ (n + m ≤ w ∧ w - (n + m) ∈ region) ∨ w ∈ E) ∧
        (g.val ∉ region → w ∉ S ∧ ((n + m ≤ w ∧ w - (n + m) ∈ region) → w = (n + m) + jroot)) := by
    intro g node w hw
    have hw' : w = (D.gates.get g).left ∨ w = (D.gates.get g).right := by
      simpa [node] using hw
    have hlt : w < (n + m) + g.val := by
      rcases hw' with rfl | rfl
      · exact (hback g).1
      · exact (hback g).2
    refine ⟨hlt, ?_, ?_⟩
    · intro hgr
      have hgm := (ht.2.2.2.2.1 g.val hgr).2.2 w (by
        rw [skel_gateAt D g.val g.isLt]
        simpa [List.get_eq_getElem] using hw')
      rcases hgm with hwires | hE
      · rcases Finset.mem_union.mp hwires with h1 | h2
        · exact Or.inl h1
        · obtain ⟨k, hkr, rfl⟩ := Finset.mem_image.mp h2
          exact Or.inr (Or.inl ⟨Nat.le_add_right _ _, by simpa using hkr⟩)
      · exact Or.inr (Or.inr hE)
    · intro hgnr
      have hcnt : 1 ≤ (gateAt (skel D) g.val).inputs.count w := by
        rw [skel_gateAt D g.val g.isLt]
        exact List.count_pos_iff.mpr (by simpa [List.get_eq_getElem] using hw')
      have hout_no : ∀ v ∈ S ∪ region.image (fun k => (n + m) + k), v ≠ (n + m) + jroot →
          (gateAt (skel D) g.val).inputs.count v = 0 := by
        intro v hv hvne
        have hvv := ht.2.2.2.2.2 v hv hvne
        have hsub : insert g.val region ⊆ Finset.range (skel D).size := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | h2
          · rw [skel_size]; exact Finset.mem_range.mpr g.isLt
          · exact ht.1 h2
        have hle := S25644.readsIn_mono (skel D) hsub v
        rw [S25644.readsIn_insert (skel D) region g.val v hgnr] at hle
        omega
      constructor
      · intro hwS
        have hne : w ≠ (n + m) + jroot := by
          have := Finset.mem_range.mp (hS hwS); omega
        have := hout_no w (Finset.mem_union_left _ hwS) hne
        omega
      · rintro ⟨hle, hmr⟩
        by_contra hne
        have hwG : w ∈ region.image (fun k => (n + m) + k) :=
          Finset.mem_image.mpr ⟨w - (n + m), hmr, by omega⟩
        have := hout_no w (Finset.mem_union_right _ hwG) hne
        omega
  have hout_ns : D.output ∉ S := by
    intro hmem
    have := Finset.mem_range.mp (hS hmem)
    omega
  have hout_in : (n + m ≤ D.output ∧ D.output - (n + m) ∈ region) → D.output = (n + m) + jroot := by
    rintro ⟨hle, hmr⟩
    by_contra hne
    have hmem : D.output ∈ S ∪ region.image (fun k => (n + m) + k) :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D.output - (n + m), hmr, by omega⟩)
    exact (ht.2.2.2.2.2 D.output hmem hne).2.2 rfl
  have hres := S25872.thm n m D R B region E jroot hreg hjroot
    (by simpa only [hsrc] using hentry)
    (by simpa only [hsrc] using hgates)
    (by simpa only [hsrc] using hout_ns) hout_in
  have hev' : ∀ (i : Fin n) (j : Fin m),
      D.eval (List.ofFn (fun v : Fin n => decide (v = i)) ++ List.ofFn (fun v : Fin m => decide (v = j))) = G i j := hev
  rcases hres with ⟨⟨mR, rR, hR⟩, ⟨mC, rC, hC⟩⟩
  refine ⟨⟨mR, rR, ?_⟩, ⟨mC, rC, ?_⟩⟩
  · intro i hi j hj
    have h := hR i hi j hj
    dsimp only at h
    rw [hev' i j] at h
    exact h
  · intro j hj i hi
    have h := hC j hj i hi
    dsimp only at h
    rw [hev' i j] at h
    exact h

lemma tree_cap {n m : ℕ} (D : BinaryCircuit) (G : Fin n → Fin m → Bool)
    (hev : ∀ u v, D.eval (PEqualNP.Represents.oneEach u v) = G u v)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val)
    (hout : D.output + 1 = (n + m) + D.size) (hpos : 0 < D.size)
    (hrichG : Rich n m G) (hrichT : Rich m n (fun j i => G i j))
    (k : ℕ) :
    ∀ (S E region : Finset ℕ) (root : ℕ),
      region.card ≤ k → S ⊆ Finset.range (n + m) → E.card ≤ 1 →
      IsTreeAt (n + m) (skel D) S E region root →
      (bankR n S).card ≤ 2 ∧ (bankC n m S).card ≤ 2 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro S E region root hrc hS hE ht
    by_contra hbig
    have h3 : 3 ≤ (bankR n S).card ∨ 3 ≤ (bankC n m S).card := by
      rcases not_and_or.mp hbig with h1 | h2
      · left; omega
      · right; omega
    have hS2 : 2 ≤ S.card := by
      have := card_eq_bankR_add_bankC n m S hS
      omega
    obtain ⟨jroot, hjroot, rfl⟩ := root_is_gate (n + m) D S E region root ht hS hback hS2
    have hjlt : jroot < D.gates.length := by
      have := Finset.mem_range.mp (ht.1 hjroot)
      simpa [skel_size, BinaryCircuit.size] using this
    set l := (D.gates.get ⟨jroot, hjlt⟩).left
    set r := (D.gates.get ⟨jroot, hjlt⟩).right
    have hjb := hback ⟨jroot, hjlt⟩
    have hl_lt : l < (n + m) + jroot := hjb.1
    have hr_lt : r < (n + m) + jroot := hjb.2
    have hroot_sw : subWires (n + m) D region ((n + m) + jroot) =
        insert ((n + m) + jroot) (subWires (n + m) D region l ∪ subWires (n + m) D region r) :=
      subWires_unfold_gate (n + m) D region hback jroot hjlt hjroot
    have hroot_eq := subWires_top_eq (n + m) D S E region ((n + m) + jroot) ht hback
    have hS_sub_lr : S ⊆ subWires (n + m) D region l ∪ subWires (n + m) D region r := by
      intro w hw
      have h1 : w ∈ subWires (n + m) D region ((n + m) + jroot) := by
        rw [hroot_eq]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      rw [hroot_sw] at h1
      rcases Finset.mem_insert.mp h1 with rfl | h2
      · have := Finset.mem_range.mp (hS hw); omega
      · exact h2
    have child_bound : ∀ c : ℕ, c < (n + m) + jroot →
        c ∈ (S ∪ region.image (fun j => (n + m) + j)) ∪ E →
        (bankR n ((subWires (n + m) D region c).filter (· ∈ S))).card ≤ 2 ∧
        (bankC n m ((subWires (n + m) D region c).filter (· ∈ S))).card ≤ 2 := by
      intro c hclt hc_in
      set Sc := (subWires (n + m) D region c).filter (· ∈ S)
      set Ec := (subWires (n + m) D region c).filter (· ∈ E)
      set Rc := region.filter (fun j => (n + m) + j ∈ subWires (n + m) D region c)
      by_cases hcg : ∃ jc ∈ region, c = (n + m) + jc
      · obtain ⟨jc, hjc, rfl⟩ := hcg
        have hRc_ssub : Rc ⊂ region := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro heq
          have hj_in : jroot ∈ Rc := heq.symm ▸ hjroot
          have hle := subWires_le (n + m) D region ((n + m) + jc) ((n + m) + jroot)
            (Finset.mem_filter.mp hj_in).2
          omega
        have hRc_lt : Rc.card < k := lt_of_lt_of_le (Finset.card_lt_card hRc_ssub) hrc
        have hSc_sub : Sc ⊆ Finset.range (n + m) := fun w hw => hS (Finset.mem_filter.mp hw).2
        have hEc_le : Ec.card ≤ 1 := le_trans (Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)) hE
        exact ih Rc.card hRc_lt Sc Ec Rc ((n + m) + jc) le_rfl hSc_sub hEc_le
          (subWires_isTreeAt (n + m) D S E region ((n + m) + jroot) ht hS hback jc hjc)
      · have hsw_c : subWires (n + m) D region c = {c} := by
          apply subWires_unfold_leaf
          rintro ⟨hle, _, hmem⟩
          exact hcg ⟨c - (n + m), hmem, by omega⟩
        have hSc_le1 : Sc.card ≤ 1 := by
          have : Sc ⊆ {c} := by rw [← hsw_c]; exact Finset.filter_subset _ _
          exact le_trans (Finset.card_le_card this) (by simp)
        have hSc_sub : Sc ⊆ Finset.range (n + m) := fun w hw => hS (Finset.mem_filter.mp hw).2
        have heq := card_eq_bankR_add_bankC n m Sc hSc_sub
        omega
    have hgate := (ht.2.2.2.2.1 jroot hjroot).2.2
    rw [skel_gateAt D jroot hjlt] at hgate
    have hl_in : l ∈ (S ∪ region.image (fun j => (n + m) + j)) ∪ E := by
      rcases hgate l (by simp [l]) with h1 | h2
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ h2
    have hr_in : r ∈ (S ∪ region.image (fun j => (n + m) + j)) ∪ E := by
      rcases hgate r (by simp [r]) with h1 | h2
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ h2
    have hbl := child_bound l hl_lt hl_in
    have hbr := child_bound r hr_lt hr_in
    have hR_le4 : (bankR n S).card ≤ 4 := by
      have hsub : bankR n S ⊆ bankR n ((subWires (n + m) D region l).filter (· ∈ S)) ∪
          bankR n ((subWires (n + m) D region r).filter (· ∈ S)) := by
        intro i hi
        have hiS : i.val ∈ S := (Finset.mem_filter.mp hi).2
        rcases Finset.mem_union.mp (hS_sub_lr hiS) with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨h1, hiS⟩⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨h2, hiS⟩⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    have hC_le4 : (bankC n m S).card ≤ 4 := by
      have hsub : bankC n m S ⊆ bankC n m ((subWires (n + m) D region l).filter (· ∈ S)) ∪
          bankC n m ((subWires (n + m) D region r).filter (· ∈ S)) := by
        intro j hj
        have hjS : n + j.val ∈ S := (Finset.mem_filter.mp hj).2
        rcases Finset.mem_union.mp (hS_sub_lr hjS) with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨h1, hjS⟩⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨h2, hjS⟩⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    obtain ⟨⟨maskR, respR, hfacR⟩, ⟨maskC, respC, hfacC⟩⟩ :=
      apply_25872 D G hev hback hout hpos S E region jroot hS hjroot ht
    obtain ⟨fE, gE, hfg⟩ := collapse_card_le_one hE
    rcases h3 with hR3 | hC3
    · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < (bankR n S).card)
      obtain ⟨x, y, hxy, hmiss⟩ := three_funcs_miss
        (fun t => respR a (gE t)) (fun t => respR b (gE t)) (fun t => respR c (gE t))
      have hsub : (Finset.univ.filter (fun col : Fin m =>
          (G b col != G a col) = x ∧ (G c col != G a col) = y)) ⊆ bankC n m S := by
        intro col hcol
        by_contra hnot
        have hcol' := (Finset.mem_filter.mp hcol).2
        let rowOff := fun j : Fin m => List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))
        let ent : ↥E → Bool := fun e => (D.wires (rowOff col)).getD e.val false
        have hfa : (G a col != D.eval (rowOff col)) = (maskR col && respR a ent) := hfacR a ha col hnot
        have hfb : (G b col != D.eval (rowOff col)) = (maskR col && respR b ent) := hfacR b hb col hnot
        have hfc : (G c col != D.eval (rowOff col)) = (maskR col && respR c ent) := hfacR c hc col hnot
        rw [← hfg ent] at hfa hfb hfc
        have hba : (G b col != G a col) = ((G b col != D.eval (rowOff col)) != (G a col != D.eval (rowOff col))) := by
          generalize G b col = u1, G a col = u2, D.eval (rowOff col) = u3
          revert u1 u2 u3; decide
        have hca : (G c col != G a col) = ((G c col != D.eval (rowOff col)) != (G a col != D.eval (rowOff col))) := by
          generalize G c col = u1, G a col = u2, D.eval (rowOff col) = u3
          revert u1 u2 u3; decide
        rw [hba, hfa, hfb] at hcol'
        rw [hca, hfa, hfc] at hcol'
        exact hmiss (maskR col) (fE ent) hcol'
      have h5 := hrichG a b c hab hac hbc x y hxy
      have hle := Finset.card_le_card hsub
      omega
    · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < (bankC n m S).card)
      obtain ⟨x, y, hxy, hmiss⟩ := three_funcs_miss
        (fun t => respC a (gE t)) (fun t => respC b (gE t)) (fun t => respC c (gE t))
      have hsub : (Finset.univ.filter (fun row : Fin n =>
          (G row b != G row a) = x ∧ (G row c != G row a) = y)) ⊆ bankR n S := by
        intro row hrow
        by_contra hnot
        have hrow' := (Finset.mem_filter.mp hrow).2
        let colOff := fun i : Fin n => List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false
        let ent : ↥E → Bool := fun e => (D.wires (colOff row)).getD e.val false
        have hfa : (G row a != D.eval (colOff row)) = (maskC row && respC a ent) := hfacC a ha row hnot
        have hfb : (G row b != D.eval (colOff row)) = (maskC row && respC b ent) := hfacC b hb row hnot
        have hfc : (G row c != D.eval (colOff row)) = (maskC row && respC c ent) := hfacC c hc row hnot
        rw [← hfg ent] at hfa hfb hfc
        have hba : (G row b != G row a) = ((G row b != D.eval (colOff row)) != (G row a != D.eval (colOff row))) := by
          generalize G row b = u1, G row a = u2, D.eval (colOff row) = u3
          revert u1 u2 u3; decide
        have hca : (G row c != G row a) = ((G row c != D.eval (colOff row)) != (G row a != D.eval (colOff row))) := by
          generalize G row c = u1, G row a = u2, D.eval (colOff row) = u3
          revert u1 u2 u3; decide
        rw [hba, hfa, hfb] at hrow'
        rw [hca, hfa, hfc] at hrow'
        exact hmiss (maskC row) (fE ent) hrow'
      have h5 := hrichT a b c hab hac hbc x y hxy
      dsimp only at h5
      have hle := Finset.card_le_card hsub
      omega

lemma pair_affordable_row {n m : ℕ} (D : BinaryCircuit) (G : Fin n → Fin m → Bool)
    (hev : ∀ u v, D.eval (PEqualNP.Represents.oneEach u v) = G u v)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val)
    (hout : D.output + 1 = (n + m) + D.size) (hpos : 0 < D.size)
    (S E region : Finset ℕ) (root : ℕ)
    (hS : S ⊆ Finset.range (n + m)) (hE : E.card ≤ 1)
    (ht : IsTreeAt (n + m) (skel D) S E region root)
    (hR2 : (bankR n S).card = 2) (hC2 : (bankC n m S).card ≤ 2) :
    let off := fun j : Fin m => D.eval (List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j)))
    ∃ e : Fin n × Fin n, e.1 ∈ bankR n S ∧ e.2 ∈ bankR n S ∧ e.1 ≠ e.2 ∧
      ∃ side : Bool,
        (Finset.univ.filter (fun col : Fin m =>
          (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ off col)).card ≤ 2 := by
  intro off
  have hS2 : 2 ≤ S.card := by
    have := card_eq_bankR_add_bankC n m S hS
    omega
  obtain ⟨jroot, hjroot, rfl⟩ := root_is_gate (n + m) D S E region root ht hS hback hS2
  obtain ⟨⟨maskR, respR, hfacR⟩, _⟩ :=
    apply_25872 D G hev hback hout hpos S E region jroot hS hjroot ht
  obtain ⟨fE, gE, hfg⟩ := collapse_card_le_one hE
  obtain ⟨a, b, hab, hRab⟩ := Finset.card_eq_two.mp hR2
  have ha : a ∈ bankR n S := hRab ▸ Finset.mem_insert_self a {b}
  have hb : b ∈ bankR n S := hRab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  rcases two_funcs_affordable (fun t => respR a (gE t)) (fun t => respR b (gE t)) with ⟨side, hbad⟩ | ⟨side, hbad⟩
  · refine ⟨(a, b), ha, hb, hab, side, ?_⟩
    have hsub : (Finset.univ.filter (fun col : Fin m =>
        (G a col != G b col) = side ∧ G a col ≠ off col)) ⊆ bankC n m S := by
      intro col hcol
      by_contra hnot
      let rowOff := fun j : Fin m => List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))
      let ent : ↥E → Bool := fun e => (D.wires (rowOff col)).getD e.val false
      have hfa : (G a col != off col) = (maskR col && respR a ent) := hfacR a ha col hnot
      have hfb : (G b col != off col) = (maskR col && respR b ent) := hfacR b hb col hnot
      rw [← hfg ent] at hfa hfb
      exact hbad (maskR col) (fE ent) (G a col) (G b col) (off col) hfa hfb (Finset.mem_filter.mp hcol).2
    exact (Finset.card_le_card hsub).trans hC2
  · refine ⟨(b, a), hb, ha, Ne.symm hab, side, ?_⟩
    have hsub : (Finset.univ.filter (fun col : Fin m =>
        (G b col != G a col) = side ∧ G b col ≠ off col)) ⊆ bankC n m S := by
      intro col hcol
      by_contra hnot
      let rowOff := fun j : Fin m => List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))
      let ent : ↥E → Bool := fun e => (D.wires (rowOff col)).getD e.val false
      have hfa : (G a col != off col) = (maskR col && respR a ent) := hfacR a ha col hnot
      have hfb : (G b col != off col) = (maskR col && respR b ent) := hfacR b hb col hnot
      rw [← hfg ent] at hfa hfb
      exact hbad (maskR col) (fE ent) (G a col) (G b col) (off col) hfa hfb (Finset.mem_filter.mp hcol).2
    exact (Finset.card_le_card hsub).trans hC2

lemma pair_affordable_col {n m : ℕ} (D : BinaryCircuit) (G : Fin n → Fin m → Bool)
    (hev : ∀ u v, D.eval (PEqualNP.Represents.oneEach u v) = G u v)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val)
    (hout : D.output + 1 = (n + m) + D.size) (hpos : 0 < D.size)
    (S E region : Finset ℕ) (root : ℕ)
    (hS : S ⊆ Finset.range (n + m)) (hE : E.card ≤ 1)
    (ht : IsTreeAt (n + m) (skel D) S E region root)
    (hC2 : (bankC n m S).card = 2) (hR2 : (bankR n S).card ≤ 2) :
    let off := fun i : Fin n => D.eval (List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false)
    ∃ e : Fin m × Fin m, e.1 ∈ bankC n m S ∧ e.2 ∈ bankC n m S ∧ e.1 ≠ e.2 ∧
      ∃ side : Bool,
        (Finset.univ.filter (fun row : Fin n =>
          (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ off row)).card ≤ 2 := by
  intro off
  have hS2 : 2 ≤ S.card := by
    have := card_eq_bankR_add_bankC n m S hS
    omega
  obtain ⟨jroot, hjroot, rfl⟩ := root_is_gate (n + m) D S E region root ht hS hback hS2
  obtain ⟨_, ⟨maskC, respC, hfacC⟩⟩ :=
    apply_25872 D G hev hback hout hpos S E region jroot hS hjroot ht
  obtain ⟨fE, gE, hfg⟩ := collapse_card_le_one hE
  obtain ⟨a, b, hab, hCab⟩ := Finset.card_eq_two.mp hC2
  have ha : a ∈ bankC n m S := hCab ▸ Finset.mem_insert_self a {b}
  have hb : b ∈ bankC n m S := hCab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  rcases two_funcs_affordable (fun t => respC a (gE t)) (fun t => respC b (gE t)) with ⟨side, hbad⟩ | ⟨side, hbad⟩
  · refine ⟨(a, b), ha, hb, hab, side, ?_⟩
    have hsub : (Finset.univ.filter (fun row : Fin n =>
        (G row a != G row b) = side ∧ G row a ≠ off row)) ⊆ bankR n S := by
      intro row hrow
      by_contra hnot
      let colOff := fun i : Fin n => List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false
      let ent : ↥E → Bool := fun e => (D.wires (colOff row)).getD e.val false
      have hfa : (G row a != off row) = (maskC row && respC a ent) := hfacC a ha row hnot
      have hfb : (G row b != off row) = (maskC row && respC b ent) := hfacC b hb row hnot
      rw [← hfg ent] at hfa hfb
      exact hbad (maskC row) (fE ent) (G row a) (G row b) (off row) hfa hfb (Finset.mem_filter.mp hrow).2
    exact (Finset.card_le_card hsub).trans hR2
  · refine ⟨(b, a), hb, ha, Ne.symm hab, side, ?_⟩
    have hsub : (Finset.univ.filter (fun row : Fin n =>
        (G row b != G row a) = side ∧ G row b ≠ off row)) ⊆ bankR n S := by
      intro row hrow
      by_contra hnot
      let colOff := fun i : Fin n => List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false
      let ent : ↥E → Bool := fun e => (D.wires (colOff row)).getD e.val false
      have hfa : (G row a != off row) = (maskC row && respC a ent) := hfacC a ha row hnot
      have hfb : (G row b != off row) = (maskC row && respC b ent) := hfacC b hb row hnot
      rw [← hfg ent] at hfa hfb
      exact hbad (maskC row) (fE ent) (G row a) (G row b) (off row) hfa hfb (Finset.mem_filter.mp hrow).2
    exact (Finset.card_le_card hsub).trans hR2

lemma unread_forbids_affordable {v w : ℕ} {T : Fin v → Fin w → Bool}
    (hr : Rich v w T) (off : Fin w → Bool)
    (u0 a b : Fin v) (hu0 : ∀ col, T u0 col = off col)
    (hua : u0 ≠ a) (hub : u0 ≠ b) (hab : a ≠ b) (side : Bool) :
    ¬ ((Finset.univ.filter (fun col : Fin w =>
        (T a col != T b col) = side ∧ T a col ≠ off col)).card ≤ 2) := by
  intro hle
  have hsub : (Finset.univ.filter (fun col : Fin w =>
      (T a col != T u0 col) = true ∧ (T b col != T u0 col) = !side)) ⊆
      (Finset.univ.filter (fun col : Fin w =>
        (T a col != T b col) = side ∧ T a col ≠ off col)) := by
    intro col hcol
    have hc := (Finset.mem_filter.mp hcol).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hu0 col]
    have hbool : ∀ g0 g1 g2 s : Bool,
        ((g1 != g0) = true ∧ (g2 != g0) = !s) → ((g1 != g2) = s ∧ g1 ≠ g0) := by
      decide
    exact hbool (T u0 col) (T a col) (T b col) side hc
  have h5 := hr u0 a b hua hub hab true (!side) (Or.inl rfl)
  have hc := Finset.card_le_card hsub
  omega

lemma sum_reads_skel (N : ℕ) (D : BinaryCircuit)
    (hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < N + j.val ∧ (D.gates.get j).right < N + j.val) :
    ∑ w ∈ Finset.range (N + D.size), readsIn (skel D) (Finset.range D.size) w = 2 * D.size := by
  unfold readsIn
  rw [Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range D.size,
      ∑ w ∈ Finset.range (N + D.size), (gateAt (skel D) j).inputs.count w = 2 := by
    intro j hj
    have hjlt : j < D.gates.length := Finset.mem_range.mp hj
    rw [skel_gateAt D j hjlt]
    have hjb := hback ⟨j, hjlt⟩
    set a := (D.gates.get ⟨j, hjlt⟩).left
    set b := (D.gates.get ⟨j, hjlt⟩).right
    have ha : a ∈ Finset.range (N + D.size) := Finset.mem_range.mpr (by
      have := hjb.1; simp [BinaryCircuit.size] at *; omega)
    have hb : b ∈ Finset.range (N + D.size) := Finset.mem_range.mpr (by
      have := hjb.2; simp [BinaryCircuit.size] at *; omega)
    have hpt : ∀ w ∈ Finset.range (N + D.size),
        ([a, b] : List ℕ).count w = (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
      intro w _
      simp only [List.count_cons, List.count_nil, Nat.zero_add, beq_iff_eq]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos ha, if_pos hb]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

lemma final_arith (n m B ur uc used once_cnt u P d markedReads pureLen chainLen Llen e pr pc hr hc : ℕ)
    (hnm : n + m = ur + uc + used)
    (hused : used = once_cnt + u)
    (hbud : used + d ≤ B + 1)
    (hsh : u + P ≤ d)
    (hmr : markedReads = d + u + P)
    (hpure : pureLen + e ≤ P + 1)
    (hchain : chainLen + e ≤ 2 * markedReads)
    (hL : Llen = pureLen + chainLen)
    (he : 1 ≤ e)
    (honce : once_cnt ≤ 2 * Llen + pr + pc)
    (hur1 : ur ≤ 1) (huc1 : uc ≤ 1)
    (hur0 : 0 < ur → pr = 0 ∧ 1 ≤ hr)
    (huc0 : 0 < uc → pc = 0 ∧ 1 ≤ hc)
    (hpr : pr ≤ hr) (hpc : pc ≤ hc) :
    11 * (n + m) ≤ 10 * B + 26 + 2 * (hr + hc) := by
  by_cases hu : ur = 0 <;> by_cases hv : uc = 0
  · omega
  · have := huc0 (by omega); omega
  · have := hur0 (by omega); omega
  · have := hur0 (by omega); have := huc0 (by omega); omega

lemma solve (n m hr hc : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hrichG : Rich n m G) (hrichT : Rich m n (fun j i => G i j))
    (hbddG : Bounded n m G hr) (hbddT : Bounded m n (fun j i => G i j) hc)
    (hdeg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrep : PEqualNP.Represents.Represents G C) :
    11 * (n + m) ≤ 10 * (C.gates.countP (fun g => g.inputs.length == 2)) + 26 + 2 * (hr + hc) := by
  classical
  have hnorm := S25873.thm (n + m) C hdeg
  dsimp only at hnorm
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by
    have := congrArg Fin.val h; simp at this
  rcases hnorm with ⟨b, hb⟩ | ⟨idx, flip, hidx⟩ | ⟨D, hDpos, hDsize, hDout, hDgates, hDeval⟩
  · exfalso
    obtain ⟨j, hj⟩ := rich_sep hn hrichG ⟨0, by omega⟩ ⟨1, by omega⟩ h01
    have h1 := hb (oneEachFn ⟨0, by omega⟩ j)
    have h2 := hb (oneEachFn ⟨1, by omega⟩ j)
    rw [ofFn_oneEachFn, hrep] at h1 h2
    exact hj (h1.trans h2.symm)
  · exfalso
    by_cases hi : idx.val < n
    · have h2 : 2 ≤ ((Finset.univ : Finset (Fin n)).erase ⟨idx.val, hi⟩).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
        omega
      obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < ((Finset.univ : Finset (Fin n)).erase ⟨idx.val, hi⟩).card)
      have hane : idx.val ≠ a.val := fun eq => (Finset.mem_erase.mp ha).1 (Fin.ext eq.symm)
      have hbne : idx.val ≠ b.val := fun eq => (Finset.mem_erase.mp hb).1 (Fin.ext eq.symm)
      obtain ⟨j, hj⟩ := rich_sep hn hrichG a b hab
      have h1 := hidx (oneEachFn a j)
      have h2' := hidx (oneEachFn b j)
      rw [ofFn_oneEachFn, hrep] at h1 h2'
      simp only [oneEachFn, hi, ↓reduceIte, hane, hbne, decide_false] at h1 h2'
      exact hj (h1.trans h2'.symm)
    · obtain ⟨j, hj⟩ := rich_sep hn hrichG ⟨0, by omega⟩ ⟨1, by omega⟩ h01
      have h1 := hidx (oneEachFn ⟨0, by omega⟩ j)
      have h2 := hidx (oneEachFn ⟨1, by omega⟩ j)
      rw [ofFn_oneEachFn, hrep] at h1 h2
      simp only [oneEachFn, hi, ↓reduceIte] at h1 h2
      exact hj (h1.trans h2.symm)
  · have hDrep : ∀ u v, D.eval (PEqualNP.Represents.oneEach u v) = G u v := by
      intro u v
      have := hDeval (oneEachFn u v)
      rw [ofFn_oneEachFn, hrep] at this
      exact this
    have hback : ∀ j : Fin D.gates.length, (D.gates.get j).left < (n + m) + j.val ∧ (D.gates.get j).right < (n + m) + j.val :=
      fun j => ⟨(hDgates j).1, (hDgates j).2.1⟩
    set Csk := skel D with hCsk_def
    have hCsk_sz : Csk.size = D.size := skel_size D
    set r := readsIn Csk (Finset.range Csk.size) with hr_def
    have hshape : ∀ g ∈ Csk.gates,
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1) := by
      intro g hg
      obtain ⟨bg, _, rfl⟩ := List.mem_map.mp hg
      exact Or.inl ⟨Or.inl rfl, rfl⟩
    have hrb : ReadsBack (n + m) Csk := by
      intro j hj w hw
      have hjlt : j < D.gates.length := by simpa [Csk, skel] using hj
      rw [skel_gateAt D j hjlt] at hw
      rcases by simpa using hw with rfl | rfl
      · exact (hback ⟨j, hjlt⟩).1
      · exact (hback ⟨j, hjlt⟩).2
    have hused_gate : ∀ j < Csk.size, j + 1 < Csk.size → 0 < r ((n + m) + j) := by
      intro j hj hjl
      have hjlt : j < D.gates.length := by simpa [hCsk_sz, BinaryCircuit.size] using hj
      obtain ⟨rd, _, hread⟩ := (hDgates ⟨j, hjlt⟩).2.2.2.2.2 (by simpa [hCsk_sz] using hjl)
      have hcnt : 1 ≤ (gateAt Csk rd.val).inputs.count ((n + m) + j) := by
        rw [skel_gateAt D rd.val rd.isLt]
        exact List.count_pos_iff.mpr (by simpa [List.get_eq_getElem] using hread.imp Eq.symm Eq.symm)
      have hrd_lt : rd.val < Csk.size := by
        rw [hCsk_sz]; exact rd.isLt
      have hle := Finset.single_le_sum (f := fun k => (gateAt Csk k).inputs.count ((n + m) + j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hrd_lt)
      change (gateAt Csk rd.val).inputs.count ((n + m) + j) ≤ r ((n + m) + j) at hle
      omega
    have hCsk_out : Csk.output + 1 = (n + m) + Csk.size := by
      rw [hCsk_sz]; exact hDout
    obtain ⟨pure, chains, e, hpure_bd, hchain_bd, he_pos, hdisj, hcov, hpure_spec, hchain_spec⟩ :=
      S25644.thm (n + m) Csk hshape hrb (by omega) hCsk_out hused_gate
    have hneg0 : (@Finset.filter ℕ (fun k => (gateAt Csk k).op = GateOp.not)
        (fun k => Classical.propDecidable ((gateAt Csk k).op = GateOp.not)) (Finset.range Csk.size)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk
      have hklt : k < D.gates.length := by simpa [hCsk_sz, BinaryCircuit.size] using Finset.mem_range.mp hk
      rw [skel_gateAt D k hklt]
      simp
    rw [hneg0, Nat.add_zero] at hpure_bd hchain_bd he_pos
    set L := pure ++ chains with hL_def
    set once := (Finset.range (n + m)).filter (fun w => r w = 1) with honce_def
    have hL_sub_once : ∀ S ∈ L, S ⊆ once := by
      intro S hS
      rw [← hcov]
      intro w hw
      exact Finset.mem_biUnion.mpr ⟨S, List.mem_toFinset.mpr hS, hw⟩
    have hL_sub_range : ∀ S ∈ L, S ⊆ Finset.range (n + m) :=
      fun S hS => (hL_sub_once S hS).trans (Finset.filter_subset _ _)
    have hL_tree : ∀ S ∈ L, ∃ E region root, E.card ≤ 1 ∧ IsTreeAt (n + m) Csk S E region root := by
      intro S hS
      rcases List.mem_append.mp hS with hp | hc
      · obtain ⟨_, region, root, htr⟩ := hpure_spec S hp
        exact ⟨∅, region, root, by simp, htr⟩
      · obtain ⟨_, b, region, root, htr⟩ := hchain_spec S hc
        exact ⟨{b}, region, root, by simp, htr⟩
    have hL_cap : ∀ S ∈ L, (bankR n S).card ≤ 2 ∧ (bankC n m S).card ≤ 2 := by
      intro S hS
      obtain ⟨E, region, root, hE, htr⟩ := hL_tree S hS
      exact tree_cap D G hDrep hback hDout hDpos hrichG hrichT region.card S E region root
        le_rfl (hL_sub_range S hS) hE htr
    set U := (Finset.univ : Finset (Fin n)).filter (fun i => r i.val = 0) with hU_def
    set V := (Finset.univ : Finset (Fin m)).filter (fun j => r (n + j.val) = 0) with hV_def
    set offR := fun j : Fin m => D.eval (List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j)))
    set offC := fun i : Fin n => D.eval (List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false)
    have hU_eq : ∀ i ∈ U, ∀ j : Fin m, G i j = offR j := by
      intro i hi j
      rw [← hDrep i j]
      have hr0 : readsIn (skel D) (Finset.range D.size) i.val = 0 := by
        simpa [r, Csk, hCsk_sz] using (Finset.mem_filter.mp hi).2
      exact unread_row_eq D hback hDout hDpos i hr0 j
    have hV_eq : ∀ j ∈ V, ∀ i : Fin n, G i j = offC i := by
      intro j hj i
      rw [← hDrep i j]
      have hr0 : readsIn (skel D) (Finset.range D.size) (n + j.val) = 0 := by
        simpa [r, Csk, hCsk_sz] using (Finset.mem_filter.mp hj).2
      exact unread_col_eq D hback hDout hDpos j hr0 i
    have hU_le1 : U.card ≤ 1 := by
      by_contra hgt
      obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < U.card)
      obtain ⟨j, hj⟩ := rich_sep hn hrichG a b hab
      exact hj ((hU_eq a ha j).trans (hU_eq b hb j).symm)
    have hV_le1 : V.card ≤ 1 := by
      by_contra hgt
      obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < V.card)
      obtain ⟨i, hi⟩ := rich_sep hm hrichT a b hab
      exact hi ((hV_eq a ha i).trans (hV_eq b hb i).symm)
    set Kr := (Finset.univ : Finset (Fin L.length)).filter (fun idx => (bankR n (L.get idx)).card = 2)
    set Kc := (Finset.univ : Finset (Fin L.length)).filter (fun idx => (bankC n m (L.get idx)).card = 2)
    have hdisj_idx : ∀ i j : Fin L.length, i ≠ j → Disjoint (L.get i) (L.get j) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hdisj.rel_get_of_lt h
      · exact (hdisj.rel_get_of_lt h).symm
    have hpr_le : Kr.card ≤ hr := by
      have hex : ∀ idx : ↥Kr, ∃ e : Fin n × Fin n,
          e.1 ∈ bankR n (L.get idx.val) ∧ e.2 ∈ bankR n (L.get idx.val) ∧ e.1 ≠ e.2 ∧
          ∃ side : Bool, (Finset.univ.filter (fun col : Fin m =>
            (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ offR col)).card ≤ 2 := by
        intro idx
        have hmem : L.get idx.val ∈ L := List.get_mem L idx.val
        obtain ⟨E, region, root, hE, htr⟩ := hL_tree _ hmem
        exact pair_affordable_row D G hDrep hback hDout hDpos _ E region root
          (hL_sub_range _ hmem) hE htr (Finset.mem_filter.mp idx.property).2 (hL_cap _ hmem).2
      choose f hf using hex
      have hinj : Function.Injective f := by
        intro i j heq
        by_contra hne
        have hne' : i.val ≠ j.val := fun h => hne (Subtype.ext h)
        have h1 : (f i).1.val ∈ L.get i.val := (Finset.mem_filter.mp (hf i).1).2
        have h2 : (f i).1.val ∈ L.get j.val := by
          rw [heq]; exact (Finset.mem_filter.mp (hf j).1).2
        exact Finset.disjoint_left.mp (hdisj_idx i.val j.val hne') h1 h2
      set F := (Finset.univ : Finset ↥Kr).image f
      have hFcard : F.card = Kr.card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
      rw [← hFcard]
      apply hbddG offR F
      · intro e he
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        exact ⟨(hf i).2.2.1, (hf i).2.2.2⟩
      · intro e1 he1 e2 he2 hne
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he1
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he2
        have hij : i.val ≠ j.val := fun h => hne (congrArg f (Subtype.ext h))
        have hd := hdisj_idx i.val j.val hij
        have hi1 : (f i).1.val ∈ L.get i.val := (Finset.mem_filter.mp (hf i).1).2
        have hi2 : (f i).2.val ∈ L.get i.val := (Finset.mem_filter.mp (hf i).2.1).2
        have hj1 : (f j).1.val ∈ L.get j.val := (Finset.mem_filter.mp (hf j).1).2
        have hj2 : (f j).2.val ∈ L.get j.val := (Finset.mem_filter.mp (hf j).2.1).2
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro eq; exact Finset.disjoint_left.mp hd hi1 (congrArg Fin.val eq ▸ hj1)
        · intro eq; exact Finset.disjoint_left.mp hd hi1 (congrArg Fin.val eq ▸ hj2)
        · intro eq; exact Finset.disjoint_left.mp hd hi2 (congrArg Fin.val eq ▸ hj1)
        · intro eq; exact Finset.disjoint_left.mp hd hi2 (congrArg Fin.val eq ▸ hj2)
    have hpc_le : Kc.card ≤ hc := by
      have hex : ∀ idx : ↥Kc, ∃ e : Fin m × Fin m,
          e.1 ∈ bankC n m (L.get idx.val) ∧ e.2 ∈ bankC n m (L.get idx.val) ∧ e.1 ≠ e.2 ∧
          ∃ side : Bool, (Finset.univ.filter (fun row : Fin n =>
            (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ offC row)).card ≤ 2 := by
        intro idx
        have hmem : L.get idx.val ∈ L := List.get_mem L idx.val
        obtain ⟨E, region, root, hE, htr⟩ := hL_tree _ hmem
        exact pair_affordable_col D G hDrep hback hDout hDpos _ E region root
          (hL_sub_range _ hmem) hE htr (Finset.mem_filter.mp idx.property).2 (hL_cap _ hmem).1
      choose f hf using hex
      have hinj : Function.Injective f := by
        intro i j heq
        by_contra hne
        have hne' : i.val ≠ j.val := fun h => hne (Subtype.ext h)
        have h1 : n + (f i).1.val ∈ L.get i.val := (Finset.mem_filter.mp (hf i).1).2
        have h2 : n + (f i).1.val ∈ L.get j.val := by
          rw [heq]; exact (Finset.mem_filter.mp (hf j).1).2
        exact Finset.disjoint_left.mp (hdisj_idx i.val j.val hne') h1 h2
      set F := (Finset.univ : Finset ↥Kc).image f
      have hFcard : F.card = Kc.card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
      rw [← hFcard]
      apply hbddT offC F
      · intro e he
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        exact ⟨(hf i).2.2.1, (hf i).2.2.2⟩
      · intro e1 he1 e2 he2 hne
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he1
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he2
        have hij : i.val ≠ j.val := fun h => hne (congrArg f (Subtype.ext h))
        have hd := hdisj_idx i.val j.val hij
        have hi1 : n + (f i).1.val ∈ L.get i.val := (Finset.mem_filter.mp (hf i).1).2
        have hi2 : n + (f i).2.val ∈ L.get i.val := (Finset.mem_filter.mp (hf i).2.1).2
        have hj1 : n + (f j).1.val ∈ L.get j.val := (Finset.mem_filter.mp (hf j).1).2
        have hj2 : n + (f j).2.val ∈ L.get j.val := (Finset.mem_filter.mp (hf j).2.1).2
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro eq; exact Finset.disjoint_left.mp hd hi1 (congrArg (fun x : Fin m => n + x.val) eq ▸ hj1)
        · intro eq; exact Finset.disjoint_left.mp hd hi1 (congrArg (fun x : Fin m => n + x.val) eq ▸ hj2)
        · intro eq; exact Finset.disjoint_left.mp hd hi2 (congrArg (fun x : Fin m => n + x.val) eq ▸ hj1)
        · intro eq; exact Finset.disjoint_left.mp hd hi2 (congrArg (fun x : Fin m => n + x.val) eq ▸ hj2)
    have hU_eff : 0 < U.card → Kr.card = 0 ∧ 1 ≤ hr := by
      intro hposU
      obtain ⟨u0, hu0⟩ := Finset.card_pos.mp hposU
      constructor
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro idx _ h2
        have hmem : L.get idx ∈ L := List.get_mem L idx
        obtain ⟨E, region, root, hE, htr⟩ := hL_tree _ hmem
        obtain ⟨e, he1, he2, hne, side, hle2⟩ :=
          pair_affordable_row D G hDrep hback hDout hDpos _ E region root
            (hL_sub_range _ hmem) hE htr h2 (hL_cap _ hmem).2
        have hu0r : r u0.val = 0 := (Finset.mem_filter.mp hu0).2
        have he1r : r e.1.val = 1 := (Finset.mem_filter.mp (hL_sub_once _ hmem (Finset.mem_filter.mp he1).2)).2
        have he2r : r e.2.val = 1 := (Finset.mem_filter.mp (hL_sub_once _ hmem (Finset.mem_filter.mp he2).2)).2
        exact unread_forbids_affordable hrichG offR u0 e.1 e.2 (hU_eq u0 hu0)
          (fun eq => by rw [eq] at hu0r; omega)
          (fun eq => by rw [eq] at hu0r; omega) hne side hle2
      · have hlt : ({u0} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
          simp; omega
        obtain ⟨v, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        have huv : u0 ≠ v := fun eq => hv.2 (Finset.mem_singleton.mpr eq.symm)
        have h1 := hbddG offR {(u0, v)}
          (by
            intro e he
            rw [Finset.mem_singleton.mp he]
            refine ⟨huv, true, ?_⟩
            have hemp : (Finset.univ.filter (fun col : Fin m =>
                (G u0 col != G v col) = true ∧ G u0 col ≠ offR col)) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro col _
              simp [hU_eq u0 hu0 col]
            rw [hemp]; simp)
          (by intro e1 he1 e2 he2 hne; rw [Finset.mem_singleton.mp he1, Finset.mem_singleton.mp he2] at hne; exact absurd rfl hne)
        simpa using h1
    have hV_eff : 0 < V.card → Kc.card = 0 ∧ 1 ≤ hc := by
      intro hposV
      obtain ⟨v0, hv0⟩ := Finset.card_pos.mp hposV
      constructor
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro idx _ h2
        have hmem : L.get idx ∈ L := List.get_mem L idx
        obtain ⟨E, region, root, hE, htr⟩ := hL_tree _ hmem
        obtain ⟨e, he1, he2, hne, side, hle2⟩ :=
          pair_affordable_col D G hDrep hback hDout hDpos _ E region root
            (hL_sub_range _ hmem) hE htr h2 (hL_cap _ hmem).1
        have hv0r : r (n + v0.val) = 0 := (Finset.mem_filter.mp hv0).2
        have he1r : r (n + e.1.val) = 1 := (Finset.mem_filter.mp (hL_sub_once _ hmem (Finset.mem_filter.mp he1).2)).2
        have he2r : r (n + e.2.val) = 1 := (Finset.mem_filter.mp (hL_sub_once _ hmem (Finset.mem_filter.mp he2).2)).2
        exact unread_forbids_affordable hrichT offC v0 e.1 e.2 (hV_eq v0 hv0)
          (fun eq => by rw [eq] at hv0r; omega)
          (fun eq => by rw [eq] at hv0r; omega) hne side hle2
      · have hlt : ({v0} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
          simp; omega
        obtain ⟨w, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        have hvw : v0 ≠ w := fun eq => hw.2 (Finset.mem_singleton.mpr eq.symm)
        have h1 := hbddT offC {(v0, w)}
          (by
            intro e he
            rw [Finset.mem_singleton.mp he]
            refine ⟨hvw, true, ?_⟩
            have hemp : (Finset.univ.filter (fun row : Fin n =>
                (G row v0 != G row w) = true ∧ G row v0 ≠ offC row)) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro row _
              simp [hV_eq v0 hv0 row]
            rw [hemp]; simp)
          (by intro e1 he1 e2 he2 hne; rw [Finset.mem_singleton.mp he1, Finset.mem_singleton.mp he2] at hne; exact absurd rfl hne)
        simpa using h1
    set shared := (Finset.range ((n + m) + Csk.size)).filter (fun w => 2 ≤ r w) with hshared_def
    set sharedRaw := (Finset.range (n + m)).filter (fun w => 2 ≤ r w)
    set sharedGates := (Finset.range Csk.size).filter (fun k => 2 ≤ r ((n + m) + k))
    set markedReads := ∑ w ∈ shared, r w with hmr_def
    have hmr_pos : 0 < markedReads := by
      by_contra h0
      have hmr0 : markedReads = 0 := by omega
      have hsh_emp : shared = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have hle := Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) hw
        have hge2 := (Finset.mem_filter.mp hw).2
        omega
      have hsg0 : sharedGates.card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk hge2
        have hmem : (n + m) + k ∈ shared :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), hge2⟩
        rw [hsh_emp] at hmem
        exact Finset.notMem_empty _ hmem
      have hL_le1 : L.length ≤ 1 := by
        have hcl : chains.length = 0 := by omega
        have hpl : pure.length ≤ 1 := by omega
        simp [L]; omega
      have hrow_cov : (Finset.univ : Finset (Fin n)) ⊆ U ∪
          (Finset.univ : Finset (Fin L.length)).biUnion (fun idx => bankR n (L.get idx)) := by
        intro i _
        by_cases hr0 : r i.val = 0
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0⟩)
        · have hr1 : r i.val = 1 := by
            by_contra hne1
            have hge2 : 2 ≤ r i.val := by omega
            have hmem : i.val ∈ shared :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hge2⟩
            rw [hsh_emp] at hmem
            exact Finset.notMem_empty _ hmem
          have hmem_once : i.val ∈ once := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr1⟩
          rw [← hcov] at hmem_once
          obtain ⟨S, hSL, hiS⟩ := Finset.mem_biUnion.mp hmem_once
          obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hSL)
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩)
          rw [hidx]
          exact hiS
      have hcard_n := (Finset.card_le_card hrow_cov).trans (Finset.card_union_le _ _)
      have hbi := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin L.length)))
        (t := fun idx => bankR n (L.get idx))
      simp only [Finset.card_univ, Fintype.card_fin] at hcard_n
      by_cases hU0 : U.card = 0
      · have hsum_le : ∑ idx : Fin L.length, (bankR n (L.get idx)).card ≤ 2 * L.length := by
          calc ∑ idx : Fin L.length, (bankR n (L.get idx)).card
              ≤ ∑ _idx : Fin L.length, 2 := Finset.sum_le_sum (fun idx _ => (hL_cap _ (List.get_mem L idx)).1)
            _ = 2 * L.length := by simp [mul_comm]
        omega
      · have hKr0 := (hU_eff (by omega)).1
        have hle1 : ∀ idx : Fin L.length, (bankR n (L.get idx)).card ≤ 1 := by
          intro idx
          have h2 := (hL_cap _ (List.get_mem L idx)).1
          by_contra hgt1
          have heq2 : (bankR n (L.get idx)).card = 2 := by omega
          have hmem : idx ∈ Kr := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq2⟩
          rw [Finset.card_eq_zero.mp hKr0] at hmem
          exact Finset.notMem_empty _ hmem
        have hsum_le : ∑ idx : Fin L.length, (bankR n (L.get idx)).card ≤ L.length := by
          calc ∑ idx : Fin L.length, (bankR n (L.get idx)).card
              ≤ ∑ _idx : Fin L.length, 1 := Finset.sum_le_sum (fun idx _ => hle1 idx)
            _ = L.length := by simp
        omega
    have he1 : 1 ≤ e := by have := he_pos hmr_pos; omega
    set usedSet := (Finset.range (n + m)).filter (fun w => 1 ≤ r w)
    set zeroSet := (Finset.range (n + m)).filter (fun w => r w = 0)
    have hnm_part : n + m = U.card + V.card + usedSet.card := by
      have h1 : (Finset.range (n + m)).card = zeroSet.card + usedSet.card := by
        have := Finset.card_filter_add_card_filter_not (s := Finset.range (n + m)) (fun w => r w = 0)
        have hnot : (Finset.range (n + m)).filter (fun w => ¬ r w = 0) = usedSet := by
          ext w
          simp only [usedSet, Finset.mem_filter]
          constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by omega⟩
        rw [hnot] at this
        exact this.symm
      have hzero : zeroSet.card = U.card + V.card := by
        have hsub : zeroSet ⊆ Finset.range (n + m) := Finset.filter_subset _ _
        have heq := card_eq_bankR_add_bankC n m zeroSet hsub
        have hR : bankR n zeroSet = U := by
          ext i
          simp only [bankR, U, zeroSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
          exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
        have hC : bankC n m zeroSet = V := by
          ext j
          simp only [bankC, V, zeroSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
          exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
        rw [hR, hC] at heq
        exact heq
      rw [Finset.card_range] at h1
      omega
    have hused_part : usedSet.card = once.card + sharedRaw.card := by
      have h1 := Finset.card_filter_add_card_filter_not (s := usedSet) (fun w => r w = 1)
      have ha : usedSet.filter (fun w => r w = 1) = once := by
        ext w
        simp only [usedSet, once, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
      have hb : usedSet.filter (fun w => ¬ r w = 1) = sharedRaw := by
        ext w
        simp only [usedSet, sharedRaw, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, by omega⟩
      rw [ha, hb] at h1
      exact h1.symm
    set d := ∑ w ∈ shared, (r w - 1) with hd_def
    have hsh_eq : shared.card = sharedRaw.card + sharedGates.card := by
      have hdisj_s : Disjoint sharedRaw (sharedGates.image (fun k => (n + m) + k)) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        have hw1 := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h2
        omega
      have hun : shared = sharedRaw ∪ sharedGates.image (fun k => (n + m) + k) := by
        ext w
        simp only [shared, sharedRaw, sharedGates, Finset.mem_union, Finset.mem_filter,
          Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hlt, h2⟩
          by_cases hwn : w < n + m
          · exact Or.inl ⟨hwn, h2⟩
          · exact Or.inr ⟨w - (n + m), ⟨by omega, by simpa [show (n + m) + (w - (n + m)) = w by omega] using h2⟩, by omega⟩
        · rintro (⟨hlt, h2⟩ | ⟨k, ⟨hk, h2⟩, rfl⟩)
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, h2⟩
      rw [hun, Finset.card_union_of_disjoint hdisj_s,
        Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)]
    have hsh_le_d : sharedRaw.card + sharedGates.card ≤ d := by
      rw [← hsh_eq]
      calc shared.card = ∑ _w ∈ shared, 1 := by simp
        _ ≤ ∑ w ∈ shared, (r w - 1) := Finset.sum_le_sum (fun w hw => by
            have := (Finset.mem_filter.mp hw).2; omega)
    have hmr_eq : markedReads = d + sharedRaw.card + sharedGates.card := by
      rw [add_assoc, ← hsh_eq, hmr_def, hd_def]
      have hpt : ∀ w ∈ shared, r w = (r w - 1) + 1 := fun w hw => by
        have := (Finset.mem_filter.mp hw).2; omega
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
      simp
    have hbud : usedSet.card + d ≤ D.size + 1 := by
      have htot : ∑ w ∈ Finset.range ((n + m) + D.size), r w = 2 * D.size := by
        simpa [r, Csk, hCsk_sz] using sum_reads_skel (n + m) D hback
      have hpt : ∀ w ∈ Finset.range ((n + m) + D.size),
          r w = (if 1 ≤ r w then 1 else 0) + (if 2 ≤ r w then r w - 1 else 0) := by
        intro w _; split_ifs <;> omega
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib] at htot
      have hs1 : ∑ w ∈ Finset.range ((n + m) + D.size), (if 1 ≤ r w then 1 else 0) =
          ((Finset.range ((n + m) + D.size)).filter (fun w => 1 ≤ r w)).card := by
        rw [Finset.sum_boole, Nat.cast_id]
      have hs2 : ∑ w ∈ Finset.range ((n + m) + D.size), (if 2 ≤ r w then r w - 1 else 0) = d := by
        rw [hd_def, hshared_def, hCsk_sz, Finset.sum_filter]
      rw [hs1, hs2] at htot
      set liveGates := (Finset.range (D.size - 1)).image (fun j => (n + m) + j)
      have hdisj_ul : Disjoint usedSet liveGates := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        have hw1 := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h2
        omega
      have hsub_all : usedSet ∪ liveGates ⊆ (Finset.range ((n + m) + D.size)).filter (fun w => 1 ≤ r w) := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp h1
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hr1; omega), hr2⟩
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h2
          have hj' := Finset.mem_range.mp hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
            hused_gate j (by omega) (by omega)⟩
      have hcl := Finset.card_le_card hsub_all
      rw [Finset.card_union_of_disjoint hdisj_ul,
        Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h),
        Finset.card_range] at hcl
      omega
    have honce_le : once.card ≤ 2 * L.length + Kr.card + Kc.card := by
      have hsub_u : once ⊆ (Finset.univ : Finset (Fin L.length)).biUnion (fun idx => L.get idx) := by
        intro w hw
        rw [← hcov] at hw
        obtain ⟨S, hSL, hwS⟩ := Finset.mem_biUnion.mp hw
        obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hSL)
        refine Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ _, ?_⟩
        rw [hidx]
        exact hwS
      have hc1 := (Finset.card_le_card hsub_u).trans Finset.card_biUnion_le
      have hterm : ∀ idx : Fin L.length,
          (L.get idx).card ≤ 2 + (if idx ∈ Kr then 1 else 0) + (if idx ∈ Kc then 1 else 0) := by
        intro idx
        have hmem : L.get idx ∈ L := List.get_mem L idx
        have hcap := hL_cap _ hmem
        have heq := card_eq_bankR_add_bankC n m (L.get idx) (hL_sub_range _ hmem)
        have hKr_iff : idx ∈ Kr ↔ (bankR n (L.get idx)).card = 2 := by
          simp only [Kr, Finset.mem_filter, Finset.mem_univ, true_and]
        have hKc_iff : idx ∈ Kc ↔ (bankC n m (L.get idx)).card = 2 := by
          simp only [Kc, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h1 : (bankR n (L.get idx)).card = 2 <;> by_cases h2 : (bankC n m (L.get idx)).card = 2
        · rw [if_pos (hKr_iff.mpr h1), if_pos (hKc_iff.mpr h2)]; omega
        · rw [if_pos (hKr_iff.mpr h1), if_neg (mt hKc_iff.mp h2)]; omega
        · rw [if_neg (mt hKr_iff.mp h1), if_pos (hKc_iff.mpr h2)]; omega
        · rw [if_neg (mt hKr_iff.mp h1), if_neg (mt hKc_iff.mp h2)]; omega
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L.length))) (fun idx _ => hterm idx)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] at hsum
      omega
    have hfin := final_arith n m D.size U.card V.card usedSet.card once.card sharedRaw.card
      sharedGates.card d markedReads pure.length chains.length L.length e Kr.card Kc.card hr hc
      hnm_part hused_part hbud hsh_le_d hmr_eq hpure_bd hchain_bd
      (by simp [L]) he1 honce_le hU_le1 hV_le1 hU_eff hV_eff hpr_le hpc_le
    omega

end Main

end PEqualNP.Outside.L_meta_25874

theorem PEqualNP.Outside.L_meta_25874 : (∀ (n m hr hc : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let rich := fun (v w : ℕ) (T : Fin v → Fin w → Bool) =>
    ∀ (i j k : Fin v), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (T j col != T i col) = x ∧ (T k col != T i col) = y)).card
  let bounded := fun (v w : ℕ) (T : Fin v → Fin w → Bool) (h : ℕ) =>
    ∀ (off : Fin w → Bool) (F : Finset (Fin v × Fin v)),
      (∀ e ∈ F, e.1 ≠ e.2 ∧ ∃ side : Bool,
        (Finset.univ.filter (fun col =>
          (T e.1 col != T e.2 col) = side ∧ T e.1 col ≠ off col)).card ≤ 2) →
      (∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) → F.card ≤ h
  let tr := fun (j : Fin m) (i : Fin n) => G i j
  3 ≤ n → 3 ≤ m → 2*hr+2 ≤ n → 2*hc+2 ≤ m →
  rich n m G → rich m n tr → bounded n m G hr → bounded m n tr hc →
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) → PEqualNP.Represents.Represents G C →
    11*(n+m) ≤ 10*(C.gates.countP (fun g => g.inputs.length == 2)) + 26 + 2*(hr+hc)) := by
  intro n m hr hc G C rich bounded tr hn hm _ _ hrichG hrichT hbddG hbddT hdeg hrep
  exact PEqualNP.Outside.L_meta_25874.Main.solve n m hr hc G C hn hm hrichG hrichT hbddG hbddT hdeg hrep
