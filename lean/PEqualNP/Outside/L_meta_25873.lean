import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25873
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

end PEqualNP.Outside.L_meta_25873

theorem PEqualNP.Outside.L_meta_25873 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
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
  rcases PEqualNP.Outside.L_meta_25873.normalized n C h with ht | ⟨D,hp,hb,ho,hg,he⟩
  · rcases ht with hc | hi
    · exact Or.inl hc
    · exact Or.inr (Or.inl hi)
  · refine Or.inr (Or.inr ⟨D,hp,hb,ho,?_,he⟩)
    intro j
    obtain ⟨⟨hl,hr,hne,hy,hz⟩,hlive⟩ := hg j
    exact ⟨hl,hr,hne,hy,hz,hlive⟩
