import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25798

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Represents


def xorSum {α : Type*} [DecidableEq α] (S : Finset α) (f : α → Bool) : Bool :=
  (S.filter (fun a => f a = true)).card % 2 == 1

lemma xorSum_empty {α : Type*} [DecidableEq α] (f : α → Bool) :
    xorSum (∅ : Finset α) f = false := by
  simp [xorSum]

lemma xorSum_insert {α : Type*} [DecidableEq α] {S : Finset α} {a : α} (ha : a ∉ S)
    (f : α → Bool) : xorSum (insert a S) f = xor (f a) (xorSum S f) := by
  unfold xorSum
  rw [Finset.filter_insert]
  cases hfa : f a
  · simp
  · simp only [↓reduceIte, Bool.true_xor]
    have hnot : a ∉ S.filter (fun x => f x = true) := fun h => ha (Finset.mem_filter.mp h).1
    rw [Finset.card_insert_of_notMem hnot]
    set k := (S.filter (fun x => f x = true)).card
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [Nat.add_mod, hk]

lemma xorSum_singleton {α : Type*} [DecidableEq α] (a : α) (f : α → Bool) :
    xorSum ({a} : Finset α) f = f a := by
  change xorSum (insert a ∅) f = f a
  rw [xorSum_insert (Finset.notMem_empty a), xorSum_empty, Bool.xor_false]

lemma xorSum_congr {α : Type*} [DecidableEq α] {S T : Finset α} (hST : S = T)
    {f g : α → Bool} (hfg : ∀ a ∈ T, f a = g a) : xorSum S f = xorSum T g := by
  subst hST
  unfold xorSum
  have hfilt : S.filter (fun a => f a = true) = S.filter (fun a => g a = true) := by
    ext a
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro ha
    rw [hfg a ha]
  rw [hfilt]

lemma xorSum_xor {α : Type*} [DecidableEq α] (S : Finset α) (f g : α → Bool) :
    xorSum S (fun a => xor (f a) (g a)) = xor (xorSum S f) (xorSum S g) := by
  induction S using Finset.induction_on with
  | empty => simp [xorSum_empty]
  | @insert a S ha ih =>
    rw [xorSum_insert ha, xorSum_insert ha, xorSum_insert ha, ih]
    cases f a <;> cases g a <;> cases xorSum S f <;> cases xorSum S g <;> rfl

lemma xorSum_and_left {α : Type*} [DecidableEq α] (S : Finset α) (c : Bool) (f : α → Bool) :
    xorSum S (fun a => c && f a) = (c && xorSum S f) := by
  cases c
  · simp [xorSum]
  · simp [xorSum]

lemma xorSum_and_right {α : Type*} [DecidableEq α] (S : Finset α) (f : α → Bool) (c : Bool) :
    xorSum S (fun a => f a && c) = (xorSum S f && c) := by
  cases c
  · simp [xorSum]
  · simp [xorSum]

lemma xorSum_false {α : Type*} [DecidableEq α] (S : Finset α) :
    xorSum S (fun _ => false) = false := by
  simp [xorSum]

lemma xorSum_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β → Bool) :
    xorSum S (fun a => xorSum T (fun b => f a b)) =
      xorSum T (fun b => xorSum S (fun a => f a b)) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [xorSum_empty]
    symm
    rw [xorSum_congr rfl (fun b _ => xorSum_empty (fun a => f a b)), xorSum_false]
  | @insert a S ha ih =>
    rw [xorSum_insert ha, ih, ← xorSum_xor]
    exact xorSum_congr rfl (fun b _ => (xorSum_insert ha (fun x => f x b)).symm)

lemma xorSum_union_disjoint {α : Type*} [DecidableEq α] {S T : Finset α}
    (h : Disjoint S T) (f : α → Bool) :
    xorSum (S ∪ T) f = xor (xorSum S f) (xorSum T f) := by
  induction S using Finset.induction_on with
  | empty => simp [xorSum_empty]
  | @insert a S ha ih =>
    have haT : a ∉ T := Finset.disjoint_left.mp h (Finset.mem_insert_self a S)
    have hST : Disjoint S T := Finset.disjoint_of_subset_left (Finset.subset_insert a S) h
    have haST : a ∉ S ∪ T := by simp [ha, haT]
    rw [Finset.insert_union, xorSum_insert haST, xorSum_insert ha, ih hST]
    cases f a <;> cases xorSum S f <;> cases xorSum T f <;> rfl

lemma xorSum_eq_ite {α : Type*} [DecidableEq α] (S : Finset α) (a0 : α) (f : α → Bool) :
    xorSum S (fun a => decide (a = a0) && f a) = if a0 ∈ S then f a0 else false := by
  induction S using Finset.induction_on with
  | empty => simp [xorSum_empty]
  | @insert a S ha ih =>
    rw [xorSum_insert ha, ih]
    by_cases h : a = a0
    · subst h
      simp [ha]
    · have h1 : decide (a = a0) = false := decide_eq_false h
      have h2 : (a0 ∈ insert a S) ↔ a0 ∈ S := by simp [Ne.symm h]
      simp [h1, h2]

lemma xorSum_eq_ite_symm {α : Type*} [DecidableEq α] (S : Finset α) (a0 : α) (f : α → Bool) :
    xorSum S (fun a => decide (a0 = a) && f a) = if a0 ∈ S then f a0 else false := by
  rw [xorSum_congr rfl (fun a _ => by
    have : decide (a0 = a) = decide (a = a0) := by
      by_cases h : a0 = a <;> simp [h, eq_comm]
    rw [this])]
  exact xorSum_eq_ite S a0 f

lemma xorSum_pair {α : Type*} [DecidableEq α] (S : Finset α) {a b : α}
    (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) (f : α → Bool) :
    xorSum S (fun x => (decide (x = a) || decide (x = b)) && f x) = xor (f a) (f b) := by
  have hfn : ∀ x ∈ S, ((decide (x = a) || decide (x = b)) && f x) =
      xor (decide (x = a) && f x) (decide (x = b) && f x) := by
    intro x _
    by_cases hxa : x = a
    · subst hxa; simp [hab]
    · by_cases hxb : x = b
      · subst hxb; simp [hxa]
      · simp [hxa, hxb]
  rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite, xorSum_eq_ite]
  simp [ha, hb]

lemma xorSum_subset_zero {α : Type*} [DecidableEq α] {S T : Finset α} (hST : S ⊆ T)
    (f : α → Bool) (h0 : ∀ a ∈ T, a ∉ S → f a = false) : xorSum S f = xorSum T f := by
  have hunion : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset hST
  rw [← hunion, xorSum_union_disjoint Finset.disjoint_sdiff]
  have hz : xorSum (T \ S) f = false := by
    rw [xorSum_congr rfl (fun a ha => h0 a (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp ha).2),
      xorSum_false]
  rw [hz, Bool.xor_false]


def dotFun (s : ℕ) (x y : Fin (4 ^ s)) : Bool :=
  ((Finset.univ : Finset (Fin (2 * s))).filter (fun i =>
    x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1

def quadFun (s : ℕ) (x : Fin (4 ^ s)) : Bool :=
  ((Finset.univ : Finset (Fin s)).filter (fun i =>
    x.val.testBit i.val && x.val.testBit (s + i.val))).card % 2 == 1

def signedFun (s : ℕ) (x y : Fin (4 ^ s)) : Bool :=
  xor (xor (quadFun s x) (quadFun s y)) (dotFun s x y)

lemma four_pow_eq_two_pow (s : ℕ) : 4 ^ s = 2 ^ (2 * s) := by
  rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]

lemma dotFun_symm (s : ℕ) (x y : Fin (4 ^ s)) : dotFun s x y = dotFun s y x := by
  unfold dotFun
  congr 1; congr 1; congr 1
  ext i
  simp [Bool.and_comm]

lemma signedFun_symm (s : ℕ) (x y : Fin (4 ^ s)) : signedFun s x y = signedFun s y x := by
  unfold signedFun
  rw [dotFun_symm, Bool.xor_comm (quadFun s x)]

lemma dotFun_zero_left (s : ℕ) (y : Fin (4 ^ s)) :
    dotFun s ⟨0, by positivity⟩ y = false := by
  unfold dotFun
  simp

lemma dotFun_one_one (s : ℕ) (hs : 1 ≤ s) :
    dotFun s ⟨1, by
      have : 4 ^ 1 ≤ 4 ^ s := Nat.pow_le_pow_right (by omega) hs
      omega⟩ ⟨1, by
      have : 4 ^ 1 ≤ 4 ^ s := Nat.pow_le_pow_right (by omega) hs
      omega⟩ = true := by
  unfold dotFun
  have hfilt : (Finset.univ : Finset (Fin (2 * s))).filter
      (fun i => (1 : ℕ).testBit i.val && (1 : ℕ).testBit i.val) = {⟨0, by omega⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
    cases hi : i.val with
    | zero => simp
    | succ k =>
      have : (1 : ℕ).testBit (k + 1) = false := by
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)))
      simp [this]
  rw [hfilt]
  simp

lemma dotFun_two_pow (s : ℕ) (x : Fin (4 ^ s)) (i : Fin (2 * s)) :
    dotFun s x ⟨2 ^ i.val, by
      rw [four_pow_eq_two_pow]
      exact Nat.pow_lt_pow_right (by omega) i.isLt⟩ = x.val.testBit i.val := by
  unfold dotFun
  have hfilt : (Finset.univ : Finset (Fin (2 * s))).filter
      (fun j => x.val.testBit j.val && (2 ^ i.val).testBit j.val) =
      if x.val.testBit i.val = true then {i} else ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_two_pow]
    by_cases hij : i.val = j.val
    · have hji : j = i := Fin.ext hij.symm
      subst hji
      cases x.val.testBit j.val <;> simp
    · have hne : j ≠ i := fun h => hij (congrArg Fin.val h).symm
      cases x.val.testBit i.val <;> simp [hij, hne]
  rw [hfilt]
  cases x.val.testBit i.val <;> simp

lemma dotFun_distinct_rows (s : ℕ) (u₁ u₂ : Fin (4 ^ s)) (c : Bool)
    (h : ∀ v, dotFun s u₁ v = xor (dotFun s u₂ v) c) : u₁ = u₂ := by
  have h0 := h ⟨0, by positivity⟩
  rw [dotFun_symm s u₁, dotFun_symm s u₂, dotFun_zero_left s, dotFun_zero_left s] at h0
  have hc : c = false := by cases c <;> simp at h0 <;> rfl
  subst hc
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 2 * s
  · have hv := h ⟨2 ^ k, by rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) hk⟩
    simp only [Bool.xor_false] at hv
    have h1 := dotFun_two_pow s u₁ ⟨k, hk⟩
    have h2 := dotFun_two_pow s u₂ ⟨k, hk⟩
    simpa [h1, h2] using hv
  · have hlt1 : u₁.val < 2 ^ k := by
      have : u₁.val < 2 ^ (2 * s) := by rw [← four_pow_eq_two_pow]; exact u₁.isLt
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
    have hlt2 : u₂.val < 2 ^ k := by
      have : u₂.val < 2 ^ (2 * s) := by rw [← four_pow_eq_two_pow]; exact u₂.isLt
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]

lemma signedFun_distinct_rows (s : ℕ) (u₁ u₂ : Fin (4 ^ s)) (c : Bool)
    (h : ∀ v, signedFun s u₁ v = xor (signedFun s u₂ v) c) : u₁ = u₂ := by
  apply dotFun_distinct_rows s u₁ u₂ (xor (xor (quadFun s u₁) (quadFun s u₂)) c)
  intro v
  have hv := h v
  unfold signedFun at hv
  generalize quadFun s u₁ = a at hv ⊢
  generalize quadFun s u₂ = b at hv ⊢
  generalize quadFun s v = d at hv ⊢
  generalize dotFun s u₁ v = e at hv ⊢
  generalize dotFun s u₂ v = f at hv ⊢
  cases a <;> cases b <;> cases d <;> cases e <;> cases f <;> cases c <;> simp_all


def isBinGate (g : Gate) : Bool := g.inputs.length == 2

def isNLGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def bCount (C : Circuit) : ℕ := C.gates.countP isBinGate
def tCount (C : Circuit) : ℕ := C.gates.countP isNLGate

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWires x := rfl

lemma foldl_stepWires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWires w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepWires_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWires w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWires w g).length := by
      simp only [stepWires, List.length_append, List.length_singleton]; omega
    rw [ih (stepWires w g) hi']
    simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_stepWires_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, i < w.length + k) :
    (gs.foldl stepWires w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl stepWires w).getD i false) := by
  induction gs generalizing w j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getD_cons_zero]
      have hlen : w.length < (stepWires w g).length := by
        simp only [stepWires, List.length_append, List.length_singleton]; omega
      rw [foldl_stepWires_getD_lt gs (stepWires w g) w.length hlen]
      have hget : (stepWires w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWires, List.getD_eq_getElem?_getD]
      rw [hget]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < w.length := by
        have := hrb 0 (Nat.succ_pos _) i
        simp only [List.getD_cons_zero, Nat.add_zero] at this
        exact this hi
      have hilt' : i < (stepWires w g).length := by
        simp only [stepWires, List.length_append, List.length_singleton]; omega
      rw [foldl_stepWires_getD_lt gs (stepWires w g) i hilt']
      simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
    | succ j' =>
      simp only [List.foldl_cons, List.getD_cons_succ]
      have hidx : w.length + (j' + 1) = (stepWires w g).length + j' := by
        simp only [stepWires, List.length_append, List.length_singleton]; omega
      rw [hidx]
      apply ih (stepWires w g) j' (Nat.lt_of_succ_lt_succ hj)
      intro k hk i hi
      have := hrb (k + 1) (Nat.succ_lt_succ hk) i
      simp only [List.getD_cons_succ] at this
      have hlt := this hi
      simp only [stepWires, List.length_append, List.length_singleton]
      omega

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  have hi' : i < (List.ofFn (fun k : Fin n => decide (k = u))).length := by simp [hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi', List.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  by_cases h : i = u.val
  · simp [Fin.ext_iff, h]
  · simp [Fin.ext_iff, h]

lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < m) :
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold oneEach
  have hlen : (List.ofFn (fun k : Fin n => decide (k = u))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left,
    List.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  by_cases h : i = v.val
  · simp [Fin.ext_iff, h]
  · simp [Fin.ext_iff, h]

lemma wireVal_left {n m : ℕ} (C : Circuit) (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (C.wires (oneEach u v)).getD i false = decide (i = u.val) := by
  have hi' : i < (oneEach u v).length := by rw [oneEach_length]; omega
  rw [wires_eq_foldl, foldl_stepWires_getD_lt _ _ _ hi', oneEach_getD_left u v i hi]

lemma wireVal_right {n m : ℕ} (C : Circuit) (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < m) :
    (C.wires (oneEach u v)).getD (n + i) false = decide (i = v.val) := by
  have hi' : n + i < (oneEach u v).length := by rw [oneEach_length]; omega
  rw [wires_eq_foldl, foldl_stepWires_getD_lt _ _ _ hi', oneEach_getD_right u v i hi]

lemma wireVal_gate {n m : ℕ} (C : Circuit) (hrb : ReadsBack (n + m) C)
    (u : Fin n) (v : Fin m) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (oneEach u v)).getD (n + m + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (C.wires (oneEach u v)).getD i false) := by
  have hlen : (oneEach u v).length = n + m := oneEach_length u v
  rw [← hlen]
  apply foldl_stepWires_getD_gate C.gates (oneEach u v) j hj
  intro k hk i hi
  rw [hlen]
  exact hrb k hk i hi


def linConst (g : Gate) : Bool :=
  match g.inputs with
  | [] => g.op.eval []
  | [_] => g.op.eval [false]
  | [_, _] => g.op.eval [false, false]
  | _ => false

def linIns (g : Gate) : List ℕ :=
  match g.inputs with
  | [] => []
  | [a] => if xor (g.op.eval [false]) (g.op.eval [true]) then [a] else []
  | [a, b] =>
    let c0 := g.op.eval [false, false]
    let c1 := xor c0 (g.op.eval [true, false])
    let c2 := xor c0 (g.op.eval [false, true])
    match c1, c2 with
    | false, false => []
    | true, false => [a]
    | false, true => [b]
    | true, true => if a == b then [] else [a, b]
  | _ => []

lemma linIns_sub (g : Gate) : ∀ i ∈ linIns g, i ∈ g.inputs := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [linIns]
  · simp only [linIns]
    split <;> simp
  · simp only [linIns]
    cases xor (op.eval [false, false]) (op.eval [true, false]) <;>
      cases xor (op.eval [false, false]) (op.eval [false, true]) <;>
      simp
  · simp [linIns]

lemma linIns_len_le (g : Gate) : (linIns g).length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [linIns]
  · simp only [linIns]; split <;> simp
  · simp only [linIns]
    cases xor (op.eval [false, false]) (op.eval [true, false]) <;>
      cases xor (op.eval [false, false]) (op.eval [false, true]) <;> simp
    split <;> simp
  · simp [linIns]

lemma linIns_len_two_imp (g : Gate) (h : (linIns g).length = 2) : isBinGate g = true := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [linIns] at h
  · simp only [linIns] at h; split at h <;> simp at h
  · simp [isBinGate]
  · simp [linIns] at h

lemma lin_gate_eval (g : Gate) (hlen : g.inputs.length ≤ 2) (hnl : isNLGate g = false)
    (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) =
      (linIns g).foldl (fun acc i => xor acc (f i)) (linConst g) := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [linIns, linConst]
  · simp only [linIns, linConst, List.map_cons, List.map_nil]
    cases h0 : op.eval [false] <;> cases h1 : op.eval [true] <;> cases hfa : f a <;>
      simp [h0, h1, hfa]
  · simp only [isNLGate, List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and] at hnl
    simp only [linIns, linConst, List.map_cons, List.map_nil]
    by_cases hab : a = b
    · subst hab
      cases h00 : op.eval [false, false] <;> cases h01 : op.eval [false, true] <;>
        cases h10 : op.eval [true, false] <;> cases h11 : op.eval [true, true] <;>
        cases hfa : f a <;> simp_all
    · have hbeq : (a == b) = false := beq_false_of_ne hab
      cases h00 : op.eval [false, false] <;> cases h01 : op.eval [false, true] <;>
        cases h10 : op.eval [true, false] <;> cases h11 : op.eval [true, true] <;>
        cases hfa : f a <;> cases hfb : f b <;> simp_all
  · simp at hlen


lemma countP_eq_range_filter {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    l.countP p = ((List.range l.length).filter (fun j => p (l.getD j d))).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.length_cons, List.range_succ_eq_map, List.filter_cons,
      List.filter_map]
    simp only [List.getD_cons_zero]
    have hcomp : ((fun j => p ((a :: l).getD j d)) ∘ Nat.succ) = (fun j => p (l.getD j d)) := by
      funext j; simp
    rw [hcomp]
    cases hp : p a
    · simp [List.length_map, hp, ih]
    · simp [List.length_map, hp, ih]

lemma list_filter_length_eq_finset_card (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = ((Finset.range n).filter (fun j => p j = true)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    have hnot : n ∉ (Finset.range n).filter (fun j => p j = true) := by simp
    cases hp : p n
    · simp [hp]
    · simp [hp, Finset.card_insert_of_notMem hnot]

section LowerBound

variable (N : ℕ) (C : Circuit)

def totalWires : ℕ := N + N + C.gates.length

def nlIndices : List ℕ :=
  (List.range C.gates.length).filter (fun j => isNLGate (gateAt C j))

lemma nlIndices_length : (nlIndices C).length = tCount C := by
  unfold nlIndices tCount
  exact (countP_eq_range_filter C.gates ⟨GateOp.or, []⟩ isNLGate).symm

lemma nlIndices_pairwise : (nlIndices C).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma nlIndices_lt (k : Fin (tCount C)) :
    (nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt) < C.gates.length := by
  have hmem := List.getElem_mem (l := nlIndices C) (n := k.val) (by rw [nlIndices_length]; exact k.isLt)
  have := (List.mem_filter.mp hmem).1
  exact List.mem_range.mp this

lemma nlIndices_isNL (k : Fin (tCount C)) :
    isNLGate (gateAt C ((nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt))) = true := by
  have hmem := List.getElem_mem (l := nlIndices C) (n := k.val) (by rw [nlIndices_length]; exact k.isLt)
  exact (List.mem_filter.mp hmem).2

lemma nlIndices_strictMono {k₁ k₂ : Fin (tCount C)} (h : k₁ < k₂) :
    (nlIndices C)[k₁.val]'(by rw [nlIndices_length]; exact k₁.isLt) <
    (nlIndices C)[k₂.val]'(by rw [nlIndices_length]; exact k₂.isLt) :=
  (List.pairwise_iff_getElem.mp (nlIndices_pairwise C)) k₁.val k₂.val
    (by rw [nlIndices_length]; exact k₁.isLt) (by rw [nlIndices_length]; exact k₂.isLt) h

lemma nlIndices_exists {j : ℕ} (hj : j < C.gates.length) (hnl : isNLGate (gateAt C j) = true) :
    ∃ k : Fin (tCount C),
      (nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt) = j := by
  have hmem : j ∈ nlIndices C := List.mem_filter.mpr ⟨List.mem_range.mpr hj, hnl⟩
  obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem hmem
  exact ⟨⟨idx, by rw [← nlIndices_length]; exact hidx⟩, heq⟩

def nlWire (k : Fin (tCount C)) : ℕ :=
  N + N + (nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt)

def isBaseWire (w : ℕ) : Bool :=
  decide (w < N + N) ||
    (decide (N + N ≤ w) && decide (w - (N + N) < C.gates.length) &&
      isNLGate (gateAt C (w - (N + N))))

lemma isBaseWire_left (u : Fin N) : isBaseWire N C u.val = true := by
  unfold isBaseWire; simp [show u.val < N + N by omega]

lemma isBaseWire_right (v : Fin N) : isBaseWire N C (N + v.val) = true := by
  unfold isBaseWire; simp [show N + v.val < N + N by omega]

lemma isBaseWire_nl (k : Fin (tCount C)) : isBaseWire N C (nlWire N C k) = true := by
  unfold isBaseWire nlWire
  simp [nlIndices_lt C k, nlIndices_isNL C k]

def coreRoot : ℕ → Option ℕ
  | w =>
    if w ≥ totalWires N C then none
    else if isBaseWire N C w then some w
    else
      match linIns (gateAt C (w - (N + N))) with
      | [] => none
      | [a] => if _ : a < w then coreRoot a else none
      | [a, b] =>
        let ra := if _ : a < w then coreRoot a else none
        let rb := if _ : b < w then coreRoot b else none
        match ra, rb with
        | none, rb => rb
        | ra, none => ra
        | some r1, some r2 => if r1 == r2 then none else some w
      | _ => none

def trueParents (w : ℕ) : Option (ℕ × ℕ) :=
  if w ≥ totalWires N C then none
  else if isBaseWire N C w then none
  else
    match linIns (gateAt C (w - (N + N))) with
    | [a, b] =>
      let ra := if a < w then coreRoot N C a else none
      let rb := if b < w then coreRoot N C b else none
      match ra, rb with
      | some r1, some r2 => if r1 == r2 then none else some (r1, r2)
      | _, _ => none
    | _ => none

def isTrueGate (w : ℕ) : Bool := (trueParents N C w).isSome

lemma coreRoot_le (w r : ℕ) (h : coreRoot N C w = some r) : r ≤ w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    unfold coreRoot at h
    dsimp only at h
    by_cases hge : w ≥ totalWires N C
    · simp [hge] at h
    · by_cases hbase : isBaseWire N C w = true
      · simp only [hge, ↓reduceIte, hbase] at h
        cases h; exact le_rfl
      · simp only [hge, ↓reduceIte, hbase, Bool.false_eq_true] at h
        cases hlin : linIns (gateAt C (w - (N + N))) with
        | nil => rw [hlin] at h; cases h
        | cons a rest =>
          cases rest with
          | nil =>
            rw [hlin] at h
            dsimp only at h
            by_cases haw : a < w
            · simp only [haw, ↓reduceDIte] at h
              exact le_of_lt (lt_of_le_of_lt (ih a haw h) haw)
            · simp [haw] at h
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              rw [hlin] at h
              simp only [dite_eq_ite] at h
              cases hra : (if a < w then coreRoot N C a else none) with
              | none =>
                rw [hra] at h
                dsimp only at h
                by_cases hbw : b < w
                · simp only [hbw, ↓reduceIte] at h
                  exact le_of_lt (lt_of_le_of_lt (ih b hbw h) hbw)
                · simp [hbw] at h
              | some r1 =>
                rw [hra] at h
                cases hrb : (if b < w then coreRoot N C b else none) with
                | none =>
                  rw [hrb] at h
                  cases h
                  by_cases haw : a < w
                  · simp only [haw, ↓reduceIte] at hra
                    exact le_of_lt (lt_of_le_of_lt (ih a haw hra) haw)
                  · simp [haw] at hra
                | some r2 =>
                  rw [hrb] at h
                  dsimp only at h
                  by_cases heq : (r1 == r2) = true
                  · simp [heq] at h
                  · simp only [heq, ↓reduceIte] at h
                    cases h; exact le_rfl
            | cons _ _ => rw [hlin] at h; cases h

lemma coreRoot_spec (w r : ℕ) (h : coreRoot N C w = some r) :
    r < totalWires N C ∧ (isBaseWire N C r = true ∨ isTrueGate N C r = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    unfold coreRoot at h
    dsimp only at h
    by_cases hge : w ≥ totalWires N C
    · simp [hge] at h
    · by_cases hbase : isBaseWire N C w = true
      · simp only [hge, ↓reduceIte, hbase] at h
        cases h
        exact ⟨by omega, Or.inl hbase⟩
      · simp only [hge, ↓reduceIte, hbase, Bool.false_eq_true] at h
        cases hlin : linIns (gateAt C (w - (N + N))) with
        | nil => rw [hlin] at h; cases h
        | cons a rest =>
          cases rest with
          | nil =>
            rw [hlin] at h
            dsimp only at h
            by_cases haw : a < w
            · simp only [haw, ↓reduceDIte] at h
              exact ih a haw h
            · simp [haw] at h
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              rw [hlin] at h
              simp only [dite_eq_ite] at h
              cases hra : (if a < w then coreRoot N C a else none) with
              | none =>
                rw [hra] at h
                dsimp only at h
                by_cases hbw : b < w
                · simp only [hbw, ↓reduceIte] at h
                  exact ih b hbw h
                · simp [hbw] at h
              | some r1 =>
                rw [hra] at h
                cases hrb : (if b < w then coreRoot N C b else none) with
                | none =>
                  rw [hrb] at h
                  cases h
                  by_cases haw : a < w
                  · simp only [haw, ↓reduceIte] at hra
                    exact ih a haw hra
                  · simp [haw] at hra
                | some r2 =>
                  rw [hrb] at h
                  dsimp only at h
                  by_cases heq : (r1 == r2) = true
                  · simp [heq] at h
                  · simp only [heq, ↓reduceIte] at h
                    cases h
                    refine ⟨by omega, Or.inr ?_⟩
                    unfold isTrueGate trueParents
                    simp only [hge, ↓reduceIte, hbase, Bool.false_eq_true, hlin, hra, hrb, heq,
                      Option.isSome_some]
            | cons _ _ => rw [hlin] at h; cases h

lemma trueParents_spec {w r1 r2 : ℕ} (h : trueParents N C w = some (r1, r2)) :
    w < totalWires N C ∧ isBaseWire N C w = false ∧
    r1 < w ∧ r2 < w ∧ r1 ≠ r2 ∧
    (isBaseWire N C r1 = true ∨ isTrueGate N C r1 = true) ∧
    (isBaseWire N C r2 = true ∨ isTrueGate N C r2 = true) ∧
    N + N ≤ w ∧ isBinGate (gateAt C (w - (N + N))) = true ∧
    isNLGate (gateAt C (w - (N + N))) = false := by
  unfold trueParents at h
  by_cases hge : w ≥ totalWires N C
  · simp [hge] at h
  · by_cases hbase : isBaseWire N C w = true
    · simp [hge, hbase] at h
    · simp only [hge, ↓reduceIte, hbase, Bool.false_eq_true] at h
      cases hlin : linIns (gateAt C (w - (N + N))) with
    | nil => rw [hlin] at h; cases h
    | cons a rest =>
      cases rest with
      | nil => rw [hlin] at h; cases h
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          rw [hlin] at h
          dsimp only at h
          cases hra : (if a < w then coreRoot N C a else none) with
          | none => rw [hra] at h; cases h
          | some r1' =>
            rw [hra] at h
            cases hrb : (if b < w then coreRoot N C b else none) with
            | none => rw [hrb] at h; cases h
            | some r2' =>
              rw [hrb] at h
              dsimp only at h
              by_cases heq : (r1' == r2') = true
              · simp [heq] at h
              · simp only [heq, ↓reduceIte] at h
                cases h
                have haw : a < w ∧ coreRoot N C a = some r1 := by
                  by_cases ha : a < w
                  · simp only [ha, ↓reduceIte] at hra; exact ⟨ha, hra⟩
                  · simp [ha] at hra
                have hbw : b < w ∧ coreRoot N C b = some r2 := by
                  by_cases hb : b < w
                  · simp only [hb, ↓reduceIte] at hrb; exact ⟨hb, hrb⟩
                  · simp [hb] at hrb
                have hr1lt : r1 < w := lt_of_le_of_lt (coreRoot_le N C a r1 haw.2) haw.1
                have hr2lt : r2 < w := lt_of_le_of_lt (coreRoot_le N C b r2 hbw.2) hbw.1
                have hne : r1 ≠ r2 := fun h => heq (beq_iff_eq.mpr h)
                have hbaseF : isBaseWire N C w = false := Bool.eq_false_iff.mpr hbase
                have hgeNN : N + N ≤ w := by
                  unfold isBaseWire at hbaseF
                  by_contra hlt
                  simp [show w < N + N by omega] at hbaseF
                have hbin : isBinGate (gateAt C (w - (N + N))) = true :=
                  linIns_len_two_imp _ (by rw [hlin]; rfl)
                have hnlF : isNLGate (gateAt C (w - (N + N))) = false := by
                  unfold isBaseWire at hbaseF
                  have hltg : w - (N + N) < C.gates.length := by unfold totalWires at hge; omega
                  simp [hgeNN, hltg, show ¬(w < N + N) by omega] at hbaseF
                  exact hbaseF
                exact ⟨by omega, hbaseF, hr1lt, hr2lt, hne,
                  (coreRoot_spec N C a r1 haw.2).2, (coreRoot_spec N C b r2 hbw.2).2,
                  hgeNN, hbin, hnlF⟩
        | cons _ _ => rw [hlin] at h; cases h

lemma coreRoot_of_isTrueGate {w : ℕ} (h : isTrueGate N C w = true) :
    coreRoot N C w = some w := by
  unfold isTrueGate at h
  cases hp : trueParents N C w with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨r1, r2⟩ := p
    unfold trueParents at hp
    unfold coreRoot
    dsimp only
    by_cases hge : w ≥ totalWires N C
    · simp [hge] at hp
    · by_cases hbase : isBaseWire N C w = true
      · simp [hge, hbase] at hp
      · simp only [hge, ↓reduceIte, hbase, Bool.false_eq_true] at hp ⊢
        cases hlin : linIns (gateAt C (w - (N + N))) with
      | nil => rw [hlin] at hp; cases hp
      | cons a rest =>
        cases rest with
        | nil => rw [hlin] at hp; cases hp
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            rw [hlin] at hp
            dsimp only at hp ⊢
            cases hra : (if a < w then coreRoot N C a else none) with
            | none => rw [hra] at hp; cases hp
            | some r1' =>
              rw [hra] at hp
              cases hrb : (if b < w then coreRoot N C b else none) with
              | none => rw [hrb] at hp; cases hp
              | some r2' =>
                rw [hrb] at hp
                dsimp only at hp ⊢
                by_cases heq : (r1' == r2') = true
                · simp [heq] at hp
                · simp only [dite_eq_ite]
                  rw [hra, hrb]
                  have hne : r1' ≠ r2' := fun h => heq (beq_iff_eq.mpr h)
                  simp [hne]
          | cons _ _ => rw [hlin] at hp; cases hp

lemma coreRoot_of_isBase {w : ℕ} (hw : w < totalWires N C) (hb : isBaseWire N C w = true) :
    coreRoot N C w = some w := by
  unfold coreRoot
  simp [show ¬(w ≥ totalWires N C) by omega, hb]

def coeffCore (i : ℕ) : ℕ → Bool
  | r =>
    if isBaseWire N C r then decide (r = i)
    else
      match trueParents N C r with
      | some (r1, r2) =>
        xor (if _ : r1 < r then coeffCore i r1 else false)
            (if _ : r2 < r then coeffCore i r2 else false)
      | none => false

lemma coeffCore_base (r i : ℕ) (hb : isBaseWire N C r = true) :
    coeffCore N C i r = decide (r = i) := by
  unfold coeffCore; simp [hb]

lemma coeffCore_trueGate {w r1 r2 : ℕ} (i : ℕ) (hp : trueParents N C w = some (r1, r2)) :
    coeffCore N C i w = xor (coeffCore N C i r1) (coeffCore N C i r2) := by
  have hspec := trueParents_spec N C hp
  conv_lhs => unfold coeffCore
  simp only [hspec.2.1, Bool.false_eq_true, ↓reduceIte, hp, hspec.2.2.1, ↓reduceDIte,
    hspec.2.2.2.1]

def coeffW (i w : ℕ) : Bool :=
  match coreRoot N C w with
  | none => false
  | some r => coeffCore N C i r

lemma coeffW_lt_zero (w i : ℕ) (h : w < i) : coeffW N C i w = false := by
  suffices ∀ r, r < i → coeffCore N C i r = false by
    unfold coeffW
    cases hr : coreRoot N C w with
    | none => rfl
    | some r => exact this r (lt_of_le_of_lt (coreRoot_le N C w r hr) h)
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hri
    unfold coeffCore
    dsimp only
    split_ifs with hb
    · exact decide_eq_false (by omega)
    · cases hp : trueParents N C r with
      | none => rfl
      | some p =>
        obtain ⟨r1, r2⟩ := p
        have hs := trueParents_spec N C hp
        simp only [hs.2.2.1, ↓reduceDIte, hs.2.2.2.1]
        rw [ih r1 hs.2.2.1 (lt_trans hs.2.2.1 hri), ih r2 hs.2.2.2.1 (lt_trans hs.2.2.2.1 hri)]
        rfl

lemma coeffW_step (hrb : ReadsBack (N + N) C) (i j : ℕ) (hj : j < C.gates.length)
    (hnl : isNLGate (gateAt C j) = false) :
    coeffW N C i (N + N + j) =
      (linIns (gateAt C j)).foldl (fun acc a => xor acc (coeffW N C i a)) false := by
  set w := N + N + j
  have hwlt : w < totalWires N C := by unfold totalWires; omega
  have hbaseF : isBaseWire N C w = false := by
    unfold isBaseWire
    simp [w, hj, hnl]
  have hins_lt : ∀ a ∈ linIns (gateAt C j), a < w := fun a ha =>
    hrb j hj a (linIns_sub _ a ha)
  have hroot : coreRoot N C w =
      match linIns (gateAt C j) with
      | [] => none
      | [a] => if a < w then coreRoot N C a else none
      | [a, b] =>
        match (if a < w then coreRoot N C a else none),
              (if b < w then coreRoot N C b else none) with
        | none, rb => rb
        | ra, none => ra
        | some r1, some r2 => if r1 == r2 then none else some w
      | _ => none := by
    conv_lhs => unfold coreRoot
    simp [w, show ¬(N + N + j ≥ totalWires N C) by omega, hbaseF]
  have hlen := linIns_len_le (gateAt C j)
  cases hlin : linIns (gateAt C j) with
  | nil =>
    unfold coeffW; rw [hroot, hlin]; rfl
  | cons a rest =>
    cases rest with
    | nil =>
      have haw : a < w := hins_lt a (by simp [hlin])
      unfold coeffW
      rw [hroot, hlin]
      simp [haw]
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        have haw : a < w := hins_lt a (by simp [hlin])
        have hbw : b < w := hins_lt b (by simp [hlin])
        simp only [List.foldl_cons, List.foldl_nil, Bool.false_xor]
        unfold coeffW
        rw [hroot, hlin]
        simp only [haw, ↓reduceIte, hbw]
        cases hra : coreRoot N C a with
        | none =>
          cases hrb' : coreRoot N C b <;> simp
        | some r1 =>
          cases hrb' : coreRoot N C b with
          | none => simp
          | some r2 =>
            by_cases heq : r1 = r2
            · subst heq; simp
            · have hbeq : (r1 == r2) = false := beq_false_of_ne heq
              simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
              have htp : trueParents N C w = some (r1, r2) := by
                unfold trueParents
                simp [w, show ¬(N + N + j ≥ totalWires N C) by omega, hbaseF, hlin, haw, hbw,
                  hra, hrb', hbeq]
              exact coeffCore_trueGate N C i htp
      | cons c rest3 =>
        rw [hlin] at hlen; simp at hlen

def constW : ℕ → Bool
  | w =>
    if w ≥ totalWires N C then false
    else if isBaseWire N C w then false
    else
      (linIns (gateAt C (w - (N + N)))).foldl
        (fun acc a => xor acc (if _ : a < w then constW a else false))
        (linConst (gateAt C (w - (N + N))))

lemma constW_step (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : j < C.gates.length)
    (hnl : isNLGate (gateAt C j) = false) :
    constW N C (N + N + j) =
      (linIns (gateAt C j)).foldl (fun acc a => xor acc (constW N C a)) (linConst (gateAt C j)) := by
  set w := N + N + j
  have hbaseF : isBaseWire N C w = false := by unfold isBaseWire; simp [w, hj, hnl]
  conv_lhs => unfold constW
  simp only [show ¬(w ≥ totalWires N C) by unfold totalWires; omega, ↓reduceIte, hbaseF, w,
    Nat.add_sub_cancel_left]
  have hins : ∀ a ∈ linIns (gateAt C j), a < N + N + j := fun a ha =>
    hrb j hj a (linIns_sub _ a ha)
  generalize linConst (gateAt C j) = init
  generalize linIns (gateAt C j) = l at hins ⊢
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    have ha : a < N + N + j := hins a List.mem_cons_self
    simp only [ha, ↓reduceDIte]
    exact ih _ (fun x hx => hins x (List.mem_cons_of_mem _ hx))

lemma foldl_xor_assoc (l : List ℕ) (f : ℕ → Bool) (c : Bool) :
    l.foldl (fun acc a => xor acc (f a)) c = xor c (l.foldl (fun acc a => xor acc (f a)) false) := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor c (f a)), ih (f a), Bool.xor_assoc]

lemma foldl_xor_xor (l : List ℕ) (f g : ℕ → Bool) :
    l.foldl (fun acc a => xor acc (xor (f a) (g a))) false =
      xor (l.foldl (fun acc a => xor acc (f a)) false)
          (l.foldl (fun acc a => xor acc (g a)) false) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [foldl_xor_assoc l (fun x => xor (f x) (g x)), ih,
      foldl_xor_assoc l f (f a), foldl_xor_assoc l g (g a)]
    cases f a <;> cases g a <;> cases l.foldl (fun acc a => xor acc (f a)) false <;>
      cases l.foldl (fun acc a => xor acc (g a)) false <;> rfl

lemma foldl_xor_xorSum {α : Type*} [DecidableEq α] (l : List ℕ) (S : Finset α)
    (f : ℕ → α → Bool) :
    l.foldl (fun acc a => xor acc (xorSum S (f a))) false =
      xorSum S (fun k => l.foldl (fun acc a => xor acc (f a k)) false) := by
  induction l with
  | nil => simp [xorSum_false]
  | cons a l ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [foldl_xor_assoc l (fun x => xorSum S (f x)), ih, ← xorSum_xor]
    exact xorSum_congr rfl (fun k _ => (foldl_xor_assoc l (fun x => f x k) (f a k)).symm)

lemma affine_repr (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (N + N) C)
    (u v : Fin N) (w : ℕ) (hw : w < totalWires N C) :
    (C.wires (oneEach u v)).getD w false =
      xor (constW N C w)
        (xor (coeffW N C u.val w)
          (xor (coeffW N C (N + v.val) w)
            (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
              coeffW N C (nlWire N C k) w &&
                (C.wires (oneEach u v)).getD (nlWire N C k) false)))) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hltN : w < N
    · have hb : isBaseWire N C w = true := by unfold isBaseWire; simp [show w < N + N by omega]
      have hcw : constW N C w = false := by
        unfold constW; simp [show ¬(w ≥ totalWires N C) by omega, hb]
      have hroot : coreRoot N C w = some w := coreRoot_of_isBase N C hw hb
      have hL : coeffW N C u.val w = decide (w = u.val) := by
        unfold coeffW; rw [hroot]; exact coeffCore_base N C w u.val hb
      have hR : coeffW N C (N + v.val) w = false := by
        unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]; exact decide_eq_false (by omega)
      have hQ : ∀ k : Fin (tCount C), coeffW N C (nlWire N C k) w = false := by
        intro k; unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]
        unfold nlWire; exact decide_eq_false (by omega)
      rw [wireVal_left C u v w hltN, hcw, hL, hR,
        xorSum_congr rfl (g := fun _ => false) (fun k _ => by rw [hQ k]; rfl), xorSum_false]
      simp
    · by_cases hlt2N : w < N + N
      · have hb : isBaseWire N C w = true := by unfold isBaseWire; simp [hlt2N]
        have hcw : constW N C w = false := by
          unfold constW; simp [show ¬(w ≥ totalWires N C) by omega, hb]
        have hroot : coreRoot N C w = some w := coreRoot_of_isBase N C hw hb
        have hL : coeffW N C u.val w = false := by
          unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]; exact decide_eq_false (by omega)
        have hR : coeffW N C (N + v.val) w = decide (w - N = v.val) := by
          unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]
          by_cases h : w = N + v.val <;> simp [h] <;> omega
        have hQ : ∀ k : Fin (tCount C), coeffW N C (nlWire N C k) w = false := by
          intro k; unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]
          unfold nlWire; exact decide_eq_false (by omega)
        have hweq : w = N + (w - N) := by omega
        have hsublt : w - N < N := by omega
        rw [hweq, wireVal_right C u v (w - N) hsublt, ← hweq, hcw, hL, hR,
          xorSum_congr rfl (g := fun _ => false) (fun k _ => by rw [hQ k]; rfl), xorSum_false]
        simp
      · set j := w - (N + N)
        have hwj : w = N + N + j := by omega
        have hjlt : j < C.gates.length := by unfold totalWires at hw; omega
        by_cases hnl : isNLGate (gateAt C j) = true
        · obtain ⟨k0, hk0⟩ := nlIndices_exists C hjlt hnl
          have hwk0 : w = nlWire N C k0 := by unfold nlWire; omega
          have hb : isBaseWire N C w = true := by rw [hwk0]; exact isBaseWire_nl N C k0
          have hcw : constW N C w = false := by
            unfold constW; simp [show ¬(w ≥ totalWires N C) by omega, hb]
          have hroot : coreRoot N C w = some w := coreRoot_of_isBase N C hw hb
          have hL : coeffW N C u.val w = false := by
            unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]; exact decide_eq_false (by omega)
          have hR : coeffW N C (N + v.val) w = false := by
            unfold coeffW; rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb]; exact decide_eq_false (by omega)
          have hQ : ∀ k : Fin (tCount C),
              coeffW N C (nlWire N C k) w = decide (k = k0) := by
            intro k
            unfold coeffW
            rw [hroot]; dsimp only; rw [coeffCore_base N C w _ hb, hwk0]
            by_cases hk : k = k0
            · subst hk; simp
            · rw [decide_eq_false hk]
              refine decide_eq_false (fun heq => hk ?_)
              have hidx : (nlIndices C)[k0.val]'(by rw [nlIndices_length]; exact k0.isLt) =
                  (nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt) := by
                unfold nlWire at heq; omega
              rcases lt_trichotomy k k0 with hlt | rfl | hgt
              · exact absurd hidx (ne_of_gt (nlIndices_strictMono C hlt))
              · rfl
              · exact absurd hidx (ne_of_lt (nlIndices_strictMono C hgt))
          rw [hcw, hL, hR,
            xorSum_congr rfl (fun k _ => by rw [hQ k]),
            xorSum_eq_ite]
          simp [hwk0]
        · have hnlF : isNLGate (gateAt C j) = false := Bool.eq_false_iff.mpr hnl
          have hglen : (gateAt C j).inputs.length ≤ 2 := by
            have hmem : gateAt C j ∈ C.gates := by
              unfold gateAt
              rw [List.getD_eq_getElem _ _ hjlt]
              exact List.getElem_mem hjlt
            exact hfan _ hmem
          rw [hwj, wireVal_gate C hrb u v j hjlt, lin_gate_eval _ hglen hnlF,
            constW_step N C hrb j hjlt hnlF, coeffW_step N C hrb u.val j hjlt hnlF,
            coeffW_step N C hrb (N + v.val) j hjlt hnlF]
          have hQstep : xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
              coeffW N C (nlWire N C k) (N + N + j) &&
                (C.wires (oneEach u v)).getD (nlWire N C k) false) =
              (linIns (gateAt C j)).foldl (fun acc a => xor acc
                (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
                  coeffW N C (nlWire N C k) a &&
                    (C.wires (oneEach u v)).getD (nlWire N C k) false))) false := by
            rw [foldl_xor_xorSum]
            apply xorSum_congr rfl
            intro k _
            rw [coeffW_step N C hrb (nlWire N C k) j hjlt hnlF]
            set c := (C.wires (oneEach u v)).getD (nlWire N C k) false
            cases c
            · simp only [Bool.and_false]
              generalize linIns (gateAt C j) = l'
              induction l' with
              | nil => rfl
              | cons a l ih' => rw [List.foldl_cons, Bool.xor_false]; exact ih'
            · simp only [Bool.and_true]
          rw [hQstep, foldl_xor_assoc (linIns (gateAt C j)) (constW N C)]
          have hcomb : ∀ (l : List ℕ) (c0 : Bool) (f1 f2 f3 f4 : ℕ → Bool),
              xor (xor c0 (l.foldl (fun acc a => xor acc (f1 a)) false))
                (xor (l.foldl (fun acc a => xor acc (f2 a)) false)
                  (xor (l.foldl (fun acc a => xor acc (f3 a)) false)
                    (l.foldl (fun acc a => xor acc (f4 a)) false))) =
              l.foldl (fun acc a => xor acc (xor (f1 a) (xor (f2 a) (xor (f3 a) (f4 a))))) c0 := by
            intro l c0 f1 f2 f3 f4
            rw [Bool.xor_assoc, ← foldl_xor_xor l f3 f4, ← foldl_xor_xor l f2, ← foldl_xor_xor l f1,
              ← foldl_xor_assoc l _ c0]
          rw [hcomb]
          have hins : ∀ a ∈ linIns (gateAt C j), a < N + N + j := fun a ha =>
            hrb j hjlt a (linIns_sub _ a ha)
          have hcongr : ∀ (l : List ℕ) (init : Bool), (∀ a ∈ l, a < w) →
              l.foldl (fun acc a => xor acc ((C.wires (oneEach u v)).getD a false)) init =
              l.foldl (fun acc a => xor acc
                (xor (constW N C a)
                  (xor (coeffW N C u.val a)
                    (xor (coeffW N C (N + v.val) a)
                      (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
                        coeffW N C (nlWire N C k) a &&
                          (C.wires (oneEach u v)).getD (nlWire N C k) false)))))) init := by
            intro l
            induction l with
            | nil => intro init _; rfl
            | cons a l ihl =>
              intro init hl
              simp only [List.foldl_cons]
              have haw : a < w := hl a List.mem_cons_self
              rw [ih a haw (lt_trans haw hw)]
              exact ihl _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
          exact hcongr (linIns (gateAt C j)) (linConst (gateAt C j)) (by simpa [hwj] using hins)


def termWire (r : Fin (2 * tCount C + 1)) : ℕ :=
  if h : r.val < 2 * tCount C then
    let k : Fin (tCount C) := ⟨r.val / 2, by omega⟩
    let g := gateAt C ((nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt))
    if r.val % 2 = 0 then g.inputs.getD 0 0 else g.inputs.getD 1 0
  else
    C.output

lemma nlGate_inputs_eq (k : Fin (tCount C)) :
    let g := gateAt C ((nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt))
    g.inputs = [termWire C ⟨2 * k.val, by omega⟩, termWire C ⟨2 * k.val + 1, by omega⟩] := by
  have hnl := nlIndices_isNL C k
  unfold isNLGate at hnl
  have hlen : (gateAt C ((nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt))).inputs.length = 2 := by
    have := (Bool.and_eq_true _ _).mp hnl
    exact beq_iff_eq.mp this.1
  rcases h : (gateAt C ((nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt))).inputs with
    _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · unfold termWire
    have h0 : 2 * k.val < 2 * tCount C := by omega
    have h1 : 2 * k.val + 1 < 2 * tCount C := by omega
    have hd0 : (2 * k.val) / 2 = k.val := by omega
    have hd1 : (2 * k.val + 1) / 2 = k.val := by omega
    have hm0 : (2 * k.val) % 2 = 0 := by omega
    have hm1 : (2 * k.val + 1) % 2 ≠ 0 := by omega
    simp [h0, h1, hd0, hd1, hm0, hm1, h]
  · simp [h] at hlen

lemma termWire_nl_lt (hrb : ReadsBack (N + N) C) (k : Fin (tCount C)) (b : Fin 2) :
    termWire C ⟨2 * k.val + b.val, by omega⟩ < nlWire N C k := by
  have heq := nlGate_inputs_eq C k
  have hmem : termWire C ⟨2 * k.val + b.val, by omega⟩ ∈
      (gateAt C ((nlIndices C)[k.val]'(by rw [nlIndices_length]; exact k.isLt))).inputs := by
    fin_cases b <;> simp [heq]
  exact hrb _ (nlIndices_lt C k) _ hmem

def psiL (u : Fin N) : Fin (2 * tCount C) → Bool :=
  fun r => coeffW N C u.val (termWire C ⟨r.val, by omega⟩)

def psiR (v : Fin N) : Fin (2 * tCount C) → Bool :=
  fun r => coeffW N C (N + v.val) (termWire C ⟨r.val, by omega⟩)

def nlFunc (hrb : ReadsBack (N + N) C) (xi : Fin (2 * tCount C) → Bool) :
    (k : ℕ) → k < tCount C → Bool
  | k, hk =>
    let kFin : Fin (tCount C) := ⟨k, hk⟩
    let g := gateAt C ((nlIndices C)[k]'(by rw [nlIndices_length]; exact hk))
    let r0 : Fin (2 * tCount C) := ⟨2 * k, by omega⟩
    let r1 : Fin (2 * tCount C) := ⟨2 * k + 1, by omega⟩
    let w0 := termWire C ⟨2 * k, by omega⟩
    let w1 := termWire C ⟨2 * k + 1, by omega⟩
    let v0 := xor (constW N C w0) (xor (xi r0)
      (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun m =>
        if hm : m.val < k then
          coeffW N C (nlWire N C m) w0 && nlFunc hrb xi m.val (lt_trans hm hk)
        else false)))
    let v1 := xor (constW N C w1) (xor (xi r1)
      (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun m =>
        if hm : m.val < k then
          coeffW N C (nlWire N C m) w1 && nlFunc hrb xi m.val (lt_trans hm hk)
        else false)))
    g.op.eval [v0, v1]

lemma nlFunc_correct (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (N + N) C)
    (u v : Fin N) (k : Fin (tCount C)) :
    (C.wires (oneEach u v)).getD (nlWire N C k) false =
      nlFunc N C hrb (fun r => xor (psiL N C u r) (psiR N C v r)) k.val k.isLt := by
  obtain ⟨kv, hkv⟩ := k
  induction kv using Nat.strong_induction_on with
  | _ kv ih =>
    set k : Fin (tCount C) := ⟨kv, hkv⟩
    set idx := (nlIndices C)[kv]'(by rw [nlIndices_length]; exact hkv)
    have hidx_lt : idx < C.gates.length := nlIndices_lt C k
    have hnlw : nlWire N C k = N + N + idx := rfl
    rw [hnlw, wireVal_gate C hrb u v idx hidx_lt]
    have hins := nlGate_inputs_eq C k
    rw [hins, List.map_cons, List.map_cons, List.map_nil]
    unfold nlFunc
    dsimp only
    congr 1
    have hterm : ∀ b : Fin 2,
        (C.wires (oneEach u v)).getD (termWire C ⟨2 * kv + b.val, by omega⟩) false =
        xor (constW N C (termWire C ⟨2 * kv + b.val, by omega⟩))
          (xor (xor (psiL N C u ⟨2 * kv + b.val, by omega⟩)
                    (psiR N C v ⟨2 * kv + b.val, by omega⟩))
            (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun m =>
              if hm : m.val < kv then
                coeffW N C (nlWire N C m) (termWire C ⟨2 * kv + b.val, by omega⟩) &&
                  nlFunc N C hrb (fun r => xor (psiL N C u r) (psiR N C v r)) m.val (lt_trans hm hkv)
              else false))) := by
      intro b
      set tw := termWire C ⟨2 * kv + b.val, by omega⟩
      have htw_lt : tw < nlWire N C k := termWire_nl_lt N C hrb k b
      have htw_tot : tw < totalWires N C := by
        unfold totalWires nlWire at *; omega
      rw [affine_repr N C hfan hrb u v tw htw_tot]
      have hassoc : ∀ a b c d : Bool, xor a (xor b (xor c d)) = xor a (xor (xor b c) d) := by
        intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> rfl
      rw [hassoc]
      congr 2
      apply xorSum_congr rfl
      intro m _
      by_cases hm : m.val < kv
      · simp only [hm, ↓reduceDIte]
        rw [ih m.val hm m.isLt]
      · simp only [hm, ↓reduceDIte]
        have hle : nlWire N C k ≤ nlWire N C m := by
          by_cases heq : m.val = kv
          · have : m = k := Fin.ext heq; rw [this]
          · have hlt : k < m := by change kv < m.val; omega
            have := nlIndices_strictMono C hlt
            unfold nlWire; omega
        have hlt_m : tw < nlWire N C m := lt_of_lt_of_le htw_lt hle
        rw [coeffW_lt_zero N C tw (nlWire N C m) hlt_m]
        rfl
    have h0 := hterm ⟨0, by omega⟩
    have h1 := hterm ⟨1, by omega⟩
    simp only [Nat.add_zero] at h0
    rw [h0, h1]

def nlOutFunc (hrb : ReadsBack (N + N) C) (xi : Fin (2 * tCount C) → Bool) : Bool :=
  if C.output < totalWires N C then
    xor (constW N C C.output)
      (xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
        coeffW N C (nlWire N C k) C.output && nlFunc N C hrb xi k.val k.isLt))
  else false

lemma eval_factor (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (N + N) C)
    (u v : Fin N) :
    C.eval (oneEach u v) =
      xor (coeffW N C u.val C.output)
        (xor (coeffW N C (N + v.val) C.output)
          (nlOutFunc N C hrb (fun r => xor (psiL N C u r) (psiR N C v r)))) := by
  unfold Circuit.eval nlOutFunc
  by_cases hout : C.output < totalWires N C
  · simp only [hout, ↓reduceIte]
    rw [affine_repr N C hfan hrb u v C.output hout]
    have hsum : xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
        coeffW N C (nlWire N C k) C.output &&
          (C.wires (oneEach u v)).getD (nlWire N C k) false) =
        xorSum (Finset.univ : Finset (Fin (tCount C))) (fun k =>
          coeffW N C (nlWire N C k) C.output &&
            nlFunc N C hrb (fun r => xor (psiL N C u r) (psiR N C v r)) k.val k.isLt) :=
      xorSum_congr rfl (fun k _ => by rw [nlFunc_correct N C hfan hrb u v k])
    rw [hsum]
    generalize constW N C C.output = c0
    generalize coeffW N C u.val C.output = cL
    generalize coeffW N C (N + v.val) C.output = cR
    generalize xorSum (Finset.univ : Finset (Fin (tCount C))) _ = cQ
    cases c0 <;> cases cL <;> cases cR <;> cases cQ <;> rfl
  · simp only [hout, ↓reduceIte]
    have hlen : (C.wires (oneEach u v)).length = totalWires N C := by
      rw [wires_eq_foldl, foldl_stepWires_length, oneEach_length]; rfl
    have hdef : (C.wires (oneEach u v)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    have hroot : coreRoot N C C.output = none := by
      unfold coreRoot; simp [show C.output ≥ totalWires N C by omega]
    simp only [hdef, coeffW, hroot]; rfl

lemma psiL_injective {H : Fin N → Fin N → Bool}
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (N + N) C)
    (hrep : Represents H C)
    (hrow : ∀ u₁ u₂ c, (∀ v, H u₁ v = xor (H u₂ v) c) → u₁ = u₂) :
    Function.Injective (psiL N C) := by
  intro u₁ u₂ hpsi
  apply hrow u₁ u₂ (xor (coeffW N C u₁.val C.output) (coeffW N C u₂.val C.output))
  intro v
  rw [← hrep u₁ v, ← hrep u₂ v, eval_factor N C hfan hrb u₁ v, eval_factor N C hfan hrb u₂ v, hpsi]
  cases coeffW N C u₁.val C.output <;> cases coeffW N C u₂.val C.output <;>
    cases coeffW N C (N + v.val) C.output <;>
    cases nlOutFunc N C hrb (fun r => xor (psiL N C u₂ r) (psiR N C v r)) <;> rfl

lemma psiR_injective {H : Fin N → Fin N → Bool}
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (N + N) C)
    (hrep : Represents H C)
    (hcol : ∀ v₁ v₂ c, (∀ u, H u v₁ = xor (H u v₂) c) → v₁ = v₂) :
    Function.Injective (psiR N C) := by
  intro v₁ v₂ hpsi
  apply hcol v₁ v₂ (xor (coeffW N C (N + v₁.val) C.output) (coeffW N C (N + v₂.val) C.output))
  intro u
  rw [← hrep u v₁, ← hrep u v₂, eval_factor N C hfan hrb u v₁, eval_factor N C hfan hrb u v₂, hpsi]
  cases coeffW N C u.val C.output <;> cases coeffW N C (N + v₁.val) C.output <;>
    cases coeffW N C (N + v₂.val) C.output <;>
    cases nlOutFunc N C hrb (fun r => xor (psiL N C u r) (psiR N C v₂ r)) <;> rfl

lemma tCount_eq_s {s : ℕ} {H : Fin (4 ^ s) → Fin (4 ^ s) → Bool}
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (4 ^ s + 4 ^ s) C)
    (hrep : Represents H C) (htle : tCount C ≤ s)
    (hrow : ∀ u₁ u₂ c, (∀ v, H u₁ v = xor (H u₂ v) c) → u₁ = u₂) :
    tCount C = s := by
  have hinj := psiL_injective (4 ^ s) C hfan hrb hrep hrow
  have hcard : Fintype.card (Fin (4 ^ s)) ≤ Fintype.card (Fin (2 * tCount C) → Bool) :=
    Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hcard
  rw [four_pow_eq_two_pow] at hcard
  have hle : 2 * s ≤ 2 * tCount C := (Nat.pow_le_pow_iff_right (by omega)).mp hcard
  omega

lemma nlGate_used {s : ℕ} {H : Fin (4 ^ s) → Fin (4 ^ s) → Bool}
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (4 ^ s + 4 ^ s) C)
    (hrep : Represents H C) (hteq : tCount C = s)
    (hrow : ∀ u₁ u₂ c, (∀ v, H u₁ v = xor (H u₂ v) c) → u₁ = u₂)
    (k0 : Fin (tCount C)) :
    ∃ r : Fin (2 * tCount C + 1), coeffW (4 ^ s) C (nlWire (4 ^ s) C k0) (termWire C r) = true := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ r : Fin (2 * tCount C + 1),
      coeffW (4 ^ s) C (nlWire (4 ^ s) C k0) (termWire C r) = false := fun r =>
    Bool.eq_false_iff.mpr (hnone r)
  have hnl_indep : ∀ (xi₁ xi₂ : Fin (2 * tCount C) → Bool),
      (∀ r : Fin (2 * tCount C), r.val / 2 ≠ k0.val → xi₁ r = xi₂ r) →
      ∀ (k : ℕ) (hk : k < tCount C), k ≠ k0.val →
        nlFunc (4 ^ s) C hrb xi₁ k hk = nlFunc (4 ^ s) C hrb xi₂ k hk := by
    intro xi₁ xi₂ hxi k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hne
      unfold nlFunc
      dsimp only
      have h0 : xi₁ ⟨2 * k, by omega⟩ = xi₂ ⟨2 * k, by omega⟩ :=
        hxi ⟨2 * k, by omega⟩ (by dsimp only; omega)
      have h1 : xi₁ ⟨2 * k + 1, by omega⟩ = xi₂ ⟨2 * k + 1, by omega⟩ :=
        hxi ⟨2 * k + 1, by omega⟩ (by dsimp only; omega)
      have hsum : ∀ b : Fin 2,
          xorSum (Finset.univ : Finset (Fin (tCount C))) (fun m =>
            if hm : m.val < k then
              coeffW (4 ^ s) C (nlWire (4 ^ s) C m) (termWire C ⟨2 * k + b.val, by omega⟩) &&
                nlFunc (4 ^ s) C hrb xi₁ m.val (lt_trans hm hk)
            else false) =
          xorSum (Finset.univ : Finset (Fin (tCount C))) (fun m =>
            if hm : m.val < k then
              coeffW (4 ^ s) C (nlWire (4 ^ s) C m) (termWire C ⟨2 * k + b.val, by omega⟩) &&
                nlFunc (4 ^ s) C hrb xi₂ m.val (lt_trans hm hk)
            else false) := by
        intro b
        apply xorSum_congr rfl
        intro m _
        by_cases hm : m.val < k
        · simp only [hm, ↓reduceDIte]
          by_cases hmk0 : m = k0
          · subst hmk0
            rw [hall ⟨2 * k + b.val, by omega⟩]; simp
          · rw [ih m.val hm (lt_trans hm hk) (fun h => hmk0 (Fin.ext h))]
        · simp [hm]
      have hs0 := hsum ⟨0, by omega⟩
      have hs1 := hsum ⟨1, by omega⟩
      simp only [Nat.add_zero] at hs0
      rw [h0, h1, hs0, hs1]
  have hout_indep : ∀ (xi₁ xi₂ : Fin (2 * tCount C) → Bool),
      (∀ r : Fin (2 * tCount C), r.val / 2 ≠ k0.val → xi₁ r = xi₂ r) →
      nlOutFunc (4 ^ s) C hrb xi₁ = nlOutFunc (4 ^ s) C hrb xi₂ := by
    intro xi₁ xi₂ hxi
    unfold nlOutFunc
    split_ifs
    · congr 1
      apply xorSum_congr rfl
      intro m _
      by_cases hmk0 : m = k0
      · subst hmk0
        have hout_term : termWire C ⟨2 * tCount C, by omega⟩ = C.output := by
          unfold termWire; simp
        have h0 := hall ⟨2 * tCount C, by omega⟩
        rw [hout_term] at h0
        rw [h0]; simp
      · rw [hnl_indep xi₁ xi₂ hxi m.val m.isLt (fun h => hmk0 (Fin.ext h))]
    · rfl
  let drop : Fin (4 ^ s) → ({r : Fin (2 * tCount C) // r.val / 2 ≠ k0.val} → Bool) :=
    fun u r => psiL (4 ^ s) C u r.1
  have hinj : Function.Injective drop := by
    intro u₁ u₂ hdrop
    apply hrow u₁ u₂ (xor (coeffW (4 ^ s) C u₁.val C.output) (coeffW (4 ^ s) C u₂.val C.output))
    intro v
    rw [← hrep u₁ v, ← hrep u₂ v, eval_factor (4 ^ s) C hfan hrb u₁ v,
      eval_factor (4 ^ s) C hfan hrb u₂ v]
    have hxi : ∀ r : Fin (2 * tCount C), r.val / 2 ≠ k0.val →
        xor (psiL (4 ^ s) C u₁ r) (psiR (4 ^ s) C v r) =
        xor (psiL (4 ^ s) C u₂ r) (psiR (4 ^ s) C v r) := by
      intro r hr
      have := congrFun hdrop ⟨r, hr⟩
      simp only [drop] at this
      rw [this]
    rw [hout_indep _ _ hxi]
    cases coeffW (4 ^ s) C u₁.val C.output <;> cases coeffW (4 ^ s) C u₂.val C.output <;>
      cases coeffW (4 ^ s) C (4 ^ s + v.val) C.output <;>
      cases nlOutFunc (4 ^ s) C hrb (fun r => xor (psiL (4 ^ s) C u₂ r) (psiR (4 ^ s) C v r)) <;> rfl
  have hcard : Fintype.card (Fin (4 ^ s)) ≤
      Fintype.card ({r : Fin (2 * tCount C) // r.val / 2 ≠ k0.val} → Bool) :=
    Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hcard
  have hsubcard : Fintype.card {r : Fin (2 * tCount C) // r.val / 2 ≠ k0.val} + 2 ≤ 2 * tCount C := by
    let pair : Finset (Fin (2 * tCount C)) := {⟨2 * k0.val, by omega⟩, ⟨2 * k0.val + 1, by omega⟩}
    have hdisj : Disjoint (Finset.univ.filter (fun r : Fin (2 * tCount C) => r.val / 2 ≠ k0.val)) pair := by
      rw [Finset.disjoint_right]
      intro r hr
      simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rcases hr with rfl | rfl <;> (dsimp only; omega)
    have hpair_card : pair.card = 2 := by
      rw [Finset.card_pair]
      intro h; have := congrArg Fin.val h; dsimp only at this; omega
    have hle := Finset.card_le_univ
      ((Finset.univ.filter (fun r : Fin (2 * tCount C) => r.val / 2 ≠ k0.val)) ∪ pair)
    rw [Finset.card_union_of_disjoint hdisj, hpair_card, Fintype.card_fin] at hle
    rw [Fintype.card_subtype]
    exact hle
  rw [four_pow_eq_two_pow] at hcard
  have hpow := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard
  omega


def isParentOf (w g : ℕ) : Bool :=
  match trueParents N C g with
  | some (r1, r2) => decide (r1 = w) || decide (r2 = w)
  | none => false

lemma isParentOf_lt {w g : ℕ} (h : isParentOf N C w g = true) : w < g := by
  unfold isParentOf at h
  cases hp : trueParents N C g with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨r1, r2⟩ := p
    rw [hp] at h
    have hs := trueParents_spec N C hp
    rcases Bool.or_eq_true_iff.mp h with h1 | h2
    · rw [← of_decide_eq_true h1]; exact hs.2.2.1
    · rw [← of_decide_eq_true h2]; exact hs.2.2.2.1

def termRoot (r : Fin (2 * tCount C + 1)) : Option ℕ :=
  coreRoot N C (termWire C r)

def isLiveAux : ℕ → ℕ → Bool
  | 0, _ => false
  | d + 1, w =>
    if w ≥ totalWires N C then false
    else
      ((Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
          (fun r => termRoot N C r = some w)).Nonempty ||
      ((Finset.range (totalWires N C)).filter
          (fun g => w < g && isParentOf N C w g && isLiveAux d g)).Nonempty

def isLive (w : ℕ) : Bool :=
  isLiveAux N C (totalWires N C - w) w

lemma isLiveAux_mono (d₁ d₂ w : ℕ) (hd : totalWires N C - w ≤ d₁) (hd2 : totalWires N C - w ≤ d₂) :
    isLiveAux N C d₁ w = isLiveAux N C d₂ w := by
  induction hgap : totalWires N C - w using Nat.strong_induction_on generalizing d₁ d₂ w with
  | _ gap ih =>
    cases d₁ with
    | zero =>
      have hw : w ≥ totalWires N C := by omega
      cases d₂ with
      | zero => rfl
      | succ d₂ => unfold isLiveAux; simp [hw]
    | succ d₁ =>
      cases d₂ with
      | zero =>
        have hw : w ≥ totalWires N C := by omega
        unfold isLiveAux; simp [hw]
      | succ d₂ =>
        unfold isLiveAux
        split_ifs with hw
        · rfl
        · congr 1
          congr 1
          congr 1
          ext g
          simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq]
          constructor <;> rintro ⟨hgt, ⟨h1, h2⟩, h3⟩
          · refine ⟨hgt, ⟨h1, h2⟩, ?_⟩
            rw [← ih (totalWires N C - g) (by omega) d₁ d₂ g (by omega) (by omega) rfl]; exact h3
          · refine ⟨hgt, ⟨h1, h2⟩, ?_⟩
            rw [ih (totalWires N C - g) (by omega) d₁ d₂ g (by omega) (by omega) rfl]; exact h3

lemma isLive_eq (w : ℕ) (hw : w < totalWires N C) :
    isLive N C w =
      (((Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
          (fun r => termRoot N C r = some w)).Nonempty ||
       ((Finset.range (totalWires N C)).filter
          (fun g => w < g && isParentOf N C w g && isLive N C g)).Nonempty) := by
  conv_lhs => unfold isLive
  have hsub : totalWires N C - w = (totalWires N C - w - 1) + 1 := by omega
  rw [hsub]
  unfold isLiveAux
  simp only [show ¬(w ≥ totalWires N C) by omega, ↓reduceIte]
  congr 1; congr 1; congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro ⟨hgt, ⟨h1, h2⟩, h3⟩
  · refine ⟨hgt, ⟨h1, h2⟩, ?_⟩
    rw [isLiveAux_mono N C (totalWires N C - w - 1) (totalWires N C - g) g (by omega) le_rfl] at h3
    exact h3
  · refine ⟨hgt, ⟨h1, h2⟩, ?_⟩
    rw [isLiveAux_mono N C (totalWires N C - w - 1) (totalWires N C - g) g (by omega) le_rfl]
    exact h3

def adjVecAux : ℕ → ℕ → Fin (2 * tCount C + 1) → Bool
  | 0, _, _ => false
  | d + 1, w, r =>
    if w ≥ totalWires N C then false
    else
      xor (decide (termRoot N C r = some w))
        (xorSum ((Finset.range (totalWires N C)).filter
          (fun g => w < g && isLive N C g && isParentOf N C w g))
          (fun g => adjVecAux d g r))

def adjVec (w : ℕ) (r : Fin (2 * tCount C + 1)) : Bool :=
  adjVecAux N C (totalWires N C - w) w r

lemma adjVecAux_mono (d₁ d₂ w : ℕ) (r : Fin (2 * tCount C + 1))
    (hd1 : totalWires N C - w ≤ d₁) (hd2 : totalWires N C - w ≤ d₂) :
    adjVecAux N C d₁ w r = adjVecAux N C d₂ w r := by
  induction hgap : totalWires N C - w using Nat.strong_induction_on generalizing d₁ d₂ w with
  | _ gap ih =>
    cases d₁ with
    | zero =>
      have hw : w ≥ totalWires N C := by omega
      cases d₂ with
      | zero => rfl
      | succ d₂ => unfold adjVecAux; simp [hw]
    | succ d₁ =>
      cases d₂ with
      | zero =>
        have hw : w ≥ totalWires N C := by omega
        unfold adjVecAux; simp [hw]
      | succ d₂ =>
        unfold adjVecAux
        split_ifs with hw
        · rfl
        · congr 1
          apply xorSum_congr rfl
          intro g hg
          have hwg : w < g := by
            have := (Finset.mem_filter.mp hg).2
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.1
          exact ih (totalWires N C - g) (by omega) d₁ d₂ g (by omega) (by omega) rfl

lemma adjVec_eq (w : ℕ) (hw : w < totalWires N C) (r : Fin (2 * tCount C + 1)) :
    adjVec N C w r =
      xor (decide (termRoot N C r = some w))
        (xorSum ((Finset.range (totalWires N C)).filter
          (fun g => isLive N C g && isParentOf N C w g))
          (fun g => adjVec N C g r)) := by
  conv_lhs => unfold adjVec
  have hsub : totalWires N C - w = (totalWires N C - w - 1) + 1 := by omega
  rw [hsub]
  unfold adjVecAux
  simp only [show ¬(w ≥ totalWires N C) by omega, ↓reduceIte]
  congr 1
  have hfilt : (Finset.range (totalWires N C)).filter
      (fun g => w < g && isLive N C g && isParentOf N C w g) =
      (Finset.range (totalWires N C)).filter
      (fun g => isLive N C g && isParentOf N C w g) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hg, ⟨_, hl⟩, hp⟩; exact ⟨hg, hl, hp⟩
    · rintro ⟨hg, hl, hp⟩; exact ⟨hg, ⟨isParentOf_lt N C hp, hl⟩, hp⟩
  rw [hfilt]
  apply xorSum_congr rfl
  intro g hg
  have hglt : g < totalWires N C := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hp : isParentOf N C w g = true := (Bool.and_eq_true _ _).mp (Finset.mem_filter.mp hg).2 |>.2
  have hwg := isParentOf_lt N C hp
  exact adjVecAux_mono N C (totalWires N C - w - 1) (totalWires N C - g) g r (by omega) le_rfl

def baseSet : Finset ℕ := (Finset.range (totalWires N C)).filter (fun w => isBaseWire N C w = true)
def liveGateSet : Finset ℕ :=
  (Finset.range (totalWires N C)).filter (fun g => isTrueGate N C g = true ∧ isLive N C g = true)

lemma disjoint_base_liveGate : Disjoint (baseSet N C) (liveGateSet N C) := by
  rw [Finset.disjoint_left]
  intro w hwB hwG
  have hb := (Finset.mem_filter.mp hwB).2
  have hg := (Finset.mem_filter.mp hwG).2.1
  unfold isTrueGate at hg
  cases hp : trueParents N C w with
  | none => rw [hp] at hg; cases hg
  | some p =>
    have hs := trueParents_spec N C hp
    rw [hs.2.1] at hb; cases hb

lemma live_parent_mem {g r1 r2 : ℕ} (hg : g ∈ liveGateSet N C)
    (hp : trueParents N C g = some (r1, r2)) :
    r1 ∈ baseSet N C ∪ liveGateSet N C ∧ r2 ∈ baseSet N C ∪ liveGateSet N C := by
  have hlg : isLive N C g = true := (Finset.mem_filter.mp hg).2.2
  have hglt : g < totalWires N C := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hs := trueParents_spec N C hp
  have hmk : ∀ r, r < g → (isBaseWire N C r = true ∨ isTrueGate N C r = true) →
      isParentOf N C r g = true → r ∈ baseSet N C ∪ liveGateSet N C := by
    intro r hrlt hcore hpar
    have hrw : r < totalWires N C := lt_trans hrlt hglt
    rcases hcore with hb | htg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrw, hb⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrw, htg, ?_⟩)
      rw [isLive_eq N C r hrw]
      apply Bool.or_eq_true_iff.mpr
      right
      rw [decide_eq_true_eq]
      exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hglt, by simp [hrlt, hpar, hlg]⟩⟩
  refine ⟨hmk r1 hs.2.2.1 hs.2.2.2.2.2.1 ?_, hmk r2 hs.2.2.2.1 hs.2.2.2.2.2.2.1 ?_⟩ <;>
    unfold isParentOf <;> simp [hp]

lemma duality {i : ℕ} (hi : i ∈ baseSet N C) (r : Fin (2 * tCount C + 1)) :
    adjVec N C i r = coeffW N C i (termWire C r) := by
  set U := baseSet N C ∪ liveGateSet N C
  have hLHS : xorSum U (fun w => coeffCore N C i w && adjVec N C w r) =
      xor (adjVec N C i r) (xorSum (liveGateSet N C) (fun g => coeffCore N C i g && adjVec N C g r)) := by
    rw [xorSum_union_disjoint (disjoint_base_liveGate N C)]
    congr 1
    rw [xorSum_congr rfl (fun w hw => by
      rw [coeffCore_base N C w i (Finset.mem_filter.mp hw).2])]
    rw [xorSum_eq_ite]
    simp [hi]
  have hRHS : xorSum U (fun w => coeffCore N C i w && adjVec N C w r) =
      xor (coeffW N C i (termWire C r))
        (xorSum (liveGateSet N C) (fun g => coeffCore N C i g && adjVec N C g r)) := by
    have hexp : ∀ w ∈ U, (coeffCore N C i w && adjVec N C w r) =
        xor (coeffCore N C i w && decide (termRoot N C r = some w))
          (xorSum (liveGateSet N C) (fun g =>
            (isParentOf N C w g && coeffCore N C i w) && adjVec N C g r)) := by
      intro w hw
      have hwlt : w < totalWires N C := by
        rcases Finset.mem_union.mp hw with h | h <;> exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
      rw [adjVec_eq N C w hwlt r, Bool.and_xor_distrib_left]
      congr 1
      rw [← xorSum_and_left]
      have hsub : (Finset.range (totalWires N C)).filter
          (fun g => isLive N C g && isParentOf N C w g) =
          (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
        ext g
        simp only [liveGateSet, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
        constructor
        · rintro ⟨hg, hl, hp⟩
          refine ⟨⟨hg, ?_, hl⟩, hp⟩
          unfold isParentOf at hp
          unfold isTrueGate
          cases htp : trueParents N C g with
          | none => rw [htp] at hp; cases hp
          | some _ => rfl
        · rintro ⟨⟨hg, _, hl⟩, hp⟩
          exact ⟨hg, hl, hp⟩
      rw [hsub]
      have hpull : xorSum ((liveGateSet N C).filter (fun g => isParentOf N C w g = true))
          (fun g => coeffCore N C i w && adjVec N C g r) =
          xorSum (liveGateSet N C) (fun g =>
            (isParentOf N C w g && coeffCore N C i w) && adjVec N C g r) := by
        have hstep := xorSum_subset_zero (S := (liveGateSet N C).filter (fun g => isParentOf N C w g = true))
          (T := liveGateSet N C) (Finset.filter_subset _ _)
          (fun g => (isParentOf N C w g && coeffCore N C i w) && adjVec N C g r)
          (fun g hg hnot => by
            have hfalse : isParentOf N C w g = false := by
              by_contra hne
              exact hnot (Finset.mem_filter.mpr ⟨hg, Bool.eq_true_of_not_eq_false hne⟩)
            simp [hfalse])
        rw [← hstep]
        apply xorSum_congr rfl
        intro g hg
        have hp := (Finset.mem_filter.mp hg).2
        simp [hp]
      exact hpull
    rw [xorSum_congr rfl hexp, xorSum_xor, xorSum_comm]
    congr 1
    · unfold coeffW termRoot
      cases htr : coreRoot N C (termWire C r) with
      | none =>
        rw [xorSum_congr rfl (fun w _ => show (coeffCore N C i w && decide (none = some w)) = false by simp),
          xorSum_false]
      | some t0 =>
        have ht0_spec := coreRoot_spec N C (termWire C r) t0 htr
        have ht0_live : isLive N C t0 = true := by
          rw [isLive_eq N C t0 ht0_spec.1]
          apply Bool.or_eq_true_iff.mpr
          left
          rw [decide_eq_true_eq]
          exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, htr⟩⟩
        have ht0_mem : t0 ∈ U := by
          rcases ht0_spec.2 with hb | htg
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht0_spec.1, hb⟩)
          · exact Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht0_spec.1, htg, ht0_live⟩)
        rw [xorSum_congr rfl (fun w _ => by
          have : decide (some t0 = some w) = decide (w = t0) := by
            by_cases h : w = t0
            · subst h; simp
            · simp [h, Ne.symm h]
          rw [this, Bool.and_comm])]
        rw [xorSum_eq_ite]
        simp [ht0_mem]
    · apply xorSum_congr rfl
      intro g hg
      rw [xorSum_and_right]
      congr 1
      have htg : isTrueGate N C g = true := (Finset.mem_filter.mp hg).2.1
      unfold isTrueGate at htg
      cases htp : trueParents N C g with
      | none => rw [htp] at htg; cases htg
      | some p =>
        obtain ⟨r1, r2⟩ := p
        have hspec := trueParents_spec N C htp
        have hmem := live_parent_mem N C hg htp
        rw [coeffCore_trueGate N C i htp]
        have hpar : ∀ w ∈ U, isParentOf N C w g = (decide (w = r1) || decide (w = r2)) := by
          intro w _
          unfold isParentOf
          rw [htp]
          by_cases h1 : w = r1 <;> by_cases h2 : w = r2 <;> simp [h1, h2, Ne.symm]
        rw [xorSum_congr rfl (fun w hw => by rw [hpar w hw])]
        exact xorSum_pair U hspec.2.2.2.2.1 hmem.1 hmem.2 (coeffCore N C i)
  have heq := hLHS.symm.trans hRHS
  generalize adjVec N C i r = a at heq ⊢
  generalize coeffW N C i (termWire C r) = b at heq ⊢
  generalize xorSum (liveGateSet N C) (fun g => coeffCore N C i g && adjVec N C g r) = c at heq
  cases a <;> cases b <;> cases c <;> simp_all


def outDegTerm (w : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * tCount C + 1))).filter (fun r => termRoot N C r = some w)).card

def outDegGate (w : ℕ) : ℕ :=
  ((liveGateSet N C).filter (fun g => isParentOf N C w g = true)).card

def outDeg (w : ℕ) : ℕ := outDegTerm N C w + outDegGate N C w

lemma outDeg_pos_iff_live {w : ℕ} (hw : w < totalWires N C) :
    0 < outDeg N C w ↔ isLive N C w = true := by
  unfold outDeg outDegTerm outDegGate
  rw [isLive_eq N C w hw, Bool.or_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq]
  have heq : (Finset.range (totalWires N C)).filter
      (fun g => w < g && isParentOf N C w g && isLive N C g) =
      (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
    ext g
    simp only [liveGateSet, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hg, ⟨_, hp⟩, hl⟩
      refine ⟨⟨hg, ?_, hl⟩, hp⟩
      unfold isParentOf at hp; unfold isTrueGate
      cases htp : trueParents N C g with
      | none => rw [htp] at hp; cases hp
      | some _ => rfl
    · rintro ⟨⟨hg, _, hl⟩, hp⟩
      exact ⟨hg, ⟨isParentOf_lt N C hp, hp⟩, hl⟩
  rw [heq, ← Finset.card_pos, ← Finset.card_pos]
  omega

lemma outDeg_zero_adjVec {w : ℕ} (hw : w < totalWires N C) (h0 : outDeg N C w = 0)
    (r : Fin (2 * tCount C + 1)) : adjVec N C w r = false := by
  unfold outDeg outDegTerm outDegGate at h0
  have ht0 : ((Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
      (fun r' => termRoot N C r' = some w)).card = 0 := by omega
  have hg0 : ((liveGateSet N C).filter (fun g => isParentOf N C w g = true)).card = 0 := by omega
  rw [Finset.card_eq_zero] at ht0 hg0
  rw [adjVec_eq N C w hw r]
  have htr : termRoot N C r ≠ some w := by
    intro heq
    have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
        (fun r' => termRoot N C r' = some w) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
    rw [ht0] at this; cases this
  have hfilt : (Finset.range (totalWires N C)).filter
      (fun g => isLive N C g && isParentOf N C w g) = ∅ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, Finset.notMem_empty, iff_false]
    rintro ⟨hg, hl, hp⟩
    have htg : isTrueGate N C g = true := by
      unfold isParentOf at hp; unfold isTrueGate
      cases htp : trueParents N C g with
      | none => rw [htp] at hp; cases hp
      | some _ => rfl
    have : g ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, htg, hl⟩, hp⟩
    rw [hg0] at this; cases this
  rw [hfilt, xorSum_empty, decide_eq_false htr]; rfl

lemma sum_outDeg_le :
    ∑ w ∈ baseSet N C ∪ liveGateSet N C, outDeg N C w ≤
      (2 * tCount C + 1) + 2 * (liveGateSet N C).card := by
  set U := baseSet N C ∪ liveGateSet N C
  have hsplit : ∑ w ∈ U, outDeg N C w = (∑ w ∈ U, outDegTerm N C w) + ∑ w ∈ U, outDegGate N C w :=
    Finset.sum_add_distrib
  rw [hsplit]
  have h1 : ∑ w ∈ U, outDegTerm N C w ≤ 2 * tCount C + 1 := by
    unfold outDegTerm
    calc ∑ w ∈ U, ((Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
            (fun r => termRoot N C r = some w)).card
        = ∑ w ∈ U, ∑ r : Fin (2 * tCount C + 1), if termRoot N C r = some w then 1 else 0 := by
          apply Finset.sum_congr rfl; intro w _; rw [Finset.card_filter]
      _ = ∑ r : Fin (2 * tCount C + 1), ∑ w ∈ U, if termRoot N C r = some w then 1 else 0 :=
          Finset.sum_comm
      _ ≤ ∑ _r : Fin (2 * tCount C + 1), 1 := by
          apply Finset.sum_le_sum
          intro r _
          cases htr : termRoot N C r with
          | none => simp
          | some w0 =>
            simp only [Option.some.injEq]
            rw [Finset.sum_ite_eq U w0 (fun _ => 1)]
            split_ifs <;> omega
      _ = 2 * tCount C + 1 := by simp
  have h2 : ∑ w ∈ U, outDegGate N C w ≤ 2 * (liveGateSet N C).card := by
    unfold outDegGate
    calc ∑ w ∈ U, ((liveGateSet N C).filter (fun g => isParentOf N C w g = true)).card
        = ∑ w ∈ U, ∑ g ∈ liveGateSet N C, if isParentOf N C w g = true then 1 else 0 := by
          apply Finset.sum_congr rfl; intro w _; rw [Finset.card_filter]
      _ = ∑ g ∈ liveGateSet N C, ∑ w ∈ U, if isParentOf N C w g = true then 1 else 0 :=
          Finset.sum_comm
      _ ≤ ∑ _g ∈ liveGateSet N C, 2 := by
          apply Finset.sum_le_sum
          intro g hg
          have htg : isTrueGate N C g = true := (Finset.mem_filter.mp hg).2.1
          unfold isTrueGate at htg
          cases htp : trueParents N C g with
          | none => rw [htp] at htg; cases htg
          | some p =>
            obtain ⟨r1, r2⟩ := p
            have hle : ∑ w ∈ U, (if isParentOf N C w g = true then 1 else 0) ≤
                ∑ w ∈ ({r1, r2} : Finset ℕ), 1 := by
              have hsub : U.filter (fun w => isParentOf N C w g = true) ⊆ {r1, r2} := by
                intro w hw
                have hp := (Finset.mem_filter.mp hw).2
                unfold isParentOf at hp; rw [htp] at hp
                rcases Bool.or_eq_true_iff.mp hp with h1 | h2
                · simp [of_decide_eq_true h1]
                · simp [of_decide_eq_true h2]
              rw [← Finset.card_filter]
              simpa using Finset.card_le_card hsub
            exact le_trans hle (by simpa using Finset.card_le_two)
      _ = 2 * (liveGateSet N C).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

lemma liveGateSet_card_le : (liveGateSet N C).card + tCount C ≤ bCount C := by
  let f : ℕ → ℕ := fun w => w - (N + N)
  have hsub : (liveGateSet N C).image f ⊆
      (Finset.range C.gates.length).filter
        (fun j => isBinGate (gateAt C j) = true ∧ isNLGate (gateAt C j) = false) := by
    intro j hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
    have htg := (Finset.mem_filter.mp hw).2.1
    unfold isTrueGate at htg
    cases htp : trueParents N C w with
    | none => rw [htp] at htg; cases htg
    | some p =>
      have hs := trueParents_spec N C htp
      have hltw := hs.1
      have hgeNN := hs.2.2.2.2.2.2.2.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hs.2.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.2⟩
      change w - (N + N) < C.gates.length
      unfold totalWires at hltw; omega
  have hinj : Set.InjOn f (liveGateSet N C : Set ℕ) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 := (Finset.mem_filter.mp hw₁).2.1
    have h2 := (Finset.mem_filter.mp hw₂).2.1
    unfold isTrueGate at h1 h2
    cases hp1 : trueParents N C w₁ with
    | none => rw [hp1] at h1; cases h1
    | some _ =>
      cases hp2 : trueParents N C w₂ with
      | none => rw [hp2] at h2; cases h2
      | some _ =>
        have hs1 := (trueParents_spec N C hp1).2.2.2.2.2.2.2.1
        have hs2 := (trueParents_spec N C hp2).2.2.2.2.2.2.2.1
        simp only [f] at heq; omega
  have hcard1 : (liveGateSet N C).card ≤
      ((Finset.range C.gates.length).filter
        (fun j => isBinGate (gateAt C j) = true ∧ isNLGate (gateAt C j) = false)).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hdisj : Disjoint
      ((Finset.range C.gates.length).filter
        (fun j => isBinGate (gateAt C j) = true ∧ isNLGate (gateAt C j) = false))
      ((Finset.range C.gates.length).filter (fun j => isNLGate (gateAt C j) = true)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have hf := (Finset.mem_filter.mp h1).2.2
    have ht := (Finset.mem_filter.mp h2).2
    rw [hf] at ht; cases ht
  have hunion :
      ((Finset.range C.gates.length).filter
        (fun j => isBinGate (gateAt C j) = true ∧ isNLGate (gateAt C j) = false)) ∪
      ((Finset.range C.gates.length).filter (fun j => isNLGate (gateAt C j) = true)) ⊆
      (Finset.range C.gates.length).filter (fun j => isBinGate (gateAt C j) = true) := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1 | h2
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h1).2.1⟩
    · have hnl := (Finset.mem_filter.mp h2).2
      unfold isNLGate at hnl
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h2).1, (Bool.and_eq_true _ _).mp hnl |>.1⟩
  have hle := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hle
  have hb : bCount C = ((Finset.range C.gates.length).filter
      (fun j => isBinGate (gateAt C j) = true)).card := by
    unfold bCount gateAt
    rw [countP_eq_range_filter C.gates ⟨GateOp.or, []⟩ isBinGate, list_filter_length_eq_finset_card]
  have ht : tCount C = ((Finset.range C.gates.length).filter
      (fun j => isNLGate (gateAt C j) = true)).card := by
    unfold tCount gateAt
    rw [countP_eq_range_filter C.gates ⟨GateOp.or, []⟩ isNLGate, list_filter_length_eq_finset_card]
  omega

lemma baseSet_card : (baseSet N C).card = N + N + tCount C := by
  have h1 : (Finset.range (N + N)) ⊆ baseSet N C := by
    intro w hw
    have hwlt := Finset.mem_range.mp hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by unfold totalWires; omega), ?_⟩
    unfold isBaseWire; simp [hwlt]
  let nlSet : Finset ℕ := (Finset.univ : Finset (Fin (tCount C))).image (nlWire N C)
  have hnl_inj : Function.Injective (nlWire N C) := by
    intro k₁ k₂ h
    rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
    · have := nlIndices_strictMono C hlt; unfold nlWire at h; omega
    · rfl
    · have := nlIndices_strictMono C hgt; unfold nlWire at h; omega
  have hnl_card : nlSet.card = tCount C := by
    rw [Finset.card_image_of_injective _ hnl_inj, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint (Finset.range (N + N)) nlSet := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have hlt := Finset.mem_range.mp hw1
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw2
    unfold nlWire at hlt; omega
  have heq : baseSet N C = Finset.range (N + N) ∪ nlSet := by
    ext w
    simp only [baseSet, nlSet, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hb⟩
      unfold isBaseWire at hb
      by_cases hlt : w < N + N
      · left; exact hlt
      · right
        simp only [hlt, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨k, hk⟩ := nlIndices_exists C hb.1.2 hb.2
        refine ⟨k, ?_⟩
        unfold nlWire; omega
    · rintro (hlt | ⟨k, rfl⟩)
      · exact ⟨by unfold totalWires; omega, by unfold isBaseWire; simp [hlt]⟩
      · refine ⟨by unfold totalWires nlWire; have := nlIndices_lt C k; omega, isBaseWire_nl N C k⟩
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_range, hnl_card]

def basisVec (r : Fin (2 * tCount C + 1)) : Fin (2 * tCount C + 1) → Bool :=
  fun r' => decide (r' = r)

def basisSet : Finset (Fin (2 * tCount C + 1) → Bool) :=
  (Finset.univ : Finset (Fin (2 * tCount C + 1))).image (basisVec C)

lemma adjVec_mem_basis_or_ge2 (w : ℕ) (hw : w ∈ baseSet N C ∪ liveGateSet N C)
    (hlive : isLive N C w = true) :
    adjVec N C w ∈ basisSet C ∪
      ((baseSet N C ∪ liveGateSet N C).filter (fun u => 2 ≤ outDeg N C u)).image (adjVec N C) := by
  induction hgap : totalWires N C - w using Nat.strong_induction_on generalizing w with
  | _ gap ih =>
    have hwlt : w < totalWires N C := by
      rcases Finset.mem_union.mp hw with h | h <;> exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
    have hdpos : 0 < outDeg N C w := (outDeg_pos_iff_live N C hwlt).mpr hlive
    by_cases hge2 : 2 ≤ outDeg N C w
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hge2⟩, rfl⟩)
    · have hd1 : outDeg N C w = 1 := by omega
      unfold outDeg at hd1
      by_cases ht1 : outDegTerm N C w = 1
      · have hg0 : outDegGate N C w = 0 := by omega
        obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp ht1
        have hmemr0 : r0 ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
            (fun r => termRoot N C r = some w) := by rw [hr0]; simp
        have htr0 : termRoot N C r0 = some w := (Finset.mem_filter.mp hmemr0).2
        have hfiltG : (Finset.range (totalWires N C)).filter
            (fun g => isLive N C g && isParentOf N C w g) = ∅ := by
          have hg0' := Finset.card_eq_zero.mp hg0
          ext g
          simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, Finset.notMem_empty, iff_false]
          rintro ⟨hg, hl, hp⟩
          have htg : isTrueGate N C g = true := by
            unfold isParentOf at hp; unfold isTrueGate
            cases htp : trueParents N C g with
            | none => rw [htp] at hp; cases hp
            | some _ => rfl
          have : g ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, htg, hl⟩, hp⟩
          rw [hg0'] at this; cases this
        have hveq : adjVec N C w = basisVec C r0 := by
          funext r
          rw [adjVec_eq N C w hwlt r, hfiltG, xorSum_empty, Bool.xor_false]
          unfold basisVec
          by_cases hrr : r = r0
          · subst hrr; simp [htr0]
          · have hne : termRoot N C r ≠ some w := by
              intro h
              have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
                  (fun r' => termRoot N C r' = some w) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
              rw [hr0, Finset.mem_singleton] at this
              exact hrr this
            simp [hne, hrr]
        rw [hveq]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, Finset.mem_univ _, rfl⟩)
      · have ht0 : outDegTerm N C w = 0 := by omega
        have hg1 : outDegGate N C w = 1 := by omega
        obtain ⟨g0, hg0⟩ := Finset.card_eq_one.mp hg1
        have hmemg0 : g0 ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
          rw [hg0]; simp
        have hg0_live : g0 ∈ liveGateSet N C := (Finset.mem_filter.mp hmemg0).1
        have hg0_par : isParentOf N C w g0 = true := (Finset.mem_filter.mp hmemg0).2
        have hwg0 : w < g0 := isParentOf_lt N C hg0_par
        have hfiltG : (Finset.range (totalWires N C)).filter
            (fun g => isLive N C g && isParentOf N C w g) = {g0} := by
          rw [← hg0]
          ext g
          simp only [liveGateSet, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
          constructor
          · rintro ⟨hg, hl, hp⟩
            refine ⟨⟨hg, ?_, hl⟩, hp⟩
            unfold isParentOf at hp; unfold isTrueGate
            cases htp : trueParents N C g with
            | none => rw [htp] at hp; cases hp
            | some _ => rfl
          · rintro ⟨⟨hg, _, hl⟩, hp⟩
            exact ⟨hg, hl, hp⟩
        have hveq : adjVec N C w = adjVec N C g0 := by
          funext r
          rw [adjVec_eq N C w hwlt r, hfiltG]
          have htr : termRoot N C r ≠ some w := by
            intro h
            have ht0' := Finset.card_eq_zero.mp ht0
            have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
                (fun r' => termRoot N C r' = some w) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
            rw [ht0'] at this; cases this
          rw [decide_eq_false htr, Bool.false_xor, xorSum_singleton]
        rw [hveq]
        exact ih (totalWires N C - g0) (by omega) g0 (Finset.mem_union_right _ hg0_live)
          (Finset.mem_filter.mp hg0_live).2.2 rfl

lemma outDeg_two_adjVec_xor {w : ℕ} (hw : w < totalWires N C) (hd2 : outDeg N C w = 2) :
    ∃ (a b : Fin (2 * tCount C + 1) → Bool),
      (∀ r, adjVec N C w r = xor (a r) (b r)) ∧
      ((∃ r0, a = basisVec C r0) ∨ (∃ g ∈ liveGateSet N C, w < g ∧ a = adjVec N C g)) ∧
      ((∃ r0, b = basisVec C r0) ∨ (∃ g ∈ liveGateSet N C, w < g ∧ b = adjVec N C g)) := by
  have hfiltG : (Finset.range (totalWires N C)).filter
      (fun g => isLive N C g && isParentOf N C w g) =
      (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
    ext g
    simp only [liveGateSet, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨hg, hl, hp⟩
      refine ⟨⟨hg, ?_, hl⟩, hp⟩
      unfold isParentOf at hp; unfold isTrueGate
      cases htp : trueParents N C g with
      | none => rw [htp] at hp; cases hp
      | some _ => rfl
    · rintro ⟨⟨hg, _, hl⟩, hp⟩
      exact ⟨hg, hl, hp⟩
  unfold outDeg at hd2
  by_cases ht2 : outDegTerm N C w = 2
  · have hg0 : outDegGate N C w = 0 := by omega
    obtain ⟨r1, r2, hne, hpair⟩ := Finset.card_eq_two.mp ht2
    have hg0' := Finset.card_eq_zero.mp hg0
    refine ⟨basisVec C r1, basisVec C r2, ?_, Or.inl ⟨r1, rfl⟩, Or.inl ⟨r2, rfl⟩⟩
    intro r
    rw [adjVec_eq N C w hw r, hfiltG, hg0', xorSum_empty, Bool.xor_false]
    have hmem : (termRoot N C r = some w) ↔ (r = r1 ∨ r = r2) := by
      have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
          (fun r' => termRoot N C r' = some w) ↔ r ∈ ({r1, r2} : Finset _) := by rw [hpair]
      simpa using this
    unfold basisVec
    by_cases h1 : r = r1
    · subst h1; simp [hmem.mpr (Or.inl rfl), hne]
    · by_cases h2 : r = r2
      · subst h2; simp [hmem.mpr (Or.inr rfl), h1]
      · have hnf : ¬(termRoot N C r = some w) := fun h => by
          rcases hmem.mp h with h' | h' <;> contradiction
        simp [hnf, h1, h2]
  · by_cases ht1 : outDegTerm N C w = 1
    · have hg1 : outDegGate N C w = 1 := by omega
      obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp ht1
      obtain ⟨g0, hg0⟩ := Finset.card_eq_one.mp hg1
      have hmemg0 : g0 ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
        rw [hg0]; simp
      have hg0L := (Finset.mem_filter.mp hmemg0).1
      have hwg0 := isParentOf_lt N C (Finset.mem_filter.mp hmemg0).2
      refine ⟨basisVec C r0, adjVec N C g0, ?_, Or.inl ⟨r0, rfl⟩, Or.inr ⟨g0, hg0L, hwg0, rfl⟩⟩
      intro r
      rw [adjVec_eq N C w hw r, hfiltG, hg0, xorSum_singleton]
      congr 1
      have hmem : (termRoot N C r = some w) ↔ r = r0 := by
        have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
            (fun r' => termRoot N C r' = some w) ↔ r ∈ ({r0} : Finset _) := by rw [hr0]
        simpa using this
      unfold basisVec
      by_cases h : r = r0
      · subst h; simp [hmem.mpr rfl]
      · simp [h, mt hmem.mp h]
    · have ht0 : outDegTerm N C w = 0 := by omega
      have hg2 : outDegGate N C w = 2 := by omega
      have ht0' := Finset.card_eq_zero.mp ht0
      obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp hg2
      have hmem1 : g1 ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
        rw [hpair]; simp
      have hmem2 : g2 ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
        rw [hpair]; simp
      refine ⟨adjVec N C g1, adjVec N C g2, ?_,
        Or.inr ⟨g1, (Finset.mem_filter.mp hmem1).1, isParentOf_lt N C (Finset.mem_filter.mp hmem1).2, rfl⟩,
        Or.inr ⟨g2, (Finset.mem_filter.mp hmem2).1, isParentOf_lt N C (Finset.mem_filter.mp hmem2).2, rfl⟩⟩
      intro r
      rw [adjVec_eq N C w hw r, hfiltG, hpair]
      have htr : termRoot N C r ≠ some w := by
        intro h
        have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
            (fun r' => termRoot N C r' = some w) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        rw [ht0'] at this; cases this
      rw [decide_eq_false htr, Bool.false_xor, xorSum_insert (by simp [hne]), xorSum_singleton]


lemma lower_bound_general {s : ℕ} (hs : 1 ≤ s) {H : Fin (4 ^ s) → Fin (4 ^ s) → Bool}
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (4 ^ s + 4 ^ s) C)
    (hrep : Represents H C) (htle : tCount C ≤ s)
    (hrow : ∀ u₁ u₂ c, (∀ v, H u₁ v = xor (H u₂ v) c) → u₁ = u₂)
    (hcol : ∀ v₁ v₂ c, (∀ u, H u v₁ = xor (H u v₂) c) → v₁ = v₂) :
    tCount C = s ∧
    3 * 4 ^ s ≤ bCount C + 2 * s + 4 ∧
    ((∃ u0 : Fin (4 ^ s), ∀ v, H u0 v = false) → (∃ u1 v1, H u1 v1 = true) →
      3 * 4 ^ s ≤ bCount C + 2 * s + 3) := by
  let N := 4 ^ s
  have hNpos : 1 ≤ N := Nat.one_le_pow s 4 (by omega)
  have hteq : tCount C = s := tCount_eq_s C hfan hrb hrep htle hrow
  have hpsiL_inj : Function.Injective (psiL N C) := psiL_injective N C hfan hrb hrep hrow
  have hpsiR_inj : Function.Injective (psiR N C) := psiR_injective N C hfan hrb hrep hcol
  have hcard_eq : Fintype.card (Fin N) = Fintype.card (Fin (2 * tCount C) → Bool) := by
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, N, hteq]
    exact four_pow_eq_two_pow s
  have hpsiL_bij : Function.Bijective (psiL N C) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hpsiL_inj, hcard_eq⟩
  have hpsiR_bij : Function.Bijective (psiR N C) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hpsiR_inj, hcard_eq⟩
  obtain ⟨u0, hu0⟩ := hpsiL_bij.2 (fun _ => false)
  obtain ⟨v0, hv0⟩ := hpsiR_bij.2 (fun _ => false)
  set deadBase := (baseSet N C).filter (fun w => outDeg N C w = 0)
  have hdead_sub : deadBase ⊆ {u0.val, N + v0.val} := by
    intro w hw
    have hwB : w ∈ baseSet N C := (Finset.mem_filter.mp hw).1
    have hw0 : outDeg N C w = 0 := (Finset.mem_filter.mp hw).2
    have hwlt : w < totalWires N C := Finset.mem_range.mp (Finset.mem_filter.mp hwB).1
    have hadj0 : ∀ r, adjVec N C w r = false := outDeg_zero_adjVec N C hwlt hw0
    have hcoeff0 : ∀ r, coeffW N C w (termWire C r) = false := fun r => by
      rw [← duality N C hwB r]; exact hadj0 r
    by_cases hltN : w < N
    · have hu_eq : psiL N C ⟨w, hltN⟩ = fun _ => false := by
        funext r; exact hcoeff0 ⟨r.val, by omega⟩
      have heq : (⟨w, hltN⟩ : Fin N) = u0 := hpsiL_inj (hu_eq.trans hu0.symm)
      have hwv : w = u0.val := congrArg Fin.val heq
      simp [hwv]
    · by_cases hlt2N : w < N + N
      · have hv_eq : psiR N C ⟨w - N, by omega⟩ = fun _ => false := by
          funext r
          have : N + (w - N) = w := by omega
          simpa [psiR, this] using hcoeff0 ⟨r.val, by omega⟩
        have heq : (⟨w - N, by omega⟩ : Fin N) = v0 := hpsiR_inj (hv_eq.trans hv0.symm)
        have hwv : w = N + v0.val := by have := congrArg Fin.val heq; dsimp only at this; omega
        simp [hwv]
      · have hb := (Finset.mem_filter.mp hwB).2
        unfold isBaseWire at hb
        simp only [hlt2N, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨k, hk⟩ := nlIndices_exists C hb.1.2 hb.2
        have hwk : w = nlWire N C k := by unfold nlWire; omega
        obtain ⟨r, hr⟩ := nlGate_used C hfan hrb hrep hteq hrow k
        rw [← hwk, hcoeff0 r] at hr
        cases hr
  have hdead_le : deadBase.card ≤ 2 := le_trans (Finset.card_le_card hdead_sub) Finset.card_le_two
  set U := baseSet N C ∪ liveGateSet N C
  set liveU := U.filter (fun w => 1 ≤ outDeg N C w)
  set ge2U := U.filter (fun w => 2 ≤ outDeg N C w)
  set E := ∑ w ∈ liveU, (outDeg N C w - 1)
  have hdeg_sum : liveU.card + E ≤ (2 * tCount C + 1) + 2 * (liveGateSet N C).card := by
    have h1 : liveU.card + E = ∑ w ∈ liveU, outDeg N C w := by
      have : ∑ w ∈ liveU, (1 + (outDeg N C w - 1)) = ∑ w ∈ liveU, outDeg N C w := by
        apply Finset.sum_congr rfl
        intro w hw
        have hpos := (Finset.mem_filter.mp hw).2
        omega
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
      exact this
    rw [h1]
    exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (sum_outDeg_le N C)
  have hliveU_card : liveU.card + deadBase.card = N + N + tCount C + (liveGateSet N C).card := by
    have hdead_eq : U.filter (fun w => ¬(1 ≤ outDeg N C w)) = deadBase := by
      ext w
      simp only [U, deadBase, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hwB | hwG, hnot⟩
        · exact ⟨hwB, by omega⟩
        · have hwlt := Finset.mem_range.mp (Finset.mem_filter.mp hwG).1
          have hpos := (outDeg_pos_iff_live N C hwlt).mpr (Finset.mem_filter.mp hwG).2.2
          omega
      · rintro ⟨hwB, h0⟩
        exact ⟨Or.inl hwB, by omega⟩
    have hpart : liveU.card + deadBase.card = U.card := by
      have hdisj : Disjoint liveU deadBase := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        have h1 := (Finset.mem_filter.mp hw1).2
        have h2 := (Finset.mem_filter.mp hw2).2
        omega
      have hunion : liveU ∪ deadBase = U := by
        rw [← hdead_eq]
        ext w; simp only [liveU, Finset.mem_union, Finset.mem_filter]; tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [Finset.card_union_of_disjoint (disjoint_base_liveGate N C), baseSet_card N C] at hpart
    exact hpart
  have hb_ge : 2 * N - 1 + E ≤ bCount C + deadBase.card := by
    have hlg := liveGateSet_card_le N C
    omega
  set leftNZ : Finset (Fin N) := Finset.univ.erase u0
  set phiLSet : Finset (Fin (2 * tCount C + 1) → Bool) := leftNZ.image (fun u => adjVec N C u.val)
  have hphiL_inj : Set.InjOn (fun u : Fin N => adjVec N C u.val) (leftNZ : Set (Fin N)) := by
    intro u₁ _ u₂ _ heq
    apply hpsiL_inj
    funext r
    have h1 := duality N C (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u₁⟩) ⟨r.val, by omega⟩
    have h2 := duality N C (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u₂⟩) ⟨r.val, by omega⟩
    have h3 := congrFun heq ⟨r.val, by omega⟩
    simpa [psiL, h1, h2] using h3
  have hphiL_card : phiLSet.card = N - 1 := by
    rw [Finset.card_image_of_injOn hphiL_inj, Finset.card_erase_of_mem (Finset.mem_univ u0),
      Finset.card_univ, Fintype.card_fin]
  have hphiL_live : ∀ u ∈ leftNZ, isLive N C u.val = true := by
    intro u hu
    have hne : u ≠ u0 := (Finset.mem_erase.mp hu).1
    have hpsi_ne : psiL N C u ≠ fun _ => false := fun h => hne (hpsiL_inj (h.trans hu0.symm))
    have hex : ∃ r : Fin (2 * tCount C), psiL N C u r = true := by
      by_contra h
      push Not at h
      exact hpsi_ne (funext fun r => Bool.eq_false_iff.mpr (h r))
    obtain ⟨r, hr⟩ := hex
    have huB : u.val ∈ baseSet N C := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u⟩
    have hadj := duality N C huB ⟨r.val, by omega⟩
    have hwlt : u.val < totalWires N C := by unfold totalWires; omega
    by_contra hnot
    have h0 : outDeg N C u.val = 0 := by
      have := (outDeg_pos_iff_live N C hwlt).not.mpr hnot; omega
    rw [outDeg_zero_adjVec N C hwlt h0] at hadj
    change false = psiL N C u r at hadj
    rw [hr] at hadj; cases hadj
  have hphiL_sub : phiLSet \ basisSet C ⊆ (ge2U.image (adjVec N C)) \ basisSet C := by
    intro vec hvec
    obtain ⟨hmem, hnb⟩ := Finset.mem_sdiff.mp hvec
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hmem
    have huB : u.val ∈ U := Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u⟩)
    have hmem2 := adjVec_mem_basis_or_ge2 N C u.val huB (hphiL_live u hu)
    rcases Finset.mem_union.mp hmem2 with hb | hg
    · exact absurd hb hnb
    · exact Finset.mem_sdiff.mpr ⟨hg, hnb⟩
  set lastIdx : Fin (2 * tCount C + 1) := ⟨2 * tCount C, by omega⟩
  have hlast_not : basisVec C lastIdx ∉ phiLSet := by
    intro hmem
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hmem
    have hne : u ≠ u0 := (Finset.mem_erase.mp hu).1
    have hpsi : psiL N C u = fun _ => false := by
      funext r
      have huB : u.val ∈ baseSet N C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u⟩
      have hadj := duality N C huB ⟨r.val, by omega⟩
      have h1 := congrFun heq ⟨r.val, by omega⟩
      unfold basisVec lastIdx at h1
      have hneq : (⟨r.val, by omega⟩ : Fin (2 * tCount C + 1)) ≠ ⟨2 * tCount C, by omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      simp only [hneq, decide_false] at h1
      change coeffW N C u.val (termWire C ⟨r.val, by omega⟩) = false
      rw [← hadj, h1]
    exact hne (hpsiL_inj (hpsi.trans hu0.symm))
  have hinter_sub : phiLSet ∩ basisSet C ⊆ (basisSet C).erase (basisVec C lastIdx) := by
    intro vec hv
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_erase.mpr ⟨fun heq => hlast_not (heq ▸ h1), h2⟩
  have hbasis_inj : Function.Injective (basisVec C) := by
    intro r₁ r₂ h
    have := congrFun h r₁
    simp [basisVec] at this
    exact this
  have hbasis_card : (basisSet C).card = 2 * tCount C + 1 := by
    unfold basisSet
    rw [Finset.card_image_of_injective _ hbasis_inj, Finset.card_univ, Fintype.card_fin]
  have hlast_mem_basis : basisVec C lastIdx ∈ basisSet C :=
    Finset.mem_image.mpr ⟨lastIdx, Finset.mem_univ _, rfl⟩
  have hinter_le : (phiLSet ∩ basisSet C).card ≤ 2 * tCount C := by
    have := Finset.card_le_card hinter_sub
    rw [Finset.card_erase_of_mem hlast_mem_basis, hbasis_card] at this
    omega
  have hsdiff_ge : N - 1 - 2 * tCount C ≤ (phiLSet \ basisSet C).card := by
    have h := Finset.card_sdiff_add_card_inter phiLSet (basisSet C)
    rw [hphiL_card] at h
    omega
  have hge2_le_E : ge2U.card ≤ E := by
    have hsub : ge2U ⊆ liveU := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
    calc ge2U.card = ∑ _w ∈ ge2U, 1 := by simp
      _ ≤ ∑ w ∈ ge2U, (outDeg N C w - 1) := by
        apply Finset.sum_le_sum
        intro w hw; have := (Finset.mem_filter.mp hw).2; omega
      _ ≤ ∑ w ∈ liveU, (outDeg N C w - 1) := Finset.sum_le_sum_of_subset hsub
  have hchain1 : (phiLSet \ basisSet C).card ≤ ((ge2U.image (adjVec N C)) \ basisSet C).card :=
    Finset.card_le_card hphiL_sub
  have hchain2 : ((ge2U.image (adjVec N C)) \ basisSet C).card ≤ (ge2U.image (adjVec N C)).card :=
    Finset.card_le_card Finset.sdiff_subset
  have hchain3 : (ge2U.image (adjVec N C)).card ≤ ge2U.card := Finset.card_image_le
  have hE_ge : N - 1 - 2 * s ≤ E := by omega
  have h4N : 2 * s + 1 ≤ N := by
    have hpow : 2 * s + 1 ≤ 2 ^ (2 * s) := by
      have : ∀ m, m + 1 ≤ 2 ^ m := by
        intro m; induction m with
        | zero => simp
        | succ m ih => rw [pow_succ]; omega
      exact this (2 * s)
    rw [show N = 2 ^ (2 * s) from four_pow_eq_two_pow s]
    exact hpow
  have hmain4 : 3 * N ≤ bCount C + 2 * s + 4 := by omega
  refine ⟨hteq, hmain4, ?_⟩
  rintro ⟨u_const, hu_const⟩ ⟨u_t, v_t, huv_t⟩
  by_contra hlt3
  have hdead_eq2 : deadBase.card = 2 := by omega
  have hE_eq : E = N - 1 - 2 * tCount C := by omega
  have hpair_card : ({u0.val, N + v0.val} : Finset ℕ).card = 2 :=
    Finset.card_pair (by omega)
  have hdead_eq_pair : deadBase = {u0.val, N + v0.val} :=
    Finset.eq_of_subset_of_card_le hdead_sub (by omega)
  have hu0_dead : outDeg N C u0.val = 0 := by
    have : u0.val ∈ deadBase := by rw [hdead_eq_pair]; simp
    exact (Finset.mem_filter.mp this).2
  have hv0_dead : outDeg N C (N + v0.val) = 0 := by
    have : N + v0.val ∈ deadBase := by rw [hdead_eq_pair]; simp
    exact (Finset.mem_filter.mp this).2
  have hu0_out : coeffW N C u0.val C.output = false := by
    have hu0B : u0.val ∈ baseSet N C := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u0⟩
    have h1 := duality N C hu0B lastIdx
    have h2 := outDeg_zero_adjVec N C (by unfold totalWires; omega) hu0_dead lastIdx
    have hterm : termWire C lastIdx = C.output := by unfold termWire lastIdx; simp
    rw [hterm] at h1; rw [← h1, h2]
  have hv0_out : coeffW N C (N + v0.val) C.output = false := by
    have hv0B : N + v0.val ∈ baseSet N C := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_right N C v0⟩
    have h1 := duality N C hv0B lastIdx
    have h2 := outDeg_zero_adjVec N C (by unfold totalWires; omega) hv0_dead lastIdx
    have hterm : termWire C lastIdx = C.output := by unfold termWire lastIdx; simp
    rw [hterm] at h1; rw [← h1, h2]
  have hge2_eq_E : ge2U.card = E := by omega
  have hall_le2 : ∀ w ∈ liveU, outDeg N C w ≤ 2 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨w0, hw0, hgt2⟩ := hnot
    have hw0_ge2 : w0 ∈ ge2U := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw0).1, by omega⟩
    have hsub : ge2U ⊆ liveU := fun w hw =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
    have hstrict : ∑ _w ∈ ge2U, 1 < ∑ w ∈ ge2U, (outDeg N C w - 1) := by
      apply Finset.sum_lt_sum
      · intro w hw; have := (Finset.mem_filter.mp hw).2; omega
      · exact ⟨w0, hw0_ge2, by omega⟩
    have hle2 : ∑ w ∈ ge2U, (outDeg N C w - 1) ≤ E := Finset.sum_le_sum_of_subset hsub
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hstrict
    omega
  set Vall := insert (basisVec C lastIdx) phiLSet
  have hinter_eq : phiLSet ∩ basisSet C = (basisSet C).erase (basisVec C lastIdx) :=
    Finset.eq_of_subset_of_card_le hinter_sub (by
      rw [Finset.card_erase_of_mem hlast_mem_basis, hbasis_card]
      have := Finset.card_sdiff_add_card_inter phiLSet (basisSet C)
      omega)
  have hbasis_sub_Vall : basisSet C ⊆ Vall := by
    intro vec hv
    by_cases hlast : vec = basisVec C lastIdx
    · rw [hlast]; exact Finset.mem_insert_self _ _
    · have : vec ∈ (basisSet C).erase (basisVec C lastIdx) := Finset.mem_erase.mpr ⟨hlast, hv⟩
      rw [← hinter_eq] at this
      exact Finset.mem_insert_of_mem (Finset.mem_inter.mp this).1
  have himg_eq : (ge2U.image (adjVec N C)) \ basisSet C = phiLSet \ basisSet C :=
    Finset.eq_of_subset_of_card_le hphiL_sub (by omega) |>.symm
  have himg_sub_Vall : ge2U.image (adjVec N C) ⊆ Vall := by
    intro vec hv
    by_cases hb : vec ∈ basisSet C
    · exact hbasis_sub_Vall hb
    · have : vec ∈ (ge2U.image (adjVec N C)) \ basisSet C := Finset.mem_sdiff.mpr ⟨hv, hb⟩
      rw [himg_eq] at this
      exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mp this).1
  have hlive_in_Vall : ∀ w ∈ U, isLive N C w = true → adjVec N C w ∈ Vall := by
    intro w hw hlw
    rcases Finset.mem_union.mp (adjVec_mem_basis_or_ge2 N C w hw hlw) with hb | hg
    · exact hbasis_sub_Vall hb
    · exact himg_sub_Vall hg
  let proj : (Fin (2 * tCount C + 1) → Bool) → (Fin (2 * tCount C) → Bool) :=
    fun f r => f ⟨r.val, by omega⟩
  have hproj_inj : Set.InjOn proj (Vall : Set (Fin (2 * tCount C + 1) → Bool)) := by
    intro v₁ hv₁ v₂ hv₂ hpeq
    rcases Finset.mem_insert.mp hv₁ with rfl | hv₁'
    · rcases Finset.mem_insert.mp hv₂ with rfl | hv₂'
      · rfl
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv₂'
        have hne : u ≠ u0 := (Finset.mem_erase.mp hu).1
        have hpsi : psiL N C u = fun _ => false := by
          funext r
          have huB : u.val ∈ baseSet N C := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u⟩
          have hadj := duality N C huB ⟨r.val, by omega⟩
          have h1 := congrFun hpeq r
          simp only [proj, basisVec, lastIdx] at h1
          have hneq : (⟨r.val, by omega⟩ : Fin (2 * tCount C + 1)) ≠ ⟨2 * tCount C, by omega⟩ := by
            intro h; have := congrArg Fin.val h; dsimp only at this; omega
          simp only [hneq, decide_false] at h1
          change coeffW N C u.val (termWire C ⟨r.val, by omega⟩) = false
          rw [← hadj, ← h1]
        exact absurd (hpsiL_inj (hpsi.trans hu0.symm)) hne
    · rcases Finset.mem_insert.mp hv₂ with rfl | hv₂'
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv₁'
        have hne : u ≠ u0 := (Finset.mem_erase.mp hu).1
        have hpsi : psiL N C u = fun _ => false := by
          funext r
          have huB : u.val ∈ baseSet N C := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u⟩
          have hadj := duality N C huB ⟨r.val, by omega⟩
          have h1 := congrFun hpeq r
          simp only [proj, basisVec, lastIdx] at h1
          have hneq : (⟨r.val, by omega⟩ : Fin (2 * tCount C + 1)) ≠ ⟨2 * tCount C, by omega⟩ := by
            intro h; have := congrArg Fin.val h; dsimp only at this; omega
          simp only [hneq, decide_false] at h1
          change coeffW N C u.val (termWire C ⟨r.val, by omega⟩) = false
          rw [← hadj, h1]
        exact absurd (hpsiL_inj (hpsi.trans hu0.symm)) hne
      · obtain ⟨u₁, _, rfl⟩ := Finset.mem_image.mp hv₁'
        obtain ⟨u₂, _, rfl⟩ := Finset.mem_image.mp hv₂'
        have hu : u₁ = u₂ := by
          apply hpsiL_inj
          funext r
          have hu1B : u₁.val ∈ baseSet N C := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u₁⟩
          have hu2B : u₂.val ∈ baseSet N C := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u₂⟩
          have h1 := duality N C hu1B ⟨r.val, by omega⟩
          have h2 := duality N C hu2B ⟨r.val, by omega⟩
          have hp := congrFun hpeq r
          simp only [proj] at hp
          change coeffW N C u₁.val (termWire C ⟨r.val, by omega⟩) =
            coeffW N C u₂.val (termWire C ⟨r.val, by omega⟩)
          rw [← h1, ← h2, hp]
        rw [hu]
  have hno_mixed : ∀ w ∈ U, isLive N C w = true → adjVec N C w lastIdx = true →
      proj (adjVec N C w) = fun _ => false := by
    intro w
    induction hgap : totalWires N C - w using Nat.strong_induction_on generalizing w with
    | _ gap ih =>
      intro hwU hlw hlast
      have hwlt : w < totalWires N C := by
        rcases Finset.mem_union.mp hwU with h | h <;> exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
      have hdpos : 0 < outDeg N C w := (outDeg_pos_iff_live N C hwlt).mpr hlw
      have hwliveU : w ∈ liveU := Finset.mem_filter.mpr ⟨hwU, hdpos⟩
      have hdle2 : outDeg N C w ≤ 2 := hall_le2 w hwliveU
      by_cases hd2 : outDeg N C w = 2
      · obtain ⟨a, b, hxor, ha, hb⟩ := outDeg_two_adjVec_xor N C hwlt hd2
        have ha_mem : a ∈ Vall := by
          rcases ha with ⟨r0, rfl⟩ | ⟨g, hgL, _, rfl⟩
          · exact hbasis_sub_Vall (Finset.mem_image.mpr ⟨r0, Finset.mem_univ _, rfl⟩)
          · exact hlive_in_Vall g (Finset.mem_union_right _ hgL) (Finset.mem_filter.mp hgL).2.2
        have hb_mem : b ∈ Vall := by
          rcases hb with ⟨r0, rfl⟩ | ⟨g, hgL, _, rfl⟩
          · exact hbasis_sub_Vall (Finset.mem_image.mpr ⟨r0, Finset.mem_univ _, rfl⟩)
          · exact hlive_in_Vall g (Finset.mem_union_right _ hgL) (Finset.mem_filter.mp hgL).2.2
        have hstep : ∀ x, ((∃ r0, x = basisVec C r0) ∨ (∃ g ∈ liveGateSet N C, w < g ∧ x = adjVec N C g)) →
            x lastIdx = true → proj x = fun _ => false := by
          intro x hx hxl
          rcases hx with ⟨r0, rfl⟩ | ⟨g, hgL, hwg, rfl⟩
          · unfold basisVec at hxl
            have hr0 : lastIdx = r0 := of_decide_eq_true hxl
            subst hr0
            funext r
            simp only [proj, basisVec, lastIdx]
            exact decide_eq_false (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
          · exact ih (totalWires N C - g) (by omega) g rfl (Finset.mem_union_right _ hgL)
              (Finset.mem_filter.mp hgL).2.2 hxl
        have hxl := hxor lastIdx
        rw [hlast] at hxl
        cases hal : a lastIdx <;> cases hbl : b lastIdx
        · rw [hal, hbl] at hxl; cases hxl
        · have hb0 : proj b = fun _ => false := hstep b hb hbl
          have hpeq : proj (adjVec N C w) = proj a := by
            funext r
            simp only [proj, hxor]
            have hbr := congrFun hb0 r
            simp only [proj] at hbr
            rw [hbr, Bool.xor_false]
          have hweq : adjVec N C w = a := hproj_inj (hlive_in_Vall w hwU hlw) ha_mem hpeq
          have : adjVec N C w lastIdx = a lastIdx := congrFun hweq lastIdx
          rw [hlast, hal] at this; cases this
        · have ha0 : proj a = fun _ => false := hstep a ha hal
          have hpeq : proj (adjVec N C w) = proj b := by
            funext r
            simp only [proj, hxor]
            have har := congrFun ha0 r
            simp only [proj] at har
            rw [har, Bool.false_xor]
          have hweq : adjVec N C w = b := hproj_inj (hlive_in_Vall w hwU hlw) hb_mem hpeq
          have : adjVec N C w lastIdx = b lastIdx := congrFun hweq lastIdx
          rw [hlast, hbl] at this; cases this
        · rw [hal, hbl] at hxl; cases hxl
      · have hd1 : outDeg N C w = 1 := by omega
        unfold outDeg at hd1
        by_cases ht1 : outDegTerm N C w = 1
        · have hg0 : outDegGate N C w = 0 := by omega
          obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp ht1
          have htr0 : termRoot N C r0 = some w :=
            (Finset.mem_filter.mp (by rw [hr0]; simp : r0 ∈ _)).2
          have hfiltG : (Finset.range (totalWires N C)).filter
              (fun g => isLive N C g && isParentOf N C w g) = ∅ := by
            have hg0' := Finset.card_eq_zero.mp hg0
            ext g
            simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, Finset.notMem_empty, iff_false]
            rintro ⟨hg, hl, hp⟩
            have htg : isTrueGate N C g = true := by
              unfold isParentOf at hp; unfold isTrueGate
              cases htp : trueParents N C g with
              | none => rw [htp] at hp; cases hp
              | some _ => rfl
            have : g ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, htg, hl⟩, hp⟩
            rw [hg0'] at this; cases this
          have hveq : adjVec N C w = basisVec C r0 := by
            funext r
            rw [adjVec_eq N C w hwlt r, hfiltG, xorSum_empty, Bool.xor_false]
            unfold basisVec
            by_cases hrr : r = r0
            · subst hrr; simp [htr0]
            · have hne : termRoot N C r ≠ some w := by
                intro h
                have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
                    (fun r' => termRoot N C r' = some w) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
                rw [hr0, Finset.mem_singleton] at this
                exact hrr this
              simp [hne, hrr]
          rw [hveq] at hlast ⊢
          unfold basisVec at hlast
          have hr0' : lastIdx = r0 := of_decide_eq_true hlast
          subst hr0'
          funext r
          simp only [proj, basisVec, lastIdx]
          exact decide_eq_false (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
        · have ht0 : outDegTerm N C w = 0 := by omega
          have hg1 : outDegGate N C w = 1 := by omega
          obtain ⟨g0, hg0⟩ := Finset.card_eq_one.mp hg1
          have hmemg0 : g0 ∈ (liveGateSet N C).filter (fun g => isParentOf N C w g = true) := by
            rw [hg0]; simp
          have hg0L := (Finset.mem_filter.mp hmemg0).1
          have hwg0 := isParentOf_lt N C (Finset.mem_filter.mp hmemg0).2
          have hfiltG : (Finset.range (totalWires N C)).filter
              (fun g => isLive N C g && isParentOf N C w g) = {g0} := by
            rw [← hg0]
            ext g
            simp only [liveGateSet, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
            constructor
            · rintro ⟨hg, hl, hp⟩
              refine ⟨⟨hg, ?_, hl⟩, hp⟩
              unfold isParentOf at hp; unfold isTrueGate
              cases htp : trueParents N C g with
              | none => rw [htp] at hp; cases hp
              | some _ => rfl
            · rintro ⟨⟨hg, _, hl⟩, hp⟩; exact ⟨hg, hl, hp⟩
          have hveq : adjVec N C w = adjVec N C g0 := by
            funext r
            rw [adjVec_eq N C w hwlt r, hfiltG]
            have htr : termRoot N C r ≠ some w := by
              intro h
              have ht0' := Finset.card_eq_zero.mp ht0
              have : r ∈ (Finset.univ : Finset (Fin (2 * tCount C + 1))).filter
                  (fun r' => termRoot N C r' = some w) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
              rw [ht0'] at this; cases this
            rw [decide_eq_false htr, Bool.false_xor, xorSum_singleton]
          rw [hveq] at hlast ⊢
          exact ih (totalWires N C - g0) (by omega) g0 rfl (Finset.mem_union_right _ hg0L)
            (Finset.mem_filter.mp hg0L).2.2 hlast
  have hall_L_out : ∀ u : Fin N, coeffW N C u.val C.output = false := by
    intro u
    by_cases hu : u = u0
    · rw [hu]; exact hu0_out
    · have huB : u.val ∈ baseSet N C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_left N C u⟩
      have hterm : termWire C lastIdx = C.output := by unfold termWire lastIdx; simp
      have h1 := duality N C huB lastIdx
      rw [hterm] at h1
      rw [← h1]
      by_contra htrue
      have htrue' : adjVec N C u.val lastIdx = true := Bool.eq_true_of_not_eq_false htrue
      have hp0 := hno_mixed u.val (Finset.mem_union_left _ huB)
        (hphiL_live u (Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩)) htrue'
      have hpsi : psiL N C u = fun _ => false := by
        funext r
        have h2 := duality N C huB ⟨r.val, by omega⟩
        change coeffW N C u.val (termWire C ⟨r.val, by omega⟩) = false
        rw [← h2]
        exact congrFun hp0 r
      exact hu (hpsiL_inj (hpsi.trans hu0.symm))
  have hall_R_out : ∀ v : Fin N, coeffW N C (N + v.val) C.output = false := by
    intro v
    by_cases hv : v = v0
    · rw [hv]; exact hv0_out
    · have hvB : N + v.val ∈ baseSet N C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by unfold totalWires; omega), isBaseWire_right N C v⟩
      have hterm : termWire C lastIdx = C.output := by unfold termWire lastIdx; simp
      have h1 := duality N C hvB lastIdx
      rw [hterm] at h1
      rw [← h1]
      by_contra htrue
      have htrue' : adjVec N C (N + v.val) lastIdx = true := Bool.eq_true_of_not_eq_false htrue
      have hvlive : isLive N C (N + v.val) = true := by
        have hwlt : N + v.val < totalWires N C := by unfold totalWires; omega
        by_contra hnot
        have h0 : outDeg N C (N + v.val) = 0 := by
          have := (outDeg_pos_iff_live N C hwlt).not.mpr hnot; omega
        rw [outDeg_zero_adjVec N C hwlt h0] at htrue'; cases htrue'
      have hp0 := hno_mixed (N + v.val) (Finset.mem_union_left _ hvB) hvlive htrue'
      have hpsi : psiR N C v = fun _ => false := by
        funext r
        have h2 := duality N C hvB ⟨r.val, by omega⟩
        change coeffW N C (N + v.val) (termWire C ⟨r.val, by omega⟩) = false
        rw [← h2]
        exact congrFun hp0 r
      exact hv (hpsiR_inj (hpsi.trans hv0.symm))
  have hH_eq : ∀ u v, H u v = nlOutFunc N C hrb (fun r => xor (psiL N C u r) (psiR N C v r)) := by
    intro u v
    rw [← hrep u v, eval_factor N C hfan hrb u v, hall_L_out u, hall_R_out v]
    simp
  have hF_false : ∀ xi : Fin (2 * tCount C) → Bool, nlOutFunc N C hrb xi = false := by
    intro xi
    obtain ⟨v, hv⟩ := hpsiR_bij.2 (fun r => xor (psiL N C u_const r) (xi r))
    have h1 := hu_const v
    rw [hH_eq u_const v, hv] at h1
    have hxi : (fun r => xor (psiL N C u_const r) (xor (psiL N C u_const r) (xi r))) = xi := by
      funext r; cases psiL N C u_const r <;> cases xi r <;> rfl
    rw [hxi] at h1
    exact h1
  have ht := huv_t
  rw [hH_eq u_t v_t, hF_false] at ht
  cases ht

end LowerBound


lemma four_pow_eq_mul (s : ℕ) : 4 ^ s = 2 ^ s * 2 ^ s := by
  rw [four_pow_eq_two_pow, two_mul, pow_add]


def WellFormed (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)

lemma wellFormed_nil (n : ℕ) : WellFormed n [] := ⟨by simp, by intro j hj; cases hj⟩

lemma wellFormed_append_gate {n : ℕ} {gs : List Gate} {g : Gate}
    (hwf : WellFormed n gs) (hlen : g.inputs.length ≤ 2)
    (hins : ∀ i ∈ g.inputs, i < n + gs.length) :
    WellFormed n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hwf.1 g' h
    · rw [List.mem_singleton.mp h]; exact hlen
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hwf.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hins i hi

def xorGates (curr a b : ℕ) : List Gate :=
  [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [curr]⟩]

lemma xorGates_countB (curr a b : ℕ) : (xorGates curr a b).countP isBinGate = 1 := by
  simp [xorGates, isBinGate]

lemma xorGates_countT (curr a b : ℕ) : (xorGates curr a b).countP isNLGate = 0 := by
  simp [xorGates, isNLGate, GateOp.eval]

lemma andGate_countB (a b : ℕ) : ([⟨GateOp.and, [a, b]⟩] : List Gate).countP isBinGate = 1 := by
  simp [isBinGate]

lemma andGate_countT (a b : ℕ) : ([⟨GateOp.and, [a, b]⟩] : List Gate).countP isNLGate = 1 := by
  simp [isNLGate, GateOp.eval]

lemma wellFormed_append_xor {n : ℕ} {gs : List Gate} {a b : ℕ}
    (hwf : WellFormed n gs) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    WellFormed n (gs ++ xorGates (n + gs.length) a b) := by
  have h1 : WellFormed n (gs ++ [⟨GateOp.mod 2, [a, b]⟩]) :=
    wellFormed_append_gate hwf (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  have h2 : WellFormed n ((gs ++ [⟨GateOp.mod 2, [a, b]⟩]) ++ [⟨GateOp.not, [n + gs.length]⟩]) :=
    wellFormed_append_gate h1 (by simp) (by
      intro i hi; simp only [List.mem_singleton] at hi; subst hi
      simp only [List.length_append, List.length_singleton]; omega)
  simpa [xorGates, List.append_assoc] using h2

lemma foldl_append_xor_eval {n : ℕ} (gs : List Gate) (a b : ℕ) (x : List Bool) (hx : x.length = n)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let gs' := gs ++ xorGates (n + gs.length) a b
    (∀ w < n + gs.length, (gs'.foldl stepWires x).getD w false = (gs.foldl stepWires x).getD w false) ∧
    (gs'.foldl stepWires x).getD (n + gs.length + 1) false =
      xor ((gs.foldl stepWires x).getD a false) ((gs.foldl stepWires x).getD b false) := by
  intro gs'
  set w0 := gs.foldl stepWires x
  have hw0len : w0.length = n + gs.length := by
    rw [foldl_stepWires_length, hx]
  have hfold : gs'.foldl stepWires x = stepWires (stepWires w0 ⟨GateOp.mod 2, [a, b]⟩) ⟨GateOp.not, [n + gs.length]⟩ := by
    simp [gs', xorGates, List.foldl_append, w0]
  constructor
  · intro w hw
    rw [hfold]
    have hlt1 : w < (stepWires w0 ⟨GateOp.mod 2, [a, b]⟩).length := by
      simp only [stepWires, List.length_append, List.length_singleton]; omega
    have hwlt0 : w < w0.length := by omega
    rw [List.getD_eq_getElem?_getD]
    change (stepWires w0 ⟨GateOp.mod 2, [a, b]⟩ ++ [_])[w]?.getD false = w0.getD w false
    rw [List.getElem?_append_left hlt1]
    change (w0 ++ [_])[w]?.getD false = w0.getD w false
    rw [List.getElem?_append_left hwlt0, ← List.getD_eq_getElem?_getD]
  · rw [hfold]
    have hmod_val : (stepWires w0 ⟨GateOp.mod 2, [a, b]⟩).getD (n + gs.length) false =
        !(xor (w0.getD a false) (w0.getD b false)) := by
      rw [List.getD_eq_getElem?_getD]
      change (w0 ++ [(GateOp.mod 2).eval [w0.getD a false, w0.getD b false]])[n + gs.length]?.getD false = _
      rw [← hw0len, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some, GateOp.eval]
      cases w0.getD a false <;> cases w0.getD b false <;> rfl
    have hlen1 : (stepWires w0 ⟨GateOp.mod 2, [a, b]⟩).length = n + gs.length + 1 := by
      simp only [stepWires, List.length_append, List.length_singleton, hw0len]
    rw [List.getD_eq_getElem?_getD]
    change (stepWires w0 ⟨GateOp.mod 2, [a, b]⟩ ++
      [GateOp.not.eval [(stepWires w0 ⟨GateOp.mod 2, [a, b]⟩).getD (n + gs.length) false]])[n + gs.length + 1]?.getD false = _
    rw [← hlen1, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, GateOp.eval, List.headD_cons, hmod_val, Bool.not_not]

lemma foldl_append_and_eval {n : ℕ} (gs : List Gate) (a b : ℕ) (x : List Bool) (hx : x.length = n) :
    let gs' := gs ++ [⟨GateOp.and, [a, b]⟩]
    (∀ w < n + gs.length, (gs'.foldl stepWires x).getD w false = (gs.foldl stepWires x).getD w false) ∧
    (gs'.foldl stepWires x).getD (n + gs.length) false =
      ((gs.foldl stepWires x).getD a false && (gs.foldl stepWires x).getD b false) := by
  intro gs'
  set w0 := gs.foldl stepWires x
  have hw0len : w0.length = n + gs.length := by rw [foldl_stepWires_length, hx]
  have hfold : gs'.foldl stepWires x = stepWires w0 ⟨GateOp.and, [a, b]⟩ := by
    simp [gs', List.foldl_append, w0]
  constructor
  · intro w hw
    rw [hfold, List.getD_eq_getElem?_getD]
    change (w0 ++ [_])[w]?.getD false = w0.getD w false
    rw [List.getElem?_append_left (by omega : w < w0.length), ← List.getD_eq_getElem?_getD]
  · rw [hfold, List.getD_eq_getElem?_getD]
    change (w0 ++ [GateOp.and.eval [w0.getD a false, w0.getD b false]])[n + gs.length]?.getD false = _
    rw [← hw0len, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, GateOp.eval]
    simp


def swapH (s u : ℕ) : ℕ := (u % 2 ^ s) * 2 ^ s + u / 2 ^ s

lemma swapH_lt (s u : ℕ) (hu : u < 4 ^ s) : swapH s u < 4 ^ s := by
  unfold swapH
  have hpow : 4 ^ s = 2 ^ s * 2 ^ s := four_pow_eq_mul s
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hmod : u % 2 ^ s < 2 ^ s := Nat.mod_lt u hpos
  have hdiv : u / 2 ^ s < 2 ^ s := Nat.div_lt_of_lt_mul (hpow ▸ hu)
  have h1 : (u % 2 ^ s + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hmod
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

lemma swapH_invol (s u : ℕ) (hu : u < 4 ^ s) : swapH s (swapH s u) = u := by
  unfold swapH
  have hpow : 4 ^ s = 2 ^ s * 2 ^ s := four_pow_eq_mul s
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hdiv : u / 2 ^ s < 2 ^ s := Nat.div_lt_of_lt_mul (hpow ▸ hu)
  have hm : ((u % 2 ^ s) * 2 ^ s + u / 2 ^ s) % 2 ^ s = u / 2 ^ s := by
    rw [Nat.mul_add_mod_of_lt hdiv]
  have hd : ((u % 2 ^ s) * 2 ^ s + u / 2 ^ s) / 2 ^ s = u % 2 ^ s := by
    rw [Nat.add_comm, Nat.mul_comm (u % 2 ^ s), Nat.add_mul_div_left _ _ hpos,
      Nat.div_eq_of_lt hdiv, Nat.zero_add]
  rw [hm, hd, Nat.mul_comm]
  exact Nat.div_add_mod u (2 ^ s)

lemma swapH_zero (s : ℕ) : swapH s 0 = 0 := by simp [swapH]

lemma swapH_ne_zero (s u : ℕ) (hu0 : 0 < u) (hu : u < 4 ^ s) : 0 < swapH s u := by
  by_contra h
  have h0 : swapH s u = 0 := by omega
  have := swapH_invol s u hu
  rw [h0, swapH_zero] at this
  omega

lemma testBit_swapH_lo (s u i : ℕ) (hi : i < s) :
    (swapH s u).testBit i = u.testBit (s + i) := by
  unfold swapH
  have hdiv : (u % 2 ^ s * 2 ^ s + u / 2 ^ s) / 2 ^ i =
      u % 2 ^ s * 2 ^ (s - i) + (u / 2 ^ s) / 2 ^ i := by
    have hmul : u % 2 ^ s * 2 ^ s = 2 ^ i * (u % 2 ^ s * 2 ^ (s - i)) := by
      have hpow : 2 ^ s = 2 ^ i * 2 ^ (s - i) := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hi)]
      calc u % 2 ^ s * 2 ^ s = u % 2 ^ s * (2 ^ i * 2 ^ (s - i)) := by rw [hpow]
        _ = 2 ^ i * (u % 2 ^ s * 2 ^ (s - i)) := by ring
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    rw [hmul, Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.add_comm]
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv,
    pow_add, ← Nat.div_div_eq_div_mul]
  have heven : 2 ∣ u % 2 ^ s * 2 ^ (s - i) := by
    have h2 : 2 ∣ 2 ^ (s - i) := dvd_pow_self 2 (by omega)
    exact dvd_mul_of_dvd_right h2 _
  obtain ⟨k, hk⟩ := heven
  rw [hk, Nat.add_comm, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_comm 1, Nat.and_one_is_mod,
    Nat.add_mul_mod_self_left]

lemma testBit_swapH_hi (s u i : ℕ) (hu : u < 4 ^ s) (hi : i < s) :
    (swapH s u).testBit (s + i) = u.testBit i := by
  have := testBit_swapH_lo s (swapH s u) i hi
  rw [swapH_invol s u hu] at this
  exact this.symm

lemma quadFun_swapH (s : ℕ) (y : Fin (4 ^ s)) :
    quadFun s ⟨swapH s y.val, swapH_lt s y.val y.isLt⟩ = quadFun s y := by
  unfold quadFun
  have hfilt : (Finset.univ : Finset (Fin s)).filter (fun i =>
      (swapH s y.val).testBit i.val && (swapH s y.val).testBit (s + i.val)) =
      (Finset.univ : Finset (Fin s)).filter (fun i =>
        y.val.testBit i.val && y.val.testBit (s + i.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      testBit_swapH_lo s y.val i.val i.isLt, testBit_swapH_hi s y.val i.val y.isLt i.isLt,
      Bool.and_comm]
  rw [hfilt]

lemma dotFun_eq_xorSum_halves (s : ℕ) (x y : Fin (4 ^ s)) :
    dotFun s x y =
      xorSum (Finset.univ : Finset (Fin s)) (fun i =>
        xor (x.val.testBit i.val && y.val.testBit i.val)
            (x.val.testBit (s + i.val) && y.val.testBit (s + i.val))) := by
  change xorSum (Finset.univ : Finset (Fin (2 * s))) (fun j =>
      x.val.testBit j.val && y.val.testBit j.val) = _
  rw [xorSum_xor]
  let eL : Fin s ↪ Fin (2 * s) := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)⟩
  let eR : Fin s ↪ Fin (2 * s) := ⟨fun i => ⟨s + i.val, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp only at this; omega)⟩
  set SL : Finset (Fin (2 * s)) := Finset.univ.map eL
  set SR : Finset (Fin (2 * s)) := Finset.univ.map eR
  have hdisj : Disjoint SL SR := by
    rw [Finset.disjoint_left]
    intro j hjL hjR
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hjL
    obtain ⟨b, _, h⟩ := Finset.mem_map.mp hjR
    have := congrArg Fin.val h; change s + b.val = a.val at this; omega
  have hunion : SL ∪ SR = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, SL, SR, Finset.mem_map, true_and]
    by_cases h : j.val < s
    · left; exact ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    · right; refine ⟨⟨j.val - s, by have := j.isLt; omega⟩, Fin.ext ?_⟩; change s + (j.val - s) = j.val; omega
  rw [← hunion]
  have hsum_disj : ∀ (A B : Finset (Fin (2 * s))) (h : Disjoint A B) (f : Fin (2 * s) → Bool),
      xorSum (A ∪ B) f = xor (xorSum A f) (xorSum B f) := by
    intro A B h f
    induction A using Finset.induction_on with
    | empty => simp [xorSum_empty]
    | @insert a A ha ih =>
      have haB : a ∉ B := Finset.disjoint_left.mp h (Finset.mem_insert_self a A)
      have hAB : Disjoint A B := Finset.disjoint_of_subset_left (Finset.subset_insert a A) h
      have haAB : a ∉ A ∪ B := by simp [ha, haB]
      rw [Finset.insert_union, xorSum_insert haAB, xorSum_insert ha, ih hAB]
      cases f a <;> cases xorSum A f <;> cases xorSum B f <;> rfl
  rw [hsum_disj SL SR hdisj]
  have hmap : ∀ (e : Fin s ↪ Fin (2 * s)) (f : Fin (2 * s) → Bool),
      xorSum (Finset.univ.map e) f = xorSum (Finset.univ : Finset (Fin s)) (fun i => f (e i)) := by
    intro e f
    unfold xorSum
    have hfilt : (Finset.univ.map e).filter (fun j => f j = true) =
        ((Finset.univ : Finset (Fin s)).filter (fun i => f (e i) = true)).map e := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, rfl⟩, hf⟩; exact ⟨i, hf, rfl⟩
      · rintro ⟨i, hf, rfl⟩; exact ⟨⟨i, rfl⟩, hf⟩
    rw [hfilt, Finset.card_map]
  rw [hmap eL, hmap eR]
  rfl

lemma signedFun_eq_prod_sum (s : ℕ) (x y : Fin (4 ^ s)) :
    signedFun s x y =
      xorSum (Finset.univ : Finset (Fin s)) (fun i =>
        xor (x.val.testBit i.val) ((swapH s y.val).testBit i.val) &&
        xor (x.val.testBit (s + i.val)) ((swapH s y.val).testBit (s + i.val))) := by
  unfold signedFun
  rw [dotFun_eq_xorSum_halves]
  change xor (xor (xorSum (Finset.univ : Finset (Fin s)) (fun i => x.val.testBit i.val && x.val.testBit (s + i.val)))
                  (xorSum (Finset.univ : Finset (Fin s)) (fun i => y.val.testBit i.val && y.val.testBit (s + i.val))))
             (xorSum (Finset.univ : Finset (Fin s)) (fun i =>
                xor (x.val.testBit i.val && y.val.testBit i.val)
                    (x.val.testBit (s + i.val) && y.val.testBit (s + i.val)))) = _
  rw [← xorSum_xor, ← xorSum_xor]
  apply xorSum_congr rfl
  intro i _
  rw [testBit_swapH_lo s y.val i.val i.isLt, testBit_swapH_hi s y.val i.val y.isLt i.isLt]
  cases x.val.testBit i.val <;> cases x.val.testBit (s + i.val) <;>
    cases y.val.testBit i.val <;> cases y.val.testBit (s + i.val) <;> rfl


section AdjointBuilder

variable {M : ℕ} (rk : Fin M → ℕ) (p1 p2 : Fin M → Fin M)

def fwdAux (a : Fin M → Bool) : ℕ → Fin M → Bool
  | 0, v => a v
  | r + 1, v => if 0 < rk v then xor (fwdAux a r (p1 v)) (fwdAux a r (p2 v)) else a v

def fwdEval (a : Fin M → Bool) (v : Fin M) : Bool := fwdAux rk p1 p2 a (rk v) v

lemma fwdAux_mono (hacyc : ∀ v, 0 < rk v → rk (p1 v) < rk v ∧ rk (p2 v) < rk v)
    (a : Fin M → Bool) (r1 r2 : ℕ) (v : Fin M) (h1 : rk v ≤ r1) (h2 : rk v ≤ r2) :
    fwdAux rk p1 p2 a r1 v = fwdAux rk p1 p2 a r2 v := by
  induction hk : rk v using Nat.strong_induction_on generalizing r1 r2 v with
  | _ k ih =>
    cases r1 with
    | zero =>
      have hk0 : rk v = 0 := by omega
      cases r2 with
      | zero => rfl
      | succ r2 => unfold fwdAux; simp [hk0]
    | succ r1 =>
      cases r2 with
      | zero =>
        have hk0 : rk v = 0 := by omega
        unfold fwdAux; simp [hk0]
      | succ r2 =>
        unfold fwdAux
        by_cases hpos : 0 < rk v
        · simp only [hpos, ↓reduceIte]
          have hp := hacyc v hpos
          rw [ih (rk (p1 v)) (by omega) r1 r2 (p1 v) (by omega) (by omega) rfl,
              ih (rk (p2 v)) (by omega) r1 r2 (p2 v) (by omega) (by omega) rfl]
        · simp [hpos]

lemma fwdEval_zero (a : Fin M → Bool) (v : Fin M) (h0 : rk v = 0) :
    fwdEval rk p1 p2 a v = a v := by
  unfold fwdEval; rw [h0]; rfl

lemma fwdEval_gate (hacyc : ∀ v, 0 < rk v → rk (p1 v) < rk v ∧ rk (p2 v) < rk v)
    (a : Fin M → Bool) (v : Fin M) (hpos : 0 < rk v) :
    fwdEval rk p1 p2 a v = xor (fwdEval rk p1 p2 a (p1 v)) (fwdEval rk p1 p2 a (p2 v)) := by
  have hrk : rk v = (rk v - 1) + 1 := by omega
  conv_lhs => unfold fwdEval; rw [hrk]; unfold fwdAux
  simp only [hpos, ↓reduceIte]
  have hp := hacyc v hpos
  rw [fwdAux_mono rk p1 p2 hacyc a (rk v - 1) (rk (p1 v)) (p1 v) (by omega) le_rfl,
      fwdAux_mono rk p1 p2 hacyc a (rk v - 1) (rk (p2 v)) (p2 v) (by omega) le_rfl]
  rfl

def accStep (n : ℕ) (st : List Gate × (Fin M → Option ℕ)) (v : Fin M) (w : ℕ) :
    List Gate × (Fin M → Option ℕ) :=
  match st.2 v with
  | none => (st.1, Function.update st.2 v (some w))
  | some w' =>
    (st.1 ++ xorGates (n + st.1.length) w' w,
      Function.update st.2 v (some (n + st.1.length + 1)))

def gateStep (n : ℕ) (st : List Gate × (Fin M → Option ℕ)) (u : Fin M) :
    List Gate × (Fin M → Option ℕ) :=
  match st.2 u with
  | none => st
  | some w =>
    let st0 := (st.1, Function.update st.2 u none)
    let st1 := accStep n st0 (p1 u) w
    accStep n st1 (p2 u) w

def someCount (adj : Fin M → Option ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin M)).filter (fun v => (adj v).isSome = true)).card

def evalOpt (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (gs.foldl stepWires x).getD w false

lemma someCount_update_none (adj : Fin M → Option ℕ) (u : Fin M) {w : ℕ} (hu : adj u = some w) :
    someCount (Function.update adj u none) + 1 = someCount adj := by
  unfold someCount
  have hmem : u ∈ (Finset.univ : Finset (Fin M)).filter (fun v => (adj v).isSome = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu]⟩
  have heq : (Finset.univ : Finset (Fin M)).filter (fun v => (Function.update adj u none v).isSome = true) =
      ((Finset.univ : Finset (Fin M)).filter (fun v => (adj v).isSome = true)).erase u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases h : v = u
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  rw [heq]
  exact Finset.card_erase_add_one hmem

lemma someCount_update_some_of_none (adj : Fin M → Option ℕ) (v : Fin M) (w : ℕ)
    (hv : adj v = none) :
    someCount (Function.update adj v (some w)) = someCount adj + 1 := by
  unfold someCount
  have hnot : v ∉ (Finset.univ : Finset (Fin M)).filter (fun u => (adj u).isSome = true) := by
    simp [hv]
  have heq : (Finset.univ : Finset (Fin M)).filter (fun u => (Function.update adj v (some w) u).isSome = true) =
      insert v ((Finset.univ : Finset (Fin M)).filter (fun u => (adj u).isSome = true)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases h : u = v
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  rw [heq, Finset.card_insert_of_notMem hnot]

lemma someCount_update_some_of_some (adj : Fin M → Option ℕ) (v : Fin M) {w' : ℕ} (w : ℕ)
    (hv : adj v = some w') :
    someCount (Function.update adj v (some w)) = someCount adj := by
  unfold someCount
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : u = v
  · subst h; simp [hv]
  · simp [Function.update_of_ne h]

lemma accStep_spec (n : ℕ) (gs : List Gate) (adj : Fin M → Option ℕ) (v : Fin M) (w : ℕ)
    (hwf : WellFormed n gs) (hadj : ∀ z r, adj z = some r → r < n + gs.length)
    (hw : w < n + gs.length) :
    let st' := accStep n (gs, adj) v w
    WellFormed n st'.1 ∧
    (∀ z r, st'.2 z = some r → r < n + st'.1.length) ∧
    st'.1.countP isBinGate + someCount st'.2 = gs.countP isBinGate + someCount adj + 1 ∧
    st'.1.countP isNLGate = gs.countP isNLGate ∧
    (∀ z, z ≠ v → st'.2 z = adj z) ∧
    (∀ x, x.length = n → ∀ r < n + gs.length,
      (st'.1.foldl stepWires x).getD r false = (gs.foldl stepWires x).getD r false) ∧
    (∀ x, x.length = n → ∀ z,
      evalOpt st'.1 x (st'.2 z) =
        if z = v then xor (evalOpt gs x (adj v)) ((gs.foldl stepWires x).getD w false)
        else evalOpt gs x (adj z)) := by
  intro st'
  cases hv : adj v with
  | none =>
    have hst : st' = (gs, Function.update adj v (some w)) := by simp [st', accStep, hv]
    rw [hst]
    dsimp only
    refine ⟨hwf, ?_, ?_, rfl, ?_, fun _ _ _ _ => rfl, ?_⟩
    · intro z r hz
      by_cases hzv : z = v
      · subst hzv; rw [Function.update_self] at hz; cases hz; exact hw
      · rw [Function.update_of_ne hzv] at hz; exact hadj z r hz
    · rw [someCount_update_some_of_none adj v w hv]; omega
    · intro z hz; exact Function.update_of_ne hz _ _
    · intro x _ z
      by_cases hzv : z = v
      · subst hzv; simp [evalOpt, hv]
      · simp [hzv, Function.update_of_ne hzv]
  | some w' =>
    have hst : st' = (gs ++ xorGates (n + gs.length) w' w,
        Function.update adj v (some (n + gs.length + 1))) := by simp [st', accStep, hv]
    rw [hst]
    dsimp only
    have hw' : w' < n + gs.length := hadj v w' hv
    have hwf' := wellFormed_append_xor hwf hw' hw
    have hlen' : (gs ++ xorGates (n + gs.length) w' w).length = gs.length + 2 := by
      simp [xorGates]
    refine ⟨hwf', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z r hz
      by_cases hzv : z = v
      · subst hzv; rw [Function.update_self] at hz; cases hz; omega
      · rw [Function.update_of_ne hzv] at hz
        have := hadj z r hz; omega
    · rw [List.countP_append, xorGates_countB, someCount_update_some_of_some adj v _ hv]
      omega
    · rw [List.countP_append, xorGates_countT]; omega
    · intro z hz; exact Function.update_of_ne hz _ _
    · intro x hx r hr
      exact (foldl_append_xor_eval gs w' w x hx hw' hw).1 r hr
    · intro x hx z
      have hev := foldl_append_xor_eval gs w' w x hx hw' hw
      by_cases hzv : z = v
      · subst hzv
        simp only [↓reduceIte, Function.update_self, evalOpt, hv]
        exact hev.2
      · simp only [hzv, ↓reduceIte, Function.update_of_ne hzv]
        cases hzj : adj z with
        | none => rfl
        | some r =>
          simp only [evalOpt]
          exact hev.1 r (hadj z r hzj)

lemma gateStep_spec (n : ℕ)
    (hacyc : ∀ v, 0 < rk v → rk (p1 v) < rk v ∧ rk (p2 v) < rk v)
    (gs : List Gate) (adj : Fin M → Option ℕ) (u : Fin M) (hu : 0 < rk u)
    (hwf : WellFormed n gs) (hadj : ∀ z r, adj z = some r → r < n + gs.length) :
    let st' := gateStep p1 p2 n (gs, adj) u
    WellFormed n st'.1 ∧
    (∀ z r, st'.2 z = some r → r < n + st'.1.length) ∧
    st'.1.countP isBinGate + someCount st'.2 ≤ gs.countP isBinGate + someCount adj + 1 ∧
    st'.1.countP isNLGate = gs.countP isNLGate ∧
    st'.2 u = none ∧
    (∀ z, rk u ≤ rk z → z ≠ u → st'.2 z = adj z) ∧
    (∀ (x : List Bool), x.length = n → ∀ (a : Fin M → Bool),
      xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt st'.1 x (st'.2 v)) =
      xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt gs x (adj v))) := by
  intro st'
  have hp := hacyc u hu
  have hp1ne : p1 u ≠ u := fun h => by rw [h] at hp; omega
  have hp2ne : p2 u ≠ u := fun h => by rw [h] at hp; omega
  cases huo : adj u with
  | none =>
    have hst : st' = (gs, adj) := by simp [st', gateStep, huo]
    rw [hst]
    exact ⟨hwf, hadj, Nat.le_succ _, rfl, huo, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | some w =>
    have hw : w < n + gs.length := hadj u w huo
    set adj0 := Function.update adj u none
    have hadj0 : ∀ z r, adj0 z = some r → r < n + gs.length := by
      intro z r hz
      by_cases hzu : z = u
      · subst hzu; simp [adj0] at hz
      · simp only [adj0, Function.update_of_ne hzu] at hz; exact hadj z r hz
    have hsc0 := someCount_update_none adj u huo
    have h1 := accStep_spec n gs adj0 (p1 u) w hwf hadj0 hw
    set st1 := accStep n (gs, adj0) (p1 u) w
    have hw1 : w < n + st1.1.length := by
      have hst1 : st1 = accStep n (gs, adj0) (p1 u) w := rfl
      unfold accStep at hst1; dsimp only at hst1
      cases hp1v : adj0 (p1 u) with
      | none => rw [hp1v] at hst1; simp only at hst1; rw [hst1]; exact hw
      | some w' =>
        rw [hp1v] at hst1; simp only at hst1; rw [hst1]
        simp only [List.length_append, xorGates, List.length_cons, List.length_nil]; omega
    have h2 := accStep_spec n st1.1 st1.2 (p2 u) w h1.1 h1.2.1 hw1
    set st2 := accStep n st1 (p2 u) w
    have hst : st' = st2 := by simp [st', gateStep, huo, adj0, st1, st2]
    rw [hst]
    refine ⟨h2.1, h2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · have hc1 : st1.1.countP isBinGate + someCount st1.2 = gs.countP isBinGate + someCount adj0 + 1 :=
        h1.2.2.1
      have hc2 : st2.1.countP isBinGate + someCount st2.2 = st1.1.countP isBinGate + someCount st1.2 + 1 :=
        h2.2.2.1
      have hsc0' : someCount adj0 + 1 = someCount adj := hsc0
      omega
    · rw [h2.2.2.2.1, h1.2.2.2.1]
    · rw [h2.2.2.2.2.1 u hp2ne.symm, h1.2.2.2.2.1 u hp1ne.symm]
      simp [adj0]
    · intro z hrz hzu
      have hzp1 : z ≠ p1 u := fun h => by rw [h] at hrz; omega
      have hzp2 : z ≠ p2 u := fun h => by rw [h] at hrz; omega
      rw [h2.2.2.2.2.1 z hzp2, h1.2.2.2.2.1 z hzp1]
      exact Function.update_of_ne hzu _ _
    · intro x hx a
      have hwval1 : (st1.1.foldl stepWires x).getD w false = (gs.foldl stepWires x).getD w false :=
        h1.2.2.2.2.2.1 x hx w hw
      have hstep2 :
          xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt st2.1 x (st2.2 v)) =
          xor (xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt st1.1 x (st1.2 v)))
              (fwdEval rk p1 p2 a (p2 u) && (gs.foldl stepWires x).getD w false) := by
        have hfn : ∀ v ∈ (Finset.univ : Finset (Fin M)),
            (fwdEval rk p1 p2 a v && evalOpt st2.1 x (st2.2 v)) =
            xor (fwdEval rk p1 p2 a v && evalOpt st1.1 x (st1.2 v))
                (decide (v = p2 u) && (fwdEval rk p1 p2 a v && (gs.foldl stepWires x).getD w false)) := by
          intro v _
          rw [h2.2.2.2.2.2.2 x hx v, hwval1]
          by_cases hv : v = p2 u
          · subst hv; simp [Bool.and_xor_distrib_left]
          · simp [hv]
        rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite]
        simp
      have hstep1 :
          xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt st1.1 x (st1.2 v)) =
          xor (xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt gs x (adj0 v)))
              (fwdEval rk p1 p2 a (p1 u) && (gs.foldl stepWires x).getD w false) := by
        have hfn : ∀ v ∈ (Finset.univ : Finset (Fin M)),
            (fwdEval rk p1 p2 a v && evalOpt st1.1 x (st1.2 v)) =
            xor (fwdEval rk p1 p2 a v && evalOpt gs x (adj0 v))
                (decide (v = p1 u) && (fwdEval rk p1 p2 a v && (gs.foldl stepWires x).getD w false)) := by
          intro v _
          rw [h1.2.2.2.2.2.2 x hx v]
          by_cases hv : v = p1 u
          · subst hv; simp [Bool.and_xor_distrib_left]
          · simp [hv]
        rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite]
        simp
      have hstep0 :
          xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt gs x (adj0 v)) =
          xor (xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt gs x (adj v)))
              (fwdEval rk p1 p2 a u && (gs.foldl stepWires x).getD w false) := by
        have hfn : ∀ v ∈ (Finset.univ : Finset (Fin M)),
            (fwdEval rk p1 p2 a v && evalOpt gs x (adj0 v)) =
            xor (fwdEval rk p1 p2 a v && evalOpt gs x (adj v))
                (decide (v = u) && (fwdEval rk p1 p2 a v && (gs.foldl stepWires x).getD w false)) := by
          intro v _
          by_cases hv : v = u
          · subst hv; simp [adj0, evalOpt, huo]
          · simp [adj0, hv, Function.update_of_ne hv]
        rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite]
        simp
      rw [hstep2, hstep1, hstep0, fwdEval_gate rk p1 p2 hacyc a u hu]
      generalize xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt gs x (adj v)) = S
      generalize fwdEval rk p1 p2 a (p1 u) = f1
      generalize fwdEval rk p1 p2 a (p2 u) = f2
      generalize (gs.foldl stepWires x).getD w false = ww
      cases S <;> cases f1 <;> cases f2 <;> cases ww <;> rfl

lemma foldl_gateStep_spec (n : ℕ)
    (hacyc : ∀ v, 0 < rk v → rk (p1 v) < rk v ∧ rk (p2 v) < rk v)
    (L : List (Fin M)) (hpos : ∀ u ∈ L, 0 < rk u) (hnodup : L.Nodup)
    (hord : L.Pairwise (fun u v => rk v ≤ rk u))
    (gs : List Gate) (adj : Fin M → Option ℕ)
    (hwf : WellFormed n gs) (hadj : ∀ z r, adj z = some r → r < n + gs.length) :
    let stF := L.foldl (gateStep p1 p2 n) (gs, adj)
    WellFormed n stF.1 ∧
    (∀ z r, stF.2 z = some r → r < n + stF.1.length) ∧
    stF.1.countP isBinGate + someCount stF.2 ≤ gs.countP isBinGate + someCount adj + L.length ∧
    stF.1.countP isNLGate = gs.countP isNLGate ∧
    (∀ u ∈ L, stF.2 u = none) ∧
    (∀ z, (∀ u ∈ L, rk u ≤ rk z ∧ z ≠ u) → stF.2 z = adj z) ∧
    (∀ (x : List Bool), x.length = n → ∀ (a : Fin M → Bool),
      xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt stF.1 x (stF.2 v)) =
      xorSum Finset.univ (fun v => fwdEval rk p1 p2 a v && evalOpt gs x (adj v))) := by
  induction L generalizing gs adj with
  | nil =>
    exact ⟨hwf, hadj, by simp, rfl, by simp, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | cons u L ih =>
    simp only [List.foldl_cons]
    have hu_pos : 0 < rk u := hpos u List.mem_cons_self
    have hL_pos : ∀ v ∈ L, 0 < rk v := fun v hv => hpos v (List.mem_cons_of_mem _ hv)
    have hnodup' := List.nodup_cons.mp hnodup
    have hord' := List.pairwise_cons.mp hord
    have h1 := gateStep_spec rk p1 p2 n hacyc gs adj u hu_pos hwf hadj
    set st1 := gateStep p1 p2 n (gs, adj) u
    have h2 := ih hL_pos hnodup'.2 hord'.2 st1.1 st1.2 h1.1 h1.2.1
    refine ⟨h2.1, h2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · have hc1 : st1.1.countP isBinGate + someCount st1.2 ≤ gs.countP isBinGate + someCount adj + 1 :=
        h1.2.2.1
      have hc2 : (L.foldl (gateStep p1 p2 n) st1).1.countP isBinGate +
          someCount (L.foldl (gateStep p1 p2 n) st1).2 ≤
          st1.1.countP isBinGate + someCount st1.2 + L.length := h2.2.2.1
      simp only [List.length_cons]; omega
    · rw [h2.2.2.2.1, h1.2.2.2.1]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hvL
      · rw [h2.2.2.2.2.2.1 v (fun w hw => ⟨hord'.1 w hw, fun heq => hnodup'.1 (heq ▸ hw)⟩)]
        exact h1.2.2.2.2.1
      · exact h2.2.2.2.2.1 v hvL
    · intro z hz
      have hzu := hz u List.mem_cons_self
      rw [h2.2.2.2.2.2.1 z (fun w hw => hz w (List.mem_cons_of_mem _ hw)),
          h1.2.2.2.2.2.1 z hzu.1 hzu.2]
    · intro x hx a
      rw [h2.2.2.2.2.2.2 x hx a, h1.2.2.2.2.2.2 x hx a]

def gateOrder (R : ℕ) : List (Fin M) :=
  ((List.range R).reverse).flatMap (fun r => (List.finRange M).filter (fun v => rk v == r + 1))

lemma mem_gateOrder {R : ℕ} (hR : ∀ v, rk v ≤ R) (v : Fin M) :
    v ∈ gateOrder rk R ↔ 0 < rk v := by
  unfold gateOrder
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_filter,
    List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · rintro ⟨r, _, hr⟩; omega
  · intro hpos
    refine ⟨rk v - 1, ?_, ?_⟩
    · have := hR v; omega
    · omega

lemma gateOrder_nodup (R : ℕ) : (gateOrder rk R).Nodup := by
  unfold gateOrder
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro r _
    exact List.Nodup.filter _ (List.nodup_finRange M)
  · have hrev : (List.range R).reverse.Pairwise (· ≠ ·) :=
      List.pairwise_reverse.mpr (List.Pairwise.imp (fun h => ne_of_gt h) List.pairwise_lt_range)
    exact List.Pairwise.imp_of_mem (fun {r1 r2} _ _ hne v hv1 hv2 => by
      have h1 := beq_iff_eq.mp (List.mem_filter.mp hv1).2
      have h2 := beq_iff_eq.mp (List.mem_filter.mp hv2).2
      exact hne (by omega)) hrev

lemma gateOrder_pairwise (R : ℕ) : (gateOrder rk R).Pairwise (fun u v => rk v ≤ rk u) := by
  unfold gateOrder
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro r _
    have hpw : ∀ (l : List (Fin M)), (∀ u ∈ l, rk u = r + 1) → l.Pairwise (fun u v => rk v ≤ rk u) := by
      intro l
      induction l with
      | nil => intro _; exact List.Pairwise.nil
      | cons a l ih =>
        intro hl
        exact List.pairwise_cons.mpr ⟨fun b hb => by
          have ha := hl a List.mem_cons_self
          have hbb := hl b (List.mem_cons_of_mem _ hb)
          omega, ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))⟩
    exact hpw _ (fun u hu => beq_iff_eq.mp (List.mem_filter.mp hu).2)
  · have hrev : (List.range R).reverse.Pairwise (· > ·) :=
      List.pairwise_reverse.mpr List.pairwise_lt_range
    exact List.Pairwise.imp_of_mem (fun {r1 r2} _ _ hgt u hu v hv => by
      have h1 := beq_iff_eq.mp (List.mem_filter.mp hu).2
      have h2 := beq_iff_eq.mp (List.mem_filter.mp hv).2
      omega) hrev

lemma gateOrder_length {R : ℕ} (hR : ∀ v, rk v ≤ R) :
    (gateOrder rk R).length = ((Finset.univ : Finset (Fin M)).filter (fun v => 0 < rk v)).card := by
  have htoFinset : (gateOrder rk R).toFinset = (Finset.univ : Finset (Fin M)).filter (fun v => 0 < rk v) := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_gateOrder rk hR v
  rw [← htoFinset, List.toFinset_card_of_nodup (gateOrder_nodup rk R)]

end AdjointBuilder


section QuadDAG

variable (s : ℕ)

def popcnt (u : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * s))).filter (fun j => u.testBit j.val = true)).card

def isPow2 (u : ℕ) : Bool :=
  (List.range (2 * s)).any (fun j => u == 2 ^ j)

def lowBit (u : ℕ) : ℕ :=
  ((List.range (2 * s)).find? (fun j => u.testBit j)).getD 0

lemma isPow2_iff {u : ℕ} : isPow2 s u = true ↔ ∃ j < 2 * s, u = 2 ^ j := by
  unfold isPow2
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]

lemma popcnt_two_pow {j : ℕ} (hj : j < 2 * s) : popcnt s (2 ^ j) = 1 := by
  unfold popcnt
  have hfilt : (Finset.univ : Finset (Fin (2 * s))).filter (fun i => (2 ^ j).testBit i.val = true) =
      {⟨j, hj⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_two_pow,
      decide_eq_true_eq, Finset.mem_singleton, Fin.ext_iff]
    exact eq_comm
  rw [hfilt, Finset.card_singleton]

lemma exists_bit_of_pos_lt {u : ℕ} (hu0 : 0 < u) (hu : u < 4 ^ s) :
    ∃ j < 2 * s, u.testBit j = true := by
  by_contra h
  push Not at h
  have hall : ∀ j, u.testBit j = false := by
    intro j
    by_cases hj : j < 2 * s
    · exact Bool.eq_false_iff.mpr (h j hj)
    · have : u < 2 ^ j := lt_of_lt_of_le (by rw [← four_pow_eq_two_pow]; exact hu)
        (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.testBit_lt_two_pow this
  have : u = 0 := Nat.eq_of_testBit_eq (fun j => by simp [hall j])
  omega

lemma lowBit_spec {u : ℕ} (hu0 : 0 < u) (hu : u < 4 ^ s) :
    lowBit s u < 2 * s ∧ u.testBit (lowBit s u) = true := by
  obtain ⟨j0, hj0, hbit0⟩ := exists_bit_of_pos_lt s hu0 hu
  unfold lowBit
  cases hf : (List.range (2 * s)).find? (fun j => u.testBit j) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf j0 (List.mem_range.mpr hj0)
    simp [hbit0] at this
  | some j =>
    simp only [Option.getD_some]
    exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some hf), List.find?_some hf⟩

lemma popcnt_ge_two {u : ℕ} (hu0 : 0 < u) (hu : u < 4 ^ s) (hnp : isPow2 s u = false) :
    2 ≤ popcnt s u := by
  obtain ⟨j0, hj0, hbit0⟩ := exists_bit_of_pos_lt s hu0 hu
  have hmem0 : (⟨j0, hj0⟩ : Fin (2 * s)) ∈
      (Finset.univ : Finset (Fin (2 * s))).filter (fun j => u.testBit j.val = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit0⟩
  have hex2 : ∃ j1 : Fin (2 * s), j1 ≠ ⟨j0, hj0⟩ ∧ u.testBit j1.val = true := by
    by_contra h
    push Not at h
    have heq : u = 2 ^ j0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_two_pow]
      by_cases hk : k = j0
      · subst hk; simp [hbit0]
      · simp only [decide_eq_false (Ne.symm hk)]
        by_cases hlt : k < 2 * s
        · exact Bool.eq_false_iff.mpr (h ⟨k, hlt⟩ (fun he => hk (congrArg Fin.val he)))
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by rw [← four_pow_eq_two_pow]; exact hu)
            (Nat.pow_le_pow_right (by omega) (by omega)))
    have hp : isPow2 s u = true := (isPow2_iff s).mpr ⟨j0, hj0, heq⟩
    rw [hp] at hnp; cases hnp
  obtain ⟨j1, hne, hbit1⟩ := hex2
  have hmem1 : j1 ∈ (Finset.univ : Finset (Fin (2 * s))).filter (fun j => u.testBit j.val = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit1⟩
  have hsub : ({⟨j0, hj0⟩, j1} : Finset (Fin (2 * s))) ⊆
      (Finset.univ : Finset (Fin (2 * s))).filter (fun j => u.testBit j.val = true) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx1
    · exact hmem0
    · rw [Finset.mem_singleton.mp hx1]; exact hmem1
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne.symm] at this
  exact this

lemma xor_two_pow_lt {u j : ℕ} (hu : u < 4 ^ s) (hj : j < 2 * s) : u ^^^ 2 ^ j < 4 ^ s := by
  rw [four_pow_eq_two_pow] at hu ⊢
  exact Nat.xor_lt_two_pow hu (Nat.pow_lt_pow_right (by omega) hj)

lemma popcnt_xor_bit {u j : ℕ} (hj : j < 2 * s) (hbit : u.testBit j = true) :
    popcnt s (u ^^^ 2 ^ j) + 1 = popcnt s u := by
  unfold popcnt
  have hmem : (⟨j, hj⟩ : Fin (2 * s)) ∈
      (Finset.univ : Finset (Fin (2 * s))).filter (fun i => u.testBit i.val = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩
  have hfilt : (Finset.univ : Finset (Fin (2 * s))).filter (fun i => (u ^^^ 2 ^ j).testBit i.val = true) =
      ((Finset.univ : Finset (Fin (2 * s))).filter (fun i => u.testBit i.val = true)).erase ⟨j, hj⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Nat.testBit_xor,
      Nat.testBit_two_pow]
    by_cases h : i.val = j
    · have hi : i = ⟨j, hj⟩ := Fin.ext h
      subst hi; simp [hbit]
    · have hne : i ≠ ⟨j, hj⟩ := fun he => h (congrArg Fin.val he)
      simp [hne, Ne.symm h]
  rw [hfilt]
  exact Finset.card_erase_add_one hmem

lemma testBit_lo_zero {u i : ℕ} (hdiv : u / 2 ^ s = 0) (hi : s ≤ i) : u.testBit i = false := by
  have hlt : u < 2 ^ s := by
    by_contra hge
    have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
    have : 1 ≤ u / 2 ^ s := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hi))

lemma testBit_hi_zero {u i : ℕ} (hmod : u % 2 ^ s = 0) (hi : i < s) : u.testBit i = false := by
  have hdvd : 2 ^ s ∣ u := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, rfl⟩ := hdvd
  rw [Nat.testBit_two_pow_mul]
  simp [show ¬(s ≤ i) by omega]

lemma popcnt_le_s_of_half_zero {u : ℕ} (h : u / 2 ^ s = 0 ∨ u % 2 ^ s = 0) :
    popcnt s u ≤ s := by
  unfold popcnt
  rcases h with hdiv | hmod
  · have hsub : (Finset.univ : Finset (Fin (2 * s))).filter (fun i => u.testBit i.val = true) ⊆
        (Finset.univ : Finset (Fin (2 * s))).filter (fun i => i.val < s) := by
      intro i hi
      have hbit := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hge
      rw [testBit_lo_zero s hdiv (by omega)] at hbit; cases hbit
    have hcard : ((Finset.univ : Finset (Fin (2 * s))).filter (fun i => i.val < s)).card = s := by
      have heq : (Finset.univ : Finset (Fin (2 * s))).filter (fun i => i.val < s) =
          (Finset.univ : Finset (Fin s)).image (fun i : Fin s => ⟨i.val, by omega⟩) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hi; exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        · rintro ⟨j, rfl⟩; exact j.isLt
      have hinj1 : Function.Injective (fun i : Fin s => (⟨i.val, by omega⟩ : Fin (2 * s))) :=
        fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)
      rw [heq, Finset.card_image_of_injective _ hinj1, Finset.card_univ, Fintype.card_fin]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)
  · have hsub : (Finset.univ : Finset (Fin (2 * s))).filter (fun i => u.testBit i.val = true) ⊆
        (Finset.univ : Finset (Fin (2 * s))).filter (fun i => s ≤ i.val) := by
      intro i hi
      have hbit := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hlt
      rw [testBit_hi_zero s hmod (by omega)] at hbit; cases hbit
    have hcard : ((Finset.univ : Finset (Fin (2 * s))).filter (fun i => s ≤ i.val)).card = s := by
      have heq : (Finset.univ : Finset (Fin (2 * s))).filter (fun i => s ≤ i.val) =
          (Finset.univ : Finset (Fin s)).image (fun i : Fin s => ⟨s + i.val, by omega⟩) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hi; refine ⟨⟨i.val - s, by have := i.isLt; omega⟩, Fin.ext ?_⟩; dsimp only; omega
        · rintro ⟨j, rfl⟩; dsimp only; omega
      have hinj2 : Function.Injective (fun i : Fin s => (⟨s + i.val, by omega⟩ : Fin (2 * s))) :=
        fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp only at this; omega)
      rw [heq, Finset.card_image_of_injective _ hinj2, Finset.card_univ, Fintype.card_fin]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)

lemma quadFun_eq_false_of_half_zero {u : Fin (4 ^ s)}
    (h : u.val / 2 ^ s = 0 ∨ u.val % 2 ^ s = 0) : quadFun s u = false := by
  unfold quadFun
  have hfilt : (Finset.univ : Finset (Fin s)).filter (fun i =>
      u.val.testBit i.val && u.val.testBit (s + i.val)) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rcases h with hdiv | hmod
    · rw [testBit_lo_zero s hdiv (i := s + i.val) (by omega)]; simp
    · rw [testBit_hi_zero s hmod i.isLt]; simp
  rw [hfilt]; simp


def dagRk (v : Fin (4 ^ s + 1)) : ℕ :=
  if v.val = 0 then 0
  else if v.val = 4 ^ s then 1
  else if isPow2 s v.val then 0
  else
    let uL := v.val % 2 ^ s
    let uR := v.val / 2 ^ s
    if uR = 0 ∨ uL = 0 then popcnt s v.val - 1
    else if hlt : v.val < 4 ^ s then
      if quadFun s ⟨v.val, hlt⟩ = false then s
      else if uL % 2 = 1 then
        if uR = 1 then (if uL = 1 then s + 1 else s + 2)
        else s + 3
      else if uR % 2 = 0 then s + 4
      else s + 5
    else 0

def mkV (x : ℕ) : Fin (4 ^ s + 1) :=
  if h : x < 4 ^ s + 1 then ⟨x, h⟩ else ⟨0, by positivity⟩

def dagP1 (v : Fin (4 ^ s + 1)) : Fin (4 ^ s + 1) :=
  if v.val = 0 then mkV s 0
  else if v.val = 4 ^ s then mkV s 1
  else if isPow2 s v.val then v
  else
    let uL := v.val % 2 ^ s
    let uR := v.val / 2 ^ s
    if uR = 0 ∨ uL = 0 then mkV s (v.val ^^^ 2 ^ lowBit s v.val)
    else if hlt : v.val < 4 ^ s then
      if quadFun s ⟨v.val, hlt⟩ = false then mkV s uL
      else if uL % 2 = 1 then
        if uR = 1 then
          if uL = 1 then mkV s (4 ^ s) else mkV s (1 + 2 ^ s)
        else mkV s (uL + 2 ^ s)
      else if uR % 2 = 0 then mkV s ((uL ^^^ 1) + uR * 2 ^ s)
      else mkV s (uL + (uR ^^^ 1) * 2 ^ s)
    else mkV s 0

def dagP2 (v : Fin (4 ^ s + 1)) : Fin (4 ^ s + 1) :=
  if v.val = 0 then mkV s 0
  else if v.val = 4 ^ s then mkV s 0
  else if isPow2 s v.val then v
  else
    let uL := v.val % 2 ^ s
    let uR := v.val / 2 ^ s
    if uR = 0 ∨ uL = 0 then mkV s (2 ^ lowBit s v.val)
    else if hlt : v.val < 4 ^ s then
      if quadFun s ⟨v.val, hlt⟩ = false then mkV s (uR * 2 ^ s)
      else if uL % 2 = 1 then
        if uR = 1 then
          if uL = 1 then mkV s (2 ^ s) else mkV s (uL ^^^ 1)
        else mkV s ((uR ^^^ 1) * 2 ^ s)
      else if uR % 2 = 0 then mkV s 1
      else mkV s (2 ^ s)
    else mkV s 0

lemma mkV_val {x : ℕ} (hx : x < 4 ^ s + 1) : (mkV s x).val = x := by
  unfold mkV; simp [hx]

lemma dagRk_le (v : Fin (4 ^ s + 1)) : dagRk s v ≤ s + 5 := by
  unfold dagRk
  by_cases h0 : v.val = 0
  · simp [h0]
  · by_cases hN : v.val = 4 ^ s
    · have h4ne : 4 ^ s ≠ 0 := by positivity
      simp only [hN, h4ne, ↓reduceIte]; omega
    · by_cases hp : isPow2 s v.val = true
      · simp only [h0, ↓reduceIte, hN, hp]; omega
      · have hpF : isPow2 s v.val = false := Bool.eq_false_iff.mpr hp
        simp only [h0, ↓reduceIte, hN, hpF, Bool.false_eq_true]
        by_cases hhalf : v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0
        · simp only [hhalf, ↓reduceIte]
          have hle := popcnt_le_s_of_half_zero s hhalf
          omega
        · simp only [hhalf, ↓reduceIte]
          by_cases hlt : v.val < 4 ^ s
          · simp only [hlt, ↓reduceDIte]
            split_ifs <;> omega
          · simp only [hlt, ↓reduceDIte]; omega

lemma dagRk_zero_iff (hs : 1 ≤ s) (v : Fin (4 ^ s + 1)) :
    dagRk s v = 0 ↔ v.val = 0 ∨ isPow2 s v.val = true := by
  unfold dagRk
  by_cases h0 : v.val = 0
  · simp [h0]
  · by_cases hN : v.val = 4 ^ s
    · have hnp : isPow2 s (4 ^ s) = false := by
        by_contra h
        obtain ⟨j, hj, heq⟩ := (isPow2_iff s).mp (Bool.eq_true_of_not_eq_false h)
        rw [four_pow_eq_two_pow] at heq
        have := (Nat.pow_right_injective (by omega : 2 ≤ 2)) heq
        omega
      have h4ne : 4 ^ s ≠ 0 := by positivity
      simp [hN, h4ne, hnp]
    · have hlt : v.val < 4 ^ s := by omega
      by_cases hp : isPow2 s v.val = true
      · simp [h0, hN, hp]
      · have hpF : isPow2 s v.val = false := Bool.eq_false_iff.mpr hp
        simp only [h0, ↓reduceIte, hN, hpF, Bool.false_eq_true, or_self, iff_false]
        by_cases hhalf : v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0
        · simp only [hhalf, ↓reduceIte]
          have h2 := popcnt_ge_two s (by omega) hlt hpF
          omega
        · simp only [hhalf, ↓reduceIte, hlt, ↓reduceDIte]
          by_cases hq : quadFun s ⟨v.val, hlt⟩ = false
          · simp only [hq, ↓reduceIte]; omega
          · have hqT : quadFun s ⟨v.val, hlt⟩ = true := Bool.eq_true_of_not_eq_false hq
            simp only [hqT, Bool.true_eq_false, ↓reduceIte]
            by_cases h1 : (v.val % 2 ^ s) % 2 = 1
            · simp only [h1, ↓reduceIte]
              by_cases h2 : v.val / 2 ^ s = 1
              · simp only [h2, ↓reduceIte]
                by_cases h3 : v.val % 2 ^ s = 1 <;> simp only [h3, ↓reduceIte] <;> omega
              · simp only [h2, ↓reduceIte]; omega
            · simp only [h1, ↓reduceIte]
              by_cases h4 : (v.val / 2 ^ s) % 2 = 0 <;> simp only [h4, ↓reduceIte] <;> omega

lemma dagRk_pos_card (hs : 1 ≤ s) :
    ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => 0 < dagRk s v)).card = 4 ^ s - 2 * s := by
  have h0set : (Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => dagRk s v = 0) =
      insert ⟨0, by positivity⟩
        ((Finset.univ : Finset (Fin (2 * s))).image (fun j : Fin (2 * s) =>
          ⟨2 ^ j.val, by rw [four_pow_eq_two_pow]; have := Nat.pow_lt_pow_right (by omega : 1 < 2) j.isLt; omega⟩)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dagRk_zero_iff s hs v,
      Finset.mem_insert, Finset.mem_image, Fin.ext_iff]
    constructor
    · rintro (h0 | hp)
      · left; exact h0
      · right
        obtain ⟨j, hj, heq⟩ := (isPow2_iff s).mp hp
        exact ⟨⟨j, hj⟩, heq.symm⟩
    · rintro (h0 | ⟨j, heq⟩)
      · left; exact h0
      · right; exact (isPow2_iff s).mpr ⟨j.val, j.isLt, heq.symm⟩
  have hnot0 : (⟨0, by positivity⟩ : Fin (4 ^ s + 1)) ∉
      (Finset.univ : Finset (Fin (2 * s))).image (fun j : Fin (2 * s) =>
        ⟨2 ^ j.val, by rw [four_pow_eq_two_pow]; have := Nat.pow_lt_pow_right (by omega : 1 < 2) j.isLt; omega⟩) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.ext_iff, not_exists]
    intro j h
    have := Nat.two_pow_pos j.val; omega
  have hinj : Function.Injective (fun j : Fin (2 * s) =>
      (⟨2 ^ j.val, by rw [four_pow_eq_two_pow]; have := Nat.pow_lt_pow_right (by omega : 1 < 2) j.isLt; omega⟩ : Fin (4 ^ s + 1))) := by
    intro a b h
    have hv : 2 ^ a.val = 2 ^ b.val := congrArg Fin.val h
    exact Fin.ext (Nat.pow_right_injective (by omega : 2 ≤ 2) hv)
  have h0card : ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => dagRk s v = 0)).card = 2 * s + 1 := by
    rw [h0set, Finset.card_insert_of_notMem hnot0, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => 0 < dagRk s v))
      ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => dagRk s v = 0)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2
    omega
  have hunion : ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => 0 < dagRk s v)) ∪
      ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => dagRk s v = 0)) = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
  have hsum : ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => 0 < dagRk s v)).card +
      ((Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => dagRk s v = 0)).card = 4 ^ s + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have h4s_ge : 2 * s + 1 ≤ 4 ^ s := by
    have : ∀ m, m + 1 ≤ 2 ^ m := fun m => by
      induction m with | zero => simp | succ m ih => rw [pow_succ]; omega
    rw [four_pow_eq_two_pow]; exact this (2 * s)
  omega


lemma lo_hi_add (u : ℕ) : u % 2 ^ s + u / 2 ^ s * 2 ^ s = u := by
  rw [Nat.mul_comm, Nat.add_comm]
  exact Nat.div_add_mod u (2 ^ s)

lemma testBit_lo_hi_add {a b : ℕ} (ha : a < 2 ^ s) (k : ℕ) :
    (a + b * 2 ^ s).testBit k = if k < s then a.testBit k else b.testBit (k - s) := by
  rw [Nat.add_comm, Nat.mul_comm b (2 ^ s), Nat.two_pow_add_eq_or_of_lt ha, Nat.testBit_or,
    Nat.testBit_two_pow_mul]
  by_cases hk : k < s
  · have hge : ¬(s ≤ k) := by omega
    simp [hk, hge]
  · have hge : s ≤ k := by omega
    have ha0 : a.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hge))
    simp [hk, hge, ha0]

lemma quadFun_lo_hi {a b : ℕ} (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    quadFun s ⟨a + b * 2 ^ s, by
      rw [four_pow_eq_mul]
      have h1 : (b + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hb
      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ =
    xorSum (Finset.univ : Finset (Fin s)) (fun i => a.testBit i.val && b.testBit i.val) := by
  change xorSum (Finset.univ : Finset (Fin s)) (fun i =>
    (a + b * 2 ^ s).testBit i.val && (a + b * 2 ^ s).testBit (s + i.val)) = _
  apply xorSum_congr rfl
  intro i _
  rw [testBit_lo_hi_add s ha i.val, testBit_lo_hi_add s ha (s + i.val)]
  simp [i.isLt, show ¬(s + i.val < s) by omega]

lemma xor_and_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma quadFun_xor_one_lo (hs : 1 ≤ s) {a b : ℕ} (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    quadFun s ⟨(a ^^^ 1) + b * 2 ^ s, by
      have ha' : a ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow ha (Nat.one_lt_two_pow (by omega))
      rw [four_pow_eq_mul]
      have h1 : (b + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hb
      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ =
    xor (quadFun s ⟨a + b * 2 ^ s, by
      rw [four_pow_eq_mul]
      have h1 : (b + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hb
      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩) (b.testBit 0) := by
  have ha' : a ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow ha (Nat.one_lt_two_pow (by omega))
  rw [quadFun_lo_hi s ha' hb, quadFun_lo_hi s ha hb]
  let z0 : Fin s := ⟨0, by omega⟩
  have hfn : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ((a ^^^ 1).testBit i.val && b.testBit i.val) =
      xor (a.testBit i.val && b.testBit i.val) (decide (i = z0) && b.testBit i.val) := by
    intro i _
    rw [Nat.testBit_xor]
    by_cases h0 : i = z0
    · rw [h0]; simp only [z0, decide_true, Bool.true_and, Nat.testBit_zero, Nat.one_mod, decide_true, Bool.xor_true]
      cases decide (a % 2 = 1) <;> cases decide (b % 2 = 1) <;> rfl
    · have h0v : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have h10 : (1 : ℕ).testBit i.val = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ i.val)))
      simp [h0, h10]
  rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite]
  simp [z0]

lemma quadFun_xor_one_hi (hs : 1 ≤ s) {a b : ℕ} (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    quadFun s ⟨a + (b ^^^ 1) * 2 ^ s, by
      have hb' : b ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow hb (Nat.one_lt_two_pow (by omega))
      rw [four_pow_eq_mul]
      have h1 : ((b ^^^ 1) + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hb'
      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ =
    xor (quadFun s ⟨a + b * 2 ^ s, by
      rw [four_pow_eq_mul]
      have h1 : (b + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hb
      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩) (a.testBit 0) := by
  have hb' : b ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow hb (Nat.one_lt_two_pow (by omega))
  rw [quadFun_lo_hi s ha hb', quadFun_lo_hi s ha hb]
  let z0 : Fin s := ⟨0, by omega⟩
  have hfn : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      (a.testBit i.val && (b ^^^ 1).testBit i.val) =
      xor (a.testBit i.val && b.testBit i.val) (decide (i = z0) && a.testBit i.val) := by
    intro i _
    rw [Nat.testBit_xor]
    by_cases h0 : i = z0
    · rw [h0]; simp only [z0, decide_true, Bool.true_and, Nat.testBit_zero, Nat.one_mod, decide_true, Bool.xor_true]
      cases decide (a % 2 = 1) <;> cases decide (b % 2 = 1) <;> rfl
    · have h0v : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have h10 : (1 : ℕ).testBit i.val = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ i.val)))
      simp [h0, h10]
  rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite]
  simp [z0]

lemma eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun n => n.testBit i) h
  rw [Nat.testBit_xor, Nat.zero_testBit] at hi
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

lemma mod_two_of_testBit0 (n : ℕ) : n.testBit 0 = decide (n % 2 = 1) := by
  rw [Nat.testBit_zero]

lemma dagRk_of_half_zero (hs : 1 ≤ s) (v : Fin (4 ^ s + 1)) (hvlt : v.val < 4 ^ s)
    (hhalf : v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0) : dagRk s v < s := by
  unfold dagRk
  by_cases h0 : v.val = 0
  · simp [h0]; omega
  · have hN : v.val ≠ 4 ^ s := by omega
    by_cases hp : isPow2 s v.val = true
    · simp only [h0, ↓reduceIte, hN, hp]; omega
    · have hpF : isPow2 s v.val = false := Bool.eq_false_iff.mpr hp
      simp only [h0, ↓reduceIte, hN, hpF, Bool.false_eq_true, hhalf]
      have hle := popcnt_le_s_of_half_zero s hhalf
      omega


lemma dag_s12 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hhalf : v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0) :
    dagRk s v = popcnt s v.val - 1 ∧
    dagP1 s v = mkV s (v.val ^^^ 2 ^ lowBit s v.val) ∧
    dagP2 s v = mkV s (2 ^ lowBit s v.val) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hhalf]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hhalf]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hhalf]

lemma dag_s3 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hnh : ¬(v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0))
    (hlt : v.val < 4 ^ s) (hq : quadFun s ⟨v.val, hlt⟩ = false) :
    dagRk s v = s ∧ dagP1 s v = mkV s (v.val % 2 ^ s) ∧ dagP2 s v = mkV s (v.val / 2 ^ s * 2 ^ s) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq]

lemma dag_s4 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hnh : ¬(v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0))
    (hlt : v.val < 4 ^ s) (hq : quadFun s ⟨v.val, hlt⟩ = true)
    (hL1 : v.val % 2 ^ s = 1) (hR1 : v.val / 2 ^ s = 1) :
    dagRk s v = s + 1 ∧ dagP1 s v = mkV s (4 ^ s) ∧ dagP2 s v = mkV s (2 ^ s) := by
  have hLm : (v.val % 2 ^ s) % 2 = 1 := by rw [hL1]
  have h10 : ¬(1 = 0 ∨ 1 = 0) := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hR1, hL1, h10]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hR1, hL1, h10]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hR1, hL1, h10]

lemma dag_s5 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hnh : ¬(v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0))
    (hlt : v.val < 4 ^ s) (hq : quadFun s ⟨v.val, hlt⟩ = true)
    (hLm : (v.val % 2 ^ s) % 2 = 1) (hR1 : v.val / 2 ^ s = 1) (hLne : v.val % 2 ^ s ≠ 1) :
    dagRk s v = s + 2 ∧ dagP1 s v = mkV s (1 + 2 ^ s) ∧ dagP2 s v = mkV s (v.val % 2 ^ s ^^^ 1) := by
  have h10 : ¬(1 = 0 ∨ v.val % 2 ^ s = 0) := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hR1, hLne, h10]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hR1, hLne, h10]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hR1, hLne, h10]

lemma dag_s6 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hnh : ¬(v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0))
    (hlt : v.val < 4 ^ s) (hq : quadFun s ⟨v.val, hlt⟩ = true)
    (hLm : (v.val % 2 ^ s) % 2 = 1) (hRne : v.val / 2 ^ s ≠ 1) :
    dagRk s v = s + 3 ∧ dagP1 s v = mkV s (v.val % 2 ^ s + 2 ^ s) ∧
    dagP2 s v = mkV s ((v.val / 2 ^ s ^^^ 1) * 2 ^ s) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRne]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRne]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRne]

lemma dag_s7 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hnh : ¬(v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0))
    (hlt : v.val < 4 ^ s) (hq : quadFun s ⟨v.val, hlt⟩ = true)
    (hLm : (v.val % 2 ^ s) % 2 ≠ 1) (hRm : (v.val / 2 ^ s) % 2 = 0) :
    dagRk s v = s + 4 ∧ dagP1 s v = mkV s ((v.val % 2 ^ s ^^^ 1) + v.val / 2 ^ s * 2 ^ s) ∧
    dagP2 s v = mkV s 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRm]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRm]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRm]

lemma dag_s8 {v : Fin (4 ^ s + 1)} (h0 : v.val ≠ 0) (hN : v.val ≠ 4 ^ s)
    (hnp : isPow2 s v.val = false) (hnh : ¬(v.val / 2 ^ s = 0 ∨ v.val % 2 ^ s = 0))
    (hlt : v.val < 4 ^ s) (hq : quadFun s ⟨v.val, hlt⟩ = true)
    (hLm : (v.val % 2 ^ s) % 2 ≠ 1) (hRm : (v.val / 2 ^ s) % 2 ≠ 0) :
    dagRk s v = s + 5 ∧ dagP1 s v = mkV s (v.val % 2 ^ s + (v.val / 2 ^ s ^^^ 1) * 2 ^ s) ∧
    dagP2 s v = mkV s (2 ^ s) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dagRk; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRm]
  · unfold dagP1; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRm]
  · unfold dagP2; simp only [h0, ↓reduceIte, hN, hnp, Bool.false_eq_true, hnh, hlt, ↓reduceDIte, hq,
      Bool.true_eq_false, hLm, hRm]

lemma xor_one_mod2 (n : ℕ) : (n ^^^ 1) % 2 = 1 - n % 2 := by
  have h0 := mod_two_of_testBit0 (n ^^^ 1)
  have h1 := mod_two_of_testBit0 n
  rw [Nat.testBit_xor, h1] at h0
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    rcases Nat.mod_two_eq_zero_or_one (n ^^^ 1) with hx | hx <;> simp_all

lemma two_pow_lt_four_pow {j : ℕ} (hj : j < 2 * s) : 2 ^ j < 4 ^ s :=
  calc 2 ^ j < 2 ^ (2 * s) := Nat.pow_lt_pow_right (by omega) hj
    _ = 4 ^ s := (four_pow_eq_two_pow s).symm

lemma dag_acyclic (hs : 1 ≤ s) (v : Fin (4 ^ s + 1)) (hpos : 0 < dagRk s v) :
    dagRk s (dagP1 s v) < dagRk s v ∧ dagRk s (dagP2 s v) < dagRk s v := by
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2s_gt1 : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
  have h4s_eq : 4 ^ s = 2 ^ s * 2 ^ s := four_pow_eq_mul s
  have hne0 : v.val ≠ 0 := fun h => by
    have := (dagRk_zero_iff s hs v).mpr (Or.inl h); omega
  by_cases hN : v.val = 4 ^ s
  · have h4ne : 4 ^ s ≠ 0 := by positivity
    have hrk : dagRk s v = 1 := by unfold dagRk; simp only [hN, h4ne, ↓reduceIte]
    have hp1 : dagP1 s v = mkV s 1 := by unfold dagP1; simp only [hN, h4ne, ↓reduceIte]
    have hp2 : dagP2 s v = mkV s 0 := by unfold dagP2; simp only [hN, h4ne, ↓reduceIte]
    rw [hrk, hp1, hp2]
    have h1lt : 1 < 4 ^ s + 1 := by have := Nat.one_le_pow s 4 (by omega); omega
    have hrk1 : dagRk s (mkV s 1) = 0 := by
      rw [dagRk_zero_iff s hs]; right
      rw [mkV_val s h1lt, isPow2_iff]; exact ⟨0, by omega, rfl⟩
    have hrk0 : dagRk s (mkV s 0) = 0 := by
      rw [dagRk_zero_iff s hs]; left; exact mkV_val s (by positivity)
    omega
  · have hvlt : v.val < 4 ^ s := by omega
    have hnp : isPow2 s v.val = false := by
      by_contra h
      have := (dagRk_zero_iff s hs v).mpr (Or.inr (Bool.eq_true_of_not_eq_false h))
      omega
    let uL := v.val % 2 ^ s
    let uR := v.val / 2 ^ s
    have huL_lt : uL < 2 ^ s := Nat.mod_lt _ h2s_pos
    have huR_lt : uR < 2 ^ s := Nat.div_lt_of_lt_mul (h4s_eq ▸ hvlt)
    have hv_eq : uL + uR * 2 ^ s = v.val := lo_hi_add s v.val
    by_cases hhalf : uR = 0 ∨ uL = 0
    · -- Stage 1/2
      have hlb := lowBit_spec s (by omega) hvlt
      have hxlt : v.val ^^^ 2 ^ lowBit s v.val < 4 ^ s := xor_two_pow_lt s hvlt hlb.1
      have h2lt : 2 ^ lowBit s v.val < 4 ^ s := two_pow_lt_four_pow s hlb.1
      obtain ⟨hrk, hp1, hp2⟩ := dag_s12 s hne0 hN hnp hhalf
      have hrk2 : dagRk s (dagP2 s v) = 0 := by
        rw [hp2, dagRk_zero_iff s hs]; right
        rw [mkV_val s (by omega), isPow2_iff]; exact ⟨lowBit s v.val, hlb.1, rfl⟩
      have hpop := popcnt_xor_bit s hlb.1 hlb.2
      have hge2 := popcnt_ge_two s (by omega) hvlt hnp
      have hhalf' : (v.val ^^^ 2 ^ lowBit s v.val) / 2 ^ s = 0 ∨
          (v.val ^^^ 2 ^ lowBit s v.val) % 2 ^ s = 0 := by
        rcases hhalf with hR0 | hL0
        · left
          have hlt2s : v.val < 2 ^ s := by rw [← hv_eq, hR0]; simp [huL_lt]
          have hlb_lt : lowBit s v.val < s := by
            by_contra hge
            rw [testBit_lo_zero s hR0 (by omega)] at hlb; cases hlb.2
          have hxlt2s : v.val ^^^ 2 ^ lowBit s v.val < 2 ^ s :=
            Nat.xor_lt_two_pow hlt2s (Nat.pow_lt_pow_right (by omega) hlb_lt)
          exact Nat.div_eq_of_lt hxlt2s
        · right
          have hlb_ge : s ≤ lowBit s v.val := by
            by_contra hlt
            rw [testBit_hi_zero s hL0 (by omega)] at hlb; cases hlb.2
          have hzero : ∀ i < s, (v.val ^^^ 2 ^ lowBit s v.val).testBit i = false := by
            intro i hi
            rw [Nat.testBit_xor, testBit_hi_zero s hL0 hi, Nat.testBit_two_pow]
            simp [show lowBit s v.val ≠ i by omega]
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
          by_cases hi : i < s
          · simp [hi, hzero i hi]
          · simp [hi]
      have hrk1_lt : dagRk s (dagP1 s v) < popcnt s v.val - 1 := by
        rw [hp1]
        by_cases h10 : (mkV s (v.val ^^^ 2 ^ lowBit s v.val)).val = 0 ∨
            isPow2 s (mkV s (v.val ^^^ 2 ^ lowBit s v.val)).val = true
        · rw [(dagRk_zero_iff s hs _).mpr h10]; omega
        · push Not at h10
          have hv1 : (mkV s (v.val ^^^ 2 ^ lowBit s v.val)).val = v.val ^^^ 2 ^ lowBit s v.val :=
            mkV_val s (by omega)
          unfold dagRk
          rw [hv1] at h10 ⊢
          simp only [h10.1, ↓reduceIte, show v.val ^^^ 2 ^ lowBit s v.val ≠ 4 ^ s by omega,
            Bool.eq_false_iff.mpr h10.2, Bool.false_eq_true, hhalf']
          omega
      rw [hrk, hrk2]; omega
    · have hneq_half : ¬(uR = 0 ∨ uL = 0) := hhalf
      have huR_ne0 : uR ≠ 0 := fun h => hhalf (Or.inl h)
      have huL_ne0 : uL ≠ 0 := fun h => hhalf (Or.inr h)
      by_cases hq : quadFun s ⟨v.val, hvlt⟩ = false
      · -- Stage 3
        obtain ⟨hrk, hp1, hp2⟩ := dag_s3 s hne0 hN hnp hneq_half hvlt hq
        change dagP1 s v = mkV s uL at hp1
        change dagP2 s v = mkV s (uR * 2 ^ s) at hp2
        have huL_lt4 : uL < 4 ^ s := by rw [h4s_eq]; exact lt_of_lt_of_le huL_lt (Nat.le_mul_of_pos_right _ h2s_pos)
        have huR_lt4 : uR * 2 ^ s < 4 ^ s := by rw [h4s_eq]; exact Nat.mul_lt_mul_of_pos_right huR_lt h2s_pos
        rw [hrk, hp1, hp2]
        refine ⟨dagRk_of_half_zero s hs _ (by rw [mkV_val s (by omega)]; exact huL_lt4)
                  (Or.inl (by rw [mkV_val s (by omega)]; exact Nat.div_eq_of_lt huL_lt)),
                dagRk_of_half_zero s hs _ (by rw [mkV_val s (by omega)]; exact huR_lt4)
                  (Or.inr (by rw [mkV_val s (by omega)]; exact Nat.mul_mod_left uR (2 ^ s)))⟩
      · have hqT : quadFun s ⟨v.val, hvlt⟩ = true := Bool.eq_true_of_not_eq_false hq
        have h12s_lt : 1 + 2 ^ s < 4 ^ s := by
          rw [h4s_eq]
          have : 2 * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
          omega
        have h12s_rk : dagRk s (mkV s (1 + 2 ^ s)) = s + 1 := by
          have hv12 : (mkV s (1 + 2 ^ s)).val = 1 + 2 ^ s := mkV_val s (by omega)
          have hmod1 : (1 + 2 ^ s) % 2 ^ s = 1 := by
            rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt h2s_gt1]
          have hdiv1 : (1 + 2 ^ s) / 2 ^ s = 1 := by
            rw [Nat.add_div_right 1 h2s_pos, Nat.div_eq_of_lt h2s_gt1]
          have hq12 : quadFun s ⟨1 + 2 ^ s, h12s_lt⟩ = true := by
            have := quadFun_lo_hi s (a := 1) (b := 1) h2s_gt1 h2s_gt1
            simp only [Nat.one_mul] at this
            rw [this]
            have hfilt : (Finset.univ : Finset (Fin s)).filter
                (fun i => (1 : ℕ).testBit i.val && (1 : ℕ).testBit i.val) = {⟨0, by omega⟩} := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
              cases hi : i.val with
              | zero => simp
              | succ k =>
                have : (1 : ℕ).testBit (k + 1) = false :=
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.succ_pos k)))
                simp [this]
            unfold xorSum; rw [hfilt]; simp
          have hnp12 : isPow2 s (1 + 2 ^ s) = false := by
            by_contra h
            obtain ⟨j, hj, heq⟩ := (isPow2_iff s).mp (Bool.eq_true_of_not_eq_false h)
            have hlt_j : 2 ^ s < 2 ^ j := by omega
            have hsj : s < j := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt_j
            have hge2 : 2 ^ (s + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hsj
            rw [pow_succ] at hge2; omega
          exact (dag_s4 s (by omega) (by omega) (by rw [hv12]; exact hnp12)
            (by rw [hv12, hdiv1, hmod1]; omega) (by rw [hv12]; exact h12s_lt)
            (by have : (⟨(mkV s (1 + 2 ^ s)).val, by rw [hv12]; exact h12s_lt⟩ : Fin (4 ^ s)) = ⟨1 + 2 ^ s, h12s_lt⟩ := Fin.ext hv12
                rw [this]; exact hq12)
            (by rw [hv12]; exact hmod1) (by rw [hv12]; exact hdiv1)).1
        by_cases huL1m : uL % 2 = 1
        · by_cases huR1 : uR = 1
          · by_cases huL1 : uL = 1
            · -- Stage 4: (1, 1)
              obtain ⟨hrk, hp1, hp2⟩ := dag_s4 s hne0 hN hnp hneq_half hvlt hqT huL1 huR1
              have hrkN : dagRk s (mkV s (4 ^ s)) = 1 := by
                unfold dagRk; rw [mkV_val s (by omega)]
                simp only [show 4 ^ s ≠ 0 by positivity, ↓reduceIte]
              have hrk2s : dagRk s (mkV s (2 ^ s)) = 0 := by
                rw [dagRk_zero_iff s hs]; right
                rw [mkV_val s (by rw [h4s_eq]; have := Nat.le_mul_of_pos_right (2 ^ s) h2s_pos; omega),
                  isPow2_iff]; exact ⟨s, by omega, rfl⟩
              rw [hrk, hp1, hp2, hrkN, hrk2s]; omega
            · -- Stage 5: uL % 2 = 1, uL ≠ 1, uR = 1
              obtain ⟨hrk, hp1, hp2⟩ := dag_s5 s hne0 hN hnp hneq_half hvlt hqT huL1m huR1 huL1
              change dagP2 s v = mkV s (uL ^^^ 1) at hp2
              have hxlt2s : uL ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huL_lt h2s_gt1
              have hxlt4 : uL ^^^ 1 < 4 ^ s := by rw [h4s_eq]; exact lt_of_lt_of_le hxlt2s (Nat.le_mul_of_pos_right _ h2s_pos)
              have hrk2 : dagRk s (mkV s (uL ^^^ 1)) < s :=
                dagRk_of_half_zero s hs _ (by rw [mkV_val s (by omega)]; exact hxlt4)
                  (Or.inl (by rw [mkV_val s (by omega)]; exact Nat.div_eq_of_lt hxlt2s))
              rw [hrk, hp1, hp2, h12s_rk]; omega
          · -- Stage 6: uL % 2 = 1, uR ≠ 1, q = true
            obtain ⟨hrk, hp1, hp2⟩ := dag_s6 s hne0 hN hnp hneq_half hvlt hqT huL1m huR1
            change dagP1 s v = mkV s (uL + 2 ^ s) at hp1
            change dagP2 s v = mkV s ((uR ^^^ 1) * 2 ^ s) at hp2
            have hu1_lt4 : uL + 2 ^ s < 4 ^ s := by
              rw [h4s_eq]
              have : 2 * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
              omega
            have hrk1 : dagRk s (mkV s (uL + 2 ^ s)) ≤ s + 2 := by
              have hval : (mkV s (uL + 2 ^ s)).val = uL + 2 ^ s := mkV_val s (by omega)
              have hmod' : (uL + 2 ^ s) % 2 ^ s = uL := by
                rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt huL_lt]
              have hdiv' : (uL + 2 ^ s) / 2 ^ s = 1 := by
                rw [Nat.add_div_right uL h2s_pos, Nat.div_eq_of_lt huL_lt]
              unfold dagRk
              rw [hval]
              simp only [show uL + 2 ^ s ≠ 0 by omega, ↓reduceIte, show uL + 2 ^ s ≠ 4 ^ s by omega,
                hu1_lt4, ↓reduceDIte, hmod', hdiv', huL1m]
              by_cases hp' : isPow2 s (uL + 2 ^ s) = true
              · simp only [hp', ↓reduceIte]; omega
              · have hpF : isPow2 s (uL + 2 ^ s) = false := Bool.eq_false_iff.mpr hp'
                simp only [hpF, Bool.false_eq_true, ↓reduceIte, show ¬(1 = 0 ∨ uL = 0) by omega]
                by_cases hq' : quadFun s ⟨uL + 2 ^ s, hu1_lt4⟩ = false
                · simp only [hq', ↓reduceIte]; omega
                · have hqT' : quadFun s ⟨uL + 2 ^ s, hu1_lt4⟩ = true := Bool.eq_true_of_not_eq_false hq'
                  simp only [hqT', Bool.true_eq_false, ↓reduceIte]
                  by_cases huL1 : uL = 1 <;> simp only [huL1, ↓reduceIte] <;> omega
            have huRx_lt : uR ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huR_lt h2s_gt1
            have huRx_lt4 : (uR ^^^ 1) * 2 ^ s < 4 ^ s := by
              rw [h4s_eq]; exact Nat.mul_lt_mul_of_pos_right huRx_lt h2s_pos
            have hrk2 : dagRk s (mkV s ((uR ^^^ 1) * 2 ^ s)) < s :=
              dagRk_of_half_zero s hs _ (by rw [mkV_val s (by omega)]; exact huRx_lt4)
                (Or.inr (by rw [mkV_val s (by omega)]; exact Nat.mul_mod_left _ _))
            rw [hrk, hp1, hp2]; omega
        · by_cases huR2 : uR % 2 = 0
          · -- Stage 7: uL % 2 = 0, uR % 2 = 0, q = true
            obtain ⟨hrk, hp1, hp2⟩ := dag_s7 s hne0 hN hnp hneq_half hvlt hqT huL1m huR2
            change dagP1 s v = mkV s ((uL ^^^ 1) + uR * 2 ^ s) at hp1
            have huLx_lt : uL ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huL_lt h2s_gt1
            have hu1_lt4 : (uL ^^^ 1) + uR * 2 ^ s < 4 ^ s := by
              rw [h4s_eq]
              have h1 : (uR + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ huR_lt
              rw [Nat.add_mul, Nat.one_mul] at h1; omega
            have huLx_mod2 : (uL ^^^ 1) % 2 = 1 := by have := xor_one_mod2 uL; omega
            have hrk1 : dagRk s (mkV s ((uL ^^^ 1) + uR * 2 ^ s)) ≤ s + 3 := by
              have hval : (mkV s ((uL ^^^ 1) + uR * 2 ^ s)).val = (uL ^^^ 1) + uR * 2 ^ s :=
                mkV_val s (by omega)
              have hmod' : ((uL ^^^ 1) + uR * 2 ^ s) % 2 ^ s = uL ^^^ 1 := by
                rw [Nat.add_comm, Nat.mul_add_mod_of_lt huLx_lt]
              have hdiv' : ((uL ^^^ 1) + uR * 2 ^ s) / 2 ^ s = uR := by
                rw [Nat.mul_comm, Nat.add_mul_div_left _ _ h2s_pos, Nat.div_eq_of_lt huLx_lt, Nat.zero_add]
              unfold dagRk
              rw [hval]
              by_cases h0' : (uL ^^^ 1) + uR * 2 ^ s = 0
              · simp only [h0', ↓reduceIte]; omega
              · simp only [h0', ↓reduceIte, show (uL ^^^ 1) + uR * 2 ^ s ≠ 4 ^ s by omega,
                  hu1_lt4, ↓reduceDIte, hmod', hdiv', huLx_mod2]
                by_cases hp' : isPow2 s ((uL ^^^ 1) + uR * 2 ^ s) = true
                · simp only [hp', ↓reduceIte]; omega
                · have hpF : isPow2 s ((uL ^^^ 1) + uR * 2 ^ s) = false := Bool.eq_false_iff.mpr hp'
                  simp only [hpF, Bool.false_eq_true, ↓reduceIte]
                  by_cases hh' : uR = 0 ∨ uL ^^^ 1 = 0
                  · simp only [hh', ↓reduceIte]
                    have hle := popcnt_le_s_of_half_zero s (by rw [hdiv', hmod']; exact hh')
                    omega
                  · simp only [hh', ↓reduceIte]
                    by_cases hq' : quadFun s ⟨(uL ^^^ 1) + uR * 2 ^ s, hu1_lt4⟩ = false
                    · simp only [hq', ↓reduceIte]; omega
                    · have hqT' : quadFun s ⟨(uL ^^^ 1) + uR * 2 ^ s, hu1_lt4⟩ = true := Bool.eq_true_of_not_eq_false hq'
                      simp only [hqT', Bool.true_eq_false, ↓reduceIte]
                      by_cases hr1 : uR = 1
                      · simp only [hr1, ↓reduceIte]; by_cases hl1 : uL ^^^ 1 = 1 <;> simp only [hl1, ↓reduceIte] <;> omega
                      · simp only [hr1, ↓reduceIte]; omega
            have hrk2 : dagRk s (mkV s 1) = 0 := by
              rw [dagRk_zero_iff s hs]; right
              rw [mkV_val s (by have := Nat.one_le_pow s 4 (by omega); omega), isPow2_iff]
              exact ⟨0, by omega, rfl⟩
            rw [hrk, hp1, hp2, hrk2]; omega
          · -- Stage 8: uL % 2 = 0, uR % 2 = 1, q = true
            obtain ⟨hrk, hp1, hp2⟩ := dag_s8 s hne0 hN hnp hneq_half hvlt hqT huL1m huR2
            change dagP1 s v = mkV s (uL + (uR ^^^ 1) * 2 ^ s) at hp1
            have huRx_lt : uR ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huR_lt h2s_gt1
            have hu1_lt4 : uL + (uR ^^^ 1) * 2 ^ s < 4 ^ s := by
              rw [h4s_eq]
              have h1 : ((uR ^^^ 1) + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ huRx_lt
              rw [Nat.add_mul, Nat.one_mul] at h1; omega
            have huRx_mod2 : (uR ^^^ 1) % 2 = 0 := by have := xor_one_mod2 uR; omega
            have hrk1 : dagRk s (mkV s (uL + (uR ^^^ 1) * 2 ^ s)) ≤ s + 4 := by
              have hval : (mkV s (uL + (uR ^^^ 1) * 2 ^ s)).val = uL + (uR ^^^ 1) * 2 ^ s :=
                mkV_val s (by omega)
              have hmod' : (uL + (uR ^^^ 1) * 2 ^ s) % 2 ^ s = uL := by
                rw [Nat.add_comm, Nat.mul_add_mod_of_lt huL_lt]
              have hdiv' : (uL + (uR ^^^ 1) * 2 ^ s) / 2 ^ s = uR ^^^ 1 := by
                rw [Nat.mul_comm, Nat.add_mul_div_left _ _ h2s_pos, Nat.div_eq_of_lt huL_lt, Nat.zero_add]
              unfold dagRk
              rw [hval]
              by_cases h0' : uL + (uR ^^^ 1) * 2 ^ s = 0
              · simp only [h0', ↓reduceIte]; omega
              · simp only [h0', ↓reduceIte, show uL + (uR ^^^ 1) * 2 ^ s ≠ 4 ^ s by omega,
                  hu1_lt4, ↓reduceDIte, hmod', hdiv', huL1m, huRx_mod2]
                by_cases hp' : isPow2 s (uL + (uR ^^^ 1) * 2 ^ s) = true
                · simp only [hp', ↓reduceIte]; omega
                · have hpF : isPow2 s (uL + (uR ^^^ 1) * 2 ^ s) = false := Bool.eq_false_iff.mpr hp'
                  simp only [hpF, Bool.false_eq_true, ↓reduceIte]
                  by_cases hh' : uR ^^^ 1 = 0 ∨ uL = 0
                  · simp only [hh', ↓reduceIte]
                    have hle := popcnt_le_s_of_half_zero s (by rw [hdiv', hmod']; exact hh')
                    omega
                  · simp only [hh', ↓reduceIte]
                    by_cases hq' : quadFun s ⟨uL + (uR ^^^ 1) * 2 ^ s, hu1_lt4⟩ = false
                    · simp only [hq', ↓reduceIte]; omega
                    · have hqT' : quadFun s ⟨uL + (uR ^^^ 1) * 2 ^ s, hu1_lt4⟩ = true := Bool.eq_true_of_not_eq_false hq'
                      simp only [hqT', Bool.true_eq_false, ↓reduceIte]; omega
            have hrk2 : dagRk s (mkV s (2 ^ s)) = 0 := by
              rw [dagRk_zero_iff s hs]; right
              rw [mkV_val s (by rw [h4s_eq]; have := Nat.le_mul_of_pos_right (2 ^ s) h2s_pos; omega),
                isPow2_iff]; exact ⟨s, by omega, rfl⟩
            rw [hrk, hp1, hp2, hrk2]; omega


def specVal (a : Fin (4 ^ s + 1) → Bool) (v : Fin (4 ^ s + 1)) : Bool :=
  if v.val = 0 then a ⟨0, by positivity⟩
  else if hlt : v.val < 4 ^ s then
    xor (xorSum (Finset.univ : Finset (Fin (2 * s))) (fun j =>
          v.val.testBit j.val && a (mkV s (2 ^ j.val))))
        (quadFun s ⟨v.val, hlt⟩ && a ⟨0, by positivity⟩)
  else
    xor (a (mkV s 1)) (a ⟨0, by positivity⟩)

lemma specVal_xor_combine {a : Fin (4 ^ s + 1) → Bool} {u w1 w2 : ℕ}
    (hu0 : u ≠ 0) (hu : u < 4 ^ s) (hw10 : w1 ≠ 0) (hw1 : w1 < 4 ^ s)
    (hw20 : w2 ≠ 0) (hw2 : w2 < 4 ^ s)
    (hbits : ∀ j < 2 * s, u.testBit j = xor (w1.testBit j) (w2.testBit j))
    (hquad : quadFun s ⟨u, hu⟩ = xor (quadFun s ⟨w1, hw1⟩) (quadFun s ⟨w2, hw2⟩)) :
    specVal s a ⟨u, by omega⟩ =
      xor (specVal s a (mkV s w1)) (specVal s a (mkV s w2)) := by
  have hv1 : (mkV s w1).val = w1 := mkV_val s (by omega)
  have hv2 : (mkV s w2).val = w2 := mkV_val s (by omega)
  unfold specVal
  simp only [hu0, ↓reduceIte, hu, ↓reduceDIte, hv1, hw10, hw1, hv2, hw20, hw2]
  have hsum :
      xorSum (Finset.univ : Finset (Fin (2 * s))) (fun j => u.testBit j.val && a (mkV s (2 ^ j.val))) =
      xor (xorSum (Finset.univ : Finset (Fin (2 * s))) (fun j => w1.testBit j.val && a (mkV s (2 ^ j.val))))
          (xorSum (Finset.univ : Finset (Fin (2 * s))) (fun j => w2.testBit j.val && a (mkV s (2 ^ j.val)))) := by
    rw [← xorSum_xor]
    apply xorSum_congr rfl
    intro j _
    rw [hbits j.val j.isLt, xor_and_right]
  rw [hsum, hquad, xor_and_right]
  generalize xorSum Finset.univ (fun j : Fin (2 * s) => w1.testBit j.val && a (mkV s (2 ^ j.val))) = A
  generalize xorSum Finset.univ (fun j : Fin (2 * s) => w2.testBit j.val && a (mkV s (2 ^ j.val))) = B
  generalize (quadFun s ⟨w1, hw1⟩ && a ⟨0, by positivity⟩) = C
  generalize (quadFun s ⟨w2, hw2⟩ && a ⟨0, by positivity⟩) = D
  cases A <;> cases B <;> cases C <;> cases D <;> rfl

lemma fwdEval_eq_specVal (hs : 1 ≤ s) (a : Fin (4 ^ s + 1) → Bool) (v : Fin (4 ^ s + 1)) :
    fwdEval (dagRk s) (dagP1 s) (dagP2 s) a v = specVal s a v := by
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2s_gt1 : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
  have h4s_eq : 4 ^ s = 2 ^ s * 2 ^ s := four_pow_eq_mul s
  induction hk : dagRk s v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    by_cases hpos : 0 < dagRk s v
    · rw [fwdEval_gate (dagRk s) (dagP1 s) (dagP2 s) (dag_acyclic s hs) a v hpos]
      have hacyc := dag_acyclic s hs v hpos
      rw [ih (dagRk s (dagP1 s v)) (by omega) (dagP1 s v) rfl,
          ih (dagRk s (dagP2 s v)) (by omega) (dagP2 s v) rfl]
      have hne0 : v.val ≠ 0 := fun h => by have := (dagRk_zero_iff s hs v).mpr (Or.inl h); omega
      by_cases hN : v.val = 4 ^ s
      · have h4ne : 4 ^ s ≠ 0 := by positivity
        have hp1 : dagP1 s v = mkV s 1 := by unfold dagP1; simp only [hN, h4ne, ↓reduceIte]
        have hp2 : dagP2 s v = mkV s 0 := by unfold dagP2; simp only [hN, h4ne, ↓reduceIte]
        rw [hp1, hp2]
        have h1lt : 1 < 4 ^ s := by have := Nat.pow_le_pow_right (by omega : 1 ≤ 4) hs; omega
        have hv1 : (mkV s 1).val = 1 := mkV_val s (by omega)
        have hv0 : (mkV s 0).val = 0 := mkV_val s (by positivity)
        have hq1 : quadFun s ⟨1, h1lt⟩ = false :=
          quadFun_eq_false_of_half_zero s (Or.inl (Nat.div_eq_of_lt h2s_gt1))
        let z0 : Fin (2 * s) := ⟨0, by omega⟩
        have hsum1 : xorSum (Finset.univ : Finset (Fin (2 * s)))
            (fun j => (1 : ℕ).testBit j.val && a (mkV s (2 ^ j.val))) = a (mkV s 1) := by
          have hfn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * s))),
              ((1 : ℕ).testBit j.val && a (mkV s (2 ^ j.val))) =
              (decide (j = z0) && a (mkV s (2 ^ j.val))) := by
            intro j _
            by_cases hj : j = z0
            · rw [hj]; simp [z0]
            · have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have h0 : (1 : ℕ).testBit j.val = false :=
                Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ j.val)))
              simp [hj, h0]
          rw [xorSum_congr rfl hfn, xorSum_eq_ite]; simp [z0]
        unfold specVal
        simp only [hN, h4ne, ↓reduceIte, lt_irrefl, ↓reduceDIte, hv1, show (1 : ℕ) ≠ 0 by omega,
          h1lt, hsum1, hq1, Bool.false_and, Bool.xor_false, hv0]
      · have hvlt : v.val < 4 ^ s := by omega
        have hnp : isPow2 s v.val = false := by
          by_contra h
          have := (dagRk_zero_iff s hs v).mpr (Or.inr (Bool.eq_true_of_not_eq_false h))
          omega
        let uL := v.val % 2 ^ s
        let uR := v.val / 2 ^ s
        have huL_lt : uL < 2 ^ s := Nat.mod_lt _ h2s_pos
        have huR_lt : uR < 2 ^ s := Nat.div_lt_of_lt_mul (h4s_eq ▸ hvlt)
        have hv_eq : uL + uR * 2 ^ s = v.val := lo_hi_add s v.val
        by_cases hhalf : uR = 0 ∨ uL = 0
        · -- Stage 1/2
          have hlb := lowBit_spec s (by omega) hvlt
          have hxlt : v.val ^^^ 2 ^ lowBit s v.val < 4 ^ s := xor_two_pow_lt s hvlt hlb.1
          have h2lt : 2 ^ lowBit s v.val < 4 ^ s := two_pow_lt_four_pow s hlb.1
          obtain ⟨_, hp1, hp2⟩ := dag_s12 s hne0 hN hnp hhalf
          have hxne0 : v.val ^^^ 2 ^ lowBit s v.val ≠ 0 := by
            intro h0
            have hpop := popcnt_xor_bit s hlb.1 hlb.2
            have hge2 := popcnt_ge_two s (by omega) hvlt hnp
            have hp0 : popcnt s 0 = 0 := by unfold popcnt; simp
            rw [h0, hp0] at hpop; omega
          have h2ne0 : 2 ^ lowBit s v.val ≠ 0 := by positivity
          have hq_v : quadFun s ⟨v.val, hvlt⟩ = false := quadFun_eq_false_of_half_zero s hhalf
          have hq_2 : quadFun s ⟨2 ^ lowBit s v.val, h2lt⟩ = false := by
            by_cases hlt_s : lowBit s v.val < s
            · exact quadFun_eq_false_of_half_zero s (Or.inl (Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlt_s)))
            · exact quadFun_eq_false_of_half_zero s (Or.inr (Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))))
          have hq_1 : quadFun s ⟨v.val ^^^ 2 ^ lowBit s v.val, hxlt⟩ = false := by
            apply quadFun_eq_false_of_half_zero s
            rcases hhalf with hR0 | hL0
            · left
              have hlt2s : v.val < 2 ^ s := by rw [← hv_eq, hR0]; simp [huL_lt]
              have hlb_lt : lowBit s v.val < s := by
                by_contra hge
                rw [testBit_lo_zero s hR0 (by omega)] at hlb; cases hlb.2
              exact Nat.div_eq_of_lt (Nat.xor_lt_two_pow hlt2s (Nat.pow_lt_pow_right (by omega) hlb_lt))
            · right
              have hlb_ge : s ≤ lowBit s v.val := by
                by_contra hlt
                rw [testBit_hi_zero s hL0 (by omega)] at hlb; cases hlb.2
              apply Nat.eq_of_testBit_eq
              intro i
              rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
              by_cases hi : i < s
              · simp [hi, Nat.testBit_xor, testBit_hi_zero s hL0 hi, Nat.testBit_two_pow,
                  show lowBit s v.val ≠ i by omega]
              · simp [hi]
          rw [hp1, hp2]
          exact (specVal_xor_combine s hne0 hvlt hxne0 hxlt h2ne0 h2lt
            (fun j _ => by rw [Nat.testBit_xor]; cases v.val.testBit j <;> cases (2 ^ lowBit s v.val).testBit j <;> rfl)
            (by rw [hq_v, hq_1, hq_2]; rfl)).symm
        · have hneq_half : ¬(uR = 0 ∨ uL = 0) := hhalf
          have huR_ne0 : uR ≠ 0 := fun h => hhalf (Or.inl h)
          have huL_ne0 : uL ≠ 0 := fun h => hhalf (Or.inr h)
          by_cases hq : quadFun s ⟨v.val, hvlt⟩ = false
          · -- Stage 3
            obtain ⟨_, hp1, hp2⟩ := dag_s3 s hne0 hN hnp hneq_half hvlt hq
            have huL_lt4 : uL < 4 ^ s := by rw [h4s_eq]; exact lt_of_lt_of_le huL_lt (Nat.le_mul_of_pos_right _ h2s_pos)
            have huR_lt4 : uR * 2 ^ s < 4 ^ s := by rw [h4s_eq]; exact Nat.mul_lt_mul_of_pos_right huR_lt h2s_pos
            have hq1 : quadFun s ⟨uL, huL_lt4⟩ = false :=
              quadFun_eq_false_of_half_zero s (Or.inl (Nat.div_eq_of_lt huL_lt))
            have hq2 : quadFun s ⟨uR * 2 ^ s, huR_lt4⟩ = false :=
              quadFun_eq_false_of_half_zero s (Or.inr (Nat.mul_mod_left uR (2 ^ s)))
            rw [hp1, hp2]
            exact (specVal_xor_combine s hne0 hvlt huL_ne0 huL_lt4 (Nat.mul_ne_zero huR_ne0 (by omega)) huR_lt4
              (fun j _ => by
                rw [← hv_eq, testBit_lo_hi_add s huL_lt j, Nat.mul_comm uR (2 ^ s), Nat.testBit_two_pow_mul]
                by_cases hj : j < s
                · simp [hj, show ¬(s ≤ j) by omega]
                · have h0 : uL.testBit j = false :=
                    Nat.testBit_lt_two_pow (lt_of_lt_of_le huL_lt (Nat.pow_le_pow_right (by omega) (by omega)))
                  simp [hj, show s ≤ j by omega, h0])
              (by rw [hq, hq1, hq2]; rfl)).symm
          · have hqT : quadFun s ⟨v.val, hvlt⟩ = true := Bool.eq_true_of_not_eq_false hq
            by_cases huL1m : uL % 2 = 1
            · by_cases huR1 : uR = 1
              · by_cases huL1 : uL = 1
                · -- Stage 4: v = 1 + 2^s
                  have hveq12 : v.val = 1 + 2 ^ s := by rw [← hv_eq, huL1, huR1, Nat.one_mul]
                  obtain ⟨_, hp1, hp2⟩ := dag_s4 s hne0 hN hnp hneq_half hvlt hqT huL1 huR1
                  rw [hp1, hp2]
                  have h2s_lt4 : 2 ^ s < 4 ^ s := two_pow_lt_four_pow s (by omega)
                  have hvN : (mkV s (4 ^ s)).val = 4 ^ s := mkV_val s (by omega)
                  have hv2s : (mkV s (2 ^ s)).val = 2 ^ s := mkV_val s (by omega)
                  have hq2s : quadFun s ⟨2 ^ s, h2s_lt4⟩ = false :=
                    quadFun_eq_false_of_half_zero s (Or.inr (Nat.mod_self _))
                  let z0 : Fin (2 * s) := ⟨0, by omega⟩
                  let zs : Fin (2 * s) := ⟨s, by omega⟩
                  have hsum2s : xorSum (Finset.univ : Finset (Fin (2 * s)))
                      (fun j => (2 ^ s).testBit j.val && a (mkV s (2 ^ j.val))) = a (mkV s (2 ^ s)) := by
                    have hfn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * s))),
                        ((2 ^ s).testBit j.val && a (mkV s (2 ^ j.val))) =
                        (decide (j = zs) && a (mkV s (2 ^ j.val))) := by
                      intro j _
                      rw [Nat.testBit_two_pow]
                      by_cases hj : j = zs
                      · rw [hj]; simp [zs]
                      · have hjv : j.val ≠ s := fun h => hj (Fin.ext h)
                        simp [hj, Ne.symm hjv]
                    rw [xorSum_congr rfl hfn, xorSum_eq_ite]; simp [zs]
                  have hsum12 : xorSum (Finset.univ : Finset (Fin (2 * s)))
                      (fun j => v.val.testBit j.val && a (mkV s (2 ^ j.val))) =
                      xor (a (mkV s 1)) (a (mkV s (2 ^ s))) := by
                    have hfn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * s))),
                        (v.val.testBit j.val && a (mkV s (2 ^ j.val))) =
                        xor (decide (j = z0) && a (mkV s (2 ^ j.val)))
                            (decide (j = zs) && a (mkV s (2 ^ j.val))) := by
                      intro j _
                      rw [hveq12, show (1 : ℕ) + 2 ^ s = 1 + 1 * 2 ^ s by ring,
                        testBit_lo_hi_add s h2s_gt1 j.val]
                      have hz0s : z0 ≠ zs := by intro h; have := congrArg Fin.val h; dsimp only [z0, zs] at this; omega
                      by_cases hj0 : j = z0
                      · rw [hj0]; simp [z0, show 0 < s by omega, hz0s]
                      · by_cases hjs : j = zs
                        · rw [hjs]; simp [zs, show ¬(s < s) by omega, hz0s.symm]
                        · have hj0v : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
                          have hjsv : j.val ≠ s := fun h => hjs (Fin.ext h)
                          simp only [hj0, decide_false, Bool.false_and, hjs, Bool.xor_false]
                          split_ifs with hlt
                          · have : (1 : ℕ).testBit j.val = false :=
                              Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ j.val)))
                            simp [this]
                          · have : (1 : ℕ).testBit (j.val - s) = false :=
                              Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ j.val - s)))
                            simp [this]
                    rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite, xorSum_eq_ite]
                    simp [z0, zs]
                  unfold specVal
                  simp only [hne0, ↓reduceIte, hvlt, ↓reduceDIte, hsum12, hqT, Bool.true_and,
                    hvN, show 4 ^ s ≠ 0 by positivity, lt_irrefl, hv2s, show 2 ^ s ≠ 0 by positivity,
                    h2s_lt4, hsum2s, hq2s, Bool.false_and, Bool.xor_false]
                  cases a (mkV s 1) <;> cases a (mkV s (2 ^ s)) <;> cases a ⟨0, by positivity⟩ <;> rfl
                · -- Stage 5: uL % 2 = 1, uL ≠ 1, uR = 1
                  obtain ⟨_, hp1, hp2⟩ := dag_s5 s hne0 hN hnp hneq_half hvlt hqT huL1m huR1 huL1
                  have h12_lt : 1 + 2 ^ s < 4 ^ s := by
                    rw [h4s_eq]; have : 2 * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ (by omega); omega
                  have hx_lt2s : uL ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huL_lt h2s_gt1
                  have hx_lt4 : uL ^^^ 1 < 4 ^ s := by rw [h4s_eq]; exact lt_of_lt_of_le hx_lt2s (Nat.le_mul_of_pos_right _ h2s_pos)
                  have hx_ne0 : uL ^^^ 1 ≠ 0 := by
                    intro h0; exact huL1 (eq_of_xor_eq_zero h0)
                  have hq12 : quadFun s ⟨1 + 2 ^ s, h12_lt⟩ = true := by
                    have h := quadFun_lo_hi s (a := 1) (b := 1) h2s_gt1 h2s_gt1
                    simp only [Nat.one_mul] at h
                    rw [h]
                    have hfilt : (Finset.univ : Finset (Fin s)).filter
                        (fun i => (1 : ℕ).testBit i.val && (1 : ℕ).testBit i.val) = {⟨0, by omega⟩} := by
                      ext i
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
                      cases hi : i.val with
                      | zero => simp
                      | succ k =>
                        have : (1 : ℕ).testBit (k + 1) = false :=
                          Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.succ_pos k)))
                        simp [this]
                    unfold xorSum; rw [hfilt]; simp
                  have hqx : quadFun s ⟨uL ^^^ 1, hx_lt4⟩ = false :=
                    quadFun_eq_false_of_half_zero s (Or.inl (Nat.div_eq_of_lt hx_lt2s))
                  rw [hp1, hp2]
                  exact (specVal_xor_combine s hne0 hvlt (by omega) h12_lt hx_ne0 hx_lt4
                    (fun j _ => by
                      rw [← hv_eq, huR1, Nat.one_mul, show (1 : ℕ) + 2 ^ s = 1 + 1 * 2 ^ s by ring,
                        show uL + 2 ^ s = uL + 1 * 2 ^ s by ring,
                        testBit_lo_hi_add s huL_lt j, testBit_lo_hi_add s h2s_gt1 j]
                      by_cases hj : j < s
                      · simp only [hj, ↓reduceIte, Nat.testBit_xor]
                        cases uL.testBit j <;> cases (1 : ℕ).testBit j <;> rfl
                      · have h0 : (uL ^^^ 1).testBit j = false :=
                          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx_lt2s (Nat.pow_le_pow_right (by omega) (by omega)))
                        simp [hj, h0])
                    (by rw [hqT, hq12, hqx]; rfl)).symm
              · -- Stage 6: uL % 2 = 1, uR ≠ 1, q = true
                obtain ⟨_, hp1, hp2⟩ := dag_s6 s hne0 hN hnp hneq_half hvlt hqT huL1m huR1
                have hu1_lt4 : uL + 2 ^ s < 4 ^ s := by
                  rw [h4s_eq]; have : 2 * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ (by omega); omega
                have huRx_lt : uR ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huR_lt h2s_gt1
                have huRx_lt4 : (uR ^^^ 1) * 2 ^ s < 4 ^ s := by
                  rw [h4s_eq]; exact Nat.mul_lt_mul_of_pos_right huRx_lt h2s_pos
                have huRx_ne0 : (uR ^^^ 1) * 2 ^ s ≠ 0 :=
                  Nat.mul_ne_zero (fun h0 => huR1 (eq_of_xor_eq_zero h0)) (by omega)
                have hq1 : quadFun s ⟨uL + 2 ^ s, hu1_lt4⟩ = true := by
                  have h := quadFun_lo_hi s (a := uL) (b := 1) huL_lt h2s_gt1
                  simp only [Nat.one_mul] at h
                  rw [h]
                  have huL0 : uL.testBit 0 = true := by rw [mod_two_of_testBit0]; simp [huL1m]
                  have hfilt : (Finset.univ : Finset (Fin s)).filter
                      (fun i => uL.testBit i.val && (1 : ℕ).testBit i.val) = {⟨0, by omega⟩} := by
                    ext i
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
                    cases hi : i.val with
                    | zero => simp [huL0]
                    | succ k =>
                      have : (1 : ℕ).testBit (k + 1) = false :=
                        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.succ_pos k)))
                      simp [this]
                  unfold xorSum; rw [hfilt]; simp
                have hq2 : quadFun s ⟨(uR ^^^ 1) * 2 ^ s, huRx_lt4⟩ = false :=
                  quadFun_eq_false_of_half_zero s (Or.inr (Nat.mul_mod_left _ _))
                rw [hp1, hp2]
                exact (specVal_xor_combine s hne0 hvlt (by omega) hu1_lt4 huRx_ne0 huRx_lt4
                  (fun j _ => by
                    rw [← hv_eq, show uL + 2 ^ s = uL + 1 * 2 ^ s by ring,
                      testBit_lo_hi_add s huL_lt j, testBit_lo_hi_add s huL_lt j,
                      Nat.mul_comm (uR ^^^ 1) (2 ^ s), Nat.testBit_two_pow_mul]
                    by_cases hj : j < s
                    · simp [hj, show ¬(s ≤ j) by omega]
                    · simp only [hj, ↓reduceIte, show s ≤ j by omega, decide_true, Bool.true_and,
                        Nat.testBit_xor]
                      cases uR.testBit (j - s) <;> cases (1 : ℕ).testBit (j - s) <;> rfl)
                  (by rw [hqT, hq1, hq2]; rfl)).symm
            · by_cases huR2 : uR % 2 = 0
              · -- Stage 7: uL % 2 = 0, uR % 2 = 0, q = true
                obtain ⟨_, hp1, hp2⟩ := dag_s7 s hne0 hN hnp hneq_half hvlt hqT huL1m huR2
                have huLx_lt : uL ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huL_lt h2s_gt1
                have hu1_lt4 : (uL ^^^ 1) + uR * 2 ^ s < 4 ^ s := by
                  rw [h4s_eq]
                  have h1 : (uR + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ huR_lt
                  rw [Nat.add_mul, Nat.one_mul] at h1; omega
                have h1lt4 : 1 < 4 ^ s := by have := Nat.pow_le_pow_right (by omega : 1 ≤ 4) hs; omega
                have hu1_ne0 : (uL ^^^ 1) + uR * 2 ^ s ≠ 0 := by
                  have : 0 < uR * 2 ^ s := Nat.mul_pos (Nat.pos_of_ne_zero huR_ne0) h2s_pos; omega
                have hq1 : quadFun s ⟨(uL ^^^ 1) + uR * 2 ^ s, hu1_lt4⟩ = true := by
                  rw [quadFun_xor_one_lo s hs huL_lt huR_lt, mod_two_of_testBit0]
                  have hv_fin : (⟨uL + uR * 2 ^ s, by
                      rw [h4s_eq]; have h1 : (uR + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ huR_lt
                      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ : Fin (4 ^ s)) = ⟨v.val, hvlt⟩ :=
                    Fin.ext hv_eq
                  rw [hv_fin, hqT]; simp [huR2]
                have hq2 : quadFun s ⟨1, h1lt4⟩ = false :=
                  quadFun_eq_false_of_half_zero s (Or.inl (Nat.div_eq_of_lt h2s_gt1))
                rw [hp1, hp2]
                exact (specVal_xor_combine s hne0 hvlt hu1_ne0 hu1_lt4 (by omega) h1lt4
                  (fun j _ => by
                    rw [← hv_eq, testBit_lo_hi_add s huL_lt j, testBit_lo_hi_add s huLx_lt j]
                    by_cases hj : j < s
                    · simp only [hj, ↓reduceIte, Nat.testBit_xor]
                      cases uL.testBit j <;> cases (1 : ℕ).testBit j <;> rfl
                    · have h10 : (1 : ℕ).testBit j = false :=
                        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ j)))
                      simp [hj, h10])
                  (by rw [hqT, hq1, hq2]; rfl)).symm
              · -- Stage 8: uL % 2 = 0, uR % 2 = 1, q = true
                obtain ⟨_, hp1, hp2⟩ := dag_s8 s hne0 hN hnp hneq_half hvlt hqT huL1m huR2
                have huRx_lt : uR ^^^ 1 < 2 ^ s := Nat.xor_lt_two_pow huR_lt h2s_gt1
                have hu1_lt4 : uL + (uR ^^^ 1) * 2 ^ s < 4 ^ s := by
                  rw [h4s_eq]
                  have h1 : ((uR ^^^ 1) + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ huRx_lt
                  rw [Nat.add_mul, Nat.one_mul] at h1; omega
                have h2s_lt4 : 2 ^ s < 4 ^ s := two_pow_lt_four_pow s (by omega)
                have hu1_ne0 : uL + (uR ^^^ 1) * 2 ^ s ≠ 0 := by omega
                have hq1 : quadFun s ⟨uL + (uR ^^^ 1) * 2 ^ s, hu1_lt4⟩ = true := by
                  rw [quadFun_xor_one_hi s hs huL_lt huR_lt, mod_two_of_testBit0]
                  have hv_fin : (⟨uL + uR * 2 ^ s, by
                      rw [h4s_eq]; have h1 : (uR + 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ huR_lt
                      rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩ : Fin (4 ^ s)) = ⟨v.val, hvlt⟩ :=
                    Fin.ext hv_eq
                  rw [hv_fin, hqT]; simp [huL1m]
                have hq2 : quadFun s ⟨2 ^ s, h2s_lt4⟩ = false :=
                  quadFun_eq_false_of_half_zero s (Or.inr (Nat.mod_self _))
                rw [hp1, hp2]
                exact (specVal_xor_combine s hne0 hvlt hu1_ne0 hu1_lt4 (by omega) h2s_lt4
                  (fun j _ => by
                    rw [← hv_eq, testBit_lo_hi_add s huL_lt j, testBit_lo_hi_add s huL_lt j,
                      Nat.testBit_two_pow]
                    by_cases hj : j < s
                    · simp [hj, show s ≠ j by omega]
                    · simp only [hj, ↓reduceIte, Nat.testBit_xor]
                      have h1bit : (1 : ℕ).testBit (j - s) = decide (s = j) := by
                        by_cases hjs : s = j
                        · subst hjs; simp
                        · have hge : 1 ≤ j - s := by omega
                          have : (1 : ℕ).testBit (j - s) = false :=
                            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hge))
                          simp [hjs, this]
                      rw [h1bit]
                      cases uR.testBit (j - s) <;> cases decide (s = j) <;> rfl)
                  (by rw [hqT, hq1, hq2]; rfl)).symm
    · -- Base case: dagRk s v = 0, so v = 0 or v = 2^j
      have h0 : dagRk s v = 0 := by omega
      rw [fwdEval_zero (dagRk s) (dagP1 s) (dagP2 s) a v h0]
      rcases (dagRk_zero_iff s hs v).mp h0 with hv0 | hp
      · unfold specVal; simp only [hv0, ↓reduceIte]; congr 1; exact Fin.ext hv0
      · obtain ⟨j0, hj0, hveq⟩ := (isPow2_iff s).mp hp
        have hvne0 : v.val ≠ 0 := by rw [hveq]; positivity
        have hvlt : v.val < 4 ^ s := by
          rw [hveq, four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) hj0
        have hqv : quadFun s ⟨v.val, hvlt⟩ = false := by
          by_cases hlt_s : j0 < s
          · exact quadFun_eq_false_of_half_zero s (Or.inl (by rw [hveq]; exact Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) hlt_s)))
          · exact quadFun_eq_false_of_half_zero s (Or.inr (by rw [hveq]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))))
        unfold specVal
        simp only [hvne0, ↓reduceIte, hvlt, ↓reduceDIte, hqv, Bool.false_and, Bool.xor_false]
        have hfn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * s))),
            (v.val.testBit j.val && a (mkV s (2 ^ j.val))) =
            (decide (j = ⟨j0, hj0⟩) && a (mkV s (2 ^ j.val))) := by
          intro j _
          rw [hveq, Nat.testBit_two_pow]
          by_cases h : j.val = j0
          · have hj : j = ⟨j0, hj0⟩ := Fin.ext h; subst hj; simp
          · have hne : j ≠ ⟨j0, hj0⟩ := fun he => h (congrArg Fin.val he)
            simp [hne, Ne.symm h]
        rw [xorSum_congr rfl hfn, xorSum_eq_ite]
        simp only [Finset.mem_univ, ↓reduceIte]
        congr 1
        apply Fin.ext
        rw [mkV_val s (by omega), hveq]

end QuadDAG


section UpperConstruction

variable (s : ℕ)

def pairPrefix : ℕ → List Gate
  | 0 => []
  | m + 1 =>
    let gs := pairPrefix m
    gs ++ xorGates (4 ^ s + 4 ^ s + gs.length) (m + 1) (4 ^ s + swapH s (m + 1))

lemma pairPrefix_spec (m : ℕ) (hm : m < 4 ^ s) :
    WellFormed (4 ^ s + 4 ^ s) (pairPrefix s m) ∧
    (pairPrefix s m).length = 2 * m ∧
    (pairPrefix s m).countP isBinGate = m ∧
    (pairPrefix s m).countP isNLGate = 0 ∧
    (∀ (x y : Fin (4 ^ s)) (u : ℕ), 1 ≤ u → u ≤ m →
      ((pairPrefix s m).foldl stepWires (oneEach x y)).getD (4 ^ s + 4 ^ s + 2 * (u - 1) + 1) false =
        xor (decide (u = x.val)) (decide (u = swapH s y.val))) := by
  induction m with
  | zero =>
    refine ⟨wellFormed_nil _, rfl, rfl, rfl, ?_⟩
    intro _ _ u h1 h0; omega
  | succ m ih =>
    obtain ⟨hwf, hlen, hB, hT, heval⟩ := ih (by omega)
    have ha : m + 1 < 4 ^ s + 4 ^ s + (pairPrefix s m).length := by omega
    have hsw_lt : swapH s (m + 1) < 4 ^ s := swapH_lt s (m + 1) hm
    have hb : 4 ^ s + swapH s (m + 1) < 4 ^ s + 4 ^ s + (pairPrefix s m).length := by omega
    refine ⟨wellFormed_append_xor hwf ha hb, ?_, ?_, ?_, ?_⟩
    · simp [pairPrefix, xorGates, hlen]; omega
    · unfold pairPrefix; rw [List.countP_append, hB, xorGates_countB]
    · unfold pairPrefix; rw [List.countP_append, hT, xorGates_countT]
    · intro x y u hu1 hum
      have hxlen : (oneEach x y).length = 4 ^ s + 4 ^ s := by simp [oneEach]
      have hstep := foldl_append_xor_eval (pairPrefix s m) (m + 1) (4 ^ s + swapH s (m + 1))
        (oneEach x y) hxlen ha hb
      by_cases hlt : u ≤ m
      · have hwlt : 4 ^ s + 4 ^ s + 2 * (u - 1) + 1 < 4 ^ s + 4 ^ s + (pairPrefix s m).length := by omega
        unfold pairPrefix
        rw [hstep.1 _ hwlt, heval x y u hu1 hlt]
      · have heq : u = m + 1 := by omega
        subst heq
        unfold pairPrefix
        have hidx : 4 ^ s + 4 ^ s + 2 * (m + 1 - 1) + 1 =
            4 ^ s + 4 ^ s + (pairPrefix s m).length + 1 := by omega
        rw [hidx, hstep.2]
        have hleft : ((pairPrefix s m).foldl stepWires (oneEach x y)).getD (m + 1) false =
            decide (m + 1 = x.val) := by
          rw [foldl_stepWires_getD_lt _ _ _ (by rw [hxlen]; omega)]
          unfold oneEach
          have hi : m + 1 < (List.ofFn (fun k : Fin (4 ^ s) => decide (k = x))).length := by simp; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_ofFn]
          simp only [hm, ↓reduceDIte, Option.getD_some]
          by_cases h : m + 1 = x.val
          · have hfin : (⟨m + 1, hm⟩ : Fin (4 ^ s)) = x := Fin.ext h
            simp [h, hfin]
          · have hfin : (⟨m + 1, hm⟩ : Fin (4 ^ s)) ≠ x := fun he => h (congrArg Fin.val he)
            simp [h, hfin]
        have hright : ((pairPrefix s m).foldl stepWires (oneEach x y)).getD (4 ^ s + swapH s (m + 1)) false =
            decide (m + 1 = swapH s y.val) := by
          rw [foldl_stepWires_getD_lt _ _ _ (by rw [hxlen]; omega)]
          unfold oneEach
          have hlenL : (List.ofFn (fun k : Fin (4 ^ s) => decide (k = x))).length = 4 ^ s := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenL,
            Nat.add_sub_cancel_left, List.getElem?_ofFn]
          simp only [hsw_lt, ↓reduceDIte, Option.getD_some]
          have hiff : (⟨swapH s (m + 1), hsw_lt⟩ = y) ↔ (m + 1 = swapH s y.val) := by
            constructor
            · intro h; have hv := congrArg Fin.val h; dsimp only at hv
              rw [← hv, swapH_invol s (m + 1) hm]
            · intro h; apply Fin.ext; dsimp only; rw [h, swapH_invol s y.val y.isLt]
          by_cases h : m + 1 = swapH s y.val
          · rw [hiff.mpr h]; simp [h]
          · simp [h, mt hiff.mp h]
        rw [hleft, hright]

def initAdj (v : Fin (4 ^ s + 1)) : Option ℕ :=
  if 1 ≤ v.val ∧ v.val < 4 ^ s then some (4 ^ s + 4 ^ s + 2 * (v.val - 1) + 1)
  else none

lemma someCount_initAdj (hs : 1 ≤ s) : someCount (initAdj s) = 4 ^ s - 1 := by
  unfold someCount
  have hfilt : (Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => (initAdj s v).isSome = true) =
      ((Finset.univ : Finset (Fin (4 ^ s + 1))).erase ⟨0, by positivity⟩).erase ⟨4 ^ s, by omega⟩ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff, and_true]
    unfold initAdj
    by_cases h1 : 1 ≤ v.val ∧ v.val < 4 ^ s
    · rw [ite_eq_left_iff.mpr (fun h => absurd h1 h)]
      exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => rfl⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h1)]
      constructor
      · intro h; cases h
      · rintro ⟨hneN, hne0⟩; exact absurd ⟨by omega, by omega⟩ h1
  rw [hfilt, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨by
    intro h; have := congrArg Fin.val h; dsimp only at this; have := Nat.one_le_pow s 4 (by omega); omega,
    Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

def prodSum (gs0 : List Gate) (L : ℕ → ℕ) : ℕ → List Gate × ℕ
  | 0 => (gs0, 0)
  | 1 =>
    let w0 := 4 ^ s + 4 ^ s + gs0.length
    (gs0 ++ [⟨GateOp.and, [L 0, L s]⟩], w0)
  | k + 2 =>
    let (gs1, acc) := prodSum gs0 L (k + 1)
    let pW := 4 ^ s + 4 ^ s + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [L (k + 1), L (s + (k + 1))]⟩]
    let sumW := 4 ^ s + 4 ^ s + gs2.length + 1
    (gs2 ++ xorGates (4 ^ s + 4 ^ s + gs2.length) acc pW, sumW)

lemma prodSum_spec (hs : 1 ≤ s) (gs0 : List Gate) (L : ℕ → ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hms : m ≤ s)
    (hwf0 : WellFormed (4 ^ s + 4 ^ s) gs0)
    (hLlt : ∀ j < 2 * s, L j < 4 ^ s + 4 ^ s + gs0.length) :
    let res := prodSum s gs0 L m
    WellFormed (4 ^ s + 4 ^ s) res.1 ∧
    res.2 < 4 ^ s + 4 ^ s + res.1.length ∧
    gs0.length ≤ res.1.length ∧
    res.1.countP isBinGate = gs0.countP isBinGate + (2 * m - 1) ∧
    res.1.countP isNLGate = gs0.countP isNLGate + m ∧
    (∀ x, x.length = 4 ^ s + 4 ^ s →
      (∀ w < 4 ^ s + 4 ^ s + gs0.length,
        (res.1.foldl stepWires x).getD w false = (gs0.foldl stepWires x).getD w false) ∧
      (res.1.foldl stepWires x).getD res.2 false =
        xorSum (Finset.range m) (fun i =>
          (gs0.foldl stepWires x).getD (L i) false &&
          (gs0.foldl stepWires x).getD (L (s + i)) false)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      unfold prodSum
      have hL0 : L 0 < 4 ^ s + 4 ^ s + gs0.length := hLlt 0 (by omega)
      have hLs : L s < 4 ^ s + 4 ^ s + gs0.length := hLlt s (by omega)
      have hwf1 : WellFormed (4 ^ s + 4 ^ s) (gs0 ++ [⟨GateOp.and, [L 0, L s]⟩]) :=
        wellFormed_append_gate hwf0 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
      refine ⟨hwf1, by simp, by simp, ?_, ?_, ?_⟩
      · rw [List.countP_append, andGate_countB]
      · rw [List.countP_append, andGate_countT]
      · intro x hx
        have hev := foldl_append_and_eval gs0 (L 0) (L s) x hx
        refine ⟨hev.1, ?_⟩
        rw [hev.2]
        have hr1 : Finset.range 1 = {0} := by ext a; simp
        rw [hr1]
        change _ = xorSum (insert 0 ∅) _
        rw [xorSum_insert (Finset.notMem_empty 0), xorSum_empty, Bool.xor_false, Nat.add_zero]
    | succ k =>
      obtain ⟨hwf1, hacc_lt, hlen1, hB1, hT1, hev1⟩ := ih (by omega) (by omega)
      unfold prodSum
      set gs1 := (prodSum s gs0 L (k + 1)).1
      set acc := (prodSum s gs0 L (k + 1)).2
      have hLa : L (k + 1) < 4 ^ s + 4 ^ s + gs1.length := by have := hLlt (k + 1) (by omega); omega
      have hLb : L (s + (k + 1)) < 4 ^ s + 4 ^ s + gs1.length := by have := hLlt (s + (k + 1)) (by omega); omega
      set gs2 := gs1 ++ [⟨GateOp.and, [L (k + 1), L (s + (k + 1))]⟩]
      have hwf2 : WellFormed (4 ^ s + 4 ^ s) gs2 :=
        wellFormed_append_gate hwf1 (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
      have hlen2 : gs2.length = gs1.length + 1 := by simp [gs2]
      have hacc_lt2 : acc < 4 ^ s + 4 ^ s + gs2.length := by omega
      have hpW_lt2 : 4 ^ s + 4 ^ s + gs1.length < 4 ^ s + 4 ^ s + gs2.length := by omega
      have hwf3 := wellFormed_append_xor hwf2 hacc_lt2 hpW_lt2
      refine ⟨hwf3, by simp [xorGates, hlen2]; omega, by simp [xorGates, hlen2]; omega, ?_, ?_, ?_⟩
      · rw [List.countP_append, xorGates_countB, List.countP_append, andGate_countB, hB1]; omega
      · rw [List.countP_append, xorGates_countT, List.countP_append, andGate_countT, hT1]; omega
      · intro x hx
        have hev2 := foldl_append_and_eval gs1 (L (k + 1)) (L (s + (k + 1))) x hx
        have hev3 := foldl_append_xor_eval gs2 acc (4 ^ s + 4 ^ s + gs1.length) x hx hacc_lt2 hpW_lt2
        constructor
        · intro w hw
          rw [hev3.1 w (by omega), hev2.1 w (by omega), (hev1 x hx).1 w hw]
        · rw [hev3.2, hev2.1 acc hacc_lt, hev2.2, (hev1 x hx).2,
            (hev1 x hx).1 (L (k + 1)) (hLlt (k + 1) (by omega)),
            (hev1 x hx).1 (L (s + (k + 1))) (hLlt (s + (k + 1)) (by omega))]
          conv_rhs => rw [Finset.range_add_one]
          rw [xorSum_insert (by simp), Bool.xor_comm]

lemma upper_bounds_exist (hs : 1 ≤ s) :
    (∃ C : Circuit,
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
      ReadsBack (4 ^ s + 4 ^ s) C ∧
      Represents (signedFun s) C ∧
      tCount C = s ∧ bCount C + 2 * s + 4 ≤ 3 * 4 ^ s) ∧
    (∃ C : Circuit,
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
      ReadsBack (4 ^ s + 4 ^ s) C ∧
      Represents (dotFun s) C ∧
      tCount C = s ∧ bCount C + 2 * s + 3 ≤ 3 * 4 ^ s) := by
  have hNpos : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by omega)
  have hpair := pairPrefix_spec s (4 ^ s - 1) (by omega)
  set gs0 := pairPrefix s (4 ^ s - 1)
  have hadj0 : ∀ z r, initAdj s z = some r → r < 4 ^ s + 4 ^ s + gs0.length := by
    intro z r hz
    unfold initAdj at hz
    by_cases h1 : 1 ≤ z.val ∧ z.val < 4 ^ s
    · rw [if_pos h1] at hz; cases hz; omega
    · rw [if_neg h1] at hz; cases hz
  set L := gateOrder (dagRk s) (s + 5)
  have hL_pos : ∀ u ∈ L, 0 < dagRk s u := fun u hu => (mem_gateOrder (dagRk s) (dagRk_le s) u).mp hu
  have hL_nodup : L.Nodup := gateOrder_nodup (dagRk s) (s + 5)
  have hL_ord : L.Pairwise (fun u v => dagRk s v ≤ dagRk s u) := gateOrder_pairwise (dagRk s) (s + 5)
  have hL_len : L.length = 4 ^ s - 2 * s := by
    rw [gateOrder_length (dagRk s) (dagRk_le s), dagRk_pos_card s hs]
  have htrans := foldl_gateStep_spec (dagRk s) (dagP1 s) (dagP2 s) (4 ^ s + 4 ^ s)
    (dag_acyclic s hs) L hL_pos hL_nodup hL_ord gs0 (initAdj s) hpair.1 hadj0
  set gsE := (L.foldl (gateStep (dagP1 s) (dagP2 s) (4 ^ s + 4 ^ s)) (gs0, initAdj s)).1
  set adjE := (L.foldl (gateStep (dagP1 s) (dagP2 s) (4 ^ s + 4 ^ s)) (gs0, initAdj s)).2
  have heval_input : ∀ (v0 : Fin (4 ^ s + 1)), dagRk s v0 = 0 → ∀ (x y : Fin (4 ^ s)),
      evalOpt gsE (oneEach x y) (adjE v0) =
      xorSum (Finset.univ : Finset (Fin (4 ^ s + 1))) (fun v =>
        specVal s (fun u => decide (u = v0)) v && evalOpt gs0 (oneEach x y) (initAdj s v)) := by
    intro v0 hv0 x y
    have hinv := htrans.2.2.2.2.2.2 (oneEach x y) (by simp [oneEach]) (fun u => decide (u = v0))
    have hLHS : xorSum (Finset.univ : Finset (Fin (4 ^ s + 1))) (fun v =>
          fwdEval (dagRk s) (dagP1 s) (dagP2 s) (fun u => decide (u = v0)) v &&
            evalOpt gsE (oneEach x y) (adjE v)) =
        evalOpt gsE (oneEach x y) (adjE v0) := by
      have hfn : ∀ v ∈ (Finset.univ : Finset (Fin (4 ^ s + 1))),
          (fwdEval (dagRk s) (dagP1 s) (dagP2 s) (fun u => decide (u = v0)) v &&
            evalOpt gsE (oneEach x y) (adjE v)) =
          (decide (v = v0) && evalOpt gsE (oneEach x y) (adjE v)) := by
        intro v _
        by_cases hrk0 : dagRk s v = 0
        · rw [fwdEval_zero _ _ _ _ v hrk0]
        · have hvL : v ∈ L := (mem_gateOrder (dagRk s) (dagRk_le s) v).mpr (by omega)
          have hnone : adjE v = none := htrans.2.2.2.2.1 v hvL
          simp [hnone, evalOpt]
      rw [xorSum_congr rfl hfn, xorSum_eq_ite]
      simp
    rw [← hLHS, hinv]
    apply xorSum_congr rfl
    intro v _
    rw [fwdEval_eq_specVal s hs]
  have heval_bit : ∀ (j : ℕ) (hj : j < 2 * s) (x y : Fin (4 ^ s)),
      evalOpt gsE (oneEach x y) (adjE (mkV s (2 ^ j))) =
        xor (x.val.testBit j) ((swapH s y.val).testBit j) := by
    intro j hj x y
    have h2j_lt : 2 ^ j < 4 ^ s := by rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) hj
    have hv0_rk : dagRk s (mkV s (2 ^ j)) = 0 := by
      rw [dagRk_zero_iff s hs]; right; rw [mkV_val s (by omega), isPow2_iff]; exact ⟨j, hj, rfl⟩
    rw [heval_input _ hv0_rk x y]
    have hfn : ∀ v ∈ (Finset.univ : Finset (Fin (4 ^ s + 1))),
        (specVal s (fun u => decide (u = mkV s (2 ^ j))) v && evalOpt gs0 (oneEach x y) (initAdj s v)) =
        if hv : 1 ≤ v.val ∧ v.val < 4 ^ s then
          v.val.testBit j && xor (decide (v.val = x.val)) (decide (v.val = swapH s y.val))
        else false := by
      intro v _
      by_cases hv : 1 ≤ v.val ∧ v.val < 4 ^ s
      · simp only [hv, ↓reduceDIte]
        have hinit : evalOpt gs0 (oneEach x y) (initAdj s v) =
            xor (decide (v.val = x.val)) (decide (v.val = swapH s y.val)) := by
          unfold initAdj evalOpt
          simp only [hv, ↓reduceIte]
          exact hpair.2.2.2.2 x y v.val hv.1 (by omega)
        rw [hinit]
        congr 1
        unfold specVal
        have h0ne : (⟨0, by positivity⟩ : Fin (4 ^ s + 1)) ≠ mkV s (2 ^ j) := by
          intro h; have := congrArg Fin.val h; dsimp only at this; rw [mkV_val s (by omega)] at this
          have := Nat.two_pow_pos j; omega
        simp only [show v.val ≠ 0 by omega, ↓reduceIte, hv.2, ↓reduceDIte, h0ne, decide_false,
          Bool.and_false, Bool.xor_false]
        have hsum : ∀ i ∈ (Finset.univ : Finset (Fin (2 * s))),
            (v.val.testBit i.val && decide (mkV s (2 ^ i.val) = mkV s (2 ^ j))) =
            (decide (i = ⟨j, hj⟩) && v.val.testBit i.val) := by
          intro i _
          have h2i_lt : 2 ^ i.val < 4 ^ s := by
            rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) i.isLt
          have hiff : (mkV s (2 ^ i.val) = mkV s (2 ^ j)) ↔ (i = ⟨j, hj⟩) := by
            constructor
            · intro h
              have := congrArg Fin.val h
              rw [mkV_val s (by omega), mkV_val s (by omega)] at this
              exact Fin.ext (Nat.pow_right_injective (by omega : 2 ≤ 2) this)
            · intro h; subst h; rfl
          by_cases h : i = ⟨j, hj⟩
          · subst h; simp
          · simp [h, mt hiff.mp h]
        rw [xorSum_congr rfl hsum, xorSum_eq_ite]; simp
      · simp only [hv, ↓reduceDIte, initAdj, ↓reduceIte, evalOpt, Bool.and_false]
    rw [xorSum_congr rfl hfn]
    have hsplit : ∀ v ∈ (Finset.univ : Finset (Fin (4 ^ s + 1))),
        (if hv : 1 ≤ v.val ∧ v.val < 4 ^ s then
          v.val.testBit j && xor (decide (v.val = x.val)) (decide (v.val = swapH s y.val))
        else false) =
        xor (decide (v = ⟨x.val, by omega⟩) && x.val.testBit j)
            (decide (v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩) &&
              (swapH s y.val).testBit j) := by
      intro v _
      by_cases hv : 1 ≤ v.val ∧ v.val < 4 ^ s
      · rw [dif_pos hv, Bool.and_xor_distrib_left]
        have h1 : (v.val.testBit j && decide (v.val = x.val)) =
            (decide (v = ⟨x.val, by omega⟩) && x.val.testBit j) := by
          by_cases hx : v.val = x.val
          · have : v = ⟨x.val, by omega⟩ := Fin.ext hx; simp [hx, this]
          · have : v ≠ ⟨x.val, by omega⟩ := fun h => hx (congrArg Fin.val h); simp [hx, this]
        have h2 : (v.val.testBit j && decide (v.val = swapH s y.val)) =
            (decide (v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩) &&
              (swapH s y.val).testBit j) := by
          by_cases hy : v.val = swapH s y.val
          · have : v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩ := Fin.ext hy
            simp [hy, this]
          · have : v ≠ ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩ :=
              fun h => hy (congrArg Fin.val h)
            simp [hy, this]
        rw [h1, h2]
      · simp only [hv, ↓reduceDIte]
        have hcase : v.val = 0 ∨ v.val = 4 ^ s := by omega
        rcases hcase with h0 | hN
        · have hx0 : (decide (v = ⟨x.val, by omega⟩) && x.val.testBit j) = false := by
            by_cases hx : v = ⟨x.val, by omega⟩
            · have : x.val = 0 := by have := congrArg Fin.val hx; dsimp only at this; omega
              simp [this]
            · simp [hx]
          have hy0 : (decide (v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩) &&
              (swapH s y.val).testBit j) = false := by
            by_cases hy : v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩
            · have : swapH s y.val = 0 := by have := congrArg Fin.val hy; dsimp only at this; omega
              simp [this]
            · simp [hy]
          rw [hx0, hy0]; rfl
        · have hne1 : v ≠ ⟨x.val, by omega⟩ := fun h => by
            have := congrArg Fin.val h; dsimp only at this; have := x.isLt; omega
          have hne2 : v ≠ ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩ := fun h => by
            have := congrArg Fin.val h; dsimp only at this; have := swapH_lt s y.val y.isLt; omega
          simp [hne1, hne2]
    rw [xorSum_congr rfl hsplit, xorSum_xor, xorSum_eq_ite, xorSum_eq_ite]
    simp
  have heval_quad : ∀ (x y : Fin (4 ^ s)),
      evalOpt gsE (oneEach x y) (adjE ⟨0, by positivity⟩) =
        xor (quadFun s x) (quadFun s y) := by
    intro x y
    have hv0_rk : dagRk s ⟨0, by positivity⟩ = 0 := by rw [dagRk_zero_iff s hs]; left; rfl
    rw [heval_input _ hv0_rk x y]
    have hfn : ∀ v ∈ (Finset.univ : Finset (Fin (4 ^ s + 1))),
        (specVal s (fun u => decide (u = ⟨0, by positivity⟩)) v && evalOpt gs0 (oneEach x y) (initAdj s v)) =
        xor (decide (v = ⟨x.val, by omega⟩) && quadFun s x)
            (decide (v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩) &&
              quadFun s ⟨swapH s y.val, swapH_lt s y.val y.isLt⟩) := by
      intro v _
      by_cases hv : 1 ≤ v.val ∧ v.val < 4 ^ s
      · have hinit : evalOpt gs0 (oneEach x y) (initAdj s v) =
            xor (decide (v.val = x.val)) (decide (v.val = swapH s y.val)) := by
          unfold initAdj evalOpt; simp only [hv, ↓reduceIte]
          exact hpair.2.2.2.2 x y v.val hv.1 (by omega)
        have hsp : specVal s (fun u => decide (u = ⟨0, by positivity⟩)) v =
            quadFun s ⟨v.val, hv.2⟩ := by
          unfold specVal
          simp only [show v.val ≠ 0 by omega, ↓reduceIte, hv.2, ↓reduceDIte]
          have hsum0 : xorSum (Finset.univ : Finset (Fin (2 * s))) (fun j =>
              v.val.testBit j.val && decide (mkV s (2 ^ j.val) = ⟨0, by positivity⟩)) = false := by
            rw [xorSum_congr rfl (g := fun _ => false) (fun j _ => by
              have h2j : 2 ^ j.val < 4 ^ s := by
                rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) j.isLt
              have hne : mkV s (2 ^ j.val) ≠ ⟨0, by positivity⟩ := by
                intro h; have := congrArg Fin.val h; dsimp only at this; rw [mkV_val s (by omega)] at this
                have := Nat.two_pow_pos j.val; omega
              rw [decide_eq_false hne, Bool.and_false]), xorSum_false]
          rw [hsum0, Bool.false_xor]
          simp
        rw [hsp, hinit, Bool.and_xor_distrib_left]
        have h1 : (quadFun s ⟨v.val, hv.2⟩ && decide (v.val = x.val)) =
            (decide (v = ⟨x.val, by omega⟩) && quadFun s x) := by
          by_cases hx : v.val = x.val
          · have hvx : v = ⟨x.val, by omega⟩ := Fin.ext hx
            have hfin : (⟨v.val, hv.2⟩ : Fin (4 ^ s)) = x := Fin.ext hx
            simp [hx, hvx, hfin]
          · have hvx : v ≠ ⟨x.val, by omega⟩ := fun h => hx (congrArg Fin.val h)
            simp [hx, hvx]
        have h2 : (quadFun s ⟨v.val, hv.2⟩ && decide (v.val = swapH s y.val)) =
            (decide (v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩) &&
              quadFun s ⟨swapH s y.val, swapH_lt s y.val y.isLt⟩) := by
          by_cases hy : v.val = swapH s y.val
          · have hvy : v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩ := Fin.ext hy
            have hfin : (⟨v.val, hv.2⟩ : Fin (4 ^ s)) = ⟨swapH s y.val, swapH_lt s y.val y.isLt⟩ :=
              Fin.ext hy
            simp [hy, hvy, hfin]
          · have hvy : v ≠ ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩ :=
              fun h => hy (congrArg Fin.val h)
            simp [hy, hvy]
        rw [h1, h2]
      · have hinitF : evalOpt gs0 (oneEach x y) (initAdj s v) = false := by
          unfold initAdj evalOpt; simp [hv]
        rw [hinitF, Bool.and_false]
        have hcase : v.val = 0 ∨ v.val = 4 ^ s := by omega
        rcases hcase with h0 | hN
        · have hx0 : (decide (v = ⟨x.val, by omega⟩) && quadFun s x) = false := by
            by_cases hx : v = ⟨x.val, by omega⟩
            · have : x = ⟨0, by positivity⟩ := Fin.ext (by
                have := congrArg Fin.val hx; dsimp only at this; change x.val = 0; omega)
              rw [this, quadFun_eq_false_of_half_zero s (Or.inl (by simp))]; simp
            · simp [hx]
          have hy0 : (decide (v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩) &&
              quadFun s ⟨swapH s y.val, swapH_lt s y.val y.isLt⟩) = false := by
            by_cases hy : v = ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩
            · have : (⟨swapH s y.val, swapH_lt s y.val y.isLt⟩ : Fin (4 ^ s)) = ⟨0, by positivity⟩ :=
                Fin.ext (by have := congrArg Fin.val hy; dsimp only at this; change swapH s y.val = 0; omega)
              rw [this, quadFun_eq_false_of_half_zero s (Or.inl (by simp))]; simp
            · simp [hy]
          rw [hx0, hy0]; rfl
        · have hne1 : v ≠ ⟨x.val, by omega⟩ := fun h => by
            have := congrArg Fin.val h; dsimp only at this; have := x.isLt; omega
          have hne2 : v ≠ ⟨swapH s y.val, by have := swapH_lt s y.val y.isLt; omega⟩ := fun h => by
            have := congrArg Fin.val h; dsimp only at this; have := swapH_lt s y.val y.isLt; omega
          simp [hne1, hne2]
    rw [xorSum_congr rfl hfn, xorSum_xor, xorSum_eq_ite, xorSum_eq_ite]
    simp [quadFun_swapH s y]
  have hbit_some : ∀ j < 2 * s, (adjE (mkV s (2 ^ j))).isSome = true := by
    intro j hj
    have h2j_lt : 2 ^ j < 4 ^ s := by rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) hj
    have h1 := heval_bit j hj ⟨2 ^ j, h2j_lt⟩ ⟨0, by positivity⟩
    rw [swapH_zero, Nat.zero_testBit, Nat.testBit_two_pow_self, Bool.xor_false] at h1
    cases hopt : adjE (mkV s (2 ^ j)) with
    | none => simp [hopt, evalOpt] at h1
    | some _ => rfl
  have hquad_some : (adjE ⟨0, by positivity⟩).isSome = true := by
    have h12_lt : 1 + 2 ^ s < 4 ^ s := by
      rw [four_pow_eq_mul]
      have h2gt : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
      have : 2 * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ h2gt
      omega
    have h1 := heval_quad ⟨1 + 2 ^ s, h12_lt⟩ ⟨0, by positivity⟩
    have hq0 : quadFun s ⟨0, by positivity⟩ = false := quadFun_eq_false_of_half_zero s (Or.inl (by simp))
    have hq12 : quadFun s ⟨1 + 2 ^ s, h12_lt⟩ = true := by
      have h := quadFun_lo_hi s (a := 1) (b := 1) (Nat.one_lt_two_pow (by omega)) (Nat.one_lt_two_pow (by omega))
      simp only [Nat.one_mul] at h
      rw [h]
      have hfilt : (Finset.univ : Finset (Fin s)).filter
          (fun i => (1 : ℕ).testBit i.val && (1 : ℕ).testBit i.val) = {⟨0, by omega⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
        cases hi : i.val with
        | zero => simp
        | succ k =>
          have : (1 : ℕ).testBit (k + 1) = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.succ_pos k)))
          simp [this]
      unfold xorSum; rw [hfilt]; simp
    rw [hq12, hq0, Bool.xor_false] at h1
    cases hopt : adjE ⟨0, by positivity⟩ with
    | none =>
      rw [hopt] at h1
      simp [evalOpt] at h1
    | some _ => rfl
  have hsc_ge : 2 * s + 1 ≤ someCount adjE := by
    unfold someCount
    let inSet : Finset (Fin (4 ^ s + 1)) :=
      insert ⟨0, by positivity⟩
        ((Finset.univ : Finset (Fin (2 * s))).image (fun j : Fin (2 * s) => mkV s (2 ^ j.val)))
    have hsub : inSet ⊆ (Finset.univ : Finset (Fin (4 ^ s + 1))).filter (fun v => (adjE v).isSome = true) := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hv with rfl | hv'
      · exact hquad_some
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv'
        exact hbit_some j.val j.isLt
    have hnot0 : (⟨0, by positivity⟩ : Fin (4 ^ s + 1)) ∉
        (Finset.univ : Finset (Fin (2 * s))).image (fun j : Fin (2 * s) => mkV s (2 ^ j.val)) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro j h
      have h2j : 2 ^ j.val < 4 ^ s := by rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) j.isLt
      have := congrArg Fin.val h; dsimp only at this; rw [mkV_val s (by omega)] at this
      have := Nat.two_pow_pos j.val; omega
    have hinj : Function.Injective (fun j : Fin (2 * s) => mkV s (2 ^ j.val)) := by
      intro a b h
      have ha : 2 ^ a.val < 4 ^ s := by rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) a.isLt
      have hb : 2 ^ b.val < 4 ^ s := by rw [four_pow_eq_two_pow]; exact Nat.pow_lt_pow_right (by omega) b.isLt
      have := congrArg Fin.val h
      rw [mkV_val s (by omega), mkV_val s (by omega)] at this
      exact Fin.ext (Nat.pow_right_injective (by omega : 2 ≤ 2) this)
    have hcard : inSet.card = 2 * s + 1 := by
      simp only [inSet]
      rw [Finset.card_insert_of_notMem hnot0, Finset.card_image_of_injective _ hinj,
        Finset.card_univ, Fintype.card_fin]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hgsE_B : gsE.countP isBinGate + 4 * s + 3 ≤ 3 * 4 ^ s := by
    have hpot : gsE.countP isBinGate + someCount adjE ≤
        gs0.countP isBinGate + someCount (initAdj s) + L.length := htrans.2.2.1
    rw [hpair.2.2.1, someCount_initAdj s hs, hL_len] at hpot
    have h4s_ge : 2 * s + 1 ≤ 4 ^ s := by
      have : ∀ m, m + 1 ≤ 2 ^ m := fun m => by
        induction m with | zero => simp | succ m ih => rw [pow_succ]; omega
      rw [four_pow_eq_two_pow]; exact this (2 * s)
    omega
  have hgsE_T : gsE.countP isNLGate = 0 := by rw [htrans.2.2.2.1, hpair.2.2.2.1]
  let Lw : ℕ → ℕ := fun j => (adjE (mkV s (2 ^ j))).getD 0
  let Qw : ℕ := (adjE ⟨0, by positivity⟩).getD 0
  have hLw_eq : ∀ j < 2 * s, adjE (mkV s (2 ^ j)) = some (Lw j) := by
    intro j hj
    have hs' := hbit_some j hj
    cases h : adjE (mkV s (2 ^ j)) with
    | none => rw [h] at hs'; cases hs'
    | some w => simp [Lw, h]
  have hQw_eq : adjE ⟨0, by positivity⟩ = some Qw := by
    cases h : adjE ⟨0, by positivity⟩ with
    | none => rw [h] at hquad_some; cases hquad_some
    | some w =>
      have hQw : Qw = w := by change (adjE ⟨0, by positivity⟩).getD 0 = w; rw [h]; rfl
      rw [hQw]
  have hLw_lt : ∀ j < 2 * s, Lw j < 4 ^ s + 4 ^ s + gsE.length := fun j hj =>
    htrans.2.1 _ _ (hLw_eq j hj)
  have hQw_lt : Qw < 4 ^ s + 4 ^ s + gsE.length := htrans.2.1 _ _ hQw_eq
  have hps := prodSum_spec s hs gsE Lw s hs le_rfl htrans.1 hLw_lt
  set gsS := (prodSum s gsE Lw s).1
  set outS := (prodSum s gsE Lw s).2
  have hC_signed_rep : Represents (signedFun s) ⟨gsS, outS⟩ := by
    intro x y
    unfold Circuit.eval Circuit.wires
    change (gsS.foldl stepWires (oneEach x y)).getD outS false = signedFun s x y
    rw [(hps.2.2.2.2.2 (oneEach x y) (by simp [oneEach])).2, signedFun_eq_prod_sum]
    have hrange : xorSum (Finset.range s) (fun i =>
        (gsE.foldl stepWires (oneEach x y)).getD (Lw i) false &&
        (gsE.foldl stepWires (oneEach x y)).getD (Lw (s + i)) false) =
      xorSum (Finset.univ : Finset (Fin s)) (fun i =>
        (gsE.foldl stepWires (oneEach x y)).getD (Lw i.val) false &&
        (gsE.foldl stepWires (oneEach x y)).getD (Lw (s + i.val)) false) := by
      unfold xorSum
      have hcard : ((Finset.range s).filter (fun i =>
          ((gsE.foldl stepWires (oneEach x y)).getD (Lw i) false &&
           (gsE.foldl stepWires (oneEach x y)).getD (Lw (s + i)) false) = true)).card =
        ((Finset.univ : Finset (Fin s)).filter (fun i =>
          ((gsE.foldl stepWires (oneEach x y)).getD (Lw i.val) false &&
           (gsE.foldl stepWires (oneEach x y)).getD (Lw (s + i.val)) false) = true)).card := by
        have himg : ((Finset.univ : Finset (Fin s)).filter (fun i =>
            ((gsE.foldl stepWires (oneEach x y)).getD (Lw i.val) false &&
             (gsE.foldl stepWires (oneEach x y)).getD (Lw (s + i.val)) false) = true)).image Fin.val =
          (Finset.range s).filter (fun i =>
            ((gsE.foldl stepWires (oneEach x y)).getD (Lw i) false &&
             (gsE.foldl stepWires (oneEach x y)).getD (Lw (s + i)) false) = true) := by
          ext k
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
          · rintro ⟨hk, hcond⟩; exact ⟨⟨k, hk⟩, hcond, rfl⟩
        rw [← himg, Finset.card_image_of_injective _ Fin.val_injective]
      rw [hcard]
    rw [hrange]
    apply xorSum_congr rfl
    intro i _
    have hb1 := heval_bit i.val (by omega) x y
    have hb2 := heval_bit (s + i.val) (by omega) x y
    rw [hLw_eq i.val (by omega)] at hb1
    rw [hLw_eq (s + i.val) (by omega)] at hb2
    simp only [evalOpt] at hb1 hb2
    rw [hb1, hb2]
  have hQw_ltS : Qw < 4 ^ s + 4 ^ s + gsS.length := by
    have hlenS : gsE.length ≤ gsS.length := hps.2.2.1
    omega
  set gsD := gsS ++ xorGates (4 ^ s + 4 ^ s + gsS.length) outS Qw
  set outD := 4 ^ s + 4 ^ s + gsS.length + 1
  have hwfD : WellFormed (4 ^ s + 4 ^ s) gsD := wellFormed_append_xor hps.1 hps.2.1 hQw_ltS
  have hC_dot_rep : Represents (dotFun s) ⟨gsD, outD⟩ := by
    intro x y
    unfold Circuit.eval Circuit.wires
    change (gsD.foldl stepWires (oneEach x y)).getD outD false = dotFun s x y
    have hxlen : (oneEach x y).length = 4 ^ s + 4 ^ s := by simp [oneEach]
    have hstep := foldl_append_xor_eval gsS outS Qw (oneEach x y) hxlen hps.2.1 hQw_ltS
    rw [hstep.2, (hps.2.2.2.2.2 (oneEach x y) hxlen).1 Qw hQw_lt]
    have hS : (gsS.foldl stepWires (oneEach x y)).getD outS false = signedFun s x y := hC_signed_rep x y
    have hQ : (gsE.foldl stepWires (oneEach x y)).getD Qw false = xor (quadFun s x) (quadFun s y) := by
      have := heval_quad x y; rw [hQw_eq] at this; exact this
    rw [hS, hQ]
    unfold signedFun
    cases quadFun s x <;> cases quadFun s y <;> cases dotFun s x y <;> rfl
  refine ⟨⟨⟨gsS, outS⟩, hps.1.1, hps.1.2, hC_signed_rep, ?_, ?_⟩,
          ⟨⟨gsD, outD⟩, hwfD.1, hwfD.2, hC_dot_rep, ?_, ?_⟩⟩
  · unfold tCount; rw [hps.2.2.2.2.1, hgsE_T]; omega
  · unfold bCount; rw [hps.2.2.2.1]; omega
  · unfold tCount gsD; rw [List.countP_append, xorGates_countT, hps.2.2.2.2.1, hgsE_T]; omega
  · unfold bCount gsD; rw [List.countP_append, xorGates_countB, hps.2.2.2.1]; omega

end UpperConstruction

theorem final :
  ∀ s : ℕ, 1 ≤ s →
    let N := 4^s
    let T := Fin N → Fin N → Bool
    let dot := fun (x y : Fin N) =>
      ((Finset.univ : Finset (Fin (2*s))).filter (fun i =>
        x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1
    let quad := fun (x : Fin N) =>
      ((Finset.univ : Finset (Fin s)).filter (fun i =>
        x.val.testBit i.val && x.val.testBit (s+i.val))).card % 2 == 1
    let signed := fun (x y : Fin N) => xor (xor (quad x) (quad y)) (dot x y)
    let b := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => g.inputs.length == 2)
    let t := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => (g.inputs.length == 2) &&
        xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
            (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
    let accepts := fun (H : T) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
      PEqualNP.Represents.Represents H C ∧ t C ≤ s
    let exact := fun (H : T) (d : ℕ) =>
      (∀ C, accepts H C → t C = s ∧ 3*N ≤ b C + 2*s + d) ∧
      ∃ C, accepts H C ∧ t C = s ∧ b C + 2*s + d = 3*N
    exact dot 3 ∧ exact signed 4 := by
  intro s hs
  dsimp only
  have hdot_lb : ∀ C,
      ((∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
       ReadsBack (4 ^ s + 4 ^ s) C ∧
       Represents (dotFun s) C ∧
       tCount C ≤ s) →
      tCount C = s ∧ 3 * 4 ^ s ≤ bCount C + 2 * s + 3 := by
    rintro C ⟨hfan, hrb, hrep, htle⟩
    have hrow := dotFun_distinct_rows s
    have hcol : ∀ v₁ v₂ c, (∀ u, dotFun s u v₁ = xor (dotFun s u v₂) c) → v₁ = v₂ := by
      intro v₁ v₂ c h
      exact hrow v₁ v₂ c (fun u => by
        rw [dotFun_symm s v₁ u, dotFun_symm s v₂ u]
        exact h u)
    have hlb := lower_bound_general C hs hfan hrb hrep htle hrow hcol
    have hzero : ∃ u0 : Fin (4 ^ s), ∀ v, dotFun s u0 v = false :=
      ⟨⟨0, by positivity⟩, dotFun_zero_left s⟩
    have h1lt : 1 < 4 ^ s := by
      have : 4 ^ 1 ≤ 4 ^ s := Nat.pow_le_pow_right (by omega) hs
      omega
    have hone : ∃ u1 v1 : Fin (4 ^ s), dotFun s u1 v1 = true :=
      ⟨⟨1, h1lt⟩, ⟨1, h1lt⟩, dotFun_one_one s hs⟩
    exact ⟨hlb.1, hlb.2.2 hzero hone⟩
  have hsigned_lb : ∀ C,
      ((∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
       ReadsBack (4 ^ s + 4 ^ s) C ∧
       Represents (signedFun s) C ∧
       tCount C ≤ s) →
      tCount C = s ∧ 3 * 4 ^ s ≤ bCount C + 2 * s + 4 := by
    rintro C ⟨hfan, hrb, hrep, htle⟩
    have hrow := signedFun_distinct_rows s
    have hcol : ∀ v₁ v₂ c, (∀ u, signedFun s u v₁ = xor (signedFun s u v₂) c) → v₁ = v₂ := by
      intro v₁ v₂ c h
      exact hrow v₁ v₂ c (fun u => by
        rw [signedFun_symm s v₁ u, signedFun_symm s v₂ u]
        exact h u)
    have hlb := lower_bound_general C hs hfan hrb hrep htle hrow hcol
    exact ⟨hlb.1, hlb.2.1⟩
  obtain ⟨⟨Cs, hCs_fan, hCs_rb, hCs_rep, hCs_t, hCs_b⟩,
          ⟨Cd, hCd_fan, hCd_rb, hCd_rep, hCd_t, hCd_b⟩⟩ := upper_bounds_exist s hs
  have hCd_lb := (hdot_lb Cd ⟨hCd_fan, hCd_rb, hCd_rep, le_of_eq hCd_t⟩).2
  have hCs_lb := (hsigned_lb Cs ⟨hCs_fan, hCs_rb, hCs_rep, le_of_eq hCs_t⟩).2
  refine ⟨⟨hdot_lb, ⟨Cd, ⟨hCd_fan, hCd_rb, hCd_rep, le_of_eq hCd_t⟩, hCd_t, le_antisymm hCd_b hCd_lb⟩⟩,
          ⟨hsigned_lb, ⟨Cs, ⟨hCs_fan, hCs_rb, hCs_rep, le_of_eq hCs_t⟩, hCs_t, le_antisymm hCs_b hCs_lb⟩⟩⟩

end PEqualNP.Outside.L_meta_25798

theorem PEqualNP.Outside.L_meta_25798 :
  ∀ s : ℕ, 1 ≤ s →
    let N := 4^s
    let T := Fin N → Fin N → Bool
    let dot := fun (x y : Fin N) =>
      ((Finset.univ : Finset (Fin (2*s))).filter (fun i =>
        x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1
    let quad := fun (x : Fin N) =>
      ((Finset.univ : Finset (Fin s)).filter (fun i =>
        x.val.testBit i.val && x.val.testBit (s+i.val))).card % 2 == 1
    let signed := fun (x y : Fin N) => xor (xor (quad x) (quad y)) (dot x y)
    let b := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => g.inputs.length == 2)
    let t := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => (g.inputs.length == 2) &&
        xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
            (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
    let accepts := fun (H : T) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
      PEqualNP.Represents.Represents H C ∧ t C ≤ s
    let exact := fun (H : T) (d : ℕ) =>
      (∀ C, accepts H C → t C = s ∧ 3*N ≤ b C + 2*s + d) ∧
      ∃ C, accepts H C ∧ t C = s ∧ b C + 2*s + d = 3*N
    exact dot 3 ∧ exact signed 4 :=
  PEqualNP.Outside.L_meta_25798.final
