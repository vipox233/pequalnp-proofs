import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50742_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

/-! ## Running the gates (copied from L_meta_7730) -/

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value w g]) w

lemma run_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [value w g])
    exact ⟨value w g :: t, by
      change run gs (w ++ [value w g]) = _
      rw [ht, List.append_assoc]
      rfl, by simp [hl]⟩

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_ext gs w
  rw [ht, List.length_append, hl]

lemma run_before (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_take (gs : List Gate) (w : List Bool) {j i : ℕ}
    (hj : j ≤ gs.length) (hi : i < w.length + j) :
    (run (gs.take j) w).getD i false = (run gs w).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_before _ _ _ (by simpa [run_length, List.length_take, min_eq_left hj])).symm

lemma gateAt_eq (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj

lemma split_gate (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) = C.gates := by
  rw [gateAt_eq C hj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

lemma value_take (C : Circuit) {n j : ℕ} (xs : List Bool) (hx : xs.length = n)
    (hj : j ≤ C.gates.length) (g : Gate) (hb : ∀ i ∈ g.inputs, i < n + j) :
    value (run (C.gates.take j) xs) g = value (C.wires xs) g := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_take _ _ hj (by rw [hx]; exact hb i hi)

lemma wire_gate (C : Circuit) {n j : ℕ} (xs : List Bool) (hx : xs.length = n)
    (hr : ReadsBack n C) (hj : j < C.gates.length) :
    (C.wires xs).getD (n + j) false = value (C.wires xs) (gateAt C j) := by
  let w := run (C.gates.take j) xs
  let b := value w (gateAt C j)
  have hl : w.length = n + j := by
    simp [w, run_length, hx, List.length_take, min_eq_left (Nat.le_of_lt hj)]
  have he : C.wires xs = run (C.gates.drop (j + 1)) (w ++ [b]) := by
    change run C.gates xs = _
    conv_lhs => rw [← split_gate C hj, run_append]
    rfl
  calc
    _ = (w ++ [b]).getD (n + j) false := by
      rw [he, run_before _ _ _ (by simp [hl])]
    _ = b := by rw [← hl]; simp
    _ = _ := value_take C xs hx hj.le _ (hr j hj)

/-! ## Wire values on an input function -/

def W (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x ++ [false, true])).getD i false

lemma W_lt (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n + 2) :
    W C x i = (List.ofFn x ++ [false, true]).getD i false := by
  unfold W
  exact run_before C.gates _ i (by simpa using hi)

@[simp] lemma W_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    W C x v.val = x v := by
  rw [W_lt C x v.val (by omega), List.getD_append _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp)]
  simp

lemma W_n (C : Circuit) {n : ℕ} (x : Fin n → Bool) : W C x n = false := by
  rw [W_lt C x n (by omega), List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
    Nat.sub_self]
  rfl

lemma W_n1 (C : Circuit) {n : ℕ} (x : Fin n → Bool) : W C x (n + 1) = true := by
  rw [W_lt C x (n + 1) (by omega), List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left]
  rfl

lemma W_gate (C : Circuit) {n j : ℕ} (hr : ReadsBack (n + 2) C) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    W C x (n + 2 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C x)) := by
  unfold W
  rw [wire_gate C _ (by simp) hr hj]
  rfl

/-! ## Six-point value vectors -/

def enc (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) +
    (if b4 then 16 else 0) + (if b5 then 32 else 0)

lemma enc_and (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    enc (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5) =
      enc a0 a1 a2 a3 a4 a5 &&& enc b0 b1 b2 b3 b4 b5 := by
  revert a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
  decide +kernel

lemma enc_or (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    enc (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5) =
      enc a0 a1 a2 a3 a4 a5 ||| enc b0 b1 b2 b3 b4 b5 := by
  revert a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
  decide +kernel

lemma enc_not (a0 a1 a2 a3 a4 a5 : Bool) :
    enc (!a0) (!a1) (!a2) (!a3) (!a4) (!a5) = enc a0 a1 a2 a3 a4 a5 ^^^ 63 := by
  revert a0 a1 a2 a3 a4 a5
  decide +kernel

lemma enc_lt (a0 a1 a2 a3 a4 a5 : Bool) : enc a0 a1 a2 a3 a4 a5 < 64 := by
  revert a0 a1 a2 a3 a4 a5
  decide +kernel

def V (C : Circuit) {n : ℕ} (x0 x1 x2 x3 x4 x5 : Fin n → Bool) (i : ℕ) : ℕ :=
  enc (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i) (W C x4 i) (W C x5 i)

lemma V_gate (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C) {j : ℕ}
    (hj : j < C.gates.length) (x0 x1 x2 x3 x4 x5 : Fin n → Bool) (M : ℕ → Prop)
    (hM : ∀ i < n + 2 + j, M (V C x0 x1 x2 x3 x4 x5 i)) :
    ((gateAt C j).op = GateOp.not →
      V C x0 x1 x2 x3 x4 x5 (n + 2 + j) = 63 ∨
        ∃ u, M u ∧ u < 64 ∧ V C x0 x1 x2 x3 x4 x5 (n + 2 + j) = u ^^^ 63) ∧
    ((gateAt C j).op ≠ GateOp.not →
      V C x0 x1 x2 x3 x4 x5 (n + 2 + j) = 0 ∨ V C x0 x1 x2 x3 x4 x5 (n + 2 + j) = 63 ∨
        ∃ u w, M u ∧ M w ∧ u < 64 ∧ w < 64 ∧
          (V C x0 x1 x2 x3 x4 x5 (n + 2 + j) = u &&& w ∨
            V C x0 x1 x2 x3 x4 x5 (n + 2 + j) = u ||| w)) := by
  have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C hj]; exact List.getElem_mem _
  have hfg := hf _ hg
  have hin : ∀ i ∈ (gateAt C j).inputs, i < n + 2 + j := hr j hj
  have hV : V C x0 x1 x2 x3 x4 x5 (n + 2 + j) =
      enc ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x0)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x1)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x2)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x3)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x4)))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (W C x5))) := by
    simp only [V, W_gate C hr hj]
  rw [hV]
  generalize gateAt C j = g at hfg hin ⊢
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hfg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hVi : ∀ i ∈ ins, M (V C x0 x1 x2 x3 x4 x5 i) := fun i hi => hM i (hin i hi)
  rcases ins with _ | ⟨i, _ | ⟨i', _ | ⟨i'', rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨fun h => (by cases h), fun _ => Or.inr (Or.inl rfl)⟩
    · exact ⟨fun h => (by cases h), fun _ => Or.inl rfl⟩
    · exact ⟨fun _ => Or.inl rfl, fun h => absurd rfl h⟩
  · have hi := hVi i (by simp)
    have hlt := enc_lt (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i) (W C x4 i) (W C x5 i)
    rcases hop with rfl | rfl | rfl
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi, hlt, hlt, Or.inl ?_⟩)⟩
      rw [Nat.and_self]
      simp [GateOp.eval, V]
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi, hlt, hlt, Or.inr ?_⟩)⟩
      rw [Nat.or_self]
      simp [GateOp.eval, V]
    · refine ⟨fun _ => Or.inr ⟨_, hi, hlt, ?_⟩, fun h => absurd rfl h⟩
      rw [V, ← enc_not]
      simp [GateOp.eval]
  · have hi := hVi i (by simp)
    have hi' := hVi i' (by simp)
    have hlt := enc_lt (W C x0 i) (W C x1 i) (W C x2 i) (W C x3 i) (W C x4 i) (W C x5 i)
    have hlt' := enc_lt (W C x0 i') (W C x1 i') (W C x2 i') (W C x3 i') (W C x4 i') (W C x5 i')
    rcases hop with rfl | rfl | rfl
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi', hlt, hlt', Or.inl ?_⟩)⟩
      rw [V, V, ← enc_and]
      simp [GateOp.eval]
    · refine ⟨fun h => (by cases h), fun _ => Or.inr (Or.inr ⟨_, _, hi, hi', hlt, hlt', Or.inr ?_⟩)⟩
      rw [V, V, ← enc_or]
      simp [GateOp.eval]
    · refine ⟨fun _ => Or.inr ⟨_, hi, hlt, ?_⟩, fun h => absurd rfl h⟩
      rw [V, ← enc_not]
      simp [GateOp.eval]
  · exfalso
    simp only [List.length_cons] at hlen
    omega

/-! ## NOT counts of gate lists -/

lemma nc_cons_not (l : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ + 1 := by
  simp [notCount, h]

lemma nc_cons_ne (l : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ := by
  simp [notCount, h]

/-! ## Bounded search over sets of value vectors

A set of six-point value vectors is a bitmask `S < 2 ^ 64`. `aoM S` is the bitmask of all values
one AND/OR gate (or a constant gate) can produce from members of `S`, `nM S` the same for NOT. -/

def mem (S v : ℕ) : Bool := S.testBit v

def ins (S v : ℕ) : ℕ := S ||| 2 ^ v

lemma mem_ins (S v u : ℕ) : mem (ins S v) u = (mem S u || decide (v = u)) := by
  simp [mem, ins, Nat.testBit_two_pow]

lemma mem_or_l {a v : ℕ} (b : ℕ) (h : mem a v = true) : mem (a ||| b) v = true := by
  simp only [mem] at h ⊢
  simp [Nat.testBit_or, h]

lemma mem_or_r (a : ℕ) {b v : ℕ} (h : mem b v = true) : mem (a ||| b) v = true := by
  simp only [mem] at h ⊢
  simp [Nat.testBit_or, h]

lemma mem_pow (v : ℕ) : mem (2 ^ v) v = true := by
  simp [mem, Nat.testBit_two_pow]

def goal (S : ℕ) : Bool := mem S 2 && mem S 35 && mem S 52

/-- How many of the three target vectors are still absent from `S`. -/
def miss (S : ℕ) : ℕ := (!mem S 2).toNat + (!mem S 35).toNat + (!mem S 52).toNat

lemma miss_goal {S : ℕ} (h : goal S = true) : miss S = 0 := by
  simp only [goal, Bool.and_eq_true] at h
  simp [miss, h.1.1, h.1.2, h.2]

lemma miss_ins (S v : ℕ) : miss S ≤ miss (ins S v) + 1 := by
  simp only [miss, mem_ins]
  cases mem S 2 <;> cases mem S 35 <;> cases mem S 52 <;>
    by_cases hA : v = 2 <;> by_cases hB : v = 35 <;> by_cases hC : v = 52 <;>
      simp_all

/-- The members of `S` below `n`. -/
def elems (S : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => cond (mem S n) (n :: elems S n) (elems S n)

lemma mem_elems (S : ℕ) : ∀ n u, u < n → mem S u = true → u ∈ elems S n := by
  intro n
  induction n with
  | zero => intro u hu _; omega
  | succ n ih =>
    intro u hu hm
    show u ∈ cond (mem S n) (n :: elems S n) (elems S n)
    by_cases h : u = n
    · rw [← h, hm]
      simp
    · have h' := ih u (by omega) hm
      cases mem S n <;> simp [h']

def row (u : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: l => 2 ^ (u &&& w) ||| 2 ^ (u ||| w) ||| row u l

lemma row_mem (u : ℕ) : ∀ l w, w ∈ l →
    mem (row u l) (u &&& w) = true ∧ mem (row u l) (u ||| w) = true := by
  intro l
  induction l with
  | nil => intro w hw; simp at hw
  | cons a l ih =>
    intro w hw
    rw [row]
    rcases List.mem_cons.1 hw with e | h
    · rw [e]
      exact ⟨mem_or_l _ (mem_or_l _ (mem_pow _)), mem_or_l _ (mem_or_r _ (mem_pow _))⟩
    · have h2 := ih w h
      exact ⟨mem_or_r _ h2.1, mem_or_r _ h2.2⟩

def pairs : List ℕ → ℕ
  | [] => 0
  | u :: l => row u (u :: l) ||| pairs l

lemma pairs_mem : ∀ l u w, u ∈ l → w ∈ l →
    mem (pairs l) (u &&& w) = true ∧ mem (pairs l) (u ||| w) = true := by
  intro l
  induction l with
  | nil => intro u w hu; simp at hu
  | cons a l ih =>
    intro u w hu hw
    rw [pairs]
    rcases List.mem_cons.1 hu with e | hu'
    · rw [e]
      have h2 := row_mem a (a :: l) w hw
      exact ⟨mem_or_l _ h2.1, mem_or_l _ h2.2⟩
    · rcases List.mem_cons.1 hw with e | hw'
      · rw [e]
        have h2 := row_mem a (a :: l) u (List.mem_cons_of_mem _ hu')
        rw [Nat.and_comm u a, Nat.or_comm u a]
        exact ⟨mem_or_l _ h2.1, mem_or_l _ h2.2⟩
      · have h2 := ih u w hu' hw'
        exact ⟨mem_or_r _ h2.1, mem_or_r _ h2.2⟩

def negs : List ℕ → ℕ
  | [] => 0
  | u :: l => 2 ^ (u ^^^ 63) ||| negs l

lemma negs_mem : ∀ l u, u ∈ l → mem (negs l) (u ^^^ 63) = true := by
  intro l
  induction l with
  | nil => intro u hu; simp at hu
  | cons a l ih =>
    intro u hu
    rw [negs]
    rcases List.mem_cons.1 hu with e | h
    · rw [e]
      exact mem_or_l _ (mem_pow _)
    · exact mem_or_r _ (ih u h)

def aoM (S : ℕ) : ℕ := 1 ||| 2 ^ 63 ||| pairs (elems S 64)

def nM (S : ℕ) : ℕ := 2 ^ 63 ||| negs (elems S 64)

lemma aoM_zero (S : ℕ) : mem (aoM S) 0 = true := by
  unfold aoM
  exact mem_or_l _ (mem_or_l _ (by decide))

lemma aoM_full (S : ℕ) : mem (aoM S) 63 = true := by
  unfold aoM
  exact mem_or_l _ (mem_or_r _ (mem_pow 63))

lemma aoM_pair (S u w : ℕ) (hu : u < 64) (hw : w < 64) (mu : mem S u = true)
    (mw : mem S w = true) : mem (aoM S) (u &&& w) = true ∧ mem (aoM S) (u ||| w) = true := by
  have h := pairs_mem (elems S 64) u w (mem_elems S 64 u hu mu) (mem_elems S 64 w hw mw)
  unfold aoM
  exact ⟨mem_or_r _ h.1, mem_or_r _ h.2⟩

lemma nM_full (S : ℕ) : mem (nM S) 63 = true := by
  unfold nM
  exact mem_or_l _ (mem_pow 63)

lemma nM_neg (S u : ℕ) (hu : u < 64) (mu : mem S u = true) : mem (nM S) (u ^^^ 63) = true := by
  unfold nM
  exact mem_or_r _ (negs_mem _ u (mem_elems S 64 u hu mu))

/-- `anyB f n` checks `f v` for some `v < n`. -/
def anyB (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => f n || anyB f n

lemma anyB_iff (f : ℕ → Bool) : ∀ n, anyB f n = true ↔ ∃ v < n, f v = true := by
  intro n
  induction n with
  | zero => simp [anyB]
  | succ n ih =>
    simp only [anyB, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨v, hv, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨v, by omega, h⟩
    · rintro ⟨v, hv, h⟩
      by_cases e : v = n
      · subst e
        exact Or.inl h
      · exact Or.inr ⟨v, by omega, h⟩

/-- Can `k` more gates, at most `r` of them NOTs, add all three targets to `S`? A NOT gate whose
value an AND/OR gate could also produce is only tried as an AND/OR gate. -/
def search : ℕ → ℕ → ℕ → Bool
  | 0, _, S => goal S
  | k + 1, 0, S => goal S || anyB (fun v => !mem S v && decide (miss (ins S v) ≤ k) &&
      mem (aoM S) v && search k 0 (ins S v)) 64
  | k + 1, r + 1, S => goal S || anyB (fun v => !mem S v && decide (miss (ins S v) ≤ k) &&
      ((mem (aoM S) v && search k (r + 1) (ins S v)) ||
        (!mem (aoM S) v && mem (nM S) v && search k r (ins S v)))) 64

lemma search_z (r S : ℕ) : search 0 r S = goal S := by
  cases r <;> rfl

lemma search_sz (k S : ℕ) : search (k + 1) 0 S = (goal S || anyB (fun v => !mem S v &&
    decide (miss (ins S v) ≤ k) && mem (aoM S) v && search k 0 (ins S v)) 64) := rfl

lemma search_ss (k r S : ℕ) : search (k + 1) (r + 1) S = (goal S || anyB (fun v => !mem S v &&
    decide (miss (ins S v) ≤ k) && ((mem (aoM S) v && search k (r + 1) (ins S v)) ||
      (!mem (aoM S) v && mem (nM S) v && search k r (ins S v)))) 64) := rfl

lemma search_goal {k r S : ℕ} (h : goal S = true) : search k r S = true := by
  cases k with
  | zero => rw [search_z]; exact h
  | succ k => cases r <;> simp [search_sz, search_ss, h]

lemma search_miss (k r S : ℕ) (h : search k r S = true) : miss S ≤ k := by
  cases k with
  | zero =>
    rw [search_z] at h
    rw [miss_goal h]
  | succ k =>
    cases r with
    | zero =>
      rw [search_sz, Bool.or_eq_true, anyB_iff] at h
      rcases h with h | ⟨v, -, hv⟩
      · rw [miss_goal h]; omega
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨⟨⟨-, hk⟩, -⟩, -⟩ := hv
        have := miss_ins S v
        omega
    | succ r =>
      rw [search_ss, Bool.or_eq_true, anyB_iff] at h
      rcases h with h | ⟨v, -, hv⟩
      · rw [miss_goal h]; omega
      · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hv
        obtain ⟨⟨-, hk⟩, -⟩ := hv
        have := miss_ins S v
        omega

lemma search_mono_k (k : ℕ) : ∀ r S, search k r S = true → search (k + 1) r S = true := by
  induction k with
  | zero =>
    intro r S h
    rw [search_z] at h
    exact search_goal h
  | succ k ih =>
    intro r S h
    cases r with
    | zero =>
      rw [search_sz, Bool.or_eq_true, anyB_iff] at h
      rw [search_sz, Bool.or_eq_true, anyB_iff]
      rcases h with h | ⟨v, hv, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨v, hv, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
        exact ⟨⟨⟨h1, by omega⟩, h3⟩, ih _ _ h4⟩
    | succ r =>
      rw [search_ss, Bool.or_eq_true, anyB_iff] at h
      rw [search_ss, Bool.or_eq_true, anyB_iff]
      rcases h with h | ⟨v, hv, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨v, hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb ⊢
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := hb
        · exact ⟨⟨h1, by omega⟩, Or.inl ⟨h3, ih _ _ h4⟩⟩
        · exact ⟨⟨h1, by omega⟩, Or.inr ⟨h3, ih _ _ h4⟩⟩

lemma search_mono_r (k : ℕ) : ∀ r S, search k r S = true → search k (r + 1) S = true := by
  induction k with
  | zero =>
    intro r S h
    rw [search_z] at h
    rw [search_z]
    exact h
  | succ k ih =>
    intro r S h
    cases r with
    | zero =>
      rw [search_sz, Bool.or_eq_true, anyB_iff] at h
      rw [search_ss, Bool.or_eq_true, anyB_iff]
      rcases h with h | ⟨v, hv, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨v, hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb ⊢
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
        exact ⟨⟨h1, h2⟩, Or.inl ⟨h3, ih _ _ h4⟩⟩
    | succ r =>
      rw [search_ss, Bool.or_eq_true, anyB_iff] at h
      rw [search_ss, Bool.or_eq_true, anyB_iff]
      rcases h with h | ⟨v, hv, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨v, hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb ⊢
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := hb
        · exact ⟨⟨h1, h2⟩, Or.inl ⟨h3, ih _ _ h4⟩⟩
        · exact ⟨⟨h1, h2⟩, Or.inr ⟨h3, ih _ _ h4⟩⟩

lemma search_mono {k k' r r' S : ℕ} (hk : k ≤ k') (hr : r ≤ r') (h : search k r S = true) :
    search k' r' S = true := by
  have h1 : search k r' S = true := by
    induction hr with
    | refl => exact h
    | step _ ih => exact search_mono_r _ _ _ ih
  induction hk with
  | refl => exact h1
  | step _ ih => exact search_mono_k _ _ _ ih

lemma search_step_ao {k r S v : ℕ} (hv : v < 64) (hm : mem S v = false)
    (ho : mem (aoM S) v = true) (h : search k r (ins S v) = true) : search (k + 1) r S = true := by
  have hk := search_miss k r _ h
  cases r with
  | zero =>
    rw [search_sz, Bool.or_eq_true, anyB_iff]
    exact Or.inr ⟨v, hv, by simp [hm, ho, h, hk]⟩
  | succ r =>
    rw [search_ss, Bool.or_eq_true, anyB_iff]
    exact Or.inr ⟨v, hv, by simp [hm, ho, h, hk]⟩

lemma search_step_n {k r S v : ℕ} (hv : v < 64) (hm : mem S v = false)
    (ho : mem (nM S) v = true) (h : search k r (ins S v) = true) :
    search (k + 1) (r + 1) S = true := by
  have hk := search_miss k r _ h
  rw [search_ss, Bool.or_eq_true, anyB_iff]
  cases ha : mem (aoM S) v
  · exact Or.inr ⟨v, hv, by simp [hm, ho, ha, h, hk]⟩
  · have h' := search_mono_r k r _ h
    exact Or.inr ⟨v, hv, by simp [hm, ha, h', hk]⟩

/-- No 5 gates with at most two NOTs reach all three targets from the chain inputs. -/
lemma chk : search 5 2 15060318633198616577 = false := by decide +kernel

lemma search_sound (C : Circuit) {n : ℕ} (hf : FanInTwo C) (hr : ReadsBack (n + 2) C)
    (x0 x1 x2 x3 x4 x5 : Fin n → Bool) (p q s : ℕ) (hp : p < n + 2 + C.gates.length)
    (hq : q < n + 2 + C.gates.length) (hs : s < n + 2 + C.gates.length)
    (hP : V C x0 x1 x2 x3 x4 x5 p = 2) (hQ : V C x0 x1 x2 x3 x4 x5 q = 35)
    (hS' : V C x0 x1 x2 x3 x4 x5 s = 52) :
    ∀ d j, j + d = C.gates.length → ∀ S,
      (∀ i < n + 2 + j, mem S (V C x0 x1 x2 x3 x4 x5 i) = true) →
        search d (notCount ⟨C.gates.drop j, 0⟩) S = true := by
  intro d
  induction d with
  | zero =>
    intro j hj S hS
    have hA := hS p (by omega)
    have hB := hS q (by omega)
    have hC := hS s (by omega)
    rw [hP] at hA
    rw [hQ] at hB
    rw [hS'] at hC
    exact search_goal (by simp [goal, hA, hB, hC])
  | succ d ih =>
    intro j hj S hS
    have hjl : j < C.gates.length := by omega
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [gateAt_eq C hjl]
      exact List.drop_eq_getElem_cons hjl
    rw [hdrop]
    have hvlt : V C x0 x1 x2 x3 x4 x5 (n + 2 + j) < 64 := enc_lt _ _ _ _ _ _
    have hgate := V_gate C hf hr hjl x0 x1 x2 x3 x4 x5 (fun u => mem S u = true) hS
    by_cases hm : mem S (V C x0 x1 x2 x3 x4 x5 (n + 2 + j)) = true
    · have h1 := ih (j + 1) (by omega) S (fun i hi => by
        rcases (show i < n + 2 + j ∨ i = n + 2 + j by omega) with h | h
        · exact hS i h
        · rw [h]; exact hm)
      by_cases hn : (gateAt C j).op = GateOp.not
      · rw [nc_cons_not _ _ hn]
        exact search_mono (Nat.le_succ d) (Nat.le_succ _) h1
      · rw [nc_cons_ne _ _ hn]
        exact search_mono (Nat.le_succ d) le_rfl h1
    · have hmS : mem S (V C x0 x1 x2 x3 x4 x5 (n + 2 + j)) = false := by simpa using hm
      have h1 := ih (j + 1) (by omega) (ins S (V C x0 x1 x2 x3 x4 x5 (n + 2 + j)))
        (fun i hi => by
          rw [mem_ins]
          rcases (show i < n + 2 + j ∨ i = n + 2 + j by omega) with h | h
          · simp [hS i h]
          · simp [h])
      by_cases hn : (gateAt C j).op = GateOp.not
      · rw [nc_cons_not _ _ hn]
        refine search_step_n hvlt hmS ?_ h1
        rcases hgate.1 hn with h | ⟨u, hu, hu64, h⟩
        · rw [h]; exact nM_full S
        · rw [h]; exact nM_neg S u hu64 hu
      · rw [nc_cons_ne _ _ hn]
        refine search_step_ao hvlt hmS ?_ h1
        rcases hgate.2 hn with h | h | ⟨u, w, hu, hw, hu64, hw64, h | h⟩
        · rw [h]; exact aoM_zero S
        · rw [h]; exact aoM_full S
        · rw [h]; exact (aoM_pair S u w hu64 hw64 hu hw).1
        · rw [h]; exact (aoM_pair S u w hu64 hw64 hu hw).2

/-! ## The chain inputs -/

def xf (t : ℕ) : Fin 5 → Bool := fun i => decide (i.val < t)

lemma V_base (C : Circuit) (i : ℕ) (hi : i < 5 + 2) :
    mem 15060318633198616577 (V C (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) (xf 5) i) = true := by
  rcases (show i < 5 ∨ i = 5 ∨ i = 5 + 1 by omega) with h | h | h
  · obtain ⟨v, rfl⟩ : ∃ v : Fin 5, v.val = i := ⟨⟨i, h⟩, rfl⟩
    simp only [V, W_input]
    fin_cases v <;> decide
  · subst h
    simp only [V, W_n]
    decide
  · subst h
    simp only [V, W_n1]
    decide

lemma V_tgt (C : Circuit) (i m : ℕ)
    (h : ∀ t : Fin 6, W C (xf t.val) i = m.testBit t.val) :
    V C (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) (xf 5) i =
      enc (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3) (m.testBit 4)
        (m.testBit 5) := by
  have e0 : W C (xf 0) i = m.testBit 0 := h ⟨0, by decide⟩
  have e1 : W C (xf 1) i = m.testBit 1 := h ⟨1, by decide⟩
  have e2 : W C (xf 2) i = m.testBit 2 := h ⟨2, by decide⟩
  have e3 : W C (xf 3) i = m.testBit 3 := h ⟨3, by decide⟩
  have e4 : W C (xf 4) i = m.testBit 4 := h ⟨4, by decide⟩
  have e5 : W C (xf 5) i = m.testBit 5 := h ⟨5, by decide⟩
  simp only [V, e0, e1, e2, e3, e4, e5]

/-- The whole argument for an arbitrary circuit. -/
lemma main (D : Circuit) (p q s : Fin (7 + D.size)) (hf : FanInTwo D) (hrb : ReadsBack 7 D)
    (hn : notCount D ≤ 2) (hsz : D.size ≤ 5)
    (hP : ∀ t : Fin 6, W D (xf t.val) p.val = (2 : ℕ).testBit t.val)
    (hQ : ∀ t : Fin 6, W D (xf t.val) q.val = (35 : ℕ).testBit t.val)
    (hS : ∀ t : Fin 6, W D (xf t.val) s.val = (52 : ℕ).testBit t.val) : False := by
  have hA : V D (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) (xf 5) p.val = 2 :=
    (V_tgt D p.val 2 hP).trans (by decide)
  have hB : V D (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) (xf 5) q.val = 35 :=
    (V_tgt D q.val 35 hQ).trans (by decide)
  have hC : V D (xf 0) (xf 1) (xf 2) (xf 3) (xf 4) (xf 5) s.val = 52 :=
    (V_tgt D s.val 52 hS).trans (by decide)
  have hlen : D.size = D.gates.length := rfl
  have hp : p.val < 5 + 2 + D.gates.length := by have := p.isLt; omega
  have hq : q.val < 5 + 2 + D.gates.length := by have := q.isLt; omega
  have hs : s.val < 5 + 2 + D.gates.length := by have := s.isLt; omega
  have hsearch := search_sound D hf hrb _ _ _ _ _ _ p.val q.val s.val hp hq hs hA hB hC
    D.gates.length 0 (by simp) 15060318633198616577 (fun i hi => V_base D i hi)
  rw [List.drop_zero] at hsearch
  have hfin := search_mono (k' := 5) (r' := 2) (by omega) hn hsearch
  rw [chk] at hfin
  cases hfin

end PEqualNP.Outside.L_meta_50742_aux

theorem PEqualNP.Outside.L_meta_50742 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (35 : Nat).testBit t.val ∧
    w.getD r.val false = (52 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, s, hf, hrb, hn, hsz, h⟩
  refine PEqualNP.Outside.L_meta_50742_aux.main D p q s hf hrb hn hsz (fun t => ?_) (fun t => ?_)
    (fun t => ?_)
  · obtain ⟨a, -, -⟩ := h t
    exact a
  · obtain ⟨-, a, -⟩ := h t
    exact a
  · obtain ⟨-, -, a⟩ := h t
    exact a
