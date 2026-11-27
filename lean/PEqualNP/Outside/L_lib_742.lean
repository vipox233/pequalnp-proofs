import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_742_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Defs.LratEncoding (litVal ClauseSat FormulaSat)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else if t = 3 then !a else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 4
  not_eq : ∀ j < s, M.op j = 3 → M.s1 j = M.s2 j
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j)
  notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 2

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2),
    P (ix n s 0 j 3)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)],
   [Q (ix n s 0 j 3), P (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 3), Q (ix n s 3 j r), Q (ix n s 4 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).map fun k =>
    [Q (ix n s 0 j 3), Q (ix n s 1 j k), P (ix n s 2 j k)]

def fNotNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).map fun i =>
    [Q (ix n s 0 j 3), Q (ix n s 0 i 3), Q (ix n s 1 j (n + i))]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l =>
      [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)] ++
        if l = k then [P (ix n s 0 j 3)] else []

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s ++ fNot n s ++ fNotNot n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 2) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
omit hv in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 4) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) ∧ ((!(t == 3) || x || a) = true) ∧
    ((!(t == 3) || !x || !a) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7 G8 G9
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [ite_eq_left h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [ite_eq_left h2] at hc; simp at hc
    · rw [ite_eq_right h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, ite_eq_left h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [ite_eq_right h1] at hc
    by_cases h3 : k < n + s
    · rw [ite_eq_left h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, ite_eq_right h1, ite_eq_left h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [ite_eq_right h3] at hc
      by_cases h4 : g r = true
      · rw [ite_eq_left h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, ite_eq_right h1, ite_eq_right h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [ite_eq_right h4] at hc; simp at hc

include hn

omit hv in
theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

omit hv in
theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    by_cases hp : M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j
    · simp [hp]
    · have hnp := h2 hp
      by_cases ho : M.op j = 2
      · exact absurd (h1 ho) hp
      · simp [ho, hnp.1, hnp.2]

omit hv in
theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

omit hv in
theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    by_cases hp : M.pad n i
    · have hp' := h1 hp; first | exact Or.inr hp'.1 | exact Or.inr hp'.2
    · exact Or.inl hp

omit hv in
theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  by_cases hlk : l = k
  · rw [ite_eq_left hlk]
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.cons_append, List.nil_append, cs_cons, cs_nil, litVal_Q,
      litVal_P, v_s1, v_s2, v_op, v_pad, or_false, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      decide_eq_true_eq, beq_iff_eq]
    by_cases hp : M.pad n j
    · exact Or.inr (Or.inr (Or.inl hp))
    · have := hn.ord j hj hp
      omega
  · rw [ite_eq_right hlk]
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.append_nil, cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2,
      v_pad, or_false, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
    by_cases hp : M.pad n j
    · exact Or.inr (Or.inr hp)
    · have := hn.ord j hj hp
      omega

omit hn in
theorem s_fNot : ∀ c ∈ fNot n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, rfl⟩ := hc
  have := hv.not_eq j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq]
  omega

omit hv in
theorem s_fNotNot : ∀ c ∈ fNotNot n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fNotNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, i, hi, rfl⟩ := hc
  have := hn.notNot j hj i hi
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_op, v_s1, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  by_cases hj3 : M.op j = 3 <;> by_cases hi3 : M.op i = 3
  · exact Or.inr (Or.inr (this hj3 hi3))
  · exact Or.inr (Or.inl hi3)
  · exact Or.inl hj3
  · exact Or.inl hj3

omit hv in
theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hn c h
  · exact s_fPad hn c h
  · exact s_fPre hn c h
  · exact s_fPadRd hn c h
  · exact s_fOrd hn c h
  · exact s_fUsed hn c h
  · exact s_fNot hv c h
  · exact s_fNotNot hn c h

end sound

section circuit
def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | .not, a :: _ => (3, nm n j a, nm n j a)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 4 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_not (n : ℕ) (g : Gate) (j : ℕ) (h : (code n g j).1 = 3) :
    (code n g j).2.1 = (code n g j).2.2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [code]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [ite_eq_left h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [ite_eq_right h6, ite_eq_left hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, ite_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : FanInTwo C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  not_eq j _ h := code_not n _ j h
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, ite_eq_left hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, ite_eq_left h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (_hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [ite_eq_right h6, ite_eq_left (show k < n + d by omega), ite_eq_right (show ¬ k + 1 < n by omega),
        ite_eq_left (show k + 1 < n + (i + 1) by omega), ite_eq_left h7, mv,
        ite_eq_right (show ¬ k + 1 - n = 0 by omega), ite_eq_left (show k + 1 - n ≤ d by omega)]
      congr 1; omega
    · simp only [ite_eq_right h6, ite_eq_left (show k < n + d by omega), ite_eq_right (show ¬ k + 1 < n by omega),
        ite_eq_right (show ¬ k + 1 < n + (i + 1) by omega), ite_eq_right h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [ite_eq_right h6, ite_eq_left h7, ite_eq_right (show ¬ k + 1 < n by omega),
        ite_eq_left (show k + 1 < n + j by omega), ite_eq_left (show k < n + j by omega), mv,
        ite_eq_right (show ¬ k + 1 - n = 0 by omega), ite_eq_left (show k + 1 - n ≤ d by omega)]
      congr 1; omega
    · simp only [ite_eq_right h6, ite_eq_right h7]
      by_cases h8 : k < n + j
      · simp only [ite_eq_left h8, mv, ite_eq_right (show ¬ k - n = 0 by omega),
          ite_eq_right (show ¬ k - n ≤ d by omega)]
      · simp only [ite_eq_right h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [ite_eq_left hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [ite_eq_right (show ¬ k < n by omega), ite_eq_left (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [ite_eq_right (show ¬ t = 0 by omega), ite_eq_right (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [ite_eq_right h6, ite_eq_left (show t - 2 < n + j by omega), ite_eq_left hc]
  · rw [ite_eq_right hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  not_eq j hj h3 := by
    simp only [mv] at h3 ⊢
    by_cases h0 : j = 0
    · rw [ite_eq_left h0] at h3; omega
    · by_cases h1 : j ≤ d
      · simp only [ite_eq_right h0, ite_eq_left h1] at h3 ⊢
        rw [hv.not_eq (j - 1) (by omega) h3]
      · simp only [ite_eq_right h0, ite_eq_right h1] at h3 ⊢
        rw [hv.not_eq j hj h3]
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, ite_eq_right h0, ite_eq_left h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, ite_eq_right h0, ite_eq_right h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, ite_eq_right (show ¬ i + 1 = 0 by omega), ite_eq_left (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, ite_eq_right (show ¬ j = 0 by omega), ite_eq_right (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  not_eq i hi h3 := by
    have := hv.not_eq i hi h3
    simp only [sw]; split_ifs with h
    · subst h; exact this.symm
    · exact this
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      by_cases h3 : M.op i = 3
      · rw [this, hv.not_eq i hi h3]
      · rw [this]; unfold gfun
        simp only [ite_eq_right h3]
        split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

omit hv hj in
theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgt true fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgt false fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_triv hv hj (by omega)

theorem notnot_triv {i : ℕ} (hi : i < j) (h3 : M.op j = 3) (hi3 : M.op i = 3)
    (he : M.s1 j = n + i) : ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hle := hv.s1_le i (by omega)
  refine copy_tgt (k := if M.s1 i < n + i then M.s1 i else n + j) (by split_ifs <;> omega)
    fun r hr => ?_
  have e1 : M.sv n j (n + i) r = M.w i r := by
    unfold Model.sv
    simp only [ite_eq_right (show ¬ n + i < n by omega), ite_eq_left (show n + i < n + j by omega),
      show n + i - n = i by omega]
  rw [hv.w_eq j hj r hr, h3, he, e1, hv.w_eq i (by omega) r hr, hi3]
  simp only [gfun, show ¬ (3 : ℕ) = 0 by omega, show ¬ (3 : ℕ) = 1 by omega, ite_true, ite_false,
    Bool.not_not]
  unfold Model.sv
  by_cases h6 : M.s1 i < n + i
  · simp only [ite_eq_left h6]
    by_cases h7 : M.s1 i < n
    · simp [h7]
    · simp only [ite_eq_right h7, ite_eq_left (show M.s1 i < n + j by omega)]
  · simp only [ite_eq_right h6, ite_eq_right (show ¬ M.s1 i < n by omega), ite_eq_right (show ¬ n + j < n by omega),
      ite_eq_right (show ¬ n + j < n + j by omega)]

theorem same_src (h3 : M.op j ≠ 3) (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  simp only [ite_eq_right h3]
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (4 * (n + s + 1)) + M.s2 j * 4 + M.op j

def lexB (n s : ℕ) : ℕ := 4 * (n + s + 1) * (n + s + 1)

theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 4 + z1 < K) (hz : z1 < 4)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 4 + z1 < x2 * K + y2 * 4 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (4 * (n + s + 1)) ≤ (n + s) * (4 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (4 * (n + s + 1)) + 4 * (n + s + 1) = 4 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (4 * (n + s + 1)) ≤ M.s1 j * (4 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model where
  op i := if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i
  s1 i := if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i
  s2 i := if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i
  so := tsw n j M.so
  w i r := if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [ite_eq_right h6, ite_eq_left (show k < n + i by omega), ite_eq_left (show k < n + i' by omega),
      xsw, ite_eq_right (show k - n ≠ j by omega), ite_eq_right (show k - n ≠ j + 1 by omega)]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [ite_eq_right h6, ite_eq_left h7, xsw, ite_eq_right (show k - n ≠ j by omega),
        ite_eq_right (show k - n ≠ j + 1 by omega)]
    · simp only [ite_eq_right h6, ite_eq_right h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [↓reduceIte]
    unfold Model.sv
    simp only [ite_eq_right (show ¬ n + j + 1 < n by omega), ite_eq_left (show n + j + 1 < n + i by omega),
      ite_eq_right (show ¬ n + j < n by omega), ite_eq_left (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      ite_eq_right (show j + 1 ≠ j by omega), ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [ite_eq_right h1, ↓reduceIte]
      unfold Model.sv
      simp only [ite_eq_right (show ¬ n + j + 1 < n by omega), ite_eq_left (show n + j + 1 < n + i by omega),
        ite_eq_right (show ¬ n + j < n by omega), ite_eq_left (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, ↓reduceIte]
    · simp only [ite_eq_right h1, ite_eq_right h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [ite_eq_right h6, ite_eq_left h7, xsw, ite_eq_right (show k - n ≠ j by omega),
            ite_eq_right (show k - n ≠ j + 1 by omega)]
        · simp only [ite_eq_right h6, ite_eq_right h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) where
  op_lt i hi := by
    simp only [xsw]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  not_eq i hi h := by
    simp only [xsw] at h ⊢
    split_ifs at h ⊢ with a b c
    · exact hv.not_eq _ hj h
    · exact hv.not_eq _ (by omega) h
    · rw [hv.not_eq i hi h]
    · exact hv.not_eq i hi h
  s1_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  so_le := tsw_le (by omega) hv.so_le
  w_eq i hi r hr := by
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  out_eq r hr := by
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, ite_eq_right a, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, ite_eq_right a, ite_eq_right b, ite_eq_left c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, ite_eq_right a, ite_eq_right b, ite_eq_right c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (_hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨_b, _hb, rfl⟩ | ⟨_c', _hc', ⟨_d, _hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

section min_of
variable (Inv : Model → Prop)

theorem nf_of_min2_of {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hInv_mv : ∀ {M d t}, Valid n s g R M → Inv M → d < s → TgtOk n d t → Inv (mv n s M d t))
    (hInv_sw : ∀ {M j}, Valid n s g R M → Inv M → j < s → Inv (sw M j))
    (hv : Valid n s g R M) (hInv : Inv M)
    (hmin : ∀ M', Valid n s g R M' → Inv M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (hInv_mv hv hInv hd ht) (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by
      by_cases h1 : M.s1 j = n + j
      · exact Or.inl h1
      · exact Or.inr (by by_contra h2; exact hc ⟨h1, h2⟩)
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by
      by_cases h1 : M.s1 j = n + i
      · exact Or.inl h1
      · exact Or.inr (by by_contra h2; exact hc ⟨h1, h2⟩)
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [ite_eq_right (show ¬ n + i < n by omega), ite_eq_left (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i := by
    intro j hj i hi h3 hi3 he
    exact htriv j hj (fun hp => by have := hp.1; omega) (notnot_triv hv hj hi h3 hi3 he)
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j) := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj (fun h3 => hc (Or.inr ⟨h3, he⟩)) he)
    · exact hmin _ (valid_sw hv j) (hInv_sw hv hInv hj) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    notNot := notNot
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

theorem lex_of_min2_of {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hInv_mv : ∀ {M d t}, Valid n s g R M → Inv M → d < s → TgtOk n d t → Inv (mv n s M d t))
    (hInv_sw : ∀ {M j}, Valid n s g R M → Inv M → j < s → Inv (sw M j))
    (hInv_xsw : ∀ {M j}, Valid n s g R M → Inv M → j + 1 < s →
      M.s1 j < n + j → M.s2 j < n + j → M.s1 (j + 1) < n + j → M.s2 (j + 1) < n + j →
      Inv (xsw n M j))
    (hv : Valid n s g R M) (hInv : Inv M)
    (hmin : ∀ M', Valid n s g R M' → Inv M' → meas2 n s M' < meas2 n s M → False) :
    LexNF n s M := by
  have hnf := nf_of_min2_of Inv hInv_mv hInv_sw hv hInv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)
  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (hInv_xsw hv hInv hj h1 h2 h3 h4)
      (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 4 → y * 4 + z < 4 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [ite_eq_right h6, ite_eq_left hk, ite_eq_left (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [ite_eq_right (show ¬ n + j < n by omega), ite_eq_left (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (hInv_mv hv hInv hj ht) (meas2_mv hv hv' hj (Or.inl hnp1))
      · have q0 := hnf.ord j (by omega) hnp
        have q1 := hnf.ord (j + 1) hj hnp1
        have n0 := hv.not_eq j (by omega)
        have n1 := hv.not_eq (j + 1) hj
        have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

theorem exists_nf2_of {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop}
    (hInv_mv : ∀ {M d t}, Valid n s g R M → Inv M → d < s → TgtOk n d t → Inv (mv n s M d t))
    (hInv_sw : ∀ {M j}, Valid n s g R M → Inv M → j < s → Inv (sw M j))
    (hInv_xsw : ∀ {M j}, Valid n s g R M → Inv M → j + 1 < s →
      M.s1 j < n + j → M.s2 j < n + j → M.s1 (j + 1) < n + j → M.s2 (j + 1) < n + j →
      Inv (xsw n M j))
    (h : ∃ M, Valid n s g R M ∧ Inv M) :
    ∃ M, Valid n s g R M ∧ Inv M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ Inv M ∧ meas2 n s M = m := by
    obtain ⟨M, h1, h2⟩ := h
    exact ⟨_, M, h1, h2, rfl⟩
  obtain ⟨M, hv, hInv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → Inv M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h2 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, h2, rfl⟩
  exact ⟨M, hv, hInv, nf_of_min2_of Inv hInv_mv hInv_sw hv hInv hmin,
    lex_of_min2_of Inv hInv_mv hInv_sw hInv_xsw hv hInv hmin⟩

end min_of

def RawNot (n s : ℕ) (M : Model) : Prop :=
  ∀ j < s, M.op j = 3 → M.s1 j < n

theorem code_not_op (n : ℕ) (g : Gate) (j : ℕ) (h : (code n g j).1 = 3) :
    g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [code]

theorem rawNot_ofCirc {n s : ℕ} (C : Circuit)
    (hraw : ∀ g ∈ C.gates, g.op = GateOp.not → ∃ i < n, g.inputs = [i]) :
    RawNot n s (ofCirc n s C) := by
  intro j _ hop
  unfold ofCirc at hop ⊢
  dsimp only at hop ⊢
  by_cases hjl : j < C.gates.length
  · have hmem : gateAt C j ∈ C.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hjl]
      exact List.getElem_mem hjl
    have hop' := code_not_op n (gateAt C j) j hop
    obtain ⟨i, hi, hins⟩ := hraw (gateAt C j) hmem hop'
    cases hg : gateAt C j with
    | mk op ins =>
      rw [hg] at hop' hins
      dsimp only at hop' hins
      subst hop' hins
      simp [code, nm, show i < n + j by omega, hi]
  · have hga : gateAt C j = ⟨GateOp.and, []⟩ := by
      rw [gateAt, List.getD_eq_default _ _ (by omega)]
    rw [hga] at hop
    simp [code] at hop

theorem rawNot_mv {n s d t : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (_hv : Valid n s g R M) (hInv : RawNot n s M) (_hd : d < s) (_ht : TgtOk n d t) :
    RawNot n s (mv n s M d t) := by
  intro j hj hop
  simp only [mv] at hop ⊢
  by_cases h0 : j = 0
  · rw [ite_eq_left h0] at hop; omega
  · by_cases h1 : j ≤ d
    · rw [ite_eq_right h0, ite_eq_left h1] at hop ⊢
      have hlt := hInv (j - 1) (by omega) hop
      unfold phi
      rw [ite_eq_left hlt]
      exact hlt
    · rw [ite_eq_right h0, ite_eq_right h1] at hop ⊢
      have hlt := hInv j hj hop
      have hne : M.s1 j ≠ n + d := by omega
      unfold rd phi
      rw [ite_eq_right hne, ite_eq_left hlt]
      exact hlt

theorem rawNot_sw {n s j : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hv : Valid n s g R M) (hInv : RawNot n s M) (_hj : j < s) :
    RawNot n s (sw M j) := by
  intro i hi hop
  simp only [sw] at hop ⊢
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ← hv.not_eq _ hi hop]
    exact hInv _ hi hop
  · rw [ite_eq_right hij]
    exact hInv i hi hop

theorem rawNot_xsw {n s j : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (_hv : Valid n s g R M) (hInv : RawNot n s M) (hj : j + 1 < s)
    (_h1 : M.s1 j < n + j) (_h2 : M.s2 j < n + j)
    (_h3 : M.s1 (j + 1) < n + j) (_h4 : M.s2 (j + 1) < n + j) :
    RawNot n s (xsw n M j) := by
  intro i hi hop
  simp only [xsw] at hop ⊢
  by_cases a : i = j
  · rw [ite_eq_left a] at hop ⊢
    exact hInv (j + 1) hj hop
  · by_cases b : i = j + 1
    · rw [ite_eq_right a, ite_eq_left b] at hop ⊢
      exact hInv j (by omega) hop
    · by_cases c : j + 1 < i
      · rw [ite_eq_right a, ite_eq_right b] at hop
        rw [ite_eq_right a, ite_eq_right b, ite_eq_left c]
        have hlt := hInv i hi hop
        unfold tsw
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact hlt
      · rw [ite_eq_right a, ite_eq_right b] at hop
        rw [ite_eq_right a, ite_eq_right b, ite_eq_right c]
        exact hInv i hi hop

def rawOnly (n s : ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    (List.range (j + 1)).map fun k => [Q (ix n s 0 j 3), Q (ix n s 1 j (n + k))]

theorem rawOnly_sat {n s : ℕ} {M : Model} (hInv : RawNot n s M) :
    ∀ c ∈ rawOnly n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [rawOnly, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, _hk, rfl⟩ := hc
  rw [cs_cons, cs_cons, cs_nil, or_false, litVal_Q, litVal_Q]
  rw [v_op M (by omega) (wd_lt1 (by omega)), v_s1 M (by omega) (wd_lt1 (by omega))]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
  by_cases hop : M.op j = 3
  · have := hInv j hj hop
    exact Or.inr (by omega)
  · exact Or.inl hop

def NotCap (s bound : ℕ) (M : Model) : Prop :=
  ((Finset.range s).filter fun j => M.op j = 3).card ≤ bound

theorem card_range_filter_list (L : List Gate) (P : Gate → Bool) :
    ((Finset.range L.length).filter fun j =>
      (L[j]?.map P).getD false = true).card = (L.filter P).length := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have hr : Finset.range (gs.length + 1) = insert gs.length (Finset.range gs.length) := by
      ext k; simp only [Finset.mem_insert, Finset.mem_range]; omega
    rw [List.length_append, List.length_singleton, hr, Finset.filter_insert,
      List.filter_append, List.filter_singleton, List.length_append]
    have hprev : ∀ j ∈ Finset.range gs.length,
        ((gs ++ [g])[j]?.map P).getD false = (gs[j]?.map P).getD false := by
      intro j hj
      have hlt : j < gs.length := Finset.mem_range.mp hj
      simp [List.getElem?_append_left hlt]
    have hfeq : (Finset.range gs.length).filter (fun j => ((gs ++ [g])[j]?.map P).getD false = true) =
        (Finset.range gs.length).filter (fun j => (gs[j]?.map P).getD false = true) := by
      ext j
      simp only [Finset.mem_filter]
      constructor <;> rintro ⟨hj, h⟩ <;> exact ⟨hj, by simp_all [hprev j hj]⟩
    by_cases hPg : P g = true
    · rw [ite_eq_left (by simp [hPg]), Finset.card_insert_of_notMem (by simp), hfeq, ih, hPg]
      simp
    · have hPg' : P g = false := Bool.eq_false_iff.mpr hPg
      rw [ite_eq_right (by simp [hPg]), hfeq, ih, hPg']
      simp

theorem notCap_ofCirc {n s bound : ℕ} (C : Circuit)
    (hcap : PEqualNP.NotBracket.notCount C ≤ bound) :
    NotCap s bound (ofCirc n s C) := by
  unfold NotCap
  let P : Gate → Bool := fun g => match g.op with | GateOp.not => true | _ => false
  have hsub : ((Finset.range s).filter fun j => (ofCirc n s C).op j = 3) ⊆
      (Finset.range C.gates.length).filter fun j => (C.gates[j]?.map P).getD false = true := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    rcases hj with ⟨hjs, hop⟩
    unfold ofCirc at hop
    dsimp only at hop
    by_cases hjl : j < C.gates.length
    · refine ⟨hjl, ?_⟩
      have hop' := code_not_op n (gateAt C j) j hop
      rw [gateAt, List.getD_eq_getElem _ _ hjl] at hop'
      rw [List.getElem?_eq_getElem hjl]
      simp [P, hop']
    · have hga : gateAt C j = ⟨GateOp.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      rw [hga] at hop
      simp [code] at hop
  have hcongr : ∀ {α : Type} (p q : α → Bool) (l : List α), (∀ x, p x = q x) →
      (l.filter p).length = (l.filter q).length := by
    intro α p q l h
    induction l with
    | nil => rfl
    | cons a t ih => simp only [List.filter_cons, h a]; cases q a <;> simp [ih]
  have dec_t : ∀ {p : Prop} (d : Decidable p), p → @decide p d = true := fun d hp => by
    cases d with
    | isTrue _ => rfl
    | isFalse hn => exact absurd hp hn
  have dec_f : ∀ {p : Prop} (d : Decidable p), ¬ p → @decide p d = false := fun d hn => by
    cases d with
    | isTrue hp => exact absurd hp hn
    | isFalse _ => rfl
  have hpq : (C.gates.filter P).length = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    apply hcongr
    intro ⟨op, ins⟩
    by_cases h : op = GateOp.not
    · subst h
      rw [dec_t _ rfl]
    · rw [dec_f _ h]
      dsimp only [P]
      cases op <;> first | exact absurd rfl h | rfl
  have hcard := (Finset.card_le_card hsub).trans_eq (card_range_filter_list C.gates P)
  exact hcard.trans (hpq ▸ hcap)

theorem notCap_mv {n s bound d t : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (_hv : Valid n s g R M) (hInv : NotCap s bound M) (_hd : d < s) (_ht : TgtOk n d t) :
    NotCap s bound (mv n s M d t) := by
  unfold NotCap at hInv ⊢
  have hinj : Finset.card ((Finset.range s).filter fun j => (mv n s M d t).op j = 3) ≤
      Finset.card ((Finset.range s).filter fun j => M.op j = 3) := by
    apply Finset.card_le_card_of_injOn (fun j => if j ≤ d then j - 1 else j)
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      rcases hj with ⟨hjs, hop⟩
      simp only [mv] at hop
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      dsimp only
      by_cases h0 : j = 0
      · rw [ite_eq_left h0] at hop; omega
      · by_cases h1 : j ≤ d
        · rw [ite_eq_right h0, ite_eq_left h1] at hop
          rw [ite_eq_left h1]
          exact ⟨by omega, hop⟩
        · rw [ite_eq_right h0, ite_eq_right h1] at hop
          rw [ite_eq_right h1]
          exact ⟨hjs, hop⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      rcases hj₁ with ⟨_, hop₁⟩
      rcases hj₂ with ⟨_, hop₂⟩
      simp only [mv] at hop₁ hop₂
      have h10 : j₁ ≠ 0 := by intro h; rw [ite_eq_left h] at hop₁; omega
      have h20 : j₂ ≠ 0 := by intro h; rw [ite_eq_left h] at hop₂; omega
      dsimp only at heq
      by_cases a1 : j₁ ≤ d <;> by_cases a2 : j₂ ≤ d
      · simp only [ite_eq_left a1, ite_eq_left a2] at heq; omega
      · simp only [ite_eq_left a1, ite_eq_right a2] at heq; omega
      · simp only [ite_eq_right a1, ite_eq_left a2] at heq; omega
      · simp only [ite_eq_right a1, ite_eq_right a2] at heq; exact heq
  exact hinj.trans hInv

theorem notCap_sw {n s bound j : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (_hv : Valid n s g R M) (hInv : NotCap s bound M) (_hj : j < s) :
    NotCap s bound (sw M j) := hInv

theorem notCap_xsw {n s bound j : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (_hv : Valid n s g R M) (hInv : NotCap s bound M) (hj : j + 1 < s)
    (_h1 : M.s1 j < n + j) (_h2 : M.s2 j < n + j)
    (_h3 : M.s1 (j + 1) < n + j) (_h4 : M.s2 (j + 1) < n + j) :
    NotCap s bound (xsw n M j) := by
  unfold NotCap at hInv ⊢
  have hinj : Finset.card ((Finset.range s).filter fun i => (xsw n M j).op i = 3) ≤
      Finset.card ((Finset.range s).filter fun i => M.op i = 3) := by
    apply Finset.card_le_card_of_injOn (fun i => if i = j then j + 1 else if i = j + 1 then j else i)
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      rcases hi with ⟨his, hop⟩
      simp only [xsw] at hop
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      dsimp only
      split_ifs with ha hb
      · rw [ite_eq_left ha] at hop; exact ⟨hj, hop⟩
      · rw [ite_eq_right ha, ite_eq_left hb] at hop; exact ⟨by omega, hop⟩
      · rw [ite_eq_right ha, ite_eq_right hb] at hop; exact ⟨his, hop⟩
    · intro i₁ _ i₂ _ heq
      dsimp only at heq
      split_ifs at heq <;> omega
  exact hinj.trans hInv

def capped (n s bound : ℕ) : List (List ℕ) :=
  (List.sublistsLen (bound + 1) (List.range s)).map fun js => js.map fun j => Q (ix n s 0 j 3)

theorem capped_sat {n s bound : ℕ} {M : Model} (hInv : NotCap s bound M) :
    ∀ c ∈ capped n s bound, ClauseSat (val n s M) c := by
  classical
  intro c hc
  simp only [capped, List.mem_map] at hc
  obtain ⟨js, hjs, rfl⟩ := hc
  obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hjs
  have hnd : js.Nodup := (List.nodup_range (n := s)).sublist hsub
  have hmem : ∀ j ∈ js, j < s := fun j hj => List.mem_range.mp (hsub.subset hj)
  have hex : ∃ j ∈ js, M.op j ≠ 3 := by
    by_contra hnot
    have hall : ∀ j ∈ js, M.op j = 3 := by
      intro j hj
      by_contra hne
      exact hnot ⟨j, hj, hne⟩
    have hsubF : js.toFinset ⊆ (Finset.range s).filter fun j => M.op j = 3 := by
      intro j hj
      rw [List.mem_toFinset] at hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hmem j hj), hall j hj⟩
    have hcard := Finset.card_le_card hsubF
    rw [List.toFinset_card_of_nodup hnd, hlen] at hcard
    unfold NotCap at hInv
    omega
  obtain ⟨j, hj_mem, hj_ne⟩ := hex
  apply cs_of_mem (List.mem_map.mpr ⟨j, hj_mem, rfl⟩)
  have hjs_lt := hmem j hj_mem
  rw [litVal_Q, v_op M (by omega) (wd_lt1 (by omega))]
  simpa using hj_ne

def repRow (n u v : ℕ) : ℕ := 2 ^ u + 2 ^ (n + v)

theorem repRow_testBit {n u : ℕ} (hu : u < n) (v i : ℕ) :
    (repRow n u v).testBit i = (decide (i = u) || decide (i = n + v)) := by
  have h : repRow n u v = 2 ^ (n + v) ||| 2 ^ u := by
    have := Nat.two_pow_add_eq_or_of_lt (i := n + v) (b := 2 ^ u)
      (Nat.pow_lt_pow_right (by decide) (by omega)) 1
    rw [mul_one] at this
    rw [← this, repRow, add_comm]
  rw [h, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, Bool.or_comm]
  congr 1 <;> exact decide_eq_decide.mpr eq_comm

theorem repRow_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    (List.ofFn fun i : Fin (n + m) => (repRow n u v).testBit i) = oneEach u v := by
  have hu := u.2
  apply List.ext_getElem
  · simp [oneEach]
  · intro i h1 h2
    rw [List.getElem_ofFn, repRow_testBit hu]
    simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
    split_ifs with h
    · have hne : ¬ i = n + (v : ℕ) := by omega
      simp [Fin.ext_iff, hne]
    · have hne : ¬ i = (u : ℕ) := by omega
      have hiff : i = n + (v : ℕ) ↔ i - n = (v : ℕ) := by omega
      simp [Fin.ext_iff, hne, hiff]

theorem repRow_lt {n m i j : ℕ} (hi : i < n) (hj : j < m) :
    repRow n i j < 2 ^ (n + m) := by
  refine Nat.lt_pow_two_of_testBit _ fun k hk => ?_
  rw [repRow_testBit hi]
  simp
  omega

theorem value_repRow (left right : ℕ) (mask : List ℕ) {i j : ℕ}
    (hi : i < left) (_hj : j < right) :
    (mask.getD (Nat.log2 (repRow left i j % 2 ^ left)) 0).testBit
      (Nat.log2 (repRow left i j / 2 ^ left)) = (mask.getD i 0).testBit j := by
  have hlt : 2 ^ i < 2 ^ left := Nat.pow_lt_pow_right (by decide) hi
  have hpos : 0 < 2 ^ left := by have := Nat.one_le_two_pow (n := left); omega
  have h1 : repRow left i j % 2 ^ left = 2 ^ i := by
    rw [repRow, pow_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have h2 : repRow left i j / 2 ^ left = 2 ^ j := by
    rw [repRow, pow_add, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
  rw [h1, h2, Nat.log2_two_pow, Nat.log2_two_pow]

end PEqualNP.Outside.L_lib_742_aux

theorem PEqualNP.Outside.L_lib_742 :
∀ (left right budget : ℕ) (mask : List ℕ),
  let n := left + right
  let s := budget
  let wd : ℕ := 2 ^ n + n + s + 2
  let ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd + a
  let P (v : ℕ) : ℕ := 2 * v + 2
  let Q (v : ℕ) : ℕ := 2 * v + 3
  let L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v
  let fOp : List (List ℕ) :=
    (List.range s).map fun j => [P (ix 0 j 0), P (ix 0 j 1), P (ix 0 j 2),
      P (ix 0 j 3)]
  let fSrcAlo : List (List ℕ) :=
    [1, 2].flatMap fun e => (List.range s).map fun j =>
      (List.range (n + j + 1)).map fun k => P (ix e j k)
  let srcEq (e j k r : ℕ) : List (List ℕ) :=
    if k < n then [[Q (ix e j k), L (ix (e + 3) j r) (r.testBit k)]]
    else if k < n + j then
      [[Q (ix e j k), Q (ix (e + 3) j r), P (ix 3 (k - n) r)],
       [Q (ix e j k), P (ix (e + 3) j r), Q (ix 3 (k - n) r)]]
    else [[Q (ix e j k), Q (ix (e + 3) j r)]]
  let fSrcEq (rows : List ℕ) : List (List ℕ) :=
    [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
      (List.range (n + j + 1)).flatMap fun k => srcEq e j k r
  let gateCl (j r : ℕ) : List (List ℕ) :=
    [[Q (ix 0 j 0), Q (ix 3 j r), P (ix 4 j r)],
     [Q (ix 0 j 0), Q (ix 3 j r), P (ix 5 j r)],
     [Q (ix 0 j 0), P (ix 3 j r), Q (ix 4 j r), Q (ix 5 j r)],
     [Q (ix 0 j 1), P (ix 3 j r), Q (ix 4 j r)],
     [Q (ix 0 j 1), P (ix 3 j r), Q (ix 5 j r)],
     [Q (ix 0 j 1), Q (ix 3 j r), P (ix 4 j r), P (ix 5 j r)],
     [Q (ix 0 j 2), P (ix 3 j r)],
     [Q (ix 0 j 3), P (ix 3 j r), P (ix 4 j r)],
     [Q (ix 0 j 3), Q (ix 3 j r), Q (ix 4 j r)]]
  let fGate (rows : List ℕ) : List (List ℕ) :=
    (List.range s).flatMap fun j => rows.flatMap fun r => gateCl j r
  let fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix 6 0 k)]
  let outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
    if k < n then (if r.testBit k = g r then [] else [[Q (ix 6 0 k)]])
    else if k < n + s then [[Q (ix 6 0 k), L (ix 3 (k - n) r) (g r)]]
    else if g r = true then [[Q (ix 6 0 k)]] else []
  let fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
    rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq g k r
  let fOut : List (List ℕ) :=
    if s = 0 then [] else [[P (ix 6 0 (n + s - 1)), P (ix 7 (s - 1) 0)]]
  let fPad : List (List ℕ) :=
    (List.range s).flatMap fun j =>
      [[Q (ix 7 j 0), P (ix 0 j 2)], [Q (ix 7 j 0), P (ix 1 j (n + j))],
       [Q (ix 7 j 0), P (ix 2 j (n + j))], [P (ix 7 j 0), Q (ix 0 j 2)],
       [P (ix 7 j 0), Q (ix 1 j (n + j))], [P (ix 7 j 0), Q (ix 2 j (n + j))]]
  let fPre : List (List ℕ) :=
    (List.range (s - 1)).map fun j => [Q (ix 7 (j + 1) 0), P (ix 7 j 0)]
  let fPadRd : List (List ℕ) :=
    (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
      [[Q (ix 7 i 0), Q (ix 1 j (n + i))], [Q (ix 7 i 0), Q (ix 2 j (n + i))]]
  let fNot : List (List ℕ) :=
    (List.range s).flatMap fun j => (List.range (n + j + 1)).map fun k =>
      [Q (ix 0 j 3), Q (ix 1 j k), P (ix 2 j k)]
  let fNotNot : List (List ℕ) :=
    (List.range s).flatMap fun j => (List.range j).map fun i =>
      [Q (ix 0 j 3), Q (ix 0 i 3), Q (ix 1 j (n + i))]
  let fOrd : List (List ℕ) :=
    (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
      (List.range (k + 1)).map fun l =>
        [Q (ix 1 j k), Q (ix 2 j l), P (ix 7 j 0)] ++
          if l = k then [P (ix 0 j 3)] else []
  let fUsed : List (List ℕ) :=
    (List.range (s - 1)).map fun j =>
      ((List.range (s - 1 - j)).map fun t => P (ix 1 (j + 1 + t) (n + j))) ++
      ((List.range (s - 1 - j)).map fun t => P (ix 2 (j + 1 + t) (n + j))) ++
        [P (ix 7 j 0)]
  let enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
    fOp ++ fSrcAlo ++ fSrcEq rows ++ fGate rows ++ fOutAlo ++
      fOutEq g rows ++ fOut ++ fPad ++ fPre ++ fPadRd ++ fOrd ++
      fUsed ++ fNot ++ fNotNot
  let lexBase (j : ℕ) : List ℕ :=
    [P (ix 7 j 0), P (ix 1 (j + 1) (n + j)), P (ix 2 (j + 1) (n + j))]
  let fLex : List (List ℕ) :=
    (List.range (s - 1)).flatMap fun j =>
      (List.range (n + j + 1)).flatMap fun a =>
        ((List.range a).map fun b => [Q (ix 1 j a), Q (ix 1 (j + 1) b)] ++ lexBase j) ++
        (List.range (n + j + 1)).flatMap fun c =>
          ((List.range c).map fun d =>
            [Q (ix 1 j a), Q (ix 1 (j + 1) a), Q (ix 2 j c), Q (ix 2 (j + 1) d)] ++
              lexBase j) ++
          [[Q (ix 1 j a), Q (ix 1 (j + 1) a), Q (ix 2 j c), Q (ix 2 (j + 1) c),
              Q (ix 0 j 1)] ++ lexBase j,
           [Q (ix 1 j a), Q (ix 1 (j + 1) a), Q (ix 2 j c), Q (ix 2 (j + 1) c),
              Q (ix 0 (j + 1) 0)] ++ lexBase j]
  let enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc g rows ++ fLex
  let rows := (List.range left).flatMap fun i =>
    (List.range right).map fun j => 2^i + 2^(left+j)
  let value := fun (r : ℕ) => (mask.getD (Nat.log2 (r % 2^left)) 0).testBit (Nat.log2 (r / 2^left))
  let base := enc2 value rows
  let rawOnly := (List.range s).flatMap fun j =>
    (List.range (j+1)).map fun k => [Q (ix 0 j 3), Q (ix 1 j (n+k))]
  let capped := fun (bound : ℕ) =>
    (List.sublistsLen (bound+1) (List.range s)).map fun js => js.map fun j => Q (ix 0 j 3)
  let graph := fun (u : Fin left) (v : Fin right) => (mask.getD u.val 0).testBit v.val
  (¬ PEqualNP.Defs.LratEncoding.FormulaSat (base ++ rawOnly) →
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ budget ∧
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ i < left + right, g.inputs = [i]) ∧
      PEqualNP.Represents.Represents graph C) ∧
    ∀ j : ℕ, ¬ PEqualNP.Defs.LratEncoding.FormulaSat (base ++ capped j) →
      ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
        C.size ≤ budget ∧ PEqualNP.NotBracket.notCount C ≤ j ∧
        PEqualNP.Represents.Represents graph C := by
  intro left right budget mask n s wd ix P Q L fOp fSrcAlo srcEq fSrcEq gateCl fGate
    fOutAlo outEq fOutEq fOut fPad fPre fPadRd fNot fNotNot fOrd fUsed enc lexBase fLex enc2
    rows value base rawOnly capped graph
  have hrows : ∀ r ∈ rows, r < 2 ^ n := by
    intro r hr
    simp only [rows, List.mem_flatMap, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, j, hj, rfl⟩ := hr
    exact PEqualNP.Outside.L_lib_742_aux.repRow_lt hi hj
  constructor
  · intro hU ⟨C, hC, hsz, hraw, hrep⟩
    have hsz' : C.gates.length ≤ s := hsz
    have hev : ∀ r, r ∈ rows → C.eval (PEqualNP.Outside.L_lib_742_aux.xr n r) = value r := by
      intro r hr
      simp only [rows, List.mem_flatMap, List.mem_map, List.mem_range] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := hr
      have heq := PEqualNP.Outside.L_lib_742_aux.repRow_eq ⟨i, hi⟩ ⟨j, hj⟩
      change C.eval (PEqualNP.Outside.L_lib_742_aux.xr (left + right)
        (PEqualNP.Outside.L_lib_742_aux.repRow left i j)) = _
      rw [PEqualNP.Outside.L_lib_742_aux.xr, heq, hrep ⟨i, hi⟩ ⟨j, hj⟩]
      exact (PEqualNP.Outside.L_lib_742_aux.value_repRow left right mask hi hj).symm
    have hv := PEqualNP.Outside.L_lib_742_aux.valid_ofCirc n s value (· ∈ rows) C hC hsz' hev
    have hr := PEqualNP.Outside.L_lib_742_aux.rawNot_ofCirc (s := s) C hraw
    obtain ⟨M, hvM, hrM, hnM, hlM⟩ := PEqualNP.Outside.L_lib_742_aux.exists_nf2_of
      (PEqualNP.Outside.L_lib_742_aux.RawNot n s)
      (fun hv' hInv hd ht => PEqualNP.Outside.L_lib_742_aux.rawNot_mv hv' hInv hd ht)
      (fun hv' hInv hj => PEqualNP.Outside.L_lib_742_aux.rawNot_sw hv' hInv hj)
      (fun hv' hInv hj h1 h2 h3 h4 =>
        PEqualNP.Outside.L_lib_742_aux.rawNot_xsw hv' hInv hj h1 h2 h3 h4)
      ⟨_, hv, hr⟩
    apply hU
    refine ⟨PEqualNP.Outside.L_lib_742_aux.val n s M, fun c hc => ?_⟩
    change c ∈ PEqualNP.Outside.L_lib_742_aux.enc2 n s value rows ++
      PEqualNP.Outside.L_lib_742_aux.rawOnly n s at hc
    rcases List.mem_append.mp hc with hc1 | hc2
    · exact PEqualNP.Outside.L_lib_742_aux.enc2_sat hrows hvM hnM hlM c hc1
    · exact PEqualNP.Outside.L_lib_742_aux.rawOnly_sat hrM c hc2
  · intro bound hU ⟨C, hC, hsz, hnot, hrep⟩
    have hsz' : C.gates.length ≤ s := hsz
    have hev : ∀ r, r ∈ rows → C.eval (PEqualNP.Outside.L_lib_742_aux.xr n r) = value r := by
      intro r hr
      simp only [rows, List.mem_flatMap, List.mem_map, List.mem_range] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := hr
      have heq := PEqualNP.Outside.L_lib_742_aux.repRow_eq ⟨i, hi⟩ ⟨j, hj⟩
      change C.eval (PEqualNP.Outside.L_lib_742_aux.xr (left + right)
        (PEqualNP.Outside.L_lib_742_aux.repRow left i j)) = _
      rw [PEqualNP.Outside.L_lib_742_aux.xr, heq, hrep ⟨i, hi⟩ ⟨j, hj⟩]
      exact (PEqualNP.Outside.L_lib_742_aux.value_repRow left right mask hi hj).symm
    have hv := PEqualNP.Outside.L_lib_742_aux.valid_ofCirc n s value (· ∈ rows) C hC hsz' hev
    have hcap := PEqualNP.Outside.L_lib_742_aux.notCap_ofCirc (n := n) (s := s) C hnot
    obtain ⟨M, hvM, hcM, hnM, hlM⟩ := PEqualNP.Outside.L_lib_742_aux.exists_nf2_of
      (PEqualNP.Outside.L_lib_742_aux.NotCap s bound)
      (fun hv' hInv hd ht => PEqualNP.Outside.L_lib_742_aux.notCap_mv hv' hInv hd ht)
      (fun hv' hInv hj => PEqualNP.Outside.L_lib_742_aux.notCap_sw hv' hInv hj)
      (fun hv' hInv hj h1 h2 h3 h4 =>
        PEqualNP.Outside.L_lib_742_aux.notCap_xsw hv' hInv hj h1 h2 h3 h4)
      ⟨_, hv, hcap⟩
    apply hU
    refine ⟨PEqualNP.Outside.L_lib_742_aux.val n s M, fun c hc => ?_⟩
    change c ∈ PEqualNP.Outside.L_lib_742_aux.enc2 n s value rows ++
      PEqualNP.Outside.L_lib_742_aux.capped n s bound at hc
    rcases List.mem_append.mp hc with hc1 | hc2
    · exact PEqualNP.Outside.L_lib_742_aux.enc2_sat hrows hvM hnM hlM c hc1
    · exact PEqualNP.Outside.L_lib_742_aux.capped_sat hcM c hc2
