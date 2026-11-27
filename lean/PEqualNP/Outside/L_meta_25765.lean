import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25765_aux

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

def tab : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

def asGate (t : Bool × Nat × Nat) : Gate := ⟨if t.1 then .or else .and, [t.2.1,t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [
  (true,25,43),(true,47,54),(true,9,39),(true,6,10),(true,15,36),(true,8,40),(true,5,20),(true,13,33),
  (true,4,58),(true,3,41),(true,0,62),(true,28,36),(true,4,61),(true,1,42),(true,29,35),(true,28,50),
  (true,30,46),(true,19,52),(true,25,35),(true,44,52),(true,24,27),(true,18,37),(true,12,55),(true,21,48),
  (true,2,51),(true,2,18),(true,17,45),(true,26,32),(true,16,60),(true,10,23),(true,0,61),(true,21,64),
  (true,65,94),(true,34,74),(true,55,77),(true,11,80),(true,66,76),(true,68,82),(true,53,67),(true,15,79),
  (true,68,73),(true,54,70),(true,48,65),(true,62,69),(true,60,84),(true,72,95),(true,19,31),(true,110,90),
  (true,111,96),(true,18,38),(true,113,75),(true,114,83),(true,115,86),(true,116,102),(true,10,20),(true,118,57),
  (true,119,71),(true,120,78),(true,41,100),(true,122,103),(true,0,56),(true,124,75),(true,125,78),(true,126,92),
  (true,3,26),(true,128,57),(true,129,76),(true,130,98),(true,1,28),(true,132,46),(true,133,105),(true,134,109),
  (true,66,67),(true,136,88),(true,137,104),(true,6,14),(true,139,32),(true,140,45),(true,141,64),(true,142,87),
  (true,24,34),(true,144,69),(true,145,98),(true,14,39),(true,147,97),(true,148,102),(true,22,37),(true,150,69),
  (true,151,91),(true,152,92),(true,13,27),(true,154,89),(true,38,106),(true,31,59),(true,157,86),(true,158,100),
  (true,52,75),(true,160,105),(true,161,108),(true,14,71),(true,163,72),(true,164,81),(true,11,53),(true,166,91),
  (true,167,104),(true,83,99),(true,169,107),(true,67,95),(true,171,96),(true,45,63),(true,173,88),(true,174,93),
  (true,33,47),(true,176,58),(true,177,66),(true,178,70),(true,179,74),(true,9,78),(true,181,89),(true,182,106),
  (true,49,63),(true,184,109),(true,24,40),(true,186,90),(true,187,99),(true,42,81),(true,189,101),(true,26,50),
  (true,191,87),(true,192,108),(true,47,85),(true,194,93),(true,195,101),(true,9,24),(true,197,51),(true,198,52),
  (true,199,59),(true,200,85),(true,4,16),(true,202,42),(true,203,73),(true,204,107),(true,7,22),(true,206,59),
  (true,207,64),(true,208,97),(true,44,71),(true,210,77),(true,211,103),(false,112,117),(false,121,123),(false,127,131),
  (false,135,138),(false,143,146),(false,149,153),(false,155,156),(false,159,162),(false,165,168),(false,170,172),(false,175,180),
  (false,183,185),(false,188,190),(false,193,196),(false,201,205),(false,209,212),(true,228,227),(true,226,225),(true,224,223),
  (true,222,221),(true,220,219),(true,218,217),(true,216,215),(true,214,213),(true,229,230),(true,231,232),(true,233,234),
  (true,235,236),(true,237,238),(true,239,240),(true,241,242)]

def circ : Circuit := ⟨codes.map asGate, 243⟩

theorem mono : Monotone2 circ := by
  intro g hg
  obtain ⟨⟨o,a,b⟩,_,rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases o <;> simp [asGate]

theorem fan : FanInTwo circ := by
  intro g hg
  obtain ⟨⟨o,a,b⟩,_,rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases o <;> simp [asGate]

theorem hrows : ∀ r ∈ tab, r < 2 ^ 32 := by decide +kernel

theorem hg : aonB circ = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem hcol : ((pcols 10 circ 32 32).getD circ.output 0 == tcol 32 tab) = true := by decide +kernel

theorem rep : Represents (fun (u : Fin 32) (v : Fin 32) => (tab.getD u.val 0).testBit v.val) circ :=
  represents_of_pcols (n := 32) (m := 32) (N := 10) (by norm_num) circ tab hrows hg hcol
end PEqualNP.Outside.L_meta_25765_aux

open PEqualNP.Outside.L_meta_25765_aux in
theorem PEqualNP.Outside.L_meta_25765 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) 200) := by
  exact ⟨circ, mono, by decide +kernel, rep⟩
