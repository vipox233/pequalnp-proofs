import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25763

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Word := BitVec 1024

def lcolNat : ℕ → ℕ
  | 0 => 2 ^ 32 - 1
  | j + 1 => 2 ^ 32 * lcolNat j

def rcolNat (v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ v + 2 ^ 32 * rcolNat v k

def tcolNat : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + 2 ^ 32 * tcolNat rs

theorem bit_lcolNat {v : ℕ} (hv : v < 32) :
    ∀ (j u : ℕ), (lcolNat j).testBit (u * 32 + v) = decide (u = j) := by
  intro j
  induction j with
  | zero =>
    intro u
    cases u with
    | zero => simp only [lcolNat, Nat.testBit_two_pow_sub_one, Nat.zero_mul, Nat.zero_add]; simp [hv]
    | succ u =>
      simp only [lcolNat, Nat.testBit_two_pow_sub_one]
      have : 32 ≤ (u + 1) * 32 := Nat.le_mul_of_pos_left 32 (Nat.succ_pos u)
      simp; omega
  | succ j ih =>
    intro u
    rw [lcolNat, Nat.testBit_two_pow_mul]
    cases u with
    | zero => simp; omega
    | succ u =>
      have e : (u + 1) * 32 + v - 32 = u * 32 + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * 32 + v ≥ 32 := by rw [Nat.succ_mul]; omega
      simp only [ge_iff_le, g, decide_true, Bool.true_and, e, ih u]
      simp

theorem bit_rcolNat {v v' : ℕ} (hv : v < 32) (hv' : v' < 32) :
    ∀ (n u : ℕ), (rcolNat v n).testBit (u * 32 + v') = decide (u < n ∧ v' = v) := by
  intro n
  induction n with
  | zero => intro u; simp [rcolNat]
  | succ n ih =>
    intro u
    have hlt : 2 ^ v < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) hv
    rw [rcolNat, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or,
      Nat.testBit_two_pow_mul, Nat.testBit_two_pow]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v' ≥ 32) = false from decide_eq_false (by omega),
        Bool.false_and, Bool.false_or]
      by_cases h : v' = v
      · subst h; simp
      · simp only [Nat.succ_pos, true_and, h, decide_false]
        exact decide_eq_false (fun e => h e.symm)
    | succ u =>
      have e : (u + 1) * 32 + v' - 32 = u * 32 + v' := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * 32 + v' ≥ 32 := by rw [Nat.succ_mul]; omega
      have ne : v ≠ (u + 1) * 32 + v' := by rw [Nat.succ_mul]; omega
      simp only [g, decide_true, Bool.true_and, e, ih u, ne, decide_false, Bool.or_false]
      simp

theorem bit_tcolNat {v : ℕ} (hv : v < 32) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ 32) → ∀ u : ℕ,
      (tcolNat rows).testBit (u * 32 + v) = (rows.getD u 0).testBit v := by
  intro rows
  induction rows with
  | nil => intro _ u; simp [tcolNat]
  | cons r rs ih =>
    intro hr u
    have hr0 : r < 2 ^ 32 := hr r List.mem_cons_self
    rw [tcolNat, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hr0, Nat.testBit_or,
      Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v ≥ 32) = false from decide_eq_false (by omega),
        Bool.false_and, Bool.false_or]
      simp
    | succ u =>
      have e : (u + 1) * 32 + v - 32 = u * 32 + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * 32 + v ≥ 32 := by rw [Nat.succ_mul]; omega
      have hpow : 2 ^ 32 ≤ 2 ^ ((u + 1) * 32 + v) :=
        Nat.pow_le_pow_right (by omega) (by rw [Nat.succ_mul]; omega)
      have hz : r.testBit ((u + 1) * 32 + v) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hr0 hpow)
      simp only [g, decide_true, Bool.true_and, e,
        ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) u, hz,
        Bool.or_false, List.getD_cons_succ]

def inCols : List Word :=
  List.ofFn (fun i : Fin 32 => BitVec.ofNat 1024 (lcolNat i.val)) ++
  List.ofFn (fun j : Fin 32 => BitVec.ofNat 1024 (rcolNat j.val 32))

def observe (r : Fin 1024) (w : Word) : Bool := w.getLsbD r.val

def allBits (xs : List Word) : Word := xs.foldr (· &&& ·) (BitVec.allOnes 1024)
def anyBits (xs : List Word) : Word := xs.foldr (· ||| ·) 0

theorem allBitsCorrect (r : Fin 1024) (xs : List Word) :
    observe r (allBits xs) = (xs.map (observe r)).all id := by
  induction xs with
  | nil =>
    change (BitVec.allOnes 1024).getLsbD r.val = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true r.isLt
  | cons x xs ih =>
    change observe r (x &&& allBits xs) = (observe r x && (xs.map (observe r)).all id)
    exact (BitVec.getLsbD_and).trans (congrArg (fun b => observe r x && b) ih)

theorem anyBitsCorrect (r : Fin 1024) (xs : List Word) :
    observe r (anyBits xs) = (xs.map (observe r)).any id := by
  induction xs with
  | nil => simp [anyBits, observe]
  | cons x xs ih =>
    change observe r (x ||| anyBits xs) = (observe r x || (xs.map (observe r)).any id)
    exact (BitVec.getLsbD_or).trans (congrArg (fun b => observe r x || b) ih)

theorem observedRead (r : Fin 1024) (xs : List Word) (i : ℕ) :
    observe r (xs.getD i 0) = (xs.map (observe r)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe]

def packedGate (op : GateOp) (xs : List Word) : Word :=
  match op with
  | .and => allBits xs
  | .or => anyBits xs
  | .not => ~~~(xs.headD 0)
  | _ => 0

theorem gateMatches (r : Fin 1024) (g : Gate) (ws : List Word)
    (ops : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    observe r (packedGate g.op (g.inputs.map (fun i => ws.getD i 0))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe r)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i 0)).map (observe r) =
      g.inputs.map (fun i => (ws.map (observe r)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead r ws i
  rcases ops with h | h | h
  · rw [h]
    change observe r (allBits _) = _
    rw [allBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (anyBits _) = _
    rw [anyBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (~~~((g.inputs.map fun i => ws.getD i 0).headD 0)) = !_
    rw [← reads]
    simp only [List.headD_eq_getD, ← observedRead]
    simp [observe, r.isLt]

def packedRun : List Gate → List Word → List Word
  | [], ws => ws
  | g :: gs, ws => packedRun gs (ws ++ [packedGate g.op (g.inputs.map (fun i => ws.getD i 0))])

theorem runMatches (r : Fin 1024) (gs : List Gate) (ws : List Word)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (packedRun gs ws).map (observe r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (observe r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [packedRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches r g ws (ops g (by simp))]

theorem inCols_observe (u v : Fin 32) :
    inCols.map (observe ⟨u.val * 32 + v.val, by omega⟩) = oneEach u v := by
  simp only [inCols, oneEach, List.map_append, List.map_ofFn]
  congr 1
  · apply List.ofFn_inj.mpr
    funext i
    change (BitVec.ofNat 1024 (lcolNat i.val)).getLsbD (u.val * 32 + v.val) = decide (i = u)
    rw [BitVec.getLsbD_ofNat]
    have hlt : u.val * 32 + v.val < 1024 := by omega
    simp only [hlt, decide_true, Bool.true_and, bit_lcolNat v.isLt i.val u.val]
    simp [Fin.ext_iff, eq_comm]
  · apply List.ofFn_inj.mpr
    funext j
    change (BitVec.ofNat 1024 (rcolNat j.val 32)).getLsbD (u.val * 32 + v.val) = decide (j = v)
    rw [BitVec.getLsbD_ofNat]
    have hlt : u.val * 32 + v.val < 1024 := by omega
    simp only [hlt, decide_true, Bool.true_and, bit_rcolNat j.isLt v.isLt 32 u.val, u.isLt, true_and]
    simp [Fin.ext_iff, eq_comm]

theorem represents_of_packed (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ 32)
    (hfan : FanInTwo C)
    (hmatch : (packedRun C.gates inCols).getD C.output 0 = BitVec.ofNat 1024 (tcolNat rows)) :
    Represents (fun u v : Fin 32 => (rows.getD u.val 0).testBit v.val) C := by
  intro u v
  let r : Fin 1024 := ⟨u.val * 32 + v.val, by omega⟩
  have ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    intro g hg
    have := (hfan g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have h1 : observe r ((packedRun C.gates inCols).getD C.output 0) = C.eval (oneEach u v) := by
    rw [observedRead, runMatches r C.gates inCols ops, inCols_observe u v]
    rfl
  rw [← h1, hmatch]
  change (BitVec.ofNat 1024 (tcolNat rows)).getLsbD (u.val * 32 + v.val) = _
  rw [BitVec.getLsbD_ofNat]
  have hlt : u.val * 32 + v.val < 1024 := by omega
  simp only [hlt, decide_true, Bool.true_and]
  exact bit_tcolNat v.isLt rows hrows u.val

def targetRows : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

def codes : List (ℕ × ℕ × ℕ) := [
  (1,25,43), (1,47,54), (1,9,39), (1,6,10), (1,15,36), (1,8,40), (1,5,20), (1,13,33), (1,4,58), (1,3,41), (1,0,62), (1,28,36),
  (1,4,61), (1,1,42), (1,29,35), (1,28,50), (1,30,46), (1,19,52), (1,25,35), (1,44,52), (1,24,27), (1,18,37), (1,12,55), (1,21,48),
  (1,2,51), (1,2,18), (1,17,45), (1,26,32), (1,16,60), (1,10,23), (1,0,61), (1,21,64), (1,65,94), (1,34,74), (1,55,77), (1,11,80),
  (1,66,76), (1,68,82), (1,53,67), (1,15,79), (1,68,73), (1,54,70), (1,48,65), (1,62,69), (1,60,84), (1,72,95), (1,19,31), (1,110,90),
  (1,111,96), (1,18,38), (1,113,75), (1,114,83), (1,115,86), (1,116,102), (1,10,20), (1,118,57), (1,119,71), (1,120,78), (1,41,100), (1,122,103),
  (1,0,56), (1,124,75), (1,125,78), (1,126,92), (1,3,26), (1,128,57), (1,129,76), (1,130,98), (1,1,28), (1,132,46), (1,133,105), (1,134,109),
  (1,66,67), (1,136,88), (1,137,104), (1,6,14), (1,139,32), (1,140,45), (1,141,64), (1,142,87), (1,24,34), (1,144,69), (1,145,98), (1,14,39),
  (1,147,97), (1,148,102), (1,22,37), (1,150,69), (1,151,91), (1,152,92), (1,13,27), (1,154,89), (1,38,106), (1,31,59), (1,157,86), (1,158,100),
  (1,52,75), (1,160,105), (1,161,108), (1,14,71), (1,163,72), (1,164,81), (1,11,53), (1,166,91), (1,167,104), (1,83,99), (1,169,107), (1,67,95),
  (1,171,96), (1,45,63), (1,173,88), (1,174,93), (1,33,47), (1,176,58), (1,177,66), (1,178,70), (1,179,74), (1,9,78), (1,181,89), (1,182,106),
  (1,49,63), (1,184,109), (1,24,40), (1,186,90), (1,187,99), (1,42,81), (1,189,101), (1,26,50), (1,191,87), (1,192,108), (1,47,85), (1,194,93),
  (1,195,101), (1,9,24), (1,197,51), (1,198,52), (1,199,59), (1,200,85), (1,4,16), (1,202,42), (1,203,73), (1,204,107), (1,7,22), (1,206,59),
  (1,207,64), (1,208,97), (1,44,71), (1,210,77), (1,211,103), (0,112,117), (0,121,123), (0,127,131), (0,135,138), (0,143,146), (0,149,153), (0,155,156),
  (0,159,162), (0,165,168), (0,170,172), (0,175,180), (0,183,185), (0,188,190), (0,193,196), (0,201,205), (0,209,212), (1,228,227), (1,226,225), (1,224,223),
  (1,222,221), (1,220,219), (1,218,217), (1,216,215), (1,214,213), (1,229,230), (1,231,232), (1,233,234), (1,235,236), (1,237,238), (1,239,240), (1,241,242)]

def asGate (t : ℕ × ℕ × ℕ) : Gate :=
  ⟨if t.1 = 0 then .and else .or, [t.2.1, t.2.2]⟩

def witness : Circuit := ⟨codes.map asGate, 243⟩

theorem witnessFan : FanInTwo witness := by
  intro g hg
  obtain ⟨⟨o, a, b⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  by_cases h : o = 0 <;> simp [asGate, h]

set_option maxRecDepth 200000 in
theorem witnessSize : witness.size ≤ 180 := by
  decide +kernel

theorem witnessNotInput :
    ∀ g ∈ witness.gates, g.op = GateOp.not → ∃ i < 64, g.inputs = [i] := by
  intro g hg hnot
  obtain ⟨⟨o, a, b⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  by_cases h : o = 0 <;> simp [asGate, h] at hnot

theorem rowsBound : ∀ r ∈ targetRows, r < 2 ^ 32 := by
  intro r hr
  have h : targetRows.all (fun x => decide (x < 2 ^ 32)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

set_option maxRecDepth 200000 in
theorem wordsMatch :
    (packedRun witness.gates inCols).getD witness.output 0 = BitVec.ofNat 1024 (tcolNat targetRows) := by
  decide +kernel

theorem witnessRep :
    Represents (fun u v : Fin 32 => (targetRows.getD u.val 0).testBit v.val) witness :=
  represents_of_packed witness targetRows rowsBound witnessFan wordsMatch

end PEqualNP.Outside.L_meta_25763

theorem PEqualNP.Outside.L_meta_25763 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 180 ∧
  (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ i < 64, g.inputs = [i]) ∧
  PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_25763.witness, PEqualNP.Outside.L_meta_25763.witnessFan, PEqualNP.Outside.L_meta_25763.witnessSize, PEqualNP.Outside.L_meta_25763.witnessNotInput, PEqualNP.Outside.L_meta_25763.witnessRep⟩
