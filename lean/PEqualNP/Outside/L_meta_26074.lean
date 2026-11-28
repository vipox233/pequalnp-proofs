import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26074
open PEqualNP.CircuitLowerBounds

abbrev Code := Bool × Nat × Nat

def asGate (c : Code) : Gate := ⟨if c.1 then .or else .and, [c.2.1, c.2.2]⟩

def next (w : List Nat) (c : Code) : Nat :=
  let a := w.getD c.2.1 0
  let b := w.getD c.2.2 0
  if c.1 then a ||| b else a &&& b

def run (cs : List Code) (w : List Nat) : List Nat := cs.foldl (fun w c => w ++ [next w c]) w

theorem read_bit (w : List Nat) (i j : Nat) : (w.getD i 0).testBit j =
    (w.map (fun n => n.testBit j)).getD i false := by
  induction w generalizing i with
  | nil => simp
  | cons a t ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem next_bit (w : List Nat) (j : Nat) (c : Code) :
    (next w c).testBit j = (asGate c).op.eval ((asGate c).inputs.map fun i =>
      (w.map (fun n => n.testBit j)).getD i false) := by
  obtain ⟨b,i,k⟩ := c
  cases b <;> simp only [next, asGate, Bool.false_eq_true, ite_false, ite_true, List.map_cons,
    List.map_nil, GateOp.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil, id_eq,
    Nat.testBit_and, Nat.testBit_or, Bool.and_true, Bool.or_false, read_bit]

theorem run_bits (j : Nat) (cs : List Code) (w : List Nat) :
    (run cs w).map (fun n => n.testBit j) = (cs.map asGate).foldl (fun s g =>
      s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) (w.map (fun n => n.testBit j)) := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih =>
    change (run cs (w ++ [next w c])).map _ = _
    rw [ih, List.map_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, next_bit]

def pack : List Nat → Nat
  | [] => 0
  | r :: rs => r ||| (pack rs <<< 32)

theorem packed_bit (v : Fin 32) : ∀ (rows : List Nat), (∀ r ∈ rows, r < 2 ^ 32) →
    ∀ u : Nat, (pack rows).testBit (32 * u + v.val) = (rows.getD u 0).testBit v.val := by
  intro rows
  induction rows with
  | nil => simp [pack]
  | cons r rs ih =>
    intro small u
    have hs := small r List.mem_cons_self
    have ht := fun z hz => small z (List.mem_cons_of_mem _ hz)
    cases u with
    | zero => simp [pack, Nat.testBit_shiftLeft, Nat.not_le.mpr v.isLt]
    | succ u =>
      have lo : 32 ≤ 32 * (u+1) + v.val := by omega
      have z : r.testBit (32 * (u+1) + v.val) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) lo))
      have sub : 32 * (u+1) + v.val - 32 = 32 * u + v.val := by omega
      simp only [pack, Nat.testBit_or, Nat.testBit_shiftLeft, lo, decide_true, Bool.true_and,
        z, Bool.false_or, sub, List.getD_cons_succ, ih ht u]

def leftRows (i : Fin 32) := List.ofFn (fun u : Fin 32 => if i = u then (2^32-1 : Nat) else 0)

def rightRows (j : Fin 32) := List.replicate 32 (2^j.val)

def bank := List.ofFn (fun i => pack (leftRows i)) ++ List.ofFn (fun j => pack (rightRows j))

theorem leftBits (i u v : Fin 32) : (pack (leftRows i)).testBit (32*u.val+v.val) = decide (i=u) := by
  rw [packed_bit v (leftRows i) (by intro r h; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h; split <;> norm_num)]
  rw [List.getD_eq_getElem _ _ (by simp [leftRows])]
  simp only [leftRows, List.getElem_ofFn]
  by_cases h : i = u
  · simp only [h, ite_true, decide_true, Nat.testBit_two_pow_sub_one, v.isLt]
  · simp [h]

theorem rightBits (j u v : Fin 32) : (pack (rightRows j)).testBit (32*u.val+v.val) = decide (j=v) := by
  have hw : ∀ r ∈ rightRows j, r < 2^32 := by
    intro r hr
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hr
    exact Nat.pow_lt_pow_right (by norm_num) j.isLt
  rw [packed_bit v _ hw, List.getD_eq_getElem _ _ (by simp [rightRows])]
  simp only [rightRows, List.getElem_replicate, Nat.testBit_two_pow, Fin.ext_iff]

theorem bank_bits (u v : Fin 32) : (bank.map (fun n => n.testBit (32*u.val+v.val))) =
    PEqualNP.Represents.oneEach u v := by
  simp only [bank, PEqualNP.Represents.oneEach, List.map_append, List.map_ofFn, Function.comp_def,
    leftBits, rightBits]

def tab : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

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

theorem shape : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  obtain ⟨⟨b,i,j⟩,_,rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

set_option maxRecDepth 16000 in
theorem gate_count : circ.size = 180 := by decide +kernel

set_option maxRecDepth 16000 in
theorem no_negations : PEqualNP.NotBracket.notCount circ = 0 := by decide +kernel

set_option maxRecDepth 16000 in
theorem table_ok : (run codes bank).getD 243 0 = pack tab := by decide +kernel

theorem represents : PEqualNP.Represents.Represents (fun u v : Fin 32 =>
    (tab.getD u.val 0).testBit v.val) circ := by
  intro u v
  have h := read_bit (run codes bank) 243 (32 * u.val + v.val)
  have small : ∀ r ∈ tab, r < 2^32 := by decide +kernel
  rw [table_ok, packed_bit v tab small, run_bits, bank_bits] at h
  exact h.symm

end PEqualNP.Outside.L_meta_26074

theorem PEqualNP.Outside.L_meta_26074 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 180 ∧
  PEqualNP.NotBracket.notCount C ≤ 1 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C) := by
  exact ⟨PEqualNP.Outside.L_meta_26074.circ, PEqualNP.Outside.L_meta_26074.shape, PEqualNP.Outside.L_meta_26074.gate_count.le,
    PEqualNP.Outside.L_meta_26074.no_negations.le.trans (Nat.zero_le _), PEqualNP.Outside.L_meta_26074.represents⟩
