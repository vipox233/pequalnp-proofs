import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50123

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W := BitVec 6

def roots : List W := [62, 60, 56, 48, 32, 0, 63]

def lacks (t : W) (s : List W) : Nat :=
  if s.contains t then 0 else 1

def missing (s : List W) : Nat := lacks 16 s + lacks 22 s + lacks 28 s

theorem lacks_cons (t : W) (s : List W) (z : W) :
    lacks t (z :: s) = if t = z then 0 else lacks t s := by
  by_cases h : t = z <;> simp [lacks, h]

theorem missing_cons (s : List W) (z : W) : missing s ≤ missing (z :: s) + 1 := by
  have h (i : W) : lacks i s ≤ 1 := by unfold lacks; split <;> decide
  have a := h 16
  have b := h 22
  have c := h 28
  simp only [missing, lacks_cons]
  split_ifs <;> first | omega | (subst_vars; contradiction)

def binOptions (s : List W) : List W :=
  ((s.flatMap fun a => s.flatMap fun b => [a &&& b, a ||| b]).filter
    (fun z => !s.contains z)).eraseDups

def negOptions (s : List W) : List W := (s.map (fun a => ~~~a)).filter (fun z => !s.contains z)

theorem in_bin {s : List W} {a b z : W} (ha : a ∈ s) (hb : b ∈ s)
    (hop : z = a &&& b ∨ z = a ||| b) (hf : z ∉ s) : z ∈ binOptions s := by
  simp only [binOptions, List.mem_filter, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, Bool.not_eq_true']
  exact ⟨⟨a, ha, b, hb, hop⟩, by simpa using hf⟩

theorem in_neg {s : List W} {a : W} (ha : a ∈ s) (hf : ~~~a ∉ s) :
    ~~~a ∈ negOptions s := by
  simp [negOptions, hf, ha]

def scan : Nat → Nat → List W → Bool
  | 0, _, s => missing s == 0
  | k+1, n, s =>
    if missing s = 0 then true else if missing s > k+1 then false else
    scan k n s || (binOptions s).any (fun z => scan k n (z :: s)) ||
      (n != 0 && (negOptions s).any (fun z => scan k (n-1) (z :: s)))

theorem scan_bound (k : Nat) : ∀ (n : Nat) (s : List W), scan k n s = true → missing s ≤ k := by
  induction k with
  | zero =>
    intro n s h
    simp [scan] at h
    omega
  | succ k ih =>
    intro n s h
    rw [scan] at h
    split at h
    · omega
    · split at h
      · simp at h
      · omega

theorem scan_done {k n : Nat} {s : List W} (h : missing s = 0) : scan k n s = true := by
  cases k <;> simp [scan, h]

theorem scan_of {k n : Nat} {s : List W} (hm : missing s ≤ k+1)
    (h : scan k n s = true ∨ (∃ z ∈ binOptions s, scan k n (z :: s) = true) ∨
      (n ≠ 0 ∧ ∃ z ∈ negOptions s, scan k (n-1) (z :: s) = true)) :
    scan (k+1) n s = true := by
  rw [scan]
  split
  · rfl
  · rw [ite_eq_right (Nat.not_lt.mpr hm)]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, bne_iff_ne]
    rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h

theorem scan_skip {k n : Nat} {s : List W} (h : scan k n s = true) : scan (k+1) n s = true :=
  scan_of (Nat.le_succ_of_le (scan_bound k n s h)) (.inl h)

theorem scan_bin {k n : Nat} {s : List W} {z : W} (hz : z ∈ binOptions s)
    (h : scan k n (z :: s) = true) : scan (k+1) n s = true := by
  have a := scan_bound _ _ _ h
  have b := missing_cons s z
  exact scan_of (by omega) (.inr (.inl ⟨z, hz, h⟩))

theorem scan_neg {k n : Nat} {s : List W} {z : W} (hz : z ∈ negOptions s)
    (h : scan k n (z :: s) = true) : scan (k+1) (n+1) s = true := by
  have a := scan_bound _ _ _ h
  have b := missing_cons s z
  exact scan_of (by omega) (.inr (.inr ⟨Nat.succ_ne_zero n, z, hz, h⟩))

def bit (r : Fin 6) (z : W) : Bool := z[r.val]

def row (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]

theorem input_rows : ∀ r : Fin 6, roots.map (bit r) = row r := by
  decide +kernel

theorem target_row : ∀ z : W,
    ((∀ t : Fin 6, bit t z = (16 : Nat).testBit t.val) → z = 16) ∧
    ((∀ t : Fin 6, bit t z = (22 : Nat).testBit t.val) → z = 22) ∧
    ((∀ t : Fin 6, bit t z = (28 : Nat).testBit t.val) → z = 28) := by
  decide +kernel

theorem read_bit (w : List W) (i : ℕ) (k : Fin 6) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem read_mem {w s : List W} (hw : w ⊆ s) (h0 : 0 ∈ s) (i : Nat) : w.getD i 0 ∈ s := by
  by_cases h : i < w.length
  · apply hw
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_default w 0 (Nat.le_of_not_gt h)]
    exact h0

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def admissible (s : List W) (op : GateOp) (z : W) : Prop :=
  z ∈ s ∨ z ∈ binOptions s ∨ (op = GateOp.not ∧ z ∈ negOptions s)

theorem classify_bin {s : List W} (op : GateOp) {a b z : W} (ha : a ∈ s) (hb : b ∈ s)
    (hop : z = a &&& b ∨ z = a ||| b) : admissible s op z := by
  by_cases hf : z ∈ s
  · exact .inl hf
  · exact .inr (.inl (in_bin ha hb hop hf))

theorem classify_neg {s : List W} {a : W} (ha : a ∈ s) : admissible s .not (~~~a) := by
  by_cases hf : ~~~a ∈ s
  · exact .inl hf
  · exact .inr (.inr ⟨rfl, in_neg ha hf⟩)

theorem gate_word (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 63 ∈ s)
    (g : Gate) (hg : legal g) :
    ∃ z, admissible s g.op z ∧ ∀ r, step (w.map (bit r)) g = (w ++ [z]).map (bit r) := by
  have mem := read_mem hw h0
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨63, .inl h1, by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, .inl h0, by simp [step, GateOp.eval, bit]⟩
    · exact ⟨63, .inl h1, by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, .inl (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, .inl (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, classify_neg (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, classify_bin _ (mem i) (mem j) (.inl rfl), by
            simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, classify_bin _ (mem i) (mem j) (.inr rfl), by
            simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, classify_neg (mem i), by
            simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def finish (gs : List Gate) (w : List W) (p q u : Nat) : Prop :=
  ∀ t : Fin 6, let v := gs.foldl step (w.map (bit t))
    v.getD p false = (16 : Nat).testBit t.val ∧
    v.getD q false = (22 : Nat).testBit t.val ∧
    v.getD u false = (28 : Nat).testBit t.val

theorem lacks_zero {s : List W} {t : W} (h : t ∈ s) : lacks t s = 0 := by
  simp [lacks, h]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem compile (gs : List Gate) (p q u : Nat) (hg : ∀ g ∈ gs, legal g)
    (k n : Nat) (hl : gs.length ≤ k) (hn : (gs.filter isNot).length ≤ n)
    (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 63 ∈ s) (hf : finish gs w p q u) :
    scan k n s = true := by
  induction gs generalizing k n w s with
  | nil =>
    simp only [finish, List.foldl_nil, read_bit] at hf
    have a := (target_row _).1 (fun t => (hf t).1)
    have b := (target_row _).2.1 (fun t => (hf t).2.1)
    have c := (target_row _).2.2 (fun t => (hf t).2.2)
    have a' := read_mem hw h0 p
    have b' := read_mem hw h0 q
    have c' := read_mem hw h0 u
    rw [a] at a'
    rw [b] at b'
    rw [c] at c'
    refine scan_done ?_
    unfold missing
    rw [lacks_zero a', lacks_zero b', lacks_zero c']
  | cons g gs ih =>
    cases k with
    | zero => simp at hl
    | succ k =>
      have htail : ∀ g' ∈ gs, legal g' := fun g' h' => hg g' (by simp [h'])
      have hlen : gs.length ≤ k := by simpa using hl
      have hnum : (gs.filter isNot).length ≤ n := by
        have ht : (gs.filter isNot).length ≤ ((g :: gs).filter isNot).length := by
          cases he : isNot g <;> simp [he]
        exact ht.trans hn
      obtain ⟨z, hz, heval⟩ := gate_word w s hw h0 h1 g (hg g (by simp))
      have hfin : finish gs (w ++ [z]) p q u := by
        intro r
        simpa only [finish, List.foldl_cons, heval] using hf r
      have old (hz : z ∈ s) : w ++ [z] ⊆ s := by simpa using And.intro hw hz
      have new : w ++ [z] ⊆ z :: s := by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact List.mem_cons_of_mem _ (hw h)
        · exact List.mem_cons.mpr (.inl (by simpa using h))
      rcases hz with hz | hz | ⟨hop, hz⟩
      · exact scan_skip (ih htail k n hlen hnum _ _ (old hz) h0 h1 hfin)
      · exact scan_bin hz (ih htail k n hlen hnum _ _ new (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin)
      · have he : isNot g = true := by simp [isNot, hop]
        simp [he] at hn
        cases n with
        | zero => omega
        | succ n => exact scan_neg hz (ih htail k n hlen (by omega) _ _ new (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem no_five : scan 5 2 roots = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_50123

open PEqualNP.Outside.L_meta_50123 in
theorem PEqualNP.Outside.L_meta_50123 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (16 : Nat).testBit t.val ∧
    w.getD q.val false = (22 : Nat).testBit t.val ∧
    w.getD r.val false = (28 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hg, _, hn, hs, hw⟩
  have hf : finish D.gates roots p.val q.val r.val := by
    intro t
    have h := hw t
    change let v := D.wires (roots.map (bit t)); _
    rw [input_rows]
    exact h
  have hg' : ∀ g ∈ D.gates, legal g := by
    intro g hm
    have h := hg g hm
    exact h
  have hn' : (D.gates.filter isNot).length ≤ 2 := by
    refine le_of_eq_of_le ?_ hn
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    obtain ⟨op, args⟩ := g
    cases op <;> simp [isNot]
  have h :=compile D.gates p.val q.val r.val hg' 5 2 hs hn' roots roots
    (fun _ h => h) (by decide +kernel) (by decide +kernel) hf
  exact Bool.false_ne_true (no_five.symm.trans h)
