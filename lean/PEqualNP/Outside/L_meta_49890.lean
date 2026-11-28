import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

-- Adapted from lean/PEqualNP/Outside/L_meta_42704.lean at
-- cc6e9805152cac493332da6f7c43ea4cc75d1bb9. The simulation is unchanged in structure;
-- five-row truth words and exact target masks replace eight-row cover classifications.
namespace PEqualNP.Outside.L_meta_49890_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W := BitVec 5

def roots : List W := [30, 28, 24, 16, 0, 31]

def kind (z : W) : Nat :=
  if z = 9 then 1 else if z = 12 then 2 else if z = 14 then 3 else 0

def lacks (k : Nat) (s : List W) : Nat :=
  if s.any (fun w => kind w == k) then 0 else 1

def missing (s : List W) : Nat := lacks 1 s + lacks 2 s + lacks 3 s

theorem lacks_cons (i : Nat) (s : List W) (z : W) :
    lacks i (z :: s) = if kind z = i then 0 else lacks i s := by
  by_cases h : kind z = i <;> simp [lacks, h]

theorem missing_cons (s : List W) (z : W) : missing s ≤ missing (z :: s) + 1 := by
  have h (i : Nat) : lacks i s ≤ 1 := by unfold lacks; split <;> decide
  have a := h 1
  have b := h 2
  have c := h 3
  simp only [missing, lacks_cons]
  split_ifs <;> omega

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

inductive Play : Nat → Nat → List W → Prop
  | done {k n s} (h : missing s = 0) : Play k n s
  | skip {k n s} (h : Play k n s) : Play (k+1) n s
  | bin {k n s z} (hz : z ∈ binOptions s) (h : Play k n (z :: s)) : Play (k+1) n s
  | neg {k n s z} (hz : z ∈ negOptions s) (h : Play k n (z :: s)) : Play (k+1) (n+1) s

theorem Play.bound {k n s} (h : Play k n s) : missing s ≤ k := by
  induction h with
  | done h => omega
  | skip h ih => omega
  | @bin k n s z _ _ ih => have := missing_cons s z; omega
  | @neg k n s z _ _ ih => have := missing_cons s z; omega

def scan : Nat → Nat → List W → Bool
  | 0, _, s => missing s == 0
  | k+1, n, s =>
    if missing s = 0 then true else if missing s > k+1 then false else
      scan k n s || (binOptions s).any (fun z => scan k n (z :: s)) ||
        (n != 0 && (negOptions s).any (fun z => scan k (n-1) (z :: s)))

theorem Play.scan_true {k n s} (h : Play k n s) : scan k n s = true := by
  induction h with
  | @done k n s h => cases k <;> simp [scan, h]
  | @skip k n s h ih =>
    have hb := (Play.skip h).bound
    simp [scan, Nat.not_lt.mpr hb, ih]
  | @bin k n s z hz h ih =>
    have hb := (Play.bin hz h).bound
    have ha := List.any_eq_true.mpr (⟨z, hz, ih⟩ : ∃ z ∈ binOptions s, scan k n (z :: s) = true)
    simp [scan, Nat.not_lt.mpr hb, ha]
  | @neg k n s z hz h ih =>
    have hb := (Play.neg hz h).bound
    have ha := List.any_eq_true.mpr (⟨z, hz, ih⟩ : ∃ z ∈ negOptions s, scan k n (z :: s) = true)
    simp [scan, Nat.not_lt.mpr hb, ha]

def bit (t : Fin 5) (z : W) : Bool := z[t.val]

theorem input_rows : ∀ t : Fin 5, roots.map (bit t) =
    (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true] := by
  decide +kernel

theorem first_row : ∀ z : W, (∀ t : Fin 5, bit t z = (9 : Nat).testBit t.val) → kind z = 1 := by
  decide +kernel

theorem second_row : ∀ z : W, (∀ t : Fin 5, bit t z = (12 : Nat).testBit t.val) → kind z = 2 := by
  decide +kernel

theorem third_row : ∀ z : W, (∀ t : Fin 5, bit t z = (14 : Nat).testBit t.val) → kind z = 3 := by
  decide +kernel

theorem read_bit (w : List W) (i : ℕ) (k : Fin 5) :
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
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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

theorem gate_word (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 31 ∈ s)
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
    · exact ⟨31, .inl h1, by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, .inl h0, by simp [step, GateOp.eval, bit]⟩
    · exact ⟨31, .inl h1, by simp [step, GateOp.eval, bit]; decide⟩
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

def finish (gs : List Gate) (w : List W) (p q r : Nat) : Prop :=
  ∀ t : Fin 5, let v := gs.foldl step (w.map (bit t))
    v.getD p false = (9 : Nat).testBit t.val ∧
    v.getD q false = (12 : Nat).testBit t.val ∧
    v.getD r false = (14 : Nat).testBit t.val

theorem lacks_zero {s : List W} {z : W} {i : Nat} (h : z ∈ s) (hi : kind z = i) : lacks i s = 0 := by
  have ht : s.any (fun w => kind w == i) = true := List.any_eq_true.mpr ⟨z, h, by simp [hi]⟩
  simp [lacks, ht]

def isNot (g : Gate) : Bool := @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)

theorem compile (gs : List Gate) (p q r : Nat) (hg : ∀ g ∈ gs, legal g)
    (k n : Nat) (hl : gs.length ≤ k) (hn : (gs.filter isNot).length ≤ n)
    (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 31 ∈ s) (hf : finish gs w p q r) :
    Play k n s := by
  induction gs generalizing k n w s with
  | nil =>
    simp only [finish, List.foldl_nil, read_bit] at hf
    have first := first_row _ (fun t => (hf t).1)
    have second := second_row _ (fun t => (hf t).2.1)
    have third := third_row _ (fun t => (hf t).2.2)
    exact .done (by simp [missing, lacks_zero (read_mem hw h0 p) first,
      lacks_zero (read_mem hw h0 q) second, lacks_zero (read_mem hw h0 r) third])
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
      have hfin : finish gs (w ++ [z]) p q r := by
        intro r
        simpa only [finish, List.foldl_cons, heval] using hf r
      have old (hz : z ∈ s) : w ++ [z] ⊆ s := by simpa using And.intro hw hz
      have new : w ++ [z] ⊆ z :: s := by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact List.mem_cons_of_mem _ (hw h)
        · exact List.mem_cons.mpr (.inl (by simpa using h))
      rcases hz with hz | hz | ⟨hop, hz⟩
      · exact .skip (ih htail k n hlen hnum _ _ (old hz) h0 h1 hfin)
      · exact .bin hz (ih htail k n hlen hnum _ _ new (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin)
      · have he : isNot g = true := by simp [isNot, hop]
        simp [he] at hn
        cases n with
        | zero => omega
        | succ n => exact .neg hz (ih htail k n hlen (by omega) _ _ new (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin)

set_option maxHeartbeats 16000000 in
theorem scan_false : scan 5 2 roots = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_49890_aux

open PEqualNP.Outside.L_meta_49890_aux in
theorem PEqualNP.Outside.L_meta_49890 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (9 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (14 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hg, _, hn, hs, hw⟩
  have hf : finish D.gates roots p.val q.val r.val := by
    intro t
    change (D.wires (roots.map (bit t))).getD p.val false = _ ∧ _
    rw [input_rows]
    exact hw t
  have h := compile D.gates p.val q.val r.val hg 5 2 hs hn roots roots
    (fun _ h => h) (by decide +kernel) (by decide +kernel) hf
  exact Bool.false_ne_true (scan_false.symm.trans h.scan_true)
