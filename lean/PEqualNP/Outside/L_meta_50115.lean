import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50115

open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 6

def roots : List W := [62, 60, 56, 48, 32, 0, 63]

def lacks (s : List W) (z : W) : Nat := if z ∈ s then 0 else 1

def missing (s : List W) : Nat := lacks s 6 + lacks s 34 + lacks s 51

theorem lacks_cons (s : List W) (a z : W) :
    lacks (a :: s) z = if z = a then 0 else lacks s z := by
  by_cases h : z = a <;> simp [lacks, h]

theorem missing_cons (s : List W) (a : W) : missing s ≤ missing (a :: s) + 1 := by
  have bound (z : W) : lacks s z ≤ 1 := by unfold lacks; split <;> omega
  have hb0 := bound 6
  have hb1 := bound 34
  have hb2 := bound 51
  have hd01 : (6 : W) ≠ 34 := by decide +kernel
  have hd02 : (6 : W) ≠ 51 := by decide +kernel
  have hd12 : (34 : W) ≠ 51 := by decide +kernel
  simp only [missing, lacks_cons]
  split_ifs <;> (first | omega | (subst a; simp_all))

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

theorem scan_done {k n : Nat} {s : List W} (h : missing s = 0) : scan k n s = true := by
  cases k <;> simp [scan, h]

theorem scan_skip {k n : Nat} {s : List W} (hb : missing s ≤ k) (h : scan k n s = true) :
    scan (k+1) n s = true := by
  simp [scan, show ¬ missing s > k+1 by omega, h]

theorem scan_bin {k n : Nat} {s : List W} {z : W} (hz : z ∈ binOptions s)
    (hb : missing (z :: s) ≤ k) (h : scan k n (z :: s) = true) : scan (k+1) n s = true := by
  have hm := missing_cons s z
  have ha := List.any_eq_true.mpr (⟨z, hz, h⟩ : ∃ z ∈ binOptions s, scan k n (z :: s) = true)
  simp [scan, show ¬ missing s > k+1 by omega, ha]

theorem scan_neg {k n : Nat} {s : List W} {z : W} (hz : z ∈ negOptions s)
    (hb : missing (z :: s) ≤ k) (h : scan k n (z :: s) = true) : scan (k+1) (n+1) s = true := by
  have hm := missing_cons s z
  have ha := List.any_eq_true.mpr (⟨z, hz, h⟩ : ∃ z ∈ negOptions s, scan k n (z :: s) = true)
  simp [scan, show ¬ missing s > k+1 by omega, ha]

def bit (t : Fin 6) (z : W) : Bool := z[t.val]

theorem input_rows : ∀ t : Fin 6,
    roots.map (bit t) = List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false,true] := by
  decide +kernel

theorem first_col : ∀ z : W, (∀ t : Fin 6, bit t z = (6 : Nat).testBit t.val) → z = 6 := by
  decide +kernel

theorem second_col : ∀ z : W, (∀ t : Fin 6, bit t z = (34 : Nat).testBit t.val) → z = 34 := by
  decide +kernel

theorem third_col : ∀ z : W, (∀ t : Fin 6, bit t z = (51 : Nat).testBit t.val) → z = 51 := by
  decide +kernel

theorem read_bit (w : List W) (i : Nat) (t : Fin 6) :
    (w.map (bit t)).getD i false = bit t (w.getD i 0) := by
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

theorem gate_word (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 63 ∈ s)
    (g : Gate) (hg : legal g) :
    ∃ z, admissible s g.op z ∧ ∀ t, step (w.map (bit t)) g = (w ++ [z]).map (bit t) := by
  have mem := read_mem hw h0
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨63, .inl h1, by simp [step, GateOp.eval, bit]; decide +kernel⟩
    · exact ⟨0, .inl h0, by simp [step, GateOp.eval, bit]⟩
    · exact ⟨63, .inl h1, by simp [step, GateOp.eval, bit]; decide +kernel⟩
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
  ∀ t : Fin 6, let v := gs.foldl step (w.map (bit t))
    v.getD p false = (6 : Nat).testBit t.val ∧
    v.getD q false = (34 : Nat).testBit t.val ∧
    v.getD r false = (51 : Nat).testBit t.val

def isNot (g : Gate) : Bool := @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)

theorem compile (gs : List Gate) (p q r : Nat) (hg : ∀ g ∈ gs, legal g)
    (k n : Nat) (hl : gs.length ≤ k) (hn : (gs.filter isNot).length ≤ n)
    (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 63 ∈ s) (hf : finish gs w p q r) :
    missing s ≤ k ∧ scan k n s = true := by
  induction gs generalizing k n w s with
  | nil =>
    simp only [finish, List.foldl_nil, read_bit] at hf
    have hp := first_col _ (fun t => (hf t).1)
    have hq := second_col _ (fun t => (hf t).2.1)
    have hr := third_col _ (fun t => (hf t).2.2)
    have hp' : (6 : W) ∈ s := hp ▸ read_mem hw h0 p
    have hq' : (34 : W) ∈ s := hq ▸ read_mem hw h0 q
    have hr' : (51 : W) ∈ s := hr ▸ read_mem hw h0 r
    have hz : missing s = 0 := by
      simp only [missing, lacks, if_pos hp', if_pos hq', if_pos hr', Nat.add_zero]
    exact ⟨by omega, scan_done hz⟩
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
        intro t
        simpa only [finish, List.foldl_cons, heval] using hf t
      have old (hz : z ∈ s) : w ++ [z] ⊆ s := by simpa using And.intro hw hz
      have new : w ++ [z] ⊆ z :: s := by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact List.mem_cons_of_mem _ (hw h)
        · exact List.mem_cons.mpr (.inl (by simpa using h))
      rcases hz with hz | hz | ⟨hop, hz⟩
      · obtain ⟨hb, hs⟩ := ih htail k n hlen hnum _ _ (old hz) h0 h1 hfin
        exact ⟨by omega, scan_skip hb hs⟩
      · obtain ⟨hb, hs⟩ := ih htail k n hlen hnum _ _ new
          (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin
        have hm := missing_cons s z
        exact ⟨by omega, scan_bin hz hb hs⟩
      · have he : isNot g = true := by simp [isNot, hop]
        simp [he] at hn
        cases n with
        | zero => omega
        | succ n =>
          obtain ⟨hb, hs⟩ := ih htail k n hlen (by omega) _ _ new
            (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin
          have hm := missing_cons s z
          exact ⟨by omega, scan_neg hz hb hs⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
theorem no_five : scan 5 2 roots = false := by decide +kernel

end PEqualNP.Outside.L_meta_50115

open PEqualNP.Outside.L_meta_50115 in
theorem PEqualNP.Outside.L_meta_50115 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (34 : Nat).testBit t.val ∧
    w.getD r.val false = (51 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hg, _, hn, hs, hw⟩
  have hf : finish D.gates roots p.val q.val r.val := by
    intro t
    change (D.wires (roots.map (bit t))).getD p.val false = _ ∧ _
    rw [input_rows]
    exact hw t
  have h := compile D.gates p.val q.val r.val hg 5 2 hs hn roots roots
    (fun _ h => h) (by decide +kernel) (by decide +kernel) hf
  exact Bool.false_ne_true (no_five.symm.trans h.2)
