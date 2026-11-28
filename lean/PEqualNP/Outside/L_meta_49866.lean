import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49866

open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 5

def roots : List W := [30, 28, 24, 16, 0, 31]

def lacks (s : List W) (t : W) : Nat := if t ∈ s then 0 else 1

def missing (s : List W) : Nat := lacks s 9 + lacks s 13 + lacks s 14

theorem lacks_cons (s : List W) (t z : W) :
    lacks (z :: s) t = if t = z then 0 else lacks s t := by
  by_cases h : t = z <;> simp [lacks, h]

theorem missing_cons (s : List W) (z : W) : missing s ≤ missing (z :: s) + 1 := by
  have hb (i : W) : lacks s i ≤ 1 := by unfold lacks; split <;> decide
  have h9 := hb 9
  have h13 := hb 13
  have h14 := hb 14
  have distinct : ∀ x : W, ¬ ((9 = x ∧ 13 = x) ∨ (9 = x ∧ 14 = x) ∨ (13 = x ∧ 14 = x)) := by
    decide +kernel
  have hd := distinct z
  simp only [missing, lacks_cons]
  split_ifs <;> first | omega | exact (hd (by tauto)).elim

theorem mem_of_lacks_zero {s : List W} {t : W} (h : lacks s t = 0) : t ∈ s := by
  unfold lacks at h
  split at h
  · assumption
  · contradiction

def dropAt (i : Nat) (w : W) : Bool := w.getLsbD i && !w.getLsbD (i + 1)

def viable (s : List W) : Bool := s.any (dropAt 0) && s.any (dropAt 3)

theorem viable_end {s : List W} (h : missing s = 0) : viable s = true := by
  have hm : 9 ∈ s := mem_of_lacks_zero (show lacks s 9 = 0 by unfold missing at h; omega)
  have h0 : s.any (dropAt 0) = true := List.any_eq_true.mpr ⟨9, hm, rfl⟩
  have h3 : s.any (dropAt 3) = true := List.any_eq_true.mpr ⟨9, hm, rfl⟩
  simp [viable, h0, h3]

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

theorem drop_bin (i : Nat) (a b : W) :
    (dropAt i (a &&& b) = true ∨ dropAt i (a ||| b) = true) →
    dropAt i a = true ∨ dropAt i b = true := by
  simp only [dropAt, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases a.getLsbD (i+1) <;>
    cases b.getLsbD (i+1) <;> decide

theorem viable_prev {s : List W} {z : W} (hz : z ∈ binOptions s) (h : viable (z :: s) = true) :
    viable s = true := by
  simp only [binOptions, List.mem_filter, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  obtain ⟨⟨a, ha, b, hb, op⟩, _⟩ := hz
  have lift (i : Nat) (hi : (z :: s).any (dropAt i) = true) : s.any (dropAt i) = true := by
    simp only [List.any_cons, Bool.or_eq_true] at hi
    rcases hi with hz | hs
    · have hd : dropAt i a = true ∨ dropAt i b = true := by
        apply drop_bin
        rcases op with rfl | rfl
        · exact .inl hz
        · exact .inr hz
      rcases hd with da | db
      · exact List.any_eq_true.mpr ⟨a, ha, da⟩
      · exact List.any_eq_true.mpr ⟨b, hb, db⟩
    · exact hs
  simp only [viable, Bool.and_eq_true] at h ⊢
  exact ⟨lift 0 h.1, lift 3 h.2⟩

def scan : Nat → Nat → List W → Bool
  | 0, _, s => missing s == 0
  | k+1, n, s =>
    if missing s = 0 then true else
    if missing s > k+1 ∨ (n = 0 ∧ viable s = false) then false else
    scan k n s || (binOptions s).any (fun z => scan k n (z :: s)) ||
      (n != 0 && (negOptions s).any (fun z => scan k (n-1) (z :: s)))

theorem scan_done {k n s} (h : missing s = 0) : scan k n s = true := by
  cases k <;> simp [scan, h]

theorem scan_facts {k n s} (h : scan k n s = true) :
    missing s ≤ k ∧ (n = 0 → viable s = true) := by
  by_cases hm : missing s = 0
  · exact ⟨by omega, fun _ => viable_end hm⟩
  cases k with
  | zero => simp [scan, hm] at h
  | succ k =>
    by_cases hp : missing s > k+1 ∨ (n = 0 ∧ viable s = false)
    · simp [scan, hm, hp] at h
    · refine ⟨by omega, fun hn => ?_⟩
      cases he : viable s with
      | true => rfl
      | false => exact (hp (.inr ⟨hn, he⟩)).elim

theorem scan_step {k n s} (hb : missing s ≤ k+1) (hv : n = 0 → viable s = true)
    (hr : scan k n s = true ∨ (∃ z ∈ binOptions s, scan k n (z :: s) = true) ∨
      (n ≠ 0 ∧ ∃ z ∈ negOptions s, scan k (n-1) (z :: s) = true)) : scan (k+1) n s = true := by
  have hp : ¬ (missing s > k+1 ∨ (n = 0 ∧ viable s = false)) := by
    rintro (h | ⟨hn, he⟩)
    · omega
    · rw [hv hn] at he
      contradiction
  by_cases hm : missing s = 0
  · exact scan_done hm
  · simpa [scan, hm, hp, List.any_eq_true, or_assoc] using hr

theorem scan_skip {k n s} (h : scan k n s = true) : scan (k+1) n s = true := by
  obtain ⟨hb, hv⟩ := scan_facts h
  exact scan_step (by omega) hv (.inl h)

theorem scan_bin {k n s z} (hz : z ∈ binOptions s) (h : scan k n (z :: s) = true) :
    scan (k+1) n s = true := by
  obtain ⟨hb, hv⟩ := scan_facts h
  have hdiff := missing_cons s z
  exact scan_step (by omega) (fun hn => viable_prev hz (hv hn)) (.inr (.inl ⟨z, hz, h⟩))

theorem scan_neg {k n s z} (hz : z ∈ negOptions s) (h : scan k n (z :: s) = true) :
    scan (k+1) (n+1) s = true := by
  have hb := (scan_facts h).1
  have hdiff := missing_cons s z
  apply scan_step (by omega) (fun hn => by omega)
  exact .inr (.inr ⟨by omega, z, hz, by simpa using h⟩)

-- The row simulation adapts lean/PEqualNP/Outside/L_meta_42704.lean at
-- 20d2295cbc492eb4561bc540548675c7440f35a1 to five rows and three exact masks.
def bit (r : Fin 5) (z : W) : Bool := z[r.val]

theorem input_rows : ∀ r : Fin 5,
    roots.map (bit r) = List.ofFn (fun i : Fin 4 => decide (i.val < r.val)) ++ [false, true] := by
  decide +kernel

theorem row_eq (z v : W) (h : ∀ r : Fin 5, bit r z = v.toNat.testBit r.val) : z = v := by
  apply BitVec.eq_of_getLsbD_eq
  exact fun i hi => h ⟨i, hi⟩

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
    v.getD p false = (9 : Nat).testBit t.val ∧ v.getD q false = (13 : Nat).testBit t.val ∧
    v.getD r false = (14 : Nat).testBit t.val

def isNot (g : Gate) : Bool := @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)

theorem compile (gs : List Gate) (p q r : Nat) (hg : ∀ g ∈ gs, legal g)
    (k n : Nat) (hl : gs.length ≤ k) (hn : (gs.filter isNot).length ≤ n)
    (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 31 ∈ s) (hf : finish gs w p q r) :
    scan k n s = true := by
  induction gs generalizing k n w s with
  | nil =>
    simp only [finish, List.foldl_nil, read_bit] at hf
    have ep : w.getD p 0 = 9 := row_eq _ _ (fun t => (hf t).1)
    have eq : w.getD q 0 = 13 := row_eq _ _ (fun t => (hf t).2.1)
    have er : w.getD r 0 = 14 := row_eq _ _ (fun t => (hf t).2.2)
    have hp := ep ▸ read_mem hw h0 p
    have hq := eq ▸ read_mem hw h0 q
    have hr := er ▸ read_mem hw h0 r
    exact scan_done (by simp only [missing, lacks, ite_eq_left hp, ite_eq_left hq, ite_eq_left hr])
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
      · exact scan_skip (ih htail k n hlen hnum _ _ (old hz) h0 h1 hfin)
      · exact scan_bin hz (ih htail k n hlen hnum _ _ new (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin)
      · have he : isNot g = true := by simp [isNot, hop]
        simp [he] at hn
        cases n with
        | zero => omega
        | succ n => exact scan_neg hz (ih htail k n hlen (by omega) _ _ new (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hfin)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 4096 in
theorem no_six : scan 6 2 roots = false := by decide +kernel

end PEqualNP.Outside.L_meta_49866

open PEqualNP.Outside.L_meta_49866 in
theorem PEqualNP.Outside.L_meta_49866 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (9 : Nat).testBit t.val ∧
    w.getD q.val false = (13 : Nat).testBit t.val ∧
    w.getD r.val false = (14 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hg, _, hn, hs, hw⟩
  have hf : finish D.gates roots p.val q.val r.val := by
    intro t
    change (D.wires (roots.map (bit t))).getD p.val false = _ ∧ _
    rw [input_rows]
    exact hw t
  have h := compile D.gates p.val q.val r.val hg 6 2 hs hn roots roots
    (fun _ h => h) (by decide) (by decide) hf
  exact Bool.false_ne_true (no_six.symm.trans h)
