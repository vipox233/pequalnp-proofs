import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42704

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W := BitVec 8

def roots : List W := [170, 204, 240, 0, 255]

def kind (z : W) : Nat :=
  if z = 232 then 1 else if z &&& 232 = 96 then 2 else if z &&& 232 = 40 then 3 else 0

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

def dropAt (i : Nat) (w : W) : Bool := w.getLsbD i && !w.getLsbD 7

def viable (s : List W) : Bool := s.any (dropAt 3) && s.any (dropAt 5) && s.any (dropAt 6)

theorem marked_drops : ∀ w : W, (kind w = 2 → dropAt 5 w = true ∧ dropAt 6 w = true) ∧
    (kind w = 3 → dropAt 3 w = true) := by decide +kernel

theorem present {s : List W} {i : Nat} (h : lacks i s = 0) : ∃ w ∈ s, kind w = i := by
  unfold lacks at h
  split at h
  next hs => simpa using List.any_eq_true.mp hs
  next => omega

theorem viable_end {s : List W} (h : missing s = 0) : viable s = true := by
  unfold missing at h
  obtain ⟨a, ha, ai⟩ := present (show lacks 2 s = 0 by omega)
  obtain ⟨b, hb, bi⟩ := present (show lacks 3 s = 0 by omega)
  have h3 := List.any_eq_true.mpr ⟨b, hb, (marked_drops b).2 bi⟩
  have h5 := List.any_eq_true.mpr ⟨a, ha, ((marked_drops a).1 ai).1⟩
  have h6 := List.any_eq_true.mpr ⟨a, ha, ((marked_drops a).1 ai).2⟩
  simp [viable, h3, h5, h6]

theorem drop_bin (i : Nat) (a b : W) :
    (dropAt i (a &&& b) = true ∨ dropAt i (a ||| b) = true) →
    dropAt i a = true ∨ dropAt i b = true := by
  simp only [dropAt, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases a.getLsbD 7 <;> cases b.getLsbD 7 <;> decide

theorem viable_prev {s : List W} {z : W} (hz : z ∈ binOptions s) (h : viable (z :: s) = true) :
    viable s = true := by
  simp only [binOptions, List.mem_filter, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  obtain ⟨⟨a, ha, b, hb, op⟩, _⟩ := hz
  have lift (i : Nat) (hi : (z :: s).any (dropAt i) = true) : s.any (dropAt i) = true := by
    simp only [List.any_cons, Bool.or_eq_true] at hi
    rcases hi with hz | hs
    · have d : dropAt i a = true ∨ dropAt i b = true := by
        apply drop_bin
        rcases op with rfl | rfl
        · exact .inl hz
        · exact .inr hz
      rcases d with da | db
      · exact List.any_eq_true.mpr ⟨a, ha, da⟩
      · exact List.any_eq_true.mpr ⟨b, hb, db⟩
    · exact hs
  simp only [viable, Bool.and_eq_true] at h ⊢
  exact ⟨⟨lift 3 h.1.1, lift 5 h.1.2⟩, lift 6 h.2⟩

theorem Play.viable_zero {k n s} (h : Play k n s) (hn : n = 0) : viable s = true := by
  induction h with
  | done h => exact viable_end h
  | skip _ ih => exact ih hn
  | bin hz _ ih => exact viable_prev hz (ih hn)
  | neg => omega

theorem Play.possible {k n s} (h : Play k n s) :
    ¬ (missing s > k ∨ (n = 0 ∧ viable s = false)) := by
  rintro (hb | ⟨hn, hv⟩)
  · have := h.bound; omega
  · rw [h.viable_zero hn] at hv; contradiction

def scan : Nat → Nat → List W → Bool
  | 0, _, s => missing s == 0
  | k+1, n, s =>
    if missing s = 0 then true else if missing s > k+1 ∨ (n = 0 ∧ viable s = false) then false else
    scan k n s || (binOptions s).any (fun z => scan k n (z :: s)) ||
      (n != 0 && (negOptions s).any (fun z => scan k (n-1) (z :: s)))

theorem Play.scan_true {k n s} (h : Play k n s) : scan k n s = true := by
  induction h with
  | @done k n s h => cases k <;> simp [scan, h]
  | @skip k n s h ih =>
    have hb := (Play.skip h).possible
    simp [scan, hb, ih]
  | @bin k n s z hz h ih =>
    have hb := (Play.bin hz h).possible
    have ha := List.any_eq_true.mpr (⟨z, hz, ih⟩ : ∃ z ∈ binOptions s, scan k n (z :: s) = true)
    simp [scan, hb, ha]
  | @neg k n s z hz h ih =>
    have hb := (Play.neg hz h).bound
    have ha := List.any_eq_true.mpr (⟨z, hz, ih⟩ : ∃ z ∈ negOptions s, scan k n (z :: s) = true)
    simp [scan, Nat.not_lt.mpr hb, ha]

theorem scan_step {k n : Nat} {s : List W} (hm : missing s ≠ 0)
    (hs : scan k n s = false)
    (hb : (binOptions s).all (fun z => !scan k n (z :: s)) = true)
    (hi : n = 0 ∨ (negOptions s).all (fun z => !scan k (n-1) (z :: s)) = true) :
    scan (k+1) n s = false := by
  have bin : (binOptions s).any (fun z => scan k n (z :: s)) = false := by
    rw [List.any_eq_false]
    intro z hz
    simpa using (List.all_eq_true.mp hb z hz)
  rw [scan, ite_eq_right hm]
  split
  · rfl
  · rw [hs, bin]
    rcases hi with rfl | hi
    · simp
    · have neg : (negOptions s).any (fun z => scan k (n-1) (z :: s)) = false := by
        rw [List.any_eq_false]
        intro z hz
        simpa using (List.all_eq_true.mp hi z hz)
      simp [neg]

def bit (r : Fin 8) (z : W) : Bool := z[r.val]

def input (r : Fin 8) (i : Fin 3) : Bool := bit r (roots.getD i.val 0)

def cover (r : Fin 8) : Bool :=
  (input r 0 && input r 1) || (input r 1 && input r 2) || (input r 0 && input r 2)

theorem input_rows : ∀ r : Fin 8, roots.map (bit r) = List.ofFn (input r) ++ [false, true] := by
  decide +kernel

theorem decision_row : ∀ z : W, (∀ r : Fin 8, bit r z = cover r) → kind z = 1 := by
  decide +kernel

theorem first_row : ∀ z : W,
    (∀ r : Fin 8, cover r = true → bit r z = xor (input r 0) (input r 1)) → kind z = 2 := by
  decide +kernel

theorem second_row : ∀ z : W,
    (∀ r : Fin 8, cover r = true → bit r z = xor (input r 1) (input r 2)) → kind z = 3 := by
  decide +kernel

theorem read_bit (w : List W) (i : ℕ) (k : Fin 8) :
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

theorem gate_word (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 255 ∈ s)
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
    · exact ⟨255, .inl h1, by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, .inl h0, by simp [step, GateOp.eval, bit]⟩
    · exact ⟨255, .inl h1, by simp [step, GateOp.eval, bit]; decide⟩
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

def finish (gs : List Gate) (w : List W) (out p q : Nat) : Prop :=
  ∀ r, let v := gs.foldl step (w.map (bit r))
       v.getD out false = cover r ∧ (cover r = true →
         v.getD p false = xor (input r 0) (input r 1) ∧ v.getD q false = xor (input r 1) (input r 2))

theorem lacks_zero {s : List W} {z : W} {i : Nat} (h : z ∈ s) (hi : kind z = i) : lacks i s = 0 := by
  have ht : s.any (fun w => kind w == i) = true := List.any_eq_true.mpr ⟨z, h, by simp [hi]⟩
  simp [lacks, ht]

def isNot (g : Gate) : Bool := @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)

theorem compile (gs : List Gate) (out p q : Nat) (hg : ∀ g ∈ gs, legal g)
    (k n : Nat) (hl : gs.length ≤ k) (hn : (gs.filter isNot).length ≤ n)
    (w s : List W) (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : 255 ∈ s) (hf : finish gs w out p q) :
    Play k n s := by
  induction gs generalizing k n w s with
  | nil =>
    simp only [finish, List.foldl_nil, read_bit] at hf
    have dec := decision_row _ (fun r => (hf r).1)
    have first := first_row _ (fun r h => ((hf r).2 h).1)
    have second := second_row _ (fun r h => ((hf r).2 h).2)
    exact .done (by simp [missing, lacks_zero (read_mem hw h0 out) dec,
      lacks_zero (read_mem hw h0 p) first, lacks_zero (read_mem hw h0 q) second])
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
      have hfin : finish gs (w ++ [z]) out p q := by
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

set_option maxHeartbeats 32000000 in
theorem no_seven_skip : scan 6 1 roots = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_b0 : scan 6 1 (136 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_b1 : scan 6 1 (238 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_b2 : scan 6 1 (160 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_b3 : scan 6 1 (250 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_b4 : scan 6 1 (192 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_b5 : scan 6 1 (252 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_n0 : scan 6 0 (85 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_n1 : scan 6 0 (51 :: roots) = false := by
  decide +kernel

set_option maxHeartbeats 32000000 in
theorem no_seven_n2 : scan 6 0 (15 :: roots) = false := by
  decide +kernel

theorem no_seven : scan 7 1 roots = false := by
  apply scan_step (k := 6) (n := 1) (s := roots) (by decide +kernel) no_seven_skip
  ·
    rw [show binOptions roots = [136, 238, 160, 250, 192, 252] by decide +kernel]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.not_eq_true', and_true]
    exact ⟨no_seven_b0, no_seven_b1, no_seven_b2, no_seven_b3, no_seven_b4, no_seven_b5⟩
  · right
    rw [show negOptions roots = [85, 51, 15] by decide +kernel]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.not_eq_true', and_true]
    exact ⟨no_seven_n0, no_seven_n1, no_seven_n2⟩

end PEqualNP.Outside.L_meta_42704

open PEqualNP.Outside.L_meta_42704 in
theorem PEqualNP.Outside.L_meta_42704 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin (5 + C.size)),
  PEqualNP.MetaComplexity.FanInTwo C ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧
  C.output < 5 + C.size ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧
  ∀ x : Fin 3 → Bool,
    let w := List.ofFn x ++ [false, true]
    let cover := (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)
    C.eval w = cover ∧
    (cover = true →
      (C.wires w).getD p.val false = xor (x 0) (x 1) ∧
      (C.wires w).getD q.val false = xor (x 1) (x 2))) := by
  rintro ⟨C, p, q, hg, _, _, hs, hn, hw⟩
  have hf : finish C.gates roots C.output p.val q.val := by
    intro r
    change (C.wires (roots.map (bit r))).getD C.output false = _ ∧ _
    rw [input_rows]
    exact hw (input r)
  have h := compile C.gates C.output p.val q.val hg 7 1 hs hn roots roots
    (fun _ h => h) (by decide +kernel) (by decide +kernel) hf
  exact Bool.false_ne_true (no_seven.symm.trans h.scan_true)
