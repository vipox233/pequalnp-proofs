import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50193
open PEqualNP.CircuitLowerBounds

def mop : GateOp → List Nat → Nat
  | .and, l => l.foldr (· &&& ·) 63 % 64
  | .or, l => l.foldr (· ||| ·) 0 % 64
  | .not, l => (63 ^^^ l.headD 0) % 64
  | _, _ => 0

def mstep (m : List Nat) (g : Gate) : List Nat := m ++ [mop g.op (g.inputs.map fun i => m.getD i 0)]

def mrun (gs : List Gate) (m : List Nat) : List Nat := gs.foldl mstep m

def ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def bstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem mod64_bit (x t : Nat) (ht : t < 6) : (x % 64).testBit t = x.testBit t := by
  rw [show (64 : Nat) = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow]
  simp [ht]

theorem bit63 (t : Nat) (ht : t < 6) : (63 : Nat).testBit t = true := by
  interval_cases t <;> decide

theorem getD_bits (m : List Nat) (i t : Nat) :
    (m.map fun a => a.testBit t).getD i false = (m.getD i 0).testBit t := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> simp

theorem step_bits (t : Nat) (ht : t < 6) (m : List Nat) (g : Gate) (hg : ok g) :
    (mstep m g).map (fun a => a.testBit t) = bstep (m.map fun a => a.testBit t) g := by
  obtain ⟨hop, hlen⟩ := hg
  simp only [mstep, bstep, List.map_append, List.map_cons, List.map_nil]
  congr 2
  have e : ∀ l : List Nat, l.map (fun i => (m.map fun a => a.testBit t).getD i false) =
      (l.map fun i => m.getD i 0).map (fun a => a.testBit t) := by
    intro l; rw [List.map_map]; congr 1; funext i; exact getD_bits m i t
  rw [e]
  have hl : (g.inputs.map fun i => m.getD i 0).length ≤ 2 := by simpa using hlen
  generalize g.inputs.map (fun i => m.getD i 0) = l at hl ⊢
  have b63 := bit63 t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with h | h | h <;> rw [h] <;> simp [mop, GateOp.eval, mod64_bit _ _ ht, b63]
  · rcases hop with h | h | h <;> rw [h] <;>
      simp [mop, GateOp.eval, mod64_bit _ _ ht, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, b63]
  · rcases hop with h | h | h <;> rw [h] <;>
      simp [mop, GateOp.eval, mod64_bit _ _ ht, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, b63]
  · simp at hl

theorem run_bits (t : Nat) (ht : t < 6) : ∀ (gs : List Gate) (m : List Nat), (∀ g ∈ gs, ok g) →
    gs.foldl bstep (m.map fun a => a.testBit t) = (mrun gs m).map (fun a => a.testBit t) := by
  intro gs
  induction gs with
  | nil => intro m _; rfl
  | cons g gs ih =>
    intro m h
    simp only [List.foldl_cons, mrun] at *
    rw [← step_bits t ht m g (h g (by simp))]
    exact ih _ (fun g' hg' => h g' (by simp [hg']))

theorem mop_lt (o : GateOp) (l : List Nat) : mop o l < 64 := by
  cases o <;> simp [mop, Nat.mod_lt]

theorem run_lt : ∀ (gs : List Gate) (m : List Nat), (∀ a ∈ m, a < 64) → ∀ a ∈ mrun gs m, a < 64 := by
  intro gs
  induction gs with
  | nil => intro m h; exact h
  | cons g gs ih =>
    intro m h
    apply ih
    intro a ha
    simp only [mstep, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact h a ha
    · exact mop_lt _ _

theorem run_len : ∀ (gs : List Gate) (m : List Nat), (mrun gs m).length = m.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro m; rfl
  | cons g gs ih =>
    intro m
    simp only [mrun, List.foldl_cons] at *
    rw [ih]; simp [mstep]; omega

theorem run_sub : ∀ (gs : List Gate) (m : List Nat), ∀ a ∈ m, a ∈ mrun gs m := by
  intro gs
  induction gs with
  | nil => intro m a h; exact h
  | cons g gs ih =>
    intro m a h
    exact ih _ a (by simp [mstep, h])

def setOf (W : List Nat) : Nat := W.foldl (fun S a => S ||| 2 ^ a) 0

theorem foldl_bit : ∀ (W : List Nat) (S x : Nat),
    (W.foldl (fun S a => S ||| 2 ^ a) S).testBit x = (S.testBit x || decide (x ∈ W)) := by
  intro W
  induction W with
  | nil => intro S x; simp
  | cons a W ih =>
    intro S x
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_or, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : a = x <;> simp [h, eq_comm]

theorem setOf_bit (W : List Nat) (x : Nat) : (setOf W).testBit x = decide (x ∈ W) := by
  simp [setOf, foldl_bit]

theorem setOf_snoc (W : List Nat) (v : Nat) : setOf (W ++ [v]) = setOf W ||| 2 ^ v := by
  simp [setOf, List.foldl_append]

def miss (S : Nat) : Nat :=
  (if S.testBit 24 then 0 else 1) + (if S.testBit 28 then 0 else 1) + (if S.testBit 46 then 0 else 1)

def targets : List Nat := [24, 28, 46]

theorem miss_or (S v : Nat) : miss S ≤ miss (S ||| 2 ^ v) + 1 := by
  unfold miss
  simp only [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h2 : v = 24 <;> by_cases h11 : v = 28 <;> by_cases h26 : v = 46 <;>
    subst_vars <;> simp_all <;> split_ifs <;> omega

theorem miss_off (S v : Nat) (hv : v ∉ targets) : miss (S ||| 2 ^ v) = miss S := by
  simp only [targets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨a, b, c⟩ := hv
  unfold miss
  simp [Nat.testBit_or, Nat.testBit_two_pow, a, b, c]

def mem (S : Nat) : List Nat := (List.range 64).filter fun a => S.testBit a

def cands (S : Nat) : List Nat :=
  (mem S).flatMap fun a => (mem S).flatMap fun b =>
    [mop .and [], mop .and [a], mop .and [a, b], mop .or [], mop .or [a], mop .or [a, b]]

def ncands (S : Nat) : List Nat :=
  (mem S).flatMap fun a => [mop .not [], mop .not [a]]

def reach (S nl : Nat) : Nat → Bool
  | 0 => miss S == 0
  | k + 1 => miss S == 0 || (decide (miss S ≤ k + 1) &&
      (if miss S = k + 1 then targets else List.range 64).any fun v =>
        ((setOf (cands S)).testBit v && reach (S ||| 2 ^ v) nl k) ||
        (decide (0 < nl) && (setOf (ncands S)).testBit v && reach (S ||| 2 ^ v) (nl - 1) k))

theorem reach_miss (S nl k : Nat) (h : reach S nl k = true) : miss S ≤ k := by
  cases k with
  | zero => simp [reach] at h; omega
  | succ k =>
    simp only [reach, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩ <;> omega

def isNot (g : Gate) : Bool := @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)

def nc (gs : List Gate) : Nat := (gs.filter isNot).length

theorem in_cands {S a b v : Nat} (ha : a ∈ mem S) (hb : b ∈ mem S)
    (hv : v ∈ [mop .and [], mop .and [a], mop .and [a, b], mop .or [], mop .or [a], mop .or [a, b]]) :
    v ∈ cands S :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, hv⟩⟩

theorem in_ncands {S a v : Nat} (ha : a ∈ mem S) (hv : v ∈ [mop .not [], mop .not [a]]) : v ∈ ncands S :=
  List.mem_flatMap.2 ⟨a, ha, hv⟩

theorem getD_mem (W : List Nat) (h0 : 0 ∈ W) (i : Nat) : W.getD i 0 ∈ W := by
  rw [List.getD_eq_getElem?_getD]
  cases h : W[i]? with
  | none => simpa using h0
  | some a => simpa using List.mem_of_getElem? h

theorem mem_mem (W : List Nat) (hW : ∀ a ∈ W, a < 64) (a : Nat) (ha : a ∈ W) :
    a ∈ mem (setOf W) := by
  simp [mem, setOf_bit, ha, hW a ha]

theorem step_cand (W : List Nat) (hW : ∀ a ∈ W, a < 64) (h0 : 0 ∈ W) (g : Gate) (hg : ok g) :
    let v := mop g.op (g.inputs.map fun i => W.getD i 0)
    (g.op ≠ GateOp.not → (setOf (cands (setOf W))).testBit v = true) ∧
    (g.op = GateOp.not → (setOf (ncands (setOf W))).testBit v = true) := by
  intro v
  obtain ⟨hop, hlen⟩ := hg
  have hm : ∀ i, W.getD i 0 ∈ mem (setOf W) := fun i => mem_mem W hW _ (getD_mem W h0 i)
  have z := mem_mem W hW 0 h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only [setOf_bit, decide_eq_true_eq, v]
  rcases g with ⟨op, ins⟩
  simp only at hop hlen ⊢
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ins⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨fun _ => in_cands z z (by simp), fun h => by cases h⟩
    · exact ⟨fun _ => in_cands z z (by simp), fun h => by cases h⟩
    · exact ⟨fun h => absurd rfl h, fun _ => in_ncands z (by simp)⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨fun _ => in_cands (hm i) z (by simp), fun h => by cases h⟩
    · exact ⟨fun _ => in_cands (hm i) z (by simp), fun h => by cases h⟩
    · exact ⟨fun h => absurd rfl h, fun _ => in_ncands (hm i) (by simp)⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨fun _ => in_cands (hm i) (hm j) (by simp), fun h => by cases h⟩
    · exact ⟨fun _ => in_cands (hm i) (hm j) (by simp), fun h => by cases h⟩
    · exact ⟨fun h => absurd rfl h, fun _ => in_ncands (hm i) (by simp [mop])⟩
  · simp at hlen

theorem sound : ∀ (gs : List Gate) (W : List Nat) (k nl : Nat), (∀ g ∈ gs, ok g) →
    (∀ a ∈ W, a < 64) → 0 ∈ W → nc gs ≤ nl → gs.length ≤ k →
    miss (setOf (mrun gs W)) = 0 → reach (setOf W) nl k = true := by
  intro gs
  induction gs with
  | nil =>
    intro W k nl _ _ _ _ _ hm
    cases k <;> simp [reach, mrun] at hm ⊢ <;> simp [hm]
  | cons g gs ih =>
    intro W k nl hok hW h0 hnc hk hm
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    set v := mop g.op (g.inputs.map fun i => W.getD i 0) with hv
    have hW' : ∀ a ∈ W ++ [v], a < 64 := by
      intro a ha; simp at ha; rcases ha with ha | rfl
      · exact hW a ha
      · exact mop_lt _ _
    have hgs : ∀ g ∈ gs, ok g := fun g' h => hok g' (by simp [h])
    have hm' : miss (setOf (mrun gs (W ++ [v]))) = 0 := hm
    have hk' : gs.length ≤ k := by simp at hk; omega
    have hc := step_cand W hW h0 g (hok g (by simp))
    have vlt : v < 64 := mop_lt _ _
    simp only [reach]
    by_cases hz : miss (setOf W) = 0
    · simp [hz]
    by_cases hn : g.op = GateOp.not
    · have hnc0 := hnc
      simp [nc, List.filter_cons, isNot, hn] at hnc0
      have hnc' : nc gs ≤ nl - 1 := by simp [nc]; omega
      have hpos : 0 < nl := by omega
      have hr := ih (W ++ [v]) k (nl - 1) hgs hW' (by simp [h0]) hnc' hk' hm'
      rw [setOf_snoc] at hr
      have hmr := reach_miss _ _ _ hr
      have hle := miss_or (setOf W) v
      simp only [Bool.or_eq_true, beq_iff_eq, hz, false_or, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true]
      refine ⟨by omega, v, ?_, Or.inr ⟨⟨hpos, hc.2 hn⟩, hr⟩⟩
      split_ifs with ht
      · by_contra hn'
        have := miss_off (setOf W) v hn'
        omega
      · simp [vlt]
    · have hnc' : nc gs ≤ nl := by
        simp [nc, List.filter_cons, isNot, hn] at hnc; simp [nc]; omega
      have hr := ih (W ++ [v]) k nl hgs hW' (by simp [h0]) hnc' hk' hm'
      rw [setOf_snoc] at hr
      have hmr := reach_miss _ _ _ hr
      have hle := miss_or (setOf W) v
      simp only [Bool.or_eq_true, beq_iff_eq, hz, false_or, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true]
      refine ⟨by omega, v, ?_, Or.inl ⟨hc.1 hn, hr⟩⟩
      split_ifs with ht
      · by_contra hn'
        have := miss_off (setOf W) v hn'
        omega
      · simp [vlt]

def M0 : List Nat := [62, 60, 56, 48, 32, 0, 63]

theorem no_reach : reach (setOf M0) 2 5 = false := by decide +kernel

theorem inputs_bits : ∀ t : Fin 6,
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] =
      M0.map (fun a => a.testBit t.val) := by decide

theorem pin (D : Circuit) (hok : ∀ g ∈ D.gates, ok g) (p : Fin (7 + D.size)) (c : Nat) (hc : c < 64)
    (h : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD p.val false =
        c.testBit t.val) : c ∈ mrun D.gates M0 := by
  have hlen := run_len D.gates M0
  have hp : p.val < (mrun D.gates M0).length := by
    rw [hlen]; have := p.isLt; simp [Circuit.size, M0] at this ⊢; omega
  have hlt := run_lt D.gates M0 (by decide) _ (List.getElem_mem hp)
  have e : (mrun D.gates M0)[p.val] = c := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 6
    · have := h ⟨i, hi⟩
      rw [inputs_bits ⟨i, hi⟩] at this
      have w : D.wires (M0.map fun a => a.testBit i) = D.gates.foldl bstep (M0.map fun a => a.testBit i) := rfl
      simp only at this
      rw [w, run_bits i hi D.gates M0 hok, getD_bits, List.getD_eq_getElem _ _ hp] at this
      exact this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (by
          calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (by
          calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rw [← e]; exact List.getElem_mem hp

end PEqualNP.Outside.L_meta_50193

open PEqualNP.Outside.L_meta_50193 in
theorem PEqualNP.Outside.L_meta_50193 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (24 : Nat).testBit t.val ∧
    w.getD q.val false = (28 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, hall⟩
  have hok : ∀ g ∈ D.gates, ok g := hfan
  have a := pin D hok p 24 (by norm_num) (fun t => (hall t).1)
  have b := pin D hok q 28 (by norm_num) (fun t => (hall t).2.1)
  have c := pin D hok r 46 (by norm_num) (fun t => (hall t).2.2)
  have hm : miss (setOf (mrun D.gates M0)) = 0 := by
    simp [miss, setOf_bit, a, b, c]
  have := sound D.gates M0 5 2 hok (by decide) (by decide) (by exact hnot) (by exact hsize) hm
  rw [no_reach] at this
  exact absurd this (by decide)
