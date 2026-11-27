import PEqualNP.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.List.Perm.Subperm

namespace PEqualNP.Outside.L_meta_27753

open PEqualNP.CircuitLowerBounds

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
  (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

abbrev active (blocked : Fin 10) (p : Fin 9) : Prop :=
  3 ≤ p.val ∧ p.val ≠ blocked.val

def probe (p q : Fin 9) (b : Bool) (i : Fin 9) : Bool :=
  if i = p then b else decide (i.val < 3 ∨ i = q)

def prefixProbe (p : Fin 9) (b : Bool) (i : Fin 9) : Bool :=
  if i = p then b else ([274, 265, 137] : List Nat).getD p.val 0 |>.testBit i.val

def pairInput (blocked : Fin 10) (p q : Fin 9) (r : Fin 4) (s : Fin 10) (i : Fin 9) : Bool :=
  if i.val < 3 then true
  else if i = p then r.val.testBit 0
  else if i = q then r.val.testBit 1
  else decide (i.val = s.val ∧ i.val ≠ blocked.val)

def pairSignature (blocked : Fin 10) (p q : Fin 9) (r : Fin 4) : List Bool :=
  List.ofFn (fun s : Fin 10 => matching (pairInput blocked p q r s))

theorem prefix_influence :
    ∀ p : Fin 9, p.val < 3 →
      matching (prefixProbe p false) ≠ matching (prefixProbe p true) ∧
      (prefixProbe p false 0 || prefixProbe p false 1) = true ∧
      (prefixProbe p true 0 || prefixProbe p true 1) = true := by
  decide +kernel

theorem probe_influence :
    ∀ (blocked : Fin 10) (p : Fin 9), 3 ≤ blocked.val → active blocked p →
      ∃ q : Fin 9, active blocked q ∧ p ≠ q ∧
        matching (probe p q false) ≠ matching (probe p q true) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem three_signatures :
    ∀ (blocked : Fin 10) (p q : Fin 9), 3 ≤ blocked.val →
      active blocked p → active blocked q → p ≠ q →
      ∃ a b c : Fin 4,
        pairSignature blocked p q a ≠ pairSignature blocked p q b ∧
        pairSignature blocked p q a ≠ pairSignature blocked p q c ∧
        pairSignature blocked p q b ≠ pairSignature blocked p q c := by
  decide +kernel

theorem distinguish_pair (blocked : Fin 10) (p q : Fin 9)
    (hd : 3 ≤ blocked.val) (hp : active blocked p) (hq : active blocked q) (hpq : p ≠ q)
    (summarize : Fin 4 → Bool) :
    ∃ r t : Fin 4, ∃ s : Fin 10, summarize r = summarize t ∧
      matching (pairInput blocked p q r s) ≠ matching (pairInput blocked p q t s) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := three_signatures blocked p q hd hp hq hpq
  have different (r t : Fin 4) (h : pairSignature blocked p q r ≠ pairSignature blocked p q t) :
      ∃ s : Fin 10, matching (pairInput blocked p q r s) ≠
        matching (pairInput blocked p q t s) := by
    by_contra! all
    apply h
    exact congrArg List.ofFn (funext all)
  by_cases eab : summarize a = summarize b
  · obtain ⟨s, hs⟩ := different a b hab
    exact ⟨a, b, s, eab, hs⟩
  by_cases eac : summarize a = summarize c
  · obtain ⟨s, hs⟩ := different a c hac
    exact ⟨a, c, s, eac, hs⟩
  have ebc : summarize b = summarize c := by
    cases ha : summarize a <;> cases hb : summarize b <;> cases hc : summarize c <;>
      simp_all
  obtain ⟨s, hs⟩ := different b c hbc
  exact ⟨b, c, s, ebc, hs⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]
    omega

theorem keep (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have more : i < (step w g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (step w g) more]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def wire (C : Circuit) (x : Fin 9 → Bool) (i : Nat) : Bool :=
  (C.wires (List.ofFn x)).getD i false

def topo (C : Circuit) : Prop :=
  ∀ (k : Fin C.gates.length) (i : Nat), i ∈ (C.gates.get k).inputs → i < 9 + k.val

def edge (C : Circuit) (u v : Nat) : Prop :=
  ∃ k : Fin C.gates.length, v = 9 + k.val ∧ u ∈ (C.gates.get k).inputs

abbrev reach (C : Circuit) := Relation.ReflTransGen (edge C)

theorem wire_raw (C : Circuit) (x : Fin 9 → Bool) (p : Fin 9) :
    wire C x p.val = x p := by
  change (C.gates.foldl step (List.ofFn x)).getD p.val false = x p
  have valid : p.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using p.isLt
  rw [keep _ _ _ valid, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid]
  change (List.ofFn x)[p.val] = x p
  rw [List.getElem_ofFn]

theorem wire_gate (C : Circuit) (hC : topo C) (x : Fin 9 → Bool)
    (k : Fin C.gates.length) : wire C x (9 + k.val) =
      (C.gates.get k).op.eval ((C.gates.get k).inputs.map (wire C x)) := by
  let w := (C.gates.take k.val).foldl step (List.ofFn x)
  have wl : w.length = 9 + k.val := by
    simp [w, length_run]
  have split : C.gates = C.gates.take k.val ++ C.gates.get k :: C.gates.drop (k.val+1) := by
    conv =>
      lhs
      rw [← List.take_append_drop k.val C.gates, List.drop_eq_getElem_cons k.isLt]
    rfl
  have run : C.wires (List.ofFn x) =
      (C.gates.drop (k.val+1)).foldl step (step w (C.gates.get k)) := by
    change C.gates.foldl step (List.ofFn x) = _
    conv =>
      lhs
      rw [split]
    simp only [List.foldl_append, List.foldl_cons]
    rfl
  have short (i : Nat) (hi : i ≤ 9+k.val) :
      wire C x i = (step w (C.gates.get k)).getD i false := by
    have hs : i < (step w (C.gates.get k)).length := by
      simp only [step, List.length_append, List.length_singleton, wl]
      omega
    unfold wire
    rw [run, keep _ _ _ hs]
  have old (i : Nat) (hi : i < 9+k.val) : wire C x i = w.getD i false := by
    rw [short i (Nat.le_of_lt hi)]
    have h' : i < w.length := by simpa [wl] using hi
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h']
  rw [short _ (Nat.le_refl _)]
  have same : ((C.gates.get k).inputs.map (wire C x)) =
      (C.gates.get k).inputs.map (fun i => w.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact old i (hC k i hi)
  rw [same]
  simp [step, List.getD_eq_getElem?_getD, wl]

theorem edge_lt (C : Circuit) (hC : topo C) {u v : Nat} (h : edge C u v) : u < v := by
  obtain ⟨k, rfl, hk⟩ := h
  exact hC k u hk

theorem reach_le (C : Circuit) (hC : topo C) {u v : Nat} (h : reach C u v) : u ≤ v := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ he ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_lt C hC he))

abbrev changeEdge (C : Circuit) (x y : Fin 9 → Bool) (u v : Nat) :=
  edge C u v ∧ wire C x u ≠ wire C y u

theorem trace_change (C : Circuit) (hC : topo C) (x y : Fin 9 → Bool)
    (i : Nat) (hi : i < 9 + C.gates.length)
    (hd : wire C x i ≠ wire C y i) :
    ∃ p : Fin 9, x p ≠ y p ∧ Relation.ReflTransGen (changeEdge C x y) p.val i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases small : i < 9
    · let p : Fin 9 := ⟨i, small⟩
      refine ⟨p, ?_, .refl⟩
      change wire C x p.val ≠ wire C y p.val at hd
      simpa only [wire_raw C x p, wire_raw C y p] using hd
    · let k : Fin C.gates.length := ⟨i-9, by omega⟩
      have he : i = 9 + k.val := by
        dsimp [k]
        omega
      have pred : ∃ j ∈ (C.gates.get k).inputs, wire C x j ≠ wire C y j := by
        by_contra! same
        apply hd
        rw [he, wire_gate C hC x k, wire_gate C hC y k]
        apply congrArg ((C.gates.get k).op.eval)
        exact List.map_congr_left same
      obtain ⟨j, hj, hdiff⟩ := pred
      have before : j < i := by simpa only [he] using hC k j hj
      obtain ⟨p, hp, path⟩ := ih j before (Nat.lt_trans before hi) hdiff
      exact ⟨p, hp, path.tail ⟨⟨k, he, hj⟩, hdiff⟩⟩

theorem trace_reaches (C : Circuit) (x y : Fin 9 → Bool) {u v : Nat}
    (h : Relation.ReflTransGen (changeEdge C x y) u v) : reach C u v :=
  Relation.ReflTransGen.mono (r := changeEdge C x y) (p := edge C) (fun _ _ h => h.1) u v h

theorem no_bypass (C : Circuit) (hC : topo C) (x y : Fin 9 → Bool)
    {p cut : Nat} (chain : reach C p cut) (same : wire C x cut = wire C y cut)
    (unique : ∀ t, reach C p t → t < cut →
      ∀ u v, edge C t u → edge C t v → u = v)
    {w : Nat} (path : Relation.ReflTransGen (changeEdge C x y) p w)
    (hw : cut ≤ w) (different : wire C x w ≠ wire C y w) : False := by
  induction chain using Relation.ReflTransGen.head_induction_on generalizing w with
  | refl =>
    rcases path.cases_head with rfl | ⟨_, hh, _⟩
    · exact different same
    · exact hh.2 same
  | @head p next e tail ih =>
    have before : p < cut := Nat.lt_of_lt_of_le (edge_lt C hC e) (reach_le C hC tail)
    rcases path.cases_head with heq | ⟨next', en, rest⟩
    · omega
    have equal : next = next' := unique p .refl before next next' e en.1
    subst next'
    apply ih ?_ rest hw different
    intro t ht hlt u v hu hv
    exact unique t ((Relation.ReflTransGen.single e).trans ht) hlt u v hu hv

abbrev uses (C : Circuit) := C.gates.flatMap Gate.inputs

theorem use_of_edge {C : Circuit} {u v : Nat} (h : edge C u v) : u ∈ uses C := by
  obtain ⟨k, _, hk⟩ := h
  exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, hk⟩

theorem twice_of_reads (gs : List Gate) (a : Nat) (p q : Fin gs.length)
    (hpq : p.val < q.val) (hp : a ∈ (gs.get p).inputs) (hq : a ∈ (gs.get q).inputs) :
    2 ≤ List.count a (gs.flatMap Gate.inputs) := by
  have hlen : q.val - (p.val+1) < (gs.drop (p.val+1)).length := by
    simp only [List.length_drop]
    have := q.isLt
    omega
  have gl : (gs.drop (p.val+1))[q.val-(p.val+1)] = gs.get q := by
    rw [List.getElem_drop, List.get_eq_getElem]
    congr 1
    omega
  have later : a ∈ (gs.drop (p.val+1)).flatMap Gate.inputs :=
    List.mem_flatMap.mpr ⟨_, gl ▸ List.getElem_mem hlen, hq⟩
  have split : gs = gs.take p.val ++ gs.get p :: gs.drop (p.val+1) := by
    conv =>
      lhs
      rw [← List.take_append_drop p.val gs, List.drop_eq_getElem_cons p.isLt]
    rfl
  conv =>
    rhs
    arg 2
    rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, List.count_append]
  have h1 := List.count_pos_iff.mpr hp
  have h2 := List.count_pos_iff.mpr later
  omega

theorem forced_twice {C : Circuit} {a b d : Nat}
    (hb : edge C a b) (hd : edge C a d) (hne : b ≠ d) :
    2 ≤ (uses C).count a := by
  obtain ⟨i, rfl, hi⟩ := hb
  obtain ⟨j, rfl, hj⟩ := hd
  rcases Nat.lt_or_gt_of_ne (show i.val ≠ j.val by omega) with l | r
  · exact twice_of_reads C.gates a i j l hi hj
  · exact twice_of_reads C.gates a j i r hj hi

theorem slot_bound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem g hk))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem one_fork (C : Circuit) (n : C.gates.length ≤ 12)
    (out : C.output + 1 = 9 + C.gates.length)
    (slots : (uses C).length ≤ 2 * C.gates.length)
    (live : ∀ k < C.output, k ∈ uses C)
    (first : ∀ k < 3, 2 ≤ (uses C).count k) :
    ∃ fork, ∀ k, 3 ≤ k → k ≠ fork → (uses C).count k ≤ 1 := by
  by_cases found : ∃ fork, 3 ≤ fork ∧ 2 ≤ (uses C).count fork
  · obtain ⟨fork, ff, fd⟩ := found
    refine ⟨fork, ?_⟩
    intro k kf kn
    by_contra! kd
    let extra := List.range C.output ++ [0,1,2,fork,k]
    have sub : List.Subperm extra (uses C) := List.subperm_iff_count.mpr (fun w => by
      have base : (List.range C.output).count w ≤ 1 := by
        rw [List.count_range]
        split <;> omega
      simp only [extra, List.count_append]
      by_cases small : w < 3
      · have hf : w ≠ fork := by omega
        have hk : w ≠ k := by omega
        have one : List.count w [0,1,2,fork,k] = 1 := by
          have casesW : w = 0 ∨ w = 1 ∨ w = 2 := by omega
          rcases casesW with rfl | rfl | rfl <;>
            simp [Ne.symm hf, Ne.symm hk]
        rw [one]
        have := first w small
        omega
      by_cases eqF : w = fork
      · subst w
        have one : List.count fork [0,1,2,fork,k] = 1 := by
          have n0 : fork ≠ 0 := by omega
          have n1 : fork ≠ 1 := by omega
          have n2 : fork ≠ 2 := by omega
          simp [Ne.symm n0, Ne.symm n1, Ne.symm n2, Ne.symm kn]
        omega
      by_cases eqK : w = k
      · subst w
        have one : List.count k [0,1,2,fork,k] = 1 := by
          have n0 : k ≠ 0 := by omega
          have n1 : k ≠ 1 := by omega
          have n2 : k ≠ 2 := by omega
          simp [Ne.symm n0, Ne.symm n1, Ne.symm n2, kn, Ne.symm kn]
        omega
      have zero : List.count w [0,1,2,fork,k] = 0 := by
        have n0 : w ≠ 0 := by omega
        have n1 : w ≠ 1 := by omega
        have n2 : w ≠ 2 := by omega
        simp [Ne.symm n0, Ne.symm n1, Ne.symm n2, Ne.symm eqF, Ne.symm eqK]
      rw [zero, Nat.add_zero, List.count_range]
      split
      · exact List.count_pos_iff.mpr (live _ (by assumption))
      · omega)
    have hlen := sub.length_le
    simp only [extra, List.length_append, List.length_range, List.length_cons, List.length_nil] at hlen
    omega
  · exact ⟨0, fun k h _ => by
      by_contra! bad
      exact found ⟨k, h, bad⟩⟩

abbrev hasMatching (C : Circuit) :=
  ∀ x : Fin 9 → Bool, wire C x C.output = matching x

theorem active_reaches_out (C : Circuit) (hC : topo C)
    (hn : C.output < 9+C.gates.length) (hf : hasMatching C)
    (blocked : Fin 10) (p : Fin 9) (hd : 3 ≤ blocked.val) (hp : active blocked p) :
    reach C p.val C.output := by
  obtain ⟨q, _, _, effect⟩ := probe_influence blocked p hd hp
  have diff : wire C (probe p q false) C.output ≠ wire C (probe p q true) C.output := by
    simpa only [hf] using effect
  obtain ⟨r, dr, path⟩ := trace_change C hC _ _ C.output hn diff
  have er : r = p := by
    by_contra neg
    exact dr (by simp [probe, neg])
  subst r
  exact trace_reaches C _ _ path

theorem equal_start (C : Circuit) (x y : Fin 9 → Bool) {u v : Nat}
    (same : wire C x u = wire C y u)
    (diff : wire C x v ≠ wire C y v)
    (path : Relation.ReflTransGen (changeEdge C x y) u v) : False := by
  rcases path.cases_head with rfl | ⟨w, he, _⟩
  · exact diff same
  · exact he.2 same

theorem repeats_prefix (C : Circuit) (hC : topo C)
    (ho : 10 ≤ C.output) (hn : C.output < 9+C.gates.length) (hf : hasMatching C)
    (i0 i1 : Fin C.gates.length) (hi0 : i0.val = 0) (hi1 : i1.val = 1)
    (g0 : C.gates.get i0 = ⟨GateOp.or,[0,1]⟩)
    (g1 : C.gates.get i1 = ⟨GateOp.or,[2,9]⟩) :
    ∀ k < 3, 2 ≤ (uses C).count k := by
  have early0 (x : Fin 9 → Bool) : wire C x 9 = (x 0 || x 1) := by
    have e := wire_gate C hC x i0
    rw [hi0, g0] at e
    have x0 : wire C x 0 = x 0 := wire_raw C x (0 : Fin 9)
    have x1 : wire C x 1 = x 1 := wire_raw C x (1 : Fin 9)
    simpa [GateOp.eval, x0, x1] using e
  have early1 (x : Fin 9 → Bool) : wire C x 10 = (x 2 || wire C x 9) := by
    have e := wire_gate C hC x i1
    rw [hi1, g1] at e
    have x2 : wire C x 2 = x 2 := wire_raw C x (2 : Fin 9)
    simpa [GateOp.eval, x2] using e
  intro k hk
  let p : Fin 9 := ⟨k, by omega⟩
  obtain ⟨probeDiff, e0, e1⟩ := prefix_influence p hk
  let x := prefixProbe p false
  let y := prefixProbe p true
  have diff : wire C x C.output ≠ wire C y C.output := by
    rw [hf, hf]
    exact probeDiff
  have eq9 : wire C x 9 = wire C y 9 := by
    rw [early0, early0]
    exact e0.trans e1.symm
  have eq10 : wire C x 10 = wire C y 10 := by
    rw [early1, early1, early0, early0]
    change (x 0 || x 1) = true at e0
    change (y 0 || y 1) = true at e1
    simp only [e0, e1, Bool.or_true]
  obtain ⟨r, dr, path⟩ := trace_change C hC x y C.output hn diff
  have eqp : r = p := by
    by_contra notEq
    exact dr (by simp [x, y, prefixProbe, notEq])
  subst r
  rcases path.cases_head with endEq | ⟨next, first, rest⟩
  · dsimp [p] at endEq
    omega
  have n9 : next ≠ 9 := by
    intro he
    subst next
    exact equal_start C x y eq9 diff rest
  have n10 : next ≠ 10 := by
    intro he
    subst next
    exact equal_start C x y eq10 diff rest
  have firstEdge : edge C k next := first.1
  by_cases small : k < 2
  · have initial : edge C k 9 := by
      refine ⟨i0, by simp [hi0], ?_⟩
      rw [g0]
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp
    exact forced_twice initial firstEdge (Ne.symm n9)
  · have initial : edge C k 10 := by
      refine ⟨i1, by simp [hi1], ?_⟩
      rw [g1]
      have : k = 2 := by omega
      simp [this]
    exact forced_twice initial firstEdge (Ne.symm n10)

theorem no_unused (C : Circuit) (hC : topo C) (hf : hasMatching C)
    (_ho : 10 ≤ C.output) (hn : C.output+1 = 9+C.gates.length)
    (first : ∀ k < 3, 2 ≤ (uses C).count k)
    (used : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs) :
    ∀ w < C.output, w ∈ uses C := by
  intro w hw
  by_cases small : w < 3
  · exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (by decide) (first w small))
  by_cases raw : w < 9
  · let p : Fin 9 := ⟨w,raw⟩
    have hp : active (9 : Fin 10) p := by
      unfold active
      dsimp [p]
      omega
    have path := active_reaches_out C hC (by omega) hf (9 : Fin 10) p (by decide) hp
    rcases path.cases_head with he | ⟨v, e, _⟩
    · dsimp [p] at he
      omega
    · exact use_of_edge e
  · let j : Fin C.gates.length := ⟨w-9, by omega⟩
    have hlt : j.val + 1 < C.gates.length := by
      dsimp [j]
      omega
    obtain ⟨k, _, h⟩ := used j hlt
    have wj : 9+j.val = w := by
      dsimp [j]
      omega
    exact List.mem_flatMap.mpr ⟨_, List.get_mem _ _, by simpa only [wj] using h⟩

def mixed (C : Circuit) (blocked : Fin 10) (w : Nat) : Prop :=
  ∃ p q : Fin 9, active blocked p ∧ active blocked q ∧ p ≠ q ∧
    reach C p.val w ∧ reach C q.val w

theorem split_path (C : Circuit) {p w : Nat} (h : reach C p w) (hne : w ≠ p) :
    ∃ a, reach C p a ∧ edge C a w := by
  rcases h.cases_tail with eq | some
  · exact False.elim (hne eq)
  exact some

theorem mixed_pos (C : Circuit) (blocked : Fin 10) (w : Nat)
    (h : mixed C blocked w) : 9 ≤ w := by
  obtain ⟨p,q,_,_,hn,hp,hq⟩ := h
  have different : p.val ≠ q.val := fun he => hn (Fin.ext he)
  by_cases same : w = p.val
  · obtain ⟨_,_,i,hi,_⟩ := split_path C hq (by omega)
    omega
  · obtain ⟨_,_,i,hi,_⟩ := split_path C hp same
    omega

theorem two_inputs (xs : List Nat) (size : xs.length ≤ 2)
    (a b : Nat) (ha : a ∈ xs) (hb : b ∈ xs) (distinct : a ≠ b) :
    ∀ i ∈ xs, i = a ∨ i = b := by
  cases xs with
  | nil => simp at ha
  | cons x tail =>
    cases tail with
    | nil => simp at ha hb; omega
    | cons y rest =>
      have zero : rest.length = 0 := by simp only [List.length_cons] at size; omega
      have er : rest = [] := List.length_eq_zero_iff.mp zero
      subst rest
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb ⊢
      intro i hi
      rcases ha with h | h <;> rcases hb with j | j <;>
        rcases hi with k | k <;> omega

theorem only_two (C : Circuit) (hC : topo C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (d : Fin 10) (cut : Nat) (least : ∀ w < cut, ¬ mixed C d w)
    (p q : Fin 9) (hp : active d p) (hq : active d q) (neq : p ≠ q)
    (ap : reach C p.val cut) (aq : reach C q.val cut) :
    ∀ r : Fin 9, active d r → reach C r.val cut → r = p ∨ r = q := by
  have large : 9 ≤ cut := mixed_pos C d cut ⟨p,q,hp,hq,neq,ap,aq⟩
  have strict (i : Fin 9) : i.val < cut := Nat.lt_of_lt_of_le i.isLt large
  obtain ⟨u,pu,ue⟩ := split_path C ap (by have := strict p; omega)
  obtain ⟨v,qv,ve⟩ := split_path C aq (by have := strict q; omega)
  have uv : u ≠ v := by
    intro h
    subst v
    exact least u (edge_lt C hC ue) ⟨p,q,hp,hq,neq,pu,qv⟩
  have ucut := edge_lt C hC ue
  have vcut := edge_lt C hC ve
  obtain ⟨i,ci,ui⟩ := ue
  obtain ⟨j,cj,vj⟩ := ve
  have eqji : j = i := Fin.ext (by omega)
  subst j
  have all := two_inputs (C.gates.get i).inputs
    (arity _ (List.get_mem _ _)) u v ui vj uv
  intro r hr rr
  obtain ⟨w,rw,k,ck,wk⟩ := split_path C rr (by have := strict r; omega)
  have eqki : k = i := Fin.ext (by omega)
  subst k
  rcases all w wk with hwu | hwv
  · rw [hwu] at rw
    exact Or.inl (by
        by_contra ne
        exact least u ucut ⟨r,p,hr,hp,ne,rw,pu⟩)
  · rw [hwv] at rw
    exact Or.inr (by
        by_contra ne
        exact least v vcut ⟨r,q,hr,hq,ne,rw,qv⟩)

theorem active_if_context_changes (d : Fin 10) (p q : Fin 9)
    (r : Fin 4) (s t : Fin 10) (i : Fin 9)
    (neq : pairInput d p q r s i ≠ pairInput d p q r t i) :
    active d i ∧ i ≠ p ∧ i ≠ q := by
  have first : ¬ i.val < 3 := fun hh => neq (by simp [pairInput,hh])
  have ip : i ≠ p := fun hh => neq (by simp [pairInput,hh])
  have iq : i ≠ q := fun hh => neq (by simp [pairInput,hh])
  have id : i.val ≠ d.val := fun hh => neq (by simp [pairInput,ip,iq,hh])
  exact ⟨⟨by omega,id⟩,ip,iq⟩

theorem no_cut (C : Circuit) (hC : topo C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hf : hasMatching C) (ho : C.output < 9+C.gates.length)
    (d : Fin 10) (hd : 3 ≤ d.val) (cut : Nat) (hc : cut ≤ C.output)
    (mix : mixed C d cut) (least : ∀ w < cut, ¬ mixed C d w)
    (simple : ∀ (p : Fin 9), active d p → ∀ w, reach C p.val w → w < cut →
      ∀ u v, edge C w u → edge C w v → u = v) : False := by
  obtain ⟨p,q,hp,hq,neq,pc,qc⟩ := mix
  let summary (r : Fin 4) := wire C (pairInput d p q r 9) cut
  have same (r : Fin 4) (s : Fin 10) : wire C (pairInput d p q r s) cut = summary r := by
    by_contra diff
    obtain ⟨i, hi, trace⟩ := trace_change C hC _ _ cut (by omega) diff
    have ⟨activeI, ip, iq⟩ := active_if_context_changes d p q r s 9 i hi
    exact (only_two C hC arity d cut least p q hp hq neq pc qc i activeI
      (trace_reaches C _ _ trace)).elim ip iq
  obtain ⟨r,t,s,he,hdiff⟩ := distinguish_pair d p q hd hp hq neq summary
  have same_cut : wire C (pairInput d p q r s) cut = wire C (pairInput d p q t s) cut :=
    (same r s).trans (he.trans (same t s).symm)
  have diff : wire C (pairInput d p q r s) C.output ≠ wire C (pairInput d p q t s) C.output := by
    simpa only [hf] using hdiff
  obtain ⟨i,hi,trace⟩ := trace_change C hC _ _ C.output ho diff
  by_cases ip : i = p
  · subst i
    exact no_bypass C hC _ _ pc same_cut (simple p hp) trace hc diff
  by_cases iq : i = q
  · subst i
    exact no_bypass C hC _ _ qc same_cut (simple q hq) trace hc diff
  exact hi (by simp [pairInput,ip,iq])

theorem two_active :
    ∀ d : Fin 10, 3 ≤ d.val → ∃ p q : Fin 9, active d p ∧ active d q ∧ p ≠ q := by
  decide +kernel

theorem avoid_fork (C : Circuit) (fork : Nat) :
    ∃ d : Fin 10, 3 ≤ d.val ∧ ∀ cut, (∀ z < cut, ¬ mixed C d z) →
      ∀ (p : Fin 9), active d p → ∀ w < cut, reach C p.val w → w ≠ fork := by
  classical
  have whole (p : Fin 9) (hp : 3 ≤ p.val) : active (9 : Fin 10) p := by
    refine ⟨hp, ?_⟩
    change p.val ≠ 9
    have := p.isLt
    omega
  by_cases many : mixed C (9 : Fin 10) fork
  · refine ⟨9, by decide, ?_⟩
    intro cut least p hp w lew path equal
    subst w
    exact least fork lew many
  by_cases one : ∃ p : Fin 9, 3 ≤ p.val ∧ reach C p.val fork
  · obtain ⟨r,hr,pr⟩ := one
    let d : Fin 10 := ⟨r.val, Nat.lt_trans r.isLt (by decide)⟩
    refine ⟨d, hr, ?_⟩
    intro cut least p hp w lew path equal
    subst w
    have hpr : r ≠ p := by
      intro eq
      apply hp.2
      simpa only [d] using (congrArg Fin.val eq).symm
    exact many ⟨r,p,whole r hr,whole p hp.1,hpr,pr,path⟩
  · refine ⟨9, by decide, ?_⟩
    intro cut least p hp w lew path equal
    subst w
    exact one ⟨p,hp.1,path⟩

theorem matching_impossible (C : Circuit) (hC : topo C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hf : hasMatching C)
    (ho : C.output < 9+C.gates.length) (fork : Nat)
    (hfork : ∀ k, 3 ≤ k → k ≠ fork → (uses C).count k ≤ 1) : False := by
  classical
  obtain ⟨d,hd,avoid⟩ := avoid_fork C fork
  obtain ⟨p,q,hp,hq,neq⟩ := two_active d hd
  have atOut : mixed C d C.output := ⟨p,q,hp,hq,neq,
    active_reaches_out C hC ho hf d p hd hp, active_reaches_out C hC ho hf d q hd hq⟩
  have exist : ∃ w, mixed C d w := ⟨C.output, atOut⟩
  let cut := Nat.find exist
  have cutMix : mixed C d cut := Nat.find_spec exist
  have cut_le : cut ≤ C.output := Nat.find_min' exist atOut
  have least : ∀ w < cut, ¬ mixed C d w := fun w hw hm =>
    (Nat.not_le_of_lt hw) (Nat.find_min' exist hm)
  apply no_cut C hC arity hf ho d hd cut cut_le cutMix least
  intro i hi w iw lew u v e1 e2
  have notFork : w ≠ fork := avoid cut least i hi w lew iw
  have w3 : 3 ≤ w := Nat.le_trans hi.1 (reach_le C hC iw)
  by_contra ne
  have two := forced_twice e1 e2 ne
  have one := hfork w w3 notFork
  omega

theorem conclude (C : Circuit)
    (hC : topo C) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (n : C.gates.length ≤ 12) (hf : hasMatching C)
    (hout : C.output + 1 = 9+C.gates.length)
    (used : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (g0 : C.gates.head? = some ⟨GateOp.or,[0,1]⟩)
    (g1 : C.gates.tail.head? = some ⟨GateOp.or,[2,9]⟩) : False := by
  rw [List.head?_eq_getElem?] at g0
  rw [List.head?_eq_getElem?, List.getElem?_tail] at g1
  obtain ⟨h0, first⟩ := List.getElem?_eq_some_iff.mp g0
  obtain ⟨h1, second⟩ := List.getElem?_eq_some_iff.mp g1
  have high : 10 ≤ C.output := by omega
  have ub : C.output < 9+C.gates.length := by omega
  have repeats := repeats_prefix C hC high ub hf ⟨0,h0⟩ ⟨1,h1⟩ rfl rfl first second
  have live := no_unused C hC hf high hout repeats used
  obtain ⟨fork, bound⟩ := one_fork C n hout (slot_bound C.gates arity) live repeats
  exact matching_impossible C hC arity hf ub fork bound

end PEqualNP.Outside.L_meta_27753

open PEqualNP.Outside.L_meta_27753

theorem PEqualNP.Outside.L_meta_27753 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩)) := by
  rintro ⟨C, hfan, hsize, heval, hout, hnorm, _, hused, hfirst, hsecond⟩
  have arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hfan g hg).2
  have topological : topo C := by
    intro j w hw
    rcases hnorm j with ⟨_, a, ha, hs⟩ | ⟨_, a, b, hab, hb, hs⟩
    · rw [hs] at hw
      simp only [List.mem_singleton] at hw
      omega
    · rw [hs] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with he | he <;> omega
  have realized : hasMatching C := fun x => heval x
  exact conclude C topological arity hsize realized hout hused hfirst hsecond
