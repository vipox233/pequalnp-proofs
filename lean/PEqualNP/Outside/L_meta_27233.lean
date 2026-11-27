import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27233
open PEqualNP.CircuitLowerBounds

abbrev Atom := Fin 6
abbrev Col := Atom × Atom
def dual (a : Atom) : Atom := if a = 0 then 5 else if a = 5 then 0 else if a = 3 then 4 else if a = 4 then 3 else a
def infimum (a b : Atom) : Atom :=
  if a = 0 ∨ b = 0 then 0 else if a = 5 then b else if b = 5 then a else
  if a = 3 ∨ b = 3 then 3 else if a = 4 then b else if b = 4 then a else if a = b then a else 3
def op (s : Bool) (a b : Atom) := if s then dual (infimum (dual a) (dual b)) else infimum a b
def dead : Col := (0,0)
def goalCol : Col := (3,4)
abbrev good (w : Col) : Prop := w ≠ goalCol ∧ w ≠ (4,3)
def blend (s : Bool) (u v : Col) : Col := (op s u.1 v.1, op s u.2 v.2)
def uses (axis : Bool) (w : Atom) : Bool :=
  if w = 0 ∨ w = 5 then false else if w = 1 then !axis else if w = 2 then axis else true
def cost (axis : Bool) (w : Col) := (uses axis w.1 || uses axis w.2).toNat
set_option maxHeartbeats 1600000 in
theorem blend_good : ∀ (s : Bool) (u v : Col), good u → good v →
    (∀ t : Bool, cost t u + cost t v ≤ 1) → good (blend s u v) := by decide +kernel
set_option maxHeartbeats 1600000 in
theorem blend_cost : ∀ (s t : Bool) (u v : Col),
    cost t (blend s u v) ≤ cost t u + cost t v := by decide +kernel
def observe (p q : Bool) (a : Atom) : Bool :=
  if a = 0 then false else if a = 1 then p else if a = 2 then q else if a = 3 then p && q else if a = 4 then p || q else true
def view (s p q : Bool) (w : Col) : Bool := observe p q (if s then w.2 else w.1)
set_option maxHeartbeats 3200000 in
theorem blend_view : ∀ (b s p q : Bool) (u v : Col),
    view s p q (blend b u v) =
      if b then view s p q u || view s p q v else view s p q u && view s p q v := by decide +kernel
theorem distinguish : ∀ w : Col, (∀ s p q, view s p q w = view s p q goalCol) → w = goalCol := by decide +kernel

def bin (op : Bool) (a b : Nat) : Gate := ⟨if op then .or else .and, [a,b]⟩

def reads (gs : List Gate) (o : Nat) := gs.flatMap Gate.inputs ++ [o]

def need (t : Bool) (w : List Col) (rs : List Nat) : Nat :=
  (rs.map fun j => cost t (w.getD j dead)).sum

theorem need_cons (t : Bool) (w : List Col) (a : Nat) (rs : List Nat) :
    need t w (a::rs) = cost t (w.getD a dead) + need t w rs := rfl

theorem snoc_eq (w : List Col) (v : Col) : (w ++ [v]).getD w.length dead = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem snoc_ne (w : List Col) (v : Col) (j : Nat) (hn : j ≠ w.length) :
    (w ++ [v]).getD j dead = w.getD j dead := by
  by_cases h : j < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem need_snoc (t : Bool) (w : List Col) (v : Col) (rs : List Nat) :
    need t (w ++ [v]) rs ≤ need t w rs + rs.count w.length * cost t v := by
  induction rs with
  | nil => simp [need]
  | cons j rs ih =>
    rw [need_cons, need_cons, List.count_cons]
    by_cases h : j = w.length
    · subst j
      rw [snoc_eq]
      simp only [beq_self_eq_true, ite_true, Nat.add_mul, Nat.one_mul]
      omega
    · rw [snoc_ne _ _ _ h]
      simp [h]
      omega

def gateCol (g : Gate) (w : List Col) : Col :=
  let s := match g.op with | .or => true | _ => false
  blend s (w.getD (g.inputs.getD 0 0) dead) (w.getD (g.inputs.getD 1 0) dead)

theorem gate_bin (s : Bool) (a b : Nat) (w : List Col) :
    gateCol (bin s a b) w = blend s (w.getD a dead) (w.getD b dead) := by cases s <;> rfl

def run : List Gate → List Col → List Col
  | [], w => w
  | g :: gs, w => run gs (w ++ [gateCol g w])

theorem flow (gs : List Gate) (o : Nat) (w : List Col)
    (binary : ∀ g ∈ gs, ∃ s a b, g = bin s a b)
    (ok : ∀ i, good (w.getD i dead))
    (budget : ∀ t, need t w (reads gs o) ≤ 1)
    (single : ∀ j, w.length ≤ j → (reads gs o).count j ≤ 1) :
    good ((run gs w).getD o dead) := by
  induction gs generalizing w with
  | nil => exact ok o
  | cons g gs ih =>
    obtain ⟨s, a, b, rfl⟩ := binary g List.mem_cons_self
    let z := blend s (w.getD a dead) (w.getD b dead)
    have reads_eq : reads (bin s a b :: gs) o = a :: b :: reads gs o := by
      simp [reads, bin]
    have bounded (t : Bool) : cost t (w.getD a dead) + cost t (w.getD b dead) +
        need t w (reads gs o) ≤ 1 := by simpa only [reads_eq, need_cons, Nat.add_assoc] using budget t
    have gz : good z := blend_good s _ _ (ok a) (ok b) (fun t => by have := bounded t; omega)
    have rest_count (j : Nat) (hj : w.length ≤ j) : (reads gs o).count j ≤ 1 := by
      have h := single j hj
      rw [reads_eq, List.count_cons, List.count_cons] at h
      omega
    rw [run, gate_bin]
    apply ih (w := w ++ [z]) (fun g hg => binary g (List.mem_cons_of_mem _ hg))
    · intro i
      by_cases hi : i = w.length
      · subst i; rwa [snoc_eq]
      · rw [snoc_ne _ _ _ hi]; exact ok i
    · intro t
      have h := need_snoc t w z (reads gs o)
      have hc := Nat.mul_le_mul_right (cost t z) (rest_count w.length le_rfl)
      simp only [Nat.one_mul] at hc
      have hcost : cost t z ≤ cost t (w.getD a dead) + cost t (w.getD b dead) := blend_cost s t _ _
      have hb := bounded t
      omega
    · intro j hj
      exact rest_count j (by simp at hj; omega)

theorem read_view (w : List Col) (s p q : Bool) (j : Nat) :
    (w.map (view s p q)).getD j false = view s p q (w.getD j dead) := by
  cases h : w[j]? <;> simp [List.getD, h, view, dead, observe]

def stepBool (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem one_view (w : List Col) (s p q b : Bool) (a d : Nat) :
    (w ++ [gateCol (bin b a d) w]).map (view s p q) =
      stepBool (w.map (view s p q)) (bin b a d) := by
  simp only [List.map_append, List.map_cons, List.map_nil, gate_bin, blend_view]
  rw [← read_view, ← read_view]
  cases b <;> simp [stepBool, bin, GateOp.eval]

theorem run_view (gs : List Gate) (w : List Col) (s p q : Bool)
    (hb : ∀ g ∈ gs, ∃ t a b, g = bin t a b) :
    (run gs w).map (view s p q) = gs.foldl stepBool (w.map (view s p q)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨t,a,b,rfl⟩ := hb g List.mem_cons_self
    rw [run, List.foldl_cons, ih _ (fun g hg => hb g (List.mem_cons_of_mem _ hg)), one_view]

def occTarget (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def occFirst : Gate := ⟨.and, [0, 4]⟩

def occSecond : Gate := ⟨.not, [9]⟩

def occProbe (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

lemma occWitness (i : Fin 9) : ∃ x y : Fin 9 → Bool,
    occTarget x ≠ occTarget y ∧ (x 0 && x 4) = (y 0 && y 4) ∧ (∀ j, j ≠ i → x j = y j) := by
  refine ⟨occProbe (![160, 96, 80, 132, 68, 66, 20, 12, 10] i),
    occProbe (![161, 98, 84, 140, 84, 98, 84, 140, 266] i), ?_⟩
  fin_cases i <;> decide

def occStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def occAgree (a b : List Bool) (i : ℕ) : Prop :=
  a.length = b.length ∧ ∀ j, j ≠ i → a.getD j false = b.getD j false

lemma occAppend {a b : List Bool} {i : ℕ} (h : occAgree a b i) (z : Bool) :
    occAgree (a ++ [z]) (b ++ [z]) i := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hjl : j < a.length
  · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (h.1 ▸ hjl)]
    exact h.2 j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

lemma occFold (gs : List Gate) {i : ℕ} (hn : i ∉ gs.flatMap Gate.inputs)
    {a b : List Bool} (h : occAgree a b i) :
    occAgree (gs.foldl occStep a) (gs.foldl occStep b) i := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hp : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hn
    have he : g.inputs.map (fun k => a.getD k false) = g.inputs.map (fun k => b.getD k false) := by
      apply List.map_congr_left
      intro k hk
      exact h.2 k (fun he => hp.1 (he ▸ hk))
    apply ih hp.2
    unfold occStep
    rw [he]
    exact occAppend h _

lemma occInitial (x : Fin 9 → Bool) (j : ℕ) (hj : j < 9) :
    (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma occPrefix (x : Fin 9 → Bool) :
    occStep (occStep (List.ofFn x) occFirst) occSecond =
      (List.ofFn x ++ [x 0 && x 4]) ++ [!(x 0 && x 4)] := by
  simp [occStep, occFirst, occSecond, GateOp.eval]

lemma occTailInput (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hout : C.output + 1 = 9 + C.size) (i : Fin 9) :
    i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨x, y, hxy, h04, hsame⟩ := occWitness i
  have hbase : occAgree (List.ofFn x) (List.ofFn y) i.val := by
    refine ⟨by simp, ?_⟩
    intro j hji
    by_cases hj : j < 9
    · rw [occInitial x j hj, occInitial y j hj]
      exact hsame _ (fun h => hji (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hpre : occAgree (occStep (occStep (List.ofFn x) occFirst) occSecond)
      (occStep (occStep (List.ofFn y) occFirst) occSecond) i.val := by
    rw [occPrefix, occPrefix, h04]
    exact occAppend (occAppend hbase _) _
  have ho : C.output ≠ i.val := by
    have hz : C.size = gs.length + 2 := by simp [Circuit.size, hg]
    have hi := i.isLt
    omega
  apply hxy
  rw [← hcomp, ← hcomp]
  change (C.gates.foldl occStep (List.ofFn x)).getD C.output false =
    (C.gates.foldl occStep (List.ofFn y)).getD C.output false
  rw [hg]
  exact (occFold gs hn hpre).2 _ ho

lemma occCap (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht := ih (fun a ha => hf a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

lemma occTight (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (he : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hf a (by simp [ha])
    have hc := occCap gs ht
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at he
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact ih ht (by omega) a ha

lemma occSplit (C : Circuit) (h0 : C.gates.head? = some occFirst)
    (h1 : C.gates.tail.head? = some occSecond) :
    ∃ gs, C.gates = occFirst :: occSecond :: gs := by
  cases hg : C.gates with
  | nil => simp [hg] at h0
  | cons a t =>
    cases ht : t with
    | nil => simp [hg, ht] at h1
    | cons b gs =>
      have ha : a = occFirst := by simpa [hg] using h0
      have hb : b = occSecond := by simpa [hg, ht] using h1
      exact ⟨gs, by simp [ha, hb]⟩

def pattern (k : Fin 3) (a b : ℕ) : Gate :=
  if k = 0 then ⟨.not, [a]⟩ else bin (decide (k = 2)) a b

def post (g : Gate) (x : Fin 9 → Bool) : List Bool :=
  occStep ((List.ofFn x ++ [x 0 && x 4]) ++ [!(x 0 && x 4)]) g

lemma post_len (g : Gate) (x : Fin 9 → Bool) : (post g x).length = 12 := by simp [post, occStep]

def pairMask (s : Bool) (a b : Fin 11) : ℕ :=
  if b.val = 10 then (if s then ![160, 96, 80, 132, 68, 66, 20, 12, 10, 0, 0] a else ![176, 113, 81, 149, 69, 83, 21, 29, 17, 0, 0] a) else
    ![![0, 98, 140, 140, 84, 98, 98, 140, 266, 0, 0], ![0, 0, 84, 104, 84, 161, 84, 140, 273, 0, 0], ![0, 0, 0, 88, 152, 98, 98, 161, 266, 0, 0], ![0, 0, 0, 0, 84, 98, 84, 161, 273, 0, 0], ![0, 0, 0, 0, 0, 98, 98, 140, 266, 0, 0], ![0, 0, 0, 0, 0, 0, 84, 140, 266, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 140, 266, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 266, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] a b

def nextMask (s : Bool) (a b : Fin 11) : ℕ :=
  (pairMask s a b ^^^ (2 ^ a.val)) ^^^ (if b.val < 9 then 2 ^ b.val else 0)

set_option maxHeartbeats 2400000 in
lemma collisionCert : ∀ (s : Bool) (a b : Fin 11), a < b → a.val ≠ 9 → b.val ≠ 9 →
    let x := occProbe (pairMask s a b)
    let y := occProbe (nextMask s a b)
    occTarget x ≠ occTarget y ∧ ∀ j : Fin 12, j.val ≠ 9 → j.val ≠ a.val → j.val ≠ b.val →
      (post (bin s a.val b.val) x).getD j.val false = (post (bin s a.val b.val) y).getD j.val false := by
  decide +kernel

lemma sameFold (R : ℕ → Prop) (gs : List Gate) {u v : List Bool}
    (hr : ∀ i ∈ gs.flatMap Gate.inputs, R i) (hl : u.length = v.length)
    (he : ∀ i, R i → u.getD i false = v.getD i false) :
    ∀ i, R i → (gs.foldl occStep u).getD i false = (gs.foldl occStep v).getD i false := by
  induction gs generalizing u v with
  | nil => exact he
  | cons g gs ih =>
    have hm : g.inputs.map (fun k => u.getD k false) = g.inputs.map (fun k => v.getD k false) := by
      apply List.map_congr_left
      intro k hk
      exact he k (hr k (List.mem_append_left _ hk))
    apply ih (fun i hi => hr i (List.mem_append_right _ hi)) (by simp [occStep, hl])
    intro i hi
    unfold occStep
    rw [hm]
    by_cases hh : i < u.length
    · rw [List.getD_append _ _ _ _ hh, List.getD_append _ _ _ _ (hl ▸ hh)]
      exact he i hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

lemma overlap (C : Circuit) (s : Bool) (a b : Fin 11) (gs : List Gate)
    (hg : C.gates = occFirst :: occSecond :: bin s a.val b.val :: gs)
    (hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hab : a < b) (ha : a.val ≠ 9) (hb : b.val ≠ 9) :
    9 ∈ reads gs C.output ∨ a.val ∈ reads gs C.output ∨ b.val ∈ reads gs C.output := by
  by_contra hn
  let R (j : ℕ) := j ≠ 9 ∧ j ≠ a.val ∧ j ≠ b.val
  have hr (j : ℕ) (hj : j ∈ reads gs C.output) : R j :=
    ⟨fun h => hn (.inl (h ▸ hj)), fun h => hn (.inr (.inl (h ▸ hj))), fun h => hn (.inr (.inr (h ▸ hj)))⟩
  let x := occProbe (pairMask s a b)
  let y := occProbe (nextMask s a b)
  let g := bin s a.val b.val
  obtain ⟨hne, he⟩ := collisionCert s a b hab ha hb
  have heq (j : ℕ) (hj : R j) : (post g x).getD j false = (post g y).getD j false := by
    by_cases h : j < 12
    · exact he ⟨j,h⟩ hj.1 hj.2.1 hj.2.2
    · rw [List.getD_eq_default _ _ (by rw [post_len]; omega), List.getD_eq_default _ _ (by rw [post_len]; omega)]
  apply hne
  change occTarget x = occTarget y
  rw [← hc, ← hc]
  change (C.gates.foldl occStep (List.ofFn x)).getD C.output false = (C.gates.foldl occStep (List.ofFn y)).getD C.output false
  rw [hg]
  simp only [List.foldl_cons, occPrefix]
  exact sameFold R gs (fun i hi => hr i (List.mem_append_left _ hi)) (by simp [post_len]) heq C.output (hr _ (by simp [reads]))

lemma occCompulsory (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hout : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hinputs : ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs) :
    (Finset.range (9 + C.size)).erase 9 ⊆ (gs.flatMap Gate.inputs ++ [C.output]).toFinset := by
  intro j hj
  obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
  have hb := Finset.mem_range.mp hj
  apply List.mem_toFinset.mpr
  by_cases hsmall : j < 9
  · exact List.mem_append_left _ (hinputs ⟨j, hsmall⟩)
  by_cases hlast : j = C.output
  · simp [hlast]
  have hidx : j - 9 < C.gates.length := by change j - 9 < C.size; omega
  let k : Fin C.gates.length := ⟨j - 9, hidx⟩
  have hjk : 9 + k.val = j := by dsimp [k]; omega
  have hnlast : k.val + 1 < C.gates.length := by change j - 9 + 1 < C.size; omega
  obtain ⟨n, _, hn⟩ := hlive k hnlast
  have hall : j ∈ C.gates.flatMap Gate.inputs :=
    List.mem_flatMap.mpr ⟨C.gates.get n, List.get_mem _ _, hjk ▸ hn⟩
  simp only [hg, List.flatMap_cons, occFirst, occSecond, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hall
  apply List.mem_append_left
  rcases hall with (h | h) | h | ha <;> omega

lemma occNormalRest (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hnorm : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) :
    ∀ g ∈ gs, (∃ a, g = ⟨.not, [a]⟩) ∨ ∃ a b, g = ⟨.and, [a,b]⟩ ∨ g = ⟨.or, [a,b]⟩ := by
  intro g hm
  obtain ⟨n, hn⟩ := List.get_of_mem (show g ∈ C.gates by simp [hg, hm])
  have h := hnorm n
  rw [hn] at h
  have heq : g = ⟨g.op, g.inputs⟩ := rfl
  rcases h with ⟨ho, a, _, hi⟩ | ⟨ho, a, b, _, _, hi⟩
  · exact .inl ⟨a, heq.trans (by rw [ho,hi])⟩
  · refine .inr ⟨a,b,?_⟩
    rcases ho with ho | ho
    · exact .inl (heq.trans (by rw [ho,hi]))
    · exact .inr (heq.trans (by rw [ho,hi]))

lemma thirdForm (C : Circuit) (g : Gate) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: g :: gs)
    (hnorm : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) :
    ∃ (k : Fin 3) (a b : Fin 11), g = pattern k a.val b.val ∧ (k ≠ 0 → a < b) := by
  have hlen : 2 < C.gates.length := by simp [hg]
  have he : C.gates.get ⟨2, hlen⟩ = g := by simp [hg]
  have h := hnorm ⟨2, hlen⟩
  rw [he] at h
  have heq : g = ⟨g.op, g.inputs⟩ := rfl
  rcases h with ⟨hop, a, ha, hi⟩ | ⟨hop, a, b, hab, hb, hi⟩
  · exact ⟨0, ⟨a,ha⟩, ⟨a,ha⟩, heq.trans (by rw [hop,hi]; rfl), fun hn => False.elim (hn rfl)⟩
  · have hh : a < 11 := lt_trans hab hb
    rcases hop with hop | hop
    · exact ⟨1, ⟨a,hh⟩, ⟨b,hb⟩, heq.trans (by rw [hop,hi]; rfl), fun _ => hab⟩
    · exact ⟨2, ⟨a,hh⟩, ⟨b,hb⟩, heq.trans (by rw [hop,hi]; rfl), fun _ => hab⟩

lemma cardSplit (U R : Finset ℕ) (a b : ℕ) (hu : 9 ∉ U) (hs : U ⊆ insert a (insert b R))
    (h : 9 ∈ insert a (insert b R) ∨ a ∈ R ∨ b ∈ R) : U.card ≤ R.card + 1 := by
  have ha := Finset.card_insert_le a (insert b R)
  have hb := Finset.card_insert_le b R
  rcases h with h | h | h
  · have hc := Finset.card_le_card ((Finset.insert_subset_iff.mpr ⟨h,hs⟩) : insert 9 U ⊆ insert a (insert b R))
    rw [Finset.card_insert_of_notMem hu] at hc
    omega
  · have hh : a ∈ insert b R := Finset.mem_insert_of_mem h
    rw [Finset.insert_eq_of_mem hh] at hs
    have hc := Finset.card_le_card hs
    omega
  · rw [Finset.insert_eq_of_mem h] at hs
    have hc := Finset.card_le_card hs
    have hcap := Finset.card_insert_le a R
    omega

lemma tightAfter (C : Circuit) (k : Fin 3) (a b : Fin 11) (gs : List Gate)
    (hg : C.gates = occFirst :: occSecond :: pattern k a.val b.val :: gs)
    (hab : k ≠ 0 → a < b)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 12)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hout : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ l : Fin C.gates.length, j.val < l.val ∧ 9 + j.val ∈ (C.gates.get l).inputs) :
    (∀ g ∈ gs, g.inputs.length = 2) ∧ (reads gs C.output).Nodup := by
  let U := (Finset.range (9 + C.size)).erase 9
  let R := (reads gs C.output).toFinset
  have hlen : C.size = gs.length + 3 := by simp [Circuit.size, hg]
  have h9 : 9 ∈ Finset.range (9 + C.size) := Finset.mem_range.mpr (by omega)
  have hU : U.card = 8 + C.size := by simp only [U,Finset.card_erase_of_mem h9, Finset.card_range]; omega
  have sub := occCompulsory C _ hg hout hlive (occTailInput C _ hg hcomp hout)
  have hcut : U.card ≤ R.card + 1 := by
    by_cases hk : k = 0
    · have hsub : U ⊆ insert a.val R := by simpa [U,R,reads,pattern,hk] using sub
      have hc := Finset.card_le_card hsub
      have hh := Finset.card_insert_le a.val R
      omega
    · let s := decide (k = 2)
      have hp : pattern k a.val b.val = bin s a.val b.val := by simp [pattern,hk,s]
      have hsub : U ⊆ insert a.val (insert b.val R) := by simpa [U,R,reads,hp,bin] using sub
      apply cardSplit U R a.val b.val (by simp [U]) hsub
      by_cases ha : a.val = 9
      · simp [ha]
      by_cases hb : b.val = 9
      · simp [hb]
      obtain h | h | h := overlap C s a b gs (by simpa only [hp] using hg) hcomp (hab hk) ha hb
      · exact .inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)))
      · exact .inr (.inl (List.mem_toFinset.mpr h))
      · exact .inr (.inr (List.mem_toFinset.mpr h))
  have hcap : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hm => (hf g (by simp [hg,hm])).2
  have hh := occCap gs hcap
  have hr : R.card ≤ (reads gs C.output).length := List.toFinset_card_le _
  have hrlen : (reads gs C.output).length = (gs.flatMap Gate.inputs).length + 1 := by simp [reads]
  refine ⟨occTight gs hcap (by omega), ?_⟩
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := ((reads gs C.output) : Multiset ℕ))).mp
    (show R.card = (reads gs C.output).length by omega)

def piWire (t : Fin 3) : ℕ := ![1,2,5] t
def qiWire (t : Fin 3) : ℕ := ![3,7,6] t
def whichWire (t : Fin 3) (axis : Bool) : ℕ := if axis then qiWire t else piWire t
abbrev clearFor (t : Fin 3) (i : Fin 11) : Prop := i.val ≠ piWire t ∧ i.val ≠ qiWire t
lemma choosePair : ∀ a b : Fin 11, ∃ t : Fin 3, clearFor t a ∧ clearFor t b := by decide
lemma whichSmall : ∀ (t : Fin 3) (axis : Bool), whichWire t axis < 9 := by decide

def fixed (x y : Bool) : Col := (if x then 5 else 0, if y then 5 else 0)
lemma fixed_view : ∀ s p q x y : Bool, view s p q (fixed x y) = if s then y else x := by decide
lemma fixed_good : ∀ x y : Bool, good (fixed x y) := by decide
lemma fixed_cost : ∀ t x y : Bool, cost t (fixed x y) = 0 := by decide

def rawCol (t : Fin 3) (i : Fin 9) : Col :=
  if i.val = piWire t then (1,1) else if i.val = qiWire t then (2,2) else
    fixed (occProbe (![256,8,2] t) i) (occProbe (![228,113,149] t) i)
def assign (t : Fin 3) (s p q : Bool) (i : Fin 9) : Bool := view s p q (rawCol t i)
def preCol (t : Fin 3) : List Col :=
  let v (s : Bool) := assign t s false false 0 && assign t s false false 4
  List.ofFn (rawCol t) ++ [fixed (v false) (v true), fixed (!(v false)) (!(v true))]
lemma pre_len (t : Fin 3) : (preCol t).length = 11 := by simp [preCol]
lemma prefixView : ∀ (t : Fin 3) (s p q : Bool),
    let x := assign t s p q
    (preCol t).map (view s p q) = (List.ofFn x ++ [x 0 && x 4]) ++ [!(x 0 && x 4)] := by decide +kernel
lemma targetView : ∀ (t : Fin 3) (s p q : Bool), occTarget (assign t s p q) = view s p q goalCol := by decide +kernel
lemma quietView : ∀ (t : Fin 3) (i : Fin 11), clearFor t i → ∀ s p q : Bool,
    view s p q ((preCol t).getD i.val dead) = view s false false ((preCol t).getD i.val dead) := by decide +kernel

def gateValue (k : Fin 3) (x y : Bool) := if k = 0 then !x else if k = 1 then x && y else x || y
lemma patternVal (k : Fin 3) (a b : ℕ) (w : List Bool) :
    (pattern k a b).op.eval ((pattern k a b).inputs.map fun i => w.getD i false) =
       gateValue k (w.getD a false) (w.getD b false) := by
  fin_cases k <;> simp [pattern, bin, gateValue, GateOp.eval]

def valueAt (k t : Fin 3) (a b : Fin 11) (s : Bool) :=
  gateValue k (view s false false ((preCol t).getD a.val dead)) (view s false false ((preCol t).getD b.val dead))
def extraCol (k t : Fin 3) (a b : Fin 11) := fixed (valueAt k t a b false) (valueAt k t a b true)
def start (k t : Fin 3) (a b : Fin 11) := preCol t ++ [extraCol k t a b]
lemma extraView (k t : Fin 3) (a b : Fin 11) (s p q : Bool) :
    view s p q (extraCol k t a b) = valueAt k t a b s := by cases s <;> simp [extraCol,fixed_view]
lemma startView (k t : Fin 3) (a b : Fin 11) (hca : clearFor t a) (hcb : clearFor t b) (s p q : Bool) :
    (start k t a b).map (view s p q) = post (pattern k a.val b.val) (assign t s p q) := by
  unfold post
  rw [← prefixView]
  simp only [start, List.map_append, List.map_cons, List.map_nil, occStep]
  rw [patternVal]
  simp only [read_view, extraView, valueAt, quietView t a hca s p q, quietView t b hcb s p q]

lemma preGood (t : Fin 3) (j : ℕ) : good ((preCol t).getD j dead) := by
  by_cases h : j < 11
  · exact (by decide : ∀ (t : Fin 3) (j : Fin 11), good ((preCol t).getD j.val dead)) t ⟨j,h⟩
  · rw [List.getD_eq_default _ _ (by rw [pre_len]; omega)]; decide
lemma preCost (t : Fin 3) (axis : Bool) (j : ℕ) :
    cost axis ((preCol t).getD j dead) = if j = whichWire t axis then 1 else 0 := by
  by_cases h : j < 11
  · exact (by decide : ∀ (t : Fin 3) (axis : Bool) (j : Fin 11), cost axis ((preCol t).getD j.val dead) =
      if j.val = whichWire t axis then 1 else 0) t axis ⟨j,h⟩
  · rw [List.getD_eq_default _ _ (by rw [pre_len]; omega)]
    have he : j ≠ whichWire t axis := by have := whichSmall t axis; omega
    simp [he, cost, dead, uses]
lemma startGood (k t : Fin 3) (a b : Fin 11) (j : ℕ) : good ((start k t a b).getD j dead) := by
  by_cases hj : j = (preCol t).length
  · subst j; rw [start,snoc_eq]; exact fixed_good _ _
  · rw [start,snoc_ne _ _ _ hj]; exact preGood _ _
lemma startCost (k t : Fin 3) (a b : Fin 11) (axis : Bool) (j : ℕ) :
    cost axis ((start k t a b).getD j dead) = if j = whichWire t axis then 1 else 0 := by
  by_cases hj : j = (preCol t).length
  · have he : j ≠ whichWire t axis := by rw [pre_len] at hj; have := whichSmall t axis; omega
    subst j; rw [start,snoc_eq,extraCol,fixed_cost]; simp [he]
  · rw [start,snoc_ne _ _ _ hj,preCost]
lemma startNeed (k t : Fin 3) (a b : Fin 11) (axis : Bool) (rs : List ℕ) :
    need axis (start k t a b) rs = rs.count (whichWire t axis) := by
  induction rs with
  | nil => rfl
  | cons j rs ih =>
    rw [need_cons,startCost,ih,List.count_cons]
    by_cases h : j = whichWire t axis <;> simp [h,Nat.add_comm]

lemma impossibleAfter (C : Circuit) (k : Fin 3) (a b : Fin 11) (gs : List Gate)
    (hg : C.gates = occFirst :: occSecond :: pattern k a.val b.val :: gs)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hb : ∀ g ∈ gs, ∃ s i j, g = bin s i j) (hn : (reads gs C.output).Nodup) : False := by
  obtain ⟨t, hca, hcb⟩ := choosePair a b
  have hw (axis : Bool) : need axis (start k t a b) (reads gs C.output) ≤ 1 := by
    rw [startNeed]
    exact List.nodup_iff_count_le_one.mp hn _
  have hf := flow gs C.output (start k t a b) hb (startGood _ _ _ _) hw (fun j _ => List.nodup_iff_count_le_one.mp hn j)
  apply hf.1
  apply distinguish
  intro s p q
  rw [← read_view, run_view _ _ _ _ _ hb, startView _ _ _ _ hca hcb]
  let x := assign t s p q
  have he := hcomp x
  change (C.gates.foldl occStep (List.ofFn x)).getD C.output false = occTarget x at he
  rw [hg] at he
  simp only [List.foldl_cons,occPrefix] at he
  exact he.trans (targetView t s p q)

end PEqualNP.Outside.L_meta_27233

open PEqualNP.Outside.L_meta_27233 in
theorem PEqualNP.Outside.L_meta_27233 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩)) := by
  rintro ⟨C, hf, hs, hc, hout, hnorm, _, hlive, h0, h1⟩
  obtain ⟨tail, ht⟩ := occSplit C h0 h1
  cases tail with
  | nil =>
    have he := occTailInput C [] ht hc hout 0
    simp at he
  | cons g gs =>
    obtain ⟨k,a,b,he,hab⟩ := thirdForm C g gs ht hnorm
    subst g
    obtain ⟨hl,hn⟩ := tightAfter C k a b gs ht hab hf hs hc hout hlive
    apply impossibleAfter C k a b gs ht hc ?_ hn
    intro g hm
    rcases occNormalRest C _ ht hnorm g (List.mem_cons_of_mem _ hm) with ⟨i,hi⟩ | ⟨i,j,h | h⟩
    · have hlen := hl g hm
      simp [hi] at hlen
    · exact ⟨false,i,j,h⟩
    · exact ⟨true,i,j,h⟩
