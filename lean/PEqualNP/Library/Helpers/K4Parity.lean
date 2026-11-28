import PEqualNP.Defs

namespace PEqualNP.Library.K4Parity

open PEqualNP.CircuitLowerBounds

abbrev Mask := BitVec 5

def inputs : List Mask := [30,29,27,23,0,31]

structure Step where
  neg : Bool
  join : Bool
  a : Mask
  b : Mask

def Step.val (t : Step) : Mask :=
  if t.neg then ~~~t.a else if t.join then t.a ||| t.b else t.a &&& t.b

def ok (ws : List Mask) (used : Bool) : List Step → Prop
  | [] => 3 ∈ ws ∧ 12 ∈ ws ∧ 5 ∈ ws
  | t :: ts => t.a ∈ ws ∧ t.b ∈ ws ∧ ¬ (used = true ∧ t.neg = true) ∧
      ok (t.val :: ws) (used || t.neg) ts

/- Each mask records the five cover rows. The low four bits correspond to a missing
   vertex, and the high bit to the full cover. The search records wire availability. -/
inductive Tree where
  | nil
  | node (left : Tree) (key : Nat) (right : Tree)

def Tree.has : Tree → Nat → Bool
  | .nil, _ => false
  | .node l a r, s => if s = a then true else if s < a then l.has s else r.has s

def Tree.every (p : Nat → Bool) : Tree → Bool
  | .nil => true
  | .node l a r => p a && l.every p && r.every p

theorem Tree.pass (t : Tree) (p : Nat → Bool) (h : t.every p = true) (s : Nat) (hs : t.has s = true) : p s = true := by
  induction t with
  | nil => simp [Tree.has] at hs
  | node l a r il ir =>
    simp only [Tree.every, Bool.and_eq_true] at h
    simp only [Tree.has] at hs
    split at hs
    · rename_i eq; exact eq ▸ h.1.1
    · split at hs
      · exact il h.1.2 hs
      · exact ir h.2 hs

abbrev Layer := Bool → Tree
def add (s : Nat) (m : Mask) := s ||| 2^m.toNat
def need (s : Nat) := (!s.testBit 3).toNat + (!s.testBit 12).toNat + (!s.testBit 5).toNat
def covers (s : Nat) (ws : List Mask) := ∀ m ∈ ws, s.testBit m.toNat = true

theorem addCovers (s : Nat) (m : Mask) (ws : List Mask) (h : covers s ws) : covers (add s m) (m :: ws) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [add]
  · simp [add, h a ha]

theorem needStep (s : Nat) (m : Mask) : need s ≤ need (add s m) + 1 := by
  simp only [need, add, Nat.testBit_or, Nat.testBit_two_pow]
  rcases eq_or_ne m.toNat 3 with e | e <;>
    rcases eq_or_ne m.toNat 12 with f | f <;>
    rcases eq_or_ne m.toNat 5 with g | g <;>
    cases s.testBit 3 <;> cases s.testBit 12 <;> cases s.testBit 5 <;>
    simp_all

theorem enough (ts : List Step) (s : Nat) (ws : List Mask) (used : Bool)
    (h : covers s ws) (ht : ok ws used ts) : need s ≤ ts.length := by
  induction ts generalizing s ws used with
  | nil =>
    obtain ⟨a,b,c⟩ := ht
    simpa [need] using (show (!s.testBit 3).toNat + (!s.testBit 12).toNat + (!s.testBit 5).toNat ≤ 0 by
      have a' : s.testBit 3 = true := h 3 a
      have b' : s.testBit 12 = true := h 12 b
      have c' : s.testBit 5 = true := h 5 c
      simp [a',b',c'])
  | cons t ts ih =>
    have hnext := ih (add s t.val) _ _ (addCovers s t.val ws h) ht.2.2.2
    have hprev := needStep s t.val
    simp only [List.length_cons]; omega

def pool (s : Nat) : List Mask :=
  (List.ofFn (fun i : Fin 32 => (BitVec.ofNat 5 i.val))).filter (fun m => s.testBit m.toNat)

theorem poolMem {s : Nat} {m : Mask} (h : s.testBit m.toNat = true) : m ∈ pool s := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨m.toFin, by simp⟩,h⟩

def allowed (next : Layer) (k s : Nat) (u : Bool) (m : Mask) : Bool :=
  let v := add s m
  decide (k < need v) || (next u).has v

def moves (next : Layer) (k s : Nat) (u : Bool) : Bool :=
  let xs := pool s
  xs.all (fun a =>
    (u || allowed next k s true (~~~a)) &&
    xs.all (fun b => allowed next k s u (a &&& b) && allowed next k s u (a ||| b)))

theorem advance (next : Layer) (k s : Nat) (u : Bool) (w : List Mask) (t : Step) (ts : List Step)
    (hm : moves next k s u = true) (hw : covers s w) (ht : ok w u (t :: ts))
    (hl : ts.length = k) : (next (u || t.neg)).has (add s t.val) = true := by
  obtain ⟨ha,hb,hn,hts⟩ := ht
  have hp := List.all_eq_true.mp hm t.a (poolMem (hw t.a ha))
  have hab := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hp).2 t.b (poolMem (hw t.b hb))
  have hv : allowed next k s (u || t.neg) t.val = true := by
    rcases t with ⟨n,j,a,b⟩
    cases u <;> cases n <;> cases j <;> simp_all [Step.val]
  have hneed := enough ts (add s t.val) _ _ (addCovers s t.val w hw) hts
  simpa [allowed,show ¬k < need (add s t.val) by omega] using hv

def verified (cur next : Layer) (k : Nat) : Bool :=
  (cur false).every (fun s => moves next k s false) && (cur true).every (fun s => moves next k s true)

def safe (l : Layer) (k : Nat) : Prop :=
  ∀ (u : Bool) (s : Nat), (l u).has s = true → ∀ (w : List Mask), covers s w →
    ∀ ts : List Step, ts.length = k → ¬ ok w u ts

theorem transfer (l next : Layer) (k : Nat) (hc : verified l next k = true) (hs : safe next k) :
    safe l (k+1) := by
  intro u s hlookup w hw ts hl ht
  have hm : moves next k s u = true := by
    cases u
    · exact Tree.pass _ _ (Bool.and_eq_true_iff.mp hc).1 _ hlookup
    · exact Tree.pass _ _ (Bool.and_eq_true_iff.mp hc).2 _ hlookup
  rcases ts with _ | ⟨t,ts⟩
  · simp at hl
  · have hk : ts.length = k := by simpa using hl
    exact hs _ _ (advance next k s u w t ts hm hw ht hk) _ (addCovers s t.val w hw) ts hk ht.2.2.2

attribute [local instance] PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq

def make (w : List Mask) (g : Gate) : Step :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  let pad : Mask := if g.op = .and then 31 else 0
  ⟨decide (g.op = .not), decide (g.op = .or), xs.getD 0 pad, xs.getD 1 pad⟩

def run (gs : List Gate) (w : List Mask) : List Mask := gs.foldl (fun v g => v ++ [(make v g).val]) w

def bit (r : Fin 5) (v : Mask) := v.getLsbD r.val

theorem read_bit (r : Fin 5) (w : List Mask) (i : Nat) :
    (w.map (bit r)).getD i false = bit r (w.getD i 0) := by
  have hz : bit r 0 = false := by fin_cases r <;> decide
  simpa only [hz] using (List.getD_map w (0 : Mask) (bit r) (n := i))

def good (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem make_eval (r : Fin 5) (w : List Mask) (g : Gate) (hg : good g) :
    bit r (make w g).val = g.op.eval (g.inputs.map fun i => (w.map (bit r)).getD i false) := by
  have hone : bit r 31 = true := by fin_cases r <;> decide
  rcases g with ⟨op, xs⟩
  obtain ⟨hop, hlen⟩ := hg
  change (op = .and ∨ op = .or ∨ op = .not) at hop
  change xs.length ≤ 2 at hlen
  have hcases : xs = [] ∨ (∃ i, xs = [i]) ∨ ∃ i j, xs = [i,j] := by
    rcases xs with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩ <;> simp_all
  rcases hcases with rfl | ⟨i,rfl⟩ | ⟨i,j,rfl⟩ <;>
    rcases hop with rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, read_bit] <;>
    simp [make, Step.val, GateOp.eval, bit, r.isLt] at hone ⊢ <;> simp_all

theorem run_bit (r : Fin 5) (gs : List Gate) (w : List Mask) (hg : ∀ g ∈ gs, good g) :
    (run gs w).map (bit r) =
      gs.foldl (fun v (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) (w.map (bit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, List.foldl_cons]
    rw [← run, ih _ (fun h hh => hg h (by simp [hh]))]
    simp [make_eval r w g (hg g (by simp))]

theorem get_mem {α : Type} (w : List α) (i : Nat) (d : α) : w.getD i d ∈ w ∨ w.getD i d = d := by
  by_cases hi : i < w.length
  · left
    rw [List.getD_eq_getElem w d hi]
    exact List.getElem_mem _
  · right
    exact List.getD_eq_default w d (Nat.le_of_not_gt hi)

theorem make_operands (w avail : List Mask) (g : Gate) (hw : ∀ z ∈ w, z ∈ avail)
    (h0 : 0 ∈ avail) (h1 : 31 ∈ avail) : (make w g).a ∈ avail ∧ (make w g).b ∈ avail := by
  let xs := g.inputs.map (fun i => w.getD i 0)
  let pad : Mask := if g.op = .and then 31 else 0
  have hp : pad ∈ avail := by dsimp [pad]; split <;> assumption
  have hget (i : Nat) : xs.getD i pad ∈ avail := by
    rcases get_mem xs i pad with hm | he
    · obtain ⟨j,_,h⟩ := List.mem_map.mp hm
      rw [← h]
      rcases get_mem w j 0 with h | h
      · exact hw _ h
      · rw [h]; exact h0
    · rw [he]; exact hp
  exact ⟨hget 0,hget 1⟩

def count (gs : List Gate) : Nat := (gs.filter (fun g => decide (g.op = .not))).length

theorem trace (gs : List Gate) (w avail : List Mask) (used : Bool) (k : Nat)
    (hl : gs.length ≤ k) (hw : ∀ z ∈ w, z ∈ avail) (h0 : 0 ∈ avail) (h1 : 31 ∈ avail)
    (hn : count gs + used.toNat ≤ 1)
    (hf : 3 ∈ run gs w ∧ 12 ∈ run gs w ∧ 5 ∈ run gs w) :
    ∃ ts : List Step, ts.length = k ∧ ok avail used ts := by
  induction k generalizing gs w avail used with
  | zero =>
    have hz : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    exact ⟨[],rfl,hw _ hf.1,hw _ hf.2.1,hw _ hf.2.2⟩
  | succ k ih =>
    rcases gs with _ | ⟨g,gs⟩
    · let t : Step := ⟨false,false,0,0⟩
      obtain ⟨ts,hlen,ht⟩ := ih [] w (t.val :: avail) used (by simp)
        (fun z hz => List.mem_cons_of_mem _ (hw z hz)) (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hn hf
      exact ⟨t :: ts,by simp [hlen],h0,h0,by simp [t],by simpa [t] using ht⟩
    · let t := make w g
      have hbudget : count gs + (used || t.neg).toNat ≤ 1 ∧ ¬ (used = true ∧ t.neg = true) := by
        by_cases h : g.op = .not <;> cases used <;> simp [count, make, t, h] at hn ⊢ <;> omega
      obtain ⟨ha,hb⟩ := make_operands w avail g hw h0 h1
      obtain ⟨ts,hlen,ht⟩ := ih gs (w ++ [t.val]) (t.val :: avail) (used || t.neg)
        (by simpa using hl) (by
          intro z hz
          rcases List.mem_append.mp hz with h | h
          · exact List.mem_cons_of_mem _ (hw z h)
          · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
        (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hbudget.1 hf
      exact ⟨t :: ts,by simp [hlen],ha,hb,hbudget.2,ht⟩

def row (r : Fin 5) (i : Fin 4) : Bool := decide (r.val ≠ i.val)

theorem row_inputs : ∀ r : Fin 5, inputs.map (bit r) = List.ofFn (row r) ++ [false,true] := by
  decide +kernel

theorem row_cover : ∀ (r : Fin 5) (i j : Fin 4), i < j → row r i = true ∨ row r j = true := by
  decide +kernel

theorem lowerBound (hseven : ∀ (t0 t1 t2 t3 t4 t5 t6 : Step),
    ¬ ok inputs false [t0,t1,t2,t3,t4,t5,t6]) (C : Circuit) (a b c : Nat)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hnot : PEqualNP.NotBracket.notCount C ≤ 1)
    (hr : ∀ x : Fin 4 → Bool, (∀ i j : Fin 4, i < j → x i = true ∨ x j = true) →
      let w := C.wires (List.ofFn x ++ [false,true])
      w.getD a false = xor (x 0) (x 1) ∧ w.getD b false = xor (x 2) (x 3) ∧
      w.getD c false = xor (x 0) (x 2)) : 8 ≤ C.size := by
  by_contra! hsmall
  have hgood : ∀ g ∈ C.gates, good g := by
    intro g hg
    obtain ⟨hop,hlen⟩ := hfan g hg
    exact ⟨hop,hlen⟩
  have atTap (w : Nat) (m : Mask) (hnz : m ≠ 0)
      (h : ∀ r : Fin 5, (C.wires (List.ofFn (row r) ++ [false,true])).getD w false = bit r m) :
      m ∈ run C.gates inputs := by
    let ws := run C.gates inputs
    have he : ws.getD w 0 = m := by
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro i hi
      let r : Fin 5 := ⟨i,hi⟩
      change bit r (ws.getD w 0) = bit r m
      rw [← read_bit, show ws.map (bit r) = C.wires (List.ofFn (row r) ++ [false,true]) by
        rw [show ws.map (bit r) = _ from run_bit r C.gates inputs hgood, row_inputs]
        rfl]
      exact h r
    rcases get_mem ws w 0 with hm | hm
    · exact he ▸ hm
    · exact False.elim (hnz (he.symm.trans hm))
  have ha := atTap a 3 (by decide) (fun r => (hr (row r) (row_cover r)).1.trans
    ((show ∀ t : Fin 5, xor (row t 0) (row t 1) = bit t 3 by decide) r))
  have hb := atTap b 12 (by decide) (fun r => (hr (row r) (row_cover r)).2.1.trans
    ((show ∀ t : Fin 5, xor (row t 2) (row t 3) = bit t 12 by decide) r))
  have hc := atTap c 5 (by decide) (fun r => (hr (row r) (row_cover r)).2.2.trans
    ((show ∀ t : Fin 5, xor (row t 0) (row t 2) = bit t 5 by decide) r))
  obtain ⟨ts,hlen,ht⟩ := trace C.gates inputs inputs false 7
    (show C.size ≤ 7 by omega) (fun _ h => h) (by decide) (by decide)
    (show count C.gates + 0 ≤ 1 from hnot) ⟨ha,hb,hc⟩
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨t4, _ | ⟨t5, _ | ⟨t6, _ | ⟨t7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> first | omega | exact hseven _ _ _ _ _ _ _ ht

end PEqualNP.Library.K4Parity
