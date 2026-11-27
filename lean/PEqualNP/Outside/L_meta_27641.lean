import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27641

open PEqualNP.CircuitLowerBounds

def firstGate : Gate := ⟨GateOp.or, [0, 1]⟩
def secondGate : Gate := ⟨GateOp.not, [9]⟩

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def bank (x : Fin 9 → Bool) := step (step (List.ofFn x) firstGate) secondGate

def matchVal (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def lo (i : Fin 9) : Nat := ![162, 97, 80, 132, 68, 66, 20, 12, 10] i
def hi (i : Fin 9) : Nat := ![163, 99, 84, 140, 84, 98, 84, 140, 266] i
def bits (n : Nat) (k : Fin 9) := n.testBit k.val

set_option maxRecDepth 4096 in
theorem witnesses : ∀ i : Fin 9,
    matchVal (bits (lo i)) ≠ matchVal (bits (hi i)) ∧
    ∀ k : Fin 11, k.val ≠ i.val →
      (bank (bits (lo i)))[k.val]? = (bank (bits (hi i)))[k.val]? := by decide

theorem bank_len (x : Fin 9 → Bool) : (bank x).length = 11 := by simp [bank, step]

theorem unchanged (gs : List Gate) (u v : List Bool) (i : Nat)
    (hlen : u.length = v.length)
    (heq : ∀ k, k ≠ i → u[k]? = v[k]?)
    (hmiss : i ∉ gs.flatMap Gate.inputs) :
    ∀ k, k ≠ i → (gs.foldl step u)[k]? = (gs.foldl step v)[k]? := by
  induction gs generalizing u v with
  | nil => exact heq
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hmiss
    have args : (g.inputs.map fun a => u.getD a false) =
        (g.inputs.map fun a => v.getD a false) := by
      apply List.map_congr_left
      intro a ha
      simpa only [List.getD_eq_getElem?_getD] using
        congrArg (fun z : Option Bool => z.getD false) (heq a (by rintro rfl; exact hmiss.1 ha))
    apply ih (step u g) (step v g) (by simp [step, hlen]) _ hmiss.2
    intro k hk
    by_cases h : k < u.length
    · simpa only [step, List.getElem?_append_left h, List.getElem?_append_left (hlen ▸ h)] using heq k hk
    · simp only [step, List.getElem?_append_right (Nat.le_of_not_gt h),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_gt h), hlen, args]

theorem raw (gs : List Gate) (out : Nat) (hout : 9 ≤ out)
    (correct : ∀ x, ((gs.foldl step (bank x)).getD out false) = matchVal x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hmiss
  obtain ⟨hdiff, hp⟩ := witnesses i
  apply hdiff
  rw [← correct, ← correct]
  simp only [List.getD_eq_getElem?_getD]
  apply congrArg (fun z : Option Bool => z.getD false)
  apply unchanged _ _ _ i.val (by simp [bank_len]) _ hmiss out (by omega)
  intro k hk
  by_cases h : k < 11
  · exact hp ⟨k, h⟩ hk
  · simp only [List.getElem?_eq_none (show (bank (bits (lo i))).length ≤ k by rw [bank_len]; omega),
        List.getElem?_eq_none (show (bank (bits (hi i))).length ≤ k by rw [bank_len]; omega)]

theorem slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h₁ := h g (by simp)
    have h₂ := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

def codes : Nat → Nat → List Nat
  | 0, 0 => [0, 0, 49762, 49762, 41044, 41557, 67724, 68237, 34900, 35413, 34402, 34402, 10324, 10837, 6284, 6797, 83107, 5898, 0, 0, 82081, 82081, 0, 0]
  | 0, 1 => [0, 0, 0, 0, 41044, 42581, 49763, 50793, 34900, 36437, 67233, 33890, 10324, 11861, 49763, 7821, 49763, 5386, 0, 0, 49250, 49250, 0, 0]
  | 0, 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 19554, 41044, 41044, 69772, 41044, 7434, 0, 0, 41557, 41044, 0, 0]
  | 0, 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 68237, 67724, 0, 0]
  | 0, 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 34900, 13578, 0, 0, 35413, 34900, 0, 0]
  | 0, 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 33890, 0, 0, 0]
  | 0, 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 10837, 10324, 0, 0]
  | 0, 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 6797, 6284, 0, 0]
  | 0, 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 0, 0, 0]
  | 1, 0 => [0, 0, 49762, 49762, 41044, 41557, 67724, 68237, 34900, 35413, 0, 0, 27220, 27220, 23180, 23180, 82081, 5898, 0, 0, 0, 0, 34402, 34402]
  | 1, 1 => [0, 0, 0, 0, 41044, 42581, 49250, 36962, 34900, 36437, 0, 0, 27732, 27732, 49250, 23692, 49250, 5386, 0, 0, 0, 0, 67233, 49250]
  | 1, 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 0, 0, 19554, 41044, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 41557, 41044]
  | 1, 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 0, 0, 30804, 30804, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 37986, 37986]
  | 1, 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25698, 34900, 34900, 30860, 34900, 13578, 0, 0, 0, 0, 35413, 34900]
  | 1, 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 55436, 26708, 38154, 0, 0, 0, 0, 27221, 26708]
  | 1, 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22668, 70922, 0, 0, 0, 0, 33890, 22668]
  | 1, 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 21770]
  | 2, 0 => [0, 0, 49762, 49762, 41044, 41557, 67724, 68237, 34900, 35413, 34402, 34402, 10324, 10837, 6284, 6797, 0, 0, 0, 0, 0, 0, 82081, 82081]
  | 2, 1 => [0, 0, 0, 0, 41044, 42581, 49763, 50793, 34900, 36437, 67233, 33890, 10324, 11861, 49763, 7821, 0, 0, 0, 0, 0, 0, 49250, 49250]
  | 2, 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 19554, 41044, 41044, 69772, 0, 0, 0, 0, 0, 0, 41557, 41044]
  | 2, 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 0, 0, 0, 0, 0, 0, 68237, 67724]
  | 2, 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 0, 0, 0, 0, 0, 0, 35413, 34900]
  | 2, 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 0, 0, 0, 0, 0, 0, 33890, 21770]
  | 2, 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 0, 0, 0, 0, 0, 0, 10837, 10324]
  | 2, 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6797, 6284]
  | _, _ => []
def binary (o : Bool) (a b : Nat) : Gate :=
  ⟨if o then GateOp.or else GateOp.and, [a,b]⟩

def width (s : Fin 3) := if s = 0 then 11 else 12
def used (s : Fin 3) : List Nat :=
  if s = 0 then [9] else [9, if s = 1 then 5 else 8, 10]

def pre (s : Fin 3) (x : Fin 9 → Bool) :=
  if s = 0 then bank x else step (bank x) (binary true (if s = 1 then 5 else 8) 10)

def special (s : Fin 3) (a b : Nat) (o : Bool) : Prop :=
  s = 0 ∧ (a = 5 ∨ a = 8) ∧ b = 10 ∧ o = true

def collision (s : Fin 3) (a b : Fin 12) (o : Bool) : Prop :=
  let code := (codes s.val a.val).getD (2*b.val + o.toNat) 0
  let x := bits (code / 512)
  let y := bits (code % 512)
  let g := binary o a.val b.val
  matchVal x ≠ matchVal y ∧ ∀ k : Fin 13,
    k.val ∉ used s → k.val ≠ a.val → k.val ≠ b.val →
    (step (pre s x) g)[k.val]? = (step (pre s y) g)[k.val]?

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem certified (s : Fin 3) (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → b.val < width s → a.val ∉ used s → b.val ∉ used s →
    ¬ (s = 0 ∧ (a.val = 5 ∨ a.val = 8) ∧ b.val = 10 ∧ o = true) →
    collision s a b o := by
  fin_cases s <;> fin_cases a <;> unfold collision <;> decide

theorem stable (gs : List Gate) (u v : List Bool) (out : Nat) (hlen : u.length = v.length)
    (heq : ∀ k ∈ out :: gs.flatMap Gate.inputs, u[k]? = v[k]?) :
    (gs.foldl step u)[out]? = (gs.foldl step v)[out]? := by
  induction gs generalizing u v with
  | nil => exact heq _ (by simp)
  | cons g gs ih =>
    have args : (g.inputs.map fun a => u.getD a false) =
        (g.inputs.map fun a => v.getD a false) := by
      apply List.map_congr_left
      intro a ha
      simpa only [List.getD_eq_getElem?_getD] using congrArg
        (fun z : Option Bool => z.getD false) (heq a (by simp [ha]))
    apply ih (step u g) (step v g) (by simp [step, hlen])
    intro k hk
    have old : u[k]? = v[k]? := heq k (by simpa only [List.mem_cons, List.flatMap_cons,
      List.mem_append] using (show k = out ∨ k ∈ g.inputs ∨ k ∈ gs.flatMap Gate.inputs by
        rcases List.mem_cons.mp hk with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)))
    by_cases h : k < u.length
    · simpa only [step, List.getElem?_append_left h, List.getElem?_append_left (hlen ▸ h)] using old
    · simp only [step, List.getElem?_append_right (Nat.le_of_not_gt h),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_gt h), hlen, args]

theorem forceCase (s : Fin 3) (a b : Nat) (o : Bool) (gs : List Gate) (out : Nat)
    (hab : a < b) (hb : b < width s)
    (ha' : a ∉ used s) (hb' : b ∉ used s)
    (hfree : ∀ k ∈ out :: gs.flatMap Gate.inputs, k ∉ a :: b :: used s)
    (correct : ∀ x, (gs.foldl step (step (pre s x) (binary o a b))).getD out false = matchVal x) :
    special s a b o := by
  by_contra bad
  have lim : width s ≤ 12 := by unfold width; split <;> decide
  have hc := certified s ⟨a, by omega⟩ ⟨b, by omega⟩ o hab hb ha' hb' bad
  let code := (codes s.val a).getD (2*b + o.toNat) 0
  let x := bits (code / 512)
  let y := bits (code % 512)
  let u := step (pre s x) (binary o a b)
  let v := step (pre s y) (binary o a b)
  have prelen (z : Fin 9 → Bool) : (pre s z).length = width s := by
    unfold pre width
    split <;> simp [bank_len, step]
  have lu : u.length = width s + 1 := by simp [u, step, prelen]
  have lv : v.length = width s + 1 := by simp [v, step, prelen]
  apply hc.1
  change matchVal x = matchVal y
  rw [← correct, ← correct]
  simp only [List.getD_eq_getElem?_getD]
  apply congrArg (fun z : Option Bool => z.getD false)
  apply stable gs u v out (lu.trans lv.symm)
  intro k hk
  have hn := hfree k hk
  simp only [List.mem_cons, not_or] at hn
  by_cases h : k < 13
  · exact hc.2 ⟨k,h⟩ hn.2.2 hn.1 hn.2.1
  · simp only [List.getElem?_eq_none (show u.length ≤ k by omega),
        List.getElem?_eq_none (show v.length ≤ k by omega)]

theorem shape (g : Gate) (n : Nat) (len : g.inputs.length = 2)
    (h : (g.op = GateOp.not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
       ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a,b])) :
    ∃ a b o, a < b ∧ b < n ∧ g = binary o a b := by
  obtain ⟨op, ins⟩ := g
  rcases h with ⟨_, a, _, hi⟩ | ⟨hop, a, b, hab, hb, hi⟩
  · change ins = [a] at hi
    change ins.length = 2 at len
    simp [hi] at len
  · rcases hop with h | h
    · exact ⟨a,b,false,hab,hb, by cases h; cases hi; rfl⟩
    · exact ⟨a,b,true,hab,hb, by cases h; cases hi; rfl⟩

theorem ruleFourth (s : Fin 3) (p : Nat) (hs : s ≠ 0)
    (hu : used s = [9,p,10]) (hp : p = if s = 1 then 5 else 8)
    (a b : Nat) (o : Bool) (rs : List Gate) (out : Nat)
    (hab : a < b) (hb : b < 12) (hout : 13 ≤ out)
    (hr : (9 :: p :: 10 :: a :: b :: rs.flatMap Gate.inputs).Nodup)
    (correct : ∀ x, (rs.foldl step (step (step (bank x) (binary true p 10)) (binary o a b))).getD out false = matchVal x) : False := by
  simp only [List.nodup_cons, List.mem_cons, not_or] at hr
  have pp : p ≤ 8 := by rw [hp]; split <;> decide
  have h := forceCase s a b o rs out hab (by simpa [width, hs] using hb)
    (by rw [hu]; simp; grind) (by rw [hu]; simp; grind)
    (by intro k hk; rw [hu]; rcases List.mem_cons.mp hk with rfl | h
        · simp; omega
        · simp; grind)
    (by simpa [pre, hs, ← hp] using correct)
  exact hs h.1
end PEqualNP.Outside.L_meta_27641
open PEqualNP.Outside.L_meta_27641 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_27641 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩)) := by
  rintro ⟨C, hfan, hsize, hfun, hout, hnorm, _, hlive, h₁, h₂⟩
  obtain ⟨gs, hgs⟩ : ∃ gs, C.gates = firstGate :: secondGate :: gs := by
    cases he : C.gates with
    | nil => simp [he] at h₁
    | cons a tail =>
      cases tail with
      | nil => simp [he] at h₂
      | cons b gs =>
        simp [he] at h₁ h₂
        exact ⟨gs, by rw [h₁, h₂]; rfl⟩
  simp only [Circuit.size, hgs, List.length_cons] at hsize hout
  have correct : ∀ x, (gs.foldl step (bank x)).getD C.output false = matchVal x := by
    intro x
    have hx := hfun x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = matchVal x at hx
    rw [hgs] at hx
    exact hx
  have cover : (Finset.range (10 + gs.length)).erase 9 ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro w hw
    apply List.mem_toFinset.mpr
    obtain ⟨hw9, hw0⟩ := Finset.mem_erase.mp hw
    have hw' := Finset.mem_range.mp hw0
    by_cases low : w < 9
    · exact raw gs _ (by omega) correct ⟨w, low⟩
    · let j : Fin C.gates.length := ⟨w - 9, by simp [hgs]; omega⟩
      have hj : j.val + 1 < C.gates.length := by simp [j, hgs]; omega
      obtain ⟨k, _, hread⟩ := hlive j hj
      have heq : 9 + j.val = w := by dsimp [j]; omega
      rw [heq] at hread
      have hmem : C.gates.get k ∈ firstGate :: secondGate :: gs :=
        by rw [← hgs]; exact List.get_mem C.gates k
      rcases List.mem_cons.mp hmem with hf | ht
      · rw [hf] at hread
        simp [firstGate] at hread
        omega
      rcases List.mem_cons.mp ht with hs | ht
      · rw [hs] at hread
        simp [secondGate] at hread
        contradiction
      exact List.mem_flatMap_of_mem ht hread
  have cap := slots gs (fun g hg => (hfan g (by rw [hgs]; simp [hg])).2)
  have lower := Finset.card_le_card cover
  have hc : ((Finset.range (10 + gs.length)).erase 9).card = 9 + gs.length := by
    rw [Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
    omega
  rw [hc] at lower
  have bound := List.toFinset_card_le (gs.flatMap Gate.inputs)
  have size : gs.length = 9 := by omega
  have full : (gs.flatMap Gate.inputs).length = 18 := by omega
  have uniq : (gs.flatMap Gate.inputs).Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑(gs.flatMap Gate.inputs) : Multiset Nat))).mp
      (show (gs.flatMap Gate.inputs).toFinset.card = (gs.flatMap Gate.inputs).length by omega)
  have sets := Finset.eq_of_subset_of_card_le cover (by omega)
  have no9 : 9 ∉ gs.flatMap Gate.inputs := by
    intro h
    have := List.mem_toFinset.mpr h
    rw [← sets] at this
    simp at this
  obtain ⟨g, h, rs, rfl⟩ : ∃ g h rs, gs = g :: h :: rs := by
    cases gs with
    | nil => simp at size
    | cons g rest =>
      cases rest with
      | nil => simp at size
      | cons h rs => exact ⟨_,_,_,rfl⟩
  have l1 := (hfan g (by simp [hgs])).2
  have l2 := (hfan h (by simp [hgs])).2
  have l3 := slots rs (fun t ht => (hfan t (by simp [hgs, ht])).2)
  simp only [List.flatMap_cons, List.length_append] at full
  simp only [List.length_cons] at size hout
  have hA := hnorm ⟨2, by simp [hgs]⟩
  have hB := hnorm ⟨3, by simp [hgs]⟩
  simp [hgs] at hA hB
  obtain ⟨a,b,o,hab,hb,rfl⟩ := shape g 11 (by omega) hA
  obtain ⟨c,d,q,hcd,hd,rfl⟩ := shape h 12 (by omega) hB
  have nd : (9 :: a :: b :: c :: d :: rs.flatMap Gate.inputs).Nodup :=
    List.nodup_cons.mpr ⟨no9,uniq⟩
  have hn := nd
  simp only [List.nodup_cons, List.mem_cons, not_or] at hn
  have hout' : 13 ≤ C.output := by omega
  have sp := forceCase 0 a b o (binary q c d :: rs) C.output hab hb
    (by simp [used]; grind) (by simp [used]; grind)
    (by intro k hk
        change k ∈ C.output :: c :: d :: rs.flatMap Gate.inputs at hk
        simp only [List.mem_cons] at hk
        simp [used]; grind)
    correct
  obtain ⟨_, ha, rfl, rfl⟩ := sp
  rcases ha with rfl | rfl
  · exact ruleFourth 1 5 (by decide) rfl rfl c d q rs _ hcd hd hout' nd correct
  · exact ruleFourth 2 8 (by decide) rfl rfl c d q rs _ hcd hd hout' nd correct
