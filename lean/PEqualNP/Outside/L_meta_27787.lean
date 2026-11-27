import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27787_aux

namespace Profiles

abbrev Word := Fin 256

def pm (a : Word) : Bool :=
  let bit : ℕ → Bool := fun i => if i = 0 then true else a.val.testBit (i-1)
  (bit 0 && bit 4 && bit 8) || (bit 0 && bit 5 && bit 7) ||
    (bit 1 && bit 3 && bit 8) || (bit 1 && bit 5 && bit 6) ||
    (bit 2 && bit 3 && bit 7) || (bit 2 && bit 4 && bit 6)

def inside (s a : Word) : ℕ := a.val &&& s.val
def outside (s a : Word) : ℕ := a.val &&& (255 ^^^ s.val)

def Factors (s : Word) : Prop :=
  ∃ h : ℕ → Bool, ∃ g : Bool → ℕ → Bool,
    ∀ a : Word, pm a = g (h (inside s a)) (outside s a)

abbrev ProfileCert := Word × Word × Word × Word × Word × Word

def certOK (s : Word) : ProfileCert → Bool
  | (a,b,c,d,e,f) =>
    inside s a == inside s d && inside s b == inside s e && inside s c == inside s f &&
    outside s a == outside s b && outside s b == outside s c &&
    outside s d == outside s e && outside s e == outside s f &&
    (pm a, pm d) != (pm b, pm e) && (pm b, pm e) != (pm c, pm f) &&
    (pm a, pm d) != (pm c, pm f)

def twoInside (s : Word) : Bool :=
  ((List.finRange 8).filter (fun j => s.val.testBit j.val)).length >= 2

def certificates : List ProfileCert :=
  [
  (48, 49, 50, 56, 57, 58),
  (192, 196, 197, 194, 198, 199),
  (128, 129, 136, 132, 133, 140),
  (192, 196, 198, 193, 197, 199),
  (34, 42, 50, 35, 43, 51),
  (16, 48, 80, 17, 49, 81),
  (33, 49, 161, 41, 57, 169),
  (36, 38, 46, 100, 102, 110),
  (34, 42, 98, 50, 58, 114),
  (5, 37, 133, 21, 53, 149),
  (36, 37, 53, 164, 165, 181),
  (12, 14, 78, 44, 46, 110),
  (132, 133, 196, 134, 135, 198),
  (128, 132, 136, 129, 133, 137),
  (192, 196, 208, 193, 197, 209),
  (40, 42, 56, 41, 43, 57),
  (130, 134, 198, 131, 135, 199),
  (24, 56, 57, 26, 58, 59),
  (4, 132, 133, 12, 140, 141),
  (24, 56, 58, 25, 57, 59),
  (68, 70, 196, 69, 71, 197),
  (66, 70, 98, 74, 78, 106),
  (65, 69, 197, 67, 71, 199),
  (18, 50, 58, 19, 51, 59),
  (4, 132, 140, 5, 133, 141),
  (9, 41, 57, 11, 43, 59),
  (32, 48, 112, 33, 49, 113),
  (6, 70, 134, 7, 71, 135)
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem coverage (s : Word) :
    twoInside s = true → s.val ≠ 255 → certificates.any (certOK s) = true := by
  decide +revert

theorem no_factor (s : Word) (hs : twoInside s = true) (ht : s.val ≠ 255) :
    ¬Factors s := by
  obtain ⟨w,_,hw⟩ := List.any_eq_true.mp (coverage s hs ht)
  rcases w with ⟨a,b,c,d,e,f⟩
  rcases h : certOK s (a,b,c,d,e,f) with _ | _
  · rw [h] at hw
    contradiction
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hw
  rcases hw with ⟨⟨⟨⟨⟨⟨⟨⟨⟨had,hbe⟩,hcf⟩,hab⟩,hbc⟩,hde⟩,hef⟩,hneAB⟩,hneBC⟩,hneAC⟩
  rintro ⟨h,g,hpm⟩
  have profile (x y : Word) (hq : inside s x = inside s y) :
      (pm x,pm y) = (g (h (inside s x)) (outside s x),
        g (h (inside s x)) (outside s y)) := by rw [hpm x, hpm y, ← hq]
  have hcA := (hab.trans hbc).symm
  have hfD := (hde.trans hef).symm
  simp only [profile a d had, profile b e hbe, profile c f hcf, hab.symm, hde.symm, hcA, hfD]
    at hneAB hneBC hneAC
  cases ha : h (inside s a) <;> cases hb : h (inside s b) <;>
    cases hc : h (inside s c) <;> simp_all

def bm (i : Fin 8) : ℕ := 2 ^ i.val

def bit (a : Word) (i : Fin 8) : Bool := a.val.testBit i.val

abbrev Adjacent (i : Fin 8) (a b : Word) : Prop :=
  bit a i = false ∧ bit b i = true ∧
  ∀ j : Fin 8, j ≠ i → bit a j = bit b j

abbrev SwitchRows := Word × Word × Word × Word × Word × Word × Word × Word

abbrev switchOK (i j : Fin 8) (s : SwitchRows) : Prop :=
  let (a00,a10,a01,a11,b00,b10,b01,b11) := s
  i ≠ j ∧
  Adjacent i a00 a10 ∧ Adjacent i a01 a11 ∧ Adjacent j a00 a01 ∧ Adjacent j a10 a11 ∧
  Adjacent i b00 b10 ∧ Adjacent i b01 b11 ∧ Adjacent j b00 b01 ∧ Adjacent j b10 b11 ∧
  pm a00 = false ∧ pm a10 = false ∧ pm a01 = false ∧ pm a11 = true ∧
  pm b00 = false ∧ pm b10 = true ∧ pm b01 = true ∧ pm b11 = true

abbrev onZero (k : Fin 8) (s : SwitchRows) : Prop :=
  let (a00,a10,a01,a11,b00,b10,b01,b11) := s
  bit a00 k = false ∧ bit a10 k = false ∧ bit a01 k = false ∧ bit a11 k = false ∧
  bit b00 k = false ∧ bit b10 k = false ∧ bit b01 k = false ∧ bit b11 k = false

def badPair (k : Fin 8) : Fin 8 × Fin 8 × SwitchRows :=
  ![
  (1, 3, 32, 34, 40, 42, 196, 198, 204, 206),
  (0, 4, 32, 33, 48, 49, 196, 197, 212, 213),
  (3, 5, 2, 10, 34, 42, 145, 153, 177, 185),
  (0, 4, 32, 33, 48, 49, 196, 197, 212, 213),
  (1, 3, 32, 34, 40, 42, 196, 198, 204, 206),
  (2, 6, 2, 6, 66, 70, 145, 149, 209, 213),
  (0, 7, 4, 5, 132, 133, 56, 57, 184, 185),
  (1, 6, 4, 6, 68, 70, 56, 58, 120, 122)
  ] k

set_option maxRecDepth 4096 in
theorem after_fixing_one (k : Fin 8) :
    let (i,j,w) := badPair k
    i ≠ k ∧ j ≠ k ∧ switchOK i j w ∧ onZero k w := by
  fin_cases k <;> decide

end Profiles

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def match3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def g0 : Gate := ⟨.or, [0, 4]⟩
def g1 : Gate := ⟨.or, [1, 9]⟩

def bits (m : ℕ) (j : Fin 9) : Bool := m.testBit j.val

theorem essential_after_prefix (i : Fin 9) :
    ∃ x y : Fin 9 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
      (x 0 || x 4) = (y 0 || y 4) ∧
      (x 1 || (x 0 || x 4)) = (y 1 || (y 0 || y 4)) ∧ match3 x ≠ match3 y := by
  fin_cases i
  · exact ⟨bits 176, bits 177, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 97, bits 99, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 80, bits 84, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 132, bits 140, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 69, bits 85, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 66, bits 98, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 20, bits 84, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 12, bits 140, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 10, bits 266, by decide, by decide, by decide, by decide⟩

def EqExcept (i : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j ≠ i, a.getD j false = b.getD j false

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem append_bit {i : ℕ} {a b : List Bool} (h : EqExcept i a b) (v : Bool) :
    EqExcept i (a ++ [v]) (b ++ [v]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hj' : j < a.length
  · rw [List.getD_append _ _ _ _ hj', List.getD_append _ _ _ _ (h.1 ▸ hj')]
    exact h.2 _ hj
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hj')]
    rw [List.getD_append_right _ _ _ _ (h.1 ▸ Nat.le_of_not_gt hj')]
    rw [h.1]

theorem step_preserve {i : ℕ} {a b : List Bool} (g : Gate)
    (h : EqExcept i a b) (hg : i ∉ g.inputs) : EqExcept i (step a g) (step b g) := by
  have hm : g.inputs.map (fun j => a.getD j false) = g.inputs.map (fun j => b.getD j false) :=
    List.map_congr_left (fun j hj => h.2 j (fun eq => hg (eq ▸ hj)))
  unfold step
  rw [hm]
  exact append_bit h _

theorem fold_preserve {i : ℕ} (gs : List Gate) :
    ∀ {a b : List Bool}, EqExcept i a b → i ∉ gs.flatMap Gate.inputs →
      EqExcept i (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h hg
    have h' : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hg
    exact ih (step_preserve g h h'.1) h'.2

theorem initial_agree {i : Fin 9} {x y : Fin 9 → Bool}
    (h : ∀ j, j ≠ i → x j = y j) : EqExcept i.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases hlt : j < 9
  · have he : (⟨j,hlt⟩ : Fin 9) ≠ i := fun e => hj (congrArg Fin.val e)
    rw [List.getD, List.getD, List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hlt, dif_pos hlt]
    exact h ⟨j,hlt⟩ he
  · rw [List.getD_eq_default, List.getD_eq_default] <;> simp [Nat.le_of_not_gt hlt]

theorem step_input (x : Fin 9 → Bool) (g : Gate) (j : Fin 9) :
    (step (List.ofFn x) g).getD j.val false = x j := by
  rw [step, List.getD_append _ _ _ _ (by simpa using j.isLt)]
  rw [List.getD, List.getElem?_ofFn, dif_pos j.isLt]
  rfl

theorem prefix_eval (x : Fin 9 → Bool) :
    step (step (List.ofFn x) g0) g1 =
      (List.ofFn x) ++ [x 0 || x 4] ++ [x 1 || (x 0 || x 4)] := by
  have hx0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD]
  have hx4 : (List.ofFn x).getD 4 false = x 4 := by simp [List.getD]
  have hx1 : (step (List.ofFn x) g0).getD 1 false = x 1 := step_input x g0 1
  have hm : step (List.ofFn x) g0 = (List.ofFn x) ++ [x 0 || x 4] := by
    change (List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false]]) = _
    rw [hx0,hx4]
    simp [GateOp.eval]
  have hx9 : (step (List.ofFn x) g0).getD 9 false = (x 0 || x 4) := by
    change ((step (List.ofFn x) g0).getD 9 false = (x 0 || x 4))
    rw [hm, List.getD_append_right _ _ _ _ (by simp)]
    simp [List.getD]
  change (step (List.ofFn x) g0 ++
      [GateOp.or.eval [(step (List.ofFn x) g0).getD 1 false, (step (List.ofFn x) g0).getD 9 false]]) = _
  rw [hx1,hx9,hm]
  simp [GateOp.eval]

theorem primary_in_tail (gs : List Gate) (out : ℕ) (hout : 9 ≤ out)
    (hf : ∀ x : Fin 9 → Bool, (Circuit.mk (g0 :: g1 :: gs) out).eval (List.ofFn x) = match3 x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨x,y,hxy,h0,h1,hd⟩ := essential_after_prefix i
  have hp : EqExcept i.val (step (step (List.ofFn x) g0) g1) (step (step (List.ofFn y) g0) g1) := by
    rw [prefix_eval, prefix_eval, ← h1, ← h0]
    exact append_bit (append_bit (initial_agree hxy) _) _
  have h := (fold_preserve gs hp hn).2 out (by have := i.isLt; omega)
  exact hd ((hf x).symm.trans (h.trans (hf y)))

theorem tail_entries (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem fixed_prefix_lower (C : Circuit) (hfan : FanInTwo C)
    (hf : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = match3 x)
    (hout : C.output+1=9+C.size)
    (hused : ∀ j : Fin C.gates.length, j.val+1<C.gates.length →
      ∃ k : Fin C.gates.length, j.val<k.val ∧ 9+j.val∈(C.gates.get k).inputs)
    (h0 : C.gates.head?=some g0) (h1 : C.gates.tail.head?=some g1) :
    11 ≤ C.size := by
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil => simp at h0
  | cons a gs =>
    cases gs with
    | nil => simp at h1
    | cons b gs =>
      have ha : a = g0 := Option.some.inj h0
      have hb : b = g1 := Option.some.inj h1
      subst a
      subst b
      change out+1 = 9+(g0 :: g1 :: gs).length at hout
      simp only [List.length_cons] at hout
      have hreq : (Finset.range (10 + gs.length)).erase 9 ⊆ (gs.flatMap Gate.inputs).toFinset := by
        intro z hz
        obtain ⟨hzneq, hz⟩ := Finset.mem_erase.mp hz
        rw [Finset.mem_range] at hz
        rw [List.mem_toFinset]
        by_cases hz9 : z < 9
        · exact primary_in_tail gs out (by omega) hf ⟨z,hz9⟩
        · let j : Fin (g0 :: g1 :: gs).length := ⟨z-9, by simp; omega⟩
          obtain ⟨k, _, hk⟩ := hused j (by simp [j]; omega)
          let g := (g0 :: g1 :: gs).get k
          have hg : z ∈ g.inputs := by
            have eq : 9+j.val=z := by dsimp [j]; omega
            rwa [eq] at hk
          have hmem : g ∈ g0 :: g1 :: gs := List.get_mem _ _
          have htail : g ∈ gs := by
            rcases List.mem_cons.mp hmem with e | hrest
            · have hh : z ∈ g0.inputs := e ▸ hg
              simp [g0] at hh
              omega
            · rcases List.mem_cons.mp hrest with e | htail
              · have hh : z ∈ g1.inputs := e ▸ hg
                simp [g1] at hh
                omega
              · exact htail
          exact List.mem_flatMap.mpr ⟨g,htail,hg⟩
      have hc := Finset.card_le_card hreq
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega) : 9 ∈ Finset.range (10+gs.length)), Finset.card_range] at hc
      have hlen := (List.toFinset_card_le (gs.flatMap Gate.inputs)).trans
        (tail_entries gs fun g hg => (hfan g (by simp [hg])).2)
      change 11 ≤ (g0 :: g1 :: gs).length
      simp only [List.length_cons]
      omega

open PEqualNP.MetaComplexity

def negF {n : ℕ} : DMFormula n → DMFormula n
  | .lit i s => .lit i (!s)
  | .and a b => .or (negF a) (negF b)
  | .or a b => .and (negF a) (negF b)

def tally {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit j _ => if i=j then 1 else 0
  | .and a b => tally i a + tally i b
  | .or a b => tally i a + tally i b

def substF {n : ℕ} (k : Fin n) (g : DMFormula n) : DMFormula n → DMFormula n
  | .lit j s => if j=k then if s then g else negF g else .lit j s
  | .and a b => .and (substF k g a) (substF k g b)
  | .or a b => .or (substF k g a) (substF k g b)

theorem neg_eval {n : ℕ} (g : DMFormula n) (x : Fin n → Bool) :
    (negF g).eval x = !(g.eval x) := by
  induction g with
  | lit i s => cases s <;> cases h : x i <;> simp [negF, DMFormula.eval, h]
  | and a b ia ib =>
    simp only [negF, DMFormula.eval, ia, ib]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b ia ib =>
    simp only [negF, DMFormula.eval, ia, ib]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem tally_neg {n : ℕ} (i : Fin n) (g : DMFormula n) : tally i (negF g) = tally i g := by
  induction g <;> simp_all [negF, tally]

theorem replace_eval {n : ℕ} (k : Fin n) (g f : DMFormula n) (x : Fin n → Bool) :
    (substF k g f).eval x = f.eval (fun j => if j=k then g.eval x else x j) := by
  induction f with
  | lit j s =>
    cases s <;> by_cases h : j=k <;> simp [substF, DMFormula.eval, neg_eval, h]
  | and a b ia ib => simp [substF, DMFormula.eval, ia, ib]
  | or a b ia ib => simp [substF, DMFormula.eval, ia, ib]

theorem replace_other_count {n : ℕ} {i k : Fin n} (hk : i≠k) (g f : DMFormula n) :
    tally i (substF k g f) = tally i f + tally k f * tally i g := by
  induction f with
  | lit j s =>
    by_cases h : j=k
    · subst j
      cases s <;> simp [substF, tally, tally_neg, hk]
    · have h' : k≠j := fun z => h z.symm
      simp [substF, tally, h, h']
  | and a b ia ib =>
    simp only [substF, tally, ia, ib, Nat.add_mul]
    omega
  | or a b ia ib =>
    simp only [substF, tally, ia, ib, Nat.add_mul]
    omega

theorem replace_self_count {n : ℕ} (k : Fin n) (g f : DMFormula n) :
    tally k (substF k g f) = tally k f * tally k g := by
  induction f with
  | lit j s =>
    by_cases h : j=k
    · subst j
      cases s <;> simp [substF, tally, tally_neg]
    · have h' : k≠j := fun z => h z.symm
      simp [substF, tally, h, h']
  | and a b ia ib => simp [substF, tally, ia, ib, Nat.add_mul]
  | or a b ia ib => simp [substF, tally, ia, ib, Nat.add_mul]

theorem eval_agree {n : ℕ} (f : DMFormula n) (a b : Fin n → Bool)
    (hc : ∀ i, 0 < tally i f → a i = b i) : f.eval a = f.eval b := by
  induction f with
  | lit i s =>
    have h := hc i (by simp [tally])
    simp [DMFormula.eval, h]
  | and x y ix iy =>
    have hx := ix (fun i hi => hc i (by simp only [tally]; omega))
    have hy := iy (fun i hi => hc i (by simp only [tally]; omega))
    simp only [DMFormula.eval, hx, hy]
  | or x y ix iy =>
    have hx := ix (fun i hi => hc i (by simp only [tally]; omega))
    have hy := iy (fun i hi => hc i (by simp only [tally]; omega))
    simp only [DMFormula.eval, hx, hy]

theorem eval_irrelevant {n : ℕ} (f : DMFormula n) (i : Fin n) (a b : Fin n → Bool)
    (hzero : tally i f = 0) (h : ∀ j ≠ i, a j = b j) : f.eval a = f.eval b := by
  apply eval_agree
  intro j hj
  apply h
  intro e
  subst j
  omega

theorem replace_not_present {n : ℕ} (i : Fin n) (g f : DMFormula n) (h : tally i f = 0) :
    substF i g f = f := by
  induction f with
  | lit j s =>
    by_cases e : i=j
    · simp [tally, e] at h
    · have e' : j≠i := fun z => e z.symm
      simp [substF, e']
  | and x y ix iy =>
    simp only [tally] at h
    simp [substF, ix (by omega), iy (by omega)]
  | or x y ix iy =>
    simp only [tally] at h
    simp [substF, ix (by omega), iy (by omega)]

theorem replace_bounded {n : ℕ} (k : Fin n) (g A B : DMFormula n)
    (hlin : tally k A + tally k B ≤ 1) (hback : tally k g = 0) :
    tally k (substF k g A) + tally k (substF k g B) = 0 ∧
    ∀ i ≠ k, tally i (substF k g A) + tally i (substF k g B) ≤
        tally i A + tally i B + tally i g := by
  refine ⟨by simp [replace_self_count, hback], ?_⟩
  intro i hi
  rw [replace_other_count hi, replace_other_count hi]
  have h := Nat.mul_le_mul_right (tally i g) hlin
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

def replaceList {n : ℕ} (l : List (Fin n × DMFormula n)) (f : DMFormula n) : DMFormula n :=
  l.foldl (fun t p => substF p.1 p.2 t) f

def assignmentStep {n : ℕ} (p : Fin n × DMFormula n) (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = p.1 then p.2.eval x else x j

theorem replaceList_eval {n : ℕ} (l : List (Fin n × DMFormula n)) (f : DMFormula n) (x : Fin n → Bool) :
    (replaceList l f).eval x = f.eval (l.foldr assignmentStep x) := by
  induction l generalizing f with
  | nil => rfl
  | cons p l ih =>
    unfold replaceList
    rw [List.foldl_cons]
    change (replaceList l (substF p.1 p.2 f)).eval x = _
    rw [ih, replace_eval]
    rfl

open PEqualNP.MetaComplexity

abbrev PairF (N : ℕ) := DMFormula N × DMFormula N
abbrev Patch (N : ℕ) := Fin N × DMFormula N

def total {N : ℕ} (i : Fin N) (p : PairF N) := tally i p.1 + tally i p.2

def debt {N : ℕ} (i : Fin N) : List (Patch N) → ℕ
  | [] => 0
  | g :: gs => tally i g.2 + debt i gs

def stepPair {N : ℕ} (p : PairF N) (g : Patch N) : PairF N :=
  (substF g.1 g.2 p.1, substF g.1 g.2 p.2)

def fillSecond {N : ℕ} (p : PairF N) (g : Patch N) : PairF N :=
  (p.1, substF g.1 g.2 p.2)

theorem step_total {N : ℕ} (p : PairF N) (g : Patch N)
    (huse : total g.1 p ≤ 1) (hback : tally g.1 g.2 = 0) (i : Fin N) :
    total i (stepPair p g) ≤ total i p + tally i g.2 := by
  obtain ⟨hs,ho⟩ := replace_bounded g.1 g.2 p.1 p.2 huse hback
  by_cases h : i=g.1
  · subst i
    simp [total, stepPair, hs]
  · exact ho i h

theorem second_total {N : ℕ} (p : PairF N) (g : Patch N) (huse : tally g.1 p.2 ≤ 1)
    (i : Fin N) (hne : i ≠ g.1) :
    total i (fillSecond p g) ≤ total i p + tally i g.2 := by
  simp only [total, fillSecond, replace_other_count hne]
  have h := Nat.mul_le_mul_right (tally i g.2) huse
  rw [Nat.one_mul] at h
  omega

theorem budgets_step {N : ℕ} (ex : Fin N) (p : PairF N) (g : Patch N)
    (l : List (Patch N))
    (hg : g.1 ≠ ex) (hback : tally g.1 g.2 = 0)
    (hd : ∀ i ≠ ex, total i p + debt i (g::l) ≤ 1) :
    ∀ i ≠ ex, total i (stepPair p g) + debt i l ≤ 1 := by
  have huse := hd g.1 hg
  have hl : total g.1 p ≤ 1 := by omega
  intro i hi
  have h := step_total p g hl hback i
  have he := hd i hi
  simp only [debt] at he
  omega

theorem budgets_ordinary {N : ℕ} (ex : Fin N) (p : PairF N) (pre post : List (Patch N))
    (h : ∀ g ∈ pre, g.1 ≠ ex ∧ tally g.1 g.2 = 0)
    (hd : ∀ i ≠ ex, total i p + debt i (pre++post) ≤ 1) :
    ∀ i ≠ ex, total i (pre.foldl stepPair p) + debt i post ≤ 1 := by
  induction pre generalizing p with
  | nil => exact hd
  | cons g gs ih =>
    obtain ⟨hn,hb⟩ := h g (by simp)
    apply ih (stepPair p g) (fun x hx => h x (by simp [hx]))
    exact budgets_step ex p g (gs++post) hn hb hd

theorem second_invariant {N : ℕ} (ex : Fin N) (a : DMFormula N) (pre : List (Patch N))
    (h : ∀ g ∈ pre, g.1 ≠ ex) :
    (pre.foldl stepPair (a,DMFormula.lit ex true)).2 = DMFormula.lit ex true := by
  induction pre generalizing a with
  | nil => rfl
  | cons g gs ih =>
    have hn := h g (by simp)
    have he : substF g.1 g.2 (DMFormula.lit ex true) = DMFormula.lit ex true :=
      replace_not_present _ _ _ (by simp [tally, hn])
    simp only [List.foldl_cons, stepPair, he]
    exact ih _ (fun g hg => h g (by simp [hg]))

theorem final_pair_linear {N : ℕ} (ex root : Fin N) (pre post : List (Patch N))
    (gEx : DMFormula N)
    (hpre : ∀ g ∈ pre, g.1 ≠ ex ∧ tally g.1 g.2 = 0)
    (hpost : ∀ g ∈ post, g.1 ≠ ex ∧ tally g.1 g.2 = 0)
    (hd : ∀ i ≠ ex, (if i=root then 1 else 0) + debt i (pre ++ (ex,gEx) :: post) ≤ 1) :
    let p := pre.foldl stepPair (DMFormula.lit root true, DMFormula.lit ex true)
    let final := post.foldl stepPair (fillSecond p (ex,gEx))
    ∀ i ≠ ex, total i final ≤ 1 := by
  let start : PairF N := (DMFormula.lit root true, DMFormula.lit ex true)
  let p := pre.foldl stepPair start
  have hpreB : p.2 = DMFormula.lit ex true := second_invariant ex _ pre (fun g hg => (hpre g hg).1)
  have hp : ∀ i ≠ ex, total i p + debt i ((ex,gEx)::post) ≤ 1 := by
    apply budgets_ordinary ex start pre ((ex,gEx)::post) hpre
    intro i hi
    simpa [start, total, tally, hi] using hd i hi
  have hmid : ∀ i ≠ ex, total i (fillSecond p (ex,gEx)) + debt i post ≤ 1 := by
    intro i hi
    have hlocal : tally ex p.2 ≤ 1 := by simp [hpreB,tally]
    have h := second_total p (ex,gEx) hlocal i hi
    change total i (fillSecond p (ex,gEx)) ≤ total i p + tally i gEx at h
    have hn := hp i hi
    simp only [debt] at hn
    omega
  have hfinal := budgets_ordinary ex (fillSecond p (ex,gEx)) post [] hpost
    (by simpa using hmid)
  simpa [start, p, debt] using hfinal

open PEqualNP.MetaComplexity

theorem replace_preserves_zero {N : ℕ} (i k : Fin N) (f g : DMFormula N)
    (hf : tally i f = 0) (hg : tally i g = 0) : tally i (substF k g f) = 0 := by
  by_cases h : i=k
  · subst i
    simp [replace_self_count,hg]
  · simp [replace_other_count h,hf,hg]

theorem replaceList_zero {N : ℕ} (i : Fin N) (l : List (Patch N)) (f : DMFormula N)
    (hf : tally i f = 0) (hl : ∀ g ∈ l, tally i g.2 = 0) :
    tally i (replaceList l f) = 0 := by
  induction l generalizing f with
  | nil => exact hf
  | cons a l ih =>
    change tally i (replaceList l (substF a.1 a.2 f)) = 0
    apply ih _ (replace_preserves_zero i _ _ _ hf (hl a (by simp)))
    exact fun g hg => hl g (by simp [hg])

theorem remove_key {N : ℕ} (i : Fin N) (g f : DMFormula N)
    (pre post : List (Patch N)) (hg : tally i g = 0)
    (hpost : ∀ a ∈ post, tally i a.2 = 0) :
    tally i (replaceList (pre ++ (i,g)::post) f) = 0 := by
  change tally i ((pre ++ (i,g)::post).foldl (fun t p => substF p.1 p.2 t) f) = 0
  rw [List.foldl_append,List.foldl_cons]
  apply replaceList_zero i post
  · simp [replace_self_count,hg]
  · exact hpost

theorem fold_pair_fst {N : ℕ} (l : List (Patch N)) (a b : DMFormula N) :
    (l.foldl stepPair (a,b)).1 = replaceList l a := by
  induction l generalizing a b with
  | nil => rfl
  | cons p l ih =>
    change (l.foldl stepPair (substF p.1 p.2 a,substF p.1 p.2 b)).1 =
      replaceList l (substF p.1 p.2 a)
    exact ih _ _

theorem fold_pair_snd {N : ℕ} (l : List (Patch N)) (a b : DMFormula N) :
    (l.foldl stepPair (a,b)).2 = replaceList l b := by
  induction l generalizing a b with
  | nil => rfl
  | cons p l ih =>
    change (l.foldl stepPair (substF p.1 p.2 a,substF p.1 p.2 b)).2 =
      replaceList l (substF p.1 p.2 b)
    exact ih _ _

theorem replaceList_append {N : ℕ} (l k : List (Patch N)) (a : DMFormula N) :
    replaceList (l++k) a = replaceList k (replaceList l a) := by simp [replaceList,List.foldl_append]

theorem cut_bundle_forms {N : ℕ} (ex root : Fin N) (gEx : DMFormula N)
    (pre post : List (Patch N)) (h : ∀ g ∈ pre, g.1 ≠ ex) :
    let p := pre.foldl stepPair (DMFormula.lit root true, DMFormula.lit ex true)
    let q := post.foldl stepPair (fillSecond p (ex,gEx))
    q.1 = replaceList (pre++post) (DMFormula.lit root true) ∧ q.2 = replaceList post gEx := by
  let p := pre.foldl stepPair (DMFormula.lit root true, DMFormula.lit ex true)
  have hp : p.2 = DMFormula.lit ex true := second_invariant ex _ pre h
  refine ⟨?_,?_⟩
  · change (post.foldl stepPair (p.1,substF ex gEx p.2)).1 = _
    rw [fold_pair_fst, replaceList_append, fold_pair_fst]
  · change (post.foldl stepPair (p.1,substF ex gEx p.2)).2 = _
    rw [fold_pair_snd,hp]
    simp [substF]

open PEqualNP.MetaComplexity

def asInt (a : Bool) : ℤ := if a then 1 else 0

theorem asInt_nonneg (a : Bool) : 0 ≤ asInt a := by cases a <;> decide
theorem asInt_le (a : Bool) : asInt a ≤ 1 := by cases a <;> decide

theorem asInt_and (a b : Bool) : asInt (a && b) = asInt a * asInt b := by
  cases a <;> cases b <;> rfl

theorem asInt_or (a b : Bool) : asInt (a || b) = asInt a + asInt b - asInt a * asInt b := by
  cases a <;> cases b <;> decide

def patch {N : ℕ} (x : Fin N → Bool) (i : Fin N) (b : Bool) : Fin N → Bool :=
  fun j => if j=i then b else x j

def deriv {N : ℕ} (f : DMFormula N) (i : Fin N) (x : Fin N → Bool) : ℤ :=
  asInt (f.eval (patch x i true)) - asInt (f.eval (patch x i false))

theorem patch_other {N : ℕ} (x : Fin N → Bool) (i j : Fin N) (h : j ≠ i) (a b : Bool) :
    patch x i a j = patch x i b j := by simp [patch,h]

theorem deriv_irrel {N : ℕ} (f : DMFormula N) (i : Fin N) (x : Fin N → Bool)
    (h : tally i f = 0) :
    f.eval (patch x i true) = f.eval (patch x i false) :=
  eval_irrelevant f i _ _ h (fun j hj => patch_other x i j hj _ _)

theorem deriv_and_left {N : ℕ} (a b : DMFormula N) (i : Fin N) (x : Fin N → Bool)
    (hb : tally i b = 0) :
    deriv (.and a b) i x = deriv a i x * asInt (b.eval (patch x i false)) := by
  simp only [deriv, DMFormula.eval, asInt_and, deriv_irrel b i x hb]
  ring

theorem deriv_or_left {N : ℕ} (a b : DMFormula N) (i : Fin N) (x : Fin N → Bool)
    (hb : tally i b = 0) :
    deriv (.or a b) i x = deriv a i x * (1-asInt (b.eval (patch x i false))) := by
  simp only [deriv, DMFormula.eval, asInt_or, deriv_irrel b i x hb]
  ring

theorem and_deriv_swap {N : ℕ} (a b : DMFormula N) (i : Fin N) (x : Fin N → Bool) :
    deriv (.and a b) i x = deriv (.and b a) i x := by simp [deriv, DMFormula.eval, Bool.and_comm]
theorem or_deriv_swap {N : ℕ} (a b : DMFormula N) (i : Fin N) (x : Fin N → Bool) :
    deriv (.or a b) i x = deriv (.or b a) i x := by simp [deriv, DMFormula.eval, Bool.or_comm]

theorem deriv_sign {N : ℕ} (f : DMFormula N) (i : Fin N) (h : tally i f ≤ 1)
    (x y : Fin N → Bool) : 0 ≤ deriv f i x * deriv f i y := by
  induction f with
  | lit k s =>
    by_cases e : k=i
    · subst k
      cases s <;> simp [deriv, DMFormula.eval, patch, asInt]
    · simp [deriv, DMFormula.eval, patch,e]
  | and a b ia ib =>
    simp only [tally] at h
    by_cases hb : tally i b = 0
    · rw [deriv_and_left a b i x hb, deriv_and_left a b i y hb]
      have hsign := ia (by omega)
      have hx := asInt_nonneg (b.eval (patch x i false))
      have hy := asInt_nonneg (b.eval (patch y i false))
      calc
        0 ≤ (deriv a i x * deriv a i y) *
          (asInt (b.eval (patch x i false)) * asInt (b.eval (patch y i false))) :=
            mul_nonneg hsign (mul_nonneg hx hy)
        _ = _ := by ring
    · have ha : tally i a = 0 := by omega
      rw [and_deriv_swap a b i x, and_deriv_swap a b i y,
        deriv_and_left b a i x ha, deriv_and_left b a i y ha]
      have hsign := ib (by omega)
      have hx := asInt_nonneg (a.eval (patch x i false))
      have hy := asInt_nonneg (a.eval (patch y i false))
      calc
        0 ≤ (deriv b i x * deriv b i y) *
          (asInt (a.eval (patch x i false)) * asInt (a.eval (patch y i false))) :=
            mul_nonneg hsign (mul_nonneg hx hy)
        _ = _ := by ring
  | or a b ia ib =>
    simp only [tally] at h
    by_cases hb : tally i b = 0
    · rw [deriv_or_left a b i x hb, deriv_or_left a b i y hb]
      have hsign := ia (by omega)
      have hx := sub_nonneg.mpr (asInt_le (b.eval (patch x i false)))
      have hy := sub_nonneg.mpr (asInt_le (b.eval (patch y i false)))
      calc
        0 ≤ (deriv a i x * deriv a i y) *
          ((1-asInt (b.eval (patch x i false))) * (1-asInt (b.eval (patch y i false)))) :=
            mul_nonneg hsign (mul_nonneg hx hy)
        _ = _ := by ring
    · have ha : tally i a = 0 := by omega
      rw [or_deriv_swap a b i x, or_deriv_swap a b i y,
        deriv_or_left b a i x ha, deriv_or_left b a i y ha]
      have hsign := ib (by omega)
      have hx := sub_nonneg.mpr (asInt_le (a.eval (patch x i false)))
      have hy := sub_nonneg.mpr (asInt_le (a.eval (patch y i false)))
      calc
        0 ≤ (deriv b i x * deriv b i y) *
          ((1-asInt (a.eval (patch x i false))) * (1-asInt (a.eval (patch y i false)))) :=
            mul_nonneg hsign (mul_nonneg hx hy)
        _ = _ := by ring

def mix {N : ℕ} (f : DMFormula N) (i j : Fin N) (x : Fin N → Bool) : ℤ :=
  deriv f i (patch x j true) - deriv f i (patch x j false)

def joinF {N : ℕ} (o : Bool) (a b : DMFormula N) : DMFormula N :=
  if o then .or a b else .and a b

def coefficient (o z : Bool) : ℤ := if o then 1-asInt z else asInt z
def sign (o : Bool) : ℤ := if o then -1 else 1

theorem coef_nonneg (o z : Bool) : 0 ≤ coefficient o z := by
  cases o <;> cases z <;> decide

theorem eval_patch {N : ℕ} (f : DMFormula N) (x : Fin N → Bool) (i : Fin N)
    (b : Bool) (hi : tally i f = 0) : f.eval (patch x i b) = f.eval x :=
  eval_irrelevant f i _ _ hi (fun j hj => by simp [patch,hj])

theorem patch_comm {N : ℕ} (x : Fin N → Bool) (i j : Fin N) (h : i≠j) (a b : Bool) :
    patch (patch x i a) j b = patch (patch x j b) i a := by
  funext k
  by_cases hki : k=i
  · subst k; simp [patch,h]
  · by_cases hkj : k=j
    · subst k; simp [patch,hki]
    · simp [patch,hki,hkj]

theorem deriv_patch_irrel {N : ℕ} (f : DMFormula N) (x : Fin N → Bool) (i j : Fin N)
    (h : i≠j) (b : Bool) (hj : tally j f = 0) :
    deriv f i (patch x j b) = deriv f i x := by
  simp only [deriv]
  rw [patch_comm x j i h.symm, patch_comm x j i h.symm]
  rw [eval_patch f _ j _ hj, eval_patch f _ j _ hj]

theorem join_deriv {N : ℕ} (o : Bool) (a b : DMFormula N) (i : Fin N) (x : Fin N → Bool)
    (hb : tally i b = 0) :
    deriv (joinF o a b) i x = deriv a i x * coefficient o (b.eval (patch x i false)) := by
  cases o
  · exact deriv_and_left a b i x hb
  · exact deriv_or_left a b i x hb

theorem join_mix_swap {N : ℕ} (o : Bool) (a b : DMFormula N) (i j : Fin N) (x : Fin N → Bool) :
    mix (joinF o a b) i j x = mix (joinF o b a) i j x := by
  cases o <;> simp [mix,joinF,and_deriv_swap a b,or_deriv_swap a b]

theorem mix_common {N : ℕ} (o : Bool) (a b : DMFormula N) (i j : Fin N) (h : i≠j)
    (x : Fin N → Bool) (hi : tally i b = 0) (hj : tally j b = 0) :
    mix (joinF o a b) i j x = mix a i j x * coefficient o (b.eval (patch x i false)) := by
  simp only [mix,join_deriv o a b i _ hi]
  rw [patch_comm x j i h.symm, patch_comm x j i h.symm]
  rw [eval_patch b _ j _ hj, eval_patch b _ j _ hj]
  ring

theorem mix_split {N : ℕ} (o : Bool) (a b : DMFormula N) (i j : Fin N) (h : i≠j)
    (x : Fin N → Bool) (hi : tally i b = 0) (hj : tally j a = 0) :
    mix (joinF o a b) i j x = sign o * (deriv a i x * deriv b j x) := by
  simp only [mix,join_deriv o a b i _ hi,deriv_patch_irrel a x i j h _ hj,
    eval_patch b _ i _ hi]
  cases o <;> simp only [coefficient,sign,Bool.false_eq_true,if_false,if_true,deriv] <;> ring

theorem mix_irrel_i {N : ℕ} (f : DMFormula N) (i j : Fin N) (x : Fin N → Bool)
    (hi : tally i f = 0) : mix f i j x = 0 := by
  simp [mix,deriv,deriv_irrel f i _ hi]

theorem mix_irrel_j {N : ℕ} (f : DMFormula N) (i j : Fin N) (h : i≠j) (x : Fin N → Bool)
    (hj : tally j f = 0) : mix f i j x = 0 := by
  simp [mix,deriv_patch_irrel f x i j h _ hj]

theorem mix_step {N : ℕ} (o : Bool) (a b : DMFormula N) (i j : Fin N) (h : i≠j)
    (x y : Fin N → Bool)
    (hi : tally i a + tally i b ≤ 1) (hj : tally j a + tally j b ≤ 1)
    (ha : 0 ≤ mix a i j x * mix a i j y) (hb : 0 ≤ mix b i j x * mix b i j y) :
    0 ≤ mix (joinF o a b) i j x * mix (joinF o a b) i j y := by
  have common (a b : DMFormula N) (ha : 0 ≤ mix a i j x * mix a i j y)
      (hbi : tally i b = 0) (hbj : tally j b = 0) :
      0 ≤ mix (joinF o a b) i j x * mix (joinF o a b) i j y := by
    rw [mix_common o a b i j h x hbi hbj, mix_common o a b i j h y hbi hbj]
    calc
      0 ≤ (mix a i j x * mix a i j y) *
        (coefficient o (b.eval (patch x i false)) * coefficient o (b.eval (patch y i false))) :=
          mul_nonneg ha (mul_nonneg (coef_nonneg _ _) (coef_nonneg _ _))
      _ = _ := by ring
  have split (a b : DMFormula N) (hai : tally i a ≤ 1) (hbj : tally j b ≤ 1)
      (hbi : tally i b = 0) (haj : tally j a = 0) :
      0 ≤ mix (joinF o a b) i j x * mix (joinF o a b) i j y := by
    rw [mix_split o a b i j h x hbi haj, mix_split o a b i j h y hbi haj]
    have ht := mul_nonneg (deriv_sign a i hai x y) (deriv_sign b j hbj x y)
    calc
      0 ≤ (deriv a i x * deriv a i y) * (deriv b j x * deriv b j y) := ht
      _ = _ := by cases o <;> simp [sign] <;> ring
  by_cases hbi : tally i b = 0
  · by_cases hbj : tally j b = 0
    · exact common a b ha hbi hbj
    · exact split a b (by omega) (by omega) hbi (by omega)
  · have hai : tally i a = 0 := by omega
    rw [join_mix_swap o a b i j x, join_mix_swap o a b i j y]
    by_cases haj : tally j a = 0
    · exact common b a hb hai haj
    · exact split b a (by omega) (by omega) hai (by omega)

theorem read_once_no_mix_change {N : ℕ} (f : DMFormula N) (i j : Fin N) (h : i≠j)
    (hi : tally i f ≤ 1) (hj : tally j f ≤ 1) (x y : Fin N → Bool) :
    0 ≤ mix f i j x * mix f i j y := by
  induction f with
  | lit k s =>
    by_cases e : i=k
    · have hh : tally j (.lit k s) = 0 := by simp [tally,show j≠k by omega]
      simp [mix_irrel_j _ _ _ h _ hh]
    · have hh : tally i (.lit k s) = 0 := by simp [tally,e]
      simp [mix_irrel_i _ _ _ _ hh]
  | and a b ia ib =>
    simp only [tally] at hi hj
    exact mix_step false a b i j h x y hi hj (ia (by omega) (by omega)) (ib (by omega) (by omega))
  | or a b ia ib =>
    simp only [tally] at hi hj
    exact mix_step true a b i j h x y hi hj (ia (by omega) (by omega)) (ib (by omega) (by omega))

open PEqualNP.MetaComplexity Profiles

noncomputable def embed {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (w : Word) (j : Fin N) : Bool := by
  classical
  exact if h : ∃ k, ix k = j then bit w (Classical.choose h) else base j

theorem embed_at {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (w : Word) (k : Fin 8) : embed ix base w (ix k) = bit w k := by
  classical
  unfold embed
  split
  · next h =>
    rw [ix.injective (Classical.choose_spec h)]
  · next h => exact False.elim (h ⟨k,rfl⟩)

theorem embed_eq_off {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (a b : Word) (i : Fin 8) (h : Adjacent i a b) (v : Fin N) (hv : v ≠ ix i) :
    embed ix base a v = embed ix base b v := by
  classical
  unfold embed
  split
  · next ha =>
    exact h.2.2 (Classical.choose ha) (fun eq => by
      have q := Classical.choose_spec ha
      rw [eq] at q
      exact hv q.symm)
  · rfl

theorem embed_patch {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (a b : Word) (i : Fin 8) (h : Adjacent i a b) :
    patch (embed ix base a) (ix i) false = embed ix base a ∧
    patch (embed ix base a) (ix i) true = embed ix base b := by
  constructor
  · funext v
    by_cases hv : v=ix i
    · subst v; simp [patch,embed_at,h.1]
    · simp [patch,hv]
  · funext v
    by_cases hv : v=ix i
    · subst v; simp [patch,embed_at,h.2.1]
    · simp [patch,hv,embed_eq_off ix base a b i h v hv]

theorem contradiction_on_zero {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (f : DMFormula N) (k : Fin 8) (hlin : ∀ i ≠ k, tally (ix i) f ≤ 1)
    (hc : ∀ a : Word, bit a k = false → f.eval (embed ix base a) = pm a) : False := by
  have he := after_fixing_one k
  generalize h : badPair k = v at he
  rcases v with ⟨i',j',a00,a10,a01,a11,b00,b10,b01,b11⟩
  rcases he with ⟨hik,hjk,hs,hz⟩
  rcases hs with ⟨hij,haI0,haI1,haJ0,haJ1,hbI0,hbI1,hbJ0,hbJ1,a0,a1,a2,a3,b0,b1,b2,b3⟩
  rcases hz with ⟨za0,za1,za2,za3,zb0,zb1,zb2,zb3⟩
  have hX : mix f (ix i') (ix j') (embed ix base a00) = 1 := by
    unfold mix deriv
    rw [(embed_patch ix base a00 a01 j' haJ0).2,
      (embed_patch ix base a00 a01 j' haJ0).1,
      (embed_patch ix base a01 a11 i' haI1).2,
      (embed_patch ix base a01 a11 i' haI1).1,
      (embed_patch ix base a00 a10 i' haI0).2,
      (embed_patch ix base a00 a10 i' haI0).1,
      hc _ za3, hc _ za2, hc _ za1, hc _ za0, a3,a2,a1,a0]
    decide
  have hY : mix f (ix i') (ix j') (embed ix base b00) = -1 := by
    unfold mix deriv
    rw [(embed_patch ix base b00 b01 j' hbJ0).2,
      (embed_patch ix base b00 b01 j' hbJ0).1,
      (embed_patch ix base b01 b11 i' hbI1).2,
      (embed_patch ix base b01 b11 i' hbI1).1,
      (embed_patch ix base b00 b10 i' hbI0).2,
      (embed_patch ix base b00 b10 i' hbI0).1,
      hc _ zb3, hc _ zb2, hc _ zb1, hc _ zb0, b3,b2,b1,b0]
    decide
  have hbad := read_once_no_mix_change f (ix i') (ix j') (fun q => hij (ix.injective q))
    (hlin _ hik) (hlin _ hjk) (embed ix base a00) (embed ix base b00)
  rw [hX,hY] at hbad
  norm_num at hbad

open PEqualNP.MetaComplexity Profiles

def wordOfBits (f : Fin 8 → Bool) : Word :=
  ⟨(BitVec.ofBoolListLE (List.ofFn f)).toNat, by
    have h := (BitVec.ofBoolListLE (List.ofFn f)).isLt
    simpa only [List.length_ofFn] using h⟩

theorem bits_of_wordOfBits (f : Fin 8 → Bool) (i : Fin 8) :
    bit (wordOfBits f) i = f i := by
  change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i
  rw [BitVec.getLsbD_ofBoolListLE]
  rw [List.getD, List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

theorem ones_mask_bit (i : Fin 8) : (255 : ℕ).testBit i.val = true := by
  fin_cases i <;> decide

theorem inside_bit (s a : Word) (i : Fin 8) (h : bit s i = true) :
    (inside s a).testBit i.val = bit a i := by
  change (a.val &&& s.val).testBit i.val = a.val.testBit i.val
  change s.val.testBit i.val = true at h
  rw [Nat.testBit_and, h, Bool.and_true]

theorem outside_bit (s a : Word) (i : Fin 8) (h : bit s i = false) :
    (outside s a).testBit i.val = bit a i := by
  change (a.val &&& (255 ^^^ s.val)).testBit i.val = a.val.testBit i.val
  change s.val.testBit i.val = false at h
  rw [Nat.testBit_and, Nat.testBit_xor, ones_mask_bit, h]
  simp

noncomputable def embedNat {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (m : ℕ) (j : Fin N) : Bool := by
  classical
  exact if h : ∃ k, ix k = j then m.testBit (Classical.choose h).val else base j

theorem embedNat_at {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (m : ℕ) (i : Fin 8) : embedNat ix base m (ix i) = m.testBit i.val := by
  classical
  unfold embedNat
  split
  · next h => rw [ix.injective (Classical.choose_spec h)]
  · next h => exact False.elim (h ⟨i,rfl⟩)

theorem embedNat_off {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (m n : ℕ) (v : Fin N) (h : ¬∃ k, ix k=v) :
    embedNat ix base m v = embedNat ix base n v := by
  classical
  simp [embedNat,h]

theorem embedNat_word {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool) (w : Word) :
    embedNat ix base w.val = embed ix base w := by rfl

theorem readB_inside {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool) (B : DMFormula N)
    (s a : Word) (hs : ∀ i, 0 < tally (ix i) B → bit s i = true) :
    B.eval (embedNat ix base (inside s a)) = B.eval (embed ix base a) := by
  rw [← embedNat_word ix base a]
  apply eval_agree
  intro v hv
  by_cases h : ∃ i, ix i=v
  · obtain ⟨i,rfl⟩ := h
    simp only [embedNat_at]
    exact inside_bit s a i (hs i hv)
  · exact embedNat_off ix base _ _ _ h

theorem readA_outside {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (A : DMFormula N) (e : Fin N) (v : Bool) (s a : Word)
    (hs : ∀ i, 0 < tally (ix i) A → bit s i = false) :
    A.eval (patch (embedNat ix base (outside s a)) e v) =
      A.eval (patch (embed ix base a) e v) := by
  rw [← embedNat_word ix base a]
  apply eval_agree
  intro j hj
  by_cases he : j=e
  · subst j; simp [patch]
  · simp only [patch,he,ite_false]
    by_cases h : ∃ i, ix i=j
    · obtain ⟨i,rfl⟩ := h
      simp only [embedNat_at]
      exact outside_bit s a i (hs i hj)
    · exact embedNat_off ix base _ _ _ h

theorem cut_makes_factor {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (A B : DMFormula N) (e : Fin N) (s : Word)
    (hA : ∀ i, 0 < tally (ix i) A → bit s i = false)
    (hB : ∀ i, 0 < tally (ix i) B → bit s i = true)
    (hc : ∀ a : Word, A.eval (patch (embed ix base a) e (B.eval (embed ix base a))) = pm a) :
    Factors s := by
  refine ⟨fun m => B.eval (embedNat ix base m),
    fun v m => A.eval (patch (embedNat ix base m) e v), ?_⟩
  intro a
  change pm a = A.eval (patch (embedNat ix base (outside s a)) e (B.eval (embedNat ix base (inside s a))))
  rw [readB_inside ix base B s a hB, readA_outside ix base A e _ s a hA, hc]

open PEqualNP.MetaComplexity Profiles

theorem embed_base_patch {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (e : Fin N) (v : Bool) (he : ¬∃ i, ix i=e) (a : Word) :
    patch (embed ix base a) e v = embed ix (patch base e v) a := by
  classical
  funext j
  by_cases h : ∃ i, ix i=j
  · obtain ⟨i,rfl⟩ := h
    have hh : ix i ≠ e := fun q => he ⟨i,q⟩
    simp [patch,hh,embed_at]
  · simp [patch,embed,h]

theorem embed_equal_off_range {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (a b : Word) (j : Fin N) (h : ¬∃ i, ix i=j) : embed ix base a j=embed ix base b j := by
  classical
  simp [embed,h]

theorem all_h_independent_A {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (A : DMFormula N) (e : Fin N) (a : Word) (v : Bool)
    (ha : ∀ i, tally (ix i) A = 0) :
    A.eval (patch (embed ix base a) e v) = A.eval (patch (embed ix base 0) e v) := by
  apply eval_agree
  intro j hj
  by_cases he : j=e
  · subst j; simp [patch]
  · simp only [patch,he,ite_false]
    exact embed_equal_off_range ix base _ _ j (by
      rintro ⟨i,rfl⟩; rw [ha i] at hj; omega)

theorem two_support {s : Word} {i j : Fin 8} (hne : i ≠ j)
    (hi : bit s i = true) (hj : bit s j = true) : twoInside s = true := by
  let L := (List.finRange 8).filter (fun q => s.val.testBit q.val)
  have hSub : ({i,j} : Finset (Fin 8)) ⊆ L.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa [L,bit] using hi
    · simpa [L,bit] using hj
  have hc := Finset.card_le_card hSub
  have hm := List.toFinset_card_le L
  have hh : ({i,j} : Finset (Fin 8)).card = 2 := by simp [Finset.card_insert_of_notMem,hne]
  rw [hh] at hc
  unfold twoInside
  change decide (2 ≤ L.length) = true
  exact decide_eq_true (hc.trans hm)

theorem no_internal_cut {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (A B : DMFormula N) (e : Fin N) (he : ¬∃ i, ix i=e)
    (hl : ∀ i, tally (ix i) A+tally (ix i) B ≤ 1)
    (hc : ∀ a : Word, A.eval (patch (embed ix base a) e (B.eval (embed ix base a))) = pm a) :
    False := by
  classical
  by_cases hfull : ∀ i : Fin 8, 0 < tally (ix i) B
  · have hA (i : Fin 8) : tally (ix i) A = 0 := by have p := hfull i; have q := hl i; omega
    let g (b : Bool) := A.eval (patch (embed ix base 0) e b)
    have hG (a : Word) : g (B.eval (embed ix base a)) = pm a :=
      (all_h_independent_A ix base A e a _ hA).symm.trans (hc a)
    have hB (i : Fin 8) : tally (ix i) B ≤ 1 := by have q := hl i; omega
    cases h0 : g false <;> cases h1 : g true
    · have all (a : Word) : pm a = false := by
        have ha := hG a
        cases e : B.eval (embed ix base a) <;> simpa [e,h0,h1] using ha.symm
      have hn : pm (136 : Word) ≠ false := by decide
      exact hn (all 136)
    · apply contradiction_on_zero ix base B 0 (fun i _ => hB i)
      intro a _
      have ha := hG a
      cases e : B.eval (embed ix base a) <;> simpa [e,h0,h1] using ha
    · apply contradiction_on_zero ix base (negF B) 0 (fun i _ => by simpa [tally_neg] using hB i)
      intro a _
      rw [neg_eval]
      have ha := hG a
      cases e : B.eval (embed ix base a) <;> simpa [e,h0,h1] using ha
    · have all (a : Word) : pm a = true := by
        have ha := hG a
        cases e : B.eval (embed ix base a) <;> simpa [e,h0,h1] using ha.symm
      have hn : pm (0 : Word) ≠ true := by decide
      exact hn (all 0)
  · push_neg at hfull
    by_cases hbig : ∃ i j : Fin 8, i≠j ∧ 0<tally (ix i) B ∧ 0<tally (ix j) B
    · let s := wordOfBits (fun q => decide (0<tally (ix q) B))
      have hflag (q : Fin 8) : bit s q = decide (0<tally (ix q) B) := bits_of_wordOfBits _ _
      obtain ⟨i,j,hij,hi,hj⟩ := hbig
      have ht := two_support (s:=s) hij (by rw [hflag]; exact decide_eq_true hi)
        (by rw [hflag]; exact decide_eq_true hj)
      have hs : s.val ≠ 255 := by
        intro h
        obtain ⟨k,hk⟩ := hfull
        have hz : bit s k = false := by simp [hflag,show ¬0<tally (ix k) B by omega]
        change s.val.testBit k.val = false at hz
        rw [h,ones_mask_bit] at hz
        contradiction
      apply no_factor s ht hs
      refine cut_makes_factor ix base A B e s ?_ ?_ hc
      · intro q h
        rw [hflag]
        have hq := hl q
        exact decide_eq_false (by omega)
      · intro q h
        simp [hflag,h]
    · have hex : ∃ k : Fin 8, ∀ i ≠ k, tally (ix i) B = 0 := by
        by_cases h : ∃ i : Fin 8, 0<tally (ix i) B
        · obtain ⟨k,hk⟩ := h
          refine ⟨k,fun i hne => ?_⟩
          by_contra hn
          exact hbig ⟨i,k,hne,by omega,hk⟩
        · exact ⟨0,fun i _ => by by_contra hn; exact h ⟨i,by omega⟩⟩
      obtain ⟨k,hk⟩ := hex
      let u := B.eval (embed ix base 0)
      let bx := patch base e u
      apply contradiction_on_zero ix bx A k (fun i _ => by have q := hl i; omega)
      intro a ha
      have hb : B.eval (embed ix base a) = u := by
        apply eval_agree
        intro j hj
        by_cases hj' : ∃ i, ix i=j
        · obtain ⟨i,rfl⟩ := hj'
          have heq : i=k := by by_contra hn; have hh := hk i hn; omega
          subst i
          rw [embed_at,embed_at,ha]
          simp [bit]
        · exact embed_equal_off_range ix base _ _ _ hj'
      rw [← embed_base_patch ix base e u he a, ← hb, hc a]

open PEqualNP.MetaComplexity Profiles

abbrev Descending {N : ℕ} (l : List (Patch N)) :=
  l.Pairwise (fun a b => b.1 < a.1)

abbrev BeforeReads {N : ℕ} (l : List (Patch N)) :=
  ∀ a ∈ l, ∀ i ≥ a.1, tally i a.2 = 0

theorem remove_key_ordered {N : ℕ} (l : List (Patch N)) (i : Fin N) (g f : DMFormula N)
    (hm : (i,g) ∈ l) (hp : Descending l) (hb : BeforeReads l) :
    tally i (replaceList l f) = 0 := by
  obtain ⟨pre,post,h,_⟩ := List.eq_append_cons_of_mem hm
  rw [h]
  apply remove_key i g f pre post (hb _ hm _ (le_refl _))
  intro a ha
  have hs := List.pairwise_cons.mp (List.pairwise_append.mp (h ▸ hp)).2.1
  exact hb a (h ▸ List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))) i
    (le_of_lt (hs.1 _ ha))

theorem fixed_replacements {N : ℕ} (l : List (Patch N)) (f : DMFormula N) (x : Fin N → Bool)
    (h : ∀ a ∈ l, a.2.eval x = x a.1) :
    (replaceList l f).eval x = f.eval x := by
  rw [replaceList_eval]
  suffices he : l.foldr assignmentStep x = x by rw [he]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, ih (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    funext i
    by_cases hi : i=a.1
    · subst i
      simp [assignmentStep,h a (by simp)]
    · simp [assignmentStep,hi]

theorem key_not_in_tail {N : ℕ} {pre post : List (Patch N)} {w : Patch N}
    (ho : Descending (pre++w::post)) :
    (∀ p ∈ pre, w.1 < p.1) ∧ (∀ p ∈ post, p.1 < w.1) := by
  have h := List.pairwise_append.mp ho
  refine ⟨fun p hp => h.2.2 p hp w (by simp), ?_⟩
  exact (List.pairwise_cons.mp h.2.1).1

theorem abstract_terminal {N : ℕ} (ix : Fin 8 ↪ Fin N) (base : Fin N → Bool)
    (l : List (Patch N)) (root ex : Fin N) (actual : Word → Fin N → Bool)
    (hdesc : Descending l) (hback : BeforeReads l)
    (hbudget : ∀ i ≠ ex, (if i=root then 1 else 0)+debt i l ≤ 1)
    (hval : ∀ w p, p ∈ l → p.2.eval (actual w) = actual w p.1)
    (hroot : ∀ w, actual w root = pm w)
    (hbase : ∀ w i, (¬∃ g, (i,g) ∈ l) → actual w i = embed ix base w i)
    (hreal : ∀ j g, (ix j,g) ∉ l) : False := by
  classical
  by_cases he : ∃ g : DMFormula N, (ex,g) ∈ l
  · obtain ⟨gE,hE⟩ := he
    obtain ⟨pre,post,hL,_⟩ := List.eq_append_cons_of_mem hE
    let p := pre.foldl stepPair (DMFormula.lit root true,DMFormula.lit ex true)
    let q := post.foldl stepPair (fillSecond p (ex,gE))
    have hL' : Descending (pre++(ex,gE)::post) := hL ▸ hdesc
    have hh := key_not_in_tail hL'
    have hp : ∀ a ∈ pre, a.1 ≠ ex ∧ tally a.1 a.2 = 0 := by
      intro a ha
      exact ⟨ne_of_gt (hh.1 a ha), hback a (hL ▸ List.mem_append.mpr (Or.inl ha)) _ (le_refl _)⟩
    have hs : ∀ a ∈ post, a.1 ≠ ex ∧ tally a.1 a.2 = 0 := by
      intro a ha
      exact ⟨ne_of_lt (hh.2 a ha), hback a (hL ▸ List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))) _ (le_refl _)⟩
    have hlin := final_pair_linear ex root pre post gE hp hs (hL ▸ hbudget)
    have hforms := cut_bundle_forms ex root gE pre post (fun a ha => (hp a ha).1)
    let A := q.1
    let B := q.2
    have hAform : A = replaceList (pre++post) (DMFormula.lit root true) := hforms.1
    have hBform : B = replaceList post gE := hforms.2
    have hA0 (i : Fin N) (g : DMFormula N) (hi : i≠ex) (hm : (i,g)∈l) : tally i A = 0 := by
      rw [hAform]
      have hsub : List.Sublist (pre++post) l := by
        rw [hL]
        exact (List.sublist_cons_self _ _).append_left pre
      apply remove_key_ordered (pre++post) i g _ ?_ (hdesc.sublist hsub)
        (fun a ha => hback a (hsub.subset ha))
      rw [hL, List.mem_append, List.mem_cons] at hm
      rcases hm with hp | hn | hs
      · exact List.mem_append.mpr (Or.inl hp)
      · exact False.elim (hi (congrArg Prod.fst hn))
      · exact List.mem_append.mpr (Or.inr hs)
    have hB0 (i : Fin N) (g : DMFormula N) (hm : (i,g)∈l) : tally i B = 0 := by
      rw [hBform]
      by_cases hpos : (i,g) ∈ post
      · have hsub : List.Sublist post l := by rw [hL]; exact (List.sublist_cons_self _ _).trans (List.sublist_append_right _ _)
        exact remove_key_ordered post i g _ hpos (hdesc.sublist hsub)
          (fun a ha => hback a (hsub.subset ha))
      · have hir : ex ≤ i := by
          rw [hL,List.mem_append,List.mem_cons] at hm
          rcases hm with hp | hb | ht
          · exact (hh.1 (i,g) hp).le
          · exact le_of_eq (congrArg Prod.fst hb).symm
          · exact False.elim (hpos ht)
        apply replaceList_zero i post gE (hback (ex,gE) hE i hir)
        intro a ha
        exact hback a (hL ▸ List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))) i
          (le_trans (hh.2 a ha).le hir)
    have hBval (a : Word) : B.eval (embed ix base a) = actual a ex := by
      calc
        _ = B.eval (actual a) := by
          apply eval_agree
          intro i hi
          exact (hbase a i (by rintro ⟨g,hg⟩; rw [hB0 i g hg] at hi; omega)).symm
        _ = gE.eval (actual a) := by
          rw [hBform]
          exact fixed_replacements post gE _ (fun z hz => hval a z
            (hL ▸ List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hz))))
        _ = _ := hval a _ hE
    apply no_internal_cut ix base A B ex (by rintro ⟨j,hj⟩; exact hreal j gE (hj ▸ hE))
    · intro j
      apply hlin
      exact fun e => hreal j gE (e ▸ hE)
    · intro a
      rw [hBval]
      calc
        _ = A.eval (actual a) := by
          apply eval_agree
          intro i hi
          by_cases hh : i=ex
          · subst i; simp [patch]
          · simp only [patch,hh,ite_false]
            exact (hbase a i (by rintro ⟨g,hg⟩; rw [hA0 i g hh hg] at hi; omega)).symm
        _ = actual a root := by
          rw [hAform]
          have sub : List.Sublist (pre++post) l := by
            rw [hL]
            exact (List.sublist_cons_self _ _).append_left pre
          rw [fixed_replacements _ _ _ (fun z hz => hval a z (sub.subset hz))]
          simp [DMFormula.eval]
        _ = _ := hroot a
  · let A := replaceList l (DMFormula.lit root true)
    have hA0 (i : Fin N) (g : DMFormula N) (hm : (i,g)∈l) : tally i A = 0 :=
      remove_key_ordered l i g _ hm hdesc hback
    have hlin (i : Fin N) (hi : i≠ex) : tally i A ≤ 1 := by
      let init : PairF N := (DMFormula.lit root true,DMFormula.lit ex true)
      have h := budgets_ordinary ex init l []
        (fun a ha => ⟨fun hh => by
          have e : a = (ex,a.2) := Prod.ext hh rfl
          exact he ⟨a.2,e ▸ ha⟩,
          hback a ha _ (le_refl _)⟩)
        (by intro j hj; simpa [init,total,tally,hj] using hbudget j hj)
        i hi
      simp only [debt, Nat.add_zero, total, init, fold_pair_fst] at h
      exact (Nat.le_add_right _ _).trans h
    have hc (a : Word) : A.eval (embed ix base a) = pm a := by
      calc
        _ = A.eval (actual a) := by
          apply eval_agree
          intro i hi
          exact (hbase a i (by rintro ⟨g,hg⟩; rw [hA0 i g hg] at hi; omega)).symm
        _ = actual a root := by
          dsimp [A]
          rw [fixed_replacements _ _ _ (hval a)]
          simp [DMFormula.eval]
        _ = _ := hroot a
    by_cases hEx : ∃ j, ix j=ex
    · obtain ⟨j,hj⟩ := hEx
      exact contradiction_on_zero ix base A j (fun i hi => hlin _ (fun e => hi (ix.injective (e.trans hj.symm)))) (fun a _ => hc a)
    · exact contradiction_on_zero ix base A 0 (fun i _ => hlin _ (fun e => hEx ⟨i,e⟩)) (fun a _ => hc a)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def readNat {N : ℕ} (v : Fin N → Bool) (i : ℕ) :=
  if h : i < N then v ⟨i,h⟩ else false

abbrev gateShape (g : Gate) (bound : ℕ) :=
  (g.op = .not ∧ ∃ a, a < bound ∧ g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < bound ∧ g.inputs = [a,b])

theorem gate_formula {N : ℕ} (g : Gate) (k : Fin N) (h : gateShape g k.val) :
    ∃ f : DMFormula N, (∀ v, f.eval v = g.op.eval (g.inputs.map (readNat v))) ∧
      (∀ i, tally i f = g.inputs.count i.val) ∧ (∀ i ≥ k, tally i f = 0) := by
  rcases h with ⟨hop,a,ha,hg⟩ | ⟨hop,a,b,hab,hb,hg⟩
  · let x : Fin N := ⟨a,ha.trans k.isLt⟩
    refine ⟨.lit x false, ?_, ?_, ?_⟩
    · intro v
      simp [DMFormula.eval,hop,hg,GateOp.eval,readNat,ha.trans k.isLt,x]
    · intro i
      have hi : i=x ↔ i.val=a := Fin.ext_iff
      have hh : a=i.val ↔ i.val=a := eq_comm
      by_cases he : i.val=a <;> simp [tally,hg,hi,hh,he]
    · intro i hi
      have hne : i≠x := by intro e; subst i; change k.val ≤ a at hi; omega
      simp [tally,hne]
  · have ha : a < k.val := hab.trans hb
    let x : Fin N := ⟨a,ha.trans k.isLt⟩
    let y : Fin N := ⟨b,hb.trans k.isLt⟩
    have hcount (i : Fin N) :
        tally i (.lit x true) + tally i (.lit y true) = g.inputs.count i.val := by
      have hix : i=x ↔ i.val=a := Fin.ext_iff
      have hiy : i=y ↔ i.val=b := Fin.ext_iff
      have e₁ : a=i.val ↔ i.val=a := eq_comm
      have e₂ : b=i.val ↔ i.val=b := eq_comm
      simp only [tally,hg,hix,hiy,List.count_cons,List.count_nil,beq_iff_eq,e₁,e₂]
      split <;> split <;> simp_all
    have hv (i : Fin N) (hi : k ≤ i) : tally i (.lit x true) + tally i (.lit y true) = 0 := by
      have hx : i≠x := by intro e; subst i; change k.val ≤ a at hi; omega
      have hy : i≠y := by intro e; subst i; change k.val ≤ b at hi; omega
      simp [tally,hx,hy]
    rcases hop with hA | hO
    · refine ⟨.and (.lit x true) (.lit y true), ?_, hcount, hv⟩
      intro v
      simp [DMFormula.eval,hA,hg,GateOp.eval,readNat,ha.trans k.isLt,hb.trans k.isLt,x,y]
    · refine ⟨.or (.lit x true) (.lit y true), ?_, hcount, hv⟩
      intro v
      simp [DMFormula.eval,hO,hg,GateOp.eval,readNat,ha.trans k.isLt,hb.trans k.isLt,x,y]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons,ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t,ht,hl⟩ := fold_prefix gs w
  rw [ht]
  simp [hl]

theorem fold_before (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t,ht,_⟩ := fold_prefix gs w
  rw [ht,List.getD_append _ _ _ _ hi]

theorem fold_gate_value (gs : List Gate) (w : List Bool) (j : Fin gs.length)
    (hback : ∀ i∈(gs.get j).inputs, i < w.length + j.val) :
    (gs.foldl step w).getD (w.length+j.val) false =
      (gs.get j).op.eval ((gs.get j).inputs.map fun i => (gs.foldl step w).getD i false) := by
  have hsplit : gs = gs.take j.val ++ gs.get j :: gs.drop (j.val+1) := by
    simp
  let p := (gs.take j.val).foldl step w
  let g := gs.get j
  have hp : p.length = w.length+j.val := by
    dsimp [p]
    rw [fold_length,List.length_take,Nat.min_eq_left j.isLt.le]
  have hh : gs.foldl step w = (gs.drop (j.val+1)).foldl step (step p g) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append,List.foldl_cons]
  have hstep : (step p g).length = w.length+j.val+1 := by simp [step,hp]
  have hm : g.inputs.map (fun i => (gs.foldl step w).getD i false)
      = g.inputs.map (fun i => p.getD i false) := by
    apply List.map_congr_left
    intro i hi
    have ht := hback i hi
    rw [hh,fold_before _ _ _ (by omega),step,List.getD_append _ _ _ _ (by omega)]
  change (gs.foldl step w).getD (w.length+j.val) false =
    g.op.eval (g.inputs.map (fun i => (gs.foldl step w).getD i false))
  rw [hm,hh,fold_before _ _ _ (by omega),step,List.getD_append_right _ _ _ _ (by omega),hp]
  simp [List.getD]

theorem read_final {N : ℕ} (l : List Bool) (hl : l.length=N) (i : ℕ) :
    readNat (fun j : Fin N => l.getD j.val false) i = l.getD i false := by
  unfold readNat
  split
  · rfl
  · symm
    apply List.getD_eq_default
    omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators
theorem excess_bound (l : List ℕ) (h : l.length ≤ l.toFinset.card + 1) :
    ∑ x ∈ l.toFinset, (l.count x - 1) ≤ 1 := by
  have hcount : (∑ x ∈ l.toFinset, ((l.count x - 1) + 1)) = l.length := by
    rw [← List.sum_toFinset_count_eq_length l]
    apply Finset.sum_congr rfl
    intro x hx
    have hpos := List.count_pos_iff.mpr (List.mem_toFinset.mp hx)
    omega
  rw [Finset.sum_add_distrib] at hcount
  simp at hcount
  omega

theorem at_most_one_share (l : List ℕ) (h : l.length ≤ l.toFinset.card + 1) :
    (∀ x : ℕ, l.count x ≤ 2) ∧
      ∀ x y : ℕ, 1 < l.count x → 1 < l.count y → x = y := by
  have he := excess_bound l h
  constructor
  · intro x
    by_cases hx : x ∈ l
    · have hx' : x ∈ l.toFinset := List.mem_toFinset.mpr hx
      have hm : l.count x - 1 ≤ ∑ z ∈ l.toFinset, (l.count z - 1) :=
        Finset.single_le_sum (f := fun z : ℕ => l.count z - 1) (fun _ _ => Nat.zero_le _) hx'
      omega
    · simpa [List.count_eq_zero_of_not_mem hx]
  · intro x y hx hy
    by_contra hn
    have hm : {x,y} ⊆ l.toFinset := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl|rfl
      · exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
      · exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
    have hs : (∑ z ∈ ({x,y}:Finset ℕ), (l.count z - 1)) ≤
        ∑ z ∈ l.toFinset, (l.count z - 1) := Finset.sum_le_sum_of_subset_of_nonneg hm (by omega)
    simp [Finset.sum_insert, hn] at hs
    omega

theorem tail_linear_if_twelve (gs : List Gate) (out : ℕ) (ht : gs.length ≤ 10)
    (hfan : FanInTwo (Circuit.mk (g0 :: g1 :: gs) out))
    (hf : ∀ x : Fin 9 → Bool, (Circuit.mk (g0 :: g1 :: gs) out).eval (List.ofFn x) = match3 x)
    (hout : out+1=9+(g0 :: g1 :: gs).length)
    (hused : ∀ j : Fin (g0 :: g1 :: gs).length, j.val+1<(g0 :: g1 :: gs).length →
      ∃ k : Fin (g0 :: g1 :: gs).length, j.val<k.val ∧ 9+j.val∈((g0 :: g1 :: gs).get k).inputs) :
    let L := gs.flatMap Gate.inputs
    (∀ x : ℕ, L.count x ≤ 2) ∧ ∀ x y : ℕ, 1 < L.count x → 1 < L.count y → x = y := by
  simp only [List.length_cons] at hout
  have hreq : (Finset.range (10 + gs.length)).erase 9 ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro z hz
    obtain ⟨hzneq, hz⟩ := Finset.mem_erase.mp hz
    rw [Finset.mem_range] at hz
    rw [List.mem_toFinset]
    by_cases hz9 : z < 9
    · exact primary_in_tail gs out (by omega) hf ⟨z,hz9⟩
    · let j : Fin (g0 :: g1 :: gs).length := ⟨z-9, by simp; omega⟩
      obtain ⟨k, _, hk⟩ := hused j (by simp [j]; omega)
      let g := (g0 :: g1 :: gs).get k
      have hg : z ∈ g.inputs := by
        have eq : 9+j.val=z := by dsimp [j]; omega
        rwa [eq] at hk
      have hmem : g ∈ g0 :: g1 :: gs := List.get_mem _ _
      have htail : g ∈ gs := by
        rcases List.mem_cons.mp hmem with e | hrest
        · have hh : z ∈ g0.inputs := e ▸ hg
          simp [g0] at hh
          omega
        · rcases List.mem_cons.mp hrest with e | htail
          · have hh : z ∈ g1.inputs := e ▸ hg
            simp [g1] at hh
            omega
          · exact htail
      exact List.mem_flatMap.mpr ⟨g,htail,hg⟩
  have hc := Finset.card_le_card hreq
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega) : 9 ∈ Finset.range (10+gs.length)),
    Finset.card_range] at hc
  have hlen := tail_entries gs fun g hg => (hfan g (by simp [hg])).2
  exact at_most_one_share _ (by omega)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem count_flat (gs : List Gate) (i : ℕ) :
    (gs.flatMap Gate.inputs).count i = (gs.map (fun g => g.inputs.count i)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.flatMap_cons,List.count_append,ih]

theorem debt_sum {N : ℕ} (i : Fin N) (l : List (Patch N)) :
    debt i l = (l.map (fun p => tally i p.2)).sum := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [debt,ih]

def restrictedInput (a : Word) : Fin 9 → Bool :=
  Fin.cases true (fun j => bit a j)

theorem pm_restricted (a : Word) : match3 (restrictedInput a) = pm a := by rfl

theorem getD_ofFn_fin {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD,List.getElem?_ofFn,dite_eq_left i.isLt]
  rfl

theorem shape_back (g : Gate) (b : ℕ) (h : gateShape g b) :
    ∀ i ∈ g.inputs, i < b := by
  rcases h with ⟨_,a,ha,he⟩ | ⟨_,a,c,ha,hc,he⟩
  · rw [he]
    intro i hi
    rw [List.mem_singleton.mp hi]
    exact ha
  · rw [he]
    intro i hi
    rcases List.mem_cons.mp hi with rfl | h
    · exact ha.trans hc
    · rw [List.mem_singleton.mp h]
      exact hc

theorem nested_impossible (gs : List Gate) (out : ℕ) (hl : gs.length≤10)
    (hfan : FanInTwo (Circuit.mk (g0::g1::gs) out))
    (hf : ∀ x : Fin 9 → Bool, (Circuit.mk (g0::g1::gs) out).eval (List.ofFn x)=match3 x)
    (hout : out+1=9+(g0::g1::gs).length)
    (hused : ∀ j : Fin (g0::g1::gs).length, j.val+1<(g0::g1::gs).length →
      ∃ k : Fin (g0::g1::gs).length, j.val<k.val ∧ 9+j.val∈((g0::g1::gs).get k).inputs)
    (hshape : ∀ j : Fin gs.length, gateShape (gs.get j) (11+j.val)) :
    False := by
  classical
  let N := 11+gs.length
  have hout' : out+1=N := by simpa [N,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hout
  let root : Fin N := ⟨out, by omega⟩
  let ix : Fin 8 ↪ Fin N :=
    ⟨fun j => ⟨j.val+1,by dsimp [N]; have := j.isLt; omega⟩,
      fun a b e => Fin.ext (by have h:=congrArg Fin.val e; change a.val+1=b.val+1 at h; omega)⟩
  let base (j : Fin N) : Bool := decide (j.val=0 ∨ j.val=9 ∨ j.val=10)
  let key (j : Fin gs.length) : Fin N := ⟨11+j.val, by dsimp [N]; have := j.isLt; omega⟩
  let f (j : Fin gs.length) := Classical.choose (gate_formula (gs.get j) (key j) (hshape j))
  have fprop (j : Fin gs.length) := Classical.choose_spec (gate_formula (gs.get j) (key j) (hshape j))
  let patchAt (j : Fin gs.length) : Patch N := (key j, f j)
  let ps := (List.ofFn patchAt).reverse
  have memP (p : Patch N) : p ∈ ps ↔ ∃ j, patchAt j = p := by
    rw [show ps=(List.ofFn patchAt).reverse from rfl,List.mem_reverse,List.mem_ofFn]
  have hdesc : Descending ps := by
    apply List.pairwise_reverse.mpr
    apply List.pairwise_ofFn.mpr
    intro i j hij
    change 11 + i.val < 11 + j.val
    exact Nat.add_lt_add_left hij _
  have hback : BeforeReads ps := by
    intro p hp
    obtain ⟨j,rfl⟩ := (memP p).mp hp
    exact (fprop j).2.2
  have hcount (i : Fin N) : debt i ps = (gs.flatMap Gate.inputs).count i.val := by
    rw [debt_sum, count_flat]
    change ((List.ofFn patchAt).reverse.map (fun p => tally i p.2)).sum = _
    rw [List.map_reverse,List.sum_reverse,List.map_ofFn,← List.ofFn_getElem_eq_map]
    congr 1
    apply congrArg (List.ofFn : (Fin gs.length → ℕ) → List ℕ)
    funext j
    exact (fprop j).2.1 i
  have ha : (∀ i : ℕ, (gs.flatMap Gate.inputs).count i ≤ 2) ∧
      ∀ i j : ℕ, 1<(gs.flatMap Gate.inputs).count i → 1<(gs.flatMap Gate.inputs).count j → i=j :=
    tail_linear_if_twelve gs out hl hfan hf hout hused
  let ex : Fin N := if h : ∃ i : Fin N, 1 < debt i ps then Classical.choose h else root
  have honce (i : Fin N) (hi : i≠ex) : debt i ps ≤ 1 := by
    by_contra h
    have hpos : 1 < debt i ps := by omega
    have he : ∃ j : Fin N, 1<debt j ps := ⟨i,hpos⟩
    have hEx : 1<debt ex ps := by
      change 1 < debt (if h : ∃ i : Fin N, 1 < debt i ps then Classical.choose h else root) ps
      rw [dite_eq_left he]
      exact Classical.choose_spec he
    rw [hcount] at hpos hEx
    exact hi (Fin.ext (ha.2 _ _ hpos hEx))
  have hrootNo : debt root ps = 0 := by
    rw [hcount]
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨g,hg,hr⟩ := List.mem_flatMap.mp hm
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
    have hrd := shape_back (gs.get j) (11+j.val) (hshape j)
    have hh := hrd out (hj.symm ▸ hr)
    have hjb := j.isLt
    dsimp [N] at hout'
    omega
  have hbudget : ∀ i : Fin N, i≠ex → (if i=root then 1 else 0)+debt i ps ≤ 1 := by
    intro i hi
    by_cases hx : i=root
    · subst i; simp [hrootNo]
    · simp [hx,honce i hi]
  let front (a : Word) := (List.ofFn (restrictedInput a)) ++ [true] ++ [true]
  have hfront (a : Word) : (front a).length=11 := by simp [front]
  let full (a : Word) := gs.foldl step (front a)
  have hlf (a : Word) : (full a).length=N := by simp [full,fold_length,hfront,N]
  let actual (a : Word) (i : Fin N) := (full a).getD i.val false
  have hval (a : Word) (p : Patch N) (hp : p∈ps) :
      p.2.eval (actual a) = actual a p.1 := by
    obtain ⟨j,rfl⟩ := (memP p).mp hp
    have hh : ∀ i∈(gs.get j).inputs, i<(front a).length+j.val := by
      rw [hfront]
      exact shape_back (gs.get j) (11+j.val) (hshape j)
    have hg := fold_gate_value gs (front a) j hh
    rw [hfront] at hg
    change (f j).eval (actual a) = (full a).getD (11+j.val) false
    rw [(fprop j).1]
    have hm : (gs.get j).inputs.map (readNat (actual a)) =
        (gs.get j).inputs.map (fun i => (full a).getD i false) :=
      List.map_congr_left (fun i _ => read_final _ (hlf a) i)
    rwa [hm,← hg]
  have hrootV (a : Word) : actual a root=pm a := by
    have ho := hf (restrictedInput a)
    change ((gs.foldl step (step (step (List.ofFn (restrictedInput a)) g0) g1)).getD out false) =
      match3 (restrictedInput a) at ho
    rw [prefix_eval] at ho
    have h00 : (restrictedInput a) 0 = true := rfl
    simp only [h00,Bool.true_or,Bool.or_true] at ho
    exact ho.trans (pm_restricted a)
  apply abstract_terminal ix base ps root ex actual hdesc hback hbudget hval hrootV
  · intro a i hi
    have hb : i.val<11 := by
      by_contra nh
      have hl' := i.isLt
      let j : Fin gs.length := ⟨i.val-11,by dsimp [N] at hl'; omega⟩
      have he : key j=i := Fin.ext (by change 11+(i.val-11)=i.val; omega)
      exact hi ⟨f j,(memP _).mpr ⟨j, by exact Prod.ext he rfl⟩⟩
    have hv := fold_before gs (front a) i.val (by rw [hfront]; exact hb)
    change (full a).getD i.val false = embed ix base a i
    rw [hv]
    by_cases him : ∃ j, ix j=i
    · obtain ⟨j,rfl⟩ := him
      rw [embed_at]
      let jj : Fin 9 := j.succ
      have hsmall : (ix j).val < (List.ofFn (restrictedInput a)).length := by
        change j.val+1 < _
        rw [List.length_ofFn]
        have := j.isLt
        omega
      have hmid : (ix j).val < (List.ofFn (restrictedInput a) ++ [true]).length :=
        hsmall.trans_le (by simp)
      unfold front
      rw [List.getD_append _ _ _ _ hmid,List.getD_append _ _ _ _ hsmall]
      exact getD_ofFn_fin (restrictedInput a) jj
    · have hn : i.val=0 ∨ i.val=9 ∨ i.val=10 := by
        by_contra no
        have hp1 : (1 : ℕ) ≤ i.val := by omega
        let j : Fin 8 := ⟨i.val-1,by omega⟩
        exact him ⟨j,Fin.ext (by change (i.val-1)+1=i.val; omega)⟩
      have hEmbed : embed ix base a i = true := by
        unfold embed
        rw [dite_eq_right him]
        exact decide_eq_true hn
      rw [hEmbed]
      rcases hn with h | h | h <;> rw [h] <;> simp [front, List.getD, restrictedInput]
  · intro j g hm
    obtain ⟨k,hk⟩ := (memP _).mp hm
    have he := congrArg (fun p : Patch N => p.1.val) hk
    change 11+k.val=j.val+1 at he
    have := j.isLt
    omega

end PEqualNP.Outside.L_meta_27787_aux

open PEqualNP.Outside.L_meta_27787_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_27787 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩) := by
  rintro ⟨⟨gs,out⟩, hfan,hsize,hf,hout,hnormal,_,hused,h0,h1⟩
  cases gs with
  | nil => simp at h0
  | cons a gs =>
    cases gs with
    | nil => simp at h1
    | cons b gs =>
      have ha : a = g0 := Option.some.inj h0
      have hb : b = g1 := Option.some.inj h1
      subst a
      subst b
      have hs : gs.length ≤ 10 := by
        change (g0 :: g1 :: gs).length ≤ 12 at hsize
        simp only [List.length_cons] at hsize
        omega
      apply nested_impossible gs out hs hfan hf hout hused
      intro j
      let k : Fin (g0 :: g1 :: gs).length := ⟨j.val+2,by simp⟩
      have he := hnormal k
      change gateShape ((g0 :: g1 :: gs).get k) (9+k.val) at he
      simpa [k,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he
