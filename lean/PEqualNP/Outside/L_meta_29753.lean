import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29753

open PEqualNP.CircuitLowerBounds

/-! Circuit surgery from our proofs of L-lib-825 and L-lib-824 (copied). -/

def Legal (n : ℕ) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))

noncomputable def paid (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

noncomputable def cost (C : Circuit) : ℕ := C.gates.countP paid

def gA (C : Circuit) (j : ℕ) : Gate := PEqualNP.MetaComplexity.NestedCover.gateAt C j

theorem gA_def (C : Circuit) (j : ℕ) : gA C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl

def stp (e : Gate → (ℕ → Bool) → Bool) (w : List Bool) (g : Gate) : List Bool :=
  w ++ [e g (fun i => w.getD i false)]

theorem gd_app_left (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_app_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD]; simp

theorem gd_out (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem fold_spec (e : Gate → (ℕ → Bool) → Bool)
    (he : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → e g V = e g V') :
    ∀ (l : List Gate) (x : List Bool),
      (l.foldl (stp e) x).length = x.length + l.length ∧
      (∀ i < x.length, (l.foldl (stp e) x).getD i false = x.getD i false) ∧
      ∀ j (hj : j < l.length), (∀ i ∈ (l[j]).inputs, i < x.length + j) →
        (l.foldl (stp e) x).getD (x.length + j) false =
          e l[j] (fun i => (l.foldl (stp e) x).getD i false) := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons g l ih =>
    intro x
    simp only [List.foldl_cons]
    have hx : (stp e x g).length = x.length + 1 := by simp [stp]
    obtain ⟨A, B, Cc⟩ := ih (stp e x g)
    refine ⟨by rw [A, hx]; simp; omega, ?_, ?_⟩
    · intro i hi
      rw [B i (by omega)]
      exact gd_app_left _ _ _ hi
    · intro j hj hin
      rcases j with _ | j
      · simp only [List.getElem_cons_zero, Nat.add_zero] at hin ⊢
        have h0 : (stp e x g).getD x.length false = e g (fun i => x.getD i false) :=
          gd_app_len _ _
        rw [B x.length (by omega), h0]
        apply he
        intro i hi
        have := hin i hi
        rw [B i (by omega)]
        exact (gd_app_left _ _ _ (hin i hi)).symm
      · simp only [List.getElem_cons_succ] at hin ⊢
        have := Cc j (by simp at hj; omega) (by intro i hi; have := hin i hi; omega)
        rw [hx] at this
        rw [show x.length + (j+1) = x.length + 1 + j by omega]
        exact this

theorem fold_get (e : Gate → (ℕ → Bool) → Bool)
    (he : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → e g V = e g V')
    (C : Circuit) (x : List Bool)
    (hrb : ∀ j < C.gates.length, ∀ i ∈ (gA C j).inputs, i < x.length + j) :
    (∀ i < x.length, (C.gates.foldl (stp e) x).getD i false = x.getD i false) ∧
    (∀ j < C.gates.length, (C.gates.foldl (stp e) x).getD (x.length + j) false =
        e (gA C j) (fun i => (C.gates.foldl (stp e) x).getD i false)) ∧
    (∀ i, x.length + C.gates.length ≤ i → (C.gates.foldl (stp e) x).getD i false = false) := by
  obtain ⟨A, B, Cc⟩ := fold_spec e he C.gates x
  have hg : ∀ j (hj : j < C.gates.length), gA C j = C.gates[j] := by
    intro j hj
    rw [gA_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  refine ⟨B, ?_, ?_⟩
  · intro j hj
    rw [hg j hj]
    exact Cc j hj (by rw [← hg j hj]; exact hrb j hj)
  · intro i hi
    exact gd_out _ _ (by omega)

def ev (g : Gate) (V : ℕ → Bool) : Bool := g.op.eval (g.inputs.map V)

theorem ev_loc : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → ev g V = ev g V' := by
  intro g V V' h
  simp only [ev]
  rw [List.map_congr_left h]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl (stp ev) x := rfl

noncomputable def gc (g : Gate) (V : ℕ → Bool) : Bool :=
  match g.inputs with
  | [a] => V a
  | [a, b] => @ite _ (g.op = .mod 2) (Classical.propDecidable _) (Bool.xor (V a) (V b)) false
  | _ => false

theorem gc_loc : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → gc g V = gc g V' := by
  intro g V V' h
  unfold gc
  split
  · rename_i a ha
    rw [ha] at h; simp at h; rw [h]
  · rename_i a b ha
    rw [ha] at h; simp at h; rw [h.1, h.2]
  · rfl


theorem facts (e : Gate → (ℕ → Bool) → Bool)
    (he : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → e g V = e g V')
    (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : List Bool) (hx : x.length = n) :
    (∀ i < n, (C.gates.foldl (stp e) x).getD i false = x.getD i false) ∧
    (∀ j < C.gates.length, (C.gates.foldl (stp e) x).getD (n + j) false =
        e (gA C j) (fun i => (C.gates.foldl (stp e) x).getD i false)) ∧
    (∀ i, n + C.gates.length ≤ i → (C.gates.foldl (stp e) x).getD i false = false) := by
  subst hx
  exact fold_get e he C x (fun j hj i hi => hrb j hj i hi)

theorem gA_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gA C j ∈ C.gates := by
  rw [gA_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

def WC (C : Circuit) (x : List Bool) (i : ℕ) : Bool := (C.wires x).getD i false

noncomputable def cl (C : Circuit) (t : ℕ) : List Bool := C.gates.foldl (stp gc) (true :: List.replicate t false)

noncomputable def cf (C : Circuit) (t : ℕ) (i : ℕ) : Bool := (cl C t).getD i false

def hit (C : Circuit) (t : ℕ) (j : ℕ) : Prop :=
  paid (gA C j) = true ∧ ∃ a ∈ (gA C j).inputs, cf C t a = true

theorem step_inv (g : Gate)
    (hl : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (Vu V0 c : ℕ → Bool) (u : Bool) (hin : ∀ i ∈ g.inputs, Vu i = Bool.xor (c i && u) (V0 i))
    (hno : ¬ (paid g = true ∧ ∃ a ∈ g.inputs, c a = true)) :
    ev g Vu = Bool.xor (gc g c && u) (ev g V0) := by
  obtain ⟨op, ins⟩ := g
  simp only at hl hin hno
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c', l⟩⟩⟩
  · simp [ev, gc]
  · have ha := hin a (by simp)
    simp only [ev, gc, List.map_cons, List.map_nil, ha]
    rcases hl.2 with h | h | h | ⟨h, _⟩ <;> subst h <;>
      cases c a <;> cases u <;> cases V0 a <;> decide
  · have ha := hin a (by simp)
    have hb := hin b (by simp)
    simp only [ev, gc, List.map_cons, List.map_nil, ha, hb]
    rcases hl.2 with h | h | h | ⟨h, h'⟩
    · subst h
      have hp : paid ⟨GateOp.and, [a, b]⟩ = true := by simp [paid]
      have hca : c a = false := by
        by_contra hc; exact hno ⟨hp, a, by simp, by simpa using hc⟩
      have hcb : c b = false := by
        by_contra hc; exact hno ⟨hp, b, by simp, by simpa using hc⟩
      simp [hca, hcb]
    · subst h
      have hp : paid ⟨GateOp.or, [a, b]⟩ = true := by simp [paid]
      have hca : c a = false := by
        by_contra hc; exact hno ⟨hp, a, by simp, by simpa using hc⟩
      have hcb : c b = false := by
        by_contra hc; exact hno ⟨hp, b, by simp, by simpa using hc⟩
      simp [hca, hcb]
    · subst h
      simp only [ite_true]
      cases c a <;> cases c b <;> cases u <;> cases V0 a <;> cases V0 b <;> decide
    · simp at h'
  · simp at hl

theorem inv (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) (u : Bool) (zl : List Bool)
    (hz : zl.length = t) (h : ℕ) (hh : h ≤ C.gates.length) (hno : ∀ j < h, ¬ hit C t j) :
    ∀ w < 1+t+h, WC C (u::zl) w = Bool.xor (cf C t w && u) (WC C (false::zl) w) := by
  have Fu := facts ev ev_loc (1+t) C hC.1 (u::zl) (by simp; omega)
  have F0 := facts ev ev_loc (1+t) C hC.1 (false::zl) (by simp; omega)
  have Fc := facts gc gc_loc (1+t) C hC.1 (true :: List.replicate t false) (by simp; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  simp only [WC, cf, cl, wires_eq] at ih ⊢
  by_cases hw1 : w < 1 + t
  · rw [Fu.1 w hw1, F0.1 w hw1, Fc.1 w hw1]
    rcases w with _ | i
    · simp
    · simp only [List.getD_cons_succ]
      have : (List.replicate t false).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      rw [this]; simp
  · obtain ⟨j, rfl⟩ : ∃ j, w = 1 + t + j := ⟨w - (1+t), by omega⟩
    have hj : j < C.gates.length := by omega
    rw [Fu.2.1 j hj, F0.2.1 j hj, Fc.2.1 j hj]
    apply step_inv (gA C j) (hC.2 _ (gA_mem C j hj))
    · intro i hi
      have hib := hC.1 j hj i hi
      exact ih i (by omega) (by omega)
    · exact hno j (by omega)


abbrev mk (F : ℕ → Gate) (M o : ℕ) : Circuit := ⟨(List.range M).map F, o⟩

theorem gA_mk (F : ℕ → Gate) (M o k : ℕ) (hk : k < M) : gA (mk F M o) k = F k := by
  rw [gA_def, List.getD_eq_getElem?_getD]; simp [hk]

theorem len_mk (F : ℕ → Gate) (M o : ℕ) : (mk F M o).gates.length = M := by simp

theorem legal_mk (t : ℕ) (F : ℕ → Gate) (M o : ℕ)
    (h1 : ∀ k < M, ∀ i ∈ (F k).inputs, i < t + k)
    (h2 : ∀ k < M, (F k).inputs.length ≤ 2 ∧
      ((F k).op = .and ∨ (F k).op = .or ∨ (F k).op = .mod 2 ∨
        ((F k).op = .not ∧ (F k).inputs.length = 1))) :
    Legal t (mk F M o) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    have hj' : j < M := by simpa using hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt (mk F M o) j = F j := gA_mk F M o j hj'
    rw [e] at hi
    exact h1 j hj' i hi
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    exact h2 k hk

theorem cost_mk (F : ℕ → Gate) (M o : ℕ) :
    cost (mk F M o) = ∑ k ∈ Finset.range M, if paid (F k) = true then 1 else 0 := by
  induction M with
  | zero => simp [cost]
  | succ M ih =>
    simp only [cost] at ih ⊢
    rw [List.range_succ, List.map_append, List.countP_append, ih, Finset.sum_range_succ]
    simp

theorem gates_eq (C : Circuit) : C.gates = (List.range C.gates.length).map (gA C) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [gA_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl

theorem cost_eq (C : Circuit) :
    cost C = ∑ k ∈ Finset.range C.gates.length, if paid (gA C k) = true then 1 else 0 := by
  have := cost_mk (gA C) C.gates.length C.output
  rw [← this]
  simp only [cost]
  rw [← gates_eq]

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem ev_ren (f : ℕ → ℕ) (g : Gate) (V : ℕ → Bool) : ev (ren f g) V = ev g (fun i => V (f i)) := by
  simp [ev, ren, List.map_map, Function.comp_def]

theorem paid_ren (f : ℕ → ℕ) (g : Gate) : paid (ren f g) = paid g := by
  unfold paid
  rw [decide_eq_decide]
  simp [ren]

def m1 (t w : ℕ) : ℕ := if w = 0 then t else if w ≤ t then w - 1 else w

theorem m1_zero (t : ℕ) : m1 t 0 = t := by simp [m1]

theorem m1_succ (t i : ℕ) (h : i < t) : m1 t (i+1) = i := by
  unfold m1; rw [if_neg (by omega), if_pos (by omega)]; omega

theorem m1_big (t w : ℕ) (h : t < w) : m1 t w = w := by
  unfold m1; rw [if_neg (by omega), if_neg (by omega)]

theorem m1_lt (t w j : ℕ) (h : w < 1 + t + j) : m1 t w < t + 1 + j := by
  unfold m1; split_ifs <;> omega

def Kg : Gate := ⟨.or, []⟩

def FE (C : Circuit) (t k : ℕ) : Gate := if k = 0 then Kg else ren (m1 t) (gA C (k-1))

theorem legal_ren (n : ℕ) (C : Circuit) (hC : Legal n C) (f : ℕ → ℕ) (j : ℕ)
    (hj : j < C.gates.length) :
    (ren f (gA C j)).inputs.length ≤ 2 ∧
      ((ren f (gA C j)).op = .and ∨ (ren f (gA C j)).op = .or ∨ (ren f (gA C j)).op = .mod 2 ∨
        ((ren f (gA C j)).op = .not ∧ (ren f (gA C j)).inputs.length = 1)) := by
  have := hC.2 _ (gA_mem C j hj)
  simpa [ren] using this

theorem rb_mk (t : ℕ) (F : ℕ → Gate) (M o : ℕ)
    (h1 : ∀ k < M, ∀ i ∈ (F k).inputs, i < t + k) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack t (mk F M o) := by
  intro j hj i hi
  have hj' : j < M := by simpa using hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt (mk F M o) j = F j := gA_mk F M o j hj'
  rw [e] at hi
  exact h1 j hj' i hi

theorem copy0 (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) (F : ℕ → Gate) (M o : ℕ) (h : ℕ)
    (hh : h ≤ C.gates.length) (hM : h + 1 ≤ M)
    (hF0 : F 0 = Kg) (hF : ∀ j < h, F (1 + j) = ren (m1 t) (gA C j))
    (hrb : ∀ k < M, ∀ i ∈ (F k).inputs, i < t + k)
    (zl : List Bool) (hz : zl.length = t) :
    ∀ w < 1 + t + h, WC (mk F M o) zl (m1 t w) = WC C (false :: zl) w := by
  have FD := facts ev ev_loc t (mk F M o) (rb_mk t F M o hrb) zl hz
  have F0 := facts ev ev_loc (1+t) C hC.1 (false::zl) (by simp; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  simp only [WC, wires_eq] at ih ⊢
  by_cases hw0 : w = 0
  · subst hw0
    have e := FD.2.1 0 (by simp; omega)
    rw [gA_mk F M o 0 (by omega), hF0, Nat.add_zero] at e
    rw [m1_zero, e, F0.1 0 (by omega)]
    rfl
  · by_cases hw1 : w ≤ t
    · obtain ⟨i, rfl⟩ : ∃ i, w = i + 1 := ⟨w - 1, by omega⟩
      rw [m1_succ t i (by omega), FD.1 i (by omega), F0.1 (i+1) (by omega)]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, w = 1 + t + j := ⟨w - (1+t), by omega⟩
      have hj : j < h := by omega
      have e := FD.2.1 (1 + j) (by simp; omega)
      rw [gA_mk F M o _ (by omega), hF j hj, ev_ren, show t + (1 + j) = 1 + t + j by omega] at e
      rw [m1_big t _ (by omega), e,
        F0.2.1 j (by omega)]
      apply ev_loc
      intro i hi
      have := hC.1 j (by omega) i hi
      exact ih i (by omega) (by omega)


theorem paid_Kg : paid Kg = false := by simp [paid, Kg]

theorem rb_FE (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) :
    ∀ k < C.gates.length + 1, ∀ i ∈ (FE C t k).inputs, i < t + k := by
  intro k hk i hi
  rcases k with _ | j
  · simp [FE, Kg] at hi
  · simp only [FE, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, ren, List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have := hC.1 j (by omega) a ha
    have := m1_lt t a j this
    omega

theorem caseA (t : ℕ) (C : Circuit) (hC : Legal (1+t) C)
    (hno : ∀ j < C.gates.length, ¬ hit C t j) :
    ∃ (a : Bool) (E : Circuit), Legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Fin t → Bool), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z)) := by
  let n := C.gates.length
  let E := mk (FE C t) (n+1) (m1 t C.output)
  refine ⟨cf C t C.output, E, ?_, ?_, ?_⟩
  · apply legal_mk t _ _ _ (rb_FE t C hC)
    intro k hk
    rcases k with _ | j
    · simp [FE, Kg]
    · simp only [FE, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact legal_ren (1+t) C hC _ j (by omega)
  · apply le_of_eq
    rw [cost_mk, cost_eq, Finset.sum_range_succ']
    simp only [FE, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, paid_ren, if_true,
      paid_Kg]
    simp [n]
  · intro u z
    have hz : (List.ofFn z).length = t := by simp
    have Fu := facts ev ev_loc (1+t) C hC.1 (u::List.ofFn z) (by simp; omega)
    have F0 := facts ev ev_loc (1+t) C hC.1 (false::List.ofFn z) (by simp; omega)
    have Fc := facts gc gc_loc (1+t) C hC.1 (true :: List.replicate t false) (by simp; omega)
    have FE' := facts ev ev_loc t E (rb_mk t _ _ _ (rb_FE t C hC)) (List.ofFn z) hz
    have hcp := copy0 t C hC (FE C t) (n+1) (m1 t C.output) n le_rfl le_rfl (by simp [FE])
      (by intro j _; simp [FE]) (rb_FE t C hC) (List.ofFn z) hz
    have hiv := inv t C hC u (List.ofFn z) hz n le_rfl hno
    show WC C _ C.output = Bool.xor _ (WC E _ (m1 t C.output))
    by_cases ho : C.output < 1 + t + n
    · rw [hiv _ ho, hcp _ ho]
    · simp only [WC, wires_eq, cf, cl]
      rw [Fu.2.2 _ (by omega), Fc.2.2 _ (by omega), m1_big t _ (by omega),
        FE'.2.2 _ (by simp [E]; omega)]
      simp


def m2 (t n h w : ℕ) : ℕ :=
  if w = 0 then t + 1 + h else if w ≤ t then w - 1 else if w < 1 + t + n then w + 1 + h else t

theorem m2_zero (t n h : ℕ) : m2 t n h 0 = t + 1 + h := by simp [m2]

theorem m2_succ (t n h i : ℕ) (hi : i < t) : m2 t n h (i+1) = i := by
  unfold m2; rw [if_neg (by omega), if_pos (by omega)]; omega

theorem m2_mid (t n h w : ℕ) (h1 : t < w) (h2 : w < 1 + t + n) : m2 t n h w = w + 1 + h := by
  unfold m2; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem m2_big (t n h w : ℕ) (h1 : 1 + t + n ≤ w) : m2 t n h w = t := by
  unfold m2; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem m2_lt (t n h w j : ℕ) (hw : w < 1 + t + j) (hj : j ≤ n) : m2 t n h w < t + (h + 2 + j) := by
  unfold m2; split_ifs <;> omega

theorem m2_le (t n h w : ℕ) : m2 t n h w ≤ t + 1 + h + n := by
  unfold m2; split_ifs <;> omega

def Ug (t x : ℕ) (b : Bool) : Gate := if b then ⟨.not, [m1 t x]⟩ else ⟨.and, [m1 t x]⟩

def Rg (t n h y : ℕ) (isAnd b : Bool) : Gate :=
  if isAnd then (if b then ⟨.and, [m2 t n h y]⟩ else ⟨.or, []⟩)
  else (if b then ⟨.and, []⟩ else ⟨.and, [m2 t n h y]⟩)

noncomputable def Sg (C : Circuit) (t h : ℕ) (R : Gate) (j : ℕ) : Gate :=
  if j < h ∧ paid (gA C j) = true then ⟨.and, [t+1+j]⟩
  else if j = h then R else ren (m2 t C.gates.length h) (gA C j)

noncomputable def FD (C : Circuit) (t h : ℕ) (U R : Gate) (d : Bool) (k : ℕ) : Gate :=
  if k = 0 then Kg
  else if k ≤ h then ren (m1 t) (gA C (k-1))
  else if k = h + 1 then U
  else if k < h + 2 + C.gates.length then Sg C t h R (k-h-2)
  else if k = h + 2 + C.gates.length then
    ⟨.mod 2, [m2 t C.gates.length h C.output, t+1+h]⟩
  else if d then ⟨.not, [t+2+h+C.gates.length]⟩ else ⟨.and, [m2 t C.gates.length h C.output]⟩

section
variable (C : Circuit) (t h : ℕ) (U R : Gate) (d : Bool)

theorem FD_0 : FD C t h U R d 0 = Kg := by simp [FD]

theorem FD_1 (j : ℕ) (hj : j < h) : FD C t h U R d (1 + j) = ren (m1 t) (gA C j) := by
  unfold FD; rw [if_neg (by omega), if_pos (by omega)]; simp

theorem FD_U : FD C t h U R d (h + 1) = U := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem FD_S (j : ℕ) (hj : j < C.gates.length) : FD C t h U R d (h + 2 + j) = Sg C t h R j := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem FD_g1 : FD C t h U R d (h + 2 + C.gates.length) =
    ⟨.mod 2, [m2 t C.gates.length h C.output, t+1+h]⟩ := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem FD_g2 : FD C t h U R d (h + 3 + C.gates.length) =
    if d then ⟨.not, [t+2+h+C.gates.length]⟩ else ⟨.and, [m2 t C.gates.length h C.output]⟩ := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end

theorem regions (h n k : ℕ) (hk : k < h + n + 4) :
    k = 0 ∨ (∃ j < h, k = 1 + j) ∨ k = h + 1 ∨ (∃ j < n, k = h + 2 + j) ∨
      k = h + 2 + n ∨ k = h + 3 + n := by
  by_cases h0 : k = 0
  · exact Or.inl h0
  by_cases h1 : k ≤ h
  · exact Or.inr (Or.inl ⟨k - 1, by omega, by omega⟩)
  by_cases h2 : k = h + 1
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : k < h + 2 + n
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k - h - 2, by omega, by omega⟩)))
  by_cases h4 : k = h + 2 + n
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

theorem gc_paid (g : Gate) (hp : paid g = true) (V : ℕ → Bool) : gc g V = false := by
  simp only [paid, decide_eq_true_eq] at hp
  obtain ⟨hop, hlen⟩ := hp
  unfold gc
  split
  · rename_i a ha; rw [ha] at hlen; simp at hlen
  · rename_i a b ha
    rcases hop with hop | hop <;> rw [hop] <;> simp
  · rfl

theorem sum_split (f g : ℕ → ℕ) (h n : ℕ) (hhn : h < n) (h1 : ∀ k < h, f k = 0) (h2 : f h = 0)
    (h3 : g h = 1) (h4 : ∀ k, h < k → k < n → f k = g k) :
    ∑ k ∈ Finset.range h, g k + ∑ k ∈ Finset.range n, f k < ∑ k ∈ Finset.range n, g k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = h + (m + 1) := ⟨n - h - 1, by omega⟩
  rw [Finset.sum_range_add f h (m+1), Finset.sum_range_add g h (m+1)]
  simp only [Finset.sum_range_succ']
  have e1 : ∑ k ∈ Finset.range h, f k = 0 := Finset.sum_eq_zero (fun k hk => h1 k (by simpa using hk))
  have e2 : ∑ k ∈ Finset.range m, f (h + (k + 1)) = ∑ k ∈ Finset.range m, g (h + (k + 1)) :=
    Finset.sum_congr rfl (fun k hk => h4 _ (by omega) (by simp at hk; omega))
  rw [e1, e2, Nat.add_zero, h2, h3]
  omega


theorem factsW (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : List Bool) (hx : x.length = n) :
    (∀ i < n, WC C x i = x.getD i false) ∧
    (∀ j < C.gates.length, WC C x (n + j) = ev (gA C j) (WC C x)) ∧
    (∀ i, n + C.gates.length ≤ i → WC C x i = false) :=
  facts ev ev_loc n C hrb x hx

theorem Ug_in (t x : ℕ) (b : Bool) : ∀ i ∈ (Ug t x b).inputs, i = m1 t x := by
  cases b <;> simp [Ug]

theorem Ug_ops (t x : ℕ) (b : Bool) : (Ug t x b).inputs.length ≤ 2 ∧
    ((Ug t x b).op = .and ∨ (Ug t x b).op = .or ∨ (Ug t x b).op = .mod 2 ∨
      ((Ug t x b).op = .not ∧ (Ug t x b).inputs.length = 1)) := by
  cases b <;> simp [Ug]

theorem paid_Ug (t x : ℕ) (b : Bool) : paid (Ug t x b) = false := by
  cases b <;> simp [Ug, paid]

theorem ev_Ug (t x : ℕ) (b : Bool) (V : ℕ → Bool) :
    ev (Ug t x b) V = Bool.xor (V (m1 t x)) b := by
  cases b <;> simp [Ug, ev, GateOp.eval]

theorem Rg_in (t n h y : ℕ) (ia b : Bool) : ∀ i ∈ (Rg t n h y ia b).inputs, i = m2 t n h y := by
  cases ia <;> cases b <;> simp [Rg]

theorem Rg_ops (t n h y : ℕ) (ia b : Bool) : (Rg t n h y ia b).inputs.length ≤ 2 ∧
    ((Rg t n h y ia b).op = .and ∨ (Rg t n h y ia b).op = .or ∨ (Rg t n h y ia b).op = .mod 2 ∨
      ((Rg t n h y ia b).op = .not ∧ (Rg t n h y ia b).inputs.length = 1)) := by
  cases ia <;> cases b <;> simp [Rg]

theorem paid_Rg (t n h y : ℕ) (ia b : Bool) : paid (Rg t n h y ia b) = false := by
  cases ia <;> cases b <;> simp [Rg, paid]

theorem ev_Rg (t n h y : ℕ) (ia b : Bool) (V : ℕ → Bool) :
    ev (Rg t n h y ia b) V = if ia then (b && V (m2 t n h y)) else (b || V (m2 t n h y)) := by
  cases ia <;> cases b <;> simp [Rg, ev, GateOp.eval]

theorem caseB (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) (h : ℕ) (hhn : h < C.gates.length)
    (hhit : hit C t h) (hmin : ∀ j < h, ¬ hit C t j) :
    0 < cost C ∧ ∃ p : (Fin t → Bool) → Bool, ∀ (b d : Bool), ∃ D : Circuit, Legal t D ∧
      cost D < cost C ∧ ∀ z : Fin t → Bool,
        D.eval (List.ofFn z) =
          Bool.xor (C.eval ((Bool.xor (p z) b) :: List.ofFn z)) (d && Bool.xor (p z) b) := by
  obtain ⟨hpaid, hsee⟩ := hhit
  have hp' := hpaid
  simp only [paid, decide_eq_true_eq] at hp'
  obtain ⟨hop, hlen⟩ := hp'
  obtain ⟨a1, a2, hins⟩ : ∃ a1 a2, (gA C h).inputs = [a1, a2] := by
    rcases hI : (gA C h).inputs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩
    · rw [hI] at hlen; simp at hlen
    · rw [hI] at hlen; simp at hlen
    · exact ⟨a1, a2, rfl⟩
    · rw [hI] at hlen; simp at hlen
  have ha1 : a1 < 1 + t + h := hC.1 h hhn a1 (by show a1 ∈ (gA C h).inputs; rw [hins]; simp)
  have ha2 : a2 < 1 + t + h := hC.1 h hhn a2 (by show a2 ∈ (gA C h).inputs; rw [hins]; simp)
  let x := if cf C t a1 = true then a1 else a2
  let y := if cf C t a1 = true then a2 else a1
  have hx : cf C t x = true := by
    obtain ⟨a, ha, hca⟩ := hsee
    rw [hins] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    by_cases h1 : cf C t a1 = true
    · simp [x, h1]
    · rcases ha with rfl | rfl
      · exact absurd hca h1
      · simp [x, h1, hca]
  have hxl : x < 1 + t + h := by simp only [x]; split_ifs <;> omega
  have hyl : y < 1 + t + h := by simp only [y]; split_ifs <;> omega
  let isAnd : Bool := @decide ((gA C h).op = .and) (Classical.propDecidable _)
  have hev : ∀ V : ℕ → Bool, ev (gA C h) V = if isAnd then (V x && V y) else (V x || V y) := by
    intro V
    simp only [ev, hins, List.map_cons, List.map_nil]
    rcases hop with hop | hop
    · have hA : isAnd = true := by simp only [isAnd, decide_eq_true_eq]; exact hop
      rw [hA, hop]
      by_cases h1 : cf C t a1 = true <;> simp [x, y, h1, GateOp.eval, Bool.and_comm]
    · have hA : isAnd = false := by
        simp only [isAnd, decide_eq_false_iff_not]; rw [hop]; simp
      rw [hA, hop]
      by_cases h1 : cf C t a1 = true <;> simp [x, y, h1, GateOp.eval, Bool.or_comm]
  refine ⟨?_, fun z => WC C (false :: List.ofFn z) x, ?_⟩
  · rw [cost_eq]
    have := Finset.single_le_sum (f := fun k => if paid (gA C k) = true then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hhn)
    simp only [hpaid, if_true] at this
    omega
  intro b d
  let U := Ug t x b
  let R := Rg t C.gates.length h y isAnd b
  let D := mk (FD C t h U R d) (h + C.gates.length + 4) (t + 3 + h + C.gates.length)
  have hrb : ∀ k < h + C.gates.length + 4, ∀ i ∈ (FD C t h U R d k).inputs, i < t + k := by
    intro k hk i hi
    rcases regions h C.gates.length k hk with rfl | ⟨j, hj, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    · rw [FD_0] at hi; simp [Kg] at hi
    · rw [FD_1 C t h U R d j hj] at hi
      simp only [ren, List.mem_map] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      have := m1_lt t a j (hC.1 j (by omega) a ha)
      omega
    · rw [FD_U] at hi
      have := m1_lt t x h hxl
      rw [Ug_in t x b i hi]
      omega
    · rw [FD_S C t h U R d j hj] at hi
      unfold Sg at hi
      split_ifs at hi with h1 h2
      · simp at hi; omega
      · rw [Rg_in _ _ _ _ _ _ i hi]
        have := m2_lt t C.gates.length h y h hyl (by omega)
        omega
      · simp only [ren, List.mem_map] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        exact m2_lt _ _ _ _ _ (hC.1 j hj a ha) (le_of_lt hj)
    · rw [FD_g1] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have := m2_le t C.gates.length h C.output
      rcases hi with rfl | rfl <;> omega
    · rw [FD_g2] at hi
      have := m2_le t C.gates.length h C.output
      cases d <;> simp at hi <;> omega
  have hops : ∀ k < h + C.gates.length + 4, (FD C t h U R d k).inputs.length ≤ 2 ∧
      ((FD C t h U R d k).op = .and ∨ (FD C t h U R d k).op = .or ∨
        (FD C t h U R d k).op = .mod 2 ∨
        ((FD C t h U R d k).op = .not ∧ (FD C t h U R d k).inputs.length = 1)) := by
    intro k hk
    rcases regions h C.gates.length k hk with rfl | ⟨j, hj, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    · rw [FD_0]; simp [Kg]
    · rw [FD_1 C t h U R d j hj]; exact legal_ren (1+t) C hC _ j (by omega)
    · rw [FD_U]; exact Ug_ops t x b
    · rw [FD_S C t h U R d j hj]
      unfold Sg
      split_ifs
      · simp
      · exact Rg_ops _ _ _ _ _ _
      · exact legal_ren (1+t) C hC _ j hj
    · rw [FD_g1]; simp
    · rw [FD_g2]; cases d <;> simp
  refine ⟨D, legal_mk t _ _ _ hrb hops, ?_, ?_⟩
  · rw [cost_mk, cost_eq]
    rw [show h + C.gates.length + 4 = (1 + h) + (1 + (C.gates.length + 2)) by omega,
      Finset.sum_range_add _ (1 + h), Finset.sum_range_add _ 1 h,
      Finset.sum_range_add _ 1 (C.gates.length + 2), Finset.sum_range_add _ C.gates.length 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero]
    have e1 : ∑ k ∈ Finset.range h, (if paid (FD C t h U R d (1 + k)) = true then 1 else 0) =
        ∑ k ∈ Finset.range h, (if paid (gA C k) = true then 1 else 0) :=
      Finset.sum_congr rfl (fun k hk => by
        rw [FD_1 C t h U R d k (by simpa using hk), paid_ren])
    have e2 : ∑ k ∈ Finset.range C.gates.length,
        (if paid (FD C t h U R d (1 + h + (1 + k))) = true then 1 else 0) =
        ∑ k ∈ Finset.range C.gates.length, (if paid (Sg C t h R k) = true then 1 else 0) :=
      Finset.sum_congr rfl (fun k hk => by
        rw [show 1 + h + (1 + k) = h + 2 + k by omega, FD_S C t h U R d k (by simpa using hk)])
    have e3 : paid (FD C t h U R d (1 + h)) = false := by
      rw [show 1 + h = h + 1 by omega, FD_U]; exact paid_Ug t x b
    have e4 : paid (FD C t h U R d (1 + h + (1 + C.gates.length))) = false := by
      rw [show 1 + h + (1 + C.gates.length) = h + 2 + C.gates.length by omega, FD_g1]
      simp [paid]
    have e5 : paid (FD C t h U R d (1 + h + (1 + (C.gates.length + 1)))) = false := by
      rw [show 1 + h + (1 + (C.gates.length + 1)) = h + 3 + C.gates.length by omega, FD_g2]
      cases d <;> simp [paid]
    simp only [e1, e2, e3, e4, e5, FD_0, paid_Kg]
    have key := sum_split (fun k => if paid (Sg C t h R k) = true then 1 else 0)
      (fun k => if paid (gA C k) = true then 1 else 0) h C.gates.length hhn
      (by
        intro k hk
        have e : paid (Sg C t h R k) = false := by
          unfold Sg
          by_cases hp : paid (gA C k) = true
          · rw [if_pos ⟨hk, hp⟩]; simp [paid]
          · rw [if_neg (by tauto), if_neg (by omega), paid_ren]; simpa using hp
        simp [e])
      (by
        have e : paid (Sg C t h R h) = false := by
          unfold Sg; rw [if_neg (by omega), if_pos rfl]; exact paid_Rg _ _ _ _ _ _
        simp [e])
      (by simp [hpaid])
      (by
        intro k hk1 hk2
        have e : paid (Sg C t h R k) = paid (gA C k) := by
          unfold Sg; rw [if_neg (by omega), if_neg (by omega), paid_ren]
        simp [e])
    simp only [Bool.false_eq_true, if_false]
    omega
  · intro z
    have hz : (List.ofFn z).length = t := by simp
    obtain ⟨uu, huu⟩ : ∃ uu, uu = Bool.xor (WC C (false :: List.ofFn z) x) b := ⟨_, rfl⟩
    show WC D (List.ofFn z) (t + 3 + h + C.gates.length) =
      Bool.xor (WC C (Bool.xor (WC C (false :: List.ofFn z) x) b :: List.ofFn z) C.output)
        (d && Bool.xor (WC C (false :: List.ofFn z) x) b)
    rw [← huu]
    have Fu := factsW (1+t) C hC.1 (uu :: List.ofFn z) (by simp; omega)
    have Fc := facts gc gc_loc (1+t) C hC.1 (true :: List.replicate t false) (by simp; omega)
    have FW := factsW t D (rb_mk t _ _ _ hrb) (List.ofFn z) hz
    have hcp := copy0 t C hC (FD C t h U R d) (h + C.gates.length + 4)
      (t + 3 + h + C.gates.length) h (le_of_lt hhn) (by omega) (FD_0 C t h U R d)
      (fun j hj => FD_1 C t h U R d j hj) hrb (List.ofFn z) hz
    have hiv := inv t C hC uu (List.ofFn z) hz h (le_of_lt hhn) hmin
    have gD : ∀ k < h + C.gates.length + 4, gA D k = FD C t h U R d k :=
      fun k hk => gA_mk _ _ _ k hk
    have hU : WC D (List.ofFn z) (t + 1 + h) = uu := by
      have e := FW.2.1 (h + 1) (by simp [D]; omega)
      rw [gD _ (by omega), FD_U, ev_Ug, hcp x hxl] at e
      rw [show t + 1 + h = t + (h + 1) by omega, e, huu]
    have hWx : WC C (uu :: List.ofFn z) x = b := by
      rw [hiv x hxl, hx, huu]
      cases b <;> simp
    have hV0 : WC D (List.ofFn z) t = false := by
      have e := FW.2.1 0 (by simp [D])
      rw [gD _ (by omega), FD_0, Nat.add_zero] at e
      rw [e]; simp [ev, Kg, GateOp.eval]
    have claim : ∀ w, WC D (List.ofFn z) (m2 t C.gates.length h w) = WC C (uu :: List.ofFn z) w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      by_cases w0 : w = 0
      · subst w0
        rw [m2_zero, hU, Fu.1 0 (by omega)]; simp
      by_cases w1 : w ≤ t
      · obtain ⟨i, rfl⟩ : ∃ i, w = i + 1 := ⟨w - 1, by omega⟩
        rw [m2_succ _ _ _ i (by omega), FW.1 i (by omega), Fu.1 (i+1) (by omega)]
        simp
      by_cases w2 : w < 1 + t + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = 1 + t + j := ⟨w - (1 + t), by omega⟩
        have hj : j < C.gates.length := by omega
        rw [m2_mid _ _ _ _ (by omega) w2, show 1 + t + j + 1 + h = t + (h + 2 + j) by omega,
          FW.2.1 (h + 2 + j) (by simp [D]; omega), gD _ (by omega),
          FD_S C t h U R d j hj]
        unfold Sg
        split_ifs with hA hB
        · have e := hcp (1 + t + j) (by omega)
          rw [m1_big t _ (by omega)] at e
          have hc : cf C t (1 + t + j) = false := by
            have := Fc.2.1 j hj
            rw [gc_paid _ hA.2] at this
            exact this
          rw [hiv (1 + t + j) (by omega), hc, ← e, show 1 + t + j = t + 1 + j by omega]
          simp [ev, GateOp.eval]
          rfl
        · rw [Fu.2.1 j hj, hB, hev, ev_Rg, hWx, ih y (by omega)]
        · rw [Fu.2.1 j hj, ev_ren]
          apply ev_loc
          intro i hi
          exact ih i (by have := hC.1 j hj i hi; omega)
      · rw [m2_big _ _ _ _ (by omega), Fu.2.2 w (by omega), hV0]
    have e1 := FW.2.1 (h + 3 + C.gates.length) (by simp [D]; omega)
    rw [gD _ (by omega), FD_g2] at e1
    have e2 := FW.2.1 (h + 2 + C.gates.length) (by simp [D]; omega)
    rw [gD _ (by omega), FD_g1] at e2
    rw [show t + 3 + h + C.gates.length = t + (h + 3 + C.gates.length) by omega, e1]
    cases d
    · simp [ev, GateOp.eval, claim]
    · simp only [ev, GateOp.eval, List.map_cons, List.map_nil, if_true]
      rw [show t + 2 + h + C.gates.length = t + (h + 2 + C.gates.length) by omega, e2]
      simp only [ev, List.map_cons, List.map_nil, claim, hU]
      cases WC C (uu :: List.ofFn z) C.output <;> cases uu <;> decide


theorem main (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) :
    (∃ (a : Bool) (E : Circuit), Legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Fin t → Bool), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z))) ∨
    (0 < cost C ∧ ∃ p : (Fin t → Bool) → Bool, ∀ (b d : Bool), ∃ D : Circuit, Legal t D ∧
      cost D < cost C ∧ ∀ z : Fin t → Bool,
        D.eval (List.ofFn z) =
          Bool.xor (C.eval ((Bool.xor (p z) b) :: List.ofFn z)) (d && Bool.xor (p z) b)) := by
  classical
  by_cases hex : ∃ j, j < C.gates.length ∧ hit C t j
  · right
    have hs := Nat.find_spec hex
    exact caseB t C hC (Nat.find hex) hs.1 hs.2
      (fun j hj hh => Nat.find_min hex hj ⟨by omega, hh⟩)
  · left
    exact caseA t C hC (fun j hj hh => hex ⟨j, hj, hh⟩)


def wf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (C : Circuit) (p : ℕ) (x : List Bool) : List Bool := (C.gates.take p).foldl wf x

def F (C : Circuit) (p : ℕ) (x : List Bool) (b : Bool) : Bool :=
  ((C.gates.drop (p+1)).foldl wf (W C p x ++ [b])).getD C.output false

theorem set_eval (C : Circuit) (p : ℕ) (hp : p < C.gates.length) (g' : Gate) (x : List Bool) :
    (⟨C.gates.set p g', C.output⟩ : Circuit).eval x =
      F C p x (g'.op.eval (g'.inputs.map fun i => (W C p x).getD i false)) := by
  simp only [Circuit.eval, Circuit.wires]
  rw [List.set_eq_take_append_cons_drop, if_pos hp, List.foldl_append, List.foldl_cons]
  rfl

theorem decomp (l : List Gate) (p : ℕ) (hp : p < l.length) :
    l = l.take p ++ l[p] :: l.drop (p+1) := by
  conv_lhs => rw [← List.set_getElem_self hp]
  rw [List.set_eq_take_append_cons_drop, if_pos hp]

theorem set_cost (C : Circuit) (p : ℕ) (hp : p < C.gates.length) (g' : Gate)
    (h1 : paid C.gates[p] = true) (h2 : paid g' = false) :
    cost ⟨C.gates.set p g', C.output⟩ < cost C := by
  simp only [cost]
  rw [List.set_eq_take_append_cons_drop, if_pos hp]
  conv_rhs => rw [decomp C.gates p hp]
  rw [List.countP_append, List.countP_append, List.countP_cons, List.countP_cons, h1, h2]
  simp

theorem set_legal (n : ℕ) (C : Circuit) (hC : Legal n C) (p : ℕ) (hp : p < C.gates.length)
    (g' : Gate)
    (hop : g'.inputs.length ≤ 2 ∧
      (g'.op = .and ∨ g'.op = .or ∨ g'.op = .mod 2 ∨ (g'.op = .not ∧ g'.inputs.length = 1)))
    (hin : ∀ i ∈ g'.inputs, i ∈ (C.gates[p]).inputs) :
    Legal n ⟨C.gates.set p g', C.output⟩ := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_set] at hi
    by_cases hpj : p = j
    · subst hpj
      rw [if_pos rfl, if_pos hp] at hi
      have := hC.1 p hp i
      apply this
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hp]
      exact hin i (by simpa using hi)
    · rw [if_neg hpj] at hi
      exact hC.1 j hj' i (by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]
        exact hi)
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hC.2 g h
    · subst h; exact hop

def s (v : Bool) : ℤ := if v then -1 else 1

theorem ident_and (G : Bool → Bool) (A B : Bool) :
    2 * s (G (GateOp.and.eval [A, B])) = s (G (GateOp.or.eval [])) + s (G (GateOp.or.eval [A])) +
      s (G ((GateOp.mod 2).eval [A, B])) - s (G (GateOp.not.eval [B])) := by
  cases A <;> cases B <;> cases h0 : G false <;> cases h1 : G true <;>
    simp [GateOp.eval, s, h0, h1]

theorem ident_or (G : Bool → Bool) (A B : Bool) :
    2 * s (G (GateOp.or.eval [A, B])) = s (G (GateOp.or.eval [A])) + s (G (GateOp.or.eval [B])) +
      s (G (GateOp.and.eval [])) - s (G ((GateOp.mod 2).eval [A, B])) := by
  cases A <;> cases B <;> cases h0 : G false <;> cases h1 : G true <;>
    simp [GateOp.eval, s, h0, h1]

theorem core (n : ℕ) (C : Circuit) (hC : Legal n C) (hc : 0 < cost C) :
    ∃ D : Fin 4 → Circuit, (∀ i, Legal n (D i) ∧ cost (D i) < cost C) ∧
      ∀ x : Fin n → Bool,
        2 * s (C.eval (List.ofFn x)) = s ((D 0).eval (List.ofFn x)) + s ((D 1).eval (List.ofFn x)) +
          s ((D 2).eval (List.ofFn x)) - s ((D 3).eval (List.ofFn x)) := by
  obtain ⟨g, hg, hpd⟩ := List.countP_pos_iff.1 hc
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
  have hpd' := hpd
  simp only [paid, decide_eq_true_eq] at hpd'
  obtain ⟨hop, hlen⟩ := hpd'
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  have hCe : ∀ x, C.eval x = F C p x (C.gates[p].op.eval
      (C.gates[p].inputs.map fun i => (W C p x).getD i false)) := by
    intro x
    have := set_eval C p hp C.gates[p] x
    rw [List.set_getElem_self] at this
    exact this
  have mk : ∀ R : Fin 4 → Gate, (∀ i, paid (R i) = false ∧ (R i).inputs.length ≤ 2 ∧
      ((R i).op = .and ∨ (R i).op = .or ∨ (R i).op = .mod 2 ∨
        ((R i).op = .not ∧ (R i).inputs.length = 1)) ∧
      ∀ w ∈ (R i).inputs, w ∈ (C.gates[p]).inputs) →
      ∀ i, Legal n (⟨C.gates.set p (R i), C.output⟩ : Circuit) ∧
        cost (⟨C.gates.set p (R i), C.output⟩ : Circuit) < cost C := by
    intro R hR i
    obtain ⟨h1, h2, h3, h4⟩ := hR i
    exact ⟨set_legal n C hC p hp (R i) ⟨h2, h3⟩ h4, set_cost C p hp (R i) hpd h1⟩
  rcases hop with ho | ho
  · let R : Fin 4 → Gate := ![⟨.or, []⟩, ⟨.or, [a]⟩, ⟨.mod 2, [a, b]⟩, ⟨.not, [b]⟩]
    refine ⟨fun i => ⟨C.gates.set p (R i), C.output⟩, mk R ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [R, paid, hab]
    · intro x
      simp only []
      rw [set_eval C p hp, set_eval C p hp, set_eval C p hp, set_eval C p hp, hCe, ho, hab]
      exact ident_and (F C p (List.ofFn x)) _ _
  · let R : Fin 4 → Gate := ![⟨.or, [a]⟩, ⟨.or, [b]⟩, ⟨.and, []⟩, ⟨.mod 2, [a, b]⟩]
    refine ⟨fun i => ⟨C.gates.set p (R i), C.output⟩, mk R ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [R, paid, hab]
    · intro x
      simp only []
      rw [set_eval C p hp, set_eval C p hp, set_eval C p hp, set_eval C p hp, hCe, ho, hab]
      exact ident_or (F C p (List.ofFn x)) _ _


/-! ## Signed sums over the inner-product pairs -/

def sig (v : Bool) : ℤ := if v then -1 else 1

def bits {k : ℕ} (u : Fin k → ZMod 2) : List Bool := List.ofFn (fun i : Fin k => decide (u i = 1))

theorem bits_len {k : ℕ} (u : Fin k → ZMod 2) : (bits u).length = k := by simp [bits]

theorem bits_cons {k : ℕ} (a : ZMod 2) (u : Fin k → ZMod 2) :
    bits (Fin.cons a u : Fin (k+1) → ZMod 2) = decide (a = 1) :: bits u := by
  simp [bits, List.ofFn_succ]

theorem dot_cons {k : ℕ} (a b : ZMod 2) (u v : Fin k → ZMod 2) :
    dotProduct (Fin.cons a u : Fin (k+1) → ZMod 2) (Fin.cons b v) = a * b + dotProduct u v := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem sum_cons {k : ℕ} (f : (Fin (k+1) → ZMod 2) → ℤ) :
    ∑ x, f x = ∑ a : ZMod 2, ∑ x' : Fin k → ZMod 2, f (Fin.cons a x') := by
  rw [← (Fin.consEquiv (fun _ => ZMod 2)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sumZ (g : ZMod 2 → ℤ) : ∑ a : ZMod 2, g a = g 0 + g 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu, Finset.sum_pair (by decide)]

theorem zdec (a b q : ZMod 2) : decide (a * b + q = 1) =
    Bool.xor (decide (a = 1) && decide (b = 1)) (decide (q = 1)) := by
  revert a b q; decide

theorem dz0 : decide ((0 : ZMod 2) = 1) = false := by decide

theorem dz1 : decide ((1 : ZMod 2) = 1) = true := by decide

noncomputable def T (k : ℕ) (C : Circuit) (zl : List Bool) : ℤ :=
  ∑ x : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2,
    sig (Bool.xor (C.eval (bits x ++ bits y ++ zl)) (decide (dotProduct x y = 1)))

def Q4 (g : Bool → Bool → ℤ) : ℤ := g false false + g false true + g true false + g true true

theorem Tdec (k : ℕ) (C : Circuit) (zl : List Bool) :
    T (k+1) C zl = ∑ x : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2, Q4 (fun A B =>
      sig (Bool.xor (Bool.xor (C.eval (A :: (bits x ++ B :: (bits y ++ zl)))) (A && B))
        (decide (dotProduct x y = 1)))) := by
  unfold T
  simp only [sum_cons, bits_cons, dot_cons, zdec, List.cons_append, List.append_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sumZ, sumZ, sumZ]
  simp only [Q4]
  simp only [show decide True = true from rfl, dz0, dz1, Bool.xor_assoc]
  ring

theorem T0 (C : Circuit) (zl : List Bool) : T 0 C zl = sig (C.eval zl) := by
  simp [T, bits, dotProduct]

theorem idA (a q : Bool) (c : Bool → Bool → Bool) (e : Bool → Bool)
    (hc : ∀ A B, c A B = Bool.xor (a && A) (e B)) :
    Q4 (fun A B => sig (Bool.xor (Bool.xor (c A B) (A && B)) q)) = 2 * sig (Bool.xor (e a) q) := by
  simp only [Q4, hc]
  cases a <;> cases e false <;> cases e true <;> cases q <;> simp [sig]

theorem idB (q : Bool) (c : Bool → Bool → Bool) (pB : Bool → Bool) (D : Bool → Bool → Bool)
    (hD : ∀ b d, D b d = Bool.xor (c (Bool.xor (pB d) b) d) (d && Bool.xor (pB d) b)) :
    Q4 (fun A B => sig (Bool.xor (Bool.xor (c A B) (A && B)) q)) =
      sig (Bool.xor (D false false) q) + sig (Bool.xor (D false true) q) +
        sig (Bool.xor (D true false) q) + sig (Bool.xor (D true true) q) := by
  simp only [Q4, hD]
  cases pB false <;> cases pB true <;> simp <;> ring

theorem idP (pr e q : Bool) :
    Q4 (fun A B => sig (Bool.xor (Bool.xor (Bool.xor e (pr && A && B)) (A && B)) q)) =
      (if pr then 4 else 2) * sig (Bool.xor e q) := by
  cases pr <;> cases e <;> cases q <;> simp [Q4, sig] <;> norm_num

def comb {m : ℕ} (E : Fin 4 → Fin m → Circuit) : Fin (4 * m) → Circuit :=
  fun i => E (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem sum_comb {m : ℕ} (E : Fin 4 → Fin m → Circuit) (f : Circuit → ℤ) :
    ∑ i, f (comb E i) = ∑ j, ∑ i, f (E j i) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [comb]

theorem ofFn_getD (w : List Bool) (n : ℕ) (hw : w.length = n) :
    List.ofFn (fun i : Fin n => w.getD i false) = w := by
  subst hw
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]


/-! ## Fixing an input, negating, splitting a sign in two -/

theorem gd_app_right (l l' : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l').getD i false = l'.getD (i - l.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

def mf (m n w : ℕ) : ℕ := if w < m then w else if w = m then n else if w ≤ n then w - 1 else w

theorem mf_lo (m n w : ℕ) (h : w < m) : mf m n w = w := by unfold mf; rw [if_pos h]

theorem mf_eq (m n : ℕ) : mf m n m = n := by unfold mf; simp

theorem mf_mid (m n w : ℕ) (h1 : m < w) (h2 : w ≤ n) : mf m n w = w - 1 := by
  unfold mf; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem mf_hi (m n w : ℕ) (hm : m ≤ n) (h : n < w) : mf m n w = w := by
  unfold mf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem mf_lt (m n w j : ℕ) (hm : m ≤ n) (h : w < n + 1 + j) : mf m n w < n + (1 + j) := by
  unfold mf; split_ifs <;> omega

def cg (c : Bool) : Gate := if c then ⟨.and, []⟩ else ⟨.or, []⟩

theorem ev_cg (c : Bool) (V : ℕ → Bool) : ev (cg c) V = c := by
  cases c <;> simp [cg, ev, GateOp.eval]

theorem paid_cg (c : Bool) : paid (cg c) = false := by cases c <;> simp [cg, paid]

def Fx (C : Circuit) (m n : ℕ) (c : Bool) (k : ℕ) : Gate :=
  if k = 0 then cg c else ren (mf m n) (gA C (k-1))

theorem Fx_0 (C : Circuit) (m n : ℕ) (c : Bool) : Fx C m n c 0 = cg c := by simp [Fx]

theorem Fx_s (C : Circuit) (m n : ℕ) (c : Bool) (j : ℕ) :
    Fx C m n c (j + 1) = ren (mf m n) (gA C j) := by simp [Fx]

theorem fixIn (n m : ℕ) (hm : m ≤ n) (C : Circuit) (hC : Legal (n+1) C) (c : Bool) :
    ∃ E : Circuit, Legal n E ∧ cost E = cost C ∧
      ∀ l1 l2 : List Bool, l1.length = m → l1.length + l2.length = n →
        E.eval (l1 ++ l2) = C.eval (l1 ++ c :: l2) := by
  have hrb : ∀ k < C.gates.length + 1, ∀ i ∈ (Fx C m n c k).inputs, i < n + k := by
    intro k hk i hi
    rcases k with _ | j
    · rw [Fx_0] at hi; cases c <;> simp [cg] at hi
    · rw [Fx_s] at hi
      simp only [ren, List.mem_map] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      have := mf_lt m n a j hm (by have := hC.1 j (by omega) a ha; omega)
      omega
  refine ⟨mk (Fx C m n c) (C.gates.length + 1) (mf m n C.output), legal_mk n _ _ _ hrb ?_, ?_, ?_⟩
  · intro k hk
    rcases k with _ | j
    · rw [Fx_0]; cases c <;> simp [cg]
    · rw [Fx_s]; exact legal_ren (n+1) C hC _ j (by omega)
  · rw [cost_mk, cost_eq, Finset.sum_range_succ']
    simp only [Fx_s, Fx_0, paid_ren, paid_cg]
    simp
  · intro l1 l2 h1 h2
    have FE := factsW n (mk (Fx C m n c) (C.gates.length + 1) (mf m n C.output))
      (rb_mk n _ _ _ hrb) (l1 ++ l2) (by simp; omega)
    have FC := factsW (n+1) C hC.1 (l1 ++ c :: l2) (by simp; omega)
    have key : ∀ w, WC (mk (Fx C m n c) (C.gates.length + 1) (mf m n C.output)) (l1 ++ l2)
        (mf m n w) = WC C (l1 ++ c :: l2) w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      by_cases w1 : w < m
      · rw [mf_lo m n w w1, FE.1 w (by omega), FC.1 w (by omega), gd_app_left _ _ _ (by omega),
          gd_app_left _ _ _ (by omega)]
      by_cases w2 : w = m
      · subst w2
        have e := FE.2.1 0 (by simp)
        simp only [Nat.add_zero] at e
        rw [gA_mk _ _ _ _ (by omega), Fx_0, ev_cg] at e
        rw [mf_eq, e, FC.1 w (by omega), gd_app_right _ _ _ (by omega)]
        simp [h1]
      by_cases w3 : w ≤ n
      · rw [mf_mid m n w (by omega) w3, FE.1 (w-1) (by omega), FC.1 w (by omega),
          gd_app_right _ _ _ (by omega), gd_app_right _ _ _ (by omega), h1]
        rw [show w - m = (w - 1 - m) + 1 by omega, List.getD_cons_succ]
      by_cases w4 : w < n + 1 + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + 1 + j := ⟨w - (n+1), by omega⟩
        have hj : j < C.gates.length := by omega
        have e := FE.2.1 (j + 1) (by simp; omega)
        rw [gA_mk _ _ _ _ (by omega), Fx_s, ev_ren] at e
        rw [mf_hi m n (n + 1 + j) hm (by omega), show n + 1 + j = n + (j + 1) by omega, e,
          show n + (j + 1) = n + 1 + j by omega, FC.2.1 j hj]
        apply ev_loc
        intro i hi
        have := hC.1 j hj i hi
        exact ih i (by omega)
      · rw [mf_hi m n w hm (by omega), FE.2.2 w (by simp; omega), FC.2.2 w (by omega)]
    exact key C.output

theorem sig_not (v : Bool) : sig (!v) = - sig v := by cases v <;> simp [sig]

theorem wires_append (C : Circuit) (L : List Gate) (o : ℕ) (x : List Bool) :
    (⟨C.gates ++ L, o⟩ : Circuit).wires x = L.foldl (stp ev) (C.wires x) := by
  simp only [Circuit.wires, List.foldl_append]; rfl

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq]; exact (fold_spec ev ev_loc C.gates x).1

def g0 (C : Circuit) (n : ℕ) : Gate :=
  if C.output < n + C.gates.length then ⟨.and, [C.output]⟩ else ⟨.or, []⟩

theorem ev_g0 (C : Circuit) (n : ℕ) (x : List Bool) (hx : x.length = n) :
    ev (g0 C n) (fun i => (C.wires x).getD i false) = C.eval x := by
  unfold g0
  split_ifs with h
  · simp [ev, GateOp.eval, Circuit.eval]
  · simp only [ev, GateOp.eval, List.map_nil, List.any_nil, Circuit.eval]
    rw [gd_out _ _ (by rw [wires_len]; omega)]

def negC (C : Circuit) (n : ℕ) : Circuit :=
  ⟨C.gates ++ [g0 C n, ⟨.not, [n + C.gates.length]⟩], n + C.gates.length + 1⟩

theorem negC_eval (C : Circuit) (n : ℕ) (x : List Bool) (hx : x.length = n) :
    (negC C n).eval x = !(C.eval x) := by
  have hl := wires_len C x
  show ((negC C n).wires x).getD (n + C.gates.length + 1) false = _
  rw [negC, wires_append]
  simp only [List.foldl_cons, List.foldl_nil, stp]
  have e1 : (C.wires x ++ [ev (g0 C n) fun i => (C.wires x).getD i false]).length =
      n + C.gates.length + 1 := by simp [hl, hx]
  rw [← e1, gd_app_len]
  have e2 : (C.wires x ++ [ev (g0 C n) fun i => (C.wires x).getD i false]).getD
      (n + C.gates.length) false = C.eval x := by
    rw [show n + C.gates.length = (C.wires x).length by rw [hl, hx], gd_app_len, ev_g0 C n x hx]
  have ev1 : ∀ (a : ℕ) (V : ℕ → Bool), ev ⟨GateOp.not, [a]⟩ V = !(V a) := fun _ _ => rfl
  simp only [ev1]
  rw [e2]

theorem gA_app (C : Circuit) (L : List Gate) (o j : ℕ) (hj : j < C.gates.length) :
    gA ⟨C.gates ++ L, o⟩ j = gA C j := by
  simp only [gA_def, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

theorem gA_app_r (C : Circuit) (L : List Gate) (o i : ℕ) :
    gA ⟨C.gates ++ L, o⟩ (C.gates.length + i) = L.getD i ⟨GateOp.or, []⟩ := by
  simp only [gA_def, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp

theorem negC_legal (C : Circuit) (n : ℕ) (hC : Legal n C) : Legal n (negC C n) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    have hj' : j < C.gates.length + 2 := by simpa [negC] using hj
    change i ∈ (gA ⟨C.gates ++ _, _⟩ j).inputs at hi
    by_cases h1 : j < C.gates.length
    · rw [gA_app C _ _ j h1] at hi
      exact hC.1 j h1 i hi
    · obtain ⟨q, rfl⟩ : ∃ q, j = C.gates.length + q := ⟨j - C.gates.length, by omega⟩
      rw [gA_app_r] at hi
      rcases q with _ | _ | q
      · simp only [List.getD_cons_zero, g0] at hi
        split_ifs at hi with ho
        · simp at hi; omega
        · simp at hi
      · simp at hi; omega
      · omega
  · intro g hg
    simp only [negC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hC.2 g hg
    · unfold g0; split_ifs <;> simp
    · simp

theorem negC_cost (C : Circuit) (n : ℕ) : cost (negC C n) = cost C := by
  have : paid (g0 C n) = false := by unfold g0; split_ifs <;> simp [paid]
  have h2 : paid ⟨GateOp.not, [n + C.gates.length]⟩ = false := by simp [paid]
  simp only [cost, negC, List.countP_append, List.countP_cons, List.countP_nil, this, h2]
  simp

theorem dbl (n c : ℕ) (D : Circuit) (hD : Legal n D) (hc : cost D ≤ c + 1) :
    ∃ F : Fin 4 → Circuit, (∀ j, Legal n (F j) ∧ cost (F j) ≤ c) ∧
      ∀ zl : List Bool, zl.length = n → 2 * sig (D.eval zl) = ∑ j, sig ((F j).eval zl) := by
  by_cases hcd : cost D ≤ c
  · refine ⟨![D, D, D, negC D n], ?_, ?_⟩
    · intro j
      fin_cases j
      · exact ⟨hD, hcd⟩
      · exact ⟨hD, hcd⟩
      · exact ⟨hD, hcd⟩
      · exact ⟨negC_legal D n hD, by simp [negC_cost, hcd]⟩
    · intro zl hz
      simp only [Fin.sum_univ_four]
      simp [negC_eval D n zl hz, sig_not]
      ring
  · obtain ⟨D4, hD4, hv⟩ := core n D hD (by omega)
    refine ⟨![D4 0, D4 1, D4 2, negC (D4 3) n], ?_, ?_⟩
    · intro j
      fin_cases j
      · exact ⟨(hD4 0).1, by have := (hD4 0).2; simp; omega⟩
      · exact ⟨(hD4 1).1, by have := (hD4 1).2; simp; omega⟩
      · exact ⟨(hD4 2).1, by have := (hD4 2).2; simp; omega⟩
      · exact ⟨negC_legal _ n (hD4 3).1, by have := (hD4 3).2; simp [negC_cost]; omega⟩
    · intro zl hz
      have := hv (fun i => zl.getD i false)
      rw [ofFn_getD zl n hz] at this
      simp only [Fin.sum_univ_four]
      simp [negC_eval _ n zl hz, sig_not]
      have e : ∀ v, sig v = s v := fun _ => rfl
      simp only [e] at this ⊢
      linarith


/-! ## Adding one pair, with or without its product -/

def mi (k w : ℕ) : ℕ := if w < k then w + 1 else w + 2

theorem mi_le (k w : ℕ) : mi k w ≤ w + 2 := by unfold mi; split_ifs <;> omega

theorem mi_lo (k w : ℕ) (h : w < k) : mi k w = w + 1 := by unfold mi; rw [if_pos h]

theorem mi_hi (k w : ℕ) (h : k ≤ w) : mi k w = w + 2 := by unfold mi; rw [if_neg (by omega)]

def Fp (C : Circuit) (k n : ℕ) (pr : Bool) (j : ℕ) : Gate :=
  if j < C.gates.length then ren (mi k) (gA C j)
  else if j = C.gates.length then (if pr then ⟨.and, [0, k+1]⟩ else ⟨.or, []⟩)
  else if j = C.gates.length + 1 then
    (if C.output < n + C.gates.length then ⟨.and, [mi k C.output]⟩ else ⟨.or, []⟩)
  else if j = C.gates.length + 2 then
    ⟨.mod 2, [n + 3 + C.gates.length, n + 2 + C.gates.length]⟩
  else ⟨.not, [n + 4 + C.gates.length]⟩

section
variable (C : Circuit) (k n : ℕ) (pr : Bool)

theorem Fp_a (j : ℕ) (hj : j < C.gates.length) : Fp C k n pr j = ren (mi k) (gA C j) := by
  unfold Fp; rw [if_pos hj]

theorem Fp_P : Fp C k n pr C.gates.length =
    (if pr then ⟨.and, [0, k+1]⟩ else ⟨.or, []⟩) := by
  unfold Fp; rw [if_neg (by omega), if_pos rfl]

theorem Fp_0 : Fp C k n pr (C.gates.length + 1) =
    (if C.output < n + C.gates.length then ⟨.and, [mi k C.output]⟩ else ⟨.or, []⟩) := by
  unfold Fp; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem Fp_1 : Fp C k n pr (C.gates.length + 2) =
    ⟨.mod 2, [n + 3 + C.gates.length, n + 2 + C.gates.length]⟩ := by
  unfold Fp; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem Fp_2 : Fp C k n pr (C.gates.length + 3) = ⟨.not, [n + 4 + C.gates.length]⟩ := by
  unfold Fp; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end

theorem insPair (k t : ℕ) (C : Circuit) (hC : Legal (2*k+t) C) (pr : Bool) :
    ∃ C' : Circuit, Legal (2*(k+1)+t) C' ∧ cost C' = cost C + (if pr then 1 else 0) ∧
      ∀ (A B : Bool) (l1 l2 : List Bool), l1.length = k → l2.length = k + t →
        C'.eval (A :: (l1 ++ B :: l2)) = Bool.xor (C.eval (l1 ++ l2)) (pr && A && B) := by
  have hrb : ∀ j < C.gates.length + 4, ∀ i ∈ (Fp C k (2*k+t) pr j).inputs,
      i < 2*(k+1)+t + j := by
    intro j hj i hi
    by_cases h1 : j < C.gates.length
    · rw [Fp_a C k _ pr j h1] at hi
      simp only [ren, List.mem_map] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      have := hC.1 j h1 a ha
      have := mi_le k a
      omega
    · obtain ⟨q, rfl⟩ : ∃ q, j = C.gates.length + q := ⟨j - C.gates.length, by omega⟩
      rcases q with _ | _ | _ | _ | q
      · rw [Nat.add_zero, Fp_P] at hi
        cases pr <;> simp at hi <;> omega
      · rw [Fp_0] at hi
        split_ifs at hi with ho
        · simp at hi; have := mi_le k C.output; omega
        · simp at hi
      · rw [Fp_1] at hi; simp at hi; omega
      · rw [Fp_2] at hi; simp at hi; omega
      · omega
  have hops : ∀ j < C.gates.length + 4, (Fp C k (2*k+t) pr j).inputs.length ≤ 2 ∧
      ((Fp C k (2*k+t) pr j).op = .and ∨ (Fp C k (2*k+t) pr j).op = .or ∨
        (Fp C k (2*k+t) pr j).op = .mod 2 ∨
        ((Fp C k (2*k+t) pr j).op = .not ∧ (Fp C k (2*k+t) pr j).inputs.length = 1)) := by
    intro j hj
    by_cases h1 : j < C.gates.length
    · rw [Fp_a C k _ pr j h1]; exact legal_ren _ C hC _ j h1
    · obtain ⟨q, rfl⟩ : ∃ q, j = C.gates.length + q := ⟨j - C.gates.length, by omega⟩
      rcases q with _ | _ | _ | _ | q
      · rw [Nat.add_zero, Fp_P]; cases pr <;> simp
      · rw [Fp_0]; split_ifs <;> simp
      · rw [Fp_1]; simp
      · rw [Fp_2]; simp
      · omega
  let C' := mk (Fp C k (2*k+t) pr) (C.gates.length + 4) (2*k+t+5+C.gates.length)
  refine ⟨C', legal_mk _ _ _ _ hrb hops, ?_, ?_⟩
  · rw [cost_mk, cost_eq, Finset.sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero]
    have e1 : ∑ x ∈ Finset.range C.gates.length,
        (if paid (Fp C k (2*k+t) pr x) = true then 1 else 0) =
        ∑ x ∈ Finset.range C.gates.length, (if paid (gA C x) = true then 1 else 0) :=
      Finset.sum_congr rfl (fun x hx => by rw [Fp_a C k _ pr x (by simpa using hx), paid_ren])
    have e2 : paid (Fp C k (2*k+t) pr C.gates.length) = pr := by
      rw [Fp_P]; cases pr <;> simp [paid]
    have e3 : paid (Fp C k (2*k+t) pr (C.gates.length + 1)) = false := by
      rw [Fp_0]; split_ifs <;> simp [paid]
    have e4 : paid (Fp C k (2*k+t) pr (C.gates.length + 2)) = false := by
      rw [Fp_1]; simp [paid]
    have e5 : paid (Fp C k (2*k+t) pr (C.gates.length + 3)) = false := by
      rw [Fp_2]; simp [paid]
    simp only [e1, e2, e3, e4, e5]
    cases pr <;> simp
  · intro A B l1 l2 h1 h2
    have hx' : (A :: (l1 ++ B :: l2)).length = 2*(k+1)+t := by simp; omega
    have FN := factsW (2*(k+1)+t) C' (rb_mk _ _ _ _ hrb) (A :: (l1 ++ B :: l2)) hx'
    have FC := factsW (2*k+t) C hC.1 (l1 ++ l2) (by simp; omega)
    have gN : ∀ j < C.gates.length + 4, gA C' j = Fp C k (2*k+t) pr j :=
      fun j hj => gA_mk _ _ _ j hj
    have key : ∀ w < 2*k+t + C.gates.length,
        WC C' (A :: (l1 ++ B :: l2)) (mi k w) = WC C (l1 ++ l2) w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      intro hw
      by_cases w1 : w < k
      · rw [mi_lo k w w1, FN.1 (w+1) (by omega), FC.1 w (by omega), List.getD_cons_succ,
          gd_app_left _ _ _ (by omega), gd_app_left _ _ _ (by omega)]
      by_cases w2 : w < 2*k+t
      · rw [mi_hi k w (by omega), FN.1 (w+2) (by omega), FC.1 w (by omega), List.getD_cons_succ,
          gd_app_right _ _ _ (by omega), gd_app_right _ _ _ (by omega), h1,
          show w + 1 - k = (w - k) + 1 by omega, List.getD_cons_succ]
      · obtain ⟨j, rfl⟩ : ∃ j, w = 2*k+t + j := ⟨w - (2*k+t), by omega⟩
        have hj : j < C.gates.length := by omega
        rw [mi_hi k _ (by omega), show 2*k+t+j+2 = 2*(k+1)+t + j by omega,
          FN.2.1 j (by simp [C']; omega), gN j (by omega), Fp_a C k _ pr j hj, ev_ren,
          FC.2.1 j hj]
        apply ev_loc
        intro i hi
        have := hC.1 j hj i hi
        exact ih i (by omega) (by omega)
    have hv0 : WC C' (A :: (l1 ++ B :: l2)) (2*(k+1)+t + (C.gates.length + 1)) =
        C.eval (l1 ++ l2) := by
      rw [FN.2.1 _ (by simp [C']), gN _ (by omega), Fp_0]
      split_ifs with ho
      · simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id, Bool.and_true]
        rw [key _ ho]; rfl
      · simp only [ev, GateOp.eval, List.map_nil, List.any_nil, Circuit.eval]
        rw [gd_out _ _ (by rw [wires_len]; simp; omega)]
    have hP : WC C' (A :: (l1 ++ B :: l2)) (2*(k+1)+t + C.gates.length) = (pr && A && B) := by
      rw [FN.2.1 _ (by simp [C']), gN _ (by omega), Fp_P]
      cases pr
      · simp [ev, GateOp.eval]
      · simp only [if_true, ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id, Bool.and_true]
        rw [FN.1 0 (by omega), FN.1 (k+1) (by omega), List.getD_cons_succ,
          gd_app_right _ _ _ (by omega), h1, Nat.sub_self]
        simp
    show WC C' (A :: (l1 ++ B :: l2)) (2*k+t+5+C.gates.length) = _
    rw [show 2*k+t+5+C.gates.length = 2*(k+1)+t + (C.gates.length + 3) by omega,
      FN.2.1 _ (by simp [C']), gN _ (by omega), Fp_2]
    have ev1 : ∀ (a : ℕ) (V : ℕ → Bool), ev ⟨GateOp.not, [a]⟩ V = !(V a) := fun _ _ => rfl
    simp only [ev1]
    rw [show 2*k+t + 4 + C.gates.length = 2*(k+1)+t + (C.gates.length + 2) by omega,
      FN.2.1 _ (by simp [C']), gN _ (by omega), Fp_1]
    have ev2 : ∀ (a b : ℕ) (V : ℕ → Bool), ev ⟨GateOp.mod 2, [a, b]⟩ V =
        decide (List.count true [V a, V b] % 2 = 0) := fun _ _ _ => rfl
    simp only [ev2]
    rw [show 2*k+t + 3 + C.gates.length = 2*(k+1)+t + (C.gates.length + 1) by omega, hv0,
      show 2*k+t + 2 + C.gates.length = 2*(k+1)+t + C.gates.length by omega, hP]
    cases C.eval (l1 ++ l2) <;> cases pr <;> cases A <;> cases B <;> decide

theorem part2 : ∀ (k r t : ℕ) (D : Circuit), r ≤ k → Legal t D →
    ∃ C : Circuit, Legal (2*k+t) C ∧ cost C = cost D + r ∧
      ∀ zl : List Bool, zl.length = t → T k C zl = 2^(k+r) * sig (D.eval zl) := by
  intro k
  induction k with
  | zero =>
    intro r t D hr hD
    obtain rfl : r = 0 := by omega
    refine ⟨D, by simpa using hD, by simp, ?_⟩
    intro zl _
    rw [T0]; simp
  | succ k ih =>
    intro r t D hr hD
    obtain ⟨Ck, hCl, hCc, hCT⟩ := ih (r - (if 0 < r then 1 else 0)) t D
      (by split_ifs <;> omega) hD
    obtain ⟨C', hl', hc', hv'⟩ := insPair k t Ck hCl (decide (0 < r))
    refine ⟨C', hl', ?_, ?_⟩
    · rw [hc', hCc]
      by_cases h : 0 < r <;> simp [h] <;> omega
    · intro zl hz
      have hq : ∀ x y : Fin k → ZMod 2, Q4 (fun A B => sig (Bool.xor (Bool.xor
          (C'.eval (A :: (bits x ++ B :: (bits y ++ zl)))) (A && B))
          (decide (dotProduct x y = 1)))) = (if decide (0 < r) then 4 else 2) *
          sig (Bool.xor (Ck.eval (bits x ++ bits y ++ zl)) (decide (dotProduct x y = 1))) := by
        intro x y
        have h2 : (bits y ++ zl).length = k + t := by simp [bits_len, hz]
        simp only [hv' _ _ (bits x) (bits y ++ zl) (bits_len x) h2]
        rw [← List.append_assoc]
        exact idP _ _ _
      rw [Tdec, Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hq x y))]
      simp only [← Finset.mul_sum]
      rw [show (∑ x : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2, sig (Bool.xor
          (Ck.eval (bits x ++ bits y ++ zl)) (decide (dotProduct x y = 1)))) = T k Ck zl from rfl,
        hCT zl hz]
      by_cases h : 0 < r
      · simp only [h, decide_true, if_true]
        rw [show k + 1 + r = (k + (r - 1)) + 2 by omega, pow_add]
        ring
      · obtain rfl : r = 0 := by omega
        simp only [lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [show k + 1 + 0 = (k + 0) + 1 by omega, pow_succ]
        ring


/-! ## The expansion, one pair at a time -/

theorem part1 : ∀ (k t s : ℕ) (C : Circuit), Legal (2*k+t) C → cost C ≤ s →
    ∃ D : Fin (4^(min k s)) → Circuit, (∀ i, Legal t (D i) ∧ cost (D i) ≤ s - min k s) ∧
      ∀ zl : List Bool, zl.length = t → T k C zl = 2^(k - min k s) * ∑ i, sig ((D i).eval zl) := by
  intro k
  induction k with
  | zero =>
    intro t s C hC hcs
    simp only [Nat.zero_min, pow_zero, Nat.sub_zero, one_mul]
    refine ⟨fun _ => C, fun _ => ⟨by simpa using hC, hcs⟩, ?_⟩
    intro zl _
    rw [T0]; simp
  | succ k ih =>
    intro t s C hC hcs
    have hC' : Legal (1 + (2*k+1+t)) C := by
      rw [show 1 + (2*k+1+t) = 2*(k+1)+t by ring]; exact hC
    have hlen : ∀ (B : Bool) (x y : Fin k → ZMod 2) (zl : List Bool), zl.length = t →
        (bits x ++ B :: (bits y ++ zl)).length = 2*k+1+t := by
      intro B x y zl hz; simp [bits_len, hz]; omega
    rcases main (2*k+1+t) C hC' with ⟨a, E, hEl, hEc, hEv⟩ | ⟨hpos, p, hp⟩
    · have hEv' : ∀ u w, w.length = 2*k+1+t → C.eval (u :: w) = Bool.xor (a && u) (E.eval w) := by
        intro u w hw
        have := hEv u (fun i => w.getD i false)
        rwa [ofFn_getD w _ hw] at this
      have hEl' : Legal (2*k+t+1) E := by rw [show 2*k+t+1 = 2*k+1+t by omega]; exact hEl
      obtain ⟨E', hE'l, hE'c, hE'v⟩ := fixIn (2*k+t) k (by omega) E hEl' a
      obtain ⟨D, hD, hDT⟩ := ih t s E' hE'l (by omega)
      have key : ∀ zl : List Bool, zl.length = t → T (k+1) C zl = 2 * T k E' zl := by
        intro zl hz
        rw [Tdec]
        unfold T
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        refine (idA a _ _ (fun B => E.eval (bits x ++ B :: (bits y ++ zl)))
          (fun A B => hEv' A _ (hlen B x y zl hz))).trans ?_
        rw [List.append_assoc, hE'v (bits x) (bits y ++ zl) (bits_len x)
          (by simp [bits_len, hz]; omega)]
      by_cases hsk : s ≤ k
      · have e1 : min (k+1) s = min k s := by omega
        rw [e1]
        refine ⟨D, hD, ?_⟩
        intro zl hz
        rw [key zl hz, hDT zl hz, ← mul_assoc,
          show k + 1 - min k s = (k - min k s) + 1 by omega, pow_succ]
        ring
      · have e1 : min (k+1) s = min k s + 1 := by omega
        have e2 : min k s = k := by omega
        rw [e1]
        have hdb := fun i => dbl t (s - (min k s + 1)) (D i) (hD i).1
          (by have := (hD i).2; omega)
        choose F hF hFv using hdb
        rw [pow_succ']
        refine ⟨comb (fun j i => F i j), fun i => hF _ _, ?_⟩
        intro zl hz
        rw [key zl hz, hDT zl hz, sum_comb (fun j i => F i j) (fun D => sig (D.eval zl)),
          Finset.sum_comm, show k + 1 - (min k s + 1) = 0 by omega,
          show k - min k s = 0 by omega, pow_zero, one_mul, one_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => hFv i zl hz)
    · have hs : 1 ≤ s := by omega
      choose Dbd hDbd using hp
      have hDl : ∀ b d, Legal (2*k+t+1) (Dbd b d) := fun b d => by
        rw [show 2*k+t+1 = 2*k+1+t by omega]; exact (hDbd b d).1
      have hfx := fun b d => fixIn (2*k+t) k (by omega) (Dbd b d) (hDl b d) d
      choose D' hD'l hD'c hD'v using hfx
      have hih := fun b d => ih t (s-1) (D' b d) (hD'l b d)
        (by rw [hD'c]; have := (hDbd b d).2.1; omega)
      choose E hE hET using hih
      have key : ∀ zl : List Bool, zl.length = t → T (k+1) C zl =
          T k (D' false false) zl + T k (D' false true) zl + T k (D' true false) zl +
            T k (D' true true) zl := by
        intro zl hz
        rw [Tdec]
        unfold T
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        refine (idB _ (fun A B => C.eval (A :: (bits x ++ B :: (bits y ++ zl))))
          (fun d => p (fun i => (bits x ++ d :: (bits y ++ zl)).getD i false))
          (fun b d => (Dbd b d).eval (bits x ++ d :: (bits y ++ zl))) ?_).trans ?_
        · intro b d
          have := (hDbd b d).2.2 (fun i => (bits x ++ d :: (bits y ++ zl)).getD i false)
          rw [ofFn_getD _ _ (hlen d x y zl hz)] at this
          exact this
        · have h2 : (bits x).length + (bits y ++ zl).length = 2*k+t := by
            simp [bits_len, hz]; omega
          simp only [List.append_assoc, hD'v _ _ (bits x) (bits y ++ zl) (bits_len x) h2]
      have e1 : min (k+1) s = min k (s-1) + 1 := by omega
      rw [e1, pow_succ']
      let G : Fin 4 → Fin (4^(min k (s-1))) → Circuit :=
        ![E false false, E false true, E true false, E true true]
      have hall : ∀ j i, Legal t (G j i) ∧ cost (G j i) ≤ s - (min k (s-1) + 1) := by
        intro j i
        fin_cases j
        · exact ⟨(hE false false i).1, by have := (hE false false i).2; simp [G]; omega⟩
        · exact ⟨(hE false true i).1, by have := (hE false true i).2; simp [G]; omega⟩
        · exact ⟨(hE true false i).1, by have := (hE true false i).2; simp [G]; omega⟩
        · exact ⟨(hE true true i).1, by have := (hE true true i).2; simp [G]; omega⟩
      refine ⟨comb G, fun i => hall _ _, ?_⟩
      intro zl hz
      rw [key zl hz, hET false false zl hz, hET false true zl hz, hET true false zl hz,
        hET true true zl hz, sum_comb G (fun D => sig (D.eval zl)), Fin.sum_univ_four,
        show k + 1 - (min k (s-1) + 1) = k - min k (s-1) by omega]
      simp only [G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
      ring

end PEqualNP.Outside.L_meta_29753

open PEqualNP.Outside.L_meta_29753 in
theorem PEqualNP.Outside.L_meta_29753 : ∀ (k t s : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let V := Fin k → ZMod 2
  let Z := Fin t → Bool
  let r := min k s
  let sig := fun (v : Bool) => if v then (-1 : ℤ) else 1
  let bits := fun (u : V) => List.ofFn (fun i : Fin k => decide (u i = 1))
  let total := fun (C : Circ) (z : Z) => ∑ x : V, ∑ y : V,
    sig (Bool.xor (C.eval (bits x ++ bits y ++ List.ofFn z))
      (decide (dotProduct x y = 1)))
  (∀ C : Circ, legal (2*k+t) C → cost C ≤ s →
    ∃ D : Fin (4^r) → Circ, (∀ i, legal t (D i) ∧ cost (D i) ≤ s-r) ∧
      ∀ z : Z, total C z = (2:ℤ)^(k-r) *
        ∑ i : Fin (4^r), sig ((D i).eval (List.ofFn z))) ∧
  (∀ D : Circ, legal t D → cost D ≤ s-r →
    ∃ C : Circ, legal (2*k+t) C ∧ cost C ≤ s ∧
      ∀ z : Z, total C z = (2:ℤ)^(k+r)*sig (D.eval (List.ofFn z))) := by
  intro k t s Circ legal cost V Z r sig bits total
  constructor
  · intro C hC hc
    obtain ⟨D, hD, hT⟩ := part1 k t s C hC hc
    exact ⟨D, hD, fun z => hT (List.ofFn z) (by simp)⟩
  · intro D hD hc
    obtain ⟨C, hCl, hCc, hCT⟩ := part2 k (min k s) t D (min_le_left _ _) hD
    refine ⟨C, hCl, ?_, fun z => hCT (List.ofFn z) (by simp)⟩
    have := min_le_right k s
    have hc' : PEqualNP.Outside.L_meta_29753.cost D ≤ s - min k s := hc
    show PEqualNP.Outside.L_meta_29753.cost C ≤ s
    omega
