import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32587

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

abbrev F := ZMod 2
def f2b (a : F) : Bool := decide (a = 1)
def b2f (b : Bool) : F := if b then 1 else 0

lemma f_cases (a : F) : a = 0 ∨ a = 1 := by
  match a with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

lemma f_one_ne_zero : (1 : F) ≠ 0 := by decide
lemma f_sq (a : F) : a * a = a := by rcases f_cases a with rfl | rfl <;> decide
lemma f_add_self (a : F) : a + a = 0 := by rcases f_cases a with rfl | rfl <;> decide
lemma f_sub_eq_add (a b : F) : a - b = a + b := by
  rcases f_cases a with rfl | rfl <;> rcases f_cases b with rfl | rfl <;> decide
lemma f_ne_iff_add_eq_one (a b : F) : a ≠ b ↔ a + b = 1 := by
  rcases f_cases a with rfl | rfl <;> rcases f_cases b with rfl | rfl <;> decide
lemma b2f_f2b (a : F) : b2f (f2b a) = a := by rcases f_cases a with rfl | rfl <;> rfl
lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by cases a <;> cases b <;> rfl
lemma b2f_or (a b : Bool) : b2f (a || b) = b2f a + b2f b + b2f a * b2f b := by
  cases a <;> cases b <;> rfl
lemma b2f_not (a : Bool) : b2f (!a) = b2f a + 1 := by cases a <;> rfl
lemma b2f_mod2_nil : b2f (GateOp.eval (.mod 2) []) = 1 := rfl
lemma b2f_mod2_one (a : Bool) : b2f (GateOp.eval (.mod 2) [a]) = b2f a + 1 := by cases a <;> rfl
lemma b2f_mod2_two (a b : Bool) : b2f (GateOp.eval (.mod 2) [a, b]) = b2f a + b2f b + 1 := by
  cases a <;> cases b <;> rfl

noncomputable def sign (a : F) : ℝ := if a = 0 then 1 else -1
lemma sign_zero : sign 0 = 1 := by simp [sign]
lemma sign_one : sign 1 = -1 := by simp [sign]
lemma sign_add (a b : F) : sign (a + b) = sign a * sign b := by
  rcases f_cases a with rfl | rfl <;> rcases f_cases b with rfl | rfl
  · simp [sign_zero]
  · simp [sign_zero, sign_one]
  · simp [sign_zero, sign_one]
  · rw [f_add_self, sign_zero, sign_one]; norm_num
lemma sign_le_one (a : F) : sign a ≤ 1 := by
  rcases f_cases a with rfl | rfl
  · rw [sign_zero]
  · rw [sign_one]; norm_num
lemma sign_quad_sum (a b c d : F) (h : a + b + c + d = 1) :
    |sign a + sign b + sign c + sign d| = 2 := by
  rcases f_cases a with rfl | rfl <;> rcases f_cases b with rfl | rfl <;>
  rcases f_cases c with rfl | rfl <;> rcases f_cases d with rfl | rfl <;>
  first | (exfalso; revert h; decide) | (simp only [sign_zero, sign_one]; norm_num)
lemma ite_eq_sign (b : Bool) (v : F) :
    (if b = decide (v = 1) then (1 : ℝ) else -1) = sign (b2f b + v) := by
  cases b <;> rcases f_cases v with rfl | rfl
  · simp [b2f, sign_zero]
  · simp [b2f, sign_one]
  · simp [b2f, sign_one]
  · rw [show b2f true = 1 from rfl, f_add_self, sign_zero]; simp

noncomputable def isMult (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

def gateLegal (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def circuitCost (C : Circuit) : ℕ := C.gates.countP isMult

def bitsOf (width : ℕ) (u : Fin width → F) : List Bool :=
  List.ofFn (fun j : Fin width => f2b (u j))

lemma bitsOf_length (width : ℕ) (u : Fin width → F) : (bitsOf width u).length = width := by
  simp [bitsOf]

lemma wires_length (gs : List Gate) (inp : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ inp).length = inp.length + gs.length := by
  unfold Circuit.wires; dsimp only
  induction gs generalizing inp with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1]

lemma wires_append (gs1 gs2 : List Gate) (inp : List Bool) :
    Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp = Circuit.wires ⟨gs2, 0⟩ (Circuit.wires ⟨gs1, 0⟩ inp) := by
  simp [Circuit.wires, List.foldl_append]

lemma wires_singleton (g : Gate) (inp : List Bool) :
    Circuit.wires ⟨[g], 0⟩ inp = inp ++ [g.op.eval (g.inputs.map (fun i => inp.getD i false))] := by
  simp [Circuit.wires]

lemma wires_getD_prefix (gs1 gs2 : List Gate) (inp : List Bool) (i : ℕ)
    (hi : i < inp.length + gs1.length) :
    (Circuit.wires ⟨gs1 ++ gs2, 0⟩ inp).getD i false = (Circuit.wires ⟨gs1, 0⟩ inp).getD i false := by
  rw [wires_append]
  have hlen : i < (Circuit.wires ⟨gs1, 0⟩ inp).length := by rwa [wires_length]
  generalize Circuit.wires ⟨gs1, 0⟩ inp = w at hlen ⊢
  induction gs2 generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons]
    have hlen' : i < (w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]).length := by
      simp; omega
    change (({ gates := gs, output := 0 } : Circuit).wires
      (w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))])).getD i false = w.getD i false
    rw [ih _ hlen']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]

lemma readsBack_append_one (w : ℕ) (gs : List Gate) (g : Gate)
    (h1 : ReadsBack w ⟨gs, 0⟩) (h2 : ∀ i ∈ g.inputs, i < w + gs.length) :
    ReadsBack w ⟨gs ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  simp only [gateAt, List.getD_eq_getElem?_getD] at hi
  by_cases hlt : j < gs.length
  · rw [List.getElem?_append_left hlt] at hi
    exact h1 j hlt i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
  · have hjeq : j = gs.length := by omega
    subst hjeq
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hi
    simp only [List.getElem?_cons_zero, Option.getD_some] at hi
    exact h2 i hi

lemma list_sum_flatMap {α β γ : Type*} [AddCommMonoid γ] (l : List α) (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma vec_add_self {α : Type*} [AddCommGroup α] [Module F α] (x : α) : x + x = 0 := by
  have h : (1 : F) + 1 = 0 := rfl
  calc x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [h, zero_smul]

def WF (w : ℕ) (gs : List Gate) : Prop :=
  ReadsBack w ⟨gs, 0⟩ ∧ ∀ h ∈ gs, gateLegal h

def evalW (w : ℕ) (gs : List Gate) (x : Fin w → F) (i : ℕ) : F :=
  b2f ((Circuit.wires ⟨gs, 0⟩ (bitsOf w x)).getD i false)

lemma evalW_input (w : ℕ) (gs : List Gate) (x : Fin w → F) (j : Fin w) :
    evalW w gs x j.val = x j := by
  have h := wires_getD_prefix [] gs (bitsOf w x) j.val (by simp [bitsOf_length, j.isLt])
  simp only [List.nil_append] at h
  unfold evalW
  rw [h]
  simp [Circuit.wires, bitsOf, List.getD_eq_getElem?_getD, j.isLt, b2f_f2b]

lemma evalW_append_left (w : ℕ) (gs1 gs2 : List Gate) (x : Fin w → F) (i : ℕ)
    (hi : i < w + gs1.length) : evalW w (gs1 ++ gs2) x i = evalW w gs1 x i := by
  unfold evalW
  rw [wires_getD_prefix gs1 gs2 (bitsOf w x) i (by rw [bitsOf_length]; exact hi)]

lemma evalW_append_new (w : ℕ) (gs : List Gate) (g : Gate) (x : Fin w → F) :
    evalW w (gs ++ [g]) x (w + gs.length) =
      b2f (g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ (bitsOf w x)).getD i false))) := by
  unfold evalW
  rw [wires_append, wires_singleton]
  have hlen : (Circuit.wires ⟨gs, 0⟩ (bitsOf w x)).length = w + gs.length := by
    rw [wires_length, bitsOf_length]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  simp

lemma wf_append_one (w : ℕ) (gs : List Gate) (g : Gate) (hwf : WF w gs)
    (hgl : gateLegal g) (hins : ∀ i ∈ g.inputs, i < w + gs.length) : WF w (gs ++ [g]) :=
  ⟨readsBack_append_one w gs g hwf.1 hins, fun h hh => by
    simp only [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hwf.2 h hh
    · exact hgl⟩

lemma exists_const_gate (w : ℕ) (gs : List Gate) (hwf : WF w gs) (c : F) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult ∧
      idx < w + (gs ++ gs').length ∧ ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = c := by
  rcases f_cases c with rfl | rfl
  · refine ⟨[⟨.or, []⟩], w + gs.length,
      wf_append_one w gs _ hwf ⟨by simp, Or.inr (Or.inl rfl)⟩ (by simp),
      by simp [isMult], by simp, fun x => by rw [evalW_append_new]; rfl⟩
  · refine ⟨[⟨.and, []⟩], w + gs.length,
      wf_append_one w gs _ hwf ⟨by simp, Or.inl rfl⟩ (by simp),
      by simp [isMult], by simp, fun x => by rw [evalW_append_new]; rfl⟩

lemma exists_xor_gate (w : ℕ) (gs : List Gate) (hwf : WF w gs) (i j : ℕ)
    (hi : i < w + gs.length) (hj : j < w + gs.length) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult ∧
      idx < w + (gs ++ gs').length ∧
      ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = evalW w gs x i + evalW w gs x j := by
  let g1 : Gate := ⟨.mod 2, [i, j]⟩
  let mIdx := w + gs.length
  let g2 : Gate := ⟨.not, [mIdx]⟩
  have hwf1 : WF w (gs ++ [g1]) := wf_append_one w gs g1 hwf ⟨by simp [g1], Or.inr (Or.inr (Or.inl rfl))⟩
    (by intro a ha; simp [g1] at ha; rcases ha with rfl | rfl <;> assumption)
  have hwf2 : WF w ((gs ++ [g1]) ++ [g2]) :=
    wf_append_one w (gs ++ [g1]) g2 hwf1 ⟨by simp [g2], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      (by intro a ha; simp [g2] at ha; subst ha; simp [mIdx])
  refine ⟨[g1, g2], w + (gs ++ [g1]).length, by simpa [List.append_assoc] using hwf2,
    by simp [isMult, g1, g2], by simp, fun x => ?_⟩
  rw [show gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] by simp]
  rw [evalW_append_new]
  simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not]
  change evalW w (gs ++ [g1]) x mIdx + 1 = _
  rw [evalW_append_new]
  simp only [g1, List.map_cons, List.map_nil, b2f_mod2_two]
  change evalW w gs x i + evalW w gs x j + 1 + 1 = evalW w gs x i + evalW w gs x j
  rw [add_assoc, f_add_self, add_zero]

lemma exists_and_gate (w : ℕ) (gs : List Gate) (hwf : WF w gs) (i j : ℕ)
    (hi : i < w + gs.length) (hj : j < w + gs.length) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult + 1 ∧
      idx < w + (gs ++ gs').length ∧
      ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = evalW w gs x i * evalW w gs x j := by
  let g : Gate := ⟨.and, [i, j]⟩
  refine ⟨[g], w + gs.length,
    wf_append_one w gs g hwf ⟨by simp [g], Or.inl rfl⟩
      (by intro a ha; simp [g] at ha; rcases ha with rfl | rfl <;> assumption),
    by simp [isMult, g], by simp, fun x => ?_⟩
  rw [evalW_append_new]
  simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    Bool.and_true, id_eq, b2f_and]
  rfl

lemma exists_xor_list (w : ℕ) (gs : List Gate) (hwf : WF w gs) (acc : ℕ)
    (hacc : acc < w + gs.length) (ws : List ℕ) (hws : ∀ i ∈ ws, i < w + gs.length) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult ∧
      idx < w + (gs ++ gs').length ∧
      ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = evalW w gs x acc + (ws.map (evalW w gs x)).sum := by
  induction ws generalizing gs acc with
  | nil => exact ⟨[], acc, by simpa using hwf, by simp, by simpa using hacc, fun x => by simp⟩
  | cons a rest ih =>
    obtain ⟨g1, idx1, hwf1, hc1, hi1, hv1⟩ :=
      exists_xor_gate w gs hwf acc a hacc (hws a (by simp))
    obtain ⟨g2, idx2, hwf2, hc2, hi2, hv2⟩ :=
      ih (gs ++ g1) hwf1 idx1 hi1 (fun i hi => by have := hws i (by simp [hi]); simp; omega)
    refine ⟨g1 ++ g2, idx2, by simpa [List.append_assoc] using hwf2,
      by rw [← List.append_assoc, hc2, hc1],
      by simpa [List.append_assoc] using hi2, fun x => ?_⟩
    rw [← List.append_assoc, hv2 x, hv1 x]
    have hmap : rest.map (evalW w (gs ++ g1) x) = rest.map (evalW w gs x) := by
      apply List.map_congr_left; intro i hi
      exact evalW_append_left w gs g1 x i (hws i (by simp [hi]))
    rw [hmap]; simp [add_assoc]

lemma exists_affine_gate (w : ℕ) (gs : List Gate) (hwf : WF w gs) (α : Fin w → F) (c : F) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult ∧
      idx < w + (gs ++ gs').length ∧
      ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = c + ∑ j : Fin w, α j * x j := by
  obtain ⟨g0, i0, hwf0, hc0, hi0, hv0⟩ := exists_const_gate w gs hwf c
  let ws : List ℕ := ((List.finRange w).filter (fun j => decide (α j = 1))).map Fin.val
  obtain ⟨g1, i1, hwf1, hc1, hi1, hv1⟩ :=
    exists_xor_list w (gs ++ g0) hwf0 i0 hi0 ws (fun i hi => by
      simp only [ws, List.mem_map] at hi; obtain ⟨j, _, rfl⟩ := hi; omega)
  refine ⟨g0 ++ g1, i1, by simpa [List.append_assoc] using hwf1,
    by rw [← List.append_assoc, hc1, hc0],
    by simpa [List.append_assoc] using hi1, fun x => ?_⟩
  rw [← List.append_assoc, hv1 x, hv0 x]
  congr 1
  simp only [ws, List.map_map]
  have hcongr : List.map (evalW w (gs ++ g0) x ∘ Fin.val)
      ((List.finRange w).filter (fun j => decide (α j = 1))) =
      List.map (fun j : Fin w => x j)
      ((List.finRange w).filter (fun j => decide (α j = 1))) := by
    apply List.map_congr_left; intro j _
    exact evalW_input w (gs ++ g0) x j
  rw [hcongr]
  have hsum : (List.map (fun j : Fin w => x j)
      ((List.finRange w).filter (fun j => decide (α j = 1)))).sum =
      ∑ j ∈ Finset.univ.filter (fun j : Fin w => α j = 1), x j := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange w).filter _)]
    congr 1; ext j; simp
  rw [hsum, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _
  rcases f_cases (α j) with h | h <;> simp [h]

lemma exists_prod_list (w : ℕ) (gs : List Gate) (hwf : WF w gs) (acc : ℕ)
    (hacc : acc < w + gs.length)
    (terms : List ((Fin w → F) × F × (Fin w → F) × F)) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult + terms.length ∧
      idx < w + (gs ++ gs').length ∧
      ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = evalW w gs x acc +
        (terms.map (fun t => (t.2.1 + ∑ j, t.1 j * x j) * (t.2.2.2 + ∑ j, t.2.2.1 j * x j))).sum := by
  induction terms generalizing gs acc with
  | nil => exact ⟨[], acc, by simpa using hwf, by simp, by simpa using hacc, fun x => by simp⟩
  | cons t rest ih =>
    obtain ⟨g1, i1, hwf1, hc1, hi1, hv1⟩ := exists_affine_gate w gs hwf t.1 t.2.1
    obtain ⟨g2, i2, hwf2, hc2, hi2, hv2⟩ := exists_affine_gate w (gs ++ g1) hwf1 t.2.2.1 t.2.2.2
    obtain ⟨g3, i3, hwf3, hc3, hi3, hv3⟩ :=
      exists_and_gate w ((gs ++ g1) ++ g2) hwf2 i1 i2 (by simp at hi1 ⊢; omega) hi2
    obtain ⟨g4, i4, hwf4, hc4, hi4, hv4⟩ :=
      exists_xor_gate w (((gs ++ g1) ++ g2) ++ g3) hwf3 acc i3 (by simp; omega) hi3
    obtain ⟨g5, i5, hwf5, hc5, hi5, hv5⟩ := ih _ hwf4 i4 hi4
    refine ⟨g1 ++ g2 ++ g3 ++ g4 ++ g5, i5,
      by simpa [List.append_assoc] using hwf5,
      by
        have hEq : gs ++ (g1 ++ g2 ++ g3 ++ g4 ++ g5) = ((((gs ++ g1) ++ g2) ++ g3) ++ g4) ++ g5 := by
          simp [List.append_assoc]
        rw [hEq, hc5, hc4, hc3, hc2, hc1]; simp; omega,
      by simpa [List.append_assoc] using hi5, fun x => ?_⟩
    have hEq : gs ++ (g1 ++ g2 ++ g3 ++ g4 ++ g5) = ((((gs ++ g1) ++ g2) ++ g3) ++ g4) ++ g5 := by
      simp [List.append_assoc]
    rw [hEq, hv5 x, hv4 x, hv3 x,
        evalW_append_left w ((gs ++ g1) ++ g2) g3 x acc (by simp; omega),
        evalW_append_left w (gs ++ g1) g2 x acc (by simp; omega),
        evalW_append_left w gs g1 x acc hacc,
        evalW_append_left w (gs ++ g1) g2 x i1 hi1, hv1 x, hv2 x]
    simp [add_assoc]

lemma exists_cubic_list (w : ℕ) (gs : List Gate) (hwf : WF w gs) (acc : ℕ)
    (hacc : acc < w + gs.length)
    (terms : List ((Fin w → F) × (Fin w → F) × (Fin w → F) × (Fin w → F) × (Fin w → F))) :
    ∃ gs' idx, WF w (gs ++ gs') ∧ (gs ++ gs').countP isMult = gs.countP isMult + 3 * terms.length ∧
      idx < w + (gs ++ gs').length ∧
      ∀ x : Fin w → F, evalW w (gs ++ gs') x idx = evalW w gs x acc +
        (terms.map (fun t =>
          (∑ j, t.2.1 j * x j) * (∑ j, t.2.2.1 j * x j) +
          (∑ j, t.2.2.2.1 j * x j) * (∑ j, t.2.2.2.2 j * x j) +
          (∑ j, t.1 j * x j) * (∑ j, t.2.2.1 j * x j) * (∑ j, t.2.2.2.2 j * x j))).sum := by
  induction terms generalizing gs acc with
  | nil => exact ⟨[], acc, by simpa using hwf, by simp, by simpa using hacc, fun x => by simp⟩
  | cons t rest ih =>
    obtain ⟨g1, iW, hwf1, hc1, hi1, hv1⟩ := exists_affine_gate w gs hwf t.1 0
    obtain ⟨g2, iBH, hwf2, hc2, hi2, hv2⟩ := exists_affine_gate w (gs ++ g1) hwf1 t.2.1 0
    obtain ⟨g3, iB, hwf3, hc3, hi3, hv3⟩ := exists_affine_gate w ((gs ++ g1) ++ g2) hwf2 t.2.2.1 0
    obtain ⟨g4, iCH, hwf4, hc4, hi4, hv4⟩ := exists_affine_gate w (((gs ++ g1) ++ g2) ++ g3) hwf3 t.2.2.2.1 0
    obtain ⟨g5, iC, hwf5, hc5, hi5, hv5⟩ := exists_affine_gate w ((((gs ++ g1) ++ g2) ++ g3) ++ g4) hwf4 t.2.2.2.2 0
    set gs5 := ((((gs ++ g1) ++ g2) ++ g3) ++ g4) ++ g5
    have hiW5 : iW < w + gs5.length := by simp [gs5] at hi1 ⊢; omega
    have hiBH5 : iBH < w + gs5.length := by simp [gs5] at hi2 ⊢; omega
    have hiB5 : iB < w + gs5.length := by simp [gs5] at hi3 ⊢; omega
    have hiCH5 : iCH < w + gs5.length := by simp [gs5] at hi4 ⊢; omega
    obtain ⟨g6, iP1, hwf6, hc6, hi6, hv6⟩ := exists_and_gate w gs5 hwf5 iW iB hiW5 hiB5
    obtain ⟨g7, iX1, hwf7, hc7, hi7, hv7⟩ := exists_xor_gate w (gs5 ++ g6) hwf6 iCH iP1 (by simp; omega) hi6
    obtain ⟨g8, iP2, hwf8, hc8, hi8, hv8⟩ := exists_and_gate w ((gs5 ++ g6) ++ g7) hwf7 iX1 iC hi7 (by simp; omega)
    obtain ⟨g9, iP3, hwf9, hc9, hi9, hv9⟩ := exists_and_gate w (((gs5 ++ g6) ++ g7) ++ g8) hwf8 iBH iB (by simp; omega) (by simp; omega)
    obtain ⟨g10, iA1, hwf10, hc10, hi10, hv10⟩ := exists_xor_gate w ((((gs5 ++ g6) ++ g7) ++ g8) ++ g9) hwf9 acc iP3 (by simp [gs5]; omega) hi9
    obtain ⟨g11, iA2, hwf11, hc11, hi11, hv11⟩ := exists_xor_gate w (((((gs5 ++ g6) ++ g7) ++ g8) ++ g9) ++ g10) hwf10 iA1 iP2 hi10 (by simp at hi8 ⊢; omega)
    obtain ⟨g12, iFin, hwf12, hc12, hi12, hv12⟩ := ih _ hwf11 iA2 hi11
    refine ⟨g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9 ++ g10 ++ g11 ++ g12, iFin,
      by simpa [gs5, List.append_assoc] using hwf12,
      by
        have hEq : gs ++ (g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9 ++ g10 ++ g11 ++ g12) =
            ((((((gs5 ++ g6) ++ g7) ++ g8) ++ g9) ++ g10) ++ g11) ++ g12 := by
          simp [gs5, List.append_assoc]
        rw [hEq, hc12, hc11, hc10, hc9, hc8, hc7, hc6, hc5, hc4, hc3, hc2, hc1]
        simp only [List.length_cons]; omega,
      by simpa [gs5, List.append_assoc] using hi12, fun x => ?_⟩
    have hEq : gs ++ (g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9 ++ g10 ++ g11 ++ g12) =
        ((((((gs5 ++ g6) ++ g7) ++ g8) ++ g9) ++ g10) ++ g11) ++ g12 := by
      simp [gs5, List.append_assoc]
    have evAcc : evalW w ((((gs5 ++ g6) ++ g7) ++ g8) ++ g9) x acc = evalW w gs x acc := by
      have : ((((gs5 ++ g6) ++ g7) ++ g8) ++ g9) = gs ++ (g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8 ++ g9) := by
        simp [gs5, List.append_assoc]
      rw [this, evalW_append_left w gs _ x acc hacc]
    have evW : evalW w gs5 x iW = ∑ j, t.1 j * x j := by
      have : gs5 = (gs ++ g1) ++ (g2 ++ g3 ++ g4 ++ g5) := by simp [gs5, List.append_assoc]
      rw [this, evalW_append_left w (gs ++ g1) _ x iW hi1, hv1 x, zero_add]
    have evBH : evalW w gs5 x iBH = ∑ j, t.2.1 j * x j := by
      have : gs5 = ((gs ++ g1) ++ g2) ++ (g3 ++ g4 ++ g5) := by simp [gs5, List.append_assoc]
      rw [this, evalW_append_left w ((gs ++ g1) ++ g2) _ x iBH hi2, hv2 x, zero_add]
    have evB : evalW w gs5 x iB = ∑ j, t.2.2.1 j * x j := by
      have : gs5 = (((gs ++ g1) ++ g2) ++ g3) ++ (g4 ++ g5) := by simp [gs5, List.append_assoc]
      rw [this, evalW_append_left w (((gs ++ g1) ++ g2) ++ g3) _ x iB hi3, hv3 x, zero_add]
    have evCH : evalW w gs5 x iCH = ∑ j, t.2.2.2.1 j * x j := by
      have : gs5 = ((((gs ++ g1) ++ g2) ++ g3) ++ g4) ++ g5 := by simp [gs5, List.append_assoc]
      rw [this, evalW_append_left w ((((gs ++ g1) ++ g2) ++ g3) ++ g4) _ x iCH hi4, hv4 x, zero_add]
    have evC : evalW w gs5 x iC = ∑ j, t.2.2.2.2 j * x j := by rw [hv5 x, zero_add]
    rw [hEq, hv12 x, hv11 x, hv10 x, evAcc]
    rw [evalW_append_left w (((((gs5 ++ g6) ++ g7) ++ g8) ++ g9)) g10 x iP2 (by simp at hi8 ⊢; omega),
        evalW_append_left w ((((gs5 ++ g6) ++ g7) ++ g8)) g9 x iP2 hi8, hv8 x, hv9 x]
    have hBH8 : evalW w (((gs5 ++ g6) ++ g7) ++ g8) x iBH = evalW w gs5 x iBH := by
      rw [show (((gs5 ++ g6) ++ g7) ++ g8) = gs5 ++ (g6 ++ g7 ++ g8) by simp [List.append_assoc]]
      exact evalW_append_left w gs5 _ x iBH hiBH5
    have hB8 : evalW w (((gs5 ++ g6) ++ g7) ++ g8) x iB = evalW w gs5 x iB := by
      rw [show (((gs5 ++ g6) ++ g7) ++ g8) = gs5 ++ (g6 ++ g7 ++ g8) by simp [List.append_assoc]]
      exact evalW_append_left w gs5 _ x iB hiB5
    have hC7 : evalW w ((gs5 ++ g6) ++ g7) x iC = evalW w gs5 x iC := by
      rw [show ((gs5 ++ g6) ++ g7) = gs5 ++ (g6 ++ g7) by simp [List.append_assoc]]
      exact evalW_append_left w gs5 _ x iC hi5
    rw [hBH8, hB8, hC7, hv7 x, evalW_append_left w gs5 g6 x iCH hiCH5, hv6 x,
        evW, evBH, evB, evCH, evC]
    simp only [List.map_cons, List.sum_cons]
    ring

def concatVec (n : ℕ) (x y : Fin n → F) : Fin (2 * n) → F :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else y ⟨i.val - n, by omega⟩

lemma bitsOf_concat (n : ℕ) (x y : Fin n → F) :
    bitsOf (2 * n) (concatVec n x y) = bitsOf n x ++ bitsOf n y := by
  apply List.ext_getElem
  · simp [bitsOf, Nat.two_mul]
  · intro i h1 h2
    simp only [bitsOf, concatVec, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with h <;> rfl

def pairCoeff (n : ℕ) (α β : Fin n → F) : Fin (2 * n) → F :=
  fun i => if h : i.val < n then α ⟨i.val, h⟩ else β ⟨i.val - n, by omega⟩

lemma sum_pairCoeff (n : ℕ) (α β x y : Fin n → F) :
    ∑ i : Fin (2 * n), pairCoeff n α β i * concatVec n x y i =
      dotProduct α x + dotProduct β y := by
  let e : Fin (n + n) ≃ Fin (2 * n) := finCongr (by omega)
  rw [← Equiv.sum_comp e]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    simp [e, pairCoeff, concatVec, i.isLt]
  · apply Finset.sum_congr rfl; intro i _
    have h1 : ¬ (n + i.val < n) := by omega
    simp [e, pairCoeff, concatVec, h1]

abbrev V (k m r : ℕ) := Fin (k + 2 * m + r) → F
abbrev S (k : ℕ) := Fin k → F
abbrev D (m : ℕ) := Fin m → F
abbrev Z (r : ℕ) := Fin r → F
abbrev Wfull (m r : ℕ) := D m × (D m × Z r)

def linCoeff {p : ℕ} (L : (Fin p → F) →ₗ[F] F) : Fin p → F := fun j => L (Pi.single j 1)

lemma linCoeff_dot {p : ℕ} (L : (Fin p → F) →ₗ[F] F) (u : Fin p → F) :
    dotProduct (linCoeff L) u = L u := by
  have hu : u = ∑ j : Fin p, u j • Pi.single j (1 : F) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hu]
  simp only [map_sum, map_smul, smul_eq_mul, linCoeff, dotProduct]
  apply Finset.sum_congr rfl; intro j _; ring

def xS {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) : S k :=
  fun i => dotProduct x (e.symm (Pi.single i 1, (0, (0, 0))))
def xB {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) : D m :=
  fun i => dotProduct x (e.symm (0, (Pi.single i 1, (0, 0))))
def xC {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) : D m :=
  fun i => dotProduct x (e.symm (0, (0, (Pi.single i 1, 0))))
def xZ {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) : Z r :=
  fun i => dotProduct x (e.symm (0, (0, (0, Pi.single i 1))))

lemma dotProduct_e_symm {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r)
    (x : V k m r) (s : S k) (b c : D m) (z : Z r) :
    dotProduct x (e.symm (s, (b, (c, z)))) =
      dotProduct (xS e x) s + dotProduct (xB e x) b +
      dotProduct (xC e x) c + dotProduct (xZ e x) z := by
  have hdecomp : (s, (b, (c, z))) =
      (∑ i : Fin k, s i • (Pi.single i (1 : F), ((0 : D m), ((0 : D m), (0 : Z r))))) +
      (∑ i : Fin m, b i • ((0 : S k), (Pi.single i (1 : F), ((0 : D m), (0 : Z r))))) +
      (∑ i : Fin m, c i • ((0 : S k), ((0 : D m), (Pi.single i (1 : F), (0 : Z r))))) +
      (∑ i : Fin r, z i • ((0 : S k), ((0 : D m), ((0 : D m), Pi.single i (1 : F))))) := by
    apply Prod.ext
    · ext i; simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · apply Prod.ext
      · ext i; simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · apply Prod.ext
        · ext i; simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · ext i; simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hdecomp]
  simp only [map_add, map_sum, map_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  change (∑ i, s i * xS e x i) + (∑ i, b i * xB e x i) +
      (∑ i, c i * xC e x i) + (∑ i, z i * xZ e x i) =
    (∑ i, xS e x i * s i) + (∑ i, xB e x i * b i) +
      (∑ i, xC e x i * c i) + (∑ i, xZ e x i * z i)
  congr 1
  · congr 1
    · congr 1
      · apply Finset.sum_congr rfl; intro i _; ring
      · apply Finset.sum_congr rfl; intro i _; ring
    · apply Finset.sum_congr rfl; intro i _; ring
  · apply Finset.sum_congr rfl; intro i _; ring

def dualShift {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (l : S k) : V k m r :=
  fun j => dotProduct l (e (Pi.single j 1)).1

lemma dotProduct_dualShift {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r)
    (l : S k) (y : V k m r) :
    dotProduct (dualShift e l) y = dotProduct l (e y).1 := by
  have hy : y = ∑ j : Fin (k + 2 * m + r), y j • Pi.single j (1 : F) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hy]
  simp only [map_sum, map_smul, Prod.fst_sum, Prod.smul_fst, dualShift, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

lemma xS_add_dualShift {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) (l : S k) :
    xS e (x + dualShift e l) = xS e x + l := by
  ext i
  simp only [xS, Pi.add_apply, add_dotProduct, dotProduct_dualShift, LinearEquiv.apply_symm_apply]
  simp [dotProduct, Pi.single_apply]

lemma xB_add_dualShift {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) (l : S k) :
    xB e (x + dualShift e l) = xB e x := by
  ext i; simp [xB, add_dotProduct, dotProduct_dualShift]

lemma xC_add_dualShift {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) (l : S k) :
    xC e (x + dualShift e l) = xC e x := by
  ext i; simp [xC, add_dotProduct, dotProduct_dualShift]

lemma xZ_add_dualShift {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (x : V k m r) (l : S k) :
    xZ e (x + dualShift e l) = xZ e x := by
  ext i; simp [xZ, add_dotProduct, dotProduct_dualShift]

def yS {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) : V k m r →ₗ[F] S k :=
  (LinearMap.fst F (S k) (Wfull m r)).comp e.toLinearMap
def yB {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) : V k m r →ₗ[F] D m :=
  (LinearMap.fst F (D m) (D m × Z r)).comp ((LinearMap.snd F (S k) (Wfull m r)).comp e.toLinearMap)
def yC {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) : V k m r →ₗ[F] D m :=
  (LinearMap.fst F (D m) (Z r)).comp
    ((LinearMap.snd F (D m) (D m × Z r)).comp ((LinearMap.snd F (S k) (Wfull m r)).comp e.toLinearMap))
def yZ {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) : V k m r →ₗ[F] Z r :=
  (LinearMap.snd F (D m) (Z r)).comp
    ((LinearMap.snd F (D m) (D m × Z r)).comp ((LinearMap.snd F (S k) (Wfull m r)).comp e.toLinearMap))

def xSLin {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (v : S k) : V k m r →ₗ[F] F where
  toFun x := dotProduct (xS e x) v
  map_add' x1 x2 := by
    have h : xS e (x1 + x2) = xS e x1 + xS e x2 := by ext i; simp [xS, add_dotProduct]
    rw [h, add_dotProduct]
  map_smul' c x := by
    have h : xS e (c • x) = c • xS e x := by ext i; simp [xS, smul_dotProduct]
    rw [h, smul_dotProduct, RingHom.id_apply]

def xBLin {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (i : Fin m) : V k m r →ₗ[F] F where
  toFun x := xB e x i
  map_add' x1 x2 := by simp [xB, add_dotProduct]
  map_smul' c x := by simp [xB, smul_dotProduct]

def xCLin {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (i : Fin m) : V k m r →ₗ[F] F where
  toFun x := xC e x i
  map_add' x1 x2 := by simp [xC, add_dotProduct]
  map_smul' c x := by simp [xC, smul_dotProduct]

def xZLin {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (j : Fin r) : V k m r →ₗ[F] F where
  toFun x := xZ e x j
  map_add' x1 x2 := by simp [xZ, add_dotProduct]
  map_smul' c x := by simp [xZ, smul_dotProduct]

lemma xSLin_apply {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (v : S k) (x : V k m r) :
    xSLin e v x = dotProduct (xS e x) v := rfl
lemma xBLin_apply {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (i : Fin m) (x : V k m r) :
    xBLin e i x = xB e x i := rfl
lemma xCLin_apply {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (i : Fin m) (x : V k m r) :
    xCLin e i x = xC e x i := rfl
lemma xZLin_apply {k m r : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r) (j : Fin r) (x : V k m r) :
    xZLin e j x = xZ e x j := rfl

lemma exists_quad_circuit {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r) (A : Fin m → S k)
    (o : F) (l : S k) (M : Fin k → Fin k → F)
    (E' : Finset (S k)) (a' : S k)
    (override : Option (Fin m × F)) :
    let W' := Submodule.span F (Set.image (fun s : S k => s - a') (↑E' : Set (S k)))
    let d' := Module.finrank F W'
    let varSet := (Finset.univ : Finset (Fin m)).filter (fun i =>
      ∃ s ∈ E', dotProduct (A i) s ≠ dotProduct (A i) a')
    let varActive := match override with
      | none => varSet
      | some (i0, _) => varSet.erase i0
    ∃ (C : Circuit) (vW : Fin d' → S k) (coordW : S k →ₗ[F] (Fin d' → F)),
      (∀ t, vW t ∈ W') ∧
      (∀ s ∈ E', s = a' + ∑ t : Fin d', coordW (s - a') t • vW t) ∧
      ReadsBack (2 * (k + 2 * m + r)) C ∧
      (∀ h ∈ C.gates, gateLegal h) ∧
      circuitCost C = (2 * m + r) + d' + varActive.card ∧
      (∀ x s b c z,
        let y := e.symm (s, (b, (c, z)))
        b2f (C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y)) =
          let lam := fun t : Fin d' => coordW (s - a') t
          let c0 := o + dotProduct l a' + ∑ i, ∑ j, M i j * a' i * a' j
          let c1 := fun t : Fin d' => dotProduct l (vW t) +
            ∑ i, ∑ j, M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)
          let c2 := fun t u : Fin d' =>
            ∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)
          dotProduct (xS e x) a' + c0 +
          (∑ t : Fin d', lam t * (dotProduct (xS e x) (vW t) + c1 t +
            ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lam u)) +
          dotProduct (xZ e x) z +
          ∑ i : Fin m, (xB e x i * b i + xC e x i * c i +
            (match override with
             | some (i0, β) => if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a'
             | none => if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a') * b i * c i)) := by
  classical
  intro W' d' varSet varActive
  set n := k + 2 * m + r
  let bW := Module.finBasis F W'
  let vW : Fin d' → S k := fun t => (bW t).1
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl W'
  let coordW : S k →ₗ[F] (Fin d' → F) := bW.equivFun.toLinearMap.comp (Submodule.projectionOnto W' K hK)
  have hvW_mem : ∀ t, vW t ∈ W' := fun t => (bW t).2
  have hrecon : ∀ s ∈ E', s = a' + ∑ t : Fin d', coordW (s - a') t • vW t := by
    intro s hs
    have hmem : s - a' ∈ W' := Submodule.subset_span ⟨s, hs, rfl⟩
    have hproj : Submodule.projectionOnto W' K hK (s - a') = ⟨s - a', hmem⟩ :=
      Submodule.projectionOnto_apply_left hK ⟨s - a', hmem⟩
    have hsum : ∑ t : Fin d', coordW (s - a') t • vW t = s - a' := by
      have h1 : ∑ t : Fin d', bW.equivFun ⟨s - a', hmem⟩ t • bW t = ⟨s - a', hmem⟩ :=
        bW.sum_equivFun ⟨s - a', hmem⟩
      have h2 : (↑(∑ t : Fin d', bW.equivFun ⟨s - a', hmem⟩ t • bW t) : S k) = s - a' :=
        congrArg Subtype.val h1
      rw [Submodule.coe_sum] at h2
      convert h2 using 1
      apply Finset.sum_congr rfl; intro t _
      simp only [coordW, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hproj, vW]
      rfl
    rw [hsum]; abel
  let c0 : F := o + dotProduct l a' + ∑ i, ∑ j, M i j * a' i * a' j
  let c1 : Fin d' → F := fun t => dotProduct l (vW t) +
    ∑ i, ∑ j, M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)
  let c2 : Fin d' → Fin d' → F := fun t u =>
    ∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)
  let lamLin : Fin d' → V k m r →ₗ[F] F := fun t => (LinearMap.proj t).comp (coordW.comp (yS e))
  let lamConst : Fin d' → F := fun t => coordW a' t
  let sTerms : List ((Fin (2 * n) → F) × F × (Fin (2 * n) → F) × F) :=
    (List.finRange d').map fun t =>
      let rhsY : V k m r →ₗ[F] F :=
        ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u • lamLin u
      let rhsC : F :=
        c1 t + ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamConst u
      (pairCoeff n 0 (linCoeff (lamLin t)), lamConst t,
       pairCoeff n (linCoeff (xSLin e (vW t))) (linCoeff rhsY), rhsC)
  let zTerms : List ((Fin (2 * n) → F) × F × (Fin (2 * n) → F) × F) :=
    (List.finRange r).map fun j =>
      (pairCoeff n (linCoeff (xZLin e j)) 0, 0,
       pairCoeff n 0 (linCoeff ((LinearMap.proj j).comp (yZ e))), 0)
  let nonVarList : List (Fin m) := (List.finRange m).filter (fun i => decide (i ∉ varActive))
  let varList : List (Fin m) := (List.finRange m).filter (fun i => decide (i ∈ varActive))
  let constBeta : Fin m → F := fun i =>
    match override with
    | some (i0, β) => if i = i0 then β else dotProduct (A i) a'
    | none => dotProduct (A i) a'
  let nonVarTerms : List ((Fin (2 * n) → F) × F × (Fin (2 * n) → F) × F) :=
    nonVarList.flatMap fun i =>
      [(pairCoeff n (linCoeff (xBLin e i)) (linCoeff (constBeta i • ((LinearMap.proj i).comp (yC e)))), 0,
        pairCoeff n 0 (linCoeff ((LinearMap.proj i).comp (yB e))), 0),
       (pairCoeff n (linCoeff (xCLin e i)) 0, 0,
        pairCoeff n 0 (linCoeff ((LinearMap.proj i).comp (yC e))), 0)]
  let allProdTerms := sTerms ++ zTerms ++ nonVarTerms
  let cubicTerms : List ((Fin (2 * n) → F) × (Fin (2 * n) → F) × (Fin (2 * n) → F) × (Fin (2 * n) → F) × (Fin (2 * n) → F)) :=
    varList.map fun i =>
      let wLin : V k m r →ₗ[F] F :=
        { toFun := fun y => dotProduct (A i) (yS e y)
          map_add' := fun y1 y2 => by simp [dotProduct_add]
          map_smul' := fun c y => by simp [dotProduct_smul] }
      (pairCoeff n 0 (linCoeff wLin),
       pairCoeff n (linCoeff (xBLin e i)) 0,
       pairCoeff n 0 (linCoeff ((LinearMap.proj i).comp (yB e))),
       pairCoeff n (linCoeff (xCLin e i)) 0,
       pairCoeff n 0 (linCoeff ((LinearMap.proj i).comp (yC e))))
  have hwf0 : WF (2 * n) [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  obtain ⟨g0, i0, hwf1, hc1, hi1, hv1⟩ :=
    exists_affine_gate (2 * n) [] hwf0 (pairCoeff n (linCoeff (xSLin e a')) 0) c0
  obtain ⟨g1, i1, hwf2, hc2, hi2, hv2⟩ :=
    exists_prod_list (2 * n) ([] ++ g0) hwf1 i0 hi1 allProdTerms
  obtain ⟨g2, i2, hwf3, hc3, hi3, hv3⟩ :=
    exists_cubic_list (2 * n) (([] ++ g0) ++ g1) hwf2 i1 hi2 cubicTerms
  refine ⟨⟨(([] ++ g0) ++ g1) ++ g2, i2⟩, vW, coordW, hvW_mem, hrecon, hwf3.1, hwf3.2, ?_, ?_⟩
  · have hnv : nonVarList.length = m - varActive.card := by
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
      have hset : nonVarList.toFinset = varActiveᶜ := by ext i; simp [nonVarList]
      rw [hset, Finset.card_compl, Fintype.card_fin]
    have hv : varList.length = varActive.card := by
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
      have hset : varList.toFinset = varActive := by ext i; simp [varList]
      rw [hset]
    have hcard_le : varActive.card ≤ m := by
      calc varActive.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
        _ = m := Fintype.card_fin m
    change ((([] ++ g0) ++ g1) ++ g2).countP isMult = 2 * m + r + d' + varActive.card
    rw [hc3, hc2, hc1]
    have hlen_nv : nonVarTerms.length = 2 * nonVarList.length := by
      simp [nonVarTerms, List.length_flatMap]; omega
    simp only [List.countP_nil, zero_add, allProdTerms, List.length_append, sTerms, zTerms,
      cubicTerms, List.length_map, List.length_finRange, hlen_nv, hnv, hv]
    omega
  · intro x s b c z
    set y := e.symm (s, (b, (c, z)))
    have hbits : bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y =
        bitsOf (2 * n) (concatVec n x y) := (bitsOf_concat n x y).symm
    change b2f ((Circuit.wires ⟨(([] ++ g0) ++ g1) ++ g2, i2⟩
      (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y)).getD i2 false) = _
    rw [hbits]
    change evalW (2 * n) ((([] ++ g0) ++ g1) ++ g2) (concatVec n x y) i2 = _
    rw [hv3, hv2, hv1]
    have hyS : yS e y = s := by simp [yS, y]
    have hyB : yB e y = b := by simp [yB, y]
    have hyC : yC e y = c := by simp [yC, y]
    have hyZ : yZ e y = z := by simp [yZ, y]
    have hlam : ∀ t : Fin d', lamConst t + lamLin t y = coordW (s - a') t := by
      intro t
      simp only [lamConst, lamLin, LinearMap.comp_apply, LinearMap.proj_apply, hyS, map_sub,
        Pi.sub_apply]
      rw [f_sub_eq_add, add_comm]
    have hbaseVal : c0 + ∑ j, pairCoeff n (linCoeff (xSLin e a')) 0 j * concatVec n x y j =
        dotProduct (xS e x) a' + c0 := by
      rw [sum_pairCoeff, linCoeff_dot, zero_dotProduct, add_zero, add_comm]; rfl
    have hsSum : (sTerms.map (fun t =>
        (t.2.1 + ∑ j, t.1 j * concatVec n x y j) *
        (t.2.2.2 + ∑ j, t.2.2.1 j * concatVec n x y j))).sum =
        ∑ t : Fin d', coordW (s - a') t * (dotProduct (xS e x) (vW t) + c1 t +
          ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * coordW (s - a') u) := by
      simp only [sTerms, List.map_map]
      rw [← List.sum_toFinset _ (List.nodup_finRange d'), List.toFinset_finRange]
      apply Finset.sum_congr rfl; intro t _
      simp only [Function.comp_apply, sum_pairCoeff, zero_dotProduct, zero_add, linCoeff_dot]
      rw [hlam t]
      congr 1
      simp only [xSLin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul]
      have hsumadd :
          (∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamConst u) +
          (∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamLin u y) =
          ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * coordW (s - a') u := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro u _
        rw [← mul_add, hlam u]
      calc c1 t + (∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamConst u) +
            (dotProduct (xS e x) (vW t) +
              ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamLin u y)
          = dotProduct (xS e x) (vW t) + c1 t +
            ((∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamConst u) +
             (∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lamLin u y)) := by ring
        _ = _ := by rw [hsumadd]
    have hzSum : (zTerms.map (fun t =>
        (t.2.1 + ∑ j, t.1 j * concatVec n x y j) *
        (t.2.2.2 + ∑ j, t.2.2.1 j * concatVec n x y j))).sum =
        dotProduct (xZ e x) z := by
      simp only [zTerms, List.map_map]
      rw [← List.sum_toFinset _ (List.nodup_finRange r), List.toFinset_finRange, dotProduct]
      apply Finset.sum_congr rfl; intro j _
      simp only [Function.comp_apply, sum_pairCoeff, zero_dotProduct, zero_add, add_zero,
        linCoeff_dot, LinearMap.comp_apply, LinearMap.proj_apply, hyZ]
      rfl
    have hnvSum : (nonVarTerms.map (fun t =>
        (t.2.1 + ∑ j, t.1 j * concatVec n x y j) *
        (t.2.2.2 + ∑ j, t.2.2.1 j * concatVec n x y j))).sum =
        ∑ i ∈ varActiveᶜ, (xB e x i * b i + xC e x i * c i + constBeta i * b i * c i) := by
      have h1 : (nonVarTerms.map (fun t =>
          (t.2.1 + ∑ j, t.1 j * concatVec n x y j) *
          (t.2.2.2 + ∑ j, t.2.2.1 j * concatVec n x y j))).sum =
          (nonVarList.map (fun i =>
            xB e x i * b i + xC e x i * c i + constBeta i * b i * c i)).sum := by
        simp only [nonVarTerms, list_sum_flatMap]
        congr 1; apply List.map_congr_left; intro i _
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          sum_pairCoeff, zero_dotProduct, zero_add, add_zero, linCoeff_dot,
          LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, hyB, hyC]
        rw [xBLin_apply, xCLin_apply]
        ring
      rw [h1, ← List.sum_toFinset _ ((List.nodup_finRange m).filter _)]
      congr 1; ext i; simp [nonVarList]
    have hvSum : (cubicTerms.map (fun t =>
        (∑ j, t.2.1 j * concatVec n x y j) * (∑ j, t.2.2.1 j * concatVec n x y j) +
        (∑ j, t.2.2.2.1 j * concatVec n x y j) * (∑ j, t.2.2.2.2 j * concatVec n x y j) +
        (∑ j, t.1 j * concatVec n x y j) * (∑ j, t.2.2.1 j * concatVec n x y j) *
          (∑ j, t.2.2.2.2 j * concatVec n x y j))).sum =
        ∑ i ∈ varActive, (xB e x i * b i + xC e x i * c i + dotProduct (A i) s * b i * c i) := by
      simp only [cubicTerms, List.map_map]
      rw [← List.sum_toFinset _ ((List.nodup_finRange m).filter _)]
      have hset : varList.toFinset = varActive := by ext i; simp [varList]
      rw [hset]
      apply Finset.sum_congr rfl; intro i _
      simp only [Function.comp_apply, sum_pairCoeff, zero_dotProduct, zero_add, add_zero,
        linCoeff_dot, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.comp_apply, LinearMap.proj_apply, hyS, hyB, hyC]
      rfl
    have hmSum :
        (∑ i ∈ varActiveᶜ, (xB e x i * b i + xC e x i * c i + constBeta i * b i * c i)) +
        (∑ i ∈ varActive, (xB e x i * b i + xC e x i * c i + dotProduct (A i) s * b i * c i)) =
        ∑ i : Fin m, (xB e x i * b i + xC e x i * c i +
          (match override with
           | some (i0, β) => if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a'
           | none => if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a') * b i * c i) := by
      conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ varActive), add_comm]
      have hf1 : Finset.univ.filter (fun i => i ∈ varActive) = varActive := by ext i; simp
      have hf2 : Finset.univ.filter (fun i => ¬ i ∈ varActive) = varActiveᶜ := by ext i; simp
      rw [hf1, hf2]
      congr 1
      · apply Finset.sum_congr rfl; intro i hi
        have hnot : i ∉ varActive := Finset.mem_compl.mp hi
        cases override with
        | none => simp [constBeta, show i ∉ varSet from hnot]
        | some p =>
          rcases p with ⟨i0, β⟩
          by_cases hEq : i = i0
          · simp [constBeta, hEq]
          · have hns : i ∉ varSet := fun hm => hnot (Finset.mem_erase.mpr ⟨hEq, hm⟩)
            simp [constBeta, hEq, hns]
      · apply Finset.sum_congr rfl; intro i hi
        cases override with
        | none => simp [show i ∈ varSet from hi]
        | some p =>
          rcases p with ⟨i0, β⟩
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          have hmem : i ∈ varSet := (Finset.mem_erase.mp hi).2
          simp [hne, hmem]
    simp only [allProdTerms, List.map_append, List.sum_append]
    rw [hbaseVal, hsSum, hzSum, hnvSum, hvSum]
    calc dotProduct (xS e x) a' + c0 +
          ((∑ t : Fin d', coordW (s - a') t * (dotProduct (xS e x) (vW t) + c1 t +
              ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * coordW (s - a') u)) +
            dotProduct (xZ e x) z +
            ∑ i ∈ varActiveᶜ, (xB e x i * b i + xC e x i * c i + constBeta i * b i * c i)) +
          ∑ i ∈ varActive, (xB e x i * b i + xC e x i * c i + dotProduct (A i) s * b i * c i)
        = dotProduct (xS e x) a' + c0 +
          (∑ t : Fin d', coordW (s - a') t * (dotProduct (xS e x) (vW t) + c1 t +
              ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * coordW (s - a') u)) +
          dotProduct (xZ e x) z +
          ((∑ i ∈ varActiveᶜ, (xB e x i * b i + xC e x i * c i + constBeta i * b i * c i)) +
            ∑ i ∈ varActive, (xB e x i * b i + xC e x i * c i + dotProduct (A i) s * b i * c i)) := by ring
      _ = _ := by rw [hmSum]

lemma quad_expand {k d' : ℕ} (o : F) (l : S k) (M : Fin k → Fin k → F)
    (a' : S k) (vW : Fin d' → S k) (lam : Fin d' → F) :
    let s := a' + ∑ t : Fin d', lam t • vW t
    let c0 := o + dotProduct l a' + ∑ i, ∑ j, M i j * a' i * a' j
    let c1 := fun t : Fin d' => dotProduct l (vW t) +
      ∑ i, ∑ j, M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)
    let c2 := fun t u : Fin d' =>
      ∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)
    o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j =
      c0 + ∑ t : Fin d', lam t * (c1 t +
        ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u), c2 t u * lam u) := by
  intro s c0 c1 c2
  have hl : dotProduct l s = dotProduct l a' + ∑ t : Fin d', lam t * dotProduct l (vW t) := by
    simp only [s, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have hq_ij : ∀ i j : Fin k, M i j * s i * s j =
      M i j * a' i * a' j +
      (∑ t : Fin d', lam t * (M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j))) +
      ∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
        lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u) := by
    intro i j
    have hsi : s i = a' i + ∑ t : Fin d', lam t * vW t i := by simp [s, Finset.sum_apply]
    have hsj : s j = a' j + ∑ u : Fin d', lam u * vW u j := by simp [s, Finset.sum_apply]
    rw [hsi, hsj]
    have hexp : M i j * (a' i + ∑ t : Fin d', lam t * vW t i) * (a' j + ∑ u : Fin d', lam u * vW u j) =
        M i j * a' i * a' j +
        (∑ t : Fin d', M i j * a' i * (lam t * vW t j)) +
        (∑ t : Fin d', M i j * (lam t * vW t i) * a' j) +
        ∑ t : Fin d', ∑ u : Fin d', M i j * (lam t * vW t i) * (lam u * vW u j) := by
      have hL : M i j * (a' i + ∑ t : Fin d', lam t * vW t i) * (a' j + ∑ u : Fin d', lam u * vW u j) =
          M i j * a' i * a' j +
          (M i j * a' i) * (∑ u : Fin d', lam u * vW u j) +
          (∑ t : Fin d', lam t * vW t i) * (M i j * a' j) +
          M i j * ((∑ t : Fin d', lam t * vW t i) * (∑ u : Fin d', lam u * vW u j)) := by ring
      rw [hL]
      have h2 : M i j * a' i * (∑ u : Fin d', lam u * vW u j) =
          ∑ t : Fin d', M i j * a' i * (lam t * vW t j) := Finset.mul_sum _ _ _
      have h3 : (∑ t : Fin d', lam t * vW t i) * (M i j * a' j) =
          ∑ t : Fin d', M i j * (lam t * vW t i) * a' j := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _; ring
      have h4 : M i j * ((∑ t : Fin d', lam t * vW t i) * (∑ u : Fin d', lam u * vW u j)) =
          ∑ t : Fin d', ∑ u : Fin d', M i j * (lam t * vW t i) * (lam u * vW u j) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _; ring
      rw [h2, h3, h4]
    rw [hexp]
    have hsplit : ∀ t : Fin d',
        (∑ u : Fin d', M i j * (lam t * vW t i) * (lam u * vW u j)) =
        lam t * (M i j * (vW t i * vW t j)) +
        (∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
          M i j * (lam t * vW t i) * (lam u * vW u j)) +
        (∑ u ∈ Finset.univ.filter (fun u : Fin d' => u < t),
          M i j * (lam t * vW t i) * (lam u * vW u j)) := by
      intro t
      have hpart : (Finset.univ : Finset (Fin d')) =
          insert t ((Finset.univ.filter (fun u : Fin d' => t < u)) ∪
                    (Finset.univ.filter (fun u : Fin d' => u < t))) := by
        ext u; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
          true_and, true_iff]
        rcases lt_trichotomy u t with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have hd1 : t ∉ (Finset.univ.filter (fun u : Fin d' => t < u)) ∪
                     (Finset.univ.filter (fun u : Fin d' => u < t)) := by simp
      have hd2 : Disjoint (Finset.univ.filter (fun u : Fin d' => t < u))
                          (Finset.univ.filter (fun u : Fin d' => u < t)) := by
        rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_filter] at hu1 hu2; exact lt_asymm hu1.2 hu2.2
      conv_lhs => rw [hpart, Finset.sum_insert hd1, Finset.sum_union hd2]
      have hdiag : M i j * (lam t * vW t i) * (lam t * vW t j) =
          lam t * (M i j * (vW t i * vW t j)) := by
        calc M i j * (lam t * vW t i) * (lam t * vW t j)
            = (lam t * lam t) * (M i j * (vW t i * vW t j)) := by ring
          _ = lam t * (M i j * (vW t i * vW t j)) := by rw [f_sq]
      rw [hdiag]; ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hswap :
        (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => u < t),
          M i j * (lam t * vW t i) * (lam u * vW u j)) =
        (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
          M i j * (lam u * vW u i) * (lam t * vW t j)) := by
      simp only [Finset.sum_filter]; rw [Finset.sum_comm]
    rw [hswap]
    have hcomb :
        (∑ t : Fin d', M i j * a' i * (lam t * vW t j)) +
        (∑ t : Fin d', M i j * (lam t * vW t i) * a' j) +
        (∑ t : Fin d', lam t * (M i j * (vW t i * vW t j))) =
        ∑ t : Fin d', lam t * (M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _; ring
    have hcomb2 :
        (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
          M i j * (lam t * vW t i) * (lam u * vW u j)) +
        (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
          M i j * (lam u * vW u i) * (lam t * vW t j)) =
        ∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
          lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro u _; ring
    calc M i j * a' i * a' j +
          (∑ t : Fin d', M i j * a' i * (lam t * vW t j)) +
          (∑ t : Fin d', M i j * (lam t * vW t i) * a' j) +
          ((∑ t : Fin d', lam t * (M i j * (vW t i * vW t j))) +
            (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              M i j * (lam t * vW t i) * (lam u * vW u j)) +
            (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              M i j * (lam u * vW u i) * (lam t * vW t j)))
        = M i j * a' i * a' j +
          ((∑ t : Fin d', M i j * a' i * (lam t * vW t j)) +
            (∑ t : Fin d', M i j * (lam t * vW t i) * a' j) +
            (∑ t : Fin d', lam t * (M i j * (vW t i * vW t j)))) +
          ((∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              M i j * (lam t * vW t i) * (lam u * vW u j)) +
            (∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              M i j * (lam u * vW u i) * (lam t * vW t j))) := by ring
      _ = _ := by rw [hcomb, hcomb2]
  simp_rw [hq_ij, Finset.sum_add_distrib]
  rw [hl]
  have h1 : (∑ i : Fin k, ∑ j : Fin k, ∑ t : Fin d',
      lam t * (M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j))) =
      ∑ t : Fin d', lam t * ∑ i : Fin k, ∑ j : Fin k,
        M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j) := by
    calc (∑ i : Fin k, ∑ j : Fin k, ∑ t : Fin d',
            lam t * (M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)))
        = ∑ i : Fin k, ∑ t : Fin d', ∑ j : Fin k,
            lam t * (M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)) := by
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
      _ = ∑ t : Fin d', ∑ i : Fin k, ∑ j : Fin k,
            lam t * (M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro t _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  have h2 : (∑ i : Fin k, ∑ j : Fin k, ∑ t : Fin d',
      ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
        lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u)) =
      ∑ t : Fin d', lam t * ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
        c2 t u * lam u := by
    calc (∑ i : Fin k, ∑ j : Fin k, ∑ t : Fin d',
            ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u))
        = ∑ i : Fin k, ∑ t : Fin d', ∑ j : Fin k,
            ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u) := by
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
      _ = ∑ t : Fin d', ∑ i : Fin k, ∑ j : Fin k,
            ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
              lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u) := Finset.sum_comm
      _ = ∑ t : Fin d', ∑ i : Fin k, ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
            ∑ j : Fin k, lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u) := by
          apply Finset.sum_congr rfl; intro t _
          apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
      _ = ∑ t : Fin d', ∑ u ∈ Finset.univ.filter (fun u : Fin d' => t < u),
            ∑ i : Fin k, ∑ j : Fin k,
              lam t * (M i j * (vW t i * vW u j + vW u i * vW t j) * lam u) := by
          apply Finset.sum_congr rfl; intro t _; exact Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro t _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
          simp only [c2, Finset.sum_mul, Finset.mul_sum]
  rw [h1, h2]
  simp only [c0, c1, mul_add, Finset.sum_add_distrib]
  ring

lemma lp_duality {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E → ℝ) (hδ_nn : ∀ i s, 0 ≤ δ i s)
    (hδ_pos : ∀ i, ∃ s : E, 0 < δ i s)
    (w : E → ℝ) (hw : ∀ s, 0 < w s) :
    let cover := fun z : E → ℝ => (∀ s, 0 ≤ z s) ∧ (∀ i : Fin N, 1 ≤ ∑ s, δ i s * z s)
    let total := fun z : E → ℝ => ∑ s, w s * z s
    ∃ (z : E → ℝ) (lam : Fin N → ℝ),
      cover z ∧ 0 < total z ∧ (∀ y, cover y → total z ≤ total y) ∧
      (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = total z) ∧
      (∀ s, ∑ i, lam i * δ i s ≤ w s) := by
  intro cover total
  have hNE : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hM_exists : ∃ M : ℝ, 0 < M ∧ ∀ i : Fin N, 1 ≤ ∑ s : E, δ i s * M := by
    have hpos_sum : ∀ i : Fin N, 0 < ∑ s : E, δ i s := by
      intro i; obtain ⟨s0, hs0⟩ := hδ_pos i
      exact lt_of_lt_of_le hs0 (Finset.single_le_sum (fun s _ => hδ_nn i s) (Finset.mem_univ s0))
    let m0 : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin N => ∑ s : E, δ i s)
    have hm0 : 0 < m0 := by rw [Finset.lt_inf'_iff]; intro i _; exact hpos_sum i
    refine ⟨1 / m0, by positivity, fun i => ?_⟩
    rw [← Finset.sum_mul]
    have hle : m0 ≤ ∑ s : E, δ i s := Finset.inf'_le _ (Finset.mem_univ i)
    have h1 : 1 = m0 * (1 / m0) := by field_simp
    conv_lhs => rw [h1]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  obtain ⟨M, hMpos, hM⟩ := hM_exists
  let z0 : E → ℝ := fun _ => M
  have hz0 : cover z0 := ⟨fun _ => le_of_lt hMpos, hM⟩
  let K : Set (E → ℝ) := {z | cover z ∧ total z ≤ total z0}
  have hK_ne : K.Nonempty := ⟨z0, hz0, le_rfl⟩
  have hK_closed : IsClosed K := by
    have h1 : IsClosed {z : E → ℝ | ∀ s, 0 ≤ z s} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
    have h2 : IsClosed {z : E → ℝ | ∀ i : Fin N, 1 ≤ ∑ s, δ i s * z s} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    have h3 : IsClosed {z : E → ℝ | total z ≤ total z0} :=
      isClosed_le (by fun_prop) continuous_const
    exact (h1.inter h2).inter h3
  have hK_sub : K ⊆ Set.pi Set.univ (fun s : E => Set.Icc 0 (total z0 / w s)) := by
    intro z hz s _
    refine ⟨hz.1.1 s, ?_⟩
    have hterm : w s * z s ≤ total z :=
      Finset.single_le_sum (fun t _ => mul_nonneg (le_of_lt (hw t)) (hz.1.1 t)) (Finset.mem_univ s)
    exact (le_div_iff₀ (hw s)).mpr (by linarith [hz.2])
  have hK_compact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hK_closed hK_sub
  have hcont : Continuous total := by fun_prop
  obtain ⟨z, hzK, hz_min⟩ := hK_compact.exists_isMinOn hK_ne hcont.continuousOn
  have hz_cov : cover z := hzK.1
  have hz_opt : ∀ y, cover y → total z ≤ total y := by
    intro y hy
    by_cases hle : total y ≤ total z0
    · exact hz_min ⟨hy, hle⟩
    · exact le_trans hzK.2 (le_of_not_ge hle)
  have hz_pos : 0 < total z := by
    let i0 : Fin N := ⟨0, hN⟩
    have h1 : 1 ≤ ∑ s : E, δ i0 s * z s := hz_cov.2 i0
    have hne : ∃ s : E, 0 < z s := by
      by_contra h; push Not at h
      have hzero : ∑ s : E, δ i0 s * z s = 0 := by
        apply Finset.sum_eq_zero; intro s _
        have : z s = 0 := le_antisymm (h s) (hz_cov.1 s); simp [this]
      linarith
    obtain ⟨s0, hs0⟩ := hne
    exact lt_of_lt_of_le (mul_pos (hw s0) hs0)
      (Finset.single_le_sum (fun s _ => mul_nonneg (le_of_lt (hw s)) (hz_cov.1 s))
        (Finset.mem_univ s0))
  set T := total z
  let Δ : Set ((Fin N → ℝ) × (E → ℝ)) :=
    {p | (∀ i, 0 ≤ p.1 i) ∧ (∀ s, 0 ≤ p.2 s) ∧ (∑ i, p.1 i) + (∑ s, p.2 s) = 1}
  have hΔ_conv : Convex ℝ Δ := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => by simp only [Prod.smul_fst, Prod.fst_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)),
            fun s => by simp only [Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact add_nonneg (mul_nonneg ha (hx.2.1 s)) (mul_nonneg hb (hy.2.1 s)), ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    calc a * ∑ i, x.1 i + b * ∑ i, y.1 i + (a * ∑ s, x.2 s + b * ∑ s, y.2 s)
        = a * ((∑ i, x.1 i) + ∑ s, x.2 s) + b * ((∑ i, y.1 i) + ∑ s, y.2 s) := by ring
      _ = a * 1 + b * 1 := by rw [hx.2.2, hy.2.2]
      _ = 1 := by linarith
  have hΔ_closed : IsClosed Δ := by
    have h1 : IsClosed {p : (Fin N → ℝ) × (E → ℝ) | ∀ i, 0 ≤ p.1 i} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {p : (Fin N → ℝ) × (E → ℝ) | ∀ s, 0 ≤ p.2 s} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun s => isClosed_le continuous_const (by fun_prop)
    have h3 : IsClosed {p : (Fin N → ℝ) × (E → ℝ) | (∑ i, p.1 i) + (∑ s, p.2 s) = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  have hΔ_sub : Δ ⊆ (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1)) ×ˢ
                     (Set.pi Set.univ (fun _ : E => Set.Icc (0 : ℝ) 1)) := by
    intro p hp
    refine ⟨fun i _ => ⟨hp.1 i, ?_⟩, fun s _ => ⟨hp.2.1 s, ?_⟩⟩
    · have h1 : p.1 i ≤ ∑ j, p.1 j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ s, p.2 s := Finset.sum_nonneg fun s _ => hp.2.1 s
      linarith [hp.2.2]
    · have h1 : p.2 s ≤ ∑ t, p.2 t := Finset.single_le_sum (fun t _ => hp.2.1 t) (Finset.mem_univ s)
      have h2 : 0 ≤ ∑ i, p.1 i := Finset.sum_nonneg fun i _ => hp.1 i
      linarith [hp.2.2]
  have hΔ_compact : IsCompact Δ :=
    ((isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)).of_isClosed_subset hΔ_closed hΔ_sub
  let L : ((Fin N → ℝ) × (E → ℝ)) →ₗ[ℝ] (E → ℝ) :=
    { toFun := fun p s => (∑ i, p.1 i * δ i s) + p.2 s - ((∑ i, p.1 i) / T) * w s
      map_add' := fun p q => by
        ext s; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun c p => by
        ext s; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, ← Finset.mul_sum, mul_assoc]; ring }
  have hL_cont : Continuous L := by
    refine continuous_pi fun s => ?_
    change Continuous (fun p : (Fin N → ℝ) × (E → ℝ) =>
      (∑ i, p.1 i * δ i s) + p.2 s - ((∑ i, p.1 i) / T) * w s)
    fun_prop
  have h0_mem : (0 : E → ℝ) ∈ L '' Δ := by
    by_contra hnot
    have hcomp : IsCompact (L '' Δ) := hΔ_compact.image hL_cont
    have hconv : Convex ℝ (L '' Δ) := hΔ_conv.linear_image L
    obtain ⟨f, u, hfu, hfg⟩ := geometric_hahn_banach_point_closed hconv hcomp.isClosed hnot
    let y : E → ℝ := fun s => f (Pi.single s 1)
    have hf_eq : ∀ v : E → ℝ, f v = ∑ s : E, y s * v s := by
      intro v
      have hv : v = ∑ s : E, v s • Pi.single s (1 : ℝ) := by
        ext s; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul, smul_eq_mul, y]
      apply Finset.sum_congr rfl; intro s _; ring
    have hu_pos : 0 < u := by simpa [map_zero] using hfu
    have hy_pos : ∀ s : E, 0 < y s := by
      intro s
      have hp : ((0 : Fin N → ℝ), Pi.single s (1 : ℝ)) ∈ Δ := by
        refine ⟨fun _ => le_rfl, fun t => ?_, ?_⟩
        · by_cases h : t = s <;> simp [h]
        · simp
      have hLp : L (0, Pi.single s 1) = Pi.single s 1 := by ext t; simp [L]
      have hgt := hfg _ ⟨_, hp, hLp⟩
      linarith
    have hdot_w : 0 < ∑ s : E, w s * y s :=
      Finset.sum_pos (fun s _ => mul_pos (hw s) (hy_pos s)) Finset.univ_nonempty
    have hδ_gt : ∀ i : Fin N, (∑ s : E, w s * y s) / T < ∑ s : E, δ i s * y s := by
      intro i
      have hp : (Pi.single i (1 : ℝ), (0 : E → ℝ)) ∈ Δ := by
        refine ⟨fun j => ?_, fun _ => le_rfl, ?_⟩
        · by_cases h : j = i <;> simp [h]
        · simp
      have hgt := hfg _ ⟨_, hp, rfl⟩
      rw [hf_eq] at hgt
      have hcalc : (∑ s : E, y s * L (Pi.single i 1, 0) s) =
          (∑ s : E, δ i s * y s) - (∑ s : E, w s * y s) / T := by
        have h1 : ∀ s : E, L (Pi.single i 1, 0) s = δ i s - (1 / T) * w s := fun s => by
          simp [L, Pi.single_apply]
        simp_rw [h1, mul_sub, Finset.sum_sub_distrib]
        congr 1
        · apply Finset.sum_congr rfl; intro s _; ring
        · rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro s _; ring
      rw [hcalc] at hgt; linarith
    let m1 : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin N => ∑ s : E, δ i s * y s)
    have hm1_gt : (∑ s : E, w s * y s) / T < m1 := by
      rw [Finset.lt_inf'_iff]; intro i _; exact hδ_gt i
    have hm1_pos : 0 < m1 := lt_trans (div_pos hdot_w hz_pos) hm1_gt
    let y' : E → ℝ := fun s => y s / m1
    have hy'_cov : cover y' := by
      refine ⟨fun s => div_nonneg (le_of_lt (hy_pos s)) (le_of_lt hm1_pos), fun i => ?_⟩
      have hle : m1 ≤ ∑ s : E, δ i s * y s := Finset.inf'_le _ (Finset.mem_univ i)
      have hsum : (∑ s : E, δ i s * y' s) = (∑ s : E, δ i s * y s) / m1 := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro s _; simp [y']; ring
      rw [hsum, one_le_div hm1_pos]; exact hle
    have hy'_tot : total y' < T := by
      have hsum : total y' = (∑ s : E, w s * y s) / m1 := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro s _; simp [y']; ring
      rw [hsum, div_lt_iff₀ hm1_pos]
      have := (div_lt_iff₀ hz_pos).mp hm1_gt; linarith
    linarith [hz_opt y' hy'_cov]
  obtain ⟨⟨μ, ν⟩, hΔ, hL0⟩ := h0_mem
  have hσ_pos : 0 < ∑ i, μ i := by
    by_contra hle; push Not at hle
    have hμ0 : ∀ i, μ i = 0 := fun i =>
      le_antisymm (le_trans (Finset.single_le_sum (fun j _ => hΔ.1 j) (Finset.mem_univ i)) hle)
        (hΔ.1 i)
    have hν0 : ∀ s, ν s = 0 := fun s => by
      have hs := congrFun hL0 s
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hμ0, zero_mul,
        Finset.sum_const_zero, zero_add, zero_div, sub_zero] at hs
      exact hs
    have hsum0 : (∑ i, μ i) + (∑ s, ν s) = 0 := by simp [hμ0, hν0]
    linarith [hΔ.2.2]
  let lam : Fin N → ℝ := fun i => (T / ∑ j, μ j) * μ i
  refine ⟨z, lam, hz_cov, hz_pos, hz_opt,
    fun i => mul_nonneg (div_nonneg (le_of_lt hz_pos) (le_of_lt hσ_pos)) (hΔ.1 i), ?_, ?_⟩
  · simp only [lam, ← Finset.mul_sum]
    have hσne : ∑ j, μ j ≠ 0 := ne_of_gt hσ_pos
    field_simp; rfl
  · intro s
    have hs := congrFun hL0 s
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hs
    have h1 : (∑ i, μ i * δ i s) ≤ ((∑ i, μ i) / T) * w s := by have := hΔ.2.1 s; linarith
    have hscale : 0 ≤ T / ∑ j, μ j := div_nonneg (le_of_lt hz_pos) (le_of_lt hσ_pos)
    have h2 : (T / ∑ j, μ j) * (∑ i, μ i * δ i s) ≤ (T / ∑ j, μ j) * (((∑ i, μ i) / T) * w s) :=
      mul_le_mul_of_nonneg_left h1 hscale
    have hlhs : ∑ i, lam i * δ i s = (T / ∑ j, μ j) * (∑ i, μ i * δ i s) := by
      simp only [lam, Finset.mul_sum, mul_assoc]
    have hrhs : (T / ∑ j, μ j) * (((∑ i, μ i) / T) * w s) = w s := by
      have hσne : ∑ j, μ j ≠ 0 := ne_of_gt hσ_pos
      have hTne : T ≠ 0 := ne_of_gt hz_pos
      field_simp
    linarith

lemma exists_lin_one_of_notMem {E : Type*} [AddCommGroup E] [Module F E]
    (U : Submodule F E) (v : E) (hv : v ∉ U) :
    ∃ φ : E →ₗ[F] F, (∀ u ∈ U, φ u = 0) ∧ φ v = 1 := by
  classical
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl U
  let pK : E →ₗ[F] K := Submodule.projectionOnto K U hK.symm
  have hpKU : ∀ u ∈ U, pK u = 0 := fun u hu => Submodule.projectionOnto_apply_right hK.symm ⟨u, hu⟩
  have hpKv : pK v ≠ 0 := by
    intro h0
    have hvsup : v ∈ U ⊔ K := by rw [hK.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, k, hk, huk⟩ := Submodule.mem_sup.mp hvsup
    have hpk : pK v = ⟨k, hk⟩ := by
      rw [← huk, map_add, hpKU u hu, zero_add]
      exact Submodule.projectionOnto_apply_left hK.symm ⟨k, hk⟩
    have hk0 : k = 0 := congrArg Subtype.val (hpk.symm.trans h0)
    rw [hk0, add_zero] at huk
    exact hv (huk ▸ hu)
  let L : Submodule F K := Submodule.span F {pK v}
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl L
  let pL : K →ₗ[F] L := Submodule.projectionOnto L K' hK'
  have hpL_self : (pL (pK v) : K) = pK v :=
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hK'
      ⟨pK v, Submodule.subset_span (Set.mem_singleton _)⟩)
  let toF : L →ₗ[F] F :=
    { toFun := fun y => if y.1 = 0 then 0 else 1
      map_add' := fun y1 y2 => by
        obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp y1.2
        obtain ⟨c2, hc2⟩ := Submodule.mem_span_singleton.mp y2.2
        have h1 : y1.1 = c1 • pK v := hc1.symm
        have h2 : y2.1 = c2 • pK v := hc2.symm
        have h12 : (y1 + y2).1 = (c1 + c2) • pK v := by
          change y1.1 + y2.1 = _; rw [h1, h2, add_smul]
        rw [h1, h2, h12]
        rcases f_cases c1 with rfl | rfl <;> rcases f_cases c2 with rfl | rfl
        · simp
        · simp [hpKv]
        · simp [hpKv]
        · rw [f_add_self]; simp [hpKv, f_add_self]
      map_smul' := fun c y => by
        obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp y.2
        have h1 : y.1 = c1 • pK v := hc1.symm
        have h2 : (c • y).1 = (c * c1) • pK v := by
          change c • y.1 = _; rw [h1, smul_smul]
        simp only [RingHom.id_apply, smul_eq_mul, h2, h1]
        rcases f_cases c with rfl | rfl <;> rcases f_cases c1 with rfl | rfl
        · simp
        · simp [hpKv]
        · simp
        · simp [hpKv] }
  refine ⟨toF.comp (pL.comp pK), fun u hu => ?_, ?_⟩
  · simp [hpKU u hu]
  · simp only [LinearMap.comp_apply, toF, LinearMap.coe_mk, AddHom.coe_mk]
    have : (pL (pK v)).1 ≠ 0 := by rw [hpL_self]; exact hpKv
    simp [this]

lemma exists_dotProduct_one_of_notMem {n : ℕ}
    (U : Submodule F (Fin n → F)) (v : Fin n → F) (hv : v ∉ U) :
    ∃ w : Fin n → F, (∀ u ∈ U, dotProduct u w = 0) ∧ dotProduct v w = 1 := by
  obtain ⟨φ, hU, hv1⟩ := exists_lin_one_of_notMem U v hv
  refine ⟨linCoeff φ, fun u hu => ?_, ?_⟩
  · rw [dotProduct_comm, linCoeff_dot]; exact hU u hu
  · rw [dotProduct_comm, linCoeff_dot]; exact hv1

lemma sum_sign_of_shift {α : Type*} [DecidableEq α] [AddCommGroup α] [Module F α]
    (A : Finset α) (g : α → F) (v0 : α)
    (hmem : ∀ x ∈ A, x + v0 ∈ A) (hflip : ∀ x ∈ A, g (x + v0) = g x + 1) :
    ∑ x ∈ A, sign (g x) = 0 := by
  have h1 : ∑ x ∈ A, sign (g (x + v0)) = ∑ x ∈ A, sign (g x) := by
    apply Finset.sum_nbij (· + v0)
    · intro x hx; exact hmem x hx
    · intro x1 _ x2 _ heq; simpa using congrArg (· + v0) heq
    · intro y hy
      refine ⟨y + v0, hmem y hy, ?_⟩
      dsimp only; rw [add_assoc, vec_add_self, add_zero]
    · intro _ _; rfl
  have h2 : ∑ x ∈ A, sign (g (x + v0)) = - ∑ x ∈ A, sign (g x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro x hx
    rw [hflip x hx, sign_add, sign_one]; ring
  linarith

lemma sum_sign_four_point {α : Type*} [DecidableEq α] [AddCommGroup α] [Module F α]
    (A : Finset α) (g : α → F) (u v : α)
    (hu : ∀ x ∈ A, x + u ∈ A) (hv : ∀ x ∈ A, x + v ∈ A)
    (h4 : ∀ x ∈ A, g (x + u + v) + g (x + u) + g (x + v) + g x = 1) :
    ∑ x ∈ A, sign (g x) ≤ (A.card : ℝ) / 2 := by
  have hshift : ∀ w : α, (∀ x ∈ A, x + w ∈ A) →
      ∑ x ∈ A, sign (g (x + w)) = ∑ x ∈ A, sign (g x) := by
    intro w hw
    apply Finset.sum_nbij (· + w)
    · intro x hx; exact hw x hx
    · intro x1 _ x2 _ heq; simpa using congrArg (· + w) heq
    · intro y hy
      refine ⟨y + w, hw y hy, ?_⟩
      dsimp only; rw [add_assoc, vec_add_self, add_zero]
    · intro _ _; rfl
  have huv : ∀ x ∈ A, x + (u + v) ∈ A := fun x hx => by
    rw [← add_assoc]; exact hv _ (hu x hx)
  have hsum4 : 4 * ∑ x ∈ A, sign (g x) =
      ∑ x ∈ A, (sign (g (x + u + v)) + sign (g (x + u)) + sign (g (x + v)) + sign (g x)) := by
    simp only [Finset.sum_add_distrib]
    have h1 := hshift u hu
    have h2 := hshift v hv
    have h3 : ∑ x ∈ A, sign (g (x + u + v)) = ∑ x ∈ A, sign (g x) := by
      have := hshift (u + v) huv
      simpa only [add_assoc] using this
    linarith
  have hle : ∑ x ∈ A, (sign (g (x + u + v)) + sign (g (x + u)) + sign (g (x + v)) + sign (g x)) ≤
      ∑ _x ∈ A, (2 : ℝ) := by
    apply Finset.sum_le_sum; intro x hx
    calc sign (g (x + u + v)) + sign (g (x + u)) + sign (g (x + v)) + sign (g x)
        ≤ |sign (g (x + u + v)) + sign (g (x + u)) + sign (g (x + v)) + sign (g x)| := le_abs_self _
      _ = 2 := sign_quad_sum _ _ _ _ (h4 x hx)
  simp only [Finset.sum_const, nsmul_eq_mul] at hle
  linarith

lemma card_filter_linear_eq {E : Type*} [Fintype E] [DecidableEq E] [AddCommGroup E] [Module F E]
    {p : ℕ} (M : E →ₗ[F] (Fin p → F)) (hsurj : Function.Surjective M) (rhs : Fin p → F) :
    (Finset.univ.filter (fun x : E => M x = rhs)).card * 2 ^ p = Fintype.card E := by
  classical
  obtain ⟨x0, hx0⟩ := hsurj rhs
  have hcard_ker : (Finset.univ.filter (fun x : E => M x = rhs)).card =
      Fintype.card (LinearMap.ker M) := by
    rw [← Finset.card_univ]; symm
    apply Finset.card_nbij (fun v : LinearMap.ker M => v.1 + x0)
    · intro v _
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [map_add, LinearMap.mem_ker.mp v.2, zero_add, hx0]⟩
    · intro v1 _ v2 _ heq; ext
      have := congrArg (· + x0) heq
      simpa only [add_assoc, vec_add_self, add_zero] using this
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      have hker : y + x0 ∈ LinearMap.ker M := by
        rw [LinearMap.mem_ker, map_add, hy.2, hx0, vec_add_self]
      refine ⟨⟨y + x0, hker⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      dsimp only; rw [add_assoc, vec_add_self, add_zero]
  rw [hcard_ker]
  have hrange : LinearMap.range M = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrk := LinearMap.finrank_range_add_finrank_ker M
  rw [hrange, finrank_top, Module.finrank_fin_fun] at hrk
  have hcE : Fintype.card E = 2 ^ Module.finrank F E := by
    have := Module.card_eq_pow_finrank (K := F) (V := E); simpa [ZMod.card] using this
  have hcK : Fintype.card (LinearMap.ker M) = 2 ^ Module.finrank F (LinearMap.ker M) := by
    have := Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker M); simpa [ZMod.card] using this
  rw [hcE, hcK, ← pow_add, add_comm, hrk]

lemma linearMap_surjective_of_li {E : Type*} [AddCommGroup E] [Module F E]
    {p : ℕ} (μ : Fin p → (E →ₗ[F] F)) (hμ : LinearIndependent F μ) :
    Function.Surjective (LinearMap.pi μ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hex : ∃ v : Fin p → F, v ∉ LinearMap.range (LinearMap.pi μ) := by
    by_contra h; push Not at h; exact hne (eq_top_iff.mpr fun v _ => h v)
  obtain ⟨v, hv⟩ := hex
  obtain ⟨c, hrange0, hcv⟩ := exists_dotProduct_one_of_notMem (LinearMap.range (LinearMap.pi μ)) v hv
  have hsum0 : ∑ j : Fin p, c j • μ j = 0 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    have hx := hrange0 (LinearMap.pi μ x) ⟨x, rfl⟩
    simpa [dotProduct, mul_comm] using hx
  have hc0 : ∀ j, c j = 0 := Fintype.linearIndependent_iff.mp hμ c hsum0
  have : dotProduct v c = 0 := by simp [dotProduct, hc0]
  rw [hcv] at this
  exact f_one_ne_zero this

lemma exists_hadamard_unit {m : ℕ} (I : Finset (Fin m))
    (W : Submodule F ((I → F) × (I → F)))
    (hdim : I.card < Module.finrank F W) :
    ∃ i ∈ I, ∃ u ∈ W, ∃ v ∈ W,
      ∀ j : I, u.1 j * v.2 j + u.2 j * v.1 j = if j.1 = i then 1 else 0 := by
  classical
  let Ub : Submodule F (I → F) := W.map (LinearMap.fst F (I → F) (I → F))
  let Uc : Submodule F (I → F) := W.comap (LinearMap.inr F (I → F) (I → F))
  let f : W →ₗ[F] (I → F) := (LinearMap.fst F (I → F) (I → F)).domRestrict W
  have hrange : LinearMap.range f = Ub := by ext b; simp [f, Ub, Submodule.mem_map]
  have hker_equiv : LinearMap.ker f ≃ₗ[F] Uc :=
    { toFun := fun x => ⟨x.1.1.2, by
        have hx0 : x.1.1.1 = 0 := x.2
        have : (0, x.1.1.2) = x.1.1 := by ext <;> simp [hx0]
        change (0, x.1.1.2) ∈ W
        rw [this]; exact x.1.2⟩
      invFun := fun c => ⟨⟨(0, c.1), c.2⟩, rfl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; apply Prod.ext; exact x.2.symm; rfl
      right_inv := fun _ => rfl }
  have hdim_sum : Module.finrank F Ub + Module.finrank F Uc = Module.finrank F W := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, hker_equiv.finrank_eq] at this; exact this
  let resUb (J : Finset I) : Ub →ₗ[F] (J → F) :=
    { toFun := fun b j => b.1 j.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let good : Finset (Finset I) := Finset.univ.filter (fun J => Function.Injective (resUb J))
  have huniv_good : (Finset.univ : Finset I) ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    intro b1 b2 heq; ext i; exact congrFun heq ⟨i, Finset.mem_univ i⟩
  obtain ⟨J, hJgood, hJmin⟩ := Finset.exists_min_image good Finset.card ⟨Finset.univ, huniv_good⟩
  have hJinj : Function.Injective (resUb J) := (Finset.mem_filter.mp hJgood).2
  have hUb_le : Module.finrank F Ub ≤ J.card := by
    have := LinearMap.finrank_le_finrank_of_injective hJinj
    simpa [Module.finrank_pi, Fintype.card_coe] using this
  have hJ_le : J.card ≤ I.card := by
    have := Finset.card_le_univ J; simpa [Fintype.card_coe] using this
  have hbasis : ∀ j ∈ J, ∃ b ∈ Ub, (∀ i ∈ J, b i = if i = j then 1 else 0) := by
    intro j hj
    have hnot : ¬ Function.Injective (resUb (J.erase j)) := by
      intro hinj
      have hmem : J.erase j ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj⟩
      have hle := hJmin (J.erase j) hmem
      have hlt := Finset.card_erase_lt_of_mem hj
      omega
    have hker_ne : LinearMap.ker (resUb (J.erase j)) ≠ ⊥ := by
      intro hbot; exact hnot (LinearMap.ker_eq_bot.mp hbot)
    obtain ⟨b, hbker, hbne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
    have hb_erase : ∀ i ∈ J.erase j, b.1 i = 0 := fun i hi =>
      congrFun (LinearMap.mem_ker.mp hbker) ⟨i, hi⟩
    have hbj : b.1 j = 1 := by
      rcases f_cases (b.1 j) with h0 | h1
      · exfalso; apply hbne; apply hJinj; ext ⟨i, hi⟩
        by_cases hij : i = j
        · subst hij; exact h0
        · exact hb_erase i (Finset.mem_erase.mpr ⟨hij, hi⟩)
      · exact h1
    refine ⟨b.1, b.2, fun i hi => ?_⟩
    by_cases hij : i = j
    · subst hij; simp [hbj]
    · simp [hij, hb_erase i (Finset.mem_erase.mpr ⟨hij, hi⟩)]
  let Jc : Finset I := Jᶜ
  let resUc : Uc →ₗ[F] (Jc → F) :=
    { toFun := fun c i => c.1 i.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hker_pos : 0 < Module.finrank F (LinearMap.ker resUc) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker resUc
    have h1 : Module.finrank F (LinearMap.range resUc) ≤ Module.finrank F (Jc → F) :=
      Submodule.finrank_le _
    have h2 : Module.finrank F (Jc → F) = Jc.card := by rw [Module.finrank_pi, Fintype.card_coe]
    have h3 : Jc.card = I.card - J.card := by simp [Jc, Finset.card_compl, Fintype.card_coe]
    omega
  have hker_ne : LinearMap.ker resUc ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hker_pos; omega
  obtain ⟨c, hcker, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hc_out : ∀ i : I, i ∉ J → c.1 i = 0 := fun i hi =>
    congrFun (LinearMap.mem_ker.mp hcker) ⟨i, Finset.mem_compl.mpr hi⟩
  have hex_j : ∃ j : I, c.1 j ≠ 0 := by
    by_contra hall; push Not at hall; apply hcne; ext i; exact hall i
  obtain ⟨j0, hj0ne⟩ := hex_j
  have hj0J : j0 ∈ J := by by_contra hn; exact hj0ne (hc_out j0 hn)
  have hcj0 : c.1 j0 = 1 := by
    rcases f_cases (c.1 j0) with h0 | h1
    · exact absurd h0 hj0ne
    · exact h1
  obtain ⟨b, hbUb, hb_spec⟩ := hbasis j0 hj0J
  obtain ⟨⟨b', c'⟩, hbcW, hfst⟩ := Submodule.mem_map.mp hbUb
  change b' = b at hfst
  subst hfst
  refine ⟨j0.1, j0.2, (b', c'), hbcW, (0, c.1), c.2, fun i => ?_⟩
  simp only [Pi.zero_apply, mul_zero, add_zero]
  by_cases hiJ : i ∈ J
  · rw [hb_spec i hiJ]
    by_cases hij : i = j0
    · subst hij; simp [hcj0]
    · have hval : i.1 ≠ j0.1 := fun h => hij (Subtype.ext h)
      simp [hij, hval]
  · rw [hc_out i hiJ, mul_zero]
    have hval : i.1 ≠ j0.1 := fun h => hiJ (Subtype.ext h ▸ hj0J)
    simp [hval]

inductive YSLP (n : ℕ) : ℕ → Type
  | nil : YSLP n 0
  | cons {pY : ℕ} (prev : YSLP n pY)
      (a1 a2 : Fin n → F) (c1 c2 : F) (w1 w2 : Fin pY → F) : YSLP n (pY + 1)

def YSLP.eval {n : ℕ} : {pY : ℕ} → YSLP n pY → (Fin n → F) → (Fin pY → F)
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .cons prev a1 a2 c1 c2 w1 w2, y =>
    let q := prev.eval y
    Fin.snoc q ((c1 + dotProduct a1 y + ∑ r, w1 r * q r) *
                (c2 + dotProduct a2 y + ∑ r, w2 r * q r))

structure YAff (n pY : ℕ) where
  lin : Fin n → F
  cst : F
  wt : Fin pY → F

def YAff.eval {n pY : ℕ} (P : YSLP n pY) (e : YAff n pY) (y : Fin n → F) : F :=
  e.cst + dotProduct e.lin y + ∑ r, e.wt r * P.eval y r
def YAff.zero {n pY : ℕ} : YAff n pY := ⟨0, 0, 0⟩
def YAff.const {n pY : ℕ} (c : F) : YAff n pY := ⟨0, c, 0⟩
def YAff.add {n pY : ℕ} (e1 e2 : YAff n pY) : YAff n pY := ⟨e1.lin + e2.lin, e1.cst + e2.cst, e1.wt + e2.wt⟩
def YAff.lift {n pY : ℕ} (e : YAff n pY) : YAff n (pY + 1) := ⟨e.lin, e.cst, Fin.snoc e.wt 0⟩
def YAff.last {n : ℕ} (pY : ℕ) : YAff n (pY + 1) := ⟨0, 0, Fin.snoc 0 1⟩
def YAff.linComb {n pY k : ℕ} (c : Fin k → F) (es : Fin k → YAff n pY) : YAff n pY :=
  ⟨∑ j, c j • (es j).lin, ∑ j, c j * (es j).cst, ∑ j, c j • (es j).wt⟩

lemma YAff.eval_zero {n pY : ℕ} (P : YSLP n pY) (y : Fin n → F) :
    (YAff.zero (n := n) (pY := pY)).eval P y = 0 := by simp [YAff.eval, YAff.zero]
lemma YAff.eval_const {n pY : ℕ} (P : YSLP n pY) (c : F) (y : Fin n → F) :
    (YAff.const (n := n) (pY := pY) c).eval P y = c := by simp [YAff.eval, YAff.const]
lemma YAff.eval_add {n pY : ℕ} (P : YSLP n pY) (e1 e2 : YAff n pY) (y : Fin n → F) :
    (e1.add e2).eval P y = e1.eval P y + e2.eval P y := by
  simp only [YAff.eval, YAff.add, add_dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
lemma YAff.eval_lift {n pY : ℕ} (prev : YSLP n pY) (a1 a2 c1 c2 w1 w2)
    (e : YAff n pY) (y : Fin n → F) :
    e.lift.eval (.cons prev a1 a2 c1 c2 w1 w2) y = e.eval prev y := by
  simp only [YAff.eval, YAff.lift, YSLP.eval, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, zero_mul, add_zero]
lemma YAff.eval_last {n pY : ℕ} (prev : YSLP n pY) (a1 a2 c1 c2 w1 w2) (y : Fin n → F) :
    (YAff.last pY).eval (.cons prev a1 a2 c1 c2 w1 w2) y =
      (c1 + dotProduct a1 y + ∑ r, w1 r * prev.eval y r) *
      (c2 + dotProduct a2 y + ∑ r, w2 r * prev.eval y r) := by
  simp only [YAff.eval, YAff.last, YSLP.eval, zero_dotProduct, zero_add,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, one_mul]
lemma YAff.eval_linComb {n pY k : ℕ} (P : YSLP n pY) (c : Fin k → F)
    (es : Fin k → YAff n pY) (y : Fin n → F) :
    (YAff.linComb c es).eval P y = ∑ j, c j * (es j).eval P y := by
  simp only [YAff.eval, YAff.linComb, sum_dotProduct, smul_dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro r _; ring

structure Branch (n : ℕ) where
  pX : ℕ
  pY : ℕ
  u : Fin pX → (Fin n → F)
  hu : LinearIndependent F u
  slp : YSLP n pY
  rhs : Fin pX → YAff n pY
  wires : ℕ → (Fin n → F) × YAff n pY

def Branch.slice {n : ℕ} (B : Branch n) (y : Fin n → F) : Finset (Fin n → F) :=
  Finset.univ.filter (fun x => ∀ j : Fin B.pX, dotProduct (B.u j) x = (B.rhs j).eval B.slp y)

def BranchValid (n : ℕ) (gs : List Gate) (B : Branch n) : Prop :=
  ∀ (x y : Fin n → F), x ∈ B.slice y → ∀ i : ℕ,
    b2f ((Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false) =
      dotProduct (B.wires i).1 x + (B.wires i).2.eval B.slp y

lemma branch_append_affine {n : ℕ} (gs : List Gate) (g : Gate) (B : Branch n)
    (hB : BranchValid n gs B) (aNew : Fin n → F) (eNew : YAff n B.pY)
    (hval : ∀ x y, x ∈ B.slice y →
      b2f (g.op.eval (g.inputs.map (fun i =>
        (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false))) =
      dotProduct aNew x + eNew.eval B.slp y) :
    ∃ B' : Branch n,
      B'.pX = B.pX ∧ B'.pY = B.pY ∧ (∀ y, B'.slice y = B.slice y) ∧ BranchValid n (gs ++ [g]) B' := by
  let B' : Branch n :=
    { B with wires := fun i => if i = 2 * n + gs.length then (aNew, eNew) else B.wires i }
  refine ⟨B', rfl, rfl, fun _ => rfl, ?_⟩
  intro x y hx i
  have hlen : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).length = 2 * n + gs.length := by
    rw [wires_length, List.length_append, bitsOf_length, bitsOf_length]; omega
  rw [wires_append, wires_singleton]
  by_cases hi : i = 2 * n + gs.length
  · subst hi; simp only [B', ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    exact hval x y hx
  · simp only [B', hi, ↓reduceIte]
    by_cases hlt : i < 2 * n + gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      simpa [List.getD_eq_getElem?_getD] using hB x y hx i
    · have h1 : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y) ++
          [g.op.eval (g.inputs.map (fun j =>
            (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD j false))]).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hlen]; omega)]; rfl
      have h2 : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h1, ← h2]; exact hB x y hx i

lemma linearIndependent_snoc_of_notMem {E : Type*} [AddCommGroup E] [Module F E]
    {p : ℕ} (u : Fin p → E) (hu : LinearIndependent F u) (a : E)
    (ha : a ∉ Submodule.span F (Set.range u)) :
    LinearIndependent F (Fin.snoc u a) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_castSucc, Fin.snoc_last] at hc
  simp only [Fin.snoc_castSucc] at hc
  have hlast : c (Fin.last p) = 0 := by
    by_contra hne
    have hc1 : c (Fin.last p) = 1 := by
      rcases f_cases (c (Fin.last p)) with h0 | h1
      · exact absurd h0 hne
      · exact h1
    rw [hc1, one_smul] at hc
    have ha_eq : a = ∑ i : Fin p, c i.castSucc • u i := by
      have := congrArg (· + a) hc
      simpa [add_assoc, vec_add_self] using this.symm
    apply ha; rw [ha_eq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hlast, zero_smul, add_zero] at hc
  have hcast := Fintype.linearIndependent_iff.mp hu (fun i => c i.castSucc) hc
  intro j; exact Fin.lastCases hlast (fun i => hcast i) j

lemma branch_step_mult {n : ℕ} (gs : List Gate) (g : Gate) (B : Branch n)
    (hB : BranchValid n gs B) (cOut c1 c2 : F) (i1 i2 : ℕ)
    (hval : ∀ x y, x ∈ B.slice y →
      b2f (g.op.eval (g.inputs.map (fun i =>
        (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false))) =
      cOut + (b2f ((Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i1 false) + c1) *
             (b2f ((Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i2 false) + c2)) :
    ∃ bs : List (Branch n),
      (∀ B' ∈ bs, B'.pX + B'.pY ≤ B.pX + B.pY + 1) ∧
      (∀ B' ∈ bs, BranchValid n (gs ++ [g]) B') ∧
      (∀ (y : Fin n → F) (G : (Fin n → F) → ℝ),
        ∑ x ∈ B.slice y, G x = (bs.map (fun B' => ∑ x ∈ B'.slice y, G x)).sum) := by
  classical
  let aL := (B.wires i1).1
  let eL := (B.wires i1).2.add (YAff.const c1)
  let aR := (B.wires i2).1
  let eR := (B.wires i2).2.add (YAff.const c2)
  let U : Submodule F (Fin n → F) := Submodule.span F (Set.range B.u)
  have hstep_split : ∀ (aP aQ : Fin n → F) (eP eQ : YAff n B.pY),
      aP ∉ U →
      (∀ x y, x ∈ B.slice y →
        b2f (g.op.eval (g.inputs.map (fun i =>
          (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false))) =
        cOut + (dotProduct aP x + eP.eval B.slp y) * (dotProduct aQ x + eQ.eval B.slp y)) →
      ∃ bs : List (Branch n),
        (∀ B' ∈ bs, B'.pX + B'.pY ≤ B.pX + B.pY + 1) ∧
        (∀ B' ∈ bs, BranchValid n (gs ++ [g]) B') ∧
        (∀ (y : Fin n → F) (G : (Fin n → F) → ℝ),
          ∑ x ∈ B.slice y, G x = (bs.map (fun B' => ∑ x ∈ B'.slice y, G x)).sum) := by
    intro aP aQ eP eQ haP hprod
    have hu' := linearIndependent_snoc_of_notMem B.u B.hu aP haP
    let mkBranch (ε : F) : Branch n :=
      { pX := B.pX + 1, pY := B.pY, u := Fin.snoc B.u aP, hu := hu', slp := B.slp
        rhs := Fin.snoc B.rhs (eP.add (YAff.const ε))
        wires := fun i =>
          if i = 2 * n + gs.length then
            if ε = 0 then (0, YAff.const cOut) else (aQ, eQ.add (YAff.const cOut))
          else B.wires i }
    have hslice_eq : ∀ ε y, (mkBranch ε).slice y =
        (B.slice y).filter (fun x => dotProduct aP x + eP.eval B.slp y = ε) := by
      intro ε y; ext x
      simp only [Branch.slice, mkBranch, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨fun j => by simpa [Fin.snoc_castSucc] using h j.castSucc, ?_⟩
        have hl := h (Fin.last B.pX)
        simp only [Fin.snoc_last, YAff.eval_add, YAff.eval_const] at hl
        rw [hl, add_comm (eP.eval B.slp y), add_assoc, f_add_self, add_zero]
      · rintro ⟨h1, h2⟩ j
        refine Fin.lastCases ?_ (fun i => by simpa [Fin.snoc_castSucc] using h1 i) j
        simp only [Fin.snoc_last, YAff.eval_add, YAff.eval_const]
        have := congrArg (· + eP.eval B.slp y) h2
        simpa only [add_assoc, f_add_self, add_zero, add_comm ε] using this
    have hvalid : ∀ ε, BranchValid n (gs ++ [g]) (mkBranch ε) := by
      intro ε x y hx i
      have hx' := (hslice_eq ε y) ▸ hx
      have hxB : x ∈ B.slice y := (Finset.mem_filter.mp hx').1
      have hpe : dotProduct aP x + eP.eval B.slp y = ε := (Finset.mem_filter.mp hx').2
      have hlen : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).length = 2 * n + gs.length := by
        rw [wires_length, List.length_append, bitsOf_length, bitsOf_length]; omega
      rw [wires_append, wires_singleton]
      by_cases hi : i = 2 * n + gs.length
      · subst hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some]
        rw [hprod x y hxB, hpe]; simp only [mkBranch, ↓reduceIte]
        rcases f_cases ε with rfl | rfl
        · simp [YAff.eval_const]
        · simp [YAff.eval_add, YAff.eval_const]; ring
      · simp only [mkBranch, hi, ↓reduceIte]
        by_cases hlt : i < 2 * n + gs.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hB x y hxB i
        · have h1 : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y) ++
              [g.op.eval (g.inputs.map (fun j =>
                (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD j false))]).getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hlen]; omega)]; rfl
          have h2 : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          rw [h1, ← h2]; exact hB x y hxB i
    refine ⟨[mkBranch 0, mkBranch 1], ?_, ?_, ?_⟩
    · intro B' hB'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hB'
      rcases hB' with rfl | rfl <;> simp [mkBranch] <;> omega
    · intro B' hB'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hB'
      rcases hB' with rfl | rfl
      · exact hvalid 0
      · exact hvalid 1
    · intro y G
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hslice_eq]
      have hdisj : Disjoint ((B.slice y).filter (fun x => dotProduct aP x + eP.eval B.slp y = 0))
                            ((B.slice y).filter (fun x => dotProduct aP x + eP.eval B.slp y = 1)) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        have e1 := (Finset.mem_filter.mp h1).2
        have e2 := (Finset.mem_filter.mp h2).2
        rw [e1] at e2; exact f_one_ne_zero e2.symm
      have hunion : ((B.slice y).filter (fun x => dotProduct aP x + eP.eval B.slp y = 0)) ∪
                    ((B.slice y).filter (fun x => dotProduct aP x + eP.eval B.slp y = 1)) = B.slice y := by
        ext x; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          rcases f_cases (dotProduct aP x + eP.eval B.slp y) with h0 | h1
          · exact Or.inl ⟨h, h0⟩
          · exact Or.inr ⟨h, h1⟩
      rw [← Finset.sum_union hdisj, hunion]
  have hprodLR : ∀ x y, x ∈ B.slice y →
      b2f (g.op.eval (g.inputs.map (fun i =>
        (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false))) =
      cOut + (dotProduct aL x + eL.eval B.slp y) * (dotProduct aR x + eR.eval B.slp y) := by
    intro x y hx
    rw [hval x y hx, hB x y hx i1, hB x y hx i2]
    simp [aL, eL, aR, eR, YAff.eval_add, YAff.eval_const, add_assoc]
  by_cases haL : aL ∈ U
  · by_cases haR : aR ∈ U
    · obtain ⟨cL, hcL⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp haL
      obtain ⟨cR, hcR⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp haR
      let fL : YAff n B.pY := (YAff.linComb cL B.rhs).add eL
      let fR : YAff n B.pY := (YAff.linComb cR B.rhs).add eR
      let slp' : YSLP n (B.pY + 1) :=
        YSLP.cons B.slp fL.lin fR.lin fL.cst fR.cst fL.wt fR.wt
      let B' : Branch n :=
        { pX := B.pX, pY := B.pY + 1, u := B.u, hu := B.hu, slp := slp'
          rhs := fun j => (B.rhs j).lift
          wires := fun i =>
            if i = 2 * n + gs.length then (0, (YAff.last B.pY).add (YAff.const cOut))
            else ((B.wires i).1, (B.wires i).2.lift) }
      have hslice' : ∀ y, B'.slice y = B.slice y := by
        intro y; ext x
        simp only [Branch.slice, B', slp', Finset.mem_filter, Finset.mem_univ, true_and,
          YAff.eval_lift]
      refine ⟨[B'], ?_, ?_, ?_⟩
      · intro B1 hB1; simp at hB1; subst hB1; simp [B']; omega
      · intro B1 hB1; simp at hB1; subst hB1
        intro x y hx i
        have hxB : x ∈ B.slice y := (hslice' y) ▸ hx
        have hlen : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).length = 2 * n + gs.length := by
          rw [wires_length, List.length_append, bitsOf_length, bitsOf_length]; omega
        rw [wires_append, wires_singleton]
        by_cases hi : i = 2 * n + gs.length
        · subst hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          simp only [List.getElem?_cons_zero, Option.getD_some]
          rw [hprodLR x y hxB]
          simp only [B', ↓reduceIte, zero_dotProduct, zero_add, YAff.eval_add, YAff.eval_const,
            slp', YAff.eval_last]
          have hdotL : dotProduct aL x = (YAff.linComb cL B.rhs).eval B.slp y := by
            rw [← hcL, sum_dotProduct, YAff.eval_linComb]
            apply Finset.sum_congr rfl; intro j _
            rw [smul_dotProduct, smul_eq_mul, (Finset.mem_filter.mp hxB).2 j]
          have hdotR : dotProduct aR x = (YAff.linComb cR B.rhs).eval B.slp y := by
            rw [← hcR, sum_dotProduct, YAff.eval_linComb]
            apply Finset.sum_congr rfl; intro j _
            rw [smul_dotProduct, smul_eq_mul, (Finset.mem_filter.mp hxB).2 j]
          rw [hdotL, hdotR]
          have heL' : (YAff.linComb cL B.rhs).eval B.slp y + eL.eval B.slp y =
              fL.cst + dotProduct fL.lin y + ∑ r, fL.wt r * B.slp.eval y r := by
            rw [← YAff.eval_add]; rfl
          have heR' : (YAff.linComb cR B.rhs).eval B.slp y + eR.eval B.slp y =
              fR.cst + dotProduct fR.lin y + ∑ r, fR.wt r * B.slp.eval y r := by
            rw [← YAff.eval_add]; rfl
          rw [heL', heR', add_comm]
        · simp only [B', hi, ↓reduceIte, slp', YAff.eval_lift]
          by_cases hlt : i < 2 * n + gs.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
            simpa [List.getD_eq_getElem?_getD] using hB x y hxB i
          · have h1 : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y) ++
                [g.op.eval (g.inputs.map (fun j =>
                  (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD j false))]).getD i false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hlen]; omega)]; rfl
            have h2 : (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
            rw [h1, ← h2]; exact hB x y hxB i
      · intro y G; simp [hslice']
    · exact hstep_split aR aL eR eL haR (fun x y hx => by rw [hprodLR x y hx, mul_comm])
  · exact hstep_split aL aR eL eR haL hprodLR

lemma stage1_decomp (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, gateLegal g) :
    ∃ bs : List (Branch n),
      (∀ B ∈ bs, B.pX + B.pY ≤ gs.countP isMult) ∧
      (∀ B ∈ bs, BranchValid n gs B) ∧
      (∀ (y : Fin n → F) (G : (Fin n → F) → ℝ),
        ∑ x : Fin n → F, G x = (bs.map (fun B => ∑ x ∈ B.slice y, G x)).sum) := by
  induction gs using List.reverseRecOn with
  | nil =>
    let B0 : Branch n :=
      { pX := 0, pY := 0, u := Fin.elim0, hu := linearIndependent_empty_type
        slp := .nil, rhs := Fin.elim0
        wires := fun i =>
          if h1 : i < n then (Pi.single ⟨i, h1⟩ 1, YAff.zero)
          else if h2 : i < 2 * n then (0, ⟨Pi.single ⟨i - n, by omega⟩ 1, 0, Fin.elim0⟩)
          else (0, YAff.zero) }
    refine ⟨[B0], ?_, ?_, ?_⟩
    · intro B hB; simp at hB; subst hB; simp [B0]
    · intro B hB; simp at hB; subst hB
      intro x y _ i
      simp only [Circuit.wires, List.foldl_nil, B0]
      by_cases h1 : i < n
      · simp only [h1, ↓reduceDIte, YAff.eval_zero, add_zero]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bitsOf_length]; exact h1)]
        simp [bitsOf, h1, b2f_f2b, dotProduct, Pi.single_apply]
      · by_cases h2 : i < 2 * n
        · simp only [h1, h2, ↓reduceDIte, zero_dotProduct, zero_add, YAff.eval]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [bitsOf_length]; omega),
            bitsOf_length]
          have hsub : i - n < n := by omega
          simp [bitsOf, hsub, b2f_f2b, dotProduct, Pi.single_apply]
        · simp only [h1, h2, ↓reduceDIte, zero_dotProduct, zero_add, YAff.eval_zero]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [bitsOf_length]; omega)]
          rfl
    · intro y G; simp [B0, Branch.slice]
  | append_singleton gs g ih =>
    have hgs' : ∀ h ∈ gs, gateLegal h := fun h hh => hgs h (by simp [hh])
    have hg : gateLegal g := hgs g (by simp)
    obtain ⟨bs, hcost, hvalid, hpart⟩ := ih hgs'
    have hstep_each : ∀ B ∈ bs,
        ∃ bs' : List (Branch n),
          (∀ B' ∈ bs', B'.pX + B'.pY ≤ B.pX + B.pY + if isMult g then 1 else 0) ∧
          (∀ B' ∈ bs', BranchValid n (gs ++ [g]) B') ∧
          (∀ (y : Fin n → F) (G : (Fin n → F) → ℝ),
            ∑ x ∈ B.slice y, G x = (bs'.map (fun B' => ∑ x ∈ B'.slice y, G x)).sum) := by
      intro B hB
      have hBv := hvalid B hB
      rcases hg with ⟨hlen, hop⟩
      match hins : g.inputs with
      | [] =>
        have hnm : isMult g = false := by simp [isMult, hins]
        have hconst : ∃ c : F, ∀ x y,
            b2f (g.op.eval (g.inputs.map (fun i =>
              (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false))) = c := by
          rw [hins]
          rcases hop with h | h | h | ⟨_, h1⟩
          · exact ⟨1, fun _ _ => by rw [h]; rfl⟩
          · exact ⟨0, fun _ _ => by rw [h]; rfl⟩
          · exact ⟨1, fun _ _ => by rw [h]; rfl⟩
          · simp [hins] at h1
        obtain ⟨c, hc⟩ := hconst
        obtain ⟨B', hpX, hpY, hsl, hv'⟩ := branch_append_affine gs g B hBv 0 (YAff.const c)
          (fun x y _ => by rw [hc x y, zero_dotProduct, zero_add, YAff.eval_const])
        exact ⟨[B'], fun B1 hB1 => by simp at hB1; subst hB1; simp [hnm, hpX, hpY],
          fun B1 hB1 => by simp at hB1; subst hB1; exact hv', fun y G => by simp [hsl]⟩
      | [i1] =>
        have hnm : isMult g = false := by simp [isMult, hins]
        have haff : ∃ c : F, ∀ x y, x ∈ B.slice y →
            b2f (g.op.eval (g.inputs.map (fun i =>
              (Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i false))) =
            dotProduct (B.wires i1).1 x + ((B.wires i1).2.add (YAff.const c)).eval B.slp y := by
          rcases hop with h | h | h | ⟨h, _⟩
          · refine ⟨0, fun x y hx => ?_⟩
            rw [hins, h]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, Bool.and_true, id_eq, YAff.eval_add, YAff.eval_const, add_zero]
            exact hBv x y hx i1
          · refine ⟨0, fun x y hx => ?_⟩
            rw [hins, h]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, Bool.or_false, id_eq, YAff.eval_add, YAff.eval_const, add_zero]
            exact hBv x y hx i1
          · refine ⟨1, fun x y hx => ?_⟩
            rw [hins, h]; simp only [List.map_cons, List.map_nil, b2f_mod2_one,
              YAff.eval_add, YAff.eval_const]
            rw [hBv x y hx i1, add_assoc]
          · refine ⟨1, fun x y hx => ?_⟩
            rw [hins, h]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons,
              b2f_not, YAff.eval_add, YAff.eval_const]
            rw [hBv x y hx i1, add_assoc]
        obtain ⟨c, hc⟩ := haff
        obtain ⟨B', hpX, hpY, hsl, hv'⟩ :=
          branch_append_affine gs g B hBv (B.wires i1).1 ((B.wires i1).2.add (YAff.const c)) hc
        exact ⟨[B'], fun B1 hB1 => by simp at hB1; subst hB1; simp [hnm, hpX, hpY],
          fun B1 hB1 => by simp at hB1; subst hB1; exact hv', fun y G => by simp [hsl]⟩
      | [i1, i2] =>
        rcases hop with h | h | h | ⟨_, h1⟩
        · have hm : isMult g = true := by simp [isMult, h, hins]
          obtain ⟨bs', h1, h2, h3⟩ := branch_step_mult gs g B hBv 0 0 0 i1 i2 (fun x y _ => by
            rw [hins, h]; simp [GateOp.eval, b2f_and])
          exact ⟨bs', fun B' hB' => by rw [hm]; simpa using h1 B' hB', h2, h3⟩
        · have hm : isMult g = true := by simp [isMult, h, hins]
          obtain ⟨bs', h1, h2, h3⟩ := branch_step_mult gs g B hBv 1 1 1 i1 i2 (fun x y _ => by
            rw [hins, h]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, Bool.or_false, id_eq, b2f_or]
            generalize b2f ((Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i1 false) = u
            generalize b2f ((Circuit.wires ⟨gs, 0⟩ (bitsOf n x ++ bitsOf n y)).getD i2 false) = v
            rcases f_cases u with rfl | rfl <;> rcases f_cases v with rfl | rfl <;> decide)
          exact ⟨bs', fun B' hB' => by rw [hm]; simpa using h1 B' hB', h2, h3⟩
        · have hnm : isMult g = false := by simp [isMult, h, hins]
          obtain ⟨B', hpX, hpY, hsl, hv'⟩ := branch_append_affine gs g B hBv
            ((B.wires i1).1 + (B.wires i2).1)
            (((B.wires i1).2.add (B.wires i2).2).add (YAff.const 1)) (fun x y hx => by
              rw [hins, h]; simp only [List.map_cons, List.map_nil, b2f_mod2_two]
              rw [hBv x y hx i1, hBv x y hx i2, add_dotProduct, YAff.eval_add, YAff.eval_add,
                YAff.eval_const]; ring)
          exact ⟨[B'], fun B1 hB1 => by simp at hB1; subst hB1; simp [hnm, hpX, hpY],
            fun B1 hB1 => by simp at hB1; subst hB1; exact hv', fun y G => by simp [hsl]⟩
        · simp [hins] at h1
      | _ :: _ :: _ :: _ => simp [hins] at hlen
    choose step_fn hstep_spec using fun B : {B // B ∈ bs} => hstep_each B.1 B.2
    let bs_all : List (Branch n) := bs.attach.flatMap step_fn
    refine ⟨bs_all, ?_, ?_, ?_⟩
    · intro B' hB'
      simp only [bs_all, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hB'
      obtain ⟨B, hB, hB'm⟩ := hB'
      have h1 : B'.pX + B'.pY ≤ B.pX + B.pY + if isMult g then 1 else 0 :=
        (hstep_spec ⟨B, hB⟩).1 B' hB'm
      have h2 := hcost B hB
      simp only [List.countP_append, List.countP_cons, List.countP_nil]
      split_ifs at h1 ⊢ <;> omega
    · intro B' hB'
      simp only [bs_all, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hB'
      obtain ⟨B, hB, hB'm⟩ := hB'
      exact (hstep_spec ⟨B, hB⟩).2.1 B' hB'm
    · intro y G
      rw [hpart y G]
      simp only [bs_all, list_sum_flatMap]
      congr 1
      conv_lhs => rw [← List.attach_map_val]
      apply List.map_congr_left; intro B _
      exact (hstep_spec B).2.2 y G

structure WBranch (k m r pY : ℕ) where
  tW : ℕ
  htW : tW ≤ pY
  μ : Fin tW → (Wfull m r →ₗ[F] F)
  hμ : LinearIndependent F μ
  ρ : Fin tW → ((Fin k → F) → F)
  Λ : Fin pY → (Wfull m r →ₗ[F] F)
  σ : Fin pY → ((Fin k → F) → F)

def WBranch.slice {k m r pY : ℕ} (τ : WBranch k m r pY) (s : Fin k → F) : Finset (Wfull m r) :=
  Finset.univ.filter (fun w => ∀ j : Fin τ.tW, τ.μ j w = τ.ρ j s)

def WBranchValid {k m r pY : ℕ} (e : V k m r ≃ₗ[F] S k × Wfull m r)
    (P : YSLP (k + 2 * m + r) pY) (τ : WBranch k m r pY) : Prop :=
  ∀ (s : S k) (w : Wfull m r), w ∈ τ.slice s → ∀ q : Fin pY,
    P.eval (e.symm (s, w)) q = τ.Λ q w + τ.σ q s

lemma stage2_decomp {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r)
    {pY : ℕ} (P : YSLP (k + 2 * m + r) pY) :
    ∃ τs : List (WBranch k m r pY),
      (∀ τ ∈ τs, WBranchValid e P τ) ∧
      (∀ (s : S k) (G : Wfull m r → ℝ),
        ∑ w : Wfull m r, G w = (τs.map (fun τ => ∑ w ∈ τ.slice s, G w)).sum) := by
  classical
  induction P with
  | nil =>
    let τ0 : WBranch k m r 0 :=
      { tW := 0, htW := le_rfl, μ := Fin.elim0, hμ := linearIndependent_empty_type,
        ρ := Fin.elim0, Λ := Fin.elim0, σ := Fin.elim0 }
    refine ⟨[τ0], fun τ hτ => by simp at hτ; subst hτ; intro _ _ _ q; exact Fin.elim0 q,
      fun s G => by simp [τ0, WBranch.slice]⟩
  | @cons pY prev a1 a2 c1 c2 w1 w2 ih =>
    obtain ⟨τs, hval, hpart⟩ := ih
    let dotW (a : V k m r) : Wfull m r →ₗ[F] F :=
      { toFun := fun w => dotProduct a (e.symm (0, w))
        map_add' := fun u v => by
          have : ((0 : S k), u + v) = (0, u) + (0, v) := by apply Prod.ext <;> simp
          rw [this, map_add, dotProduct_add]
        map_smul' := fun c u => by
          have : ((0 : S k), c • u) = c • (0, u) := by apply Prod.ext <;> simp
          rw [this, map_smul, dotProduct_smul, RingHom.id_apply] }
    have hstep_each : ∀ τ ∈ τs,
        ∃ τs' : List (WBranch k m r (pY + 1)),
          (∀ τ' ∈ τs', WBranchValid e (.cons prev a1 a2 c1 c2 w1 w2) τ') ∧
          (∀ (s : S k) (G : Wfull m r → ℝ),
            ∑ w ∈ τ.slice s, G w = (τs'.map (fun τ' => ∑ w ∈ τ'.slice s, G w)).sum) := by
      intro τ hτ
      have hτv := hval τ hτ
      let L1 : Wfull m r →ₗ[F] F := dotW a1 + ∑ q : Fin pY, w1 q • τ.Λ q
      let S1 : S k → F := fun s => c1 + dotProduct a1 (e.symm (s, 0)) + ∑ q, w1 q * τ.σ q s
      let L2 : Wfull m r →ₗ[F] F := dotW a2 + ∑ q : Fin pY, w2 q • τ.Λ q
      let S2 : S k → F := fun s => c2 + dotProduct a2 (e.symm (s, 0)) + ∑ q, w2 q * τ.σ q s
      have hev1 : ∀ s w, w ∈ τ.slice s →
          c1 + dotProduct a1 (e.symm (s, w)) + ∑ q, w1 q * prev.eval (e.symm (s, w)) q =
            L1 w + S1 s := by
        intro s w hw
        have hsum : ∑ q, w1 q * prev.eval (e.symm (s, w)) q =
            (∑ q, w1 q * τ.Λ q w) + (∑ q, w1 q * τ.σ q s) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q _; rw [hτv s w hw q]; ring
        have hdecomp : (s, w) = (s, 0) + (0, w) := by apply Prod.ext <;> simp
        rw [hsum, hdecomp, map_add, dotProduct_add]
        simp only [L1, S1, dotW, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
        ring
      have hev2 : ∀ s w, w ∈ τ.slice s →
          c2 + dotProduct a2 (e.symm (s, w)) + ∑ q, w2 q * prev.eval (e.symm (s, w)) q =
            L2 w + S2 s := by
        intro s w hw
        have hsum : ∑ q, w2 q * prev.eval (e.symm (s, w)) q =
            (∑ q, w2 q * τ.Λ q w) + (∑ q, w2 q * τ.σ q s) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q _; rw [hτv s w hw q]; ring
        have hdecomp : (s, w) = (s, 0) + (0, w) := by apply Prod.ext <;> simp
        rw [hsum, hdecomp, map_add, dotProduct_add]
        simp only [L2, S2, dotW, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
        ring
      let Uμ : Submodule F (Wfull m r →ₗ[F] F) := Submodule.span F (Set.range τ.μ)
      have hsplit : ∀ (LP LQ : Wfull m r →ₗ[F] F) (SP SQ : S k → F),
          LP ∉ Uμ →
          (∀ s w, w ∈ τ.slice s →
            (c1 + dotProduct a1 (e.symm (s, w)) + ∑ q, w1 q * prev.eval (e.symm (s, w)) q) *
            (c2 + dotProduct a2 (e.symm (s, w)) + ∑ q, w2 q * prev.eval (e.symm (s, w)) q) =
            (LP w + SP s) * (LQ w + SQ s)) →
          ∃ τs' : List (WBranch k m r (pY + 1)),
            (∀ τ' ∈ τs', WBranchValid e (.cons prev a1 a2 c1 c2 w1 w2) τ') ∧
            (∀ (s : S k) (G : Wfull m r → ℝ),
              ∑ w ∈ τ.slice s, G w = (τs'.map (fun τ' => ∑ w ∈ τ'.slice s, G w)).sum) := by
        intro LP LQ SP SQ hLP hprod
        have hμ' := linearIndependent_snoc_of_notMem τ.μ τ.hμ LP hLP
        let mkW (ε : F) : WBranch k m r (pY + 1) :=
          { tW := τ.tW + 1, htW := Nat.succ_le_succ τ.htW, μ := Fin.snoc τ.μ LP, hμ := hμ'
            ρ := Fin.snoc τ.ρ (fun s => SP s + ε)
            Λ := Fin.snoc τ.Λ (if ε = 0 then 0 else LQ)
            σ := Fin.snoc τ.σ (if ε = 0 then 0 else SQ) }
        have hsl : ∀ ε s, (mkW ε).slice s = (τ.slice s).filter (fun w => LP w + SP s = ε) := by
          intro ε s; ext w
          simp only [WBranch.slice, mkW, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            refine ⟨fun j => by simpa [Fin.snoc_castSucc] using h j.castSucc, ?_⟩
            have hl := h (Fin.last τ.tW); simp only [Fin.snoc_last] at hl
            rw [hl, add_comm (SP s), add_assoc, f_add_self, add_zero]
          · rintro ⟨h1, h2⟩ j
            refine Fin.lastCases ?_ (fun i => by simpa [Fin.snoc_castSucc] using h1 i) j
            simp only [Fin.snoc_last]
            have := congrArg (· + SP s) h2
            simpa only [add_assoc, f_add_self, add_zero, add_comm ε] using this
        have hvalW : ∀ ε, WBranchValid e (.cons prev a1 a2 c1 c2 w1 w2) (mkW ε) := by
          intro ε s w hw q
          have hw' := (hsl ε s) ▸ hw
          have hwτ : w ∈ τ.slice s := (Finset.mem_filter.mp hw').1
          have hpe : LP w + SP s = ε := (Finset.mem_filter.mp hw').2
          refine Fin.lastCases ?_ (fun i => by
            simp only [YSLP.eval, Fin.snoc_castSucc, mkW]; exact hτv s w hwτ i) q
          simp only [YSLP.eval, Fin.snoc_last, mkW]
          rw [hprod s w hwτ, hpe]
          rcases f_cases ε with rfl | rfl <;> simp
        refine ⟨[mkW 0, mkW 1], ?_, ?_⟩
        · intro τ' hτ'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ'
          rcases hτ' with rfl | rfl
          · exact hvalW 0
          · exact hvalW 1
        · intro s G
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hsl]
          have hdisj : Disjoint ((τ.slice s).filter (fun w => LP w + SP s = 0))
                                ((τ.slice s).filter (fun w => LP w + SP s = 1)) := by
            rw [Finset.disjoint_left]; intro w h1 h2
            have e1 := (Finset.mem_filter.mp h1).2; have e2 := (Finset.mem_filter.mp h2).2
            rw [e1] at e2; exact f_one_ne_zero e2.symm
          have hunion : ((τ.slice s).filter (fun w => LP w + SP s = 0)) ∪
                        ((τ.slice s).filter (fun w => LP w + SP s = 1)) = τ.slice s := by
            ext w; simp only [Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
            · intro h
              rcases f_cases (LP w + SP s) with h0 | h1
              · exact Or.inl ⟨h, h0⟩
              · exact Or.inr ⟨h, h1⟩
          rw [← Finset.sum_union hdisj, hunion]
      by_cases hL1 : L1 ∈ Uμ
      · by_cases hL2 : L2 ∈ Uμ
        · obtain ⟨d1, hd1⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hL1
          obtain ⟨d2, hd2⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hL2
          let τ' : WBranch k m r (pY + 1) :=
            { tW := τ.tW, htW := Nat.le_succ_of_le τ.htW, μ := τ.μ, hμ := τ.hμ, ρ := τ.ρ
              Λ := Fin.snoc τ.Λ 0
              σ := Fin.snoc τ.σ (fun s =>
                ((∑ j, d1 j * τ.ρ j s) + S1 s) * ((∑ j, d2 j * τ.ρ j s) + S2 s)) }
          refine ⟨[τ'], ?_, fun s G => by simp [τ', WBranch.slice]⟩
          intro τ1 hτ1; simp at hτ1; subst hτ1
          intro s w hw q
          have hwτ : w ∈ τ.slice s := hw
          refine Fin.lastCases ?_ (fun i => by
            simp only [YSLP.eval, Fin.snoc_castSucc, τ']; exact hτv s w hwτ i) q
          simp only [YSLP.eval, Fin.snoc_last, τ', LinearMap.zero_apply, zero_add]
          rw [hev1 s w hwτ, hev2 s w hwτ]
          have h1 : L1 w = ∑ j, d1 j * τ.ρ j s := by
            rw [← hd1]; simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl; intro j _; rw [(Finset.mem_filter.mp hwτ).2 j]
          have h2 : L2 w = ∑ j, d2 j * τ.ρ j s := by
            rw [← hd2]; simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl; intro j _; rw [(Finset.mem_filter.mp hwτ).2 j]
          rw [h1, h2]
        · exact hsplit L2 L1 S2 S1 hL2 (fun s w hw => by rw [hev1 s w hw, hev2 s w hw, mul_comm])
      · exact hsplit L1 L2 S1 S2 hL1 (fun s w hw => by rw [hev1 s w hw, hev2 s w hw])
    choose step_fn hstep_spec using fun τ : {τ // τ ∈ τs} => hstep_each τ.1 τ.2
    let τs_all : List (WBranch k m r (pY + 1)) := τs.attach.flatMap step_fn
    refine ⟨τs_all, ?_, ?_⟩
    · intro τ' hτ'
      simp only [τs_all, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hτ'
      obtain ⟨τ, hτ, hτ'm⟩ := hτ'
      exact (hstep_spec ⟨τ, hτ⟩).1 τ' hτ'm
    · intro s G
      rw [hpart s G]
      simp only [τs_all, list_sum_flatMap]
      congr 1
      conv_lhs => rw [← List.attach_map_val]
      apply List.map_congr_left; intro τ _
      exact (hstep_spec τ).2 s G

lemma quad_diff_aff {α : Type*} [AddCommGroup α] [Module F α]
    (f : α →ₗ[F] F) (c : F) (x u v : α) :
    (f (x + u + v) + c) + (f (x + u) + c) + (f (x + v) + c) + (f x + c) = 0 := by
  simp only [map_add]
  have h2 : ∀ a : F, a + a = 0 := f_add_self
  have : (f x + f u + f v + c) + (f x + f u + c) + (f x + f v + c) + (f x + c) =
      ((f x + f x) + (f x + f x)) + (f u + f u) + (f v + f v) + ((c + c) + (c + c)) := by ring
  rw [this]; simp [h2]

lemma quad_diff_mul {α : Type*} [AddCommGroup α] [Module F α]
    (f1 f2 : α →ₗ[F] F) (c1 c2 : F) (x u v : α) :
    (f1 (x + u + v) + c1) * (f2 (x + u + v) + c2) +
    (f1 (x + u) + c1) * (f2 (x + u) + c2) +
    (f1 (x + v) + c1) * (f2 (x + v) + c2) +
    (f1 x + c1) * (f2 x + c2) =
    f1 u * f2 v + f1 v * f2 u := by
  simp only [map_add]
  have h2 : ∀ a : F, a + a = 0 := f_add_self
  have : (f1 x + f1 u + f1 v + c1) * (f2 x + f2 u + f2 v + c2) +
      (f1 x + f1 u + c1) * (f2 x + f2 u + c2) +
      (f1 x + f1 v + c1) * (f2 x + f2 v + c2) +
      (f1 x + c1) * (f2 x + c2) =
      (f1 u * f2 v + f1 v * f2 u) +
      (((f1 x * f2 x + f1 x * f2 x) + (f1 x * f2 x + f1 x * f2 x)) +
       (f1 x * f2 u + f1 x * f2 u) + (f1 x * f2 v + f1 x * f2 v) +
       ((f1 x * c2 + f1 x * c2) + (f1 x * c2 + f1 x * c2)) +
       (f1 u * f2 x + f1 u * f2 x) + (f1 u * f2 u + f1 u * f2 u) +
       (f1 u * c2 + f1 u * c2) + (f1 v * f2 x + f1 v * f2 x) +
       (f1 v * f2 v + f1 v * f2 v) + (f1 v * c2 + f1 v * c2) +
       ((c1 * f2 x + c1 * f2 x) + (c1 * f2 x + c1 * f2 x)) +
       (c1 * f2 u + c1 * f2 u) + (c1 * f2 v + c1 * f2 v) +
       ((c1 * c2 + c1 * c2) + (c1 * c2 + c1 * c2))) := by ring
  rw [this]; simp [h2]

lemma cover_sum_ge_two {k : ℕ} {E : Finset (S k)} {a : S k} (ha : a ∈ E)
    (hd : 0 < Module.finrank F (Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))))
    (z : S k → ℝ)
    (hcut : ∀ (l : S k) (b : F),
      (E.filter (fun s => dotProduct l s ≠ b)).Nonempty →
      E.filter (fun s => dotProduct l s ≠ b) ≠ E →
      1 ≤ ∑ s ∈ E.filter (fun s => dotProduct l s ≠ b), z s) :
    2 ≤ ∑ s ∈ E, z s := by
  have hne_bot : Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k))) ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hd; omega
  have hex : ∃ s1 ∈ E, s1 ≠ a := by
    by_contra hall; push Not at hall
    apply hne_bot; rw [Submodule.span_eq_bot]
    intro v hv; obtain ⟨s, hs, rfl⟩ := hv; simp [hall s hs]
  obtain ⟨s1, hs1E, hs1ne⟩ := hex
  have hex_j : ∃ j : Fin k, s1 j ≠ a j := by
    by_contra hall; push Not at hall; exact hs1ne (funext hall)
  obtain ⟨j, hj⟩ := hex_j
  let l : S k := Pi.single j 1
  let b0 : F := a j
  have hdot : ∀ s : S k, dotProduct l s = s j := fun s => by simp [l, dotProduct, Pi.single_apply]
  let B0 := E.filter (fun s => dotProduct l s ≠ b0)
  let B1 := E.filter (fun s => dotProduct l s ≠ b0 + 1)
  have hB0_ne : B0.Nonempty := ⟨s1, Finset.mem_filter.mpr ⟨hs1E, by rw [hdot]; exact hj⟩⟩
  have hB0_prop : B0 ≠ E := by
    intro heq
    have := (Finset.mem_filter.mp (heq ▸ ha)).2
    rw [hdot] at this; exact this rfl
  have hB1_ne : B1.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, by
    rw [hdot]; intro h; have := congrArg (· + b0) h
    simp only [b0, f_add_self] at this
    rw [add_comm b0 1, add_assoc, f_add_self, add_zero] at this
    exact f_one_ne_zero this.symm⟩⟩
  have hB1_prop : B1 ≠ E := by
    intro heq
    have hns := (Finset.mem_filter.mp (heq ▸ hs1E)).2
    rw [hdot] at hns; apply hns
    rcases f_cases (s1 j) with h1 | h1 <;> rcases f_cases (a j) with h2 | h2
    · exact absurd (h1.trans h2.symm) hj
    · simp [b0, h1, h2]; decide
    · simp [b0, h1, h2]
    · exact absurd (h1.trans h2.symm) hj
  have hdisj : Disjoint B0 B1 := by
    rw [Finset.disjoint_left]; intro s h0 h1
    have e0 := (Finset.mem_filter.mp h0).2
    have e1 := (Finset.mem_filter.mp h1).2
    rcases f_cases (dotProduct l s) with hx | hx <;> rcases f_cases b0 with hb | hb <;>
      simp [hx, hb] at e0 e1
    all_goals exact e1 (by decide)
  have hunion : B0 ∪ B1 = E := by
    ext s; simp only [B0, B1, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases he : dotProduct l s = b0
      · right; refine ⟨h, ?_⟩
        rw [he]; intro h'; have := congrArg (· + b0) h'
        rw [f_add_self, add_comm b0 1, add_assoc, f_add_self, add_zero] at this
        exact f_one_ne_zero this.symm
      · exact Or.inl ⟨h, he⟩
  have hsum : ∑ s ∈ E, z s = (∑ s ∈ B0, z s) + (∑ s ∈ B1, z s) := by
    rw [← hunion, Finset.sum_union hdisj]
  linarith [hcut l b0 hB0_ne hB0_prop, hcut l (b0 + 1) hB1_ne hB1_prop]

lemma branch_slice_card {n : ℕ} (B : Branch n) (y : Fin n → F) :
    (B.slice y).card * 2 ^ B.pX = 2 ^ n := by
  let μ : Fin B.pX → ((Fin n → F) →ₗ[F] F) := fun j =>
    { toFun := fun x => dotProduct (B.u j) x
      map_add' := fun x1 x2 => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hμ : LinearIndependent F μ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply Fintype.linearIndependent_iff.mp B.hu c
    ext i
    have h := congrFun (congrArg DFunLike.coe hc) (Pi.single i 1)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, μ,
      LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Finset.sum_apply, Pi.smul_apply] at h ⊢
    simpa [dotProduct, Pi.single_apply] using h
  have hsurj := linearMap_surjective_of_li μ hμ
  have hcard := card_filter_linear_eq (LinearMap.pi μ) hsurj (fun j => (B.rhs j).eval B.slp y)
  have heq : B.slice y = Finset.univ.filter (fun x => LinearMap.pi μ x = fun j => (B.rhs j).eval B.slp y) := by
    ext x; simp [Branch.slice, LinearMap.pi_apply, μ, funext_iff]
  rw [heq, hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma wbranch_slice_card {k m r pY : ℕ} (τ : WBranch k m r pY) (s : S k) :
    (τ.slice s).card * 2 ^ τ.tW = 2 ^ (2 * m + r) := by
  have hsurj := linearMap_surjective_of_li τ.μ τ.hμ
  have hcard := card_filter_linear_eq (LinearMap.pi τ.μ) hsurj (fun j => τ.ρ j s)
  have heq : τ.slice s = Finset.univ.filter (fun w => LinearMap.pi τ.μ w = fun j => τ.ρ j s) := by
    ext w; simp [WBranch.slice, LinearMap.pi_apply, funext_iff]
  rw [heq, hcard]
  simp only [Wfull, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_add, ← pow_add]; congr 1; omega

lemma circuit_cover_bound_wbranch {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r) (A : Fin m → S k) (h : S k → F)
    (E : Finset (S k)) (a : S k) (ha : a ∈ E)
    (z : S k → ℝ) (hz_nn : ∀ s ∈ E, 0 ≤ z s)
    (hz_var : ∀ (i : Fin m) (b : F), (E.filter (fun s => dotProduct (A i) s ≠ b)).Nonempty →
      E.filter (fun s => dotProduct (A i) s ≠ b) ≠ E →
      2 ≤ ∑ s ∈ E.filter (fun s => dotProduct (A i) s ≠ b), z s)
    (B : Branch (k + 2 * m + r)) (aB : V k m r) (ψ0 : YAff (k + 2 * m + r) B.pY)
    (ξ : V k m r →ₗ[F] (Fin B.pX → F))
    (hpY_lt : B.pY < ((Finset.univ : Finset (Fin m)).filter (fun i =>
      ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)).card)
    (τ : WBranch k m r B.pY) (hτv : WBranchValid e B.slp τ) :
    ((τ.slice 0).card : ℝ) ≤
      ∑ s ∈ E, z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s,
        sign (ψ0.eval B.slp (e.symm (s, w)) +
          (∑ j : Fin B.pX, ξ (aB + e.symm (s, w)) j * (B.rhs j).eval B.slp (e.symm (s, w))) +
          (h s + ∑ i : Fin m, dotProduct (A i) s * w.1 i * w.2.1 i))) := by
  classical
  set varSet := (Finset.univ : Finset (Fin m)).filter (fun i =>
    ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)
  let Φ : S k → Wfull m r → F := fun s w => h s + ∑ i : Fin m, dotProduct (A i) s * w.1 i * w.2.1 i
  let Θ (s : S k) (w : Wfull m r) : F :=
    ψ0.eval B.slp (e.symm (s, w)) +
    (∑ j : Fin B.pX, ξ (aB + e.symm (s, w)) j * (B.rhs j).eval B.slp (e.symm (s, w))) + Φ s w
  have hcτ_eq : ∀ s : S k, (τ.slice s).card = (τ.slice 0).card := fun s =>
    Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ τ.tW)
      ((wbranch_slice_card τ s).trans (wbranch_slice_card τ 0).symm)
  let Kτ : Submodule F (Wfull m r) := LinearMap.ker (LinearMap.pi τ.μ)
  let ι : ((varSet → F) × (varSet → F)) →ₗ[F] Wfull m r :=
    { toFun := fun p => (fun i => if hi : i ∈ varSet then p.1 ⟨i, hi⟩ else 0,
                        (fun i => if hi : i ∈ varSet then p.2 ⟨i, hi⟩ else 0, 0))
      map_add' := fun p1 p2 => by
        apply Prod.ext
        · ext i; by_cases hi : i ∈ varSet <;> simp [hi]
        · apply Prod.ext
          · ext i; by_cases hi : i ∈ varSet <;> simp [hi]
          · simp
      map_smul' := fun c p => by
        apply Prod.ext
        · ext i; by_cases hi : i ∈ varSet <;> simp [hi]
        · apply Prod.ext
          · ext i; by_cases hi : i ∈ varSet <;> simp [hi]
          · simp }
  let WI : Submodule F ((varSet → F) × (varSet → F)) := Kτ.comap ι
  have hWI_dim : varSet.card < Module.finrank F WI := by
    let Mcomp : ((varSet → F) × (varSet → F)) →ₗ[F] (Fin τ.tW → F) :=
      (LinearMap.pi τ.μ).comp ι
    have hker_eq : WI = LinearMap.ker Mcomp := by
      ext p; simp [WI, Kτ, Mcomp]
    have hrk := LinearMap.finrank_range_add_finrank_ker Mcomp
    have hdom : Module.finrank F ((varSet → F) × (varSet → F)) = 2 * varSet.card := by
      rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_coe]; omega
    have hrle : Module.finrank F (LinearMap.range Mcomp) ≤ τ.tW := by
      have := Submodule.finrank_le (LinearMap.range Mcomp)
      simpa [Module.finrank_fin_fun] using this
    have htW_le : τ.tW ≤ B.pY := τ.htW
    rw [hker_eq]
    omega
  obtain ⟨i0, hi0, uI, huI, vI, hvI, hhad⟩ := exists_hadamard_unit varSet WI hWI_dim
  let u : Wfull m r := ι uI
  let v : Wfull m r := ι vI
  have huK : u ∈ Kτ := huI
  have hvK : v ∈ Kτ := hvI
  have hstep_u : ∀ s w, w ∈ τ.slice s → w + u ∈ τ.slice s := by
    intro s w hw
    simp only [WBranch.slice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro j
    have hu0 : τ.μ j u = 0 := congrFun (LinearMap.mem_ker.mp huK) j
    rw [map_add, hw j, hu0, add_zero]
  have hstep_v : ∀ s w, w ∈ τ.slice s → w + v ∈ τ.slice s := by
    intro s w hw
    simp only [WBranch.slice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro j
    have hv0 : τ.μ j v = 0 := congrFun (LinearMap.mem_ker.mp hvK) j
    rw [map_add, hw j, hv0, add_zero]
  let ξW (j : Fin B.pX) : Wfull m r →ₗ[F] F :=
    { toFun := fun w => ξ (e.symm (0, w)) j
      map_add' := fun w1 w2 => by
        have : ((0 : S k), w1 + w2) = (0, w1) + (0, w2) := by apply Prod.ext <;> simp
        rw [this, map_add, map_add, Pi.add_apply]
      map_smul' := fun c w => by
        have : ((0 : S k), c • w) = c • (0, w) := by apply Prod.ext <;> simp
        rw [this, map_smul, map_smul, Pi.smul_apply, RingHom.id_apply] }
  let rhsW (j : Fin B.pX) : Wfull m r →ₗ[F] F :=
    { toFun := fun w => dotProduct (B.rhs j).lin (e.symm (0, w)) + ∑ q, (B.rhs j).wt q * τ.Λ q w
      map_add' := fun w1 w2 => by
        have : ((0 : S k), w1 + w2) = (0, w1) + (0, w2) := by apply Prod.ext <;> simp
        rw [this, map_add, dotProduct_add]
        simp only [map_add, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c w => by
        have : ((0 : S k), c • w) = c • (0, w) := by apply Prod.ext <;> simp
        rw [this, map_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply]
        simp only [map_smul, smul_eq_mul, mul_add, Finset.mul_sum]; congr 1
        apply Finset.sum_congr rfl; intro q _; ring }
  let ψ0W : Wfull m r →ₗ[F] F :=
    { toFun := fun w => dotProduct ψ0.lin (e.symm (0, w)) + ∑ q, ψ0.wt q * τ.Λ q w
      map_add' := fun w1 w2 => by
        have : ((0 : S k), w1 + w2) = (0, w1) + (0, w2) := by apply Prod.ext <;> simp
        rw [this, map_add, dotProduct_add]
        simp only [map_add, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c w => by
        have : ((0 : S k), c • w) = c • (0, w) := by apply Prod.ext <;> simp
        rw [this, map_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply]
        simp only [map_smul, smul_eq_mul, mul_add, Finset.mul_sum]; congr 1
        apply Finset.sum_congr rfl; intro q _; ring }
  let β : F := ∑ j : Fin B.pX, (ξW j u * rhsW j v + ξW j v * rhsW j u)
  have hΘ_quad : ∀ s w, w ∈ τ.slice s →
      Θ s (w + u + v) + Θ s (w + u) + Θ s (w + v) + Θ s w = β + dotProduct (A i0) s := by
    intro s w hw
    have hwu : w + u ∈ τ.slice s := hstep_u s w hw
    have hwv : w + v ∈ τ.slice s := hstep_v s w hw
    have hwuv : w + u + v ∈ τ.slice s := hstep_v s (w + u) hwu
    let ψ0C : F := ψ0.cst + dotProduct ψ0.lin (e.symm (s, 0)) + ∑ q, ψ0.wt q * τ.σ q s
    have hψ0_eq : ∀ w', w' ∈ τ.slice s → ψ0.eval B.slp (e.symm (s, w')) = ψ0W w' + ψ0C := by
      intro w' hw'
      have hsum : ∑ q, ψ0.wt q * B.slp.eval (e.symm (s, w')) q =
          (∑ q, ψ0.wt q * τ.Λ q w') + (∑ q, ψ0.wt q * τ.σ q s) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro q _; rw [hτv s w' hw' q]; ring
      have hd' : (s, w') = (s, 0) + (0, w') := by apply Prod.ext <;> simp
      simp only [YAff.eval]
      rw [hsum, hd', map_add, dotProduct_add]
      simp only [ψ0W, ψ0C, LinearMap.coe_mk, AddHom.coe_mk]; ring
    let ξC (j : Fin B.pX) : F := ξ (aB + e.symm (s, 0)) j
    have hξ_eq : ∀ j w', ξ (aB + e.symm (s, w')) j = ξW j w' + ξC j := by
      intro j w'
      have hd' : e.symm (s, w') = e.symm (s, 0) + e.symm (0, w') := by
        rw [← map_add]; congr 1; apply Prod.ext <;> simp
      rw [hd', ← add_assoc, map_add, Pi.add_apply, add_comm]; rfl
    let rhsC (j : Fin B.pX) : F :=
      (B.rhs j).cst + dotProduct (B.rhs j).lin (e.symm (s, 0)) + ∑ q, (B.rhs j).wt q * τ.σ q s
    have hrhs_eq : ∀ j w', w' ∈ τ.slice s →
        (B.rhs j).eval B.slp (e.symm (s, w')) = rhsW j w' + rhsC j := by
      intro j w' hw'
      have hsum : ∑ q, (B.rhs j).wt q * B.slp.eval (e.symm (s, w')) q =
          (∑ q, (B.rhs j).wt q * τ.Λ q w') + (∑ q, (B.rhs j).wt q * τ.σ q s) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro q _; rw [hτv s w' hw' q]; ring
      have hd' : (s, w') = (s, 0) + (0, w') := by apply Prod.ext <;> simp
      simp only [YAff.eval]
      rw [hsum, hd', map_add, dotProduct_add]
      simp only [rhsW, rhsC, LinearMap.coe_mk, AddHom.coe_mk]; ring
    have hq1 : ψ0.eval B.slp (e.symm (s, w + u + v)) + ψ0.eval B.slp (e.symm (s, w + u)) +
        ψ0.eval B.slp (e.symm (s, w + v)) + ψ0.eval B.slp (e.symm (s, w)) = 0 := by
      rw [hψ0_eq _ hwuv, hψ0_eq _ hwu, hψ0_eq _ hwv, hψ0_eq _ hw]
      exact quad_diff_aff ψ0W ψ0C w u v
    have hq2 : (∑ j : Fin B.pX, ξ (aB + e.symm (s, w + u + v)) j * (B.rhs j).eval B.slp (e.symm (s, w + u + v))) +
        (∑ j : Fin B.pX, ξ (aB + e.symm (s, w + u)) j * (B.rhs j).eval B.slp (e.symm (s, w + u))) +
        (∑ j : Fin B.pX, ξ (aB + e.symm (s, w + v)) j * (B.rhs j).eval B.slp (e.symm (s, w + v))) +
        (∑ j : Fin B.pX, ξ (aB + e.symm (s, w)) j * (B.rhs j).eval B.slp (e.symm (s, w))) = β := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hξ_eq j (w + u + v), hξ_eq j (w + u), hξ_eq j (w + v), hξ_eq j w,
          hrhs_eq j (w + u + v) hwuv, hrhs_eq j (w + u) hwu,
          hrhs_eq j (w + v) hwv, hrhs_eq j w hw]
      exact quad_diff_mul (ξW j) (rhsW j) (ξC j) (rhsC j) w u v
    have hq3 : Φ s (w + u + v) + Φ s (w + u) + Φ s (w + v) + Φ s w = dotProduct (A i0) s := by
      have hΦ_term : ∀ i : Fin m,
          dotProduct (A i) s * (w + u + v).1 i * (w + u + v).2.1 i +
          dotProduct (A i) s * (w + u).1 i * (w + u).2.1 i +
          dotProduct (A i) s * (w + v).1 i * (w + v).2.1 i +
          dotProduct (A i) s * w.1 i * w.2.1 i =
          dotProduct (A i) s * (u.1 i * v.2.1 i + u.2.1 i * v.1 i) := by
        intro i
        let fB : Wfull m r →ₗ[F] F :=
          { toFun := fun z => z.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        let fC : Wfull m r →ₗ[F] F :=
          { toFun := fun z => z.2.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        have hdm := quad_diff_mul fB fC 0 0 w u v
        simp only [fB, fC, LinearMap.coe_mk, AddHom.coe_mk, add_zero] at hdm
        calc dotProduct (A i) s * (w + u + v).1 i * (w + u + v).2.1 i +
              dotProduct (A i) s * (w + u).1 i * (w + u).2.1 i +
              dotProduct (A i) s * (w + v).1 i * (w + v).2.1 i +
              dotProduct (A i) s * w.1 i * w.2.1 i
            = dotProduct (A i) s *
              ((w + u + v).1 i * (w + u + v).2.1 i + (w + u).1 i * (w + u).2.1 i +
               (w + v).1 i * (w + v).2.1 i + w.1 i * w.2.1 i) := by ring
          _ = dotProduct (A i) s * (u.1 i * v.2.1 i + v.1 i * u.2.1 i) := by rw [hdm]
          _ = dotProduct (A i) s * (u.1 i * v.2.1 i + u.2.1 i * v.1 i) := by ring
      have hhs : h s + h s + h s + h s = 0 := by
        rw [show h s + h s + h s + h s = (h s + h s) + (h s + h s) by ring, f_add_self]
      simp only [Φ]
      have hgrp :
          (h s + ∑ i, dotProduct (A i) s * (w + u + v).1 i * (w + u + v).2.1 i) +
          (h s + ∑ i, dotProduct (A i) s * (w + u).1 i * (w + u).2.1 i) +
          (h s + ∑ i, dotProduct (A i) s * (w + v).1 i * (w + v).2.1 i) +
          (h s + ∑ i, dotProduct (A i) s * w.1 i * w.2.1 i) =
          (h s + h s + h s + h s) +
          ∑ i, (dotProduct (A i) s * (w + u + v).1 i * (w + u + v).2.1 i +
                dotProduct (A i) s * (w + u).1 i * (w + u).2.1 i +
                dotProduct (A i) s * (w + v).1 i * (w + v).2.1 i +
                dotProduct (A i) s * w.1 i * w.2.1 i) := by
        simp only [Finset.sum_add_distrib]; ring
      rw [hgrp, hhs, zero_add]
      simp_rw [hΦ_term]
      have hval_i : ∀ i : Fin m,
          dotProduct (A i) s * (u.1 i * v.2.1 i + u.2.1 i * v.1 i) =
            if i = i0 then dotProduct (A i0) s else 0 := by
        intro i
        by_cases hi : i ∈ varSet
        · have hh := hhad ⟨i, hi⟩
          have hu1 : u.1 i = uI.1 ⟨i, hi⟩ := by simp [u, ι, hi]
          have hu2 : u.2.1 i = uI.2 ⟨i, hi⟩ := by simp [u, ι, hi]
          have hv1 : v.1 i = vI.1 ⟨i, hi⟩ := by simp [v, ι, hi]
          have hv2 : v.2.1 i = vI.2 ⟨i, hi⟩ := by simp [v, ι, hi]
          rw [hu1, hu2, hv1, hv2, hh]
          by_cases heq : i = i0
          · subst heq; simp
          · simp [heq]
        · have hne : i ≠ i0 := fun heq => hi (heq ▸ hi0)
          simp [u, v, ι, hi, hne]
      simp_rw [hval_i]
      simp
    calc Θ s (w + u + v) + Θ s (w + u) + Θ s (w + v) + Θ s w
        = (ψ0.eval B.slp (e.symm (s, w + u + v)) + ψ0.eval B.slp (e.symm (s, w + u)) +
           ψ0.eval B.slp (e.symm (s, w + v)) + ψ0.eval B.slp (e.symm (s, w))) +
          ((∑ j, ξ (aB + e.symm (s, w + u + v)) j * (B.rhs j).eval B.slp (e.symm (s, w + u + v))) +
           (∑ j, ξ (aB + e.symm (s, w + u)) j * (B.rhs j).eval B.slp (e.symm (s, w + u))) +
           (∑ j, ξ (aB + e.symm (s, w + v)) j * (B.rhs j).eval B.slp (e.symm (s, w + v))) +
           (∑ j, ξ (aB + e.symm (s, w)) j * (B.rhs j).eval B.slp (e.symm (s, w)))) +
          (Φ s (w + u + v) + Φ s (w + u) + Φ s (w + v) + Φ s w) := by
            simp only [Θ]; ring
      _ = 0 + β + dotProduct (A i0) s := by rw [hq1, hq2, hq3]
      _ = β + dotProduct (A i0) s := by rw [zero_add]
  let sideI := E.filter (fun s => dotProduct (A i0) s ≠ β)
  have hside_ne : sideI.Nonempty := by
    obtain ⟨s1, hs1E, hs1ne⟩ := (Finset.mem_filter.mp hi0).2
    by_cases h1 : dotProduct (A i0) s1 ≠ β
    · exact ⟨s1, Finset.mem_filter.mpr ⟨hs1E, h1⟩⟩
    · push Not at h1
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, fun ha' => hs1ne (h1.trans ha'.symm)⟩⟩
  have hside_prop : sideI ≠ E := by
    obtain ⟨s1, hs1E, hs1ne⟩ := (Finset.mem_filter.mp hi0).2
    intro heq
    have ha' := (Finset.mem_filter.mp (heq ▸ ha)).2
    have hs1' := (Finset.mem_filter.mp (heq ▸ hs1E)).2
    rcases f_cases (dotProduct (A i0) a) with h1 | h1 <;>
    rcases f_cases (dotProduct (A i0) s1) with h2 | h2 <;>
    rcases f_cases β with h3 | h3
    all_goals first | exact hs1ne (h2.trans h1.symm) | exact ha' (h1.trans h3.symm) | exact hs1' (h2.trans h3.symm)
  have hmass2 : 2 ≤ ∑ s ∈ sideI, z s := hz_var i0 β hside_ne hside_prop
  have hτ_le_all : ∀ s ∈ E, 0 ≤ z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)) := by
    intro s hs
    refine mul_nonneg (hz_nn s hs) (sub_nonneg.mpr ?_)
    calc ∑ w ∈ τ.slice s, sign (Θ s w) ≤ ∑ _w ∈ τ.slice s, (1 : ℝ) :=
          Finset.sum_le_sum fun w _ => sign_le_one _
      _ = ((τ.slice s).card : ℝ) := by simp
      _ = ((τ.slice 0).card : ℝ) := by rw [hcτ_eq]
  have hτ_half : ∀ s ∈ sideI,
      ((τ.slice 0).card : ℝ) / 2 ≤ ((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w) := by
    intro s hs
    have hne : dotProduct (A i0) s ≠ β := (Finset.mem_filter.mp hs).2
    have h4 : ∀ w ∈ τ.slice s, Θ s (w + u + v) + Θ s (w + u) + Θ s (w + v) + Θ s w = 1 := by
      intro w hw
      rw [hΘ_quad s w hw, add_comm]
      exact (f_ne_iff_add_eq_one _ _).mp hne
    have hbd := sum_sign_four_point (τ.slice s) (Θ s) u v (hstep_u s) (hstep_v s) h4
    rw [hcτ_eq s] at hbd
    linarith
  calc ((τ.slice 0).card : ℝ)
      = (((τ.slice 0).card : ℝ) / 2) * 2 := by ring
    _ ≤ (((τ.slice 0).card : ℝ) / 2) * ∑ s ∈ sideI, z s :=
        mul_le_mul_of_nonneg_left hmass2 (by positivity)
    _ = ∑ s ∈ sideI, z s * (((τ.slice 0).card : ℝ) / 2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    _ ≤ ∑ s ∈ sideI, z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)) :=
        Finset.sum_le_sum fun s hs =>
          mul_le_mul_of_nonneg_left (hτ_half s hs) (hz_nn s (Finset.mem_filter.mp hs).1)
    _ ≤ ∑ s ∈ E, z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun s hs _ => hτ_le_all s hs)

lemma circuit_cover_bound {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r) (A : Fin m → S k) (h : S k → F)
    (E : Finset (S k)) (a : S k) (ha : a ∈ E)
    (hd : 0 < Module.finrank F (Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))))
    (C : Circuit) (hlegal : ReadsBack (2 * (k + 2 * m + r)) C ∧ ∀ g ∈ C.gates, gateLegal g)
    (hcost : circuitCost C ≤ (2 * m + r) +
      Module.finrank F (Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))) +
      ((Finset.univ : Finset (Fin m)).filter (fun i => ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)).card - 1)
    (z : S k → ℝ)
    (hz_nn : ∀ s ∈ E, 0 ≤ z s)
    (hz_cut : ∀ (l : S k) (b : F), (E.filter (fun s => dotProduct l s ≠ b)).Nonempty →
      E.filter (fun s => dotProduct l s ≠ b) ≠ E →
      1 ≤ ∑ s ∈ E.filter (fun s => dotProduct l s ≠ b), z s)
    (hz_var : ∀ (i : Fin m) (b : F), (E.filter (fun s => dotProduct (A i) s ≠ b)).Nonempty →
      E.filter (fun s => dotProduct (A i) s ≠ b) ≠ E →
      2 ≤ ∑ s ∈ E.filter (fun s => dotProduct (A i) s ≠ b), z s) :
    1 ≤ ∑ s ∈ E, z s * (1 -
      (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
        let y := e.symm (s, (b, (c, zv)))
        let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
        if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
        then (1 : ℝ) else -1) / 2 ^ ((k + 2 * m + r) + (2 * m + r))) := by
  classical
  set n := k + 2 * m + r
  set base := 2 * m + r
  set W := Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))
  set d := Module.finrank F W
  set varSet := (Finset.univ : Finset (Fin m)).filter (fun i =>
    ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)
  set varying := varSet.card
  let Φ : S k → Wfull m r → F := fun s w => h s + ∑ i : Fin m, dotProduct (A i) s * w.1 i * w.2.1 i
  have hsum_z_ge2 : 2 ≤ ∑ s ∈ E, z s := cover_sum_ge_two ha hd z hz_cut
  obtain ⟨bs, hbs_cost, hbs_valid, hbs_part⟩ := stage1_decomp n C.gates hlegal.2
  have hcB_eq : ∀ B : Branch n, ∀ y : V k m r, (B.slice y).card = (B.slice 0).card := by
    intro B y
    have h1 := branch_slice_card B y
    have h2 := branch_slice_card B 0
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ B.pX) (h1.trans h2.symm)
  have hsum_cB : (bs.map (fun B => ((B.slice 0).card : ℝ))).sum = (2 : ℝ) ^ n := by
    have hp := hbs_part 0 (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fun, ZMod.card, Fintype.card_fin] at hp
    simpa [Nat.cast_pow] using hp.symm
  let branchSum (B : Branch n) (s : S k) : ℝ :=
    ∑ w : Wfull m r, ∑ x ∈ B.slice (e.symm (s, w)),
      sign (dotProduct ((B.wires C.output).1 + e.symm (s, w)) x +
        (B.wires C.output).2.eval B.slp (e.symm (s, w)) + Φ s w)
  have hscore_decomp : ∀ s : S k,
      (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
        let y := e.symm (s, (b, (c, zv)))
        let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (v = 1) then (1 : ℝ) else -1) =
      (bs.map (fun B => branchSum B s)).sum := by
    intro s
    have h1 : (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
        let y := e.symm (s, (b, (c, zv)))
        let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (v = 1) then (1 : ℝ) else -1) =
        ∑ w : Wfull m r, ∑ x : V k m r,
          sign (b2f (C.eval (bitsOf n x ++ bitsOf n (e.symm (s, w)))) +
            (dotProduct x (e.symm (s, w)) + Φ s w)) := by
      rw [Finset.sum_comm]
      have hprod : ∀ f : Wfull m r → ℝ,
          ∑ w : Wfull m r, f w = ∑ b : D m, ∑ c : D m, ∑ zv : Z r, f (b, (c, zv)) := by
        intro f; rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro b _; rw [Fintype.sum_prod_type]
      rw [hprod]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro zv _
      apply Finset.sum_congr rfl; intro x _
      rw [ite_eq_sign]; congr 1; simp only [Φ, add_assoc]
    rw [h1]
    have h2 : ∀ w : Wfull m r,
        ∑ x : V k m r, sign (b2f (C.eval (bitsOf n x ++ bitsOf n (e.symm (s, w)))) +
          (dotProduct x (e.symm (s, w)) + Φ s w)) =
        (bs.map (fun B => ∑ x ∈ B.slice (e.symm (s, w)),
          sign (dotProduct ((B.wires C.output).1 + e.symm (s, w)) x +
            (B.wires C.output).2.eval B.slp (e.symm (s, w)) + Φ s w))).sum := by
      intro w
      rw [hbs_part (e.symm (s, w))]
      congr 1; apply List.map_congr_left; intro B hB
      apply Finset.sum_congr rfl; intro x hx
      have hev := hbs_valid B hB x (e.symm (s, w)) hx C.output
      have hCev : b2f (C.eval (bitsOf n x ++ bitsOf n (e.symm (s, w)))) =
          dotProduct (B.wires C.output).1 x + (B.wires C.output).2.eval B.slp (e.symm (s, w)) := hev
      rw [hCev, add_dotProduct, dotProduct_comm x (e.symm (s, w))]
      congr 1; ring
    simp_rw [h2]
    have hsum_map : ∀ (l : List (Branch n)) (f : Branch n → Wfull m r → ℝ),
        (∑ w : Wfull m r, (l.map (fun B => f B w)).sum) =
        (l.map (fun B => ∑ w : Wfull m r, f B w)).sum := by
      intro l f; induction l with
      | nil => simp
      | cons B rest ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    exact hsum_map bs (fun B w => ∑ x ∈ B.slice (e.symm (s, w)),
      sign (dotProduct ((B.wires C.output).1 + e.symm (s, w)) x +
        (B.wires C.output).2.eval B.slp (e.symm (s, w)) + Φ s w))
  have hbranch_bound : ∀ B ∈ bs,
      ((B.slice 0).card : ℝ) * (2 : ℝ) ^ base ≤
        ∑ s ∈ E, z s * (((B.slice 0).card : ℝ) * (2 : ℝ) ^ base - branchSum B s) := by
    intro B hB
    set aB := (B.wires C.output).1
    set ψ0 := (B.wires C.output).2
    set U : Submodule F (V k m r) := Submodule.span F (Set.range B.u)
    set cB : ℝ := ((B.slice 0).card : ℝ)
    have hcB_nn : 0 ≤ cB := Nat.cast_nonneg _
    let Xsum (s : S k) (w : Wfull m r) : ℝ :=
      ∑ x ∈ B.slice (e.symm (s, w)),
        sign (dotProduct (aB + e.symm (s, w)) x + ψ0.eval B.slp (e.symm (s, w)) + Φ s w)
    have hXsum_le : ∀ s w, Xsum s w ≤ cB := fun s w => by
      calc Xsum s w ≤ ∑ _x ∈ B.slice (e.symm (s, w)), (1 : ℝ) :=
            Finset.sum_le_sum fun x _ => sign_le_one _
        _ = ((B.slice (e.symm (s, w))).card : ℝ) := by simp
        _ = cB := by rw [hcB_eq]
    have hXsum_zero : ∀ s w, e.symm (s, w) + aB ∉ U → Xsum s w = 0 := by
      intro s w hnot
      obtain ⟨v0, hv0U, hv01⟩ := exists_dotProduct_one_of_notMem U (e.symm (s, w) + aB) hnot
      apply sum_sign_of_shift (B.slice (e.symm (s, w))) _ v0
      · intro x hx
        simp only [Branch.slice, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        intro j
        rw [dotProduct_add, hx j, hv0U (B.u j) (Submodule.subset_span ⟨j, rfl⟩), add_zero]
      · intro x _
        rw [dotProduct_add, add_comm aB (e.symm (s, w)), hv01]; ring
    have hbsum_le : ∀ s, branchSum B s ≤ cB * (2 : ℝ) ^ base := fun s => by
      calc branchSum B s = ∑ w : Wfull m r, Xsum s w := rfl
        _ ≤ ∑ _w : Wfull m r, cB := Finset.sum_le_sum fun w _ => hXsum_le s w
        _ = (Fintype.card (Wfull m r) : ℝ) * cB := by simp
        _ = cB * (2 : ℝ) ^ base := by
            simp only [Wfull, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin,
              Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [← pow_add, ← pow_add, mul_comm]; congr 2; omega
    have hterm_nn : ∀ s ∈ E, 0 ≤ z s * (cB * (2 : ℝ) ^ base - branchSum B s) := fun s hs =>
      mul_nonneg (hz_nn s hs) (sub_nonneg.mpr (hbsum_le s))
    by_cases hcover_all : ∀ s ∈ E, ∀ w : Wfull m r, e.symm (s, w) + aB ∈ U
    · have hdimU : d + base ≤ B.pX := by
        have hU_card : Module.finrank F U = B.pX := by
          rw [finrank_span_eq_card B.hu, Fintype.card_fin]
        let Vsub : Submodule F (V k m r) := (W.prod (⊤ : Submodule F (Wfull m r))).map e.symm.toLinearMap
        have hsub : Vsub ≤ U := by
          rintro v ⟨⟨sw, w⟩, ⟨hsw, _⟩, rfl⟩
          have ha0 : e.symm (a, (0 : Wfull m r)) + aB ∈ U := hcover_all a ha 0
          have hw_mem : e.symm (0, w) ∈ U := by
            have h1 := hcover_all a ha w
            have heq : e.symm (0, w) = (e.symm (a, w) + aB) + (e.symm (a, 0) + aB) := by
              have hrearr : (e.symm (a, w) + aB) + (e.symm (a, 0) + aB) =
                  (e.symm (a, w) + e.symm (a, 0)) + (aB + aB) := by abel
              rw [hrearr, vec_add_self, add_zero, ← map_add]
              congr 1; apply Prod.ext
              · simp [vec_add_self]
              · simp
            rw [heq]; exact U.add_mem h1 ha0
          have hsw_mem : e.symm (sw, 0) ∈ U := by
            have hgen : ∀ x ∈ W, e.symm (x, (0 : Wfull m r)) ∈ U := by
              intro x hx
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
              · rintro _ ⟨s, hs, rfl⟩
                have h1 := hcover_all s hs 0
                have heq : e.symm (s - a, (0 : Wfull m r)) = (e.symm (s, 0) + aB) + (e.symm (a, 0) + aB) := by
                  have hrearr : (e.symm (s, 0) + aB) + (e.symm (a, 0) + aB) =
                      (e.symm (s, 0) + e.symm (a, 0)) + (aB + aB) := by abel
                  rw [hrearr, vec_add_self, add_zero, ← map_add]
                  congr 1; apply Prod.ext
                  · ext i; simp [f_sub_eq_add]
                  · simp
                rw [heq]; exact U.add_mem h1 ha0
              · change e.symm 0 ∈ U; rw [map_zero]; exact U.zero_mem
              · intro x1 x2 _ _ h1 h2
                have : (x1 + x2, (0 : Wfull m r)) = (x1, 0) + (x2, 0) := by apply Prod.ext <;> simp
                rw [this, map_add]; exact U.add_mem h1 h2
              · intro c x1 _ h1
                have : (c • x1, (0 : Wfull m r)) = c • (x1, 0) := by apply Prod.ext <;> simp
                rw [this, map_smul]; exact U.smul_mem c h1
            exact hgen sw hsw
          have hsum : (sw, w) = (sw, 0) + (0, w) := by apply Prod.ext <;> simp
          rw [show e.symm.toLinearMap (sw, w) = e.symm (sw, w) from rfl, hsum, map_add]
          exact U.add_mem hsw_mem hw_mem
        have hfinV : Module.finrank F Vsub = d + base := by
          have heqv : (W × Wfull m r) ≃ₗ[F] Vsub :=
            { toFun := fun x => ⟨e.symm (x.1.1, x.2),
                Submodule.mem_map.mpr ⟨(x.1.1, x.2), ⟨x.1.2, trivial⟩, rfl⟩⟩
              invFun := fun y => ⟨⟨(e y.1).1, by
                obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2
                have : e y.1 = x := by rw [← hxy]; exact e.apply_symm_apply x
                rw [this]; exact hx.1⟩, (e y.1).2⟩
              map_add' := fun x1 x2 => by
                apply Subtype.ext; exact map_add e.symm (x1.1.1, x1.2) (x2.1.1, x2.2)
              map_smul' := fun c x => by
                apply Subtype.ext; exact map_smul e.symm c (x.1.1, x.2)
              left_inv := fun ⟨⟨s, hs⟩, w⟩ => by
                have h : e (e.symm (s, w)) = (s, w) := e.apply_symm_apply (s, w)
                dsimp only; apply Prod.ext
                · apply Subtype.ext; dsimp only; rw [h]
                · dsimp only; rw [h]
              right_inv := fun y => by apply Subtype.ext; exact e.symm_apply_apply y.1 }
          rw [← heqv.finrank_eq, Module.finrank_prod]
          simp only [Wfull, Module.finrank_prod, Module.finrank_fin_fun]
          omega
        have hle := Submodule.finrank_mono hsub
        omega
      have hpY_lt : B.pY < varying := by
        have h1 := hbs_cost B hB
        change circuitCost C ≤ base + d + varying - 1 at hcost
        change B.pX + B.pY ≤ circuitCost C at h1
        omega
      let toU : (Fin B.pX → F) →ₗ[F] U :=
        { toFun := fun c => ⟨∑ j : Fin B.pX, c j • B.u j,
            Submodule.sum_mem U fun j _ => U.smul_mem (c j) (Submodule.subset_span ⟨j, rfl⟩)⟩
          map_add' := fun c1 c2 => by
            apply Subtype.ext; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; rfl
          map_smul' := fun r c => by
            apply Subtype.ext; simp only [Pi.smul_apply, smul_eq_mul, mul_smul]; rw [← Finset.smul_sum]; rfl }
      have htoU_inj : Function.Injective toU := by
        intro c1 c2 heq
        have hval : ∑ j : Fin B.pX, c1 j • B.u j = ∑ j : Fin B.pX, c2 j • B.u j :=
          congrArg Subtype.val heq
        have h0 : ∑ j : Fin B.pX, (c1 j + c2 j) • B.u j = 0 := by
          simp only [add_smul, Finset.sum_add_distrib, hval, vec_add_self]
        have hc := Fintype.linearIndependent_iff.mp B.hu (fun j => c1 j + c2 j) h0
        ext j
        have := congrArg (· + c2 j) (hc j)
        simpa [add_assoc, f_add_self] using this
      have htoU_surj : Function.Surjective toU := by
        rintro ⟨v, hv⟩
        refine Submodule.span_induction (p := fun v hv => ∃ c, toU c = ⟨v, hv⟩) ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨j, rfl⟩
          refine ⟨Pi.single j 1, Subtype.ext ?_⟩
          simp [toU, Pi.single_apply]
        · exact ⟨0, Subtype.ext (by simp [toU])⟩
        · intro x y hx hy ⟨c1, hc1⟩ ⟨c2, hc2⟩
          refine ⟨c1 + c2, Subtype.ext ?_⟩
          have h1 : ∑ j, c1 j • B.u j = x := congrArg Subtype.val hc1
          have h2 : ∑ j, c2 j • B.u j = y := congrArg Subtype.val hc2
          simp only [toU, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, add_smul,
            Finset.sum_add_distrib, h1, h2]
        · intro r x hx ⟨c1, hc1⟩
          refine ⟨r • c1, Subtype.ext ?_⟩
          have h1 : ∑ j, c1 j • B.u j = x := congrArg Subtype.val hc1
          simp only [toU, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
            mul_smul, ← Finset.smul_sum, h1]
      let eqU : (Fin B.pX → F) ≃ₗ[F] U := LinearEquiv.ofBijective toU ⟨htoU_inj, htoU_surj⟩
      obtain ⟨KU, hKU⟩ := Submodule.exists_isCompl U
      let ξ : V k m r →ₗ[F] (Fin B.pX → F) := eqU.symm.toLinearMap.comp (Submodule.projectionOnto U KU hKU)
      have hξ_recon : ∀ v ∈ U, ∑ j : Fin B.pX, ξ v j • B.u j = v := by
        intro v hv
        have hproj : Submodule.projectionOnto U KU hKU v = ⟨v, hv⟩ :=
          Submodule.projectionOnto_apply_left hKU ⟨v, hv⟩
        have h1 : eqU (eqU.symm ⟨v, hv⟩) = ⟨v, hv⟩ := eqU.apply_symm_apply ⟨v, hv⟩
        have h2 : ∑ j : Fin B.pX, eqU.symm ⟨v, hv⟩ j • B.u j = v := congrArg Subtype.val h1
        simpa only [ξ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hproj] using h2
      let Θ (s : S k) (w : Wfull m r) : F :=
        ψ0.eval B.slp (e.symm (s, w)) +
        (∑ j : Fin B.pX, ξ (aB + e.symm (s, w)) j * (B.rhs j).eval B.slp (e.symm (s, w))) + Φ s w
      have hXsum_eq : ∀ s ∈ E, ∀ w : Wfull m r, Xsum s w = cB * sign (Θ s w) := by
        intro s hs w
        have hmemU : aB + e.symm (s, w) ∈ U := by
          have heq : aB + e.symm (s, w) = e.symm (s, w) + aB := add_comm _ _
          rw [heq]; exact hcover_all s hs w
        have hconst : ∀ x ∈ B.slice (e.symm (s, w)),
            dotProduct (aB + e.symm (s, w)) x + ψ0.eval B.slp (e.symm (s, w)) + Φ s w = Θ s w := by
          intro x hx
          have hdot : dotProduct (aB + e.symm (s, w)) x =
              ∑ j : Fin B.pX, ξ (aB + e.symm (s, w)) j * (B.rhs j).eval B.slp (e.symm (s, w)) := by
            conv_lhs => rw [← hξ_recon _ hmemU]
            rw [sum_dotProduct]
            apply Finset.sum_congr rfl; intro j _
            rw [smul_dotProduct, smul_eq_mul, (Finset.mem_filter.mp hx).2 j]
          rw [hdot]; simp only [Θ]; ring
        calc Xsum s w = ∑ _x ∈ B.slice (e.symm (s, w)), sign (Θ s w) :=
              Finset.sum_congr rfl fun x hx => by rw [hconst x hx]
          _ = ((B.slice (e.symm (s, w))).card : ℝ) * sign (Θ s w) := by simp
          _ = cB * sign (Θ s w) := by rw [hcB_eq]
      have hbsum_eq : ∀ s ∈ E, branchSum B s = cB * ∑ w : Wfull m r, sign (Θ s w) := fun s hs => by
        simp only [branchSum, Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => hXsum_eq s hs w
      obtain ⟨τs, hτ_val, hτ_part⟩ := stage2_decomp e B.slp
      have hsum_cτ : (τs.map (fun τ => ((τ.slice 0).card : ℝ))).sum = (2 : ℝ) ^ base := by
        have hp := hτ_part 0 (fun _ => (1 : ℝ))
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          Wfull, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin,
          Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hp
        rw [← hp, ← pow_add, ← pow_add]; congr 1; omega
      have hτ_bound : ∀ τ ∈ τs,
          ((τ.slice 0).card : ℝ) ≤
            ∑ s ∈ E, z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)) :=
        fun τ hτ => circuit_cover_bound_wbranch e A h E a ha z hz_nn hz_var B aB ψ0 ξ hpY_lt τ (hτ_val τ hτ)
      have hinner : (2 : ℝ) ^ base ≤ ∑ s ∈ E, z s * ((2 : ℝ) ^ base - ∑ w : Wfull m r, sign (Θ s w)) := by
        have hlist_le_τ : ∀ (l : List (WBranch k m r B.pY)) (f g : WBranch k m r B.pY → ℝ),
            (∀ τ ∈ l, f τ ≤ g τ) → (l.map f).sum ≤ (l.map g).sum := by
          intro l f g hfg; induction l with
          | nil => simp
          | cons τ rest ih =>
            simp only [List.map_cons, List.sum_cons]
            exact add_le_add (hfg τ (by simp)) (ih fun t ht => hfg t (by simp [ht]))
        have hsum_τ : (τs.map (fun τ => ((τ.slice 0).card : ℝ))).sum ≤
            (τs.map (fun τ => ∑ s ∈ E, z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)))).sum :=
          hlist_le_τ τs _ _ hτ_bound
        have hswap_τ :
            (τs.map (fun τ => ∑ s ∈ E, z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)))).sum =
            ∑ s ∈ E, z s * ((2 : ℝ) ^ base - ∑ w : Wfull m r, sign (Θ s w)) := by
          have hcomm : ∀ (l : List (WBranch k m r B.pY)) (f : WBranch k m r B.pY → S k → ℝ),
              (l.map (fun τ => ∑ s ∈ E, f τ s)).sum = ∑ s ∈ E, (l.map (fun τ => f τ s)).sum := by
            intro l f; induction l with
            | nil => simp
            | cons τ rest ih => simp [ih, Finset.sum_add_distrib]
          rw [hcomm]
          apply Finset.sum_congr rfl; intro s _
          have hfac : ∀ l : List (WBranch k m r B.pY),
              (l.map (fun τ => z s * (((τ.slice 0).card : ℝ) - ∑ w ∈ τ.slice s, sign (Θ s w)))).sum =
              z s * ((l.map (fun τ => ((τ.slice 0).card : ℝ))).sum -
                (l.map (fun τ => ∑ w ∈ τ.slice s, sign (Θ s w))).sum) := by
            intro l; induction l with
            | nil => simp
            | cons τ rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
          rw [hfac, hsum_cτ, ← hτ_part s (fun w => sign (Θ s w))]
        rw [← hswap_τ, ← hsum_cτ]; exact hsum_τ
      calc cB * (2 : ℝ) ^ base
          ≤ cB * ∑ s ∈ E, z s * ((2 : ℝ) ^ base - ∑ w : Wfull m r, sign (Θ s w)) :=
            mul_le_mul_of_nonneg_left hinner hcB_nn
        _ = ∑ s ∈ E, z s * (cB * (2 : ℝ) ^ base - branchSum B s) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro s hs
            rw [hbsum_eq s hs]; ring
    · push Not at hcover_all
      obtain ⟨s1, hs1E, w1, hw1not⟩ := hcover_all
      let EB := E.filter (fun s => ∃ w : Wfull m r, e.symm (s, w) + aB ∈ U)
      by_cases hEB_all : EB = E
      · have hEB_mem : ∀ s ∈ E, ∃ w : Wfull m r, e.symm (s, w) + aB ∈ U := by
          intro s hs
          have hsEB : s ∈ EB := hEB_all.symm ▸ hs
          exact (Finset.mem_filter.mp hsEB).2
        let FB : Submodule F (Wfull m r) := U.comap (e.symm.toLinearMap.comp (LinearMap.inr F (S k) (Wfull m r)))
        have hFB_lt : FB < ⊤ := by
          obtain ⟨w0, hw0⟩ := hEB_mem s1 hs1E
          rw [lt_top_iff_ne_top]
          intro htop
          have hmem : w1 + w0 ∈ FB := htop ▸ Submodule.mem_top
          have heq : e.symm (s1, w1) + aB = (e.symm (s1, w0) + aB) + e.symm (0, w1 + w0) := by
            have hrearr : (e.symm (s1, w0) + aB) + e.symm (0, w1 + w0) =
                (e.symm (s1, w0) + e.symm (0, w1 + w0)) + aB := by abel
            rw [hrearr, ← map_add]
            congr 1; congr 1; apply Prod.ext
            · simp
            · change w1 = w0 + (w1 + w0)
              rw [add_comm w1 w0, ← add_assoc, vec_add_self, zero_add]
          exact hw1not (heq ▸ U.add_mem hw0 hmem)
        have hFB_card : 2 * Fintype.card FB ≤ 2 ^ base := by
          have hflt : Module.finrank F FB < base := by
            have h1 := Submodule.finrank_lt_finrank_of_lt hFB_lt
            rw [finrank_top] at h1
            have h2 : Module.finrank F (Wfull m r) = base := by
              simp only [Wfull, Module.finrank_prod, Module.finrank_fin_fun]; omega
            omega
          have hc : Fintype.card FB = 2 ^ Module.finrank F FB := by
            have := Module.card_eq_pow_finrank (K := F) (V := FB); simpa [ZMod.card] using this
          rw [hc]
          calc 2 * 2 ^ Module.finrank F FB = 2 ^ (Module.finrank F FB + 1) := by ring
            _ ≤ 2 ^ base := Nat.pow_le_pow_right (by omega) hflt
        have hbsum_half : ∀ s ∈ E, branchSum B s ≤ cB * ((2 : ℝ) ^ base / 2) := by
          intro s hs
          obtain ⟨ws, hws⟩ := hEB_mem s hs
          let hit := Finset.univ.filter (fun w : Wfull m r => e.symm (s, w) + aB ∈ U)
          have hhit_card : hit.card = Fintype.card FB := by
            rw [← Finset.card_univ]; symm
            apply Finset.card_nbij (fun v : FB => v.1 + ws)
            · intro v _
              rw [Finset.mem_coe, Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have heq : e.symm (s, v.1 + ws) + aB = e.symm (0, v.1) + (e.symm (s, ws) + aB) := by
                rw [← add_assoc, ← map_add]; congr 1; congr 1; apply Prod.ext <;> simp
              rw [heq]; exact U.add_mem v.2 hws
            · intro v1 _ v2 _ heq; apply Subtype.ext
              have := congrArg (· + ws) heq
              simpa only [add_assoc, vec_add_self, add_zero] using this
            · intro w hw
              rw [Finset.mem_coe, Finset.mem_filter] at hw
              have hv : w + ws ∈ FB := by
                change e.symm (0, w + ws) ∈ U
                have heq : e.symm (0, w + ws) = (e.symm (s, w) + aB) + (e.symm (s, ws) + aB) := by
                  have hrearr : (e.symm (s, w) + aB) + (e.symm (s, ws) + aB) =
                      (e.symm (s, w) + e.symm (s, ws)) + (aB + aB) := by abel
                  rw [hrearr, vec_add_self, add_zero, ← map_add]
                  congr 1; apply Prod.ext
                  · simp [vec_add_self]
                  · simp
                rw [heq]; exact U.add_mem hw.2 hws
              refine ⟨⟨w + ws, hv⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
              dsimp only; rw [add_assoc, vec_add_self, add_zero]
          have hsum_hit : branchSum B s = ∑ w ∈ hit, Xsum s w := by
            change ∑ w : Wfull m r, Xsum s w = _
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => e.symm (s, w) + aB ∈ U)]
            have hz0 : ∑ w ∈ Finset.univ.filter (fun w => ¬ e.symm (s, w) + aB ∈ U), Xsum s w = 0 :=
              Finset.sum_eq_zero fun w hw => hXsum_zero s w (Finset.mem_filter.mp hw).2
            rw [hz0, add_zero]
          rw [hsum_hit]
          calc ∑ w ∈ hit, Xsum s w ≤ ∑ _w ∈ hit, cB := Finset.sum_le_sum fun w _ => hXsum_le s w
            _ = (hit.card : ℝ) * cB := by simp
            _ = (Fintype.card FB : ℝ) * cB := by rw [hhit_card]
            _ ≤ ((2 : ℝ) ^ base / 2) * cB := by
                apply mul_le_mul_of_nonneg_right _ hcB_nn
                have : (2 : ℝ) * (Fintype.card FB : ℝ) ≤ (2 : ℝ) ^ base := by exact_mod_cast hFB_card
                linarith
            _ = cB * ((2 : ℝ) ^ base / 2) := mul_comm _ _
        calc cB * (2 : ℝ) ^ base
            = (cB * ((2 : ℝ) ^ base / 2)) * 2 := by ring
          _ ≤ (cB * ((2 : ℝ) ^ base / 2)) * ∑ s ∈ E, z s :=
              mul_le_mul_of_nonneg_left hsum_z_ge2 (by positivity)
          _ = ∑ s ∈ E, z s * (cB * ((2 : ℝ) ^ base / 2)) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
          _ ≤ ∑ s ∈ E, z s * (cB * (2 : ℝ) ^ base - branchSum B s) :=
              Finset.sum_le_sum fun s hs =>
                mul_le_mul_of_nonneg_left (by linarith [hbsum_half s hs]) (hz_nn s hs)
      · have hex_miss : ∃ s2 ∈ E, s2 ∉ EB := by
          by_contra hall; push Not at hall
          apply hEB_all; ext s; simp only [EB, Finset.mem_filter]
          exact ⟨fun h => h.1, fun hs => ⟨hs, (Finset.mem_filter.mp (hall s hs)).2⟩⟩
        obtain ⟨s2, hs2E, hs2not⟩ := hex_miss
        have hzero_out : ∀ s ∈ E, s ∉ EB → branchSum B s = 0 := by
          intro s hs hnot
          have hall : ∀ w : Wfull m r, e.symm (s, w) + aB ∉ U := by
            intro w hw; exact hnot (Finset.mem_filter.mpr ⟨hs, w, hw⟩)
          exact Finset.sum_eq_zero fun w _ => hXsum_zero s w (hall w)
        by_cases hEB_ne : EB.Nonempty
        · obtain ⟨s0, hs0EB⟩ := hEB_ne
          have hs0E : s0 ∈ E := (Finset.mem_filter.mp hs0EB).1
          obtain ⟨w0, hw0U⟩ := (Finset.mem_filter.mp hs0EB).2
          let WB : Submodule F (S k) := U.map (yS e)
          have hs2_not_WB : s2 + s0 ∉ WB := by
            intro hmem
            obtain ⟨u, huU, hueq⟩ := Submodule.mem_map.mp hmem
            have heu : e u = (s2 + s0, (e u).2) := by apply Prod.ext; exact hueq; rfl
            have hu_eq : u = e.symm (s2 + s0, (e u).2) := by
              rw [← heu, LinearEquiv.symm_apply_apply]
            have hsum_U : e.symm (s2, w0 + (e u).2) + aB ∈ U := by
              have heq : e.symm (s2, w0 + (e u).2) + aB = (e.symm (s0, w0) + aB) + u := by
                set wu := (e u).2
                have hu_eq' : u = e.symm (s2 + s0, wu) := hu_eq
                have hrearr : (e.symm (s0, w0) + aB) + u =
                    (e.symm (s0, w0) + e.symm (s2 + s0, wu)) + aB := by
                  rw [hu_eq']; abel
                rw [hrearr, ← map_add]
                congr 1; congr 1; apply Prod.ext
                · change s2 = s0 + (s2 + s0)
                  rw [add_comm s2 s0, ← add_assoc, vec_add_self, zero_add]
                · rfl
              rw [heq]; exact U.add_mem hw0U huU
            exact hs2not (Finset.mem_filter.mpr ⟨hs2E, w0 + (e u).2, hsum_U⟩)
          obtain ⟨l, hlWB, hl1⟩ := exists_dotProduct_one_of_notMem WB (s2 + s0) hs2_not_WB
          let b0 := dotProduct l s0
          let sideL := E.filter (fun s => dotProduct l s ≠ b0)
          have hsideL_ne : sideL.Nonempty := ⟨s2, Finset.mem_filter.mpr ⟨hs2E, fun h => by
            have h1 : dotProduct (s2 + s0) l = 0 := by
              rw [add_dotProduct, dotProduct_comm s2 l, dotProduct_comm s0 l, h, f_add_self]
            rw [hl1] at h1; exact f_one_ne_zero h1⟩⟩
          have hsideL_prop : sideL ≠ E := by
            intro heq
            have hs0 : s0 ∈ sideL := heq.symm ▸ hs0E
            exact (Finset.mem_filter.mp hs0).2 rfl
          have hsideL_miss : ∀ s ∈ sideL, s ∉ EB := by
            intro s hs hEBs
            obtain ⟨w, hwU⟩ := (Finset.mem_filter.mp hEBs).2
            have hmemWB : s + s0 ∈ WB := by
              refine Submodule.mem_map.mpr ⟨(e.symm (s, w) + aB) + (e.symm (s0, w0) + aB),
                U.add_mem hwU hw0U, ?_⟩
              have heq : (e.symm (s, w) + aB) + (e.symm (s0, w0) + aB) = e.symm (s + s0, w + w0) := by
                have hrearr : (e.symm (s, w) + aB) + (e.symm (s0, w0) + aB) =
                    (e.symm (s, w) + e.symm (s0, w0)) + (aB + aB) := by abel
                rw [hrearr, vec_add_self, add_zero, ← map_add]; rfl
              rw [heq]; simp [yS]
            have h0 := hlWB (s + s0) hmemWB
            rw [add_dotProduct, dotProduct_comm s l, dotProduct_comm s0 l] at h0
            have heq : dotProduct l s = b0 := by
              have := congrArg (· + b0) h0
              simpa only [b0, add_assoc, f_add_self, add_zero, zero_add] using this
            exact (Finset.mem_filter.mp hs).2 heq
          calc cB * (2 : ℝ) ^ base
              = (cB * (2 : ℝ) ^ base) * 1 := by ring
            _ ≤ (cB * (2 : ℝ) ^ base) * ∑ s ∈ sideL, z s :=
                mul_le_mul_of_nonneg_left (hz_cut l b0 hsideL_ne hsideL_prop) (by positivity)
            _ = ∑ s ∈ sideL, z s * (cB * (2 : ℝ) ^ base - branchSum B s) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro s hs
                rw [hzero_out s (Finset.mem_filter.mp hs).1 (hsideL_miss s hs), sub_zero]; ring
            _ ≤ ∑ s ∈ E, z s * (cB * (2 : ℝ) ^ base - branchSum B s) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun s hs _ => hterm_nn s hs)
        · have hEB_empty : ∀ s ∈ E, s ∉ EB := fun s _ h => hEB_ne ⟨s, h⟩
          calc cB * (2 : ℝ) ^ base
              ≤ (cB * (2 : ℝ) ^ base) * 2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) base]
            _ ≤ (cB * (2 : ℝ) ^ base) * ∑ s ∈ E, z s :=
                mul_le_mul_of_nonneg_left hsum_z_ge2 (by positivity)
            _ = ∑ s ∈ E, z s * (cB * (2 : ℝ) ^ base - branchSum B s) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro s hs
                rw [hzero_out s hs (hEB_empty s hs), sub_zero]; ring
  have hsum_all : (2 : ℝ) ^ (n + base) ≤
      ∑ s ∈ E, z s * ((2 : ℝ) ^ (n + base) -
        ∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
          let y := e.symm (s, (b, (c, zv)))
          let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
          if C.eval (bitsOf n x ++ bitsOf n y) = decide (v = 1) then (1 : ℝ) else -1) := by
    have hlist_le : ∀ (l : List (Branch n)) (f g : Branch n → ℝ),
        (∀ B ∈ l, f B ≤ g B) → (l.map f).sum ≤ (l.map g).sum := by
      intro l f g hfg; induction l with
      | nil => simp
      | cons B rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (hfg B (by simp)) (ih fun b hb => hfg b (by simp [hb]))
    have hsum_bs : (bs.map (fun B => ((B.slice 0).card : ℝ) * (2 : ℝ) ^ base)).sum ≤
        (bs.map (fun B => ∑ s ∈ E, z s * (((B.slice 0).card : ℝ) * (2 : ℝ) ^ base - branchSum B s))).sum :=
      hlist_le bs _ _ hbranch_bound
    have hlhs : (bs.map (fun B => ((B.slice 0).card : ℝ) * (2 : ℝ) ^ base)).sum = (2 : ℝ) ^ (n + base) := by
      have hmul : ∀ l : List (Branch n),
          (l.map (fun B => ((B.slice 0).card : ℝ) * (2 : ℝ) ^ base)).sum =
          (l.map (fun B => ((B.slice 0).card : ℝ))).sum * (2 : ℝ) ^ base := by
        intro l; induction l with
        | nil => simp
        | cons B rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      rw [hmul, hsum_cB, ← pow_add]
    have hrhs :
        (bs.map (fun B => ∑ s ∈ E, z s * (((B.slice 0).card : ℝ) * (2 : ℝ) ^ base - branchSum B s))).sum =
        ∑ s ∈ E, z s * ((2 : ℝ) ^ (n + base) - (bs.map (fun B => branchSum B s)).sum) := by
      have hcomm : ∀ (l : List (Branch n)) (f : Branch n → S k → ℝ),
          (l.map (fun B => ∑ s ∈ E, f B s)).sum = ∑ s ∈ E, (l.map (fun B => f B s)).sum := by
        intro l f; induction l with
        | nil => simp
        | cons B rest ih => simp [ih, Finset.sum_add_distrib]
      rw [hcomm]
      apply Finset.sum_congr rfl; intro s _
      have hfac : ∀ l : List (Branch n),
          (l.map (fun B => z s * (((B.slice 0).card : ℝ) * (2 : ℝ) ^ base - branchSum B s))).sum =
          z s * ((l.map (fun B => ((B.slice 0).card : ℝ) * (2 : ℝ) ^ base)).sum -
            (l.map (fun B => branchSum B s)).sum) := by
        intro l; induction l with
        | nil => simp
        | cons B rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      rw [hfac, hlhs]
    rw [hlhs, hrhs] at hsum_bs
    simpa only [hscore_decomp] using hsum_bs
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (n + base) := by positivity
  rw [← mul_le_mul_iff_left₀ hpow_pos, one_mul, Finset.sum_mul]
  calc (2 : ℝ) ^ (n + base)
      ≤ ∑ s ∈ E, z s * ((2 : ℝ) ^ (n + base) -
          ∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
            let y := e.symm (s, (b, (c, zv)))
            let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
            if C.eval (bitsOf n x ++ bitsOf n y) = decide (v = 1) then (1 : ℝ) else -1) := hsum_all
    _ = ∑ s ∈ E, (z s * (1 -
          (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
            let y := e.symm (s, (b, (c, zv)))
            let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
            if C.eval (bitsOf n x ++ bitsOf n y) = decide (v = 1) then (1 : ℝ) else -1) /
          (2 : ℝ) ^ (n + base))) * (2 : ℝ) ^ (n + base) := by
        apply Finset.sum_congr rfl; intro s _
        have hne : (2 : ℝ) ^ (n + base) ≠ 0 := ne_of_gt hpow_pos
        field_simp

lemma sum_sign_bic {m : ℕ} (i0 : Fin m) :
    (∑ b : D m, ∑ c : D m, sign (b i0 * c i0)) = (2 : ℝ) ^ (2 * m) / 2 := by
  have hhalf : ∀ (f : F → ℝ), (∑ b : D m, f (b i0)) = (f 0 + f 1) * (2 : ℝ) ^ (m - 1) := by
    intro f
    let proj : D m →ₗ[F] (Fin 1 → F) :=
      { toFun := fun b _ => b i0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hsurj : Function.Surjective proj := fun y =>
      ⟨Pi.single i0 (y 0), by ext j; fin_cases j; simp [proj]⟩
    have hcard : ∀ ε : F, (Finset.univ.filter (fun b : D m => b i0 = ε)).card * 2 = 2 ^ m := by
      intro ε
      have hc := card_filter_linear_eq proj hsurj (fun _ => ε)
      have heq : Finset.univ.filter (fun b : D m => b i0 = ε) =
          Finset.univ.filter (fun b : D m => proj b = fun _ => ε) := by
        ext b; simp [proj, funext_iff]
      rw [heq]; simpa [Fintype.card_fun, ZMod.card, Fintype.card_fin] using hc
    have hdisj : Disjoint (Finset.univ.filter (fun b : D m => b i0 = 0))
                          (Finset.univ.filter (fun b : D m => b i0 = 1)) := by
      rw [Finset.disjoint_left]; intro b h0 h1
      have e0 := (Finset.mem_filter.mp h0).2; have e1 := (Finset.mem_filter.mp h1).2
      rw [e0] at e1; exact f_one_ne_zero e1.symm
    have hunion : (Finset.univ.filter (fun b : D m => b i0 = 0)) ∪
                  (Finset.univ.filter (fun b : D m => b i0 = 1)) = Finset.univ := by
      ext b; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact f_cases (b i0)
    rw [← hunion, Finset.sum_union hdisj]
    have h0 : ∑ b ∈ Finset.univ.filter (fun b : D m => b i0 = 0), f (b i0) =
        ((Finset.univ.filter (fun b : D m => b i0 = 0)).card : ℝ) * f 0 := by
      rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2]),
          Finset.sum_const, nsmul_eq_mul]
    have h1 : ∑ b ∈ Finset.univ.filter (fun b : D m => b i0 = 1), f (b i0) =
        ((Finset.univ.filter (fun b : D m => b i0 = 1)).card : ℝ) * f 1 := by
      rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2]),
          Finset.sum_const, nsmul_eq_mul]
    have hm1 : 1 ≤ m := by have := i0.isLt; omega
    have hc_eq : ∀ ε : F, ((Finset.univ.filter (fun b : D m => b i0 = ε)).card : ℝ) = (2 : ℝ) ^ (m - 1) := by
      intro ε
      have hnat : (Finset.univ.filter (fun b : D m => b i0 = ε)).card * 2 = 2 ^ (m - 1) * 2 := by
        rw [hcard ε, ← pow_succ, Nat.sub_add_cancel hm1]
      exact_mod_cast Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2) hnat
    rw [h0, h1, hc_eq 0, hc_eq 1]; ring
  have hm1 : 1 ≤ m := by have := i0.isLt; omega
  have hinner : ∀ b : D m, (∑ c : D m, sign (b i0 * c i0)) =
      (sign (b i0 * 0) + sign (b i0 * 1)) * (2 : ℝ) ^ (m - 1) := fun b =>
    hhalf (fun t => sign (b i0 * t))
  simp_rw [hinner]
  rw [hhalf (fun t => (sign (t * 0) + sign (t * 1)) * (2 : ℝ) ^ (m - 1))]
  simp only [zero_mul, one_mul, mul_zero, sign_zero, sign_one]
  have hpow : (2 : ℝ) ^ (m - 1) * (2 : ℝ) ^ (m - 1) * 2 = (2 : ℝ) ^ (2 * m) / 2 := by
    rw [← pow_add]
    have h2m : (2 : ℝ) ^ (2 * m) = (2 : ℝ) ^ (m - 1 + (m - 1)) * 4 := by
      have : 2 * m = (m - 1 + (m - 1)) + 2 := by omega
      rw [this, pow_add]; norm_num
    rw [h2m]; ring
  linarith

lemma sum_const_one {k m r : ℕ} :
    (∑ _x : V k m r, ∑ _b : D m, ∑ _c : D m, ∑ _zv : Z r, (1 : ℝ)) =
      (2 : ℝ) ^ ((k + 2 * m + r) + (2 * m + r)) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega

lemma exact_circuit_exists {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r) (A : Fin m → S k) (h : S k → F)
    (E : Finset (S k)) (a : S k)
    (o : F) (l : S k) (M : Fin k → Fin k → F)
    (hext : ∀ s ∈ E, h s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j) :
    let W := Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))
    let d := Module.finrank F W
    let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
      ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)).card
    ∃ C : Circuit,
      ReadsBack (2 * (k + 2 * m + r)) C ∧ (∀ g ∈ C.gates, gateLegal g) ∧
      circuitCost C = (2 * m + r) + d + varying ∧
      ∀ s ∈ E,
        (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
          let y := e.symm (s, (b, (c, zv)))
          let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
          if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
          then (1 : ℝ) else -1) / 2 ^ ((k + 2 * m + r) + (2 * m + r)) = 1 := by
  intro W d varying
  obtain ⟨C, vW, coordW, _, hrecon, hrb, hleg, hcost, heval⟩ :=
    exists_quad_circuit e A o l M E a none
  refine ⟨C, hrb, hleg, hcost, fun s hs => ?_⟩
  have hmatch : ∀ x b c zv,
      let y := e.symm (s, (b, (c, zv)))
      let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
      (if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
       then (1 : ℝ) else -1) = 1 := by
    intro x b c zv
    dsimp only
    rw [ite_eq_sign]
    have hC := heval x s b c zv
    dsimp only at hC
    rw [hC]
    have hs_eq := hrecon s hs
    have hdot_s : dotProduct (xS e x) a + ∑ t : Fin d, coordW (s - a) t * dotProduct (xS e x) (vW t) =
        dotProduct (xS e x) s := by
      conv_rhs => rw [hs_eq]
      simp only [dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
      rfl
    have hq := quad_expand o l M a vW (fun t => coordW (s - a) t)
    dsimp only at hq
    rw [← hs_eq, ← hext s hs] at hq
    have hm : ∀ i : Fin m,
        (if i ∈ (Finset.univ : Finset (Fin m)).filter (fun i =>
            ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)
         then dotProduct (A i) s else dotProduct (A i) a) = dotProduct (A i) s := by
      intro i
      split_ifs with hi
      · rfl
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        push Not at hi; exact (hi s hs).symm
    have hsum_eq :
        dotProduct (xS e x) a + (o + dotProduct l a + ∑ i, ∑ j, M i j * a i * a j) +
        (∑ t : Fin d, coordW (s - a) t * (dotProduct (xS e x) (vW t) +
          (dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
          ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
            (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u)) +
        dotProduct (xZ e x) zv +
        ∑ i : Fin m, (xB e x i * b i + xC e x i * c i +
          (if i ∈ (Finset.univ : Finset (Fin m)).filter (fun i =>
              ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)
           then dotProduct (A i) s else dotProduct (A i) a) * b i * c i) =
        dotProduct x (e.symm (s, (b, (c, zv)))) + h s + ∑ i, dotProduct (A i) s * b i * c i := by
      simp_rw [hm]
      rw [dotProduct_e_symm, hq, ← hdot_s]
      simp only [dotProduct, mul_add, Finset.sum_add_distrib]
      ring
    rw [hsum_eq, f_add_self, sign_zero]
  simp_rw [hmatch]
  rw [sum_const_one, div_self (by positivity)]

lemma cut_circuit_exists {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r) (A : Fin m → S k) (h : S k → F)
    (E : Finset (S k)) (a : S k) (ha : a ∈ E)
    (o : F) (l : S k) (M : Fin k → Fin k → F)
    (hext : ∀ s ∈ E, h s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j)
    (l0 : S k) (b0 : F)
    (hne : (E.filter (fun s => dotProduct l0 s ≠ b0)).Nonempty)
    (hprop : E.filter (fun s => dotProduct l0 s ≠ b0) ≠ E) :
    let W := Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))
    let d := Module.finrank F W
    let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
      ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)).card
    ∃ C : Circuit,
      ReadsBack (2 * (k + 2 * m + r)) C ∧ (∀ g ∈ C.gates, gateLegal g) ∧
      circuitCost C ≤ (2 * m + r) + d + varying - 1 ∧
      ∀ s ∈ E,
        1 - (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
          let y := e.symm (s, (b, (c, zv)))
          let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
          if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
          then (1 : ℝ) else -1) / 2 ^ ((k + 2 * m + r) + (2 * m + r)) ≤
        if dotProduct l0 s ≠ b0 then (1 : ℝ) else 0 := by
  intro W d varying
  let E' := E.filter (fun s => dotProduct l0 s = b0)
  have hE'_ne : E'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hprop; ext s; simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hs heq
    have : s ∈ E' := Finset.mem_filter.mpr ⟨hs, heq⟩
    rw [hemp] at this; exact Finset.notMem_empty s this
  obtain ⟨a', ha'E'⟩ := hE'_ne
  have ha'E : a' ∈ E := (Finset.mem_filter.mp ha'E').1
  have ha'dot : dotProduct l0 a' = b0 := (Finset.mem_filter.mp ha'E').2
  let W' := Submodule.span F (Set.image (fun s : S k => s - a') (↑E' : Set (S k)))
  have hW'_le : W' ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsE : s ∈ E := (Finset.mem_filter.mp hs).1
    have h1 : s - a ∈ W := Submodule.subset_span ⟨s, hsE, rfl⟩
    have h2 : a' - a ∈ W := Submodule.subset_span ⟨a', ha'E, rfl⟩
    have heq : s - a' = (s - a) - (a' - a) := by abel
    dsimp only; rw [heq]; exact W.sub_mem h1 h2
  have hW'_ker : ∀ v ∈ W', dotProduct l0 v = 0 := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨s, hs, rfl⟩
      rw [dotProduct_sub, (Finset.mem_filter.mp hs).2, ha'dot, sub_self]
    · simp
    · intro x y _ _ hx hy; rw [dotProduct_add, hx, hy, add_zero]
    · intro c x _ hx; rw [dotProduct_smul, hx, smul_zero]
  have hW'_lt : W' < W := by
    obtain ⟨s1, hs1⟩ := hne
    have hs1E : s1 ∈ E := (Finset.mem_filter.mp hs1).1
    have hs1ne : dotProduct l0 s1 ≠ b0 := (Finset.mem_filter.mp hs1).2
    refine lt_of_le_of_ne hW'_le fun heq => ?_
    have hmemW : s1 - a' ∈ W := by
      have : s1 - a' = (s1 - a) - (a' - a) := by abel
      rw [this]; exact W.sub_mem (Submodule.subset_span ⟨s1, hs1E, rfl⟩)
        (Submodule.subset_span ⟨a', ha'E, rfl⟩)
    have h0 := hW'_ker (s1 - a') (heq ▸ hmemW)
    rw [dotProduct_sub, ha'dot, sub_eq_zero] at h0
    exact hs1ne h0
  have hd'_lt : Module.finrank F W' < d := Submodule.finrank_lt_finrank_of_lt hW'_lt
  have hvar_le : ((Finset.univ : Finset (Fin m)).filter (fun i =>
      ∃ s ∈ E', dotProduct (A i) s ≠ dotProduct (A i) a')).card ≤ varying := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨s, hsE', hsne⟩ := hi
    by_cases h1 : dotProduct (A i) s ≠ dotProduct (A i) a
    · exact ⟨s, (Finset.mem_filter.mp hsE').1, h1⟩
    · push Not at h1
      exact ⟨a', ha'E, fun ha' => hsne (h1.trans ha'.symm)⟩
  obtain ⟨C, vW, coordW, hvW_mem, hrecon, hrb, hleg, hcost, heval⟩ :=
    exists_quad_circuit e A o l M E' a' none
  have hcost_le : circuitCost C ≤ 2 * m + r + d + varying - 1 := by
    change circuitCost C = 2 * m + r + Module.finrank F W' +
      ((Finset.univ : Finset (Fin m)).filter (fun i => ∃ s ∈ E', dotProduct (A i) s ≠ dotProduct (A i) a')).card at hcost
    omega
  refine ⟨C, hrb, hleg, hcost_le, fun s hs => ?_⟩
  by_cases hcut : dotProduct l0 s ≠ b0
  · rw [if_pos hcut]
    have hzero : ∀ b c zv,
        ∑ x : V k m r,
          (let y := e.symm (s, (b, (c, zv)))
           let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
           if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
           then (1 : ℝ) else -1) = 0 := by
      intro b c zv
      set y := e.symm (s, (b, (c, zv)))
      have hrw : ∀ x : V k m r,
          (let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
           if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
           then (1 : ℝ) else -1) =
          sign (b2f (C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y)) +
            (dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i)) := fun x => ite_eq_sign _ _
      simp_rw [hrw]
      apply sum_sign_of_shift Finset.univ _ (dualShift e l0) (fun _ _ => Finset.mem_univ _)
      intro x _
      have hC1 := heval (x + dualShift e l0) s b c zv
      have hC0 := heval x s b c zv
      dsimp only at hC1 hC0
      have hdot_a' : dotProduct (xS e (x + dualShift e l0)) a' = dotProduct (xS e x) a' + b0 := by
        rw [xS_add_dualShift, add_dotProduct, ha'dot]
      have hdot_vW : ∀ t, dotProduct (xS e (x + dualShift e l0)) (vW t) = dotProduct (xS e x) (vW t) := by
        intro t; rw [xS_add_dualShift, add_dotProduct, hW'_ker (vW t) (hvW_mem t), add_zero]
      have hCdiff : b2f (C.eval (bitsOf (k + 2 * m + r) (x + dualShift e l0) ++ bitsOf (k + 2 * m + r) y)) =
          b2f (C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y)) + b0 := by
        rw [hC1, hC0]
        simp only [hdot_a', hdot_vW, xB_add_dualShift, xC_add_dualShift, xZ_add_dualShift]
        ring
      have hxdiff : dotProduct (x + dualShift e l0) y = dotProduct x y + dotProduct l0 s := by
        rw [add_dotProduct, dotProduct_dualShift]; simp [y]
      rw [hCdiff, hxdiff]
      have hsum1 : b0 + dotProduct l0 s = 1 := by
        rw [add_comm]; exact (f_ne_iff_add_eq_one _ _).mp hcut
      calc b2f (C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y)) + b0 +
            (dotProduct x y + dotProduct l0 s + h s + ∑ i, dotProduct (A i) s * b i * c i)
          = b2f (C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y)) +
            (dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i) +
            (b0 + dotProduct l0 s) := by ring
        _ = _ := by rw [hsum1]
    have hsum0 : (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
        let y := e.symm (s, (b, (c, zv)))
        let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
        if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
        then (1 : ℝ) else -1) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro c _
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro zv _
      exact hzero b c zv
    rw [hsum0, zero_div, sub_zero]
  · push Not at hcut
    rw [if_neg (not_not.mpr hcut)]
    have hsE' : s ∈ E' := Finset.mem_filter.mpr ⟨hs, hcut⟩
    have hmatch : ∀ x b c zv,
        let y := e.symm (s, (b, (c, zv)))
        let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
        (if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
         then (1 : ℝ) else -1) = 1 := by
      intro x b c zv; dsimp only; rw [ite_eq_sign]
      have hC := heval x s b c zv; dsimp only at hC; rw [hC]
      have hs_eq := hrecon s hsE'
      have hdot_s : dotProduct (xS e x) a' + ∑ t, coordW (s - a') t * dotProduct (xS e x) (vW t) =
          dotProduct (xS e x) s := by
        conv_rhs => rw [hs_eq]
        simp only [dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
      have hq := quad_expand o l M a' vW (fun t => coordW (s - a') t)
      dsimp only at hq
      rw [← hs_eq, ← hext s hs] at hq
      have hm : ∀ i : Fin m,
          (if i ∈ (Finset.univ : Finset (Fin m)).filter (fun i =>
              ∃ s ∈ E', dotProduct (A i) s ≠ dotProduct (A i) a')
           then dotProduct (A i) s else dotProduct (A i) a') = dotProduct (A i) s := by
        intro i; split_ifs with hi
        · rfl
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          push Not at hi; exact (hi s hsE').symm
      have hsum_eq :
          dotProduct (xS e x) a' + (o + dotProduct l a' + ∑ i, ∑ j, M i j * a' i * a' j) +
          (∑ t, coordW (s - a') t * (dotProduct (xS e x) (vW t) +
            (dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a' i * vW t j + vW t i * a' j + vW t i * vW t j)) +
            ∑ u ∈ Finset.univ.filter (fun u => t < u),
              (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a') u)) +
          dotProduct (xZ e x) zv +
          ∑ i : Fin m, (xB e x i * b i + xC e x i * c i +
            (if i ∈ (Finset.univ : Finset (Fin m)).filter (fun i =>
                ∃ s ∈ E', dotProduct (A i) s ≠ dotProduct (A i) a')
             then dotProduct (A i) s else dotProduct (A i) a') * b i * c i) =
          dotProduct x (e.symm (s, (b, (c, zv)))) + h s + ∑ i, dotProduct (A i) s * b i * c i := by
        simp_rw [hm]; rw [dotProduct_e_symm, hq, ← hdot_s]
        simp only [dotProduct, mul_add, Finset.sum_add_distrib]; ring
      rw [hsum_eq, f_add_self, sign_zero]
    simp_rw [hmatch]
    rw [sum_const_one, div_self (by positivity), sub_self]

lemma var_circuit_exists {k m r : ℕ}
    (e : V k m r ≃ₗ[F] S k × Wfull m r) (A : Fin m → S k) (h : S k → F)
    (E : Finset (S k)) (a : S k) (ha : a ∈ E)
    (o : F) (l : S k) (M : Fin k → Fin k → F)
    (hext : ∀ s ∈ E, h s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j)
    (i0 : Fin m) (β : F)
    (hne : (E.filter (fun s => dotProduct (A i0) s ≠ β)).Nonempty)
    (hprop : E.filter (fun s => dotProduct (A i0) s ≠ β) ≠ E) :
    let W := Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))
    let d := Module.finrank F W
    let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
      ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)).card
    ∃ C : Circuit,
      ReadsBack (2 * (k + 2 * m + r)) C ∧ (∀ g ∈ C.gates, gateLegal g) ∧
      circuitCost C ≤ (2 * m + r) + d + varying - 1 ∧
      ∀ s ∈ E,
        1 - (∑ x : V k m r, ∑ b : D m, ∑ c : D m, ∑ zv : Z r,
          let y := e.symm (s, (b, (c, zv)))
          let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
          if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
          then (1 : ℝ) else -1) / 2 ^ ((k + 2 * m + r) + (2 * m + r)) ≤
        if dotProduct (A i0) s ≠ β then (1 / 2 : ℝ) else 0 := by
  intro W d varying
  set varSet := (Finset.univ : Finset (Fin m)).filter (fun i =>
    ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)
  have hi0_var : i0 ∈ varSet := by
    simp only [varSet, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨s1, hs1⟩ := hne
    by_cases h1 : dotProduct (A i0) s1 ≠ dotProduct (A i0) a
    · exact ⟨s1, (Finset.mem_filter.mp hs1).1, h1⟩
    · push Not at h1
      have hex2 : ∃ s2 ∈ E, dotProduct (A i0) s2 = β := by
        by_contra hall; push Not at hall
        apply hprop; ext s; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hall s
      obtain ⟨s2, hs2E, hs2eq⟩ := hex2
      exact ⟨s2, hs2E, fun h2 => (Finset.mem_filter.mp hs1).2 (h1.trans (h2.symm.trans hs2eq))⟩
  obtain ⟨C, vW, coordW, _, hrecon, hrb, hleg, hcost, heval⟩ :=
    exists_quad_circuit e A o l M E a (some (i0, β))
  have hcard_erase : (varSet.erase i0).card = varying - 1 := Finset.card_erase_of_mem hi0_var
  have hvar_pos : 1 ≤ varying := Finset.card_pos.mpr ⟨i0, hi0_var⟩
  have hcost_le : circuitCost C ≤ 2 * m + r + d + varying - 1 := by
    change circuitCost C = 2 * m + r + d + (varSet.erase i0).card at hcost
    rw [hcost, hcard_erase]; omega
  refine ⟨C, hrb, hleg, hcost_le, fun s hs => ?_⟩
  have hdiff : ∀ x b c zv,
      let y := e.symm (s, (b, (c, zv)))
      let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
      (if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) = decide (v = 1)
       then (1 : ℝ) else -1) = sign ((dotProduct (A i0) s + β) * b i0 * c i0) := by
    intro x b c zv; dsimp only; rw [ite_eq_sign]
    have hC := heval x s b c zv; dsimp only at hC; rw [hC]
    have hs_eq := hrecon s hs
    have hdot_s : dotProduct (xS e x) a + ∑ t : Fin d, coordW (s - a) t * dotProduct (xS e x) (vW t) =
        dotProduct (xS e x) s := by
      conv_rhs => rw [hs_eq]
      simp only [dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
      rfl
    have hq := quad_expand o l M a vW (fun t => coordW (s - a) t)
    dsimp only at hq
    rw [← hs_eq, ← hext s hs] at hq
    have hm : ∀ i : Fin m,
        (if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i +
        dotProduct (A i) s * b i * c i =
        if i = i0 then (dotProduct (A i0) s + β) * b i0 * c i0 else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; simp; ring
      · simp only [hi, ↓reduceIte]
        by_cases hv : i ∈ varSet
        · simp [hv, f_add_self]
        · simp only [hv, ↓reduceIte]
          simp only [varSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          push Not at hv
          rw [hv s hs, f_add_self]
    congr 1
    rw [dotProduct_e_symm, hq, ← hdot_s]
    have hcancel :
        dotProduct (xS e x) a + (o + dotProduct l a + ∑ i, ∑ j, M i j * a i * a j) +
        (∑ t : Fin d, coordW (s - a) t * (dotProduct (xS e x) (vW t) +
          (dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
          ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
            (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u)) +
        dotProduct (xZ e x) zv +
        (∑ i : Fin m, (xB e x i * b i + xC e x i * c i +
          (if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i)) +
        (dotProduct (xS e x) a + ∑ t : Fin d, coordW (s - a) t * dotProduct (xS e x) (vW t) +
          dotProduct (xB e x) b + dotProduct (xC e x) c + dotProduct (xZ e x) zv +
          ((o + dotProduct l a + ∑ i, ∑ j, M i j * a i * a j) +
            ∑ t : Fin d, coordW (s - a) t *
              ((dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
               ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
                 (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u)) +
          ∑ i : Fin m, dotProduct (A i) s * b i * c i) =
        ∑ i : Fin m,
          ((if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i +
           dotProduct (A i) s * b i * c i) := by
      have hbc : dotProduct (xB e x) b + dotProduct (xC e x) c =
          ∑ i : Fin m, (xB e x i * b i + xC e x i * c i) := by
        simp [dotProduct, Finset.sum_add_distrib]
      set X1 := dotProduct (xS e x) a + ∑ t : Fin d, coordW (s - a) t * dotProduct (xS e x) (vW t)
      set X2 := (o + dotProduct l a + ∑ i, ∑ j, M i j * a i * a j) +
        ∑ t : Fin d, coordW (s - a) t *
          ((dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
           ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
             (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u)
      set X3 := dotProduct (xZ e x) zv
      set X4 := ∑ i : Fin m, (xB e x i * b i + xC e x i * c i)
      have hsplit_t :
          ∑ t : Fin d, coordW (s - a) t * (dotProduct (xS e x) (vW t) +
            (dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
            ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
              (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u) =
          (∑ t : Fin d, coordW (s - a) t * dotProduct (xS e x) (vW t)) +
          ∑ t : Fin d, coordW (s - a) t *
            ((dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
             ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
               (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u) := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro t _; ring
      have hsplit_i :
          (∑ i : Fin m, (xB e x i * b i + xC e x i * c i +
            (if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i)) =
          X4 + ∑ i : Fin m, (if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i := by
        simp [X4, Finset.sum_add_distrib]
      rw [hsplit_t, hsplit_i]
      have hgrp :
          dotProduct (xS e x) a + (o + dotProduct l a + ∑ i, ∑ j, M i j * a i * a j) +
          ((∑ t : Fin d, coordW (s - a) t * dotProduct (xS e x) (vW t)) +
           ∑ t : Fin d, coordW (s - a) t *
             ((dotProduct l (vW t) + ∑ i, ∑ j, M i j * (a i * vW t j + vW t i * a j + vW t i * vW t j)) +
              ∑ u ∈ Finset.univ.filter (fun u : Fin d => t < u),
                (∑ i, ∑ j, M i j * (vW t i * vW u j + vW u i * vW t j)) * coordW (s - a) u)) +
          X3 + (X4 + ∑ i : Fin m, (if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i) +
          (X1 + dotProduct (xB e x) b + dotProduct (xC e x) c + X3 + X2 + ∑ i : Fin m, dotProduct (A i) s * b i * c i) =
          (X1 + X1) + (X2 + X2) + (X3 + X3) + (X4 + X4) +
          ((∑ i : Fin m, (if i = i0 then β else if i ∈ varSet then dotProduct (A i) s else dotProduct (A i) a) * b i * c i) +
           ∑ i : Fin m, dotProduct (A i) s * b i * c i) := by
        have hX4 : X4 = dotProduct (xB e x) b + dotProduct (xC e x) c := hbc.symm
        simp only [X1, X2, hX4]; ring
      rw [hgrp, f_add_self X1, f_add_self X2, f_add_self X3, f_add_self X4]
      simp [Finset.sum_add_distrib]
    rw [hcancel]
    simp_rw [hm]
    simp
  simp_rw [hdiff]
  by_cases hne_s : dotProduct (A i0) s ≠ β
  · rw [if_pos hne_s]
    have h1 : dotProduct (A i0) s + β = 1 := (f_ne_iff_add_eq_one _ _).mp hne_s
    simp only [h1, one_mul]
    have htot : (∑ _x : V k m r, ∑ b : D m, ∑ c : D m, ∑ _zv : Z r, sign (b i0 * c i0)) =
        (2 : ℝ) ^ ((k + 2 * m + r) + (2 * m + r)) / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      simp_rw [← Finset.mul_sum]
      rw [sum_sign_bic i0]
      have hpow : (2 : ℝ) ^ (k + 2 * m + r) * ((2 : ℝ) ^ r * ((2 : ℝ) ^ (2 * m) / 2)) =
          (2 : ℝ) ^ ((k + 2 * m + r) + (2 * m + r)) / 2 := by
        have h2 : (2 : ℝ) ^ (k + 2 * m + r) * (2 : ℝ) ^ r * (2 : ℝ) ^ (2 * m) =
            (2 : ℝ) ^ ((k + 2 * m + r) + (2 * m + r)) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        linarith
      exact hpow
    rw [htot]
    have hne0 : (2 : ℝ) ^ ((k + 2 * m + r) + (2 * m + r)) ≠ 0 := by positivity
    field_simp; norm_num
  · push Not at hne_s
    simp only [hne_s, ne_eq, not_true_eq_false, ↓reduceIte]
    simp only [f_add_self, zero_mul, sign_zero]
    rw [sum_const_one, div_self (by positivity), sub_self]

theorem main_proof : ∀ k m r : ℕ,
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S) (h : S → F),
    let word := fun (s : S) (i : Fin m) => dotProduct (A i) s
    let score := fun (C : Circ) (s : S) =>
      (∑ x : V, ∑ b : D, ∑ c : D, ∑ z : Z,
        let y := e.symm (s,(b,(c,z)))
        let v := dotProduct x y + h s + ∑ i, word s i * b i * c i
        if C.eval (bits n x ++ bits n y) = decide (v = 1) then (1 : ℝ) else -1) / 2^(n+base)
    let fits := fun (p : ℕ) (C : Circ) => legal (2*n) C ∧ cost C ≤ p
    ∀ (E : Finset S) (a : S), a ∈ E →
      let W := Submodule.span F (Set.image (fun s : S => s-a) (↑E : Set S))
      let d := Module.finrank F W
      let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ∃ s ∈ E, word s i ≠ word a i)).card
      let price := base+d+varying
      let side := fun (l : S) (b : F) => E.filter (fun s => dotProduct l s ≠ b)
      let mass := fun (z : S → ℝ) (B : Finset S) => ∑ s ∈ B, z s
      let cover := fun (z : S → ℝ) => (∀ s ∈ E, 0 ≤ z s) ∧
        (∀ (l : S) (b : F), (side l b).Nonempty → side l b ≠ E → 1 ≤ mass z (side l b)) ∧
        ∀ (i : Fin m) (b : F), (side (A i) b).Nonempty → side (A i) b ≠ E →
          2 ≤ mass z (side (A i) b)
      let extension := ∃ (o : F) (l : S) (M : Fin k → Fin k → F), ∀ s ∈ E,
        h s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
      0 < d → ∀ w : S → ℝ, (∀ s ∈ E, 0 < w s) →
        let total := fun (z : S → ℝ) => ∑ s ∈ E, w s * z s
        let feasible := fun (q : ℝ) =>
          ∃ (N : ℕ) (C : Fin N → Circ) (v : Fin N → ℝ),
            (∀ i, fits (price-1) (C i) ∧ 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
            ∀ s ∈ E, 1-(∑ i, v i * score (C i) s) ≤ q*w s
        ∃ z : S → ℝ, cover z ∧ 0 < total z ∧
          (∀ y : S → ℝ, cover y → total z ≤ total y) ∧
          (∀ q : ℝ, feasible q → 1 ≤ q * total z) ∧
          (extension → feasible (1 / total z) ∧
            (∀ p : ℕ, (∃ C : Circ, fits p C ∧ ∀ s ∈ E, score C s = 1) ↔ price ≤ p)) := by
  classical
  intro k m r n Circ F' legal cost bits V' S' D' Z' base e A h word score fits
    E a ha W d varying price side mass cover extension hd w hw total feasible
  haveI : Nonempty E := ⟨⟨a, ha⟩⟩
  let T1 : Finset (S k × F) := Finset.univ.filter (fun p => (side p.1 p.2).Nonempty ∧ side p.1 p.2 ≠ E)
  let T2 : Finset (Fin m × F) := Finset.univ.filter (fun p => (side (A p.1) p.2).Nonempty ∧ side (A p.1) p.2 ≠ E)
  have hT1_ne : T1.Nonempty := by
    have hne_bot : W ≠ ⊥ := fun hbot => by dsimp only [d] at hd; rw [hbot, finrank_bot] at hd; omega
    have hex : ∃ s1 ∈ E, s1 ≠ a := by
      by_contra hall; push Not at hall
      apply hne_bot; rw [Submodule.span_eq_bot]
      intro v hv; obtain ⟨s, hs, rfl⟩ := hv; simp [hall s hs]
    obtain ⟨s1, hs1E, hs1ne⟩ := hex
    have hex_j : ∃ j : Fin k, s1 j ≠ a j := by
      by_contra hall; push Not at hall; exact hs1ne (funext hall)
    obtain ⟨j, hj⟩ := hex_j
    refine ⟨(Pi.single j 1, a j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · refine ⟨s1, Finset.mem_filter.mpr ⟨hs1E, ?_⟩⟩
      simpa [dotProduct, Pi.single_apply] using hj
    · intro heq
      have := (Finset.mem_filter.mp (heq ▸ ha)).2
      simp [dotProduct, Pi.single_apply] at this
  let Cuts := (T1 : Type) ⊕ (T2 : Type)
  let N := Fintype.card Cuts
  have hN_pos : 0 < N := by
    obtain ⟨p0, hp0⟩ := hT1_ne
    exact Fintype.card_pos_iff.mpr ⟨Sum.inl ⟨p0, hp0⟩⟩
  let equivC : Fin N ≃ Cuts := (Fintype.equivFin Cuts).symm
  let δ : Fin N → E → ℝ := fun idx s =>
    match equivC idx with
    | Sum.inl p => if dotProduct p.1.1 s.1 ≠ p.1.2 then 1 else 0
    | Sum.inr p => if dotProduct (A p.1.1) s.1 ≠ p.1.2 then 1 / 2 else 0
  have hδ_nn : ∀ idx s, 0 ≤ δ idx s := by
    intro idx s; simp only [δ]; cases equivC idx <;> dsimp only <;> split_ifs <;> norm_num
  have hδ_pos : ∀ idx, ∃ s : E, 0 < δ idx s := by
    intro idx; simp only [δ]
    cases hp : equivC idx with
    | inl p =>
      obtain ⟨s, hs⟩ := (Finset.mem_filter.mp p.2).2.1
      refine ⟨⟨s, (Finset.mem_filter.mp hs).1⟩, ?_⟩
      simp [(Finset.mem_filter.mp hs).2]
    | inr p =>
      obtain ⟨s, hs⟩ := (Finset.mem_filter.mp p.2).2.1
      refine ⟨⟨s, (Finset.mem_filter.mp hs).1⟩, ?_⟩
      simp [(Finset.mem_filter.mp hs).2]
  obtain ⟨zE, lam, hzE_cov, hzE_pos, hzE_opt, hlam_nn, hlam_sum, hlam_pack⟩ :=
    lp_duality hN_pos δ hδ_nn hδ_pos (fun s : E => w s.1) (fun s => hw s.1 s.2)
  let z : S k → ℝ := fun s => if hs : s ∈ E then zE ⟨s, hs⟩ else 0
  have hsumE : ∀ f : S k → ℝ, ∑ s ∈ E, f s = ∑ s : E, f s.1 := fun f =>
    (Finset.sum_coe_sort E f).symm
  have hcover_iff : ∀ y : S k → ℝ,
      cover y ↔ ((∀ s : E, 0 ≤ y s.1) ∧ ∀ idx : Fin N, 1 ≤ ∑ s : E, δ idx s * y s.1) := by
    intro y
    constructor
    · rintro ⟨hnn, hcut, hvar⟩
      refine ⟨fun s => hnn s.1 s.2, fun idx => ?_⟩
      simp only [δ]
      cases hp : equivC idx with
      | inl p =>
        have h1 := hcut p.1.1 p.1.2 (Finset.mem_filter.mp p.2).2.1 (Finset.mem_filter.mp p.2).2.2
        have heq : (∑ s : E, (if dotProduct p.1.1 s.1 ≠ p.1.2 then (1 : ℝ) else 0) * y s.1) =
            mass y (side p.1.1 p.1.2) := by
          dsimp only [mass, side]
          rw [Finset.sum_filter, hsumE]
          apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp
        linarith
      | inr p =>
        have h2 := hvar p.1.1 p.1.2 (Finset.mem_filter.mp p.2).2.1 (Finset.mem_filter.mp p.2).2.2
        have heq : (∑ s : E, (if dotProduct (A p.1.1) s.1 ≠ p.1.2 then (1 / 2 : ℝ) else 0) * y s.1) =
            (1 / 2 : ℝ) * mass y (side (A p.1.1) p.1.2) := by
          dsimp only [mass, side]
          rw [Finset.sum_filter, Finset.mul_sum, hsumE]
          apply Finset.sum_congr rfl; intro s _; split_ifs <;> ring
        linarith
    · rintro ⟨hnn, hidx⟩
      refine ⟨fun s hs => hnn ⟨s, hs⟩, fun l0 b0 hne hprop => ?_, fun i0 b0 hne hprop => ?_⟩
      · have hp : (l0, b0) ∈ T1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hprop⟩
        let idx := equivC.symm (Sum.inl ⟨(l0, b0), hp⟩)
        have h1 := hidx idx
        simp only [δ, idx, Equiv.apply_symm_apply] at h1
        have heq : (∑ s : E, (if dotProduct l0 s.1 ≠ b0 then (1 : ℝ) else 0) * y s.1) =
            mass y (side l0 b0) := by
          dsimp only [mass, side]
          rw [Finset.sum_filter, hsumE]
          apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp
        linarith
      · have hp : (i0, b0) ∈ T2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hprop⟩
        let idx := equivC.symm (Sum.inr ⟨(i0, b0), hp⟩)
        have h1 := hidx idx
        simp only [δ, idx, Equiv.apply_symm_apply] at h1
        have heq : (∑ s : E, (if dotProduct (A i0) s.1 ≠ b0 then (1 / 2 : ℝ) else 0) * y s.1) =
            (1 / 2 : ℝ) * mass y (side (A i0) b0) := by
          dsimp only [mass, side]
          rw [Finset.sum_filter, Finset.mul_sum, hsumE]
          apply Finset.sum_congr rfl; intro s _; split_ifs <;> ring
        linarith
  have hz_cov : cover z := (hcover_iff z).mpr ⟨fun s => by simp [z, s.2, hzE_cov.1 s],
    fun idx => by simpa [z] using hzE_cov.2 idx⟩
  have htot_z : total z = ∑ s : E, w s.1 * zE s := by
    rw [show total z = ∑ s ∈ E, w s * z s from rfl, hsumE]
    apply Finset.sum_congr rfl; intro s _; simp [z, s.2]
  have hz_pos : 0 < total z := by rw [htot_z]; exact hzE_pos
  have hz_opt : ∀ y : S k → ℝ, cover y → total z ≤ total y := by
    intro y hy
    rw [htot_z]
    have h1 := hzE_opt (fun s : E => y s.1) ((hcover_iff y).mp hy)
    simpa only [total, hsumE] using h1
  have hfeas_lb : ∀ q : ℝ, feasible q → 1 ≤ q * total z := by
    intro q ⟨M, Cs, vs, hfit_nn, hv_sum, hbound⟩
    have hcirc : ∀ i : Fin M, 1 ≤ ∑ s ∈ E, z s * (1 - score (Cs i) s) := fun i =>
      circuit_cover_bound e A h E a ha hd (Cs i) (hfit_nn i).1.1 (hfit_nn i).1.2 z
        hz_cov.1 hz_cov.2.1 hz_cov.2.2
    have h1 : (1 : ℝ) ≤ ∑ i : Fin M, vs i * ∑ s ∈ E, z s * (1 - score (Cs i) s) := by
      calc (1 : ℝ) = ∑ i : Fin M, vs i * 1 := by rw [← Finset.sum_mul, hv_sum, one_mul]
        _ ≤ ∑ i : Fin M, vs i * ∑ s ∈ E, z s * (1 - score (Cs i) s) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcirc i) (hfit_nn i).2
    have h2 : (∑ i : Fin M, vs i * ∑ s ∈ E, z s * (1 - score (Cs i) s)) =
        ∑ s ∈ E, z s * (1 - ∑ i : Fin M, vs i * score (Cs i) s) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro s _
      calc ∑ i : Fin M, vs i * (z s * (1 - score (Cs i) s))
          = z s * ((∑ i : Fin M, vs i) - ∑ i : Fin M, vs i * score (Cs i) s) := by
            rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
        _ = z s * (1 - ∑ i : Fin M, vs i * score (Cs i) s) := by rw [hv_sum]
    have h3 : (∑ s ∈ E, z s * (1 - ∑ i : Fin M, vs i * score (Cs i) s)) ≤ q * total z := by
      calc ∑ s ∈ E, z s * (1 - ∑ i : Fin M, vs i * score (Cs i) s)
          ≤ ∑ s ∈ E, z s * (q * w s) :=
            Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hbound s hs) (hz_cov.1 s hs)
        _ = q * total z := by
            simp only [total, Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    linarith
  refine ⟨z, hz_cov, hz_pos, hz_opt, hfeas_lb, ?_⟩
  rintro ⟨o, l, M, hext⟩
  have hfeas_ub : feasible (1 / total z) := by
    have hexC : ∀ idx : Fin N,
        ∃ C : Circuit, fits (price - 1) C ∧ ∀ s : E, 1 - score C s.1 ≤ δ idx s := by
      intro idx
      cases hp : equivC idx with
      | inl p =>
        obtain ⟨C, hrb, hleg, hcost, hsc⟩ :=
          cut_circuit_exists e A h E a ha o l M hext p.1.1 p.1.2
            (Finset.mem_filter.mp p.2).2.1 (Finset.mem_filter.mp p.2).2.2
        refine ⟨C, ⟨⟨hrb, hleg⟩, hcost⟩, fun s => ?_⟩
        simp only [δ, hp]; exact hsc s.1 s.2
      | inr p =>
        obtain ⟨C, hrb, hleg, hcost, hsc⟩ :=
          var_circuit_exists e A h E a ha o l M hext p.1.1 p.1.2
            (Finset.mem_filter.mp p.2).2.1 (Finset.mem_filter.mp p.2).2.2
        refine ⟨C, ⟨⟨hrb, hleg⟩, hcost⟩, fun s => ?_⟩
        simp only [δ, hp]; exact hsc s.1 s.2
    choose Cs hCs using hexC
    let vs : Fin N → ℝ := fun idx => lam idx / total z
    refine ⟨N, Cs, vs, fun idx => ⟨(hCs idx).1, div_nonneg (hlam_nn idx) (le_of_lt hz_pos)⟩, ?_, ?_⟩
    · simp only [vs, ← Finset.sum_div, hlam_sum, ← htot_z, div_self (ne_of_gt hz_pos)]
    · intro s hs
      have h1 : 1 - ∑ idx, vs idx * score (Cs idx) s = ∑ idx, vs idx * (1 - score (Cs idx) s) := by
        have hv1 : ∑ idx, vs idx = 1 := by
          simp only [vs, ← Finset.sum_div, hlam_sum, ← htot_z, div_self (ne_of_gt hz_pos)]
        calc 1 - ∑ idx, vs idx * score (Cs idx) s
            = (∑ idx, vs idx) - ∑ idx, vs idx * score (Cs idx) s := by rw [hv1]
          _ = ∑ idx, vs idx * (1 - score (Cs idx) s) := by
              rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro idx _; ring
      rw [h1]
      calc ∑ idx, vs idx * (1 - score (Cs idx) s)
          ≤ ∑ idx, vs idx * δ idx ⟨s, hs⟩ :=
            Finset.sum_le_sum fun idx _ =>
              mul_le_mul_of_nonneg_left ((hCs idx).2 ⟨s, hs⟩) (div_nonneg (hlam_nn idx) (le_of_lt hz_pos))
        _ = (∑ idx, lam idx * δ idx ⟨s, hs⟩) / total z := by
            rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro idx _; simp [vs]; ring
        _ ≤ w s / total z := div_le_div_of_nonneg_right (hlam_pack ⟨s, hs⟩) (le_of_lt hz_pos)
        _ = (1 / total z) * w s := by ring
  refine ⟨hfeas_ub, fun p => ⟨?_, ?_⟩⟩
  · rintro ⟨C, hfit, hsc⟩
    by_contra hlt; push Not at hlt
    have hfp : fits (price - 1) C := ⟨hfit.1, by omega⟩
    have hfeas0 : feasible 0 := by
      refine ⟨1, fun _ => C, fun _ => 1, fun _ => ⟨hfp, by norm_num⟩, by simp, fun s hs => ?_⟩
      simp [hsc s hs]
    have := hfeas_lb 0 hfeas0
    linarith
  · intro hle
    obtain ⟨C, hrb, hleg, hcost, hsc⟩ := exact_circuit_exists e A h E a o l M hext
    have hcost_eq : cost C = price := by
      change circuitCost C = (2 * m + r) +
        Module.finrank F (Submodule.span F (Set.image (fun s : S k => s - a) (↑E : Set (S k)))) +
        ((Finset.univ : Finset (Fin m)).filter (fun i =>
          ∃ s ∈ E, dotProduct (A i) s ≠ dotProduct (A i) a)).card
      convert hcost
    exact ⟨C, ⟨⟨hrb, hleg⟩, hcost_eq.symm ▸ hle⟩, hsc⟩

end PEqualNP.Outside.L_meta_32587

theorem PEqualNP.Outside.L_meta_32587 : (∀ k m r : ℕ,
  let n := k+2*m+r
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let V := Fin n → F
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let base := 2*m+r
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S) (h : S → F),
    let word := fun (s : S) (i : Fin m) => dotProduct (A i) s
    let score := fun (C : Circ) (s : S) =>
      (∑ x : V, ∑ b : D, ∑ c : D, ∑ z : Z,
        let y := e.symm (s,(b,(c,z)))
        let v := dotProduct x y + h s + ∑ i, word s i * b i * c i
        if C.eval (bits n x ++ bits n y) = decide (v = 1) then (1 : ℝ) else -1) / 2^(n+base)
    let fits := fun (p : ℕ) (C : Circ) => legal (2*n) C ∧ cost C ≤ p
    ∀ (E : Finset S) (a : S), a ∈ E →
      let W := Submodule.span F (Set.image (fun s : S => s-a) (↑E : Set S))
      let d := Module.finrank F W
      let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ∃ s ∈ E, word s i ≠ word a i)).card
      let price := base+d+varying
      let side := fun (l : S) (b : F) => E.filter (fun s => dotProduct l s ≠ b)
      let mass := fun (z : S → ℝ) (B : Finset S) => ∑ s ∈ B, z s
      let cover := fun (z : S → ℝ) => (∀ s ∈ E, 0 ≤ z s) ∧
        (∀ (l : S) (b : F), (side l b).Nonempty → side l b ≠ E → 1 ≤ mass z (side l b)) ∧
        ∀ (i : Fin m) (b : F), (side (A i) b).Nonempty → side (A i) b ≠ E →
          2 ≤ mass z (side (A i) b)
      let extension := ∃ (o : F) (l : S) (M : Fin k → Fin k → F), ∀ s ∈ E,
        h s = o + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
      0 < d → ∀ w : S → ℝ, (∀ s ∈ E, 0 < w s) →
        let total := fun (z : S → ℝ) => ∑ s ∈ E, w s * z s
        let feasible := fun (q : ℝ) =>
          ∃ (N : ℕ) (C : Fin N → Circ) (v : Fin N → ℝ),
            (∀ i, fits (price-1) (C i) ∧ 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
            ∀ s ∈ E, 1-(∑ i, v i * score (C i) s) ≤ q*w s
        ∃ z : S → ℝ, cover z ∧ 0 < total z ∧
          (∀ y : S → ℝ, cover y → total z ≤ total y) ∧
          (∀ q : ℝ, feasible q → 1 ≤ q * total z) ∧
          (extension → feasible (1 / total z) ∧
            (∀ p : ℕ, (∃ C : Circ, fits p C ∧ ∀ s ∈ E, score C s = 1) ↔ price ≤ p))) :=
  PEqualNP.Outside.L_meta_32587.main_proof
