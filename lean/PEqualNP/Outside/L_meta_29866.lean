import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_29866
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def near (a b : List Bool) : Prop :=
  a.length = b.length ∧ 4 < b.length ∧ b.getD 4 false = true ∧
  ∀ j, j ≠ 0 → a.getD j false = b.getD j false

def value (g : Gate) (a : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => a.getD j false)

def step (a : List Bool) (g : Gate) := a ++ [value g a]

theorem same_value (g : Gate) (a b : List Bool) (h : near a b)
    (silent : 0 ∉ g.inputs) : value g a = value g b := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h.2.2.2 j (fun hj0 => silent (hj0 ▸ hj))

theorem step_near (a b : List Bool) (g : Gate) (h : near a b)
    (same : value g a = value g b) : near (step a g) (step b g) := by
  obtain ⟨hlen, hbound, hfour, heq⟩ := h
  refine ⟨by simp [step, hlen], by simp [step]; omega, ?_, ?_⟩
  · simpa only [step, List.getD_append _ _ _ _ hbound] using hfour
  · intro j hj
    by_cases small : j < b.length
    · simpa only [step, List.getD_append _ _ _ _ small,
        List.getD_append _ _ _ _ (by omega : j < a.length)] using heq j hj
    · simp only [step,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
        List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),hlen,same]

theorem special (g : Gate) (a b : List Bool) (h : near a b)
    (op : g.op = .or) (fan : g.inputs.length ≤ 2)
    (h0 : 0 ∈ g.inputs) (h4 : 4 ∈ g.inputs) : value g a = value g b := by
  have h4a : a.getD 4 false = true := (h.2.2.2 4 (by decide)).trans h.2.2.1
  have form : g.inputs = [0,4] ∨ g.inputs = [4,0] := by
    cases e : g.inputs with
    | nil => simp [e] at h0
    | cons u us =>
      cases es : us with
      | nil => simp [e,es] at h0 h4; omega
      | cons v vs =>
        cases ev : vs with
        | nil =>
          simp only [e,es,ev,List.mem_cons,List.not_mem_nil,or_false] at h0 h4
          rcases h0 with h0 | h0 <;> rcases h4 with h4 | h4 <;> simp_all <;> omega
        | cons w ws => simp [e,es,ev] at fan
  rcases form with form | form <;>
    simp [value,op,form,GateOp.eval, ← List.getD_eq_getElem?_getD, h4a,h.2.2.1]

theorem fold_near (p : List Gate) (a b : List Bool) (h : near a b)
    (fan : ∀ g ∈ p, g.inputs.length ≤ 2)
    (restricted : ∀ g ∈ p, 0 ∈ g.inputs → g.op = .or ∧ 4 ∈ g.inputs) :
    near (p.foldl step a) (p.foldl step b) := by
  induction p generalizing a b with
  | nil => exact h
  | cons g p ih =>
    have same : value g a = value g b := by
      by_cases hg : 0 ∈ g.inputs
      · exact special g a b h (restricted g (by simp) hg).1 (fan g (by simp)) hg (restricted g (by simp) hg).2
      · exact same_value g a b h hg
    exact ih _ _ (step_near a b g h same)
      (fun v hv => fan v (by simp [hv]))
      (fun v hv => restricted v (by simp [hv]))

theorem fold_zero (p : List Gate) (a : List Bool) (h : 0 < a.length) :
    (p.foldl step a).getD 0 false = a.getD 0 false := by
  induction p generalizing a with
  | nil => rfl
  | cons g p ih =>
    rw [List.foldl_cons, ih (step a g) (by simp [step])]
    simp only [step, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_29866

theorem PEqualNP.Outside.L_meta_29866 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 6 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true)) := by
  intro h
  obtain ⟨C, i, k, hi, fan, size, eval, h0, unique, hop, hk, hik, link, h4, _, _, _⟩ := h
  let x : Fin 7 → Bool := fun j => decide (j = 1 ∨ j = 4)
  let y : Fin 7 → Bool := fun j => decide (j = 0 ∨ j = 1 ∨ j = 4)
  have near0 : PEqualNP.Outside.L_meta_29866.near (List.ofFn x) (List.ofFn y) := by
    unfold PEqualNP.Outside.L_meta_29866.near
    refine ⟨by simp, by simp, by decide, ?_⟩
    intro j hj
    by_cases h : j < 7
    · interval_cases j <;> simp_all [x,y,List.ofFn_succ]
    · have hx : (List.ofFn x).length ≤ j := by simp; omega
      have hy : (List.ofFn y).length ≤ j := by simp; omega
      rw [List.getD_eq_default _ _ hx, List.getD_eq_default _ _ hy]
  have fan0 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (fan g hg).2
  have only : ∀ g ∈ C.gates, 0 ∈ g.inputs →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 4 ∈ g.inputs := by
    intro g hg hg0
    obtain ⟨j, hj⟩ := List.get_of_mem hg
    have je : j = i := unique j (by rw [hj]; exact hg0)
    subst j
    rw [← hj]
    exact ⟨hop,h4⟩
  have close := PEqualNP.Outside.L_meta_29866.fold_near C.gates (List.ofFn x) (List.ofFn y) near0 fan0 only
  have output_ne : C.output ≠ 0 := by
    intro eq
    let z : Fin 7 → Bool := fun j => decide (j = 0 ∨ j = 4)
    have first : (C.wires (List.ofFn z)).getD 0 false = true := by
      change (C.gates.foldl PEqualNP.Outside.L_meta_29866.step (List.ofFn z)).getD 0 false = true
      rw [PEqualNP.Outside.L_meta_29866.fold_zero _ _ (by simp)]
      decide +kernel
    have e := eval z
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval, eq, first] at e
    simp [z] at e

  have equal : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
    exact close.2.2.2 C.output output_ne
  have ex := eval x
  have ey := eval y
  simp only [x, decide_true, decide_false, Bool.false_and, Bool.true_and, Bool.or_false, Bool.false_or] at ex
  simp only [y, decide_true, decide_false, Bool.false_and, Bool.true_and, Bool.or_false, Bool.false_or] at ey
  rw [ex,ey] at equal
  contradiction
