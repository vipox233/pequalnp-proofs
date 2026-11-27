import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29886_aux

open PEqualNP.CircuitLowerBounds

def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

def appendGate (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue g w]

theorem gateValue_eq (g : Gate) (p : ℕ) (a b : Bool) (tail : List Bool)
    (ht : tail.getD p false = true)
    (h : 0 ∉ g.inputs ∨ (g.op = .or ∧ p + 1 ∈ g.inputs)) :
    gateValue g (a :: tail) = gateValue g (b :: tail) := by
  rcases h with h | ⟨hop, hin⟩
  · unfold gateValue
    congr 1
    apply List.map_congr_left
    intro i hi
    cases i with
    | zero => exact False.elim (h hi)
    | succ i => simp only [List.getD_cons_succ]
  · have ht' (head : Bool) : gateValue g (head :: tail) = true := by
      unfold gateValue
      rw [hop]
      apply List.any_eq_true.2
      refine ⟨true, List.mem_map.2 ⟨p + 1, hin, ?_⟩, rfl⟩
      simpa only [List.getD_cons_succ] using ht
    rw [ht' a, ht' b]

theorem fold_same_tail (gates : List Gate) (p : ℕ) (a b : Bool)
    (tail : List Bool) (ht : tail.getD p false = true)
    (h : ∀ g ∈ gates, 0 ∉ g.inputs ∨ (g.op = .or ∧ p + 1 ∈ g.inputs)) :
    ∃ out, gates.foldl appendGate (a :: tail) = a :: out ∧
      gates.foldl appendGate (b :: tail) = b :: out := by
  induction gates generalizing tail with
  | nil => exact ⟨tail, rfl, rfl⟩
  | cons g gs ih =>
    have he := gateValue_eq g p a b tail ht (h g (by simp))
    have hp : p < tail.length := by
      by_contra! hp
      rw [List.getD_eq_default tail false hp] at ht
      contradiction
    let value := gateValue g (b :: tail)
    have htail : (tail ++ [value]).getD p false = true :=
      (List.getD_append tail [value] false p hp).trans ht
    have hrest : ∀ u ∈ gs, 0 ∉ u.inputs ∨ (u.op = .or ∧ p + 1 ∈ u.inputs) :=
      fun u hu => h u (List.mem_cons_of_mem _ hu)
    simpa only [List.foldl_cons, appendGate, he, List.cons_append] using ih (tail ++ [value]) htail hrest

theorem fold_head (gates : List Gate) (x : Bool) (tail : List Bool) :
    (gates.foldl appendGate (x :: tail)).getD 0 false = x := by
  induction gates generalizing tail with
  | nil => rfl
  | cons g gs ih => exact ih (tail ++ [gateValue g (x :: tail)])

def cycle (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def testInput (b : Bool) (i : Fin 7) : Bool := if i = 0 then b else decide (i = 1 ∨ i = 4)

theorem testInput_bits (b : Bool) :
    List.ofFn (testInput b) = b :: [true, false, false, true, false, false] := by
  cases b <;> decide

theorem cycle_ne_factors (C : Circuit)
    (evalCycle : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle x)
    (gateCond : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = .or ∧ 4 ∈ g.inputs)) : False := by
  by_cases houtput : C.output = 0
  · let x (i : Fin 7) := decide (i = 0)
    have hbits : List.ofFn x = [true, false, false, false, false, false, false] := by decide
    have hcycle : cycle x = false := by decide
    have htrue : C.eval (List.ofFn x) = true := by
      rw [Circuit.eval, hbits, houtput]
      exact fold_head C.gates true _
    rw [evalCycle x, hcycle] at htrue
    contradiction
  · obtain ⟨out, ha, hb⟩ :=
      fold_same_tail C.gates 3 false true [true, false, false, true, false, false] (by decide) gateCond
    have ha' : C.wires (List.ofFn (testInput false)) = false :: out := by
      rw [testInput_bits]
      exact ha
    have hb' : C.wires (List.ofFn (testInput true)) = true :: out := by
      rw [testInput_bits]
      exact hb
    have same : C.eval (List.ofFn (testInput false)) = C.eval (List.ofFn (testInput true)) := by
      unfold Circuit.eval
      rw [ha', hb']
      cases h : C.output with
      | zero => exact (houtput h).elim
      | succ i => simp only [List.getD_cons_succ]
    rw [evalCycle, evalCycle] at same
    exact (by decide : cycle (testInput false) ≠ cycle (testInput true)) same

end PEqualNP.Outside.L_meta_29886_aux

open PEqualNP.Outside.L_meta_29886_aux in
theorem PEqualNP.Outside.L_meta_29886 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 7 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true)) := by
  rintro ⟨C, i, k, _, _, _, hrep, _, hreads, hop, _, _, _, hpartner, _⟩
  refine cycle_ne_factors C hrep ?_
  intro g hg
  by_cases hzero : 0 ∈ g.inputs
  · obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
    have hji := hreads j hzero
    subst j
    exact Or.inr ⟨hop, hpartner⟩
  · exact Or.inl hzero
