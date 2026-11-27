import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29808

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma firstWire (gs : List Gate) (b : Bool) (tail : List Bool) :
    (gs.foldl step (b :: tail)).getD 0 false = b := by
  induction gs generalizing tail with
  | nil => rfl
  | cons g gs ih => exact ih _

lemma commonTail (gs : List Gate) (m : Nat)
    (masked : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ m + 1 ∈ g.inputs)
    (tail : List Bool) (lit : tail[m]? = some true) :
    ∃ s : List Bool, ∀ b : Bool, gs.foldl step (b :: tail) = b :: s := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, fun _ => rfl⟩
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => (false :: tail).getD i false)
    have same (b : Bool) :
        g.op.eval (g.inputs.map fun i => (b :: tail).getD i false) = value := by
      by_cases readsZero : 0 ∈ g.inputs
      · obtain ⟨hop, hm⟩ := masked g (by simp) readsZero
        have forced (d : Bool) :
            g.op.eval (g.inputs.map fun i => (d :: tail).getD i false) = true := by
          rw [hop, GateOp.eval, List.any_eq_true]
          refine ⟨true, List.mem_map.mpr ⟨m + 1, hm, ?_⟩, rfl⟩
          change tail[m]?.getD false = true
          rw [lit]
          rfl
        exact (forced b).trans (forced false).symm
      · apply congrArg g.op.eval
        apply List.map_congr_left
        intro i hi
        cases i with
        | zero => exact (readsZero hi).elim
        | succ i => rfl
    obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp lit
    have nextLit : (tail ++ [value])[m]? = some true := by
      rw [List.getElem?_append_left inRange, lit]
    obtain ⟨s, hs⟩ := ih (fun g' hg' => masked g' (List.mem_cons_of_mem g hg'))
      (tail ++ [value]) nextLit
    refine ⟨s, fun b => ?_⟩
    simpa only [List.foldl_cons, step, same b, List.cons_append] using hs b

def cycleEdges (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def testInput (b : Bool) (j : Fin 7) : Bool :=
  match j.val with
  | 0 => b
  | 1 | 5 => true
  | _ => false

lemma noMaskedCycle (C : Circuit) (i : Fin C.gates.length)
    (heval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycleEdges x)
    (unique : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hop : (C.gates.get i).op = .or) (h5 : 5 ∈ (C.gates.get i).inputs) : False := by
  cases out : C.output with
  | zero =>
    have eq := heval (fun j => decide (j.val = 0))
    change (C.gates.foldl step [true, false, false, false, false, false, false]).getD
      C.output false = false at eq
    rw [out, firstWire] at eq
    exact Bool.noConfusion eq
  | succ n =>
    have masked : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 5 ∈ g.inputs := by
      intro g hg hz
      obtain ⟨j, rfl⟩ := List.get_of_mem hg
      rw [unique j hz]
      exact ⟨hop, h5⟩
    obtain ⟨s, hs⟩ := commonTail C.gates 4 masked [true, false, false, false, true, false] rfl
    have result (b : Bool) : s.getD n false = b := by
      have eq := heval (testInput b)
      change (C.gates.foldl step (b :: [true, false, false, false, true, false])).getD
        C.output false = _ at eq
      rw [hs b, out] at eq
      exact eq.trans (by cases b <;> rfl)
    exact Bool.noConfusion ((result false).symm.trans (result true))

end PEqualNP.Outside.L_meta_29808

theorem PEqualNP.Outside.L_meta_29808 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 2 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true)) := by
  rintro ⟨C, i, k, _, _, _, heval, _, unique, hop, _, _, _, h5, _⟩
  exact PEqualNP.Outside.L_meta_29808.noMaskedCycle C i heval unique hop h5
