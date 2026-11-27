import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29790

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma commonTail (gs : List Gate) (avoid : ∀ g ∈ gs, 0 ∉ g.inputs) (tail : List Bool) :
    ∃ s : List Bool, ∀ b : Bool, gs.foldl step (b :: tail) = b :: s := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, fun _ => rfl⟩
  | cons g gs ih =>
    let values := g.inputs.map fun i => (false :: tail).getD i false
    have same (b : Bool) : (g.inputs.map fun i => (b :: tail).getD i false) = values := by
      apply List.map_congr_left
      intro i hi
      cases i with
      | zero => exact (avoid g (by simp) hi).elim
      | succ i => rfl
    obtain ⟨s, hs⟩ := ih (fun g' hg' => avoid g' (List.mem_cons_of_mem g hg'))
      (tail ++ [g.op.eval values])
    refine ⟨s, fun b => ?_⟩
    simpa only [List.foldl_cons, step, same b, List.cons_append] using hs b

def testInput (b t : Bool) (j : Fin 7) : Bool :=
  match j.val with
  | 0 => b
  | 1 => true
  | 2 => t
  | 5 => true
  | _ => false

lemma firstStep (g : Gate) (hop : g.op = .or) (h5 : 5 ∈ g.inputs) (b t : Bool) :
    step (List.ofFn (testInput b t)) g = b :: [true, t, false, false, true, false, true] := by
  have h : g.op.eval (g.inputs.map fun i => (List.ofFn (testInput b t)).getD i false) = true := by
    rw [hop, GateOp.eval, List.any_eq_true]
    exact ⟨true, List.mem_map.mpr ⟨5, h5, rfl⟩, rfl⟩
  unfold step
  rw [h]
  rfl

end PEqualNP.Outside.L_meta_29790

open PEqualNP.Outside.L_meta_29790

theorem PEqualNP.Outside.L_meta_29790 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 0 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true)) := by
  rintro ⟨⟨gs, out⟩, ⟨i, hi⟩, k, hi0, _, _, heval, _, unique, hop, _, _, _, h5, _⟩
  change i = 0 at hi0
  subst i
  cases gs with
  | nil => exact Nat.not_lt_zero _ hi
  | cons g gs =>
    change g.op = .or at hop
    change 5 ∈ g.inputs at h5
    have avoid : ∀ gate ∈ gs, 0 ∉ gate.inputs := by
      intro gate hg hz
      obtain ⟨j, rfl⟩ := List.get_of_mem hg
      have eq := unique j.succ hz
      exact Nat.succ_ne_zero j.val (congrArg Fin.val eq)
    have forced (t : Bool) : ∃ s : List Bool, ∀ b : Bool,
        (b :: s).getD out false = (b || t) := by
      obtain ⟨s, hs⟩ := commonTail gs avoid [true, t, false, false, true, false, true]
      refine ⟨s, fun b => ?_⟩
      have eq := heval (testInput b t)
      change (gs.foldl step (step (List.ofFn (testInput b t)) g)).getD out false = _ at eq
      rw [firstStep g hop h5, hs] at eq
      exact eq.trans (by cases b <;> cases t <;> rfl)
    cases out with
    | zero =>
      obtain ⟨s, hs⟩ := forced true
      exact Bool.noConfusion (show false = true from hs false)
    | succ n =>
      obtain ⟨s, hs⟩ := forced false
      exact Bool.noConfusion (show false = true from (hs false).symm.trans (hs true))
