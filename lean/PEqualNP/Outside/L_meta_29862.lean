import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29862

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def pt (l : List Bool) : Fin 7 → Bool := fun j => l.getD j.val false

def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) ||
    (x 6 && x 0)

def Ok (g : Gate) : Prop := 0 ∈ g.inputs → g.op = GateOp.or ∧ 2 ∈ g.inputs

theorem step_keep {b : Bool} {w : List Bool} {g : Gate} (hlen : 2 < w.length)
    (hw : w.getD 2 false = true) (hg : Ok g) : step (w.set 0 b) g = (step w g).set 0 b := by
  have h0 : 0 < w.length := by omega
  by_cases hmem : 0 ∈ g.inputs
  · obtain ⟨hop, h2⟩ := hg hmem
    have hw' : (w.set 0 b).getD 2 false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by decide), ← List.getD_eq_getElem?_getD]
      exact hw
    have e1 : g.op.eval (g.inputs.map fun k => (w.set 0 b).getD k false) = true := by
      rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map]
      exact ⟨true, ⟨2, h2, hw'⟩, rfl⟩
    have e2 : g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
      rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map]
      exact ⟨true, ⟨2, h2, hw⟩, rfl⟩
    unfold step
    rw [e1, e2, List.set_append]
    simp only [h0, ite_true]
  · have hmap : (g.inputs.map fun k => (w.set 0 b).getD k false)
        = g.inputs.map fun k => w.getD k false := by
      apply List.map_congr_left
      intro k hk
      have hne : 0 ≠ k := fun h => hmem (h ▸ hk)
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
    unfold step
    rw [hmap, List.set_append]
    simp only [h0, ite_true]

theorem foldl_keep {b : Bool} : ∀ (gs : List Gate) (w : List Bool), 2 < w.length →
    w.getD 2 false = true → (∀ g ∈ gs, Ok g) →
    gs.foldl step (w.set 0 b) = (gs.foldl step w).set 0 b := by
  intro gs
  induction gs with
  | nil => intro w _ _ _; rfl
  | cons g gs ih =>
    intro w hlen hw hg
    rw [List.foldl_cons, List.foldl_cons, step_keep hlen hw (hg g (List.mem_cons_self ..))]
    refine ih (step w g) (by simp [step]; omega) ?_ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    unfold step
    rw [List.getD_append _ _ _ _ hlen]
    exact hw

theorem foldl_front : ∀ (gs : List Gate) (w : List Bool) (k : ℕ), k < w.length →
    (gs.foldl step w).getD k false = w.getD k false := by
  intro gs
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    rw [List.foldl_cons, ih (step w g) k (by simp [step]; omega)]
    unfold step
    rw [List.getD_append _ _ _ _ hk]

end PEqualNP.Outside.L_meta_29862

theorem PEqualNP.Outside.L_meta_29862 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 6 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true)) := by
  rintro ⟨⟨gates, out⟩, i, k, -, -, -, heval, -, honly, hor, -, -, -, hpart, -, -, -⟩
  have hok : ∀ g ∈ gates, PEqualNP.Outside.L_meta_29862.Ok g := by
    intro g hg h0
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    have hj := honly j h0
    subst hj
    exact ⟨hor, hpart⟩
  have e1 : (gates.foldl PEqualNP.Outside.L_meta_29862.step
      (List.ofFn (PEqualNP.Outside.L_meta_29862.pt [false, false, true, false, false, false, true]))).getD out false
        = PEqualNP.Outside.L_meta_29862.target (PEqualNP.Outside.L_meta_29862.pt [false, false, true, false, false, false, true]) :=
    heval _
  have e2 : (gates.foldl PEqualNP.Outside.L_meta_29862.step
      (List.ofFn (PEqualNP.Outside.L_meta_29862.pt [true, false, true, false, false, false, true]))).getD out false
        = PEqualNP.Outside.L_meta_29862.target (PEqualNP.Outside.L_meta_29862.pt [true, false, true, false, false, false, true]) :=
    heval _
  have e3 : (gates.foldl PEqualNP.Outside.L_meta_29862.step
      (List.ofFn (PEqualNP.Outside.L_meta_29862.pt [false, true, true, false, false, false, false]))).getD out false
        = PEqualNP.Outside.L_meta_29862.target (PEqualNP.Outside.L_meta_29862.pt [false, true, true, false, false, false, false]) :=
    heval _
  have hset : List.ofFn (PEqualNP.Outside.L_meta_29862.pt [true, false, true, false, false, false, true])
      = (List.ofFn (PEqualNP.Outside.L_meta_29862.pt [false, false, true, false, false, false, true])).set 0 true := by
    decide
  rw [hset, PEqualNP.Outside.L_meta_29862.foldl_keep gates _ (by decide) (by decide) hok] at e2
  by_cases hout : out = 0
  · subst hout
    rw [PEqualNP.Outside.L_meta_29862.foldl_front gates _ 0 (by decide)] at e3
    exact absurd e3 (by decide)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hout),
      ← List.getD_eq_getElem?_getD, e1] at e2
    exact absurd e2 (by decide)
