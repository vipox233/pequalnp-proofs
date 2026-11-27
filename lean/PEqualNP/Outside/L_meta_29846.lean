import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29846
open PEqualNP.CircuitLowerBounds

def valAt (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun j => w.getD j false)
def step (w : List Bool) (g : Gate) := w ++ [valAt g w]

lemma hit (g : Gate) (w : List Bool) (k : Nat) (ho : g.op = .or)
    (hk : k ∈ g.inputs) (ht : w.getD k false = true) : valAt g w = true := by
  simp only [valAt, ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  exact ⟨true, ⟨k, hk, ht⟩, rfl⟩

lemma insensitive (gs : List Gate) (k : Nat)
    (hG : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ k ∈ g.inputs)
    (a b : List Bool) (hl : a.length = b.length) (hb : k < a.length)
    (ha : a.getD k false = true) (hc : b.getD k false = true)
    (he : ∀ j, j ≠ 0 → a.getD j false = b.getD j false) :
    ∀ j, j ≠ 0 → (gs.foldl step a).getD j false = (gs.foldl step b).getD j false := by
  induction gs generalizing a b with
  | nil => exact he
  | cons g gs ih =>
    have hv : valAt g a = valAt g b := by
      by_cases hz : 0 ∈ g.inputs
      · obtain ⟨ho, hk⟩ := hG g List.mem_cons_self hz
        rw [hit g a k ho hk ha, hit g b k ho hk hc]
      · unfold valAt
        congr 1
        apply List.map_congr_left
        intro j hj
        exact he j (fun eq => hz (eq ▸ hj))
    apply ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')) (step a g) (step b g)
    · simp [step,hl]
    · simp [step]; omega
    · exact (List.getD_append _ _ _ _ hb).trans ha
    · have hb' : k < b.length := hl ▸ hb
      exact (List.getD_append _ _ _ _ hb').trans hc
    · intro j hj
      unfold step
      by_cases h : j < a.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hl ▸ h), he j hj]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append, h, ite_false, ← hl, hv]

lemma keep (gs : List Gate) (a : List Bool) (j : Nat) (hj : j < a.length) :
    (gs.foldl step a).getD j false = a.getD j false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    exact (ih (step a g) (by simp [step]; omega)).trans (List.getD_append _ _ _ _ hj)

end PEqualNP.Outside.L_meta_29846
open PEqualNP.Outside.L_meta_29846 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_29846 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 5 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C,i,k,_,_,_,hfun,_,honly,hop,_,_,_,hm,_,_,_⟩
  let x : Fin 7 → Bool := fun j => decide (j.val = 3 ∨ j.val = 6)
  let y : Fin 7 → Bool := fun j => decide (j.val = 0 ∨ j.val = 3 ∨ j.val = 6)
  have hG : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs := by
    intro g hg hz
    obtain ⟨j,rfl⟩ := List.get_of_mem hg
    rw [honly j hz]
    exact ⟨hop,hm⟩
  have hn : C.output ≠ 0 := by
    intro hz
    let z : Fin 7 → Bool := fun j => decide (j.val = 0)
    have hh := hfun z
    change (C.gates.foldl step (List.ofFn z)).getD C.output false = false at hh
    rw [hz, keep _ _ _ (by simp)] at hh
    contradiction
  have hE := insensitive C.gates 3 hG (List.ofFn x) (List.ofFn y) (by simp) (by simp) (by decide) (by decide) (by
    intro j hj
    by_cases h : j < 7
    · have ht : ∀ n : Fin 7, n.val ≠ 0 → (List.ofFn x).getD n.val false = (List.ofFn y).getD n.val false := by decide
      exact ht ⟨j,h⟩ hj
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h), List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]) C.output hn
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at hE
  rw [hfun x,hfun y] at hE
  contradiction
