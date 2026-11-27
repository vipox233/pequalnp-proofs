import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29848
open PEqualNP.CircuitLowerBounds

def runG (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w

theorem keepsInputs (gs : List Gate) (w : List Bool) : ∃ s, runG gs w = w ++ s := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [runG]⟩
  | cons g gs ih =>
    obtain ⟨s,hs⟩ := ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
    exact ⟨_,hs.trans (List.append_assoc ..)⟩

theorem coupled (gs : List Gate) (b : ℕ) (t : List Bool)
    (live : (false :: t).getD b false = true)
    (hb : b ≠ 0)
    (law : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ b ∈ g.inputs) :
    ∃ s, runG gs (false :: t) = false :: s ∧ runG gs (true :: t) = true :: s := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    let v (a : Bool) := g.op.eval (g.inputs.map fun j => (a :: t).getD j false)
    have same (j : ℕ) (hj : j ≠ 0) : (false :: t).getD j false = (true :: t).getD j false := by
      cases j <;> simp_all
    have eqv : v false = v true := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨ho,hm⟩ := law g (by simp) h0
        have force (a : Bool) (ha : (a :: t).getD b false = true) : v a = true := by
          simp only [v,ho,GateOp.eval,List.any_eq_true]
          exact ⟨true,List.mem_map.mpr ⟨b,hm,ha⟩,rfl⟩
        exact (force false live).trans (force true ((same b hb).symm.trans live)).symm
      · unfold v
        congr 1
        apply List.map_congr_left
        intro j hj
        exact same j (fun h => h0 (h ▸ hj))
    have inRange : b < (false :: t).length := by
      by_contra! h
      rw [List.getD_eq_default _ _ h] at live
      contradiction
    have nextLive : ((false :: t) ++ [v false]).getD b false = true := by
      rw [List.getD_append _ _ _ _ inRange]
      exact live
    obtain ⟨s,hs,ht⟩ := ih (t ++ [v false]) nextLive (fun q hq => law q (by simp [hq]))
    refine ⟨s,hs,?_⟩
    change runG gs (true :: (t ++ [v true])) = true :: s
    rwa [← eqv]


theorem checked : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 5 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true) := by
  rintro ⟨C,i,k,_,_,_,hf,_,sole,hor,_,_,_,hwire,_⟩
  have law : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 4 ∈ g.inputs := by
    intro g hg hz
    obtain ⟨j,hj⟩ := List.get_of_mem hg
    subst g
    have hji := sole j hz
    subst j
    exact ⟨hor,hwire⟩
  let t : List Bool := [true, false, false, true, false, false]
  obtain ⟨s,hs,ht⟩ := coupled C.gates 4 t (by decide) (by decide) law
  let x (a : Bool) (j : Fin 7) := if j = 0 then a else decide (j.val = 4 ∨ j.val = 1)
  have hF := hf (x false)
  have hT := hf (x true)
  change (runG C.gates (false :: t)).getD C.output false = false at hF
  change (runG C.gates (true :: t)).getD C.output false = true at hT
  rw [hs] at hF
  rw [ht] at hT
  cases ho : C.output with
  | succ j => simp [ho] at hF hT
              simp_all
  | zero =>
    let y (j : Fin 7) := decide (j ≠ 0)
    have hy := hf y
    obtain ⟨v,hv⟩ := keepsInputs C.gates (List.ofFn y)
    change (runG C.gates (List.ofFn y)).getD C.output false = true at hy
    rw [hv,ho] at hy
    change false = true at hy
    contradiction
end PEqualNP.Outside.L_meta_29848

theorem PEqualNP.Outside.L_meta_29848 :
    ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 5 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true) := @PEqualNP.Outside.L_meta_29848.checked
