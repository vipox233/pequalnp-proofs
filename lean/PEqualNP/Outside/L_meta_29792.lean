import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_29792

open PEqualNP.CircuitLowerBounds

def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem persists (gs : List Gate) (a : List Bool) (i : Nat) (hi : i < a.length) :
    (gs.foldl stepGate a).getD i false = a.getD i false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp [stepGate]
      omega

theorem gate_same (g : Gate) (a b : List Bool) (v : Nat)
    (hh : 0 ∈ g.inputs → g.op = .or ∧ v ∈ g.inputs)
    (ha : a.getD v false = true) (hb : b.getD v false = true)
    (he : ∀ n, n ≠ 0 → a.getD n false = b.getD n false) :
    g.op.eval (g.inputs.map fun n => a.getD n false) =
      g.op.eval (g.inputs.map fun n => b.getD n false) := by
  by_cases h0 : 0 ∈ g.inputs
  · obtain ⟨hop, hv⟩ := hh h0
    rw [hop]
    change (g.inputs.map fun n => a.getD n false).any id =
      (g.inputs.map fun n => b.getD n false).any id
    have onlyTrue (w : List Bool) (hw : w.getD v false = true) :
        (g.inputs.map fun n => w.getD n false).any id = true := by
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨v, hv, hw⟩, rfl⟩
    rw [onlyTrue a ha, onlyTrue b hb]
  · congr 1
    apply List.map_congr_left
    intro n hn
    exact he n (fun h => h0 (h ▸ hn))

theorem run_same (gs : List Gate) (a b : List Bool) (v : Nat)
    (hh : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ v ∈ g.inputs)
    (hl : a.length = b.length) (hv : v < a.length)
    (ha : a.getD v false = true) (hb : b.getD v false = true)
    (he : ∀ n, n ≠ 0 → a.getD n false = b.getD n false) :
    ∀ n, n ≠ 0 → (gs.foldl stepGate a).getD n false = (gs.foldl stepGate b).getD n false := by
  induction gs generalizing a b with
  | nil => exact he
  | cons g gs ih =>
    have hval := gate_same g a b v (hh g (by simp)) ha hb he
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · intro g' hg'
      exact hh g' (List.mem_cons_of_mem _ hg')
    · simp [stepGate, hl]
    · simp [stepGate]
      omega
    · exact (List.getD_append _ _ _ _ hv).trans ha
    · exact (List.getD_append _ _ _ _ (hl ▸ hv)).trans hb
    · intro n hn
      unfold stepGate
      by_cases h : n < a.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hl ▸ h)]
        exact he n hn
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h),
          List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt h), hl, hval]

def edgeVal (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

theorem collide (C : Circuit) (v : Nat) (x y : Fin 7 → Bool)
    (hh : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ v ∈ g.inputs)
    (calcEdge : ∀ z, C.eval (List.ofFn z) = edgeVal z)
    (hv : v < 7) (ha : (List.ofFn x).getD v false = true)
    (hb : (List.ofFn y).getD v false = true)
    (he : ∀ i : Fin 7, i.val ≠ 0 → x i = y i)
    (hdiff : edgeVal x ≠ edgeVal y) : False := by
  have outNotZero : C.output ≠ 0 := by
    intro hz
    let z : Fin 7 → Bool := ![false, true, true, false, false, false, false]
    have hzval : edgeVal z = true := by decide
    have hraw : (List.ofFn z).getD 0 false = false := by decide
    have hh' := persists C.gates (List.ofFn z) 0 (by simp)
    have ev := calcEdge z
    change (C.gates.foldl stepGate (List.ofFn z)).getD C.output false = edgeVal z at ev
    rw [hz, hh', hraw, hzval] at ev
    contradiction
  have hinit : ∀ n, n ≠ 0 → (List.ofFn x).getD n false = (List.ofFn y).getD n false := by
    intro n hn
    by_cases h : n < 7
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_eq_left, Option.getD_some]
        using he ⟨n, h⟩ hn
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
  have hrun := run_same C.gates (List.ofFn x) (List.ofFn y) v hh
    (by simp) (by simpa using hv) ha hb hinit C.output outNotZero
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at hrun
  exact hdiff ((calcEdge x).symm.trans (hrun.trans (calcEdge y)))

end PEqualNP.Outside.L_meta_29792


theorem PEqualNP.Outside.L_meta_29792 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 1 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true)) := by
  rintro ⟨C, i, k, _, _, _, hEval, _, hUnique, hOr, _, _, _, hV, _⟩
  have masked : ∀ g ∈ C.gates, 0 ∈ g.inputs →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ g.inputs := by
    intro g hg h0
    obtain ⟨j, rfl⟩ := List.get_of_mem hg
    rw [hUnique j h0]
    exact ⟨hOr, hV⟩
  exact PEqualNP.Outside.L_meta_29792.collide C 2 ![false, false, true, false, false, false, true] ![true, false, true, false, false, false, true] masked hEval
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide)

