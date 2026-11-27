import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29830

open PEqualNP.CircuitLowerBounds

private theorem wire_input_preserved (gs : List Gate) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) xs).getD i false =
      xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem circuit_input_preserved (C : Circuit) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length) : (C.wires xs).getD i false = xs.getD i false :=
  wire_input_preserved C.gates xs i hi

private theorem ofFn_seven (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

private theorem cycle_output_ne_zero (C : Circuit)
    (hs : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
       (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) :
    C.output ≠ 0 := by
  intro h
  let x : Fin 7 → Bool := ![false, true, true, false, false, false, false]
  have hbits : List.ofFn x = [false, true, true, false, false, false, false] := by
    rw [ofFn_seven]
    rfl
  have htrue : C.eval (List.ofFn x) = true := hs x
  have hfalse : C.eval (List.ofFn x) = false := by
    unfold Circuit.eval
    rw [h, circuit_input_preserved _ _ _ (by simp), hbits]
    rfl
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

private def step (ys : List Bool) (g : Gate) : List Bool :=
  ys ++ [g.op.eval (g.inputs.map (fun i => ys.getD i false))]

private theorem getD_cons_swap (rs : List Bool) (i : ℕ) (h : i ≠ 0) :
    (false :: rs).getD i false = (true :: rs).getD i false := by
  cases i with
  | zero => contradiction
  | succ i => rfl

private theorem gate_mask (g : Gate) (rs : List Bool) (w : ℕ) (hw : w ≠ 0)
    (ht : (false :: rs).getD w false = true)
    (hm : 0 ∈ g.inputs → g.op = .or ∧ w ∈ g.inputs) :
    g.op.eval (g.inputs.map (fun i => (false :: rs).getD i false)) =
      g.op.eval (g.inputs.map (fun i => (true :: rs).getD i false)) := by
  by_cases hzero : 0 ∈ g.inputs
  · obtain ⟨hOr,hread⟩ := hm hzero
    rw [hOr]
    have htrue : (true :: rs).getD w false = true := (getD_cons_swap rs w hw).symm.trans ht
    have both (b : Bool) (h : (b :: rs).getD w false = true) :
        GateOp.or.eval (g.inputs.map (fun i => (b :: rs).getD i false)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨w,hread,h⟩,rfl⟩
    exact (both false ht).trans (both true htrue).symm
  · congr 1
    apply List.map_congr_left
    intro i hi
    exact getD_cons_swap rs i (fun eq => hzero (eq ▸ hi))

private theorem fold_mask (gs : List Gate) (rs : List Bool) (w : ℕ) (hw : w ≠ 0)
    (hn : w < (false :: rs).length) (ht : (false :: rs).getD w false = true)
    (hm : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ w ∈ g.inputs) :
    ∃ ss, gs.foldl step (false :: rs) = false :: ss ∧
      gs.foldl step (true :: rs) = true :: ss := by
  induction gs generalizing rs with
  | nil => exact ⟨rs,rfl,rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map (fun i => (false :: rs).getD i false))
    have evalEqual := gate_mask g rs w hw ht (hm g (by simp))
    have left : step (false :: rs) g = false :: (rs ++ [b]) := rfl
    have right : step (true :: rs) g = true :: (rs ++ [b]) := by simp [step, b, evalEqual]
    have lt : w < (false :: (rs ++ [b])).length := by
      simp only [List.length_cons, List.length_append] at hn ⊢
      omega
    have keep : (false :: (rs ++ [b])).getD w false = true := by
      change ((false :: rs) ++ [b]).getD w false = true
      rw [List.getD_append _ _ _ _ hn, ht]
    rw [List.foldl_cons, List.foldl_cons, left, right]
    exact ih (rs ++ [b]) lt keep (fun a ha => hm a (List.mem_cons_of_mem g ha))

private theorem eval_mask (C : Circuit) (rs : List Bool) (w : ℕ) (hw : w ≠ 0)
    (hn : w < (false :: rs).length) (ht : (false :: rs).getD w false = true)
    (hm : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ w ∈ g.inputs)
    (ho : C.output ≠ 0) :
    C.eval (false :: rs) = C.eval (true :: rs) := by
  obtain ⟨ss,h0,h1⟩ := fold_mask C.gates rs w hw hn ht hm
  change (C.gates.foldl step (false :: rs)).getD C.output false =
    (C.gates.foldl step (true :: rs)).getD C.output false
  rw [h0, h1]
  exact getD_cons_swap ss C.output ho

end PEqualNP.Outside.L_meta_29830

open PEqualNP.Outside.L_meta_29830 in
theorem PEqualNP.Outside.L_meta_29830 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 4 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C, i, k, _, _, _, hC, _, hunique, hop, _, _, _, hread, _, _, _⟩
  have hAll : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs := by
    intro g hg hz
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have e : (⟨j,hj⟩ : Fin C.gates.length) = i := hunique _ hz
    change (C.gates.get ⟨j,hj⟩).op = .or ∧ 3 ∈ (C.gates.get ⟨j,hj⟩).inputs
    rw [e]
    exact ⟨hop,hread⟩
  let a : Fin 7 → Bool := ![false,true,false,true,false,false,false]
  let b : Fin 7 → Bool := ![true,true,false,true,false,false,false]
  let rs := [true,false,true,false,false,false]
  have ha : List.ofFn a = false :: rs := by decide
  have hb : List.ofFn b = true :: rs := by decide
  have ea : C.eval (false :: rs) = false := by
    rw [← ha, hC]
    decide
  have eb : C.eval (true :: rs) = true := by
    rw [← hb, hC]
    decide
  have e := eval_mask C rs 3 (by decide) (by decide) (by decide) hAll
    (cycle_output_ne_zero C hC)
  rw [ea, eb] at e
  contradiction
