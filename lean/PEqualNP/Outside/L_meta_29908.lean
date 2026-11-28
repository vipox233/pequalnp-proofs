import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29908

open PEqualNP.CircuitLowerBounds

/-- One gate step of the wire fold. -/
def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (a : List Bool) (v : Bool) (n : ℕ) (h : n < a.length) :
    (a ++ [v]).getD n false = a.getD n false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_ge (a b : List Bool) (v : Bool) (n : ℕ) (hl : a.length = b.length)
    (h : a.length ≤ n) : (a ++ [v]).getD n false = (b ++ [v]).getD n false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right h, List.getElem?_append_right (hl ▸ h), hl]

theorem fold_prefix (gs : List Gate) : ∀ a : List Bool, ∀ n, n < a.length →
    (gs.foldl F a).getD n false = a.getD n false := by
  induction gs with
  | nil => intro a n _; rfl
  | cons g gs ih =>
    intro a n h
    simp only [List.foldl_cons]
    rw [ih _ n (by simp [F]; omega)]
    exact getD_snoc a _ n h

theorem fold_len (gs : List Gate) : ∀ a : List Bool,
    (gs.foldl F a).length = a.length + gs.length := by
  induction gs with
  | nil => intro a; simp
  | cons g gs ih => intro a; simp only [List.foldl_cons, ih, F]; simp; omega

theorem fold_agree (w : ℕ) (hw0 : w ≠ 0) (gs : List Gate)
    (hg : ∀ g ∈ gs, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ w ∈ g.inputs)) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ n, n ≠ 0 → a.getD n false = b.getD n false) →
      w < a.length → a.getD w false = true →
      ∀ n, n ≠ 0 → (gs.foldl F a).getD n false = (gs.foldl F b).getD n false := by
  induction gs with
  | nil => intro a b _ h _ _; exact h
  | cons g gs ih =>
    intro a b hl hab hwl hwa
    have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      rcases hg g (by simp) with h0 | ⟨hor, hw⟩
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact hab i (fun h => h0 (h ▸ hi))
      · have hwb : b.getD w false = true := by rw [← hab w hw0]; exact hwa
        rw [hor]
        simp only [GateOp.eval, List.any_map]
        rw [List.any_eq_true.mpr ⟨w, hw, by simpa using hwa⟩,
          List.any_eq_true.mpr ⟨w, hw, by simpa using hwb⟩]
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (by simp [hg'])) (F a g) (F b g)
    · simp [F, hl]
    · intro n hn
      simp only [F]
      by_cases hn' : n < a.length
      · rw [getD_snoc a _ n hn', getD_snoc b _ n (hl ▸ hn'), hab n hn]
      · rw [hv]; exact getD_snoc_ge a b _ n hl (by omega)
    · simp [F]; omega
    · simp only [F]; rw [getD_snoc a _ w hwl]; exact hwa

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

theorem getD_ofFn (x : Fin 7 → Bool) (n : ℕ) (h : n < 7) :
    (List.ofFn x).getD n false = x ⟨n, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

theorem getD_ofFn_ge (x : Fin 7 → Bool) (n : ℕ) (h : 7 ≤ n) :
    (List.ofFn x).getD n false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [show ¬ n < 7 by omega, dite_false]
  rfl

theorem key (C : Circuit) (w : ℕ) (hw0 : w ≠ 0) (hw7 : w < 7)
    (hg : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ w ∈ g.inputs))
    (x1 x2 : Fin 7 → Bool) (hagree : ∀ j : Fin 7, j.val ≠ 0 → x1 j = x2 j)
    (hw : x1 ⟨w, hw7⟩ = true) (hout : C.output ≠ 0) :
    C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  apply fold_agree w hw0 C.gates hg _ _ (by simp) _ (by simp; omega)
    (by rw [getD_ofFn x1 w hw7]; exact hw) _ hout
  intro n hn
  by_cases h : n < 7
  · rw [getD_ofFn x1 n h, getD_ofFn x2 n h]; exact hagree _ hn
  · rw [getD_ofFn_ge x1 n (by omega), getD_ofFn_ge x2 n (by omega)]

theorem out0 (C : Circuit) (x : Fin 7 → Bool) (hout : C.output = 0) :
    C.eval (List.ofFn x) = x 0 := by
  unfold Circuit.eval
  rw [wires_eq, hout, fold_prefix _ _ 0 (by simp), getD_ofFn x 0 (by omega)]
  rfl

end PEqualNP.Outside.L_meta_29908

open PEqualNP.Outside.L_meta_29908 in
theorem PEqualNP.Outside.L_meta_29908 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true) := by
  rintro ⟨C, i, k, -, -, -, hf, -, honly, hor, -, -, -, hw, -, -, -⟩
  have hg : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 4 ∈ g.inputs) := by
    intro g hgm
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hgm
    by_cases h0 : 0 ∈ (C.gates.get j).inputs
    · right; obtain rfl := honly j h0; exact ⟨hor, hw⟩
    · left; exact h0
  by_cases hout : C.output = 0
  · have h := hf ![true, false, false, false, false, false, false]
    rw [out0 C _ hout] at h
    simp at h
  · have h := key C 4 (by omega) (by omega) hg ![true, true, false, false, true, false, false] ![false, true, false, false, true, false, false]
      (by intro j hj; fin_cases j <;> simp_all) (by simp) hout
    rw [hf, hf] at h
    simp at h
