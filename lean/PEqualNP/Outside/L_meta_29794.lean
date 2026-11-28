import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29794_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma keep (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hlt : j < (step w g).length := by simp [step]; omega
    rw [List.foldl_cons, ih (step w g) hlt]
    simp only [step, List.getD_append _ _ _ _ hj]

lemma agree (h : ℕ) (gs : List Gate) (u v : List Bool) (hl : u.length = v.length)
    (hag : ∀ j, j ≠ 0 → u.getD j false = v.getD j false) (hh : h < u.length) (h0 : h ≠ 0)
    (hu : u.getD h false = true)
    (hg : ∀ g ∈ gs, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ h ∈ g.inputs)) :
    ∀ j, j ≠ 0 → (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
  induction gs generalizing u v with
  | nil => exact hag
  | cons g gs ih =>
    have val : g.op.eval (g.inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      rcases hg g (by simp) with no | ⟨isor, mem⟩
      · congr 1
        exact List.map_congr_left fun k hk => hag k (fun e => no (e ▸ hk))
      · have hv : v.getD h false = true := (hag h h0).symm.trans hu
        have a : (g.inputs.map fun i => u.getD i false).any id = true :=
          List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨h, mem, hu⟩, rfl⟩
        have c : (g.inputs.map fun i => v.getD i false).any id = true :=
          List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨h, mem, hv⟩, rfl⟩
        rw [isor]
        simp only [GateOp.eval]
        rw [a, c]
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (step u g) (step v g)
    · simp [step, hl]
    · intro j hj
      by_cases small : j < u.length
      · simpa only [step, List.getD_append _ _ _ _ small, List.getD_append _ _ _ _ (hl ▸ small)] using hag j hj
      · simp only [step, List.getD_append_right _ _ _ _ (by omega : u.length ≤ j),
          List.getD_append_right _ _ _ _ (by omega : v.length ≤ j), hl, val]
    · simp [step]
      omega
    · simpa only [step, List.getD_append _ _ _ _ hh] using hu
    · exact fun g' m => hg g' (List.mem_cons_of_mem _ m)

end PEqualNP.Outside.L_meta_29794_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29794_aux

theorem PEqualNP.Outside.L_meta_29794 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 1 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C, i, k, _, _, _, hev, _, honly, hop, _, _, _, hmem, _⟩
  have hg : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ 3 ∈ g.inputs) := by
    intro g hg
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hg
    by_cases z : 0 ∈ (C.gates.get n).inputs
    · have e := honly n z
      subst e
      exact Or.inr ⟨hop, hmem⟩
    · exact Or.inl z
  by_cases o : C.output = 0
  · have e := hev (fun j => [true, false, false, false, false, false, false].getD j.val false)
    have w : C.eval (List.ofFn fun j : Fin 7 => [true, false, false, false, false, false, false].getD j.val false) = true := by
      unfold Circuit.eval Circuit.wires
      rw [o]
      exact (keep C.gates _ 0 (by simp)).trans (by decide)
    rw [w] at e
    exact absurd e (by decide)
  · have e1 := hev (fun j => [false, true, false, true, false, false, false].getD j.val false)
    have e2 := hev (fun j => [true, true, false, true, false, false, false].getD j.val false)
    have l1 : (List.ofFn fun j : Fin 7 => [false, true, false, true, false, false, false].getD j.val false) = [false, true, false, true, false, false, false] := by decide
    have l2 : (List.ofFn fun j : Fin 7 => [true, true, false, true, false, false, false].getD j.val false) = [true, true, false, true, false, false, false] := by decide
    have same : C.eval [false, true, false, true, false, false, false] = C.eval [true, true, false, true, false, false, false] := by
      unfold Circuit.eval Circuit.wires
      refine agree 3 C.gates [false, true, false, true, false, false, false] [true, true, false, true, false, false, false] rfl ?_ (by decide) (by decide) (by decide) hg C.output o
      intro j hj
      cases j with
      | zero => exact absurd rfl hj
      | succ j => rfl
    rw [l1, same] at e1
    rw [l2] at e2
    rw [e1] at e2
    exact absurd e2 (by decide)
