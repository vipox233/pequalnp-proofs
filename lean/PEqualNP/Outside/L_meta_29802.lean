import PEqualNP.Defs

-- Input x0 is read only by an OR gate that also reads x2. With x2 on, that gate is on whatever x0 is,
-- so two inputs that differ only in x0 give the same wires apart from wire 0. With x2 and x6 on
-- and x1, x3, x5 off, the 7-cycle edge function equals x0, so the circuit cannot compute it.
namespace PEqualNP.Outside.L_meta_29802_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (w : List Bool) (v : Bool) (j : ℕ) :
    (w ++ [v]).getD j false = if j < w.length then w.getD j false
      else if j = w.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem agree (gs : List Gate)
    (hg : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = GateOp.or ∧ 2 ∈ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length → 2 < w.length →
      w.getD 2 false = true →
      (∀ j, j ≠ 0 → w.getD j false = w'.getD j false) →
      ∀ j, j ≠ 0 → (gs.foldl step w).getD j false = (gs.foldl step w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ _ h j hj; exact h j hj
  | cons g gs ih =>
    intro w w' hl h2l h2 hw
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨hop, hin⟩ := hg g (by simp) h0
        have h2' : w'.getD 2 false = true := by rw [← hw 2 (by omega)]; exact h2
        rw [hop]
        simp only [GateOp.eval, List.any_map]
        rw [List.any_eq_true.mpr ⟨2, hin, by simpa using h2⟩,
          List.any_eq_true.mpr ⟨2, hin, by simpa using h2'⟩]
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact hw i (by rintro rfl; exact h0 hi)
    apply ih (fun g' hg' => hg g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · simp only [step]; rw [getD_snoc]; simp only [h2l, ite_true]; exact h2
    · intro j hj
      simp only [step]
      rw [getD_snoc, getD_snoc, hv, ← hl]
      split_ifs
      · exact hw j hj
      · rfl
      · rfl

theorem keep (gs : List Gate) : ∀ (w : List Bool) (j : ℕ), j < w.length →
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs with
  | nil => intro w j _; rfl
  | cons g gs ih =>
    intro w j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp [step]; omega)]
    simp only [step]; rw [getD_snoc]; simp [hj]

end PEqualNP.Outside.L_meta_29802_aux

theorem PEqualNP.Outside.L_meta_29802 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 2 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true) := by
  rintro ⟨C, i, k, -, -, -, hev, -, honly, hop, -, -, -, h2, -⟩
  have hg : ∀ g ∈ C.gates, 0 ∈ g.inputs →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ g.inputs := by
    intro g hgm h0
    obtain ⟨j, rfl⟩ := List.get_of_mem hgm
    have := honly j h0
    subst this
    exact ⟨hop, h2⟩
  let xa : Fin 7 → Bool := ![false, false, true, false, false, false, true]
  let xb : Fin 7 → Bool := ![true, false, true, false, false, false, true]
  have hw := PEqualNP.Outside.L_meta_29802_aux.agree C.gates hg (List.ofFn xa) (List.ofFn xb)
    (by simp) (by simp) (by simp [xa]) (by
      intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | j
      · exact absurd rfl hj
      all_goals simp [xa, xb])
  have hwires : ∀ x : List Bool,
      C.wires x = C.gates.foldl PEqualNP.Outside.L_meta_29802_aux.step x := fun _ => rfl
  have ea := hev xa
  have eb := hev xb
  have e0 := hev ![true, false, false, false, false, false, false]
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, hwires] at ea eb e0
  by_cases ho : C.output = 0
  · rw [ho, PEqualNP.Outside.L_meta_29802_aux.keep _ _ _ (by simp)] at e0
    simp at e0
  · have := hw C.output ho
    rw [ea, eb] at this
    simp [xa, xb] at this
