import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29904_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold (L : List Gate) (x : List Bool) :
    (L.foldl step x).length = x.length + L.length := by
  induction L generalizing x with
  | nil => simp
  | cons g L ih => simp [List.foldl_cons, ih, step]; omega

theorem prefix_fold (L : List Gate) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (L.foldl step x).getD j false = x.getD j false := by
  induction L generalizing x with
  | nil => rfl
  | cons g L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [step]; omega), step, List.getD_append _ _ _ _ hj]

theorem agree_fold (L : List Gate) (hL : ∀ g ∈ L, 0 ∉ g.inputs) (x y : List Bool)
    (hxy : x.length = y.length) (h : ∀ j, j ≠ 0 → x.getD j false = y.getD j false) :
    ∀ j, j ≠ 0 → (L.foldl step x).getD j false = (L.foldl step y).getD j false := by
  induction L generalizing x y with
  | nil => exact h
  | cons g L ih =>
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map fun i => y.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hL g (List.mem_cons.2 (Or.inl rfl)) (e ▸ hi))
    apply ih (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hxy]
    · intro j hj
      simp only [step]
      rcases lt_trichotomy j x.length with hl | hl | hl
      · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ (hxy ▸ hl)]
        exact h j hj
      · rw [List.getD_append_right _ _ _ _ hl.ge, List.getD_append_right _ _ _ _ (hxy ▸ hl).ge]
        rw [show j - x.length = 0 by omega, show j - y.length = 0 by omega]
        simpa using hv
      · rw [List.getD_append_right _ _ _ _ hl.le, List.getD_append_right _ _ _ _ (hxy ▸ hl).le]
        rw [show j - x.length = (j - x.length - 1) + 1 by omega,
          show j - y.length = (j - x.length - 1) + 1 by omega]
        simp

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_lt (w : List Bool) (g : Gate) (j : ℕ) (h : j < w.length) :
    (step w g).getD j false = w.getD j false := List.getD_append _ _ _ _ h

theorem step_eq (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [step, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem step_gt (w : List Bool) (g : Gate) (j : ℕ) (h : w.length < j) :
    (step w g).getD j false = false := by
  rw [step, List.getD_append_right _ _ _ _ h.le, show j - w.length = (j - w.length - 1) + 1 by omega]
  simp

theorem two_vals (l : List ℕ) (hl : l.length ≤ 2) (h0 : 0 ∈ l) (h2 : 2 ∈ l) :
    ∀ a ∈ l, a = 0 ∨ a = 2 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at * <;> omega

theorem main (C : Circuit) (i k : Fin C.gates.length) (hi8 : i.val = 8)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size = 10)
    (hf : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
      (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)))
    (h0i : 0 ∈ (C.gates.get i).inputs)
    (honly : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hor : (C.gates.get i).op = GateOp.or) (hand : (C.gates.get k).op = GateOp.and)
    (hik : i.val < k.val) (h15k : 7 + i.val ∈ (C.gates.get k).inputs)
    (h2i : 2 ∈ (C.gates.get i).inputs) : False := by
  obtain ⟨gs, out⟩ := C
  simp only [Circuit.size] at hsize
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, rfl⟩ :
      ∃ g0 g1 g2 g3 g4 g5 g6 g7 g8 g9, gs = [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by
    match gs, hsize with
    | [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9], _ => exact ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, rfl⟩
  obtain ⟨iv, hiv⟩ := i
  obtain ⟨kv, hkv⟩ := k
  simp only at hi8 hik
  subst hi8
  obtain rfl : kv = 9 := by simp at hkv; omega
  dsimp only at h0i hor hand h15k h2i
  simp only [List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero] at h0i hor hand h15k h2i
  have hpre : ∀ g ∈ [g0, g1, g2, g3, g4, g5, g6, g7], 0 ∉ g.inputs := by
    intro g hg h0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (honly ⟨0, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨1, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨2, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨3, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨4, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨5, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨6, by simp⟩ h0) (by simp)
    · exact absurd (honly ⟨7, by simp⟩ h0) (by simp)
  have hl8 : g8.inputs.length ≤ 2 := (hfan g8 (by simp)).2
  have hv8 := two_vals _ hl8 h0i h2i
  let P := fun x : List Bool => [g0, g1, g2, g3, g4, g5, g6, g7].foldl step x
  have hw : ∀ x, Circuit.eval ⟨[g0, g1, g2, g3, g4, g5, g6, g7, g8, g9], out⟩ x =
      (step (step (P x) g8) g9).getD out false := fun x => rfl
  have hP : ∀ x : List Bool, x.length = 7 → (P x).length = 15 := by
    intro x hx
    simp only [P, len_fold, hx]
    rfl
  have ea := hf ![true, true, false, false, false, false, false]
  have eb := hf ![false, true, false, false, false, false, false]
  have ec := hf ![false, false, false, true, true, false, false]
  have ed := hf ![true, false, false, false, false, false, false]
  simp only [hw] at ea eb ec ed
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Fin.isValue] at ea eb ec ed
  simp at ea eb ec ed
  rw [← List.getD_eq_getElem?_getD] at ea eb ec ed
  have lA := hP [true, true, false, false, false, false, false] rfl
  have lB := hP [false, true, false, false, false, false, false] rfl
  have lC := hP [false, false, false, true, true, false, false] rfl
  have lD := hP [true, false, false, false, false, false, false] rfl
  by_cases o15 : out < 15
  · by_cases o0 : out = 0
    · subst o0
      rw [step_lt _ _ _ (by rw [step_len]; omega), step_lt _ _ _ (by omega)] at ed
      rw [prefix_fold _ _ _ (by simp)] at ed
      exact absurd ed (by decide)
    · rw [step_lt _ _ _ (by rw [step_len]; omega), step_lt _ _ _ (by omega)] at ea eb
      have := agree_fold _ hpre [true, true, false, false, false, false, false]
        [false, true, false, false, false, false, false] rfl (by
          intro j hj
          rcases j with _ | j
          · exact absurd rfl hj
          · simp) out o0
      simp only [P] at ea eb
      rw [this, eb] at ea
      exact absurd ea (by decide)
  · by_cases o15' : out = 15
    · subst o15'
      rw [step_lt _ _ _ (by rw [step_len]; omega), ← lC, step_eq, hor] at ec
      simp only [GateOp.eval, List.any_map] at ec
      rw [List.any_eq_true] at ec
      obtain ⟨a, ha, hav⟩ := ec
      rcases hv8 a ha with rfl | rfl
      · simp only [Function.comp_apply, id_eq, P] at hav
        rw [prefix_fold _ _ _ (by simp)] at hav
        exact absurd hav (by decide)
      · simp only [Function.comp_apply, id_eq, P] at hav
        rw [prefix_fold _ _ _ (by simp)] at hav
        exact absurd hav (by decide)
    · by_cases o16 : out = 16
      · subst o16
        have e16 : 16 = (step (P [false, false, false, true, true, false, false]) g8).length := by
          rw [step_len, lC]
        rw [e16, step_eq, hand] at ec
        simp only [GateOp.eval, List.all_map] at ec
        rw [List.all_eq_true] at ec
        have h15 := ec (7 + 8) h15k
        simp only [Function.comp_apply, id] at h15
        rw [show 7 + 8 = (P [false, false, false, true, true, false, false]).length by rw [lC],
          step_eq, hor] at h15
        simp only [GateOp.eval, List.any_map] at h15
        rw [List.any_eq_true] at h15
        obtain ⟨a, ha, hav⟩ := h15
        rcases hv8 a ha with rfl | rfl
        · simp only [Function.comp_apply, id_eq, P] at hav
          rw [prefix_fold _ _ _ (by simp)] at hav
          exact absurd hav (by decide)
        · simp only [Function.comp_apply, id_eq, P] at hav
          rw [prefix_fold _ _ _ (by simp)] at hav
          exact absurd hav (by decide)
      · rw [step_gt _ _ _ (by rw [step_len]; omega)] at ea
        exact absurd ea (by decide)

end PEqualNP.Outside.L_meta_29904_aux

theorem PEqualNP.Outside.L_meta_29904 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true) := by
  rintro ⟨C, i, k, hi8, hfan, hsize, hf, h0i, honly, hor, hand, hik, h15k, h2i, -⟩
  exact PEqualNP.Outside.L_meta_29904_aux.main C i k hi8 hfan hsize hf h0i honly hor hand hik h15k h2i
