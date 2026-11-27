import PEqualNP.Defs

-- Derive output wire bounds [25, 25 + size) and truncate + canonicalize every 2-input gate to a ≤ b.
theorem PEqualNP.Outside.R_meta_18874_3
    (hOutBounds :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (25 : ℕ) C →
        (∀ (x : Fin (25 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (p : Fin (12 : ℕ)) (l : Fin (13 : ℕ)),
              (p.succ = l ∨ p.succ = l + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨
                p.succ = l + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨
                p.succ = l + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              x (Fin.natAdd (12 : ℕ) l) = Bool.true) →
        (25 : ℕ) ≤ C.output ∧ C.output < (25 : ℕ) + C.size)
    (hTruncCanon :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (25 : ℕ) C →
        (0 : ℕ) < C.size →
        C.output = (25 : ℕ) + (C.size - (1 : ℕ)) →
        (∀ g ∈ C.gates, g.inputs.getD (0 : ℕ) (0 : ℕ) ≤ g.inputs.getD (1 : ℕ) (0 : ℕ)) →
        (∀ (x : Fin (25 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (p : Fin (12 : ℕ)) (l : Fin (13 : ℕ)),
              (p.succ = l ∨ p.succ = l + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨
                p.succ = l + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨
                p.succ = l + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              x (Fin.natAdd (12 : ℕ) l) = Bool.true) →
        (58 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (25 : ℕ) x1 →
      (∀ (x3 : Fin (25 : ℕ) → Bool),
        x1.eval (List.ofFn x3) = Bool.true ↔
          ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)),
            (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨
              x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨
              x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧
            x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧
            x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) →
      (58 : ℕ) ≤ x1.size := by
  intro x1 hAO hEv
  have hOB := hOutBounds x1 hAO hEv
  have h25_le : 25 ≤ x1.output := hOB.1
  have hout_lt : x1.output < 25 + x1.size := hOB.2
  have hx1_sz : x1.size = x1.gates.length := rfl
  let m : ℕ := x1.output - 25 + 1
  have hm_le : m ≤ x1.gates.length := by
    rw [← hx1_sz]
    dsimp [m]
    omega
  let normGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
    ⟨g.op, if g.inputs.getD 0 0 ≤ g.inputs.getD 1 0 then g.inputs else [g.inputs.getD 1 0, g.inputs.getD 0 0]⟩
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨(x1.gates.take m).map normGate, x1.output⟩
  have hC'_sz : C'.size = m := by
    dsimp [C', PEqualNP.CircuitLowerBounds.Circuit.size]
    rw [List.length_map, List.length_take, Nat.min_eq_left hm_le]
  have hC'_pos : 0 < C'.size := by omega
  have hC'_out : C'.output = 25 + (C'.size - 1) := by
    rw [hC'_sz]
    dsimp [C', m]
    omega
  have hC'_ord : ∀ g ∈ C'.gates, g.inputs.getD 0 0 ≤ g.inputs.getD 1 0 := by
    intro g hg
    dsimp [C'] at hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, _, rfl⟩
    dsimp [normGate]
    by_cases hle : g0.inputs.getD 0 0 ≤ g0.inputs.getD 1 0
    · rw [if_pos hle]; exact hle
    · rw [if_neg hle]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at hle ⊢
      omega
  have hC'_AO : PEqualNP.TopForm.IsAO2 25 C' := by
    rcases hAO with ⟨hAOO, hRB, hLen⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      dsimp [C'] at hg
      rw [List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩
      exact hAOO g0 (List.mem_of_mem_take hg0)
    · intro j hj i hi
      have hj' : j < m := by
        dsimp [C'] at hj
        rw [List.length_map, List.length_take, Nat.min_eq_left hm_le] at hj
        exact hj
      have hj_full : j < x1.gates.length := lt_of_lt_of_le hj' hm_le
      have hgate0 : PEqualNP.MetaComplexity.NestedCover.gateAt x1 j = x1.gates[j] := by
        dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_full]
        rfl
      have hgate' : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = normGate x1.gates[j] := by
        dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hj',
          List.getElem?_eq_getElem hj_full]
        rfl
      rw [hgate'] at hi
      have hi0 : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).inputs := by
        rw [hgate0]
        dsimp [normGate] at hi
        by_cases hle : x1.gates[j].inputs.getD 0 0 ≤ x1.gates[j].inputs.getD 1 0
        · simp only [hle, ↓reduceIte] at hi; exact hi
        · simp only [hle, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hi
          have hlen_j : x1.gates[j].inputs.length = 2 := hLen x1.gates[j] (List.getElem_mem hj_full)
          rcases List.length_eq_two.mp hlen_j with ⟨a, b, hab⟩
          rw [hab] at hi ⊢
          simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some] at hi
          rcases hi with rfl | rfl <;> simp
      exact hRB j hj_full i hi0
    · intro g hg
      dsimp [C'] at hg
      rw [List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩
      have hlen0 : g0.inputs.length = 2 := hLen g0 (List.mem_of_mem_take hg0)
      dsimp [normGate]
      split_ifs
      · exact hlen0
      · rfl
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      (gs.foldl step acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have hfold_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool) (j : ℕ),
      j < acc.length → (gs.foldl step acc).getD j false = acc.getD j false := by
    intro gs
    induction gs with
    | nil => intro acc _ _; rfl
    | cons g gs ih =>
      intro acc j hj
      rw [List.foldl_cons, ih (step acc g) j (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have hstep_norm : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      g.inputs.length = 2 →
      step w (normGate g) = step w g := by
    intro w g hop hlen_g
    rcases List.length_eq_two.mp hlen_g with ⟨a, b, hab⟩
    dsimp [step, normGate]
    rw [hab]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    by_cases hle : a ≤ b
    · simp only [hle, ↓reduceIte]
    · simp only [hle, ↓reduceIte, List.map_cons, List.map_nil]
      have hand_c : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] =
          PEqualNP.CircuitLowerBounds.GateOp.and.eval [v, u] := by
        intro u v; cases u <;> cases v <;> rfl
      have hor_c : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] =
          PEqualNP.CircuitLowerBounds.GateOp.or.eval [v, u] := by
        intro u v; cases u <;> cases v <;> rfl
      rcases hop with hop | hop
      · rw [hop, hand_c]
      · rw [hop, hor_c]
  have hfold_norm : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ g ∈ gs, g.inputs.length = 2) →
      (gs.map normGate).foldl step acc = gs.foldl step acc := by
    intro gs
    induction gs with
    | nil => intro acc _ _; rfl
    | cons g gs ih =>
      intro acc h1 h2
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      rw [hstep_norm acc g (h1 g (by simp)) (h2 g (by simp))]
      exact ih (step acc g) (fun g' hg' => h1 g' (by simp [hg'])) (fun g' hg' => h2 g' (by simp [hg']))
  have hC'_ev : ∀ x : Fin 25 → Bool,
      C'.eval (List.ofFn x) = Bool.true ↔
        ∃ (p : Fin 12) (l : Fin 13),
          (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
          x (Fin.castAdd 13 p) = Bool.true ∧ x (Fin.natAdd 12 l) = Bool.true := by
    intro x
    let inp := List.ofFn x
    rcases hAO with ⟨hAOO, _, hLen⟩
    have hwires_eq : C'.wires inp = (x1.gates.take m).foldl step inp :=
      hfold_norm (x1.gates.take m) inp
        (fun g hg => hAOO g (List.mem_of_mem_take hg))
        (fun g hg => hLen g (List.mem_of_mem_take hg))
    have hx1_split : x1.wires inp = (x1.gates.drop m).foldl step (C'.wires inp) := by
      rw [hwires_eq]
      change x1.gates.foldl step inp =
        (x1.gates.drop m).foldl step ((x1.gates.take m).foldl step inp)
      rw [← List.foldl_append, List.take_append_drop]
    have hout_lt_C' : x1.output < (C'.wires inp).length := by
      rw [hwires_eq, hfold_len]
      have hlen_inp : inp.length = 25 := by simp [inp]
      rw [hlen_inp, List.length_take, Nat.min_eq_left hm_le]
      omega
    have heval_eq : C'.eval inp = x1.eval inp := by
      change (C'.wires inp).getD x1.output false = (x1.wires inp).getD x1.output false
      rw [hx1_split, hfold_getD (x1.gates.drop m) (C'.wires inp) x1.output hout_lt_C']
    rw [heval_eq]
    exact hEv x
  have hres := hTruncCanon C' hC'_AO hC'_pos hC'_out hC'_ord hC'_ev
  have hsz_le : C'.size ≤ x1.size := by
    dsimp [PEqualNP.CircuitLowerBounds.Circuit.size] at *
    omega
  exact le_trans hres hsz_le
