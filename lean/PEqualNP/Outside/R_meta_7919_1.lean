import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7919_1
    (hNonStarDeg3 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)),
        (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
        (∃ (x9 x10 : Fin x1), x2.Adj x9 x10) →
        ∀ (v : Fin x1), ∃ (u w : Fin x1), x2.Adj u w ∧ u ≠ v ∧ w ≠ v)
    (hCanon : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 → (0 : ℕ) < x5.size → x5.output = x1 + (x5.size - (1 : ℕ)) → (∀ g ∈ x5.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.Pairwise (· ≤ ·)) →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3, (2 : ℕ) ≤ (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates).length) →                     (∃ x15 ∉ x3,                         have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates;                         x16.length = (2 : ℕ) ∧ ∃ x17 ∈ x16, x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                       ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3, (2 : ℕ) ≤ (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates).length) →                     (∃ x15 ∉ x3,                         have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates;                         x16.length = (2 : ℕ) ∧ ∃ x17 ∈ x16, x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                       ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro x1 x2 x3 x4 x5 hdeg hgirth hno3 hedge hx4 hfan hfun hmin hge2 hex2
  rcases hedge with ⟨eu, ew, hedg⟩
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      (gs.foldl step acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih => intro acc; rw [List.foldl_cons, ih]; simp [step]; omega
  have hfold_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool) (k : ℕ),
      k < acc.length → (gs.foldl step acc).getD k false = acc.getD k false := by
    intro gs
    induction gs with
    | nil => intro acc _ _; rfl
    | cons g gs ih =>
      intro acc k hk
      rw [List.foldl_cons, ih (step acc g) k (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have hx1_le : x1 ≤ x5.output := by
    by_contra hlt
    have hlt' : x5.output < x1 := Nat.lt_of_not_le hlt
    obtain ⟨u, w, hadj, hnu, hnw⟩ := hNonStarDeg3 x1 x2 x3 hdeg hno3 ⟨eu, ew, hedg⟩ ⟨x5.output, hlt'⟩
    let fn : Fin x1 → Bool := fun z => Decidable.decide (z = u ∨ z = w)
    have htru : x5.eval (List.ofFn fn) = true := by
      have h1 : PEqualNP.MetaComplexity.circuitFun x1 x5 fn = x4 fn := congrFun hfun fn
      change x5.eval (List.ofFn fn) = x4 fn at h1
      rw [h1, hx4 fn]
      exact Or.inr ⟨u, w, hadj, by simp [fn], by simp [fn]⟩
    have hfls : x5.eval (List.ofFn fn) = false := by
      change (x5.gates.foldl step (List.ofFn fn)).getD x5.output false = false
      rw [hfold_getD x5.gates (List.ofFn fn) x5.output (by simp [hlt']),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt']), Option.getD_some,
        List.getElem_ofFn]
      have hnu' : x5.output ≠ ↑u := fun h => hnu (Fin.ext h.symm)
      have hnw' : x5.output ≠ ↑w := fun h => hnw (Fin.ext h.symm)
      simp [fn, Fin.ext_iff, hnu', hnw']
    rw [hfls] at htru; cases htru
  have hout_lt : x5.output < x1 + x5.size := by
    by_contra hge
    have hle : x1 + x5.size ≤ x5.output := Nat.le_of_not_lt hge
    let fn : Fin x1 → Bool := fun z => Decidable.decide (z = eu ∨ z = ew)
    have htru : x5.eval (List.ofFn fn) = true := by
      have h1 : PEqualNP.MetaComplexity.circuitFun x1 x5 fn = x4 fn := congrFun hfun fn
      change x5.eval (List.ofFn fn) = x4 fn at h1
      rw [h1, hx4 fn]
      exact Or.inr ⟨eu, ew, hedg, by simp [fn], by simp [fn]⟩
    have hlen_w : (x5.wires (List.ofFn fn)).length = x1 + x5.size := by
      change (x5.gates.foldl step (List.ofFn fn)).length = x1 + x5.gates.length
      rw [hfold_len, List.length_ofFn]
    have hfls : x5.eval (List.ofFn fn) = false := by
      change (x5.wires (List.ofFn fn)).getD x5.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfls] at htru; cases htru
  let m : ℕ := x5.output - x1 + 1
  have hx5_sz : x5.size = x5.gates.length := rfl
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ x5.gates.length := by omega
  have hm_eq : m = x5.size := by
    let Ct : PEqualNP.CircuitLowerBounds.Circuit := ⟨x5.gates.take m, x5.output⟩
    have hCt_fan : PEqualNP.MetaComplexity.FanInTwo Ct := by
      intro g hg
      exact hfan g (List.mem_of_mem_take hg)
    have hCt_sz : Ct.size = m := by
      change (x5.gates.take m).length = m; rw [List.length_take, Nat.min_eq_left hm_le]
    have hCt_eval : ∀ fn : Fin x1 → Bool, Ct.eval (List.ofFn fn) = x4 fn := by
      intro fn
      have hfn0 : x5.eval (List.ofFn fn) = x4 fn := congrFun hfun fn
      rw [← hfn0]
      let inp := List.ofFn fn
      have hlen_inp : inp.length = x1 := by simp [inp]
      have hx5_split : x5.wires inp = (x5.gates.drop m).foldl step (Ct.wires inp) := by
        change x5.gates.foldl step inp = (x5.gates.drop m).foldl step ((x5.gates.take m).foldl step inp)
        rw [← List.foldl_append, List.take_append_drop]
      have hout_lt_Ct : x5.output < (Ct.wires inp).length := by
        change x5.output < ((x5.gates.take m).foldl step inp).length
        rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left hm_le]
        dsimp [m]; omega
      change (Ct.wires inp).getD x5.output false = (x5.wires inp).getD x5.output false
      rw [hx5_split, hfold_getD (x5.gates.drop m) (Ct.wires inp) x5.output hout_lt_Ct]
    have hhas : PEqualNP.MetaComplexity.HasCircuitSize x1 x4 m :=
      ⟨Ct, hCt_fan, hCt_sz.le, hCt_eval⟩
    have hle := hmin m hhas
    omega
  have hx5_pos : 0 < x5.size := by omega
  have hx5_out : x5.output = x1 + (x5.size - 1) := by dsimp [m] at *; omega
  have hfan' : ∀ g ∈ x5.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    rcases hfan g hg with ⟨hop, hlen_g⟩
    refine ⟨?_, hlen_g⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr (Or.inl hop)
    · exact Or.inr (Or.inr (by simpa [Set.mem_singleton_iff] using hop))
  let sortAO : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate) g.op
      (List.casesOn g.inputs g fun a r1 =>
        List.casesOn r1 g fun b r2 =>
          List.casesOn r2 (if b < a then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [b, a]⟩ else g) (fun _ _ => g))
      (List.casesOn g.inputs g fun a r1 =>
        List.casesOn r1 g fun b r2 =>
          List.casesOn r2 (if b < a then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [b, a]⟩ else g) (fun _ _ => g))
      g (fun _ => g) g
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨x5.gates.map sortAO, x5.output⟩
  have hC'_sz : C'.size = x5.size := List.length_map _
  have hsort_op : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (sortAO g).op = g.op := by
    intro g; rcases g with ⟨op, is⟩
    rcases op with _ | _ | _ | _ | _
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · rfl
      · rfl
      · dsimp [sortAO]; split_ifs <;> rfl
      · rfl
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · rfl
      · rfl
      · dsimp [sortAO]; split_ifs <;> rfl
      · rfl
    · rfl
    · rfl
    · rfl
  have hsort_len : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (sortAO g).inputs.length = g.inputs.length := by
    intro g; rcases g with ⟨op, is⟩
    rcases op with _ | _ | _ | _ | _
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩ <;> [rfl; rfl; (dsimp [sortAO]; split_ifs <;> rfl); rfl]
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩ <;> [rfl; rfl; (dsimp [sortAO]; split_ifs <;> rfl); rfl]
    · rfl
    · rfl
    · rfl
  have hC'_fan : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    dsimp [C'] at hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    rcases hfan g0 hg0 with ⟨hop0, hlen0⟩
    rw [hsort_op g0, hsort_len g0]
    exact ⟨hop0, hlen0⟩
  have hC'_pair : ∀ g ∈ C'.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.Pairwise (· ≤ ·) := by
    intro g hg hne_not
    dsimp [C'] at hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    rcases hfan' g0 hg0 with ⟨hop0, hlen0⟩
    rw [hsort_op] at hne_not
    rcases g0 with ⟨op, is⟩
    rcases hop0 with hop0 | hop0 | hop0 <;> dsimp only at hop0 hlen0 hne_not <;> subst hop0
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · exact List.Pairwise.nil
      · exact List.pairwise_singleton _ _
      · dsimp [sortAO]; by_cases hba : b < a
        · rw [if_pos hba]; dsimp only; rw [List.pairwise_pair]; exact Nat.le_of_lt hba
        · rw [if_neg hba]; dsimp only; rw [List.pairwise_pair]; exact Nat.le_of_not_lt hba
      · exfalso; simp at hlen0
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · exact List.Pairwise.nil
      · exact List.pairwise_singleton _ _
      · dsimp [sortAO]; by_cases hba : b < a
        · rw [if_pos hba]; dsimp only; rw [List.pairwise_pair]; exact Nat.le_of_lt hba
        · rw [if_neg hba]; dsimp only; rw [List.pairwise_pair]; exact Nat.le_of_not_lt hba
      · exfalso; simp at hlen0
    · exact absurd rfl hne_not
  have hstep_sort : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      g.inputs.length ≤ 2 →
      step w (sortAO g) = step w g := by
    intro w g hop hlen_g
    rcases g with ⟨op, is⟩
    rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · rfl
      · rfl
      · dsimp [step, sortAO]; by_cases hba : b < a
        · rw [if_pos hba]; dsimp only; simp only [List.map_cons, List.map_nil]
          cases (w.getD a false) <;> cases (w.getD b false) <;> rfl
        · rw [if_neg hba]
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · rfl
      · rfl
      · dsimp [step, sortAO]; by_cases hba : b < a
        · rw [if_pos hba]; dsimp only; simp only [List.map_cons, List.map_nil]
          cases (w.getD a false) <;> cases (w.getD b false) <;> rfl
        · rw [if_neg hba]
      · simp at hlen_g
    · rfl
  have hC'_wires : ∀ inp : List Bool, C'.wires inp = x5.wires inp := by
    intro inp
    change (x5.gates.map sortAO).foldl step inp = x5.gates.foldl step inp
    suffices h : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
        (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
        (gs.map sortAO).foldl step acc = gs.foldl step acc by
      exact h x5.gates inp hfan'
    intro gs
    induction gs with
    | nil => intro acc _; rfl
    | cons g gs ih =>
      intro acc hgs
      have h0 := hgs g List.mem_cons_self
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, hstep_sort acc g h0.1 h0.2]
      exact ih (step acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
  have hC'_eval : ∀ fn : Fin x1 → Bool, C'.eval (List.ofFn fn) = x5.eval (List.ofFn fn) := by
    intro fn
    change (C'.wires (List.ofFn fn)).getD C'.output false = (x5.wires (List.ofFn fn)).getD x5.output false
    rw [hC'_wires]
  have hfun' : PEqualNP.MetaComplexity.circuitFun x1 C' = x4 := by
    rw [← hfun]; funext fn; exact hC'_eval fn
  have hmin' : ∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → C'.size ≤ x13 := by
    intro x13 hh; rw [hC'_sz]; exact hmin x13 hh
  let pred : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun v g =>
    (List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs).contains v
  have hpred_sort : ∀ (v : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      g.inputs.length ≤ 2 →
      pred v (sortAO g) = pred v g := by
    intro v g hop hlen_g
    rcases g with ⟨op, is⟩
    rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · rfl
      · rfl
      · dsimp [sortAO]; by_cases hba : b < a
        · rw [if_pos hba]; dsimp only [pred]
          change ([b, a].contains v) = ([a, b].contains v)
          simp only [List.contains_cons, List.contains_nil, Bool.false_or, Bool.or_comm]
        · rw [if_neg hba]
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
      · rfl
      · rfl
      · dsimp [sortAO]; by_cases hba : b < a
        · rw [if_pos hba]; dsimp only [pred]
          change ([b, a].contains v) = ([a, b].contains v)
          simp only [List.contains_cons, List.contains_nil, Bool.false_or, Bool.or_comm]
        · rw [if_neg hba]
      · simp at hlen_g
    · rfl
  have hfilter_map : ∀ (v : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
      List.filter (pred v) (gs.map sortAO) = (List.filter (pred v) gs).map sortAO := by
    intro v gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro hgs
      have h0 := hgs g List.mem_cons_self
      have hgs' : ∀ g' ∈ gs, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
      rw [List.map_cons, List.filter_cons, List.filter_cons, hpred_sort v g h0.1 h0.2]
      by_cases hp : pred v g = true
      · simp only [hp, ↓reduceIte, List.map_cons, ih hgs']
      · have hpf := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, ih hgs']
  have hge2' : ∀ x14 ∉ x3, (2 : ℕ) ≤ (List.filter (pred ↑x14) C'.gates).length := by
    intro x14 hx14
    dsimp [C']
    rw [hfilter_map ↑x14 x5.gates hfan', List.length_map]
    exact hge2 x14 hx14
  have hex2' : ∃ x15 ∉ x3,
      have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (pred ↑x15) C'.gates;
      x16.length = (2 : ℕ) ∧ ∃ x17 ∈ x16, x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or := by
    rcases hex2 with ⟨x15, hx15, hlen16, x17, hx17, hop17⟩
    refine ⟨x15, hx15, ?_, sortAO x17, ?_, ?_⟩
    · dsimp [C']; rw [hfilter_map ↑x15 x5.gates hfan', List.length_map]; exact hlen16
    · dsimp [C']; rw [hfilter_map ↑x15 x5.gates hfan']; exact List.mem_map_of_mem hx17
    · rw [hsort_op]; exact hop17
  have hres := hCanon x1 x2 x3 x4 C' hdeg hgirth hno3 ⟨eu, ew, hedg⟩ hx4 hC'_fan
    (by rw [hC'_sz]; exact hx5_pos) (by rw [hC'_sz]; exact hx5_out) hC'_pair hfun' hmin' hge2' hex2'
  rw [hC'_sz] at hres
  exact hres
