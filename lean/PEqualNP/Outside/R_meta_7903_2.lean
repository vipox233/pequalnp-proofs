import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7903_2
    (hNonStarDeg3 :
      ∀ (x1 : ℕ) (x3 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)),
        (∀ x7 ∉ x5, (x3.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x5) →
        (∃ (x10 x11 : Fin x1), x3.Adj x10 x11) →
        ∀ (v : Fin x1), ∃ (u w : Fin x1), x3.Adj u w ∧ u ≠ v ∧ w ≠ v)
    (hNorm :
      ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x3.Adj] (x5 : Finset (Fin x1)) (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ x7 ∉ x5, (x3.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x5) →
        (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →
        (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x6 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x6 →
        (0 : ℕ) < x6.size →
        x6.output = x1 + (x6.size - (1 : ℕ)) →
        PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 x5 →
        ∀ x14 ∉ x5,
        ∀ (x16 : PEqualNP.CircuitLowerBounds.Gate),
          List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x14) x6.gates = [x16] →
          x16.op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (∀ (x19 : Fin x1), x19 ≠ x14 → x19 ∉ x5 → x16.inputs ≠ [↑x14, ↑x19] ∧ x16.inputs ≠ [↑x19, ↑x14]) →
          x5.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x3.Adj] (x5 : Finset (Fin x1)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x7 ∉ x5, (x3.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x5) → (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) → (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 x5 → ∀ x14 ∉ x5, ∀ (x16 : PEqualNP.CircuitLowerBounds.Gate), List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x14) x6.gates = [x16] → x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x19 : Fin x1), x19 ≠ x14 → x19 ∉ x5 → x16.inputs ≠ [↑x14, ↑x19] ∧ x16.inputs ≠ [↑x19, ↑x14]) → x5.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 x6 hdeg hgirth hno5 hedge hvc hmin hfun x14 hx14 x16 hfilt hop16 hno2
  rcases hmin with ⟨hfan, hmin_sz⟩
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
  have hx1_le : x1 ≤ x6.output := by
    by_contra hlt
    have hlt' : x6.output < x1 := Nat.lt_of_not_le hlt
    obtain ⟨u, w, hadj, hnu, hnw⟩ := hNonStarDeg3 x1 x3 x5 hdeg hno5 ⟨eu, ew, hedg⟩ ⟨x6.output, hlt'⟩
    let f : Fin x1 → Bool := fun t => Decidable.decide (t = u ∨ t = w)
    have hfx := congrFun hfun f
    have hrhs : decide (∃ u1 v1, x3.Adj u1 v1 ∧ f u1 = true ∧ f v1 = true) = true :=
      decide_eq_true ⟨u, w, hadj, by simp [f], by simp [f]⟩
    dsimp only [PEqualNP.MetaComplexity.NestedCover.graphFun] at hfx
    rw [hrhs, Bool.or_true] at hfx
    have htru : x6.eval (List.ofFn f) = true := hfx
    have hfls : x6.eval (List.ofFn f) = false := by
      change (x6.gates.foldl step (List.ofFn f)).getD x6.output false = false
      rw [hfold_getD x6.gates (List.ofFn f) x6.output (by simp [hlt']),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt']), Option.getD_some,
        List.getElem_ofFn]
      have hnu' : x6.output ≠ ↑u := fun h => hnu (Fin.ext h.symm)
      have hnw' : x6.output ≠ ↑w := fun h => hnw (Fin.ext h.symm)
      simp [f, Fin.ext_iff, hnu', hnw']
    rw [hfls] at htru; cases htru
  have hout_lt : x6.output < x1 + x6.size := by
    by_contra hge
    have hle : x1 + x6.size ≤ x6.output := Nat.le_of_not_lt hge
    let f : Fin x1 → Bool := fun t => Decidable.decide (t = eu ∨ t = ew)
    have hfx := congrFun hfun f
    have hrhs : decide (∃ u1 v1, x3.Adj u1 v1 ∧ f u1 = true ∧ f v1 = true) = true :=
      decide_eq_true ⟨eu, ew, hedg, by simp [f], by simp [f]⟩
    dsimp only [PEqualNP.MetaComplexity.NestedCover.graphFun] at hfx
    rw [hrhs, Bool.or_true] at hfx
    have htru : x6.eval (List.ofFn f) = true := hfx
    have hlen_w : (x6.wires (List.ofFn f)).length = x1 + x6.size := by
      change (x6.gates.foldl step (List.ofFn f)).length = x1 + x6.gates.length
      rw [hfold_len, List.length_ofFn]
    have hfls : x6.eval (List.ofFn f) = false := by
      change (x6.wires (List.ofFn f)).getD x6.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfls] at htru; cases htru
  let m : ℕ := x6.output - x1 + 1
  have hx6_sz : x6.size = x6.gates.length := rfl
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ x6.gates.length := by omega
  let normFan2 : ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun b g =>
    PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate) g.op
      (List.casesOn g.inputs ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ fun a r1 =>
        List.casesOn r1
          (if a < b then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a]⟩ else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
          fun c _ =>
            if a < b then
              if c < b then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩
              else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
            else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
      (List.casesOn g.inputs ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ fun a r1 =>
        List.casesOn r1
          (if a < b then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
          fun c _ =>
            if a < b then
              if c < b then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, c]⟩
              else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩
            else
              if c < b then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [c]⟩
              else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
      (List.casesOn g.inputs ⟨PEqualNP.CircuitLowerBounds.GateOp.not, []⟩ fun a _ =>
        if a < b then ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩
        else ⟨PEqualNP.CircuitLowerBounds.GateOp.not, []⟩)
      (fun _ => g)
      g
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨List.zipWith (fun j g => normFan2 (x1 + j) g) (List.range m) (x6.gates.take m), x6.output⟩
  have hC'_len : C'.gates.length = m := by
    dsimp [C']
    rw [List.length_zipWith, List.length_range, List.length_take, Nat.min_eq_left hm_le, Nat.min_self]
  have hC'_sz : C'.size = m := hC'_len
  have hC'_pos : 0 < C'.size := by omega
  have hC'_out : C'.output = x1 + (C'.size - 1) := by dsimp [C'] at *; omega
  have hfan' : ∀ g ∈ x6.gates,
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
  have hnorm_prop : ∀ (b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      g.inputs.length ≤ 2 →
      ((normFan2 b g).op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) ∧
      (normFan2 b g).inputs.length ≤ 2 ∧
      (∀ i ∈ (normFan2 b g).inputs, i < b) := by
    intro b g hop hlen_g
    rcases g with ⟨op, is⟩
    rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · dsimp [normFan2]; exact ⟨Set.mem_insert _ _, by simp, fun _ h => by simp at h⟩
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact ⟨Set.mem_insert _ _, by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact ha⟩
        · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
      · dsimp [normFan2]; by_cases ha : a < b <;> by_cases hc : c < b
        · rw [if_pos ha, if_pos hc]; exact ⟨Set.mem_insert _ _, by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with hi | hi <;> rw [hi]; exact ha; exact hc⟩
        · rw [if_pos ha, if_neg hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · dsimp [normFan2]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact ha⟩
        · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
      · dsimp [normFan2]; by_cases ha : a < b <;> by_cases hc : c < b
        · rw [if_pos ha, if_pos hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with hi | hi <;> rw [hi]; exact ha; exact hc⟩
        · rw [if_pos ha, if_neg hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact ha⟩
        · rw [if_neg ha, if_pos hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hc⟩
        · rw [if_neg ha, if_neg hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · dsimp [normFan2]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun _ h => by simp at h⟩
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact ha⟩
        · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun _ h => by simp at h⟩
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact ha⟩
        · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun _ h => by simp at h⟩
      · simp at hlen_g
  have hC'_fan : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    dsimp [C'] at hg
    rw [List.mem_iff_getElem] at hg
    rcases hg with ⟨j, hj, rfl⟩
    rw [List.getElem_zipWith, List.getElem_range, List.getElem_take]
    rw [List.length_zipWith, List.length_range, List.length_take, Nat.min_eq_left hm_le, Nat.min_self] at hj
    have hj_full : j < x6.gates.length := lt_of_lt_of_le hj hm_le
    have h0 := hfan' x6.gates[j] (List.getElem_mem hj_full)
    have hp := hnorm_prop (x1 + j) x6.gates[j] h0.1 h0.2
    exact ⟨hp.1, hp.2.1⟩
  have hC'_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C' := by
    intro j hj i hi
    rw [hC'_len] at hj
    have hj_full : j < x6.gates.length := lt_of_lt_of_le hj hm_le
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = normFan2 (x1 + j) x6.gates[j] := by
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hj,
        List.getElem?_take_of_lt hj, List.getElem?_eq_getElem hj_full]
      rfl
    rw [hgate] at hi
    have h0 := hfan' x6.gates[j] (List.getElem_mem hj_full)
    exact (hnorm_prop (x1 + j) x6.gates[j] h0.1 h0.2).2.2 i hi
  have hstep_norm : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      g.inputs.length ≤ 2 →
      step w (normFan2 w.length g) = step w g := by
    intro w g hop hlen_g
    have hnone : ∀ idx : ℕ, ¬ idx < w.length → w.getD idx false = false := by
      intro idx hni
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hni)]; rfl
    rcases g with ⟨op, is⟩
    rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · rfl
      · dsimp [step, normFan2]
        by_cases ha : a < w.length
        · rw [if_pos ha]
        · rw [if_neg ha]; simp only [List.map_nil, List.map_cons, hnone a ha]; rfl
      · dsimp [step, normFan2]
        by_cases ha : a < w.length <;> by_cases hc : c < w.length
        · rw [if_pos ha, if_pos hc]
        · rw [if_pos ha, if_neg hc]; simp only [List.map_nil, List.map_cons, hnone c hc]
          cases (w.getD a false) <;> rfl
        · rw [if_neg ha]; simp only [List.map_nil, List.map_cons, hnone a ha]; rfl
        · rw [if_neg ha]; simp only [List.map_nil, List.map_cons, hnone a ha]; rfl
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · rfl
      · dsimp [step, normFan2]
        by_cases ha : a < w.length
        · rw [if_pos ha]
        · rw [if_neg ha]; simp only [List.map_nil, List.map_cons, hnone a ha]; rfl
      · dsimp [step, normFan2]
        by_cases ha : a < w.length <;> by_cases hc : c < w.length
        · rw [if_pos ha, if_pos hc]
        · rw [if_pos ha, if_neg hc]; simp only [List.map_nil, List.map_cons, hnone c hc]
          cases (w.getD a false) <;> rfl
        · rw [if_neg ha, if_pos hc]; simp only [List.map_nil, List.map_cons, hnone a ha]
          cases (w.getD c false) <;> rfl
        · rw [if_neg ha, if_neg hc]; simp only [List.map_nil, List.map_cons, hnone a ha, hnone c hc]; rfl
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · rfl
      · dsimp [step, normFan2]
        by_cases ha : a < w.length
        · rw [if_pos ha]
        · rw [if_neg ha]; simp only [List.map_nil, List.map_cons, hnone a ha]; rfl
      · dsimp [step, normFan2]
        by_cases ha : a < w.length
        · rw [if_pos ha]; simp only [List.map_cons]; rfl
        · rw [if_neg ha]; simp only [List.map_nil, List.map_cons, hnone a ha]; rfl
      · simp at hlen_g
  have hprefix_eq : ∀ (k : ℕ) (hk : k ≤ m) (inp : List Bool), inp.length = x1 →
      ((List.zipWith (fun j g => normFan2 (x1 + j) g) (List.range k) (x6.gates.take k)).foldl step inp) =
      ((x6.gates.take k).foldl step inp) := by
    intro k hk inp hlen_inp
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hk_full : k < x6.gates.length := lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk) hm_le
      have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
      have ht : x6.gates.take (k + 1) = x6.gates.take k ++ [x6.gates[k]] :=
        List.take_succ_eq_append_getElem hk_full
      have hlen_rk : (List.range k).length = (x6.gates.take k).length := by
        rw [List.length_range, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [hr, ht, List.zipWith_append hlen_rk, List.foldl_append, List.foldl_append, ih hk']
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
      have hlen_pre : ((x6.gates.take k).foldl step inp).length = x1 + k := by
        rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [← hlen_pre]
      have h0 := hfan' x6.gates[k] (List.getElem_mem hk_full)
      exact hstep_norm ((x6.gates.take k).foldl step inp) x6.gates[k] h0.1 h0.2
  have hC'_eval : ∀ f : Fin x1 → Bool, C'.eval (List.ofFn f) = x6.eval (List.ofFn f) := by
    intro f
    let inp := List.ofFn f
    have hlen_inp : inp.length = x1 := by simp [inp]
    have hw_eq : C'.wires inp = (x6.gates.take m).foldl step inp := by
      change (List.zipWith (fun j g => normFan2 (x1 + j) g) (List.range m) (x6.gates.take m)).foldl step inp = _
      exact hprefix_eq m (le_refl m) inp hlen_inp
    have hx6_split : x6.wires inp = (x6.gates.drop m).foldl step (C'.wires inp) := by
      rw [hw_eq]
      change x6.gates.foldl step inp = (x6.gates.drop m).foldl step ((x6.gates.take m).foldl step inp)
      rw [← List.foldl_append, List.take_append_drop]
    have hout_lt_C' : x6.output < (C'.wires inp).length := by
      rw [hw_eq, hfold_len, hlen_inp, List.length_take, Nat.min_eq_left hm_le]
      dsimp [m]; omega
    change (C'.wires inp).getD x6.output false = (x6.wires inp).getD x6.output false
    rw [hx6_split, hfold_getD (x6.gates.drop m) (C'.wires inp) x6.output hout_lt_C']
  have hcf_eq : PEqualNP.MetaComplexity.circuitFun x1 C' = PEqualNP.MetaComplexity.circuitFun x1 x6 := by
    funext f
    exact hC'_eval f
  have hsz_le : x6.size ≤ C'.size := hmin_sz C' hC'_fan hcf_eq
  have hm_eq : m = x6.gates.length := by rw [hC'_sz, hx6_sz] at hsz_le; omega
  have hC'_sz_eq : C'.size = x6.size := by rw [hC'_sz, hx6_sz, hm_eq]
  have hminC' : PEqualNP.MetaComplexity.IsMinimalCircuit x1 C' :=
    ⟨hC'_fan, fun D hDf hDeq => by rw [hC'_sz_eq]; exact hmin_sz D hDf (hDeq.trans hcf_eq)⟩
  let pred : PEqualNP.CircuitLowerBounds.Gate → Bool := fun x17 =>
    (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x14
  have hpred_false : ∀ (b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      g.inputs.length ≤ 2 →
      pred g = false → pred (normFan2 b g) = false := by
    intro b g hop hlen_g hp
    rcases g with ⟨op, is⟩
    rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · exact hp
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact hp
        · rw [if_neg ha]; rfl
      · dsimp [normFan2]; by_cases ha : a < b <;> by_cases hc : c < b
        · rw [if_pos ha, if_pos hc]; exact hp
        · rw [if_pos ha, if_neg hc]; rfl
        · rw [if_neg ha]; rfl
        · rw [if_neg ha]; rfl
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · exact hp
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact hp
        · rw [if_neg ha]; rfl
      · dsimp [normFan2, pred] at hp ⊢
        have hfalse : decide (↑x14 = a) = false ∧ decide (↑x14 = c) = false := by
          change ([a, c].contains ↑x14) = false at hp
          simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.beq_eq_decide_eq,
            Bool.or_eq_false_iff] at hp
          exact hp
        by_cases ha : a < b <;> by_cases hc : c < b
        · rw [if_pos ha, if_pos hc]; exact hp
        · rw [if_pos ha, if_neg hc]; change ([a].contains ↑x14) = false
          simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.beq_eq_decide_eq]; exact hfalse.1
        · rw [if_neg ha, if_pos hc]; change ([c].contains ↑x14) = false
          simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.beq_eq_decide_eq]; exact hfalse.2
        · rw [if_neg ha, if_neg hc]; rfl
      · simp at hlen_g
    · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · exact hp
      · dsimp [normFan2]; by_cases ha : a < b
        · rw [if_pos ha]; exact hp
        · rw [if_neg ha]; rfl
      · dsimp [normFan2, pred] at hp ⊢
        by_cases ha : a < b
        · rw [if_pos ha]; exact hp
        · rw [if_neg ha]; rfl
      · simp at hlen_g
  have hpred_or_keep : ∀ (b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      x1 ≤ b → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → g.inputs.length ≤ 2 →
      pred g = true →
      (normFan2 b g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      pred (normFan2 b g) = true ∧
      (normFan2 b g = g ∨ (normFan2 b g).inputs = [↑x14]) := by
    intro b g hb hop hlen_g hp
    rcases g with ⟨op, is⟩
    dsimp only at hop hlen_g; subst hop
    have h14_lt : (↑x14 : ℕ) < b := lt_of_lt_of_le x14.isLt hb
    rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
    · simp [pred] at hp
    · dsimp [pred] at hp
      have ha_eq : a = ↑x14 := by
        change ([a].contains ↑x14) = true at hp
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.beq_eq_decide_eq,
          decide_eq_true_eq] at hp
        exact hp.symm
      subst ha_eq
      dsimp [normFan2]
      rw [if_pos h14_lt]
      exact ⟨rfl, hp, Or.inl rfl⟩
    · dsimp [pred] at hp
      have hac : a = ↑x14 ∨ c = ↑x14 := by
        change ([a, c].contains ↑x14) = true at hp
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.beq_eq_decide_eq,
          Bool.or_eq_true, decide_eq_true_eq] at hp
        rcases hp with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      dsimp [normFan2]
      by_cases ha : a < b <;> by_cases hc : c < b
      · rw [if_pos ha, if_pos hc]; exact ⟨rfl, hp, Or.inl rfl⟩
      · rw [if_pos ha, if_neg hc]
        have ha_eq : a = ↑x14 := by rcases hac with h | h; exact h; exfalso; rw [h] at hc; exact hc h14_lt
        subst ha_eq
        refine ⟨rfl, ?_, Or.inr rfl⟩
        change ([↑x14].contains ↑x14) = true; simp
      · rw [if_neg ha, if_pos hc]
        have hc_eq : c = ↑x14 := by rcases hac with h | h; exfalso; rw [h] at ha; exact ha h14_lt; exact h
        subst hc_eq
        refine ⟨rfl, ?_, Or.inr rfl⟩
        change ([↑x14].contains ↑x14) = true; simp
      · exfalso; rcases hac with h | h
        · rw [h] at ha; exact ha h14_lt
        · rw [h] at hc; exact hc h14_lt
    · simp at hlen_g
  have hfilt_nil : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (base : ℕ),
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
      List.filter pred gs = [] →
      List.filter pred (List.zipWith (fun j g => normFan2 j g) (List.range' base gs.length) gs) = [] := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro base hgs hf
      have h0 := hgs g List.mem_cons_self
      have hp_false : pred g = false := by
        cases hpg : pred g
        · rfl
        · rw [List.filter_cons, hpg] at hf; cases hf
      simp only [List.filter_cons, hp_false, Bool.false_eq_true, ↓reduceIte] at hf
      simp only [List.length_cons, List.range'_succ, List.zipWith_cons_cons, List.filter_cons,
        hpred_false base g h0.1 h0.2 hp_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (base + 1) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) hf
  have hfilt_single : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (base : ℕ),
      x1 ≤ base →
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
      List.filter pred gs = [x16] →
      ∃ x16' : PEqualNP.CircuitLowerBounds.Gate,
        List.filter pred (List.zipWith (fun j g => normFan2 j g) (List.range' base gs.length) gs) = [x16'] ∧
        x16'.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (x16' = x16 ∨ x16'.inputs = [↑x14]) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ hf; cases hf
    | cons g gs ih =>
      intro base hbase hgs hf
      have h0 := hgs g List.mem_cons_self
      have hgs' : ∀ g' ∈ gs, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
      cases hpg : pred g
      · simp only [List.filter_cons, hpg, Bool.false_eq_true, ↓reduceIte] at hf
        simp only [List.length_cons, List.range'_succ, List.zipWith_cons_cons, List.filter_cons,
          hpred_false base g h0.1 h0.2 hpg, Bool.false_eq_true, ↓reduceIte]
        exact ih (base + 1) (by omega) hgs' hf
      · simp only [List.filter_cons, hpg, ↓reduceIte] at hf
        injection hf with hgx16 hrest_nil
        subst hgx16
        obtain ⟨hop', hpred', hshape⟩ := hpred_or_keep base g hbase hop16 h0.2 hpg
        refine ⟨normFan2 base g, ?_, hop', hshape⟩
        simp only [List.length_cons, List.range'_succ, List.zipWith_cons_cons, List.filter_cons, hpred', ↓reduceIte,
          hfilt_nil gs (base + 1) hgs' hrest_nil]
  have hC'_gates_eq : C'.gates = List.zipWith (fun j g => normFan2 j g) (List.range' x1 x6.gates.length) x6.gates := by
    have htake : x6.gates.take m = x6.gates := List.take_of_length_le hm_eq.ge
    refine List.ext_getElem ?_ ?_
    · rw [hC'_len, List.length_zipWith, List.length_range', Nat.min_self, hm_eq]
    · intro i hi1 hi2
      dsimp [C']
      rw [List.getElem_zipWith, List.getElem_zipWith, List.getElem_range, List.getElem_range', List.getElem_take, Nat.one_mul]
  obtain ⟨x16', hfilt', hop16', hshape'⟩ := hfilt_single x6.gates x1 (le_refl x1) hfan' hfilt
  rw [← hC'_gates_eq] at hfilt'
  have hno2' : ∀ (x19 : Fin x1), x19 ≠ x14 → x19 ∉ x5 → x16'.inputs ≠ [↑x14, ↑x19] ∧ x16'.inputs ≠ [↑x19, ↑x14] := by
    rcases hshape' with rfl | hin
    · exact hno2
    · intro x19 _ _; rw [hin]; exact ⟨by simp, by simp⟩
  have hres := hNorm x1 x2 x3 x5 C' hdeg hgirth hno5 ⟨eu, ew, hedg⟩ hvc hminC' hC'_RB hC'_pos hC'_out (hcf_eq.trans hfun) x14 hx14 x16' hfilt' hop16' hno2'
  rw [hC'_sz_eq] at hres
  exact hres
