import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18539_2
    (hNonConst :
      ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)),
        (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) →
        (∃ (x7 x8 : Fin x1), x2.Adj x7 x8) →
        (∃ (x8 x9 : Fin x1), x3.Adj x8 x9) →
        ∀ (v : Fin x1), ∃ (u w : Fin x1), (x2 ⊔ x3).Adj u w ∧ u ≠ v ∧ w ≠ v)
    (hNorm : ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x2.Adj] [x5 : DecidableRel x3.Adj], (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9) → (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) → (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → ∀ (x11 : ℕ), (∃ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C ∧ (0 : ℕ) < C.size ∧ C.output = x1 + (C.size - (1 : ℕ)) ∧ C.size ≤ x11 ∧ ∀ (f : Fin x1 → Bool), C.eval (List.ofFn f) = PEqualNP.MetaComplexity.NestedCover.graphFun (x2 ⊔ x3) ∅ f) → ∃ (x13 : ℕ) (x14 : ℕ), x13 + x14 + (1 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x13 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅) x14) :
    ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x2.Adj] [x5 : DecidableRel x3.Adj], (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9) → (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) → (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun (x2 ⊔ x3) ∅) x11 → ∃ (x13 : ℕ) (x14 : ℕ), x13 + x14 + (1 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x13 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅) x14 := by
  intro x1 x2 x3 x4 x5 hdisj hne2 hne3 hdeg hgirth x11 hhas
  rcases hhas with ⟨C, hfan, hsz, heval⟩
  rcases hne2 with ⟨e1, e2, he12⟩
  rcases hne3 with ⟨f1, f2, hf12⟩
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
  have hx1_le : x1 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < x1 := Nat.lt_of_not_le hlt
    obtain ⟨u, w, hadj, hnu, hnw⟩ := hNonConst x1 x2 x3 hdisj ⟨e1, e2, he12⟩ ⟨f1, f2, hf12⟩ ⟨C.output, hlt'⟩
    let fn : Fin x1 → Bool := fun z => Decidable.decide (z = u ∨ z = w)
    have htru : C.eval (List.ofFn fn) = true := by
      rw [heval fn]
      dsimp only [PEqualNP.MetaComplexity.NestedCover.graphFun]
      have hrhs : decide (∃ u1 v1, (x2 ⊔ x3).Adj u1 v1 ∧ fn u1 = true ∧ fn v1 = true) = true :=
        decide_eq_true ⟨u, w, hadj, by simp [fn], by simp [fn]⟩
      rw [hrhs, Bool.or_true]
    have hfls : C.eval (List.ofFn fn) = false := by
      change (C.gates.foldl step (List.ofFn fn)).getD C.output false = false
      rw [hfold_getD C.gates (List.ofFn fn) C.output (by simp [hlt']),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt']), Option.getD_some,
        List.getElem_ofFn]
      have hnu' : C.output ≠ ↑u := fun h => hnu (Fin.ext h.symm)
      have hnw' : C.output ≠ ↑w := fun h => hnw (Fin.ext h.symm)
      simp [fn, Fin.ext_iff, hnu', hnw']
    rw [hfls] at htru; cases htru
  have hout_lt : C.output < x1 + C.size := by
    by_contra hge
    have hle : x1 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let fn : Fin x1 → Bool := fun z => Decidable.decide (z = e1 ∨ z = e2)
    have htru : C.eval (List.ofFn fn) = true := by
      rw [heval fn]
      dsimp only [PEqualNP.MetaComplexity.NestedCover.graphFun]
      have hrhs : decide (∃ u1 v1, (x2 ⊔ x3).Adj u1 v1 ∧ fn u1 = true ∧ fn v1 = true) = true :=
        decide_eq_true ⟨e1, e2, Or.inl he12, by simp [fn], by simp [fn]⟩
      rw [hrhs, Bool.or_true]
    have hlen_w : (C.wires (List.ofFn fn)).length = x1 + C.size := by
      change (C.gates.foldl step (List.ofFn fn)).length = x1 + C.gates.length
      rw [hfold_len, List.length_ofFn]
    have hfls : C.eval (List.ofFn fn) = false := by
      change (C.wires (List.ofFn fn)).getD C.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfls] at htru; cases htru
  let m : ℕ := C.output - x1 + 1
  have hC_sz : C.size = C.gates.length := rfl
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ C.gates.length := by omega
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
    ⟨List.zipWith (fun j g => normFan2 (x1 + j) g) (List.range m) (C.gates.take m), C.output⟩
  have hC'_len : C'.gates.length = m := by
    dsimp [C']
    rw [List.length_zipWith, List.length_range, List.length_take, Nat.min_eq_left hm_le, Nat.min_self]
  have hC'_sz : C'.size = m := hC'_len
  have hC'_pos : 0 < C'.size := by omega
  have hC'_out : C'.output = x1 + (C'.size - 1) := by dsimp [C'] at *; omega
  have hfan' : ∀ g ∈ C.gates,
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
    have hj_full : j < C.gates.length := lt_of_lt_of_le hj hm_le
    have h0 := hfan' C.gates[j] (List.getElem_mem hj_full)
    have hp := hnorm_prop (x1 + j) C.gates[j] h0.1 h0.2
    exact ⟨hp.1, hp.2.1⟩
  have hC'_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C' := by
    intro j hj i hi
    rw [hC'_len] at hj
    have hj_full : j < C.gates.length := lt_of_lt_of_le hj hm_le
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = normFan2 (x1 + j) C.gates[j] := by
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hj,
        List.getElem?_take_of_lt hj, List.getElem?_eq_getElem hj_full]
      rfl
    rw [hgate] at hi
    have h0 := hfan' C.gates[j] (List.getElem_mem hj_full)
    exact (hnorm_prop (x1 + j) C.gates[j] h0.1 h0.2).2.2 i hi
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
      ((List.zipWith (fun j g => normFan2 (x1 + j) g) (List.range k) (C.gates.take k)).foldl step inp) =
      ((C.gates.take k).foldl step inp) := by
    intro k hk inp hlen_inp
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hk_full : k < C.gates.length := lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk) hm_le
      have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
      have ht : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
        List.take_succ_eq_append_getElem hk_full
      have hlen_rk : (List.range k).length = (C.gates.take k).length := by
        rw [List.length_range, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [hr, ht, List.zipWith_append hlen_rk, List.foldl_append, List.foldl_append, ih hk']
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
      have hlen_pre : ((C.gates.take k).foldl step inp).length = x1 + k := by
        rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [← hlen_pre]
      have h0 := hfan' C.gates[k] (List.getElem_mem hk_full)
      exact hstep_norm ((C.gates.take k).foldl step inp) C.gates[k] h0.1 h0.2
  have hC'_eval : ∀ f : Fin x1 → Bool, C'.eval (List.ofFn f) = PEqualNP.MetaComplexity.NestedCover.graphFun (x2 ⊔ x3) ∅ f := by
    intro f
    rw [← heval f]
    let inp := List.ofFn f
    have hlen_inp : inp.length = x1 := by simp [inp]
    have hw_eq : C'.wires inp = (C.gates.take m).foldl step inp := by
      change (List.zipWith (fun j g => normFan2 (x1 + j) g) (List.range m) (C.gates.take m)).foldl step inp = _
      exact hprefix_eq m (le_refl m) inp hlen_inp
    have hC_split : C.wires inp = (C.gates.drop m).foldl step (C'.wires inp) := by
      rw [hw_eq]
      change C.gates.foldl step inp = (C.gates.drop m).foldl step ((C.gates.take m).foldl step inp)
      rw [← List.foldl_append, List.take_append_drop]
    have hout_lt_C' : C.output < (C'.wires inp).length := by
      rw [hw_eq, hfold_len, hlen_inp, List.length_take, Nat.min_eq_left hm_le]
      dsimp [m]; omega
    change (C'.wires inp).getD C.output false = (C.wires inp).getD C.output false
    rw [hC_split, hfold_getD (C.gates.drop m) (C'.wires inp) C.output hout_lt_C']
  exact hNorm x1 x2 x3 hdisj ⟨e1, e2, he12⟩ ⟨f1, f2, hf12⟩ hdeg hgirth x11
    ⟨C', hC'_fan, hC'_RB, hC'_pos, hC'_out, by rw [hC'_sz]; omega, hC'_eval⟩
