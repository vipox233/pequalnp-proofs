import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7846_1
    (hIso :
      ∀ (x1 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1),
        x4 = x3.deleteEdges (x3.incidenceSet x5) → ∀ (u : Fin x1), ¬x4.Adj x5 u ∧ ¬x4.Adj u x5)
    (hCleanCirc :
      ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool),
        (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) →
        (x3.neighborSet x5).ncard = (3 : ℕ) →
        (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        x4 = x3.deleteEdges (x3.incidenceSet x5) →
        (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
        (∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo C ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C ∧
          C.size ≤ x2 ∧
          (∀ (f : Fin x1 → Bool), C.eval (List.ofFn f) = x6 f) ∧
          C.output ≠ ↑x5 ∧
          ∀ g ∈ C.gates, ↑x5 ∉ g.inputs) →
        ∃ (x13 : List PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ),
          (∀ x15 ∈ x13, (x15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x15.inputs.length ≤ (2 : ℕ)) ∧
          x13.length ≤ x2 ∧
          (∀ (x15 : Fin x1 → Bool), { gates := x13, output := x14 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x15) = Bool.true ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x4.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧
          ∀ (x15 : Fin x13.length) (x16 : Fin x1 → Bool), (x13.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → ({ gates := x13, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x16)).getD (x1 + ↑x15) Bool.false = Bool.true → ∃ (x19 : Fin x1) (x20 : Fin x1), x4.Adj x19 x20 ∧ x16 x19 = Bool.true ∧ x16 x20 = Bool.true) :
    ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool), (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) → (x3.neighborSet x5).ncard = (3 : ℕ) → (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → x4 = x3.deleteEdges (x3.incidenceSet x5) → (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 → ∃ (x13 : List PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ), (∀ x15 ∈ x13, (x15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x15.inputs.length ≤ (2 : ℕ)) ∧ x13.length ≤ x2 ∧ (∀ (x15 : Fin x1 → Bool), { gates := x13, output := x14 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x15) = Bool.true ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x4.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ ∀ (x15 : Fin x13.length) (x16 : Fin x1 → Bool), (x13.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → ({ gates := x13, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x16)).getD (x1 + ↑x15) Bool.false = Bool.true → ∃ (x19 : Fin x1) (x20 : Fin x1), x4.Adj x19 x20 ∧ x16 x19 = Bool.true ∧ x16 x20 = Bool.true := by
  intro x1 x2 x3 x4 x5 x6 hdeg hdeg5 hgirth hdel hx6 hhas
  rcases hhas with ⟨C, hfan, hsz, heval⟩
  have hiso5 : ∀ (u : Fin x1), ¬x4.Adj x5 u ∧ ¬x4.Adj u x5 := hIso x1 x3 x4 x5 hdel
  have hx6_upd : ∀ (f : Fin x1 → Bool), x6 (Function.update f x5 false) = x6 f := by
    intro f
    have hiff : x6 (Function.update f x5 false) = true ↔ x6 f = true := by
      rw [hx6, hx6]
      constructor
      · rintro ⟨u, v, hadj, hu, hv⟩
        refine ⟨u, v, hadj, ?_, ?_⟩
        · by_cases hux : u = x5
          · subst hux; exact absurd hadj (hiso5 v).1
          · rw [Function.update_of_ne hux] at hu; exact hu
        · by_cases hvx : v = x5
          · subst hvx; exact absurd hadj (hiso5 u).2
          · rw [Function.update_of_ne hvx] at hv; exact hv
      · rintro ⟨u, v, hadj, hu, hv⟩
        refine ⟨u, v, hadj, ?_, ?_⟩
        · by_cases hux : u = x5
          · subst hux; exact absurd hadj (hiso5 v).1
          · rw [Function.update_of_ne hux]; exact hu
        · by_cases hvx : v = x5
          · subst hvx; exact absurd hadj (hiso5 u).2
          · rw [Function.update_of_ne hvx]; exact hv
    cases h1 : x6 (Function.update f x5 false) <;> cases h2 : x6 f
    · rfl
    · exfalso; rw [h1, h2] at hiff; exact absurd (hiff.mpr rfl) Bool.false_ne_true
    · exfalso; rw [h1, h2] at hiff; exact absurd (hiff.mp rfl) Bool.false_ne_true
    · rfl
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
  by_cases hout : C.output = ↑x5
  · have hx6_false : ∀ (f : Fin x1 → Bool), x6 f = false := by
      intro f
      rw [← hx6_upd f, ← heval (Function.update f x5 false)]
      change (C.wires (List.ofFn (Function.update f x5 false))).getD C.output false = false
      change (C.gates.foldl step (List.ofFn (Function.update f x5 false))).getD C.output false = false
      have hlen_fn : C.output < (List.ofFn (Function.update f x5 false)).length := by
        rw [List.length_ofFn, hout]; exact x5.isLt
      rw [hfold_getD C.gates (List.ofFn (Function.update f x5 false)) C.output hlen_fn]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_fn, Option.getD_some, List.getElem_ofFn]
      have hfin : (⟨C.output, by rw [hout]; exact x5.isLt⟩ : Fin x1) = x5 := Fin.ext hout
      rw [hfin, Function.update_self]
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], x1⟩
    have hClean : ∃ (C0 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C0 ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C0 ∧
        C0.size ≤ x2 ∧
        (∀ (f : Fin x1 → Bool), C0.eval (List.ofFn f) = x6 f) ∧
        C0.output ≠ ↑x5 ∧
        ∀ g ∈ C0.gates, ↑x5 ∉ g.inputs := by
      refine ⟨C', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; cases hj
      · exact Nat.zero_le x2
      · intro f
        rw [hx6_false f]
        change ((List.ofFn f).getD x1 false) = false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
        rfl
      · exact Nat.ne_of_gt x5.isLt
      · intro g hg; cases hg
    exact hCleanCirc x1 x2 x3 x4 x5 x6 hdeg hdeg5 hgirth hdel hx6 hClean
  · let good : ℕ → ℕ → ℕ → Bool := fun b dead i => Decidable.decide (i < b ∧ i ≠ dead)
    let normFan2 : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun b dead g =>
      PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate) g.op
        (List.casesOn g.inputs ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ fun a r1 =>
          List.casesOn r1
            (if good b dead a then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a]⟩ else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
            fun c _ =>
              if good b dead a then
                if good b dead c then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩
                else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
              else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        (List.casesOn g.inputs ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ fun a r1 =>
          List.casesOn r1
            (if good b dead a then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
            fun c _ =>
              if good b dead a then
                if good b dead c then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, c]⟩
                else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩
              else
                if good b dead c then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [c]⟩
                else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        (List.casesOn g.inputs ⟨PEqualNP.CircuitLowerBounds.GateOp.not, []⟩ fun a _ =>
          if good b dead a then ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩
          else ⟨PEqualNP.CircuitLowerBounds.GateOp.not, []⟩)
        (fun _ => g)
        g
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨List.zipWith (fun j g => normFan2 (x1 + j) ↑x5 g) (List.range C.gates.length) C.gates, C.output⟩
    have hC'_len : C'.gates.length = C.gates.length := by
      dsimp [C']; rw [List.length_zipWith, List.length_range, Nat.min_self]
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
    have hnorm_prop : ∀ (b dead : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        g.inputs.length ≤ 2 →
        ((normFan2 b dead g).op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) ∧
        (normFan2 b dead g).inputs.length ≤ 2 ∧
        (∀ i ∈ (normFan2 b dead g).inputs, i < b ∧ i ≠ dead) := by
      intro b dead g hop hlen_g
      have hgood : ∀ (i : ℕ), good b dead i = true → i < b ∧ i ≠ dead := by
        intro i hi; dsimp [good] at hi; exact of_decide_eq_true hi
      rcases g with ⟨op, is⟩
      rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
      · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
        · dsimp [normFan2]; exact ⟨Set.mem_insert _ _, by simp, fun _ h => by simp at h⟩
        · dsimp [normFan2]; by_cases ha : good b dead a = true
          · rw [if_pos ha]; exact ⟨Set.mem_insert _ _, by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hgood a ha⟩
          · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · dsimp [normFan2]; by_cases ha : good b dead a = true <;> by_cases hc : good b dead c = true
          · rw [if_pos ha, if_pos hc]; exact ⟨Set.mem_insert _ _, by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with hi | hi <;> rw [hi]; exact hgood a ha; exact hgood c hc⟩
          · rw [if_pos ha, if_neg hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
          · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
          · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · simp at hlen_g
      · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
        · dsimp [normFan2]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · dsimp [normFan2]; by_cases ha : good b dead a = true
          · rw [if_pos ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hgood a ha⟩
          · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · dsimp [normFan2]; by_cases ha : good b dead a = true <;> by_cases hc : good b dead c = true
          · rw [if_pos ha, if_pos hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with hi | hi <;> rw [hi]; exact hgood a ha; exact hgood c hc⟩
          · rw [if_pos ha, if_neg hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hgood a ha⟩
          · rw [if_neg ha, if_pos hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hgood c hc⟩
          · rw [if_neg ha, if_neg hc]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), by simp, fun _ h => by simp at h⟩
        · simp at hlen_g
      · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
        · dsimp [normFan2]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun _ h => by simp at h⟩
        · dsimp [normFan2]; by_cases ha : good b dead a = true
          · rw [if_pos ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hgood a ha⟩
          · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun _ h => by simp at h⟩
        · dsimp [normFan2]; by_cases ha : good b dead a = true
          · rw [if_pos ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; exact hgood a ha⟩
          · rw [if_neg ha]; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), by simp, fun _ h => by simp at h⟩
        · simp at hlen_g
    have hC'_fan : PEqualNP.MetaComplexity.FanInTwo C' := by
      intro g hg
      dsimp [C'] at hg
      rw [List.mem_iff_getElem] at hg
      rcases hg with ⟨j, hj, rfl⟩
      rw [List.getElem_zipWith, List.getElem_range]
      rw [List.length_zipWith, List.length_range, Nat.min_self] at hj
      have h0 := hfan' C.gates[j] (List.getElem_mem hj)
      have hp := hnorm_prop (x1 + j) ↑x5 C.gates[j] h0.1 h0.2
      exact ⟨hp.1, hp.2.1⟩
    have hC'_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C' := by
      intro j hj i hi
      rw [hC'_len] at hj
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = normFan2 (x1 + j) ↑x5 C.gates[j] := by
        dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
        rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hj,
          List.getElem?_eq_getElem hj]
        rfl
      rw [hgate] at hi
      have h0 := hfan' C.gates[j] (List.getElem_mem hj)
      exact (hnorm_prop (x1 + j) ↑x5 C.gates[j] h0.1 h0.2).2.2 i hi |>.1
    have hC'_no_dead : ∀ g ∈ C'.gates, ↑x5 ∉ g.inputs := by
      intro g hg hmem
      dsimp [C'] at hg
      rw [List.mem_iff_getElem] at hg
      rcases hg with ⟨j, hj, rfl⟩
      rw [List.getElem_zipWith, List.getElem_range] at hmem
      rw [List.length_zipWith, List.length_range, Nat.min_self] at hj
      have h0 := hfan' C.gates[j] (List.getElem_mem hj)
      exact (hnorm_prop (x1 + j) ↑x5 C.gates[j] h0.1 h0.2).2.2 ↑x5 hmem |>.2 rfl
    have hstep_inv : ∀ (w1 w2 : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
        w1.length = w2.length →
        w2.getD ↑x5 false = false →
        (∀ i : ℕ, i ≠ ↑x5 → w1.getD i false = w2.getD i false) →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        g.inputs.length ≤ 2 →
        (normFan2 w2.length ↑x5 g).op.eval ((normFan2 w2.length ↑x5 g).inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      intro w1 w2 g hlen_w hdead hag hop hlen_g
      have hbg : ∀ (i : ℕ), good w2.length ↑x5 i = false → w2.getD i false = false := by
        intro i hi
        dsimp [good] at hi
        have hnot : ¬(i < w2.length ∧ i ≠ ↑x5) := of_decide_eq_false hi
        by_cases heq : i = ↑x5
        · rw [heq]; exact hdead
        · have hge : ¬(i < w2.length) := fun hlt => hnot ⟨hlt, heq⟩
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]; rfl
      have hgg : ∀ (i : ℕ), good w2.length ↑x5 i = true → w1.getD i false = w2.getD i false := by
        intro i hi
        dsimp [good] at hi
        exact hag i (of_decide_eq_true hi).2
      rcases g with ⟨op, is⟩
      rcases hop with hop | hop | hop <;> dsimp only at hop hlen_g <;> subst hop
      · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
        · rfl
        · dsimp [normFan2]
          by_cases ha : good w2.length ↑x5 a = true
          · simp only [ha, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha]
          · have haf := Bool.eq_false_iff.mpr ha
            simp only [haf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf]; rfl
        · dsimp [normFan2]
          by_cases ha : good w2.length ↑x5 a = true <;> by_cases hc : good w2.length ↑x5 c = true
          · simp only [ha, hc, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha, hgg c hc]
          · have hcf := Bool.eq_false_iff.mpr hc
            simp only [ha, hcf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg c hcf]
            cases (w2.getD a false) <;> rfl
          · have haf := Bool.eq_false_iff.mpr ha
            simp only [haf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf]; rfl
          · have haf := Bool.eq_false_iff.mpr ha
            have hcf := Bool.eq_false_iff.mpr hc
            simp only [haf, hcf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf, hbg c hcf]; rfl
        · simp at hlen_g
      · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
        · rfl
        · dsimp [normFan2]
          by_cases ha : good w2.length ↑x5 a = true
          · simp only [ha, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha]
          · have haf := Bool.eq_false_iff.mpr ha
            simp only [haf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf]; rfl
        · dsimp [normFan2]
          by_cases ha : good w2.length ↑x5 a = true <;> by_cases hc : good w2.length ↑x5 c = true
          · simp only [ha, hc, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha, hgg c hc]
          · have hcf := Bool.eq_false_iff.mpr hc
            simp only [ha, hcf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha, hbg c hcf]
            cases (w2.getD a false) <;> rfl
          · have haf := Bool.eq_false_iff.mpr ha
            simp only [haf, hc, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf, hgg c hc]
            cases (w2.getD c false) <;> rfl
          · have haf := Bool.eq_false_iff.mpr ha
            have hcf := Bool.eq_false_iff.mpr hc
            simp only [haf, hcf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf, hbg c hcf]; rfl
        · simp at hlen_g
      · rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
        · rfl
        · dsimp [normFan2]
          by_cases ha : good w2.length ↑x5 a = true
          · simp only [ha, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha]
          · have haf := Bool.eq_false_iff.mpr ha
            simp only [haf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf]; rfl
        · dsimp [normFan2]
          by_cases ha : good w2.length ↑x5 a = true
          · simp only [ha, ↓reduceIte, List.map_cons, List.map_nil, hgg a ha]; rfl
          · have haf := Bool.eq_false_iff.mpr ha
            simp only [haf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hbg a haf]; rfl
        · simp at hlen_g
    have hprefix_inv : ∀ (f : Fin x1 → Bool) (k : ℕ) (hk : k ≤ C.gates.length),
        let w1 := (List.zipWith (fun j g => normFan2 (x1 + j) ↑x5 g) (List.range k) (C.gates.take k)).foldl step (List.ofFn f)
        let w2 := (C.gates.take k).foldl step (List.ofFn (Function.update f x5 false))
        w1.length = x1 + k ∧ w2.length = x1 + k ∧ w2.getD ↑x5 false = false ∧ (∀ i : ℕ, i ≠ ↑x5 → w1.getD i false = w2.getD i false) := by
      intro f k hk
      induction k with
      | zero =>
        refine ⟨by simp, by simp, ?_, ?_⟩
        · have hlt : (↑x5 : ℕ) < (List.ofFn (Function.update f x5 false)).length := by simp
          simp only [List.take_zero, List.foldl_nil]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn,
            Fin.eta, Function.update_self]
        · intro i hi
          simp only [List.range_zero, List.zipWith_nil_left, List.take_zero, List.foldl_nil]
          by_cases hil : i < x1
          · have hlt1 : i < (List.ofFn f).length := by simp [hil]
            have hlt2 : i < (List.ofFn (Function.update f x5 false)).length := by simp [hil]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt1, Option.getD_some, List.getElem_ofFn,
              List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2, Option.getD_some, List.getElem_ofFn]
            have hfin_ne : (⟨i, hil⟩ : Fin x1) ≠ x5 := fun h => hi (congrArg Fin.val h)
            rw [Function.update_of_ne hfin_ne]
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      | succ k ih =>
        have hk_le : k ≤ C.gates.length := Nat.le_of_succ_le hk
        have hk_lt : k < C.gates.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        rcases ih hk_le with ⟨hlen1, hlen2, hdead2, hag⟩
        have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
        have ht : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hk_lt
        have hlen_rk : (List.range k).length = (C.gates.take k).length := by
          rw [List.length_range, List.length_take, Nat.min_eq_left hk_le]
        set w1 := (List.zipWith (fun j g => normFan2 (x1 + j) ↑x5 g) (List.range k) (C.gates.take k)).foldl step (List.ofFn f)
        set w2 := (C.gates.take k).foldl step (List.ofFn (Function.update f x5 false))
        have h0 := hfan' C.gates[k] (List.getElem_mem hk_lt)
        have hbit : (normFan2 (x1 + k) ↑x5 C.gates[k]).op.eval ((normFan2 (x1 + k) ↑x5 C.gates[k]).inputs.map fun i => w1.getD i false) =
            C.gates[k].op.eval (C.gates[k].inputs.map fun i => w2.getD i false) := by
          rw [← hlen2]
          exact hstep_inv w1 w2 C.gates[k] (by omega) hdead2 hag h0.1 h0.2
        have hrew1 : (List.zipWith (fun j g => normFan2 (x1 + j) ↑x5 g) (List.range (k + 1)) (C.gates.take (k + 1))).foldl step (List.ofFn f) =
            step w1 (normFan2 (x1 + k) ↑x5 C.gates[k]) := by
          rw [hr, ht, List.zipWith_append hlen_rk, List.foldl_append]
          simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
          rfl
        have hrew2 : (C.gates.take (k + 1)).foldl step (List.ofFn (Function.update f x5 false)) =
            step w2 C.gates[k] := by
          rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hrew1, hrew2]
        refine ⟨?_, ?_, ?_, ?_⟩
        · dsimp [step]; rw [List.length_append, hlen1]; rfl
        · dsimp [step]; rw [List.length_append, hlen2]; rfl
        · dsimp [step]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen2]; exact Nat.lt_of_lt_of_le x5.isLt (Nat.le_add_right x1 k))]
          exact hdead2
        · intro i hi
          by_cases hlt : i < x1 + k
          · dsimp only [step]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen1]; exact hlt),
              List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen2]; exact hlt)]
            exact hag i hi
          · by_cases heq : i = x1 + k
            · subst heq
              dsimp only [step]
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hlen1.le, hlen1, Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some,
                List.getD_eq_getElem?_getD, List.getElem?_append_right hlen2.le, hlen2, Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some]
              exact hbit
            · dsimp only [step]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, hlen1, List.length_singleton]; omega),
                List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, hlen2, List.length_singleton]; omega)]
    have hC'_eval : ∀ (f : Fin x1 → Bool), C'.eval (List.ofFn f) = x6 f := by
      intro f
      have hp := hprefix_inv f C.gates.length (le_refl C.gates.length)
      simp only [List.take_length] at hp
      have heq_eval : C'.eval (List.ofFn f) = C.eval (List.ofFn (Function.update f x5 false)) := by
        change ((C'.gates).foldl step (List.ofFn f)).getD C.output false =
          ((C.gates).foldl step (List.ofFn (Function.update f x5 false))).getD C.output false
        exact hp.2.2.2 C.output hout
      rw [heq_eval, heval (Function.update f x5 false), hx6_upd f]
    have hClean : ∃ (C0 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C0 ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 C0 ∧
        C0.size ≤ x2 ∧
        (∀ (f : Fin x1 → Bool), C0.eval (List.ofFn f) = x6 f) ∧
        C0.output ≠ ↑x5 ∧
        ∀ g ∈ C0.gates, ↑x5 ∉ g.inputs :=
      ⟨C', hC'_fan, hC'_RB, by change C'.gates.length ≤ x2; rw [hC'_len]; exact hsz, hC'_eval, hout, hC'_no_dead⟩
    exact hCleanCirc x1 x2 x3 x4 x5 x6 hdeg hdeg5 hgirth hdel hx6 hClean
