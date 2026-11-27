import PEqualNP.Defs

-- Verify the 4-arc {0, 1, 2, 5}, normalize circuit to ReadsBack 26 + truncated output, and eliminate empty-input top AND gate.
theorem PEqualNP.Outside.R_meta_8009_1
    (hQuad :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) =>
        ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ);
      let x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))};
      x3.card = (4 : ℕ) ∧ x4 x3)
    (hNormAnd :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3};
      have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5};
      have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ);
      have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ);
      have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8;
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x7 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 →
        (0 : ℕ) < x7.size →
        x7.output = (26 : ℕ) + (x7.size - (1 : ℕ)) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (1 : ℕ) ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.size - (1 : ℕ))).inputs.length →
        x7.size ≤ (63 : ℕ) →
        (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) →
        (∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x4 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x12 (x2 x12)) = Bool.true) ∨
        ∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x5 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x12) x12) = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
    have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3};
    have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5};
    have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ);
    have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ);
    have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8;
    ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x7 →
      x7.size ≤ (63 : ℕ) →
      (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (26 : ℕ) ≤ x7.output ∧ x7.output < (26 : ℕ) + x7.size →
      (∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x4 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x12 (x2 x12)) = Bool.true) ∨
      ∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x5 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x12) x12) = Bool.true := by
  intro x1 x2 x3 x4 x5 x6 x7 hmono hsz hpos htop
  rcases htop with ⟨htop_op, h26_le, hout_lt⟩
  let m : ℕ := x7.output - 26 + 1
  have hx7_sz : x7.size = x7.gates.length := rfl
  have hm_le : m ≤ x7.gates.length := by omega
  let isAndOp : PEqualNP.CircuitLowerBounds.GateOp → Bool := fun op =>
    PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool)
      op Bool.true Bool.false Bool.false (fun _ => Bool.false) Bool.false
  let normGate : ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun b g =>
    List.casesOn g.inputs g fun a r1 =>
      List.casesOn r1
        (if a < b then g else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        fun c r2 =>
          List.casesOn r2
            (if a < b then
              if c < b then g
              else if isAndOp g.op then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
              else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩
            else
              if c < b then
                if isAndOp g.op then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
                else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [c]⟩
              else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
            (fun _ _ => g)
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨List.zipWith (fun j g => normGate (26 + j) g) (List.range m) (x7.gates.take m), x7.output⟩
  have hC'_len : C'.gates.length = m := by
    dsimp [C']
    rw [List.length_zipWith, List.length_range, List.length_take, Nat.min_eq_left hm_le, Nat.min_self]
  have hC'_sz : C'.size = m := hC'_len
  have hC'_pos : 0 < C'.size := by omega
  have hC'_out : C'.output = 26 + (C'.size - 1) := by
    dsimp [C'] at *
    omega
  have hnorm_prop : ∀ (b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      g.inputs.length ≤ 2 →
      ((normGate b g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (normGate b g).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (normGate b g).inputs.length ≤ 2 ∧
      (∀ i ∈ (normGate b g).inputs, i < b) := by
    intro b g hop hlen_g
    rcases g with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
    · dsimp [normGate]; exact ⟨hop, by simp, fun _ h => by simp at h⟩
    · dsimp [normGate]
      split_ifs with ha
      · exact ⟨hop, by simp, fun i hi => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; rw [hi]; exact ha⟩
      · exact ⟨Or.inr rfl, by simp, fun _ h => by simp at h⟩
    · dsimp [normGate]
      by_cases ha : a < b <;> by_cases hc : c < b
      · simp only [ha, hc, ↓reduceIte]; exact ⟨hop, by simp, fun i hi => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi; rcases hi with rfl | rfl <;> assumption⟩
      · simp only [ha, hc, ↓reduceIte]
        by_cases hand : isAndOp op = true <;> simp [hand, ha]
      · simp only [ha, hc, ↓reduceIte]
        by_cases hand : isAndOp op = true <;> simp [hand, hc]
      · simp only [ha, hc, ↓reduceIte]
        simp
    · simp at hlen_g
  have hmono' : ∀ g ∈ x7.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    rcases hmono g hg with ⟨hop, hlen_g⟩
    refine ⟨?_, hlen_g⟩
    rcases hop with hop | hop
    · exact Or.inl hop
    · exact Or.inr (by simpa [Set.mem_singleton_iff] using hop)
  have hC'_mono : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    dsimp [C'] at hg
    rw [List.mem_iff_getElem] at hg
    rcases hg with ⟨j, hj, rfl⟩
    rw [List.getElem_zipWith]
    have hj_m : j < m := by
      rw [List.length_zipWith, List.length_range, List.length_take, Nat.min_eq_left hm_le, Nat.min_self] at hj
      exact hj
    have hj_full : j < x7.gates.length := lt_of_lt_of_le hj_m hm_le
    have hj_take : j < (x7.gates.take m).length := by
      rw [List.length_take, Nat.min_eq_left hm_le]; exact hj_m
    have h0 := hmono' (x7.gates.take m)[j] (List.mem_of_mem_take (List.getElem_mem hj_take))
    have hp := hnorm_prop (26 + j) (x7.gates.take m)[j] h0.1 h0.2
    rw [List.getElem_range, List.getElem_take]
    rw [List.getElem_take] at hp
    refine ⟨?_, hp.2.1⟩
    rcases hp.1 with hop | hop
    · exact Or.inl hop
    · exact Or.inr (by simp [hop])
  have hC'_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' := by
    intro j hj i hi
    rw [hC'_len] at hj
    have hj_full : j < x7.gates.length := lt_of_lt_of_le hj hm_le
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = normGate (26 + j) x7.gates[j] := by
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hj,
        List.getElem?_take_of_lt hj, List.getElem?_eq_getElem hj_full]
      rfl
    rw [hgate] at hi
    have h0 := hmono' x7.gates[j] (List.getElem_mem hj_full)
    exact (hnorm_prop (26 + j) x7.gates[j] h0.1 h0.2).2.2 i hi
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
  have hstep_norm : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      g.inputs.length ≤ 2 →
      step w (normGate w.length g) = step w g := by
    intro w g hop hlen_g
    rcases g with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
    · rfl
    · dsimp [step, normGate]
      by_cases ha : a < w.length
      · simp [ha]
      · simp only [ha, ↓reduceIte, List.map_nil, List.map_cons, List.getD_eq_getElem?_getD]
        have hfalse_a : w[a]?.getD false = false := by
          rw [List.getElem?_eq_none (Nat.le_of_not_lt ha)]; rfl
        rcases hop with rfl | rfl <;> (rw [hfalse_a]; rfl)
    · dsimp [step, normGate]
      have hnone : ∀ idx : ℕ, ¬ idx < w.length → w[idx]?.getD false = false := by
        intro idx hni
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hni)]; rfl
      by_cases ha : a < w.length <;> by_cases hc : c < w.length
      · simp [ha, hc]
      · simp only [ha, hc, ↓reduceIte, List.getD_eq_getElem?_getD]
        have hcf := hnone c hc
        rcases hop with rfl | rfl
        · simp only [isAndOp, ↓reduceIte, List.map_nil, List.map_cons, hcf]; cases (w[a]?.getD false) <;> rfl
        · simp only [isAndOp, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.map_cons, hcf]; cases (w[a]?.getD false) <;> rfl
      · simp only [ha, hc, ↓reduceIte, List.getD_eq_getElem?_getD]
        have haf := hnone a ha
        rcases hop with rfl | rfl
        · simp only [isAndOp, ↓reduceIte, List.map_nil, List.map_cons, haf]; cases (w[c]?.getD false) <;> rfl
        · simp only [isAndOp, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.map_cons, haf]; cases (w[c]?.getD false) <;> rfl
      · simp only [ha, hc, ↓reduceIte, List.getD_eq_getElem?_getD]
        have haf := hnone a ha
        have hcf := hnone c hc
        rcases hop with rfl | rfl <;> (simp only [List.map_nil, List.map_cons, haf, hcf]; rfl)
    · simp at hlen_g
  have hprefix_eq : ∀ (k : ℕ) (hk : k ≤ m) (inp : List Bool), inp.length = 26 →
      ((List.zipWith (fun j g => normGate (26 + j) g) (List.range k) (x7.gates.take k)).foldl step inp) =
      ((x7.gates.take k).foldl step inp) := by
    intro k hk inp hlen_inp
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hk_full : k < x7.gates.length := lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk) hm_le
      have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
      have ht : x7.gates.take (k + 1) = x7.gates.take k ++ [x7.gates[k]] :=
        List.take_succ_eq_append_getElem hk_full
      have hlen_rk : (List.range k).length = (x7.gates.take k).length := by
        rw [List.length_range, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [hr, ht, List.zipWith_append hlen_rk, List.foldl_append, List.foldl_append, ih hk']
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
      have hlen_pre : ((x7.gates.take k).foldl step inp).length = 26 + k := by
        rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [← hlen_pre]
      have h0 := hmono' x7.gates[k] (List.getElem_mem hk_full)
      exact hstep_norm ((x7.gates.take k).foldl step inp) x7.gates[k] h0.1 h0.2
  have hC'_eval : ∀ f : Fin 26 → Bool,
      C'.eval (List.ofFn f) = x7.eval (List.ofFn f) := by
    intro f
    let inp := List.ofFn f
    have hlen_inp : inp.length = 26 := by simp [inp]
    have hw_eq : C'.wires inp = (x7.gates.take m).foldl step inp := by
      change (List.zipWith (fun j g => normGate (26 + j) g) (List.range m) (x7.gates.take m)).foldl step inp = _
      exact hprefix_eq m (le_refl m) inp hlen_inp
    have hx7_split : x7.wires inp = (x7.gates.drop m).foldl step (C'.wires inp) := by
      rw [hw_eq]
      change x7.gates.foldl step inp =
        (x7.gates.drop m).foldl step ((x7.gates.take m).foldl step inp)
      rw [← List.foldl_append, List.take_append_drop]
    have hout_lt_C' : x7.output < (C'.wires inp).length := by
      rw [hw_eq, hfold_len, hlen_inp, List.length_take, Nat.min_eq_left hm_le]
      dsimp [m]; omega
    change (C'.wires inp).getD x7.output false = (x7.wires inp).getD x7.output false
    rw [hx7_split, hfold_getD (x7.gates.drop m) (C'.wires inp) x7.output hout_lt_C']
  have hm1_lt : m - 1 < x7.gates.length := by dsimp [m]; omega
  have htop_orig : x7.gates[m - 1] = PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - 26) := by
    dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, m]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  have htop_C' : PEqualNP.MetaComplexity.NestedCover.gateAt C' (C'.size - 1) =
      normGate (26 + (m - 1)) x7.gates[m - 1] := by
    dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
    rw [List.getD_eq_getElem?_getD, hC'_sz, List.getElem?_zipWith,
      List.getElem?_range (by omega), List.getElem?_take_of_lt (by omega),
      List.getElem?_eq_getElem hm1_lt]
    rfl
  have h00 : x1 0 0 := Or.inl rfl
  have hev00 : C'.eval (List.ofFn fun i : Fin 26 => Decidable.decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))) = true := by
    rw [hC'_eval]
    exact hpos 0 0 h00
  have hC'_last_eval : ∀ (inp : List Bool), inp.length = 26 →
      C'.eval inp =
        (normGate (26 + (m - 1)) x7.gates[m - 1]).op.eval
          ((normGate (26 + (m - 1)) x7.gates[m - 1]).inputs.map fun i =>
            ((C'.gates.take (m - 1)).foldl step inp).getD i false) := by
    intro inp hlen_inp
    have hsplit_C' : C'.gates = C'.gates.take (m - 1) ++ [normGate (26 + (m - 1)) x7.gates[m - 1]] := by
      have h1 : C'.gates.take m = C'.gates := List.take_of_length_le (by rw [hC'_len])
      have h2 : C'.gates.take (m - 1 + 1) = C'.gates.take (m - 1) ++ [C'.gates[m - 1]] :=
        List.take_succ_eq_append_getElem (by rw [hC'_len]; omega)
      have hidx : m - 1 + 1 = m := by omega
      rw [hidx, h1] at h2
      have hg_at : C'.gates[m - 1] = normGate (26 + (m - 1)) x7.gates[m - 1] := by
        dsimp [C']
        rw [List.getElem_zipWith, List.getElem_range, List.getElem_take]
      rw [← hg_at]
      exact h2
    have hpre_len : ((C'.gates.take (m - 1)).foldl step inp).length = x7.output := by
      rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left (by rw [hC'_len]; omega)]
      dsimp [m]; omega
    change (C'.wires inp).getD x7.output false = _
    have hw_C' : C'.wires inp = step ((C'.gates.take (m - 1)).foldl step inp) (normGate (26 + (m - 1)) x7.gates[m - 1]) := by
      change C'.gates.foldl step inp = _
      conv_lhs => rw [hsplit_C']
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hw_C']
    dsimp [step]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hpre_len.le, hpre_len, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  have hnot_or_nil : normGate (26 + (m - 1)) x7.gates[m - 1] ≠ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
    intro hbad
    have hf : C'.eval (List.ofFn fun i : Fin 26 => Decidable.decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))) = false := by
      rw [hC'_last_eval _ (by simp), hbad]
      rfl
    rw [hf] at hev00
    cases hev00
  have hop_orig_and : x7.gates[m - 1].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    rw [htop_orig]; exact htop_op
  have hlen_orig := (hmono' x7.gates[m - 1] (List.getElem_mem hm1_lt)).2
  have htop_op_C' : (PEqualNP.MetaComplexity.NestedCover.gateAt C' (C'.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    rw [htop_C']
    rcases hg_orig : x7.gates[m - 1] with ⟨op, is⟩
    rw [hg_orig] at hop_orig_and hlen_orig hnot_or_nil
    dsimp only at hop_orig_and hlen_orig
    subst hop_orig_and
    rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
    · rfl
    · dsimp [normGate] at hnot_or_nil ⊢
      by_cases ha : a < 26 + (m - 1)
      · simp [ha]
      · simp [ha] at hnot_or_nil
    · dsimp [normGate] at hnot_or_nil ⊢
      by_cases ha : a < 26 + (m - 1) <;> by_cases hc : c < 26 + (m - 1)
      · simp [ha, hc]
      · simp [ha, hc, isAndOp] at hnot_or_nil
      · simp [ha, hc, isAndOp] at hnot_or_nil
      · simp [ha, hc] at hnot_or_nil
    · simp at hlen_orig
  by_cases hnil : (PEqualNP.MetaComplexity.NestedCover.gateAt C' (C'.size - 1)).inputs = []
  · let A : Finset (Fin 13) := {0, 1, 2, 5}
    refine Or.inl ⟨A, hQuad.1, hQuad.2, ?_⟩
    change x7.eval (List.ofFn (x6 A (x2 A))) = true
    rw [← hC'_eval (x6 A (x2 A)), hC'_last_eval _ (by simp), ← htop_C', hnil, htop_op_C']
    rfl
  · have hlen_ge1 : 1 ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (C'.size - 1)).inputs.length := by
      cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt C' (C'.size - 1)).inputs with
      | nil => exact absurd h hnil
      | cons _ _ => simp
    have hC'_pos_ev : ∀ (x10 x11 : Fin 13), x1 x10 x11 →
        (PEqualNP.MetaComplexity.circuitFun 26 C' fun i =>
          Decidable.decide (i = Fin.castAdd 13 x10 ∨ i = Fin.natAdd 13 x11)) = true := by
      intro x10 x11 hinc
      change C'.eval (List.ofFn _) = true
      rw [hC'_eval]
      exact hpos x10 x11 hinc
    have hres := hNormAnd C' hC'_mono hC'_RB hC'_pos hC'_out htop_op_C' hlen_ge1
      (by rw [hC'_sz]; dsimp [m]; omega) hC'_pos_ev
    rcases hres with ⟨A, hAc, hA, hAt⟩ | ⟨B, hBc, hB, hBt⟩
    · refine Or.inl ⟨A, hAc, hA, ?_⟩
      change x7.eval (List.ofFn (x6 A (x2 A))) = true
      rw [← hC'_eval]; exact hAt
    · refine Or.inr ⟨B, hBc, hB, ?_⟩
      change x7.eval (List.ofFn (x6 (x3 B) B)) = true
      rw [← hC'_eval]; exact hBt
