import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8119_1
    (hAvoid :
      let x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) =>
        ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (v : Fin (42 : ℕ)), ∃ (a b : Fin (42 : ℕ)), x1 a b ∧ a ≠ v ∧ b ≠ v)
    (hNorm :
      have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ (∀ (x3 x4 : Fin (42 : ℕ)), x1 x3 x4 → x2.eval (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 = x3 ∨ x6 = x4)) = Bool.true) ∧ ∀ (x3 : Fin (42 : ℕ) → Bool), (∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.true ↔ ∀ (x5 : Fin (42 : ℕ)), x3 x5 = Bool.true → ¬(x1 x4 x5 ∨ x1 x5 x4)) → x2.eval (List.ofFn x3) = Bool.false;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (42 : ℕ) x3 → (0 : ℕ) < x3.size → x3.output = (42 : ℕ) + (x3.size - (1 : ℕ)) → x3.size ≤ (124 : ℕ) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x3.size ≤ x6.size) → (∀ (x7 : Fin (42 : ℕ)) (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → (x3.wires (List.ofFn fun (x12 : Fin (42 : ℕ)) => Decidable.decide (x12 = x7))).getD ((42 : ℕ) + x8) Bool.false = Bool.false) → (∃ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (↑x10 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x8) Bool.false = Bool.true) → False) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
    have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ (∀ (x3 x4 : Fin (42 : ℕ)), x1 x3 x4 → x2.eval (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 = x3 ∨ x6 = x4)) = Bool.true) ∧ ∀ (x3 : Fin (42 : ℕ) → Bool), (∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.true ↔ ∀ (x5 : Fin (42 : ℕ)), x3 x5 = Bool.true → ¬(x1 x4 x5 ∨ x1 x5 x4)) → x2.eval (List.ofFn x3) = Bool.false;
    ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → x3.size ≤ (124 : ℕ) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x3.size ≤ x6.size) → (∀ (x7 : Fin (42 : ℕ)) (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → (x3.wires (List.ofFn fun (x12 : Fin (42 : ℕ)) => Decidable.decide (x12 = x7))).getD ((42 : ℕ) + x8) Bool.false = Bool.false) → (∃ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (↑x10 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x8) Bool.false = Bool.true) → False := by
  intro x1 x2 x3 hx2 hsz hmin hsing hwit
  rcases hx2 with ⟨hmono, hpos, hneg⟩
  rcases hwit with ⟨jw, gw, hjw, hopw, hvalw⟩
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
  have h42_le : 42 ≤ x3.output := by
    by_contra hlt
    have hlt' : x3.output < 42 := Nat.lt_of_not_le hlt
    obtain ⟨a, b, hab, hna, hnb⟩ := hAvoid ⟨x3.output, hlt'⟩
    let f : Fin 42 → Bool := fun x => Decidable.decide (x = a ∨ x = b)
    have htru : x3.eval (List.ofFn f) = true := hpos a b hab
    have hfalse : x3.eval (List.ofFn f) = false := by
      change (x3.wires (List.ofFn f)).getD x3.output false = false
      change (x3.gates.foldl step (List.ofFn f)).getD x3.output false = false
      rw [hfold_getD x3.gates (List.ofFn f) x3.output (by simp [hlt'])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt']),
        Option.getD_some, List.getElem_ofFn]
      simp only [f, Fin.ext_iff] at hna hnb ⊢
      have hna' : x3.output ≠ ↑a := fun h => hna (Fin.ext h.symm)
      have hnb' : x3.output ≠ ↑b := fun h => hnb (Fin.ext h.symm)
      simp [hna', hnb']
    rw [hfalse] at htru
    cases htru
  have hout_lt : x3.output < 42 + x3.size := by
    by_contra hge
    have hle : 42 + x3.size ≤ x3.output := Nat.le_of_not_lt hge
    obtain ⟨a, b, hab, _, _⟩ := hAvoid ⟨0, by decide⟩
    let f : Fin 42 → Bool := fun x => Decidable.decide (x = a ∨ x = b)
    have htru : x3.eval (List.ofFn f) = true := hpos a b hab
    have hlen_w : (x3.wires (List.ofFn f)).length = 42 + x3.size := by
      change (x3.gates.foldl step (List.ofFn f)).length = 42 + x3.gates.length
      rw [hfold_len, List.length_ofFn]
    have hfalse : x3.eval (List.ofFn f) = false := by
      change (x3.wires (List.ofFn f)).getD x3.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfalse] at htru
    cases htru
  let m : ℕ := x3.output - 42 + 1
  have hx3_sz : x3.size = x3.gates.length := rfl
  have hm_pos : 0 < m := by omega
  have hm_le : m ≤ x3.gates.length := by omega
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
    ⟨List.zipWith (fun j g => normGate (42 + j) g) (List.range m) (x3.gates.take m), x3.output⟩
  have hC'_len : C'.gates.length = m := by
    dsimp [C']
    rw [List.length_zipWith, List.length_range, List.length_take, Nat.min_eq_left hm_le, Nat.min_self]
  have hC'_sz : C'.size = m := hC'_len
  have hC'_pos : 0 < C'.size := by omega
  have hC'_out : C'.output = 42 + (C'.size - 1) := by dsimp [C'] at *; omega
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
  have hmono' : ∀ g ∈ x3.gates,
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
    have hj_full : j < x3.gates.length := lt_of_lt_of_le hj_m hm_le
    have hj_take : j < (x3.gates.take m).length := by
      rw [List.length_take, Nat.min_eq_left hm_le]; exact hj_m
    have h0 := hmono' (x3.gates.take m)[j] (List.mem_of_mem_take (List.getElem_mem hj_take))
    have hp := hnorm_prop (42 + j) (x3.gates.take m)[j] h0.1 h0.2
    rw [List.getElem_range, List.getElem_take]
    rw [List.getElem_take] at hp
    refine ⟨?_, hp.2.1⟩
    rcases hp.1 with hop | hop
    · exact Or.inl hop
    · exact Or.inr (by simp [hop])
  have hC'_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 42 C' := by
    intro j hj i hi
    rw [hC'_len] at hj
    have hj_full : j < x3.gates.length := lt_of_lt_of_le hj hm_le
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = normGate (42 + j) x3.gates[j] := by
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hj,
        List.getElem?_take_of_lt hj, List.getElem?_eq_getElem hj_full]
      rfl
    rw [hgate] at hi
    have h0 := hmono' x3.gates[j] (List.getElem_mem hj_full)
    exact (hnorm_prop (42 + j) x3.gates[j] h0.1 h0.2).2.2 i hi
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
  have hprefix_eq : ∀ (k : ℕ) (hk : k ≤ m) (inp : List Bool), inp.length = 42 →
      ((List.zipWith (fun j g => normGate (42 + j) g) (List.range k) (x3.gates.take k)).foldl step inp) =
      ((x3.gates.take k).foldl step inp) := by
    intro k hk inp hlen_inp
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hk_full : k < x3.gates.length := lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk) hm_le
      have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
      have ht : x3.gates.take (k + 1) = x3.gates.take k ++ [x3.gates[k]] :=
        List.take_succ_eq_append_getElem hk_full
      have hlen_rk : (List.range k).length = (x3.gates.take k).length := by
        rw [List.length_range, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [hr, ht, List.zipWith_append hlen_rk, List.foldl_append, List.foldl_append, ih hk']
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil]
      have hlen_pre : ((x3.gates.take k).foldl step inp).length = 42 + k := by
        rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left (le_of_lt hk_full)]
      rw [← hlen_pre]
      have h0 := hmono' x3.gates[k] (List.getElem_mem hk_full)
      exact hstep_norm ((x3.gates.take k).foldl step inp) x3.gates[k] h0.1 h0.2
  have hC'_eval : ∀ f : Fin 42 → Bool, C'.eval (List.ofFn f) = x3.eval (List.ofFn f) := by
    intro f
    let inp := List.ofFn f
    have hlen_inp : inp.length = 42 := by simp [inp]
    have hw_eq : C'.wires inp = (x3.gates.take m).foldl step inp := by
      change (List.zipWith (fun j g => normGate (42 + j) g) (List.range m) (x3.gates.take m)).foldl step inp = _
      exact hprefix_eq m (le_refl m) inp hlen_inp
    have hx3_split : x3.wires inp = (x3.gates.drop m).foldl step (C'.wires inp) := by
      rw [hw_eq]
      change x3.gates.foldl step inp = (x3.gates.drop m).foldl step ((x3.gates.take m).foldl step inp)
      rw [← List.foldl_append, List.take_append_drop]
    have hout_lt_C' : x3.output < (C'.wires inp).length := by
      rw [hw_eq, hfold_len, hlen_inp, List.length_take, Nat.min_eq_left hm_le]
      dsimp [m]; omega
    change (C'.wires inp).getD x3.output false = (x3.wires inp).getD x3.output false
    rw [hx3_split, hfold_getD (x3.gates.drop m) (C'.wires inp) x3.output hout_lt_C']
  have hx2C' : x2 C' := by
    refine ⟨hC'_mono, ?_, ?_⟩
    · intro a b hab; rw [hC'_eval]; exact hpos a b hab
    · intro f hf; rw [hC'_eval]; exact hneg f hf
  have hsz_le_C' : x3.size ≤ C'.size := hmin C' hx2C'
  have hm_eq : m = x3.gates.length := by
    rw [hC'_sz, hx3_sz] at hsz_le_C'
    omega
  have hC'_wires_eq : ∀ f : Fin 42 → Bool, C'.wires (List.ofFn f) = x3.wires (List.ofFn f) := by
    intro f
    have htake : x3.gates.take m = x3.gates := List.take_of_length_le hm_eq.ge
    change (List.zipWith (fun j g => normGate (42 + j) g) (List.range m) (x3.gates.take m)).foldl step (List.ofFn f) =
      x3.gates.foldl step (List.ofFn f)
    rw [hprefix_eq m (le_refl m) (List.ofFn f) (by simp), htake]
  have hnorm_and_op : ∀ (b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      g.inputs.length ≤ 2 →
      (normGate b g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro b g hop hlen_g hnop
    rcases hop with hop | hop
    · exact hop
    · exfalso
      rcases g with ⟨op, is⟩
      dsimp only at hop hlen_g hnop
      subst hop
      rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
      · cases hnop
      · dsimp [normGate] at hnop; split_ifs at hnop <;> cases hnop
      · dsimp [normGate] at hnop; split_ifs at hnop <;> cases hnop
      · simp at hlen_g
  have hsing' : ∀ (x7 : Fin 42) (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate),
      C'.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (C'.wires (List.ofFn fun x12 => Decidable.decide (x12 = x7))).getD (42 + x8) false = false := by
    intro x7 x8 x9 hx9 hop9
    have hx8_lt : x8 < m := by
      by_contra hge
      have hnone : C'.gates[x8]? = none := List.getElem?_eq_none (by rw [hC'_len]; omega)
      rw [hnone] at hx9; cases hx9
    have hx8_full : x8 < x3.gates.length := by omega
    have hg_eq : x9 = normGate (42 + x8) x3.gates[x8] := by
      dsimp [C'] at hx9
      rw [List.getElem?_zipWith, List.getElem?_range hx8_lt, List.getElem?_take_of_lt hx8_lt,
        List.getElem?_eq_getElem hx8_full] at hx9
      exact Option.some.inj hx9.symm
    have h0 := hmono' x3.gates[x8] (List.getElem_mem hx8_full)
    have hop_orig : x3.gates[x8].op = PEqualNP.CircuitLowerBounds.GateOp.and :=
      hnorm_and_op (42 + x8) x3.gates[x8] h0.1 h0.2 (by rw [← hg_eq]; exact hop9)
    rw [hC'_wires_eq]
    exact hsing x7 x8 x3.gates[x8] (List.getElem?_eq_getElem hx8_full) hop_orig
  have hjw_lt : jw < m := by
    have hjw_full' : jw < x3.gates.length := by
      by_contra hge
      have hnone : x3.gates[jw]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hnone] at hjw; cases hjw
    omega
  have hjw_full : jw < x3.gates.length := by omega
  have hgw_eq : x3.gates[jw] = gw := Option.some.inj ((List.getElem?_eq_getElem hjw_full).symm.trans hjw)
  let gw' : PEqualNP.CircuitLowerBounds.Gate := normGate (42 + jw) gw
  have hjw' : C'.gates[jw]? = Option.some gw' := by
    dsimp [C', gw']
    rw [List.getElem?_zipWith, List.getElem?_range hjw_lt, List.getElem?_take_of_lt hjw_lt, hjw]
  have hnorm_and_cases : ∀ (b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and → g.inputs.length ≤ 2 →
      normGate b g = g ∨ normGate b g = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
    intro b g hop hlen_g
    rcases g with ⟨op, is⟩
    dsimp only at hop hlen_g; subst hop
    rcases is with _ | ⟨a, _ | ⟨c, _ | d⟩⟩
    · exact Or.inl rfl
    · dsimp [normGate]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
    · dsimp [normGate]
      by_cases ha : a < b <;> by_cases hc : c < b
      · simp [ha, hc]
      · simp [ha, hc, isAndOp]
      · simp [ha, hc, isAndOp]
      · simp [ha, hc]
    · simp at hlen_g
  have hgw_len : gw.inputs.length ≤ 2 := (hmono' gw (by rw [← hgw_eq]; exact List.getElem_mem hjw_full)).2
  have hopw' : gw'.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    rcases hnorm_and_cases (42 + jw) gw hopw hgw_len with heq | hnil
    · dsimp [gw']; rw [heq]; exact hopw
    · exfalso
      let fS : Fin 42 → Bool := fun x10 => Decidable.decide (↑x10 ∈ [(0 : ℕ), 1, 2, 6, 8, 18, 24, 31, 33, 37])
      have hC_true : (C'.wires (List.ofFn fS)).getD (42 + jw) false = true := by
        rw [hC'_wires_eq]; exact hvalw
      have hC_false : (C'.wires (List.ofFn fS)).getD (42 + jw) false = false := by
        have hsplit_take : C'.gates.take (jw + 1) = C'.gates.take jw ++ [gw'] := by
          rw [List.take_succ_eq_append_getElem (by rw [hC'_len]; exact hjw_lt)]
          have hgw'_at : C'.gates[jw] = gw' :=
            Option.some.inj ((List.getElem?_eq_getElem (by rw [hC'_len]; exact hjw_lt)).symm.trans hjw')
          rw [hgw'_at]
        have hdrop_getD : C'.wires (List.ofFn fS) =
            (C'.gates.drop (jw + 1)).foldl step ((C'.gates.take (jw + 1)).foldl step (List.ofFn fS)) := by
          change C'.gates.foldl step (List.ofFn fS) = _
          rw [← List.foldl_append, List.take_append_drop]
        have hpre_len : ((C'.gates.take jw).foldl step (List.ofFn fS)).length = 42 + jw := by
          rw [hfold_len, List.length_ofFn, List.length_take, hC'_len, Nat.min_eq_left hjw_lt.le]
        have hstep1_len : 42 + jw < ((C'.gates.take (jw + 1)).foldl step (List.ofFn fS)).length := by
          rw [hfold_len, List.length_ofFn, List.length_take, hC'_len, Nat.min_eq_left hjw_lt]
          omega
        rw [hdrop_getD, hfold_getD (C'.gates.drop (jw + 1)) _ (42 + jw) hstep1_len, hsplit_take,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp [step]
        have hnil' : gw' = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := hnil
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hpre_len.le, hpre_len, Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some, hnil']
        rfl
      rw [hC_false] at hC_true
      cases hC_true
  have hvalw' : (C'.wires (List.ofFn fun (x10 : Fin 42) => Decidable.decide (↑x10 ∈ [(0 : ℕ), 1, 2, 6, 8, 18, 24, 31, 33, 37]))).getD (42 + jw) false = true := by
    rw [hC'_wires_eq]; exact hvalw
  exact hNorm C' hx2C' hC'_RB hC'_pos hC'_out (by rw [hC'_sz]; omega) (fun C6 h6 => by have hle := hmin C6 h6; omega) hsing' ⟨jw, gw', hjw', hopw', hvalw'⟩
