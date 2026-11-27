import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7792_3
    (hIncAvoid :
      ∀ i < (26 : ℕ), ∃ (p l : Fin (13 : ℕ)),
        p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
        (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD i Bool.false = Bool.false)
    (hCanon :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ)) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Finset (Fin (13 : ℕ))) => (x4.wires (x2 x6)).getD ((26 : ℕ) + x5) Bool.false = Bool.true;
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → (26 : ℕ) ≤ x5.output → x5.output < (26 : ℕ) + x5.size → (∀ g ∈ x5.gates, g.inputs.Pairwise (· ≤ ·)) → PEqualNP.GenericRejection.RightOnIncidentPairs x1 x5 → (∀ (x9 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x9 → x5.eval (x2 x9) = Bool.false) → (∀ (x10 : ℕ), x3 x5 x10 → (∃ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 ∧ x4 x5 x10 x12) ∧ (2 : ℕ) ≤ {x12 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x12.1} {x12.2}) = Bool.false}.card) → (∃ (x11 : ℕ), x3 x5 x11 ∧ x4 x5 x11 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))}) → (64 : ℕ) ≤ x5.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
    have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2);
    have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5;
    have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ)) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Finset (Fin (13 : ℕ))) => (x4.wires (x2 x6)).getD ((26 : ℕ) + x5) Bool.false = Bool.true;
    ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → PEqualNP.GenericRejection.RightOnIncidentPairs x1 x5 → (∀ (x9 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x9 → x5.eval (x2 x9) = Bool.false) → (∀ (x10 : ℕ), x3 x5 x10 → (∃ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 ∧ x4 x5 x10 x12) ∧ (2 : ℕ) ≤ {x12 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x12.1} {x12.2}) = Bool.false}.card) → (∃ (x11 : ℕ), x3 x5 x11 ∧ x4 x5 x11 {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ))}) → (64 : ℕ) ≤ x5.size := by
  intro x1 x2 x3 x4 x5 hmono hRB hright hquad hinner hwit
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
  have hinc_len : ∀ (X Y : Finset (Fin 13)),
      (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y
    dsimp only [PEqualNP.GenericRejection.incidenceInput]
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  have h26_le : 26 ≤ x5.output := by
    by_contra hlt
    have hlt' : x5.output < 26 := Nat.lt_of_not_le hlt
    obtain ⟨p, l, hp, hget⟩ := hIncAvoid x5.output hlt'
    have htru : x5.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := hright l p hp
    have hfls : x5.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = false := by
      change (x5.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5.output false = false
      rw [hfold_getD x5.gates (PEqualNP.GenericRejection.incidenceInput {p} {l}) x5.output (by rw [hinc_len]; exact hlt')]
      exact hget
    rw [hfls] at htru; cases htru
  have hout_lt : x5.output < 26 + x5.size := by
    by_contra hge
    have hle : 26 + x5.size ≤ x5.output := Nat.le_of_not_lt hge
    obtain ⟨p, l, hp, _⟩ := hIncAvoid 0 (by decide)
    have htru : x5.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := hright l p hp
    have hfls : x5.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = false := by
      change (x5.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5.output false = false
      have hlen_w : (x5.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).length = 26 + x5.size := by
        change (x5.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).length = 26 + x5.gates.length
        rw [hfold_len, hinc_len]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfls] at htru; cases htru
  let sortGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
    List.casesOn g.inputs g fun a r1 =>
      List.casesOn r1 g fun b r2 =>
        List.casesOn r2 (if b < a then ⟨g.op, [b, a]⟩ else g) (fun _ _ => g)
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨x5.gates.map sortGate, x5.output⟩
  have hC'_sz : C'.size = x5.size := List.length_map _
  have hmono_destr : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 D →
      ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro D hDm g hg
    rcases hDm g hg with ⟨hop, hlen_g⟩
    refine ⟨?_, hlen_g⟩
    rcases hop with hop | hop
    · exact Or.inl hop
    · exact Or.inr (by simpa [Set.mem_singleton_iff] using hop)
  have hsort_op : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (sortGate g).op = g.op := by
    intro g; rcases g with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
    · rfl
    · rfl
    · dsimp [sortGate]; split_ifs <;> rfl
    · rfl
  have hsort_len : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (sortGate g).inputs.length = g.inputs.length := by
    intro g; rcases g with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
    · rfl
    · rfl
    · dsimp [sortGate]; split_ifs <;> rfl
    · rfl
  have hsort_mem : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ),
      i ∈ (sortGate g).inputs ↔ i ∈ g.inputs := by
    intro g i; rcases g with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
    · rfl
    · rfl
    · dsimp [sortGate]; by_cases hba : b < a
      · rw [if_pos hba]; dsimp only
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact or_comm
      · rw [if_neg hba]
    · rfl
  have hC'_mono : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    dsimp [C'] at hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    rcases hmono g0 hg0 with ⟨hop0, hlen0⟩
    rw [hsort_op g0, hsort_len g0]
    exact ⟨hop0, hlen0⟩
  have hC'_RB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' := by
    intro j hj i hi
    have hj' : j < x5.gates.length := by dsimp [C'] at hj; rw [List.length_map] at hj; exact hj
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j = sortGate x5.gates[j] := by
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj']
      rfl
    rw [hgate, hsort_mem] at hi
    have hgate0 : x5.gates[j] = PEqualNP.MetaComplexity.NestedCover.gateAt x5 j := by
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    rw [hgate0] at hi
    exact hRB j hj' i hi
  have hC'_pair : ∀ g ∈ C'.gates, g.inputs.Pairwise (· ≤ ·) := by
    intro g hg
    dsimp [C'] at hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    have hlen0 := (hmono g0 hg0).2
    rcases g0 with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
    · exact List.Pairwise.nil
    · exact List.pairwise_singleton _ _
    · dsimp [sortGate]; by_cases hba : b < a
      · rw [if_pos hba]; dsimp only
        rw [List.pairwise_pair]; exact Nat.le_of_lt hba
      · rw [if_neg hba]; dsimp only
        rw [List.pairwise_pair]; exact Nat.le_of_not_lt hba
    · exfalso; simp at hlen0
  have hstep_sort : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      g.inputs.length ≤ 2 →
      step w (sortGate g) = step w g := by
    intro w g hop hlen_g
    rcases g with ⟨op, is⟩
    rcases is with _ | ⟨a, _ | ⟨b, _ | d⟩⟩
    · rfl
    · rfl
    · dsimp [step, sortGate]; by_cases hba : b < a
      · rw [if_pos hba]; dsimp only
        simp only [List.map_cons, List.map_nil]
        rcases hop with rfl | rfl <;> (cases (w.getD a false) <;> cases (w.getD b false) <;> rfl)
      · rw [if_neg hba]
    · simp at hlen_g
  have hwires_sort : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D →
      ∀ (inp : List Bool), ({ gates := D.gates.map sortGate, output := D.output : PEqualNP.CircuitLowerBounds.Circuit }).wires inp = D.wires inp := by
    intro D hDm inp
    change (D.gates.map sortGate).foldl step inp = D.gates.foldl step inp
    suffices h : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
        (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
        (gs.map sortGate).foldl step acc = gs.foldl step acc by
      exact h D.gates inp (hmono_destr D hDm)
    intro gs
    induction gs with
    | nil => intro acc _; rfl
    | cons g gs ih =>
      intro acc hgs
      have hg0 := hgs g List.mem_cons_self
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, hstep_sort acc g hg0.1 hg0.2]
      exact ih (step acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
  have hC'_wires : ∀ inp : List Bool, C'.wires inp = x5.wires inp := hwires_sort x5 hmono
  have hC'_eval : ∀ inp : List Bool, C'.eval inp = x5.eval inp := by
    intro inp
    change (C'.wires inp).getD C'.output false = (x5.wires inp).getD x5.output false
    rw [hC'_wires]
  have hgate_op_C' : ∀ j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x5 j).op := by
    intro j
    by_cases hj : j < x5.gates.length
    · dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, Option.getD_some, hsort_op]
    · have hj1 : ¬ j < C'.gates.length := by dsimp [C']; rw [List.length_map]; exact hj
      dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hj1),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hj)]
  have hcone_inv : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc1 acc2 : List (List ℕ)),
      acc1.length = acc2.length →
      (∀ idx m : ℕ, m ∈ acc1.getD idx [] ↔ m ∈ acc2.getD idx []) →
      ((gs.map sortGate).foldl (PEqualNP.EdgeOwnership.coneStep 26) acc1).length = (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) acc2).length ∧
      (∀ idx m : ℕ, m ∈ ((gs.map sortGate).foldl (PEqualNP.EdgeOwnership.coneStep 26) acc1).getD idx [] ↔
        m ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) acc2).getD idx []) := by
    intro gs
    induction gs with
    | nil => intro acc1 acc2 hlen hmem; exact ⟨hlen, hmem⟩
    | cons g gs ih =>
      intro acc1 acc2 hlen hmem
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      apply ih
      · dsimp only [PEqualNP.EdgeOwnership.coneStep]
        rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton, hlen]
      · intro idx m
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        by_cases hlt : idx < acc1.length
        · have hlt2 : idx < acc2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
            List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
          exact hmem idx m
        · by_cases heq : idx = acc1.length
          · have heq2 : idx = acc2.length := by omega
            subst heq
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
              List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq heq2.symm), ← heq2, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [List.mem_flatMap, List.mem_flatMap]
            constructor
            · rintro ⟨w, hw, hm⟩
              rw [List.mem_filter] at hw
              refine ⟨w, ?_, ?_⟩
              · rw [List.mem_filter]
                refine ⟨(hsort_mem g w).mp hw.1, ?_⟩
                simpa [hlen] using hw.2
              · rw [List.mem_cons] at hm ⊢
                rcases hm with rfl | hm
                · exact Or.inl rfl
                · exact Or.inr ((hmem (w - 26) m).mp hm)
            · rintro ⟨w, hw, hm⟩
              rw [List.mem_filter] at hw
              refine ⟨w, ?_, ?_⟩
              · rw [List.mem_filter]
                refine ⟨(hsort_mem g w).mpr hw.1, ?_⟩
                simpa [hlen] using hw.2
              · rw [List.mem_cons] at hm ⊢
                rcases hm with rfl | hm
                · exact Or.inl rfl
                · exact Or.inr ((hmem (w - 26) m).mpr hm)
          · have hgt1 : acc1.length + 1 ≤ idx := by omega
            have hgt2 : acc2.length + 1 ≤ idx := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; exact hgt1), Option.getD_none,
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; exact hgt2), Option.getD_none]
  have hInCone_C' : ∀ i j : ℕ, PEqualNP.EdgeOwnership.InCone 26 C' i j ↔ PEqualNP.EdgeOwnership.InCone 26 x5 i j := by
    intro i j
    dsimp only [PEqualNP.EdgeOwnership.InCone, PEqualNP.EdgeOwnership.cones, C']
    exact (hcone_inv x5.gates [] [] rfl (fun _ _ => Iff.rfl)).2 j i
  have hx3_iff : ∀ k : ℕ, x3 C' k ↔ x3 x5 k := by
    intro k
    dsimp only [x3]
    rw [hgate_op_C' k]
    constructor
    · rintro ⟨hk, m, hm, hic⟩
      exact ⟨hk, m, (hgate_op_C' m).symm.trans hm, (hInCone_C' k m).mp hic⟩
    · rintro ⟨hk, m, hm, hic⟩
      exact ⟨hk, m, (hgate_op_C' m).trans hm, (hInCone_C' k m).mpr hic⟩
  have hx4_iff : ∀ k Q, x4 C' k Q ↔ x4 x5 k Q := by
    intro k Q
    dsimp only [x4]
    rw [hC'_wires]
  have hright' : PEqualNP.GenericRejection.RightOnIncidentPairs x1 C' := by
    intro l p hp
    rw [hC'_eval]
    exact hright l p hp
  have hquad' : ∀ Q, PEqualNP.HeptadCover.IsQuadrangle x1 Q → C'.eval (x2 Q) = false := by
    intro Q hQ
    rw [hC'_eval]
    exact hquad Q hQ
  have hset_eval : ∀ (x10 : ℕ) (inp : List Bool),
      ({ gates := C'.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := C'.output : PEqualNP.CircuitLowerBounds.Circuit }).eval inp =
      ({ gates := x5.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }).eval inp := by
    intro x10 inp
    let D0 : PEqualNP.CircuitLowerBounds.Circuit :=
      { gates := x5.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output }
    have hD0_mono : PEqualNP.MetaComplexity.Monotone2 D0 := by
      intro g hg
      dsimp [D0] at hg
      rw [List.mem_iff_getElem] at hg
      rcases hg with ⟨i, hi, rfl⟩
      rw [List.length_set] at hi
      rw [List.getElem_set]
      split_ifs
      · exact ⟨Or.inr rfl, by simp⟩
      · exact hmono x5.gates[i] (List.getElem_mem hi)
    have hset_gates : C'.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } =
        D0.gates.map sortGate := by
      dsimp [C', D0]
      have hsort_nil : sortGate { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } =
          { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } := rfl
      rw [← hsort_nil, List.map_set]
    change ({ gates := C'.gates.set x10 _, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.wires inp).getD x5.output false =
      (D0.wires inp).getD x5.output false
    rw [hset_gates, hwires_sort D0 hD0_mono inp]
  have hinner' : ∀ (x10 : ℕ), x3 C' x10 →
      (∃ Q, PEqualNP.HeptadCover.IsQuadrangle x1 Q ∧ x4 C' x10 Q) ∧
      2 ≤ {x12 ∈ PEqualNP.HeptadCover.incidences x1 |
        { gates := C'.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := C'.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x12.1} {x12.2}) = false}.card := by
    intro x10 hx3c
    have h0 := hinner x10 ((hx3_iff x10).mp hx3c)
    refine ⟨?_, ?_⟩
    · rcases h0.1 with ⟨Q, hQ, h4⟩
      exact ⟨Q, hQ, (hx4_iff x10 Q).mpr h4⟩
    · have heq_set : {x12 ∈ PEqualNP.HeptadCover.incidences x1 |
          { gates := C'.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := C'.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x12.1} {x12.2}) = false} =
          {x12 ∈ PEqualNP.HeptadCover.incidences x1 |
          { gates := x5.gates.set x10 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x12.1} {x12.2}) = false} := by
        ext x12
        simp only [Finset.mem_filter, hset_eval]
      rw [heq_set]
      exact h0.2
  have hwit' : ∃ (x11 : ℕ), x3 C' x11 ∧ x4 C' x11 {(0 : Fin 13), (1 : Fin 13), (2 : Fin 13), (5 : Fin 13)} := by
    rcases hwit with ⟨x11, hx30, hx40⟩
    exact ⟨x11, (hx3_iff x11).mpr hx30, (hx4_iff x11 _).mpr hx40⟩
  have hres := hCanon C' hC'_mono hC'_RB h26_le (by rw [hC'_sz]; exact hout_lt) hC'_pair hright' hquad' hinner' hwit'
  rw [hC'_sz] at hres
  exact hres
