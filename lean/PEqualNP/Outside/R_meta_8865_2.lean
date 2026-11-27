import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8865_2
    (hUncov :
      ∀ (q v : ℕ) (I : Fin v → Fin v → Prop) [DecidableRel I],
        (1 : ℕ) ≤ q →
        v = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ (l : Fin v), Fintype.card { p : Fin v // I p l } = q + (1 : ℕ)) →
        ∀ (Y : Fin v → Bool),
          Fintype.card { l : Fin v // Y l = Bool.true } ≤ q →
          ∃ p : Fin v, ∀ l : Fin v, I p l → Y l = Bool.false)
    (hBothGateInputsLB :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),
        (87 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →
        (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →
        (∀ (Y : Fin x2 → Bool), Fintype.card { l : Fin x2 // Y l = Bool.true } ≤ x1 → ∃ p : Fin x2, ∀ l : Fin x2, x3 p l → Y l = Bool.false) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
        have x12 : ℕ → (Fin (x2 + x2) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;
        have x13 : Fin x2 × Fin x2 → Fin (x2 + x2) → Bool := fun (x13 : Fin x2 × Fin x2) (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2);
        (∀ (x15 : Fin (x2 + x2) → Bool), Fintype.card { x16 : Fin x2 // x15 (Fin.natAdd x2 x16) = Bool.true } ≤ x1 → (¬∃ (x17 : Fin x2) (x18 : Fin x2), x3 x17 x18 ∧ x15 (Fin.castAdd x2 x17) = Bool.true ∧ x15 (Fin.natAdd x2 x18) = Bool.true) → x12 x5.output x15 = Bool.false) →
        (∀ x16 ∈ x6, x3 x16.1 x16.2 ∧ x12 x5.output (x13 x16) = Bool.true ∧
          ∃ x18 < x5.size,
            (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            x12 (x2 + x2 + x18) (x13 x16) = Bool.true ∧
            ∀ (x19 : Fin (2 : ℕ)),
              x2 + x2 ≤ PEqualNP.TopForm.opnd x5 x18 x19 ∧
              PEqualNP.TopForm.opnd x5 x18 x19 < x2 + x2 + x18 ∧
              x12 (PEqualNP.TopForm.opnd x5 x18 x19) (x13 x16) = Bool.true ∧
              (x12 (PEqualNP.TopForm.opnd x5 x18 x19) fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x16.1)) = Bool.false ∧
              (x12 (PEqualNP.TopForm.opnd x5 x18 x19) fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.natAdd x2 x16.2)) = Bool.false) →
        x6.card ≤ (8 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             have x12 : ℕ → (Fin (x2 + x2) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;             have x13 : Fin x2 × Fin x2 → Fin (x2 + x2) → Bool := fun (x13 : Fin x2 × Fin x2) (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2);             have x14 : (Fin (x2 + x2) → Bool) → ℕ → ℕ → Prop := fun (x14 : Fin (x2 + x2) → Bool) => Relation.ReflTransGen fun (x15 x16 : ℕ) => ∃ x17 < x5.size, x16 = x2 + x2 + x17 ∧ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).inputs ∧ x12 x15 x14 = Bool.true ∧ x12 x16 x14 = Bool.true;             (∀ (x15 : Fin (x2 + x2) → Bool), Fintype.card { x16 : Fin x2 // x15 (Fin.natAdd x2 x16) = Bool.true } ≤ x1 → (¬∃ (x17 : Fin x2) (x18 : Fin x2), x3 x17 x18 ∧ x15 (Fin.castAdd x2 x17) = Bool.true ∧ x15 (Fin.natAdd x2 x18) = Bool.true) → x12 x5.output x15 = Bool.false) → (∀ x16 ∈ x6, x3 x16.1 x16.2 ∧ x12 x5.output (x13 x16) = Bool.true ∧ ∃ x18 < x5.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x14 (x13 x16) (x2 + x2 + x18) x5.output ∧ ∀ (x19 : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 x18 x19) fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x16.1)) = Bool.false ∧ (x12 (PEqualNP.TopForm.opnd x5 x18 x19) fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.natAdd x2 x16.2)) = Bool.false) → x6.card ≤ (8 : ℕ) * x5.size := by
  intro x1 x2 x3 _x4 x5 x6 hx1 hx2 hLine hUniq hAO x12 x13 x14 hSafe hMem
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs ++ [g]).foldl step x = gs.foldl step x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false)] := by
    intro gs g x
    simp [step, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs.foldl step x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [run_snoc]
      simp [ih]
      omega
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length →
      ((gs ++ hs).foldl step x).getD i false = (gs.foldl step x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc]
      have hlen : ((gs ++ hs).foldl step x).length = x.length + (gs ++ hs).length := run_length (gs ++ hs) x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen, List.length_append]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
    intro gs x i hi
    have := run_prefix [] gs x i (by simpa using hi)
    simpa using this
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (gs.foldl step x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (gs.foldl step x).length = x.length + gs.length := run_length gs x
      have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then ((gs ++ [g]).foldl step x).getD i false else false) =
          l.map fun i => if i < x.length + k then (gs.foldl step x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · exact run_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
        exact ih j h
      · have hjj : j = gs.length := by simp at hj; omega
        subst hjj
        have hg : (gs ++ [g])[gs.length] = g := by simp
        rw [hg, same _ le_rfl, run_snoc, ← hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hpath_true : ∀ (x : Fin (x2 + x2) → Bool) (u v : ℕ),
      x14 x u v → x12 v x = true → x12 u x = true := by
    intro x u v hp
    induction hp with
    | refl => intro h; exact h
    | @tail b c _ hstep ih =>
      intro _
      rcases hstep with ⟨_, _, _, _, hb, _⟩
      exact ih hb
  have hMem' : ∀ e ∈ x6, x3 e.1 e.2 ∧ x12 x5.output (x13 e) = Bool.true ∧
      ∃ g < x5.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x5 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        x12 (x2 + x2 + g) (x13 e) = Bool.true ∧
        ∀ (k : Fin (2 : ℕ)),
          x2 + x2 ≤ PEqualNP.TopForm.opnd x5 g k ∧
          PEqualNP.TopForm.opnd x5 g k < x2 + x2 + g ∧
          x12 (PEqualNP.TopForm.opnd x5 g k) (x13 e) = Bool.true ∧
          (x12 (PEqualNP.TopForm.opnd x5 g k) fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 e.1)) = Bool.false ∧
          (x12 (PEqualNP.TopForm.opnd x5 g k) fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.natAdd x2 e.2)) = Bool.false := by
    intro e he
    rcases hMem e he with ⟨hinc, houtTrue, g, hg, hand, hpath, hzeros⟩
    have hgTrue : x12 (x2 + x2 + g) (x13 e) = true := hpath_true (x13 e) (x2 + x2 + g) x5.output hpath houtTrue
    have hg' : g < x5.gates.length := hg
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x5 g = x5.gates[g] :=
      List.getD_eq_getElem _ _ hg'
    have hmemG : PEqualNP.MetaComplexity.NestedCover.gateAt x5 g ∈ x5.gates := by
      rw [hge]; exact List.getElem_mem hg'
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hmemG)
    have haLt : a < x2 + x2 + g := hAO.2.1 g hg' a (by rw [hab]; simp)
    have hbLt : b < x2 + x2 + g := hAO.2.1 g hg' b (by rw [hab]; simp)
    have hpair_eval : x12 (x2 + x2 + g) (x13 e) = (x12 a (x13 e) && x12 b (x13 e)) := by
      change (x5.gates.foldl step (List.ofFn (x13 e))).getD (x2 + x2 + g) false = _
      have hrg := run_gate x5.gates (List.ofFn (x13 e)) g hg'
      rw [List.length_ofFn] at hrg
      rw [hrg, ← hge, hand, hab]
      simp only [List.map_cons, List.map_nil, haLt, hbLt, ite_true]
      change ([(x5.gates.foldl step (List.ofFn (x13 e))).getD a false,
        (x5.gates.foldl step (List.ofFn (x13 e))).getD b false].all id) = _
      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rfl
    rw [hpair_eval] at hgTrue
    obtain ⟨haTrue, hbTrue⟩ := Bool.and_eq_true_iff.mp hgTrue
    refine ⟨hinc, houtTrue, g, hg, hand, hpath_true (x13 e) (x2 + x2 + g) x5.output hpath houtTrue, fun k => ?_⟩
    have hzeroK := hzeros k
    have hopVal : (PEqualNP.TopForm.opnd x5 g k = a ∨ PEqualNP.TopForm.opnd x5 g k = b) := by
      fin_cases k
      · left; change (PEqualNP.MetaComplexity.NestedCover.gateAt x5 g).inputs.getD 0 0 = a; rw [hab]; rfl
      · right; change (PEqualNP.MetaComplexity.NestedCover.gateAt x5 g).inputs.getD 1 0 = b; rw [hab]; rfl
    have hkopLt : PEqualNP.TopForm.opnd x5 g k < x2 + x2 + g := by
      rcases hopVal with h | h <;> rw [h] <;> assumption
    have hkopTrue : x12 (PEqualNP.TopForm.opnd x5 g k) (x13 e) = true := by
      rcases hopVal with h | h <;> rw [h] <;> assumption
    have hkopGe : x2 + x2 ≤ PEqualNP.TopForm.opnd x5 g k := by
      by_contra hlt
      have hlt' : PEqualNP.TopForm.opnd x5 g k < x2 + x2 := by omega
      have hT := hkopTrue
      change (x5.gates.foldl step (List.ofFn (x13 e))).getD (PEqualNP.TopForm.opnd x5 g k) false = true at hT
      rw [run_input x5.gates _ _ (by rw [List.length_ofFn]; exact hlt')] at hT
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hT
      simp only [hlt', dite_true, Option.getD_some, x13, decide_eq_true_eq] at hT
      rcases hT with hcast | hnat
      · have hF := hzeroK.1
        change (x5.gates.foldl step (List.ofFn fun x20 : Fin (x2 + x2) => Decidable.decide (x20 = Fin.castAdd x2 e.1))).getD (PEqualNP.TopForm.opnd x5 g k) false = false at hF
        rw [run_input x5.gates _ _ (by rw [List.length_ofFn]; exact hlt')] at hF
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hF
        simp only [hlt', dite_true, Option.getD_some, hcast, decide_true] at hF
        cases hF
      · have hF := hzeroK.2
        change (x5.gates.foldl step (List.ofFn fun x20 : Fin (x2 + x2) => Decidable.decide (x20 = Fin.natAdd x2 e.2))).getD (PEqualNP.TopForm.opnd x5 g k) false = false at hF
        rw [run_input x5.gates _ _ (by rw [List.length_ofFn]; exact hlt')] at hF
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hF
        simp only [hlt', dite_true, Option.getD_some, hnat, decide_true] at hF
        cases hF
    exact ⟨hkopGe, hkopLt, hkopTrue, hzeroK.1, hzeroK.2⟩
  exact hBothGateInputsLB x1 x2 x3 x5 x6 hx1 hx2 hLine hUniq (hUncov x1 x2 x3 (by omega) hx2 hLine) hAO hSafe hMem'
