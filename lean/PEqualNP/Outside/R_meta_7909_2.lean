import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7909_2
    (hUncov :
      ∀ (q v : ℕ) (I : Fin v → Fin v → Prop) [DecidableRel I],
        (1 : ℕ) ≤ q →
        v = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ (l : Fin v), Fintype.card { p : Fin v // I p l } = q + (1 : ℕ)) →
        ∀ (Y : Fin v → Bool),
          Fintype.card { l : Fin v // Y l = Bool.true } ≤ q →
          ∃ p : Fin v, ∀ l : Fin v, I p l → Y l = Bool.false)
    (hAndSplitLB :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (400 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        (∀ (Y : Fin x2 → Bool), Fintype.card { l : Fin x2 // Y l = Bool.true } ≤ x1 → ∃ p : Fin x2, ∀ l : Fin x2, x3 p l → Y l = Bool.false) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
        x2 + x2 ≤ a →
        a < b →
        b < x2 + x2 + x5.size →
        (∀ (p l : Fin x2), x3 p l →
          (x5.wires (List.ofFn fun u : Fin (x2 + x2) => Decidable.decide (u = Fin.castAdd x2 p ∨ u = Fin.natAdd x2 l))).getD a Bool.false = Bool.true ∧
          (x5.wires (List.ofFn fun u : Fin (x2 + x2) => Decidable.decide (u = Fin.castAdd x2 p ∨ u = Fin.natAdd x2 l))).getD b Bool.false = Bool.true) →
        (∀ (x16 : Fin (x2 + x2) → Bool),
          Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 →
          (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) →
          (x5.wires (List.ofFn x16)).getD a Bool.false = Bool.false ∨
          (x5.wires (List.ofFn x16)).getD b Bool.false = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (400 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5 hx1 hx2 hLine hUniq hMono houtLo houtHi hOutAnd hStrict hPos hNeg
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
  have hAO : PEqualNP.TopForm.IsAO2 (x2 + x2) x5 := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hMono g hg).1
    · intro j hj i hi
      have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x5 j = x5.gates[j] :=
        List.getD_eq_getElem _ _ hj
      rw [hge] at hi
      obtain ⟨a, b, hab, hlt, hblt⟩ := hStrict j x5.gates[j] (List.getElem?_eq_getElem hj)
      rw [hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
      obtain ⟨a, b, hab, _, _⟩ := hStrict j g (by rw [← hgj]; exact List.getElem?_eq_getElem hj)
      rw [hab]
      rfl
  let j : ℕ := x5.output - (x2 + x2)
  have hj : j < x5.gates.length := by
    change x5.output - (x2 + x2) < x5.size
    omega
  have houtEq : x5.output = x2 + x2 + j := by omega
  rcases hOutAnd with ⟨g, hgSome, hgAnd⟩
  have hgEq : x5.gates[j] = g := by
    have h1 : x5.gates[j]? = Option.some x5.gates[j] := List.getElem?_eq_getElem hj
    rw [h1] at hgSome
    exact Option.some.inj hgSome
  obtain ⟨a, b, hab, habLt, hbLt⟩ := hStrict j g hgSome
  have heval_and : ∀ (x : Fin (x2 + x2) → Bool),
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x =
      ((x5.wires (List.ofFn x)).getD a false && (x5.wires (List.ofFn x)).getD b false) := by
    intro x
    change (x5.gates.foldl step (List.ofFn x)).getD x5.output false = _
    rw [houtEq]
    have hrg := run_gate x5.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hrg
    rw [hrg, hgEq, hgAnd, hab]
    have haLt' : a < x2 + x2 + j := by omega
    simp only [List.map_cons, List.map_nil, haLt', hbLt, ite_true]
    change ([(x5.gates.foldl step (List.ofFn x)).getD a false,
      (x5.gates.foldl step (List.ofFn x)).getD b false].all id) = _
    simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rfl
  have hPosAB : ∀ (p l : Fin x2), x3 p l →
      (x5.wires (List.ofFn fun u : Fin (x2 + x2) => Decidable.decide (u = Fin.castAdd x2 p ∨ u = Fin.natAdd x2 l))).getD a Bool.false = Bool.true ∧
      (x5.wires (List.ofFn fun u : Fin (x2 + x2) => Decidable.decide (u = Fin.castAdd x2 p ∨ u = Fin.natAdd x2 l))).getD b Bool.false = Bool.true := by
    intro p l hpl
    have h1 := hPos p l hpl
    rw [heval_and] at h1
    exact Bool.and_eq_true_iff.mp h1
  have hNegAB : ∀ (x16 : Fin (x2 + x2) → Bool),
      Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 →
      (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) →
      (x5.wires (List.ofFn x16)).getD a Bool.false = Bool.false ∨
      (x5.wires (List.ofFn x16)).getD b Bool.false = Bool.false := by
    intro x16 hcard hno
    have h0 := hNeg x16 hcard hno
    rw [heval_and] at h0
    exact Bool.and_eq_false_iff.mp h0
  have hx2ge3 : 3 ≤ x2 := by
    have : 1 ≤ x1 * x1 := by nlinarith
    rw [hx2, sq]
    omega
  have haGe : x2 + x2 ≤ a := by
    by_contra hlt
    have hlt' : a < x2 + x2 := by omega
    by_cases hap : a < x2
    · let p0 : Fin x2 := ⟨a, hap⟩
      let p1 : Fin x2 := ⟨(a + 1) % x2, Nat.mod_lt _ (by omega)⟩
      let p2 : Fin x2 := ⟨(a + 2) % x2, Nat.mod_lt _ (by omega)⟩
      have hp1ne : p1 ≠ p0 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [p1, p0] at hv
        by_cases h1 : a + 1 < x2
        · rw [Nat.mod_eq_of_lt h1] at hv; omega
        · have : a + 1 = x2 := by omega
          rw [this, Nat.mod_self] at hv; omega
      have hp12ne : p1 ≠ p2 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [p1, p2] at hv
        have hmod : (a + 1) % x2 = (a + 2) % x2 := hv
        by_cases h2 : a + 2 < x2
        · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at hmod; omega
        · by_cases h1 : a + 1 < x2
          · have h2eq : a + 2 = x2 := by omega
            rw [Nat.mod_eq_of_lt h1, h2eq, Nat.mod_self] at hmod; omega
          · have h1eq : a + 1 = x2 := by omega
            have h2eq : a + 2 = x2 + 1 := by omega
            rw [h1eq, Nat.mod_self, h2eq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hmod; omega
      obtain ⟨l, ⟨hp1l, _⟩, _⟩ := hUniq p1 p2 hp12ne
      have hta := (hPosAB p1 l hp1l).1
      change (x5.gates.foldl step (List.ofFn fun u : Fin (x2 + x2) => Decidable.decide (u = Fin.castAdd x2 p1 ∨ u = Fin.natAdd x2 l))).getD a false = true at hta
      rw [run_input x5.gates _ a (by rw [List.length_ofFn]; omega)] at hta
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hta
      simp only [hlt', dite_true, Option.getD_some, decide_eq_true_eq] at hta
      rcases hta with hcast | hnat
      · apply hp1ne
        have hv := congrArg Fin.val hcast
        simp only [Fin.val_castAdd] at hv
        exact Fin.ext hv.symm
      · have hv := congrArg Fin.val hnat
        simp only [Fin.val_natAdd] at hv
        omega
    · let l0 : Fin x2 := ⟨a - x2, by omega⟩
      have hcard_lt : Fintype.card { p : Fin x2 // x3 p l0 } < Fintype.card (Fin x2) := by
        rw [hLine l0, Fintype.card_fin, hx2, sq]
        nlinarith
      have hnotall : ¬∀ p : Fin x2, x3 p l0 := by
        intro hall
        have h1 : Fintype.card { p : Fin x2 // x3 p l0 } = Fintype.card (Fin x2) := by
          refine Fintype.card_congr ⟨fun x => x.1, fun p => ⟨p, hall p⟩, fun x => rfl, fun p => rfl⟩
        omega
      rw [not_forall] at hnotall
      obtain ⟨p1, hp1n⟩ := hnotall
      let p2 : Fin x2 := ⟨(p1.val + 1) % x2, Nat.mod_lt _ (by omega)⟩
      have hp12ne : p1 ≠ p2 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [p2] at hv
        by_cases h1 : p1.val + 1 < x2
        · rw [Nat.mod_eq_of_lt h1] at hv; omega
        · have : p1.val + 1 = x2 := by omega
          rw [this, Nat.mod_self] at hv; omega
      obtain ⟨l, ⟨hp1l, _⟩, _⟩ := hUniq p1 p2 hp12ne
      have hlne : l ≠ l0 := by
        intro h
        subst h
        exact hp1n hp1l
      have hta := (hPosAB p1 l hp1l).1
      change (x5.gates.foldl step (List.ofFn fun u : Fin (x2 + x2) => Decidable.decide (u = Fin.castAdd x2 p1 ∨ u = Fin.natAdd x2 l))).getD a false = true at hta
      rw [run_input x5.gates _ a (by rw [List.length_ofFn]; omega)] at hta
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hta
      simp only [hlt', dite_true, Option.getD_some, decide_eq_true_eq] at hta
      rcases hta with hcast | hnat
      · have hv := congrArg Fin.val hcast
        simp only [Fin.val_castAdd] at hv
        omega
      · apply hlne
        have hv := congrArg Fin.val hnat
        simp only [Fin.val_natAdd] at hv
        exact Fin.ext (by simp only [l0]; omega)
  exact hAndSplitLB x1 x2 x3 x5 a b hx1 hx2 hLine hUniq (hUncov x1 x2 x3 (by omega) hx2 hLine) hAO haGe habLt (by omega) hPosAB hNegAB
