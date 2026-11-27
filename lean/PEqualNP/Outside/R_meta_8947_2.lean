import PEqualNP.Defs

-- Extract the two operands of the top OR gate at x4.output and pigeonhole onto the wire with larger incident-pair acceptance sum.
theorem PEqualNP.Outside.R_meta_8947_2
    (hLineInter :
      ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
        (∀ p1 p2 : Fin n, p1 ≠ p2 → ∃! l : Fin n, p1 ∈ S l ∧ p2 ∈ S l) →
        ∀ l1 l2 : Fin n, l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ))
    (hHalfCover :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        (200 : ℕ) ≤ q →
        n = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin n, (S l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin n, p1 ≠ p2 → ∃! l : Fin n, p1 ∈ S l ∧ p2 ∈ S l) →
        (∀ l1 l2 : Fin n, l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ)) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        w < C.output →
        C.output < n + n + C.size →
        (∀ (X Y : Finset (Fin n)), Y.card ≤ q →
          PEqualNP.GenericRejection.IsFalseInput S X Y →
          (C.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD w Bool.false = Bool.false) →
        n * (q + (1 : ℕ)) ≤ (2 : ℕ) *
          ∑ l : Fin n, {p ∈ S l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w Bool.false = Bool.true}.card →
        n * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
      x2 + x2 ≤ x4.output →
      x4.output < x2 + x2 + x4.size →
      (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate),
        x4.gates[x4.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x15 x16 : Finset (Fin x2)), x16.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x15 x16 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x15 x16) = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 hq hn hdeg huniq hAO _ hle_out hlt_out htop hright hfalse
  rcases htop with ⟨g, hget, hg_or⟩
  let j : ℕ := x4.output - (x2 + x2)
  have hj_lt : j < x4.gates.length := (List.getElem?_eq_some_iff.mp hget).1
  have hg_eq : x4.gates[j] = g := (List.getElem?_eq_some_iff.mp hget).2
  rcases hAO with ⟨hAOO, hRB, hLen⟩
  have hg_len : g.inputs.length = 2 := hLen g (hg_eq ▸ List.getElem_mem hj_lt)
  rcases List.length_eq_two.mp hg_len with ⟨a, b, hab⟩
  have hgate_j : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = g := by
    dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt]
    rw [List.getD_eq_getElem?_getD, hget]
    rfl
  have ha_lt : a < x4.output := by
    have ha_in : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs := by
      rw [hgate_j, hab]; simp
    have ha' := hRB j hj_lt a ha_in
    dsimp [j] at ha'; omega
  have hb_lt : b < x4.output := by
    have hb_in : b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs := by
      rw [hgate_j, hab]; simp
    have hb' := hRB j hj_lt b hb_in
    dsimp [j] at hb'; omega
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g' =>
    w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      (gs.foldl step acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g' gs ih => intro acc; rw [List.foldl_cons, ih]; simp [step]; omega
  have hfold_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool) (k : ℕ),
      k < acc.length → (gs.foldl step acc).getD k false = acc.getD k false := by
    intro gs
    induction gs with
    | nil => intro acc _ _; rfl
    | cons g' gs ih =>
      intro acc k hk
      rw [List.foldl_cons, ih (step acc g') k (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have heval_or : ∀ (X Y : Finset (Fin x2)),
      x4.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
        ((x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD a false ||
         (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD b false) := by
    intro X Y
    let inp := PEqualNP.GenericRejection.incidenceInput X Y
    have hlen_inp : inp.length = x2 + x2 := by
      dsimp only [inp, PEqualNP.GenericRejection.incidenceInput]
      simp only [List.length_append, List.length_ofFn]
    let pre := (x4.gates.take j).foldl step inp
    have hpre_len : pre.length = x4.output := by
      dsimp [pre]
      rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left (le_of_lt hj_lt)]
      dsimp [j]; omega
    have hsplit : x4.gates = x4.gates.take j ++ g :: x4.gates.drop (j + 1) := by
      have h1 : x4.gates.take (j + 1) = x4.gates.take j ++ [g] := by
        rw [List.take_succ_eq_append_getElem hj_lt, hg_eq]
      have h2 := List.take_append_drop (j + 1) x4.gates
      rw [h1, List.append_assoc] at h2
      exact h2.symm
    have hwires : x4.wires inp = (x4.gates.drop (j + 1)).foldl step (step pre g) := by
      change x4.gates.foldl step inp = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hwa : (x4.wires inp).getD a false = pre.getD a false := by
      rw [hwires, hfold_getD (x4.gates.drop (j + 1)) (step pre g) a (by simp [step]; omega)]
      dsimp [step]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rfl
    have hwb : (x4.wires inp).getD b false = pre.getD b false := by
      rw [hwires, hfold_getD (x4.gates.drop (j + 1)) (step pre g) b (by simp [step]; omega)]
      dsimp [step]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rfl
    have hwout : x4.eval inp = (step pre g).getD x4.output false := by
      change (x4.wires inp).getD x4.output false = _
      rw [hwires, hfold_getD (x4.gates.drop (j + 1)) (step pre g) x4.output (by simp [step]; omega)]
    rw [hwout, hwa, hwb]
    dsimp [step]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hpre_len, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some, hg_or, hab]
    simp only [List.map_cons, List.map_nil]
    cases pre.getD a false <;> cases pre.getD b false <;> rfl
  have hinter : ∀ l1 l2 : Fin x2, l1 ≠ l2 → (x3 l1 ∩ x3 l2).card ≤ 1 :=
    hLineInter x2 x3 huniq
  have hfalse_both : ∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 →
      PEqualNP.GenericRejection.IsFalseInput x3 X Y →
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD a false = false ∧
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD b false = false := by
    intro X Y hY hF
    have he := hfalse X Y hY hF
    rw [heval_or] at he
    exact Bool.or_eq_false_iff.mp he
  let sa := ∑ l : Fin x2,
    {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}.card
  let sb := ∑ l : Fin x2,
    {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}.card
  have hline_cov : ∀ l : Fin x2, x1 + 1 ≤
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}.card +
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}.card := by
    intro l
    have hsub : x3 l ⊆
        {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true} ∪
        {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true} := by
      intro p hp
      have hrt := hright l p hp
      rw [heval_or] at hrt
      rcases Bool.or_eq_true_iff.mp hrt with ha_t | hb_t
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, ha_t⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hb_t⟩)
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}
    rw [hdeg l] at hc1
    omega
  have htot : x2 * (x1 + 1) ≤ sa + sb := by
    calc
      x2 * (x1 + 1) = ∑ _l : Fin x2, (x1 + 1) := by simp
      _ ≤ ∑ l : Fin x2,
          ({p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}.card +
           {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}.card) :=
          Finset.sum_le_sum (fun l _ => hline_cov l)
      _ = sa + sb := Finset.sum_add_distrib
  rcases le_or_gt sb sa with hba | hab_lt
  · exact hHalfCover x1 x2 x3 x4 a hq hn hdeg huniq hinter ⟨hAOO, hRB, hLen⟩
      ha_lt hlt_out (fun X Y hY hF => (hfalse_both X Y hY hF).1) (by dsimp [sa, sb] at *; omega)
  · exact hHalfCover x1 x2 x3 x4 b hq hn hdeg huniq hinter ⟨hAOO, hRB, hLen⟩
      hb_lt hlt_out (fun X Y hY hF => (hfalse_both X Y hY hF).2) (by dsimp [sa, sb] at *; omega)
