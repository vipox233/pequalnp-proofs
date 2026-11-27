import PEqualNP.Defs

-- Truncate the circuit right after wire x5 so its output is the final gate wire n + n + (C.size - 1), plus pairwise line intersection.
theorem PEqualNP.Outside.R_meta_9045_2
    (hLineInter :
      ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
        (∀ p1 p2 : Fin n, p1 ≠ p2 → ∃! l : Fin n, p1 ∈ S l ∧ p2 ∈ S l) →
        ∀ l1 l2 : Fin n, l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ))
    (hTruncated :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ q →
        n = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin n, (S l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin n, p1 ≠ p2 → ∃! l : Fin n, p1 ∈ S l ∧ p2 ∈ S l) →
        (∀ l1 l2 : Fin n, l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ)) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        (0 : ℕ) < C.size →
        C.output = n + n + (C.size - (1 : ℕ)) →
        (∀ (X Y : Finset (Fin n)), Y.card ≤ q →
          PEqualNP.GenericRejection.IsFalseInput S X Y →
          C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = Bool.false) →
        n * (q + (1 : ℕ)) ≤ (2 : ℕ) *
          ∑ l : Fin n, {p ∈ S l | C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = Bool.true}.card →
        n * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      x5 < x4.output →
      x4.output < x2 + x2 + x4.size →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 →
        (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) →
      x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) *
        ∑ x14 : Fin x2, {x15 ∈ x3 x14 |
          (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card →
      x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 x5 hq hn hdeg huniq hAO hlt hbound hfalse hsum
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      (gs.foldl step acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have hfold_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool) (j : ℕ),
      j < acc.length → (gs.foldl step acc).getD j false = acc.getD j false := by
    intro gs
    induction gs with
    | nil => intro acc _ _; rfl
    | cons g gs ih =>
      intro acc j hj
      rw [List.foldl_cons, ih (step acc g) j (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have hx2_gt2 : 2 < x2 := by nlinarith
  have hx5_ge : x2 + x2 ≤ x5 := by
    by_contra hnot
    have hlt_in : x5 < x2 + x2 := Nat.lt_of_not_le hnot
    have hev_in : ∀ (p l : Fin x2),
        (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false =
          (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD x5 false := by
      intro p l
      have hlen_in : (PEqualNP.GenericRejection.incidenceInput {p} {l}).length = x2 + x2 := by
        dsimp only [PEqualNP.GenericRejection.incidenceInput]
        simp
      exact hfold_getD x4.gates _ x5 (by omega)
    by_cases hx5_side : x5 < x2
    · have hle_one : ∀ l : Fin x2,
          {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false = true}.card ≤ 1 := by
        intro l
        have hsub : {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false = true} ⊆
            {⟨x5, hx5_side⟩} := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_singleton] at hp ⊢
          rw [hev_in p l] at hp
          have hbit : (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD x5 false = true := hp.2
          dsimp only [PEqualNP.GenericRejection.incidenceInput] at hbit
          rw [List.getD_eq_getElem?_getD] at hbit
          rw [List.getElem?_append_left (by simp [hx5_side])] at hbit
          simp only [List.getElem?_ofFn, hx5_side, ↓reduceDIte, Option.getD_some,
            Finset.mem_singleton, decide_eq_true_eq] at hbit
          exact Fin.ext (congrArg Fin.val hbit).symm
        exact le_trans (Finset.card_le_card hsub) (Finset.card_singleton _).le
      have htot : ∑ l : Fin x2,
          {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false = true}.card ≤ x2 := by
        calc
          ∑ l : Fin x2, _ ≤ ∑ _l : Fin x2, (1 : ℕ) := Finset.sum_le_sum (fun l _ => hle_one l)
          _ = x2 := by simp
      have hcontra : x2 * (x1 + 1) ≤ 2 * x2 := le_trans hsum (by omega)
      nlinarith
    · have hx5_hi : x2 ≤ x5 := Nat.le_of_not_lt hx5_side
      let l0 : Fin x2 := ⟨x5 - x2, by omega⟩
      have hother : ∀ l : Fin x2, l ≠ l0 →
          {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false = true}.card = 0 := by
        intro l hl
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro p hp
        simp only [Finset.mem_filter] at hp
        rw [hev_in p l] at hp
        have hbit : (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD x5 false = true := hp.2
        dsimp only [PEqualNP.GenericRejection.incidenceInput] at hbit
        rw [List.getD_eq_getElem?_getD] at hbit
        rw [List.getElem?_append_right (by simp [hx5_hi])] at hbit
        simp only [List.length_ofFn, List.getElem?_ofFn] at hbit
        have hlt_x2 : x5 - x2 < x2 := by omega
        simp only [hlt_x2, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hbit
        apply hl
        exact Fin.ext (congrArg Fin.val hbit).symm
      have hl0_le :
          {p ∈ x3 l0 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l0})).getD x5 false = true}.card ≤ x1 + 1 := by
        calc
          _ ≤ (x3 l0).card := Finset.card_filter_le _ _
          _ = x1 + 1 := hdeg l0
      have htot : ∑ l : Fin x2,
          {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false = true}.card ≤ x1 + 1 := by
        rw [Finset.sum_eq_single l0 (fun l _ hl => hother l hl) (fun h => absurd (Finset.mem_univ l0) h)]
        exact hl0_le
      have hcontra : x2 * (x1 + 1) ≤ 2 * (x1 + 1) := le_trans hsum (by omega)
      nlinarith
  have hx4_sz : x4.size = x4.gates.length := rfl
  let m : ℕ := x5 - (x2 + x2) + 1
  have hm_le : m ≤ x4.gates.length := by
    rw [← hx4_sz]
    dsimp [m]
    omega
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨x4.gates.take m, x5⟩
  have hC'_sz : C'.size = m := by
    dsimp [C', PEqualNP.CircuitLowerBounds.Circuit.size]
    rw [List.length_take, Nat.min_eq_left hm_le]
  have hC'_pos : 0 < C'.size := by omega
  have hC'_out : C'.output = x2 + x2 + (C'.size - 1) := by
    rw [hC'_sz]
    dsimp [C', m]
    omega
  have hC'_AO : PEqualNP.TopForm.IsAO2 (x2 + x2) C' := by
    rcases hAO with ⟨hAOO, hRB, hLen⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact hAOO g (List.mem_of_mem_take hg)
    · intro j hj i hi
      have hj' : j < m := by
        dsimp [C'] at hj
        rw [List.length_take, Nat.min_eq_left hm_le] at hj
        exact hj
      have hj_full : j < x4.gates.length := lt_of_lt_of_le hj' hm_le
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          PEqualNP.MetaComplexity.NestedCover.gateAt x4 j := by
        dsimp [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_take_of_lt hj']
      rw [hgate] at hi
      exact hRB j hj_full i hi
    · intro g hg
      exact hLen g (List.mem_of_mem_take hg)
  have hC'_eval : ∀ (X Y : Finset (Fin x2)),
      C'.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
        (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD x5 false := by
    intro X Y
    let inp := PEqualNP.GenericRejection.incidenceInput X Y
    have hlen_inp : inp.length = x2 + x2 := by
      dsimp only [inp, PEqualNP.GenericRejection.incidenceInput]
      simp only [List.length_append, List.length_ofFn]
    have hx4_split : x4.wires inp = (x4.gates.drop m).foldl step (C'.wires inp) := by
      change x4.gates.foldl step inp =
        (x4.gates.drop m).foldl step ((x4.gates.take m).foldl step inp)
      rw [← List.foldl_append, List.take_append_drop]
    have hx5_lt_C' : x5 < (C'.wires inp).length := by
      change x5 < ((x4.gates.take m).foldl step inp).length
      rw [hfold_len, hlen_inp, List.length_take, Nat.min_eq_left hm_le]
      omega
    rw [hx4_split, hfold_getD (x4.gates.drop m) (C'.wires inp) x5 hx5_lt_C']
    rfl
  have hinter : ∀ l1 l2 : Fin x2, l1 ≠ l2 → (x3 l1 ∩ x3 l2).card ≤ 1 :=
    hLineInter x2 x3 huniq
  have hC'_false : ∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 →
      PEqualNP.GenericRejection.IsFalseInput x3 X Y →
      C'.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false := by
    intro X Y hY hF
    rw [hC'_eval X Y]
    exact hfalse X Y hY hF
  have hC'_sum : x2 * (x1 + 1) ≤ 2 *
      ∑ l : Fin x2, {p ∈ x3 l | C'.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true}.card := by
    have heq_sum :
        (∑ l : Fin x2, {p ∈ x3 l | C'.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true}.card) =
        (∑ l : Fin x2, {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 false = true}.card) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      congr 1
      ext p
      simp [hC'_eval {p} {l}]
    rw [heq_sum]
    exact hsum
  have hres := hTruncated x1 x2 x3 C' hq hn hdeg huniq hinter hC'_AO hC'_pos hC'_out hC'_false hC'_sum
  have hsz_le : C'.size ≤ x4.size := by
    dsimp [PEqualNP.CircuitLowerBounds.Circuit.size] at *
    omega
  exact le_trans hres (Nat.mul_le_mul_left 100 hsz_le)
