import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25686_aux

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

private theorem b2z_xor (a b : Bool) : b2z (Bool.xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> rfl

private theorem b2z_decide_eq_one (t : ZMod 2) : b2z (decide (t = 1)) = t := by
  revert t
  decide

private theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

private theorem zmod2_vec_add_self {r : ℕ} (v : Fin r → ZMod 2) : v + v = 0 := by
  ext i
  exact zmod2_add_self (v i)

private theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b h
  decide

private theorem box_b2z {n r : ℕ} (x y : Fin n → Fin r → ZMod 2) (f g : Fin n → ZMod 2)
    (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    let G := fun row col => decide (dotProduct (x row) (y col) + f row + g col = 1)
    b2z (Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i)))) =
      dotProduct (x i + x j) (y (π i) + y (π j)) := by
  intro G
  simp only [b2z_xor, G, b2z_decide_eq_one, add_dotProduct, dotProduct_add]
  calc dotProduct (x i) (y (π i)) + f i + g (π i) +
        (dotProduct (x j) (y (π j)) + f j + g (π j)) +
        (dotProduct (x i) (y (π j)) + f i + g (π j) +
        (dotProduct (x j) (y (π i)) + f j + g (π i)))
      = (dotProduct (x i) (y (π i)) + dotProduct (x j) (y (π i)) +
        (dotProduct (x i) (y (π j)) + dotProduct (x j) (y (π j)))) +
        (f i + f i) + (f j + f j) + (g (π i) + g (π i)) + (g (π j) + g (π j)) := by ring
    _ = dotProduct (x i) (y (π i)) + dotProduct (x j) (y (π i)) +
        (dotProduct (x i) (y (π j)) + dotProduct (x j) (y (π j))) := by
        simp only [zmod2_add_self, add_zero]

private theorem exists_nonzero_annihilator {r : ℕ} (S : Submodule (ZMod 2) (Fin r → ZMod 2))
    (hS : S ≠ ⊤) : ∃ a : Fin r → ZMod 2, a ≠ 0 ∧ ∀ v ∈ S, dotProduct a v = 0 := by
  obtain ⟨W, hSW⟩ := Submodule.exists_isCompl S
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply hS
    have h := hSW.sup_eq_top
    rw [hbot, sup_bot_eq] at h
    exact h
  obtain ⟨w, hwW, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hexi : ∃ i : Fin r, w i ≠ 0 := by
    by_contra hno
    apply hwne
    ext i
    by_contra hi
    exact hno ⟨i, hi⟩
  obtain ⟨i0, hi0⟩ := hexi
  let projW : (Fin r → ZMod 2) →ₗ[ZMod 2] W := Submodule.projectionOnto W S hSW.symm
  let L : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => (projW v).1 i0
      map_add' := fun v1 v2 => by simp [map_add]
      map_smul' := fun c v => by simp [map_smul] }
  let a : Fin r → ZMod 2 := fun j => L (Pi.single j 1)
  have hdot : ∀ v : Fin r → ZMod 2, dotProduct a v = L v := by
    intro v
    have hsum : ∑ j : Fin r, v j • Pi.single j (1 : ZMod 2) = v := by
      ext k
      simp [Pi.single_apply]
    conv_rhs => rw [← hsum]
    rw [map_sum]
    unfold dotProduct
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨a, ?_, ?_⟩
  · intro ha0
    have hLw : L w = 0 := by rw [← hdot w, ha0, zero_dotProduct]
    have hpw : projW w = ⟨w, hwW⟩ := Submodule.projectionOnto_apply_left hSW.symm ⟨w, hwW⟩
    have : w i0 = 0 := by
      change (projW w).1 i0 = 0 at hLw
      rw [hpw] at hLw
      exact hLw
    exact hi0 this
  · intro v hv
    rw [hdot v]
    have hpv : projW v = 0 := Submodule.projectionOnto_apply_right hSW.symm ⟨v, hv⟩
    change (projW v).1 i0 = 0
    rw [hpv]
    rfl

private theorem span_diff_eq_top {n r t : ℕ} (z : Fin n → Fin r → ZMod 2)
    (hrob : ∀ a : Fin r → ZMod 2, a ≠ 0 → ∀ b : ZMod 2,
      t < ((Finset.univ : Finset (Fin n)).filter (fun label => dotProduct a (z label) ≠ b)).card)
    (K : Finset (Fin n)) (hK : n ≤ K.card + t) (k₀ : Fin n) :
    Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = z i + z k₀ } = ⊤ := by
  by_contra hne
  obtain ⟨a, ha0, hann⟩ := exists_nonzero_annihilator _ hne
  have hgt := hrob a ha0 (dotProduct a (z k₀))
  have hsub : (Finset.univ : Finset (Fin n)).filter
      (fun label => dotProduct a (z label) ≠ dotProduct a (z k₀)) ⊆ Kᶜ := by
    intro i hi
    have hne_i : dotProduct a (z i) ≠ dotProduct a (z k₀) := (Finset.mem_filter.1 hi).2
    rw [Finset.mem_compl]
    intro hiK
    have h0 : dotProduct a (z i + z k₀) = 0 :=
      hann (z i + z k₀) (Submodule.subset_span ⟨i, hiK, rfl⟩)
    rw [dotProduct_add] at h0
    exact hne_i (zmod2_eq_of_add_eq_zero h0)
  have hle := Finset.card_le_card hsub
  have hcompl : Kᶜ.card = n - K.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  omega

private theorem linearEquiv_matrix {r : ℕ}
    (φ : (Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)) :
    ∃ T : Matrix (Fin r) (Fin r) (ZMod 2),
      (∀ w, T.mulVec w = φ w) ∧ Function.Bijective T.mulVec := by
  let T : Matrix (Fin r) (Fin r) (ZMod 2) := Matrix.of fun row col => φ (Pi.single col 1) row
  have hTmul : ∀ w : Fin r → ZMod 2, T.mulVec w = φ w := by
    intro w
    have hsum : ∑ col : Fin r, w col • Pi.single col (1 : ZMod 2) = w := by
      ext row
      simp [Pi.single_apply]
    conv_rhs => rw [← hsum]
    rw [map_sum]
    ext row
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, T, Matrix.of_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun col _ => mul_comm _ _
  refine ⟨T, hTmul, ?_⟩
  have hfn : T.mulVec = φ := funext hTmul
  rw [hfn]
  exact φ.bijective

private theorem symm_quad_add {r : ℕ} (T : Matrix (Fin r) (Fin r) (ZMod 2))
    (hT : T.transpose = T) (v w : Fin r → ZMod 2) :
    dotProduct (v + w) (T.mulVec (v + w)) =
      dotProduct v (T.mulVec v) + dotProduct w (T.mulVec w) := by
  have hcross : dotProduct v (T.mulVec w) = dotProduct w (T.mulVec v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hT, dotProduct_comm]
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross]
  calc dotProduct v (T.mulVec v) + dotProduct w (T.mulVec v) +
        (dotProduct w (T.mulVec v) + dotProduct w (T.mulVec w))
      = dotProduct v (T.mulVec v) + dotProduct w (T.mulVec w) +
        (dotProduct w (T.mulVec v) + dotProduct w (T.mulVec v)) := by ring
    _ = dotProduct v (T.mulVec v) + dotProduct w (T.mulVec w) := by
        rw [zmod2_add_self, add_zero]

private theorem exists_perm_matching {n r : ℕ} (x y : Fin n → Fin r → ZMod 2)
    (T : Matrix (Fin r) (Fin r) (ZMod 2)) (b : Fin r → ZMod 2)
    (hTbij : Function.Bijective T.mulVec) :
    let mult := fun (bank : Fin n → Fin r → ZMod 2) (type : Fin r → ZMod 2) =>
      ((Finset.univ : Finset (Fin n)).filter (fun name => bank name = type)).card
    ∃ (π : Equiv.Perm (Fin n)) (A : Finset (Fin n)),
      (∀ i ∈ A, y (π i) = T.mulVec (x i) + b) ∧
      ∀ s : ZMod 2,
        (A.filter (fun i => dotProduct (x i) (T.mulVec (x i)) = s)).card =
          ∑ v ∈ (Finset.univ : Finset (Fin r → ZMod 2)).filter
              (fun w => dotProduct w (T.mulVec w) = s),
            min (mult x v) (mult y (T.mulVec v + b)) := by
  intro mult
  let Xv : (Fin r → ZMod 2) → Finset (Fin n) := fun v => Finset.univ.filter (fun i => x i = v)
  let Yv : (Fin r → ZMod 2) → Finset (Fin n) :=
    fun v => Finset.univ.filter (fun j => y j = T.mulVec v + b)
  let mv : (Fin r → ZMod 2) → ℕ := fun v => min (Xv v).card (Yv v).card
  let Av : (Fin r → ZMod 2) → Finset (Fin n) := fun v => ((Xv v).sort (· ≤ ·)).take (mv v) |>.toFinset
  let Bv : (Fin r → ZMod 2) → Finset (Fin n) := fun v => ((Yv v).sort (· ≤ ·)).take (mv v) |>.toFinset
  have hAv_sub : ∀ v, Av v ⊆ Xv v := by
    intro v i hi
    have h1 : i ∈ ((Xv v).sort (· ≤ ·)).take (mv v) := List.mem_toFinset.mp hi
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take h1)
  have hBv_sub : ∀ v, Bv v ⊆ Yv v := by
    intro v j hj
    have h1 : j ∈ ((Yv v).sort (· ≤ ·)).take (mv v) := List.mem_toFinset.mp hj
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take h1)
  have hAv_card : ∀ v, (Av v).card = mv v := by
    intro v
    have hnd : (((Xv v).sort (· ≤ ·)).take (mv v)).Nodup :=
      ((Xv v).sort_nodup (· ≤ ·)).take
    rw [List.toFinset_card_of_nodup hnd, List.length_take, Finset.length_sort]
    exact min_eq_left (Nat.min_le_left _ _)
  have hBv_card : ∀ v, (Bv v).card = mv v := by
    intro v
    have hnd : (((Yv v).sort (· ≤ ·)).take (mv v)).Nodup :=
      ((Yv v).sort_nodup (· ≤ ·)).take
    rw [List.toFinset_card_of_nodup hnd, List.length_take, Finset.length_sort]
    exact min_eq_left (Nat.min_le_right _ _)
  have hAv_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r → ZMod 2))) Av := by
    intro v1 _ v2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i h1 h2
    have e1 : x i = v1 := (Finset.mem_filter.1 (hAv_sub v1 h1)).2
    have e2 : x i = v2 := (Finset.mem_filter.1 (hAv_sub v2 h2)).2
    exact hne (e1.symm.trans e2)
  have hBv_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r → ZMod 2))) Bv := by
    intro v1 _ v2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro j h1 h2
    have e1 : y j = T.mulVec v1 + b := (Finset.mem_filter.1 (hBv_sub v1 h1)).2
    have e2 : y j = T.mulVec v2 + b := (Finset.mem_filter.1 (hBv_sub v2 h2)).2
    have hT : T.mulVec v1 = T.mulVec v2 := add_right_cancel (e1.symm.trans e2)
    exact hne (hTbij.1 hT)
  let A : Finset (Fin n) := Finset.univ.biUnion Av
  let B : Finset (Fin n) := Finset.univ.biUnion Bv
  have hAcard : A.card = ∑ v : Fin r → ZMod 2, mv v := by
    rw [Finset.card_biUnion hAv_disj]
    exact Finset.sum_congr rfl fun v _ => hAv_card v
  have hBcard : B.card = ∑ v : Fin r → ZMod 2, mv v := by
    rw [Finset.card_biUnion hBv_disj]
    exact Finset.sum_congr rfl fun v _ => hBv_card v
  have hfev : ∀ v : Fin r → ZMod 2, ↥(Av v) ≃ ↥(Bv v) := fun v =>
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAv_card v, hBv_card v])
  have hmemA_x : ∀ i ∈ A, i ∈ Av (x i) := by
    intro i hi
    obtain ⟨v, _, hiv⟩ := Finset.mem_biUnion.1 hi
    have hxi : x i = v := (Finset.mem_filter.1 (hAv_sub v hiv)).2
    rwa [hxi]
  have hmemB_y : ∀ j ∈ B, ∃! v, j ∈ Bv v := by
    intro j hj
    obtain ⟨v, _, hjv⟩ := Finset.mem_biUnion.1 hj
    refine ⟨v, hjv, fun v' hjv' => ?_⟩
    by_contra hne
    exact Finset.disjoint_left.1 (hBv_disj (Finset.mem_univ v') (Finset.mem_univ v) hne) hjv' hjv
  have hfev_symm_eq : ∀ {v1 v2 : Fin r → ZMod 2} (_ : v1 = v2) (x0 : Fin n)
      (h1 : x0 ∈ Bv v1) (h2 : x0 ∈ Bv v2),
      ((hfev v1).symm ⟨x0, h1⟩).1 = ((hfev v2).symm ⟨x0, h2⟩).1 := by
    rintro v1 v2 rfl x0 h1 h2
    rfl
  have hfev_eq : ∀ {v1 v2 : Fin r → ZMod 2} (_ : v1 = v2) (x0 : Fin n)
      (h1 : x0 ∈ Av v1) (h2 : x0 ∈ Av v2),
      (hfev v1 ⟨x0, h1⟩).1 = (hfev v2 ⟨x0, h2⟩).1 := by
    rintro v1 v2 rfl x0 h1 h2
    rfl
  let eAB : ↥A ≃ ↥B :=
    { toFun := fun i =>
        let j := hfev (x i.1) ⟨i.1, hmemA_x i.1 i.2⟩
        ⟨j.1, Finset.mem_biUnion.2 ⟨x i.1, Finset.mem_univ _, j.2⟩⟩
      invFun := fun j =>
        let v := (hmemB_y j.1 j.2).choose
        let hv : j.1 ∈ Bv v := (hmemB_y j.1 j.2).choose_spec.1
        let i := (hfev v).symm ⟨j.1, hv⟩
        ⟨i.1, Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, i.2⟩⟩
      left_inv := fun i => by
        apply Subtype.ext
        set j := hfev (x i.1) ⟨i.1, hmemA_x i.1 i.2⟩
        have hjB : j.1 ∈ B := Finset.mem_biUnion.2 ⟨x i.1, Finset.mem_univ _, j.2⟩
        have hv : (hmemB_y j.1 hjB).choose = x i.1 :=
          (hmemB_y j.1 hjB).choose_spec.2 (x i.1) j.2 |>.symm
        change ((hfev (hmemB_y j.1 hjB).choose).symm ⟨j.1, (hmemB_y j.1 hjB).choose_spec.1⟩).1 = i.1
        rw [hfev_symm_eq hv j.1 _ j.2]
        exact congrArg Subtype.val ((hfev (x i.1)).symm_apply_apply ⟨i.1, hmemA_x i.1 i.2⟩)
      right_inv := fun j => by
        apply Subtype.ext
        set v := (hmemB_y j.1 j.2).choose
        have hv : j.1 ∈ Bv v := (hmemB_y j.1 j.2).choose_spec.1
        set i := (hfev v).symm ⟨j.1, hv⟩
        have hxi : x i.1 = v := (Finset.mem_filter.1 (hAv_sub v i.2)).2
        change (hfev (x i.1) ⟨i.1, _⟩).1 = j.1
        rw [hfev_eq hxi i.1 _ i.2]
        exact congrArg Subtype.val ((hfev v).apply_symm_apply ⟨j.1, hv⟩) }
  have hcEq : Fintype.card ↥(Aᶜ) = Fintype.card ↥(Bᶜ) := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Finset.card_compl, hAcard, hBcard]
  let eC : ↥(Aᶜ) ≃ ↥(Bᶜ) := Fintype.equivOfCardEq hcEq
  let π : Equiv.Perm (Fin n) :=
    { toFun := fun i => if h : i ∈ A then (eAB ⟨i, h⟩).1 else (eC ⟨i, Finset.mem_compl.2 h⟩).1
      invFun := fun j => if h : j ∈ B then (eAB.symm ⟨j, h⟩).1 else (eC.symm ⟨j, Finset.mem_compl.2 h⟩).1
      left_inv := fun i => by
        by_cases h : i ∈ A
        · simp only [h, ↓reduceDIte]
          have hB : (eAB ⟨i, h⟩).1 ∈ B := (eAB ⟨i, h⟩).2
          simp only [hB, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
        · simp only [h, ↓reduceDIte]
          have hnotB : (eC ⟨i, Finset.mem_compl.2 h⟩).1 ∉ B :=
            Finset.mem_compl.1 (eC ⟨i, Finset.mem_compl.2 h⟩).2
          simp only [hnotB, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun j => by
        by_cases h : j ∈ B
        · simp only [h, ↓reduceDIte]
          have hA : (eAB.symm ⟨j, h⟩).1 ∈ A := (eAB.symm ⟨j, h⟩).2
          simp only [hA, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]
        · simp only [h, ↓reduceDIte]
          have hnotA : (eC.symm ⟨j, Finset.mem_compl.2 h⟩).1 ∉ A :=
            Finset.mem_compl.1 (eC.symm ⟨j, Finset.mem_compl.2 h⟩).2
          simp only [hnotA, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply] }
  refine ⟨π, A, ?_, ?_⟩
  · intro i hi
    have hπ : π i = (eAB ⟨i, hi⟩).1 := by simp [π, hi]
    rw [hπ]
    have hj : (eAB ⟨i, hi⟩).1 ∈ Bv (x i) := (hfev (x i) ⟨i, hmemA_x i hi⟩).2
    exact (Finset.mem_filter.1 (hBv_sub (x i) hj)).2
  · intro s
    have hfilt : A.filter (fun i => dotProduct (x i) (T.mulVec (x i)) = s) =
        ((Finset.univ : Finset (Fin r → ZMod 2)).filter
          (fun w => dotProduct w (T.mulVec w) = s)).biUnion Av := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, A]
      constructor
      · rintro ⟨⟨v, hiv⟩, hs⟩
        have hxi : x i = v := (Finset.mem_filter.1 (hAv_sub v hiv)).2
        rw [hxi] at hs
        exact ⟨v, hs, hiv⟩
      · rintro ⟨v, hs, hiv⟩
        have hxi : x i = v := (Finset.mem_filter.1 (hAv_sub v hiv)).2
        exact ⟨⟨v, hiv⟩, by rw [hxi]; exact hs⟩
    rw [hfilt, Finset.card_biUnion (fun v1 _ v2 _ hne => hAv_disj (Finset.mem_univ v1) (Finset.mem_univ v2) hne)]
    refine Finset.sum_congr rfl fun v _ => hAv_card v

theorem main_aux (n r u t : ℕ) (x y : Fin n → Fin r → ZMod 2) (f g : Fin n → ZMod 2)
    (hrobx : ∀ a : Fin r → ZMod 2, a ≠ 0 → ∀ b : ZMod 2,
      t < ((Finset.univ : Finset (Fin n)).filter (fun label => dotProduct a (x label) ≠ b)).card)
    (hroby : ∀ a : Fin r → ZMod 2, a ≠ 0 → ∀ b : ZMod 2,
      t < ((Finset.univ : Finset (Fin n)).filter (fun label => dotProduct a (y label) ≠ b)).card) :
    let V := Fin r → ZMod 2
    let M := Matrix (Fin r) (Fin r) (ZMod 2)
    let G := fun row col => decide (dotProduct (x row) (y col) + f row + g col = 1)
    (∃ (π : Equiv.Perm (Fin n)) (K L : Finset (Fin n)),
      L ⊆ K ∧ L.card ≤ u ∧ n ≤ K.card + t ∧ ∀ i ∈ K, ∀ j ∈ K,
        Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
          Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔
    ∃ (T : M) (b : V), T.transpose = T ∧ Function.Bijective T.mulVec ∧
      let mult := fun (bank : Fin n → V) (type : V) =>
        ((Finset.univ : Finset (Fin n)).filter (fun name => bank name = type)).card
      let cap := fun (s : ZMod 2) =>
        ∑ v ∈ (Finset.univ : Finset V).filter (fun w => dotProduct w (T.mulVec w) = s),
          min (mult x v) (mult y (T.mulVec v + b))
      n ≤ t + max (cap 0) (cap 1) + min u (min (cap 0) (cap 1)) := by
  intro V M G
  by_cases hnt : n ≤ t
  · constructor
    · intro _
      refine ⟨1, 0, Matrix.transpose_one, ?_, ?_⟩
      · have h1 : (1 : M).mulVec = id := by ext v i; simp
        rw [h1]
        exact Function.bijective_id
      · omega
    · intro _
      exact ⟨1, ∅, ∅, Finset.empty_subset _, Nat.zero_le u, by omega, fun i hi => by simp at hi⟩
  · constructor
    · rintro ⟨π, K, L, hLK, hLu, hKt, hbox⟩
      have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨k₀, hk₀⟩ := hKne
      have hboxZ : ∀ i ∈ K, ∀ j ∈ K,
          dotProduct (x i + x j) (y (π i) + y (π j)) =
            b2z (decide (i ∈ L)) + b2z (decide (j ∈ L)) := by
        intro i hi j hj
        have h1 := congrArg b2z (hbox i hi j hj)
        rw [box_b2z x y f g π i j, b2z_xor] at h1
        exact h1
      let ux : Fin n → V := fun i => x i + x k₀
      let vy : Fin n → V := fun i => y (π i) + y (π k₀)
      have hsym_gen : ∀ i ∈ K, ∀ j ∈ K, dotProduct (ux i) (vy j) = dotProduct (ux j) (vy i) := by
        intro i hi j hj
        have e1 := hboxZ i hi k₀ hk₀
        have e2 := hboxZ j hj k₀ hk₀
        have e3 := hboxZ i hi j hj
        have hxi : x i + x j = ux i + ux j := by
          ext c
          change x i c + x j c = (x i c + x k₀ c) + (x j c + x k₀ c)
          calc x i c + x j c = (x i c + x j c) + (x k₀ c + x k₀ c) := by
                rw [zmod2_add_self, add_zero]
            _ = (x i c + x k₀ c) + (x j c + x k₀ c) := by ring
        have hyi : y (π i) + y (π j) = vy i + vy j := by
          ext c
          change y (π i) c + y (π j) c = (y (π i) c + y (π k₀) c) + (y (π j) c + y (π k₀) c)
          calc y (π i) c + y (π j) c = (y (π i) c + y (π j) c) + (y (π k₀) c + y (π k₀) c) := by
                rw [zmod2_add_self, add_zero]
            _ = (y (π i) c + y (π k₀) c) + (y (π j) c + y (π k₀) c) := by ring
        have e1' : dotProduct (ux i) (vy i) = b2z (decide (i ∈ L)) + b2z (decide (k₀ ∈ L)) := e1
        have e2' : dotProduct (ux j) (vy j) = b2z (decide (j ∈ L)) + b2z (decide (k₀ ∈ L)) := e2
        have e3' : dotProduct (ux i) (vy i) + dotProduct (ux i) (vy j) +
            (dotProduct (ux j) (vy i) + dotProduct (ux j) (vy j)) =
            b2z (decide (i ∈ L)) + b2z (decide (j ∈ L)) := by
          rw [← dotProduct_add, ← dotProduct_add, ← add_dotProduct, ← hxi, ← hyi]
          exact e3
        have hsum : dotProduct (ux i) (vy j) + dotProduct (ux j) (vy i) = 0 := by
          calc dotProduct (ux i) (vy j) + dotProduct (ux j) (vy i)
              = (dotProduct (ux i) (vy i) + dotProduct (ux i) (vy j) +
                (dotProduct (ux j) (vy i) + dotProduct (ux j) (vy j))) +
                dotProduct (ux i) (vy i) + dotProduct (ux j) (vy j) := by
                  calc _ = (dotProduct (ux i) (vy j) + dotProduct (ux j) (vy i)) +
                        (dotProduct (ux i) (vy i) + dotProduct (ux i) (vy i)) +
                        (dotProduct (ux j) (vy j) + dotProduct (ux j) (vy j)) := by
                          simp only [zmod2_add_self, add_zero]
                    _ = _ := by ring
            _ = (b2z (decide (i ∈ L)) + b2z (decide (j ∈ L))) +
                (b2z (decide (i ∈ L)) + b2z (decide (k₀ ∈ L))) +
                (b2z (decide (j ∈ L)) + b2z (decide (k₀ ∈ L))) := by rw [e3', e1', e2']
            _ = (b2z (decide (i ∈ L)) + b2z (decide (i ∈ L))) +
                (b2z (decide (j ∈ L)) + b2z (decide (j ∈ L))) +
                (b2z (decide (k₀ ∈ L)) + b2z (decide (k₀ ∈ L))) := by ring
            _ = 0 := by simp only [zmod2_add_self, add_zero]
        exact zmod2_eq_of_add_eq_zero hsum
      have hspan_x : Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = ux i } = ⊤ :=
        span_diff_eq_top x hrobx K hKt k₀
      have hrobyπ : ∀ a : V, a ≠ 0 → ∀ b : ZMod 2,
          t < ((Finset.univ : Finset (Fin n)).filter (fun label => dotProduct a (y (π label)) ≠ b)).card := by
        intro a ha b
        have hcard : ((Finset.univ : Finset (Fin n)).filter
            (fun label => dotProduct a (y (π label)) ≠ b)).card =
            ((Finset.univ : Finset (Fin n)).filter
              (fun label => dotProduct a (y label) ≠ b)).card := by
          refine Finset.card_nbij' (fun i => π i) (fun j => π.symm j) ?_ ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi
          · intro j hj
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            simpa using hj
          · intro i _; simp
          · intro j _; simp
        rw [hcard]
        exact hroby a ha b
      have hspan_y : Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = vy i } = ⊤ :=
        span_diff_eq_top (fun i => y (π i)) hrobyπ K hKt k₀
      let P : Submodule (ZMod 2) (V × V) :=
        Submodule.span (ZMod 2) { p : V × V | ∃ i ∈ K, p = (ux i, vy i) }
      have hP_iso : ∀ p₁ ∈ P, ∀ p₂ ∈ P, dotProduct p₁.1 p₂.2 = dotProduct p₂.1 p₁.2 := by
        have h1 : ∀ i ∈ K, ∀ p₂ ∈ P, dotProduct (ux i) p₂.2 = dotProduct p₂.1 (vy i) := by
          intro i hi
          let S2 : Submodule (ZMod 2) (V × V) :=
            { carrier := { p | dotProduct (ux i) p.2 = dotProduct p.1 (vy i) }, add_mem' := fun {p q} hp hq => by
                show dotProduct (ux i) (p.2 + q.2) = dotProduct (p.1 + q.1) (vy i)
                have hL : dotProduct (ux i) (p.2 + q.2) = dotProduct (ux i) p.2 + dotProduct (ux i) q.2 :=
                  dotProduct_add (ux i) p.2 q.2
                have hR : dotProduct (p.1 + q.1) (vy i) = dotProduct p.1 (vy i) + dotProduct q.1 (vy i) := add_dotProduct p.1 q.1 (vy i)
                rw [hL, hR, hp, hq]
              zero_mem' := by
                show dotProduct (ux i) 0 = dotProduct 0 (vy i)
                simp
              smul_mem' := fun c {p} hp => by
                show dotProduct (ux i) (c • p.2) = dotProduct (c • p.1) (vy i)
                rw [dotProduct_smul, smul_dotProduct, hp] }
          have hsub : P ≤ S2 := by
            unfold P
            rw [Submodule.span_le]
            rintro _ ⟨j, hj, rfl⟩
            exact hsym_gen i hi j hj
          exact fun p₂ hp₂ => hsub hp₂
        intro p₁ hp₁ p₂ hp₂
        let S1 : Submodule (ZMod 2) (V × V) :=
          { carrier := { p | dotProduct p.1 p₂.2 = dotProduct p₂.1 p.2 }, add_mem' := fun {p q} hp hq => by
              show dotProduct (p.1 + q.1) p₂.2 = dotProduct p₂.1 (p.2 + q.2)
              rw [add_dotProduct, dotProduct_add, hp, hq]
            zero_mem' := by
              show dotProduct 0 p₂.2 = dotProduct p₂.1 0
              simp
            smul_mem' := fun c {p} hp => by
              show dotProduct (c • p.1) p₂.2 = dotProduct p₂.1 (c • p.2)
              rw [smul_dotProduct, dotProduct_smul, hp] }
        have hsub : P ≤ S1 := by
          unfold P
          rw [Submodule.span_le]
          rintro _ ⟨i, hi, rfl⟩
          exact h1 i hi p₂ hp₂
        exact hsub hp₁
      let pFst : P →ₗ[ZMod 2] V := (LinearMap.fst (ZMod 2) V V).comp P.subtype
      let pSnd : P →ₗ[ZMod 2] V := (LinearMap.snd (ZMod 2) V V).comp P.subtype
      have hpFst_surj : Function.Surjective pFst := by
        rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan_x, Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨⟨(ux i, vy i), Submodule.subset_span ⟨i, hi, rfl⟩⟩, rfl⟩
      have hpSnd_surj : Function.Surjective pSnd := by
        rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan_y, Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨⟨(ux i, vy i), Submodule.subset_span ⟨i, hi, rfl⟩⟩, rfl⟩
      have hpFst_inj : Function.Injective pFst := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        rintro ⟨⟨p1, p2⟩, hp⟩ hker
        rw [LinearMap.mem_ker] at hker
        have hp1 : p1 = 0 := hker
        subst hp1
        have hp2 : p2 = 0 := by
          ext c
          have hmem : Pi.single c (1 : ZMod 2) ∈ Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = ux i } := by
            rw [hspan_x]; trivial
          let Ann : Submodule (ZMod 2) V :=
            { carrier := { w | dotProduct w p2 = 0 }, add_mem' := fun {w1 w2} h1 h2 => by
                show dotProduct (w1 + w2) p2 = 0
                rw [add_dotProduct, h1, h2, add_zero]
              zero_mem' := by show dotProduct 0 p2 = 0; exact zero_dotProduct p2
              smul_mem' := fun s {w} hw => by
                show dotProduct (s • w) p2 = 0
                rw [smul_dotProduct, hw, smul_zero] }
          have hsub : Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = ux i } ≤ Ann := by
            rw [Submodule.span_le]
            rintro _ ⟨i, hi, rfl⟩
            show dotProduct (ux i) p2 = 0
            have h := hP_iso (ux i, vy i) (Submodule.subset_span ⟨i, hi, rfl⟩) (0, p2) hp
            simpa using h
          have h0 : dotProduct (Pi.single c (1 : ZMod 2)) p2 = 0 := hsub hmem
          change p2 c = 0
          simpa [dotProduct, Pi.single_apply] using h0
        subst hp2
        rfl
      have hpSnd_inj : Function.Injective pSnd := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        rintro ⟨⟨p1, p2⟩, hp⟩ hker
        rw [LinearMap.mem_ker] at hker
        have hp2 : p2 = 0 := hker
        subst hp2
        have hp1 : p1 = 0 := by
          ext c
          have hmem : Pi.single c (1 : ZMod 2) ∈ Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = vy i } := by
            rw [hspan_y]; trivial
          let Ann : Submodule (ZMod 2) V :=
            { carrier := { w | dotProduct p1 w = 0 }, add_mem' := fun {w1 w2} h1 h2 => by
                show dotProduct p1 (w1 + w2) = 0
                rw [dotProduct_add, h1, h2, add_zero]
              zero_mem' := by show dotProduct p1 0 = 0; exact dotProduct_zero p1
              smul_mem' := fun s {w} hw => by
                show dotProduct p1 (s • w) = 0
                rw [dotProduct_smul, hw, smul_zero] }
          have hsub : Submodule.span (ZMod 2) { v | ∃ i ∈ K, v = vy i } ≤ Ann := by
            rw [Submodule.span_le]
            rintro _ ⟨i, hi, rfl⟩
            show dotProduct p1 (vy i) = 0
            have h := hP_iso (p1, 0) hp (ux i, vy i) (Submodule.subset_span ⟨i, hi, rfl⟩)
            simpa using h
          have h0 : dotProduct p1 (Pi.single c (1 : ZMod 2)) = 0 := hsub hmem
          change p1 c = 0
          simpa [dotProduct, Pi.single_apply] using h0
        subst hp1
        rfl
      let eFst : P ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective pFst ⟨hpFst_inj, hpFst_surj⟩
      let eSnd : P ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective pSnd ⟨hpSnd_inj, hpSnd_surj⟩
      let φ : V ≃ₗ[ZMod 2] V := eFst.symm.trans eSnd
      obtain ⟨T, hTmul, hTbij⟩ := linearEquiv_matrix φ
      have hgraph : ∀ w : V, (w, T.mulVec w) ∈ P := by
        intro w
        have h1 : (eFst.symm w).1.1 = w := eFst.apply_symm_apply w
        have h2 : (eFst.symm w).1.2 = T.mulVec w := by
          rw [hTmul]
          rfl
        have hpair : (w, T.mulVec w) = (eFst.symm w).1 := Prod.ext h1.symm h2.symm
        rw [hpair]
        exact (eFst.symm w).2
      have hTsymm : T.transpose = T := by
        ext row col
        have h := hP_iso (Pi.single row 1, T.mulVec (Pi.single row 1)) (hgraph _)
          (Pi.single col 1, T.mulVec (Pi.single col 1)) (hgraph _)
        simpa [Matrix.transpose_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using h.symm
      let b : V := T.mulVec (x k₀) + y (π k₀)
      have haff : ∀ i ∈ K, y (π i) = T.mulVec (x i) + b := by
        intro i hi
        have hmem1 : (ux i, vy i) ∈ P := Submodule.subset_span ⟨i, hi, rfl⟩
        have hmem2 : (ux i, T.mulVec (ux i)) ∈ P := hgraph (ux i)
        have heq : (⟨(ux i, vy i), hmem1⟩ : P) = ⟨(ux i, T.mulVec (ux i)), hmem2⟩ :=
          hpFst_inj rfl
        have hvy : vy i = T.mulVec (ux i) := congrArg (fun z : P => z.1.2) heq
        ext c
        have hc := congrFun hvy c
        simp only [vy, ux, Pi.add_apply, Matrix.mulVec_add] at hc
        change y (π i) c = T.mulVec (x i) c + (T.mulVec (x k₀) c + y (π k₀) c)
        have hadd := congrArg (· + y (π k₀) c) hc
        calc y (π i) c = y (π i) c + (y (π k₀) c + y (π k₀) c) := by
              rw [zmod2_add_self, add_zero]
          _ = (y (π i) c + y (π k₀) c) + y (π k₀) c := by ring
          _ = (T.mulVec (x i) c + T.mulVec (x k₀) c) + y (π k₀) c := hadd
          _ = T.mulVec (x i) c + (T.mulVec (x k₀) c + y (π k₀) c) := by ring
      refine ⟨T, b, hTsymm, hTbij, ?_⟩
      let mult := fun (bank : Fin n → V) (type : V) =>
        ((Finset.univ : Finset (Fin n)).filter (fun name => bank name = type)).card
      let cap := fun (s : ZMod 2) =>
        ∑ v ∈ (Finset.univ : Finset V).filter (fun w => dotProduct w (T.mulVec w) = s),
          min (mult x v) (mult y (T.mulVec v + b))
      let Ks : ZMod 2 → Finset (Fin n) :=
        fun s => K.filter (fun i => dotProduct (x i) (T.mulVec (x i)) = s)
      have hKs_le : ∀ s : ZMod 2, (Ks s).card ≤ cap s := by
        intro s
        have hfib : (Ks s).card = ∑ v ∈ (Finset.univ : Finset V).filter
            (fun w => dotProduct w (T.mulVec w) = s), (K.filter (fun i => x i = v)).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := x) (t := (Finset.univ : Finset V).filter
            (fun w => dotProduct w (T.mulVec w) = s))]
          · refine Finset.sum_congr rfl fun v hv => ?_
            congr 1
            ext i
            simp only [Ks, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            constructor
            · rintro ⟨⟨hiK, _⟩, rfl⟩; exact ⟨hiK, rfl⟩
            · rintro ⟨hiK, rfl⟩; exact ⟨⟨hiK, hv⟩, rfl⟩
          · intro i hi
            simp only [Finset.mem_coe, Ks, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi.2
        rw [hfib]
        refine Finset.sum_le_sum fun v _ => ?_
        refine le_min ?_ ?_
        · exact Finset.card_le_card (fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi.2)
        · have himg : ((K.filter (fun i => x i = v)).image π).card =
              (K.filter (fun i => x i = v)).card :=
            Finset.card_image_of_injective _ π.injective
          rw [← himg]
          refine Finset.card_le_card fun j hj => ?_
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          rw [haff i hi.1, hi.2]
      have hK_split : K.card = (Ks 0).card + (Ks 1).card := by
        have hdisj : Disjoint (Ks 0) (Ks 1) := by
          rw [Finset.disjoint_left]
          intro i h0 h1
          have e0 := (Finset.mem_filter.1 h0).2
          have e1 := (Finset.mem_filter.1 h1).2
          exact absurd (e0.symm.trans e1) (by decide)
        have hunion : K = Ks 0 ∪ Ks 1 := by
          ext i
          simp only [Finset.mem_union, Ks, Finset.mem_filter]
          constructor
          · intro hi
            have hq : dotProduct (x i) (T.mulVec (x i)) = 0 ∨
                dotProduct (x i) (T.mulVec (x i)) = 1 :=
              zmod2_cases (dotProduct (x i) (T.mulVec (x i)))
            rcases hq with hq | hq
            · exact Or.inl ⟨hi, hq⟩
            · exact Or.inr ⟨hi, hq⟩
          · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
        conv_lhs => rw [hunion]
        exact Finset.card_union_of_disjoint hdisj
      let c₀ : ZMod 2 := b2z (decide (k₀ ∈ L)) + dotProduct (x k₀) (T.mulVec (x k₀))
      have hcolor : ∀ i ∈ K, b2z (decide (i ∈ L)) = dotProduct (x i) (T.mulVec (x i)) + c₀ := by
        intro i hi
        have e1 := hboxZ i hi k₀ hk₀
        have hyk : y (π i) + y (π k₀) = T.mulVec (x i + x k₀) := by
          rw [haff i hi, haff k₀ hk₀, Matrix.mulVec_add]
          ext c
          change (T.mulVec (x i) c + b c) + (T.mulVec (x k₀) c + b c) =
            T.mulVec (x i) c + T.mulVec (x k₀) c
          calc _ = T.mulVec (x i) c + T.mulVec (x k₀) c + (b c + b c) := by ring
            _ = T.mulVec (x i) c + T.mulVec (x k₀) c := by rw [zmod2_add_self, add_zero]
        rw [hyk, symm_quad_add T hTsymm (x i) (x k₀)] at e1
        have hadd := congrArg (· + b2z (decide (k₀ ∈ L))) e1
        calc b2z (decide (i ∈ L))
            = b2z (decide (i ∈ L)) + (b2z (decide (k₀ ∈ L)) + b2z (decide (k₀ ∈ L))) := by
                rw [zmod2_add_self, add_zero]
          _ = (b2z (decide (i ∈ L)) + b2z (decide (k₀ ∈ L))) + b2z (decide (k₀ ∈ L)) := by ring
          _ = (dotProduct (x i) (T.mulVec (x i)) + dotProduct (x k₀) (T.mulVec (x k₀))) +
              b2z (decide (k₀ ∈ L)) := hadd.symm
          _ = dotProduct (x i) (T.mulVec (x i)) + c₀ := by dsimp only [c₀]; ring
      have hc₀ : c₀ = 0 ∨ c₀ = 1 := zmod2_cases c₀
      have hK0 := hKs_le 0
      have hK1 := hKs_le 1
      change n ≤ t + max (cap 0) (cap 1) + min u (min (cap 0) (cap 1))
      rcases hc₀ with hc0 | hc1
      · have hL1 : Ks 1 ⊆ L := by
          intro i hi
          have h1 := hcolor i (Finset.mem_filter.1 hi).1
          rw [(Finset.mem_filter.1 hi).2, hc0, add_zero] at h1
          have : decide (i ∈ L) = true := b2z_inj h1
          exact of_decide_eq_true this
        have hK1u : (Ks 1).card ≤ u := le_trans (Finset.card_le_card hL1) hLu
        omega
      · have hL0 : Ks 0 ⊆ L := by
          intro i hi
          have h1 := hcolor i (Finset.mem_filter.1 hi).1
          rw [(Finset.mem_filter.1 hi).2, hc1, zero_add] at h1
          have : decide (i ∈ L) = true := b2z_inj h1
          exact of_decide_eq_true this
        have hK0u : (Ks 0).card ≤ u := le_trans (Finset.card_le_card hL0) hLu
        omega
    · rintro ⟨T, b, hTsymm, hTbij, hcap_ineq⟩
      let mult := fun (bank : Fin n → V) (type : V) =>
        ((Finset.univ : Finset (Fin n)).filter (fun name => bank name = type)).card
      let cap := fun (s : ZMod 2) =>
        ∑ v ∈ (Finset.univ : Finset V).filter (fun w => dotProduct w (T.mulVec w) = s),
          min (mult x v) (mult y (T.mulVec v + b))
      change n ≤ t + max (cap 0) (cap 1) + min u (min (cap 0) (cap 1)) at hcap_ineq
      obtain ⟨π, A, hAaff, hAcard⟩ := exists_perm_matching x y T b hTbij
      let A0 := A.filter (fun i => dotProduct (x i) (T.mulVec (x i)) = 0)
      let A1 := A.filter (fun i => dotProduct (x i) (T.mulVec (x i)) = 1)
      have hA0_eq : A0.card = cap 0 := hAcard 0
      have hA1_eq : A1.card = cap 1 := hAcard 1
      have hdisj01 : Disjoint A0 A1 := by
        rw [Finset.disjoint_left]
        intro i h0 h1
        have e0 := (Finset.mem_filter.1 h0).2
        have e1 := (Finset.mem_filter.1 h1).2
        exact absurd (e0.symm.trans e1) (by decide)
      have hbox_of_color : ∀ (K L : Finset (Fin n)) (c₀ : ZMod 2),
          K ⊆ A → (∀ i ∈ K, b2z (decide (i ∈ L)) = dotProduct (x i) (T.mulVec (x i)) + c₀) →
          ∀ i ∈ K, ∀ j ∈ K,
            Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
              Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
        intro K L c₀ hKA hcol i hi j hj
        apply b2z_inj
        rw [box_b2z x y f g π i j, b2z_xor, hcol i hi, hcol j hj]
        have hyij : y (π i) + y (π j) = T.mulVec (x i + x j) := by
          rw [hAaff i (hKA hi), hAaff j (hKA hj), Matrix.mulVec_add]
          ext c
          change (T.mulVec (x i) c + b c) + (T.mulVec (x j) c + b c) =
            T.mulVec (x i) c + T.mulVec (x j) c
          calc _ = T.mulVec (x i) c + T.mulVec (x j) c + (b c + b c) := by ring
            _ = T.mulVec (x i) c + T.mulVec (x j) c := by rw [zmod2_add_self, add_zero]
        rw [hyij, symm_quad_add T hTsymm (x i) (x j)]
        calc dotProduct (x i) (T.mulVec (x i)) + dotProduct (x j) (T.mulVec (x j))
            = dotProduct (x i) (T.mulVec (x i)) + dotProduct (x j) (T.mulVec (x j)) +
              (c₀ + c₀) := by rw [zmod2_add_self, add_zero]
          _ = (dotProduct (x i) (T.mulVec (x i)) + c₀) +
              (dotProduct (x j) (T.mulVec (x j)) + c₀) := by ring
      by_cases hcmp : A0.card ≤ A1.card
      · obtain ⟨L, hLA0, hLcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right u A0.card)
        let K := A1 ∪ L
        have hdisj : Disjoint A1 L := Disjoint.mono_right hLA0 hdisj01.symm
        refine ⟨π, K, L, Finset.subset_union_right, by omega, ?_, ?_⟩
        · have hKcard : K.card = A1.card + L.card := Finset.card_union_of_disjoint hdisj
          omega
        · refine hbox_of_color K L 1 ?_ ?_
          · exact Finset.union_subset (Finset.filter_subset _ _)
              (hLA0.trans (Finset.filter_subset _ _))
          · intro i hi
            rcases Finset.mem_union.1 hi with hi1 | hiL
            · have hnotL : i ∉ L := fun h => Finset.disjoint_left.1 hdisj hi1 h
              have hq : dotProduct (x i) (T.mulVec (x i)) = 1 := (Finset.mem_filter.1 hi1).2
              rw [hq]
              simp [b2z, hnotL, zmod2_add_self]
            · have hq : dotProduct (x i) (T.mulVec (x i)) = 0 := (Finset.mem_filter.1 (hLA0 hiL)).2
              rw [hq]
              simp [b2z, hiL]
      · obtain ⟨L, hLA1, hLcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right u A1.card)
        let K := A0 ∪ L
        have hdisj : Disjoint A0 L := Disjoint.mono_right hLA1 hdisj01
        refine ⟨π, K, L, Finset.subset_union_right, by omega, ?_, ?_⟩
        · have hKcard : K.card = A0.card + L.card := Finset.card_union_of_disjoint hdisj
          omega
        · refine hbox_of_color K L 0 ?_ ?_
          · exact Finset.union_subset (Finset.filter_subset _ _)
              (hLA1.trans (Finset.filter_subset _ _))
          · intro i hi
            rcases Finset.mem_union.1 hi with hi0 | hiL
            · have hnotL : i ∉ L := fun h => Finset.disjoint_left.1 hdisj hi0 h
              have hq : dotProduct (x i) (T.mulVec (x i)) = 0 := (Finset.mem_filter.1 hi0).2
              rw [hq]
              simp [b2z, hnotL]
            · have hq : dotProduct (x i) (T.mulVec (x i)) = 1 := (Finset.mem_filter.1 (hLA1 hiL)).2
              rw [hq]
              simp [b2z, hiL]

end PEqualNP.Outside.L_meta_25686_aux

theorem PEqualNP.Outside.L_meta_25686 : ∀ (n r u t : ℕ),
  let V := Fin r → ZMod 2
  let M := Matrix (Fin r) (Fin r) (ZMod 2)
  ∀ (x y : Fin n → V) (f g : Fin n → ZMod 2),
    let robust := fun (z : Fin n → V) => ∀ (a : V), a ≠ 0 → ∀ b : ZMod 2,
      t < ((Finset.univ : Finset (Fin n)).filter (fun label => dotProduct a (z label) ≠ b)).card
    robust x → robust y →
    let G := fun row col => decide (dotProduct (x row) (y col) + f row + g col = 1)
    (∃ (π : Equiv.Perm (Fin n)) (K L : Finset (Fin n)),
      L ⊆ K ∧ L.card ≤ u ∧ n ≤ K.card + t ∧ ∀ i ∈ K, ∀ j ∈ K,
        Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
          Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔
    ∃ (T : M) (b : V), T.transpose = T ∧ Function.Bijective T.mulVec ∧
      let mult := fun (bank : Fin n → V) (type : V) =>
        ((Finset.univ : Finset (Fin n)).filter (fun name => bank name = type)).card
      let cap := fun (s : ZMod 2) =>
        ∑ v ∈ (Finset.univ : Finset V).filter (fun w => dotProduct w (T.mulVec w) = s),
          min (mult x v) (mult y (T.mulVec v + b))
      n ≤ t + max (cap 0) (cap 1) + min u (min (cap 0) (cap 1)) := by
  intro n r u t V M x y f g robust hrobx hroby G
  exact PEqualNP.Outside.L_meta_25686_aux.main_aux n r u t x y f g hrobx hroby
