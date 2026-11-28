import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_997_aux

private lemma fin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  fin_cases c <;> simp

private lemma det_zero_of_row_eq_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) {r₀ r₁ : ι} (hne : r₀ ≠ r₁) (hneg : ∀ j, M r₀ j = -M r₁ j) :
    Matrix.det M = 0 := by
  have h1 : Matrix.det (M.updateRow r₀ (M r₀ + (1 : ℝ) • M r₁)) = Matrix.det M :=
    Matrix.det_updateRow_add_smul_self M hne 1
  rw [← h1]
  refine Matrix.det_eq_zero_of_row_eq_zero r₀ (fun j => ?_)
  simp [Matrix.updateRow_self, hneg j]

private lemma det_board_ne_zero_implies {blocks : ℕ} (π : Equiv.Perm (Fin blocks × Fin 2))
    (s : (Fin blocks × Fin 2) × (Fin blocks × Fin 2) → Bool)
    (hne : Matrix.det (fun i j => if s (i, j) then -(if i.1 = (π j).1 then (1 : ℝ) else 0)
      else (if i.1 = (π j).1 then (1 : ℝ) else 0) : Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ) ≠ 0) :
    ∀ b : Fin blocks,
      xor (s ((b, 0), π.symm (b, 0))) (s ((b, 1), π.symm (b, 0))) ≠
      xor (s ((b, 0), π.symm (b, 1))) (s ((b, 1), π.symm (b, 1))) := by
  intro b heq
  let M : Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ :=
    fun i j => if s (i, j) then -(if i.1 = (π j).1 then (1 : ℝ) else 0)
      else (if i.1 = (π j).1 then (1 : ℝ) else 0)
  have hne_row : ((b, 0) : Fin blocks × Fin 2) ≠ (b, 1) := fun h => (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd h)
  have hcol_cases : ∀ j : Fin blocks × Fin 2,
      (π j).1 = b → j = π.symm (b, 0) ∨ j = π.symm (b, 1) := by
    intro j hj
    have h2 : (π j).2 = 0 ∨ (π j).2 = 1 := fin2_cases (π j).2
    rcases h2 with h0 | h1
    · left; exact (Equiv.eq_symm_apply π).mpr (Prod.ext hj h0)
    · right; exact (Equiv.eq_symm_apply π).mpr (Prod.ext hj h1)
  cases h0 : xor (s ((b, 0), π.symm (b, 0))) (s ((b, 1), π.symm (b, 0)))
  · rw [h0] at heq
    have h1 := heq.symm
    have hsame0 : s ((b, 0), π.symm (b, 0)) = s ((b, 1), π.symm (b, 0)) := by
      revert h0; generalize s ((b, 0), π.symm (b, 0)) = x; generalize s ((b, 1), π.symm (b, 0)) = y
      cases x <;> cases y <;> decide
    have hsame1 : s ((b, 0), π.symm (b, 1)) = s ((b, 1), π.symm (b, 1)) := by
      revert h1; generalize s ((b, 0), π.symm (b, 1)) = x; generalize s ((b, 1), π.symm (b, 1)) = y
      cases x <;> cases y <;> decide
    have hrow : M (b, 0) = M (b, 1) := by
      funext j
      dsimp only [M]
      by_cases hbj : b = (π j).1
      · rcases hcol_cases j hbj.symm with rfl | rfl
        · rw [hsame0]
        · rw [hsame1]
      · simp only [hbj, ↓reduceIte, neg_zero, ite_self]
    exact hne (Matrix.det_zero_of_row_eq hne_row hrow)
  · rw [h0] at heq
    have h1 := heq.symm
    have hopp0 : s ((b, 0), π.symm (b, 0)) = !s ((b, 1), π.symm (b, 0)) := by
      revert h0; generalize s ((b, 0), π.symm (b, 0)) = x; generalize s ((b, 1), π.symm (b, 0)) = y
      cases x <;> cases y <;> decide
    have hopp1 : s ((b, 0), π.symm (b, 1)) = !s ((b, 1), π.symm (b, 1)) := by
      revert h1; generalize s ((b, 0), π.symm (b, 1)) = x; generalize s ((b, 1), π.symm (b, 1)) = y
      cases x <;> cases y <;> decide
    have hrow : ∀ j, M (b, 0) j = -M (b, 1) j := by
      intro j
      dsimp only [M]
      by_cases hbj : b = (π j).1
      · rcases hcol_cases j hbj.symm with rfl | rfl
        · rw [hopp0]
          cases s ((b, 1), π.symm (b, 0)) <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, neg_neg]
        · rw [hopp1]
          cases s ((b, 1), π.symm (b, 1)) <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, neg_neg]
      · simp only [hbj, ↓reduceIte, neg_zero, ite_self]
    exact hne (det_zero_of_row_eq_neg M hne_row hrow)

private lemma card_valid_equivs_le : ∀ (n : ℕ) {α : Type*} [Fintype α] [DecidableEq α]
    (_hcard : Fintype.card α = 2 * n) (χ : Fin n → α → Bool),
    ((Finset.univ : Finset ((Fin n × Fin 2) ≃ α)).filter
      (fun e => ∀ b : Fin n, χ b (e (b, 0)) ≠ χ b (e (b, 1)))).card ≤
    2 ^ n * (Nat.factorial n) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro α _ _ hcard χ
    have hle : ((Finset.univ : Finset ((Fin 0 × Fin 2) ≃ α)).filter
        (fun e => ∀ b : Fin 0, χ b (e (b, 0)) ≠ χ b (e (b, 1)))).card ≤
        (Finset.univ : Finset ((Fin 0 × Fin 2) ≃ α)).card := Finset.card_filter_le _ _
    have h1 : (Finset.univ : Finset ((Fin 0 × Fin 2) ≃ α)).card ≤ 1 := by
      rw [Finset.card_univ]
      exact Fintype.card_le_one_iff.mpr (fun e₁ e₂ => by ext ⟨b, _⟩; exact Fin.elim0 b)
    exact le_trans hle (by simpa using h1)
  | succ n ih =>
    intro α _ _ hcard χ
    let goodPairs : Finset (α × α) :=
      Finset.univ.filter (fun p => χ 0 p.1 ≠ χ 0 p.2)
    have hgood_card : goodPairs.card ≤ 2 * (n + 1) ^ 2 := by
      let A := Finset.univ.filter (fun x : α => χ 0 x = false)
      let B := Finset.univ.filter (fun x : α => χ 0 x = true)
      have hAB_sum : A.card + B.card = 2 * (n + 1) := by
        have h1 : B = Finset.univ.filter (fun x : α => ¬ (χ 0 x = false)) := by
          ext x; simp [B]
        rw [h1, Finset.card_filter_add_card_filter_not, Finset.card_univ, hcard]
      have hgp_eq : goodPairs = (A ×ˢ B) ∪ (B ×ˢ A) := by
        ext ⟨x, y⟩
        simp only [goodPairs, A, B, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_product]
        cases χ 0 x <;> cases χ 0 y <;> simp
      have hgp_le : goodPairs.card ≤ 2 * (A.card * B.card) := by
        rw [hgp_eq]
        calc ((A ×ˢ B) ∪ (B ×ˢ A)).card ≤ (A ×ˢ B).card + (B ×ˢ A).card := Finset.card_union_le _ _
          _ = A.card * B.card + B.card * A.card := by simp [Finset.card_product]
          _ = 2 * (A.card * B.card) := by ring
      have hamgm : A.card * B.card ≤ (n + 1) ^ 2 := by
        have hZ : (A.card : ℤ) * (B.card : ℤ) ≤ ((n + 1 : ℕ) : ℤ) ^ 2 := by
          have hsumZ : (A.card : ℤ) + (B.card : ℤ) = 2 * ((n + 1 : ℕ) : ℤ) := by
            exact_mod_cast hAB_sum
          nlinarith [sq_nonneg ((A.card : ℤ) - (B.card : ℤ))]
        exact_mod_cast hZ
      nlinarith
    let S : Finset ((Fin (n + 1) × Fin 2) ≃ α) :=
      Finset.univ.filter (fun e => ∀ b : Fin (n + 1), χ b (e (b, 0)) ≠ χ b (e (b, 1)))
    let fib : α × α → Finset ((Fin (n + 1) × Fin 2) ≃ α) := fun p =>
      S.filter (fun e => e (0, 0) = p.1 ∧ e (0, 1) = p.2)
    have hcov : S ⊆ goodPairs.biUnion fib := by
      intro e he
      have hok := (Finset.mem_filter.mp he).2
      refine Finset.mem_biUnion.mpr ⟨(e (0, 0), e (0, 1)), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hok 0⟩
      · exact Finset.mem_filter.mpr ⟨he, rfl, rfl⟩
    have hfib_le : ∀ p ∈ goodPairs, (fib p).card ≤ 2 ^ n * (Nat.factorial n) ^ 2 := by
      intro p hp
      have hpne : p.1 ≠ p.2 := by
        have hchi := (Finset.mem_filter.mp hp).2
        intro heq; rw [heq] at hchi; exact hchi rfl
      let α' := {x : α // x ≠ p.1 ∧ x ≠ p.2}
      have hcard' : Fintype.card α' = 2 * n := by
        have h1 : Fintype.card α' = (Finset.univ.filter (fun x : α => x ≠ p.1 ∧ x ≠ p.2)).card :=
          Fintype.card_subtype _
        have h2 : Finset.univ.filter (fun x : α => x ≠ p.1 ∧ x ≠ p.2) =
            (Finset.univ : Finset α) \ {p.1, p.2} := by
          ext x; simp [not_or]
        rw [h1, h2, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard,
          Finset.card_pair hpne]
        omega
      let χ' : Fin n → α' → Bool := fun b x => χ b.succ x.1
      let S' : Finset ((Fin n × Fin 2) ≃ α') :=
        Finset.univ.filter (fun e => ∀ b : Fin n, χ' b (e (b, 0)) ≠ χ' b (e (b, 1)))
      have hle_ih : S'.card ≤ 2 ^ n * (Nat.factorial n) ^ 2 := ih hcard' χ'
      refine le_trans ?_ hle_ih
      have hinj : ∀ e ∈ fib p, ∃ e' ∈ S', ∀ (b : Fin n) (c : Fin 2), (e' (b, c)).1 = e (b.succ, c) := by
        intro e he
        rcases Finset.mem_filter.mp he with ⟨heS, he0, he1⟩
        have hok := (Finset.mem_filter.mp heS).2
        have hmem_α' : ∀ (b : Fin n) (c : Fin 2), e (b.succ, c) ≠ p.1 ∧ e (b.succ, c) ≠ p.2 := by
          intro b c
          constructor
          · rw [← he0]; intro h; have := congrArg Prod.fst (e.injective h); exact Fin.succ_ne_zero b this
          · rw [← he1]; intro h; have := congrArg Prod.fst (e.injective h); exact Fin.succ_ne_zero b this
        have hpre : ∀ x : α', (e.symm x.1).1 ≠ 0 := by
          intro x h0
          have h2 : (e.symm x.1).2 = 0 ∨ (e.symm x.1).2 = 1 := fin2_cases (e.symm x.1).2
          rcases h2 with hc | hc
          · have hpair : e.symm x.1 = (0, 0) := Prod.ext h0 hc
            have hx : x.1 = p.1 := by
              have h3 := congrArg e hpair
              rw [e.apply_symm_apply, he0] at h3
              exact h3
            exact x.2.1 hx
          · have hpair : e.symm x.1 = (0, 1) := Prod.ext h0 hc
            have hx : x.1 = p.2 := by
              have h3 := congrArg e hpair
              rw [e.apply_symm_apply, he1] at h3
              exact h3
            exact x.2.2 hx
        let e' : (Fin n × Fin 2) ≃ α' :=
          { toFun := fun bc => ⟨e (bc.1.succ, bc.2), hmem_α' bc.1 bc.2⟩
            invFun := fun x => ((e.symm x.1).1.pred (hpre x), (e.symm x.1).2)
            left_inv := fun ⟨b, c⟩ => by
              simp only [Equiv.symm_apply_apply, Fin.pred_succ]
            right_inv := fun x => by
              apply Subtype.ext
              dsimp only
              have : ((e.symm x.1).1.pred (hpre x)).succ = (e.symm x.1).1 := Fin.succ_pred _ _
              rw [this, Prod.mk.eta, e.apply_symm_apply] }
        refine ⟨e', Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => hok b.succ⟩, fun _ _ => rfl⟩
      classical
      let mapF : ((Fin (n + 1) × Fin 2) ≃ α) → ((Fin n × Fin 2) ≃ α') := fun e =>
        if he : e ∈ fib p then Classical.choose (hinj e he) else
          Fintype.equivOfCardEq (by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hcard']; ring)
      have hmap_sub : (fib p).image mapF ⊆ S' := by
        intro e' he'
        rcases Finset.mem_image.mp he' with ⟨e, he, rfl⟩
        simp only [mapF, he, ↓reduceDIte]
        exact (Classical.choose_spec (hinj e he)).1
      have hmap_inj : Set.InjOn mapF ↑(fib p) := by
        intro e₁ h1 e₂ h2 heq
        have hm1 : mapF e₁ = Classical.choose (hinj e₁ h1) := dif_pos h1
        have hm2 : mapF e₂ = Classical.choose (hinj e₂ h2) := dif_pos h2
        rw [hm1, hm2] at heq
        have hs1 := (Classical.choose_spec (hinj e₁ h1)).2
        have hs2 := (Classical.choose_spec (hinj e₂ h2)).2
        rcases Finset.mem_filter.mp h1 with ⟨_, h10, h11⟩
        rcases Finset.mem_filter.mp h2 with ⟨_, h20, h21⟩
        ext ⟨b, c⟩
        refine Fin.cases ?_ (fun b' => ?_) b
        · fin_cases c
          · exact h10.trans h20.symm
          · exact h11.trans h21.symm
        · rw [← hs1 b' c, ← hs2 b' c, heq]
      rw [← Finset.card_image_of_injOn hmap_inj]
      exact Finset.card_le_card hmap_sub
    calc S.card ≤ (goodPairs.biUnion fib).card := Finset.card_le_card hcov
      _ ≤ ∑ p ∈ goodPairs, (fib p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ goodPairs, (2 ^ n * (Nat.factorial n) ^ 2) := Finset.sum_le_sum hfib_le
      _ = goodPairs.card * (2 ^ n * (Nat.factorial n) ^ 2) := by simp
      _ ≤ (2 * (n + 1) ^ 2) * (2 ^ n * (Nat.factorial n) ^ 2) :=
          Nat.mul_le_mul_right _ hgood_card
      _ = 2 ^ (n + 1) * (Nat.factorial (n + 1)) ^ 2 := by
          rw [Nat.factorial_succ, pow_succ]
          ring

private lemma card_valid_perms_le (blocks : ℕ)
    (s : (Fin blocks × Fin 2) × (Fin blocks × Fin 2) → Bool) :
    ((Finset.univ : Finset (Equiv.Perm (Fin blocks × Fin 2))).filter
      (fun π => Matrix.det (fun i j =>
        if s (i, j) then -(if i.1 = (π j).1 then (1 : ℝ) else 0)
        else (if i.1 = (π j).1 then (1 : ℝ) else 0) :
          Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ) ≠ 0)).card ≤
    2 ^ blocks * (Nat.factorial blocks) ^ 2 := by
  let χ : Fin blocks → (Fin blocks × Fin 2) → Bool := fun b j => xor (s ((b, 0), j)) (s ((b, 1), j))
  have hcard : Fintype.card (Fin blocks × Fin 2) = 2 * blocks := by
    simp [Fintype.card_prod, Fintype.card_fin]; ring
  have hbound := card_valid_equivs_le blocks hcard χ
  let S_perm := (Finset.univ : Finset (Equiv.Perm (Fin blocks × Fin 2))).filter
    (fun π => Matrix.det (fun i j =>
      if s (i, j) then -(if i.1 = (π j).1 then (1 : ℝ) else 0)
      else (if i.1 = (π j).1 then (1 : ℝ) else 0) :
        Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ) ≠ 0)
  let S_eq := (Finset.univ : Finset ((Fin blocks × Fin 2) ≃ (Fin blocks × Fin 2))).filter
    (fun e => ∀ b : Fin blocks, χ b (e (b, 0)) ≠ χ b (e (b, 1)))
  have hsub : S_perm.image Equiv.symm ⊆ S_eq := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨π, hπ, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, det_board_ne_zero_implies π s (Finset.mem_filter.mp hπ).2⟩
  have hinj : Function.Injective (Equiv.symm : Equiv.Perm (Fin blocks × Fin 2) → Equiv.Perm (Fin blocks × Fin 2)) :=
    Equiv.symm_bijective.injective
  have hcard_eq : S_perm.card = (S_perm.image Equiv.symm).card :=
    (Finset.card_image_of_injective _ hinj).symm
  rw [hcard_eq]
  exact le_trans (Finset.card_le_card hsub) hbound

private lemma run_eq_of_zeros {blocks : ℕ} (t : ℕ)
    (D : Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ →
      ((Fin blocks × Fin 2) × (Fin blocks × Fin 2) → Bool) → ℝ)
    (hD0 : ∀ s, D 0 s = 0)
    (q : ℕ → List ℝ → ((Fin blocks × Fin 2) × (Fin blocks × Fin 2) → Bool))
    (mat : Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ)
    (hzero : ∀ j < t, D mat (q j (List.replicate j (0 : ℝ))) = 0) :
    (List.range t).foldl (fun h j => D mat (q j h) :: h) ([] : List ℝ) =
    (List.range t).foldl (fun h j => D 0 (q j h) :: h) ([] : List ℝ) ∧
    (List.range t).foldl (fun h j => D 0 (q j h) :: h) ([] : List ℝ) = List.replicate t (0 : ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ih' := ih (fun j hj => hzero j (Nat.lt_succ_of_lt hj))
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih'.1, ih'.2, hD0, hzero t (Nat.lt_succ_self t)]
    exact ⟨rfl, rfl⟩

private lemma bernoulli_nat (C d t : ℕ) (hd : d ≤ C) :
    (C - d) ^ t * (C + t * d) ≤ C ^ (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : (C - d) * (C + (t + 1) * d) ≤ C * (C + t * d) := by
      have h1 : (C - d) + d = C := Nat.sub_add_cancel hd
      have h2 : (C - d) * (C + (t + 1) * d) + (t + 1) * d * d = C * (C + t * d) := by
        calc (C - d) * (C + (t + 1) * d) + (t + 1) * d * d
            = (C - d) * (C + t * d) + ((C - d) + d) * d + t * d * d := by ring
          _ = (C - d) * (C + t * d) + C * d + t * d * d := by rw [h1]
          _ = ((C - d) + d) * (C + t * d) := by ring
          _ = C * (C + t * d) := by rw [h1]
      omega
    calc (C - d) ^ (t + 1) * (C + (t + 1) * d)
        = (C - d) ^ t * ((C - d) * (C + (t + 1) * d)) := by rw [pow_succ]; ring
      _ ≤ (C - d) ^ t * (C * (C + t * d)) := Nat.mul_le_mul_left _ hstep
      _ = C * ((C - d) ^ t * (C + t * d)) := by ring
      _ ≤ C * C ^ (t + 1) := Nat.mul_le_mul_left C ih
      _ = C ^ (t + 2) := by rw [pow_succ]; ring

private lemma abs_det_eq_permanent_of_transverse {blocks : ℕ}
    (π : Equiv.Perm (Fin blocks × Fin 2))
    (mat : Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ)
    (hnn : ∀ i j, 0 ≤ mat i j)
    (hsupp : ∀ i j, i.1 ≠ (π j).1 → mat i j = 0)
    (U : Finset (Fin blocks × Fin 2))
    (htrans : ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)) :
    |Matrix.det (fun i j =>
      if decide (i.2.val = 1 ∧ j ∈ U) then -mat i j else mat i j :
        Matrix (Fin blocks × Fin 2) (Fin blocks × Fin 2) ℝ)| = mat.permanent := by
  let I := Fin blocks × Fin 2
  let M : Matrix I I ℝ := fun i j => if decide (i.2.val = 1 ∧ j ∈ U) then -mat i j else mat i j
  let ε : Fin blocks → ℝ := fun b => if π.symm (b, 1) ∈ U then -1 else 1
  let c0 : ℝ := (Equiv.Perm.sign π.symm : ℝ) * ∏ b : Fin blocks, ε b
  have hc0_abs : |c0| = 1 := by
    dsimp only [c0]
    rw [abs_mul, Finset.abs_prod]
    have hs : |(Equiv.Perm.sign π.symm : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with h | h <;> simp [h]
    have hp : (∏ b : Fin blocks, |ε b|) = 1 := by
      refine Finset.prod_eq_one (fun b _ => ?_)
      dsimp only [ε]; split_ifs <;> norm_num
    rw [hs, hp, mul_one]
  have hterm : ∀ σ : Equiv.Perm I,
      (Equiv.Perm.sign σ : ℝ) * ∏ i : I, M (σ i) i = c0 * ∏ i : I, mat (σ i) i := by
    intro σ
    by_cases hpres : ∀ i : I, (σ i).1 = (π i).1
    · let τ : Equiv.Perm I := π.symm.trans σ
      have hτ_fst : ∀ x : I, (τ x).1 = x.1 := by
        intro x
        dsimp only [τ, Equiv.trans_apply]
        have h2 := hpres (π.symm x)
        rw [π.apply_symm_apply] at h2
        exact h2
      have hτ_eq : ∀ b : Fin blocks,
          (τ (b, 0) = (b, 0) ∧ τ (b, 1) = (b, 1)) ∨ (τ (b, 0) = (b, 1) ∧ τ (b, 1) = (b, 0)) := by
        intro b
        have h0 := hτ_fst (b, 0)
        have h1 := hτ_fst (b, 1)
        have hne : τ (b, 0) ≠ τ (b, 1) := fun h =>
          (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd (τ.injective h))
        have hc0 : (τ (b, 0)).2 = 0 ∨ (τ (b, 0)).2 = 1 := fin2_cases (τ (b, 0)).2
        have hc1 : (τ (b, 1)).2 = 0 ∨ (τ (b, 1)).2 = 1 := fin2_cases (τ (b, 1)).2
        rcases hc0 with h00 | h01 <;> rcases hc1 with h10 | h11
        · exfalso; exact hne (Prod.ext (h0.trans h1.symm) (h00.trans h10.symm))
        · left; exact ⟨Prod.ext h0 h00, Prod.ext h1 h11⟩
        · right; exact ⟨Prod.ext h0 h01, Prod.ext h1 h10⟩
        · exfalso; exact hne (Prod.ext (h0.trans h1.symm) (h01.trans h11.symm))
      have hσ_eq : σ = π.trans τ := by
        apply Equiv.ext; intro x; simp [τ]
      have hτ_sign : (Equiv.Perm.sign τ : ℝ) =
          ∏ b : Fin blocks, if (τ (b, 0)).2 = 1 then (-1 : ℝ) else 1 := by
        have hτ_prod : τ = (Finset.univ.filter (fun b : Fin blocks => (τ (b, 0)).2 = 1)).toList.foldr
            (fun b acc => acc.trans (Equiv.swap (b, 0) (b, 1))) (1 : Equiv.Perm I) := by
          have hfold : ∀ (L : List (Fin blocks)), L.Nodup →
              ∀ x : I, (L.foldr (fun b acc => acc.trans (Equiv.swap (b, 0) (b, 1))) (1 : Equiv.Perm I)) x =
                if x.1 ∈ L then (x.1, if x.2 = 0 then 1 else 0) else x := by
            intro L hnd
            induction L with
            | nil => intro x; simp
            | cons a L ih =>
              rw [List.nodup_cons] at hnd
              intro x
              simp only [List.foldr_cons, Equiv.trans_apply, List.mem_cons]
              rw [ih hnd.2]
              by_cases hxa : x.1 = a
              · rcases x with ⟨a', c⟩
                dsimp only at hxa ⊢
                subst hxa
                simp only [hnd.1, ↓reduceIte, true_or]
                fin_cases c <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
              · have hne0 : (x.1, if x.2 = 0 then (1 : Fin 2) else 0) ≠ (a, 0) :=
                  fun h => hxa (congrArg Prod.fst h)
                have hne1 : (x.1, if x.2 = 0 then (1 : Fin 2) else 0) ≠ (a, 1) :=
                  fun h => hxa (congrArg Prod.fst h)
                have hne0' : x ≠ (a, 0) := fun h => hxa (congrArg Prod.fst h)
                have hne1' : x ≠ (a, 1) := fun h => hxa (congrArg Prod.fst h)
                by_cases hxL : x.1 ∈ L
                · simp only [hxL, ↓reduceIte, hxa, false_or]
                  rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
                · simp only [hxL, ↓reduceIte, hxa, false_or]
                  rw [Equiv.swap_apply_of_ne_of_ne hne0' hne1']
          apply Equiv.ext
          intro x
          rw [hfold _ (Finset.nodup_toList _)]
          simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases x with ⟨b, c⟩
          rcases hτ_eq b with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · have hf : (τ (b, 0)).2 ≠ 1 := by rw [h0]; exact (by decide : (0 : Fin 2) ≠ 1)
            simp only [hf, ↓reduceIte]
            fin_cases c
            · exact h0
            · exact h1
          · have ht : (τ (b, 0)).2 = 1 := by rw [h0]
            simp only [ht, ↓reduceIte]
            fin_cases c
            · exact h0
            · exact h1
        have hsign_fold : ∀ (L : List (Fin blocks)),
            (Equiv.Perm.sign (L.foldr (fun b acc => acc.trans (Equiv.swap (b, 0) (b, 1)))
              (1 : Equiv.Perm I)) : ℝ) =
            (L.map (fun _ => (-1 : ℝ))).prod := by
          intro L
          induction L with
          | nil => simp
          | cons a L ih =>
            simp only [List.foldr_cons, List.map_cons, List.prod_cons, Equiv.Perm.sign_trans,
              Units.val_mul, Int.cast_mul]
            have hne_a : ((a, 0) : I) ≠ (a, 1) := fun h => (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd h)
            rw [Equiv.Perm.sign_swap hne_a, ih]
            simp [mul_comm]
        conv_lhs => rw [hτ_prod, hsign_fold]
        have hmap : ((Finset.univ.filter (fun b : Fin blocks => (τ (b, 0)).2 = 1)).toList.map
            (fun _ => (-1 : ℝ))).prod =
            ∏ b ∈ Finset.univ.filter (fun b : Fin blocks => (τ (b, 0)).2 = 1), (-1 : ℝ) := by
          simp only [List.map_const', List.prod_replicate, Finset.length_toList, Finset.prod_const]
        rw [hmap, Finset.prod_filter]
      have hsign_σ : (Equiv.Perm.sign σ : ℝ) = (Equiv.Perm.sign π.symm : ℝ) * (Equiv.Perm.sign τ : ℝ) := by
        have hinv : Equiv.Perm.sign π.symm = Equiv.Perm.sign π := Equiv.Perm.sign_inv π
        rw [hσ_eq, Equiv.Perm.sign_trans, hinv]
        push_cast; ring
      have hM_prod : (∏ i : I, M (σ i) i) =
          (∏ i : I, (if decide ((σ i).2.val = 1 ∧ i ∈ U) then (-1 : ℝ) else 1)) *
          (∏ i : I, mat (σ i) i) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        dsimp only [M]
        split_ifs <;> ring
      have hsign_M : (∏ i : I, (if decide ((σ i).2.val = 1 ∧ i ∈ U) then (-1 : ℝ) else 1)) =
          ∏ b : Fin blocks, (if (τ (b, 0)).2 = 1 then (-1 : ℝ) else 1) * ε b := by
        rw [← Equiv.prod_comp π.symm]
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl (fun b _ => ?_)
        rw [Fin.prod_univ_two]
        have hσ0 : σ (π.symm (b, 0)) = τ (b, 0) := by simp [τ]
        have hσ1 : σ (π.symm (b, 1)) = τ (b, 1) := by simp [τ]
        rw [hσ0, hσ1]
        have htr := htrans b
        rcases hτ_eq b with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · rw [h0, h1]
          dsimp only [ε]
          by_cases hU1 : π.symm (b, 1) ∈ U <;> simp [hU1]
        · rw [h0, h1]
          dsimp only [ε]
          by_cases hU0 : π.symm (b, 0) ∈ U <;> by_cases hU1 : π.symm (b, 1) ∈ U <;>
            simp_all
      rw [hM_prod, ← mul_assoc, hsign_σ, hτ_sign, hsign_M]
      congr 1
      dsimp only [c0]
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl (fun b _ => ?_)
      split_ifs <;> ring
    · push Not at hpres
      rcases hpres with ⟨i₀, hi₀⟩
      have hmat0 : mat (σ i₀) i₀ = 0 := hsupp (σ i₀) i₀ hi₀
      have hM0 : M (σ i₀) i₀ = 0 := by dsimp only [M]; rw [hmat0]; simp
      have hp1 : ∏ i : I, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) hM0
      have hp2 : ∏ i : I, mat (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) hmat0
      rw [hp1, hp2, mul_zero, mul_zero]
  have hdet_eq : Matrix.det M = c0 * mat.permanent := by
    rw [Matrix.det_apply, Matrix.permanent]
    simp_rw [Units.smul_def, zsmul_eq_mul]
    have h1 : (∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ : ℝ) * ∏ i : I, M (σ i) i) =
        ∑ σ : Equiv.Perm I, c0 * ∏ i : I, mat (σ i) i :=
      Finset.sum_congr rfl (fun σ _ => hterm σ)
    rw [h1, ← Finset.mul_sum]
  have hperm_nn : 0 ≤ mat.permanent := by
    rw [Matrix.permanent]
    exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => hnn (σ i) i))
  rw [hdet_eq, abs_mul, hc0_abs, one_mul, abs_of_nonneg hperm_nn]

private lemma card_transverse_subsets (blocks : ℕ) (π : Equiv.Perm (Fin blocks × Fin 2)) :
    ((Finset.univ.powersetCard blocks : Finset (Finset (Fin blocks × Fin 2))).filter
      (fun U => ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U))).card =
    2 ^ blocks := by
  let I := Fin blocks × Fin 2
  let f : (Fin blocks → Fin 2) → Finset I := fun c =>
    (Finset.univ : Finset (Fin blocks)).image (fun b => π.symm (b, c b))
  have hf_mem : ∀ c : Fin blocks → Fin 2,
      f c ∈ (Finset.univ.powersetCard blocks : Finset (Finset I)).filter
        (fun U => ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)) := by
    intro c
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · dsimp only [f]
      rw [Finset.card_image_of_injective _ (fun b₁ b₂ h =>
        congrArg Prod.fst (π.symm.injective h))]
      simp
    · intro b
      have h0 : π.symm (b, 0) ∈ f c ↔ c b = 0 := by
        simp only [f, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨b', hb'⟩
          have hpair := π.symm.injective hb'
          rcases Prod.mk.inj hpair with ⟨rfl, hc⟩
          exact hc
        · intro hc; exact ⟨b, by rw [hc]⟩
      have h1 : π.symm (b, 1) ∈ f c ↔ c b = 1 := by
        simp only [f, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨b', hb'⟩
          have hpair := π.symm.injective hb'
          rcases Prod.mk.inj hpair with ⟨rfl, hc⟩
          exact hc
        · intro hc; exact ⟨b, by rw [hc]⟩
      rcases fin2_cases (c b) with hc | hc
      · simp [h0, h1, hc]
      · simp [h0, h1, hc]
  have hf_inj : Function.Injective f := by
    intro c₁ c₂ heq
    funext b
    have hmem : π.symm (b, c₁ b) ∈ f c₂ := by
      rw [← heq]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
    rcases Finset.mem_image.mp hmem with ⟨b', _, hb'⟩
    have hpair := π.symm.injective hb'
    rcases Prod.mk.inj hpair with ⟨rfl, hc⟩
    exact hc.symm
  have hf_surj : ∀ U ∈ (Finset.univ.powersetCard blocks : Finset (Finset I)).filter
      (fun U => ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)),
      ∃ c : Fin blocks → Fin 2, f c = U := by
    intro U hU
    rcases Finset.mem_filter.mp hU with ⟨hUp, htr⟩
    refine ⟨fun b => if π.symm (b, 0) ∈ U then 0 else 1, ?_⟩
    ext x
    simp only [f, Finset.mem_image, Finset.mem_univ, true_and]
    have htr' := htr (π x).1
    constructor
    · rintro ⟨b, rfl⟩
      split_ifs with h0
      · exact h0
      · have htb := htr b
        by_contra h1
        simp [h0, h1] at htb
    · intro hxU
      refine ⟨(π x).1, ?_⟩
      have hx2 : (π x).2 = 0 ∨ (π x).2 = 1 := fin2_cases (π x).2
      rcases hx2 with h0 | h1
      · have hx_eq : x = π.symm ((π x).1, 0) := (Equiv.eq_symm_apply π).mpr (Prod.ext rfl h0)
        rw [hx_eq] at hxU
        rw [if_pos hxU]
        exact hx_eq.symm
      · have hx_eq : x = π.symm ((π x).1, 1) := (Equiv.eq_symm_apply π).mpr (Prod.ext rfl h1)
        rw [hx_eq] at hxU
        have hnot0 : π.symm ((π x).1, 0) ∉ U := by
          intro h0
          simp [h0, hxU] at htr'
        rw [if_neg hnot0]
        exact hx_eq.symm
  have heq : (Finset.univ : Finset (Fin blocks → Fin 2)).image f =
      (Finset.univ.powersetCard blocks : Finset (Finset I)).filter
        (fun U => ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)) := by
    ext U
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, rfl⟩; exact hf_mem c
    · exact hf_surj U
  rw [← heq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_pi]
  simp [Fintype.card_fin]

private lemma main_proof (blocks : ℕ) (hb : 0 < blocks) :
    let I := Fin blocks × Fin 2
    let S := I × I → Bool
    let D := fun (mat : Matrix I I ℝ) (s : S) =>
      Matrix.det (fun i j => if s (i, j) then -mat i j else mat i j : Matrix I I ℝ)
    let board := fun (π : Equiv.Perm I) (i j : I) => if i.1 = (π j).1 then (1 : ℝ) else 0
    let C := Nat.choose (2 * blocks) blocks
    (∀ (R t : ℕ), 0 < R →
      ∀ (query : Fin R → ℕ → List ℝ → S) (accept : Fin R → List ℝ → Bool),
      let run := fun (mat : Matrix I I ℝ) (u : Fin R) =>
        (List.range t).foldl (fun h j => D mat (query u j h) :: h) ([] : List ℝ)
      let yes := fun mat : Matrix I I ℝ =>
        ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run mat u))).card
      3 * yes 0 ≤ R → (∀ π : Equiv.Perm I, 2 * R ≤ 3 * yes (board π)) →
        C ≤ 3 * t * 2 ^ blocks) ∧
    (∃ (R t : ℕ) (U : Fin R → Fin t → Finset I), 0 < R ∧ 0 < t ∧
      (∀ u h, (U u h).card = blocks) ∧ t * 2 ^ blocks ≤ 2 * C + 2 ^ blocks ∧
      ∀ (π : Equiv.Perm I) (mat : Matrix I I ℝ), (∀ i j, 0 ≤ mat i j) →
        (∀ i j, i.1 ≠ (π j).1 → mat i j = 0) →
        2 * R ≤ 3 * ((Finset.univ : Finset (Fin R)).filter (fun u => ∃ h : Fin t,
          |D mat (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U u h))| = mat.permanent)).card) := by
  classical
  dsimp only
  let I := Fin blocks × Fin 2
  let S := I × I → Bool
  let D : Matrix I I ℝ → S → ℝ := fun mat s =>
    Matrix.det (fun i j => if s (i, j) then -mat i j else mat i j : Matrix I I ℝ)
  let board : Equiv.Perm I → Matrix I I ℝ := fun π i j => if i.1 = (π j).1 then (1 : ℝ) else 0
  let C := Nat.choose (2 * blocks) blocks
  constructor
  · intro R t hR query accept h0 hall
    let run : Matrix I I ℝ → Fin R → List ℝ := fun mat u =>
      (List.range t).foldl (fun h j => D mat (query u j h) :: h) ([] : List ℝ)
    let yes : Matrix I I ℝ → ℕ := fun mat =>
      ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run mat u))).card
    have hD0 : ∀ s : S, D 0 s = 0 := by
      intro s
      have hzero_mat : (fun i j : I => if s (i, j) then -(0 : Matrix I I ℝ) i j else (0 : Matrix I I ℝ) i j) =
          (0 : Matrix I I ℝ) := by ext i j; simp
      dsimp only [D]
      rw [hzero_mat]
      exact Matrix.det_eq_zero_of_row_eq_zero (⟨0, hb⟩, 0) (fun _ => rfl)
    let goodPairs : Finset (Fin R × Equiv.Perm I) :=
      Finset.univ.filter (fun p => accept p.1 (run (board p.2) p.1) = true ∧ accept p.1 (run 0 p.1) = false)
    have hlo : R * Nat.factorial (2 * blocks) ≤ 3 * goodPairs.card := by
      have hcard_perm : (Finset.univ : Finset (Equiv.Perm I)).card = Nat.factorial (2 * blocks) := by
        rw [Finset.card_univ, Fintype.card_perm, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
        congr 1; ring
      have hper_π : ∀ π : Equiv.Perm I,
          R ≤ 3 * (Finset.univ.filter (fun u : Fin R =>
            accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card := by
        intro π
        have hπ : 2 * R ≤ 3 * yes (board π) := hall π
        have h0' : 3 * yes 0 ≤ R := h0
        have hdiff : yes (board π) ≤ yes 0 +
            (Finset.univ.filter (fun u : Fin R =>
              accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card := by
          have hsub : Finset.univ.filter (fun u : Fin R => accept u (run (board π) u) = true) ⊆
              Finset.univ.filter (fun u : Fin R => accept u (run 0 u) = true) ∪
              Finset.univ.filter (fun u : Fin R =>
                accept u (run (board π) u) = true ∧ accept u (run 0 u) = false) := by
            intro u hu
            have h1 := (Finset.mem_filter.mp hu).2
            cases h2 : accept u (run 0 u)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
          exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
        omega
      have hsum : ∑ π : Equiv.Perm I,
          (Finset.univ.filter (fun u : Fin R =>
            accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card = goodPairs.card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_sigma.mp hp with ⟨_, hu⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
        · intro p₁ _ p₂ _ h
          rcases Prod.mk.inj h with ⟨h2, h1⟩
          exact Sigma.ext h1 (heq_of_eq h2)
        · intro p hp
          exact ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩⟩, rfl⟩
      calc R * Nat.factorial (2 * blocks)
          = ∑ _π : Equiv.Perm I, R := by rw [Finset.sum_const, hcard_perm, smul_eq_mul, mul_comm]
        _ ≤ ∑ π : Equiv.Perm I, 3 * (Finset.univ.filter (fun u : Fin R =>
              accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card :=
            Finset.sum_le_sum (fun π _ => hper_π π)
        _ = 3 * ∑ π : Equiv.Perm I, (Finset.univ.filter (fun u : Fin R =>
              accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card :=
            (Finset.mul_sum _ _ _).symm
        _ = 3 * goodPairs.card := by rw [hsum]
    have hhi : goodPairs.card ≤ R * (t * (2 ^ blocks * (Nat.factorial blocks) ^ 2)) := by
      have hper_u : ∀ u : Fin R,
          (Finset.univ.filter (fun π : Equiv.Perm I =>
            accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card ≤
          t * (2 ^ blocks * (Nat.factorial blocks) ^ 2) := by
        intro u
        let s_u : Fin t → S := fun j => query u j.val (List.replicate j.val (0 : ℝ))
        have hcov : Finset.univ.filter (fun π : Equiv.Perm I =>
            accept u (run (board π) u) = true ∧ accept u (run 0 u) = false) ⊆
            Finset.univ.biUnion (fun j : Fin t =>
              Finset.univ.filter (fun π : Equiv.Perm I => D (board π) (s_u j) ≠ 0)) := by
          intro π hπ
          rcases (Finset.mem_filter.mp hπ).2 with ⟨hT, hF⟩
          by_contra hnone
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
            not_exists, not_not] at hnone
          have hrun_eq := (run_eq_of_zeros t D hD0 (query u) (board π)
            (fun j hj => hnone ⟨j, hj⟩)).1
          change run (board π) u = run 0 u at hrun_eq
          rw [hrun_eq, hF] at hT
          exact Bool.false_ne_true hT
        calc (Finset.univ.filter (fun π : Equiv.Perm I =>
                accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card
            ≤ (Finset.univ.biUnion (fun j : Fin t =>
                Finset.univ.filter (fun π : Equiv.Perm I => D (board π) (s_u j) ≠ 0))).card :=
              Finset.card_le_card hcov
          _ ≤ ∑ j : Fin t, (Finset.univ.filter (fun π : Equiv.Perm I => D (board π) (s_u j) ≠ 0)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _j : Fin t, (2 ^ blocks * (Nat.factorial blocks) ^ 2) :=
              Finset.sum_le_sum (fun j _ => card_valid_perms_le blocks (s_u j))
          _ = t * (2 ^ blocks * (Nat.factorial blocks) ^ 2) := by simp
      have hsum : ∑ u : Fin R,
          (Finset.univ.filter (fun π : Equiv.Perm I =>
            accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card = goodPairs.card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun p _ => (p.1, p.2)) ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_sigma.mp hp with ⟨_, hπ⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hπ).2⟩
        · intro p₁ _ p₂ _ h
          rcases Prod.mk.inj h with ⟨h1, h2⟩
          exact Sigma.ext h1 (heq_of_eq h2)
        · intro p hp
          exact ⟨⟨p.1, p.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩⟩, rfl⟩
      rw [← hsum]
      calc ∑ u : Fin R, (Finset.univ.filter (fun π : Equiv.Perm I =>
              accept u (run (board π) u) = true ∧ accept u (run 0 u) = false)).card
          ≤ ∑ _u : Fin R, (t * (2 ^ blocks * (Nat.factorial blocks) ^ 2)) :=
            Finset.sum_le_sum (fun u _ => hper_u u)
        _ = R * (t * (2 ^ blocks * (Nat.factorial blocks) ^ 2)) := by simp
    have hcomb : R * Nat.factorial (2 * blocks) ≤ R * (3 * t * 2 ^ blocks * (Nat.factorial blocks) ^ 2) := by
      have := Nat.mul_le_mul_left 3 hhi
      have h1 : 3 * (R * (t * (2 ^ blocks * (Nat.factorial blocks) ^ 2))) =
          R * (3 * t * 2 ^ blocks * (Nat.factorial blocks) ^ 2) := by ring
      omega
    have hfac : Nat.factorial (2 * blocks) ≤ 3 * t * 2 ^ blocks * (Nat.factorial blocks) ^ 2 :=
      Nat.le_of_mul_le_mul_left hcomb hR
    have hchoose : C * (Nat.factorial blocks) ^ 2 = Nat.factorial (2 * blocks) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : blocks ≤ 2 * blocks)
      have h2 : 2 * blocks - blocks = blocks := by omega
      rw [h2] at h1
      dsimp only [C]
      nlinarith
    rw [← hchoose] at hfac
    have hfac_pos : 0 < (Nat.factorial blocks) ^ 2 := by positivity
    exact Nat.le_of_mul_le_mul_right hfac hfac_pos
  · let Subsets : Finset (Finset I) := Finset.univ.powersetCard blocks
    have hSub_card : Subsets.card = C := by
      dsimp only [Subsets, C]
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      congr 1; ring
    have hC_pos : 0 < C := Nat.choose_pos (by omega : blocks ≤ 2 * blocks)
    have h2b_le_C : 2 ^ blocks ≤ C := by
      have h1 := card_transverse_subsets blocks (1 : Equiv.Perm I)
      have h2 : ((Finset.univ.powersetCard blocks : Finset (Finset I)).filter
          (fun U => ∀ b : Fin blocks, decide ((1 : Equiv.Perm I).symm (b, 0) ∈ U) ≠
            decide ((1 : Equiv.Perm I).symm (b, 1) ∈ U))).card ≤ Subsets.card :=
        Finset.card_filter_le _ _
      rw [h1, hSub_card] at h2
      exact h2
    let t : ℕ := 2 * C / 2 ^ blocks + 1
    have ht_pos : 0 < t := Nat.succ_pos _
    have ht_lo : 2 * C ≤ t * 2 ^ blocks := by
      dsimp only [t]
      have hpos : 0 < 2 ^ blocks := by positivity
      have hmod := Nat.div_add_mod (2 * C) (2 ^ blocks)
      have hlt := Nat.mod_lt (2 * C) hpos
      nlinarith
    have ht_hi : t * 2 ^ blocks ≤ 2 * C + 2 ^ blocks := by
      dsimp only [t]
      have h1 := Nat.div_mul_le_self (2 * C) (2 ^ blocks)
      nlinarith
    let R : ℕ := C ^ t
    have hR_pos : 0 < R := Nat.pow_pos hC_pos
    have hcard_fn : Fintype.card (Fin t → ↥Subsets) = R := by
      rw [Fintype.card_pi]
      simp [Fintype.card_coe, hSub_card, R]
    let eR : Fin R ≃ (Fin t → ↥Subsets) := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard_fn])
    let U : Fin R → Fin t → Finset I := fun u h => (eR u h).1
    refine ⟨R, t, U, hR_pos, ht_pos, fun u h => (Finset.mem_powersetCard.mp (eR u h).2).2, ht_hi, ?_⟩
    intro π mat hnn hsupp
    let GoodSub : Finset ↥Subsets :=
      Finset.univ.filter (fun s : ↥Subsets =>
        ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ s.1) ≠ decide (π.symm (b, 1) ∈ s.1))
    let BadSub : Finset ↥Subsets :=
      Finset.univ.filter (fun s : ↥Subsets =>
        ¬ ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ s.1) ≠ decide (π.symm (b, 1) ∈ s.1))
    have hGood_card : GoodSub.card = 2 ^ blocks := by
      have h1 := card_transverse_subsets blocks π
      rw [← h1]
      refine Finset.card_bij (fun s _ => s.1) ?_ ?_ ?_
      · intro s hs
        exact Finset.mem_filter.mpr ⟨s.2, (Finset.mem_filter.mp hs).2⟩
      · intro s₁ _ s₂ _ h; exact Subtype.ext h
      · intro V hV
        rcases Finset.mem_filter.mp hV with ⟨hVs, htr⟩
        exact ⟨⟨V, hVs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htr⟩, rfl⟩
    have hBad_card : BadSub.card = C - 2 ^ blocks := by
      have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ↥Subsets))
        (p := fun s : ↥Subsets =>
          ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ s.1) ≠ decide (π.symm (b, 1) ∈ s.1))
      have huniv : (Finset.univ : Finset ↥Subsets).card = C := by
        rw [Finset.card_univ, Fintype.card_coe, hSub_card]
      change GoodSub.card + BadSub.card = (Finset.univ : Finset ↥Subsets).card at hsum
      rw [hGood_card, huniv] at hsum
      omega
    let AllBad : Finset (Fin R) :=
      Finset.univ.filter (fun u : Fin R => ∀ h : Fin t, eR u h ∈ BadSub)
    have hAllBad_card : AllBad.card = (C - 2 ^ blocks) ^ t := by
      have hbij : AllBad.card = Fintype.card (Fin t → ↥BadSub) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun u hu h => ⟨eR u h, (Finset.mem_filter.mp hu).2 h⟩) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro u₁ _ u₂ _ h12
          apply eR.injective
          funext h
          exact congrArg Subtype.val (congrFun h12 h)
        · intro f _
          refine ⟨eR.symm (fun h => (f h).1), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
            rw [eR.apply_symm_apply]
            exact (f h).2
          · funext h
            apply Subtype.ext
            dsimp only
            rw [eR.apply_symm_apply]
      rw [hbij, Fintype.card_pi]
      simp [Fintype.card_coe, hBad_card]
    have hBern : 3 * (C - 2 ^ blocks) ^ t ≤ R := by
      have h1 := bernoulli_nat C (2 ^ blocks) t h2b_le_C
      have h2 : 3 * C ≤ C + t * 2 ^ blocks := by omega
      have h3 : (C - 2 ^ blocks) ^ t * (3 * C) ≤ C ^ (t + 1) :=
        le_trans (Nat.mul_le_mul_left _ h2) h1
      have h4 : (3 * (C - 2 ^ blocks) ^ t) * C ≤ R * C := by
        calc (3 * (C - 2 ^ blocks) ^ t) * C = (C - 2 ^ blocks) ^ t * (3 * C) := by ring
          _ ≤ C ^ (t + 1) := h3
          _ = R * C := by dsimp only [R]; rw [pow_succ]
      exact Nat.le_of_mul_le_mul_right h4 hC_pos
    have hHit_ge : R - AllBad.card ≤ ((Finset.univ : Finset (Fin R)).filter (fun u => ∃ h : Fin t,
        |D mat (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U u h))| = mat.permanent)).card := by
      have hsub : (Finset.univ : Finset (Fin R)) \ AllBad ⊆
          (Finset.univ : Finset (Fin R)).filter (fun u => ∃ h : Fin t,
            |D mat (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U u h))| = mat.permanent) := by
        intro u hu
        have hnot : ¬ (∀ h : Fin t, eR u h ∈ BadSub) := by
          intro hall_b
          exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall_b⟩)
        push Not at hnot
        rcases hnot with ⟨h, hh⟩
        have htr : ∀ b : Fin blocks, decide (π.symm (b, 0) ∈ U u h) ≠ decide (π.symm (b, 1) ∈ U u h) := by
          simp only [BadSub, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hh
          exact hh
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, ?_⟩
        exact abs_det_eq_permanent_of_transverse π mat hnn hsupp (U u h) htr
      have hsdiff : ((Finset.univ : Finset (Fin R)) \ AllBad).card = R - AllBad.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [← hsdiff]
      exact Finset.card_le_card hsub
    rw [hAllBad_card] at hHit_ge
    change 2 * R ≤ 3 * ((Finset.univ : Finset (Fin R)).filter (fun u => ∃ h : Fin t,
      |D mat (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U u h))| = mat.permanent)).card
    omega

end PEqualNP.Outside.L_lib_997_aux

theorem PEqualNP.Outside.L_lib_997 :
  ∀ blocks : ℕ, 0 < blocks →
    let I := Fin blocks × Fin 2
    let S := I × I → Bool
    let D := fun (mat : Matrix I I ℝ) (s : S) =>
      Matrix.det (fun i j => if s (i,j) then -mat i j else mat i j : Matrix I I ℝ)
    let board := fun (π : Equiv.Perm I) (i j : I) => if i.1 = (π j).1 then (1 : ℝ) else 0
    let C := Nat.choose (2*blocks) blocks
    (∀ (R t : ℕ), 0 < R →
      ∀ (query : Fin R → ℕ → List ℝ → S) (accept : Fin R → List ℝ → Bool),
      let run := fun (mat : Matrix I I ℝ) (u : Fin R) =>
        (List.range t).foldl (fun h j => D mat (query u j h) :: h) ([] : List ℝ)
      let yes := fun mat : Matrix I I ℝ =>
        ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run mat u))).card
      3 * yes 0 ≤ R → (∀ π : Equiv.Perm I, 2*R ≤ 3 * yes (board π)) →
        C ≤ 3*t*2^blocks) ∧
    (∃ (R t : ℕ) (U : Fin R → Fin t → Finset I), 0 < R ∧ 0 < t ∧
      (∀ u h, (U u h).card = blocks) ∧ t*2^blocks ≤ 2*C + 2^blocks ∧
      ∀ (π : Equiv.Perm I) (mat : Matrix I I ℝ), (∀ i j, 0 ≤ mat i j) →
        (∀ i j, i.1 ≠ (π j).1 → mat i j = 0) →
        2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter (fun u => ∃ h : Fin t,
          |D mat (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U u h))| = mat.permanent)).card) := by
  exact PEqualNP.Outside.L_lib_997_aux.main_proof
