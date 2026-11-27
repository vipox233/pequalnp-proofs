import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_704_aux

private abbrev Psq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.permanent (fun i j => (H i j) ^ 2)

private def syl : (h : ℕ) → Matrix (Fin (2 ^ h)) (Fin (2 ^ h)) ℝ
  | 0 => fun _ _ => 1
  | h + 1 => fun i j =>
      let hi : Fin (2 ^ h) := ⟨i.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩
      let hj : Fin (2 ^ h) := ⟨j.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩
      if i.val < 2 ^ h ∨ j.val < 2 ^ h then syl h hi hj else -(syl h hi hj)

private lemma syl_entries :
    ∀ (h : ℕ) (i j : Fin (2 ^ h)), syl h i j = -1 ∨ syl h i j = 1
  | 0, _, _ => Or.inr rfl
  | h + 1, i, j => by
      unfold syl
      dsimp only
      split_ifs
      · exact syl_entries h _ _
      · rcases syl_entries h ⟨i.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩
            ⟨j.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩ with h1 | h2
        · right; rw [h1]; norm_num
        · left; rw [h2]

private lemma syl_sq_eq_one (h : ℕ) (i j : Fin (2 ^ h)) : (syl h i j) ^ 2 = 1 := by
  rcases syl_entries h i j with h1 | h2
  · rw [h1]; norm_num
  · rw [h2]; norm_num

private lemma syl_Psq (h : ℕ) : Psq (syl h) = ((2 ^ h).factorial : ℝ) := by
  unfold Psq Matrix.permanent
  have h1 : ∀ σ : Equiv.Perm (Fin (2 ^ h)), (∏ i : Fin (2 ^ h), (syl h (σ i) i) ^ 2) = 1 := by
    intro σ
    refine Finset.prod_eq_one fun i _ => syl_sq_eq_one h (σ i) i
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]

private lemma syl_succ (h : ℕ) (i j : Fin (2 ^ (h + 1))) :
    syl (h + 1) i j =
      if i.val < 2 ^ h ∨ j.val < 2 ^ h then
        syl h ⟨i.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩
          ⟨j.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩
      else
        -(syl h ⟨i.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩
          ⟨j.val % 2 ^ h, Nat.mod_lt _ (pow_pos (by decide) h)⟩) := rfl

private lemma syl_mul_transpose :
    ∀ h : ℕ, syl h * (syl h).transpose = ((2 ^ h : ℝ)) • (1 : Matrix (Fin (2 ^ h)) (Fin (2 ^ h)) ℝ)
  | 0 => by
      ext i j
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
      have hj : j = ⟨0, by decide⟩ := Fin.ext (by have := j.isLt; simp at this; omega)
      subst hi hj
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      have huniv : (Finset.univ : Finset (Fin (2 ^ 0))) = {⟨0, by decide⟩} := by
        ext x
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Fin.ext (by have := x.isLt; simp at this; omega)
      rw [huniv, Finset.sum_singleton, Matrix.transpose_apply]
      simp [syl]
  | h + 1 => by
      have ih := syl_mul_transpose h
      have hpow : 0 < 2 ^ h := pow_pos (by decide) h
      ext i j
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      let e : Fin (2 ^ h) ⊕ Fin (2 ^ h) ≃ Fin (2 ^ (h + 1)) :=
        finSumFinEquiv.trans (finCongr (by rw [pow_succ]; ring))
      rw [← Equiv.sum_comp e]
      rw [Fintype.sum_sum_type]
      let hi : Fin (2 ^ h) := ⟨i.val % 2 ^ h, Nat.mod_lt _ hpow⟩
      let hj : Fin (2 ^ h) := ⟨j.val % 2 ^ h, Nat.mod_lt _ hpow⟩
      have heL : ∀ k : Fin (2 ^ h), (e (Sum.inl k)).val = k.val := fun k => by
        simp [e, finSumFinEquiv]
      have heR : ∀ k : Fin (2 ^ h), (e (Sum.inr k)).val = 2 ^ h + k.val := fun k => by
        simp [e, finSumFinEquiv]; omega
      have hmodL : ∀ k : Fin (2 ^ h), (e (Sum.inl k)).val % 2 ^ h = k.val := fun k => by
        rw [heL, Nat.mod_eq_of_lt k.isLt]
      have hmodR : ∀ k : Fin (2 ^ h), (e (Sum.inr k)).val % 2 ^ h = k.val := fun k => by
        rw [heR, Nat.add_mod_left, Nat.mod_eq_of_lt k.isLt]
      have hltL : ∀ k : Fin (2 ^ h), (e (Sum.inl k)).val < 2 ^ h := fun k => by
        rw [heL]; exact k.isLt
      have hgeR : ∀ k : Fin (2 ^ h), ¬ ((e (Sum.inr k)).val < 2 ^ h) := fun k => by
        rw [heR]; omega
      have hsum_ih : (∑ k : Fin (2 ^ h), syl h hi k * syl h hj k) =
          (2 ^ h : ℝ) * (if hi = hj then 1 else 0) := by
        have h' := congrFun (congrFun ih hi) hj
        simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul] using h'
      have hL : (∑ k : Fin (2 ^ h), syl (h + 1) i (e (Sum.inl k)) *
          (syl (h + 1)).transpose (e (Sum.inl k)) j) =
          ∑ k : Fin (2 ^ h), syl h hi k * syl h hj k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have h1 : syl (h + 1) i (e (Sum.inl k)) = syl h hi k := by
          rw [syl_succ]
          have hcond : i.val < 2 ^ h ∨ (e (Sum.inl k)).val < 2 ^ h := Or.inr (hltL k)
          simp only [hcond, ↓reduceIte]
          congr 1; exact Fin.ext (hmodL k)
        have h2 : (syl (h + 1)).transpose (e (Sum.inl k)) j = syl h hj k := by
          rw [Matrix.transpose_apply, syl_succ]
          have hcond : j.val < 2 ^ h ∨ (e (Sum.inl k)).val < 2 ^ h := Or.inr (hltL k)
          simp only [hcond, ↓reduceIte]
          congr 1; exact Fin.ext (hmodL k)
        rw [h1, h2]
      have hR_term : ∀ k : Fin (2 ^ h),
          syl (h + 1) i (e (Sum.inr k)) * (syl (h + 1)).transpose (e (Sum.inr k)) j =
            (if i.val < 2 ^ h then syl h hi k else -(syl h hi k)) *
            (if j.val < 2 ^ h then syl h hj k else -(syl h hj k)) := by
        intro k
        have h1 : syl (h + 1) i (e (Sum.inr k)) =
            if i.val < 2 ^ h then syl h hi k else -(syl h hi k) := by
          rw [syl_succ]
          have hk : ¬ ((e (Sum.inr k)).val < 2 ^ h) := hgeR k
          by_cases hi' : i.val < 2 ^ h
          · simp only [hi', true_or, ↓reduceIte]
            congr 1; exact Fin.ext (hmodR k)
          · simp only [hi', hk, or_self, ↓reduceIte]
            congr 1; congr 1; exact Fin.ext (hmodR k)
        have h2 : (syl (h + 1)).transpose (e (Sum.inr k)) j =
            if j.val < 2 ^ h then syl h hj k else -(syl h hj k) := by
          rw [Matrix.transpose_apply, syl_succ]
          have hk : ¬ ((e (Sum.inr k)).val < 2 ^ h) := hgeR k
          by_cases hj' : j.val < 2 ^ h
          · simp only [hj', true_or, ↓reduceIte]
            congr 1; exact Fin.ext (hmodR k)
          · simp only [hj', hk, or_self, ↓reduceIte]
            congr 1; congr 1; exact Fin.ext (hmodR k)
        rw [h1, h2]
      rw [hL]
      simp_rw [hR_term]
      by_cases hi' : i.val < 2 ^ h <;> by_cases hj' : j.val < 2 ^ h
      · simp only [hi', hj', ↓reduceIte]
        rw [hsum_ih]
        have hiff : hi = hj ↔ i = j := by
          constructor
          · intro h'
            have hv : i.val % 2 ^ h = j.val % 2 ^ h := congrArg Fin.val h'
            rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hv
            exact Fin.ext hv
          · intro h'; subst h'; rfl
        by_cases hij : i = j
        · have h' : hi = hj := hiff.2 hij
          simp only [hij, h', ↓reduceIte, pow_succ]
          ring
        · have h' : hi ≠ hj := fun h'' => hij (hiff.1 h'')
          simp only [hij, h', ↓reduceIte]
          ring
      · simp only [hi', hj', ↓reduceIte, mul_neg, Finset.sum_neg_distrib]
        have hij : i ≠ j := fun h' => hj' (h' ▸ hi')
        simp only [hij, ↓reduceIte]
        ring
      · simp only [hi', hj', ↓reduceIte, neg_mul, Finset.sum_neg_distrib]
        have hij : i ≠ j := fun h' => hi' (h' ▸ hj')
        simp only [hij, ↓reduceIte]
        ring
      · simp only [hi', hj', ↓reduceIte, neg_mul_neg]
        rw [hsum_ih]
        have h2pow : 2 ^ (h + 1) = 2 ^ h + 2 ^ h := by rw [pow_succ]; ring
        have hi_lt : i.val < 2 ^ h + 2 ^ h := by have := i.isLt; omega
        have hj_lt : j.val < 2 ^ h + 2 ^ h := by have := j.isLt; omega
        have hiff : hi = hj ↔ i = j := by
          constructor
          · intro h'
            have hv : i.val % 2 ^ h = j.val % 2 ^ h := congrArg Fin.val h'
            have h1 : i.val = 2 ^ h + (i.val - 2 ^ h) := by omega
            have h1m : i.val % 2 ^ h = i.val - 2 ^ h := by
              conv_lhs => rw [h1]
              rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have h2 : j.val = 2 ^ h + (j.val - 2 ^ h) := by omega
            have h2m : j.val % 2 ^ h = j.val - 2 ^ h := by
              conv_lhs => rw [h2]
              rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            exact Fin.ext (by omega)
          · intro h'; subst h'; rfl
        by_cases hij : i = j
        · have h' : hi = hj := hiff.2 hij
          simp only [hij, h', ↓reduceIte, pow_succ]
          ring
        · have h' : hi ≠ hj := fun h'' => hij (hiff.1 h'')
          simp only [hij, h', ↓reduceIte]
          ring

private lemma syl_det_sq (h : ℕ) : (syl h).det ^ 2 = ((2 ^ h : ℕ) : ℝ) ^ (2 ^ h) := by
  have hm := congrArg Matrix.det (syl_mul_transpose h)
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_one, mul_one] at hm
  simpa using hm

private lemma permanent_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (M : Matrix α α ℝ) :
    Matrix.permanent (Matrix.reindex e e M) = Matrix.permanent M := by
  unfold Matrix.permanent
  let conj : Equiv.Perm α ≃ Equiv.Perm β :=
    { toFun := fun σ => e.symm.trans (σ.trans e)
      invFun := fun τ => e.trans (τ.trans e.symm)
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext y; simp }
  rw [← Equiv.sum_comp conj]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [conj, Matrix.reindex_apply, Matrix.submatrix_apply]

private lemma permanent_fromBlocks_zero {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    Matrix.permanent (Matrix.fromBlocks A 0 0 B) = Matrix.permanent A * Matrix.permanent B := by
  unfold Matrix.permanent
  let M := Matrix.fromBlocks A (0 : Matrix α β ℝ) (0 : Matrix β α ℝ) B
  let Good : Finset (Equiv.Perm (α ⊕ β)) :=
    Finset.univ.filter (fun σ => (∀ i : α, ∃ i' : α, σ (Sum.inl i) = Sum.inl i') ∧
      (∀ j : β, ∃ j' : β, σ (Sum.inr j) = Sum.inr j'))
  have hsum_good : (∑ σ : Equiv.Perm (α ⊕ β), ∏ x : α ⊕ β, M (σ x) x) =
      ∑ σ ∈ Good, ∏ x : α ⊕ β, M (σ x) x := by
    rw [← Finset.sum_subset (Finset.subset_univ Good)]
    intro σ _ hσ
    simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    push Not at hσ
    by_cases h1 : ∃ i : α, ∀ i' : α, σ (Sum.inl i) ≠ Sum.inl i'
    · rcases h1 with ⟨i, hi⟩
      refine Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i)) ?_
      cases hval : σ (Sum.inl i) with
      | inl i' => exact absurd hval (hi i')
      | inr j' => simp [M]
    · push Not at h1
      rcases hσ h1 with ⟨j, hj⟩
      refine Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j)) ?_
      cases hval : σ (Sum.inr j) with
      | inl i' => simp [M]
      | inr j' => exact absurd hval (hj j')
  rw [hsum_good]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun (p : Equiv.Perm α × Equiv.Perm β) _ => Equiv.Perm.sumCongr p.1 p.2)
    ?_ ?_ ?_ ?_
  · intro p _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro i; exact ⟨p.1 i, rfl⟩
    · intro j; exact ⟨p.2 j, rfl⟩
  · intro p1 _ p2 _ heq
    apply Prod.ext
    · ext i
      have h := congrArg (fun f : Equiv.Perm (α ⊕ β) => f (Sum.inl i)) heq
      simpa using h
    · ext j
      have h := congrArg (fun f : Equiv.Perm (α ⊕ β) => f (Sum.inr j)) heq
      simpa using h
  · intro σ hσ
    rcases (Finset.mem_filter.1 hσ).2 with ⟨hL, hR⟩
    have hL_inv : ∀ i : α, ∃ i' : α, σ.symm (Sum.inl i) = Sum.inl i' := by
      intro i
      cases hval : σ.symm (Sum.inl i) with
      | inl i' => exact ⟨i', rfl⟩
      | inr j' =>
          rcases hR j' with ⟨j'', hj''⟩
          have h1 := congrArg σ hval
          rw [Equiv.apply_symm_apply, hj''] at h1
          exact absurd h1 (by simp)
    have hR_inv : ∀ j : β, ∃ j' : β, σ.symm (Sum.inr j) = Sum.inr j' := by
      intro j
      cases hval : σ.symm (Sum.inr j) with
      | inr j' => exact ⟨j', rfl⟩
      | inl i' =>
          rcases hL i' with ⟨i'', hi''⟩
          have h1 := congrArg σ hval
          rw [Equiv.apply_symm_apply, hi''] at h1
          exact absurd h1 (by simp)
    let p1 : Equiv.Perm α :=
      { toFun := fun i => Classical.choose (hL i)
        invFun := fun i => Classical.choose (hL_inv i)
        left_inv := fun i => by
          apply Sum.inl.inj
          have h1 := Classical.choose_spec (hL i)
          have h2 := Classical.choose_spec (hL_inv (Classical.choose (hL i)))
          have h3 : σ.symm (Sum.inl (Classical.choose (hL i))) = Sum.inl i := by
            rw [← h1, Equiv.symm_apply_apply]
          exact h2.symm.trans h3
        right_inv := fun i => by
          apply Sum.inl.inj
          have h1 := Classical.choose_spec (hL_inv i)
          have h2 := Classical.choose_spec (hL (Classical.choose (hL_inv i)))
          have h3 : σ (Sum.inl (Classical.choose (hL_inv i))) = Sum.inl i := by
            rw [← h1, Equiv.apply_symm_apply]
          exact h2.symm.trans h3 }
    let p2 : Equiv.Perm β :=
      { toFun := fun j => Classical.choose (hR j)
        invFun := fun j => Classical.choose (hR_inv j)
        left_inv := fun j => by
          apply Sum.inr.inj
          have h1 := Classical.choose_spec (hR j)
          have h2 := Classical.choose_spec (hR_inv (Classical.choose (hR j)))
          have h3 : σ.symm (Sum.inr (Classical.choose (hR j))) = Sum.inr j := by
            rw [← h1, Equiv.symm_apply_apply]
          exact h2.symm.trans h3
        right_inv := fun j => by
          apply Sum.inr.inj
          have h1 := Classical.choose_spec (hR_inv j)
          have h2 := Classical.choose_spec (hR (Classical.choose (hR_inv j)))
          have h3 : σ (Sum.inr (Classical.choose (hR_inv j))) = Sum.inr j := by
            rw [← h1, Equiv.apply_symm_apply]
          exact h2.symm.trans h3 }
    refine ⟨(p1, p2), Finset.mem_univ _, ?_⟩
    ext x
    cases x with
    | inl i =>
        change Sum.inl (Classical.choose (hL i)) = σ (Sum.inl i)
        exact (Classical.choose_spec (hL i)).symm
    | inr j =>
        change Sum.inr (Classical.choose (hR j)) = σ (Sum.inr j)
        exact (Classical.choose_spec (hR j)).symm
  · intro p _
    rw [Fintype.prod_sum_type]
    rfl

private def blockSum {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

private lemma blockSum_ternary {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℝ} {B : Matrix (Fin b) (Fin b) ℝ}
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hB : ∀ i j, B i j = -1 ∨ B i j = 0 ∨ B i j = 1) :
    ∀ i j, blockSum A B i j = -1 ∨ blockSum A B i j = 0 ∨ blockSum A B i j = 1 := by
  intro i j
  unfold blockSum
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  cases finSumFinEquiv.symm i with
  | inl i1 =>
      cases finSumFinEquiv.symm j with
      | inl j1 => exact hA i1 j1
      | inr j2 => exact Or.inr (Or.inl rfl)
  | inr i2 =>
      cases finSumFinEquiv.symm j with
      | inl j1 => exact Or.inr (Or.inl rfl)
      | inr j2 => exact hB i2 j2

private lemma blockSum_det {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ) :
    (blockSum A B).det = A.det * B.det := by
  unfold blockSum
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

private lemma blockSum_Psq {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ) :
    Psq (blockSum A B) = Psq A * Psq B := by
  let A2 : Matrix (Fin a) (Fin a) ℝ := fun i j => (A i j) ^ 2
  let B2 : Matrix (Fin b) (Fin b) ℝ := fun i j => (B i j) ^ 2
  have hsq : (fun i j => (blockSum A B i j) ^ 2 : Matrix (Fin (a + b)) (Fin (a + b)) ℝ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A2 0 0 B2) := by
    ext i j
    unfold blockSum
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      simp [A2, B2, Matrix.fromBlocks]
  unfold Psq
  rw [hsq, permanent_reindex, permanent_fromBlocks_zero]

private lemma Psq_reindex {a b : ℕ} (e : Fin a ≃ Fin b) (M : Matrix (Fin a) (Fin a) ℝ) :
    Psq (Matrix.reindex e e M) = Psq M := by
  unfold Psq
  let M2 : Matrix (Fin a) (Fin a) ℝ := fun i j => (M i j) ^ 2
  have hsq : (fun i j => ((Matrix.reindex e e M) i j) ^ 2 : Matrix (Fin b) (Fin b) ℝ) =
      Matrix.reindex e e M2 := by
    ext i j; rfl
  exact (congrArg Matrix.permanent hsq).trans (permanent_reindex e M2)

private lemma exists_block_syl :
    ∀ exps : List ℕ,
      let n := (exps.map (fun k => 2 ^ k)).sum
      ∃ H : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1) ∧
        Psq H = ((exps.map (fun k => (2 ^ k).factorial)).prod : ℕ) ∧
        H.det ^ 2 = ((exps.map (fun k => (2 ^ k) ^ (2 ^ k))).prod : ℕ)
  | [] => by
      dsimp only [List.map_nil, List.sum_nil, List.prod_nil]
      refine ⟨(1 : Matrix (Fin 0) (Fin 0) ℝ), fun i _ => Fin.elim0 i, ?_, ?_⟩
      · unfold Psq Matrix.permanent
        simp
      · change (Matrix.det (1 : Matrix (Fin 0) (Fin 0) ℝ)) ^ 2 = 1
        simp
  | k :: rest => by
      dsimp only
      rcases exists_block_syl rest with ⟨H2, hH2_t, hH2_P, hH2_d⟩
      have hlen : 2 ^ k + (rest.map (fun k => 2 ^ k)).sum =
          ((k :: rest).map (fun k => 2 ^ k)).sum := by simp
      let e : Fin (2 ^ k + (rest.map (fun k => 2 ^ k)).sum) ≃
          Fin (((k :: rest).map (fun k => 2 ^ k)).sum) := finCongr hlen
      let H1 : Matrix (Fin (2 ^ k + (rest.map (fun k => 2 ^ k)).sum))
          (Fin (2 ^ k + (rest.map (fun k => 2 ^ k)).sum)) ℝ := blockSum (syl k) H2
      refine ⟨Matrix.reindex e e H1, ?_, ?_, ?_⟩
      · intro i j
        exact blockSum_ternary (fun i' j' => by
          rcases syl_entries k i' j' with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inr h2)) hH2_t (e.symm i) (e.symm j)
      · rw [Psq_reindex]
        change Psq (blockSum (syl k) H2) = _
        rw [blockSum_Psq, syl_Psq, hH2_P]
        simp [Nat.cast_mul]
      · rw [Matrix.det_reindex_self]
        change (blockSum (syl k) H2).det ^ 2 = _
        rw [blockSum_det, mul_pow, syl_det_sq, hH2_d]
        simp [Nat.cast_mul]

private lemma fact_mul_pow_le (d j : ℕ) : d.factorial * d ^ j ≤ j.factorial * d ^ d := by
  by_cases h : j ≤ d
  · have haux : ∀ t : ℕ, (j + t).factorial ≤ j.factorial * (j + t) ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ m ih =>
          have h1 : j + (m + 1) = (j + m) + 1 := by omega
          rw [h1, Nat.factorial_succ, pow_succ]
          have hpow : (j + m) ^ m ≤ (j + m + 1) ^ m := Nat.pow_le_pow_left (by omega) m
          calc
            (j + m + 1) * (j + m).factorial
                ≤ (j + m + 1) * (j.factorial * (j + m) ^ m) := Nat.mul_le_mul_left _ ih
            _ ≤ (j + m + 1) * (j.factorial * (j + m + 1) ^ m) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow)
            _ = j.factorial * ((j + m + 1) ^ m * (j + m + 1)) := by ring
    have hd : j + (d - j) = d := Nat.add_sub_of_le h
    have hle := haux (d - j)
    rw [hd] at hle
    calc
      d.factorial * d ^ j ≤ (j.factorial * d ^ (d - j)) * d ^ j := Nat.mul_le_mul_right _ hle
      _ = j.factorial * (d ^ (d - j) * d ^ j) := by ring
      _ = j.factorial * d ^ d := by rw [← pow_add, Nat.sub_add_cancel h]
  · have hge : d ≤ j := by omega
    have haux : ∀ t : ℕ, d.factorial * d ^ t ≤ (d + t).factorial := by
      intro t
      induction t with
      | zero => simp
      | succ m ih =>
          have h1 : d + (m + 1) = (d + m) + 1 := by omega
          rw [h1, Nat.factorial_succ, pow_succ]
          calc
            d.factorial * (d ^ m * d) = d * (d.factorial * d ^ m) := by ring
            _ ≤ (d + m + 1) * (d + m).factorial := Nat.mul_le_mul (by omega) ih
    have hj : d + (j - d) = j := Nat.add_sub_of_le hge
    have hle := haux (j - d)
    rw [hj] at hle
    calc
      d.factorial * d ^ j = d.factorial * (d ^ (j - d) * d ^ d) := by
            rw [← pow_add, Nat.sub_add_cancel hge]
      _ = (d.factorial * d ^ (j - d)) * d ^ d := by ring
      _ ≤ j.factorial * d ^ d := Nat.mul_le_mul_right _ hle

private lemma fiber_equiv_apply_eq {α β : Type*} {f g : α → β} {a : α} {b1 b2 : β}
    (e : (i : β) → {x : α // f x = i} ≃ {x : α // g x = i}) (h1 : f a = b1) (h2 : f a = b2) :
    (e b1 ⟨a, h1⟩).1 = (e b2 ⟨a, h2⟩).1 := by
  have h : b1 = b2 := h1.symm.trans h2
  subst h; rfl

private lemma fiber_equiv_symm_eq {α β : Type*} {f g : α → β} {a : α} {b1 b2 : β}
    (e : (i : β) → {x : α // f x = i} ≃ {x : α // g x = i}) (h1 : g a = b1) (h2 : g a = b2) :
    ((e b1).symm ⟨a, h1⟩).1 = ((e b2).symm ⟨a, h2⟩).1 := by
  have h : b1 = b2 := h1.symm.trans h2
  subst h; rfl

private lemma card_fiber_mul_fact_le {n r : ℕ} (c : Fin r → Fin (n + 1)) :
    let Fc := (Finset.univ : Finset (Fin n → Fin r)).filter
      (fun f => ∀ i : Fin r, (Finset.univ.filter (fun t => f t = i)).card = (c i).val)
    Fc.card * (∏ i : Fin r, (c i).val.factorial) ≤ n.factorial := by
  intro Fc
  by_cases hne : Fc.Nonempty
  · rcases hne with ⟨f0, hf0⟩
    have hf0_c : ∀ i : Fin r, (Finset.univ.filter (fun t => f0 t = i)).card = (c i).val :=
      (Finset.mem_filter.1 hf0).2
    let Stab : Finset (Equiv.Perm (Fin n)) :=
      Finset.univ.filter (fun σ => ∀ t : Fin n, f0 (σ t) = f0 t)
    have hstab_ge : (∏ i : Fin r, (c i).val.factorial) ≤ Stab.card := by
      let G := (i : Fin r) → Equiv.Perm {t : Fin n // f0 t = i}
      have hGcard : Fintype.card G = ∏ i : Fin r, (c i).val.factorial := by
        rw [Fintype.card_pi]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Fintype.card_perm, Fintype.card_subtype, hf0_c i]
      rw [← hGcard, ← Finset.card_univ]
      let emb : G → Equiv.Perm (Fin n) := fun g =>
        { toFun := fun t => (g (f0 t) ⟨t, rfl⟩).1
          invFun := fun t => ((g (f0 t)).symm ⟨t, rfl⟩).1
          left_inv := fun t => by
            let y := g (f0 t) ⟨t, rfl⟩
            change ((g (f0 y.1)).symm ⟨y.1, rfl⟩).1 = t
            rw [fiber_equiv_symm_eq g rfl y.2]
            change ((g (f0 t)).symm (g (f0 t) ⟨t, rfl⟩)).1 = t
            rw [Equiv.symm_apply_apply]
          right_inv := fun t => by
            let y := (g (f0 t)).symm ⟨t, rfl⟩
            change (g (f0 y.1) ⟨y.1, rfl⟩).1 = t
            rw [fiber_equiv_apply_eq g rfl y.2]
            change (g (f0 t) ((g (f0 t)).symm ⟨t, rfl⟩)).1 = t
            rw [Equiv.apply_symm_apply] }
      refine Finset.card_le_card_of_injOn emb ?_ ?_
      · intro g _
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun t => ?_⟩
        exact (g (f0 t) ⟨t, rfl⟩).2
      · intro g1 _ g2 _ heq
        funext i
        ext ⟨t, ht⟩
        have h := congrArg (fun σ : Equiv.Perm (Fin n) => σ t) heq
        change (g1 (f0 t) ⟨t, rfl⟩).1 = (g2 (f0 t) ⟨t, rfl⟩).1 at h
        subst ht
        exact congrArg Fin.val h
    have hex_tau : ∀ f ∈ Fc, ∃ τ : Equiv.Perm (Fin n), ∀ t : Fin n, f0 (τ t) = f t := by
      intro f hf
      have hf_c : ∀ i : Fin r, (Finset.univ.filter (fun t => f t = i)).card = (c i).val :=
        (Finset.mem_filter.1 hf).2
      let e : (i : Fin r) → {t : Fin n // f t = i} ≃ {t : Fin n // f0 t = i} := fun i =>
        Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, hf_c i, hf0_c i])
      refine ⟨{
        toFun := fun t => (e (f t) ⟨t, rfl⟩).1
        invFun := fun t => ((e (f0 t)).symm ⟨t, rfl⟩).1
        left_inv := fun t => by
          let y := e (f t) ⟨t, rfl⟩
          change ((e (f0 y.1)).symm ⟨y.1, rfl⟩).1 = t
          rw [fiber_equiv_symm_eq e rfl y.2]
          change ((e (f t)).symm (e (f t) ⟨t, rfl⟩)).1 = t
          rw [Equiv.symm_apply_apply]
        right_inv := fun t => by
          let y := (e (f0 t)).symm ⟨t, rfl⟩
          change (e (f y.1) ⟨y.1, rfl⟩).1 = t
          rw [fiber_equiv_apply_eq e rfl y.2]
          change (e (f0 t) ((e (f0 t)).symm ⟨t, rfl⟩)).1 = t
          rw [Equiv.apply_symm_apply] }, fun t => (e (f t) ⟨t, rfl⟩).2⟩
    let tau : (f : Fin n → Fin r) → Equiv.Perm (Fin n) := fun f =>
      if hf : f ∈ Fc then Classical.choose (hex_tau f hf) else Equiv.refl _
    have htau : ∀ f ∈ Fc, ∀ t : Fin n, f0 (tau f t) = f t := by
      intro f hf
      simp only [tau, hf, ↓reduceDIte]
      exact Classical.choose_spec (hex_tau f hf)
    have hprod_le : (Fc ×ˢ Stab).card ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
      refine Finset.card_le_card_of_injOn (fun p => (tau p.1).trans p.2) (fun _ _ => Finset.mem_univ _) ?_
      intro p1 hp1 p2 hp2 heq
      dsimp only at heq
      have hf1 : p1.1 ∈ Fc := (Finset.mem_product.1 hp1).1
      have hf2 : p2.1 ∈ Fc := (Finset.mem_product.1 hp2).1
      have hs1 : ∀ t, f0 (p1.2 t) = f0 t := (Finset.mem_filter.1 (Finset.mem_product.1 hp1).2).2
      have hs2 : ∀ t, f0 (p2.2 t) = f0 t := (Finset.mem_filter.1 (Finset.mem_product.1 hp2).2).2
      have hfeq : p1.1 = p2.1 := by
        funext t
        have ht := congrArg (fun σ : Equiv.Perm (Fin n) => f0 (σ t)) heq
        simp only [Equiv.trans_apply, hs1, hs2] at ht
        rw [htau p1.1 hf1, htau p2.1 hf2] at ht
        exact ht
      have hseq : p1.2 = p2.2 := by
        rw [hfeq] at heq
        apply Equiv.ext
        intro t
        have ht := congrArg (fun σ : Equiv.Perm (Fin n) => σ ((tau p2.1).symm t)) heq
        simpa [Equiv.trans_apply] using ht
      exact Prod.ext hfeq hseq
    rw [Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hprod_le
    exact le_trans (Nat.mul_le_mul_left Fc.card hstab_ge) hprod_le
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

private lemma multinomial_mode_bound {n r : ℕ} (d : Fin r → ℕ) (hsum : (∑ i : Fin r, d i) = n) :
    (∏ i : Fin r, (d i).factorial) * n ^ n ≤
      (n + 1) ^ r * n.factorial * (∏ i : Fin r, (d i) ^ (d i)) := by
  have hnn : n ^ n = ∑ f : Fin n → Fin r, ∏ t : Fin n, d (f t) := by
    have h := Fintype.prod_sum (fun (_ : Fin n) (i : Fin r) => d i)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    rw [hsum] at h
    exact h
  let cnt : (Fin n → Fin r) → (Fin r → Fin (n + 1)) := fun f i =>
    ⟨(Finset.univ.filter (fun t : Fin n => f t = i)).card, by
      have hle : (Finset.univ.filter (fun t : Fin n => f t = i)).card ≤ n := by
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun t => f t = i)
      omega⟩
  have hprod_cnt : ∀ f : Fin n → Fin r,
      (∏ t : Fin n, d (f t)) = ∏ i : Fin r, (d i) ^ (cnt f i).val := by
    intro f
    have hmaps : ∀ t ∈ (Finset.univ : Finset (Fin n)), f t ∈ (Finset.univ : Finset (Fin r)) :=
      fun _ _ => Finset.mem_univ _
    rw [← Finset.prod_fiberwise_of_maps_to hmaps]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hc : (∏ t ∈ Finset.univ.filter (fun t : Fin n => f t = i), d (f t)) =
        ∏ _t ∈ Finset.univ.filter (fun t : Fin n => f t = i), d i := by
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [(Finset.mem_filter.1 ht).2]
    rw [hc, Finset.prod_const]
  rw [hnn, Finset.mul_sum]
  have hmaps_c : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin r)),
      cnt f ∈ (Finset.univ : Finset (Fin r → Fin (n + 1))) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps_c]
  have hterm : ∀ c : Fin r → Fin (n + 1),
      (∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c),
        (∏ i : Fin r, (d i).factorial) * ∏ t : Fin n, d (f t)) ≤
        n.factorial * (∏ i : Fin r, (d i) ^ (d i)) := by
    intro c
    have hcongr :
        (∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c),
          (∏ i : Fin r, (d i).factorial) * ∏ t : Fin n, d (f t)) =
        (Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c)).card *
          ((∏ i : Fin r, (d i).factorial) * (∏ i : Fin r, (d i) ^ (c i).val)) := by
      have hc : ∀ f ∈ Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c),
          (∏ i : Fin r, (d i).factorial) * ∏ t : Fin n, d (f t) =
            (∏ i : Fin r, (d i).factorial) * (∏ i : Fin r, (d i) ^ (c i).val) := by
        intro f hf
        rw [hprod_cnt f, (Finset.mem_filter.1 hf).2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
    rw [hcongr]
    have hmode : (∏ i : Fin r, (d i).factorial) * (∏ i : Fin r, (d i) ^ (c i).val) ≤
        (∏ i : Fin r, (c i).val.factorial) * (∏ i : Fin r, (d i) ^ (d i)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod fun i _ => fact_mul_pow_le (d i) (c i).val
    have hfeq : Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c) =
        Finset.univ.filter (fun f : Fin n → Fin r =>
          ∀ i : Fin r, (Finset.univ.filter (fun t : Fin n => f t = i)).card = (c i).val) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff, cnt]
    have hfib := card_fiber_mul_fact_le c
    rw [← hfeq] at hfib
    calc
      (Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c)).card *
          ((∏ i : Fin r, (d i).factorial) * (∏ i : Fin r, (d i) ^ (c i).val))
        ≤ (Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c)).card *
            ((∏ i : Fin r, (c i).val.factorial) * (∏ i : Fin r, (d i) ^ (d i))) :=
              Nat.mul_le_mul_left _ hmode
      _ = ((Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c)).card *
            (∏ i : Fin r, (c i).val.factorial)) * (∏ i : Fin r, (d i) ^ (d i)) := by ring
      _ ≤ n.factorial * (∏ i : Fin r, (d i) ^ (d i)) := Nat.mul_le_mul_right _ hfib
  calc
    ∑ c : Fin r → Fin (n + 1),
        ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin r => cnt f = c),
          (∏ i : Fin r, (d i).factorial) * ∏ t : Fin n, d (f t)
      ≤ ∑ _c : Fin r → Fin (n + 1), n.factorial * (∏ i : Fin r, (d i) ^ (d i)) :=
          Finset.sum_le_sum fun c _ => hterm c
    _ = (n + 1) ^ r * n.factorial * (∏ i : Fin r, (d i) ^ (d i)) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_pi]
          simp [mul_assoc]

private lemma sum_testBit_range :
    ∀ (m n : ℕ), n < 2 ^ m →
      (∑ k ∈ (Finset.range m).filter (fun k => n.testBit k = true), 2 ^ k) = n
  | 0, n, hn => by
      have hn0 : n = 0 := by omega
      subst hn0; simp
  | m + 1, n, hn => by
      have hsum_ite : ∀ (r : ℕ) (x : ℕ),
          (∑ k ∈ (Finset.range r).filter (fun k => x.testBit k = true), 2 ^ k) =
            ∑ k ∈ Finset.range r, if x.testBit k = true then 2 ^ k else 0 := by
        intro r x
        rw [Finset.sum_filter]
      rw [hsum_ite, Finset.sum_range_succ']
      have h0 : (if n.testBit 0 = true then (2 : ℕ) ^ 0 else 0) = n % 2 := by
        rw [Nat.testBit_zero]
        by_cases hodd : n % 2 = 1
        · simp [hodd]
        · simp [hodd]; omega
      have hsucc : (∑ k ∈ Finset.range m, if n.testBit (k + 1) = true then 2 ^ (k + 1) else 0) =
          2 * ∑ k ∈ Finset.range m, if (n / 2).testBit k = true then 2 ^ k else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.testBit_succ, pow_succ]
        split_ifs <;> ring
      rw [h0, hsucc, ← hsum_ite, sum_testBit_range m (n / 2) (by rw [pow_succ] at hn; omega)]
      have hdm := Nat.div_add_mod n 2
      omega

private lemma lt_two_pow_log2_succ {n : ℕ} (hn : 0 < n) : n < 2 ^ (Nat.log2 n + 1) :=
  (Nat.log2_lt (by omega)).1 (Nat.lt_succ_self _)

private lemma log2_two_pow (h : ℕ) : Nat.log2 (2 ^ h) = h := by
  have h1 : h ≤ Nat.log2 (2 ^ h) := (Nat.le_log2 (by positivity)).2 (le_refl _)
  have h2 : Nat.log2 (2 ^ h) < h + 1 := (Nat.log2_lt (by positivity)).2
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self h))
  omega

end PEqualNP.Outside.L_lib_704_aux

theorem PEqualNP.Outside.L_lib_704 :
∀ n : ℕ, 0 < n →
  let I := Fin n
  let P := fun H : Matrix I I ℝ => Matrix.permanent (fun i j => (H i j)^2)
  let penalty := (n+1)^(Nat.log2 n+1)
  ∃ H : Matrix I I ℝ,
    (∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1) ∧ 0 < P H ∧
    (n : ℝ)^n * P H ≤ (penalty : ℝ) * (n.factorial : ℝ) * H.det^2 ∧
    (∀ h : ℕ, n = 2^h → (n : ℝ)^n * P H = (n.factorial : ℝ) * H.det^2) := by
  intro n hn I P penalty
  let exps : List ℕ := (List.range (Nat.log2 n + 1)).filter (fun k => n.testBit k)
  have hnodup : exps.Nodup := (List.nodup_range).filter _
  have htoFinset : exps.toFinset = (Finset.range (Nat.log2 n + 1)).filter (fun k => n.testBit k = true) := by
    ext k
    simp [exps]
  have hsum_exps : (exps.map (fun k => 2 ^ k)).sum = n := by
    rw [← List.sum_toFinset _ hnodup, htoFinset]
    exact PEqualNP.Outside.L_lib_704_aux.sum_testBit_range (Nat.log2 n + 1) n
      (PEqualNP.Outside.L_lib_704_aux.lt_two_pow_log2_succ hn)
  rcases PEqualNP.Outside.L_lib_704_aux.exists_block_syl exps with ⟨H0, hH0_t, hH0_P, hH0_d⟩
  let e : Fin ((exps.map (fun k => 2 ^ k)).sum) ≃ Fin n := finCongr hsum_exps
  let H : Matrix I I ℝ := Matrix.reindex e e H0
  have hH_t : ∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1 := fun i j => hH0_t (e.symm i) (e.symm j)
  have hH_P : P H = ((exps.map (fun k => (2 ^ k).factorial)).prod : ℕ) := by
    change PEqualNP.Outside.L_lib_704_aux.Psq (Matrix.reindex e e H0) = _
    rw [PEqualNP.Outside.L_lib_704_aux.Psq_reindex]
    exact hH0_P
  have hH_d : H.det ^ 2 = ((exps.map (fun k => (2 ^ k) ^ (2 ^ k))).prod : ℕ) := by
    have hd : H.det = H0.det := Matrix.det_reindex_self e H0
    rw [hd]
    exact hH0_d
  refine ⟨H, hH_t, ?_, ?_, ?_⟩
  · rw [hH_P]
    have hpos : 0 < (exps.map (fun k => (2 ^ k).factorial)).prod := by
      apply List.prod_pos
      intro x hx
      rcases List.mem_map.1 hx with ⟨k, _, rfl⟩
      exact Nat.factorial_pos _
    exact_mod_cast hpos
  · rw [hH_P, hH_d]
    let d : Fin exps.length → ℕ := fun i => 2 ^ (exps[i.val]'i.isLt)
    have hd_sum : (∑ i : Fin exps.length, d i) = n := by
      have h1 : (∑ i : Fin exps.length, d i) = (exps.map (fun k => 2 ^ k)).sum := by
        rw [← List.sum_ofFn]
        congr 1
        refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
        simp [d]
      rw [h1, hsum_exps]
    have hprod_fact : (exps.map (fun k => (2 ^ k).factorial)).prod =
        ∏ i : Fin exps.length, (d i).factorial := by
      rw [← List.prod_ofFn]
      congr 1
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      simp [d]
    have hprod_pow : (exps.map (fun k => (2 ^ k) ^ (2 ^ k))).prod =
        ∏ i : Fin exps.length, (d i) ^ (d i) := by
      rw [← List.prod_ofFn]
      congr 1
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      simp [d]
    have hlen_le : exps.length ≤ Nat.log2 n + 1 := by
      have h1 := List.length_filter_le (fun k => n.testBit k) (List.range (Nat.log2 n + 1))
      simpa [exps] using h1
    have hmode := PEqualNP.Outside.L_lib_704_aux.multinomial_mode_bound d hd_sum
    have hpen_le : (n + 1) ^ exps.length ≤ penalty :=
      Nat.pow_le_pow_right (by omega) hlen_le
    have hnat : n ^ n * (exps.map (fun k => (2 ^ k).factorial)).prod ≤
        penalty * n.factorial * (exps.map (fun k => (2 ^ k) ^ (2 ^ k))).prod := by
      rw [hprod_fact, hprod_pow, mul_comm (n ^ n)]
      exact le_trans hmode
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpen_le))
    exact_mod_cast hnat
  · intro h hn2
    have hexps_eq : exps = [h] := by
      have hlog : Nat.log2 n = h := by rw [hn2]; exact PEqualNP.Outside.L_lib_704_aux.log2_two_pow h
      have hset : exps.toFinset = {h} := by
        rw [htoFinset, hlog, hn2]
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.testBit_two_pow]
        constructor
        · rintro ⟨_, hk⟩
          have : h = k := of_decide_eq_true hk
          exact this.symm
        · intro hk
          rw [hk]
          exact ⟨Nat.lt_succ_self h, by simp⟩
      have hlen1 : exps.length = 1 := by
        rw [← List.toFinset_card_of_nodup hnodup, hset, Finset.card_singleton]
      have hmem : h ∈ exps := List.mem_toFinset.1 (by rw [hset]; exact Finset.mem_singleton_self h)
      cases hlist : exps with
      | nil => simp [hlist] at hlen1
      | cons a tl =>
          simp only [hlist, List.length_cons, Nat.succ.injEq] at hlen1
          have htl : tl = [] := List.eq_nil_of_length_eq_zero hlen1
          subst htl
          rw [hlist] at hmem
          simp only [List.mem_singleton] at hmem
          rw [hmem]
    rw [hH_P, hH_d, hexps_eq]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hn2]
    push_cast
    ring
