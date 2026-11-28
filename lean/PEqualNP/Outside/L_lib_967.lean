import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_967_aux

open Classical

noncomputable section

lemma fin_add_one_val {b : ℕ} (i : Fin (b + 2)) :
    (i + 1).val = if i.val + 1 = b + 2 then 0 else i.val + 1 := by
  have hi : i.val < b + 2 := i.isLt
  have h1 : (1 : Fin (b + 2)).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  change (i.val + (1 : Fin (b + 2)).val) % (b + 2) = _
  rw [h1]
  by_cases h : i.val + 1 = b + 2
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)

lemma fin_add_one_ne_self {b : ℕ} (i : Fin (b + 2)) : i + 1 ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [fin_add_one_val] at hv
  split_ifs at hv <;> omega

lemma fin_add_one_inj {b : ℕ} : Function.Injective (fun i : Fin (b + 2) => i + 1) := by
  intro i j h
  exact add_right_cancel h

lemma rank_mul_left_of_left_inv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (L : Matrix β α ℚ) (H : Matrix α β ℚ) (M : Matrix β γ ℚ)
    (hLH : L * H = 1) :
    (H * M).rank = M.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_right H M
  · calc M.rank = (L * (H * M)).rank := by rw [← Matrix.mul_assoc, hLH, Matrix.one_mul]
      _ ≤ (H * M).rank := Matrix.rank_mul_le_right L (H * M)

lemma rank_mul_right_of_right_inv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (G : Matrix α β ℚ) (T : Matrix β γ ℚ) (R : Matrix γ β ℚ)
    (hTR : T * R = 1) :
    (G * T).rank = G.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_left G T
  · calc G.rank = ((G * T) * R).rank := by rw [Matrix.mul_assoc, hTR, Matrix.mul_one]
      _ ≤ (G * T).rank := Matrix.rank_mul_le_left (G * T) R

lemma rank_mul_right_of_unit_upper {α β : Type*} [Fintype α] [Fintype β]
    (deg : β → ℕ) (G : Matrix α β ℚ) (T : Matrix β β ℚ)
    (hdiag : ∀ s : β, T s s = 1)
    (hup : ∀ s1 s2 : β, T s1 s2 ≠ 0 → deg s1 < deg s2 ∨ s1 = s2) :
    (G * T).rank = G.rank := by
  have hinj : Function.Injective (Matrix.mulVecLin T) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hvne
    have hex : (Finset.univ.filter (fun s : β => v s ≠ 0)).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      apply hvne
      funext s
      by_contra hs
      have : s ∈ Finset.univ.filter (fun s : β => v s ≠ 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩
      rw [hem] at this
      exact Finset.notMem_empty s this
    rcases Finset.exists_max_image _ deg hex with ⟨s0, hs0_mem, hs0_max⟩
    have hs0_ne : v s0 ≠ 0 := (Finset.mem_filter.mp hs0_mem).2
    have hrow := congrFun hv s0
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
    have hterm : ∀ s : β, T s0 s * v s = if s = s0 then v s0 else 0 := by
      intro s
      by_cases heq : s = s0
      · subst heq; simp [hdiag s]
      · simp only [heq, ↓reduceIte]
        by_cases hvs : v s = 0
        · simp [hvs]
        · have hle : deg s ≤ deg s0 := hs0_max s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hvs⟩)
          have hT0 : T s0 s = 0 := by
            by_contra hTne
            rcases hup s0 s hTne with hlt | hEq
            · omega
            · exact heq hEq.symm
          simp [hT0]
    simp_rw [hterm] at hrow
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hrow
    exact hs0_ne hrow
  have hsurj : Function.Surjective (Matrix.mulVecLin T) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hr : LinearMap.range (Matrix.mulVecLin (G * T)) = LinearMap.range (Matrix.mulVecLin G) := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]
  unfold Matrix.rank
  rw [hr]

def spinF (b : ℕ) (x : Fin (b + 2) → Bool) (i : Fin (b + 2)) : ℚ :=
  if x i then 1 else -1

lemma spinF_mul_self (b : ℕ) (x : Fin (b + 2) → Bool) (i : Fin (b + 2)) :
    spinF b x i * spinF b x i = 1 := by
  unfold spinF
  cases x i <;> norm_num

def walsh (b : ℕ) : Matrix (Fin (b + 2) → Bool) (Finset (Fin (b + 2))) ℚ :=
  fun x T => ∏ j ∈ T, spinF b x j

lemma walsh_left_inv (b : ℕ) :
    (((2 : ℚ) ^ (b + 2))⁻¹ • (walsh b).transpose) * walsh b = 1 := by
  have hmul : (walsh b).transpose * walsh b = ((2 : ℚ) ^ (b + 2)) • (1 : Matrix (Finset (Fin (b + 2))) (Finset (Fin (b + 2))) ℚ) := by
    ext T1 T2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, walsh]
    have hprod : ∀ x : Fin (b + 2) → Bool,
        (∏ j ∈ T1, spinF b x j) * (∏ j ∈ T2, spinF b x j) =
        ∏ j : Fin (b + 2), if (j ∈ T1) ≠ (j ∈ T2) then spinF b x j else 1 := by
      intro x
      have h1 : (∏ j ∈ T1, spinF b x j) = ∏ j : Fin (b + 2), if j ∈ T1 then spinF b x j else 1 := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
        congr 1; ext j; simp
      have h2 : (∏ j ∈ T2, spinF b x j) = ∏ j : Fin (b + 2), if j ∈ T2 then spinF b x j else 1 := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
        congr 1; ext j; simp
      rw [h1, h2, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj1 : j ∈ T1 <;> by_cases hj2 : j ∈ T2 <;> simp [hj1, hj2, spinF_mul_self]
    simp_rw [hprod]
    have hswap : (∑ x : Fin (b + 2) → Bool, ∏ j : Fin (b + 2), if (j ∈ T1) ≠ (j ∈ T2) then spinF b x j else 1) =
        ∏ j : Fin (b + 2), ∑ c : Bool, if (j ∈ T1) ≠ (j ∈ T2) then (if c then (1 : ℚ) else -1) else 1 :=
      (Fintype.prod_sum (fun (j : Fin (b + 2)) (c : Bool) =>
        if (j ∈ T1) ≠ (j ∈ T2) then (if c then (1 : ℚ) else -1) else 1)).symm
    rw [hswap]
    by_cases hEq : T1 = T2
    · subst hEq
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, mul_one, Finset.prod_const, Fintype.card_fin]
      norm_num
    · simp only [hEq, ↓reduceIte, mul_zero]
      have hex : ∃ j : Fin (b + 2), (j ∈ T1) ≠ (j ∈ T2) := by
        by_contra hall
        push Not at hall
        apply hEq
        ext j
        exact eq_iff_iff.mp (hall j)
      rcases hex with ⟨j0, hj0⟩
      apply Finset.prod_eq_zero (Finset.mem_univ j0)
      rw [Fintype.sum_bool, if_pos hj0, if_pos hj0]
      norm_num
  rw [Matrix.smul_mul, hmul, smul_smul]
  have hne : ((2 : ℚ) ^ (b + 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [inv_mul_cancel₀ hne, one_smul]

def validC {b : ℕ} (S C : Finset (Fin (b + 2))) : Prop :=
  C ⊆ S ∧ (∀ i ∈ C, i + 1 ∈ S) ∧ (∀ i ∈ C, i + 1 ∉ C)

def pairUnion {b : ℕ} (C : Finset (Fin (b + 2))) : Finset (Fin (b + 2)) :=
  C ∪ C.image (· + 1)

lemma disjoint_pairUnion_of_validC {b : ℕ} {S C : Finset (Fin (b + 2))} (hC : validC S C) :
    Disjoint C (C.image (· + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_image.mp hx2 with ⟨i, hi, rfl⟩
  exact hC.2.2 i hi hx1

lemma pairUnion_subset_of_validC {b : ℕ} {S C : Finset (Fin (b + 2))} (hC : validC S C) :
    pairUnion C ⊆ S := by
  rw [pairUnion, Finset.union_subset_iff]
  refine ⟨hC.1, ?_⟩
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  exact hC.2.1 i hi

lemma card_pairUnion_of_validC {b : ℕ} {S C : Finset (Fin (b + 2))} (hC : validC S C) :
    (pairUnion C).card = 2 * C.card := by
  rw [pairUnion, Finset.card_union_of_disjoint (disjoint_pairUnion_of_validC hC),
      Finset.card_image_of_injective C fin_add_one_inj]
  omega

lemma card_sdiff_pairUnion_of_validC {b : ℕ} {S C : Finset (Fin (b + 2))} (hC : validC S C) :
    (S \ pairUnion C).card + 2 * C.card = S.card := by
  have h1 := Finset.card_sdiff_add_card_eq_card (pairUnion_subset_of_validC hC)
  rw [card_pairUnion_of_validC hC] at h1
  exact h1

def collFree {b : ℕ} (S U : Finset (Fin (b + 2))) : Prop :=
  U ⊆ S ∧ ∀ i ∈ U, i + 1 ∉ S \ U

def imgSet {b : ℕ} (S U : Finset (Fin (b + 2))) : Finset (Fin (b + 2)) :=
  (S \ U) ∪ U.image (· + 1)

lemma disjoint_imgSet {b : ℕ} {S U : Finset (Fin (b + 2))} (h : collFree S U) :
    Disjoint (S \ U) (U.image (· + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_image.mp hx2 with ⟨i, hi, rfl⟩
  exact h.2 i hi hx1

lemma card_imgSet {b : ℕ} {S U : Finset (Fin (b + 2))} (h : collFree S U) :
    (imgSet S U).card = S.card := by
  rw [imgSet, Finset.card_union_of_disjoint (disjoint_imgSet h),
      Finset.card_image_of_injective U fin_add_one_inj,
      Finset.card_sdiff_add_card_eq_card h.1]

def Gmat (b : ℕ) (a h : Fin (b + 2) → ℚ) (keep : ℕ → Prop) :
    Matrix (Finset (Fin (b + 2))) (Finset (Fin (b + 2))) ℚ :=
  fun T S =>
    if keep S.card then
      ∑ U ∈ S.powerset.filter (fun U => (∀ i ∈ U, i + 1 ∉ S \ U) ∧ imgSet S U = T),
        (∏ i ∈ S \ U, a i) * (∏ i ∈ U, h i)
    else 0

def Gdeg (b : ℕ) (a h : Fin (b + 2) → ℚ) (d : ℕ) :
    Matrix {T : Finset (Fin (b + 2)) // T.card = d} {S : Finset (Fin (b + 2)) // S.card = d} ℚ :=
  fun T S =>
    ∑ U ∈ S.val.powerset.filter (fun U => (∀ i ∈ U, i + 1 ∉ S.val \ U) ∧ imgSet S.val U = T.val),
      (∏ i ∈ S.val \ U, a i) * (∏ i ∈ U, h i)

def Tmat (b : ℕ) (a h : Fin (b + 2) → ℚ) (keep : ℕ → Prop) :
    Matrix (Finset (Fin (b + 2))) (Finset (Fin (b + 2))) ℚ :=
  fun S' S =>
    if keep S.card then
      ∑ C ∈ S.powerset.filter (fun C => validC S C ∧ S \ pairUnion C = S'),
        ∏ i ∈ C, (h i * a (i + 1))
    else if S' = S then 1 else 0

lemma Tmat_diag (b : ℕ) (a h : Fin (b + 2) → ℚ) (keep : ℕ → Prop) (S : Finset (Fin (b + 2))) :
    Tmat b a h keep S S = 1 := by
  unfold Tmat
  by_cases hk : keep S.card
  · simp only [hk, ↓reduceIte]
    have hfilt : S.powerset.filter (fun C => validC S C ∧ S \ pairUnion C = S) = {∅} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hC, heq⟩
        have hcard := card_sdiff_pairUnion_of_validC hC
        rw [heq] at hcard
        have hc0 : C.card = 0 := by omega
        exact Finset.card_eq_zero.mp hc0
      · rintro rfl
        refine ⟨Finset.empty_subset S, ⟨Finset.empty_subset S, by simp, by simp⟩, ?_⟩
        simp [pairUnion]
    rw [hfilt]
    simp
  · simp [hk]

lemma Tmat_upper (b : ℕ) (a h : Fin (b + 2) → ℚ) (keep : ℕ → Prop) (S' S : Finset (Fin (b + 2))) :
    Tmat b a h keep S' S ≠ 0 → S'.card < S.card ∨ S' = S := by
  unfold Tmat
  by_cases hk : keep S.card
  · simp only [hk, ↓reduceIte]
    intro hne
    have hne_f : (S.powerset.filter (fun C => validC S C ∧ S \ pairUnion C = S')).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      rw [hem, Finset.sum_empty] at hne
      exact hne rfl
    rcases hne_f with ⟨C, hCm⟩
    have hC := (Finset.mem_filter.mp hCm).2
    have hcard := card_sdiff_pairUnion_of_validC hC.1
    rw [hC.2] at hcard
    by_cases hC0 : C = ∅
    · right
      rw [← hC.2, hC0]
      simp [pairUnion]
    · left
      have hpos : 0 < C.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC0)
      omega
  · simp only [hk, ↓reduceIte]
    intro hne
    by_cases heq : S' = S
    · right; exact heq
    · simp [heq] at hne

lemma factor_F_eq_walsh_G_T (b : ℕ) (a h : Fin (b + 2) → ℚ) (cut : ℕ) (par : Bool) :
    let keep := fun d : ℕ => d ≤ cut ∧ decide (d % 2 = 1) = par
    (fun (x : Fin (b + 2) → Bool) (S : Finset (Fin (b + 2))) =>
      if keep S.card then ∏ i ∈ S, (a i * spinF b x i + h i * spinF b x (i + 1)) else 0) =
    walsh b * (Gmat b a h keep * Tmat b a h keep) := by
  intro keep
  ext x S
  by_cases hk : keep S.card
  · simp only [hk, ↓reduceIte]
    have hkeep_sub : ∀ C : Finset (Fin (b + 2)), validC S C → keep (S \ pairUnion C).card := by
      intro C hC
      have hcard := card_sdiff_pairUnion_of_validC hC
      refine ⟨by omega, ?_⟩
      have hmod : (S \ pairUnion C).card % 2 = S.card % 2 := by omega
      rw [hmod]
      exact hk.2
    have hrhs1 : (walsh b * (Gmat b a h keep * Tmat b a h keep)) x S =
        ∑ S' : Finset (Fin (b + 2)), Tmat b a h keep S' S *
          ∑ T : Finset (Fin (b + 2)), walsh b x T * Gmat b a h keep T S' := by
      simp only [Matrix.mul_apply]
      calc ∑ T : Finset (Fin (b + 2)), walsh b x T * ∑ S' : Finset (Fin (b + 2)), Gmat b a h keep T S' * Tmat b a h keep S' S
          = ∑ T : Finset (Fin (b + 2)), ∑ S' : Finset (Fin (b + 2)), Tmat b a h keep S' S * (walsh b x T * Gmat b a h keep T S') := by
            apply Finset.sum_congr rfl; intro T _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S' _; ring
        _ = ∑ S' : Finset (Fin (b + 2)), ∑ T : Finset (Fin (b + 2)), Tmat b a h keep S' S * (walsh b x T * Gmat b a h keep T S') :=
            Finset.sum_comm
        _ = ∑ S' : Finset (Fin (b + 2)), Tmat b a h keep S' S * ∑ T : Finset (Fin (b + 2)), walsh b x T * Gmat b a h keep T S' := by
            apply Finset.sum_congr rfl; intro S' _; rw [← Finset.mul_sum]
    rw [hrhs1]
    have hGsum : ∀ S' : Finset (Fin (b + 2)), keep S'.card →
        (∑ T : Finset (Fin (b + 2)), walsh b x T * Gmat b a h keep T S') =
        ∑ U' ∈ S'.powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ S' \ U'),
          ((∏ i ∈ S' \ U', a i) * (∏ i ∈ U', h i)) * walsh b x (imgSet S' U') := by
      intro S' hk'
      simp only [Gmat, hk', ↓reduceIte]
      have hfib := Finset.sum_fiberwise (s := S'.powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ S' \ U'))
        (g := fun U' => imgSet S' U')
        (f := fun U' => ((∏ i ∈ S' \ U', a i) * (∏ i ∈ U', h i)) * walsh b x (imgSet S' U'))
      rw [← hfib]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.mul_sum]
      have hfilt_eq : Finset.filter (fun U' => imgSet S' U' = T)
            (S'.powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ S' \ U')) =
          S'.powerset.filter (fun U' => (∀ i ∈ U', i + 1 ∉ S' \ U') ∧ imgSet S' U' = T) := by
        ext U'; simp [and_assoc]
      rw [hfilt_eq]
      apply Finset.sum_congr rfl
      intro U' hU'
      have himg : imgSet S' U' = T := (Finset.mem_filter.mp hU').2.2
      rw [himg]; ring
    have hTsum : (∑ S' : Finset (Fin (b + 2)), Tmat b a h keep S' S *
          ∑ T : Finset (Fin (b + 2)), walsh b x T * Gmat b a h keep T S') =
        ∑ C ∈ S.powerset.filter (fun C => validC S C),
          (∏ i ∈ C, (h i * a (i + 1))) *
            ∑ U' ∈ (S \ pairUnion C).powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ (S \ pairUnion C) \ U'),
              ((∏ i ∈ (S \ pairUnion C) \ U', a i) * (∏ i ∈ U', h i)) * walsh b x (imgSet (S \ pairUnion C) U') := by
      have hfib := Finset.sum_fiberwise (s := S.powerset.filter (fun C => validC S C))
        (g := fun C => S \ pairUnion C)
        (f := fun C => (∏ i ∈ C, (h i * a (i + 1))) *
          ∑ U' ∈ (S \ pairUnion C).powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ (S \ pairUnion C) \ U'),
            ((∏ i ∈ (S \ pairUnion C) \ U', a i) * (∏ i ∈ U', h i)) * walsh b x (imgSet (S \ pairUnion C) U'))
      rw [← hfib]
      apply Finset.sum_congr rfl
      intro S' _
      simp only [Tmat, hk, ↓reduceIte]
      have hfilt_eq : Finset.filter (fun C => S \ pairUnion C = S') (S.powerset.filter (fun C => validC S C)) =
          S.powerset.filter (fun C => validC S C ∧ S \ pairUnion C = S') := by
        ext C; simp [and_assoc]
      rw [hfilt_eq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hC
      have hCm := (Finset.mem_filter.mp hC).2
      rw [← hCm.2, hGsum (S \ pairUnion C) (hkeep_sub C hCm.1)]
    rw [hTsum]
    have hprod_exp : (∏ i ∈ S, (a i * spinF b x i + h i * spinF b x (i + 1))) =
        ∑ U ∈ S.powerset, (∏ i ∈ S \ U, (a i * spinF b x i)) * (∏ i ∈ U, (h i * spinF b x (i + 1))) := by
      have := Finset.prod_add (fun i => h i * spinF b x (i + 1)) (fun i => a i * spinF b x i) S
      have hcomm : (∏ i ∈ S, (a i * spinF b x i + h i * spinF b x (i + 1))) =
          ∏ i ∈ S, (h i * spinF b x (i + 1) + a i * spinF b x i) := by
        apply Finset.prod_congr rfl; intro i _; ring
      rw [hcomm, this]
      apply Finset.sum_congr rfl
      intro U _; ring
    rw [hprod_exp]
    have hsigma : (∑ C ∈ S.powerset.filter (fun C => validC S C),
          (∏ i ∈ C, (h i * a (i + 1))) *
            ∑ U' ∈ (S \ pairUnion C).powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ (S \ pairUnion C) \ U'),
              ((∏ i ∈ (S \ pairUnion C) \ U', a i) * (∏ i ∈ U', h i)) * walsh b x (imgSet (S \ pairUnion C) U')) =
        ∑ p ∈ (S.powerset.filter (fun C => validC S C)).sigma
          (fun C => (S \ pairUnion C).powerset.filter (fun U' => ∀ i ∈ U', i + 1 ∉ (S \ pairUnion C) \ U')),
          (∏ i ∈ p.1, (h i * a (i + 1))) *
            (((∏ i ∈ (S \ pairUnion p.1) \ p.2, a i) * (∏ i ∈ p.2, h i)) * walsh b x (imgSet (S \ pairUnion p.1) p.2)) := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro C _
      rw [Finset.mul_sum]
    rw [hsigma]
    refine Finset.sum_nbij'
      (fun U => ⟨U.filter (fun i => i + 1 ∈ S \ U), U \ U.filter (fun i => i + 1 ∈ S \ U)⟩)
      (fun p => p.2 ∪ p.1)
      ?_ ?_ ?_ ?_ ?_
    · intro U hU
      have hUS : U ⊆ S := Finset.mem_powerset.mp hU
      let C := U.filter (fun i => i + 1 ∈ S \ U)
      have hC_valid : validC S C := by
        refine ⟨Finset.Subset.trans (Finset.filter_subset _ U) hUS, ?_, ?_⟩
        · intro i hi
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).1
        · intro i hi hi1
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).2 (Finset.mem_filter.mp hi1).1
      have hU'_sub : U \ C ⊆ S \ pairUnion C := by
        intro j hj
        have hjU : j ∈ U := (Finset.mem_sdiff.mp hj).1
        have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
        rw [Finset.mem_sdiff]
        refine ⟨hUS hjU, ?_⟩
        rw [pairUnion, Finset.mem_union]
        push Not
        refine ⟨hjC, ?_⟩
        intro him
        rcases Finset.mem_image.mp him with ⟨i, hi, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).2 hjU
      have hU'_cf : ∀ i ∈ U \ C, i + 1 ∉ (S \ pairUnion C) \ (U \ C) := by
        intro i hi hi1
        have hiU : i ∈ U := (Finset.mem_sdiff.mp hi).1
        have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
        have h1S : i + 1 ∈ S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi1).1).1
        have h1notPU : i + 1 ∉ pairUnion C := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi1).1).2
        have h1notUC : i + 1 ∉ U \ C := (Finset.mem_sdiff.mp hi1).2
        have h1notU : i + 1 ∉ U := by
          intro h1U
          apply h1notUC
          exact Finset.mem_sdiff.mpr ⟨h1U, fun h1C => h1notPU (Finset.mem_union_left _ h1C)⟩
        exact hiC (Finset.mem_filter.mpr ⟨hiU, Finset.mem_sdiff.mpr ⟨h1S, h1notU⟩⟩)
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC_valid.1, hC_valid⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hU'_sub, hU'_cf⟩⟩
    · intro p hp
      rw [Finset.mem_sigma] at hp
      have hCS : p.1 ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hp.1).1
      have hU'S : p.2 ⊆ S \ pairUnion p.1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hp.2).1
      exact Finset.mem_powerset.mpr (Finset.union_subset (Finset.Subset.trans hU'S Finset.sdiff_subset) hCS)
    · intro U _
      ext j
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
      tauto
    · intro p hp
      rw [Finset.mem_sigma] at hp
      have hC_valid : validC S p.1 := (Finset.mem_filter.mp hp.1).2
      have hU'_sub : p.2 ⊆ S \ pairUnion p.1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hp.2).1
      have hU'_cf : ∀ i ∈ p.2, i + 1 ∉ (S \ pairUnion p.1) \ p.2 := (Finset.mem_filter.mp hp.2).2
      have hC_eq : (p.2 ∪ p.1).filter (fun i => i + 1 ∈ S \ (p.2 ∪ p.1)) = p.1 := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ⟨hi2 | hi1, hiS, hnot⟩
          · exfalso
            have hi_not1 : i ∉ p.1 := fun h => (Finset.mem_sdiff.mp (hU'_sub hi2)).2 (Finset.mem_union_left _ h)
            apply hU'_cf i hi2
            rw [Finset.mem_sdiff, Finset.mem_sdiff]
            refine ⟨⟨hiS, ?_⟩, fun h => hnot (Or.inl h)⟩
            rw [pairUnion, Finset.mem_union]
            rintro (h1 | h2)
            · exact hnot (Or.inr h1)
            · rcases Finset.mem_image.mp h2 with ⟨j, hj, hjEq⟩
              exact hi_not1 (fin_add_one_inj hjEq ▸ hj)
          · exact hi1
        · intro hi1
          refine ⟨Or.inr hi1, hC_valid.2.1 i hi1, ?_⟩
          rintro (h2 | h1)
          · exact (Finset.mem_sdiff.mp (hU'_sub h2)).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi1))
          · exact hC_valid.2.2 i hi1 h1
      have hU'_eq : (p.2 ∪ p.1) \ p.1 = p.2 := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h2 | h1, hnot⟩
          · exact h2
          · exact absurd h1 hnot
        · intro hi2
          exact ⟨Or.inl hi2, fun h1 => (Finset.mem_sdiff.mp (hU'_sub hi2)).2 (Finset.mem_union_left _ h1)⟩
      have hsig : ∀ (a1 a2 b1 b2 : Finset (Fin (b + 2))), a1 = a2 → b1 = b2 →
          (⟨a1, b1⟩ : (_ : Finset (Fin (b + 2))) × Finset (Fin (b + 2))) = ⟨a2, b2⟩ := by
        rintro a1 _ b1 _ rfl rfl; rfl
      exact hsig _ _ _ _ hC_eq (by rw [hC_eq]; exact hU'_eq)
    · intro U hU
      have hUS : U ⊆ S := Finset.mem_powerset.mp hU
      let C := U.filter (fun i => i + 1 ∈ S \ U)
      let S' := S \ pairUnion C
      let U' := U \ C
      have hC_sub_U : C ⊆ U := Finset.filter_subset _ U
      have hC_valid : validC S C := by
        refine ⟨Finset.Subset.trans hC_sub_U hUS, ?_, ?_⟩
        · intro i hi; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).1
        · intro i hi hi1; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).2 (Finset.mem_filter.mp hi1).1
      have hU'_sub : U' ⊆ S' := by
        intro j hj
        have hjU := (Finset.mem_sdiff.mp hj).1
        have hjC := (Finset.mem_sdiff.mp hj).2
        refine Finset.mem_sdiff.mpr ⟨hUS hjU, ?_⟩
        rw [pairUnion, Finset.mem_union]
        rintro (h1 | h2)
        · exact hjC h1
        · rcases Finset.mem_image.mp h2 with ⟨i, hi, rfl⟩
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).2).2 hjU
      have hU'_cf : collFree S' U' := by
        refine ⟨hU'_sub, fun i hi hi1 => ?_⟩
        have hiU := (Finset.mem_sdiff.mp hi).1
        have hiC := (Finset.mem_sdiff.mp hi).2
        have h1S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi1).1).1
        have h1notPU := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi1).1).2
        have h1notUC := (Finset.mem_sdiff.mp hi1).2
        have h1notU : i + 1 ∉ U := fun h1U =>
          h1notUC (Finset.mem_sdiff.mpr ⟨h1U, fun h1C => h1notPU (Finset.mem_union_left _ h1C)⟩)
        exact hiC (Finset.mem_filter.mpr ⟨hiU, Finset.mem_sdiff.mpr ⟨h1S, h1notU⟩⟩)
      have hU_split : U = U' ∪ C := (Finset.sdiff_union_of_subset hC_sub_U).symm
      have hU_disj : Disjoint U' C := Finset.sdiff_disjoint
      have hCim_sub : C.image (· + 1) ⊆ S \ U := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
        exact (Finset.mem_filter.mp hi).2
      have hSU_split : S \ U = (S' \ U') ∪ C.image (· + 1) := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_union, S', U', pairUnion]
        constructor
        · rintro ⟨hjS, hjU⟩
          by_cases hjim : j ∈ C.image (· + 1)
          · exact Or.inr hjim
          · left
            refine ⟨⟨hjS, ?_⟩, fun h => hjU h.1⟩
            rintro (h1 | h2)
            · exact hjU (hC_sub_U h1)
            · exact hjim h2
        · rintro (⟨⟨hjS, hjPU⟩, hjUC⟩ | hjim)
          · refine ⟨hjS, fun hjU => hjUC ⟨hjU, fun hjC => hjPU (Or.inl hjC)⟩⟩
          · exact Finset.mem_sdiff.mp (hCim_sub hjim)
      have hSU_disj : Disjoint (S' \ U') (C.image (· + 1)) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj1).1).2 (Finset.mem_union_right _ hj2)
      have hP1 : (∏ i ∈ U, (h i * spinF b x (i + 1))) =
          (∏ i ∈ U', h i) * (∏ i ∈ U', spinF b x (i + 1)) * ((∏ i ∈ C, h i) * (∏ i ∈ C, spinF b x (i + 1))) := by
        conv_lhs => rw [hU_split]
        rw [Finset.prod_union hU_disj, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      have hP2 : (∏ i ∈ S \ U, (a i * spinF b x i)) =
          (∏ i ∈ S' \ U', a i) * (∏ i ∈ S' \ U', spinF b x i) * ((∏ i ∈ C, a (i + 1)) * (∏ i ∈ C, spinF b x (i + 1))) := by
        conv_lhs => rw [hSU_split]
        rw [Finset.prod_union hSU_disj, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_image (fun i _ j _ h => fin_add_one_inj h),
            Finset.prod_image (fun i _ j _ h => fin_add_one_inj h)]
      have hC_spin : (∏ i ∈ C, spinF b x (i + 1)) * (∏ i ∈ C, spinF b x (i + 1)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        simp [spinF_mul_self]
      have hwalsh_eq : walsh b x (imgSet S' U') =
          (∏ i ∈ S' \ U', spinF b x i) * (∏ i ∈ U', spinF b x (i + 1)) := by
        rw [walsh, imgSet, Finset.prod_union (disjoint_imgSet hU'_cf),
            Finset.prod_image (fun i _ j _ h => fin_add_one_inj h)]
      have hC_prod : (∏ i ∈ C, (h i * a (i + 1))) = (∏ i ∈ C, h i) * (∏ i ∈ C, a (i + 1)) :=
        Finset.prod_mul_distrib
      change (∏ i ∈ S \ U, (a i * spinF b x i)) * (∏ i ∈ U, (h i * spinF b x (i + 1))) =
        (∏ i ∈ C, (h i * a (i + 1))) *
          (((∏ i ∈ S' \ U', a i) * (∏ i ∈ U', h i)) * walsh b x (imgSet S' U'))
      rw [hP1, hP2, hwalsh_eq, hC_prod]
      calc (∏ i ∈ S' \ U', a i) * (∏ i ∈ S' \ U', spinF b x i) * ((∏ i ∈ C, a (i + 1)) * (∏ i ∈ C, spinF b x (i + 1))) *
            ((∏ i ∈ U', h i) * (∏ i ∈ U', spinF b x (i + 1)) * ((∏ i ∈ C, h i) * (∏ i ∈ C, spinF b x (i + 1))))
          = ((∏ i ∈ C, h i) * (∏ i ∈ C, a (i + 1))) *
              (((∏ i ∈ S' \ U', a i) * (∏ i ∈ U', h i)) *
                ((∏ i ∈ S' \ U', spinF b x i) * (∏ i ∈ U', spinF b x (i + 1)))) *
              ((∏ i ∈ C, spinF b x (i + 1)) * (∏ i ∈ C, spinF b x (i + 1))) := by ring
        _ = (∏ i ∈ C, h i) * (∏ i ∈ C, a (i + 1)) *
              ((∏ i ∈ S' \ U', a i) * (∏ i ∈ U', h i) *
                ((∏ i ∈ S' \ U', spinF b x i) * (∏ i ∈ U', spinF b x (i + 1)))) := by rw [hC_spin, mul_one]
  · simp only [hk, ↓reduceIte]
    symm
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro T _
    have h0 : (∑ S' : Finset (Fin (b + 2)), Gmat b a h keep T S' * Tmat b a h keep S' S) = 0 := by
      apply Finset.sum_eq_zero
      intro S' _
      simp only [Tmat, hk, ↓reduceIte]
      by_cases heq : S' = S
      · subst heq; simp [Gmat, hk]
      · simp [heq]
    rw [h0, mul_zero]

lemma finrank_biSup_disjoint_support {α : Type*} [Fintype α] (deg : α → ℕ)
    (R : ℕ → Submodule ℚ (α → ℚ))
    (hsupp : ∀ d : ℕ, ∀ v ∈ R d, ∀ x : α, deg x ≠ d → v x = 0) :
    ∀ s : Finset ℕ,
      Module.finrank ℚ (⨆ d ∈ s, R d : Submodule ℚ (α → ℚ)) = ∑ d ∈ s, Module.finrank ℚ (R d) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert d0 s hd0 ih =>
    rw [Finset.sum_insert hd0]
    have hsup_eq : (⨆ d ∈ insert d0 s, R d : Submodule ℚ (α → ℚ)) = R d0 ⊔ (⨆ d ∈ s, R d) := by
      apply le_antisymm
      · refine iSup₂_le fun d hd => ?_
        rcases Finset.mem_insert.mp hd with rfl | hd'
        · exact le_sup_left
        · exact le_trans (le_biSup R hd') le_sup_right
      · exact sup_le (le_biSup R (Finset.mem_insert_self d0 s))
          (iSup₂_le fun d hd => le_biSup R (Finset.mem_insert_of_mem hd))
    rw [hsup_eq]
    have hsupp_s : ∀ v ∈ (⨆ d ∈ s, R d : Submodule ℚ (α → ℚ)), ∀ x : α, deg x ∉ s → v x = 0 := by
      intro v hv
      have hle : (⨆ d ∈ s, R d : Submodule ℚ (α → ℚ)) ≤
          { carrier := {w : α → ℚ | ∀ x : α, deg x ∉ s → w x = 0}
            zero_mem' := fun _ _ => rfl, add_mem' := fun {a b} ha hb x hx => by simp [ha x hx, hb x hx],
            smul_mem' := fun c {a} ha x hx => by simp [ha x hx] } := by
        refine iSup₂_le fun d hd => ?_
        intro w hw x hx
        exact hsupp d w hw x (fun heq => hx (heq ▸ hd))
      exact hle hv
    have hinf : R d0 ⊓ (⨆ d ∈ s, R d) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      funext x
      by_cases hdx : deg x = d0
      · exact hsupp_s v hv.2 x (fun h => hd0 (hdx ▸ h))
      · exact hsupp d0 v hv.1 x hdx
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (R d0) (⨆ d ∈ s, R d)
    rw [hinf, finrank_bot, add_zero, ih] at hmod
    exact hmod

lemma rank_Gmat_eq_sum (b : ℕ) (a h : Fin (b + 2) → ℚ) (keep : ℕ → Prop) :
    (Gmat b a h keep).rank =
      ∑ d ∈ (Finset.range (b + 3)).filter keep, (Gdeg b a h d).rank := by
  let I := Fin (b + 2)
  let R : ℕ → Submodule ℚ (Finset I → ℚ) := fun d =>
    Submodule.span ℚ {v : Finset I → ℚ | ∃ S : Finset I, S.card = d ∧ v = fun T => Gmat b a h keep T S}
  have hsupp : ∀ d : ℕ, ∀ v ∈ R d, ∀ T : Finset I, T.card ≠ d → v T = 0 := by
    intro d v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨S, hSd, rfl⟩ T hTd
      simp only [Gmat]
      split_ifs with hk
      · apply Finset.sum_eq_zero
        intro U hU
        have hU' := (Finset.mem_filter.mp hU)
        have hcf : collFree S U := ⟨Finset.mem_powerset.mp hU'.1, hU'.2.1⟩
        have hcard : T.card = d := by rw [← hU'.2.2, card_imgSet hcf, hSd]
        exact absurd hcard hTd
      · rfl
    · intro _ _; rfl
    · intro x y _ _ hx hy T hT; simp [hx T hT, hy T hT]
    · intro c x _ hx T hT; simp [hx T hT]
  have hrange_eq : LinearMap.range (Matrix.mulVecLin (Gmat b a h keep)) =
      ⨆ d ∈ (Finset.range (b + 3)).filter keep, R d := by
    have hcol : LinearMap.range (Matrix.mulVecLin (Gmat b a h keep)) =
        Submodule.span ℚ (Set.range (fun (S : Finset I) (T : Finset I) => Gmat b a h keep T S)) :=
      Matrix.range_mulVecLin (Gmat b a h keep)
    rw [hcol]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro v ⟨S, rfl⟩
      by_cases hk : keep S.card
      · have hmem_d : S.card ∈ (Finset.range (b + 3)).filter keep := by
          rw [Finset.mem_filter, Finset.mem_range]
          have hle : S.card ≤ b + 2 := by
            simpa [I, Fintype.card_fin] using Finset.card_le_univ S
          exact ⟨by omega, hk⟩
        exact le_biSup R hmem_d (Submodule.subset_span ⟨S, rfl, rfl⟩)
      · have hv0 : (fun T => Gmat b a h keep T S) = 0 := by
          funext T; simp [Gmat, hk]
        change (fun T => Gmat b a h keep T S) ∈ (⨆ d ∈ (Finset.range (b + 3)).filter keep, R d : Submodule ℚ (Finset I → ℚ))
        rw [hv0]
        exact Submodule.zero_mem _
    · refine iSup₂_le fun d _ => ?_
      rw [Submodule.span_le]
      rintro v ⟨S, _, rfl⟩
      exact Submodule.subset_span ⟨S, rfl⟩
  have hdim_d : ∀ d ∈ (Finset.range (b + 3)).filter keep,
      Module.finrank ℚ (R d) = (Gdeg b a h d).rank := by
    intro d hd
    have hk : keep d := (Finset.mem_filter.mp hd).2
    let res : (Finset I → ℚ) →ₗ[ℚ] ({T : Finset I // T.card = d} → ℚ) :=
      { toFun := fun v T => v T.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : ∀ v ∈ R d, res v = 0 → v = 0 := by
      intro v hv hrv
      funext T
      by_cases hTd : T.card = d
      · exact congrFun hrv ⟨T, hTd⟩
      · exact hsupp d v hv T hTd
    have hmap : Submodule.map res (R d) = LinearMap.range (Matrix.mulVecLin (Gdeg b a h d)) := by
      rw [Matrix.range_mulVecLin, Submodule.map_span]
      congr 1
      ext w
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨S, hSd, rfl⟩, rfl⟩
        refine ⟨⟨S, hSd⟩, ?_⟩
        funext T
        simp [res, Gmat, Gdeg, hSd, hk]
      · rintro ⟨⟨S, hSd⟩, rfl⟩
        refine ⟨fun T => Gmat b a h keep T S, ⟨S, hSd, rfl⟩, ?_⟩
        funext T
        simp [res, Gmat, Gdeg, hSd, hk]
    have hker : LinearMap.ker (res.domRestrict (R d)) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      apply Subtype.ext
      exact hinj v.val v.property hv
    have hrk := LinearMap.finrank_range_add_finrank_ker (res.domRestrict (R d))
    rw [hker, finrank_bot, add_zero] at hrk
    have hran : LinearMap.range (res.domRestrict (R d)) = Submodule.map res (R d) := by
      ext w
      simp [LinearMap.mem_range, Submodule.mem_map]
    rw [hran, hmap] at hrk
    exact hrk.symm
  unfold Matrix.rank
  rw [hrange_eq, finrank_biSup_disjoint_support Finset.card R hsupp]
  exact Finset.sum_congr rfl hdim_d

def ordEmb {b d : ℕ} (T : {S : Finset (Fin (b + 2)) // S.card = d}) : Fin d ↪o Fin (b + 2) :=
  T.val.orderEmbOfFin T.property

lemma range_ordEmb {b d : ℕ} (T : {S : Finset (Fin (b + 2)) // S.card = d}) :
    Set.range (ordEmb T) = (T.val : Set (Fin (b + 2))) :=
  Finset.range_orderEmbOfFin T.val T.property

def compound (b d : ℕ) (M : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ) :
    Matrix {T : Finset (Fin (b + 2)) // T.card = d} {S : Finset (Fin (b + 2)) // S.card = d} ℚ :=
  fun T S => (M.submatrix (ordEmb T) (ordEmb S)).det

lemma strictMono_perm_eq_one {d : ℕ} (σ : Equiv.Perm (Fin d)) (h : StrictMono σ) : σ = 1 := by
  ext k
  have hle : ∀ i : Fin d, i.val ≤ (σ i).val := by
    intro i
    rcases i with ⟨i, hi⟩
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have h1 : i ≤ (σ ⟨i, by omega⟩).val := ih (by omega)
      have h2 : (σ ⟨i, by omega⟩).val < (σ ⟨i + 1, hi⟩).val := h (by show i < i + 1; omega)
      show i + 1 ≤ (σ ⟨i + 1, hi⟩).val
      omega
  have hge : ∀ i : Fin d, (σ i).val ≤ i.val := by
    have hinv : StrictMono σ.symm := by
      intro x y hxy
      by_contra hle'
      push Not at hle'
      rcases lt_or_eq_of_le hle' with hlt | heq
      · exact not_lt_of_ge (le_of_lt hxy) (by simpa using h hlt)
      · exact ne_of_lt hxy (by simpa using (congrArg σ heq).symm)
    intro i
    have h1 : ∀ j : Fin d, j.val ≤ (σ.symm j).val := by
      intro j
      rcases j with ⟨j, hj⟩
      induction j with
      | zero => exact Nat.zero_le _
      | succ j ih =>
        have h1' : j ≤ (σ.symm ⟨j, by omega⟩).val := ih (by omega)
        have h2' : (σ.symm ⟨j, by omega⟩).val < (σ.symm ⟨j + 1, hj⟩).val := hinv (by show j < j + 1; omega)
        show j + 1 ≤ (σ.symm ⟨j + 1, hj⟩).val
        omega
    simpa using h1 (σ i)
  exact le_antisymm (hge k) (hle k)

def eShift (d : ℕ) : Fin (d + 1) ≃ {x : Fin (d + 2) // x ≠ ⟨0, by omega⟩} :=
  { toFun := fun k => ⟨⟨k.val + 1, by omega⟩, fun h => by have hv : k.val + 1 = 0 := congrArg Fin.val h; omega⟩
    invFun := fun x => ⟨x.val.val - 1, by omega⟩
    left_inv := fun k => Fin.ext (by simp)
    right_inv := fun ⟨⟨x, hx⟩, hx0⟩ => by
      have hpos : 0 < x := by
        by_contra h0
        apply hx0; exact Fin.ext (by dsimp; omega)
      exact Subtype.ext (Fin.ext (by dsimp; omega)) }

lemma eShift_val (d : ℕ) (k : Fin (d + 1)) : ((eShift d k).val).val = k.val + 1 := rfl

def cyclePerm : (d : ℕ) → Equiv.Perm (Fin d)
  | 0 => 1
  | 1 => 1
  | d + 2 =>
    Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ *
      ((cyclePerm (d + 1)).extendDomain (eShift d))

lemma cyclePerm_apply (d : ℕ) (hd : 0 < d) (k : Fin d) :
    (cyclePerm d k).val = if k.val + 1 = d then 0 else k.val + 1 := by
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero =>
      simp [cyclePerm]
    | succ d =>
      simp only [cyclePerm, Equiv.Perm.mul_apply]
      by_cases hk0 : k.val = 0
      · have hkeq : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [hkeq]
        have hext : ((cyclePerm (d + 1)).extendDomain (eShift d) ⟨0, by omega⟩) = ⟨0, by omega⟩ :=
          Equiv.Perm.extendDomain_apply_not_subtype (cyclePerm (d + 1)) (eShift d) (by simp)
        rw [hext, Equiv.swap_apply_left]
        simp
      · have hpos : 0 < k.val := by omega
        let k' : Fin (d + 1) := ⟨k.val - 1, by omega⟩
        have hkeq : k = (eShift d k').val := Fin.ext (by rw [eShift_val]; dsimp [k']; omega)
        have hext : ((cyclePerm (d + 1)).extendDomain (eShift d) k) =
            (eShift d (cyclePerm (d + 1) k')).val := by
          rw [hkeq]
          exact Equiv.Perm.extendDomain_apply_image (cyclePerm (d + 1)) (eShift d) k'
        rw [hext]
        have hih := ih (by omega) k'
        by_cases hlast : k.val + 1 = d + 2
        · have hlast' : k'.val + 1 = d + 1 := by dsimp [k']; omega
          rw [hlast'] at hih
          simp only [↓reduceIte] at hih
          have h1 : (eShift d (cyclePerm (d + 1) k')).val = ⟨1, by omega⟩ :=
            Fin.ext (by rw [eShift_val, hih])
          rw [h1, Equiv.swap_apply_right]
          simp [hlast]
        · have hlast' : k'.val + 1 ≠ d + 1 := by dsimp [k']; omega
          simp only [hlast', ↓reduceIte] at hih
          have hne0 : (eShift d (cyclePerm (d + 1) k')).val ≠ ⟨0, by omega⟩ := (eShift d _).property
          have hne1 : (eShift d (cyclePerm (d + 1) k')).val ≠ ⟨1, by omega⟩ := by
            intro h
            have hv : ((eShift d (cyclePerm (d + 1) k')).val).val = 1 := congrArg Fin.val h
            rw [eShift_val, hih] at hv
            dsimp [k'] at hv
            omega
          rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
          simp only [hlast, ↓reduceIte]
          rw [eShift_val, hih]
          dsimp [k']
          omega

lemma cyclePerm_sign (d : ℕ) (hd : 0 < d) :
    Equiv.Perm.sign (cyclePerm d) = (-1 : ℤˣ) ^ (d - 1) := by
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero => simp [cyclePerm]
    | succ d =>
      have h01 : (⟨0, by omega⟩ : Fin (d + 2)) ≠ ⟨1, by omega⟩ := by
        intro h; have hv : (0 : ℕ) = 1 := congrArg Fin.val h; omega
      simp only [cyclePerm, map_mul, Equiv.Perm.sign_swap h01, Equiv.Perm.sign_extendDomain]
      rw [ih (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [pow_succ']

lemma Gdeg_eq_compound (b : ℕ) (a h : Fin (b + 2) → ℚ) (d : ℕ) :
    let A : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ := fun j i =>
      (if j = i then a i else 0) +
      (if j = i + 1 then if i.val + 1 = b + 2 ∧ d % 2 = 0 then -(h i) else h i else 0)
    Gdeg b a h d = compound b d A := by
  intro A
  let I := Fin (b + 2)
  let h' : I → ℚ := fun i => if i.val + 1 = b + 2 ∧ d % 2 = 0 then -(h i) else h i
  have hA_eq : ∀ j i : I, A j i = if j = i then a i else if j = i + 1 then h' i else 0 := by
    intro j i
    by_cases hji : j = i
    · subst hji
      have hne : j ≠ j + 1 := (fin_add_one_ne_self j).symm
      simp [A, hne]
    · simp [A, hji, h']
  ext T S
  simp only [Gdeg, compound, Matrix.det_apply]
  let t := ordEmb T
  let s := ordEmb S
  have ht_mem : ∀ k : Fin d, t k ∈ T.val := fun k => Finset.orderEmbOfFin_mem T.val T.property k
  have hs_mem : ∀ k : Fin d, s k ∈ S.val := fun k => Finset.orderEmbOfFin_mem S.val S.property k
  have ht_surj : ∀ x ∈ T.val, ∃ k : Fin d, t k = x := by
    intro x hx
    have hrange : Set.range t = (T.val : Set I) := Finset.range_orderEmbOfFin T.val T.property
    have : x ∈ Set.range t := hrange.symm ▸ hx
    exact this
  have hs_surj : ∀ x ∈ S.val, ∃ k : Fin d, s k = x := by
    intro x hx
    have hrange : Set.range s = (S.val : Set I) := Finset.range_orderEmbOfFin S.val S.property
    have : x ∈ Set.range s := hrange.symm ▸ hx
    exact this
  let surv : Finset (Equiv.Perm (Fin d)) :=
    Finset.univ.filter (fun σ : Equiv.Perm (Fin d) => ∀ k : Fin d, t (σ k) = s k ∨ t (σ k) = s k + 1)
  have hsum_surv : (∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ • ∏ k : Fin d, (A.submatrix t s) (σ k) k) =
      ∑ σ ∈ surv, (Equiv.Perm.sign σ : ℚ) * ∏ k : Fin d, A (t (σ k)) (s k) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Equiv.Perm (Fin d) => ∀ k : Fin d, t (σ k) = s k ∨ t (σ k) = s k + 1)]
    have hzero : (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin d) =>
        ¬ ∀ k : Fin d, t (σ k) = s k ∨ t (σ k) = s k + 1),
        Equiv.Perm.sign σ • ∏ k : Fin d, (A.submatrix t s) (σ k) k) = 0 := by
      apply Finset.sum_eq_zero
      intro σ hσ
      have hnot := (Finset.mem_filter.mp hσ).2
      push Not at hnot
      rcases hnot with ⟨k0, hk1, hk2⟩
      have hp0 : (∏ k : Fin d, (A.submatrix t s) (σ k) k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ k0)
        simp only [Matrix.submatrix_apply, hA_eq, hk1, hk2, ↓reduceIte]
      rw [hp0, smul_zero]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  rw [hsum_surv]
  let okU (U : Finset I) : Prop :=
    U ⊆ S.val ∧ (∀ i ∈ U, i + 1 ∉ S.val \ U) ∧ imgSet S.val U = T.val
  have hmemU : ∀ (U : Finset I), okU U → ∀ k : Fin d, (if s k ∈ U then s k + 1 else s k) ∈ T.val := by
    intro U hU k
    rw [← hU.2.2, imgSet]
    by_cases hkU : s k ∈ U
    · simp only [hkU, ↓reduceIte]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkU)
    · simp only [hkU, ↓reduceIte]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs_mem k, hkU⟩)
  let fOfU (U : Finset I) (hU : okU U) : Fin d → Fin d := fun k =>
    (ht_surj _ (hmemU U hU k)).choose
  have hfOfU_spec : ∀ U hU k, t (fOfU U hU k) = if s k ∈ U then s k + 1 else s k := fun U hU k =>
    (ht_surj _ (hmemU U hU k)).choose_spec
  have hfOfU_inj : ∀ U hU, Function.Injective (fOfU U hU) := by
    intro U hU k1 k2 hfeq
    have h1 := hfOfU_spec U hU k1
    have h2 := hfOfU_spec U hU k2
    rw [hfeq] at h1
    have heq := h1.symm.trans h2
    by_cases hk1 : s k1 ∈ U <;> by_cases hk2 : s k2 ∈ U
    · simp only [hk1, hk2, ↓reduceIte] at heq
      exact s.injective (fin_add_one_inj heq)
    · simp only [hk1, hk2, ↓reduceIte] at heq
      exact absurd (heq ▸ Finset.mem_sdiff.mpr ⟨hs_mem k2, hk2⟩) (hU.2.1 (s k1) hk1)
    · simp only [hk1, hk2, ↓reduceIte] at heq
      exact absurd (heq.symm ▸ Finset.mem_sdiff.mpr ⟨hs_mem k1, hk1⟩) (hU.2.1 (s k2) hk2)
    · simp only [hk1, hk2, ↓reduceIte] at heq
      exact s.injective heq
  let permOfU (U : Finset I) : Equiv.Perm (Fin d) :=
    if hU : okU U then Equiv.ofBijective (fOfU U hU) (Finite.injective_iff_bijective.mp (hfOfU_inj U hU)) else 1
  have hpermOfU_spec : ∀ U (hU : okU U) k, t (permOfU U k) = if s k ∈ U then s k + 1 else s k := by
    intro U hU k
    simp only [permOfU, hU, ↓reduceDIte, Equiv.ofBijective_apply]
    exact hfOfU_spec U hU k
  symm
  refine Finset.sum_nbij'
    (fun σ => (Finset.univ.filter (fun k : Fin d => t (σ k) = s k + 1)).image s)
    permOfU
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    have hσ_ok := (Finset.mem_filter.mp hσ).2
    let U := (Finset.univ.filter (fun k : Fin d => t (σ k) = s k + 1)).image s
    have hUS : U ⊆ S.val := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
      exact hs_mem k
    have hk_mem : ∀ k : Fin d, s k ∈ U ↔ t (σ k) = s k + 1 := by
      intro k
      simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k', hk', hsk⟩; rw [s.injective hsk] at hk'; exact hk'
      · intro hk'; exact ⟨k, hk', rfl⟩
    have hcf : ∀ i ∈ U, i + 1 ∉ S.val \ U := by
      intro i hi hi1
      rcases Finset.mem_image.mp hi with ⟨k1, hk1, rfl⟩
      have h1 : t (σ k1) = s k1 + 1 := (Finset.mem_filter.mp hk1).2
      rcases hs_surj (s k1 + 1) (Finset.mem_sdiff.mp hi1).1 with ⟨k2, hk2⟩
      have hk2_notU : s k2 ∉ U := hk2.symm ▸ (Finset.mem_sdiff.mp hi1).2
      have h2 : t (σ k2) = s k2 := by
        rcases hσ_ok k2 with h | h
        · exact h
        · exact absurd ((hk_mem k2).mpr h) hk2_notU
      have hteq : t (σ k1) = t (σ k2) := by rw [h1, h2, hk2]
      have hkeq : k1 = k2 := σ.injective (t.injective hteq)
      subst hkeq
      exact fin_add_one_ne_self (s k1) hk2.symm
    have himg : imgSet S.val U = T.val := by
      ext x
      rw [imgSet, Finset.mem_union]
      constructor
      · rintro (h1 | h2)
        · rcases hs_surj x (Finset.mem_sdiff.mp h1).1 with ⟨k, rfl⟩
          have hk_notU : s k ∉ U := (Finset.mem_sdiff.mp h1).2
          have hts : t (σ k) = s k := by
            rcases hσ_ok k with h | h
            · exact h
            · exact absurd ((hk_mem k).mpr h) hk_notU
          rw [← hts]; exact ht_mem (σ k)
        · rcases Finset.mem_image.mp h2 with ⟨i, hi, rfl⟩
          rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
          have h1 : t (σ k) = s k + 1 := (Finset.mem_filter.mp hk).2
          rw [← h1]; exact ht_mem (σ k)
      · intro hx
        rcases ht_surj x hx with ⟨r, rfl⟩
        let k := σ.symm r
        have hts : t (σ k) = t r := by simp [k]
        rcases hσ_ok k with h1 | h2
        · left
          rw [← hts, h1]
          refine Finset.mem_sdiff.mpr ⟨hs_mem k, fun hkU => ?_⟩
          have h2' := (hk_mem k).mp hkU
          exact fin_add_one_ne_self (s k) (h2'.symm.trans h1)
        · right
          rw [← hts, h2]
          exact Finset.mem_image_of_mem _ ((hk_mem k).mpr h2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUS, hcf, himg⟩
  · intro U hU
    have hU' := Finset.mem_filter.mp hU
    have hcond : okU U := ⟨Finset.mem_powerset.mp hU'.1, hU'.2.1, hU'.2.2⟩
    simp only [surv, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    rw [hpermOfU_spec U hcond k]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro σ hσ
    have hσ_ok := (Finset.mem_filter.mp hσ).2
    let U := (Finset.univ.filter (fun k : Fin d => t (σ k) = s k + 1)).image s
    have hcond : okU U := by
      have hUS : U ⊆ S.val := by
        intro x hx; rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩; exact hs_mem k
      have hk_mem : ∀ k : Fin d, s k ∈ U ↔ t (σ k) = s k + 1 := by
        intro k
        simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨k', hk', hsk⟩ => s.injective hsk ▸ hk', fun hk' => ⟨k, hk', rfl⟩⟩
      refine ⟨hUS, ?_, ?_⟩
      · intro i hi hi1
        rcases Finset.mem_image.mp hi with ⟨k1, hk1, rfl⟩
        have h1 : t (σ k1) = s k1 + 1 := (Finset.mem_filter.mp hk1).2
        rcases hs_surj (s k1 + 1) (Finset.mem_sdiff.mp hi1).1 with ⟨k2, hk2⟩
        have hk2_notU : s k2 ∉ U := hk2.symm ▸ (Finset.mem_sdiff.mp hi1).2
        have h2 : t (σ k2) = s k2 := by
          rcases hσ_ok k2 with h | h
          · exact h
          · exact absurd ((hk_mem k2).mpr h) hk2_notU
        have hkeq : k1 = k2 := σ.injective (t.injective (h1.trans (hk2.symm.trans h2.symm)))
        subst hkeq; exact fin_add_one_ne_self (s k1) hk2.symm
      · ext x
        rw [imgSet, Finset.mem_union]
        constructor
        · rintro (h1 | h2)
          · rcases hs_surj x (Finset.mem_sdiff.mp h1).1 with ⟨k, rfl⟩
            have hts : t (σ k) = s k := by
              rcases hσ_ok k with h | h
              · exact h
              · exact absurd ((hk_mem k).mpr h) (Finset.mem_sdiff.mp h1).2
            rw [← hts]; exact ht_mem (σ k)
          · rcases Finset.mem_image.mp h2 with ⟨i, hi, rfl⟩
            rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
            rw [← (Finset.mem_filter.mp hk).2]; exact ht_mem (σ k)
        · intro hx
          rcases ht_surj x hx with ⟨r, rfl⟩
          let k := σ.symm r
          have hts : t (σ k) = t r := by simp [k]
          rcases hσ_ok k with h1 | h2
          · left; rw [← hts, h1]
            exact Finset.mem_sdiff.mpr ⟨hs_mem k, fun hkU => fin_add_one_ne_self (s k) (((hk_mem k).mp hkU).symm.trans h1)⟩
          · right; rw [← hts, h2]; exact Finset.mem_image_of_mem _ ((hk_mem k).mpr h2)
    ext k
    apply congrArg Fin.val
    apply t.injective
    change t (permOfU U k) = t (σ k)
    rw [hpermOfU_spec U hcond k]
    by_cases hkU : s k ∈ U
    · simp only [hkU, ↓reduceIte]
      rcases Finset.mem_image.mp hkU with ⟨k', hk', hsk⟩
      rw [← s.injective hsk]
      exact ((Finset.mem_filter.mp hk').2).symm
    · simp only [hkU, ↓reduceIte]
      rcases hσ_ok k with h | h
      · exact h.symm
      · exfalso; exact hkU (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩))
  · intro U hU
    have hU' := Finset.mem_filter.mp hU
    have hcond : okU U := ⟨Finset.mem_powerset.mp hU'.1, hU'.2.1, hU'.2.2⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hpermOfU_spec U hcond k] at hk
      by_cases hkU : s k ∈ U
      · exact hkU
      · simp only [hkU, ↓reduceIte] at hk
        exact absurd hk.symm (fin_add_one_ne_self (s k))
    · intro hxU
      rcases hs_surj x (hcond.1 hxU) with ⟨k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      rw [hpermOfU_spec U hcond k]
      simp [hxU]
  · intro σ hσ
    have hσ_ok := (Finset.mem_filter.mp hσ).2
    let U := (Finset.univ.filter (fun k : Fin d => t (σ k) = s k + 1)).image s
    have hUS : U ⊆ S.val := by
      intro x hx; rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩; exact hs_mem k
    have hk_mem : ∀ k : Fin d, s k ∈ U ↔ t (σ k) = s k + 1 := by
      intro k
      simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨k', hk', hsk⟩ => s.injective hsk ▸ hk', fun hk' => ⟨k, hk', rfl⟩⟩
    have hts_eq : ∀ k : Fin d, t (σ k) = if s k ∈ U then s k + 1 else s k := by
      intro k
      by_cases hkU : s k ∈ U
      · simp only [hkU, ↓reduceIte]; exact (hk_mem k).mp hkU
      · simp only [hkU, ↓reduceIte]
        rcases hσ_ok k with h | h
        · exact h
        · exact absurd ((hk_mem k).mpr h) hkU
    have hprod_A : (∏ k : Fin d, A (t (σ k)) (s k)) =
        (∏ i ∈ S.val \ U, a i) * (∏ i ∈ U, h' i) := by
      have hpt : ∀ k : Fin d, A (t (σ k)) (s k) = if s k ∈ U then h' (s k) else a (s k) := by
        intro k
        rw [hA_eq, hts_eq k]
        by_cases hkU : s k ∈ U
        · simp only [hkU, ↓reduceIte]
          rw [if_neg (fin_add_one_ne_self (s k))]
        · simp [hkU]
      simp_rw [hpt, Finset.prod_ite]
      have h1 : (∏ k ∈ Finset.univ.filter (fun k : Fin d => s k ∈ U), h' (s k)) = ∏ i ∈ U, h' i := by
        rw [← Finset.prod_image (fun k1 _ k2 _ h => s.injective h)]
        congr 1
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨k, hk, hkx⟩ => hkx ▸ hk, fun hx => by rcases hs_surj x (hUS hx) with ⟨k, rfl⟩; exact ⟨k, hx, rfl⟩⟩
      have h2 : (∏ k ∈ Finset.univ.filter (fun k : Fin d => s k ∉ U), a (s k)) = ∏ i ∈ S.val \ U, a i := by
        rw [← Finset.prod_image (fun k1 _ k2 _ h => s.injective h)]
        congr 1
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        exact ⟨fun ⟨k, hk, hkx⟩ => hkx ▸ ⟨hs_mem k, hk⟩,
          fun ⟨hxS, hxU⟩ => by rcases hs_surj x hxS with ⟨k, rfl⟩; exact ⟨k, hxU, rfl⟩⟩
      rw [h1, h2, mul_comm]
    change (Equiv.Perm.sign σ : ℚ) * (∏ k : Fin d, A (t (σ k)) (s k)) =
      (∏ i ∈ S.val \ U, a i) * (∏ i ∈ U, h i)
    rw [hprod_A]
    let lastI : I := ⟨b + 1, by omega⟩
    by_cases hlast : lastI ∈ U
    · have hd_pos : 0 < d := by
        rcases hs_surj lastI (hUS hlast) with ⟨k0, _⟩
        exact Nat.pos_of_ne_zero (fun hd0 => by subst hd0; exact Fin.elim0 k0)
      have hs_last : s ⟨d - 1, by omega⟩ = lastI := by
        rcases hs_surj lastI (hUS hlast) with ⟨k0, hk0⟩
        have hle : k0 ≤ ⟨d - 1, by omega⟩ := by
          show k0.val ≤ d - 1; omega
        have h1 : lastI ≤ s ⟨d - 1, by omega⟩ := hk0 ▸ s.monotone hle
        have h2 : s ⟨d - 1, by omega⟩ ≤ lastI := by
          show (s ⟨d - 1, by omega⟩).val ≤ b + 1; omega
        exact le_antisymm h2 h1
      have hσ_eq : σ = cyclePerm d := by
        have hσ_last : σ ⟨d - 1, by omega⟩ = ⟨0, hd_pos⟩ := by
          have ht0 : t (σ ⟨d - 1, by omega⟩) = ⟨0, by omega⟩ := by
            rw [hts_eq, hs_last]
            simp only [hlast, ↓reduceIte]
            apply Fin.ext
            rw [fin_add_one_val]
            simp [lastI]
          by_contra hne
          have hlt : (⟨0, hd_pos⟩ : Fin d) < σ ⟨d - 1, by omega⟩ := by
            show 0 < (σ ⟨d - 1, by omega⟩).val
            have : (σ ⟨d - 1, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
            omega
          have htlt : t ⟨0, hd_pos⟩ < t (σ ⟨d - 1, by omega⟩) := t.strictMono hlt
          rw [ht0] at htlt
          have : (t ⟨0, hd_pos⟩).val < 0 := htlt
          omega
        have hmono : ∀ k1 k2 : Fin d, k1 < k2 → k2.val < d - 1 → σ k1 < σ k2 := by
          intro k1 k2 h12 hk2_lt
          have hs2_lt : s k2 < lastI := by
            rw [← hs_last]
            exact s.strictMono (by show k2.val < d - 1; omega)
          have hs1_lt : s k1 < s k2 := s.strictMono h12
          have hv1 : (t (σ k1)).val ≤ (s k1).val + 1 := by
            rw [hts_eq k1]
            by_cases hk1U : s k1 ∈ U
            · simp only [hk1U, ↓reduceIte, fin_add_one_val]
              split_ifs <;> omega
            · simp [hk1U]
          have hv2 : (s k2).val ≤ (t (σ k2)).val := by
            rw [hts_eq k2]
            by_cases hk2U : s k2 ∈ U
            · simp only [hk2U, ↓reduceIte, fin_add_one_val]
              have hlt_end : (s k2).val < b + 1 := hs2_lt
              split_ifs <;> omega
            · simp [hk2U]
          have htle : (t (σ k1)).val ≤ (t (σ k2)).val := by
            have : (s k1).val < (s k2).val := hs1_lt
            omega
          have htne : t (σ k1) ≠ t (σ k2) := fun h => ne_of_lt h12 (σ.injective (t.injective h))
          have htlt : t (σ k1) < t (σ k2) := lt_of_le_of_ne htle htne
          exact (t.lt_iff_lt).mp htlt
        have hσ_val : ∀ k : Fin d, k.val < d - 1 → (σ k).val = k.val + 1 := by
          have hge : ∀ j : ℕ, ∀ hj : j < d - 1, j + 1 ≤ (σ ⟨j, by omega⟩).val := by
            intro j
            induction j with
            | zero =>
              intro hj
              have hne0 : σ ⟨0, by omega⟩ ≠ ⟨0, hd_pos⟩ := by
                intro heq
                have := σ.injective (heq.trans hσ_last.symm)
                have hv := congrArg Fin.val this; dsimp at hv; omega
              have : (σ ⟨0, by omega⟩).val ≠ 0 := fun h => hne0 (Fin.ext h)
              omega
            | succ j ih =>
              intro hj
              have h1 := ih (by omega)
              have h2 : (σ ⟨j, by omega⟩).val < (σ ⟨j + 1, by omega⟩).val :=
                hmono ⟨j, by omega⟩ ⟨j + 1, by omega⟩ (by show j < j + 1; omega) hj
              omega
          have hle : ∀ j : ℕ, ∀ hj : j < d - 1, (σ ⟨j, by omega⟩).val ≤ j + 1 := by
            intro j hj
            have hstep : ∀ r : ℕ, r ≤ (d - 2) - j → (σ ⟨d - 2 - r, by omega⟩).val ≤ (d - 1) - r := by
              intro r
              induction r with
              | zero =>
                intro _
                have : (σ ⟨d - 2, by omega⟩).val < d := (σ ⟨d - 2, by omega⟩).isLt
                omega
              | succ r ih =>
                intro hr
                have h1 := ih (by omega)
                have h2 : (σ ⟨d - 2 - (r + 1), by omega⟩).val < (σ ⟨d - 2 - r, by omega⟩).val :=
                  hmono ⟨d - 2 - (r + 1), by omega⟩ ⟨d - 2 - r, by omega⟩
                    (by show d - 2 - (r + 1) < d - 2 - r; omega) (by show d - 2 - r < d - 1; omega)
                omega
            have := hstep ((d - 2) - j) (le_refl _)
            have heq1 : (⟨d - 2 - (d - 2 - j), by omega⟩ : Fin d) = ⟨j, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [heq1] at this
            omega
          intro k hk
          exact le_antisymm (hle k.val hk) (hge k.val hk)
        ext k
        rw [cyclePerm_apply d hd_pos k]
        by_cases hkl : k.val + 1 = d
        · have hkeq : k = ⟨d - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hkeq, hσ_last]
          have h1 : d - 1 + 1 = d := by omega
          simp [h1]
        · simp only [hkl, ↓reduceIte]
          exact hσ_val k (by omega)
      rw [hσ_eq, cyclePerm_sign d hd_pos]
      have hprod_h' : (∏ i ∈ U, h' i) = (if d % 2 = 0 then (-1 : ℚ) else 1) * (∏ i ∈ U, h i) := by
        rw [← Finset.mul_prod_erase U h' hlast, ← Finset.mul_prod_erase U h hlast]
        have hrest : (∏ i ∈ U.erase lastI, h' i) = ∏ i ∈ U.erase lastI, h i := by
          apply Finset.prod_congr rfl
          intro i hi
          have hne : i ≠ lastI := (Finset.mem_erase.mp hi).1
          have hvne : i.val + 1 ≠ b + 2 := by
            intro h1; apply hne; apply Fin.ext; dsimp [lastI]; omega
          simp only [h']
          rw [if_neg (fun h => hvne h.1)]
        rw [hrest]
        have hlast_val : h' lastI = (if d % 2 = 0 then (-1 : ℚ) else 1) * h lastI := by
          simp only [h', lastI]
          by_cases hev : d % 2 = 0 <;> simp [hev]
        rw [hlast_val]; ring
      rw [hprod_h']
      have hsign_cancel : ((((-1 : ℤˣ) ^ (d - 1) : ℤˣ) : ℚ)) * (if d % 2 = 0 then (-1 : ℚ) else 1) = 1 := by
        have hcoe : ((((-1 : ℤˣ) ^ (d - 1) : ℤˣ) : ℚ)) = (-1 : ℚ) ^ (d - 1) := by
          push_cast; rfl
        rw [hcoe]
        by_cases hev : d % 2 = 0
        · simp only [hev, ↓reduceIte]
          have hodd : Odd (d - 1) := ⟨d / 2 - 1, by omega⟩
          rw [hodd.neg_one_pow]; norm_num
        · simp only [hev, ↓reduceIte]
          have heven : Even (d - 1) := ⟨d / 2, by omega⟩
          rw [heven.neg_one_pow]; norm_num
      calc ((((-1 : ℤˣ) ^ (d - 1) : ℤˣ) : ℚ)) * ((∏ i ∈ S.val \ U, a i) * ((if d % 2 = 0 then (-1 : ℚ) else 1) * ∏ i ∈ U, h i))
          = ((((-1 : ℤˣ) ^ (d - 1) : ℤˣ) : ℚ)) * (if d % 2 = 0 then (-1 : ℚ) else 1) * ((∏ i ∈ S.val \ U, a i) * ∏ i ∈ U, h i) := by ring
        _ = (∏ i ∈ S.val \ U, a i) * ∏ i ∈ U, h i := by rw [hsign_cancel, one_mul]
    · have hmono : StrictMono σ := by
        intro k1 k2 h12
        have hs1_lt : s k1 < s k2 := s.strictMono h12
        have hv1 : (t (σ k1)).val ≤ (s k1).val + 1 := by
          rw [hts_eq k1]
          by_cases hk1U : s k1 ∈ U
          · simp only [hk1U, ↓reduceIte, fin_add_one_val]
            split_ifs <;> omega
          · simp [hk1U]
        have hv2 : (s k2).val ≤ (t (σ k2)).val := by
          rw [hts_eq k2]
          by_cases hk2U : s k2 ∈ U
          · simp only [hk2U, ↓reduceIte, fin_add_one_val]
            have hne_end : (s k2).val + 1 ≠ b + 2 := by
              intro h1; apply hlast
              have heq : s k2 = lastI := Fin.ext (by dsimp [lastI]; omega)
              exact heq ▸ hk2U
            split_ifs <;> omega
          · simp [hk2U]
        have htle : (t (σ k1)).val ≤ (t (σ k2)).val := by
          have : (s k1).val < (s k2).val := hs1_lt
          omega
        have htne : t (σ k1) ≠ t (σ k2) := fun h => ne_of_lt h12 (σ.injective (t.injective h))
        exact (t.lt_iff_lt).mp (lt_of_le_of_ne htle htne)
      have hσ1 : σ = 1 := strictMono_perm_eq_one σ hmono
      rw [hσ1, map_one]
      have hprod_h' : (∏ i ∈ U, h' i) = ∏ i ∈ U, h i := by
        apply Finset.prod_congr rfl
        intro i hi
        have hvne : i.val + 1 ≠ b + 2 := by
          intro h1; apply hlast
          have heq : i = lastI := Fin.ext (by dsimp [lastI]; omega)
          exact heq ▸ hi
        simp only [h']
        rw [if_neg (fun h => hvne h.1)]
      rw [hprod_h']
      norm_num

lemma compound_one (b d : ℕ) :
    compound b d (1 : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ) = 1 := by
  ext T S
  simp only [compound, Matrix.one_apply]
  by_cases hTS : T = S
  · subst hTS
    simp only [↓reduceIte]
    have hsub : (1 : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ).submatrix (ordEmb T) (ordEmb T) = 1 := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.one_apply, (ordEmb T).injective.eq_iff]
    rw [hsub, Matrix.det_one]
  · simp only [hTS, ↓reduceIte]
    have hne_val : T.val ≠ S.val := fun h => hTS (Subtype.ext h)
    have hnot_sub : ¬ T.val ⊆ S.val := by
      intro hsub
      exact hne_val (Finset.eq_of_subset_of_card_le hsub (by rw [T.property, S.property]))
    rw [Finset.not_subset] at hnot_sub
    rcases hnot_sub with ⟨x, hxT, hxS⟩
    have hrange : Set.range (ordEmb T) = (T.val : Set (Fin (b + 2))) :=
      Finset.range_orderEmbOfFin T.val T.property
    have hxmem : x ∈ Set.range (ordEmb T) := hrange.symm ▸ hxT
    rcases hxmem with ⟨i0, hi0⟩
    apply Matrix.det_eq_zero_of_row_eq_zero i0
    intro j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, hi0]
    have hjS : ordEmb S j ∈ S.val := Finset.orderEmbOfFin_mem S.val S.property j
    have hne : x ≠ ordEmb S j := fun h => hxS (h ▸ hjS)
    simp [hne]

lemma compound_mul (b d : ℕ) (M N : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ) :
    compound b d (M * N) = compound b d M * compound b d N := by
  ext T S
  simp only [compound, Matrix.mul_apply, Matrix.det_apply]
  let t := ordEmb T
  let s := ordEmb S
  have hlhs : (∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ • ∏ j : Fin d, ∑ k : Fin (b + 2), M (t (σ j)) k * N k (s j)) =
      ∑ f : Fin d → Fin (b + 2), (∏ j : Fin d, N (f j) (s j)) * (M.submatrix t f).det := by
    have h1 : ∀ σ : Equiv.Perm (Fin d),
        Equiv.Perm.sign σ • (∏ j : Fin d, ∑ k : Fin (b + 2), M (t (σ j)) k * N k (s j)) =
        ∑ f : Fin d → Fin (b + 2),
          (∏ j : Fin d, N (f j) (s j)) * (Equiv.Perm.sign σ • ∏ j : Fin d, M (t (σ j)) (f j)) := by
      intro σ
      rw [Fintype.prod_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.prod_mul_distrib]
      simp only [Units.smul_def, zsmul_eq_mul]
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [← Finset.mul_sum, Matrix.det_apply]
    rfl
  change (∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ • ∏ j : Fin d, ∑ k : Fin (b + 2), M (t (σ j)) k * N k (s j)) = _
  rw [hlhs]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Fin d → Fin (b + 2) => Function.Injective f)]
  have hnoninj : (∑ f ∈ Finset.univ.filter (fun f : Fin d → Fin (b + 2) => ¬ Function.Injective f),
      (∏ j : Fin d, N (f j) (s j)) * (M.submatrix t f).det) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    have hni := (Finset.mem_filter.mp hf).2
    unfold Function.Injective at hni
    push Not at hni
    rcases hni with ⟨j1, j2, hfeq, hjne⟩
    have hdet0 : (M.submatrix t f).det = 0 := by
      apply Matrix.det_zero_of_column_eq hjne
      intro i
      simp [Matrix.submatrix_apply, hfeq]
    rw [hdet0, mul_zero]
  rw [hnoninj, add_zero]
  have hrhs : (∑ K : {U : Finset (Fin (b + 2)) // U.card = d},
        (∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ • ∏ i : Fin d, (M.submatrix t (ordEmb K)) (σ i) i) *
        (∑ τ : Equiv.Perm (Fin d), Equiv.Perm.sign τ • ∏ j : Fin d, (N.submatrix (ordEmb K) s) (τ j) j)) =
      ∑ p : {U : Finset (Fin (b + 2)) // U.card = d} × Equiv.Perm (Fin d),
        (∏ j : Fin d, N (ordEmb p.1 (p.2 j)) (s j)) *
          (Equiv.Perm.sign p.2 • (M.submatrix t (ordEmb p.1)).det) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro K _
    rw [← Matrix.det_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    simp only [Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    ring
  rw [hrhs]
  let KOfF (f : Fin d → Fin (b + 2)) (hf : Function.Injective f) :
      {U : Finset (Fin (b + 2)) // U.card = d} :=
    ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]⟩
  have hmemF : ∀ (f : Fin d → Fin (b + 2)) (hf : Function.Injective f) (j : Fin d),
      f j ∈ Set.range (ordEmb (KOfF f hf)) := by
    intro f hf j
    rw [range_ordEmb]
    exact Finset.mem_image_of_mem f (Finset.mem_univ j)
  let gOfF (f : Fin d → Fin (b + 2)) (hf : Function.Injective f) : Fin d → Fin d :=
    fun j => (hmemF f hf j).choose
  have hgOfF_spec : ∀ f hf j, ordEmb (KOfF f hf) (gOfF f hf j) = f j :=
    fun f hf j => (hmemF f hf j).choose_spec
  have hgOfF_inj : ∀ f hf, Function.Injective (gOfF f hf) := by
    intro f hf j1 j2 hgeq
    have h1 := hgOfF_spec f hf j1
    have h2 := hgOfF_spec f hf j2
    rw [hgeq] at h1
    exact hf (h1.symm.trans h2)
  let permOfF (f : Fin d → Fin (b + 2)) (hf : Function.Injective f) : Equiv.Perm (Fin d) :=
    Equiv.ofBijective (gOfF f hf) (Finite.injective_iff_bijective.mp (hgOfF_inj f hf))
  have hpermOfF_spec : ∀ f hf j, ordEmb (KOfF f hf) (permOfF f hf j) = f j :=
    fun f hf j => hgOfF_spec f hf j
  refine Finset.sum_nbij'
    (fun f => if hf : Function.Injective f then (KOfF f hf, permOfF f hf) else (T, 1))
    (fun p => fun j => ordEmb p.1 (p.2 j))
    ?_ ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro p _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ordEmb p.1).injective.comp p.2.injective⟩
  · intro f hf
    have hfinj : Function.Injective f := (Finset.mem_filter.mp hf).2
    simp only [hfinj, ↓reduceDIte]
    funext j
    exact hpermOfF_spec f hfinj j
  · intro p _
    rcases p with ⟨K, τ⟩
    have hfinj : Function.Injective (fun j => ordEmb K (τ j)) := (ordEmb K).injective.comp τ.injective
    simp only [hfinj, ↓reduceDIte]
    have hKeq : KOfF (fun j => ordEmb K (τ j)) hfinj = K := by
      apply Subtype.ext
      ext x
      simp only [KOfF, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩; exact Finset.orderEmbOfFin_mem K.val K.property (τ j)
      · intro hx
        have hr : x ∈ Set.range (ordEmb K) := by rw [range_ordEmb]; exact hx
        rcases hr with ⟨r, rfl⟩
        exact ⟨τ.symm r, by simp⟩
    apply Prod.ext hKeq
    ext j
    apply congrArg Fin.val
    apply (ordEmb K).injective
    have hspec := hpermOfF_spec (fun j => ordEmb K (τ j)) hfinj j
    have hord_eq : ordEmb (KOfF (fun j => ordEmb K (τ j)) hfinj) = ordEmb K := by
      rw [hKeq]
    rw [hord_eq] at hspec
    exact hspec
  · intro f hf
    have hfinj : Function.Injective f := (Finset.mem_filter.mp hf).2
    simp only [hfinj, ↓reduceDIte]
    let K := KOfF f hfinj
    let τ := permOfF f hfinj
    have hfeq : f = fun j => ordEmb K (τ j) := by
      funext j
      exact (hpermOfF_spec f hfinj j).symm
    have hdet_perm : (M.submatrix t f).det = Equiv.Perm.sign τ • (M.submatrix t (ordEmb K)).det := by
      have hsub : M.submatrix t f = (M.submatrix t (ordEmb K)).submatrix id τ := by
        ext i j; simp [Matrix.submatrix_apply, hfeq]
      rw [hsub, ← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]
      simp [Units.smul_def, zsmul_eq_mul]
    have hprod_eq : (∏ j : Fin d, N (f j) (s j)) = ∏ j : Fin d, N (ordEmb K (τ j)) (s j) := by
      apply Finset.prod_congr rfl; intro j _; rw [hfeq]
    rw [hdet_perm, hprod_eq]

lemma basis_equivFun_symm_single {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V] (b : Module.Basis ι ℚ V) (i : ι) :
    b.equivFun.symm (Pi.single i 1) = b i := by
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  simp [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]

def diagR (b r : ℕ) : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ :=
  Matrix.diagonal (fun i : Fin (b + 2) => if i.val < r then (1 : ℚ) else 0)

lemma matrix_rank_normal_form (b : ℕ) (M : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ) :
    ∃ (U U' V V' : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ),
      U * U' = 1 ∧ U' * U = 1 ∧ V * V' = 1 ∧ V' * V = 1 ∧
      M = U * diagR b M.rank * V := by
  let n := b + 2
  let I := Fin n
  let f := M.mulVecLin
  let r := M.rank
  let R := LinearMap.range f
  let K := LinearMap.ker f
  have hr_eq : Module.finrank ℚ R = r := rfl
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hfinI : Module.finrank ℚ (I → ℚ) = n := by simp [I]
  rw [hfinI] at hrk
  have hrk' : r + Module.finrank ℚ K = n := hrk
  have hr_le : r ≤ n := by omega
  have hK_dim : Module.finrank ℚ K = n - r := by omega
  rcases Submodule.exists_isCompl K with ⟨C, hKC⟩
  rcases Submodule.exists_isCompl R with ⟨R', hRR'⟩
  have hC_dim : Module.finrank ℚ C = r := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K C
    rw [hKC.sup_eq_top, hKC.inf_eq_bot, finrank_top, finrank_bot, add_zero, hfinI] at h1
    omega
  have hR'_dim : Module.finrank ℚ R' = n - r := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq R R'
    rw [hRR'.sup_eq_top, hRR'.inf_eq_bot, finrank_top, finrank_bot, add_zero, hfinI] at h1
    omega
  let bC : Module.Basis (Fin r) ℚ C := (Module.finBasis ℚ C).reindex (finCongr hC_dim)
  let bK : Module.Basis (Fin (n - r)) ℚ K := (Module.finBasis ℚ K).reindex (finCongr hK_dim)
  let bR' : Module.Basis (Fin (n - r)) ℚ R' := (Module.finBasis ℚ R').reindex (finCongr hR'_dim)
  let fC_lin : C →ₗ[ℚ] R :=
    { toFun := fun c => ⟨f c.val, ⟨c.val, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add f a.val b.val)
      map_smul' := fun s a => Subtype.ext (map_smul f s a.val) }
  let fC : C ≃ₗ[ℚ] R :=
    LinearEquiv.ofBijective fC_lin
      ⟨fun a b hab => by
          have hsub : f (a.val - b.val) = 0 := by
            rw [map_sub, sub_eq_zero]
            exact congrArg Subtype.val hab
          have hmemK : a.val - b.val ∈ K := hsub
          have hmemC : a.val - b.val ∈ C := C.sub_mem a.property b.property
          have hbot : a.val - b.val ∈ (⊥ : Submodule ℚ (I → ℚ)) := hKC.inf_eq_bot ▸ ⟨hmemK, hmemC⟩
          rw [Submodule.mem_bot, sub_eq_zero] at hbot
          exact Subtype.ext hbot,
       fun ⟨y, x, hx⟩ => by
          have htop : x ∈ K ⊔ C := hKC.sup_eq_top ▸ Submodule.mem_top
          rcases Submodule.mem_sup.mp htop with ⟨xk, hxk, xc, hxc, rfl⟩
          refine ⟨⟨xc, hxc⟩, Subtype.ext ?_⟩
          change f xc = y
          rw [← hx, map_add, LinearMap.mem_ker.mp hxk, zero_add]⟩
  let bR : Module.Basis (Fin r) ℚ R := bC.map fC
  let eSplit : Fin r ⊕ Fin (n - r) ≃ I :=
    { toFun := fun s => match s with
        | Sum.inl i => ⟨i.val, by omega⟩
        | Sum.inr j => ⟨r + j.val, by omega⟩
      invFun := fun i => if hi : i.val < r then Sum.inl ⟨i.val, hi⟩ else Sum.inr ⟨i.val - r, by omega⟩
      left_inv := by
        rintro (i | j)
        · simp [i.isLt]
        · have hnot : ¬ r + j.val < r := by omega
          simp [hnot]
      right_inv := by
        intro i
        by_cases hi : i.val < r
        · simp [hi]
        · simp only [hi, ↓reduceDIte]
          apply Fin.ext; dsimp; omega }
  let eqDom : (I → ℚ) ≃ₗ[ℚ] (I → ℚ) :=
    let bDomSum : Module.Basis (Fin r ⊕ Fin (n - r)) ℚ (I → ℚ) :=
      (bC.prod bK).map (Submodule.prodEquivOfIsCompl C K hKC.symm)
    let bDom : Module.Basis I ℚ (I → ℚ) := bDomSum.reindex eSplit
    bDom.equivFun.symm
  let eqCod : (I → ℚ) ≃ₗ[ℚ] (I → ℚ) :=
    let bCodSum : Module.Basis (Fin r ⊕ Fin (n - r)) ℚ (I → ℚ) :=
      (bR.prod bR').map (Submodule.prodEquivOfIsCompl R R' hRR')
    let bCod : Module.Basis I ℚ (I → ℚ) := bCodSum.reindex eSplit
    bCod.equivFun.symm
  have hdom_apply : ∀ i : I,
      eqDom (Pi.single i 1) =
        if hi : i.val < r then (bC ⟨i.val, hi⟩).val else (bK ⟨i.val - r, by omega⟩).val := by
    intro i
    change (((bC.prod bK).map (Submodule.prodEquivOfIsCompl C K hKC.symm)).reindex eSplit).equivFun.symm
      (Pi.single i 1) = _
    rw [basis_equivFun_symm_single]
    simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, eSplit]
    by_cases hi : i.val < r
    · simp [hi]
    · simp [hi]
  have hcod_apply : ∀ i : I,
      eqCod (Pi.single i 1) =
        if hi : i.val < r then f (bC ⟨i.val, hi⟩).val else (bR' ⟨i.val - r, by omega⟩).val := by
    intro i
    change (((bR.prod bR').map (Submodule.prodEquivOfIsCompl R R' hRR')).reindex eSplit).equivFun.symm
      (Pi.single i 1) = _
    rw [basis_equivFun_symm_single]
    simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, eSplit]
    by_cases hi : i.val < r
    · simp [hi, bR, fC, fC_lin]; rfl
    · simp [hi]
  have hcomm_single : ∀ i : I,
      (eqCod.toLinearMap.comp (diagR b r).mulVecLin) (Pi.single i 1) =
        (f.comp eqDom.toLinearMap) (Pi.single i 1) := by
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hdom_apply i]
    have hdiag_single : (diagR b r).mulVecLin (Pi.single i 1) =
        if i.val < r then Pi.single i (1 : ℚ) else 0 := by
      funext j
      simp only [Matrix.mulVecLin_apply, diagR, Matrix.mulVec_diagonal]
      by_cases hji : j = i
      · subst hji; by_cases hi : j.val < r <;> simp [hi, Pi.single_eq_same]
      · by_cases hi : i.val < r <;> simp [hi, Pi.single_eq_of_ne hji]
    rw [hdiag_single]
    by_cases hi : i.val < r
    · simp only [hi, ↓reduceIte, ↓reduceDIte]
      rw [hcod_apply i]
      simp [hi]
    · simp only [hi, ↓reduceIte, ↓reduceDIte, map_zero]
      exact (LinearMap.mem_ker.mp (bK ⟨i.val - r, by omega⟩).property).symm
  have hcomm : eqCod.toLinearMap.comp (diagR b r).mulVecLin = f.comp eqDom.toLinearMap := by
    apply LinearMap.ext
    intro v
    have hv : v = ∑ i : I, v i • Pi.single i (1 : ℚ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul, hcomm_single i]
  let U := LinearMap.toMatrix' eqCod.toLinearMap
  let U' := LinearMap.toMatrix' eqCod.symm.toLinearMap
  let V := LinearMap.toMatrix' eqDom.symm.toLinearMap
  let V' := LinearMap.toMatrix' eqDom.toLinearMap
  have hUU' : U * U' = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, eqCod.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hU'U : U' * U = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, eqCod.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hVV' : V * V' = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, eqDom.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hV'V : V' * V = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, eqDom.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have htoMat : ∀ N : Matrix I I ℚ, LinearMap.toMatrix' N.mulVecLin = N := by
    intro N; ext j i
    simp [LinearMap.toMatrix'_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single]
  have hM : M = U * diagR b r * V := by
    have h1 : f = (eqCod.toLinearMap.comp (diagR b r).mulVecLin).comp eqDom.symm.toLinearMap := by
      rw [hcomm, LinearMap.comp_assoc, LinearEquiv.comp_coe, eqDom.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
    have h2 := congrArg LinearMap.toMatrix' h1
    simp only [f, LinearMap.toMatrix'_comp, htoMat] at h2
    exact h2
  exact ⟨U, U', V, V', hUU', hU'U, hVV', hV'V, hM⟩

lemma rank_diagonal_indicator {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (Matrix.diagonal (fun a : α => if p a then (1 : ℚ) else 0)).rank =
      (Finset.univ.filter p).card := by
  let D := Matrix.diagonal (fun a : α => if p a then (1 : ℚ) else 0)
  have hrange : LinearMap.range D.mulVecLin =
      { carrier := {v : α → ℚ | ∀ a, ¬ p a → v a = 0}
        zero_mem' := fun _ _ => rfl, add_mem' := fun {x y} hx hy a ha => by simp [hx a ha, hy a ha],
        smul_mem' := fun c {x} hx a ha => by simp [hx a ha] } := by
    ext v
    simp only [LinearMap.mem_range, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, rfl⟩ a ha
      simp [D, Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, ha]
    · intro hv
      refine ⟨v, ?_⟩
      funext a
      simp only [D, Matrix.mulVecLin_apply, Matrix.mulVec_diagonal]
      by_cases ha : p a
      · simp [ha]
      · simp [ha, hv a ha]
  let e : LinearMap.range D.mulVecLin ≃ₗ[ℚ] ({a : α // p a} → ℚ) :=
    { toFun := fun v a => v.val a.val
      invFun := fun w =>
        ⟨fun a => if ha : p a then w ⟨a, ha⟩ else 0, by
          rw [hrange]; intro a ha; simp [ha]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun v => by
        apply Subtype.ext
        funext a
        by_cases ha : p a
        · simp [ha]
        · have hv : v.val a = 0 := by
            rcases v.property with ⟨w, hw⟩
            rw [← hw]; simp [D, Matrix.mulVec_diagonal, ha]
          simp [ha, hv]
      right_inv := fun w => by
        funext ⟨a, ha⟩
        simp [ha] }
  unfold Matrix.rank
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_subtype]

lemma rank_compound_eq_choose (b d : ℕ) (M : Matrix (Fin (b + 2)) (Fin (b + 2)) ℚ) :
    (compound b d M).rank = Nat.choose M.rank d := by
  rcases matrix_rank_normal_form b M with ⟨U, U', V, V', hUU', hU'U, hVV', hV'V, hM⟩
  have hcomp_M : compound b d M = compound b d U * compound b d (diagR b M.rank) * compound b d V := by
    conv_lhs => rw [hM]
    rw [compound_mul, compound_mul]
  have hCU : compound b d U' * compound b d U = 1 := by
    rw [← compound_mul, hU'U, compound_one]
  have hCV : compound b d V * compound b d V' = 1 := by
    rw [← compound_mul, hVV', compound_one]
  rw [hcomp_M, rank_mul_right_of_right_inv _ _ _ hCV, rank_mul_left_of_left_inv _ _ _ hCU]
  have hdiag : compound b d (diagR b M.rank) =
      Matrix.diagonal (fun T : {S : Finset (Fin (b + 2)) // S.card = d} =>
        if ∀ i ∈ T.val, i.val < M.rank then (1 : ℚ) else 0) := by
    ext T S
    simp only [compound, Matrix.diagonal_apply]
    by_cases hTS : T = S
    · subst hTS
      simp only [↓reduceIte]
      have hsub : (diagR b M.rank).submatrix (ordEmb T) (ordEmb T) =
          Matrix.diagonal (fun k : Fin d => if (ordEmb T k).val < M.rank then (1 : ℚ) else 0) := by
        ext i j
        simp only [Matrix.submatrix_apply, diagR, Matrix.diagonal_apply, (ordEmb T).injective.eq_iff]
      rw [hsub, Matrix.det_diagonal]
      by_cases hall : ∀ i ∈ T.val, i.val < M.rank
      · rw [if_pos hall]
        apply Finset.prod_eq_one
        intro k _
        have hlt := hall (ordEmb T k) (Finset.orderEmbOfFin_mem T.val T.property k)
        simp [hlt]
      · rw [if_neg hall]
        push Not at hall
        rcases hall with ⟨x, hxT, hge⟩
        have hxmem : x ∈ Set.range (ordEmb T) := by rw [range_ordEmb]; exact hxT
        rcases hxmem with ⟨k0, hk0⟩
        apply Finset.prod_eq_zero (Finset.mem_univ k0)
        rw [hk0]
        have hnot : ¬ x.val < M.rank := by omega
        simp [hnot]
    · simp only [hTS, ↓reduceIte]
      have hne_val : T.val ≠ S.val := fun h => hTS (Subtype.ext h)
      have hnot_sub : ¬ T.val ⊆ S.val := fun hsub =>
        hne_val (Finset.eq_of_subset_of_card_le hsub (by rw [T.property, S.property]))
      rw [Finset.not_subset] at hnot_sub
      rcases hnot_sub with ⟨x, hxT, hxS⟩
      have hxmem : x ∈ Set.range (ordEmb T) := by rw [range_ordEmb]; exact hxT
      rcases hxmem with ⟨i0, hi0⟩
      apply Matrix.det_eq_zero_of_row_eq_zero i0
      intro j
      simp only [Matrix.submatrix_apply, diagR, Matrix.diagonal_apply, hi0]
      have hjS : ordEmb S j ∈ S.val := Finset.orderEmbOfFin_mem S.val S.property j
      have hne : x ≠ ordEmb S j := fun h => hxS (h ▸ hjS)
      simp [hne]
  rw [hdiag, rank_diagonal_indicator]
  let low : Finset (Fin (b + 2)) := Finset.univ.filter (fun i : Fin (b + 2) => i.val < M.rank)
  have hlow_card : low.card = M.rank := by
    have hr_le : M.rank ≤ b + 2 := by
      have := Submodule.finrank_le (LinearMap.range M.mulVecLin)
      simpa [Matrix.rank, Module.finrank_pi] using this
    have hlow_bij : low.card = (Finset.range M.rank).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i1 _ i2 _ h; exact Fin.ext h
      · intro x hx
        have hlt := Finset.mem_range.mp hx
        exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    rw [hlow_bij, Finset.card_range]
  have hbij : (Finset.univ.filter (fun T : {S : Finset (Fin (b + 2)) // S.card = d} => ∀ i ∈ T.val, i.val < M.rank)).card =
      (low.powersetCard d).card := by
    refine Finset.card_bij (fun T _ => T.val) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard]
      refine ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2 i hi⟩, T.property⟩
    · intro T1 _ T2 _ h; exact Subtype.ext h
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      refine ⟨⟨S, hS.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => (Finset.mem_filter.mp (hS.1 hi)).2⟩, rfl⟩
  rw [hbij, Finset.card_powersetCard, hlow_card]

lemma main_967 :
    ∀ b : ℕ,
      let I := Fin (b+2)
      let X := I → Bool
      ∀ (a h : I → ℚ) (cut : ℕ) (par : Bool),
        let spin := fun (x : X) (i : I) => if x i then (1 : ℚ) else -1
        let keep := fun d : ℕ => d ≤ cut ∧ decide (d % 2 = 1) = par
        let F : Matrix X (Finset I) ℚ := fun x S =>
          if keep S.card then ∏ i ∈ S, (a i * spin x i + h i * spin x (i+1)) else 0
        let A : ℕ → Matrix I I ℚ := fun (d : ℕ) => (fun (j i : I) =>
          (if j = i then a i else 0) +
          (if j = i+1 then
            if i.val+1 = b+2 ∧ d % 2 = 0 then -(h i) else h i
           else 0) : Matrix I I ℚ)
        F.rank = ∑ d ∈ (Finset.range (b+3)).filter keep, Nat.choose (Matrix.rank (A d)) d := by
  intro b I X a h cut par spin keep F A
  have hF : F = walsh b * (Gmat b a h keep * Tmat b a h keep) :=
    factor_F_eq_walsh_G_T b a h cut par
  rw [hF, rank_mul_left_of_left_inv _ _ _ (walsh_left_inv b),
      rank_mul_right_of_unit_upper Finset.card (Gmat b a h keep) (Tmat b a h keep)
        (Tmat_diag b a h keep) (Tmat_upper b a h keep),
      rank_Gmat_eq_sum b a h keep]
  apply Finset.sum_congr (by ext d; simp)
  intro d _
  rw [Gdeg_eq_compound b a h d, rank_compound_eq_choose b d (A d)]

end

end PEqualNP.Outside.L_lib_967_aux

theorem PEqualNP.Outside.L_lib_967 :
∀ b : ℕ,
  let I := Fin (b+2)
  let X := I → Bool
  ∀ (a h : I → ℚ) (cut : ℕ) (par : Bool),
    let spin := fun (x : X) (i : I) => if x i then (1 : ℚ) else -1
    let keep := fun d : ℕ => d ≤ cut ∧ decide (d % 2 = 1) = par
    let F : Matrix X (Finset I) ℚ := fun x S =>
      if keep S.card then ∏ i ∈ S, (a i * spin x i + h i * spin x (i+1)) else 0
    let A : ℕ → Matrix I I ℚ := fun (d : ℕ) => (fun (j i : I) =>
      (if j = i then a i else 0) +
      (if j = i+1 then
        if i.val+1 = b+2 ∧ d % 2 = 0 then -(h i) else h i
       else 0) : Matrix I I ℚ)
    F.rank = ∑ d ∈ (Finset.range (b+3)).filter keep, Nat.choose (Matrix.rank (A d)) d :=
  PEqualNP.Outside.L_lib_967_aux.main_967
