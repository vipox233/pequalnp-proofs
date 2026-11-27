import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace PEqualNP.Outside.L_lib_705_aux

open scoped BigOperators

lemma permanent_eq_row_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M i (σ i) := by
  rw [Matrix.permanent]
  refine Fintype.sum_bijective (fun σ : Equiv.Perm (Fin n) => σ.symm)
    (Function.bijective_iff_has_inverse.mpr ⟨fun σ => σ.symm, fun _ => rfl, fun _ => rfl⟩) _ _ fun σ => ?_
  refine Fintype.prod_bijective σ σ.bijective _ _ fun i => ?_
  simp

lemma capped_simplex_row_bound {n : ℕ} (d : ℕ) (hd : 0 < d) (hdn : d ≤ n)
    (c x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ (d : ℝ) * x j ≤ 1)
    (hsum : (∑ j : Fin n, x j) = 1) :
    ∃ T : Finset (Fin n), T.card = d ∧
      (∑ j : Fin n, c j * x j) ≤ (∑ j ∈ T, c j) * (d : ℝ)⁻¹ := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  let P := Finset.powersetCard d (Finset.univ : Finset (Fin n))
  have hPne : P.Nonempty := by
    rcases Finset.exists_subset_card_eq (show d ≤ (Finset.univ : Finset (Fin n)).card by
      simp [hdn]) with ⟨S, _, hScard⟩
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩⟩
  rcases Finset.exists_max_image P (fun S => ∑ j ∈ S, c j) hPne with ⟨T, hTP, hTmax⟩
  have hTcard : T.card = d := (Finset.mem_powersetCard.mp hTP).2
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  rcases Finset.exists_min_image T c hTne with ⟨a0, ha0T, ha0min⟩
  have hswap : ∀ b : Fin n, b ∉ T → c b ≤ c a0 := by
    intro b hbT
    let T' := insert b (T.erase a0)
    have hb_not_er : b ∉ T.erase a0 := fun h => hbT (Finset.mem_of_mem_erase h)
    have hT'card : T'.card = d := by
      rw [Finset.card_insert_of_notMem hb_not_er, Finset.card_erase_of_mem ha0T, hTcard]
      omega
    have hT'P : T' ∈ P := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT'card⟩
    have hle := hTmax T' hT'P
    have hs1 : (∑ j ∈ T', c j) = c b + ∑ j ∈ T.erase a0, c j :=
      Finset.sum_insert hb_not_er
    have hs2 : (∑ j ∈ T, c j) = c a0 + ∑ j ∈ T.erase a0, c j :=
      (Finset.add_sum_erase T c ha0T).symm
    linarith
  let m := c a0
  have hdiff : (∑ j : Fin n, c j * x j) - (∑ j ∈ T, c j) * (d : ℝ)⁻¹ =
      (∑ j ∈ T, (c j - m) * (x j - (d : ℝ)⁻¹)) +
      (∑ j ∈ Finset.univ \ T, (c j - m) * x j) := by
    have hsplit : (∑ j : Fin n, c j * x j) =
        (∑ j ∈ T, c j * x j) + ∑ j ∈ Finset.univ \ T, c j * x j := by
      rw [← Finset.sum_sdiff (Finset.subset_univ T), add_comm]
    have hsplit_x : (∑ j : Fin n, x j) =
        (∑ j ∈ T, x j) + ∑ j ∈ Finset.univ \ T, x j := by
      rw [← Finset.sum_sdiff (Finset.subset_univ T), add_comm]
    have h1 : (∑ j ∈ T, (c j - m) * (x j - (d : ℝ)⁻¹)) =
        (∑ j ∈ T, c j * x j) - (∑ j ∈ T, c j) * (d : ℝ)⁻¹ -
          m * (∑ j ∈ T, x j) + m * ((T.card : ℝ) * (d : ℝ)⁻¹) := by
      have hterm : ∀ j ∈ T, (c j - m) * (x j - (d : ℝ)⁻¹) =
          (c j * x j - c j * (d : ℝ)⁻¹) - (m * x j - m * (d : ℝ)⁻¹) := fun j _ => by ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    have h2 : (∑ j ∈ Finset.univ \ T, (c j - m) * x j) =
        (∑ j ∈ Finset.univ \ T, c j * x j) - m * (∑ j ∈ Finset.univ \ T, x j) := by
      have hterm : ∀ j ∈ Finset.univ \ T, (c j - m) * x j = c j * x j - m * x j :=
        fun j _ => by ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hTmul : (T.card : ℝ) * (d : ℝ)⁻¹ = 1 := by
      rw [hTcard, mul_inv_cancel₀ hd_ne]
    have hmx : m * (∑ j ∈ T, x j) + m * (∑ j ∈ Finset.univ \ T, x j) = m := by
      rw [← mul_add, ← hsplit_x, hsum, mul_one]
    rw [h1, h2, hTmul]
    linarith
  have hle1 : (∑ j ∈ T, (c j - m) * (x j - (d : ℝ)⁻¹)) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    have hc : 0 ≤ c j - m := sub_nonneg.mpr (ha0min j hj)
    have hxle : x j - (d : ℝ)⁻¹ ≤ 0 := by
      have h1 : (d : ℝ) * x j ≤ 1 := (hx j).2
      have h2 : x j ≤ (d : ℝ)⁻¹ :=
        le_of_mul_le_mul_left (by rw [mul_inv_cancel₀ hd_ne]; exact h1) hd_pos
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hc hxle
  have hle2 : (∑ j ∈ Finset.univ \ T, (c j - m) * x j) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    have hjnot : j ∉ T := (Finset.mem_sdiff.mp hj).2
    have hc : c j - m ≤ 0 := sub_nonpos.mpr (hswap j hjnot)
    exact mul_nonpos_of_nonpos_of_nonneg hc (hx j).1
  refine ⟨T, hTcard, ?_⟩
  linarith

lemma permanent_replace_row {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (r : Fin n → ℝ) :
    (Matrix.of fun a b => if a = i then r b else B a b).permanent =
      ∑ j : Fin n, r j *
        (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = j),
          ∏ a ∈ Finset.univ.erase i, B a (σ a)) := by
  rw [permanent_eq_row_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin n) => σ i)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσi : σ i = j := (Finset.mem_filter.mp hσ).2
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Matrix.of_apply, ↓reduceIte, hσi]
  congr 1
  refine Finset.prod_congr rfl fun a ha => ?_
  have hne : a ≠ i := Finset.ne_of_mem_erase ha
  simp only [hne, ↓reduceIte]

lemma capped_permanent_reduction {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, 0 ≤ B i j ∧ (d : ℝ) * B i j ≤ 1)
    (hrow : ∀ i, (∑ j : Fin n, B i j) = 1) :
    ∃ A : Fin n → Finset (Fin n), (∀ i, (A i).card = d) ∧
      (d : ℝ) ^ n * B.permanent ≤
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∈ A i)).card : ℝ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hstep : ∀ k : ℕ, k ≤ n →
      ∃ (M : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Finset (Fin n)),
        (∀ i : Fin n, i.val < k → (A i).card = d ∧ ∀ j, M i j = if j ∈ A i then (d : ℝ)⁻¹ else 0) ∧
        (∀ i : Fin n, k ≤ i.val → ∀ j, M i j = B i j) ∧
        B.permanent ≤ M.permanent := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨B, fun _ => ∅, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ => rfl, le_refl _⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨M, A, hlt, hge, hperm⟩
      let i0 : Fin n := ⟨k, by omega⟩
      let c : Fin n → ℝ := fun j =>
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ i0 = j),
          ∏ a ∈ Finset.univ.erase i0, M a (σ a)
      have hM_nonneg : ∀ a b, 0 ≤ M a b := by
        intro a b
        by_cases ha : a.val < k
        · rw [(hlt a ha).2 b]
          split_ifs
          · positivity
          · exact le_refl 0
        · rw [hge a (by omega) b]
          exact (hB a b).1
      rcases capped_simplex_row_bound d hd hdn c (fun j => B i0 j) (hB i0) (hrow i0) with
        ⟨T, hTcard, hTle⟩
      let M' : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun a b => if a = i0 then (if b ∈ T then (d : ℝ)⁻¹ else 0) else M a b
      let A' : Fin n → Finset (Fin n) := fun a => if a = i0 then T else A a
      have hMeq : M = Matrix.of (fun a b => if a = i0 then B i0 b else M a b) := by
        ext a b
        simp only [Matrix.of_apply]
        by_cases ha : a = i0
        · subst ha; simp [hge i0 (le_refl k)]
        · simp [ha]
      have hpermM : M.permanent = ∑ j : Fin n, c j * B i0 j := by
        conv_lhs => rw [hMeq]
        rw [permanent_replace_row]
        refine Finset.sum_congr rfl fun j _ => mul_comm _ _
      have hpermM' : M'.permanent = (∑ j ∈ T, c j) * (d : ℝ)⁻¹ := by
        rw [permanent_replace_row]
        have hsum_eq : (∑ j : Fin n, (if j ∈ T then (d : ℝ)⁻¹ else 0) * c j) =
            ∑ j ∈ T, (d : ℝ)⁻¹ * c j := by
          have h1 : ∀ j : Fin n, (if j ∈ T then (d : ℝ)⁻¹ else 0) * c j =
              if j ∈ T then (d : ℝ)⁻¹ * c j else 0 := fun j => by split_ifs <;> ring
          simp_rw [h1, ← Finset.sum_filter]
          congr 1; ext j; simp
        rw [hsum_eq, ← Finset.mul_sum, mul_comm]
      refine ⟨M', A', ?_, ?_, ?_⟩
      · intro i hi
        by_cases heq : i = i0
        · subst heq
          refine ⟨by simp [A', hTcard], fun j => ?_⟩
          simp [M', A']
        · have hi' : i.val < k := by
            have : i.val ≠ k := fun h => heq (Fin.ext h)
            omega
          refine ⟨by simp [A', heq, (hlt i hi').1], fun j => ?_⟩
          simp [M', A', heq, (hlt i hi').2 j]
      · intro i hi j
        have hne : i ≠ i0 := fun h => by
          have : i.val = k := congrArg Fin.val h
          omega
        simp [M', hne, hge i (by omega) j]
      · linarith
  rcases hstep n (le_refl n) with ⟨M, A, hlt, _, hperm⟩
  have hAcard : ∀ i, (A i).card = d := fun i => (hlt i i.2).1
  have hMeval : M.permanent = ((d : ℝ)⁻¹) ^ n *
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∈ A i)).card : ℝ) := by
    rw [permanent_eq_row_sum]
    have hterm : ∀ σ : Equiv.Perm (Fin n),
        (∏ i : Fin n, M i (σ i)) =
          if ∀ i, σ i ∈ A i then ((d : ℝ)⁻¹) ^ n else 0 := by
      intro σ
      by_cases hmem : ∀ i, σ i ∈ A i
      · simp only [hmem]
        have he : ∀ i : Fin n, M i (σ i) = (d : ℝ)⁻¹ := fun i => by
          rw [(hlt i i.2).2 (σ i)]
          simp [hmem i]
        simp [he]
      · simp only [hmem, ↓reduceIte]
        push Not at hmem
        rcases hmem with ⟨i, hi⟩
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [(hlt i i.2).2 (σ i)]
        simp [hi]
    simp_rw [hterm]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine ⟨A, hAcard, ?_⟩
  have h1 : (d : ℝ) ^ n * B.permanent ≤ (d : ℝ) ^ n * M.permanent :=
    mul_le_mul_of_nonneg_left hperm (by positivity)
  rw [hMeval, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hd_pos), one_pow, one_mul] at h1
  exact h1

def avail {n : ℕ} (A : Fin n → Finset (Fin n)) (τ σ : Equiv.Perm (Fin n)) (k : Fin n) :
    Finset (Fin n) :=
  (A (τ k)).filter (fun j => ∀ r : Fin n, r.val < k.val → σ (τ r) ≠ j)

lemma avail_pos {n : ℕ} (A : Fin n → Finset (Fin n)) (τ σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ i ∈ A i) (k : Fin n) :
    0 < (avail A τ σ k).card := by
  refine Finset.card_pos.mpr ⟨σ (τ k), ?_⟩
  simp only [avail, Finset.mem_filter]
  refine ⟨hσ (τ k), fun r hr heq => ?_⟩
  have h1 : τ r = τ k := σ.injective heq
  have h2 : r = k := τ.injective h1
  omega

lemma tree_weight_sum_le_one {n : ℕ} (A : Fin n → Finset (Fin n)) (τ : Equiv.Perm (Fin n)) :
    let S := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∈ A i)
    (∑ σ ∈ S, (∏ k : Fin n, ((avail A τ σ k).card : ℝ))⁻¹) ≤ 1 := by
  intro S
  have hmain : ∀ (t : ℕ), t ≤ n →
      ∀ g : Fin (n - t) → Fin n,
        (∑ σ ∈ S.filter (fun σ => ∀ r : Fin (n - t), σ (τ ⟨r.val, by omega⟩) = g r),
          (∏ k ∈ Finset.univ.filter (fun k : Fin n => n - t ≤ k.val),
            ((avail A τ σ k).card : ℝ))⁻¹) ≤ 1 := by
    intro t
    induction t with
    | zero =>
      intro _ g
      have hcard : (S.filter (fun σ => ∀ r : Fin (n - 0), σ (τ ⟨r.val, by omega⟩) = g r)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun σ1 h1 σ2 h2 => ?_
        have hg1 := (Finset.mem_filter.mp h1).2
        have hg2 := (Finset.mem_filter.mp h2).2
        apply Equiv.ext; intro i
        let r : Fin (n - 0) := ⟨(τ.symm i).val, by have := (τ.symm i).2; omega⟩
        have hτr : τ ⟨r.val, by omega⟩ = i := by
          have : (⟨r.val, by omega⟩ : Fin n) = τ.symm i := Fin.ext rfl
          rw [this, Equiv.apply_symm_apply]
        calc
          σ1 i = σ1 (τ ⟨r.val, by omega⟩) := by rw [hτr]
          _ = g r := hg1 r
          _ = σ2 (τ ⟨r.val, by omega⟩) := (hg2 r).symm
          _ = σ2 i := by rw [hτr]
      have hemp : Finset.univ.filter (fun k : Fin n => n - 0 ≤ k.val) = ∅ := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        have := k.2; omega
      rw [hemp]
      simp only [Finset.prod_empty, inv_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard
    | succ t ih =>
      intro ht g
      let m := n - (t + 1)
      have hm_lt : m < n := by omega
      have hmt : n - t = m + 1 := by omega
      let k0 : Fin n := ⟨m, hm_lt⟩
      let C : Finset (Fin n) := (A (τ k0)).filter (fun j => ∀ r : Fin m, g r ≠ j)
      let Fm := S.filter (fun σ => ∀ r : Fin m, σ (τ ⟨r.val, by omega⟩) = g r)
      have havail_eq : ∀ σ ∈ Fm, avail A τ σ k0 = C := by
        intro σ hσ
        have hg := (Finset.mem_filter.mp hσ).2
        ext j
        simp only [avail, C, Finset.mem_filter]
        refine and_congr_right fun _ => ⟨fun h r => ?_, fun h r hr => ?_⟩
        · have := h ⟨r.val, by omega⟩ r.2
          rw [hg r] at this
          exact this
        · have h1 := h ⟨r.val, hr⟩
          rw [← hg ⟨r.val, hr⟩] at h1
          exact h1
      have hmaps : ∀ σ ∈ Fm, σ (τ k0) ∈ C := by
        intro σ hσ
        rw [← havail_eq σ hσ]
        have hσS : ∀ i, σ i ∈ A i := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
        simp only [avail, Finset.mem_filter]
        refine ⟨hσS (τ k0), fun r hr heq => ?_⟩
        have := τ.injective (σ.injective heq)
        have : r.val = k0.val := congrArg Fin.val this
        omega
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ => σ (τ k0)) (t := C) hmaps]
      have hfiber_le : ∀ j ∈ C,
          (∑ σ ∈ Fm.filter (fun σ => σ (τ k0) = j),
            (∏ k ∈ Finset.univ.filter (fun k : Fin n => m ≤ k.val),
              ((avail A τ σ k).card : ℝ))⁻¹) ≤ (C.card : ℝ)⁻¹ := by
        intro j _
        let g' : Fin (n - t) → Fin n := fun r =>
          if h : r.val < m then g ⟨r.val, h⟩ else j
        have hfilt_eq : Fm.filter (fun σ => σ (τ k0) = j) =
            S.filter (fun σ => ∀ r : Fin (n - t), σ (τ ⟨r.val, by omega⟩) = g' r) := by
          ext σ
          simp only [Fm, Finset.mem_filter]
          constructor
          · rintro ⟨⟨hσS, hσg⟩, hσj⟩
            refine ⟨hσS, fun r => ?_⟩
            by_cases h : r.val < m
            · simp only [g', h, ↓reduceDIte]
              exact hσg ⟨r.val, h⟩
            · simp only [g', h, ↓reduceDIte]
              have hr : (⟨r.val, by omega⟩ : Fin n) = k0 := Fin.ext (by dsimp only [k0]; have := r.2; omega)
              rw [hr]
              exact hσj
          · rintro ⟨hσS, hσg'⟩
            refine ⟨⟨hσS, fun r => ?_⟩, ?_⟩
            · have h1 := hσg' ⟨r.val, by omega⟩
              simp only [g', r.2, ↓reduceDIte] at h1
              exact h1
            · have h1 := hσg' ⟨m, by omega⟩
              simp only [g', lt_self_iff_false, ↓reduceDIte] at h1
              exact h1
        have hprod_split : ∀ σ ∈ Fm.filter (fun σ => σ (τ k0) = j),
            (∏ k ∈ Finset.univ.filter (fun k : Fin n => m ≤ k.val),
              ((avail A τ σ k).card : ℝ))⁻¹ =
            (C.card : ℝ)⁻¹ *
              (∏ k ∈ Finset.univ.filter (fun k : Fin n => n - t ≤ k.val),
                ((avail A τ σ k).card : ℝ))⁻¹ := by
          intro σ hσ
          have hσFm : σ ∈ Fm := (Finset.mem_filter.mp hσ).1
          have hk0_mem : k0 ∈ Finset.univ.filter (fun k : Fin n => m ≤ k.val) := by
            simp [k0]
          have herase : (Finset.univ.filter (fun k : Fin n => m ≤ k.val)).erase k0 =
              Finset.univ.filter (fun k : Fin n => n - t ≤ k.val) := by
            ext k
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hne, hge⟩
              have : k.val ≠ m := fun h => hne (Fin.ext h)
              omega
            · intro hge
              refine ⟨fun h => by have : k.val = m := congrArg Fin.val h; omega, by omega⟩
          rw [← Finset.mul_prod_erase _ _ hk0_mem, herase, havail_eq σ hσFm, mul_inv]
        rw [Finset.sum_congr rfl hprod_split, ← Finset.mul_sum, hfilt_eq]
        have hih := ih (by omega) g'
        have hCnn : (0 : ℝ) ≤ (C.card : ℝ)⁻¹ := by positivity
        nlinarith
      calc
        (∑ j ∈ C, ∑ σ ∈ Fm.filter (fun σ => σ (τ k0) = j),
            (∏ k ∈ Finset.univ.filter (fun k : Fin n => m ≤ k.val),
              ((avail A τ σ k).card : ℝ))⁻¹)
            ≤ ∑ _j ∈ C, (C.card : ℝ)⁻¹ := Finset.sum_le_sum hfiber_le
        _ = (C.card : ℝ) * (C.card : ℝ)⁻¹ := by simp [Finset.sum_const]
        _ ≤ 1 := by
          by_cases hC0 : C.card = 0
          · simp [hC0]
          · rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hC0)]
  have h0 := hmain n (le_refl n) (fun r => (Fin.elim0 (by simpa using r)))
  have hS : S.filter (fun σ => ∀ r : Fin (n - n), σ (τ ⟨r.val, by omega⟩) =
      (fun r : Fin (n - n) => Fin.elim0 (by simpa using r)) r) = S := by
    ext σ
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _ r
    have := r.2
    omega
  have hall : Finset.univ.filter (fun k : Fin n => n - n ≤ k.val) = Finset.univ := by
    ext k; simp
  rw [hS, hall] at h0
  exact h0

lemma sum_rank_over_finset {α : Type*} [DecidableEq α] (f : ℕ → ℝ) :
    ∀ (d : ℕ) (R : Finset α) (g : α → ℕ),
      R.card = d → (∀ a ∈ R, ∀ b ∈ R, g a = g b → a = b) →
      (∑ a ∈ R, f ((R.filter (fun b => g a ≤ g b)).card)) =
        ∑ m ∈ Finset.Icc 1 d, f m := by
  intro d
  induction d with
  | zero =>
    intro R _ hR _
    rw [Finset.card_eq_zero.mp hR]
    simp
  | succ d ih =>
    intro R g hR hinj
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    rcases Finset.exists_min_image R g hRne with ⟨a0, ha0R, ha0min⟩
    have ha0_cnt : (R.filter (fun b => g a0 ≤ g b)).card = d + 1 := by
      have heq : R.filter (fun b => g a0 ≤ g b) = R :=
        Finset.filter_true_of_mem fun b hb => ha0min b hb
      rw [heq, hR]
    let R' := R.erase a0
    have hR'card : R'.card = d := by
      rw [Finset.card_erase_of_mem ha0R, hR]; omega
    have hR'inj : ∀ a ∈ R', ∀ b ∈ R', g a = g b → a = b :=
      fun a ha b hb => hinj a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    have hother : ∀ a ∈ R',
        (R.filter (fun b => g a ≤ g b)).card = (R'.filter (fun b => g a ≤ g b)).card := by
      intro a ha
      have hne : a ≠ a0 := Finset.ne_of_mem_erase ha
      have hlt : g a0 < g a := by
        have hle := ha0min a (Finset.mem_of_mem_erase ha)
        have hneq : g a0 ≠ g a := fun h => hne (hinj a0 ha0R a (Finset.mem_of_mem_erase ha) h).symm
        omega
      congr 1
      ext b
      simp only [R', Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hbR, hle⟩
        refine ⟨⟨fun hba0 => ?_, hbR⟩, hle⟩
        subst hba0; omega
      · rintro ⟨⟨_, hbR⟩, hle⟩
        exact ⟨hbR, hle⟩
    rw [← Finset.add_sum_erase R _ ha0R, ha0_cnt]
    change f (d + 1) + (∑ a ∈ R', f ((R.filter (fun b => g a ≤ g b)).card)) = _
    rw [Finset.sum_congr rfl fun a ha => by rw [hother a ha]]
    rw [ih R' g hR'card hR'inj]
    have hIcc : Finset.Icc 1 (d + 1) = insert (d + 1) (Finset.Icc 1 d) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp)]

lemma bregman_uniform {n d : ℕ} (hd : 0 < d) (A : Fin n → Finset (Fin n))
    (hA : ∀ i, (A i).card = d) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∈ A i)).card : ℝ) ^ d ≤
      (d.factorial : ℝ) ^ n := by
  let S := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∈ A i)
  by_cases hS0 : S.card = 0
  · rw [hS0, Nat.cast_zero, zero_pow (Nat.ne_of_gt hd)]
    positivity
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS0)
  have hlog_tau : ∀ τ : Equiv.Perm (Fin n),
      (S.card : ℝ) * Real.log (S.card : ℝ) ≤
        ∑ σ ∈ S, ∑ i : Fin n, Real.log ((avail A τ σ (τ.symm i)).card : ℝ) := by
    intro τ
    have hw := tree_weight_sum_le_one A τ
    have hsum_le : (∑ σ ∈ S, (Real.log (S.card : ℝ) -
        ∑ k : Fin n, Real.log ((avail A τ σ k).card : ℝ))) ≤ 0 := by
      have hterm : ∀ σ ∈ S,
          Real.log (S.card : ℝ) - ∑ k : Fin n, Real.log ((avail A τ σ k).card : ℝ) ≤
            (S.card : ℝ) * (∏ k : Fin n, ((avail A τ σ k).card : ℝ))⁻¹ - 1 := by
        intro σ hσ
        have hσA : ∀ i, σ i ∈ A i := (Finset.mem_filter.mp hσ).2
        have hpos_k : ∀ k : Fin n, (0 : ℝ) < ((avail A τ σ k).card : ℝ) :=
          fun k => Nat.cast_pos.mpr (avail_pos A τ σ hσA k)
        have hPpos : (0 : ℝ) < ∏ k : Fin n, ((avail A τ σ k).card : ℝ) :=
          Finset.prod_pos fun k _ => hpos_k k
        have hlog_eq : Real.log ((S.card : ℝ) * (∏ k : Fin n, ((avail A τ σ k).card : ℝ))⁻¹) =
            Real.log (S.card : ℝ) - ∑ k : Fin n, Real.log ((avail A τ σ k).card : ℝ) := by
          rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hSpos) (ne_of_gt hPpos),
            Real.log_prod fun k _ => ne_of_gt (hpos_k k)]
        rw [← hlog_eq]
        exact Real.log_le_sub_one_of_pos (mul_pos hSpos (inv_pos.mpr hPpos))
      calc
        (∑ σ ∈ S, (Real.log (S.card : ℝ) -
            ∑ k : Fin n, Real.log ((avail A τ σ k).card : ℝ)))
            ≤ ∑ σ ∈ S, ((S.card : ℝ) * (∏ k : Fin n, ((avail A τ σ k).card : ℝ))⁻¹ - 1) :=
          Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (∑ σ ∈ S, (∏ k : Fin n, ((avail A τ σ k).card : ℝ))⁻¹) -
            (S.card : ℝ) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (S.card : ℝ) * 1 - (S.card : ℝ) := by nlinarith
        _ = 0 := by ring
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_le
    have hreidx : ∀ σ ∈ S,
        (∑ k : Fin n, Real.log ((avail A τ σ k).card : ℝ)) =
          ∑ i : Fin n, Real.log ((avail A τ σ (τ.symm i)).card : ℝ) := by
      intro σ _
      exact (Fintype.sum_bijective τ.symm τ.symm.bijective _ _ fun _ => rfl).symm
    rw [Finset.sum_congr rfl hreidx] at hsum_le
    linarith
  have hsum_all_tau :
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ((S.card : ℝ) * Real.log (S.card : ℝ)) ≤
        ∑ σ ∈ S, ∑ i : Fin n, ∑ τ : Equiv.Perm (Fin n),
          Real.log ((avail A τ σ (τ.symm i)).card : ℝ) := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      fun τ _ => hlog_tau τ
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    rw [Finset.sum_comm] at h1
    have h2 : (∑ σ ∈ S, ∑ τ : Equiv.Perm (Fin n), ∑ i : Fin n,
        Real.log ((avail A τ σ (τ.symm i)).card : ℝ)) =
        ∑ σ ∈ S, ∑ i : Fin n, ∑ τ : Equiv.Perm (Fin n),
          Real.log ((avail A τ σ (τ.symm i)).card : ℝ) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [← h2]
    exact h1
  have hinner_eq : ∀ σ ∈ S, ∀ i : Fin n,
      (d : ℝ) * (∑ τ : Equiv.Perm (Fin n), Real.log ((avail A τ σ (τ.symm i)).card : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * Real.log (d.factorial : ℝ) := by
    intro σ hσ i
    have hσA : ∀ a, σ a ∈ A a := (Finset.mem_filter.mp hσ).2
    let R : Finset (Fin n) := (A i).image σ.symm
    have hRcard : R.card = d := by
      rw [Finset.card_image_of_injective _ σ.symm.injective, hA i]
    have hiR : i ∈ R := Finset.mem_image.mpr ⟨σ i, hσA i, σ.symm_apply_apply i⟩
    have havail_card : ∀ τ : Equiv.Perm (Fin n),
        (avail A τ σ (τ.symm i)).card =
          (R.filter (fun x => (τ.symm i).val ≤ (τ.symm x).val)).card := by
      intro τ
      refine Finset.card_bij (fun j _ => σ.symm j) ?_ ?_ ?_
      · intro j hj
        simp only [avail, Finset.mem_filter, Equiv.apply_symm_apply] at hj
        simp only [Finset.mem_filter]
        refine ⟨Finset.mem_image.mpr ⟨j, hj.1, rfl⟩, ?_⟩
        by_contra hlt
        push Not at hlt
        have hneq := hj.2 (τ.symm (σ.symm j)) hlt
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hneq
        exact hneq rfl
      · intro j1 _ j2 _ heq
        exact σ.symm.injective heq
      · intro x hx
        simp only [Finset.mem_filter] at hx
        rcases Finset.mem_image.mp hx.1 with ⟨j, hjA, rfl⟩
        refine ⟨j, ?_, rfl⟩
        simp only [avail, Finset.mem_filter, Equiv.apply_symm_apply]
        refine ⟨hjA, fun r hr heq => ?_⟩
        have h1 : τ r = σ.symm j := by rw [← heq, Equiv.symm_apply_apply]
        have h2 : r = τ.symm (σ.symm j) := by rw [← h1, Equiv.symm_apply_apply]
        rw [h2] at hr
        omega
    simp_rw [havail_card]
    have hsymm_j : ∀ j ∈ R,
        (∑ τ : Equiv.Perm (Fin n),
          Real.log ((R.filter (fun x => (τ.symm i).val ≤ (τ.symm x).val)).card : ℝ)) =
        ∑ τ : Equiv.Perm (Fin n),
          Real.log ((R.filter (fun x => (τ.symm j).val ≤ (τ.symm x).val)).card : ℝ) := by
      intro j hjR
      let sw := Equiv.swap i j
      let bij : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) := fun τ => τ.trans sw
      have hbij : Function.Bijective bij :=
        Function.bijective_iff_has_inverse.mpr
          ⟨fun τ => τ.trans sw,
           fun τ => by ext x; simp [bij, sw],
           fun τ => by ext x; simp [bij, sw]⟩
      refine Fintype.sum_bijective bij hbij _ _ fun τ => ?_
      congr 2
      refine Finset.card_bij (fun x _ => sw x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        have hswR : sw x ∈ R := by
          by_cases h1 : x = i
          · subst h1; simpa [sw] using hjR
          · by_cases h2 : x = j
            · subst h2; simpa [sw] using hiR
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hx.1
        refine ⟨hswR, ?_⟩
        have hpx : (bij τ).symm (sw x) = τ.symm x := by
          simp [bij, sw]
        have hpi' : (bij τ).symm j = τ.symm i := by
          simp [bij, sw]
        rw [hpi', hpx]
        exact hx.2
      · intro x1 _ x2 _ heq; exact sw.injective heq
      · intro y hy
        simp only [Finset.mem_filter] at hy
        have hswR : sw y ∈ R := by
          by_cases h1 : y = i
          · subst h1; simpa [sw] using hjR
          · by_cases h2 : y = j
            · subst h2; simpa [sw] using hiR
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hy.1
        refine ⟨sw y, ?_, by simp [sw]⟩
        simp only [Finset.mem_filter]
        refine ⟨hswR, ?_⟩
        have hpi' : (bij τ).symm j = τ.symm i := by
          simp [bij, sw]
        have hpy : (bij τ).symm y = τ.symm (sw y) := by
          simp [bij, sw]
        rw [hpi', hpy] at hy
        exact hy.2
    have hmul_d :
        (d : ℝ) * (∑ τ : Equiv.Perm (Fin n),
          Real.log ((R.filter (fun x => (τ.symm i).val ≤ (τ.symm x).val)).card : ℝ)) =
        ∑ τ : Equiv.Perm (Fin n), ∑ j ∈ R,
          Real.log ((R.filter (fun x => (τ.symm j).val ≤ (τ.symm x).val)).card : ℝ) := by
      calc
        (d : ℝ) * (∑ τ : Equiv.Perm (Fin n),
            Real.log ((R.filter (fun x => (τ.symm i).val ≤ (τ.symm x).val)).card : ℝ))
            = ∑ _j ∈ R, ∑ τ : Equiv.Perm (Fin n),
                Real.log ((R.filter (fun x => (τ.symm i).val ≤ (τ.symm x).val)).card : ℝ) := by
              rw [Finset.sum_const, hRcard, nsmul_eq_mul]
        _ = ∑ j ∈ R, ∑ τ : Equiv.Perm (Fin n),
              Real.log ((R.filter (fun x => (τ.symm j).val ≤ (τ.symm x).val)).card : ℝ) :=
            Finset.sum_congr rfl fun j hj => hsymm_j j hj
        _ = ∑ τ : Equiv.Perm (Fin n), ∑ j ∈ R,
              Real.log ((R.filter (fun x => (τ.symm j).val ≤ (τ.symm x).val)).card : ℝ) :=
            Finset.sum_comm
    rw [hmul_d]
    have hlog_fac : (∑ m ∈ Finset.Icc 1 d, Real.log (m : ℝ)) = Real.log (d.factorial : ℝ) := by
      suffices h : ∀ d' : ℕ, (∑ m ∈ Finset.Icc 1 d', Real.log (m : ℝ)) = Real.log (d'.factorial : ℝ) from h d
      intro d'
      induction d' with
      | zero => simp
      | succ k ih =>
        have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
    have hper_tau : ∀ τ : Equiv.Perm (Fin n),
        (∑ j ∈ R, Real.log ((R.filter (fun x => (τ.symm j).val ≤ (τ.symm x).val)).card : ℝ)) =
          Real.log (d.factorial : ℝ) := by
      intro τ
      rw [← hlog_fac]
      exact sum_rank_over_finset (fun m => Real.log (m : ℝ)) d R (fun x => (τ.symm x).val) hRcard
        (fun a _ b _ heq => τ.symm.injective (Fin.ext heq))
    simp_rw [hper_tau]
    simp [Finset.sum_const]
  have hmul_d_all := mul_le_mul_of_nonneg_left hsum_all_tau (Nat.cast_nonneg d)
  rw [Finset.mul_sum] at hmul_d_all
  have hrhs_eq :
      (∑ σ ∈ S, (d : ℝ) * ∑ i : Fin n, ∑ τ : Equiv.Perm (Fin n),
        Real.log ((avail A τ σ (τ.symm i)).card : ℝ)) =
      (S.card : ℝ) * (n : ℝ) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * Real.log (d.factorial : ℝ) := by
    have h1 : ∀ σ ∈ S,
        (d : ℝ) * (∑ i : Fin n, ∑ τ : Equiv.Perm (Fin n),
          Real.log ((avail A τ σ (τ.symm i)).card : ℝ)) =
        (n : ℝ) * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * Real.log (d.factorial : ℝ)) := by
      intro σ hσ
      rw [Finset.mul_sum]
      simp_rw [hinner_eq σ hσ]
      simp [Finset.sum_const]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hrhs_eq] at hmul_d_all
  have hPcard_pos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hlog_ineq : (d : ℝ) * Real.log (S.card : ℝ) ≤ (n : ℝ) * Real.log (d.factorial : ℝ) := by
    have hfac : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (S.card : ℝ) :=
      mul_pos hPcard_pos hSpos
    nlinarith
  have hlog_pow : Real.log ((S.card : ℝ) ^ d) ≤ Real.log ((d.factorial : ℝ) ^ n) := by
    rw [Real.log_pow, Real.log_pow]
    exact hlog_ineq
  exact (Real.log_le_log_iff (pow_pos hSpos d) (pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos d)) n)).mp
    hlog_pow

lemma sum_exp_unity {n : ℕ} (hn : 0 < n) (m : ℤ) (hndvd : ¬ (n : ℤ) ∣ m) :
    (∑ k : Fin n,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k.val : ℂ) / (n : ℂ))) = 0 := by
  let ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (n : ℂ))
  have hpow : ∀ k : ℕ, ω ^ k =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ)) := by
    intro k
    dsimp only [ω]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hω_ne : ω ≠ 1 := by
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    rcases h1 with ⟨q, hq⟩
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hq2 : (2 * (Real.pi : ℂ) * Complex.I) * ((m : ℂ) / (n : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ) := by
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * ((m : ℂ) / (n : ℂ))
            = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (n : ℂ) := by ring
        _ = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hq
        _ = (2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ) := by ring
    have hdiv : (m : ℂ) / (n : ℂ) = (q : ℂ) := mul_left_cancel₀ hpi hq2
    have hmc : (m : ℂ) = (n : ℂ) * (q : ℂ) := by
      have := congrArg (fun z : ℂ => z * (n : ℂ)) hdiv
      simp only [div_mul_cancel₀ _ hn_ne] at this
      rw [mul_comm] at this
      exact this
    have hm_int : m = (n : ℤ) * q := by
      have hcast : ((m : ℤ) : ℂ) = (((n : ℤ) * q : ℤ) : ℂ) := by
        push_cast; exact hmc
      exact Int.cast_injective hcast
    exact hndvd ⟨q, hm_int⟩
  have hωn : ω ^ n = 1 := by
    rw [hpow n]
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (n : ℂ) / (n : ℂ) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp [hn_ne]
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I m
  have hsum_range : (∑ k : Fin n,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k.val : ℂ) / (n : ℂ))) =
      ∑ k ∈ Finset.range n, ω ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ω ^ k)]
    refine Finset.sum_congr rfl fun k _ => (hpow k.val).symm
  rw [hsum_range, geom_sum_eq hω_ne, hωn, sub_self, zero_div]

lemma hartley_matrix_props {n : ℕ} (hn : 2 ≤ n) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      U * U.transpose = 1 ∧
      (∀ i j, (n : ℝ) * (U i j) ^ 2 ≤ 2) := by
  have hn_pos : 0 < n := by omega
  have hnr_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hnr_ne : (n : ℝ) ≠ 0 := ne_of_gt hnr_pos
  let θ : Fin n → Fin n → ℝ := fun i k =>
    2 * Real.pi * (i.val : ℝ) * (k.val : ℝ) / (n : ℝ)
  let U : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i k => (Real.cos (θ i k) + Real.sin (θ i k)) / Real.sqrt (n : ℝ)
  refine ⟨U, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, U, Matrix.of_apply]
    have hterm : ∀ k : Fin n,
        ((Real.cos (θ i k) + Real.sin (θ i k)) / Real.sqrt (n : ℝ)) *
          ((Real.cos (θ j k) + Real.sin (θ j k)) / Real.sqrt (n : ℝ)) =
        (Real.cos (θ i k - θ j k) + Real.sin (θ i k + θ j k)) / (n : ℝ) := by
      intro k
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hnr_pos)
      rw [div_mul_div_comm, hsq, Real.cos_sub, Real.sin_add]
      ring
    simp_rw [hterm, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
    have hsin_sum : (∑ k : Fin n, Real.sin (θ i k + θ j k)) = 0 := by
      let m : ℤ := (i.val : ℤ) + (j.val : ℤ)
      have harg : ∀ k : Fin n,
          θ i k + θ j k = 2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (n : ℝ) := by
        intro k; dsimp only [θ, m]; push_cast; ring
      simp_rw [harg]
      by_cases hdvd : (n : ℤ) ∣ m
      · rcases hdvd with ⟨q, hq⟩
        refine Finset.sum_eq_zero fun k _ => ?_
        have hq' : (m : ℝ) = (n : ℝ) * (q : ℝ) := by exact_mod_cast hq
        have hmul : 2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (n : ℝ) =
            ((2 * (q * (k.val : ℤ)) : ℤ) : ℝ) * Real.pi := by
          rw [hq']; push_cast; field_simp [hnr_ne]
        rw [hmul]
        exact Real.sin_int_mul_pi (2 * (q * (k.val : ℤ)))
      · have hzero := congrArg Complex.im (sum_exp_unity hn_pos m hdvd)
        rw [Complex.im_sum, Complex.zero_im] at hzero
        rw [← hzero]
        refine Finset.sum_congr rfl fun k _ => ?_
        have heq : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k.val : ℂ) / (n : ℂ) =
            ((2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [heq, Complex.exp_ofReal_mul_I_im]
    rw [hsin_sum, add_zero]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, sub_self, Real.cos_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hnr_ne]
    · simp only [hij, ↓reduceIte]
      let m : ℤ := (i.val : ℤ) - (j.val : ℤ)
      have hndvd : ¬ (n : ℤ) ∣ m := by
        rintro ⟨q, hq⟩
        have hi := i.2
        have hj := j.2
        have hne : m ≠ 0 := fun h0 => hij (Fin.ext (by dsimp only [m] at h0; omega))
        have hq0 : q ≠ 0 := fun h => hne (by rw [hq, h, mul_zero])
        have hlt : -(n : ℤ) < m ∧ m < (n : ℤ) := by dsimp only [m]; omega
        rcases lt_or_gt_of_ne hq0 with hneg | hpos
        · have : q ≤ -1 := by omega
          nlinarith
        · have : 1 ≤ q := by omega
          nlinarith
      have harg : ∀ k : Fin n,
          θ i k - θ j k = 2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (n : ℝ) := by
        intro k; dsimp only [θ, m]; push_cast; ring
      simp_rw [harg]
      have hzero := congrArg Complex.re (sum_exp_unity hn_pos m hndvd)
      rw [Complex.re_sum, Complex.zero_re] at hzero
      have hcos : (∑ k : Fin n, Real.cos (2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (n : ℝ))) = 0 := by
        rw [← hzero]
        refine Finset.sum_congr rfl fun k _ => ?_
        have heq : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k.val : ℂ) / (n : ℂ) =
            ((2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [heq, Complex.exp_ofReal_mul_I_re]
      rw [hcos, zero_mul]
  · intro i j
    simp only [U, Matrix.of_apply, div_pow, Real.sq_sqrt (le_of_lt hnr_pos)]
    rw [mul_div_cancel₀ _ hnr_ne]
    have h1 := Real.cos_sq_add_sin_sq (θ i j)
    have h2 : 0 ≤ (Real.cos (θ i j) - Real.sin (θ i j)) ^ 2 := sq_nonneg _
    nlinarith

lemma four_pow_le_choose {d : ℕ} : 4 ^ d ≤ (2 * d + 1) * Nat.choose (2 * d) d := by
  have hsum : 4 ^ d = ∑ k ∈ Finset.range (2 * d + 1), Nat.choose (2 * d) k := by
    have h1 := Nat.sum_range_choose (2 * d)
    rw [show 4 ^ d = 2 ^ (2 * d) by rw [pow_mul]; norm_num]
    exact h1.symm
  rw [hsum]
  calc
    (∑ k ∈ Finset.range (2 * d + 1), Nat.choose (2 * d) k)
        ≤ ∑ _k ∈ Finset.range (2 * d + 1), Nat.choose (2 * d) d := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hmid := Nat.choose_le_middle k (2 * d)
      rwa [Nat.mul_div_cancel_left d (by omega : 0 < 2)] at hmid
    _ = (2 * d + 1) * Nat.choose (2 * d) d := by simp [Finset.sum_const]

lemma succ_pow_le_three_mul_pow {m : ℕ} (hm : 1 ≤ m) : (m + 1) ^ m ≤ 3 * m ^ m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have h1 : 1 + (m : ℝ)⁻¹ ≤ Real.exp (m : ℝ)⁻¹ := by
    have := Real.add_one_le_exp (m : ℝ)⁻¹
    linarith
  have h2 : (1 + (m : ℝ)⁻¹) ^ m ≤ (Real.exp (m : ℝ)⁻¹) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  have h3 : (Real.exp (m : ℝ)⁻¹) ^ m = Real.exp 1 := by
    rw [← Real.exp_nat_mul, mul_inv_cancel₀ hm_ne]
  have h4 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h5 : ((m + 1 : ℝ) / (m : ℝ)) ^ m ≤ 3 := by
    have hdiv : (m + 1 : ℝ) / (m : ℝ) = 1 + (m : ℝ)⁻¹ := by field_simp [hm_ne]
    rw [hdiv]
    linarith
  rw [div_pow] at h5
  have h6 : ((m + 1 : ℝ)) ^ m ≤ 3 * (m : ℝ) ^ m :=
    (div_le_iff₀ (pow_pos hm_pos m)).mp h5
  exact_mod_cast h6

lemma factorial_le_pow_self (d : ℕ) : d.factorial ≤ d ^ d := by
  induction d with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ']
    refine Nat.mul_le_mul_left (k + 1) ?_
    calc
      k.factorial ≤ k ^ k := ih
      _ ≤ (k + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ k) k

lemma nat_ratio_bound {n : ℕ} (hn : 2 ≤ n) :
    let d := n / 2
    n ^ (n * d) * d.factorial ^ n ≤ d ^ (n * d) * (3 * (n + 1) * n.factorial) ^ d := by
  intro d
  have hd : 1 ≤ d := by dsimp only [d]; omega
  by_cases heven : n = 2 * d
  · rw [heven]
    have hbase : 4 ^ d * d.factorial ^ 2 ≤ 3 * (2 * d + 1) * (2 * d).factorial := by
      have hc := Nat.choose_mul_factorial_mul_factorial (show d ≤ 2 * d by omega)
      rw [show 2 * d - d = d by omega] at hc
      have h4 := four_pow_le_choose (d := d)
      calc
        4 ^ d * d.factorial ^ 2
            ≤ (2 * d + 1) * Nat.choose (2 * d) d * d.factorial ^ 2 :=
          Nat.mul_le_mul_right _ h4
        _ = (2 * d + 1) * (Nat.choose (2 * d) d * d.factorial * d.factorial) := by ring
        _ = (2 * d + 1) * (2 * d).factorial := by rw [hc]
        _ ≤ 3 * (2 * d + 1) * (2 * d).factorial := by nlinarith
    have hpow := Nat.pow_le_pow_left hbase d
    have hlhs : (2 * d) ^ (2 * d * d) * d.factorial ^ (2 * d) =
        d ^ (2 * d * d) * (4 ^ d * d.factorial ^ 2) ^ d := by
      calc
        (2 * d) ^ (2 * d * d) * d.factorial ^ (2 * d)
            = 2 ^ (2 * d * d) * d ^ (2 * d * d) * (d.factorial ^ 2) ^ d := by
              rw [mul_pow, ← pow_mul]
        _ = d ^ (2 * d * d) * ((2 ^ (2 * d)) ^ d * (d.factorial ^ 2) ^ d) := by
              rw [← pow_mul]; ring
        _ = d ^ (2 * d * d) * (4 ^ d * d.factorial ^ 2) ^ d := by
              rw [← mul_pow, show 2 ^ (2 * d) = 4 ^ d by rw [pow_mul]; norm_num]
    rw [hlhs]
    exact Nat.mul_le_mul_left _ hpow
  · have hodd : n = 2 * d + 1 := by dsimp only [d]; omega
    rw [hodd]
    have hbase : (2 * d + 1) ^ (2 * d + 1) * d.factorial ^ 2 ≤
        d ^ (2 * d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial) := by
      have h1 : (2 * d + 1) ^ (2 * d) ≤ 3 * (2 * d) ^ (2 * d) :=
        succ_pow_le_three_mul_pow (by omega : 1 ≤ 2 * d)
      have h2 : (2 * d) ^ (2 * d) = 4 ^ d * d ^ (2 * d) := by
        rw [mul_pow, show 2 ^ (2 * d) = 4 ^ d by rw [pow_mul]; norm_num]
      have h4 : 4 ^ d ≤ (2 * d + 1 + 1) * Nat.choose (2 * d) d := by
        have := four_pow_le_choose (d := d)
        nlinarith
      have hc := Nat.choose_mul_factorial_mul_factorial (show d ≤ 2 * d by omega)
      rw [show 2 * d - d = d by omega] at hc
      have hfac : (2 * d + 1).factorial = (2 * d + 1) * (2 * d).factorial :=
        Nat.factorial_succ (2 * d)
      calc
        (2 * d + 1) ^ (2 * d + 1) * d.factorial ^ 2
            = (2 * d + 1) * (2 * d + 1) ^ (2 * d) * d.factorial ^ 2 := by rw [pow_succ']
        _ ≤ (2 * d + 1) * (3 * (2 * d) ^ (2 * d)) * d.factorial ^ 2 := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = (2 * d + 1) * (3 * (4 ^ d * d ^ (2 * d))) * d.factorial ^ 2 := by rw [h2]
        _ ≤ (2 * d + 1) * (3 * ((2 * d + 1 + 1) * Nat.choose (2 * d) d * d ^ (2 * d))) *
            d.factorial ^ 2 := by
            refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_))
            exact Nat.mul_le_mul_right _ h4
        _ = d ^ (2 * d) * (3 * (2 * d + 1 + 1) *
            ((2 * d + 1) * (Nat.choose (2 * d) d * d.factorial * d.factorial))) := by ring
        _ = d ^ (2 * d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial) := by rw [hc, ← hfac]
    have hpow := Nat.pow_le_pow_left hbase d
    have hfac_d : d.factorial ≤ d ^ d := factorial_le_pow_self d
    have hprod := Nat.mul_le_mul hpow hfac_d
    have hlhs : ((2 * d + 1) ^ (2 * d + 1) * d.factorial ^ 2) ^ d * d.factorial =
        (2 * d + 1) ^ ((2 * d + 1) * d) * d.factorial ^ (2 * d + 1) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_succ]
    have hrhs : (d ^ (2 * d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial)) ^ d * d ^ d =
        d ^ ((2 * d + 1) * d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial) ^ d := by
      rw [mul_pow, ← pow_mul]
      have hpow_d : d ^ (2 * d * d) * d ^ d = d ^ ((2 * d + 1) * d) := by
        rw [← pow_add]; congr 1; ring
      calc
        d ^ (2 * d * d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial) ^ d * d ^ d
            = (d ^ (2 * d * d) * d ^ d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial) ^ d := by
              ring
        _ = d ^ ((2 * d + 1) * d) * (3 * (2 * d + 1 + 1) * (2 * d + 1).factorial) ^ d := by
              rw [hpow_d]
    rw [hlhs, hrhs] at hprod
    exact hprod

end PEqualNP.Outside.L_lib_705_aux

open PEqualNP.Outside.L_lib_705_aux

theorem PEqualNP.Outside.L_lib_705 :
    ∀ n : ℕ, 2 ≤ n →
      let I := Fin n
      let d := n/2
      let P := fun A : Matrix I I ℝ => Matrix.permanent (fun i j => (A i j)^2)
      (∀ B : Matrix I I ℝ, (∀ i j, 0 ≤ B i j ∧ (d : ℝ)*B i j ≤ 1) →
        (∀ i, (∑ j : I, B i j) = 1) →
        ((d : ℝ)^(n) * B.permanent)^d ≤ (d.factorial : ℝ)^n) ∧
      ∃ U : Matrix I I ℝ, U * U.transpose = 1 ∧
        (∀ i j, (n : ℝ)*(U i j)^2 ≤ 2) ∧ 0 < P U ∧
        (n : ℝ)^n * P U ≤ 3*((n : ℝ)+1)*(n.factorial : ℝ) := by
  intro n hn I d P
  have hd : 0 < d := by dsimp only [d]; omega
  have hdn : d ≤ n := by dsimp only [d]; omega
  have hpart1 : ∀ B : Matrix I I ℝ, (∀ i j, 0 ≤ B i j ∧ (d : ℝ) * B i j ≤ 1) →
      (∀ i, (∑ j : I, B i j) = 1) →
      ((d : ℝ) ^ n * B.permanent) ^ d ≤ (d.factorial : ℝ) ^ n := by
    intro B hB hrow
    rcases capped_permanent_reduction hd hdn B hB hrow with ⟨A, hAcard, hBle⟩
    have hperm_nn : 0 ≤ B.permanent := by
      rw [permanent_eq_row_sum]
      exact Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun i _ => (hB i (σ i)).1
    have h1 : ((d : ℝ) ^ n * B.permanent) ^ d ≤
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∈ A i)).card : ℝ) ^ d :=
      pow_le_pow_left₀ (by positivity) hBle d
    exact h1.trans (bregman_uniform hd A hAcard)
  refine ⟨hpart1, ?_⟩
  rcases hartley_matrix_props hn with ⟨U, hUorth, hUbound⟩
  refine ⟨U, hUorth, hUbound, ?_, ?_⟩
  · have hdet_sq : (Matrix.det U) ^ 2 = 1 := by
      calc
        (Matrix.det U) ^ 2 = Matrix.det U * Matrix.det U.transpose := by
          rw [Matrix.det_transpose, sq]
        _ = Matrix.det (U * U.transpose) := (Matrix.det_mul U U.transpose).symm
        _ = 1 := by rw [hUorth, Matrix.det_one]
    have hdet_ne : Matrix.det U ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega : 2 ≠ 0)] at hdet_sq
      norm_num at hdet_sq
    have hex : ∃ σ : Equiv.Perm (Fin n), (∏ i : Fin n, U (σ i) i) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hdet_ne
      rw [Matrix.det_apply]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [hall σ, smul_zero]
    rcases hex with ⟨σ, hσ⟩
    have hterm_pos : 0 < ∏ i : Fin n, (U (σ i) i) ^ 2 := by
      have hpow : (∏ i : Fin n, U (σ i) i) ^ 2 = ∏ i : Fin n, (U (σ i) i) ^ 2 :=
        (Finset.prod_pow (s := Finset.univ) (n := 2) (f := fun i : Fin n => U (σ i) i)).symm
      rw [← hpow]
      exact sq_pos_of_ne_zero hσ
    change (0 : ℝ) < ∑ τ : Equiv.Perm (Fin n), ∏ i : Fin n, (U (τ i) i) ^ 2
    have hle : (∏ i : Fin n, (U (σ i) i) ^ 2) ≤
        ∑ τ : Equiv.Perm (Fin n), ∏ i : Fin n, (U (τ i) i) ^ 2 :=
      Finset.single_le_sum (f := fun τ : Equiv.Perm (Fin n) => ∏ i : Fin n, (U (τ i) i) ^ 2)
        (fun τ _ => Finset.prod_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ σ)
    linarith
  · let B : Matrix I I ℝ := Matrix.of fun i j => (U i j) ^ 2
    have hB : ∀ i j, 0 ≤ B i j ∧ (d : ℝ) * B i j ≤ 1 := by
      intro i j
      refine ⟨sq_nonneg _, ?_⟩
      have h2d : (2 * (d : ℝ)) ≤ (n : ℝ) := by
        have : 2 * d ≤ n := by dsimp only [d]; omega
        exact_mod_cast this
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hb := hUbound i j
      have hmul : (n : ℝ) * ((d : ℝ) * (U i j) ^ 2) ≤ (n : ℝ) * 1 := by
        calc
          (n : ℝ) * ((d : ℝ) * (U i j) ^ 2) = (d : ℝ) * ((n : ℝ) * (U i j) ^ 2) := by ring
          _ ≤ (d : ℝ) * 2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)
          _ = 2 * (d : ℝ) := by ring
          _ ≤ (n : ℝ) * 1 := by linarith
      exact le_of_mul_le_mul_left hmul hn_pos
    have hrow : ∀ i, (∑ j : I, B i j) = 1 := by
      intro i
      have h1 := congrFun (congrFun hUorth i) i
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h1
      simpa only [B, Matrix.of_apply, sq] using h1
    have hbreg := hpart1 B hB hrow
    have hBperm : B.permanent = P U := rfl
    rw [hBperm] at hbreg
    have hPU_nn : 0 ≤ P U := by
      change (0 : ℝ) ≤ ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, (U (σ i) i) ^ 2
      exact Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun i _ => sq_nonneg _
    have hnat : ((n : ℝ) ^ (n * d)) * (d.factorial : ℝ) ^ n ≤
        ((d : ℝ) ^ (n * d)) * (3 * ((n : ℝ) + 1) * (n.factorial : ℝ)) ^ d := by
      exact_mod_cast nat_ratio_bound hn
    have hpow_le : ((d : ℝ) ^ (n * d)) * ((n : ℝ) ^ n * P U) ^ d ≤
        ((d : ℝ) ^ (n * d)) * (3 * ((n : ℝ) + 1) * (n.factorial : ℝ)) ^ d := by
      calc
        ((d : ℝ) ^ (n * d)) * ((n : ℝ) ^ n * P U) ^ d
            = ((n : ℝ) ^ (n * d)) * ((d : ℝ) ^ n * P U) ^ d := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
        _ ≤ ((n : ℝ) ^ (n * d)) * (d.factorial : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left hbreg (by positivity)
        _ ≤ ((d : ℝ) ^ (n * d)) * (3 * ((n : ℝ) + 1) * (n.factorial : ℝ)) ^ d := hnat
    have hd_pow_pos : (0 : ℝ) < (d : ℝ) ^ (n * d) := pow_pos (Nat.cast_pos.mpr hd) (n * d)
    have hpow_le' : ((n : ℝ) ^ n * P U) ^ d ≤ (3 * ((n : ℝ) + 1) * (n.factorial : ℝ)) ^ d :=
      le_of_mul_le_mul_left hpow_le hd_pow_pos
    exact le_of_pow_le_pow_left₀ (Nat.ne_of_gt hd) (by positivity) hpow_le'
