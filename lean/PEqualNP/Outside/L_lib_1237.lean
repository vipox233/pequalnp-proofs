import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Abel
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1237

section Helpers

private lemma geom_left {R : Type*} [Ring R] (D : R) :
    ∀ n : ℕ, (∑ k ∈ Finset.range n, D ^ k) * (1 - D) = 1 - D ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, add_mul, geom_left D n, mul_sub, mul_one, pow_succ]
    abel

private lemma geom_right {R : Type*} [Ring R] (D : R) :
    ∀ n : ℕ, (1 - D) * (∑ k ∈ Finset.range n, D ^ k) = 1 - D ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, mul_add, geom_right D n, sub_mul, one_mul, pow_succ']
    abel

private lemma strict_upper_pow_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rk : ι → ℕ) (D : Matrix ι ι ℤ)
    (hD : ∀ i j, D i j ≠ 0 → rk i < rk j) :
    ∀ k i j, (D ^ k) i j ≠ 0 → rk i + k ≤ rk j
  | 0, i, j, h => by
    have hij : i = j := by
      by_contra hne
      simp [Matrix.one_apply_ne hne] at h
    subst hij
    omega
  | k + 1, i, j, h => by
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (D ^ k) i m ≠ 0 := left_ne_zero_of_mul hm
    have h2 : D m j ≠ 0 := right_ne_zero_of_mul hm
    have ih := strict_upper_pow_bound rk D hD k i m h1
    have step := hD m j h2
    omega

private lemma unitriangular_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (rk : ι → ℕ) (hB : ∀ i, rk i ≤ B) (M : Matrix ι ι ℤ)
    (hdiag : ∀ i, M i i = 1)
    (hoff : ∀ i j, M i j ≠ 0 → i = j ∨ rk i < rk j) :
    ∃ N : Matrix ι ι ℤ, N * M = 1 ∧ M * N = 1 := by
  let D : Matrix ι ι ℤ := 1 - M
  have hD : ∀ i j, D i j ≠ 0 → rk i < rk j := by
    intro i j h
    by_cases hij : i = j
    · subst hij
      simp [D, hdiag] at h
    · have hM : M i j ≠ 0 := by
        intro h0
        simp [D, Matrix.one_apply_ne hij, h0] at h
      rcases hoff i j hM with rfl | hlt
      · exact absurd rfl hij
      · exact hlt
  have hpow : D ^ (B + 1) = 0 := by
    ext i j
    by_contra hne
    have hlt := strict_upper_pow_bound rk D hD (B + 1) i j hne
    have hbj := hB j
    omega
  refine ⟨∑ k ∈ Finset.range (B + 1), D ^ k, ?_, ?_⟩
  · have hM : M = 1 - D := by simp [D]
    rw [hM, geom_left, hpow, sub_zero]
  · have hM : M = 1 - D := by simp [D]
    rw [hM, geom_right, hpow, sub_zero]

private lemma card_lt_of_ssubset {α : Type*} {s t : Finset α} (hsub : s ⊆ t) (hne : s ≠ t) :
    s.card < t.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

end Helpers

end PEqualNP.Outside.L_lib_1237

theorem PEqualNP.Outside.L_lib_1237 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (l r L R : Nat) (G : Fin L → Finset (Fin L)) (H : Fin R → Finset (Fin R))
  (p : Fin l → Fin L) (s : Fin r → Fin R) (C : Fin l → Finset (Fin r)),
  Function.Injective p → Function.Injective s →
  (∀ v, v ∉ G v) → (∀ u v, v ∈ G u ↔ u ∈ G v) →
  (∀ v, v ∉ H v) → (∀ u v, v ∈ H u ↔ u ∈ H v) →
  let LM := Finset (Fin L)
  let RM := Finset (Fin R)
  let lk := (Finset.univ : Finset (Finset (Fin l))).filter
    (fun S => ∀ i ∈ S, ∀ k ∈ S, p k ∉ G (p i))
  let rk := (Finset.univ : Finset (Finset (Fin r))).filter
    (fun T => ∀ j ∈ T, ∀ k ∈ T, s k ∉ H (s j))
  let compat : Matrix ↥lk ↥rk ℤ := fun S T =>
    if ∀ i ∈ S.val, ∀ j ∈ C i, j ∉ T.val then 1 else 0
  let raw : Matrix LM RM ℤ := fun a d =>
    (((Finset.univ : Finset (LM × RM)).filter (fun z =>
      z.1 ⊆ a ∧ z.2 ⊆ d ∧ (∀ u ∈ z.1, ∀ v ∈ G u, v ∉ z.1) ∧
      (∀ u ∈ z.2, ∀ v ∈ H u, v ∉ z.2) ∧
      ∀ i, p i ∈ z.1 → ∀ j ∈ C i, s j ∉ z.2)).card : ℤ)
  (∃ (A : Matrix LM ↥lk ℤ) (B : Matrix ↥rk RM ℤ)
     (U : Matrix ↥lk LM ℤ) (V : Matrix RM ↥rk ℤ),
     A * compat * B = raw ∧ U * A = 1 ∧ B * V = 1) ∧
  (((∀ i k, p k ∉ G (p i)) ∧ (∀ j k, s k ∉ H (s j))) →
    let unions := (Finset.univ : Finset (Finset (Fin l))).image (fun S => S.biUnion C)
    ∃ (A : Matrix LM ↥unions ℤ) (B : Matrix ↥unions RM ℤ)
      (U : Matrix ↥unions LM ℤ) (V : Matrix RM ↥unions ℤ),
      A * B = raw ∧ U * A = 1 ∧ B * V = 1)) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro l r L R G H p s C hp hs _hG_irref _hG_symm _hH_irref _hH_symm
  intro LM RM lk rk compat raw

  let leftFib (a : LM) (S : ↥lk) : Finset LM :=
    Finset.univ.filter fun x =>
      x ⊆ a ∧ (∀ u ∈ x, ∀ v ∈ G u, v ∉ x) ∧ (∀ i : Fin l, p i ∈ x ↔ i ∈ S.val)
  let rightFib (T : ↥rk) (d : RM) : Finset RM :=
    Finset.univ.filter fun y =>
      y ⊆ d ∧ (∀ u ∈ y, ∀ v ∈ H u, v ∉ y) ∧ (∀ j : Fin r, s j ∈ y ↔ j ∈ T.val)
  let A : Matrix LM ↥lk ℤ := fun a S => ((leftFib a S).card : ℤ)
  let B : Matrix ↥rk RM ℤ := fun T d => ((rightFib T d).card : ℤ)

  have hACB : A * compat * B = raw := by
    ext a d
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]

    let rawSet : Finset (LM × RM) :=
      Finset.univ.filter fun z =>
        z.1 ⊆ a ∧ z.2 ⊆ d ∧ (∀ u ∈ z.1, ∀ v ∈ G u, v ∉ z.1) ∧
        (∀ u ∈ z.2, ∀ v ∈ H u, v ∉ z.2) ∧
        ∀ i, p i ∈ z.1 → ∀ j ∈ C i, s j ∉ z.2
    have hcard :
        (rawSet.card : ℤ) =
          ∑ S : ↥lk, ∑ T : ↥rk,
            ((leftFib a S).card : ℤ) * compat S T * ((rightFib T d).card : ℤ) := by
      have hnat :
          rawSet.card =
            ∑ S : ↥lk, ∑ T : ↥rk,
              if ∀ i ∈ S.val, ∀ j ∈ C i, j ∉ T.val then
                (leftFib a S ×ˢ rightFib T d).card
              else 0 := by
        rw [← Finset.sum_product']
        have hbi :
            rawSet =
              (Finset.univ : Finset (↥lk × ↥rk)).biUnion fun pST =>
                if ∀ i ∈ pST.1.val, ∀ j ∈ C i, j ∉ pST.2.val then
                  leftFib a pST.1 ×ˢ rightFib pST.2 d
                else ∅ := by
          ext ⟨x, y⟩
          simp only [rawSet, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_biUnion, Prod.exists]
          constructor
          · rintro ⟨hxa, hyd, hxG, hyH, hxy⟩
            let S0 : Finset (Fin l) := Finset.univ.filter (fun i => p i ∈ x)
            let T0 : Finset (Fin r) := Finset.univ.filter (fun j => s j ∈ y)
            have hS0 : S0 ∈ lk := by
              simp only [lk, Finset.mem_filter, Finset.mem_univ, true_and, S0]
              intro i hi k hk
              exact hxG (p i) hi (p k) |> fun h => fun hg => h hg hk
            have hT0 : T0 ∈ rk := by
              simp only [rk, Finset.mem_filter, Finset.mem_univ, true_and, T0]
              intro j hj k hk
              exact hyH (s j) hj (s k) |> fun h => fun hh => h hh hk
            refine ⟨⟨S0, hS0⟩, ⟨T0, hT0⟩, ?_⟩
            have hcmp : ∀ i ∈ S0, ∀ j ∈ C i, j ∉ T0 := by
              intro i hi j hj hjt
              simp only [S0, T0, Finset.mem_filter, Finset.mem_univ, true_and] at hi hjt
              exact hxy i hi j hj hjt
            split_ifs with hcmp'
            · simp only [Finset.mem_product, leftFib, rightFib, Finset.mem_filter,
                Finset.mem_univ, true_and, S0, T0]
              exact ⟨⟨hxa, hxG, fun _ => trivial⟩, ⟨hyd, hyH, fun _ => trivial⟩⟩
            · exact absurd hcmp hcmp'
          · rintro ⟨S, T, hmem⟩
            split_ifs at hmem with hcmp
            · simp only [Finset.mem_product, leftFib, rightFib, Finset.mem_filter,
                Finset.mem_univ, true_and] at hmem
              rcases hmem with ⟨⟨hxa, hxG, hxS⟩, ⟨hyd, hyH, hyT⟩⟩
              refine ⟨hxa, hyd, hxG, hyH, ?_⟩
              intro i hi j hj hsy
              exact hcmp i ((hxS i).mp hi) j hj ((hyT j).mp hsy)
            · simp at hmem
        rw [hbi, Finset.card_biUnion]
        · apply Finset.sum_congr rfl
          intro pST _
          split_ifs <;> simp
        · intro p1 _ p2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro ⟨x, y⟩ h1 h2
          dsimp only at h1 h2
          split_ifs at h1 with hc1
          · split_ifs at h2 with hc2
            · simp only [Finset.mem_product, leftFib, rightFib, Finset.mem_filter,
                Finset.mem_univ, true_and] at h1 h2
              have hS : p1.1 = p2.1 := Subtype.ext (by
                ext i; rw [← h1.1.2.2 i, h2.1.2.2 i])
              have hT : p1.2 = p2.2 := Subtype.ext (by
                ext j; rw [← h1.2.2.2 j, h2.2.2.2 j])
              exact hne (Prod.ext hS hT)
            · simp at h2
          · simp at h1
      rw [hnat]
      push_cast
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      simp only [compat]
      split_ifs <;> simp [Finset.card_product]
    simpa only [A, B, raw, rawSet, mul_assoc] using hcard.symm

  have hA_img : ∀ (J S : ↥lk), A (J.val.image p) S = if S.val ⊆ J.val then 1 else 0 := by
    intro J S
    change ((leftFib (J.val.image p) S).card : ℤ) = _
    split_ifs with hSJ
    · have hEq : leftFib (J.val.image p) S = {S.val.image p} := by
        ext x
        simp only [leftFib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hxsub, _, hxS⟩
          ext u
          constructor
          · intro hu
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hxsub hu)
            exact Finset.mem_image_of_mem p ((hxS i).mp hu)
          · intro hu
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
            exact (hxS i).mpr hi
        · rintro rfl
          refine ⟨Finset.image_subset_image hSJ, ?_, ?_⟩
          · intro u hu v hv hvmem
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hvmem
            have hSmem := (Finset.mem_filter.mp S.2).2
            exact hSmem i hi k hk hv
          · intro i
            exact hp.mem_finset_image
      rw [hEq]; simp
    · have hEmpty : leftFib (J.val.image p) S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [leftFib, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        apply hSJ
        intro i hi
        have hpi : p i ∈ J.val.image p := hx.1 ((hx.2.2 i).mpr hi)
        exact hp.mem_finset_image.mp hpi
      rw [hEmpty]; simp

  have hB_img : ∀ (T J : ↥rk), B T (J.val.image s) = if T.val ⊆ J.val then 1 else 0 := by
    intro T J
    change ((rightFib T (J.val.image s)).card : ℤ) = _
    split_ifs with hTJ
    · have hEq : rightFib T (J.val.image s) = {T.val.image s} := by
        ext y
        simp only [rightFib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hysub, _, hyT⟩
          ext u
          constructor
          · intro hu
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hysub hu)
            exact Finset.mem_image_of_mem s ((hyT j).mp hu)
          · intro hu
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
            exact (hyT j).mpr hj
        · rintro rfl
          refine ⟨Finset.image_subset_image hTJ, ?_, ?_⟩
          · intro u hu v hv hvmem
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hvmem
            have hTmem := (Finset.mem_filter.mp T.2).2
            exact hTmem j hj k hk hv
          · intro j
            exact hs.mem_finset_image
      rw [hEq]; simp
    · have hEmpty : rightFib T (J.val.image s) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        simp only [rightFib, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        apply hTJ
        intro j hj
        have hsj : s j ∈ J.val.image s := hy.1 ((hy.2.2 j).mpr hj)
        exact hs.mem_finset_image.mp hsj
      rw [hEmpty]; simp

  let ZL : Matrix ↥lk ↥lk ℤ := fun J S => if S.val ⊆ J.val then 1 else 0
  obtain ⟨NL, hNL_left, _⟩ :=
    PEqualNP.Outside.L_lib_1237.unitriangular_inv l (fun J : ↥lk => l - J.val.card)
      (fun _ => Nat.sub_le l _) ZL
      (fun J => by simp [ZL])
      (fun J S hne => by
        by_cases hJS : J = S
        · exact Or.inl hJS
        · right
          have hsub : S.val ⊆ J.val := by
            by_contra hn; simp [ZL] at hne; exact hn hne
          have hlt := PEqualNP.Outside.L_lib_1237.card_lt_of_ssubset hsub
            (fun h => hJS (Subtype.ext h.symm))
          have hJle : J.val.card ≤ l := by
            simpa using Finset.card_le_univ J.val
          exact Nat.sub_lt_sub_left (lt_of_lt_of_le hlt hJle) hlt)
  let U : Matrix ↥lk LM ℤ := fun K a => ∑ J : ↥lk, if a = J.val.image p then NL K J else 0
  have hUA : U * A = 1 := by
    ext K S
    rw [Matrix.mul_apply]
    have hsum :
        (∑ a : LM, U K a * A a S) = ∑ J : ↥lk, NL K J * ZL J S := by
      simp_rw [U, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J _
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (J.val.image p)]
      simp only [Finset.mem_univ, ↓reduceIte, hA_img, ZL]
    rw [hsum, ← Matrix.mul_apply, hNL_left]

  let ZR : Matrix ↥rk ↥rk ℤ := fun T J => if T.val ⊆ J.val then 1 else 0
  obtain ⟨NR, _, hNR_right⟩ :=
    PEqualNP.Outside.L_lib_1237.unitriangular_inv r (fun J : ↥rk => J.val.card)
      (fun J => by simpa using Finset.card_le_univ J.val) ZR
      (fun J => by simp [ZR])
      (fun T J hne => by
        by_cases hTJ : T = J
        · exact Or.inl hTJ
        · right
          have hsub : T.val ⊆ J.val := by
            by_contra hn; simp [ZR] at hne; exact hn hne
          exact PEqualNP.Outside.L_lib_1237.card_lt_of_ssubset hsub
            (fun h => hTJ (Subtype.ext h)))
  let V : Matrix RM ↥rk ℤ := fun d K => ∑ J : ↥rk, if d = J.val.image s then NR J K else 0
  have hBV : B * V = 1 := by
    ext T K
    rw [Matrix.mul_apply]
    have hsum :
        (∑ d : RM, B T d * V d K) = ∑ J : ↥rk, ZR T J * NR J K := by
      simp_rw [V, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J _
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (J.val.image s)]
      simp only [Finset.mem_univ, ↓reduceIte, hB_img, ZR]
    rw [hsum, ← Matrix.mul_apply, hNR_right]

  refine ⟨⟨A, B, U, V, hACB, hUA, hBV⟩, ?_⟩

  rintro ⟨hGp, hHs⟩
  intro unions

  let P : Matrix ↥lk ↥unions ℤ := fun S u => if S.val.biUnion C = u.val then 1 else 0
  let Q : Matrix ↥unions ↥rk ℤ := fun u T => if ∀ j ∈ u.val, j ∉ T.val then 1 else 0

  have hPQ : P * Q = compat := by
    ext S T
    rw [Matrix.mul_apply]
    have huMem : S.val.biUnion C ∈ unions :=
      Finset.mem_image.mpr ⟨S.val, Finset.mem_univ _, rfl⟩
    let u0 : ↥unions := ⟨S.val.biUnion C, huMem⟩
    have hsimp :
        (∑ u : ↥unions, P S u * Q u T) = Q u0 T := by
      rw [Finset.sum_eq_single u0]
      · simp [P, u0]
      · intro u _ hne
        have hv : S.val.biUnion C ≠ u.val := fun h => hne (Subtype.ext h.symm)
        simp [P, hv]
      · intro h; exact absurd (Finset.mem_univ u0) h
    rw [hsimp]
    simp only [Q, compat, u0, Finset.mem_biUnion]
    congr 1
    exact propext ⟨fun h i hi j hj => h j ⟨i, hi, hj⟩,
      fun h j ⟨i, hi, hj⟩ => h i hi j hj⟩

  have hrep_ex : ∀ u : ↥unions, ∃ S : ↥lk, S.val.biUnion C = u.val := by
    intro u
    obtain ⟨S0, _, hS0⟩ := Finset.mem_image.mp u.2
    have hS0lk : S0 ∈ lk := by
      simp only [lk, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i _ k _
      exact hGp i k
    exact ⟨⟨S0, hS0lk⟩, hS0⟩
  let rep : ↥unions → ↥lk := fun u => (hrep_ex u).choose
  have hrep : ∀ u : ↥unions, (rep u).val.biUnion C = u.val := fun u => (hrep_ex u).choose_spec
  let Rmat : Matrix ↥unions ↥lk ℤ := fun u S => if S = rep u then 1 else 0
  have hRP : Rmat * P = 1 := by
    ext u v
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (rep u)]
    · by_cases huv : u = v
      · subst huv; simp [Rmat, P, hrep]
      · have hval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
        simp [Rmat, P, hrep, hval, Matrix.one_apply_ne huv]
    · intro S _ hne; simp [Rmat, hne]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hcomp_rk : ∀ v : ↥unions, Finset.univ \ v.val ∈ rk := by
    intro v
    simp only [rk, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j _ k _
    exact hHs j k
  let comp : ↥unions → ↥rk := fun v => ⟨Finset.univ \ v.val, hcomp_rk v⟩
  have hQ_comp : ∀ u v : ↥unions, Q u (comp v) = if u.val ⊆ v.val then 1 else 0 := by
    intro u v
    dsimp only [Q]
    split_ifs with h1 h2 h3
    · rfl
    · exfalso
      apply h2
      intro j hj
      have hnot := h1 j hj
      simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hnot
      exact hnot
    · exfalso
      apply h1
      intro j hj hmem
      simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and] at hmem
      exact hmem (h3 hj)
    · rfl
  let Msub : Matrix ↥unions ↥unions ℤ := fun u v => if u.val ⊆ v.val then 1 else 0
  obtain ⟨Nsub, _, hNsub_right⟩ :=
    PEqualNP.Outside.L_lib_1237.unitriangular_inv r (fun u : ↥unions => u.val.card)
      (fun u => by simpa using Finset.card_le_univ u.val) Msub
      (fun u => by simp [Msub])
      (fun u v hne => by
        by_cases huv : u = v
        · exact Or.inl huv
        · right
          have hsub : u.val ⊆ v.val := by
            by_contra hn; simp [Msub] at hne; exact hn hne
          exact PEqualNP.Outside.L_lib_1237.card_lt_of_ssubset hsub
            (fun h => huv (Subtype.ext h)))
  let W : Matrix ↥rk ↥unions ℤ := fun T v => ∑ w : ↥unions, if T = comp w then Nsub w v else 0
  have hQW : Q * W = 1 := by
    ext u v
    rw [Matrix.mul_apply]
    have hsum : (∑ T : ↥rk, Q u T * W T v) = ∑ w : ↥unions, Msub u w * Nsub w v := by
      simp_rw [W, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (comp w)]
      simp only [Finset.mem_univ, ↓reduceIte, hQ_comp, Msub]
    rw [hsum, ← Matrix.mul_apply, hNsub_right]

  refine ⟨A * P, Q * B, Rmat * U, V * W, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P Q B, hPQ, ← Matrix.mul_assoc, hACB]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U A P, hUA, Matrix.one_mul, hRP]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B V W, hBV, Matrix.one_mul, hQW]
