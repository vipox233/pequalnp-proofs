import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1010_aux

private lemma exists_func_vanish_one {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S : Submodule K E) (x : E) (hx : x ∉ S) :
    ∃ f : E →ₗ[K] K, (∀ u ∈ S, f u = 0) ∧ f x = 1 := by
  let qx : E ⧸ S := Submodule.mkQ S x
  have hqx_ne : qx ≠ 0 := by
    intro h0
    exact hx ((Submodule.Quotient.mk_eq_zero S).mp h0)
  let L : Submodule K (E ⧸ S) := Submodule.span K ({qx} : Set (E ⧸ S))
  obtain ⟨C, hLC⟩ := Submodule.exists_isCompl L
  let proj : (E ⧸ S) →ₗ[K] L := Submodule.projectionOnto L C hLC
  let inc : L →ₗ[K] LinearMap.range (LinearMap.toSpanSingleton K (E ⧸ S) qx) :=
    { toFun := fun y => ⟨y.1, by
        have hy := y.2
        rw [Submodule.mem_span_singleton] at hy
        rcases hy with ⟨c, hc⟩
        exact ⟨c, hc⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let coord : L →ₗ[K] K :=
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton K (E ⧸ S) qx |>.rangeRestrict)
      ⟨fun a b hab => by
        have hv : a • qx = b • qx := congrArg Subtype.val hab
        have hsub : (a - b) • qx = 0 := by rw [sub_smul, hv, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 hqx_ne,
       fun ⟨y, hy⟩ => by
        rw [LinearMap.mem_range] at hy
        rcases hy with ⟨c, rfl⟩
        exact ⟨c, rfl⟩⟩).symm.toLinearMap.comp inc
  refine ⟨coord.comp (proj.comp (Submodule.mkQ S)), ?_, ?_⟩
  · intro u hu
    change coord (proj (Submodule.mkQ S u)) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr hu, map_zero, map_zero]
  · simp only [LinearMap.comp_apply]
    have hqxL : qx ∈ L := Submodule.subset_span (Set.mem_singleton qx)
    have hpr : proj qx = ⟨qx, hqxL⟩ := Submodule.projectionOnto_apply_left hLC ⟨qx, hqxL⟩
    change coord (proj qx) = 1
    rw [hpr]
    dsimp only [coord, inc, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Subtype.ext
    change qx = (1 : K) • qx
    rw [one_smul]

private lemma exists_func_vanish_two {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S : Submodule K E) (x y : E) (hx : x ∉ S) (hy : y ∉ S) :
    ∃ f : E →ₗ[K] K, (∀ u ∈ S, f u = 0) ∧ f x = 1 ∧ f y ≠ 0 := by
  obtain ⟨f1, hf1S, hf1x⟩ := exists_func_vanish_one S x hx
  by_cases hf1y : f1 y ≠ 0
  · exact ⟨f1, hf1S, hf1x, hf1y⟩
  · push Not at hf1y
    have hy_not : y ∉ S ⊔ Submodule.span K ({x} : Set E) := by
      intro hmem
      rcases Submodule.mem_sup.mp hmem with ⟨u, hu, w, hw, rfl⟩
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rw [map_add, map_smul, hf1S u hu, zero_add, hf1x, smul_eq_mul, mul_one] at hf1y
      rw [hf1y, zero_smul, add_zero] at hy
      exact hy hu
    obtain ⟨f2, hf2, hf2y⟩ := exists_func_vanish_one (S ⊔ Submodule.span K ({x} : Set E)) y hy_not
    refine ⟨f1 + f2, ?_, ?_, ?_⟩
    · intro u hu
      simp only [LinearMap.add_apply, hf1S u hu, hf2 u (Submodule.mem_sup_left hu), add_zero]
    · simp only [LinearMap.add_apply, hf1x,
        hf2 x (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))), add_zero]
    · simp only [LinearMap.add_apply, hf1y, zero_add, hf2y, ne_eq, one_ne_zero, not_false_eq_true]

private lemma exists_not_mem_two {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S1 S2 : Submodule K E) (h1 : S1 ≠ ⊤) (h2 : S2 ≠ ⊤) :
    ∃ x : E, x ∉ S1 ∧ x ∉ S2 := by
  have hex1 : ∃ x1 : E, x1 ∉ S1 := by
    by_contra hall; push Not at hall
    exact h1 (Submodule.eq_top_iff'.mpr hall)
  have hex2 : ∃ x2 : E, x2 ∉ S2 := by
    by_contra hall; push Not at hall
    exact h2 (Submodule.eq_top_iff'.mpr hall)
  rcases hex1 with ⟨x1, hx1⟩
  rcases hex2 with ⟨x2, hx2⟩
  by_cases hx1_2 : x1 ∉ S2
  · exact ⟨x1, hx1, hx1_2⟩
  · push Not at hx1_2
    by_cases hx2_1 : x2 ∉ S1
    · exact ⟨x2, hx2_1, hx2⟩
    · push Not at hx2_1
      refine ⟨x1 + x2, ?_, ?_⟩
      · intro h; exact hx1 (by simpa using Submodule.sub_mem S1 h hx2_1)
      · intro h; exact hx2 (by simpa using Submodule.sub_mem S2 h hx1_2)

private lemma mulVecLin_add {K : Type*} [Field K] {q r : ℕ}
    (A B : Matrix (Fin q) (Fin r) K) :
    (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by
  apply LinearMap.ext; intro v; funext i
  change (∑ j : Fin r, (A i j + B i j) * v j) =
    (∑ j : Fin r, A i j * v j) + ∑ j : Fin r, B i j * v j
  simp only [add_mul, Finset.sum_add_distrib]

private lemma mulVecLin_sub {K : Type*} [Field K] {q r : ℕ}
    (A B : Matrix (Fin q) (Fin r) K) :
    (A - B).mulVecLin = A.mulVecLin - B.mulVecLin := by
  apply LinearMap.ext; intro v; funext i
  change (∑ j : Fin r, (A i j - B i j) * v j) =
    (∑ j : Fin r, A i j * v j) - ∑ j : Fin r, B i j * v j
  simp only [sub_mul, Finset.sum_sub_distrib]

private lemma rank_add_le {K : Type*} [Field K] {q r : ℕ}
    (A B : Matrix (Fin q) (Fin r) K) :
    Matrix.rank (A + B) ≤ Matrix.rank A + Matrix.rank B := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    rw [mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have h1 := Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) + Module.finrank K (LinearMap.range B.mulVecLin)
  omega

private lemma rank_elim_eq_finrank_sup {K : Type*} [Field K] {q r : ℕ}
    (A J : Matrix (Fin q) (Fin r) K) :
    Matrix.rank (fun i z => Sum.elim (A i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) =
      Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range J.mulVecLin) := by
  let M : Matrix (Fin q) (Fin r ⊕ Fin r) K := fun i z => Sum.elim (A i) (J i) z
  change Module.finrank K (LinearMap.range M.mulVecLin) = _
  have hrange : LinearMap.range M.mulVecLin = LinearMap.range A.mulVecLin ⊔ LinearMap.range J.mulVecLin := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      have hsplit : M.mulVecLin w =
          A.mulVecLin (fun j => w (Sum.inl j)) + J.mulVecLin (fun j => w (Sum.inr j)) := by
        funext i
        change (∑ z : Fin r ⊕ Fin r, M i z * w z) =
          (∑ j : Fin r, A i j * w (Sum.inl j)) + ∑ j : Fin r, J i j * w (Sum.inr j)
        rw [Fintype.sum_sum_type]
        rfl
      rw [hsplit]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    · intro hy
      rcases Submodule.mem_sup.mp hy with ⟨_, ⟨x1, rfl⟩, _, ⟨x2, rfl⟩, rfl⟩
      refine ⟨Sum.elim x1 x2, ?_⟩
      funext i
      change (∑ z : Fin r ⊕ Fin r, M i z * Sum.elim x1 x2 z) =
        (∑ j : Fin r, A i j * x1 j) + ∑ j : Fin r, J i j * x2 j
      rw [Fintype.sum_sum_type]
      rfl
  rw [hrange]

private lemma rank_one_matrix {K : Type*} [Field K] {q r : ℕ}
    (u : Fin q → K) (f : (Fin r → K) →ₗ[K] K) :
    let B : Matrix (Fin q) (Fin r) K := fun i j => u i * f (Pi.single j 1)
    B.mulVecLin = (LinearMap.toSpanSingleton K (Fin q → K) u).comp f := by
  intro B
  apply LinearMap.ext; intro v; funext i
  change (∑ j : Fin r, u i * f (Pi.single j 1) * v j) = f v * u i
  have hfv : f v = ∑ j : Fin r, v j * f (Pi.single j 1) := by
    have hv : v = ∑ j : Fin r, v j • Pi.single j (1 : K) := by
      funext j0
      rw [Finset.sum_apply, Finset.sum_eq_single j0]
      · simp
      · intro j _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
  rw [hfv, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => by ring)

private lemma rank_update_dist {K : Type*} [Field K] {q r : ℕ}
    (A J : Matrix (Fin q) (Fin r) K)
    (x : Fin r → K) (f : (Fin r → K) →ₗ[K] K)
    (hfF : ∀ u ∈ LinearMap.ker (A.mulVecLin - J.mulVecLin), f u = 0)
    (hfx : f x = 1) :
    let w : Fin q → K := J.mulVecLin x - A.mulVecLin x
    let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
    let A' : Matrix (Fin q) (Fin r) K := A + B
    Matrix.rank (A - A') = 1 ∧ Matrix.rank (A' - J) = Matrix.rank (A - J) - 1 := by
  dsimp only
  let w : Fin q → K := J.mulVecLin x - A.mulVecLin x
  let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
  let A' : Matrix (Fin q) (Fin r) K := A + B
  have hx_notF : x ∉ LinearMap.ker (A.mulVecLin - J.mulVecLin) := by
    intro hxF
    have h0 := hfF x hxF
    rw [hfx] at h0
    exact one_ne_zero h0
  have hw_ne : w ≠ 0 := by
    intro h0
    apply hx_notF
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h0).symm
  have hB_lin : B.mulVecLin = (LinearMap.toSpanSingleton K (Fin q → K) w).comp f :=
    rank_one_matrix w f
  have hA'_lin : A'.mulVecLin = A.mulVecLin + B.mulVecLin := mulVecLin_add A B
  have hrank1 : Matrix.rank (A - A') = 1 := by
    have hsub : A - A' = -B := by
      dsimp only [A']; abel
    rw [hsub]
    have hneg_lin : (-B).mulVecLin = -B.mulVecLin := by
      apply LinearMap.ext; intro v; funext i
      change (∑ j : Fin r, (-B i j) * v j) = -(∑ j : Fin r, B i j * v j)
      simp [Finset.sum_neg_distrib]
    change Module.finrank K (LinearMap.range (-B).mulVecLin) = 1
    rw [hneg_lin, LinearMap.range_neg, hB_lin]
    have hrange : LinearMap.range ((LinearMap.toSpanSingleton K (Fin q → K) w).comp f) =
        Submodule.span K ({w} : Set (Fin q → K)) := by
      ext y
      simp only [LinearMap.mem_range, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
        Submodule.mem_span_singleton]
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨f v, rfl⟩
      · rintro ⟨c, rfl⟩; exact ⟨c • x, by rw [map_smul, hfx, smul_eq_mul, mul_one]⟩
    rw [hrange, finrank_span_singleton hw_ne]
  have hrank_dec : Matrix.rank (A' - J) = Matrix.rank (A - J) - 1 := by
    have hker_lt : LinearMap.ker (A.mulVecLin - J.mulVecLin) <
        LinearMap.ker (A'.mulVecLin - J.mulVecLin) := by
      rw [lt_iff_le_and_ne]
      constructor
      · intro u hu
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hA'_lin, LinearMap.add_apply, hB_lin,
          LinearMap.comp_apply, hfF u hu, map_zero, add_zero]
        exact LinearMap.mem_ker.mp hu
      · intro heq
        have hx' : x ∈ LinearMap.ker (A'.mulVecLin - J.mulVecLin) := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, hA'_lin, LinearMap.add_apply, hB_lin,
            LinearMap.comp_apply, hfx, LinearMap.toSpanSingleton_apply, one_smul]
          dsimp only [w]
          abel
        exact hx_notF (heq.symm ▸ hx')
    have hker_dim : Module.finrank K (LinearMap.ker (A.mulVecLin - J.mulVecLin)) <
        Module.finrank K (LinearMap.ker (A'.mulVecLin - J.mulVecLin)) :=
      Submodule.finrank_lt_finrank_of_lt hker_lt
    have hrn1 := LinearMap.finrank_range_add_finrank_ker (A.mulVecLin - J.mulVecLin)
    have hrn2 := LinearMap.finrank_range_add_finrank_ker (A'.mulVecLin - J.mulVecLin)
    have hlin1 : (A - J).mulVecLin = A.mulVecLin - J.mulVecLin := mulVecLin_sub A J
    have hlin2 : (A' - J).mulVecLin = A'.mulVecLin - J.mulVecLin := mulVecLin_sub A' J
    have hle1 : Matrix.rank (A' - J) + 1 ≤ Matrix.rank (A - J) := by
      change Module.finrank K (LinearMap.range (A' - J).mulVecLin) + 1 ≤
        Module.finrank K (LinearMap.range (A - J).mulVecLin)
      rw [hlin1, hlin2]
      omega
    have hge1 : Matrix.rank (A - J) ≤ 1 + Matrix.rank (A' - J) := by
      have hsplit : A - J = (A - A') + (A' - J) := by abel
      calc Matrix.rank (A - J)
          = Matrix.rank ((A - A') + (A' - J)) := by rw [hsplit]
        _ ≤ Matrix.rank (A - A') + Matrix.rank (A' - J) := rank_add_le _ _
        _ = 1 + Matrix.rank (A' - J) := by rw [hrank1]
    omega
  exact ⟨hrank1, hrank_dec⟩

private lemma exists_step {K : Type*} [Field K] {q r : ℕ}
    (A J : Matrix (Fin q) (Fin r) K) (hpos : 0 < Matrix.rank (A - J)) :
    let size := fun (M : Matrix (Fin q) (Fin r) K) =>
      Matrix.rank (fun i z => Sum.elim (M i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K)
    ∃ A' : Matrix (Fin q) (Fin r) K,
      Matrix.rank (A - A') = 1 ∧
      Matrix.rank (A' - J) = Matrix.rank (A - J) - 1 ∧
      size A' - Matrix.rank A' = size A - Matrix.rank A - 1 ∧
      size A' - Matrix.rank J = size A - Matrix.rank J - 1 := by
  dsimp only
  let LA := A.mulVecLin
  let LJ := J.mulVecLin
  let imA := LinearMap.range LA
  let imJ := LinearMap.range LJ
  let F := LinearMap.ker (LA - LJ)
  let Z := imA ⊓ imJ
  have hrankA_eq : Module.finrank K imA = Matrix.rank A := rfl
  have hmod : ∀ M : Matrix (Fin q) (Fin r) K,
      Module.finrank K ↥(LinearMap.range M.mulVecLin ⊔ imJ) +
        Module.finrank K ↥(LinearMap.range M.mulVecLin ⊓ imJ) =
      Matrix.rank M + Matrix.rank J := by
    intro M
    exact Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range M.mulVecLin) imJ
  have hF_ne_top : F ≠ ⊤ := by
    intro htop
    have hzero : Module.finrank K (LinearMap.range (A - J).mulVecLin) = 0 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (LA - LJ)
      rw [mulVecLin_sub]
      change Module.finrank K (LinearMap.range (LA - LJ)) = 0
      rw [show LinearMap.ker (LA - LJ) = F from rfl, htop, finrank_top] at hrn
      omega
    exact absurd hzero (ne_of_gt hpos)
  by_cases hJle : imJ ≤ imA
  · by_cases hAle : imA ≤ imJ
    · have him_eq : imA = imJ := le_antisymm hAle hJle
      have hszA : Module.finrank K ↥(imA ⊔ imJ) = Matrix.rank A := by
        rw [him_eq, sup_idem, ← him_eq]; rfl
      have hszJ : Module.finrank K ↥(imA ⊔ imJ) = Matrix.rank J := by
        rw [him_eq, sup_idem]; rfl
      have hex_x : ∃ x : Fin r → K, x ∉ F := by
        by_contra hall; push Not at hall
        exact hF_ne_top (Submodule.eq_top_iff'.mpr hall)
      rcases hex_x with ⟨x, hxF⟩
      have hex_f : ∃ f : (Fin r → K) →ₗ[K] K, (∀ u ∈ F, f u = 0) ∧ f x = 1 ∧
          (let w := LJ x - LA x
           let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
           LinearMap.range (A + B).mulVecLin = imA) := by
        by_cases hker : LinearMap.ker LA ≤ F
        · have hLJ_mem : LJ x ∈ imA := him_eq ▸ ⟨x, rfl⟩
          rcases hLJ_mem with ⟨y, hy⟩
          have hyF : y ∉ F := by
            intro hyin
            have hLJy : LJ y = LA y := (sub_eq_zero.mp (LinearMap.mem_ker.mp hyin)).symm
            have hkerJ : y - x ∈ LinearMap.ker LJ := by
              rw [LinearMap.mem_ker, map_sub, hLJy, hy, sub_self]
            have hker_eq : LinearMap.ker LA = LinearMap.ker LJ := by
              have hle_J : LinearMap.ker LA ≤ LinearMap.ker LJ := by
                intro u hu
                have huF := hker hu
                have h1 : LA u - LJ u = 0 := LinearMap.mem_ker.mp huF
                rw [LinearMap.mem_ker.mp hu, zero_sub, neg_eq_zero] at h1
                exact h1
              have hdim_eq : Module.finrank K (LinearMap.ker LA) = Module.finrank K (LinearMap.ker LJ) := by
                have h1 := LinearMap.finrank_range_add_finrank_ker LA
                have h2 := LinearMap.finrank_range_add_finrank_ker LJ
                have h3 : Module.finrank K (LinearMap.range LA) = Module.finrank K (LinearMap.range LJ) := by
                  change Module.finrank K imA = Module.finrank K imJ; rw [him_eq]
                omega
              exact Submodule.eq_of_le_of_finrank_eq hle_J hdim_eq
            have hsubF : y - x ∈ F := hker (hker_eq.symm ▸ hkerJ)
            exact hxF (by simpa using Submodule.sub_mem F hyin hsubF)
          obtain ⟨f, hfF, hfx, hfy⟩ := exists_func_vanish_two F x y hxF hyF
          refine ⟨f, hfF, hfx, ?_⟩
          dsimp only
          let w := LJ x - LA x
          let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
          have hA'_lin : (A + B).mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
            rw [mulVecLin_add, rank_one_matrix w f]
          apply le_antisymm
          · rintro _ ⟨v, rfl⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
            have hw_mem : w ∈ imA := Submodule.sub_mem imA (him_eq ▸ ⟨x, rfl⟩) ⟨x, rfl⟩
            exact Submodule.add_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ hw_mem)
          · have hw_in : w ∈ LinearMap.range (A + B).mulVecLin := by
              refine ⟨(f y)⁻¹ • (y - x), ?_⟩
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
                map_smul, map_sub, map_smul, map_sub, hy, hfx]
              have hcalc : (f y)⁻¹ • (LJ x - LA x) + ((f y)⁻¹ * (f y - 1)) • (LJ x - LA x) = LJ x - LA x := by
                rw [← add_smul]
                have hsc : (f y)⁻¹ + (f y)⁻¹ * (f y - 1) = 1 := by
                  field_simp [hfy]; ring
                rw [hsc, one_smul]
              simpa [w, smul_eq_mul] using hcalc
            rintro _ ⟨v, rfl⟩
            have h1 : (A + B).mulVecLin v - f v • w = LA v := by
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
              abel
            rw [← h1]
            exact Submodule.sub_mem _ ⟨v, rfl⟩ (Submodule.smul_mem _ _ hw_in)
        · have hex_u0 : ∃ u0 ∈ LinearMap.ker LA, u0 ∉ F := by
            by_contra hall; push Not at hall
            exact hker hall
          rcases hex_u0 with ⟨u0, hu0K, hu0F⟩
          obtain ⟨f, hfF, hfx, hfu0⟩ := exists_func_vanish_two F x u0 hxF hu0F
          refine ⟨f, hfF, hfx, ?_⟩
          dsimp only
          let w := LJ x - LA x
          let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
          have hA'_lin : (A + B).mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
            rw [mulVecLin_add, rank_one_matrix w f]
          apply le_antisymm
          · rintro _ ⟨v, rfl⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
            have hw_mem : w ∈ imA := Submodule.sub_mem imA (him_eq ▸ ⟨x, rfl⟩) ⟨x, rfl⟩
            exact Submodule.add_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ hw_mem)
          · have hw_in : w ∈ LinearMap.range (A + B).mulVecLin := by
              refine ⟨(f u0)⁻¹ • u0, ?_⟩
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
                map_smul, LinearMap.mem_ker.mp hu0K, smul_zero, zero_add, map_smul, smul_eq_mul,
                inv_mul_cancel₀ hfu0, one_smul]
            rintro _ ⟨v, rfl⟩
            have h1 : (A + B).mulVecLin v - f v • w = LA v := by
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
              abel
            rw [← h1]
            exact Submodule.sub_mem _ ⟨v, rfl⟩ (Submodule.smul_mem _ _ hw_in)
      rcases hex_f with ⟨f, hfF, hfx, him_A'⟩
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hdist := rank_update_dist A J x f hfF hfx
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) -
            Module.finrank K (LinearMap.range A'.mulVecLin) =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank A - 1
        rw [him_A', hszA]
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank J - 1
        rw [him_A', hszJ]
        omega
    · have hex_x : ∃ x : Fin r → K, LA x ∉ imJ := by
        by_contra hall; push Not at hall
        apply hAle
        rintro _ ⟨x, rfl⟩; exact hall x
      rcases hex_x with ⟨x, hxJ⟩
      obtain ⟨g, hgJ, hgLAx⟩ := exists_func_vanish_one imJ (LA x) hxJ
      let f : (Fin r → K) →ₗ[K] K := g.comp LA
      have hfF : ∀ u ∈ F, f u = 0 := by
        intro u hu
        have heq : LA u = LJ u := sub_eq_zero.mp (LinearMap.mem_ker.mp hu)
        dsimp only [f]; rw [LinearMap.comp_apply, heq]; exact hgJ _ ⟨u, rfl⟩
      have hfx : f x = 1 := hgLAx
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hA'_lin : A'.mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
        rw [mulVecLin_add, rank_one_matrix w f]
      let Hg : Submodule K (Fin q → K) := LinearMap.ker g ⊓ imA
      have hJleHg : imJ ≤ Hg := le_inf (fun y hy => LinearMap.mem_ker.mpr (hgJ y hy)) hJle
      have himA'_eq : LinearMap.range A'.mulVecLin = Hg := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have h1 : LA v + g (LA v) • (LJ x - LA x) = (LA v - g (LA v) • LA x) + g (LA v) • LJ x := by
            rw [smul_sub]; abel
          change LA v + g (LA v) • (LJ x - LA x) ∈ Hg
          rw [h1]
          refine Submodule.add_mem Hg ?_ (Submodule.smul_mem Hg _ (hJleHg ⟨x, rfl⟩))
          refine ⟨?_, Submodule.sub_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ ⟨x, rfl⟩)⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hgLAx, smul_eq_mul, mul_one, sub_self]
        · intro y hy
          rcases hy.2 with ⟨v, rfl⟩
          refine ⟨v, ?_⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have hgv : g (LA v) = 0 := LinearMap.mem_ker.mp hy.1
          change LA v + g (LA v) • w = LA v
          rw [hgv, zero_smul, add_zero]
      have hHg_dim : Module.finrank K Hg + 1 = Matrix.rank A := by
        let gA : imA →ₗ[K] K := g.comp imA.subtype
        have hgA_surj : Function.Surjective gA := by
          intro c
          refine ⟨⟨c • LA x, Submodule.smul_mem imA c ⟨x, rfl⟩⟩, ?_⟩
          change g (c • LA x) = c
          rw [map_smul, hgLAx, smul_eq_mul, mul_one]
        have hker_dim : Module.finrank K (LinearMap.ker gA) = Module.finrank K Hg := by
          let eK : LinearMap.ker gA ≃ₗ[K] Hg :=
            { toFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
              invFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          exact eK.finrank_eq
        have hrn := LinearMap.finrank_range_add_finrank_ker gA
        rw [LinearMap.range_eq_top.mpr hgA_surj, finrank_top, Module.finrank_self, hker_dim] at hrn
        change Module.finrank K Hg + 1 = Module.finrank K imA
        omega
      have hdist := rank_update_dist A J x f hfF hfx
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) -
            Module.finrank K (LinearMap.range A'.mulVecLin) =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank A - 1
        rw [himA'_eq, sup_eq_left.mpr hJleHg, sup_eq_left.mpr hJle]
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank J - 1
        rw [himA'_eq, sup_eq_left.mpr hJleHg, sup_eq_left.mpr hJle]
        have hJleA_dim : Matrix.rank J ≤ Matrix.rank A := Submodule.finrank_mono hJle
        have hJleHg_dim : Matrix.rank J ≤ Module.finrank K Hg := Submodule.finrank_mono hJleHg
        omega
  · by_cases hAle : imA ≤ imJ
    · have hex_x : ∃ x : Fin r → K, LJ x ∉ imA := by
        by_contra hall; push Not at hall
        apply hJle
        rintro _ ⟨x, rfl⟩; exact hall x
      rcases hex_x with ⟨x, hxA⟩
      have hxF : x ∉ F := by
        intro hx; exact hxA (by rw [← sub_eq_zero.mp (LinearMap.mem_ker.mp hx)]; exact ⟨x, rfl⟩)
      have hdim_lt : Module.finrank K imA < Module.finrank K imJ :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hAle (fun h => hJle h.symm.le))
      have hker_lt : Module.finrank K (LinearMap.ker LJ) < Module.finrank K (LinearMap.ker LA) := by
        have h1 := LinearMap.finrank_range_add_finrank_ker LA
        have h2 := LinearMap.finrank_range_add_finrank_ker LJ
        change Module.finrank K (LinearMap.range LA) < Module.finrank K (LinearMap.range LJ) at hdim_lt
        omega
      have hex_u0 : ∃ u0 ∈ LinearMap.ker LA, u0 ∉ F := by
        by_contra hall; push Not at hall
        have hle : LinearMap.ker LA ≤ LinearMap.ker LJ := by
          intro u hu
          have huF := hall u hu
          have h1 : LA u - LJ u = 0 := LinearMap.mem_ker.mp huF
          rw [LinearMap.mem_ker.mp hu, zero_sub, neg_eq_zero] at h1
          exact h1
        have := Submodule.finrank_mono hle
        omega
      rcases hex_u0 with ⟨u0, hu0K, hu0F⟩
      obtain ⟨f, hfF, hfx, hfu0⟩ := exists_func_vanish_two F x u0 hxF hu0F
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hA'_lin : A'.mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
        rw [mulVecLin_add, rank_one_matrix w f]
      have himA'_eq : LinearMap.range A'.mulVecLin = imA ⊔ Submodule.span K ({LJ x} : Set (Fin q → K)) := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have h1 : LA v + f v • (LJ x - LA x) = (LA v - f v • LA x) + f v • LJ x := by
            rw [smul_sub]; abel
          change LA v + f v • (LJ x - LA x) ∈ _
          rw [h1]
          exact Submodule.add_mem_sup
            (Submodule.sub_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ ⟨x, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
        · have hw_in : w ∈ LinearMap.range A'.mulVecLin := by
            refine ⟨(f u0)⁻¹ • u0, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
              map_smul, LinearMap.mem_ker.mp hu0K, smul_zero, zero_add, map_smul, smul_eq_mul,
              inv_mul_cancel₀ hfu0, one_smul]
          refine sup_le ?_ ?_
          · rintro _ ⟨v, rfl⟩
            have h1 : A'.mulVecLin v - f v • w = LA v := by
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
              abel
            rw [← h1]
            exact Submodule.sub_mem _ ⟨v, rfl⟩ (Submodule.smul_mem _ _ hw_in)
          · rw [Submodule.span_singleton_le_iff_mem]
            refine ⟨x, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
              hfx, one_smul]
            dsimp only [w]
            abel
      have himA'_leJ : LinearMap.range A'.mulVecLin ≤ imJ := by
        rw [himA'_eq]
        exact sup_le hAle ((Submodule.span_singleton_le_iff_mem (LJ x) imJ).mpr ⟨x, rfl⟩)
      have himA'_dim : Matrix.rank A' = Matrix.rank A + 1 := by
        change Module.finrank K (LinearMap.range A'.mulVecLin) = Module.finrank K imA + 1
        rw [himA'_eq]
        have hinf : imA ⊓ Submodule.span K ({LJ x} : Set (Fin q → K)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          rcases Submodule.mem_span_singleton.mp hy.2 with ⟨c, rfl⟩
          by_cases hc : c = 0
          · rw [hc, zero_smul]; exact Submodule.zero_mem ⊥
          · exfalso
            have hmem : LJ x ∈ imA := by
              have := Submodule.smul_mem imA c⁻¹ hy.1
              rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
            exact hxA hmem
        have hLJ_ne : LJ x ≠ 0 := fun h0 => hxA (h0 ▸ Submodule.zero_mem imA)
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq imA (Submodule.span K ({LJ x} : Set (Fin q → K)))
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hLJ_ne] at hsup
        exact hsup
      have hdist := rank_update_dist A J x f hfF hfx
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank A' =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank A - 1
        rw [sup_eq_right.mpr himA'_leJ, sup_eq_right.mpr hAle, himA'_dim]
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank J - 1
        rw [sup_eq_right.mpr himA'_leJ, sup_eq_right.mpr hAle]
        change Matrix.rank J - Matrix.rank J = Matrix.rank J - Matrix.rank J - 1
        omega
    · let S1 : Submodule K (Fin r → K) := Z.comap LA
      let S2 : Submodule K (Fin r → K) := Z.comap LJ
      have hS1_ne : S1 ≠ ⊤ := by
        intro htop
        apply hAle
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ S1 := htop ▸ Submodule.mem_top
        exact hx.2
      have hS2_ne : S2 ≠ ⊤ := by
        intro htop
        apply hJle
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ S2 := htop ▸ Submodule.mem_top
        exact hx.1
      obtain ⟨x, hx1, hx2⟩ := exists_not_mem_two S1 S2 hS1_ne hS2_ne
      have hxLA : LA x ∉ Z := hx1
      have hxLJ : LJ x ∉ Z := hx2
      obtain ⟨g, hgZ, hgLAx⟩ := exists_func_vanish_one Z (LA x) hxLA
      let f : (Fin r → K) →ₗ[K] K := g.comp LA
      have hfF : ∀ u ∈ F, f u = 0 := by
        intro u hu
        have heq : LA u = LJ u := sub_eq_zero.mp (LinearMap.mem_ker.mp hu)
        dsimp only [f]; rw [LinearMap.comp_apply]
        exact hgZ (LA u) ⟨⟨u, rfl⟩, heq ▸ ⟨u, rfl⟩⟩
      have hfx : f x = 1 := hgLAx
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hA'_lin : A'.mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
        rw [mulVecLin_add, rank_one_matrix w f]
      let Hg : Submodule K (Fin q → K) := LinearMap.ker g ⊓ imA
      have hZleHg : Z ≤ Hg := le_inf (fun y hy => LinearMap.mem_ker.mpr (hgZ y hy)) inf_le_left
      have himA'_eq : LinearMap.range A'.mulVecLin = Hg ⊔ Submodule.span K ({LJ x} : Set (Fin q → K)) := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have h1 : LA v + g (LA v) • (LJ x - LA x) = (LA v - g (LA v) • LA x) + g (LA v) • LJ x := by
            rw [smul_sub]; abel
          change LA v + g (LA v) • (LJ x - LA x) ∈ _
          rw [h1]
          refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
          refine ⟨?_, Submodule.sub_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ ⟨x, rfl⟩)⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hgLAx, smul_eq_mul, mul_one, sub_self]
        · refine sup_le ?_ ?_
          · intro y hy
            rcases hy.2 with ⟨v, rfl⟩
            refine ⟨v, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
            have hgv : g (LA v) = 0 := LinearMap.mem_ker.mp hy.1
            change LA v + g (LA v) • w = LA v
            rw [hgv, zero_smul, add_zero]
          · rw [Submodule.span_singleton_le_iff_mem]
            refine ⟨x, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
              hfx, one_smul]
            dsimp only [w]
            abel
      have hHg_dim : Module.finrank K Hg + 1 = Matrix.rank A := by
        let gA : imA →ₗ[K] K := g.comp imA.subtype
        have hgA_surj : Function.Surjective gA := by
          intro c
          refine ⟨⟨c • LA x, Submodule.smul_mem imA c ⟨x, rfl⟩⟩, ?_⟩
          change g (c • LA x) = c
          rw [map_smul, hgLAx, smul_eq_mul, mul_one]
        have hker_dim : Module.finrank K (LinearMap.ker gA) = Module.finrank K Hg := by
          let eK : LinearMap.ker gA ≃ₗ[K] Hg :=
            { toFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
              invFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          exact eK.finrank_eq
        have hrn := LinearMap.finrank_range_add_finrank_ker gA
        rw [LinearMap.range_eq_top.mpr hgA_surj, finrank_top, Module.finrank_self, hker_dim] at hrn
        change Module.finrank K Hg + 1 = Module.finrank K imA
        omega
      have hLJ_notHg : LJ x ∉ Hg := fun h => hxLJ ⟨h.2, ⟨x, rfl⟩⟩
      have hLJ_ne : LJ x ≠ 0 := fun h0 => hxLJ (h0 ▸ Submodule.zero_mem Z)
      have himA'_dim : Matrix.rank A' = Matrix.rank A := by
        change Module.finrank K (LinearMap.range A'.mulVecLin) = Matrix.rank A
        rw [himA'_eq]
        have hinf : Hg ⊓ Submodule.span K ({LJ x} : Set (Fin q → K)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          rcases Submodule.mem_span_singleton.mp hy.2 with ⟨c, rfl⟩
          by_cases hc : c = 0
          · rw [hc, zero_smul]; exact Submodule.zero_mem ⊥
          · exfalso
            have hmem : LJ x ∈ Hg := by
              have := Submodule.smul_mem Hg c⁻¹ hy.1
              rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
            exact hLJ_notHg hmem
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq Hg (Submodule.span K ({LJ x} : Set (Fin q → K)))
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hLJ_ne] at hsup
        omega
      have hZ'_eq : LinearMap.range A'.mulVecLin ⊓ imJ = Z ⊔ Submodule.span K ({LJ x} : Set (Fin q → K)) := by
        rw [himA'_eq]
        apply le_antisymm
        · intro y hy
          rcases Submodule.mem_sup.mp hy.1 with ⟨h, hh, s, hs, rfl⟩
          rcases Submodule.mem_span_singleton.mp hs with ⟨c, rfl⟩
          have hhJ : h ∈ imJ := by
            have := Submodule.sub_mem imJ hy.2 (Submodule.smul_mem imJ c ⟨x, rfl⟩)
            simpa using this
          exact Submodule.add_mem_sup ⟨hh.2, hhJ⟩ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _)))
        · exact sup_le (le_inf (le_trans hZleHg le_sup_left) inf_le_right)
            (le_inf le_sup_right ((Submodule.span_singleton_le_iff_mem (LJ x) imJ).mpr ⟨x, rfl⟩))
      have hZ'_dim : Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊓ imJ) = Module.finrank K Z + 1 := by
        rw [hZ'_eq]
        have hinf : Z ⊓ Submodule.span K ({LJ x} : Set (Fin q → K)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          rcases Submodule.mem_span_singleton.mp hy.2 with ⟨c, rfl⟩
          by_cases hc : c = 0
          · rw [hc, zero_smul]; exact Submodule.zero_mem ⊥
          · exfalso
            have hmem : LJ x ∈ Z := by
              have := Submodule.smul_mem Z c⁻¹ hy.1
              rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
            exact hxLJ hmem
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq Z (Submodule.span K ({LJ x} : Set (Fin q → K)))
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hLJ_ne] at hsup
        exact hsup
      have hdist := rank_update_dist A J x f hfF hfx
      have hmodA := hmod A
      have hmodA' := hmod A'
      have hZ_lt_A : Module.finrank K Z < Matrix.rank A :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left
          (fun h => hAle (by change A.mulVecLin.range ≤ imJ; rw [← h]; exact inf_le_right)))
      have hZ_lt_J : Module.finrank K Z < Matrix.rank J :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_right
          (fun h => hJle (by change J.mulVecLin.range ≤ imA; rw [← h]; exact inf_le_left)))
      have hZ_def : Module.finrank K ↥(A.mulVecLin.range ⊓ imJ) = Module.finrank K Z := rfl
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(A'.mulVecLin.range ⊔ imJ) - Matrix.rank A' =
          Module.finrank K ↥(A.mulVecLin.range ⊔ imJ) - Matrix.rank A - 1
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(A'.mulVecLin.range ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(A.mulVecLin.range ⊔ imJ) - Matrix.rank J - 1
        omega

private lemma path_exists_aux {K : Type*} [Field K] {q r : ℕ} :
    ∀ (d : ℕ) (H J : Matrix (Fin q) (Fin r) K),
      Matrix.rank (H - J) = d →
      let size := fun (A : Matrix (Fin q) (Fin r) K) =>
        Matrix.rank (fun i z => Sum.elim (A i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K)
      ∃ P : Fin (d + 1) → Matrix (Fin q) (Fin r) K,
        P 0 = H ∧ P (Fin.last d) = J ∧
        (∀ i j : Fin (d + 1), i ≤ j → Matrix.rank (P i - P j) = j.val - i.val) ∧
        ∀ i : Fin (d + 1),
          size (P i) - Matrix.rank (P i) = size H - Matrix.rank H - i.val ∧
          size (P i) - Matrix.rank J = size H - Matrix.rank J - i.val := by
  intro d
  induction d with
  | zero =>
    intro H J hd
    dsimp only
    have hHJ : H = J := by
      have h0 : LinearMap.range (H - J).mulVecLin = ⊥ :=
        Submodule.finrank_eq_zero.mp hd
      have hlin : (H - J).mulVecLin = 0 := LinearMap.range_eq_bot.mp h0
      have hsub0 : H - J = 0 := by
        ext i j
        have hv := congrFun (LinearMap.congr_fun hlin (Pi.single j 1)) i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using hv
      exact sub_eq_zero.mp hsub0
    refine ⟨fun _ => H, rfl, hHJ, ?_, ?_⟩
    · intro i j _
      simp
    · intro i
      simp
  | succ d ih =>
    intro H J hd
    dsimp only
    obtain ⟨H', hHH', hH'J, hdefJ, hdefA⟩ := exists_step H J (by omega)
    rw [hd] at hH'J
    have hH'J_eq : Matrix.rank (H' - J) = d := by omega
    obtain ⟨P', hP'0, hP'last, hP'dist, hP'def⟩ := ih H' J hH'J_eq
    let P : Fin (d + 2) → Matrix (Fin q) (Fin r) K := fun i =>
      Fin.cases H P' i
    refine ⟨P, rfl, ?_, ?_, ?_⟩
    · have hlast : Fin.last (d + 1) = Fin.succ (Fin.last d) := rfl
      rw [hlast]
      exact hP'last
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; simp [P]
        · intro _
          change Matrix.rank (H - P' j') = j'.val + 1
          have hle : Matrix.rank (H - P' j') ≤ j'.val + 1 := by
            have hsplit : H - P' j' = (H - H') + (H' - P' j') := by abel
            have hd' := hP'dist 0 j' (Fin.zero_le j')
            rw [hP'0] at hd'
            calc Matrix.rank (H - P' j')
                = Matrix.rank ((H - H') + (H' - P' j')) := by rw [hsplit]
              _ ≤ Matrix.rank (H - H') + Matrix.rank (H' - P' j') := rank_add_le _ _
              _ = 1 + j'.val := by rw [hHH', hd']; simp
              _ = j'.val + 1 := by omega
          have hge : j'.val + 1 ≤ Matrix.rank (H - P' j') := by
            have hsplit : H - J = (H - P' j') + (P' j' - J) := by abel
            have hd' := hP'dist j' (Fin.last d) (Fin.le_last j')
            rw [hP'last] at hd'
            have h1 : d + 1 ≤ Matrix.rank (H - P' j') + Matrix.rank (P' j' - J) := by
              rw [← hd, hsplit]
              exact rank_add_le _ _
            rw [hd'] at h1
            have hjlt : j'.val ≤ d := Nat.lt_succ_iff.mp j'.isLt
            dsimp [Fin.last] at h1
            omega
          omega
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact absurd hij (not_le.mpr (Fin.succ_pos i'))
        · intro hij
          have hij' : i' ≤ j' := Fin.succ_le_succ_iff.mp hij
          change Matrix.rank (P' i' - P' j') = (j'.val + 1) - (i'.val + 1)
          rw [hP'dist i' j' hij']
          omega
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [P]
      · have hdef' := hP'def i'
        dsimp only at hdef' hdefJ hdefA
        have hPsucc : P i'.succ = P' i' := rfl
        constructor
        · change Matrix.rank (fun i z => Sum.elim (P' i' i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank (P' i') =
            Matrix.rank (fun i z => Sum.elim (H i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank H - (i'.val + 1)
          rw [hdef'.1, hdefJ]
          omega
        · change Matrix.rank (fun i z => Sum.elim (P' i' i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank J =
            Matrix.rank (fun i z => Sum.elim (H i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank J - (i'.val + 1)
          rw [hdef'.2, hdefA]
          omega

end PEqualNP.Outside.L_lib_1010_aux

open PEqualNP.Outside.L_lib_1010_aux

theorem PEqualNP.Outside.L_lib_1010 :
    (∀ (K : Type) [Field K] (q r : ℕ) (H J : Matrix (Fin q) (Fin r) K),
  let size := fun (A : Matrix (Fin q) (Fin r) K) =>
    Matrix.rank (fun i z => Sum.elim (A i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K)
  let d := Matrix.rank (H-J)
  ∃ P : Fin (d+1) → Matrix (Fin q) (Fin r) K,
    P 0 = H ∧ P (Fin.last d) = J ∧
    (∀ i j : Fin (d+1), i ≤ j → Matrix.rank (P i-P j) = j.val-i.val) ∧
    ∀ i : Fin (d+1),
      size (P i) - Matrix.rank (P i) = size H - Matrix.rank H - i.val ∧
      size (P i) - Matrix.rank J = size H - Matrix.rank J - i.val) := by
  intro K _ q r H J
  exact path_exists_aux (Matrix.rank (H - J)) H J rfl
