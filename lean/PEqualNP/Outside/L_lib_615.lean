import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_615_aux

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma z2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

lemma z2_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_neg_eq (a : ZMod 2) : -a = a := by
  rcases z2_zero_or_one a with rfl | rfl <;> rfl

lemma z2_units_zsmul (u : ℤˣ) (a : ZMod 2) : (u : ℤ) • a = a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.val_neg, Units.val_one, neg_one_zsmul]
    exact z2_neg_eq a

lemma one_add_one_K (K : Type) [Field K] [CharP K 2] : (1 : K) + 1 = 0 := by
  have h2 : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
  simpa [Nat.cast_ofNat, one_add_one_eq_two] using h2

def z2ToK (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K where
  toFun := fun z => if z = 0 then 0 else 1
  map_one' := by simp
  map_mul' := fun a b => by
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases z2_zero_or_one a with rfl | rfl <;> rcases z2_zero_or_one b with rfl | rfl <;>
      simp [h10]
  map_zero' := by simp
  map_add' := fun a b => by
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases z2_zero_or_one a with rfl | rfl <;> rcases z2_zero_or_one b with rfl | rfl <;>
      simp [h10, h11, one_add_one_K K]

lemma natCast_eq_z2ToK (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    (n : K) = z2ToK K (n : ZMod 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, map_add, map_one, ih]

lemma toMatrix'_mulVec_eq {w : ℕ} (f : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))
    (x : Fin w → ZMod 2) : (LinearMap.toMatrix' f).mulVec x = f x := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma toMatrix'_mulVecLin_eq {w : ℕ} (M : Matrix (Fin w) (Fin w) (ZMod 2)) :
    LinearMap.toMatrix' M.mulVecLin = M := by
  exact LinearMap.toMatrix'_toLin' M

lemma det_z2 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod 2)) :
    M.det = ∑ σ : Equiv.Perm ι, ∏ i : ι, M (σ i) i := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact z2_units_zsmul (Equiv.Perm.sign σ) _

lemma det_z2_col {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod 2)) :
    M.det = ∑ σ : Equiv.Perm ι, ∏ i : ι, M i (σ i) := by
  rw [← Matrix.det_transpose, det_z2]
  rfl

lemma det_perm_matrix_z2 {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : Equiv.Perm ι) :
    (Matrix.of fun i j : ι => if j = φ i then (1 : ZMod 2) else 0).det = 1 := by
  rw [det_z2_col]
  have hterm : ∀ σ : Equiv.Perm ι,
      (∏ i : ι, (if σ i = φ i then (1 : ZMod 2) else 0)) = if σ = φ then 1 else 0 := by
    intro σ
    by_cases h : σ = φ
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      have hne : ∃ i : ι, σ i ≠ φ i := by
        by_contra hall
        apply h
        ext i
        by_contra hi
        exact hall ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hne
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp [hterm]

lemma card_mulVec_eq_det {w : ℕ} (M : Matrix (Fin w) (Fin w) (ZMod 2)) (c : Fin w → ZMod 2) :
    (((Finset.univ : Finset (Fin w → ZMod 2)).filter (fun x => M.mulVec x = c)).card : ZMod 2) =
      M.det := by
  by_cases hdet : M.det = 0
  · rw [hdet]
    let S := (Finset.univ : Finset (Fin w → ZMod 2)).filter (fun x => M.mulVec x = c)
    change (S.card : ZMod 2) = 0
    have hnotinj : ¬ Function.Injective M.mulVec := by
      intro hinj
      have hbij : Function.Bijective M.mulVec := Finite.injective_iff_bijective.mp hinj
      let e : (Fin w → ZMod 2) ≃ₗ[ZMod 2] (Fin w → ZMod 2) :=
        LinearEquiv.ofBijective M.mulVecLin hbij
      let N : Matrix (Fin w) (Fin w) (ZMod 2) := LinearMap.toMatrix' (e.symm : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))
      have hmul : N * M = 1 := by
        have hcomp : (e.symm : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)).comp M.mulVecLin =
            LinearMap.id := by
          apply LinearMap.ext
          intro x
          exact e.symm_apply_apply x
        have h1 := congrArg LinearMap.toMatrix' hcomp
        rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, toMatrix'_mulVecLin_eq] at h1
        exact h1
      have hdm : N.det * M.det = 1 := by
        rw [← Matrix.det_mul, hmul, Matrix.det_one]
      rw [hdet, mul_zero] at hdm
      exact zero_ne_one hdm
    have hker : ∃ v0 : Fin w → ZMod 2, v0 ≠ 0 ∧ M.mulVec v0 = 0 := by
      have hex : ∃ a b : Fin w → ZMod 2, M.mulVec a = M.mulVec b ∧ a ≠ b := by
        by_contra hall
        apply hnotinj
        intro a b hab
        by_contra hne
        exact hall ⟨a, b, hab, hne⟩
      obtain ⟨a, b, hab, hne⟩ := hex
      refine ⟨a + b, ?_, ?_⟩
      · intro h0
        apply hne
        ext i
        have hi := congrFun h0 i
        simp only [Pi.add_apply, Pi.zero_apply] at hi
        have ha := z2_add_self (b i)
        calc
          a i = a i + (b i + b i) := by rw [ha, add_zero]
          _ = (a i + b i) + b i := by rw [add_assoc]
          _ = b i := by rw [hi, zero_add]
      · rw [Matrix.mulVec_add, hab]
        ext i
        exact z2_add_self _
    obtain ⟨v0, hv0ne, hv0mul⟩ := hker
    have hex_i : ∃ i0 : Fin w, v0 i0 = 1 := by
      by_contra hall
      apply hv0ne
      ext i
      have hne1 : v0 i ≠ 1 := fun h => hall ⟨i, h⟩
      rcases z2_zero_or_one (v0 i) with hv0 | hv1
      · exact hv0
      · exact False.elim (hne1 hv1)
    obtain ⟨i0, hi0⟩ := hex_i
    let S0 := S.filter (fun x => x i0 = 0)
    let S1 := S.filter (fun x => x i0 = 1)
    have hunion : S = S0 ∪ S1 := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, S0, S1]
      constructor
      · intro hx
        rcases z2_zero_or_one (x i0) with hxi | hxi
        · exact Or.inl ⟨hx, hxi⟩
        · exact Or.inr ⟨hx, hxi⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro x hx0 hx1
      have h0 : x i0 = 0 := (Finset.mem_filter.mp hx0).2
      have h1 : x i0 = 1 := (Finset.mem_filter.mp hx1).2
      rw [h0] at h1
      exact zero_ne_one h1
    have hcard_eq : S0.card = S1.card := by
      refine Finset.card_bij (fun x _ => x + v0) ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxS, hxi⟩
        have hxm : M.mulVec x = c := (Finset.mem_filter.mp hxS).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [Matrix.mulVec_add, hxm, hv0mul, add_zero]
        · simp [Pi.add_apply, hxi, hi0]
      · intro x1 _ x2 _ heq
        ext i
        have hi := congrFun heq i
        simp only [Pi.add_apply] at hi
        have hv := z2_add_self (v0 i)
        calc
          x1 i = (x1 i + v0 i) + v0 i := by rw [add_assoc, hv, add_zero]
          _ = (x2 i + v0 i) + v0 i := by rw [hi]
          _ = x2 i := by rw [add_assoc, hv, add_zero]
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyS, hyi⟩
        have hym : M.mulVec y = c := (Finset.mem_filter.mp hyS).2
        refine ⟨y + v0, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [Matrix.mulVec_add, hym, hv0mul, add_zero]
          · simp [Pi.add_apply, hyi, hi0, z2_add_self]
        · ext i
          simp only [Pi.add_apply]
          rw [add_assoc, z2_add_self, add_zero]
    rw [hunion, Finset.card_union_of_disjoint hdisj, hcard_eq]
    push_cast
    exact z2_add_self _
  · have hdet1 : M.det = 1 := z2_eq_one_of_ne_zero hdet
    rw [hdet1]
    have hunit : IsUnit M.det := by rw [hdet1]; exact isUnit_one
    have hsing :
        (Finset.univ : Finset (Fin w → ZMod 2)).filter (fun x => M.mulVec x = c) =
          {M⁻¹.mulVec c} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hx
        rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
      · rintro rfl
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    rw [hsing, Finset.card_singleton]
    simp

lemma fixed_eq_det {K : Type} [Field K] [CharP K 2] {w : ℕ}
    (p r : ((Fin w → ZMod 2) ≃ₗ[ZMod 2] (Fin w → ZMod 2)) × (Fin w → ZMod 2)) :
    (((Finset.univ : Finset (Fin w → ZMod 2)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card : K) =
      z2ToK K (1 + LinearMap.toMatrix' (r.1 : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)) *
        LinearMap.toMatrix' (p.1 : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))).det := by
  let M : Matrix (Fin w) (Fin w) (ZMod 2) :=
    1 + LinearMap.toMatrix' (r.1 : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)) *
      LinearMap.toMatrix' (p.1 : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))
  let c : Fin w → ZMod 2 := r.1 p.2 + r.2
  have hfilter :
      (Finset.univ : Finset (Fin w → ZMod 2)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x) =
        (Finset.univ : Finset (Fin w → ZMod 2)).filter (fun x => M.mulVec x = c) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hmul : M.mulVec x = x + r.1 (p.1 x) := by
      dsimp only [M]
      rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        toMatrix'_mulVec_eq, toMatrix'_mulVec_eq]
      rfl
    rw [hmul, map_add]
    dsimp only [c]
    constructor
    · intro h
      ext i
      have hi := congrFun h i
      simp only [Pi.add_apply] at hi ⊢
      have hx1 := z2_add_self (r.1 (p.1 x) i)
      have hx2 := z2_add_self (x i)
      calc
        x i + r.1 (p.1 x) i
            = (r.1 (p.1 x) i + r.1 p.2 i + r.2 i) + r.1 (p.1 x) i := by rw [← hi]
        _ = (r.1 (p.1 x) i + r.1 (p.1 x) i) + (r.1 p.2 i + r.2 i) := by ring
        _ = r.1 p.2 i + r.2 i := by rw [hx1, zero_add]
    · intro h
      ext i
      have hi := congrFun h i
      simp only [Pi.add_apply] at hi ⊢
      have hx1 := z2_add_self (r.1 (p.1 x) i)
      calc
        r.1 (p.1 x) i + r.1 p.2 i + r.2 i
            = r.1 (p.1 x) i + (r.1 p.2 i + r.2 i) := by rw [add_assoc]
        _ = r.1 (p.1 x) i + (x i + r.1 (p.1 x) i) := by rw [← hi]
        _ = x i + (r.1 (p.1 x) i + r.1 (p.1 x) i) := by ring
        _ = x i := by rw [hx1, add_zero]
  rw [hfilter, natCast_eq_z2ToK K, card_mulVec_eq_det]

def minor {w : ℕ} (A : Matrix (Fin w) (Fin w) (ZMod 2))
    (S T : Finset (Fin w)) : ZMod 2 :=
  if h : S.card = T.card then
    (A.submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin h.symm)).det
  else 0

lemma minor_empty {w : ℕ} (A : Matrix (Fin w) (Fin w) (ZMod 2)) :
    minor A ∅ ∅ = 1 := by
  simp [minor]

lemma minor_univ {w : ℕ} (A : Matrix (Fin w) (Fin w) (ZMod 2)) :
    minor A Finset.univ Finset.univ = A.det := by
  simp only [minor, ↓reduceDIte]
  let eUniv : { x : Fin w // x ∈ (Finset.univ : Finset (Fin w)) } ≃ Fin w :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  let e : Fin (Finset.univ : Finset (Fin w)).card ≃ Fin w :=
    (Finset.univ.orderIsoOfFin rfl).toEquiv.trans eUniv
  have hsub : A.submatrix (Finset.univ.orderEmbOfFin rfl) (Finset.univ.orderEmbOfFin rfl) =
      A.submatrix e e := by
    ext i j
    rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

lemma minor_self_eq_submatrix {w : ℕ} (A : Matrix (Fin w) (Fin w) (ZMod 2)) (S : Finset (Fin w)) :
    minor A S S = (A.submatrix (Subtype.val : { i // i ∈ S } → Fin w) Subtype.val).det := by
  simp only [minor, ↓reduceDIte]
  let e : Fin S.card ≃ { i // i ∈ S } := (S.orderIsoOfFin rfl).toEquiv
  have hsub : A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl) =
      (A.submatrix (Subtype.val : { i // i ∈ S } → Fin w) Subtype.val).submatrix e e := by
    ext i j
    rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

lemma det_one_add_z2 {w : ℕ} (A : Matrix (Fin w) (Fin w) (ZMod 2)) :
    (1 + A).det = ∑ S : Finset (Fin w), minor A S S := by
  rw [det_z2_col]
  have hexpand : ∀ σ : Equiv.Perm (Fin w),
      (∏ i : Fin w, (1 + A) i (σ i)) =
        ∑ S : Finset (Fin w),
          (∏ i ∈ S, A i (σ i)) * (∏ i ∈ Sᶜ, (if i = σ i then (1 : ZMod 2) else 0)) := by
    intro σ
    have hprod : (∏ i : Fin w, (1 + A) i (σ i)) =
        ∏ i : Fin w, (A i (σ i) + (if i = σ i then (1 : ZMod 2) else 0)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [Matrix.add_apply, Matrix.one_apply, add_comm]
    rw [hprod, Fintype.prod_add]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [minor_self_eq_submatrix, det_z2_col]
  let goodPerms : Finset (Equiv.Perm (Fin w)) :=
    Finset.univ.filter (fun σ => ∀ i ∈ Sᶜ, i = σ i)
  have hfilt :
      ∑ σ : Equiv.Perm (Fin w),
          (∏ i ∈ S, A i (σ i)) * (∏ i ∈ Sᶜ, if i = σ i then (1 : ZMod 2) else 0) =
        ∑ σ ∈ goodPerms, ∏ i ∈ S, A i (σ i) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : Equiv.Perm (Fin w) => ∀ i ∈ Sᶜ, i = σ i)]
    have h1 :
        ∑ σ ∈ goodPerms,
            (∏ i ∈ S, A i (σ i)) * (∏ i ∈ Sᶜ, if i = σ i then (1 : ZMod 2) else 0) =
          ∑ σ ∈ goodPerms, ∏ i ∈ S, A i (σ i) := by
      refine Finset.sum_congr rfl fun σ hσ => ?_
      have hfix : ∀ i ∈ Sᶜ, i = σ i := (Finset.mem_filter.mp hσ).2
      have hp1 : (∏ i ∈ Sᶜ, if i = σ i then (1 : ZMod 2) else 0) = 1 :=
        Finset.prod_eq_one fun i hi => by
          rw [← hfix i hi]
          simp
      rw [hp1, mul_one]
    have h2 :
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin w) => ¬ ∀ i ∈ Sᶜ, i = σ i),
            (∏ i ∈ S, A i (σ i)) * (∏ i ∈ Sᶜ, if i = σ i then (1 : ZMod 2) else 0) = 0 := by
      refine Finset.sum_eq_zero fun σ hσ => ?_
      have hnot : ¬ ∀ i ∈ Sᶜ, i = σ i := (Finset.mem_filter.mp hσ).2
      have hex : ∃ i ∈ Sᶜ, i ≠ σ i := by
        by_contra hall
        apply hnot
        intro i hi
        by_contra hne
        exact hall ⟨i, hi, hne⟩
      obtain ⟨i, hi, hne⟩ := hex
      have hp0 : (∏ j ∈ Sᶜ, if j = σ j then (1 : ZMod 2) else 0) = 0 :=
        Finset.prod_eq_zero hi (by simp [hne])
      rw [hp0, mul_zero]
    rw [h1, h2, add_zero]
  rw [hfilt]
  symm
  refine Finset.sum_bij (fun (τ : Equiv.Perm { i // i ∈ S }) _ => Equiv.Perm.ofSubtype τ) ?_ ?_ ?_ ?_
  · intro τ _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩
    have hnot : i ∉ S := Finset.mem_compl.mp hi
    exact (Equiv.Perm.ofSubtype_apply_of_not_mem τ hnot).symm
  · intro τ1 _ τ2 _ heq
    apply Equiv.ext
    rintro ⟨i, hi⟩
    have h := Equiv.congr_fun heq i
    simp only [Equiv.Perm.ofSubtype_apply_of_mem _ hi] at h
    exact Subtype.ext h
  · intro σ hσ
    have hfix : ∀ i ∈ Sᶜ, i = σ i := (Finset.mem_filter.mp hσ).2
    have hmem : ∀ i : Fin w, σ i ∈ S ↔ i ∈ S := by
      intro i
      constructor
      · intro hsi
        by_contra hi
        have h1 := hfix i (Finset.mem_compl.mpr hi)
        rw [← h1] at hsi
        exact hi hsi
      · intro hi
        by_contra hsi
        have h1 := hfix (σ i) (Finset.mem_compl.mpr hsi)
        have h2 : i = σ i := σ.injective h1
        rw [← h2] at hsi
        exact hsi hi
    let τ : Equiv.Perm { i // i ∈ S } := Equiv.Perm.subtypePerm σ hmem
    refine ⟨τ, Finset.mem_univ _, ?_⟩
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ S
    · simp [τ, Equiv.Perm.ofSubtype_apply_of_mem _ hi]
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hi]
      exact hfix i (Finset.mem_compl.mpr hi)
  · intro τ _
    rw [← Finset.prod_attach S]
    refine Finset.prod_bij (fun x _ => x) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => h) (fun x _ => ⟨x, Finset.mem_attach _ _, rfl⟩) ?_
    intro x _
    simp [Matrix.submatrix_apply, Equiv.Perm.ofSubtype_apply_of_mem _ x.2]

lemma minor_mul {w : ℕ} (R P : Matrix (Fin w) (Fin w) (ZMod 2))
    (S U : Finset (Fin w)) :
    minor (R * P) S U = ∑ T : Finset (Fin w), minor R S T * minor P T U := by
  by_cases hSU : S.card = U.card
  · have hLHS0 : minor (R * P) S U =
        ((R * P).submatrix (S.orderEmbOfFin rfl) (U.orderEmbOfFin hSU.symm)).det := by
      simp only [minor, hSU, ↓reduceDIte]
    rw [hLHS0]
    let k := S.card
    let eS := S.orderEmbOfFin rfl
    let eU := U.orderEmbOfFin hSU.symm
    have hLHS :
        ((R * P).submatrix eS eU).det =
          ∑ f : Fin k → Fin w,
            (∏ a : Fin k, R (eS a) (f a)) * (P.submatrix f eU).det := by
      rw [det_z2_col]
      simp only [Matrix.submatrix_apply]
      have hstep1 :
          ∑ σ : Equiv.Perm (Fin k), ∏ a : Fin k, (R * P) (eS a) (eU (σ a)) =
            ∑ σ : Equiv.Perm (Fin k), ∑ f : Fin k → Fin w,
              ∏ a : Fin k, (R (eS a) (f a) * P (f a) (eU (σ a))) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [Matrix.mul_apply]
        exact Fintype.prod_sum fun a j => R (eS a) j * P j (eU (σ a))
      rw [hstep1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [det_z2_col, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.prod_mul_distrib]
      rfl
    rw [hLHS]
    let injF := (Finset.univ : Finset (Fin k → Fin w)).filter Function.Injective
    have hdrop :
        ∑ f : Fin k → Fin w, (∏ a : Fin k, R (eS a) (f a)) * (P.submatrix f eU).det =
          ∑ f ∈ injF, (∏ a : Fin k, R (eS a) (f a)) * (P.submatrix f eU).det := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Function.Injective]
      have h0 :
          ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin w => ¬ Function.Injective f),
              (∏ a : Fin k, R (eS a) (f a)) * (P.submatrix f eU).det = 0 := by
        refine Finset.sum_eq_zero fun f hf => ?_
        have hnot : ¬ Function.Injective f := (Finset.mem_filter.mp hf).2
        have hex : ∃ a b : Fin k, a ≠ b ∧ f a = f b := by
          by_contra hall
          apply hnot
          intro a b hab
          by_contra hne
          exact hall ⟨a, b, hne, hab⟩
        obtain ⟨a, b, hne, hab⟩ := hex
        have hdet0 : (P.submatrix f eU).det = 0 := by
          apply Matrix.det_zero_of_row_eq hne
          ext c
          simp [Matrix.submatrix_apply, hab]
        rw [hdet0, mul_zero]
      rw [h0, add_zero]
    rw [hdrop]
    have hRHS_filt :
        ∑ T : Finset (Fin w), minor R S T * minor P T U =
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin w) => T.card = k),
            if h : T.card = k then (R.submatrix eS (T.orderEmbOfFin h)).det *
              (P.submatrix (T.orderEmbOfFin h) eU).det else 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun T : Finset (Fin w) => T.card = k)]
      have h1 :
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin w) => T.card = k), minor R S T * minor P T U =
            ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin w) => T.card = k),
              if h : T.card = k then (R.submatrix eS (T.orderEmbOfFin h)).det *
                (P.submatrix (T.orderEmbOfFin h) eU).det else 0 := by
        refine Finset.sum_congr rfl fun T hT => ?_
        have hTk : T.card = k := (Finset.mem_filter.mp hT).2
        have hST : S.card = T.card := hTk.symm
        have hTU : T.card = U.card := hTk.trans hSU
        have hm1 : minor R S T = (R.submatrix eS (T.orderEmbOfFin hTk)).det := by
          simp only [minor, hST, ↓reduceDIte, eS]
        have hm2 : minor P T U = (P.submatrix (T.orderEmbOfFin hTk) eU).det := by
          have hm2' : minor P T U = (P.submatrix (T.orderEmbOfFin rfl) (U.orderEmbOfFin hTU.symm)).det := by
            simp only [minor, hTU, ↓reduceDIte]
          rw [hm2']
          let iso : Fin T.card ≃ Fin k := (Fin.castOrderIso hTk).toEquiv
          have hmat : P.submatrix (T.orderEmbOfFin hTk) eU =
              (P.submatrix (T.orderEmbOfFin rfl) (U.orderEmbOfFin hTU.symm)).submatrix iso.symm iso.symm := by
            ext a b
            simp only [Matrix.submatrix_apply, iso, eU]
            rfl
          rw [hmat, Matrix.det_submatrix_equiv_self]
        rw [hm1, hm2]
        simp only [hTk, ↓reduceDIte]
      have h2 :
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin w) => ¬ T.card = k), minor R S T * minor P T U = 0 := by
        refine Finset.sum_eq_zero fun T hT => ?_
        have hne : T.card ≠ k := (Finset.mem_filter.mp hT).2
        have hne' : ¬ S.card = T.card := fun h => hne h.symm
        simp [minor, hne']
      rw [h1, h2, add_zero]
    rw [hRHS_filt]
    have hmaps : ∀ f ∈ injF, (Finset.univ.image f) ∈ Finset.univ.filter (fun T : Finset (Fin w) => T.card = k) := by
      intro f hf
      have hinj : Function.Injective f := (Finset.mem_filter.mp hf).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTk : T.card = k := (Finset.mem_filter.mp hT).2
    simp only [hTk, ↓reduceDIte]
    rw [det_z2_col, Finset.sum_mul]
    symm
    let eT := T.orderEmbOfFin hTk
    refine Finset.sum_bij (fun (τ : Equiv.Perm (Fin k)) _ => fun a => eT (τ a)) ?_ ?_ ?_ ?_
    · intro τ _
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, eT.injective.comp τ.injective⟩, ?_⟩
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩
        exact Finset.orderEmbOfFin_mem T hTk (τ a)
      · intro hx
        let iso := T.orderIsoOfFin hTk
        refine ⟨τ.symm (iso.symm ⟨x, hx⟩), ?_⟩
        simp only [Equiv.apply_symm_apply]
        have := iso.apply_symm_apply ⟨x, hx⟩
        exact congrArg Subtype.val this
    · intro τ1 _ τ2 _ heq
      apply Equiv.ext
      intro a
      exact eT.injective (congrFun heq a)
    · intro f hf
      rcases Finset.mem_filter.mp hf with ⟨hfinj, himg⟩
      have hinj : Function.Injective f := (Finset.mem_filter.mp hfinj).2
      let iso := T.orderIsoOfFin hTk
      have hfmem : ∀ a : Fin k, f a ∈ T := by
        intro a
        rw [← himg]
        exact Finset.mem_image_of_mem f (Finset.mem_univ a)
      let gfun : Fin k → Fin k := fun a => iso.symm ⟨f a, hfmem a⟩
      have hginj : Function.Injective gfun := by
        intro a b hab
        have h1 := congrArg (fun x => (iso x).val) hab
        simp only [gfun, OrderIso.apply_symm_apply] at h1
        exact hinj h1
      let τ : Equiv.Perm (Fin k) := Equiv.ofBijective gfun (Finite.injective_iff_bijective.mp hginj)
      refine ⟨τ, Finset.mem_univ _, ?_⟩
      funext a
      change (iso (iso.symm ⟨f a, hfmem a⟩)).val = f a
      simp
    · intro τ _
      congr 1
      have hsub : P.submatrix (fun a => eT (τ a)) eU = (P.submatrix eT eU).submatrix τ id := rfl
      rw [hsub, Matrix.det_permute]
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hsign | hsign
      · simp only [hsign, Units.val_one, Int.cast_one, one_mul]; rfl
      · simp only [hsign, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul, z2_neg_eq]; rfl
  · simp only [minor, hSU, ↓reduceDIte]
    symm
    refine Finset.sum_eq_zero fun T _ => ?_
    by_cases hST : S.card = T.card
    · have hTU : ¬ T.card = U.card := fun h => hSU (hST.trans h)
      simp [hTU]
    · simp [hST]

def extMat (K : Type) [Field K] [CharP K 2] {w : ℕ} (A : Matrix (Fin w) (Fin w) (ZMod 2)) :
    Matrix (Finset (Fin w)) (Finset (Fin w)) K :=
  Matrix.of fun S T => z2ToK K (minor A S T)

lemma extMat_mul (K : Type) [Field K] [CharP K 2] {w : ℕ}
    (R P : Matrix (Fin w) (Fin w) (ZMod 2)) :
    extMat K (R * P) = extMat K R * extMat K P := by
  ext S U
  simp only [extMat, Matrix.of_apply, Matrix.mul_apply, minor_mul, map_sum, map_mul]

lemma extMat_one (K : Type) [Field K] [CharP K 2] {w : ℕ} :
    extMat K (1 : Matrix (Fin w) (Fin w) (ZMod 2)) = 1 := by
  ext S T
  simp only [extMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hST : S = T
  · subst hST
    have hm : minor (1 : Matrix (Fin w) (Fin w) (ZMod 2)) S S = 1 := by
      rw [minor_self_eq_submatrix]
      have h1 : (1 : Matrix (Fin w) (Fin w) (ZMod 2)).submatrix
          (Subtype.val : { i // i ∈ S } → Fin w) (Subtype.val : { i // i ∈ S } → Fin w) = 1 := by
        ext ⟨i, hi⟩ ⟨j, hj⟩
        simp [Matrix.one_apply]
      rw [h1, Matrix.det_one]
    simp [hm]
  · simp only [hST, ↓reduceIte]
    have hm : minor (1 : Matrix (Fin w) (Fin w) (ZMod 2)) S T = 0 := by
      dsimp only [minor]
      split_ifs with hcard
      · have hex : ∃ x ∈ S, x ∉ T := by
          by_contra hall
          have hsub : S ⊆ T := by
            intro x hx
            by_contra hxT
            exact hall ⟨x, hx, hxT⟩
          exact hST (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
        obtain ⟨x, hxS, hxT⟩ := hex
        let iso := S.orderIsoOfFin rfl
        let a : Fin S.card := iso.symm ⟨x, hxS⟩
        apply Matrix.det_eq_zero_of_row_eq_zero a
        intro b
        simp only [Matrix.submatrix_apply, Matrix.one_apply]
        have ha : S.orderEmbOfFin rfl a = x := by
          have := iso.apply_symm_apply ⟨x, hxS⟩
          exact congrArg Subtype.val this
        have hb : T.orderEmbOfFin hcard.symm b ∈ T := Finset.orderEmbOfFin_mem T hcard.symm b
        have hne : S.orderEmbOfFin rfl a ≠ T.orderEmbOfFin hcard.symm b := by
          rw [ha]
          intro heq
          exact hxT (heq ▸ hb)
        simp [hne]
      · rfl
    simp [hm]

def transvMat {w : ℕ} (i j : Fin w) : Matrix (Fin w) (Fin w) (ZMod 2) :=
  Matrix.of fun r c => (if r = c then 1 else 0) + (if r = i ∧ c = j then 1 else 0)

lemma transvMat_mul_self {w : ℕ} {i j : Fin w} (hij : i ≠ j) :
    transvMat i j * transvMat i j = 1 := by
  ext r c
  simp only [Matrix.mul_apply, transvMat, Matrix.of_apply, Matrix.one_apply]
  have hexp : ∀ k : Fin w,
      ((if r = k then (1 : ZMod 2) else 0) + (if r = i ∧ k = j then 1 else 0)) *
      ((if k = c then 1 else 0) + (if k = i ∧ c = j then 1 else 0)) =
        (if r = k ∧ k = c then 1 else 0) +
        (if k = j ∧ r = i ∧ c = j then 1 else 0) +
        (if k = i ∧ r = i ∧ c = j then 1 else 0) := by
    intro k
    by_cases hrk : r = k <;> by_cases hkc : k = c <;>
      by_cases hri : r = i <;> by_cases hkj : k = j <;>
      by_cases hki : k = i <;> by_cases hcj : c = j <;>
      simp_all
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ k : Fin w, (if r = k ∧ k = c then (1 : ZMod 2) else 0) = if r = c then 1 else 0 := by
    by_cases hrc : r = c
    · subst hrc
      have hsame : ∀ k : Fin w, (if r = k ∧ k = r then (1 : ZMod 2) else 0) = if r = k then 1 else 0 := by
        intro k
        by_cases hrk : r = k
        · subst hrk; simp
        · simp [hrk]
      simp [hsame]
    · simp only [hrc, ↓reduceIte]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs with h
      · exact False.elim (hrc (h.1.trans h.2))
      · rfl
  have h2 : ∑ k : Fin w, (if k = j ∧ r = i ∧ c = j then (1 : ZMod 2) else 0) =
      if r = i ∧ c = j then 1 else 0 := by
    by_cases h : r = i ∧ c = j
    · simp [h]
    · simp [h]
  have h3 : ∑ k : Fin w, (if k = i ∧ r = i ∧ c = j then (1 : ZMod 2) else 0) =
      if r = i ∧ c = j then 1 else 0 := by
    by_cases h : r = i ∧ c = j
    · simp [h]
    · simp [h]
  rw [h1, h2, h3, add_assoc, z2_add_self, add_zero]

lemma transvMat_det {w : ℕ} {i j : Fin w} (hij : i ≠ j) :
    (transvMat i j).det = 1 := by
  have h := congrArg Matrix.det (transvMat_mul_self hij)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have hne : (transvMat i j).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  exact z2_eq_one_of_ne_zero hne

lemma minor_transvMat {w : ℕ} {i j : Fin w} (hij : i ≠ j) (S T : Finset (Fin w)) :
    minor (transvMat i j) S T =
      (if S = T then 1 else 0) + (if i ∈ S ∧ j ∉ S ∧ T = insert j (S.erase i) then 1 else 0) := by
  by_cases hST : S = T
  · subst hST
    have hnot : ¬ (i ∈ S ∧ j ∉ S ∧ S = insert j (S.erase i)) := by
      rintro ⟨_, hj, heq⟩
      have : j ∈ S := by rw [heq]; exact Finset.mem_insert_self _ _
      exact hj this
    simp only [↓reduceIte, hnot, add_zero]
    rw [minor_self_eq_submatrix]
    by_cases hboth : i ∈ S ∧ j ∈ S
    · let a : { x // x ∈ S } := ⟨i, hboth.1⟩
      let b : { x // x ∈ S } := ⟨j, hboth.2⟩
      have hab : a ≠ b := fun h => hij (congrArg Subtype.val h)
      let e : { x // x ∈ S } ≃ Fin S.card := (S.orderIsoOfFin rfl).symm.toEquiv
      have hsub : (transvMat i j).submatrix (Subtype.val : { x // x ∈ S } → Fin w) Subtype.val =
          (transvMat (e a) (e b)).submatrix e e := by
        ext x y
        simp only [Matrix.submatrix_apply, transvMat, Matrix.of_apply]
        have hx : x.1 = i ↔ e x = e a := by
          constructor
          · intro h; congr 1; exact Subtype.ext h
          · intro h; exact congrArg Subtype.val (e.injective h)
        have hy : y.1 = j ↔ e y = e b := by
          constructor
          · intro h; congr 1; exact Subtype.ext h
          · intro h; exact congrArg Subtype.val (e.injective h)
        have hxy : x.1 = y.1 ↔ e x = e y := by
          constructor
          · intro h; congr 1; exact Subtype.ext h
          · intro h; exact congrArg Subtype.val (e.injective h)
        simp [hx, hy, hxy]
      rw [hsub, Matrix.det_submatrix_equiv_self]
      exact transvMat_det (fun h => hab (e.injective h))
    · have h1 : (transvMat i j).submatrix (Subtype.val : { x // x ∈ S } → Fin w)
          (Subtype.val : { x // x ∈ S } → Fin w) = 1 := by
        ext ⟨x, hx⟩ ⟨y, hy⟩
        simp only [Matrix.submatrix_apply, transvMat, Matrix.of_apply, Matrix.one_apply]
        have hnot2 : ¬ (x = i ∧ y = j) := by
          rintro ⟨rfl, rfl⟩
          exact hboth ⟨hx, hy⟩
        simp [hnot2]
      rw [h1, Matrix.det_one]
  · simp only [hST, ↓reduceIte, zero_add]
    by_cases hmove : i ∈ S ∧ j ∉ S ∧ T = insert j (S.erase i)
    · simp only [eq_true hmove, ↓reduceIte]
      rcases hmove with ⟨hiS, hjS, hTeq⟩
      have hcard : S.card = T.card := by
        rw [hTeq, Finset.card_insert_of_notMem (by simp [hjS]), Finset.card_erase_of_mem hiS]
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
        omega
      have hmin : minor (transvMat i j) S T =
          ((transvMat i j).submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin hcard.symm)).det := by
        simp only [minor, hcard, ↓reduceDIte]
      rw [hmin]
      let isoS := S.orderIsoOfFin rfl
      let isoT := T.orderIsoOfFin hcard.symm
      have hiT : i ∉ T := by
        rw [hTeq]
        simp [hij]
      have hjT : j ∈ T := by
        rw [hTeq]
        exact Finset.mem_insert_self _ _
      let mapVal : Fin w → Fin w := fun r => if r = i then j else r
      have hmap_mem : ∀ x ∈ S, mapVal x ∈ T := by
        intro x hx
        rw [hTeq]
        by_cases hxi : x = i
        · simp [mapVal, hxi]
        · simp only [mapVal, hxi, ↓reduceIte]
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hx⟩)
      let φfun : Fin S.card → Fin S.card := fun a => isoT.symm ⟨mapVal (S.orderEmbOfFin rfl a), hmap_mem _ (Finset.orderEmbOfFin_mem S rfl a)⟩
      have hφinj : Function.Injective φfun := by
        intro a b hab
        have h1 := congrArg (fun x => (isoT x).val) hab
        simp only [φfun, OrderIso.apply_symm_apply] at h1
        have haS := Finset.orderEmbOfFin_mem S rfl a
        have hbS := Finset.orderEmbOfFin_mem S rfl b
        dsimp only [mapVal] at h1
        split_ifs at h1 with hai hbi hbi
        · exact (S.orderEmbOfFin rfl).injective (hai.trans hbi.symm)
        · exact False.elim (hjS (h1 ▸ hbS))
        · exact False.elim (hjS (h1.symm ▸ haS))
        · exact (S.orderEmbOfFin rfl).injective h1
      let φ : Equiv.Perm (Fin S.card) := Equiv.ofBijective φfun (Finite.injective_iff_bijective.mp hφinj)
      have hmat : (transvMat i j).submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin hcard.symm) =
          Matrix.of fun a b => if b = φ a then (1 : ZMod 2) else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, transvMat, Matrix.of_apply]
        have haS := Finset.orderEmbOfFin_mem S rfl a
        have hbT := Finset.orderEmbOfFin_mem T hcard.symm b
        have hφval : T.orderEmbOfFin hcard.symm (φ a) = mapVal (S.orderEmbOfFin rfl a) := by
          change (isoT (isoT.symm ⟨mapVal (S.orderEmbOfFin rfl a), _⟩)).val = _
          simp
        have hbiff : b = φ a ↔ T.orderEmbOfFin hcard.symm b = mapVal (S.orderEmbOfFin rfl a) := by
          constructor
          · rintro rfl; exact hφval
          · intro h; exact (T.orderEmbOfFin hcard.symm).injective (h.trans hφval.symm)
        by_cases hai : S.orderEmbOfFin rfl a = i
        · have hne1 : i ≠ T.orderEmbOfFin hcard.symm b := fun heq => hiT (heq ▸ hbT)
          simp [hai, hne1, hbiff, mapVal]
        · have hiff2 : S.orderEmbOfFin rfl a = T.orderEmbOfFin hcard.symm b ↔ b = φ a := by
            rw [hbiff]
            dsimp only [mapVal]
            simp only [hai, ↓reduceIte, eq_comm]
          simp [hai, hiff2]
      rw [hmat]
      exact det_perm_matrix_z2 φ
    · simp only [hmove, ↓reduceIte]
      dsimp only [minor]
      split_ifs with hcard
      · by_cases hsub : S.erase i ⊆ T
        · have hiS : i ∈ S := by
            by_contra hiS
            have hSe : S.erase i = S := Finset.erase_eq_of_notMem hiS
            rw [hSe] at hsub
            exact hST (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
          have hiT : i ∉ T := by
            intro hiT
            have hSTsub : S ⊆ T := by
              intro x hx
              by_cases hxi : x = i
              · exact hxi ▸ hiT
              · exact hsub (Finset.mem_erase.mpr ⟨hxi, hx⟩)
            exact hST (Finset.eq_of_subset_of_card_le hSTsub (le_of_eq hcard.symm))
          by_cases hjT : j ∈ T
          · have hjS : j ∈ S := by
              by_contra hjS
              have hins : insert j (S.erase i) ⊆ T := Finset.insert_subset hjT hsub
              have hcard_ins : (insert j (S.erase i)).card = S.card := by
                rw [Finset.card_insert_of_notMem (by simp [hjS]), Finset.card_erase_of_mem hiS]
                have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
                omega
              have hTeq : T = insert j (S.erase i) :=
                (Finset.eq_of_subset_of_card_le hins (by omega)).symm
              exact hmove ⟨hiS, hjS, hTeq⟩
            have hjSe : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjS⟩
            have hex : ∃ x ∈ T, x ∉ S.erase i := by
              by_contra hall
              have hTsub : T ⊆ S.erase i := by
                intro x hx
                by_contra hxnot
                exact hall ⟨x, hx, hxnot⟩
              have hle : T.card ≤ (S.erase i).card := Finset.card_le_card hTsub
              have hlt : (S.erase i).card < S.card := Finset.card_erase_lt_of_mem hiS
              omega
            obtain ⟨x, hxT, hxnot⟩ := hex
            have hxi : x ≠ i := fun h => hiT (h ▸ hxT)
            have hxj : x ≠ j := fun h => hxnot (h ▸ hjSe)
            let isoT := T.orderIsoOfFin hcard.symm
            let b : Fin S.card := isoT.symm ⟨x, hxT⟩
            apply Matrix.det_eq_zero_of_column_eq_zero b
            intro a
            simp only [Matrix.submatrix_apply, transvMat, Matrix.of_apply]
            have hb : T.orderEmbOfFin hcard.symm b = x :=
              congrArg Subtype.val (isoT.apply_symm_apply ⟨x, hxT⟩)
            have haS := Finset.orderEmbOfFin_mem S rfl a
            have hne : S.orderEmbOfFin rfl a ≠ x := by
              intro heq
              by_cases hai : S.orderEmbOfFin rfl a = i
              · exact hxi (heq.symm.trans hai)
              · exact hxnot (heq ▸ Finset.mem_erase.mpr ⟨hai, haS⟩)
            rw [hb]
            simp [hne, hxj]
          · let isoS := S.orderIsoOfFin rfl
            let a : Fin S.card := isoS.symm ⟨i, hiS⟩
            apply Matrix.det_eq_zero_of_row_eq_zero a
            intro b
            simp only [Matrix.submatrix_apply, transvMat, Matrix.of_apply]
            have ha : S.orderEmbOfFin rfl a = i :=
              congrArg Subtype.val (isoS.apply_symm_apply ⟨i, hiS⟩)
            have hbT := Finset.orderEmbOfFin_mem T hcard.symm b
            have hne1 : i ≠ T.orderEmbOfFin hcard.symm b := fun h => hiT (h ▸ hbT)
            have hne2 : T.orderEmbOfFin hcard.symm b ≠ j := fun h => hjT (h ▸ hbT)
            rw [ha]
            simp [hne1, hne2]
        · rw [Finset.not_subset] at hsub
          obtain ⟨x, hxSe, hxT⟩ := hsub
          rcases Finset.mem_erase.mp hxSe with ⟨hxi, hxS⟩
          let isoS := S.orderIsoOfFin rfl
          let a : Fin S.card := isoS.symm ⟨x, hxS⟩
          apply Matrix.det_eq_zero_of_row_eq_zero a
          intro b
          simp only [Matrix.submatrix_apply, transvMat, Matrix.of_apply]
          have ha : S.orderEmbOfFin rfl a = x :=
            congrArg Subtype.val (isoS.apply_symm_apply ⟨x, hxS⟩)
          have hbT := Finset.orderEmbOfFin_mem T hcard.symm b
          have hne : x ≠ T.orderEmbOfFin hcard.symm b := fun h => hxT (h ▸ hbT)
          rw [ha]
          simp [hne, hxi]
      · rfl

def permMat {w : ℕ} (σ : Equiv.Perm (Fin w)) : Matrix (Fin w) (Fin w) (ZMod 2) :=
  Matrix.of fun r c => if r = σ c then 1 else 0

lemma permMat_det {w : ℕ} (σ : Equiv.Perm (Fin w)) : (permMat σ).det = 1 := by
  have h : permMat σ = Matrix.of fun r c => if c = σ.symm r then (1 : ZMod 2) else 0 := by
    ext r c
    simp only [permMat, Matrix.of_apply]
    have hiff : r = σ c ↔ c = σ.symm r := by
      constructor
      · intro h; simp [h]
      · intro h; simp [h]
    simp [hiff]
  rw [h]
  exact det_perm_matrix_z2 σ.symm

lemma minor_permMat {w : ℕ} (σ : Equiv.Perm (Fin w)) (S T : Finset (Fin w)) :
    minor (permMat σ) S T = if S = T.image σ then 1 else 0 := by
  by_cases hST : S = T.image σ
  · simp only [eq_true hST, ↓reduceIte]
    have hcard : S.card = T.card := by
      rw [hST, Finset.card_image_of_injective T σ.injective]
    have hmin : minor (permMat σ) S T =
        ((permMat σ).submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin hcard.symm)).det := by
      simp only [minor, hcard, ↓reduceDIte]
    rw [hmin]
    let isoS := S.orderIsoOfFin rfl
    let isoT := T.orderIsoOfFin hcard.symm
    have hmem : ∀ a : Fin S.card, σ.symm (S.orderEmbOfFin rfl a) ∈ T := by
      intro a
      have ha : S.orderEmbOfFin rfl a ∈ T.image σ := hST ▸ Finset.orderEmbOfFin_mem S rfl a
      rcases Finset.mem_image.mp ha with ⟨t, ht, heq⟩
      simpa [← heq] using ht
    let φfun : Fin S.card → Fin S.card := fun a => isoT.symm ⟨σ.symm (S.orderEmbOfFin rfl a), hmem a⟩
    have hφinj : Function.Injective φfun := by
      intro a b hab
      have h1 := congrArg (fun x => (isoT x).val) hab
      simp only [φfun, OrderIso.apply_symm_apply] at h1
      exact (S.orderEmbOfFin rfl).injective (σ.symm.injective h1)
    let φ : Equiv.Perm (Fin S.card) := Equiv.ofBijective φfun (Finite.injective_iff_bijective.mp hφinj)
    have hmat : (permMat σ).submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin hcard.symm) =
        Matrix.of fun a b => if b = φ a then (1 : ZMod 2) else 0 := by
      ext a b
      simp only [Matrix.submatrix_apply, permMat, Matrix.of_apply]
      have hφval : T.orderEmbOfFin hcard.symm (φ a) = σ.symm (S.orderEmbOfFin rfl a) := by
        change (isoT (isoT.symm ⟨σ.symm (S.orderEmbOfFin rfl a), _⟩)).val = _
        simp
      have hiff : S.orderEmbOfFin rfl a = σ (T.orderEmbOfFin hcard.symm b) ↔ b = φ a := by
        constructor
        · intro h
          apply (T.orderEmbOfFin hcard.symm).injective
          rw [hφval, h, Equiv.symm_apply_apply]
        · rintro rfl
          rw [hφval, Equiv.apply_symm_apply]
      simp [hiff]
    rw [hmat]
    exact det_perm_matrix_z2 φ
  · simp only [hST, ↓reduceIte]
    dsimp only [minor]
    split_ifs with hcard
    · have hex : ∃ x ∈ S, x ∉ T.image σ := by
        by_contra hall
        have hsub : S ⊆ T.image σ := by
          intro x hx
          by_contra hxnot
          exact hall ⟨x, hx, hxnot⟩
        have hcard_img : (T.image σ).card = S.card := by
          rw [Finset.card_image_of_injective T σ.injective, hcard]
        exact hST (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_img))
      obtain ⟨x, hxS, hxnot⟩ := hex
      let isoS := S.orderIsoOfFin rfl
      let a : Fin S.card := isoS.symm ⟨x, hxS⟩
      apply Matrix.det_eq_zero_of_row_eq_zero a
      intro b
      simp only [Matrix.submatrix_apply, permMat, Matrix.of_apply]
      have ha : S.orderEmbOfFin rfl a = x :=
        congrArg Subtype.val (isoS.apply_symm_apply ⟨x, hxS⟩)
      have hbT := Finset.orderEmbOfFin_mem T hcard.symm b
      have hne : x ≠ σ (T.orderEmbOfFin hcard.symm b) := by
        intro heq
        exact hxnot (heq ▸ Finset.mem_image_of_mem σ hbT)
      rw [ha]
      simp [hne]
    · rfl

abbrev GLw (w : ℕ) := { M : Matrix (Fin w) (Fin w) (ZMod 2) // M.det = 1 }

def glOne (w : ℕ) : GLw w := ⟨1, Matrix.det_one⟩

def glMul {w : ℕ} (g h : GLw w) : GLw w :=
  ⟨g.1 * h.1, by rw [Matrix.det_mul, g.2, h.2, mul_one]⟩

noncomputable def glInv {w : ℕ} (g : GLw w) : GLw w :=
  ⟨g.1⁻¹, by
    have hu : IsUnit g.1.det := by rw [g.2]; exact isUnit_one
    have h := congrArg Matrix.det (Matrix.mul_nonsing_inv g.1 hu)
    rw [Matrix.det_mul, g.2, one_mul, Matrix.det_one] at h
    exact h⟩

lemma glMul_inv_left {w : ℕ} (g : GLw w) : glMul (glInv g) g = glOne w := by
  apply Subtype.ext
  have hu : IsUnit g.1.det := by rw [g.2]; exact isUnit_one
  exact Matrix.nonsing_inv_mul g.1 hu

lemma glMul_inv_right {w : ℕ} (g : GLw w) : glMul g (glInv g) = glOne w := by
  apply Subtype.ext
  have hu : IsUnit g.1.det := by rw [g.2]; exact isUnit_one
  exact Matrix.mul_nonsing_inv g.1 hu

lemma glMul_assoc {w : ℕ} (a b c : GLw w) : glMul (glMul a b) c = glMul a (glMul b c) := by
  apply Subtype.ext
  exact Matrix.mul_assoc a.1 b.1 c.1

lemma glMul_one_left {w : ℕ} (a : GLw w) : glMul (glOne w) a = a := by
  apply Subtype.ext
  exact Matrix.one_mul a.1

def evalExt (K : Type) [Field K] [CharP K 2] {w : ℕ} (c : GLw w → K) :
    Matrix (Finset (Fin w)) (Finset (Fin w)) K :=
  ∑ g : GLw w, c g • extMat K g.1

def deltaGL (K : Type) [Field K] [CharP K 2] {w : ℕ} (g0 : GLw w) : GLw w → K :=
  fun g => if g = g0 then 1 else 0

lemma evalExt_delta (K : Type) [Field K] [CharP K 2] {w : ℕ} (g0 : GLw w) :
    evalExt K (deltaGL K g0) = extMat K g0.1 := by
  simp [evalExt, deltaGL]

lemma evalExt_add (K : Type) [Field K] [CharP K 2] {w : ℕ} (c1 c2 : GLw w → K) :
    evalExt K (c1 + c2) = evalExt K c1 + evalExt K c2 := by
  simp [evalExt, Pi.add_apply, add_smul, Finset.sum_add_distrib]

noncomputable def convGL (K : Type) [Field K] [CharP K 2] {w : ℕ} (c1 c2 : GLw w → K) : GLw w → K :=
  fun h => ∑ g : GLw w, c1 g * c2 (glMul (glInv g) h)

lemma evalExt_conv (K : Type) [Field K] [CharP K 2] {w : ℕ} (c1 c2 : GLw w → K) :
    evalExt K (convGL K c1 c2) = evalExt K c1 * evalExt K c2 := by
  simp only [evalExt, convGL]
  have h1 :
      ∑ h : GLw w, (∑ g : GLw w, c1 g * c2 (glMul (glInv g) h)) • extMat K h.1 =
        ∑ g : GLw w, ∑ h : GLw w, (c1 g * c2 (glMul (glInv g) h)) • extMat K h.1 := by
    trans ∑ h : GLw w, ∑ g : GLw w, (c1 g * c2 (glMul (glInv g) h)) • extMat K h.1
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_smul]
    · exact Finset.sum_comm
  rw [h1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun h _ => glMul (glInv g) h) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro h1 _ h2 _ heq
    have h := congrArg (glMul g) heq
    rwa [← glMul_assoc, glMul_inv_right, glMul_one_left,
      ← glMul_assoc, glMul_inv_right, glMul_one_left] at h
  · intro k _
    refine ⟨glMul g k, Finset.mem_univ _, ?_⟩
    rw [← glMul_assoc, glMul_inv_left, glMul_one_left]
  · intro h _
    have hgh : glMul g (glMul (glInv g) h) = h := by
      rw [← glMul_assoc, glMul_inv_right, glMul_one_left]
    have hmat : extMat K h.1 = extMat K g.1 * extMat K (glMul (glInv g) h).1 := by
      rw [← extMat_mul]
      congr 1
      exact congrArg Subtype.val hgh.symm
    rw [hmat, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma exists_proj_pair (K : Type) [Field K] [CharP K 2] {w : ℕ} {i j : Fin w} (hij : i ≠ j) :
    ∃ c : GLw w → K, ∀ S U : Finset (Fin w),
      evalExt K c S U = if S = U ∧ i ∈ S ∧ j ∉ S then 1 else 0 := by
  let Eij : GLw w := ⟨transvMat i j, transvMat_det hij⟩
  let Eji : GLw w := ⟨transvMat j i, transvMat_det hij.symm⟩
  let dij : GLw w → K := deltaGL K Eij + deltaGL K (glOne w)
  let dji : GLw w → K := deltaGL K Eji + deltaGL K (glOne w)
  have hdij : ∀ S T : Finset (Fin w),
      evalExt K dij S T = if i ∈ S ∧ j ∉ S ∧ T = insert j (S.erase i) then 1 else 0 := by
    intro S T
    rw [evalExt_add, evalExt_delta, evalExt_delta]
    change extMat K (transvMat i j) S T + extMat K (1 : Matrix (Fin w) (Fin w) (ZMod 2)) S T = _
    rw [extMat_one]
    simp only [extMat, Matrix.of_apply, Matrix.one_apply, minor_transvMat hij, map_add]
    by_cases hST : S = T
    · subst hST
      have hnot : ¬ (i ∈ S ∧ j ∉ S ∧ S = insert j (S.erase i)) := by
        rintro ⟨_, hj, heq⟩
        have : j ∈ S := by rw [heq]; exact Finset.mem_insert_self _ _
        exact hj this
      simp [hnot, one_add_one_K K]
    · simp only [hST, ↓reduceIte, map_zero, zero_add, add_zero]
      split_ifs <;> simp
  have hdji : ∀ T U : Finset (Fin w),
      evalExt K dji T U = if j ∈ T ∧ i ∉ T ∧ U = insert i (T.erase j) then 1 else 0 := by
    intro T U
    rw [evalExt_add, evalExt_delta, evalExt_delta]
    change extMat K (transvMat j i) T U + extMat K (1 : Matrix (Fin w) (Fin w) (ZMod 2)) T U = _
    rw [extMat_one]
    simp only [extMat, Matrix.of_apply, Matrix.one_apply, minor_transvMat hij.symm, map_add]
    by_cases hTU : T = U
    · subst hTU
      have hnot : ¬ (j ∈ T ∧ i ∉ T ∧ T = insert i (T.erase j)) := by
        rintro ⟨_, hi, heq⟩
        have : i ∈ T := by rw [heq]; exact Finset.mem_insert_self _ _
        exact hi this
      simp [hnot, one_add_one_K K]
    · simp only [hTU, ↓reduceIte, map_zero, zero_add, add_zero]
      split_ifs <;> simp
  refine ⟨convGL K dij dji, fun S U => ?_⟩
  rw [evalExt_conv, Matrix.mul_apply]
  simp_rw [hdij, hdji]
  by_cases hcond : i ∈ S ∧ j ∉ S
  · let T0 : Finset (Fin w) := insert j (S.erase i)
    have hT0j : j ∈ T0 := Finset.mem_insert_self _ _
    have hT0i : i ∉ T0 := by simp [T0, hij]
    have hT0back : insert i (T0.erase j) = S := by
      have her : T0.erase j = S.erase i := by
        dsimp only [T0]
        rw [Finset.erase_insert (by simp [hcond.2])]
      rw [her, Finset.insert_erase hcond.1]
    have hterm : ∀ T : Finset (Fin w),
        (if i ∈ S ∧ j ∉ S ∧ T = T0 then (1 : K) else 0) *
        (if j ∈ T ∧ i ∉ T ∧ U = insert i (T.erase j) then 1 else 0) =
          if T = T0 then (if S = U then 1 else 0) else 0 := by
      intro T
      by_cases hTT0 : T = T0
      · subst hTT0
        simp [hcond, hT0j, hT0i, hT0back, eq_comm]
      · simp [hTT0]
    rw [Finset.sum_congr rfl fun T _ => hterm T]
    simp [hcond]
  · have hzero : ∀ T : Finset (Fin w),
        (if i ∈ S ∧ j ∉ S ∧ T = insert j (S.erase i) then (1 : K) else 0) *
        (if j ∈ T ∧ i ∉ T ∧ U = insert i (T.erase j) then 1 else 0) = 0 := by
      intro T
      have hnot : ¬ (i ∈ S ∧ j ∉ S ∧ T = insert j (S.erase i)) := fun h => hcond ⟨h.1, h.2.1⟩
      simp [hnot]
    have hnot2 : ¬ (S = U ∧ i ∈ S ∧ j ∉ S) := fun h => hcond h.2
    rw [Finset.sum_congr rfl fun T _ => hzero T]
    simp [hnot2]

lemma exists_isolator (K : Type) [Field K] [CharP K 2] {w : ℕ}
    (S0 T0 : Finset (Fin w)) (h1 : 1 ≤ S0.card) (h2 : S0.card < w) (hcard : T0.card = S0.card) :
    ∃ c : GLw w → K, ∀ S T : Finset (Fin w),
      evalExt K c S T = if S = S0 ∧ T = T0 then 1 else 0 := by
  have hS0_ne : S0.Nonempty := Finset.card_pos.mp (by omega)
  have hS0c_ne : S0ᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hcard_c : S0ᶜ.card = 0 := by rw [hemp]; rfl
    rw [Finset.card_compl, Fintype.card_fin] at hcard_c
    omega
  let pairs : Finset (Fin w × Fin w) := S0 ×ˢ S0ᶜ
  have hpairs_ne : pairs.Nonempty := Finset.Nonempty.product hS0_ne hS0c_ne
  have hchoose : ∀ p : Fin w × Fin w, p ∈ pairs →
      ∃ c : GLw w → K, ∀ S U : Finset (Fin w),
        evalExt K c S U = if S = U ∧ p.1 ∈ S ∧ p.2 ∉ S then 1 else 0 := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hne : p.1 ≠ p.2 := fun h => (Finset.mem_compl.mp hp2) (h ▸ hp1)
    exact exists_proj_pair K hne
  have hprod : ∀ Q : Finset (Fin w × Fin w), Q ⊆ pairs → Q.Nonempty →
      ∃ c : GLw w → K, ∀ S U : Finset (Fin w),
        evalExt K c S U = if S = U ∧ ∀ p ∈ Q, p.1 ∈ S ∧ p.2 ∉ S then 1 else 0 := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      intro _ hne
      exact False.elim (Finset.not_nonempty_empty hne)
    | @insert q Q' hq ih =>
      intro hsub _
      have hqmem : q ∈ pairs := hsub (Finset.mem_insert_self q Q')
      obtain ⟨cq, hcq⟩ := hchoose q hqmem
      by_cases hQ' : Q'.Nonempty
      · have hsub' : Q' ⊆ pairs := fun x hx => hsub (Finset.mem_insert_of_mem hx)
        obtain ⟨cQ', hcQ'⟩ := ih hsub' hQ'
        refine ⟨convGL K cq cQ', fun S U => ?_⟩
        rw [evalExt_conv, Matrix.mul_apply]
        simp_rw [hcq, hcQ']
        by_cases hSU : S = U
        · subst hSU
          have hterm : ∀ T : Finset (Fin w),
              (if S = T ∧ q.1 ∈ S ∧ q.2 ∉ S then (1 : K) else 0) *
              (if T = S ∧ ∀ p ∈ Q', p.1 ∈ T ∧ p.2 ∉ T then 1 else 0) =
                if T = S then (if (q.1 ∈ S ∧ q.2 ∉ S) ∧ ∀ p ∈ Q', p.1 ∈ S ∧ p.2 ∉ S then 1 else 0) else 0 := by
            intro T
            by_cases hTS : T = S
            · subst hTS
              by_cases h1 : q.1 ∈ T ∧ q.2 ∉ T <;> simp [h1]
            · have hST : S ≠ T := Ne.symm hTS
              simp [hTS, hST]
          rw [Finset.sum_congr rfl fun T _ => hterm T]
          simp
        · have hzero : ∀ T : Finset (Fin w),
              (if S = T ∧ q.1 ∈ S ∧ q.2 ∉ S then (1 : K) else 0) *
              (if T = U ∧ ∀ p ∈ Q', p.1 ∈ T ∧ p.2 ∉ T then 1 else 0) = 0 := by
            intro T
            by_cases hST : S = T
            · subst hST
              simp [hSU]
            · simp [hST]
          rw [Finset.sum_congr rfl fun T _ => hzero T]
          simp [hSU]
      · rw [Finset.not_nonempty_iff_eq_empty] at hQ'
        subst hQ'
        refine ⟨cq, fun S U => ?_⟩
        simpa using hcq S U
  obtain ⟨cP, hcP⟩ := hprod pairs (Finset.Subset.refl _) hpairs_ne
  have hS0_iff : ∀ S : Finset (Fin w),
      (∀ p ∈ pairs, p.1 ∈ S ∧ p.2 ∉ S) ↔ S = S0 := by
    intro S
    constructor
    · intro hall
      obtain ⟨i0, hi0⟩ := hS0_ne
      obtain ⟨j0, hj0⟩ := hS0c_ne
      ext x
      constructor
      · intro hxS
        by_contra hxS0
        have hmem : (i0, x) ∈ pairs := Finset.mem_product.mpr ⟨hi0, Finset.mem_compl.mpr hxS0⟩
        exact (hall (i0, x) hmem).2 hxS
      · intro hxS0
        have hmem : (x, j0) ∈ pairs := Finset.mem_product.mpr ⟨hxS0, hj0⟩
        exact (hall (x, j0) hmem).1
    · rintro rfl p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      exact ⟨hp1, Finset.mem_compl.mp hp2⟩
  have hcP' : ∀ S U : Finset (Fin w),
      evalExt K cP S U = if S = U ∧ S = S0 then 1 else 0 := by
    intro S U
    simp only [hcP, hS0_iff]
  have hcard_in : Fintype.card { x : Fin w // x ∈ T0 } = Fintype.card { x : Fin w // x ∈ S0 } := by
    simp [Fintype.card_coe, hcard]
  have hcard_out : Fintype.card { x : Fin w // x ∉ T0 } = Fintype.card { x : Fin w // x ∉ S0 } := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard_in]
  let e1 : { x : Fin w // x ∈ T0 } ≃ { x : Fin w // x ∈ S0 } := Fintype.equivOfCardEq hcard_in
  let e2 : { x : Fin w // x ∉ T0 } ≃ { x : Fin w // x ∉ S0 } := Fintype.equivOfCardEq hcard_out
  let σ : Equiv.Perm (Fin w) :=
    (Equiv.sumCompl (· ∈ T0)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ S0)))
  have hσ_img : T0.image σ = S0 := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hxT, rfl⟩
      simp [σ, Equiv.sumCompl_symm_apply_of_pos hxT]
    · intro hyS
      refine ⟨(e1.symm ⟨y, hyS⟩).1, (e1.symm ⟨y, hyS⟩).2, ?_⟩
      simp [σ, Equiv.sumCompl_symm_apply_of_pos (e1.symm ⟨y, hyS⟩).2]
  let gσ : GLw w := ⟨permMat σ, permMat_det σ⟩
  refine ⟨convGL K cP (deltaGL K gσ), fun S T => ?_⟩
  rw [evalExt_conv, Matrix.mul_apply, evalExt_delta]
  have hterm : ∀ U : Finset (Fin w),
      evalExt K cP S U * extMat K gσ.1 U T =
        if U = S0 then (if S = S0 ∧ T = T0 then 1 else 0) else 0 := by
    intro U
    rw [hcP']
    simp only [extMat, gσ, Matrix.of_apply, minor_permMat]
    by_cases hUS0 : U = S0
    · subst U
      have hiff : S0 = T.image σ ↔ T = T0 := by
        constructor
        · intro h
          have himg : T.image σ = T0.image σ := h.symm.trans hσ_img.symm
          ext x
          have hx := Finset.ext_iff.mp himg (σ x)
          simpa [Finset.mem_image] using hx
        · rintro rfl
          exact hσ_img.symm
      simp only [hiff]
      by_cases hSS0 : S = S0 <;> by_cases hTT0 : T = T0 <;> simp [hSS0, hTT0]
    · by_cases hSS0 : S = S0
      · subst S
        have hSU : ¬ S0 = U := Ne.symm hUS0
        simp [hUS0, hSU]
      · simp [hUS0, hSS0]
  simp [hterm]

noncomputable def linOfGL {w : ℕ} (g : GLw w) : (Fin w → ZMod 2) ≃ₗ[ZMod 2] (Fin w → ZMod 2) :=
  LinearEquiv.ofLinearMap g.1.mulVecLin (glInv g).1.mulVecLin
    (by
      apply LinearMap.ext
      intro x
      change g.1.mulVec ((glInv g).1.mulVec x) = x
      rw [Matrix.mulVec_mulVec]
      have h := congrArg Subtype.val (glMul_inv_right g)
      change g.1 * (glInv g).1 = 1 at h
      rw [h, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      change (glInv g).1.mulVec (g.1.mulVec x) = x
      rw [Matrix.mulVec_mulVec]
      have h := congrArg Subtype.val (glMul_inv_left g)
      change (glInv g).1 * g.1 = 1 at h
      rw [h, Matrix.one_mulVec])

lemma toMatrix'_linOfGL {w : ℕ} (g : GLw w) :
    LinearMap.toMatrix' (linOfGL g : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)) = g.1 := by
  exact toMatrix'_mulVecLin_eq g.1

def idxSet (w : ℕ) : Finset (Finset (Fin w) × Finset (Fin w)) :=
  Finset.univ.filter (fun p => 1 ≤ p.1.card ∧ p.1.card < w ∧ p.2.card = p.1.card)

lemma card_idxSet (b : ℕ) :
    (idxSet (b + 1)).card = Nat.choose (2 * (b + 1)) (b + 1) - 2 := by
  let w := b + 1
  have hmaps : ∀ p ∈ idxSet w, p.1.card ∈ Finset.Ico 1 w := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨h1, h2, _⟩
    exact Finset.mem_Ico.mpr ⟨h1, h2⟩
  have hfib : (idxSet w).card = ∑ k ∈ Finset.Ico 1 w, Nat.choose w k * Nat.choose w k := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Finset.mem_Ico.mp hk with ⟨hk1, hkw⟩
    have heq : (idxSet w).filter (fun p => p.1.card = k) =
        (Finset.univ : Finset (Fin w)).powersetCard k ×ˢ
          (Finset.univ : Finset (Fin w)).powersetCard k := by
      ext ⟨S, T⟩
      simp only [idxSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_powersetCard, Finset.subset_univ]
      constructor
      · rintro ⟨⟨_, _, hTS⟩, hSk⟩
        exact ⟨hSk, hTS.trans hSk⟩
      · rintro ⟨hSk, hTk⟩
        exact ⟨⟨hSk.symm ▸ hk1, hSk.symm ▸ hkw, hTk.trans hSk.symm⟩, hSk⟩
    rw [heq, Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hvand : ∑ k ∈ Finset.range (w + 1), Nat.choose w k * Nat.choose w k =
      Nat.choose (2 * w) w := by
    have h2w : 2 * w = w + w := two_mul w
    rw [h2w, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose w i * Nat.choose w j)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkle : k ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.choose_symm hkle]
  have hsplit : ∑ k ∈ Finset.range (w + 1), Nat.choose w k * Nat.choose w k =
      2 + ∑ k ∈ Finset.Ico 1 w, Nat.choose w k * Nat.choose w k := by
    rw [Finset.sum_range_succ]
    have hrange : Finset.range w = insert 0 (Finset.Ico 1 w) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hrange, Finset.sum_insert (by simp)]
    simp only [Nat.choose_zero_right, Nat.choose_self, mul_one]
    omega
  dsimp only [w] at hfib hvand hsplit
  rw [hfib]
  omega

lemma det_one_add_eq_idxSet (K : Type) [Field K] [CharP K 2] {b : ℕ}
    (R P : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hR : R.det = 1) (hP : P.det = 1) :
    z2ToK K (1 + R * P).det =
      ∑ α ∈ idxSet (b + 1), extMat K R α.1 α.2 * extMat K P α.2 α.1 := by
  let w := b + 1
  rw [det_one_add_z2, map_sum]
  have hexp : ∑ S : Finset (Fin w), z2ToK K (minor (R * P) S S) =
      ∑ S : Finset (Fin w), ∑ T : Finset (Fin w), extMat K R S T * extMat K P T S := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minor_mul, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [extMat, map_mul]
  rw [hexp]
  have hne : (∅ : Finset (Fin w)) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    simp [w] at hc
  have hsplit :
      ∑ S : Finset (Fin w), ∑ T : Finset (Fin w), extMat K R S T * extMat K P T S =
        (∑ T : Finset (Fin w), extMat K R ∅ T * extMat K P T ∅) +
        (∑ T : Finset (Fin w), extMat K R Finset.univ T * extMat K P T Finset.univ) +
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin w) => 1 ≤ S.card ∧ S.card < w),
          ∑ T : Finset (Fin w), extMat K R S T * extMat K P T S := by
    let mid : Finset (Finset (Fin w)) :=
      Finset.univ.filter (fun S : Finset (Fin w) => 1 ≤ S.card ∧ S.card < w)
    have huniv : (Finset.univ : Finset (Finset (Fin w))) =
        insert ∅ (insert Finset.univ mid) := by
      ext S
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff, mid]
      by_cases h0 : S = ∅
      · exact Or.inl h0
      · by_cases hu : S = Finset.univ
        · exact Or.inr (Or.inl hu)
        · right; right
          have hpos : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr (fun hc => h0 (Finset.card_eq_zero.mp hc))
          have hle : S.card ≤ w := by simpa using Finset.card_le_univ S
          have hlt : S.card < w := by
            by_contra hge
            have heq : S.card = (Finset.univ : Finset (Fin w)).card := by
              simp only [Finset.card_univ, Fintype.card_fin]
              omega
            exact hu (Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (le_of_eq heq.symm))
          exact ⟨hpos, hlt⟩
    have hnot1 : (∅ : Finset (Fin w)) ∉ insert Finset.univ mid := by
      simp [hne, mid]
    have hnot2 : (Finset.univ : Finset (Fin w)) ∉ mid := by
      simp [mid, w]
    trans ∑ S ∈ insert ∅ (insert Finset.univ mid),
        ∑ T : Finset (Fin w), extMat K R S T * extMat K P T S
    · exact Finset.sum_congr huniv fun _ _ => rfl
    · rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, add_assoc]
  rw [hsplit]
  have hterm0 : ∑ T : Finset (Fin w), extMat K R ∅ T * extMat K P T ∅ = 1 := by
    have h0 : ∀ T : Finset (Fin w), extMat K R ∅ T * extMat K P T ∅ = if T = ∅ then 1 else 0 := by
      intro T
      by_cases hT : T = ∅
      · subst hT
        simp [extMat, minor_empty]
      · have hc : ¬ (∅ : Finset (Fin w)).card = T.card := by
          simp only [Finset.card_empty]
          intro h
          exact hT (Finset.card_eq_zero.mp h.symm)
        simp only [extMat, Matrix.of_apply, minor, eq_false hc, ↓reduceDIte, map_zero, zero_mul,
          eq_false hT, ↓reduceIte]
    simp [h0]
  have htermU : ∑ T : Finset (Fin w), extMat K R Finset.univ T * extMat K P T Finset.univ = 1 := by
    have hU : ∀ T : Finset (Fin w),
        extMat K R Finset.univ T * extMat K P T Finset.univ = if T = Finset.univ then 1 else 0 := by
      intro T
      by_cases hT : T = Finset.univ
      · subst hT
        simp [extMat, minor_univ, hR, hP]
      · have hc : ¬ (Finset.univ : Finset (Fin w)).card = T.card := by
          intro h
          exact hT (Finset.eq_of_subset_of_card_le (Finset.subset_univ T) (le_of_eq h))
        simp only [extMat, Matrix.of_apply, minor, eq_false hc, ↓reduceDIte, map_zero, zero_mul,
          eq_false hT, ↓reduceIte]
    simp [hU]
  rw [hterm0, htermU, one_add_one_K K, zero_add]
  have hpair :
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin w) => 1 ≤ S.card ∧ S.card < w),
        ∑ T : Finset (Fin w), extMat K R S T * extMat K P T S =
      ∑ α ∈ idxSet w, extMat K R α.1 α.2 * extMat K P α.2 α.1 := by
    rw [← Finset.sum_product']
    have hsub : idxSet w ⊆
        Finset.univ.filter (fun S : Finset (Fin w) => 1 ≤ S.card ∧ S.card < w) ×ˢ Finset.univ := by
      intro ⟨S, T⟩ hST
      rcases (Finset.mem_filter.mp hST).2 with ⟨h1, h2, _⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ S, h1, h2⟩, Finset.mem_univ T⟩
    symm
    refine Finset.sum_subset hsub ?_
    intro ⟨S, T⟩ hmem hnot
    rcases Finset.mem_product.mp hmem with ⟨hS, _⟩
    rcases (Finset.mem_filter.mp hS).2 with ⟨h1, h2⟩
    have hne_card : ¬ S.card = T.card := by
      intro heq
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ (S, T), h1, h2, heq.symm⟩)
    simp [extMat, minor, hne_card]
  exact hpair

theorem main : (∀ (K : Type) [Field K] [CharP K 2] (b d : ℕ),
  let w := b + 1
  let V := Fin w → ZMod 2
  let P := (V ≃ₗ[ZMod 2] V) × V
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset V).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    Nat.choose (2 * w) w - 2 ≤ d) := by
  intro K _ _ b d w V P fixed
  rw [← card_idxSet b]
  constructor
  · rintro ⟨A, B, hAB⟩
    have hchoose : ∀ α : { α // α ∈ idxSet w }, ∃ c : GLw w → K,
        ∀ S T : Finset (Fin w), evalExt K c S T = if S = α.1.1 ∧ T = α.1.2 then 1 else 0 := by
      intro ⟨⟨S0, T0⟩, hα⟩
      rcases (Finset.mem_filter.mp hα).2 with ⟨h1, h2, h3⟩
      exact exists_isolator K S0 T0 h1 h2 h3
    choose coeff hcoeff using hchoose
    have hswap_mem : ∀ α : { α // α ∈ idxSet w }, (α.1.2, α.1.1) ∈ idxSet w := by
      intro ⟨⟨S0, T0⟩, hα⟩
      rcases (Finset.mem_filter.mp hα).2 with ⟨h1, h2, h3⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3.symm ▸ h1, h3.symm ▸ h2, h3.symm⟩
    let pt : GLw w → P := fun g => (linOfGL g, 0)
    let U : Matrix { α // α ∈ idxSet w } (Fin d) K :=
      Matrix.of fun α l => ∑ g : GLw w, coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * A (pt g) l
    let W : Matrix (Fin d) { α // α ∈ idxSet w } K :=
      Matrix.of fun l β => ∑ h : GLw w, coeff β h * B (pt h) l
    have hUW : U * W = 1 := by
      ext α β
      simp only [Matrix.mul_apply, U, W, Matrix.of_apply, Matrix.one_apply]
      have h1 :
          ∑ l : Fin d,
              (∑ g : GLw w, coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * A (pt g) l) *
              (∑ h : GLw w, coeff β h * B (pt h) l) =
            ∑ g : GLw w, ∑ h : GLw w,
              coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * coeff β h *
                (∑ l : Fin d, A (pt g) l * B (pt h) l) := by
        trans ∑ l : Fin d, ∑ g : GLw w, ∑ h : GLw w,
            coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * coeff β h * (A (pt g) l * B (pt h) l)
        · refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [← Finset.mul_sum]
      rw [h1]
      have hfix : ∀ g h : GLw w,
          (∑ l : Fin d, A (pt g) l * B (pt h) l) =
            ∑ γ ∈ idxSet w, extMat K h.1 γ.1 γ.2 * extMat K g.1 γ.2 γ.1 := by
        intro g h
        rw [← hAB (pt g) (pt h), fixed_eq_det]
        simp only [pt, toMatrix'_linOfGL]
        exact det_one_add_eq_idxSet K h.1 g.1 h.2 g.2
      simp_rw [hfix]
      have h2 :
          ∑ g : GLw w, ∑ h : GLw w,
              coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * coeff β h *
                (∑ γ ∈ idxSet w, extMat K h.1 γ.1 γ.2 * extMat K g.1 γ.2 γ.1) =
            ∑ γ ∈ idxSet w,
              (evalExt K (coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩) γ.2 γ.1) *
              (evalExt K (coeff β) γ.1 γ.2) := by
        trans ∑ g : GLw w, ∑ h : GLw w, ∑ γ ∈ idxSet w,
            (coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * extMat K g.1 γ.2 γ.1) *
            (coeff β h * extMat K h.1 γ.1 γ.2)
        · refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun γ _ => ?_
          ring
        · trans ∑ γ ∈ idxSet w, ∑ g : GLw w, ∑ h : GLw w,
              (coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * extMat K g.1 γ.2 γ.1) *
              (coeff β h * extMat K h.1 γ.1 γ.2)
          · rw [Finset.sum_comm]
            trans ∑ h : GLw w, ∑ γ ∈ idxSet w, ∑ g : GLw w,
                (coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩ g * extMat K g.1 γ.2 γ.1) *
                (coeff β h * extMat K h.1 γ.1 γ.2)
            · refine Finset.sum_congr rfl fun h _ => Finset.sum_comm
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun γ _ => Finset.sum_comm
          · refine Finset.sum_congr rfl fun γ _ => ?_
            simp only [evalExt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [Finset.mul_sum]
      rw [h2]
      have hterm : ∀ γ ∈ idxSet w,
          evalExt K (coeff ⟨(α.1.2, α.1.1), hswap_mem α⟩) γ.2 γ.1 *
          evalExt K (coeff β) γ.1 γ.2 =
            if γ = β.1 then (if α = β then 1 else 0) else 0 := by
        intro γ _
        rw [hcoeff ⟨(α.1.2, α.1.1), hswap_mem α⟩, hcoeff β]
        by_cases hγβ : γ = β.1
        · subst hγβ
          have hiff : (β.1.2 = α.1.2 ∧ β.1.1 = α.1.1) ↔ α = β := by
            constructor
            · intro ⟨h1, h2⟩
              apply Subtype.ext
              exact Prod.ext h2.symm h1.symm
            · rintro rfl
              exact ⟨rfl, rfl⟩
          simp [hiff]
        · have hnot : ¬ (γ.1 = β.1.1 ∧ γ.2 = β.1.2) := fun ⟨h1, h2⟩ =>
            hγβ (Prod.ext h1 h2)
          simp [hγβ, hnot]
      rw [Finset.sum_congr rfl hterm]
      simp [β.2]
    have hsurj : LinearMap.range U.mulVecLin = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨W.mulVec y, ?_⟩
      change U.mulVec (W.mulVec y) = y
      rw [Matrix.mulVec_mulVec, hUW, Matrix.one_mulVec]
    have hrank1 : Module.finrank K (LinearMap.range U.mulVecLin) = (idxSet w).card := by
      rw [hsurj, finrank_top, Module.finrank_pi, Fintype.card_coe]
    have hrank2 : Module.finrank K (LinearMap.range U.mulVecLin) ≤ d := by
      calc
        Module.finrank K (LinearMap.range U.mulVecLin)
            ≤ Module.finrank K (Fin d → K) := LinearMap.finrank_range_le U.mulVecLin
        _ = d := by rw [Module.finrank_pi, Fintype.card_fin]
    rw [← hrank1]
    exact hrank2
  · intro hle
    let eIdx : { α // α ∈ idxSet w } ≃ Fin (idxSet w).card :=
      (Fintype.equivFinOfCardEq (Fintype.card_coe (idxSet w)))
    let A : P → Fin d → K := fun p j =>
      if hj : j.val < (idxSet w).card then
        let α := (eIdx.symm ⟨j.val, hj⟩).1
        extMat K (LinearMap.toMatrix' (p.1 : V →ₗ[ZMod 2] V)) α.2 α.1
      else 0
    let B : P → Fin d → K := fun r j =>
      if hj : j.val < (idxSet w).card then
        let α := (eIdx.symm ⟨j.val, hj⟩).1
        extMat K (LinearMap.toMatrix' (r.1 : V →ₗ[ZMod 2] V)) α.1 α.2
      else 0
    refine ⟨A, B, fun p r => ?_⟩
    rw [fixed_eq_det]
    have hdet1 : ∀ f : V ≃ₗ[ZMod 2] V, (LinearMap.toMatrix' (f : V →ₗ[ZMod 2] V)).det = 1 := by
      intro f
      have hcomp : (f.symm : V →ₗ[ZMod 2] V).comp (f : V →ₗ[ZMod 2] V) = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact f.symm_apply_apply x
      have h1 := congrArg LinearMap.toMatrix' hcomp
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h1
      have h2 := congrArg Matrix.det h1
      rw [Matrix.det_mul, Matrix.det_one] at h2
      have hne : (LinearMap.toMatrix' (f : V →ₗ[ZMod 2] V)).det ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h2
        exact zero_ne_one h2
      exact z2_eq_one_of_ne_zero hne
    rw [det_one_add_eq_idxSet K _ _ (hdet1 r.1) (hdet1 p.1)]
    have hsum_drop :
        ∑ j : Fin d, A p j * B r j =
          ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < (idxSet w).card), A p j * B r j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin d => j.val < (idxSet w).card)]
      have h0 : ∑ j ∈ Finset.univ.filter (fun j : Fin d => ¬ j.val < (idxSet w).card), A p j * B r j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hnot : ¬ j.val < (idxSet w).card := (Finset.mem_filter.mp hj).2
        simp [A, B, hnot]
      rw [h0, add_zero]
    rw [hsum_drop]
    symm
    refine Finset.sum_bij
      (fun j hj => (eIdx.symm ⟨j.val, (Finset.mem_filter.mp hj).2⟩).1) ?_ ?_ ?_ ?_
    · intro j hj
      exact (eIdx.symm ⟨j.val, (Finset.mem_filter.mp hj).2⟩).2
    · intro j1 hj1 j2 hj2 heq
      have hsub : eIdx.symm ⟨j1.val, (Finset.mem_filter.mp hj1).2⟩ =
          eIdx.symm ⟨j2.val, (Finset.mem_filter.mp hj2).2⟩ := Subtype.ext heq
      have hfin := eIdx.symm.injective hsub
      exact Fin.ext (congrArg (fun x : Fin (idxSet w).card => x.val) hfin)
    · intro α hα
      let k := eIdx ⟨α, hα⟩
      refine ⟨⟨k.val, lt_of_lt_of_le k.isLt hle⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, ?_⟩
      change (eIdx.symm k).1 = α
      simp [k]
    · intro j hj
      have hlt : j.val < (idxSet w).card := (Finset.mem_filter.mp hj).2
      simp only [A, B, hlt, ↓reduceDIte]
      exact mul_comm _ _

end PEqualNP.Outside.L_lib_615_aux

theorem PEqualNP.Outside.L_lib_615 : (∀ (K : Type) [Field K] [CharP K 2] (b d : ℕ),
  let w := b + 1
  let V := Fin w → ZMod 2
  let P := (V ≃ₗ[ZMod 2] V) × V
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset V).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    Nat.choose (2 * w) w - 2 ≤ d) := by
  exact PEqualNP.Outside.L_lib_615_aux.main
