import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace PEqualNP.Outside.L_meta_25747

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_neg_eq (a : ZMod 2) : -a = a := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_neg_eq]

lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have h1 : a + b + b = 0 + b := congrArg (· + b) h
  rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h1
  exact h1

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma sum_dot {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ZMod 2) (v : Fin r → ZMod 2) :
    dotProduct (∑ i ∈ s, f i) v = ∑ i ∈ s, dotProduct (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_dotProduct]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_dotProduct, ih]

lemma vec_add_self {r : ℕ} (u : Fin r → ZMod 2) : u + u = 0 := by
  funext k
  exact zmod2_add_self (u k)

lemma vec_sub_eq_add {r : ℕ} (u v : Fin r → ZMod 2) : u - v = u + v := by
  funext k
  exact zmod2_sub_eq_add (u k) (v k)

lemma vec_add_cancel_right {r : ℕ} (u v : Fin r → ZMod 2) : u + v + v = u := by
  rw [add_assoc, vec_add_self, add_zero]

lemma vec_add_cancel_left {r : ℕ} (u v : Fin r → ZMod 2) : v + (v + u) = u := by
  rw [← add_assoc, vec_add_self, zero_add]

lemma dot_comm {r : ℕ} (u v : Fin r → ZMod 2) : dotProduct u v = dotProduct v u := by
  unfold dotProduct
  exact Finset.sum_congr rfl (fun k _ => mul_comm (u k) (v k))

lemma vec_eq_sum_single {r : ℕ} (v : Fin r → ZMod 2) :
    v = ∑ k : Fin r, v k • Pi.single k (1 : ZMod 2) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma exists_dot_eq_linearMap {r : ℕ} (f : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ u : Fin r → ZMod 2, ∀ v, dotProduct u v = f v := by
  refine ⟨fun k => f (Pi.single k 1), fun v => ?_⟩
  conv_rhs => rw [vec_eq_sum_single v]
  rw [map_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

lemma card_submodule {r : ℕ} (M : Submodule (ZMod 2) (Fin r → ZMod 2)) [Fintype M] :
    Fintype.card M = 2 ^ Module.finrank (ZMod 2) M := by
  let b := Module.finBasis (ZMod 2) M
  rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]

def dotBil {r : ℕ} (u : Fin r → ZMod 2) : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun w := dotProduct u w
  map_add' w₁ w₂ := dotProduct_add u w₁ w₂
  map_smul' c w := by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]

def orthoMap {r : ℕ} (A : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    (Fin r → ZMod 2) →ₗ[ZMod 2] (A →ₗ[ZMod 2] ZMod 2) where
  toFun w := (dotBil w).comp A.subtype
  map_add' w₁ w₂ := by
    ext ⟨u, _⟩
    exact add_dotProduct w₁ w₂ u
  map_smul' c w := by
    ext ⟨u, _⟩
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, dotBil, LinearMap.coe_mk,
      AddHom.coe_mk, smul_dotProduct, smul_eq_mul, LinearMap.smul_apply, RingHom.id_apply]

def ortho {r : ℕ} (A : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    Submodule (ZMod 2) (Fin r → ZMod 2) :=
  LinearMap.ker (orthoMap A)

lemma mem_ortho {r : ℕ} {A : Submodule (ZMod 2) (Fin r → ZMod 2)} {w : Fin r → ZMod 2} :
    w ∈ ortho A ↔ ∀ u ∈ A, dotProduct u w = 0 := by
  simp only [ortho, LinearMap.mem_ker, orthoMap, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.ext_iff, LinearMap.comp_apply, Submodule.coe_subtype, dotBil, LinearMap.zero_apply,
    Subtype.forall]
  constructor
  · intro h u hu
    rw [dot_comm]
    exact h u hu
  · intro h u hu
    rw [dot_comm]
    exact h u hu

lemma orthoMap_range_eq_top {r : ℕ} (A : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    LinearMap.range (orthoMap A) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨B, hAB⟩ := Submodule.exists_isCompl A
  let p : (Fin r → ZMod 2) →ₗ[ZMod 2] A :=
    (LinearMap.fst (ZMod 2) A B).comp (Submodule.prodEquivOfIsCompl A B hAB).symm.toLinearMap
  obtain ⟨w, hw⟩ := exists_dot_eq_linearMap (g.comp p)
  refine ⟨w, ?_⟩
  ext ⟨u, hu⟩
  change dotProduct w u = g ⟨u, hu⟩
  rw [hw u, LinearMap.comp_apply]
  congr 1
  have h1 : Submodule.prodEquivOfIsCompl A B hAB (⟨u, hu⟩, (0 : B)) = u := by
    change u + 0 = u
    rw [add_zero]
  have h2 : (Submodule.prodEquivOfIsCompl A B hAB).symm u = (⟨u, hu⟩, (0 : B)) := by
    rw [LinearEquiv.symm_apply_eq, h1]
  change (LinearMap.fst (ZMod 2) A B) ((Submodule.prodEquivOfIsCompl A B hAB).symm u) = ⟨u, hu⟩
  rw [h2, LinearMap.fst_apply]

lemma finrank_add_finrank_ortho {r : ℕ} (A : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) (ortho A) = r := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (orthoMap A)
  rw [orthoMap_range_eq_top A, Module.finrank_fin_fun] at h1
  have h2 : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (A →ₗ[ZMod 2] ZMod 2)) =
      Module.finrank (ZMod 2) (A →ₗ[ZMod 2] ZMod 2) := Submodule.topEquiv.finrank_eq
  let b := Module.finBasis (ZMod 2) A
  have h3 : Module.finrank (ZMod 2) (A →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) A := by
    rw [← (b.constr (ZMod 2)).finrank_eq, Module.finrank_fin_fun]
  rw [h2, h3] at h1
  exact h1

lemma even_finrank_sub_rad_aux {r : ℕ} :
    ∀ (m : ℕ) (U : Submodule (ZMod 2) (Fin r → ZMod 2)),
      Module.finrank (ZMod 2) U = m →
      ∀ (β : (Fin r → ZMod 2) → (Fin r → ZMod 2) → ZMod 2),
        (∀ u₁ ∈ U, ∀ u₂ ∈ U, ∀ v ∈ U, β (u₁ + u₂) v = β u₁ v + β u₂ v) →
        (∀ u ∈ U, ∀ v₁ ∈ U, ∀ v₂ ∈ U, β u (v₁ + v₂) = β u v₁ + β u v₂) →
        (∀ u ∈ U, β u u = 0) →
        ∀ (R : Submodule (ZMod 2) (Fin r → ZMod 2)),
          (∀ u, u ∈ R ↔ u ∈ U ∧ ∀ v ∈ U, β u v = 0) →
          Even (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) R) := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro U hm β haddL haddR halt R hR
    have hzeroR : ∀ u ∈ U, β u 0 = 0 := by
      intro u hu
      have h0 := haddR u hu 0 U.zero_mem 0 U.zero_mem
      rw [add_zero] at h0
      have h1 : β u 0 + β u 0 = β u 0 + 0 := by rw [← h0, add_zero]
      exact add_left_cancel h1
    have hsmulR : ∀ c : ZMod 2, ∀ u ∈ U, ∀ v ∈ U, β u (c • v) = c * β u v := by
      intro c u hu v hv
      rcases zmod2_cases c with rfl | rfl
      · rw [zero_smul, zero_mul, hzeroR u hu]
      · rw [one_smul, one_mul]
    have hsym : ∀ u ∈ U, ∀ v ∈ U, β u v = β v u := by
      intro u hu v hv
      have h0 := halt (u + v) (U.add_mem hu hv)
      rw [haddL u hu v hv (u + v) (U.add_mem hu hv),
        haddR u hu u hu v hv, haddR v hv u hu v hv,
        halt u hu, halt v hv, zero_add, add_zero] at h0
      exact zmod2_eq_of_add_eq_zero h0
    by_cases hAll : ∀ u ∈ U, ∀ v ∈ U, β u v = 0
    · have hRU : R = U := by
        ext u
        rw [hR]
        exact ⟨fun h => h.1, fun hu => ⟨hu, hAll u hu⟩⟩
      rw [hRU, Nat.sub_self]
      exact ⟨0, rfl⟩
    · push Not at hAll
      obtain ⟨e, he, f, hf, hef_ne⟩ := hAll
      have hef : β e f = 1 := zmod2_eq_one_of_ne_zero hef_ne
      have hfe : β f e = 1 := by rw [hsym f hf e he, hef]
      let φ : U →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
        { toFun := fun u => (β e u.1, β f u.1)
          map_add' := fun u₁ u₂ => by
            ext
            · exact haddR e he u₁.1 u₁.2 u₂.1 u₂.2
            · exact haddR f hf u₁.1 u₁.2 u₂.1 u₂.2
          map_smul' := fun c u => by
            ext
            · exact hsmulR c e he u.1 u.2
            · exact hsmulR c f hf u.1 u.2 }
      have hφ_top : LinearMap.range φ = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨a, b⟩ _
        let u : U := ⟨b • e + a • f, U.add_mem (U.smul_mem b he) (U.smul_mem a hf)⟩
        refine ⟨u, ?_⟩
        ext
        · change β e (b • e + a • f) = a
          rw [haddR e he _ (U.smul_mem b he) _ (U.smul_mem a hf),
            hsmulR b e he e he, hsmulR a e he f hf, halt e he, hef, mul_zero, mul_one, zero_add]
        · change β f (b • e + a • f) = b
          rw [haddR f hf _ (U.smul_mem b he) _ (U.smul_mem a hf),
            hsmulR b f hf e he, hsmulR a f hf f hf, hfe, halt f hf, mul_one, mul_zero, add_zero]
      let U' : Submodule (ZMod 2) (Fin r → ZMod 2) := (LinearMap.ker φ).map U.subtype
      have hU'_mem : ∀ u, u ∈ U' ↔ u ∈ U ∧ β e u = 0 ∧ β f u = 0 := by
        intro u
        simp only [U', Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
        constructor
        · rintro ⟨⟨v, hv⟩, hφv, rfl⟩
          exact ⟨hv, congrArg Prod.fst hφv, congrArg Prod.snd hφv⟩
        · rintro ⟨hu, h1, h2⟩
          refine ⟨⟨u, hu⟩, ?_, rfl⟩
          exact Prod.ext h1 h2
      have hU'_le : U' ≤ U := fun u hu => (hU'_mem u).mp hu |>.1
      have hfin_ker : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) (LinearMap.ker φ) := by
        let g : LinearMap.ker φ →ₗ[ZMod 2] (Fin r → ZMod 2) := U.subtype.comp (LinearMap.ker φ).subtype
        have hg_inj : Function.Injective g :=
          Subtype.val_injective.comp Subtype.val_injective
        have hg_range : LinearMap.range g = U' := by
          ext u
          simp only [LinearMap.mem_range, U', Submodule.mem_map, Submodule.coe_subtype, g,
            LinearMap.comp_apply, Subtype.exists, exists_prop]
        rw [← hg_range]
        exact (LinearEquiv.ofInjective g hg_inj).finrank_eq.symm
      have hrank_split : Module.finrank (ZMod 2) U' + 2 = Module.finrank (ZMod 2) U := by
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        rw [hφ_top, Submodule.topEquiv.finrank_eq, Module.finrank_prod, Module.finrank_self] at hrn
        rw [hfin_ker]
        omega
      have hR_U' : ∀ u, u ∈ R ↔ u ∈ U' ∧ ∀ v ∈ U', β u v = 0 := by
        intro u
        rw [hR, hU'_mem]
        constructor
        · rintro ⟨hu, hall⟩
          refine ⟨⟨hu, ?_, ?_⟩, fun v hv => hall v (hU'_le hv)⟩
          · rw [hsym e he u hu]
            exact hall e he
          · rw [hsym f hf u hu]
            exact hall f hf
        · rintro ⟨⟨hu, heu, hfu⟩, hall'⟩
          refine ⟨hu, fun v hv => ?_⟩
          let v' := v + β f v • e + β e v • f
          have hv'_U : v' ∈ U :=
            U.add_mem (U.add_mem hv (U.smul_mem _ he)) (U.smul_mem _ hf)
          have hv'_U' : v' ∈ U' := by
            rw [hU'_mem]
            refine ⟨hv'_U, ?_, ?_⟩
            · rw [haddR e he _ (U.add_mem hv (U.smul_mem _ he)) _ (U.smul_mem _ hf),
                haddR e he v hv _ (U.smul_mem _ he),
                hsmulR _ e he e he, hsmulR _ e he f hf,
                halt e he, hef, mul_zero, add_zero, mul_one, zmod2_add_self]
            · rw [haddR f hf _ (U.add_mem hv (U.smul_mem _ he)) _ (U.smul_mem _ hf),
                haddR f hf v hv _ (U.smul_mem _ he),
                hsmulR _ f hf e he, hsmulR _ f hf f hf,
                hfe, halt f hf, mul_one, mul_zero, add_zero, zmod2_add_self]
          have h0 := hall' v' hv'_U'
          rw [haddR u hu _ (U.add_mem hv (U.smul_mem _ he)) _ (U.smul_mem _ hf),
            haddR u hu v hv _ (U.smul_mem _ he),
            hsmulR _ u hu e he, hsmulR _ u hu f hf,
            hsym u hu e he, hsym u hu f hf, heu, hfu, mul_zero, mul_zero, add_zero, add_zero] at h0
          exact h0
      have hih := ih (Module.finrank (ZMod 2) U') (by omega) U' rfl β
        (fun u₁ hu₁ u₂ hu₂ v hv => haddL u₁ (hU'_le hu₁) u₂ (hU'_le hu₂) v (hU'_le hv))
        (fun u hu v₁ hv₁ v₂ hv₂ => haddR u (hU'_le hu) v₁ (hU'_le hv₁) v₂ (hU'_le hv₂))
        (fun u hu => halt u (hU'_le hu)) R hR_U'
      have hR_le_U' : R ≤ U' := fun u hu => (hR_U' u).mp hu |>.1
      have hR_le_rank : Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) U' :=
        Submodule.finrank_mono hR_le_U'
      have hsub_eq : Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) R =
          (Module.finrank (ZMod 2) U' - Module.finrank (ZMod 2) R) + 2 := by omega
      rw [hsub_eq]
      exact hih.add ⟨1, rfl⟩

lemma min_sum_le_sum_min {α : Type*} [DecidableEq α] (M : ℕ) (s : Finset α) (f : α → ℕ) :
    min M (∑ x ∈ s, f x) ≤ ∑ x ∈ s, min M (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hstep : min M (f a + ∑ x ∈ s, f x) ≤ min M (f a) + min M (∑ x ∈ s, f x) := by omega
    exact le_trans hstep (Nat.add_le_add_left ih _)

lemma card_filter_mem_finset {r n c : ℕ} (x : Fin n → Fin r → ZMod 2)
    (hx : ∀ v, (Finset.univ.filter (fun i : Fin n => x i = v)).card = c)
    (T : Finset (Fin r → ZMod 2)) :
    (Finset.univ.filter (fun i : Fin n => x i ∈ T)).card = c * T.card := by
  have hpart : (Finset.univ.filter (fun i : Fin n => x i ∈ T)).card =
      ∑ v ∈ T, ((Finset.univ.filter (fun i : Fin n => x i ∈ T)).filter (fun i => x i = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [hpart]
  have hcongr : ∀ v ∈ T,
      ((Finset.univ.filter (fun i : Fin n => x i ∈ T)).filter (fun i => x i = v)).card = c := by
    intro v hv
    rw [← hx v]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, mul_comm]

lemma card_coset_eq_pow_finrank {r : ℕ} (M : Submodule (ZMod 2) (Fin r → ZMod 2))
    [DecidablePred (· ∈ M)] (shift : Fin r → ZMod 2) :
    (Finset.univ.filter (fun z : Fin r → ZMod 2 => z + shift ∈ M)).card =
      2 ^ Module.finrank (ZMod 2) M := by
  classical
  have hcard : Fintype.card M =
      (Finset.univ.filter (fun z : Fin r → ZMod 2 => z + shift ∈ M)).card := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun (m : M) _ => m.1 + shift) ?_ ?_ ?_
    · intro m _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [vec_add_cancel_right]; exact m.2⟩
    · intro m₁ _ m₂ _ h
      exact Subtype.ext (add_right_cancel h)
    · intro z hz
      have hzm : z + shift ∈ M := (Finset.mem_filter.mp hz).2
      exact ⟨⟨z + shift, hzm⟩, Finset.mem_univ _, vec_add_cancel_right z shift⟩
  rw [← hcard]
  exact card_submodule M

lemma card_filter_coset_eq {r n c : ℕ} (x : Fin n → Fin r → ZMod 2)
    (hx : ∀ v, (Finset.univ.filter (fun i : Fin n => x i = v)).card = c)
    (M : Submodule (ZMod 2) (Fin r → ZMod 2)) [DecidablePred (· ∈ M)]
    (shift : Fin r → ZMod 2) :
    (Finset.univ.filter (fun i : Fin n => x i + shift ∈ M)).card =
      c * 2 ^ Module.finrank (ZMod 2) M := by
  let T : Finset (Fin r → ZMod 2) := Finset.univ.filter (fun z => z + shift ∈ M)
  have heq : Finset.univ.filter (fun i : Fin n => x i + shift ∈ M) =
      Finset.univ.filter (fun i : Fin n => x i ∈ T) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
  rw [heq, card_filter_mem_finset x hx T, card_coset_eq_pow_finrank M shift]

lemma forward_dir {r c t : ℕ}
    (x y : Fin (c * 2 ^ r) → Fin r → ZMod 2)
    (hx : ∀ v : Fin r → ZMod 2,
      (Finset.univ.filter (fun i : Fin (c * 2 ^ r) => x i = v)).card = c)
    (π : Equiv.Perm (Fin (c * 2 ^ r)))
    (K : Finset (Fin (c * 2 ^ r)))
    (hKt : c * 2 ^ r ≤ K.card + t)
    (hK : ∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0) :
    ∃ (d : ℕ) (W : Finset (Fin r → ZMod 2)) (a δ : Fin r → ZMod 2),
      d ≤ r ∧ W.card = 2 ^ d ∧ 0 ∈ W ∧ (∀ v ∈ W, ∀ w ∈ W, v + w ∈ W) ∧
      δ ∈ W ∧ (δ = 0 ↔ Even d) ∧
      let bins := W.image (fun w => ({a + w, a + w + δ} : Finset (Fin r → ZMod 2)))
      c * 2 ^ r ≤ t + ∑ bin ∈ bins,
        min (c * 2 ^ (r - d)) (Finset.univ.filter (fun i : Fin (c * 2 ^ r) => y i ∈ bin)).card := by
  classical
  by_cases hKe : K = ∅
  · subst hKe
    refine ⟨0, {0}, 0, 0, Nat.zero_le r, by simp, by simp, ?_, by simp, ?_, ?_⟩
    · intro v hv w hw
      simp only [Finset.mem_singleton] at hv hw ⊢
      rw [hv, hw, add_zero]
    · simp only [true_iff]
      exact ⟨0, rfl⟩
    · simp only [Finset.card_empty, zero_add] at hKt
      exact le_trans hKt (Nat.le_add_right _ _)
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hKe
    let x₀ : Fin r → ZMod 2 := x i₀
    let a : Fin r → ZMod 2 := y (π i₀)
    let u : Fin (c * 2 ^ r) → (Fin r → ZMod 2) := fun i => x i + x₀
    let v : Fin (c * 2 ^ r) → (Fin r → ZMod 2) := fun i => y (π i) + a
    have huv_diff : ∀ i ∈ K, ∀ j ∈ K, dotProduct (u i + u j) (v i + v j) = 0 := by
      intro i hi j hj
      have h1 : u i + u j = x i - x j := by
        rw [vec_sub_eq_add]
        funext k
        simp only [u, Pi.add_apply]
        have : x i k + x₀ k + (x j k + x₀ k) = x i k + x j k + (x₀ k + x₀ k) := by ring
        rw [this, zmod2_add_self, add_zero]
      have h2 : v i + v j = y (π i) - y (π j) := by
        rw [vec_sub_eq_add]
        funext k
        simp only [v, Pi.add_apply]
        have : y (π i) k + a k + (y (π j) k + a k) = y (π i) k + y (π j) k + (a k + a k) := by ring
        rw [this, zmod2_add_self, add_zero]
      rw [h1, h2]
      exact hK i hi j hj
    have huv_self : ∀ i ∈ K, dotProduct (u i) (v i) = 0 := by
      intro i hi
      have h0 := huv_diff i hi i₀ hi₀
      have hu0 : u i₀ = 0 := vec_add_self x₀
      have hv0 : v i₀ = 0 := vec_add_self a
      rw [hu0, hv0, add_zero, add_zero] at h0
      exact h0
    have huv_sym : ∀ i ∈ K, ∀ j ∈ K, dotProduct (u i) (v j) = dotProduct (u j) (v i) := by
      intro i hi j hj
      have h0 := huv_diff i hi j hj
      rw [add_dotProduct (u i) (u j) (v i + v j),
        dotProduct_add (u i) (v i) (v j), dotProduct_add (u j) (v i) (v j),
        huv_self i hi, huv_self j hj, zero_add, add_zero] at h0
      exact zmod2_eq_of_add_eq_zero h0
    let gen : Set ((Fin r → ZMod 2) × (Fin r → ZMod 2)) := { p | ∃ i ∈ K, p = (u i, v i) }
    let S₀ : Submodule (ZMod 2) ((Fin r → ZMod 2) × (Fin r → ZMod 2)) := Submodule.span (ZMod 2) gen
    have hS₀_sym : ∀ p ∈ S₀, ∀ q ∈ S₀, dotProduct p.1 q.2 = dotProduct q.1 p.2 := by
      intro p hp
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
      · rintro _ ⟨i, hi, rfl⟩ q hq
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
        · rintro _ ⟨j, hj, rfl⟩
          exact huv_sym i hi j hj
        · simp only [Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct]
        · intro q₁ q₂ _ _ h1 h2
          simp only [Prod.snd_add, Prod.fst_add, dotProduct_add, add_dotProduct, h1, h2]
        · intro c₁ q₁ _ h1
          simp only [Prod.smul_snd, Prod.smul_fst, dotProduct_smul, smul_dotProduct, h1]
      · intro q _
        simp only [Prod.fst_zero, Prod.snd_zero, zero_dotProduct, dotProduct_zero]
      · intro p₁ p₂ _ _ h1 h2 q hq
        simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1 q hq,
          h2 q hq]
      · intro c₁ p₁ _ h1 q hq
        simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, h1 q hq]
    have hS₀_quad : ∀ p ∈ S₀, dotProduct p.1 p.2 = 0 := by
      intro p hp
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
      · rintro _ ⟨i, hi, rfl⟩
        exact huv_self i hi
      · simp only [Prod.fst_zero, Prod.snd_zero, zero_dotProduct]
      · intro p₁ p₂ hp₁ hp₂ h1 h2
        simp only [Prod.fst_add, Prod.snd_add]
        rw [add_dotProduct, dotProduct_add, dotProduct_add, h1, h2, zero_add, add_zero,
          hS₀_sym p₁ hp₁ p₂ hp₂, zmod2_add_self]
      · intro c₁ p₁ _ h1
        simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, h1, smul_zero]
    let U : Submodule (ZMod 2) (Fin r → ZMod 2) :=
      S₀.map (LinearMap.fst (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2))
    let S : Submodule (ZMod 2) ((Fin r → ZMod 2) × (Fin r → ZMod 2)) :=
      S₀ ⊔ (ortho U).map (LinearMap.inr (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2))
    have hS_mem : ∀ p, p ∈ S ↔ ∃ p₀ ∈ S₀, ∃ w ∈ ortho U, p = (p₀.1, p₀.2 + w) := by
      intro p
      simp only [S, Submodule.mem_sup, Submodule.mem_map, LinearMap.inr_apply]
      constructor
      · rintro ⟨p₀, hp₀, _, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨p₀, hp₀, w, hw, Prod.ext (add_zero _) rfl⟩
      · rintro ⟨p₀, hp₀, w, hw, rfl⟩
        exact ⟨p₀, hp₀, (0, w), ⟨w, hw, rfl⟩, Prod.ext (add_zero _) rfl⟩
    have hS_sym : ∀ p ∈ S, ∀ q ∈ S, dotProduct p.1 q.2 = dotProduct q.1 p.2 := by
      intro p hp q hq
      obtain ⟨p₀, hp₀, wp, hwp, rfl⟩ := (hS_mem p).mp hp
      obtain ⟨q₀, hq₀, wq, hwq, rfl⟩ := (hS_mem q).mp hq
      have hpU : p₀.1 ∈ U := ⟨p₀, hp₀, rfl⟩
      have hqU : q₀.1 ∈ U := ⟨q₀, hq₀, rfl⟩
      dsimp only
      rw [dotProduct_add, dotProduct_add, mem_ortho.mp hwq p₀.1 hpU,
        mem_ortho.mp hwp q₀.1 hqU, add_zero, add_zero]
      exact hS₀_sym p₀ hp₀ q₀ hq₀
    have hS_quad : ∀ p ∈ S, dotProduct p.1 p.2 = 0 := by
      intro p hp
      obtain ⟨p₀, hp₀, wp, hwp, rfl⟩ := (hS_mem p).mp hp
      have hpU : p₀.1 ∈ U := ⟨p₀, hp₀, rfl⟩
      dsimp only
      rw [dotProduct_add, hS₀_quad p₀ hp₀, mem_ortho.mp hwp p₀.1 hpU, add_zero]
    have hS_fst_eq : S.map (LinearMap.fst (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2)) = U := by
      ext x₁
      simp only [Submodule.mem_map, LinearMap.fst_apply, U]
      constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨p₀, hp₀, w, _, rfl⟩ := (hS_mem p).mp hp
        exact ⟨p₀, hp₀, rfl⟩
      · rintro ⟨p₀, hp₀, rfl⟩
        exact ⟨p₀, Submodule.mem_sup_left hp₀, rfl⟩
    have hS_zero_fst : ∀ w, ((0 : Fin r → ZMod 2), w) ∈ S ↔ w ∈ ortho U := by
      intro w
      constructor
      · intro hw
        rw [mem_ortho]
        intro x₁ hx₁
        obtain ⟨p₀, hp₀, rfl⟩ := hx₁
        have h := hS_sym p₀ (Submodule.mem_sup_left hp₀) (0, w) hw
        simp only [zero_dotProduct] at h
        exact h
      · intro hw
        exact Submodule.mem_sup_right ⟨w, hw, rfl⟩
    let Krad : Submodule (ZMod 2) (Fin r → ZMod 2) :=
      S.comap (LinearMap.inl (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2))
    let W₀ : Submodule (ZMod 2) (Fin r → ZMod 2) :=
      S.map (LinearMap.snd (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2))
    have hfinS : Module.finrank (ZMod 2) S = r := by
      let f₁ : S →ₗ[ZMod 2] (Fin r → ZMod 2) :=
        (LinearMap.fst (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2)).comp S.subtype
      have hf₁_range : LinearMap.range f₁ = U := by
        rw [← hS_fst_eq]
        ext x₁
        simp only [LinearMap.mem_range, Submodule.mem_map, f₁, LinearMap.comp_apply,
          Submodule.coe_subtype, Subtype.exists, exists_prop]
      let e₁ : LinearMap.ker f₁ ≃ₗ[ZMod 2] ortho U :=
        { toFun := fun ⟨⟨⟨u₁, w₁⟩, hp⟩, hker⟩ =>
            ⟨w₁, (hS_zero_fst w₁).mp (by
              have hu₁ : u₁ = 0 := hker
              subst hu₁; exact hp)⟩
          invFun := fun ⟨w₁, hw₁⟩ => ⟨⟨(0, w₁), (hS_zero_fst w₁).mpr hw₁⟩, rfl⟩
          left_inv := fun ⟨⟨⟨u₁, w₁⟩, hp⟩, hker⟩ => by
            have hu₁ : u₁ = 0 := hker
            subst hu₁
            rfl
          right_inv := fun ⟨w₁, hw₁⟩ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hrn := LinearMap.finrank_range_add_finrank_ker f₁
      rw [hf₁_range, e₁.finrank_eq, finrank_add_finrank_ortho U] at hrn
      exact hrn.symm
    have hfinW_K : Module.finrank (ZMod 2) W₀ + Module.finrank (ZMod 2) Krad = r := by
      let f₂ : S →ₗ[ZMod 2] (Fin r → ZMod 2) :=
        (LinearMap.snd (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2)).comp S.subtype
      have hf₂_range : LinearMap.range f₂ = W₀ := by
        ext w₁
        simp only [LinearMap.mem_range, W₀, Submodule.mem_map, f₂, LinearMap.comp_apply,
          Submodule.coe_subtype, Subtype.exists, exists_prop]
      let e₂ : LinearMap.ker f₂ ≃ₗ[ZMod 2] Krad :=
        { toFun := fun ⟨⟨⟨u₁, w₁⟩, hp⟩, hker⟩ =>
            ⟨u₁, by
              have hw₁ : w₁ = 0 := hker
              subst hw₁; exact hp⟩
          invFun := fun ⟨u₁, hu₁⟩ => ⟨⟨(u₁, 0), hu₁⟩, rfl⟩
          left_inv := fun ⟨⟨⟨u₁, w₁⟩, hp⟩, hker⟩ => by
            have hw₁ : w₁ = 0 := hker
            subst hw₁
            rfl
          right_inv := fun ⟨u₁, hu₁⟩ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hrn := LinearMap.finrank_range_add_finrank_ker f₂
      rw [hf₂_range, e₂.finrank_eq, hfinS] at hrn
      exact hrn
    have horthoU_le_W₀ : ortho U ≤ W₀ := fun w hw => ⟨(0, w), (hS_zero_fst w).mpr hw, rfl⟩
    have hKrad_le_U : Krad ≤ U := by
      intro x₁ hx₁
      rw [← hS_fst_eq]
      exact ⟨(x₁, 0), hx₁, rfl⟩
    let β : (Fin r → ZMod 2) → (Fin r → ZMod 2) → ZMod 2 := fun x₁ x₂ =>
      if h : ∃ w, (x₁, w) ∈ S then dotProduct x₂ (Classical.choose h) else 0
    have hβ_eq : ∀ x₁ w, (x₁, w) ∈ S → ∀ x₂ ∈ U, β x₁ x₂ = dotProduct x₂ w := by
      intro x₁ w hxw x₂ hx₂
      have hex : ∃ w', (x₁, w') ∈ S := ⟨w, hxw⟩
      simp only [β, hex, ↓reduceDIte]
      have hch : (x₁, Classical.choose hex) ∈ S := Classical.choose_spec hex
      have hdiff : ((0 : Fin r → ZMod 2), Classical.choose hex + w) ∈ S := by
        have hsum := S.add_mem hch hxw
        simpa only [Prod.mk_add_mk, vec_add_self] using hsum
      have hwo : Classical.choose hex + w ∈ ortho U := (hS_zero_fst _).mp hdiff
      have h0 : dotProduct x₂ (Classical.choose hex + w) = 0 := mem_ortho.mp hwo x₂ hx₂
      rw [dotProduct_add] at h0
      exact zmod2_eq_of_add_eq_zero h0
    have hU_exists : ∀ x₁ ∈ U, ∃ w, (x₁, w) ∈ S := by
      intro x₁ hx₁
      rw [← hS_fst_eq] at hx₁
      obtain ⟨⟨a₁, w⟩, hp, rfl⟩ := hx₁
      exact ⟨w, hp⟩
    have hEven_UK : Even (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) Krad) := by
      refine even_finrank_sub_rad_aux (Module.finrank (ZMod 2) U) U rfl β ?_ ?_ ?_ Krad ?_
      · intro u₁ hu₁ u₂ hu₂ x₂ hx₂
        obtain ⟨w₁, hw₁⟩ := hU_exists u₁ hu₁
        obtain ⟨w₂, hw₂⟩ := hU_exists u₂ hu₂
        have h12 : (u₁ + u₂, w₁ + w₂) ∈ S := S.add_mem hw₁ hw₂
        rw [hβ_eq (u₁ + u₂) (w₁ + w₂) h12 x₂ hx₂,
          hβ_eq u₁ w₁ hw₁ x₂ hx₂, hβ_eq u₂ w₂ hw₂ x₂ hx₂, dotProduct_add]
      · intro u₁ hu₁ v₁ hv₁ v₂ hv₂
        obtain ⟨w₁, hw₁⟩ := hU_exists u₁ hu₁
        rw [hβ_eq u₁ w₁ hw₁ (v₁ + v₂) (U.add_mem hv₁ hv₂),
          hβ_eq u₁ w₁ hw₁ v₁ hv₁, hβ_eq u₁ w₁ hw₁ v₂ hv₂, add_dotProduct]
      · intro u₁ hu₁
        obtain ⟨w₁, hw₁⟩ := hU_exists u₁ hu₁
        rw [hβ_eq u₁ w₁ hw₁ u₁ hu₁]
        exact hS_quad (u₁, w₁) hw₁
      · intro x₁
        constructor
        · intro hx₁
          refine ⟨hKrad_le_U hx₁, fun x₂ hx₂ => ?_⟩
          rw [hβ_eq x₁ 0 hx₁ x₂ hx₂, dotProduct_zero]
        · rintro ⟨hx₁, hall⟩
          obtain ⟨w, hw⟩ := hU_exists x₁ hx₁
          have hwo : w ∈ ortho U := by
            rw [mem_ortho]
            intro x₂ hx₂
            rw [← hβ_eq x₁ w hw x₂ hx₂]
            exact hall x₂ hx₂
          have h0w : ((0 : Fin r → ZMod 2), w) ∈ S := (hS_zero_fst w).mpr hwo
          have hsum : (x₁, (0 : Fin r → ZMod 2)) ∈ S := by
            have h := S.add_mem hw h0w
            simpa only [Prod.mk_add_mk, add_zero, vec_add_self] using h
          exact hsum
    let d : ℕ := Module.finrank (ZMod 2) W₀
    have hd_le : d ≤ r := by dsimp only [d]; omega
    have hKrad_rank : Module.finrank (ZMod 2) Krad = r - d := by dsimp only [d]; omega
    have hEven_W_orthoU : Even (d - Module.finrank (ZMod 2) (ortho U)) := by
      have h1 := finrank_add_finrank_ortho U
      have h2 : Module.finrank (ZMod 2) Krad ≤ Module.finrank (ZMod 2) U :=
        Submodule.finrank_mono hKrad_le_U
      have h3 : Module.finrank (ZMod 2) (ortho U) ≤ d :=
        Submodule.finrank_mono horthoU_le_W₀
      have heq : d - Module.finrank (ZMod 2) (ortho U) =
          Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) Krad := by dsimp only [d]; omega
      rw [heq]
      exact hEven_UK
    have hex_δ : ∃ δ ∈ ortho U, δ = 0 ↔ Even d := by
      by_cases hed : Even d
      · exact ⟨0, (ortho U).zero_mem, ⟨fun _ => hed, fun _ => rfl⟩⟩
      · have hne_ortho : Module.finrank (ZMod 2) (ortho U) ≠ 0 := by
          intro hz
          rw [hz, Nat.sub_zero] at hEven_W_orthoU
          exact hed hEven_W_orthoU
        have hnt : ortho U ≠ ⊥ := by
          intro hbot
          apply hne_ortho
          rw [hbot]
          exact finrank_bot (ZMod 2) (Fin r → ZMod 2)
        have hex : ∃ δ ∈ ortho U, δ ≠ 0 := by
          by_contra hnone
          push Not at hnone
          apply hnt
          rw [eq_bot_iff]
          exact fun z hz => hnone z hz
        obtain ⟨δ, hδo, hδne⟩ := hex
        exact ⟨δ, hδo, ⟨fun h => absurd h hδne, fun h => absurd h hed⟩⟩
    obtain ⟨δ, hδ_ortho, hδEven⟩ := hex_δ
    let W : Finset (Fin r → ZMod 2) := Finset.univ.filter (fun w => w ∈ W₀)
    have hW_mem : ∀ w, w ∈ W ↔ w ∈ W₀ := by
      intro w
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
    have hW_card : W.card = 2 ^ d := by
      have h1 : Fintype.card W₀ = W.card := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun (w : W₀) _ => w.1) ?_ ?_ ?_
        · intro w _; exact (hW_mem w.1).mpr w.2
        · intro w₁ _ w₂ _ h; exact Subtype.ext h
        · intro w hw; exact ⟨⟨w, (hW_mem w).mp hw⟩, Finset.mem_univ _, rfl⟩
      rw [← h1]
      exact card_submodule W₀
    refine ⟨d, W, a, δ, hd_le, hW_card, (hW_mem 0).mpr W₀.zero_mem,
      fun w₁ hw₁ w₂ hw₂ => (hW_mem _).mpr (W₀.add_mem ((hW_mem w₁).mp hw₁) ((hW_mem w₂).mp hw₂)),
      (hW_mem δ).mpr (horthoU_le_W₀ hδ_ortho), hδEven, ?_⟩
    dsimp only
    let bins : Finset (Finset (Fin r → ZMod 2)) :=
      W.image (fun w => ({a + w, a + w + δ} : Finset (Fin r → ZMod 2)))
    let cOf : (Fin r → ZMod 2) → Finset (Fin r → ZMod 2) :=
      fun w => Finset.univ.filter (fun z => z + a + w ∈ ortho U)
    let coarse : Finset (Finset (Fin r → ZMod 2)) := W.image cOf
    have hcOf_mem : ∀ w z, z ∈ cOf w ↔ z + a + w ∈ ortho U := by
      intro w z
      simp only [cOf, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcOf_disj : ∀ C₁ ∈ coarse, ∀ C₂ ∈ coarse, C₁ ≠ C₂ → Disjoint C₁ C₂ := by
      intro C₁ hC₁ C₂ hC₂ hne
      obtain ⟨w₁, _, rfl⟩ := Finset.mem_image.mp hC₁
      obtain ⟨w₂, _, rfl⟩ := Finset.mem_image.mp hC₂
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      apply hne
      have h1 := (hcOf_mem w₁ z).mp hz₁
      have h2 := (hcOf_mem w₂ z).mp hz₂
      have hw12 : w₁ + w₂ ∈ ortho U := by
        have hsum := (ortho U).add_mem h1 h2
        have heq : z + a + w₁ + (z + a + w₂) = w₁ + w₂ := by
          funext k
          simp only [Pi.add_apply]
          have : z k + a k + w₁ k + (z k + a k + w₂ k) =
              w₁ k + w₂ k + ((z k + z k) + (a k + a k)) := by ring
          rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
        rw [heq] at hsum
        exact hsum
      ext z'
      rw [hcOf_mem, hcOf_mem]
      constructor
      · intro h'
        have hsum := (ortho U).add_mem h' hw12
        have heq : z' + a + w₁ + (w₁ + w₂) = z' + a + w₂ := by
          rw [add_assoc, ← add_assoc w₁, vec_add_self, zero_add]
        rw [heq] at hsum
        exact hsum
      · intro h'
        have hsum := (ortho U).add_mem h' hw12
        have heq : z' + a + w₂ + (w₁ + w₂) = z' + a + w₁ := by
          rw [add_comm w₁ w₂, add_assoc, ← add_assoc w₂, vec_add_self, zero_add]
        rw [heq] at hsum
        exact hsum
    have hK_eq_sum : K.card = ∑ C ∈ coarse, (K.filter (fun i => y (π i) ∈ C)).card := by
      have hcov : K = coarse.biUnion (fun C => K.filter (fun i => y (π i) ∈ C)) := by
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hi
          have hvi_W : v i ∈ W := by
            rw [hW_mem]
            exact ⟨(u i, v i), Submodule.mem_sup_left (Submodule.subset_span ⟨i, hi, rfl⟩), rfl⟩
          refine ⟨cOf (v i), Finset.mem_image_of_mem cOf hvi_W, hi, ?_⟩
          rw [hcOf_mem]
          have heq : y (π i) + a + v i = 0 := vec_add_self (y (π i) + a)
          rw [heq]
          exact (ortho U).zero_mem
        · rintro ⟨_, _, hi, _⟩
          exact hi
      conv_lhs => rw [hcov]
      rw [Finset.card_biUnion]
      intro C₁ hC₁ C₂ hC₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      exact Finset.disjoint_left.mp (hcOf_disj C₁ hC₁ C₂ hC₂ hne)
        (Finset.mem_filter.mp hi₁).2 (Finset.mem_filter.mp hi₂).2
    have hcoarse_bound : ∀ C ∈ coarse,
        (K.filter (fun i => y (π i) ∈ C)).card ≤
          min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ C)).card := by
      intro C hC
      apply le_min
      · obtain ⟨w₀, hw₀W, rfl⟩ := Finset.mem_image.mp hC
        have hw₀ : w₀ ∈ W₀ := (hW_mem w₀).mp hw₀W
        obtain ⟨⟨u₀, w₀'⟩, hu₀w₀, hw₀eq⟩ := hw₀
        subst hw₀eq
        have hsub : K.filter (fun i => y (π i) ∈ cOf w₀') ⊆
            Finset.univ.filter (fun i : Fin (c * 2 ^ r) => x i + (x₀ + u₀) ∈ Krad) := by
          intro i hi
          obtain ⟨hiK, hiC⟩ := Finset.mem_filter.mp hi
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have h1 : (u i, v i) ∈ S := Submodule.mem_sup_left (Submodule.subset_span ⟨i, hiK, rfl⟩)
          have h2 : ((0 : Fin r → ZMod 2), v i + w₀') ∈ S :=
            (hS_zero_fst _).mpr ((hcOf_mem w₀' (y (π i))).mp hiC)
          have h3 := S.add_mem (S.add_mem h1 hu₀w₀) h2
          have hf : u i + u₀ + 0 = x i + (x₀ + u₀) := by rw [add_zero, add_assoc]
          have hs : v i + w₀' + (v i + w₀') = 0 := vec_add_self (v i + w₀')
          simp only [Prod.mk_add_mk, hf, hs] at h3
          exact h3
        calc (K.filter (fun i => y (π i) ∈ cOf w₀')).card
            ≤ (Finset.univ.filter (fun i : Fin (c * 2 ^ r) => x i + (x₀ + u₀) ∈ Krad)).card :=
              Finset.card_le_card hsub
          _ = c * 2 ^ Module.finrank (ZMod 2) Krad := card_filter_coset_eq x hx Krad (x₀ + u₀)
          _ = c * 2 ^ (r - d) := by rw [hKrad_rank]
      · refine Finset.card_le_card_of_injOn π ?_ (π.injective.injOn)
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi.2
    have hbin_disj : ∀ B₁ ∈ bins, ∀ B₂ ∈ bins, B₁ ≠ B₂ → Disjoint B₁ B₂ := by
      intro B₁ hB₁ B₂ hB₂ hne
      obtain ⟨w₁, _, rfl⟩ := Finset.mem_image.mp hB₁
      obtain ⟨w₂, _, rfl⟩ := Finset.mem_image.mp hB₂
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz₁ hz₂
      rcases hz₁ with rfl | rfl <;> rcases hz₂ with h | h
      · rw [h]
      · rw [h, add_assoc (a + w₂), vec_add_self, add_zero, Finset.pair_comm]
      · rw [← h, add_assoc (a + w₁), vec_add_self, add_zero, Finset.pair_comm]
      · have h' : a + w₁ = a + w₂ := add_right_cancel h
        rw [h']
    have hcoarse_split : ∀ C ∈ coarse,
        (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ C)).card =
          ∑ B ∈ bins.filter (· ⊆ C),
            (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card := by
      intro C hC
      obtain ⟨w₀, hw₀W, rfl⟩ := Finset.mem_image.mp hC
      have hcov : Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ cOf w₀) =
          (bins.filter (· ⊆ cOf w₀)).biUnion
            (fun B => Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · intro hj
          have hwj_ortho : y j + a + w₀ ∈ ortho U := (hcOf_mem w₀ (y j)).mp hj
          have hwj_W : y j + a ∈ W := by
            rw [hW_mem]
            have hsum := W₀.add_mem (horthoU_le_W₀ hwj_ortho) ((hW_mem w₀).mp hw₀W)
            rwa [vec_add_cancel_right] at hsum
          let B : Finset (Fin r → ZMod 2) := {a + (y j + a), a + (y j + a) + δ}
          have hB_mem : B ∈ bins := Finset.mem_image_of_mem _ hwj_W
          have hB_sub : B ⊆ cOf w₀ := by
            intro z hz
            rw [hcOf_mem]
            simp only [B, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · have heq : a + (y j + a) + a + w₀ = y j + a + w₀ := by
                rw [add_comm (y j) a, vec_add_cancel_left, add_comm a (y j)]
              rw [heq]
              exact hwj_ortho
            · have heq : a + (y j + a) + δ + a + w₀ = (y j + a + w₀) + δ := by
                funext k
                simp only [Pi.add_apply]
                have : a k + (y j k + a k) + δ k + a k + w₀ k =
                    y j k + a k + w₀ k + δ k + (a k + a k) := by ring
                rw [this, zmod2_add_self, add_zero]
              rw [heq]
              exact (ortho U).add_mem hwj_ortho hδ_ortho
          refine ⟨B, ⟨hB_mem, hB_sub⟩, ?_⟩
          simp only [B, Finset.mem_insert, Finset.mem_singleton]
          left
          rw [add_comm (y j) a, vec_add_cancel_left]
        · rintro ⟨B, ⟨_, hBsub⟩, hjB⟩
          exact hBsub hjB
      rw [hcov, Finset.card_biUnion]
      intro B₁ hB₁ B₂ hB₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      exact Finset.disjoint_left.mp
        (hbin_disj B₁ (Finset.mem_filter.mp hB₁).1 B₂ (Finset.mem_filter.mp hB₂).1 hne)
        (Finset.mem_filter.mp hj₁).2 (Finset.mem_filter.mp hj₂).2
    have hK_le_bins : K.card ≤ ∑ B ∈ bins,
        min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card := by
      have h1 : K.card ≤ ∑ C ∈ coarse,
          min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ C)).card := by
        rw [hK_eq_sum]
        exact Finset.sum_le_sum hcoarse_bound
      have h2 : ∑ C ∈ coarse,
          min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ C)).card ≤
          ∑ C ∈ coarse, ∑ B ∈ bins.filter (· ⊆ C),
            min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card := by
        refine Finset.sum_le_sum (fun C hC => ?_)
        rw [hcoarse_split C hC]
        exact min_sum_le_sum_min (c * 2 ^ (r - d)) (bins.filter (· ⊆ C))
          (fun B => (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card)
      have hbins_eq : coarse.biUnion (fun C => bins.filter (· ⊆ C)) = bins := by
        ext B
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨_, _, hB, _⟩; exact hB
        · intro hB
          obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hB
          refine ⟨cOf w, Finset.mem_image_of_mem cOf hwW, hB, ?_⟩
          intro z hz
          rw [hcOf_mem]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · have heq : a + w + a + w = 0 := by rw [add_assoc (a + w), vec_add_self]
            rw [heq]
            exact (ortho U).zero_mem
          · have heq : a + w + δ + a + w = δ := by
              funext k
              simp only [Pi.add_apply]
              have : a k + w k + δ k + a k + w k = δ k + ((a k + a k) + (w k + w k)) := by ring
              rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
            rw [heq]
            exact hδ_ortho
      have hdisj_f : (↑coarse : Set (Finset (Fin r → ZMod 2))).PairwiseDisjoint
          (fun C => bins.filter (· ⊆ C)) := by
        intro C₁ hC₁ C₂ hC₂ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro B hB₁ hB₂
        obtain ⟨hB, hsub₁⟩ := Finset.mem_filter.mp hB₁
        obtain ⟨_, hsub₂⟩ := Finset.mem_filter.mp hB₂
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hB
        have hmem : a + w ∈ ({a + w, a + w + δ} : Finset (Fin r → ZMod 2)) :=
          Finset.mem_insert_self _ _
        exact Finset.disjoint_left.mp (hcOf_disj C₁ hC₁ C₂ hC₂ hne) (hsub₁ hmem) (hsub₂ hmem)
      have h3 : ∑ C ∈ coarse, ∑ B ∈ bins.filter (· ⊆ C),
          min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card =
          ∑ B ∈ bins,
            min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card := by
        rw [← Finset.sum_biUnion hdisj_f, hbins_eq]
      exact le_trans h1 (le_trans h2 (le_of_eq h3))
    have hfinal : ∑ B ∈ bins,
        min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card =
        ∑ B ∈ W.image (fun w => ({a + w, a + w + δ} : Finset (Fin r → ZMod 2))),
          min (c * 2 ^ (r - d)) (Finset.univ.filter (fun j : Fin (c * 2 ^ r) => y j ∈ B)).card := by
      refine Finset.sum_congr rfl (fun B _ => ?_)
      congr 2
    rw [← hfinal]
    omega

lemma backward_dir {r c t : ℕ}
    (x y : Fin (c * 2 ^ r) → Fin r → ZMod 2)
    (hx : ∀ v : Fin r → ZMod 2,
      (Finset.univ.filter (fun i : Fin (c * 2 ^ r) => x i = v)).card = c)
    (d : ℕ) (W : Finset (Fin r → ZMod 2)) (a δ : Fin r → ZMod 2)
    (hd : d ≤ r) (hWcard : W.card = 2 ^ d) (hW0 : 0 ∈ W)
    (hWadd : ∀ v ∈ W, ∀ w ∈ W, v + w ∈ W) (hδW : δ ∈ W) (hδEven : δ = 0 ↔ Even d)
    (hn : c * 2 ^ r ≤ t + ∑ bin ∈ W.image (fun w => ({a + w, a + w + δ} : Finset (Fin r → ZMod 2))),
      min (c * 2 ^ (r - d)) (Finset.univ.filter (fun i : Fin (c * 2 ^ r) => y i ∈ bin)).card) :
    ∃ (π : Equiv.Perm (Fin (c * 2 ^ r))) (K : Finset (Fin (c * 2 ^ r))),
      c * 2 ^ r ≤ K.card + t ∧
      ∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0 := by
  classical
  let W₀ : Submodule (ZMod 2) (Fin r → ZMod 2) :=
    Submodule.mk ⟨⟨(W : Set (Fin r → ZMod 2)), fun {u₁ u₂} hu₁ hu₂ => hWadd u₁ hu₁ u₂ hu₂⟩, hW0⟩
      (fun s {u} hu => by
        rcases zmod2_cases s with rfl | rfl
        · rw [zero_smul]; exact hW0
        · rw [one_smul]; exact hu)
  have hW₀_rank : Module.finrank (ZMod 2) W₀ = d := by
    have hcard : Fintype.card W₀ = W.card := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun (w : W₀) _ => w.1) ?_ ?_ ?_
      · intro w _; exact w.2
      · intro w₁ _ w₂ _ h; exact Subtype.ext h
      · intro w hw; exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
    have hpow : 2 ^ Module.finrank (ZMod 2) W₀ = 2 ^ d := by
      rw [← card_submodule W₀, hcard, hWcard]
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
  let B₀ : Submodule (ZMod 2) (Fin r → ZMod 2) := Submodule.span (ZMod 2) {δ}
  have hB₀_mem : ∀ v, v ∈ B₀ ↔ v = 0 ∨ v = δ := by
    intro v
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨s, rfl⟩
      fin_cases s
      · left; exact zero_smul _ _
      · right; exact one_smul _ _
    · rintro (rfl | rfl)
      · exact ⟨0, zero_smul _ _⟩
      · exact ⟨1, one_smul _ _⟩
  have hB₀_le : B₀ ≤ W₀ := by
    intro v hv
    rcases (hB₀_mem v).mp hv with rfl | rfl
    · exact W₀.zero_mem
    · exact hδW
  have hEven_d_sub_B₀ : Even (d - Module.finrank (ZMod 2) B₀) ∧ Module.finrank (ZMod 2) B₀ ≤ d := by
    by_cases hδ0 : δ = 0
    · have hBbot : B₀ = ⊥ := by
        ext v
        rw [hB₀_mem, hδ0, Submodule.mem_bot, or_self]
      have hBrank : Module.finrank (ZMod 2) B₀ = 0 := by
        rw [hBbot]; exact finrank_bot (ZMod 2) (Fin r → ZMod 2)
      rw [hBrank, Nat.sub_zero]
      exact ⟨hδEven.mp hδ0, Nat.zero_le d⟩
    · have hBcard : Fintype.card B₀ = 2 ^ 1 := by
        have h1 : Fintype.card B₀ = ({(0 : Fin r → ZMod 2), δ} : Finset (Fin r → ZMod 2)).card := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun (v : B₀) _ => v.1) ?_ ?_ ?_
          · intro v _
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact (hB₀_mem v.1).mp v.2
          · intro v₁ _ v₂ _ h; exact Subtype.ext h
          · intro v hv
            have hvB : v ∈ B₀ := by
              rw [hB₀_mem]
              simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
            exact ⟨⟨v, hvB⟩, Finset.mem_univ _, rfl⟩
        rw [h1, Finset.card_pair (Ne.symm hδ0), pow_one]
      have hBrank : Module.finrank (ZMod 2) B₀ = 1 := by
        have hpow : 2 ^ Module.finrank (ZMod 2) B₀ = 2 ^ 1 := by
          rw [← card_submodule B₀, hBcard]
        exact Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
      have hOdd : ¬ Even d := fun he => hδ0 (hδEven.mpr he)
      have hd_pos : 1 ≤ d := by
        by_contra h0
        have hd0 : d = 0 := by omega
        subst hd0
        exact hOdd ⟨0, rfl⟩
      rw [hBrank]
      refine ⟨?_, hd_pos⟩
      rw [Nat.even_iff] at hOdd ⊢
      omega
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl (B₀.comap W₀.subtype)
  let Q : Submodule (ZMod 2) (Fin r → ZMod 2) := Q'.map W₀.subtype
  have hQ_le : Q ≤ W₀ := by
    rintro v ⟨⟨w, hw⟩, _, rfl⟩
    exact hw
  have hBQ_sup : B₀ ⊔ Q = W₀ := by
    apply le_antisymm (sup_le hB₀_le hQ_le)
    intro w hw
    have hmem : (⟨w, hw⟩ : W₀) ∈ (B₀.comap W₀.subtype) ⊔ Q' := by
      rw [hQ'.sup_eq_top]
      trivial
    obtain ⟨⟨b, hbW⟩, hb, ⟨q, hqW⟩, hq, hsum⟩ := Submodule.mem_sup.mp hmem
    have hweq : b + q = w := congrArg Subtype.val hsum
    rw [← hweq]
    exact Submodule.add_mem_sup hb ⟨⟨q, hqW⟩, hq, rfl⟩
  have hBQ_inf : B₀ ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvB, ⟨⟨q, hqW⟩, hqQ', rfl⟩⟩
    have hmem : (⟨q, hqW⟩ : W₀) ∈ (B₀.comap W₀.subtype) ⊓ Q' := ⟨hvB, hqQ'⟩
    rw [hQ'.inf_eq_bot, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hQ_rank : Module.finrank (ZMod 2) Q = d - Module.finrank (ZMod 2) B₀ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq B₀ Q
    rw [hBQ_sup, hBQ_inf, hW₀_rank, finrank_bot (ZMod 2) (Fin r → ZMod 2), add_zero] at h1
    omega
  obtain ⟨e, he⟩ := hEven_d_sub_B₀.1
  have hQ_rank_e : Module.finrank (ZMod 2) Q = e + e := by rw [hQ_rank, he]
  obtain ⟨Z, hWZ⟩ := Submodule.exists_isCompl W₀
  have hQ_compl : IsCompl Q (B₀ ⊔ Z) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro q ⟨hqQ, hqBZ⟩
      obtain ⟨b, hb, z, hz, hbz⟩ := Submodule.mem_sup.mp hqBZ
      have hzW : z ∈ W₀ := by
        have h1 : q + b = z := by
          rw [← hbz, add_comm b z, vec_add_cancel_right]
        rw [← h1]
        exact W₀.add_mem (hQ_le hqQ) (hB₀_le hb)
      have hz0 : z = 0 := by
        have : z ∈ W₀ ⊓ Z := ⟨hzW, hz⟩
        rwa [hWZ.inf_eq_bot, Submodule.mem_bot] at this
      subst hz0
      rw [add_zero] at hbz
      subst hbz
      have : b ∈ B₀ ⊓ Q := ⟨hb, hqQ⟩
      rwa [hBQ_inf, Submodule.mem_bot] at this
    · rw [codisjoint_iff]
      calc Q ⊔ (B₀ ⊔ Z) = (B₀ ⊔ Q) ⊔ Z := by rw [sup_comm Q (B₀ ⊔ Z), sup_assoc, sup_comm Z Q,
            ← sup_assoc]
        _ = W₀ ⊔ Z := by rw [hBQ_sup]
        _ = ⊤ := hWZ.sup_eq_top
  let BZ : Submodule (ZMod 2) (Fin r → ZMod 2) := B₀ ⊔ Z
  have hQ_compl' : IsCompl Q BZ := hQ_compl
  let eIdx : Fin (Module.finrank (ZMod 2) Q) ≃ Fin e ⊕ Fin e :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, hQ_rank_e])
  let bQ : Module.Basis (Fin e ⊕ Fin e) (ZMod 2) Q := (Module.finBasis (ZMod 2) Q).reindex eIdx
  let projQ : (Fin r → ZMod 2) →ₗ[ZMod 2] Q :=
    (LinearMap.fst (ZMod 2) Q BZ).comp
      (Submodule.prodEquivOfIsCompl Q BZ hQ_compl').symm.toLinearMap
  have hprojQ_Q : ∀ q : Q, projQ q.1 = q := by
    intro q
    have h1 : Submodule.prodEquivOfIsCompl Q BZ hQ_compl' (q, (0 : BZ)) = q.1 := by
      change q.1 + 0 = q.1
      rw [add_zero]
    have h2 : (Submodule.prodEquivOfIsCompl Q BZ hQ_compl').symm q.1 = (q, (0 : BZ)) := by
      rw [LinearEquiv.symm_apply_eq, h1]
    change (LinearMap.fst (ZMod 2) Q BZ)
      ((Submodule.prodEquivOfIsCompl Q BZ hQ_compl').symm q.1) = q
    rw [h2, LinearMap.fst_apply]
  have hprojQ_B₀ : ∀ b ∈ B₀, projQ b = 0 := by
    intro b hb
    have hb' : b ∈ BZ := Submodule.mem_sup_left hb
    have h1 : Submodule.prodEquivOfIsCompl Q BZ hQ_compl' ((0 : Q), ⟨b, hb'⟩) = b := by
      change 0 + b = b
      rw [zero_add]
    have h2 : (Submodule.prodEquivOfIsCompl Q BZ hQ_compl').symm b = ((0 : Q), ⟨b, hb'⟩) := by
      rw [LinearEquiv.symm_apply_eq, h1]
    change (LinearMap.fst (ZMod 2) Q BZ)
      ((Submodule.prodEquivOfIsCompl Q BZ hQ_compl').symm b) = 0
    rw [h2, LinearMap.fst_apply]
  have hex_dual : ∀ idx : Fin e ⊕ Fin e,
      ∃ u : Fin r → ZMod 2, ∀ v : Fin r → ZMod 2, dotProduct u v = bQ.coord idx (projQ v) :=
    fun idx => exists_dot_eq_linearMap ((bQ.coord idx).comp projQ)
  let uDual : (Fin e ⊕ Fin e) → (Fin r → ZMod 2) := fun idx => Classical.choose (hex_dual idx)
  have huDual : ∀ idx v, dotProduct (uDual idx) v = bQ.coord idx (projQ v) :=
    fun idx => Classical.choose_spec (hex_dual idx)
  let ψ : Q →ₗ[ZMod 2] (Fin r → ZMod 2) := bQ.constr (ZMod 2) (fun idx => uDual (Sum.swap idx))
  have hψ_apply : ∀ q : Q, ψ q = ∑ idx : Fin e ⊕ Fin e, bQ.repr q idx • uDual (Sum.swap idx) := by
    intro q
    conv_lhs => rw [← bQ.sum_repr q]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    rw [map_smul, Module.Basis.constr_basis]
  have hψ_B₀ : ∀ q : Q, ∀ b ∈ B₀, dotProduct (ψ q) b = 0 := by
    intro q b hb
    rw [hψ_apply q, sum_dot]
    refine Finset.sum_eq_zero (fun idx _ => ?_)
    rw [smul_dotProduct, huDual, hprojQ_B₀ b hb, map_zero, smul_zero]
  have hψ_self : ∀ q : Q, dotProduct (ψ q) q.1 = 0 := by
    intro q
    rw [hψ_apply q, sum_dot]
    have hterm : ∀ idx : Fin e ⊕ Fin e,
        dotProduct (bQ.repr q idx • uDual (Sum.swap idx)) q.1 =
          bQ.repr q idx * bQ.repr q (Sum.swap idx) := by
      intro idx
      rw [smul_dotProduct, huDual, hprojQ_Q q, smul_eq_mul, Module.Basis.coord_apply]
    simp_rw [hterm]
    rw [Fintype.sum_sum_type]
    simp only [Sum.swap_inl, Sum.swap_inr]
    have hcomm : (∑ k : Fin e, bQ.repr q (Sum.inr k) * bQ.repr q (Sum.inl k)) =
        ∑ k : Fin e, bQ.repr q (Sum.inl k) * bQ.repr q (Sum.inr k) :=
      Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [hcomm, zmod2_add_self]
  have hψ_inj_mod : ∀ q₁ q₂ : Q, ψ q₁ + ψ q₂ ∈ ortho W₀ → q₁ = q₂ := by
    intro q₁ q₂ hmem
    have hmem' : ψ (q₁ + q₂) ∈ ortho W₀ := by rwa [map_add]
    have hzero : q₁ + q₂ = 0 := by
      apply bQ.repr.injective
      rw [map_zero]
      ext idx
      rw [Finsupp.zero_apply]
      have hdot0 : dotProduct (ψ (q₁ + q₂)) (bQ (Sum.swap idx)).1 = 0 := by
        rw [dot_comm]
        exact mem_ortho.mp hmem' (bQ (Sum.swap idx)).1 (hQ_le (bQ (Sum.swap idx)).2)
      rw [hψ_apply (q₁ + q₂), sum_dot] at hdot0
      have hterm : ∀ j : Fin e ⊕ Fin e,
          dotProduct (bQ.repr (q₁ + q₂) j • uDual (Sum.swap j)) (bQ (Sum.swap idx)).1 =
            if j = idx then bQ.repr (q₁ + q₂) j else 0 := by
        intro j
        rw [smul_dotProduct, huDual, hprojQ_Q (bQ (Sum.swap idx)), smul_eq_mul,
          Module.Basis.coord_apply, Module.Basis.repr_self]
        by_cases hj : j = idx
        · subst hj
          simp only [↓reduceIte, Finsupp.single_eq_same, mul_one]
        · have hne : Sum.swap idx ≠ Sum.swap j := by
            intro h
            have h' := congrArg Sum.swap h
            simp only [Sum.swap_swap] at h'
            exact hj h'.symm
          simp only [hj, ↓reduceIte, Finsupp.single_apply, hne, mul_zero]
      simp_rw [hterm] at hdot0
      rw [Finset.sum_ite_eq'] at hdot0
      simp only [Finset.mem_univ, ↓reduceIte] at hdot0
      exact hdot0
    have hsub : q₁.1 + q₂.1 = 0 := congrArg Subtype.val hzero
    exact Subtype.ext (by
      have h1 : q₁.1 + q₂.1 + q₂.1 = 0 + q₂.1 := congrArg (· + q₂.1) hsub
      rwa [vec_add_cancel_right, zero_add] at h1)
  let rowSet : Q → Finset (Fin (c * 2 ^ r)) := fun q =>
    Finset.univ.filter (fun i => x i + ψ q ∈ ortho W₀)
  let binOf : Q → Finset (Fin r → ZMod 2) := fun q => ({a + q.1, a + q.1 + δ} : Finset (Fin r → ZMod 2))
  let colSet : Q → Finset (Fin (c * 2 ^ r)) := fun q =>
    Finset.univ.filter (fun j => y j ∈ binOf q)
  have hrow_card : ∀ q : Q, (rowSet q).card = c * 2 ^ (r - d) := by
    intro q
    have h1 := card_filter_coset_eq x hx (ortho W₀) (ψ q)
    have h2 : Module.finrank (ZMod 2) (ortho W₀) = r - d := by
      have h3 := finrank_add_finrank_ortho W₀
      rw [hW₀_rank] at h3
      omega
    rw [h2] at h1
    exact h1
  have hrow_disj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint rowSet := by
    intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have h1 := (Finset.mem_filter.mp hi₁).2
    have h2 := (Finset.mem_filter.mp hi₂).2
    have hsum := (ortho W₀).add_mem h1 h2
    have heq : x i + ψ q₁ + (x i + ψ q₂) = ψ q₁ + ψ q₂ := by
      funext k
      simp only [Pi.add_apply]
      have : x i k + ψ q₁ k + (x i k + ψ q₂ k) = ψ q₁ k + ψ q₂ k + (x i k + x i k) := by ring
      rw [this, zmod2_add_self, add_zero]
    rw [heq] at hsum
    exact hne (hψ_inj_mod q₁ q₂ hsum)
  have hbinOf_inj : Function.Injective binOf := by
    intro q₁ q₂ heq
    have hmem : a + q₁.1 ∈ binOf q₂ := by
      rw [← heq]
      exact Finset.mem_insert_self _ _
    simp only [binOf, Finset.mem_insert, Finset.mem_singleton] at hmem
    have hdiffB : q₁.1 + q₂.1 ∈ B₀ := by
      rw [hB₀_mem]
      rcases hmem with h | h
      · left
        have hq : q₁.1 = q₂.1 := add_left_cancel h
        rw [hq, vec_add_self]
      · right
        have hq : q₁.1 = q₂.1 + δ := add_left_cancel (by rwa [add_assoc] at h)
        rw [hq, add_comm q₂.1 δ, vec_add_cancel_right]
    have hdiffQ : q₁.1 + q₂.1 ∈ Q := Q.add_mem q₁.2 q₂.2
    have h0 : q₁.1 + q₂.1 = 0 := by
      have : q₁.1 + q₂.1 ∈ B₀ ⊓ Q := ⟨hdiffB, hdiffQ⟩
      rwa [hBQ_inf, Submodule.mem_bot] at this
    exact Subtype.ext (by
      have h1 : q₁.1 + q₂.1 + q₂.1 = 0 + q₂.1 := congrArg (· + q₂.1) h0
      rwa [vec_add_cancel_right, zero_add] at h1)
  have hbinOf_disj : ∀ q₁ q₂ : Q, q₁ ≠ q₂ → Disjoint (binOf q₁) (binOf q₂) := by
    intro q₁ q₂ hne
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    apply hne
    apply hbinOf_inj
    simp only [binOf, Finset.mem_insert, Finset.mem_singleton] at hz₁ hz₂
    rcases hz₁ with rfl | rfl <;> rcases hz₂ with h | h
    · simp only [binOf, h]
    · simp only [binOf, h, add_assoc (a + q₂.1), vec_add_self, add_zero, Finset.pair_comm]
    · simp only [binOf, ← h, add_assoc (a + q₁.1), vec_add_self, add_zero, Finset.pair_comm]
    · have h' : a + q₁.1 = a + q₂.1 := add_right_cancel h
      simp only [binOf, h']
  have hcol_disj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint colSet := by
    intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    exact Finset.disjoint_left.mp (hbinOf_disj q₁ q₂ hne)
      (Finset.mem_filter.mp hj₁).2 (Finset.mem_filter.mp hj₂).2
  have hbins_image : W.image (fun w => ({a + w, a + w + δ} : Finset (Fin r → ZMod 2))) =
      Finset.univ.image binOf := by
    ext B
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hwW, rfl⟩
      have hw : w ∈ B₀ ⊔ Q := by rw [hBQ_sup]; exact hwW
      obtain ⟨b, hb, q, hq, hbq⟩ := Submodule.mem_sup.mp hw
      refine ⟨⟨q, hq⟩, ?_⟩
      rcases (hB₀_mem b).mp hb with hb0 | hbδ
      · rw [hb0, zero_add] at hbq; rw [← hbq]
      · rw [hbδ] at hbq
        rw [← hbq, add_comm δ q, ← add_assoc, add_assoc (a + q), vec_add_self, add_zero,
          Finset.pair_comm]
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, hQ_le q.2, rfl⟩
  let m : Q → ℕ := fun q => min (rowSet q).card (colSet q).card
  have hex_R' : ∀ q : Q, ∃ s ⊆ rowSet q, s.card = m q :=
    fun q => Finset.exists_subset_card_eq (min_le_left _ _)
  have hex_Y' : ∀ q : Q, ∃ s ⊆ colSet q, s.card = m q :=
    fun q => Finset.exists_subset_card_eq (min_le_right _ _)
  let R' : Q → Finset (Fin (c * 2 ^ r)) := fun q => Classical.choose (hex_R' q)
  let Y' : Q → Finset (Fin (c * 2 ^ r)) := fun q => Classical.choose (hex_Y' q)
  have hR'_sub : ∀ q, R' q ⊆ rowSet q := fun q => (Classical.choose_spec (hex_R' q)).1
  have hR'_card : ∀ q, (R' q).card = m q := fun q => (Classical.choose_spec (hex_R' q)).2
  have hY'_sub : ∀ q, Y' q ⊆ colSet q := fun q => (Classical.choose_spec (hex_Y' q)).1
  have hY'_card : ∀ q, (Y' q).card = m q := fun q => (Classical.choose_spec (hex_Y' q)).2
  have hR'_disj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint R' :=
    fun q₁ h₁ q₂ h₂ hne => Disjoint.mono (hR'_sub q₁) (hR'_sub q₂) (hrow_disj h₁ h₂ hne)
  have hY'_disj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint Y' :=
    fun q₁ h₁ q₂ h₂ hne => Disjoint.mono (hY'_sub q₁) (hY'_sub q₂) (hcol_disj h₁ h₂ hne)
  let K : Finset (Fin (c * 2 ^ r)) := Finset.univ.biUnion R'
  let Ytot : Finset (Fin (c * 2 ^ r)) := Finset.univ.biUnion Y'
  have hK_card : K.card = ∑ q : Q, m q := by
    rw [Finset.card_biUnion hR'_disj]
    exact Finset.sum_congr rfl (fun q _ => hR'_card q)
  have hYtot_card : Ytot.card = ∑ q : Q, m q := by
    rw [Finset.card_biUnion hY'_disj]
    exact Finset.sum_congr rfl (fun q _ => hY'_card q)
  let eqQ : ∀ q : Q, { i // i ∈ R' q } ≃ { j // j ∈ Y' q } := fun q =>
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hR'_card q, hY'_card q])
  have hR'_uniq : ∀ {i q₁ q₂}, i ∈ R' q₁ → i ∈ R' q₂ → q₁ = q₂ := by
    intro i q₁ q₂ h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (hR'_disj (Finset.mem_univ q₁) (Finset.mem_univ q₂) hne) h1 h2
  have hY'_uniq : ∀ {j q₁ q₂}, j ∈ Y' q₁ → j ∈ Y' q₂ → q₁ = q₂ := by
    intro j q₁ q₂ h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (hY'_disj (Finset.mem_univ q₁) (Finset.mem_univ q₂) hne) h1 h2
  let qOfR : { i // i ∈ K } → Q := fun ⟨i, hi⟩ =>
    Classical.choose (Finset.mem_biUnion.mp hi)
  have hqOfR_mem : ∀ x₁ : { i // i ∈ K }, x₁.1 ∈ R' (qOfR x₁) := fun ⟨i, hi⟩ =>
    (Classical.choose_spec (Finset.mem_biUnion.mp hi)).2
  let qOfY : { j // j ∈ Ytot } → Q := fun ⟨j, hj⟩ =>
    Classical.choose (Finset.mem_biUnion.mp hj)
  have hqOfY_mem : ∀ y₁ : { j // j ∈ Ytot }, y₁.1 ∈ Y' (qOfY y₁) := fun ⟨j, hj⟩ =>
    (Classical.choose_spec (Finset.mem_biUnion.mp hj)).2
  let eK : { i // i ∈ K } ≃ { j // j ∈ Ytot } :=
    { toFun := fun x₁ =>
        ⟨(eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩).1,
          Finset.mem_biUnion.mpr ⟨qOfR x₁, Finset.mem_univ _, (eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩).2⟩⟩
      invFun := fun y₁ =>
        ⟨((eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩).1,
          Finset.mem_biUnion.mpr ⟨qOfY y₁, Finset.mem_univ _, ((eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩).2⟩⟩
      left_inv := fun x₁ => by
        apply Subtype.ext
        let y₁ : { j // j ∈ Ytot } :=
          ⟨(eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩).1,
            Finset.mem_biUnion.mpr ⟨qOfR x₁, Finset.mem_univ _, (eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩).2⟩⟩
        have hq : qOfY y₁ = qOfR x₁ :=
          hY'_uniq (hqOfY_mem y₁) (eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩).2
        change ((eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩).1 = x₁.1
        have hcast : ∀ (q : Q) (hqeq : q = qOfR x₁) (hmem : y₁.1 ∈ Y' q),
            ((eqQ q).symm ⟨y₁.1, hmem⟩).1 = x₁.1 := by
          rintro _ rfl hmem
          have hsub : (⟨y₁.1, hmem⟩ : { j // j ∈ Y' (qOfR x₁) }) =
              eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩ := Subtype.ext rfl
          rw [hsub, Equiv.symm_apply_apply]
        exact hcast (qOfY y₁) hq (hqOfY_mem y₁)
      right_inv := fun y₁ => by
        apply Subtype.ext
        let x₁ : { i // i ∈ K } :=
          ⟨((eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩).1,
            Finset.mem_biUnion.mpr ⟨qOfY y₁, Finset.mem_univ _, ((eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩).2⟩⟩
        have hq : qOfR x₁ = qOfY y₁ :=
          hR'_uniq (hqOfR_mem x₁) ((eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩).2
        change (eqQ (qOfR x₁) ⟨x₁.1, hqOfR_mem x₁⟩).1 = y₁.1
        have hcast : ∀ (q : Q) (hqeq : q = qOfY y₁) (hmem : x₁.1 ∈ R' q),
            (eqQ q ⟨x₁.1, hmem⟩).1 = y₁.1 := by
          rintro _ rfl hmem
          have hsub : (⟨x₁.1, hmem⟩ : { i // i ∈ R' (qOfY y₁) }) =
              (eqQ (qOfY y₁)).symm ⟨y₁.1, hqOfY_mem y₁⟩ := Subtype.ext rfl
          rw [hsub, Equiv.apply_symm_apply]
        exact hcast (qOfR x₁) hq (hqOfR_mem x₁) }
  let eKc : { i : Fin (c * 2 ^ r) // ¬ i ∈ K } ≃ { j : Fin (c * 2 ^ r) // ¬ j ∈ Ytot } :=
    Fintype.equivOfCardEq (by
      have h1 : Fintype.card { i : Fin (c * 2 ^ r) // ¬ i ∈ K } = Kᶜ.card := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun (i : { i : Fin (c * 2 ^ r) // ¬ i ∈ K }) _ => i.1) ?_ ?_ ?_
        · intro i _; exact Finset.mem_compl.mpr i.2
        · intro i₁ _ i₂ _ h; exact Subtype.ext h
        · intro i hi; exact ⟨⟨i, Finset.mem_compl.mp hi⟩, Finset.mem_univ _, rfl⟩
      have h2 : Fintype.card { j : Fin (c * 2 ^ r) // ¬ j ∈ Ytot } = Ytotᶜ.card := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun (j : { j : Fin (c * 2 ^ r) // ¬ j ∈ Ytot }) _ => j.1) ?_ ?_ ?_
        · intro j _; exact Finset.mem_compl.mpr j.2
        · intro j₁ _ j₂ _ h; exact Subtype.ext h
        · intro j hj; exact ⟨⟨j, Finset.mem_compl.mp hj⟩, Finset.mem_univ _, rfl⟩
      rw [h1, h2, Finset.card_compl, Finset.card_compl, hK_card, hYtot_card])
  let π : Equiv.Perm (Fin (c * 2 ^ r)) :=
    (Equiv.sumCompl (· ∈ K)).symm.trans ((Equiv.sumCongr eK eKc).trans (Equiv.sumCompl (· ∈ Ytot)))
  have hπ_K : ∀ i (hi : i ∈ K), π i = (eK ⟨i, hi⟩).1 := by
    intro i hi
    simp only [π, Equiv.trans_apply]
    have hsymm : (Equiv.sumCompl (· ∈ K)).symm i = Sum.inl ⟨i, hi⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    rw [hsymm, Equiv.sumCongr_apply, Sum.map_inl]
    rfl
  refine ⟨π, K, ?_, ?_⟩
  · have hsum_eq :
        ∑ bin ∈ W.image (fun w => ({a + w, a + w + δ} : Finset (Fin r → ZMod 2))),
          min (c * 2 ^ (r - d)) (Finset.univ.filter (fun i : Fin (c * 2 ^ r) => y i ∈ bin)).card =
        ∑ q : Q, m q := by
      rw [hbins_image, Finset.sum_image (fun q₁ _ q₂ _ h => hbinOf_inj h)]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [m, hrow_card q]
      congr 2
    rw [hK_card, ← hsum_eq]
    omega
  · intro i hi j hj
    let q₁ := qOfR ⟨i, hi⟩
    let q₂ := qOfR ⟨j, hj⟩
    have hi_row : i ∈ rowSet q₁ := hR'_sub q₁ (hqOfR_mem ⟨i, hi⟩)
    have hj_row : j ∈ rowSet q₂ := hR'_sub q₂ (hqOfR_mem ⟨j, hj⟩)
    have hi_col : π i ∈ colSet q₁ := by
      rw [hπ_K i hi]
      exact hY'_sub q₁ (eqQ q₁ ⟨i, hqOfR_mem ⟨i, hi⟩⟩).2
    have hj_col : π j ∈ colSet q₂ := by
      rw [hπ_K j hj]
      exact hY'_sub q₂ (eqQ q₂ ⟨j, hqOfR_mem ⟨j, hj⟩⟩).2
    have hw₁ : x i + ψ q₁ ∈ ortho W₀ := (Finset.mem_filter.mp hi_row).2
    have hw₂ : x j + ψ q₂ ∈ ortho W₀ := (Finset.mem_filter.mp hj_row).2
    have hy₁_mem : y (π i) ∈ binOf q₁ := (Finset.mem_filter.mp hi_col).2
    have hy₂_mem : y (π j) ∈ binOf q₂ := (Finset.mem_filter.mp hj_col).2
    have hb₁ : y (π i) + a + q₁.1 ∈ B₀ := by
      rw [hB₀_mem]
      simp only [binOf, Finset.mem_insert, Finset.mem_singleton] at hy₁_mem
      rcases hy₁_mem with h | h
      · left; rw [h, add_assoc (a + q₁.1), vec_add_self]
      · right
        rw [h]
        funext k
        simp only [Pi.add_apply]
        have : a k + q₁.1 k + δ k + a k + q₁.1 k = δ k + ((a k + a k) + (q₁.1 k + q₁.1 k)) := by ring
        rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
    have hb₂ : y (π j) + a + q₂.1 ∈ B₀ := by
      rw [hB₀_mem]
      simp only [binOf, Finset.mem_insert, Finset.mem_singleton] at hy₂_mem
      rcases hy₂_mem with h | h
      · left; rw [h, add_assoc (a + q₂.1), vec_add_self]
      · right
        rw [h]
        funext k
        simp only [Pi.add_apply]
        have : a k + q₂.1 k + δ k + a k + q₂.1 k = δ k + ((a k + a k) + (q₂.1 k + q₂.1 k)) := by ring
        rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
    let wdiff : Fin r → ZMod 2 := (x i + ψ q₁) + (x j + ψ q₂)
    have hwdiff : wdiff ∈ ortho W₀ := (ortho W₀).add_mem hw₁ hw₂
    let bdiff : Fin r → ZMod 2 := (y (π i) + a + q₁.1) + (y (π j) + a + q₂.1)
    have hbdiff : bdiff ∈ B₀ := B₀.add_mem hb₁ hb₂
    have hx_eq : x i - x j = ψ (q₁ + q₂) + wdiff := by
      rw [vec_sub_eq_add, map_add]
      funext k
      simp only [wdiff, Pi.add_apply]
      have : ψ q₁ k + ψ q₂ k + (x i k + ψ q₁ k + (x j k + ψ q₂ k)) =
          x i k + x j k + ((ψ q₁ k + ψ q₁ k) + (ψ q₂ k + ψ q₂ k)) := by ring
      rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
    have hy_eq : y (π i) - y (π j) = (q₁ + q₂).1 + bdiff := by
      rw [vec_sub_eq_add]
      funext k
      simp only [bdiff, Submodule.coe_add, Pi.add_apply]
      have : q₁.1 k + q₂.1 k + (y (π i) k + a k + q₁.1 k + (y (π j) k + a k + q₂.1 k)) =
          y (π i) k + y (π j) k + ((a k + a k) + (q₁.1 k + q₁.1 k) + (q₂.1 k + q₂.1 k)) := by ring
      simp only [this, zmod2_add_self, add_zero]
    have hy_W₀ : (q₁ + q₂).1 + bdiff ∈ W₀ := W₀.add_mem (hQ_le (q₁ + q₂).2) (hB₀_le hbdiff)
    rw [hx_eq, hy_eq, add_dotProduct, dotProduct_add,
      hψ_self (q₁ + q₂), hψ_B₀ (q₁ + q₂) bdiff hbdiff,
      dot_comm wdiff _, mem_ortho.mp hwdiff _ hy_W₀, add_zero, add_zero]

end PEqualNP.Outside.L_meta_25747

theorem PEqualNP.Outside.L_meta_25747 : ∀ (r c t : ℕ),
  let V := Fin r → ZMod 2
  let n := c * 2^r
  ∀ (x y : Fin n → V),
    (∀ v : V, (Finset.univ.filter (fun i : Fin n => x i = v)).card = c) →
    ((∃ (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)), n ≤ K.card + t ∧
      ∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0) ↔
    ∃ (d : ℕ) (W : Finset V) (a δ : V),
      d ≤ r ∧ W.card = 2^d ∧ 0 ∈ W ∧ (∀ v ∈ W, ∀ w ∈ W, v+w ∈ W) ∧
      δ ∈ W ∧ (δ = 0 ↔ Even d) ∧
      let bins := W.image (fun w => ({a+w, a+w+δ} : Finset V))
      n ≤ t + ∑ bin ∈ bins,
        min (c * 2^(r-d)) (Finset.univ.filter (fun i : Fin n => y i ∈ bin)).card) := by
  intro r c t V n x y hx
  constructor
  · rintro ⟨π, K, hKt, hK⟩
    exact PEqualNP.Outside.L_meta_25747.forward_dir x y hx π K hKt hK
  · rintro ⟨d, W, a, δ, hd, hWcard, hW0, hWadd, hδW, hδEven, hn⟩
    exact PEqualNP.Outside.L_meta_25747.backward_dir x y hx d W a δ hd hWcard hW0 hWadd hδW hδEven hn
