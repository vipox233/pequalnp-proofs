import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_456_aux

private abbrev Idx {n : ℕ} (v : Fin n → ℕ) := Σ j : Fin n, Fin (v j)

private def Balanced {n : ℕ} (v : Fin n → ℕ) : Finset (Idx v → Fin n) :=
  Finset.univ.filter (fun f =>
    ∀ k : Fin n, (Finset.univ.filter (fun x : Idx v => f x = k)).card = v k)

private def subVec {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ :=
  fun pos => w pos - (if pos ∈ S then 1 else 0)

private def GoodSet {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n)) : Prop :=
  (∀ j ∈ S, g j ∈ S) ∧ (∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b)

private instance {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n)) :
    Decidable (GoodSet g S) := by
  unfold GoodSet
  infer_instance

private lemma sigma_mk_cast {α : Type*} {β : α → Type*} (p : Σ a, β a) {k : α}
    (h1 : p.1 = k) :
    (⟨k, cast (congrArg β h1) p.2⟩ : Σ a, β a) = p := by
  rcases p with ⟨k', b'⟩
  dsimp only at h1 ⊢
  subst h1
  rfl

private lemma cast_sigma_snd {α : Type*} {β : α → Type*} {p : Σ a, β a} {k : α} {b : β k}
    (hp : p = ⟨k, b⟩) (h1 : p.1 = k) :
    cast (congrArg β h1) p.2 = b := by
  subst hp
  rfl

private lemma perm_fiber_card {n : ℕ} (v : Fin n → ℕ) (f : Idx v → Fin n)
    (hf : f ∈ Balanced v) :
    ((Finset.univ : Finset (Equiv.Perm (Idx v))).filter
      (fun σ => (fun x => (σ x).1) = f)).card =
      ∏ k : Fin n, Nat.factorial (v k) := by
  classical
  have hbal : ∀ k : Fin n, (Finset.univ.filter (fun x : Idx v => f x = k)).card = v k :=
    (Finset.mem_filter.mp hf).2
  have hbij :
      ((Finset.univ : Finset (Equiv.Perm (Idx v))).filter
        (fun σ => (fun x => (σ x).1) = f)).card =
      (Finset.univ : Finset (∀ k : Fin n, {x : Idx v // f x = k} ≃ Fin (v k))).card := by
    refine Finset.card_bij
      (fun σ hσ => fun k =>
        { toFun := fun ⟨x, hx⟩ =>
            have h1 : (σ x).1 = k := (congrFun (Finset.mem_filter.mp hσ).2 x).trans hx
            cast (congrArg (fun j => Fin (v j)) h1) (σ x).2
          invFun := fun b =>
            ⟨σ.symm ⟨k, b⟩, by
              have h1 := congrFun (Finset.mem_filter.mp hσ).2 (σ.symm ⟨k, b⟩)
              simpa using h1.symm⟩
          left_inv := by
            rintro ⟨x, hx⟩
            apply Subtype.ext
            dsimp only
            rw [@sigma_mk_cast (Fin n) (fun j => Fin (v j)) (σ x) k
              ((congrFun (Finset.mem_filter.mp hσ).2 x).trans hx), Equiv.symm_apply_apply]
          right_inv := by
            intro b
            dsimp only
            exact @cast_sigma_snd (Fin n) (fun j => Fin (v j)) _ k b
              (Equiv.apply_symm_apply σ ⟨k, b⟩)
              (congrArg Sigma.fst (Equiv.apply_symm_apply σ ⟨k, b⟩)) })
      ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro σ1 hσ1 σ2 hσ2 heq
      have hf1 : ∀ x, (σ1 x).1 = f x := fun x => congrFun (Finset.mem_filter.mp hσ1).2 x
      have hf2 : ∀ x, (σ2 x).1 = f x := fun x => congrFun (Finset.mem_filter.mp hσ2).2 x
      apply Equiv.ext
      intro x
      have hk := congrFun (congrArg Equiv.toFun (congrFun heq (f x))) ⟨x, rfl⟩
      dsimp only at hk
      have hp1 := sigma_mk_cast (σ1 x) (hf1 x)
      have hp2 := sigma_mk_cast (σ2 x) (hf2 x)
      rw [← hp1, ← hp2, hk]
    · intro e _
      let σ : Equiv.Perm (Idx v) :=
        { toFun := fun x => ⟨f x, e (f x) ⟨x, rfl⟩⟩
          invFun := fun y => ((e y.1).symm y.2).1
          left_inv := by
            intro x
            have := (e (f x)).symm_apply_apply ⟨x, rfl⟩
            exact congrArg Subtype.val this
          right_inv := by
            rintro ⟨k, b⟩
            dsimp only
            have hmem : f ((e k).symm b).1 = k := ((e k).symm b).2
            have hsub : ∀ (k' : Fin n) (y : {x : Idx v // f x = k'}) (hk : k' = k),
                (⟨k', e k' y⟩ : Idx v) = ⟨k, e k ⟨y.1, y.2.trans hk⟩⟩ := by
              rintro k' y rfl
              rfl
            rw [hsub (f ((e k).symm b).1) ⟨((e k).symm b).1, rfl⟩ hmem]
            exact congrArg (Sigma.mk k) ((e k).apply_symm_apply b) }
      refine ⟨σ, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        funext x
        rfl
      · funext k
        apply Equiv.ext
        rintro ⟨x, hx⟩
        dsimp [σ]
        cases hx
        rfl
  rw [hbij, Finset.card_univ, Fintype.card_pi]
  refine Finset.prod_congr rfl ?_
  intro k _
  have hcard : Fintype.card {x : Idx v // f x = k} = Fintype.card (Fin (v k)) := by
    rw [Fintype.card_subtype, hbal k, Fintype.card_fin]
  let eqv := Fintype.equivOfCardEq hcard
  have hcard_equiv : Fintype.card ({x : Idx v // f x = k} ≃ Fin (v k)) =
      Fintype.card (Equiv.Perm (Fin (v k))) :=
    Fintype.card_congr (Equiv.equivCongr eqv (Equiv.refl _))
  rw [hcard_equiv, Fintype.card_perm, Fintype.card_fin]

private lemma coeff_eq_sum_balanced {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℕ) :
    (let big : Matrix (Idx v) (Idx v) ℚ := fun copyRow copyCol => A copyRow.1 copyCol.1;
      big.permanent / (∏ i : Fin n, (Nat.factorial (v i) : ℚ))) =
    ∑ f ∈ Balanced v, ∏ x : Idx v, A (f x) x.1 := by
  classical
  dsimp only
  have hden : (∏ i : Fin n, (Nat.factorial (v i) : ℚ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (v i))
  rw [div_eq_iff hden, mul_comm]
  change (∑ σ : Equiv.Perm (Idx v), ∏ x : Idx v, A (σ x).1 x.1) = _
  have hmem : ∀ σ : Equiv.Perm (Idx v), (fun x => (σ x).1) ∈ Balanced v := by
    intro σ
    simp only [Balanced, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    have hbij : (Finset.univ.filter (fun x : Idx v => (σ x).1 = k)).card =
        (Finset.univ : Finset (Fin (v k))).card := by
      refine Finset.card_bij
        (fun x hx => cast (congrArg (fun j => Fin (v j)) (Finset.mem_filter.mp hx).2) (σ x).2)
        (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro x1 hx1 x2 hx2 heq
        have h1 : (σ x1).1 = k := (Finset.mem_filter.mp hx1).2
        have h2 : (σ x2).1 = k := (Finset.mem_filter.mp hx2).2
        apply σ.injective
        have hp1 := @sigma_mk_cast (Fin n) (fun j => Fin (v j)) (σ x1) k h1
        have hp2 := @sigma_mk_cast (Fin n) (fun j => Fin (v j)) (σ x2) k h2
        rw [← hp1, ← hp2, heq]
      · intro b _
        refine ⟨σ.symm ⟨k, b⟩, ?_, ?_⟩
        · simp
        · exact @cast_sigma_snd (Fin n) (fun j => Fin (v j)) _ k b
            (Equiv.apply_symm_apply σ ⟨k, b⟩)
            (congrArg Sigma.fst (Equiv.apply_symm_apply σ ⟨k, b⟩))
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Idx v) => fun x => (σ x).1)
    (fun σ _ => hmem σ)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro f hf
  have hconst :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Idx v) => (fun x => (σ x).1) = f),
        ∏ x : Idx v, A (σ x).1 x.1) =
      ∑ _σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Idx v) => (fun x => (σ x).1) = f),
        ∏ x : Idx v, A (f x) x.1 := by
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    have hEq := (Finset.mem_filter.mp hσ).2
    refine Finset.prod_congr rfl ?_
    intro x _
    rw [congrFun hEq x]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, perm_fiber_card v f hf]
  push_cast
  rfl

private noncomputable def permOn {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n))
    (h : GoodSet g S) : Equiv.Perm S :=
  Equiv.ofBijective (fun x : S => ⟨g x.1, h.1 x.1 x.2⟩)
    ((Finite.injective_iff_bijective).mp (fun a b heq =>
      Subtype.ext (h.2 a.1 a.2 b.1 b.2 (congrArg Subtype.val heq))))

private lemma permOn_apply_val {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n))
    (h : GoodSet g S) (x : S) : (permOn g S h x).1 = g x.1 :=
  rfl

private noncomputable def extPermOn {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n))
    (h : GoodSet g S) : Equiv.Perm (Fin n) :=
  (permOn g S h).extendDomain (Equiv.refl {j : Fin n // j ∈ S})

private lemma extPermOn_apply_mem {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n))
    (h : GoodSet g S) (j : Fin n) (hj : j ∈ S) :
    extPermOn g S h j = g j := by
  classical
  have h1 := Equiv.Perm.extendDomain_apply_image (e := permOn g S h)
    (f := Equiv.refl {j : Fin n // j ∈ S}) ⟨j, hj⟩
  exact h1

private lemma extPermOn_apply_notMem {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n))
    (h : GoodSet g S) (j : Fin n) (hj : j ∉ S) :
    extPermOn g S h j = j := by
  classical
  unfold extPermOn
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hj

private lemma sign_extPermOn {n : ℕ} (g : Fin n → Fin n) (S : Finset (Fin n))
    (h : GoodSet g S) :
    Equiv.Perm.sign (extPermOn g S h) = Equiv.Perm.sign (permOn g S h) := by
  unfold extPermOn
  exact Equiv.Perm.sign_extendDomain _ _

private lemma exists_cycle_of_maps {n : ℕ} (U : Finset (Fin n)) (hUne : U.Nonempty)
    (g : Fin n → Fin n) (hgU : ∀ j ∈ U, g j ∈ U) :
    ∃ (C : Finset (Fin n)) (_hCU : C ⊆ U) (hC : GoodSet g C),
      C.Nonempty ∧
      (∀ (S : Finset (Fin n)), (∀ j ∈ S, g j ∈ S) → Disjoint C S ∨ C ⊆ S) ∧
      (-1 : ℚ) ^ C.card * ((Equiv.Perm.sign (permOn g C hC) : ℤ) : ℚ) = -1 := by
  classical
  rcases hUne with ⟨u0, hu0⟩
  have hiterU : ∀ k : ℕ, g^[k] u0 ∈ U := by
    intro k
    induction k with
    | zero => exact hu0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hgU _ ih
  have hcard_lt : Fintype.card {x : Fin n // x ∈ U} < Fintype.card (Fin (U.card + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    omega
  rcases Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (U.card + 1) => (⟨g^[k.val] u0, hiterU k.val⟩ : {x : Fin n // x ∈ U}))
      hcard_lt with ⟨a, b, hab, hEq⟩
  have hval_eq : g^[a.val] u0 = g^[b.val] u0 := congrArg Subtype.val hEq
  have hex_per : ∃ x0 ∈ U, ∃ d : ℕ, 0 < d ∧ g^[d] x0 = x0 := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · refine ⟨g^[a.val] u0, hiterU a.val, b.val - a.val, by omega, ?_⟩
      rw [← Function.iterate_add_apply, show b.val - a.val + a.val = b.val by omega, hval_eq]
    · refine ⟨g^[b.val] u0, hiterU b.val, a.val - b.val, by omega, ?_⟩
      rw [← Function.iterate_add_apply, show a.val - b.val + b.val = a.val by omega, hval_eq]
  rcases hex_per with ⟨x0, hx0U, hper⟩
  let L : ℕ := Nat.find hper
  have hLspec : 0 < L ∧ g^[L] x0 = x0 := Nat.find_spec hper
  have hLpos : 0 < L := hLspec.1
  have hLfix : g^[L] x0 = x0 := hLspec.2
  have hLmin : ∀ d : ℕ, 0 < d → d < L → g^[d] x0 ≠ x0 := fun d hd hlt =>
    fun h => Nat.find_min hper hlt ⟨hd, h⟩
  have hiter_x0 : ∀ k : ℕ, g^[k] x0 ∈ U := by
    intro k
    induction k with
    | zero => exact hx0U
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hgU _ ih
  have hmod : ∀ k : ℕ, g^[k] x0 = g^[k % L] x0 := by
    intro k
    have hdiv := Nat.div_add_mod k L
    have hmul : ∀ q : ℕ, g^[L * q] x0 = x0 := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
        rw [Nat.mul_succ, Function.iterate_add_apply, hLfix, ih]
    conv_lhs => rw [← hdiv, add_comm, Function.iterate_add_apply, hmul (k / L)]
  have hdistinct : ∀ i j : ℕ, i < L → j < L → g^[i] x0 = g^[j] x0 → i = j := by
    intro i j hi hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : g^[L - j + i] x0 = x0 := by
        rw [Function.iterate_add_apply, heq, ← Function.iterate_add_apply,
          show L - j + j = L by omega, hLfix]
      have h2 : g^[L - (j - i)] x0 = x0 := by
        simpa [show L - j + i = L - (j - i) by omega] using h1
      exact hLmin (L - (j - i)) (by omega) (by omega) h2
    · have h1 : g^[L - i + j] x0 = x0 := by
        rw [Function.iterate_add_apply, ← heq, ← Function.iterate_add_apply,
          show L - i + i = L by omega, hLfix]
      have h2 : g^[L - (i - j)] x0 = x0 := by
        simpa [show L - i + j = L - (i - j) by omega] using h1
      exact hLmin (L - (i - j)) (by omega) (by omega) h2
  let C : Finset (Fin n) := (Finset.range L).image (fun k => g^[k] x0)
  have hCU : C ⊆ U := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    exact hiter_x0 k
  have hCcard : C.card = L := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range L
    · intro i hi j hj heq
      exact hdistinct i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) heq
  have hCcl : ∀ y ∈ C, g y ∈ C := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    rw [← Function.iterate_succ_apply' g k x0, hmod (k + 1)]
    exact Finset.mem_image.mpr ⟨(k + 1) % L, Finset.mem_range.mpr (Nat.mod_lt _ hLpos), rfl⟩
  have hCinj : ∀ y1 ∈ C, ∀ y2 ∈ C, g y1 = g y2 → y1 = y2 := by
    intro y1 hy1 y2 hy2 heq
    rcases Finset.mem_image.mp hy1 with ⟨k1, hk1, rfl⟩
    rcases Finset.mem_image.mp hy2 with ⟨k2, hk2, rfl⟩
    have h1 : k1 < L := Finset.mem_range.mp hk1
    have h2 : k2 < L := Finset.mem_range.mp hk2
    have hsucc : g^[k1 + 1] x0 = g^[k2 + 1] x0 := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', heq]
    rw [hmod (k1 + 1), hmod (k2 + 1)] at hsucc
    have hm : (k1 + 1) % L = (k2 + 1) % L :=
      hdistinct _ _ (Nat.mod_lt _ hLpos) (Nat.mod_lt _ hLpos) hsucc
    have hk_eq : k1 = k2 := by
      by_cases h1e : k1 + 1 = L
      · by_cases h2e : k2 + 1 = L
        · omega
        · rw [h1e, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hm
          omega
      · by_cases h2e : k2 + 1 = L
        · rw [h2e, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hm
          omega
        · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
          omega
    rw [hk_eq]
  have hCgood : GoodSet g C := ⟨hCcl, hCinj⟩
  have hCne : C.Nonempty := ⟨x0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hLpos, rfl⟩⟩
  have hdich : ∀ (S : Finset (Fin n)), (∀ j ∈ S, g j ∈ S) → Disjoint C S ∨ C ⊆ S := by
    intro S hScl
    by_cases hdisj : Disjoint C S
    · exact Or.inl hdisj
    · right
      rw [Finset.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨y, hyC, hyS⟩
      rcases Finset.mem_image.mp hyC with ⟨k, hk, rfl⟩
      have hklt : k < L := Finset.mem_range.mp hk
      have hiterS : ∀ m : ℕ, g^[m] (g^[k] x0) ∈ S := by
        intro m
        induction m with
        | zero => exact hyS
        | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact hScl _ ih
      have hx0S : x0 ∈ S := by
        have := hiterS (L - k)
        rw [← Function.iterate_add_apply, show L - k + k = L by omega, hLfix] at this
        exact this
      have hallS : ∀ r : ℕ, g^[r] x0 ∈ S := by
        intro r
        induction r with
        | zero => exact hx0S
        | succ r ih =>
          rw [Function.iterate_succ_apply']
          exact hScl _ ih
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨r, _, rfl⟩
      exact hallS r
  have hsign : (-1 : ℚ) ^ C.card * ((Equiv.Perm.sign (permOn g C hCgood) : ℤ) : ℚ) = -1 := by
    rw [← sign_extPermOn g C hCgood]
    let σ := extPermOn g C hCgood
    change (-1 : ℚ) ^ C.card * ((Equiv.Perm.sign σ : ℤ) : ℚ) = -1
    have hpow_σ : ∀ k : ℕ, (σ ^ k) x0 = g^[k] x0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply']
        have hkC : g^[k] x0 ∈ C := by
          rw [hmod k]
          exact Finset.mem_image.mpr ⟨k % L, Finset.mem_range.mpr (Nat.mod_lt _ hLpos), rfl⟩
        exact extPermOn_apply_mem g C hCgood _ hkC
    by_cases hL1 : L = 1
    · have hσ1 : σ = 1 := by
        apply Equiv.ext
        intro y
        by_cases hyC : y ∈ C
        · rcases Finset.mem_image.mp hyC with ⟨k, hk, rfl⟩
          have hk0 : k = 0 := by
            have := Finset.mem_range.mp hk
            omega
          subst hk0
          simp only [Function.iterate_zero, id_eq]
          rw [extPermOn_apply_mem g C hCgood x0 hyC]
          have h1 : g x0 = x0 := by simpa [hL1] using hLfix
          exact h1
        · exact extPermOn_apply_notMem g C hCgood y hyC
      rw [hCcard, hL1, hσ1, map_one]
      norm_num
    · have hLge2 : 2 ≤ L := by omega
      have hsupp : σ.support = C := by
        ext y
        simp only [Equiv.Perm.mem_support]
        constructor
        · intro hne
          by_contra hyC
          exact hne (extPermOn_apply_notMem g C hCgood y hyC)
        · intro hyC heq
          rw [extPermOn_apply_mem g C hCgood y hyC] at heq
          rcases Finset.mem_image.mp hyC with ⟨k, hk, rfl⟩
          have hklt : k < L := Finset.mem_range.mp hk
          have hfix_m : ∀ m : ℕ, g^[m] (g^[k] x0) = g^[k] x0 := by
            intro m
            induction m with
            | zero => rfl
            | succ m ih =>
              rw [Function.iterate_succ_apply', ih, heq]
          have hxk : x0 = g^[k] x0 := by
            have := hfix_m (L - k)
            rw [← Function.iterate_add_apply, show L - k + k = L by omega, hLfix] at this
            exact this
          have h1 : g^[1] x0 = x0 := by
            simp only [Function.iterate_one]
            rw [hxk, heq]
          exact hLmin 1 (by omega) (by omega) h1
      have hcyc : σ.IsCycle := by
        refine ⟨x0, ?_, ?_⟩
        · have hx0C : x0 ∈ C := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hLpos, rfl⟩
          rw [← Equiv.Perm.mem_support, hsupp]
          exact hx0C
        · intro y hy
          have hyC : y ∈ C := by
            rw [← hsupp, Equiv.Perm.mem_support]
            exact hy
          rcases Finset.mem_image.mp hyC with ⟨k, _, rfl⟩
          exact ⟨(k : ℤ), by rw [zpow_natCast, hpow_σ k]⟩
      have hsc := hcyc.sign
      rw [hsupp, hCcard] at hsc
      rw [hCcard, hsc]
      push_cast
      have hsq : ((-1 : ℚ) ^ L) * ((-1 : ℚ) ^ L) = 1 := by
        rw [← mul_pow]
        norm_num
      linarith
  exact ⟨C, hCU, hCgood, hCne, hdich, hsign⟩

private lemma valid_signed_sum_zero {n : ℕ} (U : Finset (Fin n)) (hUne : U.Nonempty)
    (g : Fin n → Fin n) (hgU : ∀ j ∈ U, g j ∈ U) :
    (∑ S ∈ U.powerset.filter (fun S : Finset (Fin n) => GoodSet g S),
      if h : GoodSet g S then
        (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn g S h) : ℤ) : ℚ)
      else 0) = 0 := by
  classical
  let Valid : Finset (Finset (Fin n)) := U.powerset.filter (fun S => GoodSet g S)
  change (∑ S ∈ Valid, if h : GoodSet g S then
      (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn g S h) : ℤ) : ℚ) else 0) = 0
  rcases exists_cycle_of_maps U hUne g hgU with ⟨C, hCU, hCgood, hCne, hdich, hCsign⟩
  let V0 : Finset (Finset (Fin n)) := Valid.filter (fun S => Disjoint C S)
  let V1 : Finset (Finset (Fin n)) := Valid.filter (fun S => C ⊆ S)
  have hdisj01 : Disjoint V0 V1 := by
    rw [Finset.disjoint_left]
    intro S h0 h1
    have hd := (Finset.mem_filter.mp h0).2
    have hsub := (Finset.mem_filter.mp h1).2
    rcases hCne with ⟨x, hxC⟩
    exact Finset.disjoint_left.mp hd hxC (hsub hxC)
  have hunion01 : V0 ∪ V1 = Valid := by
    ext S
    simp only [V0, V1, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hS
      have hcl := ((Finset.mem_filter.mp hS).2).1
      rcases hdich S hcl with hd | hsub
      · exact Or.inl ⟨hS, hd⟩
      · exact Or.inr ⟨hS, hsub⟩
  rw [← hunion01, Finset.sum_union hdisj01]
  have hsum1 :
      (∑ T ∈ V1,
        if h : GoodSet g T then
          (-1 : ℚ) ^ T.card * ((Equiv.Perm.sign (permOn g T h) : ℤ) : ℚ)
        else 0) =
      -(∑ S ∈ V0,
        if h : GoodSet g S then
          (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn g S h) : ℤ) : ℚ)
        else 0) := by
    rw [← Finset.sum_neg_distrib]
    symm
    refine Finset.sum_bij (fun S _ => S ∪ C) ?_ ?_ ?_ ?_
    · intro S hS
      have hSV := (Finset.mem_filter.mp hS).1
      have hdisjCS := (Finset.mem_filter.mp hS).2
      have hSU := Finset.mem_powerset.mp (Finset.mem_filter.mp hSV).1
      have hSgood := (Finset.mem_filter.mp hSV).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.union_subset hSU hCU), ⟨?_, ?_⟩⟩, Finset.subset_union_right⟩
      · intro j hj
        rcases Finset.mem_union.mp hj with hjS | hjC
        · exact Finset.mem_union_left _ (hSgood.1 j hjS)
        · exact Finset.mem_union_right _ (hCgood.1 j hjC)
      · intro a ha b hb heq
        rcases Finset.mem_union.mp ha with haS | haC <;>
        rcases Finset.mem_union.mp hb with hbS | hbC
        · exact hSgood.2 a haS b hbS heq
        · exfalso
          exact Finset.disjoint_left.mp hdisjCS (heq ▸ hCgood.1 b hbC) (hSgood.1 a haS)
        · exfalso
          exact Finset.disjoint_left.mp hdisjCS (hCgood.1 a haC) (heq.symm ▸ hSgood.1 b hbS)
        · exact hCgood.2 a haC b hbC heq
    · intro S1 hS1 S2 hS2 heq
      have hd1 := (Finset.mem_filter.mp hS1).2
      have hd2 := (Finset.mem_filter.mp hS2).2
      ext x
      constructor
      · intro hx1
        have hxC : x ∉ C := fun hxC => Finset.disjoint_left.mp hd1 hxC hx1
        have hxU : x ∈ S2 ∪ C := heq ▸ Finset.mem_union_left _ hx1
        exact (Finset.mem_union.mp hxU).resolve_right hxC
      · intro hx2
        have hxC : x ∉ C := fun hxC => Finset.disjoint_left.mp hd2 hxC hx2
        have hxU : x ∈ S1 ∪ C := heq.symm ▸ Finset.mem_union_left _ hx2
        exact (Finset.mem_union.mp hxU).resolve_right hxC
    · intro T hT
      have hTV := (Finset.mem_filter.mp hT).1
      have hCT := (Finset.mem_filter.mp hT).2
      have hTU := Finset.mem_powerset.mp (Finset.mem_filter.mp hTV).1
      have hTgood := (Finset.mem_filter.mp hTV).2
      refine ⟨T \ C, ?_, Finset.sdiff_union_of_subset hCT⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.Subset.trans Finset.sdiff_subset hTU), ⟨?_, ?_⟩⟩, Finset.disjoint_sdiff⟩
      · intro j hj
        rcases Finset.mem_sdiff.mp hj with ⟨hjT, hjC⟩
        refine Finset.mem_sdiff.mpr ⟨hTgood.1 j hjT, ?_⟩
        intro hgjC
        have hsurj : Function.Surjective (permOn g C hCgood) := (permOn g C hCgood).surjective
        rcases hsurj ⟨g j, hgjC⟩ with ⟨⟨c, hcC⟩, hce⟩
        have hgc : g c = g j := congrArg Subtype.val hce
        have hcj : c = j := hTgood.2 c (hCT hcC) j hjT hgc
        exact hjC (hcj ▸ hcC)
      · intro a ha b hb heq
        exact hTgood.2 a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1 heq
    · intro S hS
      have hSV := (Finset.mem_filter.mp hS).1
      have hdisjCS := (Finset.mem_filter.mp hS).2
      have hSgood := (Finset.mem_filter.mp hSV).2
      have hTgood : GoodSet g (S ∪ C) := by
        refine ⟨?_, ?_⟩
        · intro j hj
          rcases Finset.mem_union.mp hj with hjS | hjC
          · exact Finset.mem_union_left _ (hSgood.1 j hjS)
          · exact Finset.mem_union_right _ (hCgood.1 j hjC)
        · intro a ha b hb heq
          rcases Finset.mem_union.mp ha with haS | haC <;>
          rcases Finset.mem_union.mp hb with hbS | hbC
          · exact hSgood.2 a haS b hbS heq
          · exfalso
            exact Finset.disjoint_left.mp hdisjCS (heq ▸ hCgood.1 b hbC) (hSgood.1 a haS)
          · exfalso
            exact Finset.disjoint_left.mp hdisjCS (hCgood.1 a haC) (heq.symm ▸ hSgood.1 b hbS)
          · exact hCgood.2 a haC b hbC heq
      simp only [hSgood, hTgood, ↓reduceDIte]
      have hcard_union : (S ∪ C).card = S.card + C.card :=
        Finset.card_union_of_disjoint hdisjCS.symm
      have hperm_mul :
          extPermOn g (S ∪ C) hTgood =
            extPermOn g S hSgood * extPermOn g C hCgood := by
        apply Equiv.ext
        intro j
        rw [Equiv.Perm.mul_apply]
        by_cases hjC : j ∈ C
        · have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hdisjCS hjC h
          have hgjC : g j ∈ C := hCgood.1 j hjC
          have hgjS : g j ∉ S := fun h => Finset.disjoint_left.mp hdisjCS hgjC h
          rw [extPermOn_apply_mem g (S ∪ C) hTgood j (Finset.mem_union_right _ hjC),
            extPermOn_apply_mem g C hCgood j hjC,
            extPermOn_apply_notMem g S hSgood (g j) hgjS]
        · by_cases hjS : j ∈ S
          · rw [extPermOn_apply_mem g (S ∪ C) hTgood j (Finset.mem_union_left _ hjS),
              extPermOn_apply_notMem g C hCgood j hjC,
              extPermOn_apply_mem g S hSgood j hjS]
          · have hjSC : j ∉ S ∪ C := by simp [hjS, hjC]
            rw [extPermOn_apply_notMem g (S ∪ C) hTgood j hjSC,
              extPermOn_apply_notMem g C hCgood j hjC,
              extPermOn_apply_notMem g S hSgood j hjS]
      have hsign_mul :
          ((Equiv.Perm.sign (permOn g (S ∪ C) hTgood) : ℤ) : ℚ) =
            ((Equiv.Perm.sign (permOn g S hSgood) : ℤ) : ℚ) *
              ((Equiv.Perm.sign (permOn g C hCgood) : ℤ) : ℚ) := by
        rw [← sign_extPermOn g (S ∪ C) hTgood,
          ← sign_extPermOn g S hSgood,
          ← sign_extPermOn g C hCgood,
          hperm_mul, Equiv.Perm.sign_mul]
        push_cast
        rfl
      rw [hcard_union, pow_add, hsign_mul]
      calc
        -((-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn g S hSgood) : ℤ) : ℚ))
            = ((-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn g S hSgood) : ℤ) : ℚ)) * (-1) := by ring
        _ = ((-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn g S hSgood) : ℤ) : ℚ)) *
              ((-1 : ℚ) ^ C.card * ((Equiv.Perm.sign (permOn g C hCgood) : ℤ) : ℚ)) := by
            rw [hCsign]
        _ = (-1 : ℚ) ^ S.card * (-1 : ℚ) ^ C.card *
              (((Equiv.Perm.sign (permOn g S hSgood) : ℤ) : ℚ) *
                ((Equiv.Perm.sign (permOn g C hCgood) : ℤ) : ℚ)) := by ring
  rw [hsum1, add_neg_cancel]

private def topOf {n : ℕ} (w : Fin n → ℕ) (F : Idx w → Fin n) : Fin n → Fin n :=
  fun j => if h : 0 < w j then F ⟨j, ⟨w j - 1, by omega⟩⟩ else j

private def mergeFn {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n)) (hS : ∀ t ∈ S, 0 < w t)
    (τ : Equiv.Perm S) (f : Idx (subVec w S) → Fin n) : Idx w → Fin n :=
  fun x =>
    if hx : x.1 ∈ S then
      if ha : x.2.val = w x.1 - 1 then
        (τ ⟨x.1, hx⟩).1
      else
        f ⟨x.1, ⟨x.2.val, by
          have := hS x.1 hx
          have := x.2.isLt
          simp only [subVec, hx, ↓reduceIte]
          omega⟩⟩
    else
      f ⟨x.1, ⟨x.2.val, by
        have := x.2.isLt
        simp only [subVec, hx, ↓reduceIte]
        omega⟩⟩

private lemma mergeFn_top {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n)) (hS : ∀ t ∈ S, 0 < w t)
    (τ : Equiv.Perm S) (f : Idx (subVec w S) → Fin n) (j : Fin n) (hj : j ∈ S) :
    topOf w (mergeFn w S hS τ f) j = (τ ⟨j, hj⟩).1 := by
  have hjpos : 0 < w j := hS j hj
  simp only [topOf, hjpos, ↓reduceDIte, mergeFn, hj]

private lemma mergeFn_balanced {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n))
    (hS : ∀ t ∈ S, 0 < w t) (τ : Equiv.Perm S) (f : Idx (subVec w S) → Fin n)
    (hf : f ∈ Balanced (subVec w S)) :
    mergeFn w S hS τ f ∈ Balanced w := by
  classical
  have hbal := (Finset.mem_filter.mp hf).2
  simp only [Balanced, Finset.mem_filter, Finset.mem_univ, true_and]
  intro k
  let Top : Finset (Idx w) := Finset.univ.filter (fun x : Idx w => x.1 ∈ S ∧ x.2.val = w x.1 - 1)
  let Bot : Finset (Idx w) := Finset.univ.filter (fun x : Idx w => ¬ (x.1 ∈ S ∧ x.2.val = w x.1 - 1))
  have hsplit :
      (Finset.univ.filter (fun x : Idx w => mergeFn w S hS τ f x = k)).card =
      (Top.filter (fun x => mergeFn w S hS τ f x = k)).card +
      (Bot.filter (fun x => mergeFn w S hS τ f x = k)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Top, Bot, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
  have htop_card :
      (Top.filter (fun x => mergeFn w S hS τ f x = k)).card = if k ∈ S then 1 else 0 := by
    by_cases hkS : k ∈ S
    · simp only [hkS, ↓reduceIte]
      let j0 : S := τ.symm ⟨k, hkS⟩
      have hj0pos : 0 < w j0.1 := hS j0.1 j0.2
      let x0 : Idx w := ⟨j0.1, ⟨w j0.1 - 1, by omega⟩⟩
      have heq : Top.filter (fun x => mergeFn w S hS τ f x = k) = {x0} := by
        ext x
        simp only [Top, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hxS, hxa⟩, hmk⟩
          simp only [mergeFn, hxS, ↓reduceDIte, hxa] at hmk
          have hτ : τ ⟨x.1, hxS⟩ = ⟨k, hkS⟩ := Subtype.ext hmk
          have hx1 : (⟨x.1, hxS⟩ : S) = j0 := by
            dsimp [j0]
            rw [← hτ, Equiv.symm_apply_apply]
          rcases x with ⟨j, ⟨a, ha⟩⟩
          dsimp only at hx1 hxa
          have hj_eq : j = j0.1 := congrArg Subtype.val hx1
          subst hj_eq
          dsimp [x0]
          congr 1
          exact Fin.ext hxa
        · rintro rfl
          refine ⟨⟨j0.2, rfl⟩, ?_⟩
          dsimp only [x0]
          simp only [mergeFn, j0.2, ↓reduceDIte]
          change (τ j0).1 = k
          simp [j0]
      rw [heq, Finset.card_singleton]
    · simp only [hkS, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxT, hmk⟩
      rcases (Finset.mem_filter.mp hxT).2 with ⟨hxS, hxa⟩
      simp only [mergeFn, hxS, ↓reduceDIte, hxa] at hmk
      exact hkS (hmk ▸ (τ ⟨x.1, hxS⟩).2)
  have hbot_card :
      (Bot.filter (fun x => mergeFn w S hS τ f x = k)).card = subVec w S k := by
    rw [← hbal k]
    refine Finset.card_bij
      (fun x hx =>
        ⟨x.1, ⟨x.2.val, by
          have hnot := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
          have hlt := x.2.isLt
          by_cases hxS : x.1 ∈ S
          · have hpos := hS x.1 hxS
            have hne : x.2.val ≠ w x.1 - 1 := fun ha => hnot ⟨hxS, ha⟩
            simp only [subVec, hxS, ↓reduceIte]
            omega
          · simp only [subVec, hxS, ↓reduceIte]
            omega⟩⟩)
      ?_ ?_ ?_
    · intro x hx
      have hnot := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      have hmk := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hxS : x.1 ∈ S
      · have hne : x.2.val ≠ w x.1 - 1 := fun ha => hnot ⟨hxS, ha⟩
        simpa only [mergeFn, hxS, ↓reduceDIte, hne] using hmk
      · simpa only [mergeFn, hxS, ↓reduceDIte] using hmk
    · intro x1 _ x2 _ heq
      rcases x1 with ⟨j1, ⟨a1, ha1⟩⟩
      rcases x2 with ⟨j2, ⟨a2, ha2⟩⟩
      have hj : j1 = j2 := congrArg Sigma.fst heq
      subst hj
      have ha : a1 = a2 := congrArg (fun z : Idx (subVec w S) => z.2.val) heq
      subst ha
      rfl
    · intro y hy
      have hfy := (Finset.mem_filter.mp hy).2
      have hylt : y.2.val < w y.1 := by
        have := y.2.isLt
        by_cases hyS : y.1 ∈ S
        · simp only [subVec, hyS, ↓reduceIte] at this
          omega
        · simp only [subVec, hyS, ↓reduceIte] at this
          omega
      refine ⟨⟨y.1, ⟨y.2.val, hylt⟩⟩, ?_, ?_⟩
      · have hnot : ¬ (y.1 ∈ S ∧ y.2.val = w y.1 - 1) := by
          rintro ⟨hyS, hya⟩
          have := y.2.isLt
          simp only [subVec, hyS, ↓reduceIte] at this
          omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩, ?_⟩
        by_cases hyS : y.1 ∈ S
        · have hne : y.2.val ≠ w y.1 - 1 := fun h => hnot ⟨hyS, h⟩
          simpa only [mergeFn, hyS, ↓reduceDIte, hne] using hfy
        · simpa only [mergeFn, hyS, ↓reduceDIte] using hfy
      · rcases y with ⟨j, ⟨a, ha⟩⟩
        rfl
  rw [hsplit, htop_card, hbot_card]
  by_cases hkS : k ∈ S
  · have := hS k hkS
    simp only [subVec, hkS, ↓reduceIte]
    omega
  · simp only [subVec, hkS, ↓reduceIte]
    omega

private lemma mergeFn_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℕ)
    (S : Finset (Fin n)) (hS : ∀ t ∈ S, 0 < w t) (τ : Equiv.Perm S)
    (f : Idx (subVec w S) → Fin n) :
    ∏ x : Idx w, A (mergeFn w S hS τ f x) x.1 =
      (∏ s : S, A (τ s).1 s.1) * (∏ y : Idx (subVec w S), A (f y) y.1) := by
  classical
  let Top : Finset (Idx w) := Finset.univ.filter (fun x : Idx w => x.1 ∈ S ∧ x.2.val = w x.1 - 1)
  let Bot : Finset (Idx w) := Finset.univ.filter (fun x : Idx w => ¬ (x.1 ∈ S ∧ x.2.val = w x.1 - 1))
  have hdisj : Disjoint Top Bot := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
  have hunion : Top ∪ Bot = Finset.univ := by
    ext x
    simp only [Top, Bot, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [← hunion, Finset.prod_union hdisj]
  congr 1
  · refine Finset.prod_bij
      (fun x hx => (⟨x.1, ((Finset.mem_filter.mp hx).2).1⟩ : S))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro x1 hx1 x2 hx2 heq
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      rcases x1 with ⟨j1, ⟨a1, ha1⟩⟩
      rcases x2 with ⟨j2, ⟨a2, ha2⟩⟩
      have hj : j1 = j2 := congrArg Subtype.val heq
      subst hj
      dsimp only at h1 h2
      have ha : a1 = a2 := h1.2.trans h2.2.symm
      subst ha
      rfl
    · intro s _
      have hspos := hS s.1 s.2
      refine ⟨⟨s.1, ⟨w s.1 - 1, by omega⟩⟩, ?_, ?_⟩
      · simp [Top, s.2]
      · exact Subtype.ext rfl
    · intro x hx
      have h1 := (Finset.mem_filter.mp hx).2
      simp only [mergeFn, h1.1, ↓reduceDIte, h1.2]
  · refine Finset.prod_bij
      (fun x hx =>
        ⟨x.1, ⟨x.2.val, by
          have hnot := (Finset.mem_filter.mp hx).2
          have hlt := x.2.isLt
          by_cases hxS : x.1 ∈ S
          · have hpos := hS x.1 hxS
            have hne : x.2.val ≠ w x.1 - 1 := fun ha => hnot ⟨hxS, ha⟩
            simp only [subVec, hxS, ↓reduceIte]
            omega
          · simp only [subVec, hxS, ↓reduceIte]
            omega⟩⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro x1 _ x2 _ heq
      rcases x1 with ⟨j1, ⟨a1, ha1⟩⟩
      rcases x2 with ⟨j2, ⟨a2, ha2⟩⟩
      have hj : j1 = j2 := congrArg Sigma.fst heq
      subst hj
      have ha : a1 = a2 := congrArg (fun z : Idx (subVec w S) => z.2.val) heq
      subst ha
      rfl
    · intro y _
      have hylt : y.2.val < w y.1 := by
        have := y.2.isLt
        by_cases hyS : y.1 ∈ S
        · simp only [subVec, hyS, ↓reduceIte] at this
          omega
        · simp only [subVec, hyS, ↓reduceIte] at this
          omega
      refine ⟨⟨y.1, ⟨y.2.val, hylt⟩⟩, ?_, ?_⟩
      · simp only [Bot, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨hyS, hya⟩
        have := y.2.isLt
        simp only [subVec, hyS, ↓reduceIte] at this
        omega
      · rcases y with ⟨j, ⟨a, ha⟩⟩
        rfl
    · intro x hx
      have hnot := (Finset.mem_filter.mp hx).2
      by_cases hxS : x.1 ∈ S
      · have hne : x.2.val ≠ w x.1 - 1 := fun h => hnot ⟨hxS, h⟩
        simp only [mergeFn, hxS, ↓reduceDIte, hne]
      · simp only [mergeFn, hxS, ↓reduceDIte]

private def splitBot {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n)) (F : Idx w → Fin n) :
    Idx (subVec w S) → Fin n :=
  fun y => F ⟨y.1, ⟨y.2.val, by
    have := y.2.isLt
    by_cases hyS : y.1 ∈ S
    · simp only [subVec, hyS, ↓reduceIte] at this
      omega
    · simp only [subVec, hyS, ↓reduceIte] at this
      omega⟩⟩

private lemma mergeFn_splitBot {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n))
    (hS : ∀ t ∈ S, 0 < w t) (F : Idx w → Fin n) (hgood : GoodSet (topOf w F) S) :
    mergeFn w S hS (permOn (topOf w F) S hgood) (splitBot w S F) = F := by
  funext x
  rcases x with ⟨j, ⟨a, ha⟩⟩
  by_cases hjS : j ∈ S
  · by_cases hae : a = w j - 1
    · simp only [mergeFn, hjS, ↓reduceDIte, hae]
      rw [permOn_apply_val]
      have hjpos : 0 < w j := hS j hjS
      simp only [topOf, hjpos, ↓reduceDIte]
    · simp only [mergeFn, hjS, ↓reduceDIte, hae, splitBot]
  · simp only [mergeFn, hjS, ↓reduceDIte, splitBot]

private lemma splitBot_balanced {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n))
    (hS : ∀ t ∈ S, 0 < w t) (F : Idx w → Fin n) (hF : F ∈ Balanced w)
    (hgood : GoodSet (topOf w F) S) :
    splitBot w S F ∈ Balanced (subVec w S) := by
  classical
  have hbal := (Finset.mem_filter.mp hF).2
  let τ := permOn (topOf w F) S hgood
  simp only [Balanced, Finset.mem_filter, Finset.mem_univ, true_and]
  intro k
  let Top : Finset (Idx w) := Finset.univ.filter (fun x : Idx w => x.1 ∈ S ∧ x.2.val = w x.1 - 1)
  let Bot : Finset (Idx w) := Finset.univ.filter (fun x : Idx w => ¬ (x.1 ∈ S ∧ x.2.val = w x.1 - 1))
  have hF_eq : mergeFn w S hS τ (splitBot w S F) = F :=
    mergeFn_splitBot w S hS F hgood
  have hsplit :
      (Finset.univ.filter (fun x : Idx w => F x = k)).card =
      (Top.filter (fun x => F x = k)).card + (Bot.filter (fun x => F x = k)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Top, Bot, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
  have htop_card : (Top.filter (fun x => F x = k)).card = if k ∈ S then 1 else 0 := by
    rw [← hF_eq]
    by_cases hkS : k ∈ S
    · simp only [hkS, ↓reduceIte]
      let j0 : S := τ.symm ⟨k, hkS⟩
      have hj0pos : 0 < w j0.1 := hS j0.1 j0.2
      let x0 : Idx w := ⟨j0.1, ⟨w j0.1 - 1, by omega⟩⟩
      have heq : Top.filter (fun x => mergeFn w S hS τ (splitBot w S F) x = k) = {x0} := by
        ext x
        simp only [Top, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hxS, hxa⟩, hmk⟩
          simp only [mergeFn, hxS, ↓reduceDIte, hxa] at hmk
          have hτ : τ ⟨x.1, hxS⟩ = ⟨k, hkS⟩ := Subtype.ext hmk
          have hx1 : (⟨x.1, hxS⟩ : S) = j0 := by
            dsimp [j0]
            rw [← hτ, Equiv.symm_apply_apply]
          rcases x with ⟨j, ⟨a, ha⟩⟩
          dsimp only at hx1 hxa
          have hj_eq : j = j0.1 := congrArg Subtype.val hx1
          subst hj_eq
          dsimp [x0]
          congr 1
          exact Fin.ext hxa
        · rintro rfl
          refine ⟨⟨j0.2, rfl⟩, ?_⟩
          dsimp only [x0]
          simp only [mergeFn, j0.2, ↓reduceDIte]
          change (τ j0).1 = k
          simp [j0]
      rw [heq, Finset.card_singleton]
    · simp only [hkS, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxT, hmk⟩
      rcases (Finset.mem_filter.mp hxT).2 with ⟨hxS, hxa⟩
      simp only [mergeFn, hxS, ↓reduceDIte, hxa] at hmk
      exact hkS (hmk ▸ (τ ⟨x.1, hxS⟩).2)
  have hbot_eq :
      (Finset.univ.filter (fun y : Idx (subVec w S) => splitBot w S F y = k)).card =
      (Bot.filter (fun x => F x = k)).card := by
    refine Finset.card_bij
      (fun y _ => ⟨y.1, ⟨y.2.val, by
        have := y.2.isLt
        by_cases hyS : y.1 ∈ S
        · simp only [subVec, hyS, ↓reduceIte] at this
          omega
        · simp only [subVec, hyS, ↓reduceIte] at this
          omega⟩⟩)
      ?_ ?_ ?_
    · intro y hy
      have hfy := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hfy⟩
      rintro ⟨hyS, hya⟩
      have hylt := y.2.isLt
      simp only [subVec, hyS, ↓reduceIte] at hylt
      dsimp only at hya
      omega
    · intro y1 _ y2 _ heq
      rcases y1 with ⟨j1, ⟨a1, ha1⟩⟩
      rcases y2 with ⟨j2, ⟨a2, ha2⟩⟩
      have hj : j1 = j2 := congrArg Sigma.fst heq
      subst hj
      have ha : a1 = a2 := congrArg (fun z : Idx w => z.2.val) heq
      subst ha
      rfl
    · intro x hx
      have hnot := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      have hfx := (Finset.mem_filter.mp hx).2
      have hxlt : x.2.val < subVec w S x.1 := by
        have hlt := x.2.isLt
        by_cases hxS : x.1 ∈ S
        · have hpos := hS x.1 hxS
          have hne : x.2.val ≠ w x.1 - 1 := fun h => hnot ⟨hxS, h⟩
          simp only [subVec, hxS, ↓reduceIte]
          omega
        · simp only [subVec, hxS, ↓reduceIte]
          omega
      refine ⟨⟨x.1, ⟨x.2.val, hxlt⟩⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfx⟩
      · rcases x with ⟨j, ⟨a, ha⟩⟩
        rfl
  rw [hbot_eq]
  have htot := hbal k
  rw [hsplit, htop_card] at htot
  by_cases hkS : k ∈ S
  · simp only [subVec, hkS, ↓reduceIte] at htot ⊢
    omega
  · simp only [subVec, hkS, ↓reduceIte] at htot ⊢
    omega

private lemma main_nonzero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℕ)
    (hpos : ∃ t : Fin n, 0 < w t) :
    let choices := Finset.univ.filter (fun S : Finset (Fin n) => ∀ t ∈ S, 0 < w t)
    (∑ S ∈ choices, (-1 : ℚ) ^ S.card *
      (A.submatrix (fun rowIndex : S => rowIndex.val) (fun colIndex : S => colIndex.val)).det *
      ∑ f ∈ Balanced (subVec w S), ∏ x : Idx (subVec w S), A (f x) x.1) = 0 := by
  classical
  intro choices
  let U : Finset (Fin n) := Finset.univ.filter (fun t : Fin n => 0 < w t)
  have hUne : U.Nonempty := by
    rcases hpos with ⟨t, ht⟩
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  have hchoices_eq : choices = U.powerset := by
    ext S
    simp only [choices, U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    constructor
    · intro h t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h t ht⟩
    · intro h t ht
      exact (Finset.mem_filter.mp (h ht)).2
  let rhsSum : ℚ :=
    ∑ F ∈ Balanced w, (∏ x : Idx w, A (F x) x.1) *
      ∑ S ∈ U.powerset.filter (fun S : Finset (Fin n) => GoodSet (topOf w F) S),
        if h : GoodSet (topOf w F) S then
          (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn (topOf w F) S h) : ℤ) : ℚ)
        else 0
  have hrhs_zero : rhsSum = 0 := by
    refine Finset.sum_eq_zero ?_
    intro F hF
    have hFU : ∀ j ∈ U, topOf w F j ∈ U := by
      intro j hj
      have hjpos : 0 < w j := (Finset.mem_filter.mp hj).2
      have hbal := (Finset.mem_filter.mp hF).2 (topOf w F j)
      have hne : (Finset.univ.filter (fun x : Idx w => F x = topOf w F j)).Nonempty := by
        refine ⟨⟨j, ⟨w j - 1, by omega⟩⟩, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, topOf, hjpos, ↓reduceDIte]
      have hcard_pos : 0 < w (topOf w F j) := by
        rw [← hbal]
        exact Finset.card_pos.mpr hne
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard_pos⟩
    rw [valid_signed_sum_zero U hUne (topOf w F) hFU, mul_zero]
  have hstep1 :
      (∑ S ∈ choices, (-1 : ℚ) ^ S.card *
        (A.submatrix (fun rowIndex : S => rowIndex.val) (fun colIndex : S => colIndex.val)).det *
        ∑ f ∈ Balanced (subVec w S), ∏ x : Idx (subVec w S), A (f x) x.1) =
      ∑ S ∈ choices, ∑ τ : Equiv.Perm S, ∑ f ∈ Balanced (subVec w S),
        (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign τ : ℤ) : ℚ) *
          ((∏ s : S, A (τ s).1 s.1) * (∏ x : Idx (subVec w S), A (f x) x.1)) := by
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [Matrix.det_apply']
    simp only [Matrix.submatrix_apply]
    have hmul1 :
        (-1 : ℚ) ^ S.card * (∑ τ : Equiv.Perm S, ((Equiv.Perm.sign τ : ℤ) : ℚ) * ∏ s : S, A (τ s).1 s.1) =
        ∑ τ : Equiv.Perm S, (-1 : ℚ) ^ S.card * (((Equiv.Perm.sign τ : ℤ) : ℚ) * ∏ s : S, A (τ s).1 s.1) :=
      Finset.mul_sum _ _ _
    rw [hmul1, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro τ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro f _
    ring
  have hstep2 :
      rhsSum =
      ∑ S ∈ choices, ∑ F ∈ (Balanced w).filter (fun F => GoodSet (topOf w F) S),
        if h : GoodSet (topOf w F) S then
          (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn (topOf w F) S h) : ℤ) : ℚ) *
            (∏ x : Idx w, A (F x) x.1)
        else 0 := by
    dsimp only [rhsSum]
    simp_rw [Finset.mul_sum]
    rw [← hchoices_eq]
    have hrewrite : ∀ F ∈ Balanced w,
        (∑ S ∈ choices.filter (fun S : Finset (Fin n) => GoodSet (topOf w F) S),
          (∏ x : Idx w, A (F x) x.1) *
            if h : GoodSet (topOf w F) S then
              (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn (topOf w F) S h) : ℤ) : ℚ)
            else 0) =
        ∑ S ∈ choices,
          if h : GoodSet (topOf w F) S then
            (-1 : ℚ) ^ S.card * ((Equiv.Perm.sign (permOn (topOf w F) S h) : ℤ) : ℚ) *
              (∏ x : Idx w, A (F x) x.1)
          else 0 := by
      intro F _
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro S _
      by_cases h : GoodSet (topOf w F) S
      · simp only [h, ↓reduceDIte, ↓reduceIte]
        ring
      · simp only [h, ↓reduceDIte, ↓reduceIte]
    rw [Finset.sum_congr rfl hrewrite, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro F _
    by_cases h : GoodSet (topOf w F) S
    · simp only [h, ↓reduceDIte, ↓reduceIte]
    · simp only [h, ↓reduceDIte, ↓reduceIte]
  rw [hstep1, ← hrhs_zero, hstep2]
  refine Finset.sum_congr rfl ?_
  intro S hSmem
  have hSpos : ∀ t ∈ S, 0 < w t := (Finset.mem_filter.mp hSmem).2
  rw [← Finset.sum_product']
  refine Finset.sum_bij
    (fun p _ => mergeFn w S hSpos p.1 p.2)
    ?_ ?_ ?_ ?_
  · rintro ⟨τ, f⟩ hp
    have hf : f ∈ Balanced (subVec w S) := (Finset.mem_product.mp hp).2
    refine Finset.mem_filter.mpr ⟨mergeFn_balanced w S hSpos τ f hf, ?_, ?_⟩
    · intro j hj
      rw [mergeFn_top w S hSpos τ f j hj]
      exact (τ ⟨j, hj⟩).2
    · intro a ha b hb heq
      rw [mergeFn_top w S hSpos τ f a ha, mergeFn_top w S hSpos τ f b hb] at heq
      exact congrArg Subtype.val (τ.injective (Subtype.ext heq))
  · rintro ⟨τ1, f1⟩ _ ⟨τ2, f2⟩ _ heq
    have hτ : τ1 = τ2 := by
      apply Equiv.ext
      rintro ⟨j, hj⟩
      apply Subtype.ext
      have hjpos := hSpos j hj
      have h1 := congrFun heq ⟨j, ⟨w j - 1, by omega⟩⟩
      simpa only [mergeFn, hj, ↓reduceDIte] using h1
    have hf : f1 = f2 := by
      funext ⟨j, ⟨a, ha⟩⟩
      have hlt : a < w j := by
        by_cases hjS : j ∈ S
        · simp only [subVec, hjS, ↓reduceIte] at ha
          omega
        · simp only [subVec, hjS, ↓reduceIte] at ha
          omega
      have h1 := congrFun heq ⟨j, ⟨a, hlt⟩⟩
      by_cases hjS : j ∈ S
      · have hne : a ≠ w j - 1 := by
          simp only [subVec, hjS, ↓reduceIte] at ha
          omega
        simpa only [mergeFn, hjS, ↓reduceDIte, hne] using h1
      · simpa only [mergeFn, hjS, ↓reduceDIte] using h1
    exact Prod.ext hτ hf
  · intro F hF
    rcases Finset.mem_filter.mp hF with ⟨hFbal, hFgood⟩
    refine ⟨(permOn (topOf w F) S hFgood, splitBot w S F), ?_,
      mergeFn_splitBot w S hSpos F hFgood⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, splitBot_balanced w S hSpos F hFbal hFgood⟩
  · rintro ⟨τ, f⟩ _
    have hgood : GoodSet (topOf w (mergeFn w S hSpos τ f)) S := by
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [mergeFn_top w S hSpos τ f j hj]
        exact (τ ⟨j, hj⟩).2
      · intro a ha b hb heq
        rw [mergeFn_top w S hSpos τ f a ha, mergeFn_top w S hSpos τ f b hb] at heq
        exact congrArg Subtype.val (τ.injective (Subtype.ext heq))
    simp only [hgood, ↓reduceDIte]
    rw [mergeFn_prod]
    have hτ_eq : permOn (topOf w (mergeFn w S hSpos τ f)) S hgood = τ := by
      apply Equiv.ext
      rintro ⟨j, hj⟩
      apply Subtype.ext
      rw [permOn_apply_val, mergeFn_top w S hSpos τ f j hj]
    rw [hτ_eq]

end PEqualNP.Outside.L_lib_456_aux

theorem PEqualNP.Outside.L_lib_456 : (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℕ),
  let coeff := fun (v : Fin n → ℕ) =>
    let big : Matrix (Σ j : Fin n, Fin (v j)) (Σ j : Fin n, Fin (v j)) ℚ :=
      fun copyRow copyCol => A copyRow.1 copyCol.1
    big.permanent / (∏ i : Fin n, (Nat.factorial (v i) : ℚ))
  let choices := Finset.univ.filter (fun S : Finset (Fin n) => ∀ t ∈ S, 0 < w t)
  (∑ S ∈ choices, (-1 : ℚ)^S.card *
    (A.submatrix (fun rowIndex : S => rowIndex.val) (fun colIndex : S => colIndex.val)).det *
    coeff (fun pos => w pos - (if pos ∈ S then 1 else 0))) =
    if (∀ t, w t = 0) then 1 else 0) := by
  classical
  intro n A w coeff choices
  have hcoeff : ∀ v : Fin n → ℕ, coeff v =
      ∑ f ∈ PEqualNP.Outside.L_lib_456_aux.Balanced v,
        ∏ x : PEqualNP.Outside.L_lib_456_aux.Idx v, A (f x) x.1 :=
    fun v => PEqualNP.Outside.L_lib_456_aux.coeff_eq_sum_balanced A v
  by_cases hzero : ∀ t : Fin n, w t = 0
  · have hite : (if (∀ t : Fin n, w t = 0) then (1 : ℚ) else 0) = 1 := by simp [hzero]
    rw [hite]
    have hch : choices = {∅} := by
      ext S
      simp only [choices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        have := h t ht
        have := hzero t
        omega
      · rintro rfl t ht
        exact False.elim (Finset.notMem_empty t ht)
    rw [hch, Finset.sum_singleton]
    have hdet : (A.submatrix (fun rowIndex : (∅ : Finset (Fin n)) => rowIndex.val)
        (fun colIndex : (∅ : Finset (Fin n)) => colIndex.val)).det = 1 := by
      have : IsEmpty (∅ : Finset (Fin n)) := ⟨fun x => Finset.notMem_empty x.1 x.2⟩
      exact Matrix.det_isEmpty
    have hv : (fun pos : Fin n => w pos - (if pos ∈ (∅ : Finset (Fin n)) then 1 else 0)) =
        (fun _ => 0) := by
      funext t
      simp [hzero t]
    rw [Finset.card_empty, pow_zero, one_mul, hdet, one_mul, hv]
    have : IsEmpty (Σ j : Fin n, Fin ((fun _ : Fin n => 0) j)) := ⟨fun x => Fin.elim0 x.2⟩
    dsimp only [coeff]
    have hperm : (Matrix.permanent (fun (copyRow copyCol : Σ j : Fin n, Fin ((fun _ : Fin n => 0) j)) =>
        A copyRow.1 copyCol.1)) = 1 := by
      unfold Matrix.permanent
      simp
    rw [hperm]
    simp
  · have hite : (if (∀ t : Fin n, w t = 0) then (1 : ℚ) else 0) = 0 := by simp [hzero]
    rw [hite]
    push Not at hzero
    rcases hzero with ⟨t, ht⟩
    have hpos : ∃ t : Fin n, 0 < w t := ⟨t, Nat.pos_of_ne_zero ht⟩
    have hrew :
        (∑ S ∈ choices, (-1 : ℚ) ^ S.card *
          (A.submatrix (fun rowIndex : S => rowIndex.val) (fun colIndex : S => colIndex.val)).det *
          coeff (fun pos => w pos - (if pos ∈ S then 1 else 0))) =
        ∑ S ∈ choices, (-1 : ℚ) ^ S.card *
          (A.submatrix (fun rowIndex : S => rowIndex.val) (fun colIndex : S => colIndex.val)).det *
          ∑ f ∈ PEqualNP.Outside.L_lib_456_aux.Balanced (PEqualNP.Outside.L_lib_456_aux.subVec w S),
            ∏ x : PEqualNP.Outside.L_lib_456_aux.Idx (PEqualNP.Outside.L_lib_456_aux.subVec w S),
              A (f x) x.1 := by
      refine Finset.sum_congr rfl ?_
      intro S _
      congr 1
      exact hcoeff (PEqualNP.Outside.L_lib_456_aux.subVec w S)
    rw [hrew]
    exact PEqualNP.Outside.L_lib_456_aux.main_nonzero A w hpos
