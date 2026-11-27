import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_869_aux

abbrev BlockSpace {m : ℕ} (len : Fin m → ℕ) := (i : Fin m) → (Fin (len i) → ZMod 2)

def Mass {m s : ℕ} {len : Fin m → ℕ}
    (P : BlockSpace len →ₗ[ZMod 2] (Fin s → ZMod 2))
    (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ)
    (S : Finset (Fin s → ZMod 2)) : ℕ :=
  ∑ x : BlockSpace len, if P x ∈ S then ∏ i : Fin m, a i (x i) else 0

def Pref {m s : ℕ} {len : Fin m → ℕ}
    (P : BlockSpace len →ₗ[ZMod 2] (Fin s → ZMod 2)) (j : ℕ) : Set (Fin s → ZMod 2) :=
  {y | ∃ x : BlockSpace len, (∀ i : Fin m, j ≤ i.val → x i = 0) ∧ P x = y}

def initVec {m : ℕ} {len : Fin (m + 1) → ℕ} (x : BlockSpace len) :
    BlockSpace (fun i : Fin m => len i.castSucc) :=
  fun i => x i.castSucc

def snocVec {m : ℕ} {len : Fin (m + 1) → ℕ}
    (x' : BlockSpace (fun i : Fin m => len i.castSucc))
    (v : Fin (len (Fin.last m)) → ZMod 2) : BlockSpace len :=
  Fin.lastCases v x'

lemma initVec_snocVec {m : ℕ} {len : Fin (m + 1) → ℕ}
    (x' : BlockSpace (fun i : Fin m => len i.castSucc))
    (v : Fin (len (Fin.last m)) → ZMod 2) :
    initVec (snocVec x' v) = x' := by
  ext i j
  simp [initVec, snocVec]

lemma snocVec_last {m : ℕ} {len : Fin (m + 1) → ℕ}
    (x' : BlockSpace (fun i : Fin m => len i.castSucc))
    (v : Fin (len (Fin.last m)) → ZMod 2) :
    snocVec x' v (Fin.last m) = v := by
  simp [snocVec]

lemma snocVec_init_last {m : ℕ} {len : Fin (m + 1) → ℕ} (x : BlockSpace len) :
    snocVec (initVec x) (x (Fin.last m)) = x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [snocVec]
  · intro i'
    simp [snocVec, initVec]

lemma snocVec_add {m : ℕ} {len : Fin (m + 1) → ℕ}
    (x₁ x₂ : BlockSpace (fun i : Fin m => len i.castSucc))
    (v₁ v₂ : Fin (len (Fin.last m)) → ZMod 2) :
    snocVec (x₁ + x₂) (v₁ + v₂) = snocVec x₁ v₁ + snocVec x₂ v₂ := by
  funext i
  refine Fin.lastCases ?_ ?_ i <;> simp [snocVec]

lemma snocVec_smul {m : ℕ} {len : Fin (m + 1) → ℕ} (c : ZMod 2)
    (x' : BlockSpace (fun i : Fin m => len i.castSucc))
    (v : Fin (len (Fin.last m)) → ZMod 2) :
    snocVec (c • x') (c • v) = c • snocVec x' v := by
  funext i
  refine Fin.lastCases ?_ ?_ i <;> simp [snocVec]

lemma snocVec_zero {m : ℕ} {len : Fin (m + 1) → ℕ} :
    snocVec (len := len) 0 0 = 0 := by
  funext i
  refine Fin.lastCases ?_ ?_ i <;> simp [snocVec]

def snocEquiv {m : ℕ} (len : Fin (m + 1) → ℕ) :
    (BlockSpace (fun i : Fin m => len i.castSucc) × (Fin (len (Fin.last m)) → ZMod 2)) ≃
      BlockSpace len where
  toFun p := snocVec p.1 p.2
  invFun x := (initVec x, x (Fin.last m))
  left_inv p := by
    ext
    · exact congrFun (congrFun (initVec_snocVec p.1 p.2) _) _
    · exact congrFun (snocVec_last p.1 p.2) _
  right_inv x := snocVec_init_last x

def initLin {m : ℕ} (len : Fin (m + 1) → ℕ) :
    BlockSpace len →ₗ[ZMod 2] BlockSpace (fun i : Fin m => len i.castSucc) where
  toFun := initVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def embedInit {m : ℕ} (len : Fin (m + 1) → ℕ) :
    BlockSpace (fun i : Fin m => len i.castSucc) →ₗ[ZMod 2] BlockSpace len where
  toFun x' := snocVec x' 0
  map_add' x₁ x₂ := by simpa using snocVec_add x₁ x₂ 0 0
  map_smul' c x' := by simpa using snocVec_smul c x' 0

def embedLast {m : ℕ} (len : Fin (m + 1) → ℕ) :
    (Fin (len (Fin.last m)) → ZMod 2) →ₗ[ZMod 2] BlockSpace len where
  toFun v := snocVec 0 v
  map_add' v₁ v₂ := by simpa using snocVec_add (len := len) 0 0 v₁ v₂
  map_smul' c v := by simpa using snocVec_smul (len := len) c 0 v

lemma embedLast_eq_single {m : ℕ} {len : Fin (m + 1) → ℕ}
    (v : Fin (len (Fin.last m)) → ZMod 2) :
    embedLast len v = Pi.single (Fin.last m) v := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [embedLast, snocVec]
  · intro i'
    have hne : i'.castSucc ≠ Fin.last m := Fin.castSucc_ne_last i'
    simp [embedLast, snocVec, Pi.single_eq_of_ne hne]

lemma embedInit_single {m : ℕ} {len : Fin (m + 1) → ℕ}
    (i : Fin m) (v : Fin (len i.castSucc) → ZMod 2) :
    embedInit len (Pi.single i v) = Pi.single i.castSucc v := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · have hne : Fin.last m ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp [embedInit, snocVec, Pi.single_eq_of_ne hne]
  · intro k'
    by_cases hki : k' = i
    · subst hki
      simp [embedInit, snocVec]
    · have hne : k'.castSucc ≠ i.castSucc := fun h => hki (Fin.castSucc_inj.mp h)
      simp [embedInit, snocVec, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hne]

lemma snocVec_decomp {m : ℕ} {len : Fin (m + 1) → ℕ}
    (x' : BlockSpace (fun i : Fin m => len i.castSucc))
    (v : Fin (len (Fin.last m)) → ZMod 2) :
    snocVec x' v = embedInit len x' + embedLast len v := by
  simpa [embedInit, embedLast] using snocVec_add x' 0 0 v

lemma char2_add_self_vec {s : ℕ} (y : Fin s → ZMod 2) : y + y = 0 := by
  ext j
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h (y j)

lemma pref_ge_m {m s : ℕ} {len : Fin m → ℕ}
    (P : BlockSpace len →ₗ[ZMod 2] (Fin s → ZMod 2)) {j : ℕ} (hj : m ≤ j) :
    Pref P j = (LinearMap.range P : Set (Fin s → ZMod 2)) := by
  ext y
  simp only [Pref, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · rintro ⟨x, _, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, fun i hi => by omega, rfl⟩

lemma main_ind (s : ℕ) :
    ∀ (m : ℕ) (len : Fin m → ℕ) (P : BlockSpace len →ₗ[ZMod 2] (Fin s → ZMod 2)),
      ∃ Q : BlockSpace len →ₗ[ZMod 2] (Fin s → ZMod 2),
        (∀ j : ℕ, Pref Q j = Pref P j) ∧
        (∀ x : BlockSpace len, Q x = 0 → ∀ i : Fin m, Q (Pi.single i (x i)) = 0) ∧
        ∀ (a : (i : Fin m) → (Fin (len i) → ZMod 2) → ℕ) (S : Finset (Fin s → ZMod 2)),
          (∀ y ∈ S, y ∈ LinearMap.range P) →
          ∃ T : Finset (Fin s → ZMod 2),
            (∀ y ∈ T, y ∈ LinearMap.range Q) ∧
            T.card = S.card ∧
            Mass P a S ≤ Mass Q a T := by
  classical
  intro m
  induction m with
  | zero =>
    intro len P
    refine ⟨P, fun _ => rfl, fun _ _ i => Fin.elim0 i, fun a S hS => ⟨S, hS, rfl, le_refl _⟩⟩
  | succ m ih =>
    intro len P
    let len' : Fin m → ℕ := fun i => len i.castSucc
    let P' : BlockSpace len' →ₗ[ZMod 2] (Fin s → ZMod 2) := P.comp (embedInit len)
    let B : (Fin (len (Fin.last m)) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) := P.comp (embedLast len)
    obtain ⟨Q', hQ'_pref, hQ'_ind, hQ'_dom⟩ := ih len' P'
    let U : Submodule (ZMod 2) (Fin s → ZMod 2) := LinearMap.range P'
    have hrangeQ' : LinearMap.range Q' = U := by
      have h := hQ'_pref m
      rw [pref_ge_m Q' (le_refl m), pref_ge_m P' (le_refl m)] at h
      exact SetLike.coe_injective h
    obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
    let pU : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
      (Submodule.subtype U).comp (Submodule.projectionOnto U W hUW)
    let pW : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
      (Submodule.subtype W).comp (Submodule.projectionOnto W U hUW.symm)
    have hpU_mem : ∀ y, pU y ∈ U := fun y => (Submodule.projectionOnto U W hUW y).property
    have hpW_mem : ∀ y, pW y ∈ W := fun y => (Submodule.projectionOnto W U hUW.symm y).property
    have hpU_on_U : ∀ y ∈ U, pU y = y := fun y hy => by
      have h := Submodule.projectionOnto_apply_left hUW ⟨y, hy⟩
      exact congrArg Subtype.val h
    have hpW_on_U : ∀ y ∈ U, pW y = 0 := fun y hy => by
      have h := Submodule.projectionOnto_apply_right hUW.symm ⟨y, hy⟩
      exact congrArg Subtype.val h
    have hpU_on_W : ∀ y ∈ W, pU y = 0 := fun y hy => by
      have h := Submodule.projectionOnto_apply_right hUW ⟨y, hy⟩
      exact congrArg Subtype.val h
    have hpW_on_W : ∀ y ∈ W, pW y = y := fun y hy => by
      have h := Submodule.projectionOnto_apply_left hUW.symm ⟨y, hy⟩
      exact congrArg Subtype.val h
    have hpU_add_pW : ∀ y, pU y + pW y = y := by
      intro y
      have htop : y ∈ U ⊔ W := by rw [hUW.sup_eq_top]; trivial
      rcases Submodule.mem_sup.mp htop with ⟨u, hu, w, hw, rfl⟩
      rw [map_add, map_add, hpU_on_U u hu, hpU_on_W w hw, hpW_on_U u hu, hpW_on_W w hw, add_zero, zero_add]
    have hdirect_inj : ∀ {u₁ u₂ w₁ w₂ : Fin s → ZMod 2},
        u₁ ∈ U → u₂ ∈ U → w₁ ∈ W → w₂ ∈ W → u₁ + w₁ = u₂ + w₂ → u₁ = u₂ ∧ w₁ = w₂ := by
      intro u₁ u₂ w₁ w₂ hu₁ hu₂ hw₁ hw₂ heq
      have hpu := congrArg pU heq
      have hpw := congrArg pW heq
      rw [map_add, map_add, hpU_on_U u₁ hu₁, hpU_on_W w₁ hw₁, hpU_on_U u₂ hu₂, hpU_on_W w₂ hw₂, add_zero, add_zero] at hpu
      rw [map_add, map_add, hpW_on_U u₁ hu₁, hpW_on_W w₁ hw₁, hpW_on_U u₂ hu₂, hpW_on_W w₂ hw₂, zero_add, zero_add] at hpw
      exact ⟨hpu, hpw⟩
    let lastLin : BlockSpace len →ₗ[ZMod 2] (Fin (len (Fin.last m)) → ZMod 2) :=
      LinearMap.proj (R := ZMod 2) (Fin.last m)
    let Q : BlockSpace len →ₗ[ZMod 2] (Fin s → ZMod 2) :=
      Q'.comp (initLin len) + (pW.comp B).comp lastLin
    have hP_snoc : ∀ x' v, P (snocVec x' v) = P' x' + B v := by
      intro x' v
      rw [snocVec_decomp, map_add]
      rfl
    have hQ_snoc : ∀ x' v, Q (snocVec x' v) = Q' x' + pW (B v) := by
      intro x' v
      change Q' (initVec (snocVec x' v)) + pW (B (snocVec x' v (Fin.last m))) = Q' x' + pW (B v)
      rw [initVec_snocVec, snocVec_last]
    have hrange_eq : LinearMap.range Q = LinearMap.range P := by
      ext y
      simp only [LinearMap.mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        rw [← snocVec_init_last x, hQ_snoc]
        have hu1 : Q' (initVec x) ∈ U := by rw [← hrangeQ']; exact LinearMap.mem_range_self Q' _
        have hu2 : pU (B (x (Fin.last m))) ∈ U := hpU_mem _
        have hu_diff : Q' (initVec x) - pU (B (x (Fin.last m))) ∈ U := U.sub_mem hu1 hu2
        rcases hu_diff with ⟨x₁, hx₁⟩
        refine ⟨snocVec x₁ (x (Fin.last m)), ?_⟩
        rw [hP_snoc]
        calc P' x₁ + B (x (Fin.last m))
            = (Q' (initVec x) - pU (B (x (Fin.last m)))) +
                (pU (B (x (Fin.last m))) + pW (B (x (Fin.last m)))) := by
              rw [hx₁, hpU_add_pW]
          _ = Q' (initVec x) + pW (B (x (Fin.last m))) := by abel
      · rintro ⟨x, rfl⟩
        rw [← snocVec_init_last x, hP_snoc]
        have hu : P' (initVec x) + pU (B (x (Fin.last m))) ∈ U :=
          U.add_mem (LinearMap.mem_range_self P' _) (hpU_mem _)
        rw [← hrangeQ'] at hu
        rcases hu with ⟨x₁, hx₁⟩
        refine ⟨snocVec x₁ (x (Fin.last m)), ?_⟩
        rw [hQ_snoc, hx₁, add_assoc, hpU_add_pW]
    have hQ_pref : ∀ j : ℕ, Pref Q j = Pref P j := by
      intro j
      by_cases hjm : j ≤ m
      · ext y
        simp only [Pref, Set.mem_ofPred_eq]
        have hiffQ : (∃ x : BlockSpace len, (∀ i : Fin (m + 1), j ≤ i.val → x i = 0) ∧ Q x = y) ↔
            y ∈ Pref Q' j := by
          simp only [Pref, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨x, hx0, rfl⟩
            have hlast : x (Fin.last m) = 0 := hx0 (Fin.last m) (by simpa using hjm)
            refine ⟨initVec x, fun i hi => hx0 i.castSucc hi, ?_⟩
            conv_rhs => rw [← snocVec_init_last x, hlast, hQ_snoc, map_zero, map_zero, add_zero]
          · rintro ⟨x', hx', rfl⟩
            refine ⟨snocVec x' 0, fun i => ?_, ?_⟩
            · refine Fin.lastCases ?_ ?_ i
              · intro _; simp [snocVec]
              · intro i' hi
                simpa [snocVec] using hx' i' hi
            · rw [hQ_snoc, map_zero, map_zero, add_zero]
        have hiffP : (∃ x : BlockSpace len, (∀ i : Fin (m + 1), j ≤ i.val → x i = 0) ∧ P x = y) ↔
            y ∈ Pref P' j := by
          simp only [Pref, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨x, hx0, rfl⟩
            have hlast : x (Fin.last m) = 0 := hx0 (Fin.last m) (by simpa using hjm)
            refine ⟨initVec x, fun i hi => hx0 i.castSucc hi, ?_⟩
            conv_rhs => rw [← snocVec_init_last x, hlast, hP_snoc, map_zero, add_zero]
          · rintro ⟨x', hx', rfl⟩
            refine ⟨snocVec x' 0, fun i => ?_, ?_⟩
            · refine Fin.lastCases ?_ ?_ i
              · intro _; simp [snocVec]
              · intro i' hi
                simpa [snocVec] using hx' i' hi
            · rw [hP_snoc, map_zero, add_zero]
        rw [hiffQ, hiffP, hQ'_pref j]
      · have hj' : m + 1 ≤ j := by omega
        rw [pref_ge_m Q hj', pref_ge_m P hj', hrange_eq]
    have hQ_ind : ∀ x : BlockSpace len, Q x = 0 → ∀ i : Fin (m + 1), Q (Pi.single i (x i)) = 0 := by
      intro x hx0 i
      rw [← snocVec_init_last x, hQ_snoc] at hx0
      have hu1 : Q' (initVec x) ∈ U := by rw [← hrangeQ']; exact LinearMap.mem_range_self Q' _
      have hw1 : pW (B (x (Fin.last m))) ∈ W := hpW_mem _
      have heq0 : Q' (initVec x) + pW (B (x (Fin.last m))) = 0 + 0 := by simpa using hx0
      obtain ⟨hQ'0, hW0⟩ := hdirect_inj hu1 U.zero_mem hw1 W.zero_mem heq0
      refine Fin.lastCases ?_ ?_ i
      · rw [← embedLast_eq_single]
        change Q (snocVec 0 (x (Fin.last m))) = 0
        rw [hQ_snoc, map_zero, zero_add, hW0]
      · intro i'
        rw [← embedInit_single]
        change Q (snocVec (Pi.single i' (x i'.castSucc)) 0) = 0
        rw [hQ_snoc, map_zero, map_zero, add_zero]
        exact hQ'_ind (initVec x) hQ'0 i'
    refine ⟨Q, hQ_pref, hQ_ind, ?_⟩
    intro a S hS_range
    let a' : (i : Fin m) → (Fin (len' i) → ZMod 2) → ℕ := fun i => a i.castSucc
    let aLast : (Fin (len (Fin.last m)) → ZMod 2) → ℕ := a (Fin.last m)
    let Wfin : Finset (Fin s → ZMod 2) := Finset.univ.image (fun v => pW (B v))
    have hWfin_sub_W : ∀ w ∈ Wfin, w ∈ W := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨v, _, rfl⟩
      exact hpW_mem _
    let Ufin : Finset (Fin s → ZMod 2) := Finset.univ.filter (fun u => u ∈ U)
    let Ssec : (Fin s → ZMod 2) → Finset (Fin s → ZMod 2) :=
      fun w => Ufin.filter (fun u => u + w ∈ S)
    have hSsec_sub_U : ∀ w, Ssec w ⊆ Ufin := fun w => Finset.filter_subset _ _
    have hS_decomp : S = Wfin.biUnion (fun w => (Ssec w).image (· + w)) := by
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_image, Ssec, Finset.mem_filter, Ufin,
        Finset.mem_univ, true_and]
      constructor
      · intro hyS
        obtain ⟨x, hx⟩ := hS_range y hyS
        rw [← snocVec_init_last x, hP_snoc] at hx
        have hpw_y : pW y = pW (B (x (Fin.last m))) := by
          rw [← hx, map_add, hpW_on_U _ (LinearMap.mem_range_self P' _), zero_add]
        refine ⟨pW y, ?_, pU y, ⟨hpU_mem y, by rw [hpU_add_pW]; exact hyS⟩, hpU_add_pW y⟩
        rw [hpw_y]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · rintro ⟨w, _, u, ⟨_, huw⟩, rfl⟩
        exact huw
    have hdisj_biUnion : ∀ (F : (Fin s → ZMod 2) → Finset (Fin s → ZMod 2)),
        (∀ w ∈ Wfin, ∀ u ∈ F w, u ∈ U) →
        (Wfin : Set (Fin s → ZMod 2)).PairwiseDisjoint (fun w => (F w).image (· + w)) := by
      intro F hFU w₁ hw₁ w₂ hw₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro y hy₁ hy₂
      rcases Finset.mem_image.mp hy₁ with ⟨u₁, hu₁, rfl⟩
      rcases Finset.mem_image.mp hy₂ with ⟨u₂, hu₂, heq⟩
      exact hne (hdirect_inj (hFU w₁ hw₁ u₁ hu₁) (hFU w₂ hw₂ u₂ hu₂)
        (hWfin_sub_W w₁ hw₁) (hWfin_sub_W w₂ hw₂) heq.symm).2
    have hS_card : S.card = Wfin.sum (fun w => (Ssec w).card) := by
      conv_lhs => rw [hS_decomp]
      rw [Finset.card_biUnion (hdisj_biUnion Ssec (fun w _ u hu => (Finset.mem_filter.mp (hSsec_sub_U w hu)).2))]
      refine Finset.sum_congr rfl fun w _ => ?_
      exact Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
    have hex_Tsec : ∀ w : Fin s → ZMod 2,
        ∃ Tw : Finset (Fin s → ZMod 2),
          Tw ⊆ Ufin ∧ Tw.card = (Ssec w).card ∧
          ∀ T' : Finset (Fin s → ZMod 2), T' ⊆ Ufin → T'.card = (Ssec w).card →
            Mass Q' a' T' ≤ Mass Q' a' Tw := by
      intro w
      let cands := Ufin.powersetCard (Ssec w).card
      have hcands_ne : cands.Nonempty :=
        ⟨Ssec w, Finset.mem_powersetCard.mpr ⟨hSsec_sub_U w, rfl⟩⟩
      obtain ⟨Tw, hTw_mem, hTw_max⟩ := Finset.exists_max_image cands (fun T' => Mass Q' a' T') hcands_ne
      rcases Finset.mem_powersetCard.mp hTw_mem with ⟨hTw_sub, hTw_card⟩
      refine ⟨Tw, hTw_sub, hTw_card, fun T' hT'_sub hT'_card => ?_⟩
      exact hTw_max T' (Finset.mem_powersetCard.mpr ⟨hT'_sub, hT'_card⟩)
    choose Tsec hTsec using hex_Tsec
    let T : Finset (Fin s → ZMod 2) := Wfin.biUnion (fun w => (Tsec w).image (· + w))
    have hT_range : ∀ y ∈ T, y ∈ LinearMap.range Q := by
      intro y hy
      rcases Finset.mem_biUnion.mp hy with ⟨w, hwWfin, hyimg⟩
      rcases Finset.mem_image.mp hyimg with ⟨u, huTw, rfl⟩
      have huU : u ∈ U := (Finset.mem_filter.mp ((hTsec w).1 huTw)).2
      rw [← hrangeQ'] at huU
      rcases huU with ⟨x', rfl⟩
      rcases Finset.mem_image.mp hwWfin with ⟨v, _, rfl⟩
      exact ⟨snocVec x' v, hQ_snoc x' v⟩
    have hT_card : T.card = S.card := by
      rw [hS_card]
      dsimp only [T]
      rw [Finset.card_biUnion (hdisj_biUnion Tsec (fun w _ u hu => (Finset.mem_filter.mp ((hTsec w).1 hu)).2))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), (hTsec w).2.1]
    have hmass_P : Mass P a S =
        ∑ v : Fin (len (Fin.last m)) → ZMod 2,
          aLast v * Mass P' a' ((Ssec (pW (B v))).image (· + pU (B v))) := by
      unfold Mass
      rw [← Fintype.sum_equiv (snocEquiv len) _ _ (fun _ => rfl), Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      have hprod : (∏ i : Fin (m + 1), a i (snocVec x' v i)) =
          aLast v * ∏ i : Fin m, a' i (x' i) := by
        rw [Fin.prod_univ_castSucc, mul_comm]
        simp [snocVec, a', aLast]
      have hmem_iff : P (snocVec x' v) ∈ S ↔ P' x' ∈ (Ssec (pW (B v))).image (· + pU (B v)) := by
        rw [hP_snoc]
        simp only [Finset.mem_image, Ssec, Finset.mem_filter, Ufin, Finset.mem_univ, true_and]
        constructor
        · intro hmem
          refine ⟨P' x' + pU (B v), ⟨U.add_mem (LinearMap.mem_range_self P' x') (hpU_mem _), ?_⟩, ?_⟩
          · rw [add_assoc, hpU_add_pW]
            exact hmem
          · rw [add_assoc, char2_add_self_vec, add_zero]
        · rintro ⟨u, ⟨_, huw⟩, heq⟩
          have hu_eq : u = P' x' + pU (B v) := by
            have := congrArg (· + pU (B v)) heq
            simpa [add_assoc, char2_add_self_vec] using this
          rw [hu_eq, add_assoc, hpU_add_pW] at huw
          exact huw
      by_cases h : P (snocVec x' v) ∈ S
      · have h' : P' x' ∈ (Ssec (pW (B v))).image (· + pU (B v)) := hmem_iff.mp h
        change (if P (snocVec x' v) ∈ S then ∏ i : Fin (m + 1), a i (snocVec x' v i) else 0) =
          aLast v * if P' x' ∈ (Ssec (pW (B v))).image (· + pU (B v)) then ∏ i : Fin m, a' i (x' i) else 0
        simp only [h, h', ↓reduceIte, hprod]
      · have h' : P' x' ∉ (Ssec (pW (B v))).image (· + pU (B v)) := mt hmem_iff.mpr h
        change (if P (snocVec x' v) ∈ S then ∏ i : Fin (m + 1), a i (snocVec x' v i) else 0) =
          aLast v * if P' x' ∈ (Ssec (pW (B v))).image (· + pU (B v)) then ∏ i : Fin m, a' i (x' i) else 0
        simp only [h, h', ↓reduceIte, mul_zero]
    have hmass_Q : Mass Q a T =
        ∑ v : Fin (len (Fin.last m)) → ZMod 2,
          aLast v * Mass Q' a' (Tsec (pW (B v))) := by
      unfold Mass
      rw [← Fintype.sum_equiv (snocEquiv len) _ _ (fun _ => rfl), Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      have hprod : (∏ i : Fin (m + 1), a i (snocVec x' v i)) =
          aLast v * ∏ i : Fin m, a' i (x' i) := by
        rw [Fin.prod_univ_castSucc, mul_comm]
        simp [snocVec, a', aLast]
      have hmem_iff : Q (snocVec x' v) ∈ T ↔ Q' x' ∈ Tsec (pW (B v)) := by
        rw [hQ_snoc]
        simp only [T, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨w, hwWfin, u, huTw, heq⟩
          have hu1 : u ∈ U := (Finset.mem_filter.mp ((hTsec w).1 huTw)).2
          have hu2 : Q' x' ∈ U := by rw [← hrangeQ']; exact LinearMap.mem_range_self Q' x'
          obtain ⟨hu_eq, hw_eq⟩ := hdirect_inj hu1 hu2 (hWfin_sub_W w hwWfin) (hpW_mem _) heq
          subst hu_eq
          subst hw_eq
          exact huTw
        · intro hmem
          exact ⟨pW (B v), Finset.mem_image_of_mem _ (Finset.mem_univ v), Q' x', hmem, rfl⟩
      by_cases h : Q (snocVec x' v) ∈ T
      · have h' : Q' x' ∈ Tsec (pW (B v)) := hmem_iff.mp h
        simp [snocEquiv, h, h', hprod]
      · have h' : Q' x' ∉ Tsec (pW (B v)) := mt hmem_iff.mpr h
        simp [snocEquiv, h, h']
    have hmass_le : Mass P a S ≤ Mass Q a T := by
      rw [hmass_P, hmass_Q]
      refine Finset.sum_le_sum fun v _ => Nat.mul_le_mul_left _ ?_
      set w := pW (B v)
      set Sshift := (Ssec w).image (· + pU (B v))
      have hSshift_sub : ∀ y ∈ Sshift, y ∈ LinearMap.range P' := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
        exact U.add_mem (Finset.mem_filter.mp (hSsec_sub_U w hu)).2 (hpU_mem _)
      obtain ⟨T', hT'_range, hT'_card, hT'_mass⟩ := hQ'_dom a' Sshift hSshift_sub
      have hT'_sub_U : T' ⊆ Ufin := by
        intro y hy
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
        rw [← hrangeQ']
        exact hT'_range y hy
      have hSshift_card : Sshift.card = (Ssec w).card :=
        Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
      exact le_trans hT'_mass ((hTsec w).2.2 T' hT'_sub_U (hT'_card.trans hSshift_card))
    exact ⟨T, hT_range, hT_card, hmass_le⟩

end PEqualNP.Outside.L_lib_869_aux

theorem PEqualNP.Outside.L_lib_869 :
    ∀ (m s : Nat) (len : Fin m → Nat),
      let F := ZMod 2
      let V := fun i : Fin m => Fin (len i) → F
      let X := (i : Fin m) → V i
      let Y := Fin s → F
      let mass := fun (P : X →ₗ[F] Y) (a : (i : Fin m) → V i → Nat) (S : Finset Y) =>
        ∑ x : X, if P x ∈ S then ∏ i : Fin m, a i (x i) else 0
      let pref := fun (P : X →ₗ[F] Y) (j : Nat) =>
        {y : Y | ∃ x : X, (∀ i : Fin m, j ≤ i.val → x i = 0) ∧ P x = y}
      ∀ P : X →ₗ[F] Y, Function.Surjective P →
        ∃ Q : X →ₗ[F] Y, Function.Surjective Q ∧
          (∀ j : Nat, pref Q j = pref P j) ∧
          (∀ x : X, Q x = 0 → ∀ i : Fin m, Q (Pi.single i (x i)) = 0) ∧
          ∀ (a : (i : Fin m) → V i → Nat) (S : Finset Y), ∃ T : Finset Y,
            T.card = S.card ∧ mass P a S ≤ mass Q a T := by
  intro m s len F V X Y mass pref P hsurj
  obtain ⟨Q, hpref, hind, hdom⟩ := PEqualNP.Outside.L_lib_869_aux.main_ind s m len P
  have hsurjQ : Function.Surjective Q := by
    intro y
    have hP_m : y ∈ PEqualNP.Outside.L_lib_869_aux.Pref P m := by
      rw [PEqualNP.Outside.L_lib_869_aux.pref_ge_m P (le_refl m)]
      exact hsurj y
    rw [← hpref m, PEqualNP.Outside.L_lib_869_aux.pref_ge_m Q (le_refl m)] at hP_m
    exact hP_m
  refine ⟨Q, hsurjQ, hpref, hind, fun a S => ?_⟩
  obtain ⟨T, _, hcard, hmass⟩ := hdom a S (fun y _ => hsurj y)
  exact ⟨T, hcard, hmass⟩
