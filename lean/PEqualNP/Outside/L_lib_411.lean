import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_411

lemma choose_le_choose_half (t r : ℕ) : t.choose r ≤ t.choose (t / 2) := by
  by_cases hrt : r ≤ t
  · have hstep_up : ∀ i : ℕ, i < t / 2 → t.choose i ≤ t.choose (i + 1) := by
      intro i hi
      have hmul := Nat.choose_succ_right_eq t i
      have h1 : i + 1 ≤ t - i := by omega
      have h2 : t.choose i * (i + 1) ≤ t.choose i * (t - i) := Nat.mul_le_mul_left _ h1
      rw [← hmul] at h2
      exact Nat.le_of_mul_le_mul_right h2 (by omega : 0 < i + 1)
    have hmono_le : ∀ a b : ℕ, a ≤ b → b ≤ t / 2 → t.choose a ≤ t.choose b := by
      intro a b hab hb
      induction b with
      | zero =>
        have : a = 0 := by omega
        subst this; exact le_rfl
      | succ b ih =>
        by_cases h : a ≤ b
        · exact le_trans (ih h (by omega)) (hstep_up b (by omega))
        · have : a = b + 1 := by omega
          subst this; exact le_rfl
    by_cases hle : r ≤ t / 2
    · exact hmono_le r (t / 2) hle le_rfl
    · rw [← Nat.choose_symm hrt]
      exact hmono_le (t - r) (t / 2) (by omega) le_rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _

lemma sperner_card_le {t : ℕ} (𝒜 : Finset (Finset (Fin t)))
    (hanti : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ⊆ B → A = B) :
    𝒜.card ≤ t.choose (t / 2) := by
  classical
  let Perms : Finset (Fin t) → Finset (Equiv.Perm (Fin t)) := fun A =>
    Finset.univ.filter (fun σ => ∀ j : Fin t, j.val < A.card → σ j ∈ A)
  have hdisj : Set.PairwiseDisjoint (𝒜 : Set (Finset (Fin t))) Perms := by
    intro A hA B hB hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ hσA hσB
    have hA' := (Finset.mem_filter.mp hσA).2
    have hB' := (Finset.mem_filter.mp hσB).2
    have hsub_of_le : ∀ (X Y : Finset (Fin t)),
        (∀ j : Fin t, j.val < X.card → σ j ∈ X) →
        (∀ j : Fin t, j.val < Y.card → σ j ∈ Y) →
        X.card ≤ Y.card → X ⊆ Y := by
      intro X Y hX hY hle
      let I : Finset (Fin t) := Finset.univ.filter (fun j : Fin t => j.val < X.card)
      have hIcard : I.card = X.card := by
        have hXlt : X.card ≤ t := by
          calc X.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_univ _
            _ = t := by simp
        have hbij : I.card = Fintype.card (Fin X.card) := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin X.card))
            (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => Fin.ext (congrArg (fun z : Fin X.card => z.val) h)) ?_
          intro j _
          refine ⟨⟨j.val, by omega⟩, ?_, Fin.ext rfl⟩
          simp [I, j.isLt]
        simpa using hbij
      have himg_sub_X : I.image σ ⊆ X := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact hX j (Finset.mem_filter.mp hj).2
      have himg_card : (I.image σ).card = X.card := by
        rw [Finset.card_image_of_injective I σ.injective, hIcard]
      have himg_eq_X : I.image σ = X :=
        Finset.eq_of_subset_of_card_le himg_sub_X (by omega)
      rw [← himg_eq_X]
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hY j (lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hle)
    rcases le_total A.card B.card with hle | hle
    · exact hne (hanti A hA B hB (hsub_of_le A B hA' hB' hle))
    · exact hne (hanti B hB A hA (hsub_of_le B A hB' hA' hle)).symm
  have hperm_card : ∀ A : Finset (Fin t),
      (Perms A).card = A.card.factorial * (t - A.card).factorial := by
    intro A
    let I : Finset (Fin t) := Finset.univ.filter (fun j : Fin t => j.val < A.card)
    have hAlt : A.card ≤ t := by
      calc A.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_univ _
        _ = t := by simp
    have hIcard : I.card = A.card := by
      have hbij : I.card = Fintype.card (Fin A.card) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin A.card))
          (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h)) ?_
        intro j _
        exact ⟨⟨j.val, by omega⟩, by simp [I, j.isLt], Fin.ext rfl⟩
      simpa using hbij
    have hIc_card : (Finset.univ \ I).card = t - A.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin, hIcard]
    have hAc_card : (Finset.univ \ A).card = t - A.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]
    have he1_ex : Nonempty ({j : Fin t // j ∈ I} ≃ {x : Fin t // x ∈ A}) := by
      rw [← Fintype.card_eq]
      simp [Fintype.card_coe, hIcard]
    have he2_ex : Nonempty ({j : Fin t // j ∉ I} ≃ {x : Fin t // x ∉ A}) := by
      rw [← Fintype.card_eq]
      have h1 : Fintype.card {j : Fin t // j ∉ I} = (Finset.univ \ I).card := by
        rw [Fintype.card_subtype]; congr 1; ext j; simp
      have h2 : Fintype.card {x : Fin t // x ∉ A} = (Finset.univ \ A).card := by
        rw [Fintype.card_subtype]; congr 1; ext x; simp
      rw [h1, h2, hIc_card, hAc_card]
    obtain ⟨e1⟩ := he1_ex
    obtain ⟨e2⟩ := he2_ex
    -- Base permutation σ0 mapping I to A and Iᶜ to Aᶜ
    let σ0 : Equiv.Perm (Fin t) :=
      { toFun := fun j => if hj : j ∈ I then (e1 ⟨j, hj⟩).val else (e2 ⟨j, hj⟩).val
        invFun := fun x => if hx : x ∈ A then (e1.symm ⟨x, hx⟩).val else (e2.symm ⟨x, hx⟩).val
        left_inv := fun j => by
          dsimp only
          by_cases hj : j ∈ I
          · rw [dif_pos hj, dif_pos (e1 ⟨j, hj⟩).property]
            simp
          · rw [dif_neg hj, dif_neg (e2 ⟨j, hj⟩).property]
            simp
        right_inv := fun x => by
          dsimp only
          by_cases hx : x ∈ A
          · rw [dif_pos hx, dif_pos (e1.symm ⟨x, hx⟩).property]
            simp
          · rw [dif_neg hx, dif_neg (e2.symm ⟨x, hx⟩).property]
            simp }
    have hσ0_iff : ∀ j : Fin t, σ0 j ∈ A ↔ j ∈ I := by
      intro j
      dsimp only [σ0, Equiv.coe_fn_mk]
      by_cases hj : j ∈ I
      · rw [dif_pos hj]; simp [hj, (e1 ⟨j, hj⟩).property]
      · rw [dif_neg hj]; simp [hj, (e2 ⟨j, hj⟩).property]
    -- Bijection between Perms A and Perm {j // j ∈ I} × Perm {j // j ∉ I}
    have hbij : (Perms A).card =
        Fintype.card (Equiv.Perm {j : Fin t // j ∈ I} × Equiv.Perm {j : Fin t // j ∉ I}) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij
        (fun σ hσ =>
          let τ : Equiv.Perm (Fin t) := σ.trans σ0.symm
          have hτI : ∀ j : Fin t, τ j ∈ I ↔ j ∈ I := by
            have hσA := (Finset.mem_filter.mp hσ).2
            have himg_sub : I.image τ ⊆ I := by
              intro y hy
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
              have hjlt : j.val < A.card := (Finset.mem_filter.mp hj).2
              dsimp only [τ, Equiv.trans_apply]
              rw [← hσ0_iff, Equiv.apply_symm_apply]
              exact hσA j hjlt
            have himg_eq : I.image τ = I :=
              Finset.eq_of_subset_of_card_le himg_sub
                (by rw [Finset.card_image_of_injective I τ.injective])
            intro j
            constructor
            · intro hmem
              rw [← himg_eq] at hmem
              obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hmem
              exact (τ.injective heq) ▸ hj'
            · intro hmem
              rw [← himg_eq]; exact Finset.mem_image_of_mem τ hmem
          ({ toFun := fun j => ⟨τ j.val, (hτI j.val).mpr j.property⟩
             invFun := fun j => ⟨τ.symm j.val, by
               have := (hτI (τ.symm j.val)).mp
               rw [Equiv.apply_symm_apply] at this; exact this j.property⟩
             left_inv := fun j => Subtype.ext (τ.symm_apply_apply j.val)
             right_inv := fun j => Subtype.ext (τ.apply_symm_apply j.val) },
           { toFun := fun j => ⟨τ j.val, fun h => j.property ((hτI j.val).mp h)⟩
             invFun := fun j => ⟨τ.symm j.val, fun h => j.property (by
               have := (hτI (τ.symm j.val)).mpr h
               rwa [Equiv.apply_symm_apply] at this)⟩
             left_inv := fun j => Subtype.ext (τ.symm_apply_apply j.val)
             right_inv := fun j => Subtype.ext (τ.apply_symm_apply j.val) }))
        (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro σ1 h1 σ2 h2 heq
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        apply Equiv.ext; intro j
        apply σ0.symm.injective
        change (σ1.trans σ0.symm) j = (σ2.trans σ0.symm) j
        by_cases hj : j ∈ I
        · exact congrArg (fun p => (p ⟨j, hj⟩).val) hfst
        · exact congrArg (fun p => (p ⟨j, hj⟩).val) hsnd
      · rintro ⟨p1, p2⟩ _
        let τ : Equiv.Perm (Fin t) :=
          { toFun := fun j => if hj : j ∈ I then (p1 ⟨j, hj⟩).val else (p2 ⟨j, hj⟩).val
            invFun := fun j => if hj : j ∈ I then (p1.symm ⟨j, hj⟩).val else (p2.symm ⟨j, hj⟩).val
            left_inv := fun j => by
              dsimp only
              by_cases hj : j ∈ I
              · rw [dif_pos hj, dif_pos (p1 ⟨j, hj⟩).property]; simp
              · rw [dif_neg hj, dif_neg (p2 ⟨j, hj⟩).property]; simp
            right_inv := fun j => by
              dsimp only
              by_cases hj : j ∈ I
              · rw [dif_pos hj, dif_pos (p1.symm ⟨j, hj⟩).property]; simp
              · rw [dif_neg hj, dif_neg (p2.symm ⟨j, hj⟩).property]; simp }
        let σ : Equiv.Perm (Fin t) := τ.trans σ0
        have hσ_mem : σ ∈ Perms A := by
          simp only [Perms, Finset.mem_filter, Finset.mem_univ, true_and]
          intro j hjlt
          have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjlt⟩
          dsimp only [σ, Equiv.trans_apply]
          rw [hσ0_iff]
          dsimp only [τ, Equiv.coe_fn_mk]
          rw [dif_pos hjI]
          exact (p1 ⟨j, hjI⟩).property
        refine ⟨σ, hσ_mem, ?_⟩
        apply Prod.ext
        · apply Equiv.ext; rintro ⟨j, hj⟩
          apply Subtype.ext
          change σ0.symm (σ0 (τ j)) = (p1 ⟨j, hj⟩).val
          rw [Equiv.symm_apply_apply]
          dsimp only [τ, Equiv.coe_fn_mk]
          rw [dif_pos hj]
        · apply Equiv.ext; rintro ⟨j, hj⟩
          apply Subtype.ext
          change σ0.symm (σ0 (τ j)) = (p2 ⟨j, hj⟩).val
          rw [Equiv.symm_apply_apply]
          dsimp only [τ, Equiv.coe_fn_mk]
          rw [dif_neg hj]
    rw [hbij, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm]
    have hc1 : Fintype.card {j : Fin t // j ∈ I} = A.card := by simp [Fintype.card_coe, hIcard]
    have hc2 : Fintype.card {j : Fin t // j ∉ I} = t - A.card := by
      have h1 : Fintype.card {j : Fin t // j ∉ I} = (Finset.univ \ I).card := by
        rw [Fintype.card_subtype]; congr 1; ext j; simp
      rw [h1, hIc_card]
    rw [hc1, hc2]
  have hsum_le : 𝒜.card * t.factorial ≤ t.choose (t / 2) * t.factorial := by
    have h1 : 𝒜.card * t.factorial = ∑ _A ∈ 𝒜, t.factorial := by
      rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ A ∈ 𝒜, t.factorial ≤ ∑ A ∈ 𝒜, t.choose (t / 2) * (Perms A).card := by
      refine Finset.sum_le_sum fun A _ => ?_
      have hAlt : A.card ≤ t := by
        calc A.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_univ _
          _ = t := by simp
      rw [hperm_card A]
      have hch := Nat.choose_mul_factorial_mul_factorial hAlt
      have hmid := choose_le_choose_half t A.card
      calc t.factorial = t.choose A.card * (A.card.factorial * (t - A.card).factorial) := by
            rw [← mul_assoc]; exact hch.symm
        _ ≤ t.choose (t / 2) * (A.card.factorial * (t - A.card).factorial) :=
            Nat.mul_le_mul_right _ hmid
    have h3 : ∑ A ∈ 𝒜, t.choose (t / 2) * (Perms A).card =
        t.choose (t / 2) * (𝒜.biUnion Perms).card := by
      rw [← Finset.mul_sum, Finset.card_biUnion hdisj]
    have h4 : (𝒜.biUnion Perms).card ≤ t.factorial := by
      calc (𝒜.biUnion Perms).card ≤ (Finset.univ : Finset (Equiv.Perm (Fin t))).card :=
            Finset.card_le_univ _
        _ = t.factorial := by simp [Fintype.card_perm]
    calc 𝒜.card * t.factorial = ∑ _A ∈ 𝒜, t.factorial := h1
      _ ≤ ∑ A ∈ 𝒜, t.choose (t / 2) * (Perms A).card := h2
      _ = t.choose (t / 2) * (𝒜.biUnion Perms).card := h3
      _ ≤ t.choose (t / 2) * t.factorial := Nat.mul_le_mul_left _ h4
  exact Nat.le_of_mul_le_mul_right hsum_le (Nat.factorial_pos t)

lemma card_subsets_le_k {X : Type*} [Fintype X] [DecidableEq X] (k : ℕ) :
    ((Finset.univ : Finset (Finset X)).filter (fun S => S.card ≤ k)).card ≤
      (Fintype.card X + 1) ^ k := by
  let mkSet : (Fin k → Option X) → Finset X := fun g =>
    Finset.univ.biUnion (fun i => (g i).toFinset)
  have hsub : (Finset.univ : Finset (Finset X)).filter (fun S => S.card ≤ k) ⊆
      Finset.univ.image mkSet := by
    intro S hS
    have hcard : S.card ≤ k := (Finset.mem_filter.mp hS).2
    let L := S.toList
    have hlen : L.length = S.card := Finset.length_toList S
    let g : Fin k → Option X := fun i => L[i.val]?
    refine Finset.mem_image.mpr ⟨g, Finset.mem_univ g, ?_⟩
    ext x
    simp only [mkSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset, g]
    constructor
    · rintro ⟨i, hi⟩
      have hmemL : x ∈ L := List.mem_of_getElem? hi
      exact Finset.mem_toList.mp hmemL
    · intro hx
      have hmemL : x ∈ L := Finset.mem_toList.mpr hx
      obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hmemL
      refine ⟨⟨i, by omega⟩, ?_⟩
      simp [List.getElem?_eq_getElem hi_lt, hi_eq]
  calc ((Finset.univ : Finset (Finset X)).filter (fun S => S.card ≤ k)).card
      ≤ (Finset.univ.image mkSet).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin k → Option X)).card := Finset.card_image_le
    _ = (Fintype.card X + 1) ^ k := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

lemma exists_separating_hash {w k : ℕ} :
    let X := Fin w → Bool
    ∃ F : Fin (2 * (k + 1) * ((k + 1) * (w + 1) + 1)) → Finset X,
      ∀ (a : X) (S : Finset X), a ∉ S → S.card ≤ k →
        ∃ j, a ∈ F j ∧ Disjoint (F j) S := by
  classical
  intro X
  set B := 2 * (k + 1)
  set m := (k + 1) * (w + 1) + 1
  have hB_pos : 0 < B := by omega
  haveI : NeZero B := ⟨by omega⟩
  have hm_pos : 0 < m := by omega
  let Bad1 : X → Finset X → Finset (X → ZMod B) := fun a S =>
    Finset.univ.filter (fun f => ∃ y ∈ S, f y = f a)
  let M := Fintype.card (X → ZMod B)
  have hM_pos : 0 < M := Fintype.card_pos
  have hBad1_bound : ∀ (a : X) (S : Finset X), a ∉ S → S.card ≤ k →
      2 * (Bad1 a S).card < M := by
    intro a S ha hS
    have hsub : Bad1 a S ⊆ S.biUnion (fun y => Finset.univ.filter (fun f : X → ZMod B => f y = f a)) := by
      intro f hf
      obtain ⟨y, hy, hfy⟩ := (Finset.mem_filter.mp hf).2
      exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfy⟩⟩
    have heq_card : ∀ y ∈ S,
        B * (Finset.univ.filter (fun f : X → ZMod B => f y = f a)).card = M := by
      intro y hy
      have hya : y ≠ a := fun h => ha (h ▸ hy)
      have hfiber : ∀ c : ZMod B,
          (Finset.univ.filter (fun f : X → ZMod B => f a - f y = c)).card =
          (Finset.univ.filter (fun f : X → ZMod B => f y = f a)).card := by
        intro c
        refine Finset.card_bij (fun f _ x => if x = a then f x - c else f x) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg hya, ↓reduceIte] at hf ⊢
          have := congrArg (fun z => z + f y) hf
          have hf' : f a = c + f y := by simpa [sub_add_cancel] using this
          rw [hf']; abel
        · intro f1 _ f2 _ h
          funext x
          have hx := congrFun h x
          by_cases hxa : x = a
          · subst hxa; simp only [↓reduceIte] at hx; exact sub_left_inj.mp hx
          · simp only [if_neg hxa] at hx; exact hx
        · intro g hg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
          refine ⟨fun x => if x = a then g x + c else g x, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg hya, ↓reduceIte, hg]
            abel
          · funext x; by_cases hxa : x = a <;> simp [hxa]
      have hpart : (Finset.univ : Finset (X → ZMod B)).card =
          ∑ c : ZMod B, (Finset.univ.filter (fun f : X → ZMod B => f a - f y = c)).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise
          (f := fun f : X → ZMod B => f a - f y) (s := Finset.univ) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _))
      simp_rw [hfiber] at hpart
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Finset.card_univ] at hpart
      have hZB : Fintype.card (ZMod B) = B := ZMod.card B
      rw [hZB] at hpart
      exact hpart.symm
    have hB_le : B * (Bad1 a S).card ≤ k * M := by
      calc B * (Bad1 a S).card
          ≤ B * (S.biUnion (fun y => Finset.univ.filter (fun f : X → ZMod B => f y = f a))).card :=
            Nat.mul_le_mul_left B (Finset.card_le_card hsub)
        _ ≤ B * ∑ y ∈ S, (Finset.univ.filter (fun f : X → ZMod B => f y = f a)).card :=
            Nat.mul_le_mul_left B Finset.card_biUnion_le
        _ = ∑ y ∈ S, B * (Finset.univ.filter (fun f : X → ZMod B => f y = f a)).card :=
            Finset.mul_sum _ _ _
        _ = ∑ _y ∈ S, M := Finset.sum_congr rfl heq_card
        _ = S.card * M := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ k * M := Nat.mul_le_mul_right M hS
    have hstrict : B * (2 * (Bad1 a S).card) < B * M := by
      have h1 : B * (2 * (Bad1 a S).card) = 2 * (B * (Bad1 a S).card) := by ring
      have h2 : 2 * (k * M) < B * M := by
        have hlt : 2 * k < B := by omega
        calc 2 * (k * M) = (2 * k) * M := by ring
          _ < B * M := Nat.mul_lt_mul_of_pos_right hlt hM_pos
      calc B * (2 * (Bad1 a S).card) = 2 * (B * (Bad1 a S).card) := h1
        _ ≤ 2 * (k * M) := Nat.mul_le_mul_left 2 hB_le
        _ < B * M := h2
    exact Nat.lt_of_mul_lt_mul_left hstrict
  let BadAll : X → Finset X → Finset (Fin m → X → ZMod B) := fun a S =>
    Finset.univ.filter (fun h => ∀ i : Fin m, h i ∈ Bad1 a S)
  have hBadAll_card : ∀ (a : X) (S : Finset X), (BadAll a S).card = (Bad1 a S).card ^ m := by
    intro a S
    have hbij : (BadAll a S).card = Fintype.card (Fin m → {f : X → ZMod B // f ∈ Bad1 a S}) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun h hh i => ⟨h i, (Finset.mem_filter.mp hh).2 i⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ heq => funext fun i => congrArg Subtype.val (congrFun heq i)) ?_
      intro g _
      exact ⟨fun i => (g i).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (g i).property⟩,
        funext fun i => Subtype.ext rfl⟩
    rw [hbij, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  let Pairs : Finset (X × Finset X) :=
    ((Finset.univ : Finset X) ×ˢ ((Finset.univ : Finset (Finset X)).filter (fun S => S.card ≤ k))).filter
      (fun p => p.1 ∉ p.2)
  have hPairs_ne : Pairs.Nonempty := by
    refine ⟨(fun _ => false, ∅), ?_⟩
    simp [Pairs]
  have hPairs_card : Pairs.card ≤ 2 ^ m := by
    have hXcard : Fintype.card X = 2 ^ w := by simp [X]
    have h1 : Pairs.card ≤ 2 ^ w * (2 ^ w + 1) ^ k := by
      calc Pairs.card
          ≤ ((Finset.univ : Finset X) ×ˢ
              ((Finset.univ : Finset (Finset X)).filter (fun S => S.card ≤ k))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = (Finset.univ : Finset X).card *
              ((Finset.univ : Finset (Finset X)).filter (fun S => S.card ≤ k)).card :=
            Finset.card_product _ _
        _ ≤ 2 ^ w * (2 ^ w + 1) ^ k := by
            rw [Finset.card_univ, hXcard]
            exact Nat.mul_le_mul_left _ (by rw [← hXcard]; exact card_subsets_le_k k)
    have h2 : 2 ^ w + 1 ≤ 2 ^ (w + 1) := by
      have : 1 ≤ 2 ^ w := Nat.one_le_pow w 2 (by omega)
      rw [pow_succ]; omega
    have h3 : 2 ^ w * (2 ^ w + 1) ^ k ≤ 2 ^ (w + k * (w + 1)) := by
      calc 2 ^ w * (2 ^ w + 1) ^ k
          ≤ 2 ^ w * (2 ^ (w + 1)) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 k)
        _ = 2 ^ w * 2 ^ ((w + 1) * k) := by rw [← pow_mul]
        _ = 2 ^ (w + (w + 1) * k) := by rw [← pow_add]
        _ = 2 ^ (w + k * (w + 1)) := by rw [mul_comm k (w + 1)]
    have h4 : w + k * (w + 1) ≤ m := by
      have : (k + 1) * (w + 1) = k * (w + 1) + (w + 1) := by ring
      omega
    exact le_trans h1 (le_trans h3 (Nat.pow_le_pow_right (by omega) h4))
  have hUnion_lt : (Pairs.biUnion (fun p => BadAll p.1 p.2)).card <
      (Finset.univ : Finset (Fin m → X → ZMod B)).card := by
    have htot : (Finset.univ : Finset (Fin m → X → ZMod B)).card = M ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [htot]
    have hmul_lt : 2 ^ m * (Pairs.biUnion (fun p => BadAll p.1 p.2)).card < 2 ^ m * M ^ m := by
      have hterm_lt : ∀ p ∈ Pairs, 2 ^ m * (BadAll p.1 p.2).card < M ^ m := by
        intro p hp
        simp only [Pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
        rw [hBadAll_card, ← mul_pow]
        exact Nat.pow_lt_pow_left (hBad1_bound p.1 p.2 hp.2 hp.1) (by omega)
      calc 2 ^ m * (Pairs.biUnion (fun p => BadAll p.1 p.2)).card
          ≤ 2 ^ m * ∑ p ∈ Pairs, (BadAll p.1 p.2).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ p ∈ Pairs, 2 ^ m * (BadAll p.1 p.2).card := Finset.mul_sum _ _ _
        _ < ∑ _p ∈ Pairs, M ^ m := Finset.sum_lt_sum_of_nonempty hPairs_ne hterm_lt
        _ = Pairs.card * M ^ m := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ m * M ^ m := Nat.mul_le_mul_right _ hPairs_card
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  have hex_good : ∃ h : Fin m → X → ZMod B, h ∉ Pairs.biUnion (fun p => BadAll p.1 p.2) := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset (Fin m → X → ZMod B)) ⊆
        Pairs.biUnion (fun p => BadAll p.1 p.2) := fun h _ => hall h
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨h, hh⟩ := hex_good
  let F : Fin (B * m) → Finset X := fun idx =>
    Finset.univ.filter (fun x : X =>
      h ⟨idx.val / B, Nat.div_lt_of_lt_mul idx.isLt⟩ x =
        ((idx.val % B : ℕ) : ZMod B))
  refine ⟨F, fun a S ha hS => ?_⟩
  have hp : (a, S) ∈ Pairs := by simp [Pairs, ha, hS]
  have hnotbad : h ∉ BadAll a S := fun hb => hh (Finset.mem_biUnion.mpr ⟨(a, S), hp, hb⟩)
  simp only [BadAll, Finset.mem_filter, Finset.mem_univ, true_and] at hnotbad
  have hex_i : ∃ i : Fin m, h i ∉ Bad1 a S := by
    by_contra hall; apply hnotbad; intro i; by_contra hni; exact hall ⟨i, hni⟩
  obtain ⟨i, hi⟩ := hex_i
  simp only [Bad1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  let c : ℕ := (h i a).val
  have hclt : c < B := ZMod.val_lt (h i a)
  have hidx_lt : i.val * B + c < B * m := by
    have : i.val + 1 ≤ m := i.isLt
    calc i.val * B + c < i.val * B + B := by omega
      _ = (i.val + 1) * B := by ring
      _ ≤ m * B := Nat.mul_le_mul_right B this
      _ = B * m := mul_comm m B
  let idx : Fin (B * m) := ⟨i.val * B + c, hidx_lt⟩
  have hdiv : idx.val / B = i.val := by
    dsimp only [idx]
    rw [mul_comm i.val B, Nat.mul_add_div hB_pos, Nat.div_eq_of_lt hclt, Nat.add_zero]
  have hmod : idx.val % B = c := by
    dsimp only [idx]
    rw [mul_comm i.val B, Nat.mul_add_mod, Nat.mod_eq_of_lt hclt]
  have hFi : ∀ x : X, x ∈ F idx ↔ h i x = h i a := by
    intro x
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    have hi_eq : (⟨idx.val / B, Nat.div_lt_of_lt_mul idx.isLt⟩ : Fin m) = i :=
      Fin.ext hdiv
    rw [hi_eq, hmod]
    simp only [c, ZMod.natCast_zmod_val]
  refine ⟨idx, (hFi a).mpr rfl, Finset.disjoint_left.mpr fun y hyF hyS => ?_⟩
  exact hi ⟨y, hyS, (hFi y).mp hyF⟩

end PEqualNP.Outside.L_lib_411

open PEqualNP.Outside.L_lib_411 in
theorem PEqualNP.Outside.L_lib_411 : ∀ w : ℕ,
  let X := Fin w → Bool
  let separates := fun (k t : ℕ) (F : Fin t → Finset X) =>
    ∀ (a : X) (S : Finset X), a ∉ S → S.card ≤ k →
      ∃ j : Fin t, a ∈ F j ∧ Disjoint (F j) S
  let exact := fun (k t : ℕ) (F : Fin t → Finset X) =>
    ∀ (R : X → X → Bool) (a : X),
      (((Finset.univ : Finset X).filter (fun u => R u a)).card ≤ k ∨
       ((Finset.univ : Finset X).filter (fun v => R a v)).card ≤ k) →
      (R a a = true ↔ ∀ j : Fin t, a ∈ F j →
        (∃ b ∈ F j, R b a = true) ∧ (∃ c ∈ F j, R a c = true))
  (∀ k t : ℕ, ∀ F : Fin t → Finset X, exact k t F ↔ separates k t F) ∧
    (∀ k : ℕ, ∃ (t : ℕ) (F : Fin t → Finset X),
      t ≤ min (2 ^ w) (2 * (k + 1) * ((k + 1) * (w + 1) + 1)) ∧ exact k t F) ∧
    ∀ t : ℕ, (∃ F : Fin t → Finset X, exact 1 t F) ↔
      0 < t ∧ 2 ^ w ≤ t.choose (t / 2) := by
  classical
  intro w X separates exact
  have hpart1 : ∀ k t : ℕ, ∀ F : Fin t → Finset X, exact k t F ↔ separates k t F := by
    intro k t F
    constructor
    · intro hex a S ha hS
      let R : X → X → Bool := fun u v => decide ((u ∈ S ∧ v = a) ∨ (u = a ∧ v ∈ S))
      have hRaa : R a a = false := by simp [R, ha]
      have hRin : Finset.univ.filter (fun u : X => R u a = true) = S := by
        ext u; simp [R, ha]
      have hdeg : (Finset.univ.filter (fun u : X => R u a = true)).card ≤ k ∨
          (Finset.univ.filter (fun v : X => R a v = true)).card ≤ k :=
        Or.inl (by rw [hRin]; exact hS)
      have hiff := hex R a hdeg
      have hnot : ¬ ∀ j : Fin t, a ∈ F j →
          (∃ b ∈ F j, R b a = true) ∧ (∃ c ∈ F j, R a c = true) := by
        intro hall
        have ht := hiff.mpr hall
        rw [hRaa] at ht; exact Bool.noConfusion ht
      have hex_j : ∃ j : Fin t, a ∈ F j ∧
          ¬ ((∃ b ∈ F j, R b a = true) ∧ (∃ c ∈ F j, R a c = true)) := by
        by_contra hno; apply hnot; intro j hj; by_contra hc; exact hno ⟨j, hj, hc⟩
      obtain ⟨j, haj, hbad⟩ := hex_j
      refine ⟨j, haj, Finset.disjoint_left.mpr fun x hxF hxS => ?_⟩
      apply hbad
      exact ⟨⟨x, hxF, by simp [R, hxS]⟩, ⟨x, hxF, by simp [R, hxS]⟩⟩
    · intro hsep R a hdeg
      constructor
      · intro ha j haj; exact ⟨⟨a, haj, ha⟩, ⟨a, haj, ha⟩⟩
      · intro hall
        by_contra hfalse
        have hRaa : R a a = false := by cases h : R a a <;> simp_all
        rcases hdeg with h1 | h2
        · let S := Finset.univ.filter (fun u : X => R u a = true)
          have haS : a ∉ S := by simp [S, hRaa]
          obtain ⟨j, haj, hdisj⟩ := hsep a S haS h1
          obtain ⟨b, hbF, hba⟩ := (hall j haj).1
          exact Finset.disjoint_left.mp hdisj hbF (by simp [S, hba])
        · let S := Finset.univ.filter (fun v : X => R a v = true)
          have haS : a ∉ S := by simp [S, hRaa]
          obtain ⟨j, haj, hdisj⟩ := hsep a S haS h2
          obtain ⟨c, hcF, hac⟩ := (hall j haj).2
          exact Finset.disjoint_left.mp hdisj hcF (by simp [S, hac])
  refine ⟨hpart1, ?_, ?_⟩
  · -- Part 2: existence of small separating family
    intro k
    by_cases hcmp : 2 ^ w ≤ 2 * (k + 1) * ((k + 1) * (w + 1) + 1)
    · have hcardX : Fintype.card X = 2 ^ w := by simp [X]
      let e : Fin (2 ^ w) ≃ X := (Fintype.equivFinOfCardEq hcardX).symm
      refine ⟨2 ^ w, fun j => {e j}, by omega, (hpart1 k (2 ^ w) _).mpr ?_⟩
      intro a S ha _
      refine ⟨e.symm a, by simp, ?_⟩
      rw [Finset.disjoint_singleton_left]; simp [ha]
    · obtain ⟨F, hF⟩ := exists_separating_hash (w := w) (k := k)
      refine ⟨2 * (k + 1) * ((k + 1) * (w + 1) + 1), F, by omega, (hpart1 k _ F).mpr hF⟩
  · -- Part 3: k = 1 exact Sperner characterization
    intro t
    constructor
    · rintro ⟨F, hF⟩
      have hsep := (hpart1 1 t F).mp hF
      have ht_pos : 0 < t := by
        obtain ⟨j, _, _⟩ := hsep (fun _ => false) ∅ (by simp) (by simp)
        exact Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 j)
      refine ⟨ht_pos, ?_⟩
      let col : X → Finset (Fin t) := fun a => Finset.univ.filter (fun j => a ∈ F j)
      have hcol_sub : ∀ a b : X, col a ⊆ col b → a = b := by
        intro a b hsub
        by_contra hab
        obtain ⟨j, haj, hdisj⟩ := hsep a {b} (by simp [hab]) (by simp)
        have hja : j ∈ col a := by simp [col, haj]
        have hjb : j ∈ col b := hsub hja
        have hbF : b ∈ F j := (Finset.mem_filter.mp hjb).2
        exact Finset.disjoint_left.mp hdisj hbF (Finset.mem_singleton_self b)
      have hcol_inj : Function.Injective col := fun a b h => hcol_sub a b (by rw [h])
      let 𝒜 : Finset (Finset (Fin t)) := Finset.univ.image col
      have hanti : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ⊆ B → A = B := by
        intro A hA B hB hsub
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
        rw [hcol_sub a b hsub]
      have hcardA : 𝒜.card = 2 ^ w := by
        rw [Finset.card_image_of_injective Finset.univ hcol_inj, Finset.card_univ]
        simp [X]
      rw [← hcardA]
      exact sperner_card_le 𝒜 hanti
    · rintro ⟨ht_pos, hle⟩
      let r := (t + 1) / 2
      have hr_pos : 1 ≤ r := by omega
      have hr_le : r ≤ t := by omega
      have hsymm : t.choose r = t.choose (t / 2) := by
        rw [← Nat.choose_symm hr_le]
        congr 1; omega
      let Mid : Finset (Finset (Fin t)) := (Finset.univ : Finset (Fin t)).powersetCard r
      have hMid_card : Mid.card = t.choose (t / 2) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hsymm]
      have hcardX : Fintype.card X = 2 ^ w := by simp [X]
      let eX : X ≃ Fin (2 ^ w) := Fintype.equivFinOfCardEq hcardX
      let eM : Fin (t.choose (t / 2)) ≃ {A : Finset (Fin t) // A ∈ Mid} :=
        (Fintype.equivFinOfCardEq (by simp [Fintype.card_coe, hMid_card])).symm
      let col : X → Finset (Fin t) := fun a =>
        (eM ⟨(eX a).val, lt_of_lt_of_le (eX a).isLt hle⟩).val
      have hcol_mem : ∀ a : X, col a ∈ Mid := fun a => (eM _).property
      have hcol_card : ∀ a : X, (col a).card = r := fun a =>
        (Finset.mem_powersetCard.mp (hcol_mem a)).2
      have hcol_inj : Function.Injective col := by
        intro a b h
        have h1 : eM ⟨(eX a).val, lt_of_lt_of_le (eX a).isLt hle⟩ =
            eM ⟨(eX b).val, lt_of_lt_of_le (eX b).isLt hle⟩ := Subtype.ext h
        have h2 := eM.injective h1
        have hval : (eX a).val = (eX b).val := congrArg (fun z : Fin (t.choose (t / 2)) => z.val) h2
        exact eX.injective (Fin.ext hval)
      let F : Fin t → Finset X := fun j => Finset.univ.filter (fun a : X => j ∈ col a)
      refine ⟨F, (hpart1 1 t F).mpr ?_⟩
      intro a S ha hS
      by_cases hS0 : S = ∅
      · subst hS0
        have hne : (col a).Nonempty := Finset.card_pos.mp (by rw [hcol_card a]; omega)
        obtain ⟨j, hj⟩ := hne
        exact ⟨j, by simp [F, hj], Finset.disjoint_empty_right _⟩
      · have hS1 : S.card = 1 := by
          have : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
          omega
        obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hS1
        have hab : a ≠ b := fun h => ha (by simp [h])
        have hne_col : col a ≠ col b := fun h => hab (hcol_inj h)
        have hnot_sub : ¬ (col a ⊆ col b) := fun hsub =>
          hne_col (Finset.eq_of_subset_of_card_le hsub (by rw [hcol_card a, hcol_card b]))
        obtain ⟨j, hja, hjb⟩ := Finset.not_subset.mp hnot_sub
        refine ⟨j, by simp [F, hja], ?_⟩
        rw [Finset.disjoint_singleton_right]
        simp [F, hjb]
