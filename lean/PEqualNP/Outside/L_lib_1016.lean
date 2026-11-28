import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1016_aux

open scoped BigOperators

lemma mass_eq_list_sum {k : ℕ} (rows : List (Finset (Fin k) × Bool))
    (predicate : Finset (Fin k) → Prop) :
    ((rows.filter (fun x => x.2 && @decide (predicate x.1) (Classical.propDecidable _))).length : Int) -
      ((rows.filter (fun x => !x.2 && @decide (predicate x.1) (Classical.propDecidable _))).length : Int) =
    (rows.map (fun x => if @decide (predicate x.1) (Classical.propDecidable _)
      then (if x.2 then (1 : Int) else -1) else 0)).sum := by
  induction rows with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hb : hd.2 <;> by_cases hp : predicate hd.1 <;>
    simp [hb, hp] <;> omega

lemma covers_eq_sum_exact {k : ℕ} (rows : List (Finset (Fin k) × Bool)) (T : Finset (Fin k)) :
    ((rows.filter (fun x => x.2 && @decide (T ⊆ x.1) (Classical.propDecidable _))).length : Int) -
      ((rows.filter (fun x => !x.2 && @decide (T ⊆ x.1) (Classical.propDecidable _))).length : Int) =
    ∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
      (((rows.filter (fun x => x.2 && @decide (x.1 = A) (Classical.propDecidable _))).length : Int) -
        ((rows.filter (fun x => !x.2 && @decide (x.1 = A) (Classical.propDecidable _))).length : Int)) := by
  rw [mass_eq_list_sum]
  have hrhs : (∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
      (((rows.filter (fun x => x.2 && @decide (x.1 = A) (Classical.propDecidable _))).length : Int) -
        ((rows.filter (fun x => !x.2 && @decide (x.1 = A) (Classical.propDecidable _))).length : Int))) =
      ∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
        (rows.map (fun x => if @decide (x.1 = A) (Classical.propDecidable _)
          then (if x.2 then (1 : Int) else -1) else 0)).sum :=
    Finset.sum_congr rfl (fun A _ => mass_eq_list_sum rows (fun B => B = A))
  rw [hrhs]
  clear hrhs
  induction rows with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih]
    congr 1
    have hsum_hd : (∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
        if @decide (hd.1 = A) (Classical.propDecidable _)
        then (if hd.2 then (1 : Int) else -1) else 0) =
        if @decide (T ⊆ hd.1) (Classical.propDecidable _)
        then (if hd.2 then (1 : Int) else -1) else 0 := by
      by_cases hT : T ⊆ hd.1
      · have hmem : hd.1 ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
        rw [Finset.sum_eq_single hd.1]
        · simp [hT]
        · intro A _ hne
          have hne' : hd.1 ≠ A := hne.symm
          simp [hne']
        · intro hnot; exact (hnot hmem).elim
      · simp only [hT, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine Finset.sum_eq_zero (fun A hA => ?_)
        have hTA : T ⊆ A := (Finset.mem_filter.mp hA).2
        have hne : hd.1 ≠ A := fun heq => hT (heq ▸ hTA)
        simp [hne]
    exact hsum_hd.symm

lemma alt_sum_supersets {k : ℕ} (T : Finset (Fin k)) (hT : T ≠ Finset.univ) :
    (∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
      (-1 : Int) ^ (k - A.card)) = 0 := by
  have hex : ∃ x0 : Fin k, x0 ∉ T := by
    by_contra hall
    push_neg at hall
    exact hT (Finset.eq_univ_iff_forall.mpr hall)
  rcases hex with ⟨x0, hx0⟩
  let S : Finset (Finset (Fin k)) := (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A)
  let τ : Finset (Fin k) → Finset (Fin k) := fun A => if x0 ∈ A then A.erase x0 else insert x0 A
  have hτ_inv : ∀ A, τ (τ A) = A := by
    intro A
    by_cases h : x0 ∈ A
    · simp only [τ, h, ↓reduceIte, Finset.notMem_erase, Finset.insert_erase h]
    · simp only [τ, h, ↓reduceIte, Finset.mem_insert_self, Finset.erase_insert h]
  have hτ_mem : ∀ A ∈ S, τ A ∈ S := by
    intro A hA
    have hTA : T ⊆ A := (Finset.mem_filter.mp hA).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases h : x0 ∈ A
    · simp only [τ, h, ↓reduceIte]
      intro y hy
      exact Finset.mem_erase.mpr ⟨fun heq => hx0 (heq ▸ hy), hTA hy⟩
    · simp only [τ, h, ↓reduceIte]
      exact hTA.trans (Finset.subset_insert x0 A)
  have hτ_sign : ∀ A : Finset (Fin k), (-1 : Int) ^ (k - (τ A).card) = - ((-1 : Int) ^ (k - A.card)) := by
    intro A
    have hle : A.card ≤ k := by simpa [Fintype.card_fin] using Finset.card_le_univ A
    by_cases h : x0 ∈ A
    · have hpos : 1 ≤ A.card := Finset.card_pos.mpr ⟨x0, h⟩
      have hcard : (τ A).card = A.card - 1 := by simp only [τ, h, ↓reduceIte, Finset.card_erase_of_mem h]
      have hsub : k - (τ A).card = (k - A.card) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    · have hlt : A.card < k := by
        have h1 : (insert x0 A).card ≤ k := by simpa [Fintype.card_fin] using Finset.card_le_univ (insert x0 A)
        rw [Finset.card_insert_of_notMem h] at h1
        omega
      have hcard : (τ A).card = A.card + 1 := by simp only [τ, h, ↓reduceIte, Finset.card_insert_of_notMem h]
      have hsub : k - A.card = (k - (τ A).card) + 1 := by omega
      rw [hsub, pow_succ]
      ring
  have hsum_eq : (∑ A ∈ S, (-1 : Int) ^ (k - A.card)) =
      ∑ A ∈ S, (-1 : Int) ^ (k - (τ A).card) := by
    refine Finset.sum_bij (fun A _ => τ A) hτ_mem ?_ ?_ (fun A _ => by rw [hτ_inv A])
    · intro A₁ _ A₂ _ h
      have := congrArg τ h
      rwa [hτ_inv, hτ_inv] at this
    · intro A hA
      exact ⟨τ A, hτ_mem A hA, hτ_inv A⟩
  have hneg : (∑ A ∈ S, (-1 : Int) ^ (k - (τ A).card)) = - ∑ A ∈ S, (-1 : Int) ^ (k - A.card) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun A _ => hτ_sign A)
  have hself : (∑ A ∈ S, (-1 : Int) ^ (k - A.card)) = - ∑ A ∈ S, (-1 : Int) ^ (k - A.card) :=
    hsum_eq.trans hneg
  linarith

lemma high_card_ge {k d : ℕ} (hdk : d < k) :
    2 ^ (k - (d + 1)) ≤ ((Finset.univ : Finset (Fin k)).powerset.filter (fun T => d < T.card)).card := by
  let S0 : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => i.val < d + 1)
  have hS0_card : S0.card = d + 1 := by
    let emb : Fin (d + 1) → Fin k := fun i => ⟨i.val, by omega⟩
    have hemb_inj : Function.Injective emb := fun i₁ i₂ h => Fin.ext (congrArg (Fin.val (n := k)) h)
    have heq : S0 = (Finset.univ : Finset (Fin (d + 1))).image emb := by
      ext j
      simp only [S0, emb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj; exact ⟨⟨j.val, hj⟩, rfl⟩
      · rintro ⟨i, rfl⟩; exact i.isLt
    rw [heq, Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fin]
  let rest : Finset (Fin k) := Finset.univ \ S0
  have hrest_card : rest.card = k - (d + 1) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hS0_card]
  let f : Finset (Fin k) → Finset (Fin k) := fun R => S0 ∪ R
  have hf_mem : ∀ R ∈ rest.powerset, f R ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun T => d < T.card) := by
    intro R _
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hle : S0.card ≤ (S0 ∪ R).card := Finset.card_le_card Finset.subset_union_left
    change d < (S0 ∪ R).card
    omega
  have hf_inj : Set.InjOn f (rest.powerset : Set (Finset (Fin k))) := by
    intro R₁ hR₁ R₂ hR₂ heq
    change S0 ∪ R₁ = S0 ∪ R₂ at heq
    have h1 : R₁ ⊆ rest := Finset.mem_powerset.mp hR₁
    have h2 : R₂ ⊆ rest := Finset.mem_powerset.mp hR₂
    ext x
    constructor
    · intro hx
      have hnotS0 : x ∉ S0 := (Finset.mem_sdiff.mp (h1 hx)).2
      have hmem : x ∈ S0 ∪ R₂ := heq ▸ Finset.mem_union_right S0 hx
      rcases Finset.mem_union.mp hmem with hS | hR
      · exact (hnotS0 hS).elim
      · exact hR
    · intro hx
      have hnotS0 : x ∉ S0 := (Finset.mem_sdiff.mp (h2 hx)).2
      have hmem : x ∈ S0 ∪ R₁ := heq.symm ▸ Finset.mem_union_right S0 hx
      rcases Finset.mem_union.mp hmem with hS | hR
      · exact (hnotS0 hS).elim
      · exact hR
  calc
    2 ^ (k - (d + 1)) = rest.powerset.card := by rw [Finset.card_powerset, hrest_card]
    _ = (rest.powerset.image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ ((Finset.univ : Finset (Fin k)).powerset.filter (fun T => d < T.card)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)

lemma natAbs_mass_le_count {k : ℕ} (rows : List (Finset (Fin k) × Bool)) (T : Finset (Fin k)) :
    (((rows.filter (fun x => x.2 && @decide (x.1 = T) (Classical.propDecidable _))).length : Int) -
      ((rows.filter (fun x => !x.2 && @decide (x.1 = T) (Classical.propDecidable _))).length : Int)).natAbs ≤
    (rows.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length := by
  induction rows with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hb : hd.2 <;> by_cases hp : hd.1 = T <;>
    simp [hb, hp] <;> omega

lemma sum_filter_eq_le_length {k : ℕ} (S : Finset (Finset (Fin k)))
    (rows : List (Finset (Fin k) × Bool)) :
    (∑ T ∈ S, (rows.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length) ≤ rows.length := by
  induction rows with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.length_cons]
    have hsplit : (∑ T ∈ S, (if @decide (hd.1 = T) (Classical.propDecidable _)
        then (tl.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length + 1
        else (tl.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length)) =
        (∑ T ∈ S, (tl.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length) +
        (∑ T ∈ S, if @decide (hd.1 = T) (Classical.propDecidable _) then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      split_ifs <;> omega
    have hmap : (∑ T ∈ S, (if @decide (hd.1 = T) (Classical.propDecidable _) = true
        then hd :: tl.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))
        else tl.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length) =
        (∑ T ∈ S, (tl.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length) +
        (∑ T ∈ S, if @decide (hd.1 = T) (Classical.propDecidable _) then 1 else 0) := by
      rw [← hsplit]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      split_ifs <;> simp
    rw [hmap]
    have hone : (∑ T ∈ S, if @decide (hd.1 = T) (Classical.propDecidable _) then (1 : ℕ) else 0) ≤ 1 := by
      by_cases hmem : hd.1 ∈ S
      · rw [Finset.sum_eq_single hd.1]
        · simp
        · intro T _ hne; have hne' : hd.1 ≠ T := hne.symm; simp [hne']
        · intro hnot; exact (hnot hmem).elim
      · have h0 : (∑ T ∈ S, if @decide (hd.1 = T) (Classical.propDecidable _) then (1 : ℕ) else 0) = 0 := by
          refine Finset.sum_eq_zero (fun T hT => ?_)
          have hne : hd.1 ≠ T := fun heq => hmem (heq ▸ hT)
          simp [hne]
        omega
    omega

end PEqualNP.Outside.L_lib_1016_aux

theorem PEqualNP.Outside.L_lib_1016 :
  ∀ (k d : Nat), d < k →
  let U := (Finset.univ : Finset (Fin k))
  let high := U.powerset.filter (fun T => d < T.card)
  let mass := fun (rows : List (Finset (Fin k) × Bool)) (predicate : Finset (Fin k) → Prop) =>
    ((rows.filter (fun x => x.2 && @decide (predicate x.1) (Classical.propDecidable _))).length : Int) -
      ((rows.filter (fun x => !x.2 && @decide (predicate x.1) (Classical.propDecidable _))).length : Int)
  let covers := fun rows (T : Finset (Fin k)) => mass rows (fun A => T ⊆ A)
  let vanishes := fun rows => ∀ T ∈ high, T ≠ U → covers rows T = 0
  (∀ rows : List (Finset (Fin k) × Bool), vanishes rows →
    let c := covers rows U
    (∀ T ∈ high, mass rows (fun A => A = T) = (-1 : Int)^(k-T.card)*c) ∧
    2^(k-(d+1))*c.natAbs ≤ high.card*c.natAbs ∧ high.card*c.natAbs ≤ rows.length) ∧
  ∀ r : Nat, 0 < r → ∃ rows : List (Finset (Fin k) × Bool),
    covers rows U = (r : Int) ∧ vanishes rows ∧ rows.length = high.card*r := by
  intro k d hdk U high mass covers vanishes
  constructor
  · intro rows hvan c
    have hexact : ∀ n : ℕ, ∀ T ∈ high, k - T.card = n →
        mass rows (fun A => A = T) = (-1 : Int) ^ (k - T.card) * c := by
      intro n
      induction n using Nat.strongRecOn with
      | _ n ih =>
        intro T hThigh hn
        by_cases hTU : T = U
        · subst hTU
          have hcardU : U.card = k := by simp [U]
          rw [hcardU, Nat.sub_self, pow_zero, one_mul]
          have heq_pred : (fun A : Finset (Fin k) => A = U) = (fun A => U ⊆ A) := by
            funext A
            exact propext ⟨fun h => h ▸ le_refl _, fun h => le_antisymm (Finset.subset_univ A) h⟩
          simp only [c, covers, mass, heq_pred]
        · have hcov0 : covers rows T = 0 := hvan T hThigh hTU
          have hcov_sum := PEqualNP.Outside.L_lib_1016_aux.covers_eq_sum_exact rows T
          change covers rows T = ∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
            mass rows (fun B => B = A) at hcov_sum
          rw [hcov0] at hcov_sum
          let S := (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A)
          have hTmem : T ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩
          have hsplit1 : (∑ A ∈ S, mass rows (fun B => B = A)) =
              mass rows (fun B => B = T) + ∑ A ∈ S.erase T, mass rows (fun B => B = A) :=
            (Finset.add_sum_erase S (fun A => mass rows (fun B => B = A)) hTmem).symm
          have hsplit2 : (∑ A ∈ S, (-1 : Int) ^ (k - A.card) * c) =
              (-1 : Int) ^ (k - T.card) * c + ∑ A ∈ S.erase T, (-1 : Int) ^ (k - A.card) * c :=
            (Finset.add_sum_erase S (fun A => (-1 : Int) ^ (k - A.card) * c) hTmem).symm
          have halt : (∑ A ∈ S, (-1 : Int) ^ (k - A.card) * c) = 0 := by
            rw [← Finset.sum_mul, PEqualNP.Outside.L_lib_1016_aux.alt_sum_supersets T hTU, zero_mul]
          have hrest : (∑ A ∈ S.erase T, mass rows (fun B => B = A)) =
              ∑ A ∈ S.erase T, (-1 : Int) ^ (k - A.card) * c := by
            refine Finset.sum_congr rfl (fun A hA => ?_)
            have hAne : A ≠ T := (Finset.mem_erase.mp hA).1
            have hTA : T ⊆ A := (Finset.mem_filter.mp (Finset.mem_erase.mp hA).2).2
            have hss : T ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hTA, hAne.symm⟩
            have hlt_card : T.card < A.card := Finset.card_lt_card hss
            have hA_le : A.card ≤ k := by simpa [Fintype.card_fin] using Finset.card_le_univ A
            have hT_gt : d < T.card := (Finset.mem_filter.mp hThigh).2
            have hAhigh : A ∈ high :=
              Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), by omega⟩
            exact ih (k - A.card) (by omega) A hAhigh rfl
          rw [hsplit1, hrest] at hcov_sum
          rw [hsplit2] at halt
          omega
    have hpart1 : ∀ T ∈ high, mass rows (fun A => A = T) = (-1 : Int) ^ (k - T.card) * c :=
      fun T hT => hexact (k - T.card) T hT rfl
    have hpart2 : 2 ^ (k - (d + 1)) * c.natAbs ≤ high.card * c.natAbs :=
      Nat.mul_le_mul_right c.natAbs (PEqualNP.Outside.L_lib_1016_aux.high_card_ge hdk)
    have hpart3 : high.card * c.natAbs ≤ rows.length := by
      calc
        high.card * c.natAbs = ∑ T ∈ high, c.natAbs := by simp
        _ = ∑ T ∈ high, (mass rows (fun A => A = T)).natAbs := by
              refine Finset.sum_congr rfl (fun T hT => ?_)
              rw [hpart1 T hT, Int.natAbs_mul, Int.natAbs_pow]
              simp
        _ ≤ ∑ T ∈ high, (rows.filter (fun x => @decide (x.1 = T) (Classical.propDecidable _))).length :=
              Finset.sum_le_sum (fun T _ => PEqualNP.Outside.L_lib_1016_aux.natAbs_mass_le_count rows T)
        _ ≤ rows.length := PEqualNP.Outside.L_lib_1016_aux.sum_filter_eq_le_length high rows
    exact ⟨hpart1, hpart2, hpart3⟩
  · intro r hr
    let rows : List (Finset (Fin k) × Bool) :=
      high.toList.flatMap (fun T => List.replicate r (T, decide ((k - T.card) % 2 = 0)))
    have hlen : rows.length = high.card * r := by
      simp only [rows, List.length_flatMap, List.map_const', List.length_replicate,
        List.sum_replicate, smul_eq_mul, Finset.length_toList]
    have hmass_exact : ∀ A : Finset (Fin k),
        mass rows (fun B => B = A) = if A ∈ high then (-1 : Int) ^ (k - A.card) * (r : Int) else 0 := by
      intro A
      dsimp only [mass]
      rw [PEqualNP.Outside.L_lib_1016_aux.mass_eq_list_sum rows (fun B => B = A)]
      have hflat : ∀ (L : List (Finset (Fin k))) (g : Finset (Fin k) → List Int),
          (L.flatMap g).sum = (L.map (fun T => (g T).sum)).sum := by
        intro L g
        induction L with
        | nil => simp
        | cons hd tl ih => simp [ih]
      simp only [rows, List.map_flatMap, hflat, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
      have hsum_list : ∀ f : Finset (Fin k) → Int,
          (high.toList.map f).sum = ∑ T ∈ high, f T := by
        intro f
        have hcoe : (high.toList : Multiset (Finset (Fin k))) = high.val := Finset.coe_toList high
        change (high.toList.map f).sum = (high.val.map f).sum
        rw [← hcoe]
        rfl
      rw [hsum_list]
      by_cases hA : A ∈ high
      · rw [if_pos hA, Finset.sum_eq_single A]
        · simp only [decide_true, ↓reduceIte]
          have hsign : (if decide ((k - A.card) % 2 = 0) then (1 : Int) else -1) = (-1 : Int) ^ (k - A.card) := by
            rcases Nat.even_or_odd (k - A.card) with ⟨m, hm⟩ | ⟨m, hm⟩
            · have hmod : (k - A.card) % 2 = 0 := by omega
              rw [hmod, hm]
              simp only [decide_true, ↓reduceIte]
              rw [← two_mul, pow_mul]
              norm_num
            · have hmod : (k - A.card) % 2 = 1 := by omega
              rw [hmod, hm]
              simp only [one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]
              rw [pow_succ, pow_mul]
              norm_num
          rw [hsign, mul_comm]
        · intro T _ hne; simp [hne]
        · intro hnot; exact (hnot hA).elim
      · rw [if_neg hA]
        refine Finset.sum_eq_zero (fun T hT => ?_)
        have hne : T ≠ A := fun heq => hA (heq ▸ hT)
        simp [hne]
    have hcov_high : ∀ T ∈ high, covers rows T =
        (∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
          (-1 : Int) ^ (k - A.card)) * (r : Int) := by
      intro T hT
      have h1 := PEqualNP.Outside.L_lib_1016_aux.covers_eq_sum_exact rows T
      change covers rows T = ∑ A ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun A => T ⊆ A),
        mass rows (fun B => B = A) at h1
      rw [h1, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      have hTA : T ⊆ A := (Finset.mem_filter.mp hA).2
      have hTgt : d < T.card := (Finset.mem_filter.mp hT).2
      have hle : T.card ≤ A.card := Finset.card_le_card hTA
      have hAhigh : A ∈ high :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), by omega⟩
      rw [hmass_exact A, if_pos hAhigh]
    have hUhigh : U ∈ high := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (le_refl _), ?_⟩
      simpa [U] using hdk
    have hcovU : covers rows U = (r : Int) := by
      rw [hcov_high U hUhigh]
      have hfilt : (Finset.univ : Finset (Finset (Fin k))).filter (fun A => U ⊆ A) = {U} := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => le_antisymm (Finset.subset_univ A) h, fun h => h ▸ le_refl _⟩
      rw [hfilt, Finset.sum_singleton]
      have hcardU : U.card = k := by simp [U]
      rw [hcardU, Nat.sub_self, pow_zero, one_mul]
    have hvan : vanishes rows := by
      intro T hT hTU
      rw [hcov_high T hT, PEqualNP.Outside.L_lib_1016_aux.alt_sum_supersets T hTU, zero_mul]
    exact ⟨rows, hcovU, hvan, hlen⟩
