import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1165

private def idxFn {r : Nat} (S : Finset (Fin r)) : Nat :=
  S.sum (fun j => 2 ^ j.val)

private def ltW {r : Nat} (V S : Finset (Fin r)) : Prop :=
  V.card < S.card ∨ (V.card = S.card ∧ idxFn V < idxFn S)

private def wOrd {r : Nat} (S : Finset (Fin r)) : Nat :=
  ((Finset.univ : Finset (Finset (Fin r))).filter (fun V =>
    V.card < S.card ∨ (V.card = S.card ∧ idxFn V < idxFn S))).card

private def isDownSet {r : Nat} (M : Finset (Finset (Fin r))) : Prop :=
  ∀ S ∈ M, ∀ T ⊆ S, T ∈ M

private def matchCoord (a b : Nat) (v : Nat) (mem : Bool) : Bool :=
  if v < a then mem else if v < a + b then !mem else true

private noncomputable def seesFn {r : Nat} (a b c : Nat) (M : Finset (Finset (Fin r))) : Nat :=
  ((Finset.univ : Finset (Fin r → Fin (a + b + c))).filter (fun x =>
    M.toList.any (fun S => (Finset.univ : Finset (Fin r)).toList.all (fun j =>
      if (x j).val < a then decide (j ∈ S) else
      if (x j).val < a + b then decide (j ∉ S) else true)))).card

private lemma idxFn_lt : ∀ {r : Nat} (S : Finset (Fin r)), idxFn S < 2 ^ r
  | 0, S => by
    have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    subst hS; simp [idxFn]
  | r + 1, S => by
    let S' : Finset (Fin r) := Finset.univ.filter (fun j => j.castSucc ∈ S)
    have hsplit : idxFn S = idxFn S' + (if Fin.last r ∈ S then 2 ^ r else 0) := by
      unfold idxFn
      have hsum : (∑ j : Fin r, if j.castSucc ∈ S then 2 ^ j.val else 0) =
          S'.sum (fun j => 2 ^ j.val) := by
        rw [← Finset.sum_filter]
      have h1 : S.sum (fun j : Fin (r + 1) => 2 ^ j.val) =
          ∑ j : Fin (r + 1), if j ∈ S then 2 ^ j.val else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h1, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hsum]
    have hlt := idxFn_lt S'
    have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
    rw [hsplit]
    split_ifs <;> omega

private lemma idxFn_inj : ∀ {r : Nat} {S₁ S₂ : Finset (Fin r)}, idxFn S₁ = idxFn S₂ → S₁ = S₂
  | 0, S₁, S₂, _ => by
    rw [Finset.eq_empty_of_isEmpty S₁, Finset.eq_empty_of_isEmpty S₂]
  | r + 1, S₁, S₂, heq => by
    let S₁' : Finset (Fin r) := Finset.univ.filter (fun j => j.castSucc ∈ S₁)
    let S₂' : Finset (Fin r) := Finset.univ.filter (fun j => j.castSucc ∈ S₂)
    have hsp : ∀ S : Finset (Fin (r + 1)),
        idxFn S = idxFn (Finset.univ.filter (fun j : Fin r => j.castSucc ∈ S)) +
          (if Fin.last r ∈ S then 2 ^ r else 0) := by
      intro S
      unfold idxFn
      have h1 : S.sum (fun j : Fin (r + 1) => 2 ^ j.val) =
          ∑ j : Fin (r + 1), if j ∈ S then 2 ^ j.val else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h1, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← Finset.sum_filter]
    have h1 : idxFn S₁ = idxFn S₁' + (if Fin.last r ∈ S₁ then 2 ^ r else 0) := hsp S₁
    have h2 : idxFn S₂ = idxFn S₂' + (if Fin.last r ∈ S₂ then 2 ^ r else 0) := hsp S₂
    have hlt1 := idxFn_lt S₁'
    have hlt2 := idxFn_lt S₂'
    have hlast : (Fin.last r ∈ S₁) ↔ (Fin.last r ∈ S₂) := by
      by_cases a1 : Fin.last r ∈ S₁ <;> by_cases a2 : Fin.last r ∈ S₂ <;>
        simp [a1, a2] at h1 h2 ⊢ <;> omega
    have hsub : idxFn S₁' = idxFn S₂' := by
      by_cases a1 : Fin.last r ∈ S₁
      · have a2 : Fin.last r ∈ S₂ := hlast.mp a1
        simp only [a1, a2, ↓reduceIte] at h1 h2; omega
      · have a2 : Fin.last r ∉ S₂ := fun h => a1 (hlast.mpr h)
        simp only [a1, a2, ↓reduceIte, Nat.add_zero] at h1 h2; omega
    have hS' : S₁' = S₂' := idxFn_inj hsub
    ext j
    refine Fin.lastCases ?_ ?_ j
    · exact hlast
    · intro i
      have hi : i ∈ S₁' ↔ i ∈ S₂' := by rw [hS']
      simpa only [S₁', S₂', Finset.mem_filter, Finset.mem_univ, true_and] using hi

private lemma idxFn_mono {r : Nat} {T S : Finset (Fin r)} (h : T ⊆ S) :
    idxFn T ≤ idxFn S :=
  Finset.sum_le_sum_of_subset h

private lemma ltW_irrefl {r : Nat} (S : Finset (Fin r)) : ¬ ltW S S := by
  unfold ltW; omega

private lemma ltW_trans {r : Nat} {A B C : Finset (Fin r)}
    (h1 : ltW A B) (h2 : ltW B C) : ltW A C := by
  unfold ltW at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨e1.trans e2, lt_trans h1 h2⟩

private lemma ltW_trich {r : Nat} {A B : Finset (Fin r)} (hne : A ≠ B) :
    ltW A B ∨ ltW B A := by
  unfold ltW
  by_cases hc : A.card = B.card
  · have hi : idxFn A ≠ idxFn B := fun h => hne (idxFn_inj h)
    rcases Nat.lt_or_gt_of_ne hi with h | h
    · exact Or.inl (Or.inr ⟨hc, h⟩)
    · exact Or.inr (Or.inr ⟨hc.symm, h⟩)
  · rcases Nat.lt_or_gt_of_ne hc with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

private lemma wOrd_lt_of_ltW {r : Nat} {A B : Finset (Fin r)} (h : ltW A B) :
    wOrd A < wOrd B := by
  unfold wOrd
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
      fun hA => ltW_irrefl A (Finset.mem_filter.mp hA).2⟩
  · intro V hV
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ltW_trans (Finset.mem_filter.mp hV).2 h⟩

private lemma wOrd_inj {r : Nat} {A B : Finset (Fin r)} (h : wOrd A = wOrd B) : A = B := by
  by_contra hne
  rcases ltW_trich hne with hab | hba
  · exact Nat.ne_of_lt (wOrd_lt_of_ltW hab) h
  · exact Nat.ne_of_gt (wOrd_lt_of_ltW hba) h

private lemma wOrd_lt {r : Nat} (S : Finset (Fin r)) : wOrd S < 2 ^ r := by
  unfold wOrd
  have hss : (Finset.univ : Finset (Finset (Fin r))).filter (fun V =>
      V.card < S.card ∨ (V.card = S.card ∧ idxFn V < idxFn S)) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨S, Finset.mem_univ S, fun hS => ltW_irrefl S (Finset.mem_filter.mp hS).2⟩
  have hlt := Finset.card_lt_card hss
  simpa using hlt

private lemma card_filter_lt_of_inj_lt {r k : Nat} (hk : k ≤ 2 ^ r)
    (f : Finset (Fin r) → Nat)
    (hinj : ∀ A B, f A = f B → A = B)
    (hlt : ∀ A, f A < 2 ^ r) :
    ((Finset.univ : Finset (Finset (Fin r))).filter (fun S => f S < k)).card = k := by
  let g : Finset (Fin r) → Fin (2 ^ r) := fun S => ⟨f S, hlt S⟩
  have hginj : Function.Injective g := fun A B h => hinj A B (congrArg Fin.val h)
  have hcard : Fintype.card (Finset (Fin r)) = Fintype.card (Fin (2 ^ r)) := by
    simp
  have hgbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcard⟩
  let e := Equiv.ofBijective g hgbij
  have heq : (Finset.univ : Finset (Finset (Fin r))).filter (fun S => f S < k) =
      (Finset.univ.filter (fun x : Fin (2 ^ r) => x.val < k)).map e.symm.toEmbedding := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hS
      exact ⟨e S, hS, e.symm_apply_apply S⟩
    · rintro ⟨x, hx, rfl⟩
      have : f (e.symm x) = (e (e.symm x)).val := rfl
      rw [this, e.apply_symm_apply]
      exact hx
  rw [heq, Finset.card_map]
  let emb : Fin k ↪ Fin (2 ^ r) :=
    ⟨fun x => ⟨x.val, lt_of_lt_of_le x.isLt hk⟩,
      fun x y h => by dsimp only at h; exact Fin.ext (congrArg (fun z : Fin (2 ^ r) => z.val) h)⟩
  have heq2 : (Finset.univ : Finset (Fin (2 ^ r))).filter (fun x => x.val < k) =
      Finset.univ.map emb := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hx; exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    · rintro ⟨y, rfl⟩; exact y.isLt
  rw [heq2, Finset.card_map, Finset.card_univ, Fintype.card_fin]

-- Sees formula for down-sets
private lemma seesFn_eq_sum_of_downSet {r a b c : Nat}
    {M : Finset (Finset (Fin r))} (hM : isDownSet M) :
    seesFn a b c M = M.sum (fun S => a ^ S.card * (b + c) ^ (r - S.card)) := by
  let posOf : (Fin r → Fin (a + b + c)) → Finset (Fin r) :=
    fun x => Finset.univ.filter (fun j => (x j).val < a)
  have hfilt : (Finset.univ : Finset (Fin r → Fin (a + b + c))).filter (fun x =>
      M.toList.any (fun S => (Finset.univ : Finset (Fin r)).toList.all (fun j =>
        if (x j).val < a then decide (j ∈ S) else
        if (x j).val < a + b then decide (j ∉ S) else true))) =
      (Finset.univ : Finset (Fin r → Fin (a + b + c))).filter (fun x => posOf x ∈ M) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true, Finset.mem_toList,
      List.all_eq_true]
    constructor
    · rintro ⟨S, hSM, hall⟩
      have hsub : posOf x ⊆ S := by
        intro j hj
        have hlt : (x j).val < a := (Finset.mem_filter.mp hj).2
        have h := hall j trivial
        simp only [hlt, ↓reduceIte, decide_eq_true_eq] at h
        exact h
      exact hM S hSM (posOf x) hsub
    · intro hpx
      refine ⟨posOf x, hpx, fun j _ => ?_⟩
      by_cases hlt : (x j).val < a
      · simp only [hlt, ↓reduceIte, decide_eq_true_eq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩
      · by_cases hlt2 : (x j).val < a + b
        · simp only [hlt, hlt2, ↓reduceIte, decide_eq_true_eq]
          intro hmem
          exact hlt (Finset.mem_filter.mp hmem).2
        · simp only [hlt, hlt2, ↓reduceIte]
  unfold seesFn
  rw [hfilt]
  rw [Finset.card_eq_sum_card_fiberwise (f := posOf)
    (s := Finset.univ.filter (fun x : Fin r → Fin (a + b + c) => posOf x ∈ M)) (t := M)
    (fun x hx => (Finset.mem_filter.mp hx).2)]
  refine Finset.sum_congr rfl (fun S hSM => ?_)
  have hfib : ((Finset.univ.filter (fun x : Fin r → Fin (a + b + c) => posOf x ∈ M)).filter
      (fun x => posOf x = S)) =
      Finset.univ.filter (fun x : Fin r → Fin (a + b + c) => posOf x = S) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hSM, h⟩
  rw [hfib]
  let allowed : Fin r → Finset (Fin (a + b + c)) := fun j =>
    if j ∈ S then Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a)
    else Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val)
  have hpi : Finset.univ.filter (fun x : Fin r → Fin (a + b + c) => posOf x = S) =
      Fintype.piFinset allowed := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hpx j
      by_cases hj : j ∈ S
      · simp only [allowed, hj, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        have : j ∈ posOf x := hpx.symm ▸ hj
        exact (Finset.mem_filter.mp this).2
      · simp only [allowed, hj, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        have : j ∉ posOf x := hpx.symm ▸ hj
        have hnot : ¬ ((x j).val < a) := fun h => this (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
        omega
    · intro hall
      ext j
      simp only [posOf, Finset.mem_filter, Finset.mem_univ, true_and]
      have hj := hall j
      by_cases hmem : j ∈ S
      · simp only [allowed, hmem, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨fun _ => hmem, fun _ => hj⟩
      · simp only [allowed, hmem, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨fun hlt => absurd hlt (by omega), fun h => absurd h hmem⟩
  rw [hpi, Fintype.card_piFinset]
  have hcard_lt : (Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a)).card = a := by
    let emb : Fin a ↪ Fin (a + b + c) :=
      ⟨fun v => ⟨v.val, by omega⟩,
        fun x y h => by dsimp only at h; exact Fin.ext (congrArg (fun z : Fin (a + b + c) => z.val) h)⟩
    have heq : Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a) = Finset.univ.map emb := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hv; exact ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
      · rintro ⟨x, rfl⟩; exact x.isLt
    rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcard_ge : (Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val)).card = b + c := by
    have hcomp : Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val) =
        Finset.univ \ Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      omega
    rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard_lt]
    omega
  have hprod : (∏ j : Fin r, (allowed j).card) =
      (∏ _j ∈ S, a) * (∏ _j ∈ (Finset.univ \ S), (b + c)) := by
    have hunion : S ∪ (Finset.univ \ S) = (Finset.univ : Finset (Fin r)) :=
      Finset.union_sdiff_of_subset (Finset.subset_univ S)
    have hdisj : Disjoint S (Finset.univ \ S) := Finset.disjoint_sdiff
    calc
      (∏ j : Fin r, (allowed j).card)
          = (∏ j ∈ S ∪ (Finset.univ \ S), (allowed j).card) := by rw [hunion]
      _ = (∏ j ∈ S, (allowed j).card) * (∏ j ∈ Finset.univ \ S, (allowed j).card) :=
          Finset.prod_union hdisj
      _ = (∏ _j ∈ S, a) * (∏ _j ∈ Finset.univ \ S, (b + c)) := by
          congr 1
          · refine Finset.prod_congr rfl (fun j hj => ?_)
            simp only [allowed, hj, ↓reduceIte, hcard_lt]
          · refine Finset.prod_congr rfl (fun j hj => ?_)
            have hnot : j ∉ S := (Finset.mem_sdiff.mp hj).2
            simp only [allowed, hnot, ↓reduceIte, hcard_ge]
  rw [hprod, Finset.prod_const, Finset.prod_const]
  have hsdiff : (Finset.univ \ S).card = r - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [hsdiff]

-- Down-compression on coordinate j
private def shiftCoord {r : Nat} (j : Fin r) (M : Finset (Finset (Fin r)))
    (S : Finset (Fin r)) : Finset (Fin r) :=
  if j ∈ S ∧ S.erase j ∉ M then S.erase j else S

private def compressCoord {r : Nat} (j : Fin r) (M : Finset (Finset (Fin r))) :
    Finset (Finset (Fin r)) :=
  M.image (shiftCoord j M)

private lemma shiftCoord_injOn {r : Nat} (j : Fin r) (M : Finset (Finset (Fin r))) :
    Set.InjOn (shiftCoord j M) M := by
  intro S₁ h1 S₂ h2 heq
  unfold shiftCoord at heq
  by_cases c1 : j ∈ S₁ ∧ S₁.erase j ∉ M <;> by_cases c2 : j ∈ S₂ ∧ S₂.erase j ∉ M
  · rw [if_pos c1, if_pos c2] at heq
    rw [← Finset.insert_erase c1.1, ← Finset.insert_erase c2.1, heq]
  · rw [if_pos c1, if_neg c2] at heq
    exfalso; exact c1.2 (heq.symm ▸ h2)
  · rw [if_neg c1, if_pos c2] at heq
    exfalso; exact c2.2 (heq ▸ h1)
  · rw [if_neg c1, if_neg c2] at heq
    exact heq

private lemma card_compressCoord {r : Nat} (j : Fin r) (M : Finset (Finset (Fin r))) :
    (compressCoord j M).card = M.card :=
  Finset.card_image_of_injOn (shiftCoord_injOn j M)

private lemma sum_card_compressCoord_lt {r : Nat} (j : Fin r) (M : Finset (Finset (Fin r)))
    {S₀ : Finset (Fin r)} (hS₀ : S₀ ∈ M) (hj : j ∈ S₀) (hnot : S₀.erase j ∉ M) :
    (compressCoord j M).sum Finset.card < M.sum Finset.card := by
  unfold compressCoord
  rw [Finset.sum_image (shiftCoord_injOn j M)]
  refine Finset.sum_lt_sum ?_ ⟨S₀, hS₀, ?_⟩
  · intro S _
    unfold shiftCoord
    split_ifs with h
    · exact (Finset.card_erase_lt_of_mem h.1).le
    · exact le_refl _
  · unfold shiftCoord
    simp only [hj, hnot, and_self, ↓reduceIte]
    exact Finset.card_erase_lt_of_mem hj

private lemma seesFn_compressCoord_le {r a b c : Nat} (hba : b ≤ a)
    (j : Fin r) (M : Finset (Finset (Fin r))) :
    seesFn a b c (compressCoord j M) ≤ seesFn a b c M := by
  by_cases hzero : a + b + c = 0
  · have hemp : IsEmpty (Fin r → Fin (a + b + c)) := by
      refine ⟨fun f => ?_⟩
      have := (f j).isLt; omega
    have h0 : (Finset.univ : Finset (Fin r → Fin (a + b + c))) = ∅ :=
      Finset.eq_empty_of_isEmpty _
    unfold seesFn
    rw [h0]; simp
  · have hpos : 0 < a + b + c := by omega
    let z0 : Fin (a + b + c) := ⟨0, hpos⟩
    let base : (Fin r → Fin (a + b + c)) → (Fin r → Fin (a + b + c)) :=
      fun x => Function.update x j z0
    let seen (N : Finset (Finset (Fin r))) : Finset (Fin r → Fin (a + b + c)) :=
      Finset.univ.filter (fun x =>
        N.toList.any (fun S => (Finset.univ : Finset (Fin r)).toList.all (fun i =>
          if (x i).val < a then decide (i ∈ S) else
          if (x i).val < a + b then decide (i ∉ S) else true)))
    have hseen_iff : ∀ N x, x ∈ seen N ↔ ∃ S ∈ N, ∀ i : Fin r,
        (if (x i).val < a then i ∈ S else if (x i).val < a + b then i ∉ S else True) := by
      intro N x
      simp only [seen, Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true,
        Finset.mem_toList, List.all_eq_true]
      refine exists_congr (fun S => and_congr_right (fun _ => forall_congr' (fun i => ?_)))
      by_cases h1 : (x i).val < a
      · simp [h1]
      · by_cases h2 : (x i).val < a + b <;> simp [h1, h2]
    change (seen (compressCoord j M)).card ≤ (seen M).card
    rw [Finset.card_eq_sum_card_fiberwise (f := base) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
        Finset.card_eq_sum_card_fiberwise (f := base) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum (fun y _ => ?_)
    -- Fiber over y: map v : Fin (a+b+c) |-> Function.update y j v
    let fib (N : Finset (Finset (Fin r))) : Finset (Fin (a + b + c)) :=
      Finset.univ.filter (fun v => Function.update y j v ∈ seen N ∧ base (Function.update y j v) = y)
    have hfib_card : ∀ N, ((seen N).filter (fun x => base x = y)).card = (fib N).card := by
      intro N
      refine Finset.card_bij (fun x _ => x j) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter] at hx
        have hupd : Function.update y j (x j) = x := by
          rw [← hx.2]
          funext i
          by_cases hi : i = j
          · subst hi; simp [base]
          · simp [base, hi]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [hupd]; exact hx.1
        · rw [hupd]; exact hx.2
      · intro x₁ hx1 x₂ hx2 hxj
        simp only [Finset.mem_filter] at hx1 hx2
        funext i
        by_cases hi : i = j
        · subst hi; exact hxj
        · have h1 := congrFun hx1.2 i
          have h2 := congrFun hx2.2 i
          simp only [base, Function.update_of_ne hi] at h1 h2
          exact h1.trans h2.symm
      · intro v hv
        simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact ⟨Function.update y j v, Finset.mem_filter.mpr hv, by simp⟩
    rw [hfib_card (compressCoord j M), hfib_card M]
    by_cases hbase_y : base y = y
    · have hbase_upd : ∀ v, base (Function.update y j v) = y := by
        intro v
        funext i
        by_cases hi : i = j
        · rw [hi]
          have hyj := congrFun hbase_y j
          simp only [base, Function.update_self] at hyj ⊢
          exact hyj
        · simp [base, hi]
      let matchRest (S : Finset (Fin r)) : Prop :=
        ∀ i : Fin r, i ≠ j →
          (if (y i).val < a then i ∈ S else if (y i).val < a + b then i ∉ S else True)
      have hmr_erase : ∀ S, matchRest (S.erase j) ↔ matchRest S := by
        intro S
        refine forall_congr' (fun i => forall_congr' (fun hi => ?_))
        simp only [Finset.mem_erase, hi, ne_eq, not_false_eq_true, true_and]
      have hupd_mem : ∀ N v, v ∈ fib N ↔ ∃ S ∈ N, matchRest S ∧
          (if v.val < a then j ∈ S else if v.val < a + b then j ∉ S else True) := by
        intro N v
        simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, hbase_upd, and_true, hseen_iff]
        refine exists_congr (fun S => and_congr_right (fun _ => ?_))
        constructor
        · intro hall
          refine ⟨fun i hi => ?_, ?_⟩
          · have h := hall i; simpa [hi] using h
          · have h := hall j; simpa using h
        · rintro ⟨hmr, hjv⟩ i
          by_cases hi : i = j
          · subst hi; simpa using hjv
          · simpa [hi] using hmr i hi
      by_cases htop : ∃ S ∈ compressCoord j M, j ∈ S ∧ matchRest S
      · rcases htop with ⟨S, hSc, hjS, hmrS⟩
        rcases Finset.mem_image.mp hSc with ⟨S', hS'M, hsh⟩
        have hS'eq : S' = S := by
          unfold shiftCoord at hsh
          split_ifs at hsh with hc
          · exfalso; rw [← hsh] at hjS; exact Finset.notMem_erase j S' hjS
          · exact hsh
        rw [hS'eq] at hS'M hsh
        have herase_mem : S.erase j ∈ M := by
          by_contra hnot
          have hsh' : shiftCoord j M S = S.erase j := by
            unfold shiftCoord; rw [if_pos ⟨hjS, hnot⟩]
          rw [hsh'] at hsh
          have : j ∉ S.erase j := Finset.notMem_erase j S
          exact this (hsh.symm ▸ hjS)
        have hM_all : fib M = Finset.univ := by
          ext v
          simp only [Finset.mem_univ, iff_true, hupd_mem]
          by_cases hv : v.val < a
          · exact ⟨S, hS'M, hmrS, by simp [hv, hjS]⟩
          · exact ⟨S.erase j, herase_mem, (hmr_erase S).mpr hmrS, by
              by_cases hv2 : v.val < a + b <;> simp [hv, hv2]⟩
        rw [hM_all]
        exact Finset.card_le_univ _
      · push_neg at htop
        by_cases hbot : ∃ S ∈ compressCoord j M, matchRest S
        · rcases hbot with ⟨S, hSc, hmrS⟩
          have hsub_c : fib (compressCoord j M) ⊆
              Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val) := by
            intro v hv
            rcases (hupd_mem (compressCoord j M) v).mp hv with ⟨T, hTc, hmrT, hjv⟩
            have hjnot : j ∉ T := fun hj => htop T hTc hj hmrT
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            by_contra hlt
            have hvlt : v.val < a := by omega
            simp only [hvlt, ↓reduceIte] at hjv
            exact hjnot hjv
          have hcard_ge : (Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val)).card = b + c := by
            let emb : Fin a ↪ Fin (a + b + c) :=
              ⟨fun v => ⟨v.val, by omega⟩,
                fun x y h => by dsimp only at h; exact Fin.ext (congrArg (fun z : Fin (a + b + c) => z.val) h)⟩
            have hlt_c : (Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a)).card = a := by
              have heq : Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a) = Finset.univ.map emb := by
                ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
                exact ⟨fun hv => ⟨⟨v.val, hv⟩, Fin.ext rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.isLt⟩
              rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
            have hcomp : Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val) =
                Finset.univ \ Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a) := by
              ext v; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]; omega
            rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hlt_c]
            omega
          rcases Finset.mem_image.mp hSc with ⟨S', hS'M, hsh⟩
          unfold shiftCoord at hsh
          split_ifs at hsh with hc
          · -- S' ∈ M, j ∈ S', S = S'.erase j
            have hmrS' : matchRest S' := (hmr_erase S').mp (hsh ▸ hmrS)
            have hsub_M : Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a ∨ a + b ≤ v.val) ⊆
                fib M := by
              intro v hv
              have hor := (Finset.mem_filter.mp hv).2
              refine (hupd_mem M v).mpr ⟨S', hS'M, hmrS', ?_⟩
              rcases hor with h1 | h2
              · simp [h1, hc.1]
              · have hnot1 : ¬ (v.val < a) := by omega
                have hnot2 : ¬ (v.val < a + b) := by omega
                simp [hnot1, hnot2]
            have hcard_ac : (Finset.univ.filter (fun v : Fin (a + b + c) =>
                v.val < a ∨ a + b ≤ v.val)).card = a + c := by
              have hcomp : Finset.univ.filter (fun v : Fin (a + b + c) => v.val < a ∨ a + b ≤ v.val) =
                  Finset.univ \ Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val ∧ v.val < a + b) := by
                ext v; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]; omega
              have hmid : (Finset.univ.filter (fun v : Fin (a + b + c) =>
                  a ≤ v.val ∧ v.val < a + b)).card = b := by
                let emb : Fin b ↪ Fin (a + b + c) :=
                  ⟨fun v => ⟨a + v.val, by omega⟩,
                    fun x y h => by
                      dsimp only at h
                      have hv := congrArg (fun z : Fin (a + b + c) => z.val) h
                      dsimp only at hv; exact Fin.ext (by omega)⟩
                have heq : Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val ∧ v.val < a + b) =
                    Finset.univ.map emb := by
                  ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
                  constructor
                  · intro ⟨h1, h2⟩
                    refine ⟨⟨v.val - a, by omega⟩, ?_⟩
                    apply Fin.ext; change a + (v.val - a) = v.val; omega
                  · rintro ⟨x, rfl⟩
                    change a ≤ a + x.val ∧ a + x.val < a + b; omega
                rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
              rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hmid]
              omega
            have h1 := Finset.card_le_card hsub_c
            have h2 := Finset.card_le_card hsub_M
            rw [hcard_ge] at h1
            rw [hcard_ac] at h2
            omega
          · -- S' = S ∈ M and j ∉ S (by htop)
            subst hsh
            have hjnot : j ∉ S' := fun hj => htop S' hSc hj hmrS
            have hsub_M : Finset.univ.filter (fun v : Fin (a + b + c) => a ≤ v.val) ⊆ fib M := by
              intro v hv
              have hge := (Finset.mem_filter.mp hv).2
              refine (hupd_mem M v).mpr ⟨S', hS'M, hmrS, ?_⟩
              have hnot1 : ¬ (v.val < a) := by omega
              by_cases h2 : v.val < a + b <;> simp [hnot1, h2, hjnot]
            exact Finset.card_le_card (hsub_c.trans hsub_M)
        · push_neg at hbot
          have hemp : fib (compressCoord j M) = ∅ := by
            ext v
            simp only [Finset.notMem_empty, iff_false, hupd_mem]
            rintro ⟨S, hSc, hmrS, _⟩
            exact hbot S hSc hmrS
          rw [hemp]; simp
    · have hemp : fib (compressCoord j M) = ∅ := by
        ext v
        simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro ⟨_, hb⟩
        apply hbase_y
        funext i
        have hi := congrFun hb i
        by_cases hij : i = j
        · subst hij
          simp only [base, Function.update_self] at hi ⊢
          exact hi
        · simp only [base, Function.update_of_ne hij] at hi ⊢
      rw [hemp]; simp

private lemma exists_downSet_le {r a b c : Nat} (hba : b ≤ a) :
    ∀ M : Finset (Finset (Fin r)),
      ∃ M' : Finset (Finset (Fin r)),
        isDownSet M' ∧ M'.card = M.card ∧ seesFn a b c M' ≤ seesFn a b c M := by
  intro M
  suffices h : ∀ N : Nat, ∀ M : Finset (Finset (Fin r)), M.sum Finset.card = N →
      ∃ M' : Finset (Finset (Fin r)),
        isDownSet M' ∧ M'.card = M.card ∧ seesFn a b c M' ≤ seesFn a b c M by
    exact h (M.sum Finset.card) M rfl
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro M hsum
    by_cases hdown : isDownSet M
    · exact ⟨M, hdown, rfl, le_refl _⟩
    · have hex : ∃ S ∈ M, ∃ j ∈ S, S.erase j ∉ M := by
        by_contra hall
        push_neg at hall
        apply hdown
        intro S hSM T hTS
        have hstep : ∀ d : Nat, ∀ U : Finset (Fin r), U ⊆ S → (S \ U).card = d → U ∈ M := by
          intro d
          induction d with
          | zero =>
            intro U hUS h0
            have hsd : S \ U = ∅ := Finset.card_eq_zero.mp h0
            have hSU : S ⊆ U := Finset.sdiff_eq_empty_iff_subset.mp hsd
            have heq : U = S := Finset.Subset.antisymm hUS hSU
            rwa [heq]
          | succ d ihd =>
            intro U hUS hd
            have hne : (S \ U).Nonempty := Finset.card_pos.mp (by omega)
            rcases hne with ⟨j, hj⟩
            have hjS : j ∈ S := (Finset.mem_sdiff.mp hj).1
            have hjU : j ∉ U := (Finset.mem_sdiff.mp hj).2
            let U' := insert j U
            have hU'S : U' ⊆ S := Finset.insert_subset hjS hUS
            have hsd : S \ U' = (S \ U).erase j := by
              ext x; simp only [U', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
              tauto
            have hcard' : (S \ U').card = d := by
              rw [hsd, Finset.card_erase_of_mem hj, hd]; omega
            have hU'M : U' ∈ M := ihd U' hU'S hcard'
            have hUeq : U'.erase j = U := Finset.erase_insert hjU
            rw [← hUeq]
            exact hall U' hU'M j (Finset.mem_insert_self j U)
        exact hstep (S \ T).card T hTS rfl
      rcases hex with ⟨S₀, hS₀M, j, hjS₀, hnot⟩
      let M1 := compressCoord j M
      have hlt : M1.sum Finset.card < N := by
        rw [← hsum]
        exact sum_card_compressCoord_lt j M hS₀M hjS₀ hnot
      rcases ih (M1.sum Finset.card) hlt M1 rfl with ⟨M', hdown', hcard', hsees'⟩
      refine ⟨M', hdown', hcard'.trans (card_compressCoord j M),
        hsees'.trans (seesFn_compressCoord_le hba j M)⟩

-- Optimal weight function F a d r k for a <= d
private def optF (a d : Nat) : Nat → Nat → Nat
  | 0, k => if k = 0 then 0 else 1
  | r + 1, k =>
    if k ≤ 2 ^ r then d * optF a d r k
    else d * optF a d r (2 ^ r) + a * optF a d r (k - 2 ^ r)

private lemma optF_zero (a d : Nat) : ∀ r, optF a d r 0 = 0
  | 0 => rfl
  | r + 1 => by simp [optF, optF_zero a d r]

private lemma optF_mono (a d : Nat) : ∀ r {x y : Nat}, x ≤ y → y ≤ 2 ^ r →
    optF a d r x ≤ optF a d r y
  | 0, x, y, hxy, hy => by
    have : x = 0 ∨ x = 1 := by omega
    have : y = 0 ∨ y = 1 := by omega
    rcases ‹x = 0 ∨ x = 1› with rfl | rfl <;> rcases ‹y = 0 ∨ y = 1› with rfl | rfl <;>
      simp [optF] <;> omega
  | r + 1, x, y, hxy, hy => by
    have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
    unfold optF
    by_cases hx : x ≤ 2 ^ r <;> by_cases hy' : y ≤ 2 ^ r
    · simp only [hx, hy', ↓reduceIte]
      exact Nat.mul_le_mul_left d (optF_mono a d r hxy hy')
    · simp only [hx, hy', ↓reduceIte]
      have h1 : d * optF a d r x ≤ d * optF a d r (2 ^ r) :=
        Nat.mul_le_mul_left d (optF_mono a d r hx (le_refl _))
      omega
    · omega
    · simp only [hx, hy', ↓reduceIte]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left a (optF_mono a d r (by omega) (by omega))) _

private lemma optF_succ_le (a d r k : Nat) (h : k ≤ 2 ^ r) :
    optF a d (r + 1) k = d * optF a d r k := by
  simp only [optF, h, ↓reduceIte]

private lemma optF_succ_ge (a d r k : Nat) (h : 2 ^ r ≤ k) :
    optF a d (r + 1) k = d * optF a d r (2 ^ r) + a * optF a d r (k - 2 ^ r) := by
  by_cases heq : k = 2 ^ r
  · subst heq; rw [optF_succ_le a d r _ (le_refl _), Nat.sub_self, optF_zero]; omega
  · have hnot : ¬ (k ≤ 2 ^ r) := by omega
    simp only [optF, hnot, ↓reduceIte]

private lemma optF_full (a d r : Nat) :
    optF a d (r + 1) (2 ^ (r + 1)) = (d + a) * optF a d r (2 ^ r) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
  have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
  rw [optF_succ_ge a d r (2 ^ (r + 1)) (by omega)]
  have hsub : 2 ^ (r + 1) - 2 ^ r = 2 ^ r := by omega
  rw [hsub]; ring

private lemma optF_pair {a d : Nat} (had : a ≤ d) :
    ∀ r : Nat,
      (∀ x y : Nat, y ≤ x → x ≤ 2 ^ r →
        optF a d (r + 1) (x + y) ≤ d * optF a d r x + a * optF a d r y) ∧
      (∀ x y : Nat, x ≤ 2 ^ r → y ≤ 2 ^ r →
        (if x + y ≤ 2 ^ r then optF a d r (x + y)
         else optF a d r (2 ^ r) + optF a d r (x + y - 2 ^ r)) ≤
        optF a d r x + optF a d r y) := by
  intro r
  induction r with
  | zero =>
    constructor
    · intro x y hyx hx
      have hx' : x = 0 ∨ x = 1 := by omega
      have hy' : y = 0 ∨ y = 1 := by omega
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> simp [optF] <;> omega
    · intro x y hx hy
      have hx' : x = 0 ∨ x = 1 := by omega
      have hy' : y = 0 ∨ y = 1 := by omega
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> simp [optF]
  | succ r ih =>
    rcases ih with ⟨ih1, ih2⟩
    have hpow1 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
    have hI2_symm : ∀ x y : Nat, y ≤ x → x ≤ 2 ^ (r + 1) →
        (if x + y ≤ 2 ^ (r + 1) then optF a d (r + 1) (x + y)
         else optF a d (r + 1) (2 ^ (r + 1)) + optF a d (r + 1) (x + y - 2 ^ (r + 1))) ≤
        optF a d (r + 1) x + optF a d (r + 1) y := by
      intro x y hyx hx
      by_cases hxN : x ≤ 2 ^ r
      · have hyN : y ≤ 2 ^ r := by omega
        have hxy : x + y ≤ 2 ^ (r + 1) := by omega
        rw [if_pos hxy, optF_succ_le a d r x hxN, optF_succ_le a d r y hyN]
        have h1 : optF a d (r + 1) (x + y) ≤ d * optF a d r x + a * optF a d r y :=
          ih1 x y hyx hxN
        have hmul : a * optF a d r y ≤ d * optF a d r y := Nat.mul_le_mul_right _ had
        omega
      · by_cases hyN : 2 ^ r ≤ y
        · set u := x - 2 ^ r
          set v := y - 2 ^ r
          have hu : u ≤ 2 ^ r := by omega
          have hv : v ≤ u := by omega
          have hxy_gt : ¬ (x + y ≤ 2 ^ (r + 1)) := by omega
          have hsub : x + y - 2 ^ (r + 1) = u + v := by omega
          rw [if_neg hxy_gt, hsub, optF_full,
              optF_succ_ge a d r x (by omega), optF_succ_ge a d r y hyN]
          have h2 := ih2 u v hu (by omega)
          by_cases huv : u + v ≤ 2 ^ r
          · rw [if_pos huv] at h2
            rw [optF_succ_le a d r (u + v) huv]
            have hmon : optF a d r (u + v) ≤ optF a d r (2 ^ r) := optF_mono a d r huv (le_refl _)
            have hm1 : (d - a) * optF a d r (u + v) ≤ (d - a) * optF a d r (2 ^ r) :=
              Nat.mul_le_mul_left _ hmon
            have hm2 : a * optF a d r (u + v) ≤ a * (optF a d r u + optF a d r v) :=
              Nat.mul_le_mul_left _ h2
            have hda : (d - a) + a = d := Nat.sub_add_cancel had
            have hlin1 : (d - a) * optF a d r (u + v) + a * optF a d r (u + v) =
                d * optF a d r (u + v) := by rw [← Nat.add_mul, hda]
            have hlin2 : (d - a) * optF a d r (2 ^ r) + a * optF a d r (2 ^ r) =
                d * optF a d r (2 ^ r) := by rw [← Nat.add_mul, hda]
            nlinarith
          · rw [if_neg huv] at h2
            rw [optF_succ_ge a d r (u + v) (by omega)]
            have hm2 : a * (optF a d r (2 ^ r) + optF a d r (u + v - 2 ^ r)) ≤
                a * (optF a d r u + optF a d r v) := Nat.mul_le_mul_left _ h2
            nlinarith
        · set u := x - 2 ^ r
          have hu : u ≤ 2 ^ r := by omega
          have hyN' : y ≤ 2 ^ r := by omega
          rw [optF_succ_ge a d r x (by omega), optF_succ_le a d r y hyN']
          have h2 := ih2 u y hu hyN'
          by_cases huy : u + y ≤ 2 ^ r
          · have hxy : x + y ≤ 2 ^ (r + 1) := by omega
            rw [if_pos hxy, optF_succ_ge a d r (x + y) (by omega)]
            rw [if_pos huy] at h2
            have hsub : x + y - 2 ^ r = u + y := by omega
            rw [hsub]
            have hm1 : a * optF a d r (u + y) ≤ a * (optF a d r u + optF a d r y) :=
              Nat.mul_le_mul_left _ h2
            have hm2 : a * optF a d r y ≤ d * optF a d r y := Nat.mul_le_mul_right _ had
            nlinarith
          · have hxy : ¬ (x + y ≤ 2 ^ (r + 1)) := by omega
            have hsub : x + y - 2 ^ (r + 1) = u + y - 2 ^ r := by omega
            rw [if_neg hxy, hsub, optF_full, optF_succ_le a d r (u + y - 2 ^ r) (by omega)]
            rw [if_neg huy] at h2
            have hmon : optF a d r (u + y - 2 ^ r) ≤ optF a d r y :=
              optF_mono a d r (by omega) hyN'
            have hm1 : a * (optF a d r (2 ^ r) + optF a d r (u + y - 2 ^ r)) ≤
                a * (optF a d r u + optF a d r y) := Nat.mul_le_mul_left _ h2
            have hm2 : (d - a) * optF a d r (u + y - 2 ^ r) ≤ (d - a) * optF a d r y :=
              Nat.mul_le_mul_left _ hmon
            have hda : (d - a) + a = d := Nat.sub_add_cancel had
            have hlin1 : (d - a) * optF a d r (u + y - 2 ^ r) + a * optF a d r (u + y - 2 ^ r) =
                d * optF a d r (u + y - 2 ^ r) := by rw [← Nat.add_mul, hda]
            have hlin2 : (d - a) * optF a d r y + a * optF a d r y = d * optF a d r y := by
              rw [← Nat.add_mul, hda]
            nlinarith
    refine ⟨?_, ?_⟩
    · intro x y hyx hx
      by_cases hxN : x ≤ 2 ^ r
      · have hyN : y ≤ 2 ^ r := by omega
        have hxy : x + y ≤ 2 ^ (r + 1) := by omega
        rw [optF_succ_le a d (r + 1) (x + y) hxy,
            optF_succ_le a d r x hxN, optF_succ_le a d r y hyN]
        have h1 := ih1 x y hyx hxN
        have hmul := Nat.mul_le_mul_left d h1
        nlinarith
      · by_cases hyN : 2 ^ r ≤ y
        · set u := x - 2 ^ r
          set v := y - 2 ^ r
          have hu : u ≤ 2 ^ r := by omega
          have hv : v ≤ u := by omega
          have hsub : x + y - 2 ^ (r + 1) = u + v := by omega
          rw [optF_succ_ge a d (r + 1) (x + y) (by omega), hsub, optF_full,
              optF_succ_ge a d r x (by omega), optF_succ_ge a d r y hyN]
          have h1 := ih1 u v hv hu
          have hmul := Nat.mul_le_mul_left a h1
          nlinarith
        · set u := x - 2 ^ r
          have hu : u ≤ 2 ^ r := by omega
          have hyN' : y ≤ 2 ^ r := by omega
          rw [optF_succ_ge a d r x (by omega), optF_succ_le a d r y hyN']
          have h2 := ih2 u y hu hyN'
          by_cases huy : u + y ≤ 2 ^ r
          · have hxy : x + y ≤ 2 ^ (r + 1) := by omega
            have hsub : x + y - 2 ^ r = u + y := by omega
            rw [optF_succ_le a d (r + 1) (x + y) hxy,
                optF_succ_ge a d r (x + y) (by omega), hsub]
            rw [if_pos huy] at h2
            have hmul := Nat.mul_le_mul_left (d * a) h2
            nlinarith
          · have hsub : x + y - 2 ^ (r + 1) = u + y - 2 ^ r := by omega
            rw [optF_succ_ge a d (r + 1) (x + y) (by omega), hsub, optF_full,
                optF_succ_le a d r (u + y - 2 ^ r) (by omega)]
            rw [if_neg huy] at h2
            have hmul := Nat.mul_le_mul_left (d * a) h2
            nlinarith
    · intro x y hx hy
      by_cases hyx : y ≤ x
      · exact hI2_symm x y hyx hx
      · have hxy : x ≤ y := by omega
        have h := hI2_symm y x hxy hy
        rw [Nat.add_comm y x, Nat.add_comm (optF a d (r + 1) y)] at h
        exact h

private def lift0E (r : Nat) : Finset (Fin r) ↪ Finset (Fin (r + 1)) :=
  ⟨fun T => T.map ⟨Fin.castSucc, Fin.castSucc_injective r⟩,
    fun T₁ T₂ h => by
      dsimp only at h
      ext i
      have hi : i.castSucc ∈ T₁.map ⟨Fin.castSucc, Fin.castSucc_injective r⟩ ↔
          i.castSucc ∈ T₂.map ⟨Fin.castSucc, Fin.castSucc_injective r⟩ := by rw [h]
      simpa using hi⟩

private lemma lift0E_apply (r : Nat) (T : Finset (Fin r)) :
    lift0E r T = T.map ⟨Fin.castSucc, Fin.castSucc_injective r⟩ := rfl

private lemma last_not_mem_lift0E (r : Nat) (T : Finset (Fin r)) :
    Fin.last r ∉ lift0E r T := by
  rw [lift0E_apply]
  simp [Fin.castSucc_ne_last]

private def lift1E (r : Nat) : Finset (Fin r) ↪ Finset (Fin (r + 1)) :=
  ⟨fun T => insert (Fin.last r) (lift0E r T),
    fun T₁ T₂ h => by
      have h1 := last_not_mem_lift0E r T₁
      have h2 := last_not_mem_lift0E r T₂
      have heq : lift0E r T₁ = lift0E r T₂ := by
        have := congrArg (fun X => X.erase (Fin.last r)) h
        rwa [Finset.erase_insert h1, Finset.erase_insert h2] at this
      exact (lift0E r).injective heq⟩

private lemma lift1E_apply (r : Nat) (T : Finset (Fin r)) :
    lift1E r T = insert (Fin.last r) (lift0E r T) := rfl

private lemma optF_eq_index_sum (a d : Nat) :
    ∀ (r k : Nat), k ≤ 2 ^ r →
      optF a d r k =
        ((Finset.univ : Finset (Finset (Fin r))).filter (fun S => idxFn S < k)).sum
          (fun S => a ^ S.card * d ^ (r - S.card))
  | 0, k, hk => by
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp [optF]
    · have huniv : ((Finset.univ : Finset (Finset (Fin 0))).filter (fun S => idxFn S < 1)) = {∅} := by
        ext S
        have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
        subst hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, iff_true]
        simp [idxFn]
      rw [huniv]; simp [optF]
  | r + 1, k, hk => by
    let Fset := (Finset.univ : Finset (Finset (Fin (r + 1)))).filter (fun S => idxFn S < k)
    let F0 := Fset.filter (fun S => Fin.last r ∉ S)
    let F1 := Fset.filter (fun S => Fin.last r ∈ S)
    have hdisj : Disjoint F0 F1 := by
      rw [Finset.disjoint_left]
      intro S h0 h1
      exact (Finset.mem_filter.mp h0).2 (Finset.mem_filter.mp h1).2
    have hunion : F0 ∪ F1 = Fset := by
      ext S
      simp only [F0, F1, Finset.mem_union, Finset.mem_filter]
      tauto
    have hsplit : Fset.sum (fun S => a ^ S.card * d ^ (r + 1 - S.card)) =
        F0.sum (fun S => a ^ S.card * d ^ (r + 1 - S.card)) +
        F1.sum (fun S => a ^ S.card * d ^ (r + 1 - S.card)) := by
      rw [← hunion, Finset.sum_union hdisj]
    have hidx0 : ∀ T : Finset (Fin r), idxFn (lift0E r T) = idxFn T := by
      intro T; unfold idxFn; rw [lift0E_apply]; simp
    have hidx1 : ∀ T : Finset (Fin r), idxFn (lift1E r T) = idxFn T + 2 ^ r := by
      intro T
      have hnot := last_not_mem_lift0E r T
      unfold idxFn
      rw [lift1E_apply, Finset.sum_insert hnot]
      have h0 : (lift0E r T).sum (fun j : Fin (r + 1) => 2 ^ j.val) = idxFn T := hidx0 T
      rw [h0, Fin.val_last, Nat.add_comm]; rfl
    have hcard0 : ∀ T : Finset (Fin r), (lift0E r T).card = T.card := by
      intro T; rw [lift0E_apply, Finset.card_map]
    have hcard1 : ∀ T : Finset (Fin r), (lift1E r T).card = T.card + 1 := by
      intro T
      rw [lift1E_apply, Finset.card_insert_of_notMem (last_not_mem_lift0E r T), hcard0]
    have hF0_eq : F0 = ((Finset.univ : Finset (Finset (Fin r))).filter
        (fun T => idxFn T < min k (2 ^ r))).map (lift0E r) := by
      ext S
      simp only [F0, Fset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro ⟨hSk, hnot⟩
        let T : Finset (Fin r) := Finset.univ.filter (fun i => i.castSucc ∈ S)
        have hlift : lift0E r T = S := by
          ext j
          refine Fin.lastCases ?_ ?_ j
          · simp [last_not_mem_lift0E, hnot]
          · intro i; rw [lift0E_apply]; simp [T]
        refine ⟨T, ?_, hlift⟩
        rw [← hidx0 T, hlift]
        exact lt_min hSk (by rw [← hlift, hidx0 T]; exact idxFn_lt T)
      · rintro ⟨T, hT, rfl⟩
        refine ⟨?_, last_not_mem_lift0E r T⟩
        rw [hidx0 T]
        exact lt_of_lt_of_le hT (Nat.min_le_left _ _)
    have hF1_eq : F1 = ((Finset.univ : Finset (Finset (Fin r))).filter
        (fun T => idxFn T < k - 2 ^ r)).map (lift1E r) := by
      ext S
      simp only [F1, Fset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro ⟨hSk, hmem⟩
        let T : Finset (Fin r) := Finset.univ.filter (fun i => i.castSucc ∈ S)
        have hlift : lift1E r T = S := by
          ext j
          refine Fin.lastCases ?_ ?_ j
          · rw [lift1E_apply]; simp [hmem]
          · intro i; rw [lift1E_apply, lift0E_apply]; simp [T, Fin.castSucc_ne_last]
        refine ⟨T, ?_, hlift⟩
        have hi1 := hidx1 T
        rw [hlift] at hi1
        omega
      · rintro ⟨T, hT, rfl⟩
        refine ⟨?_, by rw [lift1E_apply]; exact Finset.mem_insert_self _ _⟩
        rw [hidx1 T]
        omega
    have hS0 : F0.sum (fun S => a ^ S.card * d ^ (r + 1 - S.card)) =
        d * ((Finset.univ : Finset (Finset (Fin r))).filter
          (fun T => idxFn T < min k (2 ^ r))).sum (fun T => a ^ T.card * d ^ (r - T.card)) := by
      rw [hF0_eq, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [hcard0 T]
      have hle : T.card ≤ r := by
        have := Finset.card_le_univ T; simpa using this
      have hsub : r + 1 - T.card = (r - T.card) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    have hS1 : F1.sum (fun S => a ^ S.card * d ^ (r + 1 - S.card)) =
        a * ((Finset.univ : Finset (Finset (Fin r))).filter
          (fun T => idxFn T < k - 2 ^ r)).sum (fun T => a ^ T.card * d ^ (r - T.card)) := by
      rw [hF1_eq, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [hcard1 T]
      have hsub : r + 1 - (T.card + 1) = r - T.card := by omega
      rw [hsub, pow_succ]
      ring
    rw [hsplit, hS0, hS1]
    by_cases hkle : k ≤ 2 ^ r
    · rw [optF_succ_le a d r k hkle]
      have hmin : min k (2 ^ r) = k := Nat.min_eq_left hkle
      have hsub : k - 2 ^ r = 0 := by omega
      simp only [hmin, hsub, Nat.not_lt_zero, Finset.filter_false,
        Finset.sum_empty, Nat.mul_zero, Nat.add_zero]
      rw [optF_eq_index_sum a d r k hkle]
    · rw [optF_succ_ge a d r k (by omega)]
      have hmin : min k (2 ^ r) = 2 ^ r := Nat.min_eq_right (by omega)
      have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
      simp only [hmin]
      rw [optF_eq_index_sum a d r (2 ^ r) (le_refl _),
          optF_eq_index_sum a d r (k - 2 ^ r) (by omega)]

private lemma optF_le_downSet_sum {a d : Nat} (had : a ≤ d) :
    ∀ (r : Nat) (M : Finset (Finset (Fin r))), isDownSet M →
      optF a d r M.card ≤ M.sum (fun S => a ^ S.card * d ^ (r - S.card))
  | 0, M, _ => by
    have hle : M.card ≤ 1 := by
      have := Finset.card_le_univ M; simpa using this
    by_cases h0 : M.card = 0
    · rw [h0]; simp [optF]
    · have h1 : M.card = 1 := by omega
      have hM : M = {∅} := by
        rcases Finset.card_eq_one.mp h1 with ⟨S, rfl⟩
        rw [Finset.eq_empty_of_isEmpty S]
      rw [hM]; simp [optF]
  | r + 1, M, hM => by
    let M0 : Finset (Finset (Fin r)) := Finset.univ.filter (fun T => lift0E r T ∈ M)
    let M1 : Finset (Finset (Fin r)) := Finset.univ.filter (fun T => lift1E r T ∈ M)
    have hdown0 : isDownSet M0 := by
      intro T hT U hUT
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM (lift0E r T) (Finset.mem_filter.mp hT).2 (lift0E r U) ?_⟩
      intro x hx
      rw [lift0E_apply] at hx ⊢
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_map.mpr ⟨i, hUT hi, rfl⟩
    have hdown1 : isDownSet M1 := by
      intro T hT U hUT
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM (lift1E r T) (Finset.mem_filter.mp hT).2 (lift1E r U) ?_⟩
      intro x hx
      rw [lift1E_apply, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · rw [lift0E_apply] at hx ⊢
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        exact Or.inr (Finset.mem_map.mpr ⟨i, hUT hi, rfl⟩)
    have hsub10 : M1 ⊆ M0 := by
      intro T hT
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hM (lift1E r T) (Finset.mem_filter.mp hT).2 (lift0E r T) (by rw [lift1E_apply]; exact Finset.subset_insert _ _)⟩
    have hdisj : Disjoint (M0.map (lift0E r)) (M1.map (lift1E r)) := by
      rw [Finset.disjoint_left]
      intro S h0 h1
      rcases Finset.mem_map.mp h0 with ⟨T0, _, rfl⟩
      rcases Finset.mem_map.mp h1 with ⟨T1, _, heq⟩
      have hmem : Fin.last r ∈ lift1E r T1 := by rw [lift1E_apply]; exact Finset.mem_insert_self _ _
      rw [heq] at hmem
      exact last_not_mem_lift0E r T0 hmem
    have hunion : M0.map (lift0E r) ∪ M1.map (lift1E r) = M := by
      ext S
      simp only [Finset.mem_union, Finset.mem_map, M0, M1, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩) <;> exact hT
      · intro hSM
        let T : Finset (Fin r) := Finset.univ.filter (fun i => i.castSucc ∈ S)
        by_cases hlast : Fin.last r ∈ S
        · right
          have hlift : lift1E r T = S := by
            ext j; refine Fin.lastCases ?_ ?_ j
            · rw [lift1E_apply]; simp [hlast]
            · intro i; rw [lift1E_apply, lift0E_apply]; simp [T, Fin.castSucc_ne_last]
          exact ⟨T, hlift.symm ▸ hSM, hlift⟩
        · left
          have hlift : lift0E r T = S := by
            ext j; refine Fin.lastCases ?_ ?_ j
            · simp [last_not_mem_lift0E, hlast]
            · intro i; rw [lift0E_apply]; simp [T]
          exact ⟨T, hlift.symm ▸ hSM, hlift⟩
    have hcard_eq : M.card = M0.card + M1.card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
    have hsum_eq : M.sum (fun S => a ^ S.card * d ^ (r + 1 - S.card)) =
        d * M0.sum (fun T => a ^ T.card * d ^ (r - T.card)) +
        a * M1.sum (fun T => a ^ T.card * d ^ (r - T.card)) := by
      rw [← hunion, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map,
        Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl (fun T _ => ?_)
        have hc : (lift0E r T).card = T.card := by rw [lift0E_apply, Finset.card_map]
        have hle : T.card ≤ r := by have := Finset.card_le_univ T; simpa using this
        have hsub : r + 1 - T.card = (r - T.card) + 1 := by omega
        rw [hc, hsub, pow_succ]; ring
      · refine Finset.sum_congr rfl (fun T _ => ?_)
        have hc : (lift1E r T).card = T.card + 1 := by
          rw [lift1E_apply, Finset.card_insert_of_notMem (last_not_mem_lift0E r T),
              lift0E_apply, Finset.card_map]
        have hsub : r + 1 - (T.card + 1) = r - T.card := by omega
        rw [hc, hsub, pow_succ]; ring
    rw [hcard_eq, hsum_eq]
    have h0le : M0.card ≤ 2 ^ r := by
      have := Finset.card_le_univ M0; simpa using this
    have h10 : M1.card ≤ M0.card := Finset.card_le_card hsub10
    have hih0 := optF_le_downSet_sum had r M0 hdown0
    have hih1 := optF_le_downSet_sum had r M1 hdown1
    calc
      optF a d (r + 1) (M0.card + M1.card)
          ≤ d * optF a d r M0.card + a * optF a d r M1.card := (optF_pair had r).1 _ _ h10 h0le
      _ ≤ d * M0.sum (fun T => a ^ T.card * d ^ (r - T.card)) +
          a * M1.sum (fun T => a ^ T.card * d ^ (r - T.card)) :=
        Nat.add_le_add (Nat.mul_le_mul_left d hih0) (Nat.mul_le_mul_left a hih1)

private lemma pow_weight_mono {r a d : Nat} (hda : d ≤ a) {s₁ s₂ : Nat}
    (hs : s₁ ≤ s₂) (hs2 : s₂ ≤ r) :
    a ^ s₁ * d ^ (r - s₁) ≤ a ^ s₂ * d ^ (r - s₂) := by
  have h1 : s₂ = s₁ + (s₂ - s₁) := by omega
  have h2 : r - s₁ = (r - s₂) + (s₂ - s₁) := by omega
  have hpow : d ^ (s₂ - s₁) ≤ a ^ (s₂ - s₁) := Nat.pow_le_pow_left hda _
  calc
    a ^ s₁ * d ^ (r - s₁)
        = a ^ s₁ * (d ^ (r - s₂) * d ^ (s₂ - s₁)) := by rw [h2, pow_add]
    _ = (a ^ s₁ * d ^ (r - s₂)) * d ^ (s₂ - s₁) := by ring
    _ ≤ (a ^ s₁ * d ^ (r - s₂)) * a ^ (s₂ - s₁) := Nat.mul_le_mul_left _ hpow
    _ = (a ^ s₁ * a ^ (s₂ - s₁)) * d ^ (r - s₂) := by ring
    _ = a ^ s₂ * d ^ (r - s₂) := by rw [← pow_add, ← h1]

theorem main_proof :
    ∀ (r k a b c : Nat), b ≤ a → k ≤ 2 ^ r →
      let Kind := Finset (Fin r)
      let kinds := (Finset.univ : Finset Kind)
      let positions := (Finset.univ : Finset (Fin r))
      let omega := (Finset.univ : Finset (Fin r → Fin (a + b + c)))
      let sees := fun (M : Finset Kind) => (omega.filter (fun x =>
        M.toList.any (fun S => positions.toList.all (fun j =>
          if (x j).val < a then decide (j ∈ S) else
          if (x j).val < a + b then decide (j ∉ S) else true)))).card
      let index := fun (S : Kind) => S.sum (fun j => 2 ^ j.val)
      let weightOrder := fun (S : Kind) => (kinds.filter (fun V =>
        V.card < S.card ∨ (V.card = S.card ∧ index V < index S))).card
      let best := kinds.filter (fun S => (if a ≤ b + c then index S else weightOrder S) < k)
      best.card = k ∧ sees best =
        best.sum (fun S => a ^ S.card * (b + c) ^ (r - S.card)) ∧
        ∀ M : Finset Kind, M.card = k → sees best ≤ sees M := by
  intro r k a b c hba hk
  dsimp only
  let best : Finset (Finset (Fin r)) :=
    (Finset.univ : Finset (Finset (Fin r))).filter (fun S =>
      (if a ≤ b + c then idxFn S else wOrd S) < k)
  have hbest_card : best.card = k := by
    by_cases hle : a ≤ b + c
    · have heq : best = (Finset.univ : Finset (Finset (Fin r))).filter (fun S => idxFn S < k) := by
        simp [best, hle]
      rw [heq]
      exact card_filter_lt_of_inj_lt hk idxFn (fun _ _ => idxFn_inj) idxFn_lt
    · have heq : best = (Finset.univ : Finset (Finset (Fin r))).filter (fun S => wOrd S < k) := by
        simp [best, hle]
      rw [heq]
      exact card_filter_lt_of_inj_lt hk wOrd (fun _ _ => wOrd_inj) wOrd_lt
  have hbest_down : isDownSet best := by
    intro S hS T hTS
    simp only [best, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    by_cases hle : a ≤ b + c
    · simp only [hle, ↓reduceIte] at hS ⊢
      exact lt_of_le_of_lt (idxFn_mono hTS) hS
    · simp only [hle, ↓reduceIte] at hS ⊢
      by_cases hTeq : T = S
      · rwa [hTeq]
      · have hlt : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTeq⟩)
        exact lt_trans (wOrd_lt_of_ltW (Or.inl hlt)) hS
  have hbest_sees : seesFn a b c best = best.sum (fun S => a ^ S.card * (b + c) ^ (r - S.card)) :=
    seesFn_eq_sum_of_downSet hbest_down
  refine ⟨hbest_card, hbest_sees, ?_⟩
  intro M hMk
  change seesFn a b c best ≤ seesFn a b c M
  rcases exists_downSet_le (a := a) (b := b) (c := c) hba M with ⟨M', hdown', hcard', hsees'⟩
  have hM'k : M'.card = k := hcard'.trans hMk
  rw [hbest_sees]
  refine le_trans ?_ hsees'
  rw [seesFn_eq_sum_of_downSet hdown']
  by_cases hle : a ≤ b + c
  · have hbest_eq : best = (Finset.univ : Finset (Finset (Fin r))).filter (fun S => idxFn S < k) := by
      simp [best, hle]
    rw [hbest_eq, ← optF_eq_index_sum a (b + c) r k hk, ← hM'k]
    exact optF_le_downSet_sum hle r M' hdown'
  · have hda : b + c ≤ a := by omega
    have hbest_eq : best = (Finset.univ : Finset (Finset (Fin r))).filter (fun S => wOrd S < k) := by
      simp [best, hle]
    let w : Finset (Fin r) → Nat := fun S => a ^ S.card * (b + c) ^ (r - S.card)
    change best.sum w ≤ M'.sum w
    have hdisj_is : ∀ A B : Finset (Finset (Fin r)), Disjoint (A ∩ B) (A \ B) := fun A B =>
      Finset.disjoint_left.mpr (fun x h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2)
    have hunion_is : ∀ A B : Finset (Finset (Fin r)), (A ∩ B) ∪ (A \ B) = A := fun A B => by
      ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hsplit1 : best.sum w = (best ∩ M').sum w + (best \ M').sum w := by
      rw [← Finset.sum_union (hdisj_is best M'), hunion_is]
    have hsplit2 : M'.sum w = (best ∩ M').sum w + (M' \ best).sum w := by
      rw [Finset.inter_comm, ← Finset.sum_union (hdisj_is M' best), hunion_is]
    rw [hsplit1, hsplit2]
    refine Nat.add_le_add_left ?_ _
    by_cases hemp : (best \ M').Nonempty
    · have hcard_eq : (best \ M').card = (M' \ best).card := by
        have h1 : (best ∩ M').card + (best \ M').card = best.card := by
          rw [← Finset.card_union_of_disjoint (hdisj_is best M'), hunion_is]
        have h2 : (M' ∩ best).card + (M' \ best).card = M'.card := by
          rw [← Finset.card_union_of_disjoint (hdisj_is M' best), hunion_is]
        rw [Finset.inter_comm] at h2
        omega
      have hemp2 : (M' \ best).Nonempty := Finset.card_pos.mp (by rw [← hcard_eq]; exact hemp.card_pos)
      rcases Finset.exists_max_image (best \ M') w hemp with ⟨Smax, hSmax, hmax⟩
      rcases Finset.exists_min_image (M' \ best) w hemp2 with ⟨Tmin, hTmin, hmin⟩
      have hSbest : Smax ∈ best := (Finset.mem_sdiff.mp hSmax).1
      have hTnot : Tmin ∉ best := (Finset.mem_sdiff.mp hTmin).2
      rw [hbest_eq] at hSbest hTnot
      have hSlt : wOrd Smax < k := (Finset.mem_filter.mp hSbest).2
      have hTge : ¬ (wOrd Tmin < k) := fun h => hTnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hcard_le : Smax.card ≤ Tmin.card := by
        by_contra hgt
        have hltW : ltW Tmin Smax := Or.inl (by omega)
        have hord := wOrd_lt_of_ltW hltW
        omega
      have hTle : Tmin.card ≤ r := by have := Finset.card_le_univ Tmin; simpa using this
      have hw_le : w Smax ≤ w Tmin := pow_weight_mono hda hcard_le hTle
      calc
        (best \ M').sum w ≤ (best \ M').sum (fun _ => w Smax) :=
          Finset.sum_le_sum (fun S hS => hmax S hS)
        _ = (best \ M').card * w Smax := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (M' \ best).card * w Tmin := by
          rw [hcard_eq]; exact Nat.mul_le_mul_left _ hw_le
        _ = (M' \ best).sum (fun _ => w Tmin) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (M' \ best).sum w := Finset.sum_le_sum (fun T hT => hmin T hT)
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty]
      exact Nat.zero_le _

end PEqualNP.Outside.L_lib_1165

theorem PEqualNP.Outside.L_lib_1165 :
∀ (r k a b c : Nat), b ≤ a → k ≤ 2 ^ r →
  let Kind := Finset (Fin r)
  let kinds := (Finset.univ : Finset Kind)
  let positions := (Finset.univ : Finset (Fin r))
  let omega := (Finset.univ : Finset (Fin r → Fin (a + b + c)))
  let sees := fun (M : Finset Kind) => (omega.filter (fun x =>
    M.toList.any (fun S => positions.toList.all (fun j =>
      if (x j).val < a then decide (j ∈ S) else
      if (x j).val < a + b then decide (j ∉ S) else true)))).card
  let index := fun (S : Kind) => S.sum (fun j => 2 ^ j.val)
  let weightOrder := fun (S : Kind) => (kinds.filter (fun V =>
    V.card < S.card ∨ (V.card = S.card ∧ index V < index S))).card
  let best := kinds.filter (fun S => (if a ≤ b + c then index S else weightOrder S) < k)
  best.card = k ∧ sees best =
    best.sum (fun S => a ^ S.card * (b + c) ^ (r - S.card)) ∧
    ∀ M : Finset Kind, M.card = k → sees best ≤ sees M :=
  PEqualNP.Outside.L_lib_1165.main_proof
