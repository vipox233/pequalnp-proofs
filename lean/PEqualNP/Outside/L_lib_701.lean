import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_701_aux

private abbrev K := ZMod 2

private lemma zmod2_add_self (x : K) : x + x = 0 := by
  revert x; decide

private lemma zmod2_eq_zero_or_one (x : K) : x = 0 ∨ x = 1 := by
  revert x; decide

private lemma zmod2_add_one_add_one (x : K) : x + 1 + 1 = x := by
  revert x; decide

private lemma zmod2_natCast_eq_ite (k : ℕ) : (k : K) = if Odd k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Nat.cast_succ, ih]
      by_cases hm : Odd m
      · have hns : ¬ Odd (m + 1) := by
          rcases hm with ⟨t, rfl⟩
          rintro ⟨u, hu⟩
          omega
        simp [hm, hns]
        decide
      · have hs : Odd (m + 1) := by
          rw [Nat.not_odd_iff_even] at hm
          rcases hm with ⟨t, rfl⟩
          exact ⟨t, by omega⟩
        simp [hm, hs]

private lemma sum_prod_univ_eq {w : ℕ} (T : Finset (Fin w)) :
    (∑ y : Fin w → K, ∏ b ∈ T, y b) = if T = Finset.univ then (1 : K) else 0 := by
  by_cases hT : T = Finset.univ
  · subst hT
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single (fun _ : Fin w => (1 : K))]
    · simp
    · intro y _ hy
      have hex : ∃ b : Fin w, y b ≠ 1 := by
        by_contra hall
        push Not at hall
        exact hy (funext hall)
      rcases hex with ⟨b, hb⟩
      have hb0 : y b = 0 := by
        rcases zmod2_eq_zero_or_one (y b) with h0 | h1
        · exact h0
        · exact absurd h1 hb
      exact Finset.prod_eq_zero (Finset.mem_univ b) hb0
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [hT, ↓reduceIte]
    have hex : ∃ b0 : Fin w, b0 ∉ T := by
      by_contra hall
      push Not at hall
      apply hT
      ext b
      simp [hall b]
    rcases hex with ⟨b0, hb0⟩
    let S0 : Finset (Fin w → K) := Finset.univ.filter (fun y => y b0 = 0)
    let S1 : Finset (Fin w → K) := Finset.univ.filter (fun y => y b0 = 1)
    have hdisj : Disjoint S0 S1 := by
      refine Finset.disjoint_left.2 fun y h0 h1 => ?_
      have e0 : y b0 = 0 := (Finset.mem_filter.1 h0).2
      have e1 : y b0 = 1 := (Finset.mem_filter.1 h1).2
      rw [e0] at e1
      exact absurd e1 (by decide)
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext y
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using zmod2_eq_zero_or_one (y b0)
    have hflip_inv : ∀ y : Fin w → K,
        Function.update (Function.update y b0 (y b0 + 1)) b0
          (Function.update y b0 (y b0 + 1) b0 + 1) = y := by
      intro y
      funext b
      by_cases hb : b = b0
      · subst hb; simp [zmod2_add_one_add_one]
      · simp [hb]
    have hsum_eq : ∑ y ∈ S0, (∏ b ∈ T, y b) = ∑ y ∈ S1, (∏ b ∈ T, y b) := by
      refine Finset.sum_bij (fun y _ => Function.update y b0 (y b0 + 1)) ?_ ?_ ?_ ?_
      · intro y hy
        have e0 : y b0 = 0 := (Finset.mem_filter.1 hy).2
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        simp [e0]
      · intro y1 _ y2 _ heq
        have h := congrArg (fun u : Fin w → K => Function.update u b0 (u b0 + 1)) heq
        rw [hflip_inv, hflip_inv] at h
        exact h
      · intro y hy
        have e1 : y b0 = 1 := (Finset.mem_filter.1 hy).2
        refine ⟨Function.update y b0 (y b0 + 1), ?_, hflip_inv y⟩
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        simp [e1]
        decide
      · intro y _
        refine Finset.prod_congr rfl fun b hb => ?_
        have hne : b ≠ b0 := fun heq => hb0 (heq ▸ hb)
        simp [hne]
    rw [← hunion, Finset.sum_union hdisj, hsum_eq]
    exact zmod2_add_self _

private def blockFiber (w : ℕ) (c : K) : Finset (Fin w → K) :=
  Finset.univ.filter (fun y => (∏ b : Fin w, y b) = c)

private lemma sum_blockFiber_prod {w : ℕ} (c : K) (T : Finset (Fin w)) :
    (∑ y ∈ blockFiber w c, ∏ b ∈ T, y b) = if T = Finset.univ then c else 1 := by
  have hones : ∀ y : Fin w → K, (∏ b : Fin w, y b) = 1 ↔ y = fun _ => 1 := by
    intro y
    constructor
    · intro h
      funext b
      by_contra hne
      have hb0 : y b = 0 := by
        rcases zmod2_eq_zero_or_one (y b) with h0 | h1
        · exact h0
        · exact absurd h1 hne
      have h0 : (∏ i : Fin w, y i) = 0 := Finset.prod_eq_zero (Finset.mem_univ b) hb0
      rw [h0] at h
      exact absurd h (by decide)
    · intro hy
      subst hy
      simp
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · have hbf0 : blockFiber w 0 = Finset.univ.erase (fun _ : Fin w => (1 : K)) := by
      ext y
      simp only [blockFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]
      constructor
      · intro h0 hy
        have h1 : (∏ b : Fin w, y b) = 1 := (hones y).2 hy
        rw [h0] at h1
        exact absurd h1 (by decide)
      · intro hne
        rcases zmod2_eq_zero_or_one (∏ b : Fin w, y b) with h0 | h1
        · exact h0
        · exact absurd ((hones y).1 h1) hne
    rw [hbf0]
    have hsplit := Finset.add_sum_erase Finset.univ (fun y : Fin w → K => ∏ b ∈ T, y b)
      (Finset.mem_univ (fun _ : Fin w => (1 : K)))
    have h1term : (∏ b ∈ T, (1 : K)) = 1 := by simp
    rw [h1term, sum_prod_univ_eq T] at hsplit
    have hadd : (∑ y ∈ Finset.univ.erase (fun _ : Fin w => (1 : K)), ∏ b ∈ T, y b) =
        1 + (if T = Finset.univ then (1 : K) else 0) := by
      have h := congrArg (fun z : K => 1 + z) hsplit
      rw [← add_assoc, zmod2_add_self, zero_add] at h
      exact h
    rw [hadd]
    by_cases hT : T = Finset.univ
    · simp [hT]; decide
    · simp [hT]
  · have hbf1 : blockFiber w 1 = {fun _ : Fin w => (1 : K)} := by
      ext y
      simp only [blockFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact hones y
    rw [hbf1, Finset.sum_singleton]
    by_cases hT : T = Finset.univ <;> simp [hT]

private def slice {n : ℕ} {width : Fin n → ℕ}
    (m : Finset ((i : Fin n) × Fin (width i))) (i : Fin n) : Finset (Fin (width i)) :=
  Finset.univ.filter (fun b => (⟨i, b⟩ : (i : Fin n) × Fin (width i)) ∈ m)

private def fullBlocks {n : ℕ} {width : Fin n → ℕ}
    (m : Finset ((i : Fin n) × Fin (width i))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => slice m i = Finset.univ)

private def liftSet {n : ℕ} (width : Fin n → ℕ) (s : Finset (Fin n)) :
    Finset ((i : Fin n) × Fin (width i)) :=
  s.sigma (fun i => (Finset.univ : Finset (Fin (width i))))

private lemma liftSet_card {n : ℕ} (width : Fin n → ℕ) (s : Finset (Fin n)) :
    (liftSet width s).card = ∑ i ∈ s, width i := by
  unfold liftSet
  rw [Finset.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

private lemma liftSet_injective {n : ℕ} {width : Fin n → ℕ} (hw : ∀ i, 0 < width i) :
    Function.Injective (liftSet width) := by
  intro s1 s2 heq
  ext i
  have hmem : (⟨i, ⟨0, hw i⟩⟩ : (i : Fin n) × Fin (width i)) ∈ liftSet width s1 ↔
      (⟨i, ⟨0, hw i⟩⟩ : (i : Fin n) × Fin (width i)) ∈ liftSet width s2 := by
    rw [heq]
  simpa [liftSet] using hmem

private lemma prod_liftSet {n : ℕ} {width : Fin n → ℕ}
    (x : ((i : Fin n) × Fin (width i)) → K) (s : Finset (Fin n)) :
    (∏ u ∈ liftSet width s, x u) = ∏ i ∈ s, ∏ b : Fin (width i), x ⟨i, b⟩ := by
  unfold liftSet
  rw [Finset.prod_sigma]

private lemma liftSet_fullBlocks_subset {n : ℕ} {width : Fin n → ℕ}
    (m : Finset ((i : Fin n) × Fin (width i))) :
    liftSet width (fullBlocks m) ⊆ m := by
  intro u hu
  rcases u with ⟨i, b⟩
  have hi : i ∈ fullBlocks m := (Finset.mem_sigma.1 hu).1
  have hfull : slice m i = Finset.univ := (Finset.mem_filter.1 hi).2
  have hb : b ∈ slice m i := by rw [hfull]; exact Finset.mem_univ b
  exact (Finset.mem_filter.1 hb).2

private lemma prod_monomial_split {n : ℕ} {width : Fin n → ℕ}
    (m : Finset ((i : Fin n) × Fin (width i)))
    (x : ((i : Fin n) × Fin (width i)) → K) :
    (∏ u ∈ m, x u) = ∏ i : Fin n, ∏ b ∈ slice m i, x ⟨i, b⟩ := by
  have hm : m = Finset.univ.sigma (fun i => slice m i) := by
    ext u
    rcases u with ⟨i, b⟩
    simp [slice]
  conv_lhs => rw [hm]
  rw [Finset.prod_sigma]

private lemma sum_fiber_monomial {n : ℕ} {width : Fin n → ℕ}
    (m : Finset ((i : Fin n) × Fin (width i))) (v : Fin n → K) :
    let fiber := (Finset.univ : Finset (((i : Fin n) × Fin (width i)) → K)).filter
      (fun x => (fun i => ∏ b : Fin (width i), x ⟨i, b⟩) = v)
    (∑ x ∈ fiber, ∏ u ∈ m, x u) = ∏ i ∈ fullBlocks m, v i := by
  intro fiber
  let P : Finset ((i : Fin n) → Fin (width i) → K) :=
    Fintype.piFinset (fun i => blockFiber (width i) (v i))
  have hbij : (∑ x ∈ fiber, ∏ u ∈ m, x u) =
      ∑ g ∈ P, ∏ i : Fin n, ∏ b ∈ slice m i, g i b := by
    refine Finset.sum_bij (fun x _ i b => x ⟨i, b⟩) ?_ ?_ ?_ ?_
    · intro x hx
      have hv : (fun i => ∏ b : Fin (width i), x ⟨i, b⟩) = v := (Finset.mem_filter.1 hx).2
      rw [Fintype.mem_piFinset]
      intro i
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      exact congrFun hv i
    · intro x1 _ x2 _ heq
      funext u
      rcases u with ⟨i, b⟩
      exact congrFun (congrFun heq i) b
    · intro g hg
      rw [Fintype.mem_piFinset] at hg
      refine ⟨fun u => g u.1 u.2, ?_, rfl⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      funext i
      exact (Finset.mem_filter.1 (hg i)).2
    · intro x _
      exact prod_monomial_split m x
  rw [hbij]
  have hprod_sum :
      (∑ g ∈ P, ∏ i : Fin n, ∏ b ∈ slice m i, g i b) =
        ∏ i : Fin n, ∑ y ∈ blockFiber (width i) (v i), ∏ b ∈ slice m i, y b := by
    let h : (i : Fin n) → (Fin (width i) → K) → K :=
      fun i y => if y ∈ blockFiber (width i) (v i) then ∏ b ∈ slice m i, y b else 0
    have hrhs : (∏ i : Fin n, ∑ y : Fin (width i) → K, h i y) =
        ∏ i : Fin n, ∑ y ∈ blockFiber (width i) (v i), ∏ b ∈ slice m i, y b := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [h, Finset.sum_ite_mem]
    have hlhs : (∑ g : (i : Fin n) → Fin (width i) → K, ∏ i : Fin n, h i (g i)) =
        ∑ g ∈ P, ∏ i : Fin n, ∏ b ∈ slice m i, g i b := by
      rw [← Finset.sum_subset (Finset.subset_univ P)]
      · refine Finset.sum_congr rfl fun g hg => ?_
        rw [Fintype.mem_piFinset] at hg
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [h, hg i]
      · intro g _ hgP
        rw [Fintype.mem_piFinset] at hgP
        push Not at hgP
        rcases hgP with ⟨i0, hi0⟩
        refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
        simp [h, hi0]
    rw [← hlhs, ← hrhs]
    exact (Fintype.prod_sum h).symm
  rw [hprod_sum]
  have hterm : ∀ i : Fin n,
      (∑ y ∈ blockFiber (width i) (v i), ∏ b ∈ slice m i, y b) =
        if i ∈ fullBlocks m then v i else 1 := by
    intro i
    rw [sum_blockFiber_prod]
    simp [fullBlocks]
  simp_rw [hterm]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

private lemma sum_fiber_one {n : ℕ} {width : Fin n → ℕ} (hw : ∀ i, 0 < width i) (v : Fin n → K) :
    let fiber := (Finset.univ : Finset (((i : Fin n) × Fin (width i)) → K)).filter
      (fun x => (fun i => ∏ b : Fin (width i), x ⟨i, b⟩) = v)
    (∑ _x ∈ fiber, (1 : K)) = 1 := by
  intro fiber
  have h := sum_fiber_monomial (width := width) (∅ : Finset ((i : Fin n) × Fin (width i))) v
  dsimp only at h
  have hfull : fullBlocks (width := width) (∅ : Finset ((i : Fin n) × Fin (width i))) = ∅ := by
    ext i
    simp only [fullBlocks, slice, Finset.notMem_empty, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_false]
    intro heq
    have hmem : (⟨0, hw i⟩ : Fin (width i)) ∈ Finset.univ.filter (fun _ : Fin (width i) => False) := by
      rw [heq]; exact Finset.mem_univ _
    simp at hmem
  simpa [hfull] using h

end PEqualNP.Outside.L_lib_701_aux

theorem PEqualNP.Outside.L_lib_701 :
∀ (n d : Nat) (width : Fin n → Nat), (∀ i, 0 < width i) →
  let K := ZMod 2
  let J := (i : Fin n) × Fin (width i)
  let V := Fin n → K
  let flags := fun (x : J → K) (i : Fin n) => ∏ b : Fin (width i), x ⟨i,b⟩
  ∀ (D : Finset V) (f : V → K),
    (∃ raw : Finset (Finset J), (∀ m ∈ raw, m.card ≤ d) ∧
      ∀ x, flags x ∈ D → (∑ m ∈ raw, ∏ u ∈ m, x u) = f (flags x)) ↔
    (∃ outer : Finset (Finset (Fin n)),
      (∀ s ∈ outer, (∑ i ∈ s, width i) ≤ d) ∧
      ∀ v ∈ D, (∑ s ∈ outer, ∏ i ∈ s, v i) = f v) := by
  intro n d width hw K J V flags D f
  constructor
  · rintro ⟨raw, hdeg, heval⟩
    let outer : Finset (Finset (Fin n)) :=
      (raw.image (PEqualNP.Outside.L_lib_701_aux.fullBlocks (width := width))).filter
        (fun s => Odd (raw.filter (fun m => PEqualNP.Outside.L_lib_701_aux.fullBlocks m = s)).card)
    refine ⟨outer, ?_, ?_⟩
    · intro s hs
      have hs_img := (Finset.mem_filter.1 hs).1
      rcases Finset.mem_image.1 hs_img with ⟨m, hm, rfl⟩
      rw [← PEqualNP.Outside.L_lib_701_aux.liftSet_card width]
      exact le_trans (Finset.card_le_card (PEqualNP.Outside.L_lib_701_aux.liftSet_fullBlocks_subset m))
        (hdeg m hm)
    · intro v hvD
      let fiber := (Finset.univ : Finset (J → K)).filter (fun x => flags x = v)
      have hsum_f : (∑ x ∈ fiber, f (flags x)) = f v := by
        have hcongr : (∑ x ∈ fiber, f (flags x)) = ∑ _x ∈ fiber, f v := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [(Finset.mem_filter.1 hx).2]
        rw [hcongr]
        have hmul : (∑ _x ∈ fiber, f v) = (∑ _x ∈ fiber, (1 : K)) * f v := by
          rw [Finset.sum_mul]
          simp
        rw [hmul, PEqualNP.Outside.L_lib_701_aux.sum_fiber_one hw v, one_mul]
      have hsum_raw : (∑ x ∈ fiber, ∑ m ∈ raw, ∏ u ∈ m, x u) = f v := by
        rw [← hsum_f]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hfx : flags x = v := (Finset.mem_filter.1 hx).2
        exact heval x (hfx ▸ hvD)
      rw [Finset.sum_comm] at hsum_raw
      have hraw_full : (∑ m ∈ raw, ∏ i ∈ PEqualNP.Outside.L_lib_701_aux.fullBlocks m, v i) = f v := by
        rw [← hsum_raw]
        refine Finset.sum_congr rfl fun m _ => ?_
        exact (PEqualNP.Outside.L_lib_701_aux.sum_fiber_monomial m v).symm
      rw [← hraw_full]
      have hmaps : ∀ m ∈ raw, PEqualNP.Outside.L_lib_701_aux.fullBlocks m ∈
          raw.image (PEqualNP.Outside.L_lib_701_aux.fullBlocks (width := width)) :=
        fun m hm => Finset.mem_image_of_mem _ hm
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      have hinner : ∀ s ∈ raw.image (PEqualNP.Outside.L_lib_701_aux.fullBlocks (width := width)),
          (∑ m ∈ raw.filter (fun m => PEqualNP.Outside.L_lib_701_aux.fullBlocks m = s),
            ∏ i ∈ PEqualNP.Outside.L_lib_701_aux.fullBlocks m, v i) =
          if Odd (raw.filter (fun m => PEqualNP.Outside.L_lib_701_aux.fullBlocks m = s)).card then
            ∏ i ∈ s, v i else 0 := by
        intro s _
        have hc :
            (∑ m ∈ raw.filter (fun m => PEqualNP.Outside.L_lib_701_aux.fullBlocks m = s),
              ∏ i ∈ PEqualNP.Outside.L_lib_701_aux.fullBlocks m, v i) =
            ∑ _m ∈ raw.filter (fun m => PEqualNP.Outside.L_lib_701_aux.fullBlocks m = s),
              ∏ i ∈ s, v i := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [(Finset.mem_filter.1 hm).2]
        rw [hc, Finset.sum_const, nsmul_eq_mul, PEqualNP.Outside.L_lib_701_aux.zmod2_natCast_eq_ite]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  · rintro ⟨outer, hdeg, heval⟩
    let raw : Finset (Finset J) := outer.image (PEqualNP.Outside.L_lib_701_aux.liftSet width)
    refine ⟨raw, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_image.1 hm with ⟨s, hs, rfl⟩
      rw [PEqualNP.Outside.L_lib_701_aux.liftSet_card]
      exact hdeg s hs
    · intro x hxD
      rw [Finset.sum_image (fun s1 _ s2 _ h => PEqualNP.Outside.L_lib_701_aux.liftSet_injective hw h)]
      have hcongr : (∑ s ∈ outer, ∏ u ∈ PEqualNP.Outside.L_lib_701_aux.liftSet width s, x u) =
          ∑ s ∈ outer, ∏ i ∈ s, flags x i := by
        refine Finset.sum_congr rfl fun s _ => ?_
        exact PEqualNP.Outside.L_lib_701_aux.prod_liftSet x s
      rw [hcongr]
      exact heval (flags x) hxD
