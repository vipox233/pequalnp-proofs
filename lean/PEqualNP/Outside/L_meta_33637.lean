import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33637_aux.Cut
def bscore {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat) (U : Finset (Fin k)) : Nat :=
  ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
theorem b_le {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat) (U : Finset (Fin k)) :
    bscore g lane phase U ≤ 2 * g := by
  unfold bscore
  calc ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
      ≤ ∑ _j ∈ Finset.range g, 2 := Finset.sum_le_sum (fun j _ => Nat.min_le_left _ _)
    _ = 2 * g := by simp [Nat.mul_comm]
theorem b_mono {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat)
    (U V : Finset (Fin k)) (h : U ⊆ V) : bscore g lane phase U ≤ bscore g lane phase V := by
  unfold bscore
  apply Finset.sum_le_sum
  intro j _
  exact min_le_min le_rfl
    (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ h)))
theorem b_lane {k : Nat} (lane : Fin k → Nat) (phase : Fin k → Nat) (j : Nat)
    (U V : Finset (Fin k)) :
    min 2 (((U ∪ V).filter (fun v => lane v = j)).image phase).card +
      min 2 (((U ∩ V).filter (fun v => lane v = j)).image phase).card ≤
    min 2 ((U.filter (fun v => lane v = j)).image phase).card +
      min 2 ((V.filter (fun v => lane v = j)).image phase).card := by
  have h1 : ((U ∪ V).filter (fun v => lane v = j)).image phase =
      (U.filter (fun v => lane v = j)).image phase ∪ (V.filter (fun v => lane v = j)).image phase := by
    rw [Finset.filter_union, Finset.image_union]
  have h2 : ((U ∩ V).filter (fun v => lane v = j)).image phase ⊆
      (U.filter (fun v => lane v = j)).image phase ∩ (V.filter (fun v => lane v = j)).image phase := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter] at hp ⊢
    obtain ⟨v, ⟨⟨hu, hv⟩, hl⟩, rfl⟩ := hp
    exact ⟨⟨v, ⟨hu, hl⟩, rfl⟩, ⟨v, ⟨hv, hl⟩, rfl⟩⟩
  rw [h1]
  have h4 := Finset.card_le_card h2
  generalize (U.filter (fun v => lane v = j)).image phase = P at *
  generalize (V.filter (fun v => lane v = j)).image phase = Q at *
  generalize ((U ∩ V).filter (fun v => lane v = j)).image phase = R at *
  have h3 := Finset.card_union_add_card_inter P Q
  have h5 : (P ∩ Q).card ≤ P.card := Finset.card_le_card Finset.inter_subset_left
  have h6 : (P ∩ Q).card ≤ Q.card := Finset.card_le_card Finset.inter_subset_right
  omega
theorem b_submod {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat)
    (U V : Finset (Fin k)) :
    bscore g lane phase (U ∪ V) + bscore g lane phase (U ∩ V) ≤
      bscore g lane phase U + bscore g lane phase V := by
  unfold bscore
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact b_lane lane phase j U V
theorem b_card {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat)
    (U : Finset (Fin k)) : bscore g lane phase U ≤ U.card := by
  unfold bscore
  calc ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
      ≤ ∑ j ∈ Finset.range g, (U.filter (fun v => lane v = j)).card :=
        Finset.sum_le_sum (fun j _ => le_trans (min_le_right _ _) Finset.card_image_le)
    _ = (U.filter (fun v => lane v ∈ Finset.range g)).card :=
        Finset.sum_card_fiberwise_eq_card_filter U (Finset.range g) lane
    _ ≤ U.card := Finset.card_filter_le _ _
theorem b_rado {α β : Type*} [DecidableEq α] [DecidableEq β] (d : β) (r : Finset β → ℕ)
    (hmono : ∀ U V : Finset β, U ⊆ V → r U ≤ r V)
    (hsub : ∀ U V : Finset β, r (U ∪ V) + r (U ∩ V) ≤ r U + r V)
    (S : Finset α) (n : ℕ) : ∀ A : α → Finset β, ∑ C ∈ S, (A C).card = n →
      (∀ C ∈ S, (A C).Nonempty) → ∀ m : ℕ, (∀ T ⊆ S, m ≤ S.card - T.card + r (T.biUnion A)) →
      ∃ f : α → β, (∀ C ∈ S, f C ∈ A C) ∧ m ≤ r (S.image f) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hne m hm
  by_cases h : ∃ C0 ∈ S, ∃ x ∈ A C0, ∃ y ∈ A C0, x ≠ y
  · obtain ⟨C0, hC0, x, hx, y, hy, hxy⟩ := h
    have key : ∀ z ∈ A C0, ∀ w ∈ A C0, w ≠ z →
        (∀ T ⊆ S, m ≤ S.card - T.card +
          r (T.biUnion (fun C => if C = C0 then (A C0).erase z else A C))) →
        ∃ f : α → β, (∀ C ∈ S, f C ∈ A C) ∧ m ≤ r (S.image f) := by
      intro z hz w hw hwz hmz
      have hlt : ∑ C ∈ S, (if C = C0 then (A C0).erase z else A C).card < n := by
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro C _
          by_cases hc : C = C0
          · rw [ite_eq_left hc, hc]
            exact Finset.card_erase_le
          · rw [ite_eq_right hc]
        · exact ⟨C0, hC0, by rw [ite_eq_left rfl]; exact Finset.card_erase_lt_of_mem hz⟩
      have hne' : ∀ C ∈ S, (if C = C0 then (A C0).erase z else A C).Nonempty := by
        intro C hC
        by_cases hc : C = C0
        · rw [ite_eq_left hc]
          exact ⟨w, Finset.mem_erase.mpr ⟨hwz, hw⟩⟩
        · rw [ite_eq_right hc]
          exact hne C hC
      obtain ⟨f, hf, hfm⟩ :=
        ih _ hlt (fun C => if C = C0 then (A C0).erase z else A C) rfl hne' m hmz
      refine ⟨f, fun C hC => ?_, hfm⟩
      have hfC := hf C hC
      by_cases hc : C = C0
      · rw [ite_eq_left hc] at hfC
        have hfC2 := Finset.mem_of_mem_erase hfC
        rw [hc] at hfC2 ⊢
        exact hfC2
      · rw [ite_eq_right hc] at hfC
        exact hfC
    by_cases h1 : ∀ T ⊆ S, m ≤ S.card - T.card +
        r (T.biUnion (fun C => if C = C0 then (A C0).erase x else A C))
    · exact key x hx y hy (Ne.symm hxy) h1
    by_cases h2 : ∀ T ⊆ S, m ≤ S.card - T.card +
        r (T.biUnion (fun C => if C = C0 then (A C0).erase y else A C))
    · exact key y hy x hx hxy h2
    exfalso
    push Not at h1 h2
    obtain ⟨T1, hT1, h1⟩ := h1
    obtain ⟨T2, hT2, h2⟩ := h2
    have hC1 : C0 ∈ T1 := by
      by_contra hc
      have he : T1.biUnion (fun C => if C = C0 then (A C0).erase x else A C) = T1.biUnion A := by
        apply Finset.biUnion_congr rfl
        intro C hC
        have hCne : C ≠ C0 := fun h => hc (h ▸ hC)
        rw [ite_eq_right hCne]
      rw [he] at h1
      have := hm T1 hT1
      omega
    have hC2 : C0 ∈ T2 := by
      by_contra hc
      have he : T2.biUnion (fun C => if C = C0 then (A C0).erase y else A C) = T2.biUnion A := by
        apply Finset.biUnion_congr rfl
        intro C hC
        have hCne : C ≠ C0 := fun h => hc (h ▸ hC)
        rw [ite_eq_right hCne]
      rw [he] at h2
      have := hm T2 hT2
      omega
    have incU : (T1 ∪ T2).biUnion A ⊆
        T1.biUnion (fun C => if C = C0 then (A C0).erase x else A C) ∪
          T2.biUnion (fun C => if C = C0 then (A C0).erase y else A C) := by
      intro v hv
      simp only [Finset.mem_biUnion, Finset.mem_union] at hv ⊢
      obtain ⟨C, hC, hvC⟩ := hv
      by_cases hc : C = C0
      · rw [hc] at hvC
        by_cases hvx : v = x
        · right
          refine ⟨C0, hC2, ?_⟩
          rw [ite_eq_left rfl]
          exact Finset.mem_erase.mpr ⟨by rw [hvx]; exact hxy, hvC⟩
        · left
          refine ⟨C0, hC1, ?_⟩
          rw [ite_eq_left rfl]
          exact Finset.mem_erase.mpr ⟨hvx, hvC⟩
      · rcases hC with hC | hC
        · left
          exact ⟨C, hC, by rw [ite_eq_right hc]; exact hvC⟩
        · right
          exact ⟨C, hC, by rw [ite_eq_right hc]; exact hvC⟩
    have incI : ((T1 ∩ T2).erase C0).biUnion A ⊆
        T1.biUnion (fun C => if C = C0 then (A C0).erase x else A C) ∩
          T2.biUnion (fun C => if C = C0 then (A C0).erase y else A C) := by
      intro v hv
      simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_erase] at hv ⊢
      obtain ⟨C, ⟨hc, hC1', hC2'⟩, hvC⟩ := hv
      exact ⟨⟨C, hC1', by rw [ite_eq_right hc]; exact hvC⟩, ⟨C, hC2', by rw [ite_eq_right hc]; exact hvC⟩⟩
    have hU := hm (T1 ∪ T2) (Finset.union_subset hT1 hT2)
    have hIS : (T1 ∩ T2).erase C0 ⊆ S :=
      (Finset.erase_subset _ _).trans (Finset.inter_subset_left.trans hT1)
    have hI := hm ((T1 ∩ T2).erase C0) hIS
    have c6 := Finset.card_le_card hIS
    have hs := hsub (T1.biUnion (fun C => if C = C0 then (A C0).erase x else A C))
      (T2.biUnion (fun C => if C = C0 then (A C0).erase y else A C))
    have hmU := hmono _ _ incU
    have hmI := hmono _ _ incI
    have c1 := Finset.card_union_add_card_inter T1 T2
    have c2 : ((T1 ∩ T2).erase C0).card + 1 = (T1 ∩ T2).card :=
      Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hC1, hC2⟩)
    have c3 := Finset.card_le_card (Finset.union_subset hT1 hT2)
    have c4 := Finset.card_le_card hT1
    have c5 := Finset.card_le_card hT2
    omega
  · push Not at h
    refine ⟨fun C => if hC : (A C).Nonempty then hC.choose else d, ?_, ?_⟩
    · intro C hC
      simp only [dite_eq_left (hne C hC)]
      exact (hne C hC).choose_spec
    · have hS := hm S (Finset.Subset.refl S)
      rw [Nat.sub_self, Nat.zero_add] at hS
      refine le_trans hS (hmono _ _ ?_)
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨C, hC, hvC⟩ := hv
      rw [Finset.mem_image]
      refine ⟨C, hC, ?_⟩
      simp only [dite_eq_left (hne C hC)]
      exact h C hC _ (hne C hC).choose_spec v hvC
theorem b_upper {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat)
    (S : Finset (Finset (Fin k))) (A : Finset (Fin k) → Finset (Fin k))
    (f : Finset (Fin k) → Fin k) (hf : ∀ C ∈ S, f C ∈ A C)
    (T : Finset (Finset (Fin k))) (hT : T ⊆ S) :
    bscore g lane phase (S.image f) ≤ (S.card - T.card) + bscore g lane phase (T.biUnion A) := by
  have hsub : S.image f ⊆ T.biUnion A ∪ (S \ T).image f := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨C, hC, rfl⟩ := hv
    by_cases hCT : C ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨C, hCT, hf C hC⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_sdiff.mpr ⟨hC, hCT⟩))
  have h1 := b_mono g lane phase _ _ hsub
  have h2 := b_submod g lane phase (T.biUnion A) ((S \ T).image f)
  have h3 := b_card g lane phase ((S \ T).image f)
  have h4 : ((S \ T).image f).card ≤ (S \ T).card := Finset.card_image_le
  have h5 : (S \ T).card = S.card - T.card := Finset.card_sdiff_of_subset hT
  omega
theorem b_lower {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Nat)
    (S : Finset (Finset (Fin k))) (A : Finset (Fin k) → Finset (Fin k))
    (hne : ∀ C ∈ S, (A C).Nonempty) (hk : 0 < k := by omega) :
    ∃ f : Finset (Fin k) → Fin k, (∀ C ∈ S, f C ∈ A C) ∧
      ∃ T : Finset (Finset (Fin k)), T ⊆ S ∧
        (S.card - T.card) + bscore g lane phase (T.biUnion A) ≤ bscore g lane phase (S.image f) := by
  obtain ⟨T0, hT0, hmin⟩ := Finset.exists_min_image S.powerset
    (fun T => S.card - T.card + bscore g lane phase (T.biUnion A)) ⟨∅, Finset.empty_mem_powerset S⟩
  obtain ⟨f, hf, hfm⟩ := b_rado (⟨0, hk⟩ : Fin k) (bscore g lane phase) (b_mono g lane phase)
    (b_submod g lane phase) S _ A rfl hne _ (fun T hT => hmin T (Finset.mem_powerset.mpr hT))
  exact ⟨f, hf, T0, Finset.mem_powerset.mp hT0, hfm⟩
def a_nx (k : Nat) (hk : 0 < k) (i : Fin k) : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
def a_pv (k : Nat) (hk : 0 < k) (i : Fin k) : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ hk⟩
theorem a_pv_nx (k : Nat) (hk : 0 < k) (i : Fin k) : a_pv k hk (a_nx k hk i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [a_pv, a_nx]
  rcases Nat.lt_or_ge (i.val + 1) k with h | h
  · rw [Nat.mod_eq_of_lt h, show i.val + 1 + k - 1 = i.val + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · rw [show i.val + 1 = k by omega, Nat.mod_self, show 0 + k - 1 = i.val by omega,
      Nat.mod_eq_of_lt hi]
theorem a_nx_pv (k : Nat) (hk : 0 < k) (i : Fin k) : a_nx k hk (a_pv k hk i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [a_pv, a_nx]
  rcases Nat.eq_zero_or_pos i.val with h | h
  · rw [h, Nat.mod_eq_of_lt (show 0 + k - 1 < k by omega), show 0 + k - 1 + 1 = k by omega,
      Nat.mod_self]
  · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show i.val - 1 < k by omega), show i.val - 1 + 1 = i.val by omega,
      Nat.mod_eq_of_lt hi]
theorem a_nx_inj (k : Nat) (hk : 0 < k) : Function.Injective (a_nx k hk) :=
  Function.LeftInverse.injective (a_pv_nx k hk)
theorem a_pv_inj (k : Nat) (hk : 0 < k) : Function.Injective (a_pv k hk) :=
  Function.LeftInverse.injective (a_nx_pv k hk)
theorem a_nx_iter (k : Nat) (hk : 0 < k) (i : Fin k) (d : Nat) :
    ((a_nx k hk)^[d] i).val = (i.val + d) % k := by
  induction d with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show (((a_nx k hk)^[n] i).val + 1) % k = _
    rw [ih, Nat.mod_add_mod, Nat.add_assoc]
theorem a_pv_iter_nx (k : Nat) (hk : 0 < k) (i : Fin k) (d : Nat) :
    (a_pv k hk)^[d] ((a_nx k hk)^[d] i) = i :=
  Function.LeftInverse.iterate (a_pv_nx k hk) d i
theorem a_nx_iter_pv (k : Nat) (hk : 0 < k) (i : Fin k) (d : Nat) :
    (a_nx k hk)^[d] ((a_pv k hk)^[d] i) = i :=
  Function.LeftInverse.iterate (a_nx_pv k hk) d i
theorem a_cyc (k : Nat) (hk : 0 < k) (v w : Fin k) : ∃ d < k, (a_pv k hk)^[d] v = w := by
  have h : (a_nx k hk)^[(v.val + k - w.val) % k] w = v := by
    apply Fin.ext
    rw [a_nx_iter, Nat.add_mod_mod, show w.val + (v.val + k - w.val) = v.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]
  obtain ⟨d, hd, h⟩ : ∃ d < k, (a_nx k hk)^[d] w = v := ⟨_, Nat.mod_lt _ hk, h⟩
  exact ⟨d, hd, by rw [← h, a_pv_iter_nx]⟩
theorem a_cyc_ne (k : Nat) (hk : 0 < k) (v : Fin k) (m : Nat) (h0 : 0 < m) (hm : m < k) :
    (a_pv k hk)^[m] v ≠ v := by
  intro h
  have h1 : (a_nx k hk)^[m] v = v := by
    have := a_nx_iter_pv k hk v m
    rwa [h] at this
  have h2 := congrArg Fin.val h1
  rw [a_nx_iter] at h2
  have hv := v.isLt
  rcases Nat.lt_or_ge (v.val + m) k with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h2; omega
  · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at h2; omega
theorem a_dist (k : Nat) (hk : 0 < k) (s v : Fin k) (d : Nat) (hd : d < k)
    (h : (a_nx k hk)^[d] s = v) : (v.val + k - s.val) % k = d := by
  have hv : v.val = (s.val + d) % k := by rw [← h, a_nx_iter]
  have hs := s.isLt
  rcases Nat.lt_or_ge (s.val + d) k with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    rw [show v.val + k - s.val = d + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hv
    rw [show v.val + k - s.val = d by omega, Nat.mod_eq_of_lt hd]
theorem a_off_ex (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k) :
    ∃ d, d < k ∧ (a_pv k hk)^[d+1] v ∉ F := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ F := by
    by_contra h
    exact hF (Finset.eq_univ_iff_forall.mpr (fun x => by
      by_contra hx
      exact h ⟨x, hx⟩))
  obtain ⟨d, hd, h⟩ := a_cyc k hk (a_pv k hk v) x
  exact ⟨d, hd, by rw [Function.iterate_succ_apply, h]; exact hx⟩
theorem a_off_ex2 (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k) :
    ∃ d, (a_pv k hk)^[d+1] v ∉ F := by
  obtain ⟨d, _, h⟩ := a_off_ex k hk F hF v
  exact ⟨d, h⟩
def a_off (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k) : Nat :=
  Nat.find (a_off_ex2 k hk F hF v)
theorem a_off_lt (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k) :
    a_off k hk F hF v < k := by
  obtain ⟨d, hd, h⟩ := a_off_ex k hk F hF v
  exact lt_of_le_of_lt (Nat.find_min' _ h) hd
theorem a_off_spec (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k) :
    (a_pv k hk)^[a_off k hk F hF v + 1] v ∉ F :=
  Nat.find_spec (a_off_ex2 k hk F hF v)
theorem a_off_min (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k)
    (d : Nat) (hd : d < a_off k hk F hF v) : (a_pv k hk)^[d+1] v ∈ F := by
  have := Nat.find_min (a_off_ex2 k hk F hF v) hd
  simpa using this
theorem a_off_zero (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k)
    (h : a_pv k hk v ∉ F) : a_off k hk F hF v = 0 := by
  unfold a_off
  rw [Nat.find_eq_zero]
  simpa using h
theorem a_off_succ (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (v : Fin k)
    (h : a_pv k hk v ∈ F) : a_off k hk F hF v = a_off k hk F hF (a_pv k hk v) + 1 := by
  apply le_antisymm
  · exact Nat.find_min' _ (a_off_spec k hk F hF (a_pv k hk v))
  · have hne : a_off k hk F hF v ≠ 0 := by
      intro h0
      have := a_off_spec k hk F hF v
      rw [h0] at this
      exact this h
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have h1 := a_off_spec k hk F hF v
    rw [hm] at h1
    have h2 : a_off k hk F hF (a_pv k hk v) ≤ m := Nat.find_min' _ h1
    omega
theorem a_off_nx_in (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) (i : Fin k)
    (h : i ∈ F) : a_off k hk F hF (a_nx k hk i) = a_off k hk F hF i + 1 := by
  rw [a_off_succ k hk F hF _ (by rw [a_pv_nx]; exact h), a_pv_nx]
noncomputable def a_cl {k : Nat} (r : Fin k → Fin k → Prop) (i : Fin k) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter
    (fun j => @decide (Relation.EqvGen r i j) (Classical.propDecidable _) = true)
theorem a_cl_mem {k : Nat} (r : Fin k → Fin k → Prop) (i j : Fin k) :
    j ∈ a_cl r i ↔ Relation.EqvGen r i j := by
  simp [a_cl]
theorem a_cl_eq {k : Nat} (r : Fin k → Fin k → Prop) (i j : Fin k) (h : Relation.EqvGen r i j) :
    a_cl r j = a_cl r i := by
  ext x
  rw [a_cl_mem, a_cl_mem]
  exact ⟨fun hx => Relation.EqvGen.trans _ _ _ h hx,
    fun hx => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hx⟩
theorem a_cl_of_mem {k : Nat} (r : Fin k → Fin k → Prop) (i j : Fin k) (h : j ∈ a_cl r i) :
    a_cl r i = a_cl r j :=
  (a_cl_eq r i j ((a_cl_mem r i j).mp h)).symm
theorem a_chain (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ) (v : Fin k) :
    ∀ d, d ≤ a_off k hk E hE v →
      Relation.EqvGen (fun i j => i ∈ E ∧ j = a_nx k hk i) ((a_pv k hk)^[d] v) v := by
  intro d
  induction d with
  | zero => intro _; exact Relation.EqvGen.refl _
  | succ n ih =>
    intro hn
    refine Relation.EqvGen.trans _ _ _ ?_ (ih (by omega))
    refine Relation.EqvGen.rel _ _ ⟨a_off_min k hk E hE v n (by omega), ?_⟩
    rw [Function.iterate_succ_apply', a_nx_pv]
theorem a_start (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ) (a b : Fin k)
    (h : Relation.EqvGen (fun i j => i ∈ E ∧ j = a_nx k hk i) a b) :
    (a_pv k hk)^[a_off k hk E hE a] a = (a_pv k hk)^[a_off k hk E hE b] b := by
  induction h with
  | rel x y hxy =>
    obtain ⟨hx, rfl⟩ := hxy
    rw [a_off_nx_in k hk E hE x hx, Function.iterate_succ_apply, a_pv_nx]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
theorem a_greedy (k : Nat) (hk : 0 < k) (F : Finset (Fin k)) (hF : F ≠ Finset.univ) :
    (∀ i ∈ F.filter (fun i => a_off k hk F hF i % 2 = 0),
      a_nx k hk i ∉ F.filter (fun i => a_off k hk F hF i % 2 = 0)) ∧
    ∀ v, v ∉ F.filter (fun i => a_off k hk F hF i % 2 = 0) ∪
        (F.filter (fun i => a_off k hk F hF i % 2 = 0)).image (a_nx k hk) ↔
      (v ∉ F ∧ a_off k hk F hF v % 2 = 0) := by
  constructor
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_filter, a_off_nx_in k hk F hF i hi.1]
    omega
  · intro v
    have himg : ∀ (M : Finset (Fin k)), v ∈ M.image (a_nx k hk) ↔ a_pv k hk v ∈ M := by
      intro M
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        rw [a_pv_nx]
        exact hi
      · intro h
        exact Finset.mem_image.mpr ⟨_, h, a_nx_pv k hk v⟩
    rw [Finset.mem_union, himg, Finset.mem_filter, Finset.mem_filter]
    by_cases hp : a_pv k hk v ∈ F
    · rw [a_off_succ k hk F hF v hp]
      by_cases hv : v ∈ F
      · simp only [hp, hv, true_and, not_true_eq_false, false_and, iff_false, not_not]
        omega
      · simp only [hp, hv, true_and, false_and, false_or, not_false_eq_true]
        omega
    · rw [a_off_zero k hk F hF v hp]
      simp [hp]
theorem a_par (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ)
    (M : Finset (Fin k)) (hME : M ⊆ E) (hM : ∀ i ∈ M, a_nx k hk i ∉ M) :
    ∀ n w, a_off k hk E hE w = n →
      (∀ d ≤ n, (a_pv k hk)^[d] w ∈ M ∪ M.image (a_nx k hk)) → (w ∈ M ↔ n % 2 = 0) := by
  have himg : ∀ w, w ∈ M ∪ M.image (a_nx k hk) ↔ w ∈ M ∨ a_pv k hk w ∈ M := by
    intro w
    rw [Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        rw [a_pv_nx]
        exact Or.inr hi
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Finset.mem_image.mpr ⟨_, h, a_nx_pv k hk w⟩)
  intro n
  induction n with
  | zero =>
    intro w hw hcov
    have hpw : a_pv k hk w ∉ E := by
      have := a_off_spec k hk E hE w
      rw [hw] at this
      exact this
    have hc := (himg w).mp (hcov 0 le_rfl)
    rcases hc with hc | hc
    · simp [hc]
    · exact absurd (hME hc) hpw
  | succ n ih =>
    intro w hw hcov
    have hpw : a_pv k hk w ∈ E := a_off_min k hk E hE w 0 (by omega)
    have hw' : a_off k hk E hE (a_pv k hk w) = n := by
      rw [a_off_succ k hk E hE w hpw] at hw
      omega
    have ih' := ih (a_pv k hk w) hw' (fun d hd => by
      have := hcov (d+1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have hc := (himg w).mp (hcov 0 (by omega))
    by_cases hn : n % 2 = 0
    · have h1 : a_pv k hk w ∈ M := ih'.mpr hn
      have h2 : w ∉ M := by
        have := hM _ h1
        rwa [a_nx_pv] at this
      constructor
      · intro h
        exact absurd h h2
      · intro h
        omega
    · have h1 : a_pv k hk w ∉ M := fun h => hn (ih'.mp h)
      have h2 : w ∈ M := by
        rcases hc with hc | hc
        · exact hc
        · exact absurd hc h1
      constructor
      · intro _
        omega
      · intro _
        exact h2
theorem a_par2 (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ)
    (M : Finset (Fin k)) (hME : M ⊆ E) (hM : ∀ i ∈ M, a_nx k hk i ∉ M) (u : Fin k)
    (hu : u ∉ M ∪ M.image (a_nx k hk))
    (hcov : ∀ d, 1 ≤ d → d ≤ a_off k hk E hE u →
      (a_pv k hk)^[d] u ∈ M ∪ M.image (a_nx k hk)) :
    a_off k hk E hE u % 2 = 0 := by
  rcases Nat.eq_zero_or_pos (a_off k hk E hE u) with h | h
  · rw [h]
  · obtain ⟨n, hn⟩ : ∃ n, a_off k hk E hE u = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    have hpu : a_pv k hk u ∈ E := a_off_min k hk E hE u 0 (by omega)
    have hw' : a_off k hk E hE (a_pv k hk u) = n := by
      rw [a_off_succ k hk E hE u hpu] at hn
      omega
    have h3 := a_par k hk E hE M hME hM n (a_pv k hk u) hw' (fun d hd => by
      have := hcov (d+1) (by omega) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have h1 : a_pv k hk u ∉ M := by
      intro h1
      apply hu
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨_, h1, a_nx_pv k hk u⟩)
    have h4 : ¬ (n % 2 = 0) := fun h => h1 (h3.mpr h)
    omega
theorem a_ends_card (k : Nat) (hk : 0 < k) (M : Finset (Fin k))
    (hM : ∀ i ∈ M, a_nx k hk i ∉ M) :
    (M ∪ M.image (a_nx k hk)).card = 2 * M.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (a_nx_inj k hk)]
  · omega
  · rw [Finset.disjoint_left]
    intro x hx hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx2
    exact hM i hi hx
theorem a_odd_unc (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (M : Finset (Fin k))
    (hME : M ⊆ E) (hM : ∀ i ∈ M, a_nx k hk i ∉ M) (i0 : Fin k)
    (hodd : (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0).card % 2 = 1) :
    ∃ v ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0, v ∉ M ∪ M.image (a_nx k hk) := by
  by_contra hcon
  have hcov : ∀ v ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0,
      v ∈ M ∪ M.image (a_nx k hk) := by
    intro v hv
    by_contra h
    exact hcon ⟨v, hv, h⟩
  have hCeq : a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0 =
      M.filter (fun x => x ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0) ∪
      (M.filter (fun x => x ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0)).image
        (a_nx k hk) := by
    ext v
    constructor
    · intro hv
      have := hcov v hv
      rw [Finset.mem_union, Finset.mem_image] at this
      rw [Finset.mem_union, Finset.mem_image]
      rcases this with h | ⟨i, hi, rfl⟩
      · exact Or.inl (Finset.mem_filter.mpr ⟨h, hv⟩)
      · refine Or.inr ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, rfl⟩
        rw [a_cl_mem] at hv ⊢
        exact Relation.EqvGen.trans _ _ _ hv
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hME hi, rfl⟩))
    · intro hv
      rw [Finset.mem_union, Finset.mem_image] at hv
      rcases hv with h | ⟨i, hi, rfl⟩
      · exact (Finset.mem_filter.mp h).2
      · have hi' := Finset.mem_filter.mp hi
        have h2 := hi'.2
        rw [a_cl_mem] at h2 ⊢
        exact Relation.EqvGen.trans _ _ _ h2 (Relation.EqvGen.rel _ _ ⟨hME hi'.1, rfl⟩)
  have hcard := a_ends_card k hk
    (M.filter (fun x => x ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i0))
    (fun i hi h => hM i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp h).1)
  rw [← hCeq] at hcard
  omega
theorem a_iter_inj (k : Nat) (hk : 0 < k) (v : Fin k) (a b : Nat) (ha : a < k) (hb : b < k)
    (h : (a_pv k hk)^[a] v = (a_pv k hk)^[b] v) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    apply a_cyc_ne k hk ((a_pv k hk)^[a] v) (b - a) (by omega) (by omega)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact h.symm
  · exact hab
  · exfalso
    apply a_cyc_ne k hk ((a_pv k hk)^[b] v) (a - b) (by omega) (by omega)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact h
theorem a_cl_card (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ) (v : Fin k)
    (hv : v ∉ E) :
    a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v =
      (Finset.range (a_off k hk E hE v + 1)).image (fun d => (a_pv k hk)^[d] v) ∧
    (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v).card = a_off k hk E hE v + 1 := by
  have heq : a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v =
      (Finset.range (a_off k hk E hE v + 1)).image (fun d => (a_pv k hk)^[d] v) := by
    ext w
    rw [a_cl_mem, Finset.mem_image]
    constructor
    · intro h
      have hs := a_start k hk E hE v w h
      have hle : a_off k hk E hE w ≤ a_off k hk E hE v := by
        by_contra hlt
        apply hv
        obtain ⟨m, hm⟩ : ∃ m, a_off k hk E hE w = a_off k hk E hE v + (m + 1) :=
          ⟨a_off k hk E hE w - a_off k hk E hE v - 1, by omega⟩
        rw [hm, Function.iterate_add_apply] at hs
        have h3 := (Function.Injective.iterate (a_pv_inj k hk) _) hs
        rw [h3]
        exact a_off_min k hk E hE w m (by omega)
      refine ⟨a_off k hk E hE v - a_off k hk E hE w, Finset.mem_range.mpr (by omega), ?_⟩
      have h2 : a_off k hk E hE v =
          a_off k hk E hE w + (a_off k hk E hE v - a_off k hk E hE w) := by
        omega
      rw [h2, Function.iterate_add_apply] at hs
      exact (Function.Injective.iterate (a_pv_inj k hk) _) hs
    · rintro ⟨d, hd, rfl⟩
      exact Relation.EqvGen.symm _ _
        (a_chain k hk E hE v d (by rw [Finset.mem_range] at hd; omega))
  refine ⟨heq, ?_⟩
  rw [heq, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have := a_off_lt k hk E hE v
  have ha' := Finset.mem_range.mp (Finset.mem_coe.mp ha)
  have hb' := Finset.mem_range.mp (Finset.mem_coe.mp hb)
  exact a_iter_inj k hk v a b (by omega) (by omega) hab
theorem a_elig_iff (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ)
    (w v : Fin k) (hv : v ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) w) :
    (∃ s ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) w, a_pv k hk s ∉ E ∧
        ((v.val + k - s.val) % k) % 2 = 0) ↔ a_off k hk E hE v % 2 = 0 := by
  rw [a_cl_mem] at hv
  constructor
  · rintro ⟨s, hs, hsE, hpar⟩
    rw [a_cl_mem] at hs
    have h1 := a_start k hk E hE s v
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hs) hv)
    rw [a_off_zero k hk E hE s hsE, Function.iterate_zero_apply] at h1
    have h2 : (a_nx k hk)^[a_off k hk E hE v] s = v := by
      rw [h1, a_nx_iter_pv]
    rw [a_dist k hk s v _ (a_off_lt k hk E hE v) h2] at hpar
    exact hpar
  · intro h
    refine ⟨(a_pv k hk)^[a_off k hk E hE v] v, ?_, ?_, ?_⟩
    · rw [a_cl_mem]
      exact Relation.EqvGen.trans _ _ _ hv
        (Relation.EqvGen.symm _ _ (a_chain k hk E hE v _ le_rfl))
    · have := a_off_spec k hk E hE v
      rwa [Function.iterate_succ_apply'] at this
    · rw [a_dist k hk _ v _ (a_off_lt k hk E hE v) (a_nx_iter_pv k hk v _)]
      exact h
theorem a_rel (k : Nat) (hk : 0 < k) (E U : Finset (Fin k)) (hE : E ≠ Finset.univ)
    (hF : E \ U ≠ Finset.univ) (hU : ∀ u ∈ U, a_off k hk E hE u % 2 = 0) :
    ∀ n v, a_off k hk E hE v = n →
      ((∃ d, 1 ≤ d ∧ d ≤ n ∧ (a_pv k hk)^[d] v ∈ U) →
        a_off k hk (E \ U) hF v % 2 = (n + 1) % 2) ∧
      ((¬ ∃ d, 1 ≤ d ∧ d ≤ n ∧ (a_pv k hk)^[d] v ∈ U) →
        a_off k hk (E \ U) hF v % 2 = n % 2) := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have h1 : a_pv k hk v ∉ E := by
      have := a_off_spec k hk E hE v
      rw [hv] at this
      exact this
    rw [a_off_zero k hk (E \ U) hF v (fun h => h1 (Finset.mem_sdiff.mp h).1)]
    refine ⟨?_, fun _ => rfl⟩
    rintro ⟨d, hd1, hd2, _⟩
    omega
  | succ n ih =>
    intro v hv
    have h1 : a_pv k hk v ∈ E := a_off_min k hk E hE v 0 (by omega)
    have h2 : a_off k hk E hE (a_pv k hk v) = n := by
      rw [a_off_succ k hk E hE v h1] at hv
      omega
    by_cases h3 : a_pv k hk v ∈ U
    · rw [a_off_zero k hk (E \ U) hF v (fun h => (Finset.mem_sdiff.mp h).2 h3)]
      have h4 := hU _ h3
      rw [h2] at h4
      refine ⟨fun _ => by omega, fun h => (h ⟨1, le_rfl, by omega, h3⟩).elim⟩
    · rw [a_off_succ k hk (E \ U) hF v (Finset.mem_sdiff.mpr ⟨h1, h3⟩)]
      obtain ⟨ih1, ih2⟩ := ih _ h2
      have hiff : (∃ d, 1 ≤ d ∧ d ≤ n + 1 ∧ (a_pv k hk)^[d] v ∈ U) ↔
          (∃ d, 1 ≤ d ∧ d ≤ n ∧ (a_pv k hk)^[d] (a_pv k hk v) ∈ U) := by
        constructor
        · rintro ⟨d, hd1, hd2, hd3⟩
          obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
          rcases Nat.eq_zero_or_pos e with he | he
          · subst he
            exact absurd hd3 h3
          · exact ⟨e, he, by omega, hd3⟩
        · rintro ⟨d, hd1, hd2, hd3⟩
          exact ⟨d + 1, by omega, by omega, hd3⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := ih1 (hiff.mp h)
        omega
      · have := ih2 (fun h' => h (hiff.mpr h'))
        omega
theorem a_cl_univ (k : Nat) (hk : 0 < k) (i : Fin k) :
    a_cl (fun i j => i ∈ (Finset.univ : Finset (Fin k)) ∧ j = a_nx k hk i) i = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro w
  rw [a_cl_mem]
  obtain ⟨d, -, hd⟩ := a_cyc k hk w i
  have hw : (a_nx k hk)^[d] i = w := by
    rw [← hd, a_nx_iter_pv]
  rw [← hw]
  clear hw hd
  induction d with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    refine Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ⟨Finset.mem_univ _, ?_⟩)
    rw [Function.iterate_succ_apply']
theorem a_cons_univ (k : Nat) (hk : 0 < k) (c : Fin k) :
    ∃ M : Finset (Fin k), (∀ i ∈ M, a_nx k hk i ∉ M) ∧
      Finset.univ \ (M ∪ M.image (a_nx k hk)) = if k % 2 = 1 then {c} else ∅ := by
  have hF : (Finset.univ \ {c} : Finset (Fin k)) ≠ Finset.univ := by
    intro h
    have : c ∈ (Finset.univ \ {c} : Finset (Fin k)) := by
      rw [h]
      exact Finset.mem_univ c
    simp at this
  obtain ⟨hg1, hg2⟩ := a_greedy k hk _ hF
  refine ⟨_, hg1, ?_⟩
  have hoc : a_off k hk _ hF c = k - 1 := by
    have h1 := a_off_spec k hk _ hF c
    have h2 := a_off_lt k hk _ hF c
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      not_not] at h1
    by_contra h3
    exact a_cyc_ne k hk c _ (by omega) (by omega) h1
  ext v
  rw [Finset.mem_sdiff, hg2 v]
  simp only [Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_singleton, not_not]
  constructor
  · rintro ⟨rfl, h⟩
    rw [hoc] at h
    rw [ite_eq_left (by omega)]
    exact Finset.mem_singleton_self _
  · intro h
    by_cases hk2 : k % 2 = 1
    · rw [ite_eq_left hk2, Finset.mem_singleton] at h
      subst h
      refine ⟨rfl, ?_⟩
      rw [hoc]
      omega
    · rw [ite_eq_right hk2] at h
      exact absurd h (Finset.notMem_empty _)
theorem a_cons_ne (k : Nat) (hk : 0 < k) (E : Finset (Fin k)) (hE : E ≠ Finset.univ)
    (oddCs : Finset (Finset (Fin k)))
    (hodd : ∀ C, C ∈ oddCs ↔
      (∃ i, a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i = C) ∧ C.card % 2 = 1)
    (f : Finset (Fin k) → Fin k)
    (hf : ∀ C ∈ oddCs, f C ∈ C ∧ a_off k hk E hE (f C) % 2 = 0) :
    ∃ M, M ⊆ E ∧ (∀ i ∈ M, a_nx k hk i ∉ M) ∧
      Finset.univ \ (M ∪ M.image (a_nx k hk)) = oddCs.image f := by
  have hF : E \ oddCs.image f ≠ Finset.univ := by
    intro h
    apply hE
    apply Finset.eq_univ_of_forall
    intro x
    have : x ∈ E \ oddCs.image f := by
      rw [h]
      exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp this).1
  have hU1 : ∀ u ∈ oddCs.image f, a_off k hk E hE u % 2 = 0 := by
    intro u hu
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hu
    exact (hf C hC).2
  have hUcl : ∀ u ∈ oddCs.image f, a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) u ∈ oddCs ∧
      f (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) u) = u := by
    intro u hu
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨⟨i, rfl⟩, _⟩ := (hodd _).mp hC
    rw [← a_cl_of_mem _ i _ (hf _ hC).1]
    exact ⟨hC, rfl⟩
  have hU2 : ∀ u ∈ oddCs.image f, ∀ u' ∈ oddCs.image f,
      Relation.EqvGen (fun i j => i ∈ E ∧ j = a_nx k hk i) u u' → u = u' := by
    intro u hu u' hu' h
    rw [← (hUcl u hu).2, ← (hUcl u' hu').2, a_cl_eq _ u u' h]
  obtain ⟨hg1, hg2⟩ := a_greedy k hk _ hF
  refine ⟨_, fun x hx => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1, hg1, ?_⟩
  ext v
  rw [Finset.mem_sdiff, hg2 v]
  simp only [Finset.mem_univ, true_and]
  have hR := a_rel k hk E (oddCs.image f) hE hF hU1 _ v rfl
  constructor
  · rintro ⟨hvF, hvo⟩
    by_contra hvU
    have hvE : v ∉ E := fun h => hvF (Finset.mem_sdiff.mpr ⟨h, hvU⟩)
    obtain ⟨hceq, hcard⟩ := a_cl_card k hk E hE v hvE
    by_cases hA : ∃ d, 1 ≤ d ∧ d ≤ a_off k hk E hE v ∧ (a_pv k hk)^[d] v ∈ oddCs.image f
    · have hR1 := hR.1 hA
      obtain ⟨d, _, hd2, hd3⟩ := hA
      have h1 := (hUcl _ hd3).1
      rw [← a_cl_eq _ _ _ (a_chain k hk E hE v d hd2)] at h1
      have h4 := ((hodd _).mp h1).2
      rw [hcard] at h4
      omega
    · have hR2 := hR.2 hA
      have hCodd : (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v).card % 2 = 1 := by
        rw [hcard]
        omega
      have hC : a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v ∈ oddCs :=
        (hodd _).mpr ⟨⟨v, rfl⟩, hCodd⟩
      have h1 : f (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v) ∈
          (Finset.range (a_off k hk E hE v + 1)).image (fun d => (a_pv k hk)^[d] v) := by
        rw [← hceq]
        exact (hf _ hC).1
      have h5 : f (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v) ∈ oddCs.image f :=
        Finset.mem_image.mpr ⟨_, hC, rfl⟩
      rw [Finset.mem_image] at h1
      obtain ⟨d, hd, hdv⟩ := h1
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        apply hvU
        rw [Function.iterate_zero_apply] at hdv
        rw [hdv]
        exact h5
      · apply hA
        refine ⟨d, h0, by omega, ?_⟩
        rw [hdv]
        exact h5
  · intro hvU
    refine ⟨fun h => (Finset.mem_sdiff.mp h).2 hvU, ?_⟩
    have hA : ¬ ∃ d, 1 ≤ d ∧ d ≤ a_off k hk E hE v ∧ (a_pv k hk)^[d] v ∈ oddCs.image f := by
      rintro ⟨d, hd1, hd2, hd3⟩
      have := hU2 _ hd3 _ hvU (a_chain k hk E hE v d hd2)
      exact a_cyc_ne k hk v d hd1 (lt_of_le_of_lt hd2 (a_off_lt k hk E hE v)) this
    rw [hR.2 hA]
    exact hU1 v hvU
theorem a_main (k : Nat) (hk : 0 < k) (E : Finset (Fin k))
    (edges : Finset (Finset (Fin k)))
    (hedges : edges = E.powerset.filter (fun M => ∀ i ∈ M, a_nx k hk i ∉ M))
    (mu : Nat) (hmu : mu = edges.sup Finset.card)
    (best : Finset (Finset (Fin k))) (hbest : best = edges.filter (fun M => M.card = mu))
    (ends : Finset (Fin k) → Finset (Fin k)) (hends : ends = fun M => M ∪ M.image (a_nx k hk))
    (cs : Finset (Finset (Fin k)))
    (hcs : cs = (Finset.univ : Finset (Fin k)).image
      (a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i)))
    (oddCs : Finset (Finset (Fin k))) (hoddCs : oddCs = cs.filter (fun C => C.card % 2 = 1))
    (eligible : Finset (Fin k) → Finset (Fin k))
    (helig : eligible = fun C => if E = Finset.univ then C else C.filter (fun v =>
        ∃ s ∈ C, a_pv k hk s ∉ E ∧ ((v.val+k-s.val) % k) % 2 = 0)) :
    (∀ M ∈ best, ∃ f : Finset (Fin k) → Fin k, (∀ C ∈ oddCs, f C ∈ eligible C) ∧
        Finset.univ \ ends M = oddCs.image f) ∧
    (∀ f : Finset (Fin k) → Fin k, (∀ C ∈ oddCs, f C ∈ eligible C) →
        ∃ M ∈ best, Finset.univ \ ends M = oddCs.image f) ∧
    (∀ C ∈ oddCs, (eligible C).Nonempty) := by
  subst hends
  have hmemE : ∀ M, M ∈ edges ↔ M ⊆ E ∧ ∀ i ∈ M, a_nx k hk i ∉ M := by
    intro M
    rw [hedges, Finset.mem_filter, Finset.mem_powerset]
  have hmemB : ∀ M, M ∈ best ↔ M ∈ edges ∧ M.card = mu := by
    intro M
    rw [hbest, Finset.mem_filter]
  have hmemO : ∀ C, C ∈ oddCs ↔
      (∃ i, a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i = C) ∧ C.card % 2 = 1 := by
    intro C
    rw [hoddCs, Finset.mem_filter, hcs, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
  have hcl : ∀ C ∈ oddCs, ∀ v ∈ C, C = a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) v := by
    intro C hC v hv
    obtain ⟨⟨i, rfl⟩, _⟩ := (hmemO C).mp hC
    exact a_cl_of_mem _ i v hv
  have hsub : ∀ C, eligible C ⊆ C := by
    intro C
    rw [helig]
    dsimp only
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.filter_subset _ _
  have himgc : ∀ g : Finset (Fin k) → Fin k, (∀ C ∈ oddCs, g C ∈ C) →
      (oddCs.image g).card = oddCs.card := by
    intro g hg
    apply Finset.card_image_of_injOn
    intro C hC C' hC' h
    rw [hcl C hC (g C) (hg C hC), hcl C' hC' (g C') (hg C' hC')]
    exact congrArg _ h
  have hec : ∀ M ∈ edges, (Finset.univ \ (M ∪ M.image (a_nx k hk))).card + 2 * M.card = k := by
    intro M hM
    rw [← a_ends_card k hk M ((hmemE M).mp hM).2,
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hunc : ∀ M ∈ edges, ∀ C ∈ oddCs, ∃ v ∈ C, v ∉ M ∪ M.image (a_nx k hk) := by
    intro M hM C hC
    obtain ⟨⟨i, rfl⟩, hodd⟩ := (hmemO C).mp hC
    exact a_odd_unc k hk E M ((hmemE M).mp hM).1 ((hmemE M).mp hM).2 i hodd
  have key : (∀ C ∈ oddCs, (eligible C).Nonempty) ∧
      (∀ f : Finset (Fin k) → Fin k, (∀ C ∈ oddCs, f C ∈ eligible C) →
        ∃ M ∈ edges, Finset.univ \ (M ∪ M.image (a_nx k hk)) = oddCs.image f) ∧
      (∀ M ∈ edges, ∀ C ∈ oddCs, ∀ u ∈ C, u ∉ M ∪ M.image (a_nx k hk) →
        (∀ w ∈ C, w ∉ M ∪ M.image (a_nx k hk) → w = u) → u ∈ eligible C) := by
    by_cases hEu : E = Finset.univ
    · have hel : ∀ C, eligible C = C := by
        intro C
        rw [helig]
        exact ite_eq_left hEu
      subst hEu
      have hO : ∀ C, C ∈ oddCs ↔ C = Finset.univ ∧ k % 2 = 1 := by
        intro C
        rw [hmemO]
        simp only [a_cl_univ k hk]
        constructor
        · rintro ⟨⟨_, rfl⟩, h⟩
          exact ⟨rfl, by rwa [Finset.card_univ, Fintype.card_fin] at h⟩
        · rintro ⟨rfl, h⟩
          exact ⟨⟨⟨0, hk⟩, rfl⟩, by rwa [Finset.card_univ, Fintype.card_fin]⟩
      refine ⟨?_, ?_, ?_⟩
      · intro C hC
        rw [hel, ((hO C).mp hC).1]
        exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      · intro f _
        obtain ⟨M, hM1, hM2⟩ := a_cons_univ k hk (f Finset.univ)
        refine ⟨M, (hmemE M).mpr ⟨Finset.subset_univ _, hM1⟩, ?_⟩
        rw [hM2]
        ext x
        rw [Finset.mem_image]
        constructor
        · intro hx
          by_cases hk2 : k % 2 = 1
          · rw [ite_eq_left hk2, Finset.mem_singleton] at hx
            exact ⟨Finset.univ, (hO _).mpr ⟨rfl, hk2⟩, hx.symm⟩
          · rw [ite_eq_right hk2] at hx
            exact absurd hx (Finset.notMem_empty _)
        · rintro ⟨C, hC, rfl⟩
          obtain ⟨rfl, hk2⟩ := (hO C).mp hC
          rw [ite_eq_left hk2]
          exact Finset.mem_singleton_self _
      · intro M _ C _ u hu _ _
        rw [hel]
        exact hu
    · have hel : ∀ C, eligible C = C.filter (fun v =>
          ∃ s ∈ C, a_pv k hk s ∉ E ∧ ((v.val+k-s.val) % k) % 2 = 0) := by
        intro C
        rw [helig]
        exact ite_eq_right hEu
      refine ⟨?_, ?_, ?_⟩
      · intro C hC
        obtain ⟨⟨i, rfl⟩, _⟩ := (hmemO C).mp hC
        refine ⟨(a_pv k hk)^[a_off k hk E hEu i] i, ?_⟩
        rw [hel, Finset.mem_filter]
        have hmem : (a_pv k hk)^[a_off k hk E hEu i] i ∈
            a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i := by
          rw [a_cl_mem]
          exact Relation.EqvGen.symm _ _ (a_chain k hk E hEu i _ le_rfl)
        refine ⟨hmem, ?_⟩
        have hs0 : a_pv k hk ((a_pv k hk)^[a_off k hk E hEu i] i) ∉ E := by
          have := a_off_spec k hk E hEu i
          rwa [Function.iterate_succ_apply'] at this
        rw [a_elig_iff k hk E hEu i _ hmem, a_off_zero k hk E hEu _ hs0]
      · intro f hf
        obtain ⟨M, hM1, hM2, hM3⟩ := a_cons_ne k hk E hEu oddCs hmemO f (fun C hC => by
          have h1 := hf C hC
          rw [hel, Finset.mem_filter] at h1
          obtain ⟨⟨i, rfl⟩, _⟩ := (hmemO C).mp hC
          exact ⟨h1.1, (a_elig_iff k hk E hEu i _ h1.1).mp h1.2⟩)
        exact ⟨M, (hmemE M).mpr ⟨hM1, hM2⟩, hM3⟩
      · intro M hM C hC u hu hunc' huniq
        obtain ⟨⟨i, rfl⟩, _⟩ := (hmemO C).mp hC
        rw [hel, Finset.mem_filter]
        refine ⟨hu, ?_⟩
        rw [a_elig_iff k hk E hEu i _ hu]
        apply a_par2 k hk E hEu M ((hmemE M).mp hM).1 ((hmemE M).mp hM).2 u hunc'
        intro d hd1 hd2
        by_contra hc
        have hdm : (a_pv k hk)^[d] u ∈ a_cl (fun i j => i ∈ E ∧ j = a_nx k hk i) i := by
          rw [a_cl_mem] at hu ⊢
          exact Relation.EqvGen.trans _ _ _ hu
            (Relation.EqvGen.symm _ _ (a_chain k hk E hEu u d hd2))
        exact a_cyc_ne k hk u d hd1 (lt_of_le_of_lt hd2 (a_off_lt k hk E hEu u))
          (huniq _ hdm hc)
  obtain ⟨hN3, hCON, hELG⟩ := key
  obtain ⟨f0, hf0⟩ : ∃ f0 : Finset (Fin k) → Fin k, ∀ C ∈ oddCs, f0 C ∈ eligible C := by
    refine ⟨fun C => if h : (eligible C).Nonempty then Classical.choose h else ⟨0, hk⟩, ?_⟩
    intro C hC
    dsimp only
    rw [dite_eq_left (hN3 C hC)]
    exact Classical.choose_spec (hN3 C hC)
  obtain ⟨M0, hM0, hM0e⟩ := hCON f0 hf0
  have hM0c : (Finset.univ \ (M0 ∪ M0.image (a_nx k hk))).card = oddCs.card := by
    rw [hM0e]
    exact himgc f0 (fun C hC => hsub C (hf0 C hC))
  have hchoose : ∀ M ∈ edges, ∃ g : Finset (Fin k) → Fin k,
      ∀ C ∈ oddCs, g C ∈ C ∧ g C ∉ M ∪ M.image (a_nx k hk) := by
    intro M hM
    refine ⟨fun C => if h : ∃ v ∈ C, v ∉ M ∪ M.image (a_nx k hk) then Classical.choose h
      else ⟨0, hk⟩, ?_⟩
    intro C hC
    dsimp only
    rw [dite_eq_left (hunc M hM C hC)]
    exact Classical.choose_spec (hunc M hM C hC)
  have hlow : ∀ M ∈ edges, oddCs.card ≤ (Finset.univ \ (M ∪ M.image (a_nx k hk))).card := by
    intro M hM
    obtain ⟨g, hg⟩ := hchoose M hM
    rw [← himgc g (fun C hC => (hg C hC).1)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hg C hC).2⟩
  have hle : ∀ M ∈ edges, M.card ≤ M0.card := by
    intro M hM
    have := hlow M hM
    have := hec M hM
    have := hec M0 hM0
    omega
  have hmu' : mu = M0.card := by
    rw [hmu]
    exact le_antisymm (Finset.sup_le hle) (Finset.le_sup hM0)
  refine ⟨?_, ?_, hN3⟩
  · intro M hMb
    obtain ⟨hM, hMc⟩ := (hmemB M).mp hMb
    have hcardW : (Finset.univ \ (M ∪ M.image (a_nx k hk))).card = oddCs.card := by
      have := hec M hM
      have := hec M0 hM0
      omega
    obtain ⟨g, hg⟩ := hchoose M hM
    have hsub2 : oddCs.image g ⊆ Finset.univ \ (M ∪ M.image (a_nx k hk)) := by
      intro x hx
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hg C hC).2⟩
    have hW : Finset.univ \ (M ∪ M.image (a_nx k hk)) = oddCs.image g := by
      symm
      apply Finset.eq_of_subset_of_card_le hsub2
      rw [hcardW, himgc g (fun C hC => (hg C hC).1)]
    refine ⟨g, ?_, hW⟩
    intro C hC
    apply hELG M hM C hC (g C) (hg C hC).1 (hg C hC).2
    intro w hw hwu
    have hw2 : w ∈ oddCs.image g := by
      rw [← hW]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwu⟩
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hw2
    have hCC : C' = C := by
      rw [hcl C' hC' (g C') (hg C' hC').1, hcl C hC (g C') hw]
    rw [hCC]
  · intro f hf
    obtain ⟨M, hM, hMe⟩ := hCON f hf
    refine ⟨M, (hmemB M).mpr ⟨hM, ?_⟩, hMe⟩
    have h1 : (Finset.univ \ (M ∪ M.image (a_nx k hk))).card = oddCs.card := by
      rw [hMe]
      exact himgc f (fun C hC => hsub C (hf C hC))
    have := hec M hM
    have := hec M0 hM0
    rw [hmu']
    omega
theorem a_struct (k : Nat) (hk : 0 < k) (_h2 : 2 ≤ k) :
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  ∀ (E : Finset (Fin k)),
    let nxt := fun i : Fin k => ix (i.val+1)
    let prv := fun i : Fin k => ix (i.val+k-1)
    let edges := E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)
    let mu := edges.sup Finset.card
    let best := edges.filter (fun M => M.card = mu)
    let ends := fun M : Finset (Fin k) => M ∪ M.image nxt
    let adj := fun i j : Fin k => i ∈ E ∧ j = nxt i
    let cs := (Finset.univ : Finset (Fin k)).image (fun i =>
      (Finset.univ : Finset (Fin k)).filter (fun j =>
        @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
    let oddCs := cs.filter (fun C => C.card % 2 = 1)
    let eligible := fun C : Finset (Fin k) =>
      if E = Finset.univ then C else C.filter (fun v =>
        ∃ s ∈ C, prv s ∉ E ∧ ((v.val+k-s.val) % k) % 2 = 0)
    (∀ M ∈ best, ∃ f : Finset (Fin k) → Fin k, (∀ C ∈ oddCs, f C ∈ eligible C) ∧
        Finset.univ \ ends M = oddCs.image f) ∧
    (∀ f : Finset (Fin k) → Fin k, (∀ C ∈ oddCs, f C ∈ eligible C) →
        ∃ M ∈ best, Finset.univ \ ends M = oddCs.image f) ∧
    (∀ C ∈ oddCs, (eligible C).Nonempty) := by
  intro ix E nxt prv edges mu best ends adj cs oddCs eligible
  exact a_main k hk E edges rfl mu rfl best rfl ends rfl cs rfl oddCs rfl eligible rfl
theorem cut_minmax (k : Nat) (hk : 0 < k) (h2 : 2 ≤ k) (E : Finset (Fin k))
    (g : Nat) (lane phase : Fin k → Nat) :
    let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let nxt := fun i : Fin k => ix (i.val+1)
    let prv := fun i : Fin k => ix (i.val+k-1)
    let edges := E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)
    let mu := edges.sup Finset.card
    let best := edges.filter (fun M => M.card = mu)
    let ends := fun M : Finset (Fin k) => M ∪ M.image nxt
    let adj := fun i j : Fin k => i ∈ E ∧ j = nxt i
    let cs := (Finset.univ : Finset (Fin k)).image (fun i =>
      (Finset.univ : Finset (Fin k)).filter (fun j =>
        @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
    let oddCs := cs.filter (fun C => C.card % 2 = 1)
    let eligible := fun C : Finset (Fin k) =>
      if E = Finset.univ then C else C.filter (fun v =>
        ∃ s ∈ C, prv s ∉ E ∧ ((v.val+k-s.val) % k) % 2 = 0)
    let score := fun U : Finset (Fin k) =>
      ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
    let deficit := oddCs.powerset.sup (fun T =>
      2*g - ((oddCs.card-T.card) + score (T.biUnion eligible)))
    (∀ M ∈ best, score (Finset.univ \ ends M) ≤ 2 * g - deficit) ∧
    (∃ M ∈ best, score (Finset.univ \ ends M) = 2 * g - deficit) ∧
    deficit ≤ 2 * g := by
  intro ix nxt prv edges mu best ends adj cs oddCs eligible score deficit
  obtain ⟨hA1, hA2, hA3⟩ := a_struct k hk h2 E
  have hsc : ∀ U, score U = bscore g lane phase U := fun _ => rfl
  obtain ⟨f0, hf0, T0, hT0, hlow⟩ := b_lower g lane phase oddCs eligible hA3
  obtain ⟨M0, hM0, hM0e⟩ := hA2 f0 hf0
  have hup : ∀ M ∈ best, ∀ T ∈ oddCs.powerset,
      score (Finset.univ \ ends M) ≤ (oddCs.card - T.card) + score (T.biUnion eligible) := by
    intro M hM T hT
    obtain ⟨f, hf, he⟩ := hA1 M hM
    rw [he, hsc, hsc]
    exact b_upper g lane phase oddCs eligible f hf T (Finset.mem_powerset.mp hT)
  have h2g : ∀ U, score U ≤ 2 * g := fun U => by
    rw [hsc]; exact b_le g lane phase U
  have hm1 : (oddCs.card - T0.card) + score (T0.biUnion eligible)
      ≤ score (Finset.univ \ ends M0) := by
    rw [hM0e, hsc, hsc] at *
    exact hlow
  have hm2 : ∀ M ∈ best, score (Finset.univ \ ends M)
      ≤ (oddCs.card - T0.card) + score (T0.biUnion eligible) :=
    fun M hM => hup M hM T0 (Finset.mem_powerset.mpr hT0)
  have hm3 : score (Finset.univ \ ends M0) ≤ 2 * g := h2g _
  have hdef1 : deficit ≤ 2 * g - score (Finset.univ \ ends M0) := by
    refine Finset.sup_le (fun T hT => ?_)
    have := hup M0 hM0 T hT
    omega
  have hdef2 : 2 * g - ((oddCs.card - T0.card) + score (T0.biUnion eligible)) ≤ deficit :=
    Finset.le_sup (f := fun T => 2*g - ((oddCs.card-T.card) + score (T.biUnion eligible)))
      (Finset.mem_powerset.mpr hT0)
  have hM0_up := hm2 M0 hM0
  refine ⟨fun M hM => ?_, ⟨M0, hM0, ?_⟩, ?_⟩
  · have := hm2 M hM; omega
  · omega
  · omega

end PEqualNP.Outside.L_meta_33637_aux.Cut

namespace PEqualNP.Outside.L_meta_33637_aux

abbrev F := ZMod 2
abbrev W (k : Nat) := Fin k → F
abbrev H := List Bool
abbrev Tree (k : Nat) := Finset H × (H → W k →ₗ[F] F) × (H → F) × (H → W k →ₗ[F] W k) × (H → W k)

lemma f2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (a : F) : a + a = 0 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma f2_add_eq_zero {a b : F} : a + b = 0 ↔ a = b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> decide

lemma f2_sub_eq_add (a b : F) : a - b = a + b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> decide

lemma f2_decide_ne_zero_eq {a b : F} : decide (a ≠ 0) = decide (b ≠ 0) ↔ a = b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> decide

def asBool (x : F) : Bool := decide (x ≠ 0)
def asField (x : Bool) : F := if x then 1 else 0

lemma asBool_asField (x : Bool) : asBool (asField x) = x := by
  cases x <;> decide

lemma asField_asBool (x : F) : asField (asBool x) = x := by
  rcases f2_cases x with rfl | rfl <;> decide

lemma asBool_false (x : F) : asBool x = false ↔ x = 0 := by
  rcases f2_cases x with rfl | rfl <;> decide

def ix {k : Nat} (hk : 0 < k) (n : Nat) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

lemma ix_val {k : Nat} (hk : 0 < k) (i : Fin k) : ix hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

lemma ix_add {k : Nat} (hk : 0 < k) (a b : Nat) : ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  apply Fin.ext
  change (a % k + b) % k = (a + b) % k
  rw [Nat.add_mod (a % k) b k, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_mul_right {k : Nat} (hk : 0 < k) (a t : Nat) : ix hk (a + k * t) = ix hk a := by
  apply Fin.ext
  change (a + k * t) % k = a % k
  exact Nat.add_mul_mod_self_left a k t

lemma ix_back_after {k : Nat} (hk : 0 < k) (a d : Nat) :
    ix hk ((ix hk (a + d)).val + k - d % k) = ix hk a := by
  apply Fin.ext
  change ((a + d) % k + k - d % k) % k = a % k
  rw [Nat.add_mod_eq_sub (a := a) (b := d)]
  have ha := Nat.mod_lt a hk
  have hd := Nat.mod_lt d hk
  split
  · rw [show a % k + d % k - 0 + k - d % k = a % k + k by omega, Nat.add_mod_right, Nat.mod_mod]
  · rw [show a % k + d % k - k + k - d % k = a % k by omega, Nat.mod_mod]

lemma ix_after_back {k : Nat} (hk : 0 < k) (u : Fin k) (d : Nat) :
    ix hk ((ix hk (u.val + k - d % k)).val + d) = u := by
  apply Fin.ext
  change ((u.val + k - d % k) % k + d) % k = u.val
  have hu := u.isLt
  have hd := Nat.mod_lt d hk
  rw [Nat.mod_add_mod, ← Nat.add_mod_mod,
      show u.val + k - d % k + d % k = u.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hu]

def reindex {k : Nat} (s : Fin k → Fin k) : W k →ₗ[F] W k where
  toFun x i := x (s i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rotLin {k : Nat} (hk : 0 < k) (n : Nat) : W k →ₗ[F] W k :=
  reindex (fun i => ix hk (i.val + k - n % k))

def fwdEquiv {k : Nat} (hk : 0 < k) (d : Nat) : Fin k ≃ Fin k where
  toFun i := ix hk (i.val + d)
  invFun i := ix hk (i.val + k - d % k)
  left_inv i := by simpa [ix_val hk i] using ix_back_after hk i.val d
  right_inv i := ix_after_back hk i d

lemma rotLin_surjective {k : Nat} (hk : 0 < k) (n : Nat) : Function.Surjective (rotLin hk n) := by
  intro y
  refine ⟨fun i => y (ix hk (i.val + n)), ?_⟩
  funext i
  change y (ix hk ((ix hk (i.val + k - n % k)).val + n)) = y i
  rw [ix_after_back hk i n]

def mixLin {k : Nat} (hk : 0 < k) (spacing : Nat) : W k →ₗ[F] W k :=
  LinearMap.id + reindex (fun i => ix hk (i.val + spacing)) +
    reindex (fun i => ix hk (i.val + k - spacing % k))

def ylin {k : Nat} (hk : 0 < k) (spacing s : Nat) : W k →ₗ[F] W k :=
  (mixLin hk spacing).comp (rotLin hk s)

def yaff {k : Nat} (hk : 0 < k) (spacing s : Nat) (name x : W k) : W k :=
  ylin hk spacing s x + mixLin hk spacing name

def baseLin {k : Nat} (hk : 0 < k) (spacing s t : Nat) : W k →ₗ[F] W k :=
  ylin hk spacing s + rotLin hk t

def biasVec {k : Nat} (hk : 0 < k) (spacing : Nat) (name constant : W k) : W k :=
  mixLin hk spacing name + constant

def rise {k : Nat} (hk : 0 < k) (y : W k) (i : Fin k) : F :=
  (1 + y (Cut.a_nx k hk i)) * y (Cut.a_nx k hk (Cut.a_nx k hk i))

def output {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant x : W k) : W k :=
  fun i => baseLin hk spacing s t x i + biasVec hk spacing name constant i +
    rise hk (yaff hk spacing s name x) i

lemma yaff_literal {k : Nat} (hk : 0 < k) (spacing s : Nat) (name x : W k) (i : Fin k) :
    let old := rotLin hk s x + name
    yaff hk spacing s name x i =
      old i + old (ix hk (i.val + spacing)) + old (ix hk (i.val + k - spacing % k)) := by
  dsimp only
  change (mixLin hk spacing (rotLin hk s x) + mixLin hk spacing name) i = _
  rw [← map_add]
  rfl

lemma output_literal {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant x : W k) (i : Fin k) :
    let old := rotLin hk s x + name
    let y := fun u : Fin k =>
      old u + old (ix hk (u.val + spacing)) + old (ix hk (u.val + k - spacing % k))
    output hk spacing s t name constant x i =
      y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rotLin hk t x i + constant i := by
  dsimp only
  rw [← yaff_literal, ← yaff_literal, ← yaff_literal]
  have e1 : Cut.a_nx k hk i = ix hk (i.val + 1) := rfl
  have e2 : Cut.a_nx k hk (Cut.a_nx k hk i) = ix hk (i.val + 2) := by
    change ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2)
    rw [ix_add, Nat.add_assoc]
  unfold output rise
  rw [e2, e1]
  change ylin hk spacing s x i + rotLin hk t x i + (mixLin hk spacing name i + constant i) + _ =
    (ylin hk spacing s x i + mixLin hk spacing name i) + _ + rotLin hk t x i + constant i
  ring

lemma rise_not_both {k : Nat} (hk : 0 < k) (y : W k) (i : Fin k) :
    rise hk y i ≠ 0 → rise hk y (Cut.a_nx k hk i) = 0 := by
  unfold rise
  rcases f2_cases (y (Cut.a_nx k hk (Cut.a_nx k hk i))) with hz | hz
  · rw [hz, mul_zero]; simp
  · rw [hz]
    have h11 : (1 : F) + 1 = 0 := by decide
    rw [h11, zero_mul]
    intro _; rfl

lemma mix_self_adjoint {k : Nat} (hk : 0 < k) (spacing : Nat) (w x : W k) :
    ∑ j : Fin k, w j * mixLin hk spacing x j = ∑ j : Fin k, mixLin hk spacing w j * x j := by
  let e := fwdEquiv hk spacing
  have h1 : ∑ j : Fin k, w j * mixLin hk spacing x j =
      (∑ j : Fin k, w j * x j) +
      (∑ j : Fin k, w j * x (e j)) +
      (∑ j : Fin k, w j * x (e.symm j)) := by
    have hs : ∀ j : Fin k, w j * mixLin hk spacing x j =
        w j * x j + w j * x (e j) + w j * x (e.symm j) := fun j => by
      change w j * (x j + x (e j) + x (e.symm j)) = _
      ring
    simp_rw [hs, Finset.sum_add_distrib]
  have h2 : ∑ j : Fin k, mixLin hk spacing w j * x j =
      (∑ j : Fin k, w j * x j) +
      (∑ j : Fin k, w (e j) * x j) +
      (∑ j : Fin k, w (e.symm j) * x j) := by
    have hs : ∀ j : Fin k, mixLin hk spacing w j * x j =
        w j * x j + w (e j) * x j + w (e.symm j) * x j := fun j => by
      change (w j + w (e j) + w (e.symm j)) * x j = _
      ring
    simp_rw [hs, Finset.sum_add_distrib]
  have he1 : ∑ j : Fin k, w j * x (e j) = ∑ j : Fin k, w (e.symm j) * x j :=
    Fintype.sum_equiv e (fun j => w j * x (e j)) (fun j => w (e.symm j) * x j) (fun j => by simp)
  have he2 : ∑ j : Fin k, w j * x (e.symm j) = ∑ j : Fin k, w (e j) * x j :=
    Fintype.sum_equiv e.symm (fun j => w j * x (e.symm j)) (fun j => w (e j) * x j) (fun j => by simp)
  rw [h1, h2, he1, he2]
  ring

/-! ### Section 2: Dual Kernel Characterization and Conjunct 1 -/

namespace DualKernel

def Period {A : Type} (x : Nat → A) (p : Nat) : Prop :=
  ∀ i, x (i + p) = x i

lemma period_mul {A : Type} {x : Nat → A} {p : Nat} (hp : Period x p) (m : Nat) :
    Period x (p * m) := by
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]

lemma period_of_dvd {A : Type} {x : Nat → A} {p q : Nat} (hp : Period x p) (d : p ∣ q) :
    Period x q := by
  obtain ⟨t, rfl⟩ := d
  exact period_mul hp t

lemma period_sub {A : Type} {x : Nat → A} {p q : Nat} (hp : Period x p) (hq : Period x q)
    (le : q ≤ p) : Period x (p - q) := by
  intro i
  have e := hq (i + (p - q))
  have f : i + (p - q) + q = i + p := by omega
  rw [f, hp] at e
  exact e.symm

lemma period_mod {A : Type} {x : Nat → A} {p q : Nat} (hp : Period x p) (hq : Period x q) :
    Period x (p % q) := by
  have e := Nat.mod_add_div p q
  have f := period_sub hp (period_mul hq (p / q)) (by omega)
  have h : p - q * (p / q) = p % q := by omega
  rwa [h] at f

lemma period_gcd {A : Type} (x : Nat → A) (p q : Nat) (hp : Period x p) (hq : Period x q) :
    Period x (p.gcd q) := by
  induction p, q using Nat.gcd.induction with
  | H0 n => simpa using hq
  | H1 m n _ ih =>
    rw [Nat.gcd_rec]
    exact ih (period_mod hq hp) hp

lemma eval_mod {A : Type} {x : Nat → A} {p : Nat} (hp : Period x p) (i : Nat) :
    x i = x (i % p) := by
  conv => lhs; rw [← Nat.mod_add_div i p]
  exact period_mul hp (i / p) (i % p)

lemma gcdThree (k d : Nat) (hk : 0 < k) :
    k.gcd (3 * d) = k.gcd d * ((k / (k.gcd d)).gcd 3) := by
  let g := k.gcd d
  let K := k / g
  let D := d / g
  have kfac : g * K = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k d)
  have dfac : g * D = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
  have cop : K.gcd D = 1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hk
  change k.gcd (3 * d) = g * (K.gcd 3)
  rw [← kfac, ← dfac, ← Nat.mul_assoc, Nat.mul_comm 3 g, Nat.mul_assoc, Nat.gcd_mul_left]
  rw [Nat.gcd_mul_left_right_of_gcd_eq_one cop]

lemma gcd_three (n : Nat) : n.gcd 3 = if 3 ∣ n then 3 else 1 := by
  by_cases h : 3 ∣ n
  · rw [ite_eq_left h, Nat.gcd_eq_right h]
  · rw [ite_eq_right h, Nat.gcd_comm n 3, Nat.gcd_rec 3 n]
    have nz : n % 3 ≠ 0 := fun e => h (Nat.dvd_of_mod_eq_zero e)
    have lt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    have e : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases e with e | e <;> rw [e] <;> decide

lemma mod_three_mul (x g : Nat) (hg : 0 < g) :
    x % (3 * g) = x % g + g * ((x / g) % 3) := by
  have h1 : x = x % g + g * (x / g) := (Nat.mod_add_div x g).symm
  have h2 : x / g = (x / g) % 3 + 3 * ((x / g) / 3) := (Nat.mod_add_div (x / g) 3).symm
  have h3 : x = (x % g + g * ((x / g) % 3)) + (3 * g) * ((x / g) / 3) := by
    calc x = x % g + g * ((x / g) % 3 + 3 * ((x / g) / 3)) := by rw [← h2, ← h1]
      _ = (x % g + g * ((x / g) % 3)) + (3 * g) * ((x / g) / 3) := by ring
  have hlt : x % g + g * ((x / g) % 3) < 3 * g := by
    have hr : x % g < g := Nat.mod_lt x hg
    have hq : (x / g) % 3 < 3 := Nat.mod_lt _ (by decide)
    nlinarith
  conv_lhs => rw [h3]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

lemma ker_mix_rec {k : Nat} (hk : 0 < k) (spacing : Nat) {w : W k}
    (hw : mixLin hk spacing w = 0) (n : Nat) :
    w (ix hk n) + w (ix hk (n + spacing)) + w (ix hk (n + spacing + spacing)) = 0 := by
  have h := congrFun hw (ix hk (n + spacing))
  change w (ix hk (n + spacing)) +
    w (ix hk ((ix hk (n + spacing)).val + spacing)) +
    w (ix hk ((ix hk (n + spacing)).val + k - spacing % k)) = 0 at h
  rw [ix_add, ix_back_after] at h
  have hcomm : w (ix hk n) + w (ix hk (n + spacing)) + w (ix hk (n + spacing + spacing)) =
      w (ix hk (n + spacing)) + w (ix hk (n + spacing + spacing)) + w (ix hk n) := by ring
  rw [hcomm, h]

lemma ker_mix_period_3d {k : Nat} (hk : 0 < k) (spacing : Nat) {w : W k}
    (hw : mixLin hk spacing w = 0) : Period (fun n => w (ix hk n)) (3 * spacing) := by
  intro n
  have h1 := ker_mix_rec hk spacing hw n
  have h2 := ker_mix_rec hk spacing hw (n + spacing)
  have h3 : n + 3 * spacing = n + spacing + spacing + spacing := by omega
  rw [h3]
  have hsum : w (ix hk (n + spacing + spacing + spacing)) + w (ix hk n) = 0 := by
    have h4 : w (ix hk (n + spacing)) + w (ix hk (n + spacing)) = 0 := f2_add_self _
    have h5 : w (ix hk (n + spacing + spacing)) + w (ix hk (n + spacing + spacing)) = 0 := f2_add_self _
    linear_combination h1 + h2 - h4 - h5
  exact f2_add_eq_zero.mp hsum

lemma ker_mix_eq_zero_of_not_dvd3 {k : Nat} (hk : 0 < k) (spacing : Nat)
    (hnd : ¬ 3 ∣ k / Nat.gcd k spacing) {w : W k} (hw : mixLin hk spacing w = 0) : w = 0 := by
  let f : Nat → F := fun n => w (ix hk n)
  have pk : Period f k := fun n => by
    dsimp [f]; rw [show n + k = n + k * 1 by omega, ix_add_mul_right]
  have p3d : Period f (3 * spacing) := ker_mix_period_3d hk spacing hw
  have pgcd := period_gcd f k (3 * spacing) pk p3d
  rw [gcdThree k spacing hk, gcd_three, ite_eq_right hnd, Nat.mul_one] at pgcd
  have pd : Period f spacing := period_of_dvd pgcd (Nat.gcd_dvd_right k spacing)
  funext u
  have hrec := ker_mix_rec hk spacing hw u.val
  change f u.val + f (u.val + spacing) + f (u.val + spacing + spacing) = 0 at hrec
  rw [pd (u.val + spacing), pd u.val] at hrec
  have h3f : f u.val + f u.val + f u.val = f u.val := by
    rw [f2_add_self, zero_add]
  rw [h3f] at hrec
  simpa [f, ix_val hk u] using hrec

lemma checks_eq_one_of_not_dvd3 {k : Nat} (hk : 0 < k) (spacing : Nat)
    (hnd : ¬ 3 ∣ k / Nat.gcd k spacing) (P : Finset (Fin k)) :
    ((Finset.univ : Finset (W k)).filter (fun w =>
      (∀ j, j ∉ P → w j = 0) ∧ ∀ j : Fin k,
        w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0)).card = 1 := by
  have heq : (Finset.univ : Finset (W k)).filter (fun w =>
      (∀ j, j ∉ P → w j = 0) ∧ ∀ j : Fin k,
        w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0) = {0} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hmix⟩
      exact ker_mix_eq_zero_of_not_dvd3 hk spacing hnd (funext hmix)
    · rintro rfl
      exact ⟨fun _ _ => rfl, fun j => by simp⟩
  rw [heq, Finset.card_singleton]

lemma card_sol_fin3 (S : Finset Nat) (hS : ∀ x ∈ S, x < 3) :
    Fintype.card {p : Fin 3 → F // p 0 + p 1 + p 2 = 0 ∧ ∀ t : Fin 3, t.val ∈ S → p t = 0} =
      2 ^ (2 - min 2 S.card) := by
  let S3 : Finset (Fin 3) := Finset.univ.filter (fun t : Fin 3 => t.val ∈ S)
  have hScard : S3.card = S.card := by
    refine Finset.card_bij (fun t _ => t.val) ?_ ?_ ?_
    · intro t ht; exact (Finset.mem_filter.mp ht).2
    · intro t1 _ t2 _ h; exact Fin.ext h
    · intro x hx
      refine ⟨⟨x, hS x hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  rw [← hScard]
  let Sol := {p : Fin 3 → F // p 0 + p 1 + p 2 = 0 ∧ ∀ t : Fin 3, t.val ∈ S → p t = 0}
  let Pairs := {ab : F × F //
    ((0 : Fin 3) ∈ S3 → ab.1 = 0) ∧
    ((1 : Fin 3) ∈ S3 → ab.2 = 0) ∧
    ((2 : Fin 3) ∈ S3 → ab.1 + ab.2 = 0)}
  have hEquiv : Sol ≃ Pairs :=
    { toFun := fun p => ⟨(p.val 0, p.val 1), by
        refine ⟨?_, ?_, ?_⟩
        · intro h0; exact p.prop.2 0 (Finset.mem_filter.mp h0).2
        · intro h1; exact p.prop.2 1 (Finset.mem_filter.mp h1).2
        · intro h2
          have hp2 := p.prop.2 2 (Finset.mem_filter.mp h2).2
          have hsum := p.prop.1
          rw [hp2, add_zero] at hsum
          exact hsum⟩
      invFun := fun ab => ⟨fun t => match t with | ⟨0, _⟩ => ab.val.1 | ⟨1, _⟩ => ab.val.2 | ⟨2, _⟩ => ab.val.1 + ab.val.2, by
        refine ⟨?_, ?_⟩
        · dsimp only
          have h1 := f2_add_self ab.val.1
          have h2 := f2_add_self ab.val.2
          linear_combination h1 + h2
        · intro t ht
          have ht3 : t ∈ S3 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
          fin_cases t
          · exact ab.prop.1 ht3
          · exact ab.prop.2.1 ht3
          · exact ab.prop.2.2 ht3⟩
      left_inv := fun p => by
        apply Subtype.ext; funext t
        fin_cases t
        · rfl
        · rfl
        · change p.val 0 + p.val 1 = p.val 2
          have hsum := p.prop.1
          have h2 := f2_add_self (p.val 2)
          linear_combination hsum - h2
      right_inv := fun ab => by
        apply Subtype.ext; rfl }
  rw [Fintype.card_congr hEquiv, Fintype.card_subtype]
  have hgen : ∀ T : Finset (Fin 3),
      ((Finset.univ : Finset (F × F)).filter (fun ab =>
        ((0 : Fin 3) ∈ T → ab.1 = 0) ∧
        ((1 : Fin 3) ∈ T → ab.2 = 0) ∧
        ((2 : Fin 3) ∈ T → ab.1 + ab.2 = 0))).card = 2 ^ (2 - min 2 T.card) := by
    intro T
    by_cases h0 : (0 : Fin 3) ∈ T <;> by_cases h1 : (1 : Fin 3) ∈ T <;> by_cases h2 : (2 : Fin 3) ∈ T
    · have hT : T = {0, 1, 2} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = {0, 1} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = {0, 2} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = {0} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = {1, 2} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = {1} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = {2} := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
    · have hT : T = ∅ := by ext t; fin_cases t <;> simp [h0, h1, h2]
      subst hT; decide
  exact hgen S3

lemma checks_eq_pow_of_dvd3 {k : Nat} (hk : 0 < k) (spacing : Nat)
    (hd3 : 3 ∣ k / Nat.gcd k spacing) (P : Finset (Fin k)) :
    let g := Nat.gcd k spacing
    let lane := fun i : Fin k => i.val % g
    let phase := fun i : Fin k => (i.val / g) % 3
    let score := fun U : Finset (Fin k) =>
      ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
    ((Finset.univ : Finset (W k)).filter (fun w =>
      (∀ j, j ∉ P → w j = 0) ∧ ∀ j : Fin k,
        w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0)).card =
      2 ^ (2 * g - score (Finset.univ \ P)) := by
  intro g lane phase score
  have hg : 0 < g := Nat.gcd_pos_of_pos_left spacing hk
  let m := k / g
  let d := spacing / g
  have hgm : g * m = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k spacing)
  have hgd : g * d = spacing := Nat.mul_div_cancel' (Nat.gcd_dvd_right k spacing)
  have hcop : m.gcd d = 1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hk
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, Nat.mul_zero] at hgm; omega
    · exact hpos
  have h3m : 3 ≤ m := Nat.le_of_dvd hm_pos hd3
  have h3g_dvd_k : 3 * g ∣ k := by
    obtain ⟨t, ht⟩ := hd3
    exact ⟨t, by calc k = g * m := hgm.symm
      _ = g * (3 * t) := by dsimp only [m]; rw [ht]
      _ = 3 * g * t := by ring⟩
  have h3g_le_k : 3 * g ≤ k := Nat.le_of_dvd hk h3g_dvd_k
  have hd_not3 : ¬ 3 ∣ d := by
    intro h3d
    have h := Nat.dvd_gcd hd3 h3d
    rw [hcop] at h
    exact (by decide : ¬ 3 ∣ 1) h
  have hd_mod3 : d % 3 = 1 ∨ d % 3 = 2 := by
    have hlt : d % 3 < 3 := Nat.mod_lt d (by decide)
    have hnz : d % 3 ≠ 0 := fun h0 => hd_not3 (Nat.dvd_of_mod_eq_zero h0)
    omega
  let U := Finset.univ \ P
  let Pf : Fin g → Finset Nat := fun r => ((U.filter (fun v => lane v = r.val)).image phase)
  let Sol : Fin g → Type := fun r =>
    {p : Fin 3 → F // p 0 + p 1 + p 2 = 0 ∧ ∀ t : Fin 3, t.val ∈ Pf r → p t = 0}
  let KerP := {w : W k // (∀ j, j ∉ P → w j = 0) ∧ ∀ j : Fin k,
    w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0}
  have hker_per : ∀ w : KerP, Period (fun n => w.val (ix hk n)) (3 * g) := by
    intro w
    have pk : Period (fun n => w.val (ix hk n)) k := fun n => by
      dsimp only
      rw [show n + k = n + k * 1 by omega, ix_add_mul_right]
    have p3d : Period (fun n => w.val (ix hk n)) (3 * spacing) :=
      ker_mix_period_3d hk spacing (funext w.prop.2)
    have pg := period_gcd (fun n => w.val (ix hk n)) k (3 * spacing) pk p3d
    rw [gcdThree k spacing hk, gcd_three, ite_eq_left hd3] at pg
    simpa [Nat.mul_comm] using pg
  have hker_val : ∀ (w : KerP) (u : Fin k),
      w.val u = w.val (ix hk (lane u + g * phase u)) := by
    intro w u
    have hper := hker_per w
    have h1 := eval_mod hper u.val
    rw [ix_val hk u] at h1
    rw [mod_three_mul u.val g hg] at h1
    exact h1
  have hker_sum : ∀ (w : KerP) (r : Fin g),
      w.val (ix hk (r.val + g * 0)) + w.val (ix hk (r.val + g * 1)) + w.val (ix hk (r.val + g * 2)) = 0 := by
    intro w r
    have hper := hker_per w
    have hrec : w.val (ix hk r.val) + w.val (ix hk (r.val + spacing)) +
        w.val (ix hk (r.val + spacing + spacing)) = 0 :=
      ker_mix_rec hk spacing (funext w.prop.2) r.val
    have e1 : w.val (ix hk (r.val + spacing)) = w.val (ix hk (r.val + g * (d % 3))) := by
      rw [eval_mod hper (r.val + spacing), mod_three_mul _ g hg]
      have hrm : (r.val + spacing) % g = r.val := by
        rw [← hgd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
      have hrd : (r.val + spacing) / g = d := by
        rw [← hgd, Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt r.isLt, Nat.zero_add]
      rw [hrm, hrd]
    have e2 : w.val (ix hk (r.val + spacing + spacing)) = w.val (ix hk (r.val + g * ((2 * d) % 3))) := by
      rw [eval_mod hper (r.val + spacing + spacing), mod_three_mul _ g hg]
      have hss : r.val + spacing + spacing = r.val + g * (2 * d) := by
        calc r.val + spacing + spacing = r.val + 2 * (g * d) := by rw [← hgd]; ring
          _ = r.val + g * (2 * d) := by ring
      rw [hss, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
          Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt r.isLt, Nat.zero_add]
    rw [e1, e2] at hrec
    rcases hd_mod3 with hd1 | hd2
    · have h2d : (2 * d) % 3 = 2 := by omega
      rw [hd1, h2d] at hrec
      simpa using hrec
    · have h2d : (2 * d) % 3 = 1 := by omega
      rw [hd2, h2d] at hrec
      have hre : w.val (ix hk (r.val + g * 0)) + w.val (ix hk (r.val + g * 1)) + w.val (ix hk (r.val + g * 2)) =
          w.val (ix hk r.val) + w.val (ix hk (r.val + g * 2)) + w.val (ix hk (r.val + g * 1)) := by
        simp only [Nat.mul_zero, Nat.add_zero]; ring
      rw [hre, hrec]
  have hlane_fwd : ∀ u : Fin k, lane (ix hk (u.val + spacing)) = lane u := by
    intro u
    have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k spacing
    change ((u.val + spacing) % k) % g = u.val % g
    rw [Nat.mod_mod_of_dvd _ hg_dvd_k, ← hgd, Nat.add_mul_mod_self_left]
  have hlane_bwd : ∀ u : Fin k, lane (ix hk (u.val + k - spacing % k)) = lane u := by
    intro u
    have h := hlane_fwd (ix hk (u.val + k - spacing % k))
    rw [ix_after_back hk u spacing] at h
    exact h.symm
  have hphase_fwd : ∀ u : Fin k, phase (ix hk (u.val + spacing)) = (phase u + d % 3) % 3 := by
    intro u
    have hmod : ((u.val + spacing) % k) % (3 * g) = (u.val + spacing) % (3 * g) :=
      Nat.mod_mod_of_dvd _ h3g_dvd_k
    rw [mod_three_mul _ g hg, mod_three_mul _ g hg] at hmod
    have hrm1 : ((u.val + spacing) % k) % g = u.val % g := hlane_fwd u
    have hrm2 : (u.val + spacing) % g = u.val % g := by
      rw [← hgd, Nat.add_mul_mod_self_left]
    have hrd2 : (u.val + spacing) / g = u.val / g + d := by
      rw [← hgd, Nat.add_mul_div_left _ _ hg]
    rw [hrm1, hrm2, hrd2] at hmod
    have heq : (((u.val + spacing) % k) / g) % 3 = (u.val / g + d) % 3 := by
      have : g * ((((u.val + spacing) % k) / g) % 3) = g * ((u.val / g + d) % 3) := by omega
      exact Nat.eq_of_mul_eq_mul_left hg this
    change (((u.val + spacing) % k) / g) % 3 = ((u.val / g) % 3 + d % 3) % 3
    rw [heq, Nat.add_mod]
  have hphase_bwd : ∀ u : Fin k, phase (ix hk (u.val + k - spacing % k)) = (phase u + 3 - d % 3) % 3 := by
    intro u
    let u' := ix hk (u.val + k - spacing % k)
    have h := hphase_fwd u'
    rw [ix_after_back hk u spacing] at h
    have hp1 : phase u < 3 := Nat.mod_lt _ (by decide)
    have hp2 : phase u' < 3 := Nat.mod_lt _ (by decide)
    change phase u' = (phase u + 3 - d % 3) % 3
    rcases hd_mod3 with hd | hd <;> rw [hd] at h ⊢ <;> omega
  have hEquiv : KerP ≃ (∀ r : Fin g, Sol r) :=
    { toFun := fun w r => ⟨fun t => w.val (ix hk (r.val + g * t.val)), by
        refine ⟨?_, ?_⟩
        · exact hker_sum w r
        · intro t ht
          simp only [Pf, Finset.mem_image, Finset.mem_filter, U, Finset.mem_sdiff,
            Finset.mem_univ, true_and] at ht
          obtain ⟨v, ⟨hvP, hvl⟩, hvp⟩ := ht
          have hv0 : w.val v = 0 := w.prop.1 v hvP
          rw [hker_val w v, hvl, hvp] at hv0
          exact hv0⟩
      invFun := fun a => ⟨fun u => (a ⟨lane u, Nat.mod_lt _ hg⟩).val ⟨phase u, Nat.mod_lt _ (by decide)⟩, by
        refine ⟨?_, ?_⟩
        · intro j hj
          have hmem : phase j ∈ Pf ⟨lane j, Nat.mod_lt _ hg⟩ := by
            simp only [Pf, Finset.mem_image, Finset.mem_filter, U, Finset.mem_sdiff,
              Finset.mem_univ, true_and]
            exact ⟨j, ⟨hj, rfl⟩, rfl⟩
          exact (a ⟨lane j, Nat.mod_lt _ hg⟩).prop.2 ⟨phase j, Nat.mod_lt _ (by decide)⟩ hmem
        · intro j
          have hlf := hlane_fwd j
          have hlb := hlane_bwd j
          have hpf := hphase_fwd j
          have hpb := hphase_bwd j
          let r : Fin g := ⟨lane j, Nat.mod_lt _ hg⟩
          have hr1 : (⟨lane (ix hk (j.val + spacing)), Nat.mod_lt _ hg⟩ : Fin g) = r := Fin.ext hlf
          have hr2 : (⟨lane (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ hg⟩ : Fin g) = r := Fin.ext hlb
          dsimp only
          rw [hr1, hr2]
          have hsum := (a r).prop.1
          have hpj : phase j < 3 := Nat.mod_lt _ (by decide)
          have hp012 : phase j = 0 ∨ phase j = 1 ∨ phase j = 2 := by omega
          rcases hd_mod3 with hd1 | hd2
          · rcases hp012 with hp | hp | hp
            · have e0 : (⟨phase j, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 := Fin.ext hp
              have e1 : (⟨phase (ix hk (j.val + spacing)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 :=
                Fin.ext (by dsimp only; rw [hpf, hp, hd1]; rfl)
              have e2 : (⟨phase (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 :=
                Fin.ext (by dsimp only; rw [hpb, hp, hd1]; rfl)
              rw [e0, e1, e2]; exact hsum
            · have e0 : (⟨phase j, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 := Fin.ext hp
              have e1 : (⟨phase (ix hk (j.val + spacing)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 :=
                Fin.ext (by dsimp only; rw [hpf, hp, hd1]; rfl)
              have e2 : (⟨phase (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 :=
                Fin.ext (by dsimp only; rw [hpb, hp, hd1]; rfl)
              rw [e0, e1, e2]; linear_combination hsum
            · have e0 : (⟨phase j, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 := Fin.ext hp
              have e1 : (⟨phase (ix hk (j.val + spacing)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 :=
                Fin.ext (by dsimp only; rw [hpf, hp, hd1]; rfl)
              have e2 : (⟨phase (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 :=
                Fin.ext (by dsimp only; rw [hpb, hp, hd1]; rfl)
              rw [e0, e1, e2]; linear_combination hsum
          · rcases hp012 with hp | hp | hp
            · have e0 : (⟨phase j, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 := Fin.ext hp
              have e1 : (⟨phase (ix hk (j.val + spacing)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 :=
                Fin.ext (by dsimp only; rw [hpf, hp, hd2]; rfl)
              have e2 : (⟨phase (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 :=
                Fin.ext (by dsimp only; rw [hpb, hp, hd2]; rfl)
              rw [e0, e1, e2]; linear_combination hsum
            · have e0 : (⟨phase j, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 := Fin.ext hp
              have e1 : (⟨phase (ix hk (j.val + spacing)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 :=
                Fin.ext (by dsimp only; rw [hpf, hp, hd2]; rfl)
              have e2 : (⟨phase (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 :=
                Fin.ext (by dsimp only; rw [hpb, hp, hd2]; rfl)
              rw [e0, e1, e2]; linear_combination hsum
            · have e0 : (⟨phase j, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 := Fin.ext hp
              have e1 : (⟨phase (ix hk (j.val + spacing)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 :=
                Fin.ext (by dsimp only; rw [hpf, hp, hd2]; rfl)
              have e2 : (⟨phase (ix hk (j.val + k - spacing % k)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 :=
                Fin.ext (by dsimp only; rw [hpb, hp, hd2]; rfl)
              rw [e0, e1, e2]; linear_combination hsum⟩
      left_inv := fun w => by
        apply Subtype.ext; funext u
        exact (hker_val w u).symm
      right_inv := fun a => by
        funext r
        apply Subtype.ext; funext t
        have hlt : r.val + g * t.val < k := by
          have hr := r.isLt
          have ht := t.isLt
          nlinarith
        have hmod : (ix hk (r.val + g * t.val)).val = r.val + g * t.val :=
          Nat.mod_eq_of_lt hlt
        have hln : lane (ix hk (r.val + g * t.val)) = r.val := by
          change (ix hk (r.val + g * t.val)).val % g = r.val
          rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
        have hph : phase (ix hk (r.val + g * t.val)) = t.val := by
          change ((ix hk (r.val + g * t.val)).val / g) % 3 = t.val
          rw [hmod, Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt r.isLt, Nat.zero_add,
              Nat.mod_eq_of_lt t.isLt]
        have hr_eq : (⟨lane (ix hk (r.val + g * t.val)), Nat.mod_lt _ hg⟩ : Fin g) = r := Fin.ext hln
        have ht_eq : (⟨phase (ix hk (r.val + g * t.val)), Nat.mod_lt _ (by decide)⟩ : Fin 3) = t := Fin.ext hph
        dsimp only
        rw [hr_eq, ht_eq] }
  have hcard1 : ((Finset.univ : Finset (W k)).filter (fun w =>
      (∀ j, j ∉ P → w j = 0) ∧ ∀ j : Fin k,
        w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0)).card =
      Fintype.card KerP := by
    rw [Fintype.card_subtype]
  rw [hcard1, Fintype.card_congr hEquiv, Fintype.card_pi]
  have hfac : ∀ r : Fin g, Fintype.card (Sol r) = 2 ^ (2 - min 2 (Pf r).card) := fun r => by
    apply card_sol_fin3 (Pf r)
    intro x hx
    simp only [Pf, Finset.mem_image] at hx
    obtain ⟨v, _, rfl⟩ := hx
    exact Nat.mod_lt _ (by decide)
  simp_rw [hfac, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum_fin : ∑ r : Fin g, (2 - min 2 (Pf r).card) =
      ∑ j ∈ Finset.range g, (2 - min 2 (((U.filter (fun v => lane v = j)).image phase).card)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => 2 - min 2 (((U.filter (fun v => lane v = j)).image phase).card)) g]
  rw [hsum_fin]
  have hadd : (∑ j ∈ Finset.range g, (2 - min 2 (((U.filter (fun v => lane v = j)).image phase).card))) +
      score U = 2 * g := by
    dsimp only [score]
    rw [← Finset.sum_add_distrib]
    have h2 : ∀ j ∈ Finset.range g,
        (2 - min 2 (((U.filter (fun v => lane v = j)).image phase).card)) +
        min 2 (((U.filter (fun v => lane v = j)).image phase).card) = 2 := by
      intro j _
      have := Nat.min_le_left 2 (((U.filter (fun v => lane v = j)).image phase).card)
      omega
    rw [Finset.sum_congr rfl h2]
    simp [Nat.mul_comm]
  change (∑ j ∈ Finset.range g, (2 - min 2 (((U.filter (fun v => lane v = j)).image phase).card))) =
    2 * g - score U
  omega

end DualKernel

/-! ### Section 3: Tree History, Fixed Pinning Tree, and Upper Bound (Conjunct 2) -/

namespace TreeAux

def cut (b : Bool) : List H → List H
  | [] => []
  | [] :: ns => cut b ns
  | (a :: p) :: ns => if a = b then p :: cut b ns else cut b ns

lemma mem_cut (b : Bool) (p : H) (ns : List H) : p ∈ cut b ns ↔ (b :: p) ∈ ns := by
  induction ns with
  | nil => simp [cut]
  | cons h ns ih =>
    cases h with
    | nil => simp [cut, ih]
    | cons a h =>
      by_cases eq : a = b
      · subst a; simp [cut, ih]
      · have ne : b ≠ a := Ne.symm eq
        simp [cut, eq, ne, ih]

lemma cut_budget (ns : List H) :
    (cut false ns).length + (cut true ns).length + (if [] ∈ ns then 1 else 0) ≤ ns.length := by
  induction ns with
  | nil => simp [cut]
  | cons h ns ih =>
    cases h with
    | nil =>
      simp only [cut, List.mem_cons, true_or, ite_true, List.length_cons]
      have h := Nat.le_add_right ((cut false ns).length + (cut true ns).length)
        (if [] ∈ ns then 1 else 0)
      omega
    | cons a h =>
      cases a <;> simp [cut] at ih ⊢ <;> omega

def leaves (ns : List H) : Nat → List H
  | 0 => [[]]
  | d + 1 => if [] ∈ ns then
      (leaves (cut false ns) d).map (false :: ·) ++
      (leaves (cut true ns) d).map (true :: ·)
    else [[]]

lemma leaf_budget (d : Nat) (ns : List H) : (leaves ns d).length ≤ ns.length + 1 := by
  induction d generalizing ns with
  | zero => simp [leaves]
  | succ d ih =>
    by_cases h : [] ∈ ns
    · have l := ih (cut false ns)
      have r := ih (cut true ns)
      have b := cut_budget ns
      simp only [h, ite_true] at b
      simp only [leaves, h, ite_true, List.length_append, List.length_map]
      omega
    · simp [leaves, h]

def advance (ns : List H) (answer : H → Bool) (p : H) : H :=
  if p ∈ ns then p ++ [answer p] else p

def follow (ns : List H) (answer : H → Bool) : Nat → H → H
  | 0, p => p
  | d + 1, p => follow ns answer d (advance ns answer p)

lemma no_node (ns : List H) (Q : H → Bool) (d : Nat) (p : H) (h : p ∉ ns) :
    follow ns Q d p = p := by
  induction d with
  | zero => rfl
  | succ d ih => simp [follow, advance, h, ih]

lemma advance_shift (ns : List H) (Q : H → Bool) (b : Bool) (p : H) :
    advance ns Q (b :: p) = b :: advance (cut b ns) (fun q => Q (b :: q)) p := by
  unfold advance
  simp only [mem_cut]
  split <;> rfl

lemma follow_shift (ns : List H) (Q : H → Bool) (b : Bool) (d : Nat) (p : H) :
    follow ns Q d (b :: p) = b :: follow (cut b ns) (fun q => Q (b :: q)) d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [follow, advance_shift]
    exact ih _

lemma mem_leaves (d : Nat) (ns : List H) (Q : H → Bool) :
    follow ns Q d [] ∈ leaves ns d := by
  induction d generalizing ns Q with
  | zero => simp [follow, leaves]
  | succ d ih =>
    by_cases h : [] ∈ ns
    · simp only [follow, advance, leaves, h, ite_true, List.nil_append, follow_shift]
      cases a : Q [] with
      | false =>
        apply List.mem_append_left
        apply List.mem_map_of_mem
        exact ih _ _
      | true =>
        apply List.mem_append_right
        apply List.mem_map_of_mem
        exact ih _ _
    · simp [no_node _ _ _ _ h, leaves, h]

lemma fold_follow {α : Type} (ns : List H) (Q : H → Bool) (xs : List α) (p : H) :
    xs.foldl (fun q _ => advance ns Q q) p = follow ns Q xs.length p := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.length_cons, follow, ih]

lemma exact_leaf_list (ns : List H) (N : Nat) :
    ∃ ls : List H, ls.length ≤ ns.length + 1 ∧
      ∀ Q : H → Bool, (List.range N).foldl (fun p _ =>
        if p ∈ ns then p ++ [Q p] else p) [] ∈ ls := by
  refine ⟨leaves ns N, leaf_budget _ _, ?_⟩
  intro Q
  change (List.range N).foldl (fun p _ => advance ns Q p) [] ∈ _
  rw [fold_follow, List.length_range]
  apply mem_leaves

lemma prefix_follow (ns : List H) (Q : H → Bool) (d : Nat) (p : H) :
    ∃ r : H, follow ns Q d p = p ++ r := by
  induction d generalizing p with
  | zero => exact ⟨[], by simp [follow]⟩
  | succ d ih =>
    obtain ⟨r, hr⟩ := ih (advance ns Q p)
    by_cases h : p ∈ ns
    · refine ⟨Q p :: r, ?_⟩
      simpa only [follow, advance, h, ite_true, List.append_assoc, List.cons_append, List.nil_append] using hr
    · refine ⟨r, ?_⟩
      simpa only [follow, advance, h, ite_false] using hr

lemma reachable_leaf_cell (ns : List H) (Q : H → Bool) (d : Nat) (p : H) :
    ∃ checks : List (H × Bool), ∀ R : H → Bool,
      follow ns R d p = follow ns Q d p ↔ ∀ z ∈ checks, R z.1 = z.2 := by
  induction d generalizing p with
  | zero => exact ⟨[], fun _ => by simp [follow]⟩
  | succ d ih =>
    by_cases h : p ∈ ns
    · obtain ⟨checks, hc⟩ := ih (p ++ [Q p])
      refine ⟨(p, Q p) :: checks, fun R => ?_⟩
      simp only [follow, advance, h, ite_true]
      constructor
      · intro same
        obtain ⟨s, hs⟩ := prefix_follow ns R d (p ++ [R p])
        obtain ⟨t, ht⟩ := prefix_follow ns Q d (p ++ [Q p])
        have hb : R p = Q p := by
          rw [hs, ht] at same
          have e := List.append_inj_left same (by simp)
          exact (List.cons.inj (List.append_cancel_left e)).1
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hb
        · apply ((hc R).mp ?_) z hz
          simpa only [hb] using same
      · intro agree
        have same₁ := agree (p, Q p) List.mem_cons_self
        change R p = Q p at same₁
        rw [same₁]
        exact (hc R).mpr (fun z hz => agree z (List.mem_cons_of_mem _ hz))
    · exact ⟨[], fun R => by simp [no_node _ R _ _ h, no_node _ Q _ _ h]⟩

def fixedNodesList : Nat → List H
  | 0 => []
  | d + 1 => [] :: (fixedNodesList d).map (false :: ·) ++ (fixedNodesList d).map (true :: ·)

lemma fixedNodes_mem (d : Nat) (p : H) : p ∈ fixedNodesList d ↔ p.length < d := by
  induction d generalizing p with
  | zero => simp [fixedNodesList]
  | succ d ih =>
    cases p with
    | nil => simp [fixedNodesList]
    | cons v p => cases v <;> simp [fixedNodesList, ih]

private lemma cons_nd (ps : List H) (nd : ps.Nodup) (b : Bool) : (ps.map (b :: ·)).Nodup :=
  List.pairwise_map.mpr (nd.imp (fun hn e => hn (List.cons.inj e).2))

lemma fixedNodes_nodup (d : Nat) : (fixedNodesList d).Nodup := by
  induction d with
  | zero => simp [fixedNodesList]
  | succ d ih =>
    rw [fixedNodesList]
    change ([] :: ((fixedNodesList d).map (false :: ·) ++ (fixedNodesList d).map (true :: ·))).Nodup
    rw [List.nodup_cons]
    refine ⟨by simp, List.nodup_append.mpr ⟨cons_nd _ ih _, cons_nd _ ih _, ?_⟩⟩
    intro a ha b hb e
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    cases e

lemma fixedNodes_count (d : Nat) : (fixedNodesList d).length + 1 = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [fixedNodesList, List.length_cons, List.length_append, List.length_map, Nat.pow_succ]
    omega

lemma fixedNodes_depth_le (d : Nat) : d ≤ (fixedNodesList d).length := by
  induction d with
  | zero => simp
  | succ d ih =>
    simp only [fixedNodesList, List.length_cons, List.length_append, List.length_map]
    omega

lemma fixed_final_length (d : Nat) (A : Nat → Bool) (fuel : Nat) (p : H) (hp : p.length ≤ d) :
    (follow (fixedNodesList d) (fun a => A a.length) fuel p).length = min d (p.length + fuel) := by
  induction fuel generalizing p with
  | zero => simp [follow, Nat.min_eq_right hp]
  | succ fuel ih =>
    by_cases e : p.length < d
    · have he := (fixedNodes_mem d p).mpr e
      simp only [follow, advance, he, ite_true]
      rw [ih (p ++ [A p.length]) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      congr 1; omega
    · have he : p ∉ fixedNodesList d :=
        fun h => (Nat.not_lt.mpr (Nat.le_of_not_gt e)) ((fixedNodes_mem d p).mp h)
      rw [no_node _ _ _ _ he, Nat.min_eq_left (by omega)]
      omega

lemma fixed_answer_get (d : Nat) (A : Nat → Bool) (fuel : Nat) (p : H)
    (j : Nat) (hj : p.length ≤ j)
    (hr : j < (follow (fixedNodesList d) (fun a => A a.length) fuel p).length) :
    (follow (fixedNodesList d) (fun a => A a.length) fuel p)[j] = A j := by
  induction fuel generalizing p with
  | zero =>
    change j < p.length at hr; omega
  | succ fuel ih =>
    by_cases e : p ∈ fixedNodesList d
    · have eq : follow (fixedNodesList d) (fun a => A a.length) (fuel + 1) p =
          follow (fixedNodesList d) (fun a => A a.length) fuel (p ++ [A p.length]) := by
        simp [follow, advance, e]
      simp only [eq] at hr ⊢
      by_cases h : j = p.length
      · subst j
        obtain ⟨ss, hss⟩ := prefix_follow (fixedNodesList d) (fun a => A a.length) fuel (p ++ [A p.length])
        simp only [hss]
        rw [List.getElem_append_left (by simp), List.getElem_append_right (by omega)]
        simp
      · exact ih (p ++ [A p.length]) (by simp; omega) hr
    · have eq := no_node (fixedNodesList d) (fun a => A a.length) (fuel + 1) p e
      rw [eq] at hr; omega

lemma fixed_history (d : Nat) (A : Nat → Bool) (fuel : Nat) (hf : d ≤ fuel) :
    let p := (List.range fuel).foldl (fun p _ =>
      if p ∈ fixedNodesList d then p ++ [A p.length] else p) []
    p.length = d ∧ ∀ j : Nat, j < d → p[j]? = some (A j) := by
  dsimp only
  have e := fold_follow (fixedNodesList d) (fun a => A a.length) (List.range fuel) []
  have len : (follow (fixedNodesList d) (fun a => A a.length) fuel []).length = d := by
    rw [fixed_final_length _ _ _ _ (by simp), List.length_nil, Nat.zero_add, Nat.min_eq_left hf]
  simp only [List.length_range] at e
  refine ⟨e ▸ len, ?_⟩
  intro j hj
  change ((List.range fuel).foldl (fun q _ => advance (fixedNodesList d) (fun a => A a.length) q) [])[j]? = _
  rw [e, List.getElem?_eq_getElem (by omega), fixed_answer_get d A fuel [] j (by simp) (by omega)]

end TreeAux

namespace Upper

def hist {k : Nat} (tree : Tree k) (x : W k) : H :=
  (List.range tree.1.card).foldl (fun (p : H) _ =>
    if p ∈ tree.1 then p ++ [decide (tree.2.1 p x + tree.2.2.1 p ≠ 0)] else p) []

def predict {k : Nat} (tree : Tree k) (x : W k) : W k :=
  let p := hist tree x
  tree.2.2.2.1 p x + tree.2.2.2.2 p

def coord {k : Nat} (i : Fin k) : W k →ₗ[F] F where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coord_apply {k : Nat} (i : Fin k) (x : W k) : coord i x = x i := rfl

def own {k : Nat} (hk : 0 < k) (C : Finset (Fin k)) (i : Fin k) : Fin k :=
  if i ∈ C then i else Cut.a_nx k hk i

lemma own_mem {k : Nat} (hk : 0 < k) (C : Finset (Fin k)) (i : Fin k)
    (cover : i ∈ C ∨ Cut.a_nx k hk i ∈ C) : own hk C i ∈ C := by
  unfold own
  split <;> rename_i c
  · exact c
  · exact cover.resolve_left c

lemma own_injective_rises {k : Nat} (hk : 0 < k) (C : Finset (Fin k)) (y : W k)
    {i j : Fin k} (hi : rise hk y i ≠ 0) (hj : rise hk y j ≠ 0)
    (eq : own hk C i = own hk C j) : i = j := by
  unfold own at eq
  split at eq <;> split at eq
  · exact eq
  · exact False.elim (hi (eq ▸ rise_not_both hk y j hj))
  · exact False.elim (hj (eq.symm ▸ rise_not_both hk y i hi))
  · exact Cut.a_nx_inj k hk eq

noncomputable def fixedNodes (n : Nat) : Finset H := (TreeAux.fixedNodesList n).toFinset

def chooseAsk {k : Nat} (hk : 0 < k) (spacing s : Nat) (qs : List (Fin k)) (p : H) : W k →ₗ[F] F :=
  if h : p.length < qs.length then (coord (Cut.a_nx k hk qs[p.length])).comp (ylin hk spacing s) else 0

def chooseBias {k : Nat} (hk : 0 < k) (spacing : Nat) (name : W k) (qs : List (Fin k)) (p : H) : F :=
  if h : p.length < qs.length then mixLin hk spacing name (Cut.a_nx k hk qs[p.length]) else 0

def pin {k : Nat} (qs : List (Fin k)) (p : H) (i : Fin k) : F :=
  asField ((p[qs.idxOf i]?).getD false)

def correctionLin {k : Nat} (hk : 0 < k) (spacing s : Nat) (C Q : Finset (Fin k))
    (qs : List (Fin k)) (p : H) (i : Fin k) : W k →ₗ[F] F :=
  let o := own hk C i
  let a := pin qs p o
  if o ∈ Q then
    if o = i then (1 + a) • (coord (Cut.a_nx k hk (Cut.a_nx k hk i))).comp (ylin hk spacing s)
    else a • (coord (Cut.a_nx k hk i)).comp (ylin hk spacing s)
  else 0

def correctionBias {k : Nat} (hk : 0 < k) (spacing : Nat) (name : W k) (C Q : Finset (Fin k))
    (qs : List (Fin k)) (p : H) (i : Fin k) : F :=
  let o := own hk C i
  let a := pin qs p o
  if o ∈ Q then
    if o = i then (1 + a) * mixLin hk spacing name (Cut.a_nx k hk (Cut.a_nx k hk i))
    else a * (1 + mixLin hk spacing name (Cut.a_nx k hk i))
  else 0

noncomputable def fixedTree {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant : W k)
    (C Q : Finset (Fin k)) : Tree k :=
  let qs := Q.toList
  (fixedNodes qs.length, chooseAsk hk spacing s qs, chooseBias hk spacing name qs,
    fun p => baseLin hk spacing s t + LinearMap.pi (correctionLin hk spacing s C Q qs p),
    fun p => biasVec hk spacing name constant + correctionBias hk spacing name C Q qs p)

lemma fixed_card {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant : W k)
    (C Q : Finset (Fin k)) :
    (fixedTree hk spacing s t name constant C Q).1.card + 1 = 2 ^ Q.card := by
  unfold fixedTree fixedNodes
  simp only [List.toFinset_card_of_nodup (TreeAux.fixedNodes_nodup _), Finset.length_toList,
    TreeAux.fixedNodes_count]

lemma fixed_pin {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant x : W k)
    (C Q : Finset (Fin k)) (i : Fin k) (hi : i ∈ Q) :
    pin Q.toList (hist (fixedTree hk spacing s t name constant C Q) x) i =
      yaff hk spacing s name x (Cut.a_nx k hk i) := by
  classical
  let qs := Q.toList
  let tree := fixedTree hk spacing s t name constant C Q
  let A := fun j : Nat =>
    if h : j < qs.length then asBool (yaff hk spacing s name x (Cut.a_nx k hk qs[j])) else false
  have Aeq (p : H) : decide (tree.2.1 p x + tree.2.2.1 p ≠ 0) = A p.length := by
    change asBool (chooseAsk hk spacing s qs p x + chooseBias hk spacing name qs p) = _
    unfold chooseAsk chooseBias A
    split
    · rfl
    · simpa using (asBool_false 0).mpr rfl
  have ds : qs.length ≤ tree.1.card := by
    change qs.length ≤ (TreeAux.fixedNodesList qs.length).toFinset.card
    rw [List.toFinset_card_of_nodup (TreeAux.fixedNodes_nodup _)]
    exact TreeAux.fixedNodes_depth_le _
  have he : hist tree x = (List.range tree.1.card).foldl (fun p _ =>
      if p ∈ TreeAux.fixedNodesList qs.length then p ++ [A p.length] else p) [] := by
    unfold hist
    simp only [Aeq]
    change (List.range tree.1.card).foldl (fun (p : H) _ =>
      if p ∈ (TreeAux.fixedNodesList qs.length).toFinset then p ++ [A p.length] else p) [] = _
    simp only [List.mem_toFinset]
  have j : qs.idxOf i < qs.length := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr hi)
  have hx := (TreeAux.fixed_history qs.length A tree.1.card ds).2 _ j
  change asField ((hist tree x)[qs.idxOf i]?.getD false) = _
  rw [he, hx]
  change asField (A (qs.idxOf i)) = _
  unfold A
  rw [dite_eq_left j, List.getElem_idxOf]
  exact asField_asBool _

lemma fixed_output {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant x : W k)
    (C Q : Finset (Fin k)) (i : Fin k) :
    predict (fixedTree hk spacing s t name constant C Q) x i =
      baseLin hk spacing s t x i + biasVec hk spacing name constant i +
      (if own hk C i ∈ Q then rise hk (yaff hk spacing s name x) i else 0) := by
  classical
  let p := hist (fixedTree hk spacing s t name constant C Q) x
  let o := own hk C i
  let qs := Q.toList
  change (baseLin hk spacing s t x i + correctionLin hk spacing s C Q qs p i x) +
    (biasVec hk spacing name constant i + correctionBias hk spacing name C Q qs p i) = _
  unfold correctionLin correctionBias
  dsimp only
  change ((baseLin hk spacing s t x i +
    ((if o ∈ Q then _ else 0) : W k →ₗ[F] F) x) +
    (biasVec hk spacing name constant i + (if o ∈ Q then _ else 0))) =
    baseLin hk spacing s t x i + biasVec hk spacing name constant i +
      (if o ∈ Q then rise hk (yaff hk spacing s name x) i else 0)
  by_cases h : o ∈ Q
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, fixed_pin hk spacing s t name constant x C Q o h]
    change _ = _ + rise hk (yaff hk spacing s name x) i
    by_cases oi : o = i
    · have eq : own hk C i = i := oi
      simp only [eq, ite_true, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, coord_apply, oi]
      unfold rise
      change _ = _ + (1 + yaff hk spacing s name x (Cut.a_nx k hk i)) *
        (ylin hk spacing s x (Cut.a_nx k hk (Cut.a_nx k hk i)) +
          mixLin hk spacing name (Cut.a_nx k hk (Cut.a_nx k hk i)))
      ring
    · have oe : o = Cut.a_nx k hk i := by
        change (if i ∈ C then i else Cut.a_nx k hk i) = _
        by_cases ic : i ∈ C
        · exact False.elim (oi (ite_eq_left ic))
        · exact ite_eq_right ic
      rw [ite_eq_right oi, ite_eq_right oi, oe]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, coord_apply]
      unfold rise
      change _ = _ + (1 + (ylin hk spacing s x (Cut.a_nx k hk i) +
          mixLin hk spacing name (Cut.a_nx k hk i))) *
        yaff hk spacing s name x (Cut.a_nx k hk (Cut.a_nx k hk i))
      ring
  · simp only [ite_eq_right h, LinearMap.zero_apply, add_zero]

lemma upper_bound {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant : W k)
    (sites : Finset (Fin k)) (e : Nat) (hsites : sites ≠ Finset.univ) :
    let E := sites.image (Cut.a_nx k hk)
    let edges := E.powerset.filter (fun M => ∀ i ∈ M, Cut.a_nx k hk i ∉ M)
    let mu := edges.sup Finset.card
    ∃ tree : Tree k, tree.1.card < 2 ^ (mu - e) ∧
      ∀ x : W k, (sites.filter (fun i => predict tree x i ≠ output hk spacing s t name constant x i)).card ≤ e := by
  classical
  intro E edges mu
  have hshift_mem : ∀ S : Finset (Fin k), S ⊆ sites →
      (∀ i ∈ S, Cut.a_nx k hk i ∉ S) → S.image (Cut.a_nx k hk) ∈ edges := by
    intro S hS hind
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.image_subset_image hS, ?_⟩
    intro u hu hnu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hnu
    have hij : Cut.a_nx k hk i = j := Cut.a_nx_inj k hk hjeq.symm
    exact hind i hi (hij ▸ hj)
  by_cases exc : mu ≤ e
  · let tree := fixedTree hk spacing s t name constant ∅ ∅
    refine ⟨tree, ?_, ?_⟩
    · have b := fixed_card hk spacing s t name constant ∅ ∅
      have pos : 0 < 2 ^ (mu - e) := Nat.two_pow_pos _
      change tree.1.card + 1 = 2 ^ 0 at b
      omega
    · intro x
      let bad := sites.filter (fun i => predict tree x i ≠ output hk spacing s t name constant x i)
      have hbad_sub : bad ⊆ sites := Finset.filter_subset _ _
      have hnz : ∀ i ∈ bad, rise hk (yaff hk spacing s name x) i ≠ 0 := by
        intro i hi hz
        have hne := (Finset.mem_filter.mp hi).2
        rw [fixed_output, output, hz, ite_eq_right (Finset.notMem_empty _), add_zero] at hne
        exact hne rfl
      have hind : ∀ i ∈ bad, Cut.a_nx k hk i ∉ bad :=
        fun i hi hj => hnz _ hj (rise_not_both hk _ _ (hnz _ hi))
      have hmem : bad.image (Cut.a_nx k hk) ∈ edges := hshift_mem bad hbad_sub hind
      have hcard : bad.card = (bad.image (Cut.a_nx k hk)).card :=
        (Finset.card_image_of_injective bad (Cut.a_nx_inj k hk)).symm
      have hle : (bad.image (Cut.a_nx k hk)).card ≤ mu :=
        Finset.le_sup (f := Finset.card) hmem
      change bad.card ≤ e
      omega
  · let Mg := sites.filter (fun i => Cut.a_off k hk sites hsites i % 2 = 0)
    let C := Mg.image (Cut.a_nx k hk)
    have hMg_sub : Mg ⊆ sites := Finset.filter_subset _ _
    have hMg_ind : ∀ i ∈ Mg, Cut.a_nx k hk i ∉ Mg := by
      intro i hi hni
      have h1 := (Finset.mem_filter.mp hi)
      have h2 := (Finset.mem_filter.mp hni).2
      rw [Cut.a_off_nx_in k hk sites hsites i h1.1] at h2
      omega
    have hC_card : C.card ≤ mu :=
      Finset.le_sup (f := Finset.card) (hshift_mem Mg hMg_sub hMg_ind)
    have hC_cov : ∀ i ∈ sites, i ∈ C ∨ Cut.a_nx k hk i ∈ C := by
      intro i hi
      by_cases hp : Cut.a_off k hk sites hsites i % 2 = 0
      · right
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi, hp⟩)
      · left
        have hpv_mem : Cut.a_pv k hk i ∈ sites := by
          by_contra hnot
          have h0 := Cut.a_off_zero k hk sites hsites i hnot
          omega
        have hsucc := Cut.a_off_succ k hk sites hsites i hpv_mem
        have hpv_even : Cut.a_off k hk sites hsites (Cut.a_pv k hk i) % 2 = 0 := by omega
        have hmem_Mg : Cut.a_pv k hk i ∈ Mg := Finset.mem_filter.mpr ⟨hpv_mem, hpv_even⟩
        have hnx := Cut.a_nx_pv k hk i
        rw [← hnx]
        exact Finset.mem_image_of_mem _ hmem_Mg
    obtain ⟨Del, hDel_sub, hDel_card⟩ := Finset.exists_subset_card_eq (Nat.min_le_right e C.card)
    let Q := C \ Del
    let tree := fixedTree hk spacing s t name constant C Q
    refine ⟨tree, ?_, ?_⟩
    · have hQcard : Q.card = C.card - Del.card := Finset.card_sdiff_of_subset hDel_sub
      have b := fixed_card hk spacing s t name constant C Q
      change tree.1.card + 1 = 2 ^ Q.card at b
      have hDel_cases : Del.card = e ∨ Del.card = C.card := by
        rw [hDel_card]; exact min_choice e C.card
      have hQle : Q.card ≤ mu - e := by
        rcases hDel_cases with h | h <;> omega
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hQle
      omega
    · intro x
      let bad := sites.filter (fun i => predict tree x i ≠ output hk spacing s t name constant x i)
      have err : ∀ i ∈ bad, own hk C i ∈ Del ∧ rise hk (yaff hk spacing s name x) i ≠ 0 := by
        intro i hi
        obtain ⟨hsite, he⟩ := Finset.mem_filter.mp hi
        have hm : own hk C i ∈ C := own_mem hk C i (hC_cov i hsite)
        rw [fixed_output, output] at he
        by_cases hq : own hk C i ∈ Q
        · exact False.elim (he (by rw [ite_eq_left hq]))
        · refine ⟨?_, ?_⟩
          · by_contra hd
            exact hq (Finset.mem_sdiff.mpr ⟨hm, hd⟩)
          · intro hz
            exact he (by rw [ite_eq_right hq, hz])
      have bc := Finset.card_le_card_of_injOn (own hk C)
        (s := bad) (t := Del) (fun i hi => (err i hi).1)
        (fun i hi j hj eq => own_injective_rises hk C _ (err i hi).2 (err j hj).2 eq)
      exact bc.trans (hDel_card ▸ Nat.min_le_left _ _)

end Upper

/-! ### Section 4: Linear Algebra Coordinate Extraction, AllWrong, and Lower Bound (Conjunct 3) -/

namespace Lower

lemma allwrong {K ι V : Type*} [CommRing K] [AddCommGroup V] [Module K V] [DecidableEq ι]
    (α β : ι → V →ₗ[K] K) (p q : ι → K) (N : Finset ι)
    (hs : ∀ z : ι → K × K, ∃ v, ∀ i ∈ N, α i v = (z i).1 ∧ β i v = (z i).2)
    (g : ι → V →ₗ[K] K) (c : ι → K) :
    ∃ v, ∀ i ∈ N, (α i v + p i) * (β i v + q i) + g i v + c i = 1 := by
  induction N using Finset.induction_on generalizing g c with
  | empty => exact ⟨0, by simp⟩
  | insert i0 N hi0 ih =>
    obtain ⟨Ua, hUa⟩ := hs (fun i => if i = i0 then (1, 0) else (0, 0))
    obtain ⟨Ub, hUb⟩ := hs (fun i => if i = i0 then (0, 1) else (0, 0))
    have hsN : ∀ z : ι → K × K, ∃ v, ∀ i ∈ N, α i v = (z i).1 ∧ β i v = (z i).2 := fun z => by
      obtain ⟨v, hv⟩ := hs z; exact ⟨v, fun i hi => hv i (Finset.mem_insert_of_mem hi)⟩
    have a1 := hUa i0 (Finset.mem_insert_self _ _)
    have b1 := hUb i0 (Finset.mem_insert_self _ _)
    simp only [ite_true] at a1 b1
    let a0 := α i0
    let b0 := β i0
    let δ := g i0
    let s : K := 1 - p i0 - δ Ub
    let Rl : V →ₗ[K] K := δ - (δ Ua) • a0 - (δ Ub) • b0
    let Rc : K := (s + p i0) * q i0 + s * δ Ua + c i0
    let g' : ι → V →ₗ[K] K := fun i => g i - (g i Ua) • a0 - (g i Ub) • (Rl + b0)
    let c' : ι → K := fun i => c i + s * g i Ua + (1 - Rc) * g i Ub
    obtain ⟨v', hv'⟩ := ih hsN g' c'
    let t : K := 1 - (Rl v' + Rc)
    refine ⟨v' + (s - a0 v') • Ua + (t - b0 v') • Ub, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [map_add, map_smul, smul_eq_mul]
      simp only [a0, b0, a1.1, a1.2, b1.1, b1.2]
      simp only [t, Rl, Rc, s, δ, a0, b0, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
      have a2 := hUa i (Finset.mem_insert_of_mem hi)
      have b2 := hUb i (Finset.mem_insert_of_mem hi)
      simp only [hne, ite_false] at a2 b2
      have h := hv' i hi
      simp only [map_add, map_smul, smul_eq_mul, a2.1, a2.2, b2.1, b2.2]
      simp only [g', c', t, Rl, Rc, s, δ, a0, b0, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, smul_eq_mul] at h ⊢
      linear_combination h

def annSub {U ι : Type*} [AddCommGroup U] [Module F U] [Fintype ι]
    (T : U →ₗ[F] (ι → F)) : Submodule F (ι → F) :=
  { carrier := {c | ∀ u : U, ∑ j : ι, c j * T u j = 0}
    zero_mem' := fun _ => by simp
    , add_mem' := fun {c1 c2} hc1 hc2 u => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hc1 u, hc2 u, add_zero]
    , smul_mem' := fun a c hc u => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc u, mul_zero] }

lemma finrank_range_add_finrank_ann {U ι : Type*} [AddCommGroup U] [Module F U]
    [Fintype ι] [DecidableEq ι] (T : U →ₗ[F] (ι → F)) :
    Module.finrank F (LinearMap.range T) + Module.finrank F (annSub T) = Fintype.card ι := by
  let R := LinearMap.range T
  let r := Module.finrank F R
  let b : Module.Basis (Fin r) F R := Module.finBasis F R
  let dotB : (ι → F) →ₗ[F] (Fin r → F) :=
    { toFun := fun c i => ∑ j : ι, c j * (b i).val j
      map_add' := fun c1 c2 => by
        funext i; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext i; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply] }
  have hker : LinearMap.ker dotB = annSub T := by
    ext c
    simp only [LinearMap.mem_ker, annSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro hc u
      have hmem : T u ∈ R := LinearMap.mem_range_self T u
      let y : R := ⟨T u, hmem⟩
      have hy : y = ∑ i : Fin r, b.repr y i • b i := (b.sum_repr y).symm
      have hcoord : ∀ j : ι, T u j = ∑ i : Fin r, b.repr y i * (b i).val j := fun j => by
        have h1 : R.subtype y = R.subtype (∑ i : Fin r, b.repr y i • b i) := by rw [← hy]
        rw [map_sum] at h1
        have h2 := congrFun h1 j
        simpa only [Submodule.subtype_apply, Finset.sum_apply, map_smul, Pi.smul_apply,
          smul_eq_mul] using h2
      simp_rw [hcoord, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro i _
      have hi : ∑ j : ι, c j * (b i).val j = 0 := congrFun hc i
      calc ∑ j : ι, c j * (b.repr y i * (b i).val j)
          = b.repr y i * ∑ j : ι, c j * (b i).val j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
        _ = 0 := by rw [hi, mul_zero]
    · intro hc
      funext i
      obtain ⟨u, hu⟩ := (b i).prop
      simpa [dotB, hu] using hc u
  have hsurj : Function.Surjective dotB := by
    intro z
    let φ : R →ₗ[F] F := b.constr F z
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
    let c : ι → F := fun j => ψ (Pi.single j 1)
    refine ⟨c, ?_⟩
    funext i
    have hpi : ∀ v : ι → F, ψ v = ∑ j : ι, c j * v j := fun v => by
      have hv : v = ∑ j : ι, v j • Pi.single j (1 : F) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, mul_comm]
    change ∑ j : ι, c j * (b i).val j = z i
    rw [← hpi (b i).val]
    have hcomp := LinearMap.congr_fun hψ (b i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hcomp
    rw [hcomp]
    exact b.constr_basis F z i
  have hrange : LinearMap.range dotB = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker dotB
  rw [hrange, hker, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_fin] at hrn
  exact hrn

lemma exists_surj_coord_subset {U ι : Type*} [AddCommGroup U] [Module F U]
    [Fintype ι] [DecidableEq ι] (T : U →ₗ[F] (ι → F)) :
    ∃ J : Finset ι,
      J.card = Module.finrank F (LinearMap.range T) ∧
      Function.Surjective (fun u : U => fun j : J => T u j.val) := by
  classical
  let f : ι → (U →ₗ[F] F) := fun j =>
    { toFun := fun u => T u j
      map_add' := fun u v => by simp
      map_smul' := fun a u => by simp }
  let trans : (ι → F) →ₗ[F] (U →ₗ[F] F) :=
    { toFun := fun c => ∑ j : ι, c j • f j
      map_add' := fun c1 c2 => by
        ext u; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        ext u; simp [mul_assoc, ← Finset.mul_sum] }
  have hker_tr : LinearMap.ker trans = annSub T := by
    ext c
    simp only [LinearMap.mem_ker, annSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, LinearMap.ext_iff, LinearMap.zero_apply]
    constructor
    · intro h u; simpa [trans, f, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h u
    · intro h u; simpa [trans, f, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h u
  have hrange_tr : LinearMap.range trans = Submodule.span F (Set.range f) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      refine Submodule.sum_mem _ (fun j _ => ?_)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, ?_⟩
      ext u
      simp [trans, Pi.single_apply]
  have hfin_span : Module.finrank F (Submodule.span F (Set.range f)) =
      Module.finrank F (LinearMap.range T) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker trans
    rw [hrange_tr, hker_tr, Module.finrank_pi] at h1
    have h2 := finrank_range_add_finrank_ann T
    omega
  obtain ⟨b, hb_sub, hb_span, hb_li⟩ := exists_linearIndependent F (Set.range f)
  let pick : b → ι := fun x => Classical.choose (hb_sub x.prop)
  have hpick_spec : ∀ x : b, f (pick x) = x.val := fun x => Classical.choose_spec (hb_sub x.prop)
  have hpick_inj : Function.Injective pick := fun x y h => by
    apply Subtype.ext
    rw [← hpick_spec x, ← hpick_spec y, h]
  let J : Finset ι := (Set.toFinite (Set.range pick)).toFinset
  have hmemJ : ∀ j : ι, j ∈ J ↔ ∃ x : b, pick x = j := fun j => by
    simp [J]
  let he : b ≃ J := Equiv.ofBijective (fun x => ⟨pick x, (hmemJ _).mpr ⟨x, rfl⟩⟩)
    ⟨fun x y h => hpick_inj (congrArg Subtype.val h),
     fun j => by obtain ⟨x, hx⟩ := (hmemJ j.val).mp j.prop; exact ⟨x, Subtype.ext hx⟩⟩
  have hf_eq : ∀ x : b, f (he x).val = x.val := fun x => by
    simp only [he, Equiv.ofBijective_apply]
    exact hpick_spec x
  have hJ_li : LinearIndependent F (fun j : J => f j.val) := by
    have hcomp : (fun j : J => f j.val) = (Subtype.val : b → (U →ₗ[F] F)) ∘ he.symm := by
      funext j
      have h1 := hf_eq (he.symm j)
      simpa using h1
    rw [hcomp]
    exact hb_li.comp he.symm he.symm.injective
  have hJ_range : Set.range (fun j : J => f j.val) = b := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      have h1 := hf_eq (he.symm j)
      rw [he.apply_symm_apply] at h1
      dsimp only
      rw [h1]
      exact (he.symm j).prop
    · intro hv
      refine ⟨he ⟨v, hv⟩, ?_⟩
      exact hf_eq ⟨v, hv⟩
  have hJ_card : J.card = Module.finrank F (LinearMap.range T) := by
    rw [← hfin_span, ← hb_span, ← hJ_range]
    let B : Module.Basis J F (Submodule.span F (Set.range (fun j : J => f j.val))) :=
      Module.Basis.span hJ_li
    have hc := Module.finrank_eq_card_basis B
    simpa [Fintype.card_coe] using hc.symm
  let TJ : U →ₗ[F] (J → F) :=
    { toFun := fun u j => T u j.val
      map_add' := fun u v => by funext j; simp
      map_smul' := fun a u => by funext j; simp }
  have hann_bot : annSub TJ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro c hc
    have hlin : ∑ j : J, c j • f j.val = 0 := by
      ext u
      simpa [f, TJ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hc u
    funext j
    exact Fintype.linearIndependent_iff.mp hJ_li c hlin j
  have hrank_TJ : Module.finrank F (LinearMap.range TJ) = Module.finrank F (J → F) := by
    have h := finrank_range_add_finrank_ann TJ
    rw [hann_bot, finrank_bot, add_zero] at h
    rw [Module.finrank_pi]
    exact h
  have htop : LinearMap.range TJ = ⊤ := Submodule.eq_top_of_finrank_eq hrank_TJ
  exact ⟨J, hJ_card, LinearMap.range_eq_top.mp htop⟩

lemma survive_pairs {k : Nat} (hk : 0 < k) (M : Finset (Fin k))
    (hind : ∀ u ∈ M, Cut.a_nx k hk u ∉ M) (J : Finset (Fin k))
    (hJsub : J ⊆ M ∪ M.image (Cut.a_nx k hk)) :
    let M' := M.filter (fun u => u ∈ J ∧ Cut.a_nx k hk u ∈ J)
    M.card - ((M ∪ M.image (Cut.a_nx k hk)).card - J.card) ≤ M'.card := by
  classical
  intro M'
  let P := M ∪ M.image (Cut.a_nx k hk)
  let D := P \ J
  have hDcard : D.card = P.card - J.card := Finset.card_sdiff_of_subset hJsub
  let lost := M \ M'
  have hdisj : Disjoint M (M.image (Cut.a_nx k hk)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu2
    exact hind v hv hu1
  have hlost_le : lost.card ≤ D.card := by
    let hit : Fin k → Fin k := fun u => if u ∉ J then u else Cut.a_nx k hk u
    refine Finset.card_le_card_of_injOn hit (s := lost) (t := D) ?_ ?_
    · intro u hu
      have huM : u ∈ M := (Finset.mem_sdiff.mp hu).1
      have huN : ¬ (u ∈ J ∧ Cut.a_nx k hk u ∈ J) := by
        intro h; exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_filter.mpr ⟨huM, h⟩)
      dsimp only [hit]
      by_cases h1 : u ∉ J
      · rw [ite_eq_left h1]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ huM, h1⟩
      · rw [ite_eq_right h1]
        have h2 : Cut.a_nx k hk u ∉ J := fun hc => huN ⟨by push Not at h1; exact h1, hc⟩
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ huM), h2⟩
    · intro u hu v hv heq
      have huM : u ∈ M := (Finset.mem_sdiff.mp hu).1
      have hvM : v ∈ M := (Finset.mem_sdiff.mp hv).1
      dsimp only [hit] at heq
      by_cases h1 : u ∉ J <;> by_cases h2 : v ∉ J
      · rw [ite_eq_left h1, ite_eq_left h2] at heq; exact heq
      · rw [ite_eq_left h1, ite_eq_right h2] at heq
        exact False.elim (hind v hvM (heq ▸ huM))
      · rw [ite_eq_right h1, ite_eq_left h2] at heq
        exact False.elim (hind u huM (heq.symm ▸ hvM))
      · rw [ite_eq_right h1, ite_eq_right h2] at heq
        exact Cut.a_nx_inj k hk heq
  have hM'_sub : M' ⊆ M := Finset.filter_subset _ _
  have hsum : M'.card + lost.card = M.card := by
    have hs1 : lost.card = M.card - M'.card := Finset.card_sdiff_of_subset hM'_sub
    have hs2 : M'.card ≤ M.card := Finset.card_le_card hM'_sub
    omega
  change M.card - (P.card - J.card) ≤ M'.card
  omega

lemma lower_bound {k : Nat} (hk : 0 < k) (spacing s t : Nat) (name constant : W k)
    (sites : Finset (Fin k)) (e L D : Nat)
    (M0 : Finset (Fin k))
    (hM0_sub : M0 ⊆ sites.image (Cut.a_nx k hk))
    (hM0_ind : ∀ u ∈ M0, Cut.a_nx k hk u ∉ M0)
    (hchecks : ((Finset.univ : Finset (W k)).filter (fun w =>
      (∀ j, j ∉ M0 ∪ M0.image (Cut.a_nx k hk) → w j = 0) ∧ ∀ j : Fin k,
        w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0)).card = 2 ^ D)
    (tree : Tree k) (hcard : tree.1.card < L)
    (herr : ∀ x : W k, (sites.filter (fun i =>
      Upper.predict tree x i ≠ output hk spacing s t name constant x i)).card ≤ e) :
    2 ^ (M0.card - e - D) ≤ L := by
  classical
  let P0 := M0 ∪ M0.image (Cut.a_nx k hk)
  let Y := ylin hk spacing s
  let T0 : W k →ₗ[F] (P0 → F) :=
    { toFun := fun x j => Y x j.val
      map_add' := fun x1 x2 => by funext j; simp
      map_smul' := fun a x => by funext j; simp }
  let KerP0 := {w : W k // (∀ j, j ∉ P0 → w j = 0) ∧ ∀ j : Fin k,
    w j + w (ix hk (j.val + spacing)) + w (ix hk (j.val + k - spacing % k)) = 0}
  have hann_equiv : annSub T0 ≃ KerP0 :=
    { toFun := fun c => ⟨fun j => if h : j ∈ P0 then c.val ⟨j, h⟩ else 0, by
        refine ⟨fun j hj => by dsimp only; rw [dite_eq_right hj], ?_⟩
        let w : W k := fun j => if h : j ∈ P0 then c.val ⟨j, h⟩ else 0
        have hdot : ∀ x : W k, ∑ j : Fin k, mixLin hk spacing w j * x j = 0 := fun x => by
          obtain ⟨raw, hraw⟩ := rotLin_surjective hk s x
          have hc := c.prop raw
          have hsum_eq : ∑ j : P0, c.val j * T0 raw j = ∑ j : Fin k, w j * mixLin hk spacing x j := by
            have h1 : ∑ j : Fin k, w j * mixLin hk spacing x j =
                ∑ j ∈ P0, w j * mixLin hk spacing x j := by
              symm
              refine Finset.sum_subset (Finset.subset_univ P0) (fun j _ hj => ?_)
              simp [w, hj]
            rw [h1, ← Finset.sum_coe_sort P0]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [w, dite_eq_left j.prop, T0, LinearMap.coe_mk, AddHom.coe_mk, Y, ylin,
              LinearMap.comp_apply, hraw]
          rw [← mix_self_adjoint hk spacing w x, ← hsum_eq]
          exact hc
        intro j
        have h := hdot (Pi.single j 1)
        have h2 : mixLin hk spacing w j = 0 := by simpa [Pi.single_apply] using h
        exact h2⟩
      invFun := fun w => ⟨fun j => w.val j.val, by
        intro raw
        have h1 : ∑ j : P0, w.val j.val * T0 raw j = ∑ j : Fin k, w.val j * mixLin hk spacing (rotLin hk s raw) j := by
          change ∑ j : P0, w.val j.val * Y raw j.val = _
          rw [Finset.sum_coe_sort P0 (fun j => w.val j * Y raw j)]
          refine Finset.sum_subset (Finset.subset_univ P0) (fun j _ hj => ?_)
          rw [w.prop.1 j hj, zero_mul]
        rw [h1, mix_self_adjoint hk spacing w.val (rotLin hk s raw)]
        apply Finset.sum_eq_zero
        intro j _
        have hm : mixLin hk spacing w.val j = 0 := w.prop.2 j
        rw [hm, zero_mul]⟩
      left_inv := fun c => by
        apply Subtype.ext; funext j; simp [dite_eq_left j.prop]
      right_inv := fun w => by
        apply Subtype.ext; funext j
        by_cases hj : j ∈ P0
        · simp [dite_eq_left hj]
        · simp [dite_eq_right hj, w.prop.1 j hj] }
  have hker_card : Fintype.card (annSub T0) = 2 ^ D := by
    rw [Fintype.card_congr hann_equiv, Fintype.card_subtype]
    exact hchecks
  have hfin_ann : Module.finrank F (annSub T0) = D := by
    have hc := Module.card_eq_pow_finrank (K := F) (V := annSub T0)
    rw [ZMod.card 2, hker_card] at hc
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hc).symm
  have hfin_range0 : Module.finrank F (LinearMap.range T0) + D = P0.card := by
    have h := finrank_range_add_finrank_ann T0
    rw [hfin_ann, Fintype.card_coe] at h
    exact h
  obtain ⟨J0_coe, hJ0_card, hJ0_surj⟩ := exists_surj_coord_subset T0
  let J0 : Finset (Fin k) := J0_coe.image Subtype.val
  have hJ0_sub : J0 ⊆ P0 := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact j.prop
  have hJ0_card_eq : J0.card = P0.card - D := by
    have hinj : J0.card = J0_coe.card := Finset.card_image_of_injective J0_coe Subtype.val_injective
    omega
  let M' := M0.filter (fun u => u ∈ J0 ∧ Cut.a_nx k hk u ∈ J0)
  have hM'_card : M0.card - D ≤ M'.card := by
    have hs : M0.card - (P0.card - J0.card) ≤ M'.card := survive_pairs hk M0 hM0_ind J0 hJ0_sub
    have hDle : P0.card - J0.card ≤ D := by omega
    omega
  have hM'_sub : M' ⊆ M0 := Finset.filter_subset _ _
  have hM'_ind : ∀ u ∈ M', Cut.a_nx k hk u ∉ M' :=
    fun u hu hnu => hM0_ind u (hM'_sub hu) (hM'_sub hnu)
  let P' := M' ∪ M'.image (Cut.a_nx k hk)
  have hP'_sub_J0 : P' ⊆ J0 := by
    intro u hu
    rcases Finset.mem_union.mp hu with h1 | h2
    · exact (Finset.mem_filter.mp h1).2.1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h2
      exact (Finset.mem_filter.mp hv).2.2
  have hP'_surj : Function.Surjective (fun x : W k => fun j : P' => Y x j.val) := by
    intro z
    let z0 : J0_coe → F := fun j =>
      if h : j.val.val ∈ P' then z ⟨j.val.val, h⟩ else 0
    obtain ⟨x, hx⟩ := hJ0_surj z0
    refine ⟨x, ?_⟩
    funext j
    have hjJ0 : j.val ∈ J0 := hP'_sub_J0 j.prop
    obtain ⟨jc, hjc_mem, hjc_eq⟩ := Finset.mem_image.mp hjJ0
    have hval := congrFun hx ⟨jc, hjc_mem⟩
    change Y x jc.val = z0 ⟨jc, hjc_mem⟩ at hval
    dsimp only [z0] at hval
    rw [hjc_eq, dite_eq_left j.prop] at hval
    exact hval
  let Ψ : W k →ₗ[F] (P' → F) :=
    { toFun := fun x j => Y x j.val
      map_add' := fun x1 x2 => by funext j; simp
      map_smul' := fun a x => by funext j; simp }
  have hΨ_range : LinearMap.range Ψ = ⊤ := LinearMap.range_eq_top.mpr hP'_surj
  have hΨ_rank : Module.finrank F (LinearMap.range Ψ) = P'.card := by
    rw [hΨ_range, finrank_top, Module.finrank_pi, Fintype.card_coe]
  -- Count reachable leaves
  have hleaf_list := TreeAux.exact_leaf_list tree.1.toList tree.1.card
  obtain ⟨ls, hls_len, hls_mem⟩ := hleaf_list
  have hhist_eq : ∀ x : W k, Upper.hist tree x =
      (List.range tree.1.card).foldl (fun p _ =>
        if p ∈ tree.1.toList then p ++ [decide (tree.2.1 p x + tree.2.2.1 p ≠ 0)] else p) [] := by
    intro x
    unfold Upper.hist
    congr 1; funext p _
    simp only [Finset.mem_toList]
  let Λ : Finset H := Finset.univ.image (Upper.hist tree)
  have hΛ_card : Λ.card ≤ L := by
    have hsub : Λ ⊆ ls.toFinset := by
      intro ℓ hℓ
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hℓ
      rw [List.mem_toFinset, hhist_eq x]
      exact hls_mem (fun p => decide (tree.2.1 p x + tree.2.2.1 p ≠ 0))
    have h1 := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le ls
    have h3 : tree.1.toList.length = tree.1.card := Finset.length_toList _
    omega
  -- Per-leaf cardinality bound
  have hleaf_bound : ∀ ℓ ∈ Λ,
      2 ^ (M'.card - e) * ((Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x = ℓ)).card ≤
        2 ^ k := by
    intro ℓ hℓ
    obtain ⟨x0, _, rfl⟩ := Finset.mem_image.mp hℓ
    let Q0 : H → Bool := fun p => decide (tree.2.1 p x0 + tree.2.2.1 p ≠ 0)
    obtain ⟨qs, hqs⟩ := TreeAux.reachable_leaf_cell tree.1.toList Q0 tree.1.card []
    have hcell : ∀ x : W k, Upper.hist tree x = Upper.hist tree x0 ↔
        ∀ z ∈ qs, decide (tree.2.1 z.1 x + tree.2.2.1 z.1 ≠ 0) = z.2 := by
      intro x
      have hx1 : Upper.hist tree x =
          TreeAux.follow tree.1.toList (fun p => decide (tree.2.1 p x + tree.2.2.1 p ≠ 0)) tree.1.card [] := by
        rw [hhist_eq x]
        have hf := TreeAux.fold_follow tree.1.toList
          (fun p => decide (tree.2.1 p x + tree.2.2.1 p ≠ 0)) (List.range tree.1.card) []
        rw [List.length_range] at hf
        exact hf
      have hx0 : Upper.hist tree x0 = TreeAux.follow tree.1.toList Q0 tree.1.card [] := by
        rw [hhist_eq x0]
        have hf := TreeAux.fold_follow tree.1.toList Q0 (List.range tree.1.card) []
        rw [List.length_range] at hf
        exact hf
      rw [hx1, hx0]
      exact hqs (fun p => decide (tree.2.1 p x + tree.2.2.1 p ≠ 0))
    have hqs0 : ∀ z ∈ qs, Q0 z.1 = z.2 := (hcell x0).mp rfl
    let V : Submodule F (W k) :=
      { carrier := {v | ∀ z ∈ qs, tree.2.1 z.1 v = 0}
        zero_mem' := fun _ _ => by simp
        , add_mem' := fun hv1 hv2 z hz => by rw [map_add, hv1 z hz, hv2 z hz, add_zero]
        , smul_mem' := fun a v hv z hz => by rw [map_smul, hv z hz, smul_zero] }
    have hcell_V : ∀ x : W k, Upper.hist tree x = Upper.hist tree x0 ↔ x - x0 ∈ V := by
      intro x
      rw [hcell x]
      constructor
      · intro hx z hz
        have h1 : decide (tree.2.1 z.1 x + tree.2.2.1 z.1 ≠ 0) =
            decide (tree.2.1 z.1 x0 + tree.2.2.1 z.1 ≠ 0) := by
          rw [hx z hz, ← hqs0 z hz]
        have h2 := f2_decide_ne_zero_eq.mp h1
        have h3 : tree.2.1 z.1 (x - x0) = tree.2.1 z.1 x - tree.2.1 z.1 x0 := map_sub _ _ _
        rw [h3, f2_sub_eq_add]
        have h4 : tree.2.1 z.1 x = tree.2.1 z.1 x0 := by
          have hb := f2_add_self (tree.2.2.1 z.1)
          linear_combination h2
        rw [h4, f2_add_self]
      · intro hv z hz
        rw [← hqs0 z hz]
        apply f2_decide_ne_zero_eq.mpr
        have h0 : tree.2.1 z.1 (x - x0) = 0 := hv z hz
        rw [map_sub, f2_sub_eq_add] at h0
        rw [f2_add_eq_zero.mp h0]
    have hcell_card : ((Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x = Upper.hist tree x0)).card =
        2 ^ Module.finrank F V := by
      have hbij : ((Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x = Upper.hist tree x0)).card =
          Fintype.card V := by
        rw [Fintype.card_subtype]
        refine Finset.card_bij (fun x _ => x - x0) ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcell_V x).mp (Finset.mem_filter.mp hx).2⟩
        · intro x1 _ x2 _ h
          exact sub_left_inj.mp h
        · intro v hv
          refine ⟨x0 + v, ?_, by simp⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcell_V (x0 + v)).mpr ?_⟩
          simpa using (Finset.mem_filter.mp hv).2
      rw [hbij, Module.card_eq_pow_finrank (K := F) (V := V), ZMod.card 2]
    have hV_le : Module.finrank F V ≤ k := by
      have h1 := Submodule.finrank_le V
      rw [Module.finrank_pi, Fintype.card_fin] at h1
      exact h1
    let dV := k - Module.finrank F V
    -- Restrict Ψ to V
    let ΨV : V →ₗ[F] (P' → F) := Ψ.comp V.subtype
    have hker_le : Module.finrank F (LinearMap.ker ΨV) ≤ Module.finrank F (LinearMap.ker Ψ) := by
      let mapK : LinearMap.ker ΨV →ₗ[F] LinearMap.ker Ψ :=
        { toFun := fun v => ⟨v.val.val, v.prop⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hinj : Function.Injective mapK := fun v1 v2 h => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun x : LinearMap.ker Ψ => x.val) h
      exact LinearMap.finrank_le_finrank_of_injective hinj
    have hΨV_rank : P'.card - dV ≤ Module.finrank F (LinearMap.range ΨV) := by
      have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
      have h2 := LinearMap.finrank_range_add_finrank_ker ΨV
      rw [hΨ_rank, Module.finrank_pi, Fintype.card_fin] at h1
      omega
    obtain ⟨J'_coe, hJ'_card, hJ'_surj⟩ := exists_surj_coord_subset ΨV
    let J' : Finset (Fin k) := J'_coe.image Subtype.val
    have hJ'_sub : J' ⊆ P' := by
      intro u hu; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu; exact j.prop
    have hJ'_card_eq : P'.card - dV ≤ J'.card := by
      have hinj : J'.card = J'_coe.card := Finset.card_image_of_injective J'_coe Subtype.val_injective
      omega
    let M'' := M'.filter (fun u => u ∈ J' ∧ Cut.a_nx k hk u ∈ J')
    have hM''_card : M'.card - dV ≤ M''.card := by
      have hs : M'.card - (P'.card - J'.card) ≤ M''.card := survive_pairs hk M' hM'_ind J' hJ'_sub
      have hdl : P'.card - J'.card ≤ dV := by omega
      omega
    have hM''_sub : M'' ⊆ M' := Finset.filter_subset _ _
    have hM''_ind : ∀ u ∈ M'', Cut.a_nx k hk u ∉ M'' :=
      fun u hu hnu => hM'_ind u (hM''_sub hu) (hM''_sub hnu)
    let S'' : Finset (Fin k) := M''.image (Cut.a_pv k hk)
    have hS''_sub : S'' ⊆ sites := by
      intro i hi
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      have huE : u ∈ sites.image (Cut.a_nx k hk) := hM0_sub (hM'_sub (hM''_sub hu))
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp huE
      rwa [Cut.a_pv_nx]
    have hS''_card : S''.card = M''.card :=
      Finset.card_image_of_injective M'' (Cut.a_pv_inj k hk)
    -- Apply allwrong on V with S''
    let α : Fin k → V →ₗ[F] F := fun i =>
      { toFun := fun v => Y v.val (Cut.a_nx k hk i)
        map_add' := fun _ _ => by simp
        map_smul' := fun _ _ => by simp }
    let β : Fin k → V →ₗ[F] F := fun i =>
      { toFun := fun v => Y v.val (Cut.a_nx k hk (Cut.a_nx k hk i))
        map_add' := fun _ _ => by simp
        map_smul' := fun _ _ => by simp }
    have hsurj_S'' : ∀ z : Fin k → F × F, ∃ v : V, ∀ i ∈ S'', α i v = (z i).1 ∧ β i v = (z i).2 := by
      intro z
      let tgt : J'_coe → F := fun j =>
        if j.val.val ∈ M'' then (z (Cut.a_pv k hk j.val.val)).1
        else if Cut.a_pv k hk j.val.val ∈ M'' then (z (Cut.a_pv k hk (Cut.a_pv k hk j.val.val))).2
        else 0
      obtain ⟨v, hv⟩ := hJ'_surj tgt
      refine ⟨v, fun i hi => ?_⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      have hu1 : Cut.a_nx k hk (Cut.a_pv k hk u) = u := Cut.a_nx_pv k hk u
      have huJ1 : u ∈ J' := (Finset.mem_filter.mp hu).2.1
      have huJ2 : Cut.a_nx k hk u ∈ J' := (Finset.mem_filter.mp hu).2.2
      obtain ⟨jc1, hjc1_mem, hjc1_eq⟩ := Finset.mem_image.mp huJ1
      obtain ⟨jc2, hjc2_mem, hjc2_eq⟩ := Finset.mem_image.mp huJ2
      constructor
      · change Y v.val (Cut.a_nx k hk (Cut.a_pv k hk u)) = (z (Cut.a_pv k hk u)).1
        rw [hu1, ← hjc1_eq]
        have h1 := congrFun hv ⟨jc1, hjc1_mem⟩
        change Y v.val jc1.val = tgt ⟨jc1, hjc1_mem⟩ at h1
        rw [h1]
        dsimp only [tgt]
        rw [hjc1_eq, ite_eq_left hu]
      · change Y v.val (Cut.a_nx k hk (Cut.a_nx k hk (Cut.a_pv k hk u))) = (z (Cut.a_pv k hk u)).2
        rw [hu1, ← hjc2_eq]
        have h2 := congrFun hv ⟨jc2, hjc2_mem⟩
        change Y v.val jc2.val = tgt ⟨jc2, hjc2_mem⟩ at h2
        rw [h2]
        dsimp only [tgt]
        rw [hjc2_eq, ite_eq_right (hM''_ind u hu), Cut.a_pv_nx, ite_eq_left hu]
    let ℓ0 := Upper.hist tree x0
    let y0 := yaff hk spacing s name x0
    let p : Fin k → F := fun i => 1 + y0 (Cut.a_nx k hk i)
    let q : Fin k → F := fun i => y0 (Cut.a_nx k hk (Cut.a_nx k hk i))
    let g : Fin k → V →ₗ[F] F := fun i =>
      { toFun := fun v => tree.2.2.2.1 ℓ0 v.val i + Y v.val i + rotLin hk t v.val i
        map_add' := fun _ _ => by simp; ring
        map_smul' := fun _ _ => by simp; ring }
    let c : Fin k → F := fun i =>
      tree.2.2.2.1 ℓ0 x0 i + tree.2.2.2.2 ℓ0 i + y0 i + rotLin hk t x0 i + constant i
    obtain ⟨v, hv⟩ := allwrong α β p q S'' hsurj_S'' g c
    have hhist_v : Upper.hist tree (x0 + v.val) = ℓ0 := (hcell_V (x0 + v.val)).mpr (by simpa using v.prop)
    have herr_all : ∀ i ∈ S'', Upper.predict tree (x0 + v.val) i ≠
        output hk spacing s t name constant (x0 + v.val) i := by
      intro i hi heq
      have hsum0 : Upper.predict tree (x0 + v.val) i +
          output hk spacing s t name constant (x0 + v.val) i = 0 := by
        rw [heq, f2_add_self]
      have hpred : Upper.predict tree (x0 + v.val) i =
          tree.2.2.2.1 ℓ0 v.val i + tree.2.2.2.1 ℓ0 x0 i + tree.2.2.2.2 ℓ0 i := by
        unfold Upper.predict
        rw [hhist_v]
        change (tree.2.2.2.1 ℓ0 (x0 + v.val) + tree.2.2.2.2 ℓ0) i = _
        rw [map_add]
        simp only [Pi.add_apply]
        ring
      have hout : output hk spacing s t name constant (x0 + v.val) i =
          (Y v.val i + y0 i) +
          (1 + Y v.val (Cut.a_nx k hk i) + y0 (Cut.a_nx k hk i)) *
            (Y v.val (Cut.a_nx k hk (Cut.a_nx k hk i)) + y0 (Cut.a_nx k hk (Cut.a_nx k hk i))) +
          rotLin hk t v.val i + rotLin hk t x0 i + constant i := by
        have hy_add : ∀ u : Fin k, yaff hk spacing s name (x0 + v.val) u = Y v.val u + y0 u := fun u => by
          dsimp only [y0, Y, yaff]
          rw [map_add]
          simp only [Pi.add_apply]
          ring
        have hbase_add : baseLin hk spacing s t (x0 + v.val) i =
            Y x0 i + Y v.val i + rotLin hk t x0 i + rotLin hk t v.val i := by
          dsimp only [baseLin, Y]
          rw [LinearMap.add_apply, Pi.add_apply, map_add, map_add]
          simp only [Pi.add_apply]
          ring
        unfold output rise biasVec
        rw [hbase_add, hy_add, hy_add]
        have hy0_i : y0 i = Y x0 i + mixLin hk spacing name i := rfl
        rw [hy0_i]
        simp only [Pi.add_apply]
        ring
      have h1 := hv i hi
      change (Y v.val (Cut.a_nx k hk i) + (1 + y0 (Cut.a_nx k hk i))) *
          (Y v.val (Cut.a_nx k hk (Cut.a_nx k hk i)) + y0 (Cut.a_nx k hk (Cut.a_nx k hk i))) +
          (tree.2.2.2.1 ℓ0 v.val i + Y v.val i + rotLin hk t v.val i) +
          (tree.2.2.2.1 ℓ0 x0 i + tree.2.2.2.2 ℓ0 i + y0 i + rotLin hk t x0 i + constant i) = 1 at h1
      rw [hpred, hout] at hsum0
      have h01 : (0 : F) = 1 := by linear_combination h1 - hsum0
      exact (by decide : (0 : F) ≠ 1) h01
    have hS''_le_e : S''.card ≤ e := by
      have hsub : S'' ⊆ sites.filter (fun i =>
          Upper.predict tree (x0 + v.val) i ≠ output hk spacing s t name constant (x0 + v.val) i) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨hS''_sub hi, herr_all i hi⟩
      exact (Finset.card_le_card hsub).trans (herr (x0 + v.val))
    have hpow_le : 2 ^ (M'.card - e) ≤ 2 ^ dV :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    rw [hcell_card]
    calc 2 ^ (M'.card - e) * 2 ^ Module.finrank F V
        ≤ 2 ^ dV * 2 ^ Module.finrank F V := Nat.mul_le_mul_right _ hpow_le
      _ = 2 ^ (dV + Module.finrank F V) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ k := by congr 1; omega
  -- Sum over all leaves
  have hsum_all : ∑ ℓ ∈ Λ, ((Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x = ℓ)).card =
      2 ^ k := by
    have h1 := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (W k)) Λ (Upper.hist tree)
    have hfilt : (Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x ∈ Λ) = Finset.univ := by
      ext x; simp [Λ]
    rw [hfilt, Finset.card_univ, Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at h1
    exact h1
  have hmul : 2 ^ (M'.card - e) * 2 ^ k ≤ L * 2 ^ k := by
    calc 2 ^ (M'.card - e) * 2 ^ k
        = 2 ^ (M'.card - e) * ∑ ℓ ∈ Λ,
            ((Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x = ℓ)).card := by
          rw [hsum_all]
      _ = ∑ ℓ ∈ Λ, 2 ^ (M'.card - e) *
            ((Finset.univ : Finset (W k)).filter (fun x => Upper.hist tree x = ℓ)).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _ℓ ∈ Λ, 2 ^ k := Finset.sum_le_sum hleaf_bound
      _ = Λ.card * 2 ^ k := by simp
      _ ≤ L * 2 ^ k := Nat.mul_le_mul_right _ hΛ_card
  have hle_M' : 2 ^ (M'.card - e) ≤ L := Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos k)
  exact le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)) hle_M'

end Lower

/-! ### Section 5: Triple-Path Corollary (Conjunct 5) -/

namespace TriplePath

lemma triple_mu_and_score {k : Nat} (hk : 0 < k) (h6 : 6 ≤ k) (h3 : 3 ∣ k)
    (spacing : Nat) (hsp : Nat.Coprime k spacing ∨ (spacing = 2 ∧ 12 ≤ k)) :
    let g := Nat.gcd k spacing
    let E := (Finset.univ : Finset (Fin k)).filter (fun i => i.val % 3 ≠ 2)
    let lane := fun i : Fin k => i.val % g
    let phase := fun i : Fin k => (i.val / g) % 3
    let edges := E.powerset.filter (fun M => ∀ i ∈ M, Cut.a_nx k hk i ∉ M)
    let mu := edges.sup Finset.card
    let best := edges.filter (fun M => M.card = mu)
    let ends := fun M : Finset (Fin k) => M ∪ M.image (Cut.a_nx k hk)
    let score := fun U : Finset (Fin k) =>
      ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
    mu = k / 3 ∧ ∃ M ∈ best, score (Finset.univ \ ends M) = 2 * g := by
  intro g E lane phase edges mu best ends score
  let m := k / 3
  have hm3 : 3 * m = k := Nat.mul_div_cancel' h3
  have hm2 : 2 ≤ m := by omega
  let Mof : (Fin m → Bool) → Finset (Fin k) := fun pick =>
    Finset.univ.image (fun q : Fin m =>
      (⟨3 * q.val + if pick q then 1 else 0, by have := q.isLt; split <;> omega⟩ : Fin k))
  have hMof_card : ∀ pick : Fin m → Bool, (Mof pick).card = m := by
    intro pick
    rw [Finset.card_image_of_injective]
    · simp
    · intro q1 q2 heq
      have hv := congrArg Fin.val heq
      dsimp only at hv
      apply Fin.ext
      cases h1 : pick q1 <;> cases h2 : pick q2 <;> simp [h1, h2] at hv <;> omega
  have hMof_edges : ∀ pick : Fin m → Bool, Mof pick ∈ edges := by
    intro pick
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      cases pick q <;> simp <;> omega
    · intro u hu hnu
      obtain ⟨q1, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨q2, _, hq2⟩ := Finset.mem_image.mp hnu
      have hv := congrArg Fin.val hq2
      change 3 * q2.val + (if pick q2 then 1 else 0) =
        (3 * q1.val + (if pick q1 then 1 else 0) + 1) % k at hv
      have hq1_lt := q1.isLt
      have hq2_lt := q2.isLt
      have hlt : 3 * q1.val + (if pick q1 then 1 else 0) + 1 < k := by
        cases h1 : pick q1 <;> simp [h1] <;> omega
      rw [Nat.mod_eq_of_lt hlt] at hv
      cases h1 : pick q1 <;> cases h2 : pick q2
      · simp [h1, h2] at hv; omega
      · simp [h1, h2] at hv
        have hqq : q1 = q2 := Fin.ext (by omega)
        rw [hqq, h2] at h1; cases h1
      · simp [h1, h2] at hv; omega
      · simp [h1, h2] at hv; omega
  have hmu : mu = m := by
    apply le_antisymm
    · refine Finset.sup_le (fun M hM => ?_)
      obtain ⟨hsub, hind⟩ := Finset.mem_filter.mp hM
      have hsubE := Finset.mem_powerset.mp hsub
      have hinj : Set.InjOn (fun i : Fin k => i.val / 3) (M : Set (Fin k)) := by
        intro i hi j hj hdiv
        dsimp only at hdiv
        have hiE : i.val % 3 ≠ 2 := (Finset.mem_filter.mp (hsubE hi)).2
        have hjE : j.val % 3 ≠ 2 := (Finset.mem_filter.mp (hsubE hj)).2
        have hlt_i := i.isLt
        have hlt_j := j.isLt
        by_cases hmod : i.val % 3 = j.val % 3
        · exact Fin.ext (by omega)
        · by_cases hi0 : i.val % 3 = 0
          · have hj1 : j.val = i.val + 1 := by omega
            have hjeq : j = Cut.a_nx k hk i := Fin.ext (by
              simp only [Cut.a_nx, hj1, Nat.mod_eq_of_lt (by omega : i.val + 1 < k)])
            exact False.elim (hind i hi (hjeq ▸ hj))
          · have hi1 : i.val = j.val + 1 := by omega
            have hieq : i = Cut.a_nx k hk j := Fin.ext (by
              simp only [Cut.a_nx, hi1, Nat.mod_eq_of_lt (by omega : j.val + 1 < k)])
            exact False.elim (hind j hj (hieq ▸ hi))
      have hmaps : ∀ i ∈ M, i.val / 3 ∈ Finset.range m := fun i _ =>
        Finset.mem_range.mpr (by omega)
      simpa using Finset.card_le_card_of_injOn (fun i : Fin k => i.val / 3) hmaps hinj
    · have h1 := Finset.le_sup (f := Finset.card) (hMof_edges (fun _ => false))
      rw [hMof_card] at h1
      exact h1
  have hMof_best : ∀ pick : Fin m → Bool, Mof pick ∈ best := fun pick =>
    Finset.mem_filter.mpr ⟨hMof_edges pick, by rw [hMof_card, hmu]⟩
  have hMof_unc_false : ∀ (pick : Fin m → Bool) (q : Fin m), pick q = false →
      (⟨3 * q.val + 2, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) := by
    intro pick q hq
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp h1
      have hv := congrArg Fin.val hq'
      dsimp only at hv
      cases hp' : pick q' <;> simp [hp'] at hv <;> omega
    · obtain ⟨u, hu, hu2⟩ := Finset.mem_image.mp h2
      obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hu
      have hv := congrArg Fin.val hu2
      simp only [Cut.a_nx] at hv
      have hlt : 3 * q'.val + (if pick q' then 1 else 0) + 1 < k := by
        cases pick q' <;> simp <;> omega
      rw [Nat.mod_eq_of_lt hlt] at hv
      cases hp' : pick q'
      · simp [hp'] at hv; omega
      · simp [hp'] at hv
        have hqq : q' = q := Fin.ext (by omega)
        rw [hqq, hq] at hp'; cases hp'
  have hMof_unc_true : ∀ (pick : Fin m → Bool) (q : Fin m), pick q = true →
      (⟨3 * q.val, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) := by
    intro pick q hq
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp h1
      have hv := congrArg Fin.val hq'
      cases hp' : pick q'
      · simp [hp'] at hv
        have hqq : q' = q := Fin.ext (by omega)
        rw [hqq, hq] at hp'; cases hp'
      · simp [hp'] at hv; omega
    · obtain ⟨u, hu, hu2⟩ := Finset.mem_image.mp h2
      obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hu
      have hv := congrArg Fin.val hu2
      simp only [Cut.a_nx] at hv
      have hlt : 3 * q'.val + (if pick q' then 1 else 0) + 1 < k := by
        cases pick q' <;> simp <;> omega
      rw [Nat.mod_eq_of_lt hlt] at hv
      cases hp' : pick q' <;> simp [hp'] at hv <;> omega
  have htwo_le : ∀ (U : Finset (Fin k)) (j : Nat) (v1 v2 : Fin k),
      v1 ∈ U → v2 ∈ U → lane v1 = j → lane v2 = j → phase v1 ≠ phase v2 →
      min 2 (((U.filter (fun v => lane v = j)).image phase).card) = 2 := by
    intro U j v1 v2 h1 h2 hl1 hl2 hne
    have hm1 : phase v1 ∈ (U.filter (fun v => lane v = j)).image phase :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨h1, hl1⟩)
    have hm2 : phase v2 ∈ (U.filter (fun v => lane v = j)).image phase :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨h2, hl2⟩)
    have hsub : ({phase v1, phase v2} : Finset Nat) ⊆ (U.filter (fun v => lane v = j)).image phase := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hm1
      · rwa [Finset.mem_singleton.mp hx]
    have hc : 2 ≤ ((U.filter (fun v => lane v = j)).image phase).card := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hne] at this
    omega
  refine ⟨hmu, ?_⟩
  have hg1_case : g = 1 → ∃ M ∈ best, score (Finset.univ \ ends M) = 2 * g := by
    intro hg1
    let pick : Fin m → Bool := fun q => decide (q.val = 1)
    refine ⟨Mof pick, hMof_best pick, ?_⟩
    have hv1 : (⟨2, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) :=
      hMof_unc_false pick ⟨0, by omega⟩ (by simp [pick])
    have hv2 : (⟨3, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) :=
      hMof_unc_true pick ⟨1, by omega⟩ (by simp [pick])
    have hsc0 := htwo_le (Finset.univ \ ends (Mof pick)) 0 ⟨2, by omega⟩ ⟨3, by omega⟩
      hv1 hv2 (by simp [lane, hg1]) (by simp [lane, hg1]) (by simp [phase, hg1])
    dsimp only [score]
    rw [hg1, Finset.range_one, Finset.sum_singleton, hsc0]
  rcases hsp with hcop | ⟨rfl, h12⟩
  · exact hg1_case hcop
  · by_cases heven : 2 ∣ k
    · have hg2 : g = 2 := Nat.gcd_eq_right heven
      have hm4 : 4 ≤ m := by omega
      let pick : Fin m → Bool := fun q => decide (q.val = 0 ∨ q.val = 1)
      refine ⟨Mof pick, hMof_best pick, ?_⟩
      have h0 : (⟨0, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) :=
        hMof_unc_true pick ⟨0, by omega⟩ (by simp [pick])
      have h3v : (⟨3, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) :=
        hMof_unc_true pick ⟨1, by omega⟩ (by simp [pick])
      have h8 : (⟨8, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) :=
        hMof_unc_false pick ⟨2, by omega⟩ (by simp [pick])
      have h11 : (⟨11, by omega⟩ : Fin k) ∈ Finset.univ \ ends (Mof pick) :=
        hMof_unc_false pick ⟨3, by omega⟩ (by simp [pick])
      have hsc0 := htwo_le (Finset.univ \ ends (Mof pick)) 0 ⟨0, by omega⟩ ⟨8, by omega⟩
        h0 h8 (by simp [lane, hg2]) (by simp [lane, hg2]) (by simp [phase, hg2])
      have hsc1 := htwo_le (Finset.univ \ ends (Mof pick)) 1 ⟨3, by omega⟩ ⟨11, by omega⟩
        h3v h11 (by simp [lane, hg2]) (by simp [lane, hg2]) (by simp [phase, hg2])
      dsimp only [score]
      rw [hg2, show Finset.range 2 = {0, 1} by decide, Finset.sum_pair (by decide : (0 : Nat) ≠ 1),
          hsc0, hsc1]
    · have hg1 : g = 1 := by
        have hlt : k % 2 = 1 := by omega
        have hd : Nat.gcd k 2 = Nat.gcd 2 (k % 2) := by rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
        change Nat.gcd k 2 = 1
        rw [hd, hlt]; decide
      exact hg1_case hg1

end TriplePath

end PEqualNP.Outside.L_meta_33637_aux

theorem PEqualNP.Outside.L_meta_33637 :
    ∀ (k : Nat) (hk : 0 < k), 2 ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  ∀ (spacing s t : Nat) (name constant : W),
    let out := fun (raw : W) (site : Fin k) =>
      let old := rot s raw + name
      let y := fun u : Fin k =>
        old u + old (ix (u.val+spacing)) + old (ix (u.val+k-spacing % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) + rot t raw site + constant site
    let H := List Bool
    let Tree := Finset H × (H → W →ₗ[F] F) × (H → F) × (H → W →ₗ[F] W) × (H → W)
    let predict : Tree → W → W := fun tree raw =>
      let nodes := tree.1
      let ask := tree.2.1
      let bias := tree.2.2.1
      let aff := tree.2.2.2.1
      let c := tree.2.2.2.2
      let leaf := (List.range nodes.card).foldl (fun (p : H) _ =>
        if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p) []
      aff leaf raw + c leaf
    let g := Nat.gcd k spacing
    ∀ (sites : Finset (Fin k)) (e : Nat), sites ≠ Finset.univ →
      let E := sites.image (fun i => ix (i.val+1))
      let lane := fun i : Fin k => i.val % g
      let phase := fun i : Fin k => (i.val/g) % 3
      let nxt := fun i : Fin k => ix (i.val+1)
      let prv := fun i : Fin k => ix (i.val+k-1)
      let edges := E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)
      let mu := edges.sup Finset.card
      let best := edges.filter (fun M => M.card = mu)
      let ends := fun M : Finset (Fin k) => M ∪ M.image nxt
      let adj := fun i j : Fin k => i ∈ E ∧ j = nxt i
      let cs := (Finset.univ : Finset (Fin k)).image (fun i =>
        (Finset.univ : Finset (Fin k)).filter (fun j =>
          @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
      let oddCs := cs.filter (fun C => C.card % 2 = 1)
      let eligible := fun C : Finset (Fin k) =>
        if E = Finset.univ then C else C.filter (fun v =>
          ∃ s ∈ C, prv s ∉ E ∧ ((v.val+k-s.val) % k) % 2 = 0)
      let score := fun U : Finset (Fin k) =>
        ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
      let deficit := oddCs.powerset.sup (fun T =>
        2*g - ((oddCs.card-T.card) + score (T.biUnion eligible)))
      let D := if 3 ∣ k/g then deficit else 0
      let checks := fun M : Finset (Fin k) => ((Finset.univ : Finset W).filter (fun w =>
        (∀ j, j ∉ ends M → w j = 0) ∧ ∀ j : Fin k,
          w j + w (ix (j.val+spacing)) + w (ix (j.val+k-spacing % k)) = 0)).card
      let feasible := fun L : Nat =>
        ∃ tree : Tree, tree.1.card < L ∧ ∀ x : W,
          (sites.filter (fun i => predict tree x i ≠ out x i)).card ≤ e
      IsLeast {z : Nat | ∃ M ∈ best, checks M = z} (2^D) ∧
        feasible (2^(mu-e)) ∧ (∀ L : Nat, feasible L → 2^(mu-e-D) ≤ L) ∧
        (D = 0 → ∀ L : Nat, feasible L ↔ 2^(mu-e) ≤ L) ∧
        ((6 ≤ k ∧ 3 ∣ k ∧ (Nat.Coprime k spacing ∨ (spacing = 2 ∧ 12 ≤ k)) ∧
          E = Finset.univ.filter (fun i : Fin k => i.val % 3 ≠ 2)) →
          ∀ L : Nat, feasible L ↔ 2^(k/3-e) ≤ L)  := by
  intro k hk h2 F W ix rot spacing s t name constant out H Tree predict g sites e hsites
    E lane phase nxt prv edges mu best ends adj cs oddCs eligible score deficit D checks feasible
  open PEqualNP.Outside.L_meta_33637_aux in
  have hcut := Cut.cut_minmax k hk h2 E g lane phase
  obtain ⟨hcut_le, ⟨M0, hM0_best, hM0_sc⟩, hdef_le⟩ := hcut
  change ∀ M ∈ best, score (Finset.univ \ ends M) ≤ 2 * g - deficit at hcut_le
  change score (Finset.univ \ ends M0) = 2 * g - deficit at hM0_sc
  change deficit ≤ 2 * g at hdef_le
  have hout_eq : ∀ (x : W) (i : Fin k),
      out x i = PEqualNP.Outside.L_meta_33637_aux.output hk spacing s t name constant x i := fun x i =>
    (PEqualNP.Outside.L_meta_33637_aux.output_literal hk spacing s t name constant x i).symm
  have hpred_eq : ∀ (tree : Tree) (x : W) (i : Fin k),
      predict tree x i = PEqualNP.Outside.L_meta_33637_aux.Upper.predict tree x i := fun _ _ _ => rfl
  have hM0_mem : M0 ∈ edges ∧ M0.card = mu := Finset.mem_filter.mp hM0_best
  have hM0_sub : M0 ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hM0_mem.1).1
  have hM0_ind : ∀ u ∈ M0, nxt u ∉ M0 := (Finset.mem_filter.mp hM0_mem.1).2
  have hchecks_eq : ∀ M : Finset (Fin k),
      checks M = if 3 ∣ k / g then 2 ^ (2 * g - score (Finset.univ \ ends M)) else 1 := by
    intro M
    by_cases hd3 : 3 ∣ k / g
    · rw [ite_eq_left hd3]
      exact PEqualNP.Outside.L_meta_33637_aux.DualKernel.checks_eq_pow_of_dvd3 hk spacing hd3 (ends M)
    · rw [ite_eq_right hd3]
      exact PEqualNP.Outside.L_meta_33637_aux.DualKernel.checks_eq_one_of_not_dvd3 hk spacing hd3 (ends M)
  have hC1 : IsLeast {z : Nat | ∃ M ∈ best, checks M = z} (2 ^ D) := by
    refine ⟨⟨M0, hM0_best, ?_⟩, ?_⟩
    · rw [hchecks_eq M0]
      by_cases hd3 : 3 ∣ k / g
      · dsimp only [D]
        rw [ite_eq_left hd3, ite_eq_left hd3, hM0_sc]
        congr 1; omega
      · dsimp only [D]
        rw [ite_eq_right hd3, ite_eq_right hd3]
        rfl
    · rintro z ⟨M, hM, rfl⟩
      rw [hchecks_eq M]
      by_cases hd3 : 3 ∣ k / g
      · dsimp only [D]
        rw [ite_eq_left hd3, ite_eq_left hd3]
        have hle := hcut_le M hM
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      · dsimp only [D]
        rw [ite_eq_right hd3, ite_eq_right hd3]
        exact le_rfl
  have hC2 : feasible (2 ^ (mu - e)) := by
    obtain ⟨tree, hcard, herr⟩ :=
      PEqualNP.Outside.L_meta_33637_aux.Upper.upper_bound hk spacing s t name constant sites e hsites
    refine ⟨tree, hcard, ?_⟩
    intro x
    have hfilt : sites.filter (fun i => predict tree x i ≠ out x i) =
        sites.filter (fun i => PEqualNP.Outside.L_meta_33637_aux.Upper.predict tree x i ≠
          PEqualNP.Outside.L_meta_33637_aux.output hk spacing s t name constant x i) := by
      ext i; simp only [Finset.mem_filter, hout_eq, hpred_eq]
    rw [hfilt]
    exact herr x
  have hC3 : ∀ L : Nat, feasible L → 2 ^ (mu - e - D) ≤ L := by
    intro L ⟨tree, hcard, herr⟩
    have hM0_checks : checks M0 = 2 ^ D := by
      rw [hchecks_eq M0]
      by_cases hd3 : 3 ∣ k / g
      · dsimp only [D]
        rw [ite_eq_left hd3, ite_eq_left hd3, hM0_sc]
        congr 1; omega
      · dsimp only [D]
        rw [ite_eq_right hd3, ite_eq_right hd3]
        rfl
    have herr' : ∀ x : PEqualNP.Outside.L_meta_33637_aux.W k,
        (sites.filter (fun i => PEqualNP.Outside.L_meta_33637_aux.Upper.predict tree x i ≠
          PEqualNP.Outside.L_meta_33637_aux.output hk spacing s t name constant x i)).card ≤ e := by
      intro x
      have hfilt : sites.filter (fun i => PEqualNP.Outside.L_meta_33637_aux.Upper.predict tree x i ≠
          PEqualNP.Outside.L_meta_33637_aux.output hk spacing s t name constant x i) =
          sites.filter (fun i => predict tree x i ≠ out x i) := by
        ext i; simp only [Finset.mem_filter, hout_eq, hpred_eq]
      rw [hfilt]
      exact herr x
    have hlow := PEqualNP.Outside.L_meta_33637_aux.Lower.lower_bound hk spacing s t name constant
      sites e L D M0 hM0_sub hM0_ind hM0_checks tree hcard herr'
    rwa [hM0_mem.2] at hlow
  have hC4 : D = 0 → ∀ L : Nat, feasible L ↔ 2 ^ (mu - e) ≤ L := by
    intro hD0 L
    constructor
    · intro hf
      have := hC3 L hf
      rwa [hD0, Nat.sub_zero] at this
    · intro hle
      obtain ⟨tree, hcard, herr⟩ := hC2
      exact ⟨tree, lt_of_lt_of_le hcard hle, herr⟩
  have hC5 : (6 ≤ k ∧ 3 ∣ k ∧ (Nat.Coprime k spacing ∨ (spacing = 2 ∧ 12 ≤ k)) ∧
      E = Finset.univ.filter (fun i : Fin k => i.val % 3 ≠ 2)) →
      ∀ L : Nat, feasible L ↔ 2 ^ (k / 3 - e) ≤ L := by
    rintro ⟨h6, h3, hsp, hEeq⟩ L
    obtain ⟨hmu_eq, Mt, hMt_best, hMt_sc⟩ :=
      PEqualNP.Outside.L_meta_33637_aux.TriplePath.triple_mu_and_score hk h6 h3 spacing hsp
    have hedges_eq : edges =
        ((Finset.univ : Finset (Fin k)).filter (fun i => i.val % 3 ≠ 2)).powerset.filter
          (fun M => ∀ i ∈ M, PEqualNP.Outside.L_meta_33637_aux.Cut.a_nx k hk i ∉ M) := by
      ext M
      simp only [edges, Finset.mem_filter, Finset.mem_powerset, hEeq]
      rfl
    have hmu_eq' : mu = k / 3 := by
      dsimp only [mu]
      rw [hedges_eq]
      exact hmu_eq
    have hMt_best' : Mt ∈ best := by
      rw [Finset.mem_filter]
      have hMt' := Finset.mem_filter.mp hMt_best
      refine ⟨?_, ?_⟩
      · rw [hedges_eq]; exact hMt'.1
      · rw [hmu_eq', ← hmu_eq]; exact hMt'.2
    have hMt_sc' : score (Finset.univ \ ends Mt) = 2 * g := hMt_sc
    have hD0 : D = 0 := by
      by_cases hd3 : 3 ∣ k / g
      · have hle : 2 ^ D ≤ checks Mt := hC1.2 ⟨Mt, hMt_best', rfl⟩
        rw [hchecks_eq Mt, ite_eq_left hd3, hMt_sc', Nat.sub_self, Nat.pow_zero] at hle
        by_contra hnz
        have h2 : 2 ≤ 2 ^ D := by
          have : 1 ≤ D := Nat.pos_of_ne_zero hnz
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide : 0 < 2) this
        omega
      · dsimp only [D]
        rw [ite_eq_right hd3]
    rw [← hmu_eq']
    exact hC4 hD0 L
  exact ⟨hC1, hC2, hC3, hC4, hC5⟩
