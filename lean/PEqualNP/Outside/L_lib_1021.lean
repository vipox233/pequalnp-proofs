import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1021
def bscore {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3) (U : Finset (Fin k)) : Nat :=
  ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
theorem b_le {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3) (U : Finset (Fin k)) :
    bscore g lane phase U ≤ 2 * g := by
  unfold bscore
  calc ∑ j ∈ Finset.range g, min 2 (((U.filter (fun v => lane v = j)).image phase).card)
      ≤ ∑ _j ∈ Finset.range g, 2 := Finset.sum_le_sum (fun j _ => Nat.min_le_left _ _)
    _ = 2 * g := by simp [Nat.mul_comm]
theorem b_mono {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3)
    (U V : Finset (Fin k)) (h : U ⊆ V) : bscore g lane phase U ≤ bscore g lane phase V := by
  unfold bscore
  apply Finset.sum_le_sum
  intro j _
  exact min_le_min le_rfl
    (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ h)))
theorem b_lane {k : Nat} (lane : Fin k → Nat) (phase : Fin k → Fin 3) (j : Nat)
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
theorem b_submod {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3)
    (U V : Finset (Fin k)) :
    bscore g lane phase (U ∪ V) + bscore g lane phase (U ∩ V) ≤
      bscore g lane phase U + bscore g lane phase V := by
  unfold bscore
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact b_lane lane phase j U V
theorem b_card {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3)
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
          · rw [if_pos hc, hc]
            exact Finset.card_erase_le
          · rw [if_neg hc]
        · exact ⟨C0, hC0, by rw [if_pos rfl]; exact Finset.card_erase_lt_of_mem hz⟩
      have hne' : ∀ C ∈ S, (if C = C0 then (A C0).erase z else A C).Nonempty := by
        intro C hC
        by_cases hc : C = C0
        · rw [if_pos hc]
          exact ⟨w, Finset.mem_erase.mpr ⟨hwz, hw⟩⟩
        · rw [if_neg hc]
          exact hne C hC
      obtain ⟨f, hf, hfm⟩ :=
        ih _ hlt (fun C => if C = C0 then (A C0).erase z else A C) rfl hne' m hmz
      refine ⟨f, fun C hC => ?_, hfm⟩
      have hfC := hf C hC
      by_cases hc : C = C0
      · rw [if_pos hc] at hfC
        have hfC2 := Finset.mem_of_mem_erase hfC
        rw [hc] at hfC2 ⊢
        exact hfC2
      · rw [if_neg hc] at hfC
        exact hfC
    by_cases h1 : ∀ T ⊆ S, m ≤ S.card - T.card +
        r (T.biUnion (fun C => if C = C0 then (A C0).erase x else A C))
    · exact key x hx y hy (Ne.symm hxy) h1
    by_cases h2 : ∀ T ⊆ S, m ≤ S.card - T.card +
        r (T.biUnion (fun C => if C = C0 then (A C0).erase y else A C))
    · exact key y hy x hx hxy h2
    exfalso
    push_neg at h1 h2
    obtain ⟨T1, hT1, h1⟩ := h1
    obtain ⟨T2, hT2, h2⟩ := h2
    have hC1 : C0 ∈ T1 := by
      by_contra hc
      have he : T1.biUnion (fun C => if C = C0 then (A C0).erase x else A C) = T1.biUnion A := by
        apply Finset.biUnion_congr rfl
        intro C hC
        have hCne : C ≠ C0 := fun h => hc (h ▸ hC)
        rw [if_neg hCne]
      rw [he] at h1
      have := hm T1 hT1
      omega
    have hC2 : C0 ∈ T2 := by
      by_contra hc
      have he : T2.biUnion (fun C => if C = C0 then (A C0).erase y else A C) = T2.biUnion A := by
        apply Finset.biUnion_congr rfl
        intro C hC
        have hCne : C ≠ C0 := fun h => hc (h ▸ hC)
        rw [if_neg hCne]
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
          rw [if_pos rfl]
          exact Finset.mem_erase.mpr ⟨by rw [hvx]; exact hxy, hvC⟩
        · left
          refine ⟨C0, hC1, ?_⟩
          rw [if_pos rfl]
          exact Finset.mem_erase.mpr ⟨hvx, hvC⟩
      · rcases hC with hC | hC
        · left
          exact ⟨C, hC, by rw [if_neg hc]; exact hvC⟩
        · right
          exact ⟨C, hC, by rw [if_neg hc]; exact hvC⟩
    have incI : ((T1 ∩ T2).erase C0).biUnion A ⊆
        T1.biUnion (fun C => if C = C0 then (A C0).erase x else A C) ∩
          T2.biUnion (fun C => if C = C0 then (A C0).erase y else A C) := by
      intro v hv
      simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_erase] at hv ⊢
      obtain ⟨C, ⟨hc, hC1', hC2'⟩, hvC⟩ := hv
      exact ⟨⟨C, hC1', by rw [if_neg hc]; exact hvC⟩, ⟨C, hC2', by rw [if_neg hc]; exact hvC⟩⟩
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
  · push_neg at h
    refine ⟨fun C => if hC : (A C).Nonempty then hC.choose else d, ?_, ?_⟩
    · intro C hC
      simp only [dif_pos (hne C hC)]
      exact (hne C hC).choose_spec
    · have hS := hm S (Finset.Subset.refl S)
      rw [Nat.sub_self, Nat.zero_add] at hS
      refine le_trans hS (hmono _ _ ?_)
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨C, hC, hvC⟩ := hv
      rw [Finset.mem_image]
      refine ⟨C, hC, ?_⟩
      simp only [dif_pos (hne C hC)]
      exact h C hC _ (hne C hC).choose_spec v hvC
theorem b_upper {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3)
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
theorem b_lower {k : Nat} (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3)
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
theorem a_struct (k : Nat) (hk : 0 < k) (h2 : 2 ≤ k) :
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
end PEqualNP.Outside.L_lib_1021
theorem PEqualNP.Outside.L_lib_1021 : ∀ (k : Nat) (hk : 0 < k), 2 ≤ k →
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  ∀ (E : Finset (Fin k)) (g : Nat) (lane : Fin k → Nat) (phase : Fin k → Fin 3),
    (∀ v, lane v < g) →
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
    (best.sup (fun M => score (Finset.univ \ ends M))) + deficit = 2*g := by
  intro k hk h2 ix E g lane phase hl nxt prv edges mu best ends adj cs oddCs eligible score deficit
  obtain ⟨hA1, hA2, hA3⟩ := PEqualNP.Outside.L_lib_1021.a_struct k hk h2 E
  have hsc : ∀ U, score U = PEqualNP.Outside.L_lib_1021.bscore g lane phase U := fun U => rfl
  obtain ⟨f0, hf0, T0, hT0, hlow⟩ := PEqualNP.Outside.L_lib_1021.b_lower g lane phase oddCs eligible hA3
  obtain ⟨M0, hM0, hM0e⟩ := hA2 f0 hf0
  have hup : ∀ M ∈ best, ∀ T ∈ oddCs.powerset,
      score (Finset.univ \ ends M) ≤ (oddCs.card - T.card) + score (T.biUnion eligible) := by
    intro M hM T hT
    obtain ⟨f, hf, he⟩ := hA1 M hM
    rw [he, hsc, hsc]
    exact PEqualNP.Outside.L_lib_1021.b_upper g lane phase oddCs eligible f hf T (Finset.mem_powerset.mp hT)
  have h2g : ∀ U, score U ≤ 2 * g := fun U => by
    rw [hsc]; exact PEqualNP.Outside.L_lib_1021.b_le g lane phase U
  have hm1 : (oddCs.card - T0.card) + score (T0.biUnion eligible)
      ≤ best.sup (fun M => score (Finset.univ \ ends M)) := by
    have h1 : score (Finset.univ \ ends M0) ≤ best.sup (fun M => score (Finset.univ \ ends M)) :=
      Finset.le_sup (f := fun M => score (Finset.univ \ ends M)) hM0
    rw [hM0e, hsc] at h1
    rw [hsc]
    exact le_trans hlow h1
  have hm2 : ∀ T ∈ oddCs.powerset, best.sup (fun M => score (Finset.univ \ ends M))
      ≤ (oddCs.card - T.card) + score (T.biUnion eligible) := by
    intro T hT
    exact Finset.sup_le (fun M hM => hup M hM T hT)
  have hm3 : best.sup (fun M => score (Finset.univ \ ends M)) ≤ 2 * g :=
    Finset.sup_le (fun M _ => h2g _)
  have hd1 : deficit ≤ 2 * g - best.sup (fun M => score (Finset.univ \ ends M)) := by
    refine Finset.sup_le (fun T hT => ?_)
    have := hm2 T hT
    omega
  have hd2 : 2 * g - ((oddCs.card - T0.card) + score (T0.biUnion eligible)) ≤ deficit :=
    Finset.le_sup (f := fun T => 2*g - ((oddCs.card-T.card) + score (T.biUnion eligible)))
      (Finset.mem_powerset.mpr hT0)
  have hm4 := hm2 T0 (Finset.mem_powerset.mpr hT0)
  omega
