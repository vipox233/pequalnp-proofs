import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_904_aux

variable {n : ℕ}

theorem disj_pairs_card (S : Finset (Fin n)) (E : Finset (Finset (Fin n)))
    (h1 : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint e f) (h2 : ∀ e ∈ E, e.card = 2)
    (h3 : ∀ e ∈ E, e ⊆ S) : 2 * E.card ≤ S.card := by
  have hc : (E.biUnion id).card = ∑ e ∈ E, e.card := Finset.card_biUnion h1
  have hs : E.biUnion id ⊆ S := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
    exact h3 e he hxe
  have := Finset.card_le_card hs
  rw [hc, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at this
  omega

def pairsOf (S : Finset (Fin n)) : Finset (Finset (Fin n)) := S.powerset.filter (fun e => e.card = 2)

abbrev Dj (M : Finset (Finset (Fin n))) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

def sg (P : Finset (Finset (Fin n))) : ℤ := if P.card = 2 then -1 else 1

def patsOf (S : Finset (Fin n)) : Finset (Finset (Finset (Fin n))) :=
  (S.powerset.filter (fun e => e.card = 2)).powerset.filter (fun P => P.Nonempty ∧ Dj P)

theorem mem_pairsOf {S : Finset (Fin n)} {e : Finset (Fin n)} :
    e ∈ pairsOf S ↔ e ⊆ S ∧ e.card = 2 := by
  simp [pairsOf, Finset.mem_powerset]

theorem hit_expand (S : Finset (Fin n)) (hS : S.card ≤ 4) (M : Finset (Finset (Fin n)))
    (hM1 : Dj M) (hM2 : ∀ e ∈ M, e.card = 2) :
    (if ∃ e ∈ M, e ⊆ S then (1 : ℤ) else 0) =
      ∑ P ∈ patsOf S, if P ⊆ M then sg P else 0 := by
  set E := M.filter (fun e => e ⊆ S) with hE
  have hEc : E.card ≤ 2 := by
    have := disj_pairs_card S E
      (fun e he f hf hne => hM1 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hne)
      (fun e he => hM2 e (Finset.mem_filter.mp he).1) (fun e he => (Finset.mem_filter.mp he).2)
    omega
  have hset : (patsOf S).filter (fun P => P ⊆ M) = E.powerset.filter (fun P => P.Nonempty) := by
    ext P
    simp only [patsOf, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hP, hne, hd⟩, hPM⟩
      refine ⟨?_, hne⟩
      intro e he
      refine Finset.mem_filter.mpr ⟨hPM he, ?_⟩
      have := Finset.mem_filter.mp (hP he)
      exact Finset.mem_powerset.mp this.1
    · rintro ⟨hPE, hne⟩
      refine ⟨⟨?_, hne, ?_⟩, fun e he => (Finset.mem_filter.mp (hPE he)).1⟩
      · intro e he
        have h := Finset.mem_filter.mp (hPE he)
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.2, hM2 e h.1⟩
      · intro e he f hf hne'
        exact hM1 e (Finset.mem_filter.mp (hPE he)).1 f (Finset.mem_filter.mp (hPE hf)).1 hne'
  rw [← Finset.sum_filter, hset]
  have hiff : (∃ e ∈ M, e ⊆ S) ↔ E.Nonempty := by
    constructor
    · rintro ⟨e, he, hes⟩
      exact ⟨e, Finset.mem_filter.mpr ⟨he, hes⟩⟩
    · rintro ⟨e, he⟩
      exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  have hsum : ∀ E' : Finset (Finset (Fin n)),
      ∑ P ∈ E'.powerset.filter (fun P => P.Nonempty), sg P =
        ∑ k ∈ Finset.range (E'.card + 1), (E'.card.choose k : ℤ) *
          (if 0 < k then (if k = 2 then -1 else 1) else 0) := by
    intro E'
    rw [Finset.sum_filter]
    have : ∀ P ∈ E'.powerset, (if P.Nonempty then sg P else 0) =
        (fun k : ℕ => (if 0 < k then (if k = 2 then (-1 : ℤ) else 1) else 0)) P.card := by
      intro P _
      simp only [sg, ← Finset.card_pos]
    rw [Finset.sum_congr rfl this, Finset.sum_powerset_apply_card
      (fun k : ℕ => (if 0 < k then (if k = 2 then (-1 : ℤ) else 1) else 0))]
    simp [nsmul_eq_mul]
  by_cases hne : E.Nonempty
  · rw [if_pos (hiff.mpr hne), hsum]
    have hc : E.card = 1 ∨ E.card = 2 := by
      have := Finset.card_pos.mpr hne
      omega
    rcases hc with hc | hc <;> rw [hc] <;> norm_num [Finset.sum_range_succ, Nat.choose]
  · rw [if_neg (fun h => hne (hiff.mp h)), hsum]
    have : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [this]
    simp

end PEqualNP.Outside.L_lib_904_aux
namespace PEqualNP.Outside.L_lib_904_aux

variable {n : ℕ}

theorem pats_card_le (S : Finset (Fin n)) {P : Finset (Finset (Fin n))} (hP : P ∈ patsOf S) :
    2 * P.card ≤ S.card := by
  simp only [patsOf, Finset.mem_filter, Finset.mem_powerset] at hP
  obtain ⟨hsub, hne, hd⟩ := hP
  apply disj_pairs_card S P hd
  · intro e he; exact (Finset.mem_filter.mp (hsub he)).2
  · intro e he; exact Finset.mem_powerset.mp (Finset.mem_filter.mp (hsub he)).1

theorem pats_nonempty {S : Finset (Fin n)} {P : Finset (Finset (Fin n))} (hP : P ∈ patsOf S) :
    P.Nonempty := by
  simp only [patsOf, Finset.mem_filter] at hP
  exact hP.2.1

theorem pats_pairs {S : Finset (Fin n)} {P : Finset (Finset (Fin n))} (hP : P ∈ patsOf S)
    {e : Finset (Fin n)} (he : e ∈ P) : e ⊆ S ∧ e.card = 2 := by
  simp only [patsOf, Finset.mem_filter, Finset.mem_powerset] at hP
  have := Finset.mem_filter.mp (hP.1 he)
  exact ⟨Finset.mem_powerset.mp this.1, this.2⟩

theorem pats_dj {S : Finset (Fin n)} {P : Finset (Finset (Fin n))} (hP : P ∈ patsOf S) : Dj P := by
  simp only [patsOf, Finset.mem_filter] at hP
  exact hP.2.2

theorem card_pairsOf (S : Finset (Fin n)) : (pairsOf S).card = S.card.choose 2 := by
  have : pairsOf S = S.powersetCard 2 := (Finset.powersetCard_eq_filter).symm
  rw [this, Finset.card_powersetCard]

theorem pats_card3 (S : Finset (Fin n)) (hS : S.card ≤ 3) : (patsOf S).card ≤ 3 := by
  have h1 : patsOf S ⊆ (pairsOf S).image (fun e => ({e} : Finset (Finset (Fin n)))) := by
    intro P hP
    have h2 := pats_card_le S hP
    have h3 := Finset.card_pos.mpr (pats_nonempty hP)
    have h4 : P.card = 1 := by omega
    obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h4
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    exact mem_pairsOf.mpr (pats_pairs hP (Finset.mem_singleton_self e))
  calc (patsOf S).card ≤ ((pairsOf S).image (fun e => ({e} : Finset (Finset (Fin n))))).card :=
        Finset.card_le_card h1
    _ ≤ (pairsOf S).card := Finset.card_image_le
    _ = S.card.choose 2 := card_pairsOf S
    _ ≤ 3 := by
        generalize S.card = k at hS ⊢
        interval_cases k <;> decide

theorem pair_with {x0 : Fin n} {e : Finset (Fin n)} (he : e.card = 2) (hx : x0 ∈ e) :
    ∃ y, y ≠ x0 ∧ e = {x0, y} := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨v, huv.symm, rfl⟩
  · exact ⟨u, huv, Finset.pair_comm _ _⟩

theorem pats_card4 (S : Finset (Fin n)) (hS : S.card = 4) : (patsOf S).card ≤ 9 := by
  obtain ⟨x0, hx0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set D := (patsOf S).filter (fun P => P.card = 2) with hD
  have hsub : patsOf S ⊆ ((pairsOf S).image (fun e => ({e} : Finset (Finset (Fin n))))) ∪ D := by
    intro P hP
    have h2 := pats_card_le S hP
    have h3 := Finset.card_pos.mpr (pats_nonempty hP)
    rcases (by omega : P.card = 1 ∨ P.card = 2) with h | h
    · apply Finset.mem_union_left
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h
      refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
      exact mem_pairsOf.mpr (pats_pairs hP (Finset.mem_singleton_self e))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP, h⟩)
  have hDc : D.card ≤ 3 := by
    set T := (S.erase x0).image (fun y => ({x0, y} : Finset (Fin n))) with hT
    have hTc : T.card ≤ 3 := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_erase_of_mem hx0]; omega
    have hDsub : D ⊆ T.image (fun e => ({e, S \ e} : Finset (Finset (Fin n)))) := by
      intro P hP
      obtain ⟨hPp, hc⟩ := Finset.mem_filter.mp hP
      obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hc
      have he := pats_pairs hPp (by simp : e ∈ ({e, f} : Finset (Finset (Fin n))))
      have hf := pats_pairs hPp (by simp : f ∈ ({e, f} : Finset (Finset (Fin n))))
      have hdis : Disjoint e f :=
        pats_dj hPp e (by simp) f (by simp) hef
      have hunion : e ∪ f = S := by
        apply Finset.eq_of_subset_of_card_le (Finset.union_subset he.1 hf.1)
        rw [Finset.card_union_of_disjoint hdis]; omega
      have hfS : f = S \ e := by
        ext z
        constructor
        · intro hz
          refine Finset.mem_sdiff.mpr ⟨hf.1 hz, ?_⟩
          intro hze
          exact Finset.disjoint_left.mp hdis hze hz
        · intro hz
          obtain ⟨hzS, hze⟩ := Finset.mem_sdiff.mp hz
          rw [← hunion] at hzS
          rcases Finset.mem_union.mp hzS with h | h
          · exact absurd h hze
          · exact h
      have hxs : x0 ∈ e ∪ f := by rw [hunion]; exact hx0
      have memT : ∀ g : Finset (Fin n), g ⊆ S → g.card = 2 → x0 ∈ g → g ∈ T := by
        intro g hg hgc hxg
        obtain ⟨y, hy, rfl⟩ := pair_with hgc hxg
        refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
        exact Finset.mem_erase.mpr ⟨hy, hg (by simp)⟩
      rcases Finset.mem_union.mp hxs with h | h
      · refine Finset.mem_image.mpr ⟨e, memT e he.1 he.2 h, ?_⟩
        rw [hfS]
      · refine Finset.mem_image.mpr ⟨f, memT f hf.1 hf.2 h, ?_⟩
        have : e = S \ f := by
          ext z
          constructor
          · intro hz
            refine Finset.mem_sdiff.mpr ⟨he.1 hz, ?_⟩
            intro hzf
            exact Finset.disjoint_left.mp hdis hz hzf
          · intro hz
            obtain ⟨hzS, hzf⟩ := Finset.mem_sdiff.mp hz
            rw [← hunion] at hzS
            rcases Finset.mem_union.mp hzS with h | h
            · exact h
            · exact absurd h hzf
        rw [← this]
        exact Finset.pair_comm _ _
    exact (Finset.card_le_card hDsub).trans (Finset.card_image_le.trans hTc)
  calc (patsOf S).card ≤ (((pairsOf S).image (fun e => ({e} : Finset (Finset (Fin n))))) ∪ D).card :=
        Finset.card_le_card hsub
    _ ≤ ((pairsOf S).image (fun e => ({e} : Finset (Finset (Fin n))))).card + D.card :=
        Finset.card_union_le _ _
    _ ≤ (pairsOf S).card + 3 := Nat.add_le_add Finset.card_image_le hDc
    _ = 9 := by rw [card_pairsOf, hS]; decide

theorem pats_card_bound (S : Finset (Fin n)) (hS : S.card ≤ 4) :
    (patsOf S).card ≤ if S.card = 4 then 9 else 3 := by
  by_cases h : S.card = 4
  · rw [if_pos h]; exact pats_card4 S h
  · rw [if_neg h]; exact pats_card3 S (by omega)

theorem prod_expand {m : ℕ} (extra : Fin m → Finset (Fin n)) (hx : ∀ i, (extra i).card ≤ 4)
    (M : Finset (Finset (Fin n))) (hM1 : Dj M) (hM2 : ∀ e ∈ M, e.card = 2) :
    (if ∀ i, ∃ e ∈ M, e ⊆ extra i then (1 : ℤ) else 0) =
      ∑ a ∈ Fintype.piFinset (fun i => patsOf (extra i)),
        if (∀ i, a i ⊆ M) then ∏ i, sg (a i) else 0 := by
  calc (if ∀ i, ∃ e ∈ M, e ⊆ extra i then (1 : ℤ) else 0)
      = ∏ i, (if ∃ e ∈ M, e ⊆ extra i then (1 : ℤ) else 0) := by
        rw [Finset.prod_boole]; simp
    _ = ∏ i, ∑ P ∈ patsOf (extra i), (if P ⊆ M then sg P else 0) :=
        Finset.prod_congr rfl (fun i _ => hit_expand (extra i) (hx i) M hM1 hM2)
    _ = ∑ a ∈ Fintype.piFinset (fun i => patsOf (extra i)), ∏ i, (if a i ⊆ M then sg (a i) else 0) :=
        Finset.prod_univ_sum _ _
    _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.prod_ite_zero]
        simp

end PEqualNP.Outside.L_lib_904_aux

namespace PEqualNP.Outside.L_lib_904_aux

variable {n : ℕ}

abbrev Bm (U : Finset (Fin n)) (H : Finset (Finset (Fin n))) (s : ℕ)
    (M : Finset (Finset (Fin n))) : Prop :=
  Dj M ∧ (∀ e ∈ M, e.card = 2 ∧ e ⊆ U) ∧ (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧ M.card = s

theorem count_eq (U : Finset (Fin n)) (H : Finset (Finset (Fin n))) (s : ℕ) :
    Nat.card {M : Finset (Finset (Fin n)) // Bm U H s M} =
      (Finset.univ.filter (Bm U H s)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem disj_of_sub {e X U : Finset (Fin n)} (h : e ⊆ U \ X) : Disjoint e X :=
  Finset.disjoint_of_subset_left h Finset.sdiff_disjoint

theorem decomp (U : Finset (Fin n)) (H : Finset (Finset (Fin n))) (s : ℕ)
    (P : Finset (Finset (Fin n))) (hP : ∀ e ∈ P, e.card = 2 ∧ e ⊆ U) (hPd : Dj P) :
    (Finset.univ.filter (fun M => Bm U H s M ∧ P ⊆ M)).card =
      if P.card ≤ s then
        (Finset.univ.filter (Bm (U \ P.biUnion id)
          ((H.filter (fun R => ¬ ∃ e ∈ P, e ⊆ R)).image (fun R => R \ P.biUnion id))
          (s - P.card))).card
      else 0 := by
  split_ifs with hle
  · apply Finset.card_nbij' (fun M => M \ P) (fun M' => M' ∪ P)
    · intro M hM
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
      obtain ⟨⟨hd, hedge, hhit, hcard⟩, hPM⟩ := hM
      have hdisj : ∀ e ∈ M \ P, Disjoint e (P.biUnion id) := by
        intro e he
        obtain ⟨heM, heP⟩ := Finset.mem_sdiff.mp he
        rw [Finset.disjoint_biUnion_right]
        intro f hf
        exact hd e heM f (hPM hf) (fun h => heP (h ▸ hf))
      refine ⟨fun e he f hf hne => hd e (Finset.mem_sdiff.mp he).1 f (Finset.mem_sdiff.mp hf).1 hne,
        ?_, ?_, ?_⟩
      · intro e he
        refine ⟨(hedge e (Finset.mem_sdiff.mp he).1).1, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨(hedge e (Finset.mem_sdiff.mp he).1).2 hx,
          fun hxb => Finset.disjoint_left.mp (hdisj e he) hx hxb⟩
      · intro R' hR'
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hR'
        obtain ⟨hRH, hRP⟩ := Finset.mem_filter.mp hR
        obtain ⟨e, heM, heR⟩ := hhit R hRH
        have heP : e ∉ P := fun h => hRP ⟨e, h, heR⟩
        have he : e ∈ M \ P := Finset.mem_sdiff.mpr ⟨heM, heP⟩
        refine ⟨e, he, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨heR hx, fun hxb => Finset.disjoint_left.mp (hdisj e he) hx hxb⟩
      · rw [Finset.card_sdiff_of_subset hPM, hcard]
    · intro M' hM'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM' ⊢
      obtain ⟨hd, hedge, hhit, hcard⟩ := hM'
      have hdisj : ∀ e ∈ M', ∀ f ∈ P, Disjoint e f := by
        intro e he f hf
        have h1 : Disjoint e (P.biUnion id) := disj_of_sub (hedge e he).2
        exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hf) h1
      have hnot : ∀ e ∈ M', e ∉ P := by
        intro e he hP'
        have h1 := hdisj e he e hP'
        have h2 := (hedge e he).1
        have : e = ∅ := Finset.disjoint_self_iff_empty _ |>.mp h1
        rw [this] at h2
        simp at h2
      refine ⟨⟨?_, ?_, ?_, ?_⟩, Finset.subset_union_right⟩
      · intro e he f hf hne
        rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
        · exact hd e he f hf hne
        · exact hdisj e he f hf
        · exact (hdisj f hf e he).symm
        · exact hPd e he f hf hne
      · intro e he
        rcases Finset.mem_union.mp he with he | he
        · exact ⟨(hedge e he).1, (hedge e he).2.trans Finset.sdiff_subset⟩
        · exact hP e he
      · intro R hR
        by_cases hRP : ∃ e ∈ P, e ⊆ R
        · obtain ⟨e, he, heR⟩ := hRP
          exact ⟨e, Finset.mem_union_right _ he, heR⟩
        · obtain ⟨e, he, heR⟩ := hhit (R \ P.biUnion id)
            (Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨hR, hRP⟩, rfl⟩)
          exact ⟨e, Finset.mem_union_left _ he, heR.trans Finset.sdiff_subset⟩
      · rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun e he heP => hnot e he heP)),
          hcard]
        omega
    · intro M hM
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM
      exact Finset.sdiff_union_of_subset hM.2
    · intro M' hM'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM'
      obtain ⟨hd, hedge, hhit, hcard⟩ := hM'
      have hnot : Disjoint M' P := by
        rw [Finset.disjoint_left]
        intro e he hP'
        have h1 : Disjoint e (P.biUnion id) := disj_of_sub (hedge e he).2
        have h1' := Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hP') h1
        have : e = ∅ := (Finset.disjoint_self_iff_empty _).mp h1'
        have h2 := (hedge e he).1
        rw [this] at h2
        simp at h2
      exact Finset.union_sdiff_cancel_right hnot
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro M _ h
    exact hle ((Finset.card_le_card h.2).trans h.1.2.2.2.le)

end PEqualNP.Outside.L_lib_904_aux

namespace PEqualNP.Outside.L_lib_904_aux

variable {n : ℕ}

theorem prod_sg {m : ℕ} (a : Fin m → Finset (Finset (Fin n))) :
    ∏ i, sg (a i) = (-1 : ℤ) ^ ((Finset.univ.filter (fun i => (a i).card = 2)).card) := by
  simp only [sg]
  rw [Finset.prod_ite]
  simp

end PEqualNP.Outside.L_lib_904_aux

open PEqualNP.Outside.L_lib_904_aux in
theorem PEqualNP.Outside.L_lib_904 : (∀ n m : Nat,
  let Rows := Finset (Finset (Fin n))
  let disj := fun M : Rows => ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f
  let linear := fun H : Rows => ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1
  let count := fun (U : Finset (Fin n)) (H : Rows) (s : Nat) =>
    Nat.card {M : Rows // disj M ∧ (∀ e ∈ M, e.card = 2 ∧ e ⊆ U) ∧
      (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧ M.card = s}
  ∀ (U : Finset (Fin n)) (H : Rows) (extra : Fin m → Finset (Fin n)),
    (∀ R ∈ H, R ⊆ U ∧ R.card ≤ 3) → linear H →
    (∀ i, extra i ⊆ U ∧ (extra i).card ≤ 4) →
    let pats := fun S : Finset (Fin n) =>
      (S.powerset.filter (fun e => e.card = 2)).powerset.filter (fun P => P.Nonempty ∧ disj P)
    let choices := Finset.univ.filter (fun a : Fin m → Rows => ∀ i, a i ∈ pats (extra i))
    let q := (Finset.univ.filter (fun i => (extra i).card = 4)).card
    let pins := fun a : Fin m → Rows => Finset.univ.biUnion a
    let rest := fun P : Rows => (H.filter (fun R => ¬ ∃ e ∈ P, e ⊆ R)).image
      (fun R => R \ P.biUnion id)
    choices.card ≤ 9^q * 3^(m-q) ∧
    (∀ a ∈ choices, linear (rest (pins a)) ∧ ∀ R ∈ rest (pins a), R.card ≤ 3) ∧
    ∀ s : Nat, (count U (H ∪ Finset.univ.image extra) s : Int) =
      choices.sum (fun a => let P := pins a
        if disj P ∧ P.card ≤ s then
          (-1 : Int)^((Finset.univ.filter (fun i => (a i).card = 2)).card) *
            (count (U \ P.biUnion id) (rest P) (s-P.card) : Int)
        else 0)) := by
  intro n m Rows disj linear count U H extra hH hlin hex pats choices q pins rest
  have hchoices : choices = Fintype.piFinset (fun i => patsOf (extra i)) := by
    ext a
    rw [Fintype.mem_piFinset]
    simp only [choices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hchoices, Fintype.card_piFinset]
    calc ∏ i, (patsOf (extra i)).card ≤ ∏ i : Fin m, (if (extra i).card = 4 then 9 else 3) :=
          Finset.prod_le_prod' (fun i _ => pats_card_bound (extra i) (hex i).2)
      _ = 9 ^ q * 3 ^ (m - q) := by
          rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
          have : (Finset.univ.filter (fun i : Fin m => ¬ (extra i).card = 4)).card = m - q := by
            rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
              Finset.card_univ, Fintype.card_fin]
          rw [this]
  · intro a ha
    constructor
    · intro e he f hf hne
      obtain ⟨R1, hR1', hR1e⟩ := Finset.mem_image.mp
        (show e ∈ (H.filter (fun R => ¬ ∃ e ∈ pins a, e ⊆ R)).image
          (fun R => R \ (pins a).biUnion id) from he)
      obtain ⟨R2, hR2', hR2e⟩ := Finset.mem_image.mp
        (show f ∈ (H.filter (fun R => ¬ ∃ e ∈ pins a, e ⊆ R)).image
          (fun R => R \ (pins a).biUnion id) from hf)
      have hR1 := (Finset.mem_filter.mp hR1').1
      have hR2 := (Finset.mem_filter.mp hR2').1
      have hne' : R1 ≠ R2 := fun h => hne (by rw [← hR1e, ← hR2e, h])
      refine (Finset.card_le_card ?_).trans (hlin R1 hR1 R2 hR2 hne')
      intro x hx
      rw [← hR1e, ← hR2e] at hx
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx ⊢
      exact ⟨hx.1.1, hx.2.1⟩
    · intro R hR
      obtain ⟨R0, hR0', hR0e⟩ := Finset.mem_image.mp
        (show R ∈ (H.filter (fun R => ¬ ∃ e ∈ pins a, e ⊆ R)).image
          (fun R => R \ (pins a).biUnion id) from hR)
      have hR0 := (Finset.mem_filter.mp hR0').1
      rw [← hR0e]
      exact (Finset.card_le_card Finset.sdiff_subset).trans (hH R0 hR0).2
  · intro s
    have hx4 : ∀ i, (extra i).card ≤ 4 := fun i => (hex i).2
    have hxU : ∀ i, extra i ⊆ U := fun i => (hex i).1
    have h1 : count U (H ∪ Finset.univ.image extra) s =
        (Finset.univ.filter (Bm U (H ∪ Finset.univ.image extra) s)).card :=
      count_eq _ _ _
    have hB : ∀ M, Bm U (H ∪ Finset.univ.image extra) s M ↔
        Bm U H s M ∧ ∀ i, ∃ e ∈ M, e ⊆ extra i := by
      intro M
      simp only [Bm, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hd, he, hh, hc⟩
        exact ⟨⟨hd, he, fun R hR => hh R (Or.inl hR), hc⟩, fun i => hh _ (Or.inr ⟨i, rfl⟩)⟩
      · rintro ⟨⟨hd, he, hh, hc⟩, hx⟩
        refine ⟨hd, he, ?_, hc⟩
        rintro R (hR | ⟨i, rfl⟩)
        · exact hh R hR
        · exact hx i
    have h2 : ((Finset.univ.filter (Bm U (H ∪ Finset.univ.image extra) s)).card : ℤ) =
        ∑ M ∈ Finset.univ.filter (Bm U H s),
          (if ∀ i, ∃ e ∈ M, e ⊆ extra i then (1 : ℤ) else 0) := by
      rw [Finset.filter_congr (fun M _ => hB M), ← Finset.filter_filter, Finset.card_filter]
      push_cast
      rfl
    have h3 : ∑ M ∈ Finset.univ.filter (Bm U H s),
          (if ∀ i, ∃ e ∈ M, e ⊆ extra i then (1 : ℤ) else 0) =
        ∑ a ∈ Fintype.piFinset (fun i => patsOf (extra i)),
          (∏ i, sg (a i)) * ((Finset.univ.filter (fun M => Bm U H s M ∧ pins a ⊆ M)).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun M hM => by
        have hM' := (Finset.mem_filter.mp hM).2
        exact prod_expand extra hx4 M hM'.1 (fun e he => (hM'.2.1 e he).1))]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      have hiff : ∀ M : Finset (Finset (Fin n)), (∀ i, a i ⊆ M) ↔ pins a ⊆ M := by
        intro M
        simp only [pins, Finset.biUnion_subset, Finset.mem_univ, true_implies]
      simp_rw [hiff]
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_filter, nsmul_eq_mul, mul_comm]
    rw [h1, h2, h3, hchoices]
    apply Finset.sum_congr rfl
    intro a ha
    have hP : ∀ e ∈ pins a, e.card = 2 ∧ e ⊆ U := by
      intro e he
      obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      have := Fintype.mem_piFinset.mp ha i
      obtain ⟨hs, hc⟩ := pats_pairs this hei
      exact ⟨hc, hs.trans (hxU i)⟩
    dsimp only
    by_cases hPd : Dj (pins a)
    · have hd := decomp U H s (pins a) hP hPd
      rw [hd]
      by_cases hle : (pins a).card ≤ s
      · have hc : count (U \ (pins a).biUnion id) (rest (pins a)) (s - (pins a).card) =
            (Finset.univ.filter (Bm (U \ (pins a).biUnion id)
              ((H.filter (fun R => ¬ ∃ e ∈ pins a, e ⊆ R)).image
                (fun R => R \ (pins a).biUnion id)) (s - (pins a).card))).card :=
          count_eq _ _ _
        rw [if_pos hle, if_pos (show disj (pins a) ∧ (pins a).card ≤ s from ⟨hPd, hle⟩),
          prod_sg, hc]
      · rw [if_neg hle, if_neg (show ¬ (disj (pins a) ∧ (pins a).card ≤ s) from fun h => hle h.2)]
        simp
    · have hz : (Finset.univ.filter (fun M => Bm U H s M ∧ pins a ⊆ M)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro M _ h
        apply hPd
        intro e he f hf hne
        exact h.1.1 e (h.2 he) f (h.2 hf) hne
      rw [hz, if_neg (show ¬ (disj (pins a) ∧ (pins a).card ≤ s) from fun h => hPd h.1)]
      simp
