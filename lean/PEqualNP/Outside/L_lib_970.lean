import Mathlib

namespace PEqualNP.Outside.L_lib_970_aux

open scoped BigOperators

private def ends {v : ℕ} (e : Fin v × Fin v) : Finset (Fin v) := {e.1,e.2}

private noncomputable def msets {v : ℕ} (S : Finset (Fin v)) (j : ℕ) :
    Finset (Finset (Fin v × Fin v)) := by
  classical
  exact (((Finset.univ : Finset (Fin v × Fin v)).filter
    (fun e => e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S)).powerset).filter
    (fun Q => (∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)) ∧ Q.card = j)

private noncomputable def coeff {v : ℕ} (x : Fin v × Fin v → ℝ)
    (S : Finset (Fin v)) (j : ℕ) : ℝ := (msets S j).sum fun Q => Q.prod x

private theorem mem_msets {v j : ℕ} {S : Finset (Fin v)} {Q : Finset (Fin v × Fin v)} :
    Q ∈ msets S j ↔
      (∀ e ∈ Q, e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S) ∧
      (∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)) ∧ Q.card = j := by
  classical
  simp [msets, Finset.subset_iff]

private theorem coeff_nonneg {v : ℕ} {x : Fin v × Fin v → ℝ} (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin v)) (j : ℕ) : 0 ≤ coeff x S j :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun e _ => hx e

private theorem coeff_mono {v : ℕ} {x : Fin v × Fin v → ℝ} (hx : ∀ e, 0 ≤ x e)
    {S T : Finset (Fin v)} (h : S ⊆ T) (j : ℕ) : coeff x S j ≤ coeff x T j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro Q hQ
    rcases mem_msets.mp hQ with ⟨h1,h2,h3⟩
    exact mem_msets.mpr ⟨fun e he => ⟨(h1 e he).1, h (h1 e he).2.1, h (h1 e he).2.2⟩, h2,h3⟩
  · exact fun Q _ _ => Finset.prod_nonneg fun e _ => hx e

private theorem coeff_pos_down {v : ℕ} {x : Fin v × Fin v → ℝ} (hx : ∀ e, 0 ≤ x e)
    {S : Finset (Fin v)} {i j : ℕ} (hij : i ≤ j) (hj : 0 < coeff x S j) :
    0 < coeff x S i := by
  classical
  obtain ⟨Q,hQ,hQpos⟩ : ∃ Q ∈ msets S j, 0 < Q.prod x := by
    by_contra! hn
    exact (not_lt.mpr (Finset.sum_nonpos hn)) hj
  rcases mem_msets.mp hQ with ⟨h1,h2,h3⟩
  obtain ⟨P,hPQ,hP⟩ := Finset.exists_subset_card_eq (h3 ▸ hij)
  have hm : P ∈ msets S i := mem_msets.mpr ⟨fun e he => h1 e (hPQ he),
    fun e he f hf => h2 e (hPQ he) f (hPQ hf), hP⟩
  have hp : ∀ e ∈ P, 0 < x e := by
    intro e he
    have hz : x e ≠ 0 := by
      intro hz
      exact hQpos.ne' (Finset.prod_eq_zero (hPQ he) hz)
    exact lt_of_le_of_ne (hx e) (Ne.symm hz)
  exact lt_of_lt_of_le (Finset.prod_pos hp)
    (Finset.single_le_sum (fun R _ => Finset.prod_nonneg fun e _ => hx e) hm)

private theorem coeff_zero {v : ℕ} (x : Fin v × Fin v → ℝ) (S : Finset (Fin v)) :
    coeff x S 0 = 1 := by
  classical
  have h : msets S 0 = {∅} := by
    ext Q
    constructor
    · intro hQ
      exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (mem_msets.mp hQ).2.2)
    · intro hQ
      rw [Finset.mem_singleton.mp hQ]
      simp [mem_msets]
  simp [coeff,h]

private def link {v : ℕ} (t u : Fin v) : Fin v × Fin v := (min t u,max t u)

private theorem link_lt {v : ℕ} {t u : Fin v} (h : t ≠ u) :
    (link t u).1 < (link t u).2 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simpa [link, min_eq_left hlt.le, max_eq_right hlt.le]
  · simpa [link, min_eq_right hgt.le, max_eq_left hgt.le]

private theorem ends_link {v : ℕ} (t u : Fin v) : ends (link t u) = {t,u} := by
  rcases le_total t u with h | h
  · simp [ends, link, min_eq_left h, max_eq_right h]
  · ext a
    simp [ends, link, min_eq_right h, max_eq_left h, or_comm]

private theorem link_repr {v : ℕ} {e : Fin v × Fin v} {t : Fin v}
    (he : e.1 < e.2) (ht : t ∈ ends e) :
    ∃ u, u ≠ t ∧ u ∈ ends e ∧ link t u = e := by
  rcases (show t = e.1 ∨ t = e.2 from by simpa [ends] using ht) with h | h
  · subst t
    exact ⟨e.2,he.ne',by simp [ends],by simp [link, min_eq_left he.le, max_eq_right he.le]⟩
  · subst t
    exact ⟨e.1,he.ne,by simp [ends],by simp [link, min_eq_right he.le, max_eq_left he.le]⟩

private theorem link_inj {v : ℕ} {t u z : Fin v} (hu : u ≠ t)
    (h : link t u = link t z) : u = z := by
  have hh : u ∈ ends (link t z) := by rw [← h, ends_link]; simp
  simpa [ends_link, hu] using hh

private theorem avoid_ends {v k : ℕ} {S : Finset (Fin v)} {Q : Finset (Fin v × Fin v)}
    (hQ : Q ∈ msets S k) {t : Fin v} (ht : t ∉ S) (e : Fin v × Fin v) (he : e ∈ Q) :
    t ∉ ends e := by
  have h := (mem_msets.mp hQ).1 e he
  simp only [ends, Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl)
  · exact ht h.2.1
  · exact ht h.2.2

private theorem insert_link {v k : ℕ} {S : Finset (Fin v)} {t u : Fin v}
    (ht : t ∉ S) (hu : u ∈ S) {Q : Finset (Fin v × Fin v)}
    (hQ : Q ∈ msets (S.erase u) k) :
    link t u ∉ Q ∧ insert (link t u) Q ∈ msets (insert t S) (k+1) := by
  have hta : t ∉ S.erase u := fun h => ht (Finset.mem_of_mem_erase h)
  have hne : t ≠ u := fun h => ht (h ▸ hu)
  have hab : link t u ∉ Q := by
    intro h
    exact avoid_ends hQ hta _ h (by simp [ends_link])
  have apart : ∀ e ∈ Q, Disjoint (ends (link t u)) (ends e) := by
    intro e he
    rw [Finset.disjoint_left, ends_link]
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact avoid_ends hQ hta e he
    · exact avoid_ends hQ (Finset.notMem_erase _ _) e he
  rcases mem_msets.mp hQ with ⟨h1,h2,h3⟩
  refine ⟨hab, mem_msets.mpr ⟨?_,?_,by rw [Finset.card_insert_of_notMem hab,h3]⟩⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · refine ⟨link_lt hne, ?_, ?_⟩
      all_goals
        have sub : ends (link t u) ⊆ insert t S := by
          rw [ends_link]
          simp [Finset.insert_subset_iff,hu]
        apply sub
        simp [ends]
    · exact ⟨(h1 e he).1,Finset.mem_insert_of_mem (Finset.mem_of_mem_erase (h1 e he).2.1),
        Finset.mem_insert_of_mem (Finset.mem_of_mem_erase (h1 e he).2.2)⟩
  · intro e he f hf hnef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (hnef rfl).elim
      · exact apart f hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (apart e he).symm
      · exact h2 e he f hf hnef

private theorem erase_link {v k : ℕ} {S : Finset (Fin v)} {t u : Fin v}
    {Q : Finset (Fin v × Fin v)} (hQ : Q ∈ msets (insert t S) (k+1))
    (he : link t u ∈ Q) : Q.erase (link t u) ∈ msets (S.erase u) k := by
  rcases mem_msets.mp hQ with ⟨h1,h2,h3⟩
  refine mem_msets.mpr ⟨?_, ?_, by rw [Finset.card_erase_of_mem he,h3]; omega⟩
  · intro f hf
    obtain ⟨hfne,hfQ⟩ := Finset.mem_erase.mp hf
    have hd := h2 (link t u) he f hfQ hfne.symm
    rw [Finset.disjoint_left, ends_link] at hd
    have ht : t ∉ ends f := hd (by simp)
    have hu : u ∉ ends f := hd (by simp)
    obtain ⟨ho,hf1,hf2⟩ := h1 f hfQ
    refine ⟨ho, ?_, ?_⟩
    all_goals
      simp only [ends, Finset.mem_insert, Finset.mem_singleton, not_or] at ht hu
      simp only [Finset.mem_erase]
    · exact ⟨Ne.symm hu.1,(Finset.mem_insert.mp hf1).resolve_left (Ne.symm ht.1)⟩
    · exact ⟨Ne.symm hu.2,(Finset.mem_insert.mp hf2).resolve_left (Ne.symm ht.2)⟩
  · exact fun e he f hf => h2 e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf)

private noncomputable def attached {v : ℕ} (S : Finset (Fin v)) (t : Fin v) (k : ℕ)
    (u : Fin v) : Finset (Finset (Fin v × Fin v)) :=
  (msets (S.erase u) k).image (insert (link t u))

private theorem msets_insert {v k : ℕ} {S : Finset (Fin v)} {t : Fin v} (ht : t ∉ S) :
    msets (insert t S) (k+1) = msets S (k+1) ∪ S.biUnion (attached S t k) := by
  classical
  ext Q
  simp only [Finset.mem_union, Finset.mem_biUnion, attached, Finset.mem_image]
  constructor
  · intro hQ
    rcases mem_msets.mp hQ with ⟨h1,h2,h3⟩
    by_cases he : ∃ e ∈ Q, t ∈ ends e
    · obtain ⟨e,heQ,het⟩ := he
      obtain ⟨u,hut,hue,reu⟩ := link_repr (h1 e heQ).1 het
      have hu : u ∈ S := by
        have hh := (h1 e heQ).2
        have hm : u ∈ insert t S := by
          rcases (show u = e.1 ∨ u = e.2 from by simpa [ends] using hue) with rfl | rfl
          · exact hh.1
          · exact hh.2
        exact (Finset.mem_insert.mp hm).resolve_left hut
      have hel : link t u ∈ Q := reu ▸ heQ
      exact Or.inr ⟨u,hu,Q.erase (link t u),erase_link hQ hel,Finset.insert_erase hel⟩
    · push Not at he
      refine Or.inl (mem_msets.mpr ⟨?_,h2,h3⟩)
      intro e heQ
      have h := he e heQ
      simp only [ends, Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact ⟨(h1 e heQ).1,(Finset.mem_insert.mp (h1 e heQ).2.1).resolve_left (Ne.symm h.1),
        (Finset.mem_insert.mp (h1 e heQ).2.2).resolve_left (Ne.symm h.2)⟩
  · rintro (hQ | ⟨u,hu,P,hP,rfl⟩)
    · rcases mem_msets.mp hQ with ⟨h1,h2,h3⟩
      exact mem_msets.mpr ⟨fun e he => ⟨(h1 e he).1,Finset.mem_insert_of_mem (h1 e he).2.1,
        Finset.mem_insert_of_mem (h1 e he).2.2⟩,h2,h3⟩
    · exact (insert_link ht hu hP).2

private theorem coeff_insert {v k : ℕ} {S : Finset (Fin v)} {t : Fin v}
    (ht : t ∉ S) (x : Fin v × Fin v → ℝ) :
    coeff x (insert t S) (k+1) = coeff x S (k+1) +
      ∑ u ∈ S, x (link t u) * coeff x (S.erase u) k := by
  classical
  have hd : Disjoint (msets S (k+1)) (S.biUnion (attached S t k)) := by
    rw [Finset.disjoint_left]
    intro Q hQ ha
    obtain ⟨u,hu,h⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨P,_,rfl⟩ := Finset.mem_image.mp h
    exact avoid_ends hQ ht _ (Finset.mem_insert_self _ _) (by simp [ends_link])
  have hp : (S : Set (Fin v)).PairwiseDisjoint (attached S t k) := by
    intro u hu z hz hne
    change Disjoint (attached S t k u) (attached S t k z)
    rw [Finset.disjoint_left]
    intro Q hQu hQz
    obtain ⟨P,hP,hPu⟩ := Finset.mem_image.mp hQu
    obtain ⟨T,_,hTz⟩ := Finset.mem_image.mp hQz
    have hQ : Q ∈ msets (insert t S) (k+1) := hPu ▸ (insert_link ht hu hP).2
    have h1 : link t u ∈ Q := hPu ▸ Finset.mem_insert_self _ _
    have h2 : link t z ∈ Q := hTz ▸ Finset.mem_insert_self _ _
    have hu' : u ≠ t := fun h => ht (h ▸ hu)
    have hh := (mem_msets.mp hQ).2.1 _ h1 _ h2 (fun he => hne (link_inj hu' he))
    rw [Finset.disjoint_left] at hh
    exact hh (a := t) (by simp [ends_link]) (by simp [ends_link])
  unfold coeff at *
  rw [msets_insert ht, Finset.sum_union hd, Finset.sum_biUnion hp]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  have hinj : Set.InjOn (insert (link t u)) (↑(msets (S.erase u) k) : Set (Finset (Fin v × Fin v))) := by
    intro P hP T hT he
    have hPe := (insert_link ht hu hP).1
    have hTe := (insert_link ht hu hT).1
    have hh := congrArg (fun Q : Finset (Fin v × Fin v) => Q.erase (link t u)) he
    simpa [Finset.erase_insert hPe, Finset.erase_insert hTe] using hh
  rw [attached, Finset.sum_image hinj, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun P hP => Finset.prod_insert (insert_link ht hu hP).1)

private def Inter (A B : ℕ → ℝ) : Prop :=
  (∀ k, B (k+1) * A k ≤ A (k+1) * B k) ∧
  (∀ k, A (k+2) * B k ≤ B (k+1) * A (k+1))

private def LC (A : ℕ → ℝ) : Prop := ∀ k, A k * A (k+2) ≤ A (k+1)^2

private theorem inter_step {v : ℕ} {x : Fin v × Fin v → ℝ} (hx : ∀ e, 0 ≤ x e)
    {S : Finset (Fin v)} {t : Fin v} (ht : t ∉ S)
    (hB : LC (coeff x S)) (hI : ∀ u ∈ S, Inter (coeff x S) (coeff x (S.erase u))) :
    Inter (coeff x (insert t S)) (coeff x S) := by
  constructor
  · intro k
    cases k with
    | zero =>
      rw [coeff_zero, coeff_zero, mul_one, mul_one]
      exact coeff_mono hx (Finset.subset_insert _ _) _
    | succ k =>
      rw [coeff_insert ht x (k := k), coeff_insert ht x (k := k+1),
        mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_comm (coeff x S (k+1+1)) (coeff x S (k+1))]
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro u hu
      have h := mul_le_mul_of_nonneg_left ((hI u hu).2 k) (hx (link t u))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · intro k
    change coeff x (insert t S) ((k+1)+1) * coeff x S k ≤ _
    rw [coeff_insert ht x (k := k+1), coeff_insert ht x (k := k),
      mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    apply add_le_add
    · simpa only [pow_two, mul_comm] using hB k
    · apply Finset.sum_le_sum
      intro u hu
      have h := mul_le_mul_of_nonneg_left ((hI u hu).1 k) (hx (link t u))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h

private theorem lc_step {v : ℕ} {x : Fin v × Fin v → ℝ} (hx : ∀ e, 0 ≤ x e)
    {S : Finset (Fin v)} {t : Fin v} (ht : t ∉ S)
    (h : Inter (coeff x (insert t S)) (coeff x S)) : LC (coeff x (insert t S)) := by
  intro k
  by_cases hp : 0 < coeff x S k
  · apply (mul_le_mul_iff_left₀ hp).mp
    rw [pow_two]
    calc
      _ = coeff x (insert t S) k * (coeff x (insert t S) (k+2) * coeff x S k) := by ring
      _ ≤ coeff x (insert t S) k * (coeff x S (k+1) * coeff x (insert t S) (k+1)) :=
        mul_le_mul_of_nonneg_left (h.2 k) (coeff_nonneg hx _ _)
      _ = (coeff x S (k+1) * coeff x (insert t S) k) * coeff x (insert t S) (k+1) := by ring
      _ ≤ (coeff x (insert t S) (k+1) * coeff x S k) * coeff x (insert t S) (k+1) :=
        mul_le_mul_of_nonneg_right (h.1 k) (coeff_nonneg hx _ _)
      _ = _ := by ring
  · have hz : ∀ j, k ≤ j → coeff x S j = 0 := by
      intro j hkj
      exact le_antisymm (le_of_not_gt (fun hj => hp (coeff_pos_down hx hkj hj))) (coeff_nonneg hx _ _)
    have hA : coeff x (insert t S) (k+2) = 0 := by
      change coeff x (insert t S) ((k+1)+1) = 0
      rw [coeff_insert ht x, hz _ (by omega)]
      have hz' : ∀ u ∈ S, coeff x (S.erase u) (k+1) = 0 := by
        intro u _
        exact le_antisymm ((coeff_mono hx (Finset.erase_subset _ _) _).trans
          (le_of_eq (hz _ (by omega)))) (coeff_nonneg hx _ _)
      rw [Finset.sum_eq_zero (fun u hu => by rw [hz' u hu, mul_zero]), add_zero]
    rw [hA,mul_zero]
    positivity

private theorem coeff_theory {v : ℕ} {x : Fin v × Fin v → ℝ} (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin v)) : LC (coeff x S) ∧ ∀ t ∈ S, Inter (coeff x S) (coeff x (S.erase t)) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have del : ∀ t ∈ S, Inter (coeff x S) (coeff x (S.erase t)) := by
      intro t ht
      have hsub : S.erase t ⊂ S := Finset.erase_ssubset ht
      have hh := ih (S.erase t) hsub
      have hnew := inter_step hx (Finset.notMem_erase t S) hh.1 hh.2
      rwa [Finset.insert_erase ht] at hnew
    refine ⟨?_,del⟩
    by_cases hs : S.Nonempty
    · obtain ⟨t,ht⟩ := hs
      have hi : Inter (coeff x (insert t (S.erase t))) (coeff x (S.erase t)) := by
        rw [Finset.insert_erase ht]
        exact del t ht
      have hh := lc_step hx (Finset.notMem_erase t S) hi
      rwa [Finset.insert_erase ht] at hh
    · have hem := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      intro k
      have hz : msets (∅ : Finset (Fin v)) (k+2) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro Q hQ
        rcases mem_msets.mp hQ with ⟨h1,_,h3⟩
        rcases Q.eq_empty_or_nonempty with he | ⟨e,he⟩
        · simp [he] at h3
        · simpa using (h1 e he).2.1
      simp only [coeff, hz, Finset.sum_empty, mul_zero]
      positivity

private theorem bounds_card {v j : ℕ} {S : Finset (Fin v)}
    {Q : Finset (Fin v × Fin v)} (hQ : Q ∈ msets S j) : Q.card = j :=
  (Finset.mem_filter.mp hQ).2.2

private theorem bounds_erase {v j : ℕ} {S : Finset (Fin v)}
    {Q : Finset (Fin v × Fin v)} {e : Fin v × Fin v}
    (hQ : Q ∈ msets S j) (he : e ∈ Q) : Q.erase e ∈ msets S (j - 1) := by
  unfold msets at hQ ⊢
  obtain ⟨hsub, hd, hj⟩ := Finset.mem_filter.mp hQ
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
  · exact (Finset.erase_subset e Q).trans (Finset.mem_powerset.mp hsub)
  · intro a ha b hb hab
    exact hd a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hab
  · rw [Finset.card_erase_of_mem he, hj]

/-- Deleting a chosen edge embeds the matchings into smaller matchings paired with edges. -/
private theorem bounds_coeff_step {v r : ℕ} {x : Fin v × Fin v → ℝ} (S : Finset (Fin v))
    (hx : ∀ e, 0 ≤ x e) (h5 : ∀ e, x e ≤ 5) (hr : 0 < r) :
    coeff x S r ≤ (5 * (v : ℝ)^2) * coeff x S (r - 1) := by
  classical
  by_cases h : (msets S r).Nonempty
  · have hn (Q : Finset (Fin v × Fin v)) (hQ : Q ∈ msets S r) : Q.Nonempty :=
      Finset.card_pos.mp ((bounds_card hQ).symm ▸ hr)
    obtain ⟨Q₀, hQ₀⟩ := h
    obtain ⟨e₀, _⟩ := hn Q₀ hQ₀
    let edge (Q : Finset (Fin v × Fin v)) : Fin v × Fin v :=
      if hQ : Q.Nonempty then Classical.choose hQ else e₀
    have hedge (Q : Finset (Fin v × Fin v)) (hQ : Q ∈ msets S r) : edge Q ∈ Q := by
      simp only [edge, dite_eq_left (hn Q hQ)]
      exact Classical.choose_spec (hn Q hQ)
    let drop (Q : Finset (Fin v × Fin v)) : Finset (Fin v × Fin v) × (Fin v × Fin v) :=
      (Q.erase (edge Q), edge Q)
    calc
      coeff x S r ≤ ((msets S (r - 1)).product (Finset.univ : Finset (Fin v × Fin v))).sum
          (fun p => p.1.prod x * 5) := by
        unfold coeff
        refine Finset.sum_le_sum_of_injOn drop ?_ ?_ ?_ ?_
        · intro Q hQ T hT hQT
          change Q ∈ msets S r at hQ
          change T ∈ msets S r at hT
          have hEq := congrArg (fun p : Finset (Fin v × Fin v) × (Fin v × Fin v) =>
            insert p.2 p.1) hQT
          simpa only [drop, Finset.insert_erase (hedge Q hQ), Finset.insert_erase (hedge T hT)]
            using hEq
        · rintro p hp
          obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_product.mpr ⟨bounds_erase hQ (hedge Q hQ), Finset.mem_univ _⟩
        · intro Q hQ
          change Q.prod x ≤ (Q.erase (edge Q)).prod x * 5
          calc
            Q.prod x = (Q.erase (edge Q)).prod x * x (edge Q) :=
              (Finset.prod_erase_mul Q x (hedge Q hQ)).symm
            _ ≤ (Q.erase (edge Q)).prod x * 5 :=
              mul_le_mul_of_nonneg_left (h5 _) (Finset.prod_nonneg fun e _ => hx e)
        · intro p _ _
          exact mul_nonneg (Finset.prod_nonneg fun e _ => hx e) (by norm_num)
      _ = (5 * (v : ℝ)^2) * coeff x S (r - 1) := by
        unfold coeff
        change (∑ p ∈ msets S (r-1) ×ˢ (Finset.univ : Finset (Fin v × Fin v)), p.1.prod x * 5) = _
        rw [Finset.sum_product' (msets S (r-1)) (Finset.univ : Finset (Fin v × Fin v))
          (fun Q _ => Q.prod x * 5), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Q _
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul]
        ring
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
    have hZero : coeff x S r = 0 := by simp [coeff, hEmpty]
    rw [hZero]
    exact mul_nonneg (by positivity) (coeff_nonneg hx S (r - 1))

private theorem bounds_ratio_lower {n v r : ℕ} {x : Fin v × Fin v → ℝ} (S : Finset (Fin v))
    (hn : 0 < n) (hv : v ≤ n) (hx : ∀ e, 0 ≤ x e) (h5 : ∀ e, x e ≤ 5)
    (hr : 0 < r) (hpos : 0 < coeff x S r) :
    1 / (5 * (n : ℝ)^2) ≤ coeff x S (r - 1) / coeff x S r := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv' : (v : ℝ) ≤ (n : ℝ) := by exact_mod_cast hv
  have hbase : (5 : ℝ) * (v : ℝ)^2 ≤ 5 * (n : ℝ)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hv' 2) (by norm_num)
  apply (div_le_div_iff₀ (by positivity) hpos).2
  rw [one_mul, mul_comm (coeff x S (r - 1))]
  exact (bounds_coeff_step S hx h5 hr).trans
    (mul_le_mul_of_nonneg_right hbase (coeff_nonneg hx S (r - 1)))

private theorem bounds_coeff_upper {n v : ℕ} {x : Fin v × Fin v → ℝ} (S : Finset (Fin v))
    (hv : v ≤ n) (hx : ∀ e, 0 ≤ x e) (h5 : ∀ e, x e ≤ 5) (k : ℕ) :
    coeff x S k ≤ (5 * ((n : ℝ) + 1)^2)^k := by
  have hv' : (v : ℝ) ≤ (n : ℝ) := by exact_mod_cast hv
  have hbase : (5 : ℝ) * (v : ℝ)^2 ≤ 5 * ((n : ℝ) + 1)^2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  induction k with
  | zero => simp [coeff_zero]
  | succ k ih =>
    rw [pow_succ']
    have hstep := bounds_coeff_step S hx h5 (Nat.succ_pos k)
    rw [Nat.succ_sub_one] at hstep
    exact hstep.trans (mul_le_mul hbase ih (coeff_nonneg hx S k) (by positivity))

private theorem bounds_coeff_lower {n v ν : ℕ} {x : Fin v × Fin v → ℝ} (S : Finset (Fin v))
    (hx : ∀ e, 0 ≤ x e) (hmin : ∀ e, 0 < x e → 1 / (n : ℝ)^2 ≤ x e)
    (hpos : 0 < coeff x S ν) : (1 / (n : ℝ)^2)^ν ≤ coeff x S ν := by
  have hne : (msets S ν).sum (fun Q => Q.prod x) ≠ 0 := ne_of_gt hpos
  obtain ⟨Q, hQ, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hwt : ∀ e ∈ Q, 0 < x e := fun e he =>
    lt_of_le_of_ne (hx e) ((Finset.prod_ne_zero_iff.mp hprod e he).symm)
  calc
    (1 / (n : ℝ)^2)^ν = ∏ _e ∈ Q, (1 / (n : ℝ)^2) := by
      rw [Finset.prod_const, bounds_card hQ]
    _ ≤ Q.prod x := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun e he => hmin e (hwt e he))
    _ ≤ coeff x S ν := Finset.single_le_sum (fun _ _ => Finset.prod_nonneg fun e _ => hx e) hQ

/-- The exact adjacent ratio makes both neighboring coefficients modes. Log-concavity
propagates the two slope inequalities across the positive support; the zero tail
cannot create a bigger value. -/
private theorem weighted_tilt_exact_mode (b : ℕ → ℝ) (ν r : ℕ)
    (hr : 1 ≤ r) (hrν : r ≤ ν)
    (hpos : ∀ j ≤ ν, 0 < b j) (hzero : ∀ j, ν < j → b j = 0)
    (hlc : ∀ j, b j * b (j + 2) ≤ (b (j + 1)) ^ 2) :
    let R := b (r - 1) / b r
    ∀ j, b j * R ^ j ≤ b (r - 1) * R ^ (r - 1) ∧
      b j * R ^ j ≤ b r * R ^ r := by
  let R := b (r - 1) / b r
  let t (j : ℕ) := b j * R ^ j
  change ∀ j, t j ≤ t (r - 1) ∧ t j ≤ t r
  have hR : 0 < R := div_pos (hpos _ (by omega)) (hpos _ hrν)
  have htpos (j : ℕ) (hj : j ≤ ν) : 0 < t j := mul_pos (hpos j hj) (pow_pos hR _)
  have htzero (j : ℕ) (hj : ν < j) : t j = 0 := by simp [t, hzero j hj]
  have htnonneg (j : ℕ) : 0 ≤ t j := by
    by_cases hj : j ≤ ν
    · exact (htpos j hj).le
    · rw [htzero j (by omega)]
  have htlc (j : ℕ) : t j * t (j + 2) ≤ (t (j + 1)) ^ 2 := by
    calc
      t j * t (j + 2) = (b j * b (j + 2)) * (R ^ j * R ^ (j + 2)) := by
        dsimp [t]
        ring
      _ ≤ (b (j + 1)) ^ 2 * (R ^ j * R ^ (j + 2)) :=
        mul_le_mul_of_nonneg_right (hlc j) (mul_nonneg (pow_nonneg hR.le _) (pow_nonneg hR.le _))
      _ = (t (j + 1)) ^ 2 := by
        change _ = (b (j + 1) * R ^ (j + 1)) ^ 2
        rw [show j + 2 = (j + 1) + 1 by omega, pow_succ R (j + 1), pow_succ R j]
        ring
  have hrstep : r - 1 + 1 = r := by omega
  have hcancel : R * b r = b (r - 1) := div_mul_cancel₀ _ (hpos _ hrν).ne'
  have hstep : t (r - 1) = t r := by
    calc
      t (r - 1) = (R * b r) * R ^ (r - 1) := by simp only [t, hcancel]
      _ = b r * R ^ (r - 1 + 1) := by rw [pow_succ]; ring
      _ = t r := by simp only [t, hrstep]
  have hleftStep : ∀ k j : ℕ, j + k = r - 1 → t j ≤ t (j + 1) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have he : j = r - 1 := by omega
      rw [he, hrstep, hstep]
    | succ k ih =>
      intro j hj
      have hnext := ih (j + 1) (by omega)
      by_contra! h
      exact (not_lt_of_ge (htlc j)) (calc
        (t (j + 1)) ^ 2 = t (j + 1) * t (j + 1) := pow_two _
        _ < t j * t (j + 1) := mul_lt_mul_of_pos_right h (htpos _ (by omega))
        _ ≤ t j * t (j + 2) := mul_le_mul_of_nonneg_left hnext (htnonneg _))
  have hleft : ∀ k ≤ r - 1, ∀ j ≤ k, t j ≤ t k := by
    intro k
    induction k with
    | zero =>
      intro _ j hj
      have he : j = 0 := by omega
      rw [he]
    | succ k ih =>
      intro hk j hj
      by_cases he : j = k + 1
      · rw [he]
      · exact (ih (by omega) j (by omega)).trans
          (hleftStep (r - 1 - k) k (by omega))
  have hrightStep : ∀ k, t (r - 1 + k + 1) ≤ t (r - 1 + k) := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero, hrstep, hstep, le_refl]
    | succ k ih =>
      let j := r - 1 + k
      change t (j + 2) ≤ t (j + 1)
      change t (j + 1) ≤ t j at ih
      by_cases hj : j + 2 ≤ ν
      · by_contra! h
        exact (not_lt_of_ge (htlc j)) (calc
          (t (j + 1)) ^ 2 = t (j + 1) * t (j + 1) := pow_two _
          _ < t (j + 1) * t (j + 2) := mul_lt_mul_of_pos_left h (htpos _ (by omega))
          _ ≤ t j * t (j + 2) := mul_le_mul_of_nonneg_right ih (htnonneg _))
      · rw [htzero (j + 2) (by omega)]
        exact htnonneg _
  have hright : AntitoneOn t {j : ℕ | r - 1 ≤ j} := by
    apply antitoneOn_nat_Ici_of_succ_le
    intro j hj
    have he : r - 1 + (j - (r - 1)) = j := by omega
    simpa only [he] using hrightStep (j - (r - 1))
  intro j
  have hj : t j ≤ t (r - 1) := by
    by_cases h : j ≤ r - 1
    · exact hleft _ le_rfl j h
    · have hh : r - 1 ≤ j := by omega
      exact hright (show r - 1 ≤ r - 1 from le_rfl) hh hh
  exact ⟨hj, hj.trans_eq hstep⟩

/-- Round upward without losing either modal lower bound. The size inequality
`5 * n^2 * (n + 1) ≤ D` and the lower ratio bound imply `n + 1 ≤ D * R`, so
the ceiling error of at most one gives `R ≤ p / D ≤ R * (1 + 1 / (n + 1))`.
Because `D*K` is an integer, `R ≤ K` gives `p ≤ D*K`. For `j ≤ v ≤ n`, the
termwise inflation is at most `exp (j / (n + 1)) ≤ exp 1 < 3`. -/
private theorem weighted_tilt_round (b : ℕ → ℝ) (n v r D K : ℕ) (R : ℝ)
    (hn : 2 ≤ n) (hv : v ≤ n) (hrv : r ≤ v) (hD : D = 10 * (n + 1) ^ 4)
    (hb : ∀ j, 0 ≤ b j)
    (hlo : 1 / (5 * (n : ℝ) ^ 2) ≤ R) (hhi : R ≤ (K : ℝ))
    (hmode : ∀ j ≤ v, b j * R ^ j ≤ b (r - 1) * R ^ (r - 1) ∧ b j * R ^ j ≤ b r * R ^ r) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ D * K ∧
      let mass (j : ℕ) := b j * (p : ℝ) ^ j * (D : ℝ) ^ (v - j)
      (Finset.range (v + 1)).sum mass ≤ (3 * ((v : ℝ) + 1)) * min (mass (r - 1)) (mass r) := by
  let d : ℝ := D
  let p := Nat.ceil (d * R)
  let s : ℝ := (p : ℝ) / d
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  let u : ℝ := 1 + δ
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hden : 0 < 5 * (n : ℝ) ^ 2 := by positivity
  have hdcast : d = 10 * ((n : ℝ) + 1) ^ 4 := by
    dsimp [d]
    rw [hD]
    push_cast
    rfl
  have hdpos : 0 < d := by rw [hdcast]; positivity
  have hR : 0 < R := (one_div_pos.mpr hden).trans_le hlo
  have hp1 : 1 ≤ p := Nat.ceil_pos.mpr (mul_pos hdpos hR)
  have hpK : p ≤ D * K := by
    apply Nat.ceil_le.mpr
    push_cast
    exact mul_le_mul_of_nonneg_left hhi hdpos.le
  have hlarge : (n : ℝ) + 1 ≤ d * R := by
    calc
      (n : ℝ) + 1 ≤ d * (1 / (5 * (n : ℝ) ^ 2)) := by
        rw [hdcast, ← mul_div_assoc, le_div_iff₀ hden]
        nlinarith only [hnpos.le, pow_nonneg hnpos.le 2, pow_nonneg hnpos.le 3,
          pow_nonneg hnpos.le 4]
      _ ≤ d * R := mul_le_mul_of_nonneg_left hlo hdpos.le
  have hceilLo : d * R ≤ (p : ℝ) := Nat.le_ceil _
  have hceilHi : (p : ℝ) ≤ d * R + 1 := (Nat.ceil_lt_add_one (mul_pos hdpos hR).le).le
  have hsLo : R ≤ s := by
    apply (le_div_iff₀ hdpos).2
    simpa only [mul_comm R d] using hceilLo
  have hsHi : s ≤ R * u := by
    apply (div_le_iff₀ hdpos).2
    have hδ : 1 ≤ d * R * δ := by
      dsimp [δ]
      rw [← mul_div_assoc, le_div_iff₀ hn1, one_mul, mul_one]
      exact hlarge
    calc
      (p : ℝ) ≤ d * R + 1 := hceilHi
      _ ≤ d * R + d * R * δ := add_le_add_right hδ _
      _ = R * u * d := by dsimp [u]; ring
  have hpEq : (p : ℝ) = d * s := by
    dsimp [s]
    rw [← mul_div_assoc, mul_comm d (p : ℝ), mul_div_cancel_right₀ _ hdpos.ne']
  have hu : 0 ≤ u := by dsimp [u, δ]; positivity
  have hpower (j : ℕ) (hj : j ≤ n) : u ^ j ≤ 3 := by
    have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    have harg : (j : ℝ) * δ ≤ 1 := by
      dsimp [δ]
      rw [← mul_div_assoc, div_le_iff₀ hn1, mul_one, one_mul]
      linarith only [hjR]
    calc
      u ^ j ≤ (Real.exp δ) ^ j := pow_le_pow_left₀ hu
        (by simpa only [u, add_comm] using Real.add_one_le_exp δ) j
      _ = Real.exp ((j : ℝ) * δ) := (Real.exp_nat_mul δ j).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr harg
      _ ≤ 3 := Real.exp_one_lt_three.le
  let mass (j : ℕ) := b j * (p : ℝ) ^ j * d ^ (v - j)
  have hfactor (j : ℕ) (hj : j ≤ v) : mass j = (b j * s ^ j) * d ^ v := by
    calc
      mass j = (b j * s ^ j) * (d ^ j * d ^ (v - j)) := by
        dsimp [mass]
        rw [hpEq, mul_pow]
        ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hcompare (j k : ℕ) (hj : j ≤ v) (hk : k ≤ v)
      (hjk : b j * R ^ j ≤ b k * R ^ k) : mass j ≤ 3 * mass k := by
    have htilt : b j * s ^ j ≤ 3 * (b k * s ^ k) := by
      calc
        b j * s ^ j ≤ b j * (R * u) ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hR.le.trans hsLo) hsHi _) (hb _)
        _ = (b j * R ^ j) * u ^ j := by rw [mul_pow, mul_assoc]
        _ ≤ (b j * R ^ j) * 3 :=
          mul_le_mul_of_nonneg_left (hpower j (hj.trans hv)) (mul_nonneg (hb _) (pow_nonneg hR.le _))
        _ ≤ (b k * R ^ k) * 3 := mul_le_mul_of_nonneg_right hjk (by norm_num)
        _ ≤ (b k * s ^ k) * 3 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hsLo _) (hb _)) (by norm_num)
        _ = 3 * (b k * s ^ k) := mul_comm _ _
    rw [hfactor j hj, hfactor k hk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right htilt (pow_nonneg hdpos.le _)
  have hterm (j : ℕ) (hj : j ≤ v) : mass j ≤ 3 * min (mass (r - 1)) (mass r) := by
    rcases hmode j hj with ⟨hleft, hright⟩
    rcases le_total (mass (r - 1)) (mass r) with hh | hh
    · rw [min_eq_left hh]
      exact hcompare j (r - 1) hj (by omega) hleft
    · rw [min_eq_right hh]
      exact hcompare j r hj hrv hright
  refine ⟨p, hp1, hpK, ?_⟩
  change (Finset.range (v + 1)).sum mass ≤ (3 * ((v : ℝ) + 1)) * min (mass (r - 1)) (mass r)
  calc
    _ ≤ (Finset.range (v + 1)).sum (fun _ => 3 * min (mass (r - 1)) (mass r)) :=
      Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range_succ_iff.mp hj))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]; ring

/-- Weighted tilt at the adjacent ratio for a log-concave sequence. -/
private theorem weighted_tilt (b : ℕ → ℝ) (n v ν r D K : ℕ)
    (hn : 2 ≤ n) (hv : v ≤ n) (hνv : ν ≤ v) (hr : 1 ≤ r) (hrν : r ≤ ν)
    (hD : D = 10 * (n + 1) ^ 4)
    (hpos : ∀ j ≤ ν, 0 < b j) (hzero : ∀ j, ν < j → b j = 0)
    (hlc : ∀ j, b j * b (j + 2) ≤ (b (j + 1)) ^ 2)
    (hlo : 1 / (5 * (n : ℝ) ^ 2) ≤ b (r - 1) / b r)
    (hhi : b (r - 1) / b r ≤ (K : ℝ)) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ D * K ∧
      let mass (j : ℕ) := b j * (p : ℝ) ^ j * (D : ℝ) ^ (v - j)
      (Finset.range (v + 1)).sum mass ≤ (3 * ((v : ℝ) + 1)) * min (mass (r - 1)) (mass r) := by
  have hb (j : ℕ) : 0 ≤ b j := by
    by_cases hj : j ≤ ν
    · exact (hpos j hj).le
    · rw [hzero j (by omega)]
  exact weighted_tilt_round b n v r D K _ hn hv (hrν.trans hνv) hD hb hlo hhi
    (fun j _ => weighted_tilt_exact_mode b ν r hr hrν hpos hzero hlc j)

private theorem coeff_support_card {v j : ℕ} {x : Fin v × Fin v → ℝ}
    {S : Finset (Fin v)} (hp : 0 < coeff x S j) : j ≤ v := by
  classical
  obtain ⟨Q,hQ,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hp)
  rcases mem_msets.mp hQ with ⟨_,hd,hc⟩
  have hinj : Set.InjOn (Prod.fst : Fin v × Fin v → Fin v) Q := by
    intro e he f hf hef
    by_contra hn
    have hd' := hd e he f hf hn
    rw [Finset.disjoint_left] at hd'
    exact hd' (a := e.1) (by simp [ends]) (by simp [ends, hef])
  calc
    j = Q.card := hc.symm
    _ = (Q.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ v := by simpa using (Finset.card_le_univ (Q.image Prod.fst))

private theorem ratio_gap {n r ν g : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hrν : r ≤ ν)
    (hgap : ν ≤ g*(ν-r)) {R bs bv : ℝ} (hR : 0 < R)
    (hmode : bv*R^ν ≤ bs*R^(r-1))
    (hbs : bs ≤ (5*((n : ℝ)+1)^2)^(r-1))
    (hbv : (1/(n : ℝ)^2)^ν ≤ bv) : R ≤ ((5*((n : ℝ)+1)^4)^(g+1)) := by
  let C : ℝ := 5*((n : ℝ)+1)^2
  let N : ℝ := ((n : ℝ)+1)^2
  let B : ℝ := 5*((n : ℝ)+1)^4
  let d := ν-(r-1)
  have hd : r-1+d=ν := by dsimp [d]; omega
  have hd₀ : d ≠ 0 := by dsimp [d]; omega
  have hsplit : R^ν = R^d * R^(r-1) := by rw [← hd, pow_add, mul_comm]
  have hmul : bv*R^d ≤ bs := by
    apply (mul_le_mul_iff_left₀ (pow_pos hR (r-1))).mp
    simpa only [hsplit, mul_assoc] using hmode
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hB : 1 ≤ B := by
    have hCN : C*N = B := by dsimp [C,N,B]; ring
    rw [← hCN]
    exact one_le_mul_of_one_le_of_one_le hC (by dsimp [N]; nlinarith)
  have hlow : (1/N)^ν ≤ bv := by
    apply le_trans _ hbv
    apply pow_le_pow_left₀ (by positivity)
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (show 0 ≤ (n : ℝ) by positivity) (show (n : ℝ) ≤ (n : ℝ)+1 by linarith) 2)
  have hlim : (1/N)^ν * R^d ≤ C^ν :=
    (mul_le_mul_of_nonneg_right hlow (by positivity)).trans
      (hmul.trans (hbs.trans (pow_right_mono₀ hC (by omega))))
  have hpower : R^d ≤ B^ν := by
    calc
      _ = ((1/N)^ν*R^d)*N^ν := by
        rw [mul_comm ((1/N)^ν) (R^d), mul_assoc, ← mul_pow, one_div_mul_cancel (ne_of_gt hN), one_pow, mul_one]
      _ ≤ C^ν*N^ν := mul_le_mul_of_nonneg_right hlim (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; dsimp [C,N,B]; ring
  have he : ν ≤ (g+1)*d := by
    apply hgap.trans
    calc
      _ ≤ g*d := Nat.mul_le_mul_left g (by dsimp [d]; omega)
      _ ≤ _ := Nat.mul_le_mul_right d (by omega)
  have hpow : R^d ≤ (B^(g+1))^d := by
    rw [← pow_mul]
    exact hpower.trans (pow_right_mono₀ hB he)
  exact le_of_pow_le_pow_left₀ hd₀ (by positivity) hpow

private noncomputable def activity {v : ℕ} (a : Fin v → ℕ) (w : Fin v → Fin v → ℕ)
    (e : Fin v × Fin v) : ℝ :=
  (w e.1 e.2 : ℝ) / ((a e.1 : ℝ)*(a e.2 : ℝ))

private noncomputable def monomers {v : ℕ} (a : Fin v → ℕ) : ℝ :=
  ∏ i : Fin v, (a i : ℝ)

private theorem monomers_pos {v : ℕ} {a : Fin v → ℕ} (ha : ∀ i, 1 ≤ a i) :
    0 < monomers a := by
  exact Finset.prod_pos (fun i _ => by exact_mod_cast (show 0 < a i from ha i))

private theorem activity_bounds {n v : ℕ} {a : Fin v → ℕ} {w : Fin v → Fin v → ℕ}
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ n) (hw : ∀ i j, w i j ≤ 5*a i*a j) :
    (∀ e, 0 ≤ activity a w e) ∧ (∀ e, activity a w e ≤ 5) ∧
    (∀ e, 0 < activity a w e → 1/(n : ℝ)^2 ≤ activity a w e) := by
  have hap : ∀ i, 0 < (a i : ℝ) := fun i => by exact_mod_cast (show 0 < a i from (ha i).1)
  have hau : ∀ i, (a i : ℝ) ≤ n := fun i => by exact_mod_cast (ha i).2
  refine ⟨fun e => div_nonneg (by positivity) (by positivity), ?_, ?_⟩
  · intro e
    apply (div_le_iff₀ (mul_pos (hap e.1) (hap e.2))).2
    have h : (w e.1 e.2 : ℝ) ≤ 5*(a e.1 : ℝ)*(a e.2 : ℝ) := by exact_mod_cast hw e.1 e.2
    simpa only [mul_assoc] using h
  · intro e hp
    have hwp : (0 : ℝ) < w e.1 e.2 := (div_pos_iff_of_pos_right (mul_pos (hap e.1) (hap e.2))).mp hp
    have hw1 : (1 : ℝ) ≤ w e.1 e.2 := by
      exact_mod_cast (show 1 ≤ w e.1 e.2 from by exact_mod_cast hwp)
    have hnn : 0 ≤ (n : ℝ) := by positivity
    have hnpos : 0 < (n : ℝ) := (hap e.1).trans_le (hau e.1)
    have hda : (a e.1 : ℝ)*(a e.2 : ℝ) ≤ (n : ℝ)^2 := by
      simpa [pow_two] using mul_le_mul (hau e.1) (hau e.2) (hap e.2).le hnn
    calc
      _ ≤ 1 / ((a e.1 : ℝ)*(a e.2 : ℝ)) := one_div_le_one_div_of_le (mul_pos (hap e.1) (hap e.2)) hda
      _ ≤ _ := div_le_div_of_nonneg_right hw1 (by positivity)

private def rawSets (v j : ℕ) : Finset (Finset (Fin v × Fin v)) :=
  let edges := (Finset.univ : Finset (Fin v × Fin v)).filter (fun z => z.1 < z.2)
  let matchings := edges.powerset.filter (fun Q =>
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f))
  matchings.filter (fun Q => Q.card = j)

private def rawCoeff {v : ℕ} (a : Fin v → ℕ) (w : Fin v → Fin v → ℕ) (j : ℕ) : ℕ :=
  (rawSets v j).sum (fun Q => ((Finset.univ \ Q.biUnion ends).prod a) * Q.prod (fun z => w z.1 z.2))

private theorem rawCoeff_eq {v : ℕ} (a : Fin v → ℕ) (w : Fin v → Fin v → ℕ)
    (ha : ∀ i, 1 ≤ a i) (j : ℕ) :
    (rawCoeff a w j : ℝ) = monomers a * coeff (activity a w) Finset.univ j := by
  classical
  have hsets : rawSets v j = msets Finset.univ j := by
    ext Q
    simp [rawSets, mem_msets, Finset.subset_iff, and_assoc]
  unfold rawCoeff
  rw [hsets, Nat.cast_sum, coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rcases mem_msets.mp hQ with ⟨hor,hd,_⟩
  let A := fun i : Fin v => (a i : ℝ)
  have hcover : (∏ i ∈ Q.biUnion ends, A i) = ∏ e ∈ Q, A e.1 * A e.2 := by
    rw [Finset.prod_biUnion (show (Q : Set (Fin v × Fin v)).PairwiseDisjoint ends from hd)]
    apply Finset.prod_congr rfl
    intro e he
    simp [ends, Finset.prod_insert, (hor e he).1.ne]
  have hsplit : (∏ i ∈ Finset.univ \ Q.biUnion ends, A i) * (∏ e ∈ Q, A e.1*A e.2) =
      monomers a := by
    rw [← hcover]
    exact Finset.prod_sdiff (Finset.subset_univ _)
  have hden : (∏ e ∈ Q, A e.1*A e.2) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro e _
    change 0 < (a e.1 : ℝ) * (a e.2 : ℝ)
    exact mul_pos (by exact_mod_cast (show 0 < a e.1 from ha e.1))
      (by exact_mod_cast (show 0 < a e.2 from ha e.2))
  push_cast
  change (∏ i ∈ Finset.univ \ Q.biUnion ends, A i) * (∏ e ∈ Q, (w e.1 e.2 : ℝ)) =
    monomers a * (∏ e ∈ Q, (w e.1 e.2 : ℝ) / (A e.1*A e.2))
  rw [Finset.prod_div_distrib, ← hsplit]
  field_simp

end PEqualNP.Outside.L_lib_970_aux

open PEqualNP.Outside.L_lib_970_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_lib_970 :
  ∀ (n v g : Nat), 2 ≤ n → v ≤ n → 1 ≤ g →
    ∀ (a : Fin v → Nat) (w : Fin v → Fin v → Nat),
    (∀ i, 1 ≤ a i ∧ a i ≤ n) →
    (∀ i, w i i = 0) → (∀ i j, w i j = w j i ∧ w i j ≤ 5*a i*a j) →
    let edges := (Finset.univ : Finset (Fin v × Fin v)).filter (fun z => z.1 < z.2)
    let verts := fun z : Fin v × Fin v => ({z.1,z.2} : Finset (Fin v))
    let matchings := edges.powerset.filter (fun Q =>
      ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (verts e) (verts f))
    let c := fun j : Nat => (matchings.filter (fun Q => Q.card = j)).sum (fun Q =>
      ((Finset.univ \ Q.biUnion verts).prod a) * Q.prod (fun z => w z.1 z.2))
    let D := 10*(n+1)^4
    let K := (5*(n+1)^4)^(g+1)
    ∀ ν r : Nat, 0 < c ν → (∀ j, 0 < c j → j ≤ ν) → 1 ≤ r → r ≤ ν →
      (ν ≤ g*(ν-r) ∨ c (r-1) ≤ K*c r) →
      ∃ p : Nat, 1 ≤ p ∧ p ≤ D*K ∧
        let mass := fun j : Nat => c j*p^j*D^(v-j)
        (Finset.range (v+1)).sum mass ≤ 3*(v+1)*min (mass (r-1)) (mass r) := by
  classical
  intro n v g hn hv _ a w ha _ hw edges verts matchings c D K ν r hν hmax hr hrν hcase
  let x := activity a w
  let A := monomers a
  let b := coeff x (Finset.univ : Finset (Fin v))
  let q : ℕ → ℝ := fun j => (c j : ℝ)
  have hA : 0 < A := monomers_pos (fun i => (ha i).1)
  have hq : ∀ j, q j = A*b j := rawCoeff_eq a w (fun i => (ha i).1)
  obtain ⟨hx,h5,hmin⟩ := activity_bounds ha (fun i j => (hw i j).2)
  have hνq : 0 < q ν := by
    change 0 < (c ν : ℝ)
    exact_mod_cast hν
  have hνb : 0 < b ν := by rw [hq] at hνq; exact (mul_pos_iff_of_pos_left hA).mp hνq
  have hνv := coeff_support_card hνb
  have hbpos : ∀ k ≤ ν, 0 < b k := fun k hk => coeff_pos_down hx hk hνb
  have hqpos : ∀ k ≤ ν, 0 < q k := fun k hk => by rw [hq]; exact mul_pos hA (hbpos k hk)
  have hqzero : ∀ k, ν < k → q k = 0 := by
    intro k hk
    have hz : c k = 0 := Nat.eq_zero_of_not_pos fun hp => (not_le_of_gt hk) (hmax k hp)
    change (c k : ℝ) = 0
    simp [hz]
  have hblc : LC b := (coeff_theory hx Finset.univ).1
  have hqlc : ∀ k, q k*q (k+2) ≤ (q (k+1))^2 := by
    intro k
    simp only [hq]
    calc
      _ = A^2 * (b k*b (k+2)) := by ring
      _ ≤ A^2 * (b (k+1))^2 := mul_le_mul_of_nonneg_left (hblc k) (by positivity)
      _ = _ := by ring
  have hbzero : ∀ k, ν < k → b k = 0 := by
    intro k hk
    have h := hqzero k hk
    rw [hq] at h
    exact (mul_eq_zero.mp h).resolve_left hA.ne'
  have hbr := hbpos r hrν
  have hrR : q (r-1)/q r = b (r-1)/b r := by
    rw [hq, hq]
    field_simp [hA.ne', hbr.ne']
  have hlo : 1/(5*(n : ℝ)^2) ≤ q (r-1)/q r := by
    rw [hrR]
    exact bounds_ratio_lower Finset.univ (by omega) hv hx h5 (by omega) hbr
  have hhi : q (r-1)/q r ≤ (K : ℝ) := by
    rcases hcase with hgap | hsmall
    · rw [hrR]
      have hR : 0 < b (r-1)/b r := div_pos (hbpos _ (by omega)) hbr
      have hm := (weighted_tilt_exact_mode b ν r hr hrν hbpos hbzero hblc ν).1
      have hb₁ := bounds_coeff_upper Finset.univ hv hx h5 (r-1)
      have hb₂ := bounds_coeff_lower Finset.univ hx hmin hνb
      have hm' := ratio_gap (by omega : 1 ≤ n) hr hrν hgap hR hm hb₁ hb₂
      dsimp [K]
      push_cast
      exact hm'
    · apply (div_le_iff₀ (hqpos r hrν)).2
      change (c (r-1) : ℝ) ≤ (K : ℝ) * (c r : ℝ)
      exact_mod_cast hsmall
  obtain ⟨p,hp,hpK,ht⟩ := weighted_tilt q n v ν r D K hn hv hνv hr hrν rfl hqpos hqzero hqlc hlo hhi
  refine ⟨p,hp,hpK,?_⟩
  let m := fun j : ℕ => c j*p^j*D^(v-j)
  change (Finset.range (v+1)).sum m ≤ 3*(v+1)*min (m (r-1)) (m r)
  have hm (j : ℕ) : (m j : ℝ) = q j * (p : ℝ)^j * (D : ℝ)^(v-j) := by
    simp only [m,q,Nat.cast_mul,Nat.cast_pow]
  have ht' : (((Finset.range (v+1)).sum m : ℕ) : ℝ) ≤
      ((3*(v+1)*min (m (r-1)) (m r) : ℕ) : ℝ) := by
    simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_min,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hm]
    exact ht
  exact_mod_cast ht'
