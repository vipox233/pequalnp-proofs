import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1143 : (∀ (n t : Nat), 0 < n →
  ∀ (A B : Finset (Fin n) → Nat) (scope : Fin t → Finset (Fin n)),
  let cube := (Finset.univ : Finset (Finset (Fin n)))
  let diff := fun (x : Finset (Fin n)) => (A x : Int) - (B x : Int)
  let delta := diff ∅
  let pinnedAt := fun (S z x : Finset (Fin n)) => x ∩ S = z
  (∀ S : Finset (Fin n), S ≠ Finset.univ → ∀ z ⊆ S,
    (cube.filter (pinnedAt S z)).sum diff = 0) → delta ≠ 0 →
  (∀ j : Fin n, ∃ i : Fin t, j ∈ scope i) →
  (∀ i : Fin t, ∃ j ∈ scope i, ∀ h : Fin t, j ∈ scope h → h = i) →
  let choices := ((Finset.univ : Finset (Fin t → Finset (Fin n)))).filter
    (fun patterns => ∀ i, patterns i ⊆ scope i)
  let gap := fun (patterns : Fin t → Finset (Fin n)) =>
    (cube.filter (fun x => ∀ i : Fin t, x ∩ scope i ≠ patterns i)).sum diff
  (∀ p ∈ choices,
    (gap p ≠ 0 ↔ ∃ x ∈ cube, ∀ i, x ∩ scope i = p i) ∧
    (∀ x ∈ cube, (∀ i, x ∩ scope i = p i) →
      gap p = (-1 : Int) ^ (t + x.card) * delta)) ∧
  (choices.filter (fun p => gap p ≠ 0)).card = 2 ^ n) := by
  intro n t hn A B scope cube diff delta pinnedAt hpin hdelta hcover hpriv choices gap
  have hflip : ∀ (j : Fin n) (x : Finset (Fin n)), j ∉ x → diff (insert j x) = - diff x := by
    intro j x hj
    have hS : (Finset.univ.erase j : Finset (Fin n)) ≠ Finset.univ := by
      intro h
      have := Finset.mem_univ j
      rw [← h] at this
      exact (Finset.mem_erase.1 this).1 rfl
    have hz : x ⊆ Finset.univ.erase j := by
      intro a ha
      exact Finset.mem_erase.2 ⟨fun h => hj (h ▸ ha), Finset.mem_univ a⟩
    have h := hpin _ hS x hz
    have hf : cube.filter (pinnedAt (Finset.univ.erase j) x) = {x, insert j x} := by
      ext y
      simp only [cube, pinnedAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hy
        by_cases hjy : j ∈ y
        · right
          rw [← hy]
          ext a
          by_cases haj : a = j
          · simp [haj, hjy]
          · simp [haj]
        · left
          rw [← hy]
          ext a
          by_cases haj : a = j
          · simp [haj, hjy]
          · simp [haj]
      · rintro (h1 | h1)
        · rw [h1]
          ext a
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨fun h => h.1, fun h => ⟨h, fun e => hj (e ▸ h)⟩⟩
        · rw [h1]
          ext a
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · rintro ⟨h2 | h2, hne⟩
            · exact absurd h2 hne
            · exact h2
          · intro h2
            exact ⟨Or.inr h2, fun e => hj (e ▸ h2)⟩
    rw [hf, Finset.sum_pair] at h
    · exact (neg_eq_of_add_eq_zero_right h).symm
    · intro e
      apply hj
      rw [e]
      exact Finset.mem_insert_self j x
  have hdiff : ∀ x : Finset (Fin n), diff x = (-1 : Int) ^ x.card * delta := by
    intro x
    induction x using Finset.induction_on with
    | empty => simp [delta]
    | insert j x hj ih =>
      rw [hflip j x hj, ih, Finset.card_insert_of_notMem hj, pow_succ]
      ring
  have huniqx : ∀ y z : Finset (Fin n), (∀ i, y ∩ scope i = z ∩ scope i) → y = z := by
    intro y z h
    ext j
    obtain ⟨i, hi⟩ := hcover j
    have := Finset.ext_iff.1 (h i) j
    simpa [hi] using this
  have hvan : ∀ (p : Fin t → Finset (Fin n)) (T : Finset (Fin t)), T ≠ Finset.univ →
      (cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i)).sum diff = 0 := by
    intro p T hT
    obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
      by_contra h
      exact hT (Finset.eq_univ_iff_forall.2 (fun i => by_contra (fun hi => h ⟨i, hi⟩)))
    obtain ⟨j, _, huniq⟩ := hpriv i
    let tog := fun x : Finset (Fin n) => if j ∈ x then x.erase j else insert j x
    have hmem : ∀ a ∈ cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i),
        tog a ∈ cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i) := by
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨Finset.mem_univ _, fun h hh => ?_⟩
      rw [← ha.2 h hh]
      ext b
      simp only [Finset.mem_inter]
      refine and_congr_left (fun hb => ?_)
      have hbj : b ≠ j := by
        intro e
        rw [e] at hb
        exact hi (huniq h hb ▸ hh)
      by_cases hja : j ∈ a
      · simp [tog, hja, hbj]
      · simp [tog, hja, hbj]
    have hinv : ∀ a : Finset (Fin n), tog (tog a) = a := by
      intro a
      by_cases hja : j ∈ a
      · simp [tog, hja, Finset.insert_erase]
      · simp [tog, hja, Finset.erase_insert]
    have key : (cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i)).sum diff
        = (cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i)).sum (fun x => - diff x) := by
      refine Finset.sum_nbij' tog tog hmem hmem (fun a _ => hinv a) (fun a _ => hinv a) (fun a _ => ?_)
      by_cases hja : j ∈ a
      · have h1 := hflip j (a.erase j) (Finset.notMem_erase j a)
        rw [Finset.insert_erase hja] at h1
        have h2 : tog a = a.erase j := by simp [tog, hja]
        rw [h2]; exact h1
      · have h2 : tog a = insert j a := by simp [tog, hja]
        rw [h2, hflip j a hja, neg_neg]
    rw [Finset.sum_neg_distrib] at key
    have hself : ∀ v : Int, v = -v → v = 0 := fun v h => by omega
    exact hself _ key
  have hgap : ∀ p : Fin t → Finset (Fin n), gap p
      = ∑ T ∈ (Finset.univ : Finset (Fin t)).powerset,
          (-1 : Int) ^ T.card * (cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i)).sum diff := by
    intro p
    have hprod : ∀ x : Finset (Fin n), (if (∀ i, x ∩ scope i ≠ p i) then (1 : Int) else 0)
        = ∑ T ∈ (Finset.univ : Finset (Fin t)).powerset,
            (-1 : Int) ^ T.card * (if ∀ i ∈ T, x ∩ scope i = p i then (1 : Int) else 0) := by
      intro x
      have h1 : (if (∀ i, x ∩ scope i ≠ p i) then (1 : Int) else 0)
          = ∏ i : Fin t, ((-(if x ∩ scope i = p i then (1 : Int) else 0)) + 1) := by
        split_ifs with h
        · symm
          apply Finset.prod_eq_one
          intro i _
          simp [h i]
        · obtain ⟨i, hi⟩ : ∃ i, x ∩ scope i = p i := by
            by_contra hc
            exact h (fun i hi => hc ⟨i, hi⟩)
          symm
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hi]
      rw [h1, Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_boole]
      split_ifs <;> rfl
    change (cube.filter (fun x => ∀ i, x ∩ scope i ≠ p i)).sum diff = _
    rw [Finset.sum_filter]
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    have h2 := congrArg (fun v => v * diff x) (hprod x)
    simp only [Finset.sum_mul] at h2
    calc (if (∀ i, x ∩ scope i ≠ p i) then diff x else 0)
        = (if (∀ i, x ∩ scope i ≠ p i) then (1 : Int) else 0) * diff x := by split_ifs <;> simp
      _ = _ := h2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T _
        split_ifs <;> simp
  have hfull : ∀ (p : Fin t → Finset (Fin n)) (x : Finset (Fin n)), (∀ i, x ∩ scope i = p i) →
      gap p = (-1 : Int) ^ (t + x.card) * delta := by
    intro p x hx
    rw [hgap p, Finset.sum_eq_single (Finset.univ : Finset (Fin t))]
    · have h1 : cube.filter (fun y => ∀ i ∈ (Finset.univ : Finset (Fin t)), y ∩ scope i = p i) = {x} := by
        ext y
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hy
          exact huniqx y x (fun i => (hy.2 i (Finset.mem_univ i)).trans (hx i).symm)
        · intro e
          rw [e]
          exact ⟨Finset.mem_univ _, fun i _ => hx i⟩
      rw [h1, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin, pow_add, mul_assoc]
      congr 1
      exact hdiff x
    · intro T _ hT
      rw [hvan p T hT, mul_zero]
    · intro h
      exact absurd (Finset.mem_powerset.2 (Finset.Subset.refl _)) h
  have hzero : ∀ p : Fin t → Finset (Fin n), (¬ ∃ x : Finset (Fin n), ∀ i, x ∩ scope i = p i) → gap p = 0 := by
    intro p hp
    rw [hgap p]
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : T = Finset.univ
    · have h0 : (cube.filter (fun x => ∀ i ∈ T, x ∩ scope i = p i)).sum diff = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        exact absurd ⟨y, fun i => (Finset.mem_filter.1 hy).2 i (hT ▸ Finset.mem_univ i)⟩ hp
      rw [h0, mul_zero]
    · rw [hvan p T hT, mul_zero]
  have hiff : ∀ p : Fin t → Finset (Fin n), gap p ≠ 0 ↔ ∃ x : Finset (Fin n), ∀ i, x ∩ scope i = p i := by
    intro p
    constructor
    · intro h
      by_contra hc
      exact h (hzero p hc)
    · rintro ⟨x, hx⟩
      rw [hfull p x hx]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdelta
  refine ⟨fun p _ => ⟨?_, fun x _ hx => hfull p x hx⟩, ?_⟩
  · rw [hiff p]
    simp [cube]
  · have h1 : choices.filter (fun p => gap p ≠ 0) = cube.image (fun x i => x ∩ scope i) := by
      ext p
      rw [Finset.mem_filter, hiff p, Finset.mem_image]
      constructor
      · rintro ⟨_, x, hx⟩
        exact ⟨x, Finset.mem_univ _, funext hx⟩
      · rintro ⟨x, _, e⟩
        refine ⟨?_, x, fun i => congrFun e i⟩
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_⟩
        rw [← e]
        exact Finset.inter_subset_right
    rw [h1, Finset.card_image_of_injective]
    · simp [cube]
    · intro y z h
      exact huniqx y z (fun i => congrFun h i)
