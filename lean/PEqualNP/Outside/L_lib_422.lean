import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_422_aux

private def sign2 (bit : ZMod 2) : ℤ :=
  if bit = 0 then 1 else -1

private theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem sign2_zero : sign2 0 = 1 := rfl

private theorem sign2_one : sign2 1 = -1 := by decide

private theorem sign2_add (a b : ZMod 2) : sign2 (a + b) = sign2 a * sign2 b := by
  fin_cases a <;> fin_cases b <;> decide

private theorem zmod2_eq_iff_add_eq_zero (a b : ZMod 2) : a = b ↔ a + b = 0 := by
  revert a b
  decide

private def suppMasks {n : ℕ} (I : Finset (Fin n)) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter (fun a => ∀ j : Fin n, j ∉ I → a j = 0)

private theorem zero_mem_suppMasks {n : ℕ} (I : Finset (Fin n)) :
    (0 : Fin n → ZMod 2) ∈ suppMasks I := by
  simp [suppMasks]

private theorem suppMasks_empty (n : ℕ) :
    suppMasks (∅ : Finset (Fin n)) = {0} := by
  ext a
  simp only [suppMasks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    not_false_eq_true, forall_true_left, Finset.mem_singleton]
  exact ⟨fun h => funext h, fun h j => by rw [h]; rfl⟩

private theorem dotProduct_update_one {n : ℕ} (a w : Fin n → ZMod 2) (i₀ : Fin n) (ha : a i₀ = 0) :
    dotProduct (Function.update a i₀ 1) w = dotProduct a w + w i₀ := by
  simp only [dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  simp only [Function.update_self, one_mul, ha, zero_mul, zero_add]
  have hsum : ∑ x ∈ Finset.univ.erase i₀, Function.update a i₀ 1 x * w x =
      ∑ x ∈ Finset.univ.erase i₀, a x * w x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hsum, add_comm]

private theorem sum_suppMasks_sign2_dot {n : ℕ} (I : Finset (Fin n)) (w : Fin n → ZMod 2) :
    ∑ a ∈ suppMasks I, sign2 (dotProduct a w) =
      if ∀ i ∈ I, w i = 0 then (2 : ℤ) ^ I.card else 0 := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    rw [suppMasks_empty, Finset.sum_singleton]
    simp [dotProduct, sign2_zero]
  | @insert i₀ I hi₀ ih =>
    let f : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun a => Function.update a i₀ 1
    have hdisj : Disjoint (suppMasks I) ((suppMasks I).image f) := by
      rw [Finset.disjoint_left]
      intro a ha hmem
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hmem
      have h0 : f b i₀ = 0 := (Finset.mem_filter.1 ha).2 i₀ hi₀
      have h1 : f b i₀ = 1 := Function.update_self i₀ 1 b
      rw [h1] at h0
      exact one_ne_zero h0
    have hunion : suppMasks (insert i₀ I) = suppMasks I ∪ (suppMasks I).image f := by
      ext b
      simp only [suppMasks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image, Finset.mem_insert, not_or]
      constructor
      · intro hb
        rcases zmod2_eq_zero_or_one (b i₀) with h0 | h1
        · left
          intro j hj
          by_cases hji : j = i₀
          · subst hji; exact h0
          · exact hb j ⟨hji, hj⟩
        · right
          refine ⟨Function.update b i₀ 0, ?_, ?_⟩
          · intro j hj
            by_cases hji : j = i₀
            · rw [hji]; exact Function.update_self i₀ 0 b
            · rw [Function.update_of_ne hji]
              exact hb j ⟨hji, hj⟩
          · funext j
            by_cases hji : j = i₀
            · subst hji; simp [f, h1]
            · simp [f, Function.update_of_ne hji]
      · rintro (hb | ⟨a, ha, rfl⟩)
        · intro j ⟨_, hj⟩
          exact hb j hj
        · intro j ⟨hji, hj⟩
          simp only [f, Function.update_of_ne hji]
          exact ha j hj
    have hinj : Set.InjOn f (suppMasks I) := by
      intro a ha b hb hab
      funext j
      by_cases hji : j = i₀
      · subst hji
        have ha0 : a j = 0 := (Finset.mem_filter.1 ha).2 j hi₀
        have hb0 : b j = 0 := (Finset.mem_filter.1 hb).2 j hi₀
        exact ha0.trans hb0.symm
      · have h := congrFun hab j
        simpa only [f, Function.update_of_ne hji] using h
    rw [hunion, Finset.sum_union hdisj, Finset.sum_image hinj]
    have hshift : ∑ a ∈ suppMasks I, sign2 (dotProduct (f a) w) =
        sign2 (w i₀) * ∑ a ∈ suppMasks I, sign2 (dotProduct a w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 : a i₀ = 0 := (Finset.mem_filter.1 ha).2 i₀ hi₀
      rw [dotProduct_update_one a w i₀ ha0, sign2_add, mul_comm]
    rw [hshift, ← one_add_mul, ih, Finset.card_insert_of_notMem hi₀]
    rcases zmod2_eq_zero_or_one (w i₀) with h0 | h1
    · rw [h0, sign2_zero]
      by_cases hall : ∀ i ∈ I, w i = 0
      · have hall' : ∀ i ∈ insert i₀ I, w i = 0 := by
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hiI
          · exact h0
          · exact hall i hiI
        simp only [if_pos hall, if_pos hall', pow_succ]
        ring
      · have hall' : ¬ ∀ i ∈ insert i₀ I, w i = 0 := fun h =>
          hall (fun i hi => h i (Finset.mem_insert_of_mem hi))
        simp only [if_neg hall, if_neg hall', mul_zero]
    · rw [h1, sign2_one]
      have hall' : ¬ ∀ i ∈ insert i₀ I, w i = 0 := by
        intro h
        have h0 := h i₀ (Finset.mem_insert_self i₀ I)
        rw [h1] at h0
        exact one_ne_zero h0
      simp only [if_neg hall']
      ring

private theorem main_core (n t : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) :
    (∀ (I : Finset (Fin n)) (v : Fin n → ZMod 2), I.card ≤ t →
      (2 : ℤ) ^ I.card * (∑ x : Fin n → ZMod 2, if ∀ i ∈ I, x i = v i then sign2 (f x) else 0) =
        ∑ y : Fin n → ZMod 2, sign2 (f y)) ↔
    ∀ a : Fin n → ZMod 2, a ≠ 0 → (Finset.univ.filter (fun j : Fin n => a j ≠ 0)).card ≤ t →
      (∑ x : Fin n → ZMod 2, sign2 (f x + dotProduct a x)) = 0 := by
  classical
  constructor
  · intro hCI a ha hcard
    set I : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => a j ≠ 0)
    have hsum_eq : ∑ v ∈ suppMasks I, sign2 (dotProduct a v) *
        ((2 : ℤ) ^ I.card * (∑ x : Fin n → ZMod 2, if ∀ i ∈ I, x i = v i then sign2 (f x) else 0)) =
        ∑ v ∈ suppMasks I, sign2 (dotProduct a v) * (∑ y : Fin n → ZMod 2, sign2 (f y)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hCI I v hcard]
    have hrhs : ∑ v ∈ suppMasks I, sign2 (dotProduct a v) * (∑ y : Fin n → ZMod 2, sign2 (f y)) = 0 := by
      rw [← Finset.sum_mul]
      have hcomm : ∑ v ∈ suppMasks I, sign2 (dotProduct a v) =
          ∑ v ∈ suppMasks I, sign2 (dotProduct v a) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [dotProduct_comm]
      rw [hcomm, sum_suppMasks_sign2_dot I a]
      have hnot : ¬ ∀ i ∈ I, a i = 0 := by
        intro hall
        apply ha
        funext j
        by_cases hj : a j = 0
        · exact hj
        · exact hall j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
      simp [hnot]
    have hlhs : ∑ v ∈ suppMasks I, sign2 (dotProduct a v) *
        ((2 : ℤ) ^ I.card * (∑ x : Fin n → ZMod 2, if ∀ i ∈ I, x i = v i then sign2 (f x) else 0)) =
        (2 : ℤ) ^ I.card * (∑ x : Fin n → ZMod 2, sign2 (f x + dotProduct a x)) := by
      have hpull : ∑ v ∈ suppMasks I, sign2 (dotProduct a v) *
          ((2 : ℤ) ^ I.card * (∑ x : Fin n → ZMod 2, if ∀ i ∈ I, x i = v i then sign2 (f x) else 0)) =
          (2 : ℤ) ^ I.card * ∑ v ∈ suppMasks I, ∑ x : Fin n → ZMod 2,
            if ∀ i ∈ I, x i = v i then sign2 (f x) * sign2 (dotProduct a v) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        rw [← mul_assoc, mul_comm (sign2 (dotProduct a v)) ((2 : ℤ) ^ I.card), mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
      rw [hpull, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      let px : Fin n → ZMod 2 := fun i => if i ∈ I then x i else 0
      have hpx_mem : px ∈ suppMasks I := by
        simp only [suppMasks, Finset.mem_filter, Finset.mem_univ, true_and, px]
        intro j hj
        exact if_neg hj
      have hiff : ∀ v ∈ suppMasks I, (∀ i ∈ I, x i = v i) ↔ v = px := by
        intro v hv
        constructor
        · intro h
          funext j
          by_cases hj : j ∈ I
          · simp only [px, if_pos hj]; exact (h j hj).symm
          · simp only [px, if_neg hj]; exact (Finset.mem_filter.1 hv).2 j hj
        · rintro rfl i hi
          simp only [px, if_pos hi]
      have hinner : ∑ v ∈ suppMasks I, (if ∀ i ∈ I, x i = v i then sign2 (f x) * sign2 (dotProduct a v) else 0) =
          sign2 (f x) * sign2 (dotProduct a px) := by
        rw [← Finset.add_sum_erase _ _ hpx_mem]
        have hself : ∀ i ∈ I, x i = px i := fun i hi => by simp only [px, if_pos hi]
        rw [if_pos hself]
        have hrest : ∑ v ∈ (suppMasks I).erase px,
            (if ∀ i ∈ I, x i = v i then sign2 (f x) * sign2 (dotProduct a v) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          have hv_mem : v ∈ suppMasks I := Finset.mem_of_mem_erase hv
          have hv_ne : v ≠ px := Finset.ne_of_mem_erase hv
          have hnot : ¬ ∀ i ∈ I, x i = v i := fun h => hv_ne ((hiff v hv_mem).1 h)
          exact if_neg hnot
        rw [hrest, add_zero]
      have hdot : dotProduct a px = dotProduct a x := by
        simp only [dotProduct, px]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ I
        · simp only [if_pos hj]
        · have haj : a j = 0 := by
            by_contra hne
            exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, hne⟩)
          simp only [if_neg hj, haj, zero_mul]
      rw [hinner, hdot, sign2_add]
    rw [hlhs, hrhs] at hsum_eq
    have hpow : (2 : ℤ) ^ I.card ≠ 0 := pow_ne_zero I.card (by norm_num)
    exact (mul_eq_zero.1 hsum_eq).resolve_left hpow
  · intro hWalsh I v hcard
    have hlhs : (2 : ℤ) ^ I.card *
        (∑ x : Fin n → ZMod 2, if ∀ i ∈ I, x i = v i then sign2 (f x) else 0) =
        ∑ x : Fin n → ZMod 2, (if ∀ i ∈ I, (x + v) i = 0 then (2 : ℤ) ^ I.card else 0) * sign2 (f x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have heq : (∀ i ∈ I, x i = v i) ↔ (∀ i ∈ I, (x + v) i = 0) := by
        constructor <;> intro h i hi
        · exact (zmod2_eq_iff_add_eq_zero (x i) (v i)).1 (h i hi)
        · exact (zmod2_eq_iff_add_eq_zero (x i) (v i)).2 (h i hi)
      by_cases h : ∀ i ∈ I, x i = v i
      · rw [if_pos h, if_pos (heq.1 h)]
      · rw [if_neg h, if_neg (fun h' => h (heq.2 h')), mul_zero, zero_mul]
    rw [hlhs]
    have hexpand : ∑ x : Fin n → ZMod 2, (if ∀ i ∈ I, (x + v) i = 0 then (2 : ℤ) ^ I.card else 0) * sign2 (f x) =
        ∑ a ∈ suppMasks I, sign2 (dotProduct a v) * ∑ x : Fin n → ZMod 2, sign2 (f x + dotProduct a x) := by
      have h1 : ∀ x : Fin n → ZMod 2,
          (if ∀ i ∈ I, (x + v) i = 0 then (2 : ℤ) ^ I.card else 0) * sign2 (f x) =
          ∑ a ∈ suppMasks I, sign2 (dotProduct a v) * sign2 (f x + dotProduct a x) := by
        intro x
        rw [← sum_suppMasks_sign2_dot I (x + v), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [dotProduct_add, sign2_add, sign2_add]
        ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
    rw [hexpand, ← Finset.add_sum_erase _ _ (zero_mem_suppMasks I)]
    have h0 : sign2 (dotProduct 0 v) * ∑ x : Fin n → ZMod 2, sign2 (f x + dotProduct 0 x) =
        ∑ y : Fin n → ZMod 2, sign2 (f y) := by
      simp [dotProduct, sign2_zero]
    have hrest : ∑ a ∈ (suppMasks I).erase 0,
        sign2 (dotProduct a v) * ∑ x : Fin n → ZMod 2, sign2 (f x + dotProduct a x) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
      have ha_mem : a ∈ suppMasks I := Finset.mem_of_mem_erase ha
      have hsub : Finset.univ.filter (fun j : Fin n => a j ≠ 0) ⊆ I := by
        intro j hj
        by_contra hjI
        exact (Finset.mem_filter.1 hj).2 ((Finset.mem_filter.1 ha_mem).2 j hjI)
      have ha_card : (Finset.univ.filter (fun j : Fin n => a j ≠ 0)).card ≤ t :=
        le_trans (Finset.card_le_card hsub) hcard
      rw [hWalsh a ha0 ha_card, mul_zero]
    rw [h0, hrest, add_zero]

end PEqualNP.Outside.L_lib_422_aux

theorem PEqualNP.Outside.L_lib_422 : (∀ n t : ℕ,
  let V := Fin n → ZMod 2
  let sign := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ f : V → ZMod 2,
    (∀ (I : Finset (Fin n)) (v : V), I.card ≤ t →
      (2:ℤ)^I.card * (∑ x : V, if ∀ i ∈ I, x i = v i then sign (f x) else 0) =
        ∑ y : V, sign (f y)) ↔
    ∀ a : V, a ≠ 0 → (Finset.univ.filter (fun j : Fin n => a j ≠ 0)).card ≤ t →
      (∑ x : V, sign (f x + dotProduct a x)) = 0) := by
  intro n t V sign f
  exact PEqualNP.Outside.L_lib_422_aux.main_core n t f
