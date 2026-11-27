import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_591_aux

lemma ringChar_dvd_iff {K : Type} [Field K] (n : ℕ) :
    ringChar K ∣ n ↔ (n : K) = 0 := by
  exact (CharP.cast_eq_zero_iff K (ringChar K) n).symm

lemma ringChar_eq_two_iff {K : Type} [Field K] :
    ringChar K = 2 ↔ (2 : K) = 0 := by
  constructor
  · intro h
    have hdiv : ringChar K ∣ 2 := by rw [h]
    exact (ringChar_dvd_iff 2).mp hdiv
  · intro h2
    have hdiv : ringChar K ∣ 2 := (ringChar_dvd_iff 2).mpr h2
    have hle : ringChar K ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hne0 : ringChar K ≠ 0 := by
      intro h0
      rw [h0] at hdiv
      exact absurd (zero_dvd_iff.mp hdiv) (by norm_num)
    have hne1 : ringChar K ≠ 1 := by
      intro h1
      have hdiv1 : ringChar K ∣ 1 := by rw [h1]
      have h10 : ((1 : ℕ) : K) = 0 := (ringChar_dvd_iff 1).mp hdiv1
      simp at h10
    omega

def delta {K : Type} [Field K] {α : Type} [DecidableEq α] (x y : α) : K :=
  if x = y then 1 else 0

lemma delta_comm {K : Type} [Field K] {α : Type} [DecidableEq α] (x y : α) :
    delta (K := K) x y = delta y x := by
  unfold delta
  by_cases h : x = y
  · subst h
    simp
  · have h' : y ≠ x := Ne.symm h
    simp [h, h']

lemma fixed_cast {K : Type} [Field K] {q : ℕ} (p r : Equiv.Perm (Fin q)) :
    (((Finset.univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card : K) =
      ∑ i : Fin q, delta (K := K) (r (p i)) i := by
  unfold delta
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

def X {K : Type} [Field K] {b : ℕ} (p : Equiv.Perm (Fin (b + 2)))
    (i j : Fin (b + 1)) : K :=
  delta (p j.castSucc) i.castSucc - delta (p (Fin.last (b + 1))) i.castSucc

lemma sum_X_mul_delta {K : Type} [Field K] {b : ℕ} (r : Equiv.Perm (Fin (b + 2)))
    (i : Fin (b + 1)) (x : Fin (b + 2)) :
    ∑ k : Fin (b + 1), X (K := K) r i k * delta x k.castSucc =
      delta (r x) i.castSucc - delta (r (Fin.last (b + 1))) i.castSucc := by
  refine Fin.lastCases ?_ ?_ x
  · have hzero : ∀ k : Fin (b + 1), delta (K := K) (Fin.last (b + 1)) k.castSucc = 0 := by
      intro k
      unfold delta
      have hne : Fin.last (b + 1) ≠ k.castSucc := Ne.symm (Fin.castSucc_ne_last k)
      simp [hne]
    simp [hzero]
  · intro m
    rw [Finset.sum_eq_single m]
    · simp [delta, X]
    · intro k _ hkm
      unfold delta
      have hne : m.castSucc ≠ k.castSucc := fun h => hkm (Fin.castSucc_injective _ h).symm
      simp [hne]
    · intro hm
      exact absurd (Finset.mem_univ m) hm

lemma X_mul {K : Type} [Field K] {b : ℕ} (r p : Equiv.Perm (Fin (b + 2)))
    (i j : Fin (b + 1)) :
    ∑ k : Fin (b + 1), X (K := K) r i k * X (K := K) p k j = X (K := K) (r * p) i j := by
  have h1 :
      ∑ k : Fin (b + 1), X (K := K) r i k * X (K := K) p k j =
        (∑ k : Fin (b + 1), X (K := K) r i k * delta (p j.castSucc) k.castSucc) -
          (∑ k : Fin (b + 1), X (K := K) r i k * delta (p (Fin.last (b + 1))) k.castSucc) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold X
    ring
  rw [h1, sum_X_mul_delta, sum_X_mul_delta]
  unfold X
  simp only [Equiv.Perm.mul_apply]
  ring

lemma sum_delta_eq_one {K : Type} [Field K] {q : ℕ} (x : Fin q) :
    ∑ i : Fin q, delta (K := K) x i = 1 := by
  rw [Finset.sum_eq_single x]
  · unfold delta
    simp
  · intro i _ hix
    unfold delta
    have hne : x ≠ i := Ne.symm hix
    simp [hne]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

lemma X_trace {K : Type} [Field K] {b : ℕ} (s : Equiv.Perm (Fin (b + 2))) :
    (∑ i : Fin (b + 1), X (K := K) s i i) + 1 =
      ∑ i : Fin (b + 2), delta (K := K) (s i) i := by
  have h1 :
      ∑ i : Fin (b + 2), delta (K := K) (s (Fin.last (b + 1))) i = 1 :=
    sum_delta_eq_one (s (Fin.last (b + 1)))
  rw [Fin.sum_univ_castSucc] at h1
  rw [Fin.sum_univ_castSucc (f := fun i : Fin (b + 2) => delta (K := K) (s i) i)]
  unfold X
  rw [Finset.sum_sub_distrib]
  linear_combination -h1

lemma X_row_sum {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (s : Equiv.Perm (Fin (b + 2))) (i : Fin (b + 1)) :
    ∑ k : Fin (b + 1), X (K := K) s i k = 1 := by
  have hperm :
      ∑ k : Fin (b + 2), delta (K := K) (s k) i.castSucc = 1 := by
    rw [Equiv.sum_comp s (fun y => delta (K := K) y i.castSucc)]
    have hcomm :
        (∑ y : Fin (b + 2), delta (K := K) y i.castSucc) =
          ∑ y : Fin (b + 2), delta (K := K) i.castSucc y :=
      Finset.sum_congr rfl (fun y _ => delta_comm y i.castSucc)
    rw [hcomm]
    exact sum_delta_eq_one i.castSucc
  rw [Fin.sum_univ_castSucc] at hperm
  unfold X
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hq' : ((b + 1 : ℕ) : K) + 1 = 0 := by
    push_cast at hq ⊢
    linear_combination hq
  linear_combination hperm - delta (K := K) (s (Fin.last (b + 1))) i.castSucc * hq'

def Y {K : Type} [Field K] {b : ℕ} (p : Equiv.Perm (Fin (b + 2))) (i j : Fin b) : K :=
  X p i.castSucc j.castSucc - X p (Fin.last b) j.castSucc

lemma Y_mul {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (r p : Equiv.Perm (Fin (b + 2))) (i j : Fin b) :
    ∑ k : Fin b, Y (K := K) r i k * Y (K := K) p k j = Y (K := K) (r * p) i j := by
  have hext :
      ∑ k : Fin b, Y (K := K) r i k * Y (K := K) p k j =
        ∑ k : Fin (b + 1),
          (X (K := K) r i.castSucc k - X (K := K) r (Fin.last b) k) *
            (X (K := K) p k j.castSucc - X (K := K) p (Fin.last b) j.castSucc) := by
    rw [Fin.sum_univ_castSucc]
    simp [Y]
  rw [hext]
  have hsplit :
      ∑ k : Fin (b + 1),
          (X (K := K) r i.castSucc k - X (K := K) r (Fin.last b) k) *
            (X (K := K) p k j.castSucc - X (K := K) p (Fin.last b) j.castSucc) =
        (∑ k : Fin (b + 1), X (K := K) r i.castSucc k * X (K := K) p k j.castSucc) -
          (∑ k : Fin (b + 1), X (K := K) r (Fin.last b) k * X (K := K) p k j.castSucc) -
          X (K := K) p (Fin.last b) j.castSucc *
            ((∑ k : Fin (b + 1), X (K := K) r i.castSucc k) -
              (∑ k : Fin (b + 1), X (K := K) r (Fin.last b) k)) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hsplit, X_mul, X_mul, X_row_sum hq, X_row_sum hq]
  unfold Y
  ring

lemma Y_trace {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (s : Equiv.Perm (Fin (b + 2))) :
    (∑ i : Fin b, Y (K := K) s i i) + 2 =
      ∑ i : Fin (b + 2), delta (K := K) (s i) i := by
  have hext :
      ∑ i : Fin b, Y (K := K) s i i =
        ∑ i : Fin (b + 1), (X (K := K) s i i - X (K := K) s (Fin.last b) i) := by
    rw [Fin.sum_univ_castSucc]
    simp [Y]
  rw [hext, Finset.sum_sub_distrib, X_row_sum hq s (Fin.last b)]
  have ht := X_trace (K := K) s
  linear_combination ht

lemma exists_factor_of_fintype {K : Type} [Field K] {P ι : Type} [Fintype ι] {d : ℕ}
    (f : P → P → K) (A0 B0 : P → ι → K)
    (hf : ∀ p r, f p r = ∑ x : ι, A0 p x * B0 r x)
    (hd : Fintype.card ι ≤ d) :
    ∃ A B : P → Fin d → K, ∀ p r, f p r = ∑ j : Fin d, A p j * B r j := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A : P → Fin d → K := fun p j =>
    if hj : j.val < Fintype.card ι then A0 p (e.symm ⟨j.val, hj⟩) else 0
  let B : P → Fin d → K := fun r j =>
    if hj : j.val < Fintype.card ι then B0 r (e.symm ⟨j.val, hj⟩) else 0
  refine ⟨A, B, fun p r => ?_⟩
  rw [hf p r]
  have h1 :
      ∑ j : Fin d, A p j * B r j =
        ∑ m : Fin (Fintype.card ι), A0 p (e.symm m) * B0 r (e.symm m) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hd)))]
    · rw [Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective hd hab)]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [A, B, Fin.val_castLE, m.isLt, ↓reduceDIte]
    · intro j _ hj
      have hnot : ¬ j.val < Fintype.card ι := by
        intro hlt
        exact hj (Finset.mem_image.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp only [A, B, hnot, ↓reduceDIte, mul_zero]
  rw [h1]
  exact (Fintype.sum_equiv e.symm
    (fun m => A0 p (e.symm m) * B0 r (e.symm m))
    (fun x => A0 p x * B0 r x)
    (fun _ => rfl)).symm

lemma upper_bound_nondiv {K : Type} [Field K] (b d : ℕ)
    (hd : (b + 1) ^ 2 + 1 ≤ d) :
    ∃ (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K),
      ∀ p r,
        (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
          ∑ j : Fin d, A p j * B r j := by
  let ι := (Fin (b + 1) × Fin (b + 1)) ⊕ Unit
  let A0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun p x =>
    match x with
    | Sum.inl (i, j) => X p j i
    | Sum.inr () => 1
  let B0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun r x =>
    match x with
    | Sum.inl (i, j) => X r i j
    | Sum.inr () => 1
  refine exists_factor_of_fintype _ A0 B0 (fun p r => ?_) ?_
  · rw [fixed_cast]
    dsimp only [ι]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique (ι := Unit)]
    simp only [A0, B0, mul_one]
    have hmul :
        (∑ i : Fin (b + 1), ∑ j : Fin (b + 1), X (K := K) p j i * X (K := K) r i j) =
          ∑ i : Fin (b + 1), X (K := K) (r * p) i i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcomm :
          (∑ j : Fin (b + 1), X (K := K) p j i * X (K := K) r i j) =
            ∑ j : Fin (b + 1), X (K := K) r i j * X (K := K) p j i :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [hcomm, X_mul]
    rw [hmul]
    exact (X_trace (K := K) (r * p)).symm
  · simpa [ι, sq] using hd

lemma upper_bound_div_char2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0) (h2 : (2 : K) = 0) (hd : b ^ 2 ≤ d) :
    ∃ (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K),
      ∀ p r,
        (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
          ∑ j : Fin d, A p j * B r j := by
  let ι := Fin b × Fin b
  let A0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun p x => Y p x.2 x.1
  let B0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun r x => Y r x.1 x.2
  refine exists_factor_of_fintype _ A0 B0 (fun p r => ?_) ?_
  · rw [fixed_cast]
    dsimp only [ι]
    rw [Fintype.sum_prod_type]
    simp only [A0, B0]
    have hmul :
        (∑ i : Fin b, ∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
          ∑ i : Fin b, Y (K := K) (r * p) i i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcomm :
          (∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
            ∑ j : Fin b, Y (K := K) r i j * Y (K := K) p j i :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [hcomm, Y_mul hq]
    rw [hmul]
    have ht := Y_trace (K := K) hq (r * p)
    rw [h2, add_zero] at ht
    exact ht.symm
  · simpa [ι, sq] using hd

lemma upper_bound_div_ne2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0) (hd : b ^ 2 + 1 ≤ d) :
    ∃ (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K),
      ∀ p r,
        (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
          ∑ j : Fin d, A p j * B r j := by
  let ι := (Fin b × Fin b) ⊕ Unit
  let A0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun p x =>
    match x with
    | Sum.inl (i, j) => Y p j i
    | Sum.inr () => 2
  let B0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun r x =>
    match x with
    | Sum.inl (i, j) => Y r i j
    | Sum.inr () => 1
  refine exists_factor_of_fintype _ A0 B0 (fun p r => ?_) ?_
  · rw [fixed_cast]
    dsimp only [ι]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique (ι := Unit)]
    simp only [A0, B0, mul_one]
    have hmul :
        (∑ i : Fin b, ∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
          ∑ i : Fin b, Y (K := K) (r * p) i i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcomm :
          (∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
            ∑ j : Fin b, Y (K := K) r i j * Y (K := K) p j i :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [hcomm, Y_mul hq]
    rw [hmul]
    exact (Y_trace (K := K) hq (r * p)).symm
  · simpa [ι, sq] using hd

def p1 {b : ℕ} (i j : Fin (b + 1)) : Equiv.Perm (Fin (b + 2)) :=
  Equiv.swap i.castSucc j.castSucc

def p2 {b : ℕ} (i j : Fin (b + 1)) : Equiv.Perm (Fin (b + 2)) :=
  Equiv.swap j.castSucc (Fin.last (b + 1)) * Equiv.swap i.castSucc j.castSucc

lemma p1_apply_i {b : ℕ} (i j : Fin (b + 1)) :
    p1 i j i.castSucc = j.castSucc := by
  simp [p1]

lemma p1_apply_last {b : ℕ} (i j : Fin (b + 1)) :
    p1 i j (Fin.last (b + 1)) = Fin.last (b + 1) := by
  unfold p1
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.castSucc_ne_last i))
    (Ne.symm (Fin.castSucc_ne_last j))]

lemma p2_apply_i {b : ℕ} (i j : Fin (b + 1)) :
    p2 i j i.castSucc = Fin.last (b + 1) := by
  simp [p2]

lemma p2_apply_last {b : ℕ} (i j : Fin (b + 1)) :
    p2 i j (Fin.last (b + 1)) = j.castSucc := by
  unfold p2
  rw [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.castSucc_ne_last i))
      (Ne.symm (Fin.castSucc_ne_last j)),
    Equiv.swap_apply_right]

lemma p2_eq_p1_of_ne {b : ℕ} (i j : Fin (b + 1)) (x : Fin (b + 2))
    (h1 : x ≠ i.castSucc) (h2 : x ≠ Fin.last (b + 1)) :
    p2 i j x = p1 i j x := by
  unfold p2 p1
  rw [Equiv.Perm.mul_apply]
  have hne1 : Equiv.swap i.castSucc j.castSucc x ≠ j.castSucc := by
    intro h
    have hx : x = i.castSucc := (Equiv.swap i.castSucc j.castSucc).injective (by
      rw [h, Equiv.swap_apply_left])
    exact h1 hx
  have hne2 : Equiv.swap i.castSucc j.castSucc x ≠ Fin.last (b + 1) := by
    intro h
    have hx : x = Fin.last (b + 1) := (Equiv.swap i.castSucc j.castSucc).injective (by
      rw [h, Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.castSucc_ne_last i))
        (Ne.symm (Fin.castSucc_ne_last j))])
    exact h2 hx
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]

def H {K : Type} [Field K] {n : ℕ} (i j : Fin n) : K :=
  delta i j + 1

lemma H_comm {K : Type} [Field K] {n : ℕ} (i j : Fin n) :
    H (K := K) i j = H j i := by
  unfold H
  rw [delta_comm]

lemma fixed_diff_left {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1))
    (r : Equiv.Perm (Fin (b + 2))) :
    (∑ k : Fin (b + 2), delta (K := K) (r (p1 i j k)) k) -
        (∑ k : Fin (b + 2), delta (K := K) (r (p2 i j k)) k) =
      delta (r j.castSucc) i.castSucc - delta (r (Fin.last (b + 1))) i.castSucc +
        delta (r (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (r j.castSucc) (Fin.last (b + 1)) := by
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
  rw [p1_apply_last, p2_apply_last]
  have hsingle :
      ∑ k : Fin (b + 1),
          (delta (K := K) (r (p1 i j k.castSucc)) k.castSucc -
            delta (K := K) (r (p2 i j k.castSucc)) k.castSucc) =
        delta (r j.castSucc) i.castSucc - delta (r (Fin.last (b + 1))) i.castSucc := by
    rw [Finset.sum_eq_single i]
    · rw [p1_apply_i, p2_apply_i]
    · intro k _ hki
      have hne1 : k.castSucc ≠ i.castSucc := fun h => hki (Fin.castSucc_injective _ h)
      have hne2 : k.castSucc ≠ Fin.last (b + 1) := Fin.castSucc_ne_last k
      rw [p2_eq_p1_of_ne i j k.castSucc hne1 hne2, sub_self]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsingle]
  ring

lemma delta_p1_sub_p2 {K : Type} [Field K] {b : ℕ} (a c : Fin (b + 1))
    (x y : Fin (b + 2)) :
    delta (K := K) (p1 a c x) y - delta (K := K) (p2 a c x) y =
      (delta x a.castSucc - delta x (Fin.last (b + 1))) *
        (delta y c.castSucc - delta y (Fin.last (b + 1))) := by
  by_cases hx1 : x = a.castSucc
  · subst hx1
    rw [p1_apply_i, p2_apply_i]
    have hne : a.castSucc ≠ Fin.last (b + 1) := Fin.castSucc_ne_last a
    rw [delta_comm c.castSucc y, delta_comm (Fin.last (b + 1)) y]
    unfold delta
    simp [hne]
  · by_cases hx2 : x = Fin.last (b + 1)
    · subst hx2
      rw [p1_apply_last, p2_apply_last]
      have hne : Fin.last (b + 1) ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last a)
      rw [delta_comm c.castSucc y, delta_comm (Fin.last (b + 1)) y]
      unfold delta
      simp [hne]
    · rw [p2_eq_p1_of_ne a c x hx1 hx2, sub_self]
      unfold delta
      simp [hx1, hx2]

lemma fixed_diff_both {K : Type} [Field K] {b : ℕ} (i j a c : Fin (b + 1)) :
    ((∑ k : Fin (b + 2), delta (K := K) (p1 c a (p1 i j k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) (p1 c a (p2 i j k)) k)) -
    ((∑ k : Fin (b + 2), delta (K := K) (p2 c a (p1 i j k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) (p2 c a (p2 i j k)) k)) =
      H (K := K) i a * H (K := K) j c := by
  rw [fixed_diff_left i j (p1 c a), fixed_diff_left i j (p2 c a)]
  have h1 :
      (delta (K := K) (p1 c a j.castSucc) i.castSucc -
        delta (K := K) (p1 c a (Fin.last (b + 1))) i.castSucc +
        delta (K := K) (p1 c a (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (K := K) (p1 c a j.castSucc) (Fin.last (b + 1))) -
      (delta (K := K) (p2 c a j.castSucc) i.castSucc -
        delta (K := K) (p2 c a (Fin.last (b + 1))) i.castSucc +
        delta (K := K) (p2 c a (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (K := K) (p2 c a j.castSucc) (Fin.last (b + 1))) =
      (delta (p1 c a j.castSucc) i.castSucc - delta (p2 c a j.castSucc) i.castSucc) -
      (delta (p1 c a (Fin.last (b + 1))) i.castSucc -
        delta (p2 c a (Fin.last (b + 1))) i.castSucc) +
      (delta (p1 c a (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (p2 c a (Fin.last (b + 1))) (Fin.last (b + 1))) -
      (delta (p1 c a j.castSucc) (Fin.last (b + 1)) -
        delta (p2 c a j.castSucc) (Fin.last (b + 1))) := by
    ring
  rw [h1, delta_p1_sub_p2, delta_p1_sub_p2, delta_p1_sub_p2, delta_p1_sub_p2]
  have hd_jc : delta (K := K) j.castSucc c.castSucc = delta j c := by
    unfold delta
    simp [Fin.castSucc_inj]
  have hd_ia : delta (K := K) i.castSucc a.castSucc = delta i a := by
    unfold delta
    simp [Fin.castSucc_inj]
  have hd_jL : delta (K := K) j.castSucc (Fin.last (b + 1)) = 0 := by
    unfold delta
    simp [Fin.castSucc_ne_last]
  have hd_iL : delta (K := K) i.castSucc (Fin.last (b + 1)) = 0 := by
    unfold delta
    simp [Fin.castSucc_ne_last]
  have hd_Lc : delta (K := K) (Fin.last (b + 1)) c.castSucc = 0 := by
    unfold delta
    simp [Ne.symm (Fin.castSucc_ne_last c)]
  have hd_La : delta (K := K) (Fin.last (b + 1)) a.castSucc = 0 := by
    unfold delta
    simp [Ne.symm (Fin.castSucc_ne_last a)]
  have hd_LL : delta (K := K) (Fin.last (b + 1)) (Fin.last (b + 1)) = 1 := by
    unfold delta
    simp
  rw [hd_jc, hd_ia, hd_jL, hd_iL, hd_Lc, hd_La, hd_LL]
  unfold H
  ring

lemma fixed_diff_one {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1)) :
    (∑ k : Fin (b + 2), delta (K := K) ((1 : Equiv.Perm (Fin (b + 2))) (p1 i j k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) ((1 : Equiv.Perm (Fin (b + 2))) (p2 i j k)) k) =
      H (K := K) i j := by
  rw [fixed_diff_left]
  simp only [Equiv.Perm.one_apply]
  have hd_ji : delta (K := K) j.castSucc i.castSucc = delta i j := by
    rw [delta_comm]
    unfold delta
    simp [Fin.castSucc_inj]
  have hd_Li : delta (K := K) (Fin.last (b + 1)) i.castSucc = 0 := by
    unfold delta
    simp [Ne.symm (Fin.castSucc_ne_last i)]
  have hd_jL : delta (K := K) j.castSucc (Fin.last (b + 1)) = 0 := by
    unfold delta
    simp [Fin.castSucc_ne_last]
  have hd_LL : delta (K := K) (Fin.last (b + 1)) (Fin.last (b + 1)) = 1 := by
    unfold delta
    simp
  rw [hd_ji, hd_Li, hd_jL, hd_LL]
  unfold H
  ring

lemma fixed_one_diff {K : Type} [Field K] {b : ℕ} (a c : Fin (b + 1)) :
    (∑ k : Fin (b + 2), delta (K := K) (p1 c a ((1 : Equiv.Perm (Fin (b + 2))) k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) (p2 c a ((1 : Equiv.Perm (Fin (b + 2))) k)) k) =
      H (K := K) a c := by
  have h := fixed_diff_one (K := K) c a
  simp only [Equiv.Perm.one_apply] at h ⊢
  rw [h, H_comm]

lemma fixed_one_one {K : Type} [Field K] {b : ℕ} :
    ∑ k : Fin (b + 2),
        delta (K := K) ((1 : Equiv.Perm (Fin (b + 2))) ((1 : Equiv.Perm (Fin (b + 2))) k)) k =
      ((b + 2 : ℕ) : K) := by
  simp [delta]

def dot {K : Type} [Field K] {d : ℕ} (u v : Fin d → K) : K :=
  ∑ k : Fin d, u k * v k

lemma dot_sub_left {K : Type} [Field K] {d : ℕ} (u1 u2 v : Fin d → K) :
    dot (u1 - u2) v = dot u1 v - dot u2 v := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [sub_mul]

lemma dot_sub_right {K : Type} [Field K] {d : ℕ} (u v1 v2 : Fin d → K) :
    dot u (v1 - v2) = dot u v1 - dot u v2 := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [mul_sub]

lemma dot_smul_left {K : Type} [Field K] {d : ℕ} (c : K) (u v : Fin d → K) :
    dot (c • u) v = c * dot u v := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [mul_assoc]

lemma dot_smul_right {K : Type} [Field K] {d : ℕ} (c : K) (u v : Fin d → K) :
    dot u (c • v) = c * dot u v := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma dot_sum_left {K : Type} [Field K] {d : ℕ} {α : Type} (s : Finset α)
    (f : α → Fin d → K) (v : Fin d → K) :
    dot (∑ x ∈ s, f x) v = ∑ x ∈ s, dot (f x) v := by
  unfold dot
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma dot_sum_right {K : Type} [Field K] {d : ℕ} {α : Type} (s : Finset α)
    (u : Fin d → K) (g : α → Fin d → K) :
    dot u (∑ x ∈ s, g x) = ∑ x ∈ s, dot u (g x) := by
  unfold dot
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma card_le_of_biorthogonal {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (U V : ι → Fin d → K)
    (hUV : ∀ a c : ι, dot (U a) (V c) = delta a c) :
    Fintype.card ι ≤ d := by
  have hli : LinearIndependent K V := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h0 : dot (U a) (∑ c : ι, g c • V c) = 0 := by
      rw [hg]
      simp [dot]
    rw [dot_sum_right] at h0
    have h1 :
        ∑ c : ι, dot (U a) (g c • V c) = g a := by
      rw [Finset.sum_eq_single a]
      · rw [dot_smul_right, hUV a a]
        unfold delta
        simp
      · intro c _ hca
        rw [dot_smul_right, hUV a c]
        unfold delta
        have hne : a ≠ c := Ne.symm hca
        simp [hne]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [h1] at h0
    exact h0
  have hle := hli.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using hle

def Hinv {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1)) : K :=
  delta i j - ((b + 2 : ℕ) : K)⁻¹

lemma H_mul_Hinv {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) ≠ 0)
    (i j : Fin (b + 1)) :
    ∑ k : Fin (b + 1), H (K := K) i k * Hinv (K := K) k j = delta i j := by
  have hsplit :
      ∑ k : Fin (b + 1), H (K := K) i k * Hinv (K := K) k j =
        (∑ k : Fin (b + 1), delta (K := K) i k * delta k j) -
        ((b + 2 : ℕ) : K)⁻¹ * (∑ k : Fin (b + 1), delta (K := K) i k) +
        (∑ k : Fin (b + 1), delta (K := K) k j) -
        ((b + 2 : ℕ) : K)⁻¹ * ((b + 1 : ℕ) : K) := by
    have hconst :
        ∑ k : Fin (b + 1), ((b + 2 : ℕ) : K)⁻¹ = ((b + 2 : ℕ) : K)⁻¹ * ((b + 1 : ℕ) : K) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    rw [← hconst, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold H Hinv
    ring
  rw [hsplit]
  have hdd : ∑ k : Fin (b + 1), delta (K := K) i k * delta k j = delta i j := by
    rw [Finset.sum_eq_single i]
    · unfold delta
      simp
    · intro k _ hki
      unfold delta
      have hne : i ≠ k := Ne.symm hki
      simp [hne]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hd1 : ∑ k : Fin (b + 1), delta (K := K) i k = 1 := sum_delta_eq_one i
  have hd2 : ∑ k : Fin (b + 1), delta (K := K) k j = 1 := by
    have hcomm :
        (∑ k : Fin (b + 1), delta (K := K) k j) = ∑ k : Fin (b + 1), delta (K := K) j k :=
      Finset.sum_congr rfl (fun k _ => delta_comm k j)
    rw [hcomm]
    exact sum_delta_eq_one j
  rw [hdd, hd1, hd2]
  have hinv : ((b + 2 : ℕ) : K)⁻¹ * (1 + ((b + 1 : ℕ) : K)) = 1 := by
    have hsum : (1 : K) + ((b + 1 : ℕ) : K) = ((b + 2 : ℕ) : K) := by
      push_cast
      ring
    rw [hsum, inv_mul_cancel₀ hq]
  linear_combination -hinv

lemma Hinv_comm {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1)) :
    Hinv (K := K) i j = Hinv j i := by
  unfold Hinv
  rw [delta_comm]

lemma H_mul_H_of_char {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (i j : Fin b) :
    ∑ k : Fin b, H (K := K) i k * H (K := K) k j = delta i j := by
  have hsplit :
      ∑ k : Fin b, H (K := K) i k * H (K := K) k j =
        (∑ k : Fin b, delta (K := K) i k * delta k j) +
        (∑ k : Fin b, delta (K := K) i k) +
        (∑ k : Fin b, delta (K := K) k j) +
        (b : K) := by
    have hconst : ∑ _k : Fin b, (1 : K) = (b : K) := by
      simp
    rw [← hconst, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold H
    ring
  rw [hsplit]
  have hdd : ∑ k : Fin b, delta (K := K) i k * delta k j = delta i j := by
    rw [Finset.sum_eq_single i]
    · unfold delta
      simp
    · intro k _ hki
      unfold delta
      have hne : i ≠ k := Ne.symm hki
      simp [hne]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hd1 : ∑ k : Fin b, delta (K := K) i k = 1 := sum_delta_eq_one i
  have hd2 : ∑ k : Fin b, delta (K := K) k j = 1 := by
    have hcomm : (∑ k : Fin b, delta (K := K) k j) = ∑ k : Fin b, delta (K := K) j k :=
      Finset.sum_congr rfl (fun k _ => delta_comm k j)
    rw [hcomm]
    exact sum_delta_eq_one j
  rw [hdd, hd1, hd2]
  have hq' : (b : K) + 2 = 0 := by
    push_cast at hq
    exact hq
  linear_combination hq'

lemma lower_bound_nondiv {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) ≠ 0)
    (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r,
      (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
        ∑ j : Fin d, A p j * B r j) :
    (b + 1) ^ 2 + 1 ≤ d := by
  have hdot : ∀ p r, dot (A p) (B r) = ∑ k : Fin (b + 2), delta (K := K) (r (p k)) k := by
    intro p r
    rw [← fixed_cast]
    exact (hAB p r).symm
  let uD : Fin (b + 1) → Fin (b + 1) → Fin d → K := fun i j => A (p1 i j) - A (p2 i j)
  let vD : Fin (b + 1) → Fin (b + 1) → Fin d → K := fun a c => B (p1 c a) - B (p2 c a)
  have hDD : ∀ i j a c, dot (uD i j) (vD a c) = H i a * H j c := by
    intro i j a c
    simp only [uD, vD, dot_sub_left, dot_sub_right, hdot]
    exact fixed_diff_both i j a c
  have hD1 : ∀ i j, dot (uD i j) (B 1) = H i j := by
    intro i j
    simp only [uD, dot_sub_left, hdot]
    exact fixed_diff_one i j
  have h1D : ∀ a c, dot (A 1) (vD a c) = H a c := by
    intro a c
    simp only [vD, dot_sub_right, hdot]
    exact fixed_one_diff a c
  have h11 : dot (A 1) (B 1) = ((b + 2 : ℕ) : K) := by
    rw [hdot]
    exact fixed_one_one
  let ι := (Fin (b + 1) × Fin (b + 1)) ⊕ Unit
  let U : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (i, j) => uD i j
    | Sum.inr () => A 1 - ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y • uD x y
  let V : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (a, c) =>
        ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), (Hinv (K := K) a x * Hinv (K := K) c y) • vD x y
    | Sum.inr () => B 1 - ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y • vD x y
  have hsum_Hinv_D : ∀ i j,
      ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * (H i x * H j y) = H i j := by
    intro i j
    have h1 :
        ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * (H i x * H j y) =
          ∑ x : Fin (b + 1), H (K := K) i x * (∑ y : Fin (b + 1), H j y * Hinv y x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Hinv_comm x y]
      ring
    rw [h1]
    have h2 :
        ∑ x : Fin (b + 1), H (K := K) i x * (∑ y : Fin (b + 1), H j y * Hinv y x) =
          ∑ x : Fin (b + 1), H (K := K) i x * delta j x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [H_mul_Hinv hq]
    rw [h2, Finset.sum_eq_single j]
    · unfold delta
      simp
    · intro x _ hxj
      unfold delta
      have hne : j ≠ x := Ne.symm hxj
      simp [hne]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hUV : ∀ α β : ι, dot (U α) (V β) = delta α β := by
    intro α β
    cases α with
    | inl ij =>
      rcases ij with ⟨i, j⟩
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        simp only [U, V, dot_sum_right, dot_smul_right, hDD]
        have hfac :
            ∑ x : Fin (b + 1), ∑ y : Fin (b + 1),
                Hinv (K := K) a x * Hinv c y * (H i x * H j y) =
              (∑ x : Fin (b + 1), H (K := K) i x * Hinv x a) *
                (∑ y : Fin (b + 1), H (K := K) j y * Hinv y c) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [Hinv_comm a x, Hinv_comm c y]
          ring
        rw [hfac, H_mul_Hinv hq, H_mul_Hinv hq]
        unfold delta
        dsimp only [ι]
        by_cases hia : i = a <;> by_cases hjc : j = c <;> simp [hia, hjc]
      | inr u =>
        cases u
        simp only [U, V, dot_sub_right, dot_sum_right, dot_smul_right, hD1, hDD]
        rw [hsum_Hinv_D i j, sub_self]
        unfold delta
        simp
    | inr u =>
      cases u
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        have hzero : ∀ x y, dot (U (Sum.inr ())) (vD x y) = 0 := by
          intro x y
          simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h1D, hDD]
          have hcomm :
              ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H s x * H t y) =
                ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H x s * H y t) := by
            refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
            rw [H_comm s x, H_comm t y]
          rw [hcomm, hsum_Hinv_D x y, sub_self]
        simp only [V, dot_sum_right, dot_smul_right, hzero, mul_zero, Finset.sum_const_zero]
        unfold delta
        simp
      | inr v =>
        cases v
        have hzero : ∀ x y, dot (U (Sum.inr ())) (vD x y) = 0 := by
          intro x y
          simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h1D, hDD]
          have hcomm :
              ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H s x * H t y) =
                ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H x s * H y t) := by
            refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
            rw [H_comm s x, H_comm t y]
          rw [hcomm, hsum_Hinv_D x y, sub_self]
        simp only [V, dot_sub_right, dot_sum_right, dot_smul_right, hzero, mul_zero,
          Finset.sum_const_zero, sub_zero]
        simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h11, hD1]
        have htr :
            ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * H x y = ((b + 1 : ℕ) : K) := by
          have h1 :
              ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * H x y =
                ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), H (K := K) x y * Hinv y x := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [Hinv_comm x y, mul_comm]
          rw [h1]
          have h2 :
              ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), H (K := K) x y * Hinv y x =
                ∑ x : Fin (b + 1), delta (K := K) x x := by
            refine Finset.sum_congr rfl (fun x _ => H_mul_Hinv hq x x)
          rw [h2]
          simp [delta]
        rw [htr]
        unfold delta
        simp only [↓reduceIte]
        push_cast
        ring
  have hcard := card_le_of_biorthogonal U V hUV
  simpa [ι, sq] using hcard

lemma lower_bound_div_char2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0)
    (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r,
      (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
        ∑ j : Fin d, A p j * B r j) :
    b ^ 2 ≤ d := by
  have hdot : ∀ p r, dot (A p) (B r) = ∑ k : Fin (b + 2), delta (K := K) (r (p k)) k := by
    intro p r
    rw [← fixed_cast]
    exact (hAB p r).symm
  let uD : Fin b → Fin b → Fin d → K := fun i j => A (p1 i.castSucc j.castSucc) - A (p2 i.castSucc j.castSucc)
  let vD : Fin b → Fin b → Fin d → K := fun a c => B (p1 c.castSucc a.castSucc) - B (p2 c.castSucc a.castSucc)
  have hH_cast : ∀ (i j : Fin b), H (K := K) i.castSucc j.castSucc = H i j := by
    intro i j
    unfold H delta
    simp [Fin.castSucc_inj]
  have hDD : ∀ i j a c, dot (uD i j) (vD a c) = H i a * H j c := by
    intro i j a c
    simp only [uD, vD, dot_sub_left, dot_sub_right, hdot]
    rw [fixed_diff_both i.castSucc j.castSucc a.castSucc c.castSucc, hH_cast, hH_cast]
  let ι := Fin b × Fin b
  let U : ι → Fin d → K := fun x => uD x.1 x.2
  let V : ι → Fin d → K := fun x =>
    ∑ s : Fin b, ∑ t : Fin b, (H (K := K) x.1 s * H (K := K) x.2 t) • vD s t
  have hUV : ∀ α β : ι, dot (U α) (V β) = delta α β := by
    intro α β
    rcases α with ⟨i, j⟩
    rcases β with ⟨a, c⟩
    simp only [U, V, dot_sum_right, dot_smul_right, hDD]
    have hfac :
        ∑ s : Fin b, ∑ t : Fin b, H (K := K) a s * H c t * (H i s * H j t) =
          (∑ s : Fin b, H (K := K) i s * H s a) * (∑ t : Fin b, H (K := K) j t * H t c) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [H_comm a s, H_comm c t]
      ring
    rw [hfac, H_mul_H_of_char hq, H_mul_H_of_char hq]
    unfold delta
    dsimp only [ι]
    by_cases hia : i = a <;> by_cases hjc : j = c <;> simp [hia, hjc]
  have hcard := card_le_of_biorthogonal U V hUV
  simpa [ι, sq] using hcard

lemma lower_bound_div_ne2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0) (h2 : (2 : K) ≠ 0)
    (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r,
      (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
        ∑ j : Fin d, A p j * B r j) :
    b ^ 2 + 1 ≤ d := by
  have hdot : ∀ p r, dot (A p) (B r) = ∑ k : Fin (b + 2), delta (K := K) (r (p k)) k := by
    intro p r
    rw [← fixed_cast]
    exact (hAB p r).symm
  let uD : Fin b → Fin b → Fin d → K := fun i j => A (p1 i.castSucc j.castSucc) - A (p2 i.castSucc j.castSucc)
  let vD : Fin b → Fin b → Fin d → K := fun a c => B (p1 c.castSucc a.castSucc) - B (p2 c.castSucc a.castSucc)
  have hH_cast : ∀ (i j : Fin b), H (K := K) i.castSucc j.castSucc = H i j := by
    intro i j
    unfold H delta
    simp [Fin.castSucc_inj]
  have hDD : ∀ i j a c, dot (uD i j) (vD a c) = H i a * H j c := by
    intro i j a c
    simp only [uD, vD, dot_sub_left, dot_sub_right, hdot]
    rw [fixed_diff_both i.castSucc j.castSucc a.castSucc c.castSucc, hH_cast, hH_cast]
  have hD1 : ∀ i j, dot (uD i j) (B 1) = H i j := by
    intro i j
    simp only [uD, dot_sub_left, hdot]
    rw [fixed_diff_one i.castSucc j.castSucc, hH_cast]
  have h1D : ∀ a c, dot (A 1) (vD a c) = H a c := by
    intro a c
    simp only [vD, dot_sub_right, hdot]
    rw [fixed_one_diff a.castSucc c.castSucc, hH_cast]
  have h11 : dot (A 1) (B 1) = ((b + 2 : ℕ) : K) := by
    rw [hdot]
    exact fixed_one_one
  have hsum_H_D : ∀ i j,
      ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * (H i x * H j y) = H i j := by
    intro i j
    have h1 :
        ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * (H i x * H j y) =
          ∑ x : Fin b, H (K := K) i x * (∑ y : Fin b, H j y * H y x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [H_comm x y]
      ring
    rw [h1]
    have h2' :
        ∑ x : Fin b, H (K := K) i x * (∑ y : Fin b, H j y * H y x) =
          ∑ x : Fin b, H (K := K) i x * delta j x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [H_mul_H_of_char hq]
    rw [h2', Finset.sum_eq_single j]
    · unfold delta
      simp
    · intro x _ hxj
      unfold delta
      have hne : j ≠ x := Ne.symm hxj
      simp [hne]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  let ι := (Fin b × Fin b) ⊕ Unit
  let U : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (i, j) => uD i j
    | Sum.inr () => A 1 - ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y • uD x y
  let V : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (a, c) =>
        ∑ x : Fin b, ∑ y : Fin b, (H (K := K) a x * H (K := K) c y) • vD x y
    | Sum.inr () => (2 : K)⁻¹ • (B 1 - ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y • vD x y)
  have hUV : ∀ α β : ι, dot (U α) (V β) = delta α β := by
    intro α β
    cases α with
    | inl ij =>
      rcases ij with ⟨i, j⟩
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        simp only [U, V, dot_sum_right, dot_smul_right, hDD]
        have hfac :
            ∑ x : Fin b, ∑ y : Fin b, H (K := K) a x * H c y * (H i x * H j y) =
              (∑ x : Fin b, H (K := K) i x * H x a) * (∑ y : Fin b, H (K := K) j y * H y c) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [H_comm a x, H_comm c y]
          ring
        rw [hfac, H_mul_H_of_char hq, H_mul_H_of_char hq]
        unfold delta
        dsimp only [ι]
        by_cases hia : i = a <;> by_cases hjc : j = c <;> simp [hia, hjc]
      | inr u =>
        cases u
        simp only [U, V, dot_smul_right, dot_sub_right, dot_sum_right, hD1, hDD]
        rw [hsum_H_D i j, sub_self, mul_zero]
        unfold delta
        simp
    | inr u =>
      cases u
      have hzero : ∀ x y, dot (U (Sum.inr ())) (vD x y) = 0 := by
        intro x y
        simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h1D, hDD]
        have hcomm :
            ∑ s : Fin b, ∑ t : Fin b, H (K := K) s t * (H s x * H t y) =
              ∑ s : Fin b, ∑ t : Fin b, H (K := K) s t * (H x s * H y t) := by
          refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
          rw [H_comm s x, H_comm t y]
        rw [hcomm, hsum_H_D x y, sub_self]
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        simp only [V, dot_sum_right, dot_smul_right, hzero, mul_zero, Finset.sum_const_zero]
        unfold delta
        simp
      | inr v =>
        cases v
        simp only [V, dot_smul_right, dot_sub_right, dot_sum_right, hzero, mul_zero,
          Finset.sum_const_zero, sub_zero]
        simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h11, hD1]
        have htr :
            ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H x y = (b : K) := by
          have h1 :
              ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H x y =
                ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H y x := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [H_comm x y]
          rw [h1]
          have h2' :
              ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H y x =
                ∑ x : Fin b, delta (K := K) x x := by
            refine Finset.sum_congr rfl (fun x _ => H_mul_H_of_char hq x x)
          rw [h2']
          simp [delta]
        rw [htr]
        unfold delta
        simp only [↓reduceIte]
        have hdiff : ((b + 2 : ℕ) : K) - (b : K) = 2 := by
          push_cast
          ring
        rw [hdiff, inv_mul_cancel₀ h2]
  have hcard := card_le_of_biorthogonal U V hUV
  simpa [ι, sq] using hcard

end PEqualNP.Outside.L_lib_591_aux

theorem PEqualNP.Outside.L_lib_591 : (∀ (K : Type) [Field K] (b d : ℕ),
  let q := b + 2
  let P := Equiv.Perm (Fin q)
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card
  let threshold := if ringChar K ∣ q then
      (q - 2) ^ 2 + (if ringChar K = 2 then 0 else 1)
    else (q - 1) ^ 2 + 1
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    threshold ≤ d) := by
  intro K _ b d
  dsimp only
  by_cases hdiv : ringChar K ∣ b + 2
  · have hq : ((b + 2 : ℕ) : K) = 0 := (PEqualNP.Outside.L_lib_591_aux.ringChar_dvd_iff (b + 2)).mp hdiv
    by_cases h2 : ringChar K = 2
    · have h2K : (2 : K) = 0 := (PEqualNP.Outside.L_lib_591_aux.ringChar_eq_two_iff).mp h2
      simp only [hdiv, ↓reduceIte]
      simp only [h2, ↓reduceIte, Nat.add_sub_cancel, add_zero]
      constructor
      · rintro ⟨A, B, hAB⟩
        exact PEqualNP.Outside.L_lib_591_aux.lower_bound_div_char2 b d hq A B hAB
      · intro hd
        exact PEqualNP.Outside.L_lib_591_aux.upper_bound_div_char2 b d hq h2K hd
    · have h2K : (2 : K) ≠ 0 := by
        intro hc
        exact h2 ((PEqualNP.Outside.L_lib_591_aux.ringChar_eq_two_iff).mpr hc)
      simp only [hdiv, ↓reduceIte]
      simp only [h2, ↓reduceIte, Nat.add_sub_cancel]
      constructor
      · rintro ⟨A, B, hAB⟩
        exact PEqualNP.Outside.L_lib_591_aux.lower_bound_div_ne2 b d hq h2K A B hAB
      · intro hd
        exact PEqualNP.Outside.L_lib_591_aux.upper_bound_div_ne2 b d hq hd
  · have hq : ((b + 2 : ℕ) : K) ≠ 0 := by
      intro hc
      exact hdiv ((PEqualNP.Outside.L_lib_591_aux.ringChar_dvd_iff (b + 2)).mpr hc)
    simp only [hdiv, ↓reduceIte]
    have hsub : b + 2 - 1 = b + 1 := by omega
    rw [hsub]
    constructor
    · rintro ⟨A, B, hAB⟩
      exact PEqualNP.Outside.L_lib_591_aux.lower_bound_nondiv b d hq A B hAB
    · intro hd
      exact PEqualNP.Outside.L_lib_591_aux.upper_bound_nondiv b d hd
