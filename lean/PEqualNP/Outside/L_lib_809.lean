import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_809_aux

private abbrev F2 := ZMod 2

private lemma z2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma z2_ne_zero_iff (a : F2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

private def sgn (a : F2) : ℤ := if a = 0 then 1 else -1

private lemma sgn_add (a b : F2) : sgn (a + b) = sgn a * sgn b := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> rcases z2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma sgn_add_one (a : F2) : sgn (a + 1) = - sgn a := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma sgn_mul_self (a : F2) : sgn a * sgn a = 1 := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma sgn_abs_le_one (a : F2) : |sgn a| = 1 := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma sgn_eq_ite (a b : F2) :
    sgn (a + b) = 2 * (if a = b then (1 : ℤ) else 0) - 1 := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> rcases z2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma dot_add_right {k : ℕ} (x y z : Fin k → F2) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dot_add_left {k : ℕ} (x y z : Fin k → F2) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_smul_left {k : ℕ} (c : F2) (x y : Fin k → F2) :
    dotProduct (c • x) y = c * dotProduct x y := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma dot_sum_left {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin k → F2)) (y : Fin k → F2) :
    dotProduct (∑ i ∈ s, f i) y = ∑ i ∈ s, dotProduct (f i) y := by
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private lemma sum_sgn_dot_eq_zero {k : ℕ} (z : Fin k → F2) (hz : z ≠ 0) :
    ∑ x : Fin k → F2, sgn (dotProduct z x) = 0 := by
  have hex : ∃ t : Fin k, z t = 1 := by
    by_contra hnot
    push Not at hnot
    apply hz
    funext t
    rcases z2_eq_zero_or_one (z t) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot t)
  obtain ⟨t, ht⟩ := hex
  let h : Fin k → F2 := Pi.single t 1
  have hzh : dotProduct z h = 1 := by
    simp only [dotProduct, h, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, ht]
  have hshift : ∑ x : Fin k → F2, sgn (dotProduct z x) =
      ∑ x : Fin k → F2, sgn (dotProduct z (x + h)) :=
    (Equiv.sum_comp (Equiv.addRight h) (fun x => sgn (dotProduct z x))).symm
  have hneg : ∑ x : Fin k → F2, sgn (dotProduct z (x + h)) =
      - ∑ x : Fin k → F2, sgn (dotProduct z x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [dot_add_right, hzh, sgn_add_one]
  omega

private lemma sum_sgn_dot_right_eq_zero {k : ℕ} (z : Fin k → F2) (hz : z ≠ 0) :
    ∑ w : Fin k → F2, sgn (dotProduct w z) = 0 := by
  have hcomm : ∀ w : Fin k → F2, dotProduct w z = dotProduct z w := fun w => dotProduct_comm w z
  simp_rw [hcomm]
  exact sum_sgn_dot_eq_zero z hz

private lemma exists_ker_separator {k d : ℕ} (p : Fin d → (Fin k → F2)) (z : Fin k → F2)
    (hz : z ∉ Submodule.span F2 (Set.range p)) :
    ∃ h : Fin k → F2, (∀ i : Fin d, dotProduct (p i) h = 0) ∧ dotProduct z h = 1 := by
  classical
  let K : Submodule F2 (Fin k → F2) := Submodule.span F2 (Set.range p)
  let q := K.mkQ z
  have hq_ne : q ≠ 0 := fun h0 => hz ((Submodule.Quotient.mk_eq_zero K).mp h0)
  let b := Module.Basis.ofVectorSpace F2 ((Fin k → F2) ⧸ K)
  have hrepr_ne : b.repr q ≠ 0 := fun h0 => hq_ne (b.repr.injective (by simpa using h0))
  have hex : ∃ idx, (b.repr q) idx ≠ 0 := by
    by_contra hnot
    push Not at hnot
    exact hrepr_ne (Finsupp.ext hnot)
  obtain ⟨idx, hidx⟩ := hex
  let ℓ : (Fin k → F2) →ₗ[F2] F2 := (Finsupp.lapply idx).comp (b.repr.toLinearMap.comp K.mkQ)
  have hℓK : ∀ y ∈ K, ℓ y = 0 := by
    intro y hy
    dsimp only [ℓ, LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hy, map_zero,
      Finsupp.lapply_apply, Finsupp.zero_apply]
  have hℓz : ℓ z = 1 := (z2_ne_zero_iff _).mp hidx
  let h : Fin k → F2 := fun t => ℓ (Pi.single t 1)
  have hdot_eq : ∀ w : Fin k → F2, dotProduct w h = ℓ w := by
    intro w
    have hw : w = ∑ t : Fin k, w t • Pi.single t (1 : F2) := by
      funext s
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hw]
    rw [map_sum]
    simp only [dotProduct, h, map_smul, smul_eq_mul]
  refine ⟨h, fun i => ?_, ?_⟩
  · rw [hdot_eq (p i)]
    exact hℓK (p i) (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hdot_eq z, hℓz]

private lemma mem_span_range_iff {k d : ℕ} (p : Fin d → (Fin k → F2)) (z : Fin k → F2) :
    z ∈ Submodule.span F2 (Set.range p) ↔ ∃ w : Fin d → F2, z = ∑ i : Fin d, w i • p i := by
  constructor
  · intro hz
    have hmem : z ∈ LinearMap.range (Fintype.linearCombination F2 p) := by
      rwa [Fintype.range_linearCombination]
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma sq_sum_le_card_mul_sum_sq_int {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (f i) ^ 2 := by
  have hnn : (0 : ℤ) ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
      2 * ((s.card : ℤ) * ∑ i ∈ s, (f i) ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
    have h1 : ∀ i j : ι, (f i - f j) ^ 2 = f i ^ 2 - 2 * (f i * f j) + f j ^ 2 := fun i j => by ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

private lemma parseval_f2 {k : ℕ} (f : (Fin k → F2) → ℤ) (hf : ∀ x, f x * f x = 1) :
    ∑ w : Fin k → F2, (∑ x : Fin k → F2, f x * sgn (dotProduct w x)) ^ 2 = ((2 ^ k : ℕ) : ℤ) ^ 2 := by
  have hsq : ∀ w : Fin k → F2,
      (∑ x : Fin k → F2, f x * sgn (dotProduct w x)) ^ 2 =
      ∑ x : Fin k → F2, ∑ y : Fin k → F2, f x * f y * sgn (dotProduct w (x + y)) := by
    intro w
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [dot_add_right, sgn_add]
    ring
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hinner : ∀ x : Fin k → F2,
      ∑ w : Fin k → F2, ∑ y : Fin k → F2, f x * f y * sgn (dotProduct w (x + y)) = (2 ^ k : ℕ) := by
    intro x
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single x]
    · have hxx : x + x = 0 := by funext t; exact z2_add_self (x t)
      simp only [hxx, dotProduct_zero, show sgn 0 = 1 by decide, mul_one, hf x,
        Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, ZMod.card,
        Finset.prod_const, nsmul_eq_mul]
    · intro y _ hyx
      rw [← Finset.mul_sum]
      have hne : x + y ≠ 0 := by
        intro h0
        apply hyx
        funext t
        have ht := congrFun h0 t
        dsimp only [Pi.add_apply, Pi.zero_apply] at ht
        have hxx := z2_add_self (x t)
        linear_combination ht - hxx
      rw [sum_sgn_dot_right_eq_zero (x + y) hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, ZMod.card,
    Finset.prod_const, nsmul_eq_mul, sq]

private lemma card_V_eq (k : ℕ) : Fintype.card (Fin k → F2) = 2 ^ k := by
  simp [Fintype.card_pi, ZMod.card]

private lemma sgain_eq {k m d : ℕ} (v : Fin m ↪ (Fin k → F2)) (p : Fin d → (Fin k → F2))
    (a : Fin k → F2) (K : Finset (Fin m)) (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2) :
    let sig := fun (x : Fin k → F2) => dotProduct a x + u (fun i => dotProduct (p i) x)
    ((2 * ∑ x : Fin k → F2, (K.filter (fun j => dec (sig x) j = dotProduct (v j) x)).card : ℕ) : ℤ) -
      ((2 ^ k * K.card : ℕ) : ℤ) =
    ∑ j ∈ K, ∑ x : Fin k → F2, sgn (dec (sig x) j + dotProduct (v j) x) := by
  intro sig
  rw [Finset.sum_comm]
  have h1 : ∀ x : Fin k → F2,
      ∑ j ∈ K, sgn (dec (sig x) j + dotProduct (v j) x) =
      2 * ((K.filter (fun j => dec (sig x) j = dotProduct (v j) x)).card : ℤ) - (K.card : ℤ) := by
    intro x
    simp_rw [sgn_eq_ite]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    card_V_eq k, nsmul_eq_mul]
  push_cast
  ring

private lemma mass_term_eq {k m : ℕ} (v : Fin m ↪ (Fin k → F2)) (J : Finset (Fin m))
    (e : Fin m → F2) (x : Fin k → F2) :
    ∑ j ∈ J, sgn (dotProduct (v j) x + e j) =
      (J.card : ℤ) - 2 * ((J.filter (fun j => dotProduct (v j) x + e j = 1)).card : ℤ) := by
  have hterm : ∀ j ∈ J, sgn (dotProduct (v j) x + e j) =
      (1 : ℤ) - 2 * (if dotProduct (v j) x + e j = 1 then (1 : ℤ) else 0) := by
    intro j _
    rcases z2_eq_zero_or_one (dotProduct (v j) x + e j) with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]

private lemma nat_sub_le_of_int_le {a b c : ℕ} (h : (a : ℤ) - (b : ℤ) ≤ (c : ℤ)) :
    a - b ≤ c := by
  omega

private lemma nat_sub_eq_of_int_eq {a b c : ℕ} (h : (a : ℤ) - (b : ℤ) = (c : ℤ)) :
    a - b = c := by
  omega

private lemma main_809 (k m d : ℕ)
    (v : Fin m ↪ (Fin k → F2)) (hv0 : ∀ j, v j ≠ 0)
    (p : Fin d → (Fin k → F2)) (a : Fin k → F2) (K : Finset (Fin m)) :
    let J := K.filter (fun j => ∃ w : Fin d → F2, v j = a + ∑ i : Fin d, w i • p i)
    let sig := fun (u : (Fin d → F2) → F2) (x : Fin k → F2) =>
      dotProduct a x + u (fun i => dotProduct (p i) x)
    let gain := fun (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2) =>
      2 * (∑ x : Fin k → F2, (K.filter (fun j => dec (sig u x) j = dotProduct (v j) x)).card) -
        2 ^ k * K.card
    let mass := fun (e : Fin m → F2) => ∑ x : Fin k → F2,
      let n := (J.filter (fun j => dotProduct (v j) x + e j = 1)).card
      ((J.card : ℤ) - 2 * (n : ℤ)).natAbs
    (∀ u dec, ∃ e, gain u dec ≤ mass e) ∧
    (∀ e, ∃ u dec, gain u dec = mass e) ∧
    (∀ u dec, (gain u dec) ^ 2 ≤ J.card * (2 ^ k) ^ 2) := by
  intro J sig gain mass
  have hcol_zero_const : ∀ (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2) (j : Fin m),
      dec 0 j = dec 1 j →
      ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) = 0 := by
    intro u dec j hconst
    have hdec : ∀ b : F2, dec b j = dec 0 j := by
      intro b
      rcases z2_eq_zero_or_one b with rfl | rfl
      · rfl
      · exact hconst.symm
    have heq : ∀ x : Fin k → F2,
        sgn (dec (sig u x) j + dotProduct (v j) x) = sgn (dec 0 j) * sgn (dotProduct (v j) x) := by
      intro x
      rw [hdec (sig u x), sgn_add]
    simp_rw [heq, ← Finset.mul_sum, sum_sgn_dot_eq_zero (v j) (hv0 j), mul_zero]
  have hcol_nonconst : ∀ (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2) (j : Fin m),
      dec 0 j ≠ dec 1 j →
      ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) =
        sgn (dec 0 j) * ∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x) := by
    intro u dec j hne
    have hdec : ∀ b : F2, dec b j = b + dec 0 j := by
      intro b
      rcases z2_eq_zero_or_one b with rfl | rfl
      · simp
      · rcases z2_eq_zero_or_one (dec 0 j) with h0 | h1 <;>
          rcases z2_eq_zero_or_one (dec 1 j) with h0' | h1'
        · exact absurd (h0.trans h0'.symm) hne
        · rw [h0, h1']; decide
        · rw [h1, h0']; decide
        · exact absurd (h1.trans h1'.symm) hne
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hdec (sig u x), show sig u x + dec 0 j + dotProduct (v j) x =
      dec 0 j + (sig u x + dotProduct (v j) x) by ring, sgn_add]
  have hcol_outside : ∀ (u : (Fin d → F2) → F2) (j : Fin m),
      j ∈ K → j ∉ J →
      ∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x) = 0 := by
    intro u j hjK hjJ
    have hnotspan : v j + a ∉ Submodule.span F2 (Set.range p) := by
      intro hmem
      apply hjJ
      refine Finset.mem_filter.mpr ⟨hjK, ?_⟩
      obtain ⟨w, hw⟩ := (mem_span_range_iff p (v j + a)).mp hmem
      refine ⟨w, ?_⟩
      have haa : a + a = 0 := by funext t; exact z2_add_self (a t)
      calc v j = v j + (a + a) := by rw [haa, add_zero]
        _ = a + (v j + a) := by abel
        _ = a + ∑ i : Fin d, w i • p i := by rw [hw]
    obtain ⟨h, hph, hzh⟩ := exists_ker_separator p (v j + a) hnotspan
    have hshift : ∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x) =
        ∑ x : Fin k → F2, sgn (sig u (x + h) + dotProduct (v j) (x + h)) :=
      (Equiv.sum_comp (Equiv.addRight h) (fun x => sgn (sig u x + dotProduct (v j) x))).symm
    have hneg : ∑ x : Fin k → F2, sgn (sig u (x + h) + dotProduct (v j) (x + h)) =
        - ∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hP : (fun i : Fin d => dotProduct (p i) (x + h)) = (fun i : Fin d => dotProduct (p i) x) := by
        funext i
        rw [dot_add_right, hph i, add_zero]
      have harg : sig u (x + h) + dotProduct (v j) (x + h) =
          (sig u x + dotProduct (v j) x) + 1 := by
        dsimp only [sig]
        rw [hP, dot_add_right, dot_add_right]
        have hsum : dotProduct a h + dotProduct (v j) h = 1 := by
          rw [add_comm, ← dot_add_left, hzh]
        linear_combination hsum
      rw [harg, sgn_add_one]
    omega
  have hcol_zero_outside : ∀ (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2) (j : Fin m),
      j ∈ K → j ∉ J →
      ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) = 0 := by
    intro u dec j hjK hjJ
    by_cases hconst : dec 0 j = dec 1 j
    · exact hcol_zero_const u dec j hconst
    · rw [hcol_nonconst u dec j hconst, hcol_outside u j hjK hjJ, mul_zero]
  have hsgain_J : ∀ (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2),
      ∑ j ∈ K, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) =
      ∑ j ∈ J, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) := by
    intro u dec
    have hsub : J ⊆ K := Finset.filter_subset _ K
    rw [← Finset.sum_subset hsub]
    intro j hjK hjJ
    exact hcol_zero_outside u dec j hjK hjJ
  have hcol_le_abs : ∀ (u : (Fin d → F2) → F2) (dec : F2 → Fin m → F2) (j : Fin m),
      ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) ≤
        |∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x)| := by
    intro u dec j
    by_cases hconst : dec 0 j = dec 1 j
    · rw [hcol_zero_const u dec j hconst]
      exact abs_nonneg _
    · rw [hcol_nonconst u dec j hconst]
      rcases z2_eq_zero_or_one (dec 0 j) with h0 | h1
      · rw [h0, show sgn 0 = 1 by decide, one_mul]; exact le_abs_self _
      · rw [h1, show sgn 1 = -1 by decide, neg_one_mul]; exact neg_le_abs _
  refine ⟨?_, ?_, ?_⟩
  · intro u dec
    let r : Fin m → ℤ := fun j => ∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x)
    let e : Fin m → F2 := fun j => if 0 ≤ r j then 0 else 1
    refine ⟨e, ?_⟩
    apply nat_sub_le_of_int_le
    have hcast_lhs : ((2 * ∑ x : Fin k → F2, (K.filter (fun j => dec (sig u x) j = dotProduct (v j) x)).card : ℕ) : ℤ) -
        ((2 ^ k * K.card : ℕ) : ℤ) =
        ∑ j ∈ J, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) := by
      rw [sgain_eq v p a K u dec, hsgain_J]
    rw [hcast_lhs]
    have hle1 : ∑ j ∈ J, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) ≤
        ∑ j ∈ J, |r j| :=
      Finset.sum_le_sum fun j _ => hcol_le_abs u dec j
    have habs_eq : ∀ j : Fin m, |r j| = sgn (e j) * r j := by
      intro j
      dsimp only [e]
      split_ifs with hnn
      · rw [show sgn 0 = 1 by decide, one_mul, abs_of_nonneg hnn]
      · push Not at hnn
        rw [show sgn 1 = -1 by decide, neg_one_mul, abs_of_neg hnn]
    have hsum_abs : ∑ j ∈ J, |r j| =
        ∑ x : Fin k → F2, sgn (sig u x) * ∑ j ∈ J, sgn (dotProduct (v j) x + e j) := by
      simp_rw [habs_eq, r, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sgn_add (sig u x), sgn_add (dotProduct (v j) x)]
      ring
    have hle2 : ∑ x : Fin k → F2, sgn (sig u x) * ∑ j ∈ J, sgn (dotProduct (v j) x + e j) ≤
        ∑ x : Fin k → F2, |∑ j ∈ J, sgn (dotProduct (v j) x + e j)| := by
      refine Finset.sum_le_sum fun x _ => ?_
      calc sgn (sig u x) * ∑ j ∈ J, sgn (dotProduct (v j) x + e j)
          ≤ |sgn (sig u x) * ∑ j ∈ J, sgn (dotProduct (v j) x + e j)| := le_abs_self _
        _ = |sgn (sig u x)| * |∑ j ∈ J, sgn (dotProduct (v j) x + e j)| := abs_mul _ _
        _ = |∑ j ∈ J, sgn (dotProduct (v j) x + e j)| := by rw [sgn_abs_le_one, one_mul]
    have hmass_eq : (mass e : ℤ) = ∑ x : Fin k → F2, |∑ j ∈ J, sgn (dotProduct (v j) x + e j)| := by
      dsimp only [mass]
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mass_term_eq v J e x]
    rw [hmass_eq]
    linarith
  · intro e
    classical
    have hex_w : ∀ j : Fin m, ∃ w : Fin d → F2, j ∈ J → v j = a + ∑ i : Fin d, w i • p i := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hj).2
        exact ⟨w, fun _ => hw⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose wOf hwOf using hex_w
    let g : (Fin d → F2) → ℤ := fun y =>
      ∑ j ∈ J, sgn ((∑ i : Fin d, wOf j i * y i) + e j)
    let u : (Fin d → F2) → F2 := fun y => if 0 ≤ g y then 0 else 1
    let dec : F2 → Fin m → F2 := fun b j => if j ∈ J then b + e j else 0
    refine ⟨u, dec, ?_⟩
    apply nat_sub_eq_of_int_eq
    have hsg : ((2 * ∑ x : Fin k → F2, (K.filter (fun j => dec (sig u x) j = dotProduct (v j) x)).card : ℕ) : ℤ) -
        ((2 ^ k * K.card : ℕ) : ℤ) =
        ∑ j ∈ J, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) := by
      rw [sgain_eq v p a K u dec, hsgain_J]
    rw [hsg, Finset.sum_comm]
    have hmass_eq : (mass e : ℤ) = ∑ x : Fin k → F2, |∑ j ∈ J, sgn (dotProduct (v j) x + e j)| := by
      dsimp only [mass]
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mass_term_eq v J e x]
    rw [hmass_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    let Px : Fin d → F2 := fun i => dotProduct (p i) x
    have hdot_v : ∀ j ∈ J, dotProduct (v j) x = dotProduct a x + ∑ i : Fin d, wOf j i * Px i := by
      intro j hj
      rw [hwOf j hj, dot_add_left, dot_sum_left]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dot_smul_left]
    have hlhs : ∑ j ∈ J, sgn (dec (sig u x) j + dotProduct (v j) x) = sgn (u Px) * g Px := by
      dsimp only [g]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hdecj : dec (sig u x) j = sig u x + e j := by simp only [dec, hj, ↓reduceIte]
      rw [hdecj, hdot_v j hj]
      dsimp only [sig]
      have haa : dotProduct a x + dotProduct a x = 0 := z2_add_self _
      have harg : dotProduct a x + u Px + e j + (dotProduct a x + ∑ i : Fin d, wOf j i * Px i) =
          u Px + ((∑ i : Fin d, wOf j i * Px i) + e j) := by
        linear_combination haa
      rw [harg, sgn_add]
    have hrhs : ∑ j ∈ J, sgn (dotProduct (v j) x + e j) = sgn (dotProduct a x) * g Px := by
      dsimp only [g]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hdot_v j hj, add_assoc, sgn_add]
    rw [hlhs, hrhs, abs_mul, sgn_abs_le_one, one_mul]
    dsimp only [u]
    split_ifs with hnn
    · rw [show sgn 0 = 1 by decide, one_mul, abs_of_nonneg hnn]
    · push Not at hnn
      rw [show sgn 1 = -1 by decide, neg_one_mul, abs_of_neg hnn]
  · intro u dec
    let r : Fin m → ℤ := fun j => ∑ x : Fin k → F2, sgn (sig u x + dotProduct (v j) x)
    have hsg : ((2 * ∑ x : Fin k → F2, (K.filter (fun j => dec (sig u x) j = dotProduct (v j) x)).card : ℕ) : ℤ) -
        ((2 ^ k * K.card : ℕ) : ℤ) =
        ∑ j ∈ J, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) := by
      rw [sgain_eq v p a K u dec, hsgain_J]
    have hgain_le : (gain u dec : ℤ) ≤ ∑ j ∈ J, |r j| := by
      have hsum_le : ∑ j ∈ J, ∑ x : Fin k → F2, sgn (dec (sig u x) j + dotProduct (v j) x) ≤
          ∑ j ∈ J, |r j| := Finset.sum_le_sum fun j _ => hcol_le_abs u dec j
      have hnn : (0 : ℤ) ≤ ∑ j ∈ J, |r j| := Finset.sum_nonneg fun j _ => abs_nonneg _
      dsimp only [gain]
      omega
    have hsq_le : ((gain u dec : ℤ)) ^ 2 ≤ (∑ j ∈ J, |r j|) ^ 2 :=
      pow_le_pow_left₀ (Int.natCast_nonneg _) hgain_le 2
    have hcs : (∑ j ∈ J, |r j|) ^ 2 ≤ (J.card : ℤ) * ∑ j ∈ J, |r j| ^ 2 :=
      sq_sum_le_card_mul_sum_sq_int J (fun j => |r j|)
    have hsum_sq : ∑ j ∈ J, |r j| ^ 2 ≤ ((2 ^ k : ℕ) : ℤ) ^ 2 := by
      have h1 : ∀ j : Fin m, |r j| ^ 2 = (∑ x : Fin k → F2, sgn (sig u x) * sgn (dotProduct (v j) x)) ^ 2 := by
        intro j
        rw [sq_abs]
        congr 1
        refine Finset.sum_congr rfl fun x _ => sgn_add _ _
      simp_rw [h1]
      have hinj : ∑ j ∈ J, (∑ x : Fin k → F2, sgn (sig u x) * sgn (dotProduct (v j) x)) ^ 2 =
          ∑ w ∈ J.image v, (∑ x : Fin k → F2, sgn (sig u x) * sgn (dotProduct w x)) ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ h => v.injective h)]
      rw [hinj]
      calc ∑ w ∈ J.image v, (∑ x : Fin k → F2, sgn (sig u x) * sgn (dotProduct w x)) ^ 2
          ≤ ∑ w : Fin k → F2, (∑ x : Fin k → F2, sgn (sig u x) * sgn (dotProduct w x)) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun w => sq_nonneg _
        _ = ((2 ^ k : ℕ) : ℤ) ^ 2 :=
            parseval_f2 (fun x => sgn (sig u x)) (fun x => sgn_mul_self _)
    have hfinal : ((gain u dec : ℤ)) ^ 2 ≤ (J.card : ℤ) * ((2 ^ k : ℕ) : ℤ) ^ 2 := by
      calc ((gain u dec : ℤ)) ^ 2
          ≤ (∑ j ∈ J, |r j|) ^ 2 := hsq_le
        _ ≤ (J.card : ℤ) * ∑ j ∈ J, |r j| ^ 2 := hcs
        _ ≤ (J.card : ℤ) * ((2 ^ k : ℕ) : ℤ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsum_sq (Int.natCast_nonneg _)
    exact_mod_cast hfinal

end PEqualNP.Outside.L_lib_809_aux

theorem PEqualNP.Outside.L_lib_809 : ∀ (k m d : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  let U := Fin d → F
  let dot := fun (x y : V) => dotProduct x y
  ∀ (v : Fin m ↪ V), (∀ j, v j ≠ 0) →
  ∀ (p : Fin d → V) (a : V) (K : Finset (Fin m)),
    let J := K.filter (fun j => ∃ w : U, v j = a + ∑ i : Fin d, w i • p i)
    let sig := fun (u : U → F) (x : V) => dot a x + u (fun i => dot (p i) x)
    let gain := fun (u : U → F) (dec : F → Fin m → F) =>
      2*(∑ x : V, (K.filter (fun j => dec (sig u x) j = dot (v j) x)).card) - 2^k*K.card
    let mass := fun (e : Fin m → F) => ∑ x : V,
      let n := (J.filter (fun j => dot (v j) x + e j = 1)).card
      ((J.card : ℤ)-2*(n : ℤ)).natAbs
    (∀ u dec, ∃ e, gain u dec ≤ mass e) ∧
    (∀ e, ∃ u dec, gain u dec = mass e) ∧
    (∀ u dec, (gain u dec)^2 ≤ J.card*(2^k)^2) := by
  intro k m d F V U dot v hv0 p a K
  exact PEqualNP.Outside.L_lib_809_aux.main_809 k m d v hv0 p a K
