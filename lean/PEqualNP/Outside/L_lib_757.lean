import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_757

def sgnB (b : Bool) : ℤ := if b then -1 else 1

lemma sgnB_xor (a b : Bool) : sgnB (Bool.xor a b) = sgnB a * sgnB b := by
  cases a <;> cases b <;> decide

lemma sgnB_sq (b : Bool) : sgnB b * sgnB b = 1 := by
  cases b <;> decide

lemma sgnB_not (b : Bool) : sgnB (!b) = -sgnB b := by
  cases b <;> decide

lemma decide_eq_one_add (a b : ZMod 2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b; decide

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide
lemma z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

def bitOf {k : ℕ} (v : Fin k → ZMod 2) (c : Bool) (x : Fin k → ZMod 2) : Bool :=
  Bool.xor c (decide ((∑ i : Fin k, x i * v i) = 1))

lemma prod_sgnB_bitOf {k h : ℕ} (v : Fin h → Fin k → ZMod 2) (c : Fin h → Bool)
    (S : Finset (Fin h)) (x : Fin k → ZMod 2) :
    ∏ j ∈ S, sgnB (bitOf (v j) (c j) x) =
      (∏ j ∈ S, sgnB (c j)) * sgnB (decide ((∑ i : Fin k, x i * (∑ j ∈ S, v j) i) = 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sgnB]
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ih]
    dsimp only [bitOf]
    rw [sgnB_xor]
    have hdot : (∑ i : Fin k, x i * (∑ t ∈ insert j S, v t) i) =
        (∑ i : Fin k, x i * v j i) + (∑ i : Fin k, x i * (∑ t ∈ S, v t) i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_insert hj, Pi.add_apply, mul_add]
    rw [hdot, decide_eq_one_add, sgnB_xor]
    ring

lemma sum_sgnB_dot_zero {k : ℕ} :
    ∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, x i * (0 : Fin k → ZMod 2) i) = 1)) =
      (2 ^ k : ℤ) := by
  have h1 : ∀ x : Fin k → ZMod 2,
      sgnB (decide ((∑ i : Fin k, x i * (0 : Fin k → ZMod 2) i) = 1)) = 1 := fun x => by
    simp [sgnB]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  simp

lemma sum_sgnB_dot_ne_zero {k : ℕ} (u : Fin k → ZMod 2) (hu : u ≠ 0) :
    ∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, x i * u i) = 1)) = 0 := by
  classical
  have hex : ∃ i0 : Fin k, u i0 ≠ 0 := by
    by_contra hno
    apply hu; funext i
    by_contra hne; exact hno ⟨i, hne⟩
  obtain ⟨i0, hi0⟩ := hex
  have hui0 : u i0 = 1 := by
    rcases z2_cases (u i0) with h0 | h1
    · exact False.elim (hi0 h0)
    · exact h1
  let e : (Fin k → ZMod 2) ≃ (Fin k → ZMod 2) :=
    { toFun := fun x => Function.update x i0 (x i0 + 1)
      invFun := fun x => Function.update x i0 (x i0 + 1)
      left_inv := fun x => by
        funext i
        by_cases hi : i = i0
        · subst hi; simp [add_assoc, z2_add_self]
        · simp [hi]
      right_inv := fun x => by
        funext i
        by_cases hi : i = i0
        · subst hi; simp [add_assoc, z2_add_self]
        · simp [hi] }
  have hflip : ∀ x : Fin k → ZMod 2,
      sgnB (decide ((∑ i : Fin k, e x i * u i) = 1)) =
        -sgnB (decide ((∑ i : Fin k, x i * u i) = 1)) := by
    intro x
    have hdot : (∑ i : Fin k, e x i * u i) = (∑ i : Fin k, x i * u i) + 1 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0),
          ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
      have hrest : ∑ i ∈ Finset.univ.erase i0, e x i * u i =
          ∑ i ∈ Finset.univ.erase i0, x i * u i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
        simp [e, hne]
      rw [hrest]
      have h0 : e x i0 * u i0 = x i0 * u i0 + 1 := by
        simp only [e, Equiv.coe_fn_mk, Function.update_self, hui0, mul_one]
      rw [h0]; ring
    rw [hdot, decide_eq_one_add, show decide ((1 : ZMod 2) = 1) = true by decide,
        Bool.xor_true, sgnB_not]
  have hS : (∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, x i * u i) = 1))) =
      -(∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, x i * u i) = 1))) := by
    calc ∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, x i * u i) = 1))
        = ∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, e x i * u i) = 1)) :=
          (Equiv.sum_comp e _).symm
      _ = ∑ x : Fin k → ZMod 2, -sgnB (decide ((∑ i : Fin k, x i * u i) = 1)) :=
          Finset.sum_congr rfl fun x _ => hflip x
      _ = -(∑ x : Fin k → ZMod 2, sgnB (decide ((∑ i : Fin k, x i * u i) = 1))) := by
          rw [Finset.sum_neg_distrib]
  omega

lemma sum_prod_bitOf_ne {k h : ℕ} (v : Fin h → Fin k → ZMod 2) (c : Fin h → Bool)
    (S : Finset (Fin h)) (hne : (∑ j ∈ S, v j) ≠ 0) :
    ∑ x : Fin k → ZMod 2, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x) = 0 := by
  simp_rw [prod_sgnB_bitOf]
  rw [← Finset.mul_sum, sum_sgnB_dot_ne_zero _ hne, mul_zero]

lemma sum_prod_bitOf_eq {k h : ℕ} (v : Fin h → Fin k → ZMod 2) (c : Fin h → Bool)
    (S : Finset (Fin h)) (heq : (∑ j ∈ S, v j) = 0) :
    ∑ x : Fin k → ZMod 2, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x) =
      (2 ^ k : ℤ) * ∏ j ∈ S, sgnB (c j) := by
  simp_rw [prod_sgnB_bitOf, heq]
  rw [← Finset.mul_sum, sum_sgnB_dot_zero, mul_comm]

lemma prod_sgnB_eq_ite {h : ℕ} (c : Fin h → Bool) (S : Finset (Fin h)) :
    ∏ j ∈ S, sgnB (c j) = if (S.filter (fun j => c j = true)).card % 2 = 1 then -1 else 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, ih, Finset.filter_insert]
    cases hc : c j
    · simp [sgnB]
    · have hj' : j ∉ S.filter (fun t => c t = true) := fun hm => hj (Finset.mem_filter.mp hm).1
      rw [if_pos rfl, Finset.card_insert_of_notMem hj']
      simp only [sgnB, ↓reduceIte]
      split_ifs <;> omega

lemma sum_sgnB_parity {h : ℕ} (b : Fin h → Bool) (S : Finset (Fin h)) :
    ∑ j ∈ S, sgnB (b j) = (S.card : ℤ) - 2 * ((S.filter (fun j => b j = true)).card : ℤ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, ih, Finset.card_insert_of_notMem hj, Finset.filter_insert]
    cases hb : b j
    · simp [sgnB]; ring
    · have hj' : j ∉ S.filter (fun t => b t = true) := fun hm => hj (Finset.mem_filter.mp hm).1
      rw [if_pos rfl, Finset.card_insert_of_notMem hj']
      simp only [sgnB, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      ring

lemma W_natAbs_mod_two {h : ℕ} (b : Fin h → Bool) :
    (∑ j : Fin h, sgnB (b j)).natAbs % 2 = h % 2 := by
  have h1 := sum_sgnB_parity b Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h1
  set r := ((Finset.univ : Finset (Fin h)).filter (fun j => b j = true)).card
  rcases Int.natAbs_eq (∑ j : Fin h, sgnB (b j)) with hpos | hneg <;> omega

lemma vec_sum_pair_ne_zero {k : ℕ} {a b : Fin k → ZMod 2} (hne : a ≠ b) : a + b ≠ 0 := by
  intro h0
  apply hne; funext i
  have hi := congrFun h0 i
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  have hb : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact hb _ _ hi

lemma sum_W_sq {k h : ℕ} (v : Fin h ↪ (Fin k → ZMod 2)) (c : Fin h → Bool) :
    ∑ x : Fin k → ZMod 2, (∑ j : Fin h, sgnB (bitOf (v j) (c j) x)) ^ 2 =
      (2 ^ k : ℤ) * (h : ℤ) := by
  classical
  have hexp : ∀ x : Fin k → ZMod 2,
      (∑ j : Fin h, sgnB (bitOf (v j) (c j) x)) ^ 2 =
        ∑ j1 : Fin h, ∑ j2 : Fin h, sgnB (bitOf (v j1) (c j1) x) * sgnB (bitOf (v j2) (c j2) x) := by
    intro x; rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hinner : ∀ j1 : Fin h,
      (∑ x : Fin k → ZMod 2, ∑ j2 : Fin h,
        sgnB (bitOf (v j1) (c j1) x) * sgnB (bitOf (v j2) (c j2) x)) = (2 ^ k : ℤ) := by
    intro j1
    rw [Finset.sum_comm]
    have hsingle : ∀ j2 : Fin h,
        (∑ x : Fin k → ZMod 2, sgnB (bitOf (v j1) (c j1) x) * sgnB (bitOf (v j2) (c j2) x)) =
          if j2 = j1 then (2 ^ k : ℤ) else 0 := by
      intro j2
      by_cases h12 : j2 = j1
      · subst h12
        simp only [↓reduceIte, sgnB_sq, Finset.sum_const, Finset.card_univ,
          Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one,
          Nat.cast_pow, Nat.cast_ofNat]
      · rw [if_neg h12]
        have hS := sum_prod_bitOf_ne v c ({j1, j2} : Finset (Fin h)) (by
          rw [Finset.sum_pair (Ne.symm h12)]
          exact vec_sum_pair_ne_zero (fun heq => h12 (v.injective heq).symm))
        have hprod : ∀ x, ∏ j ∈ ({j1, j2} : Finset (Fin h)), sgnB (bitOf (v j) (c j) x) =
            sgnB (bitOf (v j1) (c j1) x) * sgnB (bitOf (v j2) (c j2) x) := fun x =>
          Finset.prod_pair (Ne.symm h12)
        simp_rw [hprod] at hS
        exact hS
    simp_rw [hsingle]
    simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [mul_comm]

lemma sum_W_pow4 {k h : ℕ} (v : Fin h ↪ (Fin k → ZMod 2))
    (h4 : ∀ S : Finset (Fin h), S.card = 4 → (∑ j ∈ S, v j) ≠ 0) (c : Fin h → Bool) :
    ∑ x : Fin k → ZMod 2, (∑ j : Fin h, sgnB (bitOf (v j) (c j) x)) ^ 4 =
      (2 ^ k : ℤ) * (3 * (h : ℤ) ^ 2 - 2 * (h : ℤ)) := by
  classical
  let ε : Fin h → (Fin k → ZMod 2) → ℤ := fun j x => sgnB (bitOf (v j) (c j) x)
  have hpair_zero : ∀ a b : Fin h, a ≠ b → ∑ x : Fin k → ZMod 2, ε a x * ε b x = 0 := by
    intro a b hab
    have hS := sum_prod_bitOf_ne v c ({a, b} : Finset (Fin h)) (by
      rw [Finset.sum_pair hab]
      exact vec_sum_pair_ne_zero (fun heq => hab (v.injective heq)))
    have hprod : ∀ x, ∏ j ∈ ({a, b} : Finset (Fin h)), sgnB (bitOf (v j) (c j) x) = ε a x * ε b x :=
      fun x => Finset.prod_pair hab
    exact (Finset.sum_congr rfl fun x _ => (hprod x).symm).trans hS
  have hquad_zero : ∀ a b d e : Fin h,
      a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
      ∑ x : Fin k → ZMod 2, ε a x * ε b x * ε d x * ε e x = 0 := by
    intro a b d e hab had hae hbd hbe hde
    let S : Finset (Fin h) := {a, b, d, e}
    have hcard : S.card = 4 := by
      dsimp only [S]
      rw [Finset.card_insert_of_notMem (by simp [hab, had, hae]),
          Finset.card_insert_of_notMem (by simp [hbd, hbe]),
          Finset.card_insert_of_notMem (by simp [hde]),
          Finset.card_singleton]
    have hS := sum_prod_bitOf_ne v c S (h4 S hcard)
    have hprod : ∀ x, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x) = ε a x * ε b x * ε d x * ε e x := by
      intro x; dsimp only [S]
      rw [Finset.prod_insert (by simp [hab, had, hae]),
          Finset.prod_insert (by simp [hbd, hbe]),
          Finset.prod_insert (by simp [hde]),
          Finset.prod_singleton]
      dsimp only [ε]; ring
    exact (Finset.sum_congr rfl fun x _ => (hprod x).symm).trans hS
  have h1 : ∀ x : Fin k → ZMod 2,
      (∑ j : Fin h, ε j x) ^ 4 =
        ∑ j1 : Fin h, ∑ j2 : Fin h, ∑ j3 : Fin h, ∑ j4 : Fin h,
          ε j1 x * ε j2 x * ε j3 x * ε j4 x := by
    intro x
    have hsq2 : (∑ j : Fin h, ε j x) * (∑ j : Fin h, ε j x) =
        ∑ j1 : Fin h, ∑ j2 : Fin h, ε j1 x * ε j2 x := by
      rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    calc (∑ j : Fin h, ε j x) ^ 4
        = ((∑ j : Fin h, ε j x) * (∑ j : Fin h, ε j x)) *
          ((∑ j : Fin h, ε j x) * (∑ j : Fin h, ε j x)) := by ring
      _ = (∑ j1 : Fin h, ∑ j2 : Fin h, ε j1 x * ε j2 x) *
          (∑ j3 : Fin h, ∑ j4 : Fin h, ε j3 x * ε j4 x) := by rw [hsq2]
      _ = ∑ j1 : Fin h, ∑ j2 : Fin h, ∑ j3 : Fin h, ∑ j4 : Fin h,
          ε j1 x * ε j2 x * ε j3 x * ε j4 x := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j1 _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j2 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j3 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j4 _ => by ring
  have hterm : ∀ j1 j2 j3 j4 : Fin h,
      (∑ x : Fin k → ZMod 2, ε j1 x * ε j2 x * ε j3 x * ε j4 x) =
        if (j1 = j2 ∧ j3 = j4) ∨ (j1 = j3 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j3)
        then (2 ^ k : ℤ) else 0 := by
    intro j1 j2 j3 j4
    have hsq1 : ∀ j x, ε j x * ε j x = 1 := fun j x => sgnB_sq _
    by_cases h12 : j1 = j2
    · subst h12
      by_cases h34 : j3 = j4
      · subst h34
        rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
        have hall : ∀ x, ε j1 x * ε j1 x * ε j3 x * ε j3 x = 1 := fun x => by
          rw [hsq1 j1 x, one_mul, hsq1 j3 x]
        simp_rw [hall]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]; simp
      · have hnot : ¬ ((j1 = j1 ∧ j3 = j4) ∨ (j1 = j3 ∧ j1 = j4) ∨ (j1 = j4 ∧ j1 = j3)) := by
          rintro (⟨_, h⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact h34 h
          · exact h34 (h1.symm.trans h2)
          · exact h34 (h2.symm.trans h1)
        rw [if_neg hnot]
        have hall : ∀ x, ε j1 x * ε j1 x * ε j3 x * ε j4 x = ε j3 x * ε j4 x := fun x => by
          rw [hsq1 j1 x, one_mul]
        simp_rw [hall]; exact hpair_zero j3 j4 h34
    · by_cases h13 : j1 = j3
      · subst h13
        by_cases h24 : j2 = j4
        · subst h24
          rw [if_pos (Or.inr (Or.inl ⟨rfl, rfl⟩))]
          have hall : ∀ x, ε j1 x * ε j2 x * ε j1 x * ε j2 x = 1 := fun x => by
            calc ε j1 x * ε j2 x * ε j1 x * ε j2 x
                = (ε j1 x * ε j1 x) * (ε j2 x * ε j2 x) := by ring
              _ = 1 := by rw [hsq1, hsq1, one_mul]
          simp_rw [hall]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]; simp
        · have hnot : ¬ ((j1 = j2 ∧ j1 = j4) ∨ (j1 = j1 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j1)) := by
            rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩)
            · exact h12 h
            · exact h24 h
            · exact h12 h.symm
          rw [if_neg hnot]
          have hall : ∀ x, ε j1 x * ε j2 x * ε j1 x * ε j4 x = ε j2 x * ε j4 x := fun x => by
            calc ε j1 x * ε j2 x * ε j1 x * ε j4 x
                = (ε j1 x * ε j1 x) * (ε j2 x * ε j4 x) := by ring
              _ = ε j2 x * ε j4 x := by rw [hsq1, one_mul]
          simp_rw [hall]; exact hpair_zero j2 j4 h24
      · by_cases h14 : j1 = j4
        · subst h14
          by_cases h23 : j2 = j3
          · subst h23
            rw [if_pos (Or.inr (Or.inr ⟨rfl, rfl⟩))]
            have hall : ∀ x, ε j1 x * ε j2 x * ε j2 x * ε j1 x = 1 := fun x => by
              calc ε j1 x * ε j2 x * ε j2 x * ε j1 x
                  = (ε j1 x * ε j1 x) * (ε j2 x * ε j2 x) := by ring
                _ = 1 := by rw [hsq1, hsq1, one_mul]
            simp_rw [hall]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]; simp
          · have hnot : ¬ ((j1 = j2 ∧ j3 = j1) ∨ (j1 = j3 ∧ j2 = j1) ∨ (j1 = j1 ∧ j2 = j3)) := by
              rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
              · exact h12 h
              · exact h13 h
              · exact h23 h
            rw [if_neg hnot]
            have hall : ∀ x, ε j1 x * ε j2 x * ε j3 x * ε j1 x = ε j2 x * ε j3 x := fun x => by
              calc ε j1 x * ε j2 x * ε j3 x * ε j1 x
                  = (ε j1 x * ε j1 x) * (ε j2 x * ε j3 x) := by ring
                _ = ε j2 x * ε j3 x := by rw [hsq1, one_mul]
            simp_rw [hall]; exact hpair_zero j2 j3 h23
        · have hnot : ¬ ((j1 = j2 ∧ j3 = j4) ∨ (j1 = j3 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j3)) := by
            rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> contradiction
          rw [if_neg hnot]
          by_cases h23 : j2 = j3
          · subst h23
            have hall : ∀ x, ε j1 x * ε j2 x * ε j2 x * ε j4 x = ε j1 x * ε j4 x := fun x => by
              calc ε j1 x * ε j2 x * ε j2 x * ε j4 x
                  = (ε j2 x * ε j2 x) * (ε j1 x * ε j4 x) := by ring
                _ = ε j1 x * ε j4 x := by rw [hsq1, one_mul]
            simp_rw [hall]; exact hpair_zero j1 j4 h14
          · by_cases h24 : j2 = j4
            · subst h24
              have hall : ∀ x, ε j1 x * ε j2 x * ε j3 x * ε j2 x = ε j1 x * ε j3 x := fun x => by
                calc ε j1 x * ε j2 x * ε j3 x * ε j2 x
                    = (ε j2 x * ε j2 x) * (ε j1 x * ε j3 x) := by ring
                  _ = ε j1 x * ε j3 x := by rw [hsq1, one_mul]
              simp_rw [hall]; exact hpair_zero j1 j3 h13
            · by_cases h34 : j3 = j4
              · subst h34
                have hall : ∀ x, ε j1 x * ε j2 x * ε j3 x * ε j3 x = ε j1 x * ε j2 x := fun x => by
                  calc ε j1 x * ε j2 x * ε j3 x * ε j3 x
                      = (ε j3 x * ε j3 x) * (ε j1 x * ε j2 x) := by ring
                    _ = ε j1 x * ε j2 x := by rw [hsq1, one_mul]
                simp_rw [hall]; exact hpair_zero j1 j2 h12
              · exact hquad_zero j1 j2 j3 j4 h12 h13 h14 h23 h24 h34
  have h1' : (∑ x : Fin k → ZMod 2, (∑ j : Fin h, sgnB (bitOf (v j) (c j) x)) ^ 4) =
      ∑ x : Fin k → ZMod 2, ∑ j1 : Fin h, ∑ j2 : Fin h, ∑ j3 : Fin h, ∑ j4 : Fin h,
        ε j1 x * ε j2 x * ε j3 x * ε j4 x :=
    Finset.sum_congr rfl fun x _ => h1 x
  rw [h1', Finset.sum_comm]
  have hswap : ∀ j1 : Fin h,
      (∑ x : Fin k → ZMod 2, ∑ j2 : Fin h, ∑ j3 : Fin h, ∑ j4 : Fin h,
        ε j1 x * ε j2 x * ε j3 x * ε j4 x) =
      ∑ j2 : Fin h, ∑ j3 : Fin h, ∑ j4 : Fin h, ∑ x : Fin k → ZMod 2,
        ε j1 x * ε j2 x * ε j3 x * ε j4 x := by
    intro j1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j3 _ => ?_
    rw [Finset.sum_comm]
  simp_rw [hswap, hterm]
  have hinner : ∀ j1 j2 : Fin h,
      (∑ j3 : Fin h, ∑ j4 : Fin h,
        if (j1 = j2 ∧ j3 = j4) ∨ (j1 = j3 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j3)
        then (2 ^ k : ℤ) else 0) =
      if j1 = j2 then (h : ℤ) * (2 ^ k : ℤ) else 2 * (2 ^ k : ℤ) := by
    intro j1 j2
    by_cases h12 : j1 = j2
    · subst h12
      rw [if_pos rfl]
      have h3 : ∀ j3 : Fin h, (∑ j4 : Fin h,
          if (j1 = j1 ∧ j3 = j4) ∨ (j1 = j3 ∧ j1 = j4) ∨ (j1 = j4 ∧ j1 = j3)
          then (2 ^ k : ℤ) else 0) = (2 ^ k : ℤ) := by
        intro j3
        have h4eq : ∀ j4 : Fin h,
            (if (j1 = j1 ∧ j3 = j4) ∨ (j1 = j3 ∧ j1 = j4) ∨ (j1 = j4 ∧ j1 = j3)
              then (2 ^ k : ℤ) else 0) = if j4 = j3 then (2 ^ k : ℤ) else 0 := by
          intro j4; by_cases h : j4 = j3
          · subst h; simp
          · rw [if_neg h, if_neg]
            rintro (⟨_, h'⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact h h'.symm
            · exact h (h2.symm.trans h1)
            · exact h (h1.symm.trans h2)
        rw [Finset.sum_congr rfl fun j4 _ => h4eq j4]; simp
      rw [Finset.sum_congr rfl fun j3 _ => h3 j3]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
    · rw [if_neg h12]
      have h3 : ∀ j3 : Fin h, (∑ j4 : Fin h,
          if (j1 = j2 ∧ j3 = j4) ∨ (j1 = j3 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j3)
          then (2 ^ k : ℤ) else 0) =
        (if j3 = j1 then (2 ^ k : ℤ) else 0) + (if j3 = j2 then (2 ^ k : ℤ) else 0) := by
        intro j3
        by_cases h31 : j3 = j1
        · subst j3
          have h4eq : ∀ j4 : Fin h,
              (if (j1 = j2 ∧ j1 = j4) ∨ (j1 = j1 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j1)
                then (2 ^ k : ℤ) else 0) = if j4 = j2 then (2 ^ k : ℤ) else 0 := by
            intro j4; by_cases hj4 : j4 = j2
            · subst hj4; simp
            · rw [if_neg hj4, if_neg]
              rintro (⟨h', _⟩ | ⟨_, h'⟩ | ⟨_, h'⟩)
              · exact h12 h'
              · exact hj4 h'.symm
              · exact h12 h'.symm
          rw [Finset.sum_congr rfl fun j4 _ => h4eq j4]; simp [h12]
        · by_cases h32 : j3 = j2
          · subst j3
            have h4eq : ∀ j4 : Fin h,
                (if (j1 = j2 ∧ j2 = j4) ∨ (j1 = j2 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j2)
                  then (2 ^ k : ℤ) else 0) = if j4 = j1 then (2 ^ k : ℤ) else 0 := by
              intro j4; by_cases hj4 : j4 = j1
              · subst hj4; simp
              · rw [if_neg hj4, if_neg]
                rintro (⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩)
                · exact h12 h'
                · exact h12 h'
                · exact hj4 h'.symm
            rw [Finset.sum_congr rfl fun j4 _ => h4eq j4]; simp [Ne.symm h12]
          · have h4eq : ∀ j4 : Fin h,
                (if (j1 = j2 ∧ j3 = j4) ∨ (j1 = j3 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j3)
                  then (2 ^ k : ℤ) else 0) = 0 := by
              intro j4; rw [if_neg]
              rintro (⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h'⟩)
              · exact h12 h'
              · exact h31 h'.symm
              · exact h32 h'.symm
            rw [Finset.sum_congr rfl fun j4 _ => h4eq j4]; simp [h31, h32]
      rw [Finset.sum_congr rfl fun j3 _ => h3 j3, Finset.sum_add_distrib]
      simp; ring
  simp_rw [hinner]
  have houter : ∀ j1 : Fin h,
      (∑ j2 : Fin h, if j1 = j2 then (h : ℤ) * (2 ^ k : ℤ) else 2 * (2 ^ k : ℤ)) =
        (3 * (h : ℤ) - 2) * (2 ^ k : ℤ) := by
    intro j1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j1)]
    rw [if_pos rfl]
    have hrest : ∑ j2 ∈ Finset.univ.erase j1,
        (if j1 = j2 then (h : ℤ) * (2 ^ k : ℤ) else 2 * (2 ^ k : ℤ)) =
        ((h : ℤ) - 1) * (2 * (2 ^ k : ℤ)) := by
      have hc : ∀ j2 ∈ Finset.univ.erase j1,
          (if j1 = j2 then (h : ℤ) * (2 ^ k : ℤ) else 2 * (2 ^ k : ℤ)) = 2 * (2 ^ k : ℤ) := by
        intro j2 hj2; exact if_neg (Finset.mem_erase.mp hj2).1.symm
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j1),
          Finset.card_univ, Fintype.card_fin]
      have hpos : 1 ≤ h := by exact Nat.pos_of_ne_zero (fun h0 => Fin.elim0 (h0 ▸ j1))
      simp only [nsmul_eq_mul, Nat.cast_sub hpos, Nat.cast_one]
    rw [hrest]; ring
  simp_rw [houter]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]; ring

lemma prod_one_add_eq_sum_powerset {h : ℕ} (a : Fin h → ℤ) :
    ∏ j : Fin h, (1 + a j) = ∑ S : Finset (Fin h), ∏ j ∈ S, a j := by
  classical
  have hgen : ∀ T : Finset (Fin h),
      ∏ j ∈ T, (1 + a j) = ∑ S ∈ T.powerset, ∏ j ∈ S, a j := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      rw [Finset.prod_insert hj, ih, Finset.powerset_insert, Finset.sum_union]
      · rw [Finset.sum_image]
        · rw [add_mul, one_mul, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun S hS => ?_
          have hjS : j ∉ S := fun hm => hj (Finset.mem_powerset.mp hS hm)
          rw [Finset.prod_insert hjS]
        · intro S1 hS1 S2 hS2 heq
          have hj1 : j ∉ S1 := fun hm => hj (Finset.mem_powerset.mp hS1 hm)
          have hj2 : j ∉ S2 := fun hm => hj (Finset.mem_powerset.mp hS2 hm)
          have h1 : (insert j S1).erase j = S1 := Finset.erase_insert hj1
          have h2 : (insert j S2).erase j = S2 := Finset.erase_insert hj2
          rw [← h1, ← h2, heq]
      · rw [Finset.disjoint_left]
        intro S hS1 hS2
        rw [Finset.mem_image] at hS2
        obtain ⟨S', _, rfl⟩ := hS2
        exact hj (Finset.mem_powerset.mp hS1 (Finset.mem_insert_self j S'))
  simpa using hgen Finset.univ

lemma walsh_abs_sum {k h : ℕ} (zOf : (Fin k → ZMod 2) → (Fin h → Bool)) :
    let absW : (Fin h → Bool) → ℤ := fun z => ((∑ j : Fin h, sgnB (z j)).natAbs : ℤ)
    (2 ^ h : ℤ) * ∑ x : Fin k → ZMod 2, absW (zOf x) =
      ∑ S : Finset (Fin h),
        (∑ z : Fin h → Bool, absW z * ∏ j ∈ S, sgnB (z j)) *
        (∑ x : Fin k → ZMod 2, ∏ j ∈ S, sgnB (zOf x j)) := by
  classical
  intro absW
  have hrhs : (∑ S : Finset (Fin h),
        (∑ z : Fin h → Bool, absW z * ∏ j ∈ S, sgnB (z j)) *
        (∑ x : Fin k → ZMod 2, ∏ j ∈ S, sgnB (zOf x j))) =
      ∑ x : Fin k → ZMod 2, ∑ z : Fin h → Bool,
        absW z * (∑ S : Finset (Fin h), ∏ j ∈ S, (sgnB (z j) * sgnB (zOf x j))) := by
    have hstep1 : ∀ S : Finset (Fin h),
        (∑ z : Fin h → Bool, absW z * ∏ j ∈ S, sgnB (z j)) *
        (∑ x : Fin k → ZMod 2, ∏ j ∈ S, sgnB (zOf x j)) =
        ∑ x : Fin k → ZMod 2, ∑ z : Fin h → Bool,
          absW z * (∏ j ∈ S, (sgnB (z j) * sgnB (zOf x j))) := by
      intro S
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.prod_mul_distrib]; ring
    simp_rw [hstep1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
  rw [hrhs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdelta : ∀ z : Fin h → Bool,
      (∑ S : Finset (Fin h), ∏ j ∈ S, (sgnB (z j) * sgnB (zOf x j))) =
        if z = zOf x then (2 ^ h : ℤ) else 0 := by
    intro z
    rw [← prod_one_add_eq_sum_powerset]
    by_cases hz : z = zOf x
    · subst hz
      rw [if_pos rfl]
      have h2 : ∀ j : Fin h, (1 : ℤ) + sgnB (zOf x j) * sgnB (zOf x j) = 2 := fun j => by
        rw [sgnB_sq]; norm_num
      simp_rw [h2]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [if_neg hz]
      have hex : ∃ j : Fin h, z j ≠ zOf x j := by
        by_contra hno; apply hz; funext j; by_contra hne; exact hno ⟨j, hne⟩
      obtain ⟨j0, hj0⟩ := hex
      refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
      cases h1 : z j0 <;> cases h2 : zOf x j0 <;> simp [h1, h2] at hj0 <;> decide
  simp_rw [hdelta]
  simp [mul_comm]

lemma absW_walsh_odd {h : ℕ} (S : Finset (Fin h)) (hodd : S.card % 2 = 1) :
    ∑ z : Fin h → Bool, (((∑ j : Fin h, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) = 0 := by
  let e : (Fin h → Bool) ≃ (Fin h → Bool) :=
    { toFun := fun z j => !(z j)
      invFun := fun z j => !(z j)
      left_inv := fun z => by funext j; simp
      right_inv := fun z => by funext j; simp }
  have hflip : ∀ z : Fin h → Bool,
      (((∑ j : Fin h, sgnB (e z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (e z j)) =
      -(((∑ j : Fin h, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) := by
    intro z
    have hsum : ∑ j : Fin h, sgnB (e z j) = -(∑ j : Fin h, sgnB (z j)) := by
      simp only [e, Equiv.coe_fn_mk, sgnB_not, Finset.sum_neg_distrib]
    have hprod : ∏ j ∈ S, sgnB (e z j) = -(∏ j ∈ S, sgnB (z j)) := by
      have h1 : ∏ j ∈ S, sgnB (e z j) = ∏ j ∈ S, ((-1 : ℤ) * sgnB (z j)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        simp [e, sgnB_not]
      rw [h1, Finset.prod_mul_distrib, Finset.prod_const]
      have hpow : (-1 : ℤ) ^ S.card = -1 := by
        have hodd' : Odd S.card := Nat.odd_iff.mpr hodd
        exact Odd.neg_one_pow hodd'
      rw [hpow]; ring
    rw [hsum, Int.natAbs_neg, hprod]; ring
  have hT : (∑ z : Fin h → Bool, (((∑ j : Fin h, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j))) =
      -(∑ z : Fin h → Bool, (((∑ j : Fin h, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j))) := by
    calc _ = ∑ z : Fin h → Bool, (((∑ j : Fin h, sgnB (e z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (e z j)) :=
          (Equiv.sum_comp e _).symm
      _ = ∑ z : Fin h → Bool, -(((∑ j : Fin h, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) :=
          Finset.sum_congr rfl fun z _ => hflip z
      _ = -_ := by rw [Finset.sum_neg_distrib]
  omega

lemma sum_bool_by_weight {h : ℕ} (φ : ℕ → ℤ) :
    ∑ z : Fin h → Bool, φ ((Finset.univ : Finset (Fin h)).filter (fun j => z j = true)).card =
      ∑ r ∈ Finset.range (h + 1), (Nat.choose h r : ℤ) * φ r := by
  classical
  let e : (Fin h → Bool) ≃ Finset (Fin h) :=
    { toFun := fun z => (Finset.univ : Finset (Fin h)).filter (fun j => z j = true)
      invFun := fun S j => decide (j ∈ S)
      left_inv := fun z => by funext j; simp
      right_inv := fun S => by ext j; simp }
  have h1 : (∑ z : Fin h → Bool, φ ((Finset.univ : Finset (Fin h)).filter (fun j => z j = true)).card) =
      ∑ S : Finset (Fin h), φ S.card := by
    exact Equiv.sum_comp e (fun S : Finset (Fin h) => φ S.card)
  rw [h1]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (h + 1)) (g := Finset.card)
      (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)))]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hconst : ∀ S ∈ (Finset.univ : Finset (Finset (Fin h))).filter (fun S => S.card = r),
      φ S.card = φ r := fun S hS => by rw [(Finset.mem_filter.mp hS).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hfilt : (Finset.univ : Finset (Finset (Fin h))).filter (fun S => S.card = r) =
      Finset.powersetCard r (Finset.univ : Finset (Fin h)) := by
    ext S; simp [Finset.mem_powersetCard]
  rw [hfilt, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma absW_sum_6 :
    ∑ z : Fin 6 → Bool, ((∑ j : Fin 6, sgnB (z j)).natAbs : ℤ) = 120 := by
  have h1 : ∀ z : Fin 6 → Bool,
      ((∑ j : Fin 6, sgnB (z j)).natAbs : ℤ) =
        (((6 : ℤ) - 2 * (((Finset.univ : Finset (Fin 6)).filter (fun j => z j = true)).card : ℤ)).natAbs : ℤ) := by
    intro z
    have hp := sum_sgnB_parity z Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hp
    rw [hp]; rfl
  simp_rw [h1]
  rw [sum_bool_by_weight (fun r => (((6 : ℤ) - 2 * (r : ℤ)).natAbs : ℤ))]
  decide

lemma absW_sum_8 :
    ∑ z : Fin 8 → Bool, ((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) = 560 := by
  have h1 : ∀ z : Fin 8 → Bool,
      ((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) =
        (((8 : ℤ) - 2 * (((Finset.univ : Finset (Fin 8)).filter (fun j => z j = true)).card : ℤ)).natAbs : ℤ) := by
    intro z
    have hp := sum_sgnB_parity z Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hp
    rw [hp]; rfl
  simp_rw [h1]
  rw [sum_bool_by_weight (fun r => (((8 : ℤ) - 2 * (r : ℤ)).natAbs : ℤ))]
  decide

lemma absW_top_8 :
    ∑ z : Fin 8 → Bool, (((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) * ∏ j : Fin 8, sgnB (z j)) = -80 := by
  have h1 : ∀ z : Fin 8 → Bool,
      (((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) * ∏ j : Fin 8, sgnB (z j)) =
        (((8 : ℤ) - 2 * (((Finset.univ : Finset (Fin 8)).filter (fun j => z j = true)).card : ℤ)).natAbs : ℤ) *
          (if (((Finset.univ : Finset (Fin 8)).filter (fun j => z j = true)).card % 2 = 1) then (-1 : ℤ) else 1) := by
    intro z
    have hp := sum_sgnB_parity z Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hp
    rw [hp, prod_sgnB_eq_ite z Finset.univ]; rfl
  simp_rw [h1]
  rw [sum_bool_by_weight (fun r => (((8 : ℤ) - 2 * (r : ℤ)).natAbs : ℤ) * (if r % 2 = 1 then (-1 : ℤ) else 1))]
  decide

end PEqualNP.Outside.L_lib_757

open PEqualNP.Outside.L_lib_757 in
theorem PEqualNP.Outside.L_lib_757 : ∀ (k h : ℕ), 0 < h →
  let F := ZMod 2
  let V := Fin k → F
  ∀ (v : Fin h ↪ V),
    (∀ S : Finset (Fin h), S.card = 4 ∨ S.card = 6 → (∑ j ∈ S, v j) ≠ 0) →
    ∀ c : Fin h → Bool,
      let W := fun x : V => ∑ j : Fin h,
        if Bool.xor (c j) (decide ((∑ i : Fin k, x i * v j i) = 1))
          then (-1 : ℤ) else 1
      let left := 4 * ∑ x : V, (W x).natAbs
      let right := 2^k * (h + if h % 2 = 0 then 2 else 3)
      left ≤ right ∧
        (left = right ↔ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨
          (h = 8 ∧ (∑ j : Fin h, v j) = 0 ∧
            ((Finset.univ : Finset (Fin h)).filter (fun j => c j = true)).card % 2 = 1)) := by
  classical
  intro k h hh F V v h46 c W left right
  have h2k_pos : (0 : ℤ) < (2 ^ k : ℤ) := by positivity
  have hW_eq : ∀ x : V, W x = ∑ j : Fin h, sgnB (bitOf (v j) (c j) x) := fun _ => rfl
  have hM2 : ∑ x : V, (W x) ^ 2 = (2 ^ k : ℤ) * (h : ℤ) := sum_W_sq v c
  have hM4 : ∑ x : V, (W x) ^ 4 = (2 ^ k : ℤ) * (3 * (h : ℤ) ^ 2 - 2 * (h : ℤ)) :=
    sum_W_pow4 v (fun S hS => h46 S (Or.inl hS)) c
  have hW_par : ∀ x : V, (W x).natAbs % 2 = h % 2 := fun x => W_natAbs_mod_two (fun j => bitOf (v j) (c j) x)
  have hW_le_h : ∀ x : V, (W x).natAbs ≤ h := by
    intro x
    have htri : (W x).natAbs ≤ ∑ j : Fin h, (sgnB (bitOf (v j) (c j) x)).natAbs :=
      Int.natAbs_sum_le Finset.univ _
    have h1 : ∀ j : Fin h, (sgnB (bitOf (v j) (c j) x)).natAbs = 1 := fun j => by
      cases bitOf (v j) (c j) x <;> decide
    simp_rw [h1] at htri
    simpa using htri
  have hcardV : ((Finset.univ : Finset V).card : ℤ) = (2 ^ k : ℤ) := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]; simp
  have hZ_iff_le : left ≤ right ↔ (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) ≤
      (2 ^ k : ℤ) * ((h : ℤ) + if h % 2 = 0 then 2 else 3) := by
    dsimp only [left, right]
    constructor <;> intro hle
    · exact_mod_cast hle
    · exact_mod_cast hle
  have hZ_iff_eq : left = right ↔ (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) =
      (2 ^ k : ℤ) * ((h : ℤ) + if h % 2 = 0 then 2 else 3) := by
    dsimp only [left, right]
    constructor <;> intro heq
    · exact_mod_cast heq
    · exact_mod_cast heq
  rw [hZ_iff_le, hZ_iff_eq]
  by_cases hpar : h % 2 = 0
  · rw [if_pos hpar]
    have h_cases : h = 2 ∨ h = 4 ∨ h = 6 ∨ h = 8 ∨ 10 ≤ h := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | h10
    · -- h = 2
      have hpt : ∀ x : V, (4 : ℤ) * ((W x).natAbs : ℤ) = 2 * (W x) ^ 2 := by
        intro x
        have hp := hW_par x; have hl := hW_le_h x
        have ha : (W x).natAbs = 0 ∨ (W x).natAbs = 2 := by omega
        have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
        rw [hsq]
        rcases ha with h0 | h2
        · simp [h0]
        · simp [h2]
      have hsum : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = (2 ^ k : ℤ) * ((2 : ℤ) + 2) := by
        rw [Finset.mul_sum]; simp_rw [hpt, ← Finset.mul_sum, hM2]; ring
      exact ⟨le_of_eq hsum, ⟨fun _ => Or.inr (Or.inl rfl), fun _ => hsum⟩⟩
    · -- h = 4
      have hpt : ∀ x : V, (48 : ℤ) * ((W x).natAbs : ℤ) = 28 * (W x) ^ 2 - (W x) ^ 4 := by
        intro x
        have hp := hW_par x; have hl := hW_le_h x
        have ha : (W x).natAbs = 0 ∨ (W x).natAbs = 2 ∨ (W x).natAbs = 4 := by omega
        have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
        have h4eq : (W x) ^ 4 = ((W x).natAbs : ℤ) ^ 4 := by
          calc (W x) ^ 4 = ((W x) ^ 2) ^ 2 := by ring
            _ = (((W x).natAbs : ℤ) ^ 2) ^ 2 := by rw [hsq]
            _ = ((W x).natAbs : ℤ) ^ 4 := by ring
        rw [hsq, h4eq]
        rcases ha with h0 | h2 | h4'
        · simp [h0]
        · simp [h2]
        · simp [h4']
      have hsum48 : (48 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = (72 : ℤ) * (2 ^ k : ℤ) := by
        rw [Finset.mul_sum]; simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, hM2, hM4]; ring
      have hsum : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = (2 ^ k : ℤ) * ((4 : ℤ) + 2) := by omega
      exact ⟨le_of_eq hsum, ⟨fun _ => Or.inr (Or.inr (Or.inr (Or.inl rfl))), fun _ => hsum⟩⟩
    · -- h = 6
      have hwalsh := walsh_abs_sum (fun x j => bitOf (v j) (c j) x)
      dsimp only at hwalsh
      have hzero_S : ∀ S : Finset (Fin 6), S ≠ ∅ →
          (∑ z : Fin 6 → Bool, ((∑ j : Fin 6, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) *
          (∑ x : V, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x)) = 0 := by
        intro S hSne
        by_cases hodd : S.card % 2 = 1
        · rw [absW_walsh_odd S hodd, zero_mul]
        · have hcard : S.card = 2 ∨ S.card = 4 ∨ S.card = 6 := by
            have hle : S.card ≤ 6 := by simpa using Finset.card_le_univ S
            have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
            omega
          have hvne : (∑ j ∈ S, v j) ≠ 0 := by
            rcases hcard with h2 | h4' | h6'
            · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
              rw [Finset.sum_pair hab]
              exact vec_sum_pair_ne_zero (fun heq => hab (v.injective heq))
            · exact h46 S (Or.inl h4')
            · exact h46 S (Or.inr h6')
          rw [sum_prod_bitOf_ne v c S hvne, mul_zero]
      rw [Finset.sum_eq_single (∅ : Finset (Fin 6)) (fun S _ hS => hzero_S S hS)
          (fun h => False.elim (h (Finset.mem_univ _)))] at hwalsh
      simp only [Finset.prod_empty, mul_one, Finset.sum_const, nsmul_eq_mul, hcardV] at hwalsh
      rw [absW_sum_6] at hwalsh
      have hlt : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) < (2 ^ k : ℤ) * ((6 : ℤ) + 2) := by
        have h64 : (64 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = 120 * (2 ^ k : ℤ) := by
          change (2 ^ 6 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = 120 * (2 ^ k : ℤ) at hwalsh
          linarith
        nlinarith
      refine ⟨le_of_lt hlt, ?_⟩
      constructor
      · intro heq; omega
      · rintro (h | h | h | h | ⟨h, _, _⟩) <;> omega
    · -- h = 8
      have hwalsh := walsh_abs_sum (fun x j => bitOf (v j) (c j) x)
      dsimp only at hwalsh
      have hzero_S : ∀ S : Finset (Fin 8), S ≠ ∅ → S ≠ Finset.univ →
          (∑ z : Fin 8 → Bool, ((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) *
          (∑ x : V, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x)) = 0 := by
        intro S hSne hSuniv
        by_cases hodd : S.card % 2 = 1
        · rw [absW_walsh_odd S hodd, zero_mul]
        · have hcard : S.card = 2 ∨ S.card = 4 ∨ S.card = 6 := by
            have hlt : S.card < 8 := by
              have hle : S.card ≤ 8 := by simpa using Finset.card_le_univ S
              have hne8 : S.card ≠ 8 := fun hc => hSuniv
                (Finset.eq_univ_of_card S (by simpa using hc))
              omega
            have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
            omega
          have hvne : (∑ j ∈ S, v j) ≠ 0 := by
            rcases hcard with h2 | h4' | h6'
            · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
              rw [Finset.sum_pair hab]
              exact vec_sum_pair_ne_zero (fun heq => hab (v.injective heq))
            · exact h46 S (Or.inl h4')
            · exact h46 S (Or.inr h6')
          rw [sum_prod_bitOf_ne v c S hvne, mul_zero]
      have hpair_sum : (∑ S : Finset (Fin 8),
            (∑ z : Fin 8 → Bool, ((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) *
            (∑ x : V, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x))) =
          560 * (2 ^ k : ℤ) + (-80 : ℤ) * (∑ x : V, ∏ j : Fin 8, sgnB (bitOf (v j) (c j) x)) := by
        have hne0u : (∅ : Finset (Fin 8)) ≠ Finset.univ := by decide
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (∅ : Finset (Fin 8)))]
        have hu_mem : (Finset.univ : Finset (Fin 8)) ∈
            (Finset.univ : Finset (Finset (Fin 8))).erase ∅ :=
          Finset.mem_erase.mpr ⟨hne0u.symm, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hu_mem]
        have hrest : ∑ S ∈ ((Finset.univ : Finset (Finset (Fin 8))).erase ∅).erase Finset.univ,
            (∑ z : Fin 8 → Bool, ((∑ j : Fin 8, sgnB (z j)).natAbs : ℤ) * ∏ j ∈ S, sgnB (z j)) *
            (∑ x : V, ∏ j ∈ S, sgnB (bitOf (v j) (c j) x)) = 0 := by
          refine Finset.sum_eq_zero fun S hS => ?_
          rw [Finset.mem_erase, Finset.mem_erase] at hS
          exact hzero_S S hS.2.1 hS.1
        rw [hrest, add_zero, absW_top_8]
        simp only [Finset.prod_empty, mul_one, Finset.sum_const, nsmul_eq_mul, hcardV]
        rw [absW_sum_8]
      rw [hpair_sum] at hwalsh
      have h256 : (256 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) =
          560 * (2 ^ k : ℤ) + (-80 : ℤ) * (∑ x : V, ∏ j : Fin 8, sgnB (bitOf (v j) (c j) x)) := by
        change (2 ^ 8 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = _ at hwalsh
        linarith
      by_cases hvsum : (∑ j : Fin 8, v j) = 0
      · rw [sum_prod_bitOf_eq v c Finset.univ hvsum, prod_sgnB_eq_ite c Finset.univ] at h256
        by_cases hcpar : ((Finset.univ : Finset (Fin 8)).filter (fun j => c j = true)).card % 2 = 1
        · rw [if_pos hcpar] at h256
          have heq : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = (2 ^ k : ℤ) * ((8 : ℤ) + 2) := by linarith
          exact ⟨le_of_eq heq, ⟨fun _ => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hvsum, hcpar⟩))), fun _ => heq⟩⟩
        · rw [if_neg hcpar] at h256
          have hlt : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) < (2 ^ k : ℤ) * ((8 : ℤ) + 2) := by nlinarith
          refine ⟨le_of_lt hlt, ?_⟩
          constructor
          · intro heq
            change (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = (2 ^ k : ℤ) * ((8 : ℤ) + 2) at heq
            linarith
          · rintro (h | h | h | h | ⟨_, _, h⟩)
            · omega
            · omega
            · omega
            · omega
            · exact False.elim (hcpar h)
      · rw [sum_prod_bitOf_ne v c Finset.univ hvsum, mul_zero, add_zero] at h256
        have hlt : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) < (2 ^ k : ℤ) * ((8 : ℤ) + 2) := by nlinarith
        refine ⟨le_of_lt hlt, ?_⟩
        constructor
        · intro heq
          change (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) = (2 ^ k : ℤ) * ((8 : ℤ) + 2) at heq
          linarith
        · rintro (h | h | h | h | ⟨_, h, _⟩)
          · omega
          · omega
          · omega
          · omega
          · exact False.elim (hvsum h)
    · -- Even h ≥ 10
      have hpt : ∀ x : V, (6 : ℤ) * ((W x).natAbs : ℤ) ≤ (W x) ^ 2 + 8 := by
        intro x
        have hp := hW_par x
        have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
        rw [hsq]
        have hfact : (((W x).natAbs : ℤ) - 2) * (((W x).natAbs : ℤ) - 4) ≥ 0 := by
          have ha : (W x).natAbs = 0 ∨ (W x).natAbs = 2 ∨ 4 ≤ (W x).natAbs := by omega
          rcases ha with h0 | h2 | h4'
          · simp [h0]
          · simp [h2]
          · have : (4 : ℤ) ≤ ((W x).natAbs : ℤ) := by exact_mod_cast h4'
            nlinarith
        nlinarith
      have hsum6 : (6 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) ≤ (2 ^ k : ℤ) * ((h : ℤ) + 8) := by
        calc (6 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ)
            = ∑ x : V, (6 : ℤ) * ((W x).natAbs : ℤ) := Finset.mul_sum _ _ _
          _ ≤ ∑ x : V, ((W x) ^ 2 + 8) := Finset.sum_le_sum fun x _ => hpt x
          _ = (∑ x : V, (W x) ^ 2) + ∑ _x : V, (8 : ℤ) := Finset.sum_add_distrib
          _ = (2 ^ k : ℤ) * (h : ℤ) + (2 ^ k : ℤ) * 8 := by
              rw [hM2, Finset.sum_const, nsmul_eq_mul, hcardV]
          _ = (2 ^ k : ℤ) * ((h : ℤ) + 8) := by ring
      have hstrict : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) < (2 ^ k : ℤ) * ((h : ℤ) + 2) := by
        by_cases h10eq : h = 10
        · subst h10eq
          by_contra hge
          have hge' : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) ≥ (2 ^ k : ℤ) * ((10 : ℤ) + 2) := by omega
          have heq6 : ∑ x : V, ((W x) ^ 2 + 8 - (6 : ℤ) * ((W x).natAbs : ℤ)) = 0 := by
            have h1 : ∑ x : V, ((W x) ^ 2 + 8) = (2 ^ k : ℤ) * ((10 : ℤ) + 8) := by
              rw [Finset.sum_add_distrib, hM2, Finset.sum_const, nsmul_eq_mul, hcardV]; ring
            rw [Finset.sum_sub_distrib, h1, ← Finset.mul_sum]; linarith
          have hall0 : ∀ x : V, (W x) ^ 2 + 8 - (6 : ℤ) * ((W x).natAbs : ℤ) = 0 := by
            intro x
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by linarith [hpt y])).mp heq6 x (Finset.mem_univ x)
          have hpoly : ∀ x : V, (W x) ^ 4 - 20 * (W x) ^ 2 + 64 = 0 := by
            intro x
            have hx := hall0 x
            have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
            have h24 : (W x).natAbs = 2 ∨ (W x).natAbs = 4 := by
              rw [hsq] at hx
              have hfac : (((W x).natAbs : ℤ) - 2) * (((W x).natAbs : ℤ) - 4) = 0 := by linarith
              rcases mul_eq_zero.mp hfac with ha | hb <;> omega
            rcases h24 with h2 | h4'
            · have : (W x) ^ 2 = 4 := by rw [hsq, h2]; norm_num
              calc (W x) ^ 4 - 20 * (W x) ^ 2 + 64 = ((W x) ^ 2) ^ 2 - 20 * (W x) ^ 2 + 64 := by ring
                _ = 0 := by rw [this]; norm_num
            · have : (W x) ^ 2 = 16 := by rw [hsq, h4']; norm_num
              calc (W x) ^ 4 - 20 * (W x) ^ 2 + 64 = ((W x) ^ 2) ^ 2 - 20 * (W x) ^ 2 + 64 := by ring
                _ = 0 := by rw [this]; norm_num
          have hsum0 : ∑ x : V, ((W x) ^ 4 - 20 * (W x) ^ 2 + 64) = 0 :=
            Finset.sum_eq_zero fun x _ => hpoly x
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hM4, hM2,
              Finset.sum_const, nsmul_eq_mul, hcardV] at hsum0
          nlinarith
        · have hge12 : (12 : ℤ) ≤ (h : ℤ) := by omega
          nlinarith
      refine ⟨le_of_lt hstrict, ?_⟩
      constructor
      · intro heq; linarith
      · rintro (h | h | h | h | ⟨h, _, _⟩) <;> omega
  · -- Odd h
    rw [if_neg hpar]
    have hpt : ∀ x : V, (4 : ℤ) * ((W x).natAbs : ℤ) ≤ (W x) ^ 2 + 3 := by
      intro x
      have hp := hW_par x
      have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
      rw [hsq]
      have hfact : (((W x).natAbs : ℤ) - 1) * (((W x).natAbs : ℤ) - 3) ≥ 0 := by
        have ha : (W x).natAbs = 1 ∨ 3 ≤ (W x).natAbs := by omega
        rcases ha with h1 | h3
        · simp [h1]
        · have : (3 : ℤ) ≤ ((W x).natAbs : ℤ) := by exact_mod_cast h3
          nlinarith
      nlinarith
    have hle : (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ) ≤ (2 ^ k : ℤ) * ((h : ℤ) + 3) := by
      calc (4 : ℤ) * ∑ x : V, ((W x).natAbs : ℤ)
          = ∑ x : V, (4 : ℤ) * ((W x).natAbs : ℤ) := Finset.mul_sum _ _ _
        _ ≤ ∑ x : V, ((W x) ^ 2 + 3) := Finset.sum_le_sum fun x _ => hpt x
        _ = (∑ x : V, (W x) ^ 2) + ∑ _x : V, (3 : ℤ) := Finset.sum_add_distrib
        _ = (2 ^ k : ℤ) * (h : ℤ) + (2 ^ k : ℤ) * 3 := by
            rw [hM2, Finset.sum_const, nsmul_eq_mul, hcardV]
        _ = (2 ^ k : ℤ) * ((h : ℤ) + 3) := by ring
    refine ⟨hle, ?_⟩
    constructor
    · intro heq
      have heq0 : ∑ x : V, ((W x) ^ 2 + 3 - (4 : ℤ) * ((W x).natAbs : ℤ)) = 0 := by
        have h1 : ∑ x : V, ((W x) ^ 2 + 3) = (2 ^ k : ℤ) * ((h : ℤ) + 3) := by
          rw [Finset.sum_add_distrib, hM2, Finset.sum_const, nsmul_eq_mul, hcardV]; ring
        rw [Finset.sum_sub_distrib, h1, ← Finset.mul_sum]; linarith
      have hall0 : ∀ x : V, (W x) ^ 2 + 3 - (4 : ℤ) * ((W x).natAbs : ℤ) = 0 := by
        intro x
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by linarith [hpt y])).mp heq0 x (Finset.mem_univ x)
      have hpoly : ∀ x : V, (W x) ^ 4 - 10 * (W x) ^ 2 + 9 = 0 := by
        intro x
        have hx := hall0 x
        have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
        have h13 : (W x).natAbs = 1 ∨ (W x).natAbs = 3 := by
          rw [hsq] at hx
          have hfac : (((W x).natAbs : ℤ) - 1) * (((W x).natAbs : ℤ) - 3) = 0 := by linarith
          rcases mul_eq_zero.mp hfac with ha | hb <;> omega
        rcases h13 with h1 | h3
        · have : (W x) ^ 2 = 1 := by rw [hsq, h1]; norm_num
          calc (W x) ^ 4 - 10 * (W x) ^ 2 + 9 = ((W x) ^ 2) ^ 2 - 10 * (W x) ^ 2 + 9 := by ring
            _ = 0 := by rw [this]; norm_num
        · have : (W x) ^ 2 = 9 := by rw [hsq, h3]; norm_num
          calc (W x) ^ 4 - 10 * (W x) ^ 2 + 9 = ((W x) ^ 2) ^ 2 - 10 * (W x) ^ 2 + 9 := by ring
            _ = 0 := by rw [this]; norm_num
      have hsum0 : ∑ x : V, ((W x) ^ 4 - 10 * (W x) ^ 2 + 9) = 0 :=
        Finset.sum_eq_zero fun x _ => hpoly x
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hM4, hM2,
          Finset.sum_const, nsmul_eq_mul, hcardV] at hsum0
      have hquad : 3 * (h : ℤ) ^ 2 - 12 * (h : ℤ) + 9 = 0 := by nlinarith
      have hfac : ((h : ℤ) - 1) * ((h : ℤ) - 3) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h1 | h3
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · rintro (rfl | h2 | rfl | h4' | ⟨h8, _, _⟩)
      · have hpt1 : ∀ x : V, (4 : ℤ) * ((W x).natAbs : ℤ) = (W x) ^ 2 + 3 := by
          intro x
          have hp := hW_par x; have hl := hW_le_h x
          have ha : (W x).natAbs = 1 := by omega
          have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
          rw [hsq, ha]; norm_num
        rw [Finset.mul_sum, Finset.sum_congr rfl fun x _ => hpt1 x, Finset.sum_add_distrib, hM2,
            Finset.sum_const, nsmul_eq_mul, hcardV]; ring
      · omega
      · have hpt3 : ∀ x : V, (4 : ℤ) * ((W x).natAbs : ℤ) = (W x) ^ 2 + 3 := by
          intro x
          have hp := hW_par x; have hl := hW_le_h x
          have ha : (W x).natAbs = 1 ∨ (W x).natAbs = 3 := by omega
          have hsq : (W x) ^ 2 = ((W x).natAbs : ℤ) ^ 2 := (Int.natAbs_sq (W x)).symm
          rw [hsq]
          rcases ha with h1 | h3
          · simp [h1]
          · simp [h3]
        rw [Finset.mul_sum, Finset.sum_congr rfl fun x _ => hpt3 x, Finset.sum_add_distrib, hM2,
            Finset.sum_const, nsmul_eq_mul, hcardV]; ring
      · omega
      · omega
