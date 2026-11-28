import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_996_aux

private lemma real_abs_sum_eq_sum_abs_of_const {α : Type*} (S : Finset α)
    (f : α → ℝ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hf : ∀ a ∈ S, f a = ε) :
    |∑ a ∈ S, f a| = (S.card : ℝ) := by
  have hsum : ∑ a ∈ S, f a = ε * (S.card : ℝ) := by
    rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum, abs_mul, Nat.abs_cast]
  rcases hε with rfl | rfl <;> simp

private lemma const_of_abs_sum_pm_one {α : Type*} (S : Finset α)
    (f : α → ℝ) (hf : ∀ a ∈ S, f a = 1 ∨ f a = -1)
    (habs : |∑ a ∈ S, f a| = (S.card : ℝ)) :
    (∀ a ∈ S, f a = 1) ∨ (∀ a ∈ S, f a = -1) := by
  have hle : ∑ a ∈ S, f a ≤ (S.card : ℝ) := by
    calc ∑ a ∈ S, f a ≤ ∑ _a ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun a ha => by
            rcases hf a ha with h | h <;> linarith)
      _ = (S.card : ℝ) := by simp
  have hge : -(S.card : ℝ) ≤ ∑ a ∈ S, f a := by
    calc -(S.card : ℝ) = ∑ _a ∈ S, (-1 : ℝ) := by simp
      _ ≤ ∑ a ∈ S, f a := Finset.sum_le_sum (fun a ha => by
            rcases hf a ha with h | h <;> linarith)
  rcases eq_or_eq_neg_of_abs_eq habs with hpos | hneg
  · left
    intro a ha
    by_contra hne
    have hfa : f a = -1 := (hf a ha).resolve_left hne
    have hlt : ∑ x ∈ S, f x < ∑ _x ∈ S, (1 : ℝ) := by
      refine Finset.sum_lt_sum (fun x hx => by rcases hf x hx with h | h <;> linarith)
        ⟨a, ha, by linarith⟩
    simp at hlt
    linarith
  · right
    intro a ha
    by_contra hne
    have hfa : f a = 1 := (hf a ha).resolve_right hne
    have hlt : ∑ _x ∈ S, (-1 : ℝ) < ∑ x ∈ S, f x := by
      refine Finset.sum_lt_sum (fun x hx => by rcases hf x hx with h | h <;> linarith)
        ⟨a, ha, by linarith⟩
    simp at hlt
    linarith

private lemma zmod2_val_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma neg_one_zmod2_add (x y : ZMod 2) :
    (if x + y = 1 then (-1 : ℝ) else 1) =
      (if x = 1 then (-1 : ℝ) else 1) * (if y = 1 then (-1 : ℝ) else 1) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_val_eq_zero_or_one x with rfl | rfl <;>
  rcases zmod2_val_eq_zero_or_one y with rfl | rfl <;>
  simp [h11]

private lemma neg_one_zmod2_sum {α : Type*} (S : Finset α) (g : α → ZMod 2) :
    (if (∑ a ∈ S, g a) = 1 then (-1 : ℝ) else 1) =
      ∏ a ∈ S, (if g a = 1 then (-1 : ℝ) else 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_one_zmod2_add, ih]

private lemma bernoulli_nat_pow (m k : ℕ) (hm : 1 ≤ m) :
    2 ^ k * (m - 1) ^ (m * k) ≤ m ^ (m * k) := by
  have hbase : 2 * (m - 1) ^ m ≤ m ^ m := by
    rcases eq_or_lt_of_le hm with rfl | hm2
    · simp
    · have hq : (2 : ℚ) * ((m - 1 : ℕ) : ℚ) ^ m ≤ (m : ℚ) ^ m := by
        have hpos : (0 : ℚ) < ((m - 1 : ℕ) : ℚ) := by
          exact_mod_cast (by omega : 0 < m - 1)
        have h1 : (1 : ℚ) + (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) ≤
            (1 + 1 / ((m - 1 : ℕ) : ℚ)) ^ m :=
          one_add_mul_le_pow (by linarith [div_pos (one_pos : (0 : ℚ) < 1) hpos]) m
        have h2 : (2 : ℚ) ≤ 1 + (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) := by
          have hlt : ((m - 1 : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.sub_le m 1
          have hge1 : (1 : ℚ) ≤ (m : ℚ) / ((m - 1 : ℕ) : ℚ) := (one_le_div hpos).mpr hlt
          linarith [show (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) = (m : ℚ) / ((m - 1 : ℕ) : ℚ) by ring]
        have h3 : (2 : ℚ) ≤ (1 + 1 / ((m - 1 : ℕ) : ℚ)) ^ m := le_trans h2 h1
        have hfrac : (1 : ℚ) + 1 / ((m - 1 : ℕ) : ℚ) = (m : ℚ) / ((m - 1 : ℕ) : ℚ) := by
          field_simp [ne_of_gt hpos]
          have : (m - 1 : ℕ) + 1 = m := by omega
          exact_mod_cast this
        rw [hfrac, div_pow] at h3
        have hpow_pos : (0 : ℚ) < ((m - 1 : ℕ) : ℚ) ^ m := pow_pos hpos m
        exact (le_div_iff₀ hpow_pos).mp h3
      exact_mod_cast hq
  calc 2 ^ k * (m - 1) ^ (m * k)
      = 2 ^ k * ((m - 1) ^ m) ^ k := by rw [pow_mul]
    _ = (2 * (m - 1) ^ m) ^ k := by rw [mul_pow]
    _ ≤ (m ^ m) ^ k := Nat.pow_le_pow_left hbase k
    _ = m ^ (m * k) := by rw [← pow_mul]

private lemma union_bound_strict (n r : ℕ) :
    3 ^ (n ^ 2) * (2 ^ r - 1) ^ (2 ^ r * (2 * n ^ 2 + 1)) <
      (2 ^ r) ^ (2 ^ r * (2 * n ^ 2 + 1)) := by
  have hm : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h1 := bernoulli_nat_pow (2 ^ r) (2 * n ^ 2 + 1) hm
  have h34 : 3 ^ (n ^ 2) < 2 ^ (2 * n ^ 2 + 1) := by
    have hle : 3 ^ (n ^ 2) ≤ 4 ^ (n ^ 2) := Nat.pow_le_pow_left (by omega) (n ^ 2)
    have h4 : 4 ^ (n ^ 2) = 2 ^ (2 * n ^ 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hpow : 2 ^ (2 * n ^ 2 + 1) = 2 * 2 ^ (2 * n ^ 2) := by
      rw [pow_succ, mul_comm]
    have hpos : 1 ≤ 2 ^ (2 * n ^ 2) := Nat.one_le_two_pow
    omega
  rcases Nat.eq_zero_or_pos ((2 ^ r - 1) ^ (2 ^ r * (2 * n ^ 2 + 1))) with hz | hpos
  · rw [hz, mul_zero]
    exact pow_pos (Nat.two_pow_pos r) _
  · exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h34 hpos) h1

private lemma det_eq_sum_live {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : (Fin n × Fin n) → Bool) :
    Matrix.det (fun i j => if s (i, j) then -A i j else A i j : Matrix (Fin n) (Fin n) ℝ) =
      ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, A (π j) j ≠ 0),
        (Equiv.Perm.sign π : ℝ) *
          ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) * A (π j) j := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => if s (i, j) then -A i j else A i j
  change Matrix.det M = _
  rw [Matrix.det_apply]
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, A (π j) j ≠ 0) ⊆
      Finset.univ := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun π _ => ?_)
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    dsimp only [M]
    by_cases hs : s (π j, j) <;> simp [hs]
  · intro π _ hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hnot
    rcases hnot with ⟨j0, hj0⟩
    rw [Units.smul_def, zsmul_eq_mul]
    have hprod0 : ∏ j : Fin n, M (π j) j = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
      dsimp only [M]
      simp [hj0]
    rw [hprod0, mul_zero]

private lemma perm_abs_eq_sum_live {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.permanent (fun i j => |A i j| : Matrix (Fin n) (Fin n) ℝ) =
      ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, A (π j) j ≠ 0),
        ∏ j : Fin n, |A (π j) j| := by
  classical
  change ∑ π : Equiv.Perm (Fin n), ∏ j : Fin n, |A (π j) j| = _
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, A (π j) j ≠ 0) ⊆
      Finset.univ := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub]
  intro π _ hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hnot
  rcases hnot with ⟨j0, hj0⟩
  refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
  simp [hj0]

private lemma align_implies_abs_det_eq_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : (Fin n × Fin n) → Bool) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (halign : ∀ π : Equiv.Perm (Fin n), (∀ j, A (π j) j ≠ 0) →
      (Equiv.Perm.sign π : ℝ) *
        ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < A (π j) j then (1 : ℝ) else -1) = ε) :
    |Matrix.det (fun i j => if s (i, j) then -A i j else A i j : Matrix (Fin n) (Fin n) ℝ)| =
      Matrix.permanent (fun i j => |A i j| : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  rw [det_eq_sum_live, perm_abs_eq_sum_live]
  have hterm : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, A (π j) j ≠ 0),
      (Equiv.Perm.sign π : ℝ) * ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) * A (π j) j =
      ε * ∏ j : Fin n, |A (π j) j| := by
    intro π hπ
    have hlive : ∀ j, A (π j) j ≠ 0 := (Finset.mem_filter.mp hπ).2
    have hA_split : ∀ j : Fin n,
        (if s (π j, j) then (-1 : ℝ) else 1) * A (π j) j =
        ((if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < A (π j) j then (1 : ℝ) else -1)) * |A (π j) j| := by
      intro j
      have hne := hlive j
      by_cases hpos : 0 < A (π j) j
      · simp only [hpos, ↓reduceIte, abs_of_pos hpos]; ring
      · have hneg : A (π j) j < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
        simp only [hpos, ↓reduceIte, abs_of_neg hneg]; ring
    rw [Finset.prod_congr rfl (fun j _ => hA_split j), Finset.prod_mul_distrib, ← mul_assoc, halign π hlive]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, abs_mul]
  have hnonneg : 0 ≤ ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, A (π j) j ≠ 0),
      ∏ j : Fin n, |A (π j) j| :=
    Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => abs_nonneg _))
  rw [abs_of_nonneg hnonneg]
  rcases hε with rfl | rfl <;> simp

private lemma deg2_implies_rank_and_align {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i : Fin n, ((Finset.univ : Finset (Fin n)).filter (fun j => A i j ≠ 0)).card ≤ 2)
    (hcol : ∀ j : Fin n, ((Finset.univ : Finset (Fin n)).filter (fun i => A i j ≠ 0)).card ≤ 2) :
    let H : Matrix (Fin n) (Fin n) ℝ := fun i j => if A i j = 0 then 0 else 1
    let live := fun π : Equiv.Perm (Fin n) => ∀ j, A (π j) j ≠ 0
    let vec := fun (π : Equiv.Perm (Fin n)) (e : Fin n × Fin n) => if π e.2 = e.1 then (1 : ZMod 2) else 0
    let V := Submodule.span (ZMod 2) {z : (Fin n × Fin n) → ZMod 2 | ∃ π τ : Equiv.Perm (Fin n),
      live π ∧ live τ ∧ z = vec π - vec τ}
    Module.finrank (ZMod 2) V ≤ n / 2 ∧
      ∃ s : (Fin n × Fin n) → Bool,
        |Matrix.det (fun i j => if s (i, j) then -H i j else H i j : Matrix (Fin n) (Fin n) ℝ)| = H.permanent := by
  classical
  dsimp only
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j => if A i j = 0 then 0 else 1
  let live := fun π : Equiv.Perm (Fin n) => ∀ j, A (π j) j ≠ 0
  let vec := fun (π : Equiv.Perm (Fin n)) (e : Fin n × Fin n) => if π e.2 = e.1 then (1 : ZMod 2) else 0
  let V := Submodule.span (ZMod 2) {z : (Fin n × Fin n) → ZMod 2 | ∃ π τ : Equiv.Perm (Fin n),
    live π ∧ live τ ∧ z = vec π - vec τ}
  by_cases hex : ∃ π : Equiv.Perm (Fin n), live π
  · rcases hex with ⟨π0, hπ0⟩
    let Moved : Finset (Fin n) := Finset.univ.filter (fun j => ∃ π : Equiv.Perm (Fin n), live π ∧ π j ≠ π0 j)
    have huniq_col : ∀ j : Fin n, ∀ i1 i2 : Fin n,
        A i1 j ≠ 0 → A i2 j ≠ 0 → i1 ≠ π0 j → i2 ≠ π0 j → i1 = i2 := by
      intro j i1 i2 h1 h2 hne1 hne2
      by_contra h12
      let T : Finset (Fin n) := {π0 j, i1, i2}
      have hsub : T ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => A i j ≠ 0) := by
        intro i hi
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hi with rfl | rfl | rfl
        · exact hπ0 j
        · exact h1
        · exact h2
      have hcard3 : T.card = 3 := by
        dsimp only [T]
        rw [Finset.card_insert_of_notMem, Finset.card_pair h12]
        simp [hne1.symm, hne2.symm]
      have hle := Finset.card_le_card hsub
      have hle2 := hcol j
      omega
    have huniq_row : ∀ i : Fin n, ∀ j1 j2 : Fin n,
        A i j1 ≠ 0 → A i j2 ≠ 0 → π0 j1 ≠ i → π0 j2 ≠ i → j1 = j2 := by
      intro i j1 j2 h1 h2 hne1 hne2
      by_contra h12
      let j0 := π0.symm i
      have hj0 : π0 j0 = i := π0.apply_symm_apply i
      let T : Finset (Fin n) := {j0, j1, j2}
      have hsub : T ⊆ (Finset.univ : Finset (Fin n)).filter (fun j => A i j ≠ 0) := by
        intro j hj
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl | rfl
        · rw [← hj0]; exact hπ0 j0
        · exact h1
        · exact h2
      have hne01 : j0 ≠ j1 := fun h => hne1 (h ▸ hj0)
      have hne02 : j0 ≠ j2 := fun h => hne2 (h ▸ hj0)
      have hcard3 : T.card = 3 := by
        dsimp only [T]
        rw [Finset.card_insert_of_notMem, Finset.card_pair h12]
        simp [hne01, hne02]
      have hle := Finset.card_le_card hsub
      have hle2 := hrow i
      omega
    have hex_next : ∀ j : Fin n, j ∈ Moved → ∃ j' : Fin n, j' ≠ j ∧ A (π0 j') j ≠ 0 := by
      intro j hj
      rcases (Finset.mem_filter.mp hj).2 with ⟨π, hπ, hne⟩
      refine ⟨π0.symm (π j), ?_, ?_⟩
      · intro heq
        apply hne
        have := congrArg π0 heq
        rwa [π0.apply_symm_apply] at this
      · rw [π0.apply_symm_apply]; exact hπ j
    let ρFun : Fin n → Fin n := fun j =>
      if hj : j ∈ Moved then Classical.choose (hex_next j hj) else j
    have hρ_moved : ∀ j (hj : j ∈ Moved), ρFun j ≠ j ∧ A (π0 (ρFun j)) j ≠ 0 := by
      intro j hj
      dsimp only [ρFun]
      simp only [hj, ↓reduceDIte]
      exact Classical.choose_spec (hex_next j hj)
    have hρ_not_moved : ∀ j, j ∉ Moved → ρFun j = j := by
      intro j hj
      dsimp only [ρFun]
      simp only [hj, ↓reduceDIte]
    have hρ_live : ∀ j : Fin n, A (π0 (ρFun j)) j ≠ 0 := by
      intro j
      by_cases hj : j ∈ Moved
      · exact (hρ_moved j hj).2
      · rw [hρ_not_moved j hj]; exact hπ0 j
    have hρ_inj : Function.Injective ρFun := by
      intro j1 j2 heq
      by_cases h1 : j1 ∈ Moved <;> by_cases h2 : j2 ∈ Moved
      · have hm1 := hρ_moved j1 h1
        have hm2 := hρ_moved j2 h2
        rw [← heq] at hm2
        exact huniq_row (π0 (ρFun j1)) j1 j2 hm1.2 hm2.2
          (fun h => hm1.1 (π0.injective h).symm) (fun h => hm2.1 (π0.injective h).symm)
      · rw [hρ_not_moved j2 h2] at heq
        have hm1 := hρ_moved j1 h1
        rw [heq] at hm1
        rcases (Finset.mem_filter.mp h1).2 with ⟨π, hπ, hne⟩
        have hπj1 : π j1 = π0 j2 := huniq_col j1 (π j1) (π0 j2) (hπ j1) hm1.2 hne
          (fun h => hm1.1 (π0.injective h))
        have hπj2 : π j2 ≠ π0 j2 := fun h => hm1.1 (π.injective (h.trans hπj1.symm))
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, hπj2⟩) h2
      · rw [hρ_not_moved j1 h1] at heq
        have hm2 := hρ_moved j2 h2
        rw [← heq] at hm2
        rcases (Finset.mem_filter.mp h2).2 with ⟨π, hπ, hne⟩
        have hπj2 : π j2 = π0 j1 := huniq_col j2 (π j2) (π0 j1) (hπ j2) hm2.2 hne
          (fun h => hm2.1 (π0.injective h))
        have hπj1 : π j1 ≠ π0 j1 := fun h => hm2.1 (π.injective (h.trans hπj2.symm))
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, hπj1⟩) h1
      · rw [hρ_not_moved j1 h1, hρ_not_moved j2 h2] at heq
        exact heq
    let ρ : Equiv.Perm (Fin n) := Equiv.ofBijective ρFun (Finite.injective_iff_bijective.mp hρ_inj)
    have hρ_apply : ∀ j, ρ j = ρFun j := fun _ => rfl
    have hπ_cases : ∀ π : Equiv.Perm (Fin n), live π → ∀ j : Fin n,
        π j = π0 j ∨ (j ∈ Moved ∧ π j = π0 (ρ j)) := by
      intro π hπ j
      by_cases h : π j = π0 j
      · exact Or.inl h
      · have hjM : j ∈ Moved := Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, h⟩
        have hm := hρ_moved j hjM
        refine Or.inr ⟨hjM, huniq_col j (π j) (π0 (ρ j)) (hπ j) hm.2 h (fun heq => hm.1 (π0.injective heq))⟩
    let sameOrb : Fin n → Fin n → Prop := fun j1 j2 => ∃ k : ℤ, (ρ ^ k) j1 = j2
    have hso_refl : ∀ j, sameOrb j j := fun j => ⟨0, by simp⟩
    have hso_symm : ∀ {j1 j2}, sameOrb j1 j2 → sameOrb j2 j1 := by
      rintro j1 j2 ⟨k, rfl⟩
      exact ⟨-k, by rw [← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero]; rfl⟩
    have hso_trans : ∀ {j1 j2 j3}, sameOrb j1 j2 → sameOrb j2 j3 → sameOrb j1 j3 := by
      rintro j1 j2 j3 ⟨k1, rfl⟩ ⟨k2, rfl⟩
      exact ⟨k2 + k1, by rw [zpow_add, Equiv.Perm.mul_apply]⟩
    have hso_step : ∀ j, sameOrb j (ρ j) := fun j => ⟨1, by simp⟩
    let orb : Fin n → Finset (Fin n) := fun j => Finset.univ.filter (fun j' => sameOrb j j')
    have horb_mem : ∀ j j', j' ∈ orb j ↔ sameOrb j j' := by
      intro j j'; simp [orb]
    have horb_self : ∀ j, j ∈ orb j := fun j => (horb_mem j j).mpr (hso_refl j)
    have horb_eq : ∀ {j1 j2}, j2 ∈ orb j1 → orb j1 = orb j2 := by
      intro j1 j2 h
      have hs := (horb_mem j1 j2).mp h
      ext x
      simp only [horb_mem]
      exact ⟨fun hx => hso_trans (hso_symm hs) hx, fun hx => hso_trans hs hx⟩
    have horb_disj : ∀ {j1 j2}, orb j1 ≠ orb j2 → Disjoint (orb j1) (orb j2) := by
      intro j1 j2 hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hne ((horb_eq hx1).trans (horb_eq hx2).symm)
    let Orbs : Finset (Finset (Fin n)) := Moved.image orb
    have hOrbs_card_ge2 : ∀ O ∈ Orbs, 2 ≤ O.card := by
      intro O hO
      rcases Finset.mem_image.mp hO with ⟨j, hjM, rfl⟩
      have hne : ρ j ≠ j := (hρ_moved j hjM).1
      have hsub : ({j, ρ j} : Finset (Fin n)) ⊆ orb j := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxj | hxj
        · rw [hxj]; exact horb_self j
        · rw [hxj]; exact (horb_mem j (ρ j)).mpr (hso_step j)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hne.symm] at hle
      exact hle
    have hOrbs_disj : Set.PairwiseDisjoint (Orbs : Set (Finset (Fin n))) id := by
      intro O1 hO1 O2 hO2 hne
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hO1) with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hO2) with ⟨j2, _, rfl⟩
      exact horb_disj hne
    have hOrbs_count : Orbs.card ≤ n / 2 := by
      have hsum_ge : 2 * Orbs.card ≤ ∑ O ∈ Orbs, O.card := by
        calc 2 * Orbs.card = ∑ _O ∈ Orbs, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ O ∈ Orbs, O.card := Finset.sum_le_sum hOrbs_card_ge2
      have hsum_le : ∑ O ∈ Orbs, O.card ≤ n := by
        change ∑ O ∈ Orbs, (id O).card ≤ n
        rw [← Finset.card_biUnion (fun O1 h1 O2 h2 hne => hOrbs_disj h1 h2 hne)]
        calc (Orbs.biUnion id).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      omega
    have hS_inv : ∀ π : Equiv.Perm (Fin n), live π → ∀ j : Fin n,
        π j ≠ π0 j → π (ρ j) ≠ π0 (ρ j) := by
      intro π hπ j hne
      rcases hπ_cases π hπ j with h | ⟨hjM, hπj⟩
      · exact absurd h hne
      · have hne_ρ : ρ j ≠ j := (hρ_moved j hjM).1
        intro heq
        exact hne_ρ (π.injective (heq.trans hπj.symm))
    have hS_orb_closed : ∀ π : Equiv.Perm (Fin n), live π → ∀ j : Fin n,
        π j ≠ π0 j → ∀ j' ∈ orb j, π j' ≠ π0 j' := by
      intro π hπ j hne j' hj'
      have hpos : ∀ k : ℕ, π ((ρ ^ k) j) ≠ π0 ((ρ ^ k) j) := by
        intro k
        induction k with
        | zero => simpa using hne
        | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact hS_inv π hπ _ ih
      rcases (horb_mem j j').mp hj' with ⟨k, rfl⟩
      have hfin : ∃ m : ℕ, (ρ ^ k) j = (ρ ^ m) j := by
        have hord : 0 < orderOf ρ := orderOf_pos ρ
        let d : ℕ := orderOf ρ
        have hpow_d : ρ ^ d = 1 := pow_orderOf_eq_one ρ
        let r_mod : ℕ := (k % (d : ℤ)).toNat
        have hmod_nonneg : 0 ≤ k % (d : ℤ) := Int.emod_nonneg k (by positivity)
        have hmod_eq : (r_mod : ℤ) = k % (d : ℤ) := Int.toNat_of_nonneg hmod_nonneg
        refine ⟨r_mod, ?_⟩
        have hk : k = (d : ℤ) * (k / (d : ℤ)) + (r_mod : ℤ) := by
          rw [hmod_eq]; exact (Int.mul_ediv_add_emod k (d : ℤ)).symm
        rw [hk, zpow_add, zpow_mul, zpow_natCast, hpow_d, one_zpow, one_mul, zpow_natCast]
      rcases hfin with ⟨m, hm⟩
      rw [hm]
      exact hpos m
    let vOrb : Finset (Fin n) → (Fin n × Fin n) → ZMod 2 := fun O e =>
      if e.2 ∈ O ∧ (e.1 = π0 e.2 ∨ e.1 = π0 (ρ e.2)) then 1 else 0
    have hdiff_mem_span : ∀ π : Equiv.Perm (Fin n), live π →
        vec π - vec π0 ∈ Submodule.span (ZMod 2) (vOrb '' (Orbs : Set (Finset (Fin n)))) := by
      intro π hπ
      let Act : Finset (Finset (Fin n)) := Orbs.filter (fun O => ∀ j ∈ O, π j ≠ π0 j)
      have hvec_eq : vec π - vec π0 = ∑ O ∈ Act, vOrb O := by
        funext ⟨i, j⟩
        rw [Pi.sub_apply, Finset.sum_apply]
        by_cases hne : π j = π0 j
        · have hzero : ∀ O ∈ Act, vOrb O (i, j) = 0 := by
            intro O hO
            have hnot : j ∉ O := fun hjO => (Finset.mem_filter.mp hO).2 j hjO hne
            simp [vOrb, hnot]
          rw [Finset.sum_eq_zero hzero]
          simp [vec, hne]
        · have hjM : j ∈ Moved := Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, hne⟩
          have horb_mem_Act : orb j ∈ Act := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_image_of_mem orb hjM, hS_orb_closed π hπ j hne⟩
          rw [Finset.sum_eq_single (orb j)]
          · have hπj : π j = π0 (ρ j) := (hπ_cases π hπ j).resolve_left hne |>.2
            have hne_i : π0 (ρ j) ≠ π0 j := fun h => (hρ_moved j hjM).1 (π0.injective h)
            dsimp only [vec, vOrb]
            rw [hπj]
            simp only [horb_self j, true_and]
            by_cases hi1 : i = π0 j
            · subst hi1
              simp only [hne_i, ↓reduceIte, true_or]
              decide
            · by_cases hi2 : i = π0 (ρ j)
              · subst hi2
                simp only [↓reduceIte, or_true, Ne.symm hi1]
                decide
              · simp [Ne.symm hi1, Ne.symm hi2, hi1, hi2]
          · intro O hO hOne
            have hdisj : Disjoint O (orb j) :=
              hOrbs_disj (Finset.mem_coe.mpr (Finset.mem_filter.mp hO).1)
                (Finset.mem_coe.mpr (Finset.mem_image_of_mem orb hjM)) hOne
            have hnot : j ∉ O := Finset.disjoint_right.mp hdisj (horb_self j)
            simp [vOrb, hnot]
          · intro hnu; exact absurd horb_mem_Act hnu
      rw [hvec_eq]
      refine Submodule.sum_mem _ (fun O hO => ?_)
      exact Submodule.subset_span ⟨O, Finset.mem_coe.mpr (Finset.mem_filter.mp hO).1, rfl⟩
    have hV_le : V ≤ Submodule.span (ZMod 2) (vOrb '' (Orbs : Set (Finset (Fin n)))) := by
      rw [Submodule.span_le]
      rintro z ⟨π, τ, hπ, hτ, rfl⟩
      have heq : vec π - vec τ = (vec π - vec π0) - (vec τ - vec π0) := by abel
      rw [SetLike.mem_coe, heq]
      exact Submodule.sub_mem _ (hdiff_mem_span π hπ) (hdiff_mem_span τ hτ)
    have hrank_le : Module.finrank (ZMod 2) V ≤ n / 2 := by
      have h1 := Submodule.finrank_mono hV_le
      have h2 := finrank_span_le_card (R := ZMod 2) (vOrb '' (Orbs : Set (Finset (Fin n))))
      have h3 : (vOrb '' (Orbs : Set (Finset (Fin n)))).toFinset.card ≤ Orbs.card := by
        have hsub : (vOrb '' (Orbs : Set (Finset (Fin n)))).toFinset ⊆ Orbs.image vOrb := by
          intro x hx
          rw [Set.mem_toFinset] at hx
          rcases hx with ⟨O, hO, rfl⟩
          exact Finset.mem_image_of_mem vOrb (Finset.mem_coe.mp hO)
        exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
      omega
    refine ⟨hrank_le, ?_⟩
    have horb_inv : ∀ O ∈ Orbs, ∀ j : Fin n, j ∈ O ↔ ρ j ∈ O := by
      intro O hO j
      rcases Finset.mem_image.mp hO with ⟨j0, _, rfl⟩
      simp only [horb_mem]
      exact ⟨fun h => hso_trans h (hso_step j), fun h => hso_trans h (hso_symm (hso_step j))⟩
    let ρOrb : Finset (Fin n) → Equiv.Perm (Fin n) := fun O =>
      if hO : O ∈ Orbs then
        Equiv.ofBijective (fun j => if j ∈ O then ρ j else j)
          (Finite.injective_iff_bijective.mp (by
            intro j1 j2 heq
            dsimp only at heq
            by_cases h1 : j1 ∈ O <;> by_cases h2 : j2 ∈ O
            · simp only [h1, h2, ↓reduceIte] at heq; exact ρ.injective heq
            · simp only [h1, h2, ↓reduceIte] at heq
              exact absurd (heq ▸ (horb_inv O hO j1).mp h1) h2
            · simp only [h1, h2, ↓reduceIte] at heq
              exact absurd (heq.symm ▸ (horb_inv O hO j2).mp h2) h1
            · simp only [h1, h2, ↓reduceIte] at heq; exact heq))
      else 1
    have hρOrb_apply : ∀ O ∈ Orbs, ∀ j : Fin n, ρOrb O j = if j ∈ O then ρ j else j := by
      intro O hO j
      dsimp only [ρOrb]
      simp only [hO, ↓reduceDIte]
      rfl
    have hOrbs_ne : ∀ O ∈ Orbs, O.Nonempty := fun O hO =>
      Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) (hOrbs_card_ge2 O hO))
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · refine ⟨fun _ => false, ?_⟩
      change |Matrix.det H| =
        ∑ π : Equiv.Perm (Fin 0), ∏ j : Fin 0, H (π j) j
      rw [Matrix.det_apply]
      simp
    let rep : Finset (Fin n) → Fin n := fun O =>
      if hO : O ∈ Orbs then Classical.choose (hOrbs_ne O hO) else ⟨0, hn0⟩
    have hrep_mem : ∀ O ∈ Orbs, rep O ∈ O := by
      intro O hO
      dsimp only [rep]
      simp only [hO, ↓reduceDIte]
      exact Classical.choose_spec (hOrbs_ne O hO)
    let s : (Fin n × Fin n) → Bool := fun e =>
      decide (∃ O ∈ Orbs, e.2 = rep O ∧ e.1 = π0 (ρ e.2) ∧ (Equiv.Perm.sign (ρOrb O) : ℤ) = -1)
    refine ⟨s, ?_⟩
    have hH_live : ∀ π : Equiv.Perm (Fin n), (∀ j, H (π j) j ≠ 0) ↔ live π := by
      intro π
      constructor <;> intro h j <;> have hj := h j <;> dsimp only [H] at *
      · by_contra hz; simp [hz] at hj
      · simp [hj]
    have hH_pos : ∀ i j : Fin n, A i j ≠ 0 → 0 < H i j := by
      intro i j h; dsimp only [H]; simp [h]
    have hH_abs : (fun i j => |H i j| : Matrix (Fin n) (Fin n) ℝ) = H := by
      ext i j; dsimp only [H]; split_ifs <;> simp
    change |Matrix.det (fun i j => if s (i, j) then -H i j else H i j : Matrix (Fin n) (Fin n) ℝ)| = H.permanent
    conv_rhs => rw [← hH_abs]
    refine align_implies_abs_det_eq_perm H s (Equiv.Perm.sign π0 : ℝ)
      (by rcases Int.units_eq_one_or (Equiv.Perm.sign π0) with h | h <;> simp [h]) ?_
    intro π hπH
    have hπ : live π := (hH_live π).mp hπH
    let Act : Finset (Finset (Fin n)) := Orbs.filter (fun O => ∀ j ∈ O, π j ≠ π0 j)
    have hprod_perm : ∀ L : List (Finset (Fin n)), (∀ O ∈ L, O ∈ Orbs) →
        L.Pairwise (fun O1 O2 => Disjoint O1 O2) →
        ∀ j : Fin n, (L.map ρOrb).prod j = if (∃ O ∈ L, j ∈ O) then ρ j else j := by
      intro L
      induction L with
      | nil => intro _ _ j; simp
      | cons O L ih =>
        intro hmem hpw j
        have hO : O ∈ Orbs := hmem O List.mem_cons_self
        have hL : ∀ O' ∈ L, O' ∈ Orbs := fun O' hO' => hmem O' (List.mem_cons_of_mem _ hO')
        have hpw_cons := List.pairwise_cons.mp hpw
        rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hL hpw_cons.2, hρOrb_apply O hO]
        by_cases hjO : j ∈ O
        · have hnotL : ¬ ∃ O' ∈ L, j ∈ O' := by
            rintro ⟨O', hO'L, hjO'⟩
            exact Finset.disjoint_left.mp (hpw_cons.1 O' hO'L) hjO hjO'
          simp only [hnotL, ↓reduceIte, hjO, List.mem_cons, exists_eq_or_imp, true_or]
        · by_cases hjL : ∃ O' ∈ L, j ∈ O'
          · rcases hjL with ⟨O', hO'L, hjO'⟩
            have hρjO' : ρ j ∈ O' := (horb_inv O' (hL O' hO'L) j).mp hjO'
            have hρj_notO : ρ j ∉ O := Finset.disjoint_right.mp (hpw_cons.1 O' hO'L) hρjO'
            have hexL : ∃ O' ∈ L, j ∈ O' := ⟨O', hO'L, hjO'⟩
            simp only [hjO, hexL, hρj_notO, List.mem_cons, exists_eq_or_imp, false_or, ↓reduceIte]
          · simp only [hjO, hjL, ↓reduceIte, List.mem_cons, exists_eq_or_imp, or_self]
    have hπ_decomp : π0⁻¹ * π = (Act.toList.map ρOrb).prod := by
      have hmemL : ∀ O ∈ Act.toList, O ∈ Orbs := fun O hO =>
        (Finset.mem_filter.mp (Finset.mem_toList.mp hO)).1
      have hpwL : Act.toList.Pairwise (fun O1 O2 => Disjoint O1 O2) := by
        have hnd : Act.toList.Nodup := Finset.nodup_toList Act
        exact hnd.imp_of_mem (fun {O1 O2} h1 h2 hne =>
          hOrbs_disj (Finset.mem_coe.mpr (hmemL O1 h1)) (Finset.mem_coe.mpr (hmemL O2 h2)) hne)
      apply Equiv.ext
      intro j
      rw [hprod_perm Act.toList hmemL hpwL j, Equiv.Perm.mul_apply]
      by_cases hne : π j = π0 j
      · have hnot : ¬ ∃ O ∈ Act.toList, j ∈ O := by
          rintro ⟨O, hOL, hjO⟩
          exact (Finset.mem_filter.mp (Finset.mem_toList.mp hOL)).2 j hjO hne
        simp only [hnot, ↓reduceIte]
        rw [hne]; exact π0.symm_apply_apply j
      · have hjM : j ∈ Moved := Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, hne⟩
        have hex : ∃ O ∈ Act.toList, j ∈ O :=
          ⟨orb j, Finset.mem_toList.mpr (Finset.mem_filter.mpr
            ⟨Finset.mem_image_of_mem orb hjM, hS_orb_closed π hπ j hne⟩), horb_self j⟩
        simp only [hex, ↓reduceIte]
        have hπj : π j = π0 (ρ j) := (hπ_cases π hπ j).resolve_left hne |>.2
        rw [hπj]; exact π0.symm_apply_apply (ρ j)
    have hsign_eq : (Equiv.Perm.sign π : ℝ) =
        (Equiv.Perm.sign π0 : ℝ) * ∏ O ∈ Act, (Equiv.Perm.sign (ρOrb O) : ℝ) := by
      have hmul : π = π0 * (Act.toList.map ρOrb).prod := by
        rw [← hπ_decomp, mul_inv_cancel_left]
      let toR : ℤˣ →* ℝ :=
        { toFun := fun u => (u : ℝ)
          map_one' := by simp
          map_mul' := fun a b => by simp }
      have hlist : (Act.toList.map (fun O => (Equiv.Perm.sign (ρOrb O) : ℝ))).prod =
          ∏ O ∈ Act, (Equiv.Perm.sign (ρOrb O) : ℝ) := by
        rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList Act, Multiset.map_coe, Multiset.prod_coe]
      have hs1 : toR (Equiv.Perm.sign π) =
          toR (Equiv.Perm.sign π0) * (Act.toList.map (fun O => toR (Equiv.Perm.sign (ρOrb O)))).prod := by
        rw [hmul, map_mul, map_mul, map_list_prod, map_list_prod, List.map_map, List.map_map]
        rfl
      simpa only [toR, MonoidHom.coe_mk, OneHom.coe_mk, hlist] using hs1
    have hprod_s : ∏ j : Fin n,
        (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < H (π j) j then (1 : ℝ) else -1) =
        ∏ O ∈ Act, (Equiv.Perm.sign (ρOrb O) : ℝ) := by
      have hpos_term : ∀ j : Fin n,
          (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < H (π j) j then (1 : ℝ) else -1) =
          if s (π j, j) then (-1 : ℝ) else 1 := by
        intro j
        simp only [hH_pos (π j) j (hπ j), ↓reduceIte, mul_one]
      rw [Finset.prod_congr rfl (fun j _ => hpos_term j)]
      let Reps : Finset (Fin n) := Act.image rep
      have hsub_reps : Reps ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.prod_subset hsub_reps]
      · rw [Finset.prod_image]
        · refine Finset.prod_congr rfl (fun O hO => ?_)
          have hO_Orbs : O ∈ Orbs := (Finset.mem_filter.mp hO).1
          have hrepO : rep O ∈ O := hrep_mem O hO_Orbs
          have hne_rep : π (rep O) ≠ π0 (rep O) := (Finset.mem_filter.mp hO).2 (rep O) hrepO
          have hπ_rep : π (rep O) = π0 (ρ (rep O)) :=
            (hπ_cases π hπ (rep O)).resolve_left hne_rep |>.2
          have hs_iff : s (π (rep O), rep O) = true ↔ (Equiv.Perm.sign (ρOrb O) : ℤ) = -1 := by
            simp only [s, decide_eq_true_eq]
            constructor
            · rintro ⟨O', hO', hreq, _, hsg⟩
              have hsame : O' = O := by
                by_contra hne
                exact Finset.disjoint_left.mp
                  (hOrbs_disj (Finset.mem_coe.mpr hO') (Finset.mem_coe.mpr hO_Orbs) hne)
                  (hreq ▸ hrep_mem O' hO') hrepO
              rwa [hsame] at hsg
            · intro hsg
              exact ⟨O, hO_Orbs, rfl, hπ_rep, hsg⟩
          rcases Int.units_eq_one_or (Equiv.Perm.sign (ρOrb O)) with h1 | h1
          · have hsf : s (π (rep O), rep O) = false := by
              by_contra ht
              have htr : s (π (rep O), rep O) = true := Bool.eq_true_of_not_eq_false ht
              have := hs_iff.mp htr
              rw [h1] at this; norm_num at this
            simp [hsf, h1]
          · have hst : s (π (rep O), rep O) = true := hs_iff.mpr (by rw [h1]; rfl)
            simp [hst, h1]
        · intro O1 hO1 O2 hO2 heq
          by_contra hne
          exact Finset.disjoint_left.mp
            (hOrbs_disj (Finset.mem_coe.mpr (Finset.mem_filter.mp hO1).1)
              (Finset.mem_coe.mpr (Finset.mem_filter.mp hO2).1) hne)
            (hrep_mem O1 (Finset.mem_filter.mp hO1).1)
            (heq ▸ hrep_mem O2 (Finset.mem_filter.mp hO2).1)
      · intro j _ hnot
        have hsf : s (π j, j) = false := by
          by_contra ht
          have htr : s (π j, j) = true := Bool.eq_true_of_not_eq_false ht
          simp only [s, decide_eq_true_eq] at htr
          rcases htr with ⟨O, hO_Orbs, rfl, hπeq, _⟩
          have hjO : rep O ∈ O := hrep_mem O hO_Orbs
          have hjM : rep O ∈ Moved := by
            rcases Finset.mem_image.mp hO_Orbs with ⟨j0, hj0M, hOeq⟩
            have hso := (horb_mem j0 (rep O)).mp (hOeq ▸ hjO)
            have hne_ρ : ρ (rep O) ≠ rep O := by
              intro hfix
              have hfix0 : ρ j0 = j0 := by
                rcases hso with ⟨k, hk⟩
                rw [← hk] at hfix
                have hcomm : (ρ ^ k) (ρ j0) = ρ ((ρ ^ k) j0) := by
                  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, Commute.zpow_left rfl]
                exact (ρ ^ k).injective (hcomm.trans hfix)
              exact (hρ_moved j0 hj0M).1 hfix0
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, fun h =>
              hne_ρ (π0.injective (hπeq.symm.trans h))⟩
          have hne_rep : π (rep O) ≠ π0 (rep O) := fun h =>
            (hρ_moved (rep O) hjM).1 (π0.injective (hπeq.symm.trans h))
          have hO_eq : O = orb (rep O) := by
            rcases Finset.mem_image.mp hO_Orbs with ⟨j0, _, rfl⟩
            exact horb_eq hjO
          have hO_Act : O ∈ Act := by
            rw [Finset.mem_filter]
            exact ⟨hO_Orbs, fun j' hj' => hS_orb_closed π hπ (rep O) hne_rep j' (hO_eq ▸ hj')⟩
          exact hnot (Finset.mem_image_of_mem rep hO_Act)
        simp [hsf]
    rw [hsign_eq, hprod_s, mul_assoc]
    have hsq : (∏ O ∈ Act, (Equiv.Perm.sign (ρOrb O) : ℝ)) *
        (∏ O ∈ Act, (Equiv.Perm.sign (ρOrb O) : ℝ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one (fun O _ => ?_)
      rcases Int.units_eq_one_or (Equiv.Perm.sign (ρOrb O)) with h | h <;> rw [h] <;> norm_num
    rw [hsq, mul_one]
  · push Not at hex
    have hV_bot : V = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro z ⟨π, _, hπ, _, _⟩
      exact absurd hπ (hex π)
    refine ⟨by change Module.finrank (ZMod 2) V ≤ n / 2; rw [hV_bot, finrank_bot]; exact Nat.zero_le _,
      fun _ => false, ?_⟩
    have hH_abs : (fun i j => |H i j| : Matrix (Fin n) (Fin n) ℝ) = H := by
      ext i j; dsimp only [H]; split_ifs <;> simp
    change |Matrix.det (fun i j => if (fun _ => false) (i, j) then -H i j else H i j : Matrix (Fin n) (Fin n) ℝ)| = H.permanent
    conv_rhs => rw [← hH_abs]
    rw [det_eq_sum_live H (fun _ => false), perm_abs_eq_sum_live H]
    have hemp : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, H (π j) j ≠ 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro π _ h
      apply hex π
      intro j
      have hj := h j
      dsimp only [H] at hj
      by_contra hz
      simp [hz] at hj
    simp [hemp]

open Classical in
private lemma card_align_ge {n r : ℕ} (P : (Fin n × Fin n) → Fin 3)
    (hvalid :
      let H : Matrix (Fin n) (Fin n) ℝ := fun i j => if P (i, j) = 0 then 0 else 1
      let live := fun π : Equiv.Perm (Fin n) => ∀ j, P (π j, j) ≠ 0
      let vec := fun (π : Equiv.Perm (Fin n)) (e : Fin n × Fin n) => if π e.2 = e.1 then (1 : ZMod 2) else 0
      let V := Submodule.span (ZMod 2) {z : (Fin n × Fin n) → ZMod 2 | ∃ π τ : Equiv.Perm (Fin n),
        live π ∧ live τ ∧ z = vec π - vec τ}
      Module.finrank (ZMod 2) V ≤ r ∧
        ∃ s : (Fin n × Fin n) → Bool,
          |Matrix.det (fun i j => if s (i, j) then -H i j else H i j : Matrix (Fin n) (Fin n) ℝ)| = H.permanent) :
    let B : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      if P (i, j) = 0 then 0 else if P (i, j) = 1 then 1 else -1
    let Good : Finset ((Fin n × Fin n) → Bool) := Finset.univ.filter (fun s =>
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ π : Equiv.Perm (Fin n), (∀ j, P (π j, j) ≠ 0) →
          (Equiv.Perm.sign π : ℝ) *
            ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < B (π j) j then (1 : ℝ) else -1) = ε)
    2 ^ (n ^ 2) ≤ 2 ^ r * Good.card := by
  classical
  dsimp only at hvalid ⊢
  rcases hvalid with ⟨hrank, s0, hs0⟩
  let E := Fin n × Fin n
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j => if P (i, j) = 0 then 0 else 1
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if P (i, j) = 0 then 0 else if P (i, j) = 1 then 1 else -1
  let live := fun π : Equiv.Perm (Fin n) => ∀ j, P (π j, j) ≠ 0
  let vec := fun (π : Equiv.Perm (Fin n)) (e : E) => if π e.2 = e.1 then (1 : ZMod 2) else 0
  let V := Submodule.span (ZMod 2) {z : E → ZMod 2 | ∃ π τ : Equiv.Perm (Fin n),
    live π ∧ live τ ∧ z = vec π - vec τ}
  change Module.finrank (ZMod 2) V ≤ r at hrank
  change |Matrix.det (fun i j => if s0 (i, j) then -H i j else H i j : Matrix (Fin n) (Fin n) ℝ)| = H.permanent at hs0
  let Good : Finset (E → Bool) := Finset.univ.filter (fun s =>
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ π : Equiv.Perm (Fin n), live π →
        (Equiv.Perm.sign π : ℝ) *
          ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < B (π j) j then (1 : ℝ) else -1) = ε)
  have hGood_eq : Finset.univ.filter (fun s : (Fin n × Fin n) → Bool =>
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ π : Equiv.Perm (Fin n), (∀ j, P (π j, j) ≠ 0) →
          (Equiv.Perm.sign π : ℝ) *
            ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < B (π j) j then (1 : ℝ) else -1) = ε) = Good := by
    ext s; simp [Good, live]
  rw [hGood_eq]
  have hH_live : ∀ π : Equiv.Perm (Fin n), (∀ j, H (π j) j ≠ 0) ↔ live π := by
    intro π; constructor <;> intro h j <;> have hj := h j <;> dsimp only [H] at *
    · by_contra hz; simp [hz] at hj
    · simp [hj]
  have hs0_const : ∃ ε0 : ℝ, (ε0 = 1 ∨ ε0 = -1) ∧
      ∀ π : Equiv.Perm (Fin n), live π →
        (Equiv.Perm.sign π : ℝ) * ∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1) = ε0 := by
    let Live : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter live
    have hH_abs : (fun i j => |H i j| : Matrix (Fin n) (Fin n) ℝ) = H := by
      ext i j; dsimp only [H]; split_ifs <;> simp
    conv_rhs at hs0 => rw [← hH_abs]
    rw [det_eq_sum_live, perm_abs_eq_sum_live] at hs0
    have hfilt : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => ∀ j, H (π j) j ≠ 0) = Live := by
      ext π; simp [Live, hH_live]
    rw [hfilt] at hs0
    have hdet_simp : ∑ π ∈ Live, (Equiv.Perm.sign π : ℝ) *
          ∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1) * H (π j) j =
        ∑ π ∈ Live, (Equiv.Perm.sign π : ℝ) * ∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1) := by
      refine Finset.sum_congr rfl (fun π hπ => ?_)
      congr 1
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have hlj := (Finset.mem_filter.mp hπ).2 j
      dsimp only [H]; simp [hlj]
    have hperm_simp : ∑ π ∈ Live, ∏ j : Fin n, |H (π j) j| = (Live.card : ℝ) := by
      have h1 : ∀ π ∈ Live, ∏ j : Fin n, |H (π j) j| = (1 : ℝ) := by
        intro π hπ
        refine Finset.prod_eq_one (fun j _ => ?_)
        have hlj := (Finset.mem_filter.mp hπ).2 j
        dsimp only [H]; simp [hlj]
      rw [Finset.sum_congr rfl h1]; simp
    rw [hdet_simp, hperm_simp] at hs0
    have hpm : ∀ π ∈ Live,
        (Equiv.Perm.sign π : ℝ) * ∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1) = 1 ∨
        (Equiv.Perm.sign π : ℝ) * ∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1) = -1 := by
      intro π _
      have hp : (∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1)) = 1 ∨
          (∏ j : Fin n, (if s0 (π j, j) then (-1 : ℝ) else 1)) = -1 := by
        have hsub : ∀ S : Finset (Fin n),
            (∏ j ∈ S, (if s0 (π j, j) then (-1 : ℝ) else 1)) = 1 ∨
            (∏ j ∈ S, (if s0 (π j, j) then (-1 : ℝ) else 1)) = -1 := by
          intro S
          induction S using Finset.induction_on with
          | empty => exact Or.inl (by simp)
          | insert a s ha ih =>
            rw [Finset.prod_insert ha]
            rcases ih with h | h <;> rw [h] <;> by_cases hs : s0 (π a, a) <;> simp [hs]
        exact hsub Finset.univ
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1 <;>
      rcases hp with h2 | h2 <;> rw [h1, h2] <;> norm_num
    rcases const_of_abs_sum_pm_one Live _ hpm hs0 with h1 | h1
    · exact ⟨1, Or.inl rfl, fun π hπ => h1 π (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ⟩)⟩
    · exact ⟨-1, Or.inr rfl, fun π hπ => h1 π (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ⟩)⟩
  rcases hs0_const with ⟨ε0, hε0, hs0_eq⟩
  let sBase : E → Bool := fun e => xor (s0 e) (decide (P e = 2))
  let toZ2 : (E → Bool) → (E → ZMod 2) := fun s e => if s e then 1 else 0
  let orthMap : (E → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := fun x z => ∑ e : E, z.1 e * x e
      map_add' := fun x1 x2 => by
        funext z; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext z
        change ∑ e : E, z.1 e * (c * x e) = c * ∑ e : E, z.1 e * x e
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by ring) }
  let orth : Submodule (ZMod 2) (E → ZMod 2) := LinearMap.ker orthMap
  have horth_dim : n ^ 2 ≤ r + Module.finrank (ZMod 2) orth := by
    have hdimE : Module.finrank (ZMod 2) (E → ZMod 2) = n ^ 2 := by
      rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin, sq]
    let dualMap : (E → ZMod 2) →ₗ[ZMod 2] (V →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun x =>
          { toFun := fun z => ∑ e : E, z.1 e * x e
            map_add' := fun z1 z2 => by
              change ∑ e : E, (z1.1 e + z2.1 e) * x e = _
              simp only [add_mul, Finset.sum_add_distrib]
            map_smul' := fun c z => by
              change ∑ e : E, (c * z.1 e) * x e = c * ∑ e : E, z.1 e * x e
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun e _ => by ring) }
        map_add' := fun x1 x2 => by
          ext z
          change ∑ e : E, z.1 e * (x1 e + x2 e) = (∑ e : E, z.1 e * x1 e) + ∑ e : E, z.1 e * x2 e
          simp only [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          ext z
          change ∑ e : E, z.1 e * (c * x e) = c * ∑ e : E, z.1 e * x e
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun e _ => by ring) }
    have hker_eq : LinearMap.ker dualMap = orth := by
      ext x
      simp only [LinearMap.mem_ker, orth]
      constructor
      · intro h; funext z; exact LinearMap.congr_fun h z
      · intro h; ext z; exact congrFun h z
    have hrange_le : Module.finrank (ZMod 2) (LinearMap.range dualMap) ≤ r := by
      have h1 : Module.finrank (ZMod 2) (LinearMap.range dualMap) ≤
          Module.finrank (ZMod 2) (V →ₗ[ZMod 2] ZMod 2) :=
        Submodule.finrank_le _
      have h2 : Module.finrank (ZMod 2) (V →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) V := by
        rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
      omega
    have hrn := LinearMap.finrank_range_add_finrank_ker dualMap
    rw [hdimE, hker_eq] at hrn
    omega
  have hGood_ge : Fintype.card orth ≤ Good.card := by
    let shift : orth → (E → Bool) := fun x e => xor (sBase e) (decide (x.1 e = 1))
    have hshift_inj : Function.Injective shift := by
      intro x1 x2 heq
      apply Subtype.ext
      funext e
      have he := congrFun heq e
      dsimp only [shift] at he
      rcases zmod2_val_eq_zero_or_one (x1.1 e) with h1 | h1 <;>
      rcases zmod2_val_eq_zero_or_one (x2.1 e) with h2 | h2 <;>
      cases hsb : sBase e <;> simp [h1, h2, hsb] at he ⊢
    have hshift_mem : ∀ x : orth, shift x ∈ Good := by
      intro x
      simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hexL : ∃ π0 : Equiv.Perm (Fin n), live π0
      · rcases hexL with ⟨π0, hπ0⟩
        let δ : ℝ := if (∑ e : E, vec π0 e * x.1 e) = 1 then -1 else 1
        refine ⟨ε0 * δ, ?_, ?_⟩
        · rcases hε0 with rfl | rfl <;> dsimp only [δ] <;> split_ifs <;> norm_num
        · intro π hπ
          have hpair_prod : ∀ j : Fin n,
              (if shift x (π j, j) then (-1 : ℝ) else 1) * (if 0 < B (π j) j then (1 : ℝ) else -1) =
              (if s0 (π j, j) then (-1 : ℝ) else 1) * (if x.1 (π j, j) = 1 then (-1 : ℝ) else 1) := by
            intro j
            have hlj := hπ j
            have hBsign : (if 0 < B (π j) j then (1 : ℝ) else -1) =
                if decide (P (π j, j) = 2) then -1 else 1 := by
              dsimp only [B]
              have h012 : P (π j, j) = 0 ∨ P (π j, j) = 1 ∨ P (π j, j) = 2 := by
                rcases P (π j, j) with ⟨v, hv⟩
                interval_cases v <;> simp
              rcases h012 with h0 | h1 | h2
              · exact absurd h0 hlj
              · simp [h1]
              · simp [h2]
            rw [hBsign]
            dsimp only [shift, sBase]
            by_cases hs0j : s0 (π j, j) = true <;>
            by_cases hP2 : P (π j, j) = 2 <;>
            rcases zmod2_val_eq_zero_or_one (x.1 (π j, j)) with hx | hx <;>
            simp [hs0j, hP2, hx]
          rw [Finset.prod_congr rfl (fun j _ => hpair_prod j), Finset.prod_mul_distrib,
            ← mul_assoc, hs0_eq π hπ]
          congr 1
          have hsum_vec : ∑ e : E, vec π e * x.1 e = ∑ j : Fin n, x.1 (π j, j) := by
            rw [Fintype.sum_prod_type_right]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_eq_single (π j)]
            · simp [vec]
            · intro i _ hne; simp [vec, Ne.symm hne]
            · intro hnu; exact absurd (Finset.mem_univ _) hnu
          have hsum_eq : ∑ e : E, vec π e * x.1 e = ∑ e : E, vec π0 e * x.1 e := by
            have hmemV : vec π - vec π0 ∈ V := Submodule.subset_span ⟨π, π0, hπ, hπ0, rfl⟩
            have h0 : ∑ e : E, (vec π - vec π0) e * x.1 e = 0 :=
              congrFun (LinearMap.mem_ker.mp x.2) ⟨vec π - vec π0, hmemV⟩
            have hsub : ∑ e : E, (vec π - vec π0) e * x.1 e =
                (∑ e : E, vec π e * x.1 e) - (∑ e : E, vec π0 e * x.1 e) := by
              simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
            rw [hsub] at h0
            exact sub_eq_zero.mp h0
          rw [← neg_one_zmod2_sum Finset.univ (fun j => x.1 (π j, j)), ← hsum_vec, hsum_eq]
      · push Not at hexL
        exact ⟨1, Or.inl rfl, fun π hπ => absurd hπ (hexL π)⟩
    calc Fintype.card orth
        = (Finset.univ : Finset orth).card := Finset.card_univ.symm
      _ ≤ Good.card := Finset.card_le_card_of_injOn shift (fun x _ => Finset.mem_coe.mpr (hshift_mem x))
          (fun x1 _ x2 _ h => hshift_inj h)
  have horth_card : Fintype.card orth = 2 ^ Module.finrank (ZMod 2) orth := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := orth)
    simpa [ZMod.card] using h
  calc 2 ^ (n ^ 2)
      ≤ 2 ^ (r + Module.finrank (ZMod 2) orth) := Nat.pow_le_pow_right (by omega) horth_dim
    _ = 2 ^ r * 2 ^ Module.finrank (ZMod 2) orth := pow_add 2 r _
    _ = 2 ^ r * Fintype.card orth := by rw [horth_card]
    _ ≤ 2 ^ r * Good.card := Nat.mul_le_mul_left _ hGood_ge

end PEqualNP.Outside.L_lib_996_aux

open PEqualNP.Outside.L_lib_996_aux

theorem PEqualNP.Outside.L_lib_996 :
    (∀ n r : ℕ,
  let I := Fin n
  let E := I × I
  let t := 2^r*(2*n^2+1)
  let D := fun (A : Matrix I I ℝ) (s : E → Bool) =>
    Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix I I ℝ)
  let vec := fun (π : Equiv.Perm I) (e : E) => if π e.2 = e.1 then (1 : ZMod 2) else 0
  ∃ signs : Fin t → E → Bool, ∀ A : Matrix I I ℝ,
    let H : Matrix I I ℝ := fun i j => if A i j = 0 then 0 else 1
    let live := fun π : Equiv.Perm I => ∀ j, A (π j) j ≠ 0
    let V := Submodule.span (ZMod 2) {z : E → ZMod 2 | ∃ π τ : Equiv.Perm I,
      live π ∧ live τ ∧ z = vec π - vec τ}
    ((Module.finrank (ZMod 2) V ≤ r ∧ ∃ s : E → Bool, |D H s| = H.permanent) ∨
      (n/2 ≤ r ∧
        (∀ i, ((Finset.univ : Finset I).filter (fun j => A i j ≠ 0)).card ≤ 2) ∧
        (∀ j, ((Finset.univ : Finset I).filter (fun i => A i j ≠ 0)).card ≤ 2))) →
    ∃ h : Fin t, |D A (signs h)| = Matrix.permanent (fun i j => |A i j|)) := by
  intro n r
  classical
  dsimp only
  let I := Fin n
  let E := I × I
  let t := 2 ^ r * (2 * n ^ 2 + 1)
  let D := fun (A : Matrix I I ℝ) (s : E → Bool) =>
    Matrix.det (fun i j => if s (i, j) then -A i j else A i j : Matrix I I ℝ)
  let vec := fun (π : Equiv.Perm I) (e : E) => if π e.2 = e.1 then (1 : ZMod 2) else 0
  let patH : (E → Fin 3) → Matrix I I ℝ := fun P i j => if P (i, j) = 0 then 0 else 1
  let patB : (E → Fin 3) → Matrix I I ℝ := fun P i j =>
    if P (i, j) = 0 then 0 else if P (i, j) = 1 then 1 else -1
  let patValid : (E → Fin 3) → Prop := fun P =>
    let H := patH P
    let live := fun π : Equiv.Perm I => ∀ j, P (π j, j) ≠ 0
    let V := Submodule.span (ZMod 2) {z : E → ZMod 2 | ∃ π τ : Equiv.Perm I,
      live π ∧ live τ ∧ z = vec π - vec τ}
    Module.finrank (ZMod 2) V ≤ r ∧ ∃ s : E → Bool, |D H s| = H.permanent
  let patGood : (E → Fin 3) → Finset (E → Bool) := fun P =>
    Finset.univ.filter (fun s =>
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ π : Equiv.Perm I, (∀ j, P (π j, j) ≠ 0) →
          (Equiv.Perm.sign π : ℝ) *
            ∏ j : I, (if s (π j, j) then (-1 : ℝ) else 1) * (if 0 < patB P (π j) j then (1 : ℝ) else -1) = ε)
  let patBadTuples : (E → Fin 3) → Finset (Fin t → E → Bool) := fun P =>
    Finset.univ.filter (fun signs => ∀ h : Fin t, signs h ∉ patGood P)
  let ValidPats : Finset (E → Fin 3) := Finset.univ.filter patValid
  let AllBad : Finset (Fin t → E → Bool) := ValidPats.biUnion patBadTuples
  have hE_card : Fintype.card (E → Bool) = 2 ^ (n ^ 2) := by
    simp [E, I, Fintype.card_pi, sq]
  have hBad_card : ∀ P ∈ ValidPats,
      (2 ^ r) ^ t * (patBadTuples P).card ≤ ((2 ^ r - 1) * 2 ^ (n ^ 2)) ^ t := by
    intro P hP
    have hval : patValid P := (Finset.mem_filter.mp hP).2
    have hge := card_align_ge P hval
    dsimp only at hge
    have hge' : 2 ^ (n ^ 2) ≤ 2 ^ r * (patGood P).card := by
      convert hge using 2
    let BadS : Finset (E → Bool) := Finset.univ \ patGood P
    have hBadS_eq : (patBadTuples P).card = BadS.card ^ t := by
      have hbij : (patBadTuples P).card = Fintype.card (Fin t → BadS) := by
        rw [← Finset.card_univ]
        apply Finset.card_bij (fun signs hsigns h => ⟨signs h, by
          simp only [patBadTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hsigns
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsigns h⟩⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro s1 _ s2 _ heq
          funext h
          exact congrArg Subtype.val (congrFun heq h)
        · intro f _
          refine ⟨fun h => (f h).1, ?_, by funext h; exact Subtype.ext rfl⟩
          simp only [patBadTuples, Finset.mem_filter, Finset.mem_univ, true_and]
          intro h
          exact (Finset.mem_sdiff.mp (f h).2).2
      rw [hbij, Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe]
    have hBadS_le : 2 ^ r * BadS.card ≤ (2 ^ r - 1) * 2 ^ (n ^ 2) := by
      have hsum : BadS.card + (patGood P).card = 2 ^ (n ^ 2) := by
        dsimp only [BadS]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, hE_card]
        have hle : (patGood P).card ≤ 2 ^ (n ^ 2) := by
          rw [← hE_card, ← Finset.card_univ]; exact Finset.card_le_univ _
        omega
      have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      have hmul : 2 ^ r * BadS.card + 2 ^ r * (patGood P).card = 2 ^ r * 2 ^ (n ^ 2) := by
        rw [← mul_add, hsum]
      have hsub : (2 ^ r - 1) * 2 ^ (n ^ 2) + 2 ^ (n ^ 2) = 2 ^ r * 2 ^ (n ^ 2) := by
        have h1 : (2 ^ r - 1) + 1 = 2 ^ r := by omega
        calc (2 ^ r - 1) * 2 ^ (n ^ 2) + 2 ^ (n ^ 2)
            = ((2 ^ r - 1) + 1) * 2 ^ (n ^ 2) := by ring
          _ = 2 ^ r * 2 ^ (n ^ 2) := by rw [h1]
      omega
    rw [hBadS_eq, ← mul_pow]
    exact Nat.pow_le_pow_left hBadS_le t
  have hAllBad_lt : AllBad.card < (Finset.univ : Finset (Fin t → E → Bool)).card := by
    have htot : (Finset.univ : Finset (Fin t → E → Bool)).card = (2 ^ (n ^ 2)) ^ t := by
      rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hE_card]
    have hValid_le : ValidPats.card ≤ 3 ^ (n ^ 2) := by
      calc ValidPats.card ≤ (Finset.univ : Finset (E → Fin 3)).card := Finset.card_le_univ _
        _ = 3 ^ (n ^ 2) := by simp [E, I, Fintype.card_pi, sq]
    have hmul_lt : (2 ^ r) ^ t * AllBad.card < (2 ^ r) ^ t * (2 ^ (n ^ 2)) ^ t := by
      calc (2 ^ r) ^ t * AllBad.card
          ≤ (2 ^ r) ^ t * ∑ P ∈ ValidPats, (patBadTuples P).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ P ∈ ValidPats, (2 ^ r) ^ t * (patBadTuples P).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _P ∈ ValidPats, ((2 ^ r - 1) * 2 ^ (n ^ 2)) ^ t := Finset.sum_le_sum hBad_card
        _ = ValidPats.card * ((2 ^ r - 1) * 2 ^ (n ^ 2)) ^ t := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 3 ^ (n ^ 2) * ((2 ^ r - 1) * 2 ^ (n ^ 2)) ^ t := Nat.mul_le_mul_right _ hValid_le
        _ = (3 ^ (n ^ 2) * (2 ^ r - 1) ^ t) * (2 ^ (n ^ 2)) ^ t := by rw [mul_pow, ← mul_assoc]
        _ < (2 ^ r) ^ t * (2 ^ (n ^ 2)) ^ t :=
            Nat.mul_lt_mul_of_pos_right (union_bound_strict n r) (pow_pos (Nat.two_pow_pos _) t)
    rw [htot]
    exact lt_of_mul_lt_mul_left hmul_lt (Nat.zero_le _)
  have hex_good : ∃ signs : Fin t → E → Bool, signs ∉ AllBad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin t → E → Bool)) ⊆ AllBad := fun x _ => hall x
    have hle := Finset.card_le_card hsub
    omega
  rcases hex_good with ⟨signs, hsigns⟩
  refine ⟨signs, ?_⟩
  intro A hcond
  let P : E → Fin 3 := fun e =>
    if A e.1 e.2 = 0 then 0 else if 0 < A e.1 e.2 then 1 else 2
  have hP_zero : ∀ i j : I, P (i, j) = 0 ↔ A i j = 0 := by
    intro i j
    dsimp only [P]
    by_cases h0 : A i j = 0
    · simp [h0]
    · by_cases hp : 0 < A i j <;> simp [h0, hp]
  have hP_pos : ∀ i j : I, A i j ≠ 0 → (0 < patB P i j ↔ 0 < A i j) := by
    intro i j h0
    dsimp only [patB, P]
    by_cases hp : 0 < A i j
    · simp [h0, hp]
    · simp [h0, hp]
  have hH_eq : patH P = (fun i j => if A i j = 0 then 0 else 1) := by
    ext i j
    dsimp only [patH]
    by_cases h0 : A i j = 0
    · simp [(hP_zero i j).mpr h0, h0]
    · simp [mt (hP_zero i j).mp h0, h0]
  have hV_eq : Submodule.span (ZMod 2) {z : E → ZMod 2 | ∃ π τ : Equiv.Perm I,
        (∀ j, P (π j, j) ≠ 0) ∧ (∀ j, P (τ j, j) ≠ 0) ∧ z = vec π - vec τ} =
      Submodule.span (ZMod 2) {z : E → ZMod 2 | ∃ π τ : Equiv.Perm I,
        (∀ j, A (π j) j ≠ 0) ∧ (∀ j, A (τ j) j ≠ 0) ∧ z = vec π - vec τ} := by
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq]
    exact exists_congr (fun π => exists_congr (fun τ =>
      and_congr (forall_congr' (fun j => not_congr (hP_zero (π j) j)))
        (and_congr (forall_congr' (fun j => not_congr (hP_zero (τ j) j))) Iff.rfl)))
  have hP_valid : patValid P := by
    dsimp only [patValid]
    rw [hV_eq, hH_eq]
    rcases hcond with h1 | ⟨hr2, hrow, hcol⟩
    · exact h1
    · have hd := deg2_implies_rank_and_align A hrow hcol
      dsimp only at hd
      exact ⟨le_trans hd.1 hr2, hd.2⟩
  have hnot_bad : signs ∉ patBadTuples P := by
    intro hb
    exact hsigns (Finset.mem_biUnion.mpr ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP_valid⟩, hb⟩)
  simp only [patBadTuples, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hnot_bad
  rcases hnot_bad with ⟨h, hh⟩
  simp only [patGood, Finset.mem_filter, Finset.mem_univ, true_and] at hh
  rcases hh with ⟨ε, hε, halign⟩
  refine ⟨h, align_implies_abs_det_eq_perm A (signs h) ε hε ?_⟩
  intro π hπ
  have hπP : ∀ j, P (π j, j) ≠ 0 := fun j => mt (hP_zero (π j) j).mp (hπ j)
  have hterm : ∀ j : I,
      (if signs h (π j, j) then (-1 : ℝ) else 1) * (if 0 < A (π j) j then (1 : ℝ) else -1) =
      (if signs h (π j, j) then (-1 : ℝ) else 1) * (if 0 < patB P (π j) j then (1 : ℝ) else -1) := by
    intro j
    congr 1
    by_cases hp : 0 < A (π j) j
    · simp [hp, (hP_pos (π j) j (hπ j)).mpr hp]
    · simp [hp, mt (hP_pos (π j) j (hπ j)).mp hp]
  rw [Finset.prod_congr rfl (fun j _ => hterm j)]
  exact halign π hπP
