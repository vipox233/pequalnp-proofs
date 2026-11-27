import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25733_aux

private def lblEquiv {n b : ℕ} (hn : 0 < n) : Fin n × Fin b ≃ Fin (n * b) where
  toFun p := ⟨p.1.val + p.2.val * n, by
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    nlinarith⟩
  invFun x :=
    (⟨x.val % n, Nat.mod_lt _ hn⟩,
     ⟨x.val / n, Nat.div_lt_of_lt_mul (by linarith [x.isLt, mul_comm n b])⟩)
  left_inv := by
    rintro ⟨⟨r, hr⟩, ⟨k, hk⟩⟩
    ext <;> dsimp only
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    · rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hr, zero_add]
  right_inv := by
    rintro ⟨x, hx⟩
    ext
    dsimp only
    rw [mul_comm]
    exact Nat.mod_add_div x n

private theorem prod_one_sub_le_three_eighths {n : ℕ} (p : Fin n → ℚ)
    (hp0 : ∀ r, 0 ≤ p r) (hp1 : ∀ r, p r ≤ 1) (hsum : ∑ r, p r = 1) :
    ∏ r : Fin n, (1 - p r) ≤ 3 / 8 := by
  let T : ℚ → ℚ := fun u => 1 + u + u ^ 2 / 2 + u ^ 3 / 6
  have hT_mul : ∀ x y : ℚ, 0 ≤ x → 0 ≤ y → T (x + y) ≤ T x * T y := by
    intro x y hx hy
    have hdiff : T x * T y - T (x + y) =
        x * y * (x ^ 2 / 6 + x * y / 4 + y ^ 2 / 6 + x ^ 2 * y / 12 + x * y ^ 2 / 12 + x ^ 2 * y ^ 2 / 36) := by
      dsimp only [T]
      ring
    have hnn : 0 ≤ x * y * (x ^ 2 / 6 + x * y / 4 + y ^ 2 / 6 + x ^ 2 * y / 12 + x * y ^ 2 / 12 + x ^ 2 * y ^ 2 / 36) := by
      positivity
    linarith
  have hT_prod : ∀ s : Finset (Fin n), T (∑ r ∈ s, p r) ≤ ∏ r ∈ s, T (p r) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp [T]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hs0 : 0 ≤ ∑ r ∈ s, p r := Finset.sum_nonneg (fun r _ => hp0 r)
      have hTa : 0 ≤ T (p a) := by
        dsimp only [T]
        have := hp0 a
        positivity
      exact (hT_mul (p a) (∑ r ∈ s, p r) (hp0 a) hs0).trans (mul_le_mul_of_nonneg_left ih hTa)
  have hprod_le_one : (∏ r : Fin n, (1 - p r)) * (∏ r : Fin n, T (p r)) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    have haux : ∀ s : Finset (Fin n), ∏ r ∈ s, (1 - p r) * T (p r) ≤ 1 := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        have ha0 : 0 ≤ (1 - p a) * T (p a) := by
          have h1 : 0 ≤ 1 - p a := sub_nonneg.mpr (hp1 a)
          have h2 : 0 ≤ T (p a) := by
            dsimp only [T]
            have := hp0 a
            positivity
          exact mul_nonneg h1 h2
        have ha1 : (1 - p a) * T (p a) ≤ 1 := by
          have hdiff : 1 - (1 - p a) * T (p a) = (p a) ^ 2 / 2 + (p a) ^ 3 / 3 + (p a) ^ 4 / 6 := by
            dsimp only [T]
            ring
          have hnn : 0 ≤ (p a) ^ 2 / 2 + (p a) ^ 3 / 3 + (p a) ^ 4 / 6 := by
            have := hp0 a
            positivity
          linarith
        nlinarith
    exact haux Finset.univ
  have h83 : (8 / 3 : ℚ) ≤ ∏ r : Fin n, T (p r) := by
    have h := hT_prod Finset.univ
    rw [hsum] at h
    dsimp only [T] at h
    linarith
  have hP0 : 0 ≤ ∏ r : Fin n, (1 - p r) := Finset.prod_nonneg (fun r _ => sub_nonneg.mpr (hp1 r))
  nlinarith

private theorem card_filter_add_card_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have h := Finset.sum_filter_add_sum_filter_not s p (fun _ => (1 : ℕ))
  simpa using h

private theorem card_fix_two {n b : ℕ} {r₁ r₂ : Fin n} (hr : r₁ ≠ r₂) (k₁ k₂ : Fin b) :
    b ^ 2 * (Finset.univ.filter (fun ω : Fin n → Fin b => ω r₁ = k₁ ∧ ω r₂ = k₂)).card = b ^ n := by
  let S : Fin n → Finset (Fin b) :=
    fun r => if r = r₁ then {k₁} else if r = r₂ then {k₂} else Finset.univ
  have heq : Finset.univ.filter (fun ω : Fin n → Fin b => ω r₁ = k₁ ∧ ω r₂ = k₂) =
      Fintype.piFinset S := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ r
      dsimp only [S]
      by_cases hr1 : r = r₁
      · subst hr1; simp [h1]
      · simp only [hr1, ite_false]
        by_cases hr2 : r = r₂
        · subst hr2; simp [h2]
        · simp [hr2]
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := h r₁
        dsimp only [S] at h1
        simpa using h1
      · have h2 := h r₂
        dsimp only [S] at h2
        have hne : r₂ ≠ r₁ := hr.symm
        simpa [hne] using h2
  rw [heq, Fintype.card_piFinset]
  have hb2 : b ^ 2 = ∏ r : Fin n, (if r = r₁ then b else if r = r₂ then b else 1) := by
    have hsplit : ∀ r : Fin n,
        (if r = r₁ then b else if r = r₂ then b else 1) =
          (if r = r₁ then b else 1) * (if r = r₂ then b else 1) := by
      intro r
      by_cases h1 : r = r₁
      · subst h1; simp [hr]
      · by_cases h2 : r = r₂
        · subst h2; simp [h1]
        · simp [h1, h2]
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp [sq]
  rw [hb2, ← Finset.prod_mul_distrib]
  have hterm : ∀ r : Fin n,
      (if r = r₁ then b else if r = r₂ then b else 1) * (S r).card = b := by
    intro r
    dsimp only [S]
    by_cases h1 : r = r₁
    · subst h1; simp
    · by_cases h2 : r = r₂
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp_rw [hterm]
  simp

private theorem solve_25733 (n b q : ℕ) (hn : 0 < n) (hb : 0 < b)
    (rowCap colCap : Fin q → ℕ)
    (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin (n * b))) (E : ℕ) :
    let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (π : Equiv.Perm (Fin s)) (E : ℕ) =>
      ∃ (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
        (out : Finset (Fin s) → (Fin q → Bool) → Bool),
        (∀ t, (R t).card ≤ rowCap t ∧ (C t).card ≤ colCap t) ∧
        ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
          out {z.1, z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
            Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E
    let typ := fun label : Fin (n * b) => (⟨label.val % n, Nat.mod_lt _ hn⟩ : Fin n)
    let h := (n + 1) / 2
    fits (n * b) (fun x y => G (typ x) (typ y)) π E →
    ∃ row col : Fin h ↪ Fin n,
      fits h (fun x y => G (row x) (col y)) (Equiv.refl _) (4 * E / b ^ 2) := by
  intro fits typ h hfit
  classical
  rcases hfit with ⟨rf, cf, R, C, out, hcap, hBad_card⟩
  let Bad : Finset (Fin (n * b) × Fin (n * b)) :=
    Finset.univ.filter (fun z =>
      out {z.1, z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
        Bool.xor (G (typ z.1) (typ (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))))
  have hBad_le : Bad.card ≤ E := hBad_card
  let lbl : Fin n × Fin b ≃ Fin (n * b) := lblEquiv hn
  have htyp_lbl : ∀ (r : Fin n) (k : Fin b), typ (lbl (r, k)) = r := by
    intro r k
    ext
    change (r.val + k.val * n) % n = r.val
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
  let Ω := Fin n → Fin b
  have hΩ_card : Fintype.card Ω = b ^ n := by
    simp [Ω]
  have hb_pos_q : (0 : ℚ) < (b : ℚ) := Nat.cast_pos.mpr hb
  have hbn_pos : 0 < b ^ n := pow_pos hb n
  have hbn_pos_q : (0 : ℚ) < ((b ^ n : ℕ) : ℚ) := Nat.cast_pos.mpr hbn_pos
  let Cimg : Ω → Finset (Fin n) := fun ω =>
    Finset.univ.image (fun r : Fin n => typ (π (lbl (r, ω r))))
  have hmiss_le : ∀ c : Fin n,
      ((Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω)).card : ℚ) / ((b ^ n : ℕ) : ℚ) ≤ 3 / 8 := by
    intro c
    let a : Fin n → ℕ := fun r =>
      (Finset.univ.filter (fun k : Fin b => typ (π (lbl (r, k))) = c)).card
    have ha_le : ∀ r : Fin n, a r ≤ b := by
      intro r
      calc a r ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_filter_le _ _
        _ = b := by simp
    have ha_sum : ∑ r : Fin n, a r = b := by
      calc ∑ r : Fin n, a r
          = ∑ r : Fin n, ∑ k : Fin b, if typ (π (lbl (r, k))) = c then 1 else 0 := by
            simp only [a, Finset.card_filter]
        _ = ∑ p : Fin n × Fin b, if typ (π (lbl p)) = c then 1 else 0 :=
            (Fintype.sum_prod_type (fun p : Fin n × Fin b => if typ (π (lbl p)) = c then 1 else 0)).symm
        _ = ∑ y : Fin (n * b), if typ y = c then 1 else 0 :=
            Equiv.sum_comp (lbl.trans π) (fun y => if typ y = c then 1 else 0)
        _ = ∑ p : Fin n × Fin b, if typ (lbl p) = c then 1 else 0 :=
            (Equiv.sum_comp lbl (fun y => if typ y = c then 1 else 0)).symm
        _ = ∑ r : Fin n, ∑ k : Fin b, if r = c then 1 else 0 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl; intro r _
            apply Finset.sum_congr rfl; intro k _
            rw [htyp_lbl r k]
        _ = b := by simp
    have hmiss_eq : (Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω)).card =
        ∏ r : Fin n, (b - a r) := by
      let S : Fin n → Finset (Fin b) := fun r =>
        Finset.univ.filter (fun k : Fin b => ¬ typ (π (lbl (r, k))) = c)
      have hf_eq : Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω) = Fintype.piFinset S := by
        ext ω
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        simp only [Finset.mem_univ, true_and, Cimg, Finset.mem_image, not_exists, S, Finset.mem_filter]
      rw [hf_eq, Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro r _
      dsimp only [S]
      have hpart := card_filter_add_card_not
        (Finset.univ : Finset (Fin b)) (fun k : Fin b => typ (π (lbl (r, k))) = c)
      simp only [Finset.card_univ, Fintype.card_fin] at hpart
      dsimp only [a]
      omega
    let p : Fin n → ℚ := fun r => (a r : ℚ) / (b : ℚ)
    have hfrac_eq : ((Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω)).card : ℚ) / ((b ^ n : ℕ) : ℚ) =
        ∏ r : Fin n, (1 - p r) := by
      rw [hmiss_eq, Nat.cast_prod, Nat.cast_pow]
      have hbn : (b : ℚ) ^ n = ∏ _r : Fin n, (b : ℚ) := by simp
      rw [hbn, ← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro r _
      rw [Nat.cast_sub (ha_le r), sub_div, div_self (ne_of_gt hb_pos_q)]
    rw [hfrac_eq]
    apply prod_one_sub_le_three_eighths p
    · intro r; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hb_pos_q)
    · intro r
      rw [div_le_one hb_pos_q]
      exact Nat.cast_le.mpr (ha_le r)
    · dsimp only [p]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum, ha_sum, ← div_eq_mul_inv]
      exact div_self (ne_of_gt hb_pos_q)
  have hexp_ge : (5 / 8 : ℚ) * (n : ℚ) ≤
      (∑ ω : Ω, ((Cimg ω).card : ℚ)) / ((b ^ n : ℕ) : ℚ) := by
    have hsum_comm : ∑ ω : Ω, (Cimg ω).card =
        ∑ c : Fin n, (Finset.univ.filter (fun ω : Ω => c ∈ Cimg ω)).card := by
      have h1 : ∀ ω : Ω, (Cimg ω).card = ∑ c : Fin n, if c ∈ Cimg ω then 1 else 0 := by
        intro ω
        rw [← Finset.card_filter]
        congr 1; ext c; simp
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.card_filter]
    have hsum_q : (∑ ω : Ω, ((Cimg ω).card : ℚ)) / ((b ^ n : ℕ) : ℚ) =
        ∑ c : Fin n, (1 - ((Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω)).card : ℚ) / ((b ^ n : ℕ) : ℚ)) := by
      rw [← Nat.cast_sum, hsum_comm, Nat.cast_sum]
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      have hpart := card_filter_add_card_not
        (Finset.univ : Finset Ω) (fun ω : Ω => c ∈ Cimg ω)
      rw [Finset.card_univ, hΩ_card] at hpart
      have hpart_q : ((Finset.univ.filter (fun ω : Ω => c ∈ Cimg ω)).card : ℚ) +
          ((Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω)).card : ℚ) = ((b ^ n : ℕ) : ℚ) := by
        exact_mod_cast hpart
      have hne : ((b ^ n : ℕ) : ℚ) ≠ 0 := ne_of_gt hbn_pos_q
      field_simp [hne]
      linarith
    rw [hsum_q]
    calc (5 / 8 : ℚ) * (n : ℚ)
        = ∑ _c : Fin n, (5 / 8 : ℚ) := by simp [mul_comm]
      _ ≤ ∑ c : Fin n, (1 - ((Finset.univ.filter (fun ω : Ω => c ∉ Cimg ω)).card : ℚ) / ((b ^ n : ℕ) : ℚ)) := by
          apply Finset.sum_le_sum
          intro c _
          linarith [hmiss_le c]
  let Good : Finset Ω := Finset.univ.filter (fun ω : Ω => h ≤ (Cimg ω).card)
  have hGood_lb : b ^ n < 4 * Good.card := by
    by_contra hle
    push Not at hle
    have hle_q : (4 : ℚ) * (Good.card : ℚ) ≤ ((b ^ n : ℕ) : ℚ) := by exact_mod_cast hle
    have hupper_nat : ∑ ω : Ω, (Cimg ω).card ≤ Good.card * n + (b ^ n - Good.card) * (h - 1) := by
      have hsplit : ∑ ω : Ω, (Cimg ω).card =
          (∑ ω ∈ Good, (Cimg ω).card) + (∑ ω ∈ Finset.univ.filter (fun ω : Ω => ¬ h ≤ (Cimg ω).card), (Cimg ω).card) := by
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω : Ω => h ≤ (Cimg ω).card) (fun ω => (Cimg ω).card)).symm
      rw [hsplit]
      have h1 : ∑ ω ∈ Good, (Cimg ω).card ≤ Good.card * n := by
        calc ∑ ω ∈ Good, (Cimg ω).card
            ≤ ∑ _ω ∈ Good, n := Finset.sum_le_sum (fun ω _ => (Finset.card_le_univ _).trans (by simp))
          _ = Good.card * n := by simp
      have h2 : ∑ ω ∈ Finset.univ.filter (fun ω : Ω => ¬ h ≤ (Cimg ω).card), (Cimg ω).card ≤
          (b ^ n - Good.card) * (h - 1) := by
        have hcard_not : (Finset.univ.filter (fun ω : Ω => ¬ h ≤ (Cimg ω).card)).card = b ^ n - Good.card := by
          have hpart := card_filter_add_card_not
            (Finset.univ : Finset Ω) (fun ω : Ω => h ≤ (Cimg ω).card)
          rw [Finset.card_univ, hΩ_card] at hpart
          dsimp only [Good]
          omega
        calc ∑ ω ∈ Finset.univ.filter (fun ω : Ω => ¬ h ≤ (Cimg ω).card), (Cimg ω).card
            ≤ ∑ _ω ∈ Finset.univ.filter (fun ω : Ω => ¬ h ≤ (Cimg ω).card), (h - 1) := by
              apply Finset.sum_le_sum
              intro ω hω
              have hlt : (Cimg ω).card < h := Nat.lt_of_not_le (Finset.mem_filter.mp hω).2
              omega
          _ = (b ^ n - Good.card) * (h - 1) := by
              rw [Finset.sum_const, smul_eq_mul, hcard_not]
      omega
    have hGood_le_bn : Good.card ≤ b ^ n := by
      calc Good.card ≤ (Finset.univ : Finset Ω).card := Finset.card_filter_le _ _
        _ = b ^ n := by rw [Finset.card_univ, hΩ_card]
    have hupper_q : (∑ ω : Ω, ((Cimg ω).card : ℚ)) ≤
        (Good.card : ℚ) * (n : ℚ) + (((b ^ n : ℕ) : ℚ) - (Good.card : ℚ)) * ((h - 1 : ℕ) : ℚ) := by
      have hcast : ((∑ ω : Ω, (Cimg ω).card : ℕ) : ℚ) ≤
          ((Good.card * n + (b ^ n - Good.card) * (h - 1) : ℕ) : ℚ) := Nat.cast_le.mpr hupper_nat
      rw [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hGood_le_bn] at hcast
      exact hcast
    have hh_le_n : h - 1 ≤ n := by dsimp only [h]; omega
    have h2h_le : 2 * (h - 1) ≤ n - 1 := by dsimp only [h]; omega
    have h2h_q : (2 : ℚ) * ((h - 1 : ℕ) : ℚ) ≤ (n : ℚ) - 1 := by
      have : ((2 * (h - 1) : ℕ) : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := Nat.cast_le.mpr h2h_le
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn] at this
      simpa using this
    have hh_le_q : ((h - 1 : ℕ) : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hh_le_n
    have hsum_lb : (5 / 8 : ℚ) * (n : ℚ) * ((b ^ n : ℕ) : ℚ) ≤ ∑ ω : Ω, ((Cimg ω).card : ℚ) := by
      rwa [le_div_iff₀ hbn_pos_q] at hexp_ge
    nlinarith
  have hGood_ne : Good.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at hGood_lb
    omega
  let offBad : Ω → ℕ := fun ω =>
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p =>
      p.1 ≠ p.2 ∧ (lbl (p.1, ω p.1), lbl (p.2, ω p.2)) ∈ Bad)).card
  have hsum_offBad : b ^ 2 * ∑ ω ∈ Good, offBad ω ≤ E * b ^ n := by
    have hle_all : ∑ ω ∈ Good, offBad ω ≤ ∑ ω : Ω, offBad ω :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    have hall : b ^ 2 * ∑ ω : Ω, offBad ω ≤ Bad.card * b ^ n := by
      have h1 : ∑ ω : Ω, offBad ω =
          ∑ r₁ : Fin n, ∑ r₂ : Fin n,
            if r₁ ≠ r₂ then
              ∑ ω : Ω, if (lbl (r₁, ω r₁), lbl (r₂, ω r₂)) ∈ Bad then 1 else 0
            else 0 := by
        have hstep : ∀ ω : Ω, offBad ω =
            ∑ r₁ : Fin n, ∑ r₂ : Fin n,
              if r₁ ≠ r₂ then
                if (lbl (r₁, ω r₁), lbl (r₂, ω r₂)) ∈ Bad then 1 else 0
              else 0 := by
          intro ω
          dsimp only [offBad]
          rw [Finset.card_filter, Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro r₁ _
          apply Finset.sum_congr rfl; intro r₂ _
          by_cases hne : r₁ ≠ r₂ <;> simp [hne]
        simp_rw [hstep]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro r₁ _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro r₂ _
        by_cases hne : r₁ ≠ r₂ <;> simp [hne]
      rw [h1, Finset.mul_sum]
      have hinner : ∀ r₁ r₂ : Fin n, r₁ ≠ r₂ →
          b ^ 2 * (∑ ω : Ω, if (lbl (r₁, ω r₁), lbl (r₂, ω r₂)) ∈ Bad then 1 else 0) =
            (∑ k₁ : Fin b, ∑ k₂ : Fin b, if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then 1 else 0) * b ^ n := by
        intro r₁ r₂ hr
        have hpart : ∑ ω : Ω, (if (lbl (r₁, ω r₁), lbl (r₂, ω r₂)) ∈ Bad then 1 else 0) =
            ∑ k₁ : Fin b, ∑ k₂ : Fin b,
              if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then
                (Finset.univ.filter (fun ω : Ω => ω r₁ = k₁ ∧ ω r₂ = k₂)).card
              else 0 := by
          have hfib : ∀ ω : Ω, (if (lbl (r₁, ω r₁), lbl (r₂, ω r₂)) ∈ Bad then 1 else 0) =
              ∑ k₁ : Fin b, ∑ k₂ : Fin b,
                if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then
                  if ω r₁ = k₁ ∧ ω r₂ = k₂ then 1 else 0
                else 0 := by
            intro ω
            rw [Finset.sum_eq_single (ω r₁)]
            · rw [Finset.sum_eq_single (ω r₂)]
              · simp
              · intro k₂ _ hk2; simp [hk2.symm]
              · intro hmem; exact absurd (Finset.mem_univ _) hmem
            · intro k₁ _ hk1
              apply Finset.sum_eq_zero; intro k₂ _
              simp [hk1.symm]
            · intro hmem; exact absurd (Finset.mem_univ _) hmem
          simp_rw [hfib]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k₁ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k₂ _
          by_cases hm : (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad
          · simp only [hm, ite_true, Finset.card_filter]
          · simp [hm]
        rw [hpart, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k₁ _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k₂ _
        by_cases hm : (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad
        · simp only [hm, ite_true, one_mul]
          exact card_fix_two hr k₁ k₂
        · simp [hm]
      calc ∑ r₁ : Fin n, b ^ 2 * ∑ r₂ : Fin n,
              (if r₁ ≠ r₂ then ∑ ω : Ω, if (lbl (r₁, ω r₁), lbl (r₂, ω r₂)) ∈ Bad then 1 else 0 else 0)
          = ∑ r₁ : Fin n, ∑ r₂ : Fin n,
              (if r₁ ≠ r₂ then
                (∑ k₁ : Fin b, ∑ k₂ : Fin b, if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then 1 else 0) * b ^ n
              else 0) := by
            apply Finset.sum_congr rfl; intro r₁ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro r₂ _
            split_ifs with hr
            · exact hinner r₁ r₂ hr
            · simp
        _ ≤ ∑ r₁ : Fin n, ∑ r₂ : Fin n,
              (∑ k₁ : Fin b, ∑ k₂ : Fin b, if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then 1 else 0) * b ^ n := by
            apply Finset.sum_le_sum; intro r₁ _
            apply Finset.sum_le_sum; intro r₂ _
            split_ifs
            · exact le_rfl
            · exact Nat.zero_le _
        _ = (∑ r₁ : Fin n, ∑ r₂ : Fin n, ∑ k₁ : Fin b, ∑ k₂ : Fin b,
              if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then 1 else 0) * b ^ n := by
            simp_rw [← Finset.sum_mul]
        _ = Bad.card * b ^ n := by
            congr 1
            have hswap : ∑ r₁ : Fin n, ∑ r₂ : Fin n, ∑ k₁ : Fin b, ∑ k₂ : Fin b,
                (if (lbl (r₁, k₁), lbl (r₂, k₂)) ∈ Bad then 1 else 0) =
                ∑ p₁ : Fin n × Fin b, ∑ p₂ : Fin n × Fin b,
                  if (lbl p₁, lbl p₂) ∈ Bad then 1 else 0 := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl; intro r₁ _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro k₁ _
              exact (Fintype.sum_prod_type (fun p₂ : Fin n × Fin b =>
                if (lbl (r₁, k₁), lbl p₂) ∈ Bad then 1 else 0)).symm
            rw [hswap]
            have h2 : ∑ p₁ : Fin n × Fin b, ∑ p₂ : Fin n × Fin b,
                (if (lbl p₁, lbl p₂) ∈ Bad then 1 else 0) =
                ∑ x : Fin (n * b), ∑ y : Fin (n * b), if (x, y) ∈ Bad then 1 else 0 := by
              have hinner2 : ∀ p₁ : Fin n × Fin b,
                  ∑ p₂ : Fin n × Fin b, (if (lbl p₁, lbl p₂) ∈ Bad then 1 else 0) =
                    ∑ y : Fin (n * b), if (lbl p₁, y) ∈ Bad then 1 else 0 :=
                fun p₁ => Equiv.sum_comp lbl (fun y => if (lbl p₁, y) ∈ Bad then 1 else 0)
              simp_rw [hinner2]
              exact Equiv.sum_comp lbl (fun x => ∑ y : Fin (n * b), if (x, y) ∈ Bad then 1 else 0)
            rw [h2, ← Fintype.sum_prod_type (fun z : Fin (n * b) × Fin (n * b) => if z ∈ Bad then 1 else 0),
              ← Finset.card_filter]
            congr 1; ext z; simp
    calc b ^ 2 * ∑ ω ∈ Good, offBad ω
        ≤ b ^ 2 * ∑ ω : Ω, offBad ω := Nat.mul_le_mul_left _ hle_all
      _ ≤ Bad.card * b ^ n := hall
      _ ≤ E * b ^ n := Nat.mul_le_mul_right _ hBad_le
  rcases Finset.exists_min_image Good offBad hGood_ne with ⟨ω₀, hω₀_mem, hω₀_min⟩
  have hoff_le : offBad ω₀ ≤ 4 * E / b ^ 2 := by
    have hmul_le : Good.card * offBad ω₀ ≤ ∑ ω ∈ Good, offBad ω := by
      calc Good.card * offBad ω₀
          = ∑ _ω ∈ Good, offBad ω₀ := by simp
        _ ≤ ∑ ω ∈ Good, offBad ω := Finset.sum_le_sum (fun ω hω => hω₀_min ω hω)
    have h4 : (4 * Good.card) * (b ^ 2 * offBad ω₀) ≤ (4 * Good.card) * (4 * E) := by
      calc (4 * Good.card) * (b ^ 2 * offBad ω₀)
          = 4 * (b ^ 2 * (Good.card * offBad ω₀)) := by ring
        _ ≤ 4 * (b ^ 2 * ∑ ω ∈ Good, offBad ω) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (b ^ 2) hmul_le)
        _ ≤ 4 * (E * b ^ n) := Nat.mul_le_mul_left 4 hsum_offBad
        _ = (4 * E) * b ^ n := by ring
        _ ≤ (4 * E) * (4 * Good.card) := Nat.mul_le_mul_left (4 * E) (le_of_lt hGood_lb)
        _ = (4 * Good.card) * (4 * E) := by ring
    have hpos4 : 0 < 4 * Good.card := by
      have : 0 < Good.card := Finset.card_pos.mpr hGood_ne
      omega
    have hle_mul : b ^ 2 * offBad ω₀ ≤ 4 * E := Nat.le_of_mul_le_mul_left h4 hpos4
    rw [Nat.le_div_iff_mul_le (pow_pos hb 2), mul_comm]
    exact hle_mul
  have hCimg_ge : h ≤ (Cimg ω₀).card := (Finset.mem_filter.mp hω₀_mem).2
  rcases Finset.exists_subset_card_eq hCimg_ge with ⟨S', hS'_sub, hS'_card⟩
  let e : Fin h ≃ ↥S' := (Fintype.equivFinOfCardEq (by simp [hS'_card])).symm
  let col : Fin h ↪ Fin n := ⟨fun i => (e i).val, fun i j hij => e.injective (Subtype.ext hij)⟩
  have hcol_mem : ∀ i : Fin h, ∃ r : Fin n, typ (π (lbl (r, ω₀ r))) = col i := by
    intro i
    have hm : col i ∈ Cimg ω₀ := hS'_sub (e i).property
    rcases Finset.mem_image.mp hm with ⟨r, _, hr⟩
    exact ⟨r, hr⟩
  let rowFn : Fin h → Fin n := fun i => Classical.choose (hcol_mem i)
  have hrowFn_spec : ∀ i : Fin h, typ (π (lbl (rowFn i, ω₀ (rowFn i)))) = col i :=
    fun i => Classical.choose_spec (hcol_mem i)
  have hrowFn_inj : Function.Injective rowFn := by
    intro i j hij
    apply col.injective
    rw [← hrowFn_spec i, ← hrowFn_spec j, hij]
  let row : Fin h ↪ Fin n := ⟨rowFn, hrowFn_inj⟩
  let f : Fin h ↪ Fin (n * b) :=
    ⟨fun i => lbl (row i, ω₀ (row i)), by
      intro i j hij
      have hty := congrArg typ hij
      rw [htyp_lbl, htyp_lbl] at hty
      exact row.injective hty⟩
  have hf_typ : ∀ i : Fin h, typ (f i) = row i := fun i => htyp_lbl (row i) (ω₀ (row i))
  have hf_col : ∀ j : Fin h, typ (π (f j)) = col j := fun j => hrowFn_spec j
  refine ⟨row, col, ?_⟩
  let rf' : Fin h → Bool := fun i => rf (f i)
  let cf' : Fin h → Bool := fun j => cf (π (f j))
  let R' : Fin q → Finset (Fin h) := fun t => Finset.univ.filter (fun i : Fin h => f i ∈ R t)
  let C' : Fin q → Finset (Fin h) := fun t => Finset.univ.filter (fun j : Fin h => π (f j) ∈ C t)
  let out' : Finset (Fin h) → (Fin q → Bool) → Bool := fun S v =>
    if h1 : ∃ i : Fin h, S = {i} then
      let i := Classical.choose h1
      Bool.xor (G (row i) (col i)) (Bool.xor (rf' i) (cf' i))
    else
      out (S.image f) v
  refine ⟨rf', cf', R', C', out', ?_, ?_⟩
  · intro t
    constructor
    · calc (R' t).card
          ≤ (R t).card := by
            apply Finset.card_le_card_of_injOn f
            · intro i hi; exact (Finset.mem_filter.mp hi).2
            · intro i _ j _ hij; exact f.injective hij
        _ ≤ rowCap t := (hcap t).1
    · calc (C' t).card
          ≤ (C t).card := by
            apply Finset.card_le_card_of_injOn (fun j => π (f j))
            · intro j hj; exact (Finset.mem_filter.mp hj).2
            · intro i _ j _ hij; exact f.injective (π.injective hij)
        _ ≤ colCap t := (hcap t).2
  · let Err' : Finset (Fin h × Fin h) :=
      Finset.univ.filter (fun z =>
        out' {z.1, z.2} (fun t => decide (z.1 ∈ R' t ∨ (Equiv.refl _) z.2 ∈ C' t)) ≠
          Bool.xor (G (row z.1) (col ((Equiv.refl _) z.2))) (Bool.xor (rf' z.1) (cf' ((Equiv.refl _) z.2))))
    have hErr'_le : Err'.card ≤ offBad ω₀ := by
      apply Finset.card_le_card_of_injOn (fun z : Fin h × Fin h => (row z.1, row z.2))
      · intro z hz
        have herr : out' {z.1, z.2} (fun t => decide (z.1 ∈ R' t ∨ z.2 ∈ C' t)) ≠
            Bool.xor (G (row z.1) (col z.2)) (Bool.xor (rf' z.1) (cf' z.2)) :=
          (Finset.mem_filter.mp hz).2
        have hne : z.1 ≠ z.2 := by
          intro heq
          apply herr
          have hs : ({z.1, z.2} : Finset (Fin h)) = {z.1} := by rw [heq, Finset.pair_eq_singleton]
          dsimp only [out']
          split_ifs with h1
          · have hch : Classical.choose h1 = z.1 :=
              (Finset.singleton_injective (hs.symm.trans (Classical.choose_spec h1))).symm
            rw [hch, heq]
          · exact absurd ⟨z.1, hs⟩ h1
        have hnot1 : ¬ ∃ i : Fin h, ({z.1, z.2} : Finset (Fin h)) = {i} := by
          rintro ⟨i, hi⟩
          have h1 : z.1 ∈ ({i} : Finset (Fin h)) := by rw [← hi]; simp
          have h2 : z.2 ∈ ({i} : Finset (Fin h)) := by rw [← hi]; simp
          simp only [Finset.mem_singleton] at h1 h2
          exact hne (h1.trans h2.symm)
        dsimp only [out'] at herr
        split_ifs at herr
        have him : ({z.1, z.2} : Finset (Fin h)).image f = {f z.1, f z.2} := by
          simp only [Finset.image_insert, Finset.image_singleton]
        have hvec : (fun t => decide (z.1 ∈ R' t ∨ z.2 ∈ C' t)) =
            (fun t => decide (f z.1 ∈ R t ∨ π (f z.2) ∈ C t)) := by
          funext t
          simp only [R', C', Finset.mem_filter, Finset.mem_univ, true_and]
        rw [him, hvec] at herr
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hrr => hne (row.injective hrr), ?_⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        dsimp only [rf', cf'] at herr
        change out {f z.1, f z.2} (fun t => decide (f z.1 ∈ R t ∨ π (f z.2) ∈ C t)) ≠
          Bool.xor (G (typ (f z.1)) (typ (π (f z.2)))) (Bool.xor (rf (f z.1)) (cf (π (f z.2))))
        rw [hf_typ z.1, hf_col z.2]
        exact herr
      · intro z₁ _ z₂ _ heq
        have h1 : z₁.1 = z₂.1 := row.injective (congrArg Prod.fst heq)
        have h2 : z₁.2 = z₂.2 := row.injective (congrArg Prod.snd heq)
        exact Prod.ext h1 h2
    exact hErr'_le.trans hoff_le

end PEqualNP.Outside.L_meta_25733_aux

theorem PEqualNP.Outside.L_meta_25733 :
∀ (n b q : ℕ) (hn : 0 < n), 0 < b →
  ∀ (rowCap colCap : Fin q → ℕ),
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (π : Equiv.Perm (Fin s)) (E : ℕ) =>
    ∃ (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      (∀ t, (R t).card ≤ rowCap t ∧ (C t).card ≤ colCap t) ∧
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E
  let typ := fun label : Fin (n*b) => (⟨label.val % n, Nat.mod_lt _ hn⟩ : Fin n)
  let h := (n+1)/2
  ∀ (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin (n*b))) (E : ℕ),
    fits (n*b) (fun x y => G (typ x) (typ y)) π E →
    ∃ row col : Fin h ↪ Fin n,
      fits h (fun x y => G (row x) (col y)) (Equiv.refl _) (4*E/b^2) := by
  intro n b q hn hb rowCap colCap fits typ h G π E hfit
  exact PEqualNP.Outside.L_meta_25733_aux.solve_25733 n b q hn hb rowCap colCap G π E hfit
