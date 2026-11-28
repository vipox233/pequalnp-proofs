import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_352

def gr {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.image (fun c => σ c u)

def Exp {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ r → 10 * S.card < (S.biUnion (gr σ)).card

def IsBad {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (L : ℕ) (u : Fin n) : Prop :=
  ∃ a : ℕ, a + 2 ≤ L ∧ ∃ (us vs : Fin (a + 2) ↪ Fin n), us 0 = u ∧
    ∀ i, vs i ∈ gr σ (us i) ∧ vs i ∈ gr σ (us (i + 1))

noncomputable def badSet {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (L : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun u => IsBad σ L u)

theorem mem_badSet {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (L : ℕ) (u : Fin n) :
    u ∈ badSet σ L ↔ IsBad σ L u := by
  classical
  simp [badSet]

theorem constr_step (n : ℕ) (R : Finset (Fin 16 × Fin n × Fin n)) (r : Fin 16 × Fin n × Fin n)
    (hr : r ∉ R) :
    (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
      ∀ r' ∈ insert r R, σ r'.1 r'.2.1 = r'.2.2)).card * (n - R.card) ≤
    (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
      ∀ r' ∈ R, σ r'.1 r'.2.1 = r'.2.2)).card := by
  classical
  obtain ⟨c, u, v⟩ := r
  set X : Finset (Fin n) := Finset.univ.filter (fun x => ∀ r' ∈ R, ¬ (r'.1 = c ∧ r'.2.1 = x)) with hX
  have hXc : n - R.card ≤ X.card := by
    have h1 : Xᶜ ⊆ R.image (fun r' => r'.2.1) := by
      intro x hx
      simp only [hX, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
        not_not] at hx
      obtain ⟨r', hr', -, h2⟩ := hx
      exact Finset.mem_image.mpr ⟨r', hr', h2⟩
    have h2 : Xᶜ.card ≤ R.card := (Finset.card_le_card h1).trans Finset.card_image_le
    have h3 : Xᶜ.card = n - X.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have h4 : X.card ≤ n := by
      simpa using Finset.card_le_univ X
    omega
  set B := Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
      ∀ r' ∈ insert (c, u, v) R, σ r'.1 r'.2.1 = r'.2.2) with hB
  set F := Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
      ∀ r' ∈ R, σ r'.1 r'.2.1 = r'.2.2) with hF
  by_cases huX : u ∈ X
  · have hinj : (X ×ˢ B).card ≤ F.card := by
      apply Finset.card_le_card_of_injOn
        (fun p : Fin n × (Fin 16 → Equiv.Perm (Fin n)) =>
          Function.update p.2 c (p.2 c * Equiv.swap u p.1))
      · rintro ⟨x, σ⟩ hp
        have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hp)
        obtain ⟨hx, hσ⟩ := hp'
        simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx huX
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hσ
        simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        intro r' hr'
        by_cases hc : r'.1 = c
        · have h1 : r'.2.1 ≠ x := fun h => hx r' hr' ⟨hc, h⟩
          have h2 : r'.2.1 ≠ u := fun h => huX r' hr' ⟨hc, h⟩
          rw [hc, Function.update_self]
          simp only [Equiv.Perm.mul_apply]
          rw [Equiv.swap_apply_of_ne_of_ne h2 h1, ← hc]
          exact hσ r' (Or.inr hr')
        · rw [Function.update_of_ne hc]
          exact hσ r' (Or.inr hr')
      · rintro ⟨x, σ⟩ hp ⟨x', σ'⟩ hp' heq
        have hp1 := Finset.mem_product.mp (Finset.mem_coe.mp hp)
        have hp2 := Finset.mem_product.mp (Finset.mem_coe.mp hp')
        have hσ := hp1.2
        have hσ' := hp2.2
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hσ hσ'
        have e1 : σ c u = v := hσ (c, u, v) (Or.inl rfl)
        have e2 : σ' c u = v := hσ' (c, u, v) (Or.inl rfl)
        simp only at heq
        have hc := congrFun heq c
        rw [Function.update_self, Function.update_self] at hc
        have hx : x = x' := by
          have h1 := congrArg (fun π : Equiv.Perm (Fin n) => π x) hc
          simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right] at h1
          rw [e1] at h1
          have h2 : σ' c u = σ' c (Equiv.swap u x' x) := by rw [e2]; exact h1
          have h3 := (σ' c).injective h2
          have h4 : Equiv.swap u x' u = Equiv.swap u x' (Equiv.swap u x' x) := by rw [← h3]
          rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h4
          exact h4.symm
        subst hx
        have hcc : σ c = σ' c := mul_right_cancel hc
        have : σ = σ' := by
          funext c'
          by_cases h : c' = c
          · rw [h]; exact hcc
          · have := congrFun heq c'
            rwa [Function.update_of_ne h, Function.update_of_ne h] at this
        rw [this]
    rw [Finset.card_product] at hinj
    calc B.card * (n - R.card) ≤ B.card * X.card := Nat.mul_le_mul_left _ hXc
      _ = X.card * B.card := Nat.mul_comm _ _
      _ ≤ F.card := hinj
  · have hBe : B = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro σ hσ
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hσ
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at huX
      obtain ⟨r', hr', h1, h2⟩ := huX
      have e1 : σ c u = v := hσ (c, u, v) (Or.inl rfl)
      have e2 := hσ r' (Or.inr hr')
      rw [h1, h2, e1] at e2
      apply hr
      have : r' = (c, u, v) := by
        obtain ⟨a, b, d⟩ := r'
        simp only at h1 h2 e2
        rw [h1, h2, ← e2]
      rw [← this]; exact hr'
    rw [hBe]; simp

theorem card_constr (n k : ℕ) (R : Finset (Fin 16 × Fin n × Fin n)) (hR : R.card ≤ k) :
    (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
      ∀ r ∈ R, σ r.1 r.2.1 = r.2.2)).card * (n - k) ^ R.card ≤ n.factorial ^ 16 := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    simp [Fintype.card_perm]
  | insert r R hr ih =>
    rw [Finset.card_insert_of_notMem hr] at hR ⊢
    have ih' := ih (by omega)
    have hs := constr_step n R r hr
    have h1 : n - k ≤ n - R.card := by omega
    calc _ = ((Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
          ∀ r' ∈ insert r R, σ r'.1 r'.2.1 = r'.2.2)).card * (n - k)) * (n - k) ^ R.card := by
            rw [pow_succ]; ring
      _ ≤ ((Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
          ∀ r' ∈ insert r R, σ r'.1 r'.2.1 = r'.2.2)).card * (n - R.card)) * (n - k) ^ R.card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ ≤ _ := (Nat.mul_le_mul_right _ hs).trans ih'

theorem fin_succ_ne (a : ℕ) (i : Fin (a + 2)) : i + 1 ≠ i := by
  intro h
  have h1 : (1 : Fin (a + 2)) = 0 := by simp at h
  have h2 := congrArg Fin.val h1
  simp at h2

def Valid {n : ℕ} (a : ℕ) (σ : Fin 16 → Equiv.Perm (Fin n))
    (w : (Fin (a + 2) → Fin n) × (Fin (a + 2) → Fin n) × (Fin (a + 2) → Fin 16) ×
      (Fin (a + 2) → Fin 16)) : Prop :=
  Function.Injective w.1 ∧ Function.Injective w.2.1 ∧
    ∀ i, σ (w.2.2.1 i) (w.1 i) = w.2.1 i ∧ σ (w.2.2.2 i) (w.1 (i + 1)) = w.2.1 i

theorem valid_count (n a : ℕ)
    (w : (Fin (a + 2) → Fin n) × (Fin (a + 2) → Fin n) × (Fin (a + 2) → Fin 16) ×
      (Fin (a + 2) → Fin 16)) (D : DecidablePred (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ w)) :
    (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ w)).card *
      (n - 2 * (a + 2)) ^ (2 * (a + 2)) ≤ n.factorial ^ 16 := by
  classical
  obtain ⟨us, vs, c, c'⟩ := w
  by_cases hinj : Function.Injective us ∧ Function.Injective vs
  · obtain ⟨hus, hvs⟩ := hinj
    set R : Finset (Fin 16 × Fin n × Fin n) :=
      Finset.univ.image (fun i => (c i, us i, vs i)) ∪
        Finset.univ.image (fun i => (c' i, us (i + 1), vs i)) with hR
    have hcard : R.card = 2 * (a + 2) := by
      rw [hR, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
        Finset.card_image_of_injective]
      · simp; omega
      · intro i j h
        simp only [Prod.mk.injEq] at h
        exact hvs h.2.2
      · intro i j h
        simp only [Prod.mk.injEq] at h
        exact hvs h.2.2
      · rw [Finset.disjoint_left]
        intro t h1 h2
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h1
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h2
        rw [← hj] at hi
        simp only [Prod.mk.injEq] at hi
        have hij : i = j := hvs hi.2.2
        subst hij
        exact fin_succ_ne a i (hus hi.2.1).symm
    have hsub : (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ (us, vs, c, c')))
        ⊆ (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) =>
          ∀ r ∈ R, σ r.1 r.2.1 = r.2.2)) := by
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      obtain ⟨-, -, h⟩ := hσ
      intro r hr
      rw [hR, Finset.mem_union] at hr
      rcases hr with hr | hr
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hr
        rw [← hi]; exact (h i).1
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hr
        rw [← hi]; exact (h i).2
    have := card_constr n (2 * (a + 2)) R (le_of_eq hcard)
    rw [hcard] at this
    exact (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans this
  · have : (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ (us, vs, c, c'))) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact hinj ⟨hσ.1, hσ.2.1⟩
    rw [this]; simp

theorem valid_total (n a : ℕ) (h : 8 * (a + 2) ≤ n) :
    ∀ D : ∀ σ : Fin 16 → Equiv.Perm (Fin n), DecidablePred (fun w => Valid a σ w),
    ∑ σ : Fin 16 → Equiv.Perm (Fin n), (Finset.univ.filter (fun w => Valid a σ w)).card ≤
      512 ^ (a + 2) * n.factorial ^ 16 := by
  classical
  intro D
  have hswap : ∑ σ : Fin 16 → Equiv.Perm (Fin n), (Finset.univ.filter (fun w => Valid a σ w)).card
      = ∑ w, (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ w)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  set k := a + 2 with hk
  set P := (n - 2 * k) ^ (2 * k) with hP
  have hPpos : 0 < P := by
    apply pow_pos; omega
  have h1 : (∑ w, (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ w)).card) * P
      ≤ (n ^ k * (n ^ k * (16 ^ k * 16 ^ k))) * n.factorial ^ 16 := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ _w : (Fin (a + 2) → Fin n) × (Fin (a + 2) → Fin n) × (Fin (a + 2) → Fin 16) ×
          (Fin (a + 2) → Fin 16), n.factorial ^ 16 := by
            apply Finset.sum_le_sum
            intro w _
            exact valid_count n a w _
      _ = _ := by
            rw [Finset.sum_const, Finset.card_univ]
            simp [Fintype.card_prod, hk]
  have h2 : n ^ k * n ^ k ≤ 2 ^ k * P := by
    have h3 : n ^ 2 ≤ 2 * (n - 2 * k) ^ 2 := by
      have h4 : 3 * n ≤ 4 * (n - 2 * k) := by omega
      have h5 : (3 * n) ^ 2 ≤ (4 * (n - 2 * k)) ^ 2 := Nat.pow_le_pow_left h4 2
      nlinarith
    calc n ^ k * n ^ k = (n ^ 2) ^ k := by ring
      _ ≤ (2 * (n - 2 * k) ^ 2) ^ k := Nat.pow_le_pow_left h3 k
      _ = 2 ^ k * P := by rw [hP]; ring
  have h6 : (∑ w, (Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => Valid a σ w)).card) * P
      ≤ (512 ^ k * n.factorial ^ 16) * P := by
    calc _ ≤ (n ^ k * (n ^ k * (16 ^ k * 16 ^ k))) * n.factorial ^ 16 := h1
      _ = (n ^ k * n ^ k) * ((16 ^ k * 16 ^ k) * n.factorial ^ 16) := by ring
      _ ≤ (2 ^ k * P) * ((16 ^ k * 16 ^ k) * n.factorial ^ 16) := Nat.mul_le_mul_right _ h2
      _ = _ := by
            have e : (512 : ℕ) ^ k = 2 ^ k * (16 ^ k * 16 ^ k) := by
              rw [← mul_pow, ← mul_pow]; norm_num
            rw [e]; ring
  exact Nat.le_of_mul_le_mul_right h6 hPpos

theorem badSet_le (n L : ℕ) (σ : Fin 16 → Equiv.Perm (Fin n))
    (D : ∀ a : ℕ, DecidablePred (fun w => Valid a σ w)) :
    (badSet σ L).card ≤ ∑ a ∈ Finset.range (L - 1), (Finset.univ.filter (fun w => Valid a σ w)).card := by
  classical
  have hsub : badSet σ L ⊆ (Finset.range (L - 1)).biUnion (fun a =>
      (Finset.univ.filter (fun w => Valid a σ w)).image (fun w => w.1 0)) := by
    intro u hu
    rw [mem_badSet] at hu
    obtain ⟨a, ha, us, vs, hu0, hcyc⟩ := hu
    have hc : ∀ i, ∃ c : Fin 16, σ c (us i) = vs i := by
      intro i
      have := (hcyc i).1
      simp only [gr, Finset.mem_image, Finset.mem_univ, true_and] at this
      exact this
    have hc' : ∀ i, ∃ c : Fin 16, σ c (us (i + 1)) = vs i := by
      intro i
      have := (hcyc i).2
      simp only [gr, Finset.mem_image, Finset.mem_univ, true_and] at this
      exact this
    choose c hc using hc
    choose c' hc' using hc'
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_image]
    refine ⟨(us, vs, c, c'), ?_, hu0⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨us.injective, vs.injective, fun i => ⟨hc i, hc' i⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun a _ => Finset.card_image_le)

theorem geom512 (m : ℕ) : ∑ a ∈ Finset.range m, 512 ^ (a + 2) ≤ 512 ^ (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : 512 ^ (m + 1 + 2) = 512 * 512 ^ (m + 2) := by ring
    omega

theorem bad_sum (n L : ℕ) (h : 8 * L ≤ n) :
    ∑ σ : Fin 16 → Equiv.Perm (Fin n), (badSet σ L).card ≤ n.factorial ^ 16 * 512 ^ (L + 1) := by
  classical
  calc _ ≤ ∑ σ : Fin 16 → Equiv.Perm (Fin n), ∑ a ∈ Finset.range (L - 1),
          (Finset.univ.filter (fun w => Valid a σ w)).card :=
        Finset.sum_le_sum (fun σ _ => badSet_le n L σ _)
    _ = ∑ a ∈ Finset.range (L - 1), ∑ σ : Fin 16 → Equiv.Perm (Fin n),
          (Finset.univ.filter (fun w => Valid a σ w)).card := Finset.sum_comm
    _ ≤ ∑ a ∈ Finset.range (L - 1), 512 ^ (a + 2) * n.factorial ^ 16 := by
        apply Finset.sum_le_sum
        intro a ha
        have := Finset.mem_range.mp ha
        exact valid_total n a (by omega) _
    _ = (∑ a ∈ Finset.range (L - 1), 512 ^ (a + 2)) * n.factorial ^ 16 := by
        rw [Finset.sum_mul]
    _ ≤ 512 ^ (L + 1) * n.factorial ^ 16 := by
        apply Nat.mul_le_mul_right
        cases L with
        | zero => simp
        | succ L => exact geom512 L
    _ = _ := Nat.mul_comm _ _

theorem pow_le_fact (s : ℕ) : s ^ s ≤ 3 ^ s * s.factorial := by
  induction s with
  | zero => simp
  | succ s ih =>
    have key : (s + 1) ^ s ≤ 3 * s ^ s := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · subst h0; simp
      · have hs : (0 : ℝ) < s := by exact_mod_cast hpos
        have h1 : (1 / (s : ℝ) + 1) ≤ Real.exp (1 / (s : ℝ)) := Real.add_one_le_exp _
        have h2 : (1 / (s : ℝ) + 1) ^ s ≤ Real.exp (1 / (s : ℝ)) ^ s :=
          pow_le_pow_left₀ (by positivity) h1 s
        have h3 : Real.exp (1 / (s : ℝ)) ^ s = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
        have h4 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have h5 : ((s : ℝ) + 1) ^ s = (1 / (s : ℝ) + 1) ^ s * (s : ℝ) ^ s := by
          rw [← mul_pow]
          congr 1
          field_simp
          ring
        have h6 : ((s : ℝ) + 1) ^ s ≤ 3 * (s : ℝ) ^ s := by
          rw [h5]
          have : (0 : ℝ) ≤ (s : ℝ) ^ s := by positivity
          nlinarith
        exact_mod_cast h6
    calc (s + 1) ^ (s + 1) = (s + 1) ^ s * (s + 1) := pow_succ _ _
      _ ≤ 3 * s ^ s * (s + 1) := Nat.mul_le_mul_right _ key
      _ ≤ 3 * (3 ^ s * s.factorial) * (s + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ih)
      _ = 3 ^ (s + 1) * (s + 1).factorial := by
          rw [Nat.factorial_succ, pow_succ]; ring

theorem choose_pow_le (n s : ℕ) : n.choose s * s ^ s ≤ 3 ^ s * n ^ s := by
  have h1 : s.factorial * n.choose s ≤ n ^ s := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n s
  calc n.choose s * s ^ s ≤ n.choose s * (3 ^ s * s.factorial) :=
        Nat.mul_le_mul_left _ (pow_le_fact s)
    _ = 3 ^ s * (s.factorial * n.choose s) := by ring
    _ ≤ 3 ^ s * n ^ s := Nat.mul_le_mul_left _ h1

theorem num_base (n s : ℕ) (h : s * 8192 ≤ n) :
    n ^ 11 * s ^ 5 * (10 ^ 6 * 64 * 3 ^ 11) ≤ (n - 16 * s) ^ 16 := by
  have hm : n ≤ 2 * (n - 16 * s) := by omega
  have h1 : n ^ 16 ≤ (2 * (n - 16 * s)) ^ 16 := Nat.pow_le_pow_left hm 16
  have h2 : (s * 8192) ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left h 5
  have h3 : n ^ 11 * (s * 8192) ^ 5 ≤ n ^ 11 * n ^ 5 := Nat.mul_le_mul_left _ h2
  have h4 : n ^ 11 * s ^ 5 * (10 ^ 6 * 64 * 3 ^ 11) * 2 ^ 16 ≤ n ^ 11 * (s * 8192) ^ 5 := by
    have : n ^ 11 * (s * 8192) ^ 5 = n ^ 11 * s ^ 5 * 8192 ^ 5 := by ring
    rw [this, mul_assoc]
    exact Nat.mul_le_mul_left _ (by norm_num)
  have h5 : n ^ 11 * s ^ 5 * (10 ^ 6 * 64 * 3 ^ 11) * 2 ^ 16 ≤ (n - 16 * s) ^ 16 * 2 ^ 16 := by
    calc _ ≤ n ^ 11 * (s * 8192) ^ 5 := h4
      _ ≤ n ^ 11 * n ^ 5 := h3
      _ = n ^ 16 := by ring
      _ ≤ (2 * (n - 16 * s)) ^ 16 := h1
      _ = (n - 16 * s) ^ 16 * 2 ^ 16 := by ring
  exact Nat.le_of_mul_le_mul_right h5 (by positivity)

theorem num_bound (n s : ℕ) (hs : 1 ≤ s) (h : s * 8192 ≤ n) :
    n.choose s * n.choose (10 * s) * (10 * s) ^ (16 * s) * 64 ^ s ≤ (n - 16 * s) ^ (16 * s) := by
  have hb := num_base n s h
  have hP : n ^ 11 * (10 * s) ^ 6 * 64 * 3 ^ 11 ≤ (n - 16 * s) ^ 16 * s := by
    calc n ^ 11 * (10 * s) ^ 6 * 64 * 3 ^ 11
        = n ^ 11 * s ^ 5 * (10 ^ 6 * 64 * 3 ^ 11) * s := by ring
      _ ≤ (n - 16 * s) ^ 16 * s := Nat.mul_le_mul_right _ hb
  have hPs := Nat.pow_le_pow_left hP s
  have hA := choose_pow_le n s
  have hB := choose_pow_le n (10 * s)
  have hpos : 0 < s ^ s * (10 * s) ^ (10 * s) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc n.choose s * n.choose (10 * s) * (10 * s) ^ (16 * s) * 64 ^ s * (s ^ s * (10 * s) ^ (10 * s))
      = (n.choose s * s ^ s) * (n.choose (10 * s) * (10 * s) ^ (10 * s)) *
          ((10 * s) ^ (16 * s) * 64 ^ s) := by ring
    _ ≤ (3 ^ s * n ^ s) * (3 ^ (10 * s) * n ^ (10 * s)) * ((10 * s) ^ (16 * s) * 64 ^ s) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hA hB)
    _ = (n ^ 11 * (10 * s) ^ 6 * 64 * 3 ^ 11) ^ s * (10 * s) ^ (10 * s) := by
        have e1 : (3 : ℕ) ^ (10 * s) = (3 ^ s) ^ 10 := by rw [mul_comm, pow_mul]
        have e2 : n ^ (10 * s) = (n ^ s) ^ 10 := by rw [mul_comm, pow_mul]
        have e3 : (10 * s) ^ (16 * s) = ((10 * s) ^ s) ^ 16 := by rw [mul_comm 16 s, pow_mul]
        have e4 : (10 * s) ^ (10 * s) = ((10 * s) ^ s) ^ 10 := pow_mul' (10 * s) 10 s
        have e5 : (n ^ 11 * (10 * s) ^ 6 * 64 * 3 ^ 11) ^ s =
            (n ^ s) ^ 11 * ((10 * s) ^ s) ^ 6 * 64 ^ s * (3 ^ s) ^ 11 := by
          rw [mul_pow, mul_pow, mul_pow, pow_right_comm n, pow_right_comm (10 * s),
            pow_right_comm 3]
        rw [e1, e2, e3, e4, e5]
        ring
    _ ≤ ((n - 16 * s) ^ 16 * s) ^ s * (10 * s) ^ (10 * s) := Nat.mul_le_mul_right _ hPs
    _ = (n - 16 * s) ^ (16 * s) * (s ^ s * (10 * s) ^ (10 * s)) := by
        have e6 : (n - 16 * s) ^ (16 * s) = ((n - 16 * s) ^ 16) ^ s := by rw [pow_mul]
        rw [e6, mul_pow]
        ring

theorem sub_count (n s : ℕ) (S T : Finset (Fin n)) (hS : S.card = s) (hT : T.card = 10 * s)
    (F : Finset (Fin 16 → Equiv.Perm (Fin n))) (hF : ∀ σ ∈ F, S.biUnion (gr σ) ⊆ T) :
    F.card * (n - 16 * s) ^ (16 * s) ≤ (10 * s) ^ (16 * s) * n.factorial ^ 16 := by
  classical
  set S' : Finset (Fin 16 × Fin n) := Finset.univ ×ˢ S with hS'
  have hS'card : S'.card = 16 * s := by
    rw [hS', Finset.card_product, Finset.card_univ, Fintype.card_fin, hS]
  set Rg : (S' → Fin n) → Finset (Fin 16 × Fin n × Fin n) :=
    fun g => Finset.univ.image (fun p : S' => (p.1.1, p.1.2, g p)) with hRg
  have hRcard : ∀ g, (Rg g).card = 16 * s := by
    intro g
    rw [hRg]
    simp only
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, Fintype.card_coe, hS'card]
    · intro p p' hpp
      simp only [Prod.mk.injEq] at hpp
      exact Subtype.ext (Prod.ext hpp.1 hpp.2.1)
  set Fg : (S' → Fin n) → Finset (Fin 16 → Equiv.Perm (Fin n)) :=
    fun g => Finset.univ.filter (fun σ => ∀ r ∈ Rg g, σ r.1 r.2.1 = r.2.2) with hFg
  set P : Finset (S' → Fin n) := Fintype.piFinset (fun _ => T) with hP
  have hPcard : P.card = (10 * s) ^ (16 * s) := by
    rw [hP, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
      hS'card, hT]
  have hsub : F ⊆ P.biUnion Fg := by
    intro σ hσ
    rw [Finset.mem_biUnion]
    refine ⟨fun p => σ p.1.1 p.1.2, ?_, ?_⟩
    · rw [hP, Fintype.mem_piFinset]
      intro p
      apply hF σ hσ
      rw [Finset.mem_biUnion]
      refine ⟨p.1.2, (Finset.mem_product.mp p.2).2, ?_⟩
      unfold gr
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · rw [hFg]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro r hr
      rw [hRg] at hr
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hr
      obtain ⟨p, rfl⟩ := hr
      rfl
  have h1 : F.card ≤ ∑ g ∈ P, (Fg g).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have h2 : ∀ g ∈ P, (Fg g).card * (n - 16 * s) ^ (16 * s) ≤ n.factorial ^ 16 := by
    intro g _
    have := card_constr n (16 * s) (Rg g) (le_of_eq (hRcard g))
    rw [hRcard g] at this
    exact this
  calc F.card * (n - 16 * s) ^ (16 * s)
      ≤ (∑ g ∈ P, (Fg g).card) * (n - 16 * s) ^ (16 * s) := Nat.mul_le_mul_right _ h1
    _ = ∑ g ∈ P, (Fg g).card * (n - 16 * s) ^ (16 * s) := Finset.sum_mul _ _ _
    _ ≤ ∑ _g ∈ P, n.factorial ^ 16 := Finset.sum_le_sum h2
    _ = (10 * s) ^ (16 * s) * n.factorial ^ 16 := by
        rw [Finset.sum_const, hPcard, smul_eq_mul]

theorem geom_sum_bound (N : ℕ) (c : ℕ → ℕ) (R : ℕ)
    (hc : ∀ s, 1 ≤ s → s ≤ R → c s * 64 ^ s ≤ N) (r : ℕ) (hrR : r ≤ R) :
    63 * (∑ s ∈ Finset.Icc 1 r, c s) * 64 ^ r + N ≤ N * 64 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := hc (r + 1) (by omega) hrR
    rw [pow_succ] at h1 ⊢
    generalize (∑ s ∈ Finset.Icc 1 r, c s) = X at ih ⊢
    generalize c (r + 1) = y at h1 ⊢
    generalize (64 : ℕ) ^ r = E at ih h1 ⊢
    nlinarith [ih, h1]

theorem nonexp_card (n : ℕ) (A : Finset (Fin 16 → Equiv.Perm (Fin n)))
    (hA : ∀ σ ∈ A, ¬ Exp σ (n / 8192)) : 4 * A.card ≤ n.factorial ^ 16 := by
  classical
  set N := n.factorial ^ 16 with hN
  set r := n / 8192 with hr
  set F : Finset (Fin n) → Finset (Fin n) → Finset (Fin 16 → Equiv.Perm (Fin n)) :=
    fun S T => A.filter (fun σ => S.biUnion (gr σ) ⊆ T) with hFdef
  set c : ℕ → ℕ := fun s =>
    ∑ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      ∑ T ∈ Finset.powersetCard (10 * s) (Finset.univ : Finset (Fin n)), (F S T).card with hc
  have hsub : A ⊆ (Finset.Icc 1 r).biUnion (fun s =>
      (Finset.powersetCard s (Finset.univ : Finset (Fin n))).biUnion (fun S =>
        (Finset.powersetCard (10 * s) (Finset.univ : Finset (Fin n))).biUnion (fun T => F S T))) := by
    intro σ hσ
    have hne := hA σ hσ
    unfold Exp at hne
    push Not at hne
    obtain ⟨S, hS1, hS2, hS3⟩ := hne
    have h10 : 10 * S.card ≤ Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      have : S.card * 8192 ≤ n := (Nat.le_div_iff_mul_le (by norm_num)).mp hS2
      omega
    obtain ⟨T, hT1, hT2⟩ := Finset.exists_superset_card_eq hS3 h10
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard, Finset.subset_univ,
      true_and]
    refine ⟨S.card, ⟨hS1, hS2⟩, S, rfl, T, hT2, ?_⟩
    rw [hFdef]
    simp only [Finset.mem_filter]
    exact ⟨hσ, hT1⟩
  have hcard : A.card ≤ ∑ s ∈ Finset.Icc 1 r, c s := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum (fun s _ => ?_)
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum (fun S _ => ?_)
    exact Finset.card_biUnion_le
  have hcs : ∀ s, 1 ≤ s → s ≤ r → c s * 64 ^ s ≤ N := by
    intro s hs1 hsr
    have hsn : s * 8192 ≤ n := (Nat.le_div_iff_mul_le (by norm_num)).mp hsr
    · have hnum := num_bound n s hs1 hsn
      have hmpos : 0 < (n - 16 * s) ^ (16 * s) := by
        have : 0 < n - 16 * s := by omega
        positivity
      apply Nat.le_of_mul_le_mul_right _ hmpos
      have hterm : ∀ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
          ∀ T ∈ Finset.powersetCard (10 * s) (Finset.univ : Finset (Fin n)),
          (F S T).card * (n - 16 * s) ^ (16 * s) ≤ (10 * s) ^ (16 * s) * N := by
        intro S hS T hT
        refine sub_count n s S T (Finset.mem_powersetCard.mp hS).2
          (Finset.mem_powersetCard.mp hT).2 (F S T) ?_
        intro σ hσ
        rw [hFdef] at hσ
        exact (Finset.mem_filter.mp hσ).2
      have hc1 : c s * (n - 16 * s) ^ (16 * s) ≤
          n.choose s * (n.choose (10 * s) * ((10 * s) ^ (16 * s) * N)) := by
        rw [hc]
        simp only
        rw [Finset.sum_mul]
        calc _ ≤ ∑ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
              n.choose (10 * s) * ((10 * s) ^ (16 * s) * N) := by
              refine Finset.sum_le_sum (fun S hS => ?_)
              rw [Finset.sum_mul]
              calc _ ≤ ∑ T ∈ Finset.powersetCard (10 * s) (Finset.univ : Finset (Fin n)),
                    (10 * s) ^ (16 * s) * N := Finset.sum_le_sum (fun T hT => hterm S hS T hT)
                _ = n.choose (10 * s) * ((10 * s) ^ (16 * s) * N) := by
                    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                      Fintype.card_fin, smul_eq_mul]
          _ = n.choose s * (n.choose (10 * s) * ((10 * s) ^ (16 * s) * N)) := by
              rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                Fintype.card_fin, smul_eq_mul]
      calc c s * 64 ^ s * (n - 16 * s) ^ (16 * s)
          = c s * (n - 16 * s) ^ (16 * s) * 64 ^ s := by ring
        _ ≤ n.choose s * (n.choose (10 * s) * ((10 * s) ^ (16 * s) * N)) * 64 ^ s :=
            Nat.mul_le_mul_right _ hc1
        _ = n.choose s * n.choose (10 * s) * (10 * s) ^ (16 * s) * 64 ^ s * N := by ring
        _ ≤ (n - 16 * s) ^ (16 * s) * N := Nat.mul_le_mul_right _ hnum
        _ = N * (n - 16 * s) ^ (16 * s) := by ring
  have hg := geom_sum_bound N c r hcs r le_rfl
  have hE : 0 < 64 ^ r := by positivity
  have h63 : 63 * (∑ s ∈ Finset.Icc 1 r, c s) * 64 ^ r ≤ N * 64 ^ r := by omega
  have h63' : 63 * (∑ s ∈ Finset.Icc 1 r, c s) ≤ N := Nat.le_of_mul_le_mul_right h63 hE
  omega

theorem greedyD {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (j : ℕ) (hj : 256 * j ≤ n) :
    ∃ D : Finset (Fin n), D.card = j ∧ ∀ u, (gr σ u ∩ D).card ≤ 1 := by
  induction j with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨D, hD, hDu⟩ := ih (by omega)
    set Bl : Finset (Fin n) :=
      D.biUnion (fun v => (Finset.univ.image (fun c => (σ c).symm v)).biUnion (gr σ)) with hBl
    have hcard : Bl.card ≤ D.card * 256 := by
      apply Finset.card_biUnion_le_card_mul
      intro v _
      have h1 : ((Finset.univ.image (fun c => (σ c).symm v)).biUnion (gr σ)).card
          ≤ (Finset.univ.image (fun c : Fin 16 => (σ c).symm v)).card * 16 := by
        apply Finset.card_biUnion_le_card_mul
        intro u _
        exact le_trans Finset.card_image_le (by simp)
      have h2 : (Finset.univ.image (fun c : Fin 16 => (σ c).symm v)).card ≤ 16 :=
        le_trans Finset.card_image_le (by simp)
      nlinarith
    have hlt : Bl.card < (Finset.univ : Finset (Fin n)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hblock : ∀ u, ∀ v' ∈ D, v' ∈ gr σ u → v ∈ gr σ u → False := by
      intro u v' hv' h1 h2
      apply hv
      rw [hBl, Finset.mem_biUnion]
      refine ⟨v', hv', ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨u, ?_, h2⟩
      simp only [gr, Finset.mem_image, Finset.mem_univ, true_and] at h1
      obtain ⟨c, hc⟩ := h1
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨c, by rw [← hc]; simp⟩
    have hvD : v ∉ D := by
      intro hvD
      refine hblock ((σ 0).symm v) v hvD ?_ ?_ <;>
        (simp only [gr, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨0, by simp⟩)
    refine ⟨insert v D, by rw [Finset.card_insert_of_notMem hvD, hD], ?_⟩
    intro u
    by_cases hvu : v ∈ gr σ u
    · have : gr σ u ∩ insert v D ⊆ {v} := by
        intro w hw
        rw [Finset.mem_inter, Finset.mem_insert] at hw
        rcases hw.2 with h | h
        · simp [h]
        · exact (hblock u w h hw.1 hvu).elim
      exact le_trans (Finset.card_le_card this) (by simp)
    · have : gr σ u ∩ insert v D ⊆ gr σ u ∩ D := by
        intro w hw
        rw [Finset.mem_inter, Finset.mem_insert] at hw
        rcases hw.2 with h | h
        · exact (hvu (h ▸ hw.1)).elim
        · exact Finset.mem_inter.mpr ⟨hw.1, h⟩
      exact le_trans (Finset.card_le_card this) (hDu u)

theorem uniq_count {n : ℕ} (G : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (hG : ∀ u ∈ S, (G u).card ≤ 16) :
    2 * (S.biUnion G).card ≤ 16 * S.card +
      (Finset.univ.filter (fun v => (S.filter (fun u => v ∈ G u)).card = 1)).card := by
  classical
  set N := S.biUnion G with hN
  have h1 : ∑ u ∈ S, (G u).card = ∑ v ∈ N, (S.filter (fun u => v ∈ G u)).card := by
    have : ∀ u ∈ S, (G u).card = ∑ v ∈ N, if v ∈ G u then 1 else 0 := by
      intro u hu
      rw [← Finset.card_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, hN, Finset.mem_biUnion]
      exact ⟨fun h => ⟨⟨u, hu, h⟩, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.card_filter]
  have h2 : ∑ u ∈ S, (G u).card ≤ 16 * S.card := by
    have := Finset.sum_le_card_nsmul S (fun u => (G u).card) 16 hG
    simpa [mul_comm] using this
  have h3 : (N.filter (fun v => (S.filter (fun u => v ∈ G u)).card = 1)).card ≤
      (Finset.univ.filter (fun v => (S.filter (fun u => v ∈ G u)).card = 1)).card :=
    Finset.card_le_card (fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.2)
  have h4 : 2 * N.card ≤ ∑ v ∈ N, (S.filter (fun u => v ∈ G u)).card +
      (N.filter (fun v => (S.filter (fun u => v ∈ G u)).card = 1)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have : 2 * N.card = ∑ _v ∈ N, 2 := by simp [mul_comm]
    rw [this]
    apply Finset.sum_le_sum
    intro v hv
    have hpos : 0 < (S.filter (fun u => v ∈ G u)).card := by
      rw [Finset.card_pos]
      rw [hN, Finset.mem_biUnion] at hv
      obtain ⟨u, hu, hvu⟩ := hv
      exact ⟨u, Finset.mem_filter.mpr ⟨hu, hvu⟩⟩
    split_ifs <;> omega
  omega

theorem expG {n : ℕ} (σ : Fin 16 → Equiv.Perm (Fin n)) (r : ℕ) (hexp : Exp σ r)
    (D : Finset (Fin n)) (hD : ∀ u, (gr σ u ∩ D).card ≤ 1) (S : Finset (Fin n))
    (hS : S.card ≤ r) :
    2 * S.card ≤ (Finset.univ.filter
      (fun v => (S.filter (fun u => v ∈ gr σ u \ D)).card = 1)).card := by
  classical
  by_cases h0 : S.card = 0
  · simp [h0]
  have h10 := hexp S (by omega) hS
  have hc := uniq_count (gr σ) S (fun u _ => le_trans Finset.card_image_le (by simp))
  set U := Finset.univ.filter (fun v => (S.filter (fun u => v ∈ gr σ u)).card = 1) with hU
  set U₁ := Finset.univ.filter (fun v => (S.filter (fun u => v ∈ gr σ u \ D)).card = 1) with hU₁
  have hsub : U \ D ⊆ U₁ := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    simp only [hU, hU₁, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have hfe : S.filter (fun u => v ∈ gr σ u \ D) = S.filter (fun u => v ∈ gr σ u) := by
      ext u
      simp [hv.2]
    rw [hfe]
    exact hv.1
  have hint : (U ∩ D).card ≤ S.card * 1 := by
    have : U ∩ D ⊆ S.biUnion (fun u => gr σ u ∩ D) := by
      intro v hv
      rw [Finset.mem_inter] at hv
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hpos : 0 < (S.filter (fun u => v ∈ gr σ u)).card := by omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_biUnion]
      exact ⟨u, hu.1, Finset.mem_inter.mpr ⟨hu.2, hv.2⟩⟩
    exact le_trans (Finset.card_le_card this)
      (Finset.card_biUnion_le_card_mul _ _ _ (fun u _ => hD u))
  have h5 := Finset.card_sdiff_add_card_inter U D
  have h6 := Finset.card_le_card hsub
  omega

theorem exists_min_def {n : ℕ} (G : Fin n → Finset (Fin n)) (P : Finset (Fin n))
    (hP : (P.biUnion G).card < P.card) :
    ∃ T, T ⊆ P ∧ (T.biUnion G).card < T.card ∧
      ∀ S, S ⊆ T → S ≠ T → S.card ≤ (S.biUnion G).card := by
  induction P using Finset.strongInduction with
  | H P ih =>
    by_cases h : ∀ S, S ⊆ P → S ≠ P → S.card ≤ (S.biUnion G).card
    · exact ⟨P, subset_rfl, hP, h⟩
    · push Not at h
      obtain ⟨S, hS, hne, hlt⟩ := h
      obtain ⟨T, hT, h1, h2⟩ := ih S (Finset.ssubset_iff_subset_ne.mpr ⟨hS, hne⟩) hlt
      exact ⟨T, hT.trans hS, h1, h2⟩

theorem min_card {n : ℕ} (G : Fin n → Finset (Fin n)) (T : Finset (Fin n))
    (hdef : (T.biUnion G).card < T.card)
    (hmin : ∀ S, S ⊆ T → S ≠ T → S.card ≤ (S.biUnion G).card) :
    T.card = (T.biUnion G).card + 1 := by
  have hpos : 0 < T.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have h1 := hmin (T.erase u) (Finset.erase_subset _ _)
    (fun h => by have := Finset.notMem_erase u T; rw [h] at this; exact this hu)
  have h2 : ((T.erase u).biUnion G).card ≤ (T.biUnion G).card :=
    Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset _ _))
  rw [Finset.card_erase_of_mem hu] at h1
  omega

theorem min_deg {n : ℕ} (G : Fin n → Finset (Fin n)) (T : Finset (Fin n))
    (hdef : (T.biUnion G).card < T.card)
    (hmin : ∀ S, S ⊆ T → S ≠ T → S.card ≤ (S.biUnion G).card)
    (v : Fin n) (hv : v ∈ T.biUnion G) : 2 ≤ (T.filter (fun u => v ∈ G u)).card := by
  by_contra hlt
  have hcard := min_card G T hdef hmin
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hv
  have h1 := hmin (T.erase u) (Finset.erase_subset _ _)
    (fun h => by have := Finset.notMem_erase u T; rw [h] at this; exact this hu)
  have hsub : (T.erase u).biUnion G ⊆ (T.biUnion G).erase v := by
    intro w hw
    obtain ⟨u', hu', hw'⟩ := Finset.mem_biUnion.mp hw
    rw [Finset.mem_erase] at hu' ⊢
    refine ⟨?_, Finset.mem_biUnion.mpr ⟨u', hu'.2, hw'⟩⟩
    rintro rfl
    apply hu'.1
    have hle : (T.filter (fun u => w ∈ G u)).card ≤ 1 := by omega
    exact Finset.card_le_one.mp hle u' (Finset.mem_filter.mpr ⟨hu'.2, hw'⟩) u
      (Finset.mem_filter.mpr ⟨hu, hvu⟩)
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at h2
  rw [Finset.card_erase_of_mem hu] at h1
  have h3 : 0 < (T.biUnion G).card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

theorem min_conn {n : ℕ} (G : Fin n → Finset (Fin n)) (T : Finset (Fin n))
    (hdef : (T.biUnion G).card < T.card)
    (hmin : ∀ S, S ⊆ T → S ≠ T → S.card ≤ (S.biUnion G).card)
    (fL fR : Fin n → Bool) (hf : ∀ u ∈ T, ∀ v ∈ G u, fL u = fR v)
    (u : Fin n) (hu : u ∈ T) (u' : Fin n) (hu' : u' ∈ T) : fL u = fL u' := by
  by_contra hne
  set T1 := T.filter (fun x => fL x = fL u) with hT1
  set T2 := T.filter (fun x => ¬ fL x = fL u) with hT2
  have h1 := hmin T1 (Finset.filter_subset _ _) (fun h => by
    have : u' ∈ T1 := h ▸ hu'
    exact hne (Finset.mem_filter.mp this).2.symm)
  have h2 := hmin T2 (Finset.filter_subset _ _) (fun h => by
    have : u ∈ T2 := h ▸ hu
    exact (Finset.mem_filter.mp this).2 rfl)
  have hadd : T1.card + T2.card = T.card := Finset.card_filter_add_card_filter_not _
  have hdisj : Disjoint (T1.biUnion G) (T2.biUnion G) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hv1
    obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hv2
    rw [Finset.mem_filter] at ha hb
    apply hb.2
    rw [hf b hb.1 v hvb, ← hf a ha.1 v hva, ha.2]
  have hsub : T1.biUnion G ∪ T2.biUnion G ⊆ T.biUnion G :=
    Finset.union_subset
      (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
      (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h3
  omega

theorem surgery (n r L m : ℕ) (σ : Fin 16 → Equiv.Perm (Fin n)) (hr : 1 ≤ r) (hexp : Exp σ r)
    (hB : (badSet σ L).card ≤ m) (hm : 256 * (m + 1) ≤ n) :
    ∃ (G₁ : Fin n → Finset (Fin n)) (T : Finset (Fin n)) (q : ℕ),
      T.card = q + 1 ∧ (T.biUnion G₁).card = q ∧ r ≤ q ∧
      (∀ S, S ⊆ T → S.card ≤ r → 2 * S.card ≤
        (Finset.univ.filter (fun v => (S.filter (fun u => v ∈ G₁ u)).card = 1)).card) ∧
      (∀ u ∈ T, 2 ≤ (G₁ u).card ∧ (G₁ u).card ≤ 16) ∧
      (∀ v ∈ T.biUnion G₁, 2 ≤ (T.filter (fun u => v ∈ G₁ u)).card ∧
        (T.filter (fun u => v ∈ G₁ u)).card ≤ 16) ∧
      (∀ S, S ⊆ T → S ≠ T → S.card ≤ (S.biUnion G₁).card) ∧
      (∀ (fL fR : Fin n → Bool), (∀ u ∈ T, ∀ v ∈ G₁ u, fL u = fR v) →
        ∀ u ∈ T, ∀ u' ∈ T, fL u = fL u') ∧
      (∀ (a : ℕ) (us vs : Fin (a + 2) ↪ Fin n), (∀ i, us i ∈ T) →
        (∀ i, vs i ∈ G₁ (us i) ∧ vs i ∈ G₁ (us (i + 1))) → L < a + 2) := by
  classical
  have hBn : (badSet σ L).card + 1 ≤ n := by omega
  obtain ⟨D, hDc, hD⟩ := greedyD σ ((badSet σ L).card + 1) (by omega)
  set G₁ : Fin n → Finset (Fin n) := fun u => gr σ u \ D with hG₁
  set P : Finset (Fin n) := Finset.univ \ badSet σ L with hP
  have hexpG : ∀ S : Finset (Fin n), S.card ≤ r → 2 * S.card ≤
      (Finset.univ.filter (fun v => (S.filter (fun u => v ∈ G₁ u)).card = 1)).card :=
    fun S hS => expG σ r hexp D hD S hS
  have hPc : P.card = n - (badSet σ L).card := by
    rw [hP, Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  have hNP : (P.biUnion G₁).card ≤ n - D.card := by
    have : P.biUnion G₁ ⊆ Finset.univ \ D := by
      intro v hv
      obtain ⟨u, _, hvu⟩ := Finset.mem_biUnion.mp hv
      rw [Finset.mem_sdiff] at hvu ⊢
      exact ⟨Finset.mem_univ _, hvu.2⟩
    have h := Finset.card_le_card this
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)] at h
    simpa using h
  obtain ⟨T, hTP, hdef, hmin⟩ := exists_min_def G₁ P (by omega)
  have hcard := min_card G₁ T hdef hmin
  have huniq_sub : ∀ S : Finset (Fin n),
      (Finset.univ.filter (fun v => (S.filter (fun u => v ∈ G₁ u)).card = 1)) ⊆ S.biUnion G₁ := by
    intro S v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hpos : 0 < (S.filter (fun u => v ∈ G₁ u)).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hu
    exact Finset.mem_biUnion.mpr ⟨u, hu.1, hu.2⟩
  have hTr : r < T.card := by
    by_contra hle
    have h1 := hexpG T (by omega)
    have h2 := Finset.card_le_card (huniq_sub T)
    omega
  refine ⟨G₁, T, (T.biUnion G₁).card, hcard, rfl, by omega, fun S _ hS => hexpG S hS,
    ?_, ?_, hmin, ?_, ?_⟩
  · intro u _
    constructor
    · have h1 := hexpG {u} (by simp; omega)
      have h2 := Finset.card_le_card (huniq_sub {u})
      simp only [Finset.card_singleton, Finset.singleton_biUnion] at h1 h2
      omega
    · exact le_trans (Finset.card_le_card Finset.sdiff_subset)
        (le_trans Finset.card_image_le (by simp))
  · intro v hv
    refine ⟨min_deg G₁ T hdef hmin v hv, ?_⟩
    have : T.filter (fun u => v ∈ G₁ u) ⊆ Finset.univ.image (fun c : Fin 16 => (σ c).symm v) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      have h := (Finset.mem_sdiff.mp hu.2).1
      simp only [gr, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢
      obtain ⟨c, hc⟩ := h
      exact ⟨c, by rw [← hc]; simp⟩
    exact le_trans (Finset.card_le_card this) (le_trans Finset.card_image_le (by simp))
  · intro fL fR hf u hu u' hu'
    exact min_conn G₁ T hdef hmin fL fR hf u hu u' hu'
  · intro a us vs hus hcyc
    by_contra hlt
    have hbad : us 0 ∈ badSet σ L := by
      rw [mem_badSet]
      exact ⟨a, by omega, us, vs, rfl, fun i =>
        ⟨(Finset.mem_sdiff.mp (hcyc i).1).1, (Finset.mem_sdiff.mp (hcyc i).2).1⟩⟩
    have := hTP (hus 0)
    rw [hP, Finset.mem_sdiff] at this
    exact this.2 hbad

theorem card_univ_perms (n : ℕ) :
    (Finset.univ : Finset (Fin 16 → Equiv.Perm (Fin n))).card = n.factorial ^ 16 := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp [Fintype.card_perm]

theorem select (n L : ℕ) (h : 8 * L ≤ n) :
    ∃ σ : Fin 16 → Equiv.Perm (Fin n), Exp σ (n / 8192) ∧
      (badSet σ L).card ≤ 2 * 512 ^ (L + 1) := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set M := 512 ^ (L + 1) with hM
  set N := n.factorial ^ 16 with hN
  have hNpos : 0 < N := pow_pos (Nat.factorial_pos n) 16
  set A := Finset.univ.filter (fun σ : Fin 16 → Equiv.Perm (Fin n) => ¬ Exp σ (n / 8192)) with hA
  have h4 : 4 * A.card ≤ N := nonexp_card n A (fun σ hσ => (Finset.mem_filter.mp hσ).2)
  have hsum := bad_sum n L h
  have hcompl : A.card + Aᶜ.card = N := by
    rw [Finset.card_add_card_compl, hN, ← card_univ_perms n, Finset.card_univ]
  have hlow : Aᶜ.card * (2 * M + 1) ≤ ∑ σ : Fin 16 → Equiv.Perm (Fin n), (badSet σ L).card := by
    calc Aᶜ.card * (2 * M + 1) = ∑ _σ ∈ Aᶜ, (2 * M + 1) := by simp
      _ ≤ ∑ σ ∈ Aᶜ, (badSet σ L).card := by
        apply Finset.sum_le_sum
        intro σ hσ
        have : Exp σ (n / 8192) := by
          have := Finset.mem_compl.mp hσ
          simpa [hA] using this
        exact hcon σ this
      _ ≤ ∑ σ : Fin 16 → Equiv.Perm (Fin n), (badSet σ L).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hfin : Aᶜ.card * (2 * M + 1) ≤ N * M := le_trans hlow hsum
  have h3 : 3 * N ≤ 4 * Aᶜ.card := by omega
  nlinarith

theorem transfer (n r L q : ℕ) (G₁ : Fin n → Finset (Fin n)) (T : Finset (Fin n))
    (hT : T.card = q + 1) (hNT : (T.biUnion G₁).card = q)
    (h1 : ∀ S, S ⊆ T → S.card ≤ r → 2 * S.card ≤
        (Finset.univ.filter (fun v => (S.filter (fun u => v ∈ G₁ u)).card = 1)).card)
    (h2 : ∀ u ∈ T, 2 ≤ (G₁ u).card ∧ (G₁ u).card ≤ 16)
    (h3 : ∀ v ∈ T.biUnion G₁, 2 ≤ (T.filter (fun u => v ∈ G₁ u)).card ∧
        (T.filter (fun u => v ∈ G₁ u)).card ≤ 16)
    (h4 : ∀ S, S ⊆ T → S ≠ T → S.card ≤ (S.biUnion G₁).card)
    (h5 : ∀ (fL fR : Fin n → Bool), (∀ u ∈ T, ∀ v ∈ G₁ u, fL u = fR v) →
        ∀ u ∈ T, ∀ u' ∈ T, fL u = fL u')
    (h6 : ∀ (a : ℕ) (us vs : Fin (a + 2) ↪ Fin n), (∀ i, us i ∈ T) →
        (∀ i, vs i ∈ G₁ (us i) ∧ vs i ∈ G₁ (us (i + 1))) → L < a + 2) :
    ∃ G : PEqualNP.Expanders.BipGraph (q + 1) q,
      PEqualNP.Expanders.IsBdryExpander G r 2 ∧
      (∀ u, 2 ≤ (G u).card ∧ (G u).card ≤ 16) ∧
      (∀ v, 2 ≤ (PEqualNP.Expanders.rightNbrs G v).card ∧
        (PEqualNP.Expanders.rightNbrs G v).card ≤ 16) ∧
      (∀ S : Finset (Fin (q + 1)), S ≠ Finset.univ → S.card ≤ (S.biUnion G).card) ∧
      (∀ f : Fin (q + 1) ⊕ Fin q → Bool,
        (∀ u, ∀ v ∈ G u, f (Sum.inl u) = f (Sum.inr v)) → ∀ x y, f x = f y) ∧
      ∀ (a : ℕ) (us : Fin (a + 2) ↪ Fin (q + 1)) (vs : Fin (a + 2) ↪ Fin q),
        (∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i + 1))) → L < a + 2 := by
  classical
  let eL : Fin (q + 1) ≃ T := (T.equivFinOfCardEq hT).symm
  let eR : Fin q ≃ (T.biUnion G₁ : Finset (Fin n)) := ((T.biUnion G₁).equivFinOfCardEq hNT).symm
  let φL : Fin (q + 1) ↪ Fin n := eL.toEmbedding.trans (Function.Embedding.subtype _)
  let φR : Fin q ↪ Fin n := eR.toEmbedding.trans (Function.Embedding.subtype _)
  have hφL : ∀ i, φL i ∈ T := fun i => (eL i).2
  have hφR : ∀ j, φR j ∈ T.biUnion G₁ := fun j => (eR j).2
  have sL : ∀ u ∈ T, ∃ i, φL i = u := by
    intro u hu
    refine ⟨eL.symm ⟨u, hu⟩, ?_⟩
    simp [φL]
  have sR : ∀ v ∈ T.biUnion G₁, ∃ j, φR j = v := by
    intro v hv
    refine ⟨eR.symm ⟨v, hv⟩, ?_⟩
    simp [φR]
  let G : PEqualNP.Expanders.BipGraph (q + 1) q :=
    fun i => Finset.univ.filter (fun j => φR j ∈ G₁ (φL i))
  have hG : ∀ i j, j ∈ G i ↔ φR j ∈ G₁ (φL i) := by
    intro i j
    simp [G]
  have hsub : ∀ i, G₁ (φL i) ⊆ T.biUnion G₁ := by
    intro i v hv
    exact Finset.mem_biUnion.mpr ⟨φL i, hφL i, hv⟩
  have hmapG : ∀ i, (G i).map φR = G₁ (φL i) := by
    intro i
    ext v
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hG i j).mp hj
    · intro hv
      obtain ⟨j, rfl⟩ := sR v (hsub i hv)
      exact ⟨j, (hG i j).mpr hv, rfl⟩
  have hmapBU : ∀ S : Finset (Fin (q + 1)), (S.biUnion G).map φR = (S.map φL).biUnion G₁ := by
    intro S
    ext v
    simp only [Finset.mem_map, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, ⟨i, hi, hj⟩, rfl⟩
      exact ⟨φL i, ⟨i, hi, rfl⟩, (hG i j).mp hj⟩
    · rintro ⟨u, ⟨i, hi, rfl⟩, hv⟩
      obtain ⟨j, rfl⟩ := sR v (hsub i hv)
      exact ⟨j, ⟨i, hi, (hG i j).mpr hv⟩, rfl⟩
  have hmapS : ∀ S : Finset (Fin (q + 1)), S.map φL ⊆ T := by
    intro S u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    exact hφL i
  have hmapF : ∀ (S : Finset (Fin (q + 1))) (j : Fin q),
      (S.filter (fun i => j ∈ G i)).map φL = (S.map φL).filter (fun u => φR j ∈ G₁ u) := by
    intro S j
    ext u
    simp only [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨hi, hj⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (hG i j).mp hj⟩
    · rintro ⟨⟨i, hi, rfl⟩, hv⟩
      exact ⟨i, ⟨hi, (hG i j).mpr hv⟩, rfl⟩
  have hmapT : (Finset.univ : Finset (Fin (q + 1))).map φL = T := by
    ext u
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact hφL i
    · exact sL u
  refine ⟨G, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    have hS' : (S.map φL).card ≤ r := by simpa using hS
    have := h1 (S.map φL) (hmapS S) hS'
    rw [Finset.card_map] at this
    refine le_trans this ?_
    rw [← Finset.card_map φR]
    apply Finset.card_le_card
    intro v hv
    have hv1 := (Finset.mem_filter.mp hv).2
    have hpos : 0 < ((S.map φL).filter (fun u => v ∈ G₁ u)).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    have hu' := Finset.mem_filter.mp hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu'.1
    obtain ⟨j, rfl⟩ := sR v (hsub i hu'.2)
    refine Finset.mem_map.mpr ⟨j, ?_, rfl⟩
    simp only [PEqualNP.Expanders.uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.card_map φL, hmapF]
    exact hv1
  · intro i
    have := h2 (φL i) (hφL i)
    rw [← hmapG i, Finset.card_map] at this
    exact this
  · intro j
    have := h3 (φR j) (hφR j)
    have e : (PEqualNP.Expanders.rightNbrs G j).card = (T.filter (fun u => φR j ∈ G₁ u)).card := by
      rw [← hmapT, ← hmapF, Finset.card_map]
      rfl
    rw [e]
    exact this
  · intro S hS
    have hne : S.map φL ≠ T := by
      intro heq
      apply hS
      apply Finset.eq_univ_of_card
      have := congrArg Finset.card heq
      rw [Finset.card_map, hT] at this
      simpa using this
    have := h4 (S.map φL) (hmapS S) hne
    rw [Finset.card_map, ← hmapBU, Finset.card_map] at this
    exact this
  · intro f hf
    let fL : Fin n → Bool := fun u => decide (∃ i, φL i = u ∧ f (Sum.inl i) = true)
    let fR : Fin n → Bool := fun v => decide (∃ j, φR j = v ∧ f (Sum.inr j) = true)
    have hfL : ∀ i, fL (φL i) = f (Sum.inl i) := by
      intro i
      by_cases hb : f (Sum.inl i) = true
      · rw [hb]
        exact decide_eq_true ⟨i, rfl, hb⟩
      · have hb' : f (Sum.inl i) = false := by simpa using hb
        rw [hb']
        apply decide_eq_false
        rintro ⟨i', hi', ht⟩
        rw [φL.injective hi'] at ht
        exact hb ht
    have hfR : ∀ j, fR (φR j) = f (Sum.inr j) := by
      intro j
      by_cases hb : f (Sum.inr j) = true
      · rw [hb]
        exact decide_eq_true ⟨j, rfl, hb⟩
      · have hb' : f (Sum.inr j) = false := by simpa using hb
        rw [hb']
        apply decide_eq_false
        rintro ⟨j', hj', ht⟩
        rw [φR.injective hj'] at ht
        exact hb ht
    have hcon := h5 fL fR (by
      intro u hu v hv
      obtain ⟨i, rfl⟩ := sL u hu
      obtain ⟨j, rfl⟩ := sR v (hsub i hv)
      rw [hfL, hfR]
      exact hf i j ((hG i j).mpr hv))
    have hLL : ∀ i i', f (Sum.inl i) = f (Sum.inl i') := by
      intro i i'
      rw [← hfL, ← hfL]
      exact hcon _ (hφL i) _ (hφL i')
    have hRL : ∀ j, f (Sum.inr j) = f (Sum.inl 0) := by
      intro j
      obtain ⟨u, hu, hv⟩ := Finset.mem_biUnion.mp (hφR j)
      obtain ⟨i, rfl⟩ := sL u hu
      rw [← hf i j ((hG i j).mpr hv)]
      exact hLL i 0
    have hall : ∀ x, f x = f (Sum.inl 0) := by
      intro x
      cases x with
      | inl i => exact hLL i 0
      | inr j => exact hRL j
    intro x y
    rw [hall x, hall y]
  · intro a us vs hc
    refine h6 a (us.trans φL) (vs.trans φR) (fun i => hφL _) ?_
    intro i
    exact ⟨(hG _ _).mp (hc i).1, (hG _ _).mp (hc i).2⟩

end PEqualNP.Outside.L_pcx_352

theorem PEqualNP.Outside.L_pcx_352 : (∃ C Q₀ : ℕ, 2 ≤ C ∧ ∀ Q : ℕ, Q₀ ≤ Q →
  ∃ q : ℕ, 2 ≤ q ∧ q ≤ Q ∧ Q ≤ C*q ∧
    ∃ G : PEqualNP.Expanders.BipGraph (q+1) q,
      PEqualNP.Expanders.IsBdryExpander G (Q/C) 2 ∧
      (∀ u, 2 ≤ (G u).card ∧ (G u).card ≤ 16) ∧
      (∀ v, 2 ≤ (PEqualNP.Expanders.rightNbrs G v).card ∧
        (PEqualNP.Expanders.rightNbrs G v).card ≤ 16) ∧
      (∀ T : Finset (Fin (q+1)), T ≠ Finset.univ → T.card ≤ (T.biUnion G).card) ∧
      (∀ f : Fin (q+1) ⊕ Fin q → Bool,
        (∀ u, ∀ v ∈ G u, f (Sum.inl u) = f (Sum.inr v)) → ∀ x y, f x = f y) ∧
      ∀ (a : ℕ) (us : Fin (a+2) ↪ Fin (q+1)) (vs : Fin (a+2) ↪ Fin q),
        (∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i+1))) →
        Nat.clog 2 Q ≤ C*(2*(a+2))) := by
  refine ⟨16384, 2 ^ 30, by norm_num, ?_⟩
  intro Q hQ
  have hQ1 : 1 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hc1 : Q ≤ 2 ^ Nat.clog 2 Q := Nat.le_pow_clog (by norm_num) Q
  have hc2 : 2 ^ (Nat.clog 2 Q).pred < Q := Nat.pow_pred_clog_lt_self 2 hQ1
  have hc30 : 30 ≤ Nat.clog 2 Q := by
    have : (2 : ℕ) ^ 30 ≤ 2 ^ Nat.clog 2 Q := le_trans hQ hc1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  obtain ⟨c, hc⟩ : ∃ c, Nat.clog 2 Q = c := ⟨_, rfl⟩
  rw [hc] at hc1 hc2 hc30
  set L := c / 32768 with hL
  have hcQ : c ≤ Q := by
    have h1 : c - 1 < 2 ^ (c - 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (c - 1) < Q := by simpa [Nat.pred_eq_sub_one] using hc2
    omega
  have h8L : 8 * L ≤ Q := by omega
  obtain ⟨σ, hexp, hbad⟩ := PEqualNP.Outside.L_pcx_352.select Q L h8L
  have hm : 256 * (2 * 512 ^ (L + 1) + 1) ≤ Q := by
    have h2 : 2 ^ (c - 1) < Q := by simpa [Nat.pred_eq_sub_one] using hc2
    have e1 : (512 : ℕ) ^ (L + 1) = 2 ^ (9 * L + 9) := by
      rw [show (512 : ℕ) = 2 ^ 9 by norm_num, ← pow_mul]
      congr 1
    have e2 : (2 : ℕ) ^ (9 * L + 19) = 1024 * 2 ^ (9 * L + 9) := by
      rw [show 9 * L + 19 = 10 + (9 * L + 9) by ring, pow_add]
      norm_num
    have h3 : (2 : ℕ) ^ (9 * L + 19) ≤ 2 ^ (c - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 1 ≤ (2 : ℕ) ^ (9 * L + 9) := Nat.one_le_two_pow
    rw [e1]
    omega
  have hr : 1 ≤ Q / 8192 := by
    have : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    omega
  obtain ⟨G₁, T, q, hT, hNT, hrq, h1, h2, h3, h4, h5, h6⟩ :=
    PEqualNP.Outside.L_pcx_352.surgery Q (Q / 8192) L (2 * 512 ^ (L + 1)) σ hr hexp hbad hm
  obtain ⟨G, g1, g2, g3, g4, g5, g6⟩ :=
    PEqualNP.Outside.L_pcx_352.transfer Q (Q / 8192) L q G₁ T hT hNT h1 h2 h3 h4 h5 h6
  have hqQ : q + 1 ≤ Q := by
    have := Finset.card_le_univ T
    simpa [hT] using this
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  refine ⟨q, by omega, by omega, by omega, G, ?_, g2, g3, g4, g5, ?_⟩
  · intro S hS
    exact g1 S (le_trans hS (by omega))
  · intro a us vs hcyc
    have := g6 a us vs hcyc
    rw [hc]
    omega
