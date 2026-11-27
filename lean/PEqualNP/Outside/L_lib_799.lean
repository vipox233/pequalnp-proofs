import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_799

open scoped BigOperators

private def s (c : Bool) : ℤ := if c then 1 else -1

private lemma s_mul_self (c : Bool) : s c * s c = 1 := by
  cases c <;> decide

private lemma s_sq (c : Bool) : s c ^ 2 = 1 := by
  cases c <;> decide

private lemma s_not (c : Bool) : s (!c) = -s c := by
  cases c <;> decide

private lemma s_beq (a c : Bool) : s (a == c) = s a * s c := by
  cases a <;> cases c <;> decide

private lemma s_pow_even (c : Bool) {k : ℕ} (hk : Even k) : s c ^ k = 1 := by
  rcases hk with ⟨r, rfl⟩
  rw [← two_mul, pow_mul, s_sq, one_pow]

private lemma s_pow_mod_two (c : Bool) (k : ℕ) :
    s c ^ k = if k % 2 = 1 then s c else 1 := by
  have hk : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
  conv_lhs => rw [hk]
  rw [pow_add, pow_mul, s_sq, one_pow, one_mul]
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hmod with h | h <;> simp [h]

private lemma sum_s_eq_two_mul_card_sub {α : Type*} [Fintype α]
    (p q : α → Bool) [DecidablePred (fun x => p x = q x)] :
    (∑ x : α, s (p x) * s (q x)) =
      2 * (((Finset.univ : Finset α).filter (fun x => p x = q x)).card : ℤ) -
        (Fintype.card α : ℤ) := by
  have h1 : ∀ x : α, s (p x) * s (q x) = (if p x = q x then (2 : ℤ) else 0) - 1 := by
    intro x
    by_cases h : p x = q x
    · simp only [h, ↓reduceIte]; cases q x <;> decide
    · simp only [h, ↓reduceIte]
      cases hp : p x <;> cases hq : q x <;> simp_all [s]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  ring

private lemma sum_prod_s_eq_gain_int {N m b : ℕ} (f : Fin N → Fin m → Bool)
    (enc : Fin N → (Fin b → Bool)) (dec : (Fin b → Bool) → Fin m → Bool) :
    (∑ x : Fin N, ∑ j : Fin m, s (dec (enc x) j) * s (f x j)) =
      2 * (((Finset.univ : Finset (Fin N × Fin m)).filter (fun q =>
        dec (enc q.1) q.2 = f q.1 q.2)).card : ℤ) - ((N * m : ℕ) : ℤ) := by
  rw [← Fintype.sum_prod_type']
  have h := sum_s_eq_two_mul_card_sub
    (fun q : Fin N × Fin m => dec (enc q.1) q.2) (fun q : Fin N × Fin m => f q.1 q.2)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

private lemma chebyshev_pow {α : Type*} [Fintype α] (a : α → ℤ)
    (ha : ∀ x, 0 ≤ a x) (k : ℕ) :
    (∑ x : α, a x) * (∑ x : α, a x ^ k) ≤
      (Fintype.card α : ℤ) * (∑ x : α, a x ^ (k + 1)) := by
  have hnonneg :
      0 ≤ ∑ x : α, ∑ y : α, (a x - a y) * (a x ^ k - a y ^ k) := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    rcases le_total (a x) (a y) with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy)
        (sub_nonpos.mpr (pow_le_pow_left₀ (ha x) hxy k))
    · exact mul_nonneg (sub_nonneg.mpr hyx)
        (sub_nonneg.mpr (pow_le_pow_left₀ (ha y) hyx k))
  have hident :
      (∑ x : α, ∑ y : α, (a x - a y) * (a x ^ k - a y ^ k)) =
        2 * ((Fintype.card α : ℤ) * (∑ x : α, a x ^ (k + 1)) -
          (∑ x : α, a x) * (∑ x : α, a x ^ k)) := by
    have hterm : ∀ x y : α,
        (a x - a y) * (a x ^ k - a y ^ k) =
          a x ^ (k + 1) + a y ^ (k + 1) - a x * a y ^ k - a y * a x ^ k := by
      intro x y; ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  linarith

private lemma pow_sum_le_card_mul_sum_pow {α : Type*} [Fintype α] (a : α → ℤ)
    (ha : ∀ x, 0 ≤ a x) :
    ∀ k : ℕ, 1 ≤ k →
      (∑ x : α, a x) ^ k ≤ (Fintype.card α : ℤ) ^ (k - 1) * (∑ x : α, a x ^ k) := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : 1 + (n + 1) = (1 + n) + 1 := by omega
    rw [hstep, pow_succ']
    have hsum_nn : 0 ≤ ∑ x : α, a x := Finset.sum_nonneg fun x _ => ha x
    have hcard_nn : (0 : ℤ) ≤ (Fintype.card α : ℤ) ^ n := by positivity
    calc
      (∑ x : α, a x) * (∑ x : α, a x) ^ (1 + n)
          ≤ (∑ x : α, a x) *
              ((Fintype.card α : ℤ) ^ (1 + n - 1) * ∑ x : α, a x ^ (1 + n)) :=
        mul_le_mul_of_nonneg_left ih hsum_nn
      _ = (Fintype.card α : ℤ) ^ n *
            ((∑ x : α, a x) * ∑ x : α, a x ^ (1 + n)) := by
        have h1 : 1 + n - 1 = n := by omega
        rw [h1]; ring
      _ ≤ (Fintype.card α : ℤ) ^ n *
            ((Fintype.card α : ℤ) * ∑ x : α, a x ^ (1 + n + 1)) :=
        mul_le_mul_of_nonneg_left (chebyshev_pow a ha (1 + n)) hcard_nn
      _ = (Fintype.card α : ℤ) ^ (1 + n + 1 - 1) * ∑ x : α, a x ^ (1 + n + 1) := by
        have h2 : 1 + n + 1 - 1 = n + 1 := by omega
        rw [h2, pow_succ']; ring

private lemma sum_pow_eq_sum_pi {m : ℕ} (g : Fin m → ℤ) (k : ℕ) :
    (∑ j : Fin m, g j) ^ k = ∑ t : Fin k → Fin m, ∏ i : Fin k, g (t i) := by
  have h1 : (∑ j : Fin m, g j) ^ k = ∏ _i : Fin k, ∑ j : Fin m, g j := by simp
  rw [h1, Fintype.prod_sum]

private lemma sum_s_flip_zero {α : Type*} [Fintype α] [DecidableEq α]
    (j₀ : α) (F : (α → Bool) → ℤ)
    (hF : ∀ σ, F (Function.update σ j₀ !(σ j₀)) = -F σ) :
    (∑ σ : α → Bool, F σ) = 0 := by
  let flip : (α → Bool) → (α → Bool) := fun σ => Function.update σ j₀ !(σ j₀)
  have hinv : Function.Involutive flip := by
    intro σ; funext j; by_cases hj : j = j₀ <;> simp [flip, hj]
  have hsum : (∑ σ : α → Bool, F (flip σ)) = ∑ σ : α → Bool, F σ :=
    Fintype.sum_equiv (Equiv.mk flip flip hinv hinv) _ _ (fun _ => rfl)
  have hneg : (∑ σ : α → Bool, F (flip σ)) = -(∑ σ : α → Bool, F σ) := by
    dsimp only [flip]
    simp_rw [hF]
    rw [Finset.sum_neg_distrib]
  linarith

private lemma sum_prod_s_eq_zero_of_ind {N m b : ℕ}
    (f : Fin N → Fin m → Bool)
    (hInd : ∀ S : Finset (Fin m), S.card ≤ 2 * b → ∀ u : Fin m → Bool,
      2 ^ S.card * ((Finset.univ : Finset (Fin N)).filter (fun x =>
        ∀ j ∈ S, f x j = u j)).card = N)
    (S : Finset (Fin m)) (hS_ne : S.Nonempty) (hS_card : S.card ≤ 2 * b) :
    (∑ x : Fin N, ∏ j ∈ S, s (f x j)) = 0 := by
  let ext : (S → Bool) → (Fin m → Bool) := fun u j => if h : j ∈ S then u ⟨j, h⟩ else false
  let res : Fin N → (S → Bool) := fun x j => f x j.1
  have hfib : (∑ x : Fin N, ∏ j ∈ S, s (f x j)) =
      ∑ u : S → Bool,
        (((Finset.univ : Finset (Fin N)).filter (fun x => ∀ j ∈ S, f x j = ext u j)).card : ℤ) *
          ∏ j : S, s (u j) := by
    have h1 := (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset (S → Bool)))
      (g := res)
      (f := fun x => ∏ j ∈ S, s (f x j))
      (fun _ _ => Finset.mem_univ _)).symm
    rw [h1]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hfilt : (Finset.univ : Finset (Fin N)).filter (fun x => res x = u) =
        (Finset.univ : Finset (Fin N)).filter (fun x => ∀ j ∈ S, f x j = ext u j) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, res, ext]
      constructor
      · intro h j hj
        simp only [hj, ↓reduceDIte]
        exact congrFun h ⟨j, hj⟩
      · intro h
        funext ⟨j, hj⟩
        simpa [hj] using h j hj
    rw [hfilt]
    have hconst : ∀ x ∈ (Finset.univ : Finset (Fin N)).filter
        (fun x => ∀ j ∈ S, f x j = ext u j),
        (∏ j ∈ S, s (f x j)) = ∏ j : S, s (u j) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [← Finset.prod_coe_sort S (fun j => s (f x j))]
      refine Finset.prod_congr rfl fun ⟨j, hj⟩ _ => ?_
      have hxj := hx.2 j hj
      simp only [ext, hj, ↓reduceDIte] at hxj
      rw [hxj]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hsum_u : (∑ u : S → Bool, ∏ j : S, s (u j)) = 0 := by
    obtain ⟨j₀, hj₀⟩ := hS_ne
    let k₀ : S := ⟨j₀, hj₀⟩
    refine sum_s_flip_zero k₀ (fun u => ∏ j : S, s (u j)) fun u => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun j : S => s (Function.update u k₀ (!(u k₀)) j))
          (Finset.mem_univ k₀),
        ← Finset.mul_prod_erase Finset.univ (fun j : S => s (u j))
          (Finset.mem_univ k₀)]
    have hrest :
        (∏ j ∈ Finset.univ.erase k₀, s (Function.update u k₀ (!(u k₀)) j)) =
          ∏ j ∈ Finset.univ.erase k₀, s (u j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hrest, Function.update_self, s_not, neg_mul]
  have hmul : ((2 ^ S.card : ℕ) : ℤ) * (∑ x : Fin N, ∏ j ∈ S, s (f x j)) = 0 := by
    rw [hfib, Finset.mul_sum]
    have hterm : ∀ u : S → Bool,
        ((2 ^ S.card : ℕ) : ℤ) *
          ((((Finset.univ : Finset (Fin N)).filter
            (fun x => ∀ j ∈ S, f x j = ext u j)).card : ℤ) * ∏ j : S, s (u j)) =
        (N : ℤ) * ∏ j : S, s (u j) := by
      intro u
      rw [← mul_assoc]
      have hN := hInd S hS_card (ext u)
      have hcast : ((2 ^ S.card : ℕ) : ℤ) *
          (((Finset.univ : Finset (Fin N)).filter
            (fun x => ∀ j ∈ S, f x j = ext u j)).card : ℤ) = (N : ℤ) := by
        exact_mod_cast hN
      rw [hcast]
    simp_rw [hterm, ← Finset.mul_sum, hsum_u, mul_zero]
  have h2ne : ((2 ^ S.card : ℕ) : ℤ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hmul).resolve_left h2ne

private def evenTuples {n m : ℕ} (hm : 0 < m) (A : Finset (Fin n)) :
    Finset (Fin n → Fin m) :=
  Finset.univ.filter fun t =>
    (∀ i, i ∉ A → t i = ⟨0, hm⟩) ∧
    (∀ j : Fin m, Even (A.filter (fun i => t i = j)).card)

private lemma evenTuples_card_le {n m : ℕ} (hm : 0 < m) :
    ∀ (k : ℕ) (A : Finset (Fin n)), A.card = 2 * k →
      (evenTuples hm A).card ≤ (2 * k) ^ k * m ^ k := by
  intro k
  induction k with
  | zero =>
    intro A hA
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hAe
    have hsub : evenTuples hm (∅ : Finset (Fin n)) ⊆ {fun _ => ⟨0, hm⟩} := by
      intro t ht
      rw [Finset.mem_singleton]
      rw [evenTuples, Finset.mem_filter] at ht
      funext i
      exact ht.2.1 i (Finset.notMem_empty i)
    have hle := Finset.card_le_card hsub
    simpa using hle
  | succ k ih =>
    intro A hA
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hAne
    let A₁ := A.erase i₀
    have hA₁_card : A₁.card = 2 * k + 1 := by
      rw [Finset.card_erase_of_mem hi₀]; omega
    have hsub : evenTuples hm A ⊆
        A₁.biUnion fun i₁ =>
          (Finset.univ : Finset (Fin m)).biUnion fun v =>
            (evenTuples hm (A₁.erase i₁)).image fun t' =>
              Function.update (Function.update t' i₀ v) i₁ v := by
      intro t ht
      rw [evenTuples, Finset.mem_filter] at ht
      rcases ht.2 with ⟨hout, heven⟩
      let v : Fin m := t i₀
      have hi₀_mem : i₀ ∈ A.filter (fun i => t i = v) :=
        Finset.mem_filter.mpr ⟨hi₀, rfl⟩
      have hcard_pos : 0 < (A.filter (fun i => t i = v)).card :=
        Finset.card_pos.mpr ⟨i₀, hi₀_mem⟩
      have hcard_gt1 : 1 < (A.filter (fun i => t i = v)).card := by
        rcases heven v with ⟨r, hr⟩
        omega
      obtain ⟨i₁, hi₁_mem, hi₁_ne⟩ := Finset.exists_mem_ne hcard_gt1 i₀
      have hi₁_A : i₁ ∈ A := (Finset.mem_filter.mp hi₁_mem).1
      have hti₁ : t i₁ = v := (Finset.mem_filter.mp hi₁_mem).2
      have hi₁_A₁ : i₁ ∈ A₁ := Finset.mem_erase.mpr ⟨hi₁_ne, hi₁_A⟩
      let A₂ := A₁.erase i₁
      let t' : Fin n → Fin m := fun i => if i ∈ A₂ then t i else ⟨0, hm⟩
      rw [Finset.mem_biUnion]
      refine ⟨i₁, hi₁_A₁, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨v, Finset.mem_univ v, ?_⟩
      rw [Finset.mem_image]
      refine ⟨t', ?_, ?_⟩
      · rw [evenTuples, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro i hi; simp only [t', A₂, hi, ↓reduceIte]
        · intro j
          have hfilt_eq : A₂.filter (fun i => t' i = j) = A₂.filter (fun i => t i = j) := by
            refine Finset.filter_congr fun i hi => ?_
            simp [t', hi]
          rw [hfilt_eq]
          have herase_filt :
              A₂.filter (fun i => t i = j) =
                ((A.filter (fun i => t i = j)).erase i₀).erase i₁ := by
            ext i
            simp only [A₂, A₁, Finset.mem_filter, Finset.mem_erase]
            tauto
          rw [herase_filt]
          by_cases hjv : j = v
          · subst hjv
            have hi₁_e : i₁ ∈ (A.filter (fun i => t i = t i₀)).erase i₀ :=
              Finset.mem_erase.mpr ⟨hi₁_ne, hi₁_mem⟩
            rw [Finset.card_erase_of_mem hi₁_e, Finset.card_erase_of_mem hi₀_mem]
            rcases heven v with ⟨r, hr⟩
            refine ⟨r - 1, ?_⟩
            omega
          · have hi₀_not : i₀ ∉ A.filter (fun i => t i = j) := by
              simp [v, Ne.symm hjv]
            have hi₁_not : i₁ ∉ (A.filter (fun i => t i = j)).erase i₀ := by
              intro hmem
              have := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hmem)).2
              exact hjv (this.symm.trans hti₁)
            rw [Finset.erase_eq_of_notMem hi₁_not, Finset.erase_eq_of_notMem hi₀_not]
            exact heven j
      · funext i
        by_cases h1 : i = i₁
        · subst h1; simp [hti₁]
        · by_cases h0 : i = i₀
          · subst h0; simp [h1, v]
          · rw [Function.update_of_ne h1, Function.update_of_ne h0]
            by_cases hiA : i ∈ A
            · have hiA₂ : i ∈ A₂ :=
                Finset.mem_erase.mpr ⟨h1, Finset.mem_erase.mpr ⟨h0, hiA⟩⟩
              simp [t', hiA₂]
            · have hiA₂ : i ∉ A₂ := by
                intro hmem
                exact hiA (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
              simp [t', hiA₂, hout i hiA]
    have hcard_le : (evenTuples hm A).card ≤ (2 * k + 1) * (m * ((2 * k) ^ k * m ^ k)) := by
      calc
        (evenTuples hm A).card
            ≤ (A₁.biUnion fun i₁ =>
                (Finset.univ : Finset (Fin m)).biUnion fun v =>
                  (evenTuples hm (A₁.erase i₁)).image fun t' =>
                    Function.update (Function.update t' i₀ v) i₁ v).card :=
          Finset.card_le_card hsub
        _ ≤ ∑ i₁ ∈ A₁,
              ((Finset.univ : Finset (Fin m)).biUnion fun v =>
                (evenTuples hm (A₁.erase i₁)).image fun t' =>
                  Function.update (Function.update t' i₀ v) i₁ v).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ i₁ ∈ A₁,
              ∑ v : Fin m,
                ((evenTuples hm (A₁.erase i₁)).image fun t' =>
                  Function.update (Function.update t' i₀ v) i₁ v).card :=
          Finset.sum_le_sum fun i₁ _ => Finset.card_biUnion_le
        _ ≤ ∑ i₁ ∈ A₁, ∑ _v : Fin m, ((2 * k) ^ k * m ^ k) := by
          refine Finset.sum_le_sum fun i₁ hi₁ => Finset.sum_le_sum fun _v _ => ?_
          have hA₂_card : (A₁.erase i₁).card = 2 * k := by
            rw [Finset.card_erase_of_mem hi₁]; omega
          exact Finset.card_image_le.trans (ih (A₁.erase i₁) hA₂_card)
        _ = (2 * k + 1) * (m * ((2 * k) ^ k * m ^ k)) := by
          simp [hA₁_card, Fintype.card_fin]
    have hpow : (2 * k) ^ k ≤ (2 * (k + 1)) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    have h1 : (2 * k + 1) * (2 * k) ^ k ≤ (2 * (k + 1)) * (2 * (k + 1)) ^ k :=
      Nat.mul_le_mul (by omega) hpow
    calc
      (evenTuples hm A).card
          ≤ (2 * k + 1) * (m * ((2 * k) ^ k * m ^ k)) := hcard_le
      _ = ((2 * k + 1) * (2 * k) ^ k) * (m * m ^ k) := by ring
      _ ≤ ((2 * (k + 1)) * (2 * (k + 1)) ^ k) * (m * m ^ k) :=
        Nat.mul_le_mul_right _ h1
      _ = (2 * (k + 1)) ^ (k + 1) * m ^ (k + 1) := by
        rw [pow_succ', pow_succ']

private lemma moment_2b_le {N m b : ℕ} (hm : 0 < m)
    (f : Fin N → Fin m → Bool)
    (hInd : ∀ S : Finset (Fin m), S.card ≤ 2 * b → ∀ u : Fin m → Bool,
      2 ^ S.card * ((Finset.univ : Finset (Fin N)).filter (fun x =>
        ∀ j ∈ S, f x j = u j)).card = N)
    (d : Fin m → Bool) :
    (∑ x : Fin N, (∑ j : Fin m, s (d j) * s (f x j)) ^ (2 * b)) ≤
      ((2 * b) ^ b * m ^ b * N : ℕ) := by
  have hexp :
      (∑ x : Fin N, (∑ j : Fin m, s (d j) * s (f x j)) ^ (2 * b)) =
        ∑ t : Fin (2 * b) → Fin m,
          (∏ i : Fin (2 * b), s (d (t i))) *
            (∑ x : Fin N, ∏ i : Fin (2 * b), s (f x (t i))) := by
    simp_rw [sum_pow_eq_sum_pi, Finset.prod_mul_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
  rw [hexp]
  have hterm : ∀ t : Fin (2 * b) → Fin m,
      (∏ i : Fin (2 * b), s (d (t i))) *
        (∑ x : Fin N, ∏ i : Fin (2 * b), s (f x (t i))) =
      if t ∈ evenTuples hm (Finset.univ : Finset (Fin (2 * b))) then (N : ℤ) else 0 := by
    intro t
    let cnt : Fin m → ℕ := fun j =>
      ((Finset.univ : Finset (Fin (2 * b))).filter (fun i => t i = j)).card
    have hprod_fib : ∀ g : Fin m → Bool,
        (∏ i : Fin (2 * b), s (g (t i))) = ∏ j : Fin m, s (g j) ^ cnt j := by
      intro g
      have h1 := (Finset.prod_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin (2 * b))))
        (t := (Finset.univ : Finset (Fin m)))
        (g := t)
        (f := fun i => s (g (t i)))
        (fun _ _ => Finset.mem_univ _)).symm
      rw [h1]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hc : ∀ i ∈ (Finset.univ : Finset (Fin (2 * b))).filter (fun i => t i = j),
          s (g (t i)) = s (g j) := by
        intro i hi; rw [(Finset.mem_filter.mp hi).2]
      rw [Finset.prod_congr rfl hc, Finset.prod_const]
    by_cases ht : t ∈ evenTuples hm (Finset.univ : Finset (Fin (2 * b)))
    · simp only [ht, ↓reduceIte]
      rw [evenTuples, Finset.mem_filter] at ht
      have hev : ∀ j : Fin m, Even (cnt j) := ht.2.2
      have hd1 : (∏ i : Fin (2 * b), s (d (t i))) = 1 := by
        rw [hprod_fib d]
        exact Finset.prod_eq_one fun j _ => s_pow_even (d j) (hev j)
      have hf1 : ∀ x : Fin N, (∏ i : Fin (2 * b), s (f x (t i))) = 1 := by
        intro x
        rw [hprod_fib (f x)]
        exact Finset.prod_eq_one fun j _ => s_pow_even (f x j) (hev j)
      simp [hd1, hf1]
    · simp only [ht, ↓reduceIte]
      have hnot_all : ¬ ∀ j : Fin m, Even (cnt j) := by
        intro hall
        apply ht
        rw [evenTuples, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun i hi => absurd (Finset.mem_univ i) hi, hall⟩
      rw [not_forall] at hnot_all
      obtain ⟨j₀, hj₀⟩ := hnot_all
      let O : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun j => cnt j % 2 = 1)
      have hO_ne : O.Nonempty := by
        refine ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rw [Nat.even_iff] at hj₀
        omega
      have hO_sub : O ⊆ (Finset.univ : Finset (Fin (2 * b))).image t := by
        intro j hj
        have hmod : cnt j % 2 = 1 := (Finset.mem_filter.mp hj).2
        have hpos : 0 < cnt j := by omega
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      have hO_card : O.card ≤ 2 * b := by
        calc
          O.card ≤ ((Finset.univ : Finset (Fin (2 * b))).image t).card :=
            Finset.card_le_card hO_sub
          _ ≤ (Finset.univ : Finset (Fin (2 * b))).card := Finset.card_image_le
          _ = 2 * b := by simp
      have hfO : ∀ x : Fin N, (∏ i : Fin (2 * b), s (f x (t i))) = ∏ j ∈ O, s (f x j) := by
        intro x
        rw [hprod_fib (f x)]
        simp_rw [s_pow_mod_two]
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      simp_rw [hfO]
      rw [sum_prod_s_eq_zero_of_ind f hInd O hO_ne hO_card, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hfilt_eq :
      (Finset.univ : Finset (Fin (2 * b) → Fin m)).filter
        (fun t => t ∈ evenTuples hm Finset.univ) =
      evenTuples hm Finset.univ := by
    ext t; simp
  rw [hfilt_eq]
  have hcard := evenTuples_card_le hm b (Finset.univ : Finset (Fin (2 * b))) (by simp)
  have hcard_z : ((evenTuples hm (Finset.univ : Finset (Fin (2 * b)))).card : ℤ) ≤
      (((2 * b) ^ b * m ^ b : ℕ) : ℤ) := by
    exact_mod_cast hcard
  have hN_nn : (0 : ℤ) ≤ (N : ℤ) := Nat.cast_nonneg N
  calc
    ((evenTuples hm (Finset.univ : Finset (Fin (2 * b)))).card : ℤ) * (N : ℤ)
        ≤ (((2 * b) ^ b * m ^ b : ℕ) : ℤ) * (N : ℤ) :=
      mul_le_mul_of_nonneg_right hcard_z hN_nn
    _ = (((2 * b) ^ b * m ^ b * N : ℕ) : ℤ) := by push_cast; ring

private lemma upper_bound {N m b : ℕ} (hN : 0 < N) (hb : 0 < b) (hbm : b ≤ m)
    (f : Fin N → Fin m → Bool)
    (hInd : ∀ S : Finset (Fin m), S.card ≤ 2 * b → ∀ u : Fin m → Bool,
      2 ^ S.card * ((Finset.univ : Finset (Fin N)).filter (fun x =>
        ∀ j ∈ S, f x j = u j)).card = N)
    (enc : Fin N → (Fin b → Bool)) (dec : (Fin b → Bool) → Fin m → Bool) :
    (2 * ((Finset.univ : Finset (Fin N × Fin m)).filter (fun q =>
      dec (enc q.1) q.2 = f q.1 q.2)).card - N * m) ^ 2 ≤ 4 * b * m * N ^ 2 := by
  have hm : 0 < m := lt_of_lt_of_le hb hbm
  set hits := ((Finset.univ : Finset (Fin N × Fin m)).filter (fun q =>
    dec (enc q.1) q.2 = f q.1 q.2)).card
  by_cases hlt : 2 * hits < N * m
  · have h0 : 2 * hits - N * m = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
    rw [h0]; simp
  · replace hlt : N * m ≤ 2 * hits := Nat.le_of_not_lt hlt
    set G : ℤ := ∑ x : Fin N, ∑ j : Fin m, s (dec (enc x) j) * s (f x j)
    have hG_eq : ((2 * hits - N * m : ℕ) : ℤ) = G := by
      have h1 : G = 2 * (hits : ℤ) - ((N * m : ℕ) : ℤ) := sum_prod_s_eq_gain_int f enc dec
      rw [Nat.cast_sub hlt, h1]
      push_cast
      ring
    have hG_nn : 0 ≤ G := by rw [← hG_eq]; exact Nat.cast_nonneg _
    let S : Fin N → (Fin b → Bool) → ℤ :=
      fun x w => ∑ j : Fin m, s (dec w j) * s (f x j)
    have hG_le_abs : G ≤ ∑ x : Fin N, |S x (enc x)| :=
      Finset.sum_le_sum fun x _ => le_abs_self _
    have h2b_ge1 : 1 ≤ 2 * b := by omega
    have hpow_le : G ^ (2 * b) ≤ (N : ℤ) ^ (2 * b - 1) * ∑ x : Fin N, S x (enc x) ^ (2 * b) := by
      calc
        G ^ (2 * b) ≤ (∑ x : Fin N, |S x (enc x)|) ^ (2 * b) :=
          pow_le_pow_left₀ hG_nn hG_le_abs (2 * b)
        _ ≤ (Fintype.card (Fin N) : ℤ) ^ (2 * b - 1) *
              ∑ x : Fin N, |S x (enc x)| ^ (2 * b) :=
          pow_sum_le_card_mul_sum_pow (fun x => |S x (enc x)|) (fun _ => abs_nonneg _)
            (2 * b) h2b_ge1
        _ = (N : ℤ) ^ (2 * b - 1) * ∑ x : Fin N, S x (enc x) ^ (2 * b) := by
          simp only [Fintype.card_fin]
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [pow_mul, sq_abs, ← pow_mul]
    have hsum_w :
        (∑ x : Fin N, S x (enc x) ^ (2 * b)) ≤
          ∑ w : Fin b → Bool, ∑ x : Fin N, S x w ^ (2 * b) := by
      calc
        (∑ x : Fin N, S x (enc x) ^ (2 * b))
            ≤ ∑ x : Fin N, ∑ w : Fin b → Bool, S x w ^ (2 * b) := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine Finset.single_le_sum (f := fun w => S x w ^ (2 * b))
            (fun w _ => ?_) (Finset.mem_univ (enc x))
          rw [pow_mul]
          exact pow_nonneg (sq_nonneg _) b
        _ = ∑ w : Fin b → Bool, ∑ x : Fin N, S x w ^ (2 * b) := Finset.sum_comm
    have hsum_w_le :
        (∑ w : Fin b → Bool, ∑ x : Fin N, S x w ^ (2 * b)) ≤
          ((2 ^ b : ℕ) : ℤ) * (((2 * b) ^ b * m ^ b * N : ℕ) : ℤ) := by
      calc
        (∑ w : Fin b → Bool, ∑ x : Fin N, S x w ^ (2 * b))
            ≤ ∑ _w : Fin b → Bool, (((2 * b) ^ b * m ^ b * N : ℕ) : ℤ) :=
          Finset.sum_le_sum fun w _ => moment_2b_le hm f hInd (dec w)
        _ = ((2 ^ b : ℕ) : ℤ) * (((2 * b) ^ b * m ^ b * N : ℕ) : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    have hG2b : G ^ (2 * b) ≤ (((4 * b * m * N ^ 2 : ℕ) : ℤ)) ^ b := by
      have hNpow_nn : (0 : ℤ) ≤ (N : ℤ) ^ (2 * b - 1) := by positivity
      calc
        G ^ (2 * b)
            ≤ (N : ℤ) ^ (2 * b - 1) * ∑ x : Fin N, S x (enc x) ^ (2 * b) := hpow_le
        _ ≤ (N : ℤ) ^ (2 * b - 1) *
              (((2 ^ b : ℕ) : ℤ) * (((2 * b) ^ b * m ^ b * N : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left (hsum_w.trans hsum_w_le) hNpow_nn
        _ = (((4 * b * m * N ^ 2 : ℕ) : ℤ)) ^ b := by
          have hNcomb : (N : ℤ) ^ (2 * b - 1) * (N : ℤ) = (N : ℤ) ^ (2 * b) := by
            rw [← pow_succ, Nat.sub_add_cancel h2b_ge1]
          push_cast
          calc
            (N : ℤ) ^ (2 * b - 1) * (2 ^ b * ((2 * (b : ℤ)) ^ b * (m : ℤ) ^ b * (N : ℤ)))
                = (2 ^ b * (2 * (b : ℤ)) ^ b * (m : ℤ) ^ b) *
                    ((N : ℤ) ^ (2 * b - 1) * (N : ℤ)) := by ring
            _ = (2 ^ b * (2 * (b : ℤ)) ^ b * (m : ℤ) ^ b) * (N : ℤ) ^ (2 * b) := by
              rw [hNcomb]
            _ = (4 * (b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2) ^ b := by
              simp only [mul_pow, ← pow_mul]
              have h4 : (4 : ℤ) ^ b = 2 ^ b * 2 ^ b := by
                rw [← mul_pow]; norm_num
              rw [h4]
              ring
    have hnat_pow : ((2 * hits - N * m) ^ 2) ^ b ≤ (4 * b * m * N ^ 2) ^ b := by
      have hz : ((((2 * hits - N * m) ^ 2) ^ b : ℕ) : ℤ) ≤
          (((4 * b * m * N ^ 2) ^ b : ℕ) : ℤ) := by
        push_cast
        rw [hG_eq, ← pow_mul]
        exact hG2b
      exact_mod_cast hz
    exact (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hb)).mp hnat_pow

private lemma poly_cs_step {α : Type*} [Fintype α] (y : α → ℤ)
    (hy : ∀ x, 0 ≤ y x) (p : ℕ) :
    (∑ x : α, y x ^ (p + 1)) ^ 2 ≤
      (∑ x : α, y x ^ p) * (∑ x : α, y x ^ (p + 2)) := by
  have hnonneg :
      0 ≤ ∑ x : α, ∑ z : α, y x ^ p * y z ^ p * (y x - y z) ^ 2 := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ => ?_
    exact mul_nonneg (mul_nonneg (pow_nonneg (hy x) p) (pow_nonneg (hy z) p)) (sq_nonneg _)
  have hident :
      (∑ x : α, ∑ z : α, y x ^ p * y z ^ p * (y x - y z) ^ 2) =
        2 * ((∑ x : α, y x ^ p) * (∑ x : α, y x ^ (p + 2)) -
          (∑ x : α, y x ^ (p + 1)) ^ 2) := by
    have hterm : ∀ x z : α,
        y x ^ p * y z ^ p * (y x - y z) ^ 2 =
          y x ^ (p + 2) * y z ^ p + y x ^ p * y z ^ (p + 2) -
            2 * (y x ^ (p + 1) * y z ^ (p + 1)) := by
      intro x z; ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

private lemma poly_cs_124 {α : Type*} [Fintype α] (y : α → ℤ)
    (hy : ∀ x, 0 ≤ y x) :
    (∑ x : α, y x ^ 2) ^ 3 ≤ (∑ x : α, y x) ^ 2 * (∑ x : α, y x ^ 4) := by
  set S1 := ∑ x : α, y x
  set S2 := ∑ x : α, y x ^ 2
  set S3 := ∑ x : α, y x ^ 3
  set S4 := ∑ x : α, y x ^ 4
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun x _ => sq_nonneg (y x)
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun x _ => by positivity
  by_cases h0 : S2 = 0
  · rw [h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg S1) hS4
  · have hS2pos : 0 < S2 := lt_of_le_of_ne hS2 (Ne.symm h0)
    have h1 : S2 ^ 2 ≤ S1 * S3 := by
      have := poly_cs_step y hy 1
      simpa only [pow_one] using this
    have h2 : S3 ^ 2 ≤ S2 * S4 := poly_cs_step y hy 2
    have h3 : S2 ^ 4 ≤ S1 ^ 2 * S3 ^ 2 := by
      have h1' : (S2 ^ 2) ^ 2 ≤ (S1 * S3) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg S2) h1 2
      have he1 : (S2 ^ 2) ^ 2 = S2 ^ 4 := by ring
      have he2 : (S1 * S3) ^ 2 = S1 ^ 2 * S3 ^ 2 := by ring
      linarith
    have h4 : S2 * S2 ^ 3 ≤ S2 * (S1 ^ 2 * S4) := by
      calc
        S2 * S2 ^ 3 = S2 ^ 4 := by ring
        _ ≤ S1 ^ 2 * S3 ^ 2 := h3
        _ ≤ S1 ^ 2 * (S2 * S4) := mul_le_mul_of_nonneg_left h2 (sq_nonneg S1)
        _ = S2 * (S1 ^ 2 * S4) := by ring
    exact le_of_mul_le_mul_left h4 hS2pos

private lemma sum_s_pair {m : ℕ} (j₁ j₂ : Fin m) :
    (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂)) =
      if j₁ = j₂ then (2 ^ m : ℤ) else 0 := by
  by_cases h : j₁ = j₂
  · subst h
    simp [s_mul_self, Fintype.card_bool, Fintype.card_fin]
  · simp only [h, ↓reduceIte]
    refine sum_s_flip_zero j₁ (fun σ => s (σ j₁) * s (σ j₂)) fun σ => ?_
    rw [Function.update_self, Function.update_of_ne (Ne.symm h), s_not, neg_mul]

private lemma sum_sq_block {m : ℕ} (B : Finset (Fin m)) :
    (∑ σ : Fin m → Bool, (∑ j ∈ B, s (σ j)) ^ 2) = (2 ^ m : ℤ) * (B.card : ℤ) := by
  have hexp :
      (∑ σ : Fin m → Bool, (∑ j ∈ B, s (σ j)) ^ 2) =
        ∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) := by
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_comm
  rw [hexp]
  simp_rw [sum_s_pair]
  simp [mul_comm]

private lemma sum_s_quad_le {m : ℕ} (j₁ j₂ j₃ j₄ : Fin m) :
    (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₄)) ≤
      (if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ m : ℤ) else 0) +
      (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ m : ℤ) else 0) +
      (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ m : ℤ) else 0) := by
  have h2m_nn : (0 : ℤ) ≤ (2 ^ m : ℤ) := by positivity
  by_cases h12 : j₁ = j₂
  · subst h12
    have hsimp : (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₁) * s (σ j₃) * s (σ j₄)) =
        ∑ σ : Fin m → Bool, s (σ j₃) * s (σ j₄) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [s_mul_self, one_mul]
    rw [hsimp, sum_s_pair]
    split_ifs <;> first | tauto | linarith
  · by_cases h13 : j₁ = j₃
    · subst h13
      have hsimp : (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₁) * s (σ j₄)) =
          ∑ σ : Fin m → Bool, s (σ j₂) * s (σ j₄) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have hre : s (σ j₁) * s (σ j₂) * s (σ j₁) * s (σ j₄) =
            (s (σ j₁) * s (σ j₁)) * (s (σ j₂) * s (σ j₄)) := by ring
        rw [hre, s_mul_self, one_mul]
      rw [hsimp, sum_s_pair]
      split_ifs <;> first | tauto | linarith
    · by_cases h23 : j₂ = j₃
      · subst h23
        have hsimp : (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₂) * s (σ j₄)) =
            ∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₄) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          have hre : s (σ j₁) * s (σ j₂) * s (σ j₂) * s (σ j₄) =
              (s (σ j₂) * s (σ j₂)) * (s (σ j₁) * s (σ j₄)) := by ring
          rw [hre, s_mul_self, one_mul]
        rw [hsimp, sum_s_pair]
        split_ifs <;> first | tauto | linarith
      · have hzero : (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₄)) = 0 := by
          by_cases h34 : j₃ = j₄
          · subst h34
            have hsimp : (∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₃)) =
                ∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              rw [mul_assoc (s (σ j₁) * s (σ j₂)), s_mul_self, mul_one]
            rw [hsimp, sum_s_pair]; simp only [h12, ↓reduceIte]
          · refine sum_s_flip_zero j₃
              (fun σ => s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₄)) fun σ => ?_
            rw [Function.update_of_ne h13, Function.update_of_ne h23,
              Function.update_self, Function.update_of_ne (Ne.symm h34), s_not]
            ring
        rw [hzero]
        have ha : (0 : ℤ) ≤ if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ m : ℤ) else 0 := by
          split_ifs <;> linarith
        have hb : (0 : ℤ) ≤ if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ m : ℤ) else 0 := by
          split_ifs <;> linarith
        have hc : (0 : ℤ) ≤ if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ m : ℤ) else 0 := by
          split_ifs <;> linarith
        linarith

private lemma sum_four_block {m : ℕ} (B : Finset (Fin m)) :
    (∑ σ : Fin m → Bool, (∑ j ∈ B, s (σ j)) ^ 4) ≤
      3 * (B.card : ℤ) ^ 2 * (2 ^ m : ℤ) := by
  have hexp :
      (∑ σ : Fin m → Bool, (∑ j ∈ B, s (σ j)) ^ 4) =
        ∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
          ∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₄) := by
    have hterm : ∀ σ : Fin m → Bool,
        (∑ j ∈ B, s (σ j)) ^ 4 =
          ∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
            s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₄) := by
      intro σ
      have hpow4 : (∑ j ∈ B, s (σ j)) ^ 4 =
          (((∑ j ∈ B, s (σ j)) * (∑ j ∈ B, s (σ j))) * (∑ j ∈ B, s (σ j))) *
            (∑ j ∈ B, s (σ j)) := by ring
      rw [hpow4]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
        Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun j₄ _ => by ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₃ _ => Finset.sum_comm
  rw [hexp]
  have hle :
      (∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
        ∑ σ : Fin m → Bool, s (σ j₁) * s (σ j₂) * s (σ j₃) * s (σ j₄)) ≤
      ∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
        ((if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ m : ℤ) else 0) +
         (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ m : ℤ) else 0) +
         (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ m : ℤ) else 0)) :=
    Finset.sum_le_sum fun j₁ _ => Finset.sum_le_sum fun j₂ _ =>
      Finset.sum_le_sum fun j₃ _ => Finset.sum_le_sum fun j₄ _ =>
        sum_s_quad_le j₁ j₂ j₃ j₄
  have h1 :
      (∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
        (if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ m : ℤ) else 0)) =
      (B.card : ℤ) ^ 2 * (2 ^ m : ℤ) := by
    have hsplit : ∀ j₁ j₂ j₃ j₄ : Fin m,
        (if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ m : ℤ) else 0) =
          if j₁ = j₂ then (if j₃ = j₄ then (2 ^ m : ℤ) else 0) else 0 := by
      intro j₁ j₂ j₃ j₄; split_ifs <;> tauto
    simp_rw [hsplit]
    simp [sq]
    ring
  have h2 :
      (∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
        (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ m : ℤ) else 0)) =
      (B.card : ℤ) ^ 2 * (2 ^ m : ℤ) := by
    have hsplit : ∀ j₁ j₂ j₃ j₄ : Fin m,
        (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ m : ℤ) else 0) =
          if j₁ = j₃ then (if j₂ = j₄ then (2 ^ m : ℤ) else 0) else 0 := by
      intro j₁ j₂ j₃ j₄; split_ifs <;> tauto
    simp_rw [hsplit]
    simp [sq]
    ring
  have h3 :
      (∑ j₁ ∈ B, ∑ j₂ ∈ B, ∑ j₃ ∈ B, ∑ j₄ ∈ B,
        (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ m : ℤ) else 0)) =
      (B.card : ℤ) ^ 2 * (2 ^ m : ℤ) := by
    have hsplit : ∀ j₁ j₂ j₃ j₄ : Fin m,
        (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ m : ℤ) else 0) =
          if j₂ = j₃ then (if j₁ = j₄ then (2 ^ m : ℤ) else 0) else 0 := by
      intro j₁ j₂ j₃ j₄; split_ifs <;> tauto
    simp_rw [hsplit]
    simp [sq]
    ring
  simp_rw [Finset.sum_add_distrib] at hle
  linarith

private lemma block_abs_lower {m : ℕ} (B : Finset (Fin m)) (hB : 0 < B.card) :
    (2 ^ m : ℤ) ^ 2 * (B.card : ℤ) ≤
      3 * (∑ σ : Fin m → Bool, |∑ j ∈ B, s (σ j)|) ^ 2 := by
  let y : (Fin m → Bool) → ℤ := fun σ => |∑ j ∈ B, s (σ j)|
  have hy_nn : ∀ σ, 0 ≤ y σ := fun σ => abs_nonneg _
  have hcs := poly_cs_124 y hy_nn
  have hS2 : (∑ σ : Fin m → Bool, y σ ^ 2) = (2 ^ m : ℤ) * (B.card : ℤ) := by
    have hsq : ∀ σ, y σ ^ 2 = (∑ j ∈ B, s (σ j)) ^ 2 := fun σ => sq_abs _
    simp_rw [hsq]
    exact sum_sq_block B
  have hS4 : (∑ σ : Fin m → Bool, y σ ^ 4) ≤ 3 * (B.card : ℤ) ^ 2 * (2 ^ m : ℤ) := by
    have hq : ∀ σ, y σ ^ 4 = (∑ j ∈ B, s (σ j)) ^ 4 := fun σ => by
      have : y σ ^ 4 = (y σ ^ 2) ^ 2 := by ring
      rw [this, sq_abs]; ring
    simp_rw [hq]
    exact sum_four_block B
  have hmul :
      ((2 ^ m : ℤ) * (B.card : ℤ) ^ 2) * ((2 ^ m : ℤ) ^ 2 * (B.card : ℤ)) ≤
        ((2 ^ m : ℤ) * (B.card : ℤ) ^ 2) * (3 * (∑ σ : Fin m → Bool, y σ) ^ 2) := by
    calc
      ((2 ^ m : ℤ) * (B.card : ℤ) ^ 2) * ((2 ^ m : ℤ) ^ 2 * (B.card : ℤ))
          = ((2 ^ m : ℤ) * (B.card : ℤ)) ^ 3 := by ring
      _ = (∑ σ : Fin m → Bool, y σ ^ 2) ^ 3 := by rw [hS2]
      _ ≤ (∑ σ : Fin m → Bool, y σ) ^ 2 * (∑ σ : Fin m → Bool, y σ ^ 4) := hcs
      _ ≤ (∑ σ : Fin m → Bool, y σ) ^ 2 * (3 * (B.card : ℤ) ^ 2 * (2 ^ m : ℤ)) :=
        mul_le_mul_of_nonneg_left hS4 (sq_nonneg _)
      _ = ((2 ^ m : ℤ) * (B.card : ℤ) ^ 2) * (3 * (∑ σ : Fin m → Bool, y σ) ^ 2) := by ring
  have hpos : (0 : ℤ) < (2 ^ m : ℤ) * (B.card : ℤ) ^ 2 := by positivity
  exact le_of_mul_le_mul_left hmul hpos

private lemma lower_bound {N m b : ℕ} (_hN : 0 < N) (hb : 0 < b) (hbm : b ≤ m)
    (f : Fin N → Fin m → Bool) :
    ∃ (enc : Fin N → (Fin b → Bool)) (dec : (Fin b → Bool) → Fin m → Bool),
      b * m * N ^ 2 ≤
        6 * (2 * ((Finset.univ : Finset (Fin N × Fin m)).filter (fun q =>
          dec (enc q.1) q.2 = f q.1 q.2)).card - N * m) ^ 2 := by
  let q : ℕ := m / b
  have hq_pos : 0 < q := Nat.div_pos hbm hb
  have hm_le_2bq : m ≤ 2 * b * q := by
    have hdm : b * q + m % b = m := Nat.div_add_mod m b
    have hrem : m % b < b := Nat.mod_lt m hb
    have hbq : b ≤ b * q := Nat.le_mul_of_pos_right b hq_pos
    have h2 : 2 * b * q = b * q + b * q := by ring
    omega
  let blk : Fin m → Fin b := fun j => ⟨j.val % b, Nat.mod_lt j.val hb⟩
  let B : Fin b → Finset (Fin m) := fun k =>
    (Finset.univ : Finset (Fin m)).filter (fun j => blk j = k)
  have hB_card : ∀ k : Fin b, q ≤ (B k).card := by
    intro k
    let emb : Fin q → Fin m := fun t =>
      ⟨t.val * b + k.val, by
        have ht : t.val + 1 ≤ q := t.isLt
        have hqb : q * b ≤ m := Nat.div_mul_le_self m b
        have hk : k.val < b := k.isLt
        have hmul : (t.val + 1) * b ≤ q * b := Nat.mul_le_mul_right b ht
        rw [Nat.add_mul, one_mul] at hmul
        omega⟩
    have hinj : Function.Injective emb := by
      intro t₁ t₂ h
      have hv : t₁.val * b + k.val = t₂.val * b + k.val := congrArg Fin.val h
      have hmul : t₁.val * b = t₂.val * b := Nat.add_right_cancel hv
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hb hmul)
    have hsub : Finset.univ.image emb ⊆ B k := by
      intro j hj
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only [blk, emb]
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt k.isLt]
    calc
      q = (Finset.univ : Finset (Fin q)).card := by simp
      _ = (Finset.univ.image emb).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (B k).card := Finset.card_le_card hsub
  let T : (Fin m → Bool) → Fin N → Fin b → ℤ :=
    fun σ x k => ∑ j ∈ B k, s (σ j) * s (f x j)
  let encOf : (Fin m → Bool) → Fin N → (Fin b → Bool) :=
    fun σ x k => decide (0 ≤ T σ x k)
  let decOf : (Fin m → Bool) → (Fin b → Bool) → Fin m → Bool :=
    fun σ w j => (w (blk j) == σ j)
  let G : (Fin m → Bool) → ℤ := fun σ =>
    ∑ x : Fin N, ∑ k : Fin b, |T σ x k|
  have hG_eq_sum : ∀ σ : Fin m → Bool,
      G σ = ∑ x : Fin N, ∑ j : Fin m, s (decOf σ (encOf σ x) j) * s (f x j) := by
    intro σ
    refine Finset.sum_congr rfl fun x _ => ?_
    have hfib := (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin m)))
      (t := (Finset.univ : Finset (Fin b)))
      (g := blk)
      (f := fun j => s (decOf σ (encOf σ x) j) * s (f x j))
      (fun _ _ => Finset.mem_univ _)).symm
    rw [hfib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm : ∀ j ∈ B k,
        s (decOf σ (encOf σ x) j) * s (f x j) =
          s (encOf σ x k) * (s (σ j) * s (f x j)) := by
      intro j hj
      have hjk : blk j = k := (Finset.mem_filter.mp hj).2
      simp only [decOf, hjk, s_beq]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    change |T σ x k| = s (decide (0 ≤ T σ x k)) * T σ x k
    by_cases hnonneg : 0 ≤ T σ x k
    · simp [hnonneg, s, abs_of_nonneg hnonneg]
    · replace hnonneg : T σ x k < 0 := lt_of_not_ge hnonneg
      simp [not_le.mpr hnonneg, s, abs_of_neg hnonneg]
  let E : Fin b → ℤ := fun k => ∑ σ : Fin m → Bool, |∑ j ∈ B k, s (σ j)|
  have hsum_T_eq_E : ∀ (x : Fin N) (k : Fin b),
      (∑ σ : Fin m → Bool, |T σ x k|) = E k := by
    intro x k
    let φ : (Fin m → Bool) → (Fin m → Bool) := fun σ j => (σ j == f x j)
    have hinv : Function.Involutive φ := by
      intro σ; funext j; dsimp only [φ]; cases σ j <;> cases f x j <;> rfl
    have hstep : ∀ σ : Fin m → Bool, T σ x k = ∑ j ∈ B k, s (φ σ j) := by
      intro σ
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (s_beq (σ j) (f x j)).symm
    simp_rw [hstep]
    exact Fintype.sum_equiv (Equiv.mk φ φ hinv hinv) _ _ (fun _ => rfl)
  have hsum_G : (∑ σ : Fin m → Bool, G σ) = (N : ℤ) * ∑ k : Fin b, E k := by
    calc
      (∑ σ : Fin m → Bool, G σ)
          = ∑ x : Fin N, ∑ σ : Fin m → Bool, ∑ k : Fin b, |T σ x k| := Finset.sum_comm
      _ = ∑ x : Fin N, ∑ k : Fin b, ∑ σ : Fin m → Bool, |T σ x k| :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ _x : Fin N, ∑ k : Fin b, E k :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => hsum_T_eq_E x k
      _ = (N : ℤ) * ∑ k : Fin b, E k := by
        simp [Finset.sum_const]
  have hE_lower : ∀ k : Fin b, (2 ^ m : ℤ) ^ 2 * (q : ℤ) ≤ 3 * E k ^ 2 := by
    intro k
    have hBk_pos : 0 < (B k).card := lt_of_lt_of_le hq_pos (hB_card k)
    have h1 := block_abs_lower (B k) hBk_pos
    have h2 : (2 ^ m : ℤ) ^ 2 * (q : ℤ) ≤ (2 ^ m : ℤ) ^ 2 * ((B k).card : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hB_card k) (sq_nonneg _)
    exact h2.trans h1
  have hb_ne : (Finset.univ : Finset (Fin b)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hb⟩⟩
  obtain ⟨kmin, _, hkmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin b)) E hb_ne
  have hEmin_nn : 0 ≤ E kmin := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsumE_ge : (b : ℤ) * E kmin ≤ ∑ k : Fin b, E k := by
    calc
      (b : ℤ) * E kmin = ∑ _k : Fin b, E kmin := by simp [Finset.sum_const]
      _ ≤ ∑ k : Fin b, E k := Finset.sum_le_sum fun k _ => hkmin k (Finset.mem_univ k)
  have hsumE_sq : (b : ℤ) * (m : ℤ) * (2 ^ m : ℤ) ^ 2 ≤ 6 * (∑ k : Fin b, E k) ^ 2 := by
    have hsq : ((b : ℤ) * E kmin) ^ 2 ≤ (∑ k : Fin b, E k) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg b) hEmin_nn) hsumE_ge 2
    have h2bq : (m : ℤ) ≤ 2 * (b : ℤ) * (q : ℤ) := by exact_mod_cast hm_le_2bq
    have hstep1 :
        (b : ℤ) * (m : ℤ) * (2 ^ m : ℤ) ^ 2 ≤
          2 * (b : ℤ) ^ 2 * ((2 ^ m : ℤ) ^ 2 * (q : ℤ)) := by
      have hmul := mul_le_mul_of_nonneg_left h2bq (mul_nonneg (Nat.cast_nonneg b) (sq_nonneg (2 ^ m : ℤ)))
      linarith
    have hstep2 :
        2 * (b : ℤ) ^ 2 * ((2 ^ m : ℤ) ^ 2 * (q : ℤ)) ≤
          2 * (b : ℤ) ^ 2 * (3 * E kmin ^ 2) :=
      mul_le_mul_of_nonneg_left (hE_lower kmin) (by positivity)
    have hstep3 : 2 * (b : ℤ) ^ 2 * (3 * E kmin ^ 2) = 6 * ((b : ℤ) * E kmin) ^ 2 := by ring
    linarith
  have hσ_ne : (Finset.univ : Finset (Fin m → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨σmax, _, hσmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m → Bool)) G hσ_ne
  have hGmax_ge : (N : ℤ) * ∑ k : Fin b, E k ≤ (2 ^ m : ℤ) * G σmax := by
    calc
      (N : ℤ) * ∑ k : Fin b, E k = ∑ σ : Fin m → Bool, G σ := hsum_G.symm
      _ ≤ ∑ _σ : Fin m → Bool, G σmax :=
        Finset.sum_le_sum fun σ _ => hσmax σ (Finset.mem_univ σ)
      _ = (2 ^ m : ℤ) * G σmax := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast; rfl
  have hsumE_nn : 0 ≤ ∑ k : Fin b, E k :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hGmax_nn : 0 ≤ G σmax :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hGmax_sq : (b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2 ≤ 6 * (G σmax) ^ 2 := by
    have hsq : ((N : ℤ) * ∑ k : Fin b, E k) ^ 2 ≤ ((2 ^ m : ℤ) * G σmax) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg N) hsumE_nn) hGmax_ge 2
    have hmul :
        (2 ^ m : ℤ) ^ 2 * ((b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2) ≤
          (2 ^ m : ℤ) ^ 2 * (6 * (G σmax) ^ 2) := by
      calc
        (2 ^ m : ℤ) ^ 2 * ((b : ℤ) * (m : ℤ) * (N : ℤ) ^ 2)
            = (N : ℤ) ^ 2 * ((b : ℤ) * (m : ℤ) * (2 ^ m : ℤ) ^ 2) := by ring
        _ ≤ (N : ℤ) ^ 2 * (6 * (∑ k : Fin b, E k) ^ 2) :=
          mul_le_mul_of_nonneg_left hsumE_sq (sq_nonneg _)
        _ = 6 * ((N : ℤ) * ∑ k : Fin b, E k) ^ 2 := by ring
        _ ≤ 6 * ((2 ^ m : ℤ) * G σmax) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = (2 ^ m : ℤ) ^ 2 * (6 * (G σmax) ^ 2) := by ring
    have hpos : (0 : ℤ) < (2 ^ m : ℤ) ^ 2 := by positivity
    exact le_of_mul_le_mul_left hmul hpos
  refine ⟨encOf σmax, decOf σmax, ?_⟩
  set hits := ((Finset.univ : Finset (Fin N × Fin m)).filter (fun q =>
    decOf σmax (encOf σmax q.1) q.2 = f q.1 q.2)).card
  have hG_hits : G σmax = 2 * (hits : ℤ) - ((N * m : ℕ) : ℤ) := by
    rw [hG_eq_sum σmax]
    exact sum_prod_s_eq_gain_int f (encOf σmax) (decOf σmax)
  have hle_hits : N * m ≤ 2 * hits := by
    have hz : ((N * m : ℕ) : ℤ) ≤ ((2 * hits : ℕ) : ℤ) := by
      push_cast at hG_hits ⊢; linarith
    exact_mod_cast hz
  have hG_nat : ((2 * hits - N * m : ℕ) : ℤ) = G σmax := by
    rw [Nat.cast_sub hle_hits, hG_hits]
    push_cast; ring
  have hz_final : ((b * m * N ^ 2 : ℕ) : ℤ) ≤ ((6 * (2 * hits - N * m) ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [hG_nat]
    exact hGmax_sq
  exact_mod_cast hz_final

end PEqualNP.Outside.L_lib_799

theorem PEqualNP.Outside.L_lib_799 :
    ∀ (N m b : ℕ), 0 < N → 0 < b → b ≤ m →
  ∀ f : Fin N → Fin m → Bool,
    (∀ S : Finset (Fin m), S.card ≤ 2*b → ∀ u : Fin m → Bool,
      2^S.card * ((Finset.univ : Finset (Fin N)).filter (fun x =>
        ∀ j ∈ S, f x j = u j)).card = N) →
    let W := Fin b → Bool
    let gain := fun (enc : Fin N → W) (dec : W → Fin m → Bool) =>
      2*((Finset.univ : Finset (Fin N × Fin m)).filter (fun q =>
        dec (enc q.1) q.2 = f q.1 q.2)).card - N*m
    (∀ enc dec, (gain enc dec)^2 ≤ 4*b*m*N^2) ∧
    (∃ enc dec, b*m*N^2 ≤ 6*(gain enc dec)^2) := by
  intro N m b hN hb hbm f hInd
  exact ⟨fun enc dec => PEqualNP.Outside.L_lib_799.upper_bound hN hb hbm f hInd enc dec,
    PEqualNP.Outside.L_lib_799.lower_bound hN hb hbm f⟩
