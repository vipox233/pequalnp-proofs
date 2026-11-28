import PEqualNP.Defs


namespace PEqualNP.Outside.L_gct_295

theorem sumdiv' {ι : Type*} (s : Finset ι) (f : ι → ℂ) (a : ℂ) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

private def delta {α : Type*} [DecidableEq α] (x y : α) : ℂ :=
  if x = y then 1 else 0

private lemma inj4_ind {α : Type*} [DecidableEq α] (a b c d : α) :
    (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) =
      (1 - delta a b - delta a c - delta a d - delta b c - delta b d - delta c d) +
      (delta a b * delta c d + delta a c * delta b d + delta a d * delta b c) +
      2 * (delta a b * delta a c + delta a b * delta a d + delta a c * delta a d + delta b c * delta b d) -
      6 * (delta a b * delta a c * delta a d) := by
  unfold delta
  by_cases hab : a = b
  · subst hab
    by_cases hac : a = c
    · subst hac
      by_cases had : a = d
      · subst had; simp; norm_num
      · simp [had]; norm_num
    · by_cases had : a = d
      · subst had; simp [hac]; norm_num
      · by_cases hcd : c = d
        · subst hcd; simp [hac]
        · simp [hac, had, hcd]
  · by_cases hac : a = c
    · subst hac
      by_cases had : a = d
      · subst had; simp [hab, Ne.symm hab]; norm_num
      · by_cases hbd : b = d
        · subst hbd; simp [hab, Ne.symm hab]
        · simp [hab, had, hbd, Ne.symm hab]
    · by_cases had : a = d
      · subst had
        by_cases hbc : b = c
        · subst hbc; simp [hab, Ne.symm hab]
        · simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac]
      · by_cases hbc : b = c
        · subst hbc
          by_cases hbd : b = d
          · subst hbd; simp [hab]; norm_num
          · simp [hab, had, hbd]
        · by_cases hbd : b = d
          · subst hbd; simp [hab, hac, hbc, Ne.symm hbc]
          · by_cases hcd : c = d
            · subst hcd; simp [hab, hac, hbc]
            · simp [hab, hac, had, hbc, hbd, hcd]

private lemma injective_vec4_iff {α : Type*} (a b c d : α) :
    Function.Injective ![a, b, c, d] ↔
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 1) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 2) (a₂ := 3) e) (by decide)
  · rintro ⟨hab, hac, had, hbc, hbd, hcd⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private lemma sum_emb_fin4_eq_ind {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ) :
    ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) * F a b c d := by
  let e1 : { f : Fin 4 → α // Function.Injective f } ≃ (Fin 4 ↪ α) :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (Fin 4 → α) ≃ α × α × α × α :=
    { toFun := fun f => (f 0, f 1, f 2, f 3)
      invFun := fun ⟨a, b, c, d⟩ => ![a, b, c, d]
      left_inv := fun f => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  have h1 : ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) := by
    exact (Fintype.sum_equiv e1 _ _ (fun _ => rfl)).symm
  have h2 : ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) =
      ∑ f : Fin 4 → α, if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun f _ => f.1) ?_ ?_ ?_ ?_
    · intro f _; simp [f.2]
    · intro f₁ _ f₂ _ h; exact Subtype.ext h
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact ⟨⟨f, hf⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have h3 : ∑ f : Fin 4 → α, (if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0) =
      ∑ x : α × α × α × α,
        if Function.Injective ![x.1, x.2.1, x.2.2.1, x.2.2.2] then
          F x.1 x.2.1 x.2.2.1 x.2.2.2
        else 0 := by
    exact Fintype.sum_equiv e2 _ _ (fun f => by
      have hf : ![f 0, f 1, f 2, f 3] = f := e2.left_inv f
      simp [e2, hf])
  rw [h1, h2, h3]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [injective_vec4_iff]
  split_ifs <;> simp

private lemma sum_emb_fin4_of_zero_marginals {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ)
    (h0 : ∀ b c d, ∑ a, F a b c d = 0)
    (h1 : ∀ a c d, ∑ b, F a b c d = 0)
    (h2 : ∀ a b d, ∑ c, F a b c d = 0)
    (h3 : ∀ a b c, ∑ d, F a b c d = 0) :
    ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      (∑ x, ∑ y, F x x y y) + (∑ x, ∑ y, F x y x y) + (∑ x, ∑ y, F x y y x) -
      6 * ∑ x, F x x x x := by
  have hsum_a : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g b c d * F a b c d = 0 := by
    intro g
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.mul_sum, h0, mul_zero]
  have hsum_b : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g a c d * F a b c d = 0 := by
    intro g
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.mul_sum, h1, mul_zero]
  have hsum_c : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g a b d * F a b c d = 0 := by
    intro g
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.mul_sum, h2, mul_zero]
  have hsum_d : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g a b c * F a b c d = 0 := by
    intro g
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.mul_sum, h3, mul_zero]
  have hgrp1 : ∑ a, ∑ b, ∑ c, ∑ d,
      (1 - delta a b - delta a c - delta a d - delta b c - delta b d - delta c d) * F a b c d = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hsum_a (fun _ _ _ => 1),
        hsum_c (fun a b _ => delta a b),
        hsum_b (fun a c _ => delta a c),
        hsum_b (fun a _ d => delta a d),
        hsum_a (fun b c _ => delta b c),
        hsum_a (fun b _ d => delta b d),
        hsum_a (fun _ c d => delta c d)]
    ring
  have hgrp3 : ∑ a, ∑ b, ∑ c, ∑ d,
      (2 * (delta a b * delta a c + delta a b * delta a d + delta a c * delta a d + delta b c * delta b d)) *
        F a b c d = 0 := by
    have hmul : ∀ a b c d,
        (2 * (delta a b * delta a c + delta a b * delta a d + delta a c * delta a d + delta b c * delta b d)) *
          F a b c d =
        (2 * (delta a b * delta a c)) * F a b c d +
        (2 * (delta a b * delta a d)) * F a b c d +
        (2 * (delta a c * delta a d)) * F a b c d +
        (2 * (delta b c * delta b d)) * F a b c d := fun _ _ _ _ => by ring
    simp only [hmul, Finset.sum_add_distrib]
    rw [hsum_d (fun a b c => 2 * (delta a b * delta a c)),
        hsum_c (fun a b d => 2 * (delta a b * delta a d)),
        hsum_b (fun a c d => 2 * (delta a c * delta a d)),
        hsum_a (fun b c d => 2 * (delta b c * delta b d))]
    ring
  have hdelta_sum : ∀ (x : α) (f : α → ℂ), ∑ y : α, delta x y * f y = f x := by
    intro x f
    simp only [delta, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hp1 : ∑ a, ∑ b, ∑ c, ∑ d, (delta a b * delta c d) * F a b c d = ∑ x, ∑ y, F x x y y := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have h : ∀ b, ∑ c, ∑ d, (delta a b * delta c d) * F a b c d =
        delta a b * ∑ c, ∑ d, delta c d * F a b c d := by
      intro b; simp only [mul_assoc, ← Finset.mul_sum]
    simp only [h, hdelta_sum]
  have hp2 : ∑ a, ∑ b, ∑ c, ∑ d, (delta a c * delta b d) * F a b c d = ∑ x, ∑ y, F x y x y := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h : ∀ c, ∑ d, (delta a c * delta b d) * F a b c d =
        delta a c * ∑ d, delta b d * F a b c d := by
      intro c; simp only [mul_assoc, ← Finset.mul_sum]
    simp only [h, hdelta_sum]
  have hp3 : ∑ a, ∑ b, ∑ c, ∑ d, (delta a d * delta b c) * F a b c d = ∑ x, ∑ y, F x y y x := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h : ∀ c, ∑ d, (delta a d * delta b c) * F a b c d =
        delta b c * ∑ d, delta a d * F a b c d := by
      intro c
      have hcomm : ∀ d, (delta a d * delta b c) * F a b c d =
          delta b c * (delta a d * F a b c d) := fun _ => by ring
      simp only [hcomm, ← Finset.mul_sum]
    simp only [h, hdelta_sum]
  have hgrp2 : ∑ a, ∑ b, ∑ c, ∑ d,
      (delta a b * delta c d + delta a c * delta b d + delta a d * delta b c) * F a b c d =
      (∑ x, ∑ y, F x x y y) + (∑ x, ∑ y, F x y x y) + (∑ x, ∑ y, F x y y x) := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hp1, hp2, hp3]
  have hgrp4 : ∑ a, ∑ b, ∑ c, ∑ d,
      (6 * (delta a b * delta a c * delta a d)) * F a b c d = 6 * ∑ x, F x x x x := by
    have hmul : ∀ a b c d,
        (6 * (delta a b * delta a c * delta a d)) * F a b c d =
        6 * (delta a b * (delta a c * (delta a d * F a b c d))) := fun _ _ _ _ => by ring
    simp only [hmul, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hdelta_sum]
  have hsplit : ∀ (A B C D : α → α → α → α → ℂ),
      ∑ a, ∑ b, ∑ c, ∑ d, (A a b c d + B a b c d + C a b c d - D a b c d) * F a b c d =
        (∑ a, ∑ b, ∑ c, ∑ d, A a b c d * F a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d, B a b c d * F a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d, C a b c d * F a b c d) -
        (∑ a, ∑ b, ∑ c, ∑ d, D a b c d * F a b c d) := by
    intro A B C D
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_emb_fin4_eq_ind]
  simp_rw [inj4_ind]
  rw [hsplit]
  rw [hgrp1, hgrp2, hgrp3, hgrp4]
  ring

lemma quartic {q : ℕ} (x y : Fin q → ℂ) (hx : ∑ j, x j = 0) (hy : ∑ j, y j = 0) :
    ∑ f : Fin 4 ↪ Fin q, x (f 0) * x (f 1) * y (f 2) * y (f 3) =
      (∑ j, x j * x j) * (∑ j, y j * y j) + 2 * (∑ j, x j * y j) ^ 2
        - 6 * ∑ j, x j ^ 2 * y j ^ 2 := by
  have h := sum_emb_fin4_of_zero_marginals (fun a b c d => x a * x b * y c * y d)
    (fun b c d => by simp only [mul_assoc, ← Finset.sum_mul, hx, zero_mul])
    (fun a c d => by
      have : ∀ b, x a * x b * y c * y d = x b * (x a * y c * y d) := fun b => by ring
      simp only [this, ← Finset.sum_mul, hx, zero_mul])
    (fun a b d => by
      have : ∀ c, x a * x b * y c * y d = y c * (x a * x b * y d) := fun c => by ring
      simp only [this, ← Finset.sum_mul, hy, zero_mul])
    (fun a b c => by simp only [← Finset.mul_sum, hy, mul_zero])
  rw [h]
  have e1 : ∑ a, ∑ b, x a * x a * y b * y b = (∑ j, x j * x j) * (∑ j, y j * y j) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∑ a, ∑ b, x a * x b * y a * y b = (∑ j, x j * y j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e3 : ∑ a, ∑ b, x a * x b * y b * y a = (∑ j, x j * y j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e4 : ∑ a, x a * x a * y a * y a = ∑ j, x j ^ 2 * y j ^ 2 :=
    Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2, e3, e4]; ring

noncomputable def G {q : ℕ} (x y : Fin q → ℂ) (s t : ℂ) : ℂ :=
  ∑ f : Fin 4 ↪ Fin q,
    (1 + s * x (f 0)) * (1 - s * x (f 1)) * (1 + t * y (f 2)) * (1 - t * y (f 3))

lemma G_eq {q : ℕ} (K H : Submodule ℂ (Fin q → ℂ))
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x y : Fin q → ℂ) (hx : x ∈ K) (hy : y ∈ H) (s t : ℂ) :
    G x y s t = (Fintype.card (Fin 4 ↪ Fin q) : ℂ) := by
  have h := hyp (s • x) (K.smul_mem s hx) (t • y) (H.smul_mem t hy)
  simp only [Fin.prod_univ_four] at h
  rw [← h]
  unfold G
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [sub_eq_add_neg]

lemma mixed_zero {q : ℕ} (K H : Submodule ℂ (Fin q → ℂ))
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x y : Fin q → ℂ) (hx : x ∈ K) (hy : y ∈ H) :
    ∑ f : Fin 4 ↪ Fin q, x (f 0) * x (f 1) * y (f 2) * y (f 3) = 0 := by
  have e : 4 * ∑ f : Fin 4 ↪ Fin q, x (f 0) * x (f 1) * y (f 2) * y (f 3) =
      (G x y 2 2 - 2 * G x y 2 1 + G x y 2 0) - 2 * (G x y 1 2 - 2 * G x y 1 1 + G x y 1 0)
        + (G x y 0 2 - 2 * G x y 0 1 + G x y 0 0) := by
    simp only [G, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  simp only [G_eq K H hyp x y hx hy] at e
  have e' : 4 * ∑ f : Fin 4 ↪ Fin q, x (f 0) * x (f 1) * y (f 2) * y (f 3) = 0 := by
    rw [e]; ring
  simpa using e'

lemma quartic_identity {q : ℕ} (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x y : Fin q → ℂ) (hx : x ∈ K) (hy : y ∈ H) :
    (∑ j, x j * x j) * (∑ j, y j * y j) + 2 * (∑ j, x j * y j) ^ 2
        - 6 * ∑ j, x j ^ 2 * y j ^ 2 = 0 := by
  rw [← quartic x y (hK x hx) (hH y hy)]
  exact mixed_zero K H hyp x y hx hy

lemma cnt3 {q : ℕ} (a b c : Fin q) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ d : Fin q, (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0)
      = (q : ℂ) - 3 := by
  have h : ∀ d : Fin q,
      (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) =
        1 - (if a = d then 1 else 0) - (if b = d then 1 else 0) - (if c = d then 1 else 0) := by
    intro d
    by_cases h1 : a = d
    · subst h1; simp [hab, hac, Ne.symm hab, Ne.symm hac]
    by_cases h2 : b = d
    · subst h2; simp [hbc, Ne.symm hbc, h1]
    by_cases h3 : c = d
    · subst h3; simp [h1, h2]
    simp [h1, h2, h3, hab, hac, hbc]
  simp_rw [h]
  simp [Finset.sum_sub_distrib]
  ring

lemma cnt2 {q : ℕ} (a b : Fin q) (hab : a ≠ b) :
    ∑ c : Fin q, ∑ d : Fin q,
      (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0)
      = ((q : ℂ) - 2) * ((q : ℂ) - 3) := by
  have h : ∀ c : Fin q, ∑ d : Fin q,
      (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) =
        ((q : ℂ) - 3) * (1 - (if a = c then 1 else 0) - (if b = c then 1 else 0)) := by
    intro c
    by_cases h1 : a = c
    · subst h1; simp [hab, Ne.symm hab]
    by_cases h2 : b = c
    · subst h2; simp [h1]
    rw [cnt3 a b c hab h1 h2]; simp [h1, h2]
  simp_rw [h]
  rw [← Finset.mul_sum]
  simp [Finset.sum_sub_distrib]
  ring

lemma pair_sum {q : ℕ} (x : Fin q → ℂ) (hx : ∑ j, x j = 0) :
    ∑ f : Fin 4 ↪ Fin q, x (f 0) * x (f 1) =
      -(((q : ℂ) - 2) * ((q : ℂ) - 3)) * ∑ j, x j * x j := by
  rw [sum_emb_fin4_eq_ind (fun a b _ _ => x a * x b)]
  have h : ∀ a b : Fin q, ∑ c : Fin q, ∑ d : Fin q,
      (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) * (x a * x b) =
      ((q : ℂ) - 2) * ((q : ℂ) - 3) * (x a * x b) -
        (if a = b then ((q : ℂ) - 2) * ((q : ℂ) - 3) * (x a * x b) else 0) := by
    intro a b
    simp_rw [← Finset.sum_mul]
    by_cases hab : a = b
    · subst hab; simp
    · rw [cnt2 a b hab]; simp [hab]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have z : ∑ a : Fin q, ∑ b : Fin q, ((q : ℂ) - 2) * ((q : ℂ) - 3) * (x a * x b) = 0 := by
    simp [← Finset.mul_sum, hx]
  rw [z, ← Finset.mul_sum]
  ring

lemma xx_zero {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x : Fin q → ℂ) (hx : x ∈ K) : ∑ j, x j * x j = 0 := by
  have e : 2 * ∑ f : Fin 4 ↪ Fin q, x (f 0) * x (f 1) =
      -(G x 0 2 0 - 2 * G x 0 1 0 + G x 0 0 0) := by
    simp only [G, Pi.zero_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  simp only [G_eq K H hyp x 0 hx H.zero_mem] at e
  rw [pair_sum x (hK x hx)] at e
  have h2 : (q : ℂ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : q ≠ 2))
  have h3 : (q : ℂ) - 3 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : q ≠ 3))
  have e' : ((q : ℂ) - 2) * (((q : ℂ) - 3) * ∑ j, x j * x j) = 0 := by linear_combination (-1/2 : ℂ) * e
  rcases mul_eq_zero.mp e' with h | h
  · exact absurd h h2
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h h3
  · exact h

lemma pair_sum' {q : ℕ} (y : Fin q → ℂ) (hy : ∑ j, y j = 0) :
    ∑ f : Fin 4 ↪ Fin q, y (f 2) * y (f 3) =
      -(((q : ℂ) - 2) * ((q : ℂ) - 3)) * ∑ j, y j * y j := by
  rw [← pair_sum y hy]
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  have h2 : σ.symm 0 = 2 := by decide
  have h3 : σ.symm 1 = 3 := by decide
  rw [← Equiv.sum_comp (Equiv.embeddingCongr σ (Equiv.refl (Fin q)))
    (fun f : Fin 4 ↪ Fin q => y (f 0) * y (f 1))]
  refine Finset.sum_congr rfl fun f _ => ?_
  show y (f 2) * y (f 3) = y (f (σ.symm 0)) * y (f (σ.symm 1))
  rw [h2, h3]

lemma yy_zero {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (y : Fin q → ℂ) (hy : y ∈ H) : ∑ j, y j * y j = 0 := by
  have e : 2 * ∑ f : Fin 4 ↪ Fin q, y (f 2) * y (f 3) =
      -(G 0 y 0 2 - 2 * G 0 y 0 1 + G 0 y 0 0) := by
    simp only [G, Pi.zero_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  simp only [G_eq K H hyp 0 y K.zero_mem hy] at e
  rw [pair_sum' y (hH y hy)] at e
  have h2 : (q : ℂ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : q ≠ 2))
  have h3 : (q : ℂ) - 3 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : q ≠ 3))
  have e' : ((q : ℂ) - 2) * (((q : ℂ) - 3) * ∑ j, y j * y j) = 0 := by linear_combination (-1/2 : ℂ) * e
  rcases mul_eq_zero.mp e' with h | h
  · exact absurd h h2
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h h3
  · exact h

lemma sq_identity {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x y : Fin q → ℂ) (hx : x ∈ K) (hy : y ∈ H) :
    3 * ∑ j, x j ^ 2 * y j ^ 2 = (∑ j, x j * y j) ^ 2 := by
  have h := quartic_identity K H hK hH hyp x y hx hy
  rw [xx_zero hq K H hK hyp x hx] at h
  linear_combination (-1/2 : ℂ) * h

lemma polarA {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x x' y : Fin q → ℂ) (hx : x ∈ K) (hx' : x' ∈ K) (hy : y ∈ H) :
    3 * ∑ j, x j * x' j * y j ^ 2 = (∑ j, x j * y j) * (∑ j, x' j * y j) := by
  have h1 := sq_identity hq K H hK hH hyp (x + x') y (K.add_mem hx hx') hy
  have h2 := sq_identity hq K H hK hH hyp x y hx hy
  have h3 := sq_identity hq K H hK hH hyp x' y hx' hy
  simp only [Pi.add_apply] at h1
  have eQ : ∑ j, (x j + x' j) ^ 2 * y j ^ 2 = ∑ j, x j ^ 2 * y j ^ 2 + ∑ j, x' j ^ 2 * y j ^ 2
      + 2 * ∑ j, x j * x' j * y j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have eL : ∑ j, (x j + x' j) * y j = ∑ j, x j * y j + ∑ j, x' j * y j := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [eQ, eL] at h1
  linear_combination (1/2 : ℂ) * h1 - (1/2 : ℂ) * h2 - (1/2 : ℂ) * h3

lemma polar {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x x' y y' : Fin q → ℂ) (hx : x ∈ K) (hx' : x' ∈ K) (hy : y ∈ H) (hy' : y' ∈ H) :
    6 * ∑ j, x j * x' j * (y j * y' j) =
      (∑ j, x j * y j) * (∑ j, x' j * y' j) + (∑ j, x j * y' j) * (∑ j, x' j * y j) := by
  have g1 := polarA hq K H hK hH hyp x x' (y + y') hx hx' (H.add_mem hy hy')
  have g2 := polarA hq K H hK hH hyp x x' y hx hx' hy
  have g3 := polarA hq K H hK hH hyp x x' y' hx hx' hy'
  simp only [Pi.add_apply] at g1
  have eQ : ∑ j, x j * x' j * (y j + y' j) ^ 2 = ∑ j, x j * x' j * y j ^ 2
      + ∑ j, x j * x' j * y' j ^ 2 + 2 * ∑ j, x j * x' j * (y j * y' j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have eL : ∀ u : Fin q → ℂ, ∑ j, u j * (y j + y' j) = ∑ j, u j * y j + ∑ j, u j * y' j := by
    intro u
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [eQ, eL x, eL x'] at g1
  linear_combination g1 - g2 - g3

lemma prod_indep {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    {r : ℕ} (xs ys : Fin r → Fin q → ℂ) (hxs : ∀ i, xs i ∈ K) (hys : ∀ i, ys i ∈ H)
    (hdual : ∀ i j, ∑ k, xs i k * ys j k = if i = j then (1 : ℂ) else 0) :
    LinearIndependent ℂ
      (fun p : Fin r × Fin r => (fun k => xs p.1 k * ys p.2 k : Fin q → ℂ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hk : ∀ k, ∑ p : Fin r × Fin r, c p * (xs p.1 k * ys p.2 k) = 0 := by
    intro k
    have := congrFun hc k
    simpa [Finset.sum_apply] using this
  have key : ∀ a b : Fin r, (if a = b then ∑ i, c (i, i) else 0) + c (b, a) = 0 := by
    intro a b
    have h0 : ∑ k, (∑ p : Fin r × Fin r, c p * (xs p.1 k * ys p.2 k)) * (xs a k * ys b k) = 0 := by
      simp [hk]
    simp_rw [Finset.sum_mul] at h0
    rw [Finset.sum_comm] at h0
    have hp : ∀ p : Fin r × Fin r,
        ∑ k, c p * (xs p.1 k * ys p.2 k) * (xs a k * ys b k) =
        c p * (((if p.1 = p.2 then (1 : ℂ) else 0) * (if a = b then (1 : ℂ) else 0)
          + (if p.1 = b then (1 : ℂ) else 0) * (if a = p.2 then (1 : ℂ) else 0)) / 6) := by
      intro p
      have h := polar hq K H hK hH hyp (xs p.1) (xs a) (ys p.2) (ys b)
        (hxs _) (hxs _) (hys _) (hys _)
      simp only [hdual] at h
      have e : ∑ k, c p * (xs p.1 k * ys p.2 k) * (xs a k * ys b k) =
          c p * ∑ k, xs p.1 k * xs a k * (ys p.2 k * ys b k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]; linear_combination (c p / 6) * h
    simp_rw [hp] at h0
    have s1 : ∑ p : Fin r × Fin r, c p * (if p.1 = p.2 then (1 : ℂ) else 0) = ∑ i, c (i, i) := by
      rw [Fintype.sum_prod_type]; simp
    have s2 : ∑ p : Fin r × Fin r,
        c p * ((if p.1 = b then (1 : ℂ) else 0) * (if a = p.2 then (1 : ℂ) else 0)) = c (b, a) := by
      rw [Fintype.sum_prod_type]; simp
    have s3 : ∑ p : Fin r × Fin r,
        c p * (((if p.1 = p.2 then (1 : ℂ) else 0) * (if a = b then (1 : ℂ) else 0)
          + (if p.1 = b then (1 : ℂ) else 0) * (if a = p.2 then (1 : ℂ) else 0)) / 6) =
        ((∑ p : Fin r × Fin r, c p * (if p.1 = p.2 then (1 : ℂ) else 0)) *
            (if a = b then (1 : ℂ) else 0)
          + ∑ p : Fin r × Fin r,
            c p * ((if p.1 = b then (1 : ℂ) else 0) * (if a = p.2 then (1 : ℂ) else 0))) / 6 := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, sumdiv']
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [s3, s1, s2] at h0
    split_ifs at h0 ⊢ <;> linear_combination 6 * h0
  have htr : ∑ i, c (i, i) = 0 := by
    have hs : ∑ a : Fin r, ((∑ i, c (i, i)) + c (a, a)) = 0 :=
      Finset.sum_eq_zero fun a _ => by simpa using key a a
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
    have h1 : ((r : ℂ) + 1) * ∑ i, c (i, i) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (Nat.cast_add_one_ne_zero r)
    · exact h
  rintro ⟨a, b⟩
  have := key b a
  rw [htr] at this
  simpa using this

lemma exists_dual_fam {q : ℕ} (K H A : Submodule ℂ (Fin q → ℂ))
    (hA : ∀ x, x ∈ A ↔ x ∈ K ∧ ∀ y ∈ H, (∑ j, x j * y j) = 0) :
    ∃ xs ys : Fin (Module.finrank ℂ K - Module.finrank ℂ A) → Fin q → ℂ,
      (∀ i, xs i ∈ K) ∧ (∀ i, ys i ∈ H) ∧
      (∀ i j, ∑ k, xs i k * ys j k = if i = j then (1 : ℂ) else 0) ∧
      ∀ x ∈ K, ∀ y ∈ H, ∑ k, x k * y k =
        ∑ i, (∑ k, x k * ys i k) * (∑ k, xs i k * y k) := by
  classical
  let Φ : K →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun x y => ∑ k, x.1 k * y.1 k
      map_add' := fun x x' => by funext y; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by funext y; simp [Finset.mul_sum, mul_assoc] }
  have hker : Module.finrank ℂ (LinearMap.ker Φ) = Module.finrank ℂ A := by
    have hAK : A ≤ K := fun x hx => ((hA x).1 hx).1
    have : LinearMap.ker Φ = Submodule.comap K.subtype A := by
      ext x
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hA]
      constructor
      · intro h; exact ⟨x.2, fun y hy => congrFun h ⟨y, hy⟩⟩
      · intro h; funext y; exact h.2 y.1 y.2
    rw [this]; exact (Submodule.comapSubtypeEquivOfLe hAK).finrank_eq
  have hr : Module.finrank ℂ (LinearMap.range Φ) =
      Module.finrank ℂ K - Module.finrank ℂ A := by
    have := LinearMap.finrank_range_add_finrank_ker Φ; omega
  let b := Module.finBasisOfFinrankEq ℂ (LinearMap.range Φ) hr
  have hx : ∀ i, ∃ x : K, Φ x = (b i : H → ℂ) := fun i => (b i).2
  choose xs hxs using hx
  have hli : LinearIndependent ℂ (fun i => (b i : H → ℂ)) :=
    b.linearIndependent.map' (LinearMap.range Φ).subtype (Submodule.ker_subtype _)
  have hspan := (span_flip_eq_top_iff_linearIndependent).2 hli
  let ψ : H →ₗ[ℂ] (Fin (Module.finrank ℂ K - Module.finrank ℂ A) → ℂ) :=
    { toFun := fun y i => ∑ k, (xs i).1 k * y.1 k
      map_add' := fun y y' => by funext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by funext i; simp [Finset.mul_sum, mul_left_comm] }
  have hpt : ∀ (y : H) i, (b i : H → ℂ) y = ψ y i := by
    intro y i; rw [← hxs i]; rfl
  have hset : Set.range (flip fun i => (b i : H → ℂ)) = (LinearMap.range ψ : Set _) := by
    ext v
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, funext fun i => (hpt y i).symm⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, funext fun i => hpt y i⟩
  rw [hset, Submodule.span_eq] at hspan
  have hy : ∀ j, ∃ y : H, ψ y = Pi.single j 1 := fun j => by
    have : Pi.single j (1 : ℂ) ∈ LinearMap.range ψ := hspan ▸ Submodule.mem_top
    exact this
  choose ys hys using hy
  refine ⟨fun i => (xs i).1, fun j => (ys j).1, fun i => (xs i).2, fun j => (ys j).2,
    fun i j => ?_, fun x hx y hy => ?_⟩
  · have := congrFun (hys j) i
    rw [Pi.single_apply] at this
    exact this
  · have hdual' : ∀ i j, (b i : H → ℂ) (ys j) = if i = j then (1 : ℂ) else 0 := by
      intro i j
      rw [hpt]
      have := congrFun (hys j) i
      rw [Pi.single_apply] at this
      exact this
    let v : LinearMap.range Φ := ⟨Φ ⟨x, hx⟩, LinearMap.mem_range_self Φ _⟩
    have hrep := b.sum_repr v
    have hval : ∀ y' : H, ∑ k, x k * y'.1 k = ∑ i, (b.repr v i) * (b i : H → ℂ) y' := by
      intro y'
      have := congrFun (congrArg Subtype.val hrep) y'
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    have hc : ∀ j, b.repr v j = ∑ k, x k * (ys j).1 k := by
      intro j
      rw [hval (ys j)]
      simp [hdual']
    rw [hval ⟨y, hy⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, hpt]
    rfl

lemma count_lemma {q : ℕ} (N S' : Submodule ℂ (Fin q → ℂ))
    (h : ∀ z ∈ N, ∀ w ∈ S', ∑ j, z j * w j = 0) :
    Module.finrank ℂ N + Module.finrank ℂ S' ≤ q := by
  classical
  let θ : (Fin q → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin q → ℂ) :=
    { toFun := fun w =>
        { toFun := fun z => ∑ j, z j * w j
          map_add' := fun z z' => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun c z => by simp [Finset.mul_sum, mul_assoc] }
      map_add' := fun w w' => by
        refine LinearMap.ext fun z => ?_
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        refine LinearMap.ext fun z => ?_
        simp [Finset.mul_sum, mul_left_comm] }
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    funext j
    have := LinearMap.congr_fun hw (Pi.single j 1)
    simpa [θ, Pi.single_apply] using this
  have hle : S'.map θ ≤ N.dualAnnihilator := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h z hz w hw
  have h1 := (Submodule.equivMapOfInjective θ hinj S').finrank_eq
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq N
  have h3 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h2
  omega

lemma kk_zero {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    (x x' : Fin q → ℂ) (hx : x ∈ K) (hx' : x' ∈ K) : ∑ j, x j * x' j = 0 := by
  have h1 := xx_zero hq K H hK hyp (x + x') (K.add_mem hx hx')
  have h2 := xx_zero hq K H hK hyp x hx
  have h3 := xx_zero hq K H hK hyp x' hx'
  simp only [Pi.add_apply] at h1
  have eQ : ∑ j, (x j + x' j) * (x j + x' j) = ∑ j, x j * x j + ∑ j, x' j * x' j
      + 2 * ∑ j, x j * x' j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [eQ] at h1
  linear_combination (1/2 : ℂ) * h1 - (1/2 : ℂ) * h2 - (1/2 : ℂ) * h3

lemma isotropy_bound {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) :
    2 * Module.finrank ℂ K + 1 ≤ q := by
  have hone : (fun _ => 1 : Fin q → ℂ) ∉ K := fun h => by
    have := hK _ h
    simp at this
    omega
  have hmem : (fun _ => 1 : Fin q → ℂ) ∈ K ⊔ Submodule.span ℂ {(fun _ => 1 : Fin q → ℂ)} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hlt : K < K ⊔ Submodule.span ℂ {(fun _ => 1 : Fin q → ℂ)} :=
    lt_of_le_of_ne le_sup_left fun heq => hone ((le_of_eq heq.symm) hmem)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := count_lemma K (K ⊔ Submodule.span ℂ {(fun _ => 1 : Fin q → ℂ)}) (by
    intro z hz w hw
    obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, mul_add,
      Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [kk_zero hq K H hK hyp z k hz hk, hK z hz]
    simp)
  omega

lemma genA {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    {r : ℕ} (xs ys : Fin r → Fin q → ℂ) (hxs : ∀ i, xs i ∈ K) (hys : ∀ i, ys i ∈ H)
    (hd : ∀ i j, ∑ k, xs i k * ys j k = if i = j then (1 : ℂ) else 0)
    (hfac : ∀ x ∈ K, ∀ y ∈ H, ∑ k, x k * y k =
        ∑ i, (∑ k, x k * ys i k) * (∑ k, xs i k * y k))
    (x x' y y' : Fin q → ℂ) (hx : x ∈ K) (hx' : x' ∈ K) (hy : y ∈ H) (hy' : y' ∈ H) :
    ∑ k, (x' k * y' k) * (x k * y k) =
      ∑ i, ∑ j, (∑ k, x k * ys i k) * (∑ k, xs j k * y k) *
        ∑ k, (x' k * y' k) * (xs i k * ys j k) := by
  have p0 := polar hq K H hK hH hyp x' x y' y hx' hx hy' hy
  have e1 : ∑ k, (x' k * y' k) * (x k * y k) = ∑ k, x' k * x k * (y' k * y k) :=
    Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ i j, ∑ k, (x' k * y' k) * (xs i k * ys j k) =
      ((∑ k, x' k * y' k) * (if i = j then (1 : ℂ) else 0)
        + (∑ k, x' k * ys j k) * (∑ k, xs i k * y' k)) / 6 := by
    intro i j
    have h := polar hq K H hK hH hyp x' (xs i) y' (ys j) hx' (hxs i) hy' (hys j)
    rw [hd] at h
    have e : ∑ k, (x' k * y' k) * (xs i k * ys j k) = ∑ k, x' k * xs i k * (y' k * ys j k) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e]; linear_combination h / 6
  have f1 := hfac x hx y hy
  have f2 := hfac x hx y' hy'
  have f3 := hfac x' hx' y hy
  have t1 : ∑ i : Fin r, ∑ j : Fin r,
      (if i = j then (∑ k, x k * ys i k) * (∑ k, xs j k * y k) else 0) =
      ∑ i, (∑ k, x k * ys i k) * (∑ k, xs i k * y k) := by simp
  have t2 := Finset.sum_mul_sum (Finset.univ : Finset (Fin r)) (Finset.univ : Finset (Fin r))
    (fun i => (∑ k, x k * ys i k) * (∑ k, xs i k * y' k))
    (fun j => (∑ k, x' k * ys j k) * (∑ k, xs j k * y k))
  have e3 : ∑ i, ∑ j, (∑ k, x k * ys i k) * (∑ k, xs j k * y k) *
        (((∑ k, x' k * y' k) * (if i = j then (1 : ℂ) else 0)
          + (∑ k, x' k * ys j k) * (∑ k, xs i k * y' k)) / 6) =
      ((∑ k, x' k * y' k) * ∑ i : Fin r, ∑ j : Fin r,
          (if i = j then (∑ k, x k * ys i k) * (∑ k, xs j k * y k) else 0)
        + ∑ i, ∑ j, ((∑ k, x k * ys i k) * (∑ k, xs i k * y' k)) *
            ((∑ k, x' k * ys j k) * (∑ k, xs j k * y k))) / 6 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, sumdiv']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, sumdiv']
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  simp_rw [e2]
  rw [e1, e3, t1, ← t2, ← f1, ← f2, ← f3]
  linear_combination p0 / 6

lemma genB {q : ℕ} (hq : 4 ≤ q) (K H : Submodule ℂ (Fin q → ℂ))
    (hK : ∀ x ∈ K, (∑ j, x j) = 0) (hH : ∀ y ∈ H, (∑ j, y j) = 0)
    (hyp : ∀ x ∈ K, ∀ y ∈ H,
      let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ))
    {r : ℕ} (xs ys : Fin r → Fin q → ℂ) (hxs : ∀ i, xs i ∈ K) (hys : ∀ i, ys i ∈ H)
    (hd : ∀ i j, ∑ k, xs i k * ys j k = if i = j then (1 : ℂ) else 0)
    (hfac : ∀ x ∈ K, ∀ y ∈ H, ∑ k, x k * y k =
        ∑ i, (∑ k, x k * ys i k) * (∑ k, xs i k * y k))
    (x' y' : Fin q → ℂ) (hx' : x' ∈ K) (hy' : y' ∈ H) :
    ((r : ℂ) + 1) * ∑ k, x' k * y' k =
      6 * ∑ i, ∑ k, (x' k * y' k) * (xs i k * ys i k) := by
  have e2 : ∀ i, 6 * ∑ k, (x' k * y' k) * (xs i k * ys i k) =
      (∑ k, x' k * y' k) + (∑ k, x' k * ys i k) * (∑ k, xs i k * y' k) := by
    intro i
    have h := polar hq K H hK hH hyp x' (xs i) y' (ys i) hx' (hxs i) hy' (hys i)
    simp only [hd, ite_true] at h
    have e : ∑ k, (x' k * y' k) * (xs i k * ys i k) = ∑ k, x' k * xs i k * (y' k * ys i k) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e]; linear_combination h
  have e3 : 6 * ∑ i, ∑ k, (x' k * y' k) * (xs i k * ys i k) =
      ∑ i : Fin r, ((∑ k, x' k * y' k) + (∑ k, x' k * ys i k) * (∑ k, xs i k * y' k)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => e2 i
  rw [e3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hfac x' hx' y' hy']
  ring

lemma span_ext_lin {q : ℕ} (s : Set (Fin q → ℂ)) (f g : (Fin q → ℂ) → ℂ)
    (fadd : ∀ u v, f (u + v) = f u + f v) (fsmul : ∀ (c : ℂ) u, f (c • u) = c * f u)
    (gadd : ∀ u v, g (u + v) = g u + g v) (gsmul : ∀ (c : ℂ) u, g (c • u) = c * g u)
    (h : ∀ z ∈ s, f z = g z) : ∀ z ∈ Submodule.span ℂ s, f z = g z := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero =>
    have h1 := fsmul 0 0
    have h2 := gsmul 0 0
    rw [zero_smul, zero_mul] at h1 h2
    rw [h1, h2]
  | add u v _ _ hu hv => rw [fadd, gadd, hu, hv]
  | smul c u _ hu => rw [fsmul, gsmul, hu]

end PEqualNP.Outside.L_gct_295

theorem PEqualNP.Outside.L_gct_295 : ∀ (q : ℕ), 4 ≤ q → ∀ (K H A : Submodule ℂ (Fin q → ℂ)),
  (∀ x ∈ K, (∑ j, x j) = 0) →
  (∀ y ∈ H, (∑ j, y j) = 0) →
  (∀ x, x ∈ A ↔ x ∈ K ∧ ∀ y ∈ H, (∑ j, x j * y j) = 0) →
  (∀ x ∈ K, ∀ y ∈ H,
    let rows : Fin 4 → Fin q → ℂ := ![x, -x, y, -y]
    (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
      (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) →
  let r := Module.finrank ℂ K - Module.finrank ℂ A
  let S := Submodule.span ℂ
    {z : Fin q → ℂ | ∃ x ∈ K, ∃ y ∈ H, z = fun j => x j * y j}
  r ^ 2 ≤ Module.finrank ℂ S ∧
    2 * Module.finrank ℂ S + 1 ≤ q + r ^ 2 := by
  intro q hq K H A hK hH hA hyp r S
  refine ⟨?_, ?_⟩
  · obtain ⟨xs, ys, hxs, hys, hd, -⟩ := PEqualNP.Outside.L_gct_295.exists_dual_fam K H A hA
    have li := PEqualNP.Outside.L_gct_295.prod_indep hq K H hK hH hyp xs ys hxs hys hd
    have h1 := finrank_span_eq_card li
    have h2 : Submodule.span ℂ (Set.range
        (fun p : Fin r × Fin r => (fun k => xs p.1 k * ys p.2 k : Fin q → ℂ))) ≤ S :=
      Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨xs p.1, hxs _, ys p.2, hys _, rfl⟩)
    have h3 := Submodule.finrank_mono h2
    rw [h1] at h3
    simpa [sq] using h3
  · obtain ⟨xs, ys, hxs, hys, hd, hfac⟩ :=
      PEqualNP.Outside.L_gct_295.exists_dual_fam K H A hA
    have hS1 : ∀ z ∈ S, ∀ x ∈ K, ∀ y ∈ H, ∑ k, z k * (x k * y k) =
        ∑ i, ∑ j, (∑ k, x k * ys i k) * (∑ k, xs j k * y k) *
          ∑ k, z k * (xs i k * ys j k) := by
      intro z hz x hx y hy
      refine PEqualNP.Outside.L_gct_295.span_ext_lin _
        (fun z => ∑ k, z k * (x k * y k))
        (fun z => ∑ i, ∑ j, (∑ k, x k * ys i k) * (∑ k, xs j k * y k) *
          ∑ k, z k * (xs i k * ys j k)) ?_ ?_ ?_ ?_ ?_ z hz
      · intro u v; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      · intro c u
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · intro u v; simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
      · intro c u
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring
      · rintro _ ⟨x', hx', y', hy', rfl⟩
        exact PEqualNP.Outside.L_gct_295.genA hq K H hK hH hyp xs ys hxs hys hd hfac
          x x' y y' hx hx' hy hy'
    have hS2 : ∀ z ∈ S, ((r : ℂ) + 1) * ∑ k, z k =
        6 * ∑ i, ∑ k, z k * (xs i k * ys i k) := by
      intro z hz
      refine PEqualNP.Outside.L_gct_295.span_ext_lin _
        (fun z => ((r : ℂ) + 1) * ∑ k, z k)
        (fun z => 6 * ∑ i, ∑ k, z k * (xs i k * ys i k)) ?_ ?_ ?_ ?_ ?_ z hz
      · intro u v; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      · intro c u
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · intro u v; simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
      · intro c u
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      · rintro _ ⟨x', hx', y', hy', rfl⟩
        exact PEqualNP.Outside.L_gct_295.genB hq K H hK hH hyp xs ys hxs hys hd hfac
          x' y' hx' hy'
    let T : (Fin q → ℂ) →ₗ[ℂ] (Fin r × Fin r → ℂ) :=
      { toFun := fun z p => ∑ k, z k * (xs p.1 k * ys p.2 k)
        map_add' := fun u v => by funext p; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c u => by funext p; simp [Finset.mul_sum, mul_assoc] }
    let N : Submodule ℂ (Fin q → ℂ) := (LinearMap.ker (T.domRestrict S)).map S.subtype
    have hN : ∀ z ∈ N, z ∈ S ∧ ∀ i j, ∑ k, z k * (xs i k * ys j k) = 0 := by
      rintro _ ⟨z', hz', rfl⟩
      exact ⟨z'.2, fun i j => congrFun (LinearMap.mem_ker.1 hz') (i, j)⟩
    have hone : (fun _ => 1 : Fin q → ℂ) ∉ S := by
      intro h1
      have h := hS2 _ h1
      have h' : ((r : ℂ) + 1) * q = 6 * r := by simpa [hd] using h
      have h'' : (r + 1) * q = 6 * r := by exact_mod_cast h'
      have hb := PEqualNP.Outside.L_gct_295.isotropy_bound hq K H hK hyp
      have hr : r ≤ Module.finrank ℂ K := Nat.sub_le _ _
      have a1 : (r + 1) * 4 ≤ (r + 1) * q := Nat.mul_le_mul_left _ hq
      have a2 : (r + 1) * (2 * r + 1) ≤ (r + 1) * q := Nat.mul_le_mul_left _ (by omega)
      nlinarith [a1, a2, h'']
    have hmem : (fun _ => 1 : Fin q → ℂ) ∈ S ⊔ Submodule.span ℂ {(fun _ => 1 : Fin q → ℂ)} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hlt : S < S ⊔ Submodule.span ℂ {(fun _ => 1 : Fin q → ℂ)} :=
      lt_of_le_of_ne le_sup_left fun heq => hone ((le_of_eq heq.symm) hmem)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := PEqualNP.Outside.L_gct_295.count_lemma N
      (S ⊔ Submodule.span ℂ {(fun _ => 1 : Fin q → ℂ)}) (by
      intro z hz w hw
      obtain ⟨hzS, hz0⟩ := hN z hz
      obtain ⟨s, hs, m, hm, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
      have hzs : ∑ k, z k * s k = 0 := by
        refine PEqualNP.Outside.L_gct_295.span_ext_lin _
          (fun s => ∑ k, z k * s k) (fun _ => 0) ?_ ?_ ?_ ?_ ?_ s hs
        · intro u v; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        · intro c u
          simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        · intro u v; simp
        · intro c u; simp
        · rintro _ ⟨x, hx, y, hy, rfl⟩
          show ∑ k, z k * (x k * y k) = 0
          rw [hS1 z hzS x hx y hy]
          simp [hz0]
      have hz1 : ∑ k, z k = 0 := by
        have h := hS2 z hzS
        simp only [hz0, Finset.sum_const_zero, mul_zero] at h
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h (Nat.cast_add_one_ne_zero r)
        · exact h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, mul_add,
        Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hzs, hz1]
      simp)
    have k1 := LinearMap.finrank_range_add_finrank_ker (T.domRestrict S)
    have k2 : Module.finrank ℂ (LinearMap.range (T.domRestrict S)) ≤ r ^ 2 := by
      have := Submodule.finrank_le (LinearMap.range (T.domRestrict S))
      simpa [Module.finrank_fintype_fun_eq_card, sq] using this
    have k3 := (Submodule.equivMapOfInjective S.subtype S.injective_subtype
      (LinearMap.ker (T.domRestrict S))).finrank_eq
    show 2 * Module.finrank ℂ S + 1 ≤ q + r ^ 2
    have k3' : Module.finrank ℂ (LinearMap.ker (T.domRestrict S)) = Module.finrank ℂ N := k3
    linarith [h1, h2, k1, k2, k3']
