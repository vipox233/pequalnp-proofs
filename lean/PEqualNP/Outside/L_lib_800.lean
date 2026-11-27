import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_800_aux

open scoped BigOperators

def char {r : ℕ} (χ a : Fin r → ZMod 2) : ℚ :=
  ∏ i : Fin r, if χ i = 1 ∧ a i = 1 then (-1 : ℚ) else 1

lemma zmod2_char_mul (c x y : ZMod 2) :
    (if c = 1 ∧ x + y = 1 then (-1 : ℚ) else 1) =
    (if c = 1 ∧ x = 1 then (-1 : ℚ) else 1) * (if c = 1 ∧ y = 1 then (-1 : ℚ) else 1) := by
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases h2 c with rfl | rfl <;> rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl <;>
    simp [h11, h01]

lemma char_add {r : ℕ} (χ a b : Fin r → ZMod 2) :
    char χ (a + b) = char χ a * char χ b := by
  dsimp only [char]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact zmod2_char_mul (χ i) (a i) (b i)

lemma char_comm {r : ℕ} (χ a : Fin r → ZMod 2) : char χ a = char a χ := by
  dsimp only [char]
  apply Finset.prod_congr rfl
  intro i _
  simp only [and_comm]

lemma char_zero_right {r : ℕ} (χ : Fin r → ZMod 2) : char χ 0 = 1 := by
  dsimp only [char]
  apply Finset.prod_eq_one
  intro i _
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [h01]

lemma char_zero_left {r : ℕ} (a : Fin r → ZMod 2) : char 0 a = 1 := by
  rw [char_comm, char_zero_right]

lemma char_list_sum {r : ℕ} (χ : Fin r → ZMod 2) (w : List (Fin r → ZMod 2)) :
    char χ w.sum = (w.map (char χ)).prod := by
  induction w with
  | nil => simp [char_zero_right]
  | cons h t ih => simp [char_add, ih]

lemma zmod2_add_self {r : ℕ} (a : Fin r → ZMod 2) : a + a = 0 := by
  funext i
  change a i + a i = 0
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  exact h (a i)

lemma char_mul_self {r : ℕ} (χ a : Fin r → ZMod 2) : char χ a * char χ a = 1 := by
  rw [← char_add, zmod2_add_self, char_zero_right]

lemma sum_char_right {r : ℕ} (χ : Fin r → ZMod 2) :
    (∑ a : Fin r → ZMod 2, char χ a) = if χ = 0 then ((2 ^ r : ℕ) : ℚ) else 0 := by
  by_cases h0 : χ = 0
  · subst h0
    simp only [ite_true, char_zero_left, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one]
  · simp only [h0, ite_false]
    have hex : ∃ i₀ : Fin r, χ i₀ = 1 := by
      by_contra hall
      push_neg at hall
      apply h0
      funext i
      have hi := hall i
      have h2 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact h2 (χ i) hi
    rcases hex with ⟨i₀, hi₀⟩
    let δ : Fin r → ZMod 2 := fun i => if i = i₀ then 1 else 0
    have hcharδ : char χ δ = -1 := by
      dsimp only [char, δ]
      rw [Finset.prod_eq_single i₀]
      · simp [hi₀]
      · intro i _ hne
        simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ i₀) hnot
    have hneg : (∑ a : Fin r → ZMod 2, char χ a) = -(∑ a : Fin r → ZMod 2, char χ a) := by
      calc (∑ a : Fin r → ZMod 2, char χ a)
          = ∑ a : Fin r → ZMod 2, char χ (a + δ) := by
            refine Finset.sum_bij (fun a _ => a + δ) (fun _ _ => Finset.mem_univ _)
              (fun a1 _ a2 _ heq => by
                have := congrArg (· + δ) heq
                simpa [add_assoc, zmod2_add_self] using this)
              (fun b _ => ⟨b + δ, Finset.mem_univ _, by simp [add_assoc, zmod2_add_self]⟩)
              (fun a _ => by simp [add_assoc, zmod2_add_self])
        _ = ∑ a : Fin r → ZMod 2, -(char χ a) := by
            apply Finset.sum_congr rfl; intro a _
            rw [char_add, hcharδ, mul_neg_one]
        _ = -(∑ a : Fin r → ZMod 2, char χ a) := Finset.sum_neg_distrib _
    linarith

lemma sum_char_left {r : ℕ} (a : Fin r → ZMod 2) :
    (∑ χ : Fin r → ZMod 2, char χ a) = if a = 0 then ((2 ^ r : ℕ) : ℚ) else 0 := by
  have h : (∑ χ : Fin r → ZMod 2, char χ a) = ∑ χ : Fin r → ZMod 2, char a χ :=
    Finset.sum_congr rfl (fun χ _ => char_comm χ a)
  rw [h, sum_char_right]

def vecE {r : ℕ} : Option (Fin r → ZMod 2) → ℚ := fun x => x.elim 1 (fun _ => 0)

def vecV {r : ℕ} (ψ : Fin r → ZMod 2) : Option (Fin r → ZMod 2) → ℚ :=
  fun x => x.elim 0 (fun a => char ψ a)

def rankOne {α : Type*} (u w : α → ℚ) : Matrix α α ℚ := fun i j => u i * w j

lemma rankOne_mul_rankOne {α : Type*} [Fintype α] (u₁ w₁ u₂ w₂ : α → ℚ) :
    rankOne u₁ w₁ * rankOne u₂ w₂ = (∑ x : α, w₁ x * u₂ x) • rankOne u₁ w₂ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, rankOne, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _; ring

lemma dot_EE {r : ℕ} : (∑ x : Option (Fin r → ZMod 2), vecE x * vecE x) = 1 := by
  rw [Fintype.sum_option]
  simp [vecE]

lemma dot_EV {r : ℕ} (ψ : Fin r → ZMod 2) :
    (∑ x : Option (Fin r → ZMod 2), vecE x * vecV ψ x) = 0 := by
  rw [Fintype.sum_option]
  simp [vecE, vecV]

lemma dot_VE {r : ℕ} (ψ : Fin r → ZMod 2) :
    (∑ x : Option (Fin r → ZMod 2), vecV ψ x * vecE x) = 0 := by
  rw [Fintype.sum_option]
  simp [vecE, vecV]

lemma dot_VV {r : ℕ} (ψ χ : Fin r → ZMod 2) :
    (∑ x : Option (Fin r → ZMod 2), vecV ψ x * vecV χ x) =
    if ψ = χ then ((2 ^ r : ℕ) : ℚ) else 0 := by
  rw [Fintype.sum_option]
  simp only [vecV, Option.elim_none, mul_zero, zero_add, Option.elim_some]
  have h1 : ∀ a : Fin r → ZMod 2, char ψ a * char χ a = char (ψ + χ) a := fun a => by
    rw [char_comm ψ, char_comm χ, ← char_add, char_comm]
  simp_rw [h1]
  rw [sum_char_right]
  have hiff : ψ + χ = 0 ↔ ψ = χ := by
    constructor
    · intro h
      have := congrArg (· + χ) h
      simpa [add_assoc, zmod2_add_self] using this
    · rintro rfl; exact zmod2_add_self ψ
  by_cases heq : ψ = χ
  · subst heq; simp [zmod2_add_self]
  · have hne : ψ + χ ≠ 0 := fun h => heq (hiff.mp h)
    simp [heq, hne]

def Tmat {r : ℕ} (z : ℚ) (h : Fin r → ZMod 2) :
    Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ :=
  let f := fun a : Fin r → ZMod 2 => if a = 0 then z - 1 else -1
  fun before after =>
    before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
      (fun a => after.elim (f a) (fun b => if b = a + h then 1 else 0))

def Ptilde {r : ℕ} (h : Fin r → ZMod 2) :
    Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ :=
  fun before after =>
    before.elim (after.elim 1 (fun _ => 0))
      (fun a => after.elim 0 (fun b => if b = a + h then 1 else 0))

lemma Tmat_eq_T0_mul_Ptilde {r : ℕ} (z : ℚ) (h : Fin r → ZMod 2) :
    Tmat z h = Tmat z 0 * Ptilde h := by
  ext before after
  rw [Matrix.mul_apply, Fintype.sum_option]
  cases before with
  | none =>
    cases after with
    | none => simp [Tmat, Ptilde]
    | some b =>
      simp only [Tmat, Ptilde, Option.elim_none, Option.elim_some, mul_zero, zero_add]
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  | some a =>
    cases after with
    | none => simp [Tmat, Ptilde]
    | some b =>
      simp only [Tmat, Ptilde, Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma T0_cubic {r : ℕ} (z : ℚ) :
    Tmat z 0 * Tmat z 0 * Tmat z 0 - (3 : ℚ) • (Tmat z 0 * Tmat z 0) + (4 - z) • Tmat z 0 =
    (2 - z) • (1 : Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ) := by
  let X := Tmat (r := r) z 0
  let D := X - 1
  have hD_nn : D none none = 0 := by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply_eq]; simp [Tmat]
  have hD_ns : ∀ b, D none (some b) = if b = 0 then 1 else 0 := fun b => by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply_ne (by simp)]; simp [Tmat]
  have hD_sn : ∀ a, D (some a) none = if a = 0 then z - 1 else -1 := fun a => by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply_ne (by simp)]; simp [Tmat]
  have hD_ss : ∀ a b, D (some a) (some b) = 0 := fun a b => by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply]
    simp only [Tmat, Option.elim_some, add_zero, Option.some.injEq]
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := Ne.symm h
      simp [h, h']
  have hD2_nn : (D * D) none none = z - 1 := by
    rw [Matrix.mul_apply, Fintype.sum_option, hD_nn, zero_mul, zero_add]
    simp_rw [hD_ns, hD_sn]
    rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
    · simp
    · intro a _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  have hD2_ns : ∀ b, (D * D) none (some b) = 0 := fun b => by
    rw [Matrix.mul_apply, Fintype.sum_option, hD_nn, zero_mul, zero_add]
    simp_rw [hD_ss, mul_zero, Finset.sum_const_zero]
  have hD2_sn : ∀ a, (D * D) (some a) none = 0 := fun a => by
    rw [Matrix.mul_apply, Fintype.sum_option, hD_nn, mul_zero, zero_add]
    simp_rw [hD_ss, zero_mul, Finset.sum_const_zero]
  have hD2_ss : ∀ a b, (D * D) (some a) (some b) = (if a = 0 then z - 1 else -1) * (if b = 0 then 1 else 0) :=
    fun a b => by
      rw [Matrix.mul_apply, Fintype.sum_option, hD_sn, hD_ns]
      simp_rw [hD_ss, zero_mul, Finset.sum_const_zero, add_zero]
  have hD3 : D * D * D = (z - 1) • D := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.smul_apply, smul_eq_mul]
    cases i with
    | none =>
      cases j with
      | none =>
        rw [hD2_nn, hD_nn, mul_zero, zero_add]
        simp_rw [hD2_ns]; simp
      | some b =>
        rw [hD2_nn, hD_ns]
        simp_rw [hD2_ns]; simp
    | some a =>
      cases j with
      | none =>
        rw [hD2_sn, zero_mul, zero_add, hD_sn]
        simp_rw [hD2_ss, hD_sn]
        rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
        · simp [mul_comm]
        · intro x _ hne; simp [hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      | some b =>
        rw [hD2_sn, zero_mul, zero_add, hD_ss, mul_zero]
        simp_rw [hD_ss]; simp
  have hX : X = D + 1 := by simp [D]
  change X * X * X - (3 : ℚ) • (X * X) + (4 - z) • X = (2 - z) • 1
  rw [hX]
  have hexp : ((D + 1) * (D + 1) * (D + 1) - (3 : ℚ) • ((D + 1) * (D + 1)) + (4 - z) • (D + 1)) =
      (D * D * D - (z - 1) • D) + (2 - z) • 1 := by
    simp only [mul_add, add_mul, one_mul, mul_one, smul_add, sub_smul, one_smul]
    ext p q
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hexp, hD3, sub_self, zero_add]

def Qmat {r : ℕ} (ψ : Fin r → ZMod 2) :
    Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ :=
  ((2 ^ r : ℕ) : ℚ)⁻¹ • ∑ h : Fin r → ZMod 2, char ψ h • Ptilde h

lemma Qmat_ne_zero {r : ℕ} (ψ : Fin r → ZMod 2) (hψ : ψ ≠ 0) :
    Qmat ψ = ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne (vecV ψ) (vecV ψ) := by
  ext before after
  simp only [Qmat, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne]
  congr 1
  cases before with
  | none =>
    cases after with
    | none =>
      simp only [Ptilde, Option.elim_none, mul_one, vecV, zero_mul]
      rw [sum_char_right, if_neg hψ]
    | some b =>
      simp [Ptilde, vecV]
  | some a =>
    cases after with
    | none =>
      simp [Ptilde, vecV]
    | some b =>
      simp only [Ptilde, Option.elim_some, vecV]
      rw [Finset.sum_eq_single (a + b)]
      · have heq : b = a + (a + b) := by rw [← add_assoc, zmod2_add_self, zero_add]
        rw [if_pos heq, mul_one, char_add]
      · intro h _ hne
        have hne' : b ≠ a + h := by
          intro hb; apply hne
          have h1 := congrArg (a + ·) hb
          rw [← add_assoc, zmod2_add_self, zero_add] at h1
          exact h1.symm
        rw [if_neg hne', mul_zero]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma Qmat_zero {r : ℕ} :
    Qmat (0 : Fin r → ZMod 2) =
    rankOne vecE vecE + ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne (vecV 0) (vecV 0) := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext before after
  simp only [Qmat, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne]
  cases before with
  | none =>
    cases after with
    | none =>
      simp only [Ptilde, Option.elim_none, mul_one, vecE, vecV, mul_zero, add_zero, char_zero_left]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul,
        mul_one, inv_mul_cancel₀ hq0]
    | some b =>
      simp [Ptilde, vecE, vecV]
  | some a =>
    cases after with
    | none =>
      simp [Ptilde, vecE, vecV]
    | some b =>
      simp only [Ptilde, Option.elim_some, vecE, vecV, zero_mul, zero_add, char_zero_left, one_mul]
      congr 1
      rw [Finset.sum_eq_single (a + b)]
      · have heq : b = a + (a + b) := by rw [← add_assoc, zmod2_add_self, zero_add]
        rw [if_pos heq]
      · intro h _ hne
        have hne' : b ≠ a + h := by
          intro hb; apply hne
          have h1 := congrArg (a + ·) hb
          rw [← add_assoc, zmod2_add_self, zero_add] at h1
          exact h1.symm
        rw [if_neg hne']
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma Q0_mul_T0_mul_Qpsi {r : ℕ} (z : ℚ) (ψ : Fin r → ZMod 2) (hψ : ψ ≠ 0) :
    Qmat 0 * Tmat z 0 * Qmat ψ = ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV ψ) := by
  rw [Qmat_zero, Qmat_ne_zero ψ hψ]
  have hT_eq : Tmat z 0 * rankOne (vecV ψ) (vecV ψ) =
      rankOne vecE (vecV ψ) + rankOne (vecV ψ) (vecV ψ) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.add_apply]
    cases x with
    | none =>
      simp only [Tmat, rankOne, vecV, vecE, Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero, one_mul]
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp [char_zero_right]
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    | some a =>
      simp only [Tmat, rankOne, vecV, vecE, Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [Matrix.mul_assoc, Matrix.mul_smul, hT_eq, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne,
    dot_EE, dot_EV, dot_VE, dot_VV, if_neg hψ.symm]
  simp

lemma Qpsi_mul_T0_mul_Q0 {r : ℕ} (z : ℚ) (ψ : Fin r → ZMod 2) (hψ : ψ ≠ 0) :
    Qmat ψ * Tmat z 0 * Qmat 0 = (z * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV ψ) vecE := by
  rw [Qmat_zero, Qmat_ne_zero ψ hψ]
  have hv_T : rankOne (vecV ψ) (vecV ψ) * Tmat z 0 =
      z • rankOne (vecV ψ) vecE + rankOne (vecV ψ) (vecV ψ) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rankOne, vecV, vecE, Tmat]
    cases y with
    | none =>
      simp only [Option.elim_none, Option.elim_some, mul_zero, zero_add, mul_one, add_zero]
      have hsum : (∑ a : Fin r → ZMod 2, char ψ a * (if a = 0 then z - 1 else -1)) = z := by
        have hrew : ∀ a : Fin r → ZMod 2,
            char ψ a * (if a = 0 then z - 1 else -1) = (if a = 0 then z else 0) - char ψ a := fun a => by
          by_cases ha : a = 0
          · subst ha; simp [char_zero_right]
          · simp [ha]
        simp_rw [hrew, Finset.sum_sub_distrib, sum_char_right, if_neg hψ, sub_zero]
        rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
        · simp
        · intro a _ hne; simp [hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      cases x with
      | none => simp
      | some a =>
        simp only [Option.elim_some]
        have hfac : (∑ b : Fin r → ZMod 2, char ψ a * char ψ b * (if b = 0 then z - 1 else -1)) =
            char ψ a * ∑ b : Fin r → ZMod 2, char ψ b * (if b = 0 then z - 1 else -1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
        rw [hfac, hsum]; ring
    | some b =>
      simp only [Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single b]
      · simp
      · intro a _ hne; have : b ≠ a := Ne.symm hne; simp [this]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [Matrix.smul_mul, hv_T, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne,
    dot_EE, dot_EV, dot_VE, dot_VV, if_neg hψ]
  simp only [one_smul, zero_smul, smul_zero, add_zero, zero_add, smul_smul, mul_comm]

lemma Enn_mul_T0_mul_Q0 {r : ℕ} (z : ℚ) :
    rankOne (vecE (r := r)) vecE * Tmat z 0 * Qmat 0 =
    rankOne (vecE (r := r)) vecE + ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV 0) := by
  rw [Qmat_zero]
  have he_T : rankOne (vecE (r := r)) vecE * Tmat z 0 =
      Matrix.of (fun x y => vecE x * (y.elim 1 (fun b => if b = 0 then 1 else 0))) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.of_apply]
    cases y with
    | none => simp [rankOne, vecE, Tmat]
    | some b => simp [rankOne, vecE, Tmat]
  have h1 : rankOne (vecE (r := r)) vecE * Tmat z 0 * rankOne vecE vecE = rankOne vecE vecE := by
    ext x y
    rw [he_T, Matrix.mul_apply, Fintype.sum_option]
    simp [rankOne, vecE]
  have h2 : rankOne (vecE (r := r)) vecE * Tmat z 0 * rankOne (vecV 0) (vecV 0) = rankOne vecE (vecV 0) := by
    ext x y
    rw [he_T, Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.of_apply, rankOne, vecV, Option.elim_none, mul_zero, zero_add, Option.elim_some]
    rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
    · simp [char_zero_left]
    · intro b _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [Matrix.mul_add, Matrix.mul_smul, h1, h2]

lemma Q0_mul_T0_mul_Enn {r : ℕ} (z : ℚ) :
    Qmat (r := r) 0 * Tmat z 0 * rankOne vecE vecE =
    rankOne (vecE (r := r)) vecE + ((z - ((2 ^ r : ℕ) : ℚ)) * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV 0) vecE := by
  rw [Qmat_zero]
  have hT_e : Tmat (r := r) z 0 * rankOne vecE vecE =
      Matrix.of (fun x y => (x.elim 1 (fun a => if a = 0 then z - 1 else -1)) * vecE y) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.of_apply]
    cases x with
    | none => simp [rankOne, vecE, Tmat]
    | some a => simp [rankOne, vecE, Tmat]
  have h1 : rankOne (vecE (r := r)) vecE * (Tmat z 0 * rankOne vecE vecE) = rankOne vecE vecE := by
    ext x y
    rw [hT_e, Matrix.mul_apply, Fintype.sum_option]
    simp [rankOne, vecE]
  have h2 : rankOne (vecV (r := r) 0) (vecV 0) * (Tmat z 0 * rankOne vecE vecE) =
      (z - ((2 ^ r : ℕ) : ℚ)) • rankOne (vecV 0) vecE := by
    ext x y
    rw [hT_e, Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.of_apply, rankOne, vecV, Option.elim_none, mul_zero, zero_add, Option.elim_some,
      Matrix.smul_apply, smul_eq_mul, char_zero_left, one_mul]
    have hsum : (∑ a : Fin r → ZMod 2, (if a = 0 then z - 1 else -1 : ℚ)) = z - ((2 ^ r : ℕ) : ℚ) := by
      have hrew : ∀ a : Fin r → ZMod 2,
          (if a = 0 then z - 1 else -1 : ℚ) = (if a = 0 then z else 0) - 1 := fun a => by
        by_cases ha : a = 0 <;> simp [ha]
      simp_rw [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one]
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    cases x with
    | none => simp
    | some a =>
      simp only [Option.elim_some, char_zero_left, one_mul]
      rw [← Finset.sum_mul, hsum]; ring
  rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.smul_mul, h1, h2, smul_smul, mul_comm]

lemma single_nn_eq {r : ℕ} :
    Matrix.single (none : Option (Fin r → ZMod 2)) none (1 : ℚ) = rankOne vecE vecE := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.single, rankOne, vecE]

lemma single_ns_eq {r : ℕ} (b : Fin r → ZMod 2) :
    Matrix.single (none : Option (Fin r → ZMod 2)) (some b) (1 : ℚ) =
    ((2 ^ r : ℕ) : ℚ)⁻¹ • ∑ ψ : Fin r → ZMod 2, char ψ b • rankOne vecE (vecV ψ) := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.single, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne, vecE, vecV]
  cases i with
  | some a => simp
  | none =>
    cases j with
    | none => simp
    | some b' =>
      simp only [Option.elim_none, Option.elim_some, one_mul, true_and, Option.some.injEq]
      have hrew : ∀ ψ : Fin r → ZMod 2, char ψ b * char ψ b' = char ψ (b + b') :=
        fun ψ => (char_add ψ b b').symm
      simp_rw [hrew, sum_char_left]
      have hiff : b + b' = 0 ↔ b = b' := by
        constructor
        · intro h; have := congrArg (· + b') h; simpa [add_assoc, zmod2_add_self] using this
        · rintro rfl; exact zmod2_add_self b
      by_cases heq : b = b'
      · subst heq; simp [zmod2_add_self, inv_mul_cancel₀ hq0]
      · have hne : b + b' ≠ 0 := fun h => heq (hiff.mp h)
        simp [heq, hne]

lemma single_sn_eq {r : ℕ} (a : Fin r → ZMod 2) :
    Matrix.single (some a : Option (Fin r → ZMod 2)) none (1 : ℚ) =
    ((2 ^ r : ℕ) : ℚ)⁻¹ • ∑ ψ : Fin r → ZMod 2, char ψ a • rankOne (vecV ψ) vecE := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.single, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne, vecE, vecV]
  cases j with
  | some b => simp
  | none =>
    cases i with
    | none => simp
    | some a' =>
      simp only [Option.elim_none, Option.elim_some, mul_one, and_true, Option.some.injEq]
      have hrew : ∀ ψ : Fin r → ZMod 2, char ψ a * char ψ a' = char ψ (a + a') :=
        fun ψ => (char_add ψ a a').symm
      simp_rw [hrew, sum_char_left]
      have hiff : a + a' = 0 ↔ a = a' := by
        constructor
        · intro h; have := congrArg (· + a') h; simpa [add_assoc, zmod2_add_self] using this
        · rintro rfl; exact zmod2_add_self a
      by_cases heq : a = a'
      · subst heq; simp [zmod2_add_self, inv_mul_cancel₀ hq0]
      · have hne : a + a' ≠ 0 := fun h => heq (hiff.mp h)
        simp [heq, hne]

lemma single_ss_eq {r : ℕ} (a b : Fin r → ZMod 2) :
    Matrix.single (some a : Option (Fin r → ZMod 2)) (some b) (1 : ℚ) =
    (((2 ^ r : ℕ) : ℚ)⁻¹ * ((2 ^ r : ℕ) : ℚ)⁻¹) •
      ∑ ψ : Fin r → ZMod 2, ∑ χ : Fin r → ZMod 2,
        (char ψ a * char χ b) • rankOne (vecV ψ) (vecV χ) := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.single, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne, vecV]
  cases i with
  | none => simp
  | some a' =>
    cases j with
    | none => simp
    | some b' =>
      simp only [Option.elim_some, Option.some.injEq]
      have hsep : (∑ ψ : Fin r → ZMod 2, ∑ χ : Fin r → ZMod 2,
          char ψ a * char χ b * (char ψ a' * char χ b')) =
          (∑ ψ : Fin r → ZMod 2, char ψ (a + a')) * (∑ χ : Fin r → ZMod 2, char χ (b + b')) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro ψ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro χ _
        rw [char_add, char_add]; ring
      rw [hsep, sum_char_left, sum_char_left]
      have hiff1 : a + a' = 0 ↔ a = a' := by
        constructor
        · intro h; have := congrArg (· + a') h; simpa [add_assoc, zmod2_add_self] using this
        · rintro rfl; exact zmod2_add_self a
      have hiff2 : b + b' = 0 ↔ b = b' := by
        constructor
        · intro h; have := congrArg (· + b') h; simpa [add_assoc, zmod2_add_self] using this
        · rintro rfl; exact zmod2_add_self b
      by_cases ha : a = a' <;> by_cases hb : b = b'
      · subst ha; subst hb; simp only [Matrix.of_apply, ite_true, and_self, zmod2_add_self]; field_simp [hq0]
      · have hnb : b + b' ≠ 0 := fun h => hb (hiff2.mp h)
        simp [ha, hb, hnb]
      · have hna : a + a' ≠ 0 := fun h => ha (hiff1.mp h)
        simp [ha, hb, hna]
      · have hna : a + a' ≠ 0 := fun h => ha (hiff1.mp h)
        simp [ha, hb, hna]

lemma fourier_correction {r : ℕ} (z : ℚ) (a : Fin r → ZMod 2) :
    let q : ℕ := 2 ^ r
    let f : (Fin r → ZMod 2) → ℚ := fun x => if x = 0 then z - 1 else -1
    let S : Finset (Fin r → ZMod 2) := if z = 2 * (q : ℚ) then Finset.univ.erase 0 else Finset.univ
    let coeff : (Fin r → ZMod 2) → ℚ := fun χ =>
      if χ = 0 then (z - 2 * (q : ℚ)) / (q : ℚ) else (z - (q : ℚ)) / (q : ℚ)
    f a - (if a = 0 then (q : ℚ) else 0) = ∑ χ ∈ S, coeff χ * char χ a := by
  intro q f S coeff
  have hq0 : (q : ℚ) ≠ 0 := by dsimp only [q]; positivity
  have hfull : (∑ χ : Fin r → ZMod 2, coeff χ * char χ a) =
      f a - (if a = 0 then (q : ℚ) else 0) := by
    have hrew : ∀ χ : Fin r → ZMod 2,
        coeff χ * char χ a = ((z - (q : ℚ)) / (q : ℚ)) * char χ a - (if χ = 0 then 1 else 0) := by
      intro χ
      dsimp only [coeff]
      by_cases h0 : χ = 0
      · subst h0; simp only [ite_true, char_zero_left, mul_one]; field_simp [hq0]; ring
      · simp only [h0, ite_false, sub_zero]
    simp_rw [hrew, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_char_left]
    have hsum1 : (∑ χ : Fin r → ZMod 2, (if χ = 0 then (1 : ℚ) else 0)) = 1 := by
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp
      · intro χ _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    rw [hsum1]
    dsimp only [f]
    by_cases ha : a = 0
    · simp only [ha, ite_true]; field_simp [hq0]; ring
    · simp only [ha, ite_false, mul_zero, zero_sub, sub_zero]
  rw [← hfull]
  dsimp only [S]
  by_cases hz2q : z = 2 * (q : ℚ)
  · rw [if_pos hz2q]
    have h0mem : (0 : Fin r → ZMod 2) ∈ (Finset.univ : Finset (Fin r → ZMod 2)) := Finset.mem_univ _
    rw [← Finset.add_sum_erase Finset.univ (fun χ => coeff χ * char χ a) h0mem]
    have hc0 : coeff 0 = 0 := by dsimp only [coeff]; simp [hz2q]
    rw [hc0, zero_mul, zero_add]
  · rw [if_neg hz2q]

lemma fits_pad {r : ℕ} (cycle : List (Fin r → ZMod 2) → ℚ) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂)
    (h1 : ∃ (u v : Fin k₁ → ℚ) (M : (Fin r → ZMod 2) → Matrix (Fin k₁) (Fin k₁) ℚ),
      ∀ w : List (Fin r → ZMod 2), (∑ i : Fin k₁, ∑ j : Fin k₁, u i * (w.map M).prod i j * v j) = cycle w) :
    ∃ (u v : Fin k₂ → ℚ) (M : (Fin r → ZMod 2) → Matrix (Fin k₂) (Fin k₂) ℚ),
      ∀ w : List (Fin r → ZMod 2), (∑ i : Fin k₂, ∑ j : Fin k₂, u i * (w.map M).prod i j * v j) = cycle w := by
  rcases h1 with ⟨u, v, M, hM⟩
  let u' : Fin k₂ → ℚ := fun i => if hi : i.val < k₁ then u ⟨i.val, hi⟩ else 0
  let v' : Fin k₂ → ℚ := fun j => if hj : j.val < k₁ then v ⟨j.val, hj⟩ else 0
  let M' : (Fin r → ZMod 2) → Matrix (Fin k₂) (Fin k₂) ℚ := fun h i j =>
    if hi : i.val < k₁ then if hj : j.val < k₁ then M h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0
  have hprod : ∀ (w : List (Fin r → ZMod 2)) (i j : Fin k₂) (hi : i.val < k₁) (hj : j.val < k₁),
      (w.map M').prod i j = (w.map M).prod ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
    intro w
    induction w with
    | nil =>
      intro i j hi hj
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, Fin.ext_iff]
    | cons h t ih =>
      intro i j hi hj
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun x : Fin k₂ => x.val < k₁))
        (Finset.subset_univ _)]
      · refine Finset.sum_bij (fun x hx => (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin k₁))
          (fun _ _ => Finset.mem_univ _)
          (fun x1 _ x2 _ heq => Fin.ext (congrArg (fun z : Fin k₁ => z.val) heq))
          (fun y _ => ⟨Fin.castLE hle y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.isLt⟩, by ext; rfl⟩)
          (fun x hx => by
            have hxk : x.val < k₁ := (Finset.mem_filter.mp hx).2
            dsimp only [M']
            rw [dif_pos hi, dif_pos hxk, ih x j hxk hj])
      · intro x _ hnot
        have hnk : ¬ (x.val < k₁) := fun hx => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
        dsimp only [M']
        rw [dif_pos hi, dif_neg hnk, zero_mul]
  refine ⟨u', v', M', ?_⟩
  intro w
  rw [← hM w]
  rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun i : Fin k₂ => i.val < k₁)) (Finset.subset_univ _)]
  · refine Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k₁))
      (fun _ _ => Finset.mem_univ _)
      (fun i1 _ i2 _ heq => Fin.ext (congrArg (fun z : Fin k₁ => z.val) heq))
      (fun i' _ => ⟨Fin.castLE hle i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, i'.isLt⟩, by ext; rfl⟩)
      (fun i hi => by
        have hik : i.val < k₁ := (Finset.mem_filter.mp hi).2
        rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun j : Fin k₂ => j.val < k₁)) (Finset.subset_univ _)]
        · refine Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin k₁))
            (fun _ _ => Finset.mem_univ _)
            (fun j1 _ j2 _ heq => Fin.ext (congrArg (fun z : Fin k₁ => z.val) heq))
            (fun j' _ => ⟨Fin.castLE hle j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩, by ext; rfl⟩)
            (fun j hj => by
              have hjk : j.val < k₁ := (Finset.mem_filter.mp hj).2
              dsimp only [u', v']
              rw [dif_pos hik, dif_pos hjk, hprod w i j hik hjk])
        · intro j _ hnot
          have hnk : ¬ (j.val < k₁) := fun hj => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
          dsimp only [v']; rw [dif_neg hnk, mul_zero])
  · intro i _ hnot
    have hnk : ¬ (i.val < k₁) := fun hi => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    apply Finset.sum_eq_zero; intro j _
    dsimp only [u']; rw [dif_neg hnk, zero_mul, zero_mul]

lemma upper_bound_helper (r : ℕ) (z : ℚ) :
    let A := Fin r → ZMod 2
    let q : ℕ := 2 ^ r
    let f := fun a : A => if a = 0 then z - 1 else -1
    let cycle := fun w : List A =>
      Matrix.trace (w.map (Tmat z)).prod + f w.sum - (if w.sum = 0 then (q : ℚ) else 0)
    let least : ℕ := (q + 1) ^ 2 + (if z = 2 * (q : ℚ) then q - 1 else q)
    ∃ (u v : Fin least → ℚ) (M : A → Matrix (Fin least) (Fin least) ℚ),
      ∀ w : List A, (∑ i : Fin least, ∑ j : Fin least, u i * (w.map M).prod i j * v j) = cycle w := by
  intro A q f cycle least
  let S : Finset A := if z = 2 * (q : ℚ) then Finset.univ.erase 0 else Finset.univ
  have hScard : S.card = if z = 2 * (q : ℚ) then q - 1 else q := by
    dsimp only [S]
    by_cases hz2q : z = 2 * (q : ℚ)
    · rw [if_pos hz2q, if_pos hz2q, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [A, q]
    · rw [if_neg hz2q, if_neg hz2q, Finset.card_univ]
      simp [A, q]
  let I := (Option A × Option A) ⊕ {χ : A // χ ∈ S}
  have hIcard : Fintype.card I = least := by
    dsimp only [I, least]
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_coe, hScard]
    have hA : Fintype.card A = q := by simp [A, q]
    rw [hA, sq]
  let eI : Fin least ≃ I := (Fintype.equivFinOfCardEq hIcard).symm
  let coeff : A → ℚ := fun χ =>
    if χ = 0 then (z - 2 * (q : ℚ)) / (q : ℚ) else (z - (q : ℚ)) / (q : ℚ)
  let uI : I → ℚ := fun x =>
    match x with
    | Sum.inl (p, i) => if p = i then 1 else 0
    | Sum.inr χ => coeff χ.1
  let vI : I → ℚ := fun x =>
    match x with
    | Sum.inl (p, j) => if p = j then 1 else 0
    | Sum.inr _ => 1
  let MI : A → Matrix I I ℚ := fun h x y =>
    match x, y with
    | Sum.inl (p₁, i), Sum.inl (p₂, j) => if p₁ = p₂ then Tmat z h i j else 0
    | Sum.inr χ₁, Sum.inr χ₂ => if χ₁ = χ₂ then char χ₁.1 h else 0
    | _, _ => 0
  have hMI_prod : ∀ (w : List A) (x y : I),
      (w.map MI).prod x y =
      match x, y with
      | Sum.inl (p₁, i), Sum.inl (p₂, j) => if p₁ = p₂ then (w.map (Tmat z)).prod i j else 0
      | Sum.inr χ₁, Sum.inr χ₂ => if χ₁ = χ₂ then char χ₁.1 w.sum else 0
      | _, _ => 0 := by
    intro w
    induction w with
    | nil =>
      intro x y
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Matrix.one_apply, char_zero_right]
      cases x with
      | inl pi =>
        cases y with
        | inl pj =>
          rcases pi with ⟨p₁, i⟩; rcases pj with ⟨p₂, j⟩
          by_cases hp : p₁ = p₂
          · subst hp
            by_cases hij : i = j
            · subst hij; simp
            · have hne : (Sum.inl (p₁, i) : I) ≠ Sum.inl (p₁, j) := by simp [hij]
              simp [hne, hij]
          · have hne : (Sum.inl (p₁, i) : I) ≠ Sum.inl (p₂, j) := by simp [hp]
            simp [hne, hp]
        | inr χ => simp
      | inr χ₁ =>
        cases y with
        | inl pj => simp
        | inr χ₂ =>
          by_cases hχ : χ₁ = χ₂
          · subst hχ; simp
          · have hne : (Sum.inr χ₁ : I) ≠ Sum.inr χ₂ := by simp [hχ]
            simp [hne, hχ]
    | cons h t ih =>
      intro x y
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Matrix.mul_apply]
      change (∑ z : (Option A × Option A) ⊕ {χ : A // χ ∈ S}, MI h x z * (t.map MI).prod z y) = _
      rw [Fintype.sum_sum_type]
      cases x with
      | inl pi =>
        rcases pi with ⟨p₁, i⟩
        cases y with
        | inl pj =>
          rcases pj with ⟨p₂, j⟩
          simp only [MI, ih, zero_mul, Finset.sum_const_zero, add_zero]
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_eq_single p₁]
          · by_cases hp : p₁ = p₂
            · subst hp; simp only [ite_true, Matrix.mul_apply]; rfl
            · simp only [ite_true, hp, ite_false, mul_zero, Finset.sum_const_zero]
          · intro p' _ hne; apply Finset.sum_eq_zero; intro k _; simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        | inr χ =>
          simp [MI, ih]
      | inr χ₁ =>
        cases y with
        | inl pj =>
          simp [MI, ih]
        | inr χ₂ =>
          simp only [MI, ih, zero_mul, Finset.sum_const_zero, zero_add]
          rw [Finset.sum_eq_single χ₁]
          · by_cases hχ : χ₁ = χ₂
            · subst hχ; simp only [ite_true]; exact (char_add χ₁.1 h t.sum).symm
            · simp only [ite_true, hχ, ite_false, mul_zero]
          · intro χ' _ hne; simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
  let u : Fin least → ℚ := fun i => uI (eI i)
  let v : Fin least → ℚ := fun j => vI (eI j)
  let M : A → Matrix (Fin least) (Fin least) ℚ := fun h i j => MI h (eI i) (eI j)
  have hM_prod : ∀ (w : List A) (i j : Fin least),
      (w.map M).prod i j = (w.map MI).prod (eI i) (eI j) := by
    intro w
    induction w with
    | nil =>
      intro i j
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, eI.injective.eq_iff]
    | cons h t ih =>
      intro i j
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      calc (∑ x : Fin least, M h i x * (t.map M).prod x j)
          = ∑ x : Fin least, MI h (eI i) (eI x) * (t.map MI).prod (eI x) (eI j) :=
            Finset.sum_congr rfl (fun x _ => by rw [ih x j])
        _ = ∑ y : I, MI h (eI i) y * (t.map MI).prod y (eI j) :=
            Equiv.sum_comp eI (fun y => MI h (eI i) y * (t.map MI).prod y (eI j))
  refine ⟨u, v, M, ?_⟩
  intro w
  calc (∑ i : Fin least, ∑ j : Fin least, u i * (w.map M).prod i j * v j)
      = ∑ i : Fin least, ∑ j : Fin least, uI (eI i) * (w.map MI).prod (eI i) (eI j) * vI (eI j) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hM_prod]
    _ = ∑ x : I, ∑ y : I, uI x * (w.map MI).prod x y * vI y := by
        calc (∑ i : Fin least, ∑ j : Fin least, uI (eI i) * (w.map MI).prod (eI i) (eI j) * vI (eI j))
            = ∑ i : Fin least, ∑ y : I, uI (eI i) * (w.map MI).prod (eI i) y * vI y :=
              Finset.sum_congr rfl (fun i _ =>
                Equiv.sum_comp eI (fun y => uI (eI i) * (w.map MI).prod (eI i) y * vI y))
          _ = ∑ x : I, ∑ y : I, uI x * (w.map MI).prod x y * vI y :=
              Equiv.sum_comp eI (fun x => ∑ y : I, uI x * (w.map MI).prod x y * vI y)
    _ = Matrix.trace (w.map (Tmat z)).prod + ∑ χ ∈ S, coeff χ * char χ w.sum := by
        change (∑ x : (Option A × Option A) ⊕ {χ : A // χ ∈ S},
          ∑ y : (Option A × Option A) ⊕ {χ : A // χ ∈ S}, uI x * (w.map MI).prod x y * vI y) = _
        rw [Fintype.sum_sum_type]
        congr 1
        · rw [Fintype.sum_prod_type]
          simp only [Matrix.trace, Matrix.diag]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_eq_single p]
          · rw [Fintype.sum_sum_type]
            simp only [hMI_prod, uI, vI, ite_true, one_mul, mul_zero, zero_mul,
              Finset.sum_const_zero, add_zero]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single p]
            · simp only [ite_true]
              rw [Finset.sum_eq_single p]
              · simp
              · intro j _ hne; simp [Ne.symm hne]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · intro p' _ hne; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · intro i _ hne; apply Finset.sum_eq_zero; intro y _; simp [uI, Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · calc (∑ χ₁ : {χ : A // χ ∈ S}, ∑ y : (Option A × Option A) ⊕ {χ : A // χ ∈ S},
                  uI (Sum.inr χ₁) * (w.map MI).prod (Sum.inr χ₁) y * vI y)
              = ∑ χ₁ : {χ : A // χ ∈ S}, ∑ χ₂ : {χ : A // χ ∈ S},
                  coeff χ₁.1 * if χ₁ = χ₂ then char χ₁.1 w.sum else 0 := by
                apply Finset.sum_congr rfl; intro χ₁ _
                rw [Fintype.sum_sum_type]
                simp [hMI_prod, uI, vI]
            _ = ∑ χ₁ : {χ : A // χ ∈ S}, coeff χ₁.1 * char χ₁.1 w.sum := by
                apply Finset.sum_congr rfl; intro χ₁ _
                rw [Finset.sum_eq_single χ₁]
                · simp
                · intro χ₂ _ hne; simp [Ne.symm hne]
                · intro hnot; exact absurd (Finset.mem_univ _) hnot
            _ = ∑ χ ∈ S, coeff χ * char χ w.sum := Finset.sum_coe_sort S (fun χ => coeff χ * char χ w.sum)
    _ = cycle w := by
        rw [← fourier_correction z w.sum]
        dsimp only [cycle, f]; ring

abbrev AlgTy (r : ℕ) (S : Finset (Fin r → ZMod 2)) :=
  Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ × ({χ : Fin r → ZMod 2 // χ ∈ S} → ℚ)

lemma lower_bound_helper (r : ℕ) (z : ℚ) (hr : 0 < r) (hz0 : z ≠ 0) (hz2 : z ≠ 2)
    (hzq : z ≠ ((2 ^ r : ℕ) : ℚ)) (k : ℕ)
    (u v : Fin k → ℚ) (M : (Fin r → ZMod 2) → Matrix (Fin k) (Fin k) ℚ)
    (hfit : ∀ w : List (Fin r → ZMod 2), 0 < w.length →
      (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) =
        Matrix.trace (w.map (Tmat z)).prod + (if w.sum = 0 then z - 1 else -1) -
          (if w.sum = 0 then ((2 ^ r : ℕ) : ℚ) else 0)) :
    (2 ^ r + 1) ^ 2 + (if z = 2 * ((2 ^ r : ℕ) : ℚ) then 2 ^ r - 1 else 2 ^ r) ≤ k := by
  let A := Fin r → ZMod 2
  let q : ℕ := 2 ^ r
  have hq0 : (q : ℚ) ≠ 0 := by dsimp only [q]; positivity
  let S : Finset A := if z = 2 * (q : ℚ) then Finset.univ.erase 0 else Finset.univ
  let coeff : A → ℚ := fun χ =>
    if χ = 0 then (z - 2 * (q : ℚ)) / (q : ℚ) else (z - (q : ℚ)) / (q : ℚ)
  have hcoeff_ne : ∀ χ : {χ : A // χ ∈ S}, coeff χ.1 ≠ 0 := by
    intro ⟨χ, hχ⟩
    dsimp only [coeff]
    by_cases h0 : χ = 0
    · subst h0
      have hne2q : z ≠ 2 * (q : ℚ) := by
        intro heq
        dsimp only [S] at hχ
        rw [if_pos heq] at hχ
        exact (Finset.mem_erase.mp hχ).1 rfl
      rw [if_pos rfl]
      exact div_ne_zero (sub_ne_zero.mpr hne2q) hq0
    · rw [if_neg h0]
      exact div_ne_zero (sub_ne_zero.mpr hzq) hq0
  let Φ : List A → AlgTy r S := fun w => ((w.map (Tmat z)).prod, fun χ => char χ.1 w.sum)
  have hΦ_append : ∀ w₁ w₂ : List A, Φ (w₁ ++ w₂) = Φ w₁ * Φ w₂ := by
    intro w₁ w₂
    apply Prod.ext
    · simp only [Φ, List.map_append, List.prod_append, Prod.fst_mul]
    · funext χ; simp only [Φ, List.sum_append, Prod.snd_mul, Pi.mul_apply]; exact char_add χ.1 w₁.sum w₂.sum
  let Λ : AlgTy r S →ₗ[ℚ] ℚ :=
    { toFun := fun a => Matrix.trace a.1 + ∑ χ : {χ : A // χ ∈ S}, coeff χ.1 * a.2 χ
      map_add' := fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.trace_add, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c a => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.trace_smul, smul_eq_mul, Pi.smul_apply,
          RingHom.id_apply, mul_add, Finset.mul_sum]
        congr 1; apply Finset.sum_congr rfl; intro χ _; ring }
  have hΛ_Φ : ∀ w : List A, Λ (Φ w) =
      Matrix.trace (w.map (Tmat z)).prod + (if w.sum = 0 then z - 1 else -1) -
        (if w.sum = 0 then (q : ℚ) else 0) := by
    intro w
    dsimp only [Λ, Φ, LinearMap.coe_mk, AddHom.coe_mk]
    have hcorr := fourier_correction z w.sum
    dsimp only at hcorr
    have hsum : (∑ χ : {χ : A // χ ∈ S}, coeff χ.1 * char χ.1 w.sum) =
        ∑ χ ∈ S, coeff χ * char χ w.sum := Finset.sum_coe_sort S (fun χ => coeff χ * char χ w.sum)
    rw [hsum, ← hcorr]; ring
  have hnondeg : ∀ a : AlgTy r S, (∀ b : AlgTy r S, Λ (a * b) = 0) → a = 0 := by
    intro a hall
    apply Prod.ext
    · ext p p'
      have h := hall (Matrix.single p' p (1 : ℚ), 0)
      simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, mul_zero,
        Pi.zero_apply, Finset.sum_const_zero, add_zero] at h
      have htr : Matrix.trace (a.1 * Matrix.single p' p (1 : ℚ)) = a.1 p p' := by
        dsimp only [Matrix.trace, Matrix.diag]
        rw [Finset.sum_eq_single p]
        · rw [Matrix.mul_apply, Finset.sum_eq_single p']
          · simp [Matrix.single]
          · intro x _ hne; simp [Matrix.single, Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · intro x _ hne
          rw [Matrix.mul_apply]
          apply Finset.sum_eq_zero; intro y _
          simp [Matrix.single, Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      rw [htr] at h; exact h
    · funext χ
      have h := hall (0, fun χ' => if χ' = χ then 1 else 0)
      simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, mul_zero,
        Matrix.trace_zero, zero_add, Pi.mul_apply] at h
      rw [Finset.sum_eq_single χ] at h
      · simp only [ite_true, mul_one] at h
        exact (mul_eq_zero.mp h).resolve_left (hcoeff_ne χ)
      · intro χ' _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  let AlgPos : Submodule ℚ (AlgTy r S) :=
    Submodule.span ℚ {a : AlgTy r S | ∃ w : List A, 0 < w.length ∧ Φ w = a}
  have hmem_Φ : ∀ w : List A, 0 < w.length → Φ w ∈ AlgPos := fun w hw =>
    Submodule.subset_span ⟨w, hw, rfl⟩
  have hmul_mem : ∀ a ∈ AlgPos, ∀ b ∈ AlgPos, a * b ∈ AlgPos := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨w₁, hw₁, rfl⟩ b hb
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨w₂, hw₂, rfl⟩
        rw [← hΦ_append]
        exact hmem_Φ (w₁ ++ w₂) (by simp; omega)
      · rw [mul_zero]; exact AlgPos.zero_mem
      · intro x y _ _ hx hy; rw [mul_add]; exact AlgPos.add_mem hx hy
      · intro c x _ hx; rw [mul_smul_comm]; exact AlgPos.smul_mem c hx
    · intro b _; rw [zero_mul]; exact AlgPos.zero_mem
    · intro x y _ _ hx hy b hb; rw [add_mul]; exact AlgPos.add_mem (hx b hb) (hy b hb)
    · intro c x _ hx b hb; rw [smul_mul_assoc]; exact AlgPos.smul_mem c (hx b hb)
  have hΦ0 : Φ [0] ∈ AlgPos := hmem_Φ [0] (by simp)
  have hΦ0_val : Φ [0] = (Tmat z 0, 1) := by
    apply Prod.ext
    · simp [Φ]
    · funext χ; simp [Φ, char_zero_right]
  have h2z : (2 - z : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz2)
  have hone_mem : (1 : AlgTy r S) ∈ AlgPos := by
    have hcub : Φ [0] * Φ [0] * Φ [0] - (3 : ℚ) • (Φ [0] * Φ [0]) + (4 - z) • Φ [0] =
        (2 - z) • (1 : AlgTy r S) := by
      rw [hΦ0_val]
      apply Prod.ext
      · exact T0_cubic z
      · funext χ
        simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_mul,
          Prod.snd_one, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.one_apply,
          smul_eq_mul]
        ring
    have hlin : Φ [0] * Φ [0] * Φ [0] - (3 : ℚ) • (Φ [0] * Φ [0]) + (4 - z) • Φ [0] ∈ AlgPos :=
      AlgPos.add_mem
        (AlgPos.sub_mem (hmul_mem _ (hmul_mem _ hΦ0 _ hΦ0) _ hΦ0)
          (AlgPos.smul_mem 3 (hmul_mem _ hΦ0 _ hΦ0)))
        (AlgPos.smul_mem (4 - z) hΦ0)
    rw [hcub] at hlin
    have := AlgPos.smul_mem (2 - z)⁻¹ hlin
    rwa [smul_smul, inv_mul_cancel₀ h2z, one_smul] at this
  have hU_mem : ∀ h : A, ((Ptilde h, fun χ => char χ.1 h) : AlgTy r S) ∈ AlgPos := by
    intro h
    let inv0 : AlgTy r S := (2 - z)⁻¹ • (Φ [0] * Φ [0] - (3 : ℚ) • Φ [0] + (4 - z) • (1 : AlgTy r S))
    have hinv0_mem : inv0 ∈ AlgPos :=
      AlgPos.smul_mem _ (AlgPos.add_mem
        (AlgPos.sub_mem (hmul_mem _ hΦ0 _ hΦ0) (AlgPos.smul_mem 3 hΦ0))
        (AlgPos.smul_mem (4 - z) hone_mem))
    have hinv0_mul : inv0 * Φ [0] = 1 := by
      dsimp only [inv0]
      rw [smul_mul_assoc, add_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
      have hcub : Φ [0] * Φ [0] * Φ [0] - (3 : ℚ) • (Φ [0] * Φ [0]) + (4 - z) • Φ [0] =
          (2 - z) • (1 : AlgTy r S) := by
        rw [hΦ0_val]
        apply Prod.ext
        · exact T0_cubic z
        · funext χ
          simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_mul, Prod.snd_one,
            Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.one_apply, smul_eq_mul]
          ring
      rw [hcub, smul_smul, inv_mul_cancel₀ h2z, one_smul]
    have hΦh : Φ [h] ∈ AlgPos := hmem_Φ [h] (by simp)
    have hfact : Φ [h] = Φ [0] * ((Ptilde h, fun χ => char χ.1 h) : AlgTy r S) := by
      rw [hΦ0_val]
      apply Prod.ext
      · simp only [Φ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Prod.fst_mul]
        exact Tmat_eq_T0_mul_Ptilde z h
      · funext χ; simp only [Φ, List.sum_cons, List.sum_nil, add_zero, Prod.snd_mul, Pi.mul_apply,
          Pi.one_apply, one_mul]
    have heq : inv0 * Φ [h] = ((Ptilde h, fun χ => char χ.1 h) : AlgTy r S) := by
      rw [hfact, ← mul_assoc, hinv0_mul, one_mul]
    rw [← heq]
    exact hmul_mem _ hinv0_mem _ hΦh
  let proj : A → AlgTy r S := fun ψ =>
    (Qmat ψ, fun χ => if χ.1 = ψ then 1 else 0)
  have hproj_mem : ∀ ψ : A, proj ψ ∈ AlgPos := by
    intro ψ
    have heq : proj ψ = (q : ℚ)⁻¹ • ∑ h : A, char ψ h • ((Ptilde h, fun χ => char χ.1 h) : AlgTy r S) := by
      apply Prod.ext
      · simp only [proj, Qmat, q, Prod.smul_fst, Prod.fst_sum]; rfl
      · funext ⟨χ, hχ⟩
        dsimp only [proj]
        rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Prod.snd_sum, Finset.sum_apply]
        have hrew : ∀ h : A, (char ψ h • ((Ptilde h, fun χ' => char χ'.1 h) : AlgTy r S)).2 ⟨χ, hχ⟩ =
            char (ψ + χ) h := fun h => by
          rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          dsimp only
          rw [char_comm ψ, char_comm χ, ← char_add, char_comm]
        simp_rw [hrew]
        rw [sum_char_right]
        have hiff : ψ + χ = 0 ↔ χ = ψ := by
          constructor
          · intro h
            have h1 := congrArg (ψ + ·) h
            rw [← add_assoc, zmod2_add_self, zero_add, add_zero] at h1
            exact h1
          · rintro rfl; exact zmod2_add_self χ
        by_cases heq : χ = ψ
        · subst heq
          rw [if_pos rfl, zmod2_add_self, if_pos rfl]
          exact (inv_mul_cancel₀ hq0).symm
        · have hne : ψ + χ ≠ 0 := fun h => heq (hiff.mp h)
          simp [heq, hne]
    rw [heq]
    exact AlgPos.smul_mem _ (AlgPos.sum_mem (fun h _ => AlgPos.smul_mem _ (hU_mem h)))
  have hEv_nz : ∀ ψ : A, ψ ≠ 0 → ((rankOne vecE (vecV ψ), 0) : AlgTy r S) ∈ AlgPos := by
    intro ψ hψ
    have hprod : proj 0 * Φ [0] * proj ψ = ((q : ℚ)⁻¹ • rankOne vecE (vecV ψ), 0) := by
      rw [hΦ0_val]
      apply Prod.ext
      · exact Q0_mul_T0_mul_Qpsi z ψ hψ
      · funext ⟨χ, hχ⟩
        simp only [proj, Prod.snd_mul, Pi.mul_apply, Pi.one_apply, Pi.zero_apply, mul_one]
        by_cases hχ0 : χ = 0
        · subst hχ0; simp [Ne.symm hψ]
        · simp [hχ0]
    have hmem := hmul_mem _ (hmul_mem _ (hproj_mem 0) _ hΦ0) _ (hproj_mem ψ)
    rw [hprod] at hmem
    have hsc := AlgPos.smul_mem (q : ℚ) hmem
    have heq : (q : ℚ) • (((q : ℚ)⁻¹ • rankOne vecE (vecV ψ), 0) : AlgTy r S) = (rankOne vecE (vecV ψ), 0) := by
      apply Prod.ext
      · simp [smul_smul, mul_inv_cancel₀ hq0]
      · simp
    rwa [heq] at hsc
  have hvE_nz : ∀ ψ : A, ψ ≠ 0 → ((rankOne (vecV ψ) vecE, 0) : AlgTy r S) ∈ AlgPos := by
    intro ψ hψ
    have hprod : proj ψ * Φ [0] * proj 0 = ((z * (q : ℚ)⁻¹) • rankOne (vecV ψ) vecE, 0) := by
      rw [hΦ0_val]
      apply Prod.ext
      · exact Qpsi_mul_T0_mul_Q0 z ψ hψ
      · funext ⟨χ, hχ⟩
        simp only [proj, Prod.snd_mul, Pi.mul_apply, Pi.one_apply, Pi.zero_apply, mul_one]
        by_cases hχ0 : χ = 0
        · subst hχ0; simp [Ne.symm hψ]
        · simp [hχ0]
    have hmem := hmul_mem _ (hmul_mem _ (hproj_mem ψ) _ hΦ0) _ (hproj_mem 0)
    rw [hprod] at hmem
    have hsc := AlgPos.smul_mem (z⁻¹ * (q : ℚ)) hmem
    have hnz : (z⁻¹ * (q : ℚ)) * (z * (q : ℚ)⁻¹) = 1 := by field_simp [hz0, hq0]
    have heq : (z⁻¹ * (q : ℚ)) • (((z * (q : ℚ)⁻¹) • rankOne (vecV ψ) vecE, 0) : AlgTy r S) =
        (rankOne (vecV ψ) vecE, 0) := by
      apply Prod.ext
      · simp [smul_smul, hnz]
      · simp
    rwa [heq] at hsc
  let ψ₀ : A := fun i => if i = ⟨0, hr⟩ then 1 else 0
  have hψ₀ : ψ₀ ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨0, hr⟩
    simp only [ψ₀, ite_true, Pi.zero_apply] at h1
    change (1 : ZMod 2) = 0 at h1
    exact absurd h1 (by decide)
  have hEnn_mem : ((rankOne vecE vecE, 0) : AlgTy r S) ∈ AlgPos := by
    have hprod : ((rankOne vecE (vecV ψ₀), 0) : AlgTy r S) * (rankOne (vecV ψ₀) vecE, 0) =
        ((q : ℚ) • rankOne vecE vecE, 0) := by
      apply Prod.ext
      · simp only [Prod.fst_mul]; rw [rankOne_mul_rankOne, dot_VV]; simp [q]
      · simp
    have hmem := hmul_mem _ (hEv_nz ψ₀ hψ₀) _ (hvE_nz ψ₀ hψ₀)
    rw [hprod] at hmem
    have hsc := AlgPos.smul_mem (q : ℚ)⁻¹ hmem
    have heq : (q : ℚ)⁻¹ • (((q : ℚ) • rankOne vecE vecE, 0) : AlgTy r S) = (rankOne vecE vecE, 0) := by
      apply Prod.ext
      · simp [smul_smul, inv_mul_cancel₀ hq0]
      · simp
    rwa [heq] at hsc
  have hEv0_mem : ((rankOne vecE (vecV 0), 0) : AlgTy r S) ∈ AlgPos := by
    have hprod : ((rankOne vecE vecE, 0) : AlgTy r S) * Φ [0] * proj 0 =
        (rankOne vecE vecE + (q : ℚ)⁻¹ • rankOne vecE (vecV 0), 0) := by
      rw [hΦ0_val]
      apply Prod.ext
      · exact Enn_mul_T0_mul_Q0 z
      · simp
    have hmem := hmul_mem _ (hmul_mem _ hEnn_mem _ hΦ0) _ (hproj_mem 0)
    rw [hprod] at hmem
    have hsub := AlgPos.sub_mem hmem hEnn_mem
    have hsc := AlgPos.smul_mem (q : ℚ) hsub
    have heq : (q : ℚ) • (((rankOne vecE vecE + (q : ℚ)⁻¹ • rankOne vecE (vecV 0), 0) : AlgTy r S) -
        (rankOne vecE vecE, 0)) = (rankOne vecE (vecV 0), 0) := by
      apply Prod.ext
      · simp [smul_smul, mul_inv_cancel₀ hq0]
      · simp
    rwa [heq] at hsc
  have hv0E_mem : ((rankOne (vecV 0) vecE, 0) : AlgTy r S) ∈ AlgPos := by
    have hprod : proj 0 * Φ [0] * ((rankOne vecE vecE, 0) : AlgTy r S) =
        (rankOne vecE vecE + ((z - (q : ℚ)) * (q : ℚ)⁻¹) • rankOne (vecV 0) vecE, 0) := by
      rw [hΦ0_val]
      apply Prod.ext
      · exact Q0_mul_T0_mul_Enn z
      · simp
    have hmem := hmul_mem _ (hmul_mem _ (hproj_mem 0) _ hΦ0) _ hEnn_mem
    rw [hprod] at hmem
    have hsub := AlgPos.sub_mem hmem hEnn_mem
    have hsc := AlgPos.smul_mem ((z - (q : ℚ))⁻¹ * (q : ℚ)) hsub
    have hzq' : (z - (q : ℚ)) ≠ 0 := sub_ne_zero.mpr hzq
    have hnz : ((z - (q : ℚ))⁻¹ * (q : ℚ)) * ((z - (q : ℚ)) * (q : ℚ)⁻¹) = 1 := by
      field_simp [hzq', hq0]
    have heq : ((z - (q : ℚ))⁻¹ * (q : ℚ)) •
        (((rankOne vecE vecE + ((z - (q : ℚ)) * (q : ℚ)⁻¹) • rankOne (vecV 0) vecE, 0) : AlgTy r S) -
          (rankOne vecE vecE, 0)) = (rankOne (vecV 0) vecE, 0) := by
      apply Prod.ext
      · simp [smul_smul, hnz]
      · simp
    rwa [heq] at hsc
  have hEv_all : ∀ ψ : A, ((rankOne vecE (vecV ψ), 0) : AlgTy r S) ∈ AlgPos := fun ψ => by
    by_cases h0 : ψ = 0
    · subst h0; exact hEv0_mem
    · exact hEv_nz ψ h0
  have hvE_all : ∀ ψ : A, ((rankOne (vecV ψ) vecE, 0) : AlgTy r S) ∈ AlgPos := fun ψ => by
    by_cases h0 : ψ = 0
    · subst h0; exact hv0E_mem
    · exact hvE_nz ψ h0
  have hvV_all : ∀ ψ χ : A, ((rankOne (vecV ψ) (vecV χ), 0) : AlgTy r S) ∈ AlgPos := by
    intro ψ χ
    have hprod : ((rankOne (vecV ψ) vecE, 0) : AlgTy r S) * (rankOne vecE (vecV χ), 0) =
        (rankOne (vecV ψ) (vecV χ), 0) := by
      apply Prod.ext
      · simp only [Prod.fst_mul]; rw [rankOne_mul_rankOne, dot_EE, one_smul]
      · simp
    rw [← hprod]
    exact hmul_mem _ (hvE_all ψ) _ (hEv_all χ)
  have hmat_unit : ∀ p p' : Option A, ((Matrix.single p p' (1 : ℚ), 0) : AlgTy r S) ∈ AlgPos := by
    intro p p'
    cases p with
    | none =>
      cases p' with
      | none => rw [single_nn_eq]; exact hEnn_mem
      | some b =>
        have heq : ((Matrix.single (none : Option A) (some b) (1 : ℚ), 0) : AlgTy r S) =
            (q : ℚ)⁻¹ • ∑ ψ : A, char ψ b • ((rankOne vecE (vecV ψ), 0) : AlgTy r S) := by
          apply Prod.ext
          · simp only [q, Prod.smul_fst, Prod.fst_sum]; exact single_ns_eq b
          · simp only [Prod.smul_snd, Prod.snd_sum, smul_zero, Finset.sum_const_zero]
        rw [heq]
        exact AlgPos.smul_mem _ (AlgPos.sum_mem (fun ψ _ => AlgPos.smul_mem _ (hEv_all ψ)))
    | some a =>
      cases p' with
      | none =>
        have heq : ((Matrix.single (some a : Option A) none (1 : ℚ), 0) : AlgTy r S) =
            (q : ℚ)⁻¹ • ∑ ψ : A, char ψ a • ((rankOne (vecV ψ) vecE, 0) : AlgTy r S) := by
          apply Prod.ext
          · simp only [q, Prod.smul_fst, Prod.fst_sum]; exact single_sn_eq a
          · simp only [Prod.smul_snd, Prod.snd_sum, smul_zero, Finset.sum_const_zero]
        rw [heq]
        exact AlgPos.smul_mem _ (AlgPos.sum_mem (fun ψ _ => AlgPos.smul_mem _ (hvE_all ψ)))
      | some b =>
        have heq : ((Matrix.single (some a : Option A) (some b) (1 : ℚ), 0) : AlgTy r S) =
            ((q : ℚ)⁻¹ * (q : ℚ)⁻¹) • ∑ ψ : A, ∑ χ : A,
              (char ψ a * char χ b) • ((rankOne (vecV ψ) (vecV χ), 0) : AlgTy r S) := by
          apply Prod.ext
          · simp only [q, Prod.smul_fst, Prod.fst_sum]; exact single_ss_eq a b
          · simp only [Prod.smul_snd, Prod.snd_sum, smul_zero, Finset.sum_const_zero]
        rw [heq]
        exact AlgPos.smul_mem _ (AlgPos.sum_mem (fun ψ _ =>
          AlgPos.sum_mem (fun χ _ => AlgPos.smul_mem _ (hvV_all ψ χ))))
  have hchar_unit : ∀ χ : {χ : A // χ ∈ S},
      (((0 : Matrix (Option A) (Option A) ℚ), fun χ' => if χ' = χ then 1 else 0) : AlgTy r S) ∈ AlgPos := by
    intro χ
    by_cases h0 : χ.1 = 0
    · have heq : (((0 : Matrix (Option A) (Option A) ℚ), fun χ' => if χ' = χ then 1 else 0) : AlgTy r S) =
          proj 0 - (rankOne vecE vecE, 0) - (q : ℚ)⁻¹ • (rankOne (vecV 0) (vecV 0), 0) := by
        apply Prod.ext
        · simp [proj, Qmat_zero, q]
        · funext χ'
          simp only [proj, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
            smul_zero, sub_zero]
          by_cases h : χ' = χ
          · subst h; simp [h0]
          · have hne : χ'.1 ≠ 0 := fun h' => h (Subtype.ext (h'.trans h0.symm))
            simp [h, hne]
      rw [heq]
      exact AlgPos.sub_mem (AlgPos.sub_mem (hproj_mem 0) hEnn_mem) (AlgPos.smul_mem _ (hvV_all 0 0))
    · have heq : (((0 : Matrix (Option A) (Option A) ℚ), fun χ' => if χ' = χ then 1 else 0) : AlgTy r S) =
          proj χ.1 - (q : ℚ)⁻¹ • (rankOne (vecV χ.1) (vecV χ.1), 0) := by
        apply Prod.ext
        · simp [proj, Qmat_ne_zero χ.1 h0, q]
        · funext χ'
          simp only [proj, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
            smul_zero, sub_zero]
          by_cases h : χ' = χ
          · subst h; simp
          · have hne : χ'.1 ≠ χ.1 := fun h' => h (Subtype.ext h')
            simp [h, hne]
      rw [heq]
      exact AlgPos.sub_mem (hproj_mem χ.1) (AlgPos.smul_mem _ (hvV_all χ.1 χ.1))
  have hAlgPos_top : ∀ a : AlgTy r S, a ∈ AlgPos := by
    intro a
    have heq : a = (∑ p : Option A, ∑ p' : Option A, a.1 p p' • ((Matrix.single p p' (1 : ℚ), 0) : AlgTy r S)) +
        ∑ χ : {χ : A // χ ∈ S}, a.2 χ • (((0 : Matrix (Option A) (Option A) ℚ),
          fun χ' => if χ' = χ then 1 else 0) : AlgTy r S) := by
      apply Prod.ext
      · ext p p'
        simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Matrix.add_apply, Matrix.sum_apply,
          Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
        rw [Finset.sum_eq_single p]
        · rw [Finset.sum_eq_single p']
          · simp [Matrix.single]
          · intro y _ hne; simp [Matrix.single, hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · intro x _ hne; apply Finset.sum_eq_zero; intro y _; simp [Matrix.single, hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · funext χ
        simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Pi.add_apply, Finset.sum_apply,
          Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add]
        rw [Finset.sum_eq_single χ]
        · simp
        · intro χ' _ hne; simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
    rw [heq]
    exact AlgPos.add_mem
      (AlgPos.sum_mem (fun p _ => AlgPos.sum_mem (fun p' _ => AlgPos.smul_mem _ (hmat_unit p p'))))
      (AlgPos.sum_mem (fun χ _ => AlgPos.smul_mem _ (hchar_unit χ)))
  let I := (Option A × Option A) ⊕ {χ : A // χ ∈ S}
  let basisElem : I → AlgTy r S := fun idx =>
    match idx with
    | Sum.inl (p, p') => (Matrix.single p p' (1 : ℚ), 0)
    | Sum.inr χ => (0, fun χ' => if χ' = χ then 1 else 0)
  have hrep : ∀ idx : I, ∃ (s : Finset (List A)) (α : List A → ℚ),
      (∀ w ∈ s, 0 < w.length) ∧ (∑ w ∈ s, α w • Φ w) = basisElem idx := by
    intro idx
    have hmem : basisElem idx ∈ AlgPos := hAlgPos_top (basisElem idx)
    rw [Submodule.mem_span_set] at hmem
    rcases hmem with ⟨c, hc_supp, hc_sum⟩
    have hcho : ∀ a : AlgTy r S, a ∈ c.support → ∃ w : List A, 0 < w.length ∧ Φ w = a := fun a ha =>
      hc_supp ha
    choose wOf hw_pos hw_eq using hcho
    let s : Finset (List A) := c.support.attach.image (fun x => wOf x.1 x.2)
    let α : List A → ℚ := fun w => ∑ x ∈ c.support.attach.filter (fun x => wOf x.1 x.2 = w), c x.1
    refine ⟨s, α, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
      exact hw_pos x.1 x.2
    · rw [← hc_sum]
      calc (∑ w ∈ s, α w • Φ w)
          = ∑ w ∈ s, ∑ x ∈ c.support.attach.filter (fun x => wOf x.1 x.2 = w), c x.1 • Φ (wOf x.1 x.2) := by
            apply Finset.sum_congr rfl; intro w _
            dsimp only [α]
            rw [Finset.sum_smul]
            apply Finset.sum_congr rfl; intro x hx
            rw [(Finset.mem_filter.mp hx).2]
        _ = ∑ x ∈ c.support.attach, c x.1 • Φ (wOf x.1 x.2) := by
            rw [← Finset.sum_fiberwise_of_maps_to (s := c.support.attach) (t := s)
              (g := fun x => wOf x.1 x.2) (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩)]
        _ = ∑ x ∈ c.support.attach, c x.1 • x.1 := by
            apply Finset.sum_congr rfl; intro x _
            rw [hw_eq x.1 x.2]
        _ = c.sum (fun a r => r • a) := by
            rw [Finsupp.sum, Finset.sum_attach c.support (fun a => c a • a)]
  choose sRep αRep hs_pos hs_eq using hrep
  let rowVec : I → (Fin k → ℚ) := fun idx j =>
    ∑ w ∈ sRep idx, αRep idx w * ∑ i : Fin k, u i * (w.map M).prod i j
  have hlin : LinearIndependent ℚ rowVec := by
    rw [Fintype.linearIndependent_iff]
    intro β hβ
    let a : AlgTy r S := ∑ idx : I, β idx • basisElem idx
    have ha_zero_pos : ∀ w' : List A, 0 < w'.length → Λ (a * Φ w') = 0 := by
      intro w' hw'
      have h1 : a * Φ w' = ∑ idx : I, β idx • ∑ w ∈ sRep idx, αRep idx w • Φ (w ++ w') := by
        dsimp only [a]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro idx _
        rw [← hs_eq idx, smul_mul_assoc, Finset.sum_mul]
        congr 1; apply Finset.sum_congr rfl; intro w _
        rw [smul_mul_assoc, hΦ_append]
      rw [h1, map_sum]
      have h2 : (∑ idx : I, Λ (β idx • ∑ w ∈ sRep idx, αRep idx w • Φ (w ++ w'))) =
          ∑ j : Fin k, (∑ idx : I, β idx * rowVec idx j) * ∑ l : Fin k, (w'.map M).prod j l * v l := by
        have hterm : ∀ idx : I,
            Λ (β idx • ∑ w ∈ sRep idx, αRep idx w • Φ (w ++ w')) =
            ∑ j : Fin k, (β idx * rowVec idx j) * ∑ l : Fin k, (w'.map M).prod j l * v l := by
          intro idx
          rw [map_smul, map_sum, smul_eq_mul]
          have hinner : (∑ w ∈ sRep idx, Λ (αRep idx w • Φ (w ++ w'))) =
              ∑ j : Fin k, rowVec idx j * ∑ l : Fin k, (w'.map M).prod j l * v l := by
            calc (∑ w ∈ sRep idx, Λ (αRep idx w • Φ (w ++ w')))
                = ∑ w ∈ sRep idx, αRep idx w * ∑ i : Fin k, ∑ l : Fin k,
                    u i * ((w ++ w').map M).prod i l * v l := by
                  apply Finset.sum_congr rfl; intro w hw
                  rw [map_smul, smul_eq_mul, hΛ_Φ, hfit (w ++ w') (by simp; omega)]
              _ = ∑ w ∈ sRep idx, αRep idx w * ∑ j : Fin k,
                    (∑ i : Fin k, u i * (w.map M).prod i j) * ∑ l : Fin k, (w'.map M).prod j l * v l := by
                  apply Finset.sum_congr rfl; intro w _
                  congr 1
                  simp_rw [List.map_append, List.prod_append, Matrix.mul_apply]
                  calc (∑ i : Fin k, ∑ l : Fin k, u i * (∑ j : Fin k, (w.map M).prod i j * (w'.map M).prod j l) * v l)
                      = ∑ i : Fin k, ∑ l : Fin k, ∑ j : Fin k,
                          (u i * (w.map M).prod i j) * ((w'.map M).prod j l * v l) := by
                        apply Finset.sum_congr rfl; intro i _
                        apply Finset.sum_congr rfl; intro l _
                        rw [Finset.mul_sum, Finset.sum_mul]
                        apply Finset.sum_congr rfl; intro j _; ring
                    _ = ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k,
                          (u i * (w.map M).prod i j) * ((w'.map M).prod j l * v l) := by
                        apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
                    _ = ∑ j : Fin k, ∑ i : Fin k, ∑ l : Fin k,
                          (u i * (w.map M).prod i j) * ((w'.map M).prod j l * v l) := Finset.sum_comm
                    _ = ∑ j : Fin k, (∑ i : Fin k, u i * (w.map M).prod i j) *
                          ∑ l : Fin k, (w'.map M).prod j l * v l := by
                        apply Finset.sum_congr rfl; intro j _
                        rw [Finset.sum_mul]
                        apply Finset.sum_congr rfl; intro i _
                        rw [Finset.mul_sum]
              _ = ∑ j : Fin k, rowVec idx j * ∑ l : Fin k, (w'.map M).prod j l * v l := by
                  calc (∑ w ∈ sRep idx, αRep idx w * ∑ j : Fin k,
                          (∑ i : Fin k, u i * (w.map M).prod i j) * ∑ l : Fin k, (w'.map M).prod j l * v l)
                      = ∑ w ∈ sRep idx, ∑ j : Fin k,
                          (αRep idx w * ∑ i : Fin k, u i * (w.map M).prod i j) *
                            ∑ l : Fin k, (w'.map M).prod j l * v l := by
                        apply Finset.sum_congr rfl; intro w _
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl; intro j _; ring
                    _ = ∑ j : Fin k, ∑ w ∈ sRep idx,
                          (αRep idx w * ∑ i : Fin k, u i * (w.map M).prod i j) *
                            ∑ l : Fin k, (w'.map M).prod j l * v l := Finset.sum_comm
                    _ = ∑ j : Fin k, rowVec idx j * ∑ l : Fin k, (w'.map M).prod j l * v l := by
                        apply Finset.sum_congr rfl; intro j _
                        dsimp only [rowVec]
                        rw [Finset.sum_mul]
          rw [hinner, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        simp_rw [hterm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_mul]
      rw [h2]
      apply Finset.sum_eq_zero; intro j _
      have hj : (∑ idx : I, β idx * rowVec idx j) = 0 := by
        have := congrFun hβ j
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
      rw [hj, zero_mul]
    have ha_zero_all : ∀ b : AlgTy r S, Λ (a * b) = 0 := by
      intro b
      have hb : b ∈ AlgPos := hAlgPos_top b
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨w', hw', rfl⟩; exact ha_zero_pos w' hw'
      · rw [mul_zero, map_zero]
      · intro x y _ _ hx hy; rw [mul_add, map_add, hx, hy, add_zero]
      · intro c x _ hx; rw [mul_smul_comm, map_smul, hx, smul_zero]
    have ha0 : a = 0 := hnondeg a ha_zero_all
    intro idx
    cases idx with
    | inl pp =>
      rcases pp with ⟨p, p'⟩
      have h := congrArg (fun x : AlgTy r S => x.1 p p') ha0
      simp only [a, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Matrix.sum_apply,
        Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at h
      rw [Finset.sum_eq_single (Sum.inl (p, p'))] at h
      · simpa [basisElem, Matrix.single] using h
      · intro idx' _ hne
        cases idx' with
        | inl qq =>
          rcases qq with ⟨q₁, q₂⟩
          have hne' : ¬ (q₁ = p ∧ q₂ = p') := by
            rintro ⟨rfl, rfl⟩; exact hne rfl
          simp [basisElem, Matrix.single, hne']
        | inr χ => simp [basisElem]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    | inr χ =>
      have h := congrArg (fun x : AlgTy r S => x.2 χ) ha0
      simp only [a, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Finset.sum_apply,
        Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
      rw [Finset.sum_eq_single (Sum.inr χ)] at h
      · simpa [basisElem] using h
      · intro idx' _ hne
        cases idx' with
        | inl qq => simp [basisElem]
        | inr χ' =>
          have hne' : χ ≠ χ' := fun heq => hne (by rw [heq])
          simp [basisElem, hne']
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  have hcard_le : Fintype.card I ≤ Module.finrank ℚ (Fin k → ℚ) :=
    hlin.fintype_card_le_finrank
  rw [Module.finrank_fin_fun] at hcard_le
  have hScard : S.card = if z = 2 * (q : ℚ) then q - 1 else q := by
    dsimp only [S]
    by_cases hz2q : z = 2 * (q : ℚ)
    · rw [if_pos hz2q, if_pos hz2q, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [A, q]
    · rw [if_neg hz2q, if_neg hz2q, Finset.card_univ]
      simp [A, q]
  have hIcard : Fintype.card I = (q + 1) ^ 2 + (if z = 2 * (q : ℚ) then q - 1 else q) := by
    dsimp only [I]
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_coe, hScard]
    have hA : Fintype.card A = q := by simp [A, q]
    rw [hA, sq]
  rw [hIcard] at hcard_le
  exact hcard_le

end PEqualNP.Outside.L_lib_800_aux

theorem PEqualNP.Outside.L_lib_800 :
    ∀ (r : ℕ) (z : ℚ),
      let A := Fin r → ZMod 2
      let q : ℕ := 2^r
      let f := fun a : A => if a = 0 then z-1 else -1
      let T : A → Matrix (Option A) (Option A) ℚ := fun h before after =>
        before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
          (fun a => after.elim (f a) (fun b => if b = a+h then 1 else 0))
      let cycle := fun w : List A =>
        Matrix.trace (w.map T).prod + f w.sum - (if w.sum = 0 then (q : ℚ) else 0)
      let fits := fun (k : ℕ) (test : List A → Prop) =>
        ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
          ∀ w : List A, test w → (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) = cycle w
      0 < r → z ≠ 0 → z ≠ 2 → z ≠ (q : ℚ) →
        let least : ℕ := (q+1)^2 + (if z = 2*(q : ℚ) then q-1 else q)
        ∀ k : ℕ, (fits k (fun _ => True) ↔ least ≤ k) ∧
          (fits k (fun w => 0 < w.length) ↔ least ≤ k) := by
  intro r z A q f T cycle fits hr hz0 hz2 hzq least k
  have hT_eq : T = PEqualNP.Outside.L_lib_800_aux.Tmat z := rfl
  have hup : least ≤ k → fits k (fun _ => True) := by
    intro hle
    have hbase := PEqualNP.Outside.L_lib_800_aux.upper_bound_helper r z
    dsimp only at hbase
    have hpad := PEqualNP.Outside.L_lib_800_aux.fits_pad cycle hle hbase
    rcases hpad with ⟨u, v, M, hM⟩
    exact ⟨u, v, M, fun w _ => hM w⟩
  have hlo : fits k (fun w => 0 < w.length) → least ≤ k := by
    rintro ⟨u, v, M, hM⟩
    exact PEqualNP.Outside.L_lib_800_aux.lower_bound_helper r z hr hz0 hz2 hzq k u v M hM
  refine ⟨⟨fun h => hlo (by rcases h with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩), hup⟩,
    ⟨hlo, fun hle => by rcases hup hle with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩⟩⟩
