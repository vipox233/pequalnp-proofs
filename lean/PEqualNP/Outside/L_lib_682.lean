import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_682_aux

private def sgn (b : Bool) : ℤ := if b then -1 else 1

private lemma sgn_false : sgn false = 1 := rfl

private lemma sgn_true : sgn true = -1 := rfl

private lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> rfl

private lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> rfl

private lemma sgn_inj {a b : Bool} (h : sgn a = sgn b) : a = b := by
  cases a <;> cases b <;> simp [sgn] at h <;> rfl

private lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by
  cases b <;> decide

private lemma sgn_abs (b : Bool) : |sgn b| = 1 := by
  cases b <;> decide

private lemma sgn_mul_eq_sub (a b : Bool) :
    sgn a * sgn b = 1 - 2 * (if a ≠ b then (1 : ℤ) else 0) := by
  cases a <;> cases b <;> decide

private def isHad {N : ℕ} (M : Fin N → Fin N → Bool) : Prop :=
  ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N

private def sampleFn {N : ℕ} (D : Fin N → Fin N → Bool) (r c : Fin N → Fin N)
    (u v : Fin N → Bool) (i j : Fin N) : Bool :=
  xor (xor (u i) (v j)) (D (r i) (c j))

private def errorsFn {N : ℕ} (A B : Fin N → Fin N → Bool) : ℕ :=
  ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => A i j ≠ B i j)).card

private def editFn {N : ℕ} (H : Fin N → Fin N → Bool) (i j k l : Fin N) (f g : Bool)
    (x y : Fin N) : Bool :=
  xor (xor (if x = i ∧ i ≠ j then f else false) (if y = k ∧ k ≠ l then g else false))
    (H (if x = i then j else x) (if y = k then l else y))

private def errInd {N : ℕ} (A B : Fin N → Fin N → Bool) (i j : Fin N) : ℕ :=
  if A i j ≠ B i j then 1 else 0

private lemma errors_eq_sum_ind {N : ℕ} (A B : Fin N → Fin N → Bool) :
    errorsFn A B = ∑ i : Fin N, ∑ j : Fin N, errInd A B i j := by
  simp only [errorsFn, errInd, Finset.card_filter]

private lemma had_row_dot_self {N : ℕ} (M : Fin N → Fin N → Bool) (a : Fin N) :
    ∑ j : Fin N, sgn (M a j) * sgn (M a j) = (N : ℤ) := by
  simp [sgn_mul_self]

private lemma had_row_dot_ne {N : ℕ} {M : Fin N → Fin N → Bool} (hM : isHad M)
    {a b : Fin N} (hab : a ≠ b) :
    ∑ j : Fin N, sgn (M a j) * sgn (M b j) = 0 := by
  have h1 : ∀ j : Fin N,
      sgn (M a j) * sgn (M b j) = 1 - 2 * (if M a j ≠ M b j then (1 : ℤ) else 0) :=
    fun j => sgn_mul_eq_sub (M a j) (M b j)
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.sum_boole]
  have h2 := hM a b hab
  omega

private lemma had_row_dot {N : ℕ} {M : Fin N → Fin N → Bool} (hM : isHad M) (a b : Fin N) :
    ∑ j : Fin N, sgn (M a j) * sgn (M b j) = if a = b then (N : ℤ) else 0 := by
  by_cases h : a = b
  · subst h
    simp [had_row_dot_self]
  · simp [h, had_row_dot_ne hM h]

private lemma had_col_dot {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    (j₁ j₂ : Fin N) :
    ∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) = if j₁ = j₂ then (N : ℤ) else 0 := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  let f : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) :=
    { toFun := fun v i => ∑ j : Fin N, (sgn (M i j) : ℚ) * v j
      map_add' := fun u v => by
        ext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring }
  let g : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) :=
    { toFun := fun v j => (N : ℚ)⁻¹ * ∑ i : Fin N, (sgn (M i j) : ℚ) * v i
      map_add' := fun u v => by
        ext j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum, Finset.mul_sum]
        have hterm : ∀ i : Fin N,
            (N : ℚ)⁻¹ * ((sgn (M i j) : ℚ) * (c * v i)) =
            c * ((N : ℚ)⁻¹ * ((sgn (M i j) : ℚ) * v i)) := fun i => by ring
        simp_rw [hterm, ← Finset.mul_sum] }
  have hfg : ∀ v : Fin N → ℚ, f (g v) = v := by
    intro v
    ext a
    simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
    calc
      ∑ j : Fin N, (sgn (M a j) : ℚ) * ((N : ℚ)⁻¹ * ∑ b : Fin N, (sgn (M b j) : ℚ) * v b)
          = ∑ j : Fin N, ∑ b : Fin N,
              (N : ℚ)⁻¹ * v b * ((sgn (M a j) : ℚ) * (sgn (M b j) : ℚ)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b : Fin N, ∑ j : Fin N,
            (N : ℚ)⁻¹ * v b * ((sgn (M a j) : ℚ) * (sgn (M b j) : ℚ)) := Finset.sum_comm
      _ = ∑ b : Fin N, (N : ℚ)⁻¹ * v b *
            ((∑ j : Fin N, sgn (M a j) * sgn (M b j) : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← Finset.mul_sum]
            push_cast
            rfl
      _ = ∑ b : Fin N, (N : ℚ)⁻¹ * v b * ((if a = b then (N : ℤ) else 0 : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl fun b _ => by rw [had_row_dot hM a b]
      _ = (N : ℚ)⁻¹ * v a * (N : ℚ) := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro b _ hba
              simp [Ne.symm hba]
            · intro h
              exact absurd (Finset.mem_univ a) h
      _ = v a := by
            rw [mul_comm ((N : ℚ)⁻¹), mul_assoc, inv_mul_cancel₀ hNq, mul_one]
  have hsurj : Function.Surjective f := fun v => ⟨g v, hfg v⟩
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  have hgf : ∀ v : Fin N → ℚ, g (f v) = v := fun v => hinj (hfg (f v))
  let e : Fin N → ℚ := fun k => if k = j₂ then 1 else 0
  have he := congr_fun (hgf e) j₁
  simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk] at he
  have hfe : ∀ i : Fin N, ∑ j : Fin N, (sgn (M i j) : ℚ) * e j = (sgn (M i j₂) : ℚ) := by
    intro i
    rw [Finset.sum_eq_single j₂]
    · simp [e]
    · intro j _ hne
      simp [e, hne]
    · intro h
      exact absurd (Finset.mem_univ j₂) h
  simp_rw [hfe] at he
  have hsum :
      (N : ℚ)⁻¹ * ((∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) : ℤ) : ℚ) =
      if j₁ = j₂ then 1 else 0 := by
    push_cast
    simpa only [e] using he
  have hmul : ((∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) : ℤ) : ℚ) =
      ((if j₁ = j₂ then (N : ℤ) else 0 : ℤ) : ℚ) := by
    have h1 := congr_arg (fun t => (N : ℚ) * t) hsum
    simp only [← mul_assoc, mul_inv_cancel₀ hNq, one_mul] at h1
    by_cases hj : j₁ = j₂
    · simp [hj] at h1 ⊢
      exact h1
    · simp [hj] at h1 ⊢
      exact h1
  exact Int.cast_injective hmul

private lemma had_transpose {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M) :
    isHad (fun j i => M i j) := by
  intro a b hab
  dsimp only
  have h0 := had_col_dot hN hM a b
  simp only [hab, ↓reduceIte] at h0
  have h1 : ∀ i : Fin N,
      sgn (M i a) * sgn (M i b) = 1 - 2 * (if M i a ≠ M i b then (1 : ℤ) else 0) :=
    fun i => sgn_mul_eq_sub (M i a) (M i b)
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum] at h0
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.sum_boole] at h0
  omega

private lemma had_row_flip_count {N : ℕ} {M : Fin N → Fin N → Bool} (hM : isHad M)
    {a b : Fin N} (hab : a ≠ b) (s : Bool) :
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor s (M b j))).card = N := by
  cases s
  · simpa using hM a b hab
  · have hdisj : Disjoint
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j)))
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      cases ha : M a j <;> cases hb : M b j <;> simp_all
    have hunion :
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j))) ∪
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)) = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases M a j <;> cases M b j <;> decide
    have hpart :
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j))).card +
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have h0 := hM a b hab
    omega

private lemma had_col_flip_count {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    {a b : Fin N} (hab : a ≠ b) (s : Bool) :
    2 * ((Finset.univ : Finset (Fin N)).filter (fun i => M i a ≠ xor s (M i b))).card = N :=
  had_row_flip_count (had_transpose hN hM) hab s

private lemma had_row_expand {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    (z : Fin N → ℤ) (j : Fin N) :
    (N : ℤ) * z j = ∑ a : Fin N, (∑ t : Fin N, z t * sgn (M a t)) * sgn (M a j) := by
  calc
    (N : ℤ) * z j = ∑ t : Fin N, z t * (if t = j then (N : ℤ) else 0) := by
      simp [mul_comm]
    _ = ∑ t : Fin N, z t * (∑ a : Fin N, sgn (M a t) * sgn (M a j)) := by
      refine Finset.sum_congr rfl fun t _ => by rw [had_col_dot hN hM t j]
    _ = ∑ t : Fin N, ∑ a : Fin N, z t * (sgn (M a t) * sgn (M a j)) := by
      refine Finset.sum_congr rfl fun t _ => Finset.mul_sum ..
    _ = ∑ a : Fin N, ∑ t : Fin N, z t * (sgn (M a t) * sgn (M a j)) := Finset.sum_comm
    _ = ∑ a : Fin N, (∑ t : Fin N, z t * sgn (M a t)) * sgn (M a j) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => by ring

private lemma had_uncertainty {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    (x : Fin N → ℤ) (hx : x ≠ 0) :
    N ≤ ((Finset.univ : Finset (Fin N)).filter (fun j => x j ≠ 0)).card *
      ((Finset.univ : Finset (Fin N)).filter
        (fun a => ∑ j : Fin N, sgn (M a j) * x j ≠ 0)).card := by
  let y : Fin N → ℤ := fun a => ∑ j : Fin N, sgn (M a j) * x j
  let A : Finset (Fin N) := Finset.univ.filter (fun j => x j ≠ 0)
  let B : Finset (Fin N) := Finset.univ.filter (fun a => y a ≠ 0)
  have hpar : ∑ a : Fin N, y a ^ 2 = (N : ℤ) * ∑ j : Fin N, x j ^ 2 := by
    calc
      ∑ a : Fin N, y a ^ 2
          = ∑ a : Fin N, ∑ j₁ : Fin N, ∑ j₂ : Fin N,
              (x j₁ * x j₂) * (sgn (M a j₁) * sgn (M a j₂)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [y, sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j₁ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j₂ _ => by ring
      _ = ∑ j₁ : Fin N, ∑ a : Fin N, ∑ j₂ : Fin N,
            (x j₁ * x j₂) * (sgn (M a j₁) * sgn (M a j₂)) := Finset.sum_comm
      _ = ∑ j₁ : Fin N, ∑ j₂ : Fin N, ∑ a : Fin N,
            (x j₁ * x j₂) * (sgn (M a j₁) * sgn (M a j₂)) := by
            refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_comm
      _ = ∑ j₁ : Fin N, ∑ j₂ : Fin N,
            (x j₁ * x j₂) * (∑ a : Fin N, sgn (M a j₁) * sgn (M a j₂)) := by
            refine Finset.sum_congr rfl fun j₁ _ =>
              Finset.sum_congr rfl fun j₂ _ => (Finset.mul_sum ..).symm
      _ = ∑ j₁ : Fin N, ∑ j₂ : Fin N,
            (x j₁ * x j₂) * (if j₁ = j₂ then (N : ℤ) else 0) := by
            refine Finset.sum_congr rfl fun j₁ _ =>
              Finset.sum_congr rfl fun j₂ _ => by rw [had_col_dot hN hM j₁ j₂]
      _ = ∑ j₁ : Fin N, (N : ℤ) * x j₁ ^ 2 := by
            refine Finset.sum_congr rfl fun j₁ _ => ?_
            rw [Finset.sum_eq_single j₁]
            · simp [sq, mul_comm]
            · intro j₂ _ hne
              simp [Ne.symm hne]
            · intro h
              exact absurd (Finset.mem_univ j₁) h
      _ = (N : ℤ) * ∑ j : Fin N, x j ^ 2 := (Finset.mul_sum ..).symm
  have hy_bound : ∀ a : Fin N, |y a| ≤ ∑ j ∈ A, |x j| := by
    intro a
    calc
      |y a| ≤ ∑ j : Fin N, |sgn (M a j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin N, |x j| := by
            refine Finset.sum_congr rfl fun j _ => by rw [abs_mul, sgn_abs, one_mul]
      _ = ∑ j ∈ A, |x j| := by
            symm
            refine Finset.sum_subset (Finset.subset_univ A) ?_
            intro j _ hj
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
            simp [hj]
  have hy2 : ∑ a : Fin N, y a ^ 2 ≤ (B.card : ℤ) * (∑ j ∈ A, |x j|) ^ 2 := by
    have hsub : ∑ a : Fin N, y a ^ 2 = ∑ a ∈ B, y a ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ B) ?_
      intro a _ ha
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
      simp [ha]
    rw [hsub]
    calc
      ∑ a ∈ B, y a ^ 2 ≤ ∑ _a ∈ B, (∑ j ∈ A, |x j|) ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hy_bound a) 2
      _ = (B.card : ℤ) * (∑ j ∈ A, |x j|) ^ 2 := by simp
  have hcs : (∑ j ∈ A, |x j|) ^ 2 ≤ (A.card : ℤ) * ∑ j : Fin N, x j ^ 2 := by
    have hnn : (0 : ℤ) ≤ ∑ j₁ ∈ A, ∑ j₂ ∈ A, (|x j₁| - |x j₂|) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp :
        ∑ j₁ ∈ A, ∑ j₂ ∈ A, (|x j₁| - |x j₂|) ^ 2 =
        2 * ((A.card : ℤ) * ∑ j ∈ A, |x j| ^ 2 - (∑ j ∈ A, |x j|) ^ 2) := by
      have h1 : ∀ j₁ j₂ : Fin N,
          (|x j₁| - |x j₂|) ^ 2 = |x j₁| ^ 2 + |x j₂| ^ 2 - 2 * (|x j₁| * |x j₂|) :=
        fun j₁ j₂ => by ring
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hA_le : (∑ j ∈ A, |x j|) ^ 2 ≤ (A.card : ℤ) * ∑ j ∈ A, x j ^ 2 := by
      have h2 : (∑ j ∈ A, |x j|) ^ 2 ≤ (A.card : ℤ) * ∑ j ∈ A, |x j| ^ 2 := by linarith
      simpa [sq_abs] using h2
    exact le_trans hA_le (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ => sq_nonneg _))
      (Nat.cast_nonneg _))
  have hQ : 0 < ∑ j : Fin N, x j ^ 2 := by
    have hex : ∃ j : Fin N, x j ≠ 0 := Function.ne_iff.mp hx
    rcases hex with ⟨j₀, hj₀⟩
    have hpos : 0 < x j₀ ^ 2 := sq_pos_of_ne_zero hj₀
    exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (f := fun j => x j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j₀))
  have hkey : (N : ℤ) * ∑ j : Fin N, x j ^ 2 ≤
      ((A.card * B.card : ℕ) : ℤ) * ∑ j : Fin N, x j ^ 2 := by
    rw [← hpar]
    calc
      ∑ a : Fin N, y a ^ 2 ≤ (B.card : ℤ) * (∑ j ∈ A, |x j|) ^ 2 := hy2
      _ ≤ (B.card : ℤ) * ((A.card : ℤ) * ∑ j : Fin N, x j ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
      _ = ((A.card * B.card : ℕ) : ℤ) * ∑ j : Fin N, x j ^ 2 := by
            push_cast
            ring
  have hle : (N : ℤ) ≤ ((A.card * B.card : ℕ) : ℤ) := le_of_mul_le_mul_right hkey hQ
  exact_mod_cast hle

private lemma extend_partial_bij {β : Type*} [Fintype β] [DecidableEq β]
    (S T : Finset β) (e1 : S ≃ T) :
    ∃ π : Equiv.Perm β, ∀ x (hx : x ∈ S), π x = (e1 ⟨x, hx⟩).1 := by
  have hcardST : S.card = T.card := by
    have h1 := Fintype.card_congr e1
    simpa [Fintype.card_coe] using h1
  have hcardC : Fintype.card (Sᶜ : Finset β) = Fintype.card (Tᶜ : Finset β) := by
    simp only [Fintype.card_coe, Finset.card_compl, hcardST]
  let e2 : (Sᶜ : Finset β) ≃ (Tᶜ : Finset β) := Fintype.equivOfCardEq hcardC
  let f : β → β := fun x =>
    if hx : x ∈ S then (e1 ⟨x, hx⟩).1 else (e2 ⟨x, Finset.mem_compl.mpr hx⟩).1
  have hinj : Function.Injective f := by
    intro x₁ x₂ h
    by_cases hx₁ : x₁ ∈ S <;> by_cases hx₂ : x₂ ∈ S
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hsub : e1 ⟨x₁, hx₁⟩ = e1 ⟨x₂, hx₂⟩ := Subtype.ext h
      exact congr_arg Subtype.val (e1.injective hsub)
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hm1 : (e1 ⟨x₁, hx₁⟩).1 ∈ T := (e1 ⟨x₁, hx₁⟩).2
      have hm2 : (e2 ⟨x₂, Finset.mem_compl.mpr hx₂⟩).1 ∈ Tᶜ :=
        (e2 ⟨x₂, Finset.mem_compl.mpr hx₂⟩).2
      rw [h] at hm1
      exact absurd hm1 (Finset.mem_compl.mp hm2)
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hm1 : (e2 ⟨x₁, Finset.mem_compl.mpr hx₁⟩).1 ∈ Tᶜ :=
        (e2 ⟨x₁, Finset.mem_compl.mpr hx₁⟩).2
      have hm2 : (e1 ⟨x₂, hx₂⟩).1 ∈ T := (e1 ⟨x₂, hx₂⟩).2
      rw [← h] at hm2
      exact absurd hm2 (Finset.mem_compl.mp hm1)
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hsub : e2 ⟨x₁, Finset.mem_compl.mpr hx₁⟩ = e2 ⟨x₂, Finset.mem_compl.mpr hx₂⟩ :=
        Subtype.ext h
      exact congr_arg Subtype.val (e2.injective hsub)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  intro x hx
  simp only [Equiv.ofBijective_apply, f, hx, ↓reduceDIte]

private lemma extend_injOn_perm {N : ℕ} (S : Finset (Fin N)) (f : Fin N → Fin N)
    (hinj : Set.InjOn f S) :
    ∃ p : Equiv.Perm (Fin N), ∀ x ∈ S, p x = f x := by
  let T : Finset (Fin N) := S.image f
  let g : S → T := fun x => ⟨f x.1, Finset.mem_image_of_mem f x.2⟩
  have hginj : Function.Injective g := by
    intro x₁ x₂ h
    exact Subtype.ext (hinj x₁.2 x₂.2 (congr_arg Subtype.val h))
  have hgsurj : Function.Surjective g := by
    intro y
    rcases Finset.mem_image.mp y.2 with ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  rcases extend_partial_bij S T (Equiv.ofBijective g ⟨hginj, hgsurj⟩) with ⟨p, hp⟩
  exact ⟨p, fun x hx => hp x hx⟩

private lemma extend_perm_on_finset {N : ℕ} (C : Finset (Fin N))
    (eC : Fin C.card ≃ C) (σ : Equiv.Perm (Fin C.card)) :
    ∃ c : Equiv.Perm (Fin N),
      (∀ j ∉ C, c j = j) ∧
      ∀ j (hj : j ∈ C), c j = (eC (σ (eC.symm ⟨j, hj⟩))).1 := by
  let f : Fin N → Fin N := fun j =>
    if hj : j ∈ C then (eC (σ (eC.symm ⟨j, hj⟩))).1 else j
  have hinj : Function.Injective f := by
    intro j₁ j₂ h
    by_cases h1 : j₁ ∈ C <;> by_cases h2 : j₂ ∈ C
    · simp only [f, h1, h2, ↓reduceDIte] at h
      have hs : eC (σ (eC.symm ⟨j₁, h1⟩)) = eC (σ (eC.symm ⟨j₂, h2⟩)) := Subtype.ext h
      have hs2 := eC.symm.injective (σ.injective (eC.injective hs))
      exact congr_arg Subtype.val hs2
    · simp only [f, h1, h2, ↓reduceDIte] at h
      have hm : (eC (σ (eC.symm ⟨j₁, h1⟩))).1 ∈ C := (eC (σ (eC.symm ⟨j₁, h1⟩))).2
      rw [h] at hm
      exact absurd hm h2
    · simp only [f, h1, h2, ↓reduceDIte] at h
      have hm : (eC (σ (eC.symm ⟨j₂, h2⟩))).1 ∈ C := (eC (σ (eC.symm ⟨j₂, h2⟩))).2
      rw [← h] at hm
      exact absurd hm h1
    · simp only [f, h1, h2, ↓reduceDIte] at h
      exact h
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_, ?_⟩
  · intro j hj
    simp only [Equiv.ofBijective_apply, f, hj, ↓reduceDIte]
  · intro j hj
    simp only [Equiv.ofBijective_apply, f, hj, ↓reduceDIte]

private def evenVec (a : Fin 4) (t : Fin 3) : Bool :=
  match a.val with
  | 0 => false
  | 1 => decide (t ≠ 0)
  | 2 => decide (t ≠ 1)
  | _ => decide (t ≠ 2)

private def xor4 (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, _ => b
  | _, 0 => a
  | 1, 1 => 0
  | 1, 2 => 3
  | 1, 3 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 1 => 2
  | 3, 2 => 1
  | _, _ => 0

private lemma xor4_self (a : Fin 4) : xor4 a a = 0 := by
  fin_cases a <;> rfl

private lemma xor4_zero_left (a : Fin 4) : xor4 0 a = a := by
  fin_cases a <;> rfl

private lemma xor4_assoc (a b c : Fin 4) : xor4 a (xor4 b c) = xor4 (xor4 a b) c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

private lemma evenVec_xor4 (a b : Fin 4) (t : Fin 3) :
    evenVec (xor4 a b) t = xor (evenVec a t) (evenVec b t) := by
  fin_cases a <;> fin_cases b <;> fin_cases t <;> rfl

private lemma evenVec_succ (r t : Fin 3) :
    evenVec r.succ t = decide (t ≠ r) := by
  fin_cases r <;> fin_cases t <;> rfl

private lemma evenVec_dot (a b : Fin 4) :
    ∑ t : Fin 3, sgn (evenVec a t) * sgn (evenVec b t) = if a = b then 3 else -1 := by
  fin_cases a <;> fin_cases b <;> decide

private def par3 (v : Fin 3 → Bool) : Bool :=
  xor (v 0) (xor (v 1) (v 2))

private def code3 (v : Fin 3 → Bool) : Fin 4 :=
  match xor (par3 v) (v 0), xor (par3 v) (v 1) with
  | false, false => 0
  | false, true  => 1
  | true,  false => 2
  | true,  true  => 3

private lemma vec3_decomp (v : Fin 3 → Bool) (t : Fin 3) :
    v t = xor (par3 v) (evenVec (code3 v) t) := by
  have h : ∀ (b0 b1 b2 : Bool) (t : Fin 3),
      v 0 = b0 → v 1 = b1 → v 2 = b2 →
      v t = xor (par3 v) (evenVec (code3 v) t) := by
    intro b0 b1 b2 t h0 h1 h2
    fin_cases t
    · change v 0 = xor (par3 v) (evenVec (code3 v) 0)
      simp only [par3, code3, h0, h1, h2]
      cases b0 <;> cases b1 <;> cases b2 <;> rfl
    · change v 1 = xor (par3 v) (evenVec (code3 v) 1)
      simp only [par3, code3, h0, h1, h2]
      cases b0 <;> cases b1 <;> cases b2 <;> rfl
    · change v 2 = xor (par3 v) (evenVec (code3 v) 2)
      simp only [par3, code3, h0, h1, h2]
      cases b0 <;> cases b1 <;> cases b2 <;> rfl
  exact h (v 0) (v 1) (v 2) t rfl rfl rfl

private lemma dot3_formula (u v : Fin 3 → Bool) :
    ∑ t : Fin 3, sgn (u t) * sgn (v t) =
      sgn (par3 u) * sgn (par3 v) * (if code3 u = code3 v then 3 else -1) := by
  have h1 : ∀ t : Fin 3,
      sgn (u t) * sgn (v t) =
        sgn (par3 u) * sgn (par3 v) * (sgn (evenVec (code3 u) t) * sgn (evenVec (code3 v) t)) := by
    intro t
    rw [vec3_decomp u t, vec3_decomp v t, sgn_xor, sgn_xor]
    ring
  simp_rw [h1, ← Finset.mul_sum, evenVec_dot]

private lemma dot3_eq_iff (u v u' v' : Fin 3 → Bool)
    (h : ∑ t : Fin 3, sgn (u t) * sgn (v t) = ∑ t : Fin 3, sgn (u' t) * sgn (v' t)) :
    (code3 u = code3 v ↔ code3 u' = code3 v') ∧ (par3 u = par3 v ↔ par3 u' = par3 v') := by
  rw [dot3_formula, dot3_formula] at h
  by_cases hc1 : code3 u = code3 v <;> by_cases hc2 : code3 u' = code3 v' <;>
    cases hp1 : par3 u <;> cases hp2 : par3 v <;>
    cases hp3 : par3 u' <;> cases hp4 : par3 v' <;>
    simp [hc1, hc2, hp1, hp2, hp3, hp4, sgn] at h ⊢

private lemma realize_perm_fin4 (π : Equiv.Perm (Fin 4)) (s : Bool) :
    ∃ (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → Bool),
      ∀ v : Fin 3 → Bool, ∀ t : Fin 3,
        xor (w t) (v (σ t)) = xor (xor s (par3 v)) (evenVec (π (code3 v)) t) := by
  let j : Fin 4 := π 0
  let π' : Fin 4 → Fin 4 := fun i => xor4 j (π i)
  have hπ'0 : π' 0 = 0 := xor4_self j
  have hπ'inj : Function.Injective π' := by
    intro a b h
    have h1 := congr_arg (xor4 j) h
    simp only [π', xor4_assoc, xor4_self, xor4_zero_left] at h1
    exact π.injective h1
  have hne0 : ∀ r : Fin 3, π' r.succ ≠ 0 := by
    intro r h
    rw [← hπ'0] at h
    exact Fin.succ_ne_zero r (hπ'inj h)
  let τ_fun : Fin 3 → Fin 3 := fun r => (π' r.succ).pred (hne0 r)
  have hτ_succ : ∀ r : Fin 3, (τ_fun r).succ = π' r.succ := fun r => Fin.succ_pred _ _
  have hτ_inj : Function.Injective τ_fun := by
    intro r₁ r₂ h
    have h1 := congr_arg Fin.succ h
    rw [hτ_succ, hτ_succ] at h1
    exact Fin.succ_injective _ (hπ'inj h1)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective τ_fun (Finite.injective_iff_bijective.mp hτ_inj)
  let σ : Equiv.Perm (Fin 3) := τ.symm
  let w : Fin 3 → Bool := fun t => xor s (evenVec j t)
  have hact_even : ∀ i : Fin 4, ∀ t : Fin 3,
      xor (evenVec j t) (evenVec i (σ t)) = evenVec (π i) t := by
    intro i t
    refine Fin.cases ?_ ?_ i
    · have h0 : evenVec 0 (σ t) = false := rfl
      rw [h0, Bool.xor_false]
    · intro r
      rw [evenVec_succ]
      have hdec : decide (σ t ≠ r) = decide (t ≠ τ r) := by
        simp only [σ, ne_eq, Equiv.symm_apply_eq]
      rw [hdec, ← evenVec_succ (τ r) t]
      have hsucc : (τ r).succ = xor4 j (π r.succ) := hτ_succ r
      rw [hsucc, ← evenVec_xor4, xor4_assoc, xor4_self, xor4_zero_left]
  refine ⟨σ, w, ?_⟩
  intro v t
  rw [vec3_decomp v (σ t)]
  have hx : xor (xor s (evenVec j t)) (xor (par3 v) (evenVec (code3 v) (σ t))) =
      xor (xor s (par3 v)) (xor (evenVec j t) (evenVec (code3 v) (σ t))) := by
    cases s <;> cases evenVec j t <;> cases par3 v <;> cases evenVec (code3 v) (σ t) <;> rfl
  change xor (xor s (evenVec j t)) (xor (par3 v) (evenVec (code3 v) (σ t))) = _
  rw [hx, hact_even (code3 v) t]

private lemma bool2_unique :
    ∀ a0 a1 b0 b1 c0 c1 : Bool,
      c0 ≠ c1 →
      sgn a0 + sgn a1 = sgn b0 + sgn b1 →
      sgn a0 * sgn c0 + sgn a1 * sgn c1 = sgn b0 * sgn c0 + sgn b1 * sgn c1 →
      a0 = b0 ∧ a1 = b1 := by
  decide

private lemma bool2_diag :
    ∀ a0 a1 b0 b1 : Bool,
      a0 = a1 →
      sgn a0 + sgn a1 = sgn b0 + sgn b1 →
      a0 = b0 ∧ a1 = b1 := by
  decide

private lemma bool2_swap :
    ∀ a0 a1 b0 b1 : Bool,
      a0 ≠ a1 →
      sgn a0 + sgn a1 = sgn b0 + sgn b1 →
      (if a0 = b0 then b0 else b1) = a0 ∧ (if a0 = b0 then b1 else b0) = a1 := by
  decide

private lemma xor_cancel_align :
    ∀ a b c d : Bool, xor a c = xor b d → c = xor (xor a b) d := by
  decide

private lemma align_gram_two {α : Type*} (x y : α → Fin 2 → Bool)
    (hgram : ∀ a b : α,
      ∑ t : Fin 2, sgn (x a t) * sgn (x b t) = ∑ t : Fin 2, sgn (y a t) * sgn (y b t)) :
    ∃ (σ : Equiv.Perm (Fin 2)) (w : Fin 2 → Bool),
      ∀ a : α, ∀ t : Fin 2, x a t = xor (w t) (y a (σ t)) := by
  by_cases hne : Nonempty α
  · rcases hne with ⟨a₀⟩
    let x' : α → Fin 2 → Bool := fun a t => xor (x a₀ t) (x a t)
    let y' : α → Fin 2 → Bool := fun a t => xor (y a₀ t) (y a t)
    have hgram' : ∀ a b : α,
        ∑ t : Fin 2, sgn (x' a t) * sgn (x' b t) =
        ∑ t : Fin 2, sgn (y' a t) * sgn (y' b t) := by
      intro a b
      have hx : ∀ t : Fin 2, sgn (x' a t) * sgn (x' b t) = sgn (x a t) * sgn (x b t) := by
        intro t
        simp only [x', sgn_xor]
        have hsq := sgn_mul_self (x a₀ t)
        calc
          sgn (x a₀ t) * sgn (x a t) * (sgn (x a₀ t) * sgn (x b t))
              = (sgn (x a₀ t) * sgn (x a₀ t)) * (sgn (x a t) * sgn (x b t)) := by ring
          _ = sgn (x a t) * sgn (x b t) := by rw [hsq, one_mul]
      have hy : ∀ t : Fin 2, sgn (y' a t) * sgn (y' b t) = sgn (y a t) * sgn (y b t) := by
        intro t
        simp only [y', sgn_xor]
        have hsq := sgn_mul_self (y a₀ t)
        calc
          sgn (y a₀ t) * sgn (y a t) * (sgn (y a₀ t) * sgn (y b t))
              = (sgn (y a₀ t) * sgn (y a₀ t)) * (sgn (y a t) * sgn (y b t)) := by ring
          _ = sgn (y a t) * sgn (y b t) := by rw [hsq, one_mul]
      simp_rw [hx, hy]
      exact hgram a b
    have hx0 : ∀ t : Fin 2, x' a₀ t = false := fun t => Bool.xor_self (x a₀ t)
    have hy0 : ∀ t : Fin 2, y' a₀ t = false := fun t => Bool.xor_self (y a₀ t)
    have hsum0 : ∀ a : α, sgn (x' a 0) + sgn (x' a 1) = sgn (y' a 0) + sgn (y' a 1) := by
      intro a
      have h := hgram' a a₀
      simp only [Fin.sum_univ_two, hx0, hy0, sgn_false, mul_one] at h
      exact h
    by_cases h1 : ∃ a₁ : α, x' a₁ 0 ≠ x' a₁ 1
    · rcases h1 with ⟨a₁, ha₁⟩
      let σ : Equiv.Perm (Fin 2) :=
        if x' a₁ 0 = y' a₁ 0 then Equiv.refl _ else Equiv.swap 0 1
      let y'' : α → Fin 2 → Bool := fun a t => y' a (σ t)
      have hgram'' : ∀ a b : α,
          sgn (x' a 0) * sgn (x' b 0) + sgn (x' a 1) * sgn (x' b 1) =
          sgn (y'' a 0) * sgn (y'' b 0) + sgn (y'' a 1) * sgn (y'' b 1) := by
        intro a b
        have h := hgram' a b
        simp only [Fin.sum_univ_two] at h
        by_cases hc : x' a₁ 0 = y' a₁ 0
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.refl_apply]
          exact h
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.swap_apply_left, Equiv.swap_apply_right]
          linarith
      have hy''0 : y'' a₀ 0 = false ∧ y'' a₀ 1 = false := ⟨hy0 (σ 0), hy0 (σ 1)⟩
      have hy''1 : y'' a₁ 0 = x' a₁ 0 ∧ y'' a₁ 1 = x' a₁ 1 := by
        have hsw := bool2_swap (x' a₁ 0) (x' a₁ 1) (y' a₁ 0) (y' a₁ 1) ha₁ (hsum0 a₁)
        by_cases hc : x' a₁ 0 = y' a₁ 0
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.refl_apply] at hsw ⊢
          exact hsw
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.swap_apply_left, Equiv.swap_apply_right] at hsw ⊢
          exact hsw
      have hxy : ∀ a : α, ∀ t : Fin 2, x' a t = y'' a t := by
        intro a t
        have hg0 := hgram'' a a₀
        have hg1 := hgram'' a a₁
        rw [hx0 0, hx0 1, hy''0.1, hy''0.2, sgn_false, mul_one, mul_one, mul_one, mul_one] at hg0
        rw [hy''1.1, hy''1.2] at hg1
        have hpair := bool2_unique (x' a 0) (x' a 1) (y'' a 0) (y'' a 1)
          (x' a₁ 0) (x' a₁ 1) ha₁ hg0 hg1
        fin_cases t
        · exact hpair.1
        · exact hpair.2
      refine ⟨σ, fun t => xor (x a₀ t) (y a₀ (σ t)), ?_⟩
      intro a t
      exact xor_cancel_align (x a₀ t) (y a₀ (σ t)) (x a t) (y a (σ t)) (hxy a t)
    · push Not at h1
      refine ⟨Equiv.refl _, fun t => xor (x a₀ t) (y a₀ t), ?_⟩
      intro a t
      have hpair := bool2_diag (x' a 0) (x' a 1) (y' a 0) (y' a 1) (h1 a) (hsum0 a)
      have ht : x' a t = y' a t := by
        fin_cases t
        · exact hpair.1
        · exact hpair.2
      exact xor_cancel_align (x a₀ t) (y a₀ t) (x a t) (y a t) ht
  · exact ⟨Equiv.refl _, fun _ => false, fun a => False.elim (hne ⟨a⟩)⟩

private lemma align_gram_three {α : Type*} (x y : α → Fin 3 → Bool)
    (hgram : ∀ a b : α,
      ∑ t : Fin 3, sgn (x a t) * sgn (x b t) = ∑ t : Fin 3, sgn (y a t) * sgn (y b t)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → Bool),
      ∀ a : α, ∀ t : Fin 3, x a t = xor (w t) (y a (σ t)) := by
  classical
  by_cases hne : Nonempty α
  · rcases hne with ⟨a₀⟩
    have hiff : ∀ a b : α,
        (code3 (x a) = code3 (x b) ↔ code3 (y a) = code3 (y b)) ∧
        (par3 (x a) = par3 (x b) ↔ par3 (y a) = par3 (y b)) :=
      fun a b => dot3_eq_iff (x a) (x b) (y a) (y b) (hgram a b)
    let s : Bool := xor (par3 (x a₀)) (par3 (y a₀))
    have hpar : ∀ a : α, par3 (x a) = xor s (par3 (y a)) := by
      intro a
      have hp := (hiff a a₀).2
      simp only [s]
      cases h1 : par3 (x a) <;> cases h2 : par3 (x a₀) <;>
        cases h3 : par3 (y a) <;> cases h4 : par3 (y a₀) <;>
        simp_all
    let imgY : Finset (Fin 4) := Finset.univ.filter (fun u => ∃ a : α, code3 (y a) = u)
    let imgX : Finset (Fin 4) := Finset.univ.filter (fun u => ∃ a : α, code3 (x a) = u)
    have hmemY : ∀ u : Fin 4, u ∈ imgY ↔ ∃ a : α, code3 (y a) = u := by
      intro u
      simp [imgY]
    have hmemX : ∀ u : Fin 4, u ∈ imgX ↔ ∃ a : α, code3 (x a) = u := by
      intro u
      simp [imgX]
    let toFun : imgY → imgX := fun u =>
      ⟨code3 (x (Classical.choose ((hmemY u.1).mp u.2))),
       (hmemX _).mpr ⟨Classical.choose ((hmemY u.1).mp u.2), rfl⟩⟩
    let invFun : imgX → imgY := fun u =>
      ⟨code3 (y (Classical.choose ((hmemX u.1).mp u.2))),
       (hmemY _).mpr ⟨Classical.choose ((hmemX u.1).mp u.2), rfl⟩⟩
    have hto_eq : ∀ (u : imgY) (a : α), code3 (y a) = u.1 → (toFun u).1 = code3 (x a) := by
      intro u a ha
      have hc : code3 (y (Classical.choose ((hmemY u.1).mp u.2))) = u.1 :=
        Classical.choose_spec ((hmemY u.1).mp u.2)
      exact ((hiff _ a).1).mpr (hc.trans ha.symm)
    have hinv_eq : ∀ (u : imgX) (a : α), code3 (x a) = u.1 → (invFun u).1 = code3 (y a) := by
      intro u a ha
      have hc : code3 (x (Classical.choose ((hmemX u.1).mp u.2))) = u.1 :=
        Classical.choose_spec ((hmemX u.1).mp u.2)
      exact ((hiff _ a).1).mp (hc.trans ha.symm)
    let e1 : imgY ≃ imgX :=
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro u
          rcases (hmemY u.1).mp u.2 with ⟨a, ha⟩
          apply Subtype.ext
          rw [hinv_eq (toFun u) a (hto_eq u a ha).symm, ha]
        right_inv := by
          intro u
          rcases (hmemX u.1).mp u.2 with ⟨a, ha⟩
          apply Subtype.ext
          rw [hto_eq (invFun u) a (hinv_eq u a ha).symm, ha] }
    rcases extend_partial_bij imgY imgX e1 with ⟨π, hπ⟩
    have hπa : ∀ a : α, π (code3 (y a)) = code3 (x a) := by
      intro a
      have hm : code3 (y a) ∈ imgY := (hmemY _).mpr ⟨a, rfl⟩
      rw [hπ (code3 (y a)) hm]
      exact hto_eq ⟨code3 (y a), hm⟩ a rfl
    rcases realize_perm_fin4 π s with ⟨σ, w, hreal⟩
    refine ⟨σ, w, ?_⟩
    intro a t
    rw [hreal (y a) t, ← hpar a, hπa a, ← vec3_decomp (x a) t]
  · exact ⟨Equiv.refl _, fun _ => false, fun a => False.elim (hne ⟨a⟩)⟩

private lemma align_gram {α : Type*} {k : ℕ} (hk : k ≤ 3)
    (x y : α → Fin k → Bool)
    (hgram : ∀ a b : α,
      ∑ t : Fin k, sgn (x a t) * sgn (x b t) =
      ∑ t : Fin k, sgn (y a t) * sgn (y b t)) :
    ∃ (σ : Equiv.Perm (Fin k)) (w : Fin k → Bool),
      ∀ a : α, ∀ t : Fin k, x a t = xor (w t) (y a (σ t)) := by
  match k with
  | 0 =>
    exact ⟨Equiv.refl _, fun t => Fin.elim0 t, fun _ t => Fin.elim0 t⟩
  | 1 =>
    by_cases hne : Nonempty α
    · rcases hne with ⟨a₀⟩
      refine ⟨Equiv.refl _, fun _ => xor (x a₀ 0) (y a₀ 0), ?_⟩
      intro a t
      fin_cases t
      have h := hgram a a₀
      simp only [Fin.sum_univ_one] at h
      have hs : sgn (x a 0) = sgn (xor (xor (x a₀ 0) (y a₀ 0)) (y a 0)) := by
        rw [sgn_xor, sgn_xor]
        have hsq := sgn_mul_self (x a₀ 0)
        calc
          sgn (x a 0) = sgn (x a 0) * sgn (x a₀ 0) * sgn (x a₀ 0) := by
            rw [mul_assoc, hsq, mul_one]
          _ = sgn (y a 0) * sgn (y a₀ 0) * sgn (x a₀ 0) := by rw [h]
          _ = sgn (x a₀ 0) * sgn (y a₀ 0) * sgn (y a 0) := by ring
      exact sgn_inj hs
    · exact ⟨Equiv.refl _, fun _ => false, fun a => False.elim (hne ⟨a⟩)⟩
  | 2 => exact align_gram_two x y hgram
  | 3 => exact align_gram_three x y hgram
  | _ + 4 => omega

private lemma had_col_signed_perm {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    (c : Equiv.Perm (Fin N)) (v : Fin N → Bool) :
    isHad (fun i j => xor (v j) (D i (c j))) := by
  intro a b hab
  have hcard :
      ((Finset.univ : Finset (Fin N)).filter
        (fun j => xor (v j) (D a (c j)) ≠ xor (v j) (D b (c j)))).card =
      ((Finset.univ : Finset (Fin N)).filter (fun j => D a j ≠ D b j)).card := by
    refine Finset.card_bij (fun j _ => c j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro heq
      exact hj (by rw [heq])
    · intro j₁ _ j₂ _ h
      exact c.injective h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨c.symm j, ?_, c.apply_symm_apply j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, c.apply_symm_apply]
      intro heq
      have hx := congr_arg (xor (v (c.symm j))) heq
      simp only [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor] at hx
      exact hj hx
  rw [hcard]
  exact hD a b hab

private lemma had_row_signed_perm {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    (r : Equiv.Perm (Fin N)) (u : Fin N → Bool) :
    isHad (fun i j => xor (u i) (D (r i) j)) := by
  intro a b hab
  have hrab : r a ≠ r b := fun h => hab (r.injective h)
  have heq :
      (Finset.univ : Finset (Fin N)).filter
        (fun j => xor (u a) (D (r a) j) ≠ xor (u b) (D (r b) j)) =
      (Finset.univ : Finset (Fin N)).filter
        (fun j => D (r a) j ≠ xor (xor (u a) (u b)) (D (r b) j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases u a <;> cases u b <;> cases D (r a) j <;> cases D (r b) j <;> decide
  rw [heq]
  exact had_row_flip_count hD hrab (xor (u a) (u b))

private lemma had_sample_perm {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    (r c : Equiv.Perm (Fin N)) (u v : Fin N → Bool) :
    isHad (sampleFn D r c u v) := by
  have h1 := had_row_signed_perm (had_col_signed_perm hD c v) r u
  have hfun : (fun i j => xor (u i) (xor (v j) (D (r i) (c j)))) = sampleFn D r c u v := by
    ext i j
    simp only [sampleFn, Bool.xor_assoc]
  rwa [hfun] at h1

private lemma quad_dot_zero {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    {R : Finset (Fin N)} (hR : R.card ≤ 3)
    {a b p q : Fin N} (ha : a ∈ R) (hb : b ∈ R) (hp : p ∈ R) (hq : q ∈ R)
    (hab : a ≠ b) (hpq : p ≠ q) (h1 : ¬(p = a ∧ q = b)) (h2 : ¬(p = b ∧ q = a)) :
    ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j) = 0 := by
  have hshare : p = a ∨ p = b ∨ q = a ∨ q = b := by
    by_contra h
    push Not at h
    rcases h with ⟨hpa, hpb, hqa, hqb⟩
    have hsub : ({a, b, p, q} : Finset (Fin N)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hcard4 : ({a, b, p, q} : Finset (Fin N)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hpq]
      · simp [hpb.symm, hqb.symm]
      · simp [hab, hpa.symm, hqa.symm]
    have hle := Finset.card_le_card hsub
    omega
  rcases hshare with rfl | rfl | rfl | rfl
  · have hqb : b ≠ q := fun h => h1 ⟨rfl, h.symm⟩
    have hsim : ∀ j : Fin N,
        sgn (D p j) * sgn (D b j) * sgn (D p j) * sgn (D q j) = sgn (D b j) * sgn (D q j) := by
      intro j
      calc
        sgn (D p j) * sgn (D b j) * sgn (D p j) * sgn (D q j)
            = (sgn (D p j) * sgn (D p j)) * (sgn (D b j) * sgn (D q j)) := by ring
        _ = sgn (D b j) * sgn (D q j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hqb
  · have hqa : a ≠ q := fun h => h2 ⟨rfl, h.symm⟩
    have hsim : ∀ j : Fin N,
        sgn (D a j) * sgn (D p j) * sgn (D p j) * sgn (D q j) = sgn (D a j) * sgn (D q j) := by
      intro j
      calc
        sgn (D a j) * sgn (D p j) * sgn (D p j) * sgn (D q j)
            = (sgn (D p j) * sgn (D p j)) * (sgn (D a j) * sgn (D q j)) := by ring
        _ = sgn (D a j) * sgn (D q j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hqa
  · have hpb : b ≠ p := fun h => h2 ⟨h.symm, rfl⟩
    have hsim : ∀ j : Fin N,
        sgn (D q j) * sgn (D b j) * sgn (D p j) * sgn (D q j) = sgn (D b j) * sgn (D p j) := by
      intro j
      calc
        sgn (D q j) * sgn (D b j) * sgn (D p j) * sgn (D q j)
            = (sgn (D q j) * sgn (D q j)) * (sgn (D b j) * sgn (D p j)) := by ring
        _ = sgn (D b j) * sgn (D p j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hpb
  · have hpa : a ≠ p := fun h => h1 ⟨h.symm, rfl⟩
    have hsim : ∀ j : Fin N,
        sgn (D a j) * sgn (D q j) * sgn (D p j) * sgn (D q j) = sgn (D a j) * sgn (D p j) := by
      intro j
      calc
        sgn (D a j) * sgn (D q j) * sgn (D p j) * sgn (D q j)
            = (sgn (D q j) * sgn (D q j)) * (sgn (D a j) * sgn (D p j)) := by ring
        _ = sgn (D a j) * sgn (D p j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hpa

private lemma recover_one_row {N : ℕ} (hN : 0 < N)
    {H D : Fin N → Fin N → Bool} {R : Finset (Fin N)}
    (hH : isHad H) (hD : isHad D) (hR : R.card ≤ 3)
    (hagree : ∀ i ∉ R, ∀ j : Fin N, H i j = D i j)
    {i₀ : Fin N} (hi₀ : i₀ ∈ R) :
    ∃ a ∈ R, ∃ s : Bool, ∀ j : Fin N, H i₀ j = xor s (D a j) := by
  let α : Fin N → ℤ := fun a => ∑ t : Fin N, sgn (H i₀ t) * sgn (D a t)
  have hα_out : ∀ a ∉ R, α a = 0 := by
    intro a ha
    have hne : i₀ ≠ a := fun h => ha (h ▸ hi₀)
    have hcongr : ∀ t : Fin N, sgn (H i₀ t) * sgn (D a t) = sgn (H i₀ t) * sgn (H a t) := by
      intro t
      rw [hagree a ha t]
    simp only [α]
    simp_rw [hcongr]
    exact had_row_dot_ne hH hne
  have hexpand : ∀ j : Fin N, (N : ℤ) * sgn (H i₀ j) = ∑ a ∈ R, α a * sgn (D a j) := by
    intro j
    rw [had_row_expand hN hD (fun t => sgn (H i₀ t)) j]
    symm
    refine Finset.sum_subset (Finset.subset_univ R) ?_
    intro a _ ha
    simp [hα_out a ha]
  have hNz : (N : ℤ) ≠ 0 := by omega
  have hparseval : ∑ a ∈ R, α a * α a = (N : ℤ) * (N : ℤ) := by
    have h1 :
        ∑ j : Fin N, ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j)) =
        (N : ℤ) * ((N : ℤ) * (N : ℤ)) := by
      have hterm : ∀ j : Fin N,
          ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j)) = (N : ℤ) * (N : ℤ) := by
        intro j
        calc
          ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j))
              = (N : ℤ) * (N : ℤ) * (sgn (H i₀ j) * sgn (H i₀ j)) := by ring
          _ = (N : ℤ) * (N : ℤ) := by rw [sgn_mul_self, mul_one]
      simp_rw [hterm]
      simp [Finset.sum_const]
    have h2 :
        ∑ j : Fin N, ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j)) =
        (N : ℤ) * ∑ a ∈ R, α a * α a := by
      calc
        ∑ j : Fin N, ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j))
            = ∑ j : Fin N, (∑ a ∈ R, α a * sgn (D a j)) * (∑ b ∈ R, α b * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun j _ => by rw [hexpand j]
        _ = ∑ j : Fin N, ∑ a ∈ R, ∑ b ∈ R,
              (α a * α b) * (sgn (D a j) * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b _ => by ring
        _ = ∑ a ∈ R, ∑ j : Fin N, ∑ b ∈ R,
              (α a * α b) * (sgn (D a j) * sgn (D b j)) := Finset.sum_comm
        _ = ∑ a ∈ R, ∑ b ∈ R, ∑ j : Fin N,
              (α a * α b) * (sgn (D a j) * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ a ∈ R, ∑ b ∈ R, (α a * α b) * (∑ j : Fin N, sgn (D a j) * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun a _ =>
                Finset.sum_congr rfl fun b _ => (Finset.mul_sum ..).symm
        _ = ∑ a ∈ R, ∑ b ∈ R, (α a * α b) * (if a = b then (N : ℤ) else 0) := by
              refine Finset.sum_congr rfl fun a _ =>
                Finset.sum_congr rfl fun b _ => by rw [had_row_dot hD a b]
        _ = ∑ a ∈ R, (N : ℤ) * (α a * α a) := by
              refine Finset.sum_congr rfl fun a ha => ?_
              rw [Finset.sum_eq_single a]
              · simp [mul_comm]
              · intro b _ hba
                simp [Ne.symm hba]
              · intro h
                exact absurd ha h
        _ = (N : ℤ) * ∑ a ∈ R, α a * α a := (Finset.mul_sum ..).symm
    exact mul_left_cancel₀ hNz (h2.symm.trans h1)
  have hoff_zero : ∀ j : Fin N,
      ∑ p ∈ R, ∑ q ∈ R,
        (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j)) = 0 := by
    intro j
    have hsq :
        (∑ p ∈ R, α p * sgn (D p j)) * (∑ q ∈ R, α q * sgn (D q j)) =
        (N : ℤ) * (N : ℤ) := by
      rw [← hexpand j]
      calc
        ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j))
            = (N : ℤ) * (N : ℤ) * (sgn (H i₀ j) * sgn (H i₀ j)) := by ring
        _ = (N : ℤ) * (N : ℤ) := by rw [sgn_mul_self, mul_one]
    have hsplit :
        (∑ p ∈ R, α p * sgn (D p j)) * (∑ q ∈ R, α q * sgn (D q j)) =
        (∑ p ∈ R, α p * α p) +
        ∑ p ∈ R, ∑ q ∈ R,
          (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mul_sum]
      have hterm : ∀ q : Fin N,
          α p * sgn (D p j) * (α q * sgn (D q j)) =
          (if p = q then α p * α p else 0) +
          (if p = q then 0 else α p * α q * sgn (D p j) * sgn (D q j)) := by
        intro q
        by_cases hpq : p = q
        · subst hpq
          simp only [↓reduceIte, add_zero]
          calc
            α p * sgn (D p j) * (α p * sgn (D p j))
                = α p * α p * (sgn (D p j) * sgn (D p j)) := by ring
            _ = α p * α p := by rw [sgn_mul_self, mul_one]
        · simp only [hpq, ↓reduceIte, zero_add]
          ring
      simp_rw [hterm, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hqp
        simp [Ne.symm hqp]
      · intro h
        exact absurd hp h
    rw [hsplit, hparseval] at hsq
    linarith
  have hprod_zero : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → α a * α b = 0 := by
    intro a ha b hb hab
    have hzero :
        ∑ j : Fin N, sgn (D a j) * sgn (D b j) *
          (∑ p ∈ R, ∑ q ∈ R,
            (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j))) = 0 := by
      simp_rw [hoff_zero, mul_zero, Finset.sum_const_zero]
    have hrew :
        ∑ j : Fin N, sgn (D a j) * sgn (D b j) *
          (∑ p ∈ R, ∑ q ∈ R,
            (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j))) =
        ∑ p ∈ R, ∑ q ∈ R,
          (if p = q then (0 : ℤ) else
            α p * α q *
              ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) := by
      calc
        ∑ j : Fin N, sgn (D a j) * sgn (D b j) *
            (∑ p ∈ R, ∑ q ∈ R,
              (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j)))
            = ∑ j : Fin N, ∑ p ∈ R, ∑ q ∈ R,
                (if p = q then (0 : ℤ) else
                  α p * α q * (sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j))) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun q _ => ?_
              by_cases hpq : p = q
              · simp [hpq]
              · simp only [hpq, ↓reduceIte]
                ring
        _ = ∑ p ∈ R, ∑ j : Fin N, ∑ q ∈ R,
              (if p = q then (0 : ℤ) else
                α p * α q * (sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j))) :=
              Finset.sum_comm
        _ = ∑ p ∈ R, ∑ q ∈ R, ∑ j : Fin N,
              (if p = q then (0 : ℤ) else
                α p * α q * (sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j))) := by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
        _ = ∑ p ∈ R, ∑ q ∈ R,
              (if p = q then (0 : ℤ) else
                α p * α q *
                  ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) := by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
              by_cases hpq : p = q
              · simp [hpq]
              · simp only [hpq, ↓reduceIte, ← Finset.mul_sum]
    rw [hrew] at hzero
    have hcollapse :
        ∑ p ∈ R, ∑ q ∈ R,
          (if p = q then (0 : ℤ) else
            α p * α q *
              ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) =
        2 * (N : ℤ) * (α a * α b) := by
      have hterm_ab :
          ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D a j) * sgn (D b j) = (N : ℤ) := by
        have h1 : ∀ j : Fin N,
            sgn (D a j) * sgn (D b j) * sgn (D a j) * sgn (D b j) = 1 := by
          intro j
          calc
            sgn (D a j) * sgn (D b j) * sgn (D a j) * sgn (D b j)
                = (sgn (D a j) * sgn (D a j)) * (sgn (D b j) * sgn (D b j)) := by ring
            _ = 1 := by rw [sgn_mul_self, sgn_mul_self, mul_one]
        simp [h1]
      have hterm_ba :
          ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D b j) * sgn (D a j) = (N : ℤ) := by
        have h1 : ∀ j : Fin N,
            sgn (D a j) * sgn (D b j) * sgn (D b j) * sgn (D a j) = 1 := by
          intro j
          calc
            sgn (D a j) * sgn (D b j) * sgn (D b j) * sgn (D a j)
                = (sgn (D a j) * sgn (D a j)) * (sgn (D b j) * sgn (D b j)) := by ring
            _ = 1 := by rw [sgn_mul_self, sgn_mul_self, mul_one]
        simp [h1]
      have hinner : ∀ p ∈ R,
          ∑ q ∈ R,
            (if p = q then (0 : ℤ) else
              α p * α q *
                ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) =
          if p = a then α a * α b * (N : ℤ)
          else if p = b then α b * α a * (N : ℤ)
          else 0 := by
        intro p hp
        by_cases hpa : p = a
        · subst hpa
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single b]
          · simp [hab, hterm_ab]
          · intro q hq hqb
            by_cases hqp : p = q
            · simp [hqp]
            · simp only [hqp, ↓reduceIte]
              rw [quad_dot_zero hD hR ha hb ha hq hab hqp (fun h => hqb h.2)
                (fun h => hab h.1), mul_zero]
          · intro h
            exact absurd hb h
        · simp only [hpa, ↓reduceIte]
          by_cases hpb : p = b
          · subst hpb
            simp only [↓reduceIte]
            rw [Finset.sum_eq_single a]
            · simp [hab.symm, hterm_ba]
            · intro q hq hqa
              by_cases hqp : p = q
              · simp [hqp]
              · simp only [hqp, ↓reduceIte]
                rw [quad_dot_zero hD hR ha hb hb hq hab hqp (fun h => hpa h.1)
                  (fun h => hqa h.2), mul_zero]
            · intro h
              exact absurd ha h
          · simp only [hpb, ↓reduceIte]
            refine Finset.sum_eq_zero fun q hq => ?_
            by_cases hpq : p = q
            · simp [hpq]
            · simp only [hpq, ↓reduceIte]
              rw [quad_dot_zero hD hR ha hb hp hq hab hpq (fun h => hpa h.1)
                (fun h => hpb h.1), mul_zero]
      rw [Finset.sum_congr rfl hinner]
      have hsum_ab :
          ∑ p ∈ R, (if p = a then α a * α b * (N : ℤ)
            else if p = b then α b * α a * (N : ℤ) else 0) =
          α a * α b * (N : ℤ) + α b * α a * (N : ℤ) := by
        rw [← Finset.add_sum_erase _ _ ha]
        simp only [↓reduceIte]
        congr 1
        have hb' : b ∈ R.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
        rw [Finset.sum_eq_single b]
        · simp [hab.symm]
        · intro p hp hpb
          have hpa' : p ≠ a := (Finset.mem_erase.mp hp).1
          simp [hpa', hpb]
        · intro h
          exact absurd hb' h
      rw [hsum_ab]
      ring
    rw [hcollapse] at hzero
    have h2N : (2 : ℤ) * (N : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp hzero).resolve_left h2N
  have hex : ∃ a₀ ∈ R, α a₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsum0 : ∑ a ∈ R, α a * α a = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [hall a ha, mul_zero]
    rw [hsum0] at hparseval
    have hpos : (0 : ℤ) < (N : ℤ) * (N : ℤ) := by positivity
    omega
  rcases hex with ⟨a₀, ha₀, hα0⟩
  have hother : ∀ b ∈ R, b ≠ a₀ → α b = 0 := by
    intro b hb hba
    have hp := hprod_zero a₀ ha₀ b hb hba.symm
    exact (mul_eq_zero.mp hp).resolve_left hα0
  have hsq : α a₀ * α a₀ = (N : ℤ) * (N : ℤ) := by
    rw [← hparseval, Finset.sum_eq_single a₀]
    · intro b hb hba
      rw [hother b hb hba, mul_zero]
    · intro h
      exact absurd ha₀ h
  have hval : α a₀ = (N : ℤ) ∨ α a₀ = -(N : ℤ) := by
    have hfac : (α a₀ - (N : ℤ)) * (α a₀ + (N : ℤ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hsingle : ∀ j : Fin N, (N : ℤ) * sgn (H i₀ j) = α a₀ * sgn (D a₀ j) := by
    intro j
    rw [hexpand j, Finset.sum_eq_single a₀]
    · intro b hb hba
      rw [hother b hb hba, zero_mul]
    · intro h
      exact absurd ha₀ h
  rcases hval with hpos | hneg
  · refine ⟨a₀, ha₀, false, ?_⟩
    intro j
    have hj := hsingle j
    rw [hpos] at hj
    have hs := mul_left_cancel₀ hNz hj
    rw [Bool.false_xor]
    exact sgn_inj hs
  · refine ⟨a₀, ha₀, true, ?_⟩
    intro j
    have hj := hsingle j
    rw [hneg] at hj
    have hj' : (N : ℤ) * sgn (H i₀ j) = (N : ℤ) * sgn (xor true (D a₀ j)) := by
      rw [sgn_xor, sgn_true]
      linarith
    exact sgn_inj (mul_left_cancel₀ hNz hj')

private lemma recover_missing_rows {N : ℕ} (hN : 0 < N)
    (H D : Fin N → Fin N → Bool) (R : Finset (Fin N))
    (hH : isHad H) (hD : isHad D) (hR : R.card ≤ 3)
    (hagree : ∀ i ∉ R, ∀ j : Fin N, H i j = D i j) :
    ∃ (r : Equiv.Perm (Fin N)) (u : Fin N → Bool),
      (∀ i ∉ R, r i = i ∧ u i = false) ∧
      ∀ i j, H i j = xor (u i) (D (r i) j) := by
  have hex : ∀ i : Fin N, ∃ a : Fin N, ∃ s : Bool,
      (i ∉ R → a = i ∧ s = false) ∧ ∀ j : Fin N, H i j = xor s (D a j) := by
    intro i
    by_cases hi : i ∈ R
    · rcases recover_one_row hN hH hD hR hagree hi with ⟨a, _, s, hs⟩
      exact ⟨a, s, fun h => absurd hi h, hs⟩
    · refine ⟨i, false, fun _ => ⟨rfl, rfl⟩, fun j => ?_⟩
      rw [Bool.false_xor]
      exact hagree i hi j
  let r_fun : Fin N → Fin N := fun i => Classical.choose (hex i)
  let u : Fin N → Bool := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hspec : ∀ i : Fin N,
      (i ∉ R → r_fun i = i ∧ u i = false) ∧ ∀ j : Fin N, H i j = xor (u i) (D (r_fun i) j) :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hinj : Function.Injective r_fun := by
    intro i₁ i₂ hEq
    by_contra hne
    have h0 := had_row_dot_ne hH hne
    have hsum :
        ∑ j : Fin N, sgn (H i₁ j) * sgn (H i₂ j) =
        sgn (u i₁) * sgn (u i₂) * (N : ℤ) := by
      have hterm : ∀ j : Fin N,
          sgn (H i₁ j) * sgn (H i₂ j) = sgn (u i₁) * sgn (u i₂) := by
        intro j
        rw [(hspec i₁).2 j, (hspec i₂).2 j, hEq, sgn_xor, sgn_xor]
        calc
          sgn (u i₁) * sgn (D (r_fun i₂) j) * (sgn (u i₂) * sgn (D (r_fun i₂) j))
              = sgn (u i₁) * sgn (u i₂) * (sgn (D (r_fun i₂) j) * sgn (D (r_fun i₂) j)) := by ring
          _ = sgn (u i₁) * sgn (u i₂) := by rw [sgn_mul_self, mul_one]
      simp_rw [hterm]
      simp [Finset.sum_const, mul_comm]
    rw [hsum] at h0
    have hNz : (N : ℤ) ≠ 0 := by omega
    have hprod : sgn (u i₁) * sgn (u i₂) * (N : ℤ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sgn_ne_zero _) (sgn_ne_zero _)) hNz
    exact hprod h0
  let r : Equiv.Perm (Fin N) := Equiv.ofBijective r_fun (Finite.injective_iff_bijective.mp hinj)
  refine ⟨r, u, ?_, ?_⟩
  · intro i hi
    exact (hspec i).1 hi
  · intro i j
    exact (hspec i).2 j

private lemma had_completion_3x3 {N : ℕ} (hN : 0 < N)
    (H D : Fin N → Fin N → Bool) (R C : Finset (Fin N))
    (hH : isHad H) (hD : isHad D) (hR : R.card ≤ 3) (hC : C.card ≤ 3)
    (hagree : ∀ i ∉ R, ∀ j ∉ C, H i j = D i j) :
    ∃ (r c : Equiv.Perm (Fin N)) (u v : Fin N → Bool),
      (∀ i ∉ R, r i = i ∧ u i = false) ∧
      (∀ j ∉ C, c j = j ∧ v j = false) ∧
      ∀ i j, H i j = sampleFn D r c u v i j := by
  have hgramC : ∀ a ∉ R, ∀ b ∉ R,
      ∑ j ∈ C, sgn (H a j) * sgn (H b j) = ∑ j ∈ C, sgn (D a j) * sgn (D b j) := by
    intro a ha b hb
    by_cases hab : a = b
    · subst hab
      simp [sgn_mul_self]
    · have hHtot :
          (∑ j ∈ C, sgn (H a j) * sgn (H b j)) +
          (∑ j ∈ Cᶜ, sgn (H a j) * sgn (H b j)) = 0 := by
        rw [Finset.sum_add_sum_compl]
        exact had_row_dot_ne hH hab
      have hDtot :
          (∑ j ∈ C, sgn (D a j) * sgn (D b j)) +
          (∑ j ∈ Cᶜ, sgn (D a j) * sgn (D b j)) = 0 := by
        rw [Finset.sum_add_sum_compl]
        exact had_row_dot_ne hD hab
      have hcompl :
          ∑ j ∈ Cᶜ, sgn (H a j) * sgn (H b j) = ∑ j ∈ Cᶜ, sgn (D a j) * sgn (D b j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ∉ C := Finset.mem_compl.mp hj
        rw [hagree a ha j hj', hagree b hb j hj']
      linarith
  let eC : Fin C.card ≃ C := C.equivFin.symm
  let x : {a : Fin N // a ∉ R} → Fin C.card → Bool := fun a t => H a.1 (eC t).1
  let y : {a : Fin N // a ∉ R} → Fin C.card → Bool := fun a t => D a.1 (eC t).1
  have hgram_xy : ∀ a b : {a : Fin N // a ∉ R},
      ∑ t : Fin C.card, sgn (x a t) * sgn (x b t) =
      ∑ t : Fin C.card, sgn (y a t) * sgn (y b t) := by
    intro a b
    have hxC : ∑ t : Fin C.card, sgn (x a t) * sgn (x b t) =
        ∑ j ∈ C, sgn (H a.1 j) * sgn (H b.1 j) := by
      rw [← Finset.sum_attach C]
      exact Fintype.sum_equiv eC (fun t => sgn (x a t) * sgn (x b t))
        (fun j => sgn (H a.1 j.1) * sgn (H b.1 j.1)) (fun _ => rfl)
    have hyC : ∑ t : Fin C.card, sgn (y a t) * sgn (y b t) =
        ∑ j ∈ C, sgn (D a.1 j) * sgn (D b.1 j) := by
      rw [← Finset.sum_attach C]
      exact Fintype.sum_equiv eC (fun t => sgn (y a t) * sgn (y b t))
        (fun j => sgn (D a.1 j.1) * sgn (D b.1 j.1)) (fun _ => rfl)
    rw [hxC, hyC]
    exact hgramC a.1 a.2 b.1 b.2
  rcases align_gram hC x y hgram_xy with ⟨σ, w, halign⟩
  rcases extend_perm_on_finset C eC σ with ⟨c, hc_out, hc_in⟩
  let v : Fin N → Bool := fun j => if hj : j ∈ C then w (eC.symm ⟨j, hj⟩) else false
  have hv_out : ∀ j ∉ C, v j = false := fun j hj => by simp [v, hj]
  let D1 : Fin N → Fin N → Bool := fun i j => xor (v j) (D i (c j))
  have hD1_had : isHad D1 := had_col_signed_perm hD c v
  have hD1_agree : ∀ i ∉ R, ∀ j : Fin N, H i j = D1 i j := by
    intro i hi j
    by_cases hj : j ∈ C
    · have ha := halign ⟨i, hi⟩ (eC.symm ⟨j, hj⟩)
      have heC : (eC (eC.symm ⟨j, hj⟩)).1 = j := congr_arg Subtype.val (eC.apply_symm_apply ⟨j, hj⟩)
      simp only [D1, v, hj, ↓reduceDIte, hc_in j hj]
      simpa only [x, y, heC] using ha
    · simp only [D1, hv_out j hj, hc_out j hj, Bool.false_xor]
      exact hagree i hi j hj
  rcases recover_missing_rows hN H D1 R hH hD1_had hR hD1_agree with ⟨r, u, hr_out, hr_eq⟩
  refine ⟨r, c, u, v, hr_out, fun j hj => ⟨hc_out j hj, hv_out j hj⟩, ?_⟩
  intro i j
  rw [hr_eq i j]
  simp only [D1, sampleFn, Bool.xor_assoc]

private lemma errors_edit_both_ne {N : ℕ} (hN : 0 < N) {H : Fin N → Fin N → Bool} (hH : isHad H)
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (f g : Bool) :
    errorsFn H (editFn H i j k l f g) +
      (if H i k ≠ xor f (H j k) then 1 else 0) +
      (if H i k ≠ xor g (H i l) then 1 else 0) =
    N + (if H i k ≠ xor (xor f g) (H j l) then 1 else 0) := by
  let E := editFn H i j k l f g
  have hE_out : ∀ x y : Fin N, x ≠ i → y ≠ k → E x y = H x y := by
    intro x y hx hy
    simp [E, editFn, hx, hy]
  have hE_row : ∀ y : Fin N, y ≠ k → E i y = xor f (H j y) := by
    intro y hy
    simp [E, editFn, hij, hy]
  have hE_col : ∀ x : Fin N, x ≠ i → E x k = xor g (H x l) := by
    intro x hx
    simp [E, editFn, hx, hkl]
  have hE_cor : E i k = xor (xor f g) (H j l) := by
    simp [E, editFn, hij, hkl]
  have hrow_sum :
      ∑ y : Fin N, errInd H E i y =
      ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card -
        (if H i k ≠ xor f (H j k) then 1 else 0) +
        (if H i k ≠ xor (xor f g) (H j l) then 1 else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have hrest :
        ∑ y ∈ Finset.univ.erase k, errInd H E i y =
        ∑ y ∈ Finset.univ.erase k, (if H i y ≠ xor f (H j y) then 1 else 0) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hyk : y ≠ k := (Finset.mem_erase.mp hy).1
      simp only [errInd, hE_row y hyk]
    rw [hrest]
    have hfull :
        ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card =
        (if H i k ≠ xor f (H j k) then 1 else 0) +
        ∑ y ∈ Finset.univ.erase k, (if H i y ≠ xor f (H j y) then 1 else 0) := by
      rw [Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have hcor : errInd H E i k = if H i k ≠ xor (xor f g) (H j l) then 1 else 0 := by
      simp only [errInd, hE_cor]
    rw [hcor]
    omega
  have hother_sum :
      ∑ x ∈ Finset.univ.erase i, ∑ y : Fin N, errInd H E x y =
      ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card -
        (if H i k ≠ xor g (H i l) then 1 else 0) := by
    have hinner : ∀ x ∈ Finset.univ.erase i,
        ∑ y : Fin N, errInd H E x y = if H x k ≠ xor g (H x l) then 1 else 0 := by
      intro x hx
      have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
      rw [Finset.sum_eq_single k]
      · simp only [errInd, hE_col x hxi]
      · intro y _ hyk
        simp only [errInd, hE_out x y hxi hyk, ne_eq, not_true_eq_false, ↓reduceIte]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [Finset.sum_congr rfl hinner]
    have hfull :
        ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card =
        (if H i k ≠ xor g (H i l) then 1 else 0) +
        ∑ x ∈ Finset.univ.erase i, (if H x k ≠ xor g (H x l) then 1 else 0) := by
      rw [Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    omega
  have hrc : 2 * ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card = N :=
    had_row_flip_count hH hij f
  have hcc : 2 * ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card = N :=
    had_col_flip_count hN hH hkl g
  have hrc_ge : (if H i k ≠ xor f (H j k) then 1 else 0) ≤
      ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card := by
    split_ifs with h
    · exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩⟩
    · exact Nat.zero_le _
  have hcc_ge : (if H i k ≠ xor g (H i l) then 1 else 0) ≤
      ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card := by
    split_ifs with h
    · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
    · exact Nat.zero_le _
  rw [errors_eq_sum_ind, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hrow_sum, hother_sum]
  omega

private lemma errors_edit_cases {N : ℕ} (hN : 0 < N) {H : Fin N → Fin N → Bool} (hH : isHad H)
    (i j k l : Fin N) (f g : Bool) (he : errorsFn H (editFn H i j k l f g) < N) :
    errorsFn H (editFn H i j k l f g) = 0 ∨
    2 * errorsFn H (editFn H i j k l f g) = N ∨
    errorsFn H (editFn H i j k l f g) + 2 = N ∨
    errorsFn H (editFn H i j k l f g) + 1 = N := by
  by_cases hij : i = j
  · by_cases hkl : k = l
    · left
      subst hij
      subst hkl
      have hEq : editFn H i i k k f g = H := by
        ext x y
        simp only [editFn, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Bool.false_xor]
        split_ifs <;> subst_vars <;> rfl
      rw [hEq]
      simp [errorsFn]
    · right; left
      subst hij
      have hEq :
          errorsFn H (editFn H i i k l f g) =
          ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card := by
        rw [errors_eq_sum_ind, Finset.card_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hxx : (if x = i then i else x) = x := by
          split_ifs with h
          · exact h.symm
          · rfl
        rw [Finset.sum_eq_single k]
        · simp only [errInd, editFn, hxx, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            Bool.false_xor, hkl, true_and, not_false_eq_true]
        · intro y _ hyk
          simp only [errInd, editFn, hxx, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            hyk, false_and, Bool.false_xor]
        · intro h
          exact absurd (Finset.mem_univ k) h
      rw [hEq]
      exact had_col_flip_count hN hH hkl g
  · by_cases hkl : k = l
    · right; left
      subst hkl
      have hEq :
          errorsFn H (editFn H i j k k f g) =
          ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card := by
        rw [errors_eq_sum_ind, Finset.sum_eq_single i]
        · rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun y _ => ?_
          have hyy : (if y = k then k else y) = y := by
            split_ifs with h
            · exact h.symm
            · rfl
          simp only [errInd, editFn, hyy, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            Bool.xor_false, hij, true_and, not_false_eq_true]
        · intro x _ hxi
          refine Finset.sum_eq_zero fun y _ => ?_
          have hyy : (if y = k then k else y) = y := by
            split_ifs with h
            · exact h.symm
            · rfl
          simp only [errInd, editFn, hyy, hxi, false_and, ↓reduceIte, ne_eq, not_true_eq_false,
            and_false, Bool.false_xor]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [hEq]
      exact had_row_flip_count hH hij f
    · right; right
      have hform := errors_edit_both_ne hN hH hij hkl f g
      split_ifs at hform <;> omega

private lemma exists_neg_edit {N : ℕ} (hN : 8 ≤ N) {H : Fin N → Fin N → Bool} (hH : isHad H) :
    ∃ (i j k l : Fin N) (f g : Bool),
      i ≠ j ∧ k ≠ l ∧ errorsFn H (editFn H i j k l f g) + 1 = N := by
  have hNpos : 0 < N := by omega
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congr_arg Fin.val h
    simp [i, j] at this
  have hdiff_card := had_row_flip_count hH hij false
  have hsame_card := had_row_flip_count hH hij true
  have hdiff_ne : ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor false (H j y))).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsame_ne : ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor true (H j y))).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hsame_ne with ⟨k, hk⟩
  rcases hdiff_ne with ⟨l, hl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_xor] at hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hik_eq : H i k = H j k := by
    cases h1 : H i k <;> cases h2 : H j k <;> simp_all
  have hkl : k ≠ l := by
    intro h
    subst h
    exact hl hik_eq
  let f : Bool := true
  let g : Bool := xor (H i k) (H i l)
  have hform := errors_edit_both_ne hNpos hH hij hkl f g
  have h1 : H i k ≠ xor f (H j k) := by
    simp only [f, hik_eq]
    cases H j k <;> decide
  have h2 : ¬(H i k ≠ xor g (H i l)) := by
    simp only [g, not_not]
    cases H i k <;> cases H i l <;> decide
  have h3 : ¬(H i k ≠ xor (xor f g) (H j l)) := by
    simp only [f, g, not_not]
    cases ha : H i k <;> cases hb : H i l <;> cases hc : H j l <;> simp_all
  have hi1 : (if H i k ≠ xor f (H j k) then 1 else 0) = 1 := by
    split_ifs
    rfl
  have hi2 : (if H i k ≠ xor g (H i l) then 1 else 0) = 0 := by
    split_ifs
    rfl
  have hi3 : (if H i k ≠ xor (xor f g) (H j l) then 1 else 0) = 0 := by
    split_ifs
    rfl
  rw [hi1, hi2, hi3] at hform
  exact ⟨i, j, k, l, f, g, hij, hkl, by omega⟩

private lemma classify_col_inj {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H) (hD : isHad D)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    (hc_inj : Function.Injective c)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sampleFn D p q a b) ∧
    (∃ (i j k l : Fin N) (f g : Bool), sampleFn D r c u v = editFn H i j k l f g) := by
  have hNpos : 0 < N := by omega
  let cP : Equiv.Perm (Fin N) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc_inj)
  have hcP : ∀ j : Fin N, cP j = c j := fun _ => rfl
  let D1 : Fin N → Fin N → Bool := fun i j => xor (v j) (D i (cP j))
  have hD1 : isHad D1 := had_col_signed_perm hD cP v
  let K : Fin N → Fin N → Bool := sampleFn D r c u v
  have hK : ∀ i j : Fin N, K i j = xor (u i) (D1 (r i) j) := by
    intro i j
    simp only [K, sampleFn, D1, hcP, Bool.xor_assoc]
  let rowErr : Fin N → ℕ := fun i =>
    ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ K i j)).card
  have hsum_err : ∑ i : Fin N, rowErr i < N := he
  let Z : Finset (Fin N) := Finset.univ.filter (fun i => rowErr i = 0)
  have hZ_eq : ∀ i ∈ Z, ∀ j : Fin N, H i j = xor (u i) (D1 (r i) j) := by
    intro i hi j
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and, rowErr, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, not_not] at hi
    rw [hi trivial, hK i j]
  have hr_injZ : Set.InjOn r Z := by
    intro i₁ hi₁ i₂ hi₂ hEq
    by_contra hne
    have h0 := had_row_dot_ne hH hne
    have hsum :
        ∑ j : Fin N, sgn (H i₁ j) * sgn (H i₂ j) = sgn (u i₁) * sgn (u i₂) * (N : ℤ) := by
      have hterm : ∀ j : Fin N,
          sgn (H i₁ j) * sgn (H i₂ j) = sgn (u i₁) * sgn (u i₂) := by
        intro j
        rw [hZ_eq i₁ hi₁ j, hZ_eq i₂ hi₂ j, hEq, sgn_xor (u i₁), sgn_xor (u i₂)]
        calc
          sgn (u i₁) * sgn (D1 (r i₂) j) * (sgn (u i₂) * sgn (D1 (r i₂) j))
              = sgn (u i₁) * sgn (u i₂) * (sgn (D1 (r i₂) j) * sgn (D1 (r i₂) j)) := by ring
          _ = sgn (u i₁) * sgn (u i₂) := by rw [sgn_mul_self, mul_one]
      simp_rw [hterm]
      simp [Finset.sum_const, mul_comm]
    rw [hsum] at h0
    have hNz : (N : ℤ) ≠ 0 := by omega
    exact mul_ne_zero (mul_ne_zero (sgn_ne_zero _) (sgn_ne_zero _)) hNz h0
  let S1 : Finset (Fin N) := Zᶜ.filter (fun i => r i ∈ Z.image r)
  let S2 : Finset (Fin N) := Zᶜ.filter (fun i => r i ∉ Z.image r)
  have hS_disj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hS_union : S1 ∪ S2 = Zᶜ := by
    ext i
    simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
    tauto
  have hS_card : S1.card + S2.card = Zᶜ.card := by
    rw [← Finset.card_union_of_disjoint hS_disj, hS_union]
  have hS1_err : ∀ i ∈ S1, 2 * rowErr i = N := by
    intro i hi
    simp only [S1, Finset.mem_filter, Finset.mem_compl] at hi
    rcases Finset.mem_image.mp hi.2 with ⟨j, hj, hrj⟩
    have hij : i ≠ j := fun h => hi.1 (h ▸ hj)
    have hKeq : ∀ y : Fin N, K i y = xor (xor (u i) (u j)) (H j y) := by
      intro y
      rw [hK i y, ← hrj, hZ_eq j hj y]
      cases u i <;> cases u j <;> cases D1 (r j) y <;> decide
    have hf :
        (Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ K i y) =
        (Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor (xor (u i) (u j)) (H j y)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hKeq y]
    simp only [rowErr, hf]
    exact had_row_flip_count hH hij (xor (u i) (u j))
  have hS2_err : ∀ i ∈ S2, N ≤ rowErr i * Zᶜ.card := by
    intro i hi
    simp only [S2, Finset.mem_filter, Finset.mem_compl] at hi
    have hpos : 0 < rowErr i := by
      have hne0 : rowErr i ≠ 0 := by
        intro h0
        exact hi.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0⟩)
      omega
    let x : Fin N → ℤ := fun y => sgn (H i y) - sgn (K i y)
    have hx_ne : x ≠ 0 := by
      rcases Finset.card_pos.mp hpos with ⟨y₀, hy₀⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₀
      intro h0
      have hx0 : x y₀ = 0 := congr_fun h0 y₀
      simp only [x, sub_eq_zero] at hx0
      exact hy₀ (sgn_inj hx0)
    have hunc := had_uncertainty hNpos hD1 x hx_ne
    have hA_eq :
        ((Finset.univ : Finset (Fin N)).filter (fun y => x y ≠ 0)).card = rowErr i := by
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, sub_ne_zero]
      exact ⟨fun h heq => h (by rw [heq]), fun h heq => h (sgn_inj heq)⟩
    have hB_sub :
        (Finset.univ : Finset (Fin N)).filter (fun a => ∑ y : Fin N, sgn (D1 a y) * x y ≠ 0) ⊆
        (Z.image r)ᶜ := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [Finset.mem_compl]
      intro himg
      rcases Finset.mem_image.mp himg with ⟨j, hj, hrj⟩
      have hij : i ≠ j := fun h => hi.1 (h ▸ hj)
      have hari : a ≠ r i := fun h => hi.2 (h ▸ himg)
      have hy0 : ∑ y : Fin N, sgn (D1 a y) * x y = 0 := by
        have hsplit :
            ∑ y : Fin N, sgn (D1 a y) * x y =
            (∑ y : Fin N, sgn (D1 a y) * sgn (H i y)) -
            (∑ y : Fin N, sgn (D1 a y) * sgn (K i y)) := by
          simp only [x, mul_sub, Finset.sum_sub_distrib]
        rw [hsplit]
        have hterm1 : ∑ y : Fin N, sgn (D1 a y) * sgn (H i y) = 0 := by
          have h1 : ∀ y : Fin N,
              sgn (D1 a y) * sgn (H i y) = sgn (u j) * (sgn (H i y) * sgn (H j y)) := by
            intro y
            have hzj := hZ_eq j hj y
            rw [hrj] at hzj
            have hd : sgn (D1 a y) = sgn (u j) * sgn (H j y) := by
              rw [hzj, sgn_xor (u j), ← mul_assoc, sgn_mul_self, one_mul]
            rw [hd]
            ring
          simp_rw [h1, ← Finset.mul_sum, had_row_dot_ne hH hij, mul_zero]
        have hterm2 : ∑ y : Fin N, sgn (D1 a y) * sgn (K i y) = 0 := by
          have h2 : ∀ y : Fin N,
              sgn (D1 a y) * sgn (K i y) = sgn (u i) * (sgn (D1 a y) * sgn (D1 (r i) y)) := by
            intro y
            rw [hK i y, sgn_xor (u i)]
            ring
          simp_rw [h2, ← Finset.mul_sum, had_row_dot_ne hD1 hari, mul_zero]
        rw [hterm1, hterm2, sub_self]
      exact ha hy0
    have hB_le :
        ((Finset.univ : Finset (Fin N)).filter
          (fun a => ∑ y : Fin N, sgn (D1 a y) * x y ≠ 0)).card ≤ Zᶜ.card := by
      calc
        ((Finset.univ : Finset (Fin N)).filter
            (fun a => ∑ y : Fin N, sgn (D1 a y) * x y ≠ 0)).card
            ≤ (Z.image r)ᶜ.card := Finset.card_le_card hB_sub
        _ = N - (Z.image r).card := by simp [Finset.card_compl]
        _ = N - Z.card := by rw [Finset.card_image_of_injOn hr_injZ]
        _ = Zᶜ.card := by simp [Finset.card_compl]
    rw [hA_eq] at hunc
    exact le_trans hunc (Nat.mul_le_mul_left (rowErr i) hB_le)
  have hS1_sum : 2 * ∑ i ∈ S1, rowErr i = S1.card * N := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hS1_err]
    simp
  have hS2_sum : S2.card * N ≤ Zᶜ.card * ∑ i ∈ S2, rowErr i := by
    calc
      S2.card * N = ∑ _i ∈ S2, N := by simp
      _ ≤ ∑ i ∈ S2, rowErr i * Zᶜ.card := Finset.sum_le_sum hS2_err
      _ = Zᶜ.card * ∑ i ∈ S2, rowErr i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsum_le : ∑ i ∈ S1, rowErr i + ∑ i ∈ S2, rowErr i ≤ ∑ i : Fin N, rowErr i := by
    rw [← Finset.sum_union hS_disj, hS_union]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hS1_le1 : S1.card ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ S1.card := by omega
    have : 2 * N ≤ 2 * ∑ i ∈ S1, rowErr i := by
      rw [hS1_sum]
      exact Nat.mul_le_mul_right N h2
    omega
  by_cases hZc : Zᶜ.card = 0
  · have hZ_univ : Z = Finset.univ := by
      have h1 : Zᶜ = ∅ := Finset.card_eq_zero.mp hZc
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra h
      have hc : i ∈ Zᶜ := Finset.mem_compl.mpr h
      rw [h1] at hc
      exact Finset.notMem_empty i hc
    have hr_inj : Function.Injective r := by
      intro i₁ i₂ h
      exact hr_injZ (hZ_univ ▸ Finset.mem_univ i₁) (hZ_univ ▸ Finset.mem_univ i₂) h
    let rP : Equiv.Perm (Fin N) := Equiv.ofBijective r (Finite.injective_iff_bijective.mp hr_inj)
    have hHK : H = K := by
      ext i j
      rw [hZ_eq i (hZ_univ ▸ Finset.mem_univ i) j, hK i j]
    refine ⟨⟨rP, cP, u, v, ?_⟩, ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩,
      false, false, ?_⟩⟩
    · ext i j
      rw [hHK]
      rfl
    · ext x y
      rw [hHK]
      simp only [editFn, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Bool.false_xor]
      split_ifs <;> subst_vars <;> rfl
  · have hS1_eq1 : S1.card = 1 := by
      by_contra h
      have hS1_0 : S1.card = 0 := by omega
      have hS2_eq : S2.card = Zᶜ.card := by omega
      rw [hS2_eq] at hS2_sum
      have hge : Zᶜ.card * N ≤ Zᶜ.card * ∑ i : Fin N, rowErr i :=
        le_trans hS2_sum (Nat.mul_le_mul_left _ (by omega))
      have hpos : 0 < Zᶜ.card := by omega
      have : N ≤ ∑ i : Fin N, rowErr i := Nat.le_of_mul_le_mul_left hge hpos
      omega
    have hS2_eq0 : S2.card = 0 := by
      by_contra h
      have hS2_pos : 1 ≤ S2.card := by omega
      have hm_ge2 : 2 ≤ Zᶜ.card := by omega
      have hmul :
          (3 * Zᶜ.card - 2) * N ≤ 2 * Zᶜ.card * (∑ i ∈ S1, rowErr i + ∑ i ∈ S2, rowErr i) := by
        have h1 : Zᶜ.card * N = Zᶜ.card * (2 * ∑ i ∈ S1, rowErr i) := by
          rw [hS1_sum, hS1_eq1, one_mul]
        have h2 : 2 * (S2.card * N) ≤ 2 * (Zᶜ.card * ∑ i ∈ S2, rowErr i) :=
          Nat.mul_le_mul_left 2 hS2_sum
        have h3 : 3 * Zᶜ.card - 2 = Zᶜ.card + 2 * S2.card := by omega
        rw [h3, add_mul, mul_assoc]
        linarith
      have hge2m : 2 * Zᶜ.card ≤ 3 * Zᶜ.card - 2 := by omega
      have hbound : 2 * Zᶜ.card * N ≤ 2 * Zᶜ.card * ∑ i : Fin N, rowErr i := by
        calc
          2 * Zᶜ.card * N ≤ (3 * Zᶜ.card - 2) * N := Nat.mul_le_mul_right N hge2m
          _ ≤ 2 * Zᶜ.card * (∑ i ∈ S1, rowErr i + ∑ i ∈ S2, rowErr i) := hmul
          _ ≤ 2 * Zᶜ.card * ∑ i : Fin N, rowErr i := Nat.mul_le_mul_left _ hsum_le
      have hpos : 0 < 2 * Zᶜ.card := by omega
      have : N ≤ ∑ i : Fin N, rowErr i := Nat.le_of_mul_le_mul_left hbound hpos
      omega
    rcases Finset.card_eq_one.mp hS1_eq1 with ⟨i₀, hi₀_eq⟩
    have hZc_eq : Zᶜ = {i₀} := by
      have hS2_empty : S2 = ∅ := Finset.card_eq_zero.mp hS2_eq0
      rw [← hS_union, hi₀_eq, hS2_empty, Finset.union_empty]
    have hi₀_S1 : i₀ ∈ S1 := by rw [hi₀_eq]; exact Finset.mem_singleton_self i₀
    have hi₀_nZ : i₀ ∉ Z := by
      have h1 : i₀ ∈ Zᶜ := by rw [hZc_eq]; exact Finset.mem_singleton_self i₀
      exact Finset.mem_compl.mp h1
    have hi₀_img : r i₀ ∈ Z.image r := (Finset.mem_filter.mp hi₀_S1).2
    rcases Finset.mem_image.mp hi₀_img with ⟨j₀, hj₀, hrj₀⟩
    have hij₀ : i₀ ≠ j₀ := fun h => hi₀_nZ (h ▸ hj₀)
    rcases extend_injOn_perm Z r hr_injZ with ⟨r0, hr0⟩
    let D2 : Fin N → Fin N → Bool := fun x y => xor (u x) (D1 (r0 x) y)
    have hD2 : isHad D2 := had_row_signed_perm hD1 r0 u
    have hD2_agree : ∀ x ∉ ({i₀} : Finset (Fin N)), ∀ y : Fin N, H x y = D2 x y := by
      intro x hx y
      have hxZ : x ∈ Z := by
        by_contra h
        have h1 : x ∈ Zᶜ := Finset.mem_compl.mpr h
        rw [hZc_eq] at h1
        exact hx h1
      simp only [D2, hr0 x hxZ]
      exact hZ_eq x hxZ y
    rcases recover_missing_rows hNpos H D2 {i₀} hH hD2 (by simp) hD2_agree with
      ⟨p1, a1, _, hp1_eq⟩
    refine ⟨⟨p1.trans r0, cP, fun x => xor (a1 x) (u (p1 x)), v, ?_⟩,
      ⟨i₀, j₀, ⟨0, by omega⟩, ⟨0, by omega⟩, xor (u i₀) (u j₀), false, ?_⟩⟩
    · ext x y
      rw [hp1_eq x y]
      simp only [D2, D1, sampleFn, Equiv.trans_apply, hcP, Bool.xor_assoc]
    · ext x y
      have hy0 : (if y = (⟨0, hNpos⟩ : Fin N) then (⟨0, hNpos⟩ : Fin N) else y) = y := by
        split_ifs with h
        · exact h.symm
        · rfl
      by_cases hxi : x = i₀
      · rw [hxi]
        have h1 : K i₀ y = xor (xor (u i₀) (u j₀)) (H j₀ y) := by
          rw [hK i₀ y, ← hrj₀, hZ_eq j₀ hj₀ y]
          cases u i₀ <;> cases u j₀ <;> cases D1 (r j₀) y <;> decide
        change K i₀ y = _
        rw [h1]
        simp only [editFn, hy0, hij₀, true_and, not_false_eq_true, ↓reduceIte, ne_eq,
          not_true_eq_false, and_false, Bool.xor_false]
      · have hxZ : x ∈ Z := by
          by_contra h
          have h1 : x ∈ Zᶜ := Finset.mem_compl.mpr h
          rw [hZc_eq, Finset.mem_singleton] at h1
          exact hxi h1
        change K x y = _
        rw [hK x y, ← hZ_eq x hxZ y]
        simp only [editFn, hy0, hxi, false_and, ↓reduceIte, ne_eq, not_true_eq_false, and_false,
          Bool.false_xor]

private lemma corner_bool_ineq :
    ∀ e11 e12 e21 e22 : Bool,
      (if xor e11 e21 then 1 else 0) + (if xor e12 e22 then 1 else 0) +
      (if xor e11 e12 then 1 else 0) + (if xor e21 e22 then 1 else 0) ≤
      2 + (if e11 then 1 else 0) + (if e12 then 1 else 0) +
      (if e21 then 1 else 0) + (if e22 then 1 else 0) := by
  decide

private lemma bool_ne_xor_iff :
    ∀ h1 h2 k1 k2 s : Bool,
      xor k1 k2 = s →
      (h1 ≠ xor s h2 ↔ xor (xor h1 k1) (xor h2 k2) = true) := by
  decide

private lemma bool_ne_ite_xor :
    ∀ a b : Bool, (if a ≠ b then 1 else 0) = (if xor a b = true then 1 else 0) := by
  decide

private lemma ab_force_one {N e a b : ℕ} (hN : 8 ≤ N) (he : e < N)
    (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (hineq : (a + b) * N ≤ 2 * e + 4 * a * b) :
    a = 1 ∧ b = 1 := by
  interval_cases a <;> interval_cases b <;> omega

private lemma both_coll_extract_RC {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    {i₁ i₂ k₁ k₂ : Fin N} (hi12 : i₁ ≠ i₂) (hri12 : r i₁ = r i₂)
    (hk12 : k₁ ≠ k₂) (hck12 : c k₁ = c k₂)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    ∃ R : Finset (Fin N),
      R.card ≤ 3 ∧ ∀ i ∉ R, ∀ j ∉ ({k₁, k₂} : Finset (Fin N)),
        H i j = sampleFn D r c u v i j := by
  have hNpos : 0 < N := by omega
  let K := sampleFn D r c u v
  have heK : errorsFn H K < N := he
  let badR : Fin N → ℕ := fun j => if H i₁ j ≠ xor (xor (u i₁) (u i₂)) (H i₂ j) then 1 else 0
  let badC : Fin N → ℕ := fun i => if H i k₁ ≠ xor (xor (v k₁) (v k₂)) (H i k₂) then 1 else 0
  have hbadR_tot : 2 * ∑ j : Fin N, badR j = N := by
    have h1 : ∑ j : Fin N, badR j =
        ((Finset.univ : Finset (Fin N)).filter
          (fun j => H i₁ j ≠ xor (xor (u i₁) (u i₂)) (H i₂ j))).card := by
      simp only [badR, Finset.card_filter]
    rw [h1]
    exact had_row_flip_count hH hi12 (xor (u i₁) (u i₂))
  have hbadC_tot : 2 * ∑ i : Fin N, badC i = N := by
    have h1 : ∑ i : Fin N, badC i =
        ((Finset.univ : Finset (Fin N)).filter
          (fun i => H i k₁ ≠ xor (xor (v k₁) (v k₂)) (H i k₂))).card := by
      simp only [badC, Finset.card_filter]
    rw [h1]
    exact had_col_flip_count hNpos hH hk12 (xor (v k₁) (v k₂))
  have hbadR_le : ∀ j : Fin N, badR j ≤ errInd H K i₁ j + errInd H K i₂ j := by
    intro j
    have hKxor : xor (K i₁ j) (K i₂ j) = xor (u i₁) (u i₂) := by
      simp only [K, sampleFn, hri12]
      cases u i₁ <;> cases u i₂ <;> cases v j <;> cases D (r i₂) (c j) <;> decide
    simp only [badR, errInd]
    cases ha : H i₁ j <;> cases hb : H i₂ j <;> cases hc : K i₁ j <;> cases hd : K i₂ j <;>
      cases hu1 : u i₁ <;> cases hu2 : u i₂ <;> simp_all
  have hbadC_le : ∀ i : Fin N, badC i ≤ errInd H K i k₁ + errInd H K i k₂ := by
    intro i
    have hKxor : xor (K i k₁) (K i k₂) = xor (v k₁) (v k₂) := by
      simp only [K, sampleFn, hck12]
      cases u i <;> cases v k₁ <;> cases v k₂ <;> cases D (r i) (c k₂) <;> decide
    simp only [badC, errInd]
    cases ha : H i k₁ <;> cases hb : H i k₂ <;> cases hc : K i k₁ <;> cases hd : K i k₂ <;>
      cases hv1 : v k₁ <;> cases hv2 : v k₂ <;> simp_all
  have hcorner :
      badR k₁ + badR k₂ + badC i₁ + badC i₂ ≤
      2 + errInd H K i₁ k₁ + errInd H K i₁ k₂ + errInd H K i₂ k₁ + errInd H K i₂ k₂ := by
    have hKr1 : xor (K i₁ k₁) (K i₂ k₁) = xor (u i₁) (u i₂) := by
      simp only [K, sampleFn, hri12]
      cases u i₁ <;> cases u i₂ <;> cases v k₁ <;> cases D (r i₂) (c k₁) <;> decide
    have hKr2 : xor (K i₁ k₂) (K i₂ k₂) = xor (u i₁) (u i₂) := by
      simp only [K, sampleFn, hri12]
      cases u i₁ <;> cases u i₂ <;> cases v k₂ <;> cases D (r i₂) (c k₂) <;> decide
    have hKc1 : xor (K i₁ k₁) (K i₁ k₂) = xor (v k₁) (v k₂) := by
      simp only [K, sampleFn, hck12]
      cases u i₁ <;> cases v k₁ <;> cases v k₂ <;> cases D (r i₁) (c k₂) <;> decide
    have hKc2 : xor (K i₂ k₁) (K i₂ k₂) = xor (v k₁) (v k₂) := by
      simp only [K, sampleFn, hck12]
      cases u i₂ <;> cases v k₁ <;> cases v k₂ <;> cases D (r i₂) (c k₂) <;> decide
    let e11 := xor (H i₁ k₁) (K i₁ k₁)
    let e12 := xor (H i₁ k₂) (K i₁ k₂)
    let e21 := xor (H i₂ k₁) (K i₂ k₁)
    let e22 := xor (H i₂ k₂) (K i₂ k₂)
    have h11 : errInd H K i₁ k₁ = if e11 then 1 else 0 := bool_ne_ite_xor (H i₁ k₁) (K i₁ k₁)
    have h12 : errInd H K i₁ k₂ = if e12 then 1 else 0 := bool_ne_ite_xor (H i₁ k₂) (K i₁ k₂)
    have h21 : errInd H K i₂ k₁ = if e21 then 1 else 0 := bool_ne_ite_xor (H i₂ k₁) (K i₂ k₁)
    have h22 : errInd H K i₂ k₂ = if e22 then 1 else 0 := bool_ne_ite_xor (H i₂ k₂) (K i₂ k₂)
    have hr1 : badR k₁ = if xor e11 e21 then 1 else 0 := by
      simp only [badR, bool_ne_xor_iff _ _ _ _ _ hKr1, e11, e21]
    have hr2 : badR k₂ = if xor e12 e22 then 1 else 0 := by
      simp only [badR, bool_ne_xor_iff _ _ _ _ _ hKr2, e12, e22]
    have hc1 : badC i₁ = if xor e11 e12 then 1 else 0 := by
      simp only [badC, bool_ne_xor_iff _ _ _ _ _ hKc1, e11, e12]
    have hc2 : badC i₂ = if xor e21 e22 then 1 else 0 := by
      simp only [badC, bool_ne_xor_iff _ _ _ _ _ hKc2, e21, e22]
    rw [h11, h12, h21, h22, hr1, hr2, hc1, hc2]
    exact corner_bool_ineq e11 e12 e21 e22
  let R0 : Finset (Fin N) := {i₁, i₂}
  let C0 : Finset (Fin N) := {k₁, k₂}
  have hsum_R0 : ∀ f : Fin N → ℕ, ∑ i ∈ R0, f i = f i₁ + f i₂ := by
    intro f
    simp [R0, Finset.sum_pair hi12]
  have hsum_C0 : ∀ f : Fin N → ℕ, ∑ j ∈ C0, f j = f k₁ + f k₂ := by
    intro f
    simp [C0, Finset.sum_pair hk12]
  have hsplit_tot :
      errorsFn H K =
      (∑ i ∈ R0, ∑ j ∈ C0, errInd H K i j) +
      (∑ i ∈ R0, ∑ j ∈ C0ᶜ, errInd H K i j) +
      (∑ i ∈ R0ᶜ, ∑ j ∈ C0, errInd H K i j) +
      (∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j) := by
    rw [errors_eq_sum_ind, ← Finset.sum_add_sum_compl R0]
    have h1 : ∀ i : Fin N,
        ∑ j : Fin N, errInd H K i j =
        (∑ j ∈ C0, errInd H K i j) + (∑ j ∈ C0ᶜ, errInd H K i j) :=
      fun i => (Finset.sum_add_sum_compl C0 _).symm
    simp_rw [h1, Finset.sum_add_distrib]
    omega
  have hbadR_split :
      ∑ j : Fin N, badR j = badR k₁ + badR k₂ + ∑ j ∈ C0ᶜ, badR j := by
    rw [← Finset.sum_add_sum_compl C0, hsum_C0]
  have hbadC_split :
      ∑ i : Fin N, badC i = badC i₁ + badC i₂ + ∑ i ∈ R0ᶜ, badC i := by
    rw [← Finset.sum_add_sum_compl R0, hsum_R0]
  have hUr_ge : ∑ j ∈ C0ᶜ, badR j ≤ ∑ i ∈ R0, ∑ j ∈ C0ᶜ, errInd H K i j := by
    rw [hsum_R0, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hbadR_le j
  have hUc_ge : ∑ i ∈ R0ᶜ, badC i ≤ ∑ i ∈ R0ᶜ, ∑ j ∈ C0, errInd H K i j := by
    calc
      ∑ i ∈ R0ᶜ, badC i ≤ ∑ i ∈ R0ᶜ, (errInd H K i k₁ + errInd H K i k₂) :=
        Finset.sum_le_sum fun i _ => hbadC_le i
      _ = ∑ i ∈ R0ᶜ, ∑ j ∈ C0, errInd H K i j := by
        refine Finset.sum_congr rfl fun i _ => (hsum_C0 _).symm
  have hU0_eq :
      ∑ i ∈ R0, ∑ j ∈ C0, errInd H K i j =
      errInd H K i₁ k₁ + errInd H K i₁ k₂ + errInd H K i₂ k₁ + errInd H K i₂ k₂ := by
    rw [hsum_R0, hsum_C0, hsum_C0]
    omega
  have hout_le1 : ∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j ≤ 1 := by
    omega
  by_cases h0 : ∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j = 0
  · refine ⟨R0, ?_, ?_⟩
    · simp [R0, Finset.card_pair hi12]
    · intro i hi j hj
      have h1 := Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_compl.mpr hi)
      have h2 := Finset.sum_eq_zero_iff.mp h1 j (Finset.mem_compl.mpr hj)
      simp only [errInd, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h2
      exact h2
  · have hpos : 0 < ∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j := by omega
    rcases Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos) with ⟨i₃, hi₃, hrow3⟩
    refine ⟨insert i₃ R0, ?_, ?_⟩
    · have hR0c : R0.card = 2 := Finset.card_pair hi12
      have := Finset.card_insert_le i₃ R0
      omega
    · intro i hi j hj
      have hiR0 : i ∈ R0ᶜ := Finset.mem_compl.mpr (fun h => hi (Finset.mem_insert_of_mem h))
      have hne3 : i ≠ i₃ := fun h => hi (h ▸ Finset.mem_insert_self i₃ R0)
      have hle_sum :
          (∑ y ∈ C0ᶜ, errInd H K i₃ y) + (∑ y ∈ C0ᶜ, errInd H K i y) ≤
          ∑ x ∈ R0ᶜ, ∑ y ∈ C0ᶜ, errInd H K x y := by
        rw [← Finset.add_sum_erase _ _ hi₃]
        refine Nat.add_le_add_left ?_ _
        exact Finset.single_le_sum (f := fun x => ∑ y ∈ C0ᶜ, errInd H K x y)
          (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne3, hiR0⟩)
      have hi3_ge1 : 1 ≤ ∑ y ∈ C0ᶜ, errInd H K i₃ y := Nat.pos_of_ne_zero hrow3
      have hi_zero : ∑ y ∈ C0ᶜ, errInd H K i y = 0 := by omega
      have h2 := Finset.sum_eq_zero_iff.mp hi_zero j (Finset.mem_compl.mpr hj)
      simp only [errInd, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h2
      exact h2

private lemma classify_both_coll {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H) (hD : isHad D)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    (hr_coll : ∃ i₁ i₂ : Fin N, i₁ ≠ i₂ ∧ r i₁ = r i₂)
    (hc_coll : ∃ k₁ k₂ : Fin N, k₁ ≠ k₂ ∧ c k₁ = c k₂)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sampleFn D p q a b) ∧
    (∃ (i j k l : Fin N) (f g : Bool), sampleFn D r c u v = editFn H i j k l f g) := by
  have hNpos : 0 < N := by omega
  rcases hr_coll with ⟨i₁, i₂, hi12, hri12⟩
  rcases hc_coll with ⟨k₁, k₂, hk12, hck12⟩
  let K := sampleFn D r c u v
  have heK : errorsFn H K < N := he
  let C0 : Finset (Fin N) := {k₁, k₂}
  rcases both_coll_extract_RC hN H D hH r c u v hi12 hri12 hk12 hck12 he with
    ⟨R, hR_card, hHK_agree⟩
  have hC0_card : C0.card ≤ 3 := by
    have : C0.card = 2 := Finset.card_pair hk12
    omega
  have hr_inj : Set.InjOn r (Rᶜ : Finset (Fin N)) := by
    intro a ha b hb hrab
    by_contra hab
    have hagree_row : ∀ j ∉ C0, H a j = xor (xor (u a) (u b)) (H b j) := by
      intro j hj
      rw [hHK_agree a (Finset.mem_compl.mp ha) j hj, hHK_agree b (Finset.mem_compl.mp hb) j hj]
      simp only [sampleFn, hrab]
      cases u a <;> cases u b <;> cases v j <;> cases D (r b) (c j) <;> decide
    have hsub :
        (Finset.univ : Finset (Fin N)).filter (fun j => H a j ≠ xor (xor (u a) (u b)) (H b j)) ⊆
        C0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hjC0
      exact hj (hagree_row j hjC0)
    have hfc := had_row_flip_count hH hab (xor (u a) (u b))
    have hle := Finset.card_le_card hsub
    have hC2 : C0.card = 2 := Finset.card_pair hk12
    omega
  have hc_inj : Set.InjOn c (C0ᶜ : Finset (Fin N)) := by
    intro a ha b hb hcab
    by_contra hab
    have hagree_col : ∀ i ∉ R, H i a = xor (xor (v a) (v b)) (H i b) := by
      intro i hi
      rw [hHK_agree i hi a (Finset.mem_compl.mp ha), hHK_agree i hi b (Finset.mem_compl.mp hb)]
      simp only [sampleFn, hcab]
      cases u i <;> cases v a <;> cases v b <;> cases D (r i) (c b) <;> decide
    have hsub :
        (Finset.univ : Finset (Fin N)).filter (fun i => H i a ≠ xor (xor (v a) (v b)) (H i b)) ⊆
        R := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiR
      exact hi (hagree_col i hiR)
    have hfc := had_col_flip_count hNpos hH hab (xor (v a) (v b))
    have hle := Finset.card_le_card hsub
    omega
  rcases extend_injOn_perm (Rᶜ : Finset (Fin N)) r hr_inj with ⟨r0, hr0⟩
  rcases extend_injOn_perm (C0ᶜ : Finset (Fin N)) c hc_inj with ⟨c0, hc0⟩
  let D0 := sampleFn D r0 c0 u v
  have hD0 : isHad D0 := had_sample_perm hD r0 c0 u v
  have hHD0_agree : ∀ i ∉ R, ∀ j ∉ C0, H i j = D0 i j := by
    intro i hi j hj
    rw [hHK_agree i hi j hj]
    simp only [D0, sampleFn, hr0 i (Finset.mem_compl.mpr hi), hc0 j (Finset.mem_compl.mpr hj)]
  rcases had_completion_3x3 hNpos H D0 R C0 hH hD0 hR_card hC0_card hHD0_agree with
    ⟨p1, q1, a1, b1, hp1_out, hq1_out, hH_eq⟩
  let p : Equiv.Perm (Fin N) := p1.trans r0
  let q : Equiv.Perm (Fin N) := q1.trans c0
  let a : Fin N → Bool := fun i => xor (a1 i) (u (p1 i))
  let b : Fin N → Bool := fun j => xor (b1 j) (v (q1 j))
  have hH_sample : H = sampleFn D p q a b := by
    ext i j
    rw [hH_eq i j]
    simp only [D0, sampleFn, p, q, a, b, Equiv.trans_apply]
    cases a1 i <;> cases b1 j <;> cases u (p1 i) <;> cases v (q1 j) <;>
      cases D (r0 (p1 i)) (c0 (q1 j)) <;> decide
  let ρ : Fin N → Fin N := fun i => p.symm (r i)
  let γ : Fin N → Fin N := fun j => q.symm (c j)
  let α : Fin N → Bool := fun i => xor (u i) (a (ρ i))
  let β : Fin N → Bool := fun j => xor (v j) (b (γ j))
  have hK_H : ∀ i j : Fin N, K i j = sampleFn H ρ γ α β i j := by
    intro i j
    have hHρ : H (ρ i) (γ j) = xor (xor (a (ρ i)) (b (γ j))) (D (r i) (c j)) := by
      have := congr_fun (congr_fun hH_sample (ρ i)) (γ j)
      simpa only [sampleFn, ρ, γ, Equiv.apply_symm_apply] using this
    simp only [K, sampleFn, α, β, hHρ]
    cases u i <;> cases v j <;> cases a (ρ i) <;> cases b (γ j) <;>
      cases D (r i) (c j) <;> decide
  have hρ_out : ∀ i ∉ R, ρ i = i ∧ α i = false := by
    intro i hi
    have hp1i := hp1_out i hi
    have hpi : p i = r i := by
      simp only [p, Equiv.trans_apply, hp1i.1, hr0 i (Finset.mem_compl.mpr hi)]
    have hρi : ρ i = i := by
      simp only [ρ, ← hpi, Equiv.symm_apply_apply]
    refine ⟨hρi, ?_⟩
    simp only [α, hρi, a, hp1i.1, hp1i.2, Bool.false_xor, Bool.xor_self]
  have hγ_out : ∀ j ∉ C0, γ j = j ∧ β j = false := by
    intro j hj
    have hq1j := hq1_out j hj
    have hqj : q j = c j := by
      simp only [q, Equiv.trans_apply, hq1j.1, hc0 j (Finset.mem_compl.mpr hj)]
    have hγj : γ j = j := by
      simp only [γ, ← hqj, Equiv.symm_apply_apply]
    refine ⟨hγj, ?_⟩
    simp only [β, hγj, b, hq1j.1, hq1j.2, Bool.false_xor, Bool.xor_self]
  let A : Finset (Fin N) := Finset.univ.filter (fun i => ρ i ≠ i ∨ α i ≠ false)
  let B : Finset (Fin N) := Finset.univ.filter (fun j => γ j ≠ j ∨ β j ≠ false)
  have hA_sub : A ⊆ R := by
    intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hiR
    rcases hρ_out i hiR with ⟨h1, h2⟩
    rcases hi with h | h <;> exact h (by assumption)
  have hB_sub : B ⊆ C0 := by
    intro j hj
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hjC
    rcases hγ_out j hjC with ⟨h1, h2⟩
    rcases hj with h | h <;> exact h (by assumption)
  have hA_le3 : A.card ≤ 3 := le_trans (Finset.card_le_card hA_sub) hR_card
  have hB_le2 : B.card ≤ 2 := by
    have hC2 : C0.card = 2 := Finset.card_pair hk12
    exact le_trans (Finset.card_le_card hB_sub) (le_of_eq hC2)
  have hA_ge1 : 1 ≤ A.card := by
    by_contra h0
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by omega)
    have hρid : ∀ i : Fin N, ρ i = i := by
      intro i
      by_contra hne
      have : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hne⟩
      rw [hAe] at this
      exact Finset.notMem_empty i this
    have hEq : ρ i₁ = ρ i₂ := by simp [ρ, hri12]
    rw [hρid i₁, hρid i₂] at hEq
    exact hi12 hEq
  have hB_ge1 : 1 ≤ B.card := by
    by_contra h0
    have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
    have hγid : ∀ j : Fin N, γ j = j := by
      intro j
      by_contra hne
      have : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ j, Or.inl hne⟩
      rw [hBe] at this
      exact Finset.notMem_empty j this
    have hEq : γ k₁ = γ k₂ := by simp [γ, hck12]
    rw [hγid k₁, hγid k₂] at hEq
    exact hk12 hEq
  have hrow_AB : ∀ i ∈ A, N ≤ 2 * (∑ j ∈ Bᶜ, errInd H K i j) + 2 * B.card := by
    intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hK_Bc : ∀ j ∈ Bᶜ, K i j = xor (α i) (H (ρ i) j) := by
      intro j hj
      simp only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hj
      rw [hK_H i j]
      simp [sampleFn, hj.1, hj.2]
    by_cases hρi : ρ i = i
    · have hαi : α i = true := by
        rcases hi with h | h
        · exact absurd hρi h
        · cases ha : α i <;> simp_all
      have hcnt : ∑ j ∈ Bᶜ, errInd H K i j = Bᶜ.card := by
        have h1 : ∀ j ∈ Bᶜ, errInd H K i j = 1 := by
          intro j hj
          simp only [errInd, hK_Bc j hj, hρi, hαi]
          cases H i j <;> decide
        rw [Finset.sum_congr rfl h1]
        simp
      rw [hcnt, Finset.card_compl, Fintype.card_fin]
      omega
    · have hfull := had_row_flip_count hH (Ne.symm hρi) (α i)
      have htot :
          ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ xor (α i) (H (ρ i) j))).card ≤
          (∑ j ∈ Bᶜ, errInd H K i j) + B.card := by
        rw [Finset.card_filter, ← Finset.sum_add_sum_compl B]
        have h1 : ∑ j ∈ B, (if H i j ≠ xor (α i) (H (ρ i) j) then 1 else 0) ≤ B.card := by
          calc
            ∑ j ∈ B, (if H i j ≠ xor (α i) (H (ρ i) j) then 1 else 0) ≤ ∑ _j ∈ B, 1 := by
              refine Finset.sum_le_sum fun j _ => by split_ifs <;> omega
            _ = B.card := by simp
        have h2 : ∑ j ∈ Bᶜ, (if H i j ≠ xor (α i) (H (ρ i) j) then 1 else 0) =
            ∑ j ∈ Bᶜ, errInd H K i j := by
          refine Finset.sum_congr rfl fun j hj => by simp only [errInd, hK_Bc j hj]
        omega
      omega
  have hcol_AB : ∀ j ∈ B, N ≤ 2 * (∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card := by
    intro j hj
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hK_Ac : ∀ i ∈ Aᶜ, K i j = xor (β j) (H i (γ j)) := by
      intro i hi
      simp only [A, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hi
      rw [hK_H i j]
      simp [sampleFn, hi.1, hi.2]
    by_cases hγj : γ j = j
    · have hβj : β j = true := by
        rcases hj with h | h
        · exact absurd hγj h
        · cases hb : β j <;> simp_all
      have hcnt : ∑ i ∈ Aᶜ, errInd H K i j = Aᶜ.card := by
        have h1 : ∀ i ∈ Aᶜ, errInd H K i j = 1 := by
          intro i hi
          simp only [errInd, hK_Ac i hi, hγj, hβj]
          cases H i j <;> decide
        rw [Finset.sum_congr rfl h1]
        simp
      rw [hcnt, Finset.card_compl, Fintype.card_fin]
      omega
    · have hfull := had_col_flip_count hNpos hH (Ne.symm hγj) (β j)
      have htot :
          ((Finset.univ : Finset (Fin N)).filter (fun i => H i j ≠ xor (β j) (H i (γ j)))).card ≤
          (∑ i ∈ Aᶜ, errInd H K i j) + A.card := by
        rw [Finset.card_filter, ← Finset.sum_add_sum_compl A]
        have h1 : ∑ i ∈ A, (if H i j ≠ xor (β j) (H i (γ j)) then 1 else 0) ≤ A.card := by
          calc
            ∑ i ∈ A, (if H i j ≠ xor (β j) (H i (γ j)) then 1 else 0) ≤ ∑ _i ∈ A, 1 := by
              refine Finset.sum_le_sum fun i _ => by split_ifs <;> omega
            _ = A.card := by simp
        have h2 : ∑ i ∈ Aᶜ, (if H i j ≠ xor (β j) (H i (γ j)) then 1 else 0) =
            ∑ i ∈ Aᶜ, errInd H K i j := by
          refine Finset.sum_congr rfl fun i hi => by simp only [errInd, hK_Ac i hi]
        omega
      omega
  have hsum_A : A.card * N ≤ 2 * (∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j) + 2 * A.card * B.card := by
    calc
      A.card * N = ∑ _i ∈ A, N := by simp
      _ ≤ ∑ i ∈ A, (2 * (∑ j ∈ Bᶜ, errInd H K i j) + 2 * B.card) := Finset.sum_le_sum hrow_AB
      _ = 2 * (∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j) + 2 * A.card * B.card := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp [mul_assoc, mul_left_comm]
  have hsum_B : B.card * N ≤ 2 * (∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card * B.card := by
    calc
      B.card * N = ∑ _j ∈ B, N := by simp
      _ ≤ ∑ j ∈ B, (2 * (∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card) := Finset.sum_le_sum hcol_AB
      _ = 2 * (∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card * B.card := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp [mul_assoc, mul_comm]
  have hdisj_err :
      (∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j) + (∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j) ≤
      errorsFn H K := by
    rw [errors_eq_sum_ind, ← Finset.sum_add_sum_compl A]
    have h1 : ∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j ≤ ∑ i ∈ A, ∑ j : Fin N, errInd H K i j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : ∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j ≤ ∑ i ∈ Aᶜ, ∑ j : Fin N, errInd H K i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have hAB_ineq : (A.card + B.card) * N ≤ 2 * errorsFn H K + 4 * A.card * B.card := by
    have h4 : 2 * A.card * B.card + 2 * A.card * B.card = 4 * A.card * B.card := by ring
    rw [add_mul]
    omega
  have hAB1 := ab_force_one hN heK hA_ge1 hA_le3 hB_ge1 hB_le2 hAB_ineq
  have hA1 : A.card = 1 := hAB1.1
  have hB1 : B.card = 1 := hAB1.2
  rcases Finset.card_eq_one.mp hA1 with ⟨i₀, hi₀⟩
  rcases Finset.card_eq_one.mp hB1 with ⟨k₀, hk₀⟩
  have hρ_other : ∀ x : Fin N, x ≠ i₀ → ρ x = x ∧ α x = false := by
    intro x hx
    have hxA : x ∉ A := by rw [hi₀, Finset.mem_singleton]; exact hx
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hxA
    exact hxA
  have hγ_other : ∀ y : Fin N, y ≠ k₀ → γ y = y ∧ β y = false := by
    intro y hy
    have hyB : y ∉ B := by rw [hk₀, Finset.mem_singleton]; exact hy
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hyB
    exact hyB
  have hρ_ne : ρ i₀ ≠ i₀ := by
    intro heq
    have hρid : ∀ x : Fin N, ρ x = x := fun x => by
      by_cases hx : x = i₀
      · subst hx; exact heq
      · exact (hρ_other x hx).1
    have hEq : ρ i₁ = ρ i₂ := by simp [ρ, hri12]
    rw [hρid i₁, hρid i₂] at hEq
    exact hi12 hEq
  have hγ_ne : γ k₀ ≠ k₀ := by
    intro heq
    have hγid : ∀ y : Fin N, γ y = y := fun y => by
      by_cases hy : y = k₀
      · subst hy; exact heq
      · exact (hγ_other y hy).1
    have hEq : γ k₁ = γ k₂ := by simp [γ, hck12]
    rw [hγid k₁, hγid k₂] at hEq
    exact hk12 hEq
  refine ⟨⟨p, q, a, b, hH_sample⟩, ⟨i₀, ρ i₀, k₀, γ k₀, α i₀, β k₀, ?_⟩⟩
  ext x y
  change K x y = editFn H i₀ (ρ i₀) k₀ (γ k₀) (α i₀) (β k₀) x y
  rw [hK_H x y]
  by_cases hx : x = i₀ <;> by_cases hy : y = k₀
  · subst hx; subst hy
    simp [sampleFn, editFn, hρ_ne.symm, hγ_ne.symm]
  · subst hx
    rcases hγ_other y hy with ⟨h1, h2⟩
    simp [sampleFn, editFn, hρ_ne.symm, hy, h1, h2]
  · subst hy
    rcases hρ_other x hx with ⟨h1, h2⟩
    simp [sampleFn, editFn, hγ_ne.symm, hx, h1, h2]
  · rcases hρ_other x hx with ⟨h1, h2⟩
    rcases hγ_other y hy with ⟨h3, h4⟩
    simp [sampleFn, editFn, hx, hy, h1, h2, h3, h4]

private lemma classify_all {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H) (hD : isHad D)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sampleFn D p q a b) ∧
    (∃ (i j k l : Fin N) (f g : Bool), sampleFn D r c u v = editFn H i j k l f g) := by
  have hNpos : 0 < N := by omega
  by_cases hc : Function.Injective c
  · exact classify_col_inj hN H D hH hD r c u v hc he
  · by_cases hr : Function.Injective r
    · let Ht : Fin N → Fin N → Bool := fun j i => H i j
      let Dt : Fin N → Fin N → Bool := fun j i => D i j
      have hHt : isHad Ht := had_transpose hNpos hH
      have hDt : isHad Dt := had_transpose hNpos hD
      have hsample_t : ∀ j i : Fin N, sampleFn Dt c r v u j i = sampleFn D r c u v i j := by
        intro j i
        simp only [sampleFn, Dt, Bool.xor_comm (v j) (u i)]
      have herr_t : errorsFn Ht (sampleFn Dt c r v u) = errorsFn H (sampleFn D r c u v) := by
        rw [errors_eq_sum_ind, errors_eq_sum_ind, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [errInd, Ht, hsample_t j i]
      rw [← herr_t] at he
      rcases classify_col_inj hN Ht Dt hHt hDt c r v u hr he with
        ⟨⟨q, p, b, a, hHt_eq⟩, ⟨k, l, i, j, g, f, hKt_eq⟩⟩
      refine ⟨⟨p, q, a, b, ?_⟩, ⟨i, j, k, l, f, g, ?_⟩⟩
      · ext x y
        have h1 := congr_fun (congr_fun hHt_eq y) x
        simp only [Ht, Dt, sampleFn, Bool.xor_comm (b y) (a x)] at h1
        exact h1
      · ext x y
        have h1 := congr_fun (congr_fun hKt_eq y) x
        rw [hsample_t y x] at h1
        rw [h1]
        simp only [editFn, Ht, Bool.xor_comm]
    · have hr_coll : ∃ i₁ i₂ : Fin N, i₁ ≠ i₂ ∧ r i₁ = r i₂ := by
        unfold Function.Injective at hr
        push Not at hr
        rcases hr with ⟨i₁, i₂, h1, h2⟩
        exact ⟨i₁, i₂, h2, h1⟩
      have hc_coll : ∃ k₁ k₂ : Fin N, k₁ ≠ k₂ ∧ c k₁ = c k₂ := by
        unfold Function.Injective at hc
        push Not at hc
        rcases hc with ⟨k₁, k₂, h1, h2⟩
        exact ⟨k₁, k₂, h2, h1⟩
      exact classify_both_coll hN H D hH hD r c u v hr_coll hc_coll he

end PEqualNP.Outside.L_lib_682_aux

open PEqualNP.Outside.L_lib_682_aux in
theorem PEqualNP.Outside.L_lib_682 : (∀ N : ℕ, 8 ≤ N →
  let T := Fin N → Fin N → Bool
  let had := fun (M : T) => ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N
  let sample := fun (D : T) (r c : Fin N → Fin N) (u v : Fin N → Bool) (i j : Fin N) =>
    xor (xor (u i) (v j)) (D (r i) (c j))
  let errors := fun (A B : T) =>
    ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => A i j ≠ B i j)).card
  let edit := fun (H : T) (i j k l : Fin N) (f g : Bool) (x y : Fin N) =>
    xor (xor (if x = i ∧ i ≠ j then f else false) (if y = k ∧ k ≠ l then g else false))
      (H (if x = i then j else x) (if y = k then l else y))
  ∀ H D : T, had H → had D →
    (∀ (r c : Fin N → Fin N) (u v : Fin N → Bool),
      let K := sample D r c u v
      let e := errors H K
      e < N →
        (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sample D p q a b) ∧
        (∃ (i j k l : Fin N) (f g : Bool), K = edit H i j k l f g) ∧
        (e = 0 ∨ 2*e = N ∨ e+2 = N ∨ e+1 = N)) ∧
    (∃ (i j k l : Fin N) (f g : Bool),
      i ≠ j ∧ k ≠ l ∧ errors H (edit H i j k l f g) + 1 = N)) := by
  intro N hN T had sample errors edit H D hH hD
  have hNpos : 0 < N := by omega
  constructor
  · intro r c u v K e he
    rcases classify_all hN H D hH hD r c u v he with ⟨h1, ⟨i, j, k, l, f, g, h2⟩⟩
    refine ⟨h1, ⟨i, j, k, l, f, g, h2⟩, ?_⟩
    have hKeq : K = editFn H i j k l f g := h2
    have he' : errorsFn H (editFn H i j k l f g) < N := by
      have he0 : errorsFn H K < N := he
      rwa [← hKeq]
    have hcases := errors_edit_cases hNpos hH i j k l f g he'
    have hcases' : errorsFn H K = 0 ∨ 2 * errorsFn H K = N ∨
        errorsFn H K + 2 = N ∨ errorsFn H K + 1 = N := by
      rwa [hKeq]
    exact hcases'
  · exact exists_neg_edit hN hH
