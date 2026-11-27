import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_681_aux

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

private lemma sgn_mul_eq_sub (a b : Bool) :
    sgn a * sgn b = 1 - 2 * (if a ≠ b then (1 : ℤ) else 0) := by
  cases a <;> cases b <;> decide

private def isHad {N : ℕ} (M : Fin N → Fin N → Bool) : Prop :=
  ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N

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
    have hEq := h2.symm.trans h1
    exact mul_left_cancel₀ hNz hEq
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

end PEqualNP.Outside.L_lib_681_aux

open PEqualNP.Outside.L_lib_681_aux in
theorem PEqualNP.Outside.L_lib_681 : (∀ N : ℕ, 8 ≤ N →
  let T := Fin N → Fin N → Bool
  let had := fun (M : T) => ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N
  ∀ (H D : T) (R C : Finset (Fin N)), had H → had D → R.card ≤ 3 → C.card ≤ 3 →
    (∀ i ∉ R, ∀ j ∉ C, H i j = D i j) →
    ∃ (r c : Equiv.Perm (Fin N)) (u v : Fin N → Bool),
      (∀ i ∉ R, r i = i ∧ u i = false) ∧
      (∀ j ∉ C, c j = j ∧ v j = false) ∧
      ∀ i j, H i j = xor (xor (u i) (v j)) (D (r i) (c j))) := by
  intro N hN T had H D R C hH hD hR hC hagree
  have hNpos : 0 < N := by omega
  have hH' : isHad H := hH
  have hD' : isHad D := hD
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
        exact had_row_dot_ne hH' hab
      have hDtot :
          (∑ j ∈ C, sgn (D a j) * sgn (D b j)) +
          (∑ j ∈ Cᶜ, sgn (D a j) * sgn (D b j)) = 0 := by
        rw [Finset.sum_add_sum_compl]
        exact had_row_dot_ne hD' hab
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
  have hD1_had : isHad D1 := had_col_signed_perm hD' c v
  have hD1_agree : ∀ i ∉ R, ∀ j : Fin N, H i j = D1 i j := by
    intro i hi j
    by_cases hj : j ∈ C
    · have ha := halign ⟨i, hi⟩ (eC.symm ⟨j, hj⟩)
      have heC : (eC (eC.symm ⟨j, hj⟩)).1 = j := congr_arg Subtype.val (eC.apply_symm_apply ⟨j, hj⟩)
      simp only [D1, v, hj, ↓reduceDIte, hc_in j hj]
      simpa only [x, y, heC] using ha
    · simp only [D1, hv_out j hj, hc_out j hj, Bool.false_xor]
      exact hagree i hi j hj
  rcases recover_missing_rows hNpos H D1 R hH' hD1_had hR hD1_agree with ⟨r, u, hr_out, hr_eq⟩
  refine ⟨r, c, u, v, hr_out, fun j hj => ⟨hc_out j hj, hv_out j hj⟩, ?_⟩
  intro i j
  rw [hr_eq i j]
  simp only [D1, Bool.xor_assoc]
