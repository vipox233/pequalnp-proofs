import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_783

open Finset Polynomial

theorem irr (m : ℕ) : Irreducible (X ^ (2 ^ m) + 1 : ℚ[X]) := by
  have h := Polynomial.cyclotomic.irreducible_rat (n := 2 ^ (m + 1)) (by positivity)
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two] at h
  simpa [Finset.sum_range_succ, add_comm] using h

theorem deg_f (R : Type) [CommRing R] [Nontrivial R] (m : ℕ) :
    (X ^ (2 ^ m) + 1 : R[X]).degree = (2 ^ m : ℕ) := by
  have := Polynomial.degree_X_pow_add_C (R := R) (n := 2 ^ m) (by positivity) 1
  simpa using this

theorem coeff_fin_sum {R : Type} [CommRing R] {n : ℕ} (f : Fin n → R) (k : Fin n) :
    (∑ i : Fin n, C (f i) * X ^ (i : ℕ)).coeff k = f k := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    have : (k : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

theorem no_zero_div (m : ℕ) (r : Fin (2 ^ m) → ℝ) (w : Fin (2 ^ m) → ℤ) (hw : ∃ k, w k ≠ 0)
    (h : AdjoinRoot.mk (X ^ (2 ^ m) + 1 : ℝ[X]) (∑ k : Fin (2 ^ m), C (r k) * X ^ (k : ℕ)) *
       AdjoinRoot.mk (X ^ (2 ^ m) + 1 : ℝ[X]) (∑ k : Fin (2 ^ m), C ((w k : ℝ)) * X ^ (k : ℕ)) = 0) :
    ∀ k, r k = 0 := by
  have : Fact (Irreducible (X ^ (2 ^ m) + 1 : ℚ[X])) := ⟨irr m⟩
  set Wq : ℚ[X] := ∑ k : Fin (2 ^ m), C ((w k : ℚ)) * X ^ (k : ℕ) with hWq
  have hWq0 : Wq ≠ 0 := by
    obtain ⟨k, hk⟩ := hw
    intro h0
    have := coeff_fin_sum (fun i => ((w i : ℚ))) k
    rw [← hWq, h0] at this
    simp at this
    exact hk (by exact_mod_cast this.symm)
  have hmk : AdjoinRoot.mk (X ^ (2 ^ m) + 1 : ℚ[X]) Wq ≠ 0 := by
    intro h0
    rw [AdjoinRoot.mk_eq_zero] at h0
    apply hWq0
    apply Polynomial.eq_zero_of_dvd_of_degree_lt h0
    rw [deg_f ℚ m]
    exact Polynomial.degree_sum_fin_lt _
  have hunit : IsUnit (AdjoinRoot.mk (X ^ (2 ^ m) + 1 : ℚ[X]) Wq) := Ne.isUnit hmk
  have hdvd : (X ^ (2 ^ m) + 1 : ℝ[X]) ∣ (X ^ (2 ^ m) + 1 : ℚ[X]).map (algebraMap ℚ ℝ) := by
    simp
  let φ := AdjoinRoot.map (algebraMap ℚ ℝ) (X ^ (2 ^ m) + 1 : ℚ[X]) (X ^ (2 ^ m) + 1 : ℝ[X]) hdvd
  have hφ : φ (AdjoinRoot.mk (X ^ (2 ^ m) + 1 : ℚ[X]) Wq) =
      AdjoinRoot.mk (X ^ (2 ^ m) + 1 : ℝ[X]) (∑ k : Fin (2 ^ m), C ((w k : ℝ)) * X ^ (k : ℕ)) := by
    simp only [φ, hWq, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.map_of, AdjoinRoot.map_root]
    simp
  have hunitR := hunit.map φ
  rw [hφ] at hunitR
  have hR := (hunitR.mul_left_eq_zero).1 h
  rw [AdjoinRoot.mk_eq_zero] at hR
  have hR0 := Polynomial.eq_zero_of_dvd_of_degree_lt hR (by
    rw [deg_f ℝ m]; exact Polynomial.degree_sum_fin_lt _)
  intro k
  have := coeff_fin_sum r k
  rw [hR0] at this
  simpa using this.symm

abbrev Aq (a : ℕ) := AdjoinRoot (X ^ (2 ^ a) + 1 : ℝ[X])

noncomputable abbrev θ (a : ℕ) : Aq a := AdjoinRoot.root (X ^ (2 ^ a) + 1 : ℝ[X])

theorem θ_half (a : ℕ) : θ a ^ (2 ^ a) = -1 := by
  have h : AdjoinRoot.mk (X ^ (2 ^ a) + 1 : ℝ[X]) (X ^ (2 ^ a) + 1) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem θ_full (a : ℕ) : θ a ^ (2 ^ (a + 1)) = 1 := by
  rw [pow_succ, pow_mul, θ_half]
  norm_num

theorem θ_mod (a x : ℕ) : θ a ^ x = θ a ^ (x % 2 ^ (a + 1)) := by
  conv_lhs => rw [← Nat.div_add_mod x (2 ^ (a + 1)), pow_add, pow_mul, θ_full, one_pow, one_mul]

noncomputable def Φ (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) : Aq a :=
  ∑ k : Fin (2 ^ (a + 1)), f k • θ a ^ (k : ℕ)

noncomputable def Ψ (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) : Aq a :=
  ∑ k : Fin (2 ^ (a + 1)), f k • θ a ^ ((-k : Fin (2 ^ (a + 1))) : ℕ)

theorem θ_val_add (a : ℕ) (x y : Fin (2 ^ (a + 1))) :
    θ a ^ ((x + y : Fin (2 ^ (a + 1))) : ℕ) = θ a ^ (x : ℕ) * θ a ^ (y : ℕ) := by
  rw [Fin.val_add, ← θ_mod, pow_add]

theorem conv_Φ (a : ℕ) (p w : Fin (2 ^ (a + 1)) → ℝ) :
    Φ a (fun i => ∑ s, p s * w (i + s)) = Ψ a p * Φ a w := by
  have : NeZero (2 ^ (a + 1)) := ⟨by positivity⟩
  have key : ∀ s, (p s • θ a ^ ((-s : Fin (2 ^ (a + 1))) : ℕ)) * Φ a w =
      ∑ i, (p s * w (i + s)) • θ a ^ (i : ℕ) := by
    intro s
    rw [Φ, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight s)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Equiv.coe_addRight]
    rw [smul_mul_smul_comm, ← θ_val_add, show -s + (i + s) = i by abel]
  rw [Ψ, Finset.sum_mul]
  simp_rw [key]
  rw [Φ]
  simp_rw [Finset.sum_smul]
  exact Finset.sum_comm

def Mf (a : ℕ) : Fin (2 ^ (a + 1)) := ⟨2 ^ a, Nat.pow_lt_pow_right (by norm_num) (by omega)⟩

theorem Mf_add_Mf (a : ℕ) : Mf a + Mf a = 0 := by
  ext
  simp only [Mf, Fin.val_add, Fin.val_zero]
  rw [pow_succ, ← two_mul, mul_comm, Nat.mod_self]

theorem neg_Mf (a : ℕ) : -Mf a = Mf a := by
  have : NeZero (2 ^ (a + 1)) := ⟨by positivity⟩
  rw [neg_eq_iff_add_eq_zero, Mf_add_Mf]


noncomputable def ext (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) (x : ℕ) : ℝ :=
  if h : x < 2 ^ (a + 1) then f ⟨x, h⟩ else 0

theorem lt_full (a x : ℕ) (hx : x < 2 ^ a) : x < 2 ^ (a + 1) := by
  rw [pow_succ]; omega

theorem add_Mf_val (a x : ℕ) (hx : x < 2 ^ a) :
    (⟨x, lt_full a x hx⟩ + Mf a : Fin (2 ^ (a + 1))) = ⟨2 ^ a + x, by rw [pow_succ]; omega⟩ := by
  ext
  simp only [Fin.val_add, Mf]
  rw [Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  omega

theorem fold_anti (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) (hf : ∀ k, f (k + Mf a) = - f k) :
    Φ a f = (2 : ℝ) • ∑ k : Fin (2 ^ a), ext a f k • θ a ^ (k : ℕ) := by
  have h1 : Φ a f = ∑ k : Fin (2 ^ (a + 1)), ext a f k • θ a ^ (k : ℕ) := by
    simp only [Φ, ext, Fin.is_lt, ↓reduceDIte]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k => ext a f k • θ a ^ k),
    Fin.sum_univ_eq_sum_range (fun k => ext a f k • θ a ^ k)]
  have hM : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by rw [pow_succ]; omega
  rw [hM, Finset.sum_range_add, two_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_range] at hx
  have he : ext a f (2 ^ a + x) = - ext a f x := by
    simp only [ext, lt_full a x hx, ↓reduceDIte, show 2 ^ a + x < 2 ^ (a + 1) by rw [pow_succ]; omega]
    rw [← hf, add_Mf_val a x hx]
  rw [he, pow_add, θ_half]
  simp

theorem mk_sum (a : ℕ) (g : Fin (2 ^ a) → ℝ) :
    AdjoinRoot.mk (X ^ (2 ^ a) + 1 : ℝ[X]) (∑ k : Fin (2 ^ a), C (g k) * X ^ (k : ℕ)) =
      ∑ k : Fin (2 ^ a), g k • θ a ^ (k : ℕ) := by
  simp only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, Algebra.smul_def]
  rfl

theorem anti_zero (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) (hf : ∀ k, f (k + Mf a) = - f k)
    (h0 : ∀ x < 2 ^ a, ext a f x = 0) : ∀ k, f k = 0 := by
  intro k
  by_cases hk : (k : ℕ) < 2 ^ a
  · have := h0 k hk
    simpa [ext, k.isLt] using this
  · have hk' : (k : ℕ) - 2 ^ a < 2 ^ a := by
      have := k.isLt
      have e : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
      omega
    have := h0 _ hk'
    simp only [ext, lt_full a _ hk', ↓reduceDIte] at this
    have e : (⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ + Mf a : Fin (2 ^ (a + 1))) = k := by
      rw [add_Mf_val a _ hk']; ext; simp only; omega
    calc f k = f (⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ + Mf a) := by rw [e]
      _ = 0 := by rw [hf, this, neg_zero]

theorem top_lemma (a : ℕ) (p : Fin (2 ^ (a + 1)) → ℝ) (v : Fin (2 ^ (a + 1)) → ℤ)
    (hd : ∀ i, ∑ s, p s * ((v (i + s) : ℝ) - v (i + s + Mf a)) = 0) :
    (∀ k, v k = v (k + Mf a)) ∨ (∀ s, p s = p (s + Mf a)) := by
  have : NeZero (2 ^ (a + 1)) := ⟨by positivity⟩
  have hMM := Mf_add_Mf a
  by_cases hv : ∀ k, v k = v (k + Mf a)
  · exact Or.inl hv
  right
  let w : Fin (2 ^ (a + 1)) → ℝ := fun k => (v k : ℝ) - v (k + Mf a)
  have hw : ∀ k, w (k + Mf a) = - w k := by
    intro k; simp only [w, add_assoc, hMM, add_zero]; ring
  let r : Fin (2 ^ (a + 1)) → ℝ := fun s => p s - p (s + Mf a)
  have hd2 : ∀ i, ∑ s, r s * w (i + s) = 0 := by
    intro i
    have e1 : ∑ s, p (s + Mf a) * w (i + s) = - ∑ s, p s * w (i + s) := by
      rw [← Equiv.sum_comp (Equiv.addRight (Mf a))]
      simp only [Equiv.coe_addRight, add_assoc, hMM, add_zero]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s _
      have : i + (s + Mf a) = (i + s) + Mf a := by abel
      rw [this, hw]; ring
    simp only [r, sub_mul, Finset.sum_sub_distrib, e1]
    have := hd i
    simp only [w] at *
    rw [this]; ring
  let rb : Fin (2 ^ (a + 1)) → ℝ := fun t => r (-t)
  have hrb : ∀ k, rb (k + Mf a) = - rb k := by
    intro k
    simp only [rb, r]
    have e : -(k + Mf a) = -k + Mf a := by rw [neg_add, neg_Mf]
    rw [e, add_assoc, hMM, add_zero]; ring
  have hΨ : Ψ a r = Φ a rb := by
    simp only [Ψ, Φ, rb]
    rw [← Equiv.sum_comp (Equiv.neg (Fin (2 ^ (a + 1))))]
    simp
  have hprod : Φ a rb * Φ a w = 0 := by
    rw [← hΨ, ← conv_Φ]
    simp only [Φ, hd2, zero_smul, Finset.sum_const_zero]
  rw [fold_anti a rb hrb, fold_anti a w hw, smul_mul_smul_comm] at hprod
  have hprod' : (∑ k : Fin (2 ^ a), ext a rb k • θ a ^ (k : ℕ)) *
      (∑ k : Fin (2 ^ a), ext a w k • θ a ^ (k : ℕ)) = 0 := by
    have := congrArg (fun z => ((2 : ℝ) * 2)⁻¹ • z) hprod
    simpa [smul_smul] using this
  let wz : Fin (2 ^ a) → ℤ := fun k =>
    v ⟨k, lt_full a k k.isLt⟩ - v (⟨k, lt_full a k k.isLt⟩ + Mf a)
  have hwz : ∀ k : Fin (2 ^ a), ext a w k = (wz k : ℝ) := by
    intro k
    simp [ext, lt_full a k k.isLt, w, wz]
  have hwz0 : ∃ k, wz k ≠ 0 := by
    push Not at hv
    obtain ⟨k, hk⟩ := hv
    by_cases hk1 : (k : ℕ) < 2 ^ a
    · refine ⟨⟨k, hk1⟩, ?_⟩
      simp only [wz]
      have e : (⟨(k : ℕ), lt_full a k hk1⟩ : Fin (2 ^ (a + 1))) = k := rfl
      rw [e]; omega
    · have hk' : (k : ℕ) - 2 ^ a < 2 ^ a := by
        have := k.isLt
        have e : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
        omega
      refine ⟨⟨(k : ℕ) - 2 ^ a, hk'⟩, ?_⟩
      have e : (⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ + Mf a : Fin (2 ^ (a + 1))) = k := by
        rw [add_Mf_val a _ hk']; ext; simp only; omega
      simp only [wz]
      rw [e]
      have e2 : k + Mf a = ⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ := by
        calc k + Mf a = (⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ + Mf a) + Mf a := by rw [e]
          _ = _ := by rw [add_assoc, hMM, add_zero]
      rw [e2] at hk
      omega
  have key := no_zero_div a (fun k => ext a rb k) wz hwz0 (by
    rw [mk_sum, mk_sum]
    simpa [hwz] using hprod')
  have hall := anti_zero a rb hrb (fun x hx => key ⟨x, hx⟩)
  intro s
  have := hall (-s)
  simp only [rb, r, neg_neg] at this
  linarith

theorem lt_full3 (a x : ℕ) (hx : x < 2 ^ a) : x + 2 ^ a < 2 ^ (a + 1) := by
  rw [pow_succ]; omega

theorem lt_full2 (a x : ℕ) (hx : x < 2 ^ a) : 2 ^ a + x < 2 ^ (a + 1) := by
  rw [pow_succ]; omega

def emb (a : ℕ) (h : Fin (2 ^ a)) : Fin (2 ^ (a + 1)) := ⟨h, lt_full a h h.isLt⟩

def prj (a : ℕ) (k : Fin (2 ^ (a + 1))) : Fin (2 ^ a) := ⟨k % 2 ^ a, Nat.mod_lt _ (by positivity)⟩

theorem split_sum {M : Type} [AddCommMonoid M] (a : ℕ) (g : Fin (2 ^ (a + 1)) → M) :
    ∑ k, g k = ∑ h : Fin (2 ^ a), (g (emb a h) + g (emb a h + Mf a)) := by
  let G : ℕ → M := fun x => if hx : x < 2 ^ (a + 1) then g ⟨x, hx⟩ else 0
  have h1 : ∑ k, g k = ∑ k : Fin (2 ^ (a + 1)), G k := by
    simp only [G, Fin.is_lt, ↓reduceDIte]
  have h2 : ∑ h : Fin (2 ^ a), (g (emb a h) + g (emb a h + Mf a)) =
      ∑ h : Fin (2 ^ a), (G h + G (2 ^ a + h)) := by
    apply Finset.sum_congr rfl
    intro h _
    simp only [G, lt_full a h h.isLt, ↓reduceDIte, emb,
      lt_full2 a h h.isLt]
    rw [add_Mf_val a h h.isLt]
  rw [h1, h2, Fin.sum_univ_eq_sum_range G, Fin.sum_univ_eq_sum_range (fun x => G x + G (2 ^ a + x)),
    Finset.sum_add_distrib, ← Finset.sum_range_add]
  congr 1
  rw [pow_succ]; ring

theorem prj_emb (a : ℕ) (h : Fin (2 ^ a)) : prj a (emb a h) = h := by
  ext; simp [prj, emb, Nat.mod_eq_of_lt h.isLt]

theorem prj_emb_Mf (a : ℕ) (h : Fin (2 ^ a)) : prj a (emb a h + Mf a) = h := by
  ext
  simp only [prj, emb]
  rw [add_Mf_val a h h.isLt]
  simp [Nat.mod_eq_of_lt h.isLt]

theorem prj_add (a : ℕ) (x y : Fin (2 ^ (a + 1))) : prj a (x + y) = prj a x + prj a y := by
  ext
  simp only [prj, Fin.val_add]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ a)), Nat.add_mod]

def push {M : Type} [AddCommMonoid M] (a : ℕ) (f : Fin (2 ^ (a + 1)) → M) (h : Fin (2 ^ a)) : M :=
  f (emb a h) + f (emb a h + Mf a)

theorem push_prj {M : Type} [AddCommMonoid M] (a : ℕ) (f : Fin (2 ^ (a + 1)) → M)
    (k : Fin (2 ^ (a + 1))) : push a f (prj a k) = f k + f (k + Mf a) := by
  have hMM := Mf_add_Mf a
  have : NeZero (2 ^ (a + 1)) := ⟨by positivity⟩
  by_cases hk : (k : ℕ) < 2 ^ a
  · have e : emb a (prj a k) = k := by ext; simp [emb, prj, Nat.mod_eq_of_lt hk]
    simp only [push, e]
  · have hk' : (k : ℕ) - 2 ^ a < 2 ^ a := by
      have := k.isLt
      have e : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
      omega
    have e1 : emb a (prj a k) + Mf a = k := by
      have : emb a (prj a k) = ⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ := by
        ext
        simp only [emb, prj]
        have := k.isLt
        have e : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hk']
      rw [this, add_Mf_val a _ hk']
      ext; simp only; omega
    have e2 : emb a (prj a k) = k + Mf a := by
      calc emb a (prj a k) = emb a (prj a k) + Mf a + Mf a := by rw [add_assoc, hMM, add_zero]
        _ = k + Mf a := by rw [e1]
    simp only [push]
    rw [e1, e2, add_comm]

theorem sum_prj (a : ℕ) (F : Fin (2 ^ (a + 1)) → ℝ)
    (G : Fin (2 ^ a) → ℝ) :
    ∑ s, F s * G (prj a s) = ∑ h, push a F h * G h := by
  rw [split_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [push, prj_emb, prj_emb_Mf, add_mul]

def sib (a : ℕ) (f : Fin (2 ^ a) → ℝ) (j h : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ a) => (i : ℕ) % 2 ^ (j + 1) = h), f i

def sibEq (a : ℕ) (f : Fin (2 ^ a) → ℝ) (j : ℕ) : Prop :=
  ∀ h < 2 ^ j, sib a f j h = sib a f j (h + 2 ^ j)

def bal (a : ℕ) (p v : Fin (2 ^ a) → ℝ) : Prop :=
  ∀ i i' : Fin (2 ^ a), ∑ s, p s * v (i + s) = ∑ s, p s * v (i' + s)

theorem mod_shift (x a j : ℕ) (hj : j < a) : (x + 2 ^ a) % 2 ^ (j + 1) = x % 2 ^ (j + 1) := by
  obtain ⟨c, hc⟩ : 2 ^ (j + 1) ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
  rw [hc, Nat.add_mul_mod_self_left]

theorem sib_push (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) (j h : ℕ) (hj : j < a) :
    sib (a + 1) f j h = sib a (push a f) j h := by
  simp only [sib, Finset.sum_filter]
  rw [split_sum]
  apply Finset.sum_congr rfl
  intro x _
  have e1 : ((emb a x : Fin (2 ^ (a + 1))) : ℕ) % 2 ^ (j + 1) = (x : ℕ) % 2 ^ (j + 1) := rfl
  have e2 : ((emb a x + Mf a : Fin (2 ^ (a + 1))) : ℕ) % 2 ^ (j + 1) = (x : ℕ) % 2 ^ (j + 1) := by
    simp only [emb]
    rw [add_Mf_val a x x.isLt]
    simp only
    rw [add_comm]
    exact mod_shift x a j hj
  simp only [push, e1, e2]
  split_ifs <;> simp

theorem cond_push (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) (j : ℕ) (hj : j < a) :
    sibEq (a + 1) f j ↔ sibEq a (push a f) j := by
  simp only [sibEq, sib_push a f j _ hj]

theorem cond_top (a : ℕ) (f : Fin (2 ^ (a + 1)) → ℝ) :
    sibEq (a + 1) f a ↔ ∀ k, f k = f (k + Mf a) := by
  have hsingle : ∀ x (hx : x < 2 ^ (a + 1)), sib (a + 1) f a x = f ⟨x, hx⟩ := by
    intro x hx
    simp only [sib]
    rw [Finset.sum_eq_single ⟨x, hx⟩]
    · intro b hb hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      apply absurd _ hne
      ext
      simp only
      rw [Nat.mod_eq_of_lt b.isLt] at hb
      exact hb
    · intro hn
      exact absurd (by simp [Nat.mod_eq_of_lt hx]) hn
  have e2a : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
  constructor
  · intro hc k
    by_cases hk : (k : ℕ) < 2 ^ a
    · have := hc k hk
      rw [hsingle _ (lt_full a _ hk), hsingle _ (lt_full3 a _ hk)] at this
      have e : k + Mf a = ⟨(k : ℕ) + 2 ^ a, lt_full3 a _ hk⟩ := by
        ext
        simp only [Fin.val_add, Mf]
        rw [Nat.mod_eq_of_lt (lt_full3 a _ hk)]
      rw [e]
      exact this
    · have hk' : (k : ℕ) - 2 ^ a < 2 ^ a := by
        have := k.isLt
        omega
      have := hc _ hk'
      rw [hsingle _ (lt_full a _ hk'), hsingle _ (lt_full3 a _ hk')] at this
      have e1 : k = ⟨(k : ℕ) - 2 ^ a + 2 ^ a, lt_full3 a _ hk'⟩ := by
        ext; simp only; omega
      have e2 : k + Mf a = ⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ := by
        ext
        simp only [Fin.val_add, Mf]
        have := k.isLt
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [e2]
      calc f k = f ⟨(k : ℕ) - 2 ^ a + 2 ^ a, lt_full3 a _ hk'⟩ := congrArg f e1
        _ = _ := this.symm
  · intro hk h hh
    rw [hsingle _ (lt_full a _ hh), hsingle _ (lt_full3 a _ hh)]
    rw [hk ⟨h, lt_full a h hh⟩]
    congr 1
    ext
    simp only [Fin.val_add, Mf]
    rw [Nat.mod_eq_of_lt (lt_full3 a _ hh)]

theorem conv_push (a : ℕ) (p v : Fin (2 ^ (a + 1)) → ℝ) (i : Fin (2 ^ (a + 1))) :
    ∑ h, push a p h * push a v (prj a i + h) =
      (∑ s, p s * v (i + s)) + ∑ s, p s * v ((i + Mf a) + s) := by
  rw [← sum_prj a p (fun h => push a v (prj a i + h)), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← prj_add, push_prj, mul_add]
  congr 3
  abel

theorem bal_succ (a : ℕ) (p v : Fin (2 ^ (a + 1)) → ℝ) :
    bal (a + 1) p v ↔ bal a (push a p) (push a v) ∧
      ∀ i, ∑ s, p s * v (i + s) = ∑ s, p s * v ((i + Mf a) + s) := by
  constructor
  · intro hb
    refine ⟨fun h h' => ?_, fun i => hb i (i + Mf a)⟩
    have e1 := conv_push a p v (emb a h)
    have e2 := conv_push a p v (emb a h')
    rw [prj_emb] at e1 e2
    rw [e1, e2]
    have := hb (emb a h) (emb a h')
    have := hb (emb a h + Mf a) (emb a h')
    have := hb (emb a h' + Mf a) (emb a h')
    linarith
  · rintro ⟨hb, hM⟩ i i'
    have e1 := conv_push a p v i
    have e2 := conv_push a p v i'
    have := hb (prj a i) (prj a i')
    have h1 := hM i
    have h2 := hM i'
    linarith

theorem shift_cond (a : ℕ) (p v : Fin (2 ^ (a + 1)) → ℝ) :
    (∀ i, ∑ s, p s * v (i + s) = ∑ s, p s * v ((i + Mf a) + s)) ↔
      (∀ i, ∑ s, p s * (v (i + s) - v (i + s + Mf a)) = 0) := by
  have e : ∀ i s : Fin (2 ^ (a + 1)), (i + Mf a) + s = i + s + Mf a := fun i s => by abel
  constructor
  · intro h i
    simp only [mul_sub, Finset.sum_sub_distrib, ← e, h i, sub_self]
  · intro h i
    have := h i
    simp only [mul_sub, Finset.sum_sub_distrib, ← e] at this
    linarith

theorem top_iff (a : ℕ) (p : Fin (2 ^ (a + 1)) → ℝ) (v : Fin (2 ^ (a + 1)) → ℤ) :
    (∀ i, ∑ s, p s * ((v (i + s) : ℝ) - v (i + s + Mf a)) = 0) ↔
      sibEq (a + 1) (fun i => (v i : ℝ)) a ∨ sibEq (a + 1) p a := by
  rw [cond_top, cond_top]
  have hMM := Mf_add_Mf a
  constructor
  · intro h
    rcases top_lemma a p v h with hv | hp
    · left; intro k; exact_mod_cast hv k
    · right; exact hp
  · rintro (hv | hp) i
    · apply Finset.sum_eq_zero
      intro s _
      rw [← hv (i + s), sub_self, mul_zero]
    · have e1 : ∑ s, p s * (v (i + s + Mf a) : ℝ) = ∑ s, p s * (v (i + s) : ℝ) := by
        rw [← Equiv.sum_comp (Equiv.addRight (Mf a))]
        apply Finset.sum_congr rfl
        intro s _
        simp only [Equiv.coe_addRight]
        rw [← hp s]
        congr 3
        rw [show i + (s + Mf a) + Mf a = i + s + (Mf a + Mf a) by abel, hMM, add_zero]
      simp only [mul_sub, Finset.sum_sub_distrib, e1, sub_self]

theorem char (a : ℕ) : ∀ (p : Fin (2 ^ a) → ℝ) (v : Fin (2 ^ a) → ℤ),
    bal a p (fun i => (v i : ℝ)) ↔ ∀ j < a, sibEq a (fun i => (v i : ℝ)) j ∨ sibEq a p j := by
  induction a with
  | zero =>
    intro p v
    constructor
    · intro _ j hj; omega
    · intro _ i i'
      have : i = i' := by
        have h1 := i.isLt
        have h2 := i'.isLt
        simp only [pow_zero] at h1 h2
        ext; omega
      rw [this]
  | succ a ih =>
    intro p v
    have hpv := ih (push a p) (push a v)
    have hcast : (fun i => ((push a v i : ℤ) : ℝ)) = push a (fun i => (v i : ℝ)) := by
      funext i; simp [push]
    rw [hcast] at hpv
    have hT : (∀ i, ∑ s, p s * (v (i + s) : ℝ) = ∑ s, p s * (v ((i + Mf a) + s) : ℝ)) ↔
        sibEq (a + 1) (fun i => (v i : ℝ)) a ∨ sibEq (a + 1) p a :=
      (shift_cond a p (fun i => (v i : ℝ))).trans (top_iff a p v)
    rw [bal_succ, hpv, hT]
    constructor
    · rintro ⟨hlow, htop⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [cond_push a _ j hj, cond_push a _ j hj]
        exact hlow j hj
      · exact htop
    · intro h
      refine ⟨fun j hj => ?_, h a (Nat.lt_succ_self a)⟩
      rw [← cond_push a _ j hj, ← cond_push a _ j hj]
      exact h j (by omega)

theorem emb_prj_Mf (a : ℕ) (k : Fin (2 ^ (a + 1))) (hk : ¬ (k : ℕ) < 2 ^ a) :
    emb a (prj a k) + Mf a = k := by
  have hk' : (k : ℕ) - 2 ^ a < 2 ^ a := by
    have := k.isLt
    have e : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
    omega
  have : emb a (prj a k) = ⟨(k : ℕ) - 2 ^ a, lt_full a _ hk'⟩ := by
    ext
    simp only [emb, prj]
    have := k.isLt
    have e : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hk']
  rw [this, add_Mf_val a _ hk']
  ext; simp only; omega

theorem decomp (a : ℕ) (k : Fin (2 ^ (a + 1))) :
    k = emb a (prj a k) ∨ k = emb a (prj a k) + Mf a := by
  by_cases hk : (k : ℕ) < 2 ^ a
  · left; ext; simp [emb, prj, Nat.mod_eq_of_lt hk]
  · right; exact (emb_prj_Mf a k hk).symm

def inC (a : ℕ) (A : Finset ℕ) (x : ℕ) : Prop := ∀ j < a, x.testBit j = true → j ∈ A

instance (a : ℕ) (A : Finset ℕ) (x : ℕ) : Decidable (inC a A x) := by
  unfold inC; infer_instance

theorem inC_emb (a : ℕ) (A : Finset ℕ) (h : Fin (2 ^ a)) :
    inC (a + 1) A (emb a h : ℕ) ↔ inC a A h := by
  simp only [inC, emb]
  constructor
  · intro H j hj hb; exact H j (by omega) hb
  · intro H j hj hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact H j hj hb
    · rw [Nat.testBit_lt_two_pow h.isLt] at hb; exact absurd hb (by simp)

theorem inC_embMf (a : ℕ) (A : Finset ℕ) (h : Fin (2 ^ a)) :
    inC (a + 1) A ((emb a h + Mf a : Fin (2 ^ (a + 1))) : ℕ) ↔ a ∈ A ∧ inC a A h := by
  simp only [emb]
  rw [add_Mf_val a h h.isLt]
  simp only [inC]
  constructor
  · intro H
    refine ⟨H a (Nat.lt_succ_self a) ?_, fun j hj hb => H j (by omega) ?_⟩
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h.isLt]; rfl
    · rw [Nat.testBit_two_pow_add_gt hj]; exact hb
  · rintro ⟨ha, H⟩ j hj hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [Nat.testBit_two_pow_add_gt hj] at hb; exact H j hj hb
    · exact ha

theorem inC_erase (a : ℕ) (A : Finset ℕ) (x : ℕ) : inC a (A.erase a) x ↔ inC a A x := by
  simp only [inC, Finset.mem_erase]
  constructor
  · intro H j hj hb; exact (H j hj hb).2
  · intro H j hj hb; exact ⟨by omega, H j hj hb⟩

theorem coins_card (a : ℕ) : ∀ A : Finset ℕ, (∀ j ∈ A, j < a) →
    (Finset.univ.filter (fun s : Fin (2 ^ a) => inC a A s)).card = 2 ^ A.card := by
  induction a with
  | zero =>
    intro A hA
    have hA0 : A = ∅ := Finset.eq_empty_of_forall_notMem (fun j hj => by have := hA j hj; omega)
    subst hA0
    have : Finset.univ.filter (fun s : Fin (2 ^ 0) => inC 0 ∅ s) = Finset.univ := by
      ext s; simp [inC]
    rw [this]
    simp
  | succ a ih =>
    intro A hA
    have hA' : ∀ j ∈ A.erase a, j < a := by
      intro j hj
      have := Finset.mem_erase.1 hj
      have := hA j this.2
      omega
    have IH := ih (A.erase a) hA'
    rw [Finset.card_filter, split_sum]
    simp only [inC_emb, inC_embMf]
    have hc : (Finset.univ.filter (fun s : Fin (2 ^ a) => inC a A s)).card = 2 ^ (A.erase a).card := by
      rw [← IH]; congr 1; ext s; simp [inC_erase]
    by_cases ha : a ∈ A
    · simp only [ha, true_and, ← two_mul, ← Finset.mul_sum, ← Finset.card_filter, hc]
      rw [Finset.card_erase_of_mem ha, ← pow_succ']
      congr 1
      have := Finset.card_pos.2 ⟨a, ha⟩
      omega
    · simp only [ha, false_and, ↓reduceIte, add_zero, ← Finset.card_filter, hc,
        Finset.erase_eq_of_notMem ha]

theorem cond_smul (a : ℕ) (f : Fin (2 ^ a) → ℝ) (c : ℝ) (j : ℕ) (h : sibEq a f j) :
    sibEq a (fun i => c * f i) j := by
  intro x hx
  have := h x hx
  simp only [sib] at this ⊢
  rw [← Finset.mul_sum, ← Finset.mul_sum, this]

theorem coins_cond (a : ℕ) : ∀ A : Finset ℕ, (∀ j ∈ A, j < a) → ∀ j ∈ A,
    sibEq a (fun s : Fin (2 ^ a) => if inC a A s then (1 : ℝ) else 0) j := by
  induction a with
  | zero => intro A hA j hj; have := hA j hj; omega
  | succ a ih =>
    intro A hA j hj
    have hja := hA j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hja with hlt | heq
    · rw [cond_push a _ j hlt]
      have hA' : ∀ j ∈ A.erase a, j < a := by
        intro i hi
        have := Finset.mem_erase.1 hi
        have := hA i this.2
        omega
      have IH := ih (A.erase a) hA' j (Finset.mem_erase.2 ⟨by omega, hj⟩)
      have hpush : push a (fun s : Fin (2 ^ (a + 1)) => if inC (a + 1) A s then (1 : ℝ) else 0) =
          fun s : Fin (2 ^ a) => (if a ∈ A then (2 : ℝ) else 1) *
            (if inC a (A.erase a) (s : ℕ) then (1 : ℝ) else 0) := by
        funext s
        simp only [push, inC_emb, inC_embMf, inC_erase]
        by_cases h1 : a ∈ A <;> by_cases h2 : inC a A s <;> simp [h1, h2] <;> norm_num
      rw [hpush]
      exact cond_smul a _ _ j IH
    · rw [heq] at hj ⊢
      rw [cond_top]
      have hMM := Mf_add_Mf a
      have key : ∀ h : Fin (2 ^ a), inC (a + 1) A (emb a h : ℕ) ↔
          inC (a + 1) A ((emb a h + Mf a : Fin (2 ^ (a + 1))) : ℕ) := by
        intro h; rw [inC_emb, inC_embMf]; simp [hj]
      intro k
      rcases decomp a k with e | e
      · rw [e]; simp only [key]
      · rw [e, add_assoc, hMM, add_zero]; simp only [key]

theorem supp_bound (a : ℕ) : ∀ (p : Fin (2 ^ a) → ℝ) (A : Finset ℕ), (∀ s, 0 ≤ p s) →
    (∃ s, 0 < p s) → (∀ j ∈ A, j < a ∧ sibEq a p j) →
    2 ^ A.card ≤ (Finset.univ.filter (fun s => 0 < p s)).card := by
  induction a with
  | zero =>
    intro p A _ hpos hA
    have hA0 : A = ∅ := Finset.eq_empty_of_forall_notMem (fun j hj => by have := (hA j hj).1; omega)
    subst hA0
    obtain ⟨s, hs⟩ := hpos
    simp only [Finset.card_empty, pow_zero]
    exact Finset.card_pos.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  | succ a ih =>
    intro p A hnn hpos hA
    have hpnn : ∀ h, 0 ≤ push a p h := fun h => add_nonneg (hnn _) (hnn _)
    have hppos : ∃ h, 0 < push a p h := by
      obtain ⟨s, hs⟩ := hpos
      refine ⟨prj a s, ?_⟩
      rw [push_prj]
      linarith [hnn (s + Mf a)]
    have hA' : ∀ j ∈ A.erase a, j < a ∧ sibEq a (push a p) j := by
      intro j hj
      obtain ⟨hne, hjA⟩ := Finset.mem_erase.1 hj
      obtain ⟨hlt, hc⟩ := hA j hjA
      have hlt' : j < a := by omega
      exact ⟨hlt', (cond_push a p j hlt').1 hc⟩
    have IH := ih (push a p) (A.erase a) hpnn hppos hA'
    rw [Finset.card_filter, split_sum]
    rw [Finset.card_filter] at IH
    by_cases ha : a ∈ A
    · have htop := (cond_top a p).1 (hA a ha).2
      have e : ∀ h : Fin (2 ^ a), ((if 0 < p (emb a h) then 1 else 0) +
          (if 0 < p (emb a h + Mf a) then 1 else 0) : ℕ) =
          2 * (if 0 < push a p h then 1 else 0) := by
        intro h
        simp only [push, ← htop (emb a h)]
        by_cases hp : 0 < p (emb a h)
        · simp [hp, show 0 < p (emb a h) + p (emb a h) by linarith]
        · have : ¬ 0 < p (emb a h) + p (emb a h) := by linarith [hnn (emb a h)]
          simp [hp, this]
      simp only [e, ← Finset.mul_sum]
      rw [Finset.card_erase_of_mem ha] at IH
      have hpos' := Finset.card_pos.2 ⟨a, ha⟩
      calc 2 ^ A.card = 2 * 2 ^ (A.card - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ ≤ _ := by omega
    · rw [Finset.erase_eq_of_notMem ha] at IH
      refine IH.trans (Finset.sum_le_sum fun h _ => ?_)
      have hpush : push a p h = p (emb a h) + p (emb a h + Mf a) := rfl
      by_cases h3 : 0 < push a p h
      · rw [if_pos h3]
        by_cases h1 : 0 < p (emb a h)
        · simp [h1]
        · have h2 : 0 < p (emb a h + Mf a) := by rw [hpush] at h3; linarith [hnn (emb a h)]
          simp [h2]
      · rw [if_neg h3]; omega

theorem charN (a : ℕ) (p : Fin (2 ^ a) → ℝ) (v : Fin (2 ^ a) → ℕ) :
    bal a p (fun i => (v i : ℝ)) ↔ ∀ j < a, sibEq a (fun i => (v i : ℝ)) j ∨ sibEq a p j := by
  have := char a p (fun i => (v i : ℤ))
  simpa using this

end PEqualNP.Outside.L_lib_783

theorem PEqualNP.Outside.L_lib_783 : (∀ (a : ℕ) (v : Fin (2^a) → ℕ),
  let I := Fin (2^a)
  let side := fun (j h : ℕ) => (Finset.univ : Finset I).filter (fun i => i.val % (2^(j+1)) = h)
  let active := (Finset.range a).filter (fun j => (List.range (2^j)).any (fun h => decide (
    (∑ i ∈ side j h, v i) ≠ ∑ i ∈ side j (h+2^j), v i)))
  let q := 2^active.card
  let coins := (Finset.univ : Finset I).filter (fun s =>
    (List.range a).all (fun j => !(s.val.testBit j) || decide (j ∈ active)))
  let balanced := fun (p : I → ℝ) =>
    ∀ i i' : I, (∑ s : I, p s * (v (i+s) : ℝ)) = ∑ s : I, p s * (v (i'+s) : ℝ)
  coins.card = q ∧ balanced (fun s => if s ∈ coins then 1/(q : ℝ) else 0) ∧
    ∀ p : I → ℝ, (∀ s, 0 ≤ p s) → (∑ s, p s) = 1 →
      (balanced p ↔ ∀ j ∈ active, ∀ h ∈ Finset.range (2^j),
        (∑ s ∈ side j h, p s) = ∑ s ∈ side j (h+2^j), p s) ∧
      (balanced p → q ≤ ((Finset.univ : Finset I).filter (fun s => 0 < p s)).card)) := by
  intro a v I side active q coins balanced
  have hK1 : ∀ j, j ∈ active ↔
      j < a ∧ ¬ PEqualNP.Outside.L_lib_783.sibEq a (fun i => (v i : ℝ)) j := by
    intro j
    simp only [active, side, PEqualNP.Outside.L_lib_783.sibEq, PEqualNP.Outside.L_lib_783.sib,
      Finset.mem_filter, Finset.mem_range, List.any_eq_true, List.mem_range, decide_eq_true_eq]
    push Not
    constructor
    · rintro ⟨hj, h, hh, hne⟩
      refine ⟨hj, h, hh, fun he => hne ?_⟩
      exact_mod_cast he
    · rintro ⟨hj, h, hh, hne⟩
      refine ⟨hj, h, hh, fun he => hne ?_⟩
      rw [← Nat.cast_sum, ← Nat.cast_sum]
      exact congrArg _ he
  have hK3 : ∀ j ∈ active, j < a := fun j hj => ((hK1 j).1 hj).1
  have hK2 : coins = Finset.univ.filter
      (fun s : Fin (2 ^ a) => PEqualNP.Outside.L_lib_783.inC a active s) := by
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    unfold PEqualNP.Outside.L_lib_783.inC
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq]
    constructor
    · intro H j hj hb
      rcases H j hj with h | h
      · rw [hb] at h; exact absurd h (by simp)
      · exact h
    · intro H j hj
      by_cases hb : (s : ℕ).testBit j = true
      · right; exact H j hj hb
      · left; simpa using hb
  have hiff : ∀ p : I → ℝ, balanced p ↔ ∀ j ∈ active, PEqualNP.Outside.L_lib_783.sibEq a p j := by
    intro p
    have hb := PEqualNP.Outside.L_lib_783.charN a p v
    change PEqualNP.Outside.L_lib_783.bal a p (fun i => (v i : ℝ)) ↔ _
    rw [hb]
    constructor
    · intro H j hj
      obtain ⟨hja, hn⟩ := (hK1 j).1 hj
      exact (H j hja).resolve_left hn
    · intro H j hja
      by_cases hj : j ∈ active
      · right; exact H j hj
      · left
        by_contra hc
        exact hj ((hK1 j).2 ⟨hja, hc⟩)
  have hfun : (fun s : I => if s ∈ coins then 1 / (q : ℝ) else 0) =
      fun s : Fin (2 ^ a) => (1 / (q : ℝ)) *
        (if PEqualNP.Outside.L_lib_783.inC a active s then (1 : ℝ) else 0) := by
    funext s
    rw [hK2]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hK2]
    exact PEqualNP.Outside.L_lib_783.coins_card a active hK3
  · rw [hiff, hfun]
    intro j hj
    exact PEqualNP.Outside.L_lib_783.cond_smul a _ _ j
      (PEqualNP.Outside.L_lib_783.coins_cond a active hK3 j hj)
  · intro p hnn hsum
    have hiff' : balanced p ↔ ∀ j ∈ active, ∀ h ∈ Finset.range (2 ^ j),
        (∑ s ∈ side j h, p s) = ∑ s ∈ side j (h + 2 ^ j), p s := by
      rw [hiff p]
      simp only [PEqualNP.Outside.L_lib_783.sibEq, PEqualNP.Outside.L_lib_783.sib,
        Finset.mem_range, side]
      constructor
      · intro H j hj h hh; exact H j hj h hh
      · intro H j hj h hh; exact H j hj h hh
    refine ⟨hiff', fun hb => ?_⟩
    have hpos : ∃ s, 0 < p s := by
      by_contra hc
      push Not at hc
      have : ∑ s, p s ≤ 0 := Finset.sum_nonpos (fun s _ => hc s)
      linarith
    exact PEqualNP.Outside.L_lib_783.supp_bound a p active hnn hpos
      (fun j hj => ⟨hK3 j hj, (hiff p).1 hb j hj⟩)

