import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.CardEmbedding

namespace PEqualNP.Outside.L_gct_312

open Finset

noncomputable def D (n m : ℕ) (g : Fin m → Fin n → ℂ) : ℂ :=
  ∑ f : Fin m ↪ Fin n, ∏ k, g k (f k)

lemma D_zero (n : ℕ) (g : Fin 0 → Fin n → ℂ) : D n 0 g = 1 := by
  simp [D]

lemma sum_not_range {n m : ℕ} (f : Fin m ↪ Fin n) (h : Fin n → ℂ) :
    ∑ i : {i // i ∉ Set.range f}, h i = (∑ i, h i) - ∑ k, h (f k) := by
  rw [eq_sub_iff_add_eq]
  have h1 : ∑ i : {i // i ∉ Set.range f}, h i =
      ∑ i ∈ univ.filter (fun i => i ∉ Set.range f), h i :=
    (Finset.sum_subtype _ (fun i => by simp) h).symm
  have h2 : ∑ k, h (f k) = ∑ i ∈ univ.filter (fun i => i ∈ Set.range f), h i := by
    have : univ.filter (fun i => i ∈ Set.range f) = univ.map f := by
      ext i; simp
    rw [this, Finset.sum_map]
  rw [h1, h2, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma prod_update {m n : ℕ} (t : Fin m → Fin n → ℂ) (g0 : Fin n → ℂ) (f : Fin m → Fin n)
    (k0 : Fin m) :
    ∏ k, (Function.update t k0 (t k0 * g0)) k (f k) = (∏ k, t k (f k)) * g0 (f k0) := by
  have : ∀ k, (Function.update t k0 (t k0 * g0)) k (f k) =
      t k (f k) * (if k = k0 then g0 (f k0) else 1) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp
    · simp [hk]
  simp_rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

lemma D_succ (n m : ℕ) (g : Fin (m + 1) → Fin n → ℂ) :
    D n (m + 1) g = (∑ i, g 0 i) * D n m (Fin.tail g) -
      ∑ k : Fin m, D n m (Function.update (Fin.tail g) k (Fin.tail g k * g 0)) := by
  unfold D
  rw [← (Equiv.embeddingFinSucc m (Fin n)).symm.sum_comp, Fintype.sum_sigma]
  simp only [Equiv.coe_embeddingFinSucc_symm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [prod_update]
  have inner : ∀ f : Fin m ↪ Fin n, ∑ i : {i // i ∉ Set.range f}, g 0 i * ∏ k, g k.succ (f k)
      = (∏ k, Fin.tail g k (f k)) * ((∑ i, g 0 i) - ∑ k, g 0 (f k)) := by
    intro f
    rw [← Finset.sum_mul, sum_not_range, mul_comm]; rfl
  simp_rw [inner]
  rw [Finset.sum_comm (f := fun k (f : Fin m ↪ Fin n) => (∏ k, Fin.tail g k (f k)) * g 0 (f k))]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro f _; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

lemma D_one (n : ℕ) (g : Fin 1 → Fin n → ℂ) : D n 1 g = ∑ i, g 0 i := by
  rw [D_succ, D_zero]; simp

lemma D_two (n : ℕ) (g : Fin 2 → Fin n → ℂ) :
    D n 2 g = (∑ i, g 0 i) * (∑ i, g 1 i) - ∑ i, g 1 i * g 0 i := by
  rw [D_succ, D_one]; simp [D_one, Fin.tail]

lemma msum {n : ℕ} (x : Fin n → ℂ) (c0 c1 c2 c3 c4 : ℂ) :
    ∑ j, (c0 + c1 * x j + c2 * x j ^ 2 + c3 * x j ^ 3 + c4 * x j ^ 4) =
      c0 * n + c1 * (∑ j, x j) + c2 * (∑ j, x j ^ 2) + c3 * (∑ j, x j ^ 3) +
        c4 * (∑ j, x j ^ 4) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma L1 {n : ℕ} (x : Fin n → ℂ) (u : ℂ) :
    ∑ j, (1 + u * x j) = n + u * (∑ j, x j) := by
  have := msum x 1 u 0 0 0
  simp only [zero_mul, add_zero, one_mul] at this
  rw [← this]

lemma L2 {n : ℕ} (x : Fin n → ℂ) (u v : ℂ) :
    ∑ j, (1 + u * x j) * (1 + v * x j) =
      n + (u + v) * (∑ j, x j) + u * v * (∑ j, x j ^ 2) := by
  rw [Finset.sum_congr rfl (fun j _ => show (1 + u * x j) * (1 + v * x j) =
    1 + (u + v) * x j + u * v * x j ^ 2 + 0 * x j ^ 3 + 0 * x j ^ 4 by ring), msum]
  ring

lemma L3 {n : ℕ} (x : Fin n → ℂ) (u v w : ℂ) :
    ∑ j, (1 + u * x j) * ((1 + v * x j) * (1 + w * x j)) =
      n + (u + v + w) * (∑ j, x j) + (u * v + u * w + v * w) * (∑ j, x j ^ 2) +
        u * v * w * (∑ j, x j ^ 3) := by
  rw [Finset.sum_congr rfl (fun j _ => show (1 + u * x j) * ((1 + v * x j) * (1 + w * x j)) =
    1 + (u + v + w) * x j + (u * v + u * w + v * w) * x j ^ 2 + u * v * w * x j ^ 3 +
      0 * x j ^ 4 by ring), msum]
  ring

lemma L4 {n : ℕ} (x : Fin n → ℂ) (u v w z : ℂ) :
    ∑ j, (1 + u * x j) * ((1 + v * x j) * ((1 + w * x j) * (1 + z * x j))) =
      n + (u + v + w + z) * (∑ j, x j) +
        (u * v + u * w + u * z + v * w + v * z + w * z) * (∑ j, x j ^ 2) +
        (u * v * w + u * v * z + u * w * z + v * w * z) * (∑ j, x j ^ 3) +
        u * v * w * z * (∑ j, x j ^ 4) := by
  rw [Finset.sum_congr rfl (fun j _ => show
    (1 + u * x j) * ((1 + v * x j) * ((1 + w * x j) * (1 + z * x j))) =
    1 + (u + v + w + z) * x j + (u * v + u * w + u * z + v * w + v * z + w * z) * x j ^ 2 +
      (u * v * w + u * v * z + u * w * z + v * w * z) * x j ^ 3 + u * v * w * z * x j ^ 4
      by ring), msum]
  ring

def E2 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 * a 2 + a 1 * a 3 + a 2 * a 3
def E3 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 * a 2 + a 0 * a 1 * a 3 + a 0 * a 2 * a 3 + a 1 * a 2 * a 3
def E4 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 * a 2 * a 3

lemma F_closed (n : ℕ) (a : Fin 4 → ℂ) (x : Fin n → ℂ) (hx : ∑ j, x j = 0) :
    ∑ f : Fin 4 ↪ Fin n, ∏ i, (1 + a i * x (f i)) =
      (n : ℂ) * (n - 1) * (n - 2) * (n - 3) - E2 a * ((n - 2) * (n - 3)) * (∑ j, x j ^ 2) +
        2 * E3 a * (n - 3) * (∑ j, x j ^ 3) +
        E4 a * (3 * (∑ j, x j ^ 2) ^ 2 - 6 * (∑ j, x j ^ 4)) := by
  change D n 4 (fun k j => 1 + a k * x j) = _
  simp [D_succ, D_zero, Fin.sum_univ_succ, Fin.tail, Function.update_apply]
  simp only [mul_assoc, L1, L2, L3, L4, hx, E2, E3, E4]
  ring

lemma iso_core {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0) :
    Module.finrank ℂ K + Module.finrank ℂ K ≤ Module.finrank ℂ W +
      Module.finrank ℂ (LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K)) := by
  set T := W.subtype.dualMap ∘ₗ β.domRestrict K with hT
  set K' : Submodule ℂ W := K.comap W.subtype with hK'
  have hK'r : Module.finrank ℂ K' = Module.finrank ℂ K :=
    (Submodule.comapSubtypeEquivOfLe hKW).finrank_eq
  have hrange : LinearMap.range T ≤ K'.dualAnnihilator := by
    rintro φ ⟨y, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    simp only [hT, LinearMap.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
      LinearMap.domRestrict_apply]
    exact hiso y y.2 w hw
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq K'
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  have h3 := Submodule.finrank_mono hrange
  omega

lemma iso_bound0 {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0)
    (hrad : ∀ y ∈ K, (∀ z ∈ W, β y z = 0) → y = 0) :
    2 * Module.finrank ℂ K ≤ Module.finrank ℂ W := by
  have h := iso_core W K hKW β hiso
  have : LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have : (y : Fin n → ℂ) = 0 := by
      apply hrad y y.2
      intro z hz
      have := LinearMap.congr_fun hy ⟨z, hz⟩
      simpa using this
    exact Subtype.ext this
  rw [this, finrank_bot] at h
  omega

lemma iso_bound1 {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0) (ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hrad : ∀ y ∈ K, (∀ z ∈ W, β y z = 0) → ψ y = 0 → y = 0) :
    2 * Module.finrank ℂ K ≤ Module.finrank ℂ W + 1 := by
  have h := iso_core W K hKW β hiso
  set R := LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K)
  set L : R →ₗ[ℂ] ℂ := ψ ∘ₗ K.subtype ∘ₗ R.subtype with hL
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hy0 : ((y : K) : Fin n → ℂ) = 0 := by
      apply hrad _ (y : K).2
      · intro z hz
        have := LinearMap.congr_fun (LinearMap.mem_ker.mp y.2) ⟨z, hz⟩
        rw [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.domRestrict_apply] at this
        simpa using this
      · simpa [hL] using hy
    exact Subtype.ext (Subtype.ext hy0)
  have h4 := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (V := R) L
  rw [hker, finrank_bot] at h4
  have h5 := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_self] at h5
  omega

lemma generic {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) {ι : Type} (s : Finset ι)
    (g : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ m ∈ s, ∃ x ∈ K, MvPolynomial.eval x (g m) ≠ 0) :
    ∃ x ∈ K, ∀ m ∈ s, MvPolynomial.eval x (g m) ≠ 0 := by
  set b := Module.finBasis ℂ K
  set k := Module.finrank ℂ K
  let v : Fin n → MvPolynomial (Fin k) ℂ :=
    fun i => ∑ l, MvPolynomial.C ((b l : Fin n → ℂ) i) * MvPolynomial.X l
  let pt : (Fin k → ℂ) → (Fin n → ℂ) := fun c => ∑ l, c l • (b l : Fin n → ℂ)
  have hpt : ∀ c, pt c ∈ K := fun c =>
    Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (b l).2)
  have key : ∀ (c : Fin k → ℂ) (p : MvPolynomial (Fin n) ℂ),
      MvPolynomial.eval c (MvPolynomial.aeval v p) = MvPolynomial.eval (pt c) p := by
    intro c p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]
      congr 1
      simp [v, pt, Finset.sum_apply, mul_comm]
  have hne : ∀ m ∈ s, MvPolynomial.aeval v (g m) ≠ 0 := by
    intro m hm hz
    obtain ⟨x, hx, hxne⟩ := h m hm
    have hxe : pt (b.repr ⟨x, hx⟩) = x := by
      have h1 := b.sum_repr ⟨x, hx⟩
      calc pt (b.repr ⟨x, hx⟩) = ((∑ l, b.repr ⟨x, hx⟩ l • b l : K) : Fin n → ℂ) := by
            simp only [pt, Submodule.coe_sum, Submodule.coe_smul]
        _ = x := by rw [h1]
    apply hxne
    rw [← hxe, ← key, hz, map_zero]
  have hP : ∏ m ∈ s, MvPolynomial.aeval v (g m) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c (∏ m ∈ s, MvPolynomial.aeval v (g m)) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hP (MvPolynomial.funext (fun c => by simpa using hall c))
  refine ⟨pt c, hpt c, fun m hm => ?_⟩
  rw [map_prod] at hc
  rw [← key]
  exact (Finset.prod_ne_zero_iff.mp hc) m hm

def pw {n : ℕ} (r : ℕ) (x : Fin n → ℂ) : ℂ := ∑ j, x j ^ r

lemma N_closed (n : ℕ) :
    ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ) = (n : ℂ) * (n - 1) * (n - 2) * (n - 3) := by
  have := F_closed n 0 0 (by simp)
  simpa [E2, E3, E4] using this

lemma pw_smul {n : ℕ} (r : ℕ) (t : ℂ) (x : Fin n → ℂ) : pw r (t • x) = t ^ r * pw r x := by
  simp [pw, Finset.mul_sum, mul_pow]

lemma coeffs {n : ℕ} (hn : 4 ≤ n) (a : Fin 4 → ℂ) (x : Fin n → ℂ)
    (hx : ∀ t : ℂ, ∑ j, (t • x) j = 0 ∧
      ∑ f : Fin 4 ↪ Fin n, ∏ i, (1 + a i * (t • x) (f i)) = ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)) :
    E2 a * pw 2 x = 0 ∧ E3 a * pw 3 x = 0 ∧ E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) = 0 := by
  have key : ∀ t : ℂ, -(E2 a * (((n : ℂ) - 2) * ((n : ℂ) - 3)) * pw 2 x) * t ^ 2 +
      2 * E3 a * ((n : ℂ) - 3) * pw 3 x * t ^ 3 +
      E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) * t ^ 4 = 0 := by
    intro t
    obtain ⟨h1, h2⟩ := hx t
    rw [F_closed n a _ h1, N_closed] at h2
    have e2 := pw_smul 2 t x
    have e3 := pw_smul 3 t x
    have e4 := pw_smul 4 t x
    simp only [pw] at e2 e3 e4
    rw [e2, e3, e4] at h2
    simp only [pw]
    linear_combination h2
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key 2
  have hn2 : (n : ℂ) - 2 ≠ 0 := by
    intro h
    have : (n : ℂ) = 2 := by linear_combination h
    norm_cast at this; omega
  have hn3 : (n : ℂ) - 3 ≠ 0 := by
    intro h
    have : (n : ℂ) = 3 := by linear_combination h
    norm_cast at this; omega
  refine ⟨?_, ?_, ?_⟩
  · have hA : (E2 a * pw 2 x) * (((n : ℂ) - 2) * ((n : ℂ) - 3)) = 0 := by
      linear_combination -(k1 + k2 / 3 - k3 / 12)
    exact (mul_eq_zero.mp hA).resolve_right (mul_ne_zero hn2 hn3)
  · have hB : (E3 a * pw 3 x) * (2 * ((n : ℂ) - 3)) = 0 := by
      linear_combination (k1 - k2) / 2
    exact (mul_eq_zero.mp hB).resolve_right (mul_ne_zero two_ne_zero hn3)
  · linear_combination -k1 / 2 + k2 / 6 + k3 / 12

lemma some_E (a : Fin 4 → ℂ) (ha : a ≠ 0) (hs : ∑ i, a i = 0) :
    E2 a ≠ 0 ∨ E3 a ≠ 0 ∨ E4 a ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h2, h3, h4⟩ := h
  simp only [E2, E3, E4] at h2 h3 h4
  rw [Fin.sum_univ_four] at hs
  apply ha
  have z0 : a 0 ^ 4 = 0 := by
    linear_combination (a 0) ^ 3 * hs - (a 0) ^ 2 * h2 + (a 0) * h3 - h4
  have z1 : a 1 ^ 4 = 0 := by
    linear_combination (a 1) ^ 3 * hs - (a 1) ^ 2 * h2 + (a 1) * h3 - h4
  have z2 : a 2 ^ 4 = 0 := by
    linear_combination (a 2) ^ 3 * hs - (a 2) ^ 2 * h2 + (a 2) * h3 - h4
  have z3 : a 3 ^ 4 = 0 := by
    linear_combination (a 3) ^ 3 * hs - (a 3) ^ 2 * h2 + (a 3) * h3 - h4
  funext i
  fin_cases i
  · exact pow_eq_zero_iff (by norm_num) |>.mp z0
  · exact pow_eq_zero_iff (by norm_num) |>.mp z1
  · exact pow_eq_zero_iff (by norm_num) |>.mp z2
  · exact pow_eq_zero_iff (by norm_num) |>.mp z3

def Bf {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun y z => ∑ j, w j * y j * z j + κ * (∑ j, u j * y j) * (∑ j, u j * z j))
    (fun m₁ m₂ z => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring)
    (fun c m z => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ∑ j, w j * (c * m j) * z j = c * ∑ j, w j * m j * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ j, u j * (c * m j) = c * ∑ j, u j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2]; ring)
    (fun y n₁ n₂ => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring)
    (fun c y m => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ∑ j, w j * y j * (c * m j) = c * ∑ j, w j * y j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ j, u j * (c * m j) = c * ∑ j, u j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2]; ring)

lemma Bf_apply {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) (y z : Fin n → ℂ) :
    Bf w u κ y z = ∑ j, w j * y j * z j + κ * (∑ j, u j * y j) * (∑ j, u j * z j) := rfl

lemma Bf_single {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) (y : Fin n → ℂ) (i : Fin n) :
    Bf w u κ y (Pi.single i 1) = w i * y i + κ * (∑ j, u j * y j) * u i := by
  rw [Bf_apply]
  simp [Pi.single_apply]

lemma p2_add {n : ℕ} (x y : Fin n → ℂ) :
    pw 2 (x + y) = pw 2 x + 2 * (∑ j, x j * y j) + pw 2 y := by
  simp only [pw, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma p2_sub {n : ℕ} (x y : Fin n → ℂ) :
    pw 2 (x - y) = pw 2 x - 2 * (∑ j, x j * y j) + pw 2 y := by
  simp only [pw, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def sumL (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ j, z j
  map_add' y z := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum]

lemma finrank_sumL_ker {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank ℂ (LinearMap.ker (sumL n)) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumL n)
  have hr : LinearMap.range (sumL n) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single ⟨0, by omega⟩ c, ?_⟩
    simp [sumL]
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

lemma case2 {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) (hq : ∀ x ∈ K, pw 2 x = 0) :
    2 * Module.finrank ℂ K ≤ n := by
  have h := iso_bound0 ⊤ K le_top (Bf (fun _ => 1) 0 0)
    (fun y hy z hz => by
      have e := p2_add y z
      rw [hq _ (K.add_mem hy hz), hq y hy, hq z hz] at e
      rw [Bf_apply]
      simp only [one_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      linear_combination -e / 2)
    (fun y _ hy => by
      funext i
      have := hy (Pi.single i 1) trivial
      rw [Bf_single] at this
      simpa using this)
  rwa [finrank_top, Module.finrank_fin_fun] at h

lemma case3 {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) (hq : ∀ x ∈ K, pw 3 x = 0) :
    2 * Module.finrank ℂ K ≤ n := by
  classical
  obtain ⟨x, hxK, hx⟩ := generic K (univ.filter (fun j => ∃ u ∈ K, u j ≠ 0))
    (fun j => MvPolynomial.X j) (fun j hj => by simpa using (Finset.mem_filter.mp hj).2)
  have hx' : ∀ j, (∃ u ∈ K, u j ≠ 0) → x j ≠ 0 := fun j hj => by
    simpa using hx j (Finset.mem_filter.mpr ⟨mem_univ _, hj⟩)
  have h := iso_bound0 ⊤ K le_top (Bf x 0 0)
    (fun y hy z hz => by
      have pol : 6 * ∑ j, x j * y j * z j = pw 3 (x + y + z) - pw 3 (x + y) - pw 3 (x + z)
          - pw 3 (y + z) + pw 3 x + pw 3 y + pw 3 z := by
        simp only [pw, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [hq _ (K.add_mem (K.add_mem hxK hy) hz), hq _ (K.add_mem hxK hy),
        hq _ (K.add_mem hxK hz), hq _ (K.add_mem hy hz), hq x hxK, hq y hy, hq z hz] at pol
      rw [Bf_apply]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      linear_combination pol / 6)
    (fun y hyK hy => by
      funext i
      have := hy (Pi.single i 1) trivial
      rw [Bf_single] at this
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at this
      by_contra hyi
      have h' : x i = 0 ∨ y i = 0 := by simpa using this
      exact hx' i ⟨y, hyK, hyi⟩ (h'.resolve_right hyi))
  rwa [finrank_top, Module.finrank_fin_fun] at h

lemma case4 {n : ℕ} (hn : 4 ≤ n) (K : Submodule ℂ (Fin n → ℂ))
    (hK0 : ∀ x ∈ K, ∑ j, x j = 0) (hq : ∀ x ∈ K, pw 2 x ^ 2 = 2 * pw 4 x) :
    2 * Module.finrank ℂ K ≤ n := by
  classical

  let g : Bool × Fin n → MvPolynomial (Fin n) ℂ := fun m =>
    cond m.1 ((∑ i, MvPolynomial.X i ^ 2) - MvPolynomial.C 6 * MvPolynomial.X m.2 ^ 2)
      (MvPolynomial.X m.2)
  obtain ⟨x, hxK, hx⟩ := generic K (univ.filter (fun m => ∃ u ∈ K, MvPolynomial.eval u (g m) ≠ 0))
    g (fun m hm => (Finset.mem_filter.mp hm).2)
  have G0 : ∀ j, (∃ u ∈ K, u j ≠ 0) → x j ≠ 0 := fun j ⟨u, hu, huj⟩ => by
    have := hx (false, j) (Finset.mem_filter.mpr ⟨mem_univ _, ⟨u, hu, by simpa [g] using huj⟩⟩)
    simpa [g] using this
  have G1 : ∀ j, (∃ u ∈ K, pw 2 u - 6 * u j ^ 2 ≠ 0) → pw 2 x - 6 * x j ^ 2 ≠ 0 :=
    fun j ⟨u, hu, huj⟩ => by
      have := hx (true, j) (Finset.mem_filter.mpr ⟨mem_univ _, ⟨u, hu, by simpa [g, pw] using huj⟩⟩)
      simpa [g, pw] using this
  set P := pw 2 x with hP
  set d : Fin n → ℂ := fun j => P - 6 * x j ^ 2 with hd

  have quad : ∀ w ∈ K, 4 * (∑ j, x j * w j) ^ 2 + 2 * P * pw 2 w
      - 12 * ∑ j, x j ^ 2 * w j ^ 2 = 0 := by
    intro w hw
    have h1 := hq _ (K.add_mem hxK hw)
    have h2 := hq _ (K.sub_mem hxK hw)
    have h3 := hq x hxK
    have h4 := hq w hw
    rw [p2_add] at h1
    rw [p2_sub] at h2
    have e4 : pw 4 (x + w) + pw 4 (x - w) = 2 * pw 4 x + 12 * (∑ j, x j ^ 2 * w j ^ 2)
        + 2 * pw 4 w := by
      simp only [pw, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    linear_combination (h1 + h2) / 2 - h3 - h4 + e4

  have hiso : ∀ y ∈ K, ∀ z ∈ K, Bf d x 2 y z = 0 := by
    intro y hy z hz
    have q1 := quad _ (K.add_mem hy hz)
    have q2 := quad y hy
    have q3 := quad z hz
    rw [p2_add] at q1
    have ex : ∑ j, x j * (y + z) j = (∑ j, x j * y j) + ∑ j, x j * z j := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have es : ∑ j, x j ^ 2 * (y + z) j ^ 2 = (∑ j, x j ^ 2 * y j ^ 2) +
        2 * (∑ j, x j ^ 2 * y j * z j) + ∑ j, x j ^ 2 * z j ^ 2 := by
      simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have ed : ∑ j, d j * y j * z j = P * (∑ j, y j * z j) - 6 * ∑ j, x j ^ 2 * y j * z j := by
      simp only [hd, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [ex, es] at q1
    rw [Bf_apply, ed]
    linear_combination (q1 - q2 - q3) / 4

  have L0 : ∀ y ∈ K, (∀ j, d j * y j = 0) → ∑ j, x j * y j = 0 → y = 0 := by
    intro y hy hdy hxy
    funext j
    by_cases hj : d j = 0
    · by_cases ha : ∃ u ∈ K, u j ≠ 0
      · have hx0 := G0 j ha
        have hz : ∀ u ∈ K, pw 2 u - 6 * u j ^ 2 = 0 := by
          intro u hu
          by_contra hne
          exact G1 j ⟨u, hu, hne⟩ hj
        have e1 := hz _ (K.add_mem hxK hy)
        have e2 := hz x hxK
        have e3 := hz y hy
        rw [p2_add] at e1
        simp only [Pi.add_apply] at e1
        have : x j * y j = 0 := by
          linear_combination (-(e1 - e2 - e3) + 2 * hxy) / 12
        simpa [hx0] using this
      · push Not at ha
        exact ha y hy
    · exact (mul_eq_zero.mp (hdy j)).resolve_left hj

  set W := LinearMap.ker (sumL n) with hW
  have hKW : K ≤ W := fun y hy => by simpa [hW, sumL] using hK0 y hy
  have hsingle : ∀ i j : Fin n, Pi.single i (1 : ℂ) - Pi.single j 1 ∈ W := by
    intro i j
    simp [hW, sumL, Finset.sum_sub_distrib]
  have hv : ∀ y : Fin n → ℂ, (∀ z ∈ W, Bf d x 2 y z = 0) → ∀ i j : Fin n,
      d i * y i + 2 * (∑ l, x l * y l) * x i = d j * y j + 2 * (∑ l, x l * y l) * x j := by
    intro y hy i j
    have := hy _ (hsingle i j)
    rw [map_sub, Bf_single, Bf_single] at this
    linear_combination this
  have hW1 : Module.finrank ℂ W = n - 1 := finrank_sumL_ker (by omega)

  suffices H : ∃ ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ,
      ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) → ψ y = 0 → y = 0 by
    obtain ⟨ψ, hψ⟩ := H
    have := iso_bound1 W K hKW (Bf d x 2) hiso ψ hψ
    omega
  let cL : (Fin n → ℂ) →ₗ[ℂ] ℂ := (Bf x 0 0).flip (fun _ => 1)
  have hcL : ∀ y, cL y = ∑ l, x l * y l := by
    intro y
    simp [cL, Bf_apply]
  by_cases hA : ∃ i1, d i1 = 0
  · obtain ⟨i1, hi1⟩ := hA
    refine ⟨cL, fun y hyK hy hc => ?_⟩
    rw [hcL] at hc
    apply L0 y hyK _ hc
    intro j
    have := hv y hy j i1
    rw [hi1, hc] at this
    linear_combination this
  · push Not at hA
    set i0 : Fin n := ⟨0, by omega⟩
    set A := ∑ i, 1 / d i
    set Bc := ∑ i, x i / d i
    set C := ∑ i, x i ^ 2 / d i
    have hId : P * A - 6 * C = n := by
      have : ∑ i, d i / d i = n := by
        rw [Finset.sum_congr rfl (fun i _ => div_self (hA i))]
        simp
      rw [← this]
      simp only [A, C, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        have := hA i; field_simp; simp only [hd])

    have rel : ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) →
        (∀ i, y i = (Bf d x 2 y (Pi.single i0 1) - 2 * (∑ l, x l * y l) * x i) / d i) ∧
        (∑ l, x l * y l) * (1 + 2 * C) = Bf d x 2 y (Pi.single i0 1) * Bc ∧
        Bf d x 2 y (Pi.single i0 1) * A = 2 * (∑ l, x l * y l) * Bc := by
      intro y hyK hy
      set c := ∑ l, x l * y l with hc
      set μ := Bf d x 2 y (Pi.single i0 1) with hμ
      have hμ' : μ = d i0 * y i0 + 2 * c * x i0 := by rw [hμ, Bf_single]
      have yform : ∀ i, y i = (μ - 2 * c * x i) / d i := by
        intro i
        rw [eq_div_iff (hA i)]
        have := hv y hy i i0
        rw [hμ']
        linear_combination this
      refine ⟨yform, ?_, ?_⟩
      · have : (∑ l, x l * y l) = μ * Bc - 2 * c * C := by
          conv_lhs => rw [Finset.sum_congr rfl (fun i _ => by rw [yform i])]
          simp only [Bc, C, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by
            have := hA i; field_simp)
        linear_combination this
      · have hs := hK0 y hyK
        have : ∑ i, y i = μ * A - 2 * c * Bc := by
          conv_lhs => rw [Finset.sum_congr rfl (fun i _ => by rw [yform i])]
          simp only [A, Bc, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by
            have := hA i; field_simp)
        linear_combination hs - this
    have finish : ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) → ∑ l, x l * y l = 0 →
        Bf d x 2 y (Pi.single i0 1) = 0 → y = 0 := by
      intro y hyK hy hc hμ
      apply L0 y hyK _ hc
      intro j
      have := hv y hy j i0
      rw [Bf_single] at hμ
      rw [hc] at this hμ
      linear_combination this + hμ
    by_cases hBC : Bc ≠ 0 ∨ 1 + 2 * C ≠ 0
    · refine ⟨(Bf d x 2).flip (Pi.single i0 1), fun y hyK hy hμ => ?_⟩
      rw [LinearMap.flip_apply] at hμ
      obtain ⟨-, r1, r2⟩ := rel y hyK hy
      rw [hμ] at r1 r2
      apply finish y hyK hy _ hμ
      rcases hBC with hb | hb
      · have : 2 * (∑ l, x l * y l) * Bc = 0 := by linear_combination -r2
        have := (mul_eq_zero.mp this).resolve_right hb
        simpa using this
      · have : (∑ l, x l * y l) * (1 + 2 * C) = 0 := by linear_combination r1
        exact (mul_eq_zero.mp this).resolve_right hb
    · simp only [not_or, not_not] at hBC
      obtain ⟨hb, hcc⟩ := hBC
      refine ⟨cL, fun y hyK hy hc => ?_⟩
      rw [hcL] at hc
      obtain ⟨-, -, r2⟩ := rel y hyK hy
      rw [hc] at r2
      apply finish y hyK hy hc
      by_cases hA0 : A = 0
      · exfalso
        rw [hA0] at hId
        have h3 : (n : ℂ) = 3 := by linear_combination -hId - 3 * hcc
        norm_cast at h3
        omega
      · have : Bf d x 2 y (Pi.single i0 1) * A = 0 := by linear_combination r2
        exact (mul_eq_zero.mp this).resolve_right hA0

def pv (k : ℕ) (c : Fin k → ℂ) (m : ℕ) : ℂ :=
  if h : m < k then c ⟨m, h⟩ else if h2 : m < 2 * k then -c ⟨m - k, by omega⟩ else 0

lemma pv_sum (k n r : ℕ) (hkn : 2 * k ≤ n) (c : Fin k → ℂ) (hr : ∀ u : ℂ, u ^ r + (-u) ^ r = 0)
    (hr0 : (0 : ℂ) ^ r = 0) :
    ∑ m ∈ range n, pv k c m ^ r = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = k + (k + t) := ⟨n - 2 * k, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∀ m ∈ range k, pv k c m ^ r = (if h : m < k then c ⟨m, h⟩ else 0) ^ r := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    simp [pv, hm']
  have e2 : ∀ m ∈ range k, pv k c (k + m) ^ r = (-(if h : m < k then c ⟨m, h⟩ else 0)) ^ r := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    have : ¬ (k + m < k) := by omega
    have h2 : k + m < 2 * k := by omega
    simp [pv, this, h2, hm']
  have e3 : ∀ m ∈ range t, pv k c (k + (k + m)) ^ r = 0 := by
    intro m _
    have : ¬ (k + (k + m) < k) := by omega
    have h2 : ¬ (k + (k + m) < 2 * k) := by omega
    simp [pv, this, h2, hr0]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3,
    Finset.sum_const_zero, add_zero, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun m _ => hr _)

def pvL (k n : ℕ) : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun c := fun j => pv k c j.val
  map_add' c₁ c₂ := by
    funext j
    simp only [pv, Pi.add_apply]
    split_ifs <;> ring
  map_smul' t c := by
    funext j
    simp only [pv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem main : (∀ (n k : ℕ), 4 ≤ n →
  ((∃ (a : Fin 4 → ℂ) (K : Submodule ℂ (Fin n → ℂ)),
      a ≠ 0 ∧ (∑ i, a i) = 0 ∧ Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧
        (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + a i * x (f i))) =
          (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) ↔
    2 * k ≤ n)) := by
  intro n k hn
  constructor
  · rintro ⟨a, K, ha, hsa, hk, hK⟩
    subst hk
    have hK0 : ∀ x ∈ K, ∑ j, x j = 0 := fun x hx => (hK x hx).1
    have hco : ∀ x ∈ K, E2 a * pw 2 x = 0 ∧ E3 a * pw 3 x = 0 ∧
        E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) = 0 :=
      fun x hx => coeffs hn a x (fun t => hK _ (K.smul_mem t hx))
    rcases some_E a ha hsa with h2 | h3 | h4
    · exact case2 K (fun x hx => (mul_eq_zero.mp (hco x hx).1).resolve_left h2)
    · exact case3 K (fun x hx => (mul_eq_zero.mp (hco x hx).2.1).resolve_left h3)
    · refine case4 hn K hK0 (fun x hx => ?_)
      have := (mul_eq_zero.mp (hco x hx).2.2).resolve_left h4
      linear_combination this / 3
  · intro hkn
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (n := 2) (by norm_num)
    set ω : ℂ := (-1 + s) / 2 with hωd
    have hω : ω ^ 2 + ω + 1 = 0 := by rw [hωd]; linear_combination hs / 4
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    have hinj : Function.Injective (pvL k n) := by
      intro c₁ c₂ h
      funext m
      have := congrFun h ⟨m, by omega⟩
      simpa [pvL, pv] using this
    refine ⟨![0, 1, ω, ω ^ 2], LinearMap.range (pvL k n), ?_, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
    · simp only [Fin.sum_univ_four]
      simp
      linear_combination hω
    · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
    · rintro x ⟨c, rfl⟩
      have hsum : ∑ j, pvL k n c j = 0 := by
        have := pv_sum k n 1 hkn c (fun u => by ring) (by ring)
        simp only [pow_one] at this
        rw [← this, ← Fin.sum_univ_eq_sum_range (fun m => pv k c m) n]
        rfl
      have hcube : ∑ j, pvL k n c j ^ 3 = 0 := by
        have := pv_sum k n 3 hkn c (fun u => by ring) (by ring)
        rw [← this, ← Fin.sum_univ_eq_sum_range (fun m => pv k c m ^ 3) n]
        rfl
      refine ⟨hsum, ?_⟩
      rw [F_closed n _ _ hsum, N_closed, hcube]
      have hE2 : E2 ![0, 1, ω, ω ^ 2] = 0 := by
        simp [E2]
        linear_combination hω + hω3
      have hE4 : E4 ![0, 1, ω, ω ^ 2] = 0 := by simp [E4]
      rw [hE2, hE4]
      ring

end PEqualNP.Outside.L_gct_312

theorem PEqualNP.Outside.L_gct_312 : (∀ (n k : ℕ), 4 ≤ n →
  ((∃ (a : Fin 4 → ℂ) (K : Submodule ℂ (Fin n → ℂ)),
      a ≠ 0 ∧ (∑ i, a i) = 0 ∧ Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧
        (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + a i * x (f i))) =
          (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) ↔
    2 * k ≤ n)) :=
  PEqualNP.Outside.L_gct_312.main
