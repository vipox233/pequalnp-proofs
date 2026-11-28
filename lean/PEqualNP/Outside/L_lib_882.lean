import Mathlib
import PEqualNP.Defs

open Finset Polynomial

namespace PEqualNP.Outside.L_lib_882

def sg (b : Bool) : ℤ := if b = true then -1 else 1

lemma wt_eq {n : ℕ} (x : Fin n → Bool) (p0 p1 : ℤ) :
    p1 ^ (univ.filter (fun h : Fin n => x h = true)).card *
      p0 ^ (n - (univ.filter (fun h : Fin n => x h = true)).card) =
    ∏ h : Fin n, (if x h = true then p1 else p0) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun h => x h = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (univ.filter (fun h : Fin n => ¬ x h = true)).card =
      n - (univ.filter (fun h : Fin n => x h = true)).card := by omega
  rw [h2]

lemma sum_prod_bool {n : ℕ} (F : Fin n → Bool → ℤ) :
    ∑ x : Fin n → Bool, ∏ h, F h (x h) = ∏ h, (F h true + F h false) := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool)) F
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_congr rfl fun i _ => Fintype.sum_bool _

lemma fiber_prod {n m : ℕ} (r : Fin n → Fin m) (φ : Fin m → ℤ) :
    ∏ h : Fin n, φ (r h) =
      ∏ i : Fin m, φ i ^ (univ.filter (fun h : Fin n => r h = i)).card := by
  rw [← Finset.prod_fiberwise' univ r φ]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_const _

lemma sc {n m : ℕ} (r : Fin n → Fin m) (T : Finset (Fin m)) (p0 p1 : ℤ) :
    ∑ x : Fin n → Bool, (∏ h, (if x h = true then p1 else p0)) *
        ∏ i ∈ T, ∏ h, (if r h = i ∧ x h = true then (-1 : ℤ) else 1) =
      (∏ i ∈ T, (p0 - p1) ^ (univ.filter (fun h : Fin n => r h = i)).card) *
        ∏ i ∈ univ \ T, (p0 + p1) ^ (univ.filter (fun h : Fin n => r h = i)).card := by
  have key : ∀ x : Fin n → Bool, (∏ h, (if x h = true then p1 else p0)) *
        ∏ i ∈ T, ∏ h, (if r h = i ∧ x h = true then (-1 : ℤ) else 1) =
      ∏ h, (fun (h : Fin n) (b : Bool) => (if b = true then p1 else p0) *
        (if r h ∈ T ∧ b = true then (-1 : ℤ) else 1)) h (x h) := by
    intro x
    rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun h _ => ?_
    by_cases hx : x h = true
    · simp only [hx, and_true]
      rw [Finset.prod_ite_eq]
    · simp [hx]
  rw [Finset.sum_congr rfl fun x _ => key x, sum_prod_bool (fun (h : Fin n) (b : Bool) =>
    (if b = true then p1 else p0) * (if r h ∈ T ∧ b = true then (-1 : ℤ) else 1))]
  have h2 : ∀ h : Fin n, ((fun (h : Fin n) (b : Bool) => (if b = true then p1 else p0) *
        (if r h ∈ T ∧ b = true then (-1 : ℤ) else 1)) h true +
      (fun (h : Fin n) (b : Bool) => (if b = true then p1 else p0) *
        (if r h ∈ T ∧ b = true then (-1 : ℤ) else 1)) h false) =
      (fun i => if i ∈ T then p0 - p1 else p0 + p1) (r h) := by
    intro h
    by_cases hT : r h ∈ T <;> simp [hT] <;> ring
  rw [Finset.prod_congr rfl fun h _ => h2 h,
    fiber_prod r (fun i => if i ∈ T then p0 - p1 else p0 + p1),
    ← Finset.prod_sdiff (Finset.subset_univ T), mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hi]
  · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.mp hi).2]

lemma par (c : ℕ) (s : Bool) :
    (1 + sg s * (-1 : ℤ) ^ c) = if c % 2 = s.toNat then 2 else 0 := by
  rcases Nat.even_or_odd c with hc | hc
  · have h2 : c % 2 = 0 := Nat.even_iff.mp hc
    cases s <;> simp [sg, hc.neg_one_pow, h2]
  · have h2 : c % 2 = 1 := Nat.odd_iff.mp hc
    cases s <;> simp [sg, hc.neg_one_pow, h2]

lemma neg_one_pow_card {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (-1 : ℤ) ^ (univ.filter p).card = ∏ h : Fin n, (if p h then (-1 : ℤ) else 1) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

abbrev Valid {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (x : (Fin A → Bool) × (Fin B → Bool)) : Prop :=
  ∀ i : Fin m,
    ((univ.filter (fun h : Fin A => red h = i ∧ x.1 h = true)).card +
      (univ.filter (fun h : Fin B => blue h = i ∧ x.2 h = true)).card) % 2 = (s i).toNat

abbrev wt1 {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : ℕ :=
  (univ.filter (fun h : Fin A => x.1 h = true)).card

abbrev wt2 {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : ℕ :=
  (univ.filter (fun h : Fin B => x.2 h = true)).card

theorem ci {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (p0 p1 q0 q1 : ℤ) :
    (2 : ℤ) ^ m * ∑ x : (Fin A → Bool) × (Fin B → Bool),
      (if Valid red blue s x then
        p1 ^ wt1 x * p0 ^ (A - wt1 x) * (q1 ^ wt2 x * q0 ^ (B - wt2 x)) else 0) =
    ∏ i : Fin m,
      ((p0 + p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 + q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card +
        sg (s i) * ((p0 - p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 - q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card)) := by
  have hR : ∏ i : Fin m,
      ((p0 + p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 + q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card +
        sg (s i) * ((p0 - p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 - q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card)) =
      ∑ T ∈ (univ : Finset (Fin m)).powerset,
        (∏ i ∈ T, sg (s i) * ((p0 - p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 - q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card)) *
        ∏ i ∈ univ \ T, ((p0 + p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 + q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card) := by
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun i _ => add_comm _ _
  have hx : ∀ x : (Fin A → Bool) × (Fin B → Bool),
      (2 : ℤ) ^ m * (if Valid red blue s x then
        p1 ^ wt1 x * p0 ^ (A - wt1 x) * (q1 ^ wt2 x * q0 ^ (B - wt2 x)) else 0) =
      ∑ T ∈ (univ : Finset (Fin m)).powerset, (∏ i ∈ T, sg (s i)) *
        (((∏ h, (if x.1 h = true then p1 else p0)) *
          ∏ i ∈ T, ∏ h, (if red h = i ∧ x.1 h = true then (-1 : ℤ) else 1)) *
        ((∏ h, (if x.2 h = true then q1 else q0)) *
          ∏ i ∈ T, ∏ h, (if blue h = i ∧ x.2 h = true then (-1 : ℤ) else 1))) := by
    intro x
    have h1 : (if Valid red blue s x then (2 : ℤ) ^ m else 0) =
        ∏ i : Fin m, (1 + sg (s i) *
          ((∏ h, (if red h = i ∧ x.1 h = true then (-1 : ℤ) else 1)) *
            ∏ h, (if blue h = i ∧ x.2 h = true then (-1 : ℤ) else 1))) := by
      have h3 : ∀ i : Fin m, (1 + sg (s i) *
          ((∏ h, (if red h = i ∧ x.1 h = true then (-1 : ℤ) else 1)) *
            ∏ h, (if blue h = i ∧ x.2 h = true then (-1 : ℤ) else 1))) =
          if ((univ.filter (fun h : Fin A => red h = i ∧ x.1 h = true)).card +
            (univ.filter (fun h : Fin B => blue h = i ∧ x.2 h = true)).card) % 2 = (s i).toNat
          then (2 : ℤ) else 0 := by
        intro i
        rw [← neg_one_pow_card, ← neg_one_pow_card, ← pow_add, par]
      rw [Finset.prod_congr rfl fun i _ => h3 i, Finset.prod_ite_zero]
      simp [Finset.prod_const]
    rw [wt_eq, wt_eq]
    have h4 : (2 : ℤ) ^ m * (if Valid red blue s x then
        (∏ h, (if x.1 h = true then p1 else p0)) * (∏ h, (if x.2 h = true then q1 else q0))
          else 0) =
        ((∏ h, (if x.1 h = true then p1 else p0)) * (∏ h, (if x.2 h = true then q1 else q0))) *
          (if Valid red blue s x then (2 : ℤ) ^ m else 0) := by
      split_ifs <;> ring
    rw [h4, h1, Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hR, Finset.mul_sum, Finset.sum_congr rfl fun x _ => hx x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  dsimp only
  have hsplit := Finset.sum_mul_sum (univ : Finset (Fin A → Bool)) (univ : Finset (Fin B → Bool))
    (fun x => (∏ h, (if x h = true then p1 else p0)) *
      ∏ i ∈ T, ∏ h, (if red h = i ∧ x h = true then (-1 : ℤ) else 1))
    (fun y => (∏ h, (if y h = true then q1 else q0)) *
      ∏ i ∈ T, ∏ h, (if blue h = i ∧ y h = true then (-1 : ℤ) else 1))
  rw [← hsplit, sc, sc]
  simp only [Finset.prod_mul_distrib]
  ring

def Cg (n : ℕ) (c : ℤ) (p : ℤ[X]) : Prop := (X : ℤ[X]) ^ (n + 1) ∣ p - 1 - C c * X ^ n

lemma Cg_mul {n : ℕ} (hn : 1 ≤ n) {c c' : ℤ} {p q : ℤ[X]} (hp : Cg n c p) (hq : Cg n c' q) :
    Cg n (c + c') (p * q) := by
  unfold Cg at *
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hp' : p = 1 + C c * X ^ (k + 1) + X ^ (k + 1 + 1) * u := by linear_combination hu
  have hq' : q = 1 + C c' * X ^ (k + 1) + X ^ (k + 1 + 1) * v := by linear_combination hv
  refine ⟨u * q + (1 + C c * X ^ (k + 1)) * v + C c * C c' * X ^ k, ?_⟩
  rw [C_add, hp', hq']
  ring

lemma Cg_one (n : ℕ) : Cg n 0 1 := by
  unfold Cg
  simp

lemma Cg_pow {n : ℕ} (hn : 1 ≤ n) {c : ℤ} {p : ℤ[X]} (hp : Cg n c p) (k : ℕ) :
    Cg n (k * c) (p ^ k) := by
  induction k with
  | zero => simpa using Cg_one n
  | succ k ih =>
    have h := Cg_mul hn ih hp
    rw [pow_succ]
    have e : ((k + 1 : ℕ) : ℤ) * c = (k : ℤ) * c + c := by push_cast; ring
    rw [e]
    exact h

lemma Cg_base (n : ℕ) : Cg n (-1) (1 - X ^ n) := by
  unfold Cg
  have e : (1 - X ^ n - 1 - C (-1 : ℤ) * X ^ n : ℤ[X]) = 0 := by
    rw [C_neg, C_1]; ring
  rw [e]
  exact dvd_zero _

lemma Cg_high {n e : ℕ} (h : n < e) : Cg n 0 (1 - X ^ e) := by
  unfold Cg
  refine ⟨-X ^ (e - (n + 1)), ?_⟩
  have he : e = (n + 1) + (e - (n + 1)) := by omega
  rw [C_0, zero_mul, sub_zero]
  conv_lhs => rw [he]
  rw [pow_add]
  ring

lemma Cg_prod {ι : Type*} (s : Finset ι) {n : ℕ} (hn : 1 ≤ n) (f : ι → ℤ[X])
    (h : ∀ i ∈ s, Cg n 0 (f i)) : Cg n 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cg_one n
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := Cg_mul hn (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

lemma Cg_unique {n : ℕ} {c c' : ℤ} {p : ℤ[X]} (h : Cg n c p) (h' : Cg n c' p) : c = c' := by
  unfold Cg at *
  have hd := dvd_sub h h'
  have e : (p - 1 - C c * X ^ n) - (p - 1 - C c' * X ^ n) = C (c' - c) * X ^ n := by
    rw [C_sub]; ring
  rw [e, Polynomial.X_pow_dvd_iff] at hd
  have h0 := hd n (by omega)
  rw [coeff_C_mul_X_pow] at h0
  simp at h0
  omega

theorem uniq {κ : Type*} [DecidableEq κ] (K : Finset κ) (e : κ → ℕ) (he : ∀ k ∈ K, 1 ≤ e k)
    (hinj : ∀ k ∈ K, ∀ k' ∈ K, e k = e k' → k = k') (α β : κ → ℕ)
    (h : ∏ k ∈ K, (1 - (X : ℤ[X]) ^ e k) ^ α k = ∏ k ∈ K, (1 - (X : ℤ[X]) ^ e k) ^ β k) :
    ∀ k ∈ K, α k = β k := by
  suffices H : ∀ n, ∀ k ∈ K, e k = n → α k = β k from fun k hk => H (e k) k hk rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k0 hk0 hek
    have hset : K.filter (fun k => ¬ e k < n) = insert k0 (K.filter (fun k => n < e k)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hk, hlt⟩
        by_cases hkn : e k = n
        · left; exact hinj k hk k0 hk0 (hkn.trans hek.symm)
        · right; exact ⟨hk, by omega⟩
      · rintro (rfl | ⟨hk, hlt⟩)
        · exact ⟨hk0, by omega⟩
        · exact ⟨hk, by omega⟩
    have hnot : k0 ∉ K.filter (fun k => n < e k) := by
      simp only [Finset.mem_filter, not_and]
      intro _
      omega
    have hsplit : ∀ γ : κ → ℕ, ∏ k ∈ K, (1 - (X : ℤ[X]) ^ e k) ^ γ k =
        (∏ k ∈ K.filter (fun k => e k < n), (1 - (X : ℤ[X]) ^ e k) ^ γ k) *
        ((1 - (X : ℤ[X]) ^ n) ^ γ k0 *
          ∏ k ∈ K.filter (fun k => n < e k), (1 - (X : ℤ[X]) ^ e k) ^ γ k) := by
      intro γ
      rw [← Finset.prod_filter_mul_prod_filter_not K (fun k => e k < n), hset,
        Finset.prod_insert hnot, hek]
    have hL : ∏ k ∈ K.filter (fun k => e k < n), (1 - (X : ℤ[X]) ^ e k) ^ α k =
        ∏ k ∈ K.filter (fun k => e k < n), (1 - (X : ℤ[X]) ^ e k) ^ β k :=
      Finset.prod_congr rfl fun k hk => by
        rw [ih (e k) (Finset.mem_filter.mp hk).2 k (Finset.mem_filter.mp hk).1 rfl]
    have hL0 : ∏ k ∈ K.filter (fun k => e k < n), (1 - (X : ℤ[X]) ^ e k) ^ β k ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ ?_
      intro h0
      have h1 := congrArg (fun p : ℤ[X] => p.coeff 0) h0
      have h2 := he k (Finset.mem_filter.mp hk).1
      have h3 : (0 : ℕ) ≠ e k := by omega
      simp [coeff_X_pow, h3] at h1
    rw [hsplit α, hsplit β, hL] at h
    have h' := mul_left_cancel₀ hL0 h
    have hn : 1 ≤ n := hek ▸ he k0 hk0
    have cg : ∀ γ : κ → ℕ, Cg n ((γ k0 : ℤ) * (-1) + 0) ((1 - (X : ℤ[X]) ^ n) ^ γ k0 *
        ∏ k ∈ K.filter (fun k => n < e k), (1 - (X : ℤ[X]) ^ e k) ^ γ k) := fun γ =>
      Cg_mul hn (Cg_pow hn (Cg_base n) _) (Cg_prod _ hn _ fun k hk => by
        have h4 := Cg_pow hn (Cg_high (Finset.mem_filter.mp hk).2) (γ k)
        simpa using h4)
    have ca := cg α
    rw [h'] at ca
    have h5 := Cg_unique ca (cg β)
    omega

lemma fib_key {m : ℕ} {R : Type*} [CommRing R] (S : Finset (Fin m)) (key : Fin m → ℕ × ℕ)
    (K : Finset (ℕ × ℕ)) (hK : ∀ i ∈ S, key i ∈ K) (D : ℕ × ℕ → R) :
    ∏ k ∈ K, D k ^ (S.filter (fun i => key i = k)).card = ∏ i ∈ S, D (key i) := by
  rw [← Finset.prod_fiberwise_of_maps_to' hK D]
  exact Finset.prod_congr rfl fun k _ => (Finset.prod_const _).symm

theorem eo {m : ℕ} {R : Type*} [CommRing R] (a b : Fin m → ℕ) (s : Fin m → Bool)
    (K : Finset (ℕ × ℕ))
    (hK : ∀ i : Fin m, ∀ c : ℕ, c = 1 ∨ c = 2 → (c * a i, c * b i) ∈ K)
    (Pm Nm : ℕ → ℕ → R) (hP : ∀ u v, Pm (2 * u) (2 * v) = Pm u v ^ 2)
    (hN : ∀ u v, Nm (2 * u) (2 * v) = Nm u v ^ 2) :
    (∏ i : Fin m, (Pm (a i) (b i) + (if s i = true then -1 else 1) * Nm (a i) (b i))) *
      ∏ k ∈ K, (Pm k.1 k.2 - Nm k.1 k.2) ^
        (univ.filter (fun i : Fin m => s i = false ∧ 1 * a i = k.1 ∧ 1 * b i = k.2)).card =
    ∏ k ∈ K, (Pm k.1 k.2 - Nm k.1 k.2) ^
        ((univ.filter (fun i : Fin m => s i = true ∧ 1 * a i = k.1 ∧ 1 * b i = k.2)).card +
          (univ.filter (fun i : Fin m => s i = false ∧ 2 * a i = k.1 ∧ 2 * b i = k.2)).card) := by
  have hh : ∀ (par : Bool) (c : ℕ), c = 1 ∨ c = 2 →
      ∏ k ∈ K, (Pm k.1 k.2 - Nm k.1 k.2) ^
        (univ.filter (fun i : Fin m => s i = par ∧ c * a i = k.1 ∧ c * b i = k.2)).card =
      ∏ i : Fin m, (if s i = par then (Pm (c * a i) (c * b i) - Nm (c * a i) (c * b i))
        else 1) := by
    intro par c hc
    rw [← Finset.prod_filter,
      ← fib_key (univ.filter (fun i : Fin m => s i = par)) (fun i => (c * a i, c * b i)) K
        (fun i _ => hK i c hc) (fun k => Pm k.1 k.2 - Nm k.1 k.2)]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 2
    ext i
    simp [Finset.mem_filter, Prod.ext_iff]
  simp only [pow_add]
  rw [Finset.prod_mul_distrib, hh false 1 (Or.inl rfl), hh true 1 (Or.inl rfl),
    hh false 2 (Or.inr rfl), ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hs : s i <;> simp [hP, hN] <;> ring

lemma ex1 (n : ℕ) (c : ℕ → ℤ)
    (h : ∀ x : ℤ, 2 ≤ x → ∑ u ∈ range (n + 1), c u * x ^ (n - u) = 0) :
    ∀ u ≤ n, c u = 0 := by
  have hp : (∑ u ∈ range (n + 1), C (c u) * X ^ (n - u) : ℤ[X]) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.Ici (2 : ℤ))
    · intro x hx
      simp only [IsRoot.def, eval_finsetSum, eval_mul, eval_C, eval_pow,
        eval_X]
      exact h x hx
    · exact Set.Ici_infinite 2
  intro u hu
  have h1 := congrArg (fun q : ℤ[X] => q.coeff (n - u)) hp
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single u] at h1
  · simpa using h1
  · intro u' hu' hne
    have h2 : n - u ≠ n - u' := by
      have := Finset.mem_range.mp hu'
      omega
    simp [h2]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

lemma ex2 (A B : ℕ) (c : ℕ → ℕ → ℤ)
    (h : ∀ x y : ℤ, 2 ≤ x → 2 ≤ y →
      ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), c u v * (x ^ (A - u) * y ^ (B - v)) = 0) :
    ∀ u ≤ A, ∀ v ≤ B, c u v = 0 := by
  intro u hu v hv
  refine ex1 B (c u) (fun y hy => ?_) v hv
  refine ex1 A (fun u => ∑ v ∈ range (B + 1), c u v * y ^ (B - v)) (fun x hx => ?_) u hu
  rw [← h x y hx hy]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma dpos (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y) (u v : ℕ) (huv : (u, v) ≠ (0, 0)) :
    (x + 1) ^ u * (y + 1) ^ v - (x - 1) ^ u * (y - 1) ^ v ≠ 0 := by
  have hx0 : (0 : ℤ) ≤ x - 1 := by linarith
  have hy0 : (0 : ℤ) ≤ y - 1 := by linarith
  have hxl : x - 1 < x + 1 := by linarith
  have hyl : y - 1 < y + 1 := by linarith
  have h1 : (x - 1) ^ u ≤ (x + 1) ^ u := pow_le_pow_left₀ hx0 hxl.le u
  have h2 : (y - 1) ^ v ≤ (y + 1) ^ v := pow_le_pow_left₀ hy0 hyl.le v
  have hlt : (x - 1) ^ u * (y - 1) ^ v < (x + 1) ^ u * (y + 1) ^ v := by
    by_cases hu : u = 0
    · have hv : v ≠ 0 := by
        intro hv
        exact huv (by rw [hu, hv])
      subst hu
      simpa using pow_lt_pow_left₀ hyl hy0 hv
    · have h3 : (x - 1) ^ u < (x + 1) ^ u := pow_lt_pow_left₀ hxl hx0 hu
      have h4 : (0 : ℤ) < (y + 1) ^ v := by positivity
      have h5 : (0 : ℤ) ≤ (x - 1) ^ u := by positivity
      calc (x - 1) ^ u * (y - 1) ^ v ≤ (x - 1) ^ u * (y + 1) ^ v :=
            mul_le_mul_of_nonneg_left h2 h5
        _ < (x + 1) ^ u * (y + 1) ^ v := mul_lt_mul_of_pos_right h3 h4
  intro h0
  linarith

lemma fiber_sum {n m : ℕ} (r : Fin n → Fin m) :
    ∑ i : Fin m, (univ.filter (fun h : Fin n => r h = i)).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := r) (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin m))) (fun _ _ => Finset.mem_univ _)
  simpa using h.symm

lemma kron {N u v u' v' : ℕ} (hu : u < N) (hu' : u' < N) (h : u + N * v = u' + N * v') :
    u = u' ∧ v = v' := by
  have h1 : (u + N * v) % N = u := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hu
  have h2 : (u' + N * v') % N = u' := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hu'
  have h3 : u = u' := by rw [← h1, ← h2, h]
  subst h3
  have h4 : N * v = N * v' := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) h4⟩

abbrev fc {n m : ℕ} (r : Fin n → Fin m) (i : Fin m) : ℕ :=
  (univ.filter (fun h : Fin n => r h = i)).card

abbrev cnt {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (u v : ℕ) : ℕ :=
  (univ.filter (fun x : (Fin A → Bool) × (Fin B → Bool) =>
    wt1 x = u ∧ wt2 x = v ∧ Valid red blue s x)).card

abbrev hit {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (par : Bool) (c u v : ℕ) : ℕ :=
  (univ.filter (fun i : Fin m => s i = par ∧ c * fc red i = u ∧ c * fc blue i = v)).card

abbrev KK (A B : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2 * A + 1)) ×ˢ (range (2 * B + 1))).erase (0, 0)

lemma fc_le {n m : ℕ} (r : Fin n → Fin m) (i : Fin m) : fc r i ≤ n := by
  have h := Finset.card_filter_le (univ : Finset (Fin n)) (fun h => r h = i)
  simpa using h

lemma wt1_le {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : wt1 x ≤ A := by
  have h := Finset.card_filter_le (univ : Finset (Fin A)) (fun h => x.1 h = true)
  simpa using h

lemma wt2_le {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : wt2 x ≤ B := by
  have h := Finset.card_filter_le (univ : Finset (Fin B)) (fun h => x.2 h = true)
  simpa using h

lemma fib {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (φ : ℕ → ℕ → ℤ) :
    ∑ x : (Fin A → Bool) × (Fin B → Bool),
      (if Valid red blue s x then φ (wt1 x) (wt2 x) else 0) =
    ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red blue s u v : ℤ) * φ u v := by
  have h1 : ∀ u v : ℕ, (cnt red blue s u v : ℤ) * φ u v =
      ∑ x : (Fin A → Bool) × (Fin B → Bool),
        (if wt1 x = u ∧ wt2 x = v ∧ Valid red blue s x then φ u v else 0) := by
    intro u v
    rw [Finset.natCast_card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have h2 : ∀ x : (Fin A → Bool) × (Fin B → Bool),
      (if Valid red blue s x then φ (wt1 x) (wt2 x) else 0) =
      ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1),
        (if wt1 x = u ∧ wt2 x = v ∧ Valid red blue s x then φ u v else 0) := by
    intro x
    rw [Finset.sum_eq_single (wt1 x), Finset.sum_eq_single (wt2 x)]
    · simp
    · intro v _ hv
      split_ifs with hc
      · exact absurd hc.2.1.symm hv
      · rfl
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (wt2_le x))) hn
    · intro u _ hu
      refine Finset.sum_eq_zero fun v _ => ?_
      split_ifs with hc
      · exact absurd hc.1.symm hu
      · rfl
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (wt1_le x))) hn
  rw [Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => (h1 u v).symm

lemma sideG {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (N : ℕ) (t : ℤ) :
    (2 : ℤ) ^ m * ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red blue s u v : ℤ) *
        ((1 - t) ^ u * (1 + t) ^ (A - u) * ((1 - t ^ N) ^ v * (1 + t ^ N) ^ (B - v))) =
    2 ^ (A + B) * ∏ i : Fin m, (1 + sg (s i) * t ^ (fc red i + N * fc blue i)) := by
  have h1 := fib red blue s
    (fun u v => (1 - t) ^ u * (1 + t) ^ (A - u) * ((1 - t ^ N) ^ v * (1 + t ^ N) ^ (B - v)))
  have h2 := ci red blue s (1 + t) (1 - t) (1 + t ^ N) (1 - t ^ N)
  rw [← h1, h2]
  have hf : ∀ i : Fin m,
      ((1 + t + (1 - t)) ^ fc red i * (1 + t ^ N + (1 - t ^ N)) ^ fc blue i +
        sg (s i) * ((1 + t - (1 - t)) ^ fc red i * (1 + t ^ N - (1 - t ^ N)) ^ fc blue i)) =
      2 ^ (fc red i + fc blue i) * (1 + sg (s i) * t ^ (fc red i + N * fc blue i)) := by
    intro i
    ring
  rw [Finset.prod_congr rfl fun i _ => hf i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, fiber_sum, fiber_sum]

lemma sideH {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (x y : ℤ) :
    (2 : ℤ) ^ m * ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red blue s u v : ℤ) *
        (x ^ (A - u) * y ^ (B - v)) =
    ∏ i : Fin m, ((x + 1) ^ fc red i * (y + 1) ^ fc blue i +
      (if s i = true then -1 else 1) * ((x - 1) ^ fc red i * (y - 1) ^ fc blue i)) := by
  have h1 := fib red blue s (fun u v => x ^ (A - u) * y ^ (B - v))
  have h2 := ci red blue s x 1 y 1
  simp only [one_pow, one_mul] at h2
  rw [← h1, h2]
  rfl

lemma hKmem {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m)
    (hpos : ∀ i, 0 < fc red i + fc blue i) :
    ∀ i : Fin m, ∀ c : ℕ, c = 1 ∨ c = 2 → (c * fc red i, c * fc blue i) ∈ KK A B := by
  intro i c hc
  have h1 := fc_le red i
  have h2 := fc_le blue i
  have h3 := hpos i
  simp only [KK, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq, Prod.mk.injEq]
  rcases hc with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> omega

lemma hit_zero {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (hpos : ∀ i, 0 < fc red i + fc blue i) (par : Bool) (c : ℕ) (hc : c = 1 ∨ c = 2)
    (u v : ℕ) (huv : (u, v) ∉ KK A B) : hit red blue s par c u v = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro i _ ⟨_, h1, h2⟩
  apply huv
  rw [← h1, ← h2]
  exact hKmem red blue hpos i c hc

lemma scale_sum (A B : ℕ) (c0 c1 : ℕ → ℕ → ℕ) (f0 f1 : ℕ)
    (H : ∀ u v, 2 ^ f0 * c0 u v = 2 ^ f1 * c1 u v) (φ : ℕ → ℕ → ℤ) :
    (2 : ℤ) ^ f0 * ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (c0 u v : ℤ) * φ u v =
    2 ^ f1 * ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (c1 u v : ℤ) * φ u v := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h' : (2 : ℤ) ^ f0 * (c0 u v : ℤ) = 2 ^ f1 * (c1 u v : ℤ) := by exact_mod_cast H u v
  rw [← mul_assoc, ← mul_assoc, h']

lemma gzero {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) (N : ℕ) (hN : 1 ≤ N)
    (hp : ∀ i, 0 < a i + b i) :
    ∏ i : Fin m, (1 + sg (s i) * (0 : ℤ) ^ (a i + N * b i)) = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have h1 : a i + N * b i ≠ 0 := by
    have h2 := hp i
    rcases Nat.eq_zero_or_pos (b i) with h | h
    · omega
    · have h3 : 0 < N * b i := Nat.mul_pos (by omega) h
      omega
  rw [zero_pow h1, mul_zero, add_zero]

lemma peval {m : ℕ} (e : Fin m → ℕ) (s : Fin m → Bool) (t : ℤ) :
    Polynomial.eval t (∏ i : Fin m,
      ((1 : ℤ[X]) + (if s i = true then -1 else 1) * X ^ (e i))) =
    ∏ i : Fin m, (1 + sg (s i) * t ^ (e i)) := by
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold sg
  split_ifs <;> simp

lemma cancel_core {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (K : Finset ι) (D : ι → R)
    (P0 P1 : R) (hE0 hO0 hE1 hO1 : ι → ℕ)
    (E0 : P0 * ∏ k ∈ K, D k ^ hE0 k = ∏ k ∈ K, D k ^ hO0 k)
    (E1 : P1 * ∏ k ∈ K, D k ^ hE1 k = ∏ k ∈ K, D k ^ hO1 k) :
    (P0 = P1 → ∏ k ∈ K, D k ^ (hO0 k + hE1 k) = ∏ k ∈ K, D k ^ (hO1 k + hE0 k)) ∧
    ((∀ k ∈ K, D k ≠ 0) → (∀ k ∈ K, hO0 k + hE1 k = hO1 k + hE0 k) → P0 = P1) := by
  have s0 : ∀ γ δ : ι → ℕ, ∏ k ∈ K, D k ^ (γ k + δ k) =
      (∏ k ∈ K, D k ^ γ k) * ∏ k ∈ K, D k ^ δ k := fun γ δ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pow_add _ _ _
  constructor
  · intro hP
    rw [s0, s0, ← E0, ← E1, hP]
    ring
  · intro hD hk
    have hne : (∏ k ∈ K, D k ^ hE0 k) * ∏ k ∈ K, D k ^ hE1 k ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hD k hk))
        (Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hD k hk))
    apply mul_right_cancel₀ hne
    have h1 : ∏ k ∈ K, D k ^ (hO0 k + hE1 k) = ∏ k ∈ K, D k ^ (hO1 k + hE0 k) :=
      Finset.prod_congr rfl fun k hk' => by rw [hk k hk']
    rw [s0, s0, ← E0, ← E1] at h1
    linear_combination h1

theorem fwd (A B m0 m1 f0 f1 : ℕ) (red0 : Fin A → Fin m0) (blue0 : Fin B → Fin m0)
    (s0 : Fin m0 → Bool) (red1 : Fin A → Fin m1) (blue1 : Fin B → Fin m1) (s1 : Fin m1 → Bool)
    (hpos0 : ∀ i, 0 < fc red0 i + fc blue0 i) (hpos1 : ∀ i, 0 < fc red1 i + fc blue1 i)
    (H : ∀ u v, 2 ^ f0 * cnt red0 blue0 s0 u v = 2 ^ f1 * cnt red1 blue1 s1 u v) :
    f0 + m1 = f1 + m0 ∧ ∀ k ∈ KK A B,
      (hit red0 blue0 s0 true 1 k.1 k.2 + hit red0 blue0 s0 false 2 k.1 k.2) +
          hit red1 blue1 s1 false 1 k.1 k.2 =
        (hit red1 blue1 s1 true 1 k.1 k.2 + hit red1 blue1 s1 false 2 k.1 k.2) +
          hit red0 blue0 s0 false 1 k.1 k.2 := by
  have hEval : ∀ t : ℤ,
      (2 : ℤ) ^ (f0 + m1) *
          ∏ i : Fin m0, (1 + sg (s0 i) * t ^ (fc red0 i + (2 * A + 1) * fc blue0 i)) =
        2 ^ (f1 + m0) *
          ∏ i : Fin m1, (1 + sg (s1 i) * t ^ (fc red1 i + (2 * A + 1) * fc blue1 i)) := by
    intro t
    have e1 := sideG red0 blue0 s0 (2 * A + 1) t
    have e2 := sideG red1 blue1 s1 (2 * A + 1) t
    have e3 := scale_sum A B (cnt red0 blue0 s0) (cnt red1 blue1 s1) f0 f1 H
      (fun u v => (1 - t) ^ u * (1 + t) ^ (A - u) *
        ((1 - t ^ (2 * A + 1)) ^ v * (1 + t ^ (2 * A + 1)) ^ (B - v)))
    have h2 : (2 : ℤ) ^ (A + B) ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    linear_combination (-(2 ^ f0 * 2 ^ m1)) * e1 + (2 ^ f1 * 2 ^ m0) * e2 +
      (2 ^ m1 * 2 ^ m0) * e3
  have hf : f0 + m1 = f1 + m0 := by
    have h0 := hEval 0
    rw [gzero (fun i => fc red0 i) (fun i => fc blue0 i) s0 (2 * A + 1) (by omega) hpos0,
      gzero (fun i => fc red1 i) (fun i => fc blue1 i) s1 (2 * A + 1) (by omega) hpos1,
      mul_one, mul_one] at h0
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h0)
  refine ⟨hf, ?_⟩
  have hP : (∏ i : Fin m0, ((1 : ℤ[X]) + (if s0 i = true then -1 else 1) *
        X ^ (fc red0 i + (2 * A + 1) * fc blue0 i))) =
      ∏ i : Fin m1, ((1 : ℤ[X]) + (if s1 i = true then -1 else 1) *
        X ^ (fc red1 i + (2 * A + 1) * fc blue1 i)) := by
    apply Polynomial.funext
    intro t
    rw [peval (fun i => fc red0 i + (2 * A + 1) * fc blue0 i),
      peval (fun i => fc red1 i + (2 * A + 1) * fc blue1 i)]
    have h1 := hEval t
    rw [hf] at h1
    exact mul_left_cancel₀ (by positivity) h1
  have E0 := eo (R := ℤ[X]) (fun i => fc red0 i) (fun i => fc blue0 i) s0 (KK A B)
    (hKmem red0 blue0 hpos0) (fun _ _ => 1) (fun u v => X ^ (u + (2 * A + 1) * v))
    (by intro u v; simp) (by intro u v; ring)
  have E1 := eo (R := ℤ[X]) (fun i => fc red1 i) (fun i => fc blue1 i) s1 (KK A B)
    (hKmem red1 blue1 hpos1) (fun _ _ => 1) (fun u v => X ^ (u + (2 * A + 1) * v))
    (by intro u v; simp) (by intro u v; ring)
  have hprod := (cancel_core (KK A B)
    (fun k : ℕ × ℕ => (1 : ℤ[X]) - X ^ (k.1 + (2 * A + 1) * k.2)) _ _
    (fun k => hit red0 blue0 s0 false 1 k.1 k.2)
    (fun k => hit red0 blue0 s0 true 1 k.1 k.2 + hit red0 blue0 s0 false 2 k.1 k.2)
    (fun k => hit red1 blue1 s1 false 1 k.1 k.2)
    (fun k => hit red1 blue1 s1 true 1 k.1 k.2 + hit red1 blue1 s1 false 2 k.1 k.2)
    E0 E1).1 hP
  refine uniq (KK A B) (fun k => k.1 + (2 * A + 1) * k.2) ?_ ?_ _ _ hprod
  · rintro ⟨u, v⟩ hk
    simp only [KK, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq,
      Prod.mk.injEq] at hk
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h
      omega
    · have h3 : 0 < (2 * A + 1) * v := Nat.mul_pos (by omega) h
      show 1 ≤ u + (2 * A + 1) * v
      omega
  · rintro ⟨u, v⟩ hk ⟨u', v'⟩ hk' h
    simp only [KK, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq,
      Prod.mk.injEq] at hk hk'
    obtain ⟨h1, h2⟩ := kron (N := 2 * A + 1) (by omega) (by omega) h
    exact Prod.ext h1 h2

theorem bwd (A B m0 m1 f0 f1 : ℕ) (red0 : Fin A → Fin m0) (blue0 : Fin B → Fin m0)
    (s0 : Fin m0 → Bool) (red1 : Fin A → Fin m1) (blue1 : Fin B → Fin m1) (s1 : Fin m1 → Bool)
    (hpos0 : ∀ i, 0 < fc red0 i + fc blue0 i) (hpos1 : ∀ i, 0 < fc red1 i + fc blue1 i)
    (hf : f0 + m1 = f1 + m0)
    (hk : ∀ k ∈ KK A B,
      (hit red0 blue0 s0 true 1 k.1 k.2 + hit red0 blue0 s0 false 2 k.1 k.2) +
          hit red1 blue1 s1 false 1 k.1 k.2 =
        (hit red1 blue1 s1 true 1 k.1 k.2 + hit red1 blue1 s1 false 2 k.1 k.2) +
          hit red0 blue0 s0 false 1 k.1 k.2) :
    ∀ u v, 2 ^ f0 * cnt red0 blue0 s0 u v = 2 ^ f1 * cnt red1 blue1 s1 u v := by
  have hbig : ∀ u v : ℕ, ¬ (u ≤ A ∧ v ≤ B) → ∀ (m : ℕ) (red : Fin A → Fin m)
      (blue : Fin B → Fin m) (s : Fin m → Bool), cnt red blue s u v = 0 := by
    intro u v huv m red blue s
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ ⟨h1, h2, _⟩
    have h3 := wt1_le x
    have h4 := wt2_le x
    omega
  have key := ex2 A B (fun u v => (2 : ℤ) ^ f0 * (cnt red0 blue0 s0 u v : ℤ) -
      2 ^ f1 * (cnt red1 blue1 s1 u v : ℤ)) (by
    intro x y hx hy
    have e0 := sideH red0 blue0 s0 x y
    have e1 := sideH red1 blue1 s1 x y
    have E0 := eo (R := ℤ) (fun i => fc red0 i) (fun i => fc blue0 i) s0 (KK A B)
      (hKmem red0 blue0 hpos0) (fun u v => (x + 1) ^ u * (y + 1) ^ v)
      (fun u v => (x - 1) ^ u * (y - 1) ^ v) (by intro u v; ring) (by intro u v; ring)
    have E1 := eo (R := ℤ) (fun i => fc red1 i) (fun i => fc blue1 i) s1 (KK A B)
      (hKmem red1 blue1 hpos1) (fun u v => (x + 1) ^ u * (y + 1) ^ v)
      (fun u v => (x - 1) ^ u * (y - 1) ^ v) (by intro u v; ring) (by intro u v; ring)
    have hPi := (cancel_core (KK A B)
      (fun k : ℕ × ℕ => (x + 1) ^ k.1 * (y + 1) ^ k.2 - (x - 1) ^ k.1 * (y - 1) ^ k.2) _ _
      (fun k => hit red0 blue0 s0 false 1 k.1 k.2)
      (fun k => hit red0 blue0 s0 true 1 k.1 k.2 + hit red0 blue0 s0 false 2 k.1 k.2)
      (fun k => hit red1 blue1 s1 false 1 k.1 k.2)
      (fun k => hit red1 blue1 s1 true 1 k.1 k.2 + hit red1 blue1 s1 false 2 k.1 k.2)
      E0 E1).2 (by
        rintro ⟨u, v⟩ hk'
        simp only [KK, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq] at hk'
        exact dpos x y hx hy u v hk'.1) hk
    have epow : (2 : ℤ) ^ f0 * 2 ^ m1 = 2 ^ f1 * 2 ^ m0 := by
      rw [← pow_add, ← pow_add, hf]
    have h2 : (2 : ℤ) ^ m0 * 2 ^ m1 ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    rw [mul_zero]
    have hsum : ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1),
        ((2 : ℤ) ^ f0 * (cnt red0 blue0 s0 u v : ℤ) - 2 ^ f1 * (cnt red1 blue1 s1 u v : ℤ)) *
          (x ^ (A - u) * y ^ (B - v)) =
        2 ^ f0 * (∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red0 blue0 s0 u v : ℤ) *
          (x ^ (A - u) * y ^ (B - v))) -
        2 ^ f1 * (∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red1 blue1 s1 u v : ℤ) *
          (x ^ (A - u) * y ^ (B - v))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsum]
    linear_combination (2 ^ m1 * 2 ^ f0) * e0 - (2 ^ m0 * 2 ^ f1) * e1 +
      (2 ^ m1 * 2 ^ f0) * hPi +
      (∏ i : Fin m1, ((x + 1) ^ fc red1 i * (y + 1) ^ fc blue1 i +
        (if s1 i = true then -1 else 1) * ((x - 1) ^ fc red1 i * (y - 1) ^ fc blue1 i))) * epow)
  intro u v
  by_cases huv : u ≤ A ∧ v ≤ B
  · have h1 := key u huv.1 v huv.2
    have h2 : ((2 ^ f0 * cnt red0 blue0 s0 u v : ℕ) : ℤ) =
        ((2 ^ f1 * cnt red1 blue1 s1 u v : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · rw [hbig u v huv, hbig u v huv]
    simp

theorem main (A B : ℕ) (m f : Bool → ℕ)
    (red : (j : Bool) → Fin A → Fin (m j)) (blue : (j : Bool) → Fin B → Fin (m j))
    (s : (j : Bool) → Fin (m j) → Bool)
    (hpos : ∀ j i, 0 < fc (red j) i + fc (blue j) i) :
    (∀ u v, 2 ^ (f false) * cnt (red false) (blue false) (s false) u v =
        2 ^ (f true) * cnt (red true) (blue true) (s true) u v) ↔
      f false + m true = f true + m false ∧
      ∀ u v,
        ((hit (red false) (blue false) (s false) true 1 u v +
            hit (red false) (blue false) (s false) false 2 u v : ℕ) : ℤ) -
          (hit (red false) (blue false) (s false) false 1 u v : ℤ) =
        ((hit (red true) (blue true) (s true) true 1 u v +
            hit (red true) (blue true) (s true) false 2 u v : ℕ) : ℤ) -
          (hit (red true) (blue true) (s true) false 1 u v : ℤ) := by
  constructor
  · intro H
    obtain ⟨hf, hk⟩ := fwd A B (m false) (m true) (f false) (f true) (red false) (blue false)
      (s false) (red true) (blue true) (s true) (hpos false) (hpos true) H
    refine ⟨hf, fun u v => ?_⟩
    by_cases huv : (u, v) ∈ KK A B
    · have h1 := hk (u, v) huv
      simp only at h1
      omega
    · rw [hit_zero (red false) (blue false) (s false) (hpos false) true 1 (Or.inl rfl) u v huv,
        hit_zero (red false) (blue false) (s false) (hpos false) false 2 (Or.inr rfl) u v huv,
        hit_zero (red false) (blue false) (s false) (hpos false) false 1 (Or.inl rfl) u v huv,
        hit_zero (red true) (blue true) (s true) (hpos true) true 1 (Or.inl rfl) u v huv,
        hit_zero (red true) (blue true) (s true) (hpos true) false 2 (Or.inr rfl) u v huv,
        hit_zero (red true) (blue true) (s true) (hpos true) false 1 (Or.inl rfl) u v huv]
  · rintro ⟨hf, hs⟩
    refine bwd A B (m false) (m true) (f false) (f true) (red false) (blue false)
      (s false) (red true) (blue true) (s true) (hpos false) (hpos true) hf fun k _ => ?_
    have h1 := hs k.1 k.2
    omega

end PEqualNP.Outside.L_lib_882

theorem PEqualNP.Outside.L_lib_882 : (∀ (A B : ℕ) (m f : Bool → ℕ)
  (red : (j : Bool) → Fin A → Fin (m j)) (blue : (j : Bool) → Fin B → Fin (m j))
  (s : (j : Bool) → Fin (m j) → Bool),
  let a := fun (j : Bool) (i : Fin (m j)) =>
    (Finset.univ.filter (fun h : Fin A => red j h = i)).card
  let b := fun (j : Bool) (i : Fin (m j)) =>
    (Finset.univ.filter (fun h : Fin B => blue j h = i)).card
  (∀ j i, 0 < a j i + b j i) →
  let hits := fun (j parity : Bool) (k u v : ℕ) =>
    (Finset.univ.filter (fun i : Fin (m j) =>
      s j i = parity ∧ k*a j i = u ∧ k*b j i = v)).card
  let sig := fun (j : Bool) (u v : ℕ) =>
    ((hits j true 1 u v + hits j false 2 u v : ℕ) : ℤ) - (hits j false 1 u v : ℤ)
  let X := (Fin A → Bool) × (Fin B → Bool)
  let hist := fun (j : Bool) (u v : ℕ) =>
    2^(f j) * ((Finset.univ : Finset X).filter (fun x =>
      (Finset.univ.filter (fun h : Fin A => x.1 h = true)).card = u ∧
      (Finset.univ.filter (fun h : Fin B => x.2 h = true)).card = v ∧
      ∀ i : Fin (m j),
        ((Finset.univ.filter (fun h : Fin A => red j h = i ∧ x.1 h = true)).card +
         (Finset.univ.filter (fun h : Fin B => blue j h = i ∧ x.2 h = true)).card) % 2 =
        (s j i).toNat)).card
  (∀ u v, hist false u v = hist true u v) ↔
    f false + m true = f true + m false ∧ ∀ u v, sig false u v = sig true u v) := by
  intro A B m f red blue s
  exact PEqualNP.Outside.L_lib_882.main A B m f red blue s
