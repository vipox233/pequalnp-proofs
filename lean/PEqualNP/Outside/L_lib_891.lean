import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_891

open Finset

abbrev Ix (m : ℕ) := Option (Fin m) × Bool

def Quad {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ (s : ZMod 2) (h : Fin n → ZMod 2) (M : Fin n → Fin n → ZMod 2),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j

def Aff {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ (s : ZMod 2) (h : Fin n → ZMod 2), ∀ x, q x = s + dotProduct h x

def lin {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (k : Ix m)
    (x : Fin n → ZMod 2) : ZMod 2 :=
  a k + dotProduct (A k) x

def PP {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (i : Fin m)
    (x : Fin n → ZMod 2) : ZMod 2 :=
  lin A a (some i, false) x * lin A a (some i, true) x

def HH {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (x : Fin n → ZMod 2) : ZMod 2 :=
  (lin A a (none, false) x + ∑ i, u i * PP A a i x) *
    (lin A a (none, true) x + ∑ i, v i * PP A a i x)

theorem two : (2 : ZMod 2) = 0 := rfl
theorem sq_self (z : ZMod 2) : z * z = z := by revert z; decide
theorem eq_of_add (a b : ZMod 2) (h : a + b = 0) : a = b := by revert a b; decide
theorem one_of_ne (a : ZMod 2) (h : a ≠ 0) : a = 1 := by revert a; decide

theorem lin_add {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (k : Ix m)
    (x d : Fin n → ZMod 2) : lin A a k (x + d) = lin A a k x + dotProduct (A k) d := by
  unfold lin; rw [dotProduct_add]; ring

theorem q1 {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2} (hq : Quad q) (d : Fin n → ZMod 2) :
    ∃ (s : ZMod 2) (h : Fin n → ZMod 2), ∀ y, q (y + d) = q y + s + dotProduct h y := by
  obtain ⟨s, h, M, hM⟩ := hq
  refine ⟨dotProduct h d + ∑ i, ∑ j, M i j * d i * d j,
    fun k => ∑ j, M k j * d j + ∑ i, M i k * d i, fun y => ?_⟩
  have hs : ∑ k, (∑ i, M i k * d i) * y k = ∑ i, ∑ j, M i j * d i * y j := by
    simp only [Finset.sum_mul]; exact Finset.sum_comm
  have hs2 : ∑ k, (∑ j, M k j * d j) * y k = ∑ i, ∑ j, M i j * d j * y i := by
    simp only [Finset.sum_mul]
  have hdot : dotProduct (fun k => ∑ j, M k j * d j + ∑ i, M i k * d i) y =
      ∑ i, ∑ j, M i j * d j * y i + ∑ i, ∑ j, M i j * d i * y j := by
    simp only [dotProduct, add_mul, Finset.sum_add_distrib]; rw [hs, hs2]
  have hexp : ∀ i j, M i j * (y + d) i * (y + d) j = M i j * y i * y j + M i j * d i * d j +
      M i j * d j * y i + M i j * d i * y j := by
    intro i j; simp only [Pi.add_apply]; ring
  rw [hM, hM, dotProduct_add, hdot]
  simp only [hexp, Finset.sum_add_distrib]; ring

theorem q2 {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2} (hq : Quad q) (x a b c : Fin n → ZMod 2) :
    q (x + (a + b + c)) - q (x + (a + b)) - q (x + (a + c)) - q (x + (b + c)) +
      q (x + a) + q (x + b) + q (x + c) - q (x + 0) = 0 := by
  obtain ⟨s, h, hs⟩ := q1 hq a
  have e1 := hs (x + (b + c))
  have e2 := hs (x + b)
  have e3 := hs (x + c)
  have e4 := hs x
  rw [show x + (b + c) + a = x + (a + b + c) by abel] at e1
  rw [show x + b + a = x + (a + b) by abel] at e2
  rw [show x + c + a = x + (a + c) by abel] at e3
  rw [add_zero]
  simp only [dotProduct_add] at e1 e2 e3
  linear_combination e1 - e2 - e3 + e4

theorem sum1 {m : ℕ} (u f g : Fin m → ZMod 2) (j : Fin m) (h : ∀ i, i ≠ j → f i = g i) :
    ∑ i, u i * f i = ∑ i, u i * g i + u j * (f j - g j) := by
  have : ∑ i, (u i * f i - u i * g i) = u j * f j - u j * g j :=
    Fintype.sum_eq_single j (fun i hi => by rw [h i hi]; ring)
  rw [Finset.sum_sub_distrib] at this
  linear_combination this

theorem sum2 {m : ℕ} (u f g : Fin m → ZMod 2) (i j : Fin m) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    ∑ k, u k * f k = ∑ k, u k * g k + u i * (f i - g i) + u j * (f j - g j) := by
  have : ∑ k, (u k * f k - u k * g k) = (u i * f i - u i * g i) + (u j * f j - u j * g j) :=
    Fintype.sum_eq_add i j hij (fun k hk => by rw [h k hk.1 hk.2]; ring)
  rw [Finset.sum_sub_distrib] at this
  linear_combination this

theorem dot_lc {n m : ℕ} (c : Ix m → ZMod 2) (A : Ix m → Fin n → ZMod 2) (d : Fin n → ZMod 2) :
    dotProduct (∑ k, c k • A k) d = ∑ k, c k * dotProduct (A k) d := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _)

theorem dual_ex {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (T : Finset (Ix m)) (k : Ix m)
    (h : A k ∉ Submodule.span (ZMod 2) (A '' ↑T)) :
    ∃ d : Fin n → ZMod 2, dotProduct (A k) d = 1 ∧ ∀ j ∈ T, dotProduct (A j) d = 0 := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  have hfv : ∀ y, f y = dotProduct y (fun i => f (fun j => if i = j then 1 else 0)) := by
    intro y; rw [LinearMap.pi_apply_eq_sum_univ f y]; simp only [dotProduct, smul_eq_mul]
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), ?_, fun j hj => ?_⟩
  · rw [← hfv]; exact one_of_ne _ hf
  · rw [← hfv]
    have : f (A j) ∈ (Submodule.span (ZMod 2) (A '' ↑T)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
    rw [hmap] at this
    exact (Submodule.mem_bot (ZMod 2)).mp this

theorem fin_le {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (T : Finset (Ix m))
    (hall : ∀ k, A k ∈ Submodule.span (ZMod 2) (A '' ↑T)) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)) ≤ T.card := by
  have h1 : Submodule.span (ZMod 2) (Set.range A) ≤ Submodule.span (ZMod 2) (A '' ↑T) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)
  refine (Submodule.finrank_mono h1).trans ?_
  rw [← Finset.coe_image]
  exact (finrank_span_finset_le_card _).trans Finset.card_image_le

theorem not_mem_b {n m : ℕ} (A : Ix m → Fin n → ZMod 2)
    (hrank : 2 * m + 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)))
    (hL : A (none, false) ∈ Submodule.span (ZMod 2) (A '' (Finset.univ.erase ((none, false) : Ix m) : Set (Ix m))))
    (k : Ix m) (hk : k ≠ (none, false)) :
    A k ∉ Submodule.span (ZMod 2) (A '' ((Finset.univ.erase ((none, false) : Ix m)).erase k : Set (Ix m))) := by
  intro h
  have hmem : ∀ k', k' ≠ k → k' ≠ (none, false) →
      A k' ∈ Submodule.span (ZMod 2) (A '' ((Finset.univ.erase ((none, false) : Ix m)).erase k : Set (Ix m))) := by
    intro k' h1 h2; apply Submodule.subset_span; refine ⟨k', ?_, rfl⟩; simp [h1, h2]
  have hsub : Submodule.span (ZMod 2) (A '' (Finset.univ.erase ((none, false) : Ix m) : Set (Ix m))) ≤
      Submodule.span (ZMod 2) (A '' ((Finset.univ.erase ((none, false) : Ix m)).erase k : Set (Ix m))) := by
    rw [Submodule.span_le]; rintro _ ⟨k', hk', rfl⟩
    by_cases h1 : k' = k
    · rw [h1]; exact h
    · exact hmem k' h1 (by simpa using hk')
  have hall : ∀ k', A k' ∈
      Submodule.span (ZMod 2) (A '' ((Finset.univ.erase ((none, false) : Ix m)).erase k : Set (Ix m))) := by
    intro k'
    by_cases h1 : k' = k
    · rw [h1]; exact h
    by_cases h2 : k' = (none, false)
    · rw [h2]; exact hsub hL
    exact hmem k' h1 h2
  have hc := fin_le A _ hall
  rw [Finset.card_erase_of_mem (by simp [hk]), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ] at hc
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem Hshift1 {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (x t : Fin n → ZMod 2) (j : Fin m)
    (ht : ∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) t = 0) :
    HH A a u v (x + t) =
      (lin A a (none, false) x + dotProduct (A (none, false)) t + (∑ i, u i * PP A a i x +
        u j * ((lin A a (some j, false) x + dotProduct (A (some j, false)) t) *
          (lin A a (some j, true) x + dotProduct (A (some j, true)) t) - PP A a j x))) *
      (lin A a (none, true) x + dotProduct (A (none, true)) t + (∑ i, v i * PP A a i x +
        v j * ((lin A a (some j, false) x + dotProduct (A (some j, false)) t) *
          (lin A a (some j, true) x + dotProduct (A (some j, true)) t) - PP A a j x))) := by
  have hP : ∀ i, i ≠ j → PP A a i (x + t) = PP A a i x := by
    intro i hi; simp only [PP, lin_add, ht i hi, add_zero]
  have e1 : ∑ i, u i * PP A a i (x + t) =
      ∑ i, u i * PP A a i x + u j * (PP A a j (x + t) - PP A a j x) := sum1 u _ _ j hP
  have e2 : ∑ i, v i * PP A a i (x + t) =
      ∑ i, v i * PP A a i x + v j * (PP A a j (x + t) - PP A a j x) := sum1 v _ _ j hP
  have hPj : PP A a j (x + t) = (lin A a (some j, false) x + dotProduct (A (some j, false)) t) *
      (lin A a (some j, true) x + dotProduct (A (some j, true)) t) := by
    simp only [PP, lin_add]
  unfold HH; rw [e1, e2, hPj, lin_add, lin_add]

theorem Hshift2 {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (x t : Fin n → ZMod 2) (i j : Fin m) (hij : i ≠ j)
    (ht : ∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) t = 0) :
    HH A a u v (x + t) =
      (lin A a (none, false) x + dotProduct (A (none, false)) t + (∑ k, u k * PP A a k x +
        u i * ((lin A a (some i, false) x + dotProduct (A (some i, false)) t) *
          (lin A a (some i, true) x + dotProduct (A (some i, true)) t) - PP A a i x) +
        u j * ((lin A a (some j, false) x + dotProduct (A (some j, false)) t) *
          (lin A a (some j, true) x + dotProduct (A (some j, true)) t) - PP A a j x))) *
      (lin A a (none, true) x + dotProduct (A (none, true)) t + (∑ k, v k * PP A a k x +
        v i * ((lin A a (some i, false) x + dotProduct (A (some i, false)) t) *
          (lin A a (some i, true) x + dotProduct (A (some i, true)) t) - PP A a i x) +
        v j * ((lin A a (some j, false) x + dotProduct (A (some j, false)) t) *
          (lin A a (some j, true) x + dotProduct (A (some j, true)) t) - PP A a j x))) := by
  have hP : ∀ k, k ≠ i → k ≠ j → PP A a k (x + t) = PP A a k x := by
    intro k h1 h2; simp only [PP, lin_add, ht k h1 h2, add_zero]
  have e1 : ∑ k, u k * PP A a k (x + t) = ∑ k, u k * PP A a k x +
      u i * (PP A a i (x + t) - PP A a i x) + u j * (PP A a j (x + t) - PP A a j x) :=
    sum2 u _ _ i j hij hP
  have e2 : ∑ k, v k * PP A a k (x + t) = ∑ k, v k * PP A a k x +
      v i * (PP A a i (x + t) - PP A a i x) + v j * (PP A a j (x + t) - PP A a j x) :=
    sum2 v _ _ i j hij hP
  have hPi : PP A a i (x + t) = (lin A a (some i, false) x + dotProduct (A (some i, false)) t) *
      (lin A a (some i, true) x + dotProduct (A (some i, true)) t) := by
    simp only [PP, lin_add]
  have hPj : PP A a j (x + t) = (lin A a (some j, false) x + dotProduct (A (some j, false)) t) *
      (lin A a (some j, true) x + dotProduct (A (some j, true)) t) := by
    simp only [PP, lin_add]
  unfold HH; rw [e1, e2, hPi, hPj, lin_add, lin_add]

theorem inst1 {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (hq : Quad (HH A a u v)) (j : Fin m) (e f g : Fin n → ZMod 2)
    (he : ∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) e = 0)
    (hf : ∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) f = 0)
    (hg : ∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) g = 0)
    (e1 : dotProduct (A (none, true)) e = 1) (e2 : dotProduct (A (some j, false)) e = 0)
    (e3 : dotProduct (A (some j, true)) e = 0)
    (f1 : dotProduct (A (none, true)) f = 0) (f2 : dotProduct (A (some j, false)) f = 1)
    (f3 : dotProduct (A (some j, true)) f = 0)
    (g1 : dotProduct (A (none, true)) g = 0) (g2 : dotProduct (A (some j, false)) g = 0)
    (g3 : dotProduct (A (some j, true)) g = 1) :
    u j + dotProduct (A (none, false)) e * v j = 0 := by
  have key := q2 hq 0 e f g
  have Z : ∀ t t' : Fin n → ZMod 2, (∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) t = 0) →
      (∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) t' = 0) →
      ∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) (t + t') = 0 := by
    intro t t' h h' i hi b; rw [dotProduct_add, h i hi b, h' i hi b, add_zero]
  have Z0 : ∀ i, i ≠ j → ∀ b, dotProduct (A (some i, b)) (0 : Fin n → ZMod 2) = 0 :=
    fun _ _ _ => dotProduct_zero _
  rw [Hshift1 A a u v 0 _ j (Z _ _ (Z _ _ he hf) hg), Hshift1 A a u v 0 _ j (Z _ _ he hf),
    Hshift1 A a u v 0 _ j (Z _ _ he hg), Hshift1 A a u v 0 _ j (Z _ _ hf hg),
    Hshift1 A a u v 0 _ j he, Hshift1 A a u v 0 _ j hf, Hshift1 A a u v 0 _ j hg,
    Hshift1 A a u v 0 _ j Z0] at key
  simp only [dotProduct_add, dotProduct_zero, e1, e2, e3, f1, f2, f3, g1, g2, g3] at key
  linear_combination key

theorem inst2 {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (hq : Quad (HH A a u v)) (i j : Fin m) (hij : i ≠ j) (d f g : Fin n → ZMod 2)
    (hd : ∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) d = 0)
    (hf : ∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) f = 0)
    (hg : ∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) g = 0)
    (d1 : dotProduct (A (none, true)) d = 0) (d2 : dotProduct (A (some j, false)) d = 0)
    (d3 : dotProduct (A (some j, true)) d = 0)
    (f1 : dotProduct (A (none, true)) f = 0) (f2 : dotProduct (A (some i, false)) f = 0)
    (f3 : dotProduct (A (some i, true)) f = 0) (f4 : dotProduct (A (some j, false)) f = 1)
    (f5 : dotProduct (A (some j, true)) f = 0)
    (g1 : dotProduct (A (none, true)) g = 0) (g2 : dotProduct (A (some i, false)) g = 0)
    (g3 : dotProduct (A (some i, true)) g = 0) (g4 : dotProduct (A (some j, false)) g = 0)
    (g5 : dotProduct (A (some j, true)) g = 1)
    (cc : ZMod 2) (hui : u i + cc * v i = 0) (huj : u j + cc * v j = 0) :
    dotProduct (A (none, false)) d * v j = 0 := by
  have key := q2 hq 0 d f g
  have Z : ∀ t t' : Fin n → ZMod 2,
      (∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) t = 0) →
      (∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) t' = 0) →
      ∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) (t + t') = 0 := by
    intro t t' h h' k h1 h2 b; rw [dotProduct_add, h k h1 h2 b, h' k h1 h2 b, add_zero]
  have Z0 : ∀ k, k ≠ i → k ≠ j → ∀ b, dotProduct (A (some k, b)) (0 : Fin n → ZMod 2) = 0 :=
    fun _ _ _ _ => dotProduct_zero _
  rw [Hshift2 A a u v 0 _ i j hij (Z _ _ (Z _ _ hd hf) hg),
    Hshift2 A a u v 0 _ i j hij (Z _ _ hd hf),
    Hshift2 A a u v 0 _ i j hij (Z _ _ hd hg), Hshift2 A a u v 0 _ i j hij (Z _ _ hf hg),
    Hshift2 A a u v 0 _ i j hij hd, Hshift2 A a u v 0 _ i j hij hf,
    Hshift2 A a u v 0 _ i j hij hg, Hshift2 A a u v 0 _ i j hij Z0] at key
  simp only [dotProduct_add, dotProduct_zero, d1, d2, d3, f1, f2, f3, f4, f5,
    g1, g2, g3, g4, g5] at key
  linear_combination key -
    (v j * (dotProduct (A (some i, false)) d * lin A a (some i, true) 0 +
      dotProduct (A (some i, true)) d * lin A a (some i, false) 0 +
      dotProduct (A (some i, false)) d * dotProduct (A (some i, true)) d)) * hui -
    (v i * (dotProduct (A (some i, false)) d * lin A a (some i, true) 0 +
      dotProduct (A (some i, true)) d * lin A a (some i, false) 0 +
      dotProduct (A (some i, false)) d * dotProduct (A (some i, true)) d)) * huj +
    (cc * v i * v j * (dotProduct (A (some i, false)) d * lin A a (some i, true) 0 +
      dotProduct (A (some i, true)) d * lin A a (some i, false) 0 +
      dotProduct (A (some i, false)) d * dotProduct (A (some i, true)) d)) * two

theorem main_a {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (hLn : A (none, false) ∉ Submodule.span (ZMod 2)
      (A '' (Finset.univ.erase ((none, false) : Ix m) : Set (Ix m))))
    (hRn : A (none, true) ∉ Submodule.span (ZMod 2)
      (A '' (Finset.univ.erase ((none, true) : Ix m) : Set (Ix m))))
    (hq : Quad (HH A a u v)) :
    ∃ (X Y Z : (Fin n → ZMod 2) → ZMod 2) (w : Fin m → ZMod 2), Aff X ∧ Aff Y ∧ Aff Z ∧
      ∀ x, HH A a u v x = X x * Y x + Z x + ∑ i, w i * PP A a i x := by
  obtain ⟨dL, hL1, hL0⟩ := dual_ex A _ _ hLn
  obtain ⟨dR, hR1, hR0⟩ := dual_ex A _ _ hRn
  have hPL : ∀ i x, PP A a i (x + dL) = PP A a i x := by
    intro i x
    simp only [PP, lin_add, hL0 (some i, false) (by simp), hL0 (some i, true) (by simp), add_zero]
  have hPR : ∀ i x, PP A a i (x + dR) = PP A a i x := by
    intro i x
    simp only [PP, lin_add, hR0 (some i, false) (by simp), hR0 (some i, true) (by simp), add_zero]
  have hY : Aff (fun x => lin A a (none, true) x + ∑ i, v i * PP A a i x) := by
    obtain ⟨s, h, hs⟩ := q1 hq dL
    refine ⟨s, h, fun x => ?_⟩
    have e := hs x
    have e2 : HH A a u v (x + dL) = (lin A a (none, false) x + 1 + ∑ i, u i * PP A a i x) *
        (lin A a (none, true) x + ∑ i, v i * PP A a i x) := by
      unfold HH
      simp only [hPL, lin_add, hL1, hL0 (none, true) (by simp), add_zero]
    rw [e2] at e; unfold HH at e
    linear_combination e
  have hX : Aff (fun x => lin A a (none, false) x + ∑ i, u i * PP A a i x) := by
    obtain ⟨s, h, hs⟩ := q1 hq dR
    refine ⟨s, h, fun x => ?_⟩
    have e := hs x
    have e2 : HH A a u v (x + dR) = (lin A a (none, false) x + ∑ i, u i * PP A a i x) *
        (lin A a (none, true) x + 1 + ∑ i, v i * PP A a i x) := by
      unfold HH
      simp only [hPR, lin_add, hR1, hR0 (none, false) (by simp), add_zero]
    rw [e2] at e; unfold HH at e
    linear_combination e
  refine ⟨_, _, fun _ => 0, fun _ => 0, hX, hY, ⟨0, 0, fun x => by simp⟩, fun x => ?_⟩
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rfl

theorem main_b {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (hrank : 2 * m + 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)))
    (hL : A (none, false) ∈ Submodule.span (ZMod 2)
      (A '' (Finset.univ.erase ((none, false) : Ix m) : Set (Ix m))))
    (hq : Quad (HH A a u v)) :
    ∃ (X Y Z : (Fin n → ZMod 2) → ZMod 2) (w : Fin m → ZMod 2), Aff X ∧ Aff Y ∧ Aff Z ∧
      ∀ x, HH A a u v x = X x * Y x + Z x + ∑ i, w i * PP A a i x := by
  have hd : ∀ k : Ix m, k ≠ (none, false) → ∃ d : Fin n → ZMod 2,
      dotProduct (A k) d = 1 ∧ ∀ k', k' ≠ (none, false) → k' ≠ k → dotProduct (A k') d = 0 := by
    intro k hk
    obtain ⟨d, h1, h2⟩ := dual_ex A _ k (not_mem_b A hrank hL k hk)
    exact ⟨d, h1, fun k' h3 h4 => h2 k' (by simp [h3, h4])⟩
  choose D hD1 hD0 using hd
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination (ZMod 2)).mp hL
  have hc0 : l (none, false) = 0 := by
    by_contra h
    have h1 : ((none, false) : Ix m) ∈ l.support := Finsupp.mem_support_iff.mpr h
    have h2 := (Finsupp.mem_supported (ZMod 2) _).mp hl h1
    simp at h2
  have hrel : A (none, false) = ∑ k, l k • A k := by
    rw [← hlc, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have hlam : ∀ k (hk : k ≠ (none, false)), dotProduct (A (none, false)) (D k hk) = l k := by
    intro k hk
    rw [hrel, dot_lc, Fintype.sum_eq_single k, hD1, mul_one]
    intro k' hk'
    by_cases h : k' = (none, false)
    · rw [h, hc0, zero_mul]
    · rw [hD0 k hk k' h hk', mul_zero]
  have hRne : ((none, true) : Ix m) ≠ (none, false) := by simp
  have hfne : ∀ j : Fin m, ((some j, false) : Ix m) ≠ (none, false) := by simp
  have htne : ∀ j : Fin m, ((some j, true) : Ix m) ≠ (none, false) := by simp
  have hbne : ∀ (j : Fin m) (b : Bool), ((some j, b) : Ix m) ≠ (none, false) := by simp
  have hi : ∀ j, u j + l (none, true) * v j = 0 := by
    intro j
    have := inst1 A a u v hq j (D _ hRne) (D _ (hfne j)) (D _ (htne j))
      (fun i _ b => hD0 _ _ _ (by simp) (by simp))
      (fun i hi b => hD0 _ _ _ (by simp) (by simp [hi]))
      (fun i hi b => hD0 _ _ _ (by simp) (by simp [hi]))
      (hD1 _ _) (hD0 _ _ _ (by simp) (by simp)) (hD0 _ _ _ (by simp) (by simp))
      (hD0 _ _ _ (by simp) (by simp)) (hD1 _ _) (hD0 _ _ _ (by simp) (by simp))
      (hD0 _ _ _ (by simp) (by simp)) (hD0 _ _ _ (by simp) (by simp)) (hD1 _ _)
    rwa [hlam] at this
  have hα : ∀ i j : Fin m, i ≠ j → ∀ b, l (some i, b) * v j = 0 := by
    intro i j hij b
    have := inst2 A a u v hq i j hij (D _ (hbne i b)) (D _ (hfne j)) (D _ (htne j))
      (fun k hk _ b' => hD0 _ _ _ (by simp) (by simp [hk]))
      (fun k _ hk b' => hD0 _ _ _ (by simp) (by simp [hk]))
      (fun k _ hk b' => hD0 _ _ _ (by simp) (by simp [hk]))
      (hD0 _ _ _ (by simp) (by simp)) (hD0 _ _ _ (by simp) (by simp [hij, hij.symm]))
      (hD0 _ _ _ (by simp) (by simp [hij, hij.symm]))
      (hD0 _ _ _ (by simp) (by simp)) (hD0 _ _ _ (by simp) (by simp [hij, hij.symm]))
      (hD0 _ _ _ (by simp) (by simp [hij, hij.symm])) (hD1 _ _)
      (hD0 _ _ _ (by simp) (by simp))
      (hD0 _ _ _ (by simp) (by simp)) (hD0 _ _ _ (by simp) (by simp [hij, hij.symm]))
      (hD0 _ _ _ (by simp) (by simp [hij, hij.symm])) (hD0 _ _ _ (by simp) (by simp))
      (hD1 _ _) (l (none, true)) (hi i) (hi j)
    rwa [hlam] at this
  refine ⟨lin A a (none, false), lin A a (none, true), fun _ => 0,
    fun j => v j * (l (none, true) + (a (none, false) - ∑ k, l k * a k) +
      l (some j, false) + l (some j, true)),
    ⟨a _, A _, fun x => rfl⟩, ⟨a _, A _, fun x => rfl⟩, ⟨0, 0, fun x => by simp⟩, fun x => ?_⟩
  have hdot : dotProduct (A (none, false)) x = ∑ k, l k * dotProduct (A k) x := by
    rw [hrel, dot_lc]
  have hL0 : lin A a (none, false) x =
      (a (none, false) - ∑ k, l k * a k) + ∑ k, l k * lin A a k x := by
    have : ∑ k, l k * lin A a k x = ∑ k, l k * a k + ∑ k, l k * dotProduct (A k) x := by
      simp only [lin, mul_add, Finset.sum_add_distrib]
    rw [this]; unfold lin; rw [hdot]; ring
  have hdec : ∑ k, l k * lin A a k x =
      (l (none, true) * lin A a (none, true) x + l (none, false) * lin A a (none, false) x) +
      ∑ i, (l (some i, true) * lin A a (some i, true) x +
        l (some i, false) * lin A a (some i, false) x) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool]
  have hU : ∑ i, u i * PP A a i x = l (none, true) * ∑ i, v i * PP A a i x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eq_of_add _ _ (hi j)]; ring
  have hT : (∑ j, v j * PP A a j x) * ∑ i, (l (some i, true) * lin A a (some i, true) x +
        l (some i, false) * lin A a (some i, false) x) =
      ∑ j, v j * (l (some j, true) + l (some j, false)) * PP A a j x := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Fintype.sum_eq_single j]
    · have hp := sq_self (lin A a (some j, false) x)
      have hq' := sq_self (lin A a (some j, true) x)
      simp only [PP]
      linear_combination (v j * l (some j, true) * lin A a (some j, false) x) * hq' +
        (v j * l (some j, false) * lin A a (some j, true) x) * hp
    · intro i hij
      have h1 := hα i j hij true
      have h2 := hα i j hij false
      linear_combination (PP A a j x * lin A a (some i, true) x) * h1 +
        (PP A a j x * lin A a (some i, false) x) * h2
  have hw : ∑ j, v j * (l (none, true) + (a (none, false) - ∑ k, l k * a k) +
        l (some j, false) + l (some j, true)) * PP A a j x =
      (l (none, true) + (a (none, false) - ∑ k, l k * a k)) * ∑ j, v j * PP A a j x +
        ∑ j, v j * (l (some j, true) + l (some j, false)) * PP A a j x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hW := sq_self (∑ j, v j * PP A a j x)
  show (lin A a (none, false) x + ∑ i, u i * PP A a i x) *
    (lin A a (none, true) x + ∑ i, v i * PP A a i x) = _
  linear_combination (lin A a (none, true) x + ∑ i, v i * PP A a i x) * hU +
    (∑ j, v j * PP A a j x) * (hL0.trans (by rw [hdec, hc0])) + hT - hw +
    l (none, true) * hW +
    l (none, true) * lin A a (none, true) x * (∑ j, v j * PP A a j x) * two

def sw {m : ℕ} (k : Ix m) : Ix m := match k with
  | (none, b) => (none, !b)
  | (some i, b) => (some i, b)

theorem sw_sw {m : ℕ} (k : Ix m) : sw (sw k) = k := by
  rcases k with ⟨_ | i, b⟩ <;> simp [sw]

theorem sw_ne {m : ℕ} (k : Ix m) (h : k ≠ (none, true)) : sw k ≠ (none, false) := by
  rcases k with ⟨_ | i, b⟩ <;> cases b <;> simp_all [sw]

theorem main {n m : ℕ} (A : Ix m → Fin n → ZMod 2) (a : Ix m → ZMod 2) (u v : Fin m → ZMod 2)
    (hrank : 2 * m + 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)))
    (hq : Quad (HH A a u v)) :
    ∃ (X Y Z : (Fin n → ZMod 2) → ZMod 2) (w : Fin m → ZMod 2), Aff X ∧ Aff Y ∧ Aff Z ∧
      ∀ x, HH A a u v x = X x * Y x + Z x + ∑ i, w i * PP A a i x := by
  by_cases hL : A (none, false) ∈ Submodule.span (ZMod 2)
      (A '' (Finset.univ.erase ((none, false) : Ix m) : Set (Ix m)))
  · exact main_b A a u v hrank hL hq
  by_cases hR : A (none, true) ∈ Submodule.span (ZMod 2)
      (A '' (Finset.univ.erase ((none, true) : Ix m) : Set (Ix m)))
  · have hsw : ∀ x, HH (fun k => A (sw k)) (fun k => a (sw k)) v u x = HH A a u v x := by
      intro x; unfold HH; exact mul_comm _ _
    have hrange : Set.range (fun k => A (sw k)) = Set.range A := by
      ext y; constructor
      · rintro ⟨k, rfl⟩; exact ⟨sw k, rfl⟩
      · rintro ⟨k, rfl⟩; exact ⟨sw k, by simp only [sw_sw]⟩
    have hsub : A '' (Finset.univ.erase ((none, true) : Ix m) : Set (Ix m)) ⊆
        (fun k => A (sw k)) '' (Finset.univ.erase ((none, false) : Ix m) : Set (Ix m)) := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨sw k, ?_, by simp only [sw_sw]⟩
      have : k ≠ (none, true) := by simpa using hk
      simpa using sw_ne k this
    obtain ⟨s, h, M, hM⟩ := hq
    obtain ⟨X, Y, Z, w, hX, hY, hZ, hH⟩ := main_b (fun k => A (sw k)) (fun k => a (sw k)) v u
      (by rw [hrange]; exact hrank) (Submodule.span_mono hsub hR)
      ⟨s, h, M, fun x => by rw [hsw]; exact hM x⟩
    exact ⟨X, Y, Z, w, hX, hY, hZ, fun x => by rw [← hsw, hH x]; rfl⟩
  · exact main_a A a u v hL hR hq

end PEqualNP.Outside.L_lib_891

open PEqualNP.Outside.L_lib_891 in
theorem PEqualNP.Outside.L_lib_891 : ∀ n m : ℕ,
  let F := ZMod 2
  let V := Fin n → F
  let I := Option (Fin m) × Bool
  let quad := fun (q : V → F) => ∃ (s : F) (h : V) (M : Fin n → Fin n → F),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j
  let aff := fun (q : V → F) => ∃ (s : F) (h : V), ∀ x, q x = s + dotProduct h x
  ∀ (A : I → V) (a : I → F) (u v : Fin m → F),
    2*m+1 ≤ Module.finrank F (Submodule.span F (Set.range A)) →
    let lin := fun (k : I) (x : V) => a k + dotProduct (A k) x
    let P := fun (i : Fin m) (x : V) => lin (some i,false) x * lin (some i,true) x
    let H := fun (x : V) =>
      (lin (none,false) x + ∑ i, u i * P i x) * (lin (none,true) x + ∑ i, v i * P i x)
    quad H → ∃ (X Y Z : V → F) (w : Fin m → F), aff X ∧ aff Y ∧ aff Z ∧
      ∀ x, H x = X x * Y x + Z x + ∑ i, w i * P i x := by
  intro n m F V I quad aff A a u v hrank lin P H hq
  exact main A a u v hrank hq
