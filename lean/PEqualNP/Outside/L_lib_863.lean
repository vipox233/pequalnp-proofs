import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_863

open Finset Matrix

def eps (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem two0 : (2 : ZMod 2) = 0 := by decide

@[simp] theorem eps_zero : eps 0 = 1 := rfl
@[simp] theorem eps_one : eps 1 = -1 := rfl

theorem eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  rcases z2 a with h | h <;> rcases z2 b with h' | h' <;> subst h <;> subst h' <;> rfl

theorem eq_iff_add : ∀ x y : ZMod 2, x = y ↔ x + y = 0 := by decide

theorem vadd_self {n : ℕ} (u : Fin n → ZMod 2) : u + u = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; rcases z2 (u i) with h | h <;> rw [h] <;> decide

def pol {n : ℕ} (h : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) : ZMod 2 :=
  h (u + v) + h u + h v + h 0

def Rep {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) (h : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ u v, h (u + v) + h u + h v + h 0 = u ⬝ᵥ (N *ᵥ v)

def IsQ {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ (b : ZMod 2) (a : Fin n → ZMod 2) (M : Fin n → Fin n → ZMod 2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

theorem sum_eps_dot {n : ℕ} (c : Fin n → ZMod 2) :
    ∑ u : Fin n → ZMod 2, eps (u ⬝ᵥ c) = if c = 0 then 2 ^ n else 0 := by
  split_ifs with hc
  · subst hc
    simp [eps, Finset.card_univ, Fintype.card_fun, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    have hci : c i = 1 := by
      rcases z2 (c i) with h | h
      · exact absurd h hi
      · exact h
    have key := Fintype.sum_equiv (Equiv.addRight (Pi.single i 1))
      (fun u => eps ((u + Pi.single i 1) ⬝ᵥ c)) (fun u => eps (u ⬝ᵥ c)) (fun _ => rfl)
    simp only [add_dotProduct, single_dotProduct, hci, one_mul, eps_add, eps_one, mul_neg,
      mul_one, Finset.sum_neg_distrib] at key
    linarith

theorem rep_of_quad {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2}
    (b : ZMod 2) (a : Fin n → ZMod 2) (A : Fin n → Fin n → ZMod 2)
    (hq : ∀ v, q v = b + dotProduct a v + ∑ i, ∑ j, A i j * v i * v j) :
    Rep (Matrix.of A + (Matrix.of A)ᵀ) q := by
  intro u v
  have hX : ∑ i, ∑ j, A i j * (u i * v j + v i * u j) =
      u ⬝ᵥ ((Matrix.of A + (Matrix.of A)ᵀ) *ᵥ v) := by
    simp only [dotProduct, mulVec, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
      Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have hT : ∑ i, ∑ j, A i j * (u + v) i * (u + v) j = ∑ i, ∑ j, A i j * u i * u j +
      ∑ i, ∑ j, A i j * v i * v j + ∑ i, ∑ j, A i j * (u i * v j + v i * u j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    simp only [Pi.add_apply]; ring
  rw [hq, hq, hq, hq, hT, ← hX, dotProduct_add, dotProduct_zero]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  linear_combination (2 * b + a ⬝ᵥ u + a ⬝ᵥ v + ∑ i, ∑ j, A i j * u i * u j +
    ∑ i, ∑ j, A i j * v i * v j) * two0

theorem quad_rep {n : ℕ} {q : (Fin n → ZMod 2) → ZMod 2} (h : IsQ q) :
    ∃ N, Rep N q := by
  obtain ⟨b, a, A, hq⟩ := h
  exact ⟨_, rep_of_quad b a A hq⟩

theorem rep_congr {n : ℕ} {N} {f g : (Fin n → ZMod 2) → ZMod 2} (h : Rep N f)
    (e : ∀ u, g u = f u) : Rep N g := by
  intro u v; rw [e, e, e, e]; exact h u v

theorem rep_add {n : ℕ} {N N'} {f g : (Fin n → ZMod 2) → ZMod 2} (hf : Rep N f)
    (hg : Rep N' g) : Rep (N + N') (fun u => f u + g u) := by
  intro u v
  beta_reduce
  rw [add_mulVec, dotProduct_add, ← hf u v, ← hg u v]; ring

theorem rep_aff {n : ℕ} {N} {f : (Fin n → ZMod 2) → ZMod 2} (hf : Rep N f)
    (a : Fin n → ZMod 2) (b : ZMod 2) : Rep N (fun u => f u + (a ⬝ᵥ u + b)) := by
  intro u v
  beta_reduce
  rw [← hf u v, dotProduct_add, dotProduct_zero]
  linear_combination (2 * b + a ⬝ᵥ u + a ⬝ᵥ v) * two0

theorem rep_unique {n : ℕ} {N N'} {f : (Fin n → ZMod 2) → ZMod 2} (h : Rep N f)
    (h' : Rep N' f) : N = N' := by
  ext i j
  have e := (h (Pi.single i 1) (Pi.single j 1)).symm.trans (h' (Pi.single i 1) (Pi.single j 1))
  simpa [mulVec_single_one, single_dotProduct] using e

theorem rep_symm {n : ℕ} {N} {f : (Fin n → ZMod 2) → ZMod 2} (h : Rep N f) (u v) :
    u ⬝ᵥ (N *ᵥ v) = v ⬝ᵥ (N *ᵥ u) := by
  rw [← h, ← h, add_comm u v]; ring

theorem rep_diag {n : ℕ} {N} {f : (Fin n → ZMod 2) → ZMod 2} (h : Rep N f) (u) :
    u ⬝ᵥ (N *ᵥ u) = 0 := by
  rw [← h, vadd_self]
  linear_combination (f u + f 0) * two0

theorem rank_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem ker_card {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0)).card = 2 ^ (n - N.rank) := by
  classical
  have h1 : (univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0)).card =
      Fintype.card (LinearMap.ker N.mulVecLin) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by simp))
  have h2 : Fintype.card (LinearMap.ker N.mulVecLin) =
      2 ^ (Module.finrank (ZMod 2) (LinearMap.ker N.mulVecLin)) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have h3 := N.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h3
  rw [h1, h2]
  congr 1
  unfold Matrix.rank
  omega

theorem bias_sq {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) (h : (Fin n → ZMod 2) → ZMod 2)
    (hr : Rep N h) :
    (∑ u, eps (h u)) ^ 2 =
      2 ^ n * ∑ w ∈ univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0), eps (h w + h 0) := by
  rw [sq, Finset.sum_mul_sum]
  have step : ∀ u, ∑ v, eps (h u) * eps (h v) =
      ∑ w, eps (h w + h 0) * eps (u ⬝ᵥ (N *ᵥ w)) := by
    intro u
    rw [← Fintype.sum_equiv (Equiv.addLeft u) (fun w => eps (h u) * eps (h (u + w)))
      (fun v => eps (h u) * eps (h v)) (fun _ => rfl)]
    apply Finset.sum_congr rfl; intro w _
    rw [← eps_add, ← eps_add]; congr 1
    have := hr u w
    linear_combination (-(h w + h 0)) * two0 + this
  rw [Finset.sum_congr rfl (fun u _ => step u), Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_eps_dot]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w _
  split_ifs <;> ring

theorem ker_sum {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) (h : (Fin n → ZMod 2) → ZMod 2)
    (hr : Rep N h) :
    (∑ w ∈ univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0), eps (h w + h 0) = 0) ∨
    (∑ w ∈ univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0), eps (h w + h 0) =
      (univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0)).card) := by
  by_cases hall : ∀ w ∈ univ.filter (fun w : Fin n → ZMod 2 => N *ᵥ w = 0), h w + h 0 = 0
  · right
    rw [Finset.sum_congr rfl (fun w hw => by rw [hall w hw])]
    simp
  · left
    push Not at hall
    obtain ⟨w0, hw0, hne⟩ := hall
    have hw0' : N *ᵥ w0 = 0 := (Finset.mem_filter.1 hw0).2
    have h1 : h w0 + h 0 = 1 := by
      rcases z2 (h w0 + h 0) with e | e
      · exact absurd e hne
      · exact e
    rw [Finset.sum_filter]
    have key := Fintype.sum_equiv (Equiv.addRight w0)
      (fun w => if N *ᵥ (w + w0) = 0 then eps (h (w + w0) + h 0) else 0)
      (fun w => if N *ᵥ w = 0 then eps (h w + h 0) else 0) (fun _ => rfl)
    have e2 : ∀ w, (if N *ᵥ (w + w0) = 0 then eps (h (w + w0) + h 0) else 0) =
        -(if N *ᵥ w = 0 then eps (h w + h 0) else 0) := by
      intro w
      rw [mulVec_add, hw0', add_zero]
      split_ifs with hw
      · have := hr w w0
        rw [hw0', dotProduct_zero] at this
        have e3 : h (w + w0) + h 0 = (h w + h 0) + 1 := by
          rw [← h1]; linear_combination this + (-(h w + h w0 + h 0)) * two0
        rw [e3, eps_add, eps_one]; ring
      · simp
    simp only [e2, Finset.sum_neg_distrib] at key
    linarith

theorem sq_cases {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) (h : (Fin n → ZMod 2) → ZMod 2)
    (hr : Rep N h) :
    (∑ u, eps (h u)) ^ 2 = 0 ∨ (∑ u, eps (h u)) ^ 2 = 2 ^ n * 2 ^ (n - N.rank) := by
  rw [bias_sq N h hr]
  rcases ker_sum N h hr with e | e
  · left; rw [e, mul_zero]
  · right; rw [e, ker_card]; push_cast; ring

theorem sq_pow2 {x k : ℕ} (h : x ^ 2 = 2 ^ k) : ∃ i, x = 2 ^ i ∧ 2 * i = k := by
  have hx : x ∣ 2 ^ k := ⟨x, by rw [← h]; ring⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hx
  refine ⟨i, rfl, ?_⟩
  rw [← pow_mul] at h
  exact Nat.pow_right_injective le_rfl (by rw [mul_comm]; exact h)

theorem abs_cases {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) (h : (Fin n → ZMod 2) → ZMod 2)
    (hr : Rep N h) :
    (∑ u, eps (h u)) = 0 ∨ ∃ i, (∑ u, eps (h u)).natAbs = 2 ^ i ∧ 2 * i = n + (n - N.rank) := by
  rcases sq_cases N h hr with e | e
  · left; exact pow_eq_zero_iff (by norm_num) |>.1 e
  · right
    apply sq_pow2
    have := congrArg Int.natAbs e
    rw [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at this
    rw [this, pow_add]; rfl

theorem parseval {n : ℕ} (h : (Fin n → ZMod 2) → ZMod 2) :
    ∑ a : Fin n → ZMod 2, (∑ u, eps (h u + (a ⬝ᵥ u + 0))) ^ 2 = 2 ^ n * 2 ^ n := by
  have e1 : ∀ a : Fin n → ZMod 2, (∑ u, eps (h u + (a ⬝ᵥ u + 0))) ^ 2 =
      ∑ u, ∑ v, eps (h u + h v) * eps (a ⬝ᵥ (u + v)) := by
    intro a
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _
    rw [← eps_add, ← eps_add, dotProduct_add]; congr 1; ring
  have e3 : ∀ u : Fin n → ZMod 2, ∑ a : Fin n → ZMod 2, ∑ v, eps (h u + h v) * eps (a ⬝ᵥ (u + v)) =
      ∑ v, eps (h u + h v) * (if u + v = 0 then 2 ^ n else 0) := by
    intro u
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    rw [← Finset.mul_sum, sum_eps_dot]
  have e2 : ∀ u v : Fin n → ZMod 2, (u + v = 0) ↔ u = v := by
    intro u v
    constructor
    · intro e
      have : u + v + v = v := by rw [e, zero_add]
      rw [add_assoc, vadd_self, add_zero] at this
      exact this
    · intro e; rw [e]; exact vadd_self v
  simp_rw [e1]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun u _ => e3 u)]
  simp_rw [e2, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e4 : ∀ u : Fin n → ZMod 2, h u + h u = 0 := by
    intro u; linear_combination (h u) * two0
  simp only [e4, eps_zero, one_mul]
  simp [Finset.card_univ, Fintype.card_fun, ZMod.card]

theorem fit {n c : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) (h : (Fin n → ZMod 2) → ZMod 2)
    (hr : Rep N h) (hc : N.rank = 2 * c) :
    ∃ (a : Fin n → ZMod 2) (b : ZMod 2), ∑ u, eps (h u + (a ⬝ᵥ u + b)) = 2 ^ (n - c) := by
  have hcn : 2 * c ≤ n := hc ▸ N.rank_le_width
  have hex : ∃ a : Fin n → ZMod 2, ∑ u, eps (h u + (a ⬝ᵥ u + 0)) ≠ 0 := by
    by_contra hno
    push Not at hno
    have := parseval h
    simp only [hno] at this
    simp at this
  obtain ⟨a, ha⟩ := hex
  have hs := sq_cases N _ (rep_aff hr a 0)
  rcases hs with e | e
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 e) ha
  · have e' : (∑ u, eps (h u + (a ⬝ᵥ u + 0))) ^ 2 = (2 ^ (n - c)) ^ 2 := by
      rw [e, hc, ← pow_mul, ← pow_add]; congr 1; omega
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e' with e1 | e1
    · exact ⟨a, 0, e1⟩
    · refine ⟨a, 1, ?_⟩
      have : ∀ u, eps (h u + (a ⬝ᵥ u + 1)) = -eps (h u + (a ⬝ᵥ u + 0)) := by
        intro u
        rw [show h u + (a ⬝ᵥ u + 1) = (h u + (a ⬝ᵥ u + 0)) + 1 by ring, eps_add, eps_one]; ring
      simp only [this, Finset.sum_neg_distrib, e1, neg_neg]

theorem isq_add {n : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2} (hf : IsQ f) (hg : IsQ g) :
    IsQ (fun u => f u + g u) := by
  obtain ⟨b, a, A, hA⟩ := hf
  obtain ⟨b', a', A', hA'⟩ := hg
  refine ⟨b + b', a + a', fun i j => A i j + A' i j, fun v => ?_⟩
  simp only [hA, hA', add_dotProduct, add_mul, Finset.sum_add_distrib]
  ring

theorem isq_aff {n : ℕ} (a : Fin n → ZMod 2) (b : ZMod 2) : IsQ (fun u => a ⬝ᵥ u + b) :=
  ⟨b, a, fun _ _ => 0, fun v => by simp; ring⟩

theorem isq_zero {n : ℕ} : IsQ (fun _ : Fin n → ZMod 2 => 0) :=
  ⟨0, 0, fun _ _ => 0, fun v => by simp⟩

theorem mem_pair {n : ℕ} (p q z : Fin n → ZMod 2) :
    z ∈ Submodule.span (ZMod 2) (Set.range ![p, q]) ↔ ∃ s t : ZMod 2, s • p + t • q = z := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c 0, c 1, by simpa [Fin.sum_univ_two] using hc⟩
  · rintro ⟨s, t, hc⟩; exact ⟨![s, t], by simpa [Fin.sum_univ_two] using hc⟩

theorem peel {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (f : (Fin n → ZMod 2) → ZMod 2)
    (hA : Rep A f) (hpos : 0 < A.rank) :
    ∃ (g : (Fin n → ZMod 2) → ZMod 2) (H : Matrix (Fin n) (Fin n) (ZMod 2)),
      IsQ g ∧ Rep H g ∧ H.rank ≤ 2 ∧ (A + H).rank + 2 ≤ A.rank := by
  have hA0 : A ≠ 0 := by rintro rfl; simp at hpos
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hno; push Not at hno; exact hA0 (Matrix.ext hno)
  have hij1 : A i j = 1 := by
    rcases z2 (A i j) with e | e
    · exact absurd e hij
    · exact e
  set x : Fin n → ZMod 2 := Pi.single j 1
  set y : Fin n → ZMod 2 := Pi.single i 1
  set p := A *ᵥ x
  set q := A *ᵥ y
  have hyx : y ⬝ᵥ p = 1 := by simp [y, p, x, mulVec_single_one, single_dotProduct, hij1]
  have hpx : p ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact rep_diag hA x
  have hqy : q ⬝ᵥ y = 0 := by rw [dotProduct_comm]; exact rep_diag hA y
  have hqx : q ⬝ᵥ x = 1 := by rw [dotProduct_comm, rep_symm hA]; exact hyx
  have hpy : p ⬝ᵥ y = 1 := by rw [dotProduct_comm]; exact hyx
  let Bq : Fin n → Fin n → ZMod 2 := fun k l => p k * q l
  let g : (Fin n → ZMod 2) → ZMod 2 := fun u => (u ⬝ᵥ p) * (u ⬝ᵥ q)
  have hgq : ∀ v, g v = 0 + dotProduct 0 v + ∑ k, ∑ l, Bq k l * v k * v l := by
    intro v
    simp only [g, Bq, zero_dotProduct, zero_add]
    simp only [dotProduct, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring
  set H := Matrix.of Bq + (Matrix.of Bq)ᵀ
  have hH : Rep H g := rep_of_quad 0 0 Bq hgq
  have hHv : ∀ v, H *ᵥ v = (q ⬝ᵥ v) • p + (p ⬝ᵥ v) • q := by
    intro v; funext k
    simp only [H, Bq, mulVec, dotProduct, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.of_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> ring
  set P := Submodule.span (ZMod 2) (Set.range ![p, q])
  have hsep : ∀ s t : ZMod 2, (s • p + t • q) ⬝ᵥ x = t ∧ (s • p + t • q) ⬝ᵥ y = s := by
    intro s t
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hpx, hqx, hpy, hqy]
    constructor <;> ring
  have hli : LinearIndependent (ZMod 2) ![p, q] := by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have := hsep s t
    rw [e, zero_dotProduct, zero_dotProduct] at this
    exact ⟨this.2.symm, this.1.symm⟩
  have hP2 : Module.finrank (ZMod 2) P = 2 := by
    rw [finrank_span_eq_card hli]; simp
  have hpP : p ∈ P := Submodule.subset_span ⟨0, rfl⟩
  have hqP : q ∈ P := Submodule.subset_span ⟨1, rfl⟩
  have hrH : LinearMap.range H.mulVecLin ≤ P := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, hHv]
    exact P.add_mem (P.smul_mem _ hpP) (P.smul_mem _ hqP)
  refine ⟨g, H, ⟨0, 0, Bq, hgq⟩, hH, ?_, ?_⟩
  · exact (Submodule.finrank_mono hrH).trans hP2.le
  · have hAH : Rep (A + H) (fun u => f u + g u) := rep_add hA hH
    have hAHx : (A + H) *ᵥ x = 0 := by
      rw [add_mulVec, hHv, hqx, hpx]; simp only [one_smul, zero_smul, add_zero]
      exact vadd_self p
    have hAHy : (A + H) *ᵥ y = 0 := by
      rw [add_mulVec, hHv, hqy, hpy]; simp only [one_smul, zero_smul, zero_add]
      exact vadd_self q
    set W := LinearMap.range (A + H).mulVecLin
    set R := LinearMap.range A.mulVecLin
    have hWR : W ≤ R := by
      rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, add_mulVec, hHv]
      refine R.add_mem ⟨v, rfl⟩ (R.add_mem (R.smul_mem _ ⟨x, rfl⟩) (R.smul_mem _ ⟨y, rfl⟩))
    have hPR : P ≤ R := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · exact ⟨x, rfl⟩
      · exact ⟨y, rfl⟩
    have hWP : W ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨⟨v, hv⟩, hzP⟩
      obtain ⟨s, t, rfl⟩ := (mem_pair p q _).1 hzP
      rw [Matrix.mulVecLin_apply] at hv
      have hx0 : (s • p + t • q) ⬝ᵥ x = 0 := by
        rw [← hv, dotProduct_comm, rep_symm hAH, hAHx, dotProduct_zero]
      have hy0 : (s • p + t • q) ⬝ᵥ y = 0 := by
        rw [← hv, dotProduct_comm, rep_symm hAH, hAHy, dotProduct_zero]
      rw [(hsep s t).1] at hx0
      rw [(hsep s t).2] at hy0
      rw [hx0, hy0, zero_smul, zero_smul, add_zero]
      exact Submodule.zero_mem _
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W P
    rw [hWP, finrank_bot, add_zero, hP2] at hsum
    have hle := Submodule.finrank_mono (sup_le hWR hPR)
    have r1 : (A + H).rank = Module.finrank (ZMod 2) W := rfl
    have r2 : A.rank = Module.finrank (ZMod 2) R := rfl
    omega

theorem build {n r : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (d : (Fin n → ZMod 2) → ZMod 2)
    (hd : Rep M d) (hM : M.rank = 2 * r) : ∀ k ≤ r,
    ∃ (g : (Fin n → ZMod 2) → ZMod 2) (G : Matrix (Fin n) (Fin n) (ZMod 2)),
      IsQ g ∧ Rep G g ∧ G.rank ≤ 2 * k ∧ (M + G).rank ≤ 2 * r - 2 * k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => 0, 0, isq_zero, fun u v => by simp, by simp, by simp [hM]⟩
  | succ k ih =>
    intro hk
    obtain ⟨g, G, hg, hG, hGr, hMG⟩ := ih (by omega)
    have hsplit : M = G + (M + G) := by
      ext a b; simp only [Matrix.add_apply]
      rcases z2 (M a b) with e | e <;> rcases z2 (G a b) with e' | e' <;> rw [e, e'] <;> decide
    have hsub := rank_add G (M + G)
    rw [← hsplit] at hsub
    have hA : Rep (M + G) (fun u => d u + g u) := rep_add hd hG
    obtain ⟨g', H, hg', hH, hHr, hAH⟩ := peel (M + G) _ hA (by omega)
    refine ⟨fun u => g u + g' u, G + H, isq_add hg hg', rep_add hG hH, ?_, ?_⟩
    · have := rank_add G H; omega
    · rw [← add_assoc]; omega

end PEqualNP.Outside.L_lib_863

open PEqualNP.Outside.L_lib_863 in
theorem PEqualNP.Outside.L_lib_863 : ∀ (n r : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let quad := fun (q : V → F) =>
    ∃ (b : F) (a : V) (M : Fin n → Fin n → F), ∀ v,
      q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j
  ∀ (Q : Bool → V → F) (M : Matrix (Fin n) (Fin n) F), (∀ t, quad (Q t)) →
    let d := fun u : V => Q false u + Q true u
    M.rank = 2*r → (∀ u v, d (u+v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) →
    let agree := fun (q : V → F) (a : V) (b : F) (t : Bool) =>
      ∑ u : V, if Q t u = q u + (if t then dotProduct a u + b else 0) then (1 : ℤ) else -1
    (∀ (q : V → F) (a : V) (b : F), quad q →
      ∃ j ≤ r, 2^j * (agree q a b false).natAbs ≤ 2^n ∧
        2^(r-j) * (agree q a b true).natAbs ≤ 2^n) ∧
    ∀ j ≤ r, ∃ (q : V → F) (a : V) (b : F), quad q ∧
      (2 : ℤ)^j * agree q a b false = 2^n ∧
      (2 : ℤ)^(r-j) * agree q a b true = 2^n := by
  intro n r F V quad Q M hQ d hrank hpol agree
  have hd : Rep M d := hpol
  have hQ' : ∀ t, IsQ (Q t) := hQ
  have hrn : 2 * r ≤ n := hrank ▸ M.rank_le_width
  have hagf : ∀ q a b, agree q a b false = ∑ u, eps (Q false u + q u) := by
    intro q a b
    simp only [agree, Bool.false_eq_true, if_false, add_zero]
    apply Finset.sum_congr rfl; intro u _; exact if_congr (eq_iff_add _ _) rfl rfl
  have hagt : ∀ q a b, agree q a b true = ∑ u, eps (Q true u + (q u + (a ⬝ᵥ u + b))) := by
    intro q a b
    simp only [agree, if_true]
    apply Finset.sum_congr rfl; intro u _; exact if_congr (eq_iff_add _ _) rfl rfl
  refine ⟨?_, ?_⟩
  · intro q a b hq
    obtain ⟨N0, h0⟩ := quad_rep (hQ' false)
    obtain ⟨N1, h1⟩ := quad_rep (hQ' true)
    obtain ⟨Nq, hNq⟩ := quad_rep (hq : IsQ q)
    have hf : Rep (N0 + Nq) (fun u => Q false u + q u) := rep_add h0 hNq
    have ht : Rep (N1 + Nq) (fun u => Q true u + (q u + (a ⬝ᵥ u + b))) :=
      rep_congr (rep_aff (rep_add h1 hNq) a b) (fun u => by ring)
    have hsum : Rep ((N0 + Nq) + (N1 + Nq))
        (fun u => d u + (a ⬝ᵥ u + b)) := by
      refine rep_congr (rep_add hf ht) (fun u => ?_)
      simp only [d]
      linear_combination (-(q u)) * two0
    have hMe : M = (N0 + Nq) + (N1 + Nq) := rep_unique (rep_aff hd a b) hsum
    have hsub := rank_add (N0 + Nq) (N1 + Nq)
    rw [← hMe, hrank] at hsub
    have hwf := (N0 + Nq).rank_le_width
    have hwt := (N1 + Nq).rank_le_width
    rw [hagf, hagt]
    rcases abs_cases _ _ hf with ef | ⟨i, ei, hi⟩
    · refine ⟨r, le_rfl, ?_, ?_⟩
      · rw [ef]; simp
      · rw [Nat.sub_self, pow_zero, one_mul]
        rcases abs_cases _ _ ht with et | ⟨k, ek, hk⟩
        · rw [et]; simp
        · rw [ek]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · rcases abs_cases _ _ ht with et | ⟨k, ek, hk⟩
      · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
        · rw [ei, pow_zero, one_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        · rw [et]; simp
      · refine ⟨min r (n - i), min_le_left _ _, ?_, ?_⟩
        · rw [ei, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        · rw [ek, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro j hj
    obtain ⟨g, G, hg, hG, hGr, hMG⟩ := build M d hd hrank j hj
    have hsplit : M = G + (M + G) := by
      ext a b; simp only [Matrix.add_apply]
      rcases z2 (M a b) with e | e <;> rcases z2 (G a b) with e' | e' <;> rw [e, e'] <;> decide
    have hsub := rank_add G (M + G)
    rw [← hsplit, hrank] at hsub
    obtain ⟨a1, b1, hfit1⟩ := fit G g hG (c := j) (by omega)
    have hG1 : Rep G (fun u => g u + (a1 ⬝ᵥ u + b1)) := rep_aff hG a1 b1
    have hh : Rep (M + G) (fun u => d u + (g u + (a1 ⬝ᵥ u + b1))) := rep_add hd hG1
    obtain ⟨a, b, hfit2⟩ := fit (M + G) _ hh (c := r - j) (by omega)
    refine ⟨fun u => Q false u + (g u + (a1 ⬝ᵥ u + b1)), a, b,
      isq_add (hQ' false) (isq_add hg (isq_aff a1 b1)), ?_, ?_⟩
    · rw [hagf]
      have e : ∀ u, Q false u + (Q false u + (g u + (a1 ⬝ᵥ u + b1))) =
          g u + (a1 ⬝ᵥ u + b1) := by
        intro u; linear_combination (Q false u) * two0
      beta_reduce at hfit1
      simp only [e]
      rw [hfit1, ← pow_add]; congr 1; omega
    · rw [hagt]
      have e : ∀ u, Q true u + ((Q false u + (g u + (a1 ⬝ᵥ u + b1))) + (a ⬝ᵥ u + b)) =
          d u + (g u + (a1 ⬝ᵥ u + b1)) + (a ⬝ᵥ u + b) := by
        intro u; simp only [d]; ring
      beta_reduce at hfit2
      simp only [e]
      rw [hfit2, ← pow_add]; congr 1; omega
