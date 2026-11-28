import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_gct_303
open Finset Module
noncomputable section
abbrev V := Fin 5 → ℂ
def HH (U : Submodule ℂ V) : Prop := ∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0
def Concl (U : Submodule ℂ V) : Prop :=
  ∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val))
variable {U : Submodule ℂ V}
lemma fS (H : HH U) (π : Equiv.Perm (Fin 5)) {u : V} (hu : u ∈ U) :
    u (π 0) + u (π 1) + u (π 2) + u (π 3) + u (π 4) = 0 := by
  have h := (H u hu).1
  rw [← Equiv.sum_comp π u] at h
  simpa [Fin.sum_univ_five] using h
lemma fC (H : HH U) (π : Equiv.Perm (Fin 5)) {u : V} (hu : u ∈ U) :
    u (π 0)^3 + u (π 1)^3 + u (π 2)^3 + u (π 3)^3 + u (π 4)^3 = 0 := by
  have h := (H u hu).2
  rw [← Equiv.sum_comp π (fun j => u j ^ 3)] at h
  simpa [Fin.sum_univ_five] using h
lemma pol (H : HH U) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    (∑ j, x j ^ 2 * y j) = 0 := by
  have h1 := (H (x + y) (U.add_mem hx hy)).2
  have h2 := (H (x - y) (U.sub_mem hx hy)).2
  have h3 := (H y hy).2
  simp only [Pi.add_apply, Pi.sub_apply, Fin.sum_univ_five] at h1 h2 h3 ⊢
  linear_combination (h1 - h2 - 2 * h3) / 6
lemma fP (H : HH U) (π : Equiv.Perm (Fin 5)) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x (π 0)^2 * y (π 0) + x (π 1)^2 * y (π 1) + x (π 2)^2 * y (π 2) +
      x (π 3)^2 * y (π 3) + x (π 4)^2 * y (π 4) = 0 := by
  have h := pol H hx hy
  rw [← Equiv.sum_comp π (fun j => x j ^ 2 * y j)] at h
  simpa [Fin.sum_univ_five] using h
lemma GP (H : HH U) (π : Equiv.Perm (Fin 5)) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (x0 : x (π 0) = 1) (x1 : x (π 1) = -1) (x2 : x (π 2) = 0) (x3 : x (π 3) = 0)
    (x4 : x (π 4) = 0) (y0 : y (π 0) = 0) (y1 : y (π 1) = 0) (y2 : y (π 2) = 1)
    (y3 : y (π 3) = -1) (y4 : y (π 4) = 0) : Concl U := by
  refine ⟨π, Or.inl fun u => ⟨fun hu => ?_, fun ⟨s, t, h⟩ => ?_⟩⟩
  · have p1 := fP H π hx hu
    have p2 := fP H π hy hu
    have p3 := fS H π hu
    rw [x0, x1, x2, x3, x4] at p1
    rw [y0, y1, y2, y3, y4] at p2
    refine ⟨u (π 0), u (π 2), fun j => ?_⟩
    fin_cases j <;> simp <;> first | linear_combination p1 | linear_combination p2 | linear_combination p3 - p1 - p2
  · have e : u = s • x + t • y := by
      funext k
      obtain ⟨j, rfl⟩ := π.surjective k
      rw [h j]
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4]
    rw [e]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hy)
lemma GF (H : HH U) (π : Equiv.Perm (Fin 5)) (z : ℂ) (hz : IsPrimitiveRoot z 5)
    (hd : finrank ℂ U ≤ 2) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (x0 : x (π 0) = 2) (x1 : x (π 1) = z + z^4) (x2 : x (π 2) = z^2 + z^3)
    (x3 : x (π 3) = z^3 + z^2) (x4 : x (π 4) = z^4 + z)
    (y0 : y (π 0) = 0) (y1 : y (π 1) = z - z^4) (y2 : y (π 2) = z^2 - z^3)
    (y3 : y (π 3) = z^3 - z^2) (y4 : y (π 4) = z^4 - z) : Concl U := by
  have h5 : z ^ 5 = 1 := hz.pow_eq_one
  have e8 : z ^ 8 = z ^ 3 := by linear_combination z^3 * h5
  have e12 : z ^ 12 = z ^ 2 := by linear_combination (z^7 + z^2) * h5
  have e16 : z ^ 16 = z := by linear_combination (z^11 + z^6 + z) * h5
  refine ⟨π, Or.inr ⟨z, hz, fun u => ⟨fun hu => ?_, fun ⟨s, t, h⟩ => ?_⟩⟩⟩
  · have hne : z - z ^ 4 ≠ 0 := by
      intro e
      have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
      have e3 : z ^ 3 = 1 := by
        have : z * (z ^ 3 - 1) = 0 := by linear_combination -e
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hz0
        · linear_combination h
      exact hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) e3
    have hind : LinearIndependent ℂ ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have a0 := congrFun hst (π 0)
      have a1 := congrFun hst (π 1)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, x0, y0, x1, y1] at a0 a1
      have hs : s = 0 := by linear_combination a0 / 2
      subst hs
      refine ⟨rfl, ?_⟩
      have : t * (z - z ^ 4) = 0 := by linear_combination a1
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hne
    have hsp : Submodule.span ℂ (Set.range ![x, y]) = U := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hx
        · exact hy
      · rw [finrank_span_eq_card hind]; simpa using hd
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨c, hc⟩ := hu
    refine ⟨c 0 + c 1, c 0 - c 1, fun j => ?_⟩
    rw [← hc]
    fin_cases j <;> simp [Fin.sum_univ_two, x0, x1, x2, x3, x4, y0, y1, y2, y3, y4,
      e8, e12, e16] <;> ring
  · have e : u = ((s + t) / 2) • x + ((s - t) / 2) • y := by
      funext k
      obtain ⟨j, rfl⟩ := π.surjective k
      rw [h j]
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, e8, e12, e16] <;> ring
    rw [e]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hy)
lemma rev (U : Submodule ℂ V) (h : Concl U) : HH U := by
  obtain ⟨π, h⟩ := h
  intro u hu
  rw [← Equiv.sum_comp π u, ← Equiv.sum_comp π (fun j => u j ^ 3)]
  rcases h with h | ⟨z, hz, h⟩
  · obtain ⟨s, t, h⟩ := (h u).1 hu
    simp only [Fin.sum_univ_five, h]
    constructor <;> simp <;> ring
  · obtain ⟨s, t, h⟩ := (h u).1 hu
    have h5 : z ^ 5 = 1 := hz.pow_eq_one
    have e8 : z ^ 8 = z ^ 3 := by linear_combination z^3 * h5
    have e12 : z ^ 12 = z ^ 2 := by linear_combination (z^7 + z^2) * h5
    have e16 : z ^ 16 = z := by linear_combination (z^11 + z^6 + z) * h5
    have geo : 1 + z + z^2 + z^3 + z^4 = 0 := by
      have := hz.geom_sum_eq_zero (by norm_num : 1 < 5)
      simpa [Finset.sum_range_succ, add_assoc] using this
    simp only [Fin.sum_univ_five, h]
    simp [e8, e12, e16]
    constructor
    · linear_combination (s + t) * geo
    · linear_combination (s + t)^3 * geo + (3*z^1*s^2*t^1 + 3*z^4*s^1*t^2 + 1*z^7*s^0*t^3 +
        1*z^1*s^3*t^0 + 3*z^2*s^2*t^1 + 3*z^3*s^1*t^2 + 1*z^4*s^0*t^3 + 1*z^4*s^3*t^0 +
        3*z^3*s^2*t^1 + 3*z^2*s^1*t^2 + 1*z^1*s^0*t^3 + 1*z^7*s^3*t^0 + 3*z^4*s^2*t^1 +
        3*z^1*s^1*t^2 + 1*z^2*s^0*t^3 + 1*z^2*s^3*t^0) * h5
def mk5 (f g : Fin 5 → Fin 5) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) :
    Equiv.Perm (Fin 5) := ⟨f, g, h1, h2⟩
lemma mk5_apply (f g : Fin 5 → Fin 5) (h1 h2) (i : Fin 5) : mk5 f g h1 h2 i = f i := rfl
lemma tA0p (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (b : ℂ) (w0 : w (π 0) = 0) (w1 : w (π 1) = -0) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (r : ℂ)
    (v0 : v (π 0) = 0) (v1 : v (π 1) = -1) (v2 : v (π 2) = r) (v3 : v (π 3) = -r)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![4,1,2,3,0] ![4,1,2,3,0] (by decide) (by decide))
    (x := v - r • (b⁻¹ • w)) (y := b⁻¹ • w)
    (U.sub_mem hv (U.smul_mem _ (U.smul_mem _ hw))) (U.smul_mem _ hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, hb]
lemma tA0q (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (b : ℂ) (w0 : w (π 0) = 0) (w1 : w (π 1) = -0) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (r : ℂ)
    (v0 : v (π 0) = -1) (v1 : v (π 1) = 0) (v2 : v (π 2) = r) (v3 : v (π 3) = -r)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,4,2,3,1] ![0,4,2,3,1] (by decide) (by decide))
    (x := r • (b⁻¹ • w) - v) (y := b⁻¹ • w)
    (U.sub_mem (U.smul_mem _ (U.smul_mem _ hw)) hv) (U.smul_mem _ hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, hb]
lemma tB0r (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (a : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = 0) (w3 : w (π 3) = -0)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (v : V) (hv : v ∈ U) (p : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = -p) (v2 : v (π 2) = 0) (v3 : v (π 3) = -1)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,1,4,3,2] ![0,1,4,3,2] (by decide) (by decide))
    (x := a⁻¹ • w) (y := v - p • (a⁻¹ • w))
    (U.smul_mem _ hw) (U.sub_mem hv (U.smul_mem _ (U.smul_mem _ hw))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, ha]
lemma tB0s (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (a : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = 0) (w3 : w (π 3) = -0)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (v : V) (hv : v ∈ U) (p : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = -p) (v2 : v (π 2) = -1) (v3 : v (π 3) = 0)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,1,2,4,3] ![0,1,2,4,3] (by decide) (by decide))
    (x := a⁻¹ • w) (y := p • (a⁻¹ • w) - v)
    (U.smul_mem _ hw) (U.sub_mem (U.smul_mem _ (U.smul_mem _ hw)) hv) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, ha]
lemma alg1 (p q r s : ℂ) (hS : p + q + r + s + 1 = 0) (hT : r + s = 0)
    (hC : p^3 + q^3 + r^3 + s^3 + 1 = 0) : p = 0 ∨ q = 0 := by
  have hs : s = -r := by linear_combination hT
  subst hs
  have hq : q = -1 - p := by linear_combination hS
  subst hq
  have h : p * (-1 - p) = 0 := by linear_combination hC / 3
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr h
lemma alg2 (a b p r s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (E1 : a^2*p + a^2*p + b^2*r + b^2*s = 0) (E2 : b*r^2 - b*s^2 = 0)
    (S : p + p + r + s + 1 = 0) (C : p^3 + p^3 + r^3 + s^3 + 1 = 0) :
    r = s ∧ s = -1/2 - p ∧ 4*p^2 + 2*p - 1 = 0 ∧ (b = 2*p*a ∨ b = -(2*p*a)) := by
  have h1 : (r - s) * (r + s) = 0 := by
    have : b * ((r - s) * (r + s)) = 0 := by linear_combination E2
    exact (mul_eq_zero.1 this).resolve_left hb
  rcases mul_eq_zero.1 h1 with h | h
  · have hrs : r = s := by linear_combination h
    subst hrs
    have hs : r = -1/2 - p := by linear_combination S / 2
    subst hs
    have hQ : 4*p^2 + 2*p - 1 = 0 := by linear_combination (-4/3) * C
    refine ⟨rfl, rfl, hQ, ?_⟩
    have e : (b - 2*p*a) * (b + 2*p*a) * (1/2 + p) = 0 := by
      linear_combination (-1/2) * E1 - a^2 * p * hQ
    have hp : (1/2 + p) ≠ 0 := by
      intro e2
      have : p = -1/2 := by linear_combination e2
      subst this; norm_num at hQ
    rcases mul_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hp) with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · exfalso
    have : a^2 = 0 := by linear_combination -E1 + a^2 * S + (b^2 - a^2) * h
    exact ha (pow_eq_zero_iff (by norm_num) |>.1 this)
lemma CaseBgen (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (p r s : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = p) (v2 : v (π 2) = r) (v3 : v (π 3) = s)
    (v4 : v (π 4) = 1) : Concl U := by
  have E1 := fP H π hw hv
  have E2 := fP H π hv hw
  have S := fS H π hv
  have C := fC H π hv
  rw [w0, w1, w2, w3, w4, v0, v1, v2, v3, v4] at E1 E2
  rw [v0, v1, v2, v3, v4] at S C
  obtain ⟨hrs, hs, hQ, hb'⟩ := alg2 a b p r s ha hb (by linear_combination E1)
    (by linear_combination E2) (by linear_combination S) (by linear_combination C)
  obtain ⟨d, hd2⟩ := IsAlgClosed.exists_pow_nat_eq (p^2 - 1) (by norm_num : 0 < 2)
  have hzq : (p + d)^2 - 2*p*(p + d) + 1 = 0 := by linear_combination hd2
  generalize p + d = z at hzq
  have geo : 1 + z + z^2 + z^3 + z^4 = 0 := by
    linear_combination (z^2 + (1 + 2*p)*z + 2*p*(1 + 2*p)) * hzq + (2*p*z - 1) * hQ
  have h5 : z ^ 5 = 1 := by linear_combination (z - 1) * geo
  have hz1 : z ≠ 1 := by
    intro e; subst e; norm_num at geo
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz : IsPrimitiveRoot z 5 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime h5 hz1)
  have hm2 : 2*p = z + z^4 := by linear_combination (-z^4) * hzq + (z - 2*p) * h5
  have hca : ((z - z^4) * a⁻¹) * a = z - z^4 := by field_simp
  rcases hb' with hb' | hb'
  · refine GF H (π * mk5 ![4,0,2,3,1] ![1,4,2,3,0] (by decide) (by decide)) z hz hd
      (x := (2:ℂ) • v) (y := ((z - z^4) * a⁻¹) • w) (U.smul_mem _ hv) (U.smul_mem _ hw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mk5_apply, Equiv.Perm.mul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4]
    · norm_num
    · linear_combination hm2
    · linear_combination 2 * hrs + 2 * hs - hm2 - geo
    · linear_combination 2 * hs - hm2 - geo
    · linear_combination hm2
    · ring
    · linear_combination hca
    · linear_combination ((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5
    · linear_combination -(((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5)
    · linear_combination -hca
  · refine GF H (π * mk5 ![4,0,3,2,1] ![1,4,3,2,0] (by decide) (by decide)) z hz hd
      (x := (2:ℂ) • v) (y := ((z - z^4) * a⁻¹) • w) (U.smul_mem _ hv) (U.smul_mem _ hw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mk5_apply, Equiv.Perm.mul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4]
    · norm_num
    · linear_combination hm2
    · linear_combination 2 * hs - hm2 - geo
    · linear_combination 2 * hrs + 2 * hs - hm2 - geo
    · linear_combination hm2
    · ring
    · linear_combination hca
    · linear_combination -((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5
    · linear_combination ((z - z^4) * a⁻¹) * hb' - (2*p*hca + (z - z^4)*hm2 - z^3*h5)
    · linear_combination -hca
lemma CaseB1 (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hne : a ≠ 0 ∨ b ≠ 0) (v : V) (hv : v ∈ U) (p q r s : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = q) (v2 : v (π 2) = r) (v3 : v (π 3) = s)
    (v4 : v (π 4) = 1) : Concl U := by
  have E1 := fP H π hw hv
  have S := fS H π hv
  have C := fC H π hv
  rw [w0, w1, w2, w3, w4, v0, v1, v2, v3, v4] at E1
  rw [v0, v1, v2, v3, v4] at S C
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    have hb : b ≠ 0 := hne.resolve_left (by simp)
    have hrs : r + s = 0 := by
      have : b^2 * (r + s) = 0 := by linear_combination E1
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hb)
    rcases alg1 p q r s (by linear_combination S) hrs (by linear_combination C) with hp | hq
    · exact tA0p π H w hw b w0 w1 w2 w3 w4 hb v hv r (v0.trans hp)
        (by rw [v1]; linear_combination S - hp - hrs) v2 (by rw [v3]; linear_combination hrs) v4
    · exact tA0q π H w hw b w0 w1 w2 w3 w4 hb v hv r
        (by rw [v0]; linear_combination S - hq - hrs) (v1.trans hq) v2
        (by rw [v3]; linear_combination hrs) v4
  · by_cases hb : b = 0
    · subst hb
      have hpq : p + q = 0 := by
        have : a^2 * (p + q) = 0 := by linear_combination E1
        exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ ha)
      rcases alg1 r s p q (by linear_combination S) hpq (by linear_combination C) with hr | hs
      · exact tB0r π H w hw a w0 w1 w2 w3 w4 ha v hv p v0
          (by rw [v1]; linear_combination hpq) (v2.trans hr)
          (by rw [v3]; linear_combination S - hr - hpq) v4
      · exact tB0s π H w hw a w0 w1 w2 w3 w4 ha v hv p v0
          (by rw [v1]; linear_combination hpq)
          (by rw [v2]; linear_combination S - hs - hpq) (v3.trans hs) v4
    · have hvU : v + ((q - p) / (2 * a)) • w ∈ U := U.add_mem hv (U.smul_mem _ hw)
      refine CaseBgen π H hd w hw a b w0 w1 w2 w3 w4 ha hb _ hvU
        (p + (q - p) / (2 * a) * a) (r + (q - p) / (2 * a) * b) (s + (q - p) / (2 * a) * (-b))
        ?_ ?_ ?_ ?_ ?_
      all_goals simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w0, w1, w2, w3, w4,
        v0, v1, v2, v3, v4]
      · field_simp; ring
      · simp
lemma CaseB (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hne : a ≠ 0 ∨ b ≠ 0) (v : V) (hv : v ∈ U) (hv4 : v (π 4) ≠ 0) :
    Concl U := by
  have hvU : (v (π 4))⁻¹ • v ∈ U := U.smul_mem _ hv
  exact CaseB1 π H hd w hw a b w0 w1 w2 w3 w4 hne _ hvU _ _ _ _ rfl rfl rfl rfl
    (by simp [hv4])
lemma CaseA (π : Equiv.Perm (Fin 5)) (H : HH U) (x : V) (hx : x ∈ U)
    (a b : ℂ) (x0 : x (π 0) = a) (x1 : x (π 1) = -a) (x2 : x (π 2) = b) (x3 : x (π 3) = -b)
    (x4 : x (π 4) = 0) (y : V) (hy : y ∈ U)
    (a' b' : ℂ) (y0 : y (π 0) = a') (y1 : y (π 1) = -a') (y2 : y (π 2) = b') (y3 : y (π 3) = -b')
    (y4 : y (π 4) = 0) (hind : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) : Concl U := by
  have hdet : a * b' - a' * b ≠ 0 := by
    intro hd0
    have k1 := hind b' (-b) (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4] <;>
        first | linear_combination hd0 | linear_combination -hd0 | ring)
    have k2 := hind a' (-a) (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4] <;>
        first | linear_combination hd0 | linear_combination -hd0 | ring)
    have hb : b = 0 := by linear_combination -k1.2
    have ha : a = 0 := by linear_combination -k2.2
    have k3 := hind 1 0 (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, ha, hb])
    exact one_ne_zero k3.1
  refine GP H π (x := (a * b' - a' * b)⁻¹ • (b' • x - b • y))
    (y := (a * b' - a' * b)⁻¹ • (a • y - a' • x))
    (U.smul_mem _ (U.sub_mem (U.smul_mem _ hx) (U.smul_mem _ hy)))
    (U.smul_mem _ (U.sub_mem (U.smul_mem _ hy) (U.smul_mem _ hx))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, x0, x1, x2, x3, x4,
    y0, y1, y2, y3, y4]
  all_goals field_simp
  all_goals ring
lemma fac (H : HH U) {x : V} (hx : x ∈ U) (x4 : x 4 = 0) :
    (x 0 + x 1) * (x 0 + x 2) * (x 0 + x 3) = 0 := by
  have S := (H x hx).1
  have C := (H x hx).2
  simp only [Fin.sum_univ_five, x4] at S C
  have h3 : x 3 = -(x 0 + x 1 + x 2) := by linear_combination S
  rw [h3] at C ⊢
  linear_combination C / 3
lemma two {α β : ℂ} (l m : ℂ) (hlm : l ≠ m) (h1 : α + l * β = 0) (h2 : α + m * β = 0) :
    α = 0 ∧ β = 0 := by
  have hb : β = 0 := by
    have : (l - m) * β = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hlm)
  subst hb
  exact ⟨by linear_combination h1, rfl⟩
lemma pig (α1 β1 α2 β2 α3 β3 : ℂ)
    (F : ∀ l : ℂ, (α1 + l * β1) * (α2 + l * β2) * (α3 + l * β3) = 0) :
    (α1 = 0 ∧ β1 = 0) ∨ (α2 = 0 ∧ β2 = 0) ∨ (α3 = 0 ∧ β3 = 0) := by
  have e0 := F 0
  have e1 := F 1
  have e2 := F 2
  have e3 := F 3
  simp only [mul_eq_zero] at e0 e1 e2 e3
  rcases e0 with (a0 | b0) | c0 <;> rcases e1 with (a1 | b1) | c1 <;>
    rcases e2 with (a2 | b2) | c2 <;> rcases e3 with (a3 | b3) | c3 <;>
    first
    | exact Or.inl (two 0 1 (by norm_num) a0 a1)
    | exact Or.inl (two 0 2 (by norm_num) a0 a2)
    | exact Or.inl (two 0 3 (by norm_num) a0 a3)
    | exact Or.inl (two 1 2 (by norm_num) a1 a2)
    | exact Or.inl (two 1 3 (by norm_num) a1 a3)
    | exact Or.inl (two 2 3 (by norm_num) a2 a3)
    | exact Or.inr (Or.inl (two 0 1 (by norm_num) b0 b1))
    | exact Or.inr (Or.inl (two 0 2 (by norm_num) b0 b2))
    | exact Or.inr (Or.inl (two 0 3 (by norm_num) b0 b3))
    | exact Or.inr (Or.inl (two 1 2 (by norm_num) b1 b2))
    | exact Or.inr (Or.inl (two 1 3 (by norm_num) b1 b3))
    | exact Or.inr (Or.inl (two 2 3 (by norm_num) b2 b3))
    | exact Or.inr (Or.inr (two 0 1 (by norm_num) c0 c1))
    | exact Or.inr (Or.inr (two 0 2 (by norm_num) c0 c2))
    | exact Or.inr (Or.inr (two 0 3 (by norm_num) c0 c3))
    | exact Or.inr (Or.inr (two 1 2 (by norm_num) c1 c2))
    | exact Or.inr (Or.inr (two 1 3 (by norm_num) c1 c3))
    | exact Or.inr (Or.inr (two 2 3 (by norm_num) c2 c3))
lemma killG {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (X : Submodule ℂ M) {n : ℕ} (φ : M →ₗ[ℂ] (Fin n → ℂ)) (h : n < finrank ℂ X) :
    ∃ v ∈ X, v ≠ 0 ∧ φ v = 0 := by
  let ψ := φ.domRestrict X
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 : finrank ℂ (LinearMap.range ψ) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range ψ); simpa using this
  have h3 : LinearMap.ker ψ ≠ ⊥ := by
    intro e; rw [e, finrank_bot] at h1; omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨w.1, w.2, fun e => hw0 (Subtype.ext e), ?_⟩
  have : ψ w = 0 := hw
  simpa [ψ] using this
def Q12 : Equiv.Perm (Fin 5) := mk5 ![0,2,1,3,4] ![0,2,1,3,4] (by decide) (by decide)
def Q13 : Equiv.Perm (Fin 5) := mk5 ![0,3,2,1,4] ![0,3,2,1,4] (by decide) (by decide)
lemma nzf (π : Equiv.Perm (Fin 5)) (w : V) (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a)
    (w2 : w (π 2) = b) (w3 : w (π 3) = -b) (w4 : w (π 4) = 0) (hw : w ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  funext k
  obtain ⟨j, rfl⟩ := π.surjective k
  fin_cases j <;> simp [w0, w1, w2, w3, w4, h.1, h.2]
lemma topB (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U) (hw0 : w ≠ 0)
    (w4 : w 4 = 0) (v : V) (hv : v ∈ U) (hv4 : v 4 ≠ 0) : Concl U := by
  have S := (H w hw).1
  simp only [Fin.sum_univ_five, w4] at S
  rcases mul_eq_zero.1 (fac H hw w4) with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have w0 : w ((1 : Equiv.Perm (Fin 5)) 0) = w 0 := rfl
      have w1 : w ((1 : Equiv.Perm (Fin 5)) 1) = -(w 0) := by
        show w 1 = _; linear_combination h
      have w2 : w ((1 : Equiv.Perm (Fin 5)) 2) = w 2 := rfl
      have w3 : w ((1 : Equiv.Perm (Fin 5)) 3) = -(w 2) := by
        show w 3 = _; linear_combination S - h
      have w4' : w ((1 : Equiv.Perm (Fin 5)) 4) = 0 := w4
      exact CaseB 1 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf 1 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
    · have w0 : w (Q12 0) = w 0 := rfl
      have w1 : w (Q12 1) = -(w 0) := by
        show w 2 = _; linear_combination h
      have w2 : w (Q12 2) = w 1 := rfl
      have w3 : w (Q12 3) = -(w 1) := by
        show w 3 = _; linear_combination S - h
      have w4' : w (Q12 4) = 0 := w4
      exact CaseB Q12 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf Q12 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
  · have w0 : w (Q13 0) = w 0 := rfl
    have w1 : w (Q13 1) = -(w 0) := by
      show w 3 = _; linear_combination h
    have w2 : w (Q13 2) = w 2 := rfl
    have w3 : w (Q13 3) = -(w 2) := by
      show w 1 = _; linear_combination S - h
    have w4' : w (Q13 4) = 0 := w4
    exact CaseB Q13 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf Q13 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
lemma topA (H : HH U) (x : V) (hx : x ∈ U) (x4 : x 4 = 0) (y : V) (hy : y ∈ U) (y4 : y 4 = 0)
    (hind : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) : Concl U := by
  have Sx := (H x hx).1
  have Sy := (H y hy).1
  simp only [Fin.sum_univ_five, x4, y4] at Sx Sy
  have F : ∀ l : ℂ, ((x 0 + x 1) + l * (y 0 + y 1)) * ((x 0 + x 2) + l * (y 0 + y 2)) *
      ((x 0 + x 3) + l * (y 0 + y 3)) = 0 := by
    intro l
    have := fac H (U.add_mem hx (U.smul_mem l hy)) (by simp [x4, y4])
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  rcases pig _ _ _ _ _ _ F with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact CaseA 1 H x hx (x 0) (x 2) rfl (by show x 1 = _; linear_combination h) rfl
      (by show x 3 = _; linear_combination Sx - h) x4 y hy (y 0) (y 2) rfl
      (by show y 1 = _; linear_combination h') rfl
      (by show y 3 = _; linear_combination Sy - h') y4 hind
  · exact CaseA Q12 H x hx (x 0) (x 1) rfl (by show x 2 = _; linear_combination h) rfl
      (by show x 3 = _; linear_combination Sx - h) x4 y hy (y 0) (y 1) rfl
      (by show y 2 = _; linear_combination h') rfl
      (by show y 3 = _; linear_combination Sy - h') y4 hind
  · exact CaseA Q13 H x hx (x 0) (x 2) rfl (by show x 3 = _; linear_combination h) rfl
      (by show x 1 = _; linear_combination Sx - h) x4 y hy (y 0) (y 2) rfl
      (by show y 3 = _; linear_combination h') rfl
      (by show y 1 = _; linear_combination Sy - h') y4 hind
lemma fwd (U : Submodule ℂ V) (hd : 2 ≤ finrank ℂ U) (H : HH U) : Concl U := by
  obtain ⟨b0, hb0, hb00, e0⟩ :=
    killG U (LinearMap.pi ![(LinearMap.proj 4 : V →ₗ[ℂ] ℂ)]) (by omega)
  have hb04 : b0 4 = 0 := by simpa using congrFun e0 0
  obtain ⟨k, hk⟩ : ∃ k, b0 k ≠ 0 := by
    by_contra h; push_neg at h; exact hb00 (funext h)
  by_cases hA : ∃ b1 ∈ U, b1 ≠ 0 ∧ b1 4 = 0 ∧ b1 k = 0
  · obtain ⟨b1, hb1, hb10, hb14, hb1k⟩ := hA
    refine topA H b0 hb0 hb04 b1 hb1 hb14 fun s t hst => ?_
    have e := congrFun hst k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb1k, mul_zero, add_zero,
      Pi.zero_apply] at e
    have hs : s = 0 := (mul_eq_zero.1 e).resolve_right hk
    subst hs
    refine ⟨rfl, ?_⟩
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    exact hst.resolve_right hb10
  · push_neg at hA
    have hd2 : finrank ℂ U ≤ 2 := by
      by_contra h3; push_neg at h3
      obtain ⟨b1, hb1, hb10, e⟩ := killG U (LinearMap.pi ![(LinearMap.proj 4 : V →ₗ[ℂ] ℂ),
        (LinearMap.proj k : V →ₗ[ℂ] ℂ)]) (by omega)
      exact hA b1 hb1 hb10 (by simpa using congrFun e 0) (by simpa using congrFun e 1)
    have hv : ∃ v ∈ U, v 4 ≠ 0 := by
      by_contra hv; push_neg at hv
      obtain ⟨b1, hb1, hb10, e⟩ :=
        killG U (LinearMap.pi ![(LinearMap.proj k : V →ₗ[ℂ] ℂ)]) (by omega)
      exact hA b1 hb1 hb10 (hv b1 hb1) (by simpa using congrFun e 0)
    obtain ⟨v, hv, hv4⟩ := hv
    exact topB H hd2 b0 hb0 hb00 hb04 v hv hv4
end
end PEqualNP.Outside.L_gct_303
open PEqualNP.Outside.L_gct_303 in
theorem PEqualNP.Outside.L_gct_303 : ∀ U : Submodule ℂ (Fin 5 → ℂ), 2 ≤ Module.finrank ℂ U →
  ((∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0) ↔
    ∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val))) := by
  intro U hd
  exact ⟨fwd U hd, rev U⟩
