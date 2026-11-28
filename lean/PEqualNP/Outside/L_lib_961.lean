import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_961

open Finset

def tau (c3 D : ℚ) {q : ℕ} (a z : Fin q) : ℚ := if a = z then -c3 / D else 1 / D
def mu (c3 D : ℚ) {q : ℕ} (a z : Fin q) : ℚ := if a = z then c3 / D else 1 / D
def phi (c3 D : ℚ) {q : ℕ} (a b c z : Fin q) : ℚ :=
  tau c3 D a z * tau c3 D b z / mu c3 D c z
def G (c3 D : ℚ) {q : ℕ} (a b c : Fin q) : ℚ := ∑ z, phi c3 D a b c z
def H (K : ℚ) {q : ℕ} (a b c : Fin q) : ℚ :=
  if a = c then (if b = c then 1 else 0) else (if b = c then 0 else K)
def e (b : Bool) : ℚ := if b then -1 else 1

theorem e_sq (b : Bool) : e b * e b = 1 := by cases b <;> simp [e]

theorem sum_one {q : ℕ} (a : Fin q) (α γ : ℚ) (F : Fin q → ℚ)
    (hF : ∀ z, F z = if z = a then α else γ) :
    ∑ z, F z = q * γ + (α - γ) := by
  have h : ∀ z, F z = γ + (if a = z then α - γ else 0) := by
    intro z; rw [hF z]
    by_cases h1 : z = a
    · rw [if_pos h1, if_pos h1.symm]; ring
    · rw [if_neg h1, if_neg (fun h => h1 h.symm)]; ring
  rw [Finset.sum_congr rfl (fun z _ => h z)]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, nsmul_eq_mul]

theorem sum_two {q : ℕ} (a b : Fin q) (hab : a ≠ b) (α β γ : ℚ) (F : Fin q → ℚ)
    (hF : ∀ z, F z = if z = a then α else if z = b then β else γ) :
    ∑ z, F z = q * γ + (α - γ) + (β - γ) := by
  have h : ∀ z, F z = γ + (if a = z then α - γ else 0) + (if b = z then β - γ else 0) := by
    intro z; rw [hF z]
    by_cases h1 : z = a
    · rw [if_pos h1, if_pos h1.symm, if_neg (fun h => hab (h1.symm.trans h.symm))]; ring
    · by_cases h2 : z = b
      · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.symm), if_pos h2.symm]; ring
      · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm)]
        ring
  rw [Finset.sum_congr rfl (fun z _ => h z)]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, nsmul_eq_mul]

theorem G_symm {q : ℕ} (c3 D : ℚ) (a b c : Fin q) : G c3 D a b c = G c3 D b a c := by
  unfold G phi; apply Finset.sum_congr rfl; intro z _; ring

section vals
variable {q : ℕ} (c3 D : ℚ) (hc : 1 ≤ c3) (hD : 0 < D) (hrel : c3 = (q : ℚ) - 3)
  (hDr : D = 2 * ((q : ℚ) - 2))
include hc hD

theorem G_ccc (hrel : c3 = (q : ℚ) - 3) (hDr : D = 2 * ((q : ℚ) - 2)) (c : Fin q) :
    G c3 D c c c = 1 := by
  have hc0 : c3 ≠ 0 := by linarith
  have hD0 : D ≠ 0 := hD.ne'
  unfold G
  rw [sum_one c (c3 / D) (1 / D)]
  · have e1 : (q : ℚ) * (1 / D) + (c3 / D - 1 / D) = ((q : ℚ) + c3 - 1) / D := by ring
    rw [e1, div_eq_one_iff_eq hD0, hDr, hrel]; ring
  · intro z
    by_cases h : z = c
    · have h' : c = z := h.symm
      rw [if_pos h]; unfold phi tau mu; rw [if_pos h', if_pos h']; field_simp
    · have h' : ¬ c = z := fun h'' => h h''.symm
      rw [if_neg h]; unfold phi tau mu; rw [if_neg h', if_neg h']; field_simp

theorem G_cbc (hrel : c3 = (q : ℚ) - 3) (c b : Fin q) (hb : b ≠ c) :
    G c3 D c b c = 0 := by
  have hc0 : c3 ≠ 0 := by linarith
  have hD0 : D ≠ 0 := hD.ne'
  unfold G
  rw [sum_two c b (fun h => hb h.symm) (-1 / D) (-c3 / D) (1 / D)]
  · have e1 : (q : ℚ) * (1 / D) + (-1 / D - 1 / D) + (-c3 / D - 1 / D) =
        ((q : ℚ) - 3 - c3) / D := by ring
    rw [e1, hrel]; simp
  · intro z
    by_cases h : z = c
    · have h' : c = z := h.symm
      have hbz : ¬ b = z := fun h'' => hb (h''.trans h)
      rw [if_pos h]; unfold phi tau mu; rw [if_pos h', if_pos h', if_neg hbz]; field_simp
    · have h' : ¬ c = z := fun h'' => h h''.symm
      rw [if_neg h]
      by_cases h2 : z = b
      · have h2' : b = z := h2.symm
        rw [if_pos h2]; unfold phi tau mu; rw [if_neg h', if_neg h', if_pos h2']; field_simp
      · have h2' : ¬ b = z := fun h'' => h2 h''.symm
        rw [if_neg h2]; unfold phi tau mu; rw [if_neg h', if_neg h', if_neg h2']; field_simp

theorem abs_tau (a z : Fin q) : |tau c3 D a z| ≤ c3 / D := by
  unfold tau
  split_ifs
  · rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hD.le)]
  · rw [abs_of_nonneg (div_nonneg (by norm_num) hD.le)]
    exact div_le_div_of_nonneg_right hc hD.le

theorem mu_ge (a z : Fin q) : 1 / D ≤ mu c3 D a z := by
  unfold mu
  split_ifs
  · exact div_le_div_of_nonneg_right hc hD.le
  · exact le_refl _

theorem abs_phi (a b c z : Fin q) : |phi c3 D a b c z| ≤ c3 ^ 2 / D := by
  unfold phi
  have h1 := abs_tau c3 D hc hD a z
  have h2 := abs_tau c3 D hc hD b z
  have h3 := mu_ge c3 D hc hD c z
  have hp : 0 < 1 / D := by positivity
  have hm : 0 < mu c3 D c z := lt_of_lt_of_le hp h3
  rw [abs_div, abs_mul, abs_of_pos hm]
  calc |tau c3 D a z| * |tau c3 D b z| / mu c3 D c z
      ≤ (c3 / D) * (c3 / D) / mu c3 D c z := by
        apply div_le_div_of_nonneg_right _ hm.le
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ (c3 / D) * (c3 / D) / (1 / D) := by
        apply div_le_div_of_nonneg_left (by positivity) hp h3
    _ = c3 ^ 2 / D := by field_simp

theorem abs_G (a b c : Fin q) : |G c3 D a b c| ≤ q * (c3 ^ 2 / D) := by
  unfold G
  calc |∑ z, phi c3 D a b c z| ≤ ∑ z, |phi c3 D a b c z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : Fin q, c3 ^ 2 / D := Finset.sum_le_sum (fun z _ => abs_phi c3 D hc hD a b c z)
    _ = q * (c3 ^ 2 / D) := by simp

theorem G_le_H (hrel : c3 = (q : ℚ) - 3) (hDr : D = 2 * ((q : ℚ) - 2)) (a b c : Fin q) :
    |G c3 D a b c| ≤ H (q * (c3 ^ 2 / D)) a b c := by
  unfold H
  by_cases ha : a = c
  · subst ha
    by_cases hb : b = a
    · subst hb; rw [if_pos rfl, if_pos rfl, G_ccc c3 D hc hD hrel hDr]; simp
    · rw [if_pos rfl, if_neg hb, G_cbc c3 D hc hD hrel a b hb]; simp
  · rw [if_neg ha]
    by_cases hb : b = c
    · subst hb; rw [if_pos rfl, G_symm c3 D, G_cbc c3 D hc hD hrel b a ha]; simp
    · rw [if_neg hb]; exact abs_G c3 D hc hD a b c

end vals

theorem sum_H {q : ℕ} (K : ℚ) (a c : Fin q) :
    ∑ b, H K a b c = if a = c then 1 else ((q : ℚ) - 1) * K := by
  by_cases ha : a = c
  · rw [if_pos ha, sum_one c 1 0]
    · ring
    · intro z; unfold H; rw [if_pos ha]
  · rw [if_neg ha, sum_one c 0 K]
    · ring
    · intro z; unfold H; rw [if_neg ha]

theorem H_nonneg {q : ℕ} (K : ℚ) (hK : 0 ≤ K) (a b c : Fin q) : 0 ≤ H K a b c := by
  unfold H; split_ifs <;> linarith

theorem prodsum {m q : ℕ} (f : Fin m → Fin q → ℚ) :
    ∑ y : Fin m → Fin q, ∏ i, f i (y i) = ∏ i, ∑ z, f i z := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem prod_ite_pow {m : ℕ} (P : Fin m → Prop) [DecidablePred P] (c : ℚ) :
    ∏ i, (if P i then c else 1) = c ^ (univ.filter P).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem neg_one_pow_e (n : ℕ) : (-1 : ℚ) ^ n = e (n % 2 == 1) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]; have := Nat.even_iff.mp h; simp [e, this]
  · rw [h.neg_one_pow]; have := Nat.odd_iff.mp h; simp [e, this]

theorem sign_term (g l r : Bool) (n : ℕ) (M : ℚ) :
    (if g = xor (xor l r) (n % 2 == 1) then M else -M) =
      e g * e r * (e l * ((-1) ^ n * M)) := by
  rw [neg_one_pow_e]
  generalize (n % 2 == 1) = d
  cases g <;> cases l <;> cases r <;> cases d <;> simp [e]

def eqc {m q : ℕ} (x y : Fin m → Fin q) : ℕ := (univ.filter (fun i => x i = y i)).card
def massq (q m n : ℕ) : ℚ := (((q-3)^n : ℕ) : ℚ) / (((2*(q-2))^m : ℕ) : ℚ)
def T {m q : ℕ} (c3 D : ℚ) (x y : Fin m → Fin q) : ℚ := ∏ i, tau c3 D (x i) (y i)
def P {m q : ℕ} (c3 D : ℚ) (v y : Fin m → Fin q) : ℚ := ∏ i, mu c3 D (v i) (y i)
def C {m q : ℕ} (c3 D : ℚ) (S : Finset (Fin m → Fin q)) (left : (Fin m → Fin q) → Bool)
    (y : Fin m → Fin q) : ℚ := ∑ x ∈ S, e (left x) * T c3 D x y

theorem T_eq {m q : ℕ} (c3 D : ℚ) (hc3d : c3 = ((q-3 : ℕ) : ℚ)) (hDd : D = ((2*(q-2) : ℕ) : ℚ))
    (x y : Fin m → Fin q) :
    (-1) ^ (eqc x y) * massq q m (eqc x y) = T c3 D x y := by
  have ht : ∀ a z : Fin q, tau c3 D a z = (if a = z then -c3 else 1) / D := by
    intro a z; unfold tau; split_ifs <;> ring
  unfold T massq eqc
  simp only [ht]
  rw [Finset.prod_div_distrib, prod_ite_pow, Finset.prod_const, card_univ, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_pow, ← hc3d, ← hDd, neg_pow]
  ring

theorem P_eq {m q : ℕ} (c3 D : ℚ) (hc3d : c3 = ((q-3 : ℕ) : ℚ)) (hDd : D = ((2*(q-2) : ℕ) : ℚ))
    (v y : Fin m → Fin q) :
    massq q m (eqc v y) = P c3 D v y := by
  have ht : ∀ a z : Fin q, mu c3 D a z = (if a = z then c3 else 1) / D := by
    intro a z; unfold mu; split_ifs <;> ring
  unfold P massq eqc
  simp only [ht]
  rw [Finset.prod_div_distrib, prod_ite_pow, Finset.prod_const, card_univ, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_pow, ← hc3d, ← hDd]

theorem abs_ee (a b : Bool) : |e a * e b| = 1 := by cases a <;> cases b <;> simp [e]

theorem main (q m R : ℕ) (hq : 5 ≤ q) (v : Fin m → Fin q) (S : Finset (Fin m → Fin q))
    (hS : ∀ x ∈ S, m - eqc x v ≤ R) (left right guess : (Fin m → Fin q) → Bool) :
    (∑ x ∈ S, ∑ y : Fin m → Fin q,
      if guess y = xor (xor (left x) (right y)) (eqc x y % 2 == 1)
      then massq q m (eqc x y) else -(massq q m (eqc x y))) ^ 2
      ≤ (S.card : ℚ) * (((q-1)^R * (q-3)^(2*R) : ℕ) : ℚ) := by
  obtain ⟨c3, hc3d⟩ : ∃ c : ℚ, c = ((q-3 : ℕ) : ℚ) := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ c : ℚ, c = ((2*(q-2) : ℕ) : ℚ) := ⟨_, rfl⟩
  have hrel : c3 = (q:ℚ) - 3 := by rw [hc3d, Nat.cast_sub (by omega)]; norm_num
  have hDr : D = 2 * ((q:ℚ) - 2) := by rw [hDd, Nat.cast_mul, Nat.cast_sub (by omega)]; norm_num
  have hq' : (5:ℚ) ≤ q := by exact_mod_cast hq
  have hc : 1 ≤ c3 := by rw [hrel]; linarith
  have hD : 0 < D := by rw [hDr]; linarith
  have hD0 : D ≠ 0 := hD.ne'
  -- rewrite the gain
  have hgain : (∑ x ∈ S, ∑ y : Fin m → Fin q,
      if guess y = xor (xor (left x) (right y)) (eqc x y % 2 == 1)
      then massq q m (eqc x y) else -(massq q m (eqc x y))) =
      ∑ y, e (guess y) * e (right y) * C c3 D S left y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    unfold C; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    rw [sign_term, T_eq c3 D hc3d hDd]
  rw [hgain]
  -- positivity and total mass of the reference law
  have hmu : ∀ a z : Fin q, 0 < mu c3 D a z := by
    intro a z; unfold mu; split_ifs
    · exact div_pos (by linarith) hD
    · exact div_pos one_pos hD
  have hPpos : ∀ y, 0 < P c3 D v y := fun y => Finset.prod_pos (fun i _ => hmu _ _)
  have hPsum : ∑ y, P c3 D v y = 1 := by
    unfold P; rw [prodsum]
    apply Finset.prod_eq_one; intro i _
    rw [sum_one (v i) (c3 / D) (1 / D)]
    · have e1 : (q : ℚ) * (1 / D) + (c3 / D - 1 / D) = ((q : ℚ) + c3 - 1) / D := by ring
      rw [e1, div_eq_one_iff_eq hD0, hDr, hrel]; ring
    · intro z; unfold mu
      by_cases h : z = v i
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have ht := Finset.sq_sum_div_le_sum_sq_div univ
    (fun y => e (guess y) * e (right y) * C c3 D S left y) (g := P c3 D v)
    (fun y _ => hPpos y)
  rw [hPsum, div_one] at ht
  refine le_trans ht ?_
  have hsq : ∀ y, (e (guess y) * e (right y) * C c3 D S left y) ^ 2 = C c3 D S left y ^ 2 := by
    intro y
    have h1 := e_sq (guess y); have h2 := e_sq (right y)
    calc (e (guess y) * e (right y) * C c3 D S left y) ^ 2
        = (e (guess y) * e (guess y)) * (e (right y) * e (right y)) * C c3 D S left y ^ 2 := by
          ring
      _ = C c3 D S left y ^ 2 := by rw [h1, h2]; ring
  simp only [hsq]
  -- expand the square
  have hexp : ∀ y, C c3 D S left y ^ 2 / P c3 D v y = ∑ x ∈ S, ∑ x' ∈ S,
      e (left x) * e (left x') * ∏ i, phi c3 D (x i) (x' i) (v i) (y i) := by
    intro y; unfold C
    rw [sq, Finset.sum_mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro x' _
    unfold T P phi
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hexp y), Finset.sum_comm]
  have hexp2 : ∀ x ∈ S, (∑ y : Fin m → Fin q, ∑ x' ∈ S,
      e (left x) * e (left x') * ∏ i, phi c3 D (x i) (x' i) (v i) (y i)) =
      ∑ x' ∈ S, e (left x) * e (left x') * ∏ i, G c3 D (x i) (x' i) (v i) := by
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x' _
    rw [← Finset.mul_sum, prodsum]
    rfl
  rw [Finset.sum_congr rfl hexp2]
  -- bound each row
  set K : ℚ := (q : ℚ) * (c3 ^ 2 / D) with hKd
  have hK1 : 1 ≤ K := by
    rw [hKd, ← mul_div_assoc, one_le_div hD, hDr]; nlinarith
  have hKc : K ≤ c3 ^ 2 := by
    rw [hKd, ← mul_div_assoc, div_le_iff₀ hD, hDr]; nlinarith
  set L : ℚ := ((q : ℚ) - 1) * K with hLd
  have hL1 : 1 ≤ L := by rw [hLd]; nlinarith
  have hrow : ∀ x ∈ S, (∑ x' ∈ S, e (left x) * e (left x') * ∏ i, G c3 D (x i) (x' i) (v i))
      ≤ L ^ R := by
    intro x hx
    calc (∑ x' ∈ S, e (left x) * e (left x') * ∏ i, G c3 D (x i) (x' i) (v i))
        ≤ ∑ x' ∈ S, ∏ i, H K (x i) (x' i) (v i) := by
          apply Finset.sum_le_sum; intro x' _
          refine le_trans (le_abs_self _) ?_
          rw [abs_mul, abs_ee, one_mul, Finset.abs_prod]
          apply Finset.prod_le_prod₀
          · intro i _; exact abs_nonneg _
          · intro i _; exact G_le_H c3 D hc hD hrel hDr _ _ _
      _ ≤ ∑ x' : Fin m → Fin q, ∏ i, H K (x i) (x' i) (v i) :=
          Finset.sum_le_univ_sum_of_nonneg
            (fun x' => Finset.prod_nonneg (fun i _ => H_nonneg K (by linarith) _ _ _))
      _ = ∏ i, (if x i = v i then 1 else L) := by
          rw [prodsum (fun i b => H K (x i) b (v i))]
          apply Finset.prod_congr rfl; intro i _
          rw [sum_H]
      _ = L ^ (univ.filter (fun i => ¬ x i = v i)).card := by
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      _ ≤ L ^ R := by
          apply pow_le_pow_right₀ hL1
          have h1 := hS x hx
          have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
            (fun i => x i = v i)
          rw [card_univ, Fintype.card_fin] at h2
          unfold eqc at h1
          omega
  calc (∑ x ∈ S, ∑ x' ∈ S, e (left x) * e (left x') * ∏ i, G c3 D (x i) (x' i) (v i))
      ≤ ∑ _x ∈ S, L ^ R := Finset.sum_le_sum hrow
    _ = (S.card : ℚ) * L ^ R := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℚ) * (((q : ℚ) - 1) * c3 ^ 2) ^ R := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply pow_le_pow_left₀ (by linarith)
        rw [hLd]; apply mul_le_mul_of_nonneg_left hKc; linarith
    _ = (S.card : ℚ) * (((q-1)^R * (q-3)^(2*R) : ℕ) : ℚ) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ← hc3d, Nat.cast_sub (by omega : 1 ≤ q),
          Nat.cast_one, mul_pow, pow_mul]

end PEqualNP.Outside.L_lib_961

open PEqualNP.Outside.L_lib_961 in
theorem PEqualNP.Outside.L_lib_961 : ∀ (q m R : Nat), 5 ≤ q →
  let W := Fin m → Fin q
  let eqs := fun (x y : W) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card
  let mass := fun (x y : W) => (((q-3)^(eqs x y) : Nat) : ℚ) /
    (((2*(q-2))^m : Nat) : ℚ)
  ∀ (v : W) (S : Finset W), (∀ x ∈ S, m-eqs x v ≤ R) →
    ∀ (left right guess : W → Bool),
      let gain := ∑ x ∈ S, ∑ y : W,
        if guess y = xor (xor (left x) (right y)) (eqs x y % 2 == 1)
        then mass x y else -(mass x y)
      gain^2 ≤ (S.card : ℚ) * (((q-1)^R * (q-3)^(2*R) : Nat) : ℚ) := by
  intro q m R hq W eqs mass v S hS left right guess gain
  exact main q m R hq v S hS left right guess
