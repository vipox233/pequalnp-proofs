import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_978

abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n → F

lemma zmod2_cases (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma zmod2_zero_ne_one : (0 : F) ≠ 1 := zero_ne_one

lemma zmod2_add_self (x : F) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_add_eq_zero_iff (x y : F) : x + y = 0 ↔ x = y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
  · simp
  · simp
  · simp [zmod2_zero_ne_one.symm]
  · simp [zmod2_add_self]

lemma zmod2_ne_zero_iff (x : F) : x ≠ 0 ↔ x = 1 := by
  rcases zmod2_cases x with rfl | rfl
  · simp [zmod2_zero_ne_one]
  · simp [zmod2_zero_ne_one.symm]

lemma vec_add_self {n : Nat} (u : W n) : u + u = 0 := by
  funext k
  exact zmod2_add_self (u k)

lemma vec_add_eq_zero_iff {n : Nat} (u v : W n) : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    funext k
    exact (zmod2_add_eq_zero_iff (u k) (v k)).mp (congrFun h k)
  · rintro rfl
    exact vec_add_self u

lemma card_W (n : Nat) : Fintype.card (W n) = 2 ^ n := by
  simp [W, ZMod.card]

def sgn (z : F) : Int := if z = 1 then -1 else 1

lemma sgn_zero : sgn 0 = 1 := by decide

lemma sgn_one : sgn 1 = -1 := by decide

lemma sgn_add (x y : F) : sgn (x + y) = sgn x * sgn y := by
  fin_cases x <;> fin_cases y <;> decide

lemma sgn_mul_self (x : F) : sgn x * sgn x = 1 := by
  fin_cases x <;> decide

lemma abs_sgn (x : F) : |sgn x| = 1 := by
  fin_cases x <;> decide

lemma sgn_inj {x y : F} (h : sgn x = sgn y) : x = y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
  · rfl
  · rw [sgn_zero, sgn_one] at h; omega
  · rw [sgn_one, sgn_zero] at h; omega
  · rfl

def chi {n : Nat} (v x : W n) : Int := sgn (dotProduct v x)

lemma chi_zero_left {n : Nat} (x : W n) : chi 0 x = 1 := by
  simp [chi, sgn]

lemma chi_add_left {n : Nat} (u v x : W n) : chi (u + v) x = chi u x * chi v x := by
  simp [chi, add_dotProduct, sgn_add]

lemma chi_mul_self {n : Nat} (v x : W n) : chi v x * chi v x = 1 :=
  sgn_mul_self (dotProduct v x)

lemma abs_chi {n : Nat} (v x : W n) : |chi v x| = 1 :=
  abs_sgn (dotProduct v x)

lemma chi_ne_zero {n : Nat} (v x : W n) : chi v x ≠ 0 := by
  intro h
  have h1 := chi_mul_self v x
  rw [h] at h1
  norm_num at h1

lemma chi_eq_one_or_neg_one {n : Nat} (v x : W n) : chi v x = 1 ∨ chi v x = -1 := by
  unfold chi sgn
  split_ifs
  · right; rfl
  · left; rfl

lemma sum_chi_eq {n : Nat} (v : W n) :
    (∑ x : W n, chi v x) = if v = 0 then (2 : Int) ^ n else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [chi_zero_left, card_W]
  · simp only [hv, ite_false]
    have hne : ∃ j : Fin n, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    rcases hne with ⟨j, hj⟩
    have hj1 : v j = 1 := (zmod2_ne_zero_iff (v j)).mp hj
    let e : W n := Pi.single j 1
    have hshift : ∀ x : W n, chi v (x + e) = - chi v x := by
      intro x
      have hd : dotProduct v (x + e) = dotProduct v x + 1 := by
        rw [dotProduct_add, dotProduct_single_one, hj1]
      unfold chi
      rw [hd, sgn_add, sgn_one]
      ring
    have hsum : (∑ x : W n, chi v (x + e)) = ∑ x : W n, chi v x :=
      Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
    have hneg : (∑ x : W n, chi v (x + e)) = - ∑ x : W n, chi v x := by
      simp_rw [hshift, Finset.sum_neg_distrib]
    linarith

lemma sum_chi_mul {n : Nat} (u v : W n) :
    (∑ x : W n, chi u x * chi v x) = if u = v then (2 : Int) ^ n else 0 := by
  have h : ∀ x : W n, chi u x * chi v x = chi (u + v) x :=
    fun x => (chi_add_left u v x).symm
  simp_rw [h, sum_chi_eq, vec_add_eq_zero_iff]

lemma fourier_inv {n : Nat} (f c : W n → Int)
    (hf : ∀ x, f x = ∑ v : W n, c v * chi v x) (u : W n) :
    (∑ x : W n, f x * chi u x) = (2 : Int) ^ n * c u := by
  calc
    ∑ x : W n, f x * chi u x
        = ∑ x : W n, (∑ v : W n, c v * chi v x) * chi u x := by
            refine Finset.sum_congr rfl (fun x _ => by rw [hf x])
    _ = ∑ x : W n, ∑ v : W n, c v * (chi v x * chi u x) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun v _ => by ring)
    _ = ∑ v : W n, c v * (∑ x : W n, chi v x * chi u x) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun v _ => by rw [Finset.mul_sum])
    _ = ∑ v : W n, c v * (if v = u then (2 : Int) ^ n else 0) := by
            refine Finset.sum_congr rfl (fun v _ => by rw [sum_chi_mul])
    _ = (2 : Int) ^ n * c u := by
            simp [mul_ite, Finset.sum_ite_eq', mul_comm]

lemma four_mul_err_eq (α β γ δ : F) :
    4 * (if α * β ≠ γ + δ then (1 : Int) else 0) =
      2 - sgn δ * (sgn γ + sgn (γ + α) + sgn (γ + β) - sgn (γ + α + β)) := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;> fin_cases δ <;> decide

lemma four_mul_prod_eq (α β : F) :
    4 * (if α * β ≠ 0 then (1 : Int) else 0) = 1 - sgn α - sgn β + sgn (α + β) := by
  fin_cases α <;> fin_cases β <;> decide

def rowCoeff {n : Nat} (a b P : W n) (d : F) (v : W n) : Int :=
  (if v = 0 then 2 else 0) -
    sgn d * ((if v = P then 1 else 0) + (if v = P + a then 1 else 0) +
      (if v = P + b then 1 else 0) - (if v = P + a + b then 1 else 0))

lemma sum_rowCoeff_chi {n : Nat} (a b P : W n) (d : F) (x : W n) :
    (∑ v : W n, rowCoeff a b P d v * chi v x) =
      4 * (if dotProduct a x * dotProduct b x ≠ dotProduct P x + d then (1 : Int) else 0) := by
  have hterm : ∀ v : W n, rowCoeff a b P d v * chi v x =
      (if v = 0 then (2 : Int) * chi v x else 0) -
        sgn d * ((if v = P then chi v x else 0) + (if v = P + a then chi v x else 0) +
          (if v = P + b then chi v x else 0) - (if v = P + a + b then chi v x else 0)) := by
    intro v
    unfold rowCoeff
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, chi_zero_left, mul_one]
  unfold chi
  rw [add_dotProduct, add_dotProduct, add_dotProduct, add_dotProduct]
  exact (four_mul_err_eq (dotProduct a x) (dotProduct b x) (dotProduct P x) d).symm

def planeOf {n : Nat} (a b : W n) : Finset (W n) := {0, a, b, a + b}

def triOf {n : Nat} (a b : W n) : Finset (W n) := {a, b, a + b}

lemma planeOf_add_mem {n : Nat} {a b u w : W n}
    (hu : u ∈ planeOf a b) (hw : w ∈ planeOf a b) : u + w ∈ planeOf a b := by
  simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hu hw ⊢
  rcases hu with hu | hu | hu | hu <;> rcases hw with hw | hw | hw | hw <;> rw [hu, hw]
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; simp
  · right; left; simp
  · left; exact vec_add_self a
  · right; right; right; rfl
  · right; right; left; rw [← add_assoc, vec_add_self, zero_add]
  · right; right; left; simp
  · right; right; right; rw [add_comm]
  · left; exact vec_add_self b
  · right; left; rw [add_comm b (a + b), add_assoc, vec_add_self, add_zero]
  · right; right; right; simp
  · right; right; left; rw [add_comm (a + b) a, ← add_assoc, vec_add_self, zero_add]
  · right; left; rw [add_assoc, vec_add_self, add_zero]
  · left; exact vec_add_self (a + b)

lemma planeOf_card {n : Nat} {a b : W n} (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) :
    (planeOf a b).card = 4 := by
  rcases hnd with ⟨ha0, hb0, hab⟩
  have hab0 : a + b ≠ 0 := by
    intro h
    exact hab ((vec_add_eq_zero_iff a b).mp h)
  have haba : a + b ≠ a := by
    intro h
    have : b = 0 := by
      have h1 : a + (a + b) = a + a := congrArg (fun z => a + z) h
      rw [← add_assoc, vec_add_self, zero_add] at h1
      exact h1
    exact hb0 this
  have habb : a + b ≠ b := by
    intro h
    have : a = 0 := by
      have h1 : (a + b) + b = b + b := congrArg (fun z => z + b) h
      rw [add_assoc, vec_add_self, add_zero] at h1
      exact h1
    exact ha0 this
  unfold planeOf
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [habb.symm]
  · simp [hab, haba.symm]
  · simp [ha0.symm, hb0.symm, hab0.symm]

lemma disjoint_planeOf_image {n : Nat} {a b P : W n} (hP : P ∉ planeOf a b) :
    Disjoint (planeOf a b) ((planeOf a b).image (fun u => P + u)) := by
  rw [Finset.disjoint_left]
  intro v hv hvi
  rcases Finset.mem_image.mp hvi with ⟨u, hu, rfl⟩
  have h1 : P = (P + u) + u := by
    rw [add_assoc, vec_add_self, add_zero]
  rw [h1] at hP
  exact hP (planeOf_add_mem hv hu)

lemma rowCoeff_in_plane {n : Nat} {a b P : W n} (d : F)
    (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (hP : P ∈ planeOf a b) :
    1 ≤ rowCoeff a b P d 0 ∧ rowCoeff a b P d 0 % 2 = 1 ∧
      ∀ v : W n, v ≠ 0 →
        rowCoeff a b P d v % 2 = if v ∈ triOf a b then 1 else 0 := by
  rcases hnd with ⟨ha0, hb0, hab⟩
  have hab0 : a + b ≠ 0 := fun h => hab ((vec_add_eq_zero_iff a b).mp h)
  have haba : a + b ≠ a := by
    intro h
    have h1 : a + (a + b) = a + a := congrArg (fun z => a + z) h
    rw [← add_assoc, vec_add_self, zero_add] at h1
    exact hb0 h1
  have habb : a + b ≠ b := by
    intro h
    have h1 : (a + b) + b = b + b := congrArg (fun z => z + b) h
    rw [add_assoc, vec_add_self, add_zero] at h1
    exact ha0 h1
  have hsgn : sgn d = 1 ∨ sgn d = -1 := by
    fin_cases d
    · left; decide
    · right; decide
  simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with hP | hP | hP | hP <;> rw [hP]
  · refine ⟨?_, ?_, ?_⟩
    · unfold rowCoeff
      simp [ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · unfold rowCoeff
      simp [ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · intro v hv
      unfold rowCoeff triOf
      simp only [hv, ite_false, zero_add, zero_sub, Finset.mem_insert, Finset.mem_singleton]
      by_cases hva : v = a
      · subst hva
        simp [hab, haba.symm]
        rcases hsgn with h | h <;> omega
      · by_cases hvb : v = b
        · subst hvb
          simp [hab.symm, habb.symm]
          rcases hsgn with h | h <;> omega
        · by_cases hvab : v = a + b
          · subst hvab
            simp [haba, habb]
            rcases hsgn with h | h <;> omega
          · simp [hva, hvb, hvab]
  · refine ⟨?_, ?_, ?_⟩
    · unfold rowCoeff
      simp [vec_add_self, ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · unfold rowCoeff
      simp [vec_add_self, ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · intro v hv
      unfold rowCoeff triOf
      simp only [hv, ite_false, vec_add_self, zero_add, zero_sub, Finset.mem_insert, Finset.mem_singleton]
      by_cases hva : v = a
      · subst hva
        simp [hab, haba.symm]
        rcases hsgn with h | h <;> omega
      · by_cases hvb : v = b
        · subst hvb
          simp [hab.symm, habb.symm]
          rcases hsgn with h | h <;> omega
        · by_cases hvab : v = a + b
          · subst hvab
            simp [haba, habb]
            rcases hsgn with h | h <;> omega
          · simp [hva, hvb, hvab]
  · have hba : b + a = a + b := add_comm b a
    have habb' : a + b + b = a := by
      rw [add_assoc, vec_add_self, add_zero]
    refine ⟨?_, ?_, ?_⟩
    · unfold rowCoeff
      simp [hba, habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · unfold rowCoeff
      simp [hba, habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · intro v hv
      unfold rowCoeff triOf
      simp only [hv, ite_false, hba, habb', vec_add_self, zero_sub, Finset.mem_insert, Finset.mem_singleton]
      by_cases hva : v = a
      · subst hva
        simp [hab, haba.symm]
        rcases hsgn with h | h <;> omega
      · by_cases hvb : v = b
        · subst hvb
          simp [hab.symm, habb.symm]
          rcases hsgn with h | h <;> omega
        · by_cases hvab : v = a + b
          · subst hvab
            simp [haba, habb]
            rcases hsgn with h | h <;> omega
          · simp [hva, hvb, hvab]
  · have haba' : a + b + a = b := by
      rw [add_comm (a + b) a, ← add_assoc, vec_add_self, zero_add]
    have habb' : a + b + b = a := by
      rw [add_assoc, vec_add_self, add_zero]
    refine ⟨?_, ?_, ?_⟩
    · unfold rowCoeff
      simp [haba', habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · unfold rowCoeff
      simp [haba', habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm]
      rcases hsgn with h | h <;> omega
    · intro v hv
      unfold rowCoeff triOf
      simp only [hv, ite_false, haba', habb', vec_add_self, zero_sub, Finset.mem_insert, Finset.mem_singleton]
      by_cases hva : v = a
      · subst hva
        simp [hab, haba.symm]
        rcases hsgn with h | h <;> omega
      · by_cases hvb : v = b
        · subst hvb
          simp [hab.symm, habb.symm]
          rcases hsgn with h | h <;> omega
        · by_cases hvab : v = a + b
          · subst hvab
            simp [haba, habb]
            rcases hsgn with h | h <;> omega
          · simp [hva, hvb, hvab]

lemma rowCoeff_not_in_plane {n : Nat} {a b P : W n} (d : F)
    (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (hP : P ∉ planeOf a b) :
    rowCoeff a b P d 0 = 2 ∧
      ∀ v : W n, v ≠ 0 →
        rowCoeff a b P d v % 2 =
          if v ∈ (planeOf a b).image (fun u => P + u) then 1 else 0 := by
  rcases hnd with ⟨ha0, hb0, hab⟩
  have hab0 : a + b ≠ 0 := fun h => hab ((vec_add_eq_zero_iff a b).mp h)
  have hP0 : 0 ≠ P := by
    intro h; exact hP (by simp [planeOf, h.symm])
  have hPa : 0 ≠ P + a := by
    intro h
    have : P = a := (vec_add_eq_zero_iff P a).mp h.symm
    exact hP (by simp [planeOf, this])
  have hPb : 0 ≠ P + b := by
    intro h
    have : P = b := (vec_add_eq_zero_iff P b).mp h.symm
    exact hP (by simp [planeOf, this])
  have hPab : 0 ≠ P + a + b := by
    intro h
    have : P = a + b := by
      rw [add_assoc] at h
      exact (vec_add_eq_zero_iff P (a + b)).mp h.symm
    exact hP (by simp [planeOf, this])
  have hsgn : sgn d = 1 ∨ sgn d = -1 := by
    fin_cases d
    · left; decide
    · right; decide
  constructor
  · unfold rowCoeff
    simp [hP0, hPa, hPb, hPab]
  · intro v hv
    have himg : (planeOf a b).image (fun u => P + u) = {P, P + a, P + b, P + a + b} := by
      unfold planeOf
      simp [Finset.image_insert, Finset.image_singleton, add_assoc]
    rw [himg]
    have h12 : P ≠ P + a := by
      intro h
      have h' : P + P = P + (P + a) := congrArg (fun z => P + z) h
      rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h'
      exact ha0 h'.symm
    have h13 : P ≠ P + b := by
      intro h
      have h' : P + P = P + (P + b) := congrArg (fun z => P + z) h
      rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h'
      exact hb0 h'.symm
    have h14 : P ≠ P + a + b := by
      intro h
      have h' : P + P = P + (P + a + b) := congrArg (fun z => P + z) h
      rw [vec_add_self, ← add_assoc, ← add_assoc, vec_add_self, zero_add] at h'
      exact hab0 h'.symm
    have h23 : P + a ≠ P + b := fun h => hab (add_left_cancel h)
    have h24 : P + a ≠ P + a + b := by
      intro h
      have h' : (P + a) + (P + a) = (P + a) + ((P + a) + b) := congrArg (fun z => (P + a) + z) h
      rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h'
      exact hb0 h'.symm
    have h34 : P + b ≠ P + a + b := by
      intro h
      have h' : P + b = P + b + a := by
        rw [add_right_comm P a b] at h
        exact h
      have h'' : (P + b) + (P + b) = (P + b) + ((P + b) + a) := congrArg (fun z => (P + b) + z) h'
      rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h''
      exact ha0 h''.symm
    unfold rowCoeff
    simp only [hv, ite_false, zero_sub, Finset.mem_insert, Finset.mem_singleton]
    by_cases hv1 : v = P
    · subst hv1
      simp [h12, h13, h14]
      rcases hsgn with h | h <;> omega
    · by_cases hv2 : v = P + a
      · subst hv2
        simp [h12.symm, h23, h24]
        rcases hsgn with h | h <;> omega
      · by_cases hv3 : v = P + b
        · subst hv3
          simp [h13.symm, h23.symm, h34]
          rcases hsgn with h | h <;> omega
        · by_cases hv4 : v = P + a + b
          · subst hv4
            simp [h14.symm, h24.symm, h34.symm]
            rcases hsgn with h | h <;> omega
          · simp [hv1, hv2, hv3, hv4]

lemma sum_emod_two {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → Int)
    (h : ∀ i ∈ s, f i % 2 = g i % 2) :
    (∑ i ∈ s, f i) % 2 = (∑ i ∈ s, g i) % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha' : f a % 2 = g a % 2 := h a (Finset.mem_insert_self a s)
    have hs' : (∑ i ∈ s, f i) % 2 = (∑ i ∈ s, g i) % 2 :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    omega

lemma part1 (n e : Nat) (he : 0 < e) :
    let m := 4 * e - 1
    let I := Fin m
    ∀ (a b P : I → W n) (d : I → F),
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
      let errs := fun x : W n => ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card
      (∀ x, errs x ≤ e) →
      let oddLabels := (Finset.univ : Finset (W n)).filter (fun v =>
        ((Finset.univ : Finset I).filter (fun i =>
          v ∈ ({a i, b i, a i + b i} : Finset (W n)))).card % 2 = 1)
      let S := insert (0 : W n) oddLabels
      let plane := fun i : I => ({0, a i, b i, a i + b i} : Finset (W n))
      (∀ v ∈ S, ∀ w ∈ S, v + w ∈ S) ∧ 4 ≤ S.card ∧
      (((∀ i, P i ∈ plane i) ∧ ∃ z : W n, ∀ x : W n,
         e - errs x = if ∀ v ∈ S, dotProduct v x = dotProduct v z then S.card / 4 else 0) ∨
       (S.card = 8 ∧ (∀ x, errs x = e) ∧ ∃ j : I, P j ∉ plane j ∧
         (∀ i, i ≠ j → P i ∈ plane i) ∧ S = plane j ∪ (plane j).image (fun v => P j + v))) := by
  intro m I a b P d hnd errs herrs oddLabels S plane
  let g : W n → Int := fun x => (4 * e : Int) - 4 * (errs x : Int)
  let c : W n → Int := fun v =>
    (if v = 0 then (4 * e : Int) else 0) - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v
  have hg_nonneg : ∀ x : W n, 0 ≤ g x := by
    intro x
    have hx : errs x ≤ e := herrs x
    unfold g
    omega
  have hg_fourier : ∀ x : W n, g x = ∑ v : W n, c v * chi v x := by
    intro x
    have herr_sum : (4 * (errs x : Int)) =
        ∑ i : I, ∑ v : W n, rowCoeff (a i) (b i) (P i) (d i) v * chi v x := by
      have h1 : (errs x : Int) = ∑ i : I,
          (if dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i then (1 : Int) else 0) := by
        dsimp only [errs]
        rw [Finset.sum_boole]
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (sum_rowCoeff_chi (a i) (b i) (P i) (d i) x).symm
    have h2 : (∑ v : W n, c v * chi v x) =
        (4 * e : Int) - ∑ v : W n, (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) * chi v x := by
      have hsplit : ∀ v : W n, c v * chi v x =
          (if v = 0 then (4 * e : Int) * chi v x else 0) -
            (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) * chi v x := by
        intro v
        unfold c
        split_ifs <;> ring
      simp_rw [hsplit]
      rw [Finset.sum_sub_distrib]
      simp [chi_zero_left]
    have hswap : (∑ v : W n, (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) * chi v x) =
        ∑ i : I, ∑ v : W n, rowCoeff (a i) (b i) (P i) (d i) v * chi v x := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [h2, hswap, ← herr_sum]
  have hc_inv : ∀ u : W n, (∑ x : W n, g x * chi u x) = (2 : Int) ^ n * c u :=
    fun u => fourier_inv g c hg_fourier u
  have hsum_g : (∑ x : W n, g x) = (2 : Int) ^ n * c 0 := by
    have h0 := hc_inv 0
    simp only [chi_zero_left, mul_one] at h0
    exact h0
  have h2pos : (0 : Int) < (2 : Int) ^ n := by positivity
  have hc0_nonneg : 0 ≤ c 0 := by
    have hnn : 0 ≤ ∑ x : W n, g x := Finset.sum_nonneg (fun x _ => hg_nonneg x)
    rw [hsum_g] at hnn
    nlinarith
  have hc0_def : c 0 = (4 * e : Int) - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0 := by
    simp [c]
  let Bad : Finset I := Finset.univ.filter (fun i => P i ∉ plane i)
  have hrow0_lb : ∀ i : I, (1 : Int) + (if i ∈ Bad then 1 else 0) ≤
      rowCoeff (a i) (b i) (P i) (d i) 0 := by
    intro i
    by_cases hPi : P i ∈ plane i
    · have hi : i ∉ Bad := by simp [Bad, hPi]
      simp only [hi, ite_false, add_zero]
      exact (rowCoeff_in_plane (d i) (hnd i) hPi).1
    · have hi : i ∈ Bad := by simp [Bad, hPi]
      simp only [hi, ite_true]
      have h2 := (rowCoeff_not_in_plane (d i) (hnd i) hPi).1
      omega
  have hsum_lb : (m : Int) + (Bad.card : Int) ≤
      ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0 := by
    calc
      (m : Int) + (Bad.card : Int)
          = ∑ i : I, ((1 : Int) + (if i ∈ Bad then 1 else 0)) := by
              rw [Finset.sum_add_distrib]
              simp [I]
      _ ≤ ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0 :=
              Finset.sum_le_sum (fun i _ => hrow0_lb i)
  have hBad_le : Bad.card ≤ 1 := by
    have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBad_le with hBad0 | hBad1
  · have hall_plane : ∀ i : I, P i ∈ plane i := by
      intro i
      have hEmpty : Bad = ∅ := Finset.card_eq_zero.mp hBad0
      have hi : i ∉ Bad := by rw [hEmpty]; simp
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hi
    have hsum_odd : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0) % 2 = 1 := by
      have h1 : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0) % 2 =
          (∑ _i : I, (1 : Int)) % 2 := by
        refine sum_emod_two Finset.univ _ _ (fun i _ => ?_)
        have hmod := (rowCoeff_in_plane (d i) (hnd i) (hall_plane i)).2.1
        omega
      rw [h1]
      simp only [I, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
      omega
    have hc0_eq : c 0 = 1 := by
      have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
      omega
    have hsum_g_eq : (∑ x : W n, g x) = (2 : Int) ^ n := by
      rw [hsum_g, hc0_eq, mul_one]
    have hex_z : ∃ z : W n, 0 < g z := by
      by_contra h
      push Not at h
      have hzero : ∀ x : W n, g x = 0 := fun x => le_antisymm (h x) (hg_nonneg x)
      have hsum0 : (∑ x : W n, g x) = 0 := Finset.sum_eq_zero (fun x _ => hzero x)
      linarith
    rcases hex_z with ⟨z, hz⟩
    have habs_c : ∀ v : W n, |c v| ≤ 1 := by
      intro v
      have hle : (2 : Int) ^ n * |c v| ≤ (2 : Int) ^ n := by
        calc
          (2 : Int) ^ n * |c v|
              = |(2 : Int) ^ n * c v| := by
                  rw [abs_mul, abs_of_pos h2pos]
          _ = |∑ x : W n, g x * chi v x| := by
                  rw [← hc_inv v]
          _ ≤ ∑ x : W n, |g x * chi v x| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x : W n, g x := by
                  refine Finset.sum_congr rfl (fun x _ => ?_)
                  rw [abs_mul, abs_of_nonneg (hg_nonneg x), abs_chi v x, mul_one]
          _ = (2 : Int) ^ n := hsum_g_eq
      nlinarith
    have hc_mem_S : ∀ v : W n, c v ≠ 0 ↔ v ∈ S := by
      intro v
      by_cases hv : v = 0
      · subst hv
        simp [hc0_eq, S]
      · have hcv : c v = - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v := by
          simp [c, hv]
        let cnt : Nat := ((Finset.univ : Finset I).filter (fun i =>
          v ∈ ({a i, b i, a i + b i} : Finset (W n)))).card
        have hmod : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) % 2 = (cnt : Int) % 2 := by
          have h1 : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) % 2 =
              (∑ i : I, if v ∈ ({a i, b i, a i + b i} : Finset (W n)) then (1 : Int) else 0) % 2 := by
            refine sum_emod_two Finset.univ _ _ (fun i _ => ?_)
            have h2 := (rowCoeff_in_plane (d i) (hnd i) (hall_plane i)).2.2 v hv
            change rowCoeff (a i) (b i) (P i) (d i) v % 2 =
              if v ∈ ({a i, b i, a i + b i} : Finset (W n)) then 1 else 0 at h2
            split_ifs at h2 ⊢ <;> omega
          rw [h1]
          simp [cnt, Finset.sum_boole]
        have hbound : -1 ≤ c v ∧ c v ≤ 1 := abs_le.mp (habs_c v)
        have hvS : v ∈ S ↔ cnt % 2 = 1 := by
          change v ∈ insert (0 : W n) oddLabels ↔ cnt % 2 = 1
          rw [Finset.mem_insert]
          simp only [hv, false_or]
          change v ∈ (Finset.univ : Finset (W n)).filter _ ↔ cnt % 2 = 1
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and]
          rfl
        rw [hvS]
        constructor <;> intro h <;> omega
    have hc_val_on_pos : ∀ v ∈ S, ∀ x : W n, 0 < g x → chi v x = c v := by
      intro v hvS
      have hcv_ne : c v ≠ 0 := (hc_mem_S v).mpr hvS
      have hbound : -1 ≤ c v ∧ c v ≤ 1 := abs_le.mp (habs_c v)
      have hcv_pm : c v = 1 ∨ c v = -1 := by omega
      have hcv_sq : c v * c v = 1 := by
        rcases hcv_pm with h | h <;> rw [h] <;> norm_num
      have hterm_nn : ∀ x : W n, 0 ≤ g x * (1 - c v * chi v x) := by
        intro x
        have hgx := hg_nonneg x
        have hchi := chi_eq_one_or_neg_one v x
        rcases hcv_pm with h1 | h1 <;> rcases hchi with h2 | h2 <;>
          rw [h1, h2] <;> nlinarith
      have hsum_zero : (∑ x : W n, g x * (1 - c v * chi v x)) = 0 := by
        have h1 : ∀ x : W n, g x * (1 - c v * chi v x) =
            g x - c v * (g x * chi v x) := fun x => by ring
        simp_rw [h1]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_g_eq, hc_inv v]
        calc
          (2 : Int) ^ n - c v * ((2 : Int) ^ n * c v)
              = (2 : Int) ^ n * (1 - c v * c v) := by ring
          _ = 0 := by rw [hcv_sq]; ring
      have hall_zero : ∀ x : W n, g x * (1 - c v * chi v x) = 0 := by
        intro x
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hterm_nn y)).mp hsum_zero x (Finset.mem_univ x)
      intro x hgx
      have hxz := hall_zero x
      have h1 : 1 - c v * chi v x = 0 := by
        rcases mul_eq_zero.mp hxz with h | h
        · linarith
        · exact h
      have h2 : c v * chi v x = 1 := by linarith
      calc
        chi v x = (c v * c v) * chi v x := by rw [hcv_sq, one_mul]
        _ = c v * (c v * chi v x) := by ring
        _ = c v := by rw [h2, mul_one]
    have hc_eq_chi_z : ∀ v ∈ S, c v = chi v z :=
      fun v hvS => (hc_val_on_pos v hvS z hz).symm
    have hg_eq : ∀ x : W n,
        g x = if (∀ v ∈ S, dotProduct v x = dotProduct v z) then (S.card : Int) else 0 := by
      intro x
      by_cases hdot : ∀ v ∈ S, dotProduct v x = dotProduct v z
      · rw [if_pos hdot]
        rw [hg_fourier x]
        have hsub : (∑ v : W n, c v * chi v x) = ∑ v ∈ S, c v * chi v x := by
          symm
          refine Finset.sum_subset (Finset.subset_univ S) (fun v _ hvnot => ?_)
          have hcv0 : c v = 0 := by
            by_contra hne
            exact hvnot ((hc_mem_S v).mp hne)
          rw [hcv0, zero_mul]
        rw [hsub]
        have hone : ∀ v ∈ S, c v * chi v x = 1 := by
          intro v hvS
          rw [hc_eq_chi_z v hvS]
          have hchi : chi v x = chi v z := by
            unfold chi
            rw [hdot v hvS]
          rw [hchi, chi_mul_self]
        rw [Finset.sum_congr rfl hone]
        simp
      · rw [if_neg hdot]
        by_contra hne
        have hpos : 0 < g x := lt_of_le_of_ne (hg_nonneg x) (Ne.symm hne)
        apply hdot
        intro v hvS
        have hchi : chi v x = chi v z := by
          rw [hc_val_on_pos v hvS x hpos, hc_eq_chi_z v hvS]
        exact sgn_inj hchi
    have hS_closed : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S := by
      intro v hvS w hwS
      have h1 : (2 : Int) ^ n * c (v + w) = ∑ x : W n, g x * chi (v + w) x :=
        (hc_inv (v + w)).symm
      have h2 : ∀ x : W n, g x * chi (v + w) x = g x * (chi v z * chi w z) := by
        intro x
        by_cases hgx : g x = 0
        · simp [hgx]
        · have hpos : 0 < g x := lt_of_le_of_ne (hg_nonneg x) (Ne.symm hgx)
          rw [chi_add_left, hc_val_on_pos v hvS x hpos, hc_val_on_pos w hwS x hpos,
            hc_eq_chi_z v hvS, hc_eq_chi_z w hwS]
      simp_rw [h2, ← Finset.sum_mul, hsum_g_eq] at h1
      have hcvw : c (v + w) = chi v z * chi w z := by
        exact mul_left_cancel₀ (ne_of_gt h2pos) h1
      have hne : c (v + w) ≠ 0 := by
        rw [hcvw]
        exact mul_ne_zero (chi_ne_zero v z) (chi_ne_zero w z)
      exact (hc_mem_S (v + w)).mp hne
    have hgz_eq : g z = (S.card : Int) := by
      have h := hg_eq z
      simp at h
      exact h
    have hS_card_eq : (S.card : Int) = 4 * ((e - errs z : Nat) : Int) := by
      have hze : errs z ≤ e := herrs z
      unfold g at hgz_eq
      omega
    have h4le : 4 ≤ S.card := by
      omega
    have herr_formula : ∀ x : W n,
        e - errs x = if ∀ v ∈ S, dotProduct v x = dotProduct v z then S.card / 4 else 0 := by
      intro x
      have hgx := hg_eq x
      have hxe : errs x ≤ e := herrs x
      unfold g at hgx
      split_ifs at hgx ⊢ <;> omega
    exact ⟨hS_closed, h4le, Or.inl ⟨hall_plane, z, herr_formula⟩⟩
  · rcases Finset.card_eq_one.mp hBad1 with ⟨j, hBad_eq⟩
    have hj_mem : j ∈ Bad := by rw [hBad_eq]; simp
    have hj_not : P j ∉ plane j := (Finset.mem_filter.mp hj_mem).2
    have hother_in : ∀ i : I, i ≠ j → P i ∈ plane i := by
      intro i hij
      have hi : i ∉ Bad := by rw [hBad_eq]; simp [hij]
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hi
    have hc0_eq : c 0 = 0 := by
      have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
      omega
    have hsum_g_zero : (∑ x : W n, g x) = 0 := by
      rw [hsum_g, hc0_eq, mul_zero]
    have hg_zero : ∀ x : W n, g x = 0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hg_nonneg y)).mp hsum_g_zero x (Finset.mem_univ x)
    have herrs_eq : ∀ x : W n, errs x = e := by
      intro x
      have hgx := hg_zero x
      have hxe := herrs x
      unfold g at hgx
      omega
    have hc_zero : ∀ v : W n, c v = 0 := by
      intro v
      have h1 := hc_inv v
      have h0 : (∑ x : W n, g x * chi v x) = 0 :=
        Finset.sum_eq_zero (fun x _ => by rw [hg_zero x, zero_mul])
      rw [h0] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (ne_of_gt h2pos)
    have hdisj : Disjoint (plane j) ((plane j).image (fun u => P j + u)) :=
      disjoint_planeOf_image hj_not
    have hS_eq : S = plane j ∪ (plane j).image (fun v => P j + v) := by
      ext v
      by_cases hv : v = 0
      · subst hv
        simp [S, plane]
      · have hsum_row0 : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) = 0 := by
          have hcv := hc_zero v
          simp only [c, hv, ite_false, zero_sub, neg_eq_zero] at hcv
          exact hcv
        have hsplit_row : rowCoeff (a j) (b j) (P j) (d j) v +
            ∑ i ∈ Finset.univ.erase j, rowCoeff (a i) (b i) (P i) (d i) v = 0 := by
          rw [Finset.add_sum_erase Finset.univ (fun i => rowCoeff (a i) (b i) (P i) (d i) v)
            (Finset.mem_univ j)]
          exact hsum_row0
        have herase_mod : (∑ i ∈ Finset.univ.erase j, rowCoeff (a i) (b i) (P i) (d i) v) % 2 =
            (∑ i ∈ Finset.univ.erase j, if v ∈ triOf (a i) (b i) then (1 : Int) else 0) % 2 := by
          refine sum_emod_two (Finset.univ.erase j) _ _ (fun i hi => ?_)
          have hij : i ≠ j := (Finset.mem_erase.mp hi).1
          have h2 := (rowCoeff_in_plane (d i) (hnd i) (hother_in i hij)).2.2 v hv
          split_ifs at h2 ⊢ <;> omega
        have hj_mod : rowCoeff (a j) (b j) (P j) (d j) v % 2 =
            if v ∈ (plane j).image (fun u => P j + u) then 1 else 0 :=
          (rowCoeff_not_in_plane (d j) (hnd j) hj_not).2 v hv
        let cnt : Nat := ((Finset.univ : Finset I).filter (fun i =>
          v ∈ ({a i, b i, a i + b i} : Finset (W n)))).card
        have hcnt_split : (cnt : Int) =
            (if v ∈ triOf (a j) (b j) then (1 : Int) else 0) +
            ∑ i ∈ Finset.univ.erase j, if v ∈ triOf (a i) (b i) then (1 : Int) else 0 := by
          have h1 : (cnt : Int) =
              ∑ i : I, if v ∈ triOf (a i) (b i) then (1 : Int) else 0 := by
            rw [Finset.sum_boole]
            congr 2
          rw [h1, ← Finset.add_sum_erase Finset.univ
            (fun i => if v ∈ triOf (a i) (b i) then (1 : Int) else 0) (Finset.mem_univ j)]
        have hv_plane_iff : v ∈ plane j ↔ v ∈ triOf (a j) (b j) := by
          simp [plane, triOf, hv]
        have hvS : v ∈ S ↔ cnt % 2 = 1 := by
          change v ∈ insert (0 : W n) oddLabels ↔ cnt % 2 = 1
          rw [Finset.mem_insert]
          simp only [hv, false_or]
          change v ∈ (Finset.univ : Finset (W n)).filter _ ↔ cnt % 2 = 1
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and]
          rfl
        rw [hvS, Finset.mem_union, hv_plane_iff]
        by_cases h1 : v ∈ triOf (a j) (b j)
        · have h2 : v ∉ (plane j).image (fun u => P j + u) := by
            intro hmem
            exact Finset.disjoint_left.mp hdisj (hv_plane_iff.mpr h1) hmem
          simp only [h1, h2, ite_true, ite_false, true_or, iff_true] at hj_mod hcnt_split ⊢
          omega
        · by_cases h2 : v ∈ (plane j).image (fun u => P j + u)
          · simp only [h1, h2, ite_true, ite_false, or_true, iff_true] at hj_mod hcnt_split ⊢
            omega
          · simp only [h1, h2, ite_false, or_self, iff_false] at hj_mod hcnt_split ⊢
            omega
    have hS_card : S.card = 8 := by
      rw [hS_eq, Finset.card_union_of_disjoint hdisj]
      have himg_card : ((plane j).image (fun v => P j + v)).card = (plane j).card :=
        Finset.card_image_of_injective _ (fun u₁ u₂ h => add_left_cancel h)
      have hpc : (plane j).card = 4 := planeOf_card (hnd j)
      omega
    have hS_closed : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S := by
      intro v hvS w hwS
      rw [hS_eq, Finset.mem_union] at hvS hwS ⊢
      rcases hvS with hv1 | hv2 <;> rcases hwS with hw1 | hw2
      · left
        exact planeOf_add_mem hv1 hw1
      · right
        rcases Finset.mem_image.mp hw2 with ⟨u, hu, rfl⟩
        refine Finset.mem_image.mpr ⟨v + u, planeOf_add_mem hv1 hu, ?_⟩
        abel
      · right
        rcases Finset.mem_image.mp hv2 with ⟨u, hu, rfl⟩
        refine Finset.mem_image.mpr ⟨u + w, planeOf_add_mem hu hw1, ?_⟩
        abel
      · left
        rcases Finset.mem_image.mp hv2 with ⟨u₁, hu₁, rfl⟩
        rcases Finset.mem_image.mp hw2 with ⟨u₂, hu₂, rfl⟩
        have heq : (P j + u₁) + (P j + u₂) = u₁ + u₂ := by
          calc
            (P j + u₁) + (P j + u₂) = (P j + P j) + (u₁ + u₂) := by abel
            _ = 0 + (u₁ + u₂) := by rw [vec_add_self]
            _ = u₁ + u₂ := zero_add _
        rw [heq]
        exact planeOf_add_mem hu₁ hu₂
    exact ⟨hS_closed, by omega, Or.inr ⟨hS_card, herrs_eq, j, hj_not, hother_in, hS_eq⟩⟩

def mapT (h : Nat) (hh : 2 ≤ h) (u : W h) : W h := fun i =>
  if hpar : h % 2 = 0 then
    if hi : i.val % 2 = 0 then
      u ⟨i.val + 1, by omega⟩
    else
      u ⟨i.val - 1, by omega⟩ + u i
  else
    if h0 : i.val = 0 then
      u ⟨1, by omega⟩
    else if h1 : i.val = 1 then
      u ⟨2, by omega⟩
    else if h2 : i.val = 2 then
      u ⟨0, by omega⟩ + u ⟨1, by omega⟩
    else if hi : (i.val - 3) % 2 = 0 then
      u ⟨i.val + 1, by omega⟩
    else
      u ⟨i.val - 1, by omega⟩ + u i

lemma mapT_add (h : Nat) (hh : 2 ≤ h) (u v : W h) :
    mapT h hh (u + v) = mapT h hh u + mapT h hh v := by
  funext i
  simp only [Pi.add_apply]
  unfold mapT
  split_ifs <;> simp [Pi.add_apply] <;> abel

lemma mapT_zero (h : Nat) (hh : 2 ≤ h) : mapT h hh 0 = 0 := by
  funext i
  simp only [Pi.zero_apply]
  unfold mapT
  split_ifs <;> simp

lemma mapT_eq_zero (h : Nat) (hh : 2 ≤ h) (u : W h) (hu : mapT h hh u = 0) : u = 0 := by
  funext i
  by_cases hpar : h % 2 = 0
  · by_cases hi : i.val % 2 = 0
    · let j : Fin h := ⟨i.val + 1, by omega⟩
      have hjval : j.val = i.val + 1 := rfl
      have h1 : mapT h hh u i = 0 := congrFun hu i
      have h2 : mapT h hh u j = 0 := congrFun hu j
      have h1' : u j = 0 := by
        unfold mapT at h1
        simp only [hpar, hi, dite_true] at h1
        exact h1
      have h2' : u i + u j = 0 := by
        unfold mapT at h2
        have hj : ¬ j.val % 2 = 0 := by omega
        simp only [hpar, hj, dite_true, dite_false] at h2
        have hsub : (⟨j.val - 1, by omega⟩ : Fin h) = i := by
          ext; dsimp; omega
        rw [hsub] at h2
        exact h2
      rw [h1', add_zero] at h2'
      exact h2'
    · let j : Fin h := ⟨i.val - 1, by omega⟩
      have hjval : j.val = i.val - 1 := rfl
      have h1 : mapT h hh u j = 0 := congrFun hu j
      unfold mapT at h1
      have hj : j.val % 2 = 0 := by omega
      simp only [hpar, hj, dite_true] at h1
      have hadd : (⟨j.val + 1, by omega⟩ : Fin h) = i := by
        ext; dsimp; omega
      rw [hadd] at h1
      exact h1
  · by_cases hi3 : i.val < 3
    · have h0 : mapT h hh u ⟨0, by omega⟩ = 0 := congrFun hu ⟨0, by omega⟩
      have h1 : mapT h hh u ⟨1, by omega⟩ = 0 := congrFun hu ⟨1, by omega⟩
      have h2 : mapT h hh u ⟨2, by omega⟩ = 0 := congrFun hu ⟨2, by omega⟩
      unfold mapT at h0 h1 h2
      simp [hpar] at h0 h1 h2
      have hu0 : u ⟨0, by omega⟩ = 0 := by
        rw [h0, add_zero] at h2
        exact h2
      have hic : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ ∨ i = ⟨2, by omega⟩ := by
        by_cases c0 : i.val = 0
        · left; ext; exact c0
        · by_cases c1 : i.val = 1
          · right; left; ext; exact c1
          · right; right; ext; dsimp; omega
      rcases hic with hi_eq | hi_eq | hi_eq
      · rw [hi_eq]; exact hu0
      · rw [hi_eq]; exact h0
      · rw [hi_eq]; exact h1
    · by_cases hi : (i.val - 3) % 2 = 0
      · let j : Fin h := ⟨i.val + 1, by omega⟩
        have hjval : j.val = i.val + 1 := rfl
        have h1 : mapT h hh u i = 0 := congrFun hu i
        have h2 : mapT h hh u j = 0 := congrFun hu j
        have hi0 : i.val ≠ 0 := by omega
        have hi1 : i.val ≠ 1 := by omega
        have hi2 : i.val ≠ 2 := by omega
        have hj0 : j.val ≠ 0 := by omega
        have hj1 : j.val ≠ 1 := by omega
        have hj2 : j.val ≠ 2 := by omega
        have hj : ¬ (j.val - 3) % 2 = 0 := by omega
        have h1' : u j = 0 := by
          unfold mapT at h1
          simp only [hpar, hi0, hi1, hi2, hi, dite_false, dite_true] at h1
          exact h1
        have h2' : u i + u j = 0 := by
          unfold mapT at h2
          simp only [hpar, hj0, hj1, hj2, hj, dite_false] at h2
          have hsub : (⟨j.val - 1, by omega⟩ : Fin h) = i := by
            ext; dsimp; omega
          rw [hsub] at h2
          exact h2
        rw [h1', add_zero] at h2'
        exact h2'
      · let j : Fin h := ⟨i.val - 1, by omega⟩
        have hjval : j.val = i.val - 1 := rfl
        have h1 : mapT h hh u j = 0 := congrFun hu j
        have hj0 : j.val ≠ 0 := by omega
        have hj1 : j.val ≠ 1 := by omega
        have hj2 : j.val ≠ 2 := by omega
        have hj : (j.val - 3) % 2 = 0 := by omega
        unfold mapT at h1
        simp only [hpar, hj0, hj1, hj2, hj, dite_false, dite_true] at h1
        have hadd : (⟨j.val + 1, by omega⟩ : Fin h) = i := by
          ext; dsimp; omega
        rw [hadd] at h1
        exact h1

lemma mapT_eq_self (h : Nat) (hh : 2 ≤ h) (u : W h) (hu : mapT h hh u = u) : u = 0 := by
  funext i
  by_cases hpar : h % 2 = 0
  · by_cases hi : i.val % 2 = 0
    · let j : Fin h := ⟨i.val + 1, by omega⟩
      have hjval : j.val = i.val + 1 := rfl
      have h1 : mapT h hh u i = u i := congrFun hu i
      have h2 : mapT h hh u j = u j := congrFun hu j
      have h1' : u j = u i := by
        unfold mapT at h1
        simp only [hpar, hi, dite_true] at h1
        exact h1
      have h2' : u i + u j = u j := by
        unfold mapT at h2
        have hj : ¬ j.val % 2 = 0 := by omega
        simp only [hpar, hj, dite_true, dite_false] at h2
        have hsub : (⟨j.val - 1, by omega⟩ : Fin h) = i := by
          ext; dsimp; omega
        rw [hsub] at h2
        exact h2
      have hu0 : u i = 0 := by
        have h3 : u i + u j + u j = u j + u j := congrArg (fun z => z + u j) h2'
        rw [add_assoc, zmod2_add_self, add_zero] at h3
        exact h3
      exact hu0
    · let j : Fin h := ⟨i.val - 1, by omega⟩
      have hjval : j.val = i.val - 1 := rfl
      have h1 : mapT h hh u j = u j := congrFun hu j
      have h2 : mapT h hh u i = u i := congrFun hu i
      have hj : j.val % 2 = 0 := by omega
      have h1' : u i = u j := by
        unfold mapT at h1
        simp only [hpar, hj, dite_true] at h1
        have hadd : (⟨j.val + 1, by omega⟩ : Fin h) = i := by
          ext; dsimp; omega
        rw [hadd] at h1
        exact h1
      have h2' : u j + u i = u i := by
        unfold mapT at h2
        simp only [hpar, hi, dite_true, dite_false] at h2
        exact h2
      have hj0 : u j = 0 := by
        have h3 : u j + u i + u i = u i + u i := congrArg (fun z => z + u i) h2'
        rw [add_assoc, zmod2_add_self, add_zero] at h3
        exact h3
      rw [h1', hj0]
      rfl
  · by_cases hi3 : i.val < 3
    · have h0 : mapT h hh u ⟨0, by omega⟩ = u ⟨0, by omega⟩ := congrFun hu ⟨0, by omega⟩
      have h1 : mapT h hh u ⟨1, by omega⟩ = u ⟨1, by omega⟩ := congrFun hu ⟨1, by omega⟩
      have h2 : mapT h hh u ⟨2, by omega⟩ = u ⟨2, by omega⟩ := congrFun hu ⟨2, by omega⟩
      unfold mapT at h0 h1 h2
      simp [hpar] at h0 h1 h2
      have hu2 : u ⟨2, by omega⟩ = 0 := by
        rw [h0, zmod2_add_self] at h2
        exact h2.symm
      have hu1 : u ⟨1, by omega⟩ = 0 := by rw [← h1, hu2]
      have hu0 : u ⟨0, by omega⟩ = 0 := by rw [← h0, hu1]
      have hic : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ ∨ i = ⟨2, by omega⟩ := by
        by_cases c0 : i.val = 0
        · left; ext; exact c0
        · by_cases c1 : i.val = 1
          · right; left; ext; exact c1
          · right; right; ext; dsimp; omega
      rcases hic with hi_eq | hi_eq | hi_eq
      · rw [hi_eq]; exact hu0
      · rw [hi_eq]; exact hu1
      · rw [hi_eq]; exact hu2
    · by_cases hi : (i.val - 3) % 2 = 0
      · let j : Fin h := ⟨i.val + 1, by omega⟩
        have hjval : j.val = i.val + 1 := rfl
        have h1 : mapT h hh u i = u i := congrFun hu i
        have h2 : mapT h hh u j = u j := congrFun hu j
        have hi0 : i.val ≠ 0 := by omega
        have hi1 : i.val ≠ 1 := by omega
        have hi2 : i.val ≠ 2 := by omega
        have hj0 : j.val ≠ 0 := by omega
        have hj1 : j.val ≠ 1 := by omega
        have hj2 : j.val ≠ 2 := by omega
        have hj : ¬ (j.val - 3) % 2 = 0 := by omega
        have h2' : u i + u j = u j := by
          unfold mapT at h2
          simp only [hpar, hj0, hj1, hj2, hj, dite_false] at h2
          have hsub : (⟨j.val - 1, by omega⟩ : Fin h) = i := by
            ext; dsimp; omega
          rw [hsub] at h2
          exact h2
        have h3 : u i + u j + u j = u j + u j := congrArg (fun z => z + u j) h2'
        rw [add_assoc, zmod2_add_self, add_zero] at h3
        exact h3
      · let j : Fin h := ⟨i.val - 1, by omega⟩
        have hjval : j.val = i.val - 1 := rfl
        have h1 : mapT h hh u j = u j := congrFun hu j
        have h2 : mapT h hh u i = u i := congrFun hu i
        have hi0 : i.val ≠ 0 := by omega
        have hi1 : i.val ≠ 1 := by omega
        have hi2 : i.val ≠ 2 := by omega
        have hj0 : j.val ≠ 0 := by omega
        have hj1 : j.val ≠ 1 := by omega
        have hj2 : j.val ≠ 2 := by omega
        have hj : (j.val - 3) % 2 = 0 := by omega
        have h1' : u i = u j := by
          unfold mapT at h1
          simp only [hpar, hj0, hj1, hj2, hj, dite_false, dite_true] at h1
          have hadd : (⟨j.val + 1, by omega⟩ : Fin h) = i := by
            ext; dsimp; omega
          rw [hadd] at h1
          exact h1
        have h2' : u j + u i = u i := by
          unfold mapT at h2
          simp only [hpar, hi0, hi1, hi2, hi, dite_false] at h2
          exact h2
        have h3 : u j + u i + u i = u i + u i := congrArg (fun z => z + u i) h2'
        rw [add_assoc, zmod2_add_self, add_zero] at h3
        rw [h1', h3]
        rfl

lemma mapT_bijective (h : Nat) (hh : 2 ≤ h) : Function.Bijective (mapT h hh) := by
  refine (Fintype.bijective_iff_injective_and_card (mapT h hh)).mpr ⟨?_, rfl⟩
  intro u v huv
  have h1 : mapT h hh (u + v) = 0 := by
    rw [mapT_add, huv, vec_add_self]
  exact (vec_add_eq_zero_iff u v).mp (mapT_eq_zero h hh (u + v) h1)

lemma id_add_mapT_bijective (h : Nat) (hh : 2 ≤ h) :
    Function.Bijective (fun u : W h => u + mapT h hh u) := by
  refine (Fintype.bijective_iff_injective_and_card (fun u : W h => u + mapT h hh u)).mpr ⟨?_, rfl⟩
  intro u v huv
  dsimp only at huv
  have h1 : (u + v) + mapT h hh (u + v) = 0 := by
    calc
      (u + v) + mapT h hh (u + v) = (u + mapT h hh u) + (v + mapT h hh v) := by
        rw [mapT_add]; abel
      _ = 0 := by rw [huv, vec_add_self]
  have h2 : mapT h hh (u + v) = u + v := ((vec_add_eq_zero_iff (u + v) (mapT h hh (u + v))).mp h1).symm
  exact (vec_add_eq_zero_iff u v).mp (mapT_eq_self h hh (u + v) h2)

lemma part2 (h : Nat) (hh : 2 ≤ h) :
    let m := 2 ^ h - 1
    let oddLabels := fun (n m : Nat) (a b : Fin m → W n) =>
      (Finset.univ : Finset (W n)).filter (fun v =>
        ((Finset.univ : Finset (Fin m)).filter (fun i =>
          v ∈ ({a i, b i, a i + b i} : Finset (W n)))).card % 2 = 1)
    ∃ a b : Fin m → W h, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) ∧
      oddLabels h m a b = (Finset.univ : Finset (W h)).erase 0 ∧
      ∀ x : W h, ((Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ 0)).card = if x = 0 then 0 else 2 ^ (h - 2) := by
  intro m oddLabels
  let NZ : Finset (W h) := (Finset.univ : Finset (W h)).erase 0
  have hNZ_card : Fintype.card ↥NZ = m := by
    rw [Fintype.card_coe]
    simp [NZ, m, Finset.card_erase_of_mem]
  let enum : Fin m ≃ ↥NZ := (Fintype.equivFinOfCardEq hNZ_card).symm
  let a : Fin m → W h := fun i => (enum i).val
  let b : Fin m → W h := fun i => mapT h hh (enum i).val
  have ha_ne : ∀ i : Fin m, a i ≠ 0 := fun i => (Finset.mem_erase.mp (enum i).property).1
  have hnd : ∀ i : Fin m, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i := by
    intro i
    refine ⟨ha_ne i, ?_, ?_⟩
    · intro hb0
      exact ha_ne i (mapT_eq_zero h hh (a i) hb0)
    · intro hab
      exact ha_ne i (mapT_eq_self h hh (a i) hab.symm)
  let eT : W h ≃ W h := Equiv.ofBijective (mapT h hh) (mapT_bijective h hh)
  let eIT : W h ≃ W h := Equiv.ofBijective (fun u => u + mapT h hh u) (id_add_mapT_bijective h hh)
  have hodd : oddLabels h m a b = NZ := by
    ext v
    by_cases hv : v = 0
    · subst hv
      simp only [oddLabels, NZ, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false]
      have hemp : (Finset.univ : Finset (Fin m)).filter (fun i =>
          (0 : W h) ∈ ({a i, b i, a i + b i} : Finset (W h))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _
        rcases hnd i with ⟨ha0, hb0, hab⟩
        have hab0 : a i + b i ≠ 0 := fun h0 => hab ((vec_add_eq_zero_iff (a i) (b i)).mp h0)
        simp [ha0.symm, hb0.symm, hab0.symm]
      rw [hemp]
      simp
    · have hvNZ : v ∈ NZ := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
      have hv2_ne : eT.symm v ≠ 0 := by
        intro h0
        have : v = mapT h hh 0 := by
          have := eT.apply_symm_apply v
          rw [h0] at this
          exact this.symm
        rw [mapT_zero] at this
        exact hv this
      have hv3_ne : eIT.symm v ≠ 0 := by
        intro h0
        have : v = 0 + mapT h hh 0 := by
          have := eIT.apply_symm_apply v
          rw [h0] at this
          exact this.symm
        rw [mapT_zero, add_zero] at this
        exact hv this
      let u1 : ↥NZ := ⟨v, hvNZ⟩
      let u2 : ↥NZ := ⟨eT.symm v, Finset.mem_erase.mpr ⟨hv2_ne, Finset.mem_univ _⟩⟩
      let u3 : ↥NZ := ⟨eIT.symm v, Finset.mem_erase.mpr ⟨hv3_ne, Finset.mem_univ _⟩⟩
      have h12 : u1 ≠ u2 := by
        intro hEq
        have hval : v = eT.symm v := congrArg Subtype.val hEq
        have hT : mapT h hh v = v := by
          have := eT.apply_symm_apply v
          rw [← hval] at this
          exact this
        exact hv (mapT_eq_self h hh v hT)
      have h13 : u1 ≠ u3 := by
        intro hEq
        have hval : v = eIT.symm v := congrArg Subtype.val hEq
        have hIT : v + mapT h hh v = v := by
          have := eIT.apply_symm_apply v
          rw [← hval] at this
          exact this
        have hT0 : mapT h hh v = 0 := by
          have h3 : v + (v + mapT h hh v) = v + v := congrArg (fun z => v + z) hIT
          rw [← add_assoc, vec_add_self, zero_add] at h3
          exact h3
        exact hv (mapT_eq_zero h hh v hT0)
      have h23 : u2 ≠ u3 := by
        intro hEq
        have hval : eT.symm v = eIT.symm v := congrArg Subtype.val hEq
        have h1 : mapT h hh (eT.symm v) = v := eT.apply_symm_apply v
        have h2 : eT.symm v + mapT h hh (eT.symm v) = v := by
          rw [hval]
          exact eIT.apply_symm_apply v
        have h3 : eT.symm v = 0 := by
          rw [h1] at h2
          have h4 : (eT.symm v + v) + v = v + v := congrArg (fun z => z + v) h2
          rw [add_assoc, vec_add_self, add_zero] at h4
          exact h4
        exact hv2_ne h3
      have hflt : (Finset.univ : Finset (Fin m)).filter (fun i =>
          v ∈ ({a i, b i, a i + b i} : Finset (W h))) =
          {enum.symm u1, enum.symm u2, enum.symm u3} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro (hEq | hEq | hEq)
          · left
            have : enum i = u1 := Subtype.ext hEq.symm
            exact (enum.symm_apply_eq.mpr this.symm).symm
          · right; left
            have hT : eT (enum i).val = v := hEq.symm
            have : enum i = u2 := Subtype.ext (eT.symm_apply_eq.mpr hT.symm).symm
            exact (enum.symm_apply_eq.mpr this.symm).symm
          · right; right
            have hIT : eIT (enum i).val = v := hEq.symm
            have : enum i = u3 := Subtype.ext (eIT.symm_apply_eq.mpr hIT.symm).symm
            exact (enum.symm_apply_eq.mpr this.symm).symm
        · rintro (rfl | rfl | rfl)
          · left; simp [a, u1]
          · right; left
            change v = eT (enum (enum.symm u2)).val
            simp [u2]
          · right; right
            change v = eIT (enum (enum.symm u3)).val
            simp [u3]
      have hcard3 : ({enum.symm u1, enum.symm u2, enum.symm u3} : Finset (Fin m)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [enum.symm.injective.ne h23]
        · simp [enum.symm.injective.ne h12, enum.symm.injective.ne h13]
      simp only [oddLabels, Finset.mem_filter, Finset.mem_univ, true_and, hvNZ, iff_true]
      rw [hflt, hcard3]
  have hcount : ∀ x : W h, ((Finset.univ : Finset (Fin m)).filter (fun i =>
      dotProduct (a i) x * dotProduct (b i) x ≠ 0)).card = if x = 0 then 0 else 2 ^ (h - 2) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · simp only [hx, ite_false]
      have hbij : ((Finset.univ : Finset (Fin m)).filter (fun i =>
          dotProduct (a i) x * dotProduct (b i) x ≠ 0)).card =
          ((Finset.univ : Finset (W h)).filter (fun u =>
            dotProduct u x * dotProduct (mapT h hh u) x ≠ 0)).card := by
        refine Finset.card_bij (fun i _ => a i) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact hi
        · intro i₁ _ i₂ _ hEq
          exact enum.injective (Subtype.ext hEq)
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          have hu0 : u ≠ 0 := by
            intro h0
            subst h0
            simp at hu
          have huNZ : u ∈ NZ := Finset.mem_erase.mpr ⟨hu0, Finset.mem_univ u⟩
          refine ⟨enum.symm ⟨u, huNZ⟩, ?_, by simp [a]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [a, b] using hu
      rw [hbij]
      have h4 : 4 * (((Finset.univ : Finset (W h)).filter (fun u =>
          dotProduct u x * dotProduct (mapT h hh u) x ≠ 0)).card : Int) = (2 : Int) ^ h := by
        have hlhs : 4 * (((Finset.univ : Finset (W h)).filter (fun u =>
            dotProduct u x * dotProduct (mapT h hh u) x ≠ 0)).card : Int) =
            ∑ u : W h, 4 * (if dotProduct u x * dotProduct (mapT h hh u) x ≠ 0 then (1 : Int) else 0) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
        rw [hlhs]
        have hterm : ∀ u : W h,
            4 * (if dotProduct u x * dotProduct (mapT h hh u) x ≠ 0 then (1 : Int) else 0) =
              1 - chi x u - chi x (mapT h hh u) + chi x (u + mapT h hh u) := by
          intro u
          rw [four_mul_prod_eq]
          unfold chi
          rw [dotProduct_comm u x, dotProduct_comm (mapT h hh u) x, dotProduct_add]
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        have hs1 : (∑ _u : W h, (1 : Int)) = (2 : Int) ^ h := by
          simp [card_W]
        have hs2 : (∑ u : W h, chi x u) = 0 := by
          simp [sum_chi_eq, hx]
        have hs3 : (∑ u : W h, chi x (mapT h hh u)) = 0 := by
          have h1 : (∑ u : W h, chi x (eT u)) = ∑ w : W h, chi x w :=
            Fintype.sum_equiv eT _ _ (fun _ => rfl)
          change (∑ u : W h, chi x (eT u)) = 0
          rw [h1, hs2]
        have hs4 : (∑ u : W h, chi x (u + mapT h hh u)) = 0 := by
          have h1 : (∑ u : W h, chi x (eIT u)) = ∑ w : W h, chi x w :=
            Fintype.sum_equiv eIT _ _ (fun _ => rfl)
          change (∑ u : W h, chi x (eIT u)) = 0
          rw [h1, hs2]
        rw [hs1, hs2, hs3, hs4]
        ring
      have hpow : (2 : Int) ^ h = 4 * (2 : Int) ^ (h - 2) := by
        have hsplit : h = 2 + (h - 2) := by omega
        conv_lhs => rw [hsplit, pow_add]
        norm_num
      rw [hpow] at h4
      have h4' : (((Finset.univ : Finset (W h)).filter (fun u =>
          dotProduct u x * dotProduct (mapT h hh u) x ≠ 0)).card : Int) = (2 : Int) ^ (h - 2) := by
        omega
      exact_mod_cast h4'
  exact ⟨a, b, hnd, hodd, hcount⟩

end PEqualNP.Outside.L_lib_978

theorem PEqualNP.Outside.L_lib_978 : (let F := ZMod 2
let oddLabels := fun (n m : Nat) (a b : Fin m → (Fin n → F)) =>
  (Finset.univ : Finset (Fin n → F)).filter (fun v =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => v ∈ ({a i, b i, a i+b i} : Finset (Fin n → F)))).card % 2 = 1)
(∀ (n e : Nat), 0 < e →
  let m := 4*e-1
  let W := Fin n → F
  let I := Fin m
  ∀ (a b P : I → W) (d : I → F),
    (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let errs := fun x : W => ((Finset.univ : Finset I).filter (fun i =>
      dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x+d i)).card
    (∀ x, errs x ≤ e) →
    let S := insert (0 : W) (oddLabels n m a b)
    let plane := fun i : I => ({0, a i, b i, a i+b i} : Finset W)
    (∀ v ∈ S, ∀ w ∈ S, v+w ∈ S) ∧ 4 ≤ S.card ∧
    (((∀ i, P i ∈ plane i) ∧ ∃ z : W, ∀ x : W,
       e-errs x = if ∀ v ∈ S, dotProduct v x = dotProduct v z then S.card / 4 else 0) ∨
     (S.card = 8 ∧ (∀ x, errs x = e) ∧ ∃ j : I, P j ∉ plane j ∧
       (∀ i, i ≠ j → P i ∈ plane i) ∧ S = plane j ∪ (plane j).image (fun v => P j+v)))) ∧
(∀ h : Nat, 2 ≤ h →
  let m := 2^h-1
  let W := Fin h → F
  ∃ a b : Fin m → W, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) ∧
    oddLabels h m a b = (Finset.univ : Finset W).erase 0 ∧
    ∀ x : W, ((Finset.univ : Finset (Fin m)).filter (fun i =>
      dotProduct (a i) x * dotProduct (b i) x ≠ 0)).card = if x = 0 then 0 else 2^(h-2))) := by
  exact ⟨fun n e he => PEqualNP.Outside.L_lib_978.part1 n e he,
    fun h hh => PEqualNP.Outside.L_lib_978.part2 h hh⟩
