import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_979_aux

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


def totalCoeff {n m : Nat} (a b P : Fin m → W n) (d : Fin m → F) (e : Nat) (v : W n) : Int :=
  (if v = 0 then (4 * e : Int) else 0) - ∑ i : Fin m, rowCoeff (a i) (b i) (P i) (d i) v

lemma errs_fourier {n m : Nat} (a b P : Fin m → W n) (d : Fin m → F) (e : Nat) (x : W n) :
    (4 * e : Int) - 4 * (((Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : Int) =
      ∑ v : W n, totalCoeff a b P d e v * chi v x := by
  have herr_sum : 4 * (((Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : Int) =
      ∑ i : Fin m, ∑ v : W n, rowCoeff (a i) (b i) (P i) (d i) v * chi v x := by
    have h1 : (((Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : Int) =
        ∑ i : Fin m,
          (if dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i then (1 : Int) else 0) := by
      rw [Finset.sum_boole]
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (sum_rowCoeff_chi (a i) (b i) (P i) (d i) x).symm)
  have h2 : (∑ v : W n, totalCoeff a b P d e v * chi v x) =
      (4 * e : Int) - ∑ v : W n, (∑ i : Fin m, rowCoeff (a i) (b i) (P i) (d i) v) * chi v x := by
    have hsplit : ∀ v : W n, totalCoeff a b P d e v * chi v x =
        (if v = 0 then (4 * e : Int) * chi v x else 0) -
          (∑ i : Fin m, rowCoeff (a i) (b i) (P i) (d i) v) * chi v x := by
      intro v; unfold totalCoeff; split_ifs <;> ring
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib]
    simp [chi_zero_left]
  have hswap : (∑ v : W n, (∑ i : Fin m, rowCoeff (a i) (b i) (P i) (d i) v) * chi v x) =
      ∑ i : Fin m, ∑ v : W n, rowCoeff (a i) (b i) (P i) (d i) v * chi v x := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  rw [h2, hswap, ← herr_sum]

lemma sum_chi_subgroup {n : Nat} (S : Finset (W n))
    (h0 : (0 : W n) ∈ S) (hadd : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S) (x : W n) :
    (∑ v ∈ S, chi v x) = if ∀ v ∈ S, dotProduct v x = 0 then (S.card : Int) else 0 := by
  by_cases hdot : ∀ v ∈ S, dotProduct v x = 0
  · rw [if_pos hdot]
    have hone : ∀ v ∈ S, chi v x = 1 := fun v hv => by unfold chi; rw [hdot v hv, sgn_zero]
    rw [Finset.sum_congr rfl hone]
    simp
  · rw [if_neg hdot]
    push Not at hdot
    rcases hdot with ⟨u, huS, hux⟩
    have hux1 : dotProduct u x = 1 := (zmod2_ne_zero_iff _).mp hux
    have hchiu : chi u x = -1 := by unfold chi; rw [hux1, sgn_one]
    have hsum_shift : (∑ v ∈ S, chi (v + u) x) = ∑ v ∈ S, chi v x := by
      refine Finset.sum_bij (fun v _ => v + u) ?_ ?_ ?_ ?_
      · intro v hv; exact hadd v hv u huS
      · intro v₁ _ v₂ _ h; exact add_right_cancel h
      · intro v hv
        exact ⟨v + u, hadd v hv u huS, by rw [add_assoc, vec_add_self, add_zero]⟩
      · intro v _; rfl
    have hneg : (∑ v ∈ S, chi (v + u) x) = - ∑ v ∈ S, chi v x := by
      have hterm : ∀ v ∈ S, chi (v + u) x = - chi v x := by
        intro v _
        rw [chi_add_left, hchiu]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    linarith

lemma part1_strong (n e : Nat) (he : 0 < e) :
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
      (((∀ i, P i ∈ plane i) ∧ (∀ i, rowCoeff (a i) (b i) (P i) (d i) 0 = 1) ∧
          ∃ z : W n, ∀ v : W n, totalCoeff a b P d e v = if v ∈ S then chi v z else 0) ∨
       (S.card = 8 ∧ (∀ v : W n, totalCoeff a b P d e v = 0) ∧ ∃ j : I, P j ∉ plane j ∧
         (∀ i, i ≠ j → P i ∈ plane i) ∧
         (∀ i, i ≠ j → rowCoeff (a i) (b i) (P i) (d i) 0 = 1) ∧
         S = plane j ∪ (plane j).image (fun v => P j + v))) := by
  intro m I a b P d hnd errs herrs oddLabels S plane
  let g : W n → Int := fun x => (4 * e : Int) - 4 * (errs x : Int)
  let c : W n → Int := totalCoeff a b P d e
  have hg_nonneg : ∀ x : W n, 0 ≤ g x := by
    intro x; have hx := herrs x; unfold g; omega
  have hg_fourier : ∀ x : W n, g x = ∑ v : W n, c v * chi v x :=
    fun x => errs_fourier a b P d e x
  have hc_inv : ∀ u : W n, (∑ x : W n, g x * chi u x) = (2 : Int) ^ n * c u :=
    fun u => fourier_inv g c hg_fourier u
  have hsum_g : (∑ x : W n, g x) = (2 : Int) ^ n * c 0 := by
    have h0 := hc_inv 0; simp only [chi_zero_left, mul_one] at h0; exact h0
  have h2pos : (0 : Int) < (2 : Int) ^ n := by positivity
  have hc0_nonneg : 0 ≤ c 0 := by
    have hnn : 0 ≤ ∑ x : W n, g x := Finset.sum_nonneg (fun x _ => hg_nonneg x)
    rw [hsum_g] at hnn; nlinarith
  have hc0_def : c 0 = (4 * e : Int) - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0 := by
    dsimp only [c, totalCoeff]; simp; rfl
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
    calc (m : Int) + (Bad.card : Int)
        = ∑ i : I, ((1 : Int) + (if i ∈ Bad then 1 else 0)) := by
            rw [Finset.sum_add_distrib]; simp [I]
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
    have hall_row0 : ∀ i : I, rowCoeff (a i) (b i) (P i) (d i) 0 = 1 := by
      have hsum_eq : (∑ i : I, (rowCoeff (a i) (b i) (P i) (d i) 0 - 1)) = 0 := by
        rw [Finset.sum_sub_distrib]
        simp only [I, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
        linarith [hc0_def, hc0_eq, hm]
      have hnn : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ rowCoeff (a i) (b i) (P i) (d i) 0 - 1 := by
        intro i _
        have := (rowCoeff_in_plane (d i) (hnd i) (hall_plane i)).1
        omega
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_eq i (Finset.mem_univ i)
      omega
    have hsum_g_eq : (∑ x : W n, g x) = (2 : Int) ^ n := by
      rw [hsum_g, hc0_eq, mul_one]
    have hex_z : ∃ z : W n, 0 < g z := by
      by_contra h; push Not at h
      have hzero : ∀ x : W n, g x = 0 := fun x => le_antisymm (h x) (hg_nonneg x)
      have hsum0 : (∑ x : W n, g x) = 0 := Finset.sum_eq_zero (fun x _ => hzero x)
      linarith
    rcases hex_z with ⟨z, hz⟩
    have habs_c : ∀ v : W n, |c v| ≤ 1 := by
      intro v
      have hle : (2 : Int) ^ n * |c v| ≤ (2 : Int) ^ n := by
        calc (2 : Int) ^ n * |c v|
            = |(2 : Int) ^ n * c v| := by rw [abs_mul, abs_of_pos h2pos]
          _ = |∑ x : W n, g x * chi v x| := by rw [← hc_inv v]
          _ ≤ ∑ x : W n, |g x * chi v x| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x : W n, g x := Finset.sum_congr rfl (fun x _ => by
                rw [abs_mul, abs_of_nonneg (hg_nonneg x), abs_chi v x, mul_one])
          _ = (2 : Int) ^ n := hsum_g_eq
      nlinarith
    have hc_mem_S : ∀ v : W n, c v ≠ 0 ↔ v ∈ S := by
      intro v
      by_cases hv : v = 0
      · subst hv; simp [hc0_eq, S]
      · have hcv : c v = - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v := by
          dsimp only [c, totalCoeff]; simp [hv]; rfl
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
          rw [h1]; simp [cnt, Finset.sum_boole]
        have hbound : -1 ≤ c v ∧ c v ≤ 1 := abs_le.mp (habs_c v)
        have hvS : v ∈ S ↔ cnt % 2 = 1 := by
          change v ∈ insert (0 : W n) oddLabels ↔ cnt % 2 = 1
          rw [Finset.mem_insert]; simp only [hv, false_or]
          change v ∈ (Finset.univ : Finset (W n)).filter _ ↔ cnt % 2 = 1
          rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl
        rw [hvS]; constructor <;> intro h <;> omega
    have hc_val_on_pos : ∀ v ∈ S, ∀ x : W n, 0 < g x → chi v x = c v := by
      intro v hvS
      have hcv_ne : c v ≠ 0 := (hc_mem_S v).mpr hvS
      have hbound : -1 ≤ c v ∧ c v ≤ 1 := abs_le.mp (habs_c v)
      have hcv_pm : c v = 1 ∨ c v = -1 := by omega
      have hcv_sq : c v * c v = 1 := by rcases hcv_pm with h | h <;> rw [h] <;> norm_num
      have hterm_nn : ∀ x : W n, 0 ≤ g x * (1 - c v * chi v x) := by
        intro x; have hgx := hg_nonneg x; have hchi := chi_eq_one_or_neg_one v x
        rcases hcv_pm with h1 | h1 <;> rcases hchi with h2 | h2 <;> rw [h1, h2] <;> nlinarith
      have hsum_zero : (∑ x : W n, g x * (1 - c v * chi v x)) = 0 := by
        have h1 : ∀ x : W n, g x * (1 - c v * chi v x) = g x - c v * (g x * chi v x) :=
          fun x => by ring
        simp_rw [h1]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_g_eq, hc_inv v]
        calc (2 : Int) ^ n - c v * ((2 : Int) ^ n * c v)
            = (2 : Int) ^ n * (1 - c v * c v) := by ring
          _ = 0 := by rw [hcv_sq]; ring
      have hall_zero : ∀ x : W n, g x * (1 - c v * chi v x) = 0 := fun x =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hterm_nn y)).mp hsum_zero x (Finset.mem_univ x)
      intro x hgx
      have hxz := hall_zero x
      have h1 : 1 - c v * chi v x = 0 := by rcases mul_eq_zero.mp hxz with h | h; linarith; exact h
      have h2 : c v * chi v x = 1 := by linarith
      calc chi v x = (c v * c v) * chi v x := by rw [hcv_sq, one_mul]
        _ = c v * (c v * chi v x) := by ring
        _ = c v := by rw [h2, mul_one]
    have hc_eq_chi_z : ∀ v ∈ S, c v = chi v z := fun v hvS => (hc_val_on_pos v hvS z hz).symm
    have hc_formula : ∀ v : W n, c v = if v ∈ S then chi v z else 0 := by
      intro v
      by_cases hv : v ∈ S
      · rw [if_pos hv]; exact hc_eq_chi_z v hv
      · rw [if_neg hv]; by_contra hne; exact hv ((hc_mem_S v).mp hne)
    have hS_closed : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S := by
      intro v hvS w hwS
      have h1 : (2 : Int) ^ n * c (v + w) = ∑ x : W n, g x * chi (v + w) x := (hc_inv (v + w)).symm
      have h2 : ∀ x : W n, g x * chi (v + w) x = g x * (chi v z * chi w z) := by
        intro x
        by_cases hgx : g x = 0
        · simp [hgx]
        · have hpos : 0 < g x := lt_of_le_of_ne (hg_nonneg x) (Ne.symm hgx)
          rw [chi_add_left, hc_val_on_pos v hvS x hpos, hc_val_on_pos w hwS x hpos,
            hc_eq_chi_z v hvS, hc_eq_chi_z w hwS]
      simp_rw [h2, ← Finset.sum_mul, hsum_g_eq] at h1
      have hcvw : c (v + w) = chi v z * chi w z := mul_left_cancel₀ (ne_of_gt h2pos) h1
      have hne : c (v + w) ≠ 0 := by rw [hcvw]; exact mul_ne_zero (chi_ne_zero v z) (chi_ne_zero w z)
      exact (hc_mem_S (v + w)).mp hne
    have hgz_eq : g z = (S.card : Int) := by
      rw [hg_fourier z]
      have hsub : (∑ v : W n, c v * chi v z) = ∑ v ∈ S, c v * chi v z := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) (fun v _ hv => ?_)
        rw [hc_formula v, if_neg hv, zero_mul]
      rw [hsub]
      have hone : ∀ v ∈ S, c v * chi v z = 1 := fun v hv => by
        rw [hc_eq_chi_z v hv, chi_mul_self]
      rw [Finset.sum_congr rfl hone]; simp
    have h4le : 4 ≤ S.card := by
      have hze := herrs z
      unfold g at hgz_eq hz
      omega
    exact ⟨hS_closed, h4le, Or.inl ⟨hall_plane, hall_row0, z, hc_formula⟩⟩
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
    have hother_row0 : ∀ i : I, i ≠ j → rowCoeff (a i) (b i) (P i) (d i) 0 = 1 := by
      have hj2 : rowCoeff (a j) (b j) (P j) (d j) 0 = 2 :=
        (rowCoeff_not_in_plane (d j) (hnd j) hj_not).1
      have hsum_all : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) 0) = (4 * e : Int) := by omega
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), hj2] at hsum_all
      have hsum_eq : (∑ i ∈ Finset.univ.erase j, (rowCoeff (a i) (b i) (P i) (d i) 0 - 1)) = 0 := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, I]
        have hm1 : ((m - 1 : Nat) : Int) = 4 * (e : Int) - 2 := by omega
        linarith [hsum_all, hm1]
      have hnn : ∀ i ∈ Finset.univ.erase j, 0 ≤ rowCoeff (a i) (b i) (P i) (d i) 0 - 1 := by
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        have := (rowCoeff_in_plane (d i) (hnd i) (hother_in i hij)).1
        omega
      intro i hij
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_eq i
        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
      omega
    have hsum_g_zero : (∑ x : W n, g x) = 0 := by rw [hsum_g, hc0_eq, mul_zero]
    have hg_zero : ∀ x : W n, g x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hg_nonneg y)).mp hsum_g_zero x (Finset.mem_univ x)
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
      · subst hv; simp [S, plane]
      · have hsum_row0 : (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) = 0 := by
          have hcv := hc_zero v
          simp only [c, totalCoeff, hv, ite_false, zero_sub, neg_eq_zero] at hcv
          exact hcv
        have hsplit_row : rowCoeff (a j) (b j) (P j) (d j) v +
            ∑ i ∈ Finset.univ.erase j, rowCoeff (a i) (b i) (P i) (d i) v = 0 := by
          rw [Finset.add_sum_erase Finset.univ (fun i => rowCoeff (a i) (b i) (P i) (d i) v) (Finset.mem_univ j)]; exact hsum_row0
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
          have h1 : (cnt : Int) = ∑ i : I, if v ∈ triOf (a i) (b i) then (1 : Int) else 0 := by
            rw [Finset.sum_boole]; congr 2
          rw [h1, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        have hv_plane_iff : v ∈ plane j ↔ v ∈ triOf (a j) (b j) := by simp [plane, triOf, hv]
        have hvS : v ∈ S ↔ cnt % 2 = 1 := by
          change v ∈ insert (0 : W n) oddLabels ↔ cnt % 2 = 1
          rw [Finset.mem_insert]; simp only [hv, false_or]
          change v ∈ (Finset.univ : Finset (W n)).filter _ ↔ cnt % 2 = 1
          rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl
        rw [hvS, Finset.mem_union, hv_plane_iff]
        by_cases h1 : v ∈ triOf (a j) (b j)
        · have h2 : v ∉ (plane j).image (fun u => P j + u) := fun hmem =>
            Finset.disjoint_left.mp hdisj (hv_plane_iff.mpr h1) hmem
          simp only [h1, h2, ite_true, ite_false, true_or, iff_true] at hj_mod hcnt_split ⊢; omega
        · by_cases h2 : v ∈ (plane j).image (fun u => P j + u)
          · simp only [h1, h2, ite_true, ite_false, or_true, iff_true] at hj_mod hcnt_split ⊢; omega
          · simp only [h1, h2, ite_false, or_self, iff_false] at hj_mod hcnt_split ⊢; omega
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
      · left; exact planeOf_add_mem hv1 hw1
      · right; rcases Finset.mem_image.mp hw2 with ⟨u, hu, rfl⟩
        exact Finset.mem_image.mpr ⟨v + u, planeOf_add_mem hv1 hu, by abel⟩
      · right; rcases Finset.mem_image.mp hv2 with ⟨u, hu, rfl⟩
        exact Finset.mem_image.mpr ⟨u + w, planeOf_add_mem hu hw1, by abel⟩
      · left
        rcases Finset.mem_image.mp hv2 with ⟨u₁, hu₁, rfl⟩
        rcases Finset.mem_image.mp hw2 with ⟨u₂, hu₂, rfl⟩
        have heq : (P j + u₁) + (P j + u₂) = u₁ + u₂ := by
          calc (P j + u₁) + (P j + u₂) = (P j + P j) + (u₁ + u₂) := by abel
            _ = 0 + (u₁ + u₂) := by rw [vec_add_self]
            _ = u₁ + u₂ := zero_add _
        rw [heq]; exact planeOf_add_mem hu₁ hu₂
    exact ⟨hS_closed, by omega, Or.inr ⟨hS_card, hc_zero, j, hj_not, hother_in, hother_row0, hS_eq⟩⟩

-- Part A: Abstract matching count theorem for the port-and-slot gadget

def pairMate (x : Nat) : Nat := if x % 2 = 0 then x + 1 else x - 1

def sameLoc (a b : Nat) : Prop := a ≠ b ∧ (a = 4 ∨ b = 4 ∨ a / 2 = b / 2)

lemma pairMate_self (x : Nat) : pairMate (pairMate x) = x := by
  unfold pairMate; split_ifs <;> omega

lemma pairMate_ne (x : Nat) : pairMate x ≠ x := by
  unfold pairMate; split_ifs <;> omega

lemma pairMate_div2 (x : Nat) : pairMate x / 2 = x / 2 := by
  unfold pairMate; split_ifs <;> omega

lemma sameLoc_of_lt4 {a b : Nat} (ha : a < 4) (hb : b < 4) (h : sameLoc a b) :
    b = pairMate a := by
  rcases h with ⟨hne, h4 | h4 | hdiv⟩
  · omega
  · omega
  · unfold pairMate; split_ifs <;> omega

def locPartner (np : Nat) (A : Finset Nat) (x : Nat) : Nat :=
  if x = 4 then
    let U := (Finset.range np).filter (fun y => y ∉ A ∧ (pairMate y ≥ np ∨ pairMate y ∈ A))
    if h : U.Nonempty then U.min' h else 4
  else if pairMate x < np ∧ pairMate x ∉ A then
    pairMate x
  else
    4

lemma local_gadget_unique (np : Nat) (hnp : np = 3 ∨ np = 4) (A : Finset Nat)
    (hA : A ⊆ Finset.range np) (g : Nat → Nat)
    (hg : ∀ x ∈ insert 4 (Finset.range np \ A),
      g x ∈ insert 4 (Finset.range np \ A) ∧ g (g x) = x ∧ sameLoc x (g x)) :
    A.card % 2 = (if np = 4 then 1 else 0) ∧
    ∀ x ∈ insert 4 (Finset.range np \ A), g x = locPartner np A x := by
  let U := Finset.range np \ A
  let L := insert 4 U
  have h4L : 4 ∈ L := Finset.mem_insert_self 4 U
  have h4U : 4 ∉ U := by
    intro h; have := Finset.mem_range.mp (Finset.mem_sdiff.mp h).1; omega
  rcases hg 4 h4L with ⟨hg4L, hgg4, hsame4⟩
  have hg4_ne : g 4 ≠ 4 := hsame4.1.symm
  have hg4U : g 4 ∈ U := (Finset.mem_insert.mp hg4L).resolve_left hg4_ne
  set u := g 4
  have hgu : g u = 4 := hgg4
  have hpair_other : ∀ x ∈ U.erase u, pairMate x ∈ U.erase u ∧ g x = pairMate x := by
    intro x hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    have hxU : x ∈ U := (Finset.mem_erase.mp hx).2
    have hxlt : x < 4 := by have := Finset.mem_range.mp (Finset.mem_sdiff.mp hxU).1; omega
    rcases hg x (Finset.mem_insert_of_mem hxU) with ⟨hgxL, hggx, hsamex⟩
    have hgx_ne4 : g x ≠ 4 := by
      intro h4
      have : x = u := by rw [← hggx, h4]
      exact hxu this
    have hgxU : g x ∈ U := (Finset.mem_insert.mp hgxL).resolve_left hgx_ne4
    have hgxlt : g x < 4 := by have := Finset.mem_range.mp (Finset.mem_sdiff.mp hgxU).1; omega
    have hgx_eq : g x = pairMate x := sameLoc_of_lt4 hxlt hgxlt hsamex
    have hgx_neu : g x ≠ u := by
      intro heq
      have : x = 4 := by rw [← hggx, heq, hgu]
      omega
    exact ⟨Finset.mem_erase.mpr ⟨hgx_eq ▸ hgx_neu, hgx_eq ▸ hgxU⟩, hgx_eq⟩
  have hu_unpaired : pairMate u ≥ np ∨ pairMate u ∈ A := by
    by_contra hcon
    push Not at hcon
    have hpmU : pairMate u ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hcon.1, hcon.2⟩
    have hpm_erase : pairMate u ∈ U.erase u := Finset.mem_erase.mpr ⟨pairMate_ne u, hpmU⟩
    have hgpm := (hpair_other (pairMate u) hpm_erase).2
    rw [pairMate_self] at hgpm
    have : pairMate u = 4 := by
      have := (hg (pairMate u) (Finset.mem_insert_of_mem hpmU)).2.1
      rw [hgpm, hgu] at this
      exact this.symm
    omega
  have hSng : (Finset.range np).filter (fun y => y ∉ A ∧ (pairMate y ≥ np ∨ pairMate y ∈ A)) = {u} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hylt, hyA, hyun⟩
      have hyU : y ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hylt, hyA⟩
      by_contra hyu
      have hpm := (hpair_other y (Finset.mem_erase.mpr ⟨hyu, hyU⟩)).1
      have hpmU := (Finset.mem_erase.mp hpm).2
      have h1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hpmU).1
      have h2 := (Finset.mem_sdiff.mp hpmU).2
      rcases hyun with hge | hmem
      · omega
      · exact h2 hmem
    · rintro rfl
      exact ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp hg4U).1, (Finset.mem_sdiff.mp hg4U).2, hu_unpaired⟩
  have hUodd : U.card % 2 = 1 := by
    let E := U.erase u
    have hcardU : U.card = E.card + 1 := by
      have h1 := Finset.card_erase_add_one (s := U) (a := u) hg4U
      change E.card + 1 = U.card at h1
      omega
    have hEeven : E.card % 2 = 0 := by
      let E0 := E.filter (fun x => x % 2 = 0)
      let E1 := E.filter (fun x => x % 2 ≠ 0)
      have hbij : E0.card = E1.card := by
        refine Finset.card_bij (fun x _ => pairMate x) ?_ ?_ ?_
        · intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxE, hx0⟩
          have hpm := (hpair_other x hxE).1
          refine Finset.mem_filter.mpr ⟨hpm, ?_⟩
          unfold pairMate; simp [hx0]; omega
        · intro x₁ _ x₂ _ h
          have := congrArg pairMate h; rwa [pairMate_self, pairMate_self] at this
        · intro y hy
          rcases Finset.mem_filter.mp hy with ⟨hyE, hy1⟩
          refine ⟨pairMate y, ?_, pairMate_self y⟩
          refine Finset.mem_filter.mpr ⟨(hpair_other y hyE).1, ?_⟩
          unfold pairMate; split_ifs at * <;> omega
      have hsplit : E.card = E0.card + E1.card := by
        have hd : Disjoint E0 E1 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
        have hu : E = E0 ∪ E1 := by
          ext x; simp only [E0, E1, Finset.mem_union, Finset.mem_filter]
          by_cases h : x % 2 = 0 <;> simp [h]
        rw [hu, Finset.card_union_of_disjoint hd]
      omega
    omega
  have hAcard : A.card + U.card = np := by
    have := Finset.card_sdiff_add_card_eq_card hA
    change U.card + A.card = (Finset.range np).card at this
    rw [Finset.card_range] at this
    omega
  constructor
  · rcases hnp with rfl | rfl <;> simp <;> omega
  · intro x hx
    unfold locPartner
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp only [ite_true, hSng]
      have hne : ({u} : Finset Nat).Nonempty := Finset.singleton_nonempty u
      rw [dif_pos hne, Finset.min'_singleton]
    · have hxne4 : x ≠ 4 := fun h => h4U (h ▸ hxU)
      rw [if_neg hxne4]
      by_cases hxu : x = u
      · subst hxu
        have hnot : ¬ (pairMate u < np ∧ pairMate u ∉ A) := by
          rintro ⟨h1, h2⟩; rcases hu_unpaired with h3 | h3 <;> [omega; exact h2 h3]
        rw [if_neg hnot]; exact hgu
      · have hp := hpair_other x (Finset.mem_erase.mpr ⟨hxu, hxU⟩)
        have hpmU := (Finset.mem_erase.mp hp.1).2
        have hok : pairMate x < np ∧ pairMate x ∉ A :=
          ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp hpmU).1, (Finset.mem_sdiff.mp hpmU).2⟩
        rw [if_pos hok]; exact hp.2

lemma local_gadget_valid (np : Nat) (hnp : np = 3 ∨ np = 4) (A : Finset Nat)
    (hA : A ⊆ Finset.range np) (hpar : A.card % 2 = (if np = 4 then 1 else 0)) :
    ∀ x ∈ insert 4 (Finset.range np \ A),
      locPartner np A x ∈ insert 4 (Finset.range np \ A) ∧
      locPartner np A (locPartner np A x) = x ∧
      sameLoc x (locPartner np A x) := by
  let U := Finset.range np \ A
  have hUodd : U.card % 2 = 1 := by
    have h1 := Finset.card_sdiff_add_card_eq_card hA
    change U.card + A.card = (Finset.range np).card at h1
    rw [Finset.card_range] at h1
    rcases hnp with rfl | rfl <;> simp at hpar <;> omega
  let Sng := (Finset.range np).filter (fun y => y ∉ A ∧ (pairMate y ≥ np ∨ pairMate y ∈ A))
  have hSng_sub : Sng ⊆ U := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyr, hyA, _⟩
    exact Finset.mem_sdiff.mpr ⟨hyr, hyA⟩
  have hSng_card : Sng.card = 1 := by
    let P0 := U.filter (fun y => y < 2)
    let P1 := U.filter (fun y => 2 ≤ y)
    have hUdisj : Disjoint P0 P1 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
    have hUeq : U = P0 ∪ P1 := by
      ext y; simp only [P0, P1, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hy; by_cases h : y < 2; exact Or.inl ⟨hy, h⟩; exact Or.inr ⟨hy, by omega⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have hP0le : P0.card ≤ 2 := by
      have : P0 ⊆ {0, 1} := by
        intro y hy; have h1 := (Finset.mem_filter.mp hy).2; simp; omega
      exact (Finset.card_le_card this).trans (by decide)
    have hP1le : P1.card ≤ 2 := by
      have : P1 ⊆ {2, 3} := by
        intro y hy
        have h1 := (Finset.mem_filter.mp hy).2
        have h2 := Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1
        simp; omega
      exact (Finset.card_le_card this).trans (by decide)
    have hsum : P0.card + P1.card = U.card := by
      rw [← Finset.card_union_of_disjoint hUdisj, ← hUeq]
    have hSng_eq : Sng = (if P0.card = 1 then P0 else ∅) ∪ (if P1.card = 1 then P1 else ∅) := by
      ext y
      simp only [Sng, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      constructor
      · rintro ⟨hylt, hyA, hyun⟩
        have hyU : y ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hylt, hyA⟩
        by_cases h2 : y < 2
        · left
          have hyP0 : y ∈ P0 := Finset.mem_filter.mpr ⟨hyU, h2⟩
          have hpm_not : pairMate y ∉ P0 := by
            intro hmem
            have hmemU := (Finset.mem_filter.mp hmem).1
            have hlt := Finset.mem_range.mp (Finset.mem_sdiff.mp hmemU).1
            have hna := (Finset.mem_sdiff.mp hmemU).2
            rcases hyun with hge | ha <;> [omega; exact hna ha]
          have hP0eq : P0 = {y} := by
            ext z; simp only [Finset.mem_singleton]
            constructor
            · intro hz
              have hzl : z < 2 := (Finset.mem_filter.mp hz).2
              by_contra hzy
              have : z = pairMate y := by unfold pairMate; split_ifs <;> omega
              exact hpm_not (this ▸ hz)
            · rintro rfl; exact hyP0
          rw [if_pos (by rw [hP0eq]; simp)]; exact hyP0
        · right
          have hyP1 : y ∈ P1 := Finset.mem_filter.mpr ⟨hyU, by omega⟩
          have hpm_not : pairMate y ∉ P1 := by
            intro hmem
            have hmemU := (Finset.mem_filter.mp hmem).1
            have hlt := Finset.mem_range.mp (Finset.mem_sdiff.mp hmemU).1
            have hna := (Finset.mem_sdiff.mp hmemU).2
            rcases hyun with hge | ha <;> [omega; exact hna ha]
          have hP1eq : P1 = {y} := by
            ext z; simp only [Finset.mem_singleton]
            constructor
            · intro hz
              have hz1 : 2 ≤ z := (Finset.mem_filter.mp hz).2
              have hz2 : z < 4 := by
                have := Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
                omega
              by_contra hzy
              have : z = pairMate y := by unfold pairMate; split_ifs <;> omega
              exact hpm_not (this ▸ hz)
            · rintro rfl; exact hyP1
          rw [if_pos (by rw [hP1eq]; simp)]; exact hyP1
      · intro hmem
        rcases hmem with hmem | hmem
        · split_ifs at hmem with hc
          · have hyU := (Finset.mem_filter.mp hmem).1
            have hy2 := (Finset.mem_filter.mp hmem).2
            refine ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp hyU).1, (Finset.mem_sdiff.mp hyU).2, ?_⟩
            by_contra hcon; push Not at hcon
            have hpmP0 : pairMate y ∈ P0 := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hcon.1, hcon.2⟩, ?_⟩
              unfold pairMate; split_ifs <;> omega
            rcases Finset.card_eq_one.mp hc with ⟨z, hz⟩
            rw [hz, Finset.mem_singleton] at hmem hpmP0
            exact pairMate_ne y (hpmP0.trans hmem.symm)
          · exact absurd hmem (Finset.notMem_empty _)
        · split_ifs at hmem with hc
          · have hyU := (Finset.mem_filter.mp hmem).1
            have hy2 := (Finset.mem_filter.mp hmem).2
            have hylt := Finset.mem_range.mp (Finset.mem_sdiff.mp hyU).1
            refine ⟨hylt, (Finset.mem_sdiff.mp hyU).2, ?_⟩
            by_contra hcon; push Not at hcon
            have hpmP1 : pairMate y ∈ P1 := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hcon.1, hcon.2⟩, ?_⟩
              unfold pairMate; split_ifs <;> omega
            rcases Finset.card_eq_one.mp hc with ⟨z, hz⟩
            rw [hz, Finset.mem_singleton] at hmem hpmP1
            exact pairMate_ne y (hpmP1.trans hmem.symm)
          · exact absurd hmem (Finset.notMem_empty _)
    rw [hSng_eq]
    have hdisj' : Disjoint (if P0.card = 1 then P0 else ∅) (if P1.card = 1 then P1 else ∅) := by
      split_ifs <;> simp [hUdisj]
    rw [Finset.card_union_of_disjoint hdisj']
    split_ifs <;> (try simp only [Finset.card_empty]) <;> omega
  rcases Finset.card_eq_one.mp hSng_card with ⟨u, hSng_eq⟩
  have huSng : u ∈ Sng := by rw [hSng_eq]; simp
  have huU : u ∈ U := hSng_sub huSng
  have hu_prop : u < np ∧ u ∉ A ∧ (pairMate u ≥ np ∨ pairMate u ∈ A) := by
    have := Finset.mem_filter.mp huSng
    exact ⟨Finset.mem_range.mp this.1, this.2.1, this.2.2⟩
  have h4_eq : locPartner np A 4 = u := by
    unfold locPartner
    simp only [ite_true]
    have hne : Sng.Nonempty := by rw [hSng_eq]; exact Finset.singleton_nonempty u
    change (if h : Sng.Nonempty then Sng.min' h else 4) = u
    rw [dif_pos hne]
    simp [hSng_eq]
  have hu_eq : locPartner np A u = 4 := by
    unfold locPartner
    have hune4 : u ≠ 4 := by omega
    rw [if_neg hune4]
    have hnot : ¬ (pairMate u < np ∧ pairMate u ∉ A) := by
      rintro ⟨h1, h2⟩; rcases hu_prop.2.2 with h3 | h3 <;> [omega; exact h2 h3]
    rw [if_neg hnot]
  have hother_eq : ∀ x ∈ U, x ≠ u → pairMate x ∈ U ∧ pairMate x ≠ u ∧ locPartner np A x = pairMate x := by
    intro x hxU hxu
    have hxlt := Finset.mem_range.mp (Finset.mem_sdiff.mp hxU).1
    have hxA := (Finset.mem_sdiff.mp hxU).2
    have hxnotSng : x ∉ Sng := by rw [hSng_eq]; simp [hxu]
    have hpm_ok : pairMate x < np ∧ pairMate x ∉ A := by
      by_contra hcon
      have : pairMate x ≥ np ∨ pairMate x ∈ A := by
        by_cases h1 : pairMate x < np
        · right; by_contra h2; exact hcon ⟨h1, h2⟩
        · left; omega
      exact hxnotSng (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxlt, hxA, this⟩)
    have hpmU : pairMate x ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hpm_ok.1, hpm_ok.2⟩
    have hpm_neu : pairMate x ≠ u := by
      intro heq
      have : x = pairMate u := by rw [← heq, pairMate_self]
      rcases hu_prop.2.2 with hge | ha <;> [omega; exact hxA (this ▸ ha)]
    have hloc : locPartner np A x = pairMate x := by
      unfold locPartner
      have hxne4 : x ≠ 4 := by omega
      rw [if_neg hxne4, if_pos hpm_ok]
    exact ⟨hpmU, hpm_neu, hloc⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hxU
  · rw [h4_eq, hu_eq]
    exact ⟨Finset.mem_insert_of_mem huU, rfl, ⟨by omega, Or.inl rfl⟩⟩
  · by_cases hxu : x = u
    · subst hxu
      rw [hu_eq, h4_eq]
      exact ⟨Finset.mem_insert_self 4 U, rfl, ⟨by omega, Or.inr (Or.inl rfl)⟩⟩
    · rcases hother_eq x hxU hxu with ⟨hpmU, hpm_neu, hloc⟩
      rcases hother_eq (pairMate x) hpmU hpm_neu with ⟨_, _, hloc2⟩
      rw [hloc, hloc2, pairMate_self]
      exact ⟨Finset.mem_insert_of_mem hpmU, rfl, ⟨(pairMate_ne x).symm, Or.inr (Or.inr (pairMate_div2 x).symm)⟩⟩

lemma card_equiv_fin_of_card_eq {α : Type*} [Fintype α] [DecidableEq α] {k : Nat}
    (h : Fintype.card α = k) : Fintype.card (α ≃ Fin k) = Nat.factorial k := by
  let e : α ≃ Fin k := Fintype.equivFinOfCardEq h
  let eqv : (α ≃ Fin k) ≃ Equiv.Perm (Fin k) :=
    { toFun := fun f => e.symm.trans f
      invFun := fun g => e.trans g
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  rw [Fintype.card_congr eqv, Fintype.card_perm, Fintype.card_fin]

lemma matchings_card_eq {n m : Nat}
    (nports : Fin m → Nat) (hnp : ∀ i, nports i = 3 ∨ nports i = 4)
    (label : Fin m → Nat → W n) (quota : W n → Nat) :
    let I := Fin m
    let ports := (Finset.univ : Finset I).biUnion (fun i => (Finset.range (nports i)).image (fun j => (i, j)))
    let labels := ports.image (fun p => label p.1 p.2)
    let V := (I × Nat) ⊕ (W n × Nat)
    let localNodes := ports ∪ (Finset.univ : Finset I).image (fun i => (i, 4))
    let slots := labels.biUnion (fun v => (Finset.range (quota v)).image (fun j => (v, j)))
    let verts : Finset V := localNodes.image Sum.inl ∪ slots.image Sum.inr
    let sameRow := fun (p q : I × Nat) => p.1 = q.1 ∧ p.2 ≠ q.2 ∧ (p.2 = 4 ∨ q.2 = 4 ∨ p.2 / 2 = q.2 / 2)
    let attach := fun (p : I × Nat) (q : W n × Nat) => p.2 < nports p.1 ∧ label p.1 p.2 = q.1
    let edge := fun (p q : V) => Sum.elim (fun x => Sum.elim (sameRow x) (attach x) q)
      (fun y => Sum.elim (fun x => attach x y) (fun _ => False) q) p
    let matchings := (Finset.univ : Finset (↥verts → ↥verts)).filter (fun (f : ↥verts → ↥verts) =>
      @decide (∀ x : ↥verts, f (f x) = x ∧ edge x.val (f x).val) (Classical.propDecidable _) = true)
    let validA := ports.powerset.filter (fun (A : Finset (I × Nat)) =>
      (∀ i : I, (A.filter (fun p => p.1 = i)).card % 2 = if nports i = 4 then 1 else 0) ∧
      (∀ v ∈ labels, (A.filter (fun p => label p.1 p.2 = v)).card = quota v))
    matchings.card = validA.card * (∏ v ∈ labels, Nat.factorial (quota v)) := by
  intro I ports labels V localNodes slots verts sameRow attach edge matchings validA
  have hmem_ports : ∀ p : I × Nat, p ∈ ports ↔ p.2 < nports p.1 := by
    intro ⟨i, j⟩
    simp only [ports, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨i', j', hj', rfl, rfl⟩; exact hj'
    · intro hj; exact ⟨i, j, hj, rfl, rfl⟩
  have hmem_local : ∀ p : I × Nat, p ∈ localNodes ↔ p.2 < nports p.1 ∨ p.2 = 4 := by
    intro ⟨i, j⟩
    simp only [localNodes, Finset.mem_union, hmem_ports, Finset.mem_image, Finset.mem_univ,
      true_and, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨i', rfl, rfl⟩); exact Or.inl h; exact Or.inr rfl
    · rintro (h | rfl); exact Or.inl h; exact Or.inr ⟨i, rfl, rfl⟩
  have hmem_slots : ∀ q : W n × Nat, q ∈ slots ↔ q.1 ∈ labels ∧ q.2 < quota q.1 := by
    intro ⟨v, k⟩
    simp only [slots, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨v', hv', k', hk', rfl, rfl⟩; exact ⟨hv', hk'⟩
    · rintro ⟨hv, hk⟩; exact ⟨v, hv, k, hk, rfl, rfl⟩
  have hmem_verts_inl : ∀ p : I × Nat, Sum.inl p ∈ verts ↔ p ∈ localNodes := by
    intro p; simp [verts]
  have hmem_verts_inr : ∀ q : W n × Nat, Sum.inr q ∈ verts ↔ q ∈ slots := by
    intro q; simp [verts]
  let portsV (A : Finset (I × Nat)) (v : W n) : Finset (I × Nat) :=
    A.filter (fun p => label p.1 p.2 = v)
  let rowSet (A : Finset (I × Nat)) (i : I) : Finset Nat :=
    (A.filter (fun p => p.1 = i)).image Prod.snd
  have hrowSet_card : ∀ A i, (rowSet A i).card = (A.filter (fun p => p.1 = i)).card := by
    intro A i
    refine Finset.card_image_of_injOn ?_
    intro p hp q hq heq
    have hp1 := (Finset.mem_filter.mp hp).2
    have hq1 := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hp1.trans hq1.symm) heq
  have hmem_rowSet : ∀ A i j, j ∈ rowSet A i ↔ (i, j) ∈ A := by
    intro A i j
    simp only [rowSet, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨i', j'⟩, ⟨hmem, rfl⟩, rfl⟩; exact hmem
    · intro hmem; exact ⟨(i, j), ⟨hmem, rfl⟩, rfl⟩
  let attOf (f : ↥verts → ↥verts) : Finset (I × Nat) :=
    ports.filter (fun p => if h : Sum.inl p ∈ verts then (f ⟨Sum.inl p, h⟩).val.isRight else false)
  let RHS := Σ A : ↥validA, ∀ v : ↥labels, ↥(portsV A.val v.val) ≃ Fin (quota v.val)
  have htoA : ∀ f : ↥matchings,
      let A := attOf f.val
      A ∈ validA ∧
      (∀ p ∈ A, ∀ h : Sum.inl p ∈ verts, ∃ q : W n × Nat,
        (f.val ⟨Sum.inl p, h⟩).val = Sum.inr q ∧ q.1 = label p.1 p.2 ∧ q.2 < quota q.1) ∧
      (∀ q : W n × Nat, ∀ h : Sum.inr q ∈ verts, ∃ p ∈ A,
        (f.val ⟨Sum.inr q, h⟩).val = Sum.inl p ∧ label p.1 p.2 = q.1) ∧
      (∀ i : I, ∀ j ∈ insert 4 (Finset.range (nports i) \ rowSet A i),
        ∀ h : Sum.inl (i, j) ∈ verts,
        (f.val ⟨Sum.inl (i, j), h⟩).val = Sum.inl (i, locPartner (nports i) (rowSet A i) j)) := by
    intro f A
    have hf : ∀ x : ↥verts, f.val (f.val x) = x ∧ edge x.val (f.val x).val := by
      have hmem := (Finset.mem_filter.mp f.property).2
      exact (@decide_eq_true_iff _ (Classical.propDecidable _)).mp hmem
    have hA_sub : A ⊆ ports := Finset.filter_subset _ _
    have hA_right : ∀ p ∈ A, ∀ h : Sum.inl p ∈ verts, ∃ q : W n × Nat,
        (f.val ⟨Sum.inl p, h⟩).val = Sum.inr q ∧ q.1 = label p.1 p.2 ∧ q.2 < quota q.1 := by
      intro p hp h
      have hisR := (Finset.mem_filter.mp hp).2
      simp only [h, dite_true] at hisR
      cases hfv : (f.val ⟨Sum.inl p, h⟩).val with
      | inl p' => rw [hfv] at hisR; simp at hisR
      | inr q =>
        have hedge := (hf ⟨Sum.inl p, h⟩).2
        rw [hfv] at hedge
        have hqverts : Sum.inr q ∈ verts := hfv ▸ (f.val ⟨Sum.inl p, h⟩).property
        have hqmem := (hmem_slots q).mp ((hmem_verts_inr q).mp hqverts)
        exact ⟨q, rfl, hedge.2.symm, hqmem.2⟩
    have hslot_left : ∀ q : W n × Nat, ∀ h : Sum.inr q ∈ verts, ∃ p ∈ A,
        (f.val ⟨Sum.inr q, h⟩).val = Sum.inl p ∧ label p.1 p.2 = q.1 := by
      intro q h
      cases hfv : (f.val ⟨Sum.inr q, h⟩).val with
      | inr q' =>
        have hedge := (hf ⟨Sum.inr q, h⟩).2
        rw [hfv] at hedge
        exact False.elim hedge
      | inl p =>
        have hedge := (hf ⟨Sum.inr q, h⟩).2
        rw [hfv] at hedge
        have hpports : p ∈ ports := (hmem_ports p).mpr hedge.1
        have hpverts : Sum.inl p ∈ verts := hfv ▸ (f.val ⟨Sum.inr q, h⟩).property
        have hfp : (f.val ⟨Sum.inl p, hpverts⟩).val = Sum.inr q := by
          have hinv := (hf ⟨Sum.inr q, h⟩).1
          have hsub : f.val ⟨Sum.inr q, h⟩ = ⟨Sum.inl p, hpverts⟩ := Subtype.ext hfv
          rw [hsub] at hinv
          exact congrArg Subtype.val hinv
        have hpA : p ∈ A := Finset.mem_filter.mpr ⟨hpports, by simp [hpverts, hfp]⟩
        exact ⟨p, hpA, rfl, hedge.2⟩
    have hrow_res : ∀ i : I,
        (rowSet A i).card % 2 = (if nports i = 4 then 1 else 0) ∧
        ∀ j ∈ insert 4 (Finset.range (nports i) \ rowSet A i),
          ∀ h : Sum.inl (i, j) ∈ verts,
          (f.val ⟨Sum.inl (i, j), h⟩).val = Sum.inl (i, locPartner (nports i) (rowSet A i) j) := by
      intro i
      have hAi_sub : rowSet A i ⊆ Finset.range (nports i) := by
        intro j hj
        have hmem := (hmem_rowSet A i j).mp hj
        exact Finset.mem_range.mpr ((hmem_ports (i, j)).mp (hA_sub hmem))
      let g : Nat → Nat := fun j =>
        if hj : Sum.inl (i, j) ∈ verts then
          match (f.val ⟨Sum.inl (i, j), hj⟩).val with
          | Sum.inl p' => p'.2
          | Sum.inr _ => 4
        else 4
      have hg_valid : ∀ j ∈ insert 4 (Finset.range (nports i) \ rowSet A i),
          g j ∈ insert 4 (Finset.range (nports i) \ rowSet A i) ∧
          g (g j) = j ∧ sameLoc j (g j) ∧
          ∀ h : Sum.inl (i, j) ∈ verts, (f.val ⟨Sum.inl (i, j), h⟩).val = Sum.inl (i, g j) := by
        intro j hj
        have hjloc : (i, j) ∈ localNodes := by
          rw [hmem_local]
          rcases Finset.mem_insert.mp hj with rfl | hjU
          · exact Or.inr rfl
          · exact Or.inl (Finset.mem_range.mp (Finset.mem_sdiff.mp hjU).1)
        have hjv : Sum.inl (i, j) ∈ verts := (hmem_verts_inl _).mpr hjloc
        have hjnotA : (i, j) ∉ A := by
          rcases Finset.mem_insert.mp hj with rfl | hjU
          · intro hmem
            have hlt := (hmem_ports (i, 4)).mp (hA_sub hmem)
            dsimp only at hlt
            rcases hnp i with h3 | h4 <;> omega
          · intro hmem; exact (Finset.mem_sdiff.mp hjU).2 ((hmem_rowSet A i j).mpr hmem)
        cases hfv : (f.val ⟨Sum.inl (i, j), hjv⟩).val with
        | inr q =>
          have hedge := (hf ⟨Sum.inl (i, j), hjv⟩).2
          rw [hfv] at hedge
          have hp : (i, j) ∈ ports := (hmem_ports (i, j)).mpr hedge.1
          exact False.elim (hjnotA (Finset.mem_filter.mpr ⟨hp, by simp [hjv, hfv]⟩))
        | inl p' =>
          have hedge := (hf ⟨Sum.inl (i, j), hjv⟩).2
          rw [hfv] at hedge
          have hp'1 : p'.1 = i := hedge.1.symm
          have hp'v : Sum.inl p' ∈ verts := hfv ▸ (f.val ⟨Sum.inl (i, j), hjv⟩).property
          have hp'loc : p' ∈ localNodes := (hmem_verts_inl p').mp hp'v
          have hp'notA : p' ∉ A := by
            intro hp'A
            rcases hA_right p' hp'A hp'v with ⟨q, hfq, _, _⟩
            have hinv := (hf ⟨Sum.inl (i, j), hjv⟩).1
            have hsub : f.val ⟨Sum.inl (i, j), hjv⟩ = ⟨Sum.inl p', hp'v⟩ := Subtype.ext hfv
            rw [hsub] at hinv
            have : (f.val ⟨Sum.inl p', hp'v⟩).val = Sum.inl (i, j) := congrArg Subtype.val hinv
            rw [hfq] at this; cases this
          have hgj : g j = p'.2 := by simp [g, hjv, hfv]
          have hp'eq : p' = (i, p'.2) := Prod.ext hp'1 rfl
          have hgjU : g j ∈ insert 4 (Finset.range (nports i) \ rowSet A i) := by
            rw [hgj]
            rcases (hmem_local p').mp hp'loc with hlt | h4
            · rw [hp'1] at hlt
              exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
                ⟨Finset.mem_range.mpr hlt, fun h => hp'notA (hp'eq ▸ (hmem_rowSet A i p'.2).mp h)⟩)
            · rw [h4]; exact Finset.mem_insert_self _ _
          have hggj : g (g j) = j := by
            rw [hgj]
            have hp'v2 : Sum.inl (i, p'.2) ∈ verts := hp'eq ▸ hp'v
            have hinv := (hf ⟨Sum.inl (i, j), hjv⟩).1
            have hsub : f.val ⟨Sum.inl (i, j), hjv⟩ = ⟨Sum.inl (i, p'.2), hp'v2⟩ :=
              Subtype.ext (hfv.trans (congrArg Sum.inl hp'eq))
            rw [hsub] at hinv
            have hback : (f.val ⟨Sum.inl (i, p'.2), hp'v2⟩).val = Sum.inl (i, j) :=
              congrArg Subtype.val hinv
            simp [g, hp'v2, hback]
          have hsame : sameLoc j (g j) := by rw [hgj]; exact hedge.2
          refine ⟨hgjU, hggj, hsame, ?_⟩
          intro h
          have : (⟨Sum.inl (i, j), h⟩ : ↥verts) = ⟨Sum.inl (i, j), hjv⟩ := rfl
          rw [this, hfv, hgj, ← hp'eq]
      have huniq := local_gadget_unique (nports i) (hnp i) (rowSet A i) hAi_sub g
        (fun j hj => ⟨(hg_valid j hj).1, (hg_valid j hj).2.1, (hg_valid j hj).2.2.1⟩)
      refine ⟨huniq.1, ?_⟩
      intro j hj h
      rw [(hg_valid j hj).2.2.2 h, huniq.2 j hj]
    have hA_quota : ∀ v ∈ labels, (portsV A v).card = quota v := by
      intro v hv
      have hcard : (portsV A v).card = (Finset.range (quota v)).card := by
        refine Finset.card_bij (fun p hp =>
          let hpA := (Finset.mem_filter.mp hp).1
          let hpv : Sum.inl p ∈ verts := (hmem_verts_inl p).mpr
            ((hmem_local p).mpr (Or.inl ((hmem_ports p).mp (hA_sub hpA))))
          match (f.val ⟨Sum.inl p, hpv⟩).val with
          | Sum.inr q => q.2
          | Sum.inl _ => 0) ?_ ?_ ?_
        · intro p hp
          have hpA := (Finset.mem_filter.mp hp).1
          have hpl := (Finset.mem_filter.mp hp).2
          have hpv : Sum.inl p ∈ verts := (hmem_verts_inl p).mpr
            ((hmem_local p).mpr (Or.inl ((hmem_ports p).mp (hA_sub hpA))))
          rcases hA_right p hpA hpv with ⟨q, hfq, hql, hqlt⟩
          dsimp only; rw [hfq]; dsimp only
          exact Finset.mem_range.mpr (by rw [← hpl, ← hql]; exact hqlt)
        · intro p₁ hp₁ p₂ hp₂ heq
          have hp₁A := (Finset.mem_filter.mp hp₁).1
          have hp₂A := (Finset.mem_filter.mp hp₂).1
          have hp₁lab := (Finset.mem_filter.mp hp₁).2
          have hp₂lab := (Finset.mem_filter.mp hp₂).2
          have hp₁v : Sum.inl p₁ ∈ verts := (hmem_verts_inl p₁).mpr
            ((hmem_local p₁).mpr (Or.inl ((hmem_ports p₁).mp (hA_sub hp₁A))))
          have hp₂v : Sum.inl p₂ ∈ verts := (hmem_verts_inl p₂).mpr
            ((hmem_local p₂).mpr (Or.inl ((hmem_ports p₂).mp (hA_sub hp₂A))))
          rcases hA_right p₁ hp₁A hp₁v with ⟨q₁, hfq₁, hq₁l, _⟩
          rcases hA_right p₂ hp₂A hp₂v with ⟨q₂, hfq₂, hq₂l, _⟩
          dsimp only at heq; rw [hfq₁, hfq₂] at heq; dsimp only at heq
          have hqeq : q₁ = q₂ := Prod.ext (hq₁l.trans (hp₁lab.trans (hp₂lab.symm.trans hq₂l.symm))) heq
          have hf_eq : f.val ⟨Sum.inl p₁, hp₁v⟩ = f.val ⟨Sum.inl p₂, hp₂v⟩ :=
            Subtype.ext (hfq₁.trans ((congrArg Sum.inr hqeq).trans hfq₂.symm))
          have h1 := (hf ⟨Sum.inl p₁, hp₁v⟩).1
          have h2 := (hf ⟨Sum.inl p₂, hp₂v⟩).1
          rw [hf_eq] at h1
          have hsub : (⟨Sum.inl p₁, hp₁v⟩ : ↥verts) = ⟨Sum.inl p₂, hp₂v⟩ := h1.symm.trans h2
          exact Sum.inl.inj (congrArg Subtype.val hsub)
        · intro k hk
          have hklt := Finset.mem_range.mp hk
          have hqv : Sum.inr (v, k) ∈ verts := (hmem_verts_inr _).mpr ((hmem_slots _).mpr ⟨hv, hklt⟩)
          rcases hslot_left (v, k) hqv with ⟨p, hpA, hfp, hplab⟩
          have hpv : Sum.inl p ∈ verts := (hmem_verts_inl p).mpr
            ((hmem_local p).mpr (Or.inl ((hmem_ports p).mp (hA_sub hpA))))
          have hfp_back : (f.val ⟨Sum.inl p, hpv⟩).val = Sum.inr (v, k) := by
            have hinv := (hf ⟨Sum.inr (v, k), hqv⟩).1
            have hsub : f.val ⟨Sum.inr (v, k), hqv⟩ = ⟨Sum.inl p, hpv⟩ := Subtype.ext hfp
            rw [hsub] at hinv; exact congrArg Subtype.val hinv
          refine ⟨p, Finset.mem_filter.mpr ⟨hpA, hplab⟩, ?_⟩
          dsimp only; rw [hfp_back]
      simpa using hcard
    have hA_valid : A ∈ validA := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA_sub, ?_, hA_quota⟩
      intro i; rw [← hrowSet_card A i]; exact (hrow_res i).1
    exact ⟨hA_valid, hA_right, hslot_left, fun i => (hrow_res i).2⟩
  let toRHS : ↥matchings → RHS := fun f =>
    let A := attOf f.val
    let hf := htoA f
    ⟨⟨A, hf.1⟩, fun v =>
      { toFun := fun p =>
          let hpA := (Finset.mem_filter.mp p.property).1
          let hpv : Sum.inl p.val ∈ verts := (hmem_verts_inl p.val).mpr
            ((hmem_local p.val).mpr (Or.inl ((hmem_ports p.val).mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hf.1).1) hpA))))
          let hq := hf.2.1 p.val hpA hpv
          ⟨(Classical.choose hq).2, by
            have hc := Classical.choose_spec hq
            have hpl := (Finset.mem_filter.mp p.property).2
            calc (Classical.choose hq).2 < quota (Classical.choose hq).1 := hc.2.2
              _ = quota v.val := congrArg quota (hc.2.1.trans hpl)⟩
        invFun := fun k =>
          let hqv : Sum.inr (v.val, k.val) ∈ verts :=
            (hmem_verts_inr _).mpr ((hmem_slots _).mpr ⟨v.property, k.isLt⟩)
          let hp := hf.2.2.1 (v.val, k.val) hqv
          ⟨Classical.choose hp, Finset.mem_filter.mpr ⟨(Classical.choose_spec hp).1, (Classical.choose_spec hp).2.2⟩⟩
        left_inv := fun p => by
          apply Subtype.ext
          have hpA := (Finset.mem_filter.mp p.property).1
          have hpl := (Finset.mem_filter.mp p.property).2
          have hpv : Sum.inl p.val ∈ verts := (hmem_verts_inl p.val).mpr
            ((hmem_local p.val).mpr (Or.inl ((hmem_ports p.val).mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hf.1).1) hpA))))
          let hq := hf.2.1 p.val hpA hpv
          set q := Classical.choose hq
          have hqc := Classical.choose_spec hq
          have hqeq : (v.val, q.2) = q := Prod.ext (hpl.symm.trans hqc.2.1.symm) rfl
          have hqv_lt : q.2 < quota v.val :=
            calc q.2 < quota q.1 := hqc.2.2
              _ = quota v.val := congrArg quota (hqc.2.1.trans hpl)
          have hqv : Sum.inr (v.val, q.2) ∈ verts :=
            (hmem_verts_inr _).mpr ((hmem_slots _).mpr ⟨v.property, hqv_lt⟩)
          let hp := hf.2.2.1 (v.val, q.2) hqv
          have hpc := Classical.choose_spec hp
          have hfv_eq : (f.val ⟨Sum.inl p.val, hpv⟩).val = Sum.inr (v.val, q.2) :=
            hqc.1.trans (congrArg Sum.inr hqeq.symm)
          have hfprop : ∀ x : ↥verts, f.val (f.val x) = x :=
            fun x => ((@decide_eq_true_iff _ (Classical.propDecidable _)).mp (Finset.mem_filter.mp f.property).2 x).1
          have hback : (f.val ⟨Sum.inr (v.val, q.2), hqv⟩).val = Sum.inl p.val := by
            have h1 := hfprop ⟨Sum.inl p.val, hpv⟩
            have hsub : f.val ⟨Sum.inl p.val, hpv⟩ = ⟨Sum.inr (v.val, q.2), hqv⟩ := Subtype.ext hfv_eq
            rw [hsub] at h1; exact congrArg Subtype.val h1
          have : Sum.inl (Classical.choose hp) = Sum.inl p.val := hpc.2.1.symm.trans hback
          exact Sum.inl.inj this
        right_inv := fun k => by
          apply Fin.ext
          have hqv : Sum.inr (v.val, k.val) ∈ verts :=
            (hmem_verts_inr _).mpr ((hmem_slots _).mpr ⟨v.property, k.isLt⟩)
          let hp := hf.2.2.1 (v.val, k.val) hqv
          set p := Classical.choose hp
          have hpc := Classical.choose_spec hp
          have hpv : Sum.inl p ∈ verts := (hmem_verts_inl p).mpr
            ((hmem_local p).mpr (Or.inl ((hmem_ports p).mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hf.1).1) hpc.1))))
          let hq := hf.2.1 p hpc.1 hpv
          have hqc := Classical.choose_spec hq
          have hfprop : ∀ x : ↥verts, f.val (f.val x) = x :=
            fun x => ((@decide_eq_true_iff _ (Classical.propDecidable _)).mp (Finset.mem_filter.mp f.property).2 x).1
          have hback : (f.val ⟨Sum.inl p, hpv⟩).val = Sum.inr (v.val, k.val) := by
            have h1 := hfprop ⟨Sum.inr (v.val, k.val), hqv⟩
            have hsub : f.val ⟨Sum.inr (v.val, k.val), hqv⟩ = ⟨Sum.inl p, hpv⟩ := Subtype.ext hpc.2.1
            rw [hsub] at h1; exact congrArg Subtype.val h1
          have : Sum.inr (Classical.choose hq) = Sum.inr (v.val, k.val) := hqc.1.symm.trans hback
          exact congrArg Prod.snd (Sum.inr.inj this) }⟩
  let ofRHS_fun : RHS → ↥verts → ↥verts := fun ⟨A, σ⟩ x =>
    match x with
    | ⟨Sum.inl p, hxmem⟩ =>
      if hpA : p ∈ A.val then
        let v := label p.1 p.2
        have hpports : p ∈ ports := (Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) hpA
        have hv : v ∈ labels := Finset.mem_image.mpr ⟨p, hpports, rfl⟩
        let k := σ ⟨v, hv⟩ ⟨p, Finset.mem_filter.mpr ⟨hpA, rfl⟩⟩
        ⟨Sum.inr (v, k.val), (hmem_verts_inr _).mpr ((hmem_slots _).mpr ⟨hv, k.isLt⟩)⟩
      else
        let j' := locPartner (nports p.1) (rowSet A.val p.1) p.2
        have hloc : (p.1, j') ∈ localNodes := by
          have hp_sub : rowSet A.val p.1 ⊆ Finset.range (nports p.1) := by
            intro j hj
            exact Finset.mem_range.mpr ((hmem_ports (p.1, j)).mp
              ((Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) ((hmem_rowSet A.val p.1 j).mp hj)))
          have hpar : (rowSet A.val p.1).card % 2 = (if nports p.1 = 4 then 1 else 0) := by
            rw [hrowSet_card]; exact (Finset.mem_filter.mp A.property).2.1 p.1
          have hp_in : p.2 ∈ insert 4 (Finset.range (nports p.1) \ rowSet A.val p.1) := by
            rcases (hmem_local p).mp ((hmem_verts_inl p).mp hxmem) with hlt | h4
            · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
                ⟨Finset.mem_range.mpr hlt, fun h => hpA ((hmem_rowSet A.val p.1 p.2).mp h)⟩)
            · rw [h4]; exact Finset.mem_insert_self _ _
          have hgv := (local_gadget_valid (nports p.1) (hnp p.1) (rowSet A.val p.1) hp_sub hpar p.2 hp_in).1
          rw [hmem_local]
          rcases Finset.mem_insert.mp hgv with h4 | hjU
          · exact Or.inr h4
          · exact Or.inl (Finset.mem_range.mp (Finset.mem_sdiff.mp hjU).1)
        ⟨Sum.inl (p.1, j'), (hmem_verts_inl _).mpr hloc⟩
    | ⟨Sum.inr q, hxmem⟩ =>
      have hqs := (hmem_slots q).mp ((hmem_verts_inr q).mp hxmem)
      let p := (σ ⟨q.1, hqs.1⟩).symm ⟨q.2, hqs.2⟩
      have hpports : p.val ∈ ports := (Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1)
        (Finset.mem_filter.mp p.property).1
      ⟨Sum.inl p.val, (hmem_verts_inl _).mpr ((hmem_local _).mpr (Or.inl ((hmem_ports _).mp hpports)))⟩
  have hofRHS_mem : ∀ r : RHS, ofRHS_fun r ∈ matchings := by
    rintro ⟨A, σ⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (@decide_eq_true_iff _ (Classical.propDecidable _)).mpr ?_⟩
    rintro ⟨xval, hxmem⟩
    cases xval with
    | inl p =>
      by_cases hpA : p ∈ A.val
      · have hpports : p ∈ ports := (Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) hpA
        have hv : label p.1 p.2 ∈ labels := Finset.mem_image.mpr ⟨p, hpports, rfl⟩
        have h1 : ofRHS_fun ⟨A, σ⟩ ⟨Sum.inl p, hxmem⟩ =
            ⟨Sum.inr (label p.1 p.2, (σ ⟨label p.1 p.2, hv⟩ ⟨p, Finset.mem_filter.mpr ⟨hpA, rfl⟩⟩).val),
              (hmem_verts_inr _).mpr ((hmem_slots _).mpr ⟨hv, (σ ⟨label p.1 p.2, hv⟩ ⟨p, Finset.mem_filter.mpr ⟨hpA, rfl⟩⟩).isLt⟩)⟩ := by
          simp [ofRHS_fun, hpA]
        constructor
        · rw [h1]
          apply Subtype.ext
          simp only [ofRHS_fun, Fin.eta, Equiv.symm_apply_apply]
        · rw [h1]
          exact ⟨(hmem_ports p).mp hpports, rfl⟩
      · have hp_sub : rowSet A.val p.1 ⊆ Finset.range (nports p.1) := by
          intro j hj
          exact Finset.mem_range.mpr ((hmem_ports (p.1, j)).mp
            ((Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) ((hmem_rowSet A.val p.1 j).mp hj)))
        have hpar : (rowSet A.val p.1).card % 2 = (if nports p.1 = 4 then 1 else 0) := by
          rw [hrowSet_card]; exact (Finset.mem_filter.mp A.property).2.1 p.1
        have hp_in : p.2 ∈ insert 4 (Finset.range (nports p.1) \ rowSet A.val p.1) := by
          rcases (hmem_local p).mp ((hmem_verts_inl p).mp hxmem) with hlt | h4
          · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
              ⟨Finset.mem_range.mpr hlt, fun h => hpA ((hmem_rowSet A.val p.1 p.2).mp h)⟩)
          · rw [h4]; exact Finset.mem_insert_self _ _
        have hgv := local_gadget_valid (nports p.1) (hnp p.1) (rowSet A.val p.1) hp_sub hpar p.2 hp_in
        have hp'notA : (p.1, locPartner (nports p.1) (rowSet A.val p.1) p.2) ∉ A.val := by
          intro hmem
          rcases Finset.mem_insert.mp hgv.1 with h4 | hjU
          · have hlt := (hmem_ports (p.1, 4)).mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) (h4 ▸ hmem))
            dsimp only at hlt
            rcases hnp p.1 with h3 | h4' <;> omega
          · exact (Finset.mem_sdiff.mp hjU).2 ((hmem_rowSet A.val p.1 _).mpr hmem)
        have hloc' : Sum.inl (p.1, locPartner (nports p.1) (rowSet A.val p.1) p.2) ∈ verts := by
          rw [hmem_verts_inl, hmem_local]
          rcases Finset.mem_insert.mp hgv.1 with h4 | hjU
          · exact Or.inr h4
          · exact Or.inl (Finset.mem_range.mp (Finset.mem_sdiff.mp hjU).1)
        have h1 : ofRHS_fun ⟨A, σ⟩ ⟨Sum.inl p, hxmem⟩ =
            ⟨Sum.inl (p.1, locPartner (nports p.1) (rowSet A.val p.1) p.2), hloc'⟩ := by
          apply Subtype.ext; simp [ofRHS_fun, hpA]
        constructor
        · rw [h1]
          apply Subtype.ext
          simp only [ofRHS_fun, hp'notA, dite_false, hgv.2.1]
        · rw [h1]
          exact ⟨rfl, hgv.2.2⟩
    | inr q =>
      have hqs := (hmem_slots q).mp ((hmem_verts_inr q).mp hxmem)
      let p := (σ ⟨q.1, hqs.1⟩).symm ⟨q.2, hqs.2⟩
      have hpA : p.val ∈ A.val := (Finset.mem_filter.mp p.property).1
      have hplab : label p.val.1 p.val.2 = q.1 := (Finset.mem_filter.mp p.property).2
      have hpports : p.val ∈ ports := (Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) hpA
      have hpv : Sum.inl p.val ∈ verts := (hmem_verts_inl _).mpr ((hmem_local _).mpr (Or.inl ((hmem_ports _).mp hpports)))
      have h1 : ofRHS_fun ⟨A, σ⟩ ⟨Sum.inr q, hxmem⟩ = ⟨Sum.inl p.val, hpv⟩ := by
        apply Subtype.ext; simp [ofRHS_fun, p]
      constructor
      · rw [h1]
        apply Subtype.ext
        simp only [ofRHS_fun, hpA, dite_true]
        congr 1
        apply Prod.ext hplab
        have hsig_eq : (⟨label p.val.1 p.val.2, Finset.mem_image.mpr ⟨p.val, hpports, rfl⟩⟩ : ↥labels) = ⟨q.1, hqs.1⟩ :=
          Subtype.ext hplab
        have heq_val : ∀ (v₁ v₂ : ↥labels) (hv : v₁ = v₂) (a₁ : ↥(portsV A.val v₁.val)) (a₂ : ↥(portsV A.val v₂.val)),
            a₁.val = a₂.val → (σ v₁ a₁).val = (σ v₂ a₂).val := by
          rintro v₁ _ rfl a₁ a₂ h; rw [Subtype.ext h]
        have := heq_val _ ⟨q.1, hqs.1⟩ hsig_eq ⟨p.val, Finset.mem_filter.mpr ⟨hpA, rfl⟩⟩ p rfl
        rw [this]; simp [p]
      · rw [h1]
        exact ⟨(hmem_ports p.val).mp hpports, hplab⟩
  let ofRHS : RHS → ↥matchings := fun r => ⟨ofRHS_fun r, hofRHS_mem r⟩
  have hleft : ∀ f : ↥matchings, ofRHS (toRHS f) = f := by
    intro f
    apply Subtype.ext
    funext ⟨xval, hxmem⟩
    apply Subtype.ext
    let A := attOf f.val
    have hf := htoA f
    cases xval with
    | inl p =>
      by_cases hpA : p ∈ A
      · change (ofRHS_fun (toRHS f) ⟨Sum.inl p, hxmem⟩).val = (f.val ⟨Sum.inl p, hxmem⟩).val
        have h1 : (ofRHS_fun (toRHS f) ⟨Sum.inl p, hxmem⟩).val =
            Sum.inr (label p.1 p.2,
              ((toRHS f).2 ⟨label p.1 p.2, Finset.mem_image.mpr ⟨p, (Finset.mem_powerset.mp (Finset.mem_filter.mp hf.1).1) hpA, rfl⟩⟩
                ⟨p, Finset.mem_filter.mpr ⟨hpA, rfl⟩⟩).val) := by
          simp [ofRHS_fun, toRHS, A, hpA]
        rw [h1]
        have hq := hf.2.1 p hpA hxmem
        have hqc := Classical.choose_spec hq
        rw [hqc.1]
        congr 1
        dsimp only [toRHS]
        exact Prod.ext hqc.2.1.symm rfl
      · change (ofRHS_fun (toRHS f) ⟨Sum.inl p, hxmem⟩).val = (f.val ⟨Sum.inl p, hxmem⟩).val
        have h1 : (ofRHS_fun (toRHS f) ⟨Sum.inl p, hxmem⟩).val =
            Sum.inl (p.1, locPartner (nports p.1) (rowSet A p.1) p.2) := by
          simp [ofRHS_fun, toRHS, A, hpA]
        rw [h1]
        have hp_in : p.2 ∈ insert 4 (Finset.range (nports p.1) \ rowSet A p.1) := by
          rcases (hmem_local p).mp ((hmem_verts_inl p).mp hxmem) with hlt | h4
          · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
              ⟨Finset.mem_range.mpr hlt, fun h => hpA ((hmem_rowSet A p.1 p.2).mp h)⟩)
          · rw [h4]; exact Finset.mem_insert_self _ _
        exact (hf.2.2.2 p.1 p.2 hp_in hxmem).symm
    | inr q =>
      have hqs := (hmem_slots q).mp ((hmem_verts_inr q).mp hxmem)
      change (ofRHS_fun (toRHS f) ⟨Sum.inr q, hxmem⟩).val = (f.val ⟨Sum.inr q, hxmem⟩).val
      have h1 : (ofRHS_fun (toRHS f) ⟨Sum.inr q, hxmem⟩).val =
          Sum.inl (((toRHS f).2 ⟨q.1, hqs.1⟩).symm ⟨q.2, hqs.2⟩).val := by
        simp [ofRHS_fun, toRHS]
      rw [h1]
      dsimp only [toRHS]
      exact (Classical.choose_spec (hf.2.2.1 (q.1, q.2) hxmem)).2.1.symm
  have hsigma_snd_heq : ∀ (A₁ A₂ : ↥validA) (hA : A₁ = A₂)
      (g₁ : ∀ v : ↥labels, ↥(portsV A₁.val v.val) ≃ Fin (quota v.val))
      (g₂ : ∀ v : ↥labels, ↥(portsV A₂.val v.val) ≃ Fin (quota v.val)),
      (∀ (v : ↥labels) (p₁ : ↥(portsV A₁.val v.val)) (p₂ : ↥(portsV A₂.val v.val)),
        p₁.val = p₂.val → (g₁ v p₁).val = (g₂ v p₂).val) →
      HEq g₁ g₂ := by
    rintro A₁ _ rfl g₁ g₂ h
    simp only [heq_eq_eq]
    funext v; apply Equiv.ext; intro p; exact Fin.ext (h v p p rfl)
  have hright : ∀ r : RHS, toRHS (ofRHS r) = r := by
    rintro ⟨A, σ⟩
    have hAeq : attOf (ofRHS ⟨A, σ⟩).val = A.val := by
      ext p
      simp only [attOf, Finset.mem_filter]
      constructor
      · rintro ⟨hpports, hisR⟩
        have hpv : Sum.inl p ∈ verts := (hmem_verts_inl p).mpr ((hmem_local p).mpr (Or.inl ((hmem_ports p).mp hpports)))
        simp only [hpv, dite_true] at hisR
        by_contra hpA
        have : ((ofRHS ⟨A, σ⟩).val ⟨Sum.inl p, hpv⟩).val =
            Sum.inl (p.1, locPartner (nports p.1) (rowSet A.val p.1) p.2) := by
          simp [ofRHS, ofRHS_fun, hpA]
        rw [this] at hisR; simp at hisR
      · intro hpA
        have hpports : p ∈ ports := (Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) hpA
        have hpv : Sum.inl p ∈ verts := (hmem_verts_inl p).mpr ((hmem_local p).mpr (Or.inl ((hmem_ports p).mp hpports)))
        refine ⟨hpports, ?_⟩
        simp only [hpv, dite_true]
        simp [ofRHS, ofRHS_fun, hpA]
    refine Sigma.ext (Subtype.ext hAeq) ?_
    refine hsigma_snd_heq _ A (Subtype.ext hAeq) _ σ ?_
    intro v p₁ p₂ hp12
    dsimp only [toRHS]
    have hpA' : p₁.val ∈ attOf (ofRHS ⟨A, σ⟩).val := (Finset.mem_filter.mp p₁.property).1
    have hpA : p₂.val ∈ A.val := (Finset.mem_filter.mp p₂.property).1
    have hplab : label p₂.val.1 p₂.val.2 = v.val := (Finset.mem_filter.mp p₂.property).2
    have hpports : p₂.val ∈ ports := (Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1) hpA
    have hpv : Sum.inl p₁.val ∈ verts := (hmem_verts_inl p₁.val).mpr ((hmem_local p₁.val).mpr (Or.inl ((hmem_ports p₁.val).mp
      (hp12 ▸ hpports))))
    have hqc := Classical.choose_spec ((htoA (ofRHS ⟨A, σ⟩)).2.1 p₁.val hpA' hpv)
    have hval : ((ofRHS ⟨A, σ⟩).val ⟨Sum.inl p₁.val, hpv⟩).val =
        Sum.inr (label p₂.val.1 p₂.val.2,
          (σ ⟨label p₂.val.1 p₂.val.2, Finset.mem_image.mpr ⟨p₂.val, hpports, rfl⟩⟩
            ⟨p₂.val, Finset.mem_filter.mpr ⟨hpA, rfl⟩⟩).val) := by
      have hpv2 : Sum.inl p₂.val ∈ verts := hp12 ▸ hpv
      have hsub : (⟨Sum.inl p₁.val, hpv⟩ : ↥verts) = ⟨Sum.inl p₂.val, hpv2⟩ := Subtype.ext (congrArg Sum.inl hp12)
      rw [hsub]; simp [ofRHS, ofRHS_fun, hpA]
    have hqeq := Sum.inr.inj (hqc.1.symm.trans hval)
    change (Classical.choose ((htoA (ofRHS ⟨A, σ⟩)).2.1 p₁.val hpA' hpv)).2 = (σ v p₂).val
    rw [congrArg Prod.snd hqeq]
    have heq_val : ∀ (v₁ v₂ : ↥labels) (hv : v₁ = v₂) (a₁ : ↥(portsV A.val v₁.val)) (a₂ : ↥(portsV A.val v₂.val)),
        a₁.val = a₂.val → (σ v₁ a₁).val = (σ v₂ a₂).val := by
      rintro v₁ _ rfl a₁ a₂ h; rw [Subtype.ext h]
    exact heq_val _ v (Subtype.ext hplab) _ p₂ rfl
  let eqvM : ↥matchings ≃ RHS := ⟨toRHS, ofRHS, hleft, hright⟩
  calc matchings.card
      = Fintype.card ↥matchings := (Fintype.card_coe _).symm
    _ = Fintype.card RHS := Fintype.card_congr eqvM
    _ = ∑ A : ↥validA, Fintype.card (∀ v : ↥labels, ↥(portsV A.val v.val) ≃ Fin (quota v.val)) :=
          Fintype.card_sigma
    _ = ∑ A : ↥validA, ∏ v : ↥labels, Fintype.card (↥(portsV A.val v.val) ≃ Fin (quota v.val)) :=
          Finset.sum_congr rfl (fun A _ => Fintype.card_pi)
    _ = ∑ _A : ↥validA, ∏ v : ↥labels, Nat.factorial (quota v.val) := by
          refine Finset.sum_congr rfl (fun A _ => Finset.prod_congr rfl (fun v _ => ?_))
          refine card_equiv_fin_of_card_eq ?_
          rw [Fintype.card_coe]
          exact (Finset.mem_filter.mp A.property).2.2 v.val v.property
    _ = validA.card * (∏ v ∈ labels, Nat.factorial (quota v)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
          congr 1
          exact Finset.prod_coe_sort labels (fun v => Nat.factorial (quota v))

-- Part B: Character count and coset shifts for Type 0

lemma chars_card_eq {n : Nat} (S : Finset (W n))
    (h0 : (0 : W n) ∈ S) (hadd : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S) :
    ((Finset.univ : Finset (W n)).image (fun z : W n => fun v : ↥S => chi v.val z)).card = S.card := by
  classical
  let Chars := (Finset.univ : Finset (W n)).image (fun z : W n => fun v : ↥S => chi v.val z)
  let Perp := (Finset.univ : Finset (W n)).filter (fun x => ∀ v ∈ S, dotProduct v x = 0)
  have hPerp_pos : 0 < Perp.card := Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v _ => by simp⟩⟩
  have h1 : Chars.card * Perp.card = 2 ^ n := by
    have hfib : ∀ ψ ∈ Chars, ((Finset.univ : Finset (W n)).filter
        (fun z => (fun v : ↥S => chi v.val z) = ψ)).card = Perp.card := by
      intro ψ hψ
      rcases Finset.mem_image.mp hψ with ⟨z₀, _, rfl⟩
      refine Finset.card_bij (fun z _ => z + z₀) ?_ ?_ ?_
      · intro z hz
        have hzeq := (Finset.mem_filter.mp hz).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => ?_⟩
        have hv1 : chi v z = chi v z₀ := congrFun hzeq ⟨v, hv⟩
        have hdot : dotProduct v z = dotProduct v z₀ := sgn_inj hv1
        rw [dotProduct_add, hdot, zmod2_add_self]
      · intro z₁ _ z₂ _ h; exact add_right_cancel h
      · intro x hx
        have hxd := (Finset.mem_filter.mp hx).2
        refine ⟨x + z₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by rw [add_assoc, vec_add_self, add_zero]⟩
        funext ⟨v, hv⟩
        unfold chi
        rw [dotProduct_add, hxd v hv, zero_add]
    have hsum := Finset.card_eq_sum_card_fiberwise (f := fun z : W n => fun v : ↥S => chi v.val z)
      (s := Finset.univ) (t := Chars) (fun z _ => Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩)
    rw [Finset.card_univ, card_W] at hsum
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
    exact hsum.symm
  have h2 : (S.card : Int) * (Perp.card : Int) = (2 : Int) ^ n := by
    have hsum1 : (∑ x : W n, ∑ v ∈ S, chi v x) = (2 : Int) ^ n := by
      rw [Finset.sum_comm]
      have hterm : ∀ v ∈ S, (∑ x : W n, chi v x) = if v = 0 then (2 : Int) ^ n else 0 :=
        fun v _ => sum_chi_eq v
      rw [Finset.sum_congr rfl hterm]
      simp [h0]
    have hsum2 : (∑ x : W n, ∑ v ∈ S, chi v x) = (Perp.card : Int) * (S.card : Int) := by
      have hterm : ∀ x : W n, (∑ v ∈ S, chi v x) = if x ∈ Perp then (S.card : Int) else 0 := by
        intro x
        rw [sum_chi_subgroup S h0 hadd x]
        simp [Perp]
      simp_rw [hterm]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    linarith
  have h2nat : S.card * Perp.card = 2 ^ n := by exact_mod_cast h2
  have hmul : Chars.card * Perp.card = S.card * Perp.card := h1.trans h2nat.symm
  exact Nat.eq_of_mul_eq_mul_right hPerp_pos hmul

def shiftPred {n m : Nat} (a b : Fin m → W n) (z : W n)
    (p : (Fin m → W n) × (Fin m → F)) : (Fin m → W n) × (Fin m → F) :=
  (fun i => p.1 i + dotProduct (b i) z • a i + dotProduct (a i) z • b i,
   fun i => p.2 i + dotProduct (p.1 i) z + dotProduct (a i) z * dotProduct (b i) z)

lemma shiftPred_invol {n m : Nat} (a b : Fin m → W n) (z : W n)
    (p : (Fin m → W n) × (Fin m → F)) :
    shiftPred a b z (shiftPred a b z p) = p := by
  rcases p with ⟨P, d⟩
  refine Prod.ext ?_ ?_
  · funext i
    dsimp only [shiftPred]
    have h1 : dotProduct (b i) z • a i + dotProduct (b i) z • a i = 0 := vec_add_self _
    have h2 : dotProduct (a i) z • b i + dotProduct (a i) z • b i = 0 := vec_add_self _
    calc (P i + dotProduct (b i) z • a i + dotProduct (a i) z • b i) +
            dotProduct (b i) z • a i + dotProduct (a i) z • b i
        = P i + (dotProduct (b i) z • a i + dotProduct (b i) z • a i) +
            (dotProduct (a i) z • b i + dotProduct (a i) z • b i) := by abel
      _ = P i := by rw [h1, h2, add_zero, add_zero]
  · funext i
    dsimp only [shiftPred]
    rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have hz1 : dotProduct (P i) z + dotProduct (P i) z = 0 := zmod2_add_self _
    have hz2 : dotProduct (a i) z * dotProduct (b i) z + dotProduct (a i) z * dotProduct (b i) z = 0 :=
      zmod2_add_self _
    have hcomm : dotProduct (b i) z * dotProduct (a i) z = dotProduct (a i) z * dotProduct (b i) z :=
      mul_comm _ _
    rw [hcomm]
    calc d i + dotProduct (P i) z + dotProduct (a i) z * dotProduct (b i) z +
            (dotProduct (P i) z + dotProduct (a i) z * dotProduct (b i) z +
              dotProduct (a i) z * dotProduct (b i) z) +
            dotProduct (a i) z * dotProduct (b i) z
        = d i + (dotProduct (P i) z + dotProduct (P i) z) +
            (dotProduct (a i) z * dotProduct (b i) z + dotProduct (a i) z * dotProduct (b i) z) +
            (dotProduct (a i) z * dotProduct (b i) z + dotProduct (a i) z * dotProduct (b i) z) := by ring
      _ = d i := by rw [hz1, hz2, add_zero, add_zero, add_zero]

lemma shiftPred_err_iff {n m : Nat} (a b : Fin m → W n) (z : W n)
    (p : (Fin m → W n) × (Fin m → F)) (x : W n) (i : Fin m) :
    (dotProduct (a i) x * dotProduct (b i) x ≠
      dotProduct ((shiftPred a b z p).1 i) x + (shiftPred a b z p).2 i) ↔
    (dotProduct (a i) (x + z) * dotProduct (b i) (x + z) ≠
      dotProduct (p.1 i) (x + z) + p.2 i) := by
  dsimp only [shiftPred]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    dotProduct_add, dotProduct_add, dotProduct_add]
  have hsum :
      (dotProduct (a i) x * dotProduct (b i) x +
        (dotProduct (p.1 i) x + dotProduct (b i) z * dotProduct (a i) x +
          dotProduct (a i) z * dotProduct (b i) x +
          (p.2 i + dotProduct (p.1 i) z + dotProduct (a i) z * dotProduct (b i) z))) =
      ((dotProduct (a i) x + dotProduct (a i) z) * (dotProduct (b i) x + dotProduct (b i) z) +
        (dotProduct (p.1 i) x + dotProduct (p.1 i) z + p.2 i)) := by ring
  constructor <;> intro h heq
  · apply h
    have h0 : ((dotProduct (a i) x + dotProduct (a i) z) * (dotProduct (b i) x + dotProduct (b i) z) +
        (dotProduct (p.1 i) x + dotProduct (p.1 i) z + p.2 i)) = 0 := (zmod2_add_eq_zero_iff _ _).mpr heq
    rw [← hsum] at h0
    exact (zmod2_add_eq_zero_iff _ _).mp h0
  · apply h
    have h0 : (dotProduct (a i) x * dotProduct (b i) x +
        (dotProduct (p.1 i) x + dotProduct (b i) z * dotProduct (a i) x +
          dotProduct (a i) z * dotProduct (b i) x +
          (p.2 i + dotProduct (p.1 i) z + dotProduct (a i) z * dotProduct (b i) z))) = 0 :=
      (zmod2_add_eq_zero_iff _ _).mpr heq
    rw [hsum] at h0
    exact (zmod2_add_eq_zero_iff _ _).mp h0

lemma shiftPred_in_plane {n m : Nat} (a b : Fin m → W n) (z : W n)
    (p : (Fin m → W n) × (Fin m → F)) (i : Fin m) (hP : p.1 i ∈ planeOf (a i) (b i)) :
    (shiftPred a b z p).1 i ∈ planeOf (a i) (b i) := by
  dsimp only [shiftPred]
  have h1 : dotProduct (b i) z • a i ∈ planeOf (a i) (b i) := by
    rcases zmod2_cases (dotProduct (b i) z) with h | h <;> rw [h] <;> simp [planeOf]
  have h2 : dotProduct (a i) z • b i ∈ planeOf (a i) (b i) := by
    rcases zmod2_cases (dotProduct (a i) z) with h | h <;> rw [h] <;> simp [planeOf]
  exact planeOf_add_mem (planeOf_add_mem hP h1) h2

lemma shiftPred_totalCoeff {n m : Nat} (a b : Fin m → W n) (z : W n)
    (p : (Fin m → W n) × (Fin m → F)) (e : Nat) (v : W n) :
    totalCoeff a b (shiftPred a b z p).1 (shiftPred a b z p).2 e v =
      chi v z * totalCoeff a b p.1 p.2 e v := by
  let g1 : W n → Int := fun x => (4 * e : Int) - 4 * (((Finset.univ : Finset (Fin m)).filter (fun i =>
    dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (p.1 i) x + p.2 i)).card : Int)
  let g2 : W n → Int := fun x => (4 * e : Int) - 4 * (((Finset.univ : Finset (Fin m)).filter (fun i =>
    dotProduct (a i) x * dotProduct (b i) x ≠
      dotProduct ((shiftPred a b z p).1 i) x + (shiftPred a b z p).2 i)).card : Int)
  have hg2_eq : ∀ x : W n, g2 x = g1 (x + z) := by
    intro x
    dsimp only [g1, g2]
    have hfilt : (Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠
          dotProduct ((shiftPred a b z p).1 i) x + (shiftPred a b z p).2 i) =
      (Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (a i) (x + z) * dotProduct (b i) (x + z) ≠
          dotProduct (p.1 i) (x + z) + p.2 i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact shiftPred_err_iff a b z p x i
    rw [hfilt]
  have hinv1 := fourier_inv g1 (totalCoeff a b p.1 p.2 e) (fun x => errs_fourier a b p.1 p.2 e x) v
  have hinv2 := fourier_inv g2 (totalCoeff a b (shiftPred a b z p).1 (shiftPred a b z p).2 e)
    (fun x => errs_fourier a b (shiftPred a b z p).1 (shiftPred a b z p).2 e x) v
  have hsum : (∑ x : W n, g2 x * chi v x) = chi v z * ∑ y : W n, g1 y * chi v y := by
    have hshift : (∑ x : W n, g1 (x + z) * chi v x) = ∑ y : W n, g1 y * chi v (y + z) := by
      refine Fintype.sum_equiv (Equiv.addRight z) _ _ (fun x => ?_)
      simp [add_assoc, vec_add_self]
    simp_rw [hg2_eq]
    rw [hshift, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hchiy : chi v (y + z) = chi v y * chi v z := by
      unfold chi; rw [dotProduct_add, sgn_add]
    rw [hchiy]; ring
  have h2pos : (0 : Int) < (2 : Int) ^ n := by positivity
  rw [hinv2, hinv1] at hsum
  have hmul : (2 : Int) ^ n * totalCoeff a b (shiftPred a b z p).1 (shiftPred a b z p).2 e v =
      (2 : Int) ^ n * (chi v z * totalCoeff a b p.1 p.2 e v) := by linarith
  exact mul_left_cancel₀ (ne_of_gt h2pos) hmul

-- Part C: Exact row-level bijections between (P i, d i) and negative port subsets

lemma distinct_tri {n : Nat} {a b : W n} (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) :
    a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 ∧ a ≠ b ∧ a ≠ a + b ∧ b ≠ a + b := by
  rcases hnd with ⟨ha0, hb0, hab⟩
  have hab0 : a + b ≠ 0 := fun h => hab ((vec_add_eq_zero_iff a b).mp h)
  have haba : a ≠ a + b := by
    intro h
    have h1 : a + a = a + (a + b) := congrArg (fun z => a + z) h
    rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h1
    exact hb0 h1.symm
  have habb : b ≠ a + b := by
    intro h
    have h1 : b + b = (a + b) + b := congrArg (fun z => z + b) h
    rw [vec_add_self, add_assoc, vec_add_self, add_zero] at h1
    exact ha0 h1.symm
  exact ⟨ha0, hb0, hab0, hab, haba, habb⟩

lemma nonpivot_row_values {n : Nat} {a b P : W n} (d : F)
    (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (hP : P ∈ planeOf a b) (h0 : rowCoeff a b P d 0 = 1) :
    (P = 0 ∧ d = 0) ∨ (P = a ∧ d = 0) ∨ (P = b ∧ d = 0) ∨ (P = a + b ∧ d = 1) := by
  rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
  simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with hP | hP | hP | hP <;> rcases zmod2_cases d with hd | hd <;> rw [hP, hd] at h0 ⊢
  · left; exact ⟨rfl, rfl⟩
  · unfold rowCoeff at h0; simp [sgn_one, ha0.symm, hb0.symm, hab0.symm] at h0
  · right; left; exact ⟨rfl, rfl⟩
  · unfold rowCoeff at h0; simp [sgn_one, vec_add_self, ha0.symm, hb0.symm, hab0.symm] at h0
  · right; right; left; exact ⟨rfl, rfl⟩
  · unfold rowCoeff at h0
    have hba : b + a = a + b := add_comm b a
    have habb' : a + b + b = a := by rw [add_assoc, vec_add_self, add_zero]
    simp [sgn_one, hba, habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm] at h0
  · unfold rowCoeff at h0
    have haba' : a + b + a = b := by rw [add_comm (a + b) a, ← add_assoc, vec_add_self, zero_add]
    have habb' : a + b + b = a := by rw [add_assoc, vec_add_self, add_zero]
    simp [sgn_zero, haba', habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm] at h0
  · right; right; right; exact ⟨rfl, rfl⟩

def nonpivotFromSub {n : Nat} (a b : W n) (A : Finset Nat) : W n × F :=
  if 0 ∈ A ∧ 1 ∈ A then (0, 0)
  else if 0 ∈ A ∧ 2 ∈ A then (a, 0)
  else if 1 ∈ A ∧ 2 ∈ A then (b, 0)
  else (a + b, 1)

def nonpivotToSub {n : Nat} (a b P : W n) (d : F) : Finset Nat :=
  (Finset.range 3).filter (fun j =>
    rowCoeff a b P d (if j = 0 then a else if j = 1 then b else a + b) = -1)

lemma nonpivot_rowCoeff_cases {n : Nat} {a b P : W n} {d : F}
    (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
    (hPd : (P = 0 ∧ d = 0) ∨ (P = a ∧ d = 0) ∨ (P = b ∧ d = 0) ∨ (P = a + b ∧ d = 1)) :
    P ∈ planeOf a b ∧ rowCoeff a b P d 0 = 1 ∧
    (∀ v : W n, v ≠ 0 → v ∉ triOf a b → rowCoeff a b P d v = 0) ∧
    (∀ j < 3, rowCoeff a b P d (if j = 0 then a else if j = 1 then b else a + b) =
      if j ∈ nonpivotToSub a b P d then -1 else 1) ∧
    (nonpivotToSub a b P d ⊆ Finset.range 3) ∧
    (nonpivotToSub a b P d).card % 2 = 0 ∧
    nonpivotFromSub a b (nonpivotToSub a b P d) = (P, d) := by
  rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
  have hba : b + a = a + b := add_comm b a
  have haba' : a + b + a = b := by rw [add_comm (a + b) a, ← add_assoc, vec_add_self, zero_add]
  have habb' : a + b + b = a := by rw [add_assoc, vec_add_self, add_zero]
  rcases hPd with ⟨hP, hd⟩ | ⟨hP, hd⟩ | ⟨hP, hd⟩ | ⟨hP, hd⟩ <;> rw [hP, hd]
  · have hr0 : rowCoeff a b 0 0 0 = 1 := by unfold rowCoeff; simp [sgn_zero, ha0.symm, hb0.symm, hab0.symm]
    have hra : rowCoeff a b 0 0 a = -1 := by unfold rowCoeff; simp [sgn_zero, ha0, hab, haba]
    have hrb : rowCoeff a b 0 0 b = -1 := by unfold rowCoeff; simp [sgn_zero, hb0, hab.symm, habb]
    have hrab : rowCoeff a b 0 0 (a + b) = 1 := by unfold rowCoeff; simp [sgn_zero, hab0, haba.symm, habb.symm]
    have hsub : nonpivotToSub a b 0 0 = {0, 1} := by
      ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hj, hr⟩; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl | rfl; left; rfl; right; rfl; simp [hrab] at hr
      · rintro (rfl | rfl) <;> simp [hra, hrb]
    refine ⟨by simp [planeOf], hr0, ?_, ?_, ?_, by rw [hsub]; decide, by rw [hsub]; simp [nonpivotFromSub]⟩
    · intro v hv0 hnt; unfold rowCoeff; simp only [triOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hnt
      simp [hv0, hnt.1, hnt.2.1, hnt.2.2]
    · intro j hj; rw [hsub]; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [hra, hrb, hrab]
    · rw [hsub]; intro j hj; simp at hj ⊢; omega
  · have hr0 : rowCoeff a b a 0 0 = 1 := by unfold rowCoeff; simp [sgn_zero, vec_add_self, ha0.symm, hb0.symm, hab0.symm]
    have hra : rowCoeff a b a 0 a = -1 := by unfold rowCoeff; simp [sgn_zero, vec_add_self, ha0, hab, haba]
    have hrb : rowCoeff a b a 0 b = 1 := by unfold rowCoeff; simp [sgn_zero, vec_add_self, hb0, hab.symm, habb]
    have hrab : rowCoeff a b a 0 (a + b) = -1 := by unfold rowCoeff; simp [sgn_zero, vec_add_self, hab0, haba.symm, habb.symm]
    have hsub : nonpivotToSub a b a 0 = {0, 2} := by
      ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hj, hr⟩; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl | rfl; left; rfl; simp [hrb] at hr; right; rfl
      · rintro (rfl | rfl) <;> simp [hra, hrab]
    refine ⟨by simp [planeOf], hr0, ?_, ?_, ?_, by rw [hsub]; decide, by rw [hsub]; simp [nonpivotFromSub]⟩
    · intro v hv0 hnt; unfold rowCoeff; simp only [triOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hnt
      simp [hv0, vec_add_self, hnt.1, hnt.2.1, hnt.2.2]
    · intro j hj; rw [hsub]; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [hra, hrb, hrab]
    · rw [hsub]; intro j hj; simp at hj ⊢; omega
  · have hr0 : rowCoeff a b b 0 0 = 1 := by unfold rowCoeff; simp [sgn_zero, hba, habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm]
    have hra : rowCoeff a b b 0 a = 1 := by unfold rowCoeff; simp [sgn_zero, hba, habb', vec_add_self, ha0, hab, haba]
    have hrb : rowCoeff a b b 0 b = -1 := by unfold rowCoeff; simp [sgn_zero, hba, habb', vec_add_self, hb0, hab.symm, habb]
    have hrab : rowCoeff a b b 0 (a + b) = -1 := by unfold rowCoeff; simp [sgn_zero, hba, habb', vec_add_self, hab0, haba.symm, habb.symm]
    have hsub : nonpivotToSub a b b 0 = {1, 2} := by
      ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hj, hr⟩; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl | rfl; simp [hra] at hr; left; rfl; right; rfl
      · rintro (rfl | rfl) <;> simp [hrb, hrab]
    refine ⟨by simp [planeOf], hr0, ?_, ?_, ?_, by rw [hsub]; decide, by rw [hsub]; simp [nonpivotFromSub]⟩
    · intro v hv0 hnt; unfold rowCoeff; simp only [triOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hnt
      simp [hv0, hba, habb', vec_add_self, hnt.1, hnt.2.1, hnt.2.2]
    · intro j hj; rw [hsub]; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [hra, hrb, hrab]
    · rw [hsub]; intro j hj; simp at hj ⊢; omega
  · have hr0 : rowCoeff a b (a + b) 1 0 = 1 := by unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, ha0.symm, hb0.symm, hab0.symm]
    have hra : rowCoeff a b (a + b) 1 a = 1 := by unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, ha0, hab, haba]
    have hrb : rowCoeff a b (a + b) 1 b = 1 := by unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, hb0, hab.symm, habb]
    have hrab : rowCoeff a b (a + b) 1 (a + b) = 1 := by unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, hab0, haba.symm, habb.symm]
    have hsub : nonpivotToSub a b (a + b) 1 = ∅ := by
      ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro hj; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [hra, hrb, hrab]
    refine ⟨by simp [planeOf], hr0, ?_, ?_, ?_, by rw [hsub]; decide, by rw [hsub]; simp [nonpivotFromSub]⟩
    · intro v hv0 hnt; unfold rowCoeff; simp only [triOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hnt
      simp [hv0, haba', habb', vec_add_self, hnt.1, hnt.2.1, hnt.2.2]
    · intro j hj; rw [hsub]; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [hra, hrb, hrab]
    · rw [hsub]; exact Finset.empty_subset _

lemma nonpivot_even_subsets (A : Finset Nat) (hA : A ⊆ Finset.range 3) (heven : A.card % 2 = 0) :
    A = {0, 1} ∨ A = {0, 2} ∨ A = {1, 2} ∨ A = ∅ := by
  have hle : A.card ≤ 3 := (Finset.card_le_card hA).trans (by simp)
  have hc : A.card = 0 ∨ A.card = 2 := by omega
  rcases hc with h0 | h2
  · right; right; right; exact Finset.card_eq_zero.mp h0
  · have hccomp : (Finset.range 3 \ A).card = 1 := by
      have := Finset.card_sdiff_add_card_eq_card hA; rw [Finset.card_range] at this; omega
    rcases Finset.card_eq_one.mp hccomp with ⟨u, hu⟩
    have hu3 : u < 3 := Finset.mem_range.mp (Finset.mem_sdiff.mp (hu ▸ Finset.mem_singleton_self u)).1
    have hAeq : A = (Finset.range 3).erase u := by
      ext x
      have hx_iff : x ∈ Finset.range 3 \ A ↔ x = u := by rw [hu, Finset.mem_singleton]
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hx_iff ⊢
      constructor
      · intro hx; exact ⟨fun h => (hx_iff.mpr h).2 hx, hA hx⟩
      · rintro ⟨hxu, hxr⟩; by_contra hna; exact hxu (hx_iff.mp ⟨hxr, hna⟩)
    rw [hAeq]
    have : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases this with rfl | rfl | rfl
    · right; right; left; decide
    · right; left; decide
    · left; decide

lemma nonpivot_fromSub_roundtrip {n : Nat} {a b : W n} (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
    (A : Finset Nat) (hA : A ⊆ Finset.range 3) (heven : A.card % 2 = 0) :
    let pd := nonpivotFromSub a b A
    ((pd.1 = 0 ∧ pd.2 = 0) ∨ (pd.1 = a ∧ pd.2 = 0) ∨ (pd.1 = b ∧ pd.2 = 0) ∨ (pd.1 = a + b ∧ pd.2 = 1)) ∧
    nonpivotToSub a b pd.1 pd.2 = A := by
  rcases nonpivot_even_subsets A hA heven with rfl | rfl | rfl | rfl
  · have hpd : nonpivotFromSub a b {0, 1} = (0, 0) := by simp [nonpivotFromSub]
    refine ⟨by rw [hpd]; exact Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [hpd]
    have h := nonpivot_rowCoeff_cases hnd (Or.inl ⟨rfl, rfl⟩)
    rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
    ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hj, hr⟩; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl; left; rfl; right; rfl
      unfold rowCoeff at hr; simp [sgn_zero, hab0, haba.symm, habb.symm] at hr
    · rintro (rfl | rfl)
      · refine ⟨by omega, ?_⟩; unfold rowCoeff; simp [sgn_zero, ha0, hab, haba]
      · refine ⟨by omega, ?_⟩; unfold rowCoeff; simp [sgn_zero, hb0, hab.symm, habb]
  · have hpd : nonpivotFromSub a b {0, 2} = (a, 0) := by simp [nonpivotFromSub]
    refine ⟨by rw [hpd]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    rw [hpd]
    rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
    ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hj, hr⟩; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl; left; rfl
      unfold rowCoeff at hr; simp [sgn_zero, vec_add_self, hb0, hab.symm, habb] at hr
      right; rfl
    · rintro (rfl | rfl)
      · refine ⟨by omega, ?_⟩; unfold rowCoeff; simp [sgn_zero, vec_add_self, ha0, hab, haba]
      · refine ⟨by omega, ?_⟩; unfold rowCoeff; simp [sgn_zero, vec_add_self, hab0, haba.symm, habb.symm]
  · have hpd : nonpivotFromSub a b {1, 2} = (b, 0) := by simp [nonpivotFromSub]
    refine ⟨by rw [hpd]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    rw [hpd]
    rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
    have hba : b + a = a + b := add_comm b a
    have habb' : a + b + b = a := by rw [add_assoc, vec_add_self, add_zero]
    ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hj, hr⟩; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl
      unfold rowCoeff at hr; simp [sgn_zero, hba, habb', vec_add_self, ha0, hab, haba] at hr
      left; rfl; right; rfl
    · rintro (rfl | rfl)
      · refine ⟨by omega, ?_⟩; unfold rowCoeff; simp [sgn_zero, hba, habb', vec_add_self, hb0, hab.symm, habb]
      · refine ⟨by omega, ?_⟩; unfold rowCoeff; simp [sgn_zero, hba, habb', vec_add_self, hab0, haba.symm, habb.symm]
  · have hpd : nonpivotFromSub a b ∅ = (a + b, 1) := by simp [nonpivotFromSub]
    refine ⟨by rw [hpd]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    rw [hpd]
    rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
    have haba' : a + b + a = b := by rw [add_comm (a + b) a, ← add_assoc, vec_add_self, zero_add]
    have habb' : a + b + b = a := by rw [add_assoc, vec_add_self, add_zero]
    ext j; simp only [nonpivotToSub, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    intro hj; have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, ha0, hab, haba]
    · unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, hb0, hab.symm, habb]
    · unfold rowCoeff; simp [sgn_one, haba', habb', vec_add_self, hab0, haba.symm, habb.symm]

def pivotLab {n : Nat} (u a b : W n) (j : Nat) : W n :=
  u + (if j = 0 then 0 else if j = 1 then a else if j = 2 then b else a + b)

def pivotToSub {n : Nat} (u a b P : W n) (d : F) : Finset Nat :=
  (Finset.range 4).filter (fun j => rowCoeff a b P d (pivotLab u a b j) = -1)

def pivotFromSub {n : Nat} (u a b : W n) (A : Finset Nat) : W n × F :=
  let d : F := if A.card = 1 then 1 else 0
  let t : Nat :=
    if A.card = 1 then
      if 3 ∈ A then 0 else if 2 ∈ A then 1 else if 1 ∈ A then 2 else 3
    else
      if 3 ∉ A then 0 else if 2 ∉ A then 1 else if 1 ∉ A then 2 else 3
  (pivotLab u a b t, d)

lemma pivot_rowCoeff_cases {n : Nat} {u a b P : W n} {d : F}
    (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (hu : u ∉ planeOf a b)
    (hP : P ∈ (planeOf a b).image (fun w => u + w)) :
    P ∉ planeOf a b ∧ rowCoeff a b P d 0 = 2 ∧
    (∀ v : W n, v ∉ (planeOf a b).image (fun w => u + w) → v ≠ 0 → rowCoeff a b P d v = 0) ∧
    (∀ j < 4, rowCoeff a b P d (pivotLab u a b j) = if j ∈ pivotToSub u a b P d then -1 else 1) ∧
    (pivotToSub u a b P d ⊆ Finset.range 4) ∧
    (pivotToSub u a b P d).card % 2 = 1 ∧
    pivotFromSub u a b (pivotToSub u a b P d) = (P, d) := by
  rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
  have hPl : ∀ t < 4, pivotLab u a b t ∈ (planeOf a b).image (fun w => u + w) := fun t ht => by
    unfold pivotLab; refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
    have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [planeOf]
  have hPl_inj : ∀ j₁ < 4, ∀ j₂ < 4, pivotLab u a b j₁ = pivotLab u a b j₂ → j₁ = j₂ := by
    intro j₁ h1 j₂ h2 heq
    have hc := add_left_cancel heq
    have : j₁ = 0 ∨ j₁ = 1 ∨ j₁ = 2 ∨ j₁ = 3 := by omega
    have : j₂ = 0 ∨ j₂ = 1 ∨ j₂ = 2 ∨ j₂ = 3 := by omega
    rcases ‹j₁ = 0 ∨ _› with rfl | rfl | rfl | rfl <;> rcases ‹j₂ = 0 ∨ _› with rfl | rfl | rfl | rfl <;>
      simp at hc <;> (first | rfl | exact absurd hc ha0 | exact absurd hc ha0.symm | exact absurd hc hb0 | exact absurd hc hb0.symm | exact absurd hc hab0 | exact absurd hc hab0.symm | exact absurd hc hab | exact absurd hc hab.symm | exact absurd hc haba | exact absurd hc haba.symm | exact absurd hc habb | exact absurd hc habb.symm)
  have hPl_ne0 : ∀ j < 4, pivotLab u a b j ≠ 0 := by
    intro j hj h0
    have hmem : pivotLab u a b j ∈ (planeOf a b).image (fun w => u + w) := hPl j hj
    exact Finset.disjoint_left.mp (disjoint_planeOf_image hu) (by simp [planeOf] : (0 : W n) ∈ planeOf a b) (h0 ▸ hmem)
  have hPnot : P ∉ planeOf a b := fun hm => Finset.disjoint_left.mp (disjoint_planeOf_image hu) hm hP
  have hr0 : rowCoeff a b P d 0 = 2 := (rowCoeff_not_in_plane d hnd hPnot).1
  have hP_coset : ∀ w ∈ planeOf a b, P + w ∈ (planeOf a b).image (fun z => u + z) := by
    intro w hw
    rcases Finset.mem_image.mp hP with ⟨z, hz, rfl⟩
    refine Finset.mem_image.mpr ⟨z + w, planeOf_add_mem hz hw, by abel⟩
  have hP_other : ∀ v : W n, v ∉ (planeOf a b).image (fun w => u + w) → v ≠ 0 → rowCoeff a b P d v = 0 := by
    intro v hv hv0
    have h1 : v ≠ P := fun h => hv (h ▸ hP)
    have h2 : v ≠ P + a := fun h => hv (h ▸ hP_coset a (by simp [planeOf]))
    have h3 : v ≠ P + b := fun h => hv (h ▸ hP_coset b (by simp [planeOf]))
    have h4 : v ≠ P + a + b := fun h => hv (by rw [h, add_assoc]; exact hP_coset (a + b) (by simp [planeOf]))
    unfold rowCoeff; simp [hv0, h1, h2, h3, h4]
  have hex_t : ∃ t < 4, P = pivotLab u a b t := by
    rcases Finset.mem_image.mp hP with ⟨z, hz, rfl⟩
    simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by simp [pivotLab]⟩
    · exact ⟨1, by omega, by simp [pivotLab]⟩
    · exact ⟨2, by omega, by simp [pivotLab]⟩
    · exact ⟨3, by omega, by simp [pivotLab]⟩
  rcases hex_t with ⟨t, ht, rfl⟩
  let opp : Nat := 3 - t
  have hopp_lt : opp < 4 := by omega
  have hPab : pivotLab u a b t + a + b = pivotLab u a b opp := by
    have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> unfold pivotLab opp
    · simp [add_assoc]
    · simp only [Nat.reduceEqDiff, ite_false, ite_true, Nat.reduceSub]
      calc u + a + a + b = u + (a + a) + b := by abel
        _ = u + b := by rw [vec_add_self, add_zero]
    · simp only [Nat.reduceEqDiff, ite_false, ite_true, Nat.reduceSub]
      calc u + b + a + b = u + a + (b + b) := by abel
        _ = u + a := by rw [vec_add_self, add_zero]
    · simp only [Nat.reduceEqDiff, ite_false, ite_true, Nat.reduceSub, add_zero]
      calc u + (a + b) + a + b = u + (a + a) + (b + b) := by abel
        _ = u := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
  have hval : ∀ j < 4, rowCoeff a b (pivotLab u a b t) d (pivotLab u a b j) =
      if j = opp then sgn d else - sgn d := by
    intro j hj
    have hne0 := hPl_ne0 j hj
    have h4set : ∀ v ∈ (planeOf a b).image (fun w => u + w),
        v = pivotLab u a b t ∨ v = pivotLab u a b t + a ∨
        v = pivotLab u a b t + b ∨ v = pivotLab u a b t + a + b := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hP with ⟨z, hz, hz_eq⟩
      have hzw : z + w ∈ planeOf a b := planeOf_add_mem hz hw
      simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hzw
      have hrewrite : u + w = pivotLab u a b t + (z + w) := by
        rw [← hz_eq]; calc u + w = u + (z + z) + w := by rw [vec_add_self, add_zero]
          _ = (u + z) + (z + w) := by abel
      rw [hrewrite]
      rcases hzw with h | h | h | h <;> rw [h]
      · left; simp
      · right; left; rfl
      · right; right; left; rfl
      · right; right; right; rw [add_assoc]
    have h12 : pivotLab u a b t ≠ pivotLab u a b t + a := by
      intro h; have := add_left_cancel (a := pivotLab u a b t) (by simpa using h); exact ha0 this
    have h13 : pivotLab u a b t ≠ pivotLab u a b t + b := by
      intro h; have := add_left_cancel (a := pivotLab u a b t) (by simpa using h); exact hb0 this
    have h14 : pivotLab u a b t ≠ pivotLab u a b t + a + b := by
      intro h; rw [add_assoc] at h; have := add_left_cancel (a := pivotLab u a b t) (by simpa using h); exact hab0 this
    have h23 : pivotLab u a b t + a ≠ pivotLab u a b t + b := fun h => hab (add_left_cancel h)
    have h24 : pivotLab u a b t + a ≠ pivotLab u a b t + a + b := by
      intro h; have := add_left_cancel (a := pivotLab u a b t + a) (by simpa using h); exact hb0 this
    have h34 : pivotLab u a b t + b ≠ pivotLab u a b t + a + b := by
      intro h; rw [add_right_comm] at h; have := add_left_cancel (a := pivotLab u a b t + b) (by simpa using h); exact ha0 this
    by_cases hjopp : j = opp
    · subst hjopp
      rw [if_pos rfl, ← hPab]
      rw [← hPab] at hne0
      unfold rowCoeff
      simp [hne0, h14.symm, h24.symm, h34.symm]
    · rw [if_neg hjopp]
      have hne4 : pivotLab u a b j ≠ pivotLab u a b t + a + b := by
        rw [hPab]; intro heq; exact hjopp (hPl_inj j hj opp hopp_lt heq)
      rcases h4set (pivotLab u a b j) (hPl j hj) with h | h | h | h
      · unfold rowCoeff; rw [h]; simp [h ▸ hne0, h12, h13, h14]
      · unfold rowCoeff; rw [h]; simp [h ▸ hne0, h12.symm, h23, h24]
      · unfold rowCoeff; rw [h]; simp [h ▸ hne0, h13.symm, h23.symm, h34]
      · exact absurd h hne4
  have hsub_eq : pivotToSub u a b (pivotLab u a b t) d =
      if d = 1 then {opp} else (Finset.range 4).erase opp := by
    ext j
    simp only [pivotToSub, Finset.mem_filter, Finset.mem_range]
    rcases zmod2_cases d with rfl | rfl
    · simp only [zmod2_zero_ne_one, ite_false, Finset.mem_erase, Finset.mem_range]
      constructor
      · intro ⟨hj, hr⟩; rw [hval j hj, sgn_zero] at hr
        refine ⟨?_, hj⟩; intro heq; rw [if_pos heq] at hr; omega
      · intro ⟨hne, hj⟩; refine ⟨hj, ?_⟩; rw [hval j hj, if_neg hne, sgn_zero]
    · simp only [ite_true, Finset.mem_singleton]
      constructor
      · intro ⟨hj, hr⟩; rw [hval j hj, sgn_one] at hr
        by_contra hne; rw [if_neg hne] at hr; omega
      · rintro rfl; refine ⟨hopp_lt, ?_⟩; rw [hval opp hopp_lt, if_pos rfl, sgn_one]
  refine ⟨hPnot, hr0, hP_other, ?_, Finset.filter_subset _ _, ?_, ?_⟩
  · intro j hj
    rw [hval j hj, hsub_eq]
    rcases zmod2_cases d with rfl | rfl
    · simp only [zmod2_zero_ne_one, ite_false, sgn_zero, Finset.mem_erase, Finset.mem_range, hj, and_true]
      split_ifs <;> first | rfl | contradiction
    · simp only [ite_true, sgn_one, Finset.mem_singleton]
      split_ifs <;> first | rfl | contradiction
  · rw [hsub_eq]
    rcases zmod2_cases d with rfl | rfl
    · simp [Finset.card_erase_of_mem (Finset.mem_range.mpr hopp_lt)]
    · simp
  · rw [hsub_eq]
    have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases zmod2_cases d with rfl | rfl
    · have hcard3 : ((Finset.range 4).erase opp).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hopp_lt), Finset.card_range]
      unfold pivotFromSub
      simp only [zmod2_zero_ne_one, ite_false, hcard3, Nat.reduceEqDiff]
      rcases ht_cases with rfl | rfl | rfl | rfl <;>
        (dsimp only [opp]; simp)
    · unfold pivotFromSub
      simp only [ite_true, Finset.card_singleton]
      rcases ht_cases with rfl | rfl | rfl | rfl <;>
        (dsimp only [opp]; simp)

lemma pivotToSub_lab {n : Nat} {u a b : W n} (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
    (hu : u ∉ planeOf a b) {t : Nat} (ht : t < 4) (d : F) :
    pivotToSub u a b (pivotLab u a b t) d =
      if d = 1 then {3 - t} else (Finset.range 4).erase (3 - t) := by
  have hPl : pivotLab u a b t ∈ (planeOf a b).image (fun w => u + w) := by
    unfold pivotLab; refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
    have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [planeOf]
  have hrc := pivot_rowCoeff_cases hnd hu hPl (d := d)
  have hrt := hrc.2.2.2.2.2.2
  have hsub := hrc.2.2.2.2.1
  have hodd := hrc.2.2.2.2.2.1
  have hle : (pivotToSub u a b (pivotLab u a b t) d).card ≤ 4 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hPl_inj : ∀ j₁ < 4, ∀ j₂ < 4, pivotLab u a b j₁ = pivotLab u a b j₂ → j₁ = j₂ := by
    intro j₁ h1 j₂ h2 heq
    have hc := add_left_cancel heq
    rcases distinct_tri hnd with ⟨ha0, hb0, hab0, hab, haba, habb⟩
    have : j₁ = 0 ∨ j₁ = 1 ∨ j₁ = 2 ∨ j₁ = 3 := by omega
    have : j₂ = 0 ∨ j₂ = 1 ∨ j₂ = 2 ∨ j₂ = 3 := by omega
    rcases ‹j₁ = 0 ∨ _› with rfl | rfl | rfl | rfl <;> rcases ‹j₂ = 0 ∨ _› with rfl | rfl | rfl | rfl <;>
      simp at hc <;> (first | rfl | exact absurd hc ha0 | exact absurd hc ha0.symm | exact absurd hc hb0 | exact absurd hc hb0.symm | exact absurd hc hab0 | exact absurd hc hab0.symm | exact absurd hc hab | exact absurd hc hab.symm | exact absurd hc haba | exact absurd hc haba.symm | exact absurd hc habb | exact absurd hc habb.symm)
  rcases zmod2_cases d with rfl | rfl
  · simp only [zmod2_zero_ne_one, ite_false]
    have hc3 : (pivotToSub u a b (pivotLab u a b t) 0).card = 3 := by
      have hne1 : (pivotToSub u a b (pivotLab u a b t) 0).card ≠ 1 := by
        intro h1; unfold pivotFromSub at hrt; simp only [h1, ite_true] at hrt
        exact zero_ne_one (congrArg Prod.snd hrt).symm
      omega
    have hcc : (Finset.range 4 \ pivotToSub u a b (pivotLab u a b t) 0).card = 1 := by
      have := Finset.card_sdiff_add_card_eq_card hsub; rw [Finset.card_range] at this; omega
    rcases Finset.card_eq_one.mp hcc with ⟨k, hk_eq⟩
    have hklt : k < 4 := Finset.mem_range.mp (Finset.mem_sdiff.mp (hk_eq ▸ Finset.mem_singleton_self k)).1
    have hTeq : pivotToSub u a b (pivotLab u a b t) 0 = (Finset.range 4).erase k := by
      ext x
      have hx : x ∈ Finset.range 4 \ pivotToSub u a b (pivotLab u a b t) 0 ↔ x = k := by rw [hk_eq, Finset.mem_singleton]
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hx ⊢
      exact ⟨fun hm => ⟨fun h => (hx.mpr h).2 hm, hsub hm⟩, fun ⟨hne, hr⟩ => by by_contra hna; exact hne (hx.mp ⟨hr, hna⟩)⟩
    rw [hTeq] at hrt ⊢
    have hfst := congrArg Prod.fst hrt
    have hkc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    have hkeq : 3 - k = t := by
      rcases hkc with rfl | rfl | rfl | rfl
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 3 (by omega) t ht hfst
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 2 (by omega) t ht hfst
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 1 (by omega) t ht hfst
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 0 (by omega) t ht hfst
    have : k = 3 - t := by omega
    rw [this]
  · simp only [ite_true]
    have hc1 : (pivotToSub u a b (pivotLab u a b t) 1).card = 1 := by
      by_contra hne1
      unfold pivotFromSub at hrt; simp only [hne1, ite_false] at hrt
      exact zero_ne_one (congrArg Prod.snd hrt)
    rcases Finset.card_eq_one.mp hc1 with ⟨k, hk_eq⟩
    have hklt : k < 4 := Finset.mem_range.mp (hsub (hk_eq ▸ Finset.mem_singleton_self k))
    rw [hk_eq] at hrt ⊢
    have hfst := congrArg Prod.fst hrt
    have hkc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    have hkeq : 3 - k = t := by
      rcases hkc with rfl | rfl | rfl | rfl
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 3 (by omega) t ht hfst
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 2 (by omega) t ht hfst
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 1 (by omega) t ht hfst
      · unfold pivotFromSub at hfst; simp at hfst; exact hPl_inj 0 (by omega) t ht hfst
    have : k = 3 - t := by omega
    rw [this]

lemma pivot_fromSub_roundtrip {n : Nat} {u a b : W n}
    (hnd : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (hu : u ∉ planeOf a b)
    (A : Finset Nat) (hA : A ⊆ Finset.range 4) (hodd : A.card % 2 = 1) :
    let pd := pivotFromSub u a b A
    pd.1 ∈ (planeOf a b).image (fun w => u + w) ∧ pivotToSub u a b pd.1 pd.2 = A := by
  have hle : A.card ≤ 4 := (Finset.card_le_card hA).trans (by simp)
  have hc : A.card = 1 ∨ A.card = 3 := by omega
  have hPl : ∀ t < 4, pivotLab u a b t ∈ (planeOf a b).image (fun w => u + w) := fun t ht => by
    unfold pivotLab; refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
    have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [planeOf]
  rcases hc with h1 | h3
  · rcases Finset.card_eq_one.mp h1 with ⟨k, rfl⟩
    have hk : k < 4 := Finset.mem_range.mp (hA (Finset.mem_singleton_self k))
    have hkc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkc with rfl | rfl | rfl | rfl
    · refine ⟨by simpa [pivotFromSub] using hPl 3 (by omega), ?_⟩
      have : pivotFromSub u a b {0} = (pivotLab u a b 3, 1) := by unfold pivotFromSub; simp
      rw [this, pivotToSub_lab hnd hu (by omega) 1]; simp
    · refine ⟨by simpa [pivotFromSub] using hPl 2 (by omega), ?_⟩
      have : pivotFromSub u a b {1} = (pivotLab u a b 2, 1) := by unfold pivotFromSub; simp
      rw [this, pivotToSub_lab hnd hu (by omega) 1]; simp
    · refine ⟨by simpa [pivotFromSub] using hPl 1 (by omega), ?_⟩
      have : pivotFromSub u a b {2} = (pivotLab u a b 1, 1) := by unfold pivotFromSub; simp
      rw [this, pivotToSub_lab hnd hu (by omega) 1]; simp
    · refine ⟨by simpa [pivotFromSub] using hPl 0 (by omega), ?_⟩
      have : pivotFromSub u a b {3} = (pivotLab u a b 0, 1) := by unfold pivotFromSub; simp
      rw [this, pivotToSub_lab hnd hu (by omega) 1]; simp
  · have hccomp : (Finset.range 4 \ A).card = 1 := by
      have := Finset.card_sdiff_add_card_eq_card hA; rw [Finset.card_range] at this; omega
    rcases Finset.card_eq_one.mp hccomp with ⟨k, hk_eq⟩
    have hk : k < 4 := Finset.mem_range.mp (Finset.mem_sdiff.mp (hk_eq ▸ Finset.mem_singleton_self k)).1
    have hAeq : A = (Finset.range 4).erase k := by
      ext x
      have hx_iff : x ∈ Finset.range 4 \ A ↔ x = k := by rw [hk_eq, Finset.mem_singleton]
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hx_iff ⊢
      exact ⟨fun hx => ⟨fun h => (hx_iff.mpr h).2 hx, hA hx⟩, fun ⟨hxk, hxr⟩ => by by_contra hna; exact hxk (hx_iff.mp ⟨hxr, hna⟩)⟩
    rw [hAeq]
    have hkc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkc with rfl | rfl | rfl | rfl
    · have hp : pivotFromSub u a b ((Finset.range 4).erase 0) = (pivotLab u a b 3, 0) := by unfold pivotFromSub; simp
      rw [hp]; exact ⟨hPl 3 (by omega), by rw [pivotToSub_lab hnd hu (by omega) 0]; simp⟩
    · have hp : pivotFromSub u a b ((Finset.range 4).erase 1) = (pivotLab u a b 2, 0) := by unfold pivotFromSub; simp
      rw [hp]; exact ⟨hPl 2 (by omega), by rw [pivotToSub_lab hnd hu (by omega) 0]; simp⟩
    · have hp : pivotFromSub u a b ((Finset.range 4).erase 2) = (pivotLab u a b 1, 0) := by unfold pivotFromSub; simp
      rw [hp]; exact ⟨hPl 1 (by omega), by rw [pivotToSub_lab hnd hu (by omega) 0]; simp⟩
    · have hp : pivotFromSub u a b ((Finset.range 4).erase 3) = (pivotLab u a b 0, 0) := by unfold pivotFromSub; simp
      rw [hp]; exact ⟨hPl 0 (by omega), by rw [pivotToSub_lab hnd hu (by omega) 0]; simp⟩

-- Main assembly

set_option maxHeartbeats 1600000 in
lemma main_979 (n e : Nat) (he : 0 < e) :
  let m := 4*e-1
  let F := ZMod 2
  let W := Fin n → F
  let I := Fin m
  ∀ a b : I → W, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let freq := fun i : I => ({a i, b i, a i+b i} : Finset W)
    let fs := (Finset.univ : Finset I).biUnion freq
    let odd := fs.filter (fun v => ((Finset.univ : Finset I).filter (fun i => v ∈ freq i)).card % 2 = 1)
    let S := insert (0 : W) odd
    let outside := fun (i : I) => if h : ∃ v ∈ odd, v ∉ freq i then Classical.choose h else (0 : W)
    let good := (Finset.univ : Finset ((I → W) × (I → F))).filter (fun p =>
      ∀ x : W, ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (p.1 i) x+p.2 i)).card ≤ e)
    let tally := fun (pivot : Option I) =>
      let nports := fun i : I => if pivot = some i then 4 else 3
      let label := fun (i : I) (j : Nat) =>
        if pivot = some i then outside i + (if j = 0 then 0 else if j = 1 then a i else if j = 2 then b i else a i+b i)
        else if j = 0 then a i else if j = 1 then b i else a i+b i
      let ports := (Finset.univ : Finset I).biUnion (fun i => (Finset.range (nports i)).image (fun j => (i,j)))
      let labels := ports.image (fun p => label p.1 p.2)
      let quota := fun v : W => (((ports.filter (fun p => label p.1 p.2 = v)).card) + (if pivot = none then 1 else 0)) / 2
      let V := (I × Nat) ⊕ (W × Nat)
      let localNodes := ports ∪ (Finset.univ : Finset I).image (fun i => (i,4))
      let slots := labels.biUnion (fun v => (Finset.range (quota v)).image (fun j => (v,j)))
      let verts : Finset V := localNodes.image Sum.inl ∪ slots.image Sum.inr
      let sameRow := fun (p q : I × Nat) => p.1 = q.1 ∧ p.2 ≠ q.2 ∧
        (p.2 = 4 ∨ q.2 = 4 ∨ p.2 / 2 = q.2 / 2)
      let attach := fun (p : I × Nat) (q : W × Nat) => p.2 < nports p.1 ∧ label p.1 p.2 = q.1
      let edge := fun (p q : V) => Sum.elim (fun x => Sum.elim (sameRow x) (attach x) q)
        (fun y => Sum.elim (fun x => attach x y) (fun _ => False) q) p
      let matchings := (Finset.univ : Finset (↥verts → ↥verts)).filter (fun f =>
        @decide (∀ x, f (f x) = x ∧ edge x.val (f x).val) (Classical.propDecidable _) = true)
      matchings.card / (∏ v ∈ labels, Nat.factorial (quota v))
    good.card = if 4 ≤ S.card ∧ (∀ v ∈ S, ∀ w ∈ S, v+w ∈ S) then
      S.card * tally none + (if S.card = 8 then ∑ i : I, if freq i ⊆ odd then tally (some i) else 0 else 0)
      else 0 := by
  intro m F_ W_ I a b hnd freq fs odd S outside good tally
  let oddLabels := (Finset.univ : Finset (W n)).filter (fun v =>
    ((Finset.univ : Finset I).filter (fun i =>
      v ∈ ({a i, b i, a i + b i} : Finset (W n)))).card % 2 = 1)
  have hodd_eq : odd = oddLabels := by
    ext v
    simp only [odd, oddLabels, fs, freq, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, and_iff_right_iff_imp]
    intro hmod
    have hpos : 0 < ((Finset.univ : Finset I).filter (fun i => v ∈ ({a i, b i, a i + b i} : Finset (W n)))).card := by omega
    rcases Finset.card_pos.mp hpos with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have h0_not_odd : (0 : W n) ∉ odd := by
    intro h0
    have hfs := (Finset.mem_filter.mp h0).1
    rcases Finset.mem_biUnion.mp hfs with ⟨i, _, hfi⟩
    rcases distinct_tri (hnd i) with ⟨ha0, hb0, hab0, _, _, _⟩
    simp only [freq, Finset.mem_insert, Finset.mem_singleton] at hfi
    rcases hfi with h | h | h <;> first | exact ha0 h.symm | exact hb0 h.symm | exact hab0 h.symm
  have hpart : ∀ p ∈ good,
      (∀ v ∈ S, ∀ w ∈ S, v + w ∈ S) ∧ 4 ≤ S.card ∧
      (((∀ i, p.1 i ∈ planeOf (a i) (b i)) ∧ (∀ i, rowCoeff (a i) (b i) (p.1 i) (p.2 i) 0 = 1) ∧
          ∃ z : W n, ∀ v : W n, totalCoeff a b p.1 p.2 e v = if v ∈ S then chi v z else 0) ∨
       (S.card = 8 ∧ (∀ v : W n, totalCoeff a b p.1 p.2 e v = 0) ∧
         ∃ j : I, p.1 j ∉ planeOf (a j) (b j) ∧
           (∀ i, i ≠ j → p.1 i ∈ planeOf (a i) (b i)) ∧
           (∀ i, i ≠ j → rowCoeff (a i) (b i) (p.1 i) (p.2 i) 0 = 1) ∧
           S = planeOf (a j) (b j) ∪ (planeOf (a j) (b j)).image (fun v => p.1 j + v))) := by
    intro p hp
    have h1 := part1_strong n e he a b p.1 p.2 hnd (Finset.mem_filter.mp hp).2
    have hSeq : S = insert (0 : W n) oddLabels := by dsimp only [S]; rw [hodd_eq]
    rcases h1 with ⟨h1a, h1b, h1c | h1d⟩
    · refine ⟨fun v hv w hw => hSeq ▸ h1a v (hSeq ▸ hv) w (hSeq ▸ hw), hSeq ▸ h1b, Or.inl ?_⟩
      rcases h1c with ⟨hp1, hp2, z, hz⟩
      refine ⟨hp1, hp2, z, fun v => ?_⟩
      rw [hz v]
      by_cases hv : v ∈ S
      · rw [if_pos hv, if_pos (hSeq ▸ hv)]
      · rw [if_neg hv, if_neg (fun h => hv (hSeq ▸ h))]
    · refine ⟨fun v hv w hw => hSeq ▸ h1a v (hSeq ▸ hv) w (hSeq ▸ hw), hSeq ▸ h1b, Or.inr ?_⟩
      rcases h1d with ⟨h8, hcz, j, hjn, hoth, hr0, hseqj⟩
      exact ⟨hSeq ▸ h8, hcz, j, hjn, hoth, hr0, hSeq.trans hseqj⟩
  by_cases hScond : 4 ≤ S.card ∧ (∀ v ∈ S, ∀ w ∈ S, v + w ∈ S)
  · rw [if_pos hScond]
    rcases hScond with ⟨hS4, hSadd⟩
    have h0S : (0 : W n) ∈ S := Finset.mem_insert_self 0 odd
    -- Define Type 0 and Type 1 subsets of good
    let goodNone := good.filter (fun p => ∀ i : I, p.1 i ∈ planeOf (a i) (b i))
    let goodSome (j : I) := good.filter (fun p => p.1 j ∉ planeOf (a j) (b j))
    -- Disjoint union decomposition of good
    have hgood_decomp : good.card = goodNone.card +
        if S.card = 8 then ∑ j : I, if freq j ⊆ odd then (goodSome j).card else 0 else 0 := by
      have hdisj0 : ∀ j : I, Disjoint goodNone (goodSome j) := fun j =>
        Finset.disjoint_filter.mpr (fun p _ h1 h2 => h2 (h1 j))
      have hdisj1 : ∀ j₁ j₂ : I, j₁ ≠ j₂ → Disjoint (goodSome j₁) (goodSome j₂) := by
        intro j₁ j₂ hne
        refine Finset.disjoint_filter.mpr (fun p hp h1 h2 => ?_)
        rcases (hpart p hp).2.2 with ⟨hall, _, _⟩ | ⟨_, _, j, _, hoth, _, _⟩
        · exact h1 (hall j₁)
        · by_cases hjj1 : j₁ = j
          · subst hjj1; exact h2 (hoth j₂ hne.symm)
          · exact h1 (hoth j₁ hjj1)
      by_cases hS8 : S.card = 8
      · rw [if_pos hS8]
        let Jgood := (Finset.univ : Finset I).filter (fun j => freq j ⊆ odd)
        have hunion : good = goodNone ∪ Jgood.biUnion goodSome := by
          ext p
          simp only [Finset.mem_union, Finset.mem_biUnion, Jgood, goodNone, goodSome,
            Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hp
            rcases (hpart p hp).2.2 with ⟨hall, _, _⟩ | ⟨_, _, j, hjnot, _, _, hSeq⟩
            · exact Or.inl ⟨hp, hall⟩
            · right
              refine ⟨j, ?_, hp, hjnot⟩
              intro v hv
              have hvS : v ∈ S := by
                rw [hSeq, Finset.mem_union]; left
                simp only [freq, planeOf, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
                exact Or.inr hv
              have hv0 : v ≠ 0 := by
                rcases distinct_tri (hnd j) with ⟨ha0, hb0, hab0, _, _, _⟩
                simp only [freq, Finset.mem_insert, Finset.mem_singleton] at hv
                rcases hv with rfl | rfl | rfl <;> assumption
              exact (Finset.mem_insert.mp hvS).resolve_left hv0
          · rintro (⟨hp, _⟩ | ⟨j, _, hp, _⟩) <;> exact hp
        have hdisjU : Disjoint goodNone (Jgood.biUnion goodSome) :=
          Finset.disjoint_left.mpr (fun p hp1 hp2 => by
            rcases Finset.mem_biUnion.mp hp2 with ⟨j, _, hpj⟩
            exact Finset.disjoint_left.mp (hdisj0 j) hp1 hpj)
        have hpair : Set.PairwiseDisjoint (Jgood : Set I) goodSome :=
          fun j₁ _ j₂ _ hne => hdisj1 j₁ j₂ hne
        rw [hunion, Finset.card_union_of_disjoint hdisjU, Finset.card_biUnion hpair]
        congr 1
        rw [← Finset.sum_filter]
      · rw [if_neg hS8, add_zero]
        congr 1
        ext p
        simp only [goodNone, Finset.mem_filter, iff_self_and]
        intro hp
        rcases (hpart p hp).2.2 with ⟨hall, _, _⟩ | ⟨h8, _⟩
        · exact hall
        · exact absurd h8 hS8
    -- Helper: tally equals validA.card
    have htally_eq : ∀ pivot : Option I,
        let nports := fun i : I => if pivot = some i then 4 else 3
        let label := fun (i : I) (j : Nat) =>
          if pivot = some i then outside i + (if j = 0 then 0 else if j = 1 then a i else if j = 2 then b i else a i+b i)
          else if j = 0 then a i else if j = 1 then b i else a i+b i
        let ports := (Finset.univ : Finset I).biUnion (fun i => (Finset.range (nports i)).image (fun j => (i,j)))
        let labels := ports.image (fun p => label p.1 p.2)
        let quota := fun v : W n => (((ports.filter (fun p => label p.1 p.2 = v)).card) + (if pivot = none then 1 else 0)) / 2
        let validA := ports.powerset.filter (fun (A : Finset (I × Nat)) =>
          (∀ i : I, (A.filter (fun p => p.1 = i)).card % 2 = if nports i = 4 then 1 else 0) ∧
          (∀ v ∈ labels, (A.filter (fun p => label p.1 p.2 = v)).card = quota v))
        tally pivot = validA.card := by
      intro pivot nports label ports labels quota validA
      have hnp : ∀ i : I, nports i = 3 ∨ nports i = 4 := fun i => by
        dsimp only [nports]; split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
      have hmc := matchings_card_eq nports hnp label quota
      dsimp only at hmc
      have hpos : 0 < ∏ v ∈ labels, Nat.factorial (quota v) :=
        Finset.prod_pos (fun v _ => Nat.factorial_pos _)
      dsimp only [tally]
      rw [hmc]
      exact Nat.mul_div_cancel _ hpos
    -- Step 1: goodNone.card = S.card * tally none
    have hnone_card : goodNone.card = S.card * tally none := by
      let goodNoneZero := goodNone.filter (fun p => ∀ v ∈ S, totalCoeff a b p.1 p.2 e v = 1)
      let Chars := (Finset.univ : Finset (W n)).image (fun z : W n => fun v : ↥S => chi v.val z)
      have hgoodNone_shift : goodNone.card = Chars.card * goodNoneZero.card := by
        have hfib : ∀ ψ ∈ Chars, (goodNone.filter
            (fun p => (fun v : ↥S => totalCoeff a b p.1 p.2 e v.val) = ψ)).card = goodNoneZero.card := by
          intro ψ hψ
          rcases Finset.mem_image.mp hψ with ⟨z, _, rfl⟩
          refine Finset.card_bij (fun p _ => shiftPred a b z p) ?_ ?_ ?_
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hpN, hpc⟩
            rcases Finset.mem_filter.mp hpN with ⟨hpG, hpPl⟩
            have hpG' : shiftPred a b z p ∈ good := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
              have heq : (Finset.univ : Finset I).filter (fun i =>
                  dotProduct (a i) x * dotProduct (b i) x ≠
                    dotProduct ((shiftPred a b z p).1 i) x + (shiftPred a b z p).2 i) =
                  (Finset.univ : Finset I).filter (fun i =>
                    dotProduct (a i) (x + z) * dotProduct (b i) (x + z) ≠
                      dotProduct (p.1 i) (x + z) + p.2 i) := by
                ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact shiftPred_err_iff a b z p x i
              rw [heq]; exact (Finset.mem_filter.mp hpG).2 (x + z)
            have hpN' : shiftPred a b z p ∈ goodNone :=
              Finset.mem_filter.mpr ⟨hpG', fun i => shiftPred_in_plane a b z p i (hpPl i)⟩
            refine Finset.mem_filter.mpr ⟨hpN', fun v hv => ?_⟩
            rw [shiftPred_totalCoeff, congrFun hpc ⟨v, hv⟩, chi_mul_self]
          · intro p₁ _ p₂ _ h
            have := congrArg (shiftPred a b z) h
            rwa [shiftPred_invol, shiftPred_invol] at this
          · intro q hq
            rcases Finset.mem_filter.mp hq with ⟨hqN, hqc⟩
            rcases Finset.mem_filter.mp hqN with ⟨hqG, hqPl⟩
            have hqG' : shiftPred a b z q ∈ good := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
              have heq : (Finset.univ : Finset I).filter (fun i =>
                  dotProduct (a i) x * dotProduct (b i) x ≠
                    dotProduct ((shiftPred a b z q).1 i) x + (shiftPred a b z q).2 i) =
                  (Finset.univ : Finset I).filter (fun i =>
                    dotProduct (a i) (x + z) * dotProduct (b i) (x + z) ≠
                      dotProduct (q.1 i) (x + z) + q.2 i) := by
                ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact shiftPred_err_iff a b z q x i
              rw [heq]; exact (Finset.mem_filter.mp hqG).2 (x + z)
            have hqN' : shiftPred a b z q ∈ goodNone :=
              Finset.mem_filter.mpr ⟨hqG', fun i => shiftPred_in_plane a b z q i (hqPl i)⟩
            refine ⟨shiftPred a b z q, Finset.mem_filter.mpr ⟨hqN', ?_⟩, shiftPred_invol a b z q⟩
            funext ⟨v, hv⟩
            rw [shiftPred_totalCoeff, hqc v hv, mul_one]
        have hmaps : ∀ p ∈ goodNone, (fun v : ↥S => totalCoeff a b p.1 p.2 e v.val) ∈ Chars := by
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpG, hpPl⟩
          rcases (hpart p hpG).2.2 with ⟨_, _, z, hz⟩ | ⟨_, _, j, hjnot, _⟩
          · refine Finset.mem_image.mpr ⟨z, Finset.mem_univ z, ?_⟩
            funext ⟨v, hv⟩; rw [hz v, if_pos hv]
          · exact absurd (hpPl j) hjnot
        have hsum := Finset.card_eq_sum_card_fiberwise (s := goodNone) (t := Chars) hmaps
        rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
        exact hsum
      rw [hgoodNone_shift, chars_card_eq S h0S hSadd, htally_eq none]
      congr 1
      simp only [reduceCtorEq, ite_false, ite_true]
      -- Bijection between goodNoneZero and validA(none)
      let label0 := fun (i : I) (j : Nat) => if j = 0 then a i else if j = 1 then b i else a i + b i
      let ports0 := (Finset.univ : Finset I).biUnion (fun i => (Finset.range 3).image (fun j => (i, j)))
      let labels0 := ports0.image (fun p => label0 p.1 p.2)
      let quota0 := fun v : W n => (((ports0.filter (fun p => label0 p.1 p.2 = v)).card) + 1) / 2
      let validA0 := ports0.powerset.filter (fun (A : Finset (I × Nat)) =>
        (∀ i : I, (A.filter (fun p => p.1 = i)).card % 2 = 0) ∧
        (∀ v ∈ labels0, (A.filter (fun p => label0 p.1 p.2 = v)).card = quota0 v))
      change goodNoneZero.card = validA0.card
      have hmem_p0 : ∀ p : I × Nat, p ∈ ports0 ↔ p.2 < 3 := by
        intro ⟨i, j⟩
        simp only [ports0, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
        exact ⟨fun ⟨_, _, h, rfl, rfl⟩ => h, fun h => ⟨i, j, h, rfl, rfl⟩⟩
      have hdeg0 : ∀ v : W n, (ports0.filter (fun p => label0 p.1 p.2 = v)).card =
          ((Finset.univ : Finset I).filter (fun i => v ∈ freq i)).card := by
        intro v
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro ⟨i, j⟩ hp
          rcases Finset.mem_filter.mp hp with ⟨hp0, hlab⟩
          have hj : j < 3 := (hmem_p0 (i, j)).mp hp0
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
          have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases this with rfl | rfl | rfl <;> simp [label0, freq] at hlab ⊢ <;> simp [hlab.symm]
        · intro ⟨i₁, j₁⟩ hp₁ ⟨i₂, j₂⟩ hp₂ heq
          dsimp only at heq; subst heq
          rcases Finset.mem_filter.mp hp₁ with ⟨h1, hl1⟩
          rcases Finset.mem_filter.mp hp₂ with ⟨h2, hl2⟩
          have hj1 := (hmem_p0 (i₁, j₁)).mp h1
          have hj2 := (hmem_p0 (i₁, j₂)).mp h2
          rcases distinct_tri (hnd i₁) with ⟨ha0, hb0, _, hab, haba, habb⟩
          have hll := hl1.trans hl2.symm
          have : j₁ = 0 ∨ j₁ = 1 ∨ j₁ = 2 := by omega
          have : j₂ = 0 ∨ j₂ = 1 ∨ j₂ = 2 := by omega
          rcases ‹j₁ = 0 ∨ _› with rfl | rfl | rfl <;> rcases ‹j₂ = 0 ∨ _› with rfl | rfl | rfl <;>
            simp [label0] at hll <;> (first | rfl | exact absurd hll hab | exact absurd hll hab.symm | exact absurd hll ha0 | exact absurd hll ha0.symm | exact absurd hll hb0 | exact absurd hll hb0.symm | exact absurd hll haba | exact absurd hll haba.symm | exact absurd hll habb | exact absurd hll habb.symm)
        · intro i hi
          have hfi := (Finset.mem_filter.mp hi).2
          simp only [freq, Finset.mem_insert, Finset.mem_singleton] at hfi
          rcases hfi with rfl | rfl | rfl
          · exact ⟨(i, 0), Finset.mem_filter.mpr ⟨(hmem_p0 _).mpr (by omega), by simp [label0]⟩, rfl⟩
          · exact ⟨(i, 1), Finset.mem_filter.mpr ⟨(hmem_p0 _).mpr (by omega), by simp [label0]⟩, rfl⟩
          · exact ⟨(i, 2), Finset.mem_filter.mpr ⟨(hmem_p0 _).mpr (by omega), by simp [label0]⟩, rfl⟩
      have hlab0_eq : labels0 = fs := by
        ext v
        simp only [labels0, fs, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨i, j⟩, hp0, rfl⟩
          have hj := (hmem_p0 (i, j)).mp hp0
          have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases this with rfl | rfl | rfl <;> exact ⟨i, by simp [label0, freq]⟩
        · rintro ⟨i, hfi⟩
          simp only [freq, Finset.mem_insert, Finset.mem_singleton] at hfi
          rcases hfi with rfl | rfl | rfl
          · exact ⟨(i, 0), (hmem_p0 _).mpr (by omega), by simp [label0]⟩
          · exact ⟨(i, 1), (hmem_p0 _).mpr (by omega), by simp [label0]⟩
          · exact ⟨(i, 2), (hmem_p0 _).mpr (by omega), by simp [label0]⟩
      have hsum_row_eq : ∀ (P : I → W n) (d : I → F) (A : Finset (I × Nat)),
          A ⊆ ports0 →
          (∀ i, (P i = 0 ∧ d i = 0) ∨ (P i = a i ∧ d i = 0) ∨ (P i = b i ∧ d i = 0) ∨ (P i = a i + b i ∧ d i = 1)) →
          (∀ i, (A.filter (fun p => p.1 = i)).image Prod.snd = nonpivotToSub (a i) (b i) (P i) (d i)) →
          ∀ v : W n, v ≠ 0 →
            (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) =
              ((ports0.filter (fun p => label0 p.1 p.2 = v)).card : Int) -
              2 * ((A.filter (fun p => label0 p.1 p.2 = v)).card : Int) := by
        intro P d A hAsub hPd hArow v hv0
        have hterm : ∀ i : I, rowCoeff (a i) (b i) (P i) (d i) v =
            ∑ j ∈ Finset.range 3, if label0 i j = v then (if (i, j) ∈ A then (-1 : Int) else 1) else 0 := by
          intro i
          have hrc := nonpivot_rowCoeff_cases (hnd i) (hPd i)
          by_cases hvf : v ∈ triOf (a i) (b i)
          · have hex : ∃ j0 < 3, label0 i j0 = v := by
              simp only [triOf, Finset.mem_insert, Finset.mem_singleton] at hvf
              rcases hvf with rfl | rfl | rfl
              · exact ⟨0, by omega, by simp [label0]⟩
              · exact ⟨1, by omega, by simp [label0]⟩
              · exact ⟨2, by omega, by simp [label0]⟩
            rcases hex with ⟨j0, hj0, hlab0⟩
            rw [Finset.sum_eq_single j0]
            · rw [if_pos hlab0, ← hlab0, hrc.2.2.2.1 j0 hj0]
              have hmem : (i, j0) ∈ A ↔ j0 ∈ nonpivotToSub (a i) (b i) (P i) (d i) := by
                rw [← hArow i, Finset.mem_image]
                constructor
                · rintro h; exact ⟨(i, j0), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
                · rintro ⟨⟨i', j'⟩, hmem, hjeq⟩
                  have hi' := (Finset.mem_filter.mp hmem).2
                  dsimp only at hjeq; subst hi'; subst hjeq; exact (Finset.mem_filter.mp hmem).1
              simp only [hmem]
            · intro j hj hne
              have hjlt := Finset.mem_range.mp hj
              rw [if_neg]
              intro heq
              have hll := heq.trans hlab0.symm
              rcases distinct_tri (hnd i) with ⟨ha0, hb0, _, hab, haba, habb⟩
              have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
              have : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by omega
              rcases ‹j = 0 ∨ _› with rfl | rfl | rfl <;> rcases ‹j0 = 0 ∨ _› with rfl | rfl | rfl <;>
                simp [label0] at hll <;> (first | exact hne rfl | exact absurd hll hab | exact absurd hll hab.symm | exact absurd hll ha0 | exact absurd hll ha0.symm | exact absurd hll hb0 | exact absurd hll hb0.symm | exact absurd hll haba | exact absurd hll haba.symm | exact absurd hll habb | exact absurd hll habb.symm)
            · intro h; exact absurd (Finset.mem_range.mpr hj0) h
          · rw [hrc.2.2.1 v hv0 hvf]
            symm
            refine Finset.sum_eq_zero (fun j hj => ?_)
            have hjlt := Finset.mem_range.mp hj
            rw [if_neg]
            intro heq
            apply hvf
            have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
            rcases this with rfl | rfl | rfl <;> simp [label0] at heq <;> simp [triOf, heq.symm]
        simp_rw [hterm]
        have hbi : (∑ i : I, ∑ j ∈ Finset.range 3,
              if label0 i j = v then (if (i, j) ∈ A then (-1 : Int) else 1) else 0) =
            ∑ p ∈ ports0, if label0 p.1 p.2 = v then (if p ∈ A then (-1 : Int) else 1) else 0 := by
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_image (fun j₁ _ j₂ _ h => (Prod.mk.inj h).2)]
          · intro i₁ _ i₂ _ hne
            refine Finset.disjoint_left.mpr (fun p h1 h2 => ?_)
            rcases Finset.mem_image.mp h1 with ⟨j₁, _, rfl⟩
            rcases Finset.mem_image.mp h2 with ⟨j₂, _, h⟩
            exact hne (Prod.mk.inj h).1.symm
        rw [hbi]
        have hstep : ∀ p ∈ ports0,
            (if label0 p.1 p.2 = v then (if p ∈ A then (-1 : Int) else 1) else 0) =
            (if label0 p.1 p.2 = v then (1 : Int) else 0) -
            2 * (if label0 p.1 p.2 = v ∧ p ∈ A then (1 : Int) else 0) := by
          intro p _; by_cases h1 : label0 p.1 p.2 = v <;> by_cases h2 : p ∈ A <;> simp [h1, h2]
        rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hs1 : (∑ p ∈ ports0, if label0 p.1 p.2 = v then (1 : Int) else 0) =
            ((ports0.filter (fun p => label0 p.1 p.2 = v)).card : Int) := by
          rw [Finset.sum_boole]
        have hs2 : (∑ p ∈ ports0, if label0 p.1 p.2 = v ∧ p ∈ A then (1 : Int) else 0) =
            ((A.filter (fun p => label0 p.1 p.2 = v)).card : Int) := by
          rw [Finset.sum_boole]
          congr 2; ext p
          simp only [Finset.mem_filter]
          exact ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨hAsub h2, h1, h2⟩⟩
        rw [hs1, hs2]
      refine Finset.card_bij
        (fun p _ => (Finset.univ : Finset I).biUnion (fun i =>
          (nonpivotToSub (a i) (b i) (p.1 i) (p.2 i)).image (fun j => (i, j)))) ?_ ?_ ?_
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpN, hp1⟩
        rcases Finset.mem_filter.mp hpN with ⟨hpG, hpPl⟩
        rcases (hpart p hpG).2.2 with ⟨_, hrow0, z, hz⟩ | ⟨_, _, j, hjnot, _⟩
        · have hPd : ∀ i : I, (p.1 i = 0 ∧ p.2 i = 0) ∨ (p.1 i = a i ∧ p.2 i = 0) ∨
              (p.1 i = b i ∧ p.2 i = 0) ∨ (p.1 i = a i + b i ∧ p.2 i = 1) :=
            fun i => nonpivot_row_values (p.2 i) (hnd i) (hpPl i) (hrow0 i)
          let A := (Finset.univ : Finset I).biUnion (fun i =>
            (nonpivotToSub (a i) (b i) (p.1 i) (p.2 i)).image (fun j => (i, j)))
          have hAsub : A ⊆ ports0 := by
            intro ⟨i, j⟩ hmem
            rcases Finset.mem_biUnion.mp hmem with ⟨i', _, hj'⟩
            rcases Finset.mem_image.mp hj' with ⟨j', hsub, heq⟩
            rcases Prod.mk.inj heq.symm with ⟨rfl, rfl⟩
            exact (hmem_p0 (i, j)).mpr (Finset.mem_range.mp ((nonpivot_rowCoeff_cases (hnd i) (hPd i)).2.2.2.2.1 hsub))
          have hArow : ∀ i : I, (A.filter (fun q => q.1 = i)).image Prod.snd =
              nonpivotToSub (a i) (b i) (p.1 i) (p.2 i) := by
            intro i; ext j
            simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨⟨i', j'⟩, ⟨⟨i'', j'', hj'', heq⟩, rfl⟩, rfl⟩
              rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact hj''
            · intro hj; exact ⟨(i, j), ⟨⟨i, j, hj, rfl⟩, rfl⟩, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAsub, ?_, ?_⟩
          · intro i
            have hci : ((A.filter (fun q => q.1 = i)).image Prod.snd).card = (A.filter (fun q => q.1 = i)).card := by
              refine Finset.card_image_of_injOn (fun x hx y hy heq =>
                Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq)
            rw [← hci, hArow i]
            exact (nonpivot_rowCoeff_cases (hnd i) (hPd i)).2.2.2.2.2.1
          · intro v hv
            have hv0 : v ≠ 0 := by
              rw [hlab0_eq] at hv
              rcases Finset.mem_biUnion.mp hv with ⟨i, _, hfi⟩
              rcases distinct_tri (hnd i) with ⟨ha0, hb0, hab0, _, _, _⟩
              simp only [freq, Finset.mem_insert, Finset.mem_singleton] at hfi
              rcases hfi with rfl | rfl | rfl <;> assumption
            have htc : totalCoeff a b p.1 p.2 e v = if v ∈ odd then 1 else 0 := by
              by_cases hvo : v ∈ odd
              · rw [if_pos hvo]; exact hp1 v (Finset.mem_insert_of_mem hvo)
              · rw [if_neg hvo, hz v, if_neg]
                intro hvS; exact hvo ((Finset.mem_insert.mp hvS).resolve_left hv0)
            have hsr := hsum_row_eq p.1 p.2 A hAsub hPd hArow v hv0
            have htc2 : totalCoeff a b p.1 p.2 e v = - ∑ i : I, rowCoeff (a i) (b i) (p.1 i) (p.2 i) v := by
              dsimp only [totalCoeff]; simp [hv0]; rfl
            have hdeg := hdeg0 v
            have hodd_iff : v ∈ odd ↔ (ports0.filter (fun q => label0 q.1 q.2 = v)).card % 2 = 1 := by
              rw [hdeg]; rw [hlab0_eq] at hv; simp [odd, hv]
            change (A.filter (fun p => label0 p.1 p.2 = v)).card = quota0 v
            dsimp only [quota0]
            by_cases hvo : v ∈ odd
            · have hm1 := hodd_iff.mp hvo
              rw [if_pos hvo] at htc; omega
            · have hm0 : (ports0.filter (fun q => label0 q.1 q.2 = v)).card % 2 = 0 := by
                have := hodd_iff.not.mp hvo; omega
              rw [if_neg hvo] at htc; omega
        · exact absurd (hpPl j) hjnot
      · intro p₁ hp₁ p₂ hp₂ heq
        have hp₁G := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).1
        have hp₁Pl := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).2
        have hp₂G := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).1
        have hp₂Pl := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).2
        have hrow1 : ∀ i, rowCoeff (a i) (b i) (p₁.1 i) (p₁.2 i) 0 = 1 := by
          rcases (hpart p₁ hp₁G).2.2 with ⟨_, hr, _⟩ | ⟨_, _, j, hjn, _⟩
          · exact hr
          · exact absurd (hp₁Pl j) hjn
        have hrow2 : ∀ i, rowCoeff (a i) (b i) (p₂.1 i) (p₂.2 i) 0 = 1 := by
          rcases (hpart p₂ hp₂G).2.2 with ⟨_, hr, _⟩ | ⟨_, _, j, hjn, _⟩
          · exact hr
          · exact absurd (hp₂Pl j) hjn
        have hsub_eq : ∀ i : I, nonpivotToSub (a i) (b i) (p₁.1 i) (p₁.2 i) =
            nonpivotToSub (a i) (b i) (p₂.1 i) (p₂.2 i) := by
          intro i; ext j
          have hmem : (i, j) ∈ (Finset.univ : Finset I).biUnion (fun i =>
              (nonpivotToSub (a i) (b i) (p₁.1 i) (p₁.2 i)).image (fun j => (i, j))) ↔
            (i, j) ∈ (Finset.univ : Finset I).biUnion (fun i =>
              (nonpivotToSub (a i) (b i) (p₂.1 i) (p₂.2 i)).image (fun j => (i, j))) := by rw [heq]
          simpa using hmem
        have hpair : ∀ i : I, (p₁.1 i, p₁.2 i) = (p₂.1 i, p₂.2 i) := by
          intro i
          have hc1 := (nonpivot_rowCoeff_cases (hnd i) (nonpivot_row_values (p₁.2 i) (hnd i) (hp₁Pl i) (hrow1 i))).2.2.2.2.2.2
          have hc2 := (nonpivot_rowCoeff_cases (hnd i) (nonpivot_row_values (p₂.2 i) (hnd i) (hp₂Pl i) (hrow2 i))).2.2.2.2.2.2
          rw [← hc1, hsub_eq i, hc2]
        exact Prod.ext (funext (fun i => congrArg Prod.fst (hpair i))) (funext (fun i => congrArg Prod.snd (hpair i)))
      · intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hApow, hAeven, hAq⟩
        have hAsub : A ⊆ ports0 := Finset.mem_powerset.mp hApow
        let rowA (i : I) : Finset Nat := (A.filter (fun p => p.1 = i)).image Prod.snd
        have hrowA_sub : ∀ i, rowA i ⊆ Finset.range 3 := by
          intro i j hj
          rcases Finset.mem_image.mp hj with ⟨⟨i', j'⟩, hf, rfl⟩
          have hi' := (Finset.mem_filter.mp hf).2
          have hp := (Finset.mem_filter.mp hf).1
          exact Finset.mem_range.mpr ((hmem_p0 (i', j')).mp (hAsub hp))
        have hrowA_even : ∀ i, (rowA i).card % 2 = 0 := by
          intro i
          have hci : (rowA i).card = (A.filter (fun p => p.1 = i)).card :=
            Finset.card_image_of_injOn (fun x hx y hy heq =>
              Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq)
          rw [hci]; exact hAeven i
        let P : I → W n := fun i => (nonpivotFromSub (a i) (b i) (rowA i)).1
        let d : I → F := fun i => (nonpivotFromSub (a i) (b i) (rowA i)).2
        have hrt : ∀ i, ((P i = 0 ∧ d i = 0) ∨ (P i = a i ∧ d i = 0) ∨
            (P i = b i ∧ d i = 0) ∨ (P i = a i + b i ∧ d i = 1)) ∧
            nonpivotToSub (a i) (b i) (P i) (d i) = rowA i :=
          fun i => nonpivot_fromSub_roundtrip (hnd i) (rowA i) (hrowA_sub i) (hrowA_even i)
        have hArow : ∀ i, (A.filter (fun p => p.1 = i)).image Prod.snd =
            nonpivotToSub (a i) (b i) (P i) (d i) := fun i => (hrt i).2.symm
        have htc : ∀ v : W n, totalCoeff a b P d e v = if v ∈ S then 1 else 0 := by
          intro v
          by_cases hv0 : v = 0
          · subst hv0
            rw [if_pos h0S]
            have hr0 : ∀ i : I, rowCoeff (a i) (b i) (P i) (d i) 0 = 1 :=
              fun i => (nonpivot_rowCoeff_cases (hnd i) (hrt i).1).2.1
            simp only [totalCoeff, ite_true]
            rw [Finset.sum_congr rfl (fun i _ => hr0 i)]
            simp only [I, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
            omega
          · have htc2 : totalCoeff a b P d e v = - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v := by
              dsimp only [totalCoeff]; simp [hv0]; rfl
            have hsr := hsum_row_eq P d A hAsub (fun i => (hrt i).1) hArow v hv0
            by_cases hvl : v ∈ labels0
            · have hq := hAq v hvl
              have hdeg := hdeg0 v
              have hfs_v : v ∈ fs := hlab0_eq ▸ hvl
              have hvS_iff : v ∈ S ↔ (ports0.filter (fun q => label0 q.1 q.2 = v)).card % 2 = 1 := by
                rw [hdeg]; simp [S, odd, hv0, hfs_v]
              dsimp only [quota0] at hq
              by_cases hvS : v ∈ S
              · have hm1 := hvS_iff.mp hvS; rw [if_pos hvS]; omega
              · have hm0 : (ports0.filter (fun q => label0 q.1 q.2 = v)).card % 2 = 0 := by
                  have := hvS_iff.not.mp hvS; omega
                rw [if_neg hvS]; omega
            · have hvnotS : v ∉ S := by
                intro hvS
                have hvo : v ∈ odd := (Finset.mem_insert.mp hvS).resolve_left hv0
                exact hvl (hlab0_eq.symm ▸ (Finset.mem_filter.mp hvo).1)
              have hp0_empty : ports0.filter (fun q => label0 q.1 q.2 = v) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro q hq heq; exact hvl (Finset.mem_image.mpr ⟨q, hq, heq⟩)
              have hA_empty : A.filter (fun q => label0 q.1 q.2 = v) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro q hq heq; exact hvl (Finset.mem_image.mpr ⟨q, hAsub hq, heq⟩)
              rw [if_neg hvnotS, htc2, hsr, hp0_empty, hA_empty]; simp
        have hpG : (P, d) ∈ good := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
          have hf := errs_fourier a b P d e x
          have hsumS : (∑ v : W n, totalCoeff a b P d e v * chi v x) = ∑ v ∈ S, chi v x := by
            have h1 : ∀ v : W n, totalCoeff a b P d e v * chi v x = if v ∈ S then chi v x else 0 := by
              intro v; rw [htc v]; split_ifs <;> simp
            simp_rw [h1]; rw [Finset.sum_ite_mem, Finset.univ_inter]
          rw [hsumS, sum_chi_subgroup S h0S hSadd x] at hf
          set errC := ((Finset.univ : Finset (Fin m)).filter (fun i =>
            dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card
          change (4 * e : Int) - 4 * (errC : Int) = _ at hf
          change errC ≤ e
          split_ifs at hf <;> omega
        have hpPl : ∀ i : I, P i ∈ planeOf (a i) (b i) :=
          fun i => (nonpivot_rowCoeff_cases (hnd i) (hrt i).1).1
        refine ⟨(P, d), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpG, hpPl⟩,
          fun v hv => by rw [htc v, if_pos hv]⟩, ?_⟩
        ext ⟨i, j⟩
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨i', j', hj', hi', hj''⟩
          subst hi'; subst hj''
          rw [(hrt i').2] at hj'
          rcases Finset.mem_image.mp hj' with ⟨⟨i'', j''⟩, hf, hjeq⟩
          have hi'' := (Finset.mem_filter.mp hf).2
          dsimp only at hjeq; subst hi''; subst hjeq
          exact (Finset.mem_filter.mp hf).1
        · intro hmem
          refine ⟨i, j, ?_, rfl, rfl⟩
          rw [(hrt i).2]
          exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
    -- Step 2: when S.card = 8 and freq j ⊆ odd, (goodSome j).card = tally (some j)
    have hsome_card : S.card = 8 → ∀ j : I, freq j ⊆ odd → (goodSome j).card = tally (some j) := by
      intro hS8 j hfj
      rw [htally_eq (some j)]
      have hodd_card : odd.card = 7 := by
        have := Finset.card_insert_of_notMem h0_not_odd
        change S.card = odd.card + 1 at this
        omega
      have hfj_card : (freq j).card = 3 := by
        rcases distinct_tri (hnd j) with ⟨_, _, _, hab, haba, habb⟩
        unfold freq
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [habb]
        · simp [hab, haba]
      have hex_out : ∃ v ∈ odd, v ∉ freq j := by
        have hsdiff : 0 < (odd \ freq j).card := by
          have := Finset.card_sdiff_add_card_eq_card hfj; omega
        rcases Finset.card_pos.mp hsdiff with ⟨v, hv⟩
        exact ⟨v, (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
      set u := outside j
      have hu_odd : u ∈ odd := by
        have : u = Classical.choose hex_out := dif_pos hex_out
        rw [this]; exact (Classical.choose_spec hex_out).1
      have hu_not_fj : u ∉ freq j := by
        have : u = Classical.choose hex_out := dif_pos hex_out
        rw [this]; exact (Classical.choose_spec hex_out).2
      have hu_ne0 : u ≠ 0 := fun h => h0_not_odd (h ▸ hu_odd)
      have hu_not_pl : u ∉ planeOf (a j) (b j) := by
        intro hmem
        simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hu0 | hmem
        · exact hu_ne0 hu0
        · exact hu_not_fj (by simpa [freq] using hmem)
      let coset := (planeOf (a j) (b j)).image (fun w => u + w)
      have hdisj_jc : Disjoint (planeOf (a j) (b j)) coset := disjoint_planeOf_image hu_not_pl
      have hS_decomp : S = planeOf (a j) (b j) ∪ coset := by
        have hsub : planeOf (a j) (b j) ∪ coset ⊆ S := by
          intro v hv
          rcases Finset.mem_union.mp hv with hv1 | hv2
          · simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hv1
            rcases hv1 with rfl | h1
            · exact h0S
            · exact Finset.mem_insert_of_mem (hfj (by simpa [freq] using h1))
          · rcases Finset.mem_image.mp hv2 with ⟨w, hw, rfl⟩
            have hwS : w ∈ S := by
              simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | h1
              · exact h0S
              · exact Finset.mem_insert_of_mem (hfj (by simpa [freq] using h1))
            exact hSadd u (Finset.mem_insert_of_mem hu_odd) w hwS
        have hcard_u : (planeOf (a j) (b j) ∪ coset).card = 8 := by
          rw [Finset.card_union_of_disjoint hdisj_jc]
          have hc1 : (planeOf (a j) (b j)).card = 4 := planeOf_card (hnd j)
          have hc2 : coset.card = 4 := by
            rw [Finset.card_image_of_injective _ (fun x y h => add_left_cancel h), hc1]
          omega
        exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      let nportsj := fun i : I => if some j = some i then 4 else 3
      let labelj := fun (i : I) (k : Nat) =>
        if some j = some i then outside i + (if k = 0 then 0 else if k = 1 then a i else if k = 2 then b i else a i + b i)
        else if k = 0 then a i else if k = 1 then b i else a i + b i
      let portsj := (Finset.univ : Finset I).biUnion (fun i => (Finset.range (nportsj i)).image (fun k => (i, k)))
      let labelsj := portsj.image (fun p => labelj p.1 p.2)
      let quotaj := fun v : W n => (((portsj.filter (fun p => labelj p.1 p.2 = v)).card) + 0) / 2
      let validAj := portsj.powerset.filter (fun (A : Finset (I × Nat)) =>
        (∀ i : I, (A.filter (fun p => p.1 = i)).card % 2 = if nportsj i = 4 then 1 else 0) ∧
        (∀ v ∈ labelsj, (A.filter (fun p => labelj p.1 p.2 = v)).card = quotaj v))
      simp only [reduceCtorEq, ite_false]
      change (goodSome j).card = validAj.card
      have hmem_pj : ∀ p : I × Nat, p ∈ portsj ↔ p.2 < nportsj p.1 := by
        intro ⟨i, k⟩
        simp only [portsj, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
        exact ⟨fun ⟨_, _, h, rfl, rfl⟩ => h, fun h => ⟨i, k, h, rfl, rfl⟩⟩
      have hlabj_j : ∀ k : Nat, labelj j k = pivotLab u (a j) (b j) k := fun k => by
        simp [labelj, pivotLab, u]
      have hlabj_ne : ∀ i : I, i ≠ j → ∀ k : Nat,
          labelj i k = if k = 0 then a i else if k = 1 then b i else a i + b i := fun i hij k => by
        simp [labelj, hij.symm]
      have hdegj_even : ∀ v : W n, (portsj.filter (fun p => labelj p.1 p.2 = v)).card % 2 = 0 := by
        intro v
        have h0c : (0 : W n) ∉ coset := fun h =>
          Finset.disjoint_left.mp hdisj_jc (by simp [planeOf]) h
        have hcount_eq : (portsj.filter (fun p => labelj p.1 p.2 = v)).card =
            ((Finset.univ.erase j).filter (fun i => v ∈ freq i)).card +
            (if v ∈ coset then 1 else 0) := by
          let P_other := (portsj.filter (fun p => labelj p.1 p.2 = v)).filter (fun p => p.1 ≠ j)
          let P_j := (portsj.filter (fun p => labelj p.1 p.2 = v)).filter (fun p => p.1 = j)
          have hdisjP : Disjoint P_other P_j := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h1 h2)
          have hunionP : portsj.filter (fun p => labelj p.1 p.2 = v) = P_other ∪ P_j := by
            ext p; simp only [P_other, P_j, Finset.mem_union, Finset.mem_filter]
            by_cases h : p.1 = j <;> simp [h]
          rw [hunionP, Finset.card_union_of_disjoint hdisjP]
          congr 1
          · refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
            · intro ⟨i, k⟩ hp
              rcases Finset.mem_filter.mp hp with ⟨hp1, hij⟩
              rcases Finset.mem_filter.mp hp1 with ⟨hpj, hlab⟩
              have hk : k < 3 := by have := (hmem_pj (i, k)).mp hpj; simp [nportsj, hij.symm] at this; exact this
              rw [hlabj_ne i hij] at hlab
              refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, ?_⟩
              have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
              rcases this with rfl | rfl | rfl <;> simp at hlab <;> simp [freq, hlab.symm]
            · intro ⟨i₁, k₁⟩ hp₁ ⟨i₂, k₂⟩ hp₂ heq
              dsimp only at heq; subst heq
              rcases Finset.mem_filter.mp hp₁ with ⟨h1, hij⟩
              rcases Finset.mem_filter.mp h1 with ⟨hp1, hl1⟩
              rcases Finset.mem_filter.mp hp₂ with ⟨h2, _⟩
              rcases Finset.mem_filter.mp h2 with ⟨hp2, hl2⟩
              have hk1 : k₁ < 3 := by have := (hmem_pj (i₁, k₁)).mp hp1; simp [nportsj, hij.symm] at this; exact this
              have hk2 : k₂ < 3 := by have := (hmem_pj (i₁, k₂)).mp hp2; simp [nportsj, hij.symm] at this; exact this
              rw [hlabj_ne i₁ hij] at hl1 hl2
              have hll := hl1.trans hl2.symm
              rcases distinct_tri (hnd i₁) with ⟨ha0, hb0, _, hab, haba, habb⟩
              have : k₁ = 0 ∨ k₁ = 1 ∨ k₁ = 2 := by omega
              have : k₂ = 0 ∨ k₂ = 1 ∨ k₂ = 2 := by omega
              rcases ‹k₁ = 0 ∨ _› with rfl | rfl | rfl <;> rcases ‹k₂ = 0 ∨ _› with rfl | rfl | rfl <;>
                simp at hll <;> (first | rfl | exact absurd hll hab | exact absurd hll hab.symm | exact absurd hll ha0 | exact absurd hll ha0.symm | exact absurd hll hb0 | exact absurd hll hb0.symm | exact absurd hll haba | exact absurd hll haba.symm | exact absurd hll habb | exact absurd hll habb.symm)
            · intro i hi
              rcases Finset.mem_filter.mp hi with ⟨hie, hfi⟩
              have hij : i ≠ j := (Finset.mem_erase.mp hie).1
              have hnp3 : nportsj i = 3 := by simp [nportsj, hij.symm]
              simp only [freq, Finset.mem_insert, Finset.mem_singleton] at hfi
              rcases hfi with rfl | rfl | rfl
              · exact ⟨(i, 0), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hmem_pj _).mpr (by dsimp only; omega), by rw [hlabj_ne i hij]; simp⟩, hij⟩, rfl⟩
              · exact ⟨(i, 1), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hmem_pj _).mpr (by dsimp only; omega), by rw [hlabj_ne i hij]; simp⟩, hij⟩, rfl⟩
              · exact ⟨(i, 2), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hmem_pj _).mpr (by dsimp only; omega), by rw [hlabj_ne i hij]; simp⟩, hij⟩, rfl⟩
          · by_cases hvc : v ∈ coset
            · rw [if_pos hvc]
              have hex : ∃ k0 < 4, pivotLab u (a j) (b j) k0 = v := by
                rcases Finset.mem_image.mp hvc with ⟨w, hw, rfl⟩
                simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl | rfl | rfl
                · exact ⟨0, by omega, by simp [pivotLab]⟩
                · exact ⟨1, by omega, by simp [pivotLab]⟩
                · exact ⟨2, by omega, by simp [pivotLab]⟩
                · exact ⟨3, by omega, by simp [pivotLab]⟩
              rcases hex with ⟨k0, hk0, hlab0⟩
              have hPjeq : P_j = {(j, k0)} := by
                ext ⟨i, k⟩
                simp only [P_j, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
                constructor
                · rintro ⟨⟨hpj, hlab⟩, hij⟩
                  subst i
                  refine ⟨rfl, ?_⟩
                  have hk4 : k < 4 := by have := (hmem_pj (j, k)).mp hpj; simp [nportsj] at this; exact this
                  rw [hlabj_j] at hlab
                  have hll := hlab.trans hlab0.symm
                  rcases distinct_tri (hnd j) with ⟨ha0, hb0, hab0, hab, haba, habb⟩
                  have hc' := add_left_cancel hll
                  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
                  have : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 ∨ k0 = 3 := by omega
                  rcases ‹k = 0 ∨ _› with rfl | rfl | rfl | rfl <;> rcases ‹k0 = 0 ∨ _› with rfl | rfl | rfl | rfl <;>
                    simp at hc' <;> (first | rfl | exact absurd hc' ha0 | exact absurd hc' ha0.symm | exact absurd hc' hb0 | exact absurd hc' hb0.symm | exact absurd hc' hab0 | exact absurd hc' hab0.symm | exact absurd hc' hab | exact absurd hc' hab.symm | exact absurd hc' haba | exact absurd hc' haba.symm | exact absurd hc' habb | exact absurd hc' habb.symm)
                · rintro ⟨rfl, rfl⟩
                  exact ⟨⟨(hmem_pj _).mpr (by simp [nportsj]; omega), by rw [hlabj_j, hlab0]⟩, rfl⟩
              rw [hPjeq]; simp
            · rw [if_neg hvc]
              have hPjeq : P_j = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                rintro ⟨i, k⟩ hp hij
                dsimp only at hij
                subst i
                rcases Finset.mem_filter.mp hp with ⟨hpj, hlab⟩
                have hk4 : k < 4 := by have := (hmem_pj (j, k)).mp hpj; simp [nportsj] at this; exact this
                rw [hlabj_j] at hlab
                apply hvc
                rw [← hlab]; unfold pivotLab
                refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
                have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
                rcases this with rfl | rfl | rfl | rfl <;> simp [planeOf]
              rw [hPjeq]; simp
        rw [hcount_eq]
        have htot : ((Finset.univ : Finset I).filter (fun i => v ∈ freq i)).card =
            ((Finset.univ.erase j).filter (fun i => v ∈ freq i)).card + (if v ∈ freq j then 1 else 0) := by
          have h1 : (Finset.univ : Finset I).filter (fun i => v ∈ freq i) =
              (if v ∈ freq j then {j} else ∅) ∪ (Finset.univ.erase j).filter (fun i => v ∈ freq i) := by
            ext i; by_cases hij : i = j
            · subst hij; by_cases h : v ∈ freq i <;> simp [h]
            · by_cases h : v ∈ freq j <;> simp [hij, h]
          rw [h1, Finset.card_union_of_disjoint]
          · split_ifs <;> simp; omega
          · split_ifs <;> simp
        have hodd_iff : v ∈ odd ↔ ((Finset.univ : Finset I).filter (fun i => v ∈ freq i)).card % 2 = 1 := by
          rw [hodd_eq]; simp [oddLabels, freq]
        by_cases hv0 : v = 0
        · subst hv0
          have h0f : ∀ i : I, (0 : W n) ∉ freq i := fun i h => by
            rcases distinct_tri (hnd i) with ⟨ha0, hb0, hab0, _, _, _⟩
            simp only [freq, Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h | h <;> first | exact ha0 h.symm | exact hb0 h.symm | exact hab0 h.symm
          have hemp : (Finset.univ.erase j).filter (fun i => (0 : W n) ∈ freq i) = ∅ :=
            Finset.filter_eq_empty_iff.mpr (fun i _ => h0f i)
          rw [hemp, if_neg h0c]; simp
        · by_cases hvf : v ∈ freq j
          · have hvnc : v ∉ coset := fun hc =>
              Finset.disjoint_left.mp hdisj_jc (by simp only [planeOf, freq] at hvf ⊢; exact Finset.mem_insert_of_mem hvf) hc
            have hvo : v ∈ odd := hfj hvf
            have hm1 := hodd_iff.mp hvo
            rw [if_pos hvf] at htot; rw [if_neg hvnc]; omega
          · by_cases hvc : v ∈ coset
            · have hvS : v ∈ S := by rw [hS_decomp]; exact Finset.mem_union_right _ hvc
              have hvo : v ∈ odd := (Finset.mem_insert.mp hvS).resolve_left hv0
              have hm1 := hodd_iff.mp hvo
              rw [if_neg hvf] at htot; rw [if_pos hvc]; omega
            · have hvnotS : v ∉ S := by
                rw [hS_decomp, Finset.mem_union]; rintro (hpl | hc)
                · simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hpl
                  rcases hpl with h | h; exact hv0 h; exact hvf (by simpa [freq] using h)
                · exact hvc hc
              have hvno : v ∉ odd := fun h => hvnotS (Finset.mem_insert_of_mem h)
              have hm0 : ((Finset.univ : Finset I).filter (fun i => v ∈ freq i)).card % 2 = 0 := by
                have := hodd_iff.not.mp hvno; omega
              rw [if_neg hvf] at htot; rw [if_neg hvc]; omega
      have hsum_rowj_eq : ∀ (P : I → W n) (d : I → F) (A : Finset (I × Nat)),
          A ⊆ portsj →
          P j ∈ coset →
          (∀ i, i ≠ j → (P i = 0 ∧ d i = 0) ∨ (P i = a i ∧ d i = 0) ∨ (P i = b i ∧ d i = 0) ∨ (P i = a i + b i ∧ d i = 1)) →
          (A.filter (fun p => p.1 = j)).image Prod.snd = pivotToSub u (a j) (b j) (P j) (d j) →
          (∀ i, i ≠ j → (A.filter (fun p => p.1 = i)).image Prod.snd = nonpivotToSub (a i) (b i) (P i) (d i)) →
          ∀ v : W n, v ≠ 0 →
            (∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v) =
              ((portsj.filter (fun p => labelj p.1 p.2 = v)).card : Int) -
              2 * ((A.filter (fun p => labelj p.1 p.2 = v)).card : Int) := by
        intro P d A hAsub hPj hPoth hAj hAoth v hv0
        have hterm : ∀ i : I, rowCoeff (a i) (b i) (P i) (d i) v =
            ∑ k ∈ Finset.range (nportsj i), if labelj i k = v then (if (i, k) ∈ A then (-1 : Int) else 1) else 0 := by
          intro i
          by_cases hij : i = j
          · subst hij
            have hrc := pivot_rowCoeff_cases (hnd i) hu_not_pl hPj (d := d i)
            have hnp4 : nportsj i = 4 := by simp [nportsj]
            rw [hnp4]
            by_cases hvc : v ∈ coset
            · have hex : ∃ k0 < 4, pivotLab u (a i) (b i) k0 = v := by
                rcases Finset.mem_image.mp hvc with ⟨w, hw, rfl⟩
                simp only [planeOf, Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl | rfl | rfl
                · exact ⟨0, by omega, by simp [pivotLab]⟩
                · exact ⟨1, by omega, by simp [pivotLab]⟩
                · exact ⟨2, by omega, by simp [pivotLab]⟩
                · exact ⟨3, by omega, by simp [pivotLab]⟩
              rcases hex with ⟨k0, hk0, hlab0⟩
              rw [Finset.sum_eq_single k0]
              · rw [hlabj_j, if_pos hlab0, ← hlab0, hrc.2.2.2.1 k0 hk0]
                have hmem : (i, k0) ∈ A ↔ k0 ∈ pivotToSub u (a i) (b i) (P i) (d i) := by
                  rw [← hAj, Finset.mem_image]
                  constructor
                  · intro h; exact ⟨(i, k0), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
                  · rintro ⟨⟨i', k'⟩, hf, hk'⟩
                    have hi' := (Finset.mem_filter.mp hf).2
                    dsimp only at hk'; subst hi'; subst hk'; exact (Finset.mem_filter.mp hf).1
                simp only [hmem]
              · intro k hk hne
                have hklt := Finset.mem_range.mp hk
                rw [hlabj_j, if_neg]
                intro heq
                have hc' := add_left_cancel (heq.trans hlab0.symm)
                rcases distinct_tri (hnd i) with ⟨ha0, hb0, hab0, hab, haba, habb⟩
                have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
                have : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 ∨ k0 = 3 := by omega
                rcases ‹k = 0 ∨ _› with rfl | rfl | rfl | rfl <;> rcases ‹k0 = 0 ∨ _› with rfl | rfl | rfl | rfl <;>
                  simp at hc' <;> (first | exact hne rfl | exact absurd hc' ha0 | exact absurd hc' ha0.symm | exact absurd hc' hb0 | exact absurd hc' hb0.symm | exact absurd hc' hab0 | exact absurd hc' hab0.symm | exact absurd hc' hab | exact absurd hc' hab.symm | exact absurd hc' haba | exact absurd hc' haba.symm | exact absurd hc' habb | exact absurd hc' habb.symm)
              · intro h; exact absurd (Finset.mem_range.mpr hk0) h
            · rw [hrc.2.2.1 v hvc hv0]
              symm
              refine Finset.sum_eq_zero (fun k hk => ?_)
              have hklt := Finset.mem_range.mp hk
              rw [hlabj_j, if_neg]
              intro heq; apply hvc; rw [← heq]; unfold pivotLab
              refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
              have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
              rcases this with rfl | rfl | rfl | rfl <;> simp [planeOf]
          · have hrc := nonpivot_rowCoeff_cases (hnd i) (hPoth i hij)
            have hnp3 : nportsj i = 3 := by simp [nportsj, Ne.symm hij]
            rw [hnp3]
            by_cases hvf : v ∈ triOf (a i) (b i)
            · have hex : ∃ k0 < 3, labelj i k0 = v := by
                simp only [triOf, Finset.mem_insert, Finset.mem_singleton] at hvf
                rcases hvf with rfl | rfl | rfl
                · exact ⟨0, by omega, by rw [hlabj_ne i hij]; simp⟩
                · exact ⟨1, by omega, by rw [hlabj_ne i hij]; simp⟩
                · exact ⟨2, by omega, by rw [hlabj_ne i hij]; simp⟩
              rcases hex with ⟨k0, hk0, hlab0⟩
              rw [Finset.sum_eq_single k0]
              · rw [if_pos hlab0, ← hlab0, hlabj_ne i hij, hrc.2.2.2.1 k0 hk0]
                have hmem : (i, k0) ∈ A ↔ k0 ∈ nonpivotToSub (a i) (b i) (P i) (d i) := by
                  rw [← hAoth i hij, Finset.mem_image]
                  constructor
                  · intro h; exact ⟨(i, k0), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
                  · rintro ⟨⟨i', k'⟩, hf, hk'⟩
                    have hi' := (Finset.mem_filter.mp hf).2
                    dsimp only at hk'; subst hi'; subst hk'; exact (Finset.mem_filter.mp hf).1
                simp only [hmem]
              · intro k hk hne
                have hklt := Finset.mem_range.mp hk
                rw [if_neg]
                intro heq
                have hll := heq.trans hlab0.symm
                rw [hlabj_ne i hij, hlabj_ne i hij] at hll
                rcases distinct_tri (hnd i) with ⟨ha0, hb0, _, hab, haba, habb⟩
                have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
                have : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 := by omega
                rcases ‹k = 0 ∨ _› with rfl | rfl | rfl <;> rcases ‹k0 = 0 ∨ _› with rfl | rfl | rfl <;>
                  simp at hll <;> (first | exact hne rfl | exact absurd hll hab | exact absurd hll hab.symm | exact absurd hll ha0 | exact absurd hll ha0.symm | exact absurd hll hb0 | exact absurd hll hb0.symm | exact absurd hll haba | exact absurd hll haba.symm | exact absurd hll habb | exact absurd hll habb.symm)
              · intro h; exact absurd (Finset.mem_range.mpr hk0) h
            · rw [hrc.2.2.1 v hv0 hvf]
              symm
              refine Finset.sum_eq_zero (fun k hk => ?_)
              have hklt := Finset.mem_range.mp hk
              rw [hlabj_ne i hij, if_neg]
              intro heq; apply hvf
              have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
              rcases this with rfl | rfl | rfl <;> simp at heq <;> simp [triOf, heq.symm]
        simp_rw [hterm]
        have hbi : (∑ i : I, ∑ k ∈ Finset.range (nportsj i),
              if labelj i k = v then (if (i, k) ∈ A then (-1 : Int) else 1) else 0) =
            ∑ p ∈ portsj, if labelj p.1 p.2 = v then (if p ∈ A then (-1 : Int) else 1) else 0 := by
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_image (fun k₁ _ k₂ _ h => (Prod.mk.inj h).2)]
          · intro i₁ _ i₂ _ hne
            refine Finset.disjoint_left.mpr (fun p h1 h2 => ?_)
            rcases Finset.mem_image.mp h1 with ⟨k₁, _, rfl⟩
            rcases Finset.mem_image.mp h2 with ⟨k₂, _, h⟩
            exact hne (Prod.mk.inj h).1.symm
        rw [hbi]
        have hstep : ∀ p ∈ portsj,
            (if labelj p.1 p.2 = v then (if p ∈ A then (-1 : Int) else 1) else 0) =
            (if labelj p.1 p.2 = v then (1 : Int) else 0) -
            2 * (if labelj p.1 p.2 = v ∧ p ∈ A then (1 : Int) else 0) := by
          intro p _; by_cases h1 : labelj p.1 p.2 = v <;> by_cases h2 : p ∈ A <;> simp [h1, h2]
        rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hs1 : (∑ p ∈ portsj, if labelj p.1 p.2 = v then (1 : Int) else 0) =
            ((portsj.filter (fun p => labelj p.1 p.2 = v)).card : Int) := by
          rw [Finset.sum_boole]
        have hs2 : (∑ p ∈ portsj, if labelj p.1 p.2 = v ∧ p ∈ A then (1 : Int) else 0) =
            ((A.filter (fun p => labelj p.1 p.2 = v)).card : Int) := by
          rw [Finset.sum_boole]
          congr 2; ext p
          simp only [Finset.mem_filter]
          exact ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨hAsub h2, h1, h2⟩⟩
        rw [hs1, hs2]
      refine Finset.card_bij
        (fun p _ => (Finset.univ : Finset I).biUnion (fun i =>
          (if i = j then pivotToSub u (a i) (b i) (p.1 i) (p.2 i)
           else nonpivotToSub (a i) (b i) (p.1 i) (p.2 i)).image (fun k => (i, k)))) ?_ ?_ ?_
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpG, hpjnot⟩
        rcases (hpart p hpG).2.2 with ⟨hall, _, _⟩ | ⟨_, hczero, j', hj'not, hoth_in, hoth_row0, hSeq⟩
        · exact absurd (hall j) hpjnot
        · have hjj' : j' = j := by
            by_contra hne; exact hpjnot (hoth_in j (Ne.symm hne))
          subst j'
          have hPj_coset : p.1 j ∈ coset := by
            have hmemS : p.1 j ∈ S := by
              rw [hSeq, Finset.mem_union]; right
              exact Finset.mem_image.mpr ⟨0, by simp [planeOf], by simp⟩
            rw [hS_decomp, Finset.mem_union] at hmemS
            exact hmemS.resolve_left hpjnot
          have hPoth : ∀ i, i ≠ j → (p.1 i = 0 ∧ p.2 i = 0) ∨ (p.1 i = a i ∧ p.2 i = 0) ∨
              (p.1 i = b i ∧ p.2 i = 0) ∨ (p.1 i = a i + b i ∧ p.2 i = 1) :=
            fun i hij => nonpivot_row_values (p.2 i) (hnd i) (hoth_in i hij) (hoth_row0 i hij)
          let A := (Finset.univ : Finset I).biUnion (fun i =>
            (if i = j then pivotToSub u (a i) (b i) (p.1 i) (p.2 i)
             else nonpivotToSub (a i) (b i) (p.1 i) (p.2 i)).image (fun k => (i, k)))
          have hAsub : A ⊆ portsj := by
            intro ⟨i, k⟩ hmem
            rcases Finset.mem_biUnion.mp hmem with ⟨i', _, hk'⟩
            rcases Finset.mem_image.mp hk' with ⟨k', hsub, heq⟩
            rcases Prod.mk.inj heq.symm with ⟨rfl, rfl⟩
            by_cases hij : i = j
            · subst hij; simp only [ite_true] at hsub
              exact (hmem_pj (i, k)).mpr (by
                simp only [nportsj, ite_true]
                exact Finset.mem_range.mp ((pivot_rowCoeff_cases (hnd i) hu_not_pl hPj_coset (d := p.2 i)).2.2.2.2.1 hsub))
            · simp only [hij, ite_false] at hsub
              exact (hmem_pj (i, k)).mpr (by
                simp only [nportsj, Ne.symm hij, Option.some.injEq, ite_false]
                exact Finset.mem_range.mp ((nonpivot_rowCoeff_cases (hnd i) (hPoth i hij)).2.2.2.2.1 hsub))
          have hArow : ∀ i : I, (A.filter (fun q => q.1 = i)).image Prod.snd =
              if i = j then pivotToSub u (a i) (b i) (p.1 i) (p.2 i)
              else nonpivotToSub (a i) (b i) (p.1 i) (p.2 i) := by
            intro i; ext k
            simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨⟨i', k'⟩, ⟨⟨i'', k'', hk'', heq⟩, rfl⟩, rfl⟩
              rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact hk''
            · intro hk; exact ⟨(i, k), ⟨⟨i, k, hk, rfl⟩, rfl⟩, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAsub, ?_, ?_⟩
          · intro i
            have hci : ((A.filter (fun q => q.1 = i)).image Prod.snd).card = (A.filter (fun q => q.1 = i)).card :=
              Finset.card_image_of_injOn (fun x hx y hy heq =>
                Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq)
            rw [← hci, hArow i]
            by_cases hij : i = j
            · subst hij; simp only [ite_true, nportsj]
              exact (pivot_rowCoeff_cases (hnd i) hu_not_pl hPj_coset (d := p.2 i)).2.2.2.2.2.1
            · simp only [hij, Ne.symm hij, Option.some.injEq, ite_false, nportsj]
              exact (nonpivot_rowCoeff_cases (hnd i) (hPoth i hij)).2.2.2.2.2.1
          · intro v hv
            have hv0 : v ≠ 0 := by
              rcases Finset.mem_image.mp hv with ⟨⟨i, k⟩, hpj, rfl⟩
              have hklt := (hmem_pj (i, k)).mp hpj
              by_cases hij : i = j
              · subst hij
                have hk4 : k < 4 := by simp [nportsj] at hklt; exact hklt
                rw [hlabj_j]
                intro h0
                have hmem : pivotLab u (a i) (b i) k ∈ coset := by
                  unfold pivotLab; refine Finset.mem_image.mpr ⟨_, ?_, rfl⟩
                  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
                  rcases this with rfl | rfl | rfl | rfl <;> simp [planeOf]
                exact Finset.disjoint_left.mp hdisj_jc (by simp [planeOf]) (h0 ▸ hmem)
              · have hk3 : k < 3 := by simp [nportsj, Ne.symm hij] at hklt; exact hklt
                rw [hlabj_ne i hij]
                rcases distinct_tri (hnd i) with ⟨ha0, hb0, hab0, _, _, _⟩
                have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
                rcases this with rfl | rfl | rfl <;> simp <;> assumption
            have hsr := hsum_rowj_eq p.1 p.2 A hAsub hPj_coset hPoth
              (by simpa using hArow j) (fun i hij => by simpa [hij] using hArow i) v hv0
            have hsum0 : (∑ i : I, rowCoeff (a i) (b i) (p.1 i) (p.2 i) v) = 0 := by
              have hcv := hczero v
              simp only [totalCoeff, hv0, ite_false, zero_sub, neg_eq_zero] at hcv
              exact hcv
            have hev := hdegj_even v
            change (A.filter (fun p => labelj p.1 p.2 = v)).card = quotaj v
            dsimp only [quotaj]
            omega
      · intro p₁ hp₁ p₂ hp₂ heq
        rcases Finset.mem_filter.mp hp₁ with ⟨hp₁G, hp₁j⟩
        rcases Finset.mem_filter.mp hp₂ with ⟨hp₂G, hp₂j⟩
        have hinfo : ∀ p : (I → W n) × (I → F), p ∈ good → p.1 j ∉ planeOf (a j) (b j) →
            p.1 j ∈ coset ∧ (∀ i, i ≠ j → p.1 i ∈ planeOf (a i) (b i) ∧ rowCoeff (a i) (b i) (p.1 i) (p.2 i) 0 = 1) := by
          intro p hpG hpj
          rcases (hpart p hpG).2.2 with ⟨hall, _, _⟩ | ⟨_, _, j', _, hoth_in, hoth_row0, hSeq⟩
          · exact absurd (hall j) hpj
          · have hjj' : j' = j := by by_contra hne; exact hpj (hoth_in j (Ne.symm hne))
            subst j'
            refine ⟨?_, fun i hij => ⟨hoth_in i hij, hoth_row0 i hij⟩⟩
            have hmemS : p.1 j ∈ S := by
              rw [hSeq, Finset.mem_union]; right
              exact Finset.mem_image.mpr ⟨0, by simp [planeOf], by simp⟩
            rw [hS_decomp, Finset.mem_union] at hmemS
            exact hmemS.resolve_left hpj
        rcases hinfo p₁ hp₁G hp₁j with ⟨hP1j, hP1oth⟩
        rcases hinfo p₂ hp₂G hp₂j with ⟨hP2j, hP2oth⟩
        have hpair : ∀ i : I, (p₁.1 i, p₁.2 i) = (p₂.1 i, p₂.2 i) := by
          intro i
          have hsub_eq : (if i = j then pivotToSub u (a i) (b i) (p₁.1 i) (p₁.2 i)
              else nonpivotToSub (a i) (b i) (p₁.1 i) (p₁.2 i)) =
            (if i = j then pivotToSub u (a i) (b i) (p₂.1 i) (p₂.2 i)
              else nonpivotToSub (a i) (b i) (p₂.1 i) (p₂.2 i)) := by
            ext k
            have hmem : (i, k) ∈ (Finset.univ : Finset I).biUnion (fun i =>
                (if i = j then pivotToSub u (a i) (b i) (p₁.1 i) (p₁.2 i)
                 else nonpivotToSub (a i) (b i) (p₁.1 i) (p₁.2 i)).image (fun k => (i, k))) ↔
              (i, k) ∈ (Finset.univ : Finset I).biUnion (fun i =>
                (if i = j then pivotToSub u (a i) (b i) (p₂.1 i) (p₂.2 i)
                 else nonpivotToSub (a i) (b i) (p₂.1 i) (p₂.2 i)).image (fun k => (i, k))) := by rw [heq]
            simpa using hmem
          by_cases hij : i = j
          · subst hij; simp only [ite_true] at hsub_eq
            have hc1 := (pivot_rowCoeff_cases (hnd i) hu_not_pl hP1j (d := p₁.2 i)).2.2.2.2.2.2
            have hc2 := (pivot_rowCoeff_cases (hnd i) hu_not_pl hP2j (d := p₂.2 i)).2.2.2.2.2.2
            rw [← hc1, hsub_eq, hc2]
          · simp only [hij, ite_false] at hsub_eq
            have hc1 := (nonpivot_rowCoeff_cases (hnd i) (nonpivot_row_values (p₁.2 i) (hnd i) (hP1oth i hij).1 (hP1oth i hij).2)).2.2.2.2.2.2
            have hc2 := (nonpivot_rowCoeff_cases (hnd i) (nonpivot_row_values (p₂.2 i) (hnd i) (hP2oth i hij).1 (hP2oth i hij).2)).2.2.2.2.2.2
            rw [← hc1, hsub_eq, hc2]
        exact Prod.ext (funext (fun i => congrArg Prod.fst (hpair i))) (funext (fun i => congrArg Prod.snd (hpair i)))
      · intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hApow, hApar, hAq⟩
        have hAsub : A ⊆ portsj := Finset.mem_powerset.mp hApow
        let rowA (i : I) : Finset Nat := (A.filter (fun p => p.1 = i)).image Prod.snd
        have hrowA_sub : ∀ i, rowA i ⊆ Finset.range (nportsj i) := by
          intro i k hk
          rcases Finset.mem_image.mp hk with ⟨⟨i', k'⟩, hf, rfl⟩
          have hi' := (Finset.mem_filter.mp hf).2
          have hp := (Finset.mem_filter.mp hf).1
          subst hi'
          exact Finset.mem_range.mpr ((hmem_pj (i', k')).mp (hAsub hp))
        have hrowA_par : ∀ i, (rowA i).card % 2 = if nportsj i = 4 then 1 else 0 := by
          intro i
          have hci : (rowA i).card = (A.filter (fun p => p.1 = i)).card :=
            Finset.card_image_of_injOn (fun x hx y hy heq =>
              Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq)
          rw [hci]; exact hApar i
        let P : I → W n := fun i =>
          if i = j then (pivotFromSub u (a i) (b i) (rowA i)).1
          else (nonpivotFromSub (a i) (b i) (rowA i)).1
        let d : I → F := fun i =>
          if i = j then (pivotFromSub u (a i) (b i) (rowA i)).2
          else (nonpivotFromSub (a i) (b i) (rowA i)).2
        have hrt_j : P j ∈ coset ∧ pivotToSub u (a j) (b j) (P j) (d j) = rowA j := by
          have hsub4 : rowA j ⊆ Finset.range 4 := by simpa [nportsj] using hrowA_sub j
          have hodd1 : (rowA j).card % 2 = 1 := by simpa [nportsj] using hrowA_par j
          have h := pivot_fromSub_roundtrip (hnd j) hu_not_pl (rowA j) hsub4 hodd1
          refine ⟨?_, ?_⟩
          · dsimp only [P]; rw [if_pos rfl]; exact h.1
          · dsimp only [P, d]; rw [if_pos rfl, if_pos rfl]; exact h.2
        have hrt_oth : ∀ i, i ≠ j →
            ((P i = 0 ∧ d i = 0) ∨ (P i = a i ∧ d i = 0) ∨ (P i = b i ∧ d i = 0) ∨ (P i = a i + b i ∧ d i = 1)) ∧
            nonpivotToSub (a i) (b i) (P i) (d i) = rowA i := by
          intro i hij
          have hsub3 : rowA i ⊆ Finset.range 3 := by simpa [nportsj, hij.symm] using hrowA_sub i
          have heven0 : (rowA i).card % 2 = 0 := by simpa [nportsj, hij.symm] using hrowA_par i
          have h := nonpivot_fromSub_roundtrip (hnd i) (rowA i) hsub3 heven0
          simpa [P, d, hij] using h
        have htc0 : ∀ v : W n, totalCoeff a b P d e v = 0 := by
          intro v
          by_cases hv0 : v = 0
          · subst hv0
            simp only [totalCoeff, ite_true]
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
            have hrj : rowCoeff (a j) (b j) (P j) (d j) 0 = 2 :=
              (pivot_rowCoeff_cases (hnd j) hu_not_pl hrt_j.1 (d := d j)).2.1
            have hroth : ∀ i ∈ Finset.univ.erase j, rowCoeff (a i) (b i) (P i) (d i) 0 = 1 :=
              fun i hi => (nonpivot_rowCoeff_cases (hnd i) (hrt_oth i (Finset.mem_erase.mp hi).1).1).2.1
            rw [hrj, Finset.sum_congr rfl hroth]
            simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, I]
            have hm : (m : Int) = 4 * (e : Int) - 1 := by omega
            have hm1 : ((m - 1 : Nat) : Int) = 4 * (e : Int) - 2 := by omega
            omega
          · have htc2 : totalCoeff a b P d e v = - ∑ i : I, rowCoeff (a i) (b i) (P i) (d i) v := by
              dsimp only [totalCoeff]; simp [hv0]; rfl
            have hsr := hsum_rowj_eq P d A hAsub hrt_j.1 (fun i hij => (hrt_oth i hij).1)
              hrt_j.2.symm (fun i hij => (hrt_oth i hij).2.symm) v hv0
            by_cases hvl : v ∈ labelsj
            · have hq := hAq v hvl
              have hev := hdegj_even v
              dsimp only [quotaj] at hq
              omega
            · have hpj_empty : portsj.filter (fun q => labelj q.1 q.2 = v) = ∅ :=
                Finset.filter_eq_empty_iff.mpr (fun q hq heq => hvl (Finset.mem_image.mpr ⟨q, hq, heq⟩))
              have hA_empty : A.filter (fun q => labelj q.1 q.2 = v) = ∅ :=
                Finset.filter_eq_empty_iff.mpr (fun q hq heq => hvl (Finset.mem_image.mpr ⟨q, hAsub hq, heq⟩))
              rw [htc2, hsr, hpj_empty, hA_empty]; simp
        have hpG : (P, d) ∈ good := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
          have hf := errs_fourier a b P d e x
          have h0 : (∑ v : W n, totalCoeff a b P d e v * chi v x) = 0 :=
            Finset.sum_eq_zero (fun v _ => by rw [htc0 v, zero_mul])
          rw [h0] at hf
          set errC := ((Finset.univ : Finset (Fin m)).filter (fun i =>
            dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card
          change (4 * e : Int) - 4 * (errC : Int) = 0 at hf
          change errC ≤ e
          omega
        have hPj_not : P j ∉ planeOf (a j) (b j) :=
          (pivot_rowCoeff_cases (hnd j) hu_not_pl hrt_j.1 (d := d j)).1
        refine ⟨(P, d), Finset.mem_filter.mpr ⟨hpG, hPj_not⟩, ?_⟩
        ext ⟨i, k⟩
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨i', k', hk', hi', hk''⟩
          subst hi'; subst hk''
          have hkr : k' ∈ rowA i' := by
            by_cases hij : i' = j
            · subst i'; simp only [ite_true] at hk'; rwa [hrt_j.2] at hk'
            · simp only [hij, ite_false] at hk'; rwa [(hrt_oth i' hij).2] at hk'
          rcases Finset.mem_image.mp hkr with ⟨⟨i'', k''⟩, hf, hkeq⟩
          have hi'' := (Finset.mem_filter.mp hf).2
          dsimp only at hkeq; subst hi''; subst hkeq
          exact (Finset.mem_filter.mp hf).1
        · intro hmem
          refine ⟨i, k, ?_, rfl, rfl⟩
          have hk'' : k ∈ rowA i := Finset.mem_image.mpr ⟨(i, k), Finset.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
          by_cases hij : i = j
          · subst hij; simp only [ite_true]; rwa [hrt_j.2]
          · simp only [hij, ite_false]; rwa [(hrt_oth i hij).2]
    rw [hgood_decomp, hnone_card]
    congr 1
    by_cases hS8 : S.card = 8
    · rw [if_pos hS8, if_pos hS8]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hfj : freq j ⊆ odd
      · rw [if_pos hfj, if_pos hfj, hsome_card hS8 j hfj]
      · rw [if_neg hfj, if_neg hfj]
    · rw [if_neg hS8, if_neg hS8]
  · rw [if_neg hScond]
    have hemp : good = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have h := hpart p hp
      exact hScond ⟨h.2.1, h.1⟩
    rw [hemp]; simp

end PEqualNP.Outside.L_lib_979_aux

theorem PEqualNP.Outside.L_lib_979 : ∀ (n e : Nat), 0 < e →
  let m := 4*e-1
  let F := ZMod 2
  let W := Fin n → F
  let I := Fin m
  ∀ a b : I → W, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let freq := fun i : I => ({a i, b i, a i+b i} : Finset W)
    let fs := (Finset.univ : Finset I).biUnion freq
    let odd := fs.filter (fun v => ((Finset.univ : Finset I).filter (fun i => v ∈ freq i)).card % 2 = 1)
    let S := insert (0 : W) odd
    let outside := fun (i : I) => if h : ∃ v ∈ odd, v ∉ freq i then Classical.choose h else (0 : W)
    let good := (Finset.univ : Finset ((I → W) × (I → F))).filter (fun p =>
      ∀ x : W, ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (p.1 i) x+p.2 i)).card ≤ e)
    let tally := fun (pivot : Option I) =>
      let nports := fun i : I => if pivot = some i then 4 else 3
      let label := fun (i : I) (j : Nat) =>
        if pivot = some i then outside i + (if j = 0 then 0 else if j = 1 then a i else if j = 2 then b i else a i+b i)
        else if j = 0 then a i else if j = 1 then b i else a i+b i
      let ports := (Finset.univ : Finset I).biUnion (fun i => (Finset.range (nports i)).image (fun j => (i,j)))
      let labels := ports.image (fun p => label p.1 p.2)
      let quota := fun v : W => (((ports.filter (fun p => label p.1 p.2 = v)).card) + (if pivot = none then 1 else 0)) / 2
      let V := (I × Nat) ⊕ (W × Nat)
      let localNodes := ports ∪ (Finset.univ : Finset I).image (fun i => (i,4))
      let slots := labels.biUnion (fun v => (Finset.range (quota v)).image (fun j => (v,j)))
      let verts : Finset V := localNodes.image Sum.inl ∪ slots.image Sum.inr
      let sameRow := fun (p q : I × Nat) => p.1 = q.1 ∧ p.2 ≠ q.2 ∧
        (p.2 = 4 ∨ q.2 = 4 ∨ p.2 / 2 = q.2 / 2)
      let attach := fun (p : I × Nat) (q : W × Nat) => p.2 < nports p.1 ∧ label p.1 p.2 = q.1
      let edge := fun (p q : V) => Sum.elim (fun x => Sum.elim (sameRow x) (attach x) q)
        (fun y => Sum.elim (fun x => attach x y) (fun _ => False) q) p
      let matchings := (Finset.univ : Finset (↥verts → ↥verts)).filter (fun f =>
        @decide (∀ x, f (f x) = x ∧ edge x.val (f x).val) (Classical.propDecidable _) = true)
      matchings.card / (∏ v ∈ labels, Nat.factorial (quota v))
    good.card = if 4 ≤ S.card ∧ (∀ v ∈ S, ∀ w ∈ S, v+w ∈ S) then
      S.card * tally none + (if S.card = 8 then ∑ i : I, if freq i ⊆ odd then tally (some i) else 0 else 0)
      else 0 :=
  fun n e he => PEqualNP.Outside.L_lib_979_aux.main_979 n e he
