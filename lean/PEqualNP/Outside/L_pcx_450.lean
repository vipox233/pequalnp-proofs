import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_450_aux

open Finset

abbrev V (n : ℕ) := Fin n → ZMod 2

def sgn (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> decide

lemma sgn_zero : sgn 0 = 1 := by decide

lemma sgn_one : sgn 1 = -1 := by decide

lemma abs_sgn (a : ZMod 2) : |sgn a| = 1 := by
  fin_cases a <;> decide

lemma sgn_le_one (a : ZMod 2) : sgn a ≤ 1 := by
  fin_cases a <;> decide

lemma sgn_inj {a b : ZMod 2} (h : sgn a = sgn b) : a = b := by
  have key : ∀ c d : ZMod 2, sgn c = sgn d → c = d := by decide
  exact key a b h

lemma two_eq : (2 : ZMod 2) = 0 := by decide

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  exact key a

lemma eq_one_of_ne {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with h' | h'
  · exact absurd h' h
  · exact h'

lemma add_self_V {n : ℕ} (x : V n) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = c
  fin_cases c <;> decide

lemma neg_V {n : ℕ} (x : V n) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_V]

lemma sub_V {n : ℕ} (x y : V n) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_V]

def dp {n : ℕ} (w x : V n) : ZMod 2 := ∑ i, w i * x i

lemma dp_add {n : ℕ} (w x y : V n) : dp w (x + y) = dp w x + dp w y := by
  simp only [dp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma add_dp {n : ℕ} (w w' x : V n) : dp (w + w') x = dp w x + dp w' x := by
  simp only [dp, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dp_zero_left {n : ℕ} (x : V n) : dp 0 x = 0 := by simp [dp]

lemma dp_sub {n : ℕ} (w x y : V n) : dp w (x - y) = dp w x + dp w y := by
  rw [sub_V, dp_add]

def Q {n : ℕ} (f : V n → ZMod 2) (u v : V n) : ZMod 2 := f (u+v) + f u + f v + f 0

lemma Q_comm {n : ℕ} (f : V n → ZMod 2) (u v : V n) : Q f u v = Q f v u := by
  unfold Q; rw [add_comm u v]; ring

lemma f_shift {n : ℕ} (f : V n → ZMod 2) (x s : V n) :
    f (x + s) + f x = Q f x s + (f s + f 0) := by
  unfold Q
  linear_combination (-(f s) - f 0) * two_eq


lemma sum_shift {n : ℕ} (s : Finset (V n)) (hs : ∀ x ∈ s, ∀ y ∈ s, x + y ∈ s) (t : V n)
    (ht : t ∈ s) (F : V n → ℤ) : ∑ x ∈ s, F (t + x) = ∑ x ∈ s, F x := by
  apply Finset.sum_nbij' (fun x => t + x) (fun x => t + x)
  · intro x hx; exact hs t ht x hx
  · intro x hx; exact hs t ht x hx
  · intro x _; show t + (t + x) = x; rw [← add_assoc, add_self_V, zero_add]
  · intro x _; show t + (t + x) = x; rw [← add_assoc, add_self_V, zero_add]
  · intro x _; rfl

lemma char_sum_one {n : ℕ} (s : Finset (V n)) (ψ : V n → ZMod 2) (h : ∀ x ∈ s, ψ x = 0) :
    ∑ x ∈ s, sgn (ψ x) = s.card := by
  rw [Finset.sum_congr rfl (fun x hx => by rw [h x hx, sgn_zero])]
  simp

lemma char_sum_zero {n : ℕ} (s : Finset (V n)) (hs : ∀ x ∈ s, ∀ y ∈ s, x + y ∈ s)
    (ψ : V n → ZMod 2) (hψ : ∀ x ∈ s, ∀ y ∈ s, ψ (x + y) = ψ x + ψ y) (t : V n) (ht : t ∈ s)
    (h1 : ψ t = 1) : ∑ x ∈ s, sgn (ψ x) = 0 := by
  have h := sum_shift s hs t ht (fun x => sgn (ψ x))
  have h2 : ∑ x ∈ s, sgn (ψ (t + x)) = - ∑ x ∈ s, sgn (ψ x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hψ t ht x hx, h1, sgn_add, sgn_one]; ring
  linarith

lemma card_pow2 {n : ℕ} (P : V n → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) :
    ∃ k ≤ n, Nat.card {x // P x} = 2 ^ k := by
  let H : AddSubgroup (V n) :=
    { carrier := {x | P x}, zero_mem' := h0, add_mem' := fun {a b} ha hb => hadd a b ha hb,
      neg_mem' := fun {a} ha => (by show P (-a); rw [neg_V]; exact ha) }
  have hd : Nat.card H ∣ Nat.card (V n) := AddSubgroup.card_addSubgroup_dvd_card H
  have hc : Nat.card (V n) = 2 ^ n := by simp [V]
  rw [hc, Nat.dvd_prime_pow Nat.prime_two] at hd
  obtain ⟨k, hk, hk'⟩ := hd
  exact ⟨k, hk, hk'⟩

noncomputable def fs {n : ℕ} (P : V n → Prop) : Finset (V n) := by
  classical exact univ.filter P

lemma mem_fs {n : ℕ} (P : V n → Prop) (x : V n) : x ∈ fs P ↔ P x := by
  classical
  unfold fs; simp

lemma card_fs {n : ℕ} (P : V n → Prop) : (fs P).card = Nat.card {x // P x} := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => mem_fs P x))

lemma fs_closed {n : ℕ} (P : V n → Prop) (hadd : ∀ x y, P x → P y → P (x + y)) :
    ∀ x ∈ fs P, ∀ y ∈ fs P, x + y ∈ fs P := by
  intro x hx y hy
  rw [mem_fs] at *
  exact hadd x y hx hy

lemma card_fs_pow2 {n : ℕ} (P : V n → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) :
    ∃ k, ((fs P).card : ℤ) = 2 ^ k := by
  obtain ⟨k, -, hk⟩ := card_pow2 P h0 hadd
  exact ⟨k, by rw [card_fs, hk]; push_cast; ring⟩

noncomputable def chg {n : ℕ} (f : V n → ZMod 2) (P : V n → Prop) : ℤ :=
  (Nat.card {x : V n // P x ∧ f x = 0} : ℤ) - (Nat.card {x : V n // P x ∧ f x = 1} : ℤ)

lemma chg_eq {n : ℕ} (f : V n → ZMod 2) (P : V n → Prop) :
    chg f P = ∑ x ∈ fs P, sgn (f x) := by
  classical
  unfold chg
  rw [← card_fs (fun x => P x ∧ f x = 0), ← card_fs (fun x => P x ∧ f x = 1)]
  have e0 : fs (fun x => P x ∧ f x = 0) = (fs P).filter (fun x => f x = 0) := by
    ext x; simp [mem_fs]
  have e1 : fs (fun x => P x ∧ f x = 1) = (fs P).filter (fun x => ¬ f x = 0) := by
    ext x
    simp only [mem_fs, mem_filter]
    constructor
    · rintro ⟨hp, hx⟩; exact ⟨hp, by rw [hx]; decide⟩
    · rintro ⟨hp, hx⟩; exact ⟨hp, eq_one_of_ne hx⟩
  rw [e0, e1, ← Finset.sum_filter_add_sum_filter_not (fs P) (fun x => f x = 0)]
  have h0 : ∑ x ∈ (fs P).filter (fun x => f x = 0), sgn (f x)
      = ∑ x ∈ (fs P).filter (fun x => f x = 0), (1 : ℤ) :=
    Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2, sgn_zero])
  have h1 : ∑ x ∈ (fs P).filter (fun x => ¬ f x = 0), sgn (f x)
      = ∑ x ∈ (fs P).filter (fun x => ¬ f x = 0), (-1 : ℤ) :=
    Finset.sum_congr rfl (fun x hx => by rw [eq_one_of_ne (Finset.mem_filter.1 hx).2, sgn_one])
  rw [h0, h1]
  simp
  ring


lemma sep {n : ℕ} (S : Submodule (ZMod 2) (V n)) (y : V n) (hy : y ∉ S) :
    ∃ w : V n, (∀ s ∈ S, dp w s = 0) ∧ dp w y = 1 := by
  classical
  obtain ⟨φ, hφy, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  refine ⟨fun i => φ (fun j => if i = j then 1 else 0), ?_, ?_⟩
  · have key : ∀ x : V n, dp (fun i => φ (fun j => if i = j then 1 else 0)) x = φ x := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      unfold dp
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul, mul_comm]
    intro s hs
    rw [key]
    have : φ s ∈ S.map φ := Submodule.mem_map_of_mem hs
    rw [hφS, Submodule.mem_bot] at this
    exact this
  · have key : ∀ x : V n, dp (fun i => φ (fun j => if i = j then 1 else 0)) x = φ x := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      unfold dp
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul, mul_comm]
    rw [key]
    exact eq_one_of_ne hφy


noncomputable def perp {n : ℕ} (S : Submodule (ZMod 2) (V n)) : Finset (V n) :=
  fs (fun w => ∀ s ∈ S, dp w s = 0)

lemma perp_closed {n : ℕ} (S : Submodule (ZMod 2) (V n)) :
    ∀ x ∈ perp S, ∀ y ∈ perp S, x + y ∈ perp S := by
  apply fs_closed
  intro x y hx hy s hs
  rw [add_dp, hx s hs, hy s hs, add_zero]

lemma zero_mem_perp {n : ℕ} (S : Submodule (ZMod 2) (V n)) : (0 : V n) ∈ perp S := by
  unfold perp; rw [mem_fs]; intro s _; exact dp_zero_left s

lemma perp_sum_in {n : ℕ} (S : Submodule (ZMod 2) (V n)) (y : V n) (hy : y ∈ S) :
    ∑ w ∈ perp S, sgn (dp w y) = (perp S).card := by
  apply char_sum_one
  intro w hw
  unfold perp at hw; rw [mem_fs] at hw
  exact hw y hy

lemma perp_sum_out {n : ℕ} (S : Submodule (ZMod 2) (V n)) (y : V n) (hy : y ∉ S) :
    ∑ w ∈ perp S, sgn (dp w y) = 0 := by
  obtain ⟨w0, hw0, h1⟩ := sep S y hy
  apply char_sum_zero (perp S) (perp_closed S) (fun w => dp w y)
    (fun x _ z _ => add_dp x z y) w0 _ h1
  unfold perp; rw [mem_fs]; exact hw0

noncomputable def W {n : ℕ} (f : V n → ZMod 2) (w : V n) : ℤ := ∑ x, sgn (f x + dp w x)

noncomputable def val {n : ℕ} (f : V n → ZMod 2) (a : V n) (S : Submodule (ZMod 2) (V n)) : ℤ :=
  ∑ x ∈ fs (fun x => x - a ∈ S), sgn (f x)

lemma fourier {n : ℕ} (f : V n → ZMod 2) (a : V n) (S : Submodule (ZMod 2) (V n)) :
    ∑ w ∈ perp S, sgn (dp w a) * W f w = (perp S).card * val f a S := by
  unfold W val
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ x : V n, ∑ w ∈ perp S, sgn (dp w a) * sgn (f x + dp w x)
      = sgn (f x) * ∑ w ∈ perp S, sgn (dp w (x - a)) := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [← sgn_add, ← sgn_add, dp_sub]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun x _ => e x)]
  rw [← Finset.sum_subset (Finset.subset_univ (fs (fun x => x - a ∈ S)))]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [mem_fs] at hx
    rw [perp_sum_in S _ hx]; ring
  · intro x _ hx
    rw [mem_fs] at hx
    rw [perp_sum_out S _ hx, mul_zero]

lemma val_shift {n : ℕ} (f : V n → ZMod 2) (a : V n) (S : Submodule (ZMod 2) (V n)) :
    val f a S = ∑ t ∈ fs (fun t => t ∈ S), sgn (f (a + t)) := by
  unfold val
  symm
  apply Finset.sum_nbij' (fun t => a + t) (fun x => x - a)
  · intro t ht; rw [mem_fs] at ht ⊢; simpa using ht
  · intro x hx; rw [mem_fs] at hx ⊢; exact hx
  · intro t _; simp
  · intro x _; simp
  · intro t _; rfl

lemma val_le {n : ℕ} (f : V n → ZMod 2) (K : ℤ) (hW : ∀ w, |W f w| ≤ K) (a : V n)
    (S : Submodule (ZMod 2) (V n)) : |val f a S| ≤ K := by
  have hc : (0 : ℤ) < (perp S).card := by
    exact_mod_cast Finset.card_pos.2 ⟨0, zero_mem_perp S⟩
  have h0 : ((perp S).card : ℤ) * |val f a S| = |∑ w ∈ perp S, sgn (dp w a) * W f w| := by
    rw [fourier, abs_mul, abs_of_pos hc]
  have h1 : ((perp S).card : ℤ) * |val f a S| ≤ (perp S).card * K := by
    rw [h0]
    calc |∑ w ∈ perp S, sgn (dp w a) * W f w| ≤ ∑ w ∈ perp S, |sgn (dp w a) * W f w| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ perp S, K :=
          Finset.sum_le_sum (fun w _ => by rw [abs_mul, abs_sgn, one_mul]; exact hW w)
      _ = (perp S).card * K := by rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_mul_le_mul_left h1 hc

lemma eq_case {n : ℕ} (f : V n → ZMod 2) (K : ℤ) (hK : 0 ≤ K) (hW : ∀ w, |W f w| ≤ K) (a : V n)
    (S : Submodule (ZMod 2) (V n)) (habs : |val f a S| = K) :
    ∀ w ∈ perp S, val f a S * (sgn (dp w a) * W f w) = K ^ 2 := by
  have hle : ∀ w ∈ perp S, val f a S * (sgn (dp w a) * W f w) ≤ K ^ 2 := by
    intro w _
    calc val f a S * (sgn (dp w a) * W f w) ≤ |val f a S * (sgn (dp w a) * W f w)| :=
          le_abs_self _
      _ = |val f a S| * |W f w| := by rw [abs_mul, abs_mul, abs_sgn, one_mul]
      _ ≤ K * K := by rw [habs]; exact mul_le_mul_of_nonneg_left (hW w) hK
      _ = K ^ 2 := by ring
  have hv2 : val f a S ^ 2 = K ^ 2 := by rw [← habs, sq_abs]
  have hsum : ∑ w ∈ perp S, (K ^ 2 - val f a S * (sgn (dp w a) * W f w)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, fourier, Finset.sum_const, nsmul_eq_mul]
    linear_combination (-((perp S).card : ℤ)) * hv2
  intro w hw
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun w hw => sub_nonneg.2 (hle w hw))).1 hsum w hw
  linarith

lemma zadd_self (c : ZMod 2) : c + c = 0 := by
  have key : ∀ d : ZMod 2, d + d = 0 := by decide
  exact key c

lemma Q_zero_left {n : ℕ} (f : V n → ZMod 2) (v : V n) : Q f 0 v = 0 := by
  unfold Q; rw [zero_add]; linear_combination (f v + f 0) * two_eq

lemma Q_zero_right {n : ℕ} (f : V n → ZMod 2) (v : V n) : Q f v 0 = 0 := by
  rw [Q_comm]; exact Q_zero_left f v

lemma natAbs_pow2 (v : ℤ) (h : v ^ 2 = 0 ∨ ∃ e : ℕ, v ^ 2 = 2 ^ e) :
    v = 0 ∨ ∃ i : ℕ, v.natAbs = 2 ^ i := by
  rcases h with h | ⟨e, he⟩
  · left; exact (pow_eq_zero_iff (by norm_num)).1 h
  · right
    have h1 : (v.natAbs : ℤ) ^ 2 = ((2 ^ e : ℕ) : ℤ) := by
      rw [Int.natAbs_sq]; push_cast; exact he
    have h2 : v.natAbs ^ 2 = 2 ^ e := by exact_mod_cast h1
    have h3 : v.natAbs ∣ 2 ^ e := ⟨v.natAbs, by rw [← h2]; ring⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    exact ⟨i, hi⟩

lemma chg_true {n : ℕ} (f : V n → ZMod 2) : chg f (fun _ => True) = W f 0 := by
  rw [chg_eq]
  have : fs (fun _ : V n => True) = univ := by
    ext x; simp [mem_fs]
  rw [this]
  unfold W
  apply Finset.sum_congr rfl
  intro x _
  rw [dp_zero_left, add_zero]

section quad
variable {n : ℕ} {f : V n → ZMod 2}
  (hf : ∀ p u v : V n, f (p+u+v)+f (p+u)+f (p+v)+f p = Q f u v)
include hf

lemma Q_add_left (x y s : V n) : Q f (x + y) s = Q f x s + Q f y s := by
  have h := hf x y s
  unfold Q at h ⊢
  linear_combination h + (-(f (x+s)) - f x) * two_eq

lemma Q_add_right (s x y : V n) : Q f s (x + y) = Q f s x + Q f s y := by
  rw [Q_comm, Q_add_left hf, Q_comm f x, Q_comm f y]

omit hf in
lemma rad_sum_in (s : V n) (hs : ∀ v, Q f s v = 0) : ∑ x, sgn (Q f x s) = 2 ^ n := by
  rw [char_sum_one univ (fun x => Q f x s) (fun x _ => by rw [Q_comm]; exact hs x)]
  simp [V]

lemma rad_sum_out (s : V n) (hs : ¬ ∀ v, Q f s v = 0) : ∑ x, sgn (Q f x s) = 0 := by
  push Not at hs
  obtain ⟨v, hv⟩ := hs
  exact char_sum_zero univ (fun _ _ _ _ => mem_univ _) (fun x => Q f x s)
    (fun x _ y _ => Q_add_left hf x y s) v (mem_univ _) (by rw [Q_comm]; exact eq_one_of_ne hv)

lemma W_sq_le (w : V n) :
    W f w ^ 2 ≤ 2 ^ n * ((fs (fun u => ∀ v, Q f u v = 0)).card : ℤ) := by
  have e1 : W f w ^ 2 = ∑ x, ∑ s, sgn (Q f x s) * sgn (f s + f 0 + dp w s) := by
    unfold W
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← sum_shift univ (fun _ _ _ _ => mem_univ _) x (mem_univ _)
      (fun y => sgn (f x + dp w x) * sgn (f y + dp w y))]
    apply Finset.sum_congr rfl
    intro s _
    show sgn (f x + dp w x) * sgn (f (x + s) + dp w (x + s))
      = sgn (Q f x s) * sgn (f s + f 0 + dp w s)
    rw [← sgn_add, ← sgn_add, dp_add]
    congr 1
    have := f_shift f x s
    linear_combination this + (dp w x) * two_eq
  have e2 : ∑ x, ∑ s, sgn (Q f x s) * sgn (f s + f 0 + dp w s)
      = ∑ s, sgn (f s + f 0 + dp w s) * ∑ x, sgn (Q f x s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have e3 : ∑ s, sgn (f s + f 0 + dp w s) * ∑ x, sgn (Q f x s)
      = ∑ s ∈ fs (fun u => ∀ v, Q f u v = 0), sgn (f s + f 0 + dp w s) * 2 ^ n := by
    rw [← Finset.sum_subset (Finset.subset_univ (fs (fun u => ∀ v, Q f u v = 0)))]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [mem_fs] at hs
      rw [rad_sum_in s hs]
    · intro s _ hs
      rw [mem_fs] at hs
      rw [rad_sum_out hf s hs, mul_zero]
  rw [e1, e2, e3]
  calc ∑ s ∈ fs (fun u => ∀ v, Q f u v = 0), sgn (f s + f 0 + dp w s) * 2 ^ n
      ≤ ∑ s ∈ fs (fun u => ∀ v, Q f u v = 0), (2 : ℤ) ^ n := by
        apply Finset.sum_le_sum
        intro s _
        have := sgn_le_one (f s + f 0 + dp w s)
        have h2 : (0 : ℤ) < 2 ^ n := by positivity
        nlinarith
    _ = 2 ^ n * ((fs (fun u => ∀ v, Q f u v = 0)).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma val_sq (a : V n) (S : Submodule (ZMod 2) (V n)) :
    val f a S ^ 2 = 0 ∨ val f a S ^ 2 = ((fs (fun t => t ∈ S)).card : ℤ) *
      (fs (fun s => s ∈ S ∧ ∀ t ∈ S, Q f t s = 0)).card := by
  set SS := fs (fun t => t ∈ S) with hSS
  set RS := fs (fun s => s ∈ S ∧ ∀ t ∈ S, Q f t s = 0) with hRS
  have SSc : ∀ x ∈ SS, ∀ y ∈ SS, x + y ∈ SS := fs_closed _ (fun x y hx hy => S.add_mem hx hy)
  have RSc : ∀ x ∈ RS, ∀ y ∈ RS, x + y ∈ RS := by
    apply fs_closed
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨S.add_mem hx hy, fun t ht => ?_⟩
    rw [Q_add_right hf, hx' t ht, hy' t ht, add_zero]
  have e1 : val f a S ^ 2
      = ∑ t ∈ SS, ∑ s ∈ SS, sgn (Q f t s) * sgn (f s + f 0 + Q f a s) := by
    rw [val_shift, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← sum_shift SS SSc t ht (fun y => sgn (f (a + t)) * sgn (f (a + y)))]
    apply Finset.sum_congr rfl
    intro s _
    show sgn (f (a + t)) * sgn (f (a + (t + s))) = sgn (Q f t s) * sgn (f s + f 0 + Q f a s)
    rw [← sgn_add, ← sgn_add]
    congr 1
    have h1 := f_shift f (a + t) s
    have h2 := Q_add_left hf a t s
    rw [← add_assoc a t s]
    linear_combination h1 + h2
  have e2 : ∑ t ∈ SS, ∑ s ∈ SS, sgn (Q f t s) * sgn (f s + f 0 + Q f a s)
      = ∑ s ∈ SS, sgn (f s + f 0 + Q f a s) * ∑ t ∈ SS, sgn (Q f t s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hsub : RS ⊆ SS := by
    intro x hx
    rw [hRS, mem_fs] at hx
    rw [hSS, mem_fs]
    exact hx.1
  have e3 : ∑ s ∈ SS, sgn (f s + f 0 + Q f a s) * ∑ t ∈ SS, sgn (Q f t s)
      = ∑ s ∈ RS, sgn (f s + f 0 + Q f a s) * SS.card := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [hRS, mem_fs] at hs
      rw [char_sum_one SS (fun t => Q f t s)
        (fun t ht => hs.2 t (by rw [hSS, mem_fs] at ht; exact ht))]
    · intro s hs hs'
      have hsS : s ∈ S := by rw [hSS, mem_fs] at hs; exact hs
      have hn : ¬ ∀ t ∈ S, Q f t s = 0 := fun h => hs' (by rw [hRS, mem_fs]; exact ⟨hsS, h⟩)
      push Not at hn
      obtain ⟨t0, ht0, hq⟩ := hn
      rw [char_sum_zero SS SSc (fun t => Q f t s) (fun x _ y _ => Q_add_left hf x y s) t0
        (by rw [hSS, mem_fs]; exact ht0) (eq_one_of_ne hq), mul_zero]
  have e4 : ∑ s ∈ RS, sgn (f s + f 0 + Q f a s) = 0 ∨
      ∑ s ∈ RS, sgn (f s + f 0 + Q f a s) = RS.card := by
    by_cases h : ∀ s ∈ RS, f s + f 0 + Q f a s = 0
    · right; exact char_sum_one RS (fun s => f s + f 0 + Q f a s) h
    · left
      push Not at h
      obtain ⟨s0, hs0, h1⟩ := h
      apply char_sum_zero RS RSc (fun s => f s + f 0 + Q f a s) _ s0 hs0 (eq_one_of_ne h1)
      intro x hx y hy
      rw [hRS, mem_fs] at hx hy
      have hq : Q f x y = 0 := hy.2 x hx.1
      show f (x+y) + f 0 + Q f a (x+y) = (f x + f 0 + Q f a x) + (f y + f 0 + Q f a y)
      rw [Q_add_right hf]
      unfold Q at hq
      linear_combination hq + (-(f x) - f y - f 0) * two_eq
  rw [e1, e2, e3, ← Finset.sum_mul]
  rcases e4 with h | h
  · left; rw [h]; ring
  · right; rw [h]; ring

lemma val_sq' (a : V n) (S : Submodule (ZMod 2) (V n)) :
    val f a S ^ 2 = 0 ∨ ∃ e : ℕ, val f a S ^ 2 = 2 ^ e := by
  rcases val_sq hf a S with h | h
  · left; exact h
  · right
    obtain ⟨j, hj⟩ := card_fs_pow2 (fun t => t ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy)
    obtain ⟨k, hk⟩ := card_fs_pow2 (fun s => s ∈ S ∧ ∀ t ∈ S, Q f t s = 0)
      ⟨S.zero_mem, fun t _ => Q_zero_right f t⟩
      (fun x y hx hy => ⟨S.add_mem hx.1 hy.1, fun t ht => by
        rw [Q_add_right hf, hx.2 t ht, hy.2 t ht, add_zero]⟩)
    exact ⟨j + k, by rw [h, hj, hk, pow_add]⟩

lemma P1 (c : ℕ) (hW : ∀ w, |W f w| ≤ 2 ^ c) (a : V n) (S : Submodule (ZMod 2) (V n))
    (hv : 2 ^ c < 2 * (val f a S).natAbs) : (val f a S).natAbs = 2 ^ c := by
  have hle := val_le f (2 ^ c) hW a S
  have hle' : (val f a S).natAbs ≤ 2 ^ c := by
    have h2 : ((val f a S).natAbs : ℤ) ≤ 2 ^ c := by rw [Int.natCast_natAbs]; exact hle
    exact_mod_cast h2
  rcases natAbs_pow2 _ (val_sq' hf a S) with h0 | ⟨i, hi⟩
  · rw [h0] at hv; simp at hv
  · rw [hi] at hv hle' ⊢
    have h1 : i ≤ c := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle'
    have h2 : c < i + 1 := by
      have : 2 ^ c < 2 ^ (i + 1) := by rw [pow_succ]; linarith
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
    congr 1; omega

end quad

theorem clean (n : ℕ) (f : V n → ZMod 2)
    (hf : ∀ p u v : V n, f (p+u+v)+f (p+u)+f (p+v)+f p = Q f u v) (a : V n)
    (S : Submodule (ZMod 2) (V n))
    (hv : 2 ^ (n - (n - (Nat.card {u : V n // ∀ v : V n, Q f u v = 0}).log2) / 2)
      < 2 * (chg f (fun x => x - a ∈ S)).natAbs) :
    (chg f (fun x => x - a ∈ S)).natAbs
      = 2 ^ (n - (n - (Nat.card {u : V n // ∀ v : V n, Q f u v = 0}).log2) / 2) ∧
    chg f (fun x => x - a ∈ S) = chg f (fun _ => True) ∧
    ∀ (b : V n) (T : Submodule (ZMod 2) (V n)),
      2 ^ (n - (n - (Nat.card {u : V n // ∀ v : V n, Q f u v = 0}).log2) / 2)
        < 2 * (chg f (fun x => x - b ∈ T)).natAbs →
      ∃ x : V n, x - a ∈ S ∧ x - b ∈ T := by
  obtain ⟨r0, hr0n, hr0⟩ := card_pow2 (fun u : V n => ∀ v, Q f u v = 0)
    (fun v => Q_zero_left f v)
    (fun x y hx hy v => by rw [Q_add_left hf, hx v, hy v, add_zero])
  rw [hr0, Nat.log2_two_pow] at hv ⊢
  set c := n - (n - r0) / 2 with hc
  have hW : ∀ w, |W f w| ≤ (2:ℤ) ^ c := by
    intro w
    have h1 := W_sq_le hf w
    rw [card_fs, hr0] at h1
    have h2 : (2:ℤ) ^ n * ((2 ^ r0 : ℕ) : ℤ) ≤ ((2:ℤ) ^ c) ^ 2 := by
      push_cast
      rw [← pow_add, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : (0:ℤ) < 2 ^ c := by positivity
    rw [abs_le]; constructor <;> nlinarith
  have hP : ∀ (b : V n) (T : Submodule (ZMod 2) (V n)),
      2 ^ c < 2 * (val f b T).natAbs →
      (val f b T).natAbs = 2 ^ c ∧ val f b T = W f 0 ∧ |val f b T| = 2 ^ c := by
    intro b T hb
    have h1 := P1 hf c hW b T hb
    have habs : |val f b T| = 2 ^ c := by
      rw [← Int.natCast_natAbs, h1]; push_cast; ring
    refine ⟨h1, ?_, habs⟩
    have E := eq_case f (2 ^ c) (by positivity) hW b T habs 0 (zero_mem_perp T)
    rw [dp_zero_left, sgn_zero, one_mul] at E
    have hv2 : val f b T ^ 2 = (2 ^ c) ^ 2 := by rw [← habs, sq_abs]
    have hne : val f b T ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at habs
      have : (0:ℤ) < 2 ^ c := by positivity
      linarith
    have : val f b T * (W f 0 - val f b T) = 0 := by linear_combination E - hv2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hne
    · linarith
  rw [chg_eq] at hv
  rw [chg_eq, chg_true]
  change 2 ^ c < 2 * (val f a S).natAbs at hv
  obtain ⟨hA1, hA2, hA3⟩ := hP a S hv
  refine ⟨hA1, hA2, ?_⟩
  intro b T hvb
  rw [chg_eq] at hvb
  change 2 ^ c < 2 * (val f b T).natAbs at hvb
  obtain ⟨hB1, hB2, hB3⟩ := hP b T hvb
  have hab : val f a S = val f b T := by rw [hA2, hB2]
  have Ea := eq_case f (2 ^ c) (by positivity) hW a S hA3
  have Eb := eq_case f (2 ^ c) (by positivity) hW b T hB3
  have hdp : ∀ w ∈ perp S, w ∈ perp T → dp w (a - b) = 0 := by
    intro w hwS hwT
    have e1 := Ea w hwS
    have e2 := Eb w hwT
    rw [← hab] at e2
    have hne : val f a S * W f w ≠ 0 := by
      intro h0
      have h00 : val f a S * (sgn (dp w a) * W f w) = 0 := by
        rw [mul_left_comm, h0, mul_zero]
      rw [h00] at e1
      have : (0:ℤ) < (2 ^ c) ^ 2 := by positivity
      linarith
    have h3 : (sgn (dp w a) - sgn (dp w b)) * (val f a S * W f w) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.1 h3 with h | h
    · have := sgn_inj (sub_eq_zero.1 h)
      rw [dp_sub, this]; exact zadd_self _
    · exact absurd h hne
  by_contra hno
  push Not at hno
  have hnot : a - b ∉ S ⊔ T := by
    intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    apply hno (a - y) (by rw [sub_sub_cancel_left]; exact S.neg_mem hy)
    have : a - y - b = z := by
      calc a - y - b = (a - b) - y := by abel
        _ = (y + z) - y := by rw [hyz]
        _ = z := by abel
    rw [this]; exact hz
  obtain ⟨w, hw, hw1⟩ := sep (S ⊔ T) (a - b) hnot
  have hwS : w ∈ perp S := by
    unfold perp; rw [mem_fs]; intro s hs; exact hw s (Submodule.mem_sup_left hs)
  have hwT : w ∈ perp T := by
    unfold perp; rw [mem_fs]; intro s hs; exact hw s (Submodule.mem_sup_right hs)
  rw [hdp w hwS hwT] at hw1
  exact absurd hw1 (by decide)

end PEqualNP.Outside.L_pcx_450_aux

theorem PEqualNP.Outside.L_pcx_450 : (∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ f : X → F,
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
    let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let charge := fun (P : X → Prop) =>
      (Nat.card {x : X // P x ∧ f x=0} : ℤ) - (Nat.card {x : X // P x ∧ f x=1} : ℤ)
    let total := charge (fun _ => True)
    let value := fun (a : X) (S : Submodule F X) => charge (fun x => x-a ∈ S)
    let C := 2^(n-m)
    ∀ (a : X) (S : Submodule F X), C < 2*(value a S).natAbs →
      (value a S).natAbs=C ∧ value a S=total ∧
      ∀ (b : X) (T : Submodule F X), C < 2*(value b T).natAbs →
        ∃ x : X, x-a ∈ S ∧ x-b ∈ T) := by
  intro n F X f B hB m charge total value C a S hv
  exact PEqualNP.Outside.L_pcx_450_aux.clean n f hB a S hv
