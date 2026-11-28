import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.ByContra
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Sigma
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33671

namespace Tests33671
open scoped BigOperators

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

def reg {N : ℕ} (t : ℕ) (Q : Graph N) : Prop :=
  (∀ x, (Finset.univ.filter (fun y => Q x y)).card = t) ∧
  (∀ y, (Finset.univ.filter (fun x => Q x y)).card = t)

def bit (K : Type*) [Zero K] [One K] (b : Bool) : K := if b then 1 else 0

theorem bit_sum_card {α : Type*} [Fintype α] {K : Type*} [AddCommMonoidWithOne K] (b : α → Bool) :
    (∑ x, bit K (b x)) = (((Finset.univ.filter fun x => b x).card : ℕ) : K) := by
  classical
  unfold bit
  rw [← Finset.sum_filter (s := Finset.univ) (fun x => b x) (fun _ => (1 : K))]
  simp

theorem reg_relabel {N t : ℕ} (Q : Graph N) (h : reg t Q) (e f : Equiv.Perm (Fin N)) :
    reg t (fun x y => Q (e x) (f y)) := by
  constructor
  · intro x
    have hh := Equiv.sum_comp f (fun y => bit ℕ (Q (e x) y))
    simpa only [bit_sum_card, Nat.cast_id, h.1] using hh
  · intro y
    have hh := Equiv.sum_comp e (fun x => bit ℕ (Q x (f y)))
    simpa only [bit_sum_card, Nat.cast_id, h.2] using hh

def band {n : ℕ} (t : ℕ) : Graph (n+1) := fun x y => decide ((y-x).val < t)

theorem band_reg {n t : ℕ} (ht : t ≤ n+1) : reg t (@band n t) := by
  classical
  have ch : (Finset.univ.filter fun z : Fin (n+1) => z.val < t).card = t := by
    let e := Fin.castLEEmb ht
    have he : Finset.univ.filter (fun z : Fin (n+1) => z.val < t) = Finset.univ.map e := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h
        exact ⟨⟨z.val,h⟩, Fin.ext rfl⟩
      · rintro ⟨j, rfl⟩
        exact j.isLt
    rw [he, Finset.card_map]
    simp
  have hs : (∑ z : Fin (n+1), bit ℕ (decide (z.val < t))) = t := by
    simpa only [bit_sum_card, decide_eq_true_eq, Nat.cast_id] using ch
  constructor
  · intro x
    have hh := (Equiv.sum_comp (Equiv.subRight x) (fun z => bit ℕ (decide (z.val < t)))).trans hs
    change (∑ y, bit ℕ (band t x y)) = t at hh
    simpa only [bit_sum_card, Nat.cast_id] using hh
  · intro y
    have hh := (Equiv.sum_comp (Equiv.subLeft y) (fun z => bit ℕ (decide (z.val < t)))).trans hs
    change (∑ x, bit ℕ (band t x y)) = t at hh
    simpa only [bit_sum_card, Nat.cast_id] using hh

lemma band_zero_one {K : Type*} [Ring K] {n t : ℕ} (ht₀ : 0 < t) (ht : t < n+1)
    (y : Fin (n+1)) : bit K (band t 0 y) - bit K (band t 1 y) =
      (if y = 0 then 1 else 0) - (if y = (⟨t,ht⟩ : Fin (n+1)) then 1 else 0) := by
  have hn : 0 < n := by omega
  have h1 : (1 : Fin (n+1)).val = 1 := by cases n with | zero => omega | succ n => simp
  have hz : (⟨t,ht⟩ : Fin (n+1)) ≠ 0 := by
    intro h
    have e := congrArg Fin.val h
    change t = 0 at e
    omega
  have hv (h : y ≠ 0) : (y-1).val = y.val-1 := by
    rw [Fin.val_sub, h1]
    have hy : 0 < y.val := Fin.pos_iff_ne_zero.mpr h
    have h' : (n+1) - 1 + y.val = (n+1) + (y.val - 1) := by omega
    rw [h', Nat.add_mod_left, Nat.mod_eq_of_lt (show y.val - 1 < n+1 by omega)]
  by_cases h0 : y = 0
  · subst y
    have hh : (0 : Fin (n+1)) - 1 = Fin.last n := by apply Fin.ext; simp
    simp only [band, sub_zero, hh, Fin.val_zero, Fin.val_last, bit]
    simp [ht₀, show ¬ n < t by omega, Ne.symm hz]
  · have heq : y = (⟨t,ht⟩ : Fin (n+1)) ↔ y.val = t := by
      constructor
      · rintro rfl; rfl
      · exact fun h => Fin.ext h
    simp only [band, sub_zero, hv h0]
    by_cases h : y.val < t
    · simp [h0, h, show y.val - 1 < t by omega, show y.val ≠ t by omega, heq, bit]
    · by_cases he : y.val = t
      · simp [h0, he, Nat.ne_of_gt ht₀, heq, bit]
      · simp [h0, h, he, show ¬ y.val - 1 < t by omega, heq, bit]

lemma perm_two {α : Type*} [DecidableEq α] {a b u v : α} (hab : a ≠ b) (huv : u ≠ v) :
    ∃ e : Equiv.Perm α, e a = u ∧ e b = v := by
  let e := Equiv.swap a u
  have ea : e a = u := Equiv.swap_apply_left _ _
  have eb : e b ≠ u := by rw [← ea]; exact fun eq => hab (e.injective eq.symm)
  refine ⟨e.trans (Equiv.swap (e b) v), ?_, ?_⟩
  · change Equiv.swap (e b) v (e a) = u
    rw [ea, Equiv.swap_apply_of_ne_of_ne (Ne.symm eb) huv]
  · exact Equiv.swap_apply_left _ _

theorem checker {n t : ℕ} (ht₀ : 0 < t) (ht : t < n+1)
    {r₀ r₁ c₀ c₁ : Fin (n+1)} (hr : r₀ ≠ r₁) (hc : c₀ ≠ c₁) :
    ∃ B S : Graph (n+1), reg t B ∧ reg t S ∧
      ∀ (K : Type) [Ring K] (x y : Fin (n+1)), bit K (S x y) - bit K (B x y) =
        ((if x = r₁ then 1 else 0) - (if x = r₀ then 1 else 0)) *
        ((if y = c₀ then 1 else 0) - (if y = c₁ then 1 else 0)) := by
  classical
  have hn : 0 < n := by omega
  have hzero₁ : (0 : Fin (n+1)) ≠ 1 := by
    intro h
    have e := congrArg Fin.val h
    cases n with | zero => omega | succ n => simp at e
  have hzero_t : (0 : Fin (n+1)) ≠ ⟨t,ht⟩ := by
    intro h; have e := congrArg Fin.val h; change 0=t at e; omega
  obtain ⟨e,e₀,e₁⟩ := perm_two hr hzero₁
  obtain ⟨f,f₀,f₁⟩ := perm_two hc hzero_t
  let B : Graph (n+1) := fun x y => band t (e x) (f y)
  let S : Graph (n+1) := fun x y => B (Equiv.swap r₀ r₁ x) y
  have hB : reg t B := reg_relabel _ (band_reg ht.le) e f
  refine ⟨B,S,hB,reg_relabel B hB (Equiv.swap r₀ r₁) (Equiv.refl _), ?_⟩
  intro K _ x y
  have e0 : f y = 0 ↔ y = c₀ := by rw [← f₀, f.injective.eq_iff]
  have e1 : f y = (⟨t,ht⟩ : Fin (n+1)) ↔ y = c₁ := by rw [← f₁, f.injective.eq_iff]
  have hd := band_zero_one (K := K) ht₀ ht (f y)
  rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl] at hd
  by_cases h₀ : x = r₀
  · subst x
    simp only [S, B, Equiv.swap_apply_left, e₀, e₁, hr, ↓reduceIte, zero_sub, neg_mul, one_mul]
    rw [← hd, neg_sub]
  · by_cases h₁ : x = r₁
    · subst x
      simp [S, B, e₀, e₁, Ne.symm hr, hd]
    · simp [S, h₀, h₁, Equiv.swap_apply_of_ne_of_ne]

end Tests33671

namespace Tests33671
open scoped BigOperators

theorem bounded_flow {n : ℕ} (d : Fin (n+1) → ℝ)
    (hd : ∑ j, d j = 0) {B : ℝ} (hB : ∑ j, max (d j) 0 ≤ B) :
    ∃ f : Fin (n+1) → ℝ, (∀ j, 0 ≤ f j ∧ f j ≤ B) ∧
      ∀ j, f j - f (j - 1) = d j := by
  classical
  let p (j : Fin (n+1)) := ∑ k ∈ Finset.univ.filter (· ≤ j), d k
  obtain ⟨a, _, amin⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
  refine ⟨fun j => p j - p a, ?_, ?_⟩
  · intro j
    have hmin : p a ≤ p j := amin j (Finset.mem_univ _)
    refine ⟨sub_nonneg.mpr hmin, ?_⟩
    let U (k : Fin (n+1)) := Finset.univ.filter (· ≤ k)
    have aux (v w : Fin (n+1)) (h : w ≤ v) : p v - p w = ∑ k ∈ U v \ U w, d k := by
      have hsub : U w ⊆ U v := by
        intro x hx
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans h
      have hh := Finset.sum_sdiff (f := d) hsub
      change _ + p w = p v at hh
      linarith
    have bnd (S : Finset (Fin (n+1))) : ∑ k ∈ S, d k ≤ B :=
      (Finset.sum_le_sum fun k _ => le_max_left (d k) 0).trans
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ =>
          le_max_right (d k) 0).trans hB)
    change p j - p a ≤ B
    by_cases h : a ≤ j
    · rw [aux _ _ h]
      exact bnd _
    · have hj := (le_of_not_ge h : j ≤ a)
      have h' := aux a j hj
      have hc := Finset.sum_sdiff (f := d) (Finset.subset_univ (U a \ U j))
      rw [hd, ← h'] at hc
      linarith [bnd (Finset.univ \ (U a \ U j))]
  · intro j
    by_cases h0 : j = 0
    · subst j
      have hp : p (0 : Fin (n+1)) = d 0 := by
        have hh : Finset.univ.filter (fun k : Fin (n+1) => k ≤ 0) = {0} := by
          ext k
          simp
        dsimp [p]
        rw [hh, Finset.sum_singleton]
      have hm : (0 : Fin (n+1)) - 1 = Fin.last n := by
        apply Fin.ext
        simp
      have hlast : p (Fin.last n) = 0 := by
        simpa [p, Fin.le_last] using hd
      change p 0 - p a - (p (0-1) - p a) = d 0
      rw [hm, hp, hlast]
      ring
    · have hv : (j - 1).val + 1 = j.val := by
        simp [Fin.val_sub]
        have hj : 0 < j.val := Fin.pos_iff_ne_zero.mpr h0
        have hn : 0 < n := by omega
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
        have h : n+1-(1:ℕ)+j.val = n+1+(j.val-1) := by omega
        rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (show j.val - 1 < n+1 by omega)]
        omega
      have hh : Finset.univ.filter (fun k : Fin (n+1) => k ≤ j) =
          insert j (Finset.univ.filter fun k : Fin (n+1) => k ≤ j-1) := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hk
          by_cases hkj : k = j
          · exact Or.inl hkj
          · right
            have hne : k.val ≠ j.val := fun x => hkj (Fin.ext x)
            omega
        · rintro (rfl|hk)
          · omega
          · omega
      have hnot : j ∉ Finset.univ.filter (fun k : Fin (n+1) => k ≤ j-1) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have he : p j = d j + p (j-1) := by
        conv_lhs => unfold p; rw [hh, Finset.sum_insert hnot]
      linarith

end Tests33671

namespace Tests33671
open scoped BigOperators

abbrev Matrix (n : ℕ) := Fin (n+1) → Fin (n+1) → ℝ

def box {n : ℕ} (i : Fin n) (k x y : Fin (n+1)) : ℝ :=
  ((if x = i.succ then 1 else 0) - (if x = 0 then 1 else 0)) *
    ((if y = k then 1 else 0) - (if y = k+1 then 1 else 0))

theorem flow_columns {n : ℕ} (f : Fin (n+1) → ℝ) (y : Fin (n+1)) :
    (∑ k, f k * ((if y = k then 1 else 0) - (if y = k+1 then 1 else 0))) =
       f y - f (y-1) := by
  have replace (k : Fin (n+1)) : y = k+1 ↔ y-1 = k := by
    constructor
    · rintro rfl
      exact add_sub_cancel_right k 1
    · intro h
      rw [← h, sub_add_cancel]
  simp_rw [mul_sub, Finset.sum_sub_distrib, replace, mul_ite, mul_one, mul_zero]
  simp [eq_comm]

theorem flow_expansion {n : ℕ} (H : Matrix n) (f : Fin n → Fin (n+1) → ℝ)
    (hcol : ∀ y, ∑ x, H x y = 0)
    (hf : ∀ i y, f i y - f i (y-1) = H i.succ y) :
    ∀ x y, H x y = ∑ i, ∑ k, f i k * box i k x y := by
  intro x y
  have sums (i : Fin n) : (∑ k, f i k * box i k x y) =
      ((if x = i.succ then 1 else 0) - (if x = 0 then 1 else 0)) * H i.succ y := by
    rw [← hf, ← flow_columns, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold box
    ring
  simp_rw [sums]
  refine Fin.cases ?_ (fun j => ?_) x
  · have hs := hcol y
    rw [Fin.sum_univ_succ] at hs
    simp only [Ne.symm (Fin.succ_ne_zero _), ↓reduceIte, zero_sub, neg_mul, one_mul, Finset.sum_neg_distrib]
    linarith
  · simp only [Fin.succ_ne_zero, ↓reduceIte, Fin.succ_inj, sub_zero, ite_mul, one_mul, zero_mul]
    simp

def dot {n : ℕ} (W Q : Matrix n) : ℝ := ∑ x, ∑ y, W x y * Q x y

def aff {n : ℕ} (C : ℝ) (W Q : Matrix n) : ℝ := C + dot W Q

theorem aff_expand {n : ℕ} (C : ℝ) (W Q J : Matrix n)
    (B S : Fin n → Fin (n+1) → Matrix n) (f : Fin n → Fin (n+1) → ℝ)
    (hQS : ∀ x y, Q x y - J x y = ∑ i, ∑ k, f i k * (S i k x y - B i k x y)) :
    aff C W Q = aff C W J + ∑ i, ∑ k, f i k * (aff C W (S i k) - aff C W (B i k)) := by
  have he : dot W Q - dot W J = ∑ i, ∑ k, f i k * (dot W (S i k) - dot W (B i k)) := by
    simp only [dot, ← Finset.sum_sub_distrib, ← mul_sub]
    simp_rw [hQS, Finset.mul_sum]
    have swap3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
        (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    let F (x y : Fin (n+1)) (i : Fin n) (k : Fin (n+1)) :=
      W x y * (f i k * (S i k x y - B i k x y))
    calc
      _ = ∑ x, ∑ i, ∑ k, ∑ y, F x y i k :=
        Finset.sum_congr rfl (fun x _ => swap3 (F x))
      _ = ∑ i, ∑ k, ∑ x, ∑ y, F x y i k :=
        swap3 (fun x i k => ∑ y, F x y i k)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        unfold F
        ring
  have ha (i : Fin n) (k : Fin (n+1)) : aff C W (S i k) - aff C W (B i k) =
      dot W (S i k) - dot W (B i k) := by unfold aff; ring
  simpa [ha, aff, sub_eq_iff_eq_add', add_comm, add_left_comm, add_assoc] using he

theorem affine_certificate {n : ℕ} (C V h b : ℝ) (W Q J : Matrix n)
    (B S : Fin n → Fin (n+1) → Matrix n) (f : Fin n → Fin (n+1) → ℝ)
    (hf : ∀ i k, 0 ≤ f i k ∧ f i k ≤ b)
    (hQcol : ∀ y, ∑ x, (Q x y - J x y) = 0)
    (hQrow : ∀ i y, f i y - f i (y-1) = Q i.succ y - J i.succ y)
    (hbox : ∀ i k x y, S i k x y - B i k x y = box i k x y)
    (hmean : ∀ i x y, ∑ k, B i k x y = (n+1 : ℕ) * J x y)
    (hbase : ∀ i k, aff C W (B i k) ≤ V+h)
    (hswitch : ∀ i k, aff C W (S i k) ≤ V+h)
    (hV : V ≤ aff C W J) (hK : 1 ≤ (n : ℝ)*(n+1 : ℕ)*b) :
    aff C W J ≤ V+h ∧ aff C W Q ≤ V+((n : ℝ)*(n+1 : ℕ)*b)*h := by
  have hQS := flow_expansion (fun x y => Q x y - J x y) f hQcol hQrow
  simp_rw [← hbox] at hQS
  have exp := aff_expand C W Q J B S f hQS
  have mean (i : Fin n) : ∑ k, aff C W (B i k) = (n+1 : ℕ)*aff C W J := by
    have hdot : ∑ k, dot W (B i k) = (n+1 : ℕ)*dot W J := by
      unfold dot
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, hmean]
      ring
    simp [aff, Finset.sum_add_distrib, hdot, mul_add]
  have hn : 0 < n := by
    by_contra! hh
    have e : n = 0 := by omega
    norm_num [e] at hK
  have hmean_upper : aff C W J ≤ V+h := by
    let i : Fin n := ⟨0,hn⟩
    have hm := Finset.sum_le_sum (s := Finset.univ) fun k _ => hbase i k
    rw [mean] at hm
    have hh : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    apply (mul_le_mul_iff_left₀ hh).mp
    rw [mul_comm (aff C W J), mul_comm (V+h)]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hm
  refine ⟨hmean_upper, ?_⟩
  have rowBound (i : Fin n) : (∑ k, f i k * (aff C W (S i k) - aff C W (B i k))) ≤
      b * ((n+1 : ℕ) * (V+h-aff C W J)) := by
    calc
      _ ≤ ∑ k, b * (V+h-aff C W (B i k)) := by
        apply Finset.sum_le_sum
        intro k _
        exact (mul_le_mul_of_nonneg_left (sub_le_sub_right (hswitch i k) _) (hf i k).1).trans
          (mul_le_mul_of_nonneg_right (hf i k).2 (sub_nonneg.mpr (hbase i k)))
      _ = _ := by
         rw [← Finset.mul_sum, Finset.sum_sub_distrib, mean]
         simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
         ring
  have hb := Finset.sum_le_sum (s := Finset.univ) fun i _ => rowBound i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hk := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hV)
  linarith only [exp, hb, hk]

end Tests33671

namespace Tests33671
open scoped BigOperators

noncomputable def density (n t : ℕ) : ℝ := (t : ℝ) / (n+1 : ℕ)

def inc {n : ℕ} (Q : Graph (n+1)) : Matrix n := fun x y => bit ℝ (Q x y)

theorem reg_rows {n t : ℕ} {Q : Graph (n+1)} (hQ : reg t Q) (x : Fin (n+1)) :
    (∑ y, inc Q x y) = t := by
  simp [inc, bit_sum_card, hQ.1]

theorem reg_cols {n t : ℕ} {Q : Graph (n+1)} (hQ : reg t Q) (y : Fin (n+1)) :
    (∑ x, inc Q x y) = t := by
  simp [inc, bit_sum_card, hQ.2]

theorem density_scale (n t : ℕ) : ((n+1 : ℕ) : ℝ) * density n t = t := by
  unfold density
  have h : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ h]

theorem regular_tests {n t : ℕ} (ht₀ : 0 < t) (ht : t < n+1) :
    ∃ test : Fin (2*(n+1)*n) → Graph (n+1), (∀ j, reg t (test j)) ∧
      ∀ (C V h : ℝ) (W : Matrix n),
        let J : Matrix n := fun _ _ => density n t
        V ≤ aff C W J → (∀ j, aff C W (inc (test j)) ≤ V+h) →
        aff C W J ≤ V+h ∧ ∀ T, reg t T →
          aff C W (inc T) ≤ V+((n*t*(n+1-t) : ℕ) : ℝ)*h := by
  classical
  have hn : 0 < n := by omega
  have h₁ : (0 : Fin (n+1)) ≠ 1 := by
    intro h
    have e := congrArg Fin.val h
    cases n with | zero => omega | succ n => simp at e
  choose B S hB hS hs using fun i : Fin n => checker ht₀ ht (Ne.symm (Fin.succ_ne_zero i)) h₁
  let K := (Fin n × Fin (n+1)) × Bool
  let e : Fin (2*(n+1)*n) ≃ K := Fintype.equivOfCardEq (by
    simp [K, Fintype.card_prod]; ring)
  let testK : K → Graph (n+1) := fun ((i,k),s) x y => (if s then S i else B i) x (y-k)
  have testKreg (j : K) : reg t (testK j) := by
    rcases j with ⟨⟨i,k⟩,b⟩
    cases b
    · exact reg_relabel _ (hB i) (Equiv.refl _) (Equiv.subRight k)
    · exact reg_relabel _ (hS i) (Equiv.refl _) (Equiv.subRight k)
  refine ⟨testK ∘ e, fun j => testKreg (e j), ?_⟩
  intro C V h W J hV htest
  have htestK (j : K) : aff C W (inc (testK j)) ≤ V+h := by
    have hh := htest (e.symm j)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh
  let B' (i : Fin n) (k : Fin (n+1)) := inc (testK ((i,k),false))
  let S' (i : Fin n) (k : Fin (n+1)) := inc (testK ((i,k),true))
  have hbox (i : Fin n) (k x y : Fin (n+1)) : S' i k x y - B' i k x y = box i k x y := by
    have eq₀ : y-k = 0 ↔ y = k := sub_eq_zero
    have eq₁ : y-k = 1 ↔ y = k+1 := by rw [sub_eq_iff_eq_add, add_comm (1 : Fin (n+1)) k]
    simpa only [B', S', inc, testK, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true, box, eq₀, eq₁] using hs i ℝ x (y-k)
  have hmean (i : Fin n) (x y : Fin (n+1)) : ∑ k, B' i k x y = (n+1 : ℕ) * J x y := by
    dsimp [J]
    rw [density_scale]
    exact (Equiv.sum_comp (Equiv.subLeft y) (inc (B i) x)).trans (reg_rows (hB i) x)
  let b : ℝ := (t : ℝ) * (1-density n t)
  have he : (n : ℝ)*(n+1 : ℕ)*b = ((n*t*(n+1-t) : ℕ) : ℝ) := by
    have hs := density_scale n t
    have hh : t ≤ n+1 := ht.le
    push_cast [Nat.cast_sub hh] at hs ⊢
    dsimp [b]
    linear_combination -(n : ℝ)*t * hs
  have hK : 1 ≤ (n : ℝ)*(n+1 : ℕ)*b := by
    rw [he]
    exact_mod_cast (show 1 ≤ n*t*(n+1-t) from Nat.succ_le_of_lt
      (Nat.mul_pos (Nat.mul_pos hn ht₀) (Nat.sub_pos_of_lt ht)))
  have cert (T : Graph (n+1)) (hT : reg t T) :
      aff C W J ≤ V+h ∧ aff C W (inc T) ≤ V+((n*t*(n+1-t) : ℕ) : ℝ)*h := by
    let d (i : Fin n) (y : Fin (n+1)) : ℝ := inc T i.succ y - density n t
    have dsum (i : Fin n) : ∑ y, d i y = 0 := by
      simp only [d, Finset.sum_sub_distrib, reg_rows hT, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, density_scale, sub_self]
    have hcol (y : Fin (n+1)) : ∑ x, (inc T x y - J x y) = 0 := by
      simp only [J, Finset.sum_sub_distrib, reg_cols hT, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, density_scale, sub_self]
    have variation (i : Fin n) : ∑ y, max (d i y) 0 ≤ b := by
      have hn : 0 < (((n+1 : ℕ) : ℝ)) := by positivity
      have h0 : 0 ≤ density n t := by unfold density; positivity
      have h1 : density n t ≤ 1 := (div_le_one hn).2 (by exact_mod_cast ht.le)
      have hpt (y : Fin (n+1)) : max (d i y) 0 = inc T i.succ y * (1-density n t) := by
        cases h : T i.succ y
        · simp [d, inc, h, bit, h0]
        · simp [d, inc, h, bit, h1]
      rw [Finset.sum_congr rfl (fun y _ => hpt y), ← Finset.sum_mul, reg_rows hT]
    choose f hf hd using fun i => bounded_flow (d i) (dsum i) (variation i)
    have hcf := affine_certificate C V h b W (inc T) J B' S' f hf hcol hd hbox hmean
      (fun i k => htestK ((i,k),false)) (fun i k => htestK ((i,k),true)) hV hK
    simpa only [he] using hcf
  exact ⟨(cert (band t) (band_reg ht.le)).1, fun T hT => (cert T hT).2⟩

end Tests33671

namespace Tests33671
open scoped BigOperators

def area {N : ℕ} (P : Graph N) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z.1 z.2)).card

def loss {N : ℕ} (P Q : Graph N) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z.1 z.2 ≠ Q z.1 z.2)).card

def slope {n : ℕ} (P : Graph (n+1)) : Matrix n := fun x y => 1-2*inc P x y

theorem area_as_sum {n : ℕ} (P : Graph (n+1)) :
    (area P : ℝ) = ∑ x, ∑ y, inc P x y := by
  simp only [area, ← bit_sum_card (fun z : Fin (n+1) × Fin (n+1) => P z.1 z.2),
    Fintype.sum_prod_type, inc]

theorem loss_aff {n : ℕ} (P Q : Graph (n+1)) :
    (loss P Q : ℝ) = aff (area P) (slope P) (inc Q) := by
  classical
  have hc := bit_sum_card (K := ℝ) (fun z : Fin (n+1) × Fin (n+1) => decide (P z.1 z.2 ≠ Q z.1 z.2))
  simp only [decide_eq_true_eq, Fintype.sum_prod_type] at hc
  rw [loss, ← hc, aff, dot, area_as_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  cases hP : P x y <;> cases hQ : Q x y <;> norm_num [inc, slope, hP, hQ, bit]

theorem aff_mix {n M : ℕ} (D : Fin M → Graph (n+1)) (w : Fin M → ℝ) (R : Matrix n) :
    aff (∑ i, w i * area (D i)) (fun x y => ∑ i, w i * slope (D i) x y) R =
      ∑ i, w i * aff (area (D i)) (slope (D i)) R := by
  have hd : dot (fun x y => ∑ i, w i * slope (D i) x y) R =
      ∑ i, w i * dot (slope (D i)) R := by
    unfold dot
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [aff, hd, mul_add, Finset.sum_add_distrib]

theorem center_loss {n t : ℕ} (hn : n+1 ≤ 2*t) (P : Graph (n+1)) :
    aff (area P) (slope P) (fun _ _ => density n t) =
      ((((n+1)*t : ℕ)) : ℝ) - ((2*t-(n+1) : ℕ) : ℝ) * area P / (n+1 : ℕ) := by
  have hr : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj := density_scale n t
  have hd : dot (slope P) (fun _ _ => density n t) =
      (n+1 : ℕ) * t - 2*density n t*area P := by
    unfold dot
    have step (x y) : slope P x y * density n t = density n t - (2*density n t)*inc P x y := by
      unfold slope
      ring
    simp_rw [step, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [density_scale, ← area_as_sum]
  unfold aff
  rw [hd]
  push_cast [Nat.cast_sub hn] at hj ⊢
  unfold density at *
  push_cast at hr ⊢
  field_simp
  ring

theorem tests_upper {N t : ℕ} (hhalf : N < 2*t) (ht : t < N) :
    ∃ test : Fin (2*N*(N-1)) → Graph N, (∀ j, reg t (test j)) ∧
      ∀ (A gap M : ℕ) (D : Fin M → Graph N) (lines : Fin M → Prop) (w : Fin M → ℝ) (h : ℝ),
        (∀ i, area (D i) ≤ A ∧ 0 ≤ w i) →
        (∀ i, ¬ lines i → area (D i)+gap ≤ A) → (∑ i, w i) = 1 →
        let a := 2*t-N
        let V := ((N*t : ℕ) : ℝ) - (a : ℝ)*(A : ℝ)/(N : ℝ)
        let err := fun T => ∑ i, w i*(loss (D i) T : ℝ)
        (∀ j, err (test j) ≤ V+h) →
          (∀ T, reg t T → err T ≤ V+(((N-1)*t*(N-t) : ℕ) : ℝ)*h) ∧
          (a : ℝ)*(gap : ℝ)*
            (∑ i, @ite ℝ (lines i) (Classical.propDecidable _) 0 (w i)) ≤ (N : ℝ)*h := by
  classical
  have hN : N ≠ 0 := by omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hN : 0 < (((n+1 : ℕ) : ℝ)) := by positivity
  have ht₀ : 0 < t := by omega
  obtain ⟨test, htreg, htcert⟩ := regular_tests ht₀ ht
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
  refine ⟨test, htreg, ?_⟩
  intro A gap M D lines w h hD badArea hw htest
  let a := 2*t-(n+1)
  let V := ((((n+1)*t : ℕ)) : ℝ) - (a : ℝ)*A/(n+1 : ℕ)
  let err := fun T => ∑ i, w i*(loss (D i) T : ℝ)
  let U : ℝ := ∑ i, w i * area (D i)
  let W : Matrix n := fun x y => ∑ i, w i * slope (D i) x y
  let J : Matrix n := fun _ _ => density n t
  let NT : ℝ := (((n+1)*t : ℕ) : ℝ)
  have hC : aff U W J = NT - (a : ℝ)*U/(n+1 : ℕ) := by
    rw [aff_mix]
    simp_rw [J, center_loss hhalf.le]
    have step (i : Fin M) : w i * (NT - (a : ℝ)*area (D i)/(n+1 : ℕ)) =
        w i * NT - ((a : ℝ)/(n+1 : ℕ))*(w i*area (D i)) := by ring
    change (∑ i, w i * (NT - (a : ℝ)*area (D i)/(n+1 : ℕ))) = _
    simp_rw [step, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hw, one_mul]
    dsimp [U]
    ring
  have hAff (T : Graph (n+1)) : aff U W (inc T) = err T := by
    rw [aff_mix]
    simp_rw [← loss_aff]
    rfl
  let badW : ℝ := ∑ i, @ite ℝ (lines i) (Classical.propDecidable _) 0 (w i)
  have hbad (i : Fin M) : 0 ≤ @ite ℝ (lines i) (Classical.propDecidable _) 0 (w i) := by
    split <;> simp_all [(hD i).2]
  have hsum : U + (gap : ℝ)*badW ≤ A := by
    have hp (i : Fin M) : w i * (area (D i) : ℝ) + (gap : ℝ) *
        (@ite ℝ (lines i) (Classical.propDecidable _) 0 (w i)) ≤ w i * A := by
      by_cases hh : lines i
      · simp only [hh, ite_true, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hD i).1) (hD i).2
      · simp only [hh, ite_false]
        calc
          _ = w i * ((area (D i) : ℝ)+gap) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast badArea i hh) (hD i).2
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i
    simpa only [U, badW, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul] using hs
  have hU : U ≤ A := by
    have h0 : 0 ≤ badW := Finset.sum_nonneg (fun i _ => hbad i)
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ gap) h0]
  have hV : V ≤ aff U W J := by
    rw [hC]
    change NT - (a : ℝ)*A/(n+1 : ℕ) ≤ _
    exact sub_le_sub_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hU (by positivity)) hN.le) NT
  obtain ⟨hm, hT⟩ := htcert U V h W hV (fun j => by simpa only [hAff] using htest j)
  refine ⟨fun T hR => ?_, ?_⟩
  · simpa only [hAff] using hT T hR
  · change (a : ℝ)*(gap : ℝ)*badW ≤ _
    change aff U W J ≤ V+h at hm
    rw [hC] at hm
    change NT - (a : ℝ)*U/(n+1 : ℕ) ≤ NT - (a : ℝ)*A/(n+1 : ℕ)+h at hm
    have hmul : (a : ℝ)*U + (a : ℝ)*gap*badW ≤ (a : ℝ)*A := by
      simpa only [mul_add, mul_assoc] using mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ a by positivity)
    have hv : ((a : ℝ)*A - (a : ℝ)*U) / (n+1 : ℕ) ≤ h := by
      rw [sub_div]
      linarith
    have h' := (div_le_iff₀ hN).mp hv
    nlinarith

end Tests33671

namespace Rigidity

open PEqualNP.CircuitLowerBounds
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [ite_eq_left ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [ite_eq_right ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem dep (n : ℕ) (pre : List Gate) : (∀ g ∈ pre, g.inputs.length ≤ 2) →
    ∀ S : Finset ℕ, ∃ T : Finset ℕ, T.card ≤ (pre.filter (fun gate => decide (gate.inputs.length = 2))).length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro h2 S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ 2 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ 2 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ), (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ i ∈ g.inputs, i ∈ S1) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (W (pre ++ [g]) x).getD w false = (W (pre ++ [g]) y).getD w false := by
      intro T S1 hS1 hin hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [W_snoc, W_snoc]
      have hlx : (W pre x).length = n + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = n + pre.length := by rw [W_length, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        have hmap : (g.inputs.map fun i => (W pre x).getD i false)
            = (g.inputs.map fun i => (W pre y).getD i false) :=
          List.map_congr_left (fun i hi => hI2 i (hin (heq ▸ hw) i hi))
        rw [hmap]
      · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by rw [step_len]; omega)]
    by_cases hm : (n + pre.length) ∈ S
    · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
      refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
      · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_erase_of_mem hm
        have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
        simp only [List.filter_append, List.length_append]
        by_cases he : g.inputs.length = 2
        · simp [he]; omega
        · simp [he]; omega
      · intro w hw hne
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
      · intro _ i hi
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S (fun w hw _ => hw) (fun h => absurd h hm) hTv⟩
      simp only [List.filter_append, List.length_append]
      omega

theorem monoW {gs : List Gate} (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (W gs x).getD i false = true → (W gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton pre g ih =>
    have hpre := ih (fun g hg => hop g (by simp [hg]))
    have hg := hop g (by simp)
    intro i
    rw [W_snoc_getD, W_snoc_getD, ← hl]
    split
    · rcases hg with hgo | hgo
      · simp only [hgo, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        intro hp k hk
        exact hpre k (hp k hk)
      · simp only [hgo, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        rintro ⟨k, hk, hj⟩
        exact ⟨k, hk, hpre k hj⟩
    · exact hpre i

def input {n : ℕ} (x y : Option (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (x = some i)) ++
    List.ofFn (fun i : Fin n => decide (y = some i))

theorem input_some {n : ℕ} (x y : Fin n) :
    input (some x) (some y) = PEqualNP.Represents.oneEach x y := by
  simp only [input, PEqualNP.Represents.oneEach, Option.some.injEq, eq_comm]

@[simp] theorem input_length {n : ℕ} (x y : Option (Fin n)) : (input x y).length = n+n := by
  simp [input]

theorem input_read {n : ℕ} (x y : Option (Fin n)) (i : ℕ) :
    (input x y).getD i false =
      (decide (∃ a : Fin n, x = some a ∧ i = a.val) ||
      decide (∃ a : Fin n, y = some a ∧ i = n+a.val)) := by
  by_cases hi : i < n
  · rw [input, getD_app_lt _ _ _ (by simpa using hi), ofFn_getD _ _ hi]
    have hr : ¬ ∃ a : Fin n, y = some a ∧ i = n+a.val := by
      rintro ⟨a, _, ha⟩; omega
    simp only [hr, decide_false, Bool.or_false]
    congr 1
    exact propext ⟨fun h => ⟨⟨i, hi⟩, h, rfl⟩, fun ⟨a, h, ha⟩ => by
      have he : (⟨i, hi⟩ : Fin n) = a := Fin.ext ha
      rwa [he]⟩
  have hop : (input x y).getD i false = (List.ofFn (fun a : Fin n => decide (y = some a))).getD (i-n) false := by
    simp only [input, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show (List.ofFn fun a : Fin n => decide (x = some a)).length ≤ i by simpa using Nat.le_of_not_gt hi), List.length_ofFn]
  rw [hop]
  have hil : ¬ ∃ a : Fin n, x = some a ∧ i = a.val := by
    rintro ⟨a, _, ha⟩; omega
  simp only [hil, decide_false, Bool.false_or]
  by_cases hh : i-n < n
  · rw [ofFn_getD _ _ hh]
    congr 1
    exact propext ⟨fun h => ⟨⟨i-n, hh⟩, h, by change i = n + (i-n); omega⟩, fun ⟨a, h, ha⟩ => by
      have he : (⟨i-n, hh⟩ : Fin n) = a := Fin.ext (by simp; omega)
      rwa [he]⟩
  · rw [ofFn_getD_ge _ _ (by omega)]
    have hr : ¬ ∃ a : Fin n, y = some a ∧ i = n+a.val := by
      rintro ⟨a, _, ha⟩; omega
    simp [hr]

open Finset

def tabArea {N : ℕ} (G : Fin N → Fin N → Bool) : ℕ :=
  ((univ : Finset (Fin N × Fin N)).filter (fun z => G z.1 z.2)).card

def tabLines {N : ℕ} (G : Fin N → Fin N → Bool) (k : ℕ) : Prop :=
  ∃ R S : Finset (Fin N), R.card + S.card = k ∧
    ∀ x y, G x y = decide (x ∈ R ∨ y ∈ S)

def ort {N : ℕ} (F : Option (Fin N) → Option (Fin N) → Bool) :=
  fun x y => F (some x) (some y)

theorem area_cover {N : ℕ} (G : Fin N → Fin N → Bool)
    (R S U V : Finset (Fin N))
    (hc : ∀ x y, G x y = true → x ∈ R ∨ y ∈ S ∨ (x ∈ U ∧ y ∈ V)) :
    tabArea G ≤ (R.card + S.card)*N + U.card*V.card := by
  let P := ((R ×ˢ univ) ∪ (univ ×ˢ S)) ∪ (U ×ˢ V)
  have hsub : ((univ : Finset (Fin N × Fin N)).filter (fun z => G z.1 z.2)) ⊆ P := by
    intro z hz
    have hG := (mem_filter.mp hz).2
    have hh := hc z.1 z.2 hG
    simpa [P, or_assoc] using hh
  have h1 := card_union_le (R ×ˢ (univ : Finset (Fin N))) ((univ : Finset (Fin N)) ×ˢ S)
  have h2 := card_union_le ((R ×ˢ (univ : Finset (Fin N))) ∪ ((univ : Finset (Fin N)) ×ˢ S)) (U ×ˢ V)
  have h3 := card_le_card hsub
  simp only [card_product, card_univ, Fintype.card_fin] at h1 h2
  change tabArea G ≤ _ at h3
  dsimp [P] at h3
  rw [Nat.add_mul, Nat.mul_comm S.card N]
  exact by omega

theorem areaBaseline {N g d : ℕ} {F : Option (Fin N) → Option (Fin N) → Bool}
    (R S : Finset (Fin N)) (hsize : R.card + S.card ≤ g+1)
    (hN : 2*g+1 < N) (hd : 0 < d) (hcap : tabArea (ort F) ≤ (g+1)*N-d)
    (hR : ∀ x ∉ R, ∀ y, F (some x) y = F none y)
    (hS : ∀ y ∉ S, ∀ x, F x (some y) = F x none) : F none none = false := by
  by_contra hb
  have hb' : F none none = true := Bool.eq_true_of_not_eq_false hb
  have hsub : Rᶜ ×ˢ Sᶜ ⊆ ((univ : Finset (Fin N × Fin N)).filter (fun z => ort F z.1 z.2)) := by
    intro z hz
    obtain ⟨hr, hs⟩ := mem_product.mp hz
    simp only [mem_compl] at hr hs
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    change F (some z.1) (some z.2) = true
    rw [hR _ hr, hS _ hs, hb']
  have hcard := card_le_card hsub
  simp only [card_product, card_compl, Fintype.card_fin] at hcard
  have hr := card_le_univ R
  have hs := card_le_univ S
  simp only [Fintype.card_fin] at hr hs
  change _ ≤ tabArea (ort F) at hcard
  have hexpand : N*N ≤ (N-R.card)*(N-S.card) + (R.card+S.card)*N := by
    have hr1 : (N - R.card) * N + R.card * N = N*N := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hr]
    have hs1 : (N-R.card)*(N-S.card) + (N-R.card)*S.card = (N-R.card)*N := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hs]
    have hs2 : (N-R.card)*S.card ≤ S.card*N := by
      rw [Nat.mul_comm S.card N]
      exact Nat.mul_le_mul_right _ (Nat.sub_le ..)
    rw [Nat.add_mul]
    omega
  have hL : (g+1)*N + (R.card+S.card)*N ≤ N*N := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right N (by omega)
  have hP : 0 < (g+1)*N := Nat.mul_pos (by omega) (by omega)
  omega

theorem areaRigidity {N g d : ℕ} {F : Option (Fin N) → Option (Fin N) → Bool}
    (R S : Finset (Fin N)) (hsize : R.card + S.card ≤ g+1)
    (hN : 2*g+1 < N) (hd : 0 < d) (hcap : tabArea (ort F) ≤ (g+1)*N-d)
    (hR : ∀ x ∉ R, ∀ y, F (some x) y = F none y)
    (hS : ∀ y ∉ S, ∀ x, F x (some y) = F x none)
    (hm : R.card + S.card ≤ g ∨
      (∀ x y, (F (some x) none = true ∨ F none (some y) = true) → ort F x y = true)) :
    tabArea (ort F) ≤ g*N ∨ tabLines (ort F) (g+1) := by
  classical
  have hzero := areaBaseline R S hsize hN hd hcap hR hS
  have hsupp : ∀ x y, ort F x y = true → x ∈ R ∨ y ∈ S := by
    intro x y hh
    by_contra! h
    obtain ⟨hx,hy⟩ := h
    simp [ort, hR _ hx, hS _ hy, hzero] at hh
  by_cases hsmall : R.card + S.card ≤ g
  · left
    have hh := area_cover (ort F) R S ∅ ∅ (by simpa using hsupp)
    exact (by simpa using hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right N hsmall) 0))
  have heq : R.card + S.card = g+1 := by omega
  have hmono := hm.resolve_left hsmall
  let Rg := R.filter (fun x => F (some x) none)
  let Sg := S.filter (fun y => F none (some y))
  let Rb := R \ Rg
  let Sb := S \ Sg
  have hRpart : Rb.card + Rg.card = R.card := card_sdiff_add_card_eq_card (filter_subset ..)
  have hSpart : Sb.card + Sg.card = S.card := card_sdiff_add_card_eq_card (filter_subset ..)
  have hRg : ∀ x, x ∈ Rg ↔ F (some x) none = true := by
    intro x; simp only [Rg, mem_filter]
    exact ⟨And.right, fun hx => ⟨by by_contra hh; rw [hR _ hh, hzero] at hx; contradiction, hx⟩⟩
  have hSg : ∀ y, y ∈ Sg ↔ F none (some y) = true := by
    intro y; simp only [Sg, mem_filter]
    exact ⟨And.right, fun hy => ⟨by by_contra hh; rw [hS _ hh, hzero] at hy; contradiction, hy⟩⟩
  have hcov : ∀ x y, ort F x y = true → x ∈ Rg ∨ y ∈ Sg ∨ (x ∈ Rb ∧ y ∈ Sb) := by
    intro x y hh
    by_cases hxr : x ∈ Rg
    · exact Or.inl hxr
    by_cases hys : y ∈ Sg
    · exact Or.inr (Or.inl hys)
    refine Or.inr (Or.inr ⟨mem_sdiff.mpr ⟨?_, hxr⟩, mem_sdiff.mpr ⟨?_, hys⟩⟩)
    · by_contra hx
      apply hys
      exact (hSg _).mpr (by simpa [ort, hR _ hx] using hh)
    · by_contra hy
      apply hxr
      exact (hRg _).mpr (by simpa [ort, hS _ hy] using hh)
  by_cases hb : 0 < Rb.card + Sb.card
  · left
    have hv : Rb.card*Sb.card ≤ (Rb.card+Sb.card-1)*N := by
      by_cases he : Sb.card = 0
      · simp [he]
      have hbl : Sb.card ≤ N := by simpa using card_le_univ Sb
      exact Nat.mul_le_mul (by omega) hbl
    have ha := area_cover (ort F) Rg Sg Rb Sb hcov
    calc
      tabArea (ort F) ≤ (Rg.card+Sg.card)*N + Rb.card*Sb.card := ha
      _ ≤ (Rg.card+Sg.card)*N + (Rb.card+Sb.card-1)*N := Nat.add_le_add_left hv _
      _ = g*N := by rw [← Nat.add_mul]; congr 1; omega
  · right
    have hr : Rb = ∅ := card_eq_zero.mp (by omega)
    have hs : Sb = ∅ := card_eq_zero.mp (by omega)
    refine ⟨Rg, Sg, by omega, fun x y => ?_⟩
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · intro hh
      simpa [hr, hs] using (hcov x y hh)
    · intro hxy
      exact hmono x y (hxy.imp ((hRg _).mp) ((hSg _).mp))

open Finset PEqualNP.CircuitLowerBounds

def oc {n : ℕ} (C : Circuit) (x y : Option (Fin n)) : Bool := C.eval (input x y)

def tab {n : ℕ} (C : Circuit) (x y : Fin n) : Bool := C.eval (PEqualNP.Represents.oneEach x y)

theorem tab_eq {n : ℕ} (C : Circuit) : @tab n C = ort (oc C) := by
  funext x y
  exact (congrArg C.eval (input_some x y)).symm

theorem splitSupport {N : ℕ} (T : Finset ℕ) :
    ∃ R S : Finset (Fin N), R.card + S.card ≤ T.card ∧
      (∀ x, x ∈ R ↔ x.val ∈ T) ∧ (∀ y, y ∈ S ↔ N+y.val ∈ T) := by
  let R := univ.filter (fun x : Fin N => x.val ∈ T)
  let S := univ.filter (fun y : Fin N => N+y.val ∈ T)
  have hR : ∀ x, x ∈ R ↔ x.val ∈ T := by simp [R]
  have hS : ∀ y, y ∈ S ↔ N+y.val ∈ T := by simp [S]
  refine ⟨R, S, ?_, hR, hS⟩
  let f : Fin N → ℕ := Fin.val
  let F : Fin N → ℕ := fun z => N+z.val
  have hf : Function.Injective f := fun _ _ h => Fin.ext h
  have hF : Function.Injective F := by
    intro a b hh; apply Fin.ext; dsimp [F] at hh; omega
  have hd : Disjoint (R.image f) (S.image F) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨a, _, rfl⟩ := mem_image.mp hw
    obtain ⟨b, _, h⟩ := mem_image.mp hw'
    dsimp [f, F] at h
    have := a.isLt
    omega
  have hs : R.image f ∪ S.image F ⊆ T := by
    intro w hw
    rcases mem_union.mp hw with hl | hr
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
      exact (hR _).mp ha
    · obtain ⟨b, hb, rfl⟩ := mem_image.mp hr
      exact (hS _).mp hb
  have hh := card_le_card hs
  rwa [card_union_of_disjoint hd, card_image_of_injective _ hf,
    card_image_of_injective _ hF] at hh

theorem eraseRow {N : ℕ} (T : Finset ℕ) (x : Fin N) (hx : x.val ∉ T)
    (y : Option (Fin N)) : ∀ i ∈ T,
      (input (some x) y).getD i false = (input none y).getD i false := by
  intro i hi
  have hn : ¬ ∃ a : Fin N, some x = some a ∧ i = a.val := by
    rintro ⟨a, ha, hi'⟩
    cases Option.some.inj ha
    exact hx (hi' ▸ hi)
  rw [input_read, input_read]
  rw [decide_eq_false hn]
  simp

theorem eraseCol {N : ℕ} (T : Finset ℕ) (y : Fin N) (hy : N+y.val ∉ T)
    (x : Option (Fin N)) : ∀ i ∈ T,
      (input x (some y)).getD i false = (input x none).getD i false := by
  intro i hi
  have hn : ¬ ∃ a : Fin N, some y = some a ∧ i = N+a.val := by
    rintro ⟨a, ha, hi'⟩
    cases Option.some.inj ha
    exact hy (hi' ▸ hi)
  rw [input_read, input_read]
  rw [decide_eq_false hn]
  simp

theorem oc_mono {N : ℕ} (C : Circuit) (hm : ∀ a ∈ C.gates, a.op = .and ∨ a.op = .or) :
    ∀ x y : Fin N, (oc C (some x) none = true ∨ oc C none (some y) = true) →
      ort (oc C) x y = true := by
  intro x y h
  have lift : ∀ a b : Option (Fin N),
      (a = some x ∨ a = none) → (b = some y ∨ b = none) →
      oc C a b = true → ort (oc C) x y = true := by
    intro a b ha hb he
    apply monoW hm (input a b) (input (some x) (some y)) (by simp) _ C.output he
    intro i
    rw [input_read, input_read]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [Bool.or_eq_true]
    · exact Or.inl
    · exact Or.inr
  exact h.elim (lift _ _ (Or.inl rfl) (Or.inr rfl)) (lift _ _ (Or.inr rfl) (Or.inl rfl))

theorem circuitRigidity {N g d : ℕ} (C : Circuit) (hN : 2*g+1 < N) (hd : 0 < d)
    (hgate : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (hg : C.size ≤ g) (harea : tabArea (@tab N C) ≤ (g+1)*N-d) :
    tabArea (@tab N C) ≤ g*N ∨ tabLines (@tab N C) (g+1) := by
  rw [tab_eq] at harea ⊢
  obtain ⟨T, hT, hdep⟩ := dep (N+N) C.gates (fun a ha => (hgate a ha).1) {C.output}
  simp only [card_singleton] at hT
  let B := (C.gates.filter (fun gate => decide (gate.inputs.length = 2))).length
  change T.card ≤ B+1 at hT
  obtain ⟨R, S, hRS, hR, hS⟩ := splitSupport (N := N) T
  have hB : B ≤ C.size := List.length_filter_le ..
  have hdelR : ∀ x ∉ R, ∀ y, oc C (some x) y = oc C none y := by
    intro x hx y
    exact hdep _ _ (by simp) (by simp) (eraseRow T x (fun ht => hx ((hR _).mpr ht)) y) _ (mem_singleton_self _)
  have hdelS : ∀ y ∉ S, ∀ x, oc C x (some y) = oc C x none := by
    intro y hy x
    exact hdep _ _ (by simp) (by simp) (eraseCol T y (fun ht => hy ((hS _).mpr ht)) x) _ (mem_singleton_self _)
  refine areaRigidity R S (by omega) hN hd harea hdelR hdelS ?_
  by_cases hm : ∀ a ∈ C.gates, a.op = .and ∨ a.op = .or
  · exact Or.inr (oc_mono C hm)
  · left
    push Not at hm
    obtain ⟨a, ha, hna, hno⟩ := hm
    have hinput := ((hgate a ha).2.resolve_left hno).resolve_left hna |>.2
    have hbl : B < C.size := List.length_filter_lt_length_iff_exists.mpr ⟨a, ha, by simp [hinput]⟩
    omega

theorem circuitDeficit {N g r s : ℕ} (C : Circuit) (hr : 0 < r) (hrs : r ≤ s)
    (hprod : r*s < N) (hN : 2*g+1 < N)
    (hgate : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (hg : C.size ≤ g) (harea : tabArea (@tab N C) ≤ (g+1)*N-r*s)
    (hnot : ¬ tabLines (@tab N C) (g+1)) :
    tabArea (@tab N C) + (N-r*s) ≤ (g+1)*N-r*s := by
  have hpos := Nat.mul_pos hr (show 0 < s by omega)
  have h := (circuitRigidity C hN hpos hgate hg harea).resolve_right hnot
  rw [Nat.add_mul, Nat.one_mul]
  omega

open Finset PEqualNP.CircuitLowerBounds

open scoped BigOperators

noncomputable def nonLinesMass {N g M : ℕ} (D : Fin M → Circuit) (w : Fin M → ℝ) : ℝ :=
  ∑ i, @ite ℝ (tabLines (@tab N (D i)) (g+1)) (Classical.propDecidable _) 0 (w i)

theorem weightedDeficit {N g r s M : ℕ} (D : Fin M → Circuit) (w : Fin M → ℝ)
    (hr : 0 < r) (hrs : r ≤ s) (hp : r*s < N) (hN : 2*g+1 < N)
    (hgates : ∀ i, ∀ gate ∈ (D i).gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (hsize : ∀ i, (D i).size ≤ g) {A : ℕ} (hA : A = (g+1)*N-r*s)
    (hcap : ∀ i, tabArea (@tab N (D i)) ≤ A) (hw : ∀ i, 0 ≤ w i) :
    ((N-r*s : ℕ) : ℝ) * nonLinesMass (N := N) (g := g) D w ≤
      ∑ i, w i * ((A : ℝ) - (tabArea (@tab N (D i)) : ℝ)) := by
  unfold nonLinesMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : tabLines (@tab N (D i)) (g+1)
  · rw [ite_eq_left hi, mul_zero]
    exact mul_nonneg (hw i) (sub_nonneg.mpr (Nat.cast_le.mpr (hcap i)))
  · rw [ite_eq_right hi, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (hw i)
    have hd := circuitDeficit (D i) hr hrs hp hN (hgates i) (hsize i) (hA ▸ hcap i) hi
    rw [← hA] at hd
    have hcast : (tabArea (@tab N (D i)) : ℝ) + ((N-r*s : ℕ) : ℝ) ≤ (A : ℝ) := by
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr hd
    exact le_sub_iff_add_le.mpr (by simpa [add_comm] using hcast)

theorem weightedArea {N g r s M : ℕ} (D : Fin M → Circuit) (w : Fin M → ℝ)
    (hr : 0 < r) (hrs : r ≤ s) (hp : r*s < N) (hN : 2*g+1 < N)
    (hgates : ∀ i, ∀ gate ∈ (D i).gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (hsize : ∀ i, (D i).size ≤ g) {A : ℕ} (hA : A = (g+1)*N-r*s)
    (hcap : ∀ i, tabArea (@tab N (D i)) ≤ A) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (a h : ℝ) (ha : 0 ≤ a)
    (havg : a * ((A : ℝ) - ∑ i, w i * (tabArea (@tab N (D i)) : ℝ)) ≤ (N : ℝ)*h) :
    a * ((N-r*s : ℕ) : ℝ) * nonLinesMass (N := N) (g := g) D w ≤ (N : ℝ)*h := by
  have hh := weightedDeficit D w hr hrs hp hN hgates hsize hA hcap hw
  simp_rw [mul_sub] at hh
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul] at hh
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hh ha).trans havg

end Rigidity

open scoped BigOperators

namespace Converse

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev Pairs (X : Type*) (r s : ℕ) := {R : Finset X // R.card = r} × {S : Finset X // S.card = s}

lemma exists_core (a b : X) (hab : a ≠ b) {r : ℕ} (hr : 0 < r) (hrN : r < Fintype.card X) :
    ∃ U : Finset X, U.card = r-1 ∧ a ∉ U ∧ b ∉ U := by
  let K := ((Finset.univ : Finset X).erase a).erase b
  have hKa : a ∉ K := by simp [K]
  have hKb : b ∉ K := by simp [K]
  have hKc : K.card = Fintype.card X - 2 := by
    dsimp [K]
    rw [Finset.card_erase_of_mem (by simpa [Finset.mem_erase] using hab.symm),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    omega
  obtain ⟨U, hU, hc⟩ := Finset.exists_subset_card_eq (s := K) (n := r-1) (by omega)
  exact ⟨U, hc, fun h => hKa (hU h), fun h => hKb (hU h)⟩

def score {r s : ℕ} (P : Pairs X r s) (T : X → X → ℚ) (c : ℚ) : ℚ :=
  (∑ x ∈ P.1.val, ∑ y ∈ P.2.val, T x y) - c

lemma score_four {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrN : r < Fintype.card X) (hsN : s < Fintype.card X)
    (a b c d : X) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ P₁ P₂ P₃ P₄ : Pairs X r s, ∀ T k,
      score P₁ T k + score P₂ T k - score P₃ T k - score P₄ T k =
        T a c - T a d - T b c + T b d := by
  obtain ⟨U,hU,ha,hb⟩ := exists_core a b hab hr hrN
  obtain ⟨V,hV,hc,hd⟩ := exists_core c d hcd hs hsN
  have hcardU (x : X) (hx : x ∉ U) : (insert x U).card = r := by
    rw [Finset.card_insert_of_notMem hx, hU]; omega
  have hcardV (x : X) (hx : x ∉ V) : (insert x V).card = s := by
    rw [Finset.card_insert_of_notMem hx, hV]; omega
  refine ⟨(⟨insert a U, hcardU a ha⟩, ⟨insert c V, hcardV c hc⟩),
          (⟨insert b U, hcardU b hb⟩, ⟨insert d V, hcardV d hd⟩),
          (⟨insert a U, hcardU a ha⟩, ⟨insert d V, hcardV d hd⟩),
          (⟨insert b U, hcardU b hb⟩, ⟨insert c V, hcardV c hc⟩), ?_⟩
  intro T k
  simp only [score, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
    Finset.sum_insert hd, Finset.sum_add_distrib]
  ring

end Converse
namespace Converse
open scoped BigOperators

lemma flat_rows {X : Type*} [Fintype X] [DecidableEq X] {r s p : ℕ}
    (R : Fin p → {S : Finset X // S.card = r}) (S : {S : Finset X // S.card = s})
    (T : X → X → ℚ) (t d c : ℚ) (hT : ∀ y, ∑ x, T x y = t)
    (hR : ∀ x, ∑ i, (if x ∈ (R i).val then (1 : ℚ) else 0) = d)
    (hc : d*t*s = p*c) : (∑ i, score (R i, S) T c) = 0 := by
  classical
  have he (i : Fin p) : (∑ x ∈ (R i).val, ∑ y ∈ S.val, T x y) =
      ∑ x, (if x ∈ (R i).val then (1 : ℚ) else 0)*(∑ y ∈ S.val, T x y) := by
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    simp
  have he' : (∑ x, ∑ y ∈ S.val, T x y) = (s : ℚ)*t := by
    rw [Finset.sum_comm]
    simp [hT, S.property, nsmul_eq_mul]
  simp only [score, he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hR, ← Finset.mul_sum, he']
  linarith only [hc]

lemma score_transpose {X : Type*} {r s : ℕ} (P : Pairs X r s) (T : X → X → ℚ) (c : ℚ) :
    score (P.2,P.1) (fun x y => T y x) c = score P T c := by
  unfold score
  rw [Finset.sum_comm]

open Tests33671 in
lemma full_packet {n r s t : ℕ} (P : Pairs (Fin (n+1)) r s) :
    ∃ D : Fin (n+1) → Pairs (Fin (n+1)) r s, D 0 = P ∧ ∀ Q, reg t Q →
      (∑ i, score (D i) (fun x y => bit ℚ (Q x y)) ((t : ℚ)*r*s/(n+1))) = 0 := by
  classical
  let R (i : Fin (n+1)) : {S : Finset (Fin (n+1)) // S.card = r} :=
    ⟨P.1.val.map (Equiv.addRight i).toEmbedding, by simp [P.1.property]⟩
  refine ⟨fun i => (R i,P.2), ?_, ?_⟩
  · apply Prod.ext
    · apply Subtype.ext
      ext x
      simp [R, Finset.mem_map_equiv, Equiv.addRight]
    · rfl
  intro Q hQ
  have hQ' (y : Fin (n+1)) : (∑ x, bit ℚ (Q x y)) = t := by rw [bit_sum_card, hQ.2]
  apply flat_rows R P.2 _ t r _ hQ'
  · intro x
    have he (i : Fin (n+1)) : (if x ∈ (R i).val then (1 : ℚ) else 0) =
        bit ℚ (decide ((Equiv.subLeft x) i ∈ P.1.val)) := by
      simp only [R, Finset.mem_map_equiv, bit, decide_eq_true_eq]
      simp [Equiv.addRight, Equiv.subLeft, sub_eq_add_neg]
    simp_rw [he]
    rw [Equiv.sum_comp (Equiv.subLeft x) (fun z => bit ℚ (decide (z ∈ P.1.val))), bit_sum_card]
    simp [P.1.property]
  · have hn : (0 : ℚ) < ((n+1 : ℕ) : ℚ) := by positivity
    push_cast at hn ⊢
    field_simp

open Tests33671 in
lemma short_row_packet {n r s t : ℕ} (hr : r ≤ n+1)
    (S : {S : Finset (Fin (n+1)) // S.card = s}) :
    ∃ D : Fin ((n+1) / Nat.gcd (n+1) r) → Pairs (Fin (n+1)) r s,
      ∀ Q, reg t Q →
      (∑ i, score (D i) (fun x y => bit ℚ (Q x y)) ((t : ℚ)*r*s/(n+1))) = 0 := by
  classical
  let k := Nat.gcd (n+1) r
  let p := (n+1)/k
  let j := r/k
  have hk : 0 < k := Nat.gcd_pos_of_pos_left _ (by omega)
  have hp : p*k = n+1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hj : j*k = r := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hjp : j ≤ p := Nat.div_le_div_right hr
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  obtain ⟨d, hd⟩ : ∃ d : ℕ, p = d+1 := ⟨p-1, (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0)).symm⟩
  let e : Fin (d+1) × Fin k ≃ Fin (n+1) := finProdFinEquiv.trans (finCongr (by rw [← hd]; exact hp))
  let Z (i : Fin (d+1)) : Finset (Fin (d+1)) := Finset.univ.filter (fun a => band j i a)
  have hband : reg j (@band d j) := band_reg (by omega)
  let R (i : Fin (d+1)) : {S : Finset (Fin (n+1)) // S.card = r} :=
    ⟨((Z i).product Finset.univ).map e.toEmbedding, by
      simpa [Z, Finset.card_product, hband.1] using hj⟩
  refine ⟨fun i => (R (Fin.cast hd i),S), ?_⟩
  intro Q hQ
  have hQ' (y : Fin (n+1)) : (∑ x, bit ℚ (Q x y)) = t := by rw [bit_sum_card, hQ.2]
  apply flat_rows _ S _ t j _ hQ'
  · intro x
    have he (i : Fin p) : (if x ∈ (R (Fin.cast hd i)).val then (1 : ℚ) else 0) =
        bit ℚ (band j (Fin.cast hd i) (e.symm x).1) := by
      simp [R,Z,Finset.mem_map_equiv,bit]
    simp_rw [he]
    change (∑ i : Fin p, bit ℚ (band j ((finCongr hd) i) (e.symm x).1)) = _
    rw [Equiv.sum_comp (finCongr hd) (fun i => bit ℚ (band j i (e.symm x).1)), bit_sum_card, hband.2]
  · have hp' : (p : ℚ)*(k : ℚ) = (n:ℚ)+1 := by exact_mod_cast hp
    have hj' : (j : ℚ)*(k : ℚ) = (r:ℚ) := by exact_mod_cast hj
    have hk' : 0 < (k : ℚ) := by exact_mod_cast hk
    have hn' : 0 < (n : ℚ) + 1 := by positivity
    field_simp
    calc
      _ = (j : ℚ)*(k : ℚ)*(p : ℚ)*t*s := by rw [← hp']; ring
      _ = _ := by rw [hj']; ring

open Tests33671 in
lemma short_col_packet {n r s t : ℕ} (hs : s ≤ n+1)
    (R : {S : Finset (Fin (n+1)) // S.card = r}) :
    ∃ D : Fin ((n+1) / Nat.gcd (n+1) s) → Pairs (Fin (n+1)) r s,
      ∀ Q, reg t Q →
      (∑ i, score (D i) (fun x y => bit ℚ (Q x y)) ((t : ℚ)*r*s/(n+1))) = 0 := by
  obtain ⟨D, hD⟩ := short_row_packet (t := t) hs R
  refine ⟨fun i => ((D i).2,(D i).1), fun Q hQ => ?_⟩
  have h := hD (fun x y => Q y x) ⟨hQ.2,hQ.1⟩
  have hc : (t : ℚ)*s*r/(n+1) = (t : ℚ)*r*s/(n+1) := by ring
  simp_rw [hc] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (score_transpose ((D i).2,(D i).1) _ _).symm

end Converse

open scoped BigOperators

namespace Converse

lemma rational_direction {I T : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (hm : m ≤ Fintype.card I) (A : T → I → ℚ) (Q : Fin m → T)
    (hpos : ∀ z : I → ℚ, z ≠ 0 → ∃ t : T, 0 < ∑ i, z i * A t i) :
    ∃ z : I → ℚ, (∀ j, ∑ i, z i * A (Q j) i ≤ 0) ∧ ∃ t : T, 0 < ∑ i, z i * A t i := by
  classical
  let F : (I → ℚ) →ₗ[ℚ] (Fin m → ℚ) :=
    { toFun := fun z j => ∑ i, z i * A (Q j) i
      map_add' := by intro x y; funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; funext j; simp [Finset.mul_sum, mul_assoc] }
  have hF (z : I → ℚ) (j : Fin m) : F z j = ∑ i, z i * A (Q j) i := rfl
  suffices h : ∃ z : I → ℚ, z ≠ 0 ∧ ∀ j, F z j ≤ 0 by
    obtain ⟨z, hz, hzQ⟩ := h
    exact ⟨z, by simpa [hF] using hzQ, hpos z hz⟩
  by_cases hi : Function.Injective F
  · have h' := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h'
    have heq : Fintype.card I = m := le_antisymm h' hm
    have hfin : Module.finrank ℚ (I → ℚ) = Module.finrank ℚ (Fin m → ℚ) := by
      simp [Module.finrank_fintype_fun_eq_card, heq]
    have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi
    obtain ⟨z, hz⟩ := hs (fun _ => -1)
    have hmpos : 0 < m := by rw [← heq]; exact Fintype.card_pos
    obtain ⟨j⟩ : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
    refine ⟨z, ?_, fun k => by rw [hz]; norm_num⟩
    intro hz0
    rw [hz0, map_zero] at hz
    have bad := congrFun hz j
    norm_num at bad
  · obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hi
    refine ⟨x - y, sub_ne_zero.mpr hne, fun j => ?_⟩
    rw [map_sub, hxy, sub_self]
    exact le_rfl

lemma clear_denominators {I : Type*} [Fintype I] (z : I → ℚ) :
    ∃ (d : ℕ) (b : I → ℤ), 0 < d ∧ ∀ i, (b i : ℚ) = (d : ℚ) * z i := by
  classical
  let d := ∏ i, (z i).den
  have hd : 0 < d := Finset.prod_pos (fun i _ => (z i).den_pos)
  have he (i : I) : ∃ b : ℤ, (b : ℚ) = (d : ℚ) * z i := by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i : I => (z i).den) (Finset.mem_univ i)
    refine ⟨(k : ℤ) * (z i).num, ?_⟩
    change d = (z i).den * k at hk
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose b hb using he
  exact ⟨d, b, hd, hb⟩

lemma integral_direction {I T : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (hm : m ≤ Fintype.card I) (A : T → I → ℚ) (Q : Fin m → T)
    (hpos : ∀ z : I → ℚ, z ≠ 0 → ∃ t : T, 0 < ∑ i, z i * A t i) :
    ∃ b : I → ℤ, (∀ j, ∑ i, (b i : ℚ) * A (Q j) i ≤ 0) ∧
      ∃ t : T, 0 < ∑ i, (b i : ℚ) * A t i := by
  obtain ⟨z, hQ, t, ht⟩ := rational_direction hm A Q hpos
  obtain ⟨d, b, hd, hb⟩ := clear_denominators z
  have hadd (t : T) : (∑ i, (b i : ℚ) * A t i) = (d : ℚ) * ∑ i, z i * A t i := by
    simp_rw [hb, mul_assoc, Finset.mul_sum]
  have hdp : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  exact ⟨b, fun j => by rw [hadd]; exact mul_nonpos_of_nonneg_of_nonpos hdp.le (hQ j),
    t, by rw [hadd]; exact mul_pos hdp ht⟩

lemma dyadic_fill {p q B : ℕ} (hB : p.gcd q ∣ B) {u : ℕ} (hu : p.gcd q = 2^u) :
    ∃ v a b : ℕ, B + a*p + b*q = 2^v := by
  let e := B + p.pred * q.pred
  have hd : p.gcd q ∣ 2^(u+e) := by
    rw [hu, pow_add]
    exact dvd_mul_right ..
  have hpow : e < 2^(u+e) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hBd : p.gcd q ∣ 2^(u+e) - B := Nat.dvd_sub hd hB
  have hbnd : p.pred * q.pred ≤ 2^(u+e) - B := by omega
  obtain ⟨a,b,hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q _ hBd hbnd
  exact ⟨u+e, a, b, by omega⟩

end Converse

open scoped BigOperators
namespace Converse

lemma replace_at {C T : Type*} {N : ℕ} (z : Fin N) (score : C → T → ℚ)
    (D : Fin N → C) (A : C) (t : T) :
    (∑ i, score (if i = z then A else D i) t) =
      (∑ i, score (D i) t) + score A t - score (D z) t := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ z),
    ← Finset.sum_erase_add Finset.univ (fun i => score (D i) t) (Finset.mem_univ z)]
  have h : (∑ i ∈ Finset.univ.erase z, score (if i = z then A else D i) t) =
      (∑ i ∈ Finset.univ.erase z, score (D i) t) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
  rw [h, ite_eq_left rfl]
  ring

lemma uniform_mixture {I C T : Type*} [Fintype I] {N p q : ℕ} (z : Fin N)
    (hdvd : p.gcd q ∣ N) (C₀ : C) (score : C → T → ℚ)
    (hbase : ∀ c : C, ∃ D : Fin N → C, D z = c ∧ ∀ t, ∑ i, score (D i) t = 0)
    (hp : ∃ D : Fin p → C, ∀ t, ∑ i, score (D i) t = 0)
    (hq : ∃ D : Fin q → C, ∀ t, ∑ i, score (D i) t = 0)
    (A : T → I → ℚ) (pos neg : I → Bool → C)
    (hA : ∀ t i, ∑ j : Bool, (score (pos i j) t - score (neg i j) t) = A t i)
    (b : I → ℤ) :
    ∃ (M : ℕ) (D : Fin M → C), 0 < M ∧
      ((∃ u : ℕ, p.gcd q = 2^u) → ∃ u : ℕ, M = 2^u) ∧
      ∀ t, (∑ i, score (D i) t) = ∑ i, (b i : ℚ)*A t i := by
  classical
  obtain ⟨DP, hDP⟩ := hp
  obtain ⟨DQ, hDQ⟩ := hq
  choose base base_z base_flat using hbase
  let K := (Sum Unit (Σ i : I, Fin (b i).natAbs × Bool))
  let B := Fintype.card K * N
  have hB : 0 < B := by
    have hK : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
    exact Nat.mul_pos hK (Nat.zero_lt_of_lt z.isLt)
  have hdvdB : p.gcd q ∣ B := dvd_mul_of_dvd_right hdvd _
  have hpad : ∃ a₁ a₂ : ℕ, ((∃ u : ℕ, p.gcd q = 2^u) →
      ∃ u : ℕ, B+a₁*p+a₂*q = 2^u) := by
    by_cases h : ∃ u : ℕ, p.gcd q = 2^u
    · obtain ⟨u, hu⟩ := h
      obtain ⟨v,a₁,a₂,heq⟩ := dyadic_fill hdvdB hu
      exact ⟨a₁,a₂,fun _ => ⟨v,heq⟩⟩
    · exact ⟨0,0,fun e => (h e).elim⟩
  obtain ⟨a₁,a₂,hpow⟩ := hpad
  let G := ((K × Fin N) ⊕ (Fin a₁ × Fin p)) ⊕ (Fin a₂ × Fin q)
  have hG : Fintype.card G = B + a₁*p + a₂*q := by
    change Fintype.card (((K × Fin N) ⊕ (Fin a₁ × Fin p)) ⊕ (Fin a₂ × Fin q)) = _
    simp [B]
  let P (i : I) (j : Bool) := if 0 ≤ b i then pos i j else neg i j
  let U (i : I) (j : Bool) := if 0 ≤ b i then neg i j else pos i j
  let D₀ : K × Fin N → C := fun (k,v) => match k with
    | .inl _ => base C₀ v
    | .inr ⟨i,_,j⟩ => if v = z then P i j else base (U i j) v
  let D₁ : G → C := fun k => match k with
    | .inl (.inl e) => D₀ e
    | .inl (.inr (_,i)) => DP i
    | .inr (_,i) => DQ i
  let M := Fintype.card G
  let e := Fintype.equivFin G
  refine ⟨M, D₁ ∘ e.symm, by dsimp [M]; rw [hG]; omega,
    fun h => by dsimp [M]; rw [hG]; exact hpow h, ?_⟩
  intro t
  have hpack (i : I) (j : Bool) :
      (∑ v, score (if v = z then P i j else base (U i j) v) t) =
        score (P i j) t - score (U i j) t := by
    rw [replace_at, base_flat, base_z, zero_add]
  have hsum (i : I) : (∑ j : Bool, (score (P i j) t - score (U i j) t)) =
      if 0 ≤ b i then A t i else - A t i := by
    by_cases hi : 0 ≤ b i
    · simpa [P,U,hi] using hA t i
    · simp only [P,U,hi,ite_false]
      rw [← hA t i, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
  have habs (i : I) : (b i : ℚ) =
      if 0 ≤ b i then ((b i).natAbs : ℚ) else - ((b i).natAbs : ℚ) := by
    by_cases hi : 0 ≤ b i
    · rw [ite_eq_left hi]
      exact congrArg (fun x : ℤ => (x : ℚ)) (Int.natAbs_of_nonneg hi).symm |>.trans (Int.cast_natCast _)
    · rw [ite_eq_right hi]
      rcases Int.natAbs_eq (b i) with h|h
      · omega
      · exact_mod_cast h
  dsimp only [Function.comp_apply]
  rw [Fintype.sum_equiv e.symm _ (fun x : G => score (D₁ x) t) (fun _ => rfl)]
  change (∑ x : ((K × Fin N) ⊕ (Fin a₁ × Fin p)) ⊕ (Fin a₂ × Fin q), score (D₁ x) t) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  dsimp [D₁]
  rw [Fintype.sum_prod_type (fun x : Fin a₁ × Fin p => score (DP x.2) t),
    Fintype.sum_prod_type (fun x : Fin a₂ × Fin q => score (DQ x.2) t)]
  simp only [hDP, hDQ, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  change (∑ x : Sum Unit (Σ i : I, Fin (b i).natAbs × Bool), ∑ v,
    score (D₀ (x,v)) t) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  dsimp [D₀]
  simp only [base_flat, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  simp only [hpack, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [habs]
  split_ifs <;> ring

end Converse

open scoped BigOperators
namespace Converse

variable {I : Type*} [Fintype I] [DecidableEq I]

def diff (i : I) (x : Option I) : ℚ :=
  (if x = some i then 1 else 0) - (if x = none then 1 else 0)

def contrast (T : Option I → Option I → ℚ) (ij : I × I) : ℚ :=
  T (some ij.1) (some ij.2) - T (some ij.1) none - T none (some ij.2) + T none none

def rect (ij : I × I) (x y : Option I) : ℚ := diff ij.1 x * diff ij.2 y

def liftRect (z : I × I → ℚ) (x y : Option I) := ∑ ij, z ij * rect ij x y

def eval (z : I × I → ℚ) (T : Option I → Option I → ℚ) := ∑ ij, z ij * contrast T ij

lemma sum_diff (i : I) : (∑ x : Option I, diff i x) = 0 := by
  simp [diff, Finset.sum_sub_distrib]

lemma liftRect_some (z : I × I → ℚ) (i j : I) : liftRect z (some i) (some j) = z (i,j) := by
  classical
  have h : ∀ ij : I × I, z ij * rect ij (some i) (some j) = if ij = (i,j) then z ij else 0 := by
    intro ⟨a,b⟩
    by_cases ha : i = a <;> by_cases hb : j = b <;> simp [rect, diff, ha, hb, eq_comm]
  simp [liftRect, h]

lemma liftRect_row (z : I × I → ℚ) (x : Option I) : (∑ y, liftRect z x y) = 0 := by
  simp_rw [liftRect]
  rw [Finset.sum_comm]
  simp only [rect, ← mul_assoc, ← Finset.mul_sum, sum_diff, mul_zero, Finset.sum_const_zero]

lemma liftRect_col (z : I × I → ℚ) (y : Option I) : (∑ x, liftRect z x y) = 0 := by
  simp_rw [liftRect]
  rw [Finset.sum_comm]
  simp only [rect, mul_comm (_ : ℚ) (diff _ y), ← mul_assoc, ← Finset.mul_sum, sum_diff, mul_zero, Finset.sum_const_zero]

lemma eval_rect (z : I × I → ℚ) (ij : I × I) : eval z (rect ij) = contrast (liftRect z) ij := by
  simp only [eval, contrast, liftRect, mul_sub, mul_add]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h1 : j.1 = ij.1 <;> by_cases h2 : j.2 = ij.2 <;>
    simp [rect, diff, h1, h2, eq_comm]

lemma eval_sub (z : I × I → ℚ) (T U : Option I → Option I → ℚ) :
    eval z (fun x y => T x y - U x y) = eval z T - eval z U := by
  simp only [eval, ← Finset.sum_sub_distrib, contrast, ← mul_sub]
  apply Finset.sum_congr rfl
  intro ij _
  ring

lemma contrast_sep (z : I × I → ℚ) (hzero : ∀ ij, contrast (liftRect z) ij = 0) : z = 0 := by
  let H := liftRect z
  have hadd (x y : Option I) : H x y = H x none + H none y - H none none := by
    cases x <;> cases y
    case none.none => ring
    case none.some => ring
    case some.none => ring
    case some.some i j =>
      have h := hzero (i, j)
      dsimp [contrast] at h
      change H _ _ - H _ none - H none _ + H none none = 0 at h
      linarith
  have hcolumn (y : Option I) : H none y - H none none = 0 := by
    have he (x : Option I) : H x y - H x none = H none y - H none none := by
      linarith [hadd x y]
    have hz : (∑ x : Option I, (H x y - H x none)) = 0 := by
      rw [Finset.sum_sub_distrib, liftRect_col, liftRect_col, sub_self]
    simp_rw [he] at hz
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  have hrow (x : Option I) : H x none = 0 := by
    have he (y : Option I) : H x y = H x none := by linarith [hadd x y, hcolumn y]
    have hz : (∑ y : Option I, H x y) = 0 := liftRect_row z x
    simp_rw [he] at hz
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  ext i
  have h : H (some i.1) (some i.2) = 0 := by
    linarith [hadd (some i.1) (some i.2), hcolumn (some i.2), hrow (some i.1)]
  simpa [H, liftRect_some] using h

lemma eval_sum_const {K : Type*} [Fintype K] (z : I × I → ℚ)
    (C : K → Option I → Option I → ℚ) (c : Option I → ℚ)
    (hflat : ∀ x y, (∑ j, C j x y) = c y) : (∑ j, eval z (C j)) = 0 := by
  classical
  unfold eval
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro ij _
  rw [← Finset.mul_sum]
  simp [contrast, Finset.sum_add_distrib, Finset.sum_sub_distrib, hflat]

lemma eval_pos {T : Type*} {K : Type*} [Fintype K] (k₀ : K)
    (val : T → Option I → Option I → ℚ) (shift : T → K → T)
    (hfix : ∀ t, val (shift t k₀) = val t)
    (hflat : ∀ t, ∃ c : Option I → ℚ, ∀ x y, (∑ k, val (shift t k) x y) = c y)
    (hswitch : ∀ ij : I × I, ∃ t u, ∀ x y, val t x y - val u x y = rect ij x y)
    (z : I × I → ℚ) (hz : z ≠ 0) : ∃ t, 0 < eval z (val t) := by
  classical
  by_contra! hneg
  have hzero (t : T) : eval z (val t) = 0 := by
    obtain ⟨c, hc⟩ := hflat t
    have hs := eval_sum_const z (fun k => val (shift t k)) c hc
    have hle : ∀ k ∈ (Finset.univ : Finset K), eval z (val (shift t k)) ≤ 0 := fun k _ => hneg _
    have he := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hs k₀ (Finset.mem_univ _)
    rwa [hfix] at he
  apply hz
  apply contrast_sep
  intro ij
  obtain ⟨t,u,he⟩ := hswitch ij
  have hh : (fun x y => val t x y - val u x y) = rect ij := funext (fun x => funext (he x))
  rw [← eval_rect, ← hh, eval_sub, hzero, hzero, sub_self]

end Converse
namespace Converse
open scoped BigOperators
open Tests33671

lemma regular_mixture {n r s t m : ℕ} (hn : 0 < n) (ht₀ : 0 < t) (ht : t < n+1)
    (hr₀ : 0 < r) (hs₀ : 0 < s) (hr : r < n+1) (hs : s < n+1)
    (hm : m ≤ n^2) (Q : Fin m → Graph (n+1)) (hQ : ∀ j, reg t (Q j)) :
    ∃ (M : ℕ) (D : Fin M → Pairs (Fin (n+1)) r s), 0 < M ∧
      ((∃ u : ℕ, Nat.gcd ((n+1) / Nat.gcd (n+1) r) ((n+1) / Nat.gcd (n+1) s) = 2^u) →
        ∃ u : ℕ, M = 2^u) ∧
      (∀ j, (∑ i, score (D i) (fun x y => bit ℚ (Q j x y)) ((t : ℚ)*r*s/(n+1))) ≤ 0) ∧
      ∃ T : Graph (n+1), reg t T ∧
        0 < (∑ i, score (D i) (fun x y => bit ℚ (T x y)) ((t : ℚ)*r*s/(n+1))) := by
  classical
  let T := {Q : Graph (n+1) // reg t Q}
  let e : Option (Fin n) ≃ Fin (n+1) := (finSuccEquiv n).symm
  let val (q : T) (x y : Option (Fin n)) := bit ℚ (q.val (e x) (e y))
  let A (q : T) := contrast (val q)
  let sc (p : Pairs (Fin (n+1)) r s) (q : T) := score p (fun x y => bit ℚ (q.val x y)) ((t : ℚ)*r*s/(n+1))
  let shift (q : T) (k : Fin (n+1)) : T :=
    ⟨fun x y => q.val (x+k) y, reg_relabel q.val q.property (Equiv.addRight k) (Equiv.refl _)⟩
  have hshift (q : T) : val (shift q 0) = val q := by ext x y; simp [val,shift]
  have hmean (q : T) : ∃ c : Option (Fin n) → ℚ, ∀ x y, (∑ k, val (shift q k) x y) = c y := by
    refine ⟨fun _ => (t : ℚ), fun x y => ?_⟩
    change (∑ k : Fin (n+1), bit ℚ (q.val ((Equiv.addLeft (e x)) k) (e y))) = _
    rw [Equiv.sum_comp (Equiv.addLeft (e x)) (fun a => bit ℚ (q.val a (e y))), bit_sum_card, q.property.2]
  have hswitch (ij : Fin n × Fin n) : ∃ u v : T, ∀ x y, val u x y - val v x y = rect ij x y := by
    have hx : e none ≠ e (some ij.1) := by intro h; cases e.injective h
    have hy : e (some ij.2) ≠ e none := by intro h; cases e.injective h
    obtain ⟨B,S,hB,hS,h⟩ := checker ht₀ ht hx hy
    refine ⟨⟨S,hS⟩,⟨B,hB⟩,fun x y => ?_⟩
    change bit ℚ (S (e x) (e y)) - bit ℚ (B (e x) (e y)) = _
    simpa [rect, diff, e.injective.eq_iff] using h ℚ (e x) (e y)
  have hpos (z : Fin n × Fin n → ℚ) (hz : z ≠ 0) : ∃ q : T, 0 < ∑ i, z i * A q i :=
    eval_pos 0 val shift hshift hmean hswitch z hz
  have hn' : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hm' : m ≤ Fintype.card (Fin n × Fin n) := by simpa [pow_two] using hm
  obtain ⟨b,hbox,u,hu⟩ := integral_direction hm' A (fun j => ⟨Q j,hQ j⟩) hpos
  have hpairs (i : Fin n × Fin n) : ∃ P₁ P₂ P₃ P₄ : Pairs (Fin (n+1)) r s, ∀ q : T,
      sc P₁ q + sc P₂ q - sc P₃ q - sc P₄ q = A q i := by
    have hx : e (some i.1) ≠ e none := by intro h; cases e.injective h
    have hy : e (some i.2) ≠ e none := by intro h; cases e.injective h
    obtain ⟨P₁,P₂,P₃,P₄,h⟩ := score_four hr₀ hs₀ (by simpa using hr) (by simpa using hs) _ _ _ _ hx hy
    refine ⟨P₁,P₂,P₃,P₄,fun q => ?_⟩
    simpa only [sc, A, contrast, val] using h (fun x y => bit ℚ (q.val x y)) ((t : ℚ)*r*s/(n+1))
  choose P₁ P₂ P₃ P₄ hP using hpairs
  have hP' (q : T) (i : Fin n × Fin n) :
      (∑ j : Bool, (sc (if j then P₁ i else P₂ i) q - sc (if j then P₃ i else P₄ i) q)) = A q i := by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ite_true, ite_false]
    linarith only [hP i q]
  let P₀ := P₁ (⟨0,hn⟩,⟨0,hn⟩)
  have hbase (c : Pairs (Fin (n+1)) r s) : ∃ D : Fin (n+1) → _, D 0 = c ∧ ∀ q, ∑ i, sc (D i) q = 0 := by
    obtain ⟨D,he,hD⟩ := full_packet (t := t) c
    exact ⟨D,he,fun q => hD q.val q.property⟩
  have hrow : ∃ D : Fin ((n+1) / Nat.gcd (n+1) r) → _, ∀ q, ∑ i, sc (D i) q = 0 := by
    obtain ⟨D,hD⟩ := short_row_packet (t := t) hr.le P₀.2
    exact ⟨D,fun q => hD q.val q.property⟩
  have hcol : ∃ D : Fin ((n+1) / Nat.gcd (n+1) s) → _, ∀ q, ∑ i, sc (D i) q = 0 := by
    obtain ⟨D,hD⟩ := short_col_packet (t := t) hs.le P₀.1
    exact ⟨D,fun q => hD q.val q.property⟩
  have hdiv : Nat.gcd ((n+1) / Nat.gcd (n+1) r) ((n+1) / Nat.gcd (n+1) s) ∣ n+1 :=
    (Nat.gcd_dvd_left _ _).trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  obtain ⟨M,D,hM,hMd,hD⟩ := uniform_mixture 0 hdiv P₀ sc hbase hrow hcol A
    (fun i j => if j then P₁ i else P₂ i) (fun i j => if j then P₃ i else P₄ i) hP' b
  exact ⟨M,D,hM,hMd,fun j => (hD ⟨Q j,hQ j⟩).trans_le (hbox j),
    u.val,u.property, (hD u).symm ▸ hu⟩

end Converse

namespace Converse
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents (oneEach)

lemma getD_app_lt (l m : List Bool) (j : ℕ) (hj : j < l.length) :
    (l ++ m).getD j false = l.getD j false := by
  simp [List.getD, List.getElem?_append_left hj]

lemma chain_length (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons a as ih =>
    simp only [Circuit.wires, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma chain_prefix (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    ((⟨gs,0⟩ : Circuit).wires x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih _ (by simp; omega), getD_app_lt _ _ _ hi]

lemma add_or_gate {N w : ℕ} {C : Circuit} (hw : w < N)
    (hr : ReadsBack N C) (ho : C.output < N+C.size) :
    let D : Circuit := ⟨C.gates ++ [⟨.or,[C.output,w]⟩], N+C.size⟩
    ReadsBack N D ∧ D.output < N+D.size ∧ D.size = C.size+1 ∧
      (∀ g ∈ D.gates, g ∈ C.gates ∨ g.op = .or ∧ g.inputs.length = 2) ∧
      ∀ x : List Bool, x.length = N → D.eval x = (C.eval x || x.getD w false) := by
  dsimp only
  constructor
  · intro j hj i hi
    dsimp [gateAt] at hi
    by_cases h : j < C.gates.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD] at hi
      exact hr j h i hi
    · have he : j = C.gates.length := by simp at hj; omega
      subst j
      have he' : (C.gates ++ [Gate.mk .or [C.output,w]]).getD C.gates.length (Gate.mk .or []) =
          (⟨.or,[C.output,w]⟩ : Gate) := by simp [List.getD]
      rw [he'] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl
      · exact ho
      · omega
  refine ⟨by simp [Circuit.size], by simp [Circuit.size], ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with h | h
    · exact Or.inl h
    · simp only [List.mem_singleton] at h
      subst g
      exact Or.inr ⟨rfl,rfl⟩
  · intro x hx
    let W := C.wires x
    have hlen : W.length = N+C.size := by rw [← hx]; exact chain_length C.gates x
    have hnew : ((⟨C.gates ++ [⟨.or,[C.output,w]⟩], N+C.size⟩ : Circuit).wires x) =
      W ++ [GateOp.or.eval [W.getD C.output false, W.getD w false]] := by
      simp [Circuit.wires, W, List.foldl_append]
    change (((⟨C.gates ++ [⟨.or,[C.output,w]⟩], N+C.size⟩ : Circuit).wires x).getD (N+C.size) false) = _
    rw [hnew, ← hlen]
    simp only [List.getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
    change GateOp.or.eval [C.eval x, W.getD w false] = _
    have hwx : w < x.length := by omega
    rw [show W.getD w false = x.getD w false from chain_prefix C.gates x hwx]
    change GateOp.or.eval [C.eval x, x.getD w false] = (C.eval x || x.getD w false)
    generalize C.eval x = a, x.getD w false = b
    cases a <;> cases b <;> rfl

lemma or_chain {N a : ℕ} (L : List ℕ) (ha : a < N) (hL : ∀ i ∈ L, i < N) :
    ∃ C : Circuit, ReadsBack N C ∧ C.output < N+C.size ∧ C.size = L.length ∧
      (∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length = 2) ∧
      ∀ x : List Bool, x.length = N → C.eval x = ((a::L).any fun i => x.getD i false) := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨⟨[],a⟩, by simp [ReadsBack], ha, rfl, by simp, fun _ _ => by simp [Circuit.eval,Circuit.wires]⟩
  | append_singleton L w ih =>
    obtain ⟨C,hr,ho,hC,hG,he⟩ := ih (fun i hi => hL i (List.mem_append_left _ hi))
    have hw := hL w (List.mem_append_right _ (by simp))
    obtain ⟨hr',ho',hsize,hg',he'⟩ := add_or_gate hw hr ho
    refine ⟨⟨C.gates ++ [⟨.or,[C.output,w]⟩],N+C.size⟩,hr',ho',hsize.trans (by simp [hC]), ?_, ?_⟩
    · intro g hg
      exact (hg' g hg).elim (hG g) id
    · intro x hx
      rw [he' x hx, he x hx]
      change _ = ((a::L) ++ [w]).any _
      simp [Bool.or_assoc]

lemma getD_oneEach_left {N : ℕ} (x y i : Fin N) :
    (oneEach x y).getD i.val false = decide (i = x) := by
  have hi : i.val < (List.ofFn fun j : Fin N => decide (j = x)).length := by simp
  rw [oneEach, getD_app_lt _ _ _ hi]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma getD_oneEach_right {N : ℕ} (x y i : Fin N) :
    (oneEach x y).getD (N+i.val) false = decide (i = y) := by
  simp [oneEach, List.getD_eq_getElem?_getD, i.isLt]

lemma or_lines {N : ℕ} (R S : Finset (Fin N)) (hpos : 0 < R.card + S.card) :
    ∃ C : Circuit, ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
      C.size+1 = R.card+S.card ∧
      (∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length = 2) ∧
      ∀ x y, C.eval (oneEach x y) = decide (x ∈ R ∨ y ∈ S) := by
  classical
  let raw := (R.toList.map Fin.val) ++ (S.toList.map fun i => N+i.val)
  have hlen : raw.length = R.card+S.card := by simp [raw]
  have hraw : ∀ i ∈ raw, i < N+N := by
    intro i hi
    simp only [raw, List.mem_append, List.mem_map, Finset.mem_toList] at hi
    rcases hi with ⟨x,_,rfl⟩ | ⟨y,_,rfl⟩
    · have := x.isLt; omega
    · have := y.isLt; omega
  obtain ⟨a,L, hlist⟩ : ∃ a L, raw = a::L := by
    cases hh : raw with
    | nil => simp [hh] at hlen; omega
    | cons a L => exact ⟨a,L,rfl⟩
  have ha : a < N+N := hraw a (by simp [hlist])
  have hL : ∀ i ∈ L, i < N+N := fun i hi => hraw i (by simp [hlist, hi])
  obtain ⟨C,hr,ho,hs,hg,he⟩ := or_chain L ha hL
  refine ⟨C,hr,ho,by rw [hlist] at hlen; simpa [hs] using hlen, hg, ?_⟩
  intro x y
  rw [he (oneEach x y) (by simp [oneEach]), ← hlist]
  simp only [raw, List.any_append, List.any_map]
  change ((R.toList.any (fun i => (oneEach x y).getD i.val false)) ||
    (S.toList.any (fun i => (oneEach x y).getD (N+i.val) false))) = _
  simp_rw [getD_oneEach_left, getD_oneEach_right]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, List.any_eq_true, Finset.mem_toList, decide_eq_true_eq]
  constructor
  · rintro (⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩)
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (h | h)
    · exact Or.inl ⟨x,h,rfl⟩
    · exact Or.inr ⟨y,h,rfl⟩

end Converse
namespace Converse
open scoped BigOperators
open Tests33671
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents (oneEach)

def gridArea {N : ℕ} (C : Circuit) : ℕ :=
  (Finset.univ.filter (fun z : Fin N × Fin N => C.eval (oneEach z.1 z.2))).card

def gridLoss {N : ℕ} (C : Circuit) (T : Graph N) : ℕ :=
  (Finset.univ.filter (fun z : Fin N × Fin N => C.eval (oneEach z.1 z.2) ≠ T z.1 z.2)).card

noncomputable def ind {N : ℕ} (R : Finset (Fin N)) (x : Fin N) : ℝ := if x ∈ R then 1 else 0

lemma ind_sum {N : ℕ} (R : Finset (Fin N)) (f : Fin N → ℝ) :
    (∑ x, ind R x * f x) = ∑ x ∈ R, f x := by
  classical
  simp_rw [ind, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp

lemma area_loss_lines {N t r s : ℕ} (hN : 0 < N) (hhalf : N ≤ 2*t) (hs : s ≤ N)
    (P : Pairs (Fin N) r s) (C : Circuit)
    (hC : ∀ x y, C.eval (oneEach x y) = decide (x ∈ P.1.val ∨ y ∈ P.2.val)) :
    let A := (r+s)*N-r*s
    let V := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ) : ℝ)*(A : ℝ)/(N : ℝ)
    gridArea (N := N) C = A ∧
      ∀ T : Graph N, reg t T → (gridLoss C T : ℝ) =
        V + 2*(score P (fun x y => bit ℚ (T x y)) ((t : ℚ)*r*s/N) : ℝ) := by
  classical
  let U := ind P.1.val
  let W := ind P.2.val
  have hsU : (∑ x, U x) = (r : ℝ) := by
    simpa [U,P.1.property,nsmul_eq_mul] using ind_sum P.1.val (fun _ => 1)
  have hsW : (∑ y, W y) = (s : ℝ) := by
    simpa [W,P.2.property,nsmul_eq_mul] using ind_sum P.2.val (fun _ => 1)
  have eU : (∑ x, ∑ _y : Fin N, U x) = (r : ℝ)*N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, hsU, mul_comm]
  have eW : (∑ _x : Fin N, ∑ y, W y) = (s : ℝ)*N := by
    simp only [hsW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  have eUW : (∑ x, ∑ y, U x * W y) = (r : ℝ)*s := by
    simp_rw [← Finset.mul_sum, hsW, ← Finset.sum_mul, hsU]
  have Acast : ((((r+s)*N-r*s : ℕ)) : ℝ) = ((r : ℝ)+s)*N-r*s := by
    have hle : r*s ≤ (r+s)*N := (Nat.mul_le_mul_left _ hs).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
    push_cast [Nat.cast_sub hle]
    rfl
  have hbit (x y : Fin N) : bit ℝ (C.eval (oneEach x y)) = U x + W y - U x * W y := by
    rw [hC]
    by_cases h₁ : x ∈ P.1.val <;> by_cases h₂ : y ∈ P.2.val <;> norm_num [U,W,bit,ind,h₁,h₂]
  have areaCalc : (gridArea (N := N) C : ℝ) = ((r : ℝ)+s)*N-r*s := by
    simp only [gridArea, ← bit_sum_card (fun z : Fin N × Fin N => C.eval (oneEach z.1 z.2)),
      Fintype.sum_prod_type, hbit, Finset.sum_add_distrib, Finset.sum_sub_distrib, eU, eW, eUW]
    ring
  dsimp only
  refine ⟨by rw [← Acast] at areaCalc; exact_mod_cast areaCalc, ?_⟩
  intro T hT
  let Z (x y : Fin N) := bit ℝ (T x y)
  have margin_row (x : Fin N) : ∑ y, Z x y = (t : ℝ) := by simp [Z,bit_sum_card,hT.1]
  have margin_col (y : Fin N) : ∑ x, Z x y = (t : ℝ) := by simp [Z,bit_sum_card,hT.2]
  have zsum : (∑ x, ∑ y, Z x y) = (N : ℝ)*t := by
    simp [margin_row, nsmul_eq_mul]
  have uZ : (∑ x, ∑ y, U x * Z x y) = (r : ℝ)*t := by
    simp_rw [← Finset.mul_sum, margin_row, ← Finset.sum_mul, hsU]
  have wZ : (∑ x, ∑ y, W y * Z x y) = (s : ℝ)*t := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, margin_col, ← Finset.sum_mul, hsW]
  have uwZ : (∑ x, ∑ y, U x * (W y * Z x y)) = ∑ x ∈ P.1.val, ∑ y ∈ P.2.val, Z x y := by
    simp_rw [← Finset.mul_sum, W, ind_sum, U, ind_sum]
  have lossPoint (x y : Fin N) : bit ℝ (decide (C.eval (oneEach x y) ≠ T x y)) =
      Z x y + bit ℝ (C.eval (oneEach x y)) - 2*(U x * Z x y + W y * Z x y - U x * (W y * Z x y)) := by
    rw [hC]
    by_cases h₁ : x ∈ P.1.val <;> by_cases h₂ : y ∈ P.2.val <;>
      cases h₃ : T x y <;> norm_num [Z,U,W,bit,ind,h₁,h₂,h₃]
  have lossCalc : (gridLoss C T : ℝ) = (N : ℝ)*t + (((r+s)*N-r*s : ℕ) : ℝ) -
      2*((r : ℝ)*t + (s : ℝ)*t - ∑ x ∈ P.1.val, ∑ y ∈ P.2.val, Z x y) := by
    have ee := bit_sum_card (K := ℝ) (fun z : Fin N × Fin N => decide (C.eval (oneEach z.1 z.2) ≠ T z.1 z.2))
    simp only [Fintype.sum_prod_type, decide_eq_true_eq] at ee
    change _ = (gridLoss C T : ℝ) at ee
    have ac : (∑ x : Fin N, ∑ y : Fin N, bit ℝ (C.eval (oneEach x y))) = (gridArea (N := N) C : ℝ) := by
      rw [← Fintype.sum_prod_type (fun xy : Fin N × Fin N => bit ℝ (C.eval (oneEach xy.1 xy.2))),
        bit_sum_card]; rfl
    rw [← ee]
    calc
      _ = ∑ x, ∑ y, (Z x y + bit ℝ (C.eval (oneEach x y)) -
        2*(U x * Z x y + W y * Z x y - U x * (W y * Z x y))) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          exact lossPoint x y
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [zsum, ac, areaCalc, ← Acast]
        simp only [← Finset.mul_sum] at uZ uwZ
        rw [uZ,wZ,uwZ]
  have castbit (v : Bool) : ((bit ℚ v : ℚ) : ℝ) = bit ℝ v := by cases v <;> norm_num [bit]
  have castcost : ((score P (fun x y => bit ℚ (T x y)) ((t : ℚ)*r*s/N) : ℚ) : ℝ) =
      (∑ x ∈ P.1.val, ∑ y ∈ P.2.val, Z x y) - (t : ℝ)*r*s/N := by
    simp only [score, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, castbit, Z]
  rw [lossCalc, castcost, Acast]
  push_cast [Nat.cast_sub hhalf]
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  ring

end Converse

namespace Converse
open scoped BigOperators
open Tests33671
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents (oneEach)

lemma circuit_mixture {N t g r s m : ℕ} (hhalf : N < 2*t) (ht : t < N)
    (hr : 0 < r) (hrs : r ≤ s) (hrsg : r+s = g+1) (hrsN : r*s < N)
    (hm : m ≤ (N-1)^2) (Q : Fin m → Graph N) (hQ : ∀ j, reg t (Q j)) :
    let A := (g+1)*N-r*s
    let V := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ) : ℝ)*(A : ℝ)/(N : ℝ)
    let c := Nat.gcd (N / Nat.gcd N r) (N / Nat.gcd N s)
    ∃ (M : ℕ) (D : Fin M → Circuit), 0 < M ∧
      ((∃ u : ℕ, c = 2^u) → ∃ u : ℕ, M = 2^u) ∧
      (∀ i, (ReadsBack (N+N) (D i) ∧ (D i).output < N+N+(D i).size ∧
          (∀ gate ∈ (D i).gates, gate.inputs.length ≤ 2 ∧
            (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
          (D i).size ≤ g ∧ gridArea (N := N) (D i) ≤ A) ∧
        gridArea (N := N) (D i) = A ∧ ∀ gate ∈ (D i).gates, gate.op = .or) ∧
      (∀ j, (∑ i, (gridLoss (D i) (Q j) : ℝ)) ≤ (M : ℝ)*V) ∧
      ∃ T : Graph N, reg t T ∧ (M : ℝ)*V < ∑ i, (gridLoss (D i) T : ℝ) := by
  classical
  have hN : N ≠ 0 := by omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hn : 0 < n := by omega
  have ht₀ : 0 < t := by omega
  have hs₀ : 0 < s := by omega
  have hsN : s < n+1 := by
    have he := Nat.mul_le_mul_right s (show 1 ≤ r by omega)
    omega
  have hrN : r < n+1 := hrs.trans_lt hsN
  have hm' : m ≤ n^2 := by simpa using hm
  obtain ⟨M,P,hM,hPow,hPQ,T,hT,hPT⟩ := regular_mixture hn ht₀ ht hr hs₀ hrN hsN hm' Q hQ
  have hOr (i : Fin M) : ∃ C : Circuit, ReadsBack ((n+1)+(n+1)) C ∧
      C.output < (n+1)+(n+1)+C.size ∧ C.size = g ∧
      (∀ gate ∈ C.gates, gate.op = .or ∧ gate.inputs.length = 2) ∧
      ∀ x y, C.eval (oneEach x y) = decide (x ∈ (P i).1.val ∨ y ∈ (P i).2.val) := by
    have hpos : 0 < (P i).1.val.card + (P i).2.val.card := by rw [(P i).1.property,(P i).2.property]; omega
    obtain ⟨C,hB,hO,hS,hG,hC⟩ := or_lines (P i).1.val (P i).2.val hpos
    rw [(P i).1.property,(P i).2.property,hrsg] at hS
    exact ⟨C,hB,hO,Nat.add_right_cancel hS,hG,hC⟩
  choose D hDB hDO hDS hDG hDC using hOr
  let A := (g+1)*(n+1)-r*s
  let V := (((n+1)*t : ℕ) : ℝ) - ((2*t-(n+1) : ℕ) : ℝ)*(A : ℝ)/((n+1 : ℕ) : ℝ)
  let e (H : Graph (n+1)) (i : Fin M) := score (P i) (fun x y => bit ℚ (H x y)) ((t : ℚ)*r*s/(n+1))
  have hAL (i : Fin M) := area_loss_lines (show 0 < n+1 by omega) hhalf.le hsN.le (P i) (D i) (hDC i)
  simp only [hrsg] at hAL
  have htotal (H : Graph (n+1)) (hH : reg t H) :
      (∑ i, (gridLoss (D i) H : ℝ)) = (M : ℝ)*V + 2*((∑ i, e H i : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    calc
      _ = ∑ i, (V + 2*((e H i : ℚ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [V,A,e,Nat.cast_add,Nat.cast_one] using (hAL i).2 H hH
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [nsmul_eq_mul]
  refine ⟨M,D,hM,hPow,?_,?_,T,hT,?_⟩
  · intro i
    have ha := (hAL i).1
    refine ⟨⟨hDB i,hDO i,fun gate hg => ?_,(hDS i).le,ha.le⟩,ha,fun gate hg => (hDG i gate hg).1⟩
    exact ⟨(hDG i gate hg).2.le,Or.inl (hDG i gate hg).1⟩
  · intro j
    change _ ≤ (M : ℝ)*V
    rw [htotal _ (hQ j)]
    have h0 : (∑ i, e (Q j) i) ≤ 0 := hPQ j
    have heR : ((∑ i, e (Q j) i : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h0
    linarith
  · change (M : ℝ)*V < _
    rw [htotal _ hT]
    have h0 : 0 < ∑ i, e T i := hPT
    have heR : 0 < ((∑ i, e T i : ℚ) : ℝ) := by exact_mod_cast h0
    linarith

end Converse

end PEqualNP.Outside.L_meta_33671

open scoped BigOperators

theorem PEqualNP.Outside.L_meta_33671 : (∀ N t : ℕ, N < 2*t → t < N →
  let X := Fin N
  let L := 2*N*(N-1)
  let graph := X → X → Bool
  let reg := fun (T : graph) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) => ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card
  let loss := fun (C : Circ) (T : graph) => ((Finset.univ : Finset (X × X)).filter
    (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
  ∃ test : Fin L → graph, (∀ i, reg (test i)) ∧
    ∀ (g r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N → 2*g+1 < N →
      let A := (g+1)*N-r*s
      let a := 2*t-N
      let V := ((N*t : ℕ) : ℝ) - (a : ℝ)*(A : ℝ)/(N : ℝ)
      let fits := fun (C : Circ) =>
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
        (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
          (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
        C.size ≤ g ∧ area C ≤ A
      let lines := fun (C : Circ) => ∃ R S : Finset X, R.card+S.card = g+1 ∧
        ∀ x y, tab C x y = decide (x ∈ R ∨ y ∈ S)
      let c := Nat.gcd (N / Nat.gcd N r) (N / Nat.gcd N s)
      (∀ (M : ℕ) (D : Fin M → Circ) (w : Fin M → ℝ) (h : ℝ),
        (∀ i, fits (D i) ∧ 0 ≤ w i) → (∑ i, w i) = 1 → 0 ≤ h →
        let err := fun T => ∑ i, w i*(loss (D i) T : ℝ)
        (∀ j, err (test j) ≤ V+h) →
          (∀ T, reg T → err T ≤ V+(((N-1)*t*(N-t) : ℕ) : ℝ)*h) ∧
          (a : ℝ)*((N-r*s : ℕ) : ℝ)*
            (∑ i, @ite ℝ (lines (D i)) (Classical.propDecidable _) 0 (w i)) ≤ (N : ℝ)*h) ∧
      ∀ (m : ℕ) (Q : Fin m → graph), m ≤ (N-1)^2 → (∀ j, reg (Q j)) →
        ∃ (M : ℕ) (D : Fin M → Circ), 0 < M ∧
          ((∃ u : ℕ, c = 2^u) → ∃ u : ℕ, M = 2^u) ∧
          (∀ i, fits (D i) ∧ area (D i) = A ∧ ∀ gate ∈ (D i).gates, gate.op = .or) ∧
          (∀ j, (∑ i, (loss (D i) (Q j) : ℝ)) ≤ (M : ℝ)*V) ∧
          ∃ T, reg T ∧ (M : ℝ)*V < ∑ i, (loss (D i) T : ℝ)) := by
  intro N t hhalf ht
  obtain ⟨test, htreg, hupper⟩ := PEqualNP.Outside.L_meta_33671.Tests33671.tests_upper hhalf ht
  refine ⟨test, htreg, ?_⟩
  intro g r s hr hrs hgs hprod hN
  dsimp only
  constructor
  · intro M D w h hD hw _hh htests
    have badArea (i : Fin M)
        (hn : ¬ PEqualNP.Outside.L_meta_33671.Rigidity.tabLines (@PEqualNP.Outside.L_meta_33671.Rigidity.tab N (D i)) (g+1)) :
        PEqualNP.Outside.L_meta_33671.Rigidity.tabArea (@PEqualNP.Outside.L_meta_33671.Rigidity.tab N (D i)) + (N-r*s) ≤ (g+1)*N-r*s :=
      PEqualNP.Outside.L_meta_33671.Rigidity.circuitDeficit (D i) hr hrs hprod hN (hD i).1.2.2.1
        (hD i).1.2.2.2.1 (hD i).1.2.2.2.2 hn
    exact hupper ((g+1)*N-r*s) (N-r*s) M
      (fun i => @PEqualNP.Outside.L_meta_33671.Rigidity.tab N (D i))
      (fun i => PEqualNP.Outside.L_meta_33671.Rigidity.tabLines (@PEqualNP.Outside.L_meta_33671.Rigidity.tab N (D i)) (g+1)) w h
      (fun i => ⟨(hD i).1.2.2.2.2, (hD i).2⟩) badArea hw htests
  · intro m Q hm hQ
    exact PEqualNP.Outside.L_meta_33671.Converse.circuit_mixture hhalf ht hr hrs hgs hprod hm Q hQ
