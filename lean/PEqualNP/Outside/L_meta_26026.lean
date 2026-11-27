import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_meta_26026_aux

def sgn (b : Bool) : ℚ := if b then -1 else 1

lemma sgn_xor (b1 b2 : Bool) : sgn (Bool.xor b1 b2) = sgn b1 * sgn b2 := by
  cases b1 <;> cases b2 <;> norm_num [sgn]

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> norm_num [sgn]

lemma ind_ne (b1 b2 : Bool) :
    (if b1 ≠ b2 then (2 : ℚ) else 0) = 1 - sgn b1 * sgn b2 := by
  cases b1 <;> cases b2 <;> norm_num [sgn]

lemma sgn_mul_le_abs (b : Bool) (q : ℚ) : sgn b * q ≤ |q| := by
  cases b
  · simpa [sgn] using le_abs_self q
  · simpa [sgn] using neg_le_abs q

lemma sgn_decide_lt_mul (q : ℚ) : sgn (decide (q < 0)) * q = |q| := by
  by_cases h : q < 0
  · simp [sgn, h, abs_of_neg h]
  · have hnn : 0 ≤ q := not_lt.mp h
    simp [sgn, h, abs_of_nonneg hnn]

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : x.val < 2 := ZMod.val_lt x
  have hv : x.val = 0 ∨ x.val = 1 := by omega
  rcases hv with h0 | h1
  · left
    exact (ZMod.val_eq_zero x).mp h0
  · right
    have hx : (x.val : ZMod 2) = x := ZMod.natCast_zmod_val x
    rw [← hx, h1]
    rfl

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

lemma sgn_zmod2_add (x y : ZMod 2) :
    sgn (decide (x + y = 1)) = sgn (decide (x = 1)) * sgn (decide (y = 1)) := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [sgn]

lemma sgn_zmod2_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (decide ((∑ i ∈ s, f i) = 1)) = ∏ i ∈ s, sgn (decide (f i = 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [sgn]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_zmod2_add, ih]

def dotVal {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (z : Fin k → ZMod 2) (j : Fin m) : ZMod 2 :=
  ∑ i : Fin k, z i * v j i

def dotBit {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (z : Fin k → ZMod 2) (j : Fin m) : Bool :=
  decide (dotVal v z j = 1)

def sumG {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (G : Finset (Fin m)) (z : Fin k → ZMod 2) : ℚ :=
  ∑ j ∈ G, sgn (c j) * sgn (dotBit v z j)

def M {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (G : Finset (Fin m)) : ℚ :=
  (∑ z : Fin k → ZMod 2, |sumG v c G z|) / ((2 ^ k : ℕ) : ℚ)

lemma M_empty {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool) :
    M v c ∅ = 0 := by
  simp [M, sumG]

lemma M_nonneg {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (G : Finset (Fin m)) : 0 ≤ M v c G := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · positivity

lemma M_union_le {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (G1 G2 : Finset (Fin m)) (hdisj : Disjoint G1 G2) :
    M v c (G1 ∪ G2) ≤ M v c G1 + M v c G2 := by
  unfold M
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  simp only [sumG, Finset.sum_union hdisj]
  exact abs_add_le _ _

def fiber {m l : ℕ} (label : Fin m → Fin l) (t : Fin l) : Finset (Fin m) :=
  Finset.univ.filter fun j => label j = t

lemma sum_over_fibers {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid R]
    (label : α → β) (f : α → R) :
    ∑ a : α, f a = ∑ b : β, ∑ a ∈ Finset.univ.filter (fun a => label a = b), f a := by
  rw [Finset.sum_fiberwise]

def lossFn {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool) : ℕ :=
  ((Finset.univ : Finset ((Fin k → ZMod 2) × Fin m)).filter (fun z =>
    out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
      (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card

def optOut {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (label : Fin m → Fin l) (z : Fin k → ZMod 2) (t : Fin l) : Bool :=
  decide (sgn (r z) * sumG v c (fiber label t) z < 0)

lemma card_vec_zmod2 (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp [ZMod.card]

lemma two_mul_loss_eq {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool)
    (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool) :
    2 * (lossFn v r c label out : ℚ) =
      ((2 ^ k : ℕ) : ℚ) * (m : ℚ) -
      ∑ z : Fin k → ZMod 2, ∑ t : Fin l,
        sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z) := by
  have h1 : 2 * (lossFn v r c label out : ℚ) =
      ∑ z : (Fin k → ZMod 2) × Fin m,
        if out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2)) (dotBit v z.1 z.2)
        then (2 : ℚ) else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl
  rw [h1, Fintype.sum_prod_type]
  have h2 : ∀ z : Fin k → ZMod 2,
      (∑ j : Fin m,
        if out z (label j) ≠ Bool.xor (Bool.xor (r z) (c j)) (dotBit v z j)
        then (2 : ℚ) else 0) =
      (m : ℚ) - ∑ t : Fin l, sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z) := by
    intro z
    calc
      (∑ j : Fin m,
          if out z (label j) ≠ Bool.xor (Bool.xor (r z) (c j)) (dotBit v z j)
          then (2 : ℚ) else 0)
        = ∑ j : Fin m, (1 - sgn (out z (label j)) * (sgn (r z) * (sgn (c j) * sgn (dotBit v z j)))) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [ind_ne, sgn_xor, sgn_xor]
          ring
      _ = (m : ℚ) - ∑ j : Fin m, sgn (out z (label j)) * (sgn (r z) * (sgn (c j) * sgn (dotBit v z j))) := by
          rw [Finset.sum_sub_distrib]
          simp
      _ = (m : ℚ) - ∑ t : Fin l, sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z) := by
          congr 1
          rw [sum_over_fibers label]
          apply Finset.sum_congr rfl
          intro t _
          rw [sumG, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hlab : label j = t := (Finset.mem_filter.mp hj).2
          rw [hlab]
  simp_rw [h2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_vec_zmod2, nsmul_eq_mul]

lemma loss_ge_M {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool)
    (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool) :
    ((2 ^ k : ℕ) : ℚ) * ((m : ℚ) - ∑ t : Fin l, M v c (fiber label t)) ≤
      2 * (lossFn v r c label out : ℚ) := by
  rw [two_mul_loss_eq]
  have hsum :
      ∑ z : Fin k → ZMod 2, ∑ t : Fin l,
        sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z) ≤
      ((2 ^ k : ℕ) : ℚ) * ∑ t : Fin l, M v c (fiber label t) := by
    have hstep :
        ∑ z : Fin k → ZMod 2, ∑ t : Fin l,
          sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z) ≤
        ∑ z : Fin k → ZMod 2, ∑ t : Fin l, |sumG v c (fiber label t) z| := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro t _
      calc
        sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z)
          ≤ |sgn (r z) * sumG v c (fiber label t) z| := sgn_mul_le_abs _ _
        _ = |sumG v c (fiber label t) z| := by rw [abs_mul, abs_sgn, one_mul]
    calc
      ∑ z : Fin k → ZMod 2, ∑ t : Fin l,
        sgn (out z t) * (sgn (r z) * sumG v c (fiber label t) z)
        ≤ ∑ z : Fin k → ZMod 2, ∑ t : Fin l, |sumG v c (fiber label t) z| := hstep
      _ = ∑ t : Fin l, ∑ z : Fin k → ZMod 2, |sumG v c (fiber label t) z| := Finset.sum_comm
      _ = ((2 ^ k : ℕ) : ℚ) * ∑ t : Fin l, M v c (fiber label t) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          unfold M
          have hpos : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
          field_simp [hpos]
  linarith

lemma loss_optOut_eq {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool)
    (label : Fin m → Fin l) :
    2 * (lossFn v r c label (optOut v r c label) : ℚ) =
      ((2 ^ k : ℕ) : ℚ) * ((m : ℚ) - ∑ t : Fin l, M v c (fiber label t)) := by
  rw [two_mul_loss_eq]
  have hsum :
      ∑ z : Fin k → ZMod 2, ∑ t : Fin l,
        sgn (optOut v r c label z t) * (sgn (r z) * sumG v c (fiber label t) z) =
      ((2 ^ k : ℕ) : ℚ) * ∑ t : Fin l, M v c (fiber label t) := by
    have hstep :
        ∑ z : Fin k → ZMod 2, ∑ t : Fin l,
          sgn (optOut v r c label z t) * (sgn (r z) * sumG v c (fiber label t) z) =
        ∑ z : Fin k → ZMod 2, ∑ t : Fin l, |sumG v c (fiber label t) z| := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro t _
      unfold optOut
      rw [sgn_decide_lt_mul, abs_mul, abs_sgn, one_mul]
    rw [hstep, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold M
    have hpos : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp [hpos]
  linarith

lemma sum_zmod2_dot_eq_zero {k : ℕ} (u : Fin k → ZMod 2) (hu : u ≠ 0) :
    (∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, z i * u i) = 1))) = 0 := by
  have hex : ∃ i0 : Fin k, u i0 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hu
    ext i
    exact hall i
  rcases hex with ⟨i0, hi0⟩
  have hu1 : u i0 = 1 := by
    rcases zmod2_cases (u i0) with h0 | h1
    · exact False.elim (hi0 h0)
    · exact h1
  let τ : (Fin k → ZMod 2) ≃ (Fin k → ZMod 2) :=
    { toFun := fun z => Function.update z i0 (z i0 + 1)
      invFun := fun z => Function.update z i0 (z i0 + 1)
      left_inv := fun z => by
        ext i
        by_cases h : i = i0
        · subst h
          simp [add_assoc, zmod2_add_self]
        · simp [h]
      right_inv := fun z => by
        ext i
        by_cases h : i = i0
        · subst h
          simp [add_assoc, zmod2_add_self]
        · simp [h] }
  have hflip : ∀ z : Fin k → ZMod 2,
      sgn (decide ((∑ i : Fin k, τ z i * u i) = 1)) =
        - sgn (decide ((∑ i : Fin k, z i * u i) = 1)) := by
    intro z
    have hdot : (∑ i : Fin k, τ z i * u i) = (∑ i : Fin k, z i * u i) + 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      have hrest :
          ∑ i ∈ Finset.univ.erase i0, τ z i * u i =
          ∑ i ∈ Finset.univ.erase i0, z i * u i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
        simp [τ, hne]
      rw [hrest]
      have hself : τ z i0 * u i0 = z i0 * u i0 + 1 := by
        simp [τ, hu1]
      rw [hself]
      ring
    rw [hdot, sgn_zmod2_add]
    have h1 : sgn (decide ((1 : ZMod 2) = 1)) = -1 := by simp [sgn]
    rw [h1]
    ring
  have hsum :
      (∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, z i * u i) = 1))) =
      -(∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, z i * u i) = 1))) := by
    calc
      (∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, z i * u i) = 1)))
        = ∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, τ z i * u i) = 1)) := by
            exact (Equiv.sum_comp τ (fun z => sgn (decide ((∑ i : Fin k, z i * u i) = 1)))).symm
      _ = ∑ z : Fin k → ZMod 2, - sgn (decide ((∑ i : Fin k, z i * u i) = 1)) := by
            apply Finset.sum_congr rfl
            intro z _
            exact hflip z
      _ = -(∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, z i * u i) = 1))) := by
            rw [Finset.sum_neg_distrib]
  linarith

def R (h : ℕ) : ℚ :=
  (∑ x : Fin h → Bool, |∑ i : Fin h, sgn (x i)|) / ((2 ^ h : ℕ) : ℚ)

lemma M_eq_R {k m B : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (hInd : ∀ S : Finset (Fin m), 0 < S.card → S.card % 2 = 0 →
      S.card ≤ B → (∑ j ∈ S, v j) ≠ 0)
    (G : Finset (Fin m)) (hG : G.card ≤ B) :
    M v c G = R G.card := by
  let h := G.card
  let e : Fin h ≃ G := G.equivFin.symm
  let ψ : Bool × (Fin k → ZMod 2) → (Fin h → Bool) :=
    fun w i => Bool.xor w.1 (Bool.xor (c (e i).1) (dotBit v w.2 (e i).1))
  have hsum_lift :
      (∑ w : Bool × (Fin k → ZMod 2), |∑ i : Fin h, sgn (ψ w i)|) =
      2 * ∑ z : Fin k → ZMod 2, |sumG v c G z| := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ b : Bool,
        (∑ z : Fin k → ZMod 2, |∑ i : Fin h, sgn (ψ (b, z) i)|) =
        ∑ z : Fin k → ZMod 2, |sumG v c G z| := by
      intro b
      apply Finset.sum_congr rfl
      intro z _
      have hterm : (∑ i : Fin h, sgn (ψ (b, z) i)) = sgn b * sumG v c G z := by
        calc
          ∑ i : Fin h, sgn (ψ (b, z) i)
            = ∑ i : Fin h, sgn b * (sgn (c (e i).1) * sgn (dotBit v z (e i).1)) := by
                apply Finset.sum_congr rfl
                intro i _
                simp only [ψ, sgn_xor]
          _ = sgn b * ∑ i : Fin h, sgn (c (e i).1) * sgn (dotBit v z (e i).1) := by
                rw [← Finset.mul_sum]
          _ = sgn b * ∑ x : G, sgn (c x.1) * sgn (dotBit v z x.1) := by
                congr 1
                exact Equiv.sum_comp e (fun x : G => sgn (c x.1) * sgn (dotBit v z x.1))
          _ = sgn b * sumG v c G z := by
                congr 1
                rw [sumG]
                exact Finset.sum_coe_sort G (fun j => sgn (c j) * sgn (dotBit v z j))
      rw [hterm, abs_mul, abs_sgn, one_mul]
    rw [Fintype.sum_bool, hinner true, hinner false]
    ring
  have hfiber : ∀ target : Fin h → Bool,
      ((Finset.univ.filter (fun w : Bool × (Fin k → ZMod 2) => ψ w = target)).card : ℚ) *
        ((2 ^ h : ℕ) : ℚ) =
      2 * ((2 ^ k : ℕ) : ℚ) := by
    intro target
    let P : Bool × (Fin k → ZMod 2) → ℚ :=
      fun w => ∏ i : Fin h, (sgn (ψ w i) * sgn (target i) + 1)
    have hP_eval : ∀ w : Bool × (Fin k → ZMod 2),
        P w = if ψ w = target then ((2 ^ h : ℕ) : ℚ) else 0 := by
      intro w
      by_cases hw : ψ w = target
      · simp only [P, hw, ↓reduceIte]
        calc
          ∏ i : Fin h, (sgn (target i) * sgn (target i) + 1)
            = ∏ _i : Fin h, (2 : ℚ) := by
                apply Finset.prod_congr rfl
                intro i _
                rw [sgn_sq]
                norm_num
          _ = ((2 ^ h : ℕ) : ℚ) := by
                simp
      · simp only [hw, ↓reduceIte]
        have hex : ∃ i0 : Fin h, ψ w i0 ≠ target i0 := by
          by_contra hall
          push Not at hall
          apply hw
          ext i
          exact hall i
        rcases hex with ⟨i0, hi0⟩
        apply Finset.prod_eq_zero (Finset.mem_univ i0)
        cases h1 : ψ w i0 <;> cases h2 : target i0 <;> simp_all [sgn]
    have hlhs :
        (∑ w : Bool × (Fin k → ZMod 2), P w) =
        ((Finset.univ.filter (fun w : Bool × (Fin k → ZMod 2) => ψ w = target)).card : ℚ) *
          ((2 ^ h : ℕ) : ℚ) := by
      simp_rw [hP_eval]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [← hlhs]
    have hexpand : ∀ w : Bool × (Fin k → ZMod 2),
        P w = ∑ T : Finset (Fin h), ∏ i ∈ T, (sgn (ψ w i) * sgn (target i)) := by
      intro w
      simpa [P] using Finset.prod_add_one (s := (Finset.univ : Finset (Fin h)))
        (f := fun i => sgn (ψ w i) * sgn (target i))
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    have hT_eval : ∀ T : Finset (Fin h),
        (∑ w : Bool × (Fin k → ZMod 2), ∏ i ∈ T, (sgn (ψ w i) * sgn (target i))) =
        if T = ∅ then 2 * ((2 ^ k : ℕ) : ℚ) else 0 := by
      intro T
      have hfactor :
          (∑ w : Bool × (Fin k → ZMod 2), ∏ i ∈ T, (sgn (ψ w i) * sgn (target i))) =
          (∏ i ∈ T, (sgn (c (e i).1) * sgn (target i))) *
            ((∑ b : Bool, ∏ _i ∈ T, sgn b) *
             (∑ z : Fin k → ZMod 2, ∏ i ∈ T, sgn (dotBit v z (e i).1))) := by
        rw [Fintype.sum_prod_type]
        calc
          ∑ b : Bool, ∑ z : Fin k → ZMod 2, ∏ i ∈ T, (sgn (ψ (b, z) i) * sgn (target i))
            = ∑ b : Bool, ∑ z : Fin k → ZMod 2,
                (∏ i ∈ T, (sgn (c (e i).1) * sgn (target i))) *
                  ((∏ _i ∈ T, sgn b) * (∏ i ∈ T, sgn (dotBit v z (e i).1))) := by
                apply Finset.sum_congr rfl
                intro b _
                apply Finset.sum_congr rfl
                intro z _
                rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
                apply Finset.prod_congr rfl
                intro i _
                simp only [ψ, sgn_xor]
                ring
          _ = (∏ i ∈ T, (sgn (c (e i).1) * sgn (target i))) *
                ∑ b : Bool, ∑ z : Fin k → ZMod 2,
                  (∏ _i ∈ T, sgn b) * (∏ i ∈ T, sgn (dotBit v z (e i).1)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro b _
                rw [Finset.mul_sum]
          _ = (∏ i ∈ T, (sgn (c (e i).1) * sgn (target i))) *
                ((∑ b : Bool, ∏ _i ∈ T, sgn b) *
                 (∑ z : Fin k → ZMod 2, ∏ i ∈ T, sgn (dotBit v z (e i).1))) := by
                congr 1
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro b _
                rw [Finset.mul_sum]
      rw [hfactor]
      by_cases hT0 : T = ∅
      · subst hT0
        simp
      · simp only [hT0, ↓reduceIte]
        by_cases hpar : T.card % 2 = 0
        · have hz0 : (∑ z : Fin k → ZMod 2, ∏ i ∈ T, sgn (dotBit v z (e i).1)) = 0 := by
            let emb : Fin h ↪ Fin m :=
              ⟨fun i => (e i).1, fun i1 i2 hij => e.injective (Subtype.ext hij)⟩
            let S : Finset (Fin m) := T.map emb
            have hScard : S.card = T.card := Finset.card_map emb
            have hSpos : 0 < S.card := by
              rw [hScard]
              exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT0)
            have hSeven : S.card % 2 = 0 := by rw [hScard]; exact hpar
            have hSle : S.card ≤ B := by
              rw [hScard]
              calc
                T.card ≤ (Finset.univ : Finset (Fin h)).card := Finset.card_le_univ T
                _ = h := Fintype.card_fin h
                _ ≤ B := hG
            have hu : (∑ j ∈ S, v j) ≠ 0 := hInd S hSpos hSeven hSle
            have hsum_eq :
                (∑ z : Fin k → ZMod 2, ∏ i ∈ T, sgn (dotBit v z (e i).1)) =
                ∑ z : Fin k → ZMod 2, sgn (decide ((∑ r : Fin k, z r * (∑ j ∈ S, v j) r) = 1)) := by
              apply Finset.sum_congr rfl
              intro z _
              simp only [dotBit]
              rw [← sgn_zmod2_sum]
              congr 3
              calc
                ∑ i ∈ T, dotVal v z (e i).1
                  = ∑ i ∈ T, ∑ r : Fin k, z r * v (e i).1 r := rfl
                _ = ∑ r : Fin k, ∑ i ∈ T, z r * v (e i).1 r := Finset.sum_comm
                _ = ∑ r : Fin k, z r * (∑ i ∈ T, v (e i).1 r) := by
                      apply Finset.sum_congr rfl
                      intro r _
                      rw [← Finset.mul_sum]
                _ = ∑ r : Fin k, z r * (∑ j ∈ S, v j) r := by
                      apply Finset.sum_congr rfl
                      intro r _
                      congr 1
                      rw [Finset.sum_apply, Finset.sum_map]
                      rfl
            rw [hsum_eq]
            exact sum_zmod2_dot_eq_zero _ hu
          rw [hz0, mul_zero, mul_zero]
        · have hodd : Odd T.card := Nat.odd_iff.mpr (by omega)
          have hb0 : (∑ b : Bool, ∏ _i ∈ T, sgn b) = 0 := by
            rw [Fintype.sum_bool]
            simp only [Finset.prod_const, sgn]
            have hneg : (-1 : ℚ) ^ T.card = -1 := hodd.neg_one_pow
            simp [hneg]
          rw [hb0, zero_mul, mul_zero]
    simp_rw [hT_eval]
    simp
  have hsum_fib :
      (∑ w : Bool × (Fin k → ZMod 2), |∑ i : Fin h, sgn (ψ w i)|) =
      2 * ((2 ^ k : ℕ) : ℚ) * R h := by
    rw [sum_over_fibers ψ]
    have hstep :
        (∑ target : Fin h → Bool,
          ∑ w ∈ Finset.univ.filter (fun w : Bool × (Fin k → ZMod 2) => ψ w = target),
            |∑ i : Fin h, sgn (ψ w i)|) =
        ∑ target : Fin h → Bool,
          ((Finset.univ.filter (fun w : Bool × (Fin k → ZMod 2) => ψ w = target)).card : ℚ) *
            |∑ i : Fin h, sgn (target i)| := by
      apply Finset.sum_congr rfl
      intro target _
      calc
        ∑ w ∈ Finset.univ.filter (fun w => ψ w = target), |∑ i : Fin h, sgn (ψ w i)|
          = ∑ _w ∈ Finset.univ.filter (fun w => ψ w = target), |∑ i : Fin h, sgn (target i)| := by
              apply Finset.sum_congr rfl
              intro w hw
              rw [(Finset.mem_filter.mp hw).2]
        _ = ((Finset.univ.filter (fun w => ψ w = target)).card : ℚ) * |∑ i : Fin h, sgn (target i)| := by
              rw [Finset.sum_const, nsmul_eq_mul]
    rw [hstep]
    have hpos_h : ((2 ^ h : ℕ) : ℚ) ≠ 0 := by positivity
    have hcard_eq : ∀ target : Fin h → Bool,
        ((Finset.univ.filter (fun w : Bool × (Fin k → ZMod 2) => ψ w = target)).card : ℚ) =
        2 * ((2 ^ k : ℕ) : ℚ) / ((2 ^ h : ℕ) : ℚ) := by
      intro target
      have hf := hfiber target
      field_simp [hpos_h] at hf ⊢
      linarith
    simp_rw [hcard_eq]
    rw [← Finset.mul_sum, R]
    ring
  have hpos_k : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hM : 2 * ((2 ^ k : ℕ) : ℚ) * M v c G = 2 * ((2 ^ k : ℕ) : ℚ) * R h := by
    calc
      2 * ((2 ^ k : ℕ) : ℚ) * M v c G
        = 2 * ∑ z : Fin k → ZMod 2, |sumG v c G z| := by
            unfold M
            field_simp [hpos_k]
      _ = ∑ w : Bool × (Fin k → ZMod 2), |∑ i : Fin h, sgn (ψ w i)| := hsum_lift.symm
      _ = 2 * ((2 ^ k : ℕ) : ℚ) * R h := hsum_fib
  have h2k : 2 * ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  exact mul_left_cancel₀ h2k hM

def p (j : ℕ) : ℚ := (Nat.choose (2 * j) j : ℚ) / (4 : ℚ) ^ j

def meanFn (j : ℕ) : ℚ := ((2 * j + 1 : ℕ) : ℚ) * (Nat.choose (2 * j) j : ℚ) / (4 : ℚ) ^ j

lemma meanFn_eq_mul_p (j : ℕ) : meanFn j = ((2 * j + 1 : ℕ) : ℚ) * p j := by
  unfold meanFn p
  ring

def intSum {n : ℕ} (x : Fin n → Bool) : ℤ :=
  ∑ i : Fin n, if x i then (-1 : ℤ) else 1

lemma intSum_cast {n : ℕ} (x : Fin n → Bool) :
    (intSum x : ℚ) = ∑ i : Fin n, sgn (x i) := by
  unfold intSum
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [sgn]

lemma intSum_add_two_cnt {n : ℕ} (x : Fin n → Bool) :
    intSum x + 2 * ((Finset.univ.filter (fun i : Fin n => x i = true)).card : ℤ) = (n : ℤ) := by
  have hcnt :
      2 * ((Finset.univ.filter (fun i : Fin n => x i = true)).card : ℤ) =
      ∑ i : Fin n, if x i = true then (2 : ℤ) else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hcnt, intSum, ← Finset.sum_add_distrib]
  calc
    (∑ i : Fin n, ((if x i then (-1 : ℤ) else 1) + if x i = true then (2 : ℤ) else 0))
      = ∑ _i : Fin n, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _
          cases x i <;> norm_num
    _ = (n : ℤ) := by simp

lemma abs_int_step (s : ℤ) :
    |(s : ℚ) + 1| + |(s : ℚ) - 1| = 2 * |(s : ℚ)| + if s = 0 then 2 else 0 := by
  rcases lt_trichotomy s 0 with hlt | rfl | hgt
  · have hle : s ≤ -1 := by omega
    have hq : (s : ℚ) ≤ -1 := by exact_mod_cast hle
    have hne : s ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    ring
  · norm_num
  · have hge : 1 ≤ s := by omega
    have hq : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hge
    have hne : s ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    ring

lemma R_succ (n : ℕ) :
    R (n + 1) =
      R n + ((Finset.univ.filter (fun x : Fin n → Bool => intSum x = 0)).card : ℚ) /
        ((2 ^ n : ℕ) : ℚ) := by
  have hsum :
      (∑ y : Fin (n + 1) → Bool, |∑ i : Fin (n + 1), sgn (y i)|) =
      2 * (∑ x : Fin n → Bool, |∑ i : Fin n, sgn (x i)|) +
        2 * ((Finset.univ.filter (fun x : Fin n → Bool => intSum x = 0)).card : ℚ) := by
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
    rw [← Equiv.sum_comp e (fun y : Fin (n + 1) → Bool => |∑ i : Fin (n + 1), sgn (y i)|)]
    rw [Fintype.sum_prod_type_right]
    have hstep : ∀ x : Fin n → Bool,
        (∑ b : Bool, |∑ i : Fin (n + 1), sgn (e (b, x) i)|) =
        2 * |∑ i : Fin n, sgn (x i)| + if intSum x = 0 then 2 else 0 := by
      intro x
      rw [Fintype.sum_bool]
      have hT : (∑ i : Fin (n + 1), sgn (e (true, x) i)) = (intSum x : ℚ) - 1 := by
        rw [Fin.sum_univ_succ]
        simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, intSum_cast]
        simp [sgn]
        ring
      have hF : (∑ i : Fin (n + 1), sgn (e (false, x) i)) = (intSum x : ℚ) + 1 := by
        rw [Fin.sum_univ_succ]
        simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, intSum_cast]
        simp [sgn]
        ring
      rw [hT, hF, ← intSum_cast, add_comm]
      exact abs_int_step (intSum x)
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm _ (2 : ℚ)]
  unfold R
  rw [hsum]
  have hpow : ((2 ^ (n + 1) : ℕ) : ℚ) = 2 * ((2 ^ n : ℕ) : ℚ) := by
    push_cast [pow_succ]
    ring
  rw [hpow]
  have hpos : ((2 ^ n : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hpos]

lemma R_even_succ (j : ℕ) : R (2 * j + 2) = R (2 * j + 1) := by
  have h := R_succ (2 * j + 1)
  have hempty :
      (Finset.univ.filter (fun x : Fin (2 * j + 1) → Bool => intSum x = 0)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _ hx
    have hc := intSum_add_two_cnt x
    omega
  rw [hempty] at h
  simpa using h

lemma card_intSum_zero_even (j : ℕ) :
    (Finset.univ.filter (fun x : Fin (2 * j) → Bool => intSum x = 0)).card =
      Nat.choose (2 * j) j := by
  have hbij :
      (Finset.univ.filter (fun x : Fin (2 * j) → Bool => intSum x = 0)).card =
      ((Finset.univ : Finset (Fin (2 * j))).powersetCard j).card := by
    apply Finset.card_bij (fun x _ => Finset.univ.filter (fun i : Fin (2 * j) => x i = true))
    · intro x hx
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      have h0 : intSum x = 0 := (Finset.mem_filter.mp hx).2
      have hc := intSum_add_two_cnt x
      omega
    · intro x1 _ x2 _ hEq
      ext i
      have hm : i ∈ Finset.univ.filter (fun r => x1 r = true) ↔
                i ∈ Finset.univ.filter (fun r => x2 r = true) := by rw [hEq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      cases h1 : x1 i <;> cases h2 : x2 i <;> simp_all
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hc := intSum_add_two_cnt (fun i : Fin (2 * j) => decide (i ∈ S))
        have hflt : (Finset.univ.filter (fun i : Fin (2 * j) => decide (i ∈ S) = true)) = S := by
          ext i
          simp
        rw [hflt, hS.2] at hc
        omega
      · ext i
        simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma R_odd_succ (j : ℕ) : R (2 * j + 1) = R (2 * j) + p j := by
  rw [R_succ, card_intSum_zero_even]
  unfold p
  congr 1
  have hpow : ((2 ^ (2 * j) : ℕ) : ℚ) = (4 : ℚ) ^ j := by
    have : 2 ^ (2 * j) = 4 ^ j := by
      rw [pow_mul]
      norm_num
    exact_mod_cast this
  rw [hpow]

lemma choose_central_step (j : ℕ) :
    (j + 1) * Nat.choose (2 * j + 2) (j + 1) = 2 * (2 * j + 1) * Nat.choose (2 * j) j := by
  have h1 : (2 * j + 1) * Nat.choose (2 * j) j =
      Nat.choose (2 * j + 1) (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq (2 * j) j
  have hsym : Nat.choose (2 * j + 1) j = Nat.choose (2 * j + 1) (j + 1) := by
    have hs := Nat.choose_symm (n := 2 * j + 1) (k := j) (by omega)
    have hsub : 2 * j + 1 - j = j + 1 := by omega
    rw [hsub] at hs
    exact hs.symm
  have h2 : Nat.choose (2 * j + 2) (j + 1) = 2 * Nat.choose (2 * j + 1) (j + 1) := by
    rw [Nat.choose_succ_succ, hsym]
    ring
  rw [h2]
  linarith

lemma p_recurrence (j : ℕ) :
    ((2 * j + 2 : ℕ) : ℚ) * p (j + 1) = ((2 * j + 1 : ℕ) : ℚ) * p j := by
  unfold p
  have hnat : ((j + 1 : ℕ) : ℚ) * (Nat.choose (2 * j + 2) (j + 1) : ℚ) =
      2 * ((2 * j + 1 : ℕ) : ℚ) * (Nat.choose (2 * j) j : ℚ) := by
    exact_mod_cast choose_central_step j
  have h4 : (4 : ℚ) ^ (j + 1) = 4 * (4 : ℚ) ^ j := by rw [pow_succ]; ring
  have hpos : (4 : ℚ) ^ j ≠ 0 := by positivity
  have h2j : 2 * (j + 1) = 2 * j + 2 := by ring
  have h2j2 : ((2 * j + 2 : ℕ) : ℚ) = 2 * ((j + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [h4, h2j, h2j2]
  field_simp [hpos]
  linarith

lemma meanFn_step (j : ℕ) : meanFn (j + 1) = meanFn j + p (j + 1) := by
  rw [meanFn_eq_mul_p, meanFn_eq_mul_p]
  have hrec := p_recurrence j
  have hcast : ((2 * (j + 1) + 1 : ℕ) : ℚ) = ((2 * j + 2 : ℕ) : ℚ) + 1 := by push_cast; ring
  rw [hcast]
  linarith

lemma R_closed_form (j : ℕ) : R (2 * j + 1) = meanFn j ∧ R (2 * j + 2) = meanFn j := by
  induction j with
  | zero =>
    have hR0 : R 0 = 0 := by simp [R]
    have hp0 : p 0 = 1 := by simp [p]
    have hm0 : meanFn 0 = 1 := by simp [meanFn]
    have hR1 : R 1 = 1 := by
      have := R_odd_succ 0
      simpa [hR0, hp0] using this
    have hR2 : R 2 = 1 := by
      have := R_even_succ 0
      simpa [hR1] using this
    exact ⟨by linarith, by linarith⟩
  | succ j ih =>
    have h1 : R (2 * (j + 1) + 1) = meanFn (j + 1) := by
      have hodd := R_odd_succ (j + 1)
      have heq : 2 * (j + 1) = 2 * j + 2 := by omega
      rw [hodd, heq, ih.2, meanFn_step]
    have h2 : R (2 * (j + 1) + 2) = meanFn (j + 1) := by
      rw [R_even_succ (j + 1), h1]
    exact ⟨h1, h2⟩

lemma p_pos (j : ℕ) : 0 < p j := by
  unfold p
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : j ≤ 2 * j)
  · positivity

lemma p_succ_le (j : ℕ) : p (j + 1) ≤ p j := by
  have hrec := p_recurrence j
  have hpos := p_pos j
  have h1 : ((2 * j + 1 : ℕ) : ℚ) ≤ ((2 * j + 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * j + 1 ≤ 2 * j + 2)
  have h2 : (0 : ℚ) < ((2 * j + 2 : ℕ) : ℚ) := by positivity
  nlinarith

lemma p_antitone {i j : ℕ} (h : i ≤ j) : p j ≤ p i := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (p_succ_le _) ih

lemma meanFn_le_line (a j : ℕ) :
    meanFn j ≤ meanFn a + p (a + 1) * ((j : ℚ) - (a : ℚ)) := by
  rcases le_or_gt a j with hle | hlt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction d with
    | zero => simp
    | succ d ih =>
      have hstep : meanFn (a + (d + 1)) = meanFn (a + d) + p (a + d + 1) := by
        simpa [Nat.add_assoc] using meanFn_step (a + d)
      have hp : p (a + d + 1) ≤ p (a + 1) := p_antitone (by omega)
      have ih' := ih (Nat.le_add_right a d)
      rw [hstep]
      push_cast at ih' ⊢
      linarith
  · have haux : ∀ d j : ℕ, j + d = a →
        meanFn j ≤ meanFn a + p (a + 1) * ((j : ℚ) - (a : ℚ)) := by
      intro d
      induction d with
      | zero =>
        intro j hj
        have : j = a := by omega
        subst this
        simp
      | succ d ih =>
        intro j hj
        have ih' := ih (j + 1) (by omega)
        have hstep := meanFn_step j
        have hp : p (a + 1) ≤ p (j + 1) := p_antitone (by omega)
        push_cast at ih'
        linarith
    exact haux (a - j) j (by omega)

lemma cauchy_schwarz_const {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    (∑ x : ι, f x) ^ 2 ≤ (Fintype.card ι : ℚ) * ∑ x : ι, (f x) ^ 2 := by
  have hnn : (0 : ℚ) ≤ ∑ x : ι, ∑ y : ι, (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp :
      (∑ x : ι, ∑ y : ι, (f x - f y) ^ 2) =
      2 * (Fintype.card ι : ℚ) * (∑ x : ι, (f x) ^ 2) - 2 * (∑ x : ι, f x) ^ 2 := by
    have h1 : ∀ x : ι,
        (∑ y : ι, (f x - f y) ^ 2) =
        (Fintype.card ι : ℚ) * (f x) ^ 2 - 2 * f x * (∑ y : ι, f y) + ∑ y : ι, (f y) ^ 2 := by
      intro x
      calc
        ∑ y : ι, (f x - f y) ^ 2
          = ∑ y : ι, ((f x) ^ 2 - 2 * f x * f y + (f y) ^ 2) := by
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ = (∑ _y : ι, (f x) ^ 2) - (∑ y : ι, 2 * f x * f y) + ∑ y : ι, (f y) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (Fintype.card ι : ℚ) * (f x) ^ 2 - 2 * f x * (∑ y : ι, f y) + ∑ y : ι, (f y) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmid : (∑ x : ι, 2 * f x * ∑ y : ι, f y) = 2 * (∑ x : ι, f x) ^ 2 := by
      rw [← Finset.sum_mul]
      have : (∑ x : ι, 2 * f x) = 2 * ∑ x : ι, f x := by rw [← Finset.mul_sum]
      rw [this]
      ring
    rw [hmid]
    ring
  linarith

lemma M_sq_le_card {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (G : Finset (Fin m)) : (M v c G) ^ 2 ≤ (G.card : ℚ) := by
  have hparseval :
      (∑ z : Fin k → ZMod 2, (sumG v c G z) ^ 2) = ((2 ^ k : ℕ) : ℚ) * (G.card : ℚ) := by
    have hexp :
        (∑ z : Fin k → ZMod 2, (sumG v c G z) ^ 2) =
        ∑ j1 ∈ G, ∑ j2 ∈ G,
          sgn (c j1) * sgn (c j2) *
            ∑ z : Fin k → ZMod 2, sgn (dotBit v z j1) * sgn (dotBit v z j2) := by
      calc
        ∑ z : Fin k → ZMod 2, (sumG v c G z) ^ 2
          = ∑ z : Fin k → ZMod 2, ∑ j1 ∈ G, ∑ j2 ∈ G,
              (sgn (c j1) * sgn (c j2)) * (sgn (dotBit v z j1) * sgn (dotBit v z j2)) := by
              apply Finset.sum_congr rfl
              intro z _
              rw [sq, sumG, Finset.sum_mul_sum]
              apply Finset.sum_congr rfl
              intro j1 _
              apply Finset.sum_congr rfl
              intro j2 _
              ring
        _ = ∑ j1 ∈ G, ∑ z : Fin k → ZMod 2, ∑ j2 ∈ G,
              (sgn (c j1) * sgn (c j2)) * (sgn (dotBit v z j1) * sgn (dotBit v z j2)) := by
              rw [Finset.sum_comm]
        _ = ∑ j1 ∈ G, ∑ j2 ∈ G, ∑ z : Fin k → ZMod 2,
              (sgn (c j1) * sgn (c j2)) * (sgn (dotBit v z j1) * sgn (dotBit v z j2)) := by
              apply Finset.sum_congr rfl
              intro j1 _
              rw [Finset.sum_comm]
        _ = ∑ j1 ∈ G, ∑ j2 ∈ G,
              sgn (c j1) * sgn (c j2) *
                ∑ z : Fin k → ZMod 2, sgn (dotBit v z j1) * sgn (dotBit v z j2) := by
              apply Finset.sum_congr rfl
              intro j1 _
              apply Finset.sum_congr rfl
              intro j2 _
              rw [← Finset.mul_sum]
    rw [hexp]
    have horth : ∀ j1 ∈ G, ∀ j2 ∈ G,
        sgn (c j1) * sgn (c j2) *
          (∑ z : Fin k → ZMod 2, sgn (dotBit v z j1) * sgn (dotBit v z j2)) =
        if j1 = j2 then ((2 ^ k : ℕ) : ℚ) else 0 := by
      intro j1 _ j2 _
      by_cases hjj : j1 = j2
      · subst hjj
        simp [sgn_sq]
      · simp only [hjj, ↓reduceIte]
        have hu : v j1 + v j2 ≠ 0 := by
          intro hzero
          apply hjj
          apply v.injective
          ext i
          have hi : v j1 i + v j2 i = 0 := congrFun hzero i
          calc
            v j1 i = v j1 i + (v j1 i + v j2 i) := by rw [hi, add_zero]
            _ = (v j1 i + v j1 i) + v j2 i := by rw [add_assoc]
            _ = v j2 i := by rw [zmod2_add_self, zero_add]
        have hz0 : (∑ z : Fin k → ZMod 2, sgn (dotBit v z j1) * sgn (dotBit v z j2)) = 0 := by
          have heq :
              (∑ z : Fin k → ZMod 2, sgn (dotBit v z j1) * sgn (dotBit v z j2)) =
              ∑ z : Fin k → ZMod 2, sgn (decide ((∑ i : Fin k, z i * (v j1 + v j2) i) = 1)) := by
            apply Finset.sum_congr rfl
            intro z _
            unfold dotBit dotVal
            rw [← sgn_zmod2_add]
            congr 3
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            simp [mul_add]
          rw [heq]
          exact sum_zmod2_dot_eq_zero _ hu
        rw [hz0, mul_zero]
    calc
      ∑ j1 ∈ G, ∑ j2 ∈ G,
        sgn (c j1) * sgn (c j2) *
          ∑ z : Fin k → ZMod 2, sgn (dotBit v z j1) * sgn (dotBit v z j2)
        = ∑ j1 ∈ G, ∑ j2 ∈ G, if j1 = j2 then ((2 ^ k : ℕ) : ℚ) else 0 := by
            apply Finset.sum_congr rfl
            intro j1 hj1
            apply Finset.sum_congr rfl
            intro j2 hj2
            exact horth j1 hj1 j2 hj2
      _ = ∑ j1 ∈ G, ((2 ^ k : ℕ) : ℚ) := by
            apply Finset.sum_congr rfl
            intro j1 hj1
            simp [hj1]
      _ = ((2 ^ k : ℕ) : ℚ) * (G.card : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcs := cauchy_schwarz_const (fun z : Fin k → ZMod 2 => |sumG v c G z|)
  rw [card_vec_zmod2] at hcs
  have hsq_abs : (∑ z : Fin k → ZMod 2, |sumG v c G z| ^ 2) =
      ∑ z : Fin k → ZMod 2, (sumG v c G z) ^ 2 := by
    apply Finset.sum_congr rfl
    intro z _
    exact sq_abs _
  rw [hsq_abs, hparseval] at hcs
  unfold M
  rw [div_pow]
  have hden : (0 : ℚ) < ((2 ^ k : ℕ) : ℚ) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  linarith

lemma four_mul_p_sq_ge_one (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℚ) ≤ 4 * (n : ℚ) * (p n) ^ 2 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · norm_num [p]
    · have hm : 1 ≤ m + 1 := by omega
      have ihm := ih hm
      have hrec := p_recurrence (m + 1)
      have hsq :
          (((2 * (m + 1) + 2 : ℕ) : ℚ) ^ 2) * (4 * ((m + 2 : ℕ) : ℚ) * (p (m + 2)) ^ 2) =
          (((2 * (m + 1) + 1 : ℕ) : ℚ) ^ 2) * (4 * ((m + 2 : ℕ) : ℚ) * (p (m + 1)) ^ 2) := by
        have hp2 :
            (((2 * (m + 1) + 2 : ℕ) : ℚ) * p (m + 2)) ^ 2 =
            (((2 * (m + 1) + 1 : ℕ) : ℚ) * p (m + 1)) ^ 2 := by
          rw [hrec]
        nlinarith
      have hden : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) * (((2 * (m + 1) + 2 : ℕ) : ℚ) ^ 2) := by
        positivity
      have hdiff :
          ((m + 1 : ℕ) : ℚ) * (((2 * (m + 1) + 2 : ℕ) : ℚ) ^ 2) ≤
          ((m + 2 : ℕ) : ℚ) * (((2 * (m + 1) + 1 : ℕ) : ℚ) ^ 2) := by
        push_cast
        nlinarith
      have hmul :
          ((m + 1 : ℕ) : ℚ) * (((2 * (m + 1) + 2 : ℕ) : ℚ) ^ 2) *
            (4 * ((m + 2 : ℕ) : ℚ) * (p (m + 2)) ^ 2) =
          ((m + 2 : ℕ) : ℚ) * (((2 * (m + 1) + 1 : ℕ) : ℚ) ^ 2) *
            (4 * ((m + 1 : ℕ) : ℚ) * (p (m + 1)) ^ 2) := by
        calc
          ((m + 1 : ℕ) : ℚ) * (((2 * (m + 1) + 2 : ℕ) : ℚ) ^ 2) *
              (4 * ((m + 2 : ℕ) : ℚ) * (p (m + 2)) ^ 2)
            = ((m + 1 : ℕ) : ℚ) *
                ((((2 * (m + 1) + 2 : ℕ) : ℚ) ^ 2) *
                  (4 * ((m + 2 : ℕ) : ℚ) * (p (m + 2)) ^ 2)) := by ring
          _ = ((m + 1 : ℕ) : ℚ) *
                ((((2 * (m + 1) + 1 : ℕ) : ℚ) ^ 2) *
                  (4 * ((m + 2 : ℕ) : ℚ) * (p (m + 1)) ^ 2)) := by rw [hsq]
          _ = ((m + 2 : ℕ) : ℚ) * (((2 * (m + 1) + 1 : ℕ) : ℚ) ^ 2) *
                (4 * ((m + 1 : ℕ) : ℚ) * (p (m + 1)) ^ 2) := by ring
      have hpos2 : (0 : ℚ) ≤ ((m + 2 : ℕ) : ℚ) * (((2 * (m + 1) + 1 : ℕ) : ℚ) ^ 2) := by
        positivity
      nlinarith

lemma M_le_line {k m a : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (hInd : ∀ S : Finset (Fin m), 0 < S.card → S.card % 2 = 0 →
      S.card ≤ 16 * (a + 1) → (∑ j ∈ S, v j) ≠ 0)
    (G : Finset (Fin m)) (hGpos : 1 ≤ G.card) :
    M v c G ≤ meanFn a + p (a + 1) * ((((G.card - 1) / 2 : ℕ) : ℚ) - (a : ℚ)) := by
  set j := (G.card - 1) / 2
  by_cases hsmall : G.card ≤ 16 * (a + 1)
  · rw [M_eq_R v c hInd G hsmall]
    have hcase : G.card = 2 * j + 1 ∨ G.card = 2 * j + 2 := by omega
    rcases hcase with h1 | h2
    · rw [h1, (R_closed_form j).1]
      exact meanFn_le_line a j
    · rw [h2, (R_closed_form j).2]
      exact meanFn_le_line a j
  · have hbig : 16 * (a + 1) + 1 ≤ G.card := by omega
    have hj_ge : 8 * (a + 1) ≤ j := by omega
    have hG_le : G.card ≤ 2 * j + 2 := by omega
    have hmean_a : meanFn a = ((2 * a + 2 : ℕ) : ℚ) * p (a + 1) := by
      rw [meanFn_eq_mul_p, ← p_recurrence]
    set rhs := meanFn a + p (a + 1) * ((j : ℚ) - (a : ℚ))
    have hrhs_eq : rhs = p (a + 1) * ((j : ℚ) + (a : ℚ) + 2) := by
      change meanFn a + p (a + 1) * ((j : ℚ) - (a : ℚ)) = _
      rw [hmean_a]
      push_cast
      ring
    have hp_pos' : 0 < p (a + 1) := p_pos (a + 1)
    have hrhs_nn : 0 ≤ rhs := by
      rw [hrhs_eq]
      positivity
    have hp_lb : (1 : ℚ) ≤ 4 * ((a + 1 : ℕ) : ℚ) * (p (a + 1)) ^ 2 :=
      four_mul_p_sq_ge_one (a + 1) (by omega)
    have hquad :
        4 * ((a + 1 : ℕ) : ℚ) * (2 * (j : ℚ) + 2) ≤ ((j : ℚ) + (a : ℚ) + 2) ^ 2 := by
      have hjq : 8 * ((a : ℚ) + 1) ≤ (j : ℚ) := by exact_mod_cast hj_ge
      set d : ℚ := (j : ℚ) - 8 * ((a : ℚ) + 1)
      have hd : 0 ≤ d := by linarith
      have hid :
          ((j : ℚ) + (a : ℚ) + 2) ^ 2 - 4 * ((a + 1 : ℕ) : ℚ) * (2 * (j : ℚ) + 2) =
          17 * (a : ℚ) ^ 2 + 44 * (a : ℚ) + 28 + (10 * (a : ℚ) + 12) * d + d ^ 2 := by
        have hj_def : (j : ℚ) = 8 * ((a : ℚ) + 1) + d := by linarith
        rw [hj_def]
        push_cast
        ring
      have hpos_id : 0 ≤ 17 * (a : ℚ) ^ 2 + 44 * (a : ℚ) + 28 + (10 * (a : ℚ) + 12) * d + d ^ 2 := by
        positivity
      linarith
    have hcard_le : (G.card : ℚ) ≤ 2 * (j : ℚ) + 2 := by exact_mod_cast hG_le
    have hMsq : (M v c G) ^ 2 ≤ (G.card : ℚ) := M_sq_le_card v c G
    have h4a_pos : (0 : ℚ) < 4 * ((a + 1 : ℕ) : ℚ) := by positivity
    have hsq_le : (M v c G) ^ 2 ≤ rhs ^ 2 := by
      have hstep :
          4 * ((a + 1 : ℕ) : ℚ) * (M v c G) ^ 2 ≤ 4 * ((a + 1 : ℕ) : ℚ) * rhs ^ 2 := by
        calc
          4 * ((a + 1 : ℕ) : ℚ) * (M v c G) ^ 2
            ≤ 4 * ((a + 1 : ℕ) : ℚ) * (2 * (j : ℚ) + 2) := by nlinarith
          _ ≤ ((j : ℚ) + (a : ℚ) + 2) ^ 2 := hquad
          _ ≤ (4 * ((a + 1 : ℕ) : ℚ) * (p (a + 1)) ^ 2) * ((j : ℚ) + (a : ℚ) + 2) ^ 2 := by
                nlinarith [sq_nonneg ((j : ℚ) + (a : ℚ) + 2)]
          _ = 4 * ((a + 1 : ℕ) : ℚ) * rhs ^ 2 := by rw [hrhs_eq]; ring
      nlinarith
    have hMnn : 0 ≤ M v c G := M_nonneg v c G
    nlinarith

lemma sum_M_le_bound {k m l : ℕ} (hl : 0 < l) (hlm : l ≤ m)
    (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (hInd : ∀ S : Finset (Fin m), 0 < S.card → S.card % 2 = 0 →
      S.card ≤ 16 * (((m - l) / 2) / l + 1) → (∑ j ∈ S, v j) ≠ 0) :
    ∀ (e : ℕ) (P : Fin l → Finset (Fin m)),
      ((Finset.univ : Finset (Fin l)).filter (fun t => P t = ∅)).card = e →
      (∑ t : Fin l, (P t).card) = m →
      ∑ t : Fin l, M v c (P t) ≤
        ((l - ((m - l) / 2) % l : ℕ) : ℚ) * meanFn (((m - l) / 2) / l) +
        ((((m - l) / 2) % l : ℕ) : ℚ) * meanFn (((m - l) / 2) / l + 1) := by
  set pairs := (m - l) / 2
  set a := pairs / l
  set b := pairs % l
  intro e
  induction e with
  | zero =>
    intro P he hsum_card
    have hne : ∀ t : Fin l, 1 ≤ (P t).card := by
      intro t
      by_contra h0
      have hPt0 : P t = ∅ := Finset.card_eq_zero.mp (by omega)
      have hmem : t ∈ (Finset.univ : Finset (Fin l)).filter (fun t => P t = ∅) := by
        simp [hPt0]
      have hpos : 0 < ((Finset.univ : Finset (Fin l)).filter (fun t => P t = ∅)).card :=
        Finset.card_pos.mpr ⟨t, hmem⟩
      omega
    let jt : Fin l → ℕ := fun t => ((P t).card - 1) / 2
    have hjt_sum : (∑ t : Fin l, jt t) ≤ pairs := by
      have h2 : 2 * (∑ t : Fin l, jt t) + l ≤ m := by
        rw [← hsum_card]
        have hstep : ∀ t : Fin l, 2 * jt t + 1 ≤ (P t).card := by
          intro t
          have := hne t
          simp only [jt]
          omega
        calc
          2 * (∑ t : Fin l, jt t) + l
            = ∑ t : Fin l, (2 * jt t + 1) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                simp
          _ ≤ ∑ t : Fin l, (P t).card := Finset.sum_le_sum fun t _ => hstep t
      omega
    have hdivmod : l * a + b = pairs := Nat.div_add_mod pairs l
    have hblt : b < l := Nat.mod_lt pairs hl
    have hstep_M :
        ∑ t : Fin l, M v c (P t) ≤
        ∑ t : Fin l, (meanFn a + p (a + 1) * ((jt t : ℚ) - (a : ℚ))) := by
      apply Finset.sum_le_sum
      intro t _
      exact M_le_line v c hInd (P t) (hne t)
    have hrhs_simpl :
        (∑ t : Fin l, (meanFn a + p (a + 1) * ((jt t : ℚ) - (a : ℚ)))) =
        (l : ℚ) * meanFn a + p (a + 1) * ((∑ t : Fin l, (jt t : ℚ)) - (l : ℚ) * (a : ℚ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp
    have hjt_q : (∑ t : Fin l, (jt t : ℚ)) ≤ (l : ℚ) * (a : ℚ) + (b : ℚ) := by
      have hnat : (∑ t : Fin l, jt t) ≤ l * a + b := by omega
      exact_mod_cast hnat
    have hp_pos' : 0 < p (a + 1) := p_pos (a + 1)
    have hsub_cast : ((l - b : ℕ) : ℚ) = (l : ℚ) - (b : ℚ) := by
      rw [Nat.cast_sub (le_of_lt hblt)]
    have hmstep := meanFn_step a
    rw [hsub_cast, hmstep]
    have hcomb : ∑ t : Fin l, M v c (P t) ≤
        (l : ℚ) * meanFn a + p (a + 1) * ((∑ t : Fin l, (jt t : ℚ)) - (l : ℚ) * (a : ℚ)) := by
      linarith
    nlinarith
  | succ e ih =>
    intro P he hsum_card
    have hpos_e : 0 < ((Finset.univ : Finset (Fin l)).filter (fun t => P t = ∅)).card := by omega
    rcases Finset.card_pos.mp hpos_e with ⟨t0, ht0_mem⟩
    have ht0 : P t0 = ∅ := (Finset.mem_filter.mp ht0_mem).2
    have hex_ge2 : ∃ t1 : Fin l, 2 ≤ (P t1).card := by
      by_contra hall
      push Not at hall
      have hle1 : ∀ t : Fin l, (P t).card ≤ 1 := fun t => by have := hall t; omega
      have hlt_l : (∑ t : Fin l, (P t).card) < l := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0), ht0, Finset.card_empty, zero_add]
        have hsum_er :
            (∑ t ∈ Finset.univ.erase t0, (P t).card) ≤
            (Finset.univ.erase t0).card := by
          calc
            ∑ t ∈ Finset.univ.erase t0, (P t).card
              ≤ ∑ _t ∈ Finset.univ.erase t0, 1 := Finset.sum_le_sum fun t _ => hle1 t
            _ = (Finset.univ.erase t0).card := by simp
        have hcard_er : (Finset.univ.erase t0).card = l - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ t0), Finset.card_univ, Fintype.card_fin]
        omega
      omega
    rcases hex_ge2 with ⟨t1, ht1_ge2⟩
    have ht1_ne : t1 ≠ t0 := by
      intro hEq
      subst hEq
      rw [ht0] at ht1_ge2
      simp at ht1_ge2
    rcases Finset.card_pos.mp (by omega : 0 < (P t1).card) with ⟨x, hx⟩
    let P' : Fin l → Finset (Fin m) :=
      Function.update (Function.update P t1 ((P t1).erase x)) t0 {x}
    have hP'_t0 : P' t0 = {x} := by simp [P']
    have hP'_t1 : P' t1 = (P t1).erase x := by simp [P', ht1_ne]
    have hP'_other : ∀ t : Fin l, t ≠ t0 → t ≠ t1 → P' t = P t := by
      intro t h0 h1
      simp [P', h0, h1]
    have hP'_t1_ne : P' t1 ≠ ∅ := by
      rw [hP'_t1]
      intro hemp
      have hc := Finset.card_erase_of_mem hx
      rw [hemp, Finset.card_empty] at hc
      omega
    have ht1_ne0 : P t1 ≠ ∅ :=
      Finset.Nonempty.ne_empty (Finset.card_pos.mp (by omega : 0 < (P t1).card))
    have hflt_eq :
        (Finset.univ : Finset (Fin l)).filter (fun t => P' t = ∅) =
        ((Finset.univ : Finset (Fin l)).filter (fun t => P t = ∅)).erase t0 := by
      ext t
      by_cases h0 : t = t0
      · subst h0
        simp [hP'_t0]
      · by_cases h1 : t = t1
        · subst h1
          simp [hP'_t1_ne, ht1_ne0, h0]
        · simp [hP'_other t h0 h1, h0]
    have he' : ((Finset.univ : Finset (Fin l)).filter (fun t => P' t = ∅)).card = e := by
      rw [hflt_eq, Finset.card_erase_of_mem ht0_mem, he]
      omega
    have ht1_mem_er : t1 ∈ (Finset.univ : Finset (Fin l)).erase t0 :=
      Finset.mem_erase.mpr ⟨ht1_ne, Finset.mem_univ t1⟩
    have hsum_card' : (∑ t : Fin l, (P' t).card) = m := by
      have heq_sum : (∑ t : Fin l, (P' t).card) = ∑ t : Fin l, (P t).card := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0),
            ← Finset.add_sum_erase _ _ ht1_mem_er]
        symm
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0),
            ← Finset.add_sum_erase _ _ ht1_mem_er]
        have hrest :
            ∑ t ∈ (Finset.univ.erase t0).erase t1, (P t).card =
            ∑ t ∈ (Finset.univ.erase t0).erase t1, (P' t).card := by
          apply Finset.sum_congr rfl
          intro t ht
          have hne1 : t ≠ t1 := Finset.ne_of_mem_erase ht
          have hne0 : t ≠ t0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)
          rw [hP'_other t hne0 hne1]
        rw [hrest, ht0, hP'_t0, hP'_t1, Finset.card_empty, Finset.card_singleton,
          Finset.card_erase_of_mem hx]
        omega
      exact heq_sum.trans hsum_card
    have hM_le : ∑ t : Fin l, M v c (P t) ≤ ∑ t : Fin l, M v c (P' t) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0),
          ← Finset.add_sum_erase _ _ ht1_mem_er]
      conv_rhs =>
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0),
            ← Finset.add_sum_erase _ _ ht1_mem_er]
      have hrest :
          ∑ t ∈ (Finset.univ.erase t0).erase t1, M v c (P t) =
          ∑ t ∈ (Finset.univ.erase t0).erase t1, M v c (P' t) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hne1 : t ≠ t1 := Finset.ne_of_mem_erase ht
        have hne0 : t ≠ t0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)
        rw [hP'_other t hne0 hne1]
      rw [hrest, ht0, M_empty, hP'_t0, hP'_t1]
      have hunion : ({x} : Finset (Fin m)) ∪ (P t1).erase x = P t1 := by
        rw [Finset.singleton_union, Finset.insert_erase hx]
      have hdisj : Disjoint ({x} : Finset (Fin m)) ((P t1).erase x) := by
        simp
      have htri : M v c (P t1) ≤ M v c {x} + M v c ((P t1).erase x) := by
        have h := M_union_le v c {x} ((P t1).erase x) hdisj
        rwa [hunion] at h
      linarith
    exact le_trans hM_le (ih P' he' hsum_card')

lemma exists_balanced_label (m l : ℕ) (hl : 0 < l) (hlm : l ≤ m) :
    let pairs := (m - l) / 2
    let a := pairs / l
    let b := pairs % l
    ∃ label : Fin m → Fin l,
      ∀ t : Fin l,
        (fiber label t).card =
          (if t.val = 0 then (m - l) % 2 else 0) +
          (if t.val < b then 2 * a + 3 else 2 * a + 1) := by
  intro pairs a b
  let rem := (m - l) % 2
  let sz : ℕ → ℕ := fun t => (if t = 0 then rem else 0) + (if t < b then 2 * a + 3 else 2 * a + 1)
  let cum : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, sz i
  have hcum0 : cum 0 = 0 := by simp [cum]
  have hcum_succ : ∀ n, cum (n + 1) = cum n + sz n := fun n => Finset.sum_range_succ sz n
  have hcum_mono : ∀ {n1 n2}, n1 ≤ n2 → cum n1 ≤ cum n2 := by
    intro n1 n2 hle
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hle)
  have hblt : b < l := Nat.mod_lt pairs hl
  have hcum_l : cum l = m := by
    unfold cum
    have hsplit :
        (∑ i ∈ Finset.range l, sz i) =
        (∑ i ∈ Finset.range l, if i = 0 then rem else 0) +
        (∑ i ∈ Finset.range l, ((2 * a + 1) + if i < b then 2 else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [sz]
      split_ifs <;> omega
    rw [hsplit]
    have h1 : (∑ i ∈ Finset.range l, if i = 0 then rem else 0) = rem := by
      have h0 : 0 ∈ Finset.range l := Finset.mem_range.mpr hl
      simp [h0]
    have h2 :
        (∑ i ∈ Finset.range l, ((2 * a + 1) + if i < b then 2 else 0)) =
        l * (2 * a + 1) + 2 * b := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      congr 1
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      have hflt : (Finset.range l).filter (fun i => i < b) = Finset.range b := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hflt, Finset.card_range]
      ring
    rw [h1, h2]
    have hdiv1 : 2 * pairs + rem = m - l := by
      simpa [pairs, rem] using Nat.div_add_mod (m - l) 2
    have hdiv2 : l * a + b = pairs := Nat.div_add_mod pairs l
    have hmul : l * (2 * a + 1) = 2 * (l * a) + l := by ring
    omega
  have hex_t : ∀ j : Fin m, ∃ t : ℕ, j.val < cum (t + 1) := by
    intro j
    refine ⟨l - 1, ?_⟩
    have hsub : l - 1 + 1 = l := by omega
    rw [hsub, hcum_l]
    exact j.isLt
  classical
  let label : Fin m → Fin l := fun j =>
    ⟨Nat.find (hex_t j), by
      have hle : Nat.find (hex_t j) ≤ l - 1 := by
        apply Nat.find_min'
        have hsub : l - 1 + 1 = l := by omega
        rw [hsub, hcum_l]
        exact j.isLt
      omega⟩
  have hlabel_iff : ∀ (j : Fin m) (t : Fin l),
      label j = t ↔ cum t.val ≤ j.val ∧ j.val < cum (t.val + 1) := by
    intro j t
    have hlt_find : j.val < cum ((label j).val + 1) := Nat.find_spec (hex_t j)
    have hle_find : cum (label j).val ≤ j.val := by
      cases hval : (label j).val with
      | zero =>
        rw [hcum0]
        omega
      | succ u =>
        have hmin : ¬ (j.val < cum (u + 1)) := by
          apply Nat.find_min (hex_t j)
          change u < (label j).val
          omega
        omega
    constructor
    · intro hEq
      subst hEq
      exact ⟨hle_find, hlt_find⟩
    · rintro ⟨hle, hlt⟩
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h2
      · have := hcum_mono (show (label j).val + 1 ≤ t.val by omega)
        omega
      · have := hcum_mono (show t.val + 1 ≤ (label j).val by omega)
        omega
  refine ⟨label, ?_⟩
  intro t
  have hbij : (fiber label t).card = (Finset.univ : Finset (Fin (sz t.val))).card := by
    apply Finset.card_bij (fun j hj =>
      ⟨j.val - cum t.val, by
        have hmem : label j = t := (Finset.mem_filter.mp hj).2
        have hbnd := (hlabel_iff j t).mp hmem
        rw [hcum_succ] at hbnd
        omega⟩)
    · intro j _
      exact Finset.mem_univ _
    · intro j1 hj1 j2 hj2 hEq
      have hb1 := (hlabel_iff j1 t).mp (Finset.mem_filter.mp hj1).2
      have hb2 := (hlabel_iff j2 t).mp (Finset.mem_filter.mp hj2).2
      have hv : j1.val - cum t.val = j2.val - cum t.val := congrArg Fin.val hEq
      exact Fin.ext (by omega)
    · intro i _
      have hlt_m : cum t.val + i.val < m := by
        have h1 : cum (t.val + 1) ≤ cum l := hcum_mono (by omega)
        rw [hcum_succ] at h1
        rw [hcum_l] at h1
        omega
      refine ⟨⟨cum t.val + i.val, hlt_m⟩, ?_, ?_⟩
      · rw [fiber, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hlabel_iff]
        rw [hcum_succ]
        have hi : i.val < sz t.val := i.isLt
        dsimp
        exact ⟨by omega, by omega⟩
      · apply Fin.ext
        dsimp
        omega
  rw [hbij, Finset.card_univ, Fintype.card_fin]

lemma card_filter_fin_lt (l b : ℕ) (hb : b ≤ l) :
    ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => t.val < b)).card = b := by
  have hbij :
      ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => t.val < b)).card =
      (Finset.univ : Finset (Fin b)).card := by
    apply Finset.card_bij (fun t ht => ⟨t.val, (Finset.mem_filter.mp ht).2⟩)
    · intro _ _
      exact Finset.mem_univ _
    · intro t1 _ t2 _ hEq
      have hv : t1.val = t2.val := congrArg (fun x : Fin b => x.val) hEq
      exact Fin.ext hv
    · intro i _
      refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
      · simp
      · rfl
  rw [hbij, Finset.card_univ, Fintype.card_fin]

lemma main_proof : ∀ (k m l : ℕ), 0 < l → l ≤ m →
    let F := ZMod 2
    let V := Fin k → F
    let pairs := (m-l)/2
    let a := pairs/l
    let b := pairs % l
    let mean := fun j : ℕ => ((2*j+1 : ℕ) : ℚ)*(Nat.choose (2*j) j : ℚ)/(4 : ℚ)^j
    ∀ v : Fin m ↪ V,
      (∀ S : Finset (Fin m), 0 < S.card → S.card % 2 = 0 →
        S.card ≤ 16*(a+1) → (∑ j ∈ S, v j) ≠ 0) →
      ∀ (r : V → Bool) (c : Fin m → Bool),
        let loss := fun (label : Fin m → Fin l) (out : V → Fin l → Bool) =>
          ((Finset.univ : Finset (V × Fin m)).filter (fun z =>
            out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
              (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card
        let price := ((2^k : ℕ) : ℚ)*((m : ℚ)-((l-b : ℕ) : ℚ)*mean a-(b : ℚ)*mean (a+1))
        (∀ label out, price ≤ 2*(loss label out : ℚ)) ∧
          (∃ label out, 2*(loss label out : ℚ) = price) := by
  intro k m l hl hlm F V pairs a b mean v hInd r c loss price
  constructor
  · intro label out
    have hloss := loss_ge_M v r c label out
    have hsum_card : (∑ t : Fin l, (fiber label t).card) = m := by
      have h1 := sum_over_fibers label (fun _ : Fin m => (1 : ℕ))
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
      exact h1.symm
    have hM := sum_M_le_bound hl hlm v c hInd
      (((Finset.univ : Finset (Fin l)).filter (fun t => fiber label t = ∅)).card)
      (fiber label) rfl hsum_card
    have h2k : (0 : ℚ) ≤ ((2 ^ k : ℕ) : ℚ) := by positivity
    have hstep :
        price ≤ ((2 ^ k : ℕ) : ℚ) * ((m : ℚ) - ∑ t : Fin l, M v c (fiber label t)) := by
      dsimp only [price]
      have hsub :
          (m : ℚ) - ((l - b : ℕ) : ℚ) * mean a - (b : ℚ) * mean (a + 1) ≤
          (m : ℚ) - ∑ t : Fin l, M v c (fiber label t) := by
        change (m : ℚ) - ((l - b : ℕ) : ℚ) * meanFn a - (b : ℚ) * meanFn (a + 1) ≤ _
        linarith
      exact mul_le_mul_of_nonneg_left hsub h2k
    exact le_trans hstep hloss
  · rcases exists_balanced_label m l hl hlm with ⟨labelStar, hsz⟩
    refine ⟨labelStar, optOut v r c labelStar, ?_⟩
    have hopt := loss_optOut_eq v r c labelStar
    have hblt : b < l := Nat.mod_lt pairs hl
    have hM_val : ∀ t : Fin l,
        M v c (fiber labelStar t) = if t.val < b then meanFn (a + 1) else meanFn a := by
      intro t
      have htcard : (fiber labelStar t).card =
          (if t.val = 0 then (m - l) % 2 else 0) +
          (if t.val < b then 2 * a + 3 else 2 * a + 1) := hsz t
      have hrem : (m - l) % 2 = 0 ∨ (m - l) % 2 = 1 := by omega
      have hle16 : (fiber labelStar t).card ≤ 16 * (a + 1) := by
        rw [htcard]
        split_ifs <;> omega
      rw [M_eq_R v c hInd (fiber labelStar t) hle16, htcard]
      by_cases htb : t.val < b
      · simp only [htb, ↓reduceIte]
        rcases hrem with hr0 | hr1
        · have heq : (if t.val = 0 then (m - l) % 2 else 0) + (2 * a + 3) = 2 * (a + 1) + 1 := by
            split_ifs <;> omega
          rw [heq]
          exact (R_closed_form (a + 1)).1
        · by_cases ht0 : t.val = 0
          · have heq : (if t.val = 0 then (m - l) % 2 else 0) + (2 * a + 3) = 2 * (a + 1) + 2 := by
              simp [ht0, hr1]; omega
            rw [heq]
            exact (R_closed_form (a + 1)).2
          · have heq : (if t.val = 0 then (m - l) % 2 else 0) + (2 * a + 3) = 2 * (a + 1) + 1 := by
              simp [ht0]; omega
            rw [heq]
            exact (R_closed_form (a + 1)).1
      · simp only [htb, ↓reduceIte]
        rcases hrem with hr0 | hr1
        · have heq : (if t.val = 0 then (m - l) % 2 else 0) + (2 * a + 1) = 2 * a + 1 := by
            split_ifs <;> omega
          rw [heq]
          exact (R_closed_form a).1
        · by_cases ht0 : t.val = 0
          · have heq : (if t.val = 0 then (m - l) % 2 else 0) + (2 * a + 1) = 2 * a + 2 := by
              simp [ht0, hr1]; omega
            rw [heq]
            exact (R_closed_form a).2
          · have heq : (if t.val = 0 then (m - l) % 2 else 0) + (2 * a + 1) = 2 * a + 1 := by
              simp [ht0]
            rw [heq]
            exact (R_closed_form a).1
    have hsum_M :
        ∑ t : Fin l, M v c (fiber labelStar t) =
        ((l - b : ℕ) : ℚ) * meanFn a + (b : ℚ) * meanFn (a + 1) := by
      simp_rw [hM_val]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have hc1 : ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => t.val < b)).card = b :=
        card_filter_fin_lt l b (le_of_lt hblt)
      have hc2 :
          ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => ¬ t.val < b)).card = l - b := by
        have hu :
            (Finset.univ : Finset (Fin l)).filter (fun t : Fin l => t.val < b) ∪
            (Finset.univ : Finset (Fin l)).filter (fun t : Fin l => ¬ t.val < b) = Finset.univ := by
          ext t
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact Classical.em (t.val < b)
        have hd : Disjoint
            ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => t.val < b))
            ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => ¬ t.val < b)) := by
          rw [Finset.disjoint_filter]
          intro t _ h1 h2
          exact h2 h1
        have htot :
            ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => t.val < b)).card +
            ((Finset.univ : Finset (Fin l)).filter (fun t : Fin l => ¬ t.val < b)).card = l := by
          rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ, Fintype.card_fin]
        omega
      rw [hc1, hc2]
      ring
    change 2 * (lossFn v r c labelStar (optOut v r c labelStar) : ℚ) = price
    rw [hopt, hsum_M]
    dsimp only [price, mean]
    change ((2 ^ k : ℕ) : ℚ) * ((m : ℚ) - (((l - b : ℕ) : ℚ) * meanFn a + (b : ℚ) * meanFn (a + 1))) =
      ((2 ^ k : ℕ) : ℚ) * ((m : ℚ) - ((l - b : ℕ) : ℚ) * meanFn a - (b : ℚ) * meanFn (a + 1))
    ring

end PEqualNP.Outside.L_meta_26026_aux

theorem PEqualNP.Outside.L_meta_26026 : (∀ (k m l : ℕ), 0 < l → l ≤ m →
  let F := ZMod 2
  let V := Fin k → F
  let pairs := (m-l)/2
  let a := pairs/l
  let b := pairs % l
  let mean := fun j : ℕ => ((2*j+1 : ℕ) : ℚ)*(Nat.choose (2*j) j : ℚ)/(4 : ℚ)^j
  ∀ v : Fin m ↪ V,
    (∀ S : Finset (Fin m), 0 < S.card → S.card % 2 = 0 →
      S.card ≤ 16*(a+1) → (∑ j ∈ S, v j) ≠ 0) →
    ∀ (r : V → Bool) (c : Fin m → Bool),
      let loss := fun (label : Fin m → Fin l) (out : V → Fin l → Bool) =>
        ((Finset.univ : Finset (V × Fin m)).filter (fun z =>
          out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
            (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card
      let price := ((2^k : ℕ) : ℚ)*((m : ℚ)-((l-b : ℕ) : ℚ)*mean a-(b : ℚ)*mean (a+1))
      (∀ label out, price ≤ 2*(loss label out : ℚ)) ∧
        (∃ label out, 2*(loss label out : ℚ) = price)) := by
  exact PEqualNP.Outside.L_meta_26026_aux.main_proof
