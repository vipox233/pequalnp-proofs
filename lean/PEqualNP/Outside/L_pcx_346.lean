import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_346

open scoped BigOperators
open Finset

def bitsEquiv (n : ℕ) : (Bool × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) where
  toFun z := Fin.cases z.1 z.2
  invFun x := (x 0,fun i => x i.succ)
  left_inv := by intro z; rfl
  right_inv := by
    intro x
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma bool_sum (f : Bool → ℝ) : (∑ b, f b) = f false+f true := by
  rw [show (Finset.univ : Finset Bool)={false,true} by decide]
  simp

lemma sum_bits (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ x, f x) = (∑ x : Fin n → Bool, f (Fin.cases false x)) +
      ∑ x : Fin n → Bool, f (Fin.cases true x) := by
  rw [← (bitsEquiv n).sum_comp f, Fintype.sum_prod_type, bool_sum]
  rfl

lemma bits_ones (n : ℕ) : (∑ _x : Fin n → Bool, (1 : ℝ)) = (2 : ℝ)^n := by
  simp [Fintype.card_fun]

noncomputable def avg {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ := (∑ x, f x)/(2 : ℝ)^n

def bitLip {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∀ (x y : Fin n → Bool) (i : Fin n),
    (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ 2

lemma avg_split {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    avg f = (avg (fun x => f (Fin.cases false x))+
      avg (fun x => f (Fin.cases true x)))/2 := by
  unfold avg
  rw [sum_bits, pow_succ]
  ring

lemma lip_slice {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) (hf : bitLip f) (b : Bool) :
    bitLip (fun x => f (Fin.cases b x)) := by
  intro x y i hxy
  apply hf _ _ i.succ
  intro j
  refine Fin.cases ?_ (fun a => ?_) j
  · intro _; rfl
  · intro hj
    exact hxy a (by intro h; subst a; exact hj rfl)

lemma slice_diff {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) (hf : bitLip f)
    (x : Fin n → Bool) : |f (Fin.cases false x)-f (Fin.cases true x)| ≤ 2 := by
  apply hf _ _ 0
  intro j
  refine Fin.cases ?_ (fun _ _ => rfl) j
  intro hj
  exact False.elim (hj rfl)

lemma avg_slice_diff {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) (hf : bitLip f) :
    |avg (fun x => f (Fin.cases false x))-avg (fun x => f (Fin.cases true x))| ≤ 2 := by
  have hlo : ∀ x, f (Fin.cases false x) ≤ f (Fin.cases true x)+2 := by
    intro x; have := (abs_le.mp (slice_diff f hf x)).2; linarith
  have hhi : ∀ x, f (Fin.cases true x) ≤ f (Fin.cases false x)+2 := by
    intro x; have := (abs_le.mp (slice_diff f hf x)).1; linarith
  have hs0 := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n → Bool))) => hlo x)
  have hs1 := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n → Bool))) => hhi x)
  have hc : (∑ _x : Fin n → Bool, (2 : ℝ)) = 2*(2 : ℝ)^n := by
    simp [Fintype.card_fun,mul_comm]
  simp only [Finset.sum_add_distrib, hc] at hs0 hs1
  have hp : 0 < (2 : ℝ)^n := by positivity
  rw [abs_le]
  unfold avg
  rw [← sub_div]
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

lemma central_shift {n : ℕ} (f : (Fin n → Bool) → ℝ) (t a : ℝ) :
    (∑ x, Real.exp (t*(f x-a))) =
      Real.exp (t*(avg f-a)) * ∑ x, Real.exp (t*(f x-avg f)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Real.exp_add]
  congr 1
  ring

lemma finite_mgf (n : ℕ) (f : (Fin n → Bool) → ℝ) (hf : bitLip f) (t : ℝ) :
    (∑ x, Real.exp (t*(f x-avg f))) ≤
      (2 : ℝ)^n * Real.exp ((n : ℝ)*t^2/2) := by
  induction n with
  | zero =>
    have he : ∀ x : Fin 0 → Bool, x = fun i => Fin.elim0 i := by
      intro x; funext i; exact Fin.elim0 i
    simp [avg, he]
  | succ n ih =>
    let f0 := fun x : Fin n → Bool => f (Fin.cases false x)
    let f1 := fun x : Fin n → Bool => f (Fin.cases true x)
    let d := (avg f0-avg f1)/2
    have hm : avg f = (avg f0+avg f1)/2 := avg_split f
    have h0 := ih f0 (lip_slice f hf false)
    have h1 := ih f1 (lip_slice f hf true)
    have hd : d^2 ≤ 1 := by
      have h := abs_le.mp (avg_slice_diff f hf)
      dsimp [d,f0,f1]
      nlinarith [sq_nonneg (avg f0-avg f1-2),sq_nonneg (avg f0-avg f1+2)]
    have hcosh : Real.exp (t*d)+Real.exp (-(t*d)) ≤ 2*Real.exp (t^2/2) := by
      have h := Real.cosh_le_exp_half_sq (t*d)
      have hs : (t*d)^2/2 ≤ t^2/2 := by
        have := mul_le_mul_of_nonneg_left hd (sq_nonneg t)
        nlinarith
      have he := Real.exp_le_exp.mpr hs
      rw [Real.cosh_eq] at h
      linarith
    rw [sum_bits, central_shift f0, central_shift f1]
    have he0 : avg f0-avg f=d := by dsimp [d]; rw [hm]; ring
    have he1 : avg f1-avg f= -d := by dsimp [d]; rw [hm]; ring
    rw [he0,he1]
    calc
      _ ≤ Real.exp (t*d)*((2 : ℝ)^n*Real.exp ((n : ℝ)*t^2/2))+
          Real.exp (t*(-d))*((2 : ℝ)^n*Real.exp ((n : ℝ)*t^2/2)) :=
        (add_le_add (mul_le_mul_of_nonneg_left h0 (le_of_lt (Real.exp_pos _)))
          (mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))))
      _ = (Real.exp (t*d)+Real.exp (-(t*d))) *
          ((2 : ℝ)^n*Real.exp ((n : ℝ)*t^2/2)) := by rw [mul_neg]; ring
      _ ≤ (2*Real.exp (t^2/2))*((2 : ℝ)^n*Real.exp ((n : ℝ)*t^2/2)) :=
        mul_le_mul_of_nonneg_right hcosh (by positivity)
      _ = (2 : ℝ)^(n+1)*Real.exp (((n+1 : ℕ) : ℝ)*t^2/2) := by
        rw [pow_succ (2 : ℝ) n]
        push_cast
        rw [show ((n : ℝ)+1)*t^2/2 = t^2/2+(n : ℝ)*t^2/2 by ring,Real.exp_add]
        ring


lemma finite_upper_tail (n : ℕ) (f : (Fin n → Bool) → ℝ) (hf : bitLip f)
    (t u : ℝ) (ht : 0<t) :
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => u ≤ f x-avg f)).card : ℝ) ≤
      (2 : ℝ)^n * Real.exp ((n : ℝ)*t^2/2-t*u) := by
  classical
  let B := (Finset.univ : Finset (Fin n → Bool)).filter (fun x => u ≤ f x-avg f)
  rw [Real.exp_sub, ← mul_div_assoc]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  calc
    (B.card : ℝ)*Real.exp (t*u) = ∑ _x ∈ B, Real.exp (t*u) := by simp
    _ ≤ ∑ x ∈ B, Real.exp (t*(f x-avg f)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 ht.le
    _ ≤ ∑ x, Real.exp (t*(f x-avg f)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => (Real.exp_pos _).le)
    _ ≤ _ := finite_mgf n f hf t

lemma two_pow_le_exp (q : ℕ) : (2 : ℝ)^q ≤ Real.exp (q : ℝ) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, Nat.cast_succ, Real.exp_add]
    have h : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact mul_le_mul ih h (by norm_num) (Real.exp_pos _).le

lemma scaled_upper_tail (n : ℕ) (f : (Fin n → Bool) → ℝ) (hf : bitLip f) :
    2^(n/65536) *
      ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => (n : ℝ)/64 ≤ f x-avg f)).card ≤ 2^n := by
  have h := finite_upper_tail n f hf (1/128) ((n : ℝ)/64) (by norm_num)
  have he : (n : ℝ)*(1/128)^2/2-(1/128)*((n : ℝ)/64) =
      -(3*(n : ℝ)/32768) := by ring
  rw [he] at h
  have hq : ((n/65536 : ℕ) : ℝ) ≤ 3*(n : ℝ)/32768 := by
    have hn : (((n/65536 : ℕ) : ℝ)*65536) ≤ (n : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self n 65536
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hp : (2 : ℝ)^(n/65536) ≤ Real.exp (3*(n : ℝ)/32768) :=
    (two_pow_le_exp _).trans (Real.exp_le_exp.mpr hq)
  have hr : (2 : ℝ)^(n/65536) *
      (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => (n : ℝ)/64 ≤ f x-avg f)).card : ℝ) ≤ (2 : ℝ)^n := by
    calc
      _ ≤ (2 : ℝ)^(n/65536)*((2 : ℝ)^n*Real.exp (-(3*(n : ℝ)/32768))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ Real.exp (3*(n : ℝ)/32768)*((2 : ℝ)^n*Real.exp (-(3*(n : ℝ)/32768))) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (2 : ℝ)^n := by
        calc
          _ = (2 : ℝ)^n*(Real.exp (3*(n : ℝ)/32768)*Real.exp (-(3*(n : ℝ)/32768))) := by ring
          _ = _ := by rw [← Real.exp_add]; simp
  exact_mod_cast hr

lemma avg_neg {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    avg (fun x => -f x) = -avg f := by
  simp only [avg, Finset.sum_neg_distrib]
  ring

lemma lip_neg {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : bitLip f) :
    bitLip (fun x => -f x) := by
  intro x y i hi
  simpa only [neg_sub_neg, abs_sub_comm] using hf x y i hi

lemma scaled_abs_tail (n : ℕ) (f : (Fin n → Bool) → ℝ) (hf : bitLip f) :
    2^(n/65536) *
      ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => (n : ℝ)/64 ≤ |f x-avg f|)).card ≤ 2*2^n := by
  classical
  let A := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun x => (n : ℝ)/64 ≤ |f x-avg f|)
  let B := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun x => (n : ℝ)/64 ≤ f x-avg f)
  let C := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun x => (n : ℝ)/64 ≤ -f x-avg (fun x => -f x))
  have hab : A ⊆ B ∪ C := by
    intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    by_cases h : 0 ≤ f x-avg f
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [abs_of_nonneg h] using hh⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [avg_neg]
      rw [abs_of_neg (lt_of_not_ge h)] at hh
      linarith
  have hc : A.card ≤ B.card+C.card :=
    (Finset.card_le_card hab).trans (Finset.card_union_le _ _)
  have hb : 2^(n/65536)*B.card ≤ 2^n := scaled_upper_tail n f hf
  have hd : 2^(n/65536)*C.card ≤ 2^n := scaled_upper_tail n (fun x => -f x) (lip_neg f hf)
  have hm := Nat.mul_le_mul_left (2^(n/65536)) hc
  rw [Nat.mul_add] at hm
  change 2^(n/65536)*A.card ≤ 2*2^n
  omega

lemma card_difference {α : Type} [DecidableEq α] (A B S : Finset α)
    (h : ∀ i, i ∉ S → (i ∈ A ↔ i ∈ B)) :
    |(A.card : ℝ)-(B.card : ℝ)| ≤ S.card := by
  have hab : A ⊆ B ∪ S := by
    intro i hi
    by_cases hs : i∈S
    · exact Finset.mem_union_right _ hs
    · exact Finset.mem_union_left _ ((h i hs).mp hi)
  have hba : B ⊆ A ∪ S := by
    intro i hi
    by_cases hs : i∈S
    · exact Finset.mem_union_right _ hs
    · exact Finset.mem_union_left _ ((h i hs).mpr hi)
  have hu : A.card ≤ B.card+S.card :=
    (Finset.card_le_card hab).trans (Finset.card_union_le _ _)
  have hv : B.card ≤ A.card+S.card :=
    (Finset.card_le_card hba).trans (Finset.card_union_le _ _)
  have hur : (A.card : ℝ) ≤ (B.card : ℝ)+(S.card : ℝ) := by exact_mod_cast hu
  have hvr : (B.card : ℝ) ≤ (A.card : ℝ)+(S.card : ℝ) := by exact_mod_cast hv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def mismatch {n : ℕ} (π : Equiv.Perm (Fin n)) (mask z : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => z i ≠ xor (z (π i)) (mask i))).card

lemma mismatch_lip {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) :
    bitLip (fun z => (mismatch π mask z : ℝ)) := by
  classical
  intro x y i hxy
  let S : Finset (Fin n) := {i,π.symm i}
  have hs : S.card ≤ 2 := by
    have := Finset.card_insert_le i {π.symm i}
    simpa [S] using this
  have hd := card_difference
    (Finset.univ.filter (fun j => x j ≠ xor (x (π j)) (mask j)))
    (Finset.univ.filter (fun j => y j ≠ xor (y (π j)) (mask j))) S (by
      intro j hj
      have hji : j≠i := by intro h; subst j; exact hj (by simp [S])
      have hp : π j≠i := by
        intro h
        have : j=π.symm i := by simpa using congrArg π.symm h
        subst j
        exact hj (by simp [S])
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hxy j hji,hxy (π j) hp])
  change |(mismatch π mask x : ℝ)-(mismatch π mask y : ℝ)| ≤ 2
  exact hd.trans (by exact_mod_cast hs)


def toggle {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun z := fun j => if j=i then !(z j) else z j
  invFun z := fun j => if j=i then !(z j) else z j
  left_inv := by intro z; funext j; by_cases h : j=i <;> simp [h]
  right_inv := by intro z; funext j; by_cases h : j=i <;> simp [h]

noncomputable def term {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool)
    (i : Fin n) (z : Fin n → Bool) : ℝ :=
  if z i ≠ xor (z (π i)) (mask i) then 1 else 0

lemma term_bounds {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) (i : Fin n) :
    ∀ z, 0 ≤ term π mask i z ∧ term π mask i z ≤ 1 := by
  intro z
  unfold term
  split <;> norm_num

lemma avg_bounds {n : ℕ} (f : (Fin n → Bool) → ℝ) (h : ∀ z, 0≤f z ∧ f z≤1) :
    0 ≤ avg f ∧ avg f ≤ 1 := by
  have hp : 0 < (2 : ℝ)^n := by positivity
  have h0 : 0 ≤ ∑ z, f z := Finset.sum_nonneg (fun z _ => (h z).1)
  have h1 : (∑ z, f z) ≤ (2 : ℝ)^n :=
    (Finset.sum_le_sum (fun z _ => (h z).2)).trans_eq (bits_ones n)
  unfold avg
  exact ⟨div_nonneg h0 hp.le, (div_le_iff₀ hp).mpr (by simpa using h1)⟩

lemma term_pair {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) (i : Fin n)
    (hi : π i ≠ i) (z : Fin n → Bool) :
    term π mask i z + term π mask i (toggle i z) = 1 := by
  cases hz : z i <;> cases hp : z (π i) <;> cases hm : mask i <;>
    simp [term,toggle,hi,hz,hp,hm]

lemma avg_term {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) (i : Fin n)
    (hi : π i ≠ i) : avg (term π mask i) = 1/2 := by
  have he : (∑ z, term π mask i (toggle i z)) = ∑ z, term π mask i z :=
    (toggle i).sum_comp _
  have hs : 2*(∑ z, term π mask i z) = (2 : ℝ)^n := by
    calc
      _ = (∑ z, term π mask i z)+(∑ z, term π mask i (toggle i z)) := by rw [he]; ring
      _ = ∑ z, (term π mask i z+term π mask i (toggle i z)) := by rw [Finset.sum_add_distrib]
      _ = ∑ _z : Fin n → Bool, (1 : ℝ) :=
        Finset.sum_congr rfl (fun z _ => term_pair π mask i hi z)
      _ = _ := bits_ones n
  unfold avg
  apply (div_eq_iff (show (2 : ℝ)^n≠0 by positivity)).mpr
  linarith

lemma avg_mismatch {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) :
    avg (fun z => (mismatch π mask z : ℝ)) = ∑ i, avg (term π mask i) := by
  unfold avg mismatch term
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm, Finset.sum_div]

lemma mismatch_mean {n : ℕ} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool)
    (hfix : 128*(Finset.univ.filter (fun i => π i=i)).card ≤ n) :
    |avg (fun z => (mismatch π mask z : ℝ))-(n : ℝ)/2| ≤ (n : ℝ)/256 := by
  classical
  let S := Finset.univ.filter (fun i => π i=i)
  have hS : (S.card : ℝ) = ∑ i : Fin n, if π i=i then (1 : ℝ) else 0 := by
    exact_mod_cast (Finset.card_filter (fun i : Fin n => π i=i) Finset.univ)
  have hu : ∀ i : Fin n, avg (term π mask i) ≤ 1/2+(if π i=i then 1 else 0)/2 := by
    intro i
    by_cases hi : π i=i
    · have h := (avg_bounds (term π mask i) (term_bounds π mask i)).2
      norm_num [hi]
      exact h
    · rw [avg_term π mask i hi]
      simp [hi]
  have hl : ∀ i : Fin n, 1/2-(if π i=i then 1 else 0)/2 ≤ avg (term π mask i) := by
    intro i
    by_cases hi : π i=i
    · have h := (avg_bounds (term π mask i) (term_bounds π mask i)).1
      norm_num [hi]
      exact h
    · rw [avg_term π mask i hi]
      simp [hi]
  have hsu := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => hu i)
  have hsl := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => hl i)
  have heU : (∑ i : Fin n, (1/2+(if π i=i then (1 : ℝ) else 0)/2)) =
      (n : ℝ)/2+(S.card : ℝ)/2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← hS]
    simp
  have heL : (∑ i : Fin n, (1/2-(if π i=i then (1 : ℝ) else 0)/2)) =
      (n : ℝ)/2-(S.card : ℝ)/2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← hS]
    simp
  rw [heU] at hsu
  rw [heL] at hsl
  have hn : (128 : ℝ)*(S.card : ℝ) ≤ n := by exact_mod_cast hfix
  rw [avg_mismatch, abs_le]
  constructor <;> nlinarith

abbrev comfortable {n : ℕ} (π : Equiv.Perm (Fin n)) (mask z : Fin n → Bool) : Prop :=
  15*n+32 ≤ 32*mismatch π mask z ∧ 32*mismatch π mask z+32 ≤ 17*n

lemma mismatch_exceptional {n : ℕ} (hn : 128≤n) (π : Equiv.Perm (Fin n))
    (mask : Fin n → Bool)
    (hfix : 128*(Finset.univ.filter (fun i => π i=i)).card ≤ n) :
    2^(n/65536) *
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun z => ¬comfortable π mask z)).card ≤
      2*2^n := by
  classical
  let f := fun z => (mismatch π mask z : ℝ)
  have hs : (Finset.univ.filter (fun z => ¬comfortable π mask z)) ⊆
      (Finset.univ.filter (fun z => (n : ℝ)/64 ≤ |f z-avg f|)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hb
    have hh : |f z-avg f| < (n : ℝ)/64 := lt_of_not_ge hb
    have hm := abs_le.mp (mismatch_mean π mask hfix)
    have hd := abs_lt.mp hh
    have hn' : (128 : ℝ) ≤ n := by exact_mod_cast hn
    have hLo : (15 : ℝ)*n+32 ≤ 32*(mismatch π mask z : ℝ) := by
      dsimp [f] at hd
      nlinarith
    have hHi : (32 : ℝ)*(mismatch π mask z : ℝ)+32 ≤ 17*n := by
      dsimp [f] at hd
      nlinarith
    have hg : comfortable π mask z := ⟨by exact_mod_cast hLo,by exact_mod_cast hHi⟩
    exact (Finset.mem_filter.mp hz).2 hg
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hs)).trans
    (scaled_abs_tail n f (mismatch_lip π mask))


abbrev Raw (n : ℕ) := Bool × Fin n
abbrev Clause (n : ℕ) := PEqualNP.ProofComplexity.Clause (Raw n)

lemma avoid_not (a b : Bool) : (a ≠ !b) ↔ a=b := by
  cases a <;> cases b <;> decide

lemma bool_ne_not (a : Bool) : a ≠ !a := by cases a <;> decide

lemma xor_solve (a c b : Bool) : xor a c=b ↔ c=xor a b := by
  cases a <;> cases c <;> cases b <;> decide

def colorSet {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) (b : Bool) :
    Finset (Fin n) := Finset.univ.filter (fun i => xor (x (false,i)) (x (true,M i))=b)

lemma colorSet_true {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) :
    colorSet M x true = Finset.univ.filter (fun i => x (false,i) ≠ x (true,M i)) := by
  ext i
  cases h0 : x (false,i) <;> cases h1 : x (true,M i) <;> simp [colorSet,h0,h1]

lemma colorSet_false {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) :
    colorSet M x false = (colorSet M x true)ᶜ := by
  ext i
  cases h0 : x (false,i) <;> cases h1 : x (true,M i) <;> simp [colorSet,h0,h1]

lemma colorSet_false_card {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) :
    (colorSet M x false).card = n-(colorSet M x true).card := by
  rw [colorSet_false,Finset.card_compl]
  simp

lemma band_arith (n d : ℕ) (hd : d≤n) :
    16*Nat.dist (2*d) n ≤ n ↔ d ≤ 17*n/32 ∧ n-d ≤ 17*n/32 := by
  by_cases h : 2*d≤n
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

abbrev band {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) : Prop :=
  16*Nat.dist (2*(colorSet M x true).card) n ≤ n

lemma band_iff_colors {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) :
    band M x ↔ (colorSet M x true).card ≤ 17*n/32 ∧
      (colorSet M x false).card ≤ 17*n/32 := by
  have hd : (colorSet M x true).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  simpa only [colorSet_false_card] using band_arith n (colorSet M x true).card hd

def badClause {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a : Fin n → Bool) : Clause n :=
  T.image (fun i => ((false,i),!(a i))) ∪
    T.image (fun i => ((true,M i),!(xor (a i) b)))

lemma badClause_card {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a : Fin n → Bool) : (badClause M b T a).card = 2*T.card := by
  have hL : Function.Injective (fun i : Fin n => (((false,i),!(a i)) : Raw n × Bool)) := by
    intro i j h
    exact congrArg (fun l : Raw n × Bool => l.1.2) h
  have hR : Function.Injective (fun i : Fin n => (((true,M i),!(xor (a i) b)) : Raw n × Bool)) := by
    intro i j h
    exact M.injective (congrArg (fun l : Raw n × Bool => l.1.2) h)
  have hd : Disjoint (T.image (fun i => ((false,i),!(a i))))
      (T.image (fun i => ((true,M i),!(xor (a i) b)))) := by
    apply Finset.disjoint_left.mpr
    intro l hl hr
    obtain ⟨i,hi,hil⟩ := Finset.mem_image.mp hl
    obtain ⟨j,hj,hjl⟩ := Finset.mem_image.mp hr
    have he := congrArg (fun l : Raw n × Bool => l.1.1) (hil.trans hjl.symm)
    cases he
  rw [badClause,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hL,Finset.card_image_of_injective _ hR]
  omega

lemma badClause_false {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a : Fin n → Bool) (x : Raw n → Bool) :
    ¬PEqualNP.ProofComplexity.ClauseSat x (badClause M b T a) ↔
      ∀ i ∈ T, x (false,i)=a i ∧ x (true,M i)=xor (a i) b := by
  classical
  constructor
  · intro h i hi
    constructor
    · apply (avoid_not _ _).mp
      intro he
      apply h
      exact ⟨((false,i),!(a i)),
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩),he⟩
    · apply (avoid_not _ _).mp
      intro he
      apply h
      exact ⟨((true,M i),!(xor (a i) b)),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩),he⟩
  · intro h ⟨l,hl,hval⟩
    rcases Finset.mem_union.mp hl with hl | hr
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
      exact bool_ne_not _ ((h i hi).1.symm.trans hval)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
      exact bool_ne_not _ ((h i hi).2.symm.trans hval)

lemma badClause_forces {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a : Fin n → Bool) (x : Raw n → Bool)
    (h : ¬PEqualNP.ProofComplexity.ClauseSat x (badClause M b T a)) :
    T ⊆ colorSet M x b := by
  intro i hi
  have hx := (badClause_false M b T a x).mp h i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (xor_solve _ _ _).mpr ?_⟩
  rw [hx.1,hx.2]

lemma badClause_valid {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a : Fin n → Bool) (hT : T.card=17*n/32+1) (x : Raw n → Bool) (hx : band M x) :
    PEqualNP.ProofComplexity.ClauseSat x (badClause M b T a) := by
  classical
  by_contra h
  have hcard := Finset.card_le_card (badClause_forces M b T a x h)
  have hb : (colorSet M x b).card ≤ 17*n/32 := by
    cases b
    · exact (band_iff_colors M x).mp hx |>.2
    · exact (band_iff_colors M x).mp hx |>.1
  omega

lemma badClause_ext {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a a' : Fin n → Bool) (h : ∀ i∈T, a i=a' i) :
    badClause M b T a=badClause M b T a' := by
  unfold badClause
  congr 1 <;> apply Finset.image_congr <;> intro i hi <;> simp [h i hi]

def extend {n : ℕ} (T : Finset (Fin n)) (a : ↥T → Bool) (i : Fin n) : Bool :=
  if hi : i∈T then a ⟨i,hi⟩ else false

def clausesFor {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n)) :
    Finset (Clause n) :=
  Finset.univ.image (fun a : ↥T → Bool => badClause M b T (extend T a))

lemma clausesFor_card {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n)) :
    (clausesFor M b T).card ≤ 2^T.card := by
  calc
    _ ≤ (Finset.univ : Finset (↥T → Bool)).card := Finset.card_image_le
    _ = _ := by simp [Fintype.card_fun]

lemma badClause_mem {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (a : Fin n → Bool) : badClause M b T a ∈ clausesFor M b T := by
  apply Finset.mem_image.mpr
  refine ⟨fun i : ↥T => a i.val,Finset.mem_univ _,?_⟩
  apply badClause_ext
  intro i hi
  simp [extend,hi]


def family {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (t : ℕ) : Finset (Clause n) :=
  Finset.univ.biUnion (fun j : Fin r =>
    (Finset.univ : Finset Bool).biUnion (fun b =>
      ((Finset.univ : Finset (Fin n)).powersetCard t).biUnion (clausesFor (M j) b)))

lemma family_mem {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (t : ℕ) (c : Clause n) :
    c∈family M t ↔ ∃ (j : Fin r) (b : Bool) (T : Finset (Fin n)),
      T∈(Finset.univ : Finset (Fin n)).powersetCard t ∧
      ∃ a : ↥T → Bool, badClause (M j) b T (extend T a)=c := by
  simp only [family,Finset.mem_biUnion,Finset.mem_univ,true_and,
    clausesFor,Finset.mem_image]

lemma family_card {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (t : ℕ) :
    (family M t).card ≤ 2*r*Nat.choose n t*2^t := by
  have hT : ∀ (j : Fin r) (b : Bool),
      (((Finset.univ : Finset (Fin n)).powersetCard t).biUnion (clausesFor (M j) b)).card ≤
        Nat.choose n t*2^t := by
    intro j b
    calc
      _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
          (clausesFor (M j) b T).card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ (Finset.univ : Finset (Fin n)).powersetCard t, 2^t := by
        apply Finset.sum_le_sum
        intro T hT
        have hc : T.card=t := (Finset.mem_powersetCard.mp hT).2
        simpa only [hc] using clausesFor_card (M j) b T
      _ = _ := by simp
  have hb : ∀ j : Fin r,
      ((Finset.univ : Finset Bool).biUnion (fun b =>
        ((Finset.univ : Finset (Fin n)).powersetCard t).biUnion (clausesFor (M j) b))).card ≤
        2*(Nat.choose n t*2^t) := by
    intro j
    calc
      _ ≤ ∑ b : Bool,
          (((Finset.univ : Finset (Fin n)).powersetCard t).biUnion (clausesFor (M j) b)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _b : Bool, Nat.choose n t*2^t :=
        Finset.sum_le_sum (fun b _ => hT j b)
      _ = _ := by simp
  calc
    (family M t).card ≤ ∑ j : Fin r,
        ((Finset.univ : Finset Bool).biUnion (fun b =>
          ((Finset.univ : Finset (Fin n)).powersetCard t).biUnion (clausesFor (M j) b))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin r, 2*(Nat.choose n t*2^t) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [mul_assoc,mul_comm,mul_left_comm]

lemma canonical_cnf (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) :
    ∃ F : Finset (Clause n),
      (∀ x : Raw n → Bool, (∀ j, band (M j) x) ↔
        ∀ c∈F, PEqualNP.ProofComplexity.ClauseSat x c) ∧
      F.card ≤ 2*r*Nat.choose n (17*n/32+1)*2^(17*n/32+1) ∧
      ∀ c∈F, c.card=2*(17*n/32+1) := by
  classical
  let t := 17*n/32+1
  refine ⟨family M t,?_,family_card M t,?_⟩
  · intro x
    constructor
    · intro hx c hc
      obtain ⟨j,b,T,hT,a,rfl⟩ := (family_mem M t c).mp hc
      apply badClause_valid (M j) b T (extend T a) _ x (hx j)
      exact (Finset.mem_powersetCard.mp hT).2
    · intro hx j
      by_contra hn
      have hb : ∃ b : Bool, t ≤ (colorSet (M j) x b).card := by
        have he := band_iff_colors (M j) x
        by_cases ht : (colorSet (M j) x true).card ≤ 17*n/32
        · refine ⟨false,?_⟩
          have hh : ¬(colorSet (M j) x false).card ≤ 17*n/32 := by
            intro h; exact hn (he.mpr ⟨ht,h⟩)
          dsimp [t]
          omega
        · refine ⟨true,?_⟩
          dsimp [t]
          omega
      obtain ⟨b,hb⟩ := hb
      obtain ⟨T,hsub,hcard⟩ := Finset.exists_subset_card_eq hb
      have hT : T∈(Finset.univ : Finset (Fin n)).powersetCard t := by
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩
      let a : Fin n → Bool := fun i => x (false,i)
      have hc : badClause (M j) b T a ∈ family M t := by
        apply Finset.mem_biUnion.mpr
        refine ⟨j,Finset.mem_univ _,?_⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨b,Finset.mem_univ _,?_⟩
        exact Finset.mem_biUnion.mpr ⟨T,hT,badClause_mem (M j) b T a⟩
      have hfalse : ¬PEqualNP.ProofComplexity.ClauseSat x (badClause (M j) b T a) := by
        apply (badClause_false (M j) b T a x).mpr
        intro i hi
        refine ⟨rfl,?_⟩
        have he := (Finset.mem_filter.mp (hsub hi)).2
        exact (xor_solve _ _ _).mp he
      exact hfalse (hx _ hc)
  · intro c hc
    obtain ⟨j,b,T,hT,a,rfl⟩ := (family_mem M t c).mp hc
    rw [badClause_card,(Finset.mem_powersetCard.mp hT).2]


abbrev Choices (n t : ℕ) := {T : Finset (Fin n) // T∈(Finset.univ : Finset (Fin n)).powersetCard t}
abbrev Sample (n r t : ℕ) := Fin r × Bool × Choices n t × (Fin n → Bool)

def boundary {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (z : Fin n → Bool) (v : Raw n) : Bool :=
  if v.1 then xor (z (M.symm v.2)) (if M.symm v.2∈T then b else !b) else z v.2

def word {n r t : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (s : Sample n r t) : Raw n → Bool :=
  boundary (M s.1) s.2.1 s.2.2.1.val s.2.2.2

lemma boundary_color {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool) (T : Finset (Fin n))
    (z : Fin n → Bool) : colorSet M (boundary M b T z) b=T := by
  ext i
  by_cases hi : i∈T <;> cases b <;> cases hz : z i <;>
    simp [colorSet,boundary,hi,hz]

lemma boundary_mismatch {n : ℕ} (A B : Equiv.Perm (Fin n)) (b : Bool)
    (T : Finset (Fin n)) (z : Fin n → Bool) :
    (colorSet B (boundary A b T z) true).card =
      mismatch (B.trans A.symm) (fun i => if A.symm (B i)∈T then b else !b) z := by
  rw [colorSet_true]
  rfl

lemma transferred_fixed {n : ℕ} (A B : Equiv.Perm (Fin n)) :
    Finset.univ.filter (fun i => (B.trans A.symm) i=i) =
      Finset.univ.filter (fun i => B i=A i) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change (A.symm (B i)=i ↔ B i=A i)
  constructor
  · intro h; simpa using congrArg A h
  · intro h; rw [h]; simp

abbrev safe {n r t : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (s : Sample n r t) : Prop :=
  ∀ l : Fin r, l≠s.1 →
    15*n+32 ≤ 32*(colorSet (M l) (word M s) true).card ∧
      32*(colorSet (M l) (word M s) true).card+32 ≤ 17*n

lemma exceptional_z {n r t : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (hM : ∀ j l : Fin r, j≠l → 128*(Finset.univ.filter (fun i => M j i=M l i)).card ≤ n)
    (j : Fin r) (b : Bool) (T : Choices n t) :
    2^(n/65536) *
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun z => ¬safe M (j,b,T,z))).card ≤
      2*r*2^n := by
  classical
  let J := (Finset.univ : Finset (Fin r)).erase j
  let B := fun l : Fin r => (Finset.univ : Finset (Fin n → Bool)).filter (fun z =>
    ¬comfortable ((M l).trans (M j).symm)
      (fun i => if (M j).symm (M l i)∈T.val then b else !b) z)
  have hsub : (Finset.univ.filter (fun z => ¬safe M (j,b,T,z))) ⊆ J.biUnion B := by
    intro z hz
    have hh : ¬∀ l : Fin r, l≠j → comfortable ((M l).trans (M j).symm)
        (fun i => if (M j).symm (M l i)∈T.val then b else !b) z := by
      simpa only [safe,word,boundary_mismatch] using (Finset.mem_filter.mp hz).2
    push Not at hh
    obtain ⟨l,hl,hbad⟩ := hh
    apply Finset.mem_biUnion.mpr
    refine ⟨l,Finset.mem_erase.mpr ⟨hl,Finset.mem_univ _⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩
  have hbound : ∀ l∈J, 2^(n/65536)*(B l).card ≤ 2*2^n := by
    intro l hl
    have hlj : l≠j := (Finset.mem_erase.mp hl).1
    apply mismatch_exceptional hn
    simpa only [transferred_fixed] using hM l j hlj
  have hJ : J.card≤r := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  calc
    _ ≤ 2^(n/65536)*(J.biUnion B).card := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
    _ ≤ 2^(n/65536)*(∑ l∈J, (B l).card) := Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ l∈J, 2^(n/65536)*(B l).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _l∈J, 2*2^n := Finset.sum_le_sum (fun l hl => hbound l hl)
    _ = J.card*(2*2^n) := by simp
    _ ≤ r*(2*2^n) := Nat.mul_le_mul_right _ hJ
    _ = _ := by ring

lemma exceptional_samples {n r t : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (hM : ∀ j l : Fin r, j≠l → 128*(Finset.univ.filter (fun i => M j i=M l i)).card ≤ n) :
    2^(n/65536) *
      ((Finset.univ : Finset (Sample n r t)).filter (fun s => ¬safe M s)).card ≤
      2*r*Fintype.card (Sample n r t) := by
  classical
  have he : ((Finset.univ : Finset (Sample n r t)).filter (fun s => ¬safe M s)).card =
      ∑ j : Fin r, ∑ b : Bool, ∑ T : Choices n t,
        ((Finset.univ : Finset (Fin n → Bool)).filter (fun z => ¬safe M (j,b,T,z))).card := by
    simp only [Finset.card_filter,Fintype.sum_prod_type]
  rw [he]
  calc
    _ = ∑ j : Fin r, ∑ b : Bool, ∑ T : Choices n t,
        2^(n/65536)*((Finset.univ : Finset (Fin n → Bool)).filter
          (fun z => ¬safe M (j,b,T,z))).card := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ _j : Fin r, ∑ _b : Bool, ∑ _T : Choices n t, 2*r*2^n := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro b _
      exact Finset.sum_le_sum (fun T _ => exceptional_z hn M hM j b T)
    _ = _ := by simp [Sample,Fintype.card_fun,mul_assoc,mul_comm,mul_left_comm]


def flip {n : ℕ} (x : Raw n → Bool) (v : Raw n) (w : Raw n) : Bool :=
  if w=v then !(x w) else x w

def endpoint {n : ℕ} (M : Equiv.Perm (Fin n)) (i : Fin n) (side : Bool) : Raw n :=
  if side then (true,M i) else (false,i)

lemma flip_color {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool)
    (i : Fin n) (side b : Bool) :
    colorSet M (flip x (endpoint M i side)) b =
      if i∈colorSet M x b then (colorSet M x b).erase i else insert i (colorSet M x b) := by
  classical
  by_cases hi : i∈colorSet M x b
  · rw [if_pos hi]
    ext j
    by_cases hj : j=i
    · subst j
      cases side <;> cases b <;> cases h0 : x (false,i) <;> cases h1 : x (true,M i) <;>
        simp_all [colorSet,flip,endpoint]
    · have hm : M j≠M i := M.injective.ne hj
      cases side <;> simp [colorSet,flip,endpoint,hj,hm]
  · rw [if_neg hi]
    ext j
    by_cases hj : j=i
    · subst j
      cases side <;> cases b <;> cases h0 : x (false,i) <;> cases h1 : x (true,M i) <;>
        simp_all [colorSet,flip,endpoint]
    · have hm : M j≠M i := M.injective.ne hj
      cases side <;> simp [colorSet,flip,endpoint,hj,hm]

lemma flip_endpoint_dist {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool)
    (i : Fin n) (side : Bool) :
    |((colorSet M (flip x (endpoint M i side)) true).card : ℝ)-
      ((colorSet M x true).card : ℝ)| ≤ 1 := by
  have h := card_difference (colorSet M (flip x (endpoint M i side)) true)
    (colorSet M x true) {i} (by
      intro j hj
      have hji : j≠i := by simpa using hj
      rw [flip_color]
      by_cases hi : i∈colorSet M x true <;> simp [hi,hji])
  simpa using h

lemma flip_dist {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) (v : Raw n) :
    |((colorSet M (flip x v) true).card : ℝ)-((colorSet M x true).card : ℝ)| ≤ 1 := by
  rcases v with ⟨s,i⟩
  cases s
  · simpa [endpoint] using flip_endpoint_dist M x i false
  · simpa [endpoint] using flip_endpoint_dist M x (M.symm i) true

lemma band_linear (n d : ℕ) :
    16*Nat.dist (2*d) n≤n ↔ 15*n≤32*d ∧ 32*d≤17*n := by
  by_cases h : 2*d≤n
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

lemma flip_band {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) (v : Raw n)
    (hc : 15*n+32≤32*(colorSet M x true).card ∧
      32*(colorSet M x true).card+32≤17*n) :
    band M (flip x v) := by
  have hd := abs_le.mp (flip_dist M x v)
  have h0 : (15 : ℝ)*n+32≤32*((colorSet M x true).card : ℝ) := by exact_mod_cast hc.1
  have h1 : (32 : ℝ)*((colorSet M x true).card : ℝ)+32≤17*n := by exact_mod_cast hc.2
  have hl : (15 : ℝ)*n≤32*((colorSet M (flip x v) true).card : ℝ) := by linarith
  have hu : (32 : ℝ)*((colorSet M (flip x v) true).card : ℝ)≤17*n := by linarith
  exact (band_linear n _).mpr ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩

lemma colorSet_partition {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool) :
    (colorSet M x false).card+(colorSet M x true).card=n := by
  rw [colorSet_false_card]
  have h : (colorSet M x true).card≤n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  omega

lemma boundary_repair {n : ℕ} (hn : 128≤n) (M : Equiv.Perm (Fin n))
    (b : Bool) (T : Finset (Fin n)) (z : Fin n → Bool)
    (hT : T.card=17*n/32+1) (i : Fin n) (hi : i∈T) (side : Bool) :
    band M (flip (boundary M b T z) (endpoint M i side)) := by
  have he : colorSet M (flip (boundary M b T z) (endpoint M i side)) b=T.erase i := by
    rw [flip_color,boundary_color,if_pos hi]
  have hc : (colorSet M (flip (boundary M b T z) (endpoint M i side)) b).card =17*n/32 := by
    rw [he,Finset.card_erase_of_mem hi,hT]
    omega
  have hp := colorSet_partition M (flip (boundary M b T z) (endpoint M i side))
  apply (band_iff_colors M _).mpr
  have hn' : n≤2*(17*n/32) := by omega
  cases b <;> constructor <;> omega

lemma safe_repair {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (s : Sample n r (17*n/32+1)) (hs : safe M s)
    (i : Fin n) (hi : i∈s.2.2.1.val) (side : Bool) :
    ∀ l : Fin r, band (M l) (flip (word M s) (endpoint (M s.1) i side)) := by
  intro l
  by_cases hl : l=s.1
  · subst l
    exact boundary_repair hn (M s.1) s.2.1 s.2.2.1.val s.2.2.2
      (Finset.mem_powersetCard.mp s.2.2.1.property).2 i hi side
  · exact flip_band (M l) (word M s) _ (hs l hl)

lemma literal_of_flip {n : ℕ} (c : Clause n) (x : Raw n → Bool) (v : Raw n)
    (hf : ¬PEqualNP.ProofComplexity.ClauseSat x c)
    (ht : PEqualNP.ProofComplexity.ClauseSat (flip x v) c) :
    (v,!(x v))∈c := by
  obtain ⟨l,hl,hv⟩ := ht
  have he : l.1=v := by
    by_contra h
    have hx : x l.1=l.2 := by simpa [flip,h] using hv
    exact hf ⟨l,hl,hx⟩
  have hs : l.2= !(x v) := by simpa [flip,he] using hv.symm
  have hLit : l=(v,!(x v)) := Prod.ext he hs
  simpa only [hLit] using hl

lemma clause_subset_of_repairs {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool)
    (T : Finset (Fin n)) (z : Fin n → Bool) (c : Clause n)
    (hf : ¬PEqualNP.ProofComplexity.ClauseSat (boundary M b T z) c)
    (hr : ∀ i∈T, ∀ side : Bool, PEqualNP.ProofComplexity.ClauseSat
      (flip (boundary M b T z) (endpoint M i side)) c) :
    badClause M b T z ⊆ c := by
  intro l hl
  rcases Finset.mem_union.mp hl with hl | hl
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    simpa [endpoint,boundary] using
      literal_of_flip c (boundary M b T z) (endpoint M i false) hf (hr i hi false)
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    simpa [endpoint,boundary,hi] using
      literal_of_flip c (boundary M b T z) (endpoint M i true) hf (hr i hi true)

lemma safe_clause_subset {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (s : Sample n r (17*n/32+1)) (hs : safe M s) (c : Clause n)
    (hc : ∀ x, (∀ j, band (M j) x) → PEqualNP.ProofComplexity.ClauseSat x c)
    (hf : ¬PEqualNP.ProofComplexity.ClauseSat (word M s) c) :
    badClause (M s.1) s.2.1 s.2.2.1.val s.2.2.2 ⊆ c := by
  apply clause_subset_of_repairs (M s.1) s.2.1 s.2.2.1.val s.2.2.2 c hf
  intro i hi side
  exact hc _ (safe_repair hn M s hs i hi side)


abbrev reject {n : ℕ} (x : Raw n → Bool) (c : Clause n) : Prop :=
  (c.filter (fun l => x l.1=l.2)).card=0

lemma reject_iff {n : ℕ} (x : Raw n → Bool) (c : Clause n) :
    reject x c ↔ ¬PEqualNP.ProofComplexity.ClauseSat x c := by
  simp only [reject,Finset.card_eq_zero,Finset.filter_eq_empty_iff,
    PEqualNP.ProofComplexity.ClauseSat,not_exists,not_and]

lemma band_color_bound {n : ℕ} (M : Equiv.Perm (Fin n)) (x : Raw n → Bool)
    (hx : band M x) (b : Bool) : (colorSet M x b).card≤17*n/32 := by
  cases b
  · exact ((band_iff_colors M x).mp hx).2
  · exact ((band_iff_colors M x).mp hx).1

lemma bool_eq_not_of_ne (a b : Bool) (h : a≠b) : a= !b := by
  cases a <;> cases b <;> simp_all

lemma boundary_other_card {n : ℕ} (M : Equiv.Perm (Fin n)) (b : Bool)
    (T : Finset (Fin n)) (z : Fin n → Bool) :
    (colorSet M (boundary M b T z) (!b)).card=n-T.card := by
  have hc := congrArg Finset.card (boundary_color M b T z)
  have hp := colorSet_partition M (boundary M b T z)
  cases b <;> simp only [Bool.not_false,Bool.not_true] at * <;> omega

lemma safe_collision {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (s u : Sample n r (17*n/32+1)) (hs : safe M s) (hu : safe M u) (c : Clause n)
    (hc : ∀ x, (∀ j, band (M j) x) → PEqualNP.ProofComplexity.ClauseSat x c)
    (hfs : ¬PEqualNP.ProofComplexity.ClauseSat (word M s) c)
    (hfu : ¬PEqualNP.ProofComplexity.ClauseSat (word M u) c) :
    s.1=u.1 ∧ s.2.1=u.2.1 ∧ s.2.2.1.val=u.2.2.1.val ∧
      ∀ i∈s.2.2.1.val, s.2.2.2 i=u.2.2.2 i := by
  classical
  have hsub := safe_clause_subset hn M s hs c hc hfs
  have hfalse : ¬PEqualNP.ProofComplexity.ClauseSat (word M u)
      (badClause (M s.1) s.2.1 s.2.2.1.val s.2.2.2) := by
    intro ⟨l,hl,hv⟩
    exact hfu ⟨l,hsub hl,hv⟩
  have hcolors := badClause_forces (M s.1) s.2.1 s.2.2.1.val s.2.2.2 (word M u) hfalse
  have ht0 : s.2.2.1.val.card=17*n/32+1 :=
    (Finset.mem_powersetCard.mp s.2.2.1.property).2
  have ht1 : u.2.2.1.val.card=17*n/32+1 :=
    (Finset.mem_powersetCard.mp u.2.2.1.property).2
  have hj : s.1=u.1 := by
    by_contra hne
    have hd := hu s.1 hne
    have hBand : band (M s.1) (word M u) :=
      (band_linear n _).mpr ⟨by omega,by omega⟩
    have hb := band_color_bound (M s.1) (word M u) hBand s.2.1
    have ht := Finset.card_le_card hcolors
    omega
  have hb : s.2.1=u.2.1 := by
    by_contra hne
    have hneg := bool_eq_not_of_ne _ _ hne
    have hcard : (colorSet (M s.1) (word M u) s.2.1).card=n-u.2.2.1.val.card := by
      rw [hj,hneg]
      exact boundary_other_card (M u.1) u.2.1 u.2.2.1.val u.2.2.2
    have ht := Finset.card_le_card hcolors
    rw [hcard] at ht
    omega
  have hTsub : s.2.2.1.val⊆u.2.2.1.val := by
    rw [hj,hb] at hcolors
    simpa only [word,boundary_color] using hcolors
  have hT : s.2.2.1.val=u.2.2.1.val :=
    Finset.eq_of_subset_of_card_le hTsub (by rw [ht0,ht1])
  refine ⟨hj,hb,hT,?_⟩
  intro i hi
  have hz := ((badClause_false (M s.1) s.2.1 s.2.2.1.val s.2.2.2 (word M u)).mp hfalse i hi).1
  simpa [word,boundary] using hz.symm

lemma safe_wide {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (s : Sample n r (17*n/32+1)) (hs : safe M s) (c : Clause n)
    (hc : ∀ x, (∀ j, band (M j) x) → PEqualNP.ProofComplexity.ClauseSat x c)
    (hf : ¬PEqualNP.ProofComplexity.ClauseSat (word M s) c) :
    2*(17*n/32+1)≤c.card := by
  have h := Finset.card_le_card (safe_clause_subset hn M s hs c hc hf)
  rw [badClause_card,(Finset.mem_powersetCard.mp s.2.2.1.property).2] at h
  exact h

lemma safe_rejected_card {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (c : Clause n)
    (hc : ∀ x, (∀ j, band (M j) x) → PEqualNP.ProofComplexity.ClauseSat x c) :
    ((Finset.univ : Finset (Sample n r (17*n/32+1))).filter
      (fun s => safe M s ∧ reject (word M s) c)).card ≤ 2^(n-(17*n/32+1)) := by
  classical
  let t := 17*n/32+1
  let B := (Finset.univ : Finset (Sample n r t)).filter (fun s => safe M s ∧ reject (word M s) c)
  change B.card≤2^(n-t)
  by_cases hB : B.Nonempty
  · obtain ⟨s0,hs0⟩ := hB
    have h0 := (Finset.mem_filter.mp hs0).2
    let g : ↥B → (↥((s0.2.2.1.val)ᶜ) → Bool) :=
      fun s i => s.val.2.2.2 i.val
    have hg : Function.Injective g := by
      intro s u hgu
      have hs := (Finset.mem_filter.mp s.property).2
      have hu := (Finset.mem_filter.mp u.property).2
      have h0s := safe_collision hn M s0 s.val h0.1 hs.1 c hc
        ((reject_iff _ _).mp h0.2) ((reject_iff _ _).mp hs.2)
      have h0u := safe_collision hn M s0 u.val h0.1 hu.1 c hc
        ((reject_iff _ _).mp h0.2) ((reject_iff _ _).mp hu.2)
      have hj : s.val.1=u.val.1 := h0s.1.symm.trans h0u.1
      have hb : s.val.2.1=u.val.2.1 := h0s.2.1.symm.trans h0u.2.1
      have hT : s.val.2.2.1=u.val.2.2.1 :=
        Subtype.ext (h0s.2.2.1.symm.trans h0u.2.2.1)
      have hz : s.val.2.2.2=u.val.2.2.2 := by
        funext i
        by_cases hi : i∈s0.2.2.1.val
        · exact (h0s.2.2.2 i hi).symm.trans (h0u.2.2.2 i hi)
        · have he := congrArg (fun f : ↥((s0.2.2.1.val)ᶜ) → Bool =>
            f ⟨i,Finset.mem_compl.mpr hi⟩) hgu
          exact he
      apply Subtype.ext
      exact Prod.ext hj (Prod.ext hb (Prod.ext hT hz))
    have hcard := Fintype.card_le_of_injective g hg
    have hT0 : s0.2.2.1.val.card=t := (Finset.mem_powersetCard.mp s0.2.2.1.property).2
    simpa [Fintype.card_fun,hT0] using hcard
  · have he : B=∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    simp [he]

lemma rejected_bound {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (c : Clause n)
    (hc : ∀ x, (∀ j, band (M j) x) → PEqualNP.ProofComplexity.ClauseSat x c) :
    ((Finset.univ : Finset (Sample n r (17*n/32+1))).filter
      (fun s => safe M s ∧ reject (word M s) c)).card ≤
      if 2*(17*n/32+1)≤c.card then 2^(n-(17*n/32+1)) else 0 := by
  classical
  by_cases hw : 2*(17*n/32+1)≤c.card
  · simpa only [if_pos hw] using safe_rejected_card hn M c hc
  · have he : ((Finset.univ : Finset (Sample n r (17*n/32+1))).filter
        (fun s => safe M s ∧ reject (word M s) c))=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨s,hs⟩
      have h := (Finset.mem_filter.mp hs).2
      exact hw (safe_wide hn M s h.1 c hc ((reject_iff _ _).mp h.2))
    rw [if_neg hw,he]
    simp


def hits {n r t : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (F : Finset (Clause n)) :
    Finset (Sample n r t) :=
  Finset.univ.filter (fun s => 0<(F.filter (fun c => reject (word M s) c)).card)

lemma hit_iff {n r t : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (F : Finset (Clause n))
    (s : Sample n r t) :
    s∈hits M F ↔ ∃ c∈F, reject (word M s) c := by
  constructor
  · intro h
    obtain ⟨c,hc⟩ := Finset.card_pos.mp (Finset.mem_filter.mp h).2
    exact ⟨c,(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
  · rintro ⟨c,hc,hr⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Finset.card_pos.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hr⟩⟩⟩

lemma clause_lower_bound {n r : ℕ} (hn : 128≤n) (M : Fin r → Equiv.Perm (Fin n))
    (hM : ∀ j l : Fin r, j≠l → 128*(Finset.univ.filter (fun i => M j i=M l i)).card ≤ n)
    (F : Finset (Clause n))
    (hF : ∀ x, (∀ j, band (M j) x) → ∀ c∈F, PEqualNP.ProofComplexity.ClauseSat x c) :
    2^(n/65536)*(hits (t:=17*n/32+1) M F).card ≤
      2^(n/65536)*2^(n-(17*n/32+1))*(F.filter (fun c => 2*(17*n/32+1)≤c.card)).card+
        2*r*Fintype.card (Sample n r (17*n/32+1)) := by
  classical
  let t := 17*n/32+1
  let P := 2^(n/65536)
  let H : Finset (Sample n r t) := hits M F
  let Bad := (Finset.univ : Finset (Sample n r t)).filter (fun s => ¬safe M s)
  let R := fun c : Clause n => (Finset.univ : Finset (Sample n r t)).filter
    (fun s => safe M s ∧ reject (word M s) c)
  have hsub : H ⊆ Bad ∪ F.biUnion R := by
    intro s hs
    obtain ⟨c,hc,hr⟩ := (hit_iff M F s).mp hs
    by_cases hsafe : safe M s
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsafe,hr⟩⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsafe⟩
  have hR : ∀ c∈F, (R c).card ≤ if 2*t≤c.card then 2^(n-t) else 0 := by
    intro c hc
    exact rejected_bound hn M c (fun x hx => hF x hx c hc)
  have hcard : H.card≤Bad.card+2^(n-t)*(F.filter (fun c => 2*t≤c.card)).card := by
    calc
      _ ≤ (Bad∪F.biUnion R).card := Finset.card_le_card hsub
      _ ≤ Bad.card+(F.biUnion R).card := Finset.card_union_le _ _
      _ ≤ Bad.card+∑ c∈F, (R c).card := Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ Bad.card+∑ c∈F, if 2*t≤c.card then 2^(n-t) else 0 :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun c hc => hR c hc)) _
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [Nat.mul_comm]
  have hBad : P*Bad.card≤2*r*Fintype.card (Sample n r t) := exceptional_samples hn M hM
  change P*H.card≤P*2^(n-t)*(F.filter (fun c => 2*t≤c.card)).card+
    2*r*Fintype.card (Sample n r t)
  calc
    _ ≤ P*(Bad.card+2^(n-t)*(F.filter (fun c => 2*t≤c.card)).card) :=
      Nat.mul_le_mul_left P hcard
    _ = P*Bad.card+P*2^(n-t)*(F.filter (fun c => 2*t≤c.card)).card := by ring
    _ ≤ 2*r*Fintype.card (Sample n r t)+
        P*2^(n-t)*(F.filter (fun c => 2*t≤c.card)).card :=
      Nat.add_le_add_right hBad _
    _ = _ := by omega

end PEqualNP.Outside.L_pcx_346
theorem PEqualNP.Outside.L_pcx_346 :
∃ N : ℕ, ∀ (n r : ℕ), N ≤ n → ∀ M : Fin r → Equiv.Perm (Fin n),
  (∀ j l : Fin r, j ≠ l →
    128*(Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
  let V := Bool × Fin n
  let X := V → Bool
  let Cl := PEqualNP.ProofComplexity.Clause V
  let sat := fun (F : Finset Cl) (x : X) => ∀ c ∈ F, PEqualNP.ProofComplexity.ClauseSat x c
  let accept := fun x : X => ∀ j : Fin r,
    let d := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
    16 * Nat.dist (2*d) n ≤ n
  let t := 17*n/32+1
  let subsets := (Finset.univ : Finset (Fin n)).powersetCard t
  let Sample := Fin r × Bool × {T : Finset (Fin n) // T ∈ subsets} × (Fin n → Bool)
  let word := fun (s : Sample) (v : V) =>
    let z := s.2.2.2
    let i := (M s.1).symm v.2
    if v.1 then xor (z i) (if i ∈ s.2.2.1.val then s.2.1 else !s.2.1) else z v.2
  let slots := 2*r*Nat.choose n t*2^t
  let P := 2^(n/65536)
  (∃ F : Finset Cl, (∀ x : X, accept x ↔ sat F x) ∧ F.card ≤ slots ∧
    ∀ c ∈ F, c.card = 2*t) ∧
  (∀ F : Finset Cl, (∀ x : X, accept x → sat F x) →
    let hits := (Finset.univ.filter (fun s : Sample =>
      0 < (F.filter (fun c => (c.filter (fun lit => word s lit.1 = lit.2)).card = 0)).card)).card
    let wide := (F.filter (fun c => 2*t ≤ c.card)).card
    P*hits ≤ P*2^(n-t)*wide + 2*r*Fintype.card Sample) := by
  classical
  refine ⟨128,?_⟩
  intro n r hn M hM
  dsimp only
  constructor
  · obtain ⟨F,hC,hN,hW⟩ := PEqualNP.Outside.L_pcx_346.canonical_cnf n r M
    refine ⟨F,?_,hN,hW⟩
    intro x
    simpa only [PEqualNP.Outside.L_pcx_346.band,PEqualNP.Outside.L_pcx_346.colorSet_true] using hC x
  · intro F hF
    have hc : ∀ x, (∀ j, PEqualNP.Outside.L_pcx_346.band (M j) x) →
        ∀ c∈F, PEqualNP.ProofComplexity.ClauseSat x c := by
      intro x hx
      apply hF x
      intro j
      simpa only [PEqualNP.Outside.L_pcx_346.band,PEqualNP.Outside.L_pcx_346.colorSet_true] using hx j
    have h := PEqualNP.Outside.L_pcx_346.clause_lower_bound hn M hM F hc
    simpa [PEqualNP.Outside.L_pcx_346.hits,PEqualNP.Outside.L_pcx_346.word,
      PEqualNP.Outside.L_pcx_346.boundary,PEqualNP.Outside.L_pcx_346.reject,
      PEqualNP.Outside.L_pcx_346.Sample,PEqualNP.Outside.L_pcx_346.Choices,
      Fintype.card_fun] using h


