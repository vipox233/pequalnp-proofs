import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_792

open Finset Matrix

section

variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

def fz (z : ℚ) (a : A) : ℚ := if a = 0 then z - 1 else -1

def Tm (z : ℚ) (h : A) : Matrix (Option A) (Option A) ℚ := fun before after =>
  before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
    (fun a => after.elim (fz z a) (fun b => if b = a + h then 1 else 0))

def ser (z : ℚ) (w : List A) : ℚ := (w.map (Tm z)).prod none none

def Fits (z : ℚ) (k : ℕ) (test : List A → Prop) : Prop :=
  ∃ (left right : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
    ∀ w : List A, test w →
      (∑ i : Fin k, ∑ j : Fin k, left i * (w.map M).prod i j * right j) = ser z w

@[simp] theorem Tm_nn (z : ℚ) (h : A) : Tm z h none none = 1 := rfl
@[simp] theorem Tm_ns (z : ℚ) (h b : A) : Tm z h none (some b) = if b = h then 1 else 0 := rfl
@[simp] theorem Tm_sn (z : ℚ) (h a : A) : Tm z h (some a) none = fz z a := rfl
@[simp] theorem Tm_ss (z : ℚ) (h a b : A) :
    Tm z h (some a) (some b) = if b = a + h then 1 else 0 := rfl

theorem ser_nil (z : ℚ) : ser z ([] : List A) = 1 := by simp [ser]

theorem ser_one (z : ℚ) (a : A) : ser z [a] = 1 := by simp [ser]

theorem ser_two (z : ℚ) (a b : A) : ser z [a, b] = 1 + fz z a := by
  simp [ser, Matrix.mul_apply, Fintype.sum_option]

theorem ser_three (z : ℚ) (a b c : A) :
    ser z [a, b, c] = 1 + fz z a + fz z b + fz z (a + b) := by
  simp [ser, Matrix.mul_apply, Fintype.sum_option]
  ring

theorem sum_fz (z : ℚ) : ∑ x : A, fz z x = z - Fintype.card A := by
  have h : ∀ x : A, fz z x = (if x = 0 then z else 0) - 1 := by
    intro x; unfold fz; split_ifs <;> ring
  simp [h, Finset.sum_sub_distrib]

theorem sum_fz_mul (z : ℚ) (a : A) (c : A → ℚ) :
    ∑ b, fz z (a + b) * c b = z * c (-a) - ∑ b, c b := by
  have h : ∀ b, fz z (a + b) * c b = (if b = -a then z * c b else 0) - c b := by
    intro b
    by_cases hb : b = -a
    · subst hb
      simp only [fz, add_neg_cancel, eq_self_iff_true, ite_true, if_true]
      ring
    · have h2 : a + b ≠ 0 := by
        rw [add_comm]; exact fun e => hb (eq_neg_iff_add_eq_zero.mpr e)
      simp only [fz]
      rw [if_neg h2, if_neg hb]
      ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem card_ne_zero_sub : Fintype.card A = Fintype.card {a : A // a ≠ 0} + 1 := by
  have := Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℕ)) 0
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at this
  omega

/-! Upper bounds -/

theorem lump_prod {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq σ] [DecidableEq ι]
    (T : A → Matrix σ σ ℚ) (P : Matrix σ ι ℚ) (M : A → Matrix ι ι ℚ)
    (h : ∀ a, T a * P = P * M a) (w : List A) :
    (w.map T).prod * P = P * (w.map M).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem pad_fits (z : ℚ) {ι : Type} [Fintype ι] [DecidableEq ι] (left right : ι → ℚ)
    (M : A → Matrix ι ι ℚ)
    (hM : ∀ w : List A, ∑ i, ∑ j, left i * (w.map M).prod i j * right j = ser z w)
    (k : ℕ) (hk : Fintype.card ι ≤ k) : Fits (A := A) z k (fun _ => True) := by
  classical
  let R := Fin (k - Fintype.card ι)
  have hc : Fintype.card (ι ⊕ R) = k := by simp [R, Fintype.card_sum]; omega
  let e : ι ⊕ R ≃ Fin k := Fintype.equivFinOfCardEq hc
  let M' : A → Matrix (ι ⊕ R) (ι ⊕ R) ℚ := fun a => Matrix.fromBlocks (M a) 0 0 0
  have hprod : ∀ w : List A, ∃ D, (w.map M').prod = Matrix.fromBlocks (w.map M).prod 0 0 D := by
    intro w
    induction w with
    | nil => exact ⟨1, by simp [Matrix.fromBlocks_one]⟩
    | cons a w ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨0, ?_⟩
      simp only [List.map_cons, List.prod_cons, hD, M', Matrix.fromBlocks_multiply]
      simp
  have hsub : ∀ w : List A, (w.map (fun a => (M' a).submatrix e.symm e.symm)).prod =
      ((w.map M').prod).submatrix e.symm e.symm := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih => simp only [List.map_cons, List.prod_cons, ih, Matrix.submatrix_mul_equiv]
  have h1 : ∀ g : (ι ⊕ R) → (ι ⊕ R) → ℚ,
      ∑ i : Fin k, ∑ j : Fin k, g (e.symm i) (e.symm j) = ∑ x, ∑ y, g x y := fun g =>
    Fintype.sum_equiv e.symm _ _ (fun i => Fintype.sum_equiv e.symm _ _ (fun j => rfl))
  refine ⟨fun i => Sum.elim left 0 (e.symm i), fun j => Sum.elim right 0 (e.symm j),
    fun a => (M' a).submatrix e.symm e.symm, fun w _ => ?_⟩
  rw [hsub w]
  obtain ⟨D, hD⟩ := hprod w
  rw [hD]
  refine (h1 (fun x y => Sum.elim left 0 x * Matrix.fromBlocks (w.map M).prod 0 0 D x y *
    Sum.elim right 0 y)).trans ?_
  rw [← hM w]
  simp [Fintype.sum_sum_type]

theorem fits_of_lump (z : ℚ) {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix (Option A) ι ℚ)
    (M : A → Matrix ι ι ℚ) (j0 : ι) (h : ∀ a, Tm z a * P = P * M a)
    (hP : ∀ t, P t j0 = if t = none then 1 else 0) (k : ℕ) (hk : Fintype.card ι ≤ k) :
    Fits (A := A) z k (fun _ => True) := by
  refine pad_fits z (fun i => P none i) (fun j => if j = j0 then 1 else 0) M ?_ k hk
  intro w
  have h2 := congrFun (congrFun (lump_prod (Tm z) P M h w) none) j0
  simp only [Matrix.mul_apply, hP, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact h2.symm

def P0 : Matrix (Option A) (Option Unit) ℚ := fun t j =>
  Option.elim t (Option.elim j 1 (fun _ => 0)) (fun _ => Option.elim j 0 (fun _ => 1))

def M0 : Matrix (Option Unit) (Option Unit) ℚ := fun i j =>
  Option.elim i 1 (fun _ => Option.elim j (-1) (fun _ => 1))

theorem up_zero (k : ℕ) (hk : 2 ≤ k) : Fits (0 : ℚ) k (fun _ : List A => True) := by
  refine fits_of_lump 0 P0 (fun _ => M0) none ?_ ?_ k (by simpa using hk)
  · intro a
    ext t j
    rcases t with _ | x <;> rcases j with _ | u <;>
      simp [Matrix.mul_apply, Fintype.sum_option, P0, M0, fz]
  · intro t
    rcases t with _ | x <;> simp [P0]

def Pq : Matrix (Option A) (Option {a : A // a ≠ 0}) ℚ := fun t j =>
  Option.elim t (Option.elim j 1 (fun _ => 0))
    (fun a => Option.elim j 0 (fun a' => if a = 0 then -1 else if a = a'.val then 1 else 0))

@[simp] theorem Pq_nn : (Pq : Matrix (Option A) _ ℚ) none none = 1 := rfl
@[simp] theorem Pq_ns (a' : {a : A // a ≠ 0}) : (Pq : Matrix (Option A) _ ℚ) none (some a') = 0 := rfl
@[simp] theorem Pq_sn (x : A) : (Pq : Matrix (Option A) _ ℚ) (some x) none = 0 := rfl
@[simp] theorem Pq_ss (x : A) (a' : {a : A // a ≠ 0}) :
    (Pq : Matrix (Option A) _ ℚ) (some x) (some a') =
      if x = 0 then -1 else if x = a'.val then 1 else 0 := rfl

def Xq (z : ℚ) (h : A) : Matrix (Option A) (Option {a : A // a ≠ 0}) ℚ :=
  fun t j' => ∑ s : Option A, Tm z h t s * Pq s j'

def Mq (z : ℚ) (h : A) : Matrix (Option {a : A // a ≠ 0}) (Option {a : A // a ≠ 0}) ℚ :=
  fun j j' => Xq z h (j.map Subtype.val) j'

theorem up_q (z : ℚ) (hz : z = Fintype.card A) (k : ℕ) (hk : Fintype.card A ≤ k) :
    Fits z k (fun _ : List A => True) := by
  refine fits_of_lump z Pq (Mq z) none ?_ ?_ k ?_
  · intro h
    have hX : ∀ x j', Xq z h (some x) j' = fz z x * Pq none j' + Pq (some (x + h)) j' := by
      intro x j'
      simp [Xq, Fintype.sum_option]
    have hcol : ∀ j' : Option {a : A // a ≠ 0}, ∑ y : A, Pq (some y) j' = 0 := by
      intro j'
      rcases j' with _ | a'
      · simp
      · have e1 : ∀ y : A, (if y = 0 then (-1 : ℚ) else if y = a'.val then 1 else 0) =
            (if y = a'.val then 1 else 0) - (if y = 0 then 1 else 0) := by
          intro y
          by_cases hy : y = 0
          · subst hy; simp [Ne.symm a'.2]
          · simp [hy]
        simp only [Pq_ss, e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
    have hsum : ∀ j', ∑ x : A, Xq z h (some x) j' = 0 := by
      intro j'
      simp only [hX]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, sum_fz, hz, sub_self, zero_mul,
        zero_add]
      rw [show (∑ x : A, Pq (some (x + h)) j') = ∑ y : A, Pq (some y) j' from
        Fintype.sum_equiv (Equiv.addRight h) _ _ (fun x => rfl)]
      exact hcol j'
    ext t j'
    show Xq z h t j' = ∑ j, Pq t j * Mq z h j j'
    rw [Fintype.sum_option]
    rcases t with _ | x
    · simp [Mq]
    · by_cases hx : x = 0
      · subst hx
        have := hsum j'
        rw [Fintype.sum_eq_add_sum_subtype_ne _ 0] at this
        simp only [Pq_sn, zero_mul, zero_add, Pq_ss, if_true, neg_one_mul, Finset.sum_neg_distrib, Mq,
          Option.map_some]
        convert eq_neg_of_add_eq_zero_left this using 3
      · simp only [Pq_sn, zero_mul, zero_add]
        rw [Fintype.sum_eq_single ⟨x, hx⟩]
        · simp [hx, Mq]
        · intro a' ha'
          have hne : x ≠ a'.val := fun e => ha' (Subtype.ext e.symm)
          simp [hx, hne]
  · intro t
    rcases t with _ | x <;> simp
  · rw [Fintype.card_option, ← card_ne_zero_sub]
    exact hk

theorem up_gen (z : ℚ) (k : ℕ) (hk : Fintype.card A + 1 ≤ k) :
    Fits z k (fun _ : List A => True) := by
  refine fits_of_lump z 1 (Tm z) none ?_ ?_ k (by simpa using hk)
  · intro a; simp
  · intro t; simp [Matrix.one_apply]

/-! Lower bounds -/

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (X : Matrix ι (Fin d) K) (Y : Matrix (Fin d) ι K) (h : X * Y = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left X Y
  have h2 := Matrix.rank_le_card_width X
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

theorem dsum {k : ℕ} (left right : Fin k → ℚ) (N : Matrix (Fin k) (Fin k) ℚ) :
    ∑ i, ∑ j, left i * N i j * right j = left ⬝ᵥ (N *ᵥ right) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem lower (z : ℚ) {ι : Type} [Fintype ι] [DecidableEq ι] (emb : ι → A)
    (d : Option ι → ℚ) (c : Option ι → A → ℚ)
    (hnone : ∀ β, d β = if none = β then 1 else 0)
    (hsome : ∀ i β, d β + (z * c β (-emb i) - ∑ b, c β b) = if some i = β then 1 else 0)
    (k : ℕ) (hf : Fits (A := A) z k (fun w => w.length ≤ 3)) : Fintype.card ι + 1 ≤ k := by
  obtain ⟨left, right, M, hM⟩ := hf
  let L : List A → Fin k → ℚ := fun p => left ᵥ* (p.map M).prod
  let R : List A → Fin k → ℚ := fun s => (s.map M).prod *ᵥ right
  have key : ∀ p s : List A, (p ++ s).length ≤ 3 → L p ⬝ᵥ R s = ser z (p ++ s) := by
    intro p s hps
    show left ᵥ* (p.map M).prod ⬝ᵥ ((s.map M).prod *ᵥ right) = _
    rw [← hM _ hps, dsum, List.map_append, List.prod_append, ← Matrix.mulVec_mulVec]
    exact (Matrix.dotProduct_mulVec _ _ _).symm
  let pre : Option ι → List A := fun α => α.elim [] (fun i => [emb i])
  let G : Matrix (Fin k) A ℚ := fun j b => R [b, 0] j - R [0] j - fz z b * R [] j
  let X : Matrix (Option ι) (Fin k) ℚ := fun α j => L (pre α) j
  let Y : Matrix (Fin k) (Option ι) ℚ := fun j β => (d β • R [] + G *ᵥ c β) j
  have hG : ∀ p : List A, p.length ≤ 1 → ∀ b,
      (L p ᵥ* G) b = ser z (p ++ [b, 0]) - ser z (p ++ [0]) - fz z b * ser z (p ++ []) := by
    intro p hp b
    show L p ⬝ᵥ (R [b, 0] - R [0] - fz z b • R []) = _
    rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      key p _ (by simp; omega), key p _ (by simp; omega), key p _ (by simp; omega)]
  have hXY : ∀ α β, (X * Y) α β =
      d β * ser z (pre α) + ∑ b, (L (pre α) ᵥ* G) b * c β b := by
    intro α β
    show L (pre α) ⬝ᵥ (d β • R [] + G *ᵥ c β) = _
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul,
      key (pre α) [] (by rcases α with _ | i <;> simp [pre]), List.append_nil,
      Matrix.dotProduct_mulVec (L (pre α)) G (c β)]
    rfl
  have hone : X * Y = 1 := by
    ext α β
    rw [hXY, Matrix.one_apply]
    rcases α with _ | i
    · have : ∀ b, (L (pre none) ᵥ* G) b = 0 := by
        intro b
        rw [hG _ (by simp [pre])]
        simp only [pre, Option.elim_none, List.nil_append, ser_two, ser_one, ser_nil]
        ring
      simp only [this, zero_mul, Finset.sum_const_zero, add_zero]
      rw [hnone β]
      simp [pre, ser_nil]
    · have : ∀ b, (L (pre (some i)) ᵥ* G) b = fz z (emb i + b) := by
        intro b
        rw [hG _ (by simp [pre])]
        simp only [pre, Option.elim_some, List.singleton_append, ser_three, ser_two, ser_one,
          List.append_nil]
        ring
      simp only [this, sum_fz_mul]
      rw [← hsome i β]
      simp [pre, ser_one]
  have := rank_bound k X Y hone
  simpa using this

theorem low_zero (k : ℕ) (hf : Fits (0 : ℚ) k (fun w : List A => w.length ≤ 3)) : 2 ≤ k := by
  have := lower (0 : ℚ) (ι := Unit) (fun _ => (0 : A))
    (fun β => Option.elim β 1 (fun _ => 0))
    (fun β b => Option.elim β (if b = 0 then 1 else 0) (fun _ => if b = 0 then -1 else 0))
    (by intro β; rcases β with _ | u <;> simp)
    (by intro i β; rcases β with _ | u <;> simp)
    k hf
  simpa using this

theorem low_q (z : ℚ) (hz : z = Fintype.card A) (k : ℕ)
    (hf : Fits z k (fun w : List A => w.length ≤ 3)) : Fintype.card A ≤ k := by
  have hq : (Fintype.card A : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := A); positivity
  have := lower z (ι := {a : A // a ≠ 0}) (fun a => a.val)
    (fun β => Option.elim β 1 (fun _ => 0))
    (fun β b => Option.elim β (if b = 0 then 1 else 0)
      (fun a0 => (if b = -a0.val then 1 / (Fintype.card A : ℚ) else 0) -
        (if b = 0 then 1 / (Fintype.card A : ℚ) else 0)))
    (by intro β; rcases β with _ | u <;> simp)
    (by
      intro i β
      have hi : -i.val ≠ 0 := neg_ne_zero.mpr i.2
      rcases β with _ | a0
      · simp [hi]
      · simp only [Option.elim_some, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, sub_self, zero_add, if_neg hi, sub_zero, Option.some.injEq]
        by_cases h : i = a0
        · subst h; rw [if_pos rfl, if_pos rfl, hz]; field_simp
        · have h' : -i.val ≠ -a0.val := by
            intro e; apply h; exact Subtype.ext (neg_inj.mp e)
          rw [if_neg h', if_neg h]; ring)
    k hf
  rw [card_ne_zero_sub]
  exact this

theorem low_gen (z : ℚ) (hz0 : z ≠ 0) (hzq : z ≠ Fintype.card A) (k : ℕ)
    (hf : Fits z k (fun w : List A => w.length ≤ 3)) : Fintype.card A + 1 ≤ k := by
  have hzq' : z - Fintype.card A ≠ 0 := sub_ne_zero.mpr hzq
  have := lower z (ι := A) id
    (fun β => Option.elim β 1 (fun _ => 0))
    (fun β b => Option.elim β (-1 / (z - Fintype.card A))
      (fun a0 => (if b = -a0 then 1 / z else 0) + 1 / (z * (z - Fintype.card A))))
    (by intro β; rcases β with _ | u <;> simp)
    (by
      intro i β
      rcases β with _ | a0
      · simp only [Option.elim_none, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, if_neg
          (Option.some_ne_none i)]
        field_simp
        ring
      · simp only [Option.elim_some, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Option.some.injEq, id]
        by_cases h : i = a0
        · subst h; rw [if_pos rfl, if_pos rfl]; field_simp; ring
        · have h' : -i ≠ -a0 := fun e => h (neg_inj.mp e)
          rw [if_neg h', if_neg h]; field_simp; ring)
    k hf
  simpa using this

theorem main (z : ℚ) (q : ℚ) (hq : (Fintype.card A : ℚ) = q) (k : ℕ) :
    (Fits z k (fun w : List A => w.length ≤ 3) ↔
        (if z = 0 then (2 : ℚ) else if z = q then q else q + 1) ≤ (k : ℚ)) ∧
      (Fits z k (fun _ : List A => True) ↔
        (if z = 0 then (2 : ℚ) else if z = q then q else q + 1) ≤ (k : ℚ)) := by
  subst hq
  have mono : Fits z k (fun _ : List A => True) → Fits z k (fun w : List A => w.length ≤ 3) :=
    fun ⟨l, r, M, h⟩ => ⟨l, r, M, fun w _ => h w trivial⟩
  have up : (if z = 0 then (2 : ℚ) else if z = (Fintype.card A : ℚ) then (Fintype.card A : ℚ)
      else (Fintype.card A : ℚ) + 1) ≤ (k : ℚ) → Fits z k (fun _ : List A => True) := by
    split_ifs with h1 h2 <;> intro hk
    · subst h1; exact up_zero k (by exact_mod_cast hk)
    · exact up_q z h2 k (by exact_mod_cast hk)
    · exact up_gen z k (by exact_mod_cast hk)
  have low : Fits z k (fun w : List A => w.length ≤ 3) → (if z = 0 then (2 : ℚ)
      else if z = (Fintype.card A : ℚ) then (Fintype.card A : ℚ)
      else (Fintype.card A : ℚ) + 1) ≤ (k : ℚ) := by
    split_ifs with h1 h2 <;> intro hf
    · subst h1; exact_mod_cast low_zero k hf
    · exact_mod_cast low_q z h2 k hf
    · exact_mod_cast low_gen z h1 h2 k hf
  exact ⟨⟨low, fun h => mono (up h)⟩, ⟨fun h => low (mono h), up⟩⟩

end

end PEqualNP.Outside.L_lib_792

open PEqualNP.Outside.L_lib_792 in
theorem PEqualNP.Outside.L_lib_792 :
  ∀ (r : ℕ) (z : ℚ),
    let A := Fin r → ZMod 2
    let q := 2^r
    let f := fun a : A => if a = 0 then z-1 else -1
    let T : A → Matrix (Option A) (Option A) ℚ := fun h before after =>
      before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
        (fun a => after.elim (f a) (fun b => if b = a+h then 1 else 0))
    let series := fun w : List A => (w.map T).prod none none
    let fits := fun (k : ℕ) (test : List A → Prop) =>
      ∃ (left right : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List A, test w →
          (∑ i : Fin k, ∑ j : Fin k, left i * (w.map M).prod i j * right j) = series w
    let least := if z = 0 then 2 else if z = (q : ℚ) then q else q+1
    ∀ k : ℕ, (fits k (fun w => w.length ≤ 3) ↔ least ≤ k) ∧
      (fits k (fun _ => True) ↔ least ≤ k) := by
  intro r z A q f T series fits least k
  exact main (A := Fin r → ZMod 2) z ((2 : ℚ) ^ r) (by simp) k
