import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33634

open scoped BigOperators
namespace Loss
abbrev Circ := PEqualNP.CircuitLowerBounds.Circuit
abbrev X (N : ℕ) := Fin N
abbrev Tbl (N : ℕ) := X N → X N → Bool

def tab {N : ℕ} (C : Circ) : Tbl N := fun x y => C.eval (PEqualNP.Represents.oneEach x y)

def reg {N : ℕ} (t : ℕ) (T : Tbl N) : Prop :=
  (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
  (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)

def size {N : ℕ} (T : Tbl N) : ℕ :=
  ((Finset.univ : Finset (X N × X N)).filter (fun z => T z.1 z.2)).card

def loss {N : ℕ} (C T : Tbl N) : ℕ :=
  ((Finset.univ : Finset (X N × X N)).filter (fun z => C z.1 z.2 ≠ T z.1 z.2)).card

def err {N M : ℕ} (D : Fin M → Tbl N) (w : Fin M → ℝ) (T : Tbl N) : ℝ :=
  (N : ℝ)*∑ i, w i*(loss (D i) T : ℝ)

def bit (b : Bool) : ℝ := if b then 1 else 0

def inter {N : ℕ} (C T : Tbl N) : ℝ := ∑ x, ∑ y, bit (C x y) * bit (T x y)

lemma card_bit {α : Type*} [Fintype α] (p : α → Bool) :
    ((Finset.univ.filter fun a => p a).card : ℝ) = ∑ a, bit (p a) := by
  simp [bit, ← Finset.sum_filter]

lemma ind_ne (a b : Bool) : bit (decide (a ≠ b)) = bit a + bit b - 2 * bit a * bit b := by
  cases a <;> cases b <;> norm_num [bit]

lemma size_sum {N : ℕ} (T : Tbl N) : (size T : ℝ) = ∑ x, ∑ y, bit (T x y) := by
  rw [size, card_bit, Fintype.sum_prod_type]

lemma reg_size {N t : ℕ} {T : Tbl N} (hT : reg t T) : (size T : ℝ) = (N : ℝ)*t := by
  rw [size_sum]
  have hrow (x : X N) : ∑ y, bit (T x y) = (t : ℝ) := by rw [← card_bit, hT.1 x]
  simp [hrow]

lemma loss_eq {N : ℕ} (C T : Tbl N) :
    (loss C T : ℝ) = (size C : ℝ) + (size T : ℝ) - 2 * inter C T := by
  rw [loss, show (Finset.univ.filter (fun z : X N × X N => C z.1 z.2 ≠ T z.1 z.2)) =
    (Finset.univ.filter fun z : X N × X N => decide (C z.1 z.2 ≠ T z.1 z.2)) by ext z; simp]
  rw [card_bit, Fintype.sum_prod_type, size_sum C, size_sum T, inter]
  simp only [ind_ne, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

lemma sum_perm {α : Type*} [Fintype α] (e : α ≃ α) (f : α → ℝ) :
    ∑ a, f (e a) = ∑ a, f a := e.sum_comp f

lemma card_perm {α : Type*} [Fintype α] (e : α ≃ α) (f : α → Bool) :
    (Finset.univ.filter (fun a => f (e a))).card = (Finset.univ.filter (fun a => f a)).card := by
  exact_mod_cast (card_bit (fun a => f (e a))).trans ((sum_perm e (fun a => bit (f a))).trans (card_bit f).symm)

def shift {N : ℕ} [NeZero N] (T : Tbl N) (u : X N) : Tbl N := fun x y => T x (y + u)

lemma shift_reg {N t : ℕ} [NeZero N] {T : Tbl N} (hT : reg t T) (u : X N) : reg t (shift T u) := by
  refine ⟨fun x => (card_perm (Equiv.addRight u) (T x)).trans (hT.1 x), fun y => hT.2 (y + u)⟩

lemma sum_inter_shift {N t : ℕ} [NeZero N] (C : Tbl N) {T : Tbl N} (hT : reg t T) :
    ∑ u, inter C (shift T u) = (t : ℝ)*size C := by
  have hp (x y : X N) : ∑ u, bit (shift T u x y) = (t : ℝ) := by
    calc
      _ = ∑ u : X N, bit (T x u) := by
        let e : X N ≃ X N := ⟨fun u => y + u, fun u => u - y,
          fun u => add_sub_cancel_left y u, fun u => by
            change y + (u-y) = u
            rw [add_comm, sub_add_cancel]⟩
        exact sum_perm e (fun u => bit (T x u))
      _ = _ := ?_
    rw [← card_bit, hT.1 x]
  unfold inter
  rw [Finset.sum_comm]
  calc
    (∑ x, ∑ u, ∑ y, bit (C x y) * bit (shift T u x y)) =
        ∑ x, ∑ y, ∑ u, bit (C x y) * bit (shift T u x y) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ x, ∑ y, bit (C x y) * (t : ℝ) := by simp only [← Finset.mul_sum, hp]
    _ = _ := by simp only [size_sum, Finset.mul_sum, mul_comm (bit _) (t : ℝ)]

lemma sum_loss_shift {N t : ℕ} [NeZero N] (C : Tbl N) {T : Tbl N} (hT : reg t T) :
    ∑ u, (loss C (shift T u) : ℝ) = (N : ℝ)*(N*t)-(2*(t:ℝ)-N)*size C := by
  simp only [loss_eq, reg_size (shift_reg hT _), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, sum_inter_shift C hT]
  ring

lemma sum_err_shift {N t M : ℕ} [NeZero N] (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) {T : Tbl N} (hT : reg t T) :
    ∑ u, err D w (shift T u) = (N : ℝ) *
      ((N : ℝ)*(N*t)-(2*(t:ℝ)-N)*∑ i, w i * (size (D i) : ℝ)) := by
  unfold err
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_loss_shift _ hT, mul_sub, Finset.sum_sub_distrib]
  have h₁ : ∑ i, w i * ((N : ℝ)*(N*t)) = (N : ℝ)*(N*t) := by rw [← Finset.sum_mul, hw, one_mul]
  have h₂ : ∑ i, w i * ((2*(t:ℝ)-N)*size (D i)) = (2*(t:ℝ)-N) * ∑ i, w i * (size (D i) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h₁, h₂]

def benchR (N t A : ℕ) : ℝ := (N : ℝ)*(N*t)-(2*(t:ℝ)-N)*A

lemma sum_err_ge {N t M A : ℕ} [NeZero N] (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) (hp : ∀ i, 0 < w i) (hA : ∀ i, size (D i) ≤ A)
    (ht : N < 2*t) {T : Tbl N} (hT : reg t T) :
    (N : ℝ) * benchR N t A ≤ ∑ u, err D w (shift T u) := by
  have hS : ∑ i, w i * (size (D i) : ℝ) ≤ (A : ℝ) := calc
    _ ≤ ∑ i, w i * (A : ℝ) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast hA i) (hp i).le)
    _ = A := by rw [← Finset.sum_mul, hw, one_mul]
  rw [sum_err_shift _ _ hw hT, benchR]
  have hc : (0 : ℝ) ≤ 2*(t:ℝ)-N := by exact sub_nonneg.mpr (by exact_mod_cast ht.le)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (mul_le_mul_of_nonneg_left hS hc) _) (Nat.cast_nonneg _)

lemma adversary_exists {N t M A : ℕ} [NeZero N] (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) (hp : ∀ i, 0 < w i) (hA : ∀ i, size (D i) ≤ A)
    (ht : N < 2*t) {T : Tbl N} (hT : reg t T) :
    ∃ U, reg t U ∧ benchR N t A ≤ err D w U := by
  by_contra! hg
  have hlt : (∑ u, err D w (shift T u)) < ∑ _u : X N, benchR N t A := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · exact fun u _ => hg _ (shift_reg hT u)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  exact (not_lt_of_ge (sum_err_ge D w hw hp hA ht hT)) hlt

lemma saturates {N t M A : ℕ} [NeZero N] (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) (hp : ∀ i, 0 < w i) (hA : ∀ i, size (D i) ≤ A)
    (ht : N < 2*t) {T : Tbl N} (hT : reg t T)
    (hg : ∀ u, err D w (shift T u) ≤ benchR N t A) :
    (∀ i, size (D i) = A) ∧ (∀ u, err D w (shift T u) = benchR N t A) := by
  have hlo := sum_err_ge D w hw hp hA ht hT
  have hupper : (∑ u, err D w (shift T u)) ≤ (N : ℝ) * benchR N t A := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (X N))) (fun u _ => hg u)
  have heq := le_antisymm hupper hlo
  have hn : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hc : (0 : ℝ) < 2*(t:ℝ)-N := by exact sub_pos.mpr (by exact_mod_cast ht)
  have hsize : ∑ i, w i * (size (D i) : ℝ) = (A : ℝ) := by
    rw [sum_err_shift _ _ hw hT, benchR] at heq
    have he := (mul_left_cancel₀ hn.ne' heq)
    apply mul_left_cancel₀ hc.ne'
    linarith only [he]
  refine ⟨fun i => le_antisymm (hA i) ?_, fun u => le_antisymm (hg u) ?_⟩
  · by_contra! hi
    have hh : ∑ j, w j * (size (D j) : ℝ) < ∑ j, w j * (A : ℝ) := by
      apply Finset.sum_lt_sum
      · exact fun j _ => mul_le_mul_of_nonneg_left (by exact_mod_cast hA j) (hp j).le
      · exact ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left (by exact_mod_cast hi) (hp i)⟩
    rw [hsize, ← Finset.sum_mul, hw, one_mul] at hh
    exact (lt_irrefl _ hh)
  · by_contra! hu
    have hh : ∑ v, err D w (shift T v) < ∑ _v : X N, benchR N t A :=
      Finset.sum_lt_sum (fun v _ => hg v) ⟨u, Finset.mem_univ _, hu⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, heq] at hh
    exact (lt_irrefl _ hh)

end Loss

open scoped BigOperators
namespace Loss

private lemma card_slice {N t : ℕ} (h : t ≤ N) :
    (Finset.univ.filter (fun x : X N => decide (x.val < t))).card = t := by
  let e : Fin t ↪ Fin N := ⟨fun i => ⟨i.val, i.isLt.trans_le h⟩,
    fun _ _ he => Fin.ext (congrArg (fun j : Fin N => j.val) he)⟩
  have he : (Finset.univ.filter (fun x : X N => decide (x.val < t))) = Finset.univ.map e := by
    ext x
    constructor
    · intro hx
      have hx' : x.val < t := by simpa using (Finset.mem_filter.mp hx).2
      exact Finset.mem_map.mpr ⟨⟨x.val, hx'⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · rintro hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true_eq.mpr ?_⟩
      change j.val < t
      exact j.isLt
  rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def cyclic {N : ℕ} [NeZero N] (t : ℕ) : Tbl N := fun x y => decide ((y-x).val < t)

lemma cyclic_reg {N t : ℕ} [NeZero N] (ht : t ≤ N) : reg t (cyclic t : Tbl N) := by
  constructor
  · intro x
    let e : X N ≃ X N := ⟨fun y => y-x, fun z => z+x, fun y => sub_add_cancel y x,
      fun z => add_sub_cancel_right z x⟩
    exact (card_perm e (fun u => decide (u.val < t))).trans (card_slice ht)
  · intro y
    let e : X N ≃ X N := ⟨fun x => y-x, fun z => y-z, fun x => sub_sub_cancel y x,
      fun x => sub_sub_cancel y x⟩
    exact (card_perm e (fun u => decide (u.val < t))).trans (card_slice ht)

lemma perm_reg {N t : ℕ} {T : Tbl N} (hT : reg t T) (e f : X N ≃ X N) :
    reg t (fun x y => T (e x) (f y)) := by
  constructor
  · intro x
    exact (card_perm f (T (e x))).trans (hT.1 _)
  · intro y
    exact (card_perm e (fun x => T x (f y))).trans (hT.2 _)

private lemma pair_perm {α : Type*} [DecidableEq α] {a b c d : α} (hn : a ≠ b) (hm : c ≠ d) :
    ∃ e : α ≃ α, e a = c ∧ e b = d := by
  let f := Equiv.swap a c
  have hf : f a = c := Equiv.swap_apply_left a c
  have hs : f b ≠ c := fun he => hn (f.injective (hf.trans he.symm))
  refine ⟨f.trans (Equiv.swap (f b) d), ?_, Equiv.swap_apply_left _ _⟩
  change Equiv.swap (f b) d (f a) = c
  rw [hf, Equiv.swap_apply_of_ne_of_ne hs.symm hm]

lemma checkerboard {N t : ℕ} [NeZero N] (hN : 1 < N) (ht : 0 < t) (htN : t < N)
    {a b c d : X N} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ T : Tbl N, reg t T ∧ T a c = true ∧ T b d = true ∧ T a d = false ∧ T b c = false := by
  let x0 : X N := ⟨0, by omega⟩
  let x1 : X N := ⟨1, hN⟩
  let yt : X N := ⟨t, htN⟩
  obtain ⟨e, he0, he1⟩ := pair_perm hab (show x0 ≠ x1 by intro h; have := congrArg Fin.val h; simp [x0, x1] at this)
  obtain ⟨f, hf0, hf1⟩ := pair_perm hcd (show x0 ≠ yt by intro h; have := congrArg Fin.val h; simp [x0, yt] at this; omega)
  refine ⟨fun x y => cyclic t (e x) (f y), perm_reg (cyclic_reg htN.le) e f, ?_⟩
  simp only [he0, he1, hf0, hf1, cyclic, sub_self, decide_eq_true_eq, decide_eq_false_iff_not]
  have h0 : (0 : X N).val = 0 := rfl
  have hx : (yt-x1).val = t-1 := Fin.sub_val_of_le (by exact ht)
  have hy : (yt-x0).val = t := by rw [show x0 = 0 from rfl, sub_zero]
  have hz : (x0-x1).val = N-1 := by
    change (N - 1) % N = N - 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h0, hx, hy, hz]
  omega

lemma mixed_diff {N M t A : ℕ} [NeZero N] (hN : 1 < N) (ht : 0 < t) (htN : t < N)
    (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) (hp : ∀ i, 0 < w i) (hA : ∀ i, size (D i) ≤ A)
    (ht' : N < 2*t) (hg : ∀ T, reg t T → err D w T ≤ benchR N t A) :
    let G := fun x y => ∑ i, w i * bit (D i x y)
    ∀ a b c d, G a c + G b d = G a d + G b c := by
  dsimp only
  intro a b c d
  classical
  by_cases hab : a = b
  · subst b; exact add_comm _ _
  by_cases hcd : c = d
  · subst d; rfl
  obtain ⟨T, hT, hac, hbd, had, hbc⟩ := checkerboard hN ht htN hab hcd
  let U : Tbl N := fun x y => if x = a ∨ x = b then T x (Equiv.swap c d y) else T x y
  have hrow (x : X N) : (Finset.univ.filter (fun y => U x y)).card = t := by
    by_cases hx : x = a ∨ x = b
    · simpa only [U, if_pos hx] using (card_perm (Equiv.swap c d) (T x)).trans (hT.1 x)
    · simpa only [U, if_neg hx] using hT.1 x
  have hswap (x y : X N) (hy : y = c ∨ y = d) : U x y = T (Equiv.swap a b x) y := by
    rcases hy with rfl | rfl
    · by_cases hxa : x = a
      · subst x; simp [U, hab, had, hbc]
      by_cases hxb : x = b
      · subst x; simp [U, hab, hbd, hac]
      · simp [U, hxa, hxb, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    · by_cases hxa : x = a
      · subst x; simp [U, hab, hac, hbd]
      by_cases hxb : x = b
      · subst x; simp [U, hab, hbc, had]
      · simp [U, hxa, hxb, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hfixed (x y : X N) (hc : y ≠ c) (hd : y ≠ d) : U x y = T x y := by
    simp [U, Equiv.swap_apply_of_ne_of_ne hc hd]
  have hU : reg t U := ⟨hrow, fun y => by
    by_cases hy : y = c ∨ y = d
    · simpa only [hswap _ y hy] using (card_perm (Equiv.swap a b) (fun x => T x y)).trans (hT.2 y)
    · push_neg at hy
      simpa only [hfixed _ y hy.1 hy.2] using hT.2 y⟩
  have hgood (V : Tbl N) (hV : reg t V) : err D w V = benchR N t A := by
    have h := (saturates D w hw hp hA ht' hV (fun u => hg _ (shift_reg hV u))).2 (0 : X N)
    have hs : shift V (0 : X N) = V := by funext x y; change V x (y+0) = V x y; rw [add_zero]
    exact hs ▸ h
  have he := (hgood T hT).trans (hgood U hU).symm
  have hdiff (x y : X N) : bit (T x y) - bit (U x y) =
      ((if x = a then 1 else 0) - (if x = b then 1 else 0)) *
      ((if y = c then 1 else 0) - (if y = d then 1 else 0)) := by
    by_cases hx : x = a
    · subst x
      by_cases hy : y = c
      · subst y; norm_num [hswap a c (Or.inl rfl), hac, hbc, bit, hab, hcd]
      by_cases hz : y = d
      · subst y; norm_num [hswap a d (Or.inr rfl), had, hbd, bit, hab, Ne.symm hcd]
      · simp [hfixed a y hy hz, hy, hz]
    · by_cases hx' : x = b
      · subst x
        by_cases hy : y = c
        · subst y; norm_num [hswap b c (Or.inl rfl), hbc, hac, bit, Ne.symm hab, hcd]
        by_cases hz : y = d
        · subst y; norm_num [hswap b d (Or.inr rfl), hbd, had, bit, Ne.symm hab, Ne.symm hcd]
        · simp [hfixed b y hy hz, hy, hz]
      · simp [U, hx, hx']
  have hi (i : Fin M) : inter (D i) T - inter (D i) U =
      bit (D i a c) + bit (D i b d) - (bit (D i a d) + bit (D i b c)) := by
    simp only [inter, ← Finset.sum_sub_distrib, ← mul_sub, hdiff]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, zero_mul, mul_zero, mul_one, one_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  unfold err at he
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hh := mul_left_cancel₀ hn he
  have hsub : ∑ i, w i * ((loss (D i) T : ℝ) - (loss (D i) U : ℝ)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hh, sub_self]
  have hterm (i : Fin M) : (loss (D i) T : ℝ) - (loss (D i) U : ℝ) =
      -2 * (inter (D i) T - inter (D i) U) := by
    rw [loss_eq, loss_eq, reg_size hT, reg_size hU]
    ring
  simp only [hterm, hi] at hsub
  have hz : (∑ i, w i * (-2 * (bit (D i a c) + bit (D i b d) - (bit (D i a d) + bit (D i b c))))) =
      -2 * ((∑ i, w i * bit (D i a c)) + (∑ i, w i * bit (D i b d)) -
        ((∑ i, w i * bit (D i a d)) + (∑ i, w i * bit (D i b c)))) := by
    simp only [Finset.mul_sum, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [← mul_assoc, mul_comm (w _ : ℝ) (-2)]
  rw [hz] at hsub
  linarith only [hsub]

end Loss

open scoped BigOperators
namespace Loss

lemma bench_cast {N t A : ℕ} (h1 : N < 2*t) (h2 : t ≤ N) (hA : A ≤ N*N) :
    ((N*(N*t)-(2*t-N)*A : ℕ) : ℝ) = benchR N t A := by
  have h : (2*t-N)*A ≤ N*(N*t) := calc
    _ ≤ t * (N*N) := Nat.mul_le_mul (by omega) hA
    _ = _ := by ring
  rw [Nat.cast_sub h]
  simp only [Nat.cast_mul, Nat.cast_sub h1.le, Nat.cast_ofNat, benchR]

noncomputable def average {N M : ℕ} (D : Fin M → Tbl N) (w : Fin M → ℝ) (x y : X N) : ℝ :=
  ∑ i, w i * bit (D i x y)

def IsAdd {N : ℕ} (G : X N → X N → ℝ) : Prop :=
  ∀ a b c d, G a c + G b d = G a d + G b c

lemma weighted_inter {N M : ℕ} (D : Fin M → Tbl N) (w : Fin M → ℝ) (T : Tbl N) :
    ∑ i, w i * inter (D i) T = ∑ x, ∑ y, average D w x y * bit (T x y) := by
  unfold inter average
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, mul_assoc]

lemma regular_additive {N t : ℕ} {T U : Tbl N} (hT : reg t T) (hU : reg t U)
    (G : X N → X N → ℝ) (p q : X N → ℝ) (hG : ∀ x y, G x y = p x + q y) :
    ∑ x, ∑ y, G x y * bit (T x y) = ∑ x, ∑ y, G x y * bit (U x y) := by
  simp only [hG, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrow (x : X N) : ∑ y, bit (T x y) = ∑ y, bit (U x y) := by rw [← card_bit, ← card_bit, hT.1 x, hU.1 x]
  have hcol (y : X N) : ∑ x, bit (T x y) = ∑ x, bit (U x y) := by rw [← card_bit, ← card_bit, hT.2 y, hU.2 y]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => congrArg (p x * ·) (hrow x)
  · rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => q y * bit (U x y))]
    simp only [← Finset.mul_sum, hcol]

lemma err_same_of_add {N t M : ℕ} (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (p q : X N → ℝ) (hG : ∀ x y, average D w x y = p x + q y)
    {T U : Tbl N} (hT : reg t T) (hU : reg t U) : err D w T = err D w U := by
  have hi : ∑ i, w i * inter (D i) T = ∑ i, w i * inter (D i) U := by
    rw [weighted_inter, weighted_inter]
    exact regular_additive hT hU (average D w) p q hG
  unfold err
  simp only [loss_eq, reg_size hT, reg_size hU, mul_sub, Finset.sum_sub_distrib,
    show ∀ a b : ℝ, a * (2*b) = 2*(a*b) by intros; ring, ← Finset.mul_sum, hi]

lemma good_if_add {N t M A : ℕ} [NeZero N] (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (hw : ∑ i, w i = 1) (hA : ∀ i, size (D i) = A) (hG : IsAdd (average D w))
    {T : Tbl N} (hT : reg t T) : err D w T = benchR N t A := by
  let o : X N := 0
  let p := fun x => average D w x o
  let q := fun y => average D w o y - average D w o o
  have hdecomp (x y : X N) : average D w x y = p x + q y := by
    have h := hG x o y o
    dsimp only [p, q]
    linarith only [h]
  have he := sum_err_shift D w hw hT
  have hs (u : X N) : err D w (shift T u) = err D w T :=
    err_same_of_add D w p q hdecomp (shift_reg hT u) hT
  simp only [hs, hA, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, hw, one_mul] at he
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne N) he

lemma mixed_union_iff {N M : ℕ} (D : Fin M → Tbl N) (w : Fin M → ℝ)
    (A B : Fin M → Finset (X N)) (hD : ∀ i x y, D i x y = decide (x ∈ A i ∨ y ∈ B i)) :
    IsAdd (average D w) ↔ IsAdd (fun x y => ∑ i, if x ∈ A i ∧ y ∈ B i then w i else 0) := by
  have he (x y : X N) : average D w x y =
      (∑ i, if x ∈ A i then w i else 0) + (∑ i, if y ∈ B i then w i else 0) -
      (∑ i, if x ∈ A i ∧ y ∈ B i then w i else 0) := by
    simp only [average, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases ha : x ∈ A i <;> by_cases hb : y ∈ B i <;> simp [hD, bit, ha, hb]
  unfold IsAdd
  constructor <;> intro h a b c d <;> have hh := h a b c d
  · simp only [he] at hh; linarith only [hh]
  · simp only [he]; linarith only [hh]

lemma size_union_lines {N : ℕ} (R S : Finset (X N)) :
    size (fun x y => decide (x ∈ R ∨ y ∈ S)) = (R.card+S.card)*N - R.card*S.card := by
  classical
  let T₁ := R ×ˢ (Finset.univ : Finset (X N))
  let T₂ := (Finset.univ : Finset (X N)) ×ˢ S
  have hU : (Finset.univ.filter (fun z : X N × X N => decide (z.1 ∈ R ∨ z.2 ∈ S))) = T₁ ∪ T₂ := by
    ext z; simp [T₁, T₂]
  have hI : T₁ ∩ T₂ = R ×ˢ S := by ext z; simp [T₁, T₂]
  have h := Finset.card_union_add_card_inter T₁ T₂
  rw [hI] at h
  have he : (T₁ ∪ T₂).card + R.card * S.card = R.card * N + N * S.card := by
    simpa only [T₁,T₂,Finset.card_product,Finset.card_univ,Fintype.card_fin] using h
  unfold size
  rw [hU, Nat.add_mul, Nat.mul_comm S.card N]
  omega

end Loss

open scoped BigOperators
namespace Loss

def defect {N : ℕ} [NeZero N] (u : X N) : Tbl N := fun x y => decide (y-x ≠ u)

def trace {N : ℕ} [NeZero N] (C : Tbl N) (u : X N) : ℝ := ∑ x, bit (C x (x+u))

lemma defect_eq {N : ℕ} [NeZero N] (u : X N) :
    defect u = fun x y => decide ((y.val+N-x.val)%N ≠ u.val) := by
  funext x y
  unfold defect
  congr 1
  apply propext
  have hv : (y-x).val = (y.val+N-x.val)%N := by
    rw [Fin.val_sub]
    congr 1
    have hx := x.isLt
    omega
  exact not_congr ⟨fun e => hv.symm.trans (congrArg Fin.val e), fun e => Fin.ext (hv.trans e)⟩

lemma shift_defect {N t : ℕ} [NeZero N] (h : t+1 = N) (u : X N) :
    shift (cyclic t) u = defect ((⟨t, by omega⟩ : X N) - u) := by
  funext x y
  unfold shift cyclic defect
  congr 1
  have e : (y+u-x : X N) = y-x+u := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    ac_rfl
  apply propext
  have heq : y - x = (⟨t, by omega⟩ : X N) - u ↔ y-x+u = ⟨t, by omega⟩ := eq_sub_iff_add_eq
  rw [e]
  apply Iff.trans _ (not_congr heq).symm
  constructor
  · intro hl he
    have hh := congrArg Fin.val he
    change (y - x + u).val = t at hh
    omega
  · intro hne
    by_contra! hn
    apply hne
    apply Fin.ext
    change (y-x+u).val = t
    have hi := (y-x+u).isLt
    omega

lemma defect_reg {N t : ℕ} [NeZero N] (h : t+1 = N) (u : X N) : reg t (defect u) := by
  let z : X N := ⟨t, by omega⟩
  have hs := shift_reg (cyclic_reg (by omega : t ≤ N)) (z-u)
  rw [shift_defect h] at hs
  simpa only [z, sub_sub_cancel] using hs

lemma loss_defect {N t : ℕ} [NeZero N] (h : t+1 = N) (C : Tbl N) (u : X N) :
    (loss C (defect u) : ℝ) = ((N : ℝ)*t) - size C + 2 * trace C u := by
  have hi : inter C (defect u) = (size C : ℝ) - trace C u := by
    unfold inter trace
    rw [size_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have he (y : X N) : bit (defect u x y) = 1 - (if y = x+u then 1 else 0) := by
      have hh : y-x = u ↔ y = x+u := by rw [sub_eq_iff_eq_add, add_comm u x]
      by_cases hy : y = x+u <;> simp [defect, bit, hh, hy]
    simp only [he, mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [loss_eq, reg_size (defect_reg h u), hi]
  ring

lemma err_defect {N M t A : ℕ} [NeZero N] (h : t+1 = N)
    (D : Fin M → Tbl N) (w : Fin M → ℝ) (hw : ∑ i, w i = 1)
    (hA : ∀ i, size (D i) = A) (u : X N) :
    err D w (defect u) = (N:ℝ)*((N:ℝ)*t-A+2*∑ i, w i*trace (D i) u) := by
  unfold err
  simp only [loss_defect h, hA, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  congr 2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma trace_union {N : ℕ} [NeZero N] (A B : Finset (X N)) (u : X N) :
    trace (fun x y => decide (x ∈ A ∨ y ∈ B)) u =
      (A.card : ℝ) + B.card - ((Finset.univ.filter (fun x => x ∈ A ∧ x+u ∈ B)).card : ℝ) := by
  classical
  unfold trace
  have he (x : X N) : bit (decide (x ∈ A ∨ x+u ∈ B)) = bit (decide (x ∈ A)) +
      bit (decide (x+u ∈ B)) - bit (decide (x ∈ A ∧ x+u ∈ B)) := by
    by_cases ha : x ∈ A <;> by_cases hb : x+u ∈ B <;> simp [bit,ha,hb]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← card_bit, ← card_bit, ← card_bit]
  have hA : Finset.univ.filter (fun x : X N => decide (x ∈ A)) = A := by ext x; simp
  have hB : Finset.univ.filter (fun x : X N => decide (x ∈ B)) = B := by ext x; simp
  have hm : (Finset.univ.filter (fun x : X N => decide (x+u ∈ B))).card = B.card :=
    (card_perm (Equiv.addRight u) (fun x => decide (x ∈ B))).trans (congrArg Finset.card hB)
  rw [hA, hm]
  simp

lemma support_cyclic {N M g r s t : ℕ} [NeZero N] (ht : t+1 = N)
    (hgs : r+s = g+1) (hrs : 0 < r*s) (hN : r*s < N)
    (D : Fin M → Tbl N) (w : Fin M → ℝ) (hw : ∑ i, w i = 1)
    (hA : ∀ i, size (D i) = (g+1)*N-r*s)
    (A B : Fin M → Finset (X N)) (hD : ∀ i x y, D i x y = decide (x ∈ A i ∨ y ∈ B i))
    (hsize : ∀ i, (A i).card + (B i).card = r+s ∧ (A i).card*(B i).card = r*s)
    (hgood : ∀ u, err D w (defect u) ≤ benchR N t ((g+1)*N-r*s)) : N ≤ M*(r*s) := by
  classical
  let H (i : Fin M) := ((A i) ×ˢ (B i)).image (fun z => z.2-z.1)
  have hcover : (Finset.univ : Finset (X N)) ⊆ Finset.univ.biUnion H := by
    intro u _
    by_contra hu
    have htr (i : Fin M) : trace (D i) u = ((r:ℝ)+s) := by
      have hnone (x : X N) : ¬(x ∈ A i ∧ x+u ∈ B i) := fun hx => hu (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨(x,x+u), Finset.mem_product.mpr hx, add_sub_cancel_left x u⟩⟩)
      have he : D i = fun x y => decide (x ∈ A i ∨ y ∈ B i) := funext fun x => funext fun y => hD i x y
      rw [he, trace_union]
      simp only [hnone, Finset.filter_false, Finset.card_empty, Nat.cast_zero, sub_zero]
      exact_mod_cast (hsize i).1
    have hbad := hgood u
    rw [err_defect ht D w hw hA, benchR] at hbad
    simp_rw [htr] at hbad
    rw [← Finset.sum_mul, hw, one_mul] at hbad
    have hPos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hh : (r:ℝ)*s < N := by exact_mod_cast hN
    have hp : (0:ℝ) < (r:ℝ)*s := by exact_mod_cast hrs
    have hcast : (((g+1)*N-r*s : ℕ) : ℝ) = ((g:ℝ)+1)*N-(r:ℝ)*s := by
      rw [Nat.cast_sub (hN.le.trans (by nlinarith : N ≤ (g+1)*N))]
      push_cast; rfl
    rw [hcast] at hbad
    have hts : (t:ℝ)+1=N := by exact_mod_cast ht
    have hgs' : (r:ℝ)+s=(g:ℝ)+1 := by exact_mod_cast hgs
    have hb' : (0:ℝ) < 2*((r:ℝ)*s) := by linarith
    have ht' : (t:ℝ) = N-1 := by linarith only [hts]
    rw [ht', hgs'] at hbad
    ring_nf at hbad
    linarith only [hbad, hb']
  calc
    N = (Finset.univ : Finset (X N)).card := by simp
    _ ≤ (Finset.univ.biUnion H).card := Finset.card_le_card hcover
    _ ≤ ∑ i, (H i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin M, r*s := Finset.sum_le_sum fun i _ =>
      Finset.card_image_le.trans_eq ((Finset.card_product _ _).trans (hsize i).2)
    _ = _ := by simp

end Loss

namespace Shape

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

section Definitions

def tab {N : ℕ} (C : Circuit) (x y : Fin N) : Bool :=
  C.eval (PEqualNP.Represents.oneEach x y)

def accept {N : ℕ} (C : Circuit) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun z => tab C z.1 z.2

def Fits (N g r s : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N + N) C ∧ C.output < N + N + C.size ∧
    (∀ G ∈ C.gates, G.inputs.length ≤ 2 ∧
      (G.op = .or ∨ G.op = .and ∨ (G.op = .not ∧ G.inputs.length = 1))) ∧
    C.size ≤ g ∧ (accept (N := N) C).card ≤ (g + 1) * N - r * s

private def operands (n : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  (gateAt C (w - n)).inputs

private def prune (n : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  match (gateAt C (w - n)).op with
  | .and => (operands n C w).take 1
  | _ => operands n C w

private def Back (n k : ℕ) (F : ℕ → List ℕ) : Prop :=
  ∀ w, n ≤ w → w < n + k → ∀ u ∈ F w, u < w

private def Step (n k : ℕ) (F : ℕ → List ℕ) (w u : ℕ) : Prop :=
  n ≤ w ∧ w < n + k ∧ u ∈ F w

private abbrev Reach (n k : ℕ) (F : ℕ → List ℕ) :=
  Relation.ReflTransGen (Step n k F)

private noncomputable def cone (n k : ℕ) (F : ℕ → List ℕ) (o : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + k)).filter (Reach n k F o)

private def leaves (n : ℕ) (W : Finset ℕ) : Finset ℕ := W.filter (· < n)
private def internal (n : ℕ) (W : Finset ℕ) : Finset ℕ := W.filter (n ≤ ·)

private def slots (F : ℕ → List ℕ) (B : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  B.sigma fun w => Finset.range (F w).length

private def target (F : ℕ → List ℕ) (p : Σ _ : ℕ, ℕ) : ℕ := (F p.1).getD p.2 0

private def inp (n : ℕ) (P : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin n => decide (i.val ∈ P)

private abbrev value (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

private def rows (N : ℕ) (L : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun x => x.val ∈ L)

private def cols (N : ℕ) (L : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun y => N + y.val ∈ L)

private def cross {N : ℕ} (R S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun z => z.1 ∈ R ∨ z.2 ∈ S)

end Definitions

section ConeCount

variable {n k o : ℕ} {F : ℕ → List ℕ}

private theorem mem_cone {w : ℕ} :
    w ∈ cone n k F o ↔ w < n + k ∧ Reach n k F o w := by
  classical
  simp [cone]

private theorem mem_leaves {w : ℕ} :
    w ∈ leaves n (cone n k F o) ↔ w < n ∧ Reach n k F o w := by
  rw [leaves, Finset.mem_filter, mem_cone]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨by omega, h.2⟩, h.1⟩⟩

private theorem reach_le (hb : Back n k F) {w u : ℕ} (h : Reach n k F w u) : u ≤ w := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (hb _ hstep.1 hstep.2.1 _ hstep.2.2).le.trans ih

private theorem reach_mono {F' : ℕ → List ℕ}
    (hsub : ∀ w u, u ∈ F' w → u ∈ F w) {w u : ℕ} :
    Reach n k F' w u → Reach n k F w u := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail ⟨hstep.1, hstep.2.1, hsub _ _ hstep.2.2⟩

private theorem target_image (hb : Back n k F) :
    (slots F (internal n (cone n k F o))).image (target F) = (cone n k F o).erase o := by
  ext u
  constructor
  · rintro hu
    obtain ⟨⟨w, j⟩, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hw, hj⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hW, hn⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwk, hr⟩ := mem_cone.mp hW
    have hj' : j < (F w).length := Finset.mem_range.mp hj
    have hm : target F ⟨w, j⟩ ∈ F w := by
      simp [target, hj']
    have hlt := hb w hn hwk _ hm
    exact Finset.mem_erase.mpr ⟨ne_of_lt (hlt.trans_le (reach_le hb hr)),
      mem_cone.mpr ⟨hlt.trans hwk, hr.tail ⟨hn, hwk, hm⟩⟩⟩
  · intro hu
    obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
    have hr := (mem_cone.mp hu).2
    cases hr with
    | refl => exact (hne rfl).elim
    | @tail w _ hr hs =>
      obtain ⟨hn, hwk, hm⟩ := hs
      obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hm
      refine Finset.mem_image.mpr ⟨⟨w, j⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨mem_cone.mpr ⟨hwk, hr⟩, hn⟩, Finset.mem_range.mpr hj⟩, ?_⟩
      simpa [target, hj] using hju

private theorem internal_subset : internal n (cone n k F o) ⊆ Finset.Ico n (n + k) := by
  intro w hw
  obtain ⟨hw, hn⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_Ico.mpr ⟨hn, (mem_cone.mp hw).1⟩

private theorem cone_count (ho : o < n + k) (hb : Back n k F)
    (h₂ : ∀ w ∈ internal n (cone n k F o), (F w).length ≤ 2) :
    let W := cone n k F o
    let B := internal n W
    let L := leaves n W
    L.card ≤ B.card + 1 ∧ B.card ≤ k ∧
    (L.card = k + 1 → B = Finset.Ico n (n + k) ∧
      (∀ w ∈ B, (F w).length = 2) ∧ Set.InjOn (target F) (slots F B)) := by
  intro W B L
  have hW : o ∈ W := mem_cone.mpr ⟨ho, .refl⟩
  have hpart : L.card + B.card = W.card := by
    simpa [L, B, leaves, internal, not_lt] using W.card_filter_add_card_filter_not (· < n)
  have herase : (W.erase o).card + 1 = W.card := Finset.card_erase_add_one hW
  have himg : (slots F B).image (target F) = W.erase o := target_image hb
  have hmin : (W.erase o).card ≤ (slots F B).card := by
    rw [← himg]; exact Finset.card_image_le
  have hslots : (slots F B).card = ∑ w ∈ B, (F w).length := by simp [slots]
  have hmax : (slots F B).card ≤ B.card * 2 := by
    rw [hslots, ← Finset.sum_const_nat (s := B) (fun _ _ => rfl : ∀ w ∈ B, (2 : ℕ) = 2)]
    exact Finset.sum_le_sum h₂
  have hB : B.card ≤ k := by
    simpa using Finset.card_le_card (internal_subset (n := n) (k := k) (F := F) (o := o))
  refine ⟨by omega, hB, fun hL => ⟨?_, ?_, ?_⟩⟩
  · exact Finset.eq_of_subset_of_card_le internal_subset (by simp; omega)
  · intro w hw
    by_contra hne
    have hlt : (F w).length < 2 := lt_of_le_of_ne (h₂ w hw) hne
    have hsum : (∑ v ∈ B, (F v).length) < ∑ _v ∈ B, (2 : ℕ) :=
      Finset.sum_lt_sum h₂ ⟨w, hw, hlt⟩
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
    omega
  · apply Finset.card_image_iff.mp
    rw [himg]
    omega

end ConeCount

section CircuitSemantics

variable {n : ℕ} {C : Circuit}

private theorem gate_eq {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

private theorem op_back (hb : ReadsBack n C) : Back n C.size (operands n C) := by
  intro w hn hw u hu
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  have hh := hb (w - n) hj u hu
  omega

private theorem prune_sub (w u : ℕ) : u ∈ prune n C w → u ∈ operands n C w := by
  unfold prune
  split <;> rename_i h
  · exact List.mem_of_mem_take
  · exact id

private theorem fold_prefix {α β : Type*} (f : List α → β → α) (gs : List β) (x : List α) :
    x <+: gs.foldl (fun v g => v ++ [f v g]) x := by
  induction gs generalizing x with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append x [f x g]).trans (ih _)

private theorem fold_length {α β : Type*} (f : List α → β → α) (gs : List β) (x : List α) :
    (gs.foldl (fun v g => v ++ [f v g]) x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

private theorem prefix_getD {α : Type*} {x y : List α} (h : x <+: y) {i : ℕ}
    (hi : i < x.length) (d : α) : y.getD i d = x.getD i d := by
  obtain ⟨t, ht⟩ := h
  rw [← ht]
  simp [List.getElem?_append_left hi]

private theorem value_input {x : List Bool} (hx : x.length = n) {w : ℕ} (hw : w < n) :
    value C x w = x.getD w false := by
  exact prefix_getD (fold_prefix (fun v (G : Gate) => G.op.eval (G.inputs.map fun i => v.getD i false))
    C.gates x) (hx.symm ▸ hw) false

private theorem value_gate {x : List Bool} (hx : x.length = n) (hb : ReadsBack n C)
    {w : ℕ} (hn : n ≤ w) (hw : w < n + C.size) :
    value C x w = (gateAt C (w - n)).op.eval ((operands n C w).map (value C x)) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let f := fun (v : List Bool) (G : Gate) => G.op.eval (G.inputs.map fun i => v.getD i false)
  let P := (C.gates.take j).foldl (fun v G => v ++ [f v G]) x
  have hlen : P.length = w := by
    rw [fold_length, hx, List.length_take, min_eq_left hj.le]
    dsimp [j]; omega
  have hpre : P ++ [f P C.gates[j]] <+: C.wires x := by
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by simp
    unfold Circuit.wires
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact fold_prefix f _ _
  have hP : P <+: C.wires x := (List.prefix_append P _).trans hpre
  have hval : value C x w = f P C.gates[j] := by
    change (C.wires x).getD w false = _
    rw [prefix_getD hpre (i := w) (by simp [hlen]) false]
    simpa only [hlen] using
      (show (P ++ [f P C.gates[j]]).getD P.length false = f P C.gates[j] by simp)
  rw [hval, operands, gate_eq hj]
  change C.gates[j].op.eval (C.gates[j].inputs.map (fun i => P.getD i false)) = _
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < P.length := by
    have h := hb j hj i (by rwa [gate_eq hj])
    rw [hlen]; dsimp [j] at h; omega
  exact (prefix_getD hP hi' false).symm

private theorem inp_length (P : Finset ℕ) : (inp n P).length = n := by simp [inp]

private theorem inp_bit (P : Finset ℕ) {w : ℕ} (hw : w < n) :
    (inp n P).getD w false = decide (w ∈ P) := by simp [inp, hw]

private theorem pair_input {N : ℕ} (x y : Fin N) :
    PEqualNP.Represents.oneEach x y = inp (N + N) {x.val, N + y.val} := by
  have hx := x.isLt
  have hy := y.isLt
  apply List.ext_getElem
  · simp [PEqualNP.Represents.oneEach, inp]
  · intro i h₁ h₂
    simp only [PEqualNP.Represents.oneEach, inp, List.length_append, List.length_ofFn] at h₁ h₂ ⊢
    by_cases hi : i < N
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

private theorem eval_agree (hb : ReadsBack n C) (ho : C.output < n + C.size)
    {P Q : Finset ℕ}
    (h : ∀ w ∈ leaves n (cone n C.size (operands n C) C.output), w ∈ P ↔ w ∈ Q) :
    C.eval (inp n P) = C.eval (inp n Q) := by
  suffices aux : ∀ w, Reach n C.size (operands n C) C.output w →
      value C (inp n P) w = value C (inp n Q) w from aux _ .refl
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr
    by_cases hn : w < n
    · rw [value_input (inp_length _) hn, value_input (inp_length _) hn,
        inp_bit _ hn, inp_bit _ hn, decide_eq_decide]
      exact h w (mem_leaves.mpr ⟨hn, hr⟩)
    · have hw := (reach_le (op_back hb) hr).trans_lt ho
      rw [value_gate (inp_length _) hb (Nat.le_of_not_gt hn) hw,
        value_gate (inp_length _) hb (Nat.le_of_not_gt hn) hw]
      congr 1
      apply List.map_congr_left
      intro u hu
      exact ih u (op_back hb w (Nat.le_of_not_gt hn) hw u hu)
        (hr.tail ⟨Nat.le_of_not_gt hn, hw, hu⟩)

private theorem pruned_witness (hb : ReadsBack n C) (ho : C.output < n + C.size)
    (ht : ∀ w ∈ internal n (cone n C.size (operands n C) C.output),
      (operands n C w).length = 2 ∧
        ((gateAt C (w - n)).op = .or ∨ (gateAt C (w - n)).op = .and))
    {P : Finset ℕ} (hP : C.eval (inp n P) = true) :
    ∃ u ∈ leaves n (cone n C.size (prune n C) C.output), u ∈ P := by
  have aux : ∀ w, Reach n C.size (prune n C) C.output w →
      value C (inp n P) w = true → ∃ u < n, Reach n C.size (prune n C) C.output u ∧ u ∈ P := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hr hv
      by_cases hn : w < n
      · refine ⟨w, hn, hr, ?_⟩
        rwa [value_input (inp_length _) hn, inp_bit _ hn, decide_eq_true_eq] at hv
      · have hn' := Nat.le_of_not_gt hn
        have hr' : Reach n C.size (operands n C) C.output w := reach_mono prune_sub hr
        have hw := (reach_le (op_back hb) hr').trans_lt ho
        obtain ⟨hlen, hop⟩ := ht w (Finset.mem_filter.mpr ⟨mem_cone.mpr ⟨hw, hr'⟩, hn'⟩)
        rw [value_gate (inp_length _) hb hn' hw] at hv
        have child : ∃ u ∈ prune n C w, value C (inp n P) u = true := by
          rcases hop with hor | hand
          · rw [hor] at hv
            simpa [prune, hor, GateOp.eval, List.any_eq_true] using hv
          · rw [hand] at hv
            generalize hl : operands n C w = l at hv hlen
            cases l with
            | nil => simp at hlen
            | cons u l =>
              refine ⟨u, by simp [prune, hand, hl], ?_⟩
              exact (Bool.and_eq_true_iff.mp hv).1
        obtain ⟨u, hu, hval⟩ := child
        exact ih u (op_back hb w hn' hw u (prune_sub _ _ hu))
          (hr.tail ⟨hn', hw, hu⟩) hval
  obtain ⟨u, hu, hr, hp⟩ := aux _ .refl hP
  exact ⟨u, mem_leaves.mpr ⟨hu, hr⟩, hp⟩

private theorem eval_of_or_leaf (hb : ReadsBack n C)
    (hor : ∀ w ∈ internal n (cone n C.size (operands n C) C.output),
      (gateAt C (w - n)).op = .or)
    {P : Finset ℕ} {u : ℕ} (hu : u ∈ leaves n (cone n C.size (operands n C) C.output))
    (hp : u ∈ P) : C.eval (inp n P) = true := by
  by_contra hn
  have hfalse : C.eval (inp n P) = false := Bool.eq_false_of_not_eq_true hn
  obtain ⟨hun, hur⟩ := mem_leaves.mp hu
  have aux : ∀ w, Reach n C.size (operands n C) C.output w → value C (inp n P) w = false := by
    intro w hr
    induction hr with
    | refl => exact hfalse
    | @tail w u hr hs ih =>
      obtain ⟨hwn, hw, hum⟩ := hs
      have h := hor w (Finset.mem_filter.mpr ⟨mem_cone.mpr ⟨hw, hr⟩, hwn⟩)
      rw [value_gate (inp_length _) hb hwn hw, h] at ih
      cases he : value C (inp n P) u with
      | false => rfl
      | true =>
        have hc : (GateOp.or.eval ((operands n C w).map (value C (inp n P)))) = true := by
          simpa [GateOp.eval, List.any_eq_true] using
            (show ∃ v ∈ operands n C w, value C (inp n P) v = true from ⟨u, hum, he⟩)
        rw [hc] at ih
        contradiction
  have hv := aux u hur
  rw [value_input (inp_length _) hun, inp_bit _ hun, decide_eq_true hp] at hv
  contradiction

end CircuitSemantics

section TableCounts

private theorem partition_inputs {N : ℕ} {L : Finset ℕ} (hL : ∀ u ∈ L, u < N + N) :
    (rows N L).card + (cols N L).card = L.card := by
  let f : Fin N → ℕ := Fin.val
  let h : Fin N → ℕ := fun y => N + y.val
  have hf : Function.Injective f := fun _ _ hxy => Fin.ext hxy
  have hh : Function.Injective h := by intro a b hab; apply Fin.ext; dsimp [h] at hab; omega
  have hd : Disjoint ((rows N L).image f) ((cols N L).image h) := by
    rw [Finset.disjoint_left]
    intro u hu hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hv
    have hx := x.isLt
    dsimp [f, h] at hy; omega
  have he : (rows N L).image f ∪ (cols N L).image h = L := by
    ext u
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        exact (Finset.mem_filter.mp hx).2
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
        exact (Finset.mem_filter.mp hy).2
    · intro hu
      by_cases hn : u < N
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨u, hn⟩, by simp [rows, hu], rfl⟩)
      · have hu' := hL u hu
        have heq : N + (u - N) = u := by omega
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨u - N, by omega⟩, by simp [cols, heq, hu], heq⟩)
  calc
    _ = ((rows N L).image f).card + ((cols N L).image h).card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ hh]
    _ = L.card := by rw [← Finset.card_union_of_disjoint hd, he]

private theorem cross_compl {N : ℕ} (R S : Finset (Fin N)) : (cross R S)ᶜ = Rᶜ ×ˢ Sᶜ := by
  ext z
  simp [cross, not_or]

private theorem rectangle_card {N : ℕ} (R S : Finset (Fin N)) :
    ((cross R S)ᶜ).card = (N - R.card) * (N - S.card) := by
  simp [cross_compl, Finset.card_compl]

private theorem cross_count {N : ℕ} (R S : Finset (Fin N)) :
    (cross R S).card + R.card * S.card = (R.card + S.card) * N := by
  have hpart : (cross R S).card + ((cross R S)ᶜ).card = N * N := by
    simp [Finset.card_add_card_compl]
  rw [rectangle_card] at hpart
  have hR : R.card ≤ N := by simpa using R.card_le_univ
  have hS : S.card ≤ N := by simpa using S.card_le_univ
  have h₁ := congrArg (fun x : ℕ => x * (N - S.card)) (Nat.sub_add_cancel hR)
  have h₂ := congrArg (fun x : ℕ => R.card * x) (Nat.sub_add_cancel hS)
  have h₃ := congrArg (fun x : ℕ => N * x) (Nat.sub_add_cancel hS)
  nlinarith only [hpart, h₁, h₂, h₃]

private theorem product_sizes {a b r s : ℕ} (hs : a + b = r + s) (hp : a * b = r * s) :
    (a = r ∧ b = s) ∨ (a = s ∧ b = r) := by
  have hs' : (a : ℤ) + b = r + s := by exact_mod_cast hs
  have hp' : (a : ℤ) * b = r * s := by exact_mod_cast hp
  have h : ((a : ℤ) - r) * ((a : ℤ) - s) = 0 := by
    nlinarith only [hp', congrArg (fun x : ℤ => (a : ℤ) * x) hs']
  rcases mul_eq_zero.mp h with h | h
  · have h' : a = r := by exact_mod_cast (sub_eq_zero.mp h)
    exact Or.inl ⟨h', by omega⟩
  · have h' : a = s := by exact_mod_cast (sub_eq_zero.mp h)
    exact Or.inr ⟨h', by omega⟩

end TableCounts

theorem saturated_shape {N g r s : ℕ} {C : Circuit}
    (hr : 0 < r) (hrs : r ≤ s) (hsum : r + s = g + 1) (hprod : r * s < N)
    (hN : 2 * g + 1 < N) (hfit : Fits N g r s C)
    (hA : (accept (N := N) C).card = (g + 1) * N - r * s) :
    ∃ (swap : Bool) (R S : Finset (Fin N)), R.card = r ∧ S.card = s ∧
      ∀ x y : Fin N, (if swap then tab C y x else tab C x y) = decide (x ∈ R ∨ y ∈ S) := by
  obtain ⟨hb, ho, hgates, hk, hcap⟩ := hfit
  let n := N + N
  let F := operands n C
  let W := cone n C.size F C.output
  let B := internal n W
  let L := leaves n W
  let R := rows N L
  let S := cols N L
  have hLt : ∀ u ∈ L, u < N + N := fun _ hu => (mem_leaves.mp hu).1
  have hRS : R.card + S.card = L.card := partition_inputs hLt
  have h₂ : ∀ w ∈ B, (F w).length ≤ 2 := by
    intro w hw
    obtain ⟨hw', hwn⟩ := Finset.mem_filter.mp hw
    have hwk : w < n + C.size := (mem_cone.mp hw').1
    have hj : w - n < C.gates.length := by unfold Circuit.size at hwk; omega
    simpa [F, operands, gate_eq hj] using (hgates _ (List.getElem_mem hj)).1
  obtain ⟨hLB, hBk, hsat⟩ := cone_count ho (op_back hb) h₂
  change L.card ≤ B.card + 1 at hLB
  change B.card ≤ C.size at hBk
  have hLmax : L.card ≤ g + 1 := by omega
  have hgt : g * N < (accept (N := N) C).card := by rw [hA, Nat.add_mul, one_mul]; omega
  have hpos : 0 < r * s := Nat.mul_pos hr (hr.trans_le hrs)
  have hcap' : (accept (N := N) C).card < (g + 1) * N :=
    hcap.trans_lt (Nat.sub_lt (Nat.mul_pos (by omega) (by omega)) hpos)
  have same : ∀ {P Q : Finset ℕ}, (∀ u ∈ L, u ∈ P ↔ u ∈ Q) →
      C.eval (inp n P) = C.eval (inp n Q) := fun h => eval_agree hb ho h
  have hzero : C.eval (inp n ∅) = false := by
    by_contra hn
    have ht : C.eval (inp n ∅) = true := Bool.eq_true_of_not_eq_false hn
    have hrect : (cross R S)ᶜ ⊆ accept (N := N) C := by
      intro ⟨x, y⟩ hp
      have hout : x.val ∉ L ∧ N + y.val ∉ L := by simpa [cross, R, S, rows, cols, not_or] using hp
      have he : C.eval (inp n {x.val, N + y.val}) = C.eval (inp n ∅) := by
        apply same
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro (rfl | rfl) <;> tauto
      simp [accept, tab, pair_input, n, he, ht]
    have hcard := Finset.card_le_card hrect
    have hpart : (cross R S).card + ((cross R S)ᶜ).card = N * N := by
      simp [Finset.card_add_card_compl]
    have hcross := cross_count R S
    have hm := Nat.mul_le_mul_right N (show R.card + S.card ≤ g + 1 by omega)
    have hn' := Nat.mul_le_mul_right N (show (g + 1) + (g + 1) ≤ N by omega)
    rw [Nat.add_mul] at hn'
    omega
  have heval {x y : Fin N} : tab C x y = C.eval (inp n {x.val, N + y.val}) := by
    rw [tab, pair_input]
  have hit {x y : Fin N} (hxy : tab C x y = true) : x.val ∈ L ∨ N + y.val ∈ L := by
    by_contra! hout
    rw [heval, same (Q := ∅) (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro (rfl | rfl) <;> tauto), hzero] at hxy
    contradiction
  have hcover : accept (N := N) C ⊆ cross R S := by
    intro z hz
    simpa [accept, cross, R, S, rows, cols] using
      (hit (x := z.1) (y := z.2) (Finset.mem_filter.mp hz).2)
  obtain hLcard : L.card = g + 1 := by
    have hcard := Finset.card_le_card hcover
    have hc := cross_count R S
    by_contra hne
    have hm := Nat.mul_le_mul_right N (show R.card + S.card ≤ g by omega)
    omega
  have hsingle : ∀ w ∈ L, C.eval (inp n {w}) = true := by
    intro w hw
    by_contra hbad
    have hfalse : C.eval (inp n {w}) = false := Bool.eq_false_of_not_eq_true hbad
    let L' := L.erase w
    let R' := rows N L'
    let S' := cols N L'
    have hcov' : accept (N := N) C ⊆ cross R' S' := by
      intro ⟨x, y⟩ hxy
      have ht : tab C x y = true := (Finset.mem_filter.mp hxy).2
      by_contra hcross
      have hn' : x.val ∉ L' ∧ N + y.val ∉ L' := by
        simpa [cross, R', S', rows, cols, not_or] using hcross
      have hm : x.val = w ∨ N + y.val = w := by
        rcases hit ht with hx | hy
        · exact Or.inl (by simpa [L', hx] using hn'.1)
        · exact Or.inr (by simpa [L', hy] using hn'.2)
      have he : C.eval (inp n {x.val, N + y.val}) = C.eval (inp n {w}) := by
        apply same
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl)
          · simpa [L', hu] using hn'.1
          · simpa [L', hu] using hn'.2
        · rintro rfl; exact hm.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ Eq.symm)
      rw [heval, he, hfalse] at ht
      contradiction
    have hcard := Finset.card_le_card hcov'
    have hRS' : R'.card + S'.card = L'.card := partition_inputs
      (fun u hu => hLt u (Finset.mem_erase.mp hu).2)
    have hL' : L'.card + 1 = L.card := Finset.card_erase_add_one hw
    have hc := cross_count R' S'
    have hm := Nat.mul_le_mul_right N (show R'.card + S'.card ≤ g by omega)
    omega
  have hk' : C.size = g := by omega
  obtain ⟨hB, hbin, _⟩ := hsat (hLcard.trans (congrArg (· + 1) hk'.symm))
  have hmono : ∀ w ∈ B, (F w).length = 2 ∧
      ((gateAt C (w - n)).op = .or ∨ (gateAt C (w - n)).op = .and) := by
    intro w hw
    have hn := (Finset.mem_filter.mp hw).2
    have hwk := (mem_cone.mp (Finset.mem_filter.mp hw).1).1
    have hj : w - n < C.gates.length := by unfold Circuit.size at hwk; omega
    have hop := (hgates _ (List.getElem_mem hj)).2
    rw [← gate_eq hj] at hop
    refine ⟨hbin w hw, ?_⟩
    rcases hop with hor | hand | hnot
    · exact Or.inl hor
    · exact Or.inr hand
    · have hlen : (F w).length = 2 := hbin w hw
      have hlen' : (F w).length = 1 := hnot.2
      omega
  let F' := prune n C
  let W' := cone n C.size F' C.output
  let B' := internal n W'
  let L' := leaves n W'
  have hback' : Back n C.size F' := fun w hw hk u hu => op_back hb w hw hk u (prune_sub w u hu)
  have hBsub : B' ⊆ B := by
    intro w hw
    obtain ⟨hw, hn⟩ := Finset.mem_filter.mp hw
    obtain ⟨hk, hr⟩ := mem_cone.mp hw
    exact Finset.mem_filter.mpr ⟨mem_cone.mpr ⟨hk, reach_mono prune_sub hr⟩, hn⟩
  have h₂' : ∀ w ∈ B', (F' w).length ≤ 2 := by
    intro w hw
    have hf := hbin w (hBsub hw)
    unfold F' prune
    split
    · simp [show (operands n C w).length = 2 from hf]
    · exact hf.le
  obtain ⟨hcount', hbound', hsat'⟩ := cone_count ho hback' h₂'
  change L'.card ≤ B'.card + 1 at hcount'
  change B'.card ≤ C.size at hbound'
  have hLsub : L ⊆ L' := by
    intro w hw
    obtain ⟨u, hu, hm⟩ := pruned_witness hb ho hmono (hsingle w hw)
    rwa [Finset.mem_singleton.mp hm] at hu
  have hLcard' : L'.card = C.size + 1 := by
    have hle := Finset.card_le_card hLsub
    omega
  obtain ⟨hB', hbin', _⟩ := hsat' hLcard'
  have hor : ∀ w ∈ B, (gateAt C (w - n)).op = .or := by
    intro w hw
    rcases (hmono w hw).2 with hor | hand
    · exact hor
    · have hw' : w ∈ B' := by
        change B' = Finset.Ico n (n + C.size) at hB'
        change B = Finset.Ico n (n + C.size) at hB
        rwa [hB', ← hB]
      have hlen : (F' w).length = 2 := hbin' w hw'
      simp [F', prune, hand, show (operands n C w).length = 2 from hbin w hw] at hlen
  have htab : ∀ x y : Fin N, tab C x y = decide (x ∈ R ∨ y ∈ S) := by
    intro x y
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      simpa [R, S, rows, cols] using hit h
    · intro h
      have hh : x.val ∈ L ∨ N + y.val ∈ L := by simpa [R, S, rows, cols] using h
      rw [heval]
      rcases hh with hx | hy
      · exact eval_of_or_leaf hb hor hx (by simp)
      · exact eval_of_or_leaf hb hor hy (by simp)
  have hcrossEq : accept (N := N) C = cross R S := by
    ext ⟨x, y⟩
    simp [accept, cross, htab]
  have hcard := cross_count R S
  rw [← hcrossEq, hA, hRS, hLcard] at hcard
  have hpr : r * s ≤ (g + 1) * N := by
    exact hprod.le.trans (by simpa using Nat.mul_le_mul_right N (show 1 ≤ g + 1 by omega))
  have hmul : R.card * S.card = r * s := by omega
  rcases product_sizes (hRS.trans (hLcard.trans hsum.symm)) hmul with h | h
  · exact ⟨false, R, S, h.1, h.2, htab⟩
  · refine ⟨true, S, R, h.2, h.1, fun x y => ?_⟩
    simpa [or_comm] using htab y x

end Shape

open scoped BigOperators

namespace Rect

variable {N M r s : ℕ}

noncomputable def weightedIntersection (A B : Fin M → Finset (Fin N)) (w : Fin M → ℝ)
    (x y : Fin N) : ℝ :=
  ∑ i, if x ∈ A i ∧ y ∈ B i then w i else 0

def Additive (F : Fin N → Fin N → ℝ) : Prop :=
  ∀ x x' y y', F x y + F x' y' = F x y' + F x' y

def Block (r s : ℕ) (A B : Fin M → Finset (Fin N)) : Prop :=
  ∃ (swap : Bool) (R : Finset (Fin N)) (S : Fin M → Finset (Fin N)),
    R.card = r ∧ (∀ i, (S i).card = s) ∧ (∀ y, ∃! i, y ∈ S i) ∧
    ∀ i, (if swap then B i else A i) = R ∧ (if swap then A i else B i) = S i

variable {A B : Fin M → Finset (Fin N)} {w : Fin M → ℝ}

private lemma index_nonempty (hsum : ∑ i, w i = 1) : Nonempty (Fin M) := by
  classical
  by_contra hn
  letI : IsEmpty (Fin M) := ⟨fun i => hn ⟨i⟩⟩
  simpa using hsum

private lemma transpose_value (A B : Fin M → Finset (Fin N)) (w : Fin M → ℝ)
    (x y : Fin N) : weightedIntersection B A w x y = weightedIntersection A B w y x := by
  unfold weightedIntersection
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hx : x ∈ B i <;> by_cases hy : y ∈ A i <;> simp [hx, hy]

private lemma additive_transpose (h : Additive (weightedIntersection A B w)) :
    Additive (weightedIntersection B A w) := by
  intro x x' y y'
  simp only [transpose_value A B w]
  rw [add_comm (weightedIntersection A B w y' x) (weightedIntersection A B w y x')]
  exact h y y' x x'

private lemma cover_one_axis (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hadd : Additive (weightedIntersection A B w)) :
    (∀ x, ∃ i, x ∈ A i) ∨ (∀ y, ∃ i, y ∈ B i) := by
  classical
  by_cases hAcov : ∀ x, ∃ i, x ∈ A i
  · exact Or.inl hAcov
  right
  by_contra hBcov
  push Not at hAcov hBcov
  obtain ⟨x₀, hx₀⟩ := hAcov
  obtain ⟨y₀, hy₀⟩ := hBcov
  have hrow (y : Fin N) : weightedIntersection A B w x₀ y = 0 := by
    simp [weightedIntersection, hx₀]
  have hcol (x : Fin N) : weightedIntersection A B w x y₀ = 0 := by
    simp [weightedIntersection, hy₀]
  obtain ⟨i⟩ := index_nonempty hsum
  obtain ⟨x, hx⟩ := hA i
  obtain ⟨y, hy⟩ := hB i
  have hzero : weightedIntersection A B w x y = 0 := by
    simpa only [hrow, hcol, add_zero] using hadd x x₀ y y₀
  have hpos : 0 < weightedIntersection A B w x y := by
    unfold weightedIntersection
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact (hw j).le
      · exact le_rfl
    · simp [hx, hy, hw i]
  exact hpos.ne' hzero

private lemma cover_count (S : Fin M → Finset (Fin N)) (hcov : ∀ y, ∃ i, y ∈ S i) :
    (N ≤ ∑ i, (S i).card) ∧ ((∑ i, (S i).card) = N → ∀ y, ∃! i, y ∈ S i) := by
  classical
  let T := (Finset.univ : Finset (Fin M)).sigma S
  let p : (Σ _ : Fin M, Fin N) → Fin N := fun a => a.2
  have hmem (i : Fin M) (y : Fin N) (hy : y ∈ S i) :
      (⟨i, y⟩ : Σ _ : Fin M, Fin N) ∈ T :=
    Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hy⟩
  have himage : T.image p = Finset.univ := by
    ext y
    constructor
    · exact fun _ => Finset.mem_univ _
    · intro _
      obtain ⟨i, hy⟩ := hcov y
      exact Finset.mem_image.mpr ⟨⟨i, y⟩, hmem i y hy, rfl⟩
  have ht : T.card = ∑ i, (S i).card := Finset.card_sigma _ _
  have hi : (T.image p).card = N := by rw [himage]; simp
  refine ⟨hi.symm.le.trans (Finset.card_image_le.trans ht.le), ?_⟩
  intro heq y
  have hinj : Set.InjOn p (↑T : Set (Σ _ : Fin M, Fin N)) :=
    Finset.card_image_iff.mp (hi.trans (ht.trans heq).symm)
  obtain ⟨i, hy⟩ := hcov y
  refine ⟨i, hy, fun j hj => ?_⟩
  have hp : (⟨j, y⟩ : Σ _ : Fin M, Fin N) = ⟨i, y⟩ :=
    hinj (hmem j y hj) (hmem i y hy) rfl
  exact congrArg (fun a : Σ _ : Fin M, Fin N => a.1) hp

private lemma sum_card_le (S : Fin M → Finset (Fin N)) (hle : ∀ i, (S i).card ≤ s) :
    (∑ i, (S i).card) ≤ M * s := by
  calc
    (∑ i, (S i).card) ≤ ∑ _ : Fin M, s := Finset.sum_le_sum (fun i _ => hle i)
    _ = M * s := by simp

private lemma tight_cover (S : Fin M → Finset (Fin N)) (hle : ∀ i, (S i).card ≤ s)
    (hcov : ∀ y, ∃ i, y ∈ S i) (hN : M * s = N) :
    (∀ i, (S i).card = s) ∧ (∀ y, ∃! i, y ∈ S i) := by
  obtain ⟨hlo, hpart⟩ := cover_count S hcov
  have ht : (∑ i, (S i).card) = N := le_antisymm ((sum_card_le S hle).trans hN.le) hlo
  refine ⟨fun i => ?_, hpart ht⟩
  by_contra hne
  have hlt : (∑ j, (S j).card) < ∑ _ : Fin M, s :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hle i) hne⟩
  have hconst : (∑ _ : Fin M, s) = N := by simpa using hN
  rw [ht, hconst] at hlt
  exact (lt_irrefl N) hlt

private lemma at_column (hpart : ∀ y, ∃! i, y ∈ B i) {i : Fin M} {y : Fin N}
    (hy : y ∈ B i) (x : Fin N) :
    weightedIntersection A B w x y = if x ∈ A i then w i else 0 := by
  classical
  obtain ⟨j, _, huniq⟩ := hpart y
  unfold weightedIntersection
  rw [Finset.sum_eq_single i]
  · simp [hy]
  · intro k _ hki
    have hk : y ∉ B k := fun hk => hki ((huniq k hk).trans (huniq i hy).symm)
    simp [hk]
  · simp

private lemma pair_agrees (hr : 0 < r) (hsmall : 2 * r < N) (hs : 0 < s)
    (hA : ∀ i, (A i).card = r) (hB : ∀ i, (B i).card = s)
    (hpart : ∀ y, ∃! i, y ∈ B i) (hw : ∀ i, 0 < w i)
    (hadd : Additive (weightedIntersection A B w)) (i j : Fin M) :
    A i = A j ∧ w i = w j := by
  classical
  have hne (k : Fin M) : (B k).Nonempty := Finset.card_pos.mp (by rw [hB k]; exact hs)
  obtain ⟨yi, hyi⟩ := hne i
  obtain ⟨yj, hyj⟩ := hne j

  have hcard : (A i ∪ A j).card < N := calc
    (A i ∪ A j).card ≤ (A i).card + (A j).card := Finset.card_union_le _ _
    _ = 2 * r := by rw [hA i, hA j, two_mul]
    _ < N := hsmall
  have hout : ∃ x₀ : Fin N, x₀ ∉ A i ∪ A j := by
    by_contra hn
    have huniv : A i ∪ A j = Finset.univ := by
      ext x
      constructor
      · exact fun _ => Finset.mem_univ _
      · intro _
        by_contra hx
        exact hn ⟨x, hx⟩
    rw [huniv] at hcard
    simpa using hcard
  obtain ⟨x₀, hx₀⟩ := hout
  have hxi : x₀ ∉ A i := fun hx => hx₀ (Finset.mem_union.mpr (Or.inl hx))
  have hxj : x₀ ∉ A j := fun hx => hx₀ (Finset.mem_union.mpr (Or.inr hx))
  have heq (x : Fin N) : (if x ∈ A i then w i else 0) = (if x ∈ A j then w j else 0) := by
    simpa only [at_column (A := A) (w := w) hpart hyi,
      at_column (A := A) (w := w) hpart hyj, if_neg hxi, if_neg hxj, add_zero]
      using hadd x x₀ yi yj
  have hsets : A i = A j := by
    ext x
    constructor
    · intro hx
      by_contra hnx
      exact (hw i).ne' (by simpa only [if_pos hx, if_neg hnx] using heq x)
    · intro hx
      by_contra hnx
      exact (hw j).ne' (by simpa only [if_pos hx, if_neg hnx] using (heq x).symm)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (A i).card by rw [hA i]; exact hr)
  have hx' : x ∈ A j := hsets ▸ hx
  exact ⟨hsets, by simpa only [if_pos hx, if_pos hx'] using heq x⟩

private lemma short_common (hr : 0 < r) (hsmall : 2 * r < N) (hs : 0 < s)
    (hA : ∀ i, (A i).card = r) (hB : ∀ i, (B i).card = s)
    (hpart : ∀ y, ∃! i, y ∈ B i) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hadd : Additive (weightedIntersection A B w)) :
    ∃ R : Finset (Fin N), R.card = r ∧ (∀ i, A i = R) ∧ (∀ i, (M : ℝ) * w i = 1) := by
  obtain ⟨i₀⟩ := index_nonempty hsum
  have hagree (i : Fin M) : A i = A i₀ ∧ w i = w i₀ :=
    pair_agrees hr hsmall hs hA hB hpart hw hadd i i₀
  have hone : (M : ℝ) * w i₀ = 1 := calc
    (M : ℝ) * w i₀ = ∑ _ : Fin M, w i₀ := by simp
    _ = ∑ i, w i := Finset.sum_congr rfl (fun i _ => (hagree i).2.symm)
    _ = 1 := hsum
  exact ⟨A i₀, hA i₀, fun i => (hagree i).1, fun i => by rw [(hagree i).2, hone]⟩

private lemma cover_of_sizes (hr : 0 < r) (hrs : r ≤ s)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hadd : Additive (weightedIntersection A B w)) :
    (∀ x, ∃ i, x ∈ A i) ∨ (∀ y, ∃ i, y ∈ B i) := by
  refine cover_one_axis (fun i => Finset.card_pos.mp ?_) (fun i => Finset.card_pos.mp ?_)
    hw hsum hadd
  · rcases hsizes i with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega
  · rcases hsizes i with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega

theorem size_bound (hr : 0 < r) (hrs : r ≤ s)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hadd : Additive (weightedIntersection A B w)) :
    N ≤ M * s := by
  rcases cover_of_sizes hr hrs hsizes hw hsum hadd with hcov | hcov
  · refine (cover_count A hcov).1.trans (sum_card_le A (fun i => ?_))
    rcases hsizes i with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega
  · refine (cover_count B hcov).1.trans (sum_card_le B (fun i => ?_))
    rcases hsizes i with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega

theorem block_of_eq (hr : 0 < r) (hrs : r ≤ s) (hsmall : 2 * r < N) (hN : M * s = N)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hadd : Additive (weightedIntersection A B w)) :
    Block r s A B ∧ (∀ i, (M : ℝ) * w i = 1) := by
  have hs : 0 < s := hr.trans_le hrs
  rcases cover_of_sizes hr hrs hsizes hw hsum hadd with hcov | hcov
  · have hle (i : Fin M) : (A i).card ≤ s := by
      rcases hsizes i with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega
    obtain ⟨hAlong, hpart⟩ := tight_cover A hle hcov hN
    have hBshort (i : Fin M) : (B i).card = r := by
      have hh := hAlong i
      rcases hsizes i with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    obtain ⟨R, hR, hcommon, hweights⟩ :=
      short_common hr hsmall hs hBshort hAlong hpart hw hsum (additive_transpose hadd)
    refine ⟨⟨true, R, A, hR, hAlong, hpart, ?_⟩, hweights⟩
    intro i
    change B i = R ∧ A i = A i
    exact ⟨hcommon i, rfl⟩
  · have hle (i : Fin M) : (B i).card ≤ s := by
      rcases hsizes i with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega
    obtain ⟨hBlong, hpart⟩ := tight_cover B hle hcov hN
    have hAshort (i : Fin M) : (A i).card = r := by
      have hh := hBlong i
      rcases hsizes i with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    obtain ⟨R, hR, hcommon, hweights⟩ := short_common hr hsmall hs hAshort hBlong hpart hw hsum hadd
    refine ⟨⟨false, R, B, hR, hBlong, hpart, ?_⟩, hweights⟩
    intro i
    change A i = R ∧ B i = B i
    exact ⟨hcommon i, rfl⟩

private lemma additive_common {R : Finset (Fin N)} (hA : ∀ i, A i = R)
    (hpart : ∀ y, ∃! i, y ∈ B i) (hweights : ∀ i, (M : ℝ) * w i = 1) :
    Additive (weightedIntersection A B w) := by
  intro x x' y y'
  obtain ⟨i, hi, _⟩ := hpart y
  obtain ⟨j, hj, _⟩ := hpart y'
  have hm : (M : ℝ) ≠ 0 := by
    intro hz
    simpa [hz] using hweights i
  have hw : w j = w i := mul_left_cancel₀ hm ((hweights j).trans (hweights i).symm)
  simp only [at_column (A := A) (w := w) hpart hi, at_column (A := A) (w := w) hpart hj,
    hA i, hA j, hw]

theorem additive_of_block (hblock : Block r s A B) (hweights : ∀ i, (M : ℝ) * w i = 1) :
    Additive (weightedIntersection A B w) := by
  obtain ⟨swap, R, S, _, _, hpart, hsets⟩ := hblock
  cases swap with
  | false =>
    have hA (i : Fin M) : A i = R := by simpa using (hsets i).1
    have hB : B = S := funext fun i => by simpa using (hsets i).2
    rw [← hB] at hpart
    exact additive_common hA hpart hweights
  | true =>
    have hB (i : Fin M) : B i = R := by simpa using (hsets i).1
    have hA : A = S := funext fun i => by simpa using (hsets i).2
    rw [← hA] at hpart
    exact additive_transpose (additive_common hB hpart hweights)

theorem additive_iff_block (hr : 0 < r) (hrs : r ≤ s) (hsmall : 2 * r < N) (hN : M * s = N)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    Additive (weightedIntersection A B w) ↔ Block r s A B ∧ (∀ i, (M : ℝ) * w i = 1) :=
  ⟨block_of_eq hr hrs hsmall hN hsizes hw hsum, fun h => additive_of_block h.1 h.2⟩

end Rect

open scoped BigOperators

namespace Build

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.Represents (oneEach)

def tab {N : ℕ} (C : Circuit) (x y : Fin N) : Bool := C.eval (oneEach x y)

def area {N : ℕ} (C : Circuit) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => tab C z.1 z.2)).card

def Fits (N g r s : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
    C.size ≤ g ∧ area (N := N) C ≤ (g+1)*N-r*s

private def extendOr (n : ℕ) (C : Circuit) (b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, b]⟩], n + C.size⟩

private def orChain (n a : ℕ) : List ℕ → Circuit
  | [] => ⟨[], a⟩
  | b :: bs => extendOr n (orChain n a bs) b

private theorem chain_size (n a : ℕ) (bs : List ℕ) : (orChain n a bs).size = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [orChain, extendOr, Circuit.size] using ih

private theorem extend_back {n b : ℕ} {C : Circuit} (hc : ReadsBack n C)
    (ho : C.output < n + C.size) (hb : b < n) : ReadsBack n (extendOr n C b) := by
  intro j hj w hw
  by_cases h : j < C.gates.length
  · have he : gateAt (extendOr n C b) j = gateAt C j := List.getD_append _ _ _ _ h
    exact hc j h w (he ▸ hw)
  · have hj' : j = C.gates.length := by
      simp only [extendOr, List.length_append, List.length_singleton] at hj
      omega
    subst j
    have he : gateAt (extendOr n C b) C.gates.length = ⟨.or, [C.output, b]⟩ := by
      simp [gateAt, extendOr]
    rw [he] at hw
    change w ∈ [C.output, b] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ho
    · exact hb.trans_le (Nat.le_add_right _ _)

private theorem chain_legal {n a : ℕ} (ha : a < n) (bs : List ℕ)
    (hb : ∀ i ∈ bs, i < n) :
    ReadsBack n (orChain n a bs) ∧ (orChain n a bs).output < n + (orChain n a bs).size ∧
      ∀ g ∈ (orChain n a bs).gates, g.inputs.length = 2 ∧ g.op = .or := by
  induction bs with
  | nil => exact ⟨by simp [ReadsBack, orChain], by simpa [orChain, Circuit.size] using ha,
      by simp [orChain]⟩
  | cons b bs ih =>
    obtain ⟨hback, hout, hg⟩ := ih (fun i hi => hb i (List.mem_cons_of_mem _ hi))
    refine ⟨extend_back hback hout (hb b (by simp)), ?_, ?_⟩
    · simp [orChain, extendOr, Circuit.size, Nat.add_assoc]
    · intro g h
      simp only [orChain, extendOr, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact hg g h
      · exact ⟨rfl, rfl⟩

private def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, wireStep, List.length_append,
      List.length_nil, List.length_cons]; omega

private theorem fold_raw (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl wireStep (wireStep w g)).getD i false = _
    rw [ih _ (by simpa [wireStep] using hi.trans_le (Nat.le_add_right w.length 1))]
    exact List.getD_append _ _ _ _ hi

private theorem eval_extend {n b : ℕ} (C : Circuit) (w : List Bool) (hw : w.length = n)
    (hb : b < n) : (extendOr n C b).eval w = (C.eval w || w.getD b false) := by
  have hlen : (C.wires w).length = n + C.size :=
    (fold_length C.gates w).trans (by simp only [hw, Circuit.size])
  have hraw : (C.wires w).getD b false = w.getD b false := fold_raw _ _ (hw.symm ▸ hb)
  have he : (extendOr n C b).wires w = C.wires w ++ [C.eval w || w.getD b false] := by
    change ((C.gates ++ [(⟨.or, [C.output, b]⟩ : Gate)]).foldl wireStep w) = _
    rw [List.foldl_append]
    change C.wires w ++ [(C.wires w).getD C.output false || ((C.wires w).getD b false || false)] = _
    simp only [Bool.or_false, hraw, Circuit.eval]
  change ((extendOr n C b).wires w).getD (n + C.size) false = _
  rw [he, ← hlen]
  simp

private theorem eval_chain {n a : ℕ} (bs : List ℕ) (w : List Bool) (hw : w.length = n)
    (hb : ∀ i ∈ bs, i < n) :
    (orChain n a bs).eval w = true ↔ ∃ i ∈ a :: bs, w.getD i false = true := by
  induction bs with
  | nil => simp [orChain, Circuit.eval, Circuit.wires]
  | cons b bs ih =>
    change (extendOr n (orChain n a bs) b).eval w = true ↔ _
    rw [eval_extend _ _ hw (hb b (by simp)), Bool.or_eq_true_iff,
      ih (fun i hi => hb i (List.mem_cons_of_mem _ hi))]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]
    simp [or_left_comm, or_comm, or_assoc]

private theorem oneEach_left {N : ℕ} (x y i : Fin N) :
    (oneEach x y).getD i.val false = decide (i = x) := by
  unfold oneEach
  have hi : i.val < (List.ofFn (fun j : Fin N => decide (j = x))).length := by simpa using i.isLt
  rw [List.getD_append _ _ _ _ hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem oneEach_right {N : ℕ} (x y i : Fin N) :
    (oneEach x y).getD (N + i.val) false = decide (i = y) := by
  unfold oneEach
  have hi : i.val < (List.ofFn (fun j : Fin N => decide (j = y))).length := by simpa using i.isLt
  have hn : (List.ofFn (fun j : Fin N => decide (j = x))).length ≤ N + i.val := by simp
  rw [List.getD_append_right _ _ _ _ hn, List.length_ofFn, Nat.add_sub_cancel_left]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private noncomputable def labels {N : ℕ} (R S : Finset (Fin N)) : List ℕ :=
  R.toList.map Fin.val ++ S.toList.map (fun j => N + j.val)

private theorem labels_lt {N : ℕ} {R S : Finset (Fin N)} {i : ℕ} (hi : i ∈ labels R S) :
    i < N + N := by
  simp only [labels, List.mem_append, List.mem_map, Finset.mem_toList] at hi
  obtain ⟨j, _, rfl⟩ | ⟨j, _, rfl⟩ := hi
  · exact j.isLt.trans_le (Nat.le_add_right _ _)
  · exact Nat.add_lt_add_left j.isLt _

private theorem labels_hit {N : ℕ} (R S : Finset (Fin N)) (x y : Fin N) :
    (∃ i ∈ labels R S, (oneEach x y).getD i false = true) ↔ x ∈ R ∨ y ∈ S := by
  constructor
  · rintro ⟨i, hi, hv⟩
    simp only [labels, List.mem_append, List.mem_map, Finset.mem_toList] at hi
    obtain ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ := hi
    · have e : j = x := by simpa only [oneEach_left, decide_eq_true_eq] using hv
      exact Or.inl (e ▸ hj)
    · have e : j = y := by simpa only [oneEach_right, decide_eq_true_eq] using hv
      exact Or.inr (e ▸ hj)
  · rintro (hx | hy)
    · refine ⟨x.val, ?_, (oneEach_left x y x).trans (by simp)⟩
      simp only [labels, List.mem_append, List.mem_map, Finset.mem_toList]
      exact Or.inl ⟨x, hx, rfl⟩
    · refine ⟨N + y.val, ?_, (oneEach_right x y y).trans (by simp)⟩
      simp only [labels, List.mem_append, List.mem_map, Finset.mem_toList]
      exact Or.inr ⟨y, hy, rfl⟩

private theorem cross_area {N : ℕ} (R S : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R ∨ z.2 ∈ S)).card =
       (R.card + S.card)*N - R.card*S.card := by
  classical
  let U : Finset (Fin N) := Finset.univ
  have h₁ : (Finset.univ.filter (fun z : Fin N × Fin N => z.1 ∈ R ∨ z.2 ∈ S)) =
      (R ×ˢ U) ∪ (U ×ˢ S) := by ext z; simp [U]
  have h₂ : (R ×ˢ U) ∩ (U ×ˢ S) = R ×ˢ S := by ext z; simp [U]
  have hc := Finset.card_union_add_card_inter (R ×ˢ U) (U ×ˢ S)
  rw [← h₁, h₂] at hc
  simp only [Finset.card_product, U, Finset.card_univ, Fintype.card_fin] at hc
  rw [Nat.add_mul, Nat.mul_comm S.card N]
  omega

theorem synth_cross {N g r s : ℕ} (hgs : r+s=g+1) (R S : Finset (Fin N))
    (hR : R.card = r) (hS : S.card = s) :
    ∃ C : Circuit, Fits N g r s C ∧ area (N := N) C = (g+1)*N-r*s ∧
      ∀ x y, tab C x y = decide (x ∈ R ∨ y ∈ S) := by
  have hlen : (labels R S).length = g+1 := by
    simpa [labels, hR, hS] using hgs
  cases hL : labels R S with
  | nil => simp [hL] at hlen
  | cons a bs =>
    let C := orChain (N+N) a bs
    have ha : a < N+N := labels_lt (R := R) (S := S) (by rw [hL]; simp)
    have hb (i : ℕ) (hi : i ∈ bs) : i < N+N :=
      labels_lt (R := R) (S := S) (by rw [hL]; exact List.mem_cons_of_mem _ hi)
    obtain ⟨hback, hout, hgate⟩ := chain_legal ha bs hb
    have hsize : C.size = g := by
      change (orChain (N+N) a bs).size = g
      rw [chain_size]
      have hlen' : (a :: bs).length = g+1 := by simpa only [hL] using hlen
      simp only [List.length_cons] at hlen'
      omega
    have he (x y : Fin N) : tab C x y = decide (x ∈ R ∨ y ∈ S) := by
      apply Bool.eq_iff_iff.mpr
      change ((orChain (N+N) a bs).eval (oneEach x y) = true) ↔ decide (x ∈ R ∨ y ∈ S) = true
      rw [decide_eq_true_eq, eval_chain _ _ (by simp [oneEach]) hb, ← hL]
      exact labels_hit R S x y
    have harea : area (N := N) C = (g+1)*N-r*s := by
      simpa [area, he, hR, hS, hgs] using cross_area R S
    exact ⟨C, ⟨hback, hout, fun g hg => ⟨le_of_eq (hgate g hg).1, Or.inl (hgate g hg).2⟩,
      hsize.le, harea.le⟩, harea, he⟩

theorem pad_uniform {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) :
    ∃ (p : Fin M → Fin K) (w : Fin M → ℝ), Function.Surjective p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      ∀ f : Fin K → ℝ, (∑ i, w i * f (p i)) = ∑ j, (1 / (K : ℝ)) * f j := by
  classical
  let p (i : Fin M) : Fin K := if h : i.val < K then ⟨i.val, h⟩ else ⟨0, hK⟩
  have hp : Function.Surjective p := by
    intro j
    exact ⟨⟨j.val, j.isLt.trans_le hKM⟩, by simp [p, j.isLt]⟩
  let m (j : Fin K) : ℕ := (Finset.univ.filter (fun i => p i = j)).card
  have hm (j : Fin K) : (0 : ℝ) < m j := by
    obtain ⟨i, hi⟩ := hp j
    exact_mod_cast (Finset.card_pos.mpr ⟨i, by simp [hi]⟩ : 0 < m j)
  let w (i : Fin M) : ℝ := (1 / (K : ℝ)) / (m (p i) : ℝ)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum (f : Fin K → ℝ) : (∑ i, w i * f (p i)) = ∑ j, (1 / (K : ℝ)) * f j := by
    change (∑ i, ((1 / (K : ℝ)) / (m (p i) : ℝ)) * f (p i)) = _
    rw [← Finset.sum_fiberwise' Finset.univ p (fun j => ((1 / (K : ℝ)) / (m j : ℝ)) * f j)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (m j : ℝ) * ((1 / (K : ℝ)) / (m j : ℝ) * f j) = _
    field_simp [hKR.ne', (hm j).ne'] <;> ring
  refine ⟨p, w, hp, fun i => div_pos (one_div_pos.mpr hKR) (hm (p i)), ?_, hsum⟩
  have hn : (∑ _ : Fin K, (1 / (K : ℝ))) = 1 := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using mul_one_div_cancel hKR.ne'
  simpa only [mul_one, hn] using hsum (fun _ => 1)

private def columnsEquiv {N K s : ℕ} (h : N = K*s) : Fin K × Fin s ≃ Fin N :=
  finProdFinEquiv.trans (finCongr h.symm)

private def colBlock {N K s : ℕ} (h : N = K*s) (i : Fin K) : Finset (Fin N) :=
  Finset.univ.map ((⟨fun j => (i, j), fun _ _ e => congrArg Prod.snd e⟩ :
    Fin s ↪ Fin K × Fin s).trans (columnsEquiv h).toEmbedding)

private theorem colBlock_mem {N K s : ℕ} (h : N = K*s) (y : Fin N) (i : Fin K) :
    y ∈ colBlock h i ↔ i = ((columnsEquiv h).symm y).1 := by
  rw [colBlock, Finset.mem_map]
  constructor
  · rintro ⟨j, _, hj⟩
    have he : (i, j) = (columnsEquiv h).symm y := (columnsEquiv h).apply_eq_iff_eq_symm_apply.mp hj
    exact congrArg Prod.fst he
  · intro hi
    let q := (columnsEquiv h).symm y
    exact ⟨q.2, Finset.mem_univ _, (columnsEquiv h).apply_eq_iff_eq_symm_apply.mpr (Prod.ext hi rfl)⟩

theorem block_witness {N g r s M : ℕ} (hgs : r+s=g+1) (hr : 0 < r) (hs : 0 < s)
    (hrs : r*s < N) (hdvd : s ∣ N) (hM : N ≤ M*s) :
    ∃ (D : Fin M → Circuit) (w : Fin M → ℝ),
      (∀ i, Fits N g r s (D i) ∧ 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, area (N := N) (D i) = (g+1)*N-r*s) ∧
      ∃ R : Finset (Fin N), R.card = r ∧ ∀ x y : Fin N,
        (∑ i, w i * (if tab (D i) x y then 1 else 0)) = if x ∈ R then 1 else (s : ℝ)/N := by
  classical
  obtain ⟨K, hK⟩ := hdvd
  have hN : N = K*s := hK.trans (Nat.mul_comm _ _)
  have hk : 0 < K := by
    by_contra! h
    have he : K = 0 := by omega
    simp [he] at hN
    omega
  have hKM : K ≤ M := Nat.le_of_mul_le_mul_right (by simpa only [hN] using hM) hs
  let R : Finset (Fin N) := Finset.univ.map (Fin.castLEEmb ((Nat.le_mul_of_pos_right r hs).trans hrs.le))
  have hR : R.card = r := by simp [R]
  have hS (i : Fin K) : (colBlock hN i).card = s := by simp [colBlock]
  choose C hfit harea he using fun i => synth_cross hgs R (colBlock hN i) hR (hS i)
  obtain ⟨p, w, _, hw, hnorm, hsum⟩ := pad_uniform hk hKM
  refine ⟨C ∘ p, w, fun i => ⟨hfit (p i), hw i⟩, hnorm, fun i => harea (p i), R, hR, ?_⟩
  intro x y
  change (∑ i, w i * (if tab (C (p i)) x y then 1 else 0)) = _
  rw [hsum (fun j => if tab (C j) x y then 1 else 0)]
  have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hx : x ∈ R
  · simpa [he, hx, Finset.sum_const, nsmul_eq_mul] using mul_one_div_cancel hkR
  · have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [he, hx, false_or, decide_eq_true_eq, colBlock_mem, if_false, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hN, Nat.cast_mul]
    field_simp [hkR, hsR]

def cyclicInter {N : ℕ} (C : Circuit) (u : Fin N) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
    tab C z.1 z.2 ∧ (z.2.val+N-z.1.val) % N = u.val)).card

theorem diff_eq_sub {N : ℕ} (x y u : Fin N) :
    (y.val+N-x.val) % N = u.val ↔ y-x = u := by
  have he : (y-x).val = (y.val+N-x.val) % N := by
    rw [Fin.val_sub, Nat.add_sub_assoc x.isLt.le, Nat.add_comm]
  rw [← he, Fin.ext_iff]

private theorem shift_cross {N : ℕ} [NeZero N] (R S : Finset (Fin N)) (u : Fin N) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => (z.1 ∈ R ∨ z.2 ∈ S) ∧ z.2-z.1=u)).card +
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => z.1 ∈ R ∧ z.2 ∈ S ∧ z.2-z.1=u)).card = R.card+S.card := by
  classical
  let U := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R ∧ z.2-z.1=u)
  let V := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 ∈ S ∧ z.2-z.1=u)
  have hu : R.card = U.card := by
    refine Finset.card_bij (fun x _ => (x, u+x)) ?_ (fun _ _ _ _ h => congrArg Prod.fst h) ?_
    · intro x hx
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, hx, add_sub_cancel_right]
    · intro z hz
      have hz' : z.1 ∈ R ∧ z.2-z.1=u := by simpa [U] using hz
      have he : u+z.1 = z.2 := by rw [← hz'.2, sub_add_cancel]
      exact ⟨z.1, hz'.1, Prod.ext rfl he⟩
  have hv : S.card = V.card := by
    refine Finset.card_bij (fun y _ => (y-u, y)) ?_ (fun _ _ _ _ h => congrArg Prod.snd h) ?_
    · intro y hy
      have he : y-(y-u) = u := by abel
      simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, hy, he]
    · intro z hz
      have hz' : z.2 ∈ S ∧ z.2-z.1=u := by simpa [V] using hz
      have he : z.2-u = z.1 := by rw [← hz'.2]; abel
      exact ⟨z.2, hz'.1, Prod.ext he rfl⟩
  have hUnion : U ∪ V = Finset.univ.filter (fun z => (z.1 ∈ R ∨ z.2 ∈ S) ∧ z.2-z.1=u) := by
    ext z
    simp [U, V, or_and_right]
  have hInter : U ∩ V = Finset.univ.filter (fun z => z.1 ∈ R ∧ z.2 ∈ S ∧ z.2-z.1=u) := by
    ext z
    simp only [U, V, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simpa only [hUnion, hInter, ← hu, ← hv] using Finset.card_union_add_card_inter U V

private def cycRow {N r s : ℕ} (hrs : r*s ≤ N) (hs : 0 < s) : Fin r ↪ Fin N where
  toFun a := ⟨a.rev.val*s, (Nat.mul_lt_mul_of_pos_right a.rev.isLt hs).trans_le hrs⟩
  inj' a b e := Fin.rev_injective (Fin.ext (Nat.eq_of_mul_eq_mul_right hs (congrArg Fin.val e)))

private def cycCol {N K r s : ℕ} (hN : N = K*(r*s)) (hr : 0 < r) (i : Fin K) :
    Fin s ↪ Fin N where
  toFun b := columnsEquiv hN (i, finProdFinEquiv ((⟨r-1, by omega⟩ : Fin r), b))
  inj' a b e := by
    have h := (columnsEquiv hN).injective e
    exact congrArg Prod.snd (finProdFinEquiv.injective (congrArg Prod.snd h))

private def diffEquiv {N K r s : ℕ} (hN : N = K*(r*s)) : Fin K × (Fin r × Fin s) ≃ Fin N :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans (columnsEquiv hN)

private theorem cyc_code {N K r s : ℕ} (hN : N = K*(r*s)) (hrs : r*s ≤ N)
    (hr : 0 < r) (hs : 0 < s) (i : Fin K) (a : Fin r) (b : Fin s) :
    cycCol hN hr i b - cycRow hrs hs a = diffEquiv hN (i, (a,b)) := by
  have hrev : a.rev.val + a.val = r-1 := by
    rw [Fin.val_rev]
    have := a.isLt
    omega
  have hmul : a.rev.val*s + s*a.val = s*(r-1) := by
    rw [Nat.mul_comm a.rev.val s, ← Nat.mul_add, hrev]
  have hle : cycRow hrs hs a ≤ cycCol hN hr i b := by
    change a.rev.val*s ≤ b.val + s*(r-1) + (r*s)*i.val
    omega
  apply Fin.ext
  rw [Fin.sub_val_of_le hle]
  change b.val + s*(r-1) + (r*s)*i.val - a.rev.val*s = b.val + s*a.val + (r*s)*i.val
  omega

private theorem cyclic_overlap {N K r s : ℕ} (hN : N = K*(r*s)) (hrs : r*s ≤ N)
    (hr : 0 < r) (hs : 0 < s) (i : Fin K) (u : Fin N) :
    let R := Finset.univ.map (cycRow hrs hs)
    let S := Finset.univ.map (cycCol hN hr i)
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => z.1 ∈ R ∧ z.2 ∈ S ∧ z.2-z.1=u)).card =
      if i = ((diffEquiv hN).symm u).1 then 1 else 0 := by
  classical
  dsimp only
  let q := (diffEquiv hN).symm u
  let z₀ := (cycRow hrs hs q.2.1, cycCol hN hr q.1 q.2.2)
  have hmem (z : Fin N × Fin N) :
      (z.1 ∈ Finset.univ.map (cycRow hrs hs) ∧ z.2 ∈ Finset.univ.map (cycCol hN hr i) ∧
        z.2-z.1=u) ↔ i = q.1 ∧ z = z₀ := by
    constructor
    · rintro ⟨ha, hb, hd⟩
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp ha
      obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hb
      have hz : (cycRow hrs hs a, cycCol hN hr i b) = z := Prod.ext ha hb
      rw [← hz] at hd
      change cycCol hN hr i b - cycRow hrs hs a = u at hd
      rw [cyc_code hN hrs hr hs] at hd
      have hq : (i, (a,b)) = q := (diffEquiv hN).apply_eq_iff_eq_symm_apply.mp hd
      exact ⟨congrArg Prod.fst hq, hz.symm.trans (congrArg (fun p : Fin K × (Fin r × Fin s) =>
        (cycRow hrs hs p.2.1, cycCol hN hr p.1 p.2.2)) hq)⟩
    · rintro ⟨hi, rfl⟩
      refine ⟨Finset.mem_map.mpr ⟨q.2.1, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · rw [hi]
        exact Finset.mem_map.mpr ⟨q.2.2, Finset.mem_univ _, rfl⟩
      · change cycCol hN hr q.1 q.2.2 - cycRow hrs hs q.2.1 = u
        rw [cyc_code hN hrs hr hs]
        exact (diffEquiv hN).apply_symm_apply u
  have he : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
        z.1 ∈ Finset.univ.map (cycRow hrs hs) ∧ z.2 ∈ Finset.univ.map (cycCol hN hr i) ∧ z.2-z.1=u) =
      if i = q.1 then {z₀} else ∅ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
    by_cases hi : i = q.1 <;> simp [hi]
  rw [he]
  change (if i = q.1 then {z₀} else (∅ : Finset _)).card = (if i = q.1 then 1 else 0)
  by_cases hi : i = q.1 <;> simp [hi]

theorem cyclic_witness {N g r s M : ℕ} (hgs : r+s=g+1) (hr : 0 < r) (hs : 0 < s)
    (hrs : r*s < N) (hdvd : r*s ∣ N) (hM : N ≤ M*(r*s)) :
    ∃ (D : Fin M → Circuit) (w : Fin M → ℝ),
      (∀ i, Fits N g r s (D i) ∧ 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, area (N := N) (D i) = (g+1)*N-r*s) ∧ ∀ u : Fin N,
        (∑ i, w i * (cyclicInter (D i) u : ℝ)) = (r : ℝ)+s-(r*s : ℝ)/N := by
  classical
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨K, hK⟩ := hdvd
  have hN : N = K*(r*s) := hK.trans (Nat.mul_comm _ _)
  have hk : 0 < K := by
    by_contra! h
    have he : K = 0 := by omega
    simp [he] at hN
    omega
  have hKM : K ≤ M := Nat.le_of_mul_le_mul_right (by simpa only [hN] using hM) (Nat.mul_pos hr hs)
  let R := Finset.univ.map (cycRow hrs.le hs)
  let S (i : Fin K) := Finset.univ.map (cycCol hN hr i)
  have hR : R.card = r := by simp [R]
  have hS (i : Fin K) : (S i).card = s := by simp [S]
  choose C hfit harea he using fun i => synth_cross hgs R (S i) hR (hS i)
  obtain ⟨p, w, _, hw, hnorm, hsum⟩ := pad_uniform hk hKM
  refine ⟨C ∘ p, w, fun i => ⟨hfit (p i), hw i⟩, hnorm, fun i => harea (p i), ?_⟩
  intro u
  let j := ((diffEquiv hN).symm u).1
  have hcard (i : Fin K) : cyclicInter (C i) u + (if i = j then 1 else 0) = r+s := by
    have h := shift_cross R (S i) u
    rw [hR, hS i] at h
    have hint : cyclicInter (C i) u = ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => (z.1 ∈ R ∨ z.2 ∈ S i) ∧ z.2-z.1=u)).card := by
      simp [cyclicInter, he, diff_eq_sub]
    rw [hint]
    have htile := cyclic_overlap hN hrs.le hr hs i u
    change ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => z.1 ∈ R ∧ z.2 ∈ S i ∧ z.2-z.1=u)).card = (if i = j then 1 else 0) at htile
    rwa [htile] at h
  have hcardR (i : Fin K) : (cyclicInter (C i) u : ℝ) = (r : ℝ)+s-(if i = j then 1 else 0) := by
    apply eq_sub_of_add_eq
    have h := hcard i
    by_cases hi : i = j
    · simp only [hi, if_true] at h ⊢
      exact_mod_cast h
    · simp only [hi, if_false] at h ⊢
      exact_mod_cast h
  change (∑ i, w i * (cyclicInter (C (p i)) u : ℝ)) = _
  rw [hsum (fun i => (cyclicInter (C i) u : ℝ))]
  simp_rw [hcardR, mul_sub, Finset.sum_sub_distrib]
  have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hconst : (∑ _ : Fin K, (1 / (K : ℝ)) * ((r : ℝ)+s)) = (r : ℝ)+s := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_one_div_cancel hkR, one_mul]
  rw [hconst]
  simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hN]
  push_cast
  field_simp [hkR, hrR, hsR] <;> ring

end Build

open scoped BigOperators
namespace Main
open Loss
open Shape (Fits saturated_shape)

private theorem trace_card {N : ℕ} [NeZero N] (C : Circ) (u : X N) :
    trace (tab C) u = (Build.cyclicInter C u : ℝ) := by
  classical
  unfold trace
  rw [← card_bit]
  have hdiff (x y : X N) : (y.val+N-x.val)%N = u.val ↔ y = x+u := by
    have h := congrFun (congrFun (defect_eq u) x) y
    change decide (y-x ≠ u) = decide ((y.val+N-x.val)%N ≠ u.val) at h
    constructor
    · intro h₁
      rw [h₁] at h
      have h₂ : y-x = u := by simpa using h
      exact (sub_eq_iff_eq_add.mp h₂).trans (add_comm _ _)
    · intro h₁
      have he : y-x = u := by rw [h₁, add_sub_cancel_left]
      rw [he] at h
      simpa using h.symm
  let e : X N ↪ X N × X N := ⟨fun x => (x,x+u), fun _ _ h => congrArg Prod.fst h⟩
  have he : Build.cyclicInter C u =
      (Finset.univ.filter (fun x : X N => tab C x (x+u))).card := by
    unfold Build.cyclicInter
    rw [← Finset.card_map e]
    congr 1
    ext p
    rcases p with ⟨x,y⟩
    constructor
    · intro hp
      obtain ⟨_, htab, hy⟩ := Finset.mem_filter.mp hp
      have h : y = x+u := (hdiff x y).mp hy
      subst y
      exact Finset.mem_map.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htab⟩, rfl⟩
    · intro hp
      obtain ⟨z, hz, h⟩ := Finset.mem_map.mp hp
      have hx : z = x := congrArg Prod.fst h
      have hy : z+u = y := congrArg Prod.snd h
      subst z
      subst y
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2, (hdiff x (x+u)).mpr rfl⟩
  rw [he]

private theorem normal_shapes {N g r s M : ℕ} (hr : 0 < r) (hrs : r ≤ s) (hgs : r+s=g+1)
    (hp : r*s<N) (hN : 2*g+1<N) (D : Fin M → Circ)
    (hD : ∀ i, Fits N g r s (D i)) (hA : ∀ i, size (tab (D i) : Tbl N) = (g+1)*N-r*s) :
    ∃ A B : Fin M → Finset (X N),
      (∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r)) ∧
      ∀ i x y, tab (D i) x y = decide (x ∈ A i ∨ y ∈ B i) := by
  classical
  have hex (i : Fin M) : ∃ A B : Finset (X N),
      ((A.card = r ∧ B.card = s) ∨ (A.card = s ∧ B.card = r)) ∧
      ∀ x y, tab (D i) x y = decide (x ∈ A ∨ y ∈ B) := by
    obtain ⟨sw, A, B, ha, hb, he⟩ := saturated_shape hr hrs hgs hp hN (hD i) (hA i)
    cases sw with
    | false => exact ⟨A,B, Or.inl ⟨ha,hb⟩, he⟩
    | true =>
      refine ⟨B,A, Or.inr ⟨hb,ha⟩, fun x y => ?_⟩
      have h : tab (D i) x y = decide (y ∈ A ∨ x ∈ B) := he y x
      exact h.trans (by simp [or_comm])
  choose A B hs he using hex
  exact ⟨A,B,hs,he⟩

private theorem cap_on_block {N g r s M : ℕ} (hgs : r+s=g+1) (D : Fin M → Circ)
    (sw : Bool) (R : Finset (X N)) (S : Fin M → Finset (X N)) (hR : R.card=r)
    (hS : ∀ i, (S i).card=s) (hD : ∀ i x y, (if sw then tab (D i) y x else tab (D i) x y) =
      decide (x ∈ R ∨ y ∈ S i)) : ∀ i, size (tab (D i) : Tbl N) = (g+1)*N-r*s := by
  intro i
  cases sw with
  | false =>
    have he : tab (D i) = fun x y => decide (x ∈ R ∨ y ∈ S i) := funext fun x => funext fun y => hD i x y
    rw [he, size_union_lines, hR, hS, hgs]
  | true =>
    have he : tab (D i) = fun x y => decide (x ∈ S i ∨ y ∈ R) := funext fun x => funext fun y => by
      simpa [or_comm] using hD i y x
    rw [he, size_union_lines, hR, hS, Nat.add_comm s r, Nat.mul_comm s r, hgs]

end Main

end PEqualNP.Outside.L_meta_33634

open PEqualNP.Outside.L_meta_33634.Shape (Fits) in
open PEqualNP.Outside.L_meta_33634 PEqualNP.Outside.L_meta_33634.Main PEqualNP.Outside.L_meta_33634.Loss in
theorem PEqualNP.Outside.L_meta_33634 : (∀ (N g t r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N →
  2*g+1 < N → N < 2*t → t < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let A := (g+1)*N-r*s
  let fits := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
    C.size ≤ g ∧ ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card ≤ A
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let loss := fun (C : Circ) (T : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
  let bench := N*(N*t)-(2*t-N)*A
  let valid := fun (M : ℕ) (D : Fin M → Circ) (w : Fin M → ℝ) =>
    (∀ i, fits (D i) ∧ 0 < w i) ∧ ∑ i, w i = 1
  let err := fun (M : ℕ) (D : Fin M → Circ) (w : Fin M → ℝ) (T : X → X → Bool) =>
    (N : ℝ)*∑ i, w i*(loss (D i) T : ℝ)
  let good := fun M D w => ∀ T, reg T → err M D w T ≤ (bench : ℝ)
  let block := fun (M : ℕ) (D : Fin M → Circ) =>
    ∃ (swap : Bool) (R : Finset X) (S : Fin M → Finset X),
      R.card = r ∧ (∀ i, (S i).card = s) ∧ (∀ y : X, ∃! i, y ∈ S i) ∧
      ∀ (i : Fin M) (x y : X), (if swap then tab (D i) y x else tab (D i) x y) =
        decide (x ∈ R ∨ y ∈ S i)
  (∀ (M : ℕ) (D : Fin M → Circ) (w : Fin M → ℝ), valid M D w →
    (∃ T, reg T ∧ (bench : ℝ) ≤ err M D w T) ∧
    (good M D w → N ≤ M*s) ∧
    (M*s = N → (good M D w ↔ block M D ∧ ∀ i, (M : ℝ)*w i = 1))) ∧
  (s ∣ N → ∀ M : ℕ, (∃ D w, valid M D w ∧ good M D w) ↔ N ≤ M*s) ∧
  (r*s ∣ N → t+1 = N → ∀ M : ℕ,
    (∃ D w, valid M D w ∧ ∀ u : X,
      err M D w (fun x y => decide ((y.val+N-x.val) % N ≠ u.val)) ≤ (bench : ℝ)) ↔ N ≤ M*(r*s))) := by
  classical
  intro N g t r s hr hrs hgs hp hN ht htN
  dsimp only
  letI : NeZero N := ⟨by omega⟩
  let cap := (g+1)*N-r*s
  have hcapN : cap ≤ N*N := (Nat.sub_le _ _).trans (Nat.mul_le_mul_right N (by omega))
  have hbench := bench_cast ht htN.le hcapN
  have hreg : reg t (cyclic t : Tbl N) := cyclic_reg htN.le
  have hcaps {M : ℕ} (D : Fin M → Circ) (h : ∀ i, Fits N g r s (D i)) :
      ∀ i, size (tab (D i) : Tbl N) ≤ cap := fun i => (h i).2.2.2.2
  have from_good {M : ℕ} (D : Fin M → Circ) (w : Fin M → ℝ)
      (hf : ∀ i, Fits N g r s (D i)) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
      (hg : ∀ T : Tbl N, reg t T → err (fun i => tab (D i)) w T ≤ benchR N t cap) :
      ∃ A B : Fin M → Finset (X N),
        (∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r)) ∧
        (∀ i x y, tab (D i) x y = decide (x ∈ A i ∨ y ∈ B i)) ∧
        Rect.Additive (Rect.weightedIntersection A B w) := by
    have hsat := (saturates (fun i => tab (D i)) w hw1 hw (hcaps D hf) ht hreg
      (fun u => hg _ (shift_reg hreg u))).1
    obtain ⟨A,B,hs,he⟩ := Main.normal_shapes hr hrs hgs hp hN D hf hsat
    have hdiff := mixed_diff (by omega : 1 < N) (by omega : 0<t) htN
      (fun i => tab (D i)) w hw1 hw (hcaps D hf) ht hg
    exact ⟨A,B,hs,he,(mixed_union_iff (fun i => tab (D i)) w A B he).mp hdiff⟩
  have lower {M : ℕ} (D : Fin M → Circ) (w : Fin M → ℝ) (hf : ∀ i, Fits N g r s (D i))
      (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
      (hg : ∀ T : Tbl N, reg t T → err (fun i => tab (D i)) w T ≤ benchR N t cap) : N ≤ M*s := by
    obtain ⟨A,B,hs,_,ha⟩ := from_good D w hf hw hw1 hg
    exact Rect.size_bound hr hrs hs hw hw1 ha
  refine ⟨?_, ?_, ?_⟩
  · intro M D w hv
    obtain ⟨hFit,hw1⟩ := hv
    have hf : ∀ i, Fits N g r s (D i) := fun i => (hFit i).1
    have hw : ∀ i, 0 < w i := fun i => (hFit i).2
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨T,hT,he⟩ := adversary_exists (fun i => tab (D i)) w hw1 hw (hcaps D hf) ht hreg
      exact ⟨T,hT,hbench.le.trans he⟩
    · intro hg
      exact lower D w hf hw hw1 (fun T hT => (hg T hT).trans hbench.le)
    · intro hM
      constructor
      · intro hg
        obtain ⟨A,B,hs,he,ha⟩ := from_good D w hf hw hw1 (fun T hT => (hg T hT).trans hbench.le)
        obtain ⟨⟨sw,R,S,hR,hS,hpar,hSets⟩,hwM⟩ :=
          Rect.block_of_eq hr hrs (by omega) hM hs hw hw1 ha
        refine ⟨⟨sw,R,S,hR,hS,hpar,?_⟩,hwM⟩
        intro i x y
        obtain ⟨ha,hb⟩ := hSets i
        cases sw with
        | false =>
          change A i = R at ha
          change B i = S i at hb
          change tab (D i) x y = _
          rw [he,ha,hb]
        | true =>
          change B i = R at ha
          change A i = S i at hb
          change tab (D i) y x = _
          rw [he,ha,hb]
          simp [or_comm]
      · rintro ⟨⟨sw,R,S,hR,hS,hpar,he⟩,hwm⟩ T hT
        let A := fun i => if sw then S i else R
        let B := fun i => if sw then R else S i
        have hu (i) (x y : X N) : tab (D i) x y = decide (x ∈ A i ∨ y ∈ B i) := by
          cases sw
          · exact he i x y
          · simpa [A,B,Loss.tab,or_comm] using he i y x
        have hB : Rect.Block r s A B :=
          ⟨sw,R,S,hR,hS,hpar,fun i => by cases sw <;> exact ⟨rfl,rfl⟩⟩
        have ha := Rect.additive_of_block hB hwm
        have hd := (mixed_union_iff (fun i => tab (D i)) w A B hu).mpr ha
        have eq := good_if_add (fun i => tab (D i)) w hw1 (Main.cap_on_block hgs D sw R S hR hS he) hd hT
        exact (eq.trans hbench.symm).le
  · intro hdvd M
    constructor
    · rintro ⟨D,w,⟨hf,hw1⟩,hg⟩
      exact lower D w (fun i => (hf i).1) (fun i => (hf i).2) hw1 (fun T hT => (hg T hT).trans hbench.le)
    · intro hM
      obtain ⟨D,w,hf,hw1,hA,R,hR,hMass⟩ := Build.block_witness hgs hr (by omega) hp hdvd hM
      refine ⟨D,w,⟨hf,hw1⟩,fun T hT => ?_⟩
      have hm (x y : X N) : average (fun i => tab (D i)) w x y = if x ∈ R then 1 else (s:ℝ)/N := hMass x y
      have ha : IsAdd (N := N) (average (fun i => tab (D i)) w) := by
        intro a b c d
        rw [hm a c, hm b d, hm a d, hm b c]
      exact ((good_if_add (fun i => tab (D i)) w hw1 hA ha hT).trans hbench.symm).le
  · intro hdvd htn M
    constructor
    · rintro ⟨D,w,⟨hf,hw1⟩,hg⟩
      have hdef (u : X N) : err (fun i => tab (D i)) w (defect u) ≤ benchR N t cap := by
        rw [defect_eq, ← hbench]
        exact hg u
      have hs := (saturates (fun i => tab (D i)) w hw1 (fun i => (hf i).2) (hcaps D (fun i => (hf i).1))
        ht hreg (fun u => by rw [shift_defect htn]; exact hdef _)).1
      obtain ⟨A,B,hAB,he⟩ := Main.normal_shapes hr hrs hgs hp hN D (fun i => (hf i).1) hs
      exact support_cyclic htn hgs (Nat.mul_pos hr (by omega)) hp (fun i => tab (D i)) w hw1 hs A B he
        (fun i => by rcases hAB i with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [ha,hb,Nat.add_comm,Nat.mul_comm]) hdef
    · intro hM
      obtain ⟨D,w,hf,hw1,hA,hTr⟩ := Build.cyclic_witness hgs hr (by omega) hp hdvd hM
      refine ⟨D,w,⟨hf,hw1⟩,fun u => ?_⟩
      change err (fun i => tab (D i)) w (fun x y => decide ((y.val+N-x.val)%N ≠ u.val)) ≤ _
      change ∀ i, size (tab (D i) : Tbl N) = cap at hA
      rw [← defect_eq, hbench, err_defect htn (fun i => tab (D i)) w hw1 hA, benchR]
      have hc (i : Fin M) : trace (tab (D i)) u = (Build.cyclicInter (D i) u : ℝ) := Main.trace_card _ _
      simp_rw [hc]
      rw [hTr]
      have hcast : (cap : ℝ) = ((g:ℝ)+1)*N-(r:ℝ)*s := by
        unfold cap
        rw [Nat.cast_sub (hp.le.trans (by nlinarith : N ≤ (g+1)*N))]
        push_cast; rfl
      have htReal : (t:ℝ)+1=N := by exact_mod_cast htn
      have htn' : (t:ℝ)=N-1 := by linarith only [htReal]
      have hgs' : (r:ℝ)+s=(g:ℝ)+1 := by exact_mod_cast hgs
      have hn : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      rw [hcast, htn', hgs']
      apply le_of_eq
      field_simp
      ring
