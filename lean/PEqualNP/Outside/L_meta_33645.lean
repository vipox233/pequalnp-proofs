import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33645

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


end Build

open scoped BigOperators

namespace Cover

def cov (s n m : ℕ) (S : Fin m → Finset (Fin n)) (v : Fin m → ℝ) : Prop :=
  (∀ i, (S i).card = s ∧ 0 < v i) ∧ ∀ y, (∑ i, if y ∈ S i then v i else 0) = 1

noncomputable def K (s n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S v, cov s n m S v}

lemma cov_sum_weights {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (h : cov s n m S v) : (s : ℝ) * ∑ i, v i = (n : ℝ) := by
  classical
  calc
    (s : ℝ) * ∑ i, v i
      = ∑ i, ((S i).card : ℝ) * v i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [(h.1 i).1]
    _ = ∑ i, ∑ y : Fin n, if y ∈ S i then v i else 0 :=
          Finset.sum_congr rfl fun i _ => by
            simp [Finset.sum_ite, Finset.filter_mem_eq_inter]
    _ = ∑ y : Fin n, ∑ i, if y ∈ S i then v i else 0 := Finset.sum_comm
    _ = (n : ℝ) := by simp [h.2]

lemma cov_pos_m {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (hn : 0 < n) (h : cov s n m S v) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst hm0
  have hsum := cov_sum_weights h
  simp at hsum
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact hn0 hsum.symm

lemma cov_v_le_one {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (hs : 0 < s) (h : cov s n m S v) (i : Fin m) : v i ≤ 1 := by
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [(h.1 i).1]; exact hs)
  have hle : (if y ∈ S i then v i else 0) ≤ ∑ j, if y ∈ S j then v j else 0 :=
    Finset.single_le_sum (f := fun j => if y ∈ S j then v j else 0)
      (fun j _ => by split_ifs; exact (h.1 j).2.le; exact le_rfl) (Finset.mem_univ i)
  simp only [hy, ↓reduceIte, h.2 y] at hle
  exact hle

lemma cov_disjoint_of_eq_one {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (h : cov s n m S v) {i j : Fin m} (hi : v i = 1) (hji : j ≠ i) :
    Disjoint (S i) (S j) := by
  rw [Finset.disjoint_left]
  intro y hyi hyj
  have hsum : (∑ k ∈ ({i, j} : Finset (Fin m)), if y ∈ S k then v k else 0) ≤
      ∑ k : Fin m, if y ∈ S k then v k else 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => by
      split_ifs
      · exact (h.1 k).2.le
      · exact le_rfl
  rw [Finset.sum_pair hji.symm, h.2 y] at hsum
  simp only [hyi, hyj, ↓reduceIte, hi] at hsum
  linarith [(h.1 j).2]

lemma cov_eq_one_of_unique {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (h : cov s n m S v) {i : Fin m} {y : Fin n} (hy : y ∈ S i)
    (huniq : ∀ j, y ∈ S j → j = i) : v i = 1 := by
  have h1 := h.2 y
  rw [Finset.sum_eq_single i] at h1
  · simpa [hy] using h1
  · intro j _ hji
    have hj : y ∉ S j := fun hm => hji (huniq j hm)
    simp [hj]
  · simp

lemma cov_exists_cyclic {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    ∃ S v, cov s n n S v := by
  let _ : NeZero n := ⟨by omega⟩
  let S : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun y => Loss.cyclic s i y)
  let v : Fin n → ℝ := fun _ => (1 : ℝ) / (s : ℝ)
  have hreg := Loss.cyclic_reg (N := n) hsn
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  refine ⟨S, v, ⟨fun i => ⟨hreg.1 i, one_div_pos.mpr hsR⟩, fun y => ?_⟩⟩
  have hf : Finset.univ.filter (fun i : Fin n => y ∈ S i) =
      Finset.univ.filter (fun i : Fin n => Loss.cyclic s i y) := by
    ext i
    simp [S]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hf, hreg.2 y]
  exact mul_one_div_cancel hsR.ne'

lemma K_nonempty {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    {m : ℕ | ∃ S v, cov s n m S v}.Nonempty :=
  ⟨n, cov_exists_cyclic hs hsn⟩

lemma K_spec {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    ∃ S v, cov s n (K s n) S v :=
  Nat.sInf_mem (K_nonempty hs hsn)

lemma K_le {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (h : cov s n m S v) : K s n ≤ m :=
  Nat.sInf_le ⟨S, v, h⟩

lemma K_pos {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) : 0 < K s n := by
  obtain ⟨S, v, h⟩ := K_spec hs hsn
  exact cov_pos_m (by omega) h

lemma cov_add_block {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (h : cov s n m S v) : ∃ S' v', cov s (n + s) (m + 1) S' v' := by
  classical
  let eL : Fin n ↪ Fin (n + s) :=
    ⟨fun x => ⟨x.val, by omega⟩, fun a b hx => by
      cases a; cases b; simp only [Fin.mk.injEq] at hx ⊢; exact hx⟩
  let eR : Fin s ↪ Fin (n + s) :=
    ⟨fun x => ⟨n + x.val, by omega⟩, fun a b hx => by
      cases a; cases b; simp only [Fin.mk.injEq] at hx ⊢; omega⟩
  let S' : Fin (m + 1) → Finset (Fin (n + s)) :=
    Fin.snoc (fun i : Fin m => (S i).map eL) (Finset.univ.map eR)
  let v' : Fin (m + 1) → ℝ := Fin.snoc v (1 : ℝ)
  refine ⟨S', v', ⟨fun i => ?_, fun y => ?_⟩⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [S', v', Fin.snoc_last]
    · simp [S', v', Fin.snoc_castSucc, (h.1 j).1, (h.1 j).2]
  · rw [Fin.sum_univ_castSucc]
    simp only [S', v', Fin.snoc_castSucc, Fin.snoc_last]
    by_cases hy : y.val < n
    · have hnotR : y ∉ Finset.univ.map eR := by
        rw [Finset.mem_map]
        rintro ⟨x, _, hx⟩
        have hval : n + x.val = y.val := congrArg Fin.val hx
        omega
      have hmemL (j : Fin m) : y ∈ (S j).map eL ↔ (⟨y.val, hy⟩ : Fin n) ∈ S j := by
        rw [Finset.mem_map]
        constructor
        · rintro ⟨x, hx, hxy⟩
          have hval : x.val = y.val := congrArg Fin.val hxy
          have : x = ⟨y.val, hy⟩ := Fin.ext hval
          rwa [← this]
        · intro hx
          exact ⟨⟨y.val, hy⟩, hx, Fin.ext rfl⟩
      simp only [hnotR, ↓reduceIte, add_zero]
      calc
        (∑ j : Fin m, if y ∈ (S j).map eL then v j else 0)
          = ∑ j : Fin m, if (⟨y.val, hy⟩ : Fin n) ∈ S j then v j else 0 :=
              Finset.sum_congr rfl fun j _ => by simp only [hmemL j]
        _ = 1 := h.2 ⟨y.val, hy⟩
    · have hmemR : y ∈ Finset.univ.map eR := by
        rw [Finset.mem_map]
        refine ⟨⟨y.val - n, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        change n + (y.val - n) = y.val
        omega
      have hnotL (j : Fin m) : y ∉ (S j).map eL := by
        rw [Finset.mem_map]
        rintro ⟨x, _, hxy⟩
        have hval : x.val = y.val := congrArg Fin.val hxy
        omega
      simp only [hmemR, ↓reduceIte]
      have hz : (∑ j : Fin m, if y ∈ (S j).map eL then v j else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp only [hnotL j, ↓reduceIte]
      rw [hz, zero_add]

lemma K_add_s_le {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) : K s (n + s) ≤ K s n + 1 := by
  obtain ⟨S, v, h⟩ := K_spec hs hsn
  obtain ⟨S', v', h'⟩ := cov_add_block h
  exact K_le h'

lemma K_add_mul_s_le {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) (d : ℕ) :
    K s (n + d * s) ≤ K s n + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : n + (d + 1) * s = (n + d * s) + s := by ring
    rw [h1]
    exact (K_add_s_le hs (by omega)).trans (by omega)

lemma K_self_le {s : ℕ} : K s s ≤ 1 := by
  refine K_le (S := fun _ : Fin 1 => Finset.univ) (v := fun _ => 1) ⟨fun _ => ?_, fun _ => ?_⟩
  · simp
  · simp

lemma K_mul_s_le {s q : ℕ} (hs : 0 < s) (hq : 0 < q) : K s (q * s) ≤ q := by
  have h1 : q * s = s + (q - 1) * s := by
    cases q with
    | zero => omega
    | succ q' => simp [Nat.add_mul, Nat.add_comm]
  rw [h1]
  exact (K_add_mul_s_le hs le_rfl (q - 1)).trans (by have := K_self_le (s := s); omega)

lemma K_le_div_add {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) : K s n ≤ n / s + 2 * s - 2 := by
  have hq : 0 < n / s := Nat.div_pos hsn hs
  have hdiv : n = (n / s) * s + n % s := by
    have := Nat.div_add_mod n s
    linarith [Nat.mul_comm s (n / s)]
  by_cases hrem : n % s = 0
  · have hn : (n / s) * s = n := by omega
    have h1 := K_mul_s_le hs hq
    rw [hn] at h1
    omega
  · have hrem_lt : n % s < s := Nat.mod_lt n hs
    have hn : n = (s + n % s) + (n / s - 1) * s := by
      have hq1 : (n / s - 1) * s + s = (n / s) * s := by
        cases hqq : n / s with
        | zero => omega
        | succ k => simp [Nat.add_mul]
      omega
    have hcyc : K s (s + n % s) ≤ s + n % s := by
      obtain ⟨S, v, h⟩ := cov_exists_cyclic hs (by omega : s ≤ s + n % s)
      exact K_le h
    have hstep := K_add_mul_s_le hs (by omega : s ≤ s + n % s) (n / s - 1)
    rw [← hn] at hstep
    omega

lemma cov_peel_isolated {s n m : ℕ} {S : Fin m → Finset (Fin n)} {v : Fin m → ℝ}
    (h : cov s n m S v) {i₀ : Fin m} (hi₀ : v i₀ = 1) :
    ∃ S' v', cov s (n - s) (m - 1) S' v' := by
  classical
  let U : Finset (Fin n) := (S i₀)ᶜ
  let J : Finset (Fin m) := Finset.univ.erase i₀
  have hUcard : U.card = n - s := by
    simp [U, Finset.card_compl, (h.1 i₀).1]
  have hJcard : J.card = m - 1 := by
    simp [J, Finset.card_erase_of_mem]
  let eU : {y : Fin n // y ∈ U} ≃ Fin (n - s) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hUcard])
  let eJ : {j : Fin m // j ∈ J} ≃ Fin (m - 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hJcard])
  let S' : Fin (m - 1) → Finset (Fin (n - s)) :=
    fun k => Finset.univ.filter (fun z => (eU.symm z).1 ∈ S (eJ.symm k).1)
  let v' : Fin (m - 1) → ℝ := fun k => v (eJ.symm k).1
  refine ⟨S', v', ⟨fun k => ⟨?_, (h.1 _).2⟩, fun z => ?_⟩⟩
  · have hne : (eJ.symm k).1 ≠ i₀ := (Finset.mem_erase.mp (eJ.symm k).2).1
    have hdisj : Disjoint (S i₀) (S (eJ.symm k).1) := cov_disjoint_of_eq_one h hi₀ hne
    have hsub : S (eJ.symm k).1 ⊆ U := by
      intro y hy
      exact Finset.mem_compl.mpr (Finset.disjoint_right.mp hdisj hy)
    let f : Fin (n - s) → Fin n := fun z => (eU.symm z).1
    have hf : Function.Injective f := fun a b hab => eU.symm.injective (Subtype.ext hab)
    have himg : (S' k).image f = S (eJ.symm k).1 := by
      ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Finset.mem_filter.mp hz).2
      · intro hy
        refine ⟨eU ⟨y, hsub hy⟩, ?_, by simp [f]⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy⟩
    rw [← Finset.card_image_of_injective (S' k) hf, himg, (h.1 _).1]
  · let y : Fin n := (eU.symm z).1
    have hyU : y ∉ S i₀ := Finset.mem_compl.mp (eU.symm z).2
    have hsum1 : (∑ k : Fin (m - 1), if z ∈ S' k then v' k else 0) =
        ∑ j : {j : Fin m // j ∈ J}, if y ∈ S j.1 then v j.1 else 0 := by
      rw [← eJ.symm.sum_comp]
      exact Finset.sum_congr rfl fun k _ => by simp [S', v', y]
    rw [hsum1, Finset.sum_coe_sort J (fun j => if y ∈ S j then v j else 0)]
    have hsum2 : (∑ j ∈ J, if y ∈ S j then v j else 0) + (if y ∈ S i₀ then v i₀ else 0) =
        ∑ j : Fin m, if y ∈ S j then v j else 0 :=
      Finset.sum_erase_add Finset.univ (fun j => if y ∈ S j then v j else 0) (Finset.mem_univ i₀)
    simp only [hyU, ↓reduceIte, add_zero, h.2 y] at hsum2
    exact hsum2

lemma K_add_s_eq {s n : ℕ} (hs : 0 < s) (hn : 2 * s * s ≤ n) :
    K s (n + s) = K s n + 1 := by
  classical
  have hsn : s ≤ n := by nlinarith
  apply le_antisymm (K_add_s_le hs hsn)
  let m := K s (n + s)
  obtain ⟨S, v, hcov⟩ := K_spec hs (by omega : s ≤ n + s)
  have hm_pos : 0 < m := cov_pos_m (by omega) hcov
  have hm_ub : m ≤ (n + s) / s + 2 * s - 2 := K_le_div_add hs (by omega)
  have hdiv_le : ((n + s) / s) * s ≤ n + s := Nat.div_mul_le_self (n + s) s
  have hms_lt : m * s < 2 * (n + s) := by
    have h1 : m * s ≤ ((n + s) / s + 2 * s - 2) * s := Nat.mul_le_mul_right s hm_ub
    have h2 : ((n + s) / s + 2 * s - 2) * s + 2 * s = ((n + s) / s) * s + 2 * s * s := by
      have hge : 2 ≤ (n + s) / s + 2 * s := by omega
      have h3 := Nat.sub_add_cancel hge
      have h4 := congrArg (· * s) h3
      nlinarith
    nlinarith
  have hdouble : (∑ y : Fin (n + s), (Finset.univ.filter (fun i : Fin m => y ∈ S i)).card) =
      m * s := by
    calc
      (∑ y : Fin (n + s), (Finset.univ.filter (fun i : Fin m => y ∈ S i)).card)
        = ∑ y : Fin (n + s), ∑ i : Fin m, if y ∈ S i then 1 else 0 := by
            simp only [Finset.card_filter]
      _ = ∑ i : Fin m, ∑ y : Fin (n + s), if y ∈ S i then 1 else 0 := Finset.sum_comm
      _ = ∑ i : Fin m, (S i).card := by
            refine Finset.sum_congr rfl fun i _ => by simp
      _ = m * s := by
            simp [fun i => (hcov.1 i).1]
  have hex : ∃ y : Fin (n + s), (Finset.univ.filter (fun i : Fin m => y ∈ S i)).card < 2 := by
    by_contra hall
    push Not at hall
    have hge : 2 * (n + s) ≤ ∑ y : Fin (n + s), (Finset.univ.filter (fun i : Fin m => y ∈ S i)).card := by
      calc
        2 * (n + s) = ∑ _y : Fin (n + s), 2 := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun y _ => hall y
    omega
  obtain ⟨y₀, hy₀⟩ := hex
  have hex_i : ∃ i₀ : Fin m, y₀ ∈ S i₀ := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ i : Fin m, if y₀ ∈ S i then v i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp only [hnone i, ↓reduceIte]
    linarith [hcov.2 y₀]
  obtain ⟨i₀, hi₀⟩ := hex_i
  have huniq : ∀ j : Fin m, y₀ ∈ S j → j = i₀ := by
    intro j hj
    by_contra hne
    have hsub : ({i₀, j} : Finset (Fin m)) ⊆ Finset.univ.filter (fun i => y₀ ∈ S i) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [hi₀, hj]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hne)] at hcard
    omega
  have hv1 : v i₀ = 1 := cov_eq_one_of_unique hcov hi₀ huniq
  obtain ⟨S', v', hcov'⟩ := cov_peel_isolated hcov hv1
  have hle : K s (n + s - s) ≤ m - 1 := K_le hcov'
  rw [Nat.add_sub_cancel] at hle
  omega

lemma K_large_width {s N : ℕ} (hs : 0 < s) (hlarge : 4 * s ^ 3 ≤ N) :
    K s N = K s (2 * s * s + N % s) + (N - (2 * s * s + N % s)) / s := by
  let n₀ := 2 * s * s + N % s
  let d := (N - n₀) / s
  have hmod : N % s < s := Nat.mod_lt N hs
  have hle : n₀ ≤ N := by
    dsimp only [n₀]
    have h3 : s * s ≤ s * s * s := Nat.le_mul_of_pos_right (s * s) hs
    have hpow : s ^ 3 = s * s * s := by ring
    nlinarith
  have hdiv : N = (N / s) * s + N % s := by
    have := Nat.div_add_mod N s
    linarith [Nat.mul_comm s (N / s)]
  have hq : 2 * s ≤ N / s := by
    have : (2 * s) * s ≤ N := by
      have hpow : s ^ 3 = s * s * s := by ring
      nlinarith
    exact (Nat.le_div_iff_mul_le hs).mpr this
  have hsub : N - n₀ = (N / s - 2 * s) * s := by
    have h1 : (N / s - 2 * s) * s + 2 * s * s = (N / s) * s := by
      have := congrArg (· * s) (Nat.sub_add_cancel hq)
      nlinarith
    omega
  have hd_eq : d = N / s - 2 * s := by
    dsimp [d]
    rw [hsub, Nat.mul_div_cancel _ hs]
  have hN_eq : n₀ + d * s = N := by
    rw [hd_eq, ← hsub]
    omega
  have hind : ∀ k : ℕ, K s (n₀ + k * s) = K s n₀ + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have heq : n₀ + (k + 1) * s = (n₀ + k * s) + s := by ring
      rw [heq, K_add_s_eq hs (by dsimp [n₀]; omega), ih]
      omega
  simpa [hN_eq] using hind d

lemma short_of_large {N r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) (h4 : 4 ≤ N) (hlarge : 4 * s ^ 3 ≤ N) :
    (K s N) * (r + s - 1) < 2 * N - 1 ∧ (r = s ∨ (K s N) * r < N) := by
  have hs : 0 < s := hr.trans_le hrs
  have hsN : s ≤ N := by
    have hpow : s ^ 3 = s * s * s := by ring
    nlinarith
  have hK : K s N ≤ N / s + 2 * s - 2 := K_le_div_add hs hsN
  by_cases hs1 : s = 1
  · have hr1 : r = 1 := by omega
    subst hs1 hr1
    have hK1 : K 1 N ≤ N := by simpa using hK
    exact ⟨by omega, Or.inl rfl⟩
  · have hs2 : 2 ≤ s := by omega
    have hq : 4 * s ^ 2 ≤ N / s := by
      refine (Nat.le_div_iff_mul_le hs).mpr ?_
      have hpow : 4 * s ^ 2 * s = 4 * s ^ 3 := by ring
      omega
    have hqmul : (N / s) * s ≤ N := Nat.div_mul_le_self N s
    have hK_z : (K s N : ℤ) ≤ (N / s : ℤ) + 2 * (s : ℤ) - 2 := by omega
    have hq_z : 4 * (s : ℤ) ^ 2 ≤ (N / s : ℤ) := by exact_mod_cast hq
    have hqmul_z : (N / s : ℤ) * (s : ℤ) ≤ (N : ℤ) := by exact_mod_cast hqmul
    have hs2_z : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs2
    have hK_nn : (0 : ℤ) ≤ (K s N : ℤ) := Nat.cast_nonneg _
    constructor
    · have h1 : (K s N : ℤ) * ((r + s - 1 : ℕ) : ℤ) < 2 * (N : ℤ) - 1 := by
        have hrs1 : ((r + s - 1 : ℕ) : ℤ) ≤ 2 * (s : ℤ) - 1 := by omega
        have hmul1 : (K s N : ℤ) * ((r + s - 1 : ℕ) : ℤ) ≤ (K s N : ℤ) * (2 * (s : ℤ) - 1) :=
          mul_le_mul_of_nonneg_left hrs1 hK_nn
        have hmul2 : (K s N : ℤ) * (2 * (s : ℤ) - 1) ≤
            ((N / s : ℤ) + 2 * (s : ℤ) - 2) * (2 * (s : ℤ) - 1) :=
          mul_le_mul_of_nonneg_right hK_z (by linarith)
        nlinarith
      omega
    · by_cases hreq : r = s
      · exact Or.inl hreq
      · right
        have hr_le : (r : ℤ) ≤ (s : ℤ) - 1 := by omega
        have h1 : (K s N : ℤ) * (r : ℤ) < (N : ℤ) := by
          have hmul1 : (K s N : ℤ) * (r : ℤ) ≤ (K s N : ℤ) * ((s : ℤ) - 1) :=
            mul_le_mul_of_nonneg_left hr_le hK_nn
          have hmul2 : (K s N : ℤ) * ((s : ℤ) - 1) ≤
              ((N / s : ℤ) + 2 * (s : ℤ) - 2) * ((s : ℤ) - 1) :=
            mul_le_mul_of_nonneg_right hK_z (by linarith)
          nlinarith
        omega

lemma cov_pad {s N k M : ℕ} (hk : 0 < k) (hkm : k ≤ M)
    {S : Fin k → Finset (Fin N)} {v : Fin k → ℝ} (h : cov s N k S v) :
    ∃ S' v', cov s N M S' v' := by
  classical
  let p (i : Fin M) : Fin k := if hi : i.val < k then ⟨i.val, hi⟩ else ⟨0, hk⟩
  have hp : Function.Surjective p := fun j =>
    ⟨⟨j.val, j.isLt.trans_le hkm⟩, by simp [p, j.isLt]⟩
  let m (j : Fin k) : ℕ := (Finset.univ.filter (fun i : Fin M => p i = j)).card
  have hm (j : Fin k) : (0 : ℝ) < (m j : ℝ) := by
    obtain ⟨i, hi⟩ := hp j
    exact_mod_cast (Finset.card_pos.mpr ⟨i, by simp [hi]⟩ : 0 < m j)
  let S' (i : Fin M) : Finset (Fin N) := S (p i)
  let v' (i : Fin M) : ℝ := v (p i) / (m (p i) : ℝ)
  refine ⟨S', v', ⟨fun i => ⟨(h.1 (p i)).1, div_pos (h.1 (p i)).2 (hm (p i))⟩, fun y => ?_⟩⟩
  change (∑ i : Fin M, (fun j => if y ∈ S j then v j / (m j : ℝ) else 0) (p i)) = 1
  rw [← Finset.sum_fiberwise' Finset.univ p (fun j => if y ∈ S j then v j / (m j : ℝ) else 0)]
  calc
    (∑ j : Fin k, ∑ _i ∈ Finset.univ.filter (fun i : Fin M => p i = j),
        if y ∈ S j then v j / (m j : ℝ) else 0)
      = ∑ j : Fin k, if y ∈ S j then v j else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          by_cases hy : y ∈ S j
          · simp [hy, m, mul_div_cancel₀ _ (hm j).ne']
          · simp [hy]
    _ = 1 := h.2 y

lemma cov_half_rem_three {h : ℕ} (hh : 0 < h) :
    ∃ S v, cov (2 * h) (3 * h) 3 S v := by
  classical
  let S0 : Finset (Fin (3 * h)) := Finset.univ.filter (fun y => y.val < 2 * h)
  let S1 : Finset (Fin (3 * h)) := Finset.univ.filter (fun y => h ≤ y.val)
  let S2 : Finset (Fin (3 * h)) := Finset.univ.filter (fun y => y.val < h ∨ 2 * h ≤ y.val)
  let S : Fin 3 → Finset (Fin (3 * h)) := fun i =>
    match i with
    | ⟨0, _⟩ => S0
    | ⟨1, _⟩ => S1
    | ⟨2, _⟩ => S2
  let v : Fin 3 → ℝ := fun _ => (1 : ℝ) / 2
  have hS0 : S0.card = 2 * h := by
    let e : Fin (2 * h) ↪ Fin (3 * h) :=
      ⟨fun i => ⟨i.val, by omega⟩, fun a b hx => by
        cases a; cases b; simp only [Fin.mk.injEq] at hx ⊢; exact hx⟩
    have he : S0 = Finset.univ.map e := by
      ext y
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hy; exact ⟨⟨y.val, hy⟩, Fin.ext rfl⟩
      · rintro ⟨i, rfl⟩; exact i.isLt
    rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hS1 : S1.card = 2 * h := by
    let e : Fin (2 * h) ↪ Fin (3 * h) :=
      ⟨fun i => ⟨h + i.val, by omega⟩, fun a b hx => by
        cases a; cases b; simp only [Fin.mk.injEq] at hx ⊢; omega⟩
    have he : S1 = Finset.univ.map e := by
      ext y
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hy
        refine ⟨⟨y.val - h, by omega⟩, Fin.ext ?_⟩
        change h + (y.val - h) = y.val
        omega
      · rintro ⟨i, rfl⟩
        change h ≤ h + i.val
        omega
    rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hS2 : S2.card = 2 * h := by
    let e : Fin h ↪ Fin (3 * h) :=
      ⟨fun i => ⟨h + i.val, by omega⟩, fun a b hx => by
        cases a; cases b; simp only [Fin.mk.injEq] at hx ⊢; omega⟩
    have he : S2ᶜ = Finset.univ.map e := by
      ext y
      simp only [S2, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, not_or, not_lt, not_le]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨y.val - h, by omega⟩, Fin.ext ?_⟩
        change h + (y.val - h) = y.val
        omega
      · rintro ⟨i, rfl⟩
        change h ≤ h + i.val ∧ h + i.val < 2 * h
        omega
    have hc := Finset.card_add_card_compl S2
    rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at hc
    omega
  refine ⟨S, v, ⟨fun i => ⟨?_, by norm_num [v]⟩, fun y => ?_⟩⟩
  · fin_cases i
    · exact hS0
    · exact hS1
    · exact hS2
  · rw [Fin.sum_univ_three]
    change (if y ∈ S0 then (1 : ℝ) / 2 else 0) + (if y ∈ S1 then (1 : ℝ) / 2 else 0) +
      (if y ∈ S2 then (1 : ℝ) / 2 else 0) = 1
    simp only [S0, S1, S2, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> first | (norm_num; done) | omega

lemma half_rem_analyze {s N q m : ℕ} (hs : 0 < s) (hq : 0 < q) (heven : Even s)
    (hN : N = q * s + s / 2) {S : Fin m → Finset (Fin N)} {v : Fin m → ℝ}
    (hcov : cov s N m S v) (hm : m ≤ q + 2) :
    m = q + 2 ∧ (Finset.univ.filter (fun i : Fin m => v i < 1)).card = 3 ∧
      ∀ i : Fin m, v i = 1 ∨ 2 * v i = 1 := by
  classical
  obtain ⟨h, hsh⟩ := heven
  have hs2h : s = 2 * h := by omega
  have hdiv : s / 2 = h := by omega
  have hh : 0 < h := by omega
  let I : Finset (Fin m) := Finset.univ.filter (fun i => v i = 1)
  let J : Finset (Fin m) := Finset.univ.filter (fun i => v i < 1)
  have hIJ_disj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    linarith
  have hIJ_union : I ∪ J = Finset.univ := by
    ext i
    simp only [I, J, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact eq_or_lt_of_le (cov_v_le_one hs hcov i)
  have hIJ_card : I.card + J.card = m := by
    rw [← Finset.card_union_of_disjoint hIJ_disj, hIJ_union, Finset.card_univ, Fintype.card_fin]
  let W : Finset (Fin N) := I.biUnion S
  have hW_card : W.card = I.card * s := by
    rw [Finset.card_biUnion]
    · simp [fun i => (hcov.1 i).1]
    · intro i₁ hi₁ i₂ hi₂ hne
      exact cov_disjoint_of_eq_one hcov (Finset.mem_filter.mp hi₁).2 (Ne.symm hne)
  have hW_le : W.card ≤ N := by simpa using W.card_le_univ
  have hI_le : I.card ≤ q := by
    have : I.card * s < (q + 1) * s := by
      rw [← hW_card]
      have : (q + 1) * s = q * s + s := by ring
      omega
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right this)
  let U : Finset (Fin N) := Wᶜ
  have hU_card : U.card = (q - I.card) * s + h := by
    dsimp only [U]
    have hc := Finset.card_add_card_compl W
    rw [hW_card, Fintype.card_fin] at hc
    have hsub : (q - I.card) * s + I.card * s = q * s := by
      have := congrArg (· * s) (Nat.sub_add_cancel hI_le)
      nlinarith
    omega
  have hsubU : ∀ j ∈ J, S j ⊆ U := by
    intro j hj y hy
    rw [Finset.mem_compl]
    intro hyW
    obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hyW
    have hji : j ≠ i := fun heq => by
      have h1 := (Finset.mem_filter.mp hi).2
      have h2 := (Finset.mem_filter.mp hj).2
      rw [heq] at h2
      linarith
    exact Finset.disjoint_left.mp
      (cov_disjoint_of_eq_one hcov (Finset.mem_filter.mp hi).2 hji) hyi hy
  have hsumJ : ∀ y ∈ U, (∑ j ∈ J, if y ∈ S j then v j else 0) = 1 := by
    intro y hyU
    have hyW : y ∉ W := Finset.mem_compl.mp hyU
    have h1 := hcov.2 y
    rw [← hIJ_union, Finset.sum_union hIJ_disj] at h1
    have hI0 : (∑ i ∈ I, if y ∈ S i then v i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hyi : y ∉ S i := fun hm => hyW (Finset.mem_biUnion.mpr ⟨i, hi, hm⟩)
        simp only [hyi, ↓reduceIte]
    rw [hI0, zero_add] at h1
    exact h1
  have hdeg_ge : ∀ y ∈ U, 2 ≤ (J.filter (fun j => y ∈ S j)).card := by
    intro y hyU
    by_contra hlt
    push Not at hlt
    have hcases : (J.filter (fun j => y ∈ S j)).card = 0 ∨
        (J.filter (fun j => y ∈ S j)).card = 1 := by omega
    rcases hcases with h0 | h1
    · have hempty : J.filter (fun j => y ∈ S j) = ∅ := Finset.card_eq_zero.mp h0
      have hz : (∑ j ∈ J, if y ∈ S j then v j else 0) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          have hyj : y ∉ S j := fun hm => by
            have : j ∈ J.filter (fun k => y ∈ S k) := Finset.mem_filter.mpr ⟨hj, hm⟩
            rw [hempty] at this
            exact Finset.notMem_empty _ this
          simp only [hyj, ↓reduceIte]
      linarith [hsumJ y hyU]
    · obtain ⟨j₀, hj₀eq⟩ := Finset.card_eq_one.mp h1
      have hj₀mem : j₀ ∈ J.filter (fun j => y ∈ S j) := by rw [hj₀eq]; simp
      obtain ⟨hj₀J, hyj₀⟩ := Finset.mem_filter.mp hj₀mem
      have hsj := hsumJ y hyU
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hj₀eq, Finset.sum_singleton] at hsj
      linarith [(Finset.mem_filter.mp hj₀J).2]
  have hdouble : (∑ y ∈ U, (J.filter (fun j => y ∈ S j)).card) = J.card * s := by
    calc
      (∑ y ∈ U, (J.filter (fun j => y ∈ S j)).card)
        = ∑ y ∈ U, ∑ j ∈ J, if y ∈ S j then 1 else 0 := by
            refine Finset.sum_congr rfl fun y _ => by simp only [Finset.card_filter]
      _ = ∑ j ∈ J, ∑ y ∈ U, if y ∈ S j then 1 else 0 := Finset.sum_comm
      _ = ∑ j ∈ J, (U.filter (fun y => y ∈ S j)).card := by
            refine Finset.sum_congr rfl fun j _ => by simp only [Finset.card_filter]
      _ = ∑ j ∈ J, (S j).card := by
            refine Finset.sum_congr rfl fun j hj => ?_
            congr 1
            ext y
            simp only [Finset.mem_filter, and_iff_right_iff_imp]
            exact fun hy => hsubU j hj hy
      _ = J.card * s := by
            simp [fun j => (hcov.1 j).1]
  have hsum_ge : 2 * U.card ≤ J.card * s := by
    rw [← hdouble]
    calc
      2 * U.card = ∑ _y ∈ U, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ U, (J.filter (fun j => y ∈ S j)).card := Finset.sum_le_sum hdeg_ge
  have h2U : 2 * U.card = (2 * (q - I.card) + 1) * s := by
    rw [hU_card]
    nlinarith
  have hJ_ge : 2 * (q - I.card) + 1 ≤ J.card :=
    Nat.le_of_mul_le_mul_right (by omega : (2 * (q - I.card) + 1) * s ≤ J.card * s) hs
  have hk_ne0 : q - I.card ≠ 0 := by
    intro hk0
    have hUh : U.card = h := by rw [hU_card, hk0]; simp
    obtain ⟨y, hyU⟩ := Finset.card_pos.mp (by rw [hUh]; exact hh)
    have hdeg := hdeg_ge y hyU
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun k => y ∈ S k)).card)
    have hjJ := (Finset.mem_filter.mp hj).1
    have hle := Finset.card_le_card (hsubU j hjJ)
    rw [(hcov.1 j).1, hUh] at hle
    omega
  have hm_eq : m = q + 2 := by omega
  have hk_eq : q - I.card = 1 := by omega
  have hJ_card : J.card = 3 := by omega
  have hU3h : U.card = 3 * h := by rw [hU_card, hk_eq]; omega
  have hdeg_eq : ∀ y ∈ U, (J.filter (fun j => y ∈ S j)).card = 2 := by
    have hsum_eq : (∑ _y ∈ U, 2) = ∑ y ∈ U, (J.filter (fun j => y ∈ S j)).card := by
      rw [hdouble, Finset.sum_const, smul_eq_mul, hU3h, hJ_card]
      omega
    intro y hyU
    exact ((Finset.sum_eq_sum_iff_of_le hdeg_ge).mp hsum_eq y hyU).symm
  obtain ⟨j₁, j₂, j₃, h12, h13, h23, hJeq⟩ := Finset.card_eq_three.mp hJ_card
  have hpair : ∀ {a b c : Fin m}, a ≠ b → a ≠ c → b ≠ c → J = {a, b, c} → v a + v b = 1 := by
    intro a b c hab hac hbc hJabc
    have hcJ : c ∈ J := by rw [hJabc]; simp
    have hdiff_pos : 0 < (U \ S c).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hsubU c hcJ), hU3h, (hcov.1 c).1]
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hdiff_pos
    obtain ⟨hyU, hync⟩ := Finset.mem_sdiff.mp hy
    have hfilt_sub : J.filter (fun j => y ∈ S j) ⊆ {a, b} := by
      intro k hk
      obtain ⟨hkJ, hyk⟩ := Finset.mem_filter.mp hk
      rw [hJabc] at hkJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkJ ⊢
      rcases hkJ with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hyk hync
    have hfilt_eq : J.filter (fun j => y ∈ S j) = {a, b} :=
      Finset.eq_of_subset_of_card_le hfilt_sub (by rw [Finset.card_pair hab, hdeg_eq y hyU])
    have hsj := hsumJ y hyU
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfilt_eq, Finset.sum_pair hab] at hsj
    exact hsj
  have hp12 : v j₁ + v j₂ = 1 := hpair h12 h13 h23 hJeq
  have hp23 : v j₂ + v j₃ = 1 := hpair h23 h12.symm h13.symm (by
    rw [hJeq]; ext k; simp [or_comm, or_left_comm])
  have hp31 : v j₃ + v j₁ = 1 := hpair h13.symm h23.symm h12 (by
    rw [hJeq]; ext k; simp [or_comm, or_left_comm])
  refine ⟨hm_eq, hJ_card, fun i => ?_⟩
  by_cases hi : v i = 1
  · exact Or.inl hi
  · right
    have hiJ : i ∈ J := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_le_of_ne (cov_v_le_one hs hcov i) hi⟩
    rw [hJeq] at hiJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiJ
    rcases hiJ with rfl | rfl | rfl <;> linarith

lemma half_rem_K {s N q : ℕ} (hs : 0 < s) (hq : 0 < q) (heven : Even s)
    (hN : N = q * s + s / 2) : K s N = q + 2 := by
  obtain ⟨h, hsh⟩ := heven
  have hs2h : s = 2 * h := by omega
  have hdiv : s / 2 = h := by omega
  have hh : 0 < h := by omega
  have hN3 : N = 3 * h + (q - 1) * s := by
    have : (q - 1) * s + s = q * s := by
      cases q with
      | zero => omega
      | succ k => simp [Nat.add_mul]
    omega
  have hub : K s N ≤ q + 2 := by
    obtain ⟨S0, v0, h0⟩ := cov_half_rem_three hh
    have hK3 : K s (3 * h) ≤ 3 := by
      rw [hs2h]
      exact K_le h0
    have hstep := K_add_mul_s_le hs (by omega : s ≤ 3 * h) (q - 1)
    rw [← hN3] at hstep
    omega
  obtain ⟨S, v, hcov⟩ := K_spec hs (by omega : s ≤ N)
  exact (half_rem_analyze hs hq ⟨h, hsh⟩ hN hcov hub).1

end Cover

open scoped BigOperators

namespace Shore

variable {N M r s : ℕ}

noncomputable def weightedIntersection (A B : Fin M → Finset (Fin N)) (w : Fin M → ℝ)
    (x y : Fin N) : ℝ :=
  ∑ i, if x ∈ A i ∧ y ∈ B i then w i else 0

def Additive (F : Fin N → Fin N → ℝ) : Prop :=
  ∀ x x' y y', F x y + F x' y' = F x y' + F x' y

private lemma index_nonempty {w : Fin M → ℝ} (hsum : ∑ i, w i = 1) : Nonempty (Fin M) := by
  classical
  by_contra hn
  let _ : IsEmpty (Fin M) := ⟨fun i => hn ⟨i⟩⟩
  simp at hsum

private lemma transpose_value (A B : Fin M → Finset (Fin N)) (w : Fin M → ℝ)
    (x y : Fin N) : weightedIntersection B A w x y = weightedIntersection A B w y x := by
  unfold weightedIntersection
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : x ∈ B i <;> by_cases hy : y ∈ A i <;> simp [hx, hy]

private lemma additive_transpose {A B : Fin M → Finset (Fin N)} {w : Fin M → ℝ}
    (h : Additive (weightedIntersection A B w)) :
    Additive (weightedIntersection B A w) := by
  intro x x' y y'
  simp only [transpose_value A B w]
  rw [add_comm (weightedIntersection A B w y' x) (weightedIntersection A B w y x')]
  exact h y y' x x'

private lemma weightedIntersection_nonneg {A B : Fin M → Finset (Fin N)} {w : Fin M → ℝ}
    (hw : ∀ i, 0 < w i) (x y : Fin N) : 0 ≤ weightedIntersection A B w x y :=
  Finset.sum_nonneg fun i _ => by split_ifs; exact (hw i).le; exact le_rfl

private lemma no_full_row_and_col {A B : Fin M → Finset (Fin N)} {w : Fin M → ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hN : 0 < N)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hcross : M * (r + s - 1) < 2 * N - 1) :
    ¬ ((∃ x₀, ∀ y, 0 < weightedIntersection A B w x₀ y) ∧
       (∃ y₀, ∀ x, 0 < weightedIntersection A B w x y₀)) := by
  classical
  rintro ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  let C : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => z.1 = x₀ ∨ z.2 = y₀)
  have hC_card : C.card = 2 * N - 1 := by
    have h1 : C = ({x₀} ×ˢ (Finset.univ : Finset (Fin N))) ∪
        ((Finset.univ : Finset (Fin N)) ×ˢ {y₀}) := by
      ext ⟨x, y⟩
      simp [C, eq_comm]
    have h2 : ({x₀} ×ˢ (Finset.univ : Finset (Fin N))) ∩
        ((Finset.univ : Finset (Fin N)) ×ˢ {y₀}) = {(x₀, y₀)} := by
      ext ⟨x, y⟩
      simp [eq_comm]
    have hc := Finset.card_union_add_card_inter
      ({x₀} ×ˢ (Finset.univ : Finset (Fin N))) ((Finset.univ : Finset (Fin N)) ×ˢ {y₀})
    rw [← h1, h2] at hc
    simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      one_mul, mul_one] at hc
    omega
  have hcov : C ⊆ Finset.univ.biUnion (fun i : Fin M => (A i ×ˢ B i) ∩ C) := by
    intro z hz
    have hpos : 0 < weightedIntersection A B w z.1 z.2 := by
      rcases (Finset.mem_filter.mp hz).2 with hx | hy
      · rw [hx]; exact hx₀ z.2
      · rw [hy]; exact hy₀ z.1
    have hex : ∃ i : Fin M, z.1 ∈ A i ∧ z.2 ∈ B i := by
      by_contra hnone
      push Not at hnone
      have h0 : weightedIntersection A B w z.1 z.2 = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have hni : ¬ (z.1 ∈ A i ∧ z.2 ∈ B i) := fun h => hnone i h.1 h.2
          simp only [hni, ↓reduceIte]
      linarith
    obtain ⟨i, hza, hzb⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr
      ⟨Finset.mem_product.mpr ⟨hza, hzb⟩, hz⟩⟩
  have hrect : ∀ i : Fin M, ((A i ×ˢ B i) ∩ C).card ≤ r + s - 1 := by
    intro i
    have hsumAB : (A i).card + (B i).card = r + s := by
      rcases hsizes i with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    have hleA : (A i).card ≤ s := by rcases hsizes i with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega
    have hleB : (B i).card ≤ s := by rcases hsizes i with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega
    by_cases hxa : x₀ ∈ A i
    · by_cases hyb : y₀ ∈ B i
      · have hsub : (A i ×ˢ B i) ∩ C ⊆ ({x₀} ×ˢ B i) ∪ (A i ×ˢ {y₀}) := by
          intro z hz
          obtain ⟨hzab, hzc⟩ := Finset.mem_inter.mp hz
          obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hzab
          rcases (Finset.mem_filter.mp hzc).2 with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨by simp [h1], hzb⟩)
          · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hza, by simp [h2]⟩)
        have hinter : ({x₀} ×ˢ B i) ∩ (A i ×ˢ {y₀}) = {(x₀, y₀)} := by
          ext ⟨x, y⟩
          simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨rfl, _⟩, ⟨_, rfl⟩⟩; exact ⟨rfl, rfl⟩
          · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, hyb⟩, ⟨hxa, rfl⟩⟩
        have hc := Finset.card_union_add_card_inter ({x₀} ×ˢ B i) (A i ×ˢ {y₀})
        rw [hinter] at hc
        simp only [Finset.card_product, Finset.card_singleton, one_mul, mul_one] at hc
        have hle := Finset.card_le_card hsub
        omega
      · have hsub : (A i ×ˢ B i) ∩ C ⊆ {x₀} ×ˢ B i := by
          intro z hz
          obtain ⟨hzab, hzc⟩ := Finset.mem_inter.mp hz
          obtain ⟨_, hzb⟩ := Finset.mem_product.mp hzab
          rcases (Finset.mem_filter.mp hzc).2 with h1 | h2
          · exact Finset.mem_product.mpr ⟨by simp [h1], hzb⟩
          · exact absurd (h2 ▸ hzb) hyb
        have hle := Finset.card_le_card hsub
        rw [Finset.card_product, Finset.card_singleton, one_mul] at hle
        omega
    · by_cases hyb : y₀ ∈ B i
      · have hsub : (A i ×ˢ B i) ∩ C ⊆ A i ×ˢ {y₀} := by
          intro z hz
          obtain ⟨hzab, hzc⟩ := Finset.mem_inter.mp hz
          obtain ⟨hza, _⟩ := Finset.mem_product.mp hzab
          rcases (Finset.mem_filter.mp hzc).2 with h1 | h2
          · exact absurd (h1 ▸ hza) hxa
          · exact Finset.mem_product.mpr ⟨hza, by simp [h2]⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_product, Finset.card_singleton, mul_one] at hle
        omega
      · have hempty : (A i ×ˢ B i) ∩ C = ∅ := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_product, C, Finset.mem_filter,
            Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
          rintro ⟨hza, hzb⟩ (h1 | h2)
          · exact hxa (h1 ▸ hza)
          · exact hyb (h2 ▸ hzb)
        rw [hempty, Finset.card_empty]
        omega
  have hle : C.card ≤ M * (r + s - 1) := by
    calc
      C.card ≤ (Finset.univ.biUnion (fun i : Fin M => (A i ×ˢ B i) ∩ C)).card :=
        Finset.card_le_card hcov
      _ ≤ ∑ i : Fin M, ((A i ×ˢ B i) ∩ C).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin M, (r + s - 1) := Finset.sum_le_sum fun i _ => hrect i
      _ = M * (r + s - 1) := by simp
  omega

private lemma const_along_rows_of_no_full_col {F : Fin N → Fin N → ℝ}
    (hnn : ∀ x y, 0 ≤ F x y) (hadd : Additive F) (hcol : ∀ y, ∃ x, F x y = 0) :
    ∀ x y₁ y₂, F x y₁ = F x y₂ := by
  intro x y₁ y₂
  obtain ⟨x₁, hx₁⟩ := hcol y₁
  obtain ⟨x₂, hx₂⟩ := hcol y₂
  have h1 := hadd x₁ x₂ y₁ y₂
  have hx₁₂ : F x₁ y₂ = 0 := by linarith [hnn x₁ y₂, hnn x₂ y₁]
  have h2 := hadd x x₁ y₁ y₂
  linarith

private lemma oriented_structure {A B : Fin M → Finset (Fin N)} {w : Fin M → ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hN : 0 < N)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hratio : r = s ∨ M * r < N)
    (hconst : ∀ x y₁ y₂, weightedIntersection A B w x y₁ = weightedIntersection A B w x y₂) :
    Cover.K s N ≤ M ∧
    (M = Cover.K s N → ∃ R : Finset (Fin N), R.card = r ∧
      Cover.cov s N M B (fun i => (N : ℝ) * w i / (s : ℝ)) ∧ ∀ i, A i = R) := by
  classical
  let y₀ : Fin N := ⟨0, hN⟩
  let c (x : Fin N) : ℝ := weightedIntersection A B w x y₀
  have hF (x y : Fin N) : weightedIntersection A B w x y = c x := hconst x y y₀
  let P : Finset (Fin N) := Finset.univ.filter (fun x => 0 < c x)
  have hsubP : ∀ i : Fin M, A i ⊆ P := by
    intro i x hx
    have hBne : (B i).Nonempty := Finset.card_pos.mp (by rcases hsizes i with ⟨_, hb⟩ | ⟨_, hb⟩ <;> omega)
    obtain ⟨y, hy⟩ := hBne
    have hpos : 0 < weightedIntersection A B w x y := by
      unfold weightedIntersection
      refine Finset.sum_pos' (fun j _ => by split_ifs; exact (hw j).le; exact le_rfl)
        ⟨i, Finset.mem_univ _, by simp [hx, hy, hw i]⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hF] at hpos⟩
  obtain ⟨i₀⟩ := index_nonempty hsum
  have hPne : P.Nonempty := by
    have hAne : (A i₀).Nonempty := Finset.card_pos.mp (by rcases hsizes i₀ with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega)
    obtain ⟨x, hx⟩ := hAne
    exact ⟨x, hsubP i₀ hx⟩
  have hrow_cov : ∀ x ∈ P, N ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin M => x ∈ A i), (B i).card := by
    intro x hxP
    have hcx : 0 < c x := (Finset.mem_filter.mp hxP).2
    have hcov_y : (Finset.univ : Finset (Fin N)) ⊆
        (Finset.univ.filter (fun i : Fin M => x ∈ A i)).biUnion B := by
      intro y _
      have hpos : 0 < weightedIntersection A B w x y := by rw [hF]; exact hcx
      have hex : ∃ i : Fin M, x ∈ A i ∧ y ∈ B i := by
        by_contra hnone
        push Not at hnone
        have h0 : weightedIntersection A B w x y = 0 :=
          Finset.sum_eq_zero fun i _ => by
            have hni : ¬ (x ∈ A i ∧ y ∈ B i) := fun h => hnone i h.1 h.2
            simp only [hni, ↓reduceIte]
        linarith
      obtain ⟨i, hxi, hyi⟩ := hex
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, hyi⟩
    calc
      N = (Finset.univ : Finset (Fin N)).card := by simp
      _ ≤ ((Finset.univ.filter (fun i : Fin M => x ∈ A i)).biUnion B).card :=
        Finset.card_le_card hcov_y
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin M => x ∈ A i), (B i).card :=
        Finset.card_biUnion_le
  have hPN : P.card * N ≤ M * (r * s) := by
    calc
      P.card * N = ∑ _x ∈ P, N := by simp
      _ ≤ ∑ x ∈ P, ∑ i ∈ Finset.univ.filter (fun i : Fin M => x ∈ A i), (B i).card :=
          Finset.sum_le_sum hrow_cov
      _ = ∑ x ∈ P, ∑ i : Fin M, if x ∈ A i then (B i).card else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      _ = ∑ i : Fin M, ∑ x ∈ P, if x ∈ A i then (B i).card else 0 := Finset.sum_comm
      _ = ∑ i : Fin M, (A i).card * (B i).card := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
          congr 1
          have hfilt : P.filter (fun x => x ∈ A i) = A i := by
            ext x
            simp only [Finset.mem_filter, and_iff_right_iff_imp]
            exact fun hx => hsubP i hx
          rw [hfilt]
      _ = ∑ _i : Fin M, r * s := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases hsizes i with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [ha, hb]
          · rw [ha, hb, Nat.mul_comm]
      _ = M * (r * s) := by simp
  have hAB : ∀ i : Fin M, (A i).card = r ∧ (B i).card = s := by
    intro i
    rcases hratio with hreq | hMr
    · subst hreq
      rcases hsizes i with h | h <;> exact h
    · have hPs : P.card < s := by
        have h1 : P.card * N < s * N := by
          calc
            P.card * N ≤ M * (r * s) := hPN
            _ = (M * r) * s := by ring
            _ < N * s := Nat.mul_lt_mul_of_pos_right hMr (hr.trans_le hrs)
            _ = s * N := Nat.mul_comm N s
        exact Nat.lt_of_mul_lt_mul_right h1
      have hAle : (A i).card ≤ P.card := Finset.card_le_card (hsubP i)
      rcases hsizes i with h | ⟨ha, _⟩
      · exact h
      · omega
  have hK_le_inc : ∀ x ∈ P, Cover.K s N ≤ (Finset.univ.filter (fun i : Fin M => x ∈ A i)).card := by
    intro x hxP
    have hcx : 0 < c x := (Finset.mem_filter.mp hxP).2
    let Ix := Finset.univ.filter (fun i : Fin M => x ∈ A i)
    let eI : {i : Fin M // i ∈ Ix} ≃ Fin Ix.card :=
      Fintype.equivFinOfCardEq (Fintype.card_coe Ix)
    let S' : Fin Ix.card → Finset (Fin N) := fun k => B (eI.symm k).1
    let v' : Fin Ix.card → ℝ := fun k => w (eI.symm k).1 / c x
    have hcovx : Cover.cov s N Ix.card S' v' := by
      refine ⟨fun k => ⟨(hAB _).2, div_pos (hw _) hcx⟩, fun y => ?_⟩
      have h1 : (∑ k : Fin Ix.card, if y ∈ S' k then v' k else 0) =
          ∑ i : {i : Fin M // i ∈ Ix}, if y ∈ B i.1 then w i.1 / c x else 0 := by
        rw [← eI.symm.sum_comp]
      rw [h1, Finset.sum_coe_sort Ix (fun i => if y ∈ B i then w i / c x else 0)]
      have h2 : (∑ i ∈ Ix, if y ∈ B i then w i / c x else 0) =
          (∑ i ∈ Ix, if y ∈ B i then w i else 0) / c x := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp [div_eq_mul_inv]
      rw [h2]
      have h3 : (∑ i ∈ Ix, if y ∈ B i then w i else 0) = weightedIntersection A B w x y := by
        unfold weightedIntersection
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ => by
          by_cases hx : x ∈ A i <;> by_cases hy : y ∈ B i <;> simp [hx, hy]
      rw [h3, hF, div_self hcx.ne']
    exact Cover.K_le hcovx
  obtain ⟨x₁, hx₁⟩ := hPne
  have hKM : Cover.K s N ≤ M :=
    (hK_le_inc x₁ hx₁).trans (by simpa using (Finset.univ.filter (fun i : Fin M => x₁ ∈ A i)).card_le_univ)
  refine ⟨hKM, fun hMeq => ?_⟩
  have hmemA : ∀ x ∈ P, ∀ i : Fin M, x ∈ A i := by
    intro x hxP i
    let Ix := Finset.univ.filter (fun j : Fin M => x ∈ A j)
    have hge : M ≤ Ix.card := le_trans hMeq.le (hK_le_inc x hxP)
    have heq : Ix = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hge)
    have hi : i ∈ Ix := by rw [heq]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  have hAeqP : ∀ i : Fin M, A i = P := fun i =>
    Finset.Subset.antisymm (hsubP i) fun x hxP => hmemA x hxP i
  have hPcard : P.card = r := by rw [← hAeqP i₀, (hAB i₀).1]
  have hc_val : c x₁ = (s : ℝ) / (N : ℝ) := by
    have hsum_y : (N : ℝ) * c x₁ = (s : ℝ) := by
      calc
        (N : ℝ) * c x₁ = ∑ _y : Fin N, c x₁ := by simp
        _ = ∑ y : Fin N, weightedIntersection A B w x₁ y :=
            Finset.sum_congr rfl fun y _ => (hF x₁ y).symm
        _ = ∑ y : Fin N, ∑ i : Fin M, if y ∈ B i then w i else 0 := by
            refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
            simp [hmemA x₁ hx₁ i]
        _ = ∑ i : Fin M, ∑ y : Fin N, if y ∈ B i then w i else 0 := Finset.sum_comm
        _ = ∑ i : Fin M, ((B i).card : ℝ) * w i := by
            refine Finset.sum_congr rfl fun i _ => by simp
        _ = ∑ i : Fin M, (s : ℝ) * w i := Finset.sum_congr rfl fun i _ => by rw [(hAB i).2]
        _ = (s : ℝ) := by rw [← Finset.mul_sum, hsum, mul_one]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    exact (eq_div_iff hNR).mpr (by linarith)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (hr.trans_le hrs)
  refine ⟨P, hPcard, ⟨fun i => ⟨(hAB i).2, div_pos (mul_pos hNR (hw i)) hsR⟩, fun y => ?_⟩, hAeqP⟩
  have hFy : (∑ i : Fin M, if y ∈ B i then w i else 0) = (s : ℝ) / (N : ℝ) := by
    calc
      (∑ i : Fin M, if y ∈ B i then w i else 0)
        = weightedIntersection A B w x₁ y :=
            Finset.sum_congr rfl fun i _ => by simp [hmemA x₁ hx₁ i]
      _ = c x₁ := hF x₁ y
      _ = (s : ℝ) / (N : ℝ) := hc_val
  calc
    (∑ i : Fin M, if y ∈ B i then (N : ℝ) * w i / (s : ℝ) else 0)
      = ((N : ℝ) / (s : ℝ)) * (∑ i : Fin M, if y ∈ B i then w i else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs
          · ring
          · simp
    _ = ((N : ℝ) / (s : ℝ)) * ((s : ℝ) / (N : ℝ)) := by rw [hFy]
    _ = 1 := by field_simp [hNR.ne', hsR.ne']

theorem structure_main {A B : Fin M → Finset (Fin N)} {w : Fin M → ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hN : 0 < N)
    (hsizes : ∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hadd : Additive (weightedIntersection A B w))
    (hcross : M * (r + s - 1) < 2 * N - 1) (hratio : r = s ∨ M * r < N) :
    Cover.K s N ≤ M ∧
    (M = Cover.K s N → ∃ (sw : Bool) (R : Finset (Fin N)) (S : Fin M → Finset (Fin N)),
      R.card = r ∧ Cover.cov s N M S (fun i => (N : ℝ) * w i / (s : ℝ)) ∧
      ∀ i, (if sw then B i else A i) = R ∧ (if sw then A i else B i) = S i) := by
  have hno := no_full_row_and_col (w := w) hr hrs hN hsizes hcross
  have hnn := weightedIntersection_nonneg (A := A) (B := B) hw
  by_cases hcol : ∀ y, ∃ x, weightedIntersection A B w x y = 0
  · have hconst := const_along_rows_of_no_full_col hnn hadd hcol
    obtain ⟨hKM, hstruct⟩ := oriented_structure hr hrs hN hsizes hw hsum hratio hconst
    refine ⟨hKM, fun hMeq => ?_⟩
    obtain ⟨R, hR, hcov, hAeq⟩ := hstruct hMeq
    exact ⟨false, R, B, hR, hcov, fun i => ⟨hAeq i, rfl⟩⟩
  · have hrow : ∀ x, ∃ y, weightedIntersection B A w y x = 0 := by
      have hex : ∃ y₀, ∀ x, 0 < weightedIntersection A B w x y₀ := by
        push Not at hcol
        obtain ⟨y₀, hy₀⟩ := hcol
        exact ⟨y₀, fun x => lt_of_le_of_ne (hnn x y₀) (Ne.symm (hy₀ x))⟩
      have hnorow : ¬ ∃ x₀, ∀ y, 0 < weightedIntersection A B w x₀ y := fun h => hno ⟨h, hex⟩
      push Not at hnorow
      intro x
      obtain ⟨y, hy⟩ := hnorow x
      exact ⟨y, by rw [transpose_value]; exact le_antisymm hy (hnn x y)⟩
    have hsizes' : ∀ i, ((B i).card = r ∧ (A i).card = s) ∨ ((B i).card = s ∧ (A i).card = r) :=
      fun i => (hsizes i).symm.imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
    have hconst' := const_along_rows_of_no_full_col
      (weightedIntersection_nonneg (A := B) (B := A) hw) (additive_transpose hadd) hrow
    obtain ⟨hKM, hstruct⟩ := oriented_structure hr hrs hN hsizes' hw hsum hratio hconst'
    refine ⟨hKM, fun hMeq => ?_⟩
    obtain ⟨R, hR, hcov, hBeq⟩ := hstruct hMeq
    exact ⟨true, R, A, hR, hcov, fun i => ⟨hBeq i, rfl⟩⟩

theorem additive_of_shore {R : Finset (Fin N)} {S : Fin M → Finset (Fin N)} {w : Fin M → ℝ}
    (hs : 0 < s) (hN : 0 < N) (sw : Bool)
    (hcov : Cover.cov s N M S (fun i => (N : ℝ) * w i / (s : ℝ))) :
    Additive (weightedIntersection (fun i => if sw then S i else R)
      (fun i => if sw then R else S i) w) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hSw : ∀ y : Fin N, (∑ i : Fin M, if y ∈ S i then w i else 0) = (s : ℝ) / (N : ℝ) := by
    intro y
    have h1 := hcov.2 y
    have h2 : (∑ i : Fin M, if y ∈ S i then (N : ℝ) * w i / (s : ℝ) else 0) =
        ((N : ℝ) / (s : ℝ)) * (∑ i : Fin M, if y ∈ S i then w i else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    rw [h2] at h1
    have h3 := congrArg (((s : ℝ) / (N : ℝ)) * ·) h1
    field_simp [hNR, hsR] at h3 ⊢
    linarith
  cases sw with
  | false =>
    change Additive (weightedIntersection (fun _ => R) S w)
    have hval (x y : Fin N) :
        weightedIntersection (fun _ => R) S w x y = if x ∈ R then (s : ℝ) / (N : ℝ) else 0 := by
      unfold weightedIntersection
      by_cases hx : x ∈ R
      · simp [hx, hSw y]
      · simp [hx]
    intro x x' y y'
    simp only [hval]
  | true =>
    change Additive (weightedIntersection S (fun _ => R) w)
    have hval (x y : Fin N) :
        weightedIntersection S (fun _ => R) w x y = if y ∈ R then (s : ℝ) / (N : ℝ) else 0 := by
      unfold weightedIntersection
      by_cases hy : y ∈ R
      · simp [hy, hSw x]
      · simp [hy]
    intro x x' y y'
    simp only [hval]
    ring

end Shore

open scoped BigOperators
namespace Main
open Loss
open Shape (Fits saturated_shape)

private theorem normal_shapes {N g r s M : ℕ} (hr : 0 < r) (hrs : r ≤ s) (hgs : r + s = g + 1)
    (hp : r * s < N) (hN : 2 * g + 1 < N) (D : Fin M → Circ)
    (hD : ∀ i, Fits N g r s (D i)) (hA : ∀ i, size (tab (D i) : Tbl N) = (g + 1) * N - r * s) :
    ∃ A B : Fin M → Finset (X N),
      (∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r)) ∧
      ∀ i x y, tab (D i) x y = decide (x ∈ A i ∨ y ∈ B i) := by
  classical
  have hex (i : Fin M) : ∃ A B : Finset (X N),
      ((A.card = r ∧ B.card = s) ∨ (A.card = s ∧ B.card = r)) ∧
      ∀ x y, tab (D i) x y = decide (x ∈ A ∨ y ∈ B) := by
    obtain ⟨sw, A, B, ha, hb, he⟩ := saturated_shape hr hrs hgs hp hN (hD i) (hA i)
    cases sw with
    | false => exact ⟨A, B, Or.inl ⟨ha, hb⟩, he⟩
    | true =>
      refine ⟨B, A, Or.inr ⟨hb, ha⟩, fun x y => ?_⟩
      have h : tab (D i) x y = decide (y ∈ A ∨ x ∈ B) := he y x
      exact h.trans (by simp [or_comm])
  choose A B hs he using hex
  exact ⟨A, B, hs, he⟩

private theorem cap_on_shore {N g r s M : ℕ} (hgs : r + s = g + 1) (D : Fin M → Circ)
    (sw : Bool) (R : Finset (X N)) (S : Fin M → Finset (X N)) (hR : R.card = r)
    (hS : ∀ i, (S i).card = s) (hD : ∀ i x y, (if sw then tab (D i) y x else tab (D i) x y) =
      decide (x ∈ R ∨ y ∈ S i)) : ∀ i, size (tab (D i) : Tbl N) = (g + 1) * N - r * s := by
  intro i
  cases sw with
  | false =>
    have he : tab (D i) = fun x y => decide (x ∈ R ∨ y ∈ S i) :=
      funext fun x => funext fun y => hD i x y
    rw [he, size_union_lines, hR, hS, hgs]
  | true =>
    have he : tab (D i) = fun x y => decide (x ∈ S i ∨ y ∈ R) :=
      funext fun x => funext fun y => by simpa [or_comm] using hD i y x
    rw [he, size_union_lines, hR, hS, Nat.add_comm s r, Nat.mul_comm s r, hgs]

end Main

end PEqualNP.Outside.L_meta_33645

open PEqualNP.Outside.L_meta_33645.Shape (Fits) in
open PEqualNP.Outside.L_meta_33645 PEqualNP.Outside.L_meta_33645.Main PEqualNP.Outside.L_meta_33645.Loss in
theorem PEqualNP.Outside.L_meta_33645 : ∀ (N g t r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N →
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
  let cov := fun (n m : ℕ) (S : Fin m → Finset (Fin n)) (v : Fin m → ℝ) =>
    (∀ i, (S i).card = s ∧ 0 < v i) ∧ ∀ y, (∑ i, if y ∈ S i then v i else 0) = 1
  let K := fun n : ℕ => sInf {m : ℕ | ∃ S v, cov n m S v}
  let shore := fun (M : ℕ) (D : Fin M → Circ) (w : Fin M → ℝ) =>
    ∃ (swap : Bool) (R : Finset X) (S : Fin M → Finset X), R.card = r ∧
      cov N M S (fun i => (N : ℝ)*w i/(s : ℝ)) ∧
      ∀ (i : Fin M) (x y : X), (if swap then tab (D i) y x else tab (D i) x y) =
        decide (x ∈ R ∨ y ∈ S i)
  let short := (K N)*(r+s-1) < 2*N-1 ∧ (r=s ∨ (K N)*r < N)
  (short ∨ 4*s^3 ≤ N) →
    (∀ M : ℕ, (∃ D w, valid M D w ∧ good M D w) ↔ K N ≤ M) ∧
    (∀ (D : Fin (K N) → Circ) (w : Fin (K N) → ℝ), valid (K N) D w →
      (good (K N) D w ↔ shore (K N) D w)) ∧
    (4*s^3 ≤ N → K N = K (2*s*s+N % s) + (N-(2*s*s+N % s))/s) ∧
    ∀ q : ℕ, 0 < q → Even s → N = q*s+s/2 →
      K N = q+2 ∧ ∀ (D : Fin (q+2) → Circ) (w : Fin (q+2) → ℝ),
        valid (q+2) D w → good (q+2) D w →
        ((Finset.univ : Finset (Fin (q+2))).filter (fun i => (N : ℝ)*w i < (s : ℝ))).card = 3 ∧
        ∀ i, (N : ℝ)*w i = (s : ℝ) ∨ 2*(N : ℝ)*w i = (s : ℝ) := by
  intro N g t r s hr hrs hgs hp hN ht htN
  dsimp only
  intro hhyp
  have hs : 0 < s := hr.trans_le hrs
  have hNpos : 0 < N := by omega
  have hsN : s ≤ N := by
    have : s ≤ r * s := Nat.le_mul_of_pos_left s hr
    omega
  let _ : NeZero N := ⟨by omega⟩
  let cap := (g + 1) * N - r * s
  have hcapN : cap ≤ N * N := (Nat.sub_le _ _).trans (Nat.mul_le_mul_right N (by omega))
  have hbench := bench_cast ht htN.le hcapN
  have hreg : reg t (cyclic t : Tbl N) := cyclic_reg htN.le
  have hcaps {M : ℕ} (D : Fin M → Circ) (h : ∀ i, Fits N g r s (D i)) :
      ∀ i, size (tab (D i) : Tbl N) ≤ cap := fun i => (h i).2.2.2.2
  have hshort : (Cover.K s N) * (r + s - 1) < 2 * N - 1 ∧ (r = s ∨ (Cover.K s N) * r < N) := by
    rcases hhyp with hsh | hlarge
    · exact hsh
    · exact Cover.short_of_large hr hrs (by omega) hlarge
  have from_good {M : ℕ} (D : Fin M → Circ) (w : Fin M → ℝ)
      (hf : ∀ i, Fits N g r s (D i)) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
      (hg : ∀ T : Tbl N, reg t T → err (fun i => tab (D i)) w T ≤ benchR N t cap) :
      ∃ A B : Fin M → Finset (X N),
        (∀ i, ((A i).card = r ∧ (B i).card = s) ∨ ((A i).card = s ∧ (B i).card = r)) ∧
        (∀ i x y, tab (D i) x y = decide (x ∈ A i ∨ y ∈ B i)) ∧
        Shore.Additive (Shore.weightedIntersection A B w) := by
    have hsat := (saturates (fun i => tab (D i)) w hw1 hw (hcaps D hf) ht hreg
      (fun u => hg _ (shift_reg hreg u))).1
    obtain ⟨A, B, hsAB, he⟩ := Main.normal_shapes hr hrs hgs hp hN D hf hsat
    have hdiff := mixed_diff (by omega : 1 < N) (by omega : 0 < t) htN
      (fun i => tab (D i)) w hw1 hw (hcaps D hf) ht hg
    exact ⟨A, B, hsAB, he, (mixed_union_iff (fun i => tab (D i)) w A B he).mp hdiff⟩
  have hgood_of_shore {M : ℕ} (D : Fin M → Circ) (w : Fin M → ℝ) (hw1 : ∑ i, w i = 1)
      (hsh : ∃ (sw : Bool) (R : Finset (X N)) (S : Fin M → Finset (X N)), R.card = r ∧
        Cover.cov s N M S (fun i => (N : ℝ) * w i / (s : ℝ)) ∧
        ∀ (i : Fin M) (x y : X N), (if sw then tab (D i) y x else tab (D i) x y) =
          decide (x ∈ R ∨ y ∈ S i)) :
      ∀ T : Tbl N, reg t T → err (fun i => tab (D i)) w T ≤ (N * (N * t) - (2 * t - N) * cap : ℕ) := by
    obtain ⟨sw, R, S, hR, hcov, he⟩ := hsh
    intro T hT
    let A := fun i => if sw then S i else R
    let B := fun i => if sw then R else S i
    have hu (i : Fin M) (x y : X N) : tab (D i) x y = decide (x ∈ A i ∨ y ∈ B i) := by
      cases sw
      · exact he i x y
      · simpa [A, B, Loss.tab, or_comm] using he i y x
    have ha := Shore.additive_of_shore (R := R) hs hNpos sw hcov
    have hd := (mixed_union_iff (fun i => tab (D i)) w A B hu).mpr ha
    have hcap_eq := Main.cap_on_shore hgs D sw R S hR (fun i => (hcov.1 i).1) he
    have heq := good_if_add (fun i => tab (D i)) w hw1 hcap_eq hd hT
    exact (heq.trans hbench.symm).le
  have hshore_iff {M : ℕ} (hMeq : M = Cover.K s N) (D : Fin M → Circ) (w : Fin M → ℝ)
      (hf : ∀ i, Fits N g r s (D i)) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) :
      (∀ T : Tbl N, reg t T → err (fun i => tab (D i)) w T ≤ (N * (N * t) - (2 * t - N) * cap : ℕ)) ↔
      (∃ (sw : Bool) (R : Finset (X N)) (S : Fin M → Finset (X N)), R.card = r ∧
        Cover.cov s N M S (fun i => (N : ℝ) * w i / (s : ℝ)) ∧
        ∀ (i : Fin M) (x y : X N), (if sw then tab (D i) y x else tab (D i) x y) =
          decide (x ∈ R ∨ y ∈ S i)) := by
    constructor
    · intro hg
      obtain ⟨A, B, hsAB, he, ha⟩ := from_good D w hf hw hw1 (fun T hT => (hg T hT).trans hbench.le)
      have hcross : M * (r + s - 1) < 2 * N - 1 := hMeq ▸ hshort.1
      have hratio : r = s ∨ M * r < N := hMeq ▸ hshort.2
      obtain ⟨_, hstruct⟩ := Shore.structure_main hr hrs hNpos hsAB hw hw1 ha hcross hratio
      obtain ⟨sw, R, S, hR, hcov, hsets⟩ := hstruct hMeq
      refine ⟨sw, R, S, hR, hcov, fun i x y => ?_⟩
      obtain ⟨h1, h2⟩ := hsets i
      cases sw with
      | false =>
        change A i = R at h1
        change B i = S i at h2
        change tab (D i) x y = decide (x ∈ R ∨ y ∈ S i)
        rw [he, h1, h2]
      | true =>
        change B i = R at h1
        change A i = S i at h2
        change tab (D i) y x = decide (x ∈ R ∨ y ∈ S i)
        simpa [h1, h2, or_comm] using he i y x
    · exact hgood_of_shore D w hw1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M
    constructor
    · rintro ⟨D, w, ⟨hFit, hw1⟩, hg⟩
      by_contra hlt
      push Not at hlt
      have hle : M ≤ Cover.K s N := hlt.le
      have hcross : M * (r + s - 1) < 2 * N - 1 :=
        (Nat.mul_le_mul_right _ hle).trans_lt hshort.1
      have hratio : r = s ∨ M * r < N :=
        hshort.2.imp id fun h => (Nat.mul_le_mul_right r hle).trans_lt h
      obtain ⟨A, B, hsAB, _, ha⟩ := from_good D w (fun i => (hFit i).1) (fun i => (hFit i).2)
        hw1 (fun T hT => (hg T hT).trans hbench.le)
      exact hlt.not_ge (Shore.structure_main hr hrs hNpos hsAB (fun i => (hFit i).2) hw1 ha
        hcross hratio).1
    · intro hKM
      obtain ⟨S0, v0, hcov0⟩ := Cover.K_spec hs hsN
      obtain ⟨S, v, hcov⟩ := Cover.cov_pad (Cover.K_pos hs hsN) hKM hcov0
      let R : Finset (X N) :=
        Finset.univ.map (Fin.castLEEmb ((Nat.le_mul_of_pos_right r hs).trans hp.le))
      have hR : R.card = r := by simp [R]
      choose D hfit _ he using fun i => Build.synth_cross hgs R (S i) hR (hcov.1 i).1
      let w : Fin M → ℝ := fun i => (s : ℝ) * v i / (N : ℝ)
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
      have hw_pos : ∀ i, 0 < w i := fun i => div_pos (mul_pos hsR (hcov.1 i).2) hNR
      have hw_sum : ∑ i, w i = 1 := by
        have hsw := Cover.cov_sum_weights hcov
        calc
          ∑ i, (s : ℝ) * v i / (N : ℝ) = ((s : ℝ) * ∑ i, v i) / (N : ℝ) := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]
          _ = (N : ℝ) / (N : ℝ) := by rw [hsw]
          _ = 1 := div_self hNR.ne'
      have hvw : (fun i => (N : ℝ) * w i / (s : ℝ)) = v := by
        funext i
        dsimp [w]
        field_simp [hNR.ne', hsR.ne']
      refine ⟨D, w, ⟨fun i => ⟨hfit i, hw_pos i⟩, hw_sum⟩, ?_⟩
      exact hgood_of_shore D w hw_sum ⟨false, R, S, hR, hvw.symm ▸ hcov, fun i x y => he i x y⟩
  · intro D w ⟨hFit, hw1⟩
    exact hshore_iff rfl D w (fun i => (hFit i).1) (fun i => (hFit i).2) hw1
  · intro hlarge
    exact Cover.K_large_width hs hlarge
  · intro q hq heven hNq
    have hKeq : Cover.K s N = q + 2 := Cover.half_rem_K hs hq heven hNq
    refine ⟨hKeq, fun D w ⟨hFit, hw1⟩ hg => ?_⟩
    have hsh := (hshore_iff hKeq.symm D w (fun i => (hFit i).1) (fun i => (hFit i).2) hw1).mp hg
    obtain ⟨_, _, S, _, hcov, _⟩ := hsh
    obtain ⟨_, hcard, hval⟩ := Cover.half_rem_analyze hs hq heven hNq hcov le_rfl
    have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hlt_iff (i : Fin (q + 2)) : (N : ℝ) * w i < (s : ℝ) ↔ (N : ℝ) * w i / (s : ℝ) < 1 := by
      rw [div_lt_one hsR]
    refine ⟨?_, fun i => ?_⟩
    · convert hcard using 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlt_iff]
    · rcases hval i with h1 | h2
      · left
        have := (div_eq_one_iff_eq hsR.ne').mp h1
        exact this
      · right
        have := congrArg (· * (s : ℝ)) h2
        have hmul : 2 * ((N : ℝ) * w i / (s : ℝ)) * (s : ℝ) = 2 * (N : ℝ) * w i := by
          field_simp [hsR.ne']
        linarith
