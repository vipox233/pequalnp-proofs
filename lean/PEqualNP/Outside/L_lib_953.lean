import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic

namespace PEqualNP.Outside.L_lib_953

private def par {m q : Nat} (u v : Fin m → Fin q) : Bool :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => u i = v i)).card % 2 == 1

private def sign (b : Bool) : ℚ :=
  if b then -1 else 1

private def T {m q : Nat} (u v : Fin m → Fin q) : ℚ :=
  sign (par u v)

private def hdist {m q : Nat} (u v : Fin m → Fin q) : Nat :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => u i ≠ v i)).card

private lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> simp [sign]

private lemma sign_mul_sign (a b : Bool) : sign a * sign b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp [sign]

private lemma neg_one_pow_eq_sign (n : Nat) : (-1 : ℚ) ^ n = sign (n % 2 == 1) := by
  induction n with
  | zero => simp [sign]
  | succ k ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [sign, Nat.add_mod, h]

private lemma T_eq_prod {m q : Nat} (u v : Fin m → Fin q) :
    T u v = ∏ i : Fin m, (if u i = v i then (-1 : ℚ) else 1) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, neg_one_pow_eq_sign]
  rfl

private lemma row_corr {m q : Nat} (hq : 5 ≤ q) (u u' : Fin m → Fin q) :
    ∑ v : Fin m → Fin q, T u v * T u' v =
      ((q ^ m : Nat) : ℚ) * (1 - 4 / (q : ℚ)) ^ hdist u u' := by
  have hqpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr (by omega)
  have hq0 : (q : ℚ) ≠ 0 := hqpos.ne'
  have hprod : ∀ v : Fin m → Fin q, T u v * T u' v =
      ∏ i : Fin m, ((if u i = v i then (-1 : ℚ) else 1) * (if u' i = v i then (-1 : ℚ) else 1)) := by
    intro v
    rw [T_eq_prod, T_eq_prod, ← Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (i : Fin m) (a : Fin q) =>
    (if u i = a then (-1 : ℚ) else 1) * (if u' i = a then (-1 : ℚ) else 1))]
  have hcoord : ∀ i : Fin m,
      ∑ a : Fin q, (if u i = a then (-1 : ℚ) else 1) * (if u' i = a then (-1 : ℚ) else 1) =
        (q : ℚ) * (if u i ≠ u' i then 1 - 4 / (q : ℚ) else 1) := by
    intro i
    by_cases h : u i = u' i
    · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, mul_one]
      have h1 : ∀ a : Fin q,
          (if u' i = a then (-1 : ℚ) else 1) * (if u' i = a then (-1 : ℚ) else 1) = 1 := by
        intro a
        by_cases ha : u' i = a <;> simp [ha]
      simp [h1]
    · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
      have h1 : ∀ a : Fin q,
          (if u i = a then (-1 : ℚ) else 1) * (if u' i = a then (-1 : ℚ) else 1) =
            1 + (if a = u i then (-2 : ℚ) else 0) + (if a = u' i then (-2 : ℚ) else 0) := by
        intro a
        by_cases h1 : u i = a <;> by_cases h2 : u' i = a
        · exact absurd (h1.trans h2.symm) h
        · have ha2 : a ≠ u' i := Ne.symm h2
          simp only [h1, h2, ha2, ↓reduceIte]
          ring
        · have ha1 : a ≠ u i := Ne.symm h1
          simp only [h1, h2, ha1, ↓reduceIte]
          ring
        · have ha1 : a ≠ u i := Ne.symm h1
          have ha2 : a ≠ u' i := Ne.symm h2
          simp only [h1, h2, ha1, ha2, ↓reduceIte]
          ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hq0]
      ring
  simp_rw [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Nat.cast_pow]
  rfl

private def works0 (m q : Nat) (bias : ℚ) (messages : Nat) : Prop :=
  ∃ (send : (Fin m → Fin q) → Fin messages) (read : Fin messages → (Fin m → Fin q) → Bool),
    (1 + bias) * ((q ^ m : Nat) : ℚ) ^ 2 ≤
      2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read (send pair.1) pair.2 = par pair.1 pair.2)).card : ℚ)

private lemma xor_bridge1 (a b c d : Bool) : xor (xor a b) c = d ↔ a = xor (xor b c) d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma xor_bridge2 (a b c d : Bool) :
    xor (xor a b) c = xor (xor b c) d ↔ a = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma two_mul_add_toNat_div (a : Nat) (b : Bool) : (2 * a + b.toNat) / 2 = a := by
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private lemma two_mul_add_toNat_mod (a : Nat) (b : Bool) : ((2 * a + b.toNat) % 2 == 1) = b := by
  cases b <;> simp

private lemma two_mul_add_toNat_lt {a M : Nat} (ha : a < M) (b : Bool) :
    2 * a + b.toNat < 2 * M := by
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private lemma works_to_works0 {m q : Nat} {bias : ℚ} {leftFlip rightFlip : (Fin m → Fin q) → Bool}
    {M : Nat}
    (h : ∃ (send : (Fin m → Fin q) → Fin M) (read : Fin M → (Fin m → Fin q) → Bool),
      (1 + bias) * ((q ^ m : Nat) : ℚ) ^ 2 ≤
        2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
          (fun pair => read (send pair.1) pair.2 =
            xor (xor (leftFlip pair.1) (rightFlip pair.2)) (par pair.1 pair.2))).card : ℚ)) :
    works0 m q bias (2 * M) := by
  rcases h with ⟨send, read, hcorr⟩
  refine ⟨fun u => ⟨2 * (send u).val + (leftFlip u).toNat,
      two_mul_add_toNat_lt (send u).isLt (leftFlip u)⟩,
    fun c v => xor (xor (read ⟨c.val / 2, by have := c.isLt; omega⟩ v) (c.val % 2 == 1))
      (rightFlip v), ?_⟩
  have heq :
      ((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => xor (xor (read ⟨(2 * (send pair.1).val + (leftFlip pair.1).toNat) / 2,
          by have := two_mul_add_toNat_lt (send pair.1).isLt (leftFlip pair.1); omega⟩ pair.2)
          ((2 * (send pair.1).val + (leftFlip pair.1).toNat) % 2 == 1)) (rightFlip pair.2) =
          par pair.1 pair.2)) =
      ((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read (send pair.1) pair.2 =
          xor (xor (leftFlip pair.1) (rightFlip pair.2)) (par pair.1 pair.2))) := by
    apply Finset.filter_congr
    intro pair _
    have hdiv : (⟨(2 * (send pair.1).val + (leftFlip pair.1).toNat) / 2,
        by have := two_mul_add_toNat_lt (send pair.1).isLt (leftFlip pair.1); omega⟩ : Fin M) =
        send pair.1 := Fin.ext (two_mul_add_toNat_div _ _)
    rw [hdiv, two_mul_add_toNat_mod]
    exact xor_bridge1 _ _ _ _
  dsimp only
  rwa [heq]

private lemma weighted_cs {α : Type*} (s : Finset α) (w x : α → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (x i) ^ 2) := by
  have h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2 :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  have hexp : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2 =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * (x i) ^ 2)) - 2 * (∑ i ∈ s, w i * x i) ^ 2 := by
    have hpt : ∀ i j, w i * w j * (x i - x j) ^ 2 =
        (w i * x i ^ 2) * w j + w i * (w j * x j ^ 2) - 2 * ((w i * x i) * (w j * x j)) := by
      intro i j; ring
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

private lemma hdist_symm {m q : Nat} (u v : Fin m → Fin q) : hdist u v = hdist v u := by
  unfold hdist
  congr 1
  apply Finset.filter_congr
  intro i _
  exact ne_comm

private lemma hdist_eq_zero_iff {m q : Nat} (u v : Fin m → Fin q) : hdist u v = 0 ↔ u = v := by
  unfold hdist
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    by_contra hne
    exact h (Finset.mem_univ i) hne
  · intro h i _
    simp [h]

private lemma hdist_triangle {m q : Nat} (u v w : Fin m → Fin q) :
    hdist u w ≤ hdist u v + hdist v w := by
  unfold hdist
  have hsub : (Finset.univ : Finset (Fin m)).filter (fun i => u i ≠ w i) ⊆
      (Finset.univ.filter (fun i => u i ≠ v i)) ∪ (Finset.univ.filter (fun i => v i ≠ w i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases huv : u i = v i
    · right; intro hvw; exact hi (huv.trans hvw)
    · left; exact huv
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private def patchFin {m q : Nat} :
    (k : Nat) → (Fin k → Fin m × Fin q) → (Fin m → Fin q) → (Fin m → Fin q)
  | 0, _, base => base
  | k + 1, p, base => fun i =>
    if i = (p 0).1 then (p 0).2 else patchFin k (fun j => p j.succ) base i

private lemma patchFin_apply {m q : Nat} :
    ∀ (k : Nat) (p : Fin k → Fin m × Fin q) (base target : Fin m → Fin q),
      (∀ j : Fin k, (p j).2 = target (p j).1) →
      ∀ i : Fin m, ((∀ j : Fin k, i ≠ (p j).1) → base i = target i) →
      patchFin k p base i = target i
  | 0, _, base, target, _, i, hbase => hbase (fun j => Fin.elim0 j)
  | k + 1, p, base, target, hp, i, hbase => by
    by_cases hi : i = (p 0).1
    · simp only [patchFin, hi, ↓reduceIte]
      exact hp 0
    · simp only [patchFin, hi, ↓reduceIte]
      exact patchFin_apply k (fun j => p j.succ) base target
        (fun j => hp j.succ) i (fun hx => hbase (fun j => Fin.cases hi hx j))

private lemma common_ball_card_le {m q : Nat} (hm : 0 < m) (hq : 1 ≤ q) (l : Nat)
    (u u' : Fin m → Fin q) (hdu : l ≤ hdist u u') :
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun w => hdist u w ≤ l ∧ hdist u' w ≤ l)).card ≤
      q ^ (2 * l + l / 2) * m ^ (l / 2) := by
  by_cases h2l : 2 * l < hdist u u'
  · have hemp : ((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun w => hdist u w ≤ l ∧ hdist u' w ≤ l)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _ hw
      have htri := hdist_triangle u w u'
      rw [hdist_symm w u'] at htri
      omega
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _
  · have hdle : hdist u u' ≤ 2 * l := Nat.le_of_not_lt h2l
    let D : Finset (Fin m) := Finset.univ.filter (fun i => u i ≠ u' i)
    let E : Finset (Fin m) := Finset.univ.filter (fun i => u i = u' i)
    have hDcard : D.card = hdist u u' := rfl
    let k := l / 2
    let A := (Fin k → Fin m × Fin q) × ({i : Fin m // i ∈ D} → Fin q)
    let F : A → (Fin m → Fin q) := fun a =>
      patchFin k a.1 (fun i => if h : i ∈ D then a.2 ⟨i, h⟩ else u i)
    have hsub : ((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun w => hdist u w ≤ l ∧ hdist u' w ≤ l)) ⊆ Finset.univ.image F := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      let SE : Finset (Fin m) := E.filter (fun i => w i ≠ u i)
      let D1 : Finset (Fin m) := D.filter (fun i => u i ≠ w i)
      let D2 : Finset (Fin m) := D.filter (fun i => u' i ≠ w i)
      have hdisj1 : Disjoint SE D1 := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [SE, E, D1, D, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
        exact hi2.1 hi1.1
      have hdisj2 : Disjoint SE D2 := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [SE, E, D2, D, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
        exact hi2.1 hi1.1
      have hsub1 : SE ∪ D1 ⊆ Finset.univ.filter (fun i => u i ≠ w i) := by
        intro i hi
        simp only [Finset.mem_union, SE, E, D1, D, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi ⊢
        rcases hi with ⟨_, hwu⟩ | ⟨_, huw⟩
        · exact hwu.symm
        · exact huw
      have hsub2 : SE ∪ D2 ⊆ Finset.univ.filter (fun i => u' i ≠ w i) := by
        intro i hi
        simp only [Finset.mem_union, SE, E, D2, D, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi ⊢
        rcases hi with ⟨heq, hwu⟩ | ⟨_, huw⟩
        · rw [← heq]; exact hwu.symm
        · exact huw
      have hDcov : D ⊆ D1 ∪ D2 := by
        intro i hi
        simp only [Finset.mem_union, D1, D2, D, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi ⊢
        by_cases huw : u i = w i
        · right; refine ⟨hi, ?_⟩; intro hu'w; exact hi (huw.trans hu'w.symm)
        · left; exact ⟨hi, huw⟩
      have hc1 : SE.card + D1.card ≤ hdist u w := by
        rw [← Finset.card_union_of_disjoint hdisj1]
        exact Finset.card_le_card hsub1
      have hc2 : SE.card + D2.card ≤ hdist u' w := by
        rw [← Finset.card_union_of_disjoint hdisj2]
        exact Finset.card_le_card hsub2
      have hcD : D.card ≤ D1.card + D2.card :=
        (Finset.card_le_card hDcov).trans (Finset.card_union_le D1 D2)
      have hSE : SE.card ≤ k := by omega
      let L : List (Fin m) := SE.toList
      have hLlen : L.length ≤ k := by simpa [L, Finset.length_toList] using hSE
      let i0 : Fin m := ⟨0, hm⟩
      let p : Fin k → Fin m × Fin q := fun j =>
        if hj : j.val < L.length then (L[j.val], w L[j.val]) else (i0, w i0)
      let g : {i : Fin m // i ∈ D} → Fin q := fun x => w x.val
      rw [Finset.mem_image]
      refine ⟨(p, g), Finset.mem_univ _, ?_⟩
      funext i
      apply patchFin_apply
      · intro j
        dsimp [p]
        split_ifs <;> rfl
      · intro hi
        by_cases hiD : i ∈ D
        · simp [g, hiD]
        · simp only [hiD, ↓reduceDIte]
          have heq : u i = u' i := by
            simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hiD
            exact hiD
          by_contra hne
          have hiSE : i ∈ SE := by
            simp only [SE, E, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨heq, Ne.symm hne⟩
          have hiL : i ∈ L := Finset.mem_toList.mpr hiSE
          rcases List.mem_iff_getElem.mp hiL with ⟨idx, hidx, hget⟩
          have hlt : idx < k := lt_of_lt_of_le hidx hLlen
          have hcontra := hi ⟨idx, hlt⟩
          simp only [p, hidx, ↓reduceDIte] at hcontra
          exact hcontra hget.symm
    have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_univ] at hcard
    have hAcard : Fintype.card A = (m * q) ^ k * q ^ D.card := by
      simp [A, Fintype.card_prod, Fintype.card_fin]
    rw [hAcard] at hcard
    have hpow : q ^ D.card ≤ q ^ (2 * l) := Nat.pow_le_pow_right hq hdle
    calc ((Finset.univ : Finset (Fin m → Fin q)).filter
            (fun w => hdist u w ≤ l ∧ hdist u' w ≤ l)).card
        ≤ (m * q) ^ k * q ^ D.card := hcard
      _ ≤ (m * q) ^ k * q ^ (2 * l) := Nat.mul_le_mul_left _ hpow
      _ = q ^ (2 * l + k) * m ^ k := by rw [mul_pow, pow_add]; ring

private def cls {m q M : Nat} (send : (Fin m → Fin q) → Fin M) (c : Fin M) :
    Finset (Fin m → Fin q) :=
  Finset.univ.filter (fun u => send u = c)

private def Cpos {m q M : Nat} (send : (Fin m → Fin q) → Fin M) : Finset (Fin M) :=
  Finset.univ.filter (fun c => 0 < (cls send c).card)

private def pairCount {m q : Nat} (S : Finset (Fin m → Fin q)) (l : Nat) : Nat :=
  ((S ×ˢ S).filter (fun p => hdist p.1 p.2 ≤ l)).card

private def qClass {m q : Nat} (S : Finset (Fin m → Fin q)) (l : Nat) : ℚ :=
  (pairCount S l : ℚ) / ((S.card : ℚ) ^ 2)

private def Qval {m q M : Nat} (send : (Fin m → Fin q) → Fin M) (l : Nat) : ℚ :=
  ∑ c ∈ Cpos send, ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) * qClass (cls send c) l

private lemma sum_cls_card {m q M : Nat} (send : (Fin m → Fin q) → Fin M) :
    ∑ c ∈ Cpos send, (cls send c).card = q ^ m := by
  have h1 : ∑ c : Fin M, (cls send c).card = Fintype.card (Fin m → Fin q) := by
    rw [← Finset.card_univ]
    symm
    exact Finset.card_eq_sum_card_fiberwise (fun u _ => Finset.mem_univ (send u))
  have h2 : ∑ c ∈ Cpos send, (cls send c).card = ∑ c : Fin M, (cls send c).card := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro c _ hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hc
    exact hc
  rw [h2, h1, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

private lemma sum_cls_weight {m q M : Nat} (hq : 1 ≤ q) (send : (Fin m → Fin q) → Fin M) :
    ∑ c ∈ Cpos send, ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) = 1 := by
  have hN0 : ((q ^ m : Nat) : ℚ) ≠ 0 := by
    have : 0 < q ^ m := Nat.pow_pos (by omega)
    exact (Nat.cast_pos.mpr this).ne'
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_cls_card, mul_inv_cancel₀ hN0]

private lemma pairCount_zero {m q : Nat} (S : Finset (Fin m → Fin q)) :
    pairCount S 0 = S.card := by
  unfold pairCount
  have heq : (S ×ˢ S).filter (fun p => hdist p.1 p.2 ≤ 0) = S.image (fun u => (u, u)) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Nat.le_zero,
      hdist_eq_zero_iff]
    constructor
    · rintro ⟨⟨hu, _⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨w, hw, h⟩
      cases h
      exact ⟨⟨hw, hw⟩, rfl⟩
  rw [heq, Finset.card_image_of_injective]
  intro a b h
  exact (Prod.mk.inj h).1

private lemma Qval_zero_le {m q M : Nat} (send : (Fin m → Fin q) → Fin M) :
    Qval send 0 ≤ (M : ℚ) / ((q ^ m : Nat) : ℚ) := by
  unfold Qval
  have hterm : ∀ c ∈ Cpos send,
      ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) * qClass (cls send c) 0 =
        1 / ((q ^ m : Nat) : ℚ) := by
    intro c hc
    have hpos : (0 : ℚ) < ((cls send c).card : ℚ) := by
      simp only [Cpos, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact Nat.cast_pos.mpr hc
    have hne : ((cls send c).card : ℚ) ≠ 0 := hpos.ne'
    unfold qClass
    rw [pairCount_zero, div_eq_mul_inv, div_eq_mul_inv]
    calc ((cls send c).card : ℚ) * ((q ^ m : Nat) : ℚ)⁻¹ *
            (((cls send c).card : ℚ) * (((cls send c).card : ℚ) ^ 2)⁻¹)
        = (((cls send c).card : ℚ) ^ 2 * (((cls send c).card : ℚ) ^ 2)⁻¹) *
            ((q ^ m : Nat) : ℚ)⁻¹ := by ring
      _ = 1 * ((q ^ m : Nat) : ℚ)⁻¹ := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hne)]
      _ = 1 / ((q ^ m : Nat) : ℚ) := by rw [one_mul, one_div]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hle : ((Cpos send).card : ℚ) ≤ (M : ℚ) := by
    have : (Cpos send).card ≤ Fintype.card (Fin M) := Finset.card_le_univ _
    simpa [Fintype.card_fin] using (Nat.cast_le (α := ℚ)).mpr this
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)

private lemma pairCount_eq_sum_ball {m q : Nat} (S : Finset (Fin m → Fin q)) (l : Nat) :
    pairCount S l = ∑ w ∈ S, (S.filter (fun u => hdist u w ≤ l)).card := by
  unfold pairCount
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.card_filter]

private lemma sum_ball_sq_eq {m q : Nat} (S : Finset (Fin m → Fin q)) (l : Nat) :
    ∑ w ∈ S, (S.filter (fun u => hdist u w ≤ l)).card ^ 2 =
      ∑ p ∈ S ×ˢ S, (S.filter (fun w => hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l)).card := by
  have hsq : ∀ w : Fin m → Fin q,
      (S.filter (fun u => hdist u w ≤ l)).card ^ 2 =
        ∑ p ∈ S ×ˢ S, if hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l then 1 else 0 := by
    intro w
    rw [sq, ← Finset.card_product]
    have heq : (S.filter (fun u => hdist u w ≤ l)) ×ˢ (S.filter (fun u => hdist u w ≤ l)) =
        (S ×ˢ S).filter (fun p => hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_product, Finset.mem_filter]
      tauto
    rw [heq, Finset.card_filter]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.card_filter]

private lemma qClass_sq_le {m q : Nat} (hm : 0 < m) (hq : 1 ≤ q)
    (S : Finset (Fin m → Fin q)) (hS : 0 < S.card) (l : Nat) (hl : 1 ≤ l) :
    (qClass S l) ^ 2 ≤
      qClass S (l - 1) + ((q ^ (2 * l + l / 2) * m ^ (l / 2) : Nat) : ℚ) / (S.card : ℚ) := by
  let B : Nat := q ^ (2 * l + l / 2) * m ^ (l / 2)
  have hnat : ∑ w ∈ S, (S.filter (fun u => hdist u w ≤ l)).card ^ 2 ≤
      pairCount S (l - 1) * S.card + S.card * S.card * B := by
    rw [sum_ball_sq_eq]
    have hpt : ∀ p ∈ S ×ˢ S,
        (S.filter (fun w => hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l)).card ≤
          (if hdist p.1 p.2 ≤ l - 1 then S.card else 0) + B := by
      intro p _
      by_cases hp : hdist p.1 p.2 ≤ l - 1
      · simp only [hp, ↓reduceIte]
        exact (Finset.card_filter_le _ _).trans (Nat.le_add_right _ _)
      · simp only [hp, ↓reduceIte, zero_add]
        have hdu : l ≤ hdist p.1 p.2 := by omega
        have hsub : S.filter (fun w => hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l) ⊆
            (Finset.univ : Finset (Fin m → Fin q)).filter
              (fun w => hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact hw.2
        exact (Finset.card_le_card hsub).trans (common_ball_card_le hm hq l p.1 p.2 hdu)
    calc ∑ p ∈ S ×ˢ S, (S.filter (fun w => hdist p.1 w ≤ l ∧ hdist p.2 w ≤ l)).card
        ≤ ∑ p ∈ S ×ˢ S, ((if hdist p.1 p.2 ≤ l - 1 then S.card else 0) + B) :=
          Finset.sum_le_sum hpt
      _ = (∑ p ∈ S ×ˢ S, if hdist p.1 p.2 ≤ l - 1 then S.card else 0) +
            ∑ p ∈ S ×ˢ S, B := Finset.sum_add_distrib
      _ = pairCount S (l - 1) * S.card + S.card * S.card * B := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
            smul_eq_mul, Finset.sum_const, Finset.card_product, smul_eq_mul]
          rfl
  have hcs := weighted_cs S (fun _ => (1 : ℚ))
    (fun w => ((S.filter (fun u => hdist u w ≤ l)).card : ℚ)) (fun _ _ => zero_le_one)
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hpc : (pairCount S l : ℚ) = ∑ w ∈ S, ((S.filter (fun u => hdist u w ≤ l)).card : ℚ) := by
    rw [pairCount_eq_sum_ball, Nat.cast_sum]
  rw [← hpc] at hcs
  have hnatQ : ∑ w ∈ S, ((S.filter (fun u => hdist u w ≤ l)).card : ℚ) ^ 2 ≤
      (pairCount S (l - 1) : ℚ) * (S.card : ℚ) + (S.card : ℚ) * (S.card : ℚ) * (B : ℚ) := by
    exact_mod_cast hnat
  have hSq : (pairCount S l : ℚ) ^ 2 ≤
      (S.card : ℚ) ^ 2 * (pairCount S (l - 1) : ℚ) + (S.card : ℚ) ^ 3 * (B : ℚ) := by
    have hmul := mul_le_mul_of_nonneg_left hnatQ (Nat.cast_nonneg (α := ℚ) S.card)
    linarith [hcs, hmul]
  have hSpos : (0 : ℚ) < (S.card : ℚ) := Nat.cast_pos.mpr hS
  have hS4 : (0 : ℚ) < (S.card : ℚ) ^ 4 := pow_pos hSpos 4
  have hSne : (S.card : ℚ) ≠ 0 := hSpos.ne'
  have hdiv := div_le_div_of_nonneg_right hSq hS4.le
  have hrhs : ((S.card : ℚ) ^ 2 * (pairCount S (l - 1) : ℚ) + (S.card : ℚ) ^ 3 * (B : ℚ)) /
      (S.card : ℚ) ^ 4 = (pairCount S (l - 1) : ℚ) / (S.card : ℚ) ^ 2 + (B : ℚ) / (S.card : ℚ) := by
    rw [add_div]
    congr 1
    · rw [show (S.card : ℚ) ^ 4 = (S.card : ℚ) ^ 2 * (S.card : ℚ) ^ 2 by ring,
        mul_div_mul_left _ _ (pow_ne_zero 2 hSne)]
    · rw [show (S.card : ℚ) ^ 4 = (S.card : ℚ) ^ 3 * (S.card : ℚ) by ring,
        mul_div_mul_left _ _ (pow_ne_zero 3 hSne)]
  unfold qClass
  rw [div_pow, show ((S.card : ℚ) ^ 2) ^ 2 = (S.card : ℚ) ^ 4 by ring]
  linarith [hdiv, hrhs]

private lemma Qval_sq_le {m q M : Nat} (hm : 0 < m) (hq : 1 ≤ q)
    (send : (Fin m → Fin q) → Fin M) (l : Nat) (hl : 1 ≤ l) :
    (Qval send l) ^ 2 ≤
      Qval send (l - 1) +
        ((q ^ (2 * l + l / 2) * m ^ (l / 2) * M : Nat) : ℚ) / ((q ^ m : Nat) : ℚ) := by
  let B : Nat := q ^ (2 * l + l / 2) * m ^ (l / 2)
  have hcs := weighted_cs (Cpos send)
    (fun c => ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ))
    (fun c => qClass (cls send c) l)
    (fun c _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [sum_cls_weight hq send, one_mul] at hcs
  have hsum : ∑ c ∈ Cpos send, ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) *
      (qClass (cls send c) l) ^ 2 ≤
      Qval send (l - 1) + ((B * M : Nat) : ℚ) / ((q ^ m : Nat) : ℚ) := by
    have hpt : ∀ c ∈ Cpos send,
        ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) * (qClass (cls send c) l) ^ 2 ≤
          ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) * qClass (cls send c) (l - 1) +
            (B : ℚ) / ((q ^ m : Nat) : ℚ) := by
      intro c hc
      have hcpos : 0 < (cls send c).card := by
        simp only [Cpos, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact hc
      have hSne : ((cls send c).card : ℚ) ≠ 0 := (Nat.cast_pos.mpr hcpos).ne'
      have hql := qClass_sq_le hm hq (cls send c) hcpos l hl
      have hmul := mul_le_mul_of_nonneg_left hql
        (div_nonneg (Nat.cast_nonneg (cls send c).card) (Nat.cast_nonneg (q ^ m)))
      have hsimp : ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) *
          (qClass (cls send c) (l - 1) + (B : ℚ) / ((cls send c).card : ℚ)) =
          ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) * qClass (cls send c) (l - 1) +
            (B : ℚ) / ((q ^ m : Nat) : ℚ) := by
        rw [mul_add]
        congr 1
        rw [div_mul_div_comm, mul_comm ((cls send c).card : ℚ) (B : ℚ),
          mul_div_mul_right _ _ hSne]
      exact hmul.trans_eq hsimp
    calc ∑ c ∈ Cpos send, ((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) *
            (qClass (cls send c) l) ^ 2
        ≤ ∑ c ∈ Cpos send, (((cls send c).card : ℚ) / ((q ^ m : Nat) : ℚ) *
            qClass (cls send c) (l - 1) + (B : ℚ) / ((q ^ m : Nat) : ℚ)) :=
          Finset.sum_le_sum hpt
      _ = Qval send (l - 1) + ((Cpos send).card : ℚ) * ((B : ℚ) / ((q ^ m : Nat) : ℚ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          rfl
      _ ≤ Qval send (l - 1) + ((B * M : Nat) : ℚ) / ((q ^ m : Nat) : ℚ) := by
          have hle : ((Cpos send).card : ℚ) ≤ (M : ℚ) := by
            have : (Cpos send).card ≤ Fintype.card (Fin M) := Finset.card_le_univ _
            simpa [Fintype.card_fin] using (Nat.cast_le (α := ℚ)).mpr this
          have h1 : ((Cpos send).card : ℚ) * ((B : ℚ) / ((q ^ m : Nat) : ℚ)) ≤
              (M : ℚ) * ((B : ℚ) / ((q ^ m : Nat) : ℚ)) :=
            mul_le_mul_of_nonneg_right hle (div_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg (q ^ m)))
          have h2 : (M : ℚ) * ((B : ℚ) / ((q ^ m : Nat) : ℚ)) =
              ((B * M : Nat) : ℚ) / ((q ^ m : Nat) : ℚ) := by
            rw [← mul_div_assoc, mul_comm (M : ℚ) (B : ℚ), ← Nat.cast_mul]
          linarith
  exact hcs.trans hsum

private lemma sum_sign_eq_two_correct_sub {m q M : Nat}
    (send : (Fin m → Fin q) → Fin M) (read : Fin M → (Fin m → Fin q) → Bool) :
    ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
      sign (read (send pair.1) pair.2) * T pair.1 pair.2 =
      2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read (send pair.1) pair.2 = par pair.1 pair.2)).card : ℚ) -
      ((q ^ m : Nat) : ℚ) ^ 2 := by
  have hpt : ∀ pair : (Fin m → Fin q) × (Fin m → Fin q),
      sign (read (send pair.1) pair.2) * T pair.1 pair.2 =
        2 * (if read (send pair.1) pair.2 = par pair.1 pair.2 then (1 : ℚ) else 0) - 1 := by
    intro pair
    unfold T
    rw [sign_mul_sign]
    split_ifs <;> ring
  simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul, sq]

private lemma bias_sq_le_Qval {m q M r : Nat} {bias : ℚ} (hq : 5 ≤ q) (hbias : 0 < bias)
    (send : (Fin m → Fin q) → Fin M) (read : Fin M → (Fin m → Fin q) → Bool)
    (hcorr : (1 + bias) * ((q ^ m : Nat) : ℚ) ^ 2 ≤
      2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read (send pair.1) pair.2 = par pair.1 pair.2)).card : ℚ)) :
    bias ^ 2 ≤ (1 - 4 / (q : ℚ)) ^ (2 * r + 2) + Qval send (2 * r + 1) := by
  let N : ℚ := ((q ^ m : Nat) : ℚ)
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  have hqpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr (by omega)
  have hNpos : 0 < N := Nat.cast_pos.mpr (Nat.pow_pos (by omega))
  have hρ0 : 0 ≤ ρ := by
    have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    have h4 : 4 / (q : ℚ) ≤ 1 := (div_le_iff₀ hqpos).mpr (by linarith)
    dsimp [ρ]
    linarith
  have hρ1 : ρ ≤ 1 := by
    have h4 : 0 ≤ 4 / (q : ℚ) := div_nonneg (by linarith) hqpos.le
    dsimp [ρ]
    linarith
  have hadv : bias * N ^ 2 ≤
      ∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
        ((cls send p.1).card : ℚ) *
          (((cls send p.1).card : ℚ)⁻¹ * (sign (read p.1 p.2) * ∑ u ∈ cls send p.1, T u p.2)) := by
    have h1 : bias * N ^ 2 ≤
        ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
          sign (read (send pair.1) pair.2) * T pair.1 pair.2 := by
      rw [sum_sign_eq_two_correct_sub]
      dsimp [N]
      linarith
    have h2 : ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
          sign (read (send pair.1) pair.2) * T pair.1 pair.2 =
        ∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
          ((cls send p.1).card : ℚ) *
            (((cls send p.1).card : ℚ)⁻¹ *
              (sign (read p.1 p.2) * ∑ u ∈ cls send p.1, T u p.2)) := by
      have hsimp : ∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
            ((cls send p.1).card : ℚ) *
              (((cls send p.1).card : ℚ)⁻¹ *
                (sign (read p.1 p.2) * ∑ u ∈ cls send p.1, T u p.2)) =
          ∑ c ∈ Cpos send, ∑ v : Fin m → Fin q,
            sign (read c v) * ∑ u ∈ cls send c, T u v := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun v _ => ?_
        have hcpos : 0 < (cls send c).card := by
          simp only [Cpos, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact hc
        have hne : ((cls send c).card : ℚ) ≠ 0 := (Nat.cast_pos.mpr hcpos).ne'
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      rw [hsimp]
      have hfib : ∑ c ∈ Cpos send, ∑ v : Fin m → Fin q,
            sign (read c v) * ∑ u ∈ cls send c, T u v =
          ∑ c : Fin M, ∑ u ∈ cls send c, ∑ v : Fin m → Fin q,
            sign (read c v) * T u v := by
        have hsub : ∑ c ∈ Cpos send, ∑ v : Fin m → Fin q,
              sign (read c v) * ∑ u ∈ cls send c, T u v =
            ∑ c : Fin M, ∑ v : Fin m → Fin q,
              sign (read c v) * ∑ u ∈ cls send c, T u v := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro c _ hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
            Nat.le_zero, Finset.card_eq_zero] at hc
          simp [hc]
        rw [hsub]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      rw [hfib]
      have hpart : ∑ c : Fin M, ∑ u ∈ cls send c, ∑ v : Fin m → Fin q,
            sign (read c v) * T u v =
          ∑ u : Fin m → Fin q, ∑ v : Fin m → Fin q,
            sign (read (send u) v) * T u v := by
        have hcongr : ∀ c : Fin M,
            ∑ u ∈ cls send c, ∑ v : Fin m → Fin q, sign (read c v) * T u v =
            ∑ u ∈ cls send c, ∑ v : Fin m → Fin q, sign (read (send u) v) * T u v := by
          intro c
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          rw [hu]
        simp_rw [hcongr]
        exact Finset.sum_fiberwise_of_maps_to (fun u _ => Finset.mem_univ (send u)) _
      rw [hpart, Fintype.sum_prod_type]
    linarith
  have hcs := weighted_cs (Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)))
    (fun p => ((cls send p.1).card : ℚ))
    (fun p => ((cls send p.1).card : ℚ)⁻¹ * (sign (read p.1 p.2) * ∑ u ∈ cls send p.1, T u p.2))
    (fun p _ => Nat.cast_nonneg _)
  have hsq1 : (bias * N ^ 2) ^ 2 ≤
      (∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
        ((cls send p.1).card : ℚ)) *
      (∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
        ((cls send p.1).card : ℚ) *
          (((cls send p.1).card : ℚ)⁻¹ *
            (sign (read p.1 p.2) * ∑ u ∈ cls send p.1, T u p.2)) ^ 2) := by
    have hnn : 0 ≤ bias * N ^ 2 := mul_nonneg hbias.le (sq_nonneg N)
    exact (pow_le_pow_left₀ hnn hadv 2).trans hcs
  have hWsum : ∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
      ((cls send p.1).card : ℚ) = N ^ 2 := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, ← Nat.cast_sum, sum_cls_card]
    dsimp [N]
    ring
  have hRsum : ∑ p ∈ Cpos send ×ˢ (Finset.univ : Finset (Fin m → Fin q)),
      ((cls send p.1).card : ℚ) *
        (((cls send p.1).card : ℚ)⁻¹ *
          (sign (read p.1 p.2) * ∑ u ∈ cls send p.1, T u p.2)) ^ 2 =
      N * ∑ c ∈ Cpos send, ((cls send c).card : ℚ)⁻¹ *
        ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2 := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcpos : 0 < (cls send c).card := by
      simp only [Cpos, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc
    have hne : ((cls send c).card : ℚ) ≠ 0 := (Nat.cast_pos.mpr hcpos).ne'
    have hpt : ∀ v : Fin m → Fin q,
        ((cls send c).card : ℚ) *
          (((cls send c).card : ℚ)⁻¹ * (sign (read c v) * ∑ u ∈ cls send c, T u v)) ^ 2 =
        ((cls send c).card : ℚ)⁻¹ * (∑ u ∈ cls send c, T u v) ^ 2 := by
      intro v
      rw [mul_pow, mul_pow, sign_sq, one_mul, sq (((cls send c).card : ℚ)⁻¹),
        ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    dsimp only
    simp_rw [hpt, ← Finset.mul_sum]
    have hsqsum : ∑ v : Fin m → Fin q, (∑ u ∈ cls send c, T u v) ^ 2 =
        N * ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2 := by
      have hexp : ∀ v : Fin m → Fin q, (∑ u ∈ cls send c, T u v) ^ 2 =
          ∑ p ∈ cls send c ×ˢ cls send c, T p.1 v * T p.2 v := by
        intro v
        rw [sq, Finset.sum_mul_sum, Finset.sum_product]
      simp_rw [hexp]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      exact row_corr hq p.1 p.2
    rw [hsqsum]
    ring
  rw [hWsum, hRsum] at hsq1
  have hclass_le : ∀ c ∈ Cpos send,
      ((cls send c).card : ℚ)⁻¹ * ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2 ≤
        ((cls send c).card : ℚ) * ρ ^ (2 * r + 2) +
          ((cls send c).card : ℚ) * qClass (cls send c) (2 * r + 1) := by
    intro c hc
    have hcpos : 0 < (cls send c).card := by
      simp only [Cpos, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc
    have hne : ((cls send c).card : ℚ) ≠ 0 := (Nat.cast_pos.mpr hcpos).ne'
    have hpt : ∀ p ∈ cls send c ×ˢ cls send c,
        ρ ^ hdist p.1 p.2 ≤
          ρ ^ (2 * r + 2) + (if hdist p.1 p.2 ≤ 2 * r + 1 then (1 : ℚ) else 0) := by
      intro p _
      by_cases hd : hdist p.1 p.2 ≤ 2 * r + 1
      · simp only [hd, ↓reduceIte]
        have h1 : ρ ^ hdist p.1 p.2 ≤ 1 := pow_le_one₀ hρ0 hρ1
        have h2 : 0 ≤ ρ ^ (2 * r + 2) := pow_nonneg hρ0 _
        linarith
      · simp only [hd, ↓reduceIte, add_zero]
        exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    have hsumle : ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2 ≤
        ((cls send c).card : ℚ) ^ 2 * ρ ^ (2 * r + 2) +
          (pairCount (cls send c) (2 * r + 1) : ℚ) := by
      calc ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2
          ≤ ∑ p ∈ cls send c ×ˢ cls send c,
              (ρ ^ (2 * r + 2) + (if hdist p.1 p.2 ≤ 2 * r + 1 then (1 : ℚ) else 0)) :=
            Finset.sum_le_sum hpt
        _ = ((cls send c).card : ℚ) ^ 2 * ρ ^ (2 * r + 2) +
              (pairCount (cls send c) (2 * r + 1) : ℚ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_product, nsmul_eq_mul,
              Nat.cast_mul, sq, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
              nsmul_eq_mul, mul_one]
            rfl
    have hmul := mul_le_mul_of_nonneg_left hsumle
      (inv_nonneg.mpr (Nat.cast_nonneg (cls send c).card))
    have hrew : ((cls send c).card : ℚ)⁻¹ *
        (((cls send c).card : ℚ) ^ 2 * ρ ^ (2 * r + 2) +
          (pairCount (cls send c) (2 * r + 1) : ℚ)) =
        ((cls send c).card : ℚ) * ρ ^ (2 * r + 2) +
          ((cls send c).card : ℚ) * qClass (cls send c) (2 * r + 1) := by
      unfold qClass
      rw [mul_add, sq ((cls send c).card : ℚ), ← mul_assoc, ← mul_assoc,
        inv_mul_cancel₀ hne, one_mul, div_eq_mul_inv, mul_inv]
      have hterm2 : ((cls send c).card : ℚ) * ((pairCount (cls send c) (2 * r + 1) : ℚ) *
          (((cls send c).card : ℚ)⁻¹ * ((cls send c).card : ℚ)⁻¹)) =
          ((cls send c).card : ℚ)⁻¹ * (pairCount (cls send c) (2 * r + 1) : ℚ) := by
        calc ((cls send c).card : ℚ) * ((pairCount (cls send c) (2 * r + 1) : ℚ) *
              (((cls send c).card : ℚ)⁻¹ * ((cls send c).card : ℚ)⁻¹))
            = (((cls send c).card : ℚ) * ((cls send c).card : ℚ)⁻¹) *
                (((cls send c).card : ℚ)⁻¹ * (pairCount (cls send c) (2 * r + 1) : ℚ)) := by ring
          _ = 1 * (((cls send c).card : ℚ)⁻¹ * (pairCount (cls send c) (2 * r + 1) : ℚ)) := by
              rw [mul_inv_cancel₀ hne]
          _ = ((cls send c).card : ℚ)⁻¹ * (pairCount (cls send c) (2 * r + 1) : ℚ) := one_mul _
      rw [hterm2]
    linarith
  have hsum_bound : ∑ c ∈ Cpos send, ((cls send c).card : ℚ)⁻¹ *
        ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2 ≤
      N * (ρ ^ (2 * r + 2) + Qval send (2 * r + 1)) := by
    calc ∑ c ∈ Cpos send, ((cls send c).card : ℚ)⁻¹ *
            ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2
        ≤ ∑ c ∈ Cpos send, (((cls send c).card : ℚ) * ρ ^ (2 * r + 2) +
            ((cls send c).card : ℚ) * qClass (cls send c) (2 * r + 1)) :=
          Finset.sum_le_sum hclass_le
      _ = (∑ c ∈ Cpos send, ((cls send c).card : ℚ)) * ρ ^ (2 * r + 2) +
            ∑ c ∈ Cpos send, ((cls send c).card : ℚ) * qClass (cls send c) (2 * r + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = N * (ρ ^ (2 * r + 2) + Qval send (2 * r + 1)) := by
          have h1 : ∑ c ∈ Cpos send, ((cls send c).card : ℚ) = N := by
            rw [← Nat.cast_sum, sum_cls_card]
          have h2 : N * Qval send (2 * r + 1) =
              ∑ c ∈ Cpos send, ((cls send c).card : ℚ) * qClass (cls send c) (2 * r + 1) := by
            unfold Qval
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            have hNne : N ≠ 0 := hNpos.ne'
            dsimp [N] at hNne ⊢
            rw [← mul_assoc, mul_div_cancel₀ _ hNne]
          rw [h1, mul_add, h2]
  have hcomb : bias ^ 2 * N ^ 4 ≤ (ρ ^ (2 * r + 2) + Qval send (2 * r + 1)) * N ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hsum_bound
      (mul_nonneg (sq_nonneg N) hNpos.le)
    linarith [hsq1, hmul]
  have hN4 : (0 : ℚ) < N ^ 4 := pow_pos hNpos 4
  exact le_of_mul_le_mul_right hcomb hN4

private def decay (δ : ℚ) : Nat → ℚ
  | 0 => δ
  | k + 1 => (decay δ k) ^ 2 / 2

private lemma decay_pos {δ : ℚ} (hδ : 0 < δ) : ∀ k, 0 < decay δ k
  | 0 => hδ
  | k + 1 => by
    have ih := decay_pos hδ k
    unfold decay
    exact div_pos (pow_pos ih 2) (by linarith)

private lemma decay_le_one {δ : ℚ} (h0 : 0 < δ) (h1 : δ ≤ 1) : ∀ k, decay δ k ≤ 1
  | 0 => h1
  | k + 1 => by
    have hp := decay_pos h0 k
    have ih := decay_le_one h0 h1 k
    unfold decay
    nlinarith

private lemma decay_antitone {δ : ℚ} (h0 : 0 < δ) (h1 : δ ≤ 1) {j k : Nat} (hjk : j ≤ k) :
    decay δ k ≤ decay δ j := by
  induction hjk with
  | refl => exact le_rfl
  | @step m' _ ih =>
    have hp := decay_pos h0 m'
    have hle := decay_le_one h0 h1 m'
    change (decay δ m') ^ 2 / 2 ≤ decay δ j
    nlinarith

private lemma iter_decay {δ x : ℚ} {Q : Nat → ℚ} {L : Nat}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hQL : δ ≤ Q L) (hQ0 : Q 0 ≤ x)
    (hstep : ∀ l, 1 ≤ l → l ≤ L → (Q l) ^ 2 ≤ Q (l - 1) + x) :
    decay δ L ≤ x := by
  by_contra hlt
  push Not at hlt
  have hback : ∀ k, k ≤ L → decay δ k ≤ Q (L - k) := by
    intro k
    induction k with
    | zero => intro _; simpa [decay] using hQL
    | succ k ih =>
      intro hk
      have hkL : k ≤ L := Nat.le_of_succ_le hk
      have hQlk := ih hkL
      have hl1 : 1 ≤ L - k := by omega
      have hl2 : L - k ≤ L := by omega
      have hst := hstep (L - k) hl1 hl2
      have hsub : L - k - 1 = L - (k + 1) := by omega
      rw [hsub] at hst
      have hdkpos := decay_pos hδ0 k
      have hsq : (decay δ k) ^ 2 ≤ (Q (L - k)) ^ 2 :=
        pow_le_pow_left₀ hdkpos.le hQlk 2
      have hdec : decay δ L ≤ decay δ (k + 1) := decay_antitone hδ0 hδ1 hk
      have hxlt : x < (decay δ k) ^ 2 / 2 := lt_of_lt_of_le hlt hdec
      unfold decay
      linarith
  have h0 := hback L le_rfl
  simp only [Nat.sub_self] at h0
  linarith

private lemma lower_bound_works0 {q r : Nat} {bias : ℚ} (hq : 5 ≤ q)
    (hlo : (1 - 4 / (q : ℚ)) ^ (r + 1) < bias) (hhi : bias ≤ (1 - 4 / (q : ℚ)) ^ r) :
    let δ : ℚ := bias ^ 2 - (1 - 4 / (q : ℚ)) ^ (2 * r + 2)
    let C1 : Nat := (decay δ (2 * r + 1)).den * q ^ (5 * r + 2)
    0 < C1 ∧ ∀ m : Nat, 0 < m → ∀ M : Nat, works0 m q bias M →
      q ^ m ≤ C1 * M * m ^ r := by
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  let δ : ℚ := bias ^ 2 - ρ ^ (2 * r + 2)
  let K : Nat := q ^ (5 * r + 2)
  let C1 : Nat := (decay δ (2 * r + 1)).den * K
  have hqpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr (by omega)
  have hρpos : 0 < ρ := by
    have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    have h4 : 4 / (q : ℚ) ≤ 4 / 5 := (div_le_iff₀ hqpos).mpr (by linarith)
    dsimp [ρ]
    linarith
  have hρle1 : ρ ≤ 1 := by
    have h4 : 0 ≤ 4 / (q : ℚ) := div_nonneg (by linarith) hqpos.le
    dsimp [ρ]
    linarith
  have hbias_pos : 0 < bias := lt_trans (pow_pos hρpos _) hlo
  have hbias_le1 : bias ≤ 1 := hhi.trans (pow_le_one₀ hρpos.le hρle1)
  have hδ0 : 0 < δ := by
    have hpow : ρ ^ (2 * r + 2) = (ρ ^ (r + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
    have hsq : (ρ ^ (r + 1)) ^ 2 < bias ^ 2 :=
      pow_lt_pow_left₀ hlo (pow_nonneg hρpos.le _) (by omega)
    dsimp [δ]
    linarith
  have hδ1 : δ ≤ 1 := by
    have : 0 ≤ ρ ^ (2 * r + 2) := pow_nonneg hρpos.le _
    dsimp [δ]
    nlinarith
  refine ⟨Nat.mul_pos (Rat.den_pos _) (Nat.pow_pos (by omega)), ?_⟩
  intro m hm M hworks
  rcases hworks with ⟨send, read, hcorr⟩
  have hQL : δ ≤ Qval send (2 * r + 1) := by
    have hb := bias_sq_le_Qval (r := r) hq hbias_pos send read hcorr
    dsimp [δ, ρ]
    linarith
  let x : ℚ := ((K * M * m ^ r : Nat) : ℚ) / ((q ^ m : Nat) : ℚ)
  have hQ0 : Qval send 0 ≤ x := by
    have h0 := Qval_zero_le send
    have hle : M ≤ K * M * m ^ r := by
      have hK1 : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
      have hm1 : 1 ≤ m ^ r := Nat.one_le_pow _ _ hm
      calc M = 1 * M * 1 := by ring
        _ ≤ K * M * m ^ r := Nat.mul_le_mul (Nat.mul_le_mul_right M hK1) hm1
    have hleQ : (M : ℚ) ≤ ((K * M * m ^ r : Nat) : ℚ) := by exact_mod_cast hle
    exact h0.trans (div_le_div_of_nonneg_right hleQ (Nat.cast_nonneg _))
  have hstep : ∀ l, 1 ≤ l → l ≤ 2 * r + 1 → (Qval send l) ^ 2 ≤ Qval send (l - 1) + x := by
    intro l hl1 hl2
    have hqsq := Qval_sq_le hm (by omega) send l hl1
    have hmon : q ^ (2 * l + l / 2) * m ^ (l / 2) * M ≤ K * M * m ^ r := by
      have hqpow : q ^ (2 * l + l / 2) ≤ K :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hmpow : m ^ (l / 2) ≤ m ^ r :=
        Nat.pow_le_pow_right hm (by omega)
      calc q ^ (2 * l + l / 2) * m ^ (l / 2) * M
          ≤ K * m ^ r * M := Nat.mul_le_mul_right M (Nat.mul_le_mul hqpow hmpow)
        _ = K * M * m ^ r := by ring
    have hmonQ : ((q ^ (2 * l + l / 2) * m ^ (l / 2) * M : Nat) : ℚ) ≤
        ((K * M * m ^ r : Nat) : ℚ) := by exact_mod_cast hmon
    have hdiv := div_le_div_of_nonneg_right hmonQ (Nat.cast_nonneg (α := ℚ) (q ^ m))
    linarith
  have hdec_le : decay δ (2 * r + 1) ≤ x := iter_decay hδ0 hδ1 hQL hQ0 hstep
  have hdpos : 0 < decay δ (2 * r + 1) := decay_pos hδ0 _
  have hnum : (1 : ℚ) ≤ ((decay δ (2 * r + 1)).num : ℚ) := by
    have hni : 0 < (decay δ (2 * r + 1)).num := Rat.num_pos.mpr hdpos
    have hni1 : (1 : ℤ) ≤ (decay δ (2 * r + 1)).num := hni
    exact_mod_cast hni1
  have hdenpos : (0 : ℚ) < ((decay δ (2 * r + 1)).den : ℚ) :=
    Nat.cast_pos.mpr (Rat.den_pos (decay δ (2 * r + 1)))
  have hinv_le : 1 / ((decay δ (2 * r + 1)).den : ℚ) ≤ decay δ (2 * r + 1) := by
    calc 1 / ((decay δ (2 * r + 1)).den : ℚ)
        ≤ ((decay δ (2 * r + 1)).num : ℚ) / ((decay δ (2 * r + 1)).den : ℚ) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
      _ = decay δ (2 * r + 1) := Rat.num_div_den _
  have hfrac : 1 / ((decay δ (2 * r + 1)).den : ℚ) ≤
      ((K * M * m ^ r : Nat) : ℚ) / ((q ^ m : Nat) : ℚ) := hinv_le.trans hdec_le
  have hNpos : (0 : ℚ) < ((q ^ m : Nat) : ℚ) := Nat.cast_pos.mpr (Nat.pow_pos (by omega))
  have hmul : ((q ^ m : Nat) : ℚ) ≤
      ((decay δ (2 * r + 1)).den : ℚ) * ((K * M * m ^ r : Nat) : ℚ) := by
    have h1 := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hdenpos.le hNpos.le)
    have hdne : ((decay δ (2 * r + 1)).den : ℚ) ≠ 0 := hdenpos.ne'
    have hNne : ((q ^ m : Nat) : ℚ) ≠ 0 := hNpos.ne'
    have hlhs : ((decay δ (2 * r + 1)).den : ℚ) * ((q ^ m : Nat) : ℚ) *
        (1 / ((decay δ (2 * r + 1)).den : ℚ)) = ((q ^ m : Nat) : ℚ) := by
      rw [mul_comm ((decay δ (2 * r + 1)).den : ℚ) ((q ^ m : Nat) : ℚ), mul_assoc,
        mul_one_div_cancel hdne, mul_one]
    have hrhs : ((decay δ (2 * r + 1)).den : ℚ) * ((q ^ m : Nat) : ℚ) *
        (((K * M * m ^ r : Nat) : ℚ) / ((q ^ m : Nat) : ℚ)) =
        ((decay δ (2 * r + 1)).den : ℚ) * ((K * M * m ^ r : Nat) : ℚ) := by
      rw [mul_assoc, mul_div_cancel₀ _ hNne]
    linarith
  have hnat : q ^ m ≤ (decay δ (2 * r + 1)).den * (K * M * m ^ r) := by
    rw [← Nat.cast_mul] at hmul
    exact Nat.cast_le.mp hmul
  calc q ^ m ≤ (decay δ (2 * r + 1)).den * (K * M * m ^ r) := hnat
    _ = C1 * M * m ^ r := by dsimp [C1]; ring

private def digit (q j b : Nat) : Nat :=
  (j / q ^ b) % q

private def baseVal (q t : Nat) (s : Fin t → Nat) : Nat :=
  ∑ b : Fin t, s b * q ^ b.val

private lemma baseVal_lt {q : Nat} (hq : 2 ≤ q) :
    ∀ (t : Nat) (s : Fin t → Nat), (∀ b, s b < q) → baseVal q t s < q ^ t
  | 0, _, _ => by simp [baseVal]
  | t + 1, s, hs => by
    unfold baseVal
    rw [Fin.sum_univ_castSucc]
    have ih := baseVal_lt hq t (fun b => s b.castSucc) (fun b => hs b.castSucc)
    have hlast : s (Fin.last t) ≤ q - 1 := Nat.le_sub_one_of_lt (hs (Fin.last t))
    have hmul : s (Fin.last t) * q ^ t ≤ (q - 1) * q ^ t := Nat.mul_le_mul_right _ hlast
    have hpow : q ^ t + (q - 1) * q ^ t = q ^ (t + 1) := by
      rw [pow_succ']
      have : 1 + (q - 1) = q := by omega
      calc q ^ t + (q - 1) * q ^ t = (1 + (q - 1)) * q ^ t := by ring
        _ = q * q ^ t := by rw [this]
    change baseVal q t (fun b => s b.castSucc) + s (Fin.last t) * q ^ t < q ^ (t + 1)
    omega

private lemma digit_baseVal {q : Nat} (hq : 2 ≤ q) :
    ∀ (t : Nat) (s : Fin t → Nat), (∀ b, s b < q) →
      ∀ b : Fin t, digit q (baseVal q t s) b.val = s b
  | 0, _, _, b => Fin.elim0 b
  | t + 1, s, hs, b => by
    have hsplit : baseVal q (t + 1) s =
        baseVal q t (fun a => s a.castSucc) + s (Fin.last t) * q ^ t := by
      unfold baseVal
      rw [Fin.sum_univ_castSucc]
      rfl
    have hlo := baseVal_lt hq t (fun a => s a.castSucc) (fun a => hs a.castSucc)
    refine Fin.lastCases ?_ ?_ b
    · unfold digit
      rw [hsplit, Fin.val_last, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)),
        Nat.div_eq_of_lt hlo, zero_add, Nat.mod_eq_of_lt (hs (Fin.last t))]
    · intro b'
      unfold digit
      rw [hsplit, Fin.val_castSucc]
      have hpow : q ^ t = q ^ b'.val * (q * q ^ (t - b'.val - 1)) := by
        have hexp : b'.val + (t - b'.val - 1 + 1) = t := by have := b'.isLt; omega
        rw [← pow_succ', ← pow_add, hexp]
      rw [hpow, ← mul_assoc, mul_comm (s (Fin.last t)), mul_assoc,
        Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)),
        show s (Fin.last t) * (q * q ^ (t - b'.val - 1)) =
          q * (s (Fin.last t) * q ^ (t - b'.val - 1)) by ring,
        Nat.add_mul_mod_self_left]
      exact digit_baseVal hq t (fun a => s a.castSucc) (fun a => hs a.castSucc) b'

private lemma digit_pow {q : Nat} (hq : 2 ≤ q) (a b : Nat) :
    digit q (q ^ a) b = if a = b then 1 else 0 := by
  unfold digit
  by_cases hab : a = b
  · subst hab
    rw [Nat.div_self (Nat.pow_pos (by omega)), Nat.mod_eq_of_lt (by omega)]
    simp
  · simp only [hab, ↓reduceIte]
    by_cases hlt : a < b
    · have hp : q ^ a < q ^ b := Nat.pow_lt_pow_right hq hlt
      rw [Nat.div_eq_of_lt hp, Nat.zero_mod]
    · have hgt : b < a := by omega
      have hpow : q ^ a = q ^ b * (q * q ^ (a - b - 1)) := by
        have hexp : b + (a - b - 1 + 1) = a := by omega
        rw [← pow_succ', ← pow_add, hexp]
      rw [hpow, Nat.mul_div_right _ (Nat.pow_pos (by omega)), Nat.mul_mod_right]

private lemma lt_pow_self {q : Nat} (hq : 2 ≤ q) : ∀ t : Nat, t < q ^ t
  | 0 => by simp
  | t + 1 => by
    have ih := lt_pow_self hq t
    have hpow : q ^ (t + 1) = q * q ^ t := pow_succ' q t
    have h2 : 2 * q ^ t ≤ q * q ^ t := Nat.mul_le_mul_right _ hq
    omega

private lemma exists_pow_le_lt {q : Nat} (hq : 2 ≤ q) :
    ∀ n : Nat, 0 < n → ∃ t : Nat, q ^ t ≤ n ∧ n < q ^ (t + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases hnq : n < q
    · exact ⟨0, by rw [pow_zero]; omega, by simpa using hnq⟩
    · have hdiv_pos : 0 < n / q := Nat.div_pos (by omega) (by omega)
      have hdiv_lt : n / q < n := Nat.div_lt_self hn (by omega)
      rcases ih (n / q) hdiv_lt hdiv_pos with ⟨t, h1, h2⟩
      refine ⟨t + 1, ?_, ?_⟩
      · calc q ^ (t + 1) = q * q ^ t := pow_succ' q t
          _ ≤ q * (n / q) := Nat.mul_le_mul_left q h1
          _ ≤ n := Nat.mul_div_le n q
      · have hrem : n < q * (n / q + 1) := by
          have := Nat.div_add_mod n q
          have := Nat.mod_lt n (show 0 < q by omega)
          nlinarith
        calc n < q * (n / q + 1) := hrem
          _ ≤ q * q ^ (t + 1) := Nat.mul_le_mul_left q h2
          _ = q ^ (t + 2) := (pow_succ' q (t + 1)).symm

private lemma mod_eq_zero_of_add_mod {x s q : Nat} (hx : x < q) (hs : s < q)
    (h : (x + s) % q = s) : x = 0 := by
  by_cases hlt : x + s < q
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hsub : (x + s) % q = x + s - q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private lemma sub_mod_eq_of_add_mod_zero {v r q : Nat} (hv : v < q) (hr : r < q)
    (h : (v + r) % q = 0) : (q - r) % q = v := by
  by_cases hr0 : r = 0
  · subst hr0
    rw [Nat.sub_zero, Nat.mod_self]
    rw [Nat.add_zero, Nat.mod_eq_of_lt hv] at h
    exact h.symm
  · have hlt : q - r < q := by omega
    rw [Nat.mod_eq_of_lt hlt]
    by_cases hsum : v + r < q
    · rw [Nat.mod_eq_of_lt hsum] at h
      omega
    · have hsub : (v + r) % q = v + r - q := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

private def syndrome {q n t : Nat} (hqt : q ^ t ≤ n) (x : Fin n → Fin q) (b : Fin t) : Nat :=
  (∑ j : Fin (q ^ t), (x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val) % q

private def jStar {q n t : Nat} (hqt : q ^ t ≤ n) (x : Fin n → Fin q) : Nat :=
  baseVal q t (syndrome hqt x)

private lemma jStar_lt {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (x : Fin n → Fin q) :
    jStar hqt x < q ^ t :=
  baseVal_lt (by omega) t (syndrome hqt x) (fun b => Nat.mod_lt _ (by omega))

private def correctBlock {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (x : Fin n → Fin q) :
    Fin n → Fin q :=
  fun j => if j.val = jStar hqt x
    then ⟨((x j).val + q - 1) % q, Nat.mod_lt _ (by omega)⟩
    else x j

private lemma syndrome_correctBlock {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n)
    (x : Fin n → Fin q) (b : Fin t) :
    syndrome hqt (correctBlock hq hqt x) b = 0 := by
  let j0 : Fin (q ^ t) := ⟨jStar hqt x, jStar_lt hq hqt x⟩
  let s : Nat := syndrome hqt x b
  have hs_lt : s < q := Nat.mod_lt _ (by omega)
  have hdig : digit q j0.val b.val = s :=
    digit_baseVal (by omega) t (syndrome hqt x) (fun a => Nat.mod_lt _ (by omega)) b
  have hsum_x := Finset.add_sum_erase Finset.univ
    (fun j : Fin (q ^ t) => (x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val)
    (Finset.mem_univ j0)
  have hsum_w := Finset.add_sum_erase Finset.univ
    (fun j : Fin (q ^ t) =>
      (correctBlock hq hqt x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val)
    (Finset.mem_univ j0)
  have hrest : ∑ j ∈ Finset.univ.erase j0,
      (correctBlock hq hqt x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val =
      ∑ j ∈ Finset.univ.erase j0,
        (x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j.val ≠ jStar hqt x := fun heq => (Finset.ne_of_mem_erase hj) (Fin.ext heq)
    simp [correctBlock, hne]
  let a : Nat := (x ⟨j0.val, lt_of_lt_of_le j0.isLt hqt⟩).val
  have ha_lt : a < q := (x ⟨j0.val, lt_of_lt_of_le j0.isLt hqt⟩).isLt
  have hmod1 : ((a + q - 1) % q + 1) % q = a := by
    by_cases ha0 : a = 0
    · rw [ha0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : q - 1 < q)]
      have h2 : q - 1 + 1 = q := by omega
      rw [h2, Nat.mod_self]
    · have h1 : (a + q - 1) % q = a - 1 := by
        have h1' : a + q - 1 = (a - 1) + q := by omega
        rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      have h2 : a - 1 + 1 = a := by omega
      rw [h2, Nat.mod_eq_of_lt ha_lt]
  have hmod2 : (((a + q - 1) % q) * s + s) % q = (a * s) % q := by
    have h1 : ((a + q - 1) % q) * s + s = ((a + q - 1) % q + 1) * s := by ring
    calc (((a + q - 1) % q) * s + s) % q
        = (((a + q - 1) % q + 1) * s) % q := by rw [h1]
      _ = (((a + q - 1) % q + 1) % q * (s % q)) % q := Nat.mul_mod _ _ _
      _ = (a % q * (s % q)) % q := by rw [hmod1, Nat.mod_eq_of_lt ha_lt]
      _ = (a * s) % q := (Nat.mul_mod a s q).symm
  let R := ∑ j ∈ Finset.univ.erase j0,
    (x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val
  have hSw : ∑ j : Fin (q ^ t),
      (correctBlock hq hqt x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val =
      ((a + q - 1) % q) * s + R := by
    rw [← hsum_w, hrest, hdig]
    simp only [correctBlock, j0, ↓reduceIte]
    rfl
  have hSx : ∑ j : Fin (q ^ t),
      (x ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩).val * digit q j.val b.val = a * s + R := by
    rw [← hsum_x, hdig]
  have haddmod : ((((a + q - 1) % q) * s + R) + s) % q = s := by
    have h1 : (((a + q - 1) % q) * s + R) + s = (((a + q - 1) % q) * s + s) + R := by ring
    rw [h1, Nat.add_mod, hmod2, ← Nat.add_mod, ← hSx]
    rfl
  unfold syndrome
  rw [hSw]
  have hfin := haddmod
  rw [Nat.add_mod, Nat.mod_eq_of_lt hs_lt] at hfin
  exact mod_eq_zero_of_add_mod (Nat.mod_lt _ (by omega)) hs_lt hfin

private abbrev NonPivot (q n t : Nat) : Type :=
  {j : Fin n // ∀ a : Fin t, j.val ≠ q ^ a.val}

private lemma card_NonPivot {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) :
    Fintype.card (NonPivot q n t) = n - t := by
  let f : Fin t → Fin n := fun a =>
    ⟨q ^ a.val, lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) a.isLt) hqt⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hval : q ^ a.val = q ^ b.val := congrArg Fin.val hab
    have hnat : a.val = b.val := Nat.pow_right_injective (by omega) hval
    exact Fin.ext hnat
  have hcard_img : (Finset.univ.image f).card = t := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have heq : (Finset.univ : Finset (Fin n)).filter (fun j => ∀ a : Fin t, j.val ≠ q ^ a.val) =
      Finset.univ \ Finset.univ.image f := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image,
      not_exists]
    constructor
    · intro hj a hfa
      exact hj a (congrArg Fin.val hfa).symm
    · intro hj a hval
      exact hj a (Fin.ext hval.symm)
  rw [Fintype.card_subtype, heq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin, hcard_img]

private noncomputable def reconstructBlock {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n)
    (y : NonPivot q n t → Fin q) : Fin n → Fin q :=
  fun j =>
    if hj : ∀ a : Fin t, j.val ≠ q ^ a.val then
      y ⟨j, hj⟩
    else
      let a : Fin t := Classical.choose (by
        push Not at hj; exact hj : ∃ a : Fin t, j.val = q ^ a.val)
      let rem : Nat := ∑ k : Fin (q ^ t),
        if hk : ∀ a' : Fin t, k.val ≠ q ^ a'.val then
          (y ⟨⟨k.val, lt_of_lt_of_le k.isLt hqt⟩, hk⟩).val * digit q k.val a.val
        else 0
      ⟨(q - rem % q) % q, Nat.mod_lt _ (by omega)⟩

private lemma reconstructBlock_eq {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n)
    (w : Fin n → Fin q) (hsyn : ∀ b : Fin t, syndrome hqt w b = 0) :
    reconstructBlock hq hqt (fun j => w j.val) = w := by
  funext j
  dsimp [reconstructBlock]
  split_ifs with hj
  · rfl
  · have hex : ∃ a : Fin t, j.val = q ^ a.val := by push Not at hj; exact hj
    let a : Fin t := Classical.choose hex
    have ha : j.val = q ^ a.val := Classical.choose_spec hex
    let k0 : Fin (q ^ t) := ⟨q ^ a.val, Nat.pow_lt_pow_right (by omega) a.isLt⟩
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun k : Fin (q ^ t) =>
        (w ⟨k.val, lt_of_lt_of_le k.isLt hqt⟩).val * digit q k.val a.val)
      (Finset.mem_univ k0)
    have hk0_term :
        (w ⟨k0.val, lt_of_lt_of_le k0.isLt hqt⟩).val * digit q k0.val a.val = (w j).val := by
      have hjeq : (⟨k0.val, lt_of_lt_of_le k0.isLt hqt⟩ : Fin n) = j := Fin.ext ha.symm
      rw [hjeq, show digit q k0.val a.val = 1 by simp [k0, digit_pow (by omega : 2 ≤ q)], mul_one]
    let rem : Nat := ∑ k : Fin (q ^ t),
      if hk : ∀ a' : Fin t, k.val ≠ q ^ a'.val then
        (w ⟨k.val, lt_of_lt_of_le k.isLt hqt⟩).val * digit q k.val a.val
      else 0
    have hrem_eq : ∑ k ∈ Finset.univ.erase k0,
        (w ⟨k.val, lt_of_lt_of_le k.isLt hqt⟩).val * digit q k.val a.val = rem := by
      have hrem_split := Finset.add_sum_erase Finset.univ
        (fun k : Fin (q ^ t) =>
          if hk : ∀ a' : Fin t, k.val ≠ q ^ a'.val then
            (w ⟨k.val, lt_of_lt_of_le k.isLt hqt⟩).val * digit q k.val a.val
          else 0)
        (Finset.mem_univ k0)
      have hk0_zero : (if hk : ∀ a' : Fin t, k0.val ≠ q ^ a'.val then
          (w ⟨k0.val, lt_of_lt_of_le k0.isLt hqt⟩).val * digit q k0.val a.val
        else 0) = 0 := by
        rw [dite_eq_right_iff]
        intro hall
        exact absurd rfl (hall a)
      dsimp only [rem]
      rw [← hrem_split, hk0_zero, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      split_ifs with hnp
      · rfl
      · push Not at hnp
        rcases hnp with ⟨a', ha'⟩
        have hne : a' ≠ a := by
          intro heq
          subst heq
          exact (Finset.ne_of_mem_erase hk) (Fin.ext ha')
        have hdig0 : digit q k.val a.val = 0 := by
          rw [ha', digit_pow (by omega : 2 ≤ q)]
          have hvalne : a'.val ≠ a.val := fun h => hne (Fin.ext h)
          simp [hvalne]
        rw [hdig0, mul_zero]
    have hsyn0 : ((w j).val + rem) % q = 0 := by
      have h0 := hsyn a
      unfold syndrome at h0
      rw [← hsplit, hk0_term, hrem_eq] at h0
      exact h0
    apply Fin.ext
    have hwlt : (w j).val < q := (w j).isLt
    have hrmlt : rem % q < q := Nat.mod_lt _ (by omega)
    rw [Nat.add_mod, Nat.mod_eq_of_lt hwlt] at hsyn0
    exact sub_mod_eq_of_add_mod_zero hwlt hrmlt hsyn0

private def prd {q : Nat} (hq : 5 ≤ q) (a : Fin q) : Fin q :=
  ⟨(a.val + q - 1) % q, Nat.mod_lt _ (by omega)⟩

private def idx {m r n : Nat} (hrn : r * n ≤ m) (k : Fin r) (j : Fin n) : Fin m :=
  ⟨k.val * n + j.val, by
    have hk := k.isLt; have hj := j.isLt
    have : (k.val + 1) * n ≤ r * n := Nat.mul_le_mul_right n hk
    nlinarith⟩

private def blk {m q r n : Nat} (hrn : r * n ≤ m) (u : Fin m → Fin q) (k : Fin r) :
    Fin n → Fin q :=
  fun j => u (idx hrn k j)

private def win {q n t : Nat} (hqt : q ^ t ≤ n) (j : Fin (q ^ t)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt hqt⟩

private def jIdx {q n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (v : Fin n → Fin q) : Fin (q ^ t) :=
  ⟨jStar hqt v, jStar_lt hq hqt v⟩

private def cpos {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (u : Fin m → Fin q) (k : Fin r) : Fin m :=
  idx hrn k (win hqt (jIdx hq hqt (blk hrn u k)))

private def corr {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (u : Fin m → Fin q) : Fin m → Fin q :=
  fun i => if ∃ k, cpos hq hqt hrn u k = i then prd hq (u i) else u i

private def xhat {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (x s : Fin m → Fin q) : Fin m → Fin q :=
  fun i => corr hq hqt hrn (fun i => x i + s i) i - s i

private def near {q : Nat} (hq : 5 ≤ q) (a b : Fin q) : Bool :=
  decide (b = a ∨ b = prd hq a)

private def stat {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (a y : Fin m → Fin q) (k : Fin r) : Nat :=
  ((Finset.univ : Finset (Fin (q ^ t))).filter (fun j =>
    near hq (a (idx hrn k (win hqt j))) (y (idx hrn k (win hqt j))) = true)).card

private def worksR (m q : Nat) (β : ℚ) (left right : (Fin m → Fin q) → Bool) (M : Nat) : Prop :=
  ∃ (z : Nat) (send : Fin z → (Fin m → Fin q) → Fin M)
    (read : Fin z → Fin M → (Fin m → Fin q) → Bool),
    0 < z ∧ ∀ x y, (1 + β) * (z : ℚ) ≤
      2 * (((Finset.univ : Finset (Fin z)).filter
        (fun seed => read seed (send seed x) y = xor (xor (left x) (right y)) (par x y))).card : ℚ)

private lemma cpos_val {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (u : Fin m → Fin q) (k : Fin r) :
    (cpos hq hqt hrn u k).val = k.val * n + jStar hqt (blk hrn u k) := rfl

private lemma exists_cpos_iff {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (hn : 0 < n) (u : Fin m → Fin q) (i : Fin m) :
    (∃ k, cpos hq hqt hrn u k = i) ↔ ∃ hi : i.val < r * n,
      i.val % n = jStar hqt (blk hrn u ⟨i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr hi⟩) := by
  constructor
  · rintro ⟨k, rfl⟩
    have hj : jStar hqt (blk hrn u k) < n := lt_of_lt_of_le (jStar_lt hq hqt _) hqt
    have hdiv : (k.val * n + jStar hqt (blk hrn u k)) / n = k.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (k.val * n + jStar hqt (blk hrn u k)) % n = jStar hqt (blk hrn u k) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have hlt : k.val * n + jStar hqt (blk hrn u k) < r * n := by
      have : (k.val + 1) * n ≤ r * n := Nat.mul_le_mul_right n k.isLt
      nlinarith
    refine ⟨hlt, ?_⟩
    simp only [cpos_val, hmod, hdiv]
  · rintro ⟨hi, hj⟩
    refine ⟨⟨i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr hi⟩, Fin.ext ?_⟩
    rw [cpos_val, ← hj]
    exact Nat.div_add_mod' i.val n

private lemma code_exists {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (hn : 0 < n) :
    ∃ (enc : (Fin m → Fin q) → Fin (q ^ (m - r * t)))
      (dec : Fin (q ^ (m - r * t)) → (Fin m → Fin q)),
      ∀ u, dec (enc u) = corr hq hqt hrn u := by
  have htn : t ≤ n := le_trans (Nat.le_of_lt (lt_pow_self (by omega : 2 ≤ q) t)) hqt
  have hcardRem : Fintype.card {i : Fin m // r * n ≤ i.val} = m - r * n := by
    let emb : Fin (r * n) → Fin m := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hrn⟩
    have hemb : Function.Injective emb := fun a b h =>
      Fin.ext (congrArg (Fin.val : Fin m → Nat) h)
    rw [Fintype.card_subtype]
    have heq : (Finset.univ : Finset (Fin m)).filter (fun i => r * n ≤ i.val) =
        Finset.univ \ (Finset.univ.image emb) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_image, not_exists]
      constructor
      · intro hi j hji
        have hval : j.val = i.val := congrArg Fin.val hji
        have hjlt := j.isLt
        omega
      · intro hi
        by_contra hlt
        push Not at hlt
        exact hi ⟨i.val, hlt⟩ rfl
    rw [heq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hemb, Finset.card_univ, Fintype.card_fin]
  have hM : Fintype.card ((Fin r → (NonPivot q n t → Fin q)) ×
      ({i : Fin m // r * n ≤ i.val} → Fin q)) = q ^ (m - r * t) := by
    have hcardNP := card_NonPivot hq hqt
    have h1 : Fintype.card ((Fin r → (NonPivot q n t → Fin q)) ×
        ({i : Fin m // r * n ≤ i.val} → Fin q)) = (q ^ (n - t)) ^ r * q ^ (m - r * n) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin, hcardNP, hcardRem]
    rw [h1, ← pow_mul, ← pow_add]
    congr 1
    have hrt : r * t ≤ r * n := Nat.mul_le_mul_left r htn
    have hmulsub : (n - t) * r = r * n - r * t := by
      rw [Nat.sub_mul, mul_comm n r, mul_comm t r]
    omega
  let e := (Fintype.equivFin ((Fin r → (NonPivot q n t → Fin q)) ×
    ({i : Fin m // r * n ≤ i.val} → Fin q))).trans (finCongr hM)
  let encode : (Fin m → Fin q) →
      ((Fin r → (NonPivot q n t → Fin q)) × ({i : Fin m // r * n ≤ i.val} → Fin q)) := fun u =>
    (fun k np => correctBlock hq hqt (blk hrn u k) np.val, fun i => u i.val)
  let decode : ((Fin r → (NonPivot q n t → Fin q)) × ({i : Fin m // r * n ≤ i.val} → Fin q)) →
      (Fin m → Fin q) := fun msg i =>
    if hi : i.val < r * n then
      reconstructBlock hq hqt (msg.1 ⟨i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr hi⟩)
        ⟨i.val % n, Nat.mod_lt _ hn⟩
    else
      msg.2 ⟨i, Nat.le_of_not_lt hi⟩
  refine ⟨fun u => e (encode u), fun c => decode (e.symm c), fun u => ?_⟩
  simp only [Equiv.symm_apply_apply]
  funext i
  by_cases hi : i.val < r * n
  · let k : Fin r := ⟨i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr hi⟩
    let j : Fin n := ⟨i.val % n, Nat.mod_lt _ hn⟩
    have hdec : decode (encode u) i = correctBlock hq hqt (blk hrn u k) j := by
      dsimp only [decode, encode]
      simp only [hi, ↓reduceDIte]
      exact congrFun (reconstructBlock_eq hq hqt (correctBlock hq hqt (blk hrn u k))
        (syndrome_correctBlock hq hqt (blk hrn u k))) j
    have hblk : blk hrn u k j = u i := by
      dsimp only [blk]
      congr 1
      exact Fin.ext (Nat.div_add_mod' i.val n)
    rw [hdec]
    dsimp only [corr, correctBlock]
    have hiff := exists_cpos_iff hq hqt hrn hn u i
    by_cases hex : ∃ k, cpos hq hqt hrn u k = i
    · obtain ⟨_, hj⟩ := hiff.mp hex
      have hj' : j.val = jStar hqt (blk hrn u k) := hj
      simp only [hex, hj', ↓reduceIte]
      exact congrArg (prd hq) hblk
    · have hj' : ¬ j.val = jStar hqt (blk hrn u k) := fun hj => hex (hiff.mpr ⟨hi, hj⟩)
      simp only [hex, hj', ↓reduceIte]
      exact hblk
  · have hno : ¬ ∃ k, cpos hq hqt hrn u k = i := by
      rw [exists_cpos_iff hq hqt hrn hn u i]
      exact fun ⟨h, _⟩ => hi h
    dsimp only [corr, decode, encode]
    simp only [hi, hno, ↓reduceDIte, ↓reduceIte]

private lemma prd_eq_sub_one {q : Nat} (hq : 5 ≤ q) [NeZero q] (a : Fin q) : prd hq a = a - 1 := by
  apply Fin.ext
  rw [Fin.sub_def]
  simp only [prd, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < q)]
  congr 1
  omega

private lemma prd_ne {q : Nat} (hq : 5 ≤ q) (a : Fin q) : prd hq a ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  have ha := a.isLt
  simp only [prd] at hv
  rcases Nat.eq_zero_or_pos a.val with h0 | hpos
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  · rw [show a.val + q - 1 = a.val - 1 + q by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at hv
    omega

private lemma idx_inj {m r n : Nat} (hrn : r * n ≤ m) {k k' : Fin r} {j j' : Fin n}
    (h : idx hrn k j = idx hrn k' j') : k = k' ∧ j = j' := by
  have h' : k.val * n + j.val = k'.val * n + j'.val := congrArg Fin.val h
  have hj : j.val = j'.val := by
    simpa only [Nat.mul_add_mod', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] using
      congrArg (· % n) h'
  exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right j.pos (by omega)), Fin.ext hj⟩

private lemma cpos_eq_idx {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    {u : Fin m → Fin q} {k k' : Fin r} {j : Fin (q ^ t)}
    (h : cpos hq hqt hrn u k' = idx hrn k (win hqt j)) :
    k' = k ∧ j = jIdx hq hqt (blk hrn u k) := by
  obtain ⟨hk, hj⟩ := idx_inj hrn h
  subst hk
  exact ⟨rfl, Fin.ext (congrArg Fin.val hj).symm⟩

private lemma cpos_injective {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (u : Fin m → Fin q) : Function.Injective (cpos hq hqt hrn u) :=
  fun _ _ h => (idx_inj hrn h).1

private lemma xhat_apply {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (x s : Fin m → Fin q) (i : Fin m) :
    xhat hq hqt hrn x s i =
      if ∃ k, cpos hq hqt hrn (fun i => x i + s i) k = i then prd hq (x i) else x i := by
  have : NeZero q := ⟨by omega⟩
  dsimp only [xhat, corr]
  split_ifs
  · rw [prd_eq_sub_one, prd_eq_sub_one, sub_right_comm, add_sub_cancel_right]
  · exact add_sub_cancel_right (x i) (s i)

private lemma flip_prod {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (x y s : Fin m → Fin q) :
    T (xhat hq hqt hrn x s) y * T x y =
      ∏ k : Fin r, (if near hq (x (cpos hq hqt hrn (fun i => x i + s i) k))
        (y (cpos hq hqt hrn (fun i => x i + s i) k)) then (-1 : ℚ) else 1) := by
  have hfac : ∀ i : Fin m, (if xhat hq hqt hrn x s i = y i then (-1 : ℚ) else 1) *
      (if x i = y i then -1 else 1) =
      if ∃ k, cpos hq hqt hrn (fun i => x i + s i) k = i then
        (if near hq (x i) (y i) then -1 else 1) else 1 := by
    intro i
    rw [xhat_apply]
    by_cases h : ∃ k, cpos hq hqt hrn (fun i => x i + s i) k = i
    · have hne := prd_ne hq (x i)
      simp only [h, ↓reduceIte, near]
      by_cases h1 : y i = x i
      · rw [h1]
        simp [hne]
      · by_cases h2 : y i = prd hq (x i)
        · rw [h2]
          simp [Ne.symm hne]
        · simp [Ne.symm h1, Ne.symm h2, h1, h2]
    · simp only [h, ↓reduceIte]
      split_ifs <;> norm_num
  rw [T_eq_prod, T_eq_prod, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hfac i),
    Finset.prod_ite, Finset.prod_const_one, mul_one]
  have himg : (Finset.univ.filter fun i => ∃ k, cpos hq hqt hrn (fun i => x i + s i) k = i) =
      Finset.univ.image (cpos hq hqt hrn (fun i => x i + s i)) := by
    ext i
    simp
  rw [himg, Finset.prod_image (fun a _ b _ h => cpos_injective hq hqt hrn _ h)]

private def piv {q t : Nat} (hq : 5 ≤ q) (a : Fin t) : Fin (q ^ t) :=
  ⟨q ^ a.val, Nat.pow_lt_pow_right (by omega) a.isLt⟩

private def pivSet {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m) :
    Finset (Fin m) :=
  (Finset.univ : Finset (Fin r × Fin t)).image (fun p => idx hrn p.1 (win hqt (piv hq p.2)))

private lemma card_pivSet {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m) :
    (pivSet hq hqt hrn).card = r * t := by
  rw [pivSet, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  rintro ⟨k, a⟩ ⟨k', a'⟩ h
  obtain ⟨rfl, hw⟩ := idx_inj hrn h
  have : q ^ a.val = q ^ a'.val := congrArg Fin.val hw
  rw [Fin.ext (Nat.pow_right_injective (by omega) this)]

private lemma syndrome_piv {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (w : Fin m → Fin q) (k : Fin r) (a : Fin t) :
    syndrome hqt (blk hrn w k) a = ((w (idx hrn k (win hqt (piv hq a)))).val +
      ∑ j ∈ Finset.univ.erase (piv hq a),
        (w (idx hrn k (win hqt j))).val * digit q j.val a.val) % q := by
  have h1 : digit q (piv hq a).val a.val = 1 := (digit_pow (by omega) _ _).trans (ite_eq_left rfl)
  show (∑ j : Fin (q ^ t), (w (idx hrn k (win hqt j))).val * digit q j.val a.val) % q = _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (piv hq a)), h1, mul_one]

private lemma eq_of_add_mod_eq {x y c q : Nat} (hx : x < q) (hy : y < q)
    (h : (x + c) % q = (y + c) % q) : x = y := by
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  rw [Nat.add_sub_add_right, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le x y) hx)] at h1
  rw [Nat.add_sub_add_right, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le y x) hy)] at h2
  omega

private lemma eq_of_piv {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    {u u' : Fin m → Fin q} (hj : ∀ k, jIdx hq hqt (blk hrn u k) = jIdx hq hqt (blk hrn u' k))
    (hoff : ∀ i, i ∉ pivSet hq hqt hrn → u i = u' i) : u = u' := by
  funext i
  by_cases hi : i ∈ pivSet hq hqt hrn
  swap
  · exact hoff i hi
  obtain ⟨⟨k, a⟩, -, rfl⟩ := Finset.mem_image.1 hi
  have hk : baseVal q t (syndrome hqt (blk hrn u k)) =
      baseVal q t (syndrome hqt (blk hrn u' k)) := congrArg Fin.val (hj k)
  have hs : ∀ (w : Fin m → Fin q) b, syndrome hqt (blk hrn w k) b < q :=
    fun _ _ => Nat.mod_lt _ (by omega)
  have hsyn : syndrome hqt (blk hrn u k) a = syndrome hqt (blk hrn u' k) a := by
    rw [← digit_baseVal (by omega) t _ (hs u), ← digit_baseVal (by omega) t _ (hs u'), hk]

  have hrest : ∀ j ∈ Finset.univ.erase (piv hq a),
      (u (idx hrn k (win hqt j))).val * digit q j.val a.val =
        (u' (idx hrn k (win hqt j))).val * digit q j.val a.val := by
    intro j hj0
    by_cases hp : idx hrn k (win hqt j) ∈ pivSet hq hqt hrn
    · obtain ⟨⟨k', a'⟩, -, he⟩ := Finset.mem_image.1 hp
      have hja : j.val = q ^ a'.val := (congrArg Fin.val (idx_inj hrn he).2).symm
      have haa : a'.val ≠ a.val := fun h =>
        Finset.ne_of_mem_erase hj0 (Fin.ext (hja.trans (congrArg (q ^ ·) h)))
      rw [hja, digit_pow (by omega), ite_eq_right haa, mul_zero, mul_zero]
    · rw [hoff _ hp]
  rw [syndrome_piv hq hqt hrn u k a, syndrome_piv hq hqt hrn u' k a,
    Finset.sum_congr rfl hrest] at hsyn
  exact Fin.ext (eq_of_add_mod_eq (Fin.isLt _) (Fin.isLt _) hsyn)

private lemma jIdx_uniform {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (j : Fin r → Fin (q ^ t)) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun u => ∀ k, jIdx hq hqt (blk hrn u k) = j k)).card = q ^ (m - r * t) := by
  have hrt : r * t ≤ m :=
    (Nat.mul_le_mul_left r ((lt_pow_self (by omega) t).le.trans hqt)).trans hrn
  let F : (Fin r → Fin (q ^ t)) → Finset (Fin m → Fin q) := fun j =>
    (Finset.univ : Finset (Fin m → Fin q)).filter (fun u => ∀ k, jIdx hq hqt (blk hrn u k) = j k)

  have hle : ∀ j, (F j).card ≤ q ^ (m - r * t) := by
    intro j
    calc (F j).card ≤ (Finset.univ : Finset ({i // i ∈ (pivSet hq hqt hrn)ᶜ} → Fin q)).card :=
          Finset.card_le_card_of_injOn (fun u i => u i)
            (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
            (fun u hu u' hu' h => eq_of_piv hq hqt hrn
              (fun k => ((Finset.mem_filter.1 hu).2 k).trans ((Finset.mem_filter.1 hu').2 k).symm)
              (fun i hi => congrFun h ⟨i, Finset.mem_compl.2 hi⟩))
      _ = q ^ (m - r * t) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
            card_pivSet, Fintype.card_fin, Fintype.card_fin]

  have hsum : ∑ j, (F j).card = ∑ _j : Fin r → Fin (q ^ t), q ^ (m - r * t) := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := fun u : Fin m → Fin q => fun k => jIdx hq hqt (blk hrn u k))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      smul_eq_mul, ← pow_mul, ← pow_add, Nat.mul_comm t r, Nat.add_sub_cancel' hrt, this]
    exact Finset.sum_congr rfl fun j _ => by simp only [F, funext_iff]
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).1 hsum j (Finset.mem_univ j)

private lemma xhat_win {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (x s : Fin m → Fin q) (k : Fin r) (j : Fin (q ^ t))
    (hj : j ≠ jIdx hq hqt (blk hrn (fun i => x i + s i) k)) :
    xhat hq hqt hrn x s (idx hrn k (win hqt j)) = x (idx hrn k (win hqt j)) := by
  rw [xhat_apply]
  split_ifs with h
  · obtain ⟨k', hk'⟩ := h
    obtain ⟨rfl, h'⟩ := cpos_eq_idx hq hqt hrn hk'
    exact absurd h' hj
  · rfl

private lemma card_filter_le_succ {α : Type*} [Fintype α] [DecidableEq α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (a : α) (h : ∀ j, j ≠ a → P j → Q j) :
    ((Finset.univ : Finset α).filter P).card ≤ ((Finset.univ : Finset α).filter Q).card + 1 := by
  calc ((Finset.univ : Finset α).filter P).card
      ≤ (insert a ((Finset.univ : Finset α).filter Q)).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases hja : j = a
        · exact Or.inl hja
        · exact Or.inr ⟨Finset.mem_univ j, h j hja (Finset.mem_filter.mp hj).2⟩
    _ ≤ ((Finset.univ : Finset α).filter Q).card + 1 := Finset.card_insert_le _ _

private lemma stat_xhat_le {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (x y s : Fin m → Fin q) (k : Fin r) :
    stat hq hqt hrn (xhat hq hqt hrn x s) y k ≤ stat hq hqt hrn x y k + 1 ∧
      stat hq hqt hrn x y k ≤ stat hq hqt hrn (xhat hq hqt hrn x s) y k + 1 := by
  constructor
  · exact card_filter_le_succ _ _ (jIdx hq hqt (blk hrn (fun i => x i + s i) k))
      (fun j hj hP => by rwa [← xhat_win hq hqt hrn x s k j hj])
  · exact card_filter_le_succ _ _ (jIdx hq hqt (blk hrn (fun i => x i + s i) k))
      (fun j hj hP => by rwa [xhat_win hq hqt hrn x s k j hj])

private def codeSum {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (T0 L : Nat) (x y : Fin m → Fin q) : ℚ :=
  ∑ th : Fin L, ∑ s : Fin m → Fin q,
    if ∃ k, T0 + th.val ≤ stat hq hqt hrn (xhat hq hqt hrn x s) y k then 0
    else T (xhat hq hqt hrn x s) y * T x y

private lemma sum_jIdx {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (G : (Fin r → Fin (q ^ t)) → ℚ) :
    ∑ u : Fin m → Fin q, G (fun k => jIdx hq hqt (blk hrn u k)) =
      ((q : ℚ) ^ (m - r * t)) * ∑ j, G j := by
  rw [Finset.mul_sum]
  have h1 : ∀ u : Fin m → Fin q, G (fun k => jIdx hq hqt (blk hrn u k)) =
      ∑ j : Fin r → Fin (q ^ t),
        if (fun k => jIdx hq hqt (blk hrn u k)) = j then G j else 0 := by
    intro u
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hfil : (Finset.univ : Finset (Fin m → Fin q)).filter
      (fun u => (fun k => jIdx hq hqt (blk hrn u k)) = j) =
      (Finset.univ : Finset (Fin m → Fin q)).filter
        (fun u => ∀ k, jIdx hq hqt (blk hrn u k) = j k) := by
    apply Finset.filter_congr
    intro u _
    exact funext_iff
  rw [hfil, jIdx_uniform hq hqt hrn j]
  push_cast
  rfl

private lemma sum_flip {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (x y : Fin m → Fin q) :
    ∑ s : Fin m → Fin q, T (xhat hq hqt hrn x s) y * T x y =
      (q : ℚ) ^ (m - r * t) * ∏ k : Fin r, ((q : ℚ) ^ t - 2 * stat hq hqt hrn x y k) := by
  have : NeZero q := ⟨by omega⟩
  simp_rw [flip_prod]
  let φ : Fin r → Fin (q ^ t) → ℚ := fun k j =>
    if near hq (x (idx hrn k (win hqt j))) (y (idx hrn k (win hqt j))) then -1 else 1
  have hsub : ∀ s : Fin m → Fin q,
      ∏ k : Fin r, (if near hq (x (cpos hq hqt hrn (fun i => x i + s i) k))
        (y (cpos hq hqt hrn (fun i => x i + s i) k)) then (-1 : ℚ) else 1) =
      (fun u : Fin m → Fin q => ∏ k : Fin r, φ k (jIdx hq hqt (blk hrn u k)))
        (fun i => x i + s i) := fun s => rfl
  rw [Finset.sum_congr rfl (fun s _ => hsub s)]
  have hshift : ∑ s : Fin m → Fin q,
      (fun u : Fin m → Fin q => ∏ k : Fin r, φ k (jIdx hq hqt (blk hrn u k))) (fun i => x i + s i) =
      ∑ u : Fin m → Fin q, ∏ k : Fin r, φ k (jIdx hq hqt (blk hrn u k)) :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun s => rfl)
  rw [hshift]
  rw [sum_jIdx hq hqt hrn (fun j => ∏ k : Fin r, φ k (j k)), ← Fintype.prod_sum]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (q ^ t))))
    (fun j => near hq (x (idx hrn k (win hqt j))) (y (idx hrn k (win hqt j))) = true)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  simp only [φ, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, stat]
  have hs := congrArg (fun z : Nat => (z : ℚ)) hsplit
  push_cast at hs
  linarith

private def inner {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (τ : Nat) (x y : Fin m → Fin q) : ℚ :=
  ∑ s : Fin m → Fin q,
    if ∃ k, τ ≤ stat hq hqt hrn (xhat hq hqt hrn x s) y k then 0
    else T (xhat hq hqt hrn x s) y * T x y

private lemma inner_never {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (τ : Nat) (x y : Fin m → Fin q) (h : ∀ k, stat hq hqt hrn x y k + 2 ≤ τ) :
    inner hq hqt hrn τ x y = ∑ s : Fin m → Fin q, T (xhat hq hqt hrn x s) y * T x y := by
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [ite_eq_right]
  rintro ⟨k, hk⟩
  have := (stat_xhat_le hq hqt hrn x y s k).1
  have := h k
  omega

private lemma inner_always {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (τ : Nat) (x y : Fin m → Fin q) (h : ∃ k, τ + 1 ≤ stat hq hqt hrn x y k) :
    inner hq hqt hrn τ x y = 0 := by
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [ite_eq_left]
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have := (stat_xhat_le hq hqt hrn x y s k).2
  omega

private lemma codeSum_typical {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (T0 L : Nat) (hTL : 2 * (T0 + L) ≤ q ^ t) (x y : Fin m → Fin q)
    (hxy : ∀ k, stat hq hqt hrn x y k + 2 ≤ T0) :
    (L : ℚ) * (q : ℚ) ^ (m - r * t) * ((q : ℚ) ^ t - 2 * T0) ^ r ≤ codeSum hq hqt hrn T0 L x y := by
  have hprod : ((q : ℚ) ^ t - 2 * T0) ^ r ≤
      ∏ k : Fin r, ((q : ℚ) ^ t - 2 * stat hq hqt hrn x y k) := by
    rw [← Fin.prod_const]
    apply Finset.prod_le_prod₀
    · intro k _
      have h2 : ((2 * T0 : Nat) : ℚ) ≤ ((q ^ t : Nat) : ℚ) := by exact_mod_cast (by omega)
      push_cast at h2
      linarith
    · intro k _
      have h2 : ((2 * stat hq hqt hrn x y k : Nat) : ℚ) ≤ ((2 * T0 : Nat) : ℚ) := by
        exact_mod_cast (by have := hxy k; omega)
      push_cast at h2
      linarith
  have hinner : ∀ th : Fin L, inner hq hqt hrn (T0 + th.val) x y =
      (q : ℚ) ^ (m - r * t) * ∏ k : Fin r, ((q : ℚ) ^ t - 2 * stat hq hqt hrn x y k) := by
    intro th
    rw [inner_never hq hqt hrn _ x y (fun k => by have := hxy k; omega), sum_flip]
  have hcs : codeSum hq hqt hrn T0 L x y = ∑ th : Fin L, inner hq hqt hrn (T0 + th.val) x y := rfl
  rw [hcs, Finset.sum_congr rfl (fun th _ => hinner th), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left hprod (pow_nonneg (Nat.cast_nonneg _) _)

private lemma inner_ge {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (τ : Nat) (x y : Fin m → Fin q) : -((q : ℚ) ^ m) ≤ inner hq hqt hrn τ x y := by
  have hT : ∀ u v : Fin m → Fin q, -1 ≤ T u v * T x y := by
    intro u v
    unfold T sign
    split_ifs <;> norm_num
  calc -((q : ℚ) ^ m) = ∑ _s : Fin m → Fin q, (-1 : ℚ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ inner hq hqt hrn τ x y := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        split_ifs
        · norm_num
        · exact hT _ _

private lemma inner_nonneg {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (τ : Nat) (hτ : 2 * τ ≤ q ^ t) (x y : Fin m → Fin q)
    (h : ∀ k, stat hq hqt hrn x y k + 2 ≤ τ) : 0 ≤ inner hq hqt hrn τ x y := by
  rw [inner_never hq hqt hrn τ x y h, sum_flip]
  apply mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
  apply Finset.prod_nonneg
  intro k _
  have h2 : ((2 * stat hq hqt hrn x y k : Nat) : ℚ) ≤ ((q ^ t : Nat) : ℚ) := by
    exact_mod_cast (by have := h k; omega)
  push_cast at h2
  linarith

private lemma codeSum_ge {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (T0 L : Nat) (hTL : 2 * (T0 + L) ≤ q ^ t) (x y : Fin m → Fin q) :
    -(2 * r * (q : ℚ) ^ m) ≤ codeSum hq hqt hrn T0 L x y := by
  let bad : Finset (Fin L) := (Finset.univ : Finset (Fin r)).biUnion (fun k =>
    (Finset.univ : Finset (Fin L)).filter (fun th =>
      T0 + th.val = stat hq hqt hrn x y k ∨ T0 + th.val = stat hq hqt hrn x y k + 1))
  have hbad : bad.card ≤ 2 * r := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ k : Fin r, ((Finset.univ : Finset (Fin L)).filter (fun th =>
          T0 + th.val = stat hq hqt hrn x y k ∨ T0 + th.val = stat hq hqt hrn x y k + 1)).card
        ≤ ∑ _k : Fin r, 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have hsub : (Finset.univ : Finset (Fin L)).filter (fun th =>
              T0 + th.val = stat hq hqt hrn x y k ∨ T0 + th.val = stat hq hqt hrn x y k + 1) ⊆
              ((Finset.univ : Finset (Fin L)).filter (fun th =>
                T0 + th.val = stat hq hqt hrn x y k)) ∪
              ((Finset.univ : Finset (Fin L)).filter (fun th =>
                T0 + th.val = stat hq hqt hrn x y k + 1)) := by
            intro th hth
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hth ⊢
            exact hth
          have hone : ∀ c : Nat, ((Finset.univ : Finset (Fin L)).filter
              (fun th => T0 + th.val = c)).card ≤ 1 := by
            intro c
            apply Finset.card_le_one.mpr
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact Fin.ext (by omega)
          exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
            (by have := hone (stat hq hqt hrn x y k); have := hone (stat hq hqt hrn x y k + 1);
                omega))
      _ = 2 * r := by simp [mul_comm]
  have hterm : ∀ th : Fin L, (if th ∈ bad then -((q : ℚ) ^ m) else 0) ≤
      inner hq hqt hrn (T0 + th.val) x y := by
    intro th
    split_ifs with hb
    · exact inner_ge hq hqt hrn _ x y
    · by_cases ha : ∀ k, stat hq hqt hrn x y k + 2 ≤ T0 + th.val
      · exact inner_nonneg hq hqt hrn _ (by have := th.isLt; omega) x y ha
      · push Not at ha
        obtain ⟨k, hk⟩ := ha
        by_cases hb2 : ∃ k', T0 + th.val + 1 ≤ stat hq hqt hrn x y k'
        · rw [inner_always hq hqt hrn _ x y hb2]
        · push Not at hb2
          exfalso
          apply hb
          simp only [bad, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨k, by have := hb2 k; omega⟩
  have hcs : codeSum hq hqt hrn T0 L x y = ∑ th : Fin L, inner hq hqt hrn (T0 + th.val) x y := rfl
  rw [hcs]
  refine le_trans ?_ (Finset.sum_le_sum (fun th _ => hterm th))
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hb : ((Finset.univ.filter (fun th : Fin L => th ∈ bad)).card : ℚ) ≤ 2 * r := by
    have : (Finset.univ.filter (fun th : Fin L => th ∈ bad)) = bad := by ext; simp
    rw [this]
    exact_mod_cast hbad
  have hq0 : (0 : ℚ) ≤ (q : ℚ) ^ m := pow_nonneg (Nat.cast_nonneg _) _
  nlinarith

private lemma hash_coll {α : Type*} [Fintype α] [DecidableEq α] {K : Nat}
    {a b : α} (hab : a ≠ b) :
    ((Finset.univ : Finset (α → Fin K)).filter (fun h => h a = h b)).card * K =
      K ^ Fintype.card α := by
  let e : {h : α → Fin K // h a = h b} × Fin K ≃ (α → Fin K) :=
    { toFun := fun p => Function.update p.1.1 b p.2
      invFun := fun g => (⟨Function.update g b (g a), by simp [Function.update_of_ne hab]⟩, g b)
      left_inv := fun ⟨⟨h, hh⟩, c⟩ => by
        refine Prod.ext (Subtype.ext (funext fun x => ?_)) (by simp)
        by_cases hx : x = b
        · subst hx; simp [Function.update_of_ne hab, hh]
        · simp [Function.update_of_ne hx]
      right_inv := fun g => by simp }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

private lemma near_iff {q : Nat} (hq : 5 ≤ q) (a c : Fin q) :
    near hq a c = true ↔ a.val = c.val ∨ a.val = (c.val + 1) % q := by
  have hprd : (prd hq a).val = c.val ↔ a.val = (c.val + 1) % q := by
    show (a.val + q - 1) % q = c.val ↔ _
    have ha := a.isLt; have hc := c.isLt
    have e1 : (a.val + q - 1) % q = if a.val = 0 then q - 1 else a.val - 1 := by
      split_ifs with h
      · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      · rw [show a.val + q - 1 = a.val - 1 + q by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
    have e2 : (c.val + 1) % q = if c.val + 1 = q then 0 else c.val + 1 := by
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    split_ifs <;> omega
  rw [near, decide_eq_true_eq, Fin.ext_iff, Fin.ext_iff]
  exact or_congr eq_comm (eq_comm.trans hprd)

private lemma near_sum {q : Nat} (hq : 5 ≤ q) (c : Fin q) (lam : ℚ) :
    ∑ a : Fin q, (if near hq a c then lam else 1) = (q : ℚ) - 2 + 2 * lam := by
  have hne : c ≠ ⟨(c.val + 1) % q, Nat.mod_lt _ (by omega)⟩ := fun h => by
    have h' : c.val = (c.val + 1) % q := congrArg Fin.val h
    rcases (by omega : c.val + 1 < q ∨ c.val + 1 = q) with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at h'; omega
    · rw [hc, Nat.mod_self] at h'; omega
  have h2 : ((Finset.univ : Finset (Fin q)).filter (fun a => near hq a c = true)) =
      {c, ⟨(c.val + 1) % q, Nat.mod_lt _ (by omega)⟩} := by
    ext a
    simp [near_iff, Fin.ext_iff]
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin q)))
    (fun a => near hq a c = true)
  rw [h2, Finset.card_pair hne, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h2, Finset.card_pair hne,
    show (Finset.univ.filter fun a => ¬near hq a c = true).card = q - 2 by omega]
  have : 2 ≤ q := by omega
  push_cast [nsmul_eq_mul, Nat.cast_sub this]
  ring

private lemma tail_bound {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (y : Fin m → Fin q) (k : Fin r) (τ : Nat) {lam : ℚ} (hlam : 1 ≤ lam) :
    (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun x => τ ≤ stat hq hqt hrn x y k)).card : ℚ) * lam ^ τ ≤
      (q : ℚ) ^ (m - q ^ t) * ((q : ℚ) - 2 + 2 * lam) ^ (q ^ t) := by

  set W := (Finset.univ : Finset (Fin (q ^ t))).image (fun j => idx hrn k (win hqt j)) with hW
  have hinj : Function.Injective (fun j : Fin (q ^ t) => idx hrn k (win hqt j)) :=
    fun j1 j2 h => Fin.ext (Nat.add_left_cancel (Fin.ext_iff.1 h))
  have hWc : W.card = q ^ t := by
    rw [hW, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

  let w : Fin m → Fin q → ℚ := fun i a => if i ∈ W then (if near hq a (y i) then lam else 1) else 1
  have hmom : ∀ x : Fin m → Fin q, lam ^ stat hq hqt hrn x y k = ∏ i, w i (x i) := by
    intro x
    rw [Fintype.prod_ite_mem, hW, Finset.prod_image (fun a _ b _ h => hinj h),
      ← Finset.prod_filter, Finset.prod_const]
    rfl
  have hcol : ∀ i, ∑ a, w i a = if i ∈ W then (q : ℚ) - 2 + 2 * lam else q := by
    intro i
    by_cases hi : i ∈ W <;> simp [w, hi, near_sum]
  have hsum : ∑ x : Fin m → Fin q, lam ^ stat hq hqt hrn x y k =
      (q : ℚ) ^ (m - q ^ t) * ((q : ℚ) - 2 + 2 * lam) ^ (q ^ t) := by
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => i ∈ W)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hWc, Finset.card_univ,
      Fintype.card_fin] at hcard
    simp_rw [hmom]
    rw [← Fintype.prod_sum, Fintype.prod_congr _ _ hcol, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter, hWc,
      show (Finset.univ.filter fun i => i ∉ W).card = m - q ^ t by omega, mul_comm]
  rw [← nsmul_eq_mul, ← Finset.sum_const, ← hsum]
  exact (Finset.sum_le_sum fun x hx => pow_le_pow_right₀ hlam (Finset.mem_filter.1 hx).2).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => pow_nonneg (by linarith) _)

private lemma nat_mul_pow_le {μ : ℚ} (h0 : 0 ≤ μ) (h1 : μ < 1) (n : Nat) :
    (n : ℚ) * μ ^ n * (1 - μ) ≤ 1 := by
  have key : (n : ℚ) * μ ^ n * (1 - μ) + μ ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1.le (n := n + 1)) (sub_nonneg.2 h1.le)
      have h3 := mul_le_mul_of_nonneg_left ih h0
      rw [pow_succ] at h2 ⊢
      push_cast
      linarith
  linarith [pow_nonneg h0 n]

private lemma pow_mul_geom_small (r : Nat) {γ : ℚ} (h0 : 0 ≤ γ) (h1 : γ < 1) {δ : ℚ}
    (hδ : 0 < δ) : ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n → (n : ℚ) ^ r * γ ^ n ≤ δ := by
  induction r generalizing γ δ with
  | zero =>
    obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hδ h1
    exact ⟨n0, fun n hn => by simpa using (pow_le_pow_of_le_one h0 h1.le hn).trans hn0.le⟩
  | succ r ih =>

    obtain ⟨μ, hμ0, hμ1, hγμ⟩ : ∃ μ : ℚ, 0 ≤ μ ∧ μ < 1 ∧ γ ≤ μ ^ 2 :=
      ⟨(1 + γ) / 2, by linarith, by linarith, by nlinarith [sq_nonneg (1 - γ)]⟩
    obtain ⟨n0, hn0⟩ := ih hμ0 hμ1 (mul_pos hδ (sub_pos.2 hμ1))
    refine ⟨n0, fun n hn => ?_⟩
    have hA := nat_mul_pow_le hμ0 hμ1 n
    calc (n : ℚ) ^ (r + 1) * γ ^ n ≤ (n : ℚ) ^ (r + 1) * (μ ^ 2) ^ n := by gcongr
      _ = ((n : ℚ) * μ ^ n) * ((n : ℚ) ^ r * μ ^ n) := by ring
      _ ≤ ((n : ℚ) * μ ^ n) * (δ * (1 - μ)) := mul_le_mul_of_nonneg_left (hn0 n hn) (by positivity)
      _ ≤ δ := by nlinarith

private lemma one_add_pow_le {η : ℚ} (hη : 0 ≤ η) (k : Nat) (hk : (k : ℚ) * η ≤ 1) :
    (1 + η) ^ k ≤ 1 + k * η + (k * η) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast at hk ⊢
    have hk' : (k : ℚ) * η ≤ 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_right (ih hk') (by linarith : 0 ≤ 1 + η)
    have h2 : 0 ≤ η ^ 2 * ((k : ℚ) * (1 - k * η)) :=
      mul_nonneg (sq_nonneg η) (mul_nonneg k.cast_nonneg (by linarith))
    rw [pow_succ]
    nlinarith

private lemma gamma_lt_one {q : Nat} (hq : 5 ≤ q) (s : Nat) :
    (q : ℚ) - 2 + 2 * (1 + 1 / (8 * (q : ℚ) ^ (2 * s + 1))) ^ (q ^ (s + 1)) <
      (q : ℚ) * (1 + 1 / (8 * (q : ℚ) ^ (2 * s + 1))) ^ (2 * q ^ s + 1) := by
  have hq' : (5 : ℚ) ≤ q := by exact_mod_cast hq
  have hB : (1 : ℚ) ≤ (q : ℚ) ^ s := one_le_pow₀ (by linarith)
  rw [show 8 * (q : ℚ) ^ (2 * s + 1) = 8 * q * ((q : ℚ) ^ s) ^ 2 by ring]
  generalize hηdef : 1 / (8 * (q : ℚ) * ((q : ℚ) ^ s) ^ 2) = η
  have hη : 8 * q * ((q : ℚ) ^ s) ^ 2 * η = 1 := by rw [← hηdef]; field_simp
  have hη0 : 0 < η := by rw [← hηdef]; positivity
  have hk : ((q ^ (s + 1) : Nat) : ℚ) = q * (q : ℚ) ^ s := by push_cast; ring
  have up := one_add_pow_le hη0.le (q ^ (s + 1)) (by rw [hk]; nlinarith)
  have lo := one_add_mul_le_pow (a := η) (by linarith) (2 * q ^ s + 1)
  rw [hk] at up
  push_cast at lo
  have key : 2 * ((q : ℚ) * (q : ℚ) ^ s * η) ^ 2 = q * η / 4 := by
    rw [← mul_one ((q : ℚ) * η / 4), ← hη]; ring
  nlinarith [mul_le_mul_of_nonneg_left lo (by linarith : (0 : ℚ) ≤ q),
    mul_pos (by linarith : (0 : ℚ) < q) hη0]

private lemma count_of_signed {Ω : Type*} [Fintype Ω] (C : Ω → Prop) [DecidablePred C] {β : ℚ}
    (h : β * (Fintype.card Ω : ℚ) ≤ ∑ ω : Ω, (if C ω then (1 : ℚ) else -1)) :
    (1 + β) * (Fintype.card Ω : ℚ) ≤ 2 * (((Finset.univ : Finset Ω).filter C).card : ℚ) := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at h
  have hs := congrArg (fun z : Nat => (z : ℚ))
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) C)
  push_cast at hs
  rw [Finset.card_univ] at hs
  linarith

private def cmsg {m q Mc : Nat} (enc : (Fin m → Fin q) → Fin Mc)
    (left : (Fin m → Fin q) → Bool) (s x : Fin m → Fin q) : Fin (2 * Mc) :=
  ⟨2 * (enc (fun i => x i + s i)).val + (left x).toNat, two_mul_add_toNat_lt (enc _).isLt _⟩

private def cread {m q r n t Mc : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (dec : Fin Mc → (Fin m → Fin q)) (right : (Fin m → Fin q) → Bool) (T0 th : Nat)
    (s : Fin m → Fin q) (b : Bool) (c : Fin (2 * Mc)) (y : Fin m → Fin q) : Bool :=
  if ∃ k, T0 + th ≤ stat hq hqt hrn
      (fun i => dec ⟨c.val / 2, by have := c.isLt; omega⟩ i - s i) y k then b
  else xor (xor (c.val % 2 == 1) (right y))
    (par (fun i => dec ⟨c.val / 2, by have := c.isLt; omega⟩ i - s i) y)

private noncomputable def hread {m q K : Nat} (tr : (Fin m → Fin q) → (Fin m → Fin q) → Bool)
    (Ly : Finset (Fin m → Fin q)) (h : (Fin m → Fin q) → Fin K) (b : Bool) (c : Fin K)
    (y : Fin m → Fin q) : Bool :=
  if hx : ∃ x' ∈ Ly, h x' = c then tr (Classical.choose hx) y else b

private lemma coin_sum (v : Bool) : ∑ b : Bool, (if b = v then (1 : ℚ) else -1) = 0 := by
  cases v <;> simp

private lemma code_point {m q r n t Mc : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (enc : (Fin m → Fin q) → Fin Mc) (dec : Fin Mc → (Fin m → Fin q))
    (hdec : ∀ u, dec (enc u) = corr hq hqt hrn u) (left right : (Fin m → Fin q) → Bool)
    (T0 th : Nat) (s x y : Fin m → Fin q) :
    ∑ b : Bool, (if cread hq hqt hrn dec right T0 th s b (cmsg enc left s x) y =
        xor (xor (left x) (right y)) (par x y) then (1 : ℚ) else -1) =
      2 * (if ∃ k, T0 + th ≤ stat hq hqt hrn (xhat hq hqt hrn x s) y k then 0
        else T (xhat hq hqt hrn x s) y * T x y) := by
  have hdiv : (⟨(cmsg enc left s x).val / 2, by have := (cmsg enc left s x).isLt; omega⟩ :
      Fin Mc) = enc (fun i => x i + s i) := Fin.ext (two_mul_add_toNat_div _ _)
  have hxh : (fun i => dec ⟨(cmsg enc left s x).val / 2,
      by have := (cmsg enc left s x).isLt; omega⟩ i - s i) = xhat hq hqt hrn x s := by
    rw [hdiv, hdec]
    rfl
  have hbit : ((cmsg enc left s x).val % 2 == 1) = left x := two_mul_add_toNat_mod _ _
  unfold cread
  rw [hxh, hbit]
  by_cases hscr : ∃ k, T0 + th ≤ stat hq hqt hrn (xhat hq hqt hrn x s) y k
  · simp only [hscr, ↓reduceIte]
    rw [coin_sum, mul_zero]
  · simp only [hscr, ↓reduceIte]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, T, T, sign_mul_sign]
    generalize par (xhat hq hqt hrn x s) y = a
    generalize par x y = a'
    generalize left x = c
    generalize right y = d
    cases a <;> cases a' <;> cases c <;> cases d <;> norm_num

private lemma hash_point {m q K : Nat} (tr : (Fin m → Fin q) → (Fin m → Fin q) → Bool)
    (Ly : Finset (Fin m → Fin q)) (h : (Fin m → Fin q) → Fin K) (x y : Fin m → Fin q) :
    (if ∃ x' ∈ Ly, x' ≠ x ∧ h x' = h x then -2 else if x ∈ Ly then 2 else 0) ≤
      ∑ b : Bool, (if hread tr Ly h b (h x) y = tr x y then (1 : ℚ) else -1) := by
  by_cases hc : ∃ x' ∈ Ly, x' ≠ x ∧ h x' = h x
  · rw [ite_eq_left hc]
    calc (-2 : ℚ) = ∑ _b : Bool, (-1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ => by split_ifs <;> norm_num)
  · rw [ite_eq_right hc]
    push Not at hc
    by_cases hxL : x ∈ Ly
    · have hex : ∃ x' ∈ Ly, h x' = h x := ⟨x, hxL, rfl⟩
      have hch : Classical.choose hex = x := by
        obtain ⟨hmem, heq⟩ := Classical.choose_spec hex
        by_contra hne
        exact hc _ hmem hne heq
      have hval : ∀ b, hread tr Ly h b (h x) y = tr x y := by
        intro b
        unfold hread
        rw [dite_eq_left hex, hch]
      simp [hxL, hval]
    · have hex : ¬ ∃ x' ∈ Ly, h x' = h x := by
        rintro ⟨x', hx', heq⟩
        exact hc x' hx' (fun h => hxL (h ▸ hx')) heq
      have hval : ∀ b, hread tr Ly h b (h x) y = b := by
        intro b
        unfold hread
        rw [dite_eq_right hex]
      simp only [hxL, ↓reduceIte, hval]
      rw [coin_sum]

private lemma coll_card {α : Type*} [Fintype α] [DecidableEq α] {K : Nat}
    (Ly : Finset α) (x : α) :
    (((Finset.univ : Finset (α → Fin K)).filter
      (fun h => ∃ x' ∈ Ly, x' ≠ x ∧ h x' = h x)).card : ℚ) * K ≤
      (Ly.card : ℚ) * (K : ℚ) ^ Fintype.card α := by
  have hsub : (Finset.univ : Finset (α → Fin K)).filter
      (fun h => ∃ x' ∈ Ly, x' ≠ x ∧ h x' = h x) ⊆
      Ly.biUnion (fun x' => if x' = x then ∅ else
        (Finset.univ : Finset (α → Fin K)).filter (fun h => h x' = h x)) := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    obtain ⟨x', hx', hne, heq⟩ := hh
    rw [Finset.mem_biUnion]
    exact ⟨x', hx', by rw [ite_eq_right hne]; simp [heq]⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hK0 : (0 : ℚ) ≤ K := Nat.cast_nonneg _
  calc (((Finset.univ : Finset (α → Fin K)).filter
        (fun h => ∃ x' ∈ Ly, x' ≠ x ∧ h x' = h x)).card : ℚ) * K
      ≤ (∑ x' ∈ Ly, ((if x' = x then ∅ else
          (Finset.univ : Finset (α → Fin K)).filter (fun h => h x' = h x)).card : ℚ)) * K := by
        apply mul_le_mul_of_nonneg_right _ hK0
        exact_mod_cast hcard
    _ = ∑ x' ∈ Ly, ((if x' = x then ∅ else
          (Finset.univ : Finset (α → Fin K)).filter (fun h => h x' = h x)).card : ℚ) * K := by
        rw [Finset.sum_mul]
    _ ≤ ∑ _x' ∈ Ly, (K : ℚ) ^ Fintype.card α := by
        refine Finset.sum_le_sum (fun x' _ => ?_)
        split_ifs with hx
        · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
          exact pow_nonneg hK0 _
        · have := hash_coll (K := K) hx
          exact_mod_cast this.le
    _ = (Ly.card : ℚ) * (K : ℚ) ^ Fintype.card α := by
        rw [Finset.sum_const, nsmul_eq_mul]

private lemma protocol_works {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (hn : 0 < n) (T0 L D P : Nat) (hL : 0 < L) (hPD : P ≤ D) (hD : 0 < D)
    (hTL : 2 * (T0 + L) ≤ q ^ t) {β e A : ℚ} (left right : (Fin m → Fin q) → Bool)
    (hLy : ∀ y : Fin m → Fin q, (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun x => ∃ k, T0 ≤ stat hq hqt hrn x y k + 1)).card : ℚ) ≤ e * (2 * q ^ (m - r * t)))
    (hA0 : 0 ≤ A) (hA : A ≤ ((q : ℚ) ^ t - 2 * T0) / (q : ℚ) ^ t)
    (hty : β ≤ (1 - (P : ℚ) / D) * A ^ r - (P : ℚ) / D * e)
    (hat : β ≤ (P : ℚ) / D * (1 - 2 * e) - (1 - (P : ℚ) / D) * (2 * r / L)) :
    worksR m q β left right (2 * q ^ (m - r * t)) := by
  obtain ⟨enc, dec, hdec⟩ := code_exists hq hqt hrn hn
  have htn : t ≤ n := le_trans (Nat.le_of_lt (lt_pow_self (by omega : 2 ≤ q) t)) hqt
  have hrtm : r * t ≤ m := le_trans (Nat.mul_le_mul_left r htn) hrn
  let tr : (Fin m → Fin q) → (Fin m → Fin q) → Bool := fun x y =>
    xor (xor (left x) (right y)) (par x y)
  let Ly : (Fin m → Fin q) → Finset (Fin m → Fin q) := fun y =>
    (Finset.univ : Finset (Fin m → Fin q)).filter (fun x => ∃ k, T0 ≤ stat hq hqt hrn x y k + 1)
  let Ω := (Fin P ⊕ Fin (D - P)) × ((Fin m → Fin q) × (Fin L ×
    (((Fin m → Fin q) → Fin (2 * (q ^ (m - r * t)))) × Bool)))
  let send : Ω → (Fin m → Fin q) → Fin (2 * (q ^ (m - r * t))) := fun ω x =>
    Sum.elim (fun _ => ω.2.2.2.1 x) (fun _ => cmsg enc left ω.2.1 x) ω.1
  let read : Ω → Fin (2 * (q ^ (m - r * t))) → (Fin m → Fin q) → Bool := fun ω c y =>
    Sum.elim (fun _ => hread tr (Ly y) ω.2.2.2.1 ω.2.2.2.2 c y)
      (fun _ => cread hq hqt hrn dec right T0 ω.2.2.1.val ω.2.1 ω.2.2.2.2 c y) ω.1
  let eΩ := Fintype.equivFin Ω
  have hMcpos : 0 < (q ^ (m - r * t)) := Nat.pow_pos (by omega)
  have hKpos : 0 < 2 * (q ^ (m - r * t)) := by omega
  have hcard : Fintype.card Ω = (P + (D - P)) * (q ^ m * (L * ((2 * (q ^ (m - r * t))) ^ (q ^ m) * 2))) := by
    simp only [Ω, Fintype.card_prod, Fintype.card_sum, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
  have hzpos : 0 < Fintype.card Ω := by
    rw [hcard]
    apply Nat.mul_pos (by omega)
    positivity
  refine ⟨Fintype.card Ω, fun seed => send (eΩ.symm seed), fun seed => read (eΩ.symm seed),
    hzpos, fun x y => ?_⟩
  let C : Ω → Prop := fun ω => read ω (send ω x) y = tr x y
  have hcnt : ((Finset.univ : Finset (Fin (Fintype.card Ω))).filter
      (fun seed => C (eΩ.symm seed))).card = ((Finset.univ : Finset Ω).filter C).card := by
    apply Finset.card_bij (fun seed _ => eΩ.symm seed)
    · intro a ha
      simpa using ha
    · intro a _ b _ h
      exact eΩ.symm.injective h
    · intro b hb
      exact ⟨eΩ b, by simpa using hb, by simp⟩
  change (1 + β) * (Fintype.card Ω : ℚ) ≤ 2 * ((((Finset.univ : Finset (Fin (Fintype.card Ω))).filter
      (fun seed => C (eΩ.symm seed))).card : Nat) : ℚ)
  rw [hcnt]
  apply count_of_signed C

  let KN : ℚ := ((2 * (q ^ (m - r * t)) : Nat) : ℚ) ^ (q ^ m)
  let H : ℚ := ∑ h : (Fin m → Fin q) → Fin (2 * (q ^ (m - r * t))), ∑ b : Bool,
    (if hread tr (Ly y) h b (h x) y = tr x y then (1 : ℚ) else -1)
  let CS : ℚ := codeSum hq hqt hrn T0 L x y
  let fh : ((Fin m → Fin q) → Fin (2 * (q ^ (m - r * t)))) → Bool → ℚ := fun h b =>
    if hread tr (Ly y) h b (h x) y = tr x y then 1 else -1
  let fc : (Fin m → Fin q) → Fin L → Bool → ℚ := fun s th b =>
    if cread hq hqt hrn dec right T0 th.val s b (cmsg enc left s x) y = tr x y then 1 else -1
  have hsg : ∀ ω : Ω, (if C ω then (1 : ℚ) else -1) =
      Sum.elim (fun _ => fh ω.2.2.2.1 ω.2.2.2.2) (fun _ => fc ω.2.1 ω.2.2.1 ω.2.2.2.2) ω.1 := by
    rintro ⟨a | a, s, th, h, b⟩ <;> rfl
  have hfc : ∀ s th, ∑ b : Bool, fc s th b = 2 * (if ∃ k, T0 + th.val ≤
      stat hq hqt hrn (xhat hq hqt hrn x s) y k then 0 else T (xhat hq hqt hrn x s) y * T x y) :=
    fun s th => code_point hq hqt hrn enc dec hdec left right T0 th.val s x y
  have hsum : ∑ ω : Ω, (if C ω then (1 : ℚ) else -1) =
      (P : ℚ) * ((q : ℚ) ^ m * (L * H)) + ((D - P : Nat) : ℚ) * (KN * (2 * CS)) := by
    rw [Finset.sum_congr rfl (fun ω _ => hsg ω)]
    simp only [Ω, Fintype.sum_prod_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, nsmul_eq_mul, hfc]
    simp only [H, KN, CS, codeSum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m → Fin q)))]
    simp only [Finset.mul_sum]
    push_cast
    ring
  have hcardQ : (Fintype.card Ω : ℚ) = (D : ℚ) * ((q : ℚ) ^ m * (L * (KN * 2))) := by
    rw [hcard, show P + (D - P) = D by omega]
    simp only [KN]
    push_cast
    ring
  rw [hsum, hcardQ]

  have hKq : (0 : ℚ) < ((2 * (q ^ (m - r * t)) : Nat) : ℚ) := by exact_mod_cast hKpos
  have hKN : 0 < KN := pow_pos hKq _
  let Coll := (Finset.univ : Finset ((Fin m → Fin q) → Fin (2 * (q ^ (m - r * t))))).filter
    (fun h => ∃ x' ∈ Ly y, x' ≠ x ∧ h x' = h x)
  have hColl : (Coll.card : ℚ) ≤ e * KN := by
    have h1 := coll_card (K := 2 * q ^ (m - r * t)) (Ly y) x
    simp only [Fintype.card_fun, Fintype.card_fin] at h1
    have h3 : ((Ly y).card : ℚ) * KN ≤ e * (2 * (q : ℚ) ^ (m - r * t)) * KN :=
      mul_le_mul_of_nonneg_right (hLy y) hKN.le
    have hK2 : ((2 * (q ^ (m - r * t)) : Nat) : ℚ) = 2 * (q : ℚ) ^ (m - r * t) := by push_cast; ring
    have h4 : (Coll.card : ℚ) * ((2 * (q ^ (m - r * t)) : Nat) : ℚ) ≤
        e * KN * ((2 * (q ^ (m - r * t)) : Nat) : ℚ) := by
      calc (Coll.card : ℚ) * ((2 * (q ^ (m - r * t)) : Nat) : ℚ) ≤ ((Ly y).card : ℚ) * KN := h1
        _ ≤ e * (2 * (q : ℚ) ^ (m - r * t)) * KN := h3
        _ = e * KN * ((2 * (q ^ (m - r * t)) : Nat) : ℚ) := by rw [hK2]; ring
    exact le_of_mul_le_mul_right h4 hKq
  have hHpt := fun (h : (Fin m → Fin q) → Fin (2 * q ^ (m - r * t))) =>
    hash_point tr (Ly y) h x y
  have hDpos : (0 : ℚ) < D := by exact_mod_cast hD
  have hDP : ((D - P : Nat) : ℚ) = D - P := by push_cast [Nat.cast_sub hPD]; ring
  have hNpos : (0 : ℚ) < (q : ℚ) ^ m := pow_pos (by exact_mod_cast (by omega : 0 < q)) _
  have hLpos : (0 : ℚ) < L := by exact_mod_cast hL
  have hP0 : (0 : ℚ) ≤ P := Nat.cast_nonneg _
  have hDP0 : (0 : ℚ) ≤ ((D - P : Nat) : ℚ) := Nat.cast_nonneg _
  have hp : (P : ℚ) = (P : ℚ) / D * D := by field_simp
  by_cases hx : x ∈ Ly y
  ·
    have hH : 2 * KN - 4 * (Coll.card : ℚ) ≤ H := by
      calc 2 * KN - 4 * (Coll.card : ℚ)
          = ∑ h : (Fin m → Fin q) → Fin (2 * (q ^ (m - r * t))),
              (if ∃ x' ∈ Ly y, x' ≠ x ∧ h x' = h x then (-2 : ℚ) else if x ∈ Ly y then 2 else 0) := by
            simp only [hx, ↓reduceIte]
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            have hs := congrArg (fun z : Nat => (z : ℚ)) (Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset ((Fin m → Fin q) → Fin (2 * (q ^ (m - r * t))))))
              (fun h => ∃ x' ∈ Ly y, x' ≠ x ∧ h x' = h x))
            push_cast at hs
            simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hs
            simp only [KN, Coll]
            push_cast at hs ⊢
            linarith
        _ ≤ H := Finset.sum_le_sum (fun h _ => hHpt h)
    have hCS := codeSum_ge hq hqt hrn T0 L hTL x y
    have hat' : (D : ℚ) * β ≤ P * (1 - 2 * e) - (D - P) * (2 * r / L) := by
      have := mul_le_mul_of_nonneg_left hat hDpos.le
      calc (D : ℚ) * β ≤ D * ((P : ℚ) / D * (1 - 2 * e) - (1 - (P : ℚ) / D) * (2 * r / L)) := this
        _ = P * (1 - 2 * e) - (D - P) * (2 * r / L) := by field_simp
    have hA1 : (P : ℚ) * ((q : ℚ) ^ m * (L * (2 * KN * (1 - 2 * e)))) ≤
        (P : ℚ) * ((q : ℚ) ^ m * (L * H)) := by
      apply mul_le_mul_of_nonneg_left _ hP0
      apply mul_le_mul_of_nonneg_left _ hNpos.le
      apply mul_le_mul_of_nonneg_left _ hLpos.le
      nlinarith
    have hA2 : ((D - P : Nat) : ℚ) * (KN * (2 * (-(2 * r * (q : ℚ) ^ m)))) ≤
        ((D - P : Nat) : ℚ) * (KN * (2 * CS)) := by
      apply mul_le_mul_of_nonneg_left _ hDP0
      apply mul_le_mul_of_nonneg_left _ hKN.le
      linarith
    rw [hDP] at hA2
    have hZ : 0 < (q : ℚ) ^ m * (L * (KN * 2)) := by positivity
    have hfin : β * ((D : ℚ) * ((q : ℚ) ^ m * (L * (KN * 2)))) ≤
        (P : ℚ) * ((q : ℚ) ^ m * (L * (2 * KN * (1 - 2 * e)))) +
          (D - P) * (KN * (2 * (-(2 * r * (q : ℚ) ^ m)))) := by
      have := mul_le_mul_of_nonneg_left hat' hZ.le
      have hL0 : (L : ℚ) ≠ 0 := hLpos.ne'
      calc β * ((D : ℚ) * ((q : ℚ) ^ m * (L * (KN * 2))))
          = ((q : ℚ) ^ m * (L * (KN * 2))) * ((D : ℚ) * β) := by ring
        _ ≤ ((q : ℚ) ^ m * (L * (KN * 2))) * (P * (1 - 2 * e) - (D - P) * (2 * r / L)) := this
        _ = _ := by field_simp; ring
    rw [hDP]
    linarith
  ·
    have hxy : ∀ k, stat hq hqt hrn x y k + 2 ≤ T0 := by
      intro k
      by_contra hk
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨k, by omega⟩⟩)
    have hH : -2 * (Coll.card : ℚ) ≤ H := by
      calc -2 * (Coll.card : ℚ)
          = ∑ h : (Fin m → Fin q) → Fin (2 * (q ^ (m - r * t))),
              (if ∃ x' ∈ Ly y, x' ≠ x ∧ h x' = h x then (-2 : ℚ) else if x ∈ Ly y then 2 else 0) := by
            simp only [hx, ↓reduceIte]
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            simp only [Coll]
            ring
        _ ≤ H := Finset.sum_le_sum (fun h _ => hHpt h)
    have hCS := codeSum_typical hq hqt hrn T0 L hTL x y hxy
    have hqt0 : (0 : ℚ) < (q : ℚ) ^ t := pow_pos (by exact_mod_cast (by omega : 0 < q)) _
    have hAt : A * (q : ℚ) ^ t ≤ (q : ℚ) ^ t - 2 * T0 := by
      have := mul_le_mul_of_nonneg_right hA hqt0.le
      rwa [div_mul_cancel₀ _ hqt0.ne'] at this
    have hpowA : (A * (q : ℚ) ^ t) ^ r ≤ ((q : ℚ) ^ t - 2 * T0) ^ r :=
      pow_le_pow_left₀ (mul_nonneg hA0 hqt0.le) hAt r
    have hqm : (q : ℚ) ^ (m - r * t) * ((q : ℚ) ^ t) ^ r = (q : ℚ) ^ m := by
      rw [← pow_mul, ← pow_add, mul_comm t r, Nat.sub_add_cancel hrtm]
    have hCS' : (L : ℚ) * ((q : ℚ) ^ m * A ^ r) ≤ CS := by
      calc (L : ℚ) * ((q : ℚ) ^ m * A ^ r)
          = (L : ℚ) * (q : ℚ) ^ (m - r * t) * (A * (q : ℚ) ^ t) ^ r := by
            rw [mul_pow, ← hqm]; ring
        _ ≤ (L : ℚ) * (q : ℚ) ^ (m - r * t) * ((q : ℚ) ^ t - 2 * T0) ^ r :=
            mul_le_mul_of_nonneg_left hpowA (by positivity)
        _ ≤ CS := hCS
    have hty' : (D : ℚ) * β ≤ (D - P) * A ^ r - P * e := by
      have := mul_le_mul_of_nonneg_left hty hDpos.le
      calc (D : ℚ) * β ≤ D * ((1 - (P : ℚ) / D) * A ^ r - (P : ℚ) / D * e) := this
        _ = (D - P) * A ^ r - P * e := by field_simp
    have hB1 : (P : ℚ) * ((q : ℚ) ^ m * (L * (-2 * (e * KN)))) ≤
        (P : ℚ) * ((q : ℚ) ^ m * (L * H)) := by
      apply mul_le_mul_of_nonneg_left _ hP0
      apply mul_le_mul_of_nonneg_left _ hNpos.le
      apply mul_le_mul_of_nonneg_left _ hLpos.le
      linarith
    have hB2 : ((D - P : Nat) : ℚ) * (KN * (2 * ((L : ℚ) * ((q : ℚ) ^ m * A ^ r)))) ≤
        ((D - P : Nat) : ℚ) * (KN * (2 * CS)) := by
      apply mul_le_mul_of_nonneg_left _ hDP0
      apply mul_le_mul_of_nonneg_left _ hKN.le
      linarith
    rw [hDP] at hB2
    have hZ : 0 ≤ (q : ℚ) ^ m * (L * (KN * 2)) := by positivity
    have hfin := mul_le_mul_of_nonneg_left hty' hZ
    rw [hDP]
    nlinarith

private lemma small_works {m q : Nat} {β : ℚ} (hβ1 : β ≤ 1) (left right : (Fin m → Fin q) → Bool) :
    worksR m q β left right (q ^ m) := by
  let eW : (Fin m → Fin q) ≃ Fin (q ^ m) := (Fintype.equivFin (Fin m → Fin q)).trans
    (finCongr (by simp only [Fintype.card_fun, Fintype.card_fin]))
  refine ⟨1, fun _ x => eW x,
    fun _ c y => xor (xor (left (eW.symm c)) (right y)) (par (eW.symm c) y), Nat.one_pos,
    fun x y => ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ, Fintype.card_fin]
  push_cast
  linarith

private lemma sub_pow_ge {a d : ℚ} (hd : 0 ≤ d) (had : d ≤ a) (ha : a ≤ 1) :
    ∀ r : Nat, a ^ r - r * d ≤ (a - d) ^ r
  | 0 => by simp
  | r + 1 => by
    have ih := sub_pow_ge hd had ha r
    have h0 : 0 ≤ a - d := by linarith
    have har : a ^ r ≤ 1 := pow_le_one₀ (by linarith) ha
    have har0 : 0 ≤ a ^ r := pow_nonneg (by linarith) r
    have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
    calc a ^ (r + 1) - ((r + 1 : Nat) : ℚ) * d
        ≤ (a ^ r - r * d) * (a - d) := by
          push_cast
          rw [pow_succ]
          nlinarith [mul_nonneg hd (sub_nonneg.mpr har), mul_nonneg (mul_nonneg hr hd)
            (sub_nonneg.mpr ha), mul_nonneg (mul_nonneg hr hd) hd]
      _ ≤ (a - d) ^ r * (a - d) := mul_le_mul_of_nonneg_right ih h0
      _ = (a - d) ^ (r + 1) := (pow_succ _ _).symm

private lemma Ly_bound {m q r n t : Nat} (hq : 5 ≤ q) (hqt : q ^ t ≤ n) (hrn : r * n ≤ m)
    (y : Fin m → Fin q) (τ : Nat) {lam : ℚ} (hlam : 1 ≤ lam) :
    (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun x => ∃ k, τ + 1 ≤ stat hq hqt hrn x y k + 1)).card : ℚ) * lam ^ τ ≤
      r * ((q : ℚ) ^ (m - q ^ t) * ((q : ℚ) - 2 + 2 * lam) ^ (q ^ t)) := by
  have hsub : (Finset.univ : Finset (Fin m → Fin q)).filter
      (fun x => ∃ k, τ + 1 ≤ stat hq hqt hrn x y k + 1) ⊆
      (Finset.univ : Finset (Fin r)).biUnion (fun k =>
        (Finset.univ : Finset (Fin m → Fin q)).filter (fun x => τ ≤ stat hq hqt hrn x y k)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by omega⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hlam0 : 0 ≤ lam ^ τ := pow_nonneg (by linarith) τ
  calc (((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun x => ∃ k, τ + 1 ≤ stat hq hqt hrn x y k + 1)).card : ℚ) * lam ^ τ
      ≤ (∑ k : Fin r, (((Finset.univ : Finset (Fin m → Fin q)).filter
          (fun x => τ ≤ stat hq hqt hrn x y k)).card : ℚ)) * lam ^ τ := by
        apply mul_le_mul_of_nonneg_right _ hlam0
        exact_mod_cast hcard
    _ = ∑ k : Fin r, (((Finset.univ : Finset (Fin m → Fin q)).filter
          (fun x => τ ≤ stat hq hqt hrn x y k)).card : ℚ) * lam ^ τ := Finset.sum_mul _ _ _
    _ ≤ ∑ _k : Fin r, (q : ℚ) ^ (m - q ^ t) * ((q : ℚ) - 2 + 2 * lam) ^ (q ^ t) :=
        Finset.sum_le_sum (fun k _ => tail_bound hq hqt hrn y k τ hlam)
    _ = r * ((q : ℚ) ^ (m - q ^ t) * ((q : ℚ) - 2 + 2 * lam) ^ (q ^ t)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma upper_main {q r : Nat} (hq : 5 ≤ q) (hr : 0 < r) {β : ℚ} (hβ : 0 < β)
    (hβρ : β * (1 + (1 - 4 / (q : ℚ)) ^ r) < (1 - 4 / (q : ℚ)) ^ r) :
    ∃ C : Nat, 0 < C ∧ ∀ m : Nat, 0 < m → ∀ left right : (Fin m → Fin q) → Bool,
      ∃ M : Nat, worksR m q β left right M ∧ M * m ^ r ≤ C * q ^ m := by
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq5 : (5 : ℚ) ≤ q := by exact_mod_cast hq
  set ρ : ℚ := 1 - 4 / (q : ℚ) with hρdef
  have hρ0 : 1 / 5 ≤ ρ := by
    have : 4 / (q : ℚ) ≤ 4 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq5
    linarith
  have hρ1 : ρ ≤ 1 := by
    have : 0 ≤ 4 / (q : ℚ) := by positivity
    linarith
  have hρr0 : 0 < ρ ^ r := pow_pos (by linarith) r
  have hρr1 : ρ ^ r ≤ 1 := pow_le_one₀ (by linarith) hρ1
  set g : ℚ := ρ ^ r * (1 - β) - β with hgdef
  have hg : 0 < g := by rw [hgdef]; nlinarith
  have hβ1 : β < 1 := by nlinarith
  set p : ℚ := β + g / 2 with hpdef
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    have : ρ ^ r * (1 - β) ≤ 1 := by nlinarith
    linarith

  set D : Nat := p.den with hDdef
  set P : Nat := p.num.toNat with hPdef
  have hD : 0 < D := p.den_pos
  have hPD_eq : (P : ℚ) / D = p := by
    have hnum : (0 : ℤ) ≤ p.num := Rat.num_nonneg.mpr hp0.le
    have hP : (P : ℚ) = (p.num : ℚ) := by
      rw [hPdef]
      exact_mod_cast Int.toNat_of_nonneg hnum
    rw [hP, hDdef]
    exact Rat.num_div_den p
  have hPD : P ≤ D := by
    have hDq : (0 : ℚ) < D := by exact_mod_cast hD
    have : (P : ℚ) ≤ D := by
      rw [← div_le_one hDq, hPD_eq]
      exact hp1
    exact_mod_cast this

  set s : Nat := ⌈16 * r / g⌉₊ + 1 with hsdef
  have hs1 : 1 ≤ s := by omega
  have hqs : 16 * r / g < (q : ℚ) ^ (s + 1) := by
    have h1 : 16 * r / g ≤ (⌈16 * r / g⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((s + 1 : Nat) : ℚ) < ((q ^ (s + 1) : Nat) : ℚ) := by
      exact_mod_cast lt_pow_self (by omega : 2 ≤ q) (s + 1)
    push_cast at h2
    have h3 : (s : ℚ) = (⌈16 * r / g⌉₊ : ℚ) + 1 := by rw [hsdef]; push_cast; ring
    linarith

  set μ : ℚ := 1 + 1 / (8 * (q : ℚ) ^ (2 * s + 1)) with hμdef
  have hμ1 : 1 ≤ μ := by
    have : 0 ≤ 1 / (8 * (q : ℚ) ^ (2 * s + 1)) := by positivity
    linarith
  set lam : ℚ := μ ^ (q ^ (s + 1)) with hlamdef
  have hlam : 1 ≤ lam := one_le_pow₀ hμ1
  have hMpos : 0 < μ ^ (2 * q ^ s + 1) := pow_pos (by linarith) _
  have hden : 0 < (q : ℚ) * μ ^ (2 * q ^ s + 1) := mul_pos hqpos hMpos
  set γ : ℚ := ((q : ℚ) - 2 + 2 * lam) / ((q : ℚ) * μ ^ (2 * q ^ s + 1)) with hγdef
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) hden.le
  have hγ1 : γ < 1 := (div_lt_one hden).mpr (gamma_lt_one hq s)
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hr
  obtain ⟨n0, hn0⟩ := pow_mul_geom_small r hγ0 hγ1 (δ := g / (4 * r)) (by positivity)

  set R : Nat := max n0 ⌈8 * r / g⌉₊ + 1 with hRdef
  have hR : 1 ≤ R := by omega
  set m0 : Nat := r * (q ^ (s + 2) * R) with hm0
  refine ⟨max (m0 ^ r) (2 * (2 * r * q + 1) ^ r), by positivity, fun m hm left right => ?_⟩
  by_cases hsmall : m < m0
  · refine ⟨q ^ m, small_works hβ1.le left right, ?_⟩
    calc q ^ m * m ^ r ≤ q ^ m * m0 ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall.le r)
      _ = m0 ^ r * q ^ m := mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
  push Not at hsmall

  set n : Nat := m / r with hndef
  have hnR : q ^ (s + 2) * R ≤ n := (Nat.le_div_iff_mul_le hr).mpr (by rw [mul_comm]; exact hsmall)
  have hn : 0 < n := lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos (by omega)) hR) hnR
  have hrn : r * n ≤ m := Nat.mul_div_le m r
  obtain ⟨t, hqt, hlt⟩ := exists_pow_le_lt (by omega : 2 ≤ q) n hn
  have hts : s + 2 ≤ t := by
    by_contra h
    push Not at h
    have h1 : q ^ (t + 1) ≤ q ^ (s + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : q ^ (s + 2) ≤ q ^ (s + 2) * R := Nat.le_mul_of_pos_right _ hR
    omega
  have hqsplit : q ^ (t + 1) = q ^ (s + 2) * q ^ (t - 1 - s) := by
    rw [← pow_add]
    congr 1
    omega
  have hLR : R < q ^ (t - 1 - s) := by
    have : q ^ (s + 2) * R < q ^ (s + 2) * q ^ (t - 1 - s) := by rw [← hqsplit]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  set L : Nat := q ^ (t - 1 - s) with hLdef
  set τ : Nat := 2 * q ^ (t - 1) + L with hτdef
  have hTL : 2 * (τ + 1 + L) ≤ q ^ t := by
    have h1 : q ^ t = q * q ^ (t - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : q ^ (t - 1) = q ^ s * L := by rw [hLdef, ← pow_add]; congr 1; omega
    have h3 : 5 ≤ q ^ s := le_trans hq (Nat.le_self_pow (by omega) q)
    have h4 : 5 ≤ L := le_trans hq (Nat.le_self_pow (by omega) q)
    rw [hτdef, h1, h2]
    have h5 : 5 * (q ^ s * L) ≤ q * (q ^ s * L) := Nat.mul_le_mul_right _ hq
    have h6 : 5 * L ≤ q ^ s * L := Nat.mul_le_mul_right _ h3
    omega

  set d : ℚ := 2 / (q : ℚ) ^ (s + 1) + 2 / (q : ℚ) ^ t with hddef
  have hqs1 : (0 : ℚ) < (q : ℚ) ^ (s + 1) := pow_pos hqpos _
  have hqt1 : (0 : ℚ) < (q : ℚ) ^ t := pow_pos hqpos _
  have hqst : (q : ℚ) ^ (s + 1) ≤ (q : ℚ) ^ t :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hd0 : 0 ≤ d := by positivity
  have hd4 : d ≤ 4 / (q : ℚ) ^ (s + 1) := by
    have : 2 / (q : ℚ) ^ t ≤ 2 / (q : ℚ) ^ (s + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hqs1 hqst
    have h2 : (4 : ℚ) / (q : ℚ) ^ (s + 1) = 2 / (q : ℚ) ^ (s + 1) + 2 / (q : ℚ) ^ (s + 1) := by ring
    rw [hddef, h2]
    linarith
  have hrd : r * d ≤ g / 4 := by
    have h1 : 16 * r < g * (q : ℚ) ^ (s + 1) := by
      have := (div_lt_iff₀ hg).mp hqs
      linarith
    have h2 : r * (4 / (q : ℚ) ^ (s + 1)) ≤ g / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ hqs1 (by norm_num)]
      linarith
    calc r * d ≤ r * (4 / (q : ℚ) ^ (s + 1)) := mul_le_mul_of_nonneg_left hd4 hr0.le
      _ ≤ g / 4 := h2
  have hdρ : d ≤ ρ := by
    have h25 : (25 : ℚ) ≤ (q : ℚ) ^ (s + 1) := by
      have : (q : ℚ) ^ 2 ≤ (q : ℚ) ^ (s + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      nlinarith
    have : 4 / (q : ℚ) ^ (s + 1) ≤ 4 / 25 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h25
    linarith
  set A : ℚ := ρ - d with hAdef
  have hA0 : 0 ≤ A := by linarith
  have hA : A ≤ ((q : ℚ) ^ t - 2 * ((τ + 1 : Nat) : ℚ)) / (q : ℚ) ^ t := by
    apply le_of_eq
    rw [eq_div_iff hqt1.ne']
    have h1 : (q : ℚ) ^ t = q * (q : ℚ) ^ (t - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : (q : ℚ) ^ t = (q : ℚ) ^ (s + 1) * (L : ℚ) := by
      rw [hLdef]
      push_cast
      rw [← pow_add]
      congr 1
      omega
    have e1 : 4 / (q : ℚ) * (q : ℚ) ^ t = 4 * (q : ℚ) ^ (t - 1) := by
      rw [h1]; field_simp
    have e2 : 2 / (q : ℚ) ^ (s + 1) * (q : ℚ) ^ t = 2 * (L : ℚ) := by
      rw [h2]; field_simp
    have e3 : 2 / (q : ℚ) ^ t * (q : ℚ) ^ t = 2 := by field_simp
    rw [hτdef, hAdef, hddef, hρdef]
    push_cast
    have hexp : (1 - 4 / (q : ℚ) - (2 / (q : ℚ) ^ (s + 1) + 2 / (q : ℚ) ^ t)) * (q : ℚ) ^ t =
        (q : ℚ) ^ t - 4 / (q : ℚ) * (q : ℚ) ^ t - 2 / (q : ℚ) ^ (s + 1) * (q : ℚ) ^ t -
          2 / (q : ℚ) ^ t * (q : ℚ) ^ t := by ring
    rw [hexp, e1, e2, e3]
    ring

  set e : ℚ := (r / 2) * ((q : ℚ) ^ t) ^ r * γ ^ (q ^ t) with hedef
  have he0 : 0 ≤ e := by positivity
  have hn0t : n0 ≤ q ^ t := by
    have h1 : n0 < R := by omega
    have h2 : q ^ (t - 1 - s) ≤ q ^ t := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have he : e ≤ g / 8 := by
    have h := hn0 (q ^ t) hn0t
    push_cast at h
    have : e = (r / 2) * (((q : ℚ) ^ t) ^ r * γ ^ (q ^ t)) := by rw [hedef]; ring
    rw [this]
    calc (r : ℚ) / 2 * (((q : ℚ) ^ t) ^ r * γ ^ (q ^ t)) ≤ (r : ℚ) / 2 * (g / (4 * r)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = g / 8 := by field_simp; ring
  have hLy : ∀ y : Fin m → Fin q, (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun x => ∃ k, τ + 1 ≤ stat hq hqt hrn x y k + 1)).card : ℚ) ≤
        e * (2 * (q : ℚ) ^ (m - r * t)) := by
    intro y
    have hb := Ly_bound hq hqt hrn y τ hlam
    have key : q ^ (s + 1) * (2 * q ^ (t - 1) + q ^ (t - 1 - s)) = (2 * q ^ s + 1) * q ^ t := by
      have e1 : q ^ (s + 1) * q ^ (t - 1) = q ^ s * q ^ t := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have e2 : q ^ (s + 1) * q ^ (t - 1 - s) = q ^ t := by
        rw [← pow_add]
        congr 1
        omega
      calc q ^ (s + 1) * (2 * q ^ (t - 1) + q ^ (t - 1 - s))
          = 2 * (q ^ (s + 1) * q ^ (t - 1)) + q ^ (s + 1) * q ^ (t - 1 - s) := by ring
        _ = 2 * (q ^ s * q ^ t) + q ^ t := by rw [e1, e2]
        _ = (2 * q ^ s + 1) * q ^ t := by ring
    have hlamτ : lam ^ τ = (μ ^ (2 * q ^ s + 1)) ^ (q ^ t) := by
      rw [hlamdef, ← pow_mul, ← pow_mul, hτdef, hLdef, key]
    have hnum : (q : ℚ) - 2 + 2 * lam = γ * ((q : ℚ) * μ ^ (2 * q ^ s + 1)) := by
      rw [hγdef, div_mul_cancel₀ _ hden.ne']
    have hqm : (q : ℚ) ^ (m - q ^ t) * (q : ℚ) ^ (q ^ t) = (q : ℚ) ^ m := by
      rw [← pow_add]
      congr 1
      have : q ^ t ≤ m := le_trans hqt (le_trans (Nat.le_mul_of_pos_left n hr) hrn)
      omega
    have hqm2 : ((q : ℚ) ^ t) ^ r * (q : ℚ) ^ (m - r * t) = (q : ℚ) ^ m := by
      rw [← pow_mul, ← pow_add]
      congr 1
      have : r * t ≤ m := le_trans (Nat.mul_le_mul_left r
        (le_trans (Nat.le_of_lt (lt_pow_self (by omega : 2 ≤ q) t)) hqt)) hrn
      rw [mul_comm t r]
      omega
    rw [hlamτ, hnum, mul_pow, mul_pow] at hb
    have hMt : 0 < (μ ^ (2 * q ^ s + 1)) ^ (q ^ t) := pow_pos hMpos _
    have hb2 : (((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun x => ∃ k, τ + 1 ≤ stat hq hqt hrn x y k + 1)).card : ℚ) ≤
        r * ((q : ℚ) ^ m * γ ^ (q ^ t)) := by
      have hb' : (((Finset.univ : Finset (Fin m → Fin q)).filter
          (fun x => ∃ k, τ + 1 ≤ stat hq hqt hrn x y k + 1)).card : ℚ) *
            (μ ^ (2 * q ^ s + 1)) ^ (q ^ t) ≤
          (r * ((q : ℚ) ^ m * γ ^ (q ^ t))) * (μ ^ (2 * q ^ s + 1)) ^ (q ^ t) := by
        calc _ ≤ _ := hb
          _ = _ := by rw [← hqm]; ring
      exact le_of_mul_le_mul_right hb' hMt
    calc _ ≤ r * ((q : ℚ) ^ m * γ ^ (q ^ t)) := hb2
      _ = e * (2 * (q : ℚ) ^ (m - r * t)) := by rw [hedef, ← hqm2]; ring

  have hLq : (8 * r / g : ℚ) < L := by
    have h1 : 8 * r / g ≤ (⌈8 * r / g⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ⌈8 * r / g⌉₊ < L := by omega
    have h3 : ((⌈8 * r / g⌉₊ : Nat) : ℚ) < (L : ℚ) := by exact_mod_cast h2
    linarith
  have hLpos : (0 : ℚ) < L := lt_of_le_of_lt (by positivity) hLq
  have h2rL : 2 * r / L ≤ g / 4 := by
    rw [div_le_div_iff₀ hLpos (by norm_num)]
    have := (div_lt_iff₀ hg).mp hLq
    linarith
  have hAr : ρ ^ r - r * d ≤ A ^ r := sub_pow_ge hd0 hdρ hρ1 r
  have h1p : 0 ≤ 1 - p := by linarith
  have hty : β ≤ (1 - (P : ℚ) / D) * A ^ r - (P : ℚ) / D * e := by
    rw [hPD_eq]
    have hk : (1 - p) * ρ ^ r = β + g - g / 2 * ρ ^ r := by rw [hpdef, hgdef]; ring
    have h1 : (1 - p) * (ρ ^ r - r * d) ≤ (1 - p) * A ^ r := mul_le_mul_of_nonneg_left hAr h1p
    have h2 : (1 - p) * (r * d) ≤ r * d :=
      mul_le_of_le_one_left (mul_nonneg hr0.le hd0) (by linarith)
    have h3 : p * e ≤ e := mul_le_of_le_one_left he0 hp1
    have h4 : g / 2 * ρ ^ r ≤ g / 2 := mul_le_of_le_one_right (by positivity) hρr1
    have h5 : (1 - p) * (ρ ^ r - r * d) = (1 - p) * ρ ^ r - (1 - p) * (r * d) := by ring
    linarith
  have hat : β ≤ (P : ℚ) / D * (1 - 2 * e) - (1 - (P : ℚ) / D) * (2 * r / L) := by
    rw [hPD_eq]
    have h1 : (1 - p) * (2 * r / L) ≤ 2 * r / L :=
      mul_le_of_le_one_left (by positivity) (by linarith)
    have h2 : p * (2 * e) ≤ 2 * e := mul_le_of_le_one_left (by positivity) hp1
    have h3 : p * (1 - 2 * e) = p - p * (2 * e) := by ring
    linarith
  have hpw := protocol_works hq hqt hrn hn (τ + 1) L D P (by positivity) hPD hD hTL left right
    hLy hA0 hA hty hat
  refine ⟨2 * q ^ (m - r * t), hpw, ?_⟩

  have hm_le : m ≤ (2 * r * q + 1) * q ^ t := by
    have h1 : m = r * n + m % r := by
      have := Nat.div_add_mod m r
      rw [hndef]
      omega
    have h2 : m % r < r := Nat.mod_lt m hr
    have h3 : m ≤ 2 * r * n := by
      have h5 : r ≤ r * n := Nat.le_mul_of_pos_right r hn
      calc m = r * n + m % r := h1
        _ ≤ r * n + r * n := Nat.add_le_add_left (le_trans h2.le h5) _
        _ = 2 * r * n := by ring
    have h4 : n ≤ q * q ^ t := by
      have := pow_succ' q t
      omega
    calc m ≤ 2 * r * n := h3
      _ ≤ 2 * r * (q * q ^ t) := Nat.mul_le_mul_left _ h4
      _ = (2 * r * q) * q ^ t := by ring
      _ ≤ (2 * r * q + 1) * q ^ t := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hmr_le : m ^ r ≤ (2 * r * q + 1) ^ r * q ^ (r * t) := by
    calc m ^ r ≤ ((2 * r * q + 1) * q ^ t) ^ r := Nat.pow_le_pow_left hm_le r
      _ = (2 * r * q + 1) ^ r * (q ^ t) ^ r := by rw [mul_pow]
      _ = (2 * r * q + 1) ^ r * q ^ (r * t) := by rw [← pow_mul, mul_comm t r]
  have hrtm : r * t ≤ m := le_trans (Nat.mul_le_mul_left r
    (le_trans (Nat.le_of_lt (lt_pow_self (by omega : 2 ≤ q) t)) hqt)) hrn
  calc 2 * q ^ (m - r * t) * m ^ r
      ≤ 2 * q ^ (m - r * t) * ((2 * r * q + 1) ^ r * q ^ (r * t)) :=
        Nat.mul_le_mul_left _ hmr_le
    _ = 2 * (2 * r * q + 1) ^ r * (q ^ (m - r * t) * q ^ (r * t)) := by ring
    _ = 2 * (2 * r * q + 1) ^ r * q ^ m := by rw [← pow_add, Nat.sub_add_cancel hrtm]
    _ ≤ max (m0 ^ r) (2 * (2 * r * q + 1) ^ r) * q ^ m :=
        Nat.mul_le_mul_right _ (le_max_right _ _)

private lemma best_seed {m q z M : Nat} {β : ℚ} (left right : (Fin m → Fin q) → Bool)
    (send : Fin z → (Fin m → Fin q) → Fin M) (read : Fin z → Fin M → (Fin m → Fin q) → Bool)
    (hz : 0 < z)
    (h : ∀ x y, (1 + β) * (z : ℚ) ≤ 2 * (((Finset.univ : Finset (Fin z)).filter
      (fun seed => read seed (send seed x) y = xor (xor (left x) (right y)) (par x y))).card : ℚ)) :
    ∃ seed : Fin z, (1 + β) * ((q ^ m : Nat) : ℚ) ^ 2 ≤
      2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read seed (send seed pair.1) pair.2 =
          xor (xor (left pair.1) (right pair.2)) (par pair.1 pair.2))).card : ℚ) := by
  by_contra hne
  push Not at hne
  let P : Fin z → (Fin m → Fin q) × (Fin m → Fin q) → Prop := fun seed pair =>
    read seed (send seed pair.1) pair.2 = xor (xor (left pair.1) (right pair.2)) (par pair.1 pair.2)
  have hsum : ∑ seed : Fin z, (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (P seed)).card : ℚ) =
      ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
        (((Finset.univ : Finset (Fin z)).filter (fun seed => P seed pair)).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_comm
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hz⟩⟩)
    (fun seed (_ : seed ∈ Finset.univ) => hne seed)
  have hge := Finset.card_nsmul_le_sum (Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q)))
    (fun pair => 2 * (((Finset.univ : Finset (Fin z)).filter (fun seed => P seed pair)).card : ℚ))
    ((1 + β) * (z : ℚ)) (fun pair _ => h pair.1 pair.2)
  have heq : ∑ seed : Fin z, 2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (P seed)).card : ℚ) =
      ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
        2 * (((Finset.univ : Finset (Fin z)).filter (fun seed => P seed pair)).card : ℚ) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum]
  rw [heq, Finset.sum_const] at hlt
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul] at hlt hge
  push_cast at hlt hge
  nlinarith

private lemma lower_main {q r : Nat} (hq : 5 ≤ q) {β : ℚ}
    (hlo : (1 - 4 / (q : ℚ)) ^ (r + 1) < β) (hhi : β ≤ (1 - 4 / (q : ℚ)) ^ r) :
    ∃ C : Nat, 0 < C ∧ ∀ m : Nat, 0 < m → ∀ left right : (Fin m → Fin q) → Bool,
      ∀ M : Nat, worksR m q β left right M → q ^ m ≤ C * M * m ^ r := by
  have h := lower_bound_works0 hq hlo hhi
  dsimp only at h
  obtain ⟨C1, hC1, hlb⟩ : ∃ C1 : Nat, 0 < C1 ∧ ∀ m : Nat, 0 < m → ∀ M : Nat,
      works0 m q β M → q ^ m ≤ C1 * M * m ^ r := ⟨_, h.1, h.2⟩
  refine ⟨2 * C1, by omega, fun m hm left right M hM => ?_⟩
  obtain ⟨z, send, read, hz, hall⟩ := hM
  obtain ⟨seed, hseed⟩ := best_seed left right send read hz hall
  have h0 := works_to_works0 (leftFlip := left) (rightFlip := right) ⟨send seed, read seed, hseed⟩
  calc q ^ m ≤ C1 * (2 * M) * m ^ r := hlb m hm _ h0
    _ = 2 * C1 * M * m ^ r := by ring

end PEqualNP.Outside.L_lib_953

theorem PEqualNP.Outside.L_lib_953 :
(
∀ (q r : Nat), 5 ≤ q → 0 < r →
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  ∀ β : ℚ, 0 < β → β*(1+ρ^r) < ρ^r →
    ∃ C : Nat, 0 < C ∧ ∀ m : Nat, 0 < m →
      let W := Fin m → Fin q
      let N := q^m
      ∀ left right : W → Bool,
        let truth := fun (x y : W) => xor (xor (left x) (right y))
          (((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1)
        let works := fun (M : Nat) =>
          ∃ (z : Nat) (send : Fin z → W → Fin M) (read : Fin z → Fin M → W → Bool),
            0 < z ∧ ∀ x y, (1+β)*(z : ℚ) ≤
              2*(((Finset.univ : Finset (Fin z)).filter
                (fun seed => read seed (send seed x) y = truth x y)).card : ℚ)
        (∃ M : Nat, works M ∧ M*m^r ≤ C*N) ∧
        (ρ^(r+1) < β → ∀ M : Nat, works M → N ≤ C*M*m^r)
) := by
  intro q r hq hr ρ β hβ hβρ
  have hρpos : 0 < ρ := by
    have hqpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr (by omega)
    have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    have h4 : 4 / (q : ℚ) ≤ 4 / 5 := (div_le_iff₀ hqpos).mpr (by linarith)
    show 0 < 1 - 4 / (q : ℚ)
    linarith
  have hhi : β ≤ ρ ^ r := by
    have := pow_pos hρpos r
    nlinarith
  obtain ⟨C1, hC1, hup⟩ := PEqualNP.Outside.L_lib_953.upper_main hq hr hβ hβρ
  have hlow : ∃ C2 : Nat, 0 < C2 ∧ (ρ ^ (r + 1) < β → ∀ m : Nat, 0 < m →
      ∀ left right : (Fin m → Fin q) → Bool, ∀ M : Nat,
        PEqualNP.Outside.L_lib_953.worksR m q β left right M → q ^ m ≤ C2 * M * m ^ r) := by
    by_cases hlo : ρ ^ (r + 1) < β
    · obtain ⟨C2, hC2, h⟩ := PEqualNP.Outside.L_lib_953.lower_main hq hlo hhi
      exact ⟨C2, hC2, fun _ => h⟩
    · exact ⟨1, Nat.one_pos, fun h => absurd h hlo⟩
  obtain ⟨C2, hC2, hlow⟩ := hlow
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left _ _), ?_⟩
  intro m hm W N left right truth works
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hMle⟩ := hup m hm left right
    exact ⟨M, hM, hMle.trans (Nat.mul_le_mul_right _ (le_max_left _ _))⟩
  · intro hlo M hM
    exact (hlow hlo m hm left right M hM).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right _ _)))
