import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_864

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

private lemma works0_to_works {m q : Nat} {bias : ℚ} {leftFlip rightFlip : (Fin m → Fin q) → Bool}
    {M : Nat} (h : works0 m q bias M) :
    ∃ (send : (Fin m → Fin q) → Fin (2 * M)) (read : Fin (2 * M) → (Fin m → Fin q) → Bool),
      (1 + bias) * ((q ^ m : Nat) : ℚ) ^ 2 ≤
        2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
          (fun pair => read (send pair.1) pair.2 =
            xor (xor (leftFlip pair.1) (rightFlip pair.2)) (par pair.1 pair.2))).card : ℚ) := by
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
          xor (xor (leftFlip pair.1) (rightFlip pair.2)) (par pair.1 pair.2))) =
      ((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read (send pair.1) pair.2 = par pair.1 pair.2)) := by
    apply Finset.filter_congr
    intro pair _
    have hdiv : (⟨(2 * (send pair.1).val + (leftFlip pair.1).toNat) / 2,
        by have := two_mul_add_toNat_lt (send pair.1).isLt (leftFlip pair.1); omega⟩ : Fin M) =
        send pair.1 := Fin.ext (two_mul_add_toNat_div _ _)
    rw [hdiv, two_mul_add_toNat_mod]
    exact xor_bridge2 _ _ _ _
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

private lemma works0_of_rep_bound {m q M : Nat} {bias : ℚ} (hq : 5 ≤ q)
    (r : Nat) (hhi : bias ≤ (1 - 4 / (q : ℚ)) ^ r)
    (send : (Fin m → Fin q) → Fin M) (rep : Fin M → (Fin m → Fin q))
    (hdist_le : ∀ u : Fin m → Fin q, hdist u (rep (send u)) ≤ r) :
    works0 m q bias M := by
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  let N : ℚ := ((q ^ m : Nat) : ℚ)
  have hqpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr (by omega)
  have hρ0 : 0 ≤ ρ := by
    have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    have h4 : 4 / (q : ℚ) ≤ 1 := (div_le_iff₀ hqpos).mpr (by linarith)
    dsimp [ρ]
    linarith
  have hρ1 : ρ ≤ 1 := by
    have h4 : 0 ≤ 4 / (q : ℚ) := div_nonneg (by linarith) hqpos.le
    dsimp [ρ]
    linarith
  refine ⟨send, fun c v => par (rep c) v, ?_⟩
  have hsum : ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
      sign (par (rep (send pair.1)) pair.2) * T pair.1 pair.2 =
      ∑ u : Fin m → Fin q, N * ρ ^ hdist (rep (send u)) u := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact row_corr hq (rep (send u)) u
  have hge : N ^ 2 * ρ ^ r ≤
      ∑ pair : (Fin m → Fin q) × (Fin m → Fin q),
        sign (par (rep (send pair.1)) pair.2) * T pair.1 pair.2 := by
    rw [hsum]
    calc N ^ 2 * ρ ^ r
        = ∑ _u : Fin m → Fin q, N * ρ ^ r := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          dsimp [N]
          ring
      _ ≤ ∑ u : Fin m → Fin q, N * ρ ^ hdist (rep (send u)) u := by
          refine Finset.sum_le_sum fun u _ => ?_
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply pow_le_pow_of_le_one hρ0 hρ1
          rw [hdist_symm]
          exact hdist_le u
  have h2 := sum_sign_eq_two_correct_sub send (fun c v => par (rep c) v)
  have hbias_le : N ^ 2 * bias ≤ N ^ 2 * ρ ^ r :=
    mul_le_mul_of_nonneg_left hhi (sq_nonneg N)
  dsimp [N] at hge hbias_le
  linarith

private lemma upper_bound_works0 {q r : Nat} {bias : ℚ} (hq : 5 ≤ q)
    (hhi : bias ≤ (1 - 4 / (q : ℚ)) ^ r) :
    let C2 : Nat := (2 * r * q + 1) ^ r
    0 < C2 ∧ ∀ m : Nat, 0 < m → ∃ M : Nat, works0 m q bias M ∧ M * m ^ r ≤ C2 * q ^ m := by
  let C2 : Nat := (2 * r * q + 1) ^ r
  refine ⟨Nat.pow_pos (by omega), ?_⟩
  intro m hm
  by_cases hsmall : r = 0 ∨ m < r
  · let e := Fintype.equivFin (Fin m → Fin q)
    let M := Fintype.card (Fin m → Fin q)
    have hM : M = q ^ m := by simp [M, Fintype.card_fin]
    refine ⟨M, ?_, ?_⟩
    · apply works0_of_rep_bound hq r hhi e e.symm
      intro u
      simp only [Equiv.symm_apply_apply]
      have h0 : hdist u u = 0 := (hdist_eq_zero_iff u u).mpr rfl
      omega
    · rw [hM, mul_comm (q ^ m)]
      apply Nat.mul_le_mul_right
      rcases hsmall with rfl | hmr
      · simp
      · exact Nat.pow_le_pow_left (by nlinarith) r
  · push Not at hsmall
    rcases hsmall with ⟨hr0, hrm⟩
    have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
    let n : Nat := m / r
    have hn_pos : 0 < n := Nat.div_pos hrm hr1
    have hrn_le : r * n ≤ m := Nat.mul_div_le m r
    rcases exists_pow_le_lt (by omega : 2 ≤ q) n hn_pos with ⟨t, hqt, hlt_qt1⟩
    have htn : t ≤ n := le_trans (Nat.le_of_lt (lt_pow_self (by omega : 2 ≤ q) t)) hqt
    let e := Fintype.equivFin
      ((Fin r → (NonPivot q n t → Fin q)) × ({i : Fin m // r * n ≤ i.val} → Fin q))
    let M := Fintype.card
      ((Fin r → (NonPivot q n t → Fin q)) × ({i : Fin m // r * n ≤ i.val} → Fin q))
    have hcardRem : Fintype.card {i : Fin m // r * n ≤ i.val} = m - r * n := by
      let emb : Fin (r * n) → Fin m := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hrn_le⟩
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
    have hM : M = q ^ (m - r * t) := by
      have hcardNP := card_NonPivot hq hqt
      have h1 : M = (q ^ (n - t)) ^ r * q ^ (m - r * n) := by
        dsimp only [M]
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, hcardNP, hcardRem]
      rw [h1, ← pow_mul, ← pow_add]
      congr 1
      have hrt : r * t ≤ r * n := Nat.mul_le_mul_left r htn
      have hmulsub : (n - t) * r = r * n - r * t := by
        rw [Nat.sub_mul, mul_comm n r, mul_comm t r]
      omega
    let blk : (Fin m → Fin q) → Fin r → (Fin n → Fin q) := fun u k j =>
      u ⟨k.val * n + j.val, by
        have hk := k.isLt; have hj := j.isLt
        have : (k.val + 1) * n ≤ r * n := Nat.mul_le_mul_right n hk
        nlinarith⟩
    let encode : (Fin m → Fin q) →
        ((Fin r → (NonPivot q n t → Fin q)) × ({i : Fin m // r * n ≤ i.val} → Fin q)) := fun u =>
      (fun k np => correctBlock hq hqt (blk u k) np.val, fun i => u i.val)
    let decode : ((Fin r → (NonPivot q n t → Fin q)) × ({i : Fin m // r * n ≤ i.val} → Fin q)) →
        (Fin m → Fin q) := fun msg i =>
      if hi : i.val < r * n then
        reconstructBlock hq hqt (msg.1 ⟨i.val / n,
          (Nat.div_lt_iff_lt_mul hn_pos).mpr hi⟩)
          ⟨i.val % n, Nat.mod_lt _ hn_pos⟩
      else
        msg.2 ⟨i, Nat.le_of_not_lt hi⟩
    refine ⟨M, ?_, ?_⟩
    · apply works0_of_rep_bound hq r hhi (fun u => e (encode u)) (fun c => decode (e.symm c))
      intro u
      simp only [Equiv.symm_apply_apply]
      let badImg : Finset (Fin m) := Finset.univ.image (fun k : Fin r =>
        (⟨k.val * n + jStar hqt (blk u k), by
          have hk := k.isLt
          have hj := lt_of_lt_of_le (jStar_lt hq hqt (blk u k)) hqt
          have : (k.val + 1) * n ≤ r * n := Nat.mul_le_mul_right n hk
          nlinarith⟩ : Fin m))
      have hsub : (Finset.univ : Finset (Fin m)).filter (fun i => u i ≠ decode (encode u) i) ⊆
          badImg := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_cases hirn : i.val < r * n
        · let k : Fin r := ⟨i.val / n,
            (Nat.div_lt_iff_lt_mul hn_pos).mpr hirn⟩
          let j : Fin n := ⟨i.val % n, Nat.mod_lt _ hn_pos⟩
          have hdec : decode (encode u) i = correctBlock hq hqt (blk u k) j := by
            dsimp only [decode, encode]
            simp only [hirn, ↓reduceDIte]
            have hrec := reconstructBlock_eq hq hqt (correctBlock hq hqt (blk u k))
              (syndrome_correctBlock hq hqt (blk u k))
            exact congrFun hrec j
          have hkj : k.val * n + j.val = i.val := by
            dsimp [k, j]
            rw [mul_comm]
            exact Nat.div_add_mod i.val n
          have hblk : blk u k j = u i := by
            dsimp [blk]
            congr 1
            exact Fin.ext hkj
          rw [hdec, ← hblk] at hi
          have hjstar : j.val = jStar hqt (blk u k) := by
            by_contra hne
            dsimp only [correctBlock] at hi
            simp only [hne, ↓reduceIte] at hi
            exact hi rfl
          rw [Finset.mem_image]
          refine ⟨k, Finset.mem_univ k, Fin.ext ?_⟩
          dsimp only
          rw [← hjstar, hkj]
        · dsimp only [decode, encode] at hi
          simp only [hirn, ↓reduceDIte] at hi
          exact absurd rfl hi
      exact (Finset.card_le_card hsub).trans
        (Finset.card_image_le.trans (by simp [Fintype.card_fin]))
    · have hm_le : m ≤ (2 * r * q + 1) * q ^ t := by
        have h1 : m = r * n + m % r := by
          have := Nat.div_add_mod m r
          dsimp [n]
          omega
        have h2 : m % r < r := Nat.mod_lt m hr1
        have h3 : m ≤ 2 * r * n := by nlinarith
        have h4 : n ≤ q * q ^ t := by
          have := pow_succ' q t
          omega
        calc m ≤ 2 * r * n := h3
          _ ≤ 2 * r * (q * q ^ t) := Nat.mul_le_mul_left _ h4
          _ = (2 * r * q) * q ^ t := by ring
          _ ≤ (2 * r * q + 1) * q ^ t := Nat.mul_le_mul_right _ (Nat.le_succ _)
      have hmr_le : m ^ r ≤ C2 * q ^ (r * t) := by
        calc m ^ r ≤ ((2 * r * q + 1) * q ^ t) ^ r := Nat.pow_le_pow_left hm_le r
          _ = C2 * (q ^ t) ^ r := by rw [mul_pow]
          _ = C2 * q ^ (r * t) := by rw [← pow_mul, mul_comm t r]
      rw [hM]
      have hrtm : r * t ≤ m := le_trans (Nat.mul_le_mul_left r htn) hrn_le
      calc q ^ (m - r * t) * m ^ r
          ≤ q ^ (m - r * t) * (C2 * q ^ (r * t)) := Nat.mul_le_mul_left _ hmr_le
        _ = C2 * (q ^ (m - r * t) * q ^ (r * t)) := by ring
        _ = C2 * q ^ (m - r * t + r * t) := by rw [← pow_add]
        _ = C2 * q ^ m := by rw [Nat.sub_add_cancel hrtm]

end PEqualNP.Outside.L_lib_864

theorem PEqualNP.Outside.L_lib_864 :
∀ (q : Nat), 5 ≤ q →
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  ∀ (r : Nat) (bias : ℚ), ρ^(r+1) < bias → bias ≤ ρ^r →
  ∃ C : Nat, 0 < C ∧ ∀ m : Nat, 0 < m →
    let W := Fin m → Fin q
    let N := q^m
    ∀ (leftFlip rightFlip : W → Bool),
    let target := fun (u v : W) =>
      xor (xor (leftFlip u) (rightFlip v))
        (((Finset.univ : Finset (Fin m)).filter (fun i => u i = v i)).card % 2 == 1)
    let works := fun (messages : Nat) =>
      ∃ (send : W → Fin messages) (read : Fin messages → W → Bool),
        let correct := ((Finset.univ : Finset (W × W)).filter
          (fun pair => read (send pair.1) pair.2 = target pair.1 pair.2)).card
        (1+bias) * (N : ℚ)^2 ≤ 2*(correct : ℚ)
    (∀ M : Nat, works M → N ≤ C*M*m^r) ∧
      ∃ M : Nat, works M ∧ M*m^r ≤ C*N := by
  intro q hq ρ r bias hlo hhi
  have hlb := PEqualNP.Outside.L_lib_864.lower_bound_works0 hq hlo hhi
  have hub := PEqualNP.Outside.L_lib_864.upper_bound_works0 hq hhi
  dsimp only at hlb hub
  rcases hlb with ⟨hC1pos, hlb⟩
  rcases hub with ⟨hC2pos, hub⟩
  set C1 := (PEqualNP.Outside.L_lib_864.decay
    (bias ^ 2 - (1 - 4 / (q : ℚ)) ^ (2 * r + 2)) (2 * r + 1)).den * q ^ (5 * r + 2)
  set C2 := (2 * r * q + 1) ^ r
  refine ⟨max (2 * C1) (2 * C2), lt_of_lt_of_le (by omega) (le_max_left _ _), ?_⟩
  intro m hm W N leftFlip rightFlip target works
  constructor
  · intro M hM
    have h0 := PEqualNP.Outside.L_lib_864.works_to_works0 hM
    have hle := hlb m hm (2 * M) h0
    have hC1 : 2 * C1 ≤ max (2 * C1) (2 * C2) := le_max_left _ _
    calc N ≤ C1 * (2 * M) * m ^ r := hle
      _ = (2 * C1) * M * m ^ r := by ring
      _ ≤ max (2 * C1) (2 * C2) * M * m ^ r :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC1)
  · rcases hub m hm with ⟨M0, hM0, hM0le⟩
    refine ⟨2 * M0, PEqualNP.Outside.L_lib_864.works0_to_works hM0, ?_⟩
    have hC2 : 2 * C2 ≤ max (2 * C1) (2 * C2) := le_max_right _ _
    calc 2 * M0 * m ^ r = 2 * (M0 * m ^ r) := by ring
      _ ≤ 2 * (C2 * N) := Nat.mul_le_mul_left 2 hM0le
      _ = (2 * C2) * N := by ring
      _ ≤ max (2 * C1) (2 * C2) * N := Nat.mul_le_mul_right N hC2
