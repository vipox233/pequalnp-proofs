import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1013_aux

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

private lemma radius_code {q r : Nat} (hq : 5 ≤ q) :
    let C2 : Nat := (2 * r * q + 1) ^ r
    0 < C2 ∧ ∀ m : Nat, 0 < m → ∃ M : Nat, (∃ (send : (Fin m → Fin q) → Fin M) (rep : Fin M → (Fin m → Fin q)), ∀ u, hdist u (rep (send u)) ≤ r) ∧ M * m ^ r ≤ C2 * q ^ m := by
  let C2 : Nat := (2 * r * q + 1) ^ r
  refine ⟨Nat.pow_pos (by omega), ?_⟩
  intro m hm
  by_cases hsmall : r = 0 ∨ m < r
  · let e := Fintype.equivFin (Fin m → Fin q)
    let M := Fintype.card (Fin m → Fin q)
    have hM : M = q ^ m := by simp [M, Fintype.card_fin]
    refine ⟨M, ?_, ?_⟩
    · refine ⟨e, e.symm, ?_⟩
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
    · refine ⟨fun u => e (encode u), fun c => decode (e.symm c), ?_⟩
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

private lemma oriented_card {m q k b : Nat} (hm : 0 < m) (hq : 1 ≤ q) (u u' : Fin m → Fin q) (hdle : hdist u u' ≤ b) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter (fun w => hdist u w ≤ hdist u u' ∧ hdist u' w ≤ 2*k+1)).card ≤ q^(b+k)*m^k := by
  let D : Finset (Fin m) := Finset.univ.filter (fun i => u i ≠ u' i)
  let E : Finset (Fin m) := Finset.univ.filter (fun i => u i = u' i)
  have hDcard : D.card = hdist u u' := rfl
  let A := (Fin k → Fin m × Fin q) × ({i : Fin m // i ∈ D} → Fin q)
  let F : A → (Fin m → Fin q) := fun a =>
    patchFin k a.1 (fun i => if h : i ∈ D then a.2 ⟨i, h⟩ else u i)
  have hsub : ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun w => hdist u w ≤ hdist u u' ∧ hdist u' w ≤ 2*k+1)) ⊆ Finset.univ.image F := by
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
  have hpow : q ^ D.card ≤ q ^ (b) := Nat.pow_le_pow_right hq hdle
  calc ((Finset.univ : Finset (Fin m → Fin q)).filter
          (fun w => hdist u w ≤ hdist u u' ∧ hdist u' w ≤ 2*k+1)).card
      ≤ (m * q) ^ k * q ^ D.card := hcard
    _ ≤ (m * q) ^ k * q ^ (b) := Nat.mul_le_mul_left _ hpow
    _ = q ^ (b + k) * m ^ k := by rw [mul_pow, pow_add]; ring

private lemma choose_fibers {X : Type} [Fintype X] {M k : ℕ} (hM : 0 < M)
    (hk : k ≤ M) (f : X → Fin M) :
    ∃ U : Finset (Fin M), U.card = k ∧ k * Fintype.card X ≤
      M * (Finset.univ.filter fun x => f x ∈ U).card := by
  classical
  let : NeZero M := ⟨Nat.ne_of_gt hM⟩
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin M)))
    (n := k) (by simpa using hk)
  let U (t : Fin M) := Finset.univ.filter fun z : Fin M => z - t ∈ T
  have cnt (e : Fin M ≃ Fin M) : (∑ z, if e z ∈ T then 1 else 0 : ℕ) = k := by
    rw [e.sum_comp (fun z => if z ∈ T then (1:ℕ) else 0)]
    simpa using hT
  have size (t : Fin M) : (U t).card = k := by
    rw [Finset.card_filter]
    exact cnt (Equiv.subRight t)
  let coverage (t : Fin M) := (Finset.univ.filter fun x => f x ∈ U t).card
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin M)) coverage
    Finset.univ_nonempty
  refine ⟨U t, size t, ?_⟩
  have mass : (∑ t, coverage t) = k * Fintype.card X := by
    simp only [coverage, Finset.card_filter, U, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_comm]
    calc _ = ∑ _x : X, k := Finset.sum_congr rfl fun x _ => cnt (Equiv.subLeft (f x))
         _ = _ := by simp [Nat.mul_comm]
  rw [← mass]
  exact (Finset.sum_le_sum ht).trans_eq (by simp [coverage])

private lemma density_remainder {q m k : Nat} (hq : 1 ≤ q) (hm : 0 < m)
    {δ : ℚ} (hδ : 0 < δ) (h1 : δ ≤ 1) (S : Finset (Fin m → Fin q)) :
    (pairCount S (2*k+1) : ℚ) ≤ δ * (S.card : ℚ)^2 +
      ((q^(5*k+2) : Nat) : ℚ) / decay δ (2*k+1) * (m : ℚ)^k * (S.card : ℚ) := by
  let D := decay δ (2*k+1)
  let K := q^(5*k+2)
  have hD : 0 < D := decay_pos hδ _
  have hK : 0 < K := pow_pos hq _
  have hCt : 0 ≤ ((K:ℚ) / D) * (m:ℚ)^k := by positivity
  by_cases hs : S.card = 0
  · have he := Finset.card_eq_zero.mp hs
    simp [he, pairCount]
  have hS : (0:ℚ) < S.card := Nat.cast_pos.mpr (by omega)
  change _ ≤ δ * _ + (K:ℚ) / D * _ * _
  by_cases hd : δ ≤ qClass S (2*k+1)
  · let x : ℚ := ((K * m^k : Nat) : ℚ) / (S.card : ℚ)
    have hK1 : 1 ≤ K*m^k := Nat.mul_pos hK (Nat.pow_pos hm)
    have hzero : qClass S 0 ≤ x := by
      unfold qClass
      rw [pairCount_zero]
      have he : (S.card:ℚ) / (S.card:ℚ)^2 = 1 / (S.card:ℚ) := by field_simp [hS.ne']
      rw [he]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hK1) hS.le
    have hstep (l : Nat) (hl : 1 ≤ l) (hl' : l ≤ 2*k+1) :
        (qClass S l)^2 ≤ qClass S (l-1)+x := by
      apply (qClass_sq_le hm hq S (by omega) l hl).trans
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hS.le
      exact_mod_cast Nat.mul_le_mul (Nat.pow_le_pow_right hq (by omega : 2*l+l/2 ≤ 5*k+2))
        (Nat.pow_le_pow_right hm (by omega : l/2 ≤ k))
    have hb : D ≤ x := iter_decay hδ h1 hd hzero hstep
    have hmul := (le_div_iff₀ hS).mp hb
    have hcard : (S.card:ℚ) ≤ (K:ℚ) / D * (m:ℚ)^k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hD]
      push_cast at hmul
      linarith
    have hsimple : pairCount S (2*k+1) ≤ S.card*S.card :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _)
    have hp : (pairCount S (2*k+1):ℚ) ≤ (S.card:ℚ)*(S.card:ℚ) := by exact_mod_cast hsimple
    exact hp.trans ((mul_le_mul_of_nonneg_right hcard hS.le).trans (le_add_of_nonneg_left (by positivity)))
  · have hsmall := (div_le_iff₀ (sq_pos_of_pos hS)).mp (le_of_not_ge hd : qClass S (2*k+1) ≤ δ)
    exact hsmall.trans (le_add_of_nonneg_right (mul_nonneg hCt hS.le))

private def escape {q m : ℕ} (S : Finset (Fin m → Fin q)) (a : Fin m → Fin q) (d : ℕ) :=
  S.filter fun x => d < hdist a x

private def farPairs {q m : ℕ} (S : Finset (Fin m → Fin q)) (d : ℕ) :=
  ((S ×ˢ S).filter fun z => d < hdist z.1 z.2).card

private lemma anchor_point {q m : ℕ} (S : Finset (Fin m → Fin q)) (hs : S.Nonempty) (d : ℕ) :
    ∃ a ∈ S, S.card * (escape S a d).card ≤ farPairs S d := by
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S (fun x => (escape S x d).card) hs
  refine ⟨a, ha, ?_⟩
  have he : farPairs S d = ∑ x ∈ S, (escape S x d).card := by
    simp only [farPairs, escape, Finset.card_filter, Finset.sum_product]
  rw [he]
  simpa using Finset.sum_le_sum hmin

private lemma anchor_split {q m k : Nat} (hq : 1 ≤ q) (hm : 0 < m)
    (S : Finset (Fin m → Fin q)) (a : Fin m → Fin q) :
    pairCount S (2*k+1) ≤ 2*(q^(5*k+4)*m^k)*S.card + pairCount (escape S a (2*k+2)) (2*k+1) := by
  classical
  let d := 2*k+1
  let b := 4*k+4
  let R := escape S a (2*k+2)
  let orient (x y : Fin m → Fin q) := hdist a x ≤ b ∧ hdist a y ≤ hdist a x ∧ hdist x y ≤ d
  let F := (S ×ˢ S).filter fun z => orient z.1 z.2
  let G := (S ×ˢ S).filter fun z => orient z.2 z.1
  let Z := (R ×ˢ R).filter fun z => hdist z.1 z.2 ≤ d
  have sub : ((S ×ˢ S).filter fun z => hdist z.1 z.2 ≤ d) ⊆ (F ∪ G) ∪ Z := by
    intro z hz
    obtain ⟨hxy,hd⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    simp only [F,G,Z,R,escape,Finset.mem_union,Finset.mem_filter,Finset.mem_product,hx,hy,hd,true_and,and_true]
    have ht := hdist_triangle a z.1 z.2
    have ht' := hdist_triangle a z.2 z.1
    have hs := hdist_symm z.1 z.2
    dsimp [orient,b,d] at *
    omega
  have one (x : Fin m → Fin q) : (S.filter (orient x)).card ≤ q^(5*k+4)*m^k := by
    by_cases h : hdist a x ≤ b
    · have hsub : S.filter (orient x) ⊆ Finset.univ.filter (fun y => hdist a y ≤ hdist a x ∧ hdist x y ≤ 2*k+1) := by
        intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.2⟩
      have hb : b+k = 5*k+4 := by dsimp [b]; omega
      simpa only [hb] using (Finset.card_le_card hsub).trans (oriented_card (k:=k) hm hq a x h)
    · have emp : S.filter (orient x) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro y _ hxy
        exact h hxy.1
      simp [emp]
  have fcount : F.card ≤ S.card*(q^(5*k+4)*m^k) := by
    have he : F.card = ∑ x ∈ S, (S.filter (orient x)).card := by
      simp only [F,Finset.card_filter,Finset.sum_product]
    rw [he]
    simpa using Finset.sum_le_sum (s:=S) (fun x _ => one x)
  have same : G.card = F.card := by
    simp only [F,G,Finset.card_filter,Finset.sum_product]
    exact Finset.sum_comm
  have hc := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have hc' := Finset.card_union_le F G
  change pairCount S d ≤ _ at hc
  have hz : Z.card = pairCount R d := rfl
  rw [same] at hc'
  rw [hz] at hc
  change pairCount S d ≤ 2*(q^(5*k+4)*m^k)*S.card + pairCount R d
  nlinarith


private def pairConst (q k : ℕ) (δ : ℚ) : ℚ :=
  2 * (q:ℚ)^(5*k+4) + (q:ℚ)^(5*k+2) / decay δ (2*k+1)

private lemma close_against_far {q m k : Nat} (hq : 1 ≤ q) (hm : 0 < m)
    {δ : ℚ} (hδ : 0 < δ) (h1 : δ ≤ 1) (S : Finset (Fin m → Fin q)) :
    (pairCount S (2*k+1) : ℚ) ≤ δ * (farPairs S (2*k+2):ℚ) +
      pairConst q k δ * (m:ℚ)^k * (S.card:ℚ) := by
  by_cases hn : S.Nonempty
  · obtain ⟨a, _, ha⟩ := anchor_point S hn (2*k+2)
    let R := escape S a (2*k+2)
    have hsub : R.card ≤ S.card := Finset.card_filter_le _ _
    have hs : R.card^2 ≤ farPairs S (2*k+2) := by
      rw [sq]; exact (Nat.mul_le_mul_right _ hsub).trans ha
    have hs' : (R.card:ℚ)^2 ≤ (farPairs S (2*k+2):ℚ) := by exact_mod_cast hs
    have hsub' : (R.card:ℚ) ≤ (S.card:ℚ) := by exact_mod_cast hsub
    have e := anchor_split (k:=k) hq hm S a
    have e' : (pairCount S (2*k+1):ℚ) ≤ 2*((q:ℚ)^(5*k+4)*(m:ℚ)^k)*(S.card:ℚ) + (pairCount R (2*k+1):ℚ) := by exact_mod_cast e
    have h := density_remainder (k:=k) hq hm hδ h1 R
    push_cast at h
    have hD := decay_pos hδ (2*k+1)
    have hcoef : 0 ≤ (q:ℚ)^(5*k+2) / decay δ (2*k+1) * (m:ℚ)^k := by positivity
    have hsmall := mul_le_mul_of_nonneg_left hsub' hcoef
    have hfar := mul_le_mul_of_nonneg_left hs' hδ.le
    unfold pairConst
    linarith
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn,pairCount,farPairs]

private lemma potential_bound {q m k : Nat} (hq : 1 ≤ q) (hm : 0 < m)
    {ρ : ℚ} (hp : 0 < ρ) (hlt : ρ < 1) (S : Finset (Fin m → Fin q)) :
    let v := ρ^(2*k+2)
    (∑ z ∈ S ×ˢ S, ρ^hdist z.1 z.2) ≤ (S.card:ℚ)^2*v +
      pairConst q k (v*(1-ρ)) * (m:ℚ)^k * (S.card:ℚ) := by
  intro v
  let δ := v*(1-ρ)
  have hv : 0 < v := pow_pos hp _
  have hv1 : v ≤ 1 := pow_le_one₀ hp.le hlt.le
  have hd : 0 < δ := mul_pos hv (sub_pos.mpr hlt)
  have hd1 : δ ≤ 1 := (mul_le_mul_of_nonneg_left (by linarith : 1-ρ ≤ 1) hv.le).trans (by simpa using hv1)
  have h := close_against_far (k:=k) hq hm hd hd1 S
  let d := 2*k+2
  have point (p : (Fin m → Fin q) × (Fin m → Fin q)) :
      ρ^hdist p.1 p.2 ≤ v + (if hdist p.1 p.2 ≤ 2*k+1 then (1:ℚ) else 0) -
        (if d < hdist p.1 p.2 then δ else 0) := by
    by_cases hnear : hdist p.1 p.2 ≤ 2*k+1
    · have hnot : ¬d < hdist p.1 p.2 := by dsimp [d]; omega
      simp only [hnear,hnot,ite_true,ite_false,sub_zero]
      linarith [pow_le_one₀ hp.le hlt.le (n:=hdist p.1 p.2)]
    · by_cases hfar : d < hdist p.1 p.2
      · have hb := pow_le_pow_of_le_one hp.le hlt.le (show d+1 ≤ hdist p.1 p.2 from hfar)
        simp only [hnear,hfar,ite_false,ite_true,add_zero]
        rw [pow_succ] at hb
        change ρ^hdist p.1 p.2 ≤ v - v*(1-ρ)
        change ρ^hdist p.1 p.2 ≤ v*ρ at hb
        linarith
      · have he : hdist p.1 p.2 = d := by dsimp [d] at *; omega
        simp [he,d,v]
  have hh := Finset.sum_le_sum (s:=S ×ˢ S) (fun z _ => point z)
  have pred (f : (Fin m → Fin q) × (Fin m → Fin q) → Prop) [DecidablePred f] (c : ℚ) :
      (∑ z ∈ S ×ˢ S, if f z then c else 0) = (((S ×ˢ S).filter f).card:ℚ)*c := by
    simp [Finset.sum_ite]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.card_product,
    nsmul_eq_mul,Nat.cast_mul,pred,mul_one] at hh
  change (∑ z ∈ S ×ˢ S, ρ^hdist z.1 z.2) ≤ _ + (pairCount S (2*k+1):ℚ) - (farPairs S (2*k+2):ℚ)*δ at hh
  change _ ≤ _ + pairConst q k δ * _ * _
  nlinarith

set_option maxHeartbeats 1000000 in
private lemma blend_codes {m q n p k j : ℕ} (hq : 5 ≤ q) (hp : 0 < p) (hj : j ≤ p)
    (s : (Fin m → Fin q) → Fin n) (u : Fin n → (Fin m → Fin q))
    (t : (Fin m → Fin q) → Fin p) (v : Fin p → (Fin m → Fin q))
    (hu : ∀ x, hdist x (u (s x)) ≤ k+1) (hv : ∀ x, hdist x (v (t x)) ≤ k)
    (ρ β : ℚ) (he : ρ = 1-4/(q:ℚ)) (hρ : 0 < ρ) (h1 : ρ < 1)
    (hjβ : (β-ρ^(k+1))*(p:ℚ) ≤ (j:ℚ)*(ρ^k-ρ^(k+1))) : works0 m q β (n+j) := by
  classical
  let W := Fin m → Fin q
  let N := q^m
  let a := ρ^(k+1)
  let b := ρ^k
  have hab : 0 ≤ b-a := sub_nonneg.mpr (pow_le_pow_of_le_one hρ.le h1.le (Nat.le_succ k))
  obtain ⟨U, hU, hmass⟩ := choose_fibers hp hj t
  let G := (Finset.univ.filter fun x => t x ∈ U).card
  let e : (Fin n ⊕ U) ≃ Fin (n+j) := Fintype.equivFinOfCardEq (by simp [hU])
  let send (x : W) := if h : t x ∈ U then e (.inr ⟨t x,h⟩) else e (.inl (s x))
  let rep (z : Fin (n+j)) : W := Sum.elim u (fun w : U => v w.val) (e.symm z)
  have row (x : W) : a + (if t x ∈ U then b-a else 0) ≤ ρ^hdist (rep (send x)) x := by
    by_cases h : t x ∈ U
    · simp [rep,send,h]
      apply pow_le_pow_of_le_one hρ.le h1.le
      rw [hdist_symm]; exact hv x
    · simp only [rep,send,h,↓reduceDIte,Equiv.symm_apply_apply,Sum.elim_inl,ite_false,add_zero]
      apply pow_le_pow_of_le_one hρ.le h1.le
      rw [hdist_symm]; exact hu x
  have hN : Fintype.card W = N := by simp [W,N]
  have hmg : (j:ℚ)*(N:ℚ) ≤ (p:ℚ)*(G:ℚ) := by
    rw [← hN]; exact_mod_cast hmass
  have hP : (0:ℚ) < p := by exact_mod_cast hp
  have hbudget : (β-a)*(N:ℚ) ≤ (G:ℚ)*(b-a) := by
    apply le_of_mul_le_mul_right (a:= (p:ℚ)) _ hP
    calc (β-a)*(N:ℚ)*(p:ℚ) = (β-a)*(p:ℚ)*(N:ℚ) := by ring
         _ ≤ (j:ℚ)*(b-a)*(N:ℚ) := mul_le_mul_of_nonneg_right hjβ (by positivity)
         _ = (j:ℚ)*(N:ℚ)*(b-a) := by ring
         _ ≤ (p:ℚ)*(G:ℚ)*(b-a) := mul_le_mul_of_nonneg_right hmg hab
         _ = _ := by ring
  have hsum : (N:ℚ)*β ≤ ∑ x : W, ρ^hdist (rep (send x)) x := by
    have hrows := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => row x)
    have hcnt : (∑ x : W, if t x ∈ U then b-a else 0) = (G:ℚ)*(b-a) := by
      rw [Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,add_zero,nsmul_eq_mul]
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,hN,nsmul_eq_mul,hcnt] at hrows
    linarith
  refine ⟨send, fun z y => par (rep z) y, ?_⟩
  have hsign := sum_sign_eq_two_correct_sub send (fun z y => par (rep z) y)
  have hc : (∑ z : W × W, sign (par (rep (send z.1)) z.2)*T z.1 z.2) =
      (N:ℚ)*(∑ x : W, ρ^hdist (rep (send x)) x) := by
    rw [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    change (∑ y : Fin m → Fin q, sign (par (rep (send x)) y)*T x y) = (N:ℚ)*ρ^hdist (rep (send x)) x
    rw [he]; exact row_corr hq (rep (send x)) x
  rw [hc] at hsign
  change (1+β)*(N:ℚ)^2 ≤ _
  change (N:ℚ)*_ = 2*_-(N:ℚ)^2 at hsign
  linarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α:=ℚ) N)]

private lemma square_classes {m q M : Nat} {bias v err : ℚ} (hq : 5 ≤ q) (hbias : 0 < bias)
    (send : (Fin m → Fin q) → Fin M) (read : Fin M → (Fin m → Fin q) → Bool)
    (hcorr : (1 + bias) * ((q ^ m : Nat) : ℚ) ^ 2 ≤
      2 * (((Finset.univ : Finset ((Fin m → Fin q) × (Fin m → Fin q))).filter
        (fun pair => read (send pair.1) pair.2 = par pair.1 pair.2)).card : ℚ))
    (he : 0 ≤ err) (hclasses : ∀ S : Finset (Fin m → Fin q),
      (∑ z ∈ S ×ˢ S, (1-4/(q:ℚ))^hdist z.1 z.2) ≤ (S.card:ℚ)^2*v + err*(S.card:ℚ)) :
    bias^2 * ((q^m:Nat):ℚ) ≤ ((q^m:Nat):ℚ)*v+(M:ℚ)*err := by
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
  have hsum : ∑ c ∈ Cpos send, ((cls send c).card : ℚ)⁻¹ *
        ∑ p ∈ cls send c ×ˢ cls send c, ρ ^ hdist p.1 p.2 ≤ N*v+(M:ℚ)*err := by
    calc _ ≤ ∑ c ∈ Cpos send, (((cls send c).card:ℚ)*v + err) := by
               refine Finset.sum_le_sum fun c hc => ?_
               have hpos : 0 < (cls send c).card := (Finset.mem_filter.mp hc).2
               have hpos' : (0:ℚ) < (cls send c).card := Nat.cast_pos.mpr hpos
               rw [inv_mul_eq_div, div_le_iff₀ hpos']
               apply (hclasses (cls send c)).trans_eq
               ring
         _ = N*v+((Cpos send).card:ℚ)*err := by
               rw [Finset.sum_add_distrib,← Finset.sum_mul,← Nat.cast_sum,sum_cls_card,
                 Finset.sum_const,nsmul_eq_mul]
         _ ≤ _ := by
               have hc : (Cpos send).card ≤ M := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
               gcongr
  change bias^2*N ≤ N*v+(M:ℚ)*err
  apply le_of_mul_le_mul_right _ (pow_pos hNpos 3)
  calc bias^2*N*N^3 = (bias*N^2)^2 := by ring
       _ ≤ N^2*(N*_) := hsq1
       _ ≤ N^2*(N*(N*v+(M:ℚ)*err)) := by gcongr
       _ = _ := by ring

private def transitionScale (q k m : Nat) (d : ℚ) : ℚ :=
  ((q^m:Nat):ℚ)/(m:ℚ)^k*(1/(m:ℚ)+d)

private lemma scaled_radius {m k : Nat} (hm : 0 < m) (t C N : ℚ)
    (h : t*(m:ℚ)^(k+1) ≤ C*N) : t ≤ C*(N/(m:ℚ)^k)*(1/(m:ℚ)) := by
  have p : (0:ℚ) < m := Nat.cast_pos.mpr hm
  calc t ≤ C*N/(m:ℚ)^(k+1) := (le_div_iff₀ (pow_pos p _)).mpr h
       _ = _ := by rw [pow_succ,div_mul_eq_div_div]; ring

private lemma falloff_range {q : Nat} (hq : 5 ≤ q) :
    0 < 1-4/(q:ℚ) ∧ 1-4/(q:ℚ) < 1 := by
  have p : (0:ℚ) < q := Nat.cast_pos.mpr (by omega)
  have t : (4:ℚ) < q := by exact_mod_cast (by omega : 4 < q)
  exact ⟨sub_pos.mpr ((div_lt_one p).mpr t), sub_lt_self _ (div_pos (by norm_num) p)⟩

set_option maxHeartbeats 1000000 in
private lemma uniform_upper {q k : Nat} (hq : 5 ≤ q) :
    let ρ := 1-4/(q:ℚ)
    ∃ C : ℚ, ∀ (m : ℕ) (β : ℚ), 0 < m → ρ^(k+1) ≤ β → β ≤ ρ^k →
      ∃ M : Nat, works0 m q β M ∧ (M:ℚ) ≤ C*transitionScale q k m (β-ρ^(k+1)) := by
  intro ρ
  let a := ρ^(k+1)
  let b := ρ^k
  let g := b-a
  obtain ⟨hρ,h1⟩ := falloff_range hq
  have hg : 0 < g := by
    change 0 < ρ^k-ρ^(k+1); rw [pow_succ]
    exact sub_pos.mpr (mul_lt_of_lt_one_right (pow_pos hρ k) h1)
  let A : Nat := (2*(k+1)*q+1)^(k+1)
  let B : Nat := (2*k*q+1)^k
  let C : ℚ := max (2*(A:ℚ)) ((B:ℚ)/g)
  refine ⟨C, ?_⟩
  intro m β hm hlo hhi
  let d := β-a
  let N := q^m
  let E := (N:ℚ)/(m:ℚ)^k
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hd : 0 ≤ d := sub_nonneg.mpr hlo
  have hfrac : d/g ≤ 1 := (div_le_one hg).mpr (sub_le_sub_right hhi a)
  obtain ⟨n, ⟨s,u,hu⟩, cn⟩ := (radius_code (r:=k+1) hq).2 m hm
  obtain ⟨p, ⟨t,v,hv⟩, cp⟩ := (radius_code (r:=k) hq).2 m hm
  let z : Fin m → Fin q := fun _ => ⟨0,by omega⟩
  have hp0 : 0 < p := Nat.zero_lt_of_lt (t z).isLt
  have hn0 : (1:ℚ) ≤ n := by exact_mod_cast Nat.zero_lt_of_lt (s z).isLt
  have hD : 0 ≤ d/g := div_nonneg hd hg.le
  let w := d/g*(p:ℚ)
  let j := ⌈w⌉₊
  have hw : 0 ≤ w := mul_nonneg hD (Nat.cast_nonneg _)
  have hj : j ≤ p := Nat.ceil_le.mpr ((mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg (α:=ℚ) p)).trans_eq (one_mul _))
  have hjβ : d*(p:ℚ) ≤ (j:ℚ)*g := by
    calc d*(p:ℚ) = w*g := by dsimp [w]; field_simp [hg.ne']
         _ ≤ (j:ℚ)*g := mul_le_mul_of_nonneg_right (Nat.le_ceil w) hg.le
  have wks := blend_codes hq hp0 hj s u t v hu hv ρ β rfl hρ h1 hjβ
  refine ⟨n+j, wks, ?_⟩
  have hm' : (0:ℚ) < m := Nat.cast_pos.mpr hm
  have hn : (n:ℚ) ≤ (A:ℚ)*E*(1/(m:ℚ)) := by
    apply scaled_radius hm
    exact_mod_cast cn
  have hp : (p:ℚ) ≤ (B:ℚ)*E := by
    dsimp [E]; rw [← mul_div_assoc,le_div_iff₀ (pow_pos hm' k)]
    exact_mod_cast cp
  have hj' : (j:ℚ) ≤ w+1 := (Nat.ceil_lt_add_one hw).le
  have h1' : 0 ≤ 1/(m:ℚ) := by positivity
  have hmix : d/g*(p:ℚ) ≤ d/g*((B:ℚ)*E) := mul_le_mul_of_nonneg_left hp hD
  push_cast
  change (n:ℚ)+(j:ℚ) ≤ C*(E*(1/(m:ℚ)+d))
  calc _ ≤ 2*(n:ℚ)+w := by linarith
       _ ≤ 2*((A:ℚ)*E*(1/(m:ℚ))) + (d/g*((B:ℚ)*E)) := by dsimp [w]; linarith
       _ = (2*(A:ℚ))*(E*(1/(m:ℚ))) + ((B:ℚ)/g)*(E*d) := by ring
       _ ≤ C*(E*(1/(m:ℚ))) + C*(E*d) := add_le_add
         (mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hE h1'))
         (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hE hd))
       _ = _ := by ring

set_option maxHeartbeats 1000000 in
private lemma uniform_lower {q k : Nat} (hq : 5 ≤ q) :
    let ρ := 1-4/(q:ℚ)
    ∃ C : ℚ, ∀ (m : ℕ) (β : ℚ), 0 < m → ρ^(k+1) ≤ β → ∀ M : Nat,
      works0 m q β M → transitionScale q k m (β-ρ^(k+1)) ≤ C*(M:ℚ) := by
  intro ρ
  have ⟨hρ,h1⟩ := falloff_range hq
  let a := ρ^(k+1)
  let v := ρ^(2*k+2)
  let δ := v*(1-ρ)
  let K := pairConst q k δ
  have ha : 0 < a := pow_pos hρ _
  have hav : v=a^2 := by dsimp [v,a]; rw [← pow_mul]; congr 1; omega
  have hδ : 0 < δ := mul_pos (pow_pos hρ _) (sub_pos.mpr h1)
  have hK : 0 ≤ K := by
    have hpos := decay_pos hδ (2*k+1)
    dsimp only [K,pairConst]; positivity
  have hlt : ρ^((k+1)+1) < a := by
    rw [pow_succ]; exact mul_lt_of_lt_one_right ha h1
  let F := (decay (a^2-ρ^(2*(k+1)+2)) (2*(k+1)+1)).den*q^(5*(k+1)+2)
  have floor := (lower_bound_works0 (r:=k+1) (bias:=a) hq hlt (le_refl _)).2
  refine ⟨(F:ℚ)+K/a, ?_⟩
  intro m β hm hlo M wks
  let N := q^m
  let E := (N:ℚ)/(m:ℚ)^k
  let d := β-a
  have hm' : (0:ℚ) < m := Nat.cast_pos.mpr hm
  have hn : (0:ℚ) ≤ N := Nat.cast_nonneg _
  obtain ⟨send, read, hw⟩ := wks
  have wa : works0 m q a M := ⟨send,read, (mul_le_mul_of_nonneg_right (add_le_add_right hlo 1) (sq_nonneg _)).trans hw⟩
  have hf : N ≤ F*M*m^(k+1) := floor m hm M wa
  have hf' : (N:ℚ) ≤ (F:ℚ)*(M:ℚ)*(m:ℚ)^(k+1) := by exact_mod_cast hf
  have hfloor : E*(1/(m:ℚ)) ≤ (F:ℚ)*(M:ℚ) := by
    calc E*(1/(m:ℚ)) = (N:ℚ)/(m:ℚ)^(k+1) := by dsimp [E]; rw [pow_succ,div_mul_eq_div_div]; ring
         _ ≤ _ := (div_le_iff₀ (pow_pos hm' _)).mpr hf'
  have hcs := square_classes (v:=v) (err:=K*(m:ℚ)^k) hq (ha.trans_le hlo) send read hw
    (mul_nonneg hK (pow_nonneg hm'.le _)) (potential_bound (k:=k) (by omega : 1 ≤ q) hm hρ h1)
  change β^2*(N:ℚ) ≤ (N:ℚ)*v+(M:ℚ)*(K*(m:ℚ)^k) at hcs
  rw [hav] at hcs
  have hd : 0 ≤ d := sub_nonneg.mpr hlo
  have herr : a*(N:ℚ)*d ≤ (M:ℚ)*(K*(m:ℚ)^k) := by
    have hn' := mul_nonneg (mul_nonneg hd (ha.le.trans hlo)) hn
    dsimp [d] at *; nlinarith only [hcs,hn']
  have hexc : E*d ≤ (K/a)*(M:ℚ) := by
    dsimp [E]; rw [div_mul_eq_mul_div,div_le_iff₀ (pow_pos hm' _)]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,le_div_iff₀ ha]
    linarith
  change E*(1/(m:ℚ)+d) ≤ ((F:ℚ)+K/a)*(M:ℚ)
  linarith

end PEqualNP.Outside.L_lib_1013_aux
theorem PEqualNP.Outside.L_lib_1013 : (∀ (q r : Nat), 5 ≤ q → 2 ≤ r →
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  ∃ C : Nat, 0 < C ∧ ∀ (m : Nat) (β : ℚ), 0 < m → ρ^r ≤ β → β ≤ ρ^(r-1) →
    let W := Fin m → Fin q
    let N := q^m
    let scale := (N : ℚ) / (m : ℚ)^(r-1) * (1 / (m : ℚ) + (β - ρ^r))
    ∀ left right : W → Bool,
      let truth := fun (x y : W) => xor (xor (left x) (right y))
        (((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1)
      let works := fun (M : Nat) =>
        ∃ (send : W → Fin M) (read : Fin M → W → Bool),
          let hits := ((Finset.univ : Finset (W × W)).filter
            (fun p => read (send p.1) p.2 = truth p.1 p.2)).card
          (1+β)*(N : ℚ)^2 ≤ 2*(hits : ℚ)
      (∀ M : Nat, works M → scale ≤ (C : ℚ)*(M : ℚ)) ∧
        ∃ M : Nat, works M ∧ (M : ℚ) ≤ (C : ℚ)*scale) := by
  intro q r hq hr ρ
  cases r with
  | zero => omega
  | succ k =>
    obtain ⟨L,hL⟩ := PEqualNP.Outside.L_lib_1013_aux.uniform_lower (k:=k) hq
    obtain ⟨U,hU⟩ := PEqualNP.Outside.L_lib_1013_aux.uniform_upper (k:=k) hq
    obtain ⟨c,hc⟩ := exists_nat_ge (max (2*L) (2*U))
    let C := c+1
    have hc' : (c:ℚ) ≤ (C:ℚ) := by exact_mod_cast Nat.le_succ c
    have hcl : 2*L ≤ (C:ℚ) := (le_max_left _ _).trans (hc.trans hc')
    have hcu : 2*U ≤ (C:ℚ) := (le_max_right _ _).trans (hc.trans hc')
    refine ⟨C,Nat.succ_pos _,?_⟩
    intro m β hm hlo hhi W N scale left right truth works
    have hs : 0 ≤ scale := by
      change 0 ≤ ((q^m:Nat):ℚ)/(m:ℚ)^k*(1/(m:ℚ)+(β-ρ^(k+1)))
      have hd : 0 ≤ β-ρ^(k+1) := sub_nonneg.mpr hlo
      positivity
    constructor
    · intro M hw
      have hw' := PEqualNP.Outside.L_lib_1013_aux.works_to_works0 hw
      have hl := hL m β hm hlo (2*M) hw'
      change scale ≤ L*((2*M:Nat):ℚ) at hl
      push_cast at hl
      calc scale ≤ (2*L)*(M:ℚ) := by linarith
           _ ≤ _ := mul_le_mul_of_nonneg_right hcl (Nat.cast_nonneg _)
    · obtain ⟨M,hw,hb⟩ := hU m β hm hlo hhi
      refine ⟨2*M,PEqualNP.Outside.L_lib_1013_aux.works0_to_works hw,?_⟩
      change (M:ℚ) ≤ U*scale at hb
      push_cast
      calc 2*(M:ℚ) ≤ (2*U)*scale := by linarith
           _ ≤ _ := mul_le_mul_of_nonneg_right hcu hs
