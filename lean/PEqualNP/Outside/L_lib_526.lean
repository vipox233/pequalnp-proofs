import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_513

namespace PEqualNP.Outside.L_lib_526_aux

def Rows := Nat → Nat → Bool

def massF (w : Nat) (rows : Rows) (h seed tail : Nat) : Nat :=
  ((List.range (2 ^ (w + h))).filter (fun bits =>
    bits % (2 ^ w) == seed && (bits >>> h) % (2 ^ w) == tail &&
    (List.range h).all (fun i => rows i ((bits >>> i) % (2 * 2 ^ w))))).length

def countF (w t m : Nat) (left right : Rows) : Nat :=
  let L := w + t
  let n := L + w
  ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
    let pat := (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
      acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0
    if site < L then left site pat else right (site - L) pat))).length % m

def goodF (w t : Nat) (tables : Rows) : Prop :=
  let D := 2 ^ w
  ∃ a b : Fin D → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
    ∀ s z : Fin D, massF w tables (w + t) s.val z.val = a s * b z

def packBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => packBits f k + (f k).toNat * 2 ^ k

theorem packBits_lt (f : Nat → Bool) : ∀ k, packBits f k < 2 ^ k := by
  intro k
  induction k with
  | zero => simp [packBits]
  | succ k ih =>
    simp only [packBits, Nat.pow_succ, Nat.mul_two]
    cases f k <;> simp <;> omega

theorem or_shiftLeft_eq_add (a b k : Nat) (ha : a < 2 ^ k) :
    a ||| (b <<< k) = a + b * 2 ^ k := by
  rw [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
  by_cases hi : i < k
  · have hge : ¬ (k ≤ i) := by omega
    simp only [hge, decide_false, Bool.false_and, Bool.or_false]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hsplit : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hmul : b * 2 ^ k = (b * 2 ^ (k - i)) * 2 ^ i := by rw [hsplit]; ring
    rw [hmul, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
    have h2 : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
      have : k - i = (k - i - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hm2 : b * 2 ^ (k - i) = 2 * (b * 2 ^ (k - i - 1)) := by rw [h2]; ring
    rw [hm2, Nat.add_mul_mod_self_left]
  · have hle : k ≤ i := by omega
    have ha0 : a.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hle))
    simp only [ha0, Bool.false_or, hle, decide_true, Bool.true_and]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hsplit : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hsplit, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2)),
      Nat.div_eq_of_lt ha, Nat.zero_add]

theorem foldl_packBits (f : Nat → Bool) : ∀ k,
    (List.range k).foldl (fun acc bit => acc ||| ((f bit).toNat <<< bit)) 0 = packBits f k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    exact or_shiftLeft_eq_add (packBits f k) (f k).toNat k (packBits_lt f k)

theorem packBits_testBit (f : Nat → Bool) : ∀ k i,
    (packBits f k).testBit i = if i < k then f i else false := by
  intro k
  induction k with
  | zero => intro i; simp [packBits]
  | succ k ih =>
    intro i
    simp only [packBits]
    rw [← or_shiftLeft_eq_add (packBits f k) (f k).toNat k (packBits_lt f k),
      Nat.testBit_or, ih i, Nat.shiftLeft_eq, Nat.testBit_mul_two_pow]
    by_cases h1 : i < k
    · have h2 : i < k + 1 := by omega
      have h3 : ¬ (k ≤ i) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i = k
      · subst h2
        have hlt : i < i + 1 := by omega
        simp only [lt_irrefl, ↓reduceIte, Bool.false_or, le_refl, decide_true, Bool.true_and,
          Nat.sub_self, hlt]
        cases f i <;> decide
      · have h3 : ¬ (i < k + 1) := by omega
        have h4 : k ≤ i := by omega
        have h5 : 0 < i - k := by omega
        simp only [h1, h3, ↓reduceIte, Bool.false_or, h4, decide_true, Bool.true_and]
        cases f k
        · simp
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
            (Nat.pow_le_pow_right (by decide) h5))

theorem packBits_shift_mod (word site k : Nat) :
    packBits (fun bit => word.testBit (site + bit)) k = (word >>> site) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [packBits_testBit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < k <;> simp [hi]

def rightPat (w s z j : Nat) : Nat :=
  packBits (fun bit => if j + bit < w then z.testBit (j + bit) else s.testBit (j + bit - w)) (w + 1)

def rightOk (w : Nat) (right : Rows) (s z : Nat) : Bool :=
  (List.range w).all (fun j => right j (rightPat w s z j))

theorem word_pat_left (w t word site : Nat) (hsite : site < w + t) :
    (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
      acc ||| ((word.testBit ((site + bit) % (w + t + w))).toNat <<< bit)) 0 =
    (word >>> site) % (2 * 2 ^ w) := by
  rw [foldl_packBits]
  have heq : packBits (fun bit => word.testBit ((site + bit) % (w + t + w))) (w + 1) =
      packBits (fun bit => word.testBit (site + bit)) (w + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [packBits_testBit, packBits_testBit]
    by_cases hi : i < w + 1
    · simp only [hi, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp [hi]
  rw [heq, packBits_shift_mod, Nat.pow_succ, Nat.mul_comm]

theorem word_pat_right (w t word j : Nat) (hj : j < w) :
    let L := w + t
    let n := L + w
    let D := 2 ^ w
    (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
      acc ||| ((word.testBit ((L + j + bit) % n)).toNat <<< bit)) 0 =
    rightPat w (word % D) ((word >>> L) % D) j := by
  intro L n D
  rw [foldl_packBits]
  unfold rightPat
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [packBits_testBit, packBits_testBit]
  by_cases hbit : bit < w + 1
  · simp only [hbit, ↓reduceIte]
    by_cases hjb : j + bit < w
    · simp only [hjb, ↓reduceIte]
      have hmod : (L + j + bit) % n = L + (j + bit) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hmod, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      simp [hjb]
    · simp only [hjb, ↓reduceIte]
      have hmod : (L + j + bit) % n = j + bit - w := by
        have h1 : L + j + bit = (j + bit - w) + n := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, Nat.testBit_mod_two_pow]
      have hlt : j + bit - w < w := by omega
      simp [hlt]
  · simp [hbit]

theorem list_range_filter_length_eq_card (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length = ((Finset.range N).filter (fun x => p x = true)).card := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil,
      Finset.range_add_one, Finset.filter_insert]
    cases hp : p N
    · simp [ih]
    · simp only [List.length_cons, List.length_nil, Nat.zero_add, ↓reduceIte]
      rw [Finset.card_insert_of_notMem, ih]
      simp

theorem list_all_range_iff (k : Nat) (p : Nat → Bool) :
    (List.range k).all p = true ↔ ∀ i < k, p i = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi; exact h i (List.mem_range.mpr hi)
  · intro h i hi; exact h i (List.mem_range.mp hi)

theorem count_eq_sum_mass (w t m : Nat) (left right : Rows) :
    let D := 2 ^ w
    countF w t m left right =
      (∑ s : Fin D, ∑ z : Fin D,
        if rightOk w right s.val z.val then massF w left (w + t) s.val z.val else 0) % m := by
  intro D
  unfold countF
  dsimp only
  congr 1
  set L := w + t
  set n := L + w
  have hn : w + L = n := by omega
  rw [list_range_filter_length_eq_card]
  let P : Nat → Bool := fun word => (List.range n).all (fun site =>
    let pat := (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
      acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0
    if site < L then left site pat else right (site - L) pat)
  let fib : Fin D × Fin D → Finset Nat := fun p =>
    ((Finset.range (2 ^ n)).filter (fun word => P word = true)).filter
      (fun word => word % D = p.1.val ∧ (word >>> L) % D = p.2.val)
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin D × Fin D)) fib := by
    intro p1 _ p2 _ hne
    change Disjoint (fib p1) (fib p2)
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [fib, Finset.mem_filter] at hx1 hx2
    apply hne
    exact Prod.ext (Fin.ext (hx1.2.1.symm.trans hx2.2.1)) (Fin.ext (hx1.2.2.symm.trans hx2.2.2))
  have hbi : (Finset.univ : Finset (Fin D × Fin D)).biUnion fib =
      (Finset.range (2 ^ n)).filter (fun word => P word = true) := by
    ext word
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fib, Finset.mem_filter]
    constructor
    · rintro ⟨_, h, _, _⟩; exact h
    · intro h
      have hDpos : 0 < D := Nat.pow_pos (by decide : 0 < 2)
      exact ⟨(⟨word % D, Nat.mod_lt _ hDpos⟩, ⟨(word >>> L) % D, Nat.mod_lt _ hDpos⟩), h, rfl, rfl⟩
  rw [← hbi, Finset.card_biUnion hdisj, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun z _ => ?_
  have hfib_eq : (fib (s, z)).card =
      if rightOk w right s.val z.val then massF w left L s.val z.val else 0 := by
    have hP_iff : ∀ word, word % D = s.val → (word >>> L) % D = z.val →
        (P word = true ↔
          ((List.range L).all (fun i => left i ((word >>> i) % (2 * D))) = true ∧
           rightOk w right s.val z.val = true)) := by
      intro word hs hz
      simp only [P, rightOk, list_all_range_iff]
      constructor
      · intro hall
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have h := hall i (by omega)
          simp only [hi, ↓reduceIte] at h
          rwa [word_pat_left w t word i hi] at h
        · have h := hall (L + j) (by omega)
          have hnot : ¬ (L + j < L) := by omega
          have hsub : L + j - L = j := by omega
          simp only [hnot, ↓reduceIte, hsub] at h
          rw [word_pat_right w t word j hj, hs, hz] at h
          exact h
      · rintro ⟨hl, hr⟩ site hsite
        by_cases hsL : site < L
        · simp only [hsL, ↓reduceIte]
          rw [word_pat_left w t word site hsL]
          exact hl site hsL
        · simp only [hsL, ↓reduceIte]
          have hj : site - L < w := by omega
          have heq : site = L + (site - L) := by omega
          conv_lhs => rw [heq]
          rw [word_pat_right w t word (site - L) hj, hs, hz, Nat.add_sub_cancel_left]
          exact hr (site - L) hj
    cases hr : rightOk w right s.val z.val
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro word hmem
      simp only [fib, Finset.mem_filter] at hmem
      have h2 := (hP_iff word hmem.2.1 hmem.2.2).mp hmem.1.2
      rw [hr] at h2
      exact Bool.noConfusion h2.2
    · simp only [↓reduceIte]
      unfold massF
      rw [hn, list_range_filter_length_eq_card]
      congr 1
      ext word
      simp only [fib, Finset.mem_filter, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨⟨hmem, hP⟩, hs, hz⟩
        exact ⟨hmem, ⟨hs, hz⟩, ((hP_iff word hs hz).mp hP).1⟩
      · rintro ⟨hmem, ⟨hs, hz⟩, hl⟩
        exact ⟨⟨hmem, (hP_iff word hs hz).mpr ⟨hl, hr⟩⟩, hs, hz⟩
  exact hfib_eq

def rightFor (w : Nat) (T : Nat → Bool) : Rows :=
  fun j pat =>
    let D := 2 ^ w
    if j = 0 then T (pat % D) && ((pat / D) % 2 == 0)
    else ((pat / D) % 2 == 0)

theorem rightPat_mod_zero (w s z : Nat) (hz : z < 2 ^ w) :
    rightPat w s z 0 % 2 ^ w = z := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, rightPat, packBits_testBit]
  by_cases hi : i < w
  · have hi1 : i < w + 1 := by omega
    simp [hi, hi1]
  · simp [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))]

theorem rightPat_top_bit (w s z j : Nat) (hj : j < w) :
    (rightPat w s z j / 2 ^ w) % 2 = (s.testBit j).toNat := by
  have h1 : (rightPat w s z j).testBit w = s.testBit j := by
    rw [rightPat, packBits_testBit]
    have hw : w < w + 1 := by omega
    have hge : ¬ (j + w < w) := by omega
    have hsub : j + w - w = j := by omega
    simp [hw, hge, hsub]
  rw [Nat.testBit_eq_decide_div_mod_eq] at h1
  have hm : (rightPat w s z j / 2 ^ w) % 2 = 0 ∨ (rightPat w s z j / 2 ^ w) % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [hm] at h1 ⊢; simp at h1; rw [h1]; rfl
  · rw [hm] at h1 ⊢; simp at h1; rw [h1]; rfl

theorem rightOk_rightFor (w : Nat) (hw : 0 < w) (T : Nat → Bool) (s z : Nat)
    (hs : s < 2 ^ w) (hz : z < 2 ^ w) :
    rightOk w (rightFor w T) s z = (decide (s = 0) && T z) := by
  cases h : decide (s = 0) && T z
  · cases h2 : rightOk w (rightFor w T) s z
    · rfl
    · exfalso
      rw [rightOk, list_all_range_iff] at h2
      have h0 := h2 0 hw
      simp only [rightFor, ↓reduceIte, rightPat_mod_zero w s z hz, rightPat_top_bit w s z 0 hw,
        Bool.and_eq_true, beq_iff_eq] at h0
      have hs0 : s = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.zero_testBit]
        by_cases hj : j < w
        · have hj_ok := h2 j hj
          by_cases hj0 : j = 0
          · subst hj0
            cases hb : s.testBit 0
            · rfl
            · rw [hb] at h0; exact absurd h0.2 (by decide)
          · simp only [rightFor, hj0, ↓reduceIte, rightPat_top_bit w s z j hj, beq_iff_eq] at hj_ok
            cases hb : s.testBit j
            · rfl
            · rw [hb] at hj_ok; exact absurd hj_ok (by decide)
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hs0, h0.1] at h
      simp at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, hTz⟩
    rw [rightOk, list_all_range_iff]
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp [rightFor, rightPat_mod_zero w 0 z hz, rightPat_top_bit w 0 z 0 hw, hTz]
    · simp [rightFor, hj0, rightPat_top_bit w 0 z j hj]

theorem count_rightFor (w t m : Nat) (hw : 0 < w) (left : Rows) (T : Nat → Bool) :
    countF w t m left (rightFor w T) =
      (∑ z : Fin (2 ^ w), if T z.val then massF w left (w + t) 0 z.val else 0) % m := by
  rw [count_eq_sum_mass]
  congr 1
  have hDpos : 0 < 2 ^ w := Nat.pow_pos (by decide : 0 < 2)
  rw [Finset.sum_eq_single (⟨0, hDpos⟩ : Fin (2 ^ w))]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [rightOk_rightFor w hw T 0 z.val hDpos z.isLt]
    simp
  · intro s _ hne
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [rightOk_rightFor w hw T s.val z.val s.isLt z.isLt]
    have hs0 : s.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [hs0]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem upper_le_lower_pow8 (w t m : Nat) (hw : 0 < w) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    let lower := 2 ^ ((D / 2) * Nat.log2 C)
    let upper := C ^ (2 * D)
    upper ≤ lower ^ 8 := by
  intro D C lower upper
  have h2H : 2 * (D / 2) = D := by
    cases w with
    | zero => omega
    | succ w' =>
      dsimp only [D]
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), Nat.mul_comm]
  by_cases hC1 : C ≤ 1
  · by_cases hC0 : C = 0
    · have hDpos : 0 < 2 * D := by
        have : 0 < D := Nat.pow_pos (by decide : 0 < 2); omega
      dsimp only [upper]; rw [hC0, Nat.zero_pow hDpos]; omega
    · have hCe : C = 1 := by omega
      dsimp only [upper, lower]
      rw [hCe]; simp
  · have hC2 : 2 ≤ C := by omega
    set r := Nat.log2 C
    have hr_eq : r = Nat.log 2 C := Nat.log2_eq_log_two
    have hr1 : 1 ≤ r := by
      rw [hr_eq]
      have h1 : Nat.log 2 2 ≤ Nat.log 2 C := Nat.log_mono_right hC2
      have h2 : Nat.log 2 2 = 1 := by decide
      omega
    have hClt : C < 2 ^ (r + 1) := by
      rw [hr_eq]
      exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) C
    have hCle : C ≤ 2 ^ (2 * r) := by
      have h1 : C ≤ 2 ^ (r + 1) := le_of_lt hClt
      have h2 : 2 ^ (r + 1) ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact h1.trans h2
    dsimp only [upper, lower]
    calc C ^ (2 * D)
        ≤ (2 ^ (2 * r)) ^ (2 * D) := Nat.pow_le_pow_left hCle (2 * D)
      _ = 2 ^ ((2 * r) * (2 * D)) := (Nat.pow_mul 2 (2 * r) (2 * D)).symm
      _ = 2 ^ (((D / 2) * r) * 8) := by congr 1; nlinarith
      _ = (2 ^ ((D / 2) * r)) ^ 8 := Nat.pow_mul 2 ((D / 2) * r) 8

theorem mass_le_two_pow_t (w t : Nat) (rows : Rows) (s z : Nat) :
    massF w rows (w + t) s z ≤ 2 ^ t := by
  unfold massF
  rw [list_range_filter_length_eq_card]
  let S := (Finset.range (2 ^ (w + (w + t)))).filter (fun bits =>
    (bits % 2 ^ w == s && (bits >>> (w + t)) % 2 ^ w == z &&
      (List.range (w + t)).all (fun i => rows i ((bits >>> i) % (2 * 2 ^ w)))) = true)
  have hcard : S.card ≤ (Finset.range (2 ^ t)).card := by
    refine Finset.card_le_card_of_injOn (fun bits => (bits / 2 ^ w) % 2 ^ t) ?_ ?_
    · intro bits _
      exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)))
    · intro a ha b hb heq
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true,
        beq_iff_eq] at ha hb
      have htop : ∀ x, x < 2 ^ (w + (w + t)) → (x >>> (w + t)) % 2 ^ w = x / 2 ^ (w + t) := fun x hx => by
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.mod_eq_of_lt
        rw [Nat.pow_add, Nat.mul_comm] at hx
        exact Nat.div_lt_of_lt_mul hx
      have ha_top : a / 2 ^ (w + t) = z := by rw [← htop a ha.1]; exact ha.2.1.2
      have hb_top : b / 2 ^ (w + t) = z := by rw [← htop b hb.1]; exact hb.2.1.2
      have ha_mid : a / 2 ^ w = z * 2 ^ t + (a / 2 ^ w) % 2 ^ t := by
        have h1 := Nat.div_add_mod (a / 2 ^ w) (2 ^ t)
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ha_top, Nat.mul_comm] at h1
        omega
      have hb_mid : b / 2 ^ w = z * 2 ^ t + (b / 2 ^ w) % 2 ^ t := by
        have h1 := Nat.div_add_mod (b / 2 ^ w) (2 ^ t)
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hb_top, Nat.mul_comm] at h1
        omega
      have hdiv_eq : a / 2 ^ w = b / 2 ^ w := by dsimp only at heq; rw [ha_mid, hb_mid, heq]
      have ha_full := Nat.div_add_mod a (2 ^ w)
      have hb_full := Nat.div_add_mod b (2 ^ w)
      rw [ha.2.1.1] at ha_full
      rw [hb.2.1.1, ← hdiv_eq] at hb_full
      omega
  rwa [Finset.card_range] at hcard

theorem upper_protocol (w t m : Nat) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    let upper := C ^ (2 * D)
    ∃ (encode : Rows → Fin upper) (read : Fin upper → Rows → Nat),
      ∀ p q : Rows, goodF w t p → read (encode p) q = countF w t m p q := by
  classical
  intro D C upper
  have hCpos : 0 < C := by
    dsimp only [C]
    split_ifs with hm
    · exact Nat.pow_pos (by decide : 0 < 2)
    · exact Nat.lt_min.mpr ⟨Nat.pow_pos (by decide : 0 < 2), Nat.pos_of_ne_zero hm⟩
  have hup_pos : 0 < upper := Nat.pow_pos hCpos
  have hcard : Fintype.card ((Fin D → Fin C) × (Fin D → Fin C)) = upper := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, upper]
    rw [← Nat.pow_add, Nat.two_mul]
  let eqv : ((Fin D → Fin C) × (Fin D → Fin C)) ≃ Fin upper := Fintype.equivFinOfCardEq hcard
  let encode : Rows → Fin upper := fun p =>
    if hp : goodF w t p then
      let a := Classical.choose hp
      let b := Classical.choose (Classical.choose_spec hp)
      if hlt : m ≠ 0 ∧ m < 2 ^ t then
        eqv (fun i => ⟨a i % m, by
              have hCe : C = m := by dsimp only [C]; rw [if_neg hlt.1]; exact Nat.min_eq_right (le_of_lt hlt.2)
              rw [hCe]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero hlt.1)⟩,
             fun j => ⟨b j % m, by
              have hCe : C = m := by dsimp only [C]; rw [if_neg hlt.1]; exact Nat.min_eq_right (le_of_lt hlt.2)
              rw [hCe]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero hlt.1)⟩)
      else
        have hspec := Classical.choose_spec (Classical.choose_spec hp)
        have hCe : C = 2 ^ t := by
          dsimp only [C]
          by_cases hm : m = 0
          · rw [if_pos hm]
          · rw [if_neg hm]; exact Nat.min_eq_left (by omega)
        have hDpos : 0 < D := Nat.pow_pos (by decide : 0 < 2)
        eqv (fun i => ⟨a i - 1, by
              rw [hCe]
              have h1 := hspec.1 i
              have h2 := hspec.2.1 ⟨0, hDpos⟩
              have h3 := hspec.2.2 i ⟨0, hDpos⟩
              have hle : a i * b ⟨0, hDpos⟩ ≤ 2 ^ t := h3 ▸ mass_le_two_pow_t w t p i.val 0
              have ha_le : a i ≤ a i * b ⟨0, hDpos⟩ := Nat.le_mul_of_pos_right _ h2
              omega⟩,
             fun j => ⟨b j - 1, by
              rw [hCe]
              have h1 := hspec.1 ⟨0, hDpos⟩
              have h2 := hspec.2.1 j
              have h3 := hspec.2.2 ⟨0, hDpos⟩ j
              have hle : a ⟨0, hDpos⟩ * b j ≤ 2 ^ t := h3 ▸ mass_le_two_pow_t w t p 0 j.val
              have hb_le : b j ≤ a ⟨0, hDpos⟩ * b j := Nat.le_mul_of_pos_left _ h1
              omega⟩)
    else ⟨0, hup_pos⟩
  let read : Fin upper → Rows → Nat := fun code q =>
    let pair := eqv.symm code
    if m ≠ 0 ∧ m < 2 ^ t then
      (∑ s : Fin D, ∑ z : Fin D,
        if rightOk w q s.val z.val then (pair.1 s).val * (pair.2 z).val else 0) % m
    else
      (∑ s : Fin D, ∑ z : Fin D,
        if rightOk w q s.val z.val then ((pair.1 s).val + 1) * ((pair.2 z).val + 1) else 0) % m
  refine ⟨encode, read, fun p q hp => ?_⟩
  rw [count_eq_sum_mass]
  dsimp only [encode, read]
  rw [dif_pos hp]
  set a := Classical.choose hp
  set b := Classical.choose (Classical.choose_spec hp)
  have hspec := Classical.choose_spec (Classical.choose_spec hp)
  by_cases hlt : m ≠ 0 ∧ m < 2 ^ t
  · rw [dif_pos hlt, Equiv.symm_apply_apply, if_pos hlt]
    have hsum_mod : ∀ (f g : Fin D → Fin D → Nat),
        (∀ s z, f s z % m = g s z % m) →
        (∑ s : Fin D, ∑ z : Fin D, f s z) % m = (∑ s : Fin D, ∑ z : Fin D, g s z) % m := by
      intro f g hfg
      rw [Finset.sum_nat_mod, Finset.sum_nat_mod (f := fun s => ∑ z : Fin D, g s z)]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_nat_mod, Finset.sum_nat_mod (f := g s)]
      congr 1
      exact Finset.sum_congr rfl fun z _ => hfg s z
    refine hsum_mod _ _ fun s z => ?_
    rw [hspec.2.2 s z]
    cases rightOk w q s.val z.val
    · simp
    · simp only [↓reduceIte, Nat.mul_mod, Nat.mod_mod]
  · rw [dif_neg hlt, Equiv.symm_apply_apply, if_neg hlt]
    congr 1
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun z _ => ?_
    rw [hspec.2.2 s z]
    have ha : a s - 1 + 1 = a s := Nat.sub_add_cancel (hspec.1 s)
    have hb : b z - 1 + 1 = b z := Nat.sub_add_cancel (hspec.2.1 z)
    rw [ha, hb]

def delBitW (w x : Nat) : Nat :=
  x % 2 ^ w + (x / 2 ^ (w + 1)) * 2 ^ w

def insBitW (w : Nat) (b : Bool) (y : Nat) : Nat :=
  y % 2 ^ w + b.toNat * 2 ^ w + (y / 2 ^ w) * 2 ^ (w + 1)

theorem delBitW_testBit (w x i : Nat) :
    (delBitW w x).testBit i = if i < w then x.testBit i else x.testBit (i + 1) := by
  unfold delBitW
  rw [← or_shiftLeft_eq_add _ _ w (Nat.mod_lt x (Nat.pow_pos (by decide : 0 < 2))),
    Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.shiftLeft_eq, Nat.testBit_mul_two_pow]
  by_cases hi : i < w
  · have hge : ¬ (w ≤ i) := by omega
    simp [hi, hge]
  · have hle : w ≤ i := by omega
    simp only [hi, decide_false, Bool.false_and, Bool.false_or, hle, decide_true, Bool.true_and,
      ↓reduceIte]
    rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    congr 1; omega

theorem insBitW_testBit (w : Nat) (b : Bool) (y i : Nat) :
    (insBitW w b y).testBit i =
      if i < w then y.testBit i else if i = w then b else y.testBit (i - 1) := by
  unfold insBitW
  have hlo : y % 2 ^ w + b.toNat * 2 ^ w < 2 ^ (w + 1) := by
    have h1 : y % 2 ^ w < 2 ^ w := Nat.mod_lt y (Nat.pow_pos (by decide : 0 < 2))
    rw [Nat.pow_succ, Nat.mul_two]
    cases b <;> simp <;> omega
  rw [← or_shiftLeft_eq_add (y % 2 ^ w + b.toNat * 2 ^ w) (y / 2 ^ w) (w + 1) hlo,
    ← or_shiftLeft_eq_add (y % 2 ^ w) b.toNat w (Nat.mod_lt y (Nat.pow_pos (by decide : 0 < 2)))]
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  by_cases h1 : i < w
  · have h2 : ¬ (w ≤ i) := by omega
    have h3 : ¬ (w + 1 ≤ i) := by omega
    simp [h1, h2, h3]
  · by_cases h2 : i = w
    · subst h2
      have h3 : ¬ (i + 1 ≤ i) := by omega
      simp only [lt_irrefl, decide_false, Bool.false_and, le_refl, decide_true, Bool.true_and,
        Nat.sub_self, Bool.false_or, h3, Bool.or_false, ↓reduceIte]
      cases b <;> decide
    · have h3 : w ≤ i := by omega
      have h4 : w + 1 ≤ i := by omega
      have h5 : 0 < i - w := by omega
      have hb0 : b.toNat.testBit (i - w) = false := by
        cases b
        · simp
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
            (Nat.pow_le_pow_right (by decide) h5))
      simp only [h1, h2, decide_false, Bool.false_and, h3, decide_true, Bool.true_and, hb0,
        Bool.false_or, h4, ↓reduceIte]
      rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
      congr 1; omega

theorem delBitW_insBitW (w : Nat) (b : Bool) (y : Nat) :
    delBitW w (insBitW w b y) = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [delBitW_testBit]
  by_cases hi : i < w
  · simp only [hi, ↓reduceIte, insBitW_testBit]
  · have h1 : ¬ (i + 1 < w) := by omega
    have h2 : i + 1 ≠ w := by omega
    simp only [hi, ↓reduceIte, insBitW_testBit, h1, h2, Nat.add_sub_cancel]

theorem insBitW_delBitW (w x : Nat) :
    insBitW w (x.testBit w) (delBitW w x) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [insBitW_testBit]
  by_cases h1 : i < w
  · simp only [h1, ↓reduceIte, delBitW_testBit]
  · by_cases h2 : i = w
    · subst h2; simp
    · have h3 : ¬ (i - 1 < w) := by omega
      have h4 : i - 1 + 1 = i := by omega
      simp only [h1, h2, ↓reduceIte, delBitW_testBit, h3, h4]

theorem delBitW_lt (w h x : Nat) (hx : x < 2 ^ (w + (h + 1))) :
    delBitW w x < 2 ^ (w + h) := by
  unfold delBitW
  have h1 : x % 2 ^ w < 2 ^ w := Nat.mod_lt x (Nat.pow_pos (by decide : 0 < 2))
  have h2 : x / 2 ^ (w + 1) < 2 ^ h := by
    have : 2 ^ (w + (h + 1)) = 2 ^ (w + 1) * 2 ^ h := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [this] at hx
    exact Nat.div_lt_of_lt_mul hx
  have h3 : (x / 2 ^ (w + 1) + 1) * 2 ^ w ≤ 2 ^ h * 2 ^ w := Nat.mul_le_mul_right _ h2
  have h4 : 2 ^ (w + h) = 2 ^ h * 2 ^ w := by rw [Nat.pow_add, Nat.mul_comm]
  rw [Nat.succ_mul] at h3
  omega

theorem insBitW_lt (w h : Nat) (b : Bool) (y : Nat) (hy : y < 2 ^ (w + h)) :
    insBitW w b y < 2 ^ (w + (h + 1)) := by
  unfold insBitW
  have hlo : y % 2 ^ w + b.toNat * 2 ^ w < 2 ^ (w + 1) := by
    have h1 : y % 2 ^ w < 2 ^ w := Nat.mod_lt y (Nat.pow_pos (by decide : 0 < 2))
    rw [Nat.pow_succ, Nat.mul_two]
    cases b <;> simp <;> omega
  have h2 : y / 2 ^ w < 2 ^ h := by
    rw [Nat.pow_add] at hy
    exact Nat.div_lt_of_lt_mul hy
  have h3 : (y / 2 ^ w + 1) * 2 ^ (w + 1) ≤ 2 ^ h * 2 ^ (w + 1) := Nat.mul_le_mul_right _ h2
  have h4 : 2 ^ (w + (h + 1)) = 2 ^ h * 2 ^ (w + 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.succ_mul] at h3
  omega

theorem delBitW_mod (w x : Nat) : delBitW w x % 2 ^ w = x % 2 ^ w := by
  unfold delBitW
  rw [Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem delBitW_shift (w x i : Nat) (hi : w ≤ i) :
    delBitW w x >>> i = x >>> (i + 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, delBitW_testBit]
  have hnot : ¬ (i + j < w) := by omega
  simp only [hnot, ↓reduceIte]
  congr 1; omega

def insCopy (w : Nat) (rows : Rows) : Rows :=
  fun site pat =>
    if site < w then true
    else if site = w then (pat % 2 == (pat / 2 ^ w) % 2)
    else rows (site - 1) pat

theorem copy_row_iff (w x : Nat) :
    (((x >>> w) % (2 * 2 ^ w)) % 2 == (((x >>> w) % (2 * 2 ^ w)) / 2 ^ w) % 2) = true ↔
      x.testBit w = x.testBit (2 * w) := by
  have h0 : ((x >>> w) % (2 * 2 ^ w)) % 2 = (x.testBit w).toNat := by
    have ht : x.testBit w = (((x >>> w) % (2 * 2 ^ w)).testBit 0) := by
      have h2D : 2 * 2 ^ w = 2 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2D, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      simp
    conv_rhs at ht => rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
    have hm : ((x >>> w) % (2 * 2 ^ w)) % 2 = 0 ∨ ((x >>> w) % (2 * 2 ^ w)) % 2 = 1 := by omega
    rcases hm with hm | hm
    · rw [hm] at ht ⊢; simp at ht; rw [ht]; rfl
    · rw [hm] at ht ⊢; simp at ht; rw [ht]; rfl
  have h1 : (((x >>> w) % (2 * 2 ^ w)) / 2 ^ w) % 2 = (x.testBit (2 * w)).toNat := by
    have ht : x.testBit (2 * w) = (((x >>> w) % (2 * 2 ^ w)).testBit w) := by
      have h2D : 2 * 2 ^ w = 2 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2D, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      have hlt : w < w + 1 := by omega
      have h2w : w + w = 2 * w := by omega
      simp [hlt, h2w]
    conv_rhs at ht => rw [Nat.testBit_eq_decide_div_mod_eq]
    have hm : (((x >>> w) % (2 * 2 ^ w)) / 2 ^ w) % 2 = 0 ∨
        (((x >>> w) % (2 * 2 ^ w)) / 2 ^ w) % 2 = 1 := by omega
    rcases hm with hm | hm
    · rw [hm] at ht ⊢; simp at ht; rw [ht]; rfl
    · rw [hm] at ht ⊢; simp at ht; rw [ht]; rfl
  rw [h0, h1, beq_iff_eq]
  cases x.testBit w <;> cases x.testBit (2 * w) <;> simp

theorem mass_insCopy (w h : Nat) (hw : 0 < w) (hh : w ≤ h) (rows : Rows)
    (hfree : ∀ i < w, ∀ pat, rows i pat = true) (s z : Nat) :
    massF w (insCopy w rows) (h + 1) s z = massF w rows h s z := by
  unfold massF
  rw [list_range_filter_length_eq_card, list_range_filter_length_eq_card]
  refine Finset.card_bij (fun x _ => delBitW w x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, beq_iff_eq,
      list_all_range_iff] at hx ⊢
    rcases hx with ⟨hlt, ⟨hs, hz⟩, hall⟩
    refine ⟨delBitW_lt w h x hlt, ⟨by rw [delBitW_mod]; exact hs,
      by rw [delBitW_shift w x h hh]; exact hz⟩, fun i hi => ?_⟩
    by_cases hiw : i < w
    · exact hfree i hiw _
    · have h1 := hall (i + 1) (by omega)
      have hn1 : ¬ (i + 1 < w) := by omega
      have hn2 : i + 1 ≠ w := by omega
      simp only [insCopy, hn1, hn2, ↓reduceIte, Nat.add_sub_cancel] at h1
      rw [delBitW_shift w x i (by omega)]
      exact h1
  · intro x1 hx1 x2 hx2 heq
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, beq_iff_eq,
      list_all_range_iff] at hx1 hx2
    have h1 := hx1.2.2 w (by omega)
    have h2 := hx2.2.2 w (by omega)
    simp only [insCopy, lt_irrefl, ↓reduceIte] at h1 h2
    have hb1 : x1.testBit w = x1.testBit (2 * w) := (copy_row_iff w x1).mp h1
    have hb2 : x2.testBit w = x2.testBit (2 * w) := (copy_row_iff w x2).mp h2
    have hdel_bit : ∀ x, x.testBit (2 * w) = (delBitW w x).testBit (2 * w - 1) := fun x => by
      rw [delBitW_testBit]
      have hn : ¬ (2 * w - 1 < w) := by omega
      have ha : 2 * w - 1 + 1 = 2 * w := by omega
      simp [hn, ha]
    have hbit_eq : x1.testBit w = x2.testBit w := by
      rw [hb1, hb2, hdel_bit x1, hdel_bit x2, heq]
    rw [← insBitW_delBitW w x1, ← insBitW_delBitW w x2, heq, hbit_eq]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, beq_iff_eq,
      list_all_range_iff] at hy
    rcases hy with ⟨hlt, ⟨hs, hz⟩, hall⟩
    let x := insBitW w (y.testBit (2 * w - 1)) y
    have hdel : delBitW w x = y := delBitW_insBitW w _ y
    refine ⟨x, ?_, hdel⟩
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, beq_iff_eq,
      list_all_range_iff]
    refine ⟨insBitW_lt w h _ y hlt, ⟨by rw [← delBitW_mod w x, hdel]; exact hs,
      by rw [← delBitW_shift w x h hh, hdel]; exact hz⟩, fun i hi => ?_⟩
    by_cases hi1 : i < w
    · simp [insCopy, hi1]
    · by_cases hi2 : i = w
      · subst i
        simp only [insCopy, lt_irrefl, ↓reduceIte]
        rw [copy_row_iff]
        have hx1 : x.testBit w = y.testBit (2 * w - 1) := by
          simp [x, insBitW_testBit]
        have hx2 : x.testBit (2 * w) = y.testBit (2 * w - 1) := by
          have hn1 : ¬ (2 * w < w) := by omega
          have hn2 : 2 * w ≠ w := by omega
          simp [x, insBitW_testBit, hn1, hn2]
        rw [hx1, hx2]
      · simp only [insCopy, hi1, hi2, ↓reduceIte]
        have hiw : w ≤ i - 1 := by omega
        have his : (i - 1) + 1 = i := by omega
        rw [← his, ← delBitW_shift w x (i - 1) hiw, hdel]
        exact hall (i - 1) (by omega)

theorem mass_insCopy_iter (w r : Nat) (hw : 0 < w) (rows : Rows)
    (hfree : ∀ i < w, ∀ pat, rows i pat = true) :
    ∀ p s z, massF w ((insCopy w)^[p] rows) (w + r + p) s z = massF w rows (w + r) s z := by
  intro p
  induction p with
  | zero => intro s z; rfl
  | succ p ih =>
    intro s z
    have hfree_p : ∀ q, ∀ i < w, ∀ pat, ((insCopy w)^[q] rows) i pat = true := by
      intro q
      induction q with
      | zero => exact hfree
      | succ q _ =>
        intro i hi pat
        rw [Function.iterate_succ_apply']
        simp [insCopy, hi]
    rw [Function.iterate_succ_apply', ← Nat.add_assoc,
      mass_insCopy w (w + r + p) hw (by omega) _ (hfree_p p) s z, ih s z]

def familyTable (w t r : Nat) (F : Fin r → Fin (2 ^ w / 2) → Bool) : Rows :=
  let D := 2 ^ w
  let H := D / 2
  let flags : Nat → Nat → Bool := fun i u =>
    if hi : i < r then if hu : u < H then F ⟨i, hi⟩ ⟨u, hu⟩ else false else false
  let base : Rows := fun site pattern =>
    let old := pattern % 2
    let newBit := (pattern / D) % 2
    decide (site < w) || (old == newBit) || ((old == 1) == flags (site - w) ((pattern % D) / 2))
  (insCopy w)^[t - r] base

theorem family_properties (w t r : Nat) (hw : 0 < w) (hr : r ≤ t) :
    let D := 2 ^ w
    let H := D / 2
    (∀ F : Fin r → Fin H → Bool, goodF w t (familyTable w t r F)) ∧
    (∀ F : Fin r → Fin H → Bool, ∀ z : Fin D,
      1 ≤ massF w (familyTable w t r F) (w + t) 0 z.val ∧
      massF w (familyTable w t r F) (w + t) 0 z.val ≤ 2 ^ r) ∧
    (∀ F1 F2 : Fin r → Fin H → Bool,
      (∀ z : Fin D, massF w (familyTable w t r F1) (w + t) 0 z.val =
        massF w (familyTable w t r F2) (w + t) 0 z.val) → F1 = F2) := by
  intro D H
  have hmass_eq : ∀ (F : Fin r → Fin H → Bool) (s z : Nat),
      let flags : Nat → Nat → Bool := fun i u =>
        if hi : i < r then if hu : u < H then F ⟨i, hi⟩ ⟨u, hu⟩ else false else false
      let base : Rows := fun site pattern =>
        let old := pattern % 2
        let newBit := (pattern / D) % 2
        decide (site < w) || (old == newBit) || ((old == 1) == flags (site - w) ((pattern % D) / 2))
      massF w (familyTable w t r F) (w + t) s z = massF w base (w + r) s z := by
    intro F s z flags base
    have hlen : w + t = w + r + (t - r) := by omega
    rw [hlen]
    exact mass_insCopy_iter w r hw base (fun i hi pat => by simp [base, hi]) (t - r) s z
  refine ⟨?_, ?_, ?_⟩
  · intro F
    let flags : Nat → Nat → Bool := fun i u =>
      if hi : i < r then if hu : u < H then F ⟨i, hi⟩ ⟨u, hu⟩ else false else false
    have h513 := PEqualNP.Outside.L_lib_513 w r hw flags
    dsimp only at h513
    refine ⟨fun _ => 1, fun z => massF w (familyTable w t r F) (w + t) 0 z.val,
      fun _ => Nat.zero_lt_one, fun z => ?_, fun s z => ?_⟩
    · dsimp only
      rw [hmass_eq F 0 z.val]
      exact (h513.1 ⟨0, Nat.pow_pos (by decide : 0 < 2)⟩ z).2.1
    · dsimp only
      rw [Nat.one_mul, hmass_eq F s.val z.val, hmass_eq F 0 z.val]
      exact (h513.1 s z).1
  · intro F z
    let flags : Nat → Nat → Bool := fun i u =>
      if hi : i < r then if hu : u < H then F ⟨i, hi⟩ ⟨u, hu⟩ else false else false
    have h513 := PEqualNP.Outside.L_lib_513 w r hw flags
    dsimp only at h513
    rw [hmass_eq F 0 z.val]
    exact (h513.1 ⟨0, Nat.pow_pos (by decide : 0 < 2)⟩ z).2
  · intro F1 F2 hlast_eq
    let flags1 : Nat → Nat → Bool := fun i u =>
      if hi : i < r then if hu : u < H then F1 ⟨i, hi⟩ ⟨u, hu⟩ else false else false
    let flags2 : Nat → Nat → Bool := fun i u =>
      if hi : i < r then if hu : u < H then F2 ⟨i, hi⟩ ⟨u, hu⟩ else false else false
    have h513_1 := PEqualNP.Outside.L_lib_513 w r hw flags1
    have h513_2 := PEqualNP.Outside.L_lib_513 w r hw flags2
    dsimp only at h513_1 h513_2
    let undo : (Nat → Nat) → Nat → Nat := fun v j =>
      let x := v (j / 2)
      let y := v (j / 2 + H)
      if j % 2 = 0 then (if x < y then x else x - y)
      else (if x < y then y - x else y)
    have h2H : 2 * H = D := by
      cases w with
      | zero => omega
      | succ w' =>
        dsimp only [H, D]
        rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), Nat.mul_comm]
    have hback_eq : ∀ (k : Nat) (j : Nat), j < D →
        Nat.rec (motive := fun _ => Nat → Nat)
          (fun z => massF w (fun site pattern =>
            let old := pattern % 2; let newBit := (pattern / D) % 2
            decide (site < w) || (old == newBit) || ((old == 1) == flags1 (site - w) ((pattern % D) / 2)))
            (w + r) 0 z)
          (fun _ prev => undo prev) k j =
        Nat.rec (motive := fun _ => Nat → Nat)
          (fun z => massF w (fun site pattern =>
            let old := pattern % 2; let newBit := (pattern / D) % 2
            decide (site < w) || (old == newBit) || ((old == 1) == flags2 (site - w) ((pattern % D) / 2)))
            (w + r) 0 z)
          (fun _ prev => undo prev) k j := by
      intro k
      induction k with
      | zero =>
        intro j hj
        have heq := hlast_eq ⟨j, hj⟩
        rw [hmass_eq F1 0 j, hmass_eq F2 0 j] at heq
        exact heq
      | succ k ih =>
        intro j hj
        change undo _ j = undo _ j
        dsimp only [undo]
        rw [ih (j / 2) (by omega), ih (j / 2 + H) (by omega)]
    funext i u
    have h1 := h513_1.2.2 i u
    have h2 := h513_2.2.2 i u
    have hlu : u.val < D := by omega
    have hluH : u.val + H < D := by omega
    have hb1 := hback_eq (r - 1 - i.val) u.val hlu
    have hb2 := hback_eq (r - 1 - i.val) (u.val + H) hluH
    have heq_blt : flags1 i.val u.val = flags2 i.val u.val := by
      rw [← h1, ← h2]
      exact congrArg₂ Nat.blt hb2 hb1
    simpa [flags1, flags2, i.isLt, u.isLt] using heq_blt

theorem mod_inj_on_range (a b M : Nat) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hM : M = 0 ∨ (a ≤ M ∧ b ≤ M)) (hmod : a % M = b % M) : a = b := by
  rcases hM with rfl | ⟨haM, hbM⟩
  · simpa using hmod
  · by_cases ha : a < M
    · by_cases hb : b < M
      · rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
      · have hbe : b = M := by omega
        rw [Nat.mod_eq_of_lt ha, hbe, Nat.mod_self] at hmod
        omega
    · have hae : a = M := by omega
      by_cases hb : b < M
      · rw [hae, Nat.mod_self, Nat.mod_eq_of_lt hb] at hmod
        omega
      · omega

theorem det_lower_bound (w t m S : Nat) (hw : 0 < w)
    (send : Rows → Fin S) (answer : Fin S → Rows → Nat)
    (hcorr : ∀ left right : Rows, goodF w t left → answer (send left) right = countF w t m left right) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    2 ^ ((D / 2) * Nat.log2 C) ≤ S := by
  intro D C
  set r := Nat.log2 C
  set H := D / 2
  have hC_le_2t : C ≤ 2 ^ t := by
    dsimp only [C]
    split_ifs
    · exact le_rfl
    · exact Nat.min_le_left _ _
  have h2r_le_C : 2 ^ r ≤ C := by
    by_cases hC0 : C = 0
    · dsimp only [C] at hC0
      split_ifs at hC0 with hm
      · exact absurd hC0 (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
      · have h1 : 0 < min (2 ^ t) m :=
          Nat.lt_min.mpr ⟨Nat.pow_pos (by decide : 0 < 2), Nat.pos_of_ne_zero hm⟩
        omega
    · have hr_eq : r = Nat.log 2 C := Nat.log2_eq_log_two
      rw [hr_eq]
      exact Nat.pow_log_le_self 2 hC0
  have hr_le_t : r ≤ t := by
    have hpow : 2 ^ r ≤ 2 ^ t := h2r_le_C.trans hC_le_2t
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  obtain ⟨hgood, hbounds, hinj_last⟩ := family_properties w t r hw hr_le_t
  have hM : m = 0 ∨ 2 ^ r ≤ m := by
    by_cases hm : m = 0
    · exact Or.inl hm
    · right
      have hCm : C ≤ m := by dsimp only [C]; rw [if_neg hm]; exact Nat.min_le_right _ _
      exact h2r_le_C.trans hCm
  have hinj : Function.Injective (fun F : Fin r → Fin H → Bool => send (familyTable w t r F)) := by
    intro F1 F2 hsend
    apply hinj_last F1 F2
    intro z0
    let T : Nat → Bool := fun z => decide (z = z0.val)
    have hc1 := hcorr (familyTable w t r F1) (rightFor w T) (hgood F1)
    have hc2 := hcorr (familyTable w t r F2) (rightFor w T) (hgood F2)
    have hceq : countF w t m (familyTable w t r F1) (rightFor w T) =
        countF w t m (familyTable w t r F2) (rightFor w T) := by
      dsimp only at hsend
      rw [← hc1, ← hc2, hsend]
    rw [count_rightFor w t m hw, count_rightFor w t m hw] at hceq
    have hsum1 : (∑ z : Fin D, if T z.val then massF w (familyTable w t r F1) (w + t) 0 z.val else 0) =
        massF w (familyTable w t r F1) (w + t) 0 z0.val := by
      rw [Finset.sum_eq_single z0]
      · simp [T]
      · intro z _ hne; have : z.val ≠ z0.val := fun h => hne (Fin.ext h); simp [T, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsum2 : (∑ z : Fin D, if T z.val then massF w (familyTable w t r F2) (w + t) 0 z.val else 0) =
        massF w (familyTable w t r F2) (w + t) 0 z0.val := by
      rw [Finset.sum_eq_single z0]
      · simp [T]
      · intro z _ hne; have : z.val ≠ z0.val := fun h => hne (Fin.ext h); simp [T, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum1, hsum2] at hceq
    have hb1 := hbounds F1 z0
    have hb2 := hbounds F2 z0
    exact mod_inj_on_range _ _ m hb1.1 hb2.1
      (hM.imp id (fun h => ⟨hb1.2.trans h, hb2.2.trans h⟩)) hceq
  have hcard : Fintype.card (Fin r → Fin H → Bool) ≤ Fintype.card (Fin S) :=
    Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  rwa [← Nat.pow_mul] at hcard

theorem poly11_strict (b d : Nat) (hpos : 0 < 3 * b + d) :
    8 * (462 * b ^ 6 * (2 * b + d) ^ 5 + 330 * b ^ 7 * (2 * b + d) ^ 4 +
         165 * b ^ 8 * (2 * b + d) ^ 3 + 55 * b ^ 9 * (2 * b + d) ^ 2 +
         11 * b ^ 10 * (2 * b + d) + b ^ 11) < (3 * b + d) ^ 11 := by
  have hpoly : (3 * b + d) ^ 11 =
      8 * (462 * b ^ 6 * (2 * b + d) ^ 5 + 330 * b ^ 7 * (2 * b + d) ^ 4 +
           165 * b ^ 8 * (2 * b + d) ^ 3 + 55 * b ^ 9 * (2 * b + d) ^ 2 +
           11 * b ^ 10 * (2 * b + d) + b ^ 11) +
      (d ^ 11 + 33 * b * d ^ 10 + 495 * b ^ 2 * d ^ 9 + 4455 * b ^ 3 * d ^ 8 +
       26730 * b ^ 4 * d ^ 7 + 112266 * b ^ 5 * d ^ 6 + 333102 * b ^ 6 * d ^ 5 +
       682110 * b ^ 7 * d ^ 4 + 912285 * b ^ 8 * d ^ 3 + 715165 * b ^ 9 * d ^ 2 +
       251691 * b ^ 10 * d + 4131 * b ^ 11) := by ring
  have hrem_pos : 0 < d ^ 11 + 4131 * b ^ 11 := by
    by_cases hb : 0 < b
    · have : 1 ≤ b ^ 11 := Nat.one_le_pow 11 b hb
      omega
    · have hd : 0 < d := by omega
      have : 1 ≤ d ^ 11 := Nat.one_le_pow 11 d hd
      omega
  omega

theorem bad11_card_bound (R : Nat) (hR : 0 < R) (G : Finset (Fin R))
    (hG : 2 * R ≤ 3 * G.card) :
    8 * ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun c =>
      6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun k => c k ∉ G)).card)).card < R ^ 11 := by
  classical
  let B : Finset (Fin R) := Gᶜ
  let g := G.card
  let b := B.card
  have hgb : g + b = R := by
    dsimp only [g, b, B]
    rw [Finset.card_compl, Fintype.card_fin]
    have hle : G.card ≤ R := by
      calc G.card ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_univ _
        _ = R := Finset.card_fin R
    omega
  have h3b : 3 * b ≤ R := by omega
  let d := R - 3 * b
  have hR_eq : R = 3 * b + d := by omega
  have hg_eq : g = 2 * b + d := by omega
  let badSet : Finset (Fin 11 → Fin R) := (Finset.univ : Finset (Fin 11 → Fin R)).filter (fun c =>
    6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun k => c k ∈ B)).card)
  have hbad_eq : ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun c =>
      6 ≤ ((Finset.univ : Finset (Fin 11)).filter (fun k => c k ∉ G)).card)) = badSet := by
    ext c; simp [badSet, B]
  rw [hbad_eq]
  let fibS : Finset (Fin 11) → Finset (Fin 11 → Fin R) := fun S =>
    (Finset.univ : Finset (Fin 11 → Fin R)).filter
      (fun c => (Finset.univ.filter (fun k => c k ∈ B)) = S)
  let bigS : Finset (Finset (Fin 11)) := (Finset.univ : Finset (Finset (Fin 11))).filter (fun S => 6 ≤ S.card)
  have hdisj : Set.PairwiseDisjoint (bigS : Set (Finset (Fin 11))) fibS := by
    intro S1 _ S2 _ hne
    change Disjoint (fibS S1) (fibS S2)
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [fibS, Finset.mem_filter] at hc1 hc2
    exact hne (hc1.2.symm.trans hc2.2)
  have hbi : bigS.biUnion fibS = badSet := by
    ext c
    simp only [Finset.mem_biUnion, bigS, fibS, badSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨S, hS6, rfl⟩; exact hS6
    · intro h; exact ⟨_, h, rfl⟩
  have hfib_card : ∀ S : Finset (Fin 11), (fibS S).card = b ^ S.card * g ^ (11 - S.card) := by
    intro S
    have heq_pi : fibS S = Fintype.piFinset (fun k : Fin 11 => if k ∈ S then B else G) := by
      ext c
      simp only [fibS, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · intro hS k
        by_cases hk : k ∈ S
        · simp only [hk, ↓reduceIte]
          rw [← hS] at hk
          exact (Finset.mem_filter.mp hk).2
        · simp only [hk, ↓reduceIte]
          rw [← hS] at hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, B, Finset.mem_compl, not_not] at hk
          exact hk
      · intro hall
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hk := hall k
        by_cases hmem : k ∈ S
        · simp only [hmem, ↓reduceIte] at hk
          exact ⟨fun _ => hmem, fun _ => hk⟩
        · simp only [hmem, ↓reduceIte] at hk
          have hnotB : c k ∉ B := by simp [B, hk]
          exact ⟨fun h => absurd h hnotB, fun h => absurd h hmem⟩
    rw [heq_pi, Fintype.card_piFinset]
    have hprod : (∏ k : Fin 11, (if k ∈ S then B else G).card) =
        ∏ k : Fin 11, (if k ∈ S then b else g) :=
      Finset.prod_congr rfl fun k _ => by split_ifs <;> rfl
    rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (Finset.univ.filter (fun k : Fin 11 => k ∈ S)).card = S.card := by
      congr 1; ext k; simp
    have h2 : (Finset.univ.filter (fun k : Fin 11 => k ∉ S)).card = 11 - S.card := by
      have hc : (Finset.univ.filter (fun k : Fin 11 => k ∉ S)) = Sᶜ := by ext k; simp
      rw [hc, Finset.card_compl, Fintype.card_fin]
    rw [h1, h2]
  rw [← hbi, Finset.card_biUnion hdisj]
  simp_rw [hfib_card]
  have hgroup : (∑ S ∈ bigS, b ^ S.card * g ^ (11 - S.card)) =
      ∑ k ∈ Finset.Icc 6 11, Nat.choose 11 k * (b ^ k * g ^ (11 - k)) := by
    let layer : Nat → Finset (Finset (Fin 11)) := fun k =>
      (Finset.univ : Finset (Fin 11)).powersetCard k
    have hdisj2 : Set.PairwiseDisjoint (Finset.Icc 6 11 : Set Nat) layer := by
      intro k1 _ k2 _ hne
      change Disjoint (layer k1) (layer k2)
      rw [Finset.disjoint_left]
      intro S h1 h2
      simp only [layer, Finset.mem_powersetCard] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    have hbi2 : (Finset.Icc 6 11).biUnion layer = bigS := by
      ext S
      simp only [Finset.mem_biUnion, Finset.mem_Icc, layer, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, bigS, Finset.mem_filter, Finset.mem_univ]
      constructor
      · rintro ⟨k, ⟨h6, _⟩, rfl⟩; exact h6
      · intro h6
        have h11 : S.card ≤ 11 := by
          calc S.card ≤ (Finset.univ : Finset (Fin 11)).card := Finset.card_le_univ _
            _ = 11 := Finset.card_fin 11
        exact ⟨S.card, ⟨h6, h11⟩, rfl⟩
    rw [← hbi2, Finset.sum_biUnion hdisj2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hconst : ∀ S ∈ layer k, b ^ S.card * g ^ (11 - S.card) = b ^ k * g ^ (11 - k) := fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    congr 1
    simp [layer, Finset.card_powersetCard]
  rw [hgroup]
  have hIcc : Finset.Icc 6 11 = {6, 7, 8, 9, 10, 11} := by decide
  rw [hIcc]
  have hsum6 : ∀ f : Nat → Nat, (∑ k ∈ ({6, 7, 8, 9, 10, 11} : Finset Nat), f k) =
      f 6 + (f 7 + (f 8 + (f 9 + (f 10 + f 11)))) := fun f => by simp
  rw [hsum6]
  have hc6 : Nat.choose 11 6 = 462 := by decide
  have hc7 : Nat.choose 11 7 = 330 := by decide
  have hc8 : Nat.choose 11 8 = 165 := by decide
  have hc9 : Nat.choose 11 9 = 55 := by decide
  have hc10 : Nat.choose 11 10 = 11 := by decide
  have hc11 : Nat.choose 11 11 = 1 := by decide
  rw [hc6, hc7, hc8, hc9, hc10, hc11, hR_eq, hg_eq]
  have hpoly := poly11_strict b d (by omega)
  have heq_sum : 462 * (b ^ 6 * (2 * b + d) ^ (11 - 6)) +
      (330 * (b ^ 7 * (2 * b + d) ^ (11 - 7)) +
      (165 * (b ^ 8 * (2 * b + d) ^ (11 - 8)) +
      (55 * (b ^ 9 * (2 * b + d) ^ (11 - 9)) +
      (11 * (b ^ 10 * (2 * b + d) ^ (11 - 10)) +
       1 * (b ^ 11 * (2 * b + d) ^ (11 - 11)))))) =
      462 * b ^ 6 * (2 * b + d) ^ 5 + 330 * b ^ 7 * (2 * b + d) ^ 4 +
      165 * b ^ 8 * (2 * b + d) ^ 3 + 55 * b ^ 9 * (2 * b + d) ^ 2 +
      11 * b ^ 10 * (2 * b + d) + b ^ 11 := by ring
  rw [heq_sum]
  exact hpoly

theorem subset_distinguish_half (D m : Nat) (v1 v2 : Fin D → Nat)
    (z0 : Fin D) (hdiff : v1 z0 % m ≠ v2 z0 % m) :
    2 ^ D ≤ 2 * ((Finset.univ : Finset (Fin D → Bool)).filter (fun T =>
      (∑ z : Fin D, if T z then v1 z else 0) % m ≠
      (∑ z : Fin D, if T z then v2 z else 0) % m)).card := by
  classical
  let A : Finset (Fin D → Bool) := (Finset.univ : Finset (Fin D → Bool)).filter (fun T =>
    (∑ z : Fin D, if T z then v1 z else 0) % m ≠
    (∑ z : Fin D, if T z then v2 z else 0) % m)
  let B0 : Finset (Fin D → Bool) := (Finset.univ : Finset (Fin D → Bool)).filter (fun T => T z0 = false)
  let fl : (Fin D → Bool) → (Fin D → Bool) := fun T z => if z = z0 then !T z else T z
  have hfl_inj : Function.Injective fl := by
    intro T1 T2 h
    funext z
    have hz := congrFun h z
    dsimp only [fl] at hz
    by_cases hzz : z = z0
    · simp only [hzz, ↓reduceIte] at hz
      cases h1 : T1 z0 <;> cases h2 : T2 z0 <;> simp_all
    · simpa [hzz] using hz
  have hB0_card : 2 * B0.card = 2 ^ D := by
    let B1 : Finset (Fin D → Bool) := (Finset.univ : Finset (Fin D → Bool)).filter (fun T => T z0 = true)
    have hdisj : Disjoint B0 B1 := by
      rw [Finset.disjoint_left]
      intro T h0 h1
      simp only [B0, B1, Finset.mem_filter] at h0 h1
      rw [h0.2] at h1; exact Bool.noConfusion h1.2
    have hunion : B0 ∪ B1 = Finset.univ := by
      ext T; simp only [B0, B1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases T z0 <;> simp
    have hbij : B1 = B0.image fl := by
      ext T
      simp only [B1, B0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hT
        refine ⟨fl T, by simp [fl, hT], ?_⟩
        funext z; dsimp only [fl]; by_cases hzz : z = z0 <;> simp [hzz]
      · rintro ⟨T', hT', rfl⟩; simp [fl, hT']
    have hcard_u : (Finset.univ : Finset (Fin D → Bool)).card = 2 ^ D := by
      simp [Fintype.card_fun]
    rw [← hcard_u, ← hunion, Finset.card_union_of_disjoint hdisj, hbij,
      Finset.card_image_of_injective _ hfl_inj]
    omega
  have hpair : ∀ T ∈ B0, T ∈ A ∨ fl T ∈ A := by
    intro T hT
    have hTz : T z0 = false := (Finset.mem_filter.mp hT).2
    by_cases hTA : T ∈ A
    · exact Or.inl hTA
    · right
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hTA ⊢
      have hsum_fl : ∀ v : Fin D → Nat,
          (∑ z : Fin D, if fl T z then v z else 0) =
          (∑ z : Fin D, if T z then v z else 0) + v z0 := fun v => by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ z0),
            ← Finset.add_sum_erase Finset.univ (fun z => if T z then v z else 0) (Finset.mem_univ z0)]
        have hrest : (∑ z ∈ Finset.univ.erase z0, if fl T z then v z else 0) =
            ∑ z ∈ Finset.univ.erase z0, if T z then v z else 0 := by
          refine Finset.sum_congr rfl fun z hz => ?_
          have hne : z ≠ z0 := (Finset.mem_erase.mp hz).1
          simp [fl, hne]
        rw [hrest]
        simp [fl, hTz]
        omega
      rw [hsum_fl v1, hsum_fl v2]
      intro hfl_eq
      apply hdiff
      by_cases hm : m = 0
      · subst hm; simp at hTA hfl_eq ⊢; omega
      · have hmod1 : ((∑ z : Fin D, if T z then v1 z else 0) % m + v1 z0 % m) % m =
            ((∑ z : Fin D, if T z then v2 z else 0) % m + v2 z0 % m) % m := by
          rw [← Nat.add_mod, ← Nat.add_mod]; exact hfl_eq
        rw [hTA] at hmod1
        set S := (∑ z : Fin D, if T z then v2 z else 0) % m
        have hSlt : S < m := Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
        have hv1lt : v1 z0 % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
        have hv2lt : v2 z0 % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
        have hsub : ∀ x y : Nat, x < m → y < m → (S + x) % m = (S + y) % m → x = y := by
          intro x y hx hy heq
          by_cases h1 : S + x < m
          · by_cases h2 : S + y < m
            · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at heq; omega
            · have h2' : (S + y) % m = S + y - m := by
                have : S + y = (S + y - m) + m := by omega
                conv_lhs => rw [this]
                rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [Nat.mod_eq_of_lt h1, h2'] at heq; omega
          · have h1' : (S + x) % m = S + x - m := by
              have : S + x = (S + x - m) + m := by omega
              conv_lhs => rw [this]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            by_cases h2 : S + y < m
            · rw [h1', Nat.mod_eq_of_lt h2] at heq; omega
            · have h2' : (S + y) % m = S + y - m := by
                have : S + y = (S + y - m) + m := by omega
                conv_lhs => rw [this]
                rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [h1', h2'] at heq; omega
        exact hsub _ _ hv1lt hv2lt hmod1
  have hB0_le : B0.card ≤ A.card := by
    let pick : (Fin D → Bool) → (Fin D → Bool) := fun T => if T ∈ A then T else fl T
    refine Finset.card_le_card_of_injOn pick ?_ ?_
    · intro T hT
      simp only [Finset.mem_coe] at hT ⊢
      dsimp only [pick]
      by_cases hTA : T ∈ A
      · rw [if_pos hTA]; exact hTA
      · rw [if_neg hTA]
        exact (hpair T hT).resolve_left hTA
    · intro T1 hT1 T2 hT2 heq
      simp only [Finset.mem_coe, B0, Finset.mem_filter, Finset.mem_univ, true_and] at hT1 hT2
      dsimp only [pick] at heq
      by_cases h1 : T1 ∈ A <;> by_cases h2 : T2 ∈ A
      · simpa [h1, h2] using heq
      · simp only [h1, h2, ↓reduceIte] at heq
        have hz := congrFun heq z0
        simp [fl, hT1, hT2] at hz
      · simp only [h1, h2, ↓reduceIte] at heq
        have hz := congrFun heq z0
        simp [fl, hT1, hT2] at hz
      · simp only [h1, h2, ↓reduceIte] at heq
        exact hfl_inj heq
  change 2 ^ D ≤ 2 * A.card
  omega

theorem rand_lower_bound (w t m S R : Nat) (hw : 0 < w) (hR : 0 < R)
    (put : Fin R → Rows → Fin S) (get : Fin R → Fin S → Rows → Nat)
    (hcorr : ∀ x y : Rows, goodF w t x →
      2 * R ≤ 3 * ((List.finRange R).filter (fun coin => get coin (put coin x) y == countF w t m x y)).length) :
    let D := 2 ^ w
    let C := if m = 0 then 2 ^ t else min (2 ^ t) m
    2 ^ ((D / 2) * Nat.log2 C) ≤ 2 * S ^ 11 := by
  classical
  intro D C
  set r := Nat.log2 C
  set H := D / 2
  have hC_le_2t : C ≤ 2 ^ t := by
    dsimp only [C]
    split_ifs
    · exact le_rfl
    · exact Nat.min_le_left _ _
  have h2r_le_C : 2 ^ r ≤ C := by
    by_cases hC0 : C = 0
    · dsimp only [C] at hC0
      split_ifs at hC0 with hm
      · exact absurd hC0 (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
      · have h1 : 0 < min (2 ^ t) m :=
          Nat.lt_min.mpr ⟨Nat.pow_pos (by decide : 0 < 2), Nat.pos_of_ne_zero hm⟩
        omega
    · have hr_eq : r = Nat.log 2 C := Nat.log2_eq_log_two
      rw [hr_eq]
      exact Nat.pow_log_le_self 2 hC0
  have hr_le_t : r ≤ t :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (h2r_le_C.trans hC_le_2t)
  obtain ⟨hgood, hbounds, hinj_last⟩ := family_properties w t r hw hr_le_t
  have hM : m = 0 ∨ 2 ^ r ≤ m := by
    by_cases hm : m = 0
    · exact Or.inl hm
    · right
      have hCm : C ≤ m := by dsimp only [C]; rw [if_neg hm]; exact Nat.min_le_right _ _
      exact h2r_le_C.trans hCm
  let I := Fin r → Fin H → Bool
  let Y := Fin D → Bool
  let X : I → Rows := fun F => familyTable w t r F
  let yOf : Y → Rows := fun T => rightFor w (fun z => if hz : z < D then T ⟨z, hz⟩ else false)
  let bad : (Fin 11 → Fin R) → I → Y → Bool := fun c F T =>
    decide (6 ≤ ((Finset.univ : Finset (Fin 11)).filter
      (fun k => get (c k) (put (c k) (X F)) (yOf T) ≠ countF w t m (X F) (yOf T))).card)
  have hbad_FT : ∀ (F : I) (T : Y),
      8 * ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun c => bad c F T = true)).card < R ^ 11 := by
    intro F T
    let G : Finset (Fin R) := Finset.univ.filter (fun coin =>
      get coin (put coin (X F)) (yOf T) = countF w t m (X F) (yOf T))
    have hG_card : G.card = ((List.finRange R).filter (fun coin =>
        get coin (put coin (X F)) (yOf T) == countF w t m (X F) (yOf T))).length := by
      have hnd : (List.finRange R).Nodup := List.nodup_finRange R
      have htoF : ((List.finRange R).filter (fun coin =>
          get coin (put coin (X F)) (yOf T) == countF w t m (X F) (yOf T))).toFinset = G := by
        ext coin
        simp [G, List.mem_finRange]
      rw [← htoF, List.toFinset_card_of_nodup (hnd.filter _)]
    have hG_ge : 2 * R ≤ 3 * G.card := by
      rw [hG_card]
      exact hcorr (X F) (yOf T) (hgood F)
    have hbound := bad11_card_bound R hR G hG_ge
    convert hbound using 2
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad, decide_eq_true_eq]
    apply iff_of_eq
    congr 2
    ext k
    simp [G]
  have htotal : 8 * (∑ c : Fin 11 → Fin R, ∑ F : I, ∑ T : Y, (bad c F T).toNat) <
      R ^ 11 * (Fintype.card I * Fintype.card Y) := by
    have hswap : (∑ c : Fin 11 → Fin R, ∑ F : I, ∑ T : Y, (bad c F T).toNat) =
        ∑ F : I, ∑ T : Y, ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun c => bad c F T = true)).card := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ => ?_
      have h1 : ∀ c : Fin 11 → Fin R, (bad c F T).toNat = if bad c F T = true then 1 else 0 := fun c => by
        cases bad c F T <;> rfl
      simp_rw [h1]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hswap, Finset.mul_sum]
    have hIpos : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
    have hYpos : (Finset.univ : Finset Y).Nonempty := Finset.univ_nonempty
    have hlt1 : ∑ F : I, 8 * ∑ T : Y,
        ((Finset.univ : Finset (Fin 11 → Fin R)).filter (fun c => bad c F T = true)).card <
        ∑ _F : I, ∑ _T : Y, R ^ 11 := by
      refine Finset.sum_lt_sum_of_nonempty hIpos fun F _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_lt_sum_of_nonempty hYpos fun T _ => hbad_FT F T
    have hrhs : (∑ _F : I, ∑ _T : Y, R ^ 11) = R ^ 11 * (Fintype.card I * Fintype.card Y) := by
      simp [Finset.sum_const, smul_eq_mul]; ring
    exact hlt1.trans_eq hrhs
  have hex_c : ∃ c0 : Fin 11 → Fin R,
      8 * (∑ F : I, ∑ T : Y, (bad c0 F T).toNat) < Fintype.card I * Fintype.card Y := by
    by_contra hall
    push Not at hall
    have hge : ∑ _c : Fin 11 → Fin R, Fintype.card I * Fintype.card Y ≤
        ∑ c : Fin 11 → Fin R, 8 * (∑ F : I, ∑ T : Y, (bad c F T).toNat) :=
      Finset.sum_le_sum fun c _ => hall c
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at hge
    have hc_card : Fintype.card (Fin 11 → Fin R) = R ^ 11 := by simp
    rw [hc_card] at hge
    omega
  obtain ⟨c0, hc0⟩ := hex_c
  let errF : I → Nat := fun F => ∑ T : Y, (bad c0 F T).toNat
  let Igood : Finset I := Finset.univ.filter (fun F => 4 * errF F < Fintype.card Y)
  let Ibad : Finset I := Finset.univ.filter (fun F => Fintype.card Y ≤ 4 * errF F)
  have hIbad_bound : 2 * Ibad.card < Fintype.card I := by
    have h1 : 2 * Ibad.card * Fintype.card Y ≤ 8 * ∑ F : I, errF F := by
      calc 2 * Ibad.card * Fintype.card Y
          = ∑ _F ∈ Ibad, 2 * Fintype.card Y := by rw [Finset.sum_const, smul_eq_mul]; ring
        _ ≤ ∑ F ∈ Ibad, 8 * errF F := by
            refine Finset.sum_le_sum fun F hF => ?_
            have := (Finset.mem_filter.mp hF).2; omega
        _ = 8 * ∑ F ∈ Ibad, errF F := (Finset.mul_sum ..).symm
        _ ≤ 8 * ∑ F : I, errF F :=
            Nat.mul_le_mul_left 8 (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _)
    have h2 : 2 * Ibad.card * Fintype.card Y < Fintype.card I * Fintype.card Y := lt_of_le_of_lt h1 hc0
    exact Nat.lt_of_mul_lt_mul_right h2
  have hI_split : Igood.card + Ibad.card = Fintype.card I := by
    have hdisj : Disjoint Igood Ibad := by
      rw [Finset.disjoint_left]
      intro F h1 h2
      simp only [Igood, Ibad, Finset.mem_filter] at h1 h2; omega
    have hunion : Igood ∪ Ibad = Finset.univ := by
      ext F; simp only [Igood, Ibad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hI_le_2good : Fintype.card I ≤ 2 * Igood.card := by omega
  have hinj_good : Set.InjOn (fun F : I => fun k : Fin 11 => put (c0 k) (X F)) (Igood : Set I) := by
    intro F1 hF1 F2 hF2 hput
    by_contra hne
    have hlast_ne : ∃ z0 : Fin D, massF w (X F1) (w + t) 0 z0.val ≠ massF w (X F2) (w + t) 0 z0.val := by
      by_contra hall
      push Not at hall
      exact hne (hinj_last F1 F2 hall)
    obtain ⟨z0, hz0⟩ := hlast_ne
    have hmod_ne : massF w (X F1) (w + t) 0 z0.val % m ≠ massF w (X F2) (w + t) 0 z0.val % m := by
      intro hmeq
      have hb1 := hbounds F1 z0
      have hb2 := hbounds F2 z0
      exact hz0 (mod_inj_on_range _ _ m hb1.1 hb2.1
        (hM.imp id (fun h => ⟨hb1.2.trans h, hb2.2.trans h⟩)) hmeq)
    have hhalf := subset_distinguish_half D m
      (fun z => massF w (X F1) (w + t) 0 z.val)
      (fun z => massF w (X F2) (w + t) 0 z.val) z0 hmod_ne
    let Dist : Finset Y := (Finset.univ : Finset Y).filter (fun T =>
      countF w t m (X F1) (yOf T) ≠ countF w t m (X F2) (yOf T))
    have hDist_eq : Dist = (Finset.univ : Finset Y).filter (fun T =>
        (∑ z : Fin D, if T z then massF w (X F1) (w + t) 0 z.val else 0) % m ≠
        (∑ z : Fin D, if T z then massF w (X F2) (w + t) 0 z.val else 0) % m) := by
      ext T
      simp only [Dist, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [count_rightFor w t m hw, count_rightFor w t m hw]
      have h1 : ∀ z : Fin D, (if (if hz : z.val < D then T ⟨z.val, hz⟩ else false) = true then
          massF w (X F1) (w + t) 0 z.val else 0) =
          if T z = true then massF w (X F1) (w + t) 0 z.val else 0 := fun z => by simp [z.isLt]
      have h2 : ∀ z : Fin D, (if (if hz : z.val < D then T ⟨z.val, hz⟩ else false) = true then
          massF w (X F2) (w + t) 0 z.val else 0) =
          if T z = true then massF w (X F2) (w + t) 0 z.val else 0 := fun z => by simp [z.isLt]
      simp_rw [h1, h2]; rfl
    have hDist_ge : Fintype.card Y ≤ 2 * Dist.card := by
      have hYc : Fintype.card Y = 2 ^ D := by simp [Y, Fintype.card_fun]
      rw [hYc, hDist_eq]; exact hhalf
    have hDist_sub : ∀ T ∈ Dist, bad c0 F1 T = true ∨ bad c0 F2 T = true := by
      intro T hT
      have hcnt_ne : countF w t m (X F1) (yOf T) ≠ countF w t m (X F2) (yOf T) :=
        (Finset.mem_filter.mp hT).2
      let Ok1 : Finset (Fin 11) := Finset.univ.filter (fun k =>
        get (c0 k) (put (c0 k) (X F1)) (yOf T) = countF w t m (X F1) (yOf T))
      let Ok2 : Finset (Fin 11) := Finset.univ.filter (fun k =>
        get (c0 k) (put (c0 k) (X F2)) (yOf T) = countF w t m (X F2) (yOf T))
      have hdisj_ok : Disjoint Ok1 Ok2 := by
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [Ok1, Ok2, Finset.mem_filter] at hk1 hk2
        have hpk : put (c0 k) (X F1) = put (c0 k) (X F2) := congrFun hput k
        rw [hpk] at hk1
        exact hcnt_ne (hk1.2.symm.trans hk2.2)
      have hok_sum : Ok1.card + Ok2.card ≤ 11 := by
        rw [← Finset.card_union_of_disjoint hdisj_ok]
        calc (Ok1 ∪ Ok2).card ≤ (Finset.univ : Finset (Fin 11)).card := Finset.card_le_univ _
          _ = 11 := Finset.card_fin 11
      have hcompl1 : ((Finset.univ : Finset (Fin 11)).filter (fun k =>
          get (c0 k) (put (c0 k) (X F1)) (yOf T) ≠ countF w t m (X F1) (yOf T))).card + Ok1.card = 11 := by
        have hc : ((Finset.univ : Finset (Fin 11)).filter (fun k =>
            get (c0 k) (put (c0 k) (X F1)) (yOf T) ≠ countF w t m (X F1) (yOf T))) = Ok1ᶜ := by
          ext k; simp [Ok1]
        rw [hc, Finset.card_compl, Fintype.card_fin]
        have hle : Ok1.card ≤ 11 := by
          calc Ok1.card ≤ (Finset.univ : Finset (Fin 11)).card := Finset.card_le_univ _
            _ = 11 := Finset.card_fin 11
        omega
      have hcompl2 : ((Finset.univ : Finset (Fin 11)).filter (fun k =>
          get (c0 k) (put (c0 k) (X F2)) (yOf T) ≠ countF w t m (X F2) (yOf T))).card + Ok2.card = 11 := by
        have hc : ((Finset.univ : Finset (Fin 11)).filter (fun k =>
            get (c0 k) (put (c0 k) (X F2)) (yOf T) ≠ countF w t m (X F2) (yOf T))) = Ok2ᶜ := by
          ext k; simp [Ok2]
        rw [hc, Finset.card_compl, Fintype.card_fin]
        have hle : Ok2.card ≤ 11 := by
          calc Ok2.card ≤ (Finset.univ : Finset (Fin 11)).card := Finset.card_le_univ _
            _ = 11 := Finset.card_fin 11
        omega
      simp only [bad, decide_eq_true_eq]
      omega
    have hDist_le : Dist.card ≤ errF F1 + errF F2 := by
      have hsub_u : Dist ⊆ (Finset.univ.filter (fun T => bad c0 F1 T = true)) ∪
          (Finset.univ.filter (fun T => bad c0 F2 T = true)) := by
        intro T hT
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hDist_sub T hT
      have herr_eq : ∀ F : I, (Finset.univ.filter (fun T => bad c0 F T = true)).card = errF F := fun F => by
        dsimp only [errF]
        have h1 : ∀ T : Y, (bad c0 F T).toNat = if bad c0 F T = true then 1 else 0 := fun T => by
          cases bad c0 F T <;> rfl
        simp_rw [h1]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      calc Dist.card
          ≤ ((Finset.univ.filter (fun T => bad c0 F1 T = true)) ∪
              (Finset.univ.filter (fun T => bad c0 F2 T = true))).card := Finset.card_le_card hsub_u
        _ ≤ (Finset.univ.filter (fun T => bad c0 F1 T = true)).card +
            (Finset.univ.filter (fun T => bad c0 F2 T = true)).card := Finset.card_union_le _ _
        _ = errF F1 + errF F2 := by rw [herr_eq F1, herr_eq F2]
    have hg1 : 4 * errF F1 < Fintype.card Y := (Finset.mem_filter.mp hF1).2
    have hg2 : 4 * errF F2 < Fintype.card Y := (Finset.mem_filter.mp hF2).2
    omega
  have hgood_le_S11 : Igood.card ≤ S ^ 11 := by
    have h1 := Finset.card_le_card_of_injOn (fun F : I => fun k : Fin 11 => put (c0 k) (X F))
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj_good
    have h2 : (Finset.univ : Finset (Fin 11 → Fin S)).card = S ^ 11 := by simp [Fintype.card_fun]
    rwa [h2] at h1
  have hI_card : Fintype.card I = 2 ^ (H * r) := by
    simp only [I, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← Nat.pow_mul]
  omega

end PEqualNP.Outside.L_lib_526_aux

theorem PEqualNP.Outside.L_lib_526 : (∀ (w t m : Nat), 0 < w →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  let L := w+t
  let n := L+w
  let good := fun (tables : Rows) =>
    ∃ a b : Fin D → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      ∀ s z : Fin D, mass tables L s.val z.val = a s * b z
  let count := fun (left right : Rows) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      if site < L then left site pat else right (site-L) pat))).length % m
  let C := if m = 0 then 2^t else min (2^t) m
  let lower := 2^((D/2)*Nat.log2 C)
  let upper := C^(2*D)
  upper ≤ lower^8 ∧
  (∃ (encode : Rows → Fin upper) (read : Fin upper → Rows → Nat),
    ∀ p q : Rows, good p → read (encode p) q = count p q) ∧
  (∀ (S : Nat) (send : Rows → Fin S) (answer : Fin S → Rows → Nat),
    (∀ left right : Rows, good left → answer (send left) right = count left right) →
    lower ≤ S) ∧
  ∀ (S R : Nat), 0 < R →
    ∀ (put : Fin R → Rows → Fin S) (get : Fin R → Fin S → Rows → Nat),
      (∀ x y : Rows, good x →
        2*R ≤ 3*((List.finRange R).filter (fun coin =>
          get coin (put coin x) y == count x y)).length) →
      lower ≤ 2*S^11) := by
  intro w t m hw D Rows mass L n good count C lower upper
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_lib_526_aux.upper_le_lower_pow8 w t m hw
  · exact PEqualNP.Outside.L_lib_526_aux.upper_protocol w t m
  · intro S send answer hcorr
    exact PEqualNP.Outside.L_lib_526_aux.det_lower_bound w t m S hw send answer hcorr
  · intro S R hR put get hcorr
    exact PEqualNP.Outside.L_lib_526_aux.rand_lower_bound w t m S R hw hR put get hcorr
