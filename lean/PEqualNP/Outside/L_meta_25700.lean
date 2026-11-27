import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25700_aux

lemma two_pow_pred_ge (a : ℕ) (ha : 1 ≤ a) : a ≤ 2 ^ (a - 1) := by
  induction a with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      have hprev := ih hm
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
        rw [pow_succ, mul_comm]
      have hge1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      simp only [Nat.add_sub_cancel] at hprev ⊢
      omega

lemma r_div_two_eq (a c : ℕ) (ha : 2 ≤ a) (hca : c < a) :
    2 ^ (a - 1 - c) * 2 ^ c = 2 ^ a / 2 := by
  rw [← pow_add]
  have h1 : a - 1 - c + c = a - 1 := by omega
  rw [h1]
  have h2 : 2 ^ a = 2 ^ (a - 1) * 2 := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
  rw [h2, Nat.mul_div_cancel _ (by norm_num)]

lemma mul_add_lt {m b : ℕ} (t : Fin m) (o : Fin b) : t.val * b + o.val < m * b := by
  have ht : t.val + 1 ≤ m := t.isLt
  have ho : o.val < b := o.isLt
  nlinarith

lemma mul_add_inj {b t1 t2 o1 o2 : ℕ} (ho1 : o1 < b) (ho2 : o2 < b)
    (heq : t1 * b + o1 = t2 * b + o2) : t1 = t2 ∧ o1 = o2 := by
  have hdiv : (b * t1 + o1) / b = (b * t2 + o2) / b := by
    rw [mul_comm b t1, mul_comm b t2, heq]
  have hb : 0 < b := by omega
  rw [Nat.mul_add_div hb, Nat.mul_add_div hb, Nat.div_eq_of_lt ho1, Nat.div_eq_of_lt ho2, add_zero, add_zero] at hdiv
  exact ⟨hdiv, by nlinarith⟩

noncomputable def bitsEquiv (k : ℕ) :
    { e : Fin (2 ^ k) ≃ (Fin k → Bool) // ∀ x i, e x i = x.val.testBit i.val } := by
  let f : Fin (2 ^ k) → (Fin k → Bool) := fun x i => x.val.testBit i.val
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · exact congrFun hxy ⟨j, hj⟩
    · have hx : x.val < 2 ^ j := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : y.val < 2 ^ j := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  have hcard : Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → Bool) := by
    simp
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  exact ⟨Equiv.ofBijective f hbij, fun _ _ => rfl⟩

noncomputable def splitEquiv (k a c : ℕ) (ha : 2 ≤ a) (hk : 2 ^ a ≤ k) (hca : c < a) :
    { e : Fin (2 ^ k) ≃
        (Fin (2 ^ (a - 1 - c)) → Fin (2 ^ c) → Bool) × Bool ×
          (Fin (2 ^ (a - 1 - c)) × Fin (2 ^ c)) ×
          (Fin (k - (2 ^ a / 2 + a)) → Bool) //
      (∀ x t o, (e x).1 t o = x.val.testBit (t.val * 2 ^ c + o.val)) ∧
      (∀ (j : Fin k), 2 ^ a / 2 ≤ j.val →
        ∀ act1 act2 bank slot rest,
          (e.symm (act1, bank, slot, rest)).val.testBit j.val =
            (e.symm (act2, bank, slot, rest)).val.testBit j.val) } := by
  let r := 2 ^ a
  let b := 2 ^ c
  let m := 2 ^ (a - 1 - c)
  have hmb : m * b = r / 2 := r_div_two_eq a c ha hca
  have hr_half : r / 2 = 2 ^ (a - 1) := by
    have hpow : 2 ^ a = 2 ^ (a - 1) * 2 := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    change 2 ^ a / 2 = 2 ^ (a - 1)
    rw [hpow, Nat.mul_div_cancel _ (by norm_num)]
  have ha_le_half : a ≤ r / 2 := by
    rw [hr_half]
    exact two_pow_pred_ge a (by omega)
  have hhalf_add : r / 2 + a ≤ k := by
    have : r / 2 + r / 2 ≤ r := by omega
    omega
  let TailIdx := Unit ⊕ Fin (a - 1) ⊕ Fin (k - (r / 2 + a))
  let S := (Fin m × Fin b) ⊕ TailIdx
  let idxBack : S → Fin k := fun z =>
    match z with
    | Sum.inl (t, o) =>
        ⟨t.val * b + o.val, by
          have h1 := mul_add_lt t o
          omega⟩
    | Sum.inr (Sum.inl ()) => ⟨r / 2, by omega⟩
    | Sum.inr (Sum.inr (Sum.inl s)) => ⟨r / 2 + 1 + s.val, by omega⟩
    | Sum.inr (Sum.inr (Sum.inr u)) => ⟨r / 2 + a + u.val, by omega⟩
  have hinj : Function.Injective idxBack := by
    intro z1 z2 h
    cases z1 with
    | inl p1 =>
      rcases p1 with ⟨t1, o1⟩
      have h1 : t1.val * b + o1.val < r / 2 := by
        have := mul_add_lt t1 o1
        omega
      cases z2 with
      | inl p2 =>
        rcases p2 with ⟨t2, o2⟩
        have hval : t1.val * b + o1.val = t2.val * b + o2.val := congrArg Fin.val h
        rcases mul_add_inj o1.isLt o2.isLt hval with ⟨ht, ho⟩
        exact congrArg Sum.inl (Prod.ext (Fin.ext ht) (Fin.ext ho))
      | inr z2' =>
        cases z2' with
        | inl u2 =>
          have hval : t1.val * b + o1.val = r / 2 := congrArg Fin.val h
          omega
        | inr z2'' =>
          cases z2'' with
          | inl s2 =>
            have hval : t1.val * b + o1.val = r / 2 + 1 + s2.val := congrArg Fin.val h
            omega
          | inr u2 =>
            have hval : t1.val * b + o1.val = r / 2 + a + u2.val := congrArg Fin.val h
            omega
    | inr z1' =>
      cases z1' with
      | inl u1 =>
        cases u1
        cases z2 with
        | inl p2 =>
          rcases p2 with ⟨t2, o2⟩
          have h2 : t2.val * b + o2.val < r / 2 := by
            have := mul_add_lt t2 o2
            omega
          have hval : r / 2 = t2.val * b + o2.val := congrArg Fin.val h
          omega
        | inr z2' =>
          cases z2' with
          | inl u2 =>
            cases u2
            rfl
          | inr z2'' =>
            cases z2'' with
            | inl s2 =>
              have hval : r / 2 = r / 2 + 1 + s2.val := congrArg Fin.val h
              omega
            | inr u2 =>
              have hval : r / 2 = r / 2 + a + u2.val := congrArg Fin.val h
              omega
      | inr z1'' =>
        cases z1'' with
        | inl s1 =>
          cases z2 with
          | inl p2 =>
            rcases p2 with ⟨t2, o2⟩
            have h2 : t2.val * b + o2.val < r / 2 := by
              have := mul_add_lt t2 o2
              omega
            have hval : r / 2 + 1 + s1.val = t2.val * b + o2.val := congrArg Fin.val h
            omega
          | inr z2' =>
            cases z2' with
            | inl u2 =>
              have hval : r / 2 + 1 + s1.val = r / 2 := congrArg Fin.val h
              omega
            | inr z2'' =>
              cases z2'' with
              | inl s2 =>
                have hval : r / 2 + 1 + s1.val = r / 2 + 1 + s2.val := congrArg Fin.val h
                exact congrArg (fun s => Sum.inr (Sum.inr (Sum.inl s))) (Fin.ext (by omega))
              | inr u2 =>
                have hval : r / 2 + 1 + s1.val = r / 2 + a + u2.val := congrArg Fin.val h
                have hs1 := s1.isLt
                omega
        | inr u1 =>
          cases z2 with
          | inl p2 =>
            rcases p2 with ⟨t2, o2⟩
            have h2 : t2.val * b + o2.val < r / 2 := by
              have := mul_add_lt t2 o2
              omega
            have hval : r / 2 + a + u1.val = t2.val * b + o2.val := congrArg Fin.val h
            omega
          | inr z2' =>
            cases z2' with
            | inl u2 =>
              have hval : r / 2 + a + u1.val = r / 2 := congrArg Fin.val h
              omega
            | inr z2'' =>
              cases z2'' with
              | inl s2 =>
                have hval : r / 2 + a + u1.val = r / 2 + 1 + s2.val := congrArg Fin.val h
                have hs2 := s2.isLt
                omega
              | inr u2 =>
                have hval : r / 2 + a + u1.val = r / 2 + a + u2.val := congrArg Fin.val h
                exact congrArg (fun u => Sum.inr (Sum.inr (Sum.inr u))) (Fin.ext (by omega))
  have hcard : Fintype.card S = Fintype.card (Fin k) := by
    simp only [S, TailIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
    omega
  let eIdx : S ≃ Fin k := Equiv.ofBijective idxBack
    ((Fintype.bijective_iff_injective_and_card idxBack).mpr ⟨hinj, hcard⟩)
  let eBits := bitsEquiv k
  let eSlot : (Fin (a - 1) → Bool) ≃ Fin m × Fin b :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_prod]
      rw [hmb, hr_half])
  let eTail : (TailIdx → Bool) ≃ Bool × (Fin m × Fin b) × (Fin (k - (r / 2 + a)) → Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ Bool).trans
      (Equiv.prodCongr (Equiv.punitArrowEquiv Bool)
        ((Equiv.sumArrowEquivProdArrow _ _ Bool).trans
          (Equiv.prodCongr eSlot (Equiv.refl _))))
  let eFun : (Fin k → Bool) ≃
      (Fin m → Fin b → Bool) × Bool × (Fin m × Fin b) × (Fin (k - (r / 2 + a)) → Bool) :=
    (Equiv.arrowCongr eIdx.symm (Equiv.refl Bool)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ Bool).trans
        (Equiv.prodCongr (Equiv.curry (Fin m) (Fin b) Bool) eTail))
  refine ⟨eBits.1.trans eFun, ⟨fun x t o => ?_, fun j hj act1 act2 bank slot rest => ?_⟩⟩
  · change eBits.1 x (eIdx (Sum.inl (t, o))) = x.val.testBit (t.val * 2 ^ c + o.val)
    rw [eBits.2]
    rfl
  · rw [← eBits.2, ← eBits.2]
    have hstep : ∀ act : Fin m → Fin b → Bool,
        eBits.1 ((eBits.1.trans eFun).symm (act, bank, slot, rest)) j =
          eFun.symm (act, bank, slot, rest) j := by
      intro act
      rw [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    rw [hstep act1, hstep act2]
    have hnot : ∀ p : Fin m × Fin b, eIdx.symm j ≠ Sum.inl p := by
      intro p hp
      have h1 : idxBack (Sum.inl p) = j := by
        have := congrArg eIdx hp
        simpa [eIdx] using this.symm
      have hval : p.1.val * b + p.2.val = j.val := congrArg Fin.val h1
      have hlt := mul_add_lt p.1 p.2
      omega
    cases hs : eIdx.symm j with
    | inl p => exact absurd hs (hnot p)
    | inr sr =>
      have heval : ∀ act : Fin m → Fin b → Bool,
          eFun.symm (act, bank, slot, rest) j = eTail.symm (bank, slot, rest) sr := by
        intro act
        change (Equiv.sumArrowEquivProdArrow (Fin m × Fin b) TailIdx Bool).symm
          ((Equiv.curry (Fin m) (Fin b) Bool).symm act, eTail.symm (bank, slot, rest)) (eIdx.symm j) = _
        rw [hs]
        rfl
      rw [heval act1, heval act2]

def isConstBlock {b : ℕ} (hb : 0 < b) (f : Fin b → Bool) : Prop :=
  ∀ o : Fin b, f o = f ⟨0, hb⟩

instance {b : ℕ} (hb : 0 < b) : DecidablePred (isConstBlock hb) :=
  fun f => inferInstanceAs (Decidable (∀ o : Fin b, f o = f ⟨0, hb⟩))

lemma card_filter_compl {α : Type} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card + (Finset.univ.filter (fun x => ¬ p x)).card = Fintype.card α := by
  rw [← Finset.card_union_of_disjoint]
  · have hun : Finset.univ.filter p ∪ Finset.univ.filter (fun x => ¬ p x) = Finset.univ := by
      ext x
      simp [em]
    rw [hun, Finset.card_univ]
  · rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

lemma card_nonconst_block {b : ℕ} (hb : 0 < b) :
    (Finset.univ.filter (fun f : Fin b → Bool => ¬ isConstBlock hb f)).card = 2 ^ b - 2 := by
  let fF : Fin b → Bool := fun _ => false
  let fT : Fin b → Bool := fun _ => true
  have hne : fF ≠ fT := by
    intro h
    have := congrFun h ⟨0, hb⟩
    simp [fF, fT] at this
  have hconst : Finset.univ.filter (fun f : Fin b → Bool => isConstBlock hb f) = {fF, fT} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hf
      cases h0 : f ⟨0, hb⟩
      · left
        funext o
        rw [hf o, h0]
      · right
        funext o
        rw [hf o, h0]
    · rintro (rfl | rfl) o <;> rfl
  have hcard_c : (Finset.univ.filter (fun f : Fin b → Bool => isConstBlock hb f)).card = 2 := by
    rw [hconst, Finset.card_pair hne]
  have hsum := card_filter_compl (fun f : Fin b → Bool => isConstBlock hb f)
  have huniv : Fintype.card (Fin b → Bool) = 2 ^ b := by
    simp
  rw [hcard_c, huniv] at hsum
  omega

def isConst {m b : ℕ} (hb : 0 < b) (act : Fin m → Fin b → Bool) (t : Fin m) : Prop :=
  isConstBlock hb (act t)

instance {m b : ℕ} (hb : 0 < b) (act : Fin m → Fin b → Bool) : DecidablePred (isConst hb act) :=
  fun t => inferInstanceAs (Decidable (isConstBlock hb (act t)))

def hasConst {m b : ℕ} (hb : 0 < b) (act : Fin m → Fin b → Bool) : Prop :=
  ∃ t : Fin m, isConst hb act t

instance {m b : ℕ} (hb : 0 < b) : DecidablePred (hasConst (m := m) hb) :=
  fun act => inferInstanceAs (Decidable (∃ t : Fin m, isConst hb act t))

lemma card_hasConst {m b : ℕ} (hb : 0 < b) :
    (Finset.univ.filter (fun act : Fin m → Fin b → Bool => hasConst hb act)).card =
      2 ^ (m * b) - (2 ^ b - 2) ^ m := by
  let Snon : Finset (Fin b → Bool) := Finset.univ.filter (fun f => ¬ isConstBlock hb f)
  have hneg :
      Finset.univ.filter (fun act : Fin m → Fin b → Bool => ¬ hasConst hb act) =
        Fintype.piFinset (fun _ : Fin m => Snon) := by
    ext act
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Snon,
      hasConst, isConst, not_exists]
  have hcard_neg :
      (Finset.univ.filter (fun act : Fin m → Fin b → Bool => ¬ hasConst hb act)).card =
        (2 ^ b - 2) ^ m := by
    rw [hneg, Fintype.card_piFinset_const, card_nonconst_block hb]
  have hsum := card_filter_compl (fun act : Fin m → Fin b → Bool => hasConst hb act)
  have huniv : Fintype.card (Fin m → Fin b → Bool) = 2 ^ (m * b) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul, mul_comm]
  rw [hcard_neg, huniv] at hsum
  omega

noncomputable def chosenShift {m b : ℕ} [NeZero m] (hb : 0 < b)
    (act : Fin m → Fin b → Bool) (start : Fin m) : Fin m :=
  if h : ∃ d : ℕ, ∃ hd : d < m, isConst hb act (start + ⟨d, hd⟩) then
    ⟨Nat.find h, (Nat.find_spec h).1⟩
  else
    0

noncomputable def chosenBlock {m b : ℕ} [NeZero m] (hb : 0 < b)
    (act : Fin m → Fin b → Bool) (start : Fin m) : Fin m :=
  start + chosenShift hb act start

lemma chosenBlock_isConst {m b : ℕ} [NeZero m] (hb : 0 < b)
    (act : Fin m → Fin b → Bool) (start : Fin m) (h : hasConst hb act) :
    isConst hb act (chosenBlock hb act start) := by
  rcases h with ⟨t, ht⟩
  have hex : ∃ d : ℕ, ∃ hd : d < m, isConst hb act (start + ⟨d, hd⟩) := by
    refine ⟨(t - start).val, (t - start).isLt, ?_⟩
    have heq : start + ⟨(t - start).val, (t - start).isLt⟩ = t := by
      simp
    rwa [heq]
  unfold chosenBlock chosenShift
  simp only [hex, ↓reduceDIte]
  exact (Nat.find_spec hex).2

def rot {m b : ℕ} [NeZero m] (s : Fin m) (act : Fin m → Fin b → Bool) :
    Fin m → Fin b → Bool :=
  fun t => act (t - s)

lemma isConst_rot {m b : ℕ} [NeZero m] (hb : 0 < b) (s : Fin m)
    (act : Fin m → Fin b → Bool) (t : Fin m) :
    isConst hb (rot s act) (t + s) ↔ isConst hb act t := by
  simp [isConst, rot]

lemma hasConst_rot {m b : ℕ} [NeZero m] (hb : 0 < b) (s : Fin m)
    (act : Fin m → Fin b → Bool) :
    hasConst hb (rot s act) ↔ hasConst hb act := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t - s, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t + s, (isConst_rot hb s act t).mpr ht⟩

lemma chosenShift_rot {m b : ℕ} [NeZero m] (hb : 0 < b) (s : Fin m)
    (act : Fin m → Fin b → Bool) (start : Fin m) :
    chosenShift hb (rot s act) (start + s) = chosenShift hb act start := by
  have hiff : ∀ d : ℕ,
      (∃ hd : d < m, isConst hb (rot s act) ((start + s) + ⟨d, hd⟩)) ↔
        (∃ hd : d < m, isConst hb act (start + ⟨d, hd⟩)) := by
    intro d
    constructor <;> rintro ⟨hd, hcd⟩ <;> refine ⟨hd, ?_⟩
    · have hrew : (start + s) + ⟨d, hd⟩ = (start + ⟨d, hd⟩) + s := by abel
      rw [hrew, isConst_rot] at hcd
      exact hcd
    · have hrew : (start + s) + ⟨d, hd⟩ = (start + ⟨d, hd⟩) + s := by abel
      rw [hrew, isConst_rot]
      exact hcd
  unfold chosenShift
  by_cases h1 : ∃ d : ℕ, ∃ hd : d < m, isConst hb act (start + ⟨d, hd⟩)
  · have h2 : ∃ d : ℕ, ∃ hd : d < m, isConst hb (rot s act) ((start + s) + ⟨d, hd⟩) := by
      rcases h1 with ⟨d, hd⟩
      exact ⟨d, (hiff d).mpr hd⟩
    simp only [h1, h2, ↓reduceDIte]
    apply Fin.ext
    exact Nat.find_congr' (fun {d} => hiff d)
  · have h2 : ¬ ∃ d : ℕ, ∃ hd : d < m, isConst hb (rot s act) ((start + s) + ⟨d, hd⟩) := by
      rintro ⟨d, hd⟩
      exact h1 ⟨d, (hiff d).mp hd⟩
    simp only [h1, h2, ↓reduceDIte]

lemma chosenBlock_rot {m b : ℕ} [NeZero m] (hb : 0 < b) (s : Fin m)
    (act : Fin m → Fin b → Bool) (start : Fin m) :
    chosenBlock hb (rot s act) (start + s) = chosenBlock hb act start + s := by
  unfold chosenBlock
  rw [chosenShift_rot]
  abel

lemma card_chosenBlock_eq {m b : ℕ} [NeZero m] (hb : 0 < b) (t0 : Fin m) :
    (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
      chosenBlock hb p.1 p.2 = t0)).card = 2 ^ (m * b) := by
  have heq_all : ∀ t1 : Fin m,
      (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
        chosenBlock hb p.1 p.2 = t1)).card =
      (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
        chosenBlock hb p.1 p.2 = t0)).card := by
    intro t1
    let s := t1 - t0
    refine Finset.card_bij (fun p _ => (rot (-s) p.1, p.2 + (-s))) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [chosenBlock_rot, hp]
      simp [s]
    · intro p1 _ p2 _ h
      have h1 : rot (-s) p1.1 = rot (-s) p2.1 := congrArg Prod.fst h
      have h2 : p1.2 + (-s) = p2.2 + (-s) := congrArg Prod.snd h
      refine Prod.ext ?_ (add_right_cancel h2)
      funext t
      have := congrFun h1 (t + (-s))
      simpa [rot] using this
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(rot s q.1, q.2 + s), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [chosenBlock_rot, hq]
        simp [s]
      · refine Prod.ext ?_ (add_neg_cancel_right q.2 s)
        funext t
        simp [rot]
  have hsum :
      ∑ t1 : Fin m,
          (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
            chosenBlock hb p.1 p.2 = t1)).card =
        m * 2 ^ (m * b) := by
    rw [← Finset.card_biUnion]
    · have hun :
          Finset.univ.biUnion (fun t1 : Fin m =>
            Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
              chosenBlock hb p.1 p.2 = t1)) = Finset.univ := by
        ext p
        simp
      rw [hun, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm b m, mul_comm]
    · intro t1 _ t2 _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.symm.trans hp2.2)
  have hsum2 :
      ∑ t1 : Fin m,
          (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
            chosenBlock hb p.1 p.2 = t1)).card =
        m * (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
          chosenBlock hb p.1 p.2 = t0)).card := by
    rw [Finset.sum_congr rfl (fun t1 _ => heq_all t1), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hsum2] at hsum
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne m)) hsum

lemma card_hasConst_chosenBlock_eq {m b : ℕ} [NeZero m] (hb : 0 < b) (t0 : Fin m) :
    (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
      hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t0)).card =
      2 ^ (m * b) - (2 ^ b - 2) ^ m := by
  have heq_all : ∀ t1 : Fin m,
      (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
        hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t1)).card =
      (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
        hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t0)).card := by
    intro t1
    let s := t1 - t0
    refine Finset.card_bij (fun p _ => (rot (-s) p.1, p.2 + (-s))) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨(hasConst_rot hb (-s) p.1).mpr hp.1, ?_⟩
      rw [chosenBlock_rot, hp.2]
      simp [s]
    · intro p1 _ p2 _ h
      have h1 : rot (-s) p1.1 = rot (-s) p2.1 := congrArg Prod.fst h
      have h2 : p1.2 + (-s) = p2.2 + (-s) := congrArg Prod.snd h
      refine Prod.ext ?_ (add_right_cancel h2)
      funext t
      have := congrFun h1 (t + (-s))
      simpa [rot] using this
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(rot s q.1, q.2 + s), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨(hasConst_rot hb s q.1).mpr hq.1, ?_⟩
        rw [chosenBlock_rot, hq.2]
        simp [s]
      · refine Prod.ext ?_ (add_neg_cancel_right q.2 s)
        funext t
        simp [rot]
  have hsum :
      ∑ t1 : Fin m,
          (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
            hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t1)).card =
        m * (2 ^ (m * b) - (2 ^ b - 2) ^ m) := by
    rw [← Finset.card_biUnion]
    · have hun :
          Finset.univ.biUnion (fun t1 : Fin m =>
            Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
              hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t1)) =
            (Finset.univ.filter (fun act : Fin m → Fin b → Bool => hasConst hb act)) ×ˢ
              (Finset.univ : Finset (Fin m)) := by
        ext p
        simp
      rw [hun, Finset.card_product, card_hasConst hb, Finset.card_univ, Fintype.card_fin, mul_comm]
    · intro t1 _ t2 _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.2.symm.trans hp2.2.2)
  have hsum2 :
      ∑ t1 : Fin m,
          (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
            hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t1)).card =
        m * (Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
          hasConst hb p.1 ∧ chosenBlock hb p.1 p.2 = t0)).card := by
    rw [Finset.sum_congr rfl (fun t1 _ => heq_all t1), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hsum2] at hsum
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne m)) hsum

def sgn (x : Bool) : ℤ :=
  if x then -1 else 1

lemma sgn_xor (x y : Bool) : sgn (xor x y) = sgn x * sgn y := by
  cases x <;> cases y <;> rfl

lemma sgn_not (x : Bool) : sgn (!x) = - sgn x := by
  cases x <;> rfl

lemma sgn_mul_self (x : Bool) : sgn x * sgn x = 1 := by
  cases x <;> rfl

lemma sum_eq_zero_of_invol {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (τ : α → α) (hmem : ∀ x ∈ s, τ x ∈ s) (hinv : ∀ x ∈ s, τ (τ x) = x)
    (hneg : ∀ x ∈ s, f (τ x) = - f x) :
    ∑ x ∈ s, f x = 0 := by
  have h1 : ∑ x ∈ s, f x = ∑ x ∈ s, f (τ x) := by
    refine (Finset.sum_nbij τ hmem ?_ ?_ (fun _ _ => rfl)).symm
    · intro a ha b hb hab
      have := congrArg τ hab
      rwa [hinv a ha, hinv b hb] at this
    · intro y hy
      exact ⟨τ y, hmem y hy, hinv y hy⟩
  have h2 : ∑ x ∈ s, f (τ x) = - ∑ x ∈ s, f x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hneg
  linarith

def flipBlock {m b : ℕ} (t1 : Fin m) (act : Fin m → Fin b → Bool) :
    Fin m → Fin b → Bool :=
  fun t o => if t = t1 then !(act t o) else act t o

lemma flipBlock_invol {m b : ℕ} (t1 : Fin m) (act : Fin m → Fin b → Bool) :
    flipBlock t1 (flipBlock t1 act) = act := by
  funext t o
  unfold flipBlock
  by_cases h : t = t1 <;> simp [h]

lemma isConst_flipBlock {m b : ℕ} (hb : 0 < b) (t1 : Fin m)
    (act : Fin m → Fin b → Bool) (t : Fin m) :
    isConst hb (flipBlock t1 act) t ↔ isConst hb act t := by
  unfold isConst isConstBlock flipBlock
  by_cases h : t = t1 <;> simp [h]

lemma hasConst_flipBlock {m b : ℕ} (hb : 0 < b) (t1 : Fin m)
    (act : Fin m → Fin b → Bool) :
    hasConst hb (flipBlock t1 act) ↔ hasConst hb act := by
  unfold hasConst
  exact exists_congr (fun t => isConst_flipBlock hb t1 act t)

lemma chosenBlock_flipBlock {m b : ℕ} [NeZero m] (hb : 0 < b) (t1 : Fin m)
    (act : Fin m → Fin b → Bool) (start : Fin m) :
    chosenBlock hb (flipBlock t1 act) start = chosenBlock hb act start := by
  unfold chosenBlock chosenShift
  have hiff : ∀ d : ℕ,
      (∃ hd : d < m, isConst hb (flipBlock t1 act) (start + ⟨d, hd⟩)) ↔
        (∃ hd : d < m, isConst hb act (start + ⟨d, hd⟩)) := by
    intro d
    exact exists_congr (fun hd => isConst_flipBlock hb t1 act _)
  by_cases h1 : ∃ d : ℕ, ∃ hd : d < m, isConst hb act (start + ⟨d, hd⟩)
  · have h2 : ∃ d : ℕ, ∃ hd : d < m, isConst hb (flipBlock t1 act) (start + ⟨d, hd⟩) := by
      rcases h1 with ⟨d, hd⟩
      exact ⟨d, (hiff d).mpr hd⟩
    simp only [h1, h2, ↓reduceDIte]
    congr 1
    apply Fin.ext
    exact Nat.find_congr' (fun {d} => hiff d)
  · have h2 : ¬ ∃ d : ℕ, ∃ hd : d < m, isConst hb (flipBlock t1 act) (start + ⟨d, hd⟩) := by
      rintro ⟨d, hd⟩
      exact h1 ⟨d, (hiff d).mp hd⟩
    simp only [h1, h2, ↓reduceDIte]

def flipBit {m b : ℕ} (p : Fin m × Fin b) (act : Fin m → Fin b → Bool) :
    Fin m → Fin b → Bool :=
  fun t o => if (t, o) = p then !(act t o) else act t o

lemma flipBit_invol {m b : ℕ} (p : Fin m × Fin b) (act : Fin m → Fin b → Bool) :
    flipBit p (flipBit p act) = act := by
  funext t o
  unfold flipBit
  by_cases h : (t, o) = p <;> simp [h]

lemma sum_bank1_const {m b : ℕ} (p0 p1 : Fin m × Fin b) (hne : p0 ≠ p1) :
    ∑ act : Fin m → Fin b → Bool, sgn (xor (act p0.1 p0.2) (act p1.1 p1.2)) = 0 := by
  refine sum_eq_zero_of_invol Finset.univ _ (flipBit p0) (fun _ _ => Finset.mem_univ _)
    (fun act _ => flipBit_invol p0 act) (fun act _ => ?_)
  have h1 : flipBit p0 act p0.1 p0.2 = !(act p0.1 p0.2) := by simp [flipBit]
  have h2 : flipBit p0 act p1.1 p1.2 = act p1.1 p1.2 := by
    have hne' : (p1.1, p1.2) ≠ p0 := fun h => hne h.symm
    simp [flipBit, hne']
  rw [h1, h2, sgn_xor, sgn_not, sgn_xor]
  ring

lemma sum_bank1_active {m b : ℕ} (p0 p1 q : Fin m × Fin b) (hne : p0 ≠ p1) :
    ∑ act : Fin m → Fin b → Bool,
        sgn (xor (act p0.1 p0.2) (act p1.1 p1.2)) * sgn (act q.1 q.2) = 0 := by
  by_cases hq : q = p0
  · rw [hq]
    refine sum_eq_zero_of_invol Finset.univ _ (flipBit p1) (fun _ _ => Finset.mem_univ _)
      (fun act _ => flipBit_invol p1 act) (fun act _ => ?_)
    have h1 : flipBit p1 act p0.1 p0.2 = act p0.1 p0.2 := by
      have hne' : (p0.1, p0.2) ≠ p1 := hne
      simp [flipBit, hne']
    have h2 : flipBit p1 act p1.1 p1.2 = !(act p1.1 p1.2) := by simp [flipBit]
    rw [h1, h2, sgn_xor, sgn_not, sgn_xor]
    ring
  · refine sum_eq_zero_of_invol Finset.univ _ (flipBit p0) (fun _ _ => Finset.mem_univ _)
      (fun act _ => flipBit_invol p0 act) (fun act _ => ?_)
    have h1 : flipBit p0 act p0.1 p0.2 = !(act p0.1 p0.2) := by simp [flipBit]
    have h2 : flipBit p0 act p1.1 p1.2 = act p1.1 p1.2 := by
      have hne' : (p1.1, p1.2) ≠ p0 := fun h => hne h.symm
      simp [flipBit, hne']
    have h3 : flipBit p0 act q.1 q.2 = act q.1 q.2 := by
      have hne' : (q.1, q.2) ≠ p0 := hq
      simp [flipBit, hne']
    rw [h1, h2, h3, sgn_xor, sgn_not, sgn_xor]
    ring

lemma card_mod_eq {N r : ℕ} (hr : 0 < r) (hdvd : r ∣ N) (j : Fin r) :
    (Finset.univ.filter (fun y : Fin N => (⟨y.val % r, Nat.mod_lt y.val hr⟩ : Fin r) = j)).card =
      N / r := by
  rcases hdvd with ⟨q, rfl⟩
  have hdiv : r * q / r = q := Nat.mul_div_cancel_left q hr
  rw [hdiv]
  trans (Finset.univ : Finset (Fin q)).card
  · refine Finset.card_bij (t := (Finset.univ : Finset (Fin q)))
      (fun (y : Fin (r * q)) _ => (⟨y.val / r, by
        have hy := y.isLt
        exact (Nat.div_lt_iff_lt_mul hr).mpr (by rw [mul_comm q r]; exact hy)⟩ : Fin q)) ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro y1 hy1 y2 hy2 h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      have hmod1 : y1.val % r = j.val := congrArg Fin.val hy1
      have hmod2 : y2.val % r = j.val := congrArg Fin.val hy2
      have hdiv12 : y1.val / r = y2.val / r := congrArg Fin.val h
      apply Fin.ext
      have e1 := Nat.div_add_mod y1.val r
      have e2 := Nat.div_add_mod y2.val r
      rw [← e1, ← e2, hdiv12, hmod1, hmod2]
    · intro u _
      have hlt : r * u.val + j.val < r * q := by
        have hu : u.val + 1 ≤ q := u.isLt
        nlinarith [j.isLt]
      refine ⟨⟨r * u.val + j.val, hlt⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Fin.ext
        simp [Nat.mod_eq_of_lt j.isLt]
      · apply Fin.ext
        simp only [Nat.mul_add_div hr, Nat.div_eq_of_lt j.isLt, add_zero]
  · simp

lemma optimal_decoder_props {N : ℕ} (M : Fin N → Fin N → Bool) :
    ∃ best : Finset (Fin N) → Bool,
      (∀ other : Finset (Fin N) → Bool,
        (Finset.univ.filter (fun z : Fin N × Fin N => best {z.1, z.2} ≠ M z.1 z.2)).card ≤
          (Finset.univ.filter (fun z : Fin N × Fin N => other {z.1, z.2} ≠ M z.1 z.2)).card) ∧
      4 * ((Finset.univ.filter (fun z : Fin N × Fin N => best {z.1, z.2} ≠ M z.1 z.2)).card : ℤ) +
        ∑ x : Fin N, ∑ y : Fin N, sgn (M x y) * sgn (M y x) = (N : ℤ) ^ 2 ∧
      (∀ x y : Fin N, best {x, y} = (M x y && M y x)) := by
  let best : Finset (Fin N) → Bool :=
    fun S => decide (∃ x y : Fin N, S = {x, y} ∧ M x y = true ∧ M y x = true)
  have hbest : ∀ x y : Fin N, best {x, y} = (M x y && M y x) := by
    intro x y
    unfold best
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨x', y', hpair, hm1, hm2⟩
      have hx : x ∈ ({x', y'} : Finset (Fin N)) := by
        rw [← hpair]
        simp
      have hy : y ∈ ({x', y'} : Finset (Fin N)) := by
        rw [← hpair]
        simp
      have hx' : x' ∈ ({x, y} : Finset (Fin N)) := by
        rw [hpair]
        simp
      have hy' : y' ∈ ({x, y} : Finset (Fin N)) := by
        rw [hpair]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hx' hy'
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        rcases hx' with h1 | h1 <;> rcases hy' with h2 | h2 <;>
        subst_vars
      all_goals first | exact ⟨hm1, hm2⟩ | exact ⟨hm2, hm1⟩
    · rintro ⟨hm1, hm2⟩
      exact ⟨x, y, rfl, hm1, hm2⟩
  let err : (Finset (Fin N) → Bool) → Fin N → Fin N → ℕ :=
    fun dec x y => if dec {x, y} ≠ M x y then 1 else 0
  have hcard_err : ∀ dec : Finset (Fin N) → Bool,
      (Finset.univ.filter (fun z : Fin N × Fin N => dec {z.1, z.2} ≠ M z.1 z.2)).card =
        ∑ x : Fin N, ∑ y : Fin N, err dec x y := by
    intro dec
    rw [← Fintype.sum_prod_type (f := fun z : Fin N × Fin N => err dec z.1 z.2)]
    unfold err
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hopt : ∀ other : Finset (Fin N) → Bool,
      (Finset.univ.filter (fun z : Fin N × Fin N => best {z.1, z.2} ≠ M z.1 z.2)).card ≤
        (Finset.univ.filter (fun z : Fin N × Fin N => other {z.1, z.2} ≠ M z.1 z.2)).card := by
    intro other
    rw [hcard_err best, hcard_err other]
    have hpt : ∀ x y : Fin N, err best x y + err best y x ≤ err other x y + err other y x := by
      intro x y
      unfold err
      rw [hbest x y, hbest y x, Finset.pair_comm y x]
      cases M x y <;> cases M y x <;> cases other {x, y} <;> decide
    have hsum :
        ∑ x : Fin N, ∑ y : Fin N, (err best x y + err best y x) ≤
          ∑ x : Fin N, ∑ y : Fin N, (err other x y + err other y x) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hpt x y))
    have hswap : ∀ dec : Finset (Fin N) → Bool,
        ∑ x : Fin N, ∑ y : Fin N, (err dec x y + err dec y x) =
          2 * ∑ x : Fin N, ∑ y : Fin N, err dec x y := by
      intro dec
      have h1 :
          ∑ x : Fin N, ∑ y : Fin N, (err dec x y + err dec y x) =
            (∑ x : Fin N, ∑ y : Fin N, err dec x y) +
              (∑ x : Fin N, ∑ y : Fin N, err dec y x) := by
        simp only [Finset.sum_add_distrib]
      rw [h1, Finset.sum_comm (f := fun x y => err dec y x), two_mul]
    rw [hswap best, hswap other] at hsum
    omega
  have htr :
      4 * ((Finset.univ.filter (fun z : Fin N × Fin N => best {z.1, z.2} ≠ M z.1 z.2)).card : ℤ) +
        ∑ x : Fin N, ∑ y : Fin N, sgn (M x y) * sgn (M y x) = (N : ℤ) ^ 2 := by
    rw [hcard_err best]
    have hpt : ∀ x y : Fin N,
        2 * ((err best x y : ℤ) + (err best y x : ℤ)) + sgn (M x y) * sgn (M y x) = 1 := by
      intro x y
      unfold err
      rw [hbest x y, hbest y x]
      cases M x y <;> cases M y x <;> decide
    have hsum :
        ∑ x : Fin N, ∑ y : Fin N,
          (2 * ((err best x y : ℤ) + (err best y x : ℤ)) + sgn (M x y) * sgn (M y x)) =
        (N : ℤ) ^ 2 := by
      simp only [hpt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, sq]
    have hexp :
        ∑ x : Fin N, ∑ y : Fin N,
          (2 * ((err best x y : ℤ) + (err best y x : ℤ)) + sgn (M x y) * sgn (M y x)) =
        4 * ((∑ x : Fin N, ∑ y : Fin N, err best x y : ℕ) : ℤ) +
          ∑ x : Fin N, ∑ y : Fin N, sgn (M x y) * sgn (M y x) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.cast_sum]
      rw [Finset.sum_comm (f := fun x y => (err best y x : ℤ))]
      ring
    rw [← hexp]
    exact hsum
  exact ⟨best, hopt, htr, hbest⟩

lemma errors_patch_bound {N : ℕ} (base T : Fin N → Fin N → Bool)
    (π : Equiv.Perm (Fin N)) (flip : Fin N → Bool) (best : Finset (Fin N) → Bool)
    (A B : Finset (Fin N)) (hT : ∀ x ∉ A, ∀ y ∉ B, T x y = base x y) :
    (Finset.univ.filter (fun z : Fin N × Fin N =>
      best {z.1, z.2} ≠ xor (T z.1 (π z.2)) (flip z.1))).card +
      (N - A.card) * (N - B.card) ≤
    (Finset.univ.filter (fun z : Fin N × Fin N =>
      best {z.1, z.2} ≠ xor (base z.1 (π z.2)) (flip z.1))).card + N ^ 2 := by
  let S1 : Finset (Fin N) := Finset.univ \ A
  let S2 : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => π y ∉ B)
  let Sgood : Finset (Fin N × Fin N) := S1 ×ˢ S2
  have hS1 : S1.card = N - A.card := by
    simp [S1, Finset.card_sdiff]
  have hS2 : S2.card = N - B.card := by
    have hbij : S2.card = (Finset.univ \ B).card := by
      refine Finset.card_bij (fun y _ => π y) ?_ ?_ ?_
      · intro y hy
        simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp [hy]
      · intro y1 _ y2 _ h
        exact π.injective h
      · intro b hb
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
        exact ⟨π.symm b, by simp [S2, hb], by simp⟩
    rw [hbij]
    simp [Finset.card_sdiff]
  have hSgood : Sgood.card = (N - A.card) * (N - B.card) := by
    rw [Finset.card_product, hS1, hS2]
  let ET := Finset.univ.filter (fun z : Fin N × Fin N =>
    best {z.1, z.2} ≠ xor (T z.1 (π z.2)) (flip z.1))
  let EB := Finset.univ.filter (fun z : Fin N × Fin N =>
    best {z.1, z.2} ≠ xor (base z.1 (π z.2)) (flip z.1))
  have hsplit : ET.card = (ET ∩ Sgood).card + (ET \ Sgood).card :=
    (Finset.card_inter_add_card_sdiff ET Sgood).symm
  have h1 : (ET ∩ Sgood).card ≤ EB.card := by
    refine Finset.card_le_card ?_
    intro z hz
    simp only [Finset.mem_inter, ET, EB, Sgood, S1, S2, Finset.mem_product,
      Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz ⊢
    rw [← hT z.1 hz.2.1 (π z.2) hz.2.2]
    exact hz.1
  have h2 : (ET \ Sgood).card + Sgood.card ≤ N ^ 2 := by
    have hsub : ET \ Sgood ⊆ Finset.univ \ Sgood :=
      Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
    have hc : (ET \ Sgood).card ≤ (Finset.univ \ Sgood).card := Finset.card_le_card hsub
    have htot : (Finset.univ \ Sgood).card + Sgood.card = N ^ 2 := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Sgood)
      simpa [sq] using this
    omega
  change ET.card + (N - A.card) * (N - B.card) ≤ EB.card + N ^ 2
  rw [hsplit, ← hSgood]
  omega

lemma bernoulli_nat (t m : ℕ) : t ^ m + m * t ^ (m - 1) ≤ (t + 1) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ d =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      have h1 : (t + 1) ^ (d + 1 + 1) = (t + 1) * (t + 1) ^ (d + 1) := by
        rw [pow_succ, mul_comm]
      have h2 : (t + 1) * (t ^ (d + 1) + (d + 1) * t ^ d) ≤ (t + 1) * (t + 1) ^ (d + 1) :=
        Nat.mul_le_mul_left (t + 1) ih
      have hpow : t ^ (d + 1 + 1) = t * t ^ (d + 1) := by
        rw [pow_succ, mul_comm]
      have hpow2 : t ^ (d + 1) = t * t ^ d := by
        rw [pow_succ, mul_comm]
      have hmid :
          (t + 1) * (t ^ (d + 1) + (d + 1) * t ^ d) =
            t ^ (d + 1 + 1) + (d + 1 + 1) * t ^ (d + 1) + (d + 1) * t ^ d := by
        rw [hpow, hpow2]
        ring
      omega

lemma two_mul_hit_ge_Z (a c : ℕ) (ha : 2 ≤ a) (hca : c < a) (h2b : 2 * 2 ^ c ≤ a) :
    2 ^ (2 ^ a / 2) ≤ 2 * (2 ^ (2 ^ a / 2) - (2 ^ (2 ^ c) - 2) ^ 2 ^ (a - 1 - c)) := by
  let b := 2 ^ c
  let m := 2 ^ (a - 1 - c)
  have hmb : m * b = 2 ^ a / 2 := r_div_two_eq a c ha hca
  have hZ : 2 ^ (2 ^ a / 2) = (2 ^ b) ^ m := by
    rw [← pow_mul, mul_comm, hmb]
  have hle : 2 * (2 ^ b - 2) ^ m ≤ (2 ^ b) ^ m := by
    cases c with
    | zero =>
      have hm : 0 < m := Nat.two_pow_pos _
      have h0 : 2 ^ b - 2 = 0 := by simp [b]
      rw [h0, zero_pow (Nat.ne_of_gt hm), mul_zero]
      exact Nat.zero_le _
    | succ c' =>
      have hb2 : 2 ≤ b := by
        have : 1 ≤ c' + 1 := by omega
        exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) this)
      let u := 2 ^ (b - 1)
      have hu2 : 2 ≤ u := by
        have : 1 ≤ b - 1 := by omega
        exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) this)
      have h2b_eq : 2 ^ b = 2 * u := by
        dsimp [u]
        conv_lhs => rw [show b = (b - 1) + 1 by omega, pow_succ, mul_comm]
      have hsub_eq : 2 ^ b - 2 = 2 * (u - 1) := by omega
      rw [hsub_eq, h2b_eq, mul_pow, mul_pow]
      have hcm : c' + 1 < b := Nat.lt_two_pow_self
      have hexp : b - 1 ≤ a - 1 - (c' + 1) := by omega
      have hu_le_m : u ≤ m := Nat.pow_le_pow_right (by norm_num) hexp
      let t := u - 1
      have ht1 : 1 ≤ t := by omega
      have hu_eq : u = t + 1 := by omega
      have htm : t ≤ m := by omega
      have hbern := bernoulli_nat t m
      have hstep : 2 * t ^ m ≤ (t + 1) ^ m := by
        have htm2 : t ^ m ≤ m * t ^ (m - 1) := by
          have hpow : t ^ m = t * t ^ (m - 1) := by
            conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ, mul_comm]
          rw [hpow]
          exact Nat.mul_le_mul_right _ htm
        omega
      rw [← hu_eq] at hstep
      have hmul := Nat.mul_le_mul_left (2 ^ m) hstep
      linarith
  dsimp only [b, m] at hle hZ
  rw [hZ]
  omega

end PEqualNP.Outside.L_meta_25700_aux

theorem PEqualNP.Outside.L_meta_25700 : (∀ (k a c : ℕ), 2 ≤ a → 2^a ≤ k → c < a →
  let N := 2^k
  let r := 2^a
  let b := 2^c
  let m := 2^(a-1-c)
  let Z := 2^(r/2)
  let hit := Z - (2^b-2)^m
  let base := fun (x y : Fin N) => x.val.testBit (y.val % r)
  ∃ (π : Equiv.Perm (Fin N)) (flip : Fin N → Bool),
    let errors := fun (G : Fin N → Fin N → Bool) (decode : Finset (Fin N) → Bool) =>
      (Finset.univ.filter (fun z : Fin N × Fin N =>
        decode ({z.1,z.2} : Finset (Fin N)) ≠ xor (G z.1 (π z.2)) (flip z.1))).card
    let cost := errors base
    ∃ best : Finset (Fin N) → Bool,
      (∀ other : Finset (Fin N) → Bool, cost best ≤ cost other) ∧
      8*r*Z^2*cost best + b*N^2*hit^2 = 2*r*Z^2*N^2 ∧
      (2*b ≤ a → a < 4*b → 128*r*cost best + a*N^2 ≤ 32*r*N^2) ∧
      ∀ (A B : Finset (Fin N)) (T : Fin N → Fin N → Bool),
        (∀ x ∉ A, ∀ y ∉ B, T x y = base x y) →
        errors T best + (N-A.card)*(N-B.card) ≤ cost best + N^2) := by
  intro k a c ha hk hca
  dsimp only
  let N := 2 ^ k
  let r := 2 ^ a
  let b := 2 ^ c
  let m := 2 ^ (a - 1 - c)
  let Z := 2 ^ (r / 2)
  let hit := Z - (2 ^ b - 2) ^ m
  let base : Fin N → Fin N → Bool := fun x y => x.val.testBit (y.val % r)
  have hb_pos : 0 < b := Nat.two_pow_pos c
  have hm_pos : 0 < m := Nat.two_pow_pos (a - 1 - c)
  have : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  have hr_pos : 0 < r := Nat.two_pow_pos a
  have hmb : m * b = r / 2 := PEqualNP.Outside.L_meta_25700_aux.r_div_two_eq a c ha hca
  have hr_half : r / 2 = 2 ^ (a - 1) := by
    have hpow : 2 ^ a = 2 ^ (a - 1) * 2 := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    change 2 ^ a / 2 = 2 ^ (a - 1)
    rw [hpow, Nat.mul_div_cancel _ (by norm_num)]
  have hr_half_ge2 : 2 ≤ r / 2 := by
    rw [hr_half]
    have : 1 ≤ a - 1 := by omega
    exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) this)
  have hr_eq_2half : 2 * (r / 2) = r := by
    have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ, mul_comm]
    change 2 * (2 ^ a / 2) = 2 ^ a
    rw [hr_half, ← hpow]
  have ha_le_half : a ≤ r / 2 := by
    rw [hr_half]
    exact PEqualNP.Outside.L_meta_25700_aux.two_pow_pred_ge a (by omega)
  have hhalf_add : r / 2 + a ≤ k := by omega
  have hr_dvd_N : r ∣ N := Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨eSplit, heSplit1, heSplit2⟩ := PEqualNP.Outside.L_meta_25700_aux.splitEquiv k a c ha hk hca
  let R := Fin (k - (r / 2 + a)) → Bool
  let C := Fintype.card R
  have hC_eq : C = 2 ^ (k - (r / 2 + a)) := by
    simp [C, R]
  have hN_eq : N = r * Z * C := by
    rw [hC_eq]
    change 2 ^ k = 2 ^ a * 2 ^ (r / 2) * 2 ^ (k - (r / 2 + a))
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hN_div_r : N / r = Z * C := by
    rw [hN_eq, mul_assoc, Nat.mul_div_cancel_left _ hr_pos]
  have hZ_eq : Z = 2 ^ (m * b) := by
    dsimp [Z]
    rw [hmb]
  have hcard_pair : 1 < Fintype.card (Fin m × Fin b) := by
    simp only [Fintype.card_prod, Fintype.card_fin, hmb]
    omega
  obtain ⟨p0, p1, hp01⟩ := Fintype.one_lt_card_iff.mp hcard_pair
  let g : Fin N → Fin r := fun x =>
    let s := eSplit x
    if s.2.1 = false then
      ⟨(PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos s.1 s.2.2.1.1).val * b + s.2.2.1.2.val,
        by
          have h1 : (PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos s.1 s.2.2.1.1).val * b +
              s.2.2.1.2.val < m * b :=
            PEqualNP.Outside.L_meta_25700_aux.mul_add_lt
              (PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos s.1 s.2.2.1.1) s.2.2.1.2
          omega⟩
    else
      ⟨r / 2 + (s.2.2.1.1.val * b + s.2.2.1.2.val),
        by
          have h1 : s.2.2.1.1.val * b + s.2.2.1.2.val < m * b :=
            PEqualNP.Outside.L_meta_25700_aux.mul_add_lt s.2.2.1.1 s.2.2.1.2
          omega⟩
  let flip : Fin N → Bool := fun x =>
    let s := eSplit x
    if s.2.1 = false then
      if PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos s.1 then
        s.1 (PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos s.1 s.2.2.1.1) ⟨0, hb_pos⟩
      else false
    else
      xor (s.1 p0.1 p0.2) (s.1 p1.1 p1.2)
  have hg_bank_false : ∀ x : Fin N, (eSplit x).2.1 = false → (g x).val < r / 2 := by
    intro x hbf
    simp only [g, hbf, ↓reduceIte]
    have h1 : (PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos (eSplit x).1 (eSplit x).2.2.1.1).val * b +
        (eSplit x).2.2.1.2.val < m * b :=
      PEqualNP.Outside.L_meta_25700_aux.mul_add_lt
        (PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos (eSplit x).1 (eSplit x).2.2.1.1)
        (eSplit x).2.2.1.2
    omega
  have hg_bank_true : ∀ x : Fin N, (eSplit x).2.1 = true → r / 2 ≤ (g x).val := by
    intro x hbt
    simp only [g, hbt, Bool.true_eq_false, ↓reduceIte]
    omega
  have hbank_of_lt : ∀ x : Fin N, (g x).val < r / 2 → (eSplit x).2.1 = false := by
    intro x hlt
    cases h : (eSplit x).2.1
    · rfl
    · have := hg_bank_true x h
      omega
  have hbank_of_ge : ∀ x : Fin N, ¬ (g x).val < r / 2 → (eSplit x).2.1 = true := by
    intro x hge
    cases h : (eSplit x).2.1
    · have := hg_bank_false x h
      omega
    · rfl
  let modR : Fin N → Fin r := fun y => ⟨y.val % r, Nat.mod_lt y.val hr_pos⟩
  have hcard_g : ∀ j : Fin r, (Finset.univ.filter (fun x : Fin N => g x = j)).card = N / r := by
    intro j
    rw [hN_div_r]
    by_cases hj : j.val < r / 2
    · let t0 : Fin m := ⟨j.val / b, (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [hmb]; exact hj)⟩
      let o0 : Fin b := ⟨j.val % b, Nat.mod_lt j.val hb_pos⟩
      have hj_eq : t0.val * b + o0.val = j.val := by
        dsimp [t0, o0]
        rw [mul_comm]
        exact Nat.div_add_mod j.val b
      have hbij :
          (Finset.univ.filter (fun x : Fin N => g x = j)).card =
            ((Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
              PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos p.1 p.2 = t0)) ×ˢ
              (Finset.univ : Finset R)).card := by
        refine Finset.card_bij (fun x _ => (((eSplit x).1, (eSplit x).2.2.1.1), (eSplit x).2.2.2)) ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hbank : (eSplit x).2.1 = false := hbank_of_lt x (hx.symm ▸ hj)
          have hval := congrArg Fin.val hx
          simp only [g, hbank, ↓reduceIte] at hval
          rw [← hj_eq] at hval
          have hpair := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x).2.2.1.2.isLt o0.isLt hval
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          exact Fin.ext hpair.1
        · intro x1 hx1 x2 hx2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
          have hbank1 : (eSplit x1).2.1 = false := hbank_of_lt x1 (hx1.symm ▸ hj)
          have hbank2 : (eSplit x2).2.1 = false := hbank_of_lt x2 (hx2.symm ▸ hj)
          have hval1 := congrArg Fin.val hx1
          have hval2 := congrArg Fin.val hx2
          simp only [g, hbank1, ↓reduceIte] at hval1
          simp only [g, hbank2, ↓reduceIte] at hval2
          rw [← hj_eq] at hval1 hval2
          have ho1 := (PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x1).2.2.1.2.isLt o0.isLt hval1).2
          have ho2 := (PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x2).2.2.1.2.isLt o0.isLt hval2).2
          apply eSplit.injective
          have hact : (eSplit x1).1 = (eSplit x2).1 := congrArg (fun p => p.1.1) heq
          have hst : (eSplit x1).2.2.1.1 = (eSplit x2).2.2.1.1 := congrArg (fun p => p.1.2) heq
          have hrest : (eSplit x1).2.2.2 = (eSplit x2).2.2.2 := congrArg (fun p => p.2) heq
          have hoff : (eSplit x1).2.2.1.2 = (eSplit x2).2.2.1.2 := Fin.ext (ho1.trans ho2.symm)
          refine Prod.ext hact (Prod.ext (hbank1.trans hbank2.symm) (Prod.ext (Prod.ext hst hoff) hrest))
        · intro q hq
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hq
          let x := eSplit.symm (q.1.1, false, (q.1.2, o0), q.2)
          refine ⟨x, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            apply Fin.ext
            simp only [g, x, Equiv.apply_symm_apply, ↓reduceIte, hq, hj_eq]
          · simp [x]
      rw [hbij, Finset.card_product, PEqualNP.Outside.L_meta_25700_aux.card_chosenBlock_eq hb_pos t0,
        Finset.card_univ, ← hZ_eq]
    · let t0 : Fin m := ⟨(j.val - r / 2) / b,
        (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [hmb]; have := j.isLt; omega)⟩
      let o0 : Fin b := ⟨(j.val - r / 2) % b, Nat.mod_lt _ hb_pos⟩
      have hj_eq : r / 2 + (t0.val * b + o0.val) = j.val := by
        dsimp [t0, o0]
        have hdm := Nat.div_add_mod (j.val - r / 2) b
        rw [mul_comm]
        omega
      have hbij :
          (Finset.univ.filter (fun x : Fin N => g x = j)).card =
            ((Finset.univ : Finset (Fin m → Fin b → Bool)) ×ˢ (Finset.univ : Finset R)).card := by
        refine Finset.card_bij (fun x _ => ((eSplit x).1, (eSplit x).2.2.2)) ?_ ?_ ?_
        · intro _ _
          exact Finset.mem_univ _
        · intro x1 hx1 x2 hx2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
          have hbank1 : (eSplit x1).2.1 = true := hbank_of_ge x1 (hx1.symm ▸ hj)
          have hbank2 : (eSplit x2).2.1 = true := hbank_of_ge x2 (hx2.symm ▸ hj)
          have hval1 := congrArg Fin.val hx1
          have hval2 := congrArg Fin.val hx2
          simp only [g, hbank1, Bool.true_eq_false, ↓reduceIte] at hval1
          simp only [g, hbank2, Bool.true_eq_false, ↓reduceIte] at hval2
          have hsum1 : (eSplit x1).2.2.1.1.val * b + (eSplit x1).2.2.1.2.val = t0.val * b + o0.val := by
            omega
          have hsum2 : (eSplit x2).2.2.1.1.val * b + (eSplit x2).2.2.1.2.val = t0.val * b + o0.val := by
            omega
          have hpair1 := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x1).2.2.1.2.isLt o0.isLt hsum1
          have hpair2 := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x2).2.2.1.2.isLt o0.isLt hsum2
          apply eSplit.injective
          have hact : (eSplit x1).1 = (eSplit x2).1 := congrArg (fun p => p.1) heq
          have hrest : (eSplit x1).2.2.2 = (eSplit x2).2.2.2 := congrArg (fun p => p.2) heq
          refine Prod.ext hact
            (Prod.ext (hbank1.trans hbank2.symm)
              (Prod.ext (Prod.ext (Fin.ext (hpair1.1.trans hpair2.1.symm))
                (Fin.ext (hpair1.2.trans hpair2.2.symm))) hrest))
        · intro q _
          let x := eSplit.symm (q.1, true, (t0, o0), q.2)
          refine ⟨x, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            apply Fin.ext
            simp only [g, x, Equiv.apply_symm_apply, Bool.true_eq_false, ↓reduceIte, hj_eq]
          · simp [x]
      rw [hbij, Finset.card_product, Finset.card_univ, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, mul_comm b m, ← hZ_eq]
  have hfib : ∀ j : Fin r, {x : Fin N // g x = j} ≃ {y : Fin N // modR y = j} := by
    intro j
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_subtype, Fintype.card_subtype, hcard_g j,
      PEqualNP.Outside.L_meta_25700_aux.card_mod_eq hr_pos hr_dvd_N j]
  let π : Equiv.Perm (Fin N) :=
    (Equiv.sigmaFiberEquiv g).symm.trans
      ((Equiv.sigmaCongrRight hfib).trans (Equiv.sigmaFiberEquiv modR))
  have hπ_mod : ∀ y : Fin N, modR (π y) = g y := by
    intro y
    change modR ((hfib (g y) ⟨y, rfl⟩).1) = g y
    exact (hfib (g y) ⟨y, rfl⟩).2
  let M : Fin N → Fin N → Bool := fun x y => xor (base x (π y)) (flip x)
  obtain ⟨best, hbest_opt, hbest_tr, _⟩ := PEqualNP.Outside.L_meta_25700_aux.optimal_decoder_props M
  have hEq :
      8 * r * Z ^ 2 *
        (Finset.univ.filter (fun z : Fin N × Fin N =>
          best {z.1, z.2} ≠ xor (base z.1 (π z.2)) (flip z.1))).card +
      b * N ^ 2 * hit ^ 2 = 2 * r * Z ^ 2 * N ^ 2 := by
    let W : Fin r → Fin r → ℤ := fun i j =>
      ∑ x ∈ Finset.univ.filter (fun x : Fin N => g x = i),
        PEqualNP.Outside.L_meta_25700_aux.sgn (flip x) *
          PEqualNP.Outside.L_meta_25700_aux.sgn (x.val.testBit j.val)
    have htr_W :
        ∑ x : Fin N, ∑ y : Fin N,
          PEqualNP.Outside.L_meta_25700_aux.sgn (M x y) *
            PEqualNP.Outside.L_meta_25700_aux.sgn (M y x) =
          ∑ i : Fin r, ∑ j : Fin r, W i j * W j i := by
      have h1 : ∀ x y : Fin N,
          PEqualNP.Outside.L_meta_25700_aux.sgn (M x y) *
            PEqualNP.Outside.L_meta_25700_aux.sgn (M y x) =
          (PEqualNP.Outside.L_meta_25700_aux.sgn (flip x) *
            PEqualNP.Outside.L_meta_25700_aux.sgn (x.val.testBit (g y).val)) *
          (PEqualNP.Outside.L_meta_25700_aux.sgn (flip y) *
            PEqualNP.Outside.L_meta_25700_aux.sgn (y.val.testBit (g x).val)) := by
        intro x y
        have hgy : (π y).val % r = (g y).val := congrArg Fin.val (hπ_mod y)
        have hgx : (π x).val % r = (g x).val := congrArg Fin.val (hπ_mod x)
        simp only [M, base, hgy, hgx, PEqualNP.Outside.L_meta_25700_aux.sgn_xor]
        ring
      simp_rw [h1]
      rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := (Finset.univ : Finset (Fin r)))
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hinner : ∀ x ∈ Finset.univ.filter (fun x : Fin N => g x = i),
          ∑ y : Fin N,
            (PEqualNP.Outside.L_meta_25700_aux.sgn (flip x) *
              PEqualNP.Outside.L_meta_25700_aux.sgn (x.val.testBit (g y).val)) *
            (PEqualNP.Outside.L_meta_25700_aux.sgn (flip y) *
              PEqualNP.Outside.L_meta_25700_aux.sgn (y.val.testBit (g x).val)) =
          ∑ j : Fin r,
            (PEqualNP.Outside.L_meta_25700_aux.sgn (flip x) *
              PEqualNP.Outside.L_meta_25700_aux.sgn (x.val.testBit j.val)) * W j i := by
        intro x hx
        have hgx : g x = i := (Finset.mem_filter.mp hx).2
        rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := (Finset.univ : Finset (Fin r)))
          (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        dsimp only [W]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y hy => ?_)
        have hgy : g y = j := (Finset.mem_filter.mp hy).2
        rw [hgx, hgy]
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_mul]
    have hW_bank1 : ∀ i j : Fin r, ¬ i.val < r / 2 → W i j = 0 := by
      intro i j hi
      let t0 : Fin m := ⟨(i.val - r / 2) / b,
        (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [hmb]; have := i.isLt; omega)⟩
      let o0 : Fin b := ⟨(i.val - r / 2) % b, Nat.mod_lt _ hb_pos⟩
      have hi_eq : r / 2 + (t0.val * b + o0.val) = i.val := by
        dsimp [t0, o0]
        have hdm := Nat.div_add_mod (i.val - r / 2) b
        rw [mul_comm]
        omega
      have hreidx :
          W i j =
            ∑ q ∈ (Finset.univ : Finset (Fin m → Fin b → Bool)) ×ˢ (Finset.univ : Finset R),
              PEqualNP.Outside.L_meta_25700_aux.sgn (xor (q.1 p0.1 p0.2) (q.1 p1.1 p1.2)) *
                PEqualNP.Outside.L_meta_25700_aux.sgn
                  ((eSplit.symm (q.1, true, (t0, o0), q.2)).val.testBit j.val) := by
        dsimp only [W]
        refine Finset.sum_bij (fun x _ => ((eSplit x).1, (eSplit x).2.2.2)) ?_ ?_ ?_ ?_
        · intro _ _
          exact Finset.mem_univ _
        · intro x1 hx1 x2 hx2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
          have hbank1 : (eSplit x1).2.1 = true := hbank_of_ge x1 (hx1.symm ▸ hi)
          have hbank2 : (eSplit x2).2.1 = true := hbank_of_ge x2 (hx2.symm ▸ hi)
          have hval1 := congrArg Fin.val hx1
          have hval2 := congrArg Fin.val hx2
          simp only [g, hbank1, Bool.true_eq_false, ↓reduceIte] at hval1
          simp only [g, hbank2, Bool.true_eq_false, ↓reduceIte] at hval2
          have hsum1 : (eSplit x1).2.2.1.1.val * b + (eSplit x1).2.2.1.2.val = t0.val * b + o0.val := by
            omega
          have hsum2 : (eSplit x2).2.2.1.1.val * b + (eSplit x2).2.2.1.2.val = t0.val * b + o0.val := by
            omega
          have hpair1 := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x1).2.2.1.2.isLt o0.isLt hsum1
          have hpair2 := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x2).2.2.1.2.isLt o0.isLt hsum2
          apply eSplit.injective
          have hact : (eSplit x1).1 = (eSplit x2).1 := congrArg (fun p => p.1) heq
          have hrest : (eSplit x1).2.2.2 = (eSplit x2).2.2.2 := congrArg (fun p => p.2) heq
          refine Prod.ext hact
            (Prod.ext (hbank1.trans hbank2.symm)
              (Prod.ext (Prod.ext (Fin.ext (hpair1.1.trans hpair2.1.symm))
                (Fin.ext (hpair1.2.trans hpair2.2.symm))) hrest))
        · intro q _
          let x := eSplit.symm (q.1, true, (t0, o0), q.2)
          refine ⟨x, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            apply Fin.ext
            simp only [g, x, Equiv.apply_symm_apply, Bool.true_eq_false, ↓reduceIte, hi_eq]
          · simp [x]
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hbank : (eSplit x).2.1 = true := hbank_of_ge x (hx.symm ▸ hi)
          have hval := congrArg Fin.val hx
          simp only [g, hbank, Bool.true_eq_false, ↓reduceIte] at hval
          have hsum : (eSplit x).2.2.1.1.val * b + (eSplit x).2.2.1.2.val = t0.val * b + o0.val := by
            omega
          have hpair := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x).2.2.1.2.isLt o0.isLt hsum
          have hxeq : eSplit.symm ((eSplit x).1, true, (t0, o0), (eSplit x).2.2.2) = x := by
            apply eSplit.injective
            rw [Equiv.apply_symm_apply]
            refine Prod.ext rfl (Prod.ext hbank.symm
              (Prod.ext (Prod.ext (Fin.ext hpair.1.symm) (Fin.ext hpair.2.symm)) rfl))
          rw [hxeq]
          simp only [flip, hbank, Bool.true_eq_false, ↓reduceIte]
      rw [hreidx, Finset.sum_product_right]
      refine Finset.sum_eq_zero (fun rest _ => ?_)
      by_cases hj : j.val < r / 2
      · let t1 : Fin m := ⟨j.val / b, (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [hmb]; exact hj)⟩
        let o1 : Fin b := ⟨j.val % b, Nat.mod_lt j.val hb_pos⟩
        have hj_eq : t1.val * b + o1.val = j.val := by
          dsimp [t1, o1]
          rw [mul_comm]
          exact Nat.div_add_mod j.val b
        have hbit : ∀ act : Fin m → Fin b → Bool,
            (eSplit.symm (act, true, (t0, o0), rest)).val.testBit j.val = act t1 o1 := by
          intro act
          rw [← hj_eq, ← heSplit1]
          simp
        simp_rw [hbit]
        exact PEqualNP.Outside.L_meta_25700_aux.sum_bank1_active p0 p1 (t1, o1) hp01
      · have hbit_indep : ∀ act1 act2 : Fin m → Fin b → Bool,
            (eSplit.symm (act1, true, (t0, o0), rest)).val.testBit j.val =
              (eSplit.symm (act2, true, (t0, o0), rest)).val.testBit j.val := by
          intro act1 act2
          exact heSplit2 ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ (by dsimp; omega) act1 act2 true (t0, o0) rest
        let cbit := PEqualNP.Outside.L_meta_25700_aux.sgn
          ((eSplit.symm (fun _ _ => false, true, (t0, o0), rest)).val.testBit j.val)
        have hconst : ∀ act : Fin m → Fin b → Bool,
            PEqualNP.Outside.L_meta_25700_aux.sgn (xor (act p0.1 p0.2) (act p1.1 p1.2)) *
              PEqualNP.Outside.L_meta_25700_aux.sgn
                ((eSplit.symm (act, true, (t0, o0), rest)).val.testBit j.val) =
            PEqualNP.Outside.L_meta_25700_aux.sgn (xor (act p0.1 p0.2) (act p1.1 p1.2)) * cbit := by
          intro act
          rw [hbit_indep act (fun _ _ => false)]
        simp_rw [hconst]
        rw [← Finset.sum_mul, PEqualNP.Outside.L_meta_25700_aux.sum_bank1_const p0 p1 hp01,
          zero_mul]
    have hW_bank0 : ∀ (t0 t1 : Fin m) (o0 o1 : Fin b),
        W ⟨t0.val * b + o0.val, by
            have hlt := PEqualNP.Outside.L_meta_25700_aux.mul_add_lt t0 o0
            omega⟩
          ⟨t1.val * b + o1.val, by
            have hlt := PEqualNP.Outside.L_meta_25700_aux.mul_add_lt t1 o1
            omega⟩ =
          if t0 = t1 then (C : ℤ) * (hit : ℤ) else 0 := by
      intro t0 t1 o0 o1
      have hi0_lt : t0.val * b + o0.val < r / 2 := by
        have hlt := PEqualNP.Outside.L_meta_25700_aux.mul_add_lt t0 o0
        omega
      let i0 : Fin r := ⟨t0.val * b + o0.val, by omega⟩
      let j0 : Fin r := ⟨t1.val * b + o1.val, by
        have hlt := PEqualNP.Outside.L_meta_25700_aux.mul_add_lt t1 o1
        omega⟩
      let P0 : Finset ((Fin m → Fin b → Bool) × Fin m) :=
        Finset.univ.filter (fun p => PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos p.1 p.2 = t0)
      have hreidx :
          W i0 j0 =
            ∑ q ∈ P0 ×ˢ (Finset.univ : Finset R),
              PEqualNP.Outside.L_meta_25700_aux.sgn
                (if PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos q.1.1 then
                  q.1.1 t0 ⟨0, hb_pos⟩ else false) *
              PEqualNP.Outside.L_meta_25700_aux.sgn (q.1.1 t1 o1) := by
        dsimp only [W]
        refine Finset.sum_bij (fun x _ => (((eSplit x).1, (eSplit x).2.2.1.1), (eSplit x).2.2.2)) ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hbank : (eSplit x).2.1 = false := hbank_of_lt x (hx.symm ▸ hi0_lt)
          have hval := congrArg Fin.val hx
          simp only [g, i0, hbank, ↓reduceIte] at hval
          have hpair := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x).2.2.1.2.isLt o0.isLt hval
          simp only [Finset.mem_product, P0, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          exact Fin.ext hpair.1
        · intro x1 hx1 x2 hx2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
          have hbank1 : (eSplit x1).2.1 = false := hbank_of_lt x1 (hx1.symm ▸ hi0_lt)
          have hbank2 : (eSplit x2).2.1 = false := hbank_of_lt x2 (hx2.symm ▸ hi0_lt)
          have hval1 := congrArg Fin.val hx1
          have hval2 := congrArg Fin.val hx2
          simp only [g, i0, hbank1, ↓reduceIte] at hval1
          simp only [g, i0, hbank2, ↓reduceIte] at hval2
          have ho1 := (PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x1).2.2.1.2.isLt o0.isLt hval1).2
          have ho2 := (PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x2).2.2.1.2.isLt o0.isLt hval2).2
          apply eSplit.injective
          have hact : (eSplit x1).1 = (eSplit x2).1 := congrArg (fun p => p.1.1) heq
          have hst : (eSplit x1).2.2.1.1 = (eSplit x2).2.2.1.1 := congrArg (fun p => p.1.2) heq
          have hrest : (eSplit x1).2.2.2 = (eSplit x2).2.2.2 := congrArg (fun p => p.2) heq
          refine Prod.ext hact
            (Prod.ext (hbank1.trans hbank2.symm)
              (Prod.ext (Prod.ext hst (Fin.ext (ho1.trans ho2.symm))) hrest))
        · intro q hq
          simp only [Finset.mem_product, P0, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hq
          let x := eSplit.symm (q.1.1, false, (q.1.2, o0), q.2)
          refine ⟨x, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            apply Fin.ext
            simp only [g, i0, x, Equiv.apply_symm_apply, ↓reduceIte, hq]
          · simp [x]
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hbank : (eSplit x).2.1 = false := hbank_of_lt x (hx.symm ▸ hi0_lt)
          have hval := congrArg Fin.val hx
          simp only [g, i0, hbank, ↓reduceIte] at hval
          have hcb : PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos (eSplit x).1
              (eSplit x).2.2.1.1 = t0 :=
            Fin.ext (PEqualNP.Outside.L_meta_25700_aux.mul_add_inj (eSplit x).2.2.1.2.isLt o0.isLt hval).1
          have hbit : x.val.testBit j0.val = (eSplit x).1 t1 o1 := (heSplit1 x t1 o1).symm
          rw [hbit]
          simp only [flip, hbank, ↓reduceIte, hcb]
      rw [hreidx, Finset.sum_product_right]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      let P0_yes := P0.filter (fun p => PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos p.1)
      let P0_no := P0.filter (fun p => ¬ PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos p.1)
      have hsplitP :
          ∑ p ∈ P0,
              PEqualNP.Outside.L_meta_25700_aux.sgn
                (if PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos p.1 then p.1 t0 ⟨0, hb_pos⟩ else false) *
              PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t1 o1) =
            (∑ p ∈ P0_yes,
              PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t0 ⟨0, hb_pos⟩) *
                PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t1 o1)) +
            (∑ p ∈ P0_no,
              PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t1 o1)) := by
        rw [← Finset.sum_filter_add_sum_filter_not P0
          (fun p => PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos p.1)]
        congr 1
        · refine Finset.sum_congr rfl (fun p hp => ?_)
          have hyes := (Finset.mem_filter.mp hp).2
          simp only [hyes, ↓reduceIte]
        · refine Finset.sum_congr rfl (fun p hp => ?_)
          have hno := (Finset.mem_filter.mp hp).2
          simp only [hno, ↓reduceIte, PEqualNP.Outside.L_meta_25700_aux.sgn, Bool.false_eq_true,
            one_mul]
      have hno_zero : ∑ p ∈ P0_no, PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t1 o1) = 0 := by
        refine PEqualNP.Outside.L_meta_25700_aux.sum_eq_zero_of_invol P0_no _
          (fun p => (PEqualNP.Outside.L_meta_25700_aux.flipBlock t1 p.1, p.2)) ?_ ?_ ?_
        · intro p hp
          simp only [P0_no, P0, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact ⟨by rw [PEqualNP.Outside.L_meta_25700_aux.chosenBlock_flipBlock]; exact hp.1,
            by rw [PEqualNP.Outside.L_meta_25700_aux.hasConst_flipBlock]; exact hp.2⟩
        · intro p _
          exact Prod.ext (PEqualNP.Outside.L_meta_25700_aux.flipBlock_invol t1 p.1) rfl
        · intro p _
          simp only [PEqualNP.Outside.L_meta_25700_aux.flipBlock, ↓reduceIte,
            PEqualNP.Outside.L_meta_25700_aux.sgn_not]
      rw [hsplitP, hno_zero, add_zero]
      by_cases ht01 : t0 = t1
      · subst ht01
        simp only [↓reduceIte]
        have hall1 : ∀ p ∈ P0_yes,
            PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t0 ⟨0, hb_pos⟩) *
              PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t0 o1) = 1 := by
          intro p hp
          simp only [P0_yes, P0, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hct0 : PEqualNP.Outside.L_meta_25700_aux.isConst hb_pos p.1 t0 := by
            rw [← hp.1]
            exact PEqualNP.Outside.L_meta_25700_aux.chosenBlock_isConst hb_pos p.1 p.2 hp.2
          rw [hct0 o1, PEqualNP.Outside.L_meta_25700_aux.sgn_mul_self]
        rw [Finset.sum_congr rfl hall1, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hcard_yes : P0_yes.card = hit := by
          have heq : P0_yes = Finset.univ.filter (fun p : (Fin m → Fin b → Bool) × Fin m =>
              PEqualNP.Outside.L_meta_25700_aux.hasConst hb_pos p.1 ∧
                PEqualNP.Outside.L_meta_25700_aux.chosenBlock hb_pos p.1 p.2 = t0) := by
            ext p
            simp [P0_yes, P0, and_comm]
          rw [heq, PEqualNP.Outside.L_meta_25700_aux.card_hasConst_chosenBlock_eq hb_pos t0, ← hZ_eq]
        rw [hcard_yes]
      · simp only [ht01, ↓reduceIte]
        have hyes_zero :
            ∑ p ∈ P0_yes,
              PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t0 ⟨0, hb_pos⟩) *
                PEqualNP.Outside.L_meta_25700_aux.sgn (p.1 t1 o1) = 0 := by
          refine PEqualNP.Outside.L_meta_25700_aux.sum_eq_zero_of_invol P0_yes _
            (fun p => (PEqualNP.Outside.L_meta_25700_aux.flipBlock t1 p.1, p.2)) ?_ ?_ ?_
          · intro p hp
            simp only [P0_yes, P0, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
            exact ⟨by rw [PEqualNP.Outside.L_meta_25700_aux.chosenBlock_flipBlock]; exact hp.1,
              by rw [PEqualNP.Outside.L_meta_25700_aux.hasConst_flipBlock]; exact hp.2⟩
          · intro p _
            exact Prod.ext (PEqualNP.Outside.L_meta_25700_aux.flipBlock_invol t1 p.1) rfl
          · intro p _
            simp only [PEqualNP.Outside.L_meta_25700_aux.flipBlock, ht01, ↓reduceIte,
              PEqualNP.Outside.L_meta_25700_aux.sgn_not]
            ring
        rw [hyes_zero, mul_zero]
    have hsum_W :
        ∑ i : Fin r, ∑ j : Fin r, W i j * W j i =
          (m : ℤ) * (b : ℤ) ^ 2 * ((C : ℤ) * (hit : ℤ)) ^ 2 := by
      let Sact := Finset.univ.filter (fun i : Fin r => i.val < r / 2)
      have hact_i :
          ∑ i : Fin r, ∑ j : Fin r, W i j * W j i =
            ∑ i ∈ Sact, ∑ j ∈ Sact, W i j * W j i := by
        rw [← Finset.sum_subset (Finset.subset_univ Sact)]
        · refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_subset (Finset.subset_univ Sact)]
          intro j _ hj
          simp only [Sact, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [hW_bank1 j i hj, mul_zero]
        · intro i _ hi
          simp only [Sact, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine Finset.sum_eq_zero (fun j _ => ?_)
          rw [hW_bank1 i j hi, zero_mul]
      rw [hact_i]
      let emb : Fin m × Fin b → Fin r := fun p =>
        ⟨p.1.val * b + p.2.val, by
          have hlt := PEqualNP.Outside.L_meta_25700_aux.mul_add_lt p.1 p.2
          omega⟩
      have hemb_inj : Function.Injective emb := by
        intro p1 p2 h
        have hval := congrArg Fin.val h
        have hpair := PEqualNP.Outside.L_meta_25700_aux.mul_add_inj p1.2.isLt p2.2.isLt hval
        exact Prod.ext (Fin.ext hpair.1) (Fin.ext hpair.2)
      have hSact_img : Sact = Finset.univ.image emb := by
        ext i
        simp only [Sact, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hi
          refine ⟨(⟨i.val / b, (Nat.div_lt_iff_lt_mul hb_pos).mpr (by rw [hmb]; exact hi)⟩,
            ⟨i.val % b, Nat.mod_lt i.val hb_pos⟩), ?_⟩
          apply Fin.ext
          dsimp [emb]
          rw [mul_comm]
          exact Nat.div_add_mod i.val b
        · rintro ⟨⟨t, o⟩, rfl⟩
          have hlt := PEqualNP.Outside.L_meta_25700_aux.mul_add_lt t o
          dsimp [emb]
          omega
      rw [hSact_img, Finset.sum_image (fun p1 _ p2 _ h => hemb_inj h)]
      have hinner : ∀ p : Fin m × Fin b,
          ∑ j ∈ Finset.univ.image emb, W (emb p) j * W j (emb p) =
            (b : ℤ) * ((C : ℤ) * (hit : ℤ)) ^ 2 := by
        intro p
        rw [Finset.sum_image (fun q1 _ q2 _ h => hemb_inj h), Fintype.sum_prod_type]
        rw [Finset.sum_eq_single p.1]
        · have hterm : ∀ o1 : Fin b,
              W (emb p) (emb (p.1, o1)) * W (emb (p.1, o1)) (emb p) =
                ((C : ℤ) * (hit : ℤ)) ^ 2 := by
            intro o1
            dsimp only [emb]
            rw [hW_bank0 p.1 p.1 p.2 o1, hW_bank0 p.1 p.1 o1 p.2]
            simp [sq]
          rw [Finset.sum_congr rfl (fun o1 _ => hterm o1), Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        · intro t1 _ ht1
          refine Finset.sum_eq_zero (fun o1 _ => ?_)
          dsimp only [emb]
          rw [hW_bank0 p.1 t1 p.2 o1]
          have hne : p.1 ≠ t1 := Ne.symm ht1
          simp [hne]
        · intro hp
          exact absurd (Finset.mem_univ p.1) hp
      rw [Finset.sum_congr rfl (fun p _ => hinner p), Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [htr_W, hsum_W] at hbest_tr
    have hint :
        (8 : ℤ) * (r : ℤ) * (Z : ℤ) ^ 2 *
          ((Finset.univ.filter (fun z : Fin N × Fin N =>
            best {z.1, z.2} ≠ xor (base z.1 (π z.2)) (flip z.1))).card : ℤ) +
        (b : ℤ) * (N : ℤ) ^ 2 * (hit : ℤ) ^ 2 =
        (2 : ℤ) * (r : ℤ) * (Z : ℤ) ^ 2 * (N : ℤ) ^ 2 := by
      have hN_int : (N : ℤ) = (r : ℤ) * (Z : ℤ) * (C : ℤ) := by exact_mod_cast hN_eq
      have h2mb_int : (2 : ℤ) * (m : ℤ) * (b : ℤ) = (r : ℤ) := by
        have h : 2 * m * b = r := by
          rw [mul_assoc, hmb, hr_eq_2half]
        exact_mod_cast h
      have hpoly :
          (2 : ℤ) * (r : ℤ) * (Z : ℤ) ^ 2 * ((m : ℤ) * (b : ℤ) ^ 2 * ((C : ℤ) * (hit : ℤ)) ^ 2) =
            (b : ℤ) * (N : ℤ) ^ 2 * (hit : ℤ) ^ 2 := by
        rw [hN_int]
        linear_combination (b : ℤ) * (r : ℤ) * (Z : ℤ) ^ 2 * (C : ℤ) ^ 2 * (hit : ℤ) ^ 2 * h2mb_int
      linear_combination (2 : ℤ) * (r : ℤ) * (Z : ℤ) ^ 2 * hbest_tr - hpoly
    exact_mod_cast hint
  refine ⟨π, flip, best, hbest_opt, hEq, ?_, ?_⟩
  · intro h2b ha4b
    have hhit : Z ≤ 2 * hit := PEqualNP.Outside.L_meta_25700_aux.two_mul_hit_ge_Z a c ha hca h2b
    have ha4b' : a < 4 * b := ha4b
    have hZ_pos : 0 < Z ^ 2 := by positivity
    have hsq : Z ^ 2 ≤ 4 * hit ^ 2 := by nlinarith
    have hba : a * Z ^ 2 ≤ 16 * b * hit ^ 2 := by nlinarith
    have hmul :
        (128 * r *
          (Finset.univ.filter (fun z : Fin N × Fin N =>
            best {z.1, z.2} ≠ xor (base z.1 (π z.2)) (flip z.1))).card + a * N ^ 2) * Z ^ 2 ≤
        (32 * r * N ^ 2) * Z ^ 2 := by
      nlinarith
    exact Nat.le_of_mul_le_mul_right hmul hZ_pos
  · intro A B T hT
    exact PEqualNP.Outside.L_meta_25700_aux.errors_patch_bound base T π flip best A B hT
