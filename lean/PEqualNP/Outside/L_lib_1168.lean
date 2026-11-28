import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1168_aux

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

-- ============================================================
-- Section 1: Exact 1-site Walsh-Hadamard data on Fin 16 mod 11
-- ============================================================

lemma xor1_lt (a b : Fin 16) : a.val ^^^ b.val < 16 := by
  revert a b; decide

def xor1 (a b : Fin 16) : Fin 16 := ⟨a.val ^^^ b.val, xor1_lt a b⟩

lemma xor1_comm (a b : Fin 16) : xor1 a b = xor1 b a := by
  revert a b; decide

lemma xor1_invol (a b : Fin 16) : xor1 (xor1 a b) b = a := by
  revert a b; decide

def f0 (w : Fin 16) : ZMod 11 :=
  if ((w.val &&& 3) != 0 && (w.val &&& 13) != 0) then 1 else 0

def f1 (w : Fin 16) : ZMod 11 :=
  if ((w.val &&& 3) != 0 && (w.val &&& 13) != 1) then 1 else 0

def chi1 (a x : Fin 16) : ZMod 11 :=
  (-1 : ZMod 11) ^ (∑ b : Fin 4, if (a.val.testBit b.val && x.val.testBit b.val) then 1 else 0)

lemma chi1_comm (a x : Fin 16) : chi1 a x = chi1 x a := by
  revert a x; decide

lemma chi1_mul (a x y : Fin 16) : chi1 a (xor1 x y) = chi1 a x * chi1 a y := by
  revert a x y; decide

lemma chi1_orth (a b : Fin 16) :
    (∑ x : Fin 16, chi1 a x * chi1 b x) = if a = b then (16 : ZMod 11) else 0 := by
  revert a b; decide

def f0Hat (a : Fin 16) : ZMod 11 := ∑ w : Fin 16, chi1 a w * f0 w
def f1Hat (a : Fin 16) : ZMod 11 := ∑ w : Fin 16, chi1 a w * f1 w

def only1Set : Finset (Fin 16) := {6, 7, 10, 11, 14, 15}
def neitherSet : Finset (Fin 16) := {1, 2, 3, 4, 5, 8, 9, 12, 13}

lemma f0Hat_eq_zero_iff (a : Fin 16) : f0Hat a = 0 ↔ a = 0 := by
  revert a; decide

lemma f1Hat_eq_zero_iff (a : Fin 16) : f1Hat a = 0 ↔ a ∈ only1Set := by
  revert a; decide

lemma only1Set_card : only1Set.card = 6 := by decide
lemma neitherSet_card : neitherSet.card = 9 := by decide

lemma zero_notMem_only1 : (0 : Fin 16) ∉ only1Set := by decide

lemma mem_neither_iff (a : Fin 16) : a ∈ neitherSet ↔ a ≠ 0 ∧ a ∉ only1Set := by
  revert a; decide

lemma sixteen_ne_zero_z11 : (16 : ZMod 11) ≠ 0 := by decide

-- ============================================================
-- Section 2: Product Walsh-Hadamard transform on Word r over ZMod 11
-- ============================================================

abbrev Word (r : Nat) := Fin r → Fin 16
abbrev Kind (r : Nat) := Finset (Fin r)

def xorR {r : Nat} (x y : Word r) : Word r := fun j => xor1 (x j) (y j)

lemma xorR_invol {r : Nat} (x y : Word r) : xorR (xorR x y) y = x := by
  funext j; exact xor1_invol (x j) (y j)

def chiR {r : Nat} (ξ x : Word r) : ZMod 11 := ∏ j : Fin r, chi1 (ξ j) (x j)

lemma chiR_comm {r : Nat} (ξ x : Word r) : chiR ξ x = chiR x ξ := by
  simp only [chiR]
  exact Finset.prod_congr rfl (fun j _ => chi1_comm (ξ j) (x j))

lemma chiR_mul {r : Nat} (ξ x y : Word r) : chiR ξ (xorR x y) = chiR ξ x * chiR ξ y := by
  simp only [chiR, xorR, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => chi1_mul (ξ j) (x j) (y j))

lemma chiR_orth {r : Nat} (ξ η : Word r) :
    (∑ x : Word r, chiR ξ x * chiR η x) = if ξ = η then (16 : ZMod 11) ^ r else 0 := by
  have h1 : (∑ x : Word r, chiR ξ x * chiR η x) =
      ∏ j : Fin r, ∑ a : Fin 16, chi1 (ξ j) a * chi1 (η j) a := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [chiR, ← Finset.prod_mul_distrib]
  rw [h1]
  have h2 : (∏ j : Fin r, ∑ a : Fin 16, chi1 (ξ j) a * chi1 (η j) a) =
      ∏ j : Fin r, (if ξ j = η j then (16 : ZMod 11) else 0) :=
    Finset.prod_congr rfl (fun j _ => chi1_orth (ξ j) (η j))
  rw [h2]
  by_cases h : ξ = η
  · subst h
    simp [Finset.prod_const]
  · rw [if_neg h]
    have hex : ∃ j : Fin r, ξ j ≠ η j := by
      by_contra hall
      apply h
      funext j
      by_contra hne
      exact hall ⟨j, hne⟩
    rcases hex with ⟨j0, hj0⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j0) (if_neg hj0)

def wht {r : Nat} (d : Word r → ZMod 11) (ξ : Word r) : ZMod 11 :=
  ∑ x : Word r, chiR ξ x * d x

def iwht {r : Nat} (g : Word r → ZMod 11) (x : Word r) : ZMod 11 :=
  ((16 : ZMod 11) ^ r)⁻¹ * ∑ ξ : Word r, chiR ξ x * g ξ

lemma iwht_wht {r : Nat} (d : Word r → ZMod 11) : iwht (wht d) = d := by
  funext x
  simp only [iwht, wht]
  have hswap : (∑ ξ : Word r, chiR ξ x * ∑ y : Word r, chiR ξ y * d y) =
      ∑ y : Word r, d y * ∑ ξ : Word r, chiR x ξ * chiR y ξ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun ξ _ => ?_))
    rw [chiR_comm ξ x, chiR_comm ξ y]
    ring
  rw [hswap]
  have heval : (∑ y : Word r, d y * ∑ ξ : Word r, chiR x ξ * chiR y ξ) =
      d x * (16 : ZMod 11) ^ r := by
    have hterm : ∀ y : Word r, d y * (∑ ξ : Word r, chiR x ξ * chiR y ξ) =
        if y = x then d x * (16 : ZMod 11) ^ r else 0 := by
      intro y
      rw [chiR_orth x y]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hxy : x ≠ y := Ne.symm hyx
        simp [hyx, hxy]
    rw [Finset.sum_congr rfl (fun y _ => hterm y)]
    simp
  rw [heval]
  have hne : (16 : ZMod 11) ^ r ≠ 0 := pow_ne_zero r sixteen_ne_zero_z11
  rw [mul_comm (d x), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

lemma wht_iwht {r : Nat} (g : Word r → ZMod 11) : wht (iwht g) = g := by
  funext ξ
  simp only [wht, iwht]
  have hswap : (∑ x : Word r, chiR ξ x * (((16 : ZMod 11) ^ r)⁻¹ * ∑ η : Word r, chiR η x * g η)) =
      ((16 : ZMod 11) ^ r)⁻¹ * ∑ η : Word r, g η * ∑ x : Word r, chiR ξ x * chiR η x := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun η _ => Finset.sum_congr rfl (fun x _ => ?_))
    ring
  rw [hswap]
  have heval : (∑ η : Word r, g η * ∑ x : Word r, chiR ξ x * chiR η x) =
      g ξ * (16 : ZMod 11) ^ r := by
    have hterm : ∀ η : Word r, g η * (∑ x : Word r, chiR ξ x * chiR η x) =
        if η = ξ then g ξ * (16 : ZMod 11) ^ r else 0 := by
      intro η
      rw [chiR_orth ξ η]
      by_cases h : η = ξ
      · subst h; simp
      · have h' : ξ ≠ η := Ne.symm h
        simp [h, h']
    rw [Finset.sum_congr rfl (fun η _ => hterm η)]
    simp
  rw [heval]
  have hne : (16 : ZMod 11) ^ r ≠ 0 := pow_ne_zero r sixteen_ne_zero_z11
  rw [mul_comm (g ξ), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

def whtEquiv (r : Nat) : (Word r → ZMod 11) ≃ (Word r → ZMod 11) where
  toFun := wht
  invFun := iwht
  left_inv := iwht_wht
  right_inv := wht_iwht

noncomputable def passB {r : Nat} (e : Kind r) (z x : Word r) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))

def kernelVal {r : Nat} (e : Kind r) (w : Word r) : ZMod 11 :=
  ∏ j : Fin r, if j ∈ e then f1 (w j) else f0 (w j)

lemma passB_cast_eq_kernelVal {r : Nat} (e : Kind r) (z x : Word r) :
    (if passB e z x then (1 : ZMod 11) else 0) = kernelVal e (xorR z x) := by
  let pred : Fin r → Bool := fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0)
  have hbool : ∀ j : Fin r,
      (if j ∈ e then f1 (xor1 (z j) (x j)) else f0 (xor1 (z j) (x j))) =
      if pred j = true then (1 : ZMod 11) else 0 := by
    intro j
    dsimp only [pred]
    by_cases hj : j ∈ e
    · simp [hj, f1, xor1]
    · simp [hj, f0, xor1]
  simp only [kernelVal, xorR]
  rw [Finset.prod_congr rfl (fun j _ => hbool j)]
  by_cases hp : passB e z x = true
  · rw [if_pos hp]
    symm
    apply Finset.prod_eq_one
    intro j _
    have hmem : j ∈ (Finset.univ : Finset (Fin r)).toList := Finset.mem_toList.mpr (Finset.mem_univ j)
    have hall : pred j = true := List.all_eq_true.mp hp j hmem
    simp [hall]
  · rw [if_neg hp]
    symm
    have hnotall : ¬ ∀ j ∈ (Finset.univ : Finset (Fin r)).toList, pred j = true := by
      intro hall; exact hp (List.all_eq_true.mpr hall)
    have hex : ∃ j : Fin r, pred j ≠ true := by
      by_contra hno
      apply hnotall
      intro j _
      by_contra hne
      exact hno ⟨j, hne⟩
    rcases hex with ⟨j0, hj0⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j0) (if_neg hj0)

def conv {r : Nat} (e : Kind r) (d : Word r → ZMod 11) (z : Word r) : ZMod 11 :=
  ∑ x : Word r, kernelVal e (xorR z x) * d x

def eig {r : Nat} (e : Kind r) (ξ : Word r) : ZMod 11 :=
  ∏ j : Fin r, if j ∈ e then f1Hat (ξ j) else f0Hat (ξ j)

lemma wht_conv {r : Nat} (e : Kind r) (d : Word r → ZMod 11) (ξ : Word r) :
    wht (conv e d) ξ = eig e ξ * wht d ξ := by
  simp only [wht, conv]
  have h1 : (∑ z : Word r, chiR ξ z * ∑ x : Word r, kernelVal e (xorR z x) * d x) =
      ∑ x : Word r, (∑ z : Word r, chiR ξ z * kernelVal e (xorR z x)) * d x := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    ring
  rw [h1]
  have h2 : ∀ x : Word r, (∑ z : Word r, chiR ξ z * kernelVal e (xorR z x)) =
      eig e ξ * chiR ξ x := by
    intro x
    let φ : Word r ≃ Word r :=
      { toFun := fun z => xorR z x
        invFun := fun w => xorR w x
        left_inv := fun z => xorR_invol z x
        right_inv := fun w => xorR_invol w x }
    have hbij : (∑ z : Word r, chiR ξ z * kernelVal e (xorR z x)) =
        ∑ w : Word r, chiR ξ (xorR w x) * kernelVal e w := by
      refine Fintype.sum_equiv φ _ _ (fun z => ?_)
      simp [φ, xorR_invol]
    rw [hbij]
    have hmul : (∑ w : Word r, chiR ξ (xorR w x) * kernelVal e w) =
        (∑ w : Word r, chiR ξ w * kernelVal e w) * chiR ξ x := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [chiR_mul]; ring
    rw [hmul]
    congr 1
    simp only [eig, f0Hat, f1Hat]
    have hprod : (∏ j : Fin r, if j ∈ e then ∑ w : Fin 16, chi1 (ξ j) w * f1 w
                               else ∑ w : Fin 16, chi1 (ξ j) w * f0 w) =
        ∏ j : Fin r, ∑ w : Fin 16, chi1 (ξ j) w * (if j ∈ e then f1 w else f0 w) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      by_cases hj : j ∈ e <;> simp [hj]
    rw [hprod, Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp only [chiR, kernelVal, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun x _ => by rw [h2 x])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => by ring)

-- ============================================================
-- Section 3: Kernel size = 11 ^ loss(V)
-- ============================================================

def toZ11 (a : Fin 11) : ZMod 11 := (a.val : ZMod 11)
def ofZ11 (a : ZMod 11) : Fin 11 := ⟨a.val, a.val_lt⟩

lemma ofZ11_toZ11 (a : Fin 11) : ofZ11 (toZ11 a) = a := by
  ext; simp only [ofZ11, toZ11]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]

lemma toZ11_ofZ11 (a : ZMod 11) : toZ11 (ofZ11 a) = a := by
  simp only [toZ11, ofZ11, ZMod.natCast_zmod_val]

def fin11EquivZ11 : Fin 11 ≃ ZMod 11 where
  toFun := toZ11
  invFun := ofZ11
  left_inv := ofZ11_toZ11
  right_inv := toZ11_ofZ11

lemma zeroRead_iff_conv_zero {r : Nat} (d : Word r → Fin 11) (e : Kind r) (z : Word r) :
    (((Finset.univ : Finset (Word r)).filter (fun x => passB e z x)).sum (fun x => (d x).val)) % 11 = 0 ↔
    conv e (fun x => toZ11 (d x)) z = 0 := by
  let S : Nat := ((Finset.univ : Finset (Word r)).filter (fun x => passB e z x)).sum (fun x => (d x).val)
  have hcast : (S : ZMod 11) = conv e (fun x => toZ11 (d x)) z := by
    dsimp only [S]
    rw [Nat.cast_sum, Finset.sum_filter]
    simp only [conv, toZ11]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← passB_cast_eq_kernelVal]
    by_cases hp : passB e z x = true <;> simp [hp]
  change S % 11 = 0 ↔ conv e (fun x => toZ11 (d x)) z = 0
  rw [← hcast, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h; exact Nat.dvd_of_mod_eq_zero h
  · intro h; exact Nat.mod_eq_zero_of_dvd h

def eigNeZero {r : Nat} (e : Kind r) (ξ : Word r) : Prop := eig e ξ ≠ 0

lemma eig_ne_zero_iff {r : Nat} (e : Kind r) (ξ : Word r) :
    eig e ξ ≠ 0 ↔ ∀ j : Fin r, (ξ j = 0 → j ∈ e) ∧ (ξ j ∈ only1Set → j ∉ e) := by
  simp only [eig, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  refine forall_congr' (fun j => ?_)
  by_cases hj : j ∈ e
  · simp [hj, f1Hat_eq_zero_iff]
  · simp [hj, f0Hat_eq_zero_iff]

def killSet {r : Nat} (U : Finset (Kind r)) : Finset (Word r) :=
  (Finset.univ : Finset (Word r)).filter (fun ξ =>
    ∀ e : Kind r, (∀ j : Fin r, (ξ j = 0 → j ∈ e) ∧ (ξ j ∈ only1Set → j ∉ e)) → e ∈ U)

lemma kernelSize_eq_eleven_pow_kill {r : Nat} (U : Finset (Kind r)) :
    ((Finset.univ : Finset (Word r → Fin 11)).filter (fun d =>
      ∀ q ∈ ((Finset.univ : Finset (Kind r)) \ U).product (Finset.univ : Finset (Word r)),
        (((Finset.univ : Finset (Word r)).filter (fun x => passB q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0)).card =
    11 ^ (killSet U).card := by
  let M := (Finset.univ : Finset (Kind r)) \ U
  let K_dom := (Finset.univ : Finset (Word r → Fin 11)).filter (fun d =>
    ∀ q ∈ M.product (Finset.univ : Finset (Word r)),
      (((Finset.univ : Finset (Word r)).filter (fun x => passB q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0)
  let K_hat := (Finset.univ : Finset (Word r → ZMod 11)).filter (fun g =>
    ∀ ξ : Word r, ξ ∉ killSet U → g ξ = 0)
  let φ : (Word r → Fin 11) ≃ (Word r → ZMod 11) :=
    (Equiv.arrowCongr (Equiv.refl (Word r)) fin11EquivZ11).trans (whtEquiv r)
  have hmem_iff : ∀ d : Word r → Fin 11, d ∈ K_dom ↔ φ d ∈ K_hat := by
    intro d
    simp only [K_dom, K_hat, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (∀ q ∈ M.product (Finset.univ : Finset (Word r)),
        (((Finset.univ : Finset (Word r)).filter (fun x => passB q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0) ↔
        ∀ e ∈ M, ∀ z : Word r, conv e (fun x => toZ11 (d x)) z = 0 := by
      constructor
      · intro h e he z
        exact (zeroRead_iff_conv_zero d e z).mp (h (e, z) (Finset.mem_product.mpr ⟨he, Finset.mem_univ z⟩))
      · intro h q hq
        exact (zeroRead_iff_conv_zero d q.1 q.2).mpr (h q.1 (Finset.mem_product.mp hq).1 q.2)
    rw [h1]
    have h2 : (∀ e ∈ M, ∀ z : Word r, conv e (fun x => toZ11 (d x)) z = 0) ↔
        ∀ e ∈ M, ∀ ξ : Word r, eig e ξ * wht (fun x => toZ11 (d x)) ξ = 0 := by
      refine forall₂_congr (fun e _ => ?_)
      constructor
      · intro hz ξ
        have hfun : conv e (fun x => toZ11 (d x)) = fun _ => 0 := funext hz
        rw [← wht_conv, hfun]
        simp [wht]
      · intro hξ z
        have hfun : wht (conv e (fun x => toZ11 (d x))) = fun _ => 0 := by
          funext ξ; rw [wht_conv]; exact hξ ξ
        have hinv : conv e (fun x => toZ11 (d x)) = iwht (fun _ => 0) := by
          rw [← iwht_wht (conv e (fun x => toZ11 (d x))), hfun]
        rw [hinv]; simp [iwht]
    rw [h2]
    have hphi : φ d = wht (fun x => toZ11 (d x)) := rfl
    rw [hphi]
    constructor
    · intro h ξ hnotK
      simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnotK
      have hex : ∃ e : Kind r, (∀ j : Fin r, (ξ j = 0 → j ∈ e) ∧ (ξ j ∈ only1Set → j ∉ e)) ∧ e ∉ U := by
        by_contra hno
        apply hnotK
        intro e he
        by_contra hnu
        exact hno ⟨e, he, hnu⟩
      rcases hex with ⟨e, he, hnu⟩
      have heM : e ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hnu⟩
      have hmul0 := h e heM ξ
      have heig : eig e ξ ≠ 0 := (eig_ne_zero_iff e ξ).mpr he
      exact (mul_eq_zero.mp hmul0).resolve_left heig
    · intro h e heM ξ
      by_cases heig : eig e ξ = 0
      · rw [heig, zero_mul]
      · have hnotK : ξ ∉ killSet U := by
          intro hK
          simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and] at hK
          exact (Finset.mem_sdiff.mp heM).2 (hK e ((eig_ne_zero_iff e ξ).mp heig))
        rw [h ξ hnotK, mul_zero]
  have hcard_eq : K_dom.card = K_hat.card := by
    refine Finset.card_bij (fun d _ => φ d) ?_ ?_ ?_
    · intro d hd; exact (hmem_iff d).mp hd
    · intro d1 _ d2 _ h; exact φ.injective h
    · intro g hg
      refine ⟨φ.symm g, ?_, φ.apply_symm_apply g⟩
      rw [hmem_iff, φ.apply_symm_apply]; exact hg
  rw [hcard_eq]
  -- Count K_hat via bijection with (killSet U → ZMod 11)
  have hcard_hat : K_hat.card = Fintype.card (↥(killSet U) → ZMod 11) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun g _ => fun ξ : ↥(killSet U) => g ξ.1)
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro g1 hg1 g2 hg2 hEq
      have h1 := (Finset.mem_filter.mp hg1).2
      have h2 := (Finset.mem_filter.mp hg2).2
      funext ξ
      by_cases hξ : ξ ∈ killSet U
      · exact congrFun hEq ⟨ξ, hξ⟩
      · rw [h1 ξ hξ, h2 ξ hξ]
    · intro f _
      refine ⟨fun ξ => if h : ξ ∈ killSet U then f ⟨ξ, h⟩ else 0, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ξ hnot => by simp [hnot]⟩
      · funext ⟨ξ, hξ⟩; simp [hξ]
  rw [hcard_hat, Fintype.card_fun, Fintype.card_coe, ZMod.card]

def goodPairs {r : Nat} (V : Finset (Kind r)) : Finset (Kind r × Kind r) :=
  (Finset.univ : Finset (Kind r × Kind r)).filter (fun p =>
    p.1 ⊆ p.2 ∧ ∀ v : Kind r, p.1 ⊆ v → v ⊆ p.2 → v ∈ V)

def lossV {r : Nat} (V : Finset (Kind r)) : Nat :=
  (goodPairs V).sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card)

def complF {r : Nat} (e : Kind r) : Kind r := (Finset.univ : Finset (Fin r)) \ e

lemma complF_invol {r : Nat} (e : Kind r) : complF (complF e) = e := by
  ext j; simp [complF]

lemma complF_inj {r : Nat} : Function.Injective (@complF r) := by
  intro a b h; rw [← complF_invol a, ← complF_invol b, h]

lemma killSet_card_eq_lossV {r : Nat} (U : Finset (Kind r)) :
    (killSet U).card = lossV (U.image complF) := by
  let V := U.image complF
  let BOf : Word r → Kind r := fun ξ => Finset.univ.filter (fun j => ξ j ∈ only1Set)
  let SOf : Word r → Kind r := fun ξ => Finset.univ.filter (fun j => ξ j ≠ 0)
  have hBS_sub : ∀ ξ : Word r, BOf ξ ⊆ SOf ξ := by
    intro ξ j hj
    have h1 : ξ j ∈ only1Set := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
    intro h0; rw [h0] at h1; exact zero_notMem_only1 h1
  have hkill_iff : ∀ ξ : Word r, ξ ∈ killSet U ↔ (BOf ξ, SOf ξ) ∈ goodPairs V := by
    intro ξ
    simp only [killSet, goodPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨hBS_sub ξ, fun v hBv hvS => ?_⟩
      have heU : complF v ∈ U := by
        apply h (complF v)
        intro j
        constructor
        · intro h0
          have hjS : j ∉ SOf ξ := by simp [SOf, h0]
          have hjv : j ∉ v := fun hv => hjS (hvS hv)
          simp [complF, hjv]
        · intro h1
          have hjB : j ∈ BOf ξ := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1⟩
          have hjv : j ∈ v := hBv hjB
          simp [complF, hjv]
      exact Finset.mem_image.mpr ⟨complF v, heU, complF_invol v⟩
    · rintro ⟨_, hvV⟩ e he
      have hv_in : complF e ∈ V := by
        apply hvV (complF e)
        · intro j hjB
          have h1 : ξ j ∈ only1Set := (Finset.mem_filter.mp hjB).2
          simp [complF, (he j).2 h1]
        · intro j hjc
          have hne : j ∉ e := (Finset.mem_sdiff.mp hjc).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
          intro h0; exact hne ((he j).1 h0)
      rcases Finset.mem_image.mp hv_in with ⟨e', he'U, he'eq⟩
      rwa [← complF_inj he'eq]
  have hpart : (killSet U).card =
      (goodPairs V).sum (fun p => ((killSet U).filter (fun ξ => (BOf ξ, SOf ξ) = p)).card) := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext ξ
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hξ; exact ⟨(BOf ξ, SOf ξ), (hkill_iff ξ).mp hξ, hξ, rfl⟩
      · rintro ⟨_, _, hξ, _⟩; exact hξ
    · intro p1 _ p2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro ξ h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart, lossV]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp_sub : p.1 ⊆ p.2 := (Finset.mem_filter.mp hp).2.1
  let allowed : Fin r → Finset (Fin 16) := fun j =>
    if j ∈ p.1 then only1Set else if j ∈ p.2 then neitherSet else {0}
  have hfilt_eq : (killSet U).filter (fun ξ => (BOf ξ, SOf ξ) = p) =
      Fintype.piFinset allowed := by
    ext ξ
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨_, hEq⟩ j
      have hB : BOf ξ = p.1 := congrArg Prod.fst hEq
      have hS : SOf ξ = p.2 := congrArg Prod.snd hEq
      dsimp only [allowed]
      by_cases h1 : j ∈ p.1
      · rw [if_pos h1, ← hB] at *; exact (Finset.mem_filter.mp h1).2
      · rw [if_neg h1]
        by_cases h2 : j ∈ p.2
        · rw [if_pos h2]
          rw [mem_neither_iff]
          have hjS_mem : j ∈ SOf ξ := by rwa [hS]
          have hjS : ξ j ≠ 0 := (Finset.mem_filter.mp hjS_mem).2
          have hjB : ξ j ∉ only1Set := by
            intro hmem
            exact h1 (hB ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩)
          exact ⟨hjS, hjB⟩
        · rw [if_neg h2, Finset.mem_singleton]
          by_contra hnz
          exact h2 (hS ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnz⟩)
    · intro hall
      have hB : BOf ξ = p.1 := by
        ext j; simp only [BOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hj := hall j
        dsimp only [allowed] at hj
        by_cases h1 : j ∈ p.1
        · rw [if_pos h1] at hj; simp [h1, hj]
        · rw [if_neg h1] at hj
          by_cases h2 : j ∈ p.2
          · rw [if_pos h2, mem_neither_iff] at hj; simp [h1, hj.2]
          · rw [if_neg h2, Finset.mem_singleton] at hj; rw [hj]; simp [h1, zero_notMem_only1]
      have hS : SOf ξ = p.2 := by
        ext j; simp only [SOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hj := hall j
        dsimp only [allowed] at hj
        by_cases h1 : j ∈ p.1
        · rw [if_pos h1] at hj
          have h2 : j ∈ p.2 := hp_sub h1
          have hnz : ξ j ≠ 0 := fun h0 => zero_notMem_only1 (h0 ▸ hj)
          simp [h2, hnz]
        · rw [if_neg h1] at hj
          by_cases h2 : j ∈ p.2
          · rw [if_pos h2, mem_neither_iff] at hj; simp [h2, hj.1]
          · rw [if_neg h2, Finset.mem_singleton] at hj; simp [h2, hj]
      have hpair : (BOf ξ, SOf ξ) = p := Prod.ext hB hS
      exact ⟨(hkill_iff ξ).mpr (hpair.symm ▸ hp), hpair⟩
  rw [hfilt_eq, Fintype.card_piFinset]
  have hprod_split : (∏ j : Fin r, (allowed j).card) =
      (∏ j ∈ p.1, (allowed j).card) * (∏ j ∈ p.2 \ p.1, (allowed j).card) *
      (∏ j ∈ (Finset.univ : Finset (Fin r)) \ p.2, (allowed j).card) := by
    have hdisj1 : Disjoint p.1 (p.2 \ p.1) := Finset.disjoint_sdiff
    have hu1 : p.1 ∪ (p.2 \ p.1) = p.2 := Finset.union_sdiff_of_subset hp_sub
    have hdisj2 : Disjoint p.2 ((Finset.univ : Finset (Fin r)) \ p.2) := Finset.disjoint_sdiff
    have hu2 : p.2 ∪ ((Finset.univ : Finset (Fin r)) \ p.2) = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ p.2)
    rw [← Finset.prod_union hdisj1, hu1, ← Finset.prod_union hdisj2, hu2]
  rw [hprod_split]
  have hp1 : ∏ j ∈ p.1, (allowed j).card = 6 ^ p.1.card := by
    have h : ∀ j ∈ p.1, (allowed j).card = 6 := by
      intro j hj; simp [allowed, hj, only1Set_card]
    rw [Finset.prod_congr rfl h, Finset.prod_const]
  have hp2 : ∏ j ∈ p.2 \ p.1, (allowed j).card = 9 ^ (p.2 \ p.1).card := by
    have h : ∀ j ∈ p.2 \ p.1, (allowed j).card = 9 := by
      intro j hj
      have hj2 := (Finset.mem_sdiff.mp hj).1
      have hj1 := (Finset.mem_sdiff.mp hj).2
      simp [allowed, hj1, hj2, neitherSet_card]
    rw [Finset.prod_congr rfl h, Finset.prod_const]
  have hp3 : ∏ j ∈ (Finset.univ : Finset (Fin r)) \ p.2, (allowed j).card = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hj2 := (Finset.mem_sdiff.mp hj).2
    have hj1 : j ∉ p.1 := fun h => hj2 (hp_sub h)
    simp [allowed, hj1, hj2]
  rw [hp1, hp2, hp3, mul_one]

-- ============================================================
-- Section 4: Master 4-layer lower bound on lossV V
-- ============================================================

lemma lossV_four_layer_bound {r : Nat} (V : Finset (Kind r)) :
    let c0 := if (∅ : Kind r) ∈ V then 1 else 0
    let U1 := (Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V)
    let D2 := V.filter (fun s => s.card = 2)
    let D2_0 := D2.filter (fun s => (s ∩ U1).card = 0)
    let D2_1 := D2.filter (fun s => (s ∩ U1).card = 1)
    let D2_2 := D2.filter (fun s => (s ∩ U1).card = 2)
    let T3 := V.filter (fun s => 3 ≤ s.card)
    c0 + U1.card + D2_0.card + D2_1.card + D2_2.card + T3.card = V.card ∧
    2 * D2_0.card ≤ (r - U1.card) * (r - U1.card - 1) ∧
    D2_1.card ≤ (r - U1.card) * U1.card ∧
    2 * D2_2.card ≤ U1.card * (U1.card - 1) ∧
    (r ≤ 2 → T3.card = 0) ∧
    c0 * (1 + 9 * U1.card) + 6 * U1.card + 36 * D2_0.card + 90 * D2_1.card +
      (144 + 81 * c0) * D2_2.card + 216 * T3.card ≤ lossV V := by
  intro c0 U1 D2 D2_0 D2_1 D2_2 T3
  let K := (Finset.univ : Finset (Fin r)) \ U1
  have hKcard : K.card = r - U1.card := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ U1)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h
  -- Partition of D2 by (s ∩ U1).card ∈ {0, 1, 2}
  have hD2_part : D2 = D2_0 ∪ D2_1 ∪ D2_2 := by
    ext s; simp only [D2_0, D2_1, D2_2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hs
      have hle2 : (s ∩ U1).card ≤ 2 := by
        have h1 := Finset.card_le_card (Finset.inter_subset_left (s₁ := s) (s₂ := U1))
        have h2 := (Finset.mem_filter.mp hs).2
        omega
      have hc : (s ∩ U1).card = 0 ∨ (s ∩ U1).card = 1 ∨ (s ∩ U1).card = 2 := by omega
      rcases hc with h | h | h
      · exact Or.inl (Or.inl ⟨hs, h⟩)
      · exact Or.inl (Or.inr ⟨hs, h⟩)
      · exact Or.inr ⟨hs, h⟩
    · rintro ((⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩) <;> exact hs
  have hD2_card : D2_0.card + D2_1.card + D2_2.card = D2.card := by
    have hd01 : Disjoint D2_0 D2_1 := by
      rw [Finset.disjoint_left]; intro s h0 h1
      have a := (Finset.mem_filter.mp h0).2; have b := (Finset.mem_filter.mp h1).2; omega
    have hd012 : Disjoint (D2_0 ∪ D2_1) D2_2 := by
      rw [Finset.disjoint_left]; intro s h01 h2
      have b := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h01 with h0 | h1
      · have a := (Finset.mem_filter.mp h0).2; omega
      · have a := (Finset.mem_filter.mp h1).2; omega
    rw [hD2_part, Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01]
  -- Partition of V into V0, V1, D2, T3
  let V0 := V.filter (fun s => s.card = 0)
  let V1 := V.filter (fun s => s.card = 1)
  have hV0_card : V0.card = c0 := by
    dsimp only [c0]
    by_cases h0 : (∅ : Kind r) ∈ V
    · rw [if_pos h0]
      have hEq : V0 = {∅} := by
        ext s; simp only [V0, Finset.mem_filter, Finset.mem_singleton, Finset.card_eq_zero]
        exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ h0, h⟩⟩
      rw [hEq, Finset.card_singleton]
    · rw [if_neg h0]
      have hEq : V0 = ∅ := by
        ext s; simp only [V0, Finset.mem_filter, Finset.notMem_empty, iff_false, Finset.card_eq_zero]
        rintro ⟨hs, rfl⟩; exact h0 hs
      rw [hEq, Finset.card_empty]
  have hV1_card : V1.card = U1.card := by
    have hEq : V1 = U1.image (fun i => ({i} : Kind r)) := by
      ext s; simp only [V1, U1, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hsV, hsc⟩
        rcases Finset.card_eq_one.mp hsc with ⟨i, rfl⟩
        exact ⟨i, hsV, rfl⟩
      · rintro ⟨i, hiV, rfl⟩
        exact ⟨hiV, Finset.card_singleton i⟩
    rw [hEq, Finset.card_image_of_injective _ Finset.singleton_injective]
  have hV_sum : c0 + U1.card + D2_0.card + D2_1.card + D2_2.card + T3.card = V.card := by
    have hpartV : V = V0 ∪ V1 ∪ D2 ∪ T3 := by
      ext s; simp only [V0, V1, D2, T3, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hs
        have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ 3 ≤ s.card := by omega
        rcases hc with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hs, h⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hs, h⟩))
        · exact Or.inl (Or.inr ⟨hs, h⟩)
        · exact Or.inr ⟨hs, h⟩
      · rintro (((⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩) | ⟨hs, _⟩) <;> exact hs
    have hd1 : Disjoint V0 V1 := by
      rw [Finset.disjoint_left]; intro s h0 h1
      have a := (Finset.mem_filter.mp h0).2; have b := (Finset.mem_filter.mp h1).2; omega
    have hd2 : Disjoint (V0 ∪ V1) D2 := by
      rw [Finset.disjoint_left]; intro s h01 h2
      have b := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h01 with h0 | h1
      · have a := (Finset.mem_filter.mp h0).2; omega
      · have a := (Finset.mem_filter.mp h1).2; omega
    have hd3 : Disjoint (V0 ∪ V1 ∪ D2) T3 := by
      rw [Finset.disjoint_left]; intro s h012 h3
      have b := (Finset.mem_filter.mp h3).2
      rcases Finset.mem_union.mp h012 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · have a := (Finset.mem_filter.mp h0).2; omega
        · have a := (Finset.mem_filter.mp h1).2; omega
      · have a := (Finset.mem_filter.mp h2).2; omega
    have hcV : V.card = V0.card + V1.card + D2.card + T3.card := by
      conv_lhs => rw [hpartV]
      rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
          Finset.card_union_of_disjoint hd1]
    omega
  -- Bounds on D2_0, D2_1, D2_2, T3
  have hD2_0_bd : 2 * D2_0.card ≤ (r - U1.card) * (r - U1.card - 1) := by
    have hsub : D2_0 ⊆ K.powersetCard 2 := by
      intro s hs
      have hs2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
      have hinter0 := (Finset.mem_filter.mp hs).2
      refine Finset.mem_powersetCard.mpr ⟨?_, hs2⟩
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun hiU => ?_⟩
      have hpos : 0 < (s ∩ U1).card := Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hi, hiU⟩⟩
      omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_powersetCard, hKcard, Nat.choose_two_right] at hc
    omega
  have hD2_1_bd : D2_1.card ≤ (r - U1.card) * U1.card := by
    have hsub : D2_1 ⊆ (K ×ˢ U1).image (fun p => ({p.1, p.2} : Kind r)) := by
      intro s hs
      have hs2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
      have hinter1 := (Finset.mem_filter.mp hs).2
      rcases Finset.card_eq_one.mp hinter1 with ⟨a, ha_eq⟩
      have ha_in : a ∈ s ∩ U1 := by rw [ha_eq]; exact Finset.mem_singleton_self a
      have ha_s : a ∈ s := (Finset.mem_inter.mp ha_in).1
      have ha_U : a ∈ U1 := (Finset.mem_inter.mp ha_in).2
      have her1 : (s.erase a).card = 1 := by
        have := Finset.card_erase_add_one ha_s; omega
      rcases Finset.card_eq_one.mp her1 with ⟨k, hk_eq⟩
      have hk_er : k ∈ s.erase a := by rw [hk_eq]; exact Finset.mem_singleton_self k
      have hk_ne : k ≠ a := (Finset.mem_erase.mp hk_er).1
      have hk_s : k ∈ s := (Finset.mem_erase.mp hk_er).2
      have hk_K : k ∈ K := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, fun hkU => ?_⟩
        have : k ∈ s ∩ U1 := Finset.mem_inter.mpr ⟨hk_s, hkU⟩
        rw [ha_eq, Finset.mem_singleton] at this
        exact hk_ne this
      refine Finset.mem_image.mpr ⟨(k, a), Finset.mem_product.mpr ⟨hk_K, ha_U⟩, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact hk_s
        · exact ha_s
      · intro hx
        by_cases hxa : x = a
        · exact Or.inr hxa
        · left
          have : x ∈ s.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
          rwa [hk_eq, Finset.mem_singleton] at this
    have hc := Finset.card_le_card hsub
    have hci := Finset.card_image_le (s := K ×ˢ U1) (f := fun p : Fin r × Fin r => ({p.1, p.2} : Kind r))
    rw [Finset.card_product, hKcard] at hci
    omega
  have hD2_2_bd : 2 * D2_2.card ≤ U1.card * (U1.card - 1) := by
    have hsub : D2_2 ⊆ U1.powersetCard 2 := by
      intro s hs
      have hs2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
      have hinter2 := (Finset.mem_filter.mp hs).2
      have hEq : s ∩ U1 = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      refine Finset.mem_powersetCard.mpr ⟨?_, hs2⟩
      rw [← hEq]; exact Finset.inter_subset_right
    have hc := Finset.card_le_card hsub
    rw [Finset.card_powersetCard, Nat.choose_two_right] at hc
    omega
  have hT3_r2 : r ≤ 2 → T3.card = 0 := by
    intro hr2
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    have h3 := (Finset.mem_filter.mp hs).2
    have hle : s.card ≤ r := by
      have := Finset.card_le_univ s
      simpa using this
    omega
  -- 4 disjoint subfamilies of goodPairs V
  let w : Kind r × Kind r → Nat := fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card
  let P0 : Finset (Kind r × Kind r) := V.image (fun v => (v, v))
  let P1c : Finset (Kind r × Kind r) := if (∅ : Kind r) ∈ V then U1.image (fun i => (∅, {i})) else ∅
  let P1u : Finset (Kind r × Kind r) := D2.biUnion (fun s => (s ∩ U1).image (fun i => ({i}, s)))
  let P2f : Finset (Kind r × Kind r) := if (∅ : Kind r) ∈ V then D2_2.image (fun s => (∅, s)) else ∅
  have hP0_sub : P0 ⊆ goodPairs V := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨v, hvV, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.rfl, fun x h1 h2 => ?_⟩
    rw [Finset.Subset.antisymm h2 h1]; exact hvV
  have hP1c_sub : P1c ⊆ goodPairs V := by
    intro p hp
    dsimp only [P1c] at hp
    split_ifs at hp with h0
    · rcases Finset.mem_image.mp hp with ⟨i, hiU, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.empty_subset _, fun x _ hx => ?_⟩
      rcases Finset.subset_singleton_iff.mp hx with rfl | rfl
      · exact h0
      · exact (Finset.mem_filter.mp hiU).2
    · exact (Finset.notMem_empty p hp).elim
  have hP1u_sub : P1u ⊆ goodPairs V := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨s, hsD, hps⟩
    rcases Finset.mem_image.mp hps with ⟨i, hiSU, rfl⟩
    have hi_s : i ∈ s := (Finset.mem_inter.mp hiSU).1
    have hi_U : i ∈ U1 := (Finset.mem_inter.mp hiSU).2
    have hsV : s ∈ V := (Finset.mem_filter.mp hsD).1
    have hs2 : s.card = 2 := (Finset.mem_filter.mp hsD).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.singleton_subset_iff.mpr hi_s, fun x h1 h2 => ?_⟩
    dsimp only at h1 h2
    have hx_le : x.card ≤ 2 := by have := Finset.card_le_card h2; omega
    have hx_ge : 1 ≤ x.card := by have := Finset.card_le_card h1; rw [Finset.card_singleton] at this; exact this
    have hc : x.card = 1 ∨ x.card = 2 := by omega
    rcases hc with hxc1 | hxc2
    · have hEq : ({i} : Kind r) = x := Finset.eq_of_subset_of_card_le h1 (by simp [hxc1])
      rw [← hEq]; exact (Finset.mem_filter.mp hi_U).2
    · have hEq : x = s := Finset.eq_of_subset_of_card_le h2 (by omega)
      rw [hEq]; exact hsV
  have hP2f_sub : P2f ⊆ goodPairs V := by
    intro p hp
    dsimp only [P2f] at hp
    split_ifs at hp with h0
    · rcases Finset.mem_image.mp hp with ⟨s, hsD2, rfl⟩
      have hsD : s ∈ D2 := (Finset.mem_filter.mp hsD2).1
      have hsV : s ∈ V := (Finset.mem_filter.mp hsD).1
      have hs2 : s.card = 2 := (Finset.mem_filter.mp hsD).2
      have hinter2 : (s ∩ U1).card = 2 := (Finset.mem_filter.mp hsD2).2
      have hsU : s ⊆ U1 := by
        have hEq : s ∩ U1 = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        rw [← hEq]; exact Finset.inter_subset_right
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.empty_subset _, fun x _ hx => ?_⟩
      dsimp only at hx
      have hx_le : x.card ≤ 2 := by have := Finset.card_le_card hx; omega
      have hc : x.card = 0 ∨ x.card = 1 ∨ x.card = 2 := by omega
      rcases hc with hxc0 | hxc1 | hxc2
      · rw [Finset.card_eq_zero.mp hxc0]; exact h0
      · rcases Finset.card_eq_one.mp hxc1 with ⟨i, rfl⟩
        have hi_s : i ∈ s := hx (Finset.mem_singleton_self i)
        exact (Finset.mem_filter.mp (hsU hi_s)).2
      · rw [Finset.eq_of_subset_of_card_le hx (by omega)]; exact hsV
    · exact (Finset.notMem_empty p hp).elim
  -- Disjointness by (p.1.card, p.2.card)
  have hP0_sig : ∀ p ∈ P0, p.1.card = p.2.card := by
    intro p hp; rcases Finset.mem_image.mp hp with ⟨v, _, rfl⟩; rfl
  have hP1c_sig : ∀ p ∈ P1c, p.1.card = 0 ∧ p.2.card = 1 := by
    intro p hp; dsimp only [P1c] at hp
    split_ifs at hp with h0
    · rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩; simp
    · exact (Finset.notMem_empty p hp).elim
  have hP1u_sig : ∀ p ∈ P1u, p.1.card = 1 ∧ p.2.card = 2 := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨s, hsD, hps⟩
    rcases Finset.mem_image.mp hps with ⟨i, _, rfl⟩
    exact ⟨Finset.card_singleton i, (Finset.mem_filter.mp hsD).2⟩
  have hP2f_sig : ∀ p ∈ P2f, p.1.card = 0 ∧ p.2.card = 2 := by
    intro p hp; dsimp only [P2f] at hp
    split_ifs at hp with h0
    · rcases Finset.mem_image.mp hp with ⟨s, hsD2, rfl⟩
      exact ⟨Finset.card_empty, (Finset.mem_filter.mp (Finset.mem_filter.mp hsD2).1).2⟩
    · exact (Finset.notMem_empty p hp).elim
  have hd_0_1c : Disjoint P0 P1c := by
    rw [Finset.disjoint_left]; intro p h1 h2
    have a := hP0_sig p h1; have b := hP1c_sig p h2; omega
  have hd_01c_1u : Disjoint (P0 ∪ P1c) P1u := by
    rw [Finset.disjoint_left]; intro p h1 h2
    have b := hP1u_sig p h2
    rcases Finset.mem_union.mp h1 with h0 | hc
    · have a := hP0_sig p h0; omega
    · have a := hP1c_sig p hc; omega
  have hd_01c1u_2f : Disjoint (P0 ∪ P1c ∪ P1u) P2f := by
    rw [Finset.disjoint_left]; intro p h1 h2
    have b := hP2f_sig p h2
    rcases Finset.mem_union.mp h1 with h01 | hu
    · rcases Finset.mem_union.mp h01 with h0 | hc
      · have a := hP0_sig p h0; omega
      · have a := hP1c_sig p hc; omega
    · have a := hP1u_sig p hu; omega
  have hall_sub : P0 ∪ P1c ∪ P1u ∪ P2f ⊆ goodPairs V :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset hP0_sub hP1c_sub) hP1u_sub) hP2f_sub
  have hsum_le : P0.sum w + P1c.sum w + P1u.sum w + P2f.sum w ≤ lossV V := by
    have h1 := Finset.sum_le_sum_of_subset (f := w) hall_sub
    rw [Finset.sum_union hd_01c1u_2f, Finset.sum_union hd_01c_1u, Finset.sum_union hd_0_1c] at h1
    exact h1
  -- Evaluate each of the 4 sums!
  have hP0_sum : c0 + 6 * U1.card + 36 * D2.card + 216 * T3.card ≤ P0.sum w := by
    have hinj : Function.Injective (fun v : Kind r => (v, v)) := fun a b h => congrArg Prod.fst h
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    have hpartV : V = V0 ∪ V1 ∪ D2 ∪ T3 := by
      ext s; simp only [V0, V1, D2, T3, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hs
        have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ 3 ≤ s.card := by omega
        rcases hc with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hs, h⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hs, h⟩))
        · exact Or.inl (Or.inr ⟨hs, h⟩)
        · exact Or.inr ⟨hs, h⟩
      · rintro (((⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩) | ⟨hs, _⟩) <;> exact hs
    have hd1 : Disjoint V0 V1 := by
      rw [Finset.disjoint_left]; intro s h0 h1
      have a := (Finset.mem_filter.mp h0).2; have b := (Finset.mem_filter.mp h1).2; omega
    have hd2 : Disjoint (V0 ∪ V1) D2 := by
      rw [Finset.disjoint_left]; intro s h01 h2
      have b := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h01 with h0 | h1
      · have a := (Finset.mem_filter.mp h0).2; omega
      · have a := (Finset.mem_filter.mp h1).2; omega
    have hd3 : Disjoint (V0 ∪ V1 ∪ D2) T3 := by
      rw [Finset.disjoint_left]; intro s h012 h3
      have b := (Finset.mem_filter.mp h3).2
      rcases Finset.mem_union.mp h012 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · have a := (Finset.mem_filter.mp h0).2; omega
        · have a := (Finset.mem_filter.mp h1).2; omega
      · have a := (Finset.mem_filter.mp h2).2; omega
    conv_rhs => rw [hpartV]
    rw [Finset.sum_union hd3, Finset.sum_union hd2, Finset.sum_union hd1]
    have hs0 : V0.sum (fun v => w (v, v)) = c0 := by
      rw [Finset.sum_congr rfl (fun v hv => show w (v, v) = 1 by simp [w, (Finset.mem_filter.mp hv).2]),
          Finset.sum_const, smul_eq_mul, mul_one, hV0_card]
    have hs1 : V1.sum (fun v => w (v, v)) = 6 * U1.card := by
      rw [Finset.sum_congr rfl (fun v hv => show w (v, v) = 6 by simp [w, (Finset.mem_filter.mp hv).2]),
          Finset.sum_const, smul_eq_mul, hV1_card, mul_comm]
    have hs2 : D2.sum (fun v => w (v, v)) = 36 * D2.card := by
      rw [Finset.sum_congr rfl (fun v hv => show w (v, v) = 36 by simp [w, (Finset.mem_filter.mp hv).2]),
          Finset.sum_const, smul_eq_mul, mul_comm]
    have hs3 : 216 * T3.card ≤ T3.sum (fun v => w (v, v)) := by
      have hge : ∀ v ∈ T3, 216 ≤ w (v, v) := by
        intro v hv
        have h3 := (Finset.mem_filter.mp hv).2
        simp only [w, Finset.sdiff_self, Finset.card_empty, pow_zero, mul_one]
        exact le_trans (by norm_num : 216 ≤ 6 ^ 3) (Nat.pow_le_pow_right (by omega) h3)
      calc 216 * T3.card = T3.sum (fun _ => 216) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ T3.sum (fun v => w (v, v)) := Finset.sum_le_sum hge
    change c0 + 6 * U1.card + 36 * D2.card + 216 * T3.card ≤
      V0.sum (fun v => w (v, v)) + V1.sum (fun v => w (v, v)) + D2.sum (fun v => w (v, v)) + T3.sum (fun v => w (v, v))
    omega
  have hP1c_sum : P1c.sum w = c0 * (9 * U1.card) := by
    dsimp only [P1c, c0]
    by_cases h0 : (∅ : Kind r) ∈ V
    · rw [if_pos h0, if_pos h0, one_mul]
      rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.snd h))]
      rw [Finset.sum_congr rfl (fun i _ => show w (∅, ({i} : Kind r)) = 9 by simp [w]),
          Finset.sum_const, smul_eq_mul, mul_comm]
    · simp [h0]
  have hP1u_sum : P1u.sum w = 54 * D2_1.card + 108 * D2_2.card := by
    have hdisj : Set.PairwiseDisjoint (D2 : Set (Kind r))
        (fun s => (s ∩ U1).image (fun i => (({i} : Kind r), s))) := by
      intro s1 _ s2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p h1 h2
      rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
      exact hne (congrArg Prod.snd hEq).symm
    rw [Finset.sum_biUnion hdisj]
    have hinner : ∀ s ∈ D2, ((s ∩ U1).image (fun i => ({i}, s))).sum w = 54 * (s ∩ U1).card := by
      intro s hs
      rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.fst h))]
      have hterm : ∀ i ∈ s ∩ U1, w ({i}, s) = 54 := by
        intro i hi
        have hs2 : s.card = 2 := (Finset.mem_filter.mp hs).2
        have his : i ∈ s := (Finset.mem_inter.mp hi).1
        have hsd : (s \ {i}).card = 1 := by
          rw [Finset.sdiff_singleton_eq_erase]
          have := Finset.card_erase_add_one his; omega
        simp [w, hsd]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl hinner]
    have hd01 : Disjoint D2_0 D2_1 := by
      rw [Finset.disjoint_left]; intro s h0 h1
      have a := (Finset.mem_filter.mp h0).2; have b := (Finset.mem_filter.mp h1).2; omega
    have hd012 : Disjoint (D2_0 ∪ D2_1) D2_2 := by
      rw [Finset.disjoint_left]; intro s h01 h2
      have b := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h01 with h0 | h1
      · have a := (Finset.mem_filter.mp h0).2; omega
      · have a := (Finset.mem_filter.mp h1).2; omega
    conv_lhs => rw [hD2_part]
    rw [Finset.sum_union hd012, Finset.sum_union hd01]
    have h0 : D2_0.sum (fun s => 54 * (s ∩ U1).card) = 0 := by
      rw [Finset.sum_congr rfl (fun s hs => show 54 * (s ∩ U1).card = 0 by rw [(Finset.mem_filter.mp hs).2]),
          Finset.sum_const_zero]
    have h1 : D2_1.sum (fun s => 54 * (s ∩ U1).card) = 54 * D2_1.card := by
      rw [Finset.sum_congr rfl (fun s hs => show 54 * (s ∩ U1).card = 54 by rw [(Finset.mem_filter.mp hs).2]),
          Finset.sum_const, smul_eq_mul, mul_comm]
    have h2 : D2_2.sum (fun s => 54 * (s ∩ U1).card) = 108 * D2_2.card := by
      rw [Finset.sum_congr rfl (fun s hs => show 54 * (s ∩ U1).card = 108 by rw [(Finset.mem_filter.mp hs).2]),
          Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hP2f_sum : P2f.sum w = 81 * c0 * D2_2.card := by
    dsimp only [P2f, c0]
    by_cases h0 : (∅ : Kind r) ∈ V
    · rw [if_pos h0, if_pos h0, mul_one]
      rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)]
      have hterm : ∀ s ∈ D2_2, w (∅, s) = 81 := by
        intro s hs
        have hs2 : s.card = 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
        simp [w, hs2]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    · simp [h0]
  refine ⟨hV_sum, hD2_0_bd, hD2_1_bd, hD2_2_bd, hT3_r2, ?_⟩
  have hc0_cases : c0 = 0 ∨ c0 = 1 := by dsimp only [c0]; split_ifs <;> simp
  rcases hc0_cases with hc0 | hc0 <;> rw [hc0] at hP0_sum hP1c_sum hP2f_sum ⊢ <;> omega

-- ============================================================
-- Section 5: Pure arithmetic lower bounds for l = r + 1 and l = r + 2
-- ============================================================

lemma lb_r_plus_1 {r : Nat} (V : Finset (Kind r)) (hcard : V.card = r + 1) :
    min (15 * r + 1) (6 * r + 144) ≤ lossV V := by
  have hb := lossV_four_layer_bound V
  rcases hb with ⟨hsum, hd0, hd1, hd2, _, hlb⟩
  set c0 := if (∅ : Kind r) ∈ V then 1 else 0
  set u := ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V)).card
  set D2 := V.filter (fun s => s.card = 2)
  set d0 := (D2.filter (fun s => (s ∩ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))).card = 0)).card
  set d1 := (D2.filter (fun s => (s ∩ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))).card = 1)).card
  set d2 := (D2.filter (fun s => (s ∩ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))).card = 2)).card
  set q := (V.filter (fun s => 3 ≤ s.card)).card
  have hu_le : u ≤ r := by
    have := Finset.card_le_univ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))
    simpa using this
  set t := r - u
  have hc0_cases : c0 = 0 ∨ c0 = 1 := by dsimp only [c0]; split_ifs <;> simp
  rcases hc0_cases with hc0 | hc0
  · rw [hc0] at hsum hlb
    have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t := by omega
    rcases ht_cases with ht | ht | ht | ht | ht
    · rw [ht] at hd0 hd1; simp at hd0 hd1; omega
    · rw [ht] at hd0; simp at hd0; omega
    · rw [ht] at hd0; norm_num at hd0; omega
    · rw [ht] at hd0; norm_num at hd0; omega
    · omega
  · rw [hc0] at hsum hlb
    omega

lemma lb_r_plus_2 {r : Nat} (hr : 2 ≤ r) (V : Finset (Kind r)) (hcard : V.card = r + 2) :
    (if r = 2 then 256 else if r = 3 then 211 else min (15 * r + 121) (6 * r + 192)) ≤ lossV V := by
  have hb := lossV_four_layer_bound V
  rcases hb with ⟨hsum, hd0, hd1, hd2, htr2, hlb⟩
  set c0 := if (∅ : Kind r) ∈ V then 1 else 0
  set u := ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V)).card
  set D2 := V.filter (fun s => s.card = 2)
  set d0 := (D2.filter (fun s => (s ∩ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))).card = 0)).card
  set d1 := (D2.filter (fun s => (s ∩ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))).card = 1)).card
  set d2 := (D2.filter (fun s => (s ∩ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))).card = 2)).card
  set q := (V.filter (fun s => 3 ≤ s.card)).card
  have hu_le : u ≤ r := by
    have := Finset.card_le_univ ((Finset.univ : Finset (Fin r)).filter (fun i => ({i} : Kind r) ∈ V))
    simpa using this
  set t := r - u
  have hc0_cases : c0 = 0 ∨ c0 = 1 := by dsimp only [c0]; split_ifs <;> simp
  by_cases hr2 : r = 2
  · rw [if_pos hr2]
    have hq0 : q = 0 := htr2 (by omega)
    rcases hc0_cases with hc0 | hc0 <;> rw [hc0] at hsum hlb
    · have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      rcases ht_cases with ht | ht | ht
      · rw [ht] at hd0 hd1; simp at hd0 hd1
        have hu2 : u = 2 := by omega
        rw [hu2] at hd2; omega
      · rw [ht] at hd0 hd1; simp at hd0 hd1
        have hu1 : u = 1 := by omega
        rw [hu1] at hd2; simp at hd2; omega
      · rw [ht] at hd0 hd1; norm_num at hd0 hd1
        have hu0 : u = 0 := by omega
        rw [hu0] at hd1 hd2; simp at hd1 hd2; omega
    · have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      rcases ht_cases with ht | ht | ht
      · rw [ht] at hd0 hd1; simp at hd0 hd1; omega
      · rw [ht] at hd0 hd1; simp at hd0 hd1
        have hu1 : u = 1 := by omega
        rw [hu1] at hd2; simp at hd2; omega
      · rw [ht] at hd0; norm_num at hd0
        have hu0 : u = 0 := by omega
        rw [hu0] at hd1 hd2; simp at hd1 hd2; omega
  · rw [if_neg hr2]
    by_cases hr3 : r = 3
    · rw [if_pos hr3]
      rcases hc0_cases with hc0 | hc0 <;> rw [hc0] at hsum hlb
      · have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases ht_cases with ht | ht | ht | ht
        · rw [ht] at hd0 hd1; simp at hd0 hd1; omega
        · rw [ht] at hd0; simp at hd0; omega
        · rw [ht] at hd0; norm_num at hd0; omega
        · rw [ht] at hd0; norm_num at hd0
          have hu0 : u = 0 := by omega
          rw [hu0] at hd1 hd2; simp at hd1 hd2; omega
      · have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases ht_cases with ht | ht | ht | ht
        · rw [ht] at hd0 hd1; simp at hd0 hd1; omega
        · rw [ht] at hd0; simp at hd0; omega
        · rw [ht] at hd0; norm_num at hd0; omega
        · rw [ht] at hd0; norm_num at hd0
          have hu0 : u = 0 := by omega
          rw [hu0] at hd1 hd2; simp at hd1 hd2; omega
    · rw [if_neg hr3]
      rcases hc0_cases with hc0 | hc0 <;> rw [hc0] at hsum hlb
      · have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t := by omega
        rcases ht_cases with ht | ht | ht | ht | ht
        · rw [ht] at hd0 hd1; simp at hd0 hd1; omega
        · rw [ht] at hd0; simp at hd0; omega
        · rw [ht] at hd0; norm_num at hd0; omega
        · rw [ht] at hd0; norm_num at hd0; omega
        · omega
      · have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t := by omega
        rcases ht_cases with ht | ht | ht | ht | ht
        · rw [ht] at hd0 hd1; simp at hd0 hd1; omega
        · rw [ht] at hd0; simp at hd0; omega
        · rw [ht] at hd0; norm_num at hd0; omega
        · rw [ht] at hd0; norm_num at hd0; omega
        · omega

-- ============================================================
-- Section 6: Exact extremizer constructions (upper bounds)
-- ============================================================

lemma witness_r_plus_1_center (r : Nat) :
    ∃ V : Finset (Kind r), V.card = r + 1 ∧ lossV V = 15 * r + 1 := by
  let S1 : Finset (Kind r) := (Finset.univ : Finset (Fin r)).image (fun i => ({i} : Kind r))
  let V : Finset (Kind r) := insert (∅ : Kind r) S1
  have h0_not : (∅ : Kind r) ∉ S1 := by
    intro h; rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    exact Finset.singleton_ne_empty i hi
  have hcardV : V.card = r + 1 := by
    rw [Finset.card_insert_of_notMem h0_not, Finset.card_image_of_injective _ Finset.singleton_injective,
        Finset.card_univ, Fintype.card_fin]
  refine ⟨V, hcardV, ?_⟩
  let P0 : Finset (Kind r × Kind r) := {(∅, ∅)}
  let P1 : Finset (Kind r × Kind r) := (Finset.univ : Finset (Fin r)).image (fun i => (∅, {i}))
  let P2 : Finset (Kind r × Kind r) := (Finset.univ : Finset (Fin r)).image (fun i => ({i}, {i}))
  have hgp : goodPairs V = P0 ∪ P1 ∪ P2 := by
    ext p
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      P0, P1, P2, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ⟨hsub, hall⟩
      have hp2 : p.2 ∈ V := hall p.2 hsub Finset.Subset.rfl
      simp only [V, S1, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp2
      rcases hp2 with h20 | ⟨i, hi⟩
      · have h10 : p.1 = ∅ := Finset.subset_empty.mp (h20 ▸ hsub)
        exact Or.inl (Or.inl (Prod.ext h10 h20))
      · rcases Finset.subset_singleton_iff.mp (hi ▸ hsub) with h10 | h1i
        · exact Or.inl (Or.inr ⟨i, Prod.ext h10.symm hi⟩)
        · exact Or.inr ⟨i, Prod.ext h1i.symm hi⟩
    · rintro ((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine ⟨Finset.Subset.rfl, fun v _ h2 => ?_⟩
        rw [Finset.subset_empty.mp h2]; exact Finset.mem_insert_self _ _
      · refine ⟨Finset.empty_subset _, fun v _ h2 => ?_⟩
        rcases Finset.subset_singleton_iff.mp h2 with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hd01 : Disjoint P0 P1 := by
    rw [Finset.disjoint_left]; intro p h0 h1
    rw [Finset.mem_singleton] at h0; subst h0
    rcases Finset.mem_image.mp h1 with ⟨i, _, hi⟩
    exact Finset.singleton_ne_empty i (congrArg Prod.snd hi)
  have hd012 : Disjoint (P0 ∪ P1) P2 := by
    rw [Finset.disjoint_left]; intro p h01 h2
    rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
    rcases Finset.mem_union.mp h01 with h0 | h1
    · rw [Finset.mem_singleton] at h0
      exact Finset.singleton_ne_empty i (congrArg Prod.fst h0)
    · rcases Finset.mem_image.mp h1 with ⟨j, _, hj⟩
      exact Finset.singleton_ne_empty i (congrArg Prod.fst hj).symm
  rw [lossV, hgp, Finset.sum_union hd012, Finset.sum_union hd01]
  have hs0 : P0.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 1 := by simp [P0]
  have hs1 : P1.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 9 * r := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.snd h))]
    simp [Finset.sum_const, mul_comm]
  have hs2 : P2.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 6 * r := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.fst h))]
    simp [Finset.sum_const, mul_comm]
  omega

lemma witness_r_plus_1_nocenter {r : Nat} (hr : 2 ≤ r) :
    ∃ V : Finset (Kind r), V.card = r + 1 ∧ lossV V = 6 * r + 144 := by
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  let d01 : Kind r := {i0, i1}
  let S1 : Finset (Kind r) := (Finset.univ : Finset (Fin r)).image (fun i => ({i} : Kind r))
  let V : Finset (Kind r) := insert d01 S1
  have hd_not : d01 ∉ S1 := by
    intro h; rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    have hc := congrArg Finset.card hi
    rw [Finset.card_singleton, Finset.card_pair hne] at hc; omega
  have hcardV : V.card = r + 1 := by
    rw [Finset.card_insert_of_notMem hd_not, Finset.card_image_of_injective _ Finset.singleton_injective,
        Finset.card_univ, Fintype.card_fin]
  refine ⟨V, hcardV, ?_⟩
  let P1 : Finset (Kind r × Kind r) := (Finset.univ : Finset (Fin r)).image (fun i => ({i}, {i}))
  let P2 : Finset (Kind r × Kind r) := {(d01, d01), ({i0}, d01), ({i1}, d01)}
  have hgp : goodPairs V = P1 ∪ P2 := by
    ext p
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      P1, P2, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hall⟩
      have hp1 : p.1 ∈ V := hall p.1 Finset.Subset.rfl hsub
      have hp2 : p.2 ∈ V := hall p.2 hsub Finset.Subset.rfl
      have hp1_ne : p.1 ≠ ∅ := by
        intro h0; rw [h0] at hp1
        simp only [V, S1, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp1
        rcases hp1 with hd | ⟨i, hi⟩
        · have := congrArg Finset.card hd; rw [Finset.card_empty, Finset.card_pair hne] at this; omega
        · exact Finset.singleton_ne_empty i hi
      simp only [V, S1, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp2
      rcases hp2 with h2d | ⟨i, hi⟩
      · right
        have hsub' : p.1 ⊆ {i0, i1} := by change p.1 ⊆ d01; rw [← h2d]; exact hsub
        have hcases : p.1 = {i0, i1} ∨ p.1 = {i0} ∨ p.1 = {i1} := by
          by_cases h0 : i0 ∈ p.1 <;> by_cases h1 : i1 ∈ p.1
          · left; apply Finset.Subset.antisymm hsub'
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          · right; left; apply Finset.Subset.antisymm
            · intro x hx
              have := hsub' hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl
              · exact Finset.mem_singleton_self i0
              · exact (h1 hx).elim
            · exact Finset.singleton_subset_iff.mpr h0
          · right; right; apply Finset.Subset.antisymm
            · intro x hx
              have := hsub' hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl
              · exact (h0 hx).elim
              · exact Finset.mem_singleton_self i1
            · exact Finset.singleton_subset_iff.mpr h1
          · exfalso; apply hp1_ne
            apply Finset.subset_empty.mp
            intro x hx
            have := hsub' hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl
            · exact (h0 hx).elim
            · exact (h1 hx).elim
        rcases hcases with h | h | h
        · exact Or.inl (Prod.ext h h2d)
        · exact Or.inr (Or.inl (Prod.ext h h2d))
        · exact Or.inr (Or.inr (Prod.ext h h2d))
      · left
        rcases Finset.subset_singleton_iff.mp (hi ▸ hsub) with h0 | h1
        · exact (hp1_ne h0).elim
        · exact ⟨i, Prod.ext h1.symm hi⟩
    · rintro (⟨i, rfl⟩ | rfl | rfl | rfl)
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]; exact Finset.mem_insert_self _ _
      · refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), fun v h1 h2 => ?_⟩
        by_cases hi1v : i1 ∈ v
        · have hEq : v = d01 := Finset.Subset.antisymm h2 (by
            intro x hx; simp only [d01, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact h1 (Finset.mem_singleton_self i0)
            · exact hi1v)
          rw [hEq]; exact Finset.mem_insert_self _ _
        · have hEq : v = {i0} := Finset.Subset.antisymm (by
            intro x hx
            have := h2 hx; simp only [d01, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl
            · exact Finset.mem_singleton_self i0
            · exact (hi1v hx).elim) h1
          rw [hEq]; exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩)
      · refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
          fun v h1 h2 => ?_⟩
        by_cases hi0v : i0 ∈ v
        · have hEq : v = d01 := Finset.Subset.antisymm h2 (by
            intro x hx; simp only [d01, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hi0v
            · exact h1 (Finset.mem_singleton_self i1))
          rw [hEq]; exact Finset.mem_insert_self _ _
        · have hEq : v = {i1} := Finset.Subset.antisymm (by
            intro x hx
            have := h2 hx; simp only [d01, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl
            · exact (hi0v hx).elim
            · exact Finset.mem_singleton_self i1) h1
          rw [hEq]; exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i1, Finset.mem_univ i1, rfl⟩)
  have hdisj : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    simp only [P2, Finset.mem_insert, Finset.mem_singleton] at h2
    have hcard_snd : ({i} : Kind r).card = 2 := by
      rcases h2 with h | h | h
      · have hs : ({i} : Kind r) = d01 := congrArg Prod.snd h
        rw [hs, Finset.card_pair hne]
      · have hs : ({i} : Kind r) = d01 := congrArg Prod.snd h
        rw [hs, Finset.card_pair hne]
      · have hs : ({i} : Kind r) = d01 := congrArg Prod.snd h
        rw [hs, Finset.card_pair hne]
    simp at hcard_snd
  rw [lossV, hgp, Finset.sum_union hdisj]
  have hs1 : P1.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 6 * r := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.fst h))]
    simp [Finset.sum_const, mul_comm]
  have hne1 : (d01, d01) ≠ (({i0} : Kind r), d01) := by
    intro h; have := congrArg (fun q => q.1.card) h
    simp [d01, Finset.card_pair hne] at this
  have hne2 : (d01, d01) ≠ (({i1} : Kind r), d01) := by
    intro h; have := congrArg (fun q => q.1.card) h
    simp [d01, Finset.card_pair hne] at this
  have hne3 : (({i0} : Kind r), d01) ≠ (({i1} : Kind r), d01) := by
    intro h; exact hne (Finset.singleton_injective (congrArg Prod.fst h))
  have hs2 : P2.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 144 := by
    dsimp only [P2]
    rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
        Finset.sum_singleton]
    have hd01c : d01.card = 2 := Finset.card_pair hne
    have hc1 : (d01 \ {i0}).card = 1 := by
      have : d01 \ {i0} = {i1} := by
        ext x; simp only [d01, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, h⟩
          · exact (h rfl).elim
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, hne.symm⟩
      rw [this, Finset.card_singleton]
    have hc2 : (d01 \ {i1}).card = 1 := by
      have : d01 \ {i1} = {i0} := by
        ext x; simp only [d01, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, h⟩
          · rfl
          · exact (h rfl).elim
        · rintro rfl; exact ⟨Or.inl rfl, hne⟩
      rw [this, Finset.card_singleton]
    simp [hd01c, hc1, hc2]
  rw [hs1, hs2]

lemma witness_r2_l4 :
    ∃ V : Finset (Kind 2), V.card = 4 ∧ lossV V = 256 := by
  refine ⟨Finset.univ, by decide, by decide⟩

lemma witness_r3_l5 :
    ∃ V : Finset (Kind 3), V.card = 5 ∧ lossV V = 211 := by
  refine ⟨{∅, {0}, {1}, {0, 2}, {1, 2}}, by decide, by decide⟩

lemma witness_r_plus_2_center {r : Nat} (hr : 4 ≤ r) :
    ∃ V : Finset (Kind r), V.card = r + 2 ∧ lossV V = 15 * r + 121 := by
  let a0 : Fin r := ⟨0, by omega⟩
  let a1 : Fin r := ⟨1, by omega⟩
  let a2 : Fin r := ⟨2, by omega⟩
  let a3 : Fin r := ⟨3, by omega⟩
  have h01 : a0 ≠ a1 := by intro h; have := congrArg Fin.val h; simp [a0, a1] at this
  have h02 : a0 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a0, a2] at this
  have h03 : a0 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a0, a3] at this
  have h12 : a1 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a1, a2] at this
  have h13 : a1 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a1, a3] at this
  have h23 : a2 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a2, a3] at this
  let K4 : Finset (Fin r) := {a0, a1, a2, a3}
  have hK4_card : K4.card = 4 := by
    simp [K4, h01, h02, h03, h12, h13, h23]
  let Rest : Finset (Fin r) := Finset.univ \ K4
  have hRest_card : Rest.card = r - 4 := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ K4)
    simp only [Finset.card_univ, Fintype.card_fin, hK4_card] at h
    exact h
  let D5 : Finset (Kind r) := (K4.powersetCard 2).erase {a2, a3}
  have h23_in : ({a2, a3} : Kind r) ∈ K4.powersetCard 2 := by
    refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair h23⟩
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [K4]
  have hD5_card : D5.card = 5 := by
    have h1 : D5.card + 1 = (K4.powersetCard 2).card := Finset.card_erase_add_one h23_in
    have h2 : (K4.powersetCard 2).card = 6 := by rw [Finset.card_powersetCard, hK4_card]; decide
    omega
  have hD5_sub : ∀ s ∈ D5, s ⊆ K4 ∧ s.card = 2 :=
    fun s hs => Finset.mem_powersetCard.mp (Finset.mem_erase.mp hs).2
  let S1 : Finset (Kind r) := Rest.image (fun i => ({i} : Kind r))
  let V : Finset (Kind r) := insert (∅ : Kind r) (S1 ∪ D5)
  have hd_S1_D5 : Disjoint S1 D5 := by
    rw [Finset.disjoint_left]; intro s h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    have hc := (hD5_sub {i} h2).2; simp at hc
  have h0_not : (∅ : Kind r) ∉ S1 ∪ D5 := by
    intro h; rcases Finset.mem_union.mp h with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨i, _, hi⟩; exact Finset.singleton_ne_empty i hi
    · have hc := (hD5_sub ∅ h2).2; simp at hc
  have hcardV : V.card = r + 2 := by
    rw [Finset.card_insert_of_notMem h0_not, Finset.card_union_of_disjoint hd_S1_D5,
        Finset.card_image_of_injective _ Finset.singleton_injective, hRest_card, hD5_card]
    omega
  refine ⟨V, hcardV, ?_⟩
  let P0 : Finset (Kind r × Kind r) := {(∅, ∅)}
  let P1 : Finset (Kind r × Kind r) := Rest.image (fun i => (∅, {i}))
  let P2 : Finset (Kind r × Kind r) := Rest.image (fun i => ({i}, {i}))
  let P3 : Finset (Kind r × Kind r) := D5.image (fun s => (s, s))
  have hgp : goodPairs V = P0 ∪ P1 ∪ P2 ∪ P3 := by
    ext p
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      P0, P1, P2, P3, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ⟨hsub, hall⟩
      have hp1 : p.1 ∈ V := hall p.1 Finset.Subset.rfl hsub
      have hp2 : p.2 ∈ V := hall p.2 hsub Finset.Subset.rfl
      simp only [V, S1, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp2
      rcases hp2 with h20 | ⟨i, hiR, hi⟩ | h2D
      · have h10 : p.1 = ∅ := Finset.subset_empty.mp (h20 ▸ hsub)
        exact Or.inl (Or.inl (Or.inl (Prod.ext h10 h20)))
      · rcases Finset.subset_singleton_iff.mp (hi ▸ hsub) with h10 | h1i
        · exact Or.inl (Or.inl (Or.inr ⟨i, hiR, Prod.ext h10.symm hi⟩))
        · exact Or.inl (Or.inr ⟨i, hiR, Prod.ext h1i.symm hi⟩)
      · right
        have hp1_eq : p.1 = p.2 := by
          simp only [V, S1, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp1
          rcases hp1 with h10 | ⟨i, hiR, hi⟩ | h1D
          · exfalso
            have hne : p.2.Nonempty := Finset.card_pos.mp (by rw [(hD5_sub p.2 h2D).2]; omega)
            rcases hne with ⟨x, hxp⟩
            have hxV : ({x} : Kind r) ∈ V := hall {x} (h10.symm ▸ Finset.empty_subset _) (Finset.singleton_subset_iff.mpr hxp)
            simp only [V, S1, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hxV
            rcases hxV with h0 | ⟨j, hjR, hj⟩ | hD
            · exact Finset.singleton_ne_empty x h0
            · have hjx : j = x := Finset.singleton_injective hj
              exact (Finset.mem_sdiff.mp hjR).2 (hjx.symm ▸ (hD5_sub p.2 h2D).1 hxp)
            · have hc := (hD5_sub {x} hD).2; simp at hc
          · exfalso
            have hip : i ∈ p.2 := hsub (hi ▸ Finset.mem_singleton_self i)
            exact (Finset.mem_sdiff.mp hiR).2 ((hD5_sub p.2 h2D).1 hip)
          · exact Finset.eq_of_subset_of_card_le hsub (by rw [(hD5_sub p.1 h1D).2, (hD5_sub p.2 h2D).2])
        exact ⟨p.2, h2D, Prod.ext hp1_eq.symm rfl⟩
    · rintro (((rfl | ⟨i, hiR, rfl⟩) | ⟨i, hiR, rfl⟩) | ⟨s, hsD, rfl⟩)
      · refine ⟨Finset.Subset.rfl, fun v _ h2 => ?_⟩
        rw [Finset.subset_empty.mp h2]; exact Finset.mem_insert_self _ _
      · refine ⟨Finset.empty_subset _, fun v _ h2 => ?_⟩
        rcases Finset.subset_singleton_iff.mp h2 with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiR, rfl⟩))
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiR, rfl⟩))
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hsD)
  have hd01 : Disjoint P0 P1 := by
    rw [Finset.disjoint_left]; intro p h0 h1
    rw [Finset.mem_singleton] at h0; subst h0
    rcases Finset.mem_image.mp h1 with ⟨i, _, hi⟩
    exact Finset.singleton_ne_empty i (congrArg Prod.snd hi)
  have hd012 : Disjoint (P0 ∪ P1) P2 := by
    rw [Finset.disjoint_left]; intro p h01 h2
    rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
    rcases Finset.mem_union.mp h01 with h0 | h1
    · rw [Finset.mem_singleton] at h0; exact Finset.singleton_ne_empty i (congrArg Prod.fst h0)
    · rcases Finset.mem_image.mp h1 with ⟨_, _, hj⟩; exact Finset.singleton_ne_empty i (congrArg Prod.fst hj).symm
  have hd0123 : Disjoint (P0 ∪ P1 ∪ P2) P3 := by
    rw [Finset.disjoint_left]; intro p h012 h3
    rcases Finset.mem_image.mp h3 with ⟨s, hsD, rfl⟩
    have hs2 := (hD5_sub s hsD).2
    rcases Finset.mem_union.mp h012 with h01 | h2
    · rcases Finset.mem_union.mp h01 with h0 | h1
      · rw [Finset.mem_singleton] at h0; have := congrArg (fun q => q.2.card) h0; simp [hs2] at this
      · rcases Finset.mem_image.mp h1 with ⟨_, _, hj⟩; have := congrArg (fun q => q.2.card) hj; simp [hs2] at this
    · rcases Finset.mem_image.mp h2 with ⟨_, _, hj⟩; have := congrArg (fun q => q.2.card) hj; simp [hs2] at this
  rw [lossV, hgp, Finset.sum_union hd0123, Finset.sum_union hd012, Finset.sum_union hd01]
  have hs0 : P0.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 1 := by simp [P0]
  have hs1 : P1.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 9 * (r - 4) := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.snd h))]
    simp [Finset.sum_const, hRest_card, mul_comm]
  have hs2 : P2.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 6 * (r - 4) := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.fst h))]
    simp [Finset.sum_const, hRest_card, mul_comm]
  have hs3 : P3.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 180 := by
    rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)]
    rw [Finset.sum_congr rfl (fun s hs => show 6 ^ s.card * 9 ^ (s \ s).card = 36 by simp [(hD5_sub s hs).2]),
        Finset.sum_const, smul_eq_mul, hD5_card]
  omega

lemma witness_r_plus_2_nocenter {r : Nat} (hr : 4 ≤ r) :
    ∃ V : Finset (Kind r), V.card = r + 2 ∧ lossV V = 6 * r + 192 := by
  let a0 : Fin r := ⟨0, by omega⟩
  let a1 : Fin r := ⟨1, by omega⟩
  let a2 : Fin r := ⟨2, by omega⟩
  let a3 : Fin r := ⟨3, by omega⟩
  have h01 : a0 ≠ a1 := by intro h; have := congrArg Fin.val h; simp [a0, a1] at this
  have h02 : a0 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a0, a2] at this
  have h03 : a0 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a0, a3] at this
  have h12 : a1 ≠ a2 := by intro h; have := congrArg Fin.val h; simp [a1, a2] at this
  have h13 : a1 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a1, a3] at this
  have h23 : a2 ≠ a3 := by intro h; have := congrArg Fin.val h; simp [a2, a3] at this
  let K4 : Finset (Fin r) := {a0, a1, a2, a3}
  have hK4_card : K4.card = 4 := by simp [K4, h01, h02, h03, h12, h13, h23]
  let Rest : Finset (Fin r) := Finset.univ \ K4
  have hRest_card : Rest.card = r - 4 := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ K4)
    simp only [Finset.card_univ, Fintype.card_fin, hK4_card] at h
    exact h
  let D6 : Finset (Kind r) := K4.powersetCard 2
  have hD6_card : D6.card = 6 := by
    rw [Finset.card_powersetCard, hK4_card]; decide
  have hD6_sub : ∀ s ∈ D6, s ⊆ K4 ∧ s.card = 2 := fun s hs => Finset.mem_powersetCard.mp hs
  let S1 : Finset (Kind r) := Rest.image (fun i => ({i} : Kind r))
  let V : Finset (Kind r) := S1 ∪ D6
  have hd_S1_D6 : Disjoint S1 D6 := by
    rw [Finset.disjoint_left]; intro s h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    have hc := (hD6_sub {i} h2).2; simp at hc
  have hcardV : V.card = r + 2 := by
    rw [Finset.card_union_of_disjoint hd_S1_D6,
        Finset.card_image_of_injective _ Finset.singleton_injective, hRest_card, hD6_card]
    omega
  refine ⟨V, hcardV, ?_⟩
  let P1 : Finset (Kind r × Kind r) := Rest.image (fun i => ({i}, {i}))
  let P2 : Finset (Kind r × Kind r) := D6.image (fun s => (s, s))
  have hgp : goodPairs V = P1 ∪ P2 := by
    ext p
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      P1, P2, Finset.mem_image]
    constructor
    · rintro ⟨hsub, hall⟩
      have hp1 : p.1 ∈ V := hall p.1 Finset.Subset.rfl hsub
      have hp2 : p.2 ∈ V := hall p.2 hsub Finset.Subset.rfl
      have hp1_ne : p.1 ≠ ∅ := by
        intro h0; rw [h0] at hp1
        rcases Finset.mem_union.mp hp1 with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨i, _, hi⟩; exact Finset.singleton_ne_empty i hi
        · have hc := (hD6_sub ∅ h2).2; simp at hc
      rcases Finset.mem_union.mp hp2 with h21 | h22
      · rcases Finset.mem_image.mp h21 with ⟨i, hiR, hi⟩
        rcases Finset.subset_singleton_iff.mp (hi ▸ hsub) with h0 | h1
        · exact (hp1_ne h0).elim
        · exact Or.inl ⟨i, hiR, Prod.ext h1.symm hi⟩
      · right
        have hp1_eq : p.1 = p.2 := by
          rcases Finset.mem_union.mp hp1 with h11 | h12
          · rcases Finset.mem_image.mp h11 with ⟨i, hiR, hi⟩
            have hip : i ∈ p.2 := hsub (hi ▸ Finset.mem_singleton_self i)
            exact ((Finset.mem_sdiff.mp hiR).2 ((hD6_sub p.2 h22).1 hip)).elim
          · exact Finset.eq_of_subset_of_card_le hsub (by rw [(hD6_sub p.1 h12).2, (hD6_sub p.2 h22).2])
        exact ⟨p.2, h22, Prod.ext hp1_eq.symm rfl⟩
    · rintro (⟨i, hiR, rfl⟩ | ⟨s, hsD, rfl⟩)
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiR, rfl⟩)
      · refine ⟨Finset.Subset.rfl, fun v h1 h2 => ?_⟩
        rw [Finset.Subset.antisymm h2 h1]
        exact Finset.mem_union_right _ hsD
  have hdisj : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨s, hsD, hs⟩
    have hc := congrArg (fun q => q.1.card) hs
    simp [(hD6_sub s hsD).2] at hc
  rw [lossV, hgp, Finset.sum_union hdisj]
  have hs1 : P1.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 6 * (r - 4) := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective (congrArg Prod.fst h))]
    simp [Finset.sum_const, hRest_card, mul_comm]
  have hs2 : P2.sum (fun p => 6 ^ p.1.card * 9 ^ (p.2 \ p.1).card) = 216 := by
    rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)]
    rw [Finset.sum_congr rfl (fun s hs => show 6 ^ s.card * 9 ^ (s \ s).card = 36 by simp [(hD6_sub s hs).2]),
        Finset.sum_const, smul_eq_mul, hD6_card]
  omega

lemma exists_compl_of_V {r l loss : Nat} (h : ∃ V : Finset (Kind r), V.card = l ∧ lossV V = loss) :
    ∃ U : Finset (Kind r), U.card = l ∧ lossV (U.image complF) = loss := by
  rcases h with ⟨V, hcard, hloss⟩
  refine ⟨V.image complF, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ complF_inj]; exact hcard
  · have hEq : (V.image complF).image complF = V := by
      ext x; simp only [Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rwa [complF_invol]
      · intro hx; exact ⟨complF x, ⟨x, hx, rfl⟩, complF_invol x⟩
    rw [hEq]; exact hloss

end PEqualNP.Outside.L_lib_1168_aux

theorem PEqualNP.Outside.L_lib_1168 : ∀ r : Nat,
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let zeroRead := fun (d : Word → Fin 11) (q : Kind × Word) =>
    ((cube.filter (fun x => pass q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0
  let kernelSize := fun (M : Finset Kind) =>
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product cube, zeroRead d q)).card
  let minimumAt := fun (l loss : Nat) =>
    (∀ U : Finset Kind, U.card = l → 11 ^ loss ≤ kernelSize (kinds \ U)) ∧
    ∃ U : Finset Kind, U.card = l ∧ kernelSize (kinds \ U) = 11 ^ loss
  minimumAt (r + 1) (min (15 * r + 1) (6 * r + 144)) ∧
    (2 ≤ r → minimumAt (r + 2)
      (if r = 2 then 256 else if r = 3 then 211 else min (15 * r + 121) (6 * r + 192))) := by
  intro r
  dsimp only
  have hker : ∀ U : Finset (Finset (Fin r)),
      ((Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
        ∀ q ∈ ((Finset.univ : Finset (Finset (Fin r))) \ U).product (Finset.univ : Finset (Fin r → Fin 16)),
          (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x =>
            (Finset.univ : Finset (Fin r)).toList.all (fun j =>
              let w := (q.2 j).val ^^^ (x j).val
              (w &&& 3) != 0 && (w &&& 13) != (if j ∈ q.1 then 1 else 0)))).sum (fun x => (d x).val)) % 11 = 0)).card =
      11 ^ PEqualNP.Outside.L_lib_1168_aux.lossV (U.image PEqualNP.Outside.L_lib_1168_aux.complF) := by
    intro U
    exact (PEqualNP.Outside.L_lib_1168_aux.kernelSize_eq_eleven_pow_kill U).trans
      (by rw [PEqualNP.Outside.L_lib_1168_aux.killSet_card_eq_lossV U])
  constructor
  · constructor
    · intro U hU
      rw [hker U]
      have hVcard : (U.image PEqualNP.Outside.L_lib_1168_aux.complF).card = r + 1 := by
        rw [Finset.card_image_of_injective _ PEqualNP.Outside.L_lib_1168_aux.complF_inj]; exact hU
      exact Nat.pow_le_pow_right (by omega)
        (PEqualNP.Outside.L_lib_1168_aux.lb_r_plus_1 _ hVcard)
    · by_cases hcmp : 15 * r + 1 ≤ 6 * r + 144
      · rcases PEqualNP.Outside.L_lib_1168_aux.exists_compl_of_V
          (PEqualNP.Outside.L_lib_1168_aux.witness_r_plus_1_center r) with ⟨U, hU, hloss⟩
        refine ⟨U, hU, ?_⟩
        rw [hker U, hloss, min_eq_left hcmp]
      · rcases PEqualNP.Outside.L_lib_1168_aux.exists_compl_of_V
          (PEqualNP.Outside.L_lib_1168_aux.witness_r_plus_1_nocenter (r := r) (by omega)) with ⟨U, hU, hloss⟩
        refine ⟨U, hU, ?_⟩
        rw [hker U, hloss, min_eq_right (by omega)]
  · intro hr
    constructor
    · intro U hU
      rw [hker U]
      have hVcard : (U.image PEqualNP.Outside.L_lib_1168_aux.complF).card = r + 2 := by
        rw [Finset.card_image_of_injective _ PEqualNP.Outside.L_lib_1168_aux.complF_inj]; exact hU
      exact Nat.pow_le_pow_right (by omega)
        (PEqualNP.Outside.L_lib_1168_aux.lb_r_plus_2 hr _ hVcard)
    · by_cases hr2 : r = 2
      · subst hr2
        rcases PEqualNP.Outside.L_lib_1168_aux.exists_compl_of_V
          PEqualNP.Outside.L_lib_1168_aux.witness_r2_l4 with ⟨U, hU, hloss⟩
        refine ⟨U, hU, ?_⟩
        rw [hker U, hloss]; simp
      · by_cases hr3 : r = 3
        · subst hr3
          rcases PEqualNP.Outside.L_lib_1168_aux.exists_compl_of_V
            PEqualNP.Outside.L_lib_1168_aux.witness_r3_l5 with ⟨U, hU, hloss⟩
          refine ⟨U, hU, ?_⟩
          rw [hker U, hloss]; simp
        · by_cases hcmp : 15 * r + 121 ≤ 6 * r + 192
          · rcases PEqualNP.Outside.L_lib_1168_aux.exists_compl_of_V
              (PEqualNP.Outside.L_lib_1168_aux.witness_r_plus_2_center (r := r) (by omega)) with ⟨U, hU, hloss⟩
            refine ⟨U, hU, ?_⟩
            rw [hker U, hloss, if_neg hr2, if_neg hr3, min_eq_left hcmp]
          · rcases PEqualNP.Outside.L_lib_1168_aux.exists_compl_of_V
              (PEqualNP.Outside.L_lib_1168_aux.witness_r_plus_2_nocenter (r := r) (by omega)) with ⟨U, hU, hloss⟩
            refine ⟨U, hU, ?_⟩
            rw [hker U, hloss, if_neg hr2, if_neg hr3, min_eq_right (by omega)]
