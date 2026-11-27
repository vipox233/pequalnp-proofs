import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25936

def dot {k : ℕ} (x y : Fin k → ZMod 2) : ZMod 2 :=
  ∑ i : Fin k, x i * y i

def chi {k : ℕ} (c : Bool) (w x : Fin k → ZMod 2) : ℤ :=
  if Bool.xor c (decide (dot x w = 1)) then -1 else 1

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma zmod2_vec_add_eq_zero_iff {k : ℕ} (u w : Fin k → ZMod 2) : u + w = 0 ↔ u = w := by
  constructor
  · intro h
    funext i
    exact (zmod2_add_eq_zero_iff (u i) (w i)).mp (congrFun h i)
  · intro h
    subst h
    funext i
    exact (zmod2_add_eq_zero_iff (u i) (u i)).mpr rfl

lemma decide_zmod2_add (a b : ZMod 2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma dot_add {k : ℕ} (x u w : Fin k → ZMod 2) : dot x (u + w) = dot x u + dot x w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_zero {k : ℕ} (x : Fin k → ZMod 2) : dot x 0 = 0 := by
  simp [dot]

lemma chi_mul {k : ℕ} (c1 c2 : Bool) (w1 w2 x : Fin k → ZMod 2) :
    chi c1 w1 x * chi c2 w2 x = chi (Bool.xor c1 c2) (w1 + w2) x := by
  simp only [chi, dot_add, decide_zmod2_add]
  cases c1 <;> cases c2 <;> cases decide (dot x w1 = 1) <;> cases decide (dot x w2 = 1) <;> rfl

lemma chi_abs {k : ℕ} (c : Bool) (w x : Fin k → ZMod 2) :
    |chi c w x| = 1 := by
  simp only [chi]
  split_ifs <;> norm_num

lemma sum_chi_zero {k : ℕ} (c : Bool) :
    (∑ x : Fin k → ZMod 2, chi c 0 x) = (if c then -1 else 1) * (2 ^ k : ℤ) := by
  have h1 : ∀ x : Fin k → ZMod 2, chi c 0 x = if c then -1 else 1 := by
    intro x
    simp only [chi, dot_zero]
    cases c <;> decide
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

lemma sum_chi_eq_zero {k : ℕ} {w : Fin k → ZMod 2} (hw : w ≠ 0) (c : Bool) :
    (∑ x : Fin k → ZMod 2, chi c w x) = 0 := by
  have hex : ∃ i0 : Fin k, w i0 = 1 := by
    by_contra hno
    push Not at hno
    apply hw
    funext i
    rcases zmod2_cases (w i) with h0 | h1
    · exact h0
    · exact absurd h1 (hno i)
  obtain ⟨i0, hi0⟩ := hex
  let f : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun x => Function.update x i0 (x i0 + 1)
  have hf_inv : Function.Involutive f := by
    intro x
    funext i
    by_cases h : i = i0
    · subst h
      simp only [f, Function.update_self]
      rcases zmod2_cases (x i) with hx | hx <;> rw [hx] <;> decide
    · simp [f, h]
  have hdot : ∀ x : Fin k → ZMod 2, dot (f x) w = dot x w + 1 := by
    intro x
    simp only [dot]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    have hrest : ∑ i ∈ Finset.univ.erase i0, f x i * w i =
        ∑ i ∈ Finset.univ.erase i0, x i * w i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [f, Finset.ne_of_mem_erase hi]
    rw [hrest]
    simp only [f, Function.update_self, hi0, mul_one]
    ring
  have hchi : ∀ x : Fin k → ZMod 2, chi c w (f x) = - chi c w x := by
    intro x
    simp only [chi, hdot x, decide_zmod2_add, decide_true]
    cases c <;> cases decide (dot x w = 1) <;> rfl
  let e : (Fin k → ZMod 2) ≃ (Fin k → ZMod 2) := hf_inv.toPerm
  have hsum : (∑ x : Fin k → ZMod 2, chi c w x) = ∑ x : Fin k → ZMod 2, chi c w (f x) :=
    (Equiv.sum_comp e (fun x => chi c w x)).symm
  simp_rw [hchi, Finset.sum_neg_distrib] at hsum
  omega

def grpSum {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (x : Fin k → ZMod 2) : ℤ :=
  ∑ j ∈ A, chi (c j) (v j) x

lemma finset_even_sum {ι α : Type*} [AddCommMonoid α] (s : Finset ι) (f : ι → α)
    (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (fun x => Even x) (fun _ _ ha hb => ha.add hb) ⟨0, (zero_add 0).symm⟩ h

lemma grpSum_parity {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (x : Fin k → ZMod 2) :
    Even (grpSum v c A x - (A.card : ℤ)) := by
  have h1 : grpSum v c A x - (A.card : ℤ) = ∑ j ∈ A, (chi (c j) (v j) x - 1) := by
    simp [grpSum, Finset.sum_sub_distrib]
  rw [h1]
  clear h1
  refine finset_even_sum A (fun j => chi (c j) (v j) x - 1) fun j _ => ?_
  simp only [chi]
  split_ifs
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

lemma grpSum_abs_le {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (x : Fin k → ZMod 2) :
    |grpSum v c A x| ≤ (A.card : ℤ) := by
  calc |grpSum v c A x|
      ≤ ∑ j ∈ A, |chi (c j) (v j) x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _j ∈ A, (1 : ℤ) := Finset.sum_congr rfl fun j _ => chi_abs (c j) (v j) x
    _ = (A.card : ℤ) := by simp

lemma zmod2_sum_even_card {k : ℕ} (w : Fin k → ZMod 2) (n : ℕ) (hn : Even n) :
    n • w = 0 := by
  obtain ⟨r, rfl⟩ := hn
  funext i
  simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
  rw [← two_mul, Nat.cast_mul, Nat.cast_ofNat]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, zero_mul]

lemma coin_moments (d : ℕ) :
    let cs (x : Fin d → Bool) : ℤ := ∑ i : Fin d, if x i then 1 else -1
    (∑ x : Fin d → Bool, (cs x) ^ 2) = (2 ^ d : ℤ) * (d : ℤ) ∧
    (∑ x : Fin d → Bool, (cs x) ^ 4) = (2 ^ d : ℤ) * (3 * (d : ℤ) ^ 2 - 2 * (d : ℤ)) ∧
    (∑ x : Fin d → Bool, (cs x) ^ 6) =
      (2 ^ d : ℤ) * (15 * (d : ℤ) ^ 3 - 30 * (d : ℤ) ^ 2 + 16 * (d : ℤ)) := by
  induction d with
  | zero =>
    simp
  | succ d ih =>
    obtain ⟨ih2, ih4, ih6⟩ := ih
    let e : (Fin (d + 1) → Bool) ≃ Bool × (Fin d → Bool) :=
      { toFun := fun x => (x 0, fun i => x i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun x => by funext i; refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun ⟨b, y⟩ => Prod.ext rfl (funext fun i => by simp) }
    have hcs : ∀ (p : Bool × (Fin d → Bool)),
        (∑ i : Fin (d + 1), if e.symm p i then (1 : ℤ) else -1) =
        (if p.1 then (1 : ℤ) else -1) + ∑ i : Fin d, if p.2 i then (1 : ℤ) else -1 := by
      intro ⟨b, y⟩
      rw [Fin.sum_univ_succ]
      simp [e]
    have hsplit : ∀ (f : ℤ → ℤ),
        (∑ x : Fin (d + 1) → Bool, f (∑ i : Fin (d + 1), if x i then (1 : ℤ) else -1)) =
        ∑ y : Fin d → Bool,
          (f (1 + ∑ i : Fin d, if y i then (1 : ℤ) else -1) +
           f (-1 + ∑ i : Fin d, if y i then (1 : ℤ) else -1)) := by
      intro f
      rw [← Equiv.sum_comp e.symm]
      simp_rw [hcs]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => by simp
    have hcard : (∑ _y : Fin d → Bool, (1 : ℤ)) = (2 ^ d : ℤ) := by
      simp [Fintype.card_fun]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit (fun t => t ^ 2)]
      have hring : ∀ t : ℤ, (1 + t) ^ 2 + (-1 + t) ^ 2 = 2 * t ^ 2 + 2 * 1 := fun t => by ring
      simp_rw [hring, Finset.sum_add_distrib, ← Finset.mul_sum, ih2, hcard]
      push_cast
      ring
    · rw [hsplit (fun t => t ^ 4)]
      have hring : ∀ t : ℤ, (1 + t) ^ 4 + (-1 + t) ^ 4 = 2 * t ^ 4 + 12 * t ^ 2 + 2 * 1 :=
        fun t => by ring
      simp_rw [hring, Finset.sum_add_distrib, ← Finset.mul_sum, ih4, ih2, hcard]
      push_cast
      ring
    · rw [hsplit (fun t => t ^ 6)]
      have hring : ∀ t : ℤ,
          (1 + t) ^ 6 + (-1 + t) ^ 6 = 2 * t ^ 6 + 30 * t ^ 4 + 30 * t ^ 2 + 2 * 1 :=
        fun t => by ring
      simp_rw [hring, Finset.sum_add_distrib, ← Finset.mul_sum, ih6, ih4, ih2, hcard]
      push_cast
      ring

lemma sum_coin_prod {d r : ℕ} (t : Fin r → Fin d) :
    (∑ x : Fin d → Bool, ∏ j : Fin r, if x (t j) then (1 : ℤ) else -1) =
    if ∀ a : Fin d, Even (Finset.univ.filter fun j : Fin r => t j = a).card then (2 ^ d : ℤ) else 0 := by
  have hprod : ∀ x : Fin d → Bool,
      (∏ j : Fin r, if x (t j) then (1 : ℤ) else -1) =
      ∏ a : Fin d, (if x a then (1 : ℤ) else -1) ^ (Finset.univ.filter fun j : Fin r => t j = a).card := by
    intro x
    rw [← Finset.prod_fiberwise_of_maps_to (g := t) (fun _ _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.prod_const]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (a : Fin d) (b : Bool) =>
    (if b then (1 : ℤ) else -1) ^ (Finset.univ.filter fun j : Fin r => t j = a).card)]
  by_cases hev : ∀ a : Fin d, Even (Finset.univ.filter fun j : Fin r => t j = a).card
  · rw [if_pos hev]
    have h2 : ∀ a : Fin d,
        (∑ b : Bool, (if b then (1 : ℤ) else -1) ^ (Finset.univ.filter fun j : Fin r => t j = a).card) = 2 := by
      intro a
      rw [Fintype.sum_bool]
      simp [Even.neg_one_pow (hev a)]
    simp_rw [h2]
    simp
  · rw [if_neg hev]
    push Not at hev
    obtain ⟨a0, ha0⟩ := hev
    apply Finset.prod_eq_zero (Finset.mem_univ a0)
    rw [Fintype.sum_bool]
    simp [Odd.neg_one_pow ha0]

lemma card_even_tuples (d r : ℕ) :
    ((Finset.univ : Finset (Fin r → Fin d)).filter
      (fun t => ∀ a : Fin d, Even (Finset.univ.filter fun j : Fin r => t j = a).card)).card * (2 ^ d : ℤ) =
    ∑ x : Fin d → Bool, (∑ i : Fin d, if x i then (1 : ℤ) else -1) ^ r := by
  have hexp : ∀ x : Fin d → Bool,
      (∑ i : Fin d, if x i then (1 : ℤ) else -1) ^ r =
      ∑ t : Fin r → Fin d, ∏ j : Fin r, if x (t j) then (1 : ℤ) else -1 := by
    intro x
    rw [Fintype.sum_pow]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [sum_coin_prod]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma prod_chi {k r : ℕ} (c : Fin r → Bool) (w : Fin r → (Fin k → ZMod 2)) (x : Fin k → ZMod 2) :
    (∏ j : Fin r, chi (c j) (w j) x) =
    chi (decide (Odd (Finset.univ.filter fun j : Fin r => c j = true).card)) (∑ j : Fin r, w j) x := by
  induction r with
  | zero =>
    simp [chi, dot_zero]
  | succ r ih =>
    rw [Fin.prod_univ_succ, ih (fun j => c j.succ) (fun j => w j.succ), chi_mul, Fin.sum_univ_succ]
    congr 1
    have hcard : (Finset.univ.filter fun j : Fin (r + 1) => c j = true).card =
        (if c 0 = true then 1 else 0) +
        (Finset.univ.filter fun j : Fin r => c j.succ = true).card := by
      have h1 : ∀ f : Fin (r + 1) → Bool,
          (Finset.univ.filter fun j : Fin (r + 1) => f j = true).card =
          (if f 0 = true then 1 else 0) +
          (Finset.univ.filter fun j : Fin r => f j.succ = true).card := by
        intro f
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      exact h1 c
    rw [hcard]
    cases c 0
    · simp
    · simp only [ite_true]
      by_cases ho : Odd (Finset.univ.filter fun j : Fin r => c j.succ = true).card
      · have hne : ¬ Odd (1 + (Finset.univ.filter fun j : Fin r => c j.succ = true).card) := by
          obtain ⟨m, hm⟩ := ho; rw [hm, Nat.not_odd_iff_even]; exact ⟨m + 1, by ring⟩
        simp [ho, hne]
      · have hy : Odd (1 + (Finset.univ.filter fun j : Fin r => c j.succ = true).card) := by
          rw [Nat.not_odd_iff_even] at ho; obtain ⟨m, hm⟩ := ho; exact ⟨m, by omega⟩
        simp [ho, hy]

lemma sum_pow_grpSum_eq_coin {k m r : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (hr : Even r)
    (hno : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ r → Even S.card → (∑ j ∈ S, v j) ≠ 0) :
    (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ r) * (2 ^ A.card : ℤ) =
      (2 ^ k : ℤ) * (∑ y : Fin A.card → Bool, (∑ i : Fin A.card, if y i then (1 : ℤ) else -1) ^ r) := by
  let e : Fin A.card ≃ A := A.equivFin.symm
  have hgrp : ∀ x : Fin k → ZMod 2, grpSum v c A x = ∑ i : Fin A.card, chi (c (e i).1) (v (e i).1) x := by
    intro x
    rw [grpSum, ← Finset.sum_attach A (fun j => chi (c j) (v j) x)]
    exact (Equiv.sum_comp e (fun j : A => chi (c j.1) (v j.1) x)).symm
  simp_rw [hgrp]
  have hexp : ∀ x : Fin k → ZMod 2,
      (∑ i : Fin A.card, chi (c (e i).1) (v (e i).1) x) ^ r =
      ∑ t : Fin r → Fin A.card, ∏ j : Fin r, chi (c (e (t j)).1) (v (e (t j)).1) x := by
    intro x
    rw [Fintype.sum_pow]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hterm : ∀ t : Fin r → Fin A.card,
      (∑ x : Fin k → ZMod 2, ∏ j : Fin r, chi (c (e (t j)).1) (v (e (t j)).1) x) =
      if ∀ a : Fin A.card, Even (Finset.univ.filter fun j : Fin r => t j = a).card then (2 ^ k : ℤ) else 0 := by
    intro t
    simp_rw [prod_chi]
    let oddA : Finset (Fin A.card) :=
      Finset.univ.filter fun a : Fin A.card => Odd (Finset.univ.filter fun j : Fin r => t j = a).card
    have hvec : (∑ j : Fin r, v (e (t j)).1) = ∑ a ∈ oddA, v (e a).1 := by
      have hfib : (∑ j : Fin r, v (e (t j)).1) =
          ∑ a : Fin A.card, (Finset.univ.filter fun j : Fin r => t j = a).card • v (e a).1 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := t) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const]
      rw [hfib, ← Finset.sum_filter_add_sum_filter_not _ (fun a => Odd (Finset.univ.filter fun j : Fin r => t j = a).card)]
      have hev0 : ∑ a ∈ Finset.univ.filter (fun a => ¬ Odd (Finset.univ.filter fun j : Fin r => t j = a).card),
          (Finset.univ.filter fun j : Fin r => t j = a).card • v (e a).1 = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        exact zmod2_sum_even_card _ _ (Nat.not_odd_iff_even.mp (Finset.mem_filter.mp ha).2)
      rw [hev0, add_zero]
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨q, hq⟩ := (Finset.mem_filter.mp ha).2
      rw [hq, add_smul, one_smul, zmod2_sum_even_card _ (2 * q) ⟨q, by ring⟩, zero_add]
    by_cases hev : ∀ a : Fin A.card, Even (Finset.univ.filter fun j : Fin r => t j = a).card
    · simp only [hev, ite_true]
      have hodd0 : oddA = ∅ := by
        ext a; simp [oddA, Nat.not_odd_iff_even.mpr (hev a)]
      rw [hvec, hodd0, Finset.sum_empty]
      have hceven : Even (Finset.univ.filter fun j : Fin r => c (e (t j)).1 = true).card := by
        have hfib := Finset.card_eq_sum_card_fiberwise (f := t)
          (s := Finset.univ.filter fun j : Fin r => c (e (t j)).1 = true)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
        rw [hfib]
        refine finset_even_sum Finset.univ _ fun a _ => ?_
        by_cases hca : c (e a).1 = true
        · have hsub : (Finset.univ.filter fun j : Fin r => c (e (t j)).1 = true).filter (fun j => t j = a) =
              Finset.univ.filter fun j : Fin r => t j = a := by
            ext j; simp; intro h; rw [h, hca]
          rw [hsub]; exact hev a
        · have hsub : (Finset.univ.filter fun j : Fin r => c (e (t j)).1 = true).filter (fun j => t j = a) = ∅ := by
            ext j; simp; intro h1 h2; rw [h2] at h1; exact hca h1
          rw [hsub, Finset.card_empty]; exact (⟨0, rfl⟩ : Even _)
      rw [show decide (Odd (Finset.univ.filter fun j : Fin r => c (e (t j)).1 = true).card) = false by
        simp [Nat.not_odd_iff_even.mpr hceven]]
      rw [sum_chi_zero]
      simp
    · simp only [hev, ite_false]
      rw [hvec]
      apply sum_chi_eq_zero
      let S : Finset (Fin m) := oddA.image (fun a => (e a).1)
      have hinj : Function.Injective (fun a : Fin A.card => (e a).1) :=
        Subtype.val_injective.comp e.injective
      have hsumS : ∑ a ∈ oddA, v (e a).1 = ∑ j ∈ S, v j := by
        rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      rw [hsumS]
      have hcardS : S.card = oddA.card := Finset.card_image_of_injective _ hinj
      have hpos : 0 < oddA.card := by
        push Not at hev
        obtain ⟨a0, ha0⟩ := hev
        exact Finset.card_pos.mpr ⟨a0, by simp [oddA, ha0]⟩
      have hle : oddA.card ≤ r := by
        have hsumr : (∑ a : Fin A.card, (Finset.univ.filter fun j : Fin r => t j = a).card) = r := by
          have := Finset.card_eq_sum_card_fiberwise (f := t) (s := Finset.univ) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)
          simpa using this.symm
        have hge1 : ∀ a ∈ oddA, 1 ≤ (Finset.univ.filter fun j : Fin r => t j = a).card := by
          intro a ha
          obtain ⟨q, hq⟩ := (Finset.mem_filter.mp ha).2
          omega
        have h1 := Finset.card_nsmul_le_sum oddA (fun a => (Finset.univ.filter fun j : Fin r => t j = a).card) 1 hge1
        have h2 : ∑ a ∈ oddA, (Finset.univ.filter fun j : Fin r => t j = a).card ≤
            ∑ a : Fin A.card, (Finset.univ.filter fun j : Fin r => t j = a).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        simp only [smul_eq_mul, mul_one] at h1
        omega
      have hev_oddA : Even oddA.card := by
        have hsumr : (∑ a : Fin A.card, (Finset.univ.filter fun j : Fin r => t j = a).card) = r := by
          have := Finset.card_eq_sum_card_fiberwise (f := t) (s := Finset.univ) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)
          simpa using this.symm
        have hmod : (∑ a : Fin A.card, (Finset.univ.filter fun j : Fin r => t j = a).card) % 2 = oddA.card % 2 := by
          rw [← Finset.sum_filter_add_sum_filter_not _ (fun a => Odd (Finset.univ.filter fun j : Fin r => t j = a).card)]
          rw [Nat.add_mod]
          have h1 : (∑ a ∈ oddA, (Finset.univ.filter fun j : Fin r => t j = a).card) % 2 = oddA.card % 2 := by
            rw [Finset.sum_nat_mod]
            have hcon : ∑ a ∈ oddA, (Finset.univ.filter fun j : Fin r => t j = a).card % 2 =
                ∑ _a ∈ oddA, 1 := Finset.sum_congr rfl fun a ha => Nat.odd_iff.mp (Finset.mem_filter.mp ha).2
            rw [hcon]
            simp
          have h2 : (∑ a ∈ Finset.univ.filter (fun a => ¬ Odd (Finset.univ.filter fun j : Fin r => t j = a).card),
              (Finset.univ.filter fun j : Fin r => t j = a).card) % 2 = 0 := by
            rw [Finset.sum_nat_mod]
            have hcon : ∑ a ∈ Finset.univ.filter (fun a => ¬ Odd (Finset.univ.filter fun j : Fin r => t j = a).card),
                (Finset.univ.filter fun j : Fin r => t j = a).card % 2 = 0 :=
              Finset.sum_eq_zero fun a ha =>
                Nat.even_iff.mp (Nat.not_odd_iff_even.mp (Finset.mem_filter.mp ha).2)
            rw [hcon]
          rw [h1, h2, add_zero, Nat.mod_mod]
        rw [hsumr] at hmod
        exact Nat.even_iff.mpr (hmod.symm.trans (Nat.even_iff.mp hr))
      exact hno S (by omega) (by omega) (by rw [hcardS]; exact hev_oddA)
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [← card_even_tuples A.card r]
  ring

lemma sum_sq_grpSum {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) :
    (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 2) = (2 ^ k : ℤ) * (A.card : ℤ) := by
  have hno : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ 2 → Even S.card → (∑ j ∈ S, v j) ≠ 0 := by
    intro S hpos hle hev
    have h2 : S.card = 2 := by obtain ⟨q, hq⟩ := hev; omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    rw [Finset.sum_pair hab]
    intro h0
    exact hab (v.injective ((zmod2_vec_add_eq_zero_iff (v a) (v b)).mp h0))
  have h := sum_pow_grpSum_eq_coin v c A ⟨1, rfl⟩ hno
  rw [(coin_moments A.card).1] at h
  have hpos : (0 : ℤ) < 2 ^ A.card := by positivity
  nlinarith

lemma sum_pow4_grpSum {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (h4 : ∀ S : Finset (Fin m), S.card = 4 → (∑ j ∈ S, v j) ≠ 0)
    (A : Finset (Fin m)) :
    (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 4) =
      (2 ^ k : ℤ) * (3 * (A.card : ℤ) ^ 2 - 2 * (A.card : ℤ)) := by
  have hno : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ 4 → Even S.card → (∑ j ∈ S, v j) ≠ 0 := by
    intro S hpos hle hev
    have h24 : S.card = 2 ∨ S.card = 4 := by obtain ⟨q, hq⟩ := hev; omega
    rcases h24 with h2 | h4c
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      rw [Finset.sum_pair hab]
      intro h0
      exact hab (v.injective ((zmod2_vec_add_eq_zero_iff (v a) (v b)).mp h0))
    · exact h4 S h4c
  have h := sum_pow_grpSum_eq_coin v c A ⟨2, rfl⟩ hno
  rw [(coin_moments A.card).2.1] at h
  have hpos : (0 : ℤ) < 2 ^ A.card := by positivity
  nlinarith

lemma sum_pow6_grpSum {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (h46 : ∀ S : Finset (Fin m), S.card = 4 ∨ S.card = 6 → (∑ j ∈ S, v j) ≠ 0)
    (A : Finset (Fin m)) :
    (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 6) =
      (2 ^ k : ℤ) * (15 * (A.card : ℤ) ^ 3 - 30 * (A.card : ℤ) ^ 2 + 16 * (A.card : ℤ)) := by
  have hno : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ 6 → Even S.card → (∑ j ∈ S, v j) ≠ 0 := by
    intro S hpos hle hev
    have h246 : S.card = 2 ∨ S.card = 4 ∨ S.card = 6 := by obtain ⟨q, hq⟩ := hev; omega
    rcases h246 with h2 | h4c | h6c
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      rw [Finset.sum_pair hab]
      intro h0
      exact hab (v.injective ((zmod2_vec_add_eq_zero_iff (v a) (v b)).mp h0))
    · exact h46 S (Or.inl h4c)
    · exact h46 S (Or.inr h6c)
  have h := sum_pow_grpSum_eq_coin v c A ⟨3, rfl⟩ hno
  rw [(coin_moments A.card).2.2] at h
  have hpos : (0 : ℤ) < 2 ^ A.card := by positivity
  nlinarith

lemma odd_abs_le (t : ℤ) (ht : Odd t) : 4 * |t| ≤ t ^ 2 + 3 := by
  have hodd_abs : Odd |t| := by
    rcases le_or_gt 0 t with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg h]; exact ht.neg
  obtain ⟨q, hq⟩ := hodd_abs
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  rw [hsq, hq]
  have : (2 * q + 1) ^ 2 + 3 - 4 * (2 * q + 1) = 4 * q * (q - 1) := by ring
  have hq0 : 0 ≤ q := by
    have : 0 ≤ |t| := abs_nonneg t
    omega
  have hprod : 0 ≤ q * (q - 1) := by
    by_cases hq1 : q = 0
    · simp [hq1]
    · have : 1 ≤ q := by omega
      nlinarith
  linarith

lemma even_abs_poly6 (t : ℤ) (ht : Even t) :
    1920 * |t| ≤ 1184 * t ^ 2 - 60 * t ^ 4 + t ^ 6 := by
  have hev_abs : Even |t| := by
    rcases le_or_gt 0 t with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg h]; exact ht.neg
  obtain ⟨q, hq⟩ := hev_abs
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hp4 : t ^ 4 = |t| ^ 4 := by
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (|t| ^ 2) ^ 2 := by rw [hsq]
      _ = |t| ^ 4 := by ring
  have hp6 : t ^ 6 = |t| ^ 6 := by
    calc t ^ 6 = (t ^ 2) ^ 3 := by ring
      _ = (|t| ^ 2) ^ 3 := by rw [hsq]
      _ = |t| ^ 6 := by ring
  rw [hsq, hp4, hp6, hq]
  have hfac : 1184 * (q + q) ^ 2 - 60 * (q + q) ^ 4 + (q + q) ^ 6 - 1920 * (q + q) =
      64 * q * (q - 1) * (q - 2) * (q - 3) * (q ^ 2 + 6 * q + 10) := by ring
  have hq0 : 0 ≤ q := by
    have : 0 ≤ |t| := abs_nonneg t
    omega
  have hpos : 0 ≤ q * (q - 1) * (q - 2) * (q - 3) := by
    by_cases h0 : q = 0
    · simp [h0]
    · by_cases h1 : q = 1
      · simp [h1]
      · by_cases h2 : q = 2
        · simp [h2]
        · by_cases h3 : q = 3
          · simp [h3]
          · have h4 : 4 ≤ q := by omega
            have hp1 : 0 ≤ q * (q - 1) := by nlinarith
            have hp2 : 0 ≤ (q - 2) * (q - 3) := by nlinarith
            have hp3 : 0 ≤ (q * (q - 1)) * ((q - 2) * (q - 3)) := mul_nonneg hp1 hp2
            linarith
  have hquad : 0 ≤ q ^ 2 + 6 * q + 10 := by nlinarith
  have hmul : 0 ≤ 64 * q * (q - 1) * (q - 2) * (q - 3) * (q ^ 2 + 6 * q + 10) := by
    have : 0 ≤ (q * (q - 1) * (q - 2) * (q - 3)) * (q ^ 2 + 6 * q + 10) :=
      mul_nonneg hpos hquad
    linarith
  linarith

lemma even_abs_poly10 (t : ℤ) (ht : Even t) (hle : |t| ≤ 10) :
    1008 * |t| ≤ 1280 + 188 * t ^ 2 - t ^ 4 := by
  have hev_abs : Even |t| := by
    rcases le_or_gt 0 t with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg h]; exact ht.neg
  obtain ⟨q, hq⟩ := hev_abs
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hp4 : t ^ 4 = |t| ^ 4 := by
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (|t| ^ 2) ^ 2 := by rw [hsq]
      _ = |t| ^ 4 := by ring
  rw [hsq, hp4, hq]
  have hq0 : 0 ≤ q := by have := abs_nonneg t; omega
  have hq5 : q ≤ 5 := by omega
  interval_cases q <;> norm_num

lemma sum_abs_bound_odd {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (hodd : Odd A.card) :
    4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ≤ (2 ^ k : ℤ) * ((A.card : ℤ) + 3) := by
  have hpt : ∀ x : Fin k → ZMod 2, 4 * |grpSum v c A x| ≤ (grpSum v c A x) ^ 2 + 3 := by
    intro x
    apply odd_abs_le
    obtain ⟨r, hr⟩ := grpSum_parity v c A x
    obtain ⟨q, hq⟩ := hodd
    exact ⟨r + q, by omega⟩
  calc 4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)
      = ∑ x : Fin k → ZMod 2, 4 * |grpSum v c A x| := by rw [Finset.mul_sum]
    _ ≤ ∑ x : Fin k → ZMod 2, ((grpSum v c A x) ^ 2 + 3) := Finset.sum_le_sum fun x _ => hpt x
    _ = (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 2) + ∑ _x : Fin k → ZMod 2, (3 : ℤ) :=
        Finset.sum_add_distrib
    _ = (2 ^ k : ℤ) * (A.card : ℤ) + (2 ^ k : ℤ) * 3 := by
        rw [sum_sq_grpSum]
        simp [mul_comm]
    _ = (2 ^ k : ℤ) * ((A.card : ℤ) + 3) := by ring

lemma sum_abs_bound_even {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (h46 : ∀ S : Finset (Fin m), S.card = 4 ∨ S.card = 6 → (∑ j ∈ S, v j) ≠ 0)
    (A : Finset (Fin m)) (hev : Even A.card) (hpos : 0 < A.card) :
    4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ≤ (2 ^ k : ℤ) * ((A.card : ℤ) + 2) := by
  have hpt_ev : ∀ x : Fin k → ZMod 2, Even (grpSum v c A x) := by
    intro x
    obtain ⟨r, hr⟩ := grpSum_parity v c A x
    obtain ⟨q, hq⟩ := hev
    exact ⟨r + q, by omega⟩
  by_cases hd8 : A.card ≤ 8
  · have hsum : 1920 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ≤
        (2 ^ k : ℤ) * (15 * (A.card : ℤ) ^ 3 - 210 * (A.card : ℤ) ^ 2 + 1320 * (A.card : ℤ)) := by
      calc 1920 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)
          = ∑ x : Fin k → ZMod 2, 1920 * |grpSum v c A x| := by rw [Finset.mul_sum]
        _ ≤ ∑ x : Fin k → ZMod 2,
              (1184 * (grpSum v c A x) ^ 2 - 60 * (grpSum v c A x) ^ 4 + (grpSum v c A x) ^ 6) :=
            Finset.sum_le_sum fun x _ => even_abs_poly6 (grpSum v c A x) (hpt_ev x)
        _ = 1184 * (∑ x, (grpSum v c A x) ^ 2) - 60 * (∑ x, (grpSum v c A x) ^ 4) +
              (∑ x, (grpSum v c A x) ^ 6) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
        _ = (2 ^ k : ℤ) * (15 * (A.card : ℤ) ^ 3 - 210 * (A.card : ℤ) ^ 2 + 1320 * (A.card : ℤ)) := by
            rw [sum_sq_grpSum, sum_pow4_grpSum v c (fun S h => h46 S (Or.inl h)), sum_pow6_grpSum v c h46]
            ring
    have hpoly : 15 * (A.card : ℤ) ^ 3 - 210 * (A.card : ℤ) ^ 2 + 1320 * (A.card : ℤ) ≤
        480 * ((A.card : ℤ) + 2) := by
      have : A.card = 2 ∨ A.card = 4 ∨ A.card = 6 ∨ A.card = 8 := by
        obtain ⟨q, hq⟩ := hev; omega
      rcases this with h | h | h | h <;> rw [h] <;> norm_num
    have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
    have hmul := mul_le_mul_of_nonneg_left hpoly h2k
    linarith
  · by_cases hd10 : A.card = 10
    · have hsum : 1008 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ≤
          (2 ^ k : ℤ) * (1280 + 188 * (A.card : ℤ) - (3 * (A.card : ℤ) ^ 2 - 2 * (A.card : ℤ))) := by
        calc 1008 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)
            = ∑ x : Fin k → ZMod 2, 1008 * |grpSum v c A x| := by rw [Finset.mul_sum]
          _ ≤ ∑ x : Fin k → ZMod 2,
                (1280 + 188 * (grpSum v c A x) ^ 2 - (grpSum v c A x) ^ 4) := by
              refine Finset.sum_le_sum fun x _ => even_abs_poly10 (grpSum v c A x) (hpt_ev x) ?_
              have := grpSum_abs_le v c A x
              omega
          _ = (∑ _x : Fin k → ZMod 2, (1280 : ℤ)) + 188 * (∑ x, (grpSum v c A x) ^ 2) -
                (∑ x, (grpSum v c A x) ^ 4) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
          _ = (2 ^ k : ℤ) * (1280 + 188 * (A.card : ℤ) - (3 * (A.card : ℤ) ^ 2 - 2 * (A.card : ℤ))) := by
              rw [sum_sq_grpSum, sum_pow4_grpSum v c (fun S h => h46 S (Or.inl h))]
              simp
              ring
      rw [hd10] at hsum ⊢
      norm_num at hsum ⊢
      have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
      linarith
    · have hd12 : 12 ≤ A.card := by obtain ⟨q, hq⟩ := hev; omega
      have hcs : (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ^ 2 ≤
          (2 ^ k : ℤ) * (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 2) := by
        have hnn : (0 : ℤ) ≤ ∑ x : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2,
            (|grpSum v c A x| - |grpSum v c A y|) ^ 2 :=
          Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
        have hexp : (∑ x : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2,
            (|grpSum v c A x| - |grpSum v c A y|) ^ 2) =
            2 * (2 ^ k : ℤ) * (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 2) -
            2 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ^ 2 := by
          have h1 : ∀ x y : Fin k → ZMod 2,
              (|grpSum v c A x| - |grpSum v c A y|) ^ 2 =
              (grpSum v c A x) ^ 2 + (grpSum v c A y) ^ 2 - 2 * (|grpSum v c A x| * |grpSum v c A y|) := by
            intro x y; rw [sub_sq, sq_abs, sq_abs]; ring
          simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul,
            Nat.cast_pow, Nat.cast_ofNat, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
        linarith
      rw [sum_sq_grpSum] at hcs
      have hsq : (4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)) ^ 2 ≤
          ((2 ^ k : ℤ) * ((A.card : ℤ) + 2)) ^ 2 := by
        have h16 : 16 * (A.card : ℤ) ≤ ((A.card : ℤ) + 2) ^ 2 := by nlinarith
        have h2k2 : (0 : ℤ) ≤ (2 ^ k : ℤ) ^ 2 := by positivity
        calc (4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)) ^ 2
            = 16 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) ^ 2 := by ring
          _ ≤ 16 * ((2 ^ k : ℤ) * ((2 ^ k : ℤ) * (A.card : ℤ))) := by linarith
          _ = (2 ^ k : ℤ) ^ 2 * (16 * (A.card : ℤ)) := by ring
          _ ≤ (2 ^ k : ℤ) ^ 2 * ((A.card : ℤ) + 2) ^ 2 := mul_le_mul_of_nonneg_left h16 h2k2
          _ = ((2 ^ k : ℤ) * ((A.card : ℤ) + 2)) ^ 2 := by ring
      have hrhs : (0 : ℤ) ≤ (2 ^ k : ℤ) * ((A.card : ℤ) + 2) := by positivity
      nlinarith

lemma sum_abs_eq_card1 {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (h1 : A.card = 1) :
    4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) = (2 ^ k : ℤ) * 4 := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
  have : ∀ x : Fin k → ZMod 2, |grpSum v c {a} x| = 1 := fun x => by
    simp [grpSum, chi_abs]
  simp_rw [this]
  simp [Fintype.card_fun, mul_comm]

lemma sum_abs_eq_card2 {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (h2 : A.card = 2) :
    4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) = (2 ^ k : ℤ) * 4 := by
  have hpt : ∀ x : Fin k → ZMod 2, 2 * |grpSum v c A x| = (grpSum v c A x) ^ 2 := by
    intro x
    have hle := grpSum_abs_le v c A x
    have hev : Even (grpSum v c A x) := by
      obtain ⟨r, hr⟩ := grpSum_parity v c A x
      exact ⟨r + 1, by omega⟩
    have hev_abs : Even |grpSum v c A x| := by
      rcases le_or_gt 0 (grpSum v c A x) with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hev.neg
    obtain ⟨q, hq⟩ := hev_abs
    rw [← sq_abs, hq]
    have hq0 : 0 ≤ q := by have := abs_nonneg (grpSum v c A x); omega
    have hq1 : q ≤ 1 := by omega
    interval_cases q <;> norm_num
  calc 4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)
      = 2 * (∑ x : Fin k → ZMod 2, 2 * |grpSum v c A x|) := by rw [← Finset.mul_sum]; ring
    _ = 2 * (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 2) := by simp_rw [hpt]
    _ = 2 * ((2 ^ k : ℤ) * (A.card : ℤ)) := by rw [sum_sq_grpSum]
    _ = (2 ^ k : ℤ) * 4 := by rw [h2]; ring

lemma sum_abs_eq_card3 {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (A : Finset (Fin m)) (h3 : A.card = 3) :
    4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) = (2 ^ k : ℤ) * 6 := by
  have hpt : ∀ x : Fin k → ZMod 2, 4 * |grpSum v c A x| = (grpSum v c A x) ^ 2 + 3 := by
    intro x
    have hle := grpSum_abs_le v c A x
    have hodd : Odd (grpSum v c A x) := by
      obtain ⟨r, hr⟩ := grpSum_parity v c A x
      exact ⟨r + 1, by omega⟩
    have hodd_abs : Odd |grpSum v c A x| := by
      rcases le_or_gt 0 (grpSum v c A x) with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hodd.neg
    obtain ⟨q, hq⟩ := hodd_abs
    rw [← sq_abs, hq]
    have hq0 : 0 ≤ q := by have := abs_nonneg (grpSum v c A x); omega
    have hq1 : q ≤ 1 := by omega
    interval_cases q <;> norm_num
  calc 4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)
      = ∑ x : Fin k → ZMod 2, 4 * |grpSum v c A x| := by rw [Finset.mul_sum]
    _ = ∑ x : Fin k → ZMod 2, ((grpSum v c A x) ^ 2 + 3) := by simp_rw [hpt]
    _ = (∑ x : Fin k → ZMod 2, (grpSum v c A x) ^ 2) + ∑ _x : Fin k → ZMod 2, (3 : ℤ) :=
        Finset.sum_add_distrib
    _ = (2 ^ k : ℤ) * 6 := by
        rw [sum_sq_grpSum, h3]
        simp [Fintype.card_fun]
        ring

lemma sum_abs_eq_card4 {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (h4 : ∀ S : Finset (Fin m), S.card = 4 → (∑ j ∈ S, v j) ≠ 0)
    (A : Finset (Fin m)) (hA4 : A.card = 4) :
    4 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) = (2 ^ k : ℤ) * 6 := by
  have hpt : ∀ x : Fin k → ZMod 2,
      48 * |grpSum v c A x| = 28 * (grpSum v c A x) ^ 2 - (grpSum v c A x) ^ 4 := by
    intro x
    have hle := grpSum_abs_le v c A x
    have hev : Even (grpSum v c A x) := by
      obtain ⟨r, hr⟩ := grpSum_parity v c A x
      exact ⟨r + 2, by omega⟩
    have hev_abs : Even |grpSum v c A x| := by
      rcases le_or_gt 0 (grpSum v c A x) with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact hev.neg
    obtain ⟨q, hq⟩ := hev_abs
    have hsq : (grpSum v c A x) ^ 2 = |grpSum v c A x| ^ 2 := (sq_abs _).symm
    have hp4 : (grpSum v c A x) ^ 4 = |grpSum v c A x| ^ 4 := by
      calc (grpSum v c A x) ^ 4 = ((grpSum v c A x) ^ 2) ^ 2 := by ring
        _ = (|grpSum v c A x| ^ 2) ^ 2 := by rw [hsq]
        _ = |grpSum v c A x| ^ 4 := by ring
    rw [hsq, hp4, hq]
    have hq0 : 0 ≤ q := by have := abs_nonneg (grpSum v c A x); omega
    have hq2 : q ≤ 2 := by omega
    interval_cases q <;> norm_num
  have h48 : 48 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|) = (2 ^ k : ℤ) * 72 := by
    calc 48 * (∑ x : Fin k → ZMod 2, |grpSum v c A x|)
        = ∑ x : Fin k → ZMod 2, 48 * |grpSum v c A x| := by rw [Finset.mul_sum]
      _ = ∑ x : Fin k → ZMod 2, (28 * (grpSum v c A x) ^ 2 - (grpSum v c A x) ^ 4) := by
          simp_rw [hpt]
      _ = 28 * (∑ x, (grpSum v c A x) ^ 2) - ∑ x, (grpSum v c A x) ^ 4 := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (2 ^ k : ℤ) * 72 := by
          rw [sum_sq_grpSum, sum_pow4_grpSum v c h4, hA4]
          ring
  omega

def grpLoss {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (A : Finset (Fin m)) (f : (Fin k → ZMod 2) → Bool) : ℕ :=
  ∑ x : Fin k → ZMod 2,
    (A.filter fun j => f x ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1))).card

def majOut {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (A : Finset (Fin m)) (x : Fin k → ZMod 2) : Bool :=
  Bool.xor (r x) (decide (grpSum v c A x < 0))

lemma row_loss_formula {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (A : Finset (Fin m)) (x : Fin k → ZMod 2) (b : Bool) :
    2 * ((A.filter fun j => b ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1))).card : ℤ) =
      (A.card : ℤ) - (if Bool.xor b (r x) then -1 else 1) * grpSum v c A x := by
  have hterm : ∀ j ∈ A,
      (if b ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1)) then (2 : ℤ) else 0) =
      1 - (if Bool.xor b (r x) then -1 else 1) * chi (c j) (v j) x := by
    intro j _
    simp only [chi]
    cases b <;> cases r x <;> cases c j <;> cases decide (dot x (v j) = 1) <;> decide
  calc 2 * ((A.filter fun j => b ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1))).card : ℤ)
      = ∑ j ∈ A, if b ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1)) then (2 : ℤ) else 0 := by
        rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    _ = ∑ j ∈ A, (1 - (if Bool.xor b (r x) then -1 else 1) * chi (c j) (v j) x) :=
        Finset.sum_congr rfl hterm
    _ = (A.card : ℤ) - (if Bool.xor b (r x) then -1 else 1) * grpSum v c A x := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp [grpSum]

lemma grpLoss_ge {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (A : Finset (Fin m)) (f : (Fin k → ZMod 2) → Bool) :
    (2 ^ k : ℤ) * (A.card : ℤ) - ∑ x : Fin k → ZMod 2, |grpSum v c A x| ≤
      2 * (grpLoss v r c A f : ℤ) := by
  rw [grpLoss]
  push_cast
  rw [Finset.mul_sum]
  calc (2 ^ k : ℤ) * (A.card : ℤ) - ∑ x : Fin k → ZMod 2, |grpSum v c A x|
      = ∑ x : Fin k → ZMod 2, ((A.card : ℤ) - |grpSum v c A x|) := by
        rw [Finset.sum_sub_distrib]
        simp [Fintype.card_fun]
    _ ≤ ∑ x : Fin k → ZMod 2,
          ((A.card : ℤ) - (if Bool.xor (f x) (r x) then -1 else 1) * grpSum v c A x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        split_ifs
        · have := neg_le_abs (grpSum v c A x); linarith
        · have := le_abs_self (grpSum v c A x); linarith
    _ = ∑ x : Fin k → ZMod 2,
          2 * ((A.filter fun j => f x ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1))).card : ℤ) := by
        refine Finset.sum_congr rfl fun x _ => (row_loss_formula v r c A x (f x)).symm

lemma grpLoss_maj {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (r : (Fin k → ZMod 2) → Bool)
    (c : Fin m → Bool) (A : Finset (Fin m)) :
    2 * (grpLoss v r c A (majOut v r c A) : ℤ) =
      (2 ^ k : ℤ) * (A.card : ℤ) - ∑ x : Fin k → ZMod 2, |grpSum v c A x| := by
  rw [grpLoss]
  push_cast
  rw [Finset.mul_sum]
  calc ∑ x : Fin k → ZMod 2,
        2 * ((A.filter fun j => majOut v r c A x ≠ Bool.xor (Bool.xor (r x) (c j)) (decide (dot x (v j) = 1))).card : ℤ)
      = ∑ x : Fin k → ZMod 2,
          ((A.card : ℤ) - (if Bool.xor (majOut v r c A x) (r x) then -1 else 1) * grpSum v c A x) := by
        refine Finset.sum_congr rfl fun x _ => row_loss_formula v r c A x (majOut v r c A x)
    _ = ∑ x : Fin k → ZMod 2, ((A.card : ℤ) - |grpSum v c A x|) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hxor : Bool.xor (majOut v r c A x) (r x) = decide (grpSum v c A x < 0) := by
          simp only [majOut]
          cases r x <;> cases decide (grpSum v c A x < 0) <;> rfl
        rw [hxor]
        by_cases hneg : grpSum v c A x < 0
        · simp [hneg, abs_of_neg hneg]
        · have hnn : 0 ≤ grpSum v c A x := by omega
          simp [hneg, abs_of_nonneg hnn]
    _ = (2 ^ k : ℤ) * (A.card : ℤ) - ∑ x : Fin k → ZMod 2, |grpSum v c A x| := by
        rw [Finset.sum_sub_distrib]
        simp [Fintype.card_fun]

lemma loss_eq_sum_grpLoss {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool)
    (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool) :
    ((Finset.univ : Finset ((Fin k → ZMod 2) × Fin m)).filter (fun z =>
      out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
        (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card =
    ∑ a : Fin l, grpLoss v r c (Finset.univ.filter fun j => label j = a) (fun x => out x a) := by
  simp only [grpLoss, dot]
  rw [Finset.sum_comm]
  have hcard : ((Finset.univ : Finset ((Fin k → ZMod 2) × Fin m)).filter (fun z =>
      out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
        (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card =
      ∑ x : Fin k → ZMod 2,
        ((Finset.univ : Finset (Fin m)).filter fun j =>
          out x (label j) ≠ Bool.xor (Bool.xor (r x) (c j))
            (decide ((∑ i : Fin k, x i * v j i) = 1))).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
  rw [hcard]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_eq_sum_card_fiberwise (f := label) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by rwa [h2] at h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨by rwa [h2], h2⟩

lemma forward_lower {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (h46 : ∀ S : Finset (Fin m), S.card = 4 ∨ S.card = 6 → (∑ j ∈ S, v j) ≠ 0)
    (hlm : l ≤ m) (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool)
    (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool) :
    2 ^ k * (3 * (m - l) + (m - l) % 2) ≤
      8 * ((Finset.univ : Finset ((Fin k → ZMod 2) × Fin m)).filter (fun z =>
        out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
          (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card := by
  rw [loss_eq_sum_grpLoss]
  let fib (a : Fin l) : Finset (Fin m) := Finset.univ.filter fun j => label j = a
  let nonemp : Finset (Fin l) := Finset.univ.filter fun a => (fib a).Nonempty
  let evenGrp : Finset (Fin l) := nonemp.filter fun a => Even (fib a).card
  have hgrp : ∀ a : Fin l,
      (2 ^ k : ℤ) * (if a ∈ nonemp then (3 * ((fib a).card - 1 : ℕ) + if Even (fib a).card then (1 : ℤ) else 0) else 0) ≤
      8 * (grpLoss v r c (fib a) (fun x => out x a) : ℤ) := by
    intro a
    by_cases hne : a ∈ nonemp
    · simp only [hne, ite_true]
      have hpos : 0 < (fib a).card := Finset.card_pos.mpr (Finset.mem_filter.mp hne).2
      have hge := grpLoss_ge v r c (fib a) (fun x => out x a)
      have hsub : (((fib a).card - 1 : ℕ) : ℤ) = ((fib a).card : ℤ) - 1 := by omega
      by_cases hev : Even (fib a).card
      · simp only [hev, ite_true]
        have hb := sum_abs_bound_even v c h46 (fib a) hev hpos
        rw [hsub]
        linarith
      · simp only [hev, ite_false]
        have hb := sum_abs_bound_odd v c (fib a) (Nat.not_even_iff_odd.mp hev)
        rw [hsub]
        linarith
    · simp only [hne, ite_false, mul_zero]
      positivity
  have hsum_int :
      (2 ^ k : ℤ) * ((∑ a ∈ nonemp, (3 * ((fib a).card - 1) + if Even (fib a).card then 1 else 0) : ℕ) : ℤ) ≤
      8 * (∑ a : Fin l, (grpLoss v r c (fib a) (fun x => out x a) : ℤ)) := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin l))) (fun a _ => hgrp a)
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 : (∑ a : Fin l, if a ∈ nonemp then
        (3 * ((fib a).card - 1 : ℕ) + if Even (fib a).card then (1 : ℤ) else 0) else 0) =
        ((∑ a ∈ nonemp, (3 * ((fib a).card - 1) + if Even (fib a).card then 1 else 0) : ℕ) : ℤ) := by
      rw [← Finset.sum_filter]
      have : (Finset.univ : Finset (Fin l)).filter (fun a => a ∈ nonemp) = nonemp := by
        ext a; simp
      rw [this]
      push_cast
      refine Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
    rw [h2] at h1
    exact h1
  have hsum_nat :
      2 ^ k * (∑ a ∈ nonemp, (3 * ((fib a).card - 1) + if Even (fib a).card then 1 else 0)) ≤
      8 * ∑ a : Fin l, grpLoss v r c (fib a) (fun x => out x a) := by
    exact_mod_cast hsum_int
  have hfib_sum : ∑ a ∈ nonemp, (fib a).card = m := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := label) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h0 : ∑ a ∈ Finset.univ.filter (fun a => ¬ (fib a).Nonempty), (fib a).card = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      have := (Finset.mem_filter.mp ha).2
      rw [Finset.not_nonempty_iff_eq_empty] at this
      simp [this]
    calc ∑ a ∈ nonemp, (fib a).card
        = ∑ a ∈ nonemp, (fib a).card + ∑ a ∈ Finset.univ.filter (fun a => ¬ (fib a).Nonempty), (fib a).card := by
          rw [h0, add_zero]
      _ = ∑ a : Fin l, (fib a).card := Finset.sum_filter_add_sum_filter_not _ _ _
      _ = m := by simpa [fib] using h1.symm
  have hsub_sum : ∑ a ∈ nonemp, ((fib a).card - 1) = m - nonemp.card := by
    have hge1 : ∀ a ∈ nonemp, 1 ≤ (fib a).card := fun a ha =>
      Finset.card_pos.mpr (Finset.mem_filter.mp ha).2
    have hadd : ∑ a ∈ nonemp, ((fib a).card - 1) + nonemp.card = m := by
      calc ∑ a ∈ nonemp, ((fib a).card - 1) + nonemp.card
          = ∑ a ∈ nonemp, ((fib a).card - 1) + ∑ _a ∈ nonemp, 1 := by simp
        _ = ∑ a ∈ nonemp, ((fib a).card - 1 + 1) := (Finset.sum_add_distrib).symm
        _ = ∑ a ∈ nonemp, (fib a).card := Finset.sum_congr rfl fun a ha => Nat.sub_add_cancel (hge1 a ha)
        _ = m := hfib_sum
    omega
  have hsplit : ∑ a ∈ nonemp, (3 * ((fib a).card - 1) + if Even (fib a).card then 1 else 0) =
      3 * (m - nonemp.card) + evenGrp.card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsub_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, smul_eq_mul, mul_one]
  have hne_le : nonemp.card ≤ l := by
    have := Finset.card_le_univ nonemp
    simpa using this
  have hcomb : 3 * (m - l) + (m - l) % 2 ≤ 3 * (m - nonemp.card) + evenGrp.card := by
    by_cases heq : nonemp.card = l
    · rw [heq]
      have hpar : (m - l) % 2 = evenGrp.card % 2 := by
        have hml_eq : m - l = ∑ a ∈ nonemp, ((fib a).card - 1) := by rw [hsub_sum, heq]
        rw [hml_eq, Finset.sum_nat_mod]
        have hcon : ∀ a ∈ nonemp, ((fib a).card - 1) % 2 = if Even (fib a).card then 1 else 0 := by
          intro a ha
          have hpos : 0 < (fib a).card := Finset.card_pos.mpr (Finset.mem_filter.mp ha).2
          by_cases h : Even (fib a).card
          · obtain ⟨q, hq⟩ := h; simp only [show Even (fib a).card from ⟨q, hq⟩, ite_true]; omega
          · rw [Nat.not_even_iff_odd] at h; obtain ⟨q, hq⟩ := h
            simp only [Nat.not_even_iff_odd.mpr ⟨q, hq⟩, ite_false]; omega
        rw [Finset.sum_congr rfl hcon, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]
      have hmod_le : evenGrp.card % 2 ≤ evenGrp.card := Nat.mod_le _ _
      omega
    · have hlt : nonemp.card < l := by omega
      have hmod : (m - l) % 2 ≤ 1 := by omega
      omega
  calc 2 ^ k * (3 * (m - l) + (m - l) % 2)
      ≤ 2 ^ k * (3 * (m - nonemp.card) + evenGrp.card) := Nat.mul_le_mul_left _ hcomb
    _ = 2 ^ k * (∑ a ∈ nonemp, (3 * ((fib a).card - 1) + if Even (fib a).card then 1 else 0)) := by
        rw [hsplit]
    _ ≤ 8 * ∑ a : Fin l, grpLoss v r c (fib a) (fun x => out x a) := hsum_nat

lemma exists_partition_sizes {m l : ℕ} (hl0 : 0 < l) (hlm : l ≤ m) (h3 : m ≤ 3 * l + 1) :
    ∃ label : Fin m → Fin l,
      (∀ a : Fin l, 1 ≤ (Finset.univ.filter fun j => label j = a).card ∧
        (Finset.univ.filter fun j => label j = a).card ≤ 4) ∧
      ((Finset.univ : Finset (Fin l)).filter fun a =>
        Even (Finset.univ.filter fun j => label j = a).card).card = (m - l) % 2 := by
  let q : ℕ := (m - l) / 2
  let rem : ℕ := (m - l) % 2
  have hmq : m = l + 2 * q + rem := by omega
  by_cases hrem : rem = 0
  · have hql : q ≤ l := by omega
    let label : Fin m → Fin l := fun j =>
      if h : j.val < 3 * q then ⟨j.val / 3, by omega⟩
      else ⟨q + (j.val - 3 * q), by omega⟩
    have hcard_fn : ∀ a : Fin l,
        (Finset.univ.filter fun j : Fin m => label j = a).card =
        if a.val < q then 3 else 1 := by
      intro a
      by_cases ha : a.val < q
      · simp only [ha, ite_true]
        have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
            {⟨3 * a.val, by omega⟩, ⟨3 * a.val + 1, by omega⟩, ⟨3 * a.val + 2, by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, label]
          constructor
          · intro h
            by_cases hj : j.val < 3 * q
            · simp only [hj, dite_true, Fin.ext_iff] at h
              have : j.val = 3 * a.val ∨ j.val = 3 * a.val + 1 ∨ j.val = 3 * a.val + 2 := by omega
              rcases this with h0 | h1 | h2
              · left; exact Fin.ext h0
              · right; left; exact Fin.ext h1
              · right; right; exact Fin.ext h2
            · simp only [hj, dite_false, Fin.ext_iff] at h; omega
          · rintro (rfl | rfl | rfl) <;> (dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega)
        rw [hset]; simp [Fin.ext_iff]
      · simp only [ha, ite_false]
        have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
            {⟨3 * q + (a.val - q), by omega⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, label]
          constructor
          · intro h
            by_cases hj : j.val < 3 * q
            · simp only [hj, dite_true, Fin.ext_iff] at h; omega
            · simp only [hj, dite_false, Fin.ext_iff] at h; exact Fin.ext (by dsimp only; omega)
          · rintro rfl
            dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega
        rw [hset]; simp
    refine ⟨label, fun a => by rw [hcard_fn a]; split_ifs <;> omega, ?_⟩
    have hempty : ((Finset.univ : Finset (Fin l)).filter fun a =>
        Even (Finset.univ.filter fun j => label j = a).card) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, hcard_fn a]
      split_ifs <;> decide
    rw [hempty, Finset.card_empty]
    exact hrem.symm
  · have hrem1 : rem = 1 := by omega
    by_cases hql : q < l
    · let label : Fin m → Fin l := fun j =>
        if h1 : j.val < 3 * q then ⟨j.val / 3, by omega⟩
        else if h2 : j.val < 3 * q + 2 then ⟨q, hql⟩
        else ⟨q + 1 + (j.val - (3 * q + 2)), by omega⟩
      have hcard_fn : ∀ a : Fin l,
          (Finset.univ.filter fun j : Fin m => label j = a).card =
          if a.val < q then 3 else if a.val = q then 2 else 1 := by
        intro a
        by_cases ha1 : a.val < q
        · simp only [ha1, ite_true]
          have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
              {⟨3 * a.val, by omega⟩, ⟨3 * a.val + 1, by omega⟩, ⟨3 * a.val + 2, by omega⟩} := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, label]
            constructor
            · intro h
              by_cases hj1 : j.val < 3 * q
              · simp only [hj1, dite_true, Fin.ext_iff] at h
                have : j.val = 3 * a.val ∨ j.val = 3 * a.val + 1 ∨ j.val = 3 * a.val + 2 := by omega
                rcases this with h0 | h1 | h2
                · left; exact Fin.ext h0
                · right; left; exact Fin.ext h1
                · right; right; exact Fin.ext h2
              · by_cases hj2 : j.val < 3 * q + 2
                · simp only [hj1, hj2, dite_false, dite_true, Fin.ext_iff] at h; omega
                · simp only [hj1, hj2, dite_false, Fin.ext_iff] at h; omega
            · rintro (rfl | rfl | rfl) <;> (dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega)
          rw [hset]; simp [Fin.ext_iff]
        · simp only [ha1, ite_false]
          by_cases ha2 : a.val = q
          · simp only [ha2, ite_true]
            have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
                {⟨3 * q, by omega⟩, ⟨3 * q + 1, by omega⟩} := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton, label]
              constructor
              · intro h
                by_cases hj1 : j.val < 3 * q
                · simp only [hj1, dite_true, Fin.ext_iff] at h; omega
                · by_cases hj2 : j.val < 3 * q + 2
                  · have : j.val = 3 * q ∨ j.val = 3 * q + 1 := by omega
                    rcases this with h0 | h1
                    · left; exact Fin.ext h0
                    · right; exact Fin.ext h1
                  · simp only [hj1, hj2, dite_false, Fin.ext_iff] at h; omega
              · rintro (rfl | rfl) <;> (dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega)
            rw [hset]; simp [Fin.ext_iff]
          · simp only [ha2, ite_false]
            have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
                {⟨3 * q + 2 + (a.val - (q + 1)), by omega⟩} := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, label]
              constructor
              · intro h
                by_cases hj1 : j.val < 3 * q
                · simp only [hj1, dite_true, Fin.ext_iff] at h; omega
                · by_cases hj2 : j.val < 3 * q + 2
                  · simp only [hj1, hj2, dite_false, dite_true, Fin.ext_iff] at h; omega
                  · simp only [hj1, hj2, dite_false, Fin.ext_iff] at h; exact Fin.ext (by dsimp only; omega)
              · rintro rfl
                dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega
            rw [hset]; simp
      refine ⟨label, fun a => by rw [hcard_fn a]; split_ifs <;> omega, ?_⟩
      have hsing : ((Finset.univ : Finset (Fin l)).filter fun a =>
          Even (Finset.univ.filter fun j => label j = a).card) = {⟨q, hql⟩} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hcard_fn a]
        split_ifs with h1 h2
        · simp [Fin.ext_iff, show ¬ Even (3 : ℕ) by decide]; omega
        · simp [Fin.ext_iff, show Even (2 : ℕ) by decide, h2]
        · simp [Fin.ext_iff, show ¬ Even (1 : ℕ) by decide, h2]
      rw [hsing, Finset.card_singleton]
      exact hrem1.symm
    · have hql_eq : q = l := by omega
      let label : Fin m → Fin l := fun j =>
        if h : j.val < 3 * (l - 1) then ⟨j.val / 3, by omega⟩
        else ⟨l - 1, by omega⟩
      have hcard_fn : ∀ a : Fin l,
          (Finset.univ.filter fun j : Fin m => label j = a).card =
          if a.val < l - 1 then 3 else 4 := by
        intro a
        by_cases ha : a.val < l - 1
        · simp only [ha, ite_true]
          have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
              {⟨3 * a.val, by omega⟩, ⟨3 * a.val + 1, by omega⟩, ⟨3 * a.val + 2, by omega⟩} := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, label]
            constructor
            · intro h
              by_cases hj : j.val < 3 * (l - 1)
              · simp only [hj, dite_true, Fin.ext_iff] at h
                have : j.val = 3 * a.val ∨ j.val = 3 * a.val + 1 ∨ j.val = 3 * a.val + 2 := by omega
                rcases this with h0 | h1 | h2
                · left; exact Fin.ext h0
                · right; left; exact Fin.ext h1
                · right; right; exact Fin.ext h2
              · simp only [hj, dite_false, Fin.ext_iff] at h; omega
            · rintro (rfl | rfl | rfl) <;> (dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega)
          rw [hset]; simp [Fin.ext_iff]
        · simp only [ha, ite_false]
          have hset : (Finset.univ.filter fun j : Fin m => label j = a) =
              {⟨3 * (l - 1), by omega⟩, ⟨3 * (l - 1) + 1, by omega⟩,
               ⟨3 * (l - 1) + 2, by omega⟩, ⟨3 * (l - 1) + 3, by omega⟩} := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, label]
            constructor
            · intro h
              by_cases hj : j.val < 3 * (l - 1)
              · simp only [hj, dite_true, Fin.ext_iff] at h; omega
              · have : j.val = 3 * (l - 1) ∨ j.val = 3 * (l - 1) + 1 ∨
                    j.val = 3 * (l - 1) + 2 ∨ j.val = 3 * (l - 1) + 3 := by omega
                rcases this with h0 | h1 | h2 | h3
                · left; exact Fin.ext h0
                · right; left; exact Fin.ext h1
                · right; right; left; exact Fin.ext h2
                · right; right; right; exact Fin.ext h3
            · rintro (rfl | rfl | rfl | rfl) <;> (dsimp only; split_ifs <;> simp [Fin.ext_iff] <;> omega)
          rw [hset]; simp [Fin.ext_iff]
      refine ⟨label, fun a => by rw [hcard_fn a]; split_ifs <;> omega, ?_⟩
      have hsing : ((Finset.univ : Finset (Fin l)).filter fun a =>
          Even (Finset.univ.filter fun j => label j = a).card) = {⟨l - 1, by omega⟩} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hcard_fn a]
        split_ifs with h1
        · simp [Fin.ext_iff, show ¬ Even (3 : ℕ) by decide]; omega
        · simp [Fin.ext_iff, show Even (4 : ℕ) by decide]; omega
      rw [hsing, Finset.card_singleton]
      exact hrem1.symm

lemma forward_achievable {k m l : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (h4 : ∀ S : Finset (Fin m), S.card = 4 → (∑ j ∈ S, v j) ≠ 0)
    (hl0 : 0 < l) (hlm : l ≤ m) (h3 : m ≤ 3 * l + 1)
    (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool) :
    ∃ (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool),
      8 * ((Finset.univ : Finset ((Fin k → ZMod 2) × Fin m)).filter (fun z =>
        out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
          (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card =
      2 ^ k * (3 * (m - l) + (m - l) % 2) := by
  obtain ⟨label, hsz, heven⟩ := exists_partition_sizes hl0 hlm h3
  let fib (a : Fin l) : Finset (Fin m) := Finset.univ.filter fun j => label j = a
  let out : (Fin k → ZMod 2) → Fin l → Bool := fun x a => majOut v r c (fib a) x
  refine ⟨label, out, ?_⟩
  rw [loss_eq_sum_grpLoss]
  have hgrp : ∀ a : Fin l,
      8 * (grpLoss v r c (fib a) (fun x => out x a) : ℤ) =
      (2 ^ k : ℤ) * (3 * ((fib a).card - 1 : ℕ) + if Even (fib a).card then 1 else 0) := by
    intro a
    have hmaj := grpLoss_maj v r c (fib a)
    have h14 : 1 ≤ (fib a).card ∧ (fib a).card ≤ 4 := hsz a
    have hcases : (fib a).card = 1 ∨ (fib a).card = 2 ∨ (fib a).card = 3 ∨ (fib a).card = 4 := by
      omega
    change 8 * (grpLoss v r c (fib a) (majOut v r c (fib a)) : ℤ) = _
    rcases hcases with h1 | h2 | h3c | h4c
    · have habs := sum_abs_eq_card1 v c (fib a) h1
      rw [h1] at hmaj ⊢
      have hne : ¬ Even (1 : ℕ) := by decide
      simp only [hne, ite_false]
      norm_num at hmaj habs ⊢
      linarith
    · have habs := sum_abs_eq_card2 v c (fib a) h2
      rw [h2] at hmaj ⊢
      have hev : Even (2 : ℕ) := by decide
      simp only [hev, ite_true]
      norm_num at hmaj habs ⊢
      linarith
    · have habs := sum_abs_eq_card3 v c (fib a) h3c
      rw [h3c] at hmaj ⊢
      have hne : ¬ Even (3 : ℕ) := by decide
      simp only [hne, ite_false]
      norm_num at hmaj habs ⊢
      linarith
    · have habs := sum_abs_eq_card4 v c h4 (fib a) h4c
      rw [h4c] at hmaj ⊢
      have hev : Even (4 : ℕ) := by decide
      simp only [hev, ite_true]
      norm_num at hmaj habs ⊢
      linarith
  have hfib_sum : ∑ a : Fin l, (fib a).card = m := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := label) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simpa using h1.symm
  have hsub_sum : ∑ a : Fin l, ((fib a).card - 1) = m - l := by
    have hadd : ∑ a : Fin l, ((fib a).card - 1) + l = m := by
      calc ∑ a : Fin l, ((fib a).card - 1) + l
          = ∑ a : Fin l, ((fib a).card - 1) + ∑ _a : Fin l, 1 := by simp
        _ = ∑ a : Fin l, ((fib a).card - 1 + 1) := (Finset.sum_add_distrib).symm
        _ = ∑ a : Fin l, (fib a).card := Finset.sum_congr rfl fun a _ => Nat.sub_add_cancel (hsz a).1
        _ = m := hfib_sum
    omega
  zify
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun a _ => hgrp a), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : (∑ a : Fin l, ((fib a).card - 1 : ℕ) : ℤ) = ((m - l : ℕ) : ℤ) := by
    norm_cast
  have h2 : (∑ a : Fin l, if Even (fib a).card then (1 : ℤ) else 0) = (((m - l) % 2 : ℕ) : ℤ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast heven
  rw [h1, h2]
  push_cast
  ring

lemma label_collapse {m : ℕ} (S : Finset (Fin m)) (hS : 1 ≤ S.card) :
    ∃ label : Fin m → Fin (m - S.card + 1),
      (Finset.univ.filter fun j => label j = ⟨0, by omega⟩) = S ∧
      ∀ a : Fin (m - S.card + 1), a ≠ ⟨0, by omega⟩ →
        (Finset.univ.filter fun j => label j = a).card = 1 := by
  let rest : Finset (Fin m) := Finset.univ \ S
  have hrest_card : rest.card = m - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  let e : rest ≃ Fin (m - S.card) := rest.equivFin.trans (finCongr hrest_card)
  let label : Fin m → Fin (m - S.card + 1) := fun j =>
    if hj : j ∈ S then ⟨0, by omega⟩
    else ⟨(e ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩).val + 1, by omega⟩
  refine ⟨label, ?_, ?_⟩
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, label]
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj, Fin.ext_iff]
  · intro a ha
    have ha0 : 0 < a.val := Nat.pos_of_ne_zero (fun h0 => ha (Fin.ext h0))
    let idx : Fin (m - S.card) := ⟨a.val - 1, by omega⟩
    let j0 : Fin m := (e.symm idx).1
    have hj0 : j0 ∉ S := (Finset.mem_sdiff.mp (e.symm idx).2).2
    have hset : (Finset.univ.filter fun j : Fin m => label j = a) = {j0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, label]
      constructor
      · intro h
        by_cases hj : j ∈ S
        · simp only [hj, dite_true, Fin.ext_iff] at h; omega
        · simp only [hj, dite_false, Fin.ext_iff] at h
          have heq : e ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩ = idx :=
            Fin.ext (by simp [idx]; omega)
          have := congrArg (fun z => (e.symm z).1) heq
          simpa [j0] using this
      · rintro rfl
        simp only [hj0, dite_false, Fin.ext_iff]
        have : e ⟨j0, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j0, hj0⟩⟩ = idx := by
          simp [j0]
        rw [this]
        simp [idx]
        omega
    rw [hset, Finset.card_singleton]

lemma prod_chi_finset {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2)) (c : Fin m → Bool)
    (S : Finset (Fin m)) (x : Fin k → ZMod 2) :
    (∏ j ∈ S, chi (c j) (v j) x) =
    chi (decide (Odd (S.filter fun j => c j = true).card)) (∑ j ∈ S, v j) x := by
  induction S using Finset.induction_on with
  | empty =>
    simp [chi, dot_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, chi_mul, Finset.sum_insert ha]
    congr 1
    rw [Finset.filter_insert]
    by_cases hca : c a = true
    · rw [if_pos hca, Finset.card_insert_of_notMem (by simp [ha]), hca]
      by_cases ho : Odd (s.filter fun j => c j = true).card
      · have hne : ¬ Odd ((s.filter fun j => c j = true).card + 1) := by
          obtain ⟨q, hq⟩ := ho; rw [hq, Nat.not_odd_iff_even]; exact ⟨q + 1, by ring⟩
        simp [ho, hne]
      · have hy : Odd ((s.filter fun j => c j = true).card + 1) := by
          rw [Nat.not_odd_iff_even] at ho; obtain ⟨q, hq⟩ := ho; exact ⟨q, by omega⟩
        simp [ho, hy]
    · have hcf : c a = false := Bool.eq_false_iff.mpr hca
      rw [if_neg hca, hcf]
      simp

lemma converse_dir {k m : ℕ} (v : Fin m ↪ (Fin k → ZMod 2))
    (h : ∀ (l : ℕ), 0 < l → l ≤ m →
      ∀ (r : (Fin k → ZMod 2) → Bool) (c : Fin m → Bool),
        let loss := fun (label : Fin m → Fin l) (out : (Fin k → ZMod 2) → Fin l → Bool) =>
          ((Finset.univ : Finset ((Fin k → ZMod 2) × Fin m)).filter (fun z =>
            out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
              (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card
        let price := 2 ^ k * (3 * (m - l) + (m - l) % 2)
        (∀ label out, price ≤ 8 * loss label out) ∧
          (m ≤ 3 * l + 1 → ∃ label out, 8 * loss label out = price)) :
    ∀ S : Finset (Fin m), S.card = 4 ∨ S.card = 6 → (∑ j ∈ S, v j) ≠ 0 := by
  have h4 : ∀ S : Finset (Fin m), S.card = 4 → (∑ j ∈ S, v j) ≠ 0 := by
    intro S hS4 hsum0
    have h4m : 4 ≤ m := by
      have := Finset.card_le_univ S
      simpa [hS4] using this
    let l : ℕ := m - 3
    have hl0 : 0 < l := by omega
    have hlm : l ≤ m := by omega
    obtain ⟨j0, hj0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    let r : (Fin k → ZMod 2) → Bool := fun _ => false
    let c : Fin m → Bool := fun j => decide (j = j0)
    have hfilt : S.filter (fun j => c j = true) = {j0} := by
      ext j; simp [c]; intro h; subst h; exact hj0
    obtain ⟨label, hlab0, hlab1⟩ := label_collapse S (by omega)
    have hl_eq : m - S.card + 1 = l := by omega
    let label' : Fin m → Fin l := fun j => finCongr hl_eq (label j)
    let fib (a : Fin l) : Finset (Fin m) := Finset.univ.filter fun j => label' j = a
    let out : (Fin k → ZMod 2) → Fin l → Bool := fun x a => majOut v r c (fib a) x
    have hbound := (h l hl0 hlm r c).1 label' out
    dsimp only at hbound
    rw [loss_eq_sum_grpLoss] at hbound
    have hfib0 : fib ⟨0, hl0⟩ = S := by
      rw [← hlab0]
      ext j
      simp only [fib, label', Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
        finCongr_apply, Fin.val_cast]
    have hfib_other : ∀ a : Fin l, a ≠ ⟨0, hl0⟩ → (fib a).card = 1 := by
      intro a ha
      have ha' : (finCongr hl_eq.symm a) ≠ ⟨0, by omega⟩ := by
        intro heq; apply ha; exact Fin.ext (by simpa [Fin.ext_iff] using heq)
      have hc := hlab1 (finCongr hl_eq.symm a) ha'
      convert hc using 2
      ext j
      simp [fib, label', Fin.ext_iff]
    have hloss_other : ∀ a : Fin l, a ≠ ⟨0, hl0⟩ → grpLoss v r c (fib a) (fun x => out x a) = 0 := by
      intro a ha
      show grpLoss v r c (fib a) (majOut v r c (fib a)) = 0
      have hmaj := grpLoss_maj v r c (fib a)
      have habs := sum_abs_eq_card1 v c (fib a) (hfib_other a ha)
      rw [hfib_other a ha] at hmaj
      have hzero : (grpLoss v r c (fib a) (majOut v r c (fib a)) : ℤ) = 0 := by
        norm_num at hmaj; linarith
      exact_mod_cast hzero
    have hsum_loss : ∑ a : Fin l, grpLoss v r c (fib a) (fun x => out x a) =
        grpLoss v r c S (fun x => out x ⟨0, hl0⟩) := by
      rw [Finset.sum_eq_single ⟨0, hl0⟩]
      · rw [hfib0]
      · intro a _ ha; exact hloss_other a ha
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum_loss] at hbound
    have hprod_neg : ∀ x : Fin k → ZMod 2, ∏ j ∈ S, chi (c j) (v j) x = -1 := by
      intro x
      rw [prod_chi_finset, hfilt, hsum0, Finset.card_singleton]
      simp [chi, dot_zero]
    have habs2 : ∀ x : Fin k → ZMod 2, |grpSum v c S x| = 2 := by
      intro x
      have hprod := hprod_neg x
      have hle := grpSum_abs_le v c S x
      have hev : Even (grpSum v c S x) := by
        obtain ⟨q, hq⟩ := grpSum_parity v c S x
        exact ⟨q + 2, by omega⟩
      have hneg_cnt : Odd (S.filter fun j => chi (c j) (v j) x = -1).card := by
        have h1 : ∏ j ∈ S, chi (c j) (v j) x = (-1 : ℤ) ^ (S.filter fun j => chi (c j) (v j) x = -1).card := by
          rw [← Finset.prod_filter_mul_prod_filter_not S (fun j => chi (c j) (v j) x = -1)]
          have hp1 : ∏ j ∈ S.filter (fun j => chi (c j) (v j) x = -1), chi (c j) (v j) x =
              (-1 : ℤ) ^ (S.filter fun j => chi (c j) (v j) x = -1).card := by
            rw [Finset.prod_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.prod_const]
          have hp2 : ∏ j ∈ S.filter (fun j => ¬ chi (c j) (v j) x = -1), chi (c j) (v j) x = 1 := by
            refine Finset.prod_eq_one fun j hj => ?_
            have hne := (Finset.mem_filter.mp hj).2
            simp only [chi] at hne ⊢
            split_ifs at hne ⊢
            · exact absurd rfl hne
            · rfl
          rw [hp1, hp2, mul_one]
        rw [h1] at hprod
        by_contra hne
        rw [Nat.not_odd_iff_even] at hne
        rw [Even.neg_one_pow hne] at hprod
        norm_num at hprod
      have hsum_neg : grpSum v c S x = (S.card : ℤ) - 2 * ((S.filter fun j => chi (c j) (v j) x = -1).card : ℤ) := by
        rw [grpSum, ← Finset.sum_filter_add_sum_filter_not S (fun j => chi (c j) (v j) x = -1)]
        have hs1 : ∑ j ∈ S.filter (fun j => chi (c j) (v j) x = -1), chi (c j) (v j) x =
            -((S.filter fun j => chi (c j) (v j) x = -1).card : ℤ) := by
          rw [Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.sum_const, nsmul_eq_mul]
          ring
        have hs2 : ∑ j ∈ S.filter (fun j => ¬ chi (c j) (v j) x = -1), chi (c j) (v j) x =
            ((S.filter fun j => ¬ chi (c j) (v j) x = -1).card : ℤ) := by
          have : ∀ j ∈ S.filter (fun j => ¬ chi (c j) (v j) x = -1), chi (c j) (v j) x = 1 := by
            intro j hj
            have hne := (Finset.mem_filter.mp hj).2
            simp only [chi] at hne ⊢
            split_ifs at hne ⊢
            · exact absurd rfl hne
            · rfl
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
        have htot : (S.filter fun j => chi (c j) (v j) x = -1).card +
            (S.filter fun j => ¬ chi (c j) (v j) x = -1).card = S.card := by
          rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
          have : ∀ j ∈ S, (if chi (c j) (v j) x = -1 then 1 else 0) +
              (if ¬ chi (c j) (v j) x = -1 then 1 else 0) = 1 := fun j _ => by split_ifs <;> rfl
          rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one]
        omega
      obtain ⟨q, hq⟩ := hneg_cnt
      have hq1 : q = 0 ∨ q = 1 := by
        have := Finset.card_filter_le S (fun j => chi (c j) (v j) x = -1)
        omega
      rcases hq1 with rfl | rfl <;> rw [hsum_neg, hS4, hq] <;> norm_num
    have hmaj := grpLoss_maj v r c S
    have hlossS : (grpLoss v r c S (majOut v r c S) : ℤ) = (2 ^ k : ℤ) := by
      simp_rw [habs2] at hmaj
      rw [hS4] at hmaj
      simp [Fintype.card_fun] at hmaj
      omega
    have hprice : m - l = 3 := by omega
    have hbound_int : (2 ^ k : ℤ) * 10 ≤ 8 * (grpLoss v r c S (majOut v r c S) : ℤ) := by
      have : 2 ^ k * (3 * (m - l) + (m - l) % 2) = 2 ^ k * 10 := by rw [hprice]
      rw [this] at hbound
      have hcast : (2 ^ k * 10 : ℕ) ≤ 8 * grpLoss v r c S (majOut v r c S) := by
        simpa [out, hfib0] using hbound
      exact_mod_cast hcast
    rw [hlossS] at hbound_int
    have h2k : (0 : ℤ) < 2 ^ k := by positivity
    linarith
  intro S hS46
  rcases hS46 with hS4 | hS6
  · exact h4 S hS4
  · intro hsum0
    have h6m : 6 ≤ m := by
      have := Finset.card_le_univ S
      simpa [hS6] using this
    let l : ℕ := m - 5
    have hl0 : 0 < l := by omega
    have hlm : l ≤ m := by omega
    let r : (Fin k → ZMod 2) → Bool := fun _ => false
    let c : Fin m → Bool := fun _ => false
    obtain ⟨label, hlab0, hlab1⟩ := label_collapse S (by omega)
    have hl_eq : m - S.card + 1 = l := by omega
    let label' : Fin m → Fin l := fun j => finCongr hl_eq (label j)
    let fib (a : Fin l) : Finset (Fin m) := Finset.univ.filter fun j => label' j = a
    let out : (Fin k → ZMod 2) → Fin l → Bool := fun x a => majOut v r c (fib a) x
    have hbound := (h l hl0 hlm r c).1 label' out
    dsimp only at hbound
    rw [loss_eq_sum_grpLoss] at hbound
    have hfib0 : fib ⟨0, hl0⟩ = S := by
      rw [← hlab0]
      ext j
      simp only [fib, label', Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
        finCongr_apply, Fin.val_cast]
    have hfib_other : ∀ a : Fin l, a ≠ ⟨0, hl0⟩ → (fib a).card = 1 := by
      intro a ha
      have ha' : (finCongr hl_eq.symm a) ≠ ⟨0, by omega⟩ := by
        intro heq; apply ha; exact Fin.ext (by simpa [Fin.ext_iff] using heq)
      have hc := hlab1 (finCongr hl_eq.symm a) ha'
      convert hc using 2
      ext j
      simp [fib, label', Fin.ext_iff]
    have hloss_other : ∀ a : Fin l, a ≠ ⟨0, hl0⟩ → grpLoss v r c (fib a) (fun x => out x a) = 0 := by
      intro a ha
      show grpLoss v r c (fib a) (majOut v r c (fib a)) = 0
      have hmaj := grpLoss_maj v r c (fib a)
      have habs := sum_abs_eq_card1 v c (fib a) (hfib_other a ha)
      rw [hfib_other a ha] at hmaj
      have hzero : (grpLoss v r c (fib a) (majOut v r c (fib a)) : ℤ) = 0 := by
        norm_num at hmaj; linarith
      exact_mod_cast hzero
    have hsum_loss : ∑ a : Fin l, grpLoss v r c (fib a) (fun x => out x a) =
        grpLoss v r c S (fun x => out x ⟨0, hl0⟩) := by
      rw [Finset.sum_eq_single ⟨0, hl0⟩]
      · rw [hfib0]
      · intro a _ ha; exact hloss_other a ha
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum_loss] at hbound
    have hprod_pos : ∀ x : Fin k → ZMod 2, ∏ j ∈ S, chi (c j) (v j) x = 1 := by
      intro x
      rw [prod_chi_finset, hsum0]
      simp [c, chi, dot_zero]
    have habs_eq : ∀ x : Fin k → ZMod 2, 8 * |grpSum v c S x| = (grpSum v c S x) ^ 2 + 12 := by
      intro x
      have hprod := hprod_pos x
      have hev_cnt : Even (S.filter fun j => chi (c j) (v j) x = -1).card := by
        have h1 : ∏ j ∈ S, chi (c j) (v j) x = (-1 : ℤ) ^ (S.filter fun j => chi (c j) (v j) x = -1).card := by
          rw [← Finset.prod_filter_mul_prod_filter_not S (fun j => chi (c j) (v j) x = -1)]
          have hp1 : ∏ j ∈ S.filter (fun j => chi (c j) (v j) x = -1), chi (c j) (v j) x =
              (-1 : ℤ) ^ (S.filter fun j => chi (c j) (v j) x = -1).card := by
            rw [Finset.prod_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.prod_const]
          have hp2 : ∏ j ∈ S.filter (fun j => ¬ chi (c j) (v j) x = -1), chi (c j) (v j) x = 1 := by
            refine Finset.prod_eq_one fun j hj => ?_
            have hne := (Finset.mem_filter.mp hj).2
            simp only [chi] at hne ⊢
            split_ifs at hne ⊢
            · exact absurd rfl hne
            · rfl
          rw [hp1, hp2, mul_one]
        rw [h1] at hprod
        by_contra hne
        rw [Nat.not_even_iff_odd] at hne
        rw [Odd.neg_one_pow hne] at hprod
        norm_num at hprod
      have hsum_neg : grpSum v c S x = (S.card : ℤ) - 2 * ((S.filter fun j => chi (c j) (v j) x = -1).card : ℤ) := by
        rw [grpSum, ← Finset.sum_filter_add_sum_filter_not S (fun j => chi (c j) (v j) x = -1)]
        have hs1 : ∑ j ∈ S.filter (fun j => chi (c j) (v j) x = -1), chi (c j) (v j) x =
            -((S.filter fun j => chi (c j) (v j) x = -1).card : ℤ) := by
          rw [Finset.sum_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.sum_const, nsmul_eq_mul]
          ring
        have hs2 : ∑ j ∈ S.filter (fun j => ¬ chi (c j) (v j) x = -1), chi (c j) (v j) x =
            ((S.filter fun j => ¬ chi (c j) (v j) x = -1).card : ℤ) := by
          have : ∀ j ∈ S.filter (fun j => ¬ chi (c j) (v j) x = -1), chi (c j) (v j) x = 1 := by
            intro j hj
            have hne := (Finset.mem_filter.mp hj).2
            simp only [chi] at hne ⊢
            split_ifs at hne ⊢
            · exact absurd rfl hne
            · rfl
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
        have htot : (S.filter fun j => chi (c j) (v j) x = -1).card +
            (S.filter fun j => ¬ chi (c j) (v j) x = -1).card = S.card := by
          rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
          have : ∀ j ∈ S, (if chi (c j) (v j) x = -1 then 1 else 0) +
              (if ¬ chi (c j) (v j) x = -1 then 1 else 0) = 1 := fun j _ => by split_ifs <;> rfl
          rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one]
        omega
      obtain ⟨q, hq⟩ := hev_cnt
      have hq3 : q ≤ 3 := by
        have := Finset.card_filter_le S (fun j => chi (c j) (v j) x = -1)
        omega
      rw [hsum_neg, hS6, hq]
      interval_cases q <;> norm_num
    have hsum_abs : 8 * (∑ x : Fin k → ZMod 2, |grpSum v c S x|) = (2 ^ k : ℤ) * 18 := by
      calc 8 * (∑ x : Fin k → ZMod 2, |grpSum v c S x|)
          = ∑ x : Fin k → ZMod 2, 8 * |grpSum v c S x| := by rw [Finset.mul_sum]
        _ = ∑ x : Fin k → ZMod 2, ((grpSum v c S x) ^ 2 + 12) := by simp_rw [habs_eq]
        _ = (∑ x, (grpSum v c S x) ^ 2) + ∑ _x : Fin k → ZMod 2, (12 : ℤ) := Finset.sum_add_distrib
        _ = (2 ^ k : ℤ) * 18 := by
            rw [sum_sq_grpSum, hS6]
            simp [Fintype.card_fun]
            ring
    have hmaj := grpLoss_maj v r c S
    rw [hS6] at hmaj
    norm_num at hmaj
    have hprice : m - l = 5 := by omega
    have hbound_int : (2 ^ k : ℤ) * 16 ≤ 8 * (grpLoss v r c S (majOut v r c S) : ℤ) := by
      have : 2 ^ k * (3 * (m - l) + (m - l) % 2) = 2 ^ k * 16 := by rw [hprice]
      rw [this] at hbound
      have hcast : (2 ^ k * 16 : ℕ) ≤ 8 * grpLoss v r c S (majOut v r c S) := by
        simpa [out, hfib0] using hbound
      exact_mod_cast hcast
    have h2k : (0 : ℤ) < 2 ^ k := by positivity
    norm_num at hmaj
    linarith

end PEqualNP.Outside.L_meta_25936

theorem PEqualNP.Outside.L_meta_25936 : ∀ (k m : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  ∀ v : Fin m ↪ V,
    (∀ S : Finset (Fin m), S.card = 4 ∨ S.card = 6 → (∑ j ∈ S, v j) ≠ 0) ↔
    ∀ (l : ℕ), 0 < l → l ≤ m →
      ∀ (r : V → Bool) (c : Fin m → Bool),
        let loss := fun (label : Fin m → Fin l) (out : V → Fin l → Bool) =>
          ((Finset.univ : Finset (V × Fin m)).filter (fun z =>
            out z.1 (label z.2) ≠ Bool.xor (Bool.xor (r z.1) (c z.2))
              (decide ((∑ i : Fin k, z.1 i * v z.2 i) = 1)))).card
        let price := 2^k * (3*(m-l) + (m-l)%2)
        (∀ label out, price ≤ 8*loss label out) ∧
          (m ≤ 3*l+1 → ∃ label out, 8*loss label out = price) := by
  open PEqualNP.Outside.L_meta_25936 in
  intro k m F V v
  constructor
  · intro h46 l hl0 hlm r c
    exact ⟨fun label out => forward_lower v h46 hlm r c label out,
      fun h3 => forward_achievable v (fun S h => h46 S (Or.inl h)) hl0 hlm h3 r c⟩
  · exact converse_dir v
