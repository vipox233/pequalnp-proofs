import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1166_aux

open scoped BigOperators

/-! ### Part A: Single-block (Fin 16) Walsh spectrum modulo 11 -/

def localPass (opp : Bool) (z x : Fin 16) : Bool :=
  let w := z.val ^^^ x.val
  (w &&& 3) != 0 && (w &&& 13) != (if opp then 1 else 0)

def chi16 (a b : Fin 16) : ℤ :=
  (-1 : ℤ) ^ ((Finset.univ : Finset (Fin 4)).filter
    (fun k => a.val.testBit k.val && b.val.testBit k.val)).card

def ev16 (opp : Bool) (t : Fin 16) : ℤ :=
  (Finset.univ : Finset (Fin 16)).sum (fun x =>
    if localPass opp 0 x = true then chi16 x t else 0)

def localSupp (opp : Bool) (t : Fin 16) : Bool :=
  decide ((ev16 opp t) % 11 ≠ 0)

def suppFalse : Finset (Fin 16) :=
  (Finset.univ : Finset (Fin 16)).filter (fun t => localSupp false t = true)

def suppTrue : Finset (Fin 16) :=
  (Finset.univ : Finset (Fin 16)).filter (fun t => localSupp true t = true)

def suppBoth : Finset (Fin 16) := suppFalse ∩ suppTrue
def suppOnlyFalse : Finset (Fin 16) := suppFalse \ suppTrue
def suppOnlyTrue : Finset (Fin 16) := suppTrue \ suppFalse

lemma localPass_symm : ∀ (opp : Bool) (z x : Fin 16), localPass opp z x = localPass opp x z := by
  decide

lemma local_walsh_orth : ∀ (x y : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun t => chi16 x t * chi16 y t) =
    if x = y then 16 else 0 := by
  decide

lemma local_walsh_conv : ∀ (opp : Bool) (z t : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun x =>
      if localPass opp z x = true then chi16 x t else 0) =
    ev16 opp t * chi16 z t := by
  decide

lemma card_suppFalse : suppFalse.card = 15 := by decide
lemma card_suppTrue : suppTrue.card = 10 := by decide
lemma card_suppBoth : suppBoth.card = 9 := by decide
lemma card_suppOnlyFalse : suppOnlyFalse.card = 6 := by decide
lemma card_suppOnlyTrue : suppOnlyTrue.card = 1 := by decide

lemma supp_cover : ∀ t : Fin 16, t ∈ suppFalse ∨ t ∈ suppTrue := by decide

lemma chi16_comm : ∀ a b : Fin 16, chi16 a b = chi16 b a := by decide

lemma zmod11_9_mul_16 : (9 : ZMod 11) * (16 : ZMod 11) = 1 := by decide

lemma prime_11 : Nat.Prime 11 := by decide

lemma ev16_zmod_ne_zero_iff (opp : Bool) (t : Fin 16) :
    ((ev16 opp t : ℤ) : ZMod 11) ≠ 0 ↔ localSupp opp t = true := by
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  simp [localSupp]

/-! ### Part B: Multi-block pass, Walsh transform, and exact kernel size -/

noncomputable def passOf {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))

lemma passOf_iff {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    passOf e z x = true ↔ ∀ j : Fin r, localPass (decide (j ∈ e)) (z j) (x j) = true := by
  simp only [passOf, List.all_eq_true, Finset.mem_toList, Finset.mem_univ, forall_true_left]
  refine forall_congr' fun j => ?_
  dsimp only [localPass]
  by_cases hj : j ∈ e <;> simp [hj]

lemma passOf_symm {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    passOf e z x = passOf e x z := by
  apply Bool.eq_iff_iff.mpr
  rw [passOf_iff, passOf_iff]
  refine forall_congr' fun j => ?_
  rw [localPass_symm]

lemma passOf_indicator {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    (if passOf e z x = true then (1 : ZMod 11) else 0) =
    ∏ j : Fin r, if localPass (decide (j ∈ e)) (z j) (x j) = true then (1 : ZMod 11) else 0 := by
  by_cases hp : passOf e z x = true
  · rw [if_pos hp]
    exact (Finset.prod_eq_one fun j _ => if_pos ((passOf_iff e z x).mp hp j)).symm
  · rw [if_neg hp]
    have hex : ∃ j : Fin r, localPass (decide (j ∈ e)) (z j) (x j) ≠ true := by
      by_contra hall; push Not at hall
      exact hp ((passOf_iff e z x).mpr hall)
    rcases hex with ⟨j, hj⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)).symm

def chiW {r : ℕ} (x t : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, ((chi16 (x j) (t j) : ℤ) : ZMod 11)

def wht {r : ℕ} (d : (Fin r → Fin 16) → ZMod 11) (t : Fin r → Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * chiW x t)

def whtInv {r : ℕ} (f : (Fin r → Fin 16) → ZMod 11) (x : Fin r → Fin 16) : ZMod 11 :=
  (9 : ZMod 11) ^ r * wht f x

lemma sum_chiW_mul {r : ℕ} (x y : Fin r → Fin 16) :
    (Finset.univ : Finset (Fin r → Fin 16)).sum (fun t => chiW x t * chiW y t) =
    if x = y then (16 : ZMod 11) ^ r else 0 := by
  have hprod : ∀ t : Fin r → Fin 16,
      chiW x t * chiW y t = ∏ j : Fin r, (((chi16 (x j) (t j) * chi16 (y j) (t j) : ℤ)) : ZMod 11) := by
    intro t
    dsimp only [chiW]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => by push_cast; rfl
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j a => (((chi16 (x j) a * chi16 (y j) a : ℤ)) : ZMod 11))]
  have hloc : ∀ j : Fin r,
      (Finset.univ : Finset (Fin 16)).sum (fun a => (((chi16 (x j) a * chi16 (y j) a : ℤ)) : ZMod 11)) =
      if x j = y j then (16 : ZMod 11) else 0 := by
    intro j
    rw [← Int.cast_sum, local_walsh_orth]
    split_ifs <;> simp
  simp_rw [hloc]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy]
    have hex : ∃ j : Fin r, x j ≠ y j := by
      by_contra hall; push Not at hall; exact hxy (funext hall)
    rcases hex with ⟨j, hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

lemma wht_wht {r : ℕ} (d : (Fin r → Fin 16) → ZMod 11) (y : Fin r → Fin 16) :
    wht (wht d) y = (16 : ZMod 11) ^ r * d y := by
  dsimp only [wht]
  have h1 : (Finset.univ : Finset (Fin r → Fin 16)).sum
      (fun t => ((Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * chiW x t)) * chiW t y) =
      (Finset.univ : Finset (Fin r → Fin 16)).sum
        (fun x => d x * (Finset.univ : Finset (Fin r → Fin 16)).sum (fun t => chiW x t * chiW y t)) := by
    have hmul : ∀ t : Fin r → Fin 16,
        ((Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * chiW x t)) * chiW t y =
        (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * (chiW x t * chiW y t)) := by
      intro t
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hsym : chiW t y = chiW y t := by
        dsimp only [chiW]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [chi16_comm]
      rw [hsym, mul_assoc]
    simp_rw [hmul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm
  rw [h1]
  simp_rw [sum_chiW_mul]
  rw [Finset.sum_eq_single y]
  · simp [mul_comm]
  · intro x _ hxy; simp [hxy]
  · intro h; exact absurd (Finset.mem_univ y) h

lemma wht_bijective (r : ℕ) : Function.Bijective (wht (r := r)) := by
  have h916 : (9 : ZMod 11) * (16 : ZMod 11) = 1 := zmod11_9_mul_16
  refine ⟨?_, ?_⟩
  · intro d₁ d₂ hEq
    funext y
    have h1 := congrFun (congrArg wht hEq) y
    rw [wht_wht, wht_wht] at h1
    have hmul := congrArg (fun v => (9 : ZMod 11) ^ r * v) h1
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, h916, one_pow, one_mul, one_mul] at hmul
    exact hmul
  · intro f
    refine ⟨whtInv f, ?_⟩
    funext t
    dsimp only [whtInv, wht]
    have hpull : (Finset.univ : Finset (Fin r → Fin 16)).sum
        (fun x => ((9 : ZMod 11) ^ r * (Finset.univ : Finset (Fin r → Fin 16)).sum (fun u => f u * chiW u x)) * chiW x t) =
        (9 : ZMod 11) ^ r * wht (wht f) t := by
      unfold wht
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hpull, wht_wht, ← mul_assoc, ← mul_pow, h916, one_pow, one_mul]

def evW {r : ℕ} (e : Finset (Fin r)) (t : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, ((ev16 (decide (j ∈ e)) (t j) : ℤ) : ZMod 11)

noncomputable def convW {r : ℕ} (e : Finset (Fin r)) (d : (Fin r → Fin 16) → ZMod 11)
    (z : Fin r → Fin 16) : ZMod 11 :=
  ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf e z x = true)).sum d

lemma wht_convW {r : ℕ} (e : Finset (Fin r)) (d : (Fin r → Fin 16) → ZMod 11) (t : Fin r → Fin 16) :
    wht (convW e d) t = evW e t * wht d t := by
  dsimp only [wht, convW]
  have h1 : (Finset.univ : Finset (Fin r → Fin 16)).sum
      (fun z => ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf e z x = true)).sum d * chiW z t) =
      (Finset.univ : Finset (Fin r → Fin 16)).sum
        (fun x => d x * ((Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
          if passOf e x z = true then chiW z t else 0))) := by
    have hinner : ∀ z : Fin r → Fin 16,
        ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf e z x = true)).sum d * chiW z t =
        (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x =>
          if passOf e x z = true then d x * chiW z t else 0) := by
      intro z
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => by rw [passOf_symm]; split_ifs <;> simp
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
  rw [h1]
  have heval : ∀ x : Fin r → Fin 16,
      (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z => if passOf e x z = true then chiW z t else 0) =
      evW e t * chiW x t := by
    intro x
    have hprod : ∀ z : Fin r → Fin 16,
        (if passOf e x z = true then chiW z t else 0) =
        ∏ j : Fin r, if localPass (decide (j ∈ e)) (x j) (z j) = true then ((chi16 (z j) (t j) : ℤ) : ZMod 11) else 0 := by
      intro z
      have hmul : (if passOf e x z = true then chiW z t else 0) =
          (if passOf e x z = true then (1 : ZMod 11) else 0) * chiW z t := by split_ifs <;> simp
      rw [hmul, passOf_indicator]
      dsimp only [chiW]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun j a =>
      if localPass (decide (j ∈ e)) (x j) a = true then ((chi16 a (t j) : ℤ) : ZMod 11) else 0)]
    have hloc : ∀ j : Fin r,
        (Finset.univ : Finset (Fin 16)).sum (fun a =>
          if localPass (decide (j ∈ e)) (x j) a = true then ((chi16 a (t j) : ℤ) : ZMod 11) else 0) =
        ((ev16 (decide (j ∈ e)) (t j) : ℤ) : ZMod 11) * ((chi16 (x j) (t j) : ℤ) : ZMod 11) := by
      intro j
      have hcast : (Finset.univ : Finset (Fin 16)).sum (fun a =>
          if localPass (decide (j ∈ e)) (x j) a = true then ((chi16 a (t j) : ℤ) : ZMod 11) else 0) =
          (((Finset.univ : Finset (Fin 16)).sum (fun a =>
            if localPass (decide (j ∈ e)) (x j) a = true then chi16 a (t j) else 0) : ℤ) : ZMod 11) := by
        rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      rw [hcast, local_walsh_conv]
      push_cast; rfl
    simp_rw [hloc, Finset.prod_mul_distrib]
    rfl
  simp_rw [heval]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

def seenOf {r : ℕ} (e : Finset (Fin r)) : Finset (Fin r → Fin 16) :=
  Fintype.piFinset (fun j => if j ∈ e then suppTrue else suppFalse)

lemma mem_seenOf_iff {r : ℕ} (e : Finset (Fin r)) (t : Fin r → Fin 16) :
    t ∈ seenOf e ↔ evW e t ≠ 0 := by
  have : Fact (Nat.Prime 11) := ⟨prime_11⟩
  simp only [seenOf, Fintype.mem_piFinset, evW, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]
  refine forall_congr' fun j => ?_
  rw [ev16_zmod_ne_zero_iff]
  by_cases hj : j ∈ e <;> simp [hj, suppTrue, suppFalse]

def seenMenu {r : ℕ} (M : Finset (Finset (Fin r))) : Finset (Fin r → Fin 16) :=
  M.biUnion seenOf

def missedMenu {r : ℕ} (M : Finset (Finset (Fin r))) : Finset (Fin r → Fin 16) :=
  (Finset.univ : Finset (Fin r → Fin 16)) \ seenMenu M

lemma card_missedMenu_add_seenMenu {r : ℕ} (M : Finset (Finset (Fin r))) :
    (missedMenu M).card + (seenMenu M).card = 16 ^ r := by
  have hsub : seenMenu M ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.card_sdiff_add_card_eq_card hsub
  simpa [missedMenu, Fintype.card_fin] using h

lemma kernelSize_eq_pow {r : ℕ} (M : Finset (Finset (Fin r))) :
    ((Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf q.1 q.2 x = true)).sum
          (fun x => (d x).val)) % 11 = 0)).card =
    11 ^ (missedMenu M).card := by
  classical
  have : Fact (Nat.Prime 11) := ⟨prime_11⟩
  let toZ : ((Fin r → Fin 16) → Fin 11) → ((Fin r → Fin 16) → ZMod 11) := fun d x => ((d x).val : ZMod 11)
  have htoZ_bij : Function.Bijective toZ := by
    refine ⟨fun d₁ d₂ h => funext fun x => ?_, fun f => ⟨fun x => ⟨(f x).val, ZMod.val_lt (f x)⟩, funext fun x => ?_⟩⟩
    · have hx := congrFun h x
      dsimp only [toZ] at hx
      have h1 := ZMod.val_natCast_of_lt (n := 11) (d₁ x).isLt
      have h2 := ZMod.val_natCast_of_lt (n := 11) (d₂ x).isLt
      exact Fin.ext (by rw [← h1, hx, h2])
    · dsimp only [toZ]; exact ZMod.natCast_zmod_val (f x)
  let phi : ((Fin r → Fin 16) → Fin 11) → ((Fin r → Fin 16) → ZMod 11) := fun d => wht (toZ d)
  have hphi_bij : Function.Bijective phi := (wht_bijective r).comp htoZ_bij
  have hker_iff : ∀ d : (Fin r → Fin 16) → Fin 11,
      (∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf q.1 q.2 x = true)).sum
          (fun x => (d x).val)) % 11 = 0) ↔
      (∀ t ∈ seenMenu M, phi d t = 0) := by
    intro d
    have hstep1 : (∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf q.1 q.2 x = true)).sum
          (fun x => (d x).val)) % 11 = 0) ↔
        (∀ e ∈ M, convW e (toZ d) = 0) := by
      constructor
      · intro h e he
        funext z
        have hq := h (e, z) (Finset.mem_product.mpr ⟨he, Finset.mem_univ z⟩)
        dsimp only [convW, toZ]
        rw [Pi.zero_apply, ← Nat.cast_sum, ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero hq
      · intro h q hq
        rcases Finset.mem_product.mp hq with ⟨hq1, _⟩
        have hz := congrFun (h q.1 hq1) q.2
        dsimp only [convW, toZ, Pi.zero_apply] at hz
        rw [← Nat.cast_sum, ZMod.natCast_eq_zero_iff] at hz
        exact Nat.mod_eq_zero_of_dvd hz
    rw [hstep1]
    have hstep2 : (∀ e ∈ M, convW e (toZ d) = 0) ↔ (∀ e ∈ M, wht (convW e (toZ d)) = 0) := by
      refine forall₂_congr fun e _ => ?_
      have hzero : wht (r := r) 0 = 0 := by funext t; simp [wht]
      constructor
      · intro h; rw [h, hzero]
      · intro h; exact (wht_bijective r).1 (h.trans hzero.symm)
    rw [hstep2]
    constructor
    · intro h t ht
      rcases Finset.mem_biUnion.mp ht with ⟨e, he, hte⟩
      have hev : evW e t ≠ 0 := (mem_seenOf_iff e t).mp hte
      have h0 := congrFun (h e he) t
      rw [wht_convW, Pi.zero_apply, mul_eq_zero] at h0
      exact h0.resolve_left hev
    · intro h e he
      funext t
      rw [wht_convW, Pi.zero_apply]
      by_cases hev : evW e t = 0
      · rw [hev, zero_mul]
      · have hte : t ∈ seenOf e := (mem_seenOf_iff e t).mpr hev
        have htm : t ∈ seenMenu M := Finset.mem_biUnion.mpr ⟨e, he, hte⟩
        rw [show wht (toZ d) t = phi d t from rfl, h t htm, mul_zero]
  -- Biject the kernel with ({t // t ∈ missedMenu M} → ZMod 11)
  let restrict : ((Fin r → Fin 16) → Fin 11) → ({t // t ∈ missedMenu M} → ZMod 11) :=
    fun d t => phi d t.1
  have hcard_eq : ((Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf q.1 q.2 x = true)).sum
          (fun x => (d x).val)) % 11 = 0)).card =
      (Finset.univ : Finset ({t // t ∈ missedMenu M} → ZMod 11)).card := by
    refine Finset.card_bij (fun d _ => restrict d) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro d₁ hd₁ d₂ hd₂ hEq
      have h1 := (hker_iff d₁).mp (Finset.mem_filter.mp hd₁).2
      have h2 := (hker_iff d₂).mp (Finset.mem_filter.mp hd₂).2
      apply hphi_bij.1
      funext t
      by_cases ht : t ∈ seenMenu M
      · rw [h1 t ht, h2 t ht]
      · have htm : t ∈ missedMenu M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ht⟩
        exact congrFun hEq ⟨t, htm⟩
    · intro g _
      let f : (Fin r → Fin 16) → ZMod 11 := fun t =>
        if ht : t ∈ missedMenu M then g ⟨t, ht⟩ else 0
      rcases hphi_bij.2 f with ⟨d, hd⟩
      have hd_ker : ∀ t ∈ seenMenu M, phi d t = 0 := by
        intro t ht
        rw [hd]
        have hnot : t ∉ missedMenu M := fun hm => (Finset.mem_sdiff.mp hm).2 ht
        simp [f, hnot]
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, (hker_iff d).mpr hd_ker⟩, ?_⟩
      funext ⟨t, ht⟩
      dsimp only [restrict]
      rw [hd]
      simp [f, ht]
  rw [hcard_eq]
  simp

/-! ### Part C: Claim 1 (Optimal pairs of signing types, M.card = 2) -/

lemma card_seenOf {r : ℕ} (e : Finset (Fin r)) :
    (seenOf e).card = 10 ^ e.card * 15 ^ (r - e.card) := by
  classical
  rw [seenOf, Fintype.card_piFinset]
  have h1 : (Finset.univ : Finset (Fin r)).prod (fun j => (if j ∈ e then suppTrue else suppFalse).card) =
      (Finset.univ : Finset (Fin r)).prod (fun j => if j ∈ e then 10 else 15) :=
    Finset.prod_congr rfl fun j _ => by by_cases hj : j ∈ e <;> simp [hj, card_suppTrue, card_suppFalse]
  rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hf1 : (Finset.univ.filter (fun j : Fin r => j ∈ e)).card = e.card := by
    congr 1; ext j; simp
  have hf2 : (Finset.univ.filter (fun j : Fin r => j ∉ e)).card = r - e.card := by
    have hcompl : Finset.univ.filter (fun j : Fin r => j ∉ e) = Finset.univ \ e := by
      ext j; simp
    rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [hf1, hf2]

lemma card_seenOf_inter {r : ℕ} (e₁ e₂ : Finset (Fin r)) :
    (seenOf e₁ ∩ seenOf e₂).card =
    10 ^ (e₁ ∩ e₂).card * 15 ^ ((Finset.univ : Finset (Fin r)) \ (e₁ ∪ e₂)).card *
      9 ^ ((e₁ \ e₂).card + (e₂ \ e₁).card) := by
  classical
  have hinter : seenOf e₁ ∩ seenOf e₂ =
      Fintype.piFinset (fun j => (if j ∈ e₁ then suppTrue else suppFalse) ∩
        (if j ∈ e₂ then suppTrue else suppFalse)) := by
    ext t
    simp only [Finset.mem_inter, seenOf, Fintype.mem_piFinset]
    constructor
    · intro h j; exact ⟨h.1 j, h.2 j⟩
    · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2⟩
  rw [hinter, Fintype.card_piFinset]
  let A := e₁ ∩ e₂
  let B := (e₁ \ e₂) ∪ (e₂ \ e₁)
  let C := (Finset.univ : Finset (Fin r)) \ (e₁ ∪ e₂)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [A, B, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at h1 h2
    tauto
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [A, C, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union] at h1 h2
    tauto
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [B, C, Finset.mem_union, Finset.mem_sdiff] at h1 h2
    tauto
  have huniv : (Finset.univ : Finset (Fin r)) = A ∪ (B ∪ C) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_union, A, B, C, Finset.mem_inter, Finset.mem_sdiff, true_iff]
    by_cases h1 : j ∈ e₁ <;> by_cases h2 : j ∈ e₂ <;> tauto
  conv_lhs => rw [huniv]
  rw [Finset.prod_union (Finset.disjoint_union_right.mpr ⟨hAB, hAC⟩), Finset.prod_union hBC]
  have hPA : A.prod (fun j => ((if j ∈ e₁ then suppTrue else suppFalse) ∩
      (if j ∈ e₂ then suppTrue else suppFalse)).card) = 10 ^ A.card := by
    calc A.prod (fun j => ((if j ∈ e₁ then suppTrue else suppFalse) ∩
          (if j ∈ e₂ then suppTrue else suppFalse)).card)
        = A.prod (fun _ => 10) := Finset.prod_congr rfl fun j hj => by
            rcases Finset.mem_inter.mp hj with ⟨h1, h2⟩
            simp [h1, h2, card_suppTrue]
      _ = 10 ^ A.card := Finset.prod_const 10
  have hPC : C.prod (fun j => ((if j ∈ e₁ then suppTrue else suppFalse) ∩
      (if j ∈ e₂ then suppTrue else suppFalse)).card) = 15 ^ C.card := by
    calc C.prod (fun j => ((if j ∈ e₁ then suppTrue else suppFalse) ∩
          (if j ∈ e₂ then suppTrue else suppFalse)).card)
        = C.prod (fun _ => 15) := Finset.prod_congr rfl fun j hj => by
            have hnot : j ∉ e₁ ∧ j ∉ e₂ := by
              have := (Finset.mem_sdiff.mp hj).2
              simpa [Finset.mem_union] using this
            simp [hnot.1, hnot.2, card_suppFalse]
      _ = 15 ^ C.card := Finset.prod_const 15
  have hPB : B.prod (fun j => ((if j ∈ e₁ then suppTrue else suppFalse) ∩
      (if j ∈ e₂ then suppTrue else suppFalse)).card) = 9 ^ B.card := by
    calc B.prod (fun j => ((if j ∈ e₁ then suppTrue else suppFalse) ∩
          (if j ∈ e₂ then suppTrue else suppFalse)).card)
        = B.prod (fun _ => 9) := Finset.prod_congr rfl fun j hj => by
            rcases Finset.mem_union.mp hj with h1 | h2
            · rcases Finset.mem_sdiff.mp h1 with ⟨ha, hb⟩
              have hcomm : suppTrue ∩ suppFalse = suppBoth := Finset.inter_comm _ _
              simp [ha, hb, hcomm, card_suppBoth]
            · rcases Finset.mem_sdiff.mp h2 with ⟨ha, hb⟩
              simp [ha, hb, show suppFalse ∩ suppTrue = suppBoth from rfl, card_suppBoth]
      _ = 9 ^ B.card := Finset.prod_const 9
  have hBcard : B.card = (e₁ \ e₂).card + (e₂ \ e₁).card := by
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]; intro j h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  rw [hPA, hPB, hPC, hBcard]
  dsimp only [A, C]
  ring

lemma nine_pow_le_95_mul_fifteen (d : ℕ) (hd : 3 ≤ d) :
    9 ^ d ≤ 95 * 15 ^ (d - 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsub : k + 1 - 2 = (k - 2) + 1 := by omega
    rw [hsub, pow_succ, pow_succ]
    have h1 : 9 ^ k * 9 ≤ 95 * 15 ^ (k - 2) * 9 := Nat.mul_le_mul_right 9 ih
    have h2 : 95 * 15 ^ (k - 2) * 9 ≤ 95 * (15 ^ (k - 2) * 15) := by
      have : 95 * 15 ^ (k - 2) * 9 ≤ 95 * 15 ^ (k - 2) * 15 :=
        Nat.mul_le_mul_left _ (by omega)
      linarith
    exact le_trans h1 h2

lemma ten_pow_lt_nine_pow_add_19 (d : ℕ) (hd : 3 ≤ d) :
    10 ^ d < 9 ^ d + 19 * 15 ^ (d - 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsub : k + 1 - 2 = (k - 2) + 1 := by omega
    rw [hsub, pow_succ, pow_succ, pow_succ]
    have h9 := nine_pow_le_95_mul_fifteen k hk
    have h10 : 10 ^ k * 10 < (9 ^ k + 19 * 15 ^ (k - 2)) * 10 := by
      have := Nat.mul_lt_mul_of_pos_right ih (by omega : 0 < 10)
      exact this
    linarith

lemma pair_convexity (b₁ b₂ : ℕ) :
    10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ ≤ 15 ^ (b₁ + b₂) + 10 ^ (b₁ + b₂) ∧
    (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ = 15 ^ (b₁ + b₂) + 10 ^ (b₁ + b₂) ↔
      b₁ = 0 ∨ b₂ = 0) := by
  have h1 : 10 ^ b₁ ≤ 15 ^ b₁ := Nat.pow_le_pow_left (by omega) b₁
  have h2 : 10 ^ b₂ ≤ 15 ^ b₂ := Nat.pow_le_pow_left (by omega) b₂
  have hid : (15 ^ b₁ - 10 ^ b₁) * (15 ^ b₂ - 10 ^ b₂) + (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁) =
      15 ^ (b₁ + b₂) + 10 ^ (b₁ + b₂) := by
    zify [h1, h2]
    rw [pow_add, pow_add]
    ring
  refine ⟨by omega, ?_⟩
  constructor
  · intro heq
    have hzero : (15 ^ b₁ - 10 ^ b₁) * (15 ^ b₂ - 10 ^ b₂) = 0 := by omega
    rcases mul_eq_zero.mp hzero with hz1 | hz2
    · left
      by_contra hne
      have hlt : 10 ^ b₁ < 15 ^ b₁ := Nat.pow_lt_pow_left (by omega) hne
      omega
    · right
      by_contra hne
      have hlt : 10 ^ b₂ < 15 ^ b₂ := Nat.pow_lt_pow_left (by omega) hne
      omega
  · rintro (rfl | rfl) <;> simp [add_comm]

lemma pair_seen_bound {r : ℕ} (hr : 2 ≤ r) (e₁ e₂ : Finset (Fin r)) (hne : e₁ ≠ e₂) :
    (seenOf e₁ ∪ seenOf e₂).card ≤ 244 * 15 ^ (r - 2) ∧
    ((seenOf e₁ ∪ seenOf e₂).card = 244 * 15 ^ (r - 2) ↔
      (e₁ = ∅ ∧ e₂.card = 2) ∨ (e₂ = ∅ ∧ e₁.card = 2)) := by
  classical
  let a := (e₁ ∩ e₂).card
  let b₁ := (e₁ \ e₂).card
  let b₂ := (e₂ \ e₁).card
  let c := ((Finset.univ : Finset (Fin r)) \ (e₁ ∪ e₂)).card
  have he1_card : e₁.card = a + b₁ := by
    have h := Finset.card_sdiff_add_card_inter e₁ e₂
    dsimp only [a, b₁]; omega
  have he2_card : e₂.card = a + b₂ := by
    have h := Finset.card_sdiff_add_card_inter e₂ e₁
    rw [Finset.inter_comm] at h
    dsimp only [a, b₂]; omega
  have hunion_card : (e₁ ∪ e₂).card = a + b₁ + b₂ := by
    have h := Finset.card_union_add_card_inter e₁ e₂
    omega
  have hsum_r : a + b₁ + b₂ + c = r := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (e₁ ∪ e₂))
    rw [Finset.card_univ, Fintype.card_fin] at h
    dsimp only [c]; omega
  have hd_pos : 0 < b₁ + b₂ := by
    by_contra h0
    have hb10 : e₁ \ e₂ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hb20 : e₂ \ e₁ = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hne
    exact le_antisymm (Finset.sdiff_eq_empty_iff_subset.mp hb10) (Finset.sdiff_eq_empty_iff_subset.mp hb20)
  let d := b₁ + b₂
  have h9le : 9 ^ d < 10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ := by
    have h1 : 9 ^ d < 10 ^ d := Nat.pow_lt_pow_left (by omega) (by omega)
    have h2 : 10 ^ d ≤ 10 ^ b₁ * 15 ^ b₂ := by
      have : 10 ^ b₂ ≤ 15 ^ b₂ := Nat.pow_le_pow_left (by omega) b₂
      calc 10 ^ d = 10 ^ b₁ * 10 ^ b₂ := by dsimp only [d]; rw [pow_add]
        _ ≤ 10 ^ b₁ * 15 ^ b₂ := Nat.mul_le_mul_left _ this
    omega
  have hunion_seen : (seenOf e₁ ∪ seenOf e₂).card =
      10 ^ a * 15 ^ c * (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d) := by
    have hinc := Finset.card_union_add_card_inter (seenOf e₁) (seenOf e₂)
    rw [card_seenOf, card_seenOf, card_seenOf_inter] at hinc
    have hr1 : r - e₁.card = b₂ + c := by omega
    have hr2 : r - e₂.card = b₁ + c := by omega
    rw [hr1, hr2, he1_card, he2_card] at hinc
    have hmul : 10 ^ a * 15 ^ c * (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d) +
        10 ^ a * 15 ^ c * 9 ^ d =
        10 ^ (a + b₁) * 15 ^ (b₂ + c) + 10 ^ (a + b₂) * 15 ^ (b₁ + c) := by
      have hle : 9 ^ d ≤ 10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ := le_of_lt h9le
      zify [hle]
      rw [pow_add, pow_add, pow_add, pow_add]
      ring
    have hinter_eq : 10 ^ a * 15 ^ c * 9 ^ d =
        10 ^ (e₁ ∩ e₂).card * 15 ^ ((Finset.univ : Finset (Fin r)) \ (e₁ ∪ e₂)).card *
          9 ^ ((e₁ \ e₂).card + (e₂ \ e₁).card) := rfl
    omega
  -- Step 1: 10^a * 15^c <= 15^(r - d), equality iff a = 0
  have hac_le : 10 ^ a * 15 ^ c ≤ 15 ^ (r - d) := by
    have : a + c = r - d := by dsimp only [d]; omega
    rw [← this, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) a)
  have hstep1 : (seenOf e₁ ∪ seenOf e₂).card ≤
      15 ^ (r - d) * (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d) := by
    rw [hunion_seen]
    exact Nat.mul_le_mul_right _ hac_le
  -- Step 2: convexity in (b1, b2)
  rcases pair_convexity b₁ b₂ with ⟨hconv_le, hconv_eq⟩
  have hstep2 : 15 ^ (r - d) * (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d) ≤
      15 ^ (r - d) * (15 ^ d + 10 ^ d - 9 ^ d) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hconv_le _)
  -- Step 3: maximize over 1 <= d <= r
  have hstep3 : 15 ^ (r - d) * (15 ^ d + 10 ^ d - 9 ^ d) ≤ 244 * 15 ^ (r - 2) ∧
      (15 ^ (r - d) * (15 ^ d + 10 ^ d - 9 ^ d) = 244 * 15 ^ (r - 2) ↔ d = 2) := by
    by_cases hd1 : d = 1
    · rw [hd1]
      have hpow : 15 ^ (r - 1) = 15 ^ (r - 2) * 15 := by
        have : r - 1 = (r - 2) + 1 := by omega
        rw [this, pow_succ]
      have h16 : 15 ^ 1 + 10 ^ 1 - 9 ^ 1 = 16 := by norm_num
      rw [hpow, h16]
      have hpos : 0 < 15 ^ (r - 2) := by positivity
      refine ⟨by nlinarith, by constructor <;> intro h <;> nlinarith⟩
    · by_cases hd2 : d = 2
      · rw [hd2]
        have h244 : 15 ^ 2 + 10 ^ 2 - 9 ^ 2 = 244 := by norm_num
        rw [h244, mul_comm]
        exact ⟨le_rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩
      · have hd3 : 3 ≤ d := by dsimp only [d] at hd1 hd2 ⊢; omega
        have hlt := ten_pow_lt_nine_pow_add_19 d hd3
        have hle_d : 9 ^ d ≤ 15 ^ d + 10 ^ d :=
          le_trans (Nat.pow_le_pow_left (by omega) d) (Nat.le_add_left (10 ^ d) (15 ^ d))
        have hlt_inner : 15 ^ d + 10 ^ d - 9 ^ d < 244 * 15 ^ (d - 2) := by
          have h15 : 15 ^ d = 225 * 15 ^ (d - 2) := by
            have : d = (d - 2) + 2 := by omega
            conv_lhs => rw [this, pow_add]
            ring
          omega
        have hpow : 15 ^ (r - d) * (244 * 15 ^ (d - 2)) = 244 * 15 ^ (r - 2) := by
          have hsum : (r - d) + (d - 2) = r - 2 := by dsimp only [d]; omega
          calc 15 ^ (r - d) * (244 * 15 ^ (d - 2)) = 244 * (15 ^ (r - d) * 15 ^ (d - 2)) := by ring
            _ = 244 * 15 ^ ((r - d) + (d - 2)) := by rw [← pow_add]
            _ = 244 * 15 ^ (r - 2) := by rw [hsum]
        have hpos : 0 < 15 ^ (r - d) := by positivity
        have hstrict : 15 ^ (r - d) * (15 ^ d + 10 ^ d - 9 ^ d) < 244 * 15 ^ (r - 2) := by
          rw [← hpow]
          exact Nat.mul_lt_mul_of_pos_left hlt_inner hpos
        exact ⟨le_of_lt hstrict, ⟨fun h => absurd h (ne_of_lt hstrict), fun h => absurd h hd2⟩⟩
  refine ⟨le_trans (le_trans hstep1 hstep2) hstep3.1, ?_⟩
  constructor
  · intro heq
    have h1eq : (seenOf e₁ ∪ seenOf e₂).card =
        15 ^ (r - d) * (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d) := by omega
    have h2eq : 15 ^ (r - d) * (10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d) =
        15 ^ (r - d) * (15 ^ d + 10 ^ d - 9 ^ d) := by omega
    have h3eq : 15 ^ (r - d) * (15 ^ d + 10 ^ d - 9 ^ d) = 244 * 15 ^ (r - 2) := by omega
    have hd2 : d = 2 := hstep3.2.mp h3eq
    have ha0 : a = 0 := by
      rw [hunion_seen] at h1eq
      have hpos_rhs : 0 < 10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d := by omega
      have hfac : 10 ^ a * 15 ^ c = 15 ^ (r - d) := Nat.eq_of_mul_eq_mul_right hpos_rhs h1eq
      by_contra hane
      have hlt : 10 ^ a < 15 ^ a := Nat.pow_lt_pow_left (by omega) hane
      have hsum_ac : a + c = r - d := by dsimp only [d]; omega
      have hlt2 : 10 ^ a * 15 ^ c < 15 ^ a * 15 ^ c :=
        Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      rw [← pow_add, hsum_ac] at hlt2
      omega
    have hpos15 : 0 < 15 ^ (r - d) := by positivity
    have hsub_eq : 10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ - 9 ^ d = 15 ^ d + 10 ^ d - 9 ^ d :=
      Nat.eq_of_mul_eq_mul_left hpos15 h2eq
    have hconv : 10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ = 15 ^ (b₁ + b₂) + 10 ^ (b₁ + b₂) := by
      have hle1 : 9 ^ d ≤ 10 ^ b₁ * 15 ^ b₂ + 10 ^ b₂ * 15 ^ b₁ := le_of_lt h9le
      have hle2 : 9 ^ d ≤ 15 ^ d + 10 ^ d := le_trans hle1 hconv_le
      dsimp only [d] at hsub_eq hle1 hle2
      omega
    rcases hconv_eq.mp hconv with hb1 | hb2
    · left
      exact ⟨Finset.card_eq_zero.mp (by omega), by omega⟩
    · right
      exact ⟨Finset.card_eq_zero.mp (by omega), by omega⟩
  · rintro (⟨he1, he2⟩ | ⟨he2, he1⟩)
    · have ha0 : a = 0 := by dsimp only [a]; rw [he1]; simp
      have hb1 : b₁ = 0 := by dsimp only [b₁]; rw [he1]; simp
      have hb2 : b₂ = 2 := by omega
      have hd2 : d = 2 := by dsimp only [d]; omega
      have hc : c = r - 2 := by omega
      rw [hunion_seen, ha0, hb1, hb2, hd2, hc]
      norm_num; ring
    · have ha0 : a = 0 := by dsimp only [a]; rw [he2]; simp
      have hb2 : b₂ = 0 := by dsimp only [b₂]; rw [he2]; simp
      have hb1 : b₁ = 2 := by omega
      have hd2 : d = 2 := by dsimp only [d]; omega
      have hc : c = r - 2 := by omega
      rw [hunion_seen, ha0, hb1, hb2, hd2, hc]
      norm_num; ring

/-! ### Part D: Claim 2 (Optimal near-complete menus, kinds \ U) -/

def privOf {r : ℕ} (e : Finset (Fin r)) : Finset (Fin r → Fin 16) :=
  Fintype.piFinset (fun j => if j ∈ e then suppOnlyTrue else suppOnlyFalse)

lemma card_privOf {r : ℕ} (e : Finset (Fin r)) :
    (privOf e).card = 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card := by
  classical
  rw [privOf, Fintype.card_piFinset]
  have h1 : (Finset.univ : Finset (Fin r)).prod (fun j => (if j ∈ e then suppOnlyTrue else suppOnlyFalse).card) =
      (Finset.univ : Finset (Fin r)).prod (fun j => if j ∈ e then 1 else 6) :=
    Finset.prod_congr rfl fun j _ => by by_cases hj : j ∈ e <;> simp [hj, card_suppOnlyTrue, card_suppOnlyFalse]
  rw [h1, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2; ext j; simp

lemma privOf_seen_iff {r : ℕ} {e f : Finset (Fin r)} {t : Fin r → Fin 16} (ht : t ∈ privOf e) :
    t ∈ seenOf f ↔ f = e := by
  rw [privOf, Fintype.mem_piFinset] at ht
  rw [seenOf, Fintype.mem_piFinset]
  constructor
  · intro hf
    ext j
    have htj := ht j
    have hfj := hf j
    by_cases hje : j ∈ e <;> by_cases hjf : j ∈ f
    · simp [hje, hjf]
    · simp only [hje, ite_true] at htj
      simp only [hjf, ite_false] at hfj
      exact absurd hfj (Finset.mem_sdiff.mp htj).2
    · simp only [hje, ite_false] at htj
      simp only [hjf, ite_true] at hfj
      exact absurd hfj (Finset.mem_sdiff.mp htj).2
    · simp [hje, hjf]
  · rintro rfl j
    have htj := ht j
    by_cases hje : j ∈ f
    · simp only [hje, ite_true] at htj ⊢
      exact (Finset.mem_sdiff.mp htj).1
    · simp only [hje, ite_false] at htj ⊢
      exact (Finset.mem_sdiff.mp htj).1

lemma privOf_disjoint {r : ℕ} {e₁ e₂ : Finset (Fin r)} (hne : e₁ ≠ e₂) :
    Disjoint (privOf e₁) (privOf e₂) := by
  rw [Finset.disjoint_left]
  intro t h1 h2
  have hseen : t ∈ seenOf e₁ := (privOf_seen_iff h1).mpr rfl
  exact hne ((privOf_seen_iff h2).mp hseen)

lemma privOf_subset_missed {r : ℕ} {U : Finset (Finset (Fin r))} {e : Finset (Fin r)} (he : e ∈ U) :
    privOf e ⊆ missedMenu ((Finset.univ : Finset (Finset (Fin r))) \ U) := by
  intro t ht
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
  intro hmem
  rcases Finset.mem_biUnion.mp hmem with ⟨f, hf, htf⟩
  have hfe : f = e := (privOf_seen_iff ht).mp htf
  subst hfe
  exact (Finset.mem_sdiff.mp hf).2 he

def sharedAt {r : ℕ} (j₀ : Fin r) : Finset (Fin r → Fin 16) :=
  Fintype.piFinset (fun j => if j = j₀ then suppBoth else suppOnlyTrue)

lemma card_sharedAt {r : ℕ} (j₀ : Fin r) : (sharedAt j₀).card = 9 := by
  classical
  rw [sharedAt, Fintype.card_piFinset]
  rw [Finset.prod_eq_single j₀]
  · simp [card_suppBoth]
  · intro j _ hne; simp [hne, card_suppOnlyTrue]
  · intro h; exact absurd (Finset.mem_univ j₀) h

lemma sharedAt_seen_iff {r : ℕ} {j₀ : Fin r} {f : Finset (Fin r)} {t : Fin r → Fin 16}
    (ht : t ∈ sharedAt j₀) :
    t ∈ seenOf f ↔ f = Finset.univ ∨ f = Finset.univ.erase j₀ := by
  rw [sharedAt, Fintype.mem_piFinset] at ht
  rw [seenOf, Fintype.mem_piFinset]
  constructor
  · intro hf
    have hall : ∀ j : Fin r, j ≠ j₀ → j ∈ f := by
      intro j hne
      have htj := ht j
      simp only [hne, ite_false] at htj
      have hfj := hf j
      by_contra hjf
      simp only [hjf, ite_false] at hfj
      exact (Finset.mem_sdiff.mp htj).2 hfj
    by_cases hj₀ : j₀ ∈ f
    · left; ext j; by_cases h : j = j₀ <;> simp [h, hj₀, hall]
    · right; ext j; by_cases h : j = j₀ <;> simp [h, hj₀, hall]
  · rintro (rfl | rfl) j
    · have htj := ht j
      by_cases h : j = j₀
      · simp only [h, ite_true, Finset.mem_univ] at htj ⊢
        exact (Finset.mem_inter.mp htj).2
      · simp only [h, ite_false, Finset.mem_univ, ite_true] at htj ⊢
        exact (Finset.mem_sdiff.mp htj).1
    · have htj := ht j
      by_cases h : j = j₀
      · subst h
        simp only [ite_true, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false] at htj ⊢
        exact (Finset.mem_inter.mp htj).1
      · simp only [h, ite_false, Finset.mem_erase, ne_eq, not_false_eq_true, Finset.mem_univ,
          and_self, ite_true] at htj ⊢
        exact (Finset.mem_sdiff.mp htj).1

lemma sharedAt_disjoint_privOf {r : ℕ} (j₀ : Fin r) (e : Finset (Fin r)) :
    Disjoint (sharedAt j₀) (privOf e) := by
  rw [Finset.disjoint_left]
  intro t hs hp
  rw [sharedAt, Fintype.mem_piFinset] at hs
  rw [privOf, Fintype.mem_piFinset] at hp
  have hs0 := hs j₀
  have hp0 := hp j₀
  simp only [ite_true] at hs0
  rcases Finset.mem_inter.mp hs0 with ⟨hF, hT⟩
  by_cases hje : j₀ ∈ e
  · simp only [hje, ite_true] at hp0
    exact (Finset.mem_sdiff.mp hp0).2 hF
  · simp only [hje, ite_false] at hp0
    exact (Finset.mem_sdiff.mp hp0).2 hT

lemma sharedAt_subset_missed {r : ℕ} {U : Finset (Finset (Fin r))} {j₀ : Fin r}
    (hU1 : (Finset.univ : Finset (Fin r)) ∈ U) (hU2 : (Finset.univ : Finset (Fin r)).erase j₀ ∈ U) :
    sharedAt j₀ ⊆ missedMenu ((Finset.univ : Finset (Finset (Fin r))) \ U) := by
  intro t ht
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
  intro hmem
  rcases Finset.mem_biUnion.mp hmem with ⟨f, hf, htf⟩
  rcases (sharedAt_seen_iff ht).mp htf with rfl | rfl
  · exact (Finset.mem_sdiff.mp hf).2 hU1
  · exact (Finset.mem_sdiff.mp hf).2 hU2

lemma missed_eq_biUnion_priv_of_all_one {r : ℕ} (U : Finset (Finset (Fin r)))
    (hall : ∀ e ∈ U, ((Finset.univ : Finset (Fin r)) \ e).card = 1) :
    missedMenu ((Finset.univ : Finset (Finset (Fin r))) \ U) = U.biUnion privOf := by
  classical
  ext t
  constructor
  · intro ht
    have hnot : ∀ f : Finset (Fin r), f ∉ U → t ∉ seenOf f := by
      intro f hf htf
      exact (Finset.mem_sdiff.mp ht).2
        (Finset.mem_biUnion.mpr ⟨f, Finset.mem_sdiff.mpr ⟨Finset.mem_univ f, hf⟩, htf⟩)
    -- Define O(t) = {j | t j in suppOnlyTrue} and A(t) = {j | t j in suppOnlyFalse}
    let Ot : Finset (Fin r) := Finset.univ.filter (fun j => t j ∈ suppOnlyTrue)
    let At : Finset (Fin r) := Finset.univ.filter (fun j => t j ∈ suppOnlyFalse)
    have ht_Ot : t ∈ seenOf Ot := by
      rw [seenOf, Fintype.mem_piFinset]
      intro j
      by_cases h1 : t j ∈ suppOnlyTrue
      · have hjO : j ∈ Ot := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1⟩
        simp only [hjO, ite_true]
        exact (Finset.mem_sdiff.mp h1).1
      · have hjO : j ∉ Ot := fun h => h1 (Finset.mem_filter.mp h).2
        simp only [hjO, ite_false]
        rcases supp_cover (t j) with hF | hT
        · exact hF
        · by_contra hnotF
          exact h1 (Finset.mem_sdiff.mpr ⟨hT, hnotF⟩)
    have ht_compAt : t ∈ seenOf ((Finset.univ : Finset (Fin r)) \ At) := by
      rw [seenOf, Fintype.mem_piFinset]
      intro j
      by_cases h1 : t j ∈ suppOnlyFalse
      · have hj : j ∉ (Finset.univ : Finset (Fin r)) \ At := by
          simp [At, h1]
        simp only [hj, ite_false]
        exact (Finset.mem_sdiff.mp h1).1
      · have hj : j ∈ (Finset.univ : Finset (Fin r)) \ At := by
          simp [At, h1]
        simp only [hj, ite_true]
        rcases supp_cover (t j) with hF | hT
        · by_contra hnotT
          exact h1 (Finset.mem_sdiff.mpr ⟨hF, hnotT⟩)
        · exact hT
    have hOtU : Ot ∈ U := by
      by_contra h; exact hnot Ot h ht_Ot
    have hAtU : (Finset.univ : Finset (Fin r)) \ At ∈ U := by
      by_contra h; exact hnot _ h ht_compAt
    have hOt_sub : Ot ⊆ (Finset.univ : Finset (Fin r)) \ At := by
      intro j hj
      have h1 : t j ∈ suppOnlyTrue := (Finset.mem_filter.mp hj).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hA => ?_⟩
      have h2 : t j ∈ suppOnlyFalse := (Finset.mem_filter.mp hA).2
      exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
    have hcard1 : ((Finset.univ : Finset (Fin r)) \ Ot).card = 1 := hall Ot hOtU
    have hcard2 : ((Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ At)).card = 1 :=
      hall _ hAtU
    have hsub_sdiff : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ At) ⊆
        (Finset.univ : Finset (Fin r)) \ Ot := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hOt_sub
    have hsdiff_eq : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ At) =
        (Finset.univ : Finset (Fin r)) \ Ot :=
      Finset.eq_of_subset_of_card_le hsub_sdiff (by omega)
    have hOt_eq : Ot = (Finset.univ : Finset (Fin r)) \ At := by
      ext j
      have hj := Finset.ext_iff.mp hsdiff_eq j
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj ⊢
      tauto
    refine Finset.mem_biUnion.mpr ⟨Ot, hOtU, ?_⟩
    rw [privOf, Fintype.mem_piFinset]
    intro j
    by_cases hj : j ∈ Ot
    · simp only [hj, ite_true]
      exact (Finset.mem_filter.mp hj).2
    · simp only [hj, ite_false]
      rw [hOt_eq] at hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
      exact (Finset.mem_filter.mp hj).2
  · intro ht
    rcases Finset.mem_biUnion.mp ht with ⟨e, he, hte⟩
    exact privOf_subset_missed he hte

lemma near_complete_bound {r : ℕ} (U : Finset (Finset (Fin r))) (hU2 : 2 ≤ U.card) :
    6 * U.card ≤ (missedMenu ((Finset.univ : Finset (Finset (Fin r))) \ U)).card ∧
    ((missedMenu ((Finset.univ : Finset (Finset (Fin r))) \ U)).card = 6 * U.card ↔
      ∀ e ∈ U, ((Finset.univ : Finset (Fin r)) \ e).card = 1) := by
  classical
  let M := (Finset.univ : Finset (Finset (Fin r))) \ U
  have hpriv_sub : U.biUnion privOf ⊆ missedMenu M := by
    intro t ht
    rcases Finset.mem_biUnion.mp ht with ⟨e, he, hte⟩
    exact privOf_subset_missed he hte
  have hpriv_card : (U.biUnion privOf).card =
      U.sum (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) := by
    rw [Finset.card_biUnion (fun e₁ _ e₂ _ hne => privOf_disjoint hne)]
    exact Finset.sum_congr rfl fun e _ => card_privOf e
  by_cases hunivU : (Finset.univ : Finset (Fin r)) ∈ U
  · -- Case B: univ in U -> strict inequality 6 * U.card < (missedMenu M).card
    have hstrict : 6 * U.card < (missedMenu M).card := by
      by_cases hex1 : ∃ e₀ ∈ U, ((Finset.univ : Finset (Fin r)) \ e₀).card = 1
      · -- Subcase B1: a neighbor e0 of univ is in U
        rcases hex1 with ⟨e₀, he₀U, he₀_card⟩
        rcases Finset.card_eq_one.mp he₀_card with ⟨j₀, hj₀_eq⟩
        have he₀_erase : e₀ = (Finset.univ : Finset (Fin r)).erase j₀ := by
          ext j
          have hmem : j ∈ (Finset.univ : Finset (Fin r)) \ e₀ ↔ j = j₀ := by
            rw [hj₀_eq, Finset.mem_singleton]
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hmem
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          tauto
        have hsh_sub : sharedAt j₀ ⊆ missedMenu M :=
          sharedAt_subset_missed hunivU (he₀_erase ▸ he₀U)
        have hdisj : Disjoint (sharedAt j₀) (U.biUnion privOf) := by
          rw [Finset.disjoint_right]
          intro t ht hsh
          rcases Finset.mem_biUnion.mp ht with ⟨e, _, hte⟩
          exact Finset.disjoint_left.mp (sharedAt_disjoint_privOf j₀ e) hsh hte
        have hunion_sub : sharedAt j₀ ∪ U.biUnion privOf ⊆ missedMenu M :=
          Finset.union_subset hsh_sub hpriv_sub
        have hcard_le : (sharedAt j₀).card + (U.biUnion privOf).card ≤ (missedMenu M).card := by
          rw [← Finset.card_union_of_disjoint hdisj]
          exact Finset.card_le_card hunion_sub
        rw [card_sharedAt, hpriv_card, ← Finset.add_sum_erase _ _ hunivU] at hcard_le
        have hrest : 6 * (U.card - 1) ≤ (U.erase Finset.univ).sum
            (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) := by
          calc 6 * (U.card - 1) = (U.erase Finset.univ).card * 6 := by
                rw [Finset.card_erase_of_mem hunivU]; ring
            _ = (U.erase Finset.univ).sum (fun _ => 6) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ (U.erase Finset.univ).sum (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) :=
                Finset.sum_le_sum fun e he => by
                  have hne : e ≠ Finset.univ := (Finset.mem_erase.mp he).1
                  have hpos : 1 ≤ ((Finset.univ : Finset (Fin r)) \ e).card := by
                    by_contra h0
                    have hempty : (Finset.univ : Finset (Fin r)) \ e = ∅ :=
                      Finset.card_eq_zero.mp (by omega)
                    apply hne; ext j
                    have : j ∉ (Finset.univ : Finset (Fin r)) \ e := by rw [hempty]; simp
                    simpa using this
                  calc 6 = 6 ^ 1 := by norm_num
                    _ ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card := Nat.pow_le_pow_right (by omega) hpos
        have h0 : 6 ^ ((Finset.univ : Finset (Fin r)) \ (Finset.univ : Finset (Fin r))).card = 1 := by simp
        rw [h0] at hcard_le
        omega
      · -- Subcase B2: no e in U has (univ \ e).card = 1, so some e1 in U has (univ \ e1).card >= 2
        push Not at hex1
        have hne_er : (U.erase Finset.univ).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem hunivU]; omega
        rcases hne_er with ⟨e₁, he₁_er⟩
        have he₁U : e₁ ∈ U := (Finset.mem_erase.mp he₁_er).2
        have he₁_ne : e₁ ≠ Finset.univ := (Finset.mem_erase.mp he₁_er).1
        have he₁_ge2 : 2 ≤ ((Finset.univ : Finset (Fin r)) \ e₁).card := by
          have hpos : 1 ≤ ((Finset.univ : Finset (Fin r)) \ e₁).card := by
            by_contra h0
            have hempty : (Finset.univ : Finset (Fin r)) \ e₁ = ∅ :=
              Finset.card_eq_zero.mp (by omega)
            apply he₁_ne; ext j
            have : j ∉ (Finset.univ : Finset (Fin r)) \ e₁ := by rw [hempty]; simp
            simpa using this
          have hne1 := hex1 e₁ he₁U
          omega
        have hcard_le : (U.biUnion privOf).card ≤ (missedMenu M).card := Finset.card_le_card hpriv_sub
        rw [hpriv_card, ← Finset.add_sum_erase _ _ hunivU, ← Finset.add_sum_erase _ _ he₁_er] at hcard_le
        have hrest : 6 * (U.card - 2) ≤ ((U.erase Finset.univ).erase e₁).sum
            (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) := by
          calc 6 * (U.card - 2) = ((U.erase Finset.univ).erase e₁).card * 6 := by
                rw [Finset.card_erase_of_mem he₁_er, Finset.card_erase_of_mem hunivU]; omega
            _ = ((U.erase Finset.univ).erase e₁).sum (fun _ => 6) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ ((U.erase Finset.univ).erase e₁).sum
                  (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) :=
                Finset.sum_le_sum fun e he => by
                  have hne : e ≠ Finset.univ := (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
                  have hpos : 1 ≤ ((Finset.univ : Finset (Fin r)) \ e).card := by
                    by_contra h0
                    have hempty : (Finset.univ : Finset (Fin r)) \ e = ∅ :=
                      Finset.card_eq_zero.mp (by omega)
                    apply hne; ext j
                    have : j ∉ (Finset.univ : Finset (Fin r)) \ e := by rw [hempty]; simp
                    simpa using this
                  calc 6 = 6 ^ 1 := by norm_num
                    _ ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card := Nat.pow_le_pow_right (by omega) hpos
        have h0 : 6 ^ ((Finset.univ : Finset (Fin r)) \ (Finset.univ : Finset (Fin r))).card = 1 := by simp
        have h36 : 36 ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e₁).card := by
          calc 36 = 6 ^ 2 := by norm_num
            _ ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e₁).card := Nat.pow_le_pow_right (by omega) he₁_ge2
        rw [h0] at hcard_le
        omega
    refine ⟨le_of_lt hstrict, ?_⟩
    constructor
    · intro heq; exact absurd heq (ne_of_gt hstrict)
    · intro hall
      have h0 := hall Finset.univ hunivU
      simp at h0
  · -- Case A: univ not in U -> every e in U has (univ \ e).card >= 1
    have hge1 : ∀ e ∈ U, 1 ≤ ((Finset.univ : Finset (Fin r)) \ e).card := by
      intro e he
      by_contra h0
      have hempty : (Finset.univ : Finset (Fin r)) \ e = ∅ := Finset.card_eq_zero.mp (by omega)
      have heq : e = Finset.univ := by
        ext j
        have : j ∉ (Finset.univ : Finset (Fin r)) \ e := by rw [hempty]; simp
        simpa using this
      exact hunivU (heq ▸ he)
    have hsum_ge : 6 * U.card ≤ U.sum (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) := by
      calc 6 * U.card = U.card * 6 := mul_comm _ _
        _ = U.sum (fun _ => 6) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ U.sum (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) :=
            Finset.sum_le_sum fun e he => by
              calc 6 = 6 ^ 1 := by norm_num
                _ ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card := Nat.pow_le_pow_right (by omega) (hge1 e he)
    have hcard_le : (U.biUnion privOf).card ≤ (missedMenu M).card := Finset.card_le_card hpriv_sub
    rw [hpriv_card] at hcard_le
    refine ⟨le_trans hsum_ge hcard_le, ?_⟩
    constructor
    · intro heq e he
      have hsum_eq : U.sum (fun e' => 6 ^ ((Finset.univ : Finset (Fin r)) \ e').card) = 6 * U.card := by
        change (missedMenu M).card = 6 * U.card at heq
        omega
      by_contra hne1
      have hge2 : 2 ≤ ((Finset.univ : Finset (Fin r)) \ e).card := by have := hge1 e he; omega
      have h36 : 36 ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card := by
        calc 36 = 6 ^ 2 := by norm_num
          _ ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card := Nat.pow_le_pow_right (by omega) hge2
      have hrest : 6 * (U.card - 1) ≤ (U.erase e).sum (fun e' => 6 ^ ((Finset.univ : Finset (Fin r)) \ e').card) := by
        calc 6 * (U.card - 1) = (U.erase e).card * 6 := by rw [Finset.card_erase_of_mem he]; ring
          _ = (U.erase e).sum (fun _ => 6) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (U.erase e).sum (fun e' => 6 ^ ((Finset.univ : Finset (Fin r)) \ e').card) :=
              Finset.sum_le_sum fun e' he' => by
                calc 6 = 6 ^ 1 := by norm_num
                  _ ≤ 6 ^ ((Finset.univ : Finset (Fin r)) \ e').card :=
                    Nat.pow_le_pow_right (by omega) (hge1 e' (Finset.mem_erase.mp he').2)
      rw [← Finset.add_sum_erase _ _ he] at hsum_eq
      omega
    · intro hall
      rw [missed_eq_biUnion_priv_of_all_one U hall, hpriv_card]
      have hcongr : U.sum (fun e => 6 ^ ((Finset.univ : Finset (Fin r)) \ e).card) = U.sum (fun _ => 6) :=
        Finset.sum_congr rfl fun e he => by rw [hall e he]; norm_num
      rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm]

theorem main :
    ∀ r : Nat, 2 ≤ r →
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
      (∀ M : Finset Kind, M.card = 2 →
        let bound := 11 ^ (16 ^ r - 244 * 15 ^ (r - 2))
        bound ≤ kernelSize M ∧ (kernelSize M = bound ↔
          (∅ : Kind) ∈ M ∧ ∃ e ∈ M, e.card = 2)) ∧
      (∀ U : Finset Kind, 2 ≤ U.card → U.card ≤ r →
        let bound := 11 ^ (6 * U.card)
        bound ≤ kernelSize (kinds \ U) ∧ (kernelSize (kinds \ U) = bound ↔
          ∀ e ∈ U, (sites \ e).card = 1)) := by
  intro r hr Kind Word kinds cube sites pass zeroRead kernelSize
  have hker : ∀ M : Finset Kind, kernelSize M = 11 ^ (missedMenu M).card :=
    fun M => kernelSize_eq_pow M
  constructor
  · intro M hM2
    rw [hker M]
    rcases Finset.card_eq_two.mp hM2 with ⟨e₁, e₂, hne, rfl⟩
    have hseen_eq : seenMenu ({e₁, e₂} : Finset (Finset (Fin r))) = seenOf e₁ ∪ seenOf e₂ := by
      simp [seenMenu]
    have hsum := card_missedMenu_add_seenMenu ({e₁, e₂} : Finset (Finset (Fin r)))
    rw [hseen_eq] at hsum
    rcases pair_seen_bound hr e₁ e₂ hne with ⟨hle_seen, heq_seen⟩
    have hle_miss : 16 ^ r - 244 * 15 ^ (r - 2) ≤ (missedMenu ({e₁, e₂} : Finset (Finset (Fin r)))).card := by
      omega
    have h244_le : 244 * 15 ^ (r - 2) ≤ 16 ^ r := by
      have h16 : Fintype.card (Fin r → Fin 16) = 16 ^ r := by simp
      have h244_ex : ∃ f : Finset (Fin r), f.card = 2 := by
        refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair ?_⟩
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      rcases h244_ex with ⟨f, hf⟩
      have hne0 : (∅ : Finset (Fin r)) ≠ f := by
        intro heq; rw [← heq] at hf; simp at hf
      have hf_eq := (pair_seen_bound hr ∅ f hne0).2.mpr (Or.inl ⟨rfl, hf⟩)
      have hle_u := Finset.card_le_univ (seenOf (∅ : Finset (Fin r)) ∪ seenOf f)
      rw [hf_eq, h16] at hle_u
      exact hle_u
    refine ⟨Nat.pow_le_pow_right (by omega) hle_miss, ?_⟩
    rw [Nat.pow_right_inj (by omega : 1 < 11)]
    have heq_iff : (missedMenu ({e₁, e₂} : Finset (Finset (Fin r)))).card = 16 ^ r - 244 * 15 ^ (r - 2) ↔
        (seenOf e₁ ∪ seenOf e₂).card = 244 * 15 ^ (r - 2) := by omega
    rw [heq_iff, heq_seen]
    constructor
    · rintro (⟨rfl, h2⟩ | ⟨rfl, h2⟩)
      · exact ⟨Finset.mem_insert_self _ _, e₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h2⟩
      · exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), e₁, Finset.mem_insert_self _ _, h2⟩
    · rintro ⟨h0, e, heM, he2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at h0 heM
      rcases h0 with h0 | h0
      · left
        refine ⟨h0.symm, ?_⟩
        rcases heM with rfl | rfl
        · rw [← h0] at he2; dsimp only [Kind] at he2; simp at he2
        · exact he2
      · right
        refine ⟨h0.symm, ?_⟩
        rcases heM with rfl | rfl
        · exact he2
        · rw [← h0] at he2; dsimp only [Kind] at he2; simp at he2
  · intro U hU2 _hUr
    rw [hker]
    rcases near_complete_bound U hU2 with ⟨hle, heq⟩
    refine ⟨Nat.pow_le_pow_right (by omega) hle, ?_⟩
    rw [Nat.pow_right_inj (by omega : 1 < 11)]
    exact heq

end PEqualNP.Outside.L_lib_1166_aux

theorem PEqualNP.Outside.L_lib_1166 :
∀ r : Nat, 2 ≤ r →
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
  (∀ M : Finset Kind, M.card = 2 →
    let bound := 11 ^ (16 ^ r - 244 * 15 ^ (r - 2))
    bound ≤ kernelSize M ∧ (kernelSize M = bound ↔
      (∅ : Kind) ∈ M ∧ ∃ e ∈ M, e.card = 2)) ∧
  (∀ U : Finset Kind, 2 ≤ U.card → U.card ≤ r →
    let bound := 11 ^ (6 * U.card)
    bound ≤ kernelSize (kinds \ U) ∧ (kernelSize (kinds \ U) = bound ↔
      ∀ e ∈ U, (sites \ e).card = 1)) :=
  PEqualNP.Outside.L_lib_1166_aux.main
