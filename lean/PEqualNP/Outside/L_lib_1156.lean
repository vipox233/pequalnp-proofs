import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1156

private instance instPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩

private def xor16 (a b : Fin 16) : Fin 16 :=
  ⟨(a.val ^^^ b.val) % 16, Nat.mod_lt _ (by decide)⟩

private lemma xor16_val (a b : Fin 16) : (xor16 a b).val = a.val ^^^ b.val := by
  revert a b; decide

private def pop4 (n : Nat) : Nat :=
  (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 1 else 0) +
  (if n.testBit 2 then 1 else 0) + (if n.testBit 3 then 1 else 0)

private def chi1 (t x : Fin 16) : ZMod 11 :=
  if pop4 (t.val &&& x.val) % 2 = 0 then 1 else -1

private def ker1 (flag : Bool) (w : Fin 16) : Bool :=
  (w.val &&& 3) != 0 && (w.val &&& 13) != (if flag then 1 else 0)

private def hat1 (flag : Bool) (t : Fin 16) : ZMod 11 :=
  ∑ w : Fin 16, (if ker1 flag w then (1 : ZMod 11) else 0) * chi1 t w

private def bothSet : Finset (Fin 16) := {1, 2, 3, 4, 5, 8, 9, 12, 13}
private def only0Set : Finset (Fin 16) := {6, 7, 10, 11, 14, 15}
private def only1Set : Finset (Fin 16) := {0}

private lemma bothSet_card : bothSet.card = 9 := by decide
private lemma only0Set_card : only0Set.card = 6 := by decide
private lemma only1Set_card : only1Set.card = 1 := by decide

private lemma chi1_orth (t₁ t₂ : Fin 16) :
    ∑ x : Fin 16, chi1 t₁ x * chi1 t₂ x = if t₁ = t₂ then (16 : ZMod 11) else 0 := by
  revert t₁ t₂; decide

private lemma ker1_chi1 (flag : Bool) (t z : Fin 16) :
    ∑ x : Fin 16, (if ker1 flag (xor16 z x) then (1 : ZMod 11) else 0) * chi1 t x =
      hat1 flag t * chi1 t z := by
  revert flag t z; decide

private lemma hat1_ne_zero_iff (flag : Bool) (t : Fin 16) :
    hat1 flag t ≠ 0 ↔
      (t ∈ bothSet ∨ (flag = false ∧ t ∈ only0Set) ∨ (flag = true ∧ t ∈ only1Set)) := by
  revert flag t; decide

private lemma fin16_part (t : Fin 16) :
    (t ∈ bothSet ∨ t ∈ only0Set ∨ t ∈ only1Set) ∧
    (t ∈ bothSet → t ∉ only0Set ∧ t ∉ only1Set) ∧
    (t ∈ only0Set → t ∉ only1Set) := by
  revert t; decide

private lemma sixteen_ne_zero : (16 : ZMod 11) ≠ 0 := by decide

private def chi {r : Nat} (t x : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, chi1 (t j) (x j)

private def hat {r : Nat} (e : Finset (Fin r)) (t : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, hat1 (decide (j ∈ e)) (t j)

private def passFn {r : Nat} (e : Finset (Fin r)) (z x : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, if ker1 (decide (j ∈ e)) (xor16 (z j) (x j)) then (1 : ZMod 11) else 0

private lemma chi_orth {r : Nat} (t₁ t₂ : Fin r → Fin 16) :
    ∑ x : Fin r → Fin 16, chi t₁ x * chi t₂ x =
      if t₁ = t₂ then (16 : ZMod 11) ^ r else 0 := by
  have hprod : ∀ x : Fin r → Fin 16,
      chi t₁ x * chi t₂ x = ∏ j : Fin r, (chi1 (t₁ j) (x j) * chi1 (t₂ j) (x j)) := by
    intro x
    simp [chi, Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j a => chi1 (t₁ j) a * chi1 (t₂ j) a)]
  simp_rw [chi1_orth]
  by_cases h : t₁ = t₂
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    have hex : ∃ j : Fin r, t₁ j ≠ t₂ j := by
      by_contra hall
      push_neg at hall
      exact h (funext hall)
    rcases hex with ⟨j, hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

private lemma pass_chi {r : Nat} (e : Finset (Fin r)) (t z : Fin r → Fin 16) :
    ∑ x : Fin r → Fin 16, passFn e z x * chi t x = hat e t * chi t z := by
  have hprod : ∀ x : Fin r → Fin 16,
      passFn e z x * chi t x =
        ∏ j : Fin r,
          ((if ker1 (decide (j ∈ e)) (xor16 (z j) (x j)) then (1 : ZMod 11) else 0) *
            chi1 (t j) (x j)) := by
    intro x
    rw [passFn, chi, ← Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j a =>
    (if ker1 (decide (j ∈ e)) (xor16 (z j) a) then (1 : ZMod 11) else 0) * chi1 (t j) a)]
  simp_rw [ker1_chi1]
  simp [hat, chi, Finset.prod_mul_distrib]

private def wht {r : Nat} (d : (Fin r → Fin 16) → ZMod 11) (t : Fin r → Fin 16) : ZMod 11 :=
  ∑ x : Fin r → Fin 16, d x * chi t x

private lemma wht_inv {r : Nat} (d : (Fin r → Fin 16) → ZMod 11) (x : Fin r → Fin 16) :
    ((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16, wht d t * chi t x = d x := by
  have hsum : ∑ t : Fin r → Fin 16, wht d t * chi t x =
      ∑ y : Fin r → Fin 16, d y * (∑ t : Fin r → Fin 16, chi t y * chi t x) := by
    simp only [wht, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _
    ring
  have hchi_symm : ∀ (t y : Fin r → Fin 16), chi t y = chi y t := by
    intro t y
    simp only [chi]
    refine Finset.prod_congr rfl ?_
    intro j _
    have h1 : ∀ a b : Fin 16, chi1 a b = chi1 b a := by decide
    exact h1 (t j) (y j)
  have horth_t : ∀ y : Fin r → Fin 16,
      ∑ t : Fin r → Fin 16, chi t y * chi t x = if y = x then (16 : ZMod 11) ^ r else 0 := by
    intro y
    simp_rw [hchi_symm _ y, hchi_symm _ x]
    exact chi_orth y x
  rw [hsum]
  simp_rw [horth_t]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hne : (16 : ZMod 11) ^ r ≠ 0 := pow_ne_zero r sixteen_ne_zero
  rw [mul_comm (d x), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

private lemma wht_bijective {r : Nat} : Function.Bijective (@wht r) := by
  refine ⟨?_, ?_⟩
  · intro d₁ d₂ h
    funext x
    rw [← wht_inv d₁ x, ← wht_inv d₂ x, h]
  · intro f
    refine ⟨fun x => ((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16, f t * chi t x, ?_⟩
    funext t₀
    simp only [wht, Finset.mul_sum, Finset.sum_mul]
    have hswap :
        ∑ x : Fin r → Fin 16, ∑ t : Fin r → Fin 16,
          ((16 : ZMod 11) ^ r)⁻¹ * (f t * chi t x) * chi t₀ x =
        ((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16,
          f t * (∑ x : Fin r → Fin 16, chi t x * chi t₀ x) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    rw [hswap]
    simp_rw [chi_orth]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hne : (16 : ZMod 11) ^ r ≠ 0 := pow_ne_zero r sixteen_ne_zero
    rw [mul_comm (f t₀), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

private lemma pass_dot_eq {r : Nat} (e : Finset (Fin r)) (z : Fin r → Fin 16)
    (d : (Fin r → Fin 16) → ZMod 11) :
    ∑ x : Fin r → Fin 16, passFn e z x * d x =
      ((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16, (hat e t * chi t z) * wht d t := by
  have h1 : ∑ x : Fin r → Fin 16, passFn e z x * d x =
      ∑ x : Fin r → Fin 16, passFn e z x *
        (((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16, wht d t * chi t x) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [wht_inv]
  rw [h1]
  have h2 :
      ∑ x : Fin r → Fin 16, passFn e z x *
        (((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16, wht d t * chi t x) =
      ((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16,
        wht d t * (∑ x : Fin r → Fin 16, passFn e z x * chi t x) := by
    have hL : ∑ x : Fin r → Fin 16, passFn e z x *
        (((16 : ZMod 11) ^ r)⁻¹ * ∑ t : Fin r → Fin 16, wht d t * chi t x) =
      ∑ x : Fin r → Fin 16, ∑ t : Fin r → Fin 16,
        ((16 : ZMod 11) ^ r)⁻¹ * (wht d t * (passFn e z x * chi t x)) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro t _; ring
    rw [hL, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [h2]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [pass_chi]
  ring

private lemma pass_dot_zero_iff {r : Nat} (e : Finset (Fin r)) (z : Fin r → Fin 16)
    (d : (Fin r → Fin 16) → ZMod 11) :
    (∑ x : Fin r → Fin 16, passFn e z x * d x = 0) ↔
      (∑ t : Fin r → Fin 16, (hat e t * chi t z) * wht d t = 0) := by
  rw [pass_dot_eq]
  have hne : ((16 : ZMod 11) ^ r)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero r sixteen_ne_zero)
  simp [hne]

private lemma all_z_zero_iff {r : Nat} (e : Finset (Fin r)) (d : (Fin r → Fin 16) → ZMod 11) :
    (∀ z : Fin r → Fin 16, ∑ x : Fin r → Fin 16, passFn e z x * d x = 0) ↔
      (∀ t : Fin r → Fin 16, hat e t ≠ 0 → wht d t = 0) := by
  simp_rw [pass_dot_zero_iff]
  constructor
  · intro hall
    have hw : wht (fun t => hat e t * wht d t) = wht (fun _ => 0) := by
      funext z
      have hz := hall z
      have hchi_symm : ∀ (a b : Fin r → Fin 16), chi a b = chi b a := by
        intro a b; simp only [chi]; refine Finset.prod_congr rfl (fun j _ => ?_)
        have h1 : ∀ u v : Fin 16, chi1 u v = chi1 v u := by decide
        exact h1 (a j) (b j)
      have hrew : ∑ t : Fin r → Fin 16, hat e t * wht d t * chi z t =
          ∑ t : Fin r → Fin 16, hat e t * chi t z * wht d t := by
        refine Finset.sum_congr rfl ?_
        intro t _
        rw [hchi_symm z t]; ring
      change ∑ t : Fin r → Fin 16, (hat e t * wht d t) * chi z t =
        ∑ t : Fin r → Fin 16, (0 : ZMod 11) * chi z t
      simp only [zero_mul, Finset.sum_const_zero]
      rw [hrew, hz]
    have hfn := wht_bijective.1 hw
    intro t hne
    have ht : hat e t * wht d t = 0 := congrFun hfn t
    exact (mul_eq_zero.mp ht).resolve_left hne
  · intro hall z
    refine Finset.sum_eq_zero ?_
    intro t _
    by_cases h : hat e t = 0
    · simp [h]
    · simp [hall t h]

private lemma hat_ne_zero_iff {r : Nat} (e : Finset (Fin r)) (t : Fin r → Fin 16) :
    hat e t ≠ 0 ↔
      e ∩ Finset.univ.filter (fun j => t j ∉ bothSet) =
        Finset.univ.filter (fun j => t j ∈ only1Set) := by
  have hprod : hat e t ≠ 0 ↔ ∀ j : Fin r, hat1 (decide (j ∈ e)) (t j) ≠ 0 := by
    simp [hat, Finset.prod_ne_zero_iff]
  rw [hprod]
  constructor
  · intro hall
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    have hj := (hat1_ne_zero_iff (decide (j ∈ e)) (t j)).mp (hall j)
    have hp := fin16_part (t j)
    constructor
    · rintro ⟨hje, hnb⟩
      simp only [decide_eq_true hje, Bool.true_eq_false, false_and, true_and, false_or] at hj
      rcases hj with hb | h1
      · exact absurd hb hnb
      · exact h1
    · intro h1
      have hnb : t j ∉ bothSet := fun hb => (hp.2.1 hb).2 h1
      have hn0 : t j ∉ only0Set := fun h0 => hp.2.2 h0 h1
      by_cases hje : j ∈ e
      · exact ⟨hje, hnb⟩
      · simp only [decide_eq_false hje, Bool.false_eq_true, false_and, true_and, or_false] at hj
        rcases hj with hb | h0
        · exact absurd hb hnb
        · exact absurd h0 hn0
  · intro heq j
    rw [hat1_ne_zero_iff]
    have hp := fin16_part (t j)
    by_cases hb : t j ∈ bothSet
    · exact Or.inl hb
    · have hj_eq := congrArg (fun S => j ∈ S) heq
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hb,
        not_false_eq_true, and_true] at hj_eq
      rcases hp.1 with hb' | h0 | h1
      · exact absurd hb' hb
      · right; left
        have hn1 : t j ∉ only1Set := hp.2.2 h0
        have hje : j ∉ e := fun h => hn1 (hj_eq.mp h)
        exact ⟨decide_eq_false hje, h0⟩
      · right; right
        have hje : j ∈ e := hj_eq.mpr h1
        exact ⟨decide_eq_true hje, h1⟩

private def supp {r : Nat} (menu : Finset (Finset (Fin r))) : Finset (Fin r → Fin 16) :=
  Finset.univ.filter (fun t => ∃ e ∈ menu, hat e t ≠ 0)

private lemma card_supp_eq_rho {r : Nat} (menu : Finset (Finset (Fin r))) :
    (supp menu).card =
      (Finset.univ : Finset (Finset (Fin r))).sum (fun J =>
        9 ^ (r - J.card) * (menu.image (fun e => e ∩ J)).sum (fun B => 6 ^ (J.card - B.card))) := by
  let Jof : (Fin r → Fin 16) → Finset (Fin r) :=
    fun t => Finset.univ.filter (fun j => t j ∉ bothSet)
  let Bof : (Fin r → Fin 16) → Finset (Fin r) :=
    fun t => Finset.univ.filter (fun j => t j ∈ only1Set)
  let fiber : Finset (Fin r) → Finset (Fin r) → Finset (Fin r → Fin 16) := fun J B =>
    Finset.univ.filter (fun t => Jof t = J ∧ Bof t = B)
  have hfiber_card : ∀ (J B : Finset (Fin r)), B ⊆ J →
      (fiber J B).card = 9 ^ (r - J.card) * 6 ^ (J.card - B.card) := by
    intro J B hBJ
    let choice : Fin r → Finset (Fin 16) := fun j =>
      if j ∉ J then bothSet else if j ∈ B then only1Set else only0Set
    have hfib_eq : fiber J B = Fintype.piFinset choice := by
      ext t
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨rfl, rfl⟩ j
        have hp := fin16_part (t j)
        by_cases hj : t j ∈ bothSet
        · have hnotJ : j ∉ Jof t := by simp [Jof, hj]
          simp [choice, hnotJ, hj]
        · have hinJ : j ∈ Jof t := by simp [Jof, hj]
          by_cases h1 : t j ∈ only1Set
          · have hinB : j ∈ Bof t := by simp [Bof, h1]
            simp [choice, hinJ, hinB, h1]
          · have hnotB : j ∉ Bof t := by simp [Bof, h1]
            rcases hp.1 with hb | h0 | h1'
            · exact absurd hb hj
            · simp [choice, hinJ, hnotB, h0]
            · exact absurd h1' h1
      · intro hpi
        constructor
        · ext j
          have hj := hpi j
          have hp := fin16_part (t j)
          simp only [Jof, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hJ : j ∈ J
          · simp only [choice, hJ, not_true_eq_false, ↓reduceIte] at hj
            by_cases hB : j ∈ B
            · simp only [hB, ↓reduceIte] at hj
              exact ⟨fun _ => hJ, fun _ hb => (hp.2.1 hb).2 hj⟩
            · simp only [hB, ↓reduceIte] at hj
              exact ⟨fun _ => hJ, fun _ hb => (hp.2.1 hb).1 hj⟩
          · simp only [choice, hJ, not_false_eq_true, ↓reduceIte] at hj
            exact ⟨fun h => absurd hj h, fun h => absurd h hJ⟩
        · ext j
          have hj := hpi j
          have hp := fin16_part (t j)
          simp only [Bof, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hB : j ∈ B
          · have hJ : j ∈ J := hBJ hB
            simp only [choice, hJ, not_true_eq_false, ↓reduceIte, hB] at hj
            exact ⟨fun _ => hB, fun _ => hj⟩
          · by_cases hJ : j ∈ J
            · simp only [choice, hJ, not_true_eq_false, ↓reduceIte, hB] at hj
              exact ⟨fun h1 => absurd h1 (hp.2.2 hj), fun h => absurd h hB⟩
            · simp only [choice, hJ, not_false_eq_true, ↓reduceIte] at hj
              exact ⟨fun h1 => absurd h1 (hp.2.1 hj).2, fun h => absurd h hB⟩
    rw [hfib_eq, Fintype.card_piFinset]
    have hsplit : ∏ j : Fin r, (choice j).card =
        (∏ j ∈ Finset.univ.filter (fun j => j ∉ J), (choice j).card) *
        (∏ j ∈ Finset.univ.filter (fun j => j ∈ J), (choice j).card) := by
      have h := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin r))
        (fun j => j ∉ J) (fun j => (choice j).card)
      simpa using h.symm
    rw [hsplit]
    have hp1 : ∏ j ∈ Finset.univ.filter (fun j => j ∉ J), (choice j).card = 9 ^ (r - J.card) := by
      have hval : ∀ j ∈ Finset.univ.filter (fun j => j ∉ J), (choice j).card = 9 := by
        intro j hj
        have hnot : j ∉ J := (Finset.mem_filter.mp hj).2
        simp [choice, hnot, bothSet_card]
      rw [Finset.prod_congr rfl hval, Finset.prod_const]
      have hcard : (Finset.univ.filter (fun j : Fin r => j ∉ J)).card = r - J.card := by
        have h1 : (Finset.univ.filter (fun j : Fin r => j ∉ J)) = Finset.univ \ J := by
          ext j; simp
        rw [h1, Finset.card_sdiff]
        simp
      rw [hcard]
    have hp2 : ∏ j ∈ Finset.univ.filter (fun j => j ∈ J), (choice j).card = 6 ^ (J.card - B.card) := by
      have hJeq : Finset.univ.filter (fun j : Fin r => j ∈ J) = J := by ext j; simp
      rw [hJeq]
      rw [← Finset.prod_filter_mul_prod_filter_not J (fun j => j ∈ B) (fun j => (choice j).card)]
      have ha : ∏ j ∈ J.filter (fun j => j ∈ B), (choice j).card = 1 := by
        refine Finset.prod_eq_one ?_
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hJ, hB⟩
        simp [choice, hJ, hB, only1Set_card]
      have hb : ∏ j ∈ J.filter (fun j => j ∉ B), (choice j).card = 6 ^ (J.card - B.card) := by
        have hval : ∀ j ∈ J.filter (fun j => j ∉ B), (choice j).card = 6 := by
          intro j hj
          rcases Finset.mem_filter.mp hj with ⟨hJ, hB⟩
          simp [choice, hJ, hB, only0Set_card]
        rw [Finset.prod_congr rfl hval, Finset.prod_const]
        have hcard : (J.filter (fun j => j ∉ B)).card = J.card - B.card := by
          have h1 : J.filter (fun j => j ∉ B) = J \ B := by ext j; simp
          rw [h1, Finset.card_sdiff, Finset.inter_eq_left.mpr hBJ]
        rw [hcard]
      rw [ha, hb, one_mul]
    rw [hp1, hp2]
  have hsupp_eq : supp menu =
      (Finset.univ : Finset (Finset (Fin r))).biUnion (fun J =>
        (menu.image (fun e => e ∩ J)).biUnion (fun B => fiber J B)) := by
    ext t
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image, fiber]
    constructor
    · rintro ⟨e, he, hne⟩
      have heq := (hat_ne_zero_iff e t).mp hne
      refine ⟨Jof t, Bof t, ⟨e, he, heq⟩, rfl, rfl⟩
    · rintro ⟨J, B, ⟨e, he, rfl⟩, rfl, hB⟩
      refine ⟨e, he, (hat_ne_zero_iff e t).mpr hB.symm⟩
  have hdisj_J : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Finset (Fin r))) : Set _)
      (fun J => (menu.image (fun e => e ∩ J)).biUnion (fun B => fiber J B)) := by
    intro J₁ _ J₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    rcases ht1 with ⟨_, _, hJ1, _⟩
    rcases ht2 with ⟨_, _, hJ2, _⟩
    exact hne (hJ1.symm.trans hJ2)
  rw [hsupp_eq, Finset.card_biUnion hdisj_J]
  refine Finset.sum_congr rfl ?_
  intro J _
  have hdisj_B : Set.PairwiseDisjoint (↑(menu.image (fun e => e ∩ J)) : Set _)
      (fun B => fiber J B) := by
    intro B₁ _ B₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    exact hne (ht1.2.symm.trans ht2.2)
  rw [Finset.card_biUnion hdisj_B, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨e, _, rfl⟩
  exact hfiber_card J (e ∩ J) Finset.inter_subset_right

private def rowVec {r : Nat} (e : Finset (Fin r)) (z : Fin r → Fin 16) :
    (Fin r → Fin 16) → ZMod 11 :=
  fun t => hat e t * chi t z

private lemma coord_mem_span_rowVec {r : Nat} (e : Finset (Fin r)) (t₀ : Fin r → Fin 16)
    (ht₀ : hat e t₀ ≠ 0) :
    Pi.single t₀ (1 : ZMod 11) ∈
      Submodule.span (ZMod 11) (Set.range (fun z : Fin r → Fin 16 => rowVec e z)) := by
  have hsum_mem :
      ∑ z : Fin r → Fin 16, chi t₀ z • rowVec e z ∈
        Submodule.span (ZMod 11) (Set.range (fun z : Fin r → Fin 16 => rowVec e z)) := by
    refine Submodule.sum_mem _ ?_
    intro z _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, rfl⟩)
  have hsum_eq :
      ∑ z : Fin r → Fin 16, chi t₀ z • rowVec e z =
        (hat e t₀ * (16 : ZMod 11) ^ r) • Pi.single t₀ (1 : ZMod 11) := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowVec, Pi.single_apply]
    have hpull : ∑ z : Fin r → Fin 16, chi t₀ z * (hat e t * chi t z) =
        hat e t * ∑ z : Fin r → Fin 16, chi t₀ z * chi t z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _; ring
    rw [hpull, chi_orth]
    by_cases h : t = t₀
    · subst h; simp
    · have h' : t₀ ≠ t := Ne.symm h
      simp [h, h']
  have hc_ne : hat e t₀ * (16 : ZMod 11) ^ r ≠ 0 :=
    mul_ne_zero ht₀ (pow_ne_zero r sixteen_ne_zero)
  have hscaled := Submodule.smul_mem _ (hat e t₀ * (16 : ZMod 11) ^ r)⁻¹ hsum_mem
  rw [hsum_eq, smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at hscaled
  exact hscaled

private lemma rowVec_mem_coordSpan {r : Nat} (e : Finset (Fin r)) (z : Fin r → Fin 16)
    (S : Finset (Fin r → Fin 16)) (hS : ∀ t, hat e t ≠ 0 → t ∈ S) :
    rowVec e z ∈ Submodule.span (ZMod 11) ((S : Set (Fin r → Fin 16)).image (fun t => Pi.single t (1 : ZMod 11))) := by
  have heq : rowVec e z = ∑ t ∈ S, (hat e t * chi t z) • Pi.single t (1 : ZMod 11) := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, rowVec]
    by_cases ht : t ∈ S
    · simp [ht]
    · have h0 : hat e t = 0 := by
        by_contra hne; exact ht (hS t hne)
      simp [ht, h0]
  rw [heq]
  refine Submodule.sum_mem _ ?_
  intro t ht
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)

private lemma pass_bool_eq {r : Nat} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    ((Finset.univ : Finset (Fin r)).toList.all (fun j =>
      let w := (z j).val ^^^ (x j).val
      (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))) = true ↔
    ∀ j : Fin r, ker1 (decide (j ∈ e)) (xor16 (z j) (x j)) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h j
    have hj := h j (Finset.mem_toList.mpr (Finset.mem_univ j))
    simpa [ker1, xor16_val] using hj
  · intro h j _
    simpa [ker1, xor16_val] using h j

private lemma passFn_eq_ite {r : Nat} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    passFn e z x =
      if ((Finset.univ : Finset (Fin r)).toList.all (fun j =>
        let w := (z j).val ^^^ (x j).val
        (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))) = true
      then (1 : ZMod 11) else 0 := by
  by_cases h : ∀ j : Fin r, ker1 (decide (j ∈ e)) (xor16 (z j) (x j)) = true
  · have h1 := (pass_bool_eq e z x).mpr h
    simp only [h1, ↓reduceIte, passFn]
    refine Finset.prod_eq_one ?_
    intro j _
    simp [h j]
  · have h1 : ¬ ((Finset.univ : Finset (Fin r)).toList.all (fun j =>
        let w := (z j).val ^^^ (x j).val
        (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))) = true :=
      fun ht => h ((pass_bool_eq e z x).mp ht)
    simp only [h1, ↓reduceIte, passFn]
    push_neg at h
    rcases h with ⟨j, hj⟩
    have hjf : ker1 (decide (j ∈ e)) (xor16 (z j) (x j)) = false := by
      cases hk : ker1 (decide (j ∈ e)) (xor16 (z j) (x j)) <;> simp_all
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjf])

private lemma span_rowVec_eq_top_iff {r : Nat} (qs : Finset (Finset (Fin r) × (Fin r → Fin 16))) :
    Submodule.span (ZMod 11)
      ((qs : Set (Finset (Fin r) × (Fin r → Fin 16))).image (fun q => rowVec q.1 q.2)) = ⊤ ↔
    ∀ f : (Fin r → Fin 16) → ZMod 11,
      (∀ q ∈ qs, ∑ t : Fin r → Fin 16, rowVec q.1 q.2 t * f t = 0) → f = 0 := by
  let V := (Fin r → Fin 16) → ZMod 11
  let M : Submodule (ZMod 11) V :=
    Submodule.span (ZMod 11)
      ((qs : Set (Finset (Fin r) × (Fin r → Fin 16))).image (fun q => rowVec q.1 q.2))
  let dotL : V →ₗ[ZMod 11] (V →ₗ[ZMod 11] ZMod 11) :=
    { toFun := fun f =>
        { toFun := fun v => ∑ t, v t * f t
          map_add' := fun u w => by
            change ∑ t, (u t + w t) * f t = (∑ t, u t * f t) + ∑ t, w t * f t
            simp_rw [add_mul, Finset.sum_add_distrib]
          map_smul' := fun c u => by
            change ∑ t, (c * u t) * f t = c * ∑ t, u t * f t
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => by ring) }
      map_add' := fun f₁ f₂ => by
        apply LinearMap.ext; intro v
        change ∑ t, v t * (f₁ t + f₂ t) = (∑ t, v t * f₁ t) + ∑ t, v t * f₂ t
        simp_rw [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        apply LinearMap.ext; intro v
        change ∑ t, v t * (c * f t) = c * ∑ t, v t * f t
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => by ring) }
  have hdot_inj : Function.Injective dotL := by
    intro f₁ f₂ h
    funext t
    have ht := LinearMap.congr_fun h (Pi.single t (1 : ZMod 11) : V)
    change ∑ x, (Pi.single t (1 : ZMod 11) : V) x * f₁ x =
      ∑ x, (Pi.single t (1 : ZMod 11) : V) x * f₂ x at ht
    simpa [Pi.single_apply] using ht
  have hdot_surj : Function.Surjective dotL := by
    intro φ
    refine ⟨fun t => φ (Pi.single t (1 : ZMod 11) : V), ?_⟩
    apply LinearMap.ext; intro v
    have hv : v = ∑ t : Fin r → Fin 16, v t • (Pi.single t (1 : ZMod 11) : V) := by
      funext t; simp [Pi.single_apply]
    change ∑ t, v t * φ (Pi.single t (1 : ZMod 11) : V) = φ v
    conv_rhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_smul, smul_eq_mul]
  constructor
  · intro htop f hzero
    have hall : ∀ v ∈ M, dotL f v = 0 := by
      intro v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨q, hq, rfl⟩; exact hzero q hq
      · simp
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro c x _ hx; rw [map_smul, hx, smul_zero]
    have h0 : dotL f = dotL 0 := by
      apply LinearMap.ext; intro v
      have hv : v ∈ M := by dsimp only [M]; rw [htop]; trivial
      rw [hall v hv, map_zero, LinearMap.zero_apply]
    exact hdot_inj h0
  · intro horth
    by_contra hne
    have hex : ∃ φ : V →ₗ[ZMod 11] ZMod 11, φ ≠ 0 ∧ ∀ v ∈ M, φ v = 0 := by
      rcases Submodule.exists_isCompl M with ⟨N, hMN⟩
      have hN_ne : N ≠ ⊥ := by
        intro hbot
        have htop : M = ⊤ := by
          have := hMN.sup_eq_top
          rwa [hbot, sup_bot_eq] at this
        exact hne htop
      have hex_y : ∃ y ∈ N, y ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hN_ne
        rw [eq_bot_iff]
        intro y hy
        rw [Submodule.mem_bot]
        exact hall y hy
      rcases hex_y with ⟨y, hyN, hy0⟩
      let b := Module.Basis.ofVectorSpace (ZMod 11) N
      have hex_i : ∃ i, b.repr ⟨y, hyN⟩ i ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hrep0 : b.repr ⟨y, hyN⟩ = 0 := by ext i; exact hall i
        have hy_sub : (⟨y, hyN⟩ : N) = 0 := b.repr.injective (by simpa using hrep0)
        exact hy0 (congrArg Subtype.val hy_sub)
      rcases hex_i with ⟨i, hi⟩
      let proj : V →ₗ[ZMod 11] N := Submodule.linearProjOfIsCompl N M hMN.symm
      refine ⟨(b.coord i).comp proj, ?_, ?_⟩
      · intro h0
        have hy_app := LinearMap.congr_fun h0 y
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hy_app
        have hpy : proj y = ⟨y, hyN⟩ := Submodule.linearProjOfIsCompl_apply_left hMN.symm ⟨y, hyN⟩
        rw [hpy] at hy_app
        exact hi hy_app
      · intro v hv
        simp only [LinearMap.comp_apply]
        have hpv : proj v = 0 := Submodule.linearProjOfIsCompl_apply_right hMN.symm ⟨v, hv⟩
        rw [hpv, map_zero]
    rcases hex with ⟨φ, hφ_ne, hφ_zero⟩
    rcases hdot_surj φ with ⟨f, hf⟩
    have hf0 : f = 0 := horth f (fun q hq => by
      have hmem : rowVec q.1 q.2 ∈ M := Submodule.subset_span ⟨q, hq, rfl⟩
      have := hφ_zero _ hmem
      rw [← hf] at this
      exact this)
    subst hf0
    exact hφ_ne (by simpa using hf.symm)

theorem main_proof :
    ∀ (r : Nat) (budget : Finset (Fin r) → Nat),
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
      let rho := fun (menu : Finset Kind) => kinds.sum (fun J =>
        9 ^ (r - J.card) * (menu.image (fun e => e ∩ J)).sum (fun B => 6 ^ (J.card - B.card)))
      (∀ menu : Finset Kind,
        ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
          ∀ q ∈ menu.product cube, zeroRead d q)).card = 11 ^ (16 ^ r - rho menu)) ∧
      ((∃ qs : Finset (Kind × Word),
        (∀ e : Kind, (qs.filter (fun q => q.1 = e)).card ≤ budget e) ∧
        ∀ d : Word → Fin 11, (∀ q ∈ qs, zeroRead d q) → ∀ x, (d x).val = 0) ↔
          ∀ menu : Finset Kind, 16 ^ r ≤ rho menu + (kinds \ menu).sum budget) := by
  classical
  intro r budget
  dsimp only
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let toF : (Word → Fin 11) ≃ (Word → ZMod 11) :=
    { toFun := fun d x => ((d x).val : ZMod 11)
      invFun := fun f x => ⟨(f x).val, ZMod.val_lt (f x)⟩
      left_inv := fun d => by
        funext x
        apply Fin.ext
        exact ZMod.val_natCast_of_lt (d x).isLt
      right_inv := fun f => by
        funext x
        exact ZMod.natCast_zmod_val (f x) }
  have hzero_iff : ∀ (d : Word → Fin 11) (e : Kind) (z : Word),
      (((Finset.univ : Finset Word).filter (fun x =>
        (Finset.univ : Finset (Fin r)).toList.all (fun j =>
          let w := (z j).val ^^^ (x j).val
          (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0)))).sum
        (fun x => (d x).val)) % 11 = 0 ↔
      ∑ x : Word, passFn e z x * toF d x = 0 := by
    intro d e z
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    push_cast
    have hsum :
        ∑ x ∈ (Finset.univ : Finset Word).filter (fun x =>
          (Finset.univ : Finset (Fin r)).toList.all (fun j =>
            let w := (z j).val ^^^ (x j).val
            (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))),
          ((d x).val : ZMod 11) =
        ∑ x : Word, passFn e z x * toF d x := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [passFn_eq_ite]
      split_ifs <;> simp [toF]
    rw [hsum]
  constructor
  · intro menu
    let eW : (Word → Fin 11) ≃ (Word → ZMod 11) :=
      toF.trans (Equiv.ofBijective (@wht r) wht_bijective)
    let target : Finset (Word → ZMod 11) :=
      Finset.univ.filter (fun f => ∀ t ∈ supp menu, f t = 0)
    have hcard_eq :
        ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
          ∀ q ∈ menu.product (Finset.univ : Finset Word),
            (((Finset.univ : Finset Word).filter (fun x =>
              (Finset.univ : Finset (Fin r)).toList.all (fun j =>
                let w := (q.2 j).val ^^^ (x j).val
                (w &&& 3) != 0 && (w &&& 13) != (if j ∈ q.1 then 1 else 0)))).sum
              (fun x => (d x).val)) % 11 = 0)).card =
        target.card := by
      refine Finset.card_bij (fun d _ => eW d) ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        simp only [target, Finset.mem_filter, Finset.mem_univ, true_and, supp]
        rintro t ⟨e, he, hne⟩
        have hz : ∀ z : Word, ∑ x : Word, passFn e z x * toF d x = 0 := fun z =>
          (hzero_iff d e z).mp (hd (e, z) (Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩))
        exact (all_z_zero_iff e (toF d)).mp hz t hne
      · intro d₁ _ d₂ _ h; exact eW.injective h
      · intro f hf
        refine ⟨eW.symm f, ?_, eW.apply_symm_apply f⟩
        simp only [target, Finset.mem_filter, Finset.mem_univ, true_and, supp] at hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro q hq
        have he : q.1 ∈ menu := (Finset.mem_product.mp hq).1
        rw [hzero_iff]
        have hwf : wht (toF (eW.symm f)) = f := eW.apply_symm_apply f
        have hall : ∀ t : Word, hat q.1 t ≠ 0 → wht (toF (eW.symm f)) t = 0 := by
          intro t hne
          rw [hwf]
          exact hf t ⟨q.1, he, hne⟩
        exact (all_z_zero_iff q.1 (toF (eW.symm f))).mpr hall q.2
    rw [hcard_eq]
    have ht_card : target.card = 11 ^ (16 ^ r - (supp menu).card) := by
      let eSub : {f : Word → ZMod 11 // f ∈ target} ≃ ({t : Word // t ∉ supp menu} → ZMod 11) :=
        { toFun := fun f t => f.1 t.1
          invFun := fun g =>
            ⟨fun t => if h : t ∈ supp menu then 0 else g ⟨t, h⟩, by
              simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
              intro t ht; simp [ht]⟩
          left_inv := fun ⟨f, hf⟩ => by
            ext t
            simp only [target, Finset.mem_filter, Finset.mem_univ, true_and] at hf
            by_cases ht : t ∈ supp menu
            · simp [ht, hf t ht]
            · simp [ht]
          right_inv := fun g => by
            funext ⟨t, ht⟩; simp [ht] }
      have h1 : target.card = Fintype.card {f : Word → ZMod 11 // f ∈ target} :=
        (Fintype.card_coe target).symm
      rw [h1, Fintype.card_congr eSub, Fintype.card_fun, ZMod.card]
      have hc : Fintype.card {t : Word // t ∉ supp menu} = 16 ^ r - (supp menu).card := by
        have hcomp : Fintype.card {t : Word // t ∉ supp menu} = (supp menu)ᶜ.card := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
          intro t; simp
        rw [hcomp, Finset.card_compl]
        simp [Word]
      rw [hc]
    rw [ht_card, card_supp_eq_rho]
  · constructor
    · rintro ⟨qs, hbud, hsep⟩ menu
      have hspan : Submodule.span (ZMod 11)
          ((qs : Set (Kind × Word)).image (fun q => rowVec q.1 q.2)) = ⊤ := by
        rw [span_rowVec_eq_top_iff]
        intro f hf
        let d0 : Word → ZMod 11 := (Equiv.ofBijective (@wht r) wht_bijective).symm f
        let d : Word → Fin 11 := toF.symm d0
        have hwd : wht (toF d) = f := by
          simp only [d, Equiv.apply_symm_apply]
          exact (Equiv.ofBijective (@wht r) wht_bijective).apply_symm_apply f
        have hd_zero : ∀ x, (d x).val = 0 := by
          apply hsep d
          intro q hq
          rw [hzero_iff, pass_dot_zero_iff, hwd]
          exact hf q hq
        have htoF0 : toF d = 0 := by
          funext x; simp [toF, hd_zero x]
        rw [← hwd, htoF0]
        funext t; simp [wht]
      let S_coord : Submodule (ZMod 11) (Word → ZMod 11) :=
        Submodule.span (ZMod 11)
          ((supp menu : Set Word).image (fun t => Pi.single t (1 : ZMod 11)))
      let qs_out := qs.filter (fun q => q.1 ∉ menu)
      let S_out : Submodule (ZMod 11) (Word → ZMod 11) :=
        Submodule.span (ZMod 11)
          ((qs_out : Set (Kind × Word)).image (fun q => rowVec q.1 q.2))
      have htop_le : (⊤ : Submodule (ZMod 11) (Word → ZMod 11)) ≤ S_coord ⊔ S_out := by
        rw [← hspan, Submodule.span_le]
        rintro _ ⟨q, hq, rfl⟩
        by_cases hqm : q.1 ∈ menu
        · apply Submodule.mem_sup_left
          exact rowVec_mem_coordSpan q.1 q.2 (supp menu) (fun t hne =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.1, hqm, hne⟩)
        · apply Submodule.mem_sup_right
          exact Submodule.subset_span ⟨q, Finset.mem_filter.mpr ⟨hq, hqm⟩, rfl⟩
      have htop_eq : S_coord ⊔ S_out = ⊤ := top_unique htop_le
      have hdim_top : Module.finrank (ZMod 11) (Word → ZMod 11) = 16 ^ r := by
        simp [Word]
      have hdim_coord : Module.finrank (ZMod 11) S_coord ≤ (supp menu).card := by
        let fc : Finset (Word → ZMod 11) :=
          (supp menu).image (fun t => (Pi.single t (1 : ZMod 11) : Word → ZMod 11))
        have hSc : S_coord = Submodule.span (ZMod 11) (fc : Set (Word → ZMod 11)) := by
          simp [S_coord, fc]
        rw [hSc]
        have h1 : Module.finrank (ZMod 11) (Submodule.span (ZMod 11) (fc : Set (Word → ZMod 11))) ≤
            fc.card := by
          simpa using finrank_span_le_card (R := ZMod 11) (fc : Set (Word → ZMod 11))
        exact h1.trans Finset.card_image_le
      have hdim_out : Module.finrank (ZMod 11) S_out ≤ qs_out.card := by
        let fo : Finset (Word → ZMod 11) := qs_out.image (fun q => rowVec q.1 q.2)
        have hSo : S_out = Submodule.span (ZMod 11) (fo : Set (Word → ZMod 11)) := by
          simp [S_out, fo]; rfl
        rw [hSo]
        have h1 : Module.finrank (ZMod 11) (Submodule.span (ZMod 11) (fo : Set (Word → ZMod 11))) ≤
            fo.card := by
          simpa using finrank_span_le_card (R := ZMod 11) (fo : Set (Word → ZMod 11))
        exact h1.trans Finset.card_image_le
      have hsup_le : Module.finrank (ZMod 11) (S_coord ⊔ S_out : Submodule (ZMod 11) (Word → ZMod 11)) ≤
          Module.finrank (ZMod 11) S_coord + Module.finrank (ZMod 11) S_out := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq S_coord S_out
        omega
      have hqs_out_le : qs_out.card ≤ (Finset.univ \ menu).sum budget := by
        have hpart : qs_out = (Finset.univ \ menu).biUnion (fun e => qs.filter (fun q => q.1 = e)) := by
          ext q
          simp only [qs_out, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_sdiff,
            Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hq, hnot⟩; exact ⟨q.1, hnot, hq, rfl⟩
          · rintro ⟨e, hnot, hq, rfl⟩; exact ⟨hq, hnot⟩
        rw [hpart]
        calc ((Finset.univ \ menu).biUnion (fun e => qs.filter (fun q => q.1 = e))).card
            ≤ (Finset.univ \ menu).sum (fun e => (qs.filter (fun q => q.1 = e)).card) :=
              Finset.card_biUnion_le
          _ ≤ (Finset.univ \ menu).sum budget := Finset.sum_le_sum (fun e _ => hbud e)
      have hfin_top : Module.finrank (ZMod 11) (S_coord ⊔ S_out : Submodule (ZMod 11) (Word → ZMod 11)) =
          16 ^ r := by
        rw [htop_eq, finrank_top, hdim_top]
      rw [← card_supp_eq_rho]
      omega
    · intro hhall_hyp
      let Slot := Σ e : Kind, Fin (budget e)
      let N : Word → Finset Slot := fun t =>
        Finset.univ.filter (fun s => hat s.1 t ≠ 0)
      have hhall : ∀ A : Finset Word, A.card ≤ (A.biUnion N).card := by
        intro A
        let menu : Finset Kind := Finset.univ.filter (fun e => ∀ t ∈ A, hat e t = 0)
        have hdisj : Disjoint A (supp menu) := by
          rw [Finset.disjoint_left]
          intro t htA htS
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at htS
          rcases htS with ⟨e, heM, hne⟩
          exact hne ((Finset.mem_filter.mp heM).2 t htA)
        have hA_le : A.card + (supp menu).card ≤ 16 ^ r := by
          have hun := Finset.card_union_of_disjoint hdisj
          have hle : (A ∪ supp menu).card ≤ (Finset.univ : Finset Word).card :=
            Finset.card_le_univ _
          have h16 : (Finset.univ : Finset Word).card = 16 ^ r := by simp [Word]
          omega
        have hsub_slots :
            (Finset.univ \ menu).biUnion (fun e =>
              (Finset.univ : Finset (Fin (budget e))).map
                ⟨fun k => (⟨e, k⟩ : Slot), fun _ _ h => by cases h; rfl⟩) ⊆
            A.biUnion N := by
          intro s hs
          simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_map, Function.Embedding.coeFn_mk] at hs
          rcases hs with ⟨e, hnotM, k, rfl⟩
          simp only [menu, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnotM
          rcases hnotM with ⟨t, htA, hne⟩
          exact Finset.mem_biUnion.mpr ⟨t, htA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩
        have hdisj_s : Set.PairwiseDisjoint (↑(Finset.univ \ menu) : Set Kind)
            (fun e => (Finset.univ : Finset (Fin (budget e))).map
              ⟨fun k => (⟨e, k⟩ : Slot), fun _ _ h => by cases h; rfl⟩) := by
          intro e₁ _ e₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro s hs1 hs2
          simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hs1 hs2
          rcases hs1 with ⟨k₁, rfl⟩
          rcases hs2 with ⟨k₂, h2⟩
          exact hne (congrArg Sigma.fst h2).symm
        have hbud_le : (Finset.univ \ menu).sum budget ≤ (A.biUnion N).card := by
          have h1 := Finset.card_le_card hsub_slots
          rw [Finset.card_biUnion hdisj_s] at h1
          have h2 : (Finset.univ \ menu).sum (fun e =>
              ((Finset.univ : Finset (Fin (budget e))).map
                ⟨fun k => (⟨e, k⟩ : Slot), fun _ _ h => by cases h; rfl⟩).card) =
              (Finset.univ \ menu).sum budget := by
            refine Finset.sum_congr rfl ?_
            intro e _; simp
          omega
        have hhyp := hhall_hyp menu
        rw [← card_supp_eq_rho] at hhyp
        omega
      rcases (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hhall with
        ⟨matchSlot, hmatch_inj, hmatch_mem⟩
      let assign : Word → Kind := fun t => (matchSlot t).1
      have hassign_ne : ∀ t : Word, hat (assign t) t ≠ 0 := fun t =>
        (Finset.mem_filter.mp (hmatch_mem t)).2
      have hassign_bud : ∀ e : Kind, (Finset.univ.filter (fun t => assign t = e)).card ≤ budget e := by
        intro e
        have hsub : (Finset.univ.filter (fun t => assign t = e)).image matchSlot ⊆
            (Finset.univ : Finset (Fin (budget e))).map
              ⟨fun k => (⟨e, k⟩ : Slot), fun _ _ h => by cases h; rfl⟩ := by
          intro s hs
          rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
          have he : (matchSlot t).1 = e := (Finset.mem_filter.mp ht).2
          rcases hms : matchSlot t with ⟨e', k⟩
          have heq : e' = e := by rw [hms] at he; exact he
          subst heq
          exact Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩
        have hc1 := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ hmatch_inj] at hc1
        simpa using hc1
      have hswap : ∀ S : Finset Word,
          ∃ qs : Finset (Kind × Word),
            (∀ e : Kind, (qs.filter (fun q => q.1 = e)).card ≤
              (S.filter (fun t => assign t = e)).card) ∧
            Submodule.span (ZMod 11)
              (((qs : Set (Kind × Word)).image (fun q => rowVec q.1 q.2)) ∪
               (((Finset.univ \ S : Finset Word) : Set Word).image
                 (fun t => Pi.single t (1 : ZMod 11)))) = ⊤ := by
        intro S
        induction S using Finset.induction_on with
        | empty =>
          refine ⟨∅, ?_, ?_⟩
          · intro e; simp
          · simp only [Finset.coe_empty, Set.image_empty, Set.empty_union, Finset.sdiff_empty]
            rw [eq_top_iff]
            intro v _
            have hv : v = ∑ t : Word, v t • Pi.single t (1 : ZMod 11) := by
              funext t; simp [Pi.single_apply]
            rw [hv]
            refine Submodule.sum_mem _ ?_
            intro t _
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, Finset.mem_univ _, rfl⟩)
        | @insert t₀ S ht₀ ih =>
          rcases ih with ⟨qs, hqbud, hqspan⟩
          let W : Submodule (ZMod 11) (Word → ZMod 11) :=
            Submodule.span (ZMod 11)
              (((qs : Set (Kind × Word)).image (fun q => rowVec q.1 q.2)) ∪
               (((Finset.univ \ insert t₀ S : Finset Word) : Set Word).image
                 (fun t => Pi.single t (1 : ZMod 11))))
          have hsup_top : W ⊔ Submodule.span (ZMod 11) {Pi.single t₀ (1 : ZMod 11)} = ⊤ := by
            rw [← hqspan, ← Submodule.span_union]
            congr 1
            ext v
            simp only [Set.mem_union, Set.mem_image, Finset.mem_coe, Finset.mem_sdiff,
              Finset.mem_univ, true_and, Finset.mem_insert, Set.mem_singleton_iff]
            constructor
            · rintro ((h | ⟨t, ht, rfl⟩) | rfl)
              · exact Or.inl h
              · exact Or.inr ⟨t, fun hS => ht (Or.inr hS), rfl⟩
              · exact Or.inr ⟨t₀, ht₀, rfl⟩
            · rintro (h | ⟨t, ht, rfl⟩)
              · exact Or.inl (Or.inl h)
              · by_cases heq : t = t₀
                · subst heq; exact Or.inr rfl
                · exact Or.inl (Or.inr ⟨t, by push_neg; exact ⟨heq, ht⟩, rfl⟩)
          by_cases hmem : Pi.single t₀ (1 : ZMod 11) ∈ W
          · refine ⟨qs, ?_, ?_⟩
            · intro e
              exact (hqbud e).trans (Finset.card_le_card (Finset.filter_subset_filter _
                (Finset.subset_insert _ _)))
            · have hsp : Submodule.span (ZMod 11) {Pi.single t₀ (1 : ZMod 11)} ≤ W :=
                Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
              rwa [sup_eq_left.mpr hsp] at hsup_top
          · have hex_z : ∃ z₀ : Word, rowVec (assign t₀) z₀ ∉ W := by
              by_contra hall
              push_neg at hall
              have hle : Submodule.span (ZMod 11)
                  (Set.range (fun z : Word => rowVec (assign t₀) z)) ≤ W := by
                rw [Submodule.span_le]
                rintro _ ⟨z, rfl⟩
                exact hall z
              exact hmem (hle (coord_mem_span_rowVec (assign t₀) t₀ (hassign_ne t₀)))
            rcases hex_z with ⟨z₀, hz₀⟩
            have hnot_in_qs : (assign t₀, z₀) ∉ qs := by
              intro hin
              apply hz₀
              exact Submodule.subset_span (Or.inl ⟨(assign t₀, z₀), hin, rfl⟩)
            refine ⟨insert (assign t₀, z₀) qs, ?_, ?_⟩
            · intro e
              by_cases he : assign t₀ = e
              · have h1 : ((insert (assign t₀, z₀) qs).filter (fun q => q.1 = e)).card =
                    (qs.filter (fun q => q.1 = e)).card + 1 := by
                  rw [Finset.filter_insert, if_pos he, Finset.card_insert_of_notMem]
                  intro h; exact hnot_in_qs (Finset.mem_filter.mp h).1
                have h2 : ((insert t₀ S).filter (fun t => assign t = e)).card =
                    (S.filter (fun t => assign t = e)).card + 1 := by
                  rw [Finset.filter_insert, if_pos he, Finset.card_insert_of_notMem]
                  intro h; exact ht₀ (Finset.mem_filter.mp h).1
                have hb := hqbud e
                omega
              · have h1 : (insert (assign t₀, z₀) qs).filter (fun q => q.1 = e) =
                    qs.filter (fun q => q.1 = e) := by
                  rw [Finset.filter_insert, if_neg he]
                have h2 : (insert t₀ S).filter (fun t => assign t = e) =
                    S.filter (fun t => assign t = e) := by
                  rw [Finset.filter_insert, if_neg he]
                rw [h1, h2]
                exact hqbud e
            · have hdecomp : rowVec (assign t₀) z₀ ∈ W ⊔ Submodule.span (ZMod 11) {Pi.single t₀ (1 : ZMod 11)} := by
                rw [hsup_top]; trivial
              rcases Submodule.mem_sup.mp hdecomp with ⟨w, hwW, y, hy, hwy⟩
              rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
              have hc_ne : c ≠ 0 := by
                intro hc0; subst hc0; simp only [zero_smul, add_zero] at hwy
                exact hz₀ (hwy ▸ hwW)
              let qs' : Finset (Kind × Word) := insert (assign t₀, z₀) qs
              let W' : Submodule (ZMod 11) (Word → ZMod 11) :=
                Submodule.span (ZMod 11)
                  (((qs' : Set (Kind × Word)).image (fun q => rowVec q.1 q.2)) ∪
                   (((Finset.univ \ insert t₀ S : Finset Word) : Set Word).image
                      (fun t => Pi.single t (1 : ZMod 11))))
              have hW_le : W ≤ W' := by
                apply Submodule.span_mono
                intro v hv
                rcases hv with ⟨q, hq, rfl⟩ | h
                · exact Or.inl ⟨q, Finset.mem_insert_of_mem hq, rfl⟩
                · exact Or.inr h
              have hrv_in : rowVec (assign t₀) z₀ ∈ W' :=
                Submodule.subset_span (Or.inl ⟨(assign t₀, z₀), Finset.mem_insert_self _ _, rfl⟩)
              have ht0_in : Pi.single t₀ (1 : ZMod 11) ∈ W' := by
                have hdiff : c • Pi.single t₀ (1 : ZMod 11) ∈ W' := by
                  have hsub := Submodule.sub_mem W' hrv_in (hW_le hwW)
                  have heq : rowVec (assign t₀) z₀ - w = c • Pi.single t₀ (1 : ZMod 11) := by
                    rw [← hwy]; abel
                  rwa [heq] at hsub
                have hsc := Submodule.smul_mem W' c⁻¹ hdiff
                rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at hsc
              have hle_top : (⊤ : Submodule (ZMod 11) (Word → ZMod 11)) ≤ W' := by
                rw [← hsup_top]
                exact sup_le hW_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ht0_in))
              exact top_unique hle_top
      rcases hswap Finset.univ with ⟨qs, hqbud, hqspan⟩
      refine ⟨qs, fun e => (hqbud e).trans (hassign_bud e), ?_⟩
      simp only [Finset.sdiff_self, Finset.coe_empty, Set.image_empty, Set.union_empty] at hqspan
      intro d hd
      have hf0 : wht (toF d) = 0 :=
        (span_rowVec_eq_top_iff qs).mp hqspan (wht (toF d)) (fun q hq =>
          (pass_dot_zero_iff q.1 q.2 (toF d)).mp ((hzero_iff d q.1 q.2).mp (hd q hq)))
      have hw0 : wht (0 : Word → ZMod 11) = 0 := by funext t; simp [wht]
      have htoF0 : toF d = 0 := wht_bijective.1 (hf0.trans hw0.symm)
      intro x
      have hx : ((d x).val : ZMod 11) = 0 := congrFun htoF0 x
      have hdvd : 11 ∣ (d x).val := (ZMod.natCast_eq_zero_iff _ _).mp hx
      have hlt : (d x).val < 11 := (d x).isLt
      omega

end PEqualNP.Outside.L_lib_1156

theorem PEqualNP.Outside.L_lib_1156 :
∀ (r : Nat) (budget : Finset (Fin r) → Nat),
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
  let rho := fun (menu : Finset Kind) => kinds.sum (fun J =>
    9 ^ (r - J.card) * (menu.image (fun e => e ∩ J)).sum (fun B => 6 ^ (J.card - B.card)))
  (∀ menu : Finset Kind,
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ menu.product cube, zeroRead d q)).card = 11 ^ (16 ^ r - rho menu)) ∧
  ((∃ qs : Finset (Kind × Word),
    (∀ e : Kind, (qs.filter (fun q => q.1 = e)).card ≤ budget e) ∧
    ∀ d : Word → Fin 11, (∀ q ∈ qs, zeroRead d q) → ∀ x, (d x).val = 0) ↔
      ∀ menu : Finset Kind, 16 ^ r ≤ rho menu + (kinds \ menu).sum budget) :=
  PEqualNP.Outside.L_lib_1156.main_proof
