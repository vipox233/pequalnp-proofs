import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Combinatorics.Enumerative.Stirling
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_856

def bm {D : Nat} (f : Fin (D+1) → Nat) (j : Nat) : Nat :=
  ∑ i, f i * i.val.choose j

end PEqualNP.Outside.L_lib_856

namespace PEqualNP.Outside.L_lib_856

private theorem choose_square_lower (D : Nat) : D ^ D ≤ Nat.choose (D ^ 2 + D) D := by
  suffices h : ∀ a ≤ D, D ^ a ≤ Nat.choose (D ^ 2 + D) a from h D le_rfl
  intro a ha
  induction a with
  | zero => simp
  | succ a ih =>
    apply Nat.le_of_mul_le_mul_right (c := a+1) ?_ (by omega)
    rw [Nat.choose_succ_right_eq, pow_succ, Nat.mul_assoc]
    apply Nat.mul_le_mul (ih (by omega))
    calc
      D * (a + 1) ≤ D * D := Nat.mul_le_mul_left D ha
      _ ≤ D ^ 2 + D - a := by rw [pow_two]; omega

private theorem twice_slot_exponents (d : Nat) :
    2 * (∑ j ∈ Finset.range d, (j+4)) = d * (d+7) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

theorem special_slots (D d P : Nat)
    (h : ∃ k : Nat, 0 < k ∧ D = 2 ^ k ∧ P = D ^ 2 ∧ d * (d + 7) < 2 * D) :
    (∏ j ∈ Finset.range d, (P * Nat.choose D (j + 1) + 1)) < Nat.choose (P + D) D := by
  obtain ⟨k, hk, hD, rfl, hsmall⟩ := h
  have htwo : 2 ≤ D := by
    rw [hD]
    calc 2 = 2 ^ 1 := by rfl
         _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hterm (j : Nat) : D ^ 2 * Nat.choose D (j+1) + 1 ≤ D ^ (j+4) := by
    have hp : 0 < D ^ (j+3) := Nat.pow_pos (by omega)
    calc
      _ ≤ D ^ 2 * D ^ (j+1) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _)) 1
      _ = D ^ (j+3) + 1 := by rw [← pow_add, show 2 + (j+1) = j+3 by omega]
      _ ≤ D ^ (j+3) * 2 := by omega
      _ ≤ D ^ (j+3) * D := Nat.mul_le_mul_left _ htwo
      _ = D ^ (j+4) := (pow_succ D (j+3)).symm
  have hprod (r : Nat) : (∏ j ∈ Finset.range r, (D ^ 2 * Nat.choose D (j+1) + 1)) ≤
      D ^ (∑ j ∈ Finset.range r, (j+4)) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_add]
      exact Nat.mul_le_mul ih (hterm r)
  have hexp : (∑ j ∈ Finset.range d, (j+4)) < D := by
    have := twice_slot_exponents d
    omega
  exact lt_of_le_of_lt (hprod d) (lt_of_lt_of_le (Nat.pow_lt_pow_right htwo hexp) (choose_square_lower D))

end PEqualNP.Outside.L_lib_856

namespace PEqualNP.Outside.L_lib_856

theorem collision (D d P : Nat)
    (h : (∏ j ∈ Finset.range d, (P * Nat.choose D (j+1)+1)) < Nat.choose (P+D) D) :
    ∃ f g : Fin (D+1) → Nat, (∑ i, f i) = P ∧ (∑ i, g i) = P ∧ f ≠ g ∧
      ∀ n ≤ d, bm f n = bm g n := by
  classical
  let hist (s : Sym (Fin (D+1)) P) : Fin (D+1) → Nat := fun i => s.val.count i
  have mass (s : Sym (Fin (D+1)) P) : (∑ i, hist s i) = P := by
    change (∑ i, s.val.count i) = P
    rw [Multiset.sum_count_eq_card (by simp)]
    exact s.property
  have bound (s : Sym (Fin (D+1)) P) (j : Nat) : bm (hist s) j ≤ P * D.choose j := by
    calc bm (hist s) j
        ≤ ∑ i : Fin (D+1), hist s i * D.choose j := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.mul_le_mul_left _ (Nat.choose_le_choose j (Nat.le_of_lt_succ i.isLt))
      _ = P * D.choose j := by rw [← Finset.sum_mul, mass]
  let profile (s : Sym (Fin (D+1)) P) (j : Fin d) : Fin (P * D.choose (j.val+1)+1) :=
    ⟨bm (hist s) (j.val+1), Nat.lt_succ_of_le (bound s _)⟩
  have hc : Fintype.card ((j : Fin d) → Fin (P * D.choose (j.val+1)+1)) <
      Fintype.card (Sym (Fin (D+1)) P) := by
    rw [Fintype.card_pi, Sym.card_sym_eq_choose]
    simp only [Fintype.card_fin]
    rw [Fin.prod_univ_eq_prod_range (fun j => P * D.choose (j+1)+1) d]
    rw [show D + 1 + P - 1 = P + D by omega, Nat.choose_symm_add]
    exact h
  obtain ⟨a, b, hab, hp⟩ := Fintype.exists_ne_map_eq_of_card_lt profile hc
  refine ⟨hist a, hist b, mass a, mass b, ?_, ?_⟩
  · intro hh
    apply hab
    apply Subtype.ext
    apply Multiset.ext'
    intro i
    exact congrFun hh i
  · intro n hn
    cases n with
    | zero => simpa [bm] using (mass a).trans (mass b).symm
    | succ j =>
      have hj : j < d := by omega
      exact congrArg Fin.val (congrFun hp ⟨j,hj⟩)

end PEqualNP.Outside.L_lib_856

namespace PEqualNP.Outside.L_lib_856

private def shiftTail {D : Nat} (f : Fin (D+2) → Nat) (i : Fin (D+1)) : Nat :=
  f i.succ

private theorem shift_pascal {D : Nat} (f : Fin (D+2) → Nat) (n : Nat) :
    bm f (n+1) = bm (shiftTail f) n + bm (shiftTail f) (n+1) := by
  unfold bm
  rw [Fin.sum_univ_succ]
  simp [shiftTail, Nat.choose_succ_succ', Nat.mul_add, Finset.sum_add_distrib]

private def shiftExtend {D : Nat} (f : Fin (D+1) → Nat) (a : Nat) : Fin (D+2) → Nat :=
  Fin.lastCases a f

private theorem shift_mass {D : Nat} (f : Fin (D+1) → Nat) (a : Nat) :
    (∑ i, shiftExtend f a i) = (∑ i, f i) + a := by
  rw [Fin.sum_univ_castSucc]
  simp [shiftExtend]

private theorem shift_bm_extend {D : Nat} (f : Fin (D+1) → Nat) (a n : Nat) :
    bm (shiftExtend f a) n = bm f n + a * (D+1).choose n := by
  unfold bm
  rw [Fin.sum_univ_castSucc]
  simp [shiftExtend]

private theorem shift_extend_zero {D : Nat} (f : Fin (D+1) → Nat) (a : Nat) :
    shiftExtend f a 0 = f 0 := by
  change shiftExtend f a (Fin.castSucc (0 : Fin (D+1))) = f 0
  simp only [shiftExtend, Fin.lastCases_castSucc]

theorem shift_collision (D d P : Nat) (f g : Fin (D+1) → Nat)
    (hf : (∑ i, f i) = P) (hg : (∑ i, g i) = P) (hne : f ≠ g)
    (hm : ∀ n ≤ d, bm f n = bm g n) :
    ∃ u v : Fin (D+1) → Nat, (∑ i, u i) = P ∧ (∑ i, v i) = P ∧
      u 0 ≠ v 0 ∧ ∀ n ≤ d, bm u n = bm v n := by
  induction D generalizing P with
  | zero =>
    have eq : f 0 = g 0 := by simpa using hf.trans hg.symm
    exfalso
    apply hne
    funext i
    have hz : i = 0 := Fin.ext (by have := i.isLt; change i.val = 0; omega)
    simpa only [hz] using eq
  | succ D ih =>
    by_cases h0 : f 0 = g 0
    · let Q := ∑ i, shiftTail f i
      have hF : f 0 + Q = P := by
        simpa only [Fin.sum_univ_succ f, Q, shiftTail] using hf
      have hG : g 0 + (∑ i, shiftTail g i) = P := by
        simpa only [Fin.sum_univ_succ g, shiftTail] using hg
      have massG : (∑ i, shiftTail g i) = Q := by omega
      have htail : shiftTail f ≠ shiftTail g := by
        intro eq
        apply hne
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun eq j
      have mT : ∀ n ≤ d, bm (shiftTail f) n = bm (shiftTail g) n := by
        intro n
        induction n with
        | zero => intro _; simpa [bm, Q] using massG.symm
        | succ n ihn =>
          intro hn
          have total := hm (n+1) hn
          rw [shift_pascal, shift_pascal] at total
          have prev := ihn (by omega)
          omega
      obtain ⟨u,v,hu,hv,huv,hvm⟩ := ih Q (shiftTail f) (shiftTail g) rfl massG htail mT
      refine ⟨shiftExtend u (f 0), shiftExtend v (f 0), ?_, ?_, ?_, ?_⟩
      · rw [shift_mass, hu]; omega
      · rw [shift_mass, hv]; omega
      · rwa [shift_extend_zero, shift_extend_zero]
      · intro n hn
        rw [shift_bm_extend, shift_bm_extend, hvm n hn]
    · exact ⟨f,g,hf,hg,h0,hm⟩

end PEqualNP.Outside.L_lib_856

namespace PEqualNP.Outside.L_lib_856

theorem power_as_moments {D : Nat} (f : Fin (D+1) → Nat) (k : Nat) :
    (∑ i, f i * i.val ^ k) =
      ∑ j ∈ Finset.range (k+1), (Nat.stirlingSecond k j * j.factorial) * bm f j := by
  calc
    (∑ i, f i * i.val ^ k) =
        ∑ i, ∑ j ∈ Finset.range (k+1),
          (Nat.stirlingSecond k j * j.factorial) * (f i * i.val.choose j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ac_rfl
    _ = ∑ j ∈ Finset.range (k+1), (Nat.stirlingSecond k j * j.factorial) * bm f j := by
      rw [Finset.sum_comm]
      simp only [bm, Finset.mul_sum]

theorem ordinary_equal {D d : Nat} (f g : Fin (D+1) → Nat)
    (hm : ∀ j ≤ d, bm f j = bm g j) (n : Nat) (hn : n ≤ d) :
    (∑ i, f i * i.val ^ n) = ∑ i, g i * i.val ^ n := by
  rw [power_as_moments, power_as_moments]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hm j (by have := Finset.mem_range.mp hj; omega)]

end PEqualNP.Outside.L_lib_856

open PEqualNP.Outside.L_lib_856

theorem PEqualNP.Outside.L_lib_856 : (∀ (D d P : ℕ),
  let slots := ∏ j ∈ Finset.range d, (P * Nat.choose D (j+1) + 1)
  (slots < Nat.choose (P+D) D ∨
    (∃ k : ℕ, 0 < k ∧ D = 2^k ∧ P = D^2 ∧ d*(d+7) < 2*D)) →
  ∃ (f g : Fin (D+1) → ℕ),
    (∑ i, f i) = P ∧ (∑ i, g i) = P ∧ f 0 ≠ g 0 ∧
      ∀ n ≤ d, (∑ i : Fin (D+1), f i * i.val^n) =
        ∑ i : Fin (D+1), g i * i.val^n) := by
  intro D d P
  dsimp only
  intro h
  have hslots : (∏ j ∈ Finset.range d, (P * Nat.choose D (j+1) + 1)) < Nat.choose (P+D) D :=
    h.elim id (special_slots D d P)
  obtain ⟨f,g,hf,hg,hne,hb⟩ := collision D d P hslots
  obtain ⟨u,v,hu,hv,hd,he⟩ := shift_collision D d P f g hf hg hne hb
  exact ⟨u,v,hu,hv,hd,ordinary_equal u v he⟩
