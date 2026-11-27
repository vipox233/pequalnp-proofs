import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20814_aux
open Finset

theorem inp (S : Finset ℕ) (a : ℕ → ℕ) :
    (∑ w ∈ @Finset.filter ℕ (fun w1 => 2 ≤ a w1) (fun _ => Classical.propDecidable _) S, a w) +
      2 * (@Finset.filter ℕ (fun w2 => 1 ≤ a w2) (fun _ => Classical.propDecidable _) S).card ≤
    2 * ∑ w ∈ S, a w := by
  rw [sum_filter, card_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun w _ => ?_
  split_ifs <;> omega

theorem gat (s : ℕ) (r : ℕ → ℕ) (P : ℕ → Prop) (h : ∀ j < s, (r j = 0 ↔ j + 1 = s)) :
    (∑ j ∈ @Finset.filter ℕ (fun j1 => P j1 ∨ 2 ≤ r j1) (fun _ => Classical.propDecidable _)
      (range s), r j) ≤
    2 * (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < s) (fun _ => Classical.propDecidable _)
      (range s), (r j - 1)) +
      2 * (@Finset.filter ℕ P (fun _ => Classical.propDecidable _) (range s)).card := by
  rw [sum_filter, sum_filter, card_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun j hj => ?_
  have hjs := mem_range.mp hj
  have e := h j hjs
  have hr : r j = 0 ∨ (1 ≤ r j ∧ j + 1 < s) := by
    by_cases h0 : r j = 0
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, by have := mt e.2 h0; omega⟩
  by_cases hp : P j <;> simp only [hp, true_or, false_or, ↓reduceIte] <;> split_ifs <;> omega

end PEqualNP.Outside.L_meta_20814_aux

open PEqualNP.Outside.L_meta_20814_aux in
theorem PEqualNP.Outside.L_meta_20814 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (∑ w ∈ @Finset.filter ℕ
        (fun w1 => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w1)
        (fun d1 => Classical.propDecidable _) (Finset.range m),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
    (∑ j ∈ @Finset.filter ℕ
        (fun j1 => (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op =
            PEqualNP.CircuitLowerBounds.GateOp.not ∨
          2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j1))
        (fun d2 => Classical.propDecidable _) (Finset.range C.size),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
    2 * (@Finset.filter ℕ
        (fun w2 => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w2)
        (fun d3 => Classical.propDecidable _) (Finset.range m)).card ≤
  2 * ((∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d4 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d5 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C _ _ _ hlast
  have h1 := inp (Finset.range m)
    (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w)
  have h2 := gat C.size
    (fun j => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j))
    (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.not) hlast
  beta_reduce at h1 h2
  omega
