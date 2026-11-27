import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20813_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_count (l : List ℕ) (N : ℕ) (h : ∀ i ∈ l, i < N) :
    ∑ w ∈ Finset.range N, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < N := h a (by simp)
    rw [List.length_cons, ← ih (fun i hi => h i (by simp [hi]))]
    simp [List.count_cons, Finset.sum_add_distrib, ha]

theorem key (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) :
    (∑ w ∈ Finset.range m, readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size, readsIn C (Finset.range C.size) (m + j)) =
    ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := by
  rw [← Finset.sum_range_add]
  unfold readsIn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => sum_count _ _ fun i hi => ?_
  have h1 : j < C.size := Finset.mem_range.mp hj
  have := hrb j h1 i hi
  omega

theorem slots (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length) +
      (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not) (fun d1 => Classical.propDecidable _)
        (Finset.range C.size)).card = C.size + C.size := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => 2) ?_]
  · simp [Circuit.size]
    omega
  · intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    have hmem : gateAt C j ∈ C.gates := by
      simp only [gateAt, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    rcases hg _ hmem with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem tail (s : ℕ) (f : ℕ → ℕ) (hs : 0 < s) (h : ∀ j < s, (f j = 0 ↔ j + 1 = s)) :
    (∑ j ∈ Finset.range (s - 1), (f j - 1)) + (s - 1) = ∑ j ∈ Finset.range s, f j := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : f k = 0 := (h k (by omega)).2 rfl
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, hk, Nat.add_zero]
  have : ∀ j ∈ Finset.range k, f j - 1 + 1 = f j := fun j hj => by
    have hj' : j < k := Finset.mem_range.mp hj
    have : f j ≠ 0 := fun h0 => by have := (h j (by omega)).1 h0; omega
    omega
  rw [← Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp

end PEqualNP.Outside.L_meta_20813_aux

open PEqualNP.Outside.L_meta_20813_aux in
theorem PEqualNP.Outside.L_meta_20813 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (C.size + C.size =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size,
        PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d1 => Classical.propDecidable _)
          (Finset.range C.size)).card) ∧
  (C.size + 1 =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k2 => (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C hg hrb hpos hlast
  have hk := key m C hrb
  have hs := slots C hg
  have hf : @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
      (Finset.range C.size) = Finset.range (C.size - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have ht := tail C.size (fun j => PEqualNP.MetaComplexity.NestedCover.readsIn C
    (Finset.range C.size) (m + j)) hpos hlast
  rw [hf]
  constructor <;> omega
