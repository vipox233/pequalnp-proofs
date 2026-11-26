import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19452_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.MetaComplexity.NestedCover 

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem snoc {α : Type} (l : List α) (b d : α) (w : ℕ) :
    (l ++ [b]).getD w d = if w < l.length then l.getD w d else if w = l.length then b else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- Wires off `B` that the gates in `D` need agree. -/
theorem agree (N : ℕ) (B D : ℕ → Prop) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w, ¬ B w → x.getD w false = y.getD w false) (gs : List Gate) :
    (∀ j, D j → ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, ¬ B w ∧ (N ≤ w → w < N + j → D (w - N))) →
    ∀ w, ¬ B w → (N ≤ w → w < N + gs.length → D (w - N)) →
      (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ w hb _ => hxy w hb
  | append_singleton gs g ih =>
    intro hD w hb hw
    have ih := ih (fun j hj i hi => by
      by_cases hj' : j < gs.length
      · refine hD j hj i ?_
        rwa [snoc, if_pos hj']
      · rw [List.getD_eq_default _ _ (by omega)] at hi; simp at hi) 
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [snoc, snoc, len, len, hx, hy]
    split_ifs with h1 h2
    · exact ih w hb fun a _ => hw a (by simp; omega)
    · have hj : D gs.length := by
        have := hw (by omega) (by simp; omega); rwa [h2, Nat.add_sub_cancel_left] at this
      congr 1
      refine List.map_congr_left fun i hi => ?_
      obtain ⟨hb', hc⟩ := hD _ hj i (by simpa [snoc] using hi)
      exact ih i hb' hc
    · rfl

theorem clen (n : ℕ) (gs : List Gate) : (gs.foldl (coneStep n) []).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [List.foldl_append, coneStep, ih]

theorem cmem (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
    (j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro j i; simp
  | append_singleton gs g ih =>
    intro j i
    have hl := clen n gs
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (coneStep n) [] = F at ih hl ⊢
    unfold coneStep
    have e : ∀ k b, k < gs.length → (F ++ [b]).getD k [] = F.getD k [] := fun k b hk => by
      rw [snoc, if_pos (by omega)]
    rw [snoc, snoc, hl]
    split_ifs with h1 h2
    · rw [ih j i]
      constructor
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨by simp; omega, w, hw, h3, h4, by rwa [e _ _ (by omega)]⟩
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨h1, w, hw, h3, h4, by rwa [e _ _ (by omega)] at h5⟩
    · subst h2
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h3, h4⟩, h5⟩
        exact ⟨by simp, w, hw, h3, h4, by rwa [e _ _ (by omega)]⟩
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨w, ⟨hw, h3, h4⟩, by rwa [e _ _ (by omega)] at h5⟩
    · simp

theorem ctrans (n : ℕ) (C : Circuit) : ∀ j i k, InCone n C i j → InCone n C k i → InCone n C k j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
    intro i k hi hk
    unfold InCone cones at *
    obtain ⟨hj, w, hw, h3, h4, h5⟩ := (cmem n C.gates j i).1 hi
    refine (cmem n C.gates j k).2 ⟨hj, w, hw, h3, h4, Or.inr ?_⟩
    rcases h5 with rfl | h5
    · exact hk
    · exact ihj _ (by omega) i k h5 hk

/-- The output cone is closed under reading earlier gates. -/
theorem oclosed (N : ℕ) (C : Circuit) (j : ℕ) (hj : InOutputCone N C j) (w : ℕ)
    (hw : w ∈ (gateAt C j).inputs) (h1 : N ≤ w) (h2 : w < N + j) : InOutputCone N C (w - N) := by
  have hd : InCone N C (w - N) j := by
    unfold InCone cones
    exact (cmem N C.gates j _).2 ⟨hj.1, w, hw, h1, h2, Or.inl rfl⟩
  refine ⟨by have := hj.1; omega, Or.inr ?_⟩
  rcases hj.2 with h | ⟨h3, h4⟩
  · exact ⟨by omega, by rwa [h, Nat.add_sub_cancel_left]⟩
  · exact ⟨h3, ctrans N C _ _ _ h4 hd⟩

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem silent (N : ℕ) (C : Circuit) (B : ℕ → Prop)
    (hB : ∀ j, InOutputCone N C j → ∀ w ∈ (gateAt C j).inputs, ¬ B w) (ho : ¬ B C.output)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w, ¬ B w → x.getD w false = y.getD w false) : C.eval x = C.eval y :=
  agree N B (InOutputCone N C) x y hx hy hxy C.gates
    (fun j hj w hw => ⟨hB j hj w hw, oclosed N C j hj w hw⟩) _ ho
    (fun h1 h2 => ⟨by omega, Or.inl (by omega)⟩)

theorem gd (C : Circuit) {j : ℕ} (h : j < C.gates.length) :
    C.gates.getD j ⟨GateOp.and, []⟩ = gateAt C j := by
  rw [gateAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

end PEqualNP.Outside.L_meta_19452_aux

open PEqualNP.Outside.L_meta_19452_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.MetaComplexity.NestedCover  in
theorem PEqualNP.Outside.L_meta_19452 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u u' : Fin n), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ u'.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u'.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ v : Fin m, A u v = A u' v := by
  intro n m A C u u' _ hR hu hu' v
  rw [← hR u v, ← hR u' v]
  refine silent (n + m) C (fun w => w = u.val ∨ w = u'.val)
    (fun j hj w hw h => h.elim (fun e => hu.2 j hj.1 hj.2 (by rw [gd C hj.1]; exact e ▸ hw)) (fun e => hu'.2 j hj.1 hj.2 (by rw [gd C hj.1]; exact e ▸ hw)))
    (fun h => h.elim hu.1 hu'.1) _ _ (by simp [oneEach]) (by simp [oneEach]) fun w hw => ?_
  refine Bool.eq_iff_iff.2 ?_
  rw [oe, oe]; constructor <;> intro h <;> omega
