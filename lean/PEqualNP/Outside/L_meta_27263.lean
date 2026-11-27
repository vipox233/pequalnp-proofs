import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27263

open PEqualNP.CircuitLowerBounds

private def target (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

private def refs (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

private def fbStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fbFold (gs : List Gate) (i : ℕ) (hi : i ∉ refs gs)
    (a b : List Bool) (hl : a.length = b.length)
    (h : ∀ j : ℕ, j ≠ i → a.getD j false = b.getD j false) :
    ∀ j : ℕ, j ≠ i → (gs.foldl fbStep a).getD j false = (gs.foldl fbStep b).getD j false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hn : i ∉ g.inputs ∧ i ∉ refs gs := by
      simpa [refs] using hi
    have hm : g.inputs.map (fun j => a.getD j false) =
        g.inputs.map (fun j => b.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact h j (fun he => hn.1 (he ▸ hj))
    simp only [List.foldl_cons]
    apply ih hn.2 (fbStep a g) (fbStep b g)
    · simp [fbStep, hl]
    · intro j hj
      by_cases hk : j < a.length
      · simpa only [fbStep, List.getD_append _ _ _ _ hk,
          List.getD_append _ _ _ _ (hl ▸ hk)] using h j hj
      · rw [fbStep, fbStep, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hk),
          List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hk), hm, hl]

private def fbPrefix (x : Fin 9 → Bool) : List Bool :=
  fbStep (fbStep (List.ofFn x) ⟨.and, [0, 1]⟩) ⟨.or, [0, 5]⟩

private def fbRow (i : Fin 9) (flip : Bool) (j : Fin 9) : Bool :=
  (([160, 264, 136, 132, 68, 129, 20, 12, 10] : List ℕ).getD i.val 0).testBit j.val ||
    (flip && (j == i))

private theorem fbRows (i : Fin 9) :
    target (fbRow i false) ≠ target (fbRow i true) ∧
      ∀ j : Fin 11, j.val ≠ i.val →
        (fbPrefix (fbRow i false)).getD j.val false = (fbPrefix (fbRow i true)).getD j.val false := by
  fin_cases i <;> decide +kernel

private theorem forceReads (C : Circuit)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x)
    (ho : C.output + 1 = 9 + C.size)
    (gs : List Gate)
    (hg : C.gates = ⟨.and, [0, 1]⟩ :: ⟨.or, [0, 5]⟩ :: gs) :
    ∀ i : ℕ, i < 9 → i ∈ refs gs := by
  intro i hi
  by_contra hn
  let k : Fin 9 := ⟨i, hi⟩
  have hlen (x : Fin 9 → Bool) : (fbPrefix x).length = 11 := by simp [fbPrefix, fbStep]
  have hrows := fbRows k
  have hagree : ∀ j : ℕ, j ≠ i →
      (fbPrefix (fbRow k false)).getD j false = (fbPrefix (fbRow k true)).getD j false := by
    intro j hj
    by_cases hj' : j < 11
    · exact hrows.2 ⟨j, hj'⟩ hj
    · have ha : (fbPrefix (fbRow k false)).length ≤ j := by rw [hlen]; omega
      have hb : (fbPrefix (fbRow k true)).length ≤ j := by rw [hlen]; omega
      simp [ha, hb]
  have hout : C.output ≠ i := by
    simp [Circuit.size, hg] at ho
    omega
  have hEq := fbFold gs i hn _ _ (by rw [hlen, hlen]) hagree C.output hout
  have heval (x : Fin 9 → Bool) : C.eval (List.ofFn x) =
      (gs.foldl fbStep (fbPrefix x)).getD C.output false := by
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl_cons]
    rfl
  rw [← heval, ← heval, he, he] at hEq
  exact hrows.1 hEq

private theorem refLength (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have hs := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

-- The suffix must read all nine input wires and every nonoutput gate wire.
private theorem refCount (C : Circuit) (gs : List Gate)
    (hgs : C.gates = ⟨.and, [0, 1]⟩ :: ⟨.or, [0, 5]⟩ :: gs)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsmall : C.size ≤ 11)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hinputs : ∀ i < 9, i ∈ gs.flatMap Gate.inputs) : False := by
  have hsub : List.range (8 + C.gates.length) ⊆ gs.flatMap Gate.inputs := by
    intro i hi
    have hi' := List.mem_range.mp hi
    by_cases h : i < 9
    · exact hinputs i h
    · let j : Fin C.gates.length := ⟨i - 9, by omega⟩
      have jlt : j.val + 1 < C.gates.length := by
        dsimp [j]
        omega
      obtain ⟨k, _, hk⟩ := hlive j jlt
      have eq : 9 + j.val = i := by
        dsimp [j]
        omega
      rw [eq] at hk
      let g := C.gates.get k
      have hm : g ∈ C.gates := List.get_mem C.gates k
      change i ∈ g.inputs at hk
      rw [hgs] at hm
      simp only [List.mem_cons] at hm
      rcases hm with h₀ | h₁ | hg
      · rw [h₀] at hk
        simp at hk
        omega
      · rw [h₁] at hk
        simp at hk
        omega
      · exact List.mem_flatMap_of_mem hg hk
  have hlo := List.nodup_range.length_le_of_subset hsub
  rw [List.length_range] at hlo
  have hhi := refLength gs (fun g hg => (hfan g (by simp [hgs, hg])).2)
  have hlen : C.gates.length = gs.length + 2 := by simp [hgs]
  change C.gates.length ≤ 11 at hsmall
  omega

end PEqualNP.Outside.L_meta_27263

theorem PEqualNP.Outside.L_meta_27263 :
¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩) := by
  rintro ⟨C, hfan, hsmall, heval, hout, _, _, hlive, hfirst, hsecond⟩
  cases hgs : C.gates with
  | nil => simp [hgs] at hfirst
  | cons a rest =>
    cases rest with
    | nil => simp [hgs] at hsecond
    | cons b gs =>
      have ha : a = (⟨.and, [0, 1]⟩ : PEqualNP.CircuitLowerBounds.Gate) := by
        simpa [hgs] using hfirst
      have hb : b = (⟨.or, [0, 5]⟩ : PEqualNP.CircuitLowerBounds.Gate) := by
        simpa [hgs] using hsecond
      rw [ha, hb] at hgs
      exact PEqualNP.Outside.L_meta_27263.refCount C gs hgs hfan hsmall hlive
        (PEqualNP.Outside.L_meta_27263.forceReads C heval hout gs hgs)
