import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27315

open PEqualNP.CircuitLowerBounds

def gateA : Gate := ⟨.and, [0, 4]⟩
def gateB : Gate := ⟨.or, [0, 8]⟩

def advance (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def initial (x : Fin 9 → Bool) := advance (advance (List.ofFn x) gateA) gateB

def matching (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def onInput (i j : Fin 9) :=
  (([417, 98, 84, 140, 84, 98, 84, 140, 267] : List ℕ).getD i.val 0).testBit j.val

def offInput (i j : Fin 9) := onInput i j && decide (i ≠ j)

theorem distinguishes : ∀ i : Fin 9,
    matching (onInput i) ≠ matching (offInput i) ∧
    ∀ j : Fin 11, j.val ≠ i.val →
      (initial (onInput i)).getD j.val false = (initial (offInput i)).getD j.val false := by
  decide +kernel

theorem initial_length (x : Fin 9 → Bool) : (initial x).length = 11 := by
  simp [initial, advance]

theorem agree_fold (s : ℕ) (gs : List Gate) (w v : List Bool)
    (hlen : w.length = v.length)
    (agree : ∀ j, j ≠ s → w.getD j false = v.getD j false)
    (absent : s ∉ gs.flatMap Gate.inputs) :
    ∀ j, j ≠ s → (gs.foldl advance w).getD j false = (gs.foldl advance v).getD j false := by
  induction gs generalizing w v with
  | nil => exact agree
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at absent
    have same : (g.inputs.map fun j => w.getD j false) =
        (g.inputs.map fun j => v.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact agree j (fun e => absent.1 (e ▸ hj))
    apply ih (advance w g) (advance v g) (by simp [advance, hlen]) _ absent.2
    intro j hj
    unfold advance
    rw [same]
    by_cases h : j < w.length
    · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
      exact agree j hj
    · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hlen]

theorem slots_bound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem impossible (gs : List Gate) (out : ℕ)
    (fan : PEqualNP.MetaComplexity.FanInTwo ⟨gateA :: gateB :: gs, out⟩)
    (bound : (gateA :: gateB :: gs).length ≤ 11)
    (correct : ∀ x : Fin 9 → Bool,
      (Circuit.mk (gateA :: gateB :: gs) out).eval (List.ofFn x) = matching x)
    (last : out + 1 = 9 + (gateA :: gateB :: gs).length)
    (live : ∀ j : Fin (gateA :: gateB :: gs).length, j.val + 1 < (gateA :: gateB :: gs).length →
      ∃ k : Fin (gateA :: gateB :: gs).length, j.val < k.val ∧
      9 + j.val ∈ ((gateA :: gateB :: gs).get k).inputs) : False := by
  simp only [List.length_cons] at bound last
  have originals (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
    by_contra absent
    obtain ⟨different, agree⟩ := distinguishes i
    apply different
    rw [← correct, ← correct]
    change (gs.foldl advance (initial (onInput i))).getD out false =
      (gs.foldl advance (initial (offInput i))).getD out false
    apply agree_fold i.val gs _ _ (by simp [initial_length]) _ absent out (by omega)
    intro j hj
    by_cases h : j < 11
    · exact agree ⟨j, h⟩ hj
    · rw [List.getD_eq_default _ _ (by simp [initial_length]; omega),
          List.getD_eq_default _ _ (by simp [initial_length]; omega)]
  have subset : Finset.range (10 + gs.length) ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro t ht
    rw [List.mem_toFinset]
    have upper := Finset.mem_range.mp ht
    by_cases small : t < 9
    · exact originals ⟨t, small⟩
    · let j : Fin (gateA :: gateB :: gs).length := ⟨t-9, by simp; omega⟩
      obtain ⟨k, _, hk⟩ := live j (by dsimp [j]; simp; omega)
      have val : 9 + j.val = t := by dsimp [j]; omega
      rw [val] at hk
      have mem : t ∈ (gateA :: gateB :: gs).flatMap Gate.inputs :=
        List.mem_flatMap.mpr ⟨_, List.get_mem _ _, hk⟩
      change t ∈ 0 :: 4 :: 0 :: 8 :: gs.flatMap Gate.inputs at mem
      simp only [List.mem_cons] at mem
      rcases mem with h | h | h | h | h <;> omega
  have lo := Finset.card_le_card subset
  rw [Finset.card_range] at lo
  have len := List.toFinset_card_le (gs.flatMap Gate.inputs)
  have hi := slots_bound gs (fun g hg => (fan g (by simp [hg])).2)
  omega

end PEqualNP.Outside.L_meta_27315

theorem PEqualNP.Outside.L_meta_27315 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩)) := by
  rintro ⟨⟨gates, out⟩, fan, bound, correct, last, _, _, live, hA, hB⟩
  cases gates with
  | nil => simp at hA
  | cons a rest =>
    cases rest with
    | nil => simp at hB
    | cons b gs =>
      change some a = some PEqualNP.Outside.L_meta_27315.gateA at hA
      change some b = some PEqualNP.Outside.L_meta_27315.gateB at hB
      cases Option.some.inj hA
      cases Option.some.inj hB
      exact PEqualNP.Outside.L_meta_27315.impossible gs out fan bound correct last live
