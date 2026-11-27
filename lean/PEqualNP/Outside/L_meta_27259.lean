import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27259

open PEqualNP.CircuitLowerBounds

def firstGate : Gate := ⟨GateOp.and, [0, 1]⟩
def secondGate : Gate := ⟨GateOp.or, [0, 3]⟩

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def bank (x : Fin 9 → Bool) := step (step (List.ofFn x) firstGate) secondGate

def matchVal (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def lo (i : Fin 9) : Nat := ![168, 96, 80, 133, 68, 66, 20, 12, 10] i
def hi (i : Fin 9) : Nat := ![169, 98, 84, 141, 84, 98, 84, 140, 266] i
def bits (n : Nat) (k : Fin 9) := n.testBit k.val

set_option maxRecDepth 4096 in
theorem witnesses : ∀ i : Fin 9,
    matchVal (bits (lo i)) ≠ matchVal (bits (hi i)) ∧
    ∀ k : Fin 11, k.val ≠ i.val →
      (bank (bits (lo i)))[k.val]? = (bank (bits (hi i)))[k.val]? := by decide

theorem bank_len (x : Fin 9 → Bool) : (bank x).length = 11 := by simp [bank, step]

theorem unchanged (gs : List Gate) (u v : List Bool) (i : Nat)
    (hlen : u.length = v.length)
    (heq : ∀ k, k ≠ i → u[k]? = v[k]?)
    (hmiss : i ∉ gs.flatMap Gate.inputs) :
    ∀ k, k ≠ i → (gs.foldl step u)[k]? = (gs.foldl step v)[k]? := by
  induction gs generalizing u v with
  | nil => exact heq
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hmiss
    have args : (g.inputs.map fun a => u.getD a false) =
        (g.inputs.map fun a => v.getD a false) := by
      apply List.map_congr_left
      intro a ha
      simpa only [List.getD_eq_getElem?_getD] using
        congrArg (fun z : Option Bool => z.getD false) (heq a (by rintro rfl; exact hmiss.1 ha))
    apply ih (step u g) (step v g) (by simp [step, hlen]) _ hmiss.2
    intro k hk
    by_cases h : k < u.length
    · simpa only [step, List.getElem?_append_left h, List.getElem?_append_left (hlen ▸ h)] using heq k hk
    · simp only [step, List.getElem?_append_right (Nat.le_of_not_gt h),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_gt h), hlen, args]

theorem raw (gs : List Gate) (out : Nat) (hout : 9 ≤ out)
    (correct : ∀ x, ((gs.foldl step (bank x)).getD out false) = matchVal x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hmiss
  obtain ⟨hdiff, hp⟩ := witnesses i
  apply hdiff
  rw [← correct, ← correct]
  simp only [List.getD_eq_getElem?_getD]
  apply congrArg (fun z : Option Bool => z.getD false)
  apply unchanged _ _ _ i.val (by simp [bank_len]) _ hmiss out (by omega)
  intro k hk
  by_cases h : k < 11
  · exact hp ⟨k, h⟩ hk
  · simp only [List.getElem?_eq_none (show (bank (bits (lo i))).length ≤ k by rw [bank_len]; omega),
        List.getElem?_eq_none (show (bank (bits (hi i))).length ≤ k by rw [bank_len]; omega)]

theorem slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h₁ := h g (by simp)
    have h₂ := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_27259

theorem PEqualNP.Outside.L_meta_27259 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩)) := by
  rintro ⟨C, hfan, hsize, hfun, hout, _, _, hlive, h₁, h₂⟩
  obtain ⟨gs, hgs⟩ : ∃ gs, C.gates = PEqualNP.Outside.L_meta_27259.firstGate :: PEqualNP.Outside.L_meta_27259.secondGate :: gs := by
    cases he : C.gates with
    | nil => simp [he] at h₁
    | cons a tail =>
      cases tail with
      | nil => simp [he] at h₂
      | cons b gs =>
        simp [he] at h₁ h₂
        exact ⟨gs, by rw [h₁, h₂]; rfl⟩
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size, hgs, List.length_cons] at hsize hout
  have correct : ∀ x, (gs.foldl PEqualNP.Outside.L_meta_27259.step (PEqualNP.Outside.L_meta_27259.bank x)).getD C.output false = PEqualNP.Outside.L_meta_27259.matchVal x := by
    intro x
    have hx := hfun x
    change (C.gates.foldl PEqualNP.Outside.L_meta_27259.step (List.ofFn x)).getD C.output false = PEqualNP.Outside.L_meta_27259.matchVal x at hx
    rw [hgs] at hx
    exact hx
  have cover : Finset.range (10 + gs.length) ⊆ (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset := by
    intro w hw
    apply List.mem_toFinset.mpr
    have hw' := Finset.mem_range.mp hw
    by_cases low : w < 9
    · exact PEqualNP.Outside.L_meta_27259.raw gs _ (by omega) correct ⟨w, low⟩
    · let j : Fin C.gates.length := ⟨w - 9, by simp [hgs]; omega⟩
      have hj : j.val + 1 < C.gates.length := by simp [j, hgs]; omega
      obtain ⟨k, _, hread⟩ := hlive j hj
      have heq : 9 + j.val = w := by dsimp [j]; omega
      rw [heq] at hread
      have hmem : C.gates.get k ∈ PEqualNP.Outside.L_meta_27259.firstGate :: PEqualNP.Outside.L_meta_27259.secondGate :: gs :=
        by rw [← hgs]; exact List.get_mem C.gates k
      rcases List.mem_cons.mp hmem with hf | ht
      · rw [hf] at hread
        simp [PEqualNP.Outside.L_meta_27259.firstGate] at hread
        omega
      rcases List.mem_cons.mp ht with hs | ht
      · rw [hs] at hread
        simp [PEqualNP.Outside.L_meta_27259.secondGate] at hread
        omega
      exact List.mem_flatMap_of_mem ht hread
  have cap := PEqualNP.Outside.L_meta_27259.slots gs (fun g hg => (hfan g (by rw [hgs]; simp [hg])).2)
  have lower := Finset.card_le_card cover
  rw [Finset.card_range] at lower
  have bound := List.toFinset_card_le (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs)
  omega
