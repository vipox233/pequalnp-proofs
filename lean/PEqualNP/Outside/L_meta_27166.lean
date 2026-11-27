import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_27166

def firstGate : Gate := ⟨.and, [0, 4]⟩

def secondGate : Gate := ⟨.and, [0, 2]⟩

def step (bank : List Bool) (gate : Gate) : List Bool :=
  bank ++ [gate.op.eval (gate.inputs.map fun addr => bank.getD addr false)]

def start (input : Fin 9 → Bool) : List Bool :=
  step (step (List.ofFn input) firstGate) secondGate

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def matching (edge : Fin 9) : Fin 9 → Bool :=
  let masks : List Nat := [161, 266, 84, 266, 84, 161, 84, 161, 266]
  fun coord => (masks.getD edge.val 0).testBit coord.val

def erased (edge : Fin 9) (coord : Fin 9) : Bool :=
  coord != edge && matching edge coord

lemma sensitive : ∀ edge : Fin 9,
    target (matching edge) ≠ target (erased edge) ∧
    ∀ addr : Fin 11, addr.val ≠ edge.val →
      (start (matching edge)).getD addr.val false = (start (erased edge)).getD addr.val false := by
  decide +kernel

lemma fold_agrees (gates : List Gate) (edge : Nat) (left right : List Bool)
    (hlen : left.length = right.length)
    (agree : ∀ addr, addr ≠ edge → left.getD addr false = right.getD addr false)
    (absent : edge ∉ gates.flatMap Gate.inputs) :
    ∀ addr, addr ≠ edge → (gates.foldl step left).getD addr false =
      (gates.foldl step right).getD addr false := by
  induction gates generalizing left right with
  | nil => exact agree
  | cons gate rest ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at absent
    have same : gate.inputs.map (fun addr => left.getD addr false) =
        gate.inputs.map (fun addr => right.getD addr false) := by
      apply List.map_congr_left
      intro addr hmem
      exact agree addr (fun heq => absent.1 (heq ▸ hmem))
    apply ih (step left gate) (step right gate) (by simp [step, hlen]) _ absent.2
    intro addr hne
    unfold step
    rw [same]
    by_cases hlt : addr < left.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
      exact agree addr hne
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]

lemma raw_used (rest : List Gate) (out : Nat) (hout : 9 ≤ out)
    (correct : ∀ x, (rest.foldl step (start x)).getD out false = target x) :
    ∀ edge : Fin 9, edge.val ∈ rest.flatMap Gate.inputs := by
  intro edge
  by_contra absent
  have lengths (x : Fin 9 → Bool) : (start x).length = 11 := by simp [start, step]
  obtain ⟨diff, equal⟩ := sensitive edge
  apply diff
  rw [← correct, ← correct]
  apply fold_agrees rest edge.val _ _ (by simp [lengths]) _ absent out (by omega)
  intro addr hne
  by_cases hlt : addr < 11
  · exact equal ⟨addr, hlt⟩ hne
  · rw [List.getD_eq_default _ _ (by simpa [lengths] using Nat.le_of_not_gt hlt),
        List.getD_eq_default _ _ (by simpa [lengths] using Nat.le_of_not_gt hlt)]

lemma slots (rest : List Gate) (h : ∀ gate ∈ rest, gate.inputs.length ≤ 2) :
    (rest.flatMap Gate.inputs).length ≤ 2 * rest.length := by
  induction rest with
  | nil => simp
  | cons gate rest ih =>
    have headBound := h gate (by simp)
    have tailBound := ih (fun member hmem => h member (by simp [hmem]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

lemma gates_split (gates : List Gate) (hfirst : gates.head? = some firstGate)
    (hsecond : gates.tail.head? = some secondGate) :
    ∃ rest, gates = firstGate :: secondGate :: rest := by
  cases gates with
  | nil => simp at hfirst
  | cons head tail =>
    cases tail with
    | nil => simp at hsecond
    | cons next rest =>
      exact ⟨rest, by simp_all⟩

end PEqualNP.Outside.L_meta_27166

open PEqualNP.Outside.L_meta_27166

theorem PEqualNP.Outside.L_meta_27166 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩)) := by
  rintro ⟨⟨gates, out⟩, fan, size, correct, output, _, _, live, hfirst, hsecond⟩
  obtain ⟨rest, rfl⟩ := gates_split gates hfirst hsecond
  change (firstGate :: secondGate :: rest).length ≤ 11 at size
  change out + 1 = 9 + (firstGate :: secondGate :: rest).length at output
  simp only [List.length_cons] at size output
  have raw := raw_used rest out (by omega) correct
  have used (idx : Nat) (hlt : idx < rest.length + 1) : 9 + idx ∈ rest.flatMap Gate.inputs := by
    obtain ⟨⟨child, bound⟩, later, mem⟩ := live ⟨idx, by simp; omega⟩ (by simp; omega)
    change idx < child at later
    cases child with
    | zero => omega
    | succ child =>
      cases child with
      | zero =>
        change 9 + idx ∈ ([0, 2] : List Nat) at mem
        simp at mem
        omega
      | succ child =>
        have bound' : child < rest.length := by simpa using bound
        exact List.mem_flatMap_of_mem (List.getElem_mem (l := rest) bound') mem
  have incl : Finset.range (10 + rest.length) ⊆ (rest.flatMap Gate.inputs).toFinset := by
    intro wire hwire
    apply List.mem_toFinset.mpr
    have limit := Finset.mem_range.mp hwire
    by_cases small : wire < 9
    · exact raw ⟨wire, small⟩
    · have counted := used (wire - 9) (by omega)
      rwa [show 9 + (wire - 9) = wire by omega] at counted
  have lower := Finset.card_le_card incl
  rw [Finset.card_range] at lower
  have bounded := (rest.flatMap Gate.inputs).toFinset_card_le
  have upper := slots rest (fun gate hmem => (fan gate (by simp [hmem])).2)
  omega
