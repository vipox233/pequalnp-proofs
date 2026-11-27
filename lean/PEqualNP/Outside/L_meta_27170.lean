import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27170

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def first : Gate := ⟨.and, [0, 4]⟩
private def second : Gate := ⟨.and, [0, 8]⟩

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

-- Three disjoint perfect matchings keep both leading gates false.
private def on (i : Fin 9) (j : Fin 9) : Bool :=
  if i == 0 || i == 5 || i == 7 then j == 0 || j == 5 || j == 7
  else if i == 2 || i == 4 || i == 6 then j == 2 || j == 4 || j == 6
  else j == 1 || j == 3 || j == 8

private def off (i : Fin 9) (j : Fin 9) : Bool := on i j && (j != i)

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem onMatch : ∀ i : Fin 9, matching (on i) = true := by decide +kernel
private theorem offMatch : ∀ i : Fin 9, matching (off i) = false := by decide +kernel

private theorem preOn : ∀ i : Fin 9,
    [first, second].foldl step (List.ofFn (on i)) = List.ofFn (on i) ++ [false, false] := by
  decide +kernel

private theorem preOff : ∀ i : Fin 9,
    [first, second].foldl step (List.ofFn (off i)) = List.ofFn (off i) ++ [false, false] := by
  decide +kernel

private theorem preAgree : ∀ (i : Fin 9) (j : Fin 11), j.val ≠ i.val →
    (List.ofFn (on i) ++ [false, false]).getD j.val false =
      (List.ofFn (off i) ++ [false, false]).getD j.val false := by
  decide +kernel

private theorem foldAgree (p : ℕ) (gs : List Gate) (a b : List Bool)
    (length : a.length = b.length) (agree : ∀ w, w ≠ p → a.getD w false = b.getD w false)
    (miss : p ∉ gs.flatMap Gate.inputs) :
    ∀ w, w ≠ p → (gs.foldl step a).getD w false = (gs.foldl step b).getD w false := by
  induction gs generalizing a b with
  | nil => exact agree
  | cons g tail ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at miss
    have values : (g.inputs.map fun j => a.getD j false) =
        (g.inputs.map fun j => b.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact agree j (fun h => miss.1 (h ▸ hj))
    change ∀ w, w ≠ p → (tail.foldl step (step a g)).getD w false =
      (tail.foldl step (step b g)).getD w false
    apply ih (step a g) (step b g) (by simp [step, length]) _ miss.2
    intro w hw
    by_cases small : w < b.length
    · simpa only [step, List.getD_append _ _ _ _ small,
        List.getD_append _ _ _ _ (by omega : w < a.length)] using agree w hw
    · simp only [step, List.getD_append_right _ _ _ _ (by omega : a.length ≤ w),
        List.getD_append_right _ _ _ _ (by omega : b.length ≤ w), length, values]

private theorem inputBound (gs : List Gate) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g tail ih =>
    have hg := fan g (by simp)
    have ht := ih (fun h hh => fan h (by simp [hh]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem lower (C : Circuit)
    (fan : FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x)
    (last : C.output + 1 = 9 + C.size)
    (live : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (head : C.gates.head? = some first) (next : C.gates.tail.head? = some second) :
    12 ≤ C.size := by
  obtain ⟨tail, layout⟩ : ∃ tail : List Gate, C.gates = first :: second :: tail := by
    cases e : C.gates with
    | nil => simp [e] at head
    | cons a t =>
      cases t with
      | nil => simp [e] at next
      | cons b t =>
        simp [e] at head next
        exact ⟨t, by simp [head, next]⟩
  have size : C.size = tail.length + 2 := by simp [Circuit.size, layout]
  let reads := tail.flatMap Gate.inputs
  have rawRead (i : Fin 9) : i.val ∈ reads := by
    by_contra missing
    let a := List.ofFn (on i) ++ [false, false]
    let b := List.ofFn (off i) ++ [false, false]
    have lengthA : a.length = 11 := by simp [a]
    have lengthB : b.length = 11 := by simp [b]
    have agree (j : ℕ) (hne : j ≠ i.val) : a.getD j false = b.getD j false := by
      by_cases small : j < 11
      · exact preAgree i ⟨j, small⟩ hne
      · simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega : a.length ≤ j),
          List.getElem?_eq_none (by omega : b.length ≤ j)]
    have inputLt := i.isLt
    have outNe : C.output ≠ i.val := by omega
    have equal := foldAgree i.val tail a b (by omega) agree missing C.output outNe
    have evalPrefix (x : Fin 9 → Bool) : C.eval (List.ofFn x) =
        (tail.foldl step ([first, second].foldl step (List.ofFn x))).getD C.output false := by
      rw [Circuit.eval, Circuit.wires, layout]
      rfl
    have hon := computes (on i)
    have hoff := computes (off i)
    rw [evalPrefix, preOn, onMatch] at hon
    rw [evalPrefix, preOff, offMatch] at hoff
    exact (by decide : (true : Bool) ≠ false) (hon.symm.trans (equal.trans hoff))
  have gateRead (j : ℕ) (hj : j + 1 < C.gates.length) : 9 + j ∈ reads := by
    obtain ⟨k, _, hr⟩ := live ⟨j, by omega⟩ hj
    let g := C.gates.get k
    change 9 + j ∈ g.inputs at hr
    have member : g ∈ C.gates := List.get_mem _ _
    rw [layout] at member
    simp only [List.mem_cons] at member
    rcases member with one | two | inTail
    · rw [one] at hr
      simp [first] at hr
      omega
    · rw [two] at hr
      simp [second] at hr
      omega
    · exact List.mem_flatMap.mpr ⟨_, inTail, hr⟩
  have covers : Finset.range C.output ⊆ reads.toFinset := by
    intro j hj
    apply List.mem_toFinset.mpr
    have bound := Finset.mem_range.mp hj
    by_cases raw : j < 9
    · exact rawRead ⟨j, raw⟩
    · let k := j - 9
      have len : C.gates.length = C.size := rfl
      have same : j = 9 + k := by omega
      rw [same]
      exact gateRead k (by omega)
  have card : C.output ≤ reads.toFinset.card := by
    simpa only [Finset.card_range] using Finset.card_le_card covers
  have readLen := List.toFinset_card_le reads
  have tailFan (g : Gate) (hg : g ∈ tail) : g.inputs.length ≤ 2 :=
    (fan g (by rw [layout]; simp [hg])).2
  have total : reads.length ≤ 2 * tail.length := inputBound tail tailFan
  omega

end PEqualNP.Outside.L_meta_27170


theorem PEqualNP.Outside.L_meta_27170 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩) := by
  rintro ⟨C, fan, small, computes, last, _, _, live, head, next⟩
  have bound := PEqualNP.Outside.L_meta_27170.lower C fan computes last live head next
  omega
