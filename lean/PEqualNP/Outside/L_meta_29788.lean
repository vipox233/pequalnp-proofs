import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29788

open PEqualNP.CircuitLowerBounds

def step (wires : List Bool) (gate : Gate) : List Bool :=
  wires ++ [gate.op.eval (gate.inputs.map fun j => wires.getD j false)]

theorem head_preserved (gates : List Gate) (bit : Bool) (rest : List Bool) :
    (gates.foldl step (bit :: rest)).getD 0 false = bit := by
  induction gates generalizing rest with
  | nil => rfl
  | cons gate gates ih =>
    exact ih (rest ++ [gate.op.eval (gate.inputs.map fun j => (bit :: rest).getD j false)])

theorem same_tail (gates : List Gate)
    (hnoread : ∀ gate ∈ gates, 0 ∉ gate.inputs) (rest : List Bool) :
    ∃ result, gates.foldl step (false :: rest) = false :: result ∧
      gates.foldl step (true :: rest) = true :: result := by
  induction gates generalizing rest with
  | nil => exact ⟨rest, rfl, rfl⟩
  | cons gate gates ih =>
    have hreads :
        gate.inputs.map (fun j => (false :: rest).getD j false) =
          gate.inputs.map (fun j => (true :: rest).getD j false) := by
      apply List.map_congr_left
      intro j hj
      cases j with
      | zero => exact (hnoread gate (by simp) hj).elim
      | succ j => rfl
    let next := rest ++ [gate.op.eval (gate.inputs.map fun j => (false :: rest).getD j false)]
    obtain ⟨result, hlo, hhi⟩ := ih (fun g hg => hnoread g (by simp [hg])) next
    refine ⟨result, hlo, ?_⟩
    have hstep : step (true :: rest) gate = true :: next := by
      simp only [step, List.cons_append, next, hreads]
    rw [List.foldl_cons, hstep]
    exact hhi

def rest : List Bool := [true, false, false, true, false, false]

def input (bit : Bool) (j : Fin 7) : Bool := (bit :: rest).getD j.val false

theorem first_gate_true (gate : Gate) (hop : gate.op = .or)
    (hfour : 4 ∈ gate.inputs) (bit : Bool) :
    step (bit :: rest) gate = bit :: (rest ++ [true]) := by
  have hval : gate.op.eval (gate.inputs.map fun j => (bit :: rest).getD j false) = true := by
    rw [hop]
    apply List.any_eq_true.mpr
    exact ⟨true, List.mem_map.mpr ⟨4, hfour, rfl⟩, rfl⟩
  simp only [step, List.cons_append, hval]

end PEqualNP.Outside.L_meta_29788

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29788

theorem PEqualNP.Outside.L_meta_29788 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 0 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true)) := by
  rintro ⟨⟨gates, out⟩, i, _, hi, _, _, correct, _, hUnique, hOp, _, _, _, hReadFour, _, _, _⟩
  cases gates with
  | nil => exact Fin.elim0 i
  | cons gate gates =>
    have hfirst : i = (⟨0, Nat.zero_lt_succ _⟩ : Fin (gate :: gates).length) := Fin.ext hi
    have hOr : gate.op = .or := by simpa [hfirst] using hOp
    have hFour : 4 ∈ gate.inputs := by simpa [hfirst] using hReadFour
    have hTail : ∀ g ∈ gates, 0 ∉ g.inputs := by
      intro g hg hzero
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      let j' : Fin (gate :: gates).length := ⟨j + 1, Nat.succ_lt_succ hj⟩
      have hRead : 0 ∈ ((⟨gate :: gates, out⟩ : Circuit).gates.get j').inputs := hzero
      have heq : j + 1 = i.val := congrArg Fin.val (hUnique j' hRead)
      exact Nat.succ_ne_zero j (heq.trans hi)
    cases out with
    | zero =>
      have h := correct (fun j => decide (j = 0))
      change ((gate :: gates).foldl step [true, false, false, false, false, false, false]).getD 0 false =
        false at h
      rw [head_preserved] at h
      contradiction
    | succ out =>
      obtain ⟨result, hfalse, htrue⟩ := same_tail gates hTail (rest ++ [true])
      have hlo := correct (input false)
      have hhi := correct (input true)
      change ((gate :: gates).foldl step (false :: rest)).getD (out + 1) false = false at hlo
      change ((gate :: gates).foldl step (true :: rest)).getD (out + 1) false = true at hhi
      rw [List.foldl_cons, first_gate_true gate hOr hFour, hfalse] at hlo
      rw [List.foldl_cons, first_gate_true gate hOr hFour, htrue] at hhi
      change result.getD out false = false at hlo
      change result.getD out false = true at hhi
      rw [hlo] at hhi
      contradiction
