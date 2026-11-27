import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_824

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private def Allowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

private def Legal (n : ℕ) (C : Circuit) : Prop :=
  ReadsBack n C ∧ ∀ g ∈ C.gates, Allowed g

private def Paid (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private noncomputable def cost (C : Circuit) : ℕ :=
  C.gates.countP (fun g => @decide (Paid g) (Classical.propDecidable _))

private def replace (pre post : List Gate) (o : ℕ) (g : Gate) : Circuit :=
  ⟨pre ++ [g] ++ post, o⟩

private def sign (b : Bool) : ℤ := if b then -1 else 1

private def replacementGate (isOr : Bool) (i j : ℕ) (d : Fin 4) : Gate :=
  let yes : Gate := ⟨.and, []⟩
  let same : Gate := ⟨.mod 2, [i, j]⟩
  ![⟨.and, [i]⟩, ⟨.and, [j]⟩, if isOr then yes else same,
    if isOr then same else yes] d

private theorem replacementGate_valid (b : Bool) (i j : ℕ) (d : Fin 4) :
    Allowed (replacementGate b i j d) ∧ ¬Paid (replacementGate b i j d) ∧
      ∀ a ∈ (replacementGate b i j d).inputs, a ∈ [i, j] := by
  cases b <;> fin_cases d <;> simp [replacementGate, Allowed, Paid]

private theorem four_terms (v : ℕ → Bool) (F : Bool → ℤ) (i j : ℕ) (b : Bool) :
    let E := fun g : Gate => F (g.op.eval (g.inputs.map v))
    2 * E ⟨if b then .or else .and, [i,j]⟩ =
      E (replacementGate b i j 0) + E (replacementGate b i j 1) +
      E (replacementGate b i j 2) - E (replacementGate b i j 3) := by
  cases b <;> cases hi : v i <;> cases hj : v j <;>
    simp [replacementGate, GateOp.eval, hi, hj] <;> ring

private def stepVal (pre : List Gate) (bits : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => ((Circuit.mk pre 0).wires bits).getD i false))

private def suffixOut (pre post : List Gate) (o : ℕ) (bits : List Bool) (b : Bool) : Bool :=
  (Circuit.mk post o).eval ((Circuit.mk pre 0).wires bits ++ [b])

private theorem replace_eval (pre post : List Gate) (o : ℕ) (g : Gate) (bits : List Bool) :
    (replace pre post o g).eval bits = suffixOut pre post o bits (stepVal pre bits g) := by
  simp only [replace, suffixOut, stepVal, Circuit.eval, Circuit.wires, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

private theorem gateAt_replace_center (pre post : List Gate) (o : ℕ) (g : Gate) :
    gateAt (replace pre post o g) pre.length = g := by
  have h : pre.length < (pre ++ [g]).length := by simp
  change ((pre ++ [g]) ++ post).getD pre.length _ = g
  rw [List.getD_append _ _ _ _ h, List.getD_append_right _ _ _ _ le_rfl]
  simp

private theorem gateAt_replace_else (pre post : List Gate) (o j : ℕ) (g g' : Gate)
    (h : j ≠ pre.length) :
    gateAt (replace pre post o g') j = gateAt (replace pre post o g) j := by
  change ((pre ++ [g']) ++ post).getD j _ = ((pre ++ [g]) ++ post).getD j _
  by_cases hj : j < pre.length
  · have hg : j < (pre ++ [g]).length := by
      simp
      omega
    have hg' : j < (pre ++ [g']).length := by simpa using hg
    simp only [List.getD_append _ _ _ _ hg', List.getD_append _ _ _ _ hg,
      List.getD_append _ _ _ _ hj]
  · have hg : (pre ++ [g]).length ≤ j := by
      simp
      omega
    have hg' : (pre ++ [g']).length ≤ j := by simpa using hg
    simp only [List.getD_append_right _ _ _ _ hg', List.getD_append_right _ _ _ _ hg,
      List.length_append, List.length_singleton]

private theorem replace_legal (n : ℕ) (pre post : List Gate) (o : ℕ) (g g' : Gate)
    (h : Legal n (replace pre post o g)) (h' : Allowed g') (hs : g'.inputs ⊆ g.inputs) :
    Legal n (replace pre post o g') := by
  obtain ⟨back, allowed⟩ := h
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    have hj' : j < (replace pre post o g).gates.length := by
      simpa [replace] using hj
    apply back j hj' i
    by_cases hc : j = pre.length
    · subst j
      rw [gateAt_replace_center] at hi ⊢
      exact hs hi
    · rwa [gateAt_replace_else pre post o j g g' hc] at hi
  · intro t ht
    change t ∈ (pre ++ [g']) ++ post at ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact allowed t (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ht))))
      · simpa using (List.mem_singleton.mp ht).symm ▸ h'
    · exact allowed t (List.mem_append.mpr (Or.inr ht))

private theorem selectPaid (C : Circuit) (hcost : 0 < cost C) :
    ∃ pre g post, C = replace pre post C.output g ∧ Paid g := by
  classical
  unfold cost at hcost
  obtain ⟨g, hg, hp⟩ := List.countP_pos_iff.mp hcost
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hg
  refine ⟨pre, g, post, ?_, of_decide_eq_true hp⟩
  cases C with
  | mk gates output =>
    apply congrArg (fun gates' => Circuit.mk gates' output)
    simpa [List.append_assoc] using hs

private theorem replaceCostAddOne (pre post : List Gate) (o : ℕ) (g h : Gate)
    (hg : Paid g) (hh : ¬ Paid h) :
    cost (replace pre post o h) + 1 = cost (replace pre post o g) := by
  classical
  simp [cost, replace, List.countP_append, hg, hh]
  omega

private theorem replaceCostLt (pre post : List Gate) (o : ℕ) (g h : Gate)
    (hg : Paid g) (hh : ¬ Paid h) :
    cost (replace pre post o h) < cost (replace pre post o g) :=
  Nat.lt_of_succ_le (replaceCostAddOne pre post o g h hg hh).le

end PEqualNP.Outside.L_lib_824

open PEqualNP.Outside.L_lib_824 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_lib_824 : (∀ n : ℕ,
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let sig := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ C : Circ, legal n C → 0 < cost C →
    ∃ D : Fin 4 → Circ,
      (∀ i, legal n (D i) ∧ cost (D i) < cost C) ∧
      ∀ x : Fin n → Bool,
        let bits := List.ofFn x
        2*sig (C.eval bits) = sig ((D 0).eval bits) + sig ((D 1).eval bits) +
          sig ((D 2).eval bits) - sig ((D 3).eval bits)) := by
  intro n
  dsimp only
  intro C hlegal hcost
  change Legal n C at hlegal
  change 0 < cost C at hcost
  obtain ⟨pre, g, post, hC, hg⟩ := selectPaid C hcost
  have hform : ∃ (b : Bool) (i j : ℕ), g = ⟨if b then .or else .and, [i,j]⟩ := by
    obtain ⟨op, inputs⟩ := g
    obtain ⟨i, j, rfl⟩ := List.length_eq_two.mp hg.2
    rcases hg.1 with h | h
    · exact ⟨false, i, j, by change op = .and at h; simp [h]⟩
    · exact ⟨true, i, j, by change op = .or at h; simp [h]⟩
  obtain ⟨b, i, j, rfl⟩ := hform
  let o := C.output
  change C = replace pre post o ⟨if b then .or else .and, [i,j]⟩ at hC
  refine ⟨fun d => replace pre post o (replacementGate b i j d), ?_, ?_⟩
  · intro d
    obtain ⟨ha, hn, hsub⟩ := replacementGate_valid b i j d
    change Legal n (replace pre post o (replacementGate b i j d)) ∧
      cost (replace pre post o (replacementGate b i j d)) < cost C
    exact ⟨replace_legal n pre post o ⟨if b then .or else .and, [i,j]⟩ _
      (hC ▸ hlegal) ha hsub,
      hC.symm ▸ replaceCostLt pre post o _ _ hg hn⟩
  · intro x
    let bits := List.ofFn x
    change 2 * sign (C.eval bits) =
      sign ((replace pre post o (replacementGate b i j 0)).eval bits) +
      sign ((replace pre post o (replacementGate b i j 1)).eval bits) +
      sign ((replace pre post o (replacementGate b i j 2)).eval bits) -
      sign ((replace pre post o (replacementGate b i j 3)).eval bits)
    rw [hC]
    simp only [replace_eval]
    exact four_terms (fun a => ((Circuit.mk pre 0).wires bits).getD a false)
      (fun z => sign (suffixOut pre post o bits z)) i j b
