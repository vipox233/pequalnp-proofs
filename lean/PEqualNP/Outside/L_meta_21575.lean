import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21575_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C_ : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩], 10⟩

def isOk (g : Gate) : Bool :=
  (match g.op with | .and => true | .or => true | .not => true | _ => false) && (g.inputs.length == 1 || g.inputs.length == 2)

theorem wf_ : FanInTwo C_ := by
  intro g hg
  have h1 := List.all_eq_true.1 (by decide : C_.gates.all isOk = true) g hg
  simp only [isOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1
  refine ⟨?_, by omega⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_21575_aux

open PEqualNP.Outside.L_meta_21575_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21575 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17052255 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨C_, wf_, by decide, by decide +kernel⟩
