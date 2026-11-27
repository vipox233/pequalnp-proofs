import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25266

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [0, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [10, 13]⟩], 14⟩

theorem basis_ok : FanInTwo witness := by
  simp [FanInTwo, witness]

end PEqualNP.Outside.L_meta_25266

theorem PEqualNP.Outside.L_meta_25266 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25266.witness, PEqualNP.Outside.L_meta_25266.basis_ok, by decide, by decide +kernel⟩
