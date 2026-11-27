import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22673

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 2, 8), (true, 3, 6), (true, 1, 4), (true, 7, 11), (true, 9, 11), (true, 2, 12), (true, 0, 5), (true, 0, 12), (true, 5, 10), (false, 13, 15), (false, 14, 16), (false, 17, 18), (true, 19, 20), (true, 22, 21)]

def circuit : Circuit := ⟨codes.map asGate, 23⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22673

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22673 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841654 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22673.circuit, PEqualNP.Outside.L_meta_22673.mono, by decide, by decide +kernel⟩
