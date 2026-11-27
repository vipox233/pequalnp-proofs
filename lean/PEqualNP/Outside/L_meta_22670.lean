import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 1, 4), (true, 0, 7), (true, 0, 5), (true, 6, 11), (true, 3, 13), (true, 1, 9), (true, 5, 10), (true, 10, 13), (true, 2, 8), (false, 12, 15), (false, 14, 16), (false, 17, 18), (true, 19, 20), (true, 22, 21)]

def circuit : Circuit := ⟨codes.map asGate, 23⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22670

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22670 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841651 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22670.circuit, PEqualNP.Outside.L_meta_22670.mono, by decide, by decide +kernel⟩
