import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22373

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 0, 4), (true, 6, 7), (true, 2, 8), (true, 3, 9), (true, 5, 12), (true, 10, 11), (true, 11, 14), (true, 5, 10), (false, 1, 16), (false, 13, 17), (false, 14, 15), (true, 18, 19), (true, 21, 20)]

def circuit : Circuit := ⟨codes.map asGate, 22⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22373

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22373 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841650 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22373.circuit, PEqualNP.Outside.L_meta_22373.mono, by decide, by decide +kernel⟩
