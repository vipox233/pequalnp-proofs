import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22754

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 5, 6), (true, 0, 7), (true, 7, 9), (true, 6, 12), (true, 2, 10), (true, 12, 14), (true, 0, 1), (true, 4, 14), (true, 4, 8), (true, 16, 18), (true, 3, 11), (false, 15, 19), (false, 17, 20), (true, 21, 22)]

def circuit : Circuit := ⟨codes.map asGate, 23⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22754

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22754 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940399 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22754.circuit, PEqualNP.Outside.L_meta_22754.mono, by decide, by decide +kernel⟩
