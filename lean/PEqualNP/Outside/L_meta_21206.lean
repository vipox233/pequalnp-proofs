import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21206

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(false, 3, 5), (true, 1, 7), (true, 2, 8), (true, 0, 6), (true, 4, 9), (false, 10, 12), (true, 10, 12), (false, 11, 15), (true, 14, 16), (true, 13, 17)]

def circuit : Circuit := ⟨codes.map asGate, 18⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_21206

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_21206 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112313 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21206.circuit, PEqualNP.Outside.L_meta_21206.mono, by decide, by decide +kernel⟩
