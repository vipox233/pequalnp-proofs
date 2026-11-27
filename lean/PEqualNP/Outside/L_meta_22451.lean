import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 1, 7), (true, 8, 9), (true, 2, 11), (true, 0, 4), (true, 5, 13), (true, 3, 10), (true, 0, 3), (true, 10, 14), (false, 6, 16), (false, 12, 17), (false, 14, 15), (true, 18, 19), (true, 21, 20)]

def circuit : Circuit := ⟨codes.map asGate, 22⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22451

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22451 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883388 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22451.circuit, PEqualNP.Outside.L_meta_22451.mono, by decide, by decide +kernel⟩
