import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22354

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 7, 8), (true, 3, 6), (true, 1, 4), (true, 2, 5), (true, 12, 13), (true, 8, 13), (true, 7, 12), (true, 9, 10), (false, 0, 17), (false, 11, 14), (false, 15, 16), (true, 18, 19), (true, 21, 20)]

def circuit : Circuit := ⟨codes.map asGate, 22⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_22354

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_22354 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841144 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22354.circuit, PEqualNP.Outside.L_meta_22354.mono, by decide, by decide +kernel⟩
