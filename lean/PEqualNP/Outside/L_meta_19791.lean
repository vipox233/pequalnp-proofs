import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 9, 12), (true, 10, 13), (true, 14, 15), (true, 8, 11), (true, 11, 13), (true, 20, 18), (false, 0, 21), (true, 16, 19), (false, 1, 23), (true, 8, 15), (true, 25, 17), (false, 2, 26), (true, 9, 10), (true, 28, 11), (true, 29, 14), (false, 3, 30), (true, 8, 12), (true, 32, 18), (false, 4, 33), (true, 16, 18), (false, 5, 35), (true, 16, 17), (false, 6, 37), (true, 17, 19), (false, 7, 39), (true, 22, 24), (true, 41, 27), (true, 42, 31), (true, 43, 34), (true, 44, 36), (true, 45, 38), (true, 46, 40)]

def circuit : Circuit := ⟨codes.map asGate, 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19791

open PEqualNP.Outside.L_meta_19791 in
theorem PEqualNP.Outside.L_meta_19791 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
