import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20144

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate list obtained by factoring a cover of the matrix by rectangles.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 0, 1), (true, 4, 7), (true, 3, 5), (true, 6, 18), (true, 6, 16), (true, 17, 18), (true, 19, 2), (true, 17, 16), (true, 19, 0), (true, 4, 20), (true, 2, 3), (true, 26, 17), (true, 2, 20), (true, 7, 5), (true, 29, 2), (true, 30, 1), (false, 21, 8), (false, 22, 9), (false, 23, 10), (false, 24, 11), (false, 25, 12), (false, 27, 13), (false, 28, 14), (false, 31, 15), (true, 32, 33), (true, 40, 34), (true, 41, 35), (true, 42, 36), (true, 43, 37), (true, 44, 38), (true, 45, 39)]
def circuit : Circuit := ⟨codes.map asGate, 46⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20144

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_20144 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  exact ⟨PEqualNP.Outside.L_meta_20144.circuit, PEqualNP.Outside.L_meta_20144.mono, by decide, by decide +kernel⟩
