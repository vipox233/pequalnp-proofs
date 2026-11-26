import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20163

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate list obtained by factoring a cover of the matrix by rectangles.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 8, 14), (true, 10, 11), (true, 9, 15), (true, 12, 17), (true, 13, 18), (true, 13, 16), (true, 20, 8), (true, 14, 20), (true, 15, 19), (true, 18, 12), (true, 25, 10), (true, 9, 19), (true, 11, 21), (true, 17, 16), (true, 12, 21), (false, 0, 22), (false, 1, 23), (false, 2, 24), (false, 3, 26), (false, 4, 27), (false, 5, 28), (false, 6, 29), (false, 7, 30), (true, 31, 32), (true, 39, 33), (true, 40, 34), (true, 41, 35), (true, 42, 36), (true, 43, 37), (true, 44, 38)]
def circuit : Circuit := ⟨codes.map asGate, 45⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20163

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_20163 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8164297279589376675 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  exact ⟨PEqualNP.Outside.L_meta_20163.circuit, PEqualNP.Outside.L_meta_20163.mono, by decide, by decide +kernel⟩
