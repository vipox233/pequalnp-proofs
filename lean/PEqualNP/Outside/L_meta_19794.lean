import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19794

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The posted sketch gives the gate list in wire order.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 8, 12), (true, 9, 13), (true, 10, 11), (true, 10, 15), (true, 11, 15), (true, 9, 14), (true, 21, 20), (false, 0, 22), (true, 13, 14), (true, 24, 18), (false, 1, 25), (true, 16, 19), (false, 2, 27), (true, 16, 20), (false, 3, 29), (true, 16, 17), (false, 4, 31), (true, 8, 14), (true, 33, 17), (false, 5, 34), (true, 17, 18), (false, 6, 36), (true, 12, 14), (true, 38, 19), (false, 7, 39), (true, 23, 26), (true, 41, 28), (true, 42, 30), (true, 43, 32), (true, 44, 35), (true, 45, 37), (true, 46, 40)]
def circuit : Circuit := ⟨codes.map asGate, 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19794

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_19794 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15289266858240601290 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19794.circuit, PEqualNP.Outside.L_meta_19794.mono, by decide, by decide +kernel⟩
