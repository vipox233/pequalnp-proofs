import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19797

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The posted sketch gives the gate list in wire order.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 9, 13), (true, 10, 12), (true, 8, 14), (true, 11, 15), (true, 11, 16), (true, 14, 19), (true, 17, 18), (true, 16, 21), (false, 0, 23), (true, 8, 10), (true, 25, 13), (true, 26, 19), (false, 1, 27), (true, 9, 22), (false, 2, 29), (true, 18, 20), (false, 3, 31), (true, 17, 21), (false, 4, 33), (true, 8, 12), (true, 35, 15), (true, 36, 16), (false, 5, 37), (true, 17, 20), (false, 6, 39), (true, 15, 22), (false, 7, 41), (true, 24, 28), (true, 43, 30), (true, 44, 32), (true, 45, 34), (true, 46, 38), (true, 47, 40), (true, 48, 42)]
def circuit : Circuit := ⟨codes.map asGate, 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19797

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_19797 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15365916737909796330 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19797.circuit, PEqualNP.Outside.L_meta_19797.mono, by decide, by decide +kernel⟩
