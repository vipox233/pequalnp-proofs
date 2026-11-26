import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19730

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 9, 14), (true, 10, 11), (true, 13, 17), (true, 8, 18), (true, 12, 18), (true, 13, 16), (true, 8, 21), (true, 15, 21), (true, 8, 12), (true, 15, 24), (true, 9, 25), (true, 10, 25), (true, 12, 16), (true, 11, 28), (true, 14, 17), (true, 15, 30), (false, 0, 20), (false, 1, 23), (false, 2, 29), (false, 3, 22), (false, 4, 19), (false, 5, 31), (false, 6, 26), (false, 7, 27), (true, 32, 33), (true, 40, 34), (true, 41, 35), (true, 42, 36), (true, 43, 37), (true, 44, 38), (true, 45, 39)]

def circuit : Circuit := ⟨codes.map asGate, 46⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19730

open PEqualNP.Outside.L_meta_19730 in
theorem PEqualNP.Outside.L_meta_19730 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
