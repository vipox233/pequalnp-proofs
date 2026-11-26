import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19721

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 10, 11), (true, 14, 15), (true, 9, 13), (true, 17, 18), (true, 8, 19), (true, 12, 19), (true, 13, 16), (true, 14, 22), (true, 8, 23), (true, 12, 23), (true, 15, 16), (true, 9, 26), (true, 8, 27), (true, 12, 27), (true, 8, 12), (true, 18, 30), (true, 11, 31), (true, 10, 17), (true, 30, 33), (false, 0, 25), (false, 1, 28), (false, 2, 29), (false, 3, 34), (false, 4, 20), (false, 5, 24), (false, 6, 21), (false, 7, 32), (true, 35, 36), (true, 43, 37), (true, 44, 38), (true, 45, 39), (true, 46, 40), (true, 47, 41), (true, 48, 42)]

def circuit : Circuit := ⟨codes.map asGate, 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19721

open PEqualNP.Outside.L_meta_19721 in
theorem PEqualNP.Outside.L_meta_19721 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
