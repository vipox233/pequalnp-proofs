import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19746

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mkGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def specs : List (Bool × Nat × Nat) :=
  [(true, 8, 15), (true, 9, 12), (true, 10, 11), (true, 13, 14), (true, 14, 18), (true, 9, 13), (true, 21, 16), (false, 0, 22), (true, 15, 20), (false, 1, 24), (true, 17, 19), (false, 2, 26), (true, 16, 19), (false, 3, 28), (true, 11, 12), (true, 30, 16), (false, 4, 31), (true, 10, 13), (true, 33, 17), (false, 5, 34), (true, 8, 20), (false, 6, 36), (true, 17, 18), (false, 7, 38), (true, 23, 25), (true, 40, 27), (true, 41, 29), (true, 42, 32), (true, 43, 35), (true, 44, 37), (true, 45, 39)]

def wit : Circuit := ⟨specs.map mkGate, 46⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ specs.map mkGate from hg)
  cases b <;> simp [mkGate]

end PEqualNP.Outside.L_meta_19746

open PEqualNP.Outside.L_meta_19746 in
theorem PEqualNP.Outside.L_meta_19746 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2183461428884851875 : ℕ).testBit (8 * u.val + v.val)) 31) :=
  ⟨wit, wit_mono, by decide, by decide +kernel⟩
