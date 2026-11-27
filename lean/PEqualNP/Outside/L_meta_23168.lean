import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23168
open PEqualNP.CircuitLowerBounds

def gate (s : Bool × Nat × Nat) : Gate := ⟨if s.1 then .or else .and, [s.2.1,s.2.2]⟩
def gates : List (Bool × Nat × Nat) := [(true,1,5), (true,0,3), (true,4,10), (true,9,11), (true,2,6), (true,7,3), (true,13,14), (true,8,9), (false,11,16), (true,15,17), (false,12,18)]
def circuit : Circuit := ⟨gates.map gate, 19⟩

theorem valid : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ gates.map gate from hg)
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_23168

open PEqualNP.Outside.L_meta_23168
theorem PEqualNP.Outside.L_meta_23168 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨circuit, valid, by decide, by decide +kernel⟩
