import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21255
open PEqualNP.CircuitLowerBounds

def gate (s : Bool × Nat × Nat) : Gate := ⟨if s.1 then .or else .and, [s.2.1,s.2.2]⟩
def gates : List (Bool × Nat × Nat) := [(true,0,4), (true,2,6), (true,3,10), (true,11,8), (true,1,5), (true,12,13), (false,9,14), (true,10,7), (false,13,16), (true,15,17)]
def circuit : Circuit := ⟨gates.map gate, 18⟩

theorem valid : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ gates.map gate from hg)
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_21255

open PEqualNP.Outside.L_meta_21255
theorem PEqualNP.Outside.L_meta_21255 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36278 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨circuit, valid, by decide, by decide +kernel⟩
