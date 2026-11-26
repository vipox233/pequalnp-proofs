import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21327
open PEqualNP.CircuitLowerBounds

def gate (s : Bool × Nat × Nat) : Gate := ⟨if s.1 then .or else .and, [s.2.1,s.2.2]⟩
def gates : List (Bool × Nat × Nat) := [(true,7,2), (true,6,1), (true,0,10), (false,9,11), (true,5,4), (true,0,13), (true,3,2), (true,8,10), (true,15,16), (false,14,17), (true,12,18)]
def circuit : Circuit := ⟨gates.map gate, 19⟩

theorem valid : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ gates.map gate from hg)
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_21327

open PEqualNP.Outside.L_meta_21327
theorem PEqualNP.Outside.L_meta_21327 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105852 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨circuit, valid, by decide, by decide +kernel⟩
