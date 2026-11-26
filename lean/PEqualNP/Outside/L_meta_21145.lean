import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21145
open PEqualNP.CircuitLowerBounds

def gate (s : Bool × Nat × Nat) : Gate := ⟨if s.1 then .or else .and, [s.2.1,s.2.2]⟩
def gates : List (Bool × Nat × Nat) := [(true,0,2), (true,0,3), (true,1,4), (true,5,6), (true,7,10), (true,8,11), (true,9,11), (false,13,14), (true,12,16), (false,15,17)]
def circuit : Circuit := ⟨gates.map gate, 18⟩

theorem valid : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ gates.map gate from hg)
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_21145

open PEqualNP.Outside.L_meta_21145
theorem PEqualNP.Outside.L_meta_21145 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39383 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨circuit, valid, by decide, by decide +kernel⟩
