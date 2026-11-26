import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21210
open PEqualNP.CircuitLowerBounds

def gate (s : Bool × Nat × Nat) : Gate := ⟨if s.1 then .or else .and, [s.2.1,s.2.2]⟩
def gates : List (Bool × Nat × Nat) := [(true,1,4), (true,2,5), (true,3,6), (true,2,8), (true,9,10), (true,7,11), (false,9,12), (false,13,14), (true,0,15), (true,16,17)]
def circuit : Circuit := ⟨gates.map gate, 18⟩

theorem valid : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ gates.map gate from hg)
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_21210

open PEqualNP.Outside.L_meta_21210
theorem PEqualNP.Outside.L_meta_21210 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112543 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨circuit, valid, by decide, by decide +kernel⟩
