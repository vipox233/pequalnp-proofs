import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21274
open PEqualNP.CircuitLowerBounds

def gate (s : Bool × Nat × Nat) : Gate := ⟨if s.1 then .or else .and, [s.2.1,s.2.2]⟩
def gates : List (Bool × Nat × Nat) := [(true,0,3), (true,2,4), (true,0,5), (true,1,6), (true,7,10), (true,8,10), (true,9,11), (true,11,13), (false,14,15), (true,12,17), (false,16,18)]
def circuit : Circuit := ⟨gates.map gate, 19⟩

theorem valid : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ gates.map gate from hg)
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_21274

open PEqualNP.Outside.L_meta_21274
theorem PEqualNP.Outside.L_meta_21274 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39285 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨circuit, valid, by decide, by decide +kernel⟩
