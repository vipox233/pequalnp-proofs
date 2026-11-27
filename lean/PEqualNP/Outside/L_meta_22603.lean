import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22603_aux

open PEqualNP.CircuitLowerBounds

def o (a b : ℕ) : Gate := ⟨.or, [a,b]⟩
def a (u v : ℕ) : Gate := ⟨.and, [u,v]⟩

def witness : Circuit := ⟨[
  o 1 4, o 5 0, a 0 5, o 2 11, o 13 10, o 12 10, o 8 3,
  a 15 13, o 14 6, o 9 17, o 19 16, o 7 20, a 18 21], 22⟩

lemma monotone : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness, o, a]

end PEqualNP.Outside.L_meta_22603_aux

open PEqualNP.Outside.L_meta_22603_aux

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22603 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072251 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, monotone, by decide, by decide⟩
