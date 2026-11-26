import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20250_aux

open PEqualNP.CircuitLowerBounds

def o (a b : ℕ) : Gate := ⟨.or, [a,b]⟩
def a (u v : ℕ) : Gate := ⟨.and, [u,v]⟩

def witness : Circuit := ⟨[
  o 3 13, o 8 16, o 0 17, o 9 18,
  o 0 6, a 9 20, o 15 21, o 5 22,
  o 4 11, o 23 24, a 19 25, o 1 12,
  o 6 8, o 27 28, o 10 24, o 2 30,
  o 16 31, a 29 32, o 2 14, o 7 34,
  o 0 27, o 10 36, o 23 37, a 7 14,
  o 38 39, a 35 40, o 33 41, o 26 42], 43⟩

lemma monotone : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness, List.forall_mem_cons, o, a]

end PEqualNP.Outside.L_meta_20250_aux

open PEqualNP.Outside.L_meta_20250_aux

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_20250 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15289266858240601290 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨witness, monotone, by decide, by decide⟩
