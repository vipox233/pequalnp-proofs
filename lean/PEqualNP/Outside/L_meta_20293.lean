import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20293
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

def specifications : List (Bool × ℕ × ℕ) := [
  (true, 7, 13),
  (true, 9, 16),
  (true, 4, 8),
  (true, 5, 15),
  (true, 0, 11),
  (true, 1, 10),
  (true, 1, 18),
  (true, 6, 9),
  (true, 6, 14),
  (true, 20, 17),
  (true, 16, 24),
  (true, 18, 20),
  (true, 22, 12),
  (true, 28, 17),
  (true, 3, 19),
  (true, 12, 30),
  (true, 2, 19),
  (true, 3, 27),
  (true, 14, 32),
  (true, 4, 21),
  (true, 21, 26),
  (true, 2, 23),
  (true, 6, 25),
  (false, 36, 33),
  (false, 29, 34),
  (false, 37, 35),
  (false, 38, 31),
  (true, 39, 40),
  (true, 43, 41),
  (true, 44, 42)]

def gate : Bool × ℕ × ℕ → Gate
  | (false, a, b) => ⟨.and, [a,b]⟩
  | (true, a, b) => ⟨.or, [a,b]⟩

def candidate : Circuit := ⟨specifications.map gate, 45⟩

lemma uniform : Monotone2 candidate := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨⟨op,a,b⟩,_,rfl⟩
  cases op <;> simp [gate]

end PEqualNP.Outside.L_meta_20293

open PEqualNP.Outside.L_meta_20293

theorem PEqualNP.Outside.L_meta_20293 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15680755338451602420 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨candidate, uniform, by decide, ?_⟩
  decide +kernel
