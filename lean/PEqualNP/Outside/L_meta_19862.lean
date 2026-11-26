import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19862
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

def specifications : List (Bool × ℕ × ℕ) := [
  (true, 8, 14),
  (true, 10, 12),
  (true, 11, 15),
  (true, 9, 13),
  (true, 13, 17),
  (true, 16, 18),
  (true, 9, 11),
  (true, 22, 14),
  (true, 23, 17),
  (false, 0, 24),
  (true, 16, 20),
  (false, 1, 26),
  (true, 15, 17),
  (true, 28, 19),
  (false, 2, 29),
  (true, 10, 21),
  (false, 3, 31),
  (true, 9, 21),
  (false, 4, 33),
  (true, 12, 16),
  (true, 35, 19),
  (false, 5, 36),
  (true, 8, 18),
  (true, 38, 19),
  (false, 6, 39),
  (true, 18, 20),
  (false, 7, 41),
  (true, 25, 27),
  (true, 43, 30),
  (true, 44, 32),
  (true, 45, 34),
  (true, 46, 37),
  (true, 47, 40),
  (true, 48, 42)]

def gate : Bool × ℕ × ℕ → Gate
  | (false, a, b) => ⟨.and, [a,b]⟩
  | (true, a, b) => ⟨.or, [a,b]⟩

def candidate : Circuit := ⟨specifications.map gate, 49⟩

lemma uniform : Monotone2 candidate := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨⟨op,a,b⟩,_,rfl⟩
  cases op <;> simp [gate]

end PEqualNP.Outside.L_meta_19862

open PEqualNP.Outside.L_meta_19862

theorem PEqualNP.Outside.L_meta_19862 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13595087219314816350 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  refine ⟨candidate, uniform, by decide, ?_⟩
  decide +kernel
