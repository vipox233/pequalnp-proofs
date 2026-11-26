import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20181
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

def specifications : List (Bool × ℕ × ℕ) := [
  (true, 5, 11),
  (true, 2, 15),
  (true, 0, 8),
  (true, 6, 10),
  (true, 7, 9),
  (true, 3, 13),
  (true, 4, 14),
  (true, 19, 21),
  (true, 5, 20),
  (true, 18, 20),
  (true, 8, 24),
  (true, 1, 22),
  (true, 19, 17),
  (true, 9, 22),
  (true, 11, 23),
  (true, 12, 27),
  (true, 0, 29),
  (true, 1, 18),
  (true, 16, 12),
  (true, 26, 21),
  (true, 16, 32),
  (true, 25, 17),
  (false, 37, 30),
  (false, 33, 34),
  (false, 35, 31),
  (false, 28, 36),
  (true, 38, 39),
  (true, 42, 40),
  (true, 43, 41)]

def gate : Bool × ℕ × ℕ → Gate
  | (false, a, b) => ⟨.and, [a,b]⟩
  | (true, a, b) => ⟨.or, [a,b]⟩

def candidate : Circuit := ⟨specifications.map gate, 44⟩

lemma uniform : Monotone2 candidate := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨⟨op,a,b⟩,_,rfl⟩
  cases op <;> simp [gate]

end PEqualNP.Outside.L_meta_20181

open PEqualNP.Outside.L_meta_20181

theorem PEqualNP.Outside.L_meta_20181 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8992515997758798780 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨candidate, uniform, by decide, ?_⟩
  decide +kernel
