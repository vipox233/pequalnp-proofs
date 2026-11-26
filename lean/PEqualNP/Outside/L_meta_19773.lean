import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19773 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5672340417107567985 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  let C : Circuit := ⟨[⟨.or, [8, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [22, 16]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [25, 18]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [4, 30]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [32, 16]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [35, 18]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [38, 17]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩], 47⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
