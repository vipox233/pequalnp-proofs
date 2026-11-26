import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19738

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [9, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [15, 19]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [15, 22]⟩,
    ⟨.or, [16, 23]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.or, [15, 20]⟩,
    ⟨.and, [1, 26]⟩,
    ⟨.or, [11, 20]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [15, 32]⟩,
    ⟨.or, [17, 33]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [8, 21]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [25, 27]⟩,
    ⟨.or, [29, 42]⟩,
    ⟨.or, [31, 43]⟩,
    ⟨.or, [35, 44]⟩,
    ⟨.or, [37, 45]⟩,
    ⟨.or, [39, 46]⟩,
    ⟨.or, [41, 47]⟩], 48⟩

end PEqualNP.Outside.L_meta_19738

theorem PEqualNP.Outside.L_meta_19738 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8857115674703410590 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19738.witness, by simp [PEqualNP.Outside.L_meta_19738.witness, PEqualNP.MetaComplexity.Monotone2],
    by decide, by decide +kernel⟩
