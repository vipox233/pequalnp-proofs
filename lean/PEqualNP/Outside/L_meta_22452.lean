import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22452

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [13, 16]⟩,
    ⟨.or, [4, 17]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.or, [20, 21]⟩], 22⟩

def validGate (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && (g.inputs.length ≤ 2)

theorem circuit_monotone : Monotone2 circuit := by
  have h : circuit.gates.all validGate = true := by decide
  intro g hg
  have hv := List.all_eq_true.mp h g hg
  cases he : g.op <;> simp_all [validGate]

theorem circuit_represents :
    Represents (fun (u : Fin 4) (v : Fin 6) =>
      (1883389 : ℕ).testBit (6 * u.val + v.val)) circuit := by
  decide +kernel

end PEqualNP.Outside.L_meta_22452

theorem PEqualNP.Outside.L_meta_22452 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) =>
      (1883389 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22452.circuit,
    PEqualNP.Outside.L_meta_22452.circuit_monotone, by decide,
    PEqualNP.Outside.L_meta_22452.circuit_represents⟩
