import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19950_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 3]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [18, 23]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [27, 23]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [18, 28]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [19, 2]⟩, ⟨.and, [31, 25]⟩, ⟨.or, [33, 22]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [36, 17]⟩, ⟨.and, [37, 20]⟩, ⟨.and, [35, 32]⟩, ⟨.or, [34, 39]⟩, ⟨.or, [40, 38]⟩, ⟨.and, [29, 30]⟩, ⟨.or, [42, 41]⟩], 43⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2119688362457708970 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19950_aux

theorem PEqualNP.Outside.L_meta_19950 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2119688362457708970 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_19950_aux.main
