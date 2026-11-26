import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20199_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [14, 5]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [6, 23]⟩, ⟨.or, [19, 22]⟩, ⟨.and, [30, 29]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [28, 17]⟩, ⟨.or, [13, 34]⟩, ⟨.or, [0, 26]⟩, ⟨.or, [0, 25]⟩, ⟨.or, [27, 31]⟩, ⟨.or, [18, 28]⟩, ⟨.and, [33, 39]⟩, ⟨.and, [35, 36]⟩, ⟨.and, [37, 38]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [43, 42]⟩, ⟨.or, [41, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12606226115316667695 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20199_aux

theorem PEqualNP.Outside.L_meta_20199 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12606226115316667695 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20199_aux.main
