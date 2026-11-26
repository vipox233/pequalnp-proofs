import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20198_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 3]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [18, 2]⟩, ⟨.or, [16, 11]⟩, ⟨.and, [19, 16]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [27, 8]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [26, 30]⟩, ⟨.and, [24, 20]⟩, ⟨.or, [1, 18]⟩, ⟨.and, [30, 29]⟩, ⟨.and, [25, 8]⟩, ⟨.or, [6, 23]⟩, ⟨.or, [15, 36]⟩, ⟨.and, [28, 33]⟩, ⟨.and, [31, 37]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [32, 38]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [42, 41]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20198_aux

theorem PEqualNP.Outside.L_meta_20198 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20198_aux.main
