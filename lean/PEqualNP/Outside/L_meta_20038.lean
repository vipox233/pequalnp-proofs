import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20038_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 13]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [24, 8]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [25, 21]⟩, ⟨.or, [6, 22]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [2, 27]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [17, 31]⟩, ⟨.or, [13, 2]⟩, ⟨.and, [29, 30]⟩, ⟨.or, [32, 34]⟩, ⟨.or, [26, 19]⟩, ⟨.and, [37, 28]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [18, 41]⟩, ⟨.and, [42, 36]⟩, ⟨.or, [40, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10184235645427475370 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20038_aux

theorem PEqualNP.Outside.L_meta_20038 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10184235645427475370 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20038_aux.main
