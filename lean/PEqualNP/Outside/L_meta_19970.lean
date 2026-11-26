import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 10]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [17, 1]⟩, ⟨.and, [12, 1]⟩, ⟨.or, [2, 20]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [27, 11]⟩, ⟨.or, [18, 26]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [28, 32]⟩, ⟨.or, [22, 21]⟩, ⟨.and, [25, 23]⟩, ⟨.or, [30, 29]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [30, 17]⟩, ⟨.and, [34, 36]⟩, ⟨.and, [38, 31]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19970_aux

theorem PEqualNP.Outside.L_meta_19970 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19970_aux.main
