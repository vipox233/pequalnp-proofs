import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20246_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 4]⟩, ⟨.and, [7, 14]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [2, 15]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [26, 20]⟩, ⟨.or, [17, 27]⟩, ⟨.or, [11, 24]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [30, 2]⟩, ⟨.and, [31, 29]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [21, 33]⟩, ⟨.or, [22, 33]⟩, ⟨.or, [26, 25]⟩, ⟨.and, [35, 18]⟩, ⟨.or, [5, 22]⟩, ⟨.or, [34, 23]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [12, 20]⟩, ⟨.and, [39, 38]⟩, ⟨.and, [41, 36]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8851041321372796905 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20246_aux

theorem PEqualNP.Outside.L_meta_20246 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8851041321372796905 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20246_aux.main
