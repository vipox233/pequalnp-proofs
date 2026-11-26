import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20036_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [22, 1]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [24, 12]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [26, 25]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [22, 26]⟩, ⟨.or, [23, 21]⟩, ⟨.and, [33, 2]⟩, ⟨.and, [32, 27]⟩, ⟨.and, [31, 28]⟩, ⟨.or, [2, 29]⟩, ⟨.or, [30, 34]⟩, ⟨.or, [35, 38]⟩, ⟨.or, [37, 1]⟩, ⟨.or, [40, 9]⟩, ⟨.and, [41, 20]⟩, ⟨.or, [39, 42]⟩, ⟨.or, [43, 36]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6839968994078334435 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20036_aux

theorem PEqualNP.Outside.L_meta_20036 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6839968994078334435 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20036_aux.main
