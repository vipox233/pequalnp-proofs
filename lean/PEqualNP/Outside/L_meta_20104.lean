import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20104_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 7]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [23, 22]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [11, 1]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [19, 28]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [17, 25]⟩, ⟨.or, [29, 26]⟩, ⟨.or, [6, 33]⟩, ⟨.or, [6, 26]⟩, ⟨.or, [36, 10]⟩, ⟨.and, [27, 24]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [38, 39]⟩, ⟨.and, [34, 35]⟩, ⟨.and, [37, 32]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [41, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11442406341415304295 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20104_aux

theorem PEqualNP.Outside.L_meta_20104 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11442406341415304295 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20104_aux.main
