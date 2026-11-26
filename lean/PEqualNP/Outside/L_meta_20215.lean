import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20215_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 14]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [20, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [26, 22]⟩, ⟨.or, [0, 24]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [25, 3]⟩, ⟨.and, [29, 23]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [5, 28]⟩, ⟨.or, [19, 0]⟩, ⟨.and, [34, 35]⟩, ⟨.and, [17, 31]⟩, ⟨.or, [31, 17]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [37, 36]⟩, ⟨.and, [30, 33]⟩, ⟨.or, [38, 5]⟩, ⟨.and, [39, 42]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [40, 44]⟩, ⟨.or, [41, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20215_aux

theorem PEqualNP.Outside.L_meta_20215 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20215_aux.main
