import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20289_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 12]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [14, 2]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [22, 19]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [14, 27]⟩, ⟨.or, [25, 4]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [2, 28]⟩, ⟨.or, [28, 19]⟩, ⟨.or, [16, 11]⟩, ⟨.and, [30, 26]⟩, ⟨.or, [29, 24]⟩, ⟨.or, [31, 29]⟩, ⟨.or, [17, 32]⟩, ⟨.and, [35, 21]⟩, ⟨.and, [37, 33]⟩, ⟨.or, [38, 34]⟩, ⟨.or, [24, 18]⟩, ⟨.or, [39, 40]⟩, ⟨.and, [41, 36]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17604493529221135470 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20289_aux

theorem PEqualNP.Outside.L_meta_20289 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17604493529221135470 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20289_aux.main
