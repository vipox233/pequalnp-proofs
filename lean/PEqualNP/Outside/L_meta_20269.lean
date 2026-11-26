import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20269_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 9]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 12]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [4, 21]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [17, 28]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [30, 16]⟩, ⟨.or, [29, 27]⟩, ⟨.or, [32, 23]⟩, ⟨.or, [31, 4]⟩, ⟨.or, [27, 9]⟩, ⟨.or, [22, 36]⟩, ⟨.and, [19, 37]⟩, ⟨.and, [35, 26]⟩, ⟨.and, [20, 34]⟩, ⟨.or, [24, 40]⟩, ⟨.or, [38, 39]⟩, ⟨.and, [33, 41]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6614477138885590260 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20269_aux

theorem PEqualNP.Outside.L_meta_20269 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6614477138885590260 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20269_aux.main
