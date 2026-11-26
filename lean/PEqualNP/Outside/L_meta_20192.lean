import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20192_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 1]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [17, 25]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [6, 25]⟩, ⟨.or, [16, 30]⟩, ⟨.or, [20, 29]⟩, ⟨.and, [31, 26]⟩, ⟨.or, [27, 3]⟩, ⟨.or, [28, 22]⟩, ⟨.and, [35, 32]⟩, ⟨.or, [34, 26]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [38, 39]⟩, ⟨.or, [33, 23]⟩, ⟨.and, [37, 41]⟩, ⟨.or, [36, 40]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12374965280498343630 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20192_aux

theorem PEqualNP.Outside.L_meta_20192 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12374965280498343630 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20192_aux.main
