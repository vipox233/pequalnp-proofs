import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20110_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 7]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [22, 9]⟩, ⟨.or, [23, 24]⟩, ⟨.and, [6, 25]⟩, ⟨.or, [5, 21]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [19, 9]⟩, ⟨.and, [30, 28]⟩, ⟨.or, [27, 2]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [34, 11]⟩, ⟨.and, [29, 35]⟩, ⟨.or, [5, 17]⟩, ⟨.and, [38, 31]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [33, 26]⟩, ⟨.or, [23, 36]⟩, ⟨.and, [42, 32]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7788925477185833355 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20110_aux

theorem PEqualNP.Outside.L_meta_20110 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7788925477185833355 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20110_aux.main
