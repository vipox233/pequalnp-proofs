import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19906_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 7]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [18, 10]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [25, 30]⟩, ⟨.or, [26, 29]⟩, ⟨.and, [32, 24]⟩, ⟨.or, [10, 27]⟩, ⟨.or, [20, 5]⟩, ⟨.and, [23, 28]⟩, ⟨.and, [34, 35]⟩, ⟨.or, [37, 33]⟩, ⟨.and, [14, 0]⟩, ⟨.or, [31, 36]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19906_aux

theorem PEqualNP.Outside.L_meta_19906 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19906_aux.main
