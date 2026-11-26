import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19857_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 9]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [26, 3]⟩, ⟨.and, [29, 21]⟩, ⟨.or, [14, 22]⟩, ⟨.or, [21, 28]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [25, 33]⟩, ⟨.and, [12, 5]⟩, ⟨.or, [30, 27]⟩, ⟨.or, [24, 6]⟩, ⟨.and, [37, 31]⟩, ⟨.or, [29, 10]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [34, 20]⟩, ⟨.or, [39, 16]⟩, ⟨.or, [38, 41]⟩, ⟨.and, [42, 40]⟩, ⟨.or, [43, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6650604754610151990 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19857_aux

theorem PEqualNP.Outside.L_meta_19857 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6650604754610151990 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19857_aux.main
