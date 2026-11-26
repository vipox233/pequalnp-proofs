import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20379_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 15]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [21, 15]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [27, 16]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [30, 8]⟩, ⟨.and, [29, 20]⟩, ⟨.or, [30, 18]⟩, ⟨.or, [28, 2]⟩, ⟨.or, [27, 25]⟩, ⟨.or, [23, 34]⟩, ⟨.or, [35, 24]⟩, ⟨.or, [34, 33]⟩, ⟨.or, [10, 25]⟩, ⟨.and, [37, 31]⟩, ⟨.and, [26, 38]⟩, ⟨.and, [39, 36]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6609709397838714315 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20379_aux

theorem PEqualNP.Outside.L_meta_20379 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6609709397838714315 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20379_aux.main
