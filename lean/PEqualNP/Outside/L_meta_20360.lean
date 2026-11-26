import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20360_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 14]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [19, 1]⟩, ⟨.or, [11, 20]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [18, 11]⟩, ⟨.and, [21, 17]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [3, 26]⟩, ⟨.or, [22, 28]⟩, ⟨.or, [19, 9]⟩, ⟨.or, [22, 16]⟩, ⟨.and, [27, 30]⟩, ⟨.and, [29, 24]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [10, 34]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [31, 1]⟩, ⟨.or, [10, 19]⟩, ⟨.and, [2, 38]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 25]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20360_aux

theorem PEqualNP.Outside.L_meta_20360 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20360_aux.main
