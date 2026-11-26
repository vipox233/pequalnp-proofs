import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20187_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 13]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [25, 16]⟩, ⟨.and, [23, 19]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [25, 2]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [10, 26]⟩, ⟨.and, [28, 29]⟩, ⟨.or, [32, 19]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [26, 30]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 8]⟩, ⟨.and, [37, 38]⟩, ⟨.or, [31, 5]⟩, ⟨.or, [14, 34]⟩, ⟨.or, [36, 41]⟩, ⟨.or, [24, 39]⟩, ⟨.and, [42, 40]⟩, ⟨.or, [43, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20187_aux

theorem PEqualNP.Outside.L_meta_20187 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20187_aux.main
