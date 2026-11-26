import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20099_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 1]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [3, 19]⟩, ⟨.and, [16, 20]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [24, 2]⟩, ⟨.and, [27, 28]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [29, 21]⟩, ⟨.or, [22, 30]⟩, ⟨.or, [10, 26]⟩, ⟨.and, [32, 25]⟩, ⟨.or, [33, 12]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [36, 26]⟩, ⟨.or, [34, 31]⟩, ⟨.or, [37, 3]⟩, ⟨.and, [35, 39]⟩, ⟨.or, [38, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11871860300395540620 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20099_aux

theorem PEqualNP.Outside.L_meta_20099 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11871860300395540620 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20099_aux.main
