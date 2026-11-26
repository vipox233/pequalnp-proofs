import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19938_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 7]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [21, 19]⟩, ⟨.and, [6, 17]⟩, ⟨.and, [18, 20]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [10, 23]⟩, ⟨.or, [12, 20]⟩, ⟨.or, [25, 3]⟩, ⟨.and, [29, 26]⟩, ⟨.or, [16, 25]⟩, ⟨.and, [27, 6]⟩, ⟨.and, [28, 31]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [27, 19]⟩, ⟨.or, [22, 34]⟩, ⟨.or, [36, 32]⟩, ⟨.or, [24, 0]⟩, ⟨.or, [35, 38]⟩, ⟨.and, [37, 39]⟩, ⟨.or, [33, 30]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19938_aux

theorem PEqualNP.Outside.L_meta_19938 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19938_aux.main
