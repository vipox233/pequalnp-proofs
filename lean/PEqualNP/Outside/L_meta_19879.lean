import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19879_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 0]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [20, 6]⟩, ⟨.and, [18, 4]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [24, 9]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [19, 20]⟩, ⟨.and, [23, 26]⟩, ⟨.or, [6, 26]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [21, 30]⟩, ⟨.or, [25, 28]⟩, ⟨.and, [33, 31]⟩, ⟨.and, [22, 4]⟩, ⟨.and, [32, 27]⟩, ⟨.and, [29, 34]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [38, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3585502085313761580 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19879_aux

theorem PEqualNP.Outside.L_meta_19879 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3585502085313761580 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19879_aux.main
