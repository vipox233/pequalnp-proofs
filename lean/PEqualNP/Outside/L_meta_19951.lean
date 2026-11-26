import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 1]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [7, 16]⟩, ⟨.and, [14, 19]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [22, 23]⟩, ⟨.or, [7, 24]⟩, ⟨.and, [27, 18]⟩, ⟨.or, [26, 25]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [3, 28]⟩, ⟨.or, [9, 30]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [31, 17]⟩, ⟨.and, [33, 29]⟩, ⟨.or, [27, 10]⟩, ⟨.or, [34, 13]⟩, ⟨.or, [36, 1]⟩, ⟨.or, [20, 35]⟩, ⟨.and, [38, 37]⟩, ⟨.or, [40, 39]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19951_aux

theorem PEqualNP.Outside.L_meta_19951 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19951_aux.main
