import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19892_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 10]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [21, 13]⟩, ⟨.and, [3, 14]⟩, ⟨.and, [16, 25]⟩, ⟨.or, [12, 26]⟩, ⟨.or, [6, 24]⟩, ⟨.or, [0, 23]⟩, ⟨.and, [21, 31]⟩, ⟨.or, [30, 32]⟩, ⟨.or, [27, 23]⟩, ⟨.or, [0, 29]⟩, ⟨.and, [7, 22]⟩, ⟨.or, [19, 28]⟩, ⟨.or, [34, 25]⟩, ⟨.and, [37, 38]⟩, ⟨.and, [33, 35]⟩, ⟨.or, [36, 39]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9886157967400379655 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19892_aux

theorem PEqualNP.Outside.L_meta_19892 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9886157967400379655 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19892_aux.main
