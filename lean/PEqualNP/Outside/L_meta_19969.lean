import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19969_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 3]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [14, 19]⟩, ⟨.and, [19, 14]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [18, 22]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [20, 0]⟩, ⟨.and, [16, 25]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [27, 2]⟩, ⟨.or, [30, 26]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [32, 29]⟩, ⟨.or, [17, 32]⟩, ⟨.or, [10, 28]⟩, ⟨.and, [33, 35]⟩, ⟨.or, [36, 24]⟩, ⟨.or, [37, 31]⟩, ⟨.and, [23, 34]⟩, ⟨.or, [38, 39]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11683908189968026665 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19969_aux

theorem PEqualNP.Outside.L_meta_19969 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11683908189968026665 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19969_aux.main
