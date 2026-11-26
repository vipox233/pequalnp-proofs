import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20336_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 5]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [3, 19]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [22, 6]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [17, 3]⟩, ⟨.or, [28, 7]⟩, ⟨.and, [24, 29]⟩, ⟨.or, [8, 23]⟩, ⟨.or, [2, 18]⟩, ⟨.and, [25, 26]⟩, ⟨.and, [32, 27]⟩, ⟨.or, [19, 23]⟩, ⟨.and, [31, 20]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [30, 33]⟩, ⟨.or, [14, 35]⟩, ⟨.and, [37, 39]⟩, ⟨.or, [38, 34]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [36, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10852103239182430665 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20336_aux

theorem PEqualNP.Outside.L_meta_20336 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10852103239182430665 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20336_aux.main
