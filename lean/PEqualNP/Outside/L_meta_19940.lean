import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19940_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 11]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [3, 22]⟩, ⟨.or, [1, 20]⟩, ⟨.and, [19, 18]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [13, 25]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [27, 7]⟩, ⟨.or, [23, 30]⟩, ⟨.and, [28, 34]⟩, ⟨.or, [29, 35]⟩, ⟨.and, [31, 30]⟩, ⟨.or, [37, 36]⟩, ⟨.and, [32, 33]⟩, ⟨.or, [39, 38]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19940_aux

theorem PEqualNP.Outside.L_meta_19940 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19940_aux.main
