import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20042_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 9]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [6, 21]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [9, 26]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [2, 26]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [17, 27]⟩, ⟨.and, [23, 30]⟩, ⟨.and, [20, 31]⟩, ⟨.or, [17, 22]⟩, ⟨.and, [24, 34]⟩, ⟨.or, [11, 18]⟩, ⟨.and, [36, 29]⟩, ⟨.or, [35, 33]⟩, ⟨.or, [38, 32]⟩, ⟨.or, [39, 37]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7093347072485314830 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20042_aux

theorem PEqualNP.Outside.L_meta_20042 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7093347072485314830 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20042_aux.main
