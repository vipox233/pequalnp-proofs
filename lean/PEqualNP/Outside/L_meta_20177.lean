import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20177_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 11]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [12, 3]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [29, 28]⟩, ⟨.and, [30, 26]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [32, 27]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [17, 23]⟩, ⟨.and, [36, 34]⟩, ⟨.and, [27, 32]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [39, 31]⟩, ⟨.and, [33, 24]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [37, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20177_aux

theorem PEqualNP.Outside.L_meta_20177 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20177_aux.main
