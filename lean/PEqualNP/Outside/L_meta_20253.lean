import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20253_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [0, 23]⟩, ⟨.or, [20, 11]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [20, 4]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [20, 28]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [27, 21]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [14, 25]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [24, 31]⟩, ⟨.and, [28, 26]⟩, ⟨.or, [35, 29]⟩, ⟨.or, [22, 34]⟩, ⟨.and, [39, 33]⟩, ⟨.and, [36, 32]⟩, ⟨.and, [38, 30]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [41, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15365916737909796330 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20253_aux

theorem PEqualNP.Outside.L_meta_20253 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15365916737909796330 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20253_aux.main
