import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20058_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [25, 8]⟩, ⟨.or, [5, 22]⟩, ⟨.and, [8, 24]⟩, ⟨.or, [21, 26]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [14, 23]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [0, 27]⟩, ⟨.or, [33, 0]⟩, ⟨.and, [31, 32]⟩, ⟨.and, [20, 34]⟩, ⟨.or, [35, 12]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [37, 29]⟩, ⟨.and, [28, 30]⟩, ⟨.and, [38, 39]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [43, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5582313321192137625 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20058_aux

theorem PEqualNP.Outside.L_meta_20058 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5582313321192137625 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20058_aux.main
