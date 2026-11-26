import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20183_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 10]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [7, 24]⟩, ⟨.and, [21, 23]⟩, ⟨.or, [11, 22]⟩, ⟨.or, [21, 28]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [27, 25]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [32, 0]⟩, ⟨.or, [32, 20]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [33, 26]⟩, ⟨.or, [13, 28]⟩, ⟨.and, [31, 35]⟩, ⟨.and, [38, 2]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [37, 41]⟩, ⟨.and, [36, 34]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20183_aux

theorem PEqualNP.Outside.L_meta_20183 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20183_aux.main
