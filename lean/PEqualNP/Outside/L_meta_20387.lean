import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20387_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 10]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [16, 0]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [15, 9]⟩, ⟨.or, [7, 22]⟩, ⟨.or, [20, 8]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [17, 7]⟩, ⟨.and, [28, 23]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [26, 19]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [3, 33]⟩, ⟨.or, [21, 34]⟩, ⟨.or, [15, 19]⟩, ⟨.and, [35, 31]⟩, ⟨.and, [32, 37]⟩, ⟨.and, [30, 36]⟩, ⟨.and, [25, 24]⟩, ⟨.or, [29, 41]⟩, ⟨.or, [38, 42]⟩, ⟨.or, [39, 43]⟩, ⟨.or, [44, 40]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16399645806311595450 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20387_aux

theorem PEqualNP.Outside.L_meta_20387 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16399645806311595450 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20387_aux.main
