import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19898_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 9]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [23, 4]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [11, 27]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [26, 29]⟩, ⟨.and, [21, 26]⟩, ⟨.or, [24, 32]⟩, ⟨.and, [31, 1]⟩, ⟨.and, [22, 32]⟩, ⟨.or, [20, 28]⟩, ⟨.and, [19, 25]⟩, ⟨.and, [27, 33]⟩, ⟨.or, [30, 35]⟩, ⟨.and, [8, 16]⟩, ⟨.or, [8, 39]⟩, ⟨.or, [36, 40]⟩, ⟨.and, [41, 42]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [38, 44]⟩, ⟨.or, [34, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19898_aux

theorem PEqualNP.Outside.L_meta_19898 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19898_aux.main
