import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19885_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 12]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [6, 20]⟩, ⟨.or, [22, 1]⟩, ⟨.and, [9, 23]⟩, ⟨.and, [13, 18]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [5, 22]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [25, 28]⟩, ⟨.and, [6, 21]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [31, 27]⟩, ⟨.or, [28, 19]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [32, 30]⟩, ⟨.or, [16, 33]⟩, ⟨.or, [7, 35]⟩, ⟨.or, [1, 34]⟩, ⟨.and, [37, 39]⟩, ⟨.or, [29, 5]⟩, ⟨.or, [40, 36]⟩, ⟨.and, [38, 41]⟩, ⟨.or, [24, 42]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3120634772845828080 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19885_aux

theorem PEqualNP.Outside.L_meta_19885 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3120634772845828080 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19885_aux.main
