import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19995_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 7]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [0, 21]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [28, 16]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [4, 27]⟩, ⟨.or, [21, 27]⟩, ⟨.and, [23, 30]⟩, ⟨.or, [28, 22]⟩, ⟨.or, [7, 25]⟩, ⟨.and, [16, 31]⟩, ⟨.or, [14, 2]⟩, ⟨.and, [26, 24]⟩, ⟨.and, [37, 35]⟩, ⟨.and, [32, 34]⟩, ⟨.or, [33, 38]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [29, 39]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19995_aux

theorem PEqualNP.Outside.L_meta_19995 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19995_aux.main
