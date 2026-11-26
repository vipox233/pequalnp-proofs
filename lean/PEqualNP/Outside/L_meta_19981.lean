import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19981_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 2]⟩, ⟨.and, [10, 0]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [19, 21]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [0, 23]⟩, ⟨.or, [8, 24]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [23, 5]⟩, ⟨.or, [28, 20]⟩, ⟨.or, [1, 16]⟩, ⟨.and, [18, 29]⟩, ⟨.or, [29, 18]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [31, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [34, 33]⟩, ⟨.or, [3, 35]⟩, ⟨.and, [37, 27]⟩, ⟨.and, [26, 5]⟩, ⟨.or, [22, 39]⟩, ⟨.or, [32, 36]⟩, ⟨.and, [38, 42]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6616700159142438735 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19981_aux

theorem PEqualNP.Outside.L_meta_19981 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6616700159142438735 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19981_aux.main
