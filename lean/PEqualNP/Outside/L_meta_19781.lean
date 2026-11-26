import PEqualNP.Defs

/-! Proof skeleton in the form of upstream `L_meta_19800` (Legoshi): an explicit AND/OR circuit of
fan-in two with 30 gates, checked by `decide`. -/

namespace PEqualNP.Outside.L_meta_19781_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [0, 22]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [8, 23]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [26, 17]⟩, ⟨.or, [3, 19]⟩, ⟨.and, [27, 15]⟩, ⟨.and, [16, 20]⟩, ⟨.or, [30, 5]⟩, ⟨.or, [27, 22]⟩, ⟨.or, [24, 6]⟩, ⟨.or, [15, 26]⟩, ⟨.and, [28, 25]⟩, ⟨.and, [33, 34]⟩, ⟨.or, [6, 21]⟩, ⟨.and, [9, 37]⟩, ⟨.or, [10, 31]⟩, ⟨.or, [39, 0]⟩, ⟨.or, [35, 29]⟩, ⟨.or, [36, 41]⟩, ⟨.or, [42, 38]⟩, ⟨.and, [32, 40]⟩, ⟨.or, [43, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19781_aux

theorem PEqualNP.Outside.L_meta_19781 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19781_aux.main
