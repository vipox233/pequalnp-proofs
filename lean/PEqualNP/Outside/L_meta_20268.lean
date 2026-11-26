import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20268_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 2]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [0, 22]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [13, 25]⟩, ⟨.and, [26, 7]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [21, 10]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [12, 27]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [14, 30]⟩, ⟨.and, [32, 29]⟩, ⟨.and, [35, 31]⟩, ⟨.or, [28, 14]⟩, ⟨.or, [38, 23]⟩, ⟨.and, [39, 19]⟩, ⟨.and, [34, 33]⟩, ⟨.or, [37, 41]⟩, ⟨.or, [40, 36]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16443534311632980495 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20268_aux

theorem PEqualNP.Outside.L_meta_20268 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16443534311632980495 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20268_aux.main
