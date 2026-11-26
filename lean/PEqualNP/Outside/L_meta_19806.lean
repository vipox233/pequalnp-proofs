import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 3]⟩, ⟨.or, [16, 0]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [19, 9]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [18, 2]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [21, 14]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [27, 29]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [12, 21]⟩, ⟨.and, [26, 31]⟩, ⟨.and, [28, 16]⟩, ⟨.or, [33, 34]⟩, ⟨.and, [25, 23]⟩, ⟨.or, [20, 32]⟩, ⟨.and, [37, 24]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [30, 39]⟩, ⟨.or, [40, 36]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5346231350888391705 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19806_aux

theorem PEqualNP.Outside.L_meta_19806 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5346231350888391705 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_19806_aux.main
