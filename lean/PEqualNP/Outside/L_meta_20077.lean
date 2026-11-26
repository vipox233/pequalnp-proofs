import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20077_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 6]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [20, 3]⟩, ⟨.or, [24, 12]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [28, 4]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [28, 30]⟩, ⟨.and, [16, 27]⟩, ⟨.or, [26, 3]⟩, ⟨.and, [25, 32]⟩, ⟨.and, [22, 31]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [37, 33]⟩, ⟨.and, [19, 34]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [29, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7107882128747567250 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20077_aux

theorem PEqualNP.Outside.L_meta_20077 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7107882128747567250 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20077_aux.main
