import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20076_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 2]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [23, 22]⟩, ⟨.or, [25, 6]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [5, 20]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [25, 13]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [33, 4]⟩, ⟨.and, [29, 32]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [31, 35]⟩, ⟨.and, [37, 28]⟩, ⟨.or, [38, 36]⟩, ⟨.and, [30, 34]⟩, ⟨.or, [39, 41]⟩, ⟨.or, [27, 40]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16879102062354748875 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20076_aux

theorem PEqualNP.Outside.L_meta_20076 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16879102062354748875 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20076_aux.main
