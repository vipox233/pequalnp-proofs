import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20366_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 5]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [4, 25]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [29, 13]⟩, ⟨.and, [31, 26]⟩, ⟨.or, [22, 3]⟩, ⟨.or, [27, 21]⟩, ⟨.or, [28, 4]⟩, ⟨.or, [30, 34]⟩, ⟨.and, [29, 20]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [16, 11]⟩, ⟨.and, [33, 36]⟩, ⟨.and, [39, 35]⟩, ⟨.or, [41, 40]⟩, ⟨.and, [38, 24]⟩, ⟨.or, [32, 42]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 43]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15737650488314554035 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20366_aux

theorem PEqualNP.Outside.L_meta_20366 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15737650488314554035 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20366_aux.main
