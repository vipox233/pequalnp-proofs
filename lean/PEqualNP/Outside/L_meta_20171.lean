import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20171_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 11]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [17, 3]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [6, 14]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [27, 25]⟩, ⟨.or, [8, 28]⟩, ⟨.and, [30, 23]⟩, ⟨.or, [24, 21]⟩, ⟨.and, [12, 23]⟩, ⟨.or, [32, 34]⟩, ⟨.or, [0, 33]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [3, 31]⟩, ⟨.and, [36, 28]⟩, ⟨.or, [35, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [18, 29]⟩, ⟨.and, [37, 42]⟩, ⟨.or, [41, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7598353482589123020 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20171_aux

theorem PEqualNP.Outside.L_meta_20171 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7598353482589123020 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20171_aux.main
