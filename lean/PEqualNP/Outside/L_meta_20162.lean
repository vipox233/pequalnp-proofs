import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20162_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 13]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [14, 2]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [5, 20]⟩, ⟨.or, [19, 0]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [4, 22]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [28, 29]⟩, ⟨.and, [10, 17]⟩, ⟨.or, [24, 14]⟩, ⟨.or, [3, 23]⟩, ⟨.or, [30, 24]⟩, ⟨.and, [27, 35]⟩, ⟨.and, [33, 26]⟩, ⟨.or, [37, 32]⟩, ⟨.and, [34, 15]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [36, 31]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3051417864780919815 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20162_aux

theorem PEqualNP.Outside.L_meta_20162 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3051417864780919815 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20162_aux.main
