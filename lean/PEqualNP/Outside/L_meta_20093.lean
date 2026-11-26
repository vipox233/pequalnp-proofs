import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20093_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 4]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [17, 11]⟩, ⟨.and, [20, 22]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [23, 8]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [15, 0]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [9, 29]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [20, 9]⟩, ⟨.or, [19, 1]⟩, ⟨.or, [18, 26]⟩, ⟨.or, [34, 27]⟩, ⟨.or, [21, 32]⟩, ⟨.and, [35, 30]⟩, ⟨.or, [25, 5]⟩, ⟨.and, [38, 36]⟩, ⟨.and, [33, 31]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973668958787351700 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20093_aux

theorem PEqualNP.Outside.L_meta_20093 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973668958787351700 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20093_aux.main
