import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 15]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [17, 7]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [24, 4]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [22, 29]⟩, ⟨.or, [25, 30]⟩, ⟨.or, [31, 16]⟩, ⟨.or, [25, 2]⟩, ⟨.and, [32, 23]⟩, ⟨.or, [35, 28]⟩, ⟨.or, [34, 18]⟩, ⟨.and, [37, 27]⟩, ⟨.and, [33, 26]⟩, ⟨.or, [36, 38]⟩, ⟨.or, [40, 39]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14134136632318694985 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20057_aux

theorem PEqualNP.Outside.L_meta_20057 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14134136632318694985 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20057_aux.main
