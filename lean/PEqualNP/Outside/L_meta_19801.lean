import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19801_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 6]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [17, 9]⟩, ⟨.or, [20, 5]⟩, ⟨.and, [19, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [23, 20]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [26, 12]⟩, ⟨.or, [29, 10]⟩, ⟨.and, [24, 30]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [23, 29]⟩, ⟨.and, [16, 33]⟩, ⟨.or, [27, 7]⟩, ⟨.or, [31, 34]⟩, ⟨.and, [11, 28]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [36, 38]⟩, ⟨.and, [35, 32]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11624384703659074185 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19801_aux

theorem PEqualNP.Outside.L_meta_19801 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11624384703659074185 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19801_aux.main
