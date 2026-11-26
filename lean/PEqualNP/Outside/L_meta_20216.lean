import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20216_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 4]⟩, ⟨.and, [14, 0]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [15, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [6, 18]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [25, 20]⟩, ⟨.and, [18, 20]⟩, ⟨.or, [15, 23]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [28, 22]⟩, ⟨.or, [30, 31]⟩, ⟨.and, [33, 26]⟩, ⟨.and, [24, 32]⟩, ⟨.or, [30, 28]⟩, ⟨.and, [36, 29]⟩, ⟨.or, [35, 34]⟩, ⟨.or, [37, 38]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20216_aux

theorem PEqualNP.Outside.L_meta_20216 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20216_aux.main
