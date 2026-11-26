import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20206_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 8]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [6, 18]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [22, 9]⟩, ⟨.or, [24, 23]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [17, 28]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [19, 29]⟩, ⟨.and, [31, 21]⟩, ⟨.and, [18, 6]⟩, ⟨.and, [25, 32]⟩, ⟨.or, [27, 30]⟩, ⟨.or, [35, 34]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [38, 33]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5360062095110517900 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20206_aux

theorem PEqualNP.Outside.L_meta_20206 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5360062095110517900 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20206_aux.main
