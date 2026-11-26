import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20329_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [17, 8]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [7, 22]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [24, 25]⟩, ⟨.and, [19, 26]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [23, 8]⟩, ⟨.or, [9, 29]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [31, 34]⟩, ⟨.and, [32, 28]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [0, 33]⟩, ⟨.and, [37, 38]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [35, 40]⟩, ⟨.or, [41, 36]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20329_aux

theorem PEqualNP.Outside.L_meta_20329 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20329_aux.main
