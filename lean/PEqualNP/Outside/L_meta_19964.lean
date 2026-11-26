import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19964_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 2]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [3, 22]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [20, 17]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [24, 8]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [16, 25]⟩, ⟨.or, [12, 22]⟩, ⟨.or, [0, 19]⟩, ⟨.or, [29, 31]⟩, ⟨.or, [27, 11]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [21, 28]⟩, ⟨.or, [34, 32]⟩, ⟨.or, [11, 35]⟩, ⟨.and, [38, 33]⟩, ⟨.or, [30, 35]⟩, ⟨.and, [19, 40]⟩, ⟨.or, [26, 39]⟩, ⟨.or, [41, 36]⟩, ⟨.and, [23, 37]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12374965280498343630 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19964_aux

theorem PEqualNP.Outside.L_meta_19964 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12374965280498343630 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19964_aux.main
