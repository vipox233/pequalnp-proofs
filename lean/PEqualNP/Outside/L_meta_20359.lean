import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20359_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 12]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [13, 0]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [11, 2]⟩, ⟨.and, [21, 26]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [27, 30]⟩, ⟨.or, [28, 24]⟩, ⟨.and, [20, 29]⟩, ⟨.and, [31, 1]⟩, ⟨.or, [35, 23]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [38, 34]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2045083468351882920 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20359_aux

theorem PEqualNP.Outside.L_meta_20359 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2045083468351882920 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20359_aux.main
