import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20112_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [16, 24]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [20, 25]⟩, ⟨.and, [26, 27]⟩, ⟨.and, [7, 22]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [21, 18]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [23, 34]⟩, ⟨.or, [29, 33]⟩, ⟨.or, [28, 35]⟩, ⟨.and, [24, 30]⟩, ⟨.or, [38, 36]⟩, ⟨.or, [39, 32]⟩, ⟨.or, [37, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1885146376704737940 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20112_aux

theorem PEqualNP.Outside.L_meta_20112 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1885146376704737940 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20112_aux.main
