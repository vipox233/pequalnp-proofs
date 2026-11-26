import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20037_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 1]⟩, ⟨.and, [3, 14]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [24, 12]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [23, 16]⟩, ⟨.and, [26, 8]⟩, ⟨.or, [24, 4]⟩, ⟨.or, [29, 13]⟩, ⟨.or, [15, 7]⟩, ⟨.and, [26, 2]⟩, ⟨.or, [31, 3]⟩, ⟨.or, [32, 28]⟩, ⟨.and, [22, 30]⟩, ⟨.or, [11, 33]⟩, ⟨.and, [27, 36]⟩, ⟨.or, [31, 16]⟩, ⟨.and, [21, 38]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [35, 40]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3630327413337270285 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20037_aux

theorem PEqualNP.Outside.L_meta_20037 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3630327413337270285 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20037_aux.main
