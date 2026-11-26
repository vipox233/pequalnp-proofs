import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20015_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 32 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [4, 6]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [20, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [27, 14]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [25, 15]⟩, ⟨.or, [25, 8]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [32, 14]⟩, ⟨.or, [33, 15]⟩, ⟨.and, [21, 34]⟩, ⟨.and, [19, 26]⟩, ⟨.and, [24, 30]⟩, ⟨.and, [17, 28]⟩, ⟨.and, [23, 29]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [16, 31]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20015_aux

theorem PEqualNP.Outside.L_meta_20015 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20015_aux.main
