import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20018_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 33 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [23, 6]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [26, 10]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [28, 15]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [25, 15]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [32, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [18, 30]⟩, ⟨.and, [4, 25]⟩, ⟨.and, [17, 33]⟩, ⟨.and, [22, 27]⟩, ⟨.and, [24, 29]⟩, ⟨.and, [19, 35]⟩, ⟨.and, [20, 31]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩, ⟨.or, [47, 42]⟩], 48⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8851041321372796905 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20018_aux

theorem PEqualNP.Outside.L_meta_20018 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8851041321372796905 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20018_aux.main
