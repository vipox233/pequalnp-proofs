import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20019_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 31 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [1, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [21, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [23, 12]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [31, 11]⟩, ⟨.or, [32, 14]⟩, ⟨.and, [0, 27]⟩, ⟨.and, [16, 28]⟩, ⟨.and, [18, 29]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [20, 30]⟩, ⟨.and, [3, 33]⟩, ⟨.and, [19, 25]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20019_aux

theorem PEqualNP.Outside.L_meta_20019 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20019_aux.main
