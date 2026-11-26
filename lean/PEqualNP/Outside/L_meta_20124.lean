import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20124_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 32 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [20, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [23, 5]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [25, 9]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [28, 13]⟩, ⟨.or, [29, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [32, 15]⟩, ⟨.or, [25, 12]⟩, ⟨.and, [24, 30]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [16, 33]⟩, ⟨.and, [21, 27]⟩, ⟨.and, [18, 31]⟩, ⟨.and, [19, 34]⟩, ⟨.and, [22, 26]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20124_aux

theorem PEqualNP.Outside.L_meta_20124 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20124_aux.main
