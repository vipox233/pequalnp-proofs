import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19896_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 33 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [0, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [24, 7]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [27, 14]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [30, 13]⟩, ⟨.or, [31, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [10, 15]⟩, ⟨.and, [26, 34]⟩, ⟨.and, [21, 35]⟩, ⟨.and, [18, 33]⟩, ⟨.and, [23, 32]⟩, ⟨.and, [20, 9]⟩, ⟨.and, [25, 29]⟩, ⟨.and, [17, 28]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩, ⟨.or, [47, 42]⟩], 48⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19896_aux

theorem PEqualNP.Outside.L_meta_19896 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19896_aux.main
