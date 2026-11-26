import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20039_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 32 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [22, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [27, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [29, 12]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [25, 13]⟩, ⟨.or, [25, 14]⟩, ⟨.and, [16, 30]⟩, ⟨.and, [24, 34]⟩, ⟨.and, [21, 33]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [23, 28]⟩, ⟨.and, [20, 32]⟩, ⟨.and, [18, 31]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [46, 41]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20039_aux

theorem PEqualNP.Outside.L_meta_20039 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20039_aux.main
