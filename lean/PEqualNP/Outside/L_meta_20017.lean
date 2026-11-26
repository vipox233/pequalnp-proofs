import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20017_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 31 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [12, 15]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [19, 21]⟩, ⟨.and, [0, 26]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 27]⟩, ⟨.and, [3, 28]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 30]⟩, ⟨.and, [6, 25]⟩, ⟨.and, [7, 31]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12886077434404292460 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20017_aux

theorem PEqualNP.Outside.L_meta_20017 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12886077434404292460 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20017_aux.main
