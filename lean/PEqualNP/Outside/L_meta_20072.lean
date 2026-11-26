import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20072_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 32 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [12, 14]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [26, 11]⟩, ⟨.or, [16, 23]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [0, 24]⟩, ⟨.and, [1, 25]⟩, ⟨.and, [2, 27]⟩, ⟨.and, [3, 28]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 30]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [7, 32]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩, ⟨.or, [46, 40]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20072_aux

theorem PEqualNP.Outside.L_meta_20072 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20072_aux.main
