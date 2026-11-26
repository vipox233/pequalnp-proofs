import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19902_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [15, 3]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [25, 23]⟩, ⟨.or, [10, 24]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [24, 2]⟩, ⟨.or, [2, 25]⟩, ⟨.or, [20, 15]⟩, ⟨.and, [31, 27]⟩, ⟨.or, [22, 29]⟩, ⟨.and, [28, 8]⟩, ⟨.and, [18, 19]⟩, ⟨.and, [32, 1]⟩, ⟨.or, [7, 30]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [15, 22]⟩, ⟨.or, [36, 40]⟩, ⟨.or, [39, 33]⟩, ⟨.or, [26, 21]⟩, ⟨.or, [3, 41]⟩, ⟨.and, [38, 34]⟩, ⟨.and, [44, 43]⟩, ⟨.or, [46, 42]⟩, ⟨.or, [45, 47]⟩], 48⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17418911685824797215 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19902_aux

theorem PEqualNP.Outside.L_meta_19902 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17418911685824797215 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19902_aux.main
