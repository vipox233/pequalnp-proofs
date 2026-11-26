import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19953_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 10]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [1, 22]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [30, 29]⟩, ⟨.or, [29, 16]⟩, ⟨.and, [26, 27]⟩, ⟨.or, [5, 20]⟩, ⟨.or, [21, 35]⟩, ⟨.and, [25, 33]⟩, ⟨.or, [18, 31]⟩, ⟨.and, [38, 32]⟩, ⟨.or, [39, 34]⟩, ⟨.and, [36, 28]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 37]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8992515997758798780 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19953_aux

theorem PEqualNP.Outside.L_meta_19953 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8992515997758798780 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19953_aux.main
