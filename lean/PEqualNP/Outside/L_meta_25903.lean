import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25903

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 8]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [25, 9]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [17, 25]⟩, ⟨.or, [12, 24]⟩, ⟨.and, [17, 26]⟩, ⟨.or, [29, 20]⟩, ⟨.or, [1, 18]⟩, ⟨.and, [27, 31]⟩, ⟨.and, [0, 28]⟩, ⟨.and, [22, 23]⟩, ⟨.or, [35, 30]⟩, ⟨.or, [33, 34]⟩, ⟨.and, [32, 20]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [39, 36]⟩], 40⟩

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

end PEqualNP.Outside.L_meta_25903

theorem PEqualNP.Outside.L_meta_25903 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8080454460742251720 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨PEqualNP.Outside.L_meta_25903.C_, PEqualNP.Outside.L_meta_25903.monoTwoB_sound PEqualNP.Outside.L_meta_25903.C_ (by decide +kernel), by decide, by decide +kernel⟩
