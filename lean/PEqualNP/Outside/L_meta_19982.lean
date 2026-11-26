import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19982_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 14]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [25, 10]⟩, ⟨.or, [9, 23]⟩, ⟨.or, [4, 26]⟩, ⟨.and, [18, 10]⟩, ⟨.or, [22, 13]⟩, ⟨.and, [27, 28]⟩, ⟨.and, [21, 30]⟩, ⟨.and, [22, 17]⟩, ⟨.or, [24, 15]⟩, ⟨.and, [34, 3]⟩, ⟨.or, [0, 25]⟩, ⟨.and, [17, 36]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [33, 31]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [38, 29]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19982_aux

theorem PEqualNP.Outside.L_meta_19982 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19982_aux.main
