import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19941_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 3]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [13, 24]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [22, 1]⟩, ⟨.and, [27, 21]⟩, ⟨.or, [25, 1]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [31, 11]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [4, 28]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [36, 34]⟩, ⟨.and, [33, 18]⟩, ⟨.or, [38, 29]⟩, ⟨.and, [32, 30]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [16, 35]⟩, ⟨.and, [17, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19941_aux

theorem PEqualNP.Outside.L_meta_19941 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19941_aux.main
