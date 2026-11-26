import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20656

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def monotone2Bool (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
     | .and => true
     | .or => true
     | _ => false) && decide (g.inputs.length ≤ 2)

theorem monotone2_of_bool (C : Circuit) (h : monotone2Bool C = true) : Monotone2 C := by
  intro g hg
  have hall := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  refine ⟨?_, hall.2⟩
  cases hop : g.op <;> simp [hop] at hall ⊢

def witness : Circuit :=
  ⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [11, 7]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [11, 8]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.or, [13, 15]⟩
  ], 16⟩

theorem hMono : Monotone2 witness :=
  monotone2_of_bool witness (by decide)

theorem hSize : witness.size ≤ 7 := by
  decide

theorem hRep : Represents (fun u v : Fin 5 => (11770880 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20656

open PEqualNP.Outside.L_meta_20656 in
theorem PEqualNP.Outside.L_meta_20656 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11770880 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  exact ⟨witness, hMono, hSize, hRep⟩
