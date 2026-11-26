import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20286

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 27 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [2, 14]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [20, 10]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [24, 18]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [26, 19]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [28, 0]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [30, 8]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [32, 4]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [34, 13]⟩, ⟨.and, [21, 35]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [33, 31]⟩, ⟨.and, [23, 25]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 36]⟩], 42⟩

/-- Boolean check: every gate is AND or OR and reads at most two wires. -/
def andOrTwo (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
      | GateOp.and => true
      | GateOp.or => true
      | _ => false) && decide (g.inputs.length ≤ 2)

theorem andOrTwo_mono (C : Circuit) (h : andOrTwo C = true) : Monotone2 C := by
  intro g hg
  have hg' := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
  refine ⟨?_, hg'.2⟩
  cases hop : g.op <;> simp [hop] at hg' ⊢

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5582313321192137625 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20286

theorem PEqualNP.Outside.L_meta_20286 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5582313321192137625 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20286.rep
