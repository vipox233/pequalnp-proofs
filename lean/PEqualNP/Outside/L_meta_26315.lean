import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26315

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12]⟩], 13⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 4 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 7, 7, 7] : List ℕ).getD u.val 0).testBit v.val) wit := by
  decide

end PEqualNP.Outside.L_meta_26315

theorem PEqualNP.Outside.L_meta_26315 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 7, 7, 7] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_26315.wit, PEqualNP.Outside.L_meta_26315.wit_fan, PEqualNP.Outside.L_meta_26315.wit_size,
    PEqualNP.Outside.L_meta_26315.wit_rep⟩
