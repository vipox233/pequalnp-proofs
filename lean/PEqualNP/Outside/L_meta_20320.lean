import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20320

open PEqualNP.CircuitLowerBounds

private def gateMono2 (g : Gate) : Bool :=
  (match g.op with | .and => true | .or => true | _ => false) && g.inputs.length ≤ 2

private theorem gateMono2_sound (g : Gate) (h : gateMono2 g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases ho : g.op <;> simp [gateMono2, ho] at h ⊢
  · exact h
  · exact h

private theorem monotone2_of_all (C : Circuit) (h : C.gates.all gateMono2 = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  exact gateMono2_sound g ((List.all_eq_true.mp h) g hg)

private def witness : Circuit :=
  ⟨[⟨.or, [7, 13]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [4, 8]⟩,
    ⟨.or, [6, 16]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [22, 14]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [9, 16]⟩,
    ⟨.or, [25, 19]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [29, 17]⟩,
    ⟨.or, [30, 21]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [32, 12]⟩, ⟨.or, [3, 21]⟩, ⟨.or, [14, 19]⟩,
    ⟨.or, [6, 9]⟩, ⟨.or, [36, 20]⟩, ⟨.and, [24, 26]⟩, ⟨.and, [28, 31]⟩, ⟨.and, [33, 34]⟩,
    ⟨.and, [35, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [43, 41]⟩], 44⟩

end PEqualNP.Outside.L_meta_20320

theorem PEqualNP.Outside.L_meta_20320 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15374695358257377210 : ℕ).testBit (8 * u.val + v.val)) 29) := by
  refine ⟨PEqualNP.Outside.L_meta_20320.witness,
    PEqualNP.Outside.L_meta_20320.monotone2_of_all _ (by decide),
    by decide, ?_⟩
  decide +kernel
