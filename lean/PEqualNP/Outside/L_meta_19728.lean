import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19728_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [12, 14]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [5, 19]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [10, 22]⟩, ⟨.or, [21, 23]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [9, 26]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [27, 28]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [25, 30]⟩, ⟨.or, [16, 23]⟩, ⟨.and, [2, 32]⟩, ⟨.or, [16, 27]⟩, ⟨.and, [0, 34]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [12, 28]⟩, ⟨.or, [26, 37]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [4, 40]⟩, ⟨.or, [39, 41]⟩, ⟨.or, [18, 37]⟩, ⟨.and, [6, 43]⟩, ⟨.or, [42, 44]⟩, ⟨.or, [36, 45]⟩, ⟨.or, [31, 46]⟩, ⟨.or, [20, 47]⟩], 48⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19728_aux

theorem PEqualNP.Outside.L_meta_19728 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) 35) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_19728_aux.witness, PEqualNP.Outside.L_meta_19728_aux.witnessFit, by decide, by decide +kernel⟩
