import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19555

def witness : Circuit :=
  ⟨[⟨.or, [11, 6]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [25, 12]⟩, ⟨.or, [16, 25]⟩, ⟨.or, [2, 22]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [29, 21]⟩, ⟨.or, [27, 22]⟩, ⟨.and, [30, 23]⟩, ⟨.or, [2, 21]⟩, ⟨.or, [23, 19]⟩, ⟨.and, [20, 27]⟩, ⟨.or, [29, 34]⟩, ⟨.and, [28, 26]⟩, ⟨.and, [18, 36]⟩, ⟨.or, [38, 37]⟩, ⟨.and, [33, 31]⟩, ⟨.or, [40, 35]⟩, ⟨.or, [32, 39]⟩, ⟨.or, [42, 41]⟩], 43⟩

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

end PEqualNP.Outside.L_meta_19555

open PEqualNP.Outside.L_meta_19555 in
theorem PEqualNP.Outside.L_meta_19555 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x2e87c9d235786996 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
