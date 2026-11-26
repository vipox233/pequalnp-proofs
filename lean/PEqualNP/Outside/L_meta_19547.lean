import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19547

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [23, 9]⟩, ⟨.or, [26, 11]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [28, 14]⟩, ⟨.or, [25, 10]⟩, ⟨.or, [30, 12]⟩, ⟨.and, [20, 22]⟩, ⟨.and, [17, 21]⟩, ⟨.and, [18, 25]⟩, ⟨.and, [0, 24]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [16, 23]⟩, ⟨.and, [7, 27]⟩, ⟨.and, [6, 31]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_19547

open PEqualNP.Outside.L_meta_19547 in
theorem PEqualNP.Outside.L_meta_19547 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x4eb463b8a3475c99 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
