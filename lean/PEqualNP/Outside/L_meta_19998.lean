import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19998

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 7]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [2, 22]⟩, ⟨.or, [6, 22]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [16, 25]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [5, 30]⟩, ⟨.and, [23, 8]⟩, ⟨.and, [28, 9]⟩, ⟨.and, [29, 10]⟩, ⟨.and, [20, 11]⟩, ⟨.and, [26, 12]⟩, ⟨.and, [21, 13]⟩, ⟨.and, [31, 14]⟩, ⟨.and, [24, 15]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

def isMonoOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem isMonoOpSound (g : Gate) (ok : isMonoOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [isMonoOp, h] at ok ⊢

theorem witnessMono : Monotone2 witness := by
  have legal : witness.gates.all (fun g => isMonoOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using isMonoOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19998

theorem PEqualNP.Outside.L_meta_19998 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨PEqualNP.Outside.L_meta_19998.witness, PEqualNP.Outside.L_meta_19998.witnessMono, by decide, ?_⟩
  unfold PEqualNP.Represents.Represents
  decide +kernel
