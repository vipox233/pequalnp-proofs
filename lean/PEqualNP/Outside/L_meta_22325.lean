import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22325

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [1, 14]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 18]⟩,
    ⟨.and, [19, 15]⟩,
    ⟨.and, [13, 17]⟩,
    ⟨.or, [20, 21]⟩], 22⟩

def isMonoOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem isMonoOp_sound (g : Gate) (h : isMonoOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases hg : g.op <;> simp [isMonoOp, hg] at h ⊢

theorem witness_mono : Monotone2 witness := by
  have h : witness.gates.all (fun g => isMonoOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have hp := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using isMonoOp_sound g hp.1,
    hp.2⟩

theorem main_aux :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840702 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨witness, witness_mono, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22325

theorem PEqualNP.Outside.L_meta_22325 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840702 : ℕ).testBit (6 * u.val + v.val)) 13) :=
  PEqualNP.Outside.L_meta_22325.main_aux
