import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21378

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [14, 3]⟩,
    ⟨.and, [10, 5]⟩,
    ⟨.and, [11, 15]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 18]⟩], 20⟩

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
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104254 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  ⟨witness, witness_mono, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21378

theorem PEqualNP.Outside.L_meta_21378 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104254 : ℕ).testBit (5 * u.val + v.val)) 12) :=
  PEqualNP.Outside.L_meta_21378.main_aux
