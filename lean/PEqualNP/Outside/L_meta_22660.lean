import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22660 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841198 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [4, 0]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [1, 3]⟩,
    ⟨.or, [12, 6]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [6, 8]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [11, 10]⟩,
    ⟨.or, [17, 18]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [19, 20]⟩,
    ⟨.and, [1, 16]⟩, ⟨.or, [21, 22]⟩], 23⟩
  refine ⟨C,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
