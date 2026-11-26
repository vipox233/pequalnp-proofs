import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19756.Work

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gate (o : Bool × Nat × Nat) : Gate :=
  ⟨if o.1 then .and else .or, [o.2.1, o.2.2]⟩

def operations : List (Bool × Nat × Nat) :=
  [(false, 8, 11), (false, 9, 10), (false, 12, 14), (false, 13, 15),
    (false, 9, 13), (false, 20, 16), (true, 0, 21), (false, 18, 19),
    (true, 1, 23), (false, 11, 15), (false, 25, 18), (true, 2, 26),
    (false, 17, 19), (true, 3, 28), (false, 17, 18), (true, 4, 30),
    (false, 10, 12), (false, 32, 16), (true, 5, 33), (false, 8, 14),
    (false, 35, 19), (true, 6, 36), (false, 16, 17), (true, 7, 38),
    (false, 22, 24), (false, 40, 27), (false, 41, 29), (false, 42, 31),
    (false, 43, 34), (false, 44, 37), (false, 45, 39)]

def circuit : Circuit := ⟨operations.map gate, 46⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  change g ∈ operations.map gate at hg
  obtain ⟨⟨b, a, c⟩, _, rfl⟩ := List.mem_map.mp hg
  cases b <;> simp [gate]

end PEqualNP.Outside.L_meta_19756.Work

open PEqualNP.Outside.L_meta_19756.Work in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19756 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1144228038332444715 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨circuit, monotone, by decide, ?_⟩
  unfold PEqualNP.Represents.Represents
  decide +kernel
