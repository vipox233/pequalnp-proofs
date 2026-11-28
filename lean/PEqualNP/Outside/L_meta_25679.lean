import PEqualNP.Defs

-- L-meta-25679: the identity matching with the full row set K and empty L already passes the four-cell test
-- on every pair, so the left side holds for every u and t; the right side 0 ≤ t is trivial.

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25679 :
    ∀ u t : ℕ,
    let G := fun (i j : Fin 4) => (854 : ℕ).testBit (4 * i.val + j.val)
    (∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
        L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
        ∀ i ∈ K, ∀ j ∈ K,
          Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
          Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 0 ≤ t := by
  intro u t G
  refine iff_of_true ⟨Equiv.refl _, Finset.univ, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩ (Nat.zero_le t)
  · simp
  · intro i _ j _
    revert i j
    decide
