import PEqualNP.Defs

-- L-meta-25678: with t = 0 the row set K is all four rows; a finite check over every column matching
-- and every set L shows the four-cell test fails on some pair. With t at least 1 the matching that swaps
-- columns 1 and 3, rows K = {0,1,2} and empty L pass.

namespace PEqualNP.Outside.L_meta_25678_aux

def Gm (i j : Fin 4) : Bool := (53 : ℕ).testBit (4 * i.val + j.val)

def bad (f : Fin 4 → Fin 4) (i j : Fin 4) : Bool :=
  Bool.xor (Bool.xor (Gm i (f i)) (Gm j (f j))) (Bool.xor (Gm i (f j)) (Gm j (f i)))

theorem key : ∀ a0 a1 a2 a3 : Fin 4,
    (∀ i j : Fin 4, i ≠ j → (![a0, a1, a2, a3] : Fin 4 → Fin 4) i ≠ ![a0, a1, a2, a3] j) →
    ∀ l0 l1 l2 l3 : Bool, ∃ i j : Fin 4,
      bad ![a0, a1, a2, a3] i j ≠ Bool.xor ((![l0, l1, l2, l3] : Fin 4 → Bool) i) (![l0, l1, l2, l3] j) := by
  decide

end PEqualNP.Outside.L_meta_25678_aux

open PEqualNP.Outside.L_meta_25678_aux in
theorem PEqualNP.Outside.L_meta_25678 :
    ∀ u t : ℕ,
    let G := fun (i j : Fin 4) => (53 : ℕ).testBit (4 * i.val + j.val)
    (∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
        L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
        ∀ i ∈ K, ∀ j ∈ K,
          Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
          Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 1 ≤ t := by
  intro u t G
  constructor
  · rintro ⟨π, K, L, _, _, hK, hcond⟩
    by_contra ht
    have ht0 : t = 0 := by omega
    subst ht0
    have hKu : K = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      have hK' : 4 ≤ K.card := hK
      have := Finset.card_le_univ K
      simp only [Fintype.card_fin] at this
      omega
    subst hKu
    have hf : (π : Fin 4 → Fin 4) = ![π 0, π 1, π 2, π 3] := by
      funext i; fin_cases i <;> rfl
    have hl : (fun i : Fin 4 => decide (i ∈ L)) =
        ![decide (0 ∈ L), decide (1 ∈ L), decide (2 ∈ L), decide (3 ∈ L)] := by
      funext i; fin_cases i <;> rfl
    obtain ⟨i, j, hij⟩ := key (π 0) (π 1) (π 2) (π 3) (by
      rw [← hf]; intro i j hne heq; exact hne (π.injective heq))
      (decide (0 ∈ L)) (decide (1 ∈ L)) (decide (2 ∈ L)) (decide (3 ∈ L))
    have hc := hcond i (Finset.mem_univ _) j (Finset.mem_univ _)
    rw [← hf, ← hl] at hij
    exact hij hc
  · intro ht
    refine ⟨Equiv.swap 1 3, {0, 1, 2}, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩
    · have h3 : ({0, 1, 2} : Finset (Fin 4)).card = 3 := rfl
      rw [h3]; omega
    · revert ht
      intro _
      decide
