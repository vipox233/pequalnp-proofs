import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

theorem PEqualNP.Outside.L_meta_25673 : (let G := fun (i j : Fin 5) => (25298977 : ℕ).testBit (5 * i.val + j.val)
let u : ℕ := 0
let t : ℕ := 0
(∃ (π : Equiv.Perm (Fin 5)) (K L : Finset (Fin 5)),
    L ⊆ K ∧ L.card ≤ u ∧ 5 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L)))) := by
  let π : Equiv.Perm (Fin 5) :=
    ((Equiv.swap 0 3).trans (Equiv.swap 0 1)).trans (Equiv.swap 0 4)
  exact ⟨π, Finset.univ, ∅, by decide, by decide, by decide, by decide⟩
