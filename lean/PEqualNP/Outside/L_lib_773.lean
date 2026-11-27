import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

theorem PEqualNP.Outside.L_lib_773 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool),
  (∀ a b : Fin n, a ≠ b → ∀ c d : Fin m, c ≠ d →
    ¬ (G a c = true ∧ G a d = true ∧ G b c = true ∧ G b d = true)) →
  (∑ c : Fin m, Nat.choose (Finset.univ.filter (fun a : Fin n => G a c = true)).card 2)
    ≤ Nat.choose n 2 := by
  intro n m G noFour
  let rows (c : Fin m) := Finset.univ.filter (fun a : Fin n => G a c = true)
  let pairs (c : Fin m) := (rows c).powersetCard 2
  have separate : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint pairs := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro P hPc hPd
    obtain ⟨subC, size⟩ := Finset.mem_powersetCard.mp hPc
    have subD := (Finset.mem_powersetCard.mp hPd).1
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [size]; decide : 1 < P.card)
    exact noFour a b hab c d hcd
      ⟨(Finset.mem_filter.mp (subC ha)).2, (Finset.mem_filter.mp (subD ha)).2,
       (Finset.mem_filter.mp (subC hb)).2, (Finset.mem_filter.mp (subD hb)).2⟩
  have subset :
      Finset.univ.biUnion pairs ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro P hP
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hP
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hc).2⟩
  have bound := Finset.card_le_card subset
  rw [Finset.card_biUnion separate, Finset.card_powersetCard] at bound
  simpa only [pairs, Finset.card_powersetCard, rows, Finset.card_univ, Fintype.card_fin] using bound
