import PEqualNP.MetaComplexity.Helpers.FullBorder

theorem PEqualNP.MetaComplexity.L32019 :
∀ (a b p q s : Nat) (A : Fin a → Fin b → Bool),
  (∀ i, ∃ j, A i j = false) → (∀ j, ∃ i, A i j = false) → (∃ i j, A i j = true) →
  (PEqualNP.Represents.RepSizeAtMost
    (fun (i : Fin (a+p)) (j : Fin (b+q)) =>
      if hi : i.val < a then
        if hj : j.val < b then A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else true
      else true) s ↔
    ∃ t : Nat, PEqualNP.Represents.RepSizeAtMost A t ∧ t+p+q ≤ s) :=
  PEqualNP.FullBorder.exact
