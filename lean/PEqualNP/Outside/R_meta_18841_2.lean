import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18841_2
    (hPG23Invariants :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
        (∀ (u v : Fin 26), G.Adj u v ↔
          ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            (u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨ v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) →
        (∀ (a b c d : Fin 26), a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) ∧
        (∀ (u : Fin 26), G.degree u = 4) ∧
        (∀ (u v : Fin 26), G.Adj u v → (u.1 < 13 ∧ 13 ≤ v.1) ∨ (13 ≤ u.1 ∧ v.1 < 13)))
    (hC4FreeJunkLB :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a b c d : Fin 26), a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) →
        (∀ (u : Fin 26), G.degree u = 4) →
        (∀ (u v : Fin 26), G.Adj u v → (u.1 < 13 ∧ 13 ≤ v.1) ∨ (13 ≤ u.1 ∧ v.1 < 13)) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.junk G C ≠ ∅ →
        65 ≤ C.size) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → (65 : ℕ) ≤ x3.size) :=
  fun x1 _ x3 hG hLeast hJunk =>
    let hP := hPG23Invariants x1 hG
    hC4FreeJunkLB x1 x3 hP.1 hP.2.1 hP.2.2 hLeast hJunk
