import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- A cut by the size of U* (edges that are no top's cross pair).
-- |U*| <= 2 is impossible (proved here): two junk gates force 4*2+4 <= 5*|U*|.
-- few:  3 <= |U*| <= 12, so the non-centreless tops number at least 10.
-- many: |U*| >= 13.
theorem PEqualNP.Outside.R_meta_8943_412
    (few : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
      52 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card +
          (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
      52 ≤ 4 * (tops G C \ centreless G C).card + (Ustar G C).card →
      4 * ((junk G C).card + 2 * (centreless G C).card + (orN G C \ lam G C).card) + 4 ≤
          5 * (Ustar G C).card →
      3 ≤ (Ustar G C).card → (Ustar G C).card ≤ 12 → False)
    (many : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
      52 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card +
          (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
      52 ≤ 4 * (tops G C \ centreless G C).card + (Ustar G C).card →
      4 * ((junk G C).card + 2 * (centreless G C).card + (orN G C \ lam G C).card) + 4 ≤
          5 * (Ustar G C).card →
      13 ≤ (Ustar G C).card → False) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → x3.size ≤ (63 : ℕ) → (52 : ℕ) + (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + (PEqualNP.TopForm.Ustar x1 x3).card + (1 : ℕ) → (52 : ℕ) ≤ (4 : ℕ) * (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.Ustar x1 x3).card → (4 : ℕ) * ((PEqualNP.TopForm.junk x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) + (4 : ℕ) ≤ (5 : ℕ) * (PEqualNP.TopForm.Ustar x1 x3).card → False := by
  intro G inst C hG hL hT hJ hs h1 h2 h3
  rcases Nat.lt_or_ge (Ustar G C).card 13 with hlt | hge
  · rcases Nat.lt_or_ge (Ustar G C).card 3 with hdeg | hmid
    · omega
    · exact few G C hG hL hT hJ hs h1 h2 h3 hmid (Nat.lt_succ_iff.1 hlt)
  · exact many G C hG hL hT hJ hs h1 h2 h3 hge
