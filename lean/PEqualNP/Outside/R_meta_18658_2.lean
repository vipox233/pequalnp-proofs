import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18658_2
    (hOrNonLamGe2 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        PEqualNP.TopForm.junk x1 x3 = {x4, x5} →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
        x3.size ≤ (21 : ℕ) →
        have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;
        have x14 : ℕ := (2 : ℕ) * x13.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;
        (4 : ℕ) ≤ x12.card →
        (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card →
        (3 : ℕ) + x14 ≤ (2 : ℕ) * x12.card →
        (PEqualNP.TopForm.tops x1 x3 \ x13).card + x14 ≤ (4 : ℕ) + x12.card →
        (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x12 →
          (∀ (b : Fin (2 : ℕ)), u ∈ PEqualNP.TopForm.side x3 x4 b ∨ v ∈ PEqualNP.TopForm.side x3 x4 b) ∨
          (∀ (b : Fin (2 : ℕ)), u ∈ PEqualNP.TopForm.side x3 x5 b ∨ v ∈ PEqualNP.TopForm.side x3 x5 b)) →
        False)
    (hOrNonLamEq1 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        PEqualNP.TopForm.junk x1 x3 = {x4, x5} →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
        x3.size ≤ (21 : ℕ) →
        have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;
        (4 : ℕ) ≤ x12.card →
        (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card = (1 : ℕ) →
        (0 : ℕ) < x13.card →
        (2 : ℕ) + x13.card ≤ x12.card →
        (PEqualNP.TopForm.tops x1 x3 \ x13).card + (2 : ℕ) * x13.card ≤ (3 : ℕ) + x12.card →
        (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x12 →
          (∀ (b : Fin (2 : ℕ)), u ∈ PEqualNP.TopForm.side x3 x4 b ∨ v ∈ PEqualNP.TopForm.side x3 x4 b) ∨
          (∀ (b : Fin (2 : ℕ)), u ∈ PEqualNP.TopForm.side x3 x5 b ∨ v ∈ PEqualNP.TopForm.side x3 x5 b)) →
        False) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             x3.size < (22 : ℕ) →               have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;               have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;               have x14 : ℕ := (2 : ℕ) * x13.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;               (4 : ℕ) ≤ x12.card → (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ∨ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card = (1 : ℕ) ∧ (0 : ℕ) < x13.card → (3 : ℕ) + x14 ≤ (2 : ℕ) * x12.card → (PEqualNP.TopForm.tops x1 x3 \ x13).card + x14 ≤ (4 : ℕ) + x12.card → (∀ (x19 x20 : Fin (11 : ℕ)), s(x19, x20) ∈ x12 → ∃ x22 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x23 : Fin (2 : ℕ)), x19 ∈ PEqualNP.TopForm.side x3 x22 x23 ∨ x20 ∈ PEqualNP.TopForm.side x3 x22 x23) → False) := by
  intro x1 x2 x3 x4 x5 hEqG hLeast hTF hJunk hIC hSz x12 x13 x14 hU4 hDisj hIneq1 hIneq2 hCov
  subst hEqG
  have hDec : x2 = (by clear x2 hLeast hTF hJunk hIC hSz x12 x13 x14 hU4 hDisj hIneq1 hIneq2 hCov; infer_instance) :=
    Subsingleton.elim _ _
  subst hDec
  have hCov' : ∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x12 →
      (∀ (b : Fin (2 : ℕ)), u ∈ PEqualNP.TopForm.side x3 x4 b ∨ v ∈ PEqualNP.TopForm.side x3 x4 b) ∨
      (∀ (b : Fin (2 : ℕ)), u ∈ PEqualNP.TopForm.side x3 x5 b ∨ v ∈ PEqualNP.TopForm.side x3 x5 b) := by
    intro u v huv
    exact Exists.elim (hCov u v huv) fun g hg => by
      have hg1 : g ∈ ({x4, x5} : Finset ℕ) := by rw [← hJunk]; exact hg.1
      exact Or.elim (Finset.mem_insert.mp hg1)
        (fun h4 => by subst h4; exact Or.inl hg.2)
        (fun h5 => by have h5' := Finset.mem_singleton.mp h5; subst h5'; exact Or.inr hg.2)
  exact Or.elim hDisj
    (fun hGe2 =>
      hOrNonLamGe2 x3 x4 x5 hLeast hTF hJunk hIC (Nat.le_of_lt_succ hSz) hU4 hGe2 hIneq1 hIneq2 hCov')
    (fun hEq1 =>
      hOrNonLamEq1 x3 x4 x5 hLeast hTF hJunk hIC (Nat.le_of_lt_succ hSz) hU4 hEq1.1 hEq1.2
        (by have h := hIneq1; dsimp only [x12, x13, x14] at h; rw [hEq1.1] at h; omega)
        (by have h := hIneq2; dsimp only [x12, x13, x14] at h; rw [hEq1.1] at h; omega)
        hCov')
