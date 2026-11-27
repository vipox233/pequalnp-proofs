import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18133_1
    (hLow512 :
      have x1 : ℕ → ℕ × ℕ := fun (x1 : ℕ) => ((9756579394148765952 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ), (11071986058226140329 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ));
      let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map x1 (List.range (16 : ℕ)));
      have x3 : List ℕ := [(9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9838263503687778304 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ), (12297791852880363648 : ℕ)];
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x2 x4 →
        PEqualNP.TopForm.TopForm x2 x4 →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;
        x4.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (4 : ℕ) ≤ x7.card → x8 < (2 : ℕ) * x7.card →
        ∀ x13 < (512 : ℕ), (x3.getD (x13 / (64 : ℕ)) (0 : ℕ)).testBit (x13 % (64 : ℕ)) = Bool.true →
        (∀ x16 < (16 : ℕ), (x13 + (1024 : ℕ)).testBit (x1 x16).1 = Bool.true → (x13 + (1024 : ℕ)).testBit (x1 x16).2 = Bool.true → s(Fin.ofNat (11 : ℕ) (x1 x16).1, Fin.ofNat (11 : ℕ) (x1 x16).2) ∈ x7) →
        x7.card + (List.filter (fun (x17 : ℕ) => (x13 + (1024 : ℕ)).testBit x17) (List.range (11 : ℕ))).length ≤ x8 + (4 : ℕ))
    (hHigh512 :
      have x1 : ℕ → ℕ × ℕ := fun (x1 : ℕ) => ((9756579394148765952 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ), (11071986058226140329 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ));
      let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map x1 (List.range (16 : ℕ)));
      have x3 : List ℕ := [(14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14757395258765525184 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ), (18446687779320545472 : ℕ)];
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x2 x4 →
        PEqualNP.TopForm.TopForm x2 x4 →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;
        x4.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (4 : ℕ) ≤ x7.card → x8 < (2 : ℕ) * x7.card →
        ∀ x13 < (512 : ℕ), (x3.getD (x13 / (64 : ℕ)) (0 : ℕ)).testBit (x13 % (64 : ℕ)) = Bool.true →
        (∀ x16 < (16 : ℕ), (x13 + (1536 : ℕ)).testBit (x1 x16).1 = Bool.true → (x13 + (1536 : ℕ)).testBit (x1 x16).2 = Bool.true → s(Fin.ofNat (11 : ℕ) (x1 x16).1, Fin.ofNat (11 : ℕ) (x1 x16).2) ∈ x7) →
        x7.card + (List.filter (fun (x17 : ℕ) => (x13 + (1536 : ℕ)).testBit x17) (List.range (11 : ℕ))).length ≤ x8 + (4 : ℕ)) :
    have x1 : ℕ → ℕ × ℕ := fun (x1 : ℕ) => ((9756579394148765952 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ), (11071986058226140329 : ℕ) >>> ((4 : ℕ) * x1) % (16 : ℕ)); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map x1 (List.range (16 : ℕ))); have x3 : List ℕ := [(9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9838263503687778304 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ), (12297791852880363648 : ℕ), (14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14757395258765525184 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ), (18446687779320545472 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x2 x4 →     PEqualNP.TopForm.TopForm x2 x4 →       have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;       have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;       x4.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (4 : ℕ) ≤ x7.card → x8 < (2 : ℕ) * x7.card → ∀ x13 < (1024 : ℕ), (x3.getD (x13 / (64 : ℕ)) (0 : ℕ)).testBit (x13 % (64 : ℕ)) = Bool.true → (∀ x16 < (16 : ℕ), (x13 + (1024 : ℕ)).testBit (x1 x16).1 = Bool.true → (x13 + (1024 : ℕ)).testBit (x1 x16).2 = Bool.true → s(Fin.ofNat (11 : ℕ) (x1 x16).1, Fin.ofNat (11 : ℕ) (x1 x16).2) ∈ x7) → x7.card + (List.filter (fun (x17 : ℕ) => (x13 + (1024 : ℕ)).testBit x17) (List.range (11 : ℕ))).length ≤ x8 + (4 : ℕ) := by
  intro x1 x2 x3 x4 hL hT x7 x8 hSz hJ hU h8 x13 h13 hBit hEdges
  rcases Nat.lt_or_ge x13 512 with hlo | hhi
  · have hq : x13 / 64 = 0 ∨ x13 / 64 = 1 ∨ x13 / 64 = 2 ∨ x13 / 64 = 3 ∨
              x13 / 64 = 4 ∨ x13 / 64 = 5 ∨ x13 / 64 = 6 ∨ x13 / 64 = 7 := by omega
    have hget : x3.getD (x13 / 64) 0 =
        ([(9799982322739576832 : ℕ), (9799982322739576832 : ℕ), (9799982322739576832 : ℕ),
          (9838263503687778304 : ℕ), (12249940522713513984 : ℕ), (12249940522713513984 : ℕ),
          (12249940522713513984 : ℕ), (12297791852880363648 : ℕ)] : List ℕ).getD (x13 / 64) 0 := by
      rcases hq with h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
    rw [hget] at hBit
    exact hLow512 x4 hL hT hSz hJ hU h8 x13 hlo hBit hEdges
  · set k := x13 - 512 with hk
    have hklt : k < 512 := by omega
    have hkeq : k + 1536 = x13 + 1024 := by omega
    have hdiv : x13 / 64 = k / 64 + 8 := by omega
    have hmod : x13 % 64 = k % 64 := by omega
    have hq : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
              k / 64 = 4 ∨ k / 64 = 5 ∨ k / 64 = 6 ∨ k / 64 = 7 := by omega
    have hget : x3.getD (x13 / 64) 0 =
        ([(14699973487330639872 : ℕ), (14699973487330639872 : ℕ), (14699973487330639872 : ℕ),
          (14757395258765525184 : ℕ), (18374910784070270976 : ℕ), (18374910784070270976 : ℕ),
          (18374910784070270976 : ℕ), (18446687779320545472 : ℕ)] : List ℕ).getD (k / 64) 0 := by
      rw [hdiv]; rcases hq with h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
    rw [hget, hmod] at hBit
    have hres := hHigh512 x4 hL hT hSz hJ hU h8 k hklt hBit (by rw [hkeq]; exact hEdges)
    rw [← hkeq]
    exact hres
