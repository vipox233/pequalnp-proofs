import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17138_2
    (hSingerMem :
      ∀ (p l : Fin (13 : ℕ)),
        (p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ))) ↔
        p ∈ PEqualNP.HeptadCover.singerLines3 l)
    (hSinger64 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C →
        (∀ (Q : Finset (Fin (13 : ℕ))),
          PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
          C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = Bool.false) →
        (64 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x4 x5 : Fin (13 : ℕ)), x4 - x5 = (0 : Fin (13 : ℕ)) ∨ x4 - x5 = (1 : Fin (13 : ℕ)) ∨ x4 - x5 = (3 : Fin (13 : ℕ)) ∨ x4 - x5 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 = x4)) ++ List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 = x5)) = Bool.true) → (∀ (x5 : Finset (Fin (13 : ℕ))), x5.card = (4 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x5 | x8 - x7 = (0 : Fin (13 : ℕ)) ∨ x8 - x7 = (1 : Fin (13 : ℕ)) ∨ x8 - x7 = (3 : Fin (13 : ℕ)) ∨ x8 - x7 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (∀ x9 ∈ x5, ¬(x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro x1 hmono hrb htrue hfalse
  have hInc : ∀ (X Y : Finset (Fin (13 : ℕ))),
      PEqualNP.GenericRejection.incidenceInput X Y =
      (List.ofFn fun (p : Fin (13 : ℕ)) => Decidable.decide (p ∈ X)) ++
      List.ofFn (fun (l : Fin (13 : ℕ)) => Decidable.decide (l ∈ Y)) := fun _ _ => rfl
  have hMiss : ∀ (S : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (Q : Finset (Fin (13 : ℕ))) (l : Fin (13 : ℕ)),
      l ∈ PEqualNP.HeptadCover.missLines S Q ↔ Disjoint (S l) Q := by
    intro S Q l
    change l ∈ Finset.univ.filter (fun l' => Disjoint (S l') Q) ↔ Disjoint (S l) Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hRight : PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x1 := by
    intro l p hp
    have hIn :
        PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin (13 : ℕ))) ({l} : Finset (Fin (13 : ℕ))) =
        (List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 = p)) ++
        List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 = l) := by
      rw [hInc]
      exact congrArg₂ (· ++ ·)
        (congrArg List.ofFn (funext fun k => decide_eq_decide.mpr Finset.mem_singleton))
        (congrArg List.ofFn (funext fun k => decide_eq_decide.mpr Finset.mem_singleton))
    rw [hIn]
    exact htrue p l ((hSingerMem p l).mpr hp)
  have hQuadFalse :
      ∀ (Q : Finset (Fin (13 : ℕ))),
        PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
        x1.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = Bool.false := by
    intro Q hQ
    obtain ⟨hcard, hsec⟩ := hQ
    have hsec' :
        ∀ (x7 : Fin (13 : ℕ)),
          {x8 ∈ Q | x8 - x7 = (0 : Fin (13 : ℕ)) ∨ x8 - x7 = (1 : Fin (13 : ℕ)) ∨ x8 - x7 = (3 : Fin (13 : ℕ)) ∨ x8 - x7 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ) := by
      intro l
      have hEq :
          {x8 ∈ Q | x8 - l = (0 : Fin (13 : ℕ)) ∨ x8 - l = (1 : Fin (13 : ℕ)) ∨ x8 - l = (3 : Fin (13 : ℕ)) ∨ x8 - l = (9 : Fin (13 : ℕ))} =
          Q ∩ PEqualNP.HeptadCover.singerLines3 l := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_inter, hSingerMem p l]
      rw [hEq]
      exact hsec l
    have hIn :
        PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) =
        (List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ Q)) ++
        List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (∀ x9 ∈ Q, ¬(x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ)))) := by
      rw [hInc]
      refine congrArg₂ (· ++ ·)
        (congrArg List.ofFn (funext fun p => decide_eq_decide.mpr Iff.rfl))
        (congrArg List.ofFn (funext fun l => decide_eq_decide.mpr ?_))
      rw [hMiss, Finset.disjoint_right]
      constructor
      · intro h p hp hdiff
        exact h hp ((hSingerMem p l).mp hdiff)
      · intro h p hp hmem
        exact h p hp ((hSingerMem p l).mpr hmem)
    rw [hIn]
    exact hfalse Q hcard hsec'
  exact hSinger64 x1 hmono hrb hRight hQuadFalse
