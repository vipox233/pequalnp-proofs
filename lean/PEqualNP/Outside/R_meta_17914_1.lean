import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17914_1
    (hCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (23 : ℕ) ∧
        C.output < (26 : ℕ) + C.size ∧
        ∀ (S T : Finset (Fin (13 : ℕ))),
          C.eval (List.ofFn fun (k : Fin (26 : ℕ)) =>
            if (k : ℕ) < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ S)
            else Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ T)) = Bool.true ↔
          ∃ p ∈ S, ∃ l ∈ T,
            ((13 : ℕ) * (p : ℕ) + (l : ℕ)) ∈
              [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ), (15 : ℕ), (21 : ℕ), (25 : ℕ),
               (27 : ℕ), (33 : ℕ), (37 : ℕ), (38 : ℕ), (39 : ℕ), (45 : ℕ), (49 : ℕ), (50 : ℕ),
               (81 : ℕ), (85 : ℕ), (86 : ℕ), (88 : ℕ)])
    (hEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        (((13 : ℕ) * (p : ℕ) + (l : ℕ)) ∈
          [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ), (15 : ℕ), (21 : ℕ), (25 : ℕ),
           (27 : ℕ), (33 : ℕ), (37 : ℕ), (38 : ℕ), (39 : ℕ), (45 : ℕ), (49 : ℕ), (50 : ℕ),
           (81 : ℕ), (85 : ℕ), (86 : ℕ), (88 : ℕ)]) ↔
        ((p : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧
          (((p : ℕ) + (l : ℕ)) % (13 : ℕ)) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x5 x4}; have x4 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))}; ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (23 : ℕ) ∧ x5.output < (26 : ℕ) + x5.size ∧ (∀ x6 ∈ x4, ∀ (x8 : Fin (13 : ℕ)), x1 x6 x8 → x5.eval (x2 {x6} {x8}) = Bool.true) ∧ ∀ x6 ⊆ x4, x6 = x4 ∨ x3 x6 ≠ x3 x4 → x5.eval (x2 (x6 ∪ x4ᶜ) (x3 x6)) = Bool.false) := by
  dsimp only
  exact Exists.elim hCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1,
      fun p hp l hpl =>
        (hC.2.2.2 {p} {l}).mpr
          ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l,
            (hEquiv p l).mpr
              ⟨Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.head _) fun hp =>
               Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.tail _ (List.Mem.head _)) fun hp =>
               Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) fun hp =>
               Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) fun hp =>
               (Finset.mem_singleton.mp hp) ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
               hpl⟩⟩,
      fun S _ _ =>
        Bool.eq_false_iff.mpr fun ht =>
          Exists.elim ((hC.2.2.2 (S ∪ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))ᶜ) _).mp ht) fun p hp =>
            Exists.elim hp.2 fun l hl =>
              let hpair := (hEquiv p l).mp hl.2
              have hp4 : p ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) :=
                Or.elim (List.mem_cons.mp hpair.1) (fun h => Finset.mem_insert.mpr (Or.inl (Fin.ext h))) fun hp1 =>
                Or.elim (List.mem_cons.mp hp1) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))) fun hp2 =>
                Or.elim (List.mem_cons.mp hp2) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))))) fun hp3 =>
                Or.elim (List.mem_cons.mp hp3) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))))))) fun hp4 =>
                Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext (List.mem_singleton.mp hp4))))))))))
              have hpS : p ∈ S :=
                Or.elim (Finset.mem_union.mp hp.1) (fun h => h)
                  (fun h => False.elim ((Finset.mem_compl.mp h) hp4))
              ((Finset.mem_filter.mp hl.1).2 p hpS) hpair.2⟩
