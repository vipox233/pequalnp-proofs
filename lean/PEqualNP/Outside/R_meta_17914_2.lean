import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17914_2
    (hFullCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (23 : ℕ) ∧
        C.output < (26 : ℕ) + C.size ∧
        ∀ (v : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn v) = Bool.true ↔
          ∃ (i : Fin (5 : ℕ)) (l : Fin (13 : ℕ)),
            ([(523 : ℕ), (4357 : ℕ), (6274 : ℕ), (3137 : ℕ), (1416 : ℕ)].getD (i : ℕ) (0 : ℕ)).testBit (l : ℕ) = Bool.true ∧
            v (Fin.castAdd (13 : ℕ) (Fin.ofNat (13 : ℕ) ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)].getD (i : ℕ) (0 : ℕ)))) = Bool.true ∧
            v (Fin.natAdd (13 : ℕ) l) = Bool.true)
    (hRowEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        ((p : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧
          (((p : ℕ) + (l : ℕ)) % (13 : ℕ)) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ↔
        ∃ (i : Fin (5 : ℕ)),
          ([(523 : ℕ), (4357 : ℕ), (6274 : ℕ), (3137 : ℕ), (1416 : ℕ)].getD (i : ℕ) (0 : ℕ)).testBit (l : ℕ) = Bool.true ∧
          p = Fin.ofNat (13 : ℕ) ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)].getD (i : ℕ) (0 : ℕ))) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x5 x4}; have x4 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))}; ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (23 : ℕ) ∧ x5.output < (26 : ℕ) + x5.size ∧ (∀ x6 ∈ x4, ∀ (x8 : Fin (13 : ℕ)), x1 x6 x8 → x5.eval (x2 {x6} {x8}) = Bool.true) ∧ ∀ x6 ⊆ x4, x6 = x4 ∨ x3 x6 ≠ x3 x4 → x5.eval (x2 (x6 ∪ x4ᶜ) (x3 x6)) = Bool.false) := by
  dsimp only
  let v : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun S T k =>
    if (k : ℕ) < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ S)
    else Decidable.decide (Fin.ofNat (13 : ℕ) (k : ℕ) ∈ T)
  have hvL : ∀ (S T : Finset (Fin (13 : ℕ))) (p : Fin (13 : ℕ)),
      v S T (Fin.castAdd (13 : ℕ) p) = Decidable.decide (p ∈ S) := fun S T p =>
    Eq.trans (if_pos p.isLt)
      (congrArg (fun q => Decidable.decide (q ∈ S)) (Fin.ext (Nat.mod_eq_of_lt p.isLt)))
  have hvR : ∀ (S T : Finset (Fin (13 : ℕ))) (l : Fin (13 : ℕ)),
      v S T (Fin.natAdd (13 : ℕ) l) = Decidable.decide (l ∈ T) := fun S T l =>
    Eq.trans (if_neg (Nat.not_lt.mpr (Nat.le_add_right (13 : ℕ) (l : ℕ))))
      (congrArg (fun q => Decidable.decide (q ∈ T))
        (Fin.ext (Eq.trans (Nat.add_mod_left (13 : ℕ) (l : ℕ)) (Nat.mod_eq_of_lt l.isLt))))
  let hmem4_to : ∀ {p : Fin (13 : ℕ)},
      p ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) →
      (p : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] := fun hp =>
    Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.head _) fun hp =>
    Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.tail _ (List.Mem.head _)) fun hp =>
    Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) fun hp =>
    Or.elim (Finset.mem_insert.mp hp) (fun h => h ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) fun hp =>
    (Finset.mem_singleton.mp hp) ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  let hmem4_of : ∀ {p : Fin (13 : ℕ)},
      (p : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] →
      p ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := fun hp =>
    Or.elim (List.mem_cons.mp hp) (fun h => Finset.mem_insert.mpr (Or.inl (Fin.ext h))) fun hp1 =>
    Or.elim (List.mem_cons.mp hp1) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))) fun hp2 =>
    Or.elim (List.mem_cons.mp hp2) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))))) fun hp3 =>
    Or.elim (List.mem_cons.mp hp3) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))))))) fun hp4 =>
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext (List.mem_singleton.mp hp4))))))))))
  exact Exists.elim hFullCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1,
      fun p hp l hpl =>
        Exists.elim ((hRowEquiv p l).mp ⟨hmem4_to hp, hpl⟩) fun i hi =>
          (hC.2.2.2 (v {p} {l})).mpr
            ⟨i, l, hi.1,
              Eq.trans (hvL {p} {l} _) (decide_eq_true (Finset.mem_singleton.mpr hi.2.symm)),
              Eq.trans (hvR {p} {l} l) (decide_eq_true (Finset.mem_singleton_self l))⟩,
      fun S _ _ =>
        Bool.eq_false_iff.mpr fun ht =>
          Exists.elim ((hC.2.2.2 (v (S ∪ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))ᶜ) _)).mp ht) fun i hi =>
            Exists.elim hi fun l hl =>
              let p := Fin.ofNat (13 : ℕ) ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)].getD (i : ℕ) (0 : ℕ))
              let hp_in := of_decide_eq_true (Eq.trans (hvL _ _ p).symm hl.2.1)
              let hl_in := of_decide_eq_true (Eq.trans (hvR _ _ l).symm hl.2.2)
              let hpair := (hRowEquiv p l).mpr ⟨i, hl.1, rfl⟩
              have hpS : p ∈ S :=
                Or.elim (Finset.mem_union.mp hp_in) (fun h => h)
                  (fun h => False.elim ((Finset.mem_compl.mp h) (hmem4_of hpair.1)))
              ((Finset.mem_filter.mp hl_in).2 p hpS) hpair.2⟩
