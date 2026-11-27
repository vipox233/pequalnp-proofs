import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18763_2
    (hMonoSound :
      ∀ (adj : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop) (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        let wv := PEqualNP.BlindGate.wireValue x1 (26 : ℕ)
        (∀ (u v : Fin (13 : ℕ)), adj u v → wv (fun k => Decidable.decide (k = Fin.castAdd (13 : ℕ) u ∨ k = Fin.natAdd (13 : ℕ) v)) x2 = Bool.true) →
        (∀ (x4 : Fin (26 : ℕ) → Bool), (¬∃ (u v : Fin (13 : ℕ)), adj u v ∧ x4 (Fin.castAdd (13 : ℕ) u) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) v) = Bool.true) → wv x4 x2 = Bool.false) →
        (∀ (k : Fin (26 : ℕ)), k.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] → wv (fun j => Decidable.decide (j = k)) x3 = Bool.true) →
        (∀ (x4 : Fin (26 : ℕ) → Bool), x4 (0 : Fin (26 : ℕ)) = Bool.false → x4 (1 : Fin (26 : ℕ)) = Bool.false → x4 (3 : Fin (26 : ℕ)) = Bool.false → x4 (9 : Fin (26 : ℕ)) = Bool.false → wv x4 x3 = Bool.false) →
        ∀ (x4 : Fin (26 : ℕ) → Bool),
          (wv x4 x2 = Bool.true ↔ ∃ (u v : Fin (13 : ℕ)), adj u v ∧ x4 (Fin.castAdd (13 : ℕ) u) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) v) = Bool.true) ∧
          wv x4 x3 = (x4 (0 : Fin (26 : ℕ)) || x4 (1 : Fin (26 : ℕ)) || x4 (3 : Fin (26 : ℕ)) || x4 (9 : Fin (26 : ℕ))))
    (hEdgeTests :
      let adj : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun u v => v ≠ (0 : Fin (13 : ℕ)) ∧ (u = v ∨ u = v + (1 : Fin (13 : ℕ)) ∨ u = v + (3 : Fin (13 : ℕ)) ∨ u = v + (9 : Fin (13 : ℕ)))
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),
        x1.size ≤ (61 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
        (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧
        x2 < (26 : ℕ) + x1.size ∧
        x3 < (26 : ℕ) + x1.size ∧
        x2 ≠ x3 ∧
        x2 ≠ (13 : ℕ) ∧
        let wv := PEqualNP.BlindGate.wireValue x1 (26 : ℕ)
        (∀ (u v : Fin (13 : ℕ)), adj u v → wv (fun k => Decidable.decide (k = Fin.castAdd (13 : ℕ) u ∨ k = Fin.natAdd (13 : ℕ) v)) x2 = Bool.true) ∧
        (∀ (x4 : Fin (26 : ℕ) → Bool), (¬∃ (u v : Fin (13 : ℕ)), adj u v ∧ x4 (Fin.castAdd (13 : ℕ) u) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) v) = Bool.true) → wv x4 x2 = Bool.false) ∧
        (∀ (k : Fin (26 : ℕ)), k.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] → wv (fun j => Decidable.decide (j = k)) x3 = Bool.true) ∧
        (∀ (x4 : Fin (26 : ℕ) → Bool), x4 (0 : Fin (26 : ℕ)) = Bool.false → x4 (1 : Fin (26 : ℕ)) = Bool.false → x4 (3 : Fin (26 : ℕ)) = Bool.false → x4 (9 : Fin (26 : ℕ)) = Bool.false → wv x4 x3 = Bool.false)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ), x1.size ≤ (61 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧ x2 < (26 : ℕ) + x1.size ∧ x3 < (26 : ℕ) + x1.size ∧ x2 ≠ x3 ∧ x2 ≠ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x2 = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x6 ≠ (0 : Fin (13 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x3 = (x4 (0 : Fin (26 : ℕ)) || x4 (1 : Fin (26 : ℕ)) || x4 (3 : Fin (26 : ℕ)) || x4 (9 : Fin (26 : ℕ)))) :=
  Exists.elim hEdgeTests fun x1 h1 =>
    Exists.elim h1 fun x2 h2 =>
      Exists.elim h2 fun x3 h =>
        let hFull := hMonoSound _ x1 x2 x3 h.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2
        ⟨x1, x2, x3, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
          fun x4 => ⟨(hFull x4).1.trans (exists_congr fun x5 => exists_congr fun x6 => and_assoc), (hFull x4).2⟩⟩
