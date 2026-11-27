import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18500_1
    (hCircuit :
      ∃ (g : List (Bool × ℕ × ℕ)) (o1 o2 : ℕ),
        g.length ≤ (61 : ℕ) ∧
        o1 < (25 : ℕ) + g.length ∧
        o2 < (25 : ℕ) + g.length ∧
        ∀ (p : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))),
          have w : List Bool :=
            List.foldl (fun (ws : List Bool) (t : Bool × ℕ × ℕ) =>
              ws.concat (if t.1 = Bool.true then ws.getD t.2.1 Bool.false && ws.getD t.2.2 Bool.false else ws.getD t.2.1 Bool.false || ws.getD t.2.2 Bool.false))
              (List.ofFn fun (i : Fin (25 : ℕ)) =>
                if (i : ℕ) < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) + (1 : ℕ)) ∈ p.1)
                else Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) - (12 : ℕ)) ∈ p.2)) g;
          have P4 : Prop := ∃ a ∈ p.1, a ≠ (0 : Fin (13 : ℕ)) ∧ ∃ b ∈ p.2,
            a + b = (0 : Fin (13 : ℕ)) ∨ a + b = (1 : Fin (13 : ℕ)) ∨ a + b = (3 : Fin (13 : ℕ)) ∨ a + b = (9 : Fin (13 : ℕ));
          have P5 : Prop := ∃ b ∈ p.2,
            b = (0 : Fin (13 : ℕ)) ∨ b = (1 : Fin (13 : ℕ)) ∨ b = (3 : Fin (13 : ℕ)) ∨ b = (9 : Fin (13 : ℕ));
          (w.getD o1 Bool.false = Bool.true ↔ P4) ∧
          (P5 → ¬P4 → w.getD o2 Bool.false = Bool.true) ∧
          (w.getD o2 Bool.false = Bool.true → P5 ∨ P4))
    (hEvalSound :
      ∀ (g : List (Bool × ℕ × ℕ)) (k : ℕ) (p : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))),
        (p ∈ (List.foldl (fun (ws : List (Set (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))))) (t : Bool × ℕ × ℕ) =>
          ws.concat (if t.1 = Bool.true then ws.getD t.2.1 ∅ ∩ ws.getD t.2.2 ∅ else ws.getD t.2.1 ∅ ∪ ws.getD t.2.2 ∅))
          (List.ofFn fun (i : Fin (25 : ℕ)) =>
            {q : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) |
              if (i : ℕ) < (12 : ℕ) then Fin.ofNat (13 : ℕ) ((i : ℕ) + (1 : ℕ)) ∈ q.1
              else Fin.ofNat (13 : ℕ) ((i : ℕ) - (12 : ℕ)) ∈ q.2}) g).getD k ∅) ↔
        ((List.foldl (fun (ws : List Bool) (t : Bool × ℕ × ℕ) =>
          ws.concat (if t.1 = Bool.true then ws.getD t.2.1 Bool.false && ws.getD t.2.2 Bool.false else ws.getD t.2.1 Bool.false || ws.getD t.2.2 Bool.false))
          (List.ofFn fun (i : Fin (25 : ℕ)) =>
            if (i : ℕ) < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) + (1 : ℕ)) ∈ p.1)
            else Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) - (12 : ℕ)) ∈ p.2)) g).getD k Bool.false = Bool.true)) :
    (let x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : Fin (25 : ℕ) → Set x1 := fun (x3 : Fin (25 : ℕ)) => {x4 : x1 | if ↑x3 < (12 : ℕ) then Fin.ofNat (13 : ℕ) (↑x3 + (1 : ℕ)) ∈ x4.1 else Fin.ofNat (13 : ℕ) (↑x3 - (12 : ℕ)) ∈ x4.2}; have x4 : Set x1 := {x4 : x1 | ∃ x5 ∈ x4.1, x5 ≠ (0 : Fin (13 : ℕ)) ∧ ∃ x6 ∈ x4.2, x5 + x6 ∈ x2}; have x5 : Set x1 := {x5 : x1 | ∃ x6 ∈ x5.2, x6 ∈ x2}; ∃ (x6 : List (Bool × ℕ × ℕ)) (x7 : ℕ) (x8 : ℕ),   have x9 : List (Set x1) := List.foldl (fun (x9 : List (Set x1)) (x10 : Bool × ℕ × ℕ) => x9.concat (if x10.1 = Bool.true then x9.getD x10.2.1 ∅ ∩ x9.getD x10.2.2 ∅ else x9.getD x10.2.1 ∅ ∪ x9.getD x10.2.2 ∅)) (List.ofFn x3) x6;   x6.length ≤ (61 : ℕ) ∧ x7 < (25 : ℕ) + x6.length ∧ x8 < (25 : ℕ) + x6.length ∧ x9.getD x7 ∅ = x4 ∧ x5 \ x4 ⊆ x9.getD x8 ∅ ∧ x9.getD x8 ∅ ⊆ x5 ∪ x4) := by
  dsimp only
  let mem2_to : ∀ {z : Fin (13 : ℕ)}, z ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) → (z = (0 : Fin (13 : ℕ)) ∨ z = (1 : Fin (13 : ℕ)) ∨ z = (3 : Fin (13 : ℕ)) ∨ z = (9 : Fin (13 : ℕ))) := fun h =>
    Or.elim (Finset.mem_insert.mp h) Or.inl fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => Or.inr (Or.inl h)) fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => Or.inr (Or.inr (Or.inl h))) fun h =>
    Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h)))
  let mem2_of : ∀ {z : Fin (13 : ℕ)}, (z = (0 : Fin (13 : ℕ)) ∨ z = (1 : Fin (13 : ℕ)) ∨ z = (3 : Fin (13 : ℕ)) ∨ z = (9 : Fin (13 : ℕ))) → z ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := fun h =>
    Or.elim h (fun h => Finset.mem_insert.mpr (Or.inl h)) fun h =>
    Or.elim h (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))) fun h =>
    Or.elim h (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))))) fun h =>
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))))
  let h4_iff : ∀ (p : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))),
      (∃ a ∈ p.1, a ≠ (0 : Fin (13 : ℕ)) ∧ ∃ b ∈ p.2, a + b = (0 : Fin (13 : ℕ)) ∨ a + b = (1 : Fin (13 : ℕ)) ∨ a + b = (3 : Fin (13 : ℕ)) ∨ a + b = (9 : Fin (13 : ℕ))) ↔
      (∃ a ∈ p.1, a ≠ (0 : Fin (13 : ℕ)) ∧ ∃ b ∈ p.2, a + b ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := fun p =>
    ⟨fun h => Exists.elim h fun a ha => ⟨a, ha.1, ha.2.1, Exists.elim ha.2.2 fun b hb => ⟨b, hb.1, mem2_of hb.2⟩⟩,
     fun h => Exists.elim h fun a ha => ⟨a, ha.1, ha.2.1, Exists.elim ha.2.2 fun b hb => ⟨b, hb.1, mem2_to hb.2⟩⟩⟩
  let h5_iff : ∀ (p : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))),
      (∃ b ∈ p.2, b = (0 : Fin (13 : ℕ)) ∨ b = (1 : Fin (13 : ℕ)) ∨ b = (3 : Fin (13 : ℕ)) ∨ b = (9 : Fin (13 : ℕ))) ↔
      (∃ b ∈ p.2, b ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := fun p =>
    ⟨fun h => Exists.elim h fun b hb => ⟨b, hb.1, mem2_of hb.2⟩,
     fun h => Exists.elim h fun b hb => ⟨b, hb.1, mem2_to hb.2⟩⟩
  exact Exists.elim hCircuit fun g hg => Exists.elim hg fun o1 ho1 => Exists.elim ho1 fun o2 h =>
    ⟨g, o1, o2, h.1, h.2.1, h.2.2.1,
      Set.ext fun p => Iff.trans (hEvalSound g o1 p) (Iff.trans (h.2.2.2 p).1 (h4_iff p)),
      fun p hp => (hEvalSound g o2 p).mpr ((h.2.2.2 p).2.1 ((h5_iff p).mpr hp.1) (fun h4 => hp.2 ((h4_iff p).mp h4))),
      fun p hp => Or.elim ((h.2.2.2 p).2.2 ((hEvalSound g o2 p).mp hp))
        (fun h5 => Or.inl ((h5_iff p).mp h5))
        (fun h4 => Or.inr ((h4_iff p).mp h4))⟩
