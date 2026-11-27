import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18500_3
    (hAO25 :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        PEqualNP.TopForm.IsAO2 (25 : ℕ) C ∧
        C.size ≤ (61 : ℕ) ∧
        C.output < (25 : ℕ) + C.size ∧
        w < (25 : ℕ) + C.size ∧
        ∀ (x : Fin (25 : ℕ) → Bool),
          have P4 : Prop :=
            ∃ (i : Fin (12 : ℕ)) (j : Fin (13 : ℕ)),
              (i.val + (1 : ℕ) + j.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) i) = Bool.true ∧ x (Fin.natAdd (12 : ℕ) j) = Bool.true;
          (C.eval (List.ofFn x) = Bool.true ↔ P4) ∧
          (¬P4 → (C.wires (List.ofFn x)).getD w Bool.false =
            (x (12 : Fin (25 : ℕ)) || x (13 : Fin (25 : ℕ)) || x (15 : Fin (25 : ℕ)) || x (21 : Fin (25 : ℕ)))))
    (hCompileSetDAG :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (25 : ℕ) C →
        ∃ (g : List (Bool × ℕ × ℕ)),
          g.length = C.size ∧
          ∀ (k : ℕ) (p : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))),
            (p ∈ (List.foldl (fun (ws : List (Set (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))))) (t : Bool × ℕ × ℕ) =>
              ws.concat (if t.1 = Bool.true then ws.getD t.2.1 ∅ ∩ ws.getD t.2.2 ∅ else ws.getD t.2.1 ∅ ∪ ws.getD t.2.2 ∅))
              (List.ofFn fun (i : Fin (25 : ℕ)) =>
                {q : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) |
                  if (i : ℕ) < (12 : ℕ) then Fin.ofNat (13 : ℕ) ((i : ℕ) + (1 : ℕ)) ∈ q.1
                  else Fin.ofNat (13 : ℕ) ((i : ℕ) - (12 : ℕ)) ∈ q.2}) g).getD k ∅) ↔
            (C.wires (List.ofFn fun (i : Fin (25 : ℕ)) =>
              if (i : ℕ) < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) + (1 : ℕ)) ∈ p.1)
              else Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) - (12 : ℕ)) ∈ p.2))).getD k Bool.false = Bool.true) :
    (let x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : Fin (25 : ℕ) → Set x1 := fun (x3 : Fin (25 : ℕ)) => {x4 : x1 | if ↑x3 < (12 : ℕ) then Fin.ofNat (13 : ℕ) (↑x3 + (1 : ℕ)) ∈ x4.1 else Fin.ofNat (13 : ℕ) (↑x3 - (12 : ℕ)) ∈ x4.2}; have x4 : Set x1 := {x4 : x1 | ∃ x5 ∈ x4.1, x5 ≠ (0 : Fin (13 : ℕ)) ∧ ∃ x6 ∈ x4.2, x5 + x6 ∈ x2}; have x5 : Set x1 := {x5 : x1 | ∃ x6 ∈ x5.2, x6 ∈ x2}; ∃ (x6 : List (Bool × ℕ × ℕ)) (x7 : ℕ) (x8 : ℕ),   have x9 : List (Set x1) := List.foldl (fun (x9 : List (Set x1)) (x10 : Bool × ℕ × ℕ) => x9.concat (if x10.1 = Bool.true then x9.getD x10.2.1 ∅ ∩ x9.getD x10.2.2 ∅ else x9.getD x10.2.1 ∅ ∪ x9.getD x10.2.2 ∅)) (List.ofFn x3) x6;   x6.length ≤ (61 : ℕ) ∧ x7 < (25 : ℕ) + x6.length ∧ x8 < (25 : ℕ) + x6.length ∧ x9.getD x7 ∅ = x4 ∧ x5 \ x4 ⊆ x9.getD x8 ∅ ∧ x9.getD x8 ∅ ⊆ x5 ∪ x4) := by
  intro x1 x2 x3 x4 x5
  have hPair1 : ∀ (i : Fin (12 : ℕ)) (j : Fin (13 : ℕ)),
      Fin.ofNat (13 : ℕ) (i.val + (1 : ℕ)) ≠ (0 : Fin (13 : ℕ)) ∧
      ((i.val + (1 : ℕ) + j.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔
        Fin.ofNat (13 : ℕ) (i.val + (1 : ℕ)) + j ∈ x2) := by
    decide
  have hPair2 : ∀ (a : Fin (13 : ℕ)), a ≠ (0 : Fin (13 : ℕ)) →
      ∃ (i : Fin (12 : ℕ)), Fin.ofNat (13 : ℕ) (i.val + (1 : ℕ)) = a := by
    decide
  have hJ : ∀ (j : Fin (13 : ℕ)), ¬((Fin.natAdd (12 : ℕ) j).val < (12 : ℕ)) ∧
      Fin.ofNat (13 : ℕ) ((Fin.natAdd (12 : ℕ) j).val - (12 : ℕ)) = j := by
    decide
  have hMemX2 : ∀ (b : Fin (13 : ℕ)), b ∈ x2 ↔
      b = (0 : Fin (13 : ℕ)) ∨ b = (1 : Fin (13 : ℕ)) ∨ b = (3 : Fin (13 : ℕ)) ∨ b = (9 : Fin (13 : ℕ)) := by
    decide
  let enc (p : x1) : Fin (25 : ℕ) → Bool := fun i =>
    if (i : ℕ) < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) + (1 : ℕ)) ∈ p.1)
    else Decidable.decide (Fin.ofNat (13 : ℕ) ((i : ℕ) - (12 : ℕ)) ∈ p.2)
  have hP4Iff : ∀ (p : x1),
      (∃ (i : Fin (12 : ℕ)) (j : Fin (13 : ℕ)),
        (i.val + (1 : ℕ) + j.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
        enc p (Fin.castAdd (13 : ℕ) i) = Bool.true ∧ enc p (Fin.natAdd (12 : ℕ) j) = Bool.true) ↔ p ∈ x4 := by
    intro p
    refine Iff.intro (fun h => ?_) (fun h => ?_)
    · refine Exists.elim h fun i hi => Exists.elim hi fun j hj => ?_
      have hiT : (if i.val < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (i.val + (1 : ℕ)) ∈ p.1)
          else Decidable.decide (Fin.ofNat (13 : ℕ) (i.val - (12 : ℕ)) ∈ p.2)) = Bool.true := hj.2.1
      rw [ite_eq_left i.isLt] at hiT
      have hjT : (if (Fin.natAdd (12 : ℕ) j).val < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ((Fin.natAdd (12 : ℕ) j).val + (1 : ℕ)) ∈ p.1)
          else Decidable.decide (Fin.ofNat (13 : ℕ) ((Fin.natAdd (12 : ℕ) j).val - (12 : ℕ)) ∈ p.2)) = Bool.true := hj.2.2
      rw [ite_eq_right (fun h => False.elim ((hJ j).1 h)), (hJ j).2] at hjT
      exact ⟨Fin.ofNat (13 : ℕ) (i.val + (1 : ℕ)), of_decide_eq_true hiT, (hPair1 i j).1,
        j, of_decide_eq_true hjT, (hPair1 i j).2.mp hj.1⟩
    · refine Exists.elim h fun a ha => Exists.elim ha.2.2 fun b hb => ?_
      refine Exists.elim (hPair2 a ha.2.1) fun i hi => ?_
      refine ⟨i, b, (hPair1 i b).2.mpr (hi.symm ▸ hb.2), ?_, ?_⟩
      · change (if i.val < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (i.val + (1 : ℕ)) ∈ p.1)
          else Decidable.decide (Fin.ofNat (13 : ℕ) (i.val - (12 : ℕ)) ∈ p.2)) = Bool.true
        rw [ite_eq_left i.isLt, hi]
        exact decide_eq_true ha.1
      · change (if (Fin.natAdd (12 : ℕ) b).val < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ((Fin.natAdd (12 : ℕ) b).val + (1 : ℕ)) ∈ p.1)
          else Decidable.decide (Fin.ofNat (13 : ℕ) ((Fin.natAdd (12 : ℕ) b).val - (12 : ℕ)) ∈ p.2)) = Bool.true
        rw [ite_eq_right (fun h => False.elim ((hJ b).1 h)), (hJ b).2]
        exact decide_eq_true hb.1
  refine Exists.elim hAO25 fun C hC => ?_
  refine Exists.elim hC fun w hw => ?_
  refine Exists.elim (hCompileSetDAG C hw.1) fun g hg => ?_
  have hLen : g.length = C.size := hg.1
  refine ⟨g, C.output, w, hLen ▸ hw.2.1, hLen ▸ hw.2.2.1, hLen ▸ hw.2.2.2.1, ?_, ?_, ?_⟩
  · exact Set.ext fun p => Iff.trans (hg.2 C.output p) (Iff.trans (hw.2.2.2.2 (enc p)).1 (hP4Iff p))
  · intro p hp
    have hNotP4 := fun h => hp.2 ((hP4Iff p).mp h)
    refine (hg.2 w p).mpr (Eq.trans ((hw.2.2.2.2 (enc p)).2 hNotP4) ?_)
    refine Exists.elim hp.1 fun b hb => ?_
    refine Or.elim ((hMemX2 b).mp hb.2) (fun h0 => ?_) (fun h => Or.elim h (fun h1 => ?_) (fun h => Or.elim h (fun h3 => ?_) (fun h9 => ?_)))
    · have h12 : enc p (12 : Fin (25 : ℕ)) = Bool.true := by
        change Decidable.decide ((0 : Fin (13 : ℕ)) ∈ p.2) = Bool.true
        exact decide_eq_true (h0 ▸ hb.1)
      rw [h12]; rfl
    · have h13 : enc p (13 : Fin (25 : ℕ)) = Bool.true := by
        change Decidable.decide ((1 : Fin (13 : ℕ)) ∈ p.2) = Bool.true
        exact decide_eq_true (h1 ▸ hb.1)
      rw [h13, Bool.or_true]; rfl
    · have h15 : enc p (15 : Fin (25 : ℕ)) = Bool.true := by
        change Decidable.decide ((3 : Fin (13 : ℕ)) ∈ p.2) = Bool.true
        exact decide_eq_true (h3 ▸ hb.1)
      rw [h15, Bool.or_true]; rfl
    · have h21 : enc p (21 : Fin (25 : ℕ)) = Bool.true := by
        change Decidable.decide ((9 : Fin (13 : ℕ)) ∈ p.2) = Bool.true
        exact decide_eq_true (h9 ▸ hb.1)
      rw [h21, Bool.or_true]
  · intro p hp
    refine Or.elim (Classical.em (p ∈ x4)) Or.inr fun hNot4 => Or.inl ?_
    have hNotP4 := fun h => hNot4 ((hP4Iff p).mp h)
    have hOr : (enc p (12 : Fin (25 : ℕ)) || enc p (13 : Fin (25 : ℕ)) || enc p (15 : Fin (25 : ℕ)) || enc p (21 : Fin (25 : ℕ))) = Bool.true :=
      Eq.trans ((hw.2.2.2.2 (enc p)).2 hNotP4).symm ((hg.2 w p).mp hp)
    refine Or.elim (Bool.or_eq_true _ _ |>.mp hOr) (fun h1 => Or.elim (Bool.or_eq_true _ _ |>.mp h1) (fun h2 => Or.elim (Bool.or_eq_true _ _ |>.mp h2) (fun h12 => ?_) (fun h13 => ?_)) (fun h15 => ?_)) (fun h21 => ?_)
    · change Decidable.decide ((0 : Fin (13 : ℕ)) ∈ p.2) = Bool.true at h12
      exact ⟨(0 : Fin (13 : ℕ)), of_decide_eq_true h12, (hMemX2 (0 : Fin (13 : ℕ))).mpr (Or.inl rfl)⟩
    · change Decidable.decide ((1 : Fin (13 : ℕ)) ∈ p.2) = Bool.true at h13
      exact ⟨(1 : Fin (13 : ℕ)), of_decide_eq_true h13, (hMemX2 (1 : Fin (13 : ℕ))).mpr (Or.inr (Or.inl rfl))⟩
    · change Decidable.decide ((3 : Fin (13 : ℕ)) ∈ p.2) = Bool.true at h15
      exact ⟨(3 : Fin (13 : ℕ)), of_decide_eq_true h15, (hMemX2 (3 : Fin (13 : ℕ))).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · change Decidable.decide ((9 : Fin (13 : ℕ)) ∈ p.2) = Bool.true at h21
      exact ⟨(9 : Fin (13 : ℕ)), of_decide_eq_true h21, (hMemX2 (9 : Fin (13 : ℕ))).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩
