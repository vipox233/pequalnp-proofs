import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7788_2 :
    (∀ (u v : Fin (26 : ℕ)),
      (∃ (p l : Fin (13 : ℕ)), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
        (u = Fin.castAdd (13 : ℕ) p ∧ v = Fin.natAdd (13 : ℕ) l ∨
         v = Fin.castAdd (13 : ℕ) p ∧ u = Fin.natAdd (13 : ℕ) l)) →
      u ≠ v ∧
      ((u.val < (13 : ℕ) ∧ (13 : ℕ) ≤ v.val) ∨ (v.val < (13 : ℕ) ∧ (13 : ℕ) ≤ u.val)) ∧
      ∃ (p l : Fin (13 : ℕ)), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
        (v = Fin.castAdd (13 : ℕ) p ∧ u = Fin.natAdd (13 : ℕ) l ∨
         u = Fin.castAdd (13 : ℕ) p ∧ v = Fin.natAdd (13 : ℕ) l)) →
    (have pairIn : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun u v => List.ofFn fun k : Fin (26 : ℕ) => Decidable.decide (k = u ∨ k = v);
     have wval : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun C w inp => (C.wires inp).getD w Bool.false;
     have nestedAnd : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun C g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs, (26 : ℕ) ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and;
     ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj],
       (∀ (p l : Fin (13 : ℕ)), G.Adj (Fin.castAdd (13 : ℕ) p) (Fin.natAdd (13 : ℕ) l) ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l) →
       (∀ (u v : Fin (26 : ℕ)), G.Adj u v → (u.val < (13 : ℕ) ∧ (13 : ℕ) ≤ v.val) ∨ (v.val < (13 : ℕ) ∧ (13 : ℕ) ≤ u.val)) →
       ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w1 w2 : ℕ) (S : Finset ℕ),
         PEqualNP.MetaComplexity.Monotone2 C →
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
         w1 < (26 : ℕ) + C.size →
         w2 < (26 : ℕ) + C.size →
         (∀ (u v : Fin (26 : ℕ)), (wval C w1 (pairIn u v) || wval C w2 (pairIn u v)) = Decidable.decide (G.Adj u v)) →
         (∃ (u v : Fin (26 : ℕ)), wval C w1 (pairIn u v) = Bool.true ∧ wval C w2 (pairIn u v) = Bool.false) →
         (∃ (u v : Fin (26 : ℕ)), wval C w2 (pairIn u v) = Bool.true ∧ wval C w1 (pairIn u v) = Bool.false) →
         S.card = (2 : ℕ) →
         (∀ (g : ℕ), g ∈ S ↔ g < C.size ∧ nestedAnd C g) →
         (63 : ℕ) ≤ C.size) →
    (let x1 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x1 x2 : Fin (26 : ℕ)) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ (x1 = Fin.castAdd (13 : ℕ) x3 ∧ x2 = Fin.natAdd (13 : ℕ) x4 ∨ x2 = Fin.castAdd (13 : ℕ) x3 ∧ x1 = Fin.natAdd (13 : ℕ) x4); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (x2 x3 : Fin (26 : ℕ)) => List.ofFn fun (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = x2 ∨ x4 = x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) =>   have x7 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;   (x4 x5 x6).op = x7 ∧ ∃ x8 ∈ (x4 x5 x6).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x5 (x8 - (26 : ℕ))).op = x7; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x6 → x7 < (26 : ℕ) + x6.size → x8 < (26 : ℕ) + x6.size → (∀ (x13 x14 : Fin (26 : ℕ)), (x3 x6 x7 (x2 x13 x14) || x3 x6 x8 (x2 x13 x14)) = Decidable.decide (x1 x13 x14)) → (∃ (x14 : Fin (26 : ℕ)) (x15 : Fin (26 : ℕ)), x3 x6 x7 (x2 x14 x15) = Bool.true ∧ x3 x6 x8 (x2 x14 x15) = Bool.false) → (∃ (x15 : Fin (26 : ℕ)) (x16 : Fin (26 : ℕ)), x3 x6 x8 (x2 x15 x16) = Bool.true ∧ x3 x6 x7 (x2 x15 x16) = Bool.false) → (∃ x16 ∈ Finset.range x6.size, ∃ x17 ∈ Finset.range x6.size, x16 ≠ x17 ∧ x5 x6 x16 ∧ x5 x6 x17 ∧ ∀ x18 ∈ Finset.range x6.size, x5 x6 x18 → x18 = x16 ∨ x18 = x17) → (63 : ℕ) ≤ x6.size) := by
  intro hBipGraph hGraphSplit63
  intro x1 x2 x3 x4 x5 x6 x7 x8 hmono hrb hw1 hw2 hor h1only h2only hnested
  let G : SimpleGraph (Fin (26 : ℕ)) :=
    { Adj := x1
      symm := ⟨fun u v h => (hBipGraph u v h).2.2⟩
      loopless := ⟨fun u h => (hBipGraph u u h).1 rfl⟩ }
  letI : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (x1 u v))
  have hAdj : ∀ (p l : Fin (13 : ℕ)),
      G.Adj (Fin.castAdd (13 : ℕ) p) (Fin.natAdd (13 : ℕ) l) ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l :=
    fun p l =>
      Iff.intro
        (fun h =>
          Exists.elim h fun p' h' =>
            Exists.elim h' fun l' h'' =>
              Or.elim h''.2
                (fun hlr =>
                  have h1v : p.val = p'.val := congrArg (fun x : Fin (26 : ℕ) => x.val) hlr.1
                  have h2v : (13 : ℕ) + l.val = (13 : ℕ) + l'.val := congrArg (fun x : Fin (26 : ℕ) => x.val) hlr.2
                  have hp : p = p' := Fin.ext h1v
                  have hl : l = l' := Fin.ext (Nat.add_left_cancel h2v)
                  Eq.subst (motive := fun y => p ∈ PEqualNP.HeptadCover.singerLines3 y) hl.symm
                    (Eq.subst (motive := fun x => x ∈ PEqualNP.HeptadCover.singerLines3 l') hp.symm h''.1))
                (fun hrl =>
                  have h1v : (13 : ℕ) + l.val = p'.val := congrArg (fun x : Fin (26 : ℕ) => x.val) hrl.1
                  False.elim
                    (Nat.not_lt_of_ge (Nat.le_add_right (13 : ℕ) l.val)
                      (Eq.subst (motive := fun k => k < (13 : ℕ)) h1v.symm p'.isLt))))
        (fun h => Exists.intro p (Exists.intro l (And.intro h (Or.inl (And.intro rfl rfl)))))
  have hBip : ∀ (u v : Fin (26 : ℕ)),
      G.Adj u v → (u.val < (13 : ℕ) ∧ (13 : ℕ) ≤ v.val) ∨ (v.val < (13 : ℕ) ∧ (13 : ℕ) ≤ u.val) :=
    fun u v h => (hBipGraph u v h).2.1
  exact Exists.elim hnested fun g1 hg1_all =>
    Exists.elim hg1_all.2 fun g2 hg2_all =>
      let S : Finset ℕ := {g1, g2}
      have hScard : S.card = (2 : ℕ) := Finset.card_pair hg2_all.2.1
      have hSmem : ∀ (g : ℕ), g ∈ S ↔ g < x6.size ∧ x5 x6 g := fun g =>
        Iff.intro
          (fun hg =>
            Or.elim (Finset.mem_insert.mp hg)
              (fun h =>
                Eq.subst (motive := fun k => k < x6.size ∧ x5 x6 k) h.symm
                  (And.intro (Finset.mem_range.mp hg1_all.1) hg2_all.2.2.1))
              (fun hg' =>
                Eq.subst (motive := fun k => k < x6.size ∧ x5 x6 k) (Finset.mem_singleton.mp hg').symm
                  (And.intro (Finset.mem_range.mp hg2_all.1) hg2_all.2.2.2.1)))
          (fun h =>
            Or.elim (hg2_all.2.2.2.2 g (Finset.mem_range.mpr h.1) h.2)
              (fun hg1eq =>
                Eq.subst (motive := fun k => k ∈ S) hg1eq.symm (Finset.mem_insert_self g1 {g2}))
              (fun hg2eq =>
                Eq.subst (motive := fun k => k ∈ S) hg2eq.symm
                  (Finset.mem_insert_of_mem (Finset.mem_singleton_self g2))))
      hGraphSplit63 G hAdj hBip x6 x7 x8 S hmono hrb hw1 hw2 hor h1only h2only hScard hSmem
