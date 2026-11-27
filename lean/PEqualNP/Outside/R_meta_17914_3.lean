import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17914_3
    (hStarCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (23 : ℕ) ∧
        C.output < (26 : ℕ) + C.size ∧
        ∀ (x : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn x) = ((x (0 : Fin (26 : ℕ)) && (x (13 : Fin (26 : ℕ)) || x (14 : Fin (26 : ℕ)) || x (16 : Fin (26 : ℕ)) || x (22 : Fin (26 : ℕ)))) || (x (1 : Fin (26 : ℕ)) && (x (13 : Fin (26 : ℕ)) || x (15 : Fin (26 : ℕ)) || x (21 : Fin (26 : ℕ)) || x (25 : Fin (26 : ℕ)))) || (x (2 : Fin (26 : ℕ)) && (x (14 : Fin (26 : ℕ)) || x (20 : Fin (26 : ℕ)) || x (24 : Fin (26 : ℕ)) || x (25 : Fin (26 : ℕ)))) || (x (3 : Fin (26 : ℕ)) && (x (13 : Fin (26 : ℕ)) || x (19 : Fin (26 : ℕ)) || x (23 : Fin (26 : ℕ)) || x (24 : Fin (26 : ℕ)))) || (x (6 : Fin (26 : ℕ)) && (x (16 : Fin (26 : ℕ)) || x (20 : Fin (26 : ℕ)) || x (21 : Fin (26 : ℕ)) || x (23 : Fin (26 : ℕ))))))
    (hStarEquiv :
      ∀ (a b : Fin (13 : ℕ) → Bool) (x : Fin (26 : ℕ) → Bool),
        (∀ k : Fin (26 : ℕ), x k = if k.val < (13 : ℕ) then a (Fin.ofNat (13 : ℕ) k.val) else b (Fin.ofNat (13 : ℕ) k.val)) →
        (((x (0 : Fin (26 : ℕ)) && (x (13 : Fin (26 : ℕ)) || x (14 : Fin (26 : ℕ)) || x (16 : Fin (26 : ℕ)) || x (22 : Fin (26 : ℕ)))) || (x (1 : Fin (26 : ℕ)) && (x (13 : Fin (26 : ℕ)) || x (15 : Fin (26 : ℕ)) || x (21 : Fin (26 : ℕ)) || x (25 : Fin (26 : ℕ)))) || (x (2 : Fin (26 : ℕ)) && (x (14 : Fin (26 : ℕ)) || x (20 : Fin (26 : ℕ)) || x (24 : Fin (26 : ℕ)) || x (25 : Fin (26 : ℕ)))) || (x (3 : Fin (26 : ℕ)) && (x (13 : Fin (26 : ℕ)) || x (19 : Fin (26 : ℕ)) || x (23 : Fin (26 : ℕ)) || x (24 : Fin (26 : ℕ)))) || (x (6 : Fin (26 : ℕ)) && (x (16 : Fin (26 : ℕ)) || x (20 : Fin (26 : ℕ)) || x (21 : Fin (26 : ℕ)) || x (23 : Fin (26 : ℕ))))) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            p.val ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧
            (p.val + l.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
            a p = Bool.true ∧ b l = Bool.true)) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x5 x4}; have x4 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))}; ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (23 : ℕ) ∧ x5.output < (26 : ℕ) + x5.size ∧ (∀ x6 ∈ x4, ∀ (x8 : Fin (13 : ℕ)), x1 x6 x8 → x5.eval (x2 {x6} {x8}) = Bool.true) ∧ ∀ x6 ⊆ x4, x6 = x4 ∨ x3 x6 ≠ x3 x4 → x5.eval (x2 (x6 ∪ x4ᶜ) (x3 x6)) = Bool.false) := by
  have hMem4 : ∀ p : Fin (13 : ℕ), p.val ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ↔
      p ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := by
    decide
  intro x1 x2 x3 x4
  obtain ⟨C, hM, hSz, hOut, hEv⟩ := hStarCircuit
  refine ⟨C, hM, hSz, hOut, ?_, ?_⟩
  · intro p hp l hpl
    let a : Fin (13 : ℕ) → Bool := fun u => Decidable.decide (u ∈ ({p} : Finset (Fin (13 : ℕ))))
    let b : Fin (13 : ℕ) → Bool := fun v => Decidable.decide (v ∈ ({l} : Finset (Fin (13 : ℕ))))
    let xVec : Fin (26 : ℕ) → Bool := fun k => if k.val < (13 : ℕ) then a (Fin.ofNat (13 : ℕ) k.val) else b (Fin.ofNat (13 : ℕ) k.val)
    exact (hEv xVec).trans ((hStarEquiv a b xVec (fun _ => rfl)).mpr
      ⟨p, l, (hMem4 p).mpr hp, hpl, decide_eq_true (Finset.mem_singleton_self p), decide_eq_true (Finset.mem_singleton_self l)⟩)
  · intro S hSub _
    let a : Fin (13 : ℕ) → Bool := fun u => Decidable.decide (u ∈ S ∪ x4ᶜ)
    let b : Fin (13 : ℕ) → Bool := fun v => Decidable.decide (v ∈ x3 S)
    let xVec : Fin (26 : ℕ) → Bool := fun k => if k.val < (13 : ℕ) then a (Fin.ofNat (13 : ℕ) k.val) else b (Fin.ofNat (13 : ℕ) k.val)
    refine Bool.eq_false_iff.mpr (fun ht => ?_)
    obtain ⟨p, l, hp4, hpl, hpU, hlT⟩ := (hStarEquiv a b xVec (fun _ => rfl)).mp ((hEv xVec).symm.trans ht)
    have hpMem4 : p ∈ x4 := (hMem4 p).mp hp4
    have hpS : p ∈ S := Or.elim (Finset.mem_union.mp (of_decide_eq_true hpU)) id (fun hnc => False.elim ((Finset.mem_compl.mp hnc) hpMem4))
    exact (Finset.mem_filter.mp (of_decide_eq_true hlT)).2 p hpS hpl
