import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7782_3
    (hFuncToSetDAG :
      ∀ (base gs : List ((Fin (26 : ℕ) → Bool) → Bool)) (f : (Fin (26 : ℕ) → Bool) → Bool),
        f ∈ base ++ gs →
        (∀ (k : Fin gs.length),
          ∃ u ∈ base ++ List.take (↑k) gs, ∃ v ∈ base ++ List.take (↑k) gs,
            (∀ (x : Fin (26 : ℕ) → Bool), gs.get k x = (u x || v x)) ∨
            (∀ (x : Fin (26 : ℕ) → Bool), gs.get k x = (u x && v x))) →
        have lift : ((Fin (26 : ℕ) → Bool) → Bool) → Bool → Set (Fin (26 : ℕ) → Bool) :=
          fun (h : (Fin (26 : ℕ) → Bool) → Bool) (b : Bool) => {x : Fin (26 : ℕ) → Bool | h x = b}
        have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map lift base
        have x3 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map lift gs
        x3.length = gs.length ∧
        lift f ∈ x1 ++ x3 ∧
        (∀ (k : Fin x3.length),
          have ctx : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑k) x3
          ∃ u ∈ ctx, ∃ v ∈ ctx, ∃ (op : Bool), ∀ (b : Bool), x3.get k b ⊆ if b = op then u b ∪ v b else u b ∩ v b))
    (hFuncSLP :
      have base : List ((Fin (26 : ℕ) → Bool) → Bool) :=
        (List.ofFn fun (i : Fin (26 : ℕ)) (x : Fin (26 : ℕ) → Bool) => x i) ++
        [fun (x : Fin (26 : ℕ) → Bool) => x (0 : Fin (26 : ℕ)) || x (1 : Fin (26 : ℕ))]
      ∃ (gs : List ((Fin (26 : ℕ) → Bool) → Bool)) (f : (Fin (26 : ℕ) → Bool) → Bool),
        gs.length ≤ (43 : ℕ) ∧
        f ∈ base ++ gs ∧
        (∀ (k : Fin gs.length),
          ∃ u ∈ base ++ List.take (↑k) gs, ∃ v ∈ base ++ List.take (↑k) gs,
            (∀ (x : Fin (26 : ℕ) → Bool), gs.get k x = (u x || v x)) ∨
            (∀ (x : Fin (26 : ℕ) → Bool), gs.get k x = (u x && v x))) ∧
        (∀ (x : Fin (26 : ℕ) → Bool),
          f x = Bool.true ↔
            ∃ (a b : Fin (13 : ℕ)),
              ↑b ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              (↑a + ↑b) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) a) = Bool.true ∧
              x (Fin.natAdd (13 : ℕ) b) = Bool.true)) :
    (have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x1 : (Fin (26 : ℕ) → Bool) → Bool) (x2 : Bool) => {x3 : Fin (26 : ℕ) → Bool | x1 x3 = x2}) ((List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), ↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x4 : Bool → Set (Fin (26 : ℕ) → Bool)),   x3.length ≤ (43 : ℕ) ∧     x4 ∈ x1 ++ x3 ∧       (∀ (x5 : Fin x3.length),           have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑x5) x3;           ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x3.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10) ∧         ∀ (x5 : Fin (26 : ℕ) → Bool), (x2 x5 → x5 ∈ x4 Bool.true) ∧ (¬x2 x5 → x5 ∈ x4 Bool.false)) := by
  obtain ⟨gs, f, hLen, hfMem, hStep, hCorr⟩ := hFuncSLP
  obtain ⟨hLenEq, hLiftMem, hSetStep⟩ := hFuncToSetDAG _ gs f hfMem hStep
  refine ⟨List.map (fun (h : (Fin (26 : ℕ) → Bool) → Bool) (b : Bool) => {x : Fin (26 : ℕ) → Bool | h x = b}) gs,
    (fun (b : Bool) => {x : Fin (26 : ℕ) → Bool | f x = b}),
    ?_, hLiftMem, hSetStep, fun x => ⟨fun hx => (hCorr x).mpr hx, fun hnx => Bool.eq_false_iff.mpr (fun ht => hnx ((hCorr x).mp ht))⟩⟩
  rw [hLenEq]
  exact hLen
