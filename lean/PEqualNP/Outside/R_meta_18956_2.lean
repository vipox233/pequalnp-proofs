import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18956_2
    (hCompileDAG :
      ∀ (T : Set (Fin 26 → Bool)) (L : List (Set (Fin 26 → Bool))),
        L.length ≤ 62 →
        L.Nodup →
        (∀ s ∈ L, s ≠ ∅ ∧ s ≠ Set.univ ∧ ∀ i : Fin 26, s ≠ {x : Fin 26 → Bool | x i = true}) →
        (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s →
          ∃ (a b : Set (Fin 26 → Bool)),
            (a = ∅ ∨ a = Set.univ ∨ (∃ k : Fin 26, a = {x : Fin 26 → Bool | x k = true}) ∨ a ∈ L.take i) ∧
            (b = ∅ ∨ b = Set.univ ∨ (∃ k : Fin 26, b = {x : Fin 26 → Bool | x k = true}) ∨ b ∈ L.take i) ∧
            (s = a ∩ b ∨ s = a ∪ b)) →
        T ∈ L →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsAO2 26 C ∧ C.size ≤ 62 ∧
          ∀ (x : Fin 26 → Bool), PEqualNP.MetaComplexity.circuitFun 26 C x = true ↔ x ∈ T)
    (hNoCircuit62 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 26 C →
        C.size ≤ 62 →
        ¬∀ (x : Fin 26 → Bool),
          PEqualNP.MetaComplexity.circuitFun 26 C x = true ↔
            ∃ (p l : Fin 13), (p.1 + l.1) % 13 ∈ [0, 1, 3, 9] ∧
              x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → (∀ (x7 : ℕ) (x8 : Set (Fin (26 : ℕ) → Bool)), x3[x7]? = Option.some x8 → ∃ (x10 : Set (Fin (26 : ℕ) → Bool)), (x10 ∈ x1 ∨ x10 ∈ List.take x7 x3) ∧ ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x7 x3) ∧ (x8 = x10 ∩ x11 ∨ x8 = x10 ∪ x11)) → x2 ∉ x3) :=
  fun x3 hlen hnd hnotB hstep hmem =>
    let x1 : Set (Set (Fin 26 → Bool)) :=
      {∅, Set.univ} ∪ Set.range fun (i : Fin 26) => {y : Fin 26 → Bool | y i = true}
    let hMemB : ∀ {a : Set (Fin 26 → Bool)},
        a ∈ x1 → a = ∅ ∨ a = Set.univ ∨ ∃ k : Fin 26, a = {x : Fin 26 → Bool | x k = true} := fun ha =>
      Or.elim ((Set.mem_union _ _ _).mp ha)
        (fun h01 => Or.elim (Set.mem_insert_iff.mp h01) Or.inl (fun hu => Or.inr (Or.inl (Set.mem_singleton_iff.mp hu))))
        (fun hr => Exists.elim (Set.mem_range.mp hr) fun k hk => Or.inr (Or.inr ⟨k, hk.symm⟩))
    let hNotB' : ∀ s ∈ x3, s ≠ ∅ ∧ s ≠ Set.univ ∧ ∀ i : Fin 26, s ≠ {x : Fin 26 → Bool | x i = true} :=
      fun s hs =>
        ⟨fun h0 => hnotB s hs (Set.mem_union_left _ (h0.symm ▸ Set.mem_insert ∅ {Set.univ})),
         fun hu => hnotB s hs (Set.mem_union_left _ (Set.mem_insert_of_mem ∅ (Set.mem_singleton_iff.mpr hu))),
         fun i hi => hnotB s hs (Set.mem_union_right _ (Set.mem_range.mpr ⟨i, hi.symm⟩))⟩
    let hStep' : ∀ (i : ℕ) (s : Set (Fin 26 → Bool)), x3[i]? = some s →
        ∃ (a b : Set (Fin 26 → Bool)),
          (a = ∅ ∨ a = Set.univ ∨ (∃ k : Fin 26, a = {x : Fin 26 → Bool | x k = true}) ∨ a ∈ x3.take i) ∧
          (b = ∅ ∨ b = Set.univ ∨ (∃ k : Fin 26, b = {x : Fin 26 → Bool | x k = true}) ∨ b ∈ x3.take i) ∧
          (s = a ∩ b ∨ s = a ∪ b) :=
      fun i s his =>
        Exists.elim (hstep i s his) fun a ha =>
        Exists.elim ha.2 fun b hb =>
          ⟨a, b,
            Or.elim ha.1
              (fun hB => Or.elim (hMemB hB) Or.inl (fun h2 => Or.elim h2 (fun hu => Or.inr (Or.inl hu)) (fun hr => Or.inr (Or.inr (Or.inl hr)))))
              (fun hL => Or.inr (Or.inr (Or.inr hL))),
            Or.elim hb.1
              (fun hB => Or.elim (hMemB hB) Or.inl (fun h2 => Or.elim h2 (fun hu => Or.inr (Or.inl hu)) (fun hr => Or.inr (Or.inr (Or.inl hr)))))
              (fun hL => Or.inr (Or.inr (Or.inr hL))),
            hb.2⟩
    Exists.elim (hCompileDAG _ x3 hlen hnd hNotB' hStep' hmem) fun C hC =>
      hNoCircuit62 C hC.1 hC.2.1 hC.2.2
