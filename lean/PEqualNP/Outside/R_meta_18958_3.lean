import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18958_3
    (hChainToCircuit63 :
      ∀ (L : List (Set (Fin (26 : ℕ) → Bool))),
        have B : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (i : Fin (26 : ℕ)) => {x : Fin (26 : ℕ) → Bool | x i = Bool.true};
        have T : Set (Fin (26 : ℕ) → Bool) := {x : Fin (26 : ℕ) → Bool | ∃ (p l : Fin (13 : ℕ)), (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true};
        L.length ≤ (63 : ℕ) →
        L.Nodup →
        (∀ s ∈ L, s ∉ B) →
        (∀ (i : ℕ) (s : Set (Fin (26 : ℕ) → Bool)), L[i]? = Option.some s →
          ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) →
        T ∈ L →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 C ∧
          C.size ≤ (63 : ℕ) ∧
          ∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔ x ∈ T)
    (hLowerBound64 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (x : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)), (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (64 : ℕ) ≤ C.size) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → x2 ∉ x3 → (∀ (x8 : ℕ) (x9 : Set (Fin (26 : ℕ) → Bool)), x3[x8]? = Option.some x9 → ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x8 x3) ∧ ∃ (x12 : Set (Fin (26 : ℕ) → Bool)), (x12 ∈ x1 ∨ x12 ∈ List.take x8 x3) ∧ (x9 = x11 ∩ x12 ∨ x9 = x11 ∪ x12)) → ∀ x9 ∈ x3, ∀ x11 ∈ x3, x9 ≠ x11 → x2 ⊆ x9 → x9 ≠ x2 → x2 ⊆ x11 → x11 ≠ x2 → x9 ∩ x11 ≠ x2) := by
  intro x1 x2 x3 hlen hnd hnotB hnotT hstep a ha b hb _ _ _ _ _ hab
  have hT_not_B : x2 ∉ x1 := by
    intro hm
    simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hm
    let y0 : Fin 26 → Bool := fun z => decide (z.val = 0 ∨ z.val = 13)
    let y1 : Fin 26 → Bool := fun z => decide (z.val = 1 ∨ z.val = 15)
    have hy0 : y0 ∈ x2 := ⟨(0 : Fin 13), (0 : Fin 13), by decide, by decide, by decide⟩
    have hy1 : y1 ∈ x2 := ⟨(1 : Fin 13), (2 : Fin 13), by decide, by decide, by decide⟩
    rcases hm with (h0 | hu) | ⟨i, hi⟩
    · exact Set.notMem_empty y0 (h0 ▸ hy0)
    · have hc : (fun _ : Fin 26 => false) ∈ x2 := hu ▸ Set.mem_univ _
      rcases hc with ⟨_, _, _, h1, _⟩
      exact Bool.false_ne_true h1
    · have h0i : y0 i = true := by
        have hmem : y0 ∈ {x : Fin 26 → Bool | x i = true} := hi ▸ hy0
        exact hmem
      have h1i : y1 i = true := by
        have hmem : y1 ∈ {x : Fin 26 → Bool | x i = true} := hi ▸ hy1
        exact hmem
      have : ∀ j : Fin 26, ¬ (y0 j = true ∧ y1 j = true) := by decide
      exact this i ⟨h0i, h1i⟩
  let L := x3 ++ [x2]
  have hL_len : L.length ≤ 63 := by simp only [L, List.length_append, List.length_singleton]; omega
  have hL_nd : L.Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton x2, fun s hs t ht heq => ?_⟩
    rw [List.mem_singleton] at ht
    subst ht
    subst heq
    exact hnotT hs
  have hL_notB : ∀ s ∈ L, s ∉ x1 := by
    intro s hs
    simp only [L, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hnotB s hs
    · exact hT_not_B
  have hL_step : ∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s →
      ∃ u, (u ∈ x1 ∨ u ∈ L.take i) ∧ ∃ v, (v ∈ x1 ∨ v ∈ L.take i) ∧ (s = u ∩ v ∨ s = u ∪ v) := by
    intro i s hi
    by_cases hlt : i < x3.length
    · have hi' : x3[i]? = some s := by
        simpa only [L, List.getElem?_append_left hlt] using hi
      obtain ⟨u, hu, v, hv, hop⟩ := hstep i s hi'
      have htk : L.take i = x3.take i := by simp only [L, List.take_append_of_le_length (Nat.le_of_lt hlt)]
      rw [htk]
      exact ⟨u, hu, v, hv, hop⟩
    · have heq : i = x3.length := by
        by_contra hne
        have hge : L.length ≤ i := by simp only [L, List.length_append, List.length_singleton]; omega
        rw [List.getElem?_eq_none hge] at hi
        cases hi
      subst heq
      have hs : s = x2 := by
        have hget : L[x3.length]? = some x2 := by simp [L]
        rw [hget] at hi
        exact (Option.some.inj hi).symm
      subst hs
      have htk : L.take x3.length = x3 := by simp [L]
      rw [htk]
      exact ⟨a, Or.inr ha, b, Or.inr hb, Or.inl hab.symm⟩
  have hT_mem : x2 ∈ L := by simp [L]
  obtain ⟨C, hmono, hsz, hev⟩ := hChainToCircuit63 L hL_len hL_nd hL_notB hL_step hT_mem
  have hge := hLowerBound64 C hmono hev
  omega

