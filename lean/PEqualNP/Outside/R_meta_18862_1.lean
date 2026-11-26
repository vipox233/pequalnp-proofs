import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18862_1
    (hNotInList : let B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let T : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}; ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 62 → (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s → ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) → T ∉ L)
    (hInterTwo : let B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let T : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}; ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 62 → (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s → ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) → T ∉ L → ∀ a ∈ L, ∀ b ∈ L, a ≠ b → T ⊆ a → a ≠ T → T ⊆ b → b ≠ T → a ∩ b ≠ T) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; ∀ (x2 : List (Set (Fin (26 : ℕ) → Bool))), x2.length ≤ (62 : ℕ) → (∀ (x4 : ℕ) (x5 : Set (Fin (26 : ℕ) → Bool)), x2[x4]? = Option.some x5 → ∃ x7 ∈ x1 ∪ ↑(List.take x4 x2).toFinset, ∃ x8 ∈ x1 ∪ ↑(List.take x4 x2).toFinset, x5 = x7 ∩ x8 ∨ x5 = x7 ∪ x8) → ∀ x5 ∈ x1 ∪ ↑x2.toFinset, ∀ x7 ∈ x1 ∪ ↑x2.toFinset, x5 ∩ x7 ≠ {x9 : Fin (26 : ℕ) → Bool | ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), (↑x10 + ↑x11) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x9 (Fin.castAdd (13 : ℕ) x10) = Bool.true ∧ x9 (Fin.natAdd (13 : ℕ) x11) = Bool.true}) := by
  intro x1 L hlen hstep a ha b hb hInt
  let T : Set (Fin 26 → Bool) :=
    {x9 : Fin 26 → Bool | ∃ (x10 x11 : Fin 13), (x10.val + x11.val) % 13 ∈ [0, 1, 3, 9] ∧
      x9 (Fin.castAdd 13 x10) = true ∧ x9 (Fin.natAdd 13 x11) = true}
  change a ∩ b = T at hInt
  let y0 : Fin 26 → Bool := fun z => decide (z.val = 0 ∨ z.val = 13)
  let y1 : Fin 26 → Bool := fun z => decide (z.val = 1 ∨ z.val = 15)
  have hy0 : y0 ∈ T := ⟨(0 : Fin 13), (0 : Fin 13), by decide, by decide, by decide⟩
  have hy1 : y1 ∈ T := ⟨(1 : Fin 13), (2 : Fin 13), by decide, by decide, by decide⟩
  have hDisjY : ∀ i : Fin 26, y0 i = true → y1 i = true → False := by
    dsimp only [y0, y1]
    decide
  have hT_not_sub_var : ∀ i : Fin 26, ¬ (T ⊆ {z : Fin 26 → Bool | z i = true}) := by
    intro i hsub
    exact hDisjY i (hsub hy0) (hsub hy1)
  have hT_not_B : T ∉ x1 := by
    intro hm
    simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hm
    rcases hm with (h0 | hu) | ⟨i, hi⟩
    · have hc : y0 ∈ (∅ : Set (Fin 26 → Bool)) := h0 ▸ hy0
      simp at hc
    · let yz : Fin 26 → Bool := fun _ => false
      have hc : yz ∈ T := hu ▸ Set.mem_univ yz
      rcases hc with ⟨_, _, _, h1t, _⟩
      simp [yz] at h1t
    · exact hT_not_sub_var i (by rw [← hi])
  have hstep' : ∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s →
      ∃ u, (u ∈ x1 ∨ u ∈ L.take i) ∧ ∃ v, (v ∈ x1 ∨ v ∈ L.take i) ∧ (s = u ∩ v ∨ s = u ∪ v) := by
    intro i s hi
    obtain ⟨u, hu, v, hv, hop⟩ := hstep i s hi
    simp only [Set.mem_union, Finset.mem_coe, List.mem_toFinset] at hu hv
    exact ⟨u, hu, v, hv, hop⟩
  have hT_not_L : T ∉ L := hNotInList L hlen hstep'
  simp only [Set.mem_union, Finset.mem_coe, List.mem_toFinset] at ha hb
  have ha_ne_T : a ≠ T := by
    rintro rfl
    rcases ha with haB | haL
    · exact hT_not_B haB
    · exact hT_not_L haL
  have hb_ne_T : b ≠ T := by
    rintro rfl
    rcases hb with hbB | hbL
    · exact hT_not_B hbB
    · exact hT_not_L hbL
  have hab : a ≠ b := by
    rintro rfl
    rw [Set.inter_self] at hInt
    exact ha_ne_T hInt
  have hTa : T ⊆ a := by rw [← hInt]; exact Set.inter_subset_left
  have hTb : T ⊆ b := by rw [← hInt]; exact Set.inter_subset_right
  have haL : a ∈ L := by
    rcases ha with haB | haL
    · exfalso
      simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at haB
      rcases haB with (ha0 | haU) | ⟨i, hai⟩
      · rw [ha0] at hInt
        have hc : y0 ∈ (∅ ∩ b : Set (Fin 26 → Bool)) := hInt ▸ hy0
        simp at hc
      · rw [haU, Set.univ_inter] at hInt
        exact hb_ne_T hInt
      · rw [← hai] at hTa
        exact hT_not_sub_var i hTa
    · exact haL
  have hbL : b ∈ L := by
    rcases hb with hbB | hbL
    · exfalso
      simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hbB
      rcases hbB with (hb0 | hbU) | ⟨i, hbi⟩
      · rw [hb0] at hInt
        have hc : y0 ∈ (a ∩ ∅ : Set (Fin 26 → Bool)) := hInt ▸ hy0
        simp at hc
      · rw [hbU, Set.inter_univ] at hInt
        exact ha_ne_T hInt
      · rw [← hbi] at hTb
        exact hT_not_sub_var i hTb
    · exact hbL
  exact hInterTwo L hlen hstep' hT_not_L a haL b hbL hab hTa ha_ne_T hTb hb_ne_T hInt
