import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25553 : ∀ (nr nc q k : ℕ) (G : Fin nr → Fin nc → Bool)
    (points : (Fin q × Fin 3 × Fin 3) ↪ Fin nr)
    (lines : (Fin q × Bool × Fin 3) ↪ Fin nc)
    (rows : Fin k ↪ Fin nr) (cols : Fin k ↪ Fin nc),
  let touch := fun (a b : Fin nr) =>
    a ≠ b ∧ ∃ c : Fin nc, G a c = true ∧ G b c = true
  (∀ a b : Fin nr, a ≠ b → ∀ w : Fin 3 ↪ Fin nr,
    ¬ (∀ j : Fin 3, touch a (w j) ∧ touch b (w j))) →
  (∀ plane : Fin q, ∀ x y : Fin 3,
    G (points (plane, x, y)) (lines (plane, false, x)) = true ∧
    G (points (plane, x, y)) (lines (plane, true, y)) = true) →
  (∀ i j : Fin k, G (rows i) (cols j) = G (rows j) (cols i)) →
  2 * q ≤ (nr - k) + (nc - k) := by
  intro nr nc q k G points lines rows cols
  dsimp only
  intro H1 H2 H3
  classical
  obtain ⟨lostP, hlostP⟩ : ∃ s : Finset (Fin q × Fin 3 × Fin 3),
      s = Finset.univ.filter (fun t => ∀ j, rows j ≠ points t) := ⟨_, rfl⟩
  obtain ⟨lostL, hlostL⟩ : ∃ s : Finset (Fin q × Bool × Fin 3),
      s = Finset.univ.filter (fun t => ∀ j, cols j ≠ lines t) := ⟨_, rfl⟩
  have memP : ∀ t, t ∈ lostP ↔ ∀ j, rows j ≠ points t := by
    intro t; rw [hlostP, Finset.mem_filter]; simp
  have memL : ∀ t, t ∈ lostL ↔ ∀ j, cols j ≠ lines t := by
    intro t; rw [hlostL, Finset.mem_filter]; simp
  have hP : lostP.card ≤ nr - k := by
    have h1 : (lostP.map points).card ≤ (Finset.univ \ (Finset.univ.map rows)).card := by
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_map] at hr
      obtain ⟨t, ht, rfl⟩ := hr
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      rw [Finset.mem_map] at hmem
      obtain ⟨j, _, hj⟩ := hmem
      exact (memP t).1 ht j hj
    rw [Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1
  have hL : lostL.card ≤ nc - k := by
    have h1 : (lostL.map lines).card ≤ (Finset.univ \ (Finset.univ.map cols)).card := by
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_map] at hr
      obtain ⟨t, ht, rfl⟩ := hr
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      rw [Finset.mem_map] at hmem
      obtain ⟨j, _, hj⟩ := hmem
      exact (memL t).1 ht j hj
    rw [Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1
  have aux : ∀ x0 : Fin 3, ∃ x1 x2 : Fin 3, x1 ≠ x2 ∧ x1 ≠ x0 ∧ x2 ≠ x0 := by decide
  have key : ∀ p : Fin q, 2 ≤ (lostP.filter (fun t => t.1 = p)).card +
      (lostL.filter (fun t => t.1 = p)).card := by
    intro p
    by_contra hlt
    have hlt' : (lostP.filter (fun t => t.1 = p)).card +
        (lostL.filter (fun t => t.1 = p)).card ≤ 1 := by omega
    obtain ⟨d, x0, hline, hpt⟩ : ∃ (d : Bool) (x0 : Fin 3),
        (∀ (e : Bool) (i : Fin 3), (p, e, i) ∈ lostL → e = d ∧ i = x0) ∧
        (∀ x y : Fin 3, (p, x, y) ∈ lostP → (if d = false then x else y) = x0) := by
      by_cases hb : ∃ l, l ∈ lostL.filter (fun t => t.1 = p)
      · obtain ⟨l0, hl0⟩ := hb
        have hb1 : 1 ≤ (lostL.filter (fun t => t.1 = p)).card := Finset.card_pos.mpr ⟨l0, hl0⟩
        have ha0 : (lostP.filter (fun t => t.1 = p)).card = 0 := by omega
        have hb1' : (lostL.filter (fun t => t.1 = p)).card ≤ 1 := by omega
        refine ⟨l0.2.1, l0.2.2, ?_, ?_⟩
        · intro e i hei
          have h : ((p, e, i) : Fin q × Bool × Fin 3) = l0 :=
            Finset.card_le_one.mp hb1' _ (Finset.mem_filter.mpr ⟨hei, rfl⟩) _ hl0
          rw [← h]
          exact ⟨rfl, rfl⟩
        · intro x y hxy
          exfalso
          have h : (p, x, y) ∈ lostP.filter (fun t => t.1 = p) := Finset.mem_filter.mpr ⟨hxy, rfl⟩
          rw [Finset.card_eq_zero] at ha0
          rw [ha0] at h
          simp at h
      · have hb0 : ∀ (e : Bool) (i : Fin 3), (p, e, i) ∉ lostL := by
          intro e i h
          exact hb ⟨_, Finset.mem_filter.mpr ⟨h, rfl⟩⟩
        have ha1 : (lostP.filter (fun t => t.1 = p)).card ≤ 1 := by omega
        by_cases ha : ∃ t, t ∈ lostP.filter (fun t => t.1 = p)
        · obtain ⟨t0, ht0⟩ := ha
          refine ⟨false, t0.2.1, fun e i h => absurd h (hb0 e i), ?_⟩
          intro x y hxy
          have h : ((p, x, y) : Fin q × Fin 3 × Fin 3) = t0 :=
            Finset.card_le_one.mp ha1 _ (Finset.mem_filter.mpr ⟨hxy, rfl⟩) _ ht0
          rw [← h]
          simp
        · refine ⟨false, 0, fun e i h => absurd h (hb0 e i), ?_⟩
          intro x y hxy
          exact absurd ⟨_, Finset.mem_filter.mpr ⟨hxy, rfl⟩⟩ ha
    obtain ⟨x1, x2, h12, h10, h20⟩ := aux x0
    have hpt1 : ∀ x y, G (if d = false then points (p, x, y) else points (p, y, x))
        (lines (p, d, x)) = true := by
      intro x y
      cases d
      · exact (H2 p x y).1
      · exact (H2 p y x).2
    have hpt2 : ∀ x y, G (if d = false then points (p, x, y) else points (p, y, x))
        (lines (p, !d, y)) = true := by
      intro x y
      cases d
      · exact (H2 p x y).2
      · exact (H2 p y x).1
    have retL : ∀ (e : Bool) (i : Fin 3), (e = d → i ≠ x0) → ∃ j, cols j = lines (p, e, i) := by
      intro e i h
      by_contra hne
      have hm : (p, e, i) ∈ lostL := (memL _).2 (fun j hj => hne ⟨j, hj⟩)
      obtain ⟨h1, h2⟩ := hline e i hm
      exact h h1 h2
    have retP : ∀ x y, x ≠ x0 →
        ∃ j, rows j = (if d = false then points (p, x, y) else points (p, y, x)) := by
      intro x y hx
      by_contra hne
      cases d
      · have hm : (p, x, y) ∈ lostP := (memP _).2 (fun j hj => hne ⟨j, hj⟩)
        have h := hpt x y hm
        simp at h
        exact hx h
      · have hm : (p, y, x) ∈ lostP := (memP _).2 (fun j hj => hne ⟨j, hj⟩)
        have h := hpt y x hm
        simp at h
        exact hx h
    obtain ⟨i1, hi1⟩ := retL d x1 (fun _ => h10)
    obtain ⟨i2, hi2⟩ := retL d x2 (fun _ => h20)
    have hperp : ∀ y, ∃ j, cols j = lines (p, !d, y) :=
      fun y => retL (!d) y (fun h => absurd h (by cases d <;> simp))
    choose t ht using hperp
    have hr1 := fun y => retP x1 y h10
    have hr2 := fun y => retP x2 y h20
    choose j1 hj1 using hr1
    choose j2 hj2 using hr2
    have hne : rows i1 ≠ rows i2 := by
      intro h
      have h1 := rows.injective h
      have h2 : lines (p, d, x1) = lines (p, d, x2) := by rw [← hi1, ← hi2, h1]
      have h3 := lines.injective h2
      simp at h3
      exact h12 h3
    have tinj : Function.Injective (fun y => rows (t y)) := by
      intro y y' h
      have h1 := rows.injective h
      have h2 : lines (p, !d, y) = lines (p, !d, y') := by rw [← ht y, ← ht y', h1]
      have h3 := lines.injective h2
      simpa using h3
    apply H1 (rows i1) (rows i2) hne ⟨fun y => rows (t y), tinj⟩
    intro y
    have hti1 : rows i1 ≠ rows (t y) := by
      intro h
      have h1 := rows.injective h
      have h2 : lines (p, d, x1) = lines (p, !d, y) := by rw [← hi1, ← ht y, h1]
      have h3 := lines.injective h2
      cases d <;> simp at h3
    have hti2 : rows i2 ≠ rows (t y) := by
      intro h
      have h1 := rows.injective h
      have h2 : lines (p, d, x2) = lines (p, !d, y) := by rw [← hi2, ← ht y, h1]
      have h3 := lines.injective h2
      cases d <;> simp at h3
    have g1 : G (rows i1) (cols (j1 y)) = true := by
      rw [H3 i1 (j1 y), hj1 y, hi1]; exact hpt1 x1 y
    have g2 : G (rows (t y)) (cols (j1 y)) = true := by
      rw [H3 (t y) (j1 y), hj1 y, ht y]; exact hpt2 x1 y
    have g3 : G (rows i2) (cols (j2 y)) = true := by
      rw [H3 i2 (j2 y), hj2 y, hi2]; exact hpt1 x2 y
    have g4 : G (rows (t y)) (cols (j2 y)) = true := by
      rw [H3 (t y) (j2 y), hj2 y, ht y]; exact hpt2 x2 y
    exact ⟨⟨hti1, cols (j1 y), g1, g2⟩, ⟨hti2, cols (j2 y), g3, g4⟩⟩
  have hsum : 2 * q ≤ lostP.card + lostL.card := by
    have e1 := Finset.card_eq_sum_card_fiberwise (s := lostP) (t := Finset.univ)
      (f := fun t => t.1) (fun _ _ => Finset.mem_univ _)
    have e2 := Finset.card_eq_sum_card_fiberwise (s := lostL) (t := Finset.univ)
      (f := fun t => t.1) (fun _ _ => Finset.mem_univ _)
    rw [e1, e2, ← Finset.sum_add_distrib]
    calc 2 * q = ∑ _p : Fin q, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun p _ => key p)
  omega
