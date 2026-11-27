import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25459 : ∀ (n m t : ℕ) (K : Bool → Bool → (Fin n → Bool) → (Fin m → Bool) → Bool) (A : Fin n → Fin m → Bool), 1 ≤ t → t + 2 ≤ n → t ≤ m → (t + 3 ≤ n ∨ t + 3 ≤ m) → (∀ (a a' b b' : Bool) (x x' : Fin n → Bool) (y y' : Fin m → Bool), a ≤ a' → b ≤ b' → (∀ i, x i ≤ x' i) → (∀ j, y j ≤ y' j) → K a b x y ≤ K a' b' x' y') → (∀ (a b : Bool) (x x' : Fin n → Bool) (y y' : Fin m → Bool), (∀ i : Fin n, t < i.val → i.val < n - 1 → x i = x' i) → (∀ j : Fin m, t ≤ j.val → j.val < m - 1 → y j = y' j) → K a b x y = K a b x' y') → A = (fun u v => K (!(decide (u.val = v.val ∧ u.val < t))) (!(decide (u.val = t))) (fun p => decide (p = u)) (fun q => decide (q = v))) → (∃ u u' : Fin n, u ≠ u' ∧ ∀ v, A u v = A u' v) ∨ (∃ v v' : Fin m, v ≠ v' ∧ ∀ u, A u v = A u v') := by
  intro n m t K A ht hn hm hnm hmono hign hA
  subst hA
  cases hc : K true true (fun _ => false) (fun _ => false) with
  | false =>
    left
    refine ⟨⟨0, by omega⟩, ⟨n - 1, by omega⟩, ?_, ?_⟩
    · intro h
      have hval := congrArg Fin.val h
      dsimp at hval
      omega
    · intro v
      have h0t : decide (0 = t) = false := decide_eq_false (by omega)
      have hnt : decide (n - 1 = t) = false := decide_eq_false (by omega)
      have hnlt : decide (n - 1 = v.val ∧ n - 1 < t) = false := decide_eq_false (by omega)
      dsimp only
      rw [h0t, hnt, hnlt]
      simp only [Bool.not_false]
      by_cases hv : v.val = 0
      · have h0v : decide (0 = v.val ∧ 0 < t) = true := decide_eq_true ⟨by omega, by omega⟩
        rw [h0v]
        simp only [Bool.not_true]
        have h1 : K false true (fun p => decide (p = ⟨0, by omega⟩)) (fun q => decide (q = v)) =
            K false true (fun _ => false) (fun _ => false) := by
          apply hign
          · intro i hi1 hi2
            exact decide_eq_false (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
          · intro j hj1 hj2
            exact decide_eq_false (fun h => by have := congrArg Fin.val h; omega)
        have h2 : K true true (fun p => decide (p = ⟨n - 1, by omega⟩)) (fun q => decide (q = v)) =
            K true true (fun _ => false) (fun _ => false) := by
          apply hign
          · intro i hi1 hi2
            exact decide_eq_false (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
          · intro j hj1 hj2
            exact decide_eq_false (fun h => by have := congrArg Fin.val h; omega)
        rw [h1, h2, hc]
        have hle : K false true (fun _ => false) (fun _ => false) ≤
            K true true (fun _ => false) (fun _ => false) :=
          hmono false true true true _ _ _ _ (by decide) (by decide) (fun _ => le_rfl) (fun _ => le_rfl)
        rw [hc] at hle
        cases hk : K false true (fun _ => false) (fun _ => false)
        · rfl
        · rw [hk] at hle
          exact absurd hle (by decide)
      · have h0v : decide (0 = v.val ∧ 0 < t) = false := decide_eq_false (fun h => hv h.1.symm)
        rw [h0v]
        simp only [Bool.not_false]
        apply hign
        · intro i hi1 hi2
          have h1 : decide (i = ⟨0, by omega⟩) = false :=
            decide_eq_false (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
          have h2 : decide (i = ⟨n - 1, by omega⟩) = false :=
            decide_eq_false (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
          rw [h1, h2]
        · intro j _ _
          rfl
  | true =>
    rcases hnm with hn3 | hm3
    · left
      have hall : ∀ (u : Fin n) (v : Fin m), t < u.val →
          K (!(decide (u.val = v.val ∧ u.val < t))) (!(decide (u.val = t)))
            (fun p => decide (p = u)) (fun q => decide (q = v)) = true := by
        intro u v hu
        have h1 : decide (u.val = v.val ∧ u.val < t) = false := decide_eq_false (by omega)
        have h2 : decide (u.val = t) = false := decide_eq_false (by omega)
        rw [h1, h2]
        simp only [Bool.not_false]
        have hle : K true true (fun _ => false) (fun _ => false) ≤
            K true true (fun p => decide (p = u)) (fun q => decide (q = v)) :=
          hmono true true true true _ _ _ _ le_rfl le_rfl
            (fun i => by generalize decide (i = u) = b; cases b <;> decide)
            (fun j => by generalize decide (j = v) = b; cases b <;> decide)
        rw [hc] at hle
        cases hk : K true true (fun p => decide (p = u)) (fun q => decide (q = v))
        · rw [hk] at hle
          exact absurd hle (by decide)
        · rfl
      refine ⟨⟨t + 1, by omega⟩, ⟨n - 1, by omega⟩, ?_, ?_⟩
      · intro h
        have hval := congrArg Fin.val h
        dsimp at hval
        omega
      · intro v
        dsimp only
        rw [hall ⟨t + 1, by omega⟩ v (by dsimp; omega),
            hall ⟨n - 1, by omega⟩ v (by dsimp; omega)]
    · right
      have hall : ∀ (u : Fin n) (v : Fin m), u.val ≠ t → t ≤ v.val →
          K (!(decide (u.val = v.val ∧ u.val < t))) (!(decide (u.val = t)))
            (fun p => decide (p = u)) (fun q => decide (q = v)) = true := by
        intro u v hu hv
        have h1 : decide (u.val = v.val ∧ u.val < t) = false := decide_eq_false (by omega)
        have h2 : decide (u.val = t) = false := decide_eq_false hu
        rw [h1, h2]
        simp only [Bool.not_false]
        have hle : K true true (fun _ => false) (fun _ => false) ≤
            K true true (fun p => decide (p = u)) (fun q => decide (q = v)) :=
          hmono true true true true _ _ _ _ le_rfl le_rfl
            (fun i => by generalize decide (i = u) = b; cases b <;> decide)
            (fun j => by generalize decide (j = v) = b; cases b <;> decide)
        rw [hc] at hle
        cases hk : K true true (fun p => decide (p = u)) (fun q => decide (q = v))
        · rw [hk] at hle
          exact absurd hle (by decide)
        · rfl
      let v0 : Fin m := ⟨t, by omega⟩
      let v1 : Fin m := ⟨t + 1, by omega⟩
      let v2 : Fin m := ⟨m - 1, by omega⟩
      let ut : Fin n := ⟨t, by omega⟩
      have heq_of_ut : ∀ (va vb : Fin m), t ≤ va.val → t ≤ vb.val →
          K (!(decide (ut.val = va.val ∧ ut.val < t))) (!(decide (ut.val = t)))
            (fun p => decide (p = ut)) (fun q => decide (q = va)) =
          K (!(decide (ut.val = vb.val ∧ ut.val < t))) (!(decide (ut.val = t)))
            (fun p => decide (p = ut)) (fun q => decide (q = vb)) →
          ∀ u : Fin n,
            K (!(decide (u.val = va.val ∧ u.val < t))) (!(decide (u.val = t)))
              (fun p => decide (p = u)) (fun q => decide (q = va)) =
            K (!(decide (u.val = vb.val ∧ u.val < t))) (!(decide (u.val = t)))
              (fun p => decide (p = u)) (fun q => decide (q = vb)) := by
        intro va vb hva hvb hrow u
        by_cases hu : u.val = t
        · have huut : u = ut := Fin.ext hu
          subst huut
          exact hrow
        · rw [hall u va hu hva, hall u vb hu hvb]
      cases h0 : K (!(decide (ut.val = v0.val ∧ ut.val < t))) (!(decide (ut.val = t)))
          (fun p => decide (p = ut)) (fun q => decide (q = v0)) <;>
      cases h1 : K (!(decide (ut.val = v1.val ∧ ut.val < t))) (!(decide (ut.val = t)))
          (fun p => decide (p = ut)) (fun q => decide (q = v1)) <;>
      cases h2 : K (!(decide (ut.val = v2.val ∧ ut.val < t))) (!(decide (ut.val = t)))
          (fun p => decide (p = ut)) (fun q => decide (q = v2))
      · exact ⟨v0, v1, fun h => by have := congrArg Fin.val h; dsimp [v0, v1] at this; omega,
          heq_of_ut v0 v1 (by dsimp [v0]; omega) (by dsimp [v1]; omega) (h0.trans h1.symm)⟩
      · exact ⟨v0, v1, fun h => by have := congrArg Fin.val h; dsimp [v0, v1] at this; omega,
          heq_of_ut v0 v1 (by dsimp [v0]; omega) (by dsimp [v1]; omega) (h0.trans h1.symm)⟩
      · exact ⟨v0, v2, fun h => by have := congrArg Fin.val h; dsimp [v0, v2] at this; omega,
          heq_of_ut v0 v2 (by dsimp [v0]; omega) (by dsimp [v2]; omega) (h0.trans h2.symm)⟩
      · exact ⟨v1, v2, fun h => by have := congrArg Fin.val h; dsimp [v1, v2] at this; omega,
          heq_of_ut v1 v2 (by dsimp [v1]; omega) (by dsimp [v2]; omega) (h1.trans h2.symm)⟩
      · exact ⟨v1, v2, fun h => by have := congrArg Fin.val h; dsimp [v1, v2] at this; omega,
          heq_of_ut v1 v2 (by dsimp [v1]; omega) (by dsimp [v2]; omega) (h1.trans h2.symm)⟩
      · exact ⟨v0, v2, fun h => by have := congrArg Fin.val h; dsimp [v0, v2] at this; omega,
          heq_of_ut v0 v2 (by dsimp [v0]; omega) (by dsimp [v2]; omega) (h0.trans h2.symm)⟩
      · exact ⟨v0, v1, fun h => by have := congrArg Fin.val h; dsimp [v0, v1] at this; omega,
          heq_of_ut v0 v1 (by dsimp [v0]; omega) (by dsimp [v1]; omega) (h0.trans h1.symm)⟩
      · exact ⟨v0, v1, fun h => by have := congrArg Fin.val h; dsimp [v0, v1] at this; omega,
          heq_of_ut v0 v1 (by dsimp [v0]; omega) (by dsimp [v1]; omega) (h0.trans h1.symm)⟩
