import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_438

def F (n m : ℕ) (t : ℕ) (y : Fin n → ZMod 2) : Fin m → ZMod 2 :=
  fun i => ∑ j : Fin n, if t.testBit (i.val + (n - 1 - j.val)) then y j else 0

theorem z2_add_self : ∀ u : ZMod 2, u + u = 0 := by decide

theorem z2_ne_add_one : ∀ u v : ZMod 2, u ≠ v → u + 1 = v := by decide

theorem F_sub (n m t : ℕ) (x z : Fin n → ZMod 2) :
    F n m t (x - z) = F n m t x - F n m t z := by
  funext i
  simp only [F, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem F_xor (n m t u : ℕ) (y : Fin n → ZMod 2) :
    F n m (t ^^^ u) y = F n m t y + F n m u y := by
  funext i
  simp only [F, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_xor]
  cases t.testBit (i.val + (n - 1 - j.val)) <;> cases u.testBit (i.val + (n - 1 - j.val)) <;>
    simp [z2_add_self]

theorem F_pow (n m p : ℕ) (y : Fin n → ZMod 2) (i : Fin m) :
    F n m (2 ^ p) y i = ∑ j : Fin n, if p = i.val + (n - 1 - j.val) then y j else 0 := by
  simp only [F, Nat.testBit_two_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p = i.val + (n - 1 - j.val) <;> simp [h]

theorem surj (n m : ℕ) (y : Fin n → ZMod 2) (hy : y ≠ 0) (c : Fin m → ZMod 2) :
    ∃ t, t < 2 ^ (n + m - 1) ∧ F n m t y = c := by
  have hS : (Finset.univ.filter (fun j : Fin n => y j ≠ 0)).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
    exact ⟨j, by simpa using hj⟩
  set j0 := (Finset.univ.filter (fun j : Fin n => y j ≠ 0)).min' hS with hj0
  have hy0 : y j0 ≠ 0 := by
    have := Finset.min'_mem _ hS
    rw [← hj0] at this
    simpa using this
  have hy1 : y j0 = 1 := by
    exact (by decide : ∀ u : ZMod 2, u ≠ 0 → u = 1) _ hy0
  have hlow : ∀ j : Fin n, j.val < j0.val → y j = 0 := by
    intro j hj
    by_contra hne
    have : j0 ≤ j := Finset.min'_le _ _ (by simpa using hne)
    exact absurd (Fin.le_def.mp this) (by omega)
  have key : ∀ k, k ≤ m → ∃ t, t < 2 ^ (n + m - 1) ∧
      ∀ i : Fin m, i.val < k → F n m t y i = c i := by
    intro k
    induction k with
    | zero => intro _; exact ⟨0, by positivity, fun i hi => absurd hi (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨t, ht, hti⟩ := ih (by omega)
      let i0 : Fin m := ⟨k, by omega⟩
      by_cases hgood : F n m t y i0 = c i0
      · refine ⟨t, ht, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hti i h
        · have : i = i0 := Fin.ext h
          rw [this]; exact hgood
      · let p := k + (n - 1 - j0.val)
        have hp : p < n + m - 1 := by
          have := j0.isLt
          omega
        refine ⟨t ^^^ 2 ^ p, Nat.xor_lt_two_pow ht (Nat.pow_lt_pow_right (by norm_num) hp),
          fun i hi => ?_⟩
        rw [F_xor, Pi.add_apply, F_pow]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · rw [hti i h, Finset.sum_eq_zero, add_zero]
          intro j _
          split_ifs with hj
          · apply hlow
            have := j.isLt
            have := j0.isLt
            omega
          · rfl
        · have hi0 : i = i0 := Fin.ext h
          subst hi0
          rw [Finset.sum_eq_single j0]
          · rw [if_pos rfl, hy1]
            exact z2_ne_add_one _ _ hgood
          · intro j _ hne
            rw [if_neg]
            intro hj
            apply hne
            apply Fin.ext
            have := j.isLt
            have := j0.isLt
            show j.val = j0.val
            simp only [i0, p] at hj
            omega
          · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨t, ht, hti⟩ := key m le_rfl
  exact ⟨t, ht, funext fun i => hti i i.isLt⟩

theorem fiber (n m : ℕ) (y : Fin n → ZMod 2) (hy : y ≠ 0) (c : Fin m → ZMod 2) :
    2 ^ m * (Finset.univ.filter (fun t : Fin (2 ^ (n + m - 1)) => F n m t.val y = c)).card =
      2 ^ (n + m - 1) := by
  have heq : ∀ c c' : Fin m → ZMod 2,
      (Finset.univ.filter (fun t : Fin (2 ^ (n + m - 1)) => F n m t.val y = c)).card =
      (Finset.univ.filter (fun t : Fin (2 ^ (n + m - 1)) => F n m t.val y = c')).card := by
    intro c c'
    obtain ⟨u, hu, hFu⟩ := surj n m y hy (c + c')
    let g : Fin (2 ^ (n + m - 1)) → Fin (2 ^ (n + m - 1)) :=
      fun t => ⟨t.val ^^^ u, Nat.xor_lt_two_pow t.isLt hu⟩
    have gg : ∀ t, g (g t) = t := by
      intro t
      apply Fin.ext
      show t.val ^^^ u ^^^ u = t.val
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have hg : ∀ t, F n m (g t).val y = F n m t.val y + (c + c') := by
      intro t
      show F n m (t.val ^^^ u) y = _
      rw [F_xor, hFu]
    apply Finset.card_nbij' g g
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [hg, ht, ← add_assoc, (show c + c = 0 from funext fun i => z2_add_self _), zero_add]
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [hg, ht, add_comm c c', ← add_assoc,
        (show c' + c' = 0 from funext fun i => z2_add_self _), zero_add]
    · intro t _; exact gg t
    · intro t _; exact gg t
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (2 ^ (n + m - 1)))))
    (t := (Finset.univ : Finset (Fin m → ZMod 2)))
    (f := fun t => F n m t.val y) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  rw [Finset.sum_congr rfl (fun c' _ => heq c' c), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum.symm

theorem main (n m : ℕ) (x z : Fin n → ZMod 2) (hxz : x ≠ z) (a b : Fin m → ZMod 2) :
    2 ^ (2 * m) * (Finset.univ.filter (fun s : Fin (2 ^ (n + m - 1)) × (Fin m → ZMod 2) =>
        (fun i => s.2 i + F n m s.1.val x i) = a ∧ (fun i => s.2 i + F n m s.1.val z i) = b)).card =
      2 ^ (n + m - 1) * 2 ^ m := by
  have hy : x - z ≠ 0 := sub_ne_zero.mpr hxz
  have hc : (Finset.univ.filter (fun s : Fin (2 ^ (n + m - 1)) × (Fin m → ZMod 2) =>
        (fun i => s.2 i + F n m s.1.val x i) = a ∧ (fun i => s.2 i + F n m s.1.val z i) = b)).card =
      (Finset.univ.filter (fun t : Fin (2 ^ (n + m - 1)) => F n m t.val (x - z) = a - b)).card := by
    apply Finset.card_nbij' (fun s => s.1) (fun t => (t, a - F n m t.val x))
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
      obtain ⟨h1, h2⟩ := hs
      rw [F_sub, ← h1, ← h2]
      funext i
      simp only [Pi.sub_apply]
      ring
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [F_sub] at ht
      refine ⟨?_, ?_⟩
      · funext i; simp
      · funext i
        have := congrFun ht i
        simp only [Pi.sub_apply] at this ⊢
        linear_combination -this
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs
      obtain ⟨h1, _⟩ := hs
      ext
      · rfl
      · rename_i i
        simp only [← h1, Pi.sub_apply]
        ring
    · intro t _; rfl
  rw [hc, two_mul, pow_add, mul_assoc, fiber n m (x - z) hy (a - b)]
  ring

end PEqualNP.Outside.L_lib_438

theorem PEqualNP.Outside.L_lib_438 : ∀ n m : Nat, 0 < n →
  let Seed := Fin (2^(n+m-1)) × (Fin m → ZMod 2)
  let h := fun (s : Seed) (x : Fin n → ZMod 2) (i : Fin m) =>
    s.2 i + ∑ j : Fin n, if s.1.val.testBit (i.val+(n-1-j.val)) then x j else 0
  ∀ x z : Fin n → ZMod 2, x ≠ z → ∀ a b : Fin m → ZMod 2,
    2^(2*m) * (Finset.univ.filter (fun draw : Seed => h draw x = a ∧ h draw z = b)).card =
      2^(n+m-1) * 2^m := by
  intro n m _ Seed h x z hxz a b
  exact PEqualNP.Outside.L_lib_438.main n m x z hxz a b
