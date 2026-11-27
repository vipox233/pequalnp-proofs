import Mathlib

namespace PEqualNP.Outside.L_lib_399_aux

theorem wd {m : ℕ} (F : Finset (Finset (Fin m))) (c : Fin m → ℕ) (H : Finset (Fin m))
    (p : Finset (Fin m) → ℕ)
    (hit : ∀ I ∈ F, (H ∩ I).Nonempty)
    (load : ∀ x : Fin m, (∑ I ∈ F, if x ∈ I then p I else 0) ≤ c x) :
    ∑ I ∈ F, p I ≤ ∑ x ∈ H, c x := by
  calc ∑ I ∈ F, p I ≤ ∑ I ∈ F, ∑ x ∈ H, (if x ∈ I then p I else 0) := by
        apply Finset.sum_le_sum
        intro I hI
        obtain ⟨x, hx⟩ := hit I hI
        rw [Finset.mem_inter] at hx
        have := Finset.single_le_sum (f := fun x => if x ∈ I then p I else 0)
          (fun i _ => Nat.zero_le _) hx.1
        simpa [hx.2] using this
    _ = ∑ x ∈ H, ∑ I ∈ F, (if x ∈ I then p I else 0) := Finset.sum_comm
    _ ≤ ∑ x ∈ H, c x := Finset.sum_le_sum (fun x _ => load x)

theorem main {m : ℕ} : ∀ (n : ℕ) (F : Finset (Finset (Fin m))) (c : Fin m → ℕ),
    (∑ x, c x) + F.card = n →
    (∀ I ∈ F, I.Nonempty ∧ ∀ a ∈ I, ∀ b ∈ I, ∀ x : Fin m, a ≤ x → x ≤ b → x ∈ I) →
    ∃ (H : Finset (Fin m)) (p : Finset (Fin m) → ℕ),
      (∀ I ∈ F, (H ∩ I).Nonempty) ∧
      (∀ x : Fin m, (∑ I ∈ F, if x ∈ I then p I else 0) ≤ c x) ∧
      (F.filter (fun I => 0 < p I)).card ≤ (Finset.univ.filter (fun x => 0 < c x)).card ∧
      (∑ x ∈ H, c x) = ∑ I ∈ F, p I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F c hn hF
  by_cases hz : ∃ I ∈ F, ∃ x ∈ I, c x = 0
  · obtain ⟨I1, hI1, x, hx, hcx⟩ := hz
    have hlt : (F.filter (fun I => x ∉ I)).card < F.card :=
      Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨I1, hI1, by simpa using hx⟩)
    obtain ⟨H', p', hit', load', supp', eq'⟩ := ih _ (by omega) (F.filter (fun I => x ∉ I)) c rfl
      (fun I hI => hF I (Finset.mem_filter.mp hI).1)
    refine ⟨insert x H', fun I => if x ∈ I then 0 else p' I, ?_, ?_, ?_, ?_⟩
    · intro I hI
      by_cases hxI : x ∈ I
      · exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hxI⟩⟩
      · obtain ⟨y, hy⟩ := hit' I (Finset.mem_filter.mpr ⟨hI, hxI⟩)
        rw [Finset.mem_inter] at hy
        exact ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩⟩
    · intro y
      refine le_trans (le_of_eq ?_) (load' y)
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro I _
      by_cases hxI : x ∈ I <;> simp [hxI]
    · refine le_trans (Finset.card_le_card ?_) supp'
      intro I hI
      simp only [Finset.mem_filter] at hI ⊢
      obtain ⟨h1, h2⟩ := hI
      by_cases hxI : x ∈ I
      · simp [hxI] at h2
      · simp only [hxI, if_false] at h2
        exact ⟨⟨h1, hxI⟩, h2⟩
    · rw [Finset.sum_filter] at eq'
      have e1 : ∑ y ∈ insert x H', c y = ∑ y ∈ H', c y := by
        by_cases hxH : x ∈ H'
        · rw [Finset.insert_eq_of_mem hxH]
        · rw [Finset.sum_insert hxH, hcx, zero_add]
      rw [e1, eq']
      apply Finset.sum_congr rfl
      intro I _
      by_cases hxI : x ∈ I <;> simp [hxI]
  · push_neg at hz
    by_cases hFe : F = ∅
    · subst hFe
      exact ⟨∅, fun _ => 0, by simp, by simp, by simp, by simp⟩
    · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFe
      obtain ⟨I0, hI0, hmin⟩ := Finset.exists_min_image F (fun I => I.max) hFne
      obtain ⟨hI0ne, hI0int⟩ := hF I0 hI0
      obtain ⟨x0, hx0, hx0min⟩ := Finset.exists_min_image I0 c hI0ne
      have hδ : 0 < c x0 := Nat.pos_of_ne_zero (hz I0 hI0 x0 hx0)
      obtain ⟨c', hc'⟩ : ∃ c' : Fin m → ℕ, ∀ x, c' x = if x ∈ I0 then c x - c x0 else c x :=
        ⟨_, fun _ => rfl⟩
      have hc'le : ∀ x, c' x ≤ c x := by
        intro x
        rw [hc']
        split_ifs <;> omega
      have hc'x0 : c' x0 = 0 := by rw [hc', if_pos hx0]; omega
      have hsum : ∑ x, c' x < ∑ x, c x :=
        Finset.sum_lt_sum (fun x _ => hc'le x) ⟨x0, Finset.mem_univ _, by rw [hc'x0]; exact hδ⟩
      obtain ⟨H', p', hit', load', supp', eq'⟩ := ih _ (by omega) F c' rfl hF
      have hne : (H' ∩ I0).Nonempty := hit' I0 hI0
      obtain ⟨b, hbdef⟩ : ∃ b, b = (H' ∩ I0).max' hne := ⟨_, rfl⟩
      have hbmem : b ∈ H' ∩ I0 := by rw [hbdef]; exact Finset.max'_mem _ _
      rw [Finset.mem_inter] at hbmem
      obtain ⟨H, hHdef⟩ : ∃ H, H = H'.filter (fun a => a ∉ I0 ∨ a = b) := ⟨_, rfl⟩
      have hbH : b ∈ H := by rw [hHdef]; exact Finset.mem_filter.mpr ⟨hbmem.1, Or.inr rfl⟩
      have hitH : ∀ J ∈ F, (H ∩ J).Nonempty := by
        intro J hJ
        obtain ⟨a, ha⟩ := hit' J hJ
        rw [Finset.mem_inter] at ha
        by_cases hk : a ∉ I0 ∨ a = b
        · exact ⟨a, Finset.mem_inter.mpr ⟨by rw [hHdef]; exact Finset.mem_filter.mpr ⟨ha.1, hk⟩, ha.2⟩⟩
        · push_neg at hk
          have hab : a ≤ b := by
            rw [hbdef]; exact Finset.le_max' _ _ (Finset.mem_inter.mpr ⟨ha.1, hk.1⟩)
          obtain ⟨hJne, hJint⟩ := hF J hJ
          have h1 : I0.max ≤ J.max := hmin J hJ
          have h2 : b ≤ J.max' hJne := by
            have h0 : (b : WithBot (Fin m)) ≤ I0.max := Finset.le_max hbmem.2
            have h3 := le_trans h0 h1
            rw [← Finset.coe_max' hJne] at h3
            exact WithBot.coe_le_coe.mp h3
          have hbJ : b ∈ J := hJint a ha.2 _ (Finset.max'_mem J hJne) b hab h2
          exact ⟨b, Finset.mem_inter.mpr ⟨hbH, hbJ⟩⟩
      have hHiff : ∀ x ∈ H, (x ∈ I0 ↔ x = b) := by
        intro x hx
        rw [hHdef] at hx
        have hor := (Finset.mem_filter.mp hx).2
        constructor
        · intro h
          rcases hor with h' | h'
          · exact absurd h h'
          · exact h'
        · intro h
          rw [h]; exact hbmem.2
      have hcH : ∑ x ∈ H, c x = ∑ x ∈ H, c' x + c x0 := by
        have hpt : ∀ x ∈ H, c x = c' x + (if x = b then c x0 else 0) := by
          intro x hx
          by_cases hxI : x ∈ I0
          · have hle := hx0min x hxI
            rw [if_pos ((hHiff x hx).mp hxI), hc', if_pos hxI]
            omega
          · have hxb : x ≠ b := fun h => hxI ((hHiff x hx).mpr h)
            rw [if_neg hxb, hc', if_neg hxI]
            rfl
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hbH]
      have hwd := wd F c' H p' hitH load'
      have hsub : ∑ x ∈ H, c' x ≤ ∑ x ∈ H', c' x :=
        Finset.sum_le_sum_of_subset (by rw [hHdef]; exact Finset.filter_subset _ _)
      refine ⟨H, fun I => p' I + (if I = I0 then c x0 else 0), hitH, ?_, ?_, ?_⟩
      · intro x
        have e : ∑ I ∈ F, (if x ∈ I then p' I + (if I = I0 then c x0 else 0) else 0)
            = (∑ I ∈ F, if x ∈ I then p' I else 0)
              + ∑ I ∈ F, (if I = I0 then (if x ∈ I0 then c x0 else 0) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro I _
          by_cases h2 : I = I0
          · rw [h2]
            by_cases h1 : x ∈ I0 <;> simp [h1]
          · by_cases h1 : x ∈ I <;> simp [h1, h2]
        rw [e, Finset.sum_ite_eq', if_pos hI0]
        have hl := load' x
        have hcx : c' x + (if x ∈ I0 then c x0 else 0) ≤ c x := by
          by_cases h : x ∈ I0
          · have hle := hx0min x h
            rw [if_pos h, hc', if_pos h]
            omega
          · rw [if_neg h, hc', if_neg h]
            exact le_of_eq rfl
        exact le_trans (Nat.add_le_add_right hl _) hcx
      · have hpos : (Finset.univ.filter (fun x => 0 < c' x)).card
            < (Finset.univ.filter (fun x => 0 < c x)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨x0, by simpa using hδ, by simp [hc'x0]⟩
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact lt_of_lt_of_le hx (hc'le x)
        have hs : F.filter (fun I => 0 < p' I + (if I = I0 then c x0 else 0))
            ⊆ insert I0 (F.filter (fun I => 0 < p' I)) := by
          intro I hI
          simp only [Finset.mem_filter, Finset.mem_insert] at hI ⊢
          by_cases h : I = I0
          · exact Or.inl h
          · right
            rw [if_neg h, add_zero] at hI
            exact hI
        have hc1 := Finset.card_le_card hs
        have hc2 := Finset.card_insert_le I0 (F.filter (fun I => 0 < p' I))
        exact le_trans hc1 (le_trans hc2 (by omega))
      · rw [hcH, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hI0]
        omega

end PEqualNP.Outside.L_lib_399_aux

theorem PEqualNP.Outside.L_lib_399 : ∀ (m : ℕ) (F : Finset (Finset (Fin m))) (c : Fin m → ℕ),
  (∀ I ∈ F, I.Nonempty ∧ ∀ a ∈ I, ∀ b ∈ I, ∀ x : Fin m, a ≤ x → x ≤ b → x ∈ I) →
  ∃ (H : Finset (Fin m)) (p : Finset (Fin m) → ℕ),
    (∀ I ∈ F, (H ∩ I).Nonempty) ∧
    (∀ x : Fin m, (∑ I ∈ F, if x ∈ I then p I else 0) ≤ c x) ∧
    (F.filter (fun I => 0 < p I)).card ≤ m ∧
    (∑ x ∈ H, c x) = ∑ I ∈ F, p I := by
  intro m F c hF
  obtain ⟨H, p, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_lib_399_aux.main _ F c rfl hF
  refine ⟨H, p, h1, h2, le_trans h3 ?_, h4⟩
  calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp
