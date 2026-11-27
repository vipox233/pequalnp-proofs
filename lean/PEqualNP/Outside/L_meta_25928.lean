import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25928

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide
lemma z2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma natCast_add_nat {n : ℕ} (a b : ℕ) :
    ((a : ℕ) : ZMod n) + ((b : ℕ) : ZMod n) = ((a + b : ℕ) : ZMod n) :=
  (Nat.cast_add a b).symm

lemma natCast_add_one {n : ℕ} (a : ℕ) :
    ((a : ℕ) : ZMod n) + 1 = ((a + 1 : ℕ) : ZMod n) := by
  rw [Nat.cast_add, Nat.cast_one]

lemma natCast_add_two {n : ℕ} (a : ℕ) :
    ((a : ℕ) : ZMod n) + 2 = ((a + 2 : ℕ) : ZMod n) := by
  rw [Nat.cast_add, Nat.cast_ofNat]

lemma zmod_eq_of_mod_eq {n : ℕ} [NeZero n] {a b : ℕ} (h : a % n = b % n) :
    ((a : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, ZMod.val_natCast]
  exact h

lemma wedge_zero_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f g : V →ₗ[ZMod 2] ZMod 2) :
    (∀ u v : V, f u * g v + f v * g u = 0) ↔ (f = 0 ∨ g = 0 ∨ f = g) := by
  constructor
  · intro hw
    by_cases hf : f = 0
    · exact Or.inl hf
    · by_cases hg : g = 0
      · exact Or.inr (Or.inl hg)
      · right; right
        have hex_f : ∃ u : V, f u = 1 := by
          by_contra hno
          apply hf; ext u
          rcases z2_cases (f u) with h0 | h1
          · exact h0
          · exact False.elim (hno ⟨u, h1⟩)
        have hex_g : ∃ v : V, g v = 1 := by
          by_contra hno
          apply hg; ext v
          rcases z2_cases (g v) with h0 | h1
          · exact h0
          · exact False.elim (hno ⟨v, h1⟩)
        obtain ⟨u0, hu0⟩ := hex_f
        obtain ⟨v0, hv0⟩ := hex_g
        ext x
        have h1 := hw u0 x
        have h2 := hw v0 x
        have h3 := hw u0 v0
        rw [hu0, one_mul] at h1 h3
        rw [hv0, mul_one] at h2
        rw [hv0] at h3
        have hbool : ∀ a b fx gx : ZMod 2,
            gx + fx * a = 0 → b * gx + fx = 0 → 1 + b * a = 0 → fx = gx := by decide
        exact hbool (g u0) (f v0) (f x) (g x) h1 h2 h3
  · rintro (rfl | rfl | rfl) u v
    · simp
    · simp
    · rw [mul_comm (f v) (f u), z2_add_self]

lemma cyclic_label_dim_le {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    {m : ℕ} (hm : 2 ≤ m)
    (ℓ : ZMod (3 * m) → (A →ₗ[ZMod 2] ZMod 2))
    (hinj : ∀ a : A, (∀ j : ZMod (3 * m), ℓ j a = 0) → a = 0)
    (hP1 : ∀ j : ZMod (3 * m), ℓ j = 0 ∨ ℓ (j + 1) = 0 ∨ ℓ j = ℓ (j + 1))
    (hP2 : ∀ j : ZMod (3 * m),
      let C := fun t : ZMod (3 * m) => ℓ t + ℓ (t + 1) + ℓ (t + 2)
      C j = 0 ∨ C (j + 1) = 0 ∨ C j = C (j + 1))
    (hP3 : (∑ q : Fin m, ℓ ((3 * q.val : ℕ) : ZMod (3 * m)) =
            ∑ q : Fin m, ℓ ((3 * q.val + 1 : ℕ) : ZMod (3 * m))) ∧
           (∑ q : Fin m, ℓ ((3 * q.val + 1 : ℕ) : ZMod (3 * m)) =
            ∑ q : Fin m, ℓ ((3 * q.val + 2 : ℕ) : ZMod (3 * m)))) :
    Module.finrank (ZMod 2) A ≤ m - 1 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : NeZero (3 * m) := ⟨by omega⟩
  let NZ : Finset (A →ₗ[ZMod 2] ZMod 2) := (Finset.univ.image ℓ).erase 0
  let Uspan := Submodule.span (ZMod 2) (NZ : Set (A →ₗ[ZMod 2] ZMod 2))
  haveI : Module.Finite (ZMod 2) Uspan :=
    Module.Finite.span_of_finite (ZMod 2) (Finset.finite_toSet NZ)
  haveI : Module.Free (ZMod 2) Uspan := Module.Free.of_divisionRing (ZMod 2) Uspan
  have hfinA_le : Module.finrank (ZMod 2) A ≤ Module.finrank (ZMod 2) Uspan := by
    let d := Module.finrank (ZMod 2) Uspan
    let bas := Module.finBasis (ZMod 2) Uspan
    let ev : A →ₗ[ZMod 2] (Fin d → ZMod 2) :=
      { toFun := fun a i => (bas i).val a
        map_add' := fun a1 a2 => by funext i; simp
        map_smul' := fun c a => by funext i; simp }
    have hev_inj : Function.Injective ev := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      apply hinj a
      intro j
      by_cases h0 : ℓ j = 0
      · rw [h0]; simp
      · have hmem : ℓ j ∈ Uspan := Submodule.subset_span
          (Finset.mem_erase.mpr ⟨h0, Finset.mem_image_of_mem ℓ (Finset.mem_univ j)⟩)
        let eval_a : Uspan →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun f => f.val a
            map_add' := fun f1 f2 => by simp
            map_smul' := fun c f => by simp }
        have hzero : eval_a = 0 := bas.ext fun i => by
          have := congrFun ha i
          simpa [ev, eval_a] using this
        have := LinearMap.congr_fun hzero ⟨ℓ j, hmem⟩
        simpa [eval_a] using this
    have hle := LinearMap.finrank_le_finrank_of_injective hev_inj
    simpa [d] using hle
  suffices hspan : Module.finrank (ZMod 2) Uspan ≤ m - 1 from le_trans hfinA_le hspan
  have hspan_le_card : ∀ S : Finset (A →ₗ[ZMod 2] ZMod 2),
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set (A →ₗ[ZMod 2] ZMod 2))) ≤ S.card := by
    intro S
    simpa using finrank_span_le_card (R := ZMod 2) (S : Set (A →ₗ[ZMod 2] ZMod 2))
  by_cases hD1 : NZ.card ≤ 1
  · exact le_trans (hspan_le_card NZ) (by omega)
  · have hD2 : 2 ≤ NZ.card := by omega
    have hex_end : ∀ α ∈ NZ, ∃ j : ZMod (3 * m), ℓ j = α ∧ ℓ (j + 1) = 0 ∧ ℓ (j + 2) ≠ α := by
      intro α hα
      have hα_ne0 : α ≠ 0 := (Finset.mem_erase.mp hα).1
      obtain ⟨j1, _, hj1⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hα).2
      have hex_β : ∃ β ∈ NZ, β ≠ α := by
        have hpos : 0 < (NZ.erase α).card := by rw [Finset.card_erase_of_mem hα]; omega
        obtain ⟨β, hβ⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_erase] at hβ
        exact ⟨β, hβ.2, hβ.1⟩
      obtain ⟨β, hβ, hβα⟩ := hex_β
      have hβ_ne0 : β ≠ 0 := (Finset.mem_erase.mp hβ).1
      obtain ⟨j2, _, hj2⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hβ).2
      set d : ℕ := (j2 - j1).val
      have hd_pos : 0 < d := by
        have hne : j2 - j1 ≠ 0 := by
          intro h0
          have heq : j2 = j1 := sub_eq_zero.mp h0
          rw [heq, hj1] at hj2; exact hβα hj2.symm
        have hv : (j2 - j1).val ≠ 0 := fun h =>
          hne (by rw [← ZMod.natCast_zmod_val (j2 - j1), h]; simp)
        omega
      let Sα : Finset ℕ := (Finset.range d).filter (fun n => ℓ (j1 + (n : ZMod (3 * m))) = α)
      have hne_S : Sα.Nonempty := ⟨0, by simp [Sα, hd_pos, hj1]⟩
      obtain ⟨n0, hn0_mem, hn0_max⟩ := Finset.exists_max_image Sα id hne_S
      have hn0_lt : n0 < d := Finset.mem_range.mp (Finset.mem_filter.mp hn0_mem).1
      have hn0_eq : ℓ (j1 + (n0 : ZMod (3 * m))) = α := (Finset.mem_filter.mp hn0_mem).2
      let j := j1 + (n0 : ZMod (3 * m))
      have hj1_ne : ℓ (j + 1) ≠ α := by
        by_cases hlast : n0 + 1 = d
        · have heq : j + 1 = j2 := by
            dsimp only [j]
            rw [add_assoc, natCast_add_one, hlast, ZMod.natCast_zmod_val]; abel
          rw [heq, hj2]; exact hβα
        · intro h
          have hmem : n0 + 1 ∈ Sα := by
            simp only [Sα, Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ?_⟩
            rw [← natCast_add_one, ← add_assoc]; exact h
          have hle := hn0_max (n0 + 1) hmem
          dsimp only [id] at hle; omega
      have hj1_zero : ℓ (j + 1) = 0 := by
        rcases hP1 j with h0 | h1 | heq
        · rw [hn0_eq] at h0; exact False.elim (hα_ne0 h0)
        · exact h1
        · rw [hn0_eq] at heq; exact False.elim (hj1_ne heq.symm)
      have hj2_ne : ℓ (j + 2) ≠ α := by
        have hnot1 : n0 + 1 ≠ d := by
          intro hlast
          have heq : j + 1 = j2 := by
            dsimp only [j]
            rw [add_assoc, natCast_add_one, hlast, ZMod.natCast_zmod_val]; abel
          rw [heq, hj2] at hj1_zero; exact hβ_ne0 hj1_zero
        by_cases hlast2 : n0 + 2 = d
        · have heq : j + 2 = j2 := by
            dsimp only [j]
            rw [add_assoc, natCast_add_two, hlast2, ZMod.natCast_zmod_val]; abel
          rw [heq, hj2]; exact hβα
        · intro h
          have hmem : n0 + 2 ∈ Sα := by
            simp only [Sα, Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ?_⟩
            rw [← natCast_add_two, ← add_assoc]; exact h
          have hle := hn0_max (n0 + 2) hmem
          dsimp only [id] at hle; omega
      exact ⟨j, hn0_eq, hj1_zero, hj2_ne⟩
    have hex_all : ∀ α : A →ₗ[ZMod 2] ZMod 2,
        ∃ j : ZMod (3 * m), α ∈ NZ → ℓ j = α ∧ ℓ (j + 1) = 0 ∧ ℓ (j + 2) ≠ α := by
      intro α
      by_cases h : α ∈ NZ
      · obtain ⟨j, hj⟩ := hex_end α h; exact ⟨j, fun _ => hj⟩
      · exact ⟨0, fun h' => False.elim (h h')⟩
    choose jw hjw using hex_all
    have htype2 : ∀ α ∈ NZ, ℓ (jw α - 1) ≠ α → ℓ (jw α - 1) = 0 ∧ ℓ (jw α + 2) = 0 := by
      intro α hα hne
      obtain ⟨hj0, hj1, hj2⟩ := hjw α hα
      have hα_ne0 : α ≠ 0 := (Finset.mem_erase.mp hα).1
      have hm1 : ℓ (jw α - 1) = 0 := by
        have hp := hP1 (jw α - 1)
        rw [sub_add_cancel, hj0] at hp
        rcases hp with h0 | h1 | heq
        · exact h0
        · exact False.elim (hα_ne0 h1)
        · exact False.elim (hne heq)
      refine ⟨hm1, ?_⟩
      have hp2 := hP2 (jw α - 1)
      dsimp only at hp2
      have ha1 : jw α - 1 + 1 = jw α := by abel
      have ha2 : jw α - 1 + 2 = jw α + 1 := by ring
      rw [ha1, ha2, hm1, hj0, hj1, zero_add, add_zero] at hp2
      rcases hp2 with h0 | hsum0 | heq
      · exact False.elim (hα_ne0 h0)
      · exfalso; apply hj2
        ext a
        have h0 := LinearMap.congr_fun hsum0 a
        simp only [LinearMap.add_apply, LinearMap.zero_apply] at h0
        have hb : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
        exact hb (α a) (ℓ (jw α + 2) a) h0
      · ext a
        have h0 := LinearMap.congr_fun heq a
        simp only [LinearMap.add_apply, LinearMap.zero_apply] at h0
        have hb : ∀ x y : ZMod 2, x = x + y → y = 0 := by decide
        exact hb (α a) (ℓ (jw α + 2) a) h0
    let T : (A →ₗ[ZMod 2] ZMod 2) → Finset (ZMod (3 * m)) := fun α =>
      if ℓ (jw α - 1) = α then {jw α - 1, jw α, jw α + 1} else {jw α, jw α + 1, jw α + 2}
    have hneq_small : ∀ (x : ZMod (3 * m)) (a b : ℕ), a < 6 → b < 6 → a ≠ b →
        x + (a : ZMod (3 * m)) ≠ x + (b : ZMod (3 * m)) := by
      intro x a b ha hb hab h
      have h1 : ((a : ℕ) : ZMod (3 * m)) = ((b : ℕ) : ZMod (3 * m)) := add_left_cancel h
      have h2 := congrArg ZMod.val h1
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h2
      exact hab h2
    have hT_card : ∀ α, (T α).card = 3 := by
      intro α
      dsimp only [T]
      have hne01 : ∀ x : ZMod (3 * m), x ≠ x + 1 := fun x h =>
        hneq_small x 0 1 (by omega) (by omega) (by omega) (by simpa using h)
      have hne02 : ∀ x : ZMod (3 * m), x ≠ x + 2 := fun x h =>
        hneq_small x 0 2 (by omega) (by omega) (by omega) (by simpa using h)
      have hne12 : ∀ x : ZMod (3 * m), x + 1 ≠ x + 2 := fun x h =>
        hneq_small x 1 2 (by omega) (by omega) (by omega) (by simpa using h)
      split_ifs
      · have h1 : jw α - 1 ≠ jw α := fun h => hne01 (jw α - 1) (by rw [sub_add_cancel]; exact h)
        have h2 : jw α - 1 ≠ jw α + 1 := fun h => hne02 (jw α - 1) (by
          have : jw α - 1 + 2 = jw α + 1 := by ring
          rw [this]; exact h)
        have h3 : jw α ≠ jw α + 1 := hne01 (jw α)
        simp [Finset.card_insert_of_notMem, h1, h2, h3]
      · simp [Finset.card_insert_of_notMem, hne01, hne02, hne12]
    have hT_disj : Set.PairwiseDisjoint (NZ : Set (A →ₗ[ZMod 2] ZMod 2)) T := by
      intro α hα β hβ hαβ
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hxα hxβ
      have hα_ne0 : α ≠ 0 := (Finset.mem_erase.mp hα).1
      have hβ_ne0 : β ≠ 0 := (Finset.mem_erase.mp hβ).1
      have hclass : ∀ γ ∈ NZ, x ∈ T γ →
          ℓ x = γ ∨ (ℓ x = 0 ∧ ℓ (x - 1) = γ) ∨ (ℓ x = 0 ∧ ℓ (x - 1) = 0 ∧ ℓ (x - 2) = γ) := by
        intro γ hγ hxγ
        obtain ⟨hg0, hg1, _⟩ := hjw γ hγ
        dsimp only [T] at hxγ
        by_cases ht1 : ℓ (jw γ - 1) = γ
        · rw [if_pos ht1] at hxγ
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxγ
          rcases hxγ with rfl | rfl | rfl
          · exact Or.inl ht1
          · exact Or.inl hg0
          · exact Or.inr (Or.inl ⟨hg1, by rw [add_sub_cancel_right]; exact hg0⟩)
        · rw [if_neg ht1] at hxγ
          obtain ⟨_, hg2⟩ := htype2 γ hγ ht1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxγ
          rcases hxγ with rfl | rfl | rfl
          · exact Or.inl hg0
          · exact Or.inr (Or.inl ⟨hg1, by rw [add_sub_cancel_right]; exact hg0⟩)
          · refine Or.inr (Or.inr ⟨hg2, ?_, ?_⟩)
            · have : jw γ + 2 - 1 = jw γ + 1 := by ring
              rw [this]; exact hg1
            · rw [add_sub_cancel_right]; exact hg0
      rcases hclass α hα hxα with h1 | ⟨h10, h11⟩ | ⟨h10, h11, h12⟩ <;>
        rcases hclass β hβ hxβ with h2 | ⟨h20, h21⟩ | ⟨h20, h21, h22⟩
      · exact hαβ (h1.symm.trans h2)
      · rw [h20] at h1; exact hα_ne0 h1.symm
      · rw [h20] at h1; exact hα_ne0 h1.symm
      · rw [h10] at h2; exact hβ_ne0 h2.symm
      · exact hαβ (h11.symm.trans h21)
      · rw [h21] at h11; exact hα_ne0 h11.symm
      · rw [h10] at h2; exact hβ_ne0 h2.symm
      · rw [h11] at h21; exact hβ_ne0 h21.symm
      · exact hαβ (h12.symm.trans h22)
    have hbi_card : (NZ.biUnion T).card = 3 * NZ.card := by
      rw [Finset.card_biUnion hT_disj]
      simp [hT_card, mul_comm]
    have hD_le_m : NZ.card ≤ m := by
      have hle : (NZ.biUnion T).card ≤ (Finset.univ : Finset (ZMod (3 * m))).card := Finset.card_le_univ _
      rw [hbi_card, Finset.card_univ, ZMod.card] at hle
      omega
    by_cases hD_lt : NZ.card < m
    · exact le_trans (hspan_le_card NZ) (by omega)
    · have hD_eq : NZ.card = m := by omega
      have hpart_univ : NZ.biUnion T = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        rw [hbi_card, hD_eq, Finset.card_univ, ZMod.card]
      have hall_type1 : ∀ α ∈ NZ, ℓ (jw α - 1) = α := by
        intro α hα
        by_contra hne
        obtain ⟨hα0, hα1, _⟩ := hjw α hα
        obtain ⟨_, hα2⟩ := htype2 α hα hne
        have hα_ne0 : α ≠ 0 := (Finset.mem_erase.mp hα).1
        have hmem3 : jw α + 3 ∈ NZ.biUnion T := by rw [hpart_univ]; exact Finset.mem_univ _
        obtain ⟨β, hβ, h3β⟩ := Finset.mem_biUnion.mp hmem3
        have hβ_ne0 : β ≠ 0 := (Finset.mem_erase.mp hβ).1
        have hβα : β ≠ α := by
          intro hba; subst hba
          dsimp only [T] at h3β
          rw [if_neg hne] at h3β
          simp only [Finset.mem_insert, Finset.mem_singleton] at h3β
          rcases h3β with h | h | h
          · exact hneq_small (jw β) 0 3 (by omega) (by omega) (by omega) (by simpa using h.symm)
          · exact hneq_small (jw β) 1 3 (by omega) (by omega) (by omega) (by simpa using h.symm)
          · exact hneq_small (jw β) 2 3 (by omega) (by omega) (by omega) (by simpa using h.symm)
        have h2_in_α : jw α + 2 ∈ T α := by dsimp only [T]; rw [if_neg hne]; simp
        have h2_not_β : jw α + 2 ∉ T β := Finset.disjoint_left.mp (hT_disj hα hβ hβα.symm) h2_in_α
        have hℓ3 : ℓ (jw α + 3) = β := by
          obtain ⟨hb0, _, _⟩ := hjw β hβ
          dsimp only [T] at h3β h2_not_β
          by_cases ht1β : ℓ (jw β - 1) = β
          · rw [if_pos ht1β] at h3β h2_not_β
            simp only [Finset.mem_insert, Finset.mem_singleton] at h3β
            rcases h3β with h | h | h
            · rw [h]; exact ht1β
            · exfalso; apply h2_not_β
              have : jw α + 2 = jw β - 1 := by
                have := congrArg (fun z : ZMod (3 * m) => z - 1) h
                simpa [show jw α + 3 - 1 = jw α + 2 by ring] using this
              rw [this]; simp
            · exfalso; apply h2_not_β
              have : jw α + 2 = jw β := by
                have := congrArg (fun z : ZMod (3 * m) => z - 1) h
                simpa [show jw α + 3 - 1 = jw α + 2 by ring] using this
              rw [this]; simp
          · rw [if_neg ht1β] at h3β h2_not_β
            simp only [Finset.mem_insert, Finset.mem_singleton] at h3β
            rcases h3β with h | h | h
            · rw [h]; exact hb0
            · exfalso; apply h2_not_β
              have : jw α + 2 = jw β := by
                have := congrArg (fun z : ZMod (3 * m) => z - 1) h
                simpa [show jw α + 3 - 1 = jw α + 2 by ring] using this
              rw [this]; simp
            · exfalso; apply h2_not_β
              have : jw α + 2 = jw β + 1 := by
                have := congrArg (fun z : ZMod (3 * m) => z - 1) h
                simpa [show jw α + 3 - 1 = jw α + 2 by ring,
                       show jw β + 2 - 1 = jw β + 1 by ring] using this
              rw [this]; simp
        have hp2 := hP2 (jw α)
        dsimp only at hp2
        have h13 : jw α + 1 + 1 = jw α + 2 := by ring
        have h14 : jw α + 1 + 2 = jw α + 3 := by ring
        rw [h13, h14, hα0, hα1, hα2, hℓ3, add_zero, add_zero, zero_add, zero_add] at hp2
        rcases hp2 with h | h | h
        · exact hα_ne0 h
        · exact hβ_ne0 h
        · exact hβα h.symm
      have hNZ_ne : NZ.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨α0, hα0⟩ := hNZ_ne
      set z0 := jw α0 + 1
      -- Step +3 preserves membership in the jw γ + 1 orbit
      have hstep3 : ∀ x : ZMod (3 * m),
          (∃ γ ∈ NZ, x = jw γ + 1) → ∃ γ' ∈ NZ, x + 3 = jw γ' + 1 := by
        rintro x ⟨γ, hγ, rfl⟩
        have hmem : jw γ + 2 ∈ NZ.biUnion T := by rw [hpart_univ]; exact Finset.mem_univ _
        obtain ⟨γ', hγ', h2γ'⟩ := Finset.mem_biUnion.mp hmem
        have hγγ' : γ' ≠ γ := by
          intro hge; subst hge
          dsimp only [T] at h2γ'
          rw [if_pos (hall_type1 γ' hγ')] at h2γ'
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2γ'
          rcases h2γ' with h | h | h
          · exact hneq_small (jw γ' - 1) 0 3 (by omega) (by omega) (by omega)
              (by rw [Nat.cast_zero, add_zero, show jw γ' - 1 + ((3 : ℕ) : ZMod (3 * m)) = jw γ' + 2 by rw [Nat.cast_ofNat]; ring]; exact h.symm)
          · exact hneq_small (jw γ') 0 2 (by omega) (by omega) (by omega) (by simpa using h.symm)
          · exact hneq_small (jw γ') 1 2 (by omega) (by omega) (by omega) (by simpa using h.symm)
        have h1_in_γ : jw γ + 1 ∈ T γ := by dsimp only [T]; rw [if_pos (hall_type1 γ hγ)]; simp
        have h1_not_γ' : jw γ + 1 ∉ T γ' := Finset.disjoint_left.mp (hT_disj hγ hγ' hγγ'.symm) h1_in_γ
        dsimp only [T] at h2γ' h1_not_γ'
        rw [if_pos (hall_type1 γ' hγ')] at h2γ' h1_not_γ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at h2γ'
        rcases h2γ' with h | h | h
        · refine ⟨γ', hγ', ?_⟩
          have := congrArg (fun z : ZMod (3 * m) => z + 2) h
          simpa [show jw γ + 2 + 2 = jw γ + 1 + 3 by ring,
                 show jw γ' - 1 + 2 = jw γ' + 1 by ring] using this
        · exfalso; apply h1_not_γ'
          have : jw γ + 1 = jw γ' - 1 := by
            have := congrArg (fun z : ZMod (3 * m) => z - 1) h
            simpa [show jw γ + 2 - 1 = jw γ + 1 by ring] using this
          rw [this]; simp
        · exfalso; apply h1_not_γ'
          have : jw γ + 1 = jw γ' := by
            have := congrArg (fun z : ZMod (3 * m) => z - 1) h
            simpa [show jw γ + 2 - 1 = jw γ + 1 by ring] using this
          rw [this]; simp
      have hzero_orbit : ∀ q : ℕ, ∃ γ ∈ NZ, z0 + ((3 * q : ℕ) : ZMod (3 * m)) = jw γ + 1 := by
        intro q
        induction q with
        | zero => exact ⟨α0, hα0, by simp [z0]⟩
        | succ q ih =>
          obtain ⟨γ, hγ, hq⟩ := ih
          obtain ⟨γ', hγ', hq'⟩ := hstep3 _ ⟨γ, hγ, hq⟩
          refine ⟨γ', hγ', ?_⟩
          have : ((3 * (q + 1) : ℕ) : ZMod (3 * m)) = ((3 * q : ℕ) : ZMod (3 * m)) + 3 := by
            rw [Nat.mul_add, Nat.mul_one, Nat.cast_add]; rfl
          rw [this, ← add_assoc]; exact hq'
      set r0 := z0.val % 3
      have hr0_lt : r0 < 3 := Nat.mod_lt _ (by omega)
      have hdiff_orbit : ∀ q : Fin m,
          ((3 * q.val + r0 : ℕ) : ZMod (3 * m)) =
            z0 + ((3 * ((q.val + m - z0.val / 3) % m) : ℕ) : ZMod (3 * m)) := by
        intro q
        have hz_lt : z0.val < 3 * m := ZMod.val_lt z0
        set q0 := z0.val / 3
        have hz_eq : z0 = ((3 * q0 + r0 : ℕ) : ZMod (3 * m)) := by
          rw [show 3 * q0 + r0 = z0.val by omega, ZMod.natCast_zmod_val]
        rw [hz_eq, natCast_add_nat]
        apply zmod_eq_of_mod_eq
        have h1 : 3 * ((q.val + m - q0) % m) = (3 * (q.val + m - q0)) % (3 * m) :=
          (Nat.mul_mod_mul_left 3 (q.val + m - q0) m).symm
        rw [h1, Nat.add_mod_mod]
        have h2 : 3 * q0 + r0 + 3 * (q.val + m - q0) =
            3 * q.val + r0 + 3 * m := by omega
        rw [h2, Nat.add_mod_right]
      have h0_res : ∀ q : Fin m, ℓ ((3 * q.val + r0 : ℕ) : ZMod (3 * m)) = 0 := by
        intro q
        rw [hdiff_orbit q]
        obtain ⟨γ, hγ, hγeq⟩ := hzero_orbit ((q.val + m - z0.val / 3) % m)
        rw [hγeq]; exact (hjw γ hγ).2.1
      have hsum_prev_eq : ∑ q : Fin m, ℓ (((3 * q.val + r0 : ℕ) : ZMod (3 * m)) - 1) = ∑ α ∈ NZ, α := by
        let φ : Fin m → (A →ₗ[ZMod 2] ZMod 2) := fun q => ℓ (((3 * q.val + r0 : ℕ) : ZMod (3 * m)) - 1)
        have hget : ∀ q : Fin m, ∃ γ ∈ NZ, ((3 * q.val + r0 : ℕ) : ZMod (3 * m)) - 1 = jw γ := by
          intro q
          obtain ⟨γ, hγ, hγeq⟩ := hzero_orbit ((q.val + m - z0.val / 3) % m)
          exact ⟨γ, hγ, by rw [hdiff_orbit q, hγeq, add_sub_cancel_right]⟩
        have hmem_NZ : ∀ q : Fin m, φ q ∈ NZ := by
          intro q; obtain ⟨γ, hγ, hq⟩ := hget q
          dsimp only [φ]; rw [hq, (hjw γ hγ).1]; exact hγ
        have hinj_φ : Function.Injective φ := by
          intro q1 q2 heq
          obtain ⟨γ1, hγ1, h1⟩ := hget q1
          obtain ⟨γ2, hγ2, h2⟩ := hget q2
          have hγeq : γ1 = γ2 := by
            dsimp only [φ] at heq
            rw [h1, h2, (hjw γ1 hγ1).1, (hjw γ2 hγ2).1] at heq; exact heq
          subst hγeq
          have hzeq : ((3 * q1.val + r0 : ℕ) : ZMod (3 * m)) = ((3 * q2.val + r0 : ℕ) : ZMod (3 * m)) := by
            have := congrArg (fun z : ZMod (3 * m) => z + 1) (h1.trans h2.symm)
            simpa [sub_add_cancel] using this
          have hv := congrArg ZMod.val hzeq
          rw [ZMod.val_natCast_of_lt (by have := q1.isLt; omega),
              ZMod.val_natCast_of_lt (by have := q2.isLt; omega)] at hv
          exact Fin.ext (by omega)
        have himg : Finset.univ.image φ = NZ := by
          apply Finset.eq_of_subset_of_card_le
          · intro α hα; obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hα; exact hmem_NZ q
          · rw [Finset.card_image_of_injective _ hinj_φ, Finset.card_univ, Fintype.card_fin, hD_eq]
        rw [← himg, Finset.sum_image (fun q1 _ q2 _ h => hinj_φ h)]
      have hsum_zero : ∑ α ∈ NZ, α = 0 := by
        rw [← hsum_prev_eq]
        have hS0_eq : ∑ q : Fin m, ℓ ((3 * q.val + r0 : ℕ) : ZMod (3 * m)) = 0 :=
          Finset.sum_eq_zero fun q _ => h0_res q
        have hshift_sum : ∀ r1 : ℕ, r1 < 3 →
            ∑ q : Fin m, ℓ (((3 * q.val + r1 : ℕ) : ZMod (3 * m)) - 1) =
            ∑ q : Fin m, ℓ ((3 * q.val + (r1 + 2) % 3 : ℕ) : ZMod (3 * m)) := by
          intro r1 hr1
          by_cases hr10 : r1 = 0
          · subst hr10
            refine Finset.sum_bij (fun q _ => (⟨(q.val + m - 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m))
              (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
            · intro q1 _ q2 _ h
              have hv : (q1.val + m - 1) % m = (q2.val + m - 1) % m := congrArg Fin.val h
              have h1 := q1.isLt; have h2 := q2.isLt
              apply Fin.ext
              by_cases hq1 : q1.val = 0 <;> by_cases hq2 : q2.val = 0
              · omega
              · have e1 : (q1.val + m - 1) % m = m - 1 := by rw [hq1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
                have e2 : (q2.val + m - 1) % m = q2.val - 1 := by
                  rw [show q2.val + m - 1 = (q2.val - 1) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                omega
              · have e1 : (q1.val + m - 1) % m = q1.val - 1 := by
                  rw [show q1.val + m - 1 = (q1.val - 1) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                have e2 : (q2.val + m - 1) % m = m - 1 := by rw [hq2, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
                omega
              · have e1 : (q1.val + m - 1) % m = q1.val - 1 := by
                  rw [show q1.val + m - 1 = (q1.val - 1) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                have e2 : (q2.val + m - 1) % m = q2.val - 1 := by
                  rw [show q2.val + m - 1 = (q2.val - 1) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                omega
            · intro q' _
              refine ⟨⟨(q'.val + 1) % m, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
              apply Fin.ext; dsimp only
              have hq' := q'.isLt
              by_cases hlast : q'.val + 1 = m
              · rw [hlast, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
              · have hq1 : (q'.val + 1) % m = q'.val + 1 := Nat.mod_eq_of_lt (by omega)
                rw [hq1, show q'.val + 1 + m - 1 = q'.val + m by omega,
                    Nat.add_mod_right, Nat.mod_eq_of_lt hq']
            · intro q _
              congr 1
              have hq := q.isLt
              by_cases hq0 : q.val = 0
              · simp only [hq0, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
                have h2 : 3 * (m - 1) + 2 = 3 * m - 1 := by omega
                rw [show (0 + 2) % 3 = 2 by omega, h2, Nat.cast_zero, zero_sub]
                have h3 : ((3 * m - 1 : ℕ) : ZMod (3 * m)) + 1 = 0 := by
                  rw [natCast_add_one, show 3 * m - 1 + 1 = 3 * m by omega, ZMod.natCast_self]
                exact (eq_neg_of_add_eq_zero_left h3).symm
              · have e : (q.val + m - 1) % m = q.val - 1 := by
                  rw [show q.val + m - 1 = (q.val - 1) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                dsimp only
                rw [e, show (0 + 2) % 3 = 2 by omega, Nat.add_zero]
                have h3 : ((3 * (q.val - 1) + 2 : ℕ) : ZMod (3 * m)) + 1 = ((3 * q.val : ℕ) : ZMod (3 * m)) := by
                  rw [natCast_add_one]; congr 1; omega
                rw [← h3, add_sub_cancel_right]
          · refine Finset.sum_congr rfl fun q _ => ?_
            congr 1
            have h2 : (r1 + 2) % 3 = r1 - 1 := by omega
            rw [h2]
            have h3 : ((3 * q.val + (r1 - 1) : ℕ) : ZMod (3 * m)) + 1 =
                ((3 * q.val + r1 : ℕ) : ZMod (3 * m)) := by
              rw [natCast_add_one]; congr 1; omega
            rw [← h3, add_sub_cancel_right]
        rw [hshift_sum r0 hr0_lt]
        have hr0_cases : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 := by omega
        rcases hr0_cases with h | h | h
        · rw [h] at hS0_eq ⊢
          simp only [Nat.add_zero] at hS0_eq
          have e2 : (0 + 2) % 3 = 2 := by omega
          rw [e2]; exact (hP3.1.trans hP3.2).symm.trans hS0_eq
        · rw [h] at hS0_eq ⊢
          have e0 : (1 + 2) % 3 = 0 := by omega
          rw [e0]; simp only [Nat.add_zero]; exact hP3.1.trans hS0_eq
        · rw [h] at hS0_eq ⊢
          have e1 : (2 + 2) % 3 = 1 := by omega
          rw [e1]; exact hP3.2.trans hS0_eq
      have hα0_in : α0 ∈ Submodule.span (ZMod 2) ((NZ.erase α0 : Finset _) : Set (A →ₗ[ZMod 2] ZMod 2)) := by
        have hsplit := Finset.add_sum_erase NZ (fun α => α) hα0
        rw [hsum_zero] at hsplit
        have hα0_eq : α0 = ∑ α ∈ NZ.erase α0, α := by
          ext a
          have h0 := LinearMap.congr_fun hsplit a
          simp only [LinearMap.add_apply, LinearMap.zero_apply] at h0
          have hb : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
          exact hb (α0 a) ((∑ α ∈ NZ.erase α0, α) a) h0
        let S0 := NZ.erase α0
        have hmem_sum : ∑ α ∈ S0, α ∈ Submodule.span (ZMod 2) (S0 : Set (A →ₗ[ZMod 2] ZMod 2)) :=
          Submodule.sum_mem _ fun α hα => Submodule.subset_span hα
        rwa [← hα0_eq] at hmem_sum
      have hspan_eq : Uspan ≤ Submodule.span (ZMod 2) ((NZ.erase α0 : Finset _) : Set (A →ₗ[ZMod 2] ZMod 2)) := by
        rw [Submodule.span_le]
        intro α hα
        by_cases heq : α = α0
        · subst heq; exact hα0_in
        · exact Submodule.subset_span (Finset.mem_erase.mpr ⟨heq, hα⟩)
      have hcard_er : (NZ.erase α0).card = m - 1 := by
        rw [Finset.card_erase_of_mem hα0, hD_eq]
      exact le_trans (Submodule.finrank_mono hspan_eq) (by rw [← hcard_er]; exact hspan_le_card _)

lemma take_succ_finRange {d : ℕ} (n : ℕ) (hlt : n < d) :
    (List.finRange d).take (n + 1) = (List.finRange d).take n ++ [⟨n, hlt⟩] := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi1 hi2
    simp only [List.length_take, List.length_finRange] at hi1
    have hilt : i < n + 1 := by omega
    by_cases hit : i < n
    · rw [List.getElem_take, List.getElem_append_left (by simp; omega), List.getElem_take]
    · have hieq : i = n := by omega
      rw [List.getElem_take, List.getElem_append_right (by simp; omega)]
      have hlen : ((List.finRange d).take n).length = n := by simp; omega
      simp [hlen, hieq]

lemma foldl_run_zero {k d : ℕ} (ask : Fin d → ℕ → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin k → ZMod 2) (hx : ∀ j : Fin d, ask j 0 x = 0) :
    ∀ n : ℕ, ((List.finRange d).take n).foldl
      (fun t j => 2 * t + (if ask j t x = 0 then 0 else 1)) 0 = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hlt : n < d
    · rw [take_succ_finRange n hlt, List.foldl_append, ih]
      simp [hx ⟨n, hlt⟩]
    · have heq : (List.finRange d).take (n + 1) = (List.finRange d).take n := by
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      rw [heq]; exact ih

lemma foldl_run_inj {d : ℕ} (f g : Fin d → ZMod 2) :
    ((List.finRange d).foldl (fun t j => 2 * t + (if f j = 0 then 0 else 1)) 0 =
     (List.finRange d).foldl (fun t j => 2 * t + (if g j = 0 then 0 else 1)) 0) →
    f = g := by
  suffices ∀ (n : ℕ) (hn : n ≤ d),
      ((List.finRange d).take n).foldl (fun t j => 2 * t + (if f j = 0 then 0 else 1)) 0 =
      ((List.finRange d).take n).foldl (fun t j => 2 * t + (if g j = 0 then 0 else 1)) 0 →
      ∀ j : Fin d, j.val < n → f j = g j by
    intro heq
    funext j
    have htake : (List.finRange d).take d = List.finRange d := List.take_of_length_le (by simp)
    apply this d le_rfl (by rw [htake]; exact heq) j j.isLt
  intro n
  induction n with
  | zero => intro _ _ j hj; omega
  | succ n ih =>
    intro hn heq j hj
    have hlt : n < d := by omega
    rw [take_succ_finRange n hlt, List.foldl_append, List.foldl_append] at heq
    simp only [List.foldl_cons, List.foldl_nil] at heq
    set tf := ((List.finRange d).take n).foldl (fun t j => 2 * t + (if f j = 0 then 0 else 1)) 0
    set tg := ((List.finRange d).take n).foldl (fun t j => 2 * t + (if g j = 0 then 0 else 1)) 0
    have hbf : (if f ⟨n, hlt⟩ = 0 then 0 else 1) < 2 := by split_ifs <;> omega
    have hbg : (if g ⟨n, hlt⟩ = 0 then 0 else 1) < 2 := by split_ifs <;> omega
    have hteq : tf = tg := by omega
    have hbeq : (if f ⟨n, hlt⟩ = 0 then 0 else 1) = (if g ⟨n, hlt⟩ = 0 then 0 else 1) := by omega
    by_cases hjn : j.val < n
    · exact ih (by omega) hteq j hjn
    · have hjeq : j = ⟨n, hlt⟩ := Fin.ext (by dsimp only; omega)
      subst hjeq
      rcases z2_cases (f ⟨n, hlt⟩) with h1 | h1 <;> rcases z2_cases (g ⟨n, hlt⟩) with h2 | h2 <;>
        simp [h1, h2] at hbeq ⊢

-- Standalone helpers for rot, mix, step, M on Fin (3 * m)
def ixF {k : ℕ} (hk : 0 < k) (j : ℕ) : Fin k := ⟨j % k, Nat.mod_lt _ hk⟩

def rotF {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x (ixF hk (i.val + k - s % k))

def mixF {k : ℕ} (hk : 0 < k) (g : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + x (ixF hk (i.val + g)) + x (ixF hk (i.val + k - g % k))

def stepF {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + (1 + x (ixF hk (i.val + 1))) * x (ixF hk (i.val + 2))

lemma rotF_add {k : ℕ} (hk : 0 < k) (s : ℕ) (x y : Fin k → ZMod 2) :
    rotF hk s (x + y) = rotF hk s x + rotF hk s y := rfl

lemma mixF_add {k : ℕ} (hk : 0 < k) (g : ℕ) (x y : Fin k → ZMod 2) :
    mixF hk g (x + y) = mixF hk g x + mixF hk g y := by
  funext i; simp only [mixF, Pi.add_apply]; ring

def MF {k : ℕ} (hk : 0 < k) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun := fun x => mixF hk 1 (rotF hk 1 x)
  map_add' := fun x y => by rw [rotF_add, mixF_add]
  map_smul' := fun c x => by
    rcases z2_cases c with rfl | rfl
    · funext i; simp [mixF, rotF]
    · simp

lemma ixF_eq_zmod {k : ℕ} (hk : 0 < k) [NeZero k] (a : ℕ) (z : ZMod k)
    (hz : ((a : ℕ) : ZMod k) = z) :
    ixF hk a = ⟨z.val, ZMod.val_lt z⟩ := by
  apply Fin.ext; dsimp only [ixF]; rw [← hz, ZMod.val_natCast]

lemma zmod_sub_nat {k : ℕ} (hk : 0 < k) [NeZero k] (z : ZMod k) (s : ℕ) :
    ((z.val + k - s % k : ℕ) : ZMod k) = z - ((s : ℕ) : ZMod k) := by
  have hlt : s % k < k := Nat.mod_lt s hk
  have hadd : ((z.val + k - s % k : ℕ) : ZMod k) + ((s : ℕ) : ZMod k) = z := by
    have hsm : ((s : ℕ) : ZMod k) = ((s % k : ℕ) : ZMod k) := (ZMod.natCast_mod s k).symm
    rw [hsm, natCast_add_nat, show z.val + k - s % k + s % k = z.val + k by omega,
        Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  exact eq_sub_of_add_eq hadd

def zget {k : ℕ} [NeZero k] (x : Fin k → ZMod 2) (z : ZMod k) : ZMod 2 :=
  x ⟨z.val, ZMod.val_lt z⟩

lemma zget_natCast {k : ℕ} [NeZero k] (x : Fin k → ZMod 2) {a : ℕ} (ha : a < k) :
    zget x ((a : ℕ) : ZMod k) = x ⟨a, ha⟩ := by
  unfold zget; congr 1; exact Fin.ext (ZMod.val_natCast_of_lt ha)

lemma zget_fin {k : ℕ} [NeZero k] (x : Fin k → ZMod 2) (i : Fin k) :
    x i = zget x ((i.val : ℕ) : ZMod k) := (zget_natCast x i.isLt).symm

lemma rotF_zmod {k : ℕ} (hk : 0 < k) [NeZero k] (s : ℕ) (x : Fin k → ZMod 2) (z : ZMod k) :
    zget (rotF hk s x) z = zget x (z - (s : ZMod k)) := by
  unfold zget rotF
  rw [ixF_eq_zmod hk _ (z - (s : ZMod k)) (zmod_sub_nat hk z s)]

lemma mixF_zmod {k : ℕ} (hk : 0 < k) [NeZero k] (g : ℕ) (x : Fin k → ZMod 2) (z : ZMod k) :
    zget (mixF hk g x) z =
      zget x z + zget x (z + (g : ZMod k)) + zget x (z - (g : ZMod k)) := by
  unfold zget mixF
  have h1 : ((z.val + g : ℕ) : ZMod k) = z + ((g : ℕ) : ZMod k) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [ixF_eq_zmod hk _ (z + (g : ZMod k)) h1,
      ixF_eq_zmod hk _ (z - (g : ZMod k)) (zmod_sub_nat hk z g)]

lemma MF_zmod {k : ℕ} (hk : 0 < k) [NeZero k] (x : Fin k → ZMod 2) (z : ZMod k) :
    zget (MF hk x) z = zget x (z - 2) + zget x (z - 1) + zget x z := by
  change zget (mixF hk 1 (rotF hk 1 x)) z = _
  rw [mixF_zmod, rotF_zmod, rotF_zmod, rotF_zmod]
  simp only [Nat.cast_one]
  rw [show z + 1 - 1 = z by ring, show z - 1 - 1 = z - 2 by ring]; ring

lemma M2_zmod {k : ℕ} (hk : 0 < k) [NeZero k] (x : Fin k → ZMod 2) (z : ZMod k) :
    zget (mixF hk 2 (rotF hk 3 x)) z =
      zget (MF hk x) (z - 3) + zget (MF hk x) (z - 2) + zget (MF hk x) (z - 1) := by
  rw [mixF_zmod, rotF_zmod, rotF_zmod, rotF_zmod, MF_zmod, MF_zmod, MF_zmod]
  simp only [Nat.cast_ofNat]
  rw [show z + 2 - 3 = z - 1 by ring, show z - 2 - 3 = z - 5 by ring,
      show z - 3 - 2 = z - 5 by ring, show z - 3 - 1 = z - 4 by ring,
      show z - 2 - 2 = z - 4 by ring, show z - 2 - 1 = z - 3 by ring,
      show z - 1 - 2 = z - 3 by ring, show z - 1 - 1 = z - 2 by ring]
  have hb : ∀ a1 a2 a3 a4 a5 : ZMod 2,
      a3 + a1 + a5 = (a5 + a4 + a3) + (a4 + a3 + a2) + (a3 + a2 + a1) := by decide
  exact hb _ _ _ _ _

lemma MF_res_eq {m : ℕ} (hm : 0 < m) (hk : 0 < 3 * m) (x : Fin (3 * m) → ZMod 2) :
    (∑ q : Fin m, MF hk x ⟨3 * q.val, by have := q.isLt; omega⟩ =
     ∑ q : Fin m, MF hk x ⟨3 * q.val + 1, by have := q.isLt; omega⟩) ∧
    (∑ q : Fin m, MF hk x ⟨3 * q.val + 1, by have := q.isLt; omega⟩ =
     ∑ q : Fin m, MF hk x ⟨3 * q.val + 2, by have := q.isLt; omega⟩) := by
  haveI : NeZero (3 * m) := ⟨by omega⟩
  have hsum_all : ∀ (r0 : ℕ) (hr0 : r0 < 3),
      (∑ q : Fin m, MF hk x ⟨3 * q.val + r0, by have := q.isLt; omega⟩) =
        ∑ j : ZMod (3 * m), zget x j := by
    intro r0 hr0
    have hterm : ∀ q : Fin m, MF hk x ⟨3 * q.val + r0, by have := q.isLt; omega⟩ =
        zget x (((3 * q.val + r0 : ℕ) : ZMod (3 * m)) - 2) +
        zget x (((3 * q.val + r0 : ℕ) : ZMod (3 * m)) - 1) +
        zget x ((3 * q.val + r0 : ℕ) : ZMod (3 * m)) := by
      intro q
      rw [zget_fin (MF hk x) ⟨3 * q.val + r0, by have := q.isLt; omega⟩, MF_zmod]
    simp_rw [hterm]
    let e : Fin m × Fin 3 ≃ ZMod (3 * m) :=
      { toFun := fun p => ((3 * p.1.val + r0 : ℕ) : ZMod (3 * m)) - (p.2.val : ZMod (3 * m))
        invFun := fun z =>
          let w := (z - (r0 : ZMod (3 * m))).val
          let t := (3 - w % 3) % 3
          (⟨((w + t) / 3) % m, Nat.mod_lt _ hm⟩, ⟨t, Nat.mod_lt _ (by omega)⟩)
        left_inv := fun ⟨q, t⟩ => by
          dsimp only
          have hq := q.isLt; have ht := t.isLt
          have hsub : ((3 * q.val + r0 : ℕ) : ZMod (3 * m)) - (t.val : ZMod (3 * m)) - (r0 : ZMod (3 * m)) =
              ((3 * q.val : ℕ) : ZMod (3 * m)) - (t.val : ZMod (3 * m)) := by
            rw [Nat.cast_add]; abel
          rw [hsub]
          have hw_eq : (((3 * q.val : ℕ) : ZMod (3 * m)) - (t.val : ZMod (3 * m))).val =
              (3 * q.val + 3 * m - t.val) % (3 * m) := by
            have hcast : ((3 * q.val + 3 * m - t.val : ℕ) : ZMod (3 * m)) =
                ((3 * q.val : ℕ) : ZMod (3 * m)) - (t.val : ZMod (3 * m)) := by
              have hadd : ((3 * q.val + 3 * m - t.val : ℕ) : ZMod (3 * m)) + (t.val : ZMod (3 * m)) =
                  ((3 * q.val : ℕ) : ZMod (3 * m)) := by
                rw [natCast_add_nat, show 3 * q.val + 3 * m - t.val + t.val = 3 * q.val + 3 * m by omega,
                    Nat.cast_add, ZMod.natCast_self, add_zero]
              exact eq_sub_of_add_eq hadd
            rw [← hcast, ZMod.val_natCast]
          rw [hw_eq]
          apply Prod.ext
          · apply Fin.ext; dsimp only
            by_cases ht0 : t.val = 0
            · have h1 : (3 * q.val + 3 * m - t.val) % (3 * m) = 3 * q.val := by
                rw [ht0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [h1]
              have h2 : (3 - 3 * q.val % 3) % 3 = 0 := by omega
              rw [h2]; simp [Nat.mod_eq_of_lt hq]
            · by_cases hq0 : q.val = 0
              · have h1 : (3 * q.val + 3 * m - t.val) % (3 * m) = 3 * m - t.val := by
                  rw [hq0, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
                rw [h1]
                have h2 : (3 - (3 * m - t.val) % 3) % 3 = t.val := by omega
                rw [h2, show 3 * m - t.val + t.val = 3 * m by omega,
                    Nat.mul_div_cancel_left m (by omega), Nat.mod_self, hq0]
              · have h1 : (3 * q.val + 3 * m - t.val) % (3 * m) = 3 * q.val - t.val := by
                  rw [show 3 * q.val + 3 * m - t.val = (3 * q.val - t.val) + 3 * m by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                rw [h1]
                have h2 : (3 - (3 * q.val - t.val) % 3) % 3 = t.val := by omega
                rw [h2, show 3 * q.val - t.val + t.val = 3 * q.val by omega,
                    Nat.mul_div_cancel_left q.val (by omega), Nat.mod_eq_of_lt hq]
          · apply Fin.ext; dsimp only
            by_cases ht0 : t.val = 0
            · have h1 : (3 * q.val + 3 * m - t.val) % (3 * m) = 3 * q.val := by
                rw [ht0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [h1]; omega
            · by_cases hq0 : q.val = 0
              · have h1 : (3 * q.val + 3 * m - t.val) % (3 * m) = 3 * m - t.val := by
                  rw [hq0, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
                rw [h1]; omega
              · have h1 : (3 * q.val + 3 * m - t.val) % (3 * m) = 3 * q.val - t.val := by
                  rw [show 3 * q.val + 3 * m - t.val = (3 * q.val - t.val) + 3 * m by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                rw [h1]; omega
        right_inv := fun z => by
          dsimp only
          set w := (z - (r0 : ZMod (3 * m))).val
          set t := (3 - w % 3) % 3
          have h3div : 3 ∣ w + t := by omega
          have h3mul : 3 * (((w + t) / 3) % m) = (w + t) % (3 * m) := by
            rw [← Nat.mul_mod_mul_left, Nat.mul_div_cancel' h3div]
          rw [Nat.cast_add, h3mul, ZMod.natCast_mod, Nat.cast_add]
          have hw_cast : (w : ZMod (3 * m)) = z - (r0 : ZMod (3 * m)) := ZMod.natCast_zmod_val _
          rw [hw_cast]; abel }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_three]
    dsimp only [e, Equiv.coe_fn_mk]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, sub_zero, Nat.cast_one, Nat.cast_ofNat]
    ring
  exact ⟨(hsum_all 0 (by omega)).trans (hsum_all 1 (by omega)).symm,
         (hsum_all 1 (by omega)).trans (hsum_all 2 (by omega)).symm⟩

lemma ker_MF_finrank {m : ℕ} (hm : 0 < m) (hk : 0 < 3 * m) :
    Module.finrank (ZMod 2) (LinearMap.ker (MF hk)) = 2 := by
  haveI : NeZero (3 * m) := ⟨by omega⟩
  let ψ : (Fin 2 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker (MF hk) :=
    { toFun := fun ab =>
        ⟨fun i => if i.val % 3 = 0 then ab 0 else if i.val % 3 = 1 then ab 1 else ab 0 + ab 1, by
          rw [LinearMap.mem_ker]
          funext i
          rw [zget_fin (MF hk _) i, MF_zmod]
          unfold zget
          have hval0 : ((i.val : ℕ) : ZMod (3 * m)).val % 3 = i.val % 3 := by
            rw [ZMod.val_natCast_of_lt i.isLt]
          have hval1 : (((i.val : ℕ) : ZMod (3 * m)) - 1).val % 3 = (i.val + 2) % 3 := by
            have h1 := zmod_sub_nat hk ((i.val : ℕ) : ZMod (3 * m)) 1
            rw [ZMod.val_natCast_of_lt i.isLt, Nat.cast_one] at h1
            rw [← h1, ZMod.val_natCast, Nat.mod_mod_of_dvd _ ⟨m, rfl⟩]
            have hm1 : 1 % (3 * m) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [hm1]; omega
          have hval2 : (((i.val : ℕ) : ZMod (3 * m)) - 2).val % 3 = (i.val + 1) % 3 := by
            have h1 := zmod_sub_nat hk ((i.val : ℕ) : ZMod (3 * m)) 2
            rw [ZMod.val_natCast_of_lt i.isLt, Nat.cast_ofNat] at h1
            rw [← h1, ZMod.val_natCast, Nat.mod_mod_of_dvd _ ⟨m, rfl⟩]
            have hm2 : 2 % (3 * m) = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hm2]; omega
          dsimp only
          rw [hval0, hval1, hval2]
          have hmod : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
          rcases hmod with hm0 | hm1 | hm2
          · have e1 : (i.val + 1) % 3 = 1 := by omega
            have e2 : (i.val + 2) % 3 = 2 := by omega
            rw [hm0, e1, e2]; simp only [↓reduceIte, Nat.one_ne_zero, show 2 ≠ 0 by omega, show 2 ≠ 1 by omega]
            have hb : ∀ a b : ZMod 2, b + (a + b) + a = 0 := by decide
            exact hb (ab 0) (ab 1)
          · have e1 : (i.val + 1) % 3 = 2 := by omega
            have e2 : (i.val + 2) % 3 = 0 := by omega
            rw [hm1, e1, e2]; simp only [↓reduceIte, Nat.one_ne_zero, show 2 ≠ 0 by omega, show 2 ≠ 1 by omega]
            have hb : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
            exact hb (ab 0) (ab 1)
          · have e1 : (i.val + 1) % 3 = 0 := by omega
            have e2 : (i.val + 2) % 3 = 1 := by omega
            rw [hm2, e1, e2]; simp only [↓reduceIte, Nat.one_ne_zero, show 2 ≠ 0 by omega, show 2 ≠ 1 by omega]
            have hb : ∀ a b : ZMod 2, a + b + (a + b) = 0 := by decide
            exact hb (ab 0) (ab 1)⟩
      map_add' := fun u v => by
        apply Subtype.ext; funext i; simp only [Submodule.coe_add, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c u => by
        apply Subtype.ext; funext i
        rcases z2_cases c with rfl | rfl <;> simp }
  have hψ_bij : Function.Bijective ψ := by
    constructor
    · intro u v h
      have hv := congrArg Subtype.val h
      funext j
      fin_cases j
      · have := congrFun hv ⟨0, by omega⟩; simpa [ψ] using this
      · have := congrFun hv ⟨1, by omega⟩; simpa [ψ] using this
    · rintro ⟨x, hx⟩
      refine ⟨fun j => if j = 0 then x ⟨0, by omega⟩ else x ⟨1, by omega⟩, ?_⟩
      apply Subtype.ext
      have hstep_x : ∀ (n : ℕ) (hn : n < 3 * m),
          x ⟨n, hn⟩ = if n % 3 = 0 then x ⟨0, by omega⟩ else
            if n % 3 = 1 then x ⟨1, by omega⟩ else x ⟨0, by omega⟩ + x ⟨1, by omega⟩ := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ih =>
          intro hn
          by_cases h0 : n = 0
          · subst h0; simp
          · by_cases h1 : n = 1
            · subst h1; simp
            · have hM0 := congrFun (LinearMap.mem_ker.mp hx) ⟨n, hn⟩
              rw [zget_fin (MF hk x) ⟨n, hn⟩, MF_zmod] at hM0
              unfold zget at hM0
              have hv0 : ((n : ℕ) : ZMod (3 * m)).val = n := ZMod.val_natCast_of_lt hn
              have hv1 : (((n : ℕ) : ZMod (3 * m)) - 1).val = n - 1 := by
                have : ((n - 1 : ℕ) : ZMod (3 * m)) = ((n : ℕ) : ZMod (3 * m)) - 1 := by
                  have hadd : ((n - 1 : ℕ) : ZMod (3 * m)) + 1 = ((n : ℕ) : ZMod (3 * m)) := by
                    rw [natCast_add_one, show n - 1 + 1 = n by omega]
                  exact eq_sub_of_add_eq hadd
                rw [← this, ZMod.val_natCast_of_lt (by omega)]
              have hv2 : (((n : ℕ) : ZMod (3 * m)) - 2).val = n - 2 := by
                have : ((n - 2 : ℕ) : ZMod (3 * m)) = ((n : ℕ) : ZMod (3 * m)) - 2 := by
                  have hadd : ((n - 2 : ℕ) : ZMod (3 * m)) + 2 = ((n : ℕ) : ZMod (3 * m)) := by
                    rw [natCast_add_two, show n - 2 + 2 = n by omega]
                  exact eq_sub_of_add_eq hadd
                rw [← this, ZMod.val_natCast_of_lt (by omega)]
              have hx_sum : x ⟨n - 2, by omega⟩ + x ⟨n - 1, by omega⟩ + x ⟨n, hn⟩ = 0 := by
                have hfin0 : (⟨((n : ℕ) : ZMod (3 * m)).val, ZMod.val_lt _⟩ : Fin (3 * m)) = ⟨n, hn⟩ := Fin.ext hv0
                have hfin1 : (⟨(((n : ℕ) : ZMod (3 * m)) - 1).val, ZMod.val_lt _⟩ : Fin (3 * m)) = ⟨n - 1, by omega⟩ := Fin.ext hv1
                have hfin2 : (⟨(((n : ℕ) : ZMod (3 * m)) - 2).val, ZMod.val_lt _⟩ : Fin (3 * m)) = ⟨n - 2, by omega⟩ := Fin.ext hv2
                rw [hfin0, hfin1, hfin2] at hM0
                exact hM0
              rw [ih (n - 2) (by omega) (by omega), ih (n - 1) (by omega) (by omega)] at hx_sum
              have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
              rcases hmod with hm0 | hm1 | hm2
              · have e1 : (n - 1) % 3 = 2 := by omega
                have e2 : (n - 2) % 3 = 1 := by omega
                rw [hm0]; simp only [↓reduceIte]
                rw [e1, e2] at hx_sum
                simp only [Nat.one_ne_zero, ↓reduceIte, show 2 ≠ 0 by omega, show 2 ≠ 1 by omega] at hx_sum
                have hb : ∀ a b c : ZMod 2, b + (a + b) + c = 0 → c = a := by decide
                exact hb _ _ _ hx_sum
              · have e1 : (n - 1) % 3 = 0 := by omega
                have e2 : (n - 2) % 3 = 2 := by omega
                rw [hm1]; simp only [Nat.one_ne_zero, ↓reduceIte]
                rw [e1, e2] at hx_sum
                simp only [↓reduceIte, show 2 ≠ 0 by omega, show 2 ≠ 1 by omega] at hx_sum
                have hb : ∀ a b c : ZMod 2, (a + b) + a + c = 0 → c = b := by decide
                exact hb _ _ _ hx_sum
              · have e1 : (n - 1) % 3 = 1 := by omega
                have e2 : (n - 2) % 3 = 0 := by omega
                rw [hm2]; simp only [show 2 ≠ 0 by omega, show 2 ≠ 1 by omega, ↓reduceIte]
                rw [e1, e2] at hx_sum
                simp only [↓reduceIte, Nat.one_ne_zero] at hx_sum
                have hb : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b := by decide
                exact hb _ _ _ hx_sum
      funext i; dsimp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
      simpa using (hstep_x i.val i.isLt).symm
  have heq := LinearEquiv.finrank_eq (LinearEquiv.ofBijective ψ hψ_bij)
  simpa [Module.finrank_fin_fun] using heq.symm

lemma stepF_polar {k : ℕ} (hk : 0 < k) (y1 y2 r0 : Fin k → ZMod 2) (i : Fin k) :
    stepF hk (y1 + y2 + r0) i + stepF hk (y1 + r0) i + stepF hk (y2 + r0) i + stepF hk r0 i =
      y1 (ixF hk (i.val + 1)) * y2 (ixF hk (i.val + 2)) +
      y2 (ixF hk (i.val + 1)) * y1 (ixF hk (i.val + 2)) := by
  simp only [stepF, Pi.add_apply]
  have hb : ∀ a1 a2 a0 b1 b2 b0 c1 c2 c0 : ZMod 2,
      (a1 + a2 + a0 + (1 + (b1 + b2 + b0)) * (c1 + c2 + c0)) +
      (a1 + a0 + (1 + (b1 + b0)) * (c1 + c0)) +
      (a2 + a0 + (1 + (b2 + b0)) * (c2 + c0)) +
      (a0 + (1 + b0) * c0) = b1 * c2 + b2 * c1 := by decide
  exact hb _ _ _ _ _ _ _ _ _

lemma admits_of_ker_polar {k d : ℕ}
    (target : (Fin k → ZMod 2) → Bool → Fin k → ZMod 2)
    (Q : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (hpolar : ∀ u ∈ LinearMap.ker Q, ∀ v ∈ LinearMap.ker Q,
      ∀ (x0 : Fin k → ZMod 2) (b : Bool) (i : Fin k),
        target (x0 + u + v) b i + target (x0 + u) b i + target (x0 + v) b i + target x0 b i = 0) :
    let run := fun (ask : Fin d → ℕ → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)) (x : Fin k → ZMod 2) =>
      (List.finRange d).foldl (fun t j => 2 * t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      (readout : ℕ → Bool → Fin k → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      (bias : ℕ → Bool → Fin k → ZMod 2),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i := by
  classical
  intro run
  let U := LinearMap.ker Q
  obtain ⟨V, hUV⟩ := Submodule.exists_isCompl U
  let eUV : (U × V) ≃ₗ[ZMod 2] (Fin k → ZMod 2) := Submodule.prodEquivOfIsCompl U V hUV
  let proj : (Fin k → ZMod 2) →ₗ[ZMod 2] U := (LinearMap.fst (ZMod 2) U V).comp eUV.symm.toLinearMap
  have hproj_U : ∀ u : U, proj u.val = u := by
    intro u
    have h1 : eUV (u, 0) = u.val := by simp [eUV]
    have h2 : eUV.symm u.val = (u, 0) := by rw [← h1, LinearEquiv.symm_apply_apply]
    simp [proj, h2]
  let ask : Fin d → ℕ → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) := fun j _ =>
    { toFun := fun x => Q x j
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hrun_iff : ∀ x y : Fin k → ZMod 2, run ask x = run ask y → x - y ∈ U := by
    intro x y hxy
    have hQeq : Q x = Q y := foldl_run_inj (Q x) (Q y) hxy
    rw [LinearMap.mem_ker, map_sub, hQeq, sub_self]
  let rep : ℕ → (Fin k → ZMod 2) := fun t => if ht : ∃ x, run ask x = t then ht.choose else 0
  let linLeaf : ℕ → Bool → Fin k → (U →ₗ[ZMod 2] ZMod 2) := fun t b i =>
    { toFun := fun u => target (rep t + u.val) b i + target (rep t) b i
      map_add' := fun u1 u2 => by
        have hp := hpolar u1.val u1.property u2.val u2.property (rep t) b i
        rw [add_assoc (rep t) u1.val u2.val] at hp
        have hb : ∀ a b1 b2 c : ZMod 2, a + b1 + b2 + c = 0 → a + c = (b1 + c) + (b2 + c) := by decide
        exact hb _ _ _ _ hp
      map_smul' := fun c u => by
        rcases z2_cases c with rfl | rfl
        · simp [z2_add_self]
        · simp }
  let readout : ℕ → Bool → Fin k → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) := fun t b i =>
    (linLeaf t b i).comp proj
  let bias : ℕ → Bool → Fin k → ZMod 2 := fun t b i => target (rep t) b i + readout t b i (rep t)
  refine ⟨ask, readout, bias, fun x b i => ?_⟩
  set t := run ask x
  have htx : ∃ y, run ask y = t := ⟨x, rfl⟩
  have hrep_run : run ask (rep t) = t := by dsimp only [rep]; rw [dif_pos htx]; exact htx.choose_spec
  have hdiff_U : x - rep t ∈ U := hrun_iff x (rep t) hrep_run.symm
  have hx_eq : x = rep t + (x - rep t) := by abel
  have hread : readout t b i x + bias t b i = readout t b i (x - rep t) + target (rep t) b i := by
    dsimp only [bias]
    conv_lhs => rw [hx_eq, map_add]
    have hb : ∀ a b1 c : ZMod 2, a + b1 + (c + a) = b1 + c := by decide
    exact hb _ _ _
  rw [hread]
  have hval : readout t b i (x - rep t) = target (rep t + (x - rep t)) b i + target (rep t) b i := by
    dsimp only [readout, LinearMap.comp_apply]
    rw [hproj_U ⟨x - rep t, hdiff_U⟩]; rfl
  rw [hval, ← hx_eq]
  have hb : ∀ a c : ZMod 2, a = a + c + c := by decide
  exact hb _ _

end PEqualNP.Outside.L_meta_25928

open PEqualNP.Outside.L_meta_25928 in
theorem PEqualNP.Outside.L_meta_25928 : ∀ (k : ℕ) (hk : 0 < k), 3 ∣ k →
  let h := k
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let W := Fin k → F
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val+g)) + x (ix (i.val+k-g % k))
  let step := fun (x : W) (i : Fin k) => x i + (1+x (ix (i.val+1))) * x (ix (i.val+2))
  ∀ (start d : ℕ) (row col c₁ c₂ : W),
    let target := fun (x : W) (b : Bool) (i : Fin h) =>
      let site := ix (start + i.val)
      if b then step (mix 2 (rot 3 x + col)) site + rot 4 x site + c₂ site
      else step (mix 1 (rot 1 x + row)) site + x site + c₁ site
    admits k target d ↔ (if k = 3 then 0 else 2*(k/3)-1) ≤ d := by
  classical
  intro k hk h3 h F admits W ix rot mix step start d row col c₁ c₂ target
  obtain ⟨m, rfl⟩ := h3
  have hm_pos : 0 < m := by omega
  haveI : NeZero (3 * m) := ⟨by omega⟩
  have htarget_polar_false : ∀ (x0 u v : W) (i : Fin (3 * m)),
      target (x0 + u + v) false i + target (x0 + u) false i + target (x0 + v) false i + target x0 false i =
        MF hk u (ixF hk ((ixF hk (start + i.val)).val + 1)) * MF hk v (ixF hk ((ixF hk (start + i.val)).val + 2)) +
        MF hk v (ixF hk ((ixF hk (start + i.val)).val + 1)) * MF hk u (ixF hk ((ixF hk (start + i.val)).val + 2)) := by
    intro x0 u v i
    set site := ixF hk (start + i.val)
    change (stepF hk (mixF hk 1 (rotF hk 1 (x0 + u + v) + row)) site + (x0 + u + v) site + c₁ site) +
      (stepF hk (mixF hk 1 (rotF hk 1 (x0 + u) + row)) site + (x0 + u) site + c₁ site) +
      (stepF hk (mixF hk 1 (rotF hk 1 (x0 + v) + row)) site + (x0 + v) site + c₁ site) +
      (stepF hk (mixF hk 1 (rotF hk 1 x0 + row)) site + x0 site + c₁ site) = _
    have h1 : mixF hk 1 (rotF hk 1 (x0 + u + v) + row) = MF hk u + MF hk v + mixF hk 1 (rotF hk 1 x0 + row) := by
      change _ = mixF hk 1 (rotF hk 1 u) + mixF hk 1 (rotF hk 1 v) + _
      rw [rotF_add, rotF_add, mixF_add, mixF_add, mixF_add, mixF_add]; abel
    have h2 : mixF hk 1 (rotF hk 1 (x0 + u) + row) = MF hk u + mixF hk 1 (rotF hk 1 x0 + row) := by
      change _ = mixF hk 1 (rotF hk 1 u) + _
      rw [rotF_add, mixF_add, mixF_add, mixF_add]; abel
    have h3 : mixF hk 1 (rotF hk 1 (x0 + v) + row) = MF hk v + mixF hk 1 (rotF hk 1 x0 + row) := by
      change _ = mixF hk 1 (rotF hk 1 v) + _
      rw [rotF_add, mixF_add, mixF_add, mixF_add]; abel
    rw [h1, h2, h3, ← stepF_polar hk (MF hk u) (MF hk v) (mixF hk 1 (rotF hk 1 x0 + row)) site]
    dsimp only [W, F] at x0 u v ⊢
    simp only [Pi.add_apply]
    have hb : ∀ s1 s2 s3 s4 a b c e : ZMod 2,
        (s1 + (a + b + c) + e) + (s2 + (a + b) + e) + (s3 + (a + c) + e) + (s4 + a + e) =
          s1 + s2 + s3 + s4 := by decide
    exact hb _ _ _ _ _ _ _ _
  have htarget_polar_true : ∀ (x0 u v : W) (i : Fin (3 * m)),
      target (x0 + u + v) true i + target (x0 + u) true i + target (x0 + v) true i + target x0 true i =
        mixF hk 2 (rotF hk 3 u) (ixF hk ((ixF hk (start + i.val)).val + 1)) *
          mixF hk 2 (rotF hk 3 v) (ixF hk ((ixF hk (start + i.val)).val + 2)) +
        mixF hk 2 (rotF hk 3 v) (ixF hk ((ixF hk (start + i.val)).val + 1)) *
          mixF hk 2 (rotF hk 3 u) (ixF hk ((ixF hk (start + i.val)).val + 2)) := by
    intro x0 u v i
    set site := ixF hk (start + i.val)
    change (stepF hk (mixF hk 2 (rotF hk 3 (x0 + u + v) + col)) site + rotF hk 4 (x0 + u + v) site + c₂ site) +
      (stepF hk (mixF hk 2 (rotF hk 3 (x0 + u) + col)) site + rotF hk 4 (x0 + u) site + c₂ site) +
      (stepF hk (mixF hk 2 (rotF hk 3 (x0 + v) + col)) site + rotF hk 4 (x0 + v) site + c₂ site) +
      (stepF hk (mixF hk 2 (rotF hk 3 x0 + col)) site + rotF hk 4 x0 site + c₂ site) = _
    have h1 : mixF hk 2 (rotF hk 3 (x0 + u + v) + col) =
        mixF hk 2 (rotF hk 3 u) + mixF hk 2 (rotF hk 3 v) + mixF hk 2 (rotF hk 3 x0 + col) := by
      rw [rotF_add, rotF_add, mixF_add, mixF_add, mixF_add, mixF_add]; abel
    have h2 : mixF hk 2 (rotF hk 3 (x0 + u) + col) =
        mixF hk 2 (rotF hk 3 u) + mixF hk 2 (rotF hk 3 x0 + col) := by
      rw [rotF_add, mixF_add, mixF_add, mixF_add]; abel
    have h3 : mixF hk 2 (rotF hk 3 (x0 + v) + col) =
        mixF hk 2 (rotF hk 3 v) + mixF hk 2 (rotF hk 3 x0 + col) := by
      rw [rotF_add, mixF_add, mixF_add, mixF_add]; abel
    rw [h1, h2, h3, ← stepF_polar hk (mixF hk 2 (rotF hk 3 u)) (mixF hk 2 (rotF hk 3 v))
        (mixF hk 2 (rotF hk 3 x0 + col)) site]
    have hrot : ∀ a b : W, rotF hk 4 (a + b) site = rotF hk 4 a site + rotF hk 4 b site := fun _ _ => rfl
    rw [hrot (x0 + u) v, hrot x0 u, hrot x0 v]
    have hb : ∀ s1 s2 s3 s4 a b c e : ZMod 2,
        (s1 + (a + b + c) + e) + (s2 + (a + b) + e) + (s3 + (a + c) + e) + (s4 + a + e) =
          s1 + s2 + s3 + s4 := by decide
    exact hb _ _ _ _ _ _ _ _
  by_cases hm1 : m = 1
  · subst hm1
    simp only [Nat.mul_one, ↓reduceIte, Nat.zero_le, iff_true]
    refine admits_of_ker_polar target (0 : W →ₗ[F] (Fin d → F)) fun u _ v _ x0 b i => ?_
    have hconst_M : ∀ (z : Fin 3 → ZMod 2) (j1 j2 : Fin 3), MF hk z j1 = MF hk z j2 := by
      intro z j1 j2
      have heq : ∀ j : Fin 3, MF hk z j = z 0 + z 1 + z 2 := by
        intro j; fin_cases j <;> simp [MF, mixF, rotF, ixF] <;> ring
      rw [heq j1, heq j2]
    have hconst_M2 : ∀ (z : Fin 3 → ZMod 2) (j1 j2 : Fin 3),
        mixF hk 2 (rotF hk 3 z) j1 = mixF hk 2 (rotF hk 3 z) j2 := by
      intro z j1 j2
      have heq : ∀ j : Fin 3, mixF hk 2 (rotF hk 3 z) j = z 0 + z 1 + z 2 := by
        intro j; fin_cases j <;> simp [mixF, rotF, ixF] <;> ring
      rw [heq j1, heq j2]
    cases b
    · rw [htarget_polar_false,
          hconst_M u (ixF hk ((ixF hk (start + i.val)).val + 1)) 0,
          hconst_M v (ixF hk ((ixF hk (start + i.val)).val + 2)) 0,
          hconst_M v (ixF hk ((ixF hk (start + i.val)).val + 1)) 0,
          hconst_M u (ixF hk ((ixF hk (start + i.val)).val + 2)) 0,
          mul_comm (MF hk v 0), z2_add_self]
    · rw [htarget_polar_true,
          hconst_M2 u (ixF hk ((ixF hk (start + i.val)).val + 1)) 0,
          hconst_M2 v (ixF hk ((ixF hk (start + i.val)).val + 2)) 0,
          hconst_M2 v (ixF hk ((ixF hk (start + i.val)).val + 1)) 0,
          hconst_M2 u (ixF hk ((ixF hk (start + i.val)).val + 2)) 0,
          mul_comm (mixF hk 2 (rotF hk 3 v) 0), z2_add_self]
  · have hm2 : 2 ≤ m := by omega
    have hne3 : 3 * m ≠ 3 := by omega
    have hdiv3 : 3 * m / 3 = m := Nat.mul_div_cancel_left m (by omega)
    rw [if_neg hne3, hdiv3]
    constructor
    · -- Lower bound: admits → 2 * m - 1 ≤ d
      rintro ⟨ask, readout, bias, hok⟩
      let Q : W →ₗ[F] (Fin d → F) :=
        { toFun := fun x j => ask j 0 x
          map_add' := fun x y => by funext j; simp
          map_smul' := fun c x => by funext j; simp }
      let U := LinearMap.ker Q
      have hrun0 : ∀ x ∈ U, (List.finRange d).foldl
          (fun t j => 2 * t + (if ask j t x = 0 then 0 else 1)) 0 = 0 := by
        intro x hx
        have hxj : ∀ j : Fin d, ask j 0 x = 0 := fun j => congrFun (LinearMap.mem_ker.mp hx) j
        have htake : (List.finRange d).take d = List.finRange d := List.take_of_length_le (by simp)
        rw [← htake]
        exact foldl_run_zero ask x hxj d
      have hpolar0 : ∀ u ∈ U, ∀ v ∈ U, ∀ (b : Bool) (i : Fin (3 * m)),
          target (u + v) b i + target u b i + target v b i + target 0 b i = 0 := by
        intro u hu v hv b i
        have h0 : (0 : W) ∈ U := Submodule.zero_mem U
        have huv : u + v ∈ U := Submodule.add_mem U hu hv
        rw [hok (u + v) b i, hok u b i, hok v b i, hok 0 b i]
        dsimp only
        rw [hrun0 (u + v) huv, hrun0 u hu, hrun0 v hv, hrun0 0 h0, map_add, map_zero, zero_add]
        have hb : ∀ a c e : ZMod 2, a + c + e + (a + e) + (c + e) + e = 0 := by decide
        exact hb _ _ _
      let A := U.map (MF hk)
      let ℓ : ZMod (3 * m) → (A →ₗ[F] F) := fun j =>
        { toFun := fun a => zget a.val j
          map_add' := fun a1 a2 => by simp [zget]
          map_smul' := fun c a => by simp [zget] }
      have hinj_A : ∀ a : A, (∀ j : ZMod (3 * m), ℓ j a = 0) → a = 0 := by
        intro a ha
        apply Subtype.ext; funext i
        have h0 : zget a.val ((i.val : ℕ) : ZMod (3 * m)) = 0 := ha ((i.val : ℕ) : ZMod (3 * m))
        rw [zget_natCast a.val i.isLt] at h0
        exact h0
      have hsite_surj : ∀ j : ZMod (3 * m), ∃ i : Fin (3 * m),
          ixF hk (start + i.val) = ⟨j.val, ZMod.val_lt j⟩ := by
        intro j
        let i : Fin (3 * m) := ⟨(j - (start : ZMod (3 * m))).val, ZMod.val_lt _⟩
        refine ⟨i, ixF_eq_zmod hk _ j ?_⟩
        dsimp only [i]; rw [Nat.cast_add, ZMod.natCast_zmod_val]; abel
      have hix_add : ∀ (j : ZMod (3 * m)) (t : ℕ),
          ixF hk (j.val + t) = ⟨(j + (t : ZMod (3 * m))).val, ZMod.val_lt _⟩ := by
        intro j t
        exact ixF_eq_zmod hk _ (j + (t : ZMod (3 * m))) (by rw [Nat.cast_add, ZMod.natCast_zmod_val])
      have hix_zget : ∀ (x : W) (j : ZMod (3 * m)) (t : ℕ),
          x (ixF hk (j.val + t)) = zget x (j + (t : ZMod (3 * m))) := by
        intro x j t; unfold zget; rw [hix_add j t]
      have hP1 : ∀ j : ZMod (3 * m), ℓ j = 0 ∨ ℓ (j + 1) = 0 ∨ ℓ j = ℓ (j + 1) := by
        intro j
        rw [← wedge_zero_iff]
        rintro ⟨_, u, hu, rfl⟩ ⟨_, v, hv, rfl⟩
        obtain ⟨i, hi⟩ := hsite_surj (j - 1)
        have hp := hpolar0 u hu v hv false i
        have hp' := htarget_polar_false 0 u v i
        rw [zero_add, zero_add] at hp'
        rw [hp', hi, hix_zget (MF hk u), hix_zget (MF hk v),
            hix_zget (MF hk v), hix_zget (MF hk u)] at hp
        have ha1 : j - 1 + ((1 : ℕ) : ZMod (3 * m)) = j := by simp
        have ha2 : j - 1 + ((2 : ℕ) : ZMod (3 * m)) = j + 1 := by rw [Nat.cast_ofNat]; ring
        rw [ha1, ha2] at hp
        exact hp
      have hP2 : ∀ j : ZMod (3 * m),
          let C := fun t : ZMod (3 * m) => ℓ t + ℓ (t + 1) + ℓ (t + 2)
          C j = 0 ∨ C (j + 1) = 0 ∨ C j = C (j + 1) := by
        intro j
        dsimp only
        rw [← wedge_zero_iff]
        rintro ⟨_, u, hu, rfl⟩ ⟨_, v, hv, rfl⟩
        obtain ⟨i, hi⟩ := hsite_surj (j + 2)
        have hp := hpolar0 u hu v hv true i
        have hp' := htarget_polar_true 0 u v i
        rw [zero_add, zero_add] at hp'
        rw [hp', hi, hix_zget (mixF hk 2 (rotF hk 3 u)), hix_zget (mixF hk 2 (rotF hk 3 v)),
            hix_zget (mixF hk 2 (rotF hk 3 v)), hix_zget (mixF hk 2 (rotF hk 3 u)),
            M2_zmod hk u, M2_zmod hk v, M2_zmod hk v, M2_zmod hk u] at hp
        have he1 : j + 2 + ((1 : ℕ) : ZMod (3 * m)) - 3 = j := by rw [Nat.cast_one]; ring
        have he2 : j + 2 + ((1 : ℕ) : ZMod (3 * m)) - 2 = j + 1 := by rw [Nat.cast_one]; ring
        have he3 : j + 2 + ((1 : ℕ) : ZMod (3 * m)) - 1 = j + 2 := by rw [Nat.cast_one]; ring
        have hf1 : j + 2 + ((2 : ℕ) : ZMod (3 * m)) - 3 = j + 1 := by rw [Nat.cast_ofNat]; ring
        have hf2 : j + 2 + ((2 : ℕ) : ZMod (3 * m)) - 2 = j + 2 := by rw [Nat.cast_ofNat]; ring
        have hf3 : j + 2 + ((2 : ℕ) : ZMod (3 * m)) - 1 = j + 1 + 2 := by rw [Nat.cast_ofNat]; ring
        have hj11 : j + 1 + 1 = j + 2 := by ring
        rw [he1, he2, he3, hf1, hf2, hf3] at hp
        change (zget (MF hk u) j + zget (MF hk u) (j + 1) + zget (MF hk u) (j + 2)) *
               (zget (MF hk v) (j + 1) + zget (MF hk v) (j + 1 + 1) + zget (MF hk v) (j + 1 + 2)) +
               (zget (MF hk v) j + zget (MF hk v) (j + 1) + zget (MF hk v) (j + 2)) *
               (zget (MF hk u) (j + 1) + zget (MF hk u) (j + 1 + 1) + zget (MF hk u) (j + 1 + 2)) = 0
        rw [hj11]
        exact hp
      have hP3 : (∑ q : Fin m, ℓ ((3 * q.val : ℕ) : ZMod (3 * m)) =
                  ∑ q : Fin m, ℓ ((3 * q.val + 1 : ℕ) : ZMod (3 * m))) ∧
                 (∑ q : Fin m, ℓ ((3 * q.val + 1 : ℕ) : ZMod (3 * m)) =
                  ∑ q : Fin m, ℓ ((3 * q.val + 2 : ℕ) : ZMod (3 * m))) := by
        constructor
        · ext ⟨_, u, _, rfl⟩
          simp only [LinearMap.sum_apply]
          change (∑ q : Fin m, zget (MF hk u) ((3 * q.val : ℕ) : ZMod (3 * m))) =
                 (∑ q : Fin m, zget (MF hk u) ((3 * q.val + 1 : ℕ) : ZMod (3 * m)))
          have h0 : ∀ q : Fin m, zget (MF hk u) ((3 * q.val : ℕ) : ZMod (3 * m)) =
              MF hk u ⟨3 * q.val, by have := q.isLt; omega⟩ := fun q => zget_natCast _ _
          have h1 : ∀ q : Fin m, zget (MF hk u) ((3 * q.val + 1 : ℕ) : ZMod (3 * m)) =
              MF hk u ⟨3 * q.val + 1, by have := q.isLt; omega⟩ := fun q => zget_natCast _ _
          simp_rw [h0, h1]
          exact (MF_res_eq hm_pos hk u).1
        · ext ⟨_, u, _, rfl⟩
          simp only [LinearMap.sum_apply]
          change (∑ q : Fin m, zget (MF hk u) ((3 * q.val + 1 : ℕ) : ZMod (3 * m))) =
                 (∑ q : Fin m, zget (MF hk u) ((3 * q.val + 2 : ℕ) : ZMod (3 * m)))
          have h1 : ∀ q : Fin m, zget (MF hk u) ((3 * q.val + 1 : ℕ) : ZMod (3 * m)) =
              MF hk u ⟨3 * q.val + 1, by have := q.isLt; omega⟩ := fun q => zget_natCast _ _
          have h2 : ∀ q : Fin m, zget (MF hk u) ((3 * q.val + 2 : ℕ) : ZMod (3 * m)) =
              MF hk u ⟨3 * q.val + 2, by have := q.isLt; omega⟩ := fun q => zget_natCast _ _
          simp_rw [h1, h2]
          exact (MF_res_eq hm_pos hk u).2
      have hfinA : Module.finrank F A ≤ m - 1 := cyclic_label_dim_le hm2 ℓ hinj_A hP1 hP2 hP3
      let MU : U →ₗ[F] W := (MF hk).comp U.subtype
      have hrange_MU : LinearMap.range MU = A := by ext w; simp [MU, A, Submodule.mem_map]; exact Iff.rfl
      have hker_MU_le : Module.finrank F (LinearMap.ker MU) ≤ 2 := by
        let emb : LinearMap.ker MU →ₗ[F] LinearMap.ker (MF hk) :=
          { toFun := fun u => ⟨u.val.val, u.property⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hinj_emb : Function.Injective emb := fun u1 u2 h =>
          Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker (MF hk) => z.val) h))
        calc Module.finrank F (LinearMap.ker MU)
            ≤ Module.finrank F (LinearMap.ker (MF hk)) := LinearMap.finrank_le_finrank_of_injective hinj_emb
          _ = 2 := ker_MF_finrank hm_pos hk
      have hrn_MU := LinearMap.finrank_range_add_finrank_ker MU
      rw [hrange_MU] at hrn_MU
      have hfinU_le : Module.finrank F U ≤ m + 1 := by
        have h1 : Module.finrank (ZMod 2) A ≤ m - 1 := hfinA
        have h2 : Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) (LinearMap.ker MU) =
            Module.finrank (ZMod 2) U := hrn_MU
        have h3 : Module.finrank (ZMod 2) (LinearMap.ker MU) ≤ 2 := hker_MU_le
        change Module.finrank (ZMod 2) U ≤ m + 1
        omega
      have hrn_Q := LinearMap.finrank_range_add_finrank_ker Q
      have hfinW : Module.finrank F W = 3 * m := Module.finrank_fin_fun F
      have hrQ_le : Module.finrank F (LinearMap.range Q) ≤ d := by
        calc Module.finrank F (LinearMap.range Q)
            ≤ Module.finrank F (Fin d → F) := Submodule.finrank_le _
          _ = d := Module.finrank_fin_fun F
      have hUeq : LinearMap.ker Q = U := rfl
      rw [hfinW, hUeq] at hrn_Q
      omega
    · -- Upper bound: 2 * m - 1 ≤ d → admits
      intro hd
      let Q : W →ₗ[F] (Fin d → F) :=
        { toFun := fun x j =>
            if hj1 : j.val < m then
              MF hk x ⟨3 * j.val + 2, by omega⟩
            else if hj2 : j.val < 2 * m - 1 then
              MF hk x ⟨3 * (j.val - m), by omega⟩ + MF hk x ⟨3 * (j.val - m) + 1, by omega⟩
            else 0
          map_add' := fun x y => by
            funext j; simp only [Pi.add_apply]; split_ifs
            · simp [map_add]
            · simp only [map_add, Pi.add_apply]; ring
            · simp
          map_smul' := fun c x => by
            rcases z2_cases c with rfl | rfl
            · funext j; by_cases hj1 : j.val < m
              · simp [hj1]
              · by_cases hj2 : j.val < 2 * m - 1 <;> simp [hj1, hj2]
            · funext j; by_cases hj1 : j.val < m
              · simp [hj1]
              · by_cases hj2 : j.val < 2 * m - 1 <;> simp [hj1, hj2] }
      refine admits_of_ker_polar target Q fun u hu v hv x0 b i => ?_
      have hker_pat : ∀ z ∈ LinearMap.ker Q,
          (∀ q : Fin m, MF hk z ⟨3 * q.val + 2, by have := q.isLt; omega⟩ = 0) ∧
          (∀ q : Fin m, MF hk z ⟨3 * q.val, by have := q.isLt; omega⟩ =
            MF hk z ⟨3 * q.val + 1, by have := q.isLt; omega⟩) := by
        intro z hz
        have hQz : ∀ j : Fin d, Q z j = 0 := fun j => congrFun (LinearMap.mem_ker.mp hz) j
        have h2 : ∀ q : Fin m, MF hk z ⟨3 * q.val + 2, by have := q.isLt; omega⟩ = 0 := by
          intro q
          have h := hQz ⟨q.val, by have := q.isLt; omega⟩
          simpa [Q, q.isLt] using h
        have h01_lt : ∀ q : Fin m, q.val < m - 1 →
            MF hk z ⟨3 * q.val, by have := q.isLt; omega⟩ =
            MF hk z ⟨3 * q.val + 1, by have := q.isLt; omega⟩ := by
          intro q hq
          have h := hQz ⟨m + q.val, by omega⟩
          have hn1 : ¬ (m + q.val < m) := by omega
          have hlt2 : m + q.val < 2 * m - 1 := by omega
          simp only [Q, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hn1, dif_pos hlt2] at h
          have heq_sub : m + q.val - m = q.val := by omega
          simp only [heq_sub] at h
          have hb : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
          exact hb _ _ h
        refine ⟨h2, fun q => ?_⟩
        by_cases hq : q.val < m - 1
        · exact h01_lt q hq
        · have hq_last : q = ⟨m - 1, by omega⟩ := Fin.ext (by have := q.isLt; dsimp only; omega)
          rw [hq_last]
          have hres := (MF_res_eq hm_pos hk z).1
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨m - 1, by omega⟩ : Fin m)),
              ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨m - 1, by omega⟩ : Fin m))] at hres
          have htail : ∑ q ∈ Finset.univ.erase (⟨m - 1, by omega⟩ : Fin m),
              MF hk z ⟨3 * q.val, by have := q.isLt; omega⟩ =
              ∑ q ∈ Finset.univ.erase (⟨m - 1, by omega⟩ : Fin m),
              MF hk z ⟨3 * q.val + 1, by have := q.isLt; omega⟩ := by
            refine Finset.sum_congr rfl fun q hq => ?_
            have hne : q ≠ ⟨m - 1, by omega⟩ := (Finset.mem_erase.mp hq).1
            exact h01_lt q (by have := q.isLt; have : q.val ≠ m - 1 := fun h => hne (Fin.ext h); omega)
          rw [htail] at hres
          exact add_right_cancel hres
      have hM_val : ∀ z ∈ LinearMap.ker Q, ∀ j : Fin (3 * m),
          (j.val % 3 = 2 → MF hk z j = 0) ∧
          (j.val % 3 = 0 → MF hk z j = MF hk z (ixF hk (j.val + 1))) := by
        intro z hz j
        obtain ⟨h2, h01⟩ := hker_pat z hz
        have hq_lt : j.val / 3 < m := by have := j.isLt; omega
        constructor
        · intro hm2
          have heq : j = ⟨3 * (j.val / 3) + 2, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [heq]; exact h2 ⟨j.val / 3, hq_lt⟩
        · intro hm0
          set q := j.val / 3
          have heq1 : j = ⟨3 * q, by omega⟩ := Fin.ext (by dsimp only; omega)
          have heq2 : ixF hk (j.val + 1) = ⟨3 * q + 1, by omega⟩ := by
            apply Fin.ext; dsimp only [ixF]; rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]; omega
          rw [heq2]; exact (congrArg (MF hk z) heq1).trans (h01 ⟨q, hq_lt⟩)
      cases b
      · rw [htarget_polar_false]
        set s1 := ixF hk ((ixF hk (start + i.val)).val + 1)
        have hs2 : ixF hk ((ixF hk (start + i.val)).val + 2) = ixF hk (s1.val + 1) := by
          apply Fin.ext; dsimp only [ixF, s1]
          simp only [Nat.mod_add_mod, add_assoc]
        rw [hs2]
        have hmod : s1.val % 3 = 0 ∨ s1.val % 3 = 1 ∨ s1.val % 3 = 2 := by omega
        rcases hmod with hm0 | hm1 | hm2
        · rw [(hM_val u hu s1).2 hm0, (hM_val v hv s1).2 hm0, mul_comm (MF hk v _), z2_add_self]
        · have hs1_lt : s1.val + 1 < 3 * m := by have := s1.isLt; omega
          have hs2_m : (ixF hk (s1.val + 1)).val % 3 = 2 := by
            dsimp only [ixF]; rw [Nat.mod_eq_of_lt hs1_lt]; omega
          rw [(hM_val u hu _).1 hs2_m, (hM_val v hv _).1 hs2_m, mul_zero, mul_zero, add_zero]
        · rw [(hM_val u hu s1).1 hm2, (hM_val v hv s1).1 hm2, zero_mul, zero_mul, add_zero]
      · rw [htarget_polar_true]
        have hM2_zero : ∀ z ∈ LinearMap.ker Q, ∀ j : Fin (3 * m),
            j.val % 3 ≠ 1 → mixF hk 2 (rotF hk 3 z) j = 0 := by
          intro z hz j hne1
          rw [zget_fin (mixF hk 2 (rotF hk 3 z)) j, M2_zmod]
          set zj : ZMod (3 * m) := ((j.val : ℕ) : ZMod (3 * m))
          unfold zget
          have hsub_mod : ∀ t : ℕ, t ≤ 3 → (zj - (t : ZMod (3 * m))).val % 3 = (j.val + 3 - t) % 3 := by
            intro t ht
            have h1 := zmod_sub_nat hk zj t
            rw [ZMod.val_natCast_of_lt j.isLt] at h1
            rw [← h1, ZMod.val_natCast, Nat.mod_mod_of_dvd _ ⟨m, rfl⟩]
            have htlt : t % (3 * m) = t := Nat.mod_eq_of_lt (by omega)
            rw [htlt]; omega
          have hm3 := hsub_mod 3 (by omega)
          have hm2 := hsub_mod 2 (by omega)
          have hm1 := hsub_mod 1 (by omega)
          have hsucc_eq : ∀ w : ZMod (3 * m),
              ixF hk (w.val + 1) = ⟨(w + 1).val, ZMod.val_lt _⟩ := fun w =>
            ixF_eq_zmod hk _ (w + 1) (by rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val])
          have hmod : j.val % 3 = 0 ∨ j.val % 3 = 2 := by omega
          rcases hmod with h0 | h2
          · have e3 : (⟨(zj - 3).val, ZMod.val_lt _⟩ : Fin (3 * m)).val % 3 = 0 := by
              dsimp only; rw [show (3 : ZMod (3 * m)) = ((3 : ℕ) : ZMod (3 * m)) from rfl, hm3]; omega
            have e1 : (⟨(zj - 1).val, ZMod.val_lt _⟩ : Fin (3 * m)).val % 3 = 2 := by
              dsimp only; rw [show (1 : ZMod (3 * m)) = ((1 : ℕ) : ZMod (3 * m)) from Nat.cast_one.symm, hm1]; omega
            have hstep : ixF hk ((zj - 3).val + 1) = ⟨(zj - 2).val, ZMod.val_lt _⟩ := by
              rw [hsucc_eq]; apply Fin.ext; dsimp only; exact congrArg ZMod.val (by ring : zj - 3 + 1 = zj - 2)
            rw [(hM_val z hz ⟨(zj - 1).val, ZMod.val_lt _⟩).1 e1, add_zero,
                (hM_val z hz ⟨(zj - 3).val, ZMod.val_lt _⟩).2 e3, hstep, z2_add_self]
          · have e3 : (⟨(zj - 3).val, ZMod.val_lt _⟩ : Fin (3 * m)).val % 3 = 2 := by
              dsimp only; rw [show (3 : ZMod (3 * m)) = ((3 : ℕ) : ZMod (3 * m)) from rfl, hm3]; omega
            have e2 : (⟨(zj - 2).val, ZMod.val_lt _⟩ : Fin (3 * m)).val % 3 = 0 := by
              dsimp only; rw [show (2 : ZMod (3 * m)) = ((2 : ℕ) : ZMod (3 * m)) from rfl, hm2]; omega
            have hstep : ixF hk ((zj - 2).val + 1) = ⟨(zj - 1).val, ZMod.val_lt _⟩ := by
              rw [hsucc_eq]; apply Fin.ext; dsimp only; exact congrArg ZMod.val (by ring : zj - 2 + 1 = zj - 1)
            rw [(hM_val z hz ⟨(zj - 3).val, ZMod.val_lt _⟩).1 e3, zero_add,
                (hM_val z hz ⟨(zj - 2).val, ZMod.val_lt _⟩).2 e2, hstep, z2_add_self]
        set s1 := ixF hk ((ixF hk (start + i.val)).val + 1)
        set s2 := ixF hk ((ixF hk (start + i.val)).val + 2)
        have hnot_both : s1.val % 3 ≠ 1 ∨ s2.val % 3 ≠ 1 := by
          have hs2_mod : s2.val % 3 = (s1.val + 1) % 3 := by
            have h1 : s2.val = (s1.val + 1) % (3 * m) := by
              dsimp only [ixF, s1, s2]
              simp only [Nat.mod_add_mod, add_assoc]
            rw [h1, Nat.mod_mod_of_dvd _ ⟨m, rfl⟩]
          omega
        rcases hnot_both with h1 | h2
        · rw [hM2_zero u hu s1 h1, hM2_zero v hv s1 h1, zero_mul, zero_mul, add_zero]
        · rw [hM2_zero u hu s2 h2, hM2_zero v hv s2 h2, mul_zero, mul_zero, add_zero]
