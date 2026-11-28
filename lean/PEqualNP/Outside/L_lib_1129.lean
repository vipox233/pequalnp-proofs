import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1129_aux

open scoped BigOperators

lemma sum_powerset_neg_one {α : Type*} [DecidableEq α] (K : Finset α) :
    (∑ I ∈ K.powerset, (-1 : ℤ) ^ I.card) = if K = ∅ then 1 else 0 := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · have h1 : (∑ I ∈ s.powerset, (-1 : ℤ) ^ (insert a I).card) =
            -(∑ I ∈ s.powerset, (-1 : ℤ) ^ I.card) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun I hI => ?_
          have haI : a ∉ I := fun h => ha (Finset.mem_powerset.mp hI h)
          rw [Finset.card_insert_of_notMem haI, pow_succ]
          ring
        rw [h1, add_neg_cancel]
        simp [Finset.insert_ne_empty]
      · intro I₁ hI₁ I₂ hI₂ hEq
        have ha₁ : a ∉ I₁ := fun h => ha (Finset.mem_powerset.mp hI₁ h)
        have ha₂ : a ∉ I₂ := fun h => ha (Finset.mem_powerset.mp hI₂ h)
        have := congrArg (fun u => u.erase a) hEq
        simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using this
    · rw [Finset.disjoint_left]
      intro I hI hIm
      rcases Finset.mem_image.mp hIm with ⟨J, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hI (Finset.mem_insert_self a J))

lemma pos_sum_iff {α : Type*} (s : Finset α) (f : α → ℕ) :
    0 < s.sum f ↔ ∃ x ∈ s, 0 < f x := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have h0 : s.sum f = 0 := Finset.sum_eq_zero fun x hx => Nat.le_zero.mp (hall x hx)
    omega
  · rintro ⟨x, hx, hfx⟩
    exact lt_of_lt_of_le hfx (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx)

theorem main :
    ∀ (m : Nat) (T : Finset (Fin m)) (t w : Nat), 0 < w →
      let Clause := Finset (Fin m × Bool)
      let holds := fun (x : Finset (Fin m)) (C : Clause) =>
        ∃ l ∈ C, decide (l.1 ∈ x) = l.2
      let valid := fun (F : Finset Clause) =>
        F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T
      let cube := (Finset.univ : Finset (Finset (Fin m)))
      let total := fun (A : Finset (Fin m) → Nat) (F : Finset Clause) =>
        (cube.filter (fun x => ∀ C ∈ F, holds x C)).sum A
      let pin := fun (A : Finset (Fin m) → Nat) (S B : Finset (Fin m)) =>
        (cube.filter (fun x => x ∩ S = B)).sum A
      ∀ A D : Finset (Fin m) → Nat,
        ((∀ F, valid F → (0 < total A F ↔ 0 < total D F)) ↔
          ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S, (0 < pin A S B ↔ 0 < pin D S B)) ∧
        ((∀ F, valid F → total A F = total D F) ↔
          ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S, pin A S B = pin D S B) := by
  classical
  intro m T t w hw
  dsimp only
  intro A D
  let Clause := Finset (Fin m × Bool)
  let holds : Finset (Fin m) → Clause → Prop := fun x C => ∃ l ∈ C, decide (l.1 ∈ x) = l.2
  let valid : Finset Clause → Prop := fun F =>
    F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T
  let cube : Finset (Finset (Fin m)) := Finset.univ
  let total : (Finset (Fin m) → ℕ) → Finset Clause → ℕ := fun f F =>
    (cube.filter (fun x => ∀ C ∈ F, holds x C)).sum f
  let pin : (Finset (Fin m) → ℕ) → Finset (Fin m) → Finset (Fin m) → ℕ := fun f S B =>
    (cube.filter (fun x => x ∩ S = B)).sum f
  have hinter_eq : ∀ (x S B : Finset (Fin m)), B ⊆ S →
      (x ∩ S = B ↔ ∀ i ∈ S, decide (i ∈ x) = decide (i ∈ B)) := by
    intro x S B hBS
    constructor
    · rintro rfl i hi
      simp [hi]
    · intro h
      ext i
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hix, hiS⟩
        have := h i hiS
        simpa [hix] using this.symm
      · intro hiB
        have hiS := hBS hiB
        have := h i hiS
        exact ⟨by simpa [hiB] using this, hiS⟩
  constructor
  · -- Part 1: SAT equivalence
    constructor
    · intro hF S hST hSt B hBS
      let F : Finset Clause := S.image (fun i => ({(i, decide (i ∈ B))} : Clause))
      have hval : valid F := by
        refine ⟨(Finset.card_image_le).trans hSt, ?_⟩
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨i, hiS, rfl⟩
        refine ⟨by rw [Finset.card_singleton]; exact hw, ?_⟩
        intro l hl
        rw [Finset.mem_singleton] at hl
        subst hl
        exact hST hiS
      have hfilt : ∀ f, total f F = pin f S B := by
        intro f
        dsimp only [total, pin]
        congr 1
        ext x
        simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and, F, Finset.mem_image]
        rw [hinter_eq x S B hBS]
        constructor
        · intro h i hiS
          obtain ⟨l, hl, heq⟩ := h {(i, decide (i ∈ B))} ⟨i, hiS, rfl⟩
          rw [Finset.mem_singleton] at hl
          subst hl
          exact heq
        · rintro h C ⟨i, hiS, rfl⟩
          exact ⟨(i, decide (i ∈ B)), Finset.mem_singleton_self _, h i hiS⟩
      change 0 < pin A S B ↔ 0 < pin D S B
      rw [← hfilt A, ← hfilt D]
      exact hF F hval
    · intro hpin F hval
      have hone : ∀ (f g : Finset (Fin m) → ℕ),
          (∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S, 0 < pin f S B → 0 < pin g S B) →
          0 < total f F → 0 < total g F := by
        intro f g hfg hfpos
        obtain ⟨x, hx, hfx⟩ := (pos_sum_iff _ _).mp hfpos
        have hxF : ∀ C ∈ F, holds x C := (Finset.mem_filter.mp hx).2
        let S : Finset (Fin m) := F.attach.image (fun C => (hxF C.val C.property).choose.1)
        have hST : S ⊆ T := by
          intro i hi
          rcases Finset.mem_image.mp hi with ⟨C, _, rfl⟩
          exact (hval.2 C.val C.property).2 _ (hxF C.val C.property).choose_spec.1
        have hSt : S.card ≤ t := by
          calc S.card ≤ F.attach.card := Finset.card_image_le
            _ = F.card := Finset.card_attach
            _ ≤ t := hval.1
        let B : Finset (Fin m) := x ∩ S
        have hBS : B ⊆ S := Finset.inter_subset_right
        have hpin_f : 0 < pin f S B :=
          (pos_sum_iff _ _).mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hfx⟩
        have hpin_g : 0 < pin g S B := hfg S hST hSt B hBS hpin_f
        obtain ⟨y, hy, hgy⟩ := (pos_sum_iff _ _).mp hpin_g
        have hyS : y ∩ S = x ∩ S := (Finset.mem_filter.mp hy).2
        refine (pos_sum_iff _ _).mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hgy⟩
        intro C hCF
        let l := (hxF C hCF).choose
        have hlC : l ∈ C := (hxF C hCF).choose_spec.1
        have hlx : decide (l.1 ∈ x) = l.2 := (hxF C hCF).choose_spec.2
        have hlS : l.1 ∈ S := Finset.mem_image.mpr ⟨⟨C, hCF⟩, Finset.mem_attach _ _, rfl⟩
        have hyx : l.1 ∈ y ↔ l.1 ∈ x := by
          have h1 := congrArg (fun u => l.1 ∈ u) hyS
          simpa [Finset.mem_inter, hlS] using h1
        exact ⟨l, hlC, by rw [← hlx]; exact decide_eq_decide.mpr hyx⟩
      exact ⟨hone A D (fun S hST hSt B hBS h => (hpin S hST hSt B hBS).mp h),
             hone D A (fun S hST hSt B hBS h => (hpin S hST hSt B hBS).mpr h)⟩
  · -- Part 2: Exact model counts
    constructor
    · intro hF S hST hStw B hBS
      let L : List (Fin m) := S.toList
      have hLlen : L.length = S.card := Finset.length_toList S
      let U : Fin t → Finset (Fin m) := fun j => ((L.drop (j.val * w)).take w).toFinset
      have hUcard : ∀ j : Fin t, (U j).card ≤ w := by
        intro j
        calc (U j).card ≤ ((L.drop (j.val * w)).take w).length := List.toFinset_card_le _
          _ ≤ w := List.length_take_le _ _
      have hUS : ∀ j : Fin t, U j ⊆ S := by
        intro j i hi
        have h1 : i ∈ (L.drop (j.val * w)).take w := List.mem_toFinset.mp hi
        have h2 : i ∈ L.drop (j.val * w) := List.mem_of_mem_take h1
        have h3 : i ∈ L := List.mem_of_mem_drop h2
        exact Finset.mem_toList.mp h3
      have hcover : ∀ i ∈ S, ∃ j : Fin t, i ∈ U j := by
        intro i hiS
        have hiL : i ∈ L := Finset.mem_toList.mpr hiS
        obtain ⟨pos, hpos, hget⟩ := List.mem_iff_getElem.mp hiL
        have hjlt : pos / w < t := by
          rw [Nat.div_lt_iff_lt_mul hw]
          omega
        refine ⟨⟨pos / w, hjlt⟩, List.mem_toFinset.mpr ?_⟩
        have hdrop_len : pos % w < (L.drop ((pos / w) * w)).length := by
          rw [List.length_drop]
          have h1 := Nat.div_add_mod pos w
          have h2 : (pos / w) * w = w * (pos / w) := Nat.mul_comm _ _
          omega
        have htake_len : pos % w < ((L.drop ((pos / w) * w)).take w).length := by
          rw [List.length_take]
          exact lt_min (Nat.mod_lt pos hw) hdrop_len
        refine List.mem_iff_getElem.mpr ⟨pos % w, htake_len, ?_⟩
        rw [List.getElem_take, List.getElem_drop]
        have hidx : (pos / w) * w + pos % w = pos := by
          have := Nat.div_add_mod pos w; linarith
        simpa [hidx] using hget
      let cl : Fin t → Clause := fun j => (U j).image (fun i => (i, !decide (i ∈ B)))
      have hcl_valid : ∀ I : Finset (Fin t), valid (I.image cl) := by
        intro I
        refine ⟨?_, ?_⟩
        · calc (I.image cl).card ≤ I.card := Finset.card_image_le
            _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_univ _
            _ = t := Fintype.card_fin t
        · intro C hC
          rcases Finset.mem_image.mp hC with ⟨j, _, rfl⟩
          refine ⟨(Finset.card_image_le).trans (hUcard j), ?_⟩
          intro l hl
          rcases Finset.mem_image.mp hl with ⟨i, hi, rfl⟩
          exact hST (hUS j hi)
      have hie : ∀ f : Finset (Fin m) → ℕ,
          (pin f S B : ℤ) = ∑ I ∈ (Finset.univ : Finset (Fin t)).powerset,
            (-1 : ℤ) ^ I.card * (total f (I.image cl) : ℤ) := by
        intro f
        have hstep1 : (∑ I ∈ (Finset.univ : Finset (Fin t)).powerset,
            (-1 : ℤ) ^ I.card * (total f (I.image cl) : ℤ)) =
            ∑ I ∈ (Finset.univ : Finset (Fin t)).powerset,
              ∑ x ∈ cube, if (∀ j ∈ I, holds x (cl j)) then (-1 : ℤ) ^ I.card * (f x : ℤ) else 0 := by
          refine Finset.sum_congr rfl fun I _ => ?_
          dsimp only [total]
          rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          have hiff : (∀ C ∈ I.image cl, holds x C) ↔ (∀ j ∈ I, holds x (cl j)) := by
            simp only [Finset.mem_image]
            constructor
            · intro h j hj; exact h (cl j) ⟨j, hj, rfl⟩
            · rintro h C ⟨j, hj, rfl⟩; exact h j hj
          by_cases hc : ∀ j ∈ I, holds x (cl j)
          · rw [if_pos (hiff.mpr hc), if_pos hc]
          · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
        rw [hstep1, Finset.sum_comm]
        have hstep2 : ∀ x : Finset (Fin m),
            (∑ I ∈ (Finset.univ : Finset (Fin t)).powerset,
              if (∀ j ∈ I, holds x (cl j)) then (-1 : ℤ) ^ I.card * (f x : ℤ) else 0) =
            if x ∩ S = B then (f x : ℤ) else 0 := by
          intro x
          let K : Finset (Fin t) := Finset.univ.filter (fun j => holds x (cl j))
          have hfilt_eq : (Finset.univ : Finset (Fin t)).powerset.filter (fun I => ∀ j ∈ I, holds x (cl j)) =
              K.powerset := by
            ext I
            simp [K, Finset.subset_iff]
          rw [← Finset.sum_filter, hfilt_eq, ← Finset.sum_mul, sum_powerset_neg_one K]
          have hK_iff : K = ∅ ↔ x ∩ S = B := by
            rw [hinter_eq x S B hBS, Finset.eq_empty_iff_forall_notMem]
            simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h i hiS
              obtain ⟨j, hij⟩ := hcover i hiS
              have hnh := h j
              dsimp only [holds, cl] at hnh
              push Not at hnh
              have hneq := hnh (i, !decide (i ∈ B)) (Finset.mem_image_of_mem _ hij)
              cases hx : decide (i ∈ x) <;> cases hb : decide (i ∈ B) <;> simp_all
            · intro h j hhold
              rcases hhold with ⟨l, hl, hlx⟩
              rcases Finset.mem_image.mp hl with ⟨i, hiU, rfl⟩
              have hiS := hUS j hiU
              have := h i hiS
              dsimp only at hlx
              rw [this] at hlx
              cases decide (i ∈ B) <;> simp at hlx
          by_cases hxB : x ∩ S = B
          · simp [hxB, hK_iff.mpr hxB]
          · have hKne : K ≠ ∅ := fun h => hxB (hK_iff.mp h)
            simp [hxB, hKne]
        simp_rw [hstep2]
        dsimp only [pin]
        rw [Nat.cast_sum, Finset.sum_filter]
      have hZ : (pin A S B : ℤ) = (pin D S B : ℤ) := by
        rw [hie A, hie D]
        refine Finset.sum_congr rfl fun I _ => ?_
        have hEq : total A (I.image cl) = total D (I.image cl) := hF (I.image cl) (hcl_valid I)
        rw [hEq]
      exact Int.ofNat.inj hZ
    · intro hpin F hval
      let S : Finset (Fin m) := F.biUnion (fun C => C.image Prod.fst)
      have hST : S ⊆ T := by
        intro i hi
        rcases Finset.mem_biUnion.mp hi with ⟨C, hCF, hiC⟩
        rcases Finset.mem_image.mp hiC with ⟨l, hlC, rfl⟩
        exact (hval.2 C hCF).2 l hlC
      have hStw : S.card ≤ t * w := by
        calc S.card ≤ ∑ C ∈ F, (C.image Prod.fst).card := Finset.card_biUnion_le
          _ ≤ ∑ C ∈ F, C.card := Finset.sum_le_sum fun C _ => Finset.card_image_le
          _ ≤ ∑ _C ∈ F, w := Finset.sum_le_sum fun C hCF => (hval.2 C hCF).1
          _ = F.card * w := by simp
          _ ≤ t * w := Nat.mul_le_mul_right w hval.1
      have hdep : ∀ x : Finset (Fin m),
          (∀ C ∈ F, holds x C) ↔ (∀ C ∈ F, holds (x ∩ S) C) := by
        intro x
        refine forall₂_congr fun C hCF => ?_
        refine exists_congr fun l => and_congr_right fun hlC => ?_
        have hlS : l.1 ∈ S := Finset.mem_biUnion.mpr ⟨C, hCF, Finset.mem_image.mpr ⟨l, hlC, rfl⟩⟩
        simp [Finset.mem_inter, hlS]
      have hgroup : ∀ f : Finset (Fin m) → ℕ,
          total f F = ∑ B ∈ S.powerset.filter (fun B => ∀ C ∈ F, holds B C), pin f S B := by
        intro f
        dsimp only [total, pin]
        rw [← Finset.sum_biUnion]
        · congr 1
          ext x
          simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_powerset]
          constructor
          · intro hx
            exact ⟨x ∩ S, ⟨Finset.inter_subset_right, (hdep x).mp hx⟩, rfl⟩
          · rintro ⟨B, ⟨_, hBF⟩, hxB⟩
            rw [hdep x, hxB]
            exact hBF
        · intro B₁ _ B₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact hne (((Finset.mem_filter.mp hx1).2).symm.trans (Finset.mem_filter.mp hx2).2)
      change total A F = total D F
      rw [hgroup A, hgroup D]
      refine Finset.sum_congr rfl fun B hB => ?_
      exact hpin S hST hStw B (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)

end PEqualNP.Outside.L_lib_1129_aux

theorem PEqualNP.Outside.L_lib_1129 :
∀ (m : Nat) (T : Finset (Fin m)) (t w : Nat), 0 < w →

  let Clause := Finset (Fin m × Bool)
  let holds := fun (x : Finset (Fin m)) (C : Clause) =>
    ∃ l ∈ C, decide (l.1 ∈ x) = l.2
  let valid := fun (F : Finset Clause) =>
    F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T

  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let total := fun (A : Finset (Fin m) → Nat) (F : Finset Clause) =>
    (cube.filter (fun x => ∀ C ∈ F, holds x C)).sum A
  let pin := fun (A : Finset (Fin m) → Nat) (S B : Finset (Fin m)) =>
    (cube.filter (fun x => x ∩ S = B)).sum A
  ∀ A D : Finset (Fin m) → Nat,
    ((∀ F, valid F → (0 < total A F ↔ 0 < total D F)) ↔
      ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S, (0 < pin A S B ↔ 0 < pin D S B)) ∧
    ((∀ F, valid F → total A F = total D F) ↔
      ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S, pin A S B = pin D S B) :=
  PEqualNP.Outside.L_lib_1129_aux.main
