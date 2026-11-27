import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_798

theorem z2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem sum_supp {k m : ℕ} (v : Fin m → Fin k → ZMod 2) (d : Fin m → ZMod 2) :
    ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), v j = ∑ j, d j • v j := by
  rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : d j = 0
  · simp [h]
  · simp [z2 _ h]

theorem sum_set {k m : ℕ} (v : Fin m → Fin k → ZMod 2) (S : Finset (Fin m)) :
    ∑ j ∈ S, v j = ∑ j, (if j ∈ S then (1:ZMod 2) else 0) • v j := by
  simp [ite_smul, Finset.sum_ite_mem]

theorem bound {k m a h t : ℕ} (v : Fin m → Fin k → ZMod 2)
    (hv : ∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a+1)*h → (∑ j ∈ S, v j) ≠ 0)
    (p : Fin a → Fin k → ZMod 2) (S : ℕ → Finset (Fin m)) (x : ℕ → Fin m) (ht : t ≤ a+1)
    (hS : ∀ i < t, (S i).card ≤ h ∧ (∃ z : Fin a → ZMod 2, ∑ j ∈ S i, v j = ∑ l, z l • p l) ∧
      x i ∈ S i ∧ ∀ j < t, i < j → x i ∉ S j) : t ≤ a := by
  classical
  have hz : ∀ i : Fin t, ∃ z : Fin a → ZMod 2, ∑ j ∈ S i, v j = ∑ l, z l • p l :=
    fun i => (hS i i.2).2.1
  choose z hz using hz
  let w : Fin t → Fin k → ZMod 2 := fun i => ∑ j ∈ S i, v j
  let D : (Fin t → ZMod 2) → Fin m → ZMod 2 :=
    fun c j => ∑ i, c i * (if j ∈ S i then 1 else 0)
  have hval : ∀ c, ∑ j, D c j • v j = ∑ i, c i • w i := by
    intro c
    simp only [D, w, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_set v (S i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul]
  have hP : ∀ c : Fin t → ZMod 2, ∃ zz : Fin a → ZMod 2, ∑ i, c i • w i = ∑ l, zz l • p l := by
    intro c
    refine ⟨fun l => ∑ i, c i * z i l, ?_⟩
    simp only [w, hz, Finset.smul_sum, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  have hsupp : ∀ c, (Finset.univ.filter (fun j => D c j ≠ 0)).card ≤ t * h := by
    intro c
    have hsub : Finset.univ.filter (fun j => D c j ≠ 0) ⊆
        (Finset.univ : Finset (Fin t)).biUnion (fun i => S i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      by_contra hn
      push Not at hn
      apply hj
      simp only [D]
      exact Finset.sum_eq_zero fun i _ => by simp [hn i]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin t, (S i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin t, h := Finset.sum_le_sum fun i _ => (hS i i.2).1
      _ = t * h := by simp
  have hnz : ∀ c : Fin t → ZMod 2, c ≠ 0 → ∑ i, c i • w i ≠ 0 := by
    intro c hc
    have hne : (Finset.univ.filter (fun i => c i ≠ 0)).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
      exact ⟨i, by simpa using hi⟩
    set i0 := (Finset.univ.filter (fun i => c i ≠ 0)).min' hne with hi0
    have hi0m := Finset.min'_mem _ hne
    rw [← hi0] at hi0m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0m
    have hmin : ∀ i, i < i0 → c i = 0 := by
      intro i hi
      by_contra hci
      have := Finset.min'_le (Finset.univ.filter (fun i => c i ≠ 0)) i (by simpa using hci)
      rw [← hi0] at this
      exact absurd hi (not_lt.mpr this)
    have hD : D c (x i0) = c i0 := by
      simp only [D]
      rw [Finset.sum_eq_single i0]
      · simp [(hS i0 i0.2).2.2.1]
      · intro i _ hne
        rcases lt_or_gt_of_ne hne with hl | hl
        · simp [hmin i hl]
        · have := (hS i0 i0.2).2.2.2 i i.2 hl
          simp [this]
      · simp
    rw [← hval, ← sum_supp]
    apply hv
    · exact ⟨x i0, by simp [hD, hi0m]⟩
    · exact (hsupp c).trans (Nat.mul_le_mul_right _ ht)
  have hinj : Set.InjOn (fun c : Fin t → ZMod 2 => ∑ i, c i • w i) ((Finset.univ : Finset (Fin t → ZMod 2)) : Set (Fin t → ZMod 2)) := by
    intro c _ c' _ hcc
    by_contra hne
    apply hnz (c - c') (sub_ne_zero.mpr hne)
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hcc
  have hcard := Finset.card_le_card_of_injOn (fun c : Fin t → ZMod 2 => ∑ i, c i • w i)
    (s := Finset.univ) (t := Finset.univ.image (fun zz : Fin a → ZMod 2 => ∑ l, zz l • p l))
    (fun c _ => by
      obtain ⟨zz, hzz⟩ := hP c
      exact Finset.mem_image.mpr ⟨zz, Finset.mem_univ _, hzz.symm⟩) hinj
  have h2 := hcard.trans Finset.card_image_le
  simp only [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

end PEqualNP.Outside.L_lib_798
theorem PEqualNP.Outside.L_lib_798 : ∀ (k m a h : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  ∀ v : Fin m → V,
    (∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a+1)*h →
      (∑ j ∈ S, v j) ≠ 0) →
    ∀ p : Fin a → V,
      ∃ R : Finset (Fin m), R.card ≤ a ∧
        ∀ S : Finset (Fin m), S.Nonempty → Disjoint S R → S.card ≤ h →
          ∀ z : Fin a → F, (∑ j ∈ S, v j) ≠ ∑ i : Fin a, z i • p i := by
  intro k m a h F V v hv p
  classical
  by_cases hm : m = 0
  · subst hm
    refine ⟨∅, by simp, ?_⟩
    intro S hS
    exact absurd hS (by simp [Finset.eq_empty_of_isEmpty S])
  have x0 : Fin m := ⟨0, by omega⟩
  let Tri : ℕ → Prop := fun t => ∃ S : ℕ → Finset (Fin m), ∃ x : ℕ → Fin m, ∀ i < t,
    (S i).card ≤ h ∧ (∃ z : Fin a → ZMod 2, ∑ j ∈ S i, v j = ∑ l, z l • p l) ∧
      x i ∈ S i ∧ ∀ j < t, i < j → x i ∉ S j
  have h0 : Tri 0 := ⟨fun _ => ∅, fun _ => x0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hspec : Tri (Nat.findGreatest Tri a) := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) h0
  have hle : Nat.findGreatest Tri a ≤ a := Nat.findGreatest_le a
  obtain ⟨S, x, hS⟩ := hspec
  set t := Nat.findGreatest Tri a with ht
  refine ⟨(Finset.range t).image x, (Finset.card_image_le).trans (by simpa using hle), ?_⟩
  intro T hT hdisj hTc zz heq
  have hxT : ∀ i < t, x i ∉ T := fun i hi hx =>
    Finset.disjoint_left.mp hdisj hx (Finset.mem_image_of_mem x (Finset.mem_range.2 hi))
  let S' : ℕ → Finset (Fin m) := fun i => if i = t then T else S i
  let x' : ℕ → Fin m := fun i => if i = t then hT.choose else x i
  have hS' : ∀ i < t + 1, (S' i).card ≤ h ∧ (∃ z : Fin a → ZMod 2, ∑ j ∈ S' i, v j = ∑ l, z l • p l) ∧
      x' i ∈ S' i ∧ ∀ j < t + 1, i < j → x' i ∉ S' j := by
    intro i hi
    by_cases hit : i = t
    · subst hit
      simp only [S', x', if_true]
      exact ⟨hTc, ⟨zz, heq⟩, hT.choose_spec, fun j hj hij => by omega⟩
    · have hi' : i < t := by omega
      obtain ⟨a1, a2, a3, a4⟩ := hS i hi'
      simp only [S', x', hit, if_false]
      refine ⟨a1, a2, a3, fun j hj hij => ?_⟩
      by_cases hjt : j = t
      · simp only [hjt, if_true]; exact hxT i hi'
      · simp only [hjt, if_false]; exact a4 j (by omega) hij
  have hb := PEqualNP.Outside.L_lib_798.bound v hv p S' x' (t := t + 1) (by omega) hS'
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self t) hb ⟨S', x', hS'⟩
