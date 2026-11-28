import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1015_aux

abbrev F := ZMod 2

lemma f_cases (x : F) : x = 0 ∨ x = 1 := by
  match x with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

lemma f_add_self (x : F) : x + x = 0 := by
  rcases f_cases x with rfl | rfl <;> decide

lemma f_add_one_eq_of_ne {x y : F} (h : x ≠ y) : x + 1 = y := by
  rcases f_cases x with rfl | rfl <;> rcases f_cases y with rfl | rfl
  · exact (h rfl).elim
  · decide
  · decide
  · exact (h rfl).elim

lemma f_add_one_ne (x : F) : x + 1 ≠ x := by
  rcases f_cases x with rfl | rfl <;> decide

def fiberSum {m k : ℕ} (proj : Fin m → Fin k) (x : Fin m → F) (v : Fin k) : F :=
  ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => proj i = v), x i

lemma card_fiberSum_eq {m k : ℕ} (proj : Fin m → Fin k) (hsurj : Function.Surjective proj)
    (p : Fin k → F) :
    ((Finset.univ : Finset (Fin m → F)).filter (fun x => fiberSum proj x = p)).card = 2 ^ (m - k) := by
  classical
  choose sec hsec using hsurj
  let S : Finset (Fin m) := Finset.univ.image sec
  have hsec_inj : Function.Injective sec := by
    intro u v huv
    have := congrArg proj huv
    rw [hsec u, hsec v] at this
    exact this
  have hS_card : S.card = k := by
    rw [Finset.card_image_of_injective _ hsec_inj, Finset.card_univ, Fintype.card_fin]
  let Sc : Finset (Fin m) := Sᶜ
  have hSc_card : Sc.card = m - k := by
    change Sᶜ.card = m - k
    rw [Finset.card_compl, Fintype.card_fin, hS_card]
  have hnotS : ∀ (v : Fin k) (t : Fin m), proj t = v → t ≠ sec v → t ∈ Sc := by
    intro v t hpt hne
    change t ∈ Sᶜ
    rw [Finset.mem_compl]
    intro htS
    rcases Finset.mem_image.mp htS with ⟨u, _, rfl⟩
    rw [hsec u] at hpt
    subst hpt
    exact hne rfl
  have hsec_mem : ∀ v : Fin k, sec v ∈ S := fun v => Finset.mem_image_of_mem sec (Finset.mem_univ v)
  let build : (Sc → F) → (Fin m → F) := fun f i =>
    if hi : i ∈ Sc then f ⟨i, hi⟩
    else p (proj i) + ∑ t ∈ ((Finset.univ : Finset (Fin m)).filter (fun t => proj t = proj i)).erase i,
      if ht : t ∈ Sc then f ⟨t, ht⟩ else 0
  have hbuild_mem : ∀ f : Sc → F, fiberSum proj (build f) = p := by
    intro f
    funext v
    unfold fiberSum
    have hsec_in : sec v ∈ (Finset.univ : Finset (Fin m)).filter (fun i => proj i = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsec v⟩
    rw [← Finset.add_sum_erase _ _ hsec_in]
    have hnot_in : sec v ∉ Sc := by change sec v ∉ Sᶜ; simp [hsec_mem v]
    have hsec_val : build f (sec v) = p v +
        ∑ t ∈ ((Finset.univ : Finset (Fin m)).filter (fun t => proj t = v)).erase (sec v), build f t := by
      simp only [build, hnot_in, dite_false, hsec v]
      congr 1
      apply Finset.sum_congr rfl; intro t ht
      have hne : t ≠ sec v := (Finset.mem_erase.mp ht).1
      have hpt : proj t = v := (Finset.mem_filter.mp (Finset.mem_erase.mp ht).2).2
      have htSc : t ∈ Sc := hnotS v t hpt hne
      simp only [htSc, dite_true]
    rw [hsec_val, add_assoc, f_add_self, add_zero]
  have hbij : ((Finset.univ : Finset (Fin m → F)).filter (fun x => fiberSum proj x = p)).card =
      (Finset.univ : Finset (Sc → F)).card := by
    apply Finset.card_bij (fun x _ i => x i.1)
    · intro _ _; exact Finset.mem_univ _
    · intro x₁ hx₁ x₂ hx₂ heq
      have hf1 : fiberSum proj x₁ = p := (Finset.mem_filter.mp hx₁).2
      have hf2 : fiberSum proj x₂ = p := (Finset.mem_filter.mp hx₂).2
      funext i
      by_cases hi : i ∈ Sc
      · exact congrFun heq ⟨i, hi⟩
      · have hiS : i ∈ S := by
          change i ∉ Sᶜ at hi; rw [Finset.mem_compl] at hi; exact not_not.mp hi
        rcases Finset.mem_image.mp hiS with ⟨v, _, rfl⟩
        have h1 := congrFun hf1 v
        have h2 := congrFun hf2 v
        unfold fiberSum at h1 h2
        have hsec_in : sec v ∈ (Finset.univ : Finset (Fin m)).filter (fun t => proj t = v) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsec v⟩
        rw [← Finset.add_sum_erase _ _ hsec_in] at h1 h2
        have hrest : ∑ t ∈ ((Finset.univ : Finset (Fin m)).filter (fun t => proj t = v)).erase (sec v), x₁ t =
            ∑ t ∈ ((Finset.univ : Finset (Fin m)).filter (fun t => proj t = v)).erase (sec v), x₂ t := by
          apply Finset.sum_congr rfl; intro t ht
          have htSc : t ∈ Sc := hnotS v t (Finset.mem_filter.mp (Finset.mem_erase.mp ht).2).2 (Finset.mem_erase.mp ht).1
          exact congrFun heq ⟨t, htSc⟩
        rw [hrest] at h1
        have h3 := congrArg (· + ∑ t ∈ ((Finset.univ : Finset (Fin m)).filter (fun t => proj t = v)).erase (sec v), x₂ t) (h1.trans h2.symm)
        simp only [add_assoc, f_add_self, add_zero] at h3
        exact h3
    · intro f _
      refine ⟨build f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbuild_mem f⟩, ?_⟩
      funext ⟨i, hi⟩
      simp only [build, hi, dite_true]
  rw [hbij, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe, hSc_card]

lemma part1_isLeast {m a b : ℕ} (left : Fin m → Fin a) (right : Fin m → Fin b)
    (hleft : Function.Surjective left) (hright : Function.Surjective right)
    (c : (Fin m → F) × (Fin m → F)) (u v : F) :
    let L := (Finset.univ : Finset (Fin a)).filter (fun j => fiberSum left c.1 j ≠ u)
    let R := (Finset.univ : Finset (Fin b)).filter (fun j => fiberSum right c.2 j ≠ v)
    let edges := (Finset.univ : Finset (Fin m)).filter (fun i => left i ∈ L ∧ right i ∈ R)
    let mu := (edges.powerset.filter (fun M => (M.image left).card = M.card ∧ (M.image right).card = M.card)).sup Finset.card
    let dist := fun (c x : (Fin m → F) × (Fin m → F)) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => x.1 i ≠ c.1 i ∨ x.2 i ≠ c.2 i)).card
    IsLeast
      {k : ℕ | ∃ x : (Fin m → F) × (Fin m → F), (∀ j, fiberSum left x.1 j = u) ∧ (∀ j, fiberSum right x.2 j = v) ∧ dist c x = k}
      (L.card + R.card - mu) := by
  classical
  intro L R edges mu dist
  let validM := edges.powerset.filter (fun M => (M.image left).card = M.card ∧ (M.image right).card = M.card)
  have hempty_mem : ∅ ∈ validM := by
    simp [validM]
  have hvalid_ne : validM.Nonempty := ⟨∅, hempty_mem⟩
  constructor
  · obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_mem_eq_sup validM hvalid_ne Finset.card
    have hM_sub : M ⊆ edges := Finset.mem_powerset.mp (Finset.mem_filter.mp hM_mem).1
    have hM_left : (M.image left).card = M.card := (Finset.mem_filter.mp hM_mem).2.1
    have hM_right : (M.image right).card = M.card := (Finset.mem_filter.mp hM_mem).2.2
    have hML_sub : M.image left ⊆ L := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp (hM_sub hi)).2.1
    have hMR_sub : M.image right ⊆ R := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp (hM_sub hi)).2.2
    have hmu_eq : mu = M.card := hM_max
    let L' := L \ M.image left
    let R' := R \ M.image right
    choose p hp using hleft
    choose q hq using hright
    let P1 : Finset (Fin m) := L'.image p
    let P2 : Finset (Fin m) := R'.image q
    have hp_inj : Function.Injective p := fun j1 j2 h => by
      have := congrArg left h; rwa [hp j1, hp j2] at this
    have hq_inj : Function.Injective q := fun k1 k2 h => by
      have := congrArg right h; rwa [hq k1, hq k2] at this
    have hP1_card : P1.card = L'.card := Finset.card_image_of_injective _ hp_inj
    have hP2_card : P2.card = R'.card := Finset.card_image_of_injective _ hq_inj
    have hL'_card : L'.card = L.card - M.card := by
      have h := Finset.card_sdiff_add_card_eq_card hML_sub
      change L'.card + (M.image left).card = L.card at h
      rw [hM_left] at h; omega
    have hR'_card : R'.card = R.card - M.card := by
      have h := Finset.card_sdiff_add_card_eq_card hMR_sub
      change R'.card + (M.image right).card = R.card at h
      rw [hM_right] at h; omega
    have hdisj_MP1 : Disjoint M P1 := by
      rw [Finset.disjoint_left]; intro i hiM hiP1
      rcases Finset.mem_image.mp hiP1 with ⟨j, hjL', rfl⟩
      have h1 : left (p j) ∈ M.image left := Finset.mem_image_of_mem left hiM
      rw [hp j] at h1
      exact (Finset.mem_sdiff.mp hjL').2 h1
    have hdisj_MP2 : Disjoint M P2 := by
      rw [Finset.disjoint_left]; intro i hiM hiP2
      rcases Finset.mem_image.mp hiP2 with ⟨k, hkR', rfl⟩
      have h1 : right (q k) ∈ M.image right := Finset.mem_image_of_mem right hiM
      rw [hq k] at h1
      exact (Finset.mem_sdiff.mp hkR').2 h1
    have hdisj_P1P2 : Disjoint P1 P2 := by
      rw [Finset.disjoint_left]; intro i hiP1 hiP2
      rcases Finset.mem_image.mp hiP1 with ⟨j, hjL', rfl⟩
      rcases Finset.mem_image.mp hiP2 with ⟨k, hkR', hqp⟩
      have hli : left (p j) ∈ L ∧ left (p j) ∉ M.image left := by
        rw [hp j]; exact Finset.mem_sdiff.mp hjL'
      have hri : right (p j) ∈ R ∧ right (p j) ∉ M.image right := by
        rw [← hqp, hq k]; exact Finset.mem_sdiff.mp hkR'
      have hi_edges : p j ∈ edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli.1, hri.1⟩
      have hi_notM : p j ∉ M := Finset.disjoint_right.mp hdisj_MP1 (Finset.mem_image_of_mem p hjL')
      have hins_valid : insert (p j) M ∈ validM := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi_edges hM_sub), ?_, ?_⟩
        · rw [Finset.image_insert, Finset.card_insert_of_notMem hli.2,
            Finset.card_insert_of_notMem hi_notM, hM_left]
        · rw [Finset.image_insert, Finset.card_insert_of_notMem hri.2,
            Finset.card_insert_of_notMem hi_notM, hM_right]
      have hle := Finset.le_sup (f := Finset.card) hins_valid
      rw [Finset.card_insert_of_notMem hi_notM] at hle
      change M.card + 1 ≤ mu at hle
      omega
    let F1 := M ∪ P1
    let F2 := M ∪ P2
    let x1 : Fin m → F := fun i => c.1 i + (if i ∈ F1 then 1 else 0)
    let x2 : Fin m → F := fun i => c.2 i + (if i ∈ F2 then 1 else 0)
    have hF1_left_inj : Set.InjOn left (F1 : Set (Fin m)) := by
      have hM_inj : Set.InjOn left (M : Set (Fin m)) := Finset.injOn_of_card_image_eq hM_left
      intro i1 hi1 i2 hi2 hlr
      rcases Finset.mem_union.mp hi1 with h1M | h1P <;> rcases Finset.mem_union.mp hi2 with h2M | h2P
      · exact hM_inj h1M h2M hlr
      · rcases Finset.mem_image.mp h2P with ⟨j2, hj2, rfl⟩
        rw [hp j2] at hlr
        exact ((Finset.mem_sdiff.mp hj2).2 (hlr ▸ Finset.mem_image_of_mem left h1M)).elim
      · rcases Finset.mem_image.mp h1P with ⟨j1, hj1, rfl⟩
        rw [hp j1] at hlr
        exact ((Finset.mem_sdiff.mp hj1).2 (hlr.symm ▸ Finset.mem_image_of_mem left h2M)).elim
      · rcases Finset.mem_image.mp h1P with ⟨j1, _, rfl⟩
        rcases Finset.mem_image.mp h2P with ⟨j2, _, rfl⟩
        rw [hp j1, hp j2] at hlr; subst hlr; rfl
    have hF1_image : F1.image left = L := by
      ext j
      simp only [F1, Finset.image_union, Finset.mem_union]
      constructor
      · rintro (hjM | hjP)
        · exact hML_sub hjM
        · rcases Finset.mem_image.mp hjP with ⟨i, hiP, rfl⟩
          rcases Finset.mem_image.mp hiP with ⟨j', hj', rfl⟩
          rw [hp j']; exact (Finset.mem_sdiff.mp hj').1
      · intro hjL
        by_cases hjM : j ∈ M.image left
        · exact Or.inl hjM
        · right
          have hjL' : j ∈ L' := Finset.mem_sdiff.mpr ⟨hjL, hjM⟩
          exact Finset.mem_image.mpr ⟨p j, Finset.mem_image_of_mem p hjL', hp j⟩
    have hF2_right_inj : Set.InjOn right (F2 : Set (Fin m)) := by
      have hM_inj : Set.InjOn right (M : Set (Fin m)) := Finset.injOn_of_card_image_eq hM_right
      intro i1 hi1 i2 hi2 hlr
      rcases Finset.mem_union.mp hi1 with h1M | h1P <;> rcases Finset.mem_union.mp hi2 with h2M | h2P
      · exact hM_inj h1M h2M hlr
      · rcases Finset.mem_image.mp h2P with ⟨k2, hk2, rfl⟩
        rw [hq k2] at hlr
        exact ((Finset.mem_sdiff.mp hk2).2 (hlr ▸ Finset.mem_image_of_mem right h1M)).elim
      · rcases Finset.mem_image.mp h1P with ⟨k1, hk1, rfl⟩
        rw [hq k1] at hlr
        exact ((Finset.mem_sdiff.mp hk1).2 (hlr.symm ▸ Finset.mem_image_of_mem right h2M)).elim
      · rcases Finset.mem_image.mp h1P with ⟨k1, _, rfl⟩
        rcases Finset.mem_image.mp h2P with ⟨k2, _, rfl⟩
        rw [hq k1, hq k2] at hlr; subst hlr; rfl
    have hF2_image : F2.image right = R := by
      ext k
      simp only [F2, Finset.image_union, Finset.mem_union]
      constructor
      · rintro (hkM | hkP)
        · exact hMR_sub hkM
        · rcases Finset.mem_image.mp hkP with ⟨i, hiP, rfl⟩
          rcases Finset.mem_image.mp hiP with ⟨k', hk', rfl⟩
          rw [hq k']; exact (Finset.mem_sdiff.mp hk').1
      · intro hkR
        by_cases hkM : k ∈ M.image right
        · exact Or.inl hkM
        · right
          have hkR' : k ∈ R' := Finset.mem_sdiff.mpr ⟨hkR, hkM⟩
          exact Finset.mem_image.mpr ⟨q k, Finset.mem_image_of_mem q hkR', hq k⟩
    refine ⟨(x1, x2), ?_, ?_, ?_⟩
    · intro j
      unfold fiberSum
      simp only [x1, Finset.sum_add_distrib]
      change fiberSum left c.1 j + ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => left i = j), (if i ∈ F1 then (1 : F) else 0) = u
      by_cases hjL : j ∈ L
      · have hjim : j ∈ F1.image left := hF1_image.symm ▸ hjL
        rcases Finset.mem_image.mp hjim with ⟨i0, hi0F1, hli0⟩
        have hsum1 : ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => left i = j), (if i ∈ F1 then (1 : F) else 0) = 1 := by
          rw [Finset.sum_eq_single i0]
          · simp [hi0F1]
          · intro i hi hne
            have hli : left i = j := (Finset.mem_filter.mp hi).2
            have hiNot : i ∉ F1 := fun hiF1 => hne (hF1_left_inj hiF1 hi0F1 (hli.trans hli0.symm))
            simp [hiNot]
          · intro hni; exact (hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli0⟩)).elim
        rw [hsum1]
        exact f_add_one_eq_of_ne (Finset.mem_filter.mp hjL).2
      · have hsum0 : ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => left i = j), (if i ∈ F1 then (1 : F) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          have hli : left i = j := (Finset.mem_filter.mp hi).2
          have hiNot : i ∉ F1 := fun hiF1 => hjL (hF1_image ▸ (hli ▸ Finset.mem_image_of_mem left hiF1))
          simp [hiNot]
        rw [hsum0, add_zero]
        by_contra hne
        exact hjL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    · intro k
      unfold fiberSum
      simp only [x2, Finset.sum_add_distrib]
      change fiberSum right c.2 k + ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => right i = k), (if i ∈ F2 then (1 : F) else 0) = v
      by_cases hkR : k ∈ R
      · have hkim : k ∈ F2.image right := hF2_image.symm ▸ hkR
        rcases Finset.mem_image.mp hkim with ⟨i0, hi0F2, hri0⟩
        have hsum1 : ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => right i = k), (if i ∈ F2 then (1 : F) else 0) = 1 := by
          rw [Finset.sum_eq_single i0]
          · simp [hi0F2]
          · intro i hi hne
            have hri : right i = k := (Finset.mem_filter.mp hi).2
            have hiNot : i ∉ F2 := fun hiF2 => hne (hF2_right_inj hiF2 hi0F2 (hri.trans hri0.symm))
            simp [hiNot]
          · intro hni; exact (hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri0⟩)).elim
        rw [hsum1]
        exact f_add_one_eq_of_ne (Finset.mem_filter.mp hkR).2
      · have hsum0 : ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => right i = k), (if i ∈ F2 then (1 : F) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          have hri : right i = k := (Finset.mem_filter.mp hi).2
          have hiNot : i ∉ F2 := fun hiF2 => hkR (hF2_image ▸ (hri ▸ Finset.mem_image_of_mem right hiF2))
          simp [hiNot]
        rw [hsum0, add_zero]
        by_contra hne
        exact hkR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    · have hset : (Finset.univ : Finset (Fin m)).filter (fun i => x1 i ≠ c.1 i ∨ x2 i ≠ c.2 i) = M ∪ P1 ∪ P2 := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, x1, x2, F1, F2]
        have hx1 : (c.1 i + if i ∈ M ∪ P1 then (1 : F) else 0) ≠ c.1 i ↔ i ∈ M ∪ P1 := by
          by_cases h : i ∈ M ∪ P1
          · simp [h]
          · simp [h]
        have hx2 : (c.2 i + if i ∈ M ∪ P2 then (1 : F) else 0) ≠ c.2 i ↔ i ∈ M ∪ P2 := by
          by_cases h : i ∈ M ∪ P2
          · simp [h]
          · simp [h]
        rw [hx1, hx2]
        simp only [Finset.mem_union]
        constructor
        · rintro ((h | h) | (h | h))
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
      change ((Finset.univ : Finset (Fin m)).filter (fun i => x1 i ≠ c.1 i ∨ x2 i ≠ c.2 i)).card = L.card + R.card - mu
      rw [hset]
      have hd12 : Disjoint (M ∪ P1) P2 := Finset.disjoint_union_left.mpr ⟨hdisj_MP2, hdisj_P1P2⟩
      rw [Finset.card_union_of_disjoint hd12, Finset.card_union_of_disjoint hdisj_MP1,
        hP1_card, hP2_card, hL'_card, hR'_card, hmu_eq]
      have hML_le : M.card ≤ L.card := by rw [← hM_left]; exact Finset.card_le_card hML_sub
      have hMR_le : M.card ≤ R.card := by rw [← hM_right]; exact Finset.card_le_card hMR_sub
      omega
  · rintro k ⟨x, hxl, hxr, rfl⟩
    let D := (Finset.univ : Finset (Fin m)).filter (fun i => x.1 i ≠ c.1 i ∨ x.2 i ≠ c.2 i)
    have hexL : ∀ j ∈ L, ∃ i : Fin m, left i = j ∧ x.1 i ≠ c.1 i := by
      intro j hj
      by_contra hnone
      have heq : fiberSum left x.1 j = fiberSum left c.1 j := by
        unfold fiberSum
        apply Finset.sum_congr rfl; intro i hi
        by_contra hne
        exact hnone ⟨i, (Finset.mem_filter.mp hi).2, hne⟩
      rw [hxl j] at heq
      exact (Finset.mem_filter.mp hj).2 heq.symm
    have hexR : ∀ j ∈ R, ∃ i : Fin m, right i = j ∧ x.2 i ≠ c.2 i := by
      intro j hj
      by_contra hnone
      have heq : fiberSum right x.2 j = fiberSum right c.2 j := by
        unfold fiberSum
        apply Finset.sum_congr rfl; intro i hi
        by_contra hne
        exact hnone ⟨i, (Finset.mem_filter.mp hi).2, hne⟩
      rw [hxr j] at heq
      exact (Finset.mem_filter.mp hj).2 heq.symm
    let S1 : Finset (Fin m) := L.attach.image (fun j => (hexL j.1 j.2).choose)
    let S2 : Finset (Fin m) := R.attach.image (fun j => (hexR j.1 j.2).choose)
    have hS1_card : S1.card = L.card := by
      rw [Finset.card_image_of_injOn, Finset.card_attach]
      intro j1 _ j2 _ heq
      dsimp only at heq
      have h1 := (hexL j1.1 j1.2).choose_spec.1
      have h2 := (hexL j2.1 j2.2).choose_spec.1
      exact Subtype.ext (by rw [← h1, ← h2, heq])
    have hS2_card : S2.card = R.card := by
      rw [Finset.card_image_of_injOn, Finset.card_attach]
      intro j1 _ j2 _ heq
      dsimp only at heq
      have h1 := (hexR j1.1 j1.2).choose_spec.1
      have h2 := (hexR j2.1 j2.2).choose_spec.1
      exact Subtype.ext (by rw [← h1, ← h2, heq])
    have hS1_sub : S1 ⊆ D := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (hexL j.1 j.2).choose_spec.2⟩
    have hS2_sub : S2 ⊆ D := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (hexR j.1 j.2).choose_spec.2⟩
    let M := S1 ∩ S2
    have hM_sub : M ⊆ edges := by
      intro i hi
      have h1 := (Finset.mem_inter.mp hi).1
      have h2 := (Finset.mem_inter.mp hi).2
      rcases Finset.mem_image.mp h1 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j2, _, heq⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [(hexL j1.1 j1.2).choose_spec.1]; exact j1.2
      · rw [← heq, (hexR j2.1 j2.2).choose_spec.1]; exact j2.2
    have hM_left : (M.image left).card = M.card := by
      apply Finset.card_image_of_injOn
      intro i1 hi1 i2 hi2 hlr
      rcases Finset.mem_image.mp (Finset.mem_inter.mp hi1).1 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_inter.mp hi2).1 with ⟨j2, _, rfl⟩
      rw [(hexL j1.1 j1.2).choose_spec.1, (hexL j2.1 j2.2).choose_spec.1] at hlr
      have hj : j1 = j2 := Subtype.ext hlr
      subst hj; rfl
    have hM_right : (M.image right).card = M.card := by
      apply Finset.card_image_of_injOn
      intro i1 hi1 i2 hi2 hlr
      rcases Finset.mem_image.mp (Finset.mem_inter.mp hi1).2 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_inter.mp hi2).2 with ⟨j2, _, rfl⟩
      rw [(hexR j1.1 j1.2).choose_spec.1, (hexR j2.1 j2.2).choose_spec.1] at hlr
      have hj : j1 = j2 := Subtype.ext hlr
      subst hj; rfl
    have hM_valid : M ∈ validM :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hM_sub, hM_left, hM_right⟩
    have hM_le : (S1 ∩ S2).card ≤ mu := Finset.le_sup (f := Finset.card) hM_valid
    have hunion_le : (S1 ∪ S2).card ≤ D.card := Finset.card_le_card (Finset.union_subset hS1_sub hS2_sub)
    have hcard_ui := Finset.card_union_add_card_inter S1 S2
    rw [hS1_card, hS2_card] at hcard_ui
    change L.card + R.card - mu ≤ D.card
    omega

lemma main_proof : ∀ (m a b e : Nat),
  let F := ZMod 2
  let I := Fin m
  let A := Fin a
  let B := Fin b
  let W := I → F
  ∀ (left : I → A) (right : I → B), Function.Surjective left → Function.Surjective right →
    let ls := fun (x : W) (v : A) => ∑ i ∈ (Finset.univ : Finset I).filter (fun i => left i = v), x i
    let rs := fun (y : W) (v : B) => ∑ i ∈ (Finset.univ : Finset I).filter (fun i => right i = v), y i
    let works := fun (c : W × W) => ∀ x y : W,
      (∀ u v : A, ls x u = ls x v) → (∀ u v : B, rs y u = rs y v) →
      ((Finset.univ : Finset I).filter (fun i => x i = c.1 i ∧ y i = c.2 i)).card ≤ e
    let cost := fun (p : A → F) (q : B → F) (u v : F) =>
      let L := (Finset.univ : Finset A).filter (fun j => p j ≠ u)
      let R := (Finset.univ : Finset B).filter (fun j => q j ≠ v)
      let edges := (Finset.univ : Finset I).filter (fun i => left i ∈ L ∧ right i ∈ R)
      let mu := (edges.powerset.filter (fun M => (M.image left).card = M.card ∧ (M.image right).card = M.card)).sup Finset.card
      L.card + R.card - mu
    let passes := fun (p : A → F) (q : B → F) => ∀ u v : F, m ≤ e + cost p q u v
    let dist := fun (c x : W × W) => ((Finset.univ : Finset I).filter (fun i => x.1 i ≠ c.1 i ∨ x.2 i ≠ c.2 i)).card
    (∀ (c : W × W) (u v : F), IsLeast
      {k : Nat | ∃ x : W × W, (∀ j, ls x.1 j = u) ∧ (∀ j, rs x.2 j = v) ∧ dist c x = k}
      (cost (ls c.1) (rs c.2) u v)) ∧
    (∀ c : W × W, works c ↔ passes (ls c.1) (rs c.2)) ∧
      ((Finset.univ : Finset (W × W)).filter (fun c => @decide (works c) (Classical.propDecidable _) = true)).card =
      2 ^ (2 * m - a - b) * ((Finset.univ : Finset ((A → F) × (B → F))).filter (fun v =>
        @decide (passes v.1 v.2) (Classical.propDecidable _) = true)).card := by
  classical
  intro m a b e F I A B W left right hleft hright ls rs works cost passes dist
  have hp1 : ∀ (c : W × W) (u v : F), IsLeast
      {k : Nat | ∃ x : W × W, (∀ j, ls x.1 j = u) ∧ (∀ j, rs x.2 j = v) ∧ dist c x = k}
      (cost (ls c.1) (rs c.2) u v) := fun c u v =>
    part1_isLeast left right hleft hright c u v
  have hp2 : ∀ c : W × W, works c ↔ passes (ls c.1) (rs c.2) := by
    intro c
    have hcomp : ∀ x : W × W,
        ((Finset.univ : Finset I).filter (fun i => x.1 i = c.1 i ∧ x.2 i = c.2 i)).card + dist c x = m := by
      intro x
      have hdisj : Disjoint
          ((Finset.univ : Finset I).filter (fun i => x.1 i = c.1 i ∧ x.2 i = c.2 i))
          ((Finset.univ : Finset I).filter (fun i => x.1 i ≠ c.1 i ∨ x.2 i ≠ c.2 i)) := by
        rw [Finset.disjoint_filter]; intro i _ h1 h2; rcases h2 with h | h
        · exact h h1.1
        · exact h h1.2
      have hunion : ((Finset.univ : Finset I).filter (fun i => x.1 i = c.1 i ∧ x.2 i = c.2 i)) ∪
          ((Finset.univ : Finset I).filter (fun i => x.1 i ≠ c.1 i ∨ x.2 i ≠ c.2 i)) = Finset.univ := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        by_cases h1 : x.1 i = c.1 i
        · by_cases h2 : x.2 i = c.2 i
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h1)
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at hc
      exact hc.symm
    constructor
    · intro hwc u v
      obtain ⟨x, hxl, hxr, hdist⟩ := (hp1 c u v).1
      have h1 : ∀ u' v' : A, ls x.1 u' = ls x.1 v' := fun u' v' => (hxl u').trans (hxl v').symm
      have h2 : ∀ u' v' : B, rs x.2 u' = rs x.2 v' := fun u' v' => (hxr u').trans (hxr v').symm
      have hle := hwc x.1 x.2 h1 h2
      have hcm := hcomp x
      omega
    · intro hpc x y hx hy
      have hexU : ∃ u : F, ∀ j : A, ls x j = u := by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · exact ⟨0, fun j => j.elim0⟩
        · exact ⟨ls x ⟨0, ha⟩, fun j => hx j ⟨0, ha⟩⟩
      have hexV : ∃ v : F, ∀ j : B, rs y j = v := by
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · exact ⟨0, fun j => j.elim0⟩
        · exact ⟨rs y ⟨0, hb⟩, fun j => hy j ⟨0, hb⟩⟩
      obtain ⟨u, hu⟩ := hexU
      obtain ⟨v, hv⟩ := hexV
      have hge : cost (ls c.1) (rs c.2) u v ≤ dist c (x, y) :=
        (hp1 c u v).2 ⟨(x, y), hu, hv, rfl⟩
      have hpm := hpc u v
      have hcm := hcomp (x, y)
      dsimp only at hcm
      omega
  refine ⟨hp1, hp2, ?_⟩
  let Φ : W × W → (A → F) × (B → F) := fun c => (ls c.1, rs c.2)
  let S_works := (Finset.univ : Finset (W × W)).filter (fun c => @decide (works c) (Classical.propDecidable _) = true)
  let S_pass := (Finset.univ : Finset ((A → F) × (B → F))).filter (fun v => @decide (passes v.1 v.2) (Classical.propDecidable _) = true)
  have hmaps : ∀ c ∈ S_works, Φ c ∈ S_pass := by
    intro c hc
    have hwc : works c := @of_decide_eq_true (works c) (Classical.propDecidable _) (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, @decide_eq_true (passes (ls c.1) (rs c.2)) (Classical.propDecidable _) ((hp2 c).mp hwc)⟩
  have hfib_sum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib_eq : ∀ v ∈ S_pass, (S_works.filter (fun c => Φ c = v)).card = 2 ^ (2 * m - a - b) := by
    intro v hv
    have hvp : passes v.1 v.2 := @of_decide_eq_true (passes v.1 v.2) (Classical.propDecidable _) (Finset.mem_filter.mp hv).2
    have hset : S_works.filter (fun c => Φ c = v) =
        ((Finset.univ : Finset W).filter (fun x => ls x = v.1)) ×ˢ
        ((Finset.univ : Finset W).filter (fun y => rs y = v.2)) := by
      ext ⟨c1, c2⟩
      simp only [S_works, Φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Prod.ext_iff]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨@decide_eq_true (works (c1, c2)) (Classical.propDecidable _) ((hp2 (c1, c2)).mpr (by rw [h1, h2]; exact hvp)), h1, h2⟩
    rw [hset, Finset.card_product]
    have h1 := card_fiberSum_eq left hleft v.1
    have h2 := card_fiberSum_eq right hright v.2
    change ((Finset.univ : Finset W).filter (fun x => fiberSum left x = v.1)).card *
      ((Finset.univ : Finset W).filter (fun y => fiberSum right y = v.2)).card = _
    rw [h1, h2, ← pow_add]
    have ha_le : a ≤ m := by
      have := Fintype.card_le_of_surjective left hleft
      simpa [A, I, Fintype.card_fin] using this
    have hb_le : b ≤ m := by
      have := Fintype.card_le_of_surjective right hright
      simpa [B, I, Fintype.card_fin] using this
    congr 1; omega
  rw [hfib_sum, Finset.sum_congr rfl hfib_eq, Finset.sum_const, smul_eq_mul, mul_comm]

end PEqualNP.Outside.L_lib_1015_aux

theorem PEqualNP.Outside.L_lib_1015 : (∀ (m a b e : Nat),
  let F := ZMod 2
  let I := Fin m
  let A := Fin a
  let B := Fin b
  let W := I → F
  ∀ (left : I → A) (right : I → B), Function.Surjective left → Function.Surjective right →
    let ls := fun (x : W) (v : A) => ∑ i ∈ (Finset.univ : Finset I).filter (fun i => left i = v), x i
    let rs := fun (y : W) (v : B) => ∑ i ∈ (Finset.univ : Finset I).filter (fun i => right i = v), y i
    let works := fun (c : W × W) => ∀ x y : W,
      (∀ u v : A, ls x u = ls x v) → (∀ u v : B, rs y u = rs y v) →
      ((Finset.univ : Finset I).filter (fun i => x i = c.1 i ∧ y i = c.2 i)).card ≤ e
    let cost := fun (p : A → F) (q : B → F) (u v : F) =>
      let L := (Finset.univ : Finset A).filter (fun j => p j ≠ u)
      let R := (Finset.univ : Finset B).filter (fun j => q j ≠ v)
      let edges := (Finset.univ : Finset I).filter (fun i => left i ∈ L ∧ right i ∈ R)
      let mu := (edges.powerset.filter (fun M => (M.image left).card = M.card ∧ (M.image right).card = M.card)).sup Finset.card
      L.card+R.card-mu
    let passes := fun (p : A → F) (q : B → F) => ∀ u v : F, m ≤ e + cost p q u v
    let dist := fun (c x : W × W) => ((Finset.univ : Finset I).filter (fun i => x.1 i ≠ c.1 i ∨ x.2 i ≠ c.2 i)).card
    (∀ (c : W × W) (u v : F), IsLeast
      {k : Nat | ∃ x : W × W, (∀ j, ls x.1 j = u) ∧ (∀ j, rs x.2 j = v) ∧ dist c x = k}
      (cost (ls c.1) (rs c.2) u v)) ∧
    (∀ c : W × W, works c ↔ passes (ls c.1) (rs c.2)) ∧
      ((Finset.univ : Finset (W × W)).filter (fun c => @decide (works c) (Classical.propDecidable _) = true)).card =
      2^(2*m-a-b) * ((Finset.univ : Finset ((A → F) × (B → F))).filter (fun v =>
        @decide (passes v.1 v.2) (Classical.propDecidable _) = true)).card) :=
  PEqualNP.Outside.L_lib_1015_aux.main_proof
