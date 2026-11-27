import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_382_aux

private lemma prod_two_pow_coeff {t N : ℕ} (a : Fin t → Bool → ℕ) :
    (∏ c : Fin t,
      ((Polynomial.X : Polynomial ℕ) ^ (a c false) + (Polynomial.X : Polynomial ℕ) ^ (a c true))).coeff N =
      ∑ f : Fin t → Bool, if N = ∑ c : Fin t, a c (f c) then 1 else 0 := by
  have hprod :
      (∏ c : Fin t,
        ((Polynomial.X : Polynomial ℕ) ^ (a c false) + (Polynomial.X : Polynomial ℕ) ^ (a c true))) =
      ∑ f : Fin t → Bool, (Polynomial.X : Polynomial ℕ) ^ (∑ c : Fin t, a c (f c)) := by
    calc (∏ c : Fin t,
          ((Polynomial.X : Polynomial ℕ) ^ (a c false) + (Polynomial.X : Polynomial ℕ) ^ (a c true)))
        = ∏ c : Fin t, ∑ b : Bool, (Polynomial.X : Polynomial ℕ) ^ (a c b) := by
          refine Finset.prod_congr rfl fun c _ => ?_
          rw [Fintype.sum_bool, add_comm]
      _ = ∑ f : Fin t → Bool, ∏ c : Fin t, (Polynomial.X : Polynomial ℕ) ^ (a c (f c)) :=
          Fintype.prod_sum (fun c (b : Bool) => (Polynomial.X : Polynomial ℕ) ^ (a c b))
      _ = ∑ f : Fin t → Bool, (Polynomial.X : Polynomial ℕ) ^ (∑ c : Fin t, a c (f c)) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          exact Finset.prod_pow_eq_pow_sum Finset.univ (fun c => a c (f c)) (Polynomial.X : Polynomial ℕ)
  rw [hprod]
  change Polynomial.lcoeff ℕ N (∑ f : Fin t → Bool, (Polynomial.X : Polynomial ℕ) ^ (∑ c : Fin t, a c (f c))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact Polynomial.coeff_X_pow (∑ c : Fin t, a c (f c)) N

private lemma prod_two_pow_coeff_pos_iff {t N : ℕ} (a : Fin t → Bool → ℕ) :
    0 < (∏ c : Fin t,
      ((Polynomial.X : Polynomial ℕ) ^ (a c false) + (Polynomial.X : Polynomial ℕ) ^ (a c true))).coeff N ↔
      ∃ f : Fin t → Bool, (∑ c : Fin t, a c (f c)) = N := by
  rw [prod_two_pow_coeff]
  constructor
  · intro hpos
    by_contra hall
    push Not at hall
    have h0 : (∑ f : Fin t → Bool, if N = ∑ c : Fin t, a c (f c) then (1 : ℕ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [if_neg (Ne.symm (hall f))]
    omega
  · rintro ⟨f, hf⟩
    have hle : (if N = ∑ c : Fin t, a c (f c) then (1 : ℕ) else 0) ≤
        ∑ g : Fin t → Bool, if N = ∑ c : Fin t, a c (g c) then (1 : ℕ) else 0 :=
      Finset.single_le_sum
        (f := fun g : Fin t → Bool => if N = ∑ c : Fin t, a c (g c) then (1 : ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ f)
    rw [if_pos hf.symm] at hle
    omega

private lemma card_filter_lt_half (N : ℕ) :
    (Finset.univ.filter (fun w : Fin (2 * N) => w.val < N)).card = N := by
  have hbij : (Finset.univ : Finset (Fin N)).card =
      (Finset.univ.filter (fun w : Fin (2 * N) => w.val < N)).card := by
    refine Finset.card_bij (fun (k : Fin N) _ => (⟨k.val, by omega⟩ : Fin (2 * N))) ?_ ?_ ?_
    · intro k _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact k.isLt
    · intro a _ b _ h
      exact Fin.ext (congrArg (Fin.val : Fin (2 * N) → ℕ) h)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨⟨w.val, hw⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [← hbij, Finset.card_fin]

private lemma card_perm_lt_half {N : ℕ} (π : Equiv.Perm (Fin (2 * N))) :
    (Finset.univ.filter (fun v : Fin (2 * N) => decide ((π v).val < N) = true)).card = N := by
  have hbij : (Finset.univ.filter (fun v : Fin (2 * N) => decide ((π v).val < N) = true)).card =
      (Finset.univ.filter (fun w : Fin (2 * N) => w.val < N)).card := by
    refine Finset.card_bij (fun v _ => π v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hv ⊢
      exact hv
    · intro a _ b _ h
      exact π.injective h
    · intro w hw
      refine ⟨π.symm w, ?_, π.apply_symm_apply w⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hw ⊢
      rw [π.apply_symm_apply]
      exact hw
  rw [hbij, card_filter_lt_half]

private lemma perm_of_balanced_col {N : ℕ} (col : Fin (2 * N) → Bool)
    (hbal : (Finset.univ.filter (fun v : Fin (2 * N) => col v = true)).card = N) :
    ∃ π : Equiv.Perm (Fin (2 * N)), ∀ v, decide ((π v).val < N) = col v := by
  let S : Finset (Fin (2 * N)) := Finset.univ.filter (fun v => col v = true)
  let T : Finset (Fin (2 * N)) := Finset.univ.filter (fun v => col v = false)
  let L : Finset (Fin (2 * N)) := Finset.univ.filter (fun w => w.val < N)
  let R : Finset (Fin (2 * N)) := Finset.univ.filter (fun w => ¬ (w.val < N))
  have hST_disj : Disjoint S T := by
    refine Finset.disjoint_left.mpr fun v hvS hvT => ?_
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hvS hvT
    rw [hvS] at hvT
    exact Bool.noConfusion hvT
  have hST_union : S ∪ T = Finset.univ := by
    ext v
    simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases col v <;> simp
  have hT_card : T.card = N := by
    have hadd : S.card + T.card = 2 * N := by
      rw [← Finset.card_union_of_disjoint hST_disj, hST_union, Finset.card_fin]
    have hS_card : S.card = N := hbal
    omega
  have hLR_disj : Disjoint L R := by
    refine Finset.disjoint_left.mpr fun w hwL hwR => ?_
    simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at hwL hwR
    exact hwR hwL
  have hLR_union : L ∪ R = Finset.univ := by
    ext w
    simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact em (w.val < N)
  have hL_card : L.card = N := card_filter_lt_half N
  have hR_card : R.card = N := by
    have hadd : L.card + R.card = 2 * N := by
      rw [← Finset.card_union_of_disjoint hLR_disj, hLR_union, Finset.card_fin]
    omega
  have hSL : Fintype.card {v // v ∈ S} = Fintype.card {w // w ∈ L} := by
    simp only [Fintype.card_coe, hL_card]
    exact hbal
  have hTR : Fintype.card {v // v ∈ T} = Fintype.card {w // w ∈ R} := by
    simp only [Fintype.card_coe, hT_card, hR_card]
  let eS : {v // v ∈ S} ≃ {w // w ∈ L} := Fintype.equivOfCardEq hSL
  let eT : {v // v ∈ T} ≃ {w // w ∈ R} := Fintype.equivOfCardEq hTR
  have hnotS_T : ∀ v, v ∉ S → v ∈ T := by
    intro v hv
    have hmem : v ∈ S ∪ T := by rw [hST_union]; exact Finset.mem_univ v
    rcases Finset.mem_union.mp hmem with h1 | h2
    · exact absurd h1 hv
    · exact h2
  have hnotL_R : ∀ w, w ∉ L → w ∈ R := by
    intro w hw
    have hmem : w ∈ L ∪ R := by rw [hLR_union]; exact Finset.mem_univ w
    rcases Finset.mem_union.mp hmem with h1 | h2
    · exact absurd h1 hw
    · exact h2
  have hR_notL : ∀ w, w ∈ R → w ∉ L := fun w hw hL => Finset.disjoint_left.mp hLR_disj hL hw
  have hT_notS : ∀ v, v ∈ T → v ∉ S := fun v hv hS => Finset.disjoint_left.mp hST_disj hS hv
  let π : Equiv.Perm (Fin (2 * N)) :=
    { toFun := fun v =>
        if hv : v ∈ S then (eS ⟨v, hv⟩).val else (eT ⟨v, hnotS_T v hv⟩).val
      invFun := fun w =>
        if hw : w ∈ L then (eS.symm ⟨w, hw⟩).val else (eT.symm ⟨w, hnotL_R w hw⟩).val
      left_inv := fun v => by
        by_cases hv : v ∈ S
        · simp only [dif_pos hv]
          have hmemL : (eS ⟨v, hv⟩).val ∈ L := (eS ⟨v, hv⟩).property
          simp only [dif_pos hmemL, Subtype.coe_eta, Equiv.symm_apply_apply]
        · simp only [dif_neg hv]
          have hmemR : (eT ⟨v, hnotS_T v hv⟩).val ∈ R := (eT ⟨v, hnotS_T v hv⟩).property
          have hnotL : (eT ⟨v, hnotS_T v hv⟩).val ∉ L := hR_notL _ hmemR
          simp only [dif_neg hnotL, Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun w => by
        by_cases hw : w ∈ L
        · simp only [dif_pos hw]
          have hmemS : (eS.symm ⟨w, hw⟩).val ∈ S := (eS.symm ⟨w, hw⟩).property
          simp only [dif_pos hmemS, Subtype.coe_eta, Equiv.apply_symm_apply]
        · simp only [dif_neg hw]
          have hmemT : (eT.symm ⟨w, hnotL_R w hw⟩).val ∈ T := (eT.symm ⟨w, hnotL_R w hw⟩).property
          have hnotS : (eT.symm ⟨w, hnotL_R w hw⟩).val ∉ S := hT_notS _ hmemT
          simp only [dif_neg hnotS, Subtype.coe_eta, Equiv.apply_symm_apply] }
  refine ⟨π, fun v => ?_⟩
  by_cases hv : col v = true
  · have hvS : v ∈ S := by simp [S, hv]
    have hmemL : (π v).val < N := by
      have hm : π v ∈ L := by
        change (if hv' : v ∈ S then (eS ⟨v, hv'⟩).val else (eT ⟨v, hnotS_T v hv'⟩).val) ∈ L
        rw [dif_pos hvS]
        exact (eS ⟨v, hvS⟩).property
      simpa [L] using hm
    rw [hv, decide_eq_true hmemL]
  · have hvF : col v = false := by cases h : col v <;> simp_all
    have hvNotS : v ∉ S := by simp [S, hvF]
    have hnotLt : ¬ ((π v).val < N) := by
      have hm : π v ∈ R := by
        change (if hv' : v ∈ S then (eS ⟨v, hv'⟩).val else (eT ⟨v, hnotS_T v hv'⟩).val) ∈ R
        rw [dif_neg hvNotS]
        exact (eT ⟨v, hnotS_T v hvNotS⟩).property
      simpa [R] using hm
    rw [hvF, decide_eq_false hnotLt]

private lemma card_filter_eq_sum_sides {N t : ℕ} (base : Fin (2 * N) → Bool)
    (comp : Fin (2 * N) → Fin t) (flip : Fin t → Bool) :
    (Finset.univ.filter (fun v : Fin (2 * N) => decide (base v = flip (comp v)) = true)).card =
      ∑ c : Fin t, (Finset.univ.filter (fun v : Fin (2 * N) => comp v = c ∧ base v = flip c)).card := by
  have hbiU : Finset.univ.filter (fun v : Fin (2 * N) => decide (base v = flip (comp v)) = true) =
      Finset.univ.biUnion (fun c : Fin t =>
        Finset.univ.filter (fun v : Fin (2 * N) => comp v = c ∧ base v = flip c)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_biUnion]
    constructor
    · intro h; exact ⟨comp v, rfl, h⟩
    · rintro ⟨c, rfl, h⟩; exact h
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin t))
      (fun c => Finset.univ.filter (fun v : Fin (2 * N) => comp v = c ∧ base v = flip c)) := by
    intro c1 _ c2 _ hne
    refine Finset.disjoint_left.mpr fun v hv1 hv2 => hne ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
    exact hv1.1.symm.trans hv2.1
  rw [hbiU, Finset.card_biUnion hdisj]

private lemma bool_flip_ne (b1 b2 f : Bool) (h : b1 ≠ b2) :
    decide (b1 = f) ≠ decide (b2 = f) := by
  cases b1 <;> cases b2 <;> cases f <;> simp_all

private lemma bool_eqv_edge (c1 c2 b1 b2 : Bool) (hc : c1 ≠ c2) (hb : b1 ≠ b2) :
    decide (c1 = b1) = decide (c2 = b2) := by
  cases c1 <;> cases c2 <;> cases b1 <;> cases b2 <;> simp_all

private lemma bool_true_iff_base_eq_eqv (c b : Bool) :
    c = true ↔ decide (b = decide (c = b)) = true := by
  cases c <;> cases b <;> decide

end PEqualNP.Outside.L_lib_382_aux

open PEqualNP.Outside.L_lib_382_aux in
theorem PEqualNP.Outside.L_lib_382 :
    ∀ (n N t : ℕ) (left right : Fin n → Fin (2 * N))
      (base : Fin (2 * N) → Bool) (comp : Fin (2 * N) → Fin t),
      (∀ z, base (left z) ≠ base (right z)) →
      Function.Surjective comp →
      (∀ x y, comp x = comp y ↔
        Relation.EqvGen (fun u v => ∃ z, left z = u ∧ right z = v) x y) →
      let sides := fun (c : Fin t) (b : Bool) =>
        (Finset.univ.filter (fun v => comp v = c ∧ base v = b)).card
      let orientations : Polynomial ℕ :=
        ∏ c : Fin t, (Polynomial.X ^ (sides c false) + Polynomial.X ^ (sides c true))
      (∃ π : Equiv.Perm (Fin (2 * N)), ∀ z,
        decide ((π (left z)).val < N) ≠ decide ((π (right z)).val < N)) ↔
        0 < orientations.coeff N := by
  intro n N t left right base comp hbase hsurj hcomp sides orientations
  rw [prod_two_pow_coeff_pos_iff sides]
  constructor
  · rintro ⟨π, hπ⟩
    let col : Fin (2 * N) → Bool := fun v => decide ((π v).val < N)
    let eqv : Fin (2 * N) → Bool := fun v => decide (col v = base v)
    have heqv_rel : ∀ x y,
        Relation.EqvGen (fun u v => ∃ z, left z = u ∧ right z = v) x y → eqv x = eqv y := by
      intro x y hrel
      induction hrel with
      | rel u v huv =>
        rcases huv with ⟨z, rfl, rfl⟩
        exact bool_eqv_edge (col (left z)) (col (right z)) (base (left z)) (base (right z))
          (hπ z) (hbase z)
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    let rep : Fin t → Fin (2 * N) := fun c => Classical.choose (hsurj c)
    have hrep : ∀ c, comp (rep c) = c := fun c => Classical.choose_spec (hsurj c)
    let flip : Fin t → Bool := fun c => eqv (rep c)
    refine ⟨flip, ?_⟩
    have hcol_eq : ∀ v, col v = true ↔ decide (base v = flip (comp v)) = true := by
      intro v
      have hsame : eqv v = flip (comp v) := by
        apply heqv_rel
        exact (hcomp v (rep (comp v))).mp (hrep (comp v)).symm
      rw [← hsame]
      exact bool_true_iff_base_eq_eqv (col v) (base v)
    have hfilt :
        Finset.univ.filter (fun v : Fin (2 * N) => decide (base v = flip (comp v)) = true) =
        Finset.univ.filter (fun v : Fin (2 * N) => col v = true) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcol_eq v).symm
    rw [← card_filter_eq_sum_sides base comp flip, hfilt]
    exact card_perm_lt_half π
  · rintro ⟨flip, hflip⟩
    let col : Fin (2 * N) → Bool := fun v => decide (base v = flip (comp v))
    have hbal : (Finset.univ.filter (fun v : Fin (2 * N) => col v = true)).card = N := by
      rw [card_filter_eq_sum_sides base comp flip]
      exact hflip
    rcases perm_of_balanced_col col hbal with ⟨π, hπ⟩
    refine ⟨π, fun z => ?_⟩
    rw [hπ (left z), hπ (right z)]
    have hceq : comp (left z) = comp (right z) :=
      (hcomp (left z) (right z)).mpr (Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩)
    dsimp only [col]
    rw [hceq]
    exact bool_flip_ne (base (left z)) (base (right z)) (flip (comp (right z))) (hbase z)
