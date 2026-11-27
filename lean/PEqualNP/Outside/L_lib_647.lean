import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_647_aux

private lemma card_VV (t : ℕ) :
    Fintype.card ((Fin t → ZMod 2) × (Fin t → ZMod 2)) = 4 ^ t := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← mul_pow]
  rfl

private def setCoord {t : ℕ} (j : Fin t) (a b : ZMod 2)
    (z : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    (Fin t → ZMod 2) × (Fin t → ZMod 2) :=
  (Function.update z.1 j a, Function.update z.2 j b)

private lemma four_mul_fiber_card {t : ℕ} (j : Fin t)
    (S : Finset ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (hind : ∀ z a b, setCoord j a b z ∈ S ↔ z ∈ S) (a0 b0 : ZMod 2) :
    4 * (S.filter (fun z => z.1 j = a0 ∧ z.2 j = b0)).card = S.card := by
  have hfib_eq : ∀ a b : ZMod 2,
      (S.filter (fun z => z.1 j = a ∧ z.2 j = b)).card =
        (S.filter (fun z => z.1 j = a0 ∧ z.2 j = b0)).card := by
    intro a b
    refine Finset.card_bij (fun z _ => setCoord j a0 b0 z) ?_ ?_ ?_
    · intro z hz
      have h1 := (Finset.mem_filter.mp hz).1
      refine Finset.mem_filter.mpr ⟨(hind z a0 b0).mpr h1, ?_, ?_⟩
      · simp [setCoord]
      · simp [setCoord]
    · intro z1 hz1 z2 hz2 hEq
      have h1 := (Finset.mem_filter.mp hz1).2
      have h2 := (Finset.mem_filter.mp hz2).2
      apply Prod.ext
      · funext i
        by_cases hij : i = j
        · subst hij; rw [h1.1, h2.1]
        · have hv := congrFun (congrArg Prod.fst hEq) i
          dsimp only [setCoord] at hv
          simpa [Function.update, hij] using hv
      · funext i
        by_cases hij : i = j
        · subst hij; rw [h1.2, h2.2]
        · have hv := congrFun (congrArg Prod.snd hEq) i
          dsimp only [setCoord] at hv
          simpa [Function.update, hij] using hv
    · intro w hw
      have h1 := (Finset.mem_filter.mp hw).1
      have h2 := (Finset.mem_filter.mp hw).2
      refine ⟨setCoord j a b w, Finset.mem_filter.mpr ⟨(hind w a b).mpr h1, by simp [setCoord]⟩, ?_⟩
      apply Prod.ext
      · funext i
        by_cases hij : i = j
        · subst hij; simp [setCoord, h2.1]
        · simp [setCoord, Function.update, hij]
      · funext i
        by_cases hij : i = j
        · subst hij; simp [setCoord, h2.2]
        · simp [setCoord, Function.update, hij]
  have hpart : S.card = ∑ p : ZMod 2 × ZMod 2, (S.filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) => (z.1 j, z.2 j))
      (s := S) (t := (Finset.univ : Finset (ZMod 2 × ZMod 2))) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun p _ => congrArg Finset.card (by ext z; simp [Prod.ext_iff])
  rw [hpart]
  have hconst : (∑ p : ZMod 2 × ZMod 2, (S.filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card) =
      ∑ _p : ZMod 2 × ZMod 2, (S.filter (fun z => z.1 j = a0 ∧ z.2 j = b0)).card :=
    Finset.sum_congr rfl fun p _ => hfib_eq p.1 p.2
  rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]

private lemma card_hyperplane_two_mul {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (γ : Fin t → ZMod 2) (j : Fin t)
    (hsrc : ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0)) :
    2 * (Finset.univ.filter (fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = 0)).card = 4 ^ t := by
  rcases hsrc with ⟨i0, hi0, hAB⟩
  let cf : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ZMod 2 := fun z =>
    γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
  let H0 := Finset.univ.filter (fun z => cf z = 0)
  let H1 := Finset.univ.filter (fun z => cf z = 1)
  have h11 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x; fin_cases x
    · left; rfl
    · right; rfl
  have hdisj : Disjoint H0 H1 := by
    rw [Finset.disjoint_left]
    intro z h0 h1
    have a0 := (Finset.mem_filter.mp h0).2
    have a1 := (Finset.mem_filter.mp h1).2
    rw [a0] at a1; exact absurd a1 (by decide)
  have hunion : H0 ∪ H1 = Finset.univ := by
    ext z
    simp only [H0, H1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact h11 (cf z)
  have hflip : ∃ τ : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ((Fin t → ZMod 2) × (Fin t → ZMod 2)),
      (∀ z, τ (τ z) = z) ∧ (∀ z, cf (τ z) = cf z + 1) := by
    have hmem : i0 ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hi0
    rcases hAB with hA | hB
    · have hA1 : A i0 j = 1 := by
        rcases h11 (A i0 j) with h0 | h1
        · exact absurd h0 hA
        · exact h1
      refine ⟨fun z => (Function.update z.1 i0 (z.1 i0 + 1), z.2), ?_, ?_⟩
      · intro z
        apply Prod.ext
        · funext i
          by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            generalize z.1 i = v; revert v; decide
          · simp [Function.update, hi]
        · rfl
      · intro z
        dsimp only [cf]
        rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
        have hrest :
            (∑ i ∈ (Finset.Ioi j).erase i0, (Function.update z.1 i0 (z.1 i0 + 1) i * A i j + z.2 i * B i j)) =
              ∑ i ∈ (Finset.Ioi j).erase i0, (z.1 i * A i j + z.2 i * B i j) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          simp [Function.update, hne]
        rw [hrest, Function.update_self, hA1]
        ring
    · have hB1 : B i0 j = 1 := by
        rcases h11 (B i0 j) with h0 | h1
        · exact absurd h0 hB
        · exact h1
      refine ⟨fun z => (z.1, Function.update z.2 i0 (z.2 i0 + 1)), ?_, ?_⟩
      · intro z
        apply Prod.ext
        · rfl
        · funext i
          by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            generalize z.2 i = v; revert v; decide
          · simp [Function.update, hi]
      · intro z
        dsimp only [cf]
        rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
        have hrest :
            (∑ i ∈ (Finset.Ioi j).erase i0, (z.1 i * A i j + Function.update z.2 i0 (z.2 i0 + 1) i * B i j)) =
              ∑ i ∈ (Finset.Ioi j).erase i0, (z.1 i * A i j + z.2 i * B i j) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          simp [Function.update, hne]
        rw [hrest, Function.update_self, hB1]
        ring
  rcases hflip with ⟨τ, hinv, hadd1⟩
  have hcard_eq : H0.card = H1.card := by
    refine Finset.card_bij (fun z _ => τ z) ?_ ?_ ?_
    · intro z hz
      have hc0 : cf z = 0 := (Finset.mem_filter.mp hz).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hadd1, hc0, zero_add]
    · intro z1 _ z2 _ hEq
      have := congrArg τ hEq
      rwa [hinv, hinv] at this
    · intro w hw
      have hc1 : cf w = 1 := (Finset.mem_filter.mp hw).2
      refine ⟨τ w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hinv w⟩
      rw [hadd1, hc1]
      decide
  have htot : H0.card + H1.card = 4 ^ t := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, card_VV]
  change 2 * H0.card = 4 ^ t
  omega

private lemma four_mul_union_update {t : ℕ} (j : Fin t)
    (H U : Finset ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (hHind : ∀ z a b, setCoord j a b z ∈ H ↔ z ∈ H)
    (hUind : ∀ z a b, setCoord j a b z ∈ U ↔ z ∈ U) :
    let D := H.filter (fun z => ¬ (z.1 j = 0 ∧ z.2 j = 0))
    4 * (D ∪ U).card = U.card + 3 * (H ∪ U).card := by
  intro D
  have hHUind : ∀ z a b, setCoord j a b z ∈ H ∪ U ↔ z ∈ H ∪ U := by
    intro z a b
    simp only [Finset.mem_union, hHind, hUind]
  have hpart : (D ∪ U).card =
      ∑ p : ZMod 2 × ZMod 2, ((D ∪ U).filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) => (z.1 j, z.2 j))
      (s := D ∪ U) (t := (Finset.univ : Finset (ZMod 2 × ZMod 2))) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun p _ => congrArg Finset.card (by ext z; simp [Prod.ext_iff])
  have h00 : ((D ∪ U).filter (fun z => z.1 j = 0 ∧ z.2 j = 0)) =
      U.filter (fun z => z.1 j = 0 ∧ z.2 j = 0) := by
    ext z
    simp only [D, Finset.mem_filter, Finset.mem_union]
    tauto
  have hnz : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) →
      ((D ∪ U).filter (fun z => z.1 j = a ∧ z.2 j = b)) =
        (H ∪ U).filter (fun z => z.1 j = a ∧ z.2 j = b) := by
    intro a b hab
    ext z
    simp only [D, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h2, h3⟩
      · exact ⟨Or.inl h1.1, h3⟩
      · exact ⟨Or.inr h2, h3⟩
    · rintro ⟨h1 | h2, h3⟩
      · refine ⟨Or.inl ⟨h1, ?_⟩, h3⟩
        rintro ⟨ha, hb⟩
        rw [h3.1] at ha; rw [h3.2] at hb
        exact hab ⟨ha, hb⟩
      · exact ⟨Or.inr h2, h3⟩
  have hsum4 : (∑ p : ZMod 2 × ZMod 2, ((D ∪ U).filter (fun z => z.1 j = p.1 ∧ z.2 j = p.2)).card) =
      ((D ∪ U).filter (fun z => z.1 j = 0 ∧ z.2 j = 0)).card +
      ((D ∪ U).filter (fun z => z.1 j = 0 ∧ z.2 j = 1)).card +
      ((D ∪ U).filter (fun z => z.1 j = 1 ∧ z.2 j = 0)).card +
      ((D ∪ U).filter (fun z => z.1 j = 1 ∧ z.2 j = 1)).card := by
    have huniv : (Finset.univ : Finset (ZMod 2 × ZMod 2)) = {(0, 0), (0, 1), (1, 0), (1, 1)} := by
      decide
    rw [huniv]
    simp [add_assoc]
  rw [hpart, hsum4, h00,
    hnz 0 1 (by decide), hnz 1 0 (by decide), hnz 1 1 (by decide)]
  have e0 := four_mul_fiber_card j U hUind 0 0
  have e1 := four_mul_fiber_card j (H ∪ U) hHUind 0 1
  have e2 := four_mul_fiber_card j (H ∪ U) hHUind 1 0
  have e3 := four_mul_fiber_card j (H ∪ U) hHUind 1 1
  omega

private lemma hyperplane_inclusion_of_D_sub {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (γ : Fin t → ZMod 2) (j m : Fin t) (hjm : j < m)
    (hsub : ∀ z : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      (γ m + ∑ i ∈ Finset.Ioi m, (z.1 i * A i m + z.2 i * B i m) = 0) →
      ¬ (z.1 m = 0 ∧ z.2 m = 0) →
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = 0) :
    ∀ z : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      (γ m + ∑ i ∈ Finset.Ioi m, (z.1 i * A i m + z.2 i * B i m) = 0) →
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = 0 := by
  intro z hcm
  by_cases hnz : ¬ (z.1 m = 0 ∧ z.2 m = 0)
  · exact hsub z hcm hnz
  · push_neg at hnz
    have hcm_ind : ∀ a b : ZMod 2,
        γ m + ∑ i ∈ Finset.Ioi m, ((setCoord m a b z).1 i * A i m + (setCoord m a b z).2 i * B i m) = 0 := by
      intro a b
      have hsum : (∑ i ∈ Finset.Ioi m, ((setCoord m a b z).1 i * A i m + (setCoord m a b z).2 i * B i m)) =
          ∑ i ∈ Finset.Ioi m, (z.1 i * A i m + z.2 i * B i m) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ m := ne_of_gt (Finset.mem_Ioi.mp hi)
        simp [setCoord, Function.update, hne]
      rw [hsum]; exact hcm
    have hcj_eval : ∀ a b : ZMod 2,
        γ j + ∑ i ∈ Finset.Ioi j, ((setCoord m a b z).1 i * A i j + (setCoord m a b z).2 i * B i j) =
          (γ j + ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j)) + (a * A m j + b * B m j) := by
      intro a b
      have hm_mem : m ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hjm
      rw [← Finset.add_sum_erase _ _ hm_mem]
      have hrest : (∑ i ∈ (Finset.Ioi j).erase m, ((setCoord m a b z).1 i * A i j + (setCoord m a b z).2 i * B i j)) =
          ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ m := (Finset.mem_erase.mp hi).1
        simp [setCoord, Function.update, hne]
      rw [hrest]
      simp only [setCoord, Function.update_self]
      ring
    have h10 := hsub (setCoord m 1 0 z) (hcm_ind 1 0) (by simp [setCoord])
    have h01 := hsub (setCoord m 0 1 z) (hcm_ind 0 1) (by simp [setCoord])
    have h11 := hsub (setCoord m 1 1 z) (hcm_ind 1 1) (by simp [setCoord])
    rw [hcj_eval 1 0] at h10
    rw [hcj_eval 0 1] at h01
    rw [hcj_eval 1 1] at h11
    have hm_mem : m ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hjm
    have hbase : γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) =
        γ j + ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j) := by
      rw [← Finset.add_sum_erase _ _ hm_mem, hnz.1, hnz.2]
      ring
    rw [hbase]
    set S0 := γ j + ∑ i ∈ (Finset.Ioi j).erase m, (z.1 i * A i j + z.2 i * B i j)
    have hsum3 : (S0 + (1 * A m j + 0 * B m j)) + (S0 + (0 * A m j + 1 * B m j)) +
        (S0 + (1 * A m j + 1 * B m j)) = S0 := by
      have h20 : ∀ x : ZMod 2, x + x = 0 := by intro x; fin_cases x <;> decide
      calc
        (S0 + (1 * A m j + 0 * B m j)) + (S0 + (0 * A m j + 1 * B m j)) +
            (S0 + (1 * A m j + 1 * B m j))
            = (S0 + S0) + (A m j + A m j) + (B m j + B m j) + S0 := by ring
        _ = 0 + 0 + 0 + S0 := by rw [h20 S0, h20 (A m j), h20 (B m j)]
        _ = S0 := by ring
    rw [← hsum3, h10, h01, h11]
    simp

end PEqualNP.Outside.L_lib_647_aux

theorem PEqualNP.Outside.L_lib_647 : (∀ t : ℕ,
  let V := Fin t → ZMod 2
  ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
    let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
      ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
    let c := fun (j : Fin t) (z : V × V) =>
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
    let live := (Finset.univ : Finset (V × V)).filter (fun z =>
      ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
    let lhs := 2 * 4^sources.card * live.card
    let rhs := (4^sources.card + 1) * 4^t
    lhs ≤ rhs ∧
      (lhs = rhs ↔
        (∀ j, j ∉ sources → γ j = 1) ∧
        ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z)) := by
  classical
  intro t V A B γ sources c live lhs rhs
  have h11 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x; fin_cases x
    · left; rfl
    · right; rfl
  have hc_nonsrc : ∀ j : Fin t, j ∉ sources → ∀ z : V × V, c j z = γ j := by
    intro j hj z
    dsimp only [c]
    have hzero : ∀ i ∈ Finset.Ioi j, z.1 i * A i j + z.2 i * B i j = 0 := by
      intro i hi
      have hnot : ¬ (A i j ≠ 0 ∨ B i j ≠ 0) := by
        intro hAB
        apply hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨i, Finset.mem_Ioi.mp hi, hAB⟩⟩
      push_neg at hnot
      rw [hnot.1, hnot.2]; ring
    rw [Finset.sum_eq_zero hzero, add_zero]
  by_cases hsink : ∀ j : Fin t, j ∉ sources → γ j = 1
  · let H : Fin t → Finset (V × V) := fun j => Finset.univ.filter (fun z => c j z = 0)
    let D : Fin t → Finset (V × V) := fun j => (H j).filter (fun z => ¬ (z.1 j = 0 ∧ z.2 j = 0))
    let Sk : ℕ → Finset (Fin t) := fun k => sources.filter (fun j => k ≤ j.val)
    let Uk : ℕ → Finset (V × V) := fun k => (Sk k).biUnion D
    have hc_ind_le : ∀ (j j0 : Fin t), j0 ≤ j → ∀ z a b,
        c j (PEqualNP.Outside.L_lib_647_aux.setCoord j0 a b z) = c j z := by
      intro j j0 hle z a b
      dsimp only [c]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i ≠ j0 := ne_of_gt (lt_of_le_of_lt hle (Finset.mem_Ioi.mp hi))
      simp [PEqualNP.Outside.L_lib_647_aux.setCoord, Function.update, hne]
    have hHind : ∀ (j : Fin t) (z : V × V) (a b : ZMod 2),
        PEqualNP.Outside.L_lib_647_aux.setCoord j a b z ∈ H j ↔ z ∈ H j := by
      intro j z a b
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, hc_ind_le j j le_rfl]
    have hUind : ∀ (k : ℕ) (j0 : Fin t), j0.val < k → ∀ z a b,
        PEqualNP.Outside.L_lib_647_aux.setCoord j0 a b z ∈ Uk k ↔ z ∈ Uk k := by
      intro k j0 hlt z a b
      simp only [Uk, Finset.mem_biUnion]
      refine exists_congr fun j => and_congr_right fun hj => ?_
      have hk : k ≤ j.val := (Finset.mem_filter.mp hj).2
      have hj0lt : j0 < j := Fin.mk_lt_mk.mpr (by omega)
      have hjne : j ≠ j0 := ne_of_gt hj0lt
      simp only [D, H, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hc_ind_le j j0 (le_of_lt hj0lt)]
      simp only [PEqualNP.Outside.L_lib_647_aux.setCoord, Function.update, hjne, ↓reduceDIte]
    have hmain : ∀ r : ℕ, r ≤ t →
        let k := t - r
        (4 ^ (Sk k).card - 1) * 4 ^ t ≤ 2 * 4 ^ (Sk k).card * (Uk k).card ∧
        ((4 ^ (Sk k).card - 1) * 4 ^ t = 2 * 4 ^ (Sk k).card * (Uk k).card ↔
          ∀ j ∈ Sk k, Uk (j.val + 1) ⊆ H j) := by
      intro r
      induction r with
      | zero =>
        intro _
        dsimp only
        have hSk0 : Sk t = ∅ := by
          ext j; simp only [Sk, Finset.mem_filter, Finset.notMem_empty, iff_false]
          intro h; have := j.isLt; omega
        simp only [Nat.sub_zero, hSk0, Uk, Finset.biUnion_empty, Finset.card_empty]
        simp
      | succ r ih =>
        intro hr
        have hih := ih (by omega)
        dsimp only at hih ⊢
        set k := t - (r + 1)
        have hks : k + 1 = t - r := by omega
        have hklt : k < t := by omega
        let j0 : Fin t := ⟨k, hklt⟩
        by_cases hj0 : j0 ∈ sources
        · have hSk_eq : Sk k = insert j0 (Sk (k + 1)) := by
            ext j
            simp only [Sk, Finset.mem_insert, Finset.mem_filter]
            constructor
            · rintro ⟨hjs, hkj⟩
              by_cases hEq : j.val = k
              · left; exact Fin.ext hEq
              · right; exact ⟨hjs, by omega⟩
            · rintro (rfl | ⟨hjs, hkj⟩)
              · exact ⟨hj0, le_rfl⟩
              · exact ⟨hjs, by omega⟩
          have hj0_not : j0 ∉ Sk (k + 1) := by
            simp only [Sk, Finset.mem_filter, j0]
            omega
          have hcard_S : (Sk k).card = (Sk (k + 1)).card + 1 := by
            rw [hSk_eq, Finset.card_insert_of_notMem hj0_not]
          have hUk_eq : Uk k = D j0 ∪ Uk (k + 1) := by
            dsimp only [Uk]
            rw [hSk_eq, Finset.biUnion_insert]
          have h4 := PEqualNP.Outside.L_lib_647_aux.four_mul_union_update j0 (H j0) (Uk (k + 1))
            (hHind j0) (hUind (k + 1) j0 (by dsimp [j0]; omega))
          have h4' : 4 * (Uk k).card = (Uk (k + 1)).card + 3 * (H j0 ∪ Uk (k + 1)).card := by
            rw [hUk_eq]; exact h4
          have hHcard : 2 * (H j0).card = 4 ^ t :=
            PEqualNP.Outside.L_lib_647_aux.card_hyperplane_two_mul A B γ j0
              (Finset.mem_filter.mp hj0).2
          have hHle : (H j0).card ≤ (H j0 ∪ Uk (k + 1)).card :=
            Finset.card_le_card Finset.subset_union_left
          rw [← hks] at hih
          set s := (Sk (k + 1)).card
          have hs_pos : 1 ≤ 4 ^ s := Nat.one_le_pow _ _ (by decide)
          have hs1_pos : 1 ≤ 4 ^ (s + 1) := Nat.one_le_pow _ _ (by decide)
          have hpow : 4 ^ (s + 1) = 4 * 4 ^ s := by ring
          have h8 : 2 * (Uk (k + 1)).card + 3 * 4 ^ t ≤ 8 * (Uk k).card := by
            omega
          have hineq : (4 ^ (Sk k).card - 1) * 4 ^ t ≤ 2 * 4 ^ (Sk k).card * (Uk k).card := by
            rw [hcard_S]
            have hstep1 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) ≤ 4 ^ s * (8 * (Uk k).card) :=
              Nat.mul_le_mul_left _ h8
            have hstep2 : (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t = (4 ^ (s + 1) - 1) * 4 ^ t := by
              zify [hs_pos, hs1_pos]
              ring
            have hstep3 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) =
                2 * 4 ^ s * (Uk (k + 1)).card + 3 * 4 ^ s * 4 ^ t := by ring
            have hstep4 : 4 ^ s * (8 * (Uk k).card) = 2 * 4 ^ (s + 1) * (Uk k).card := by
              rw [hpow]; ring
            have hih1 := hih.1
            omega
          refine ⟨hineq, ?_⟩
          constructor
          · intro hEq j hj
            rw [hcard_S] at hEq
            have hstep1 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) ≤ 4 ^ s * (8 * (Uk k).card) :=
              Nat.mul_le_mul_left _ h8
            have hstep2 : (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t = (4 ^ (s + 1) - 1) * 4 ^ t := by
              zify [hs_pos, hs1_pos]; ring
            have hstep3 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) =
                2 * 4 ^ s * (Uk (k + 1)).card + 3 * 4 ^ s * 4 ^ t := by ring
            have hstep4 : 4 ^ s * (8 * (Uk k).card) = 2 * 4 ^ (s + 1) * (Uk k).card := by
              rw [hpow]; ring
            have hih1 := hih.1
            have h4s_pos : 0 < 4 ^ s := Nat.pow_pos (by decide)
            have hEq_prev : (4 ^ s - 1) * 4 ^ t = 2 * 4 ^ s * (Uk (k + 1)).card := by omega
            have hEq_8 : 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) = 4 ^ s * (8 * (Uk k).card) := by
              omega
            have h8eq : 2 * (Uk (k + 1)).card + 3 * 4 ^ t = 8 * (Uk k).card :=
              Nat.eq_of_mul_eq_mul_left h4s_pos hEq_8
            have hHeq : (H j0).card = (H j0 ∪ Uk (k + 1)).card := by omega
            have hHunion : H j0 = H j0 ∪ Uk (k + 1) :=
              Finset.eq_of_subset_of_card_le Finset.subset_union_left (le_of_eq hHeq.symm)
            have hUsubH : Uk (k + 1) ⊆ H j0 := by
              intro z hz
              rw [hHunion]
              exact Finset.mem_union_right _ hz
            rw [hSk_eq] at hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact hUsubH
            · exact hih.2.mp hEq_prev j hj'
          · intro hall
            have hUsubH : Uk (k + 1) ⊆ H j0 := hall j0 (by rw [hSk_eq]; exact Finset.mem_insert_self _ _)
            have hprev_eq : (4 ^ s - 1) * 4 ^ t = 2 * 4 ^ s * (Uk (k + 1)).card :=
              hih.2.mpr fun j hj => hall j (by rw [hSk_eq]; exact Finset.mem_insert_of_mem hj)
            have hHunion : H j0 ∪ Uk (k + 1) = H j0 := Finset.union_eq_left.mpr hUsubH
            rw [hHunion] at h4'
            rw [hcard_S]
            have hstep2 : (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t = (4 ^ (s + 1) - 1) * 4 ^ t := by
              zify [hs_pos, hs1_pos]; ring
            have h8eq : 8 * (Uk k).card = 2 * (Uk (k + 1)).card + 3 * 4 ^ t := by omega
            calc
              (4 ^ (s + 1) - 1) * 4 ^ t = (4 ^ s - 1) * 4 ^ t + 3 * 4 ^ s * 4 ^ t := hstep2.symm
              _ = 2 * 4 ^ s * (Uk (k + 1)).card + 3 * 4 ^ s * 4 ^ t := by rw [hprev_eq]
              _ = 4 ^ s * (2 * (Uk (k + 1)).card + 3 * 4 ^ t) := by ring
              _ = 4 ^ s * (8 * (Uk k).card) := by rw [h8eq]
              _ = 2 * 4 ^ (s + 1) * (Uk k).card := by rw [hpow]; ring
        · have hSk_eq : Sk k = Sk (k + 1) := by
            ext j
            simp only [Sk, Finset.mem_filter]
            constructor
            · rintro ⟨hjs, hkj⟩
              refine ⟨hjs, ?_⟩
              by_contra hlt
              have hEq : j = j0 := Fin.ext (by dsimp [j0]; omega)
              rw [hEq] at hjs
              exact hj0 hjs
            · rintro ⟨hjs, hkj⟩
              exact ⟨hjs, by omega⟩
          have hUk_eq : Uk k = Uk (k + 1) := by dsimp only [Uk]; rw [hSk_eq]
          rw [← hks] at hih
          rw [hSk_eq, hUk_eq]
          exact hih
    have h0 := hmain t le_rfl
    dsimp only at h0
    rw [Nat.sub_self] at h0
    have hSk0 : Sk 0 = sources := by
      ext j; simp [Sk]
    have hlive_comp : live.card + (Uk 0).card = 4 ^ t := by
      have hdisj : Disjoint live (Uk 0) := by
        rw [Finset.disjoint_left]
        intro z hzl hzu
        have hl := (Finset.mem_filter.mp hzl).2
        rcases Finset.mem_biUnion.mp hzu with ⟨j, _, hjD⟩
        have hD := Finset.mem_filter.mp hjD
        have hc0 := (Finset.mem_filter.mp hD.1).2
        rcases hl j with hne | h00
        · exact hne hc0
        · exact hD.2 h00
      have hunion : live ∪ Uk 0 = Finset.univ := by
        ext z
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases hl : z ∈ live
        · exact Or.inl hl
        · right
          simp only [live, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          push_neg at hl
          rcases hl with ⟨j, hcj, hnz⟩
          have hjs : j ∈ sources := by
            by_contra hnot
            have h1 := hsink j hnot
            rw [hc_nonsrc j hnot z, h1] at hcj
            exact absurd hcj (by decide)
          refine Finset.mem_biUnion.mpr ⟨j, by rw [hSk0]; exact hjs, ?_⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hcj⟩, ?_⟩
          rintro ⟨h1, h2⟩
          exact hnz h1 h2
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        PEqualNP.Outside.L_lib_647_aux.card_VV]
    rw [hSk0] at h0
    set s := sources.card
    have hs_pos : 1 ≤ 4 ^ s := Nat.one_le_pow _ _ (by decide)
    have hconv : (4 ^ s - 1) * 4 ^ t + (4 ^ s + 1) * 4 ^ t = 2 * 4 ^ s * 4 ^ t := by
      zify [hs_pos]; ring
    have hlive_eq : 2 * 4 ^ s * live.card + 2 * 4 ^ s * (Uk 0).card = 2 * 4 ^ s * 4 ^ t := by
      rw [← mul_add, hlive_comp]
    refine ⟨?_, ?_⟩
    · change 2 * 4 ^ s * live.card ≤ (4 ^ s + 1) * 4 ^ t
      have h01 := h0.1
      omega
    · change 2 * 4 ^ s * live.card = (4 ^ s + 1) * 4 ^ t ↔ _
      have hiff_eq : 2 * 4 ^ s * live.card = (4 ^ s + 1) * 4 ^ t ↔
          (4 ^ s - 1) * 4 ^ t = 2 * 4 ^ s * (Uk 0).card := by omega
      rw [hiff_eq, h0.2]
      constructor
      · intro hall
        refine ⟨hsink, ?_⟩
        have hlt_eq : ∀ j ∈ sources, ∀ k ∈ sources, j < k → ∀ z, c j z = c k z := by
          intro j hj k hk hjk
          have hsub : H k ⊆ H j := by
            intro z hz
            have hck : c k z = 0 := (Finset.mem_filter.mp hz).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
            apply PEqualNP.Outside.L_lib_647_aux.hyperplane_inclusion_of_D_sub A B γ j k hjk
            · intro w hcw hnz
              have hwU : w ∈ Uk (j.val + 1) := by
                refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, by omega⟩, ?_⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ w, hcw⟩, hnz⟩
              exact (Finset.mem_filter.mp (hall j hj hwU)).2
            · exact hck
          have hck_card : 2 * (H k).card = 4 ^ t :=
            PEqualNP.Outside.L_lib_647_aux.card_hyperplane_two_mul A B γ k (Finset.mem_filter.mp hk).2
          have hcj_card : 2 * (H j).card = 4 ^ t :=
            PEqualNP.Outside.L_lib_647_aux.card_hyperplane_two_mul A B γ j (Finset.mem_filter.mp hj).2
          have hHeq : H k = H j := Finset.eq_of_subset_of_card_le hsub (by omega)
          intro z
          have hiff0 : c k z = 0 ↔ c j z = 0 := by
            have := Finset.ext_iff.mp hHeq z
            simpa [H] using this
          rcases h11 (c j z) with hj0 | hj1 <;> rcases h11 (c k z) with hk0 | hk1
          · rw [hj0, hk0]
          · exfalso; have := hiff0.mpr hj0; rw [hk1] at this; exact absurd this (by decide)
          · exfalso; have := hiff0.mp hk0; rw [hj1] at this; exact absurd this (by decide)
          · rw [hj1, hk1]
        intro j hj k hk z
        rcases lt_trichotomy j k with hlt | rfl | hgt
        · exact hlt_eq j hj k hk hlt z
        · rfl
        · exact (hlt_eq k hk j hj hgt z).symm
      · rintro ⟨_, hceq⟩ j hj z hz
        rcases Finset.mem_biUnion.mp hz with ⟨k, hk, hkD⟩
        have hks : k ∈ sources := (Finset.mem_filter.mp hk).1
        have hck0 : c k z = 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hkD).1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
        rw [hceq j hj k hks z, hck0]
  · push_neg at hsink
    rcases hsink with ⟨j0, hj0_not, hγne⟩
    have hγ0 : γ j0 = 0 := by
      rcases h11 (γ j0) with h0 | h1
      · exact h0
      · exact absurd h1 hγne
    have hlive_sub : live ⊆ Finset.univ.filter (fun z : V × V => z.1 j0 = 0 ∧ z.2 j0 = 0) := by
      intro z hz
      have hl := (Finset.mem_filter.mp hz).2 j0
      rw [hc_nonsrc j0 hj0_not z, hγ0] at hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
      rcases hl with hne | h00
      · exact absurd rfl hne
      · exact h00
    have h4live : 4 * live.card ≤ 4 ^ t := by
      have hcard_le : live.card ≤
          (Finset.univ.filter (fun z : (Fin t → ZMod 2) × (Fin t → ZMod 2) => z.1 j0 = 0 ∧ z.2 j0 = 0)).card :=
        Finset.card_le_card hlive_sub
      have hfib := PEqualNP.Outside.L_lib_647_aux.four_mul_fiber_card j0
        (Finset.univ : Finset ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
        (fun _ _ _ => by simp) 0 0
      rw [Finset.card_univ, PEqualNP.Outside.L_lib_647_aux.card_VV] at hfib
      omega
    have hstrict : lhs < rhs := by
      dsimp only [lhs, rhs]
      have hpow_pos : 0 < 4 ^ t := Nat.pow_pos (by decide)
      have h4s_pos : 0 < 4 ^ sources.card := Nat.pow_pos (by decide)
      have hmul : 2 * (2 * 4 ^ sources.card * live.card) = 4 ^ sources.card * (4 * live.card) := by ring
      have hle1 : 4 ^ sources.card * (4 * live.card) ≤ 4 ^ sources.card * 4 ^ t :=
        Nat.mul_le_mul_left _ h4live
      have hlt2 : 4 ^ sources.card * 4 ^ t < 2 * ((4 ^ sources.card + 1) * 4 ^ t) := by
        have h1 : 4 ^ sources.card * 4 ^ t < (2 * 4 ^ sources.card + 2) * 4 ^ t := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) hpow_pos
        linarith
      omega
    refine ⟨le_of_lt hstrict, ?_⟩
    constructor
    · intro hEq; omega
    · rintro ⟨hall, _⟩
      exact absurd (hall j0 hj0_not) hγne
