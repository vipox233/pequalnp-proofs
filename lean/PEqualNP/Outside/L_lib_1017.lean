import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1017_aux

open scoped BigOperators

private lemma foldl_zero_eq_replicate (k : ℕ) :
    (List.range k).foldl (fun h (_ : ℕ) => (0 : ℂ) :: h) ([] : List ℂ) = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.replicate_succ]

private lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  calc ∑ x ∈ s, ((if p x then 1 else 0) + (if ¬ p x then 1 else 0))
      = ∑ _x ∈ s, 1 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : p x <;> simp [hx]
    _ = s.card := by simp

private lemma foldl_eq_replicate_of_zero {Q : Type} (obs : Q → ℂ) (ask : ℕ → List ℂ → Q) :
    ∀ k : ℕ, (∀ j < k, obs (ask j (List.replicate j 0)) = 0) →
      (List.range k).foldl (fun h j => obs (ask j h) :: h) ([] : List ℂ) =
        List.replicate k 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    rfl
  | succ k ih =>
    intro hzero
    rw [List.range_succ, List.foldl_append]
    have hprev := ih (fun j hj => hzero j (Nat.lt_succ_of_lt hj))
    rw [hprev]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hzero k (Nat.lt_succ_self k), List.replicate_succ]

private lemma mem_foldl_nonadap {Q : Type} (obs : Q → ℂ) (f : ℕ → Q) :
    ∀ k : ℕ, ∀ z : ℂ,
      z ∈ (List.range k).foldl (fun h j => obs (f j) :: h) ([] : List ℂ) ↔
        ∃ j < k, obs (f j) = z := by
  intro k
  induction k with
  | zero =>
    intro z
    simp
  | succ k ih =>
    intro z
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨k, Nat.lt_succ_self k, rfl⟩
      · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hjk : j = k
      · left
        rw [hjk]
      · right
        exact ⟨j, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hjk, rfl⟩

private lemma main_iff (G Q : Type) [Group G] [Fintype G] [DecidableEq G] [Nonempty Q]
    (F : Q → G → ℂ)
    (horb : ∀ (g : G) (s : Q), ∃ v : Q, ∀ x : G, F v x ≠ 0 ↔ F s (x * g) ≠ 0)
    (t a d : ℕ) (hd : 0 < d) (had : a ≤ d) :
    ((∃ (R : ℕ) (ask : Fin R → ℕ → List ℂ → Q) (accept : Fin R → List ℂ → Bool),
      0 < R ∧
      let run := fun (obs : Q → ℂ) (u : Fin R) =>
        (List.range t).foldl (fun h j => obs (ask u j h) :: h) ([] : List ℂ)
      let yes := fun obs : Q → ℂ =>
        ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run obs u))).card
      d * yes (fun _ => 0) ≤ a * R ∧ (∀ x : G, d * (R - yes (fun s => F s x)) ≤ a * R)) ↔
    ∃ L : Fin t → Q,
      let missed := ((Finset.univ : Finset G).filter (fun x => ∀ i : Fin t, F (L i) x = 0)).card
      (d - a) * missed ≤ a * Fintype.card G) := by
  classical
  constructor
  · rintro ⟨R, ask, accept, hR, h0, hG⟩
    by_cases hda : d = a
    · subst hda
      exact ⟨fun _ => Classical.arbitrary Q, by simp⟩
    · have had_lt : a < d := Nat.lt_of_le_of_ne had (Ne.symm hda)
      let run : (Q → ℂ) → Fin R → List ℂ := fun obs u =>
        (List.range t).foldl (fun h j => obs (ask u j h) :: h) ([] : List ℂ)
      let yes : (Q → ℂ) → ℕ := fun obs =>
        ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run obs u))).card
      let B : Finset (Fin R) :=
        (Finset.univ : Finset (Fin R)).filter (fun u => accept u (run (fun _ => 0) u) = false)
      have hB_card : B.card = R - yes (fun _ => 0) := by
        have hcomp := card_filter_add_not (Finset.univ : Finset (Fin R))
          (fun u => accept u (run (fun _ => 0) u) = true)
        have hB_eq : B = (Finset.univ : Finset (Fin R)).filter
            (fun u => ¬ accept u (run (fun _ => 0) u) = true) := by
          ext u
          simp [B]
        rw [Finset.card_univ, Fintype.card_fin] at hcomp
        change yes (fun _ => 0) + ((Finset.univ : Finset (Fin R)).filter
          (fun u => ¬ accept u (run (fun _ => 0) u) = true)).card = R at hcomp
        rw [← hB_eq] at hcomp
        omega
      have hB_pos : 0 < B.card := by
        have h1 : d * yes (fun _ => 0) < d * R :=
          lt_of_le_of_lt h0 (Nat.mul_lt_mul_of_pos_right had_lt hR)
        have h2 : yes (fun _ => 0) < R := Nat.lt_of_mul_lt_mul_left h1
        omega
      have hB_ne : B.Nonempty := Finset.card_pos.mp hB_pos
      let Lu : Fin R → Fin t → Q := fun u i => ask u i.val (List.replicate i.val 0)
      let missed : Fin R → ℕ := fun u =>
        ((Finset.univ : Finset G).filter (fun x => ∀ i : Fin t, F (Lu u i) x = 0)).card
      obtain ⟨u0, hu0B, hu0_min⟩ := Finset.exists_min_image B missed hB_ne
      refine ⟨Lu u0, ?_⟩
      have hsum_le : B.card * missed u0 ≤ ∑ u ∈ B, missed u := by
        calc B.card * missed u0
            = ∑ _u ∈ B, missed u0 := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ u ∈ B, missed u := Finset.sum_le_sum (fun u hu => hu0_min u hu)
      have hswap : (∑ u ∈ B, missed u) =
          ∑ x : G, (B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0)).card := by
        simp only [missed, Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      have hper_x : ∀ x : G,
          (B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0)).card ≤ R - yes (fun s => F s x) := by
        intro x
        have hsub : B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0) ⊆
            (Finset.univ : Finset (Fin R)).filter
              (fun u => ¬ accept u (run (fun s => F s x) u) = true) := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hu ⊢
          rcases hu with ⟨hu0, hzero⟩
          have hrun_eq : run (fun s => F s x) u = run (fun _ => 0) u := by
            have h1 : run (fun s => F s x) u = List.replicate t 0 :=
              foldl_eq_replicate_of_zero (fun s => F s x) (ask u) t
                (fun j hj => hzero ⟨j, hj⟩)
            have h2 : run (fun _ => 0) u = List.replicate t 0 :=
              foldl_zero_eq_replicate t
            rw [h1, h2]
          rw [hrun_eq, hu0]
          decide
        have hle := Finset.card_le_card hsub
        have hcomp := card_filter_add_not (Finset.univ : Finset (Fin R))
          (fun u => accept u (run (fun s => F s x) u) = true)
        rw [Finset.card_univ, Fintype.card_fin] at hcomp
        change yes (fun s => F s x) + _ = R at hcomp
        omega
      have htotal : d * (∑ u ∈ B, missed u) ≤ a * R * Fintype.card G := by
        rw [hswap, Finset.mul_sum]
        calc ∑ x : G, d * (B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0)).card
            ≤ ∑ x : G, d * (R - yes (fun s => F s x)) :=
              Finset.sum_le_sum (fun x _ => Nat.mul_le_mul_left d (hper_x x))
          _ ≤ ∑ _x : G, a * R := Finset.sum_le_sum (fun x _ => hG x)
          _ = Fintype.card G * (a * R) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          _ = a * R * Fintype.card G := by ring
      have hdB : (d - a) * R ≤ d * B.card := by
        rw [hB_card, Nat.mul_sub_left_distrib, Nat.sub_mul]
        exact Nat.sub_le_sub_left h0 (d * R)
      have hcomb : R * ((d - a) * missed u0) ≤ R * (a * Fintype.card G) := by
        calc R * ((d - a) * missed u0)
            = ((d - a) * R) * missed u0 := by ring
          _ ≤ (d * B.card) * missed u0 := Nat.mul_le_mul_right _ hdB
          _ = d * (B.card * missed u0) := by ring
          _ ≤ d * (∑ u ∈ B, missed u) := Nat.mul_le_mul_left d hsum_le
          _ ≤ a * R * Fintype.card G := htotal
          _ = R * (a * Fintype.card G) := by ring
      exact Nat.le_of_mul_le_mul_left hcomb hR
  · rintro ⟨L, hL⟩
    have hshift : ∀ (g : G) (i : Fin t), ∃ v : Q, ∀ x : G, F v x ≠ 0 ↔ F (L i) (x * g) ≠ 0 :=
      fun g i => horb g (L i)
    choose Lg hLg using hshift
    let R := d * Fintype.card G
    have hR : 0 < R := Nat.mul_pos hd Fintype.card_pos
    let eG : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
    let eR : Fin R ≃ Fin d × G :=
      (finProdFinEquiv.symm).trans (Equiv.prodCongr (Equiv.refl (Fin d)) eG.symm)
    let ask : Fin R → ℕ → List ℂ → Q := fun u j _ =>
      if hj : j < t then Lg (eR u).2 ⟨j, hj⟩ else Classical.arbitrary Q
    let accept : Fin R → List ℂ → Bool := fun u h =>
      if (eR u).1.val < a then true
      else @decide (∃ z ∈ h, z ≠ 0) (Classical.propDecidable _)
    refine ⟨R, ask, accept, hR, ?_, ?_⟩
    · have hyes0 : ((Finset.univ : Finset (Fin R)).filter (fun u =>
          accept u ((List.range t).foldl (fun h j => (0 : ℂ) :: h) ([] : List ℂ)))).card =
          a * Fintype.card G := by
        have hpred : ∀ u : Fin R,
            (accept u ((List.range t).foldl (fun h j => (0 : ℂ) :: h) ([] : List ℂ)) = true) ↔
              (eR u).1.val < a := by
          intro u
          rw [foldl_zero_eq_replicate t]
          simp only [accept]
          by_cases hca : (eR u).1.val < a
          · simp [hca]
          · simp only [hca, ↓reduceIte, decide_eq_true_eq, iff_false, not_exists, not_and,
              not_not]
            intro z hz
            exact List.eq_of_mem_replicate hz
        have hcard_eq : ((Finset.univ : Finset (Fin R)).filter (fun u =>
            accept u ((List.range t).foldl (fun h j => (0 : ℂ) :: h) ([] : List ℂ)))).card =
            ((Finset.univ : Finset (Fin d × G)).filter (fun p => p.1.val < a)).card := by
          refine Finset.card_bij (fun u _ => eR u) ?_ ?_ ?_
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            exact (hpred u).mp hu
          · intro u1 _ u2 _ h
            exact eR.injective h
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
            refine ⟨eR.symm p, ?_, eR.apply_symm_apply p⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hpred, eR.apply_symm_apply]
            exact hp
        rw [hcard_eq]
        have hprod : (Finset.univ : Finset (Fin d × G)).filter (fun p => p.1.val < a) =
            ((Finset.univ : Finset (Fin d)).filter (fun c => c.val < a)) ×ˢ
              (Finset.univ : Finset G) := by
          ext ⟨c, g⟩
          simp
        rw [hprod, Finset.card_product, Finset.card_univ]
        have hca_card : ((Finset.univ : Finset (Fin d)).filter (fun c => c.val < a)).card = a := by
          calc ((Finset.univ : Finset (Fin d)).filter (fun c => c.val < a)).card
              = (Finset.range a).card := by
                refine Finset.card_bij (fun (c : Fin d) _ => c.val) ?_ ?_ ?_
                · intro c hc
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
                  exact Finset.mem_range.mpr hc
                · intro c1 _ c2 _ h
                  exact Fin.ext h
                · intro k hk
                  rw [Finset.mem_range] at hk
                  refine ⟨⟨k, lt_of_lt_of_le hk had⟩, ?_, rfl⟩
                  simp [hk]
            _ = a := Finset.card_range a
        rw [hca_card]
      dsimp only
      rw [hyes0]
      change d * (a * Fintype.card G) ≤ a * (d * Fintype.card G)
      rw [Nat.mul_left_comm]
    · intro x
      let run_x : Fin R → List ℂ := fun u =>
        (List.range t).foldl (fun h j => F (ask u j h) x :: h) ([] : List ℂ)
      let yes_x : ℕ := ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run_x u))).card
      have hcomp := card_filter_add_not (Finset.univ : Finset (Fin R))
        (fun u => accept u (run_x u) = true)
      rw [Finset.card_univ, Fintype.card_fin] at hcomp
      change yes_x + ((Finset.univ : Finset (Fin R)).filter
        (fun u => ¬ accept u (run_x u) = true)).card = R at hcomp
      have hsub_eq : R - yes_x =
          ((Finset.univ : Finset (Fin R)).filter (fun u => ¬ accept u (run_x u) = true)).card := by
        omega
      rw [hsub_eq]
      have hpred : ∀ u : Fin R,
          (¬ accept u (run_x u) = true) ↔
            (a ≤ (eR u).1.val ∧ ∀ i : Fin t, F (L i) (x * (eR u).2) = 0) := by
        intro u
        have hmem : ∀ z : ℂ, z ∈ run_x u ↔
            ∃ j < t, F (if hj : j < t then Lg (eR u).2 ⟨j, hj⟩ else Classical.arbitrary Q) x = z :=
          mem_foldl_nonadap (fun s => F s x)
            (fun j => if hj : j < t then Lg (eR u).2 ⟨j, hj⟩ else Classical.arbitrary Q) t
        simp only [accept]
        by_cases hca : (eR u).1.val < a
        · simp only [hca, ↓reduceIte, not_true_eq_false, false_iff, not_and]
          intro hle
          omega
        · simp only [hca, ↓reduceIte, decide_eq_true_eq, not_exists, not_and, not_not]
          have hle : a ≤ (eR u).1.val := Nat.le_of_not_lt hca
          simp only [hle, true_and]
          constructor
          · intro hall i
            have hz := hall (F (Lg (eR u).2 i) x) ((hmem _).mpr ⟨i.val, i.isLt, by simp [i.isLt]⟩)
            by_contra hne
            exact ((hLg (eR u).2 i x).mpr hne) hz
          · intro hall z hz
            rcases (hmem z).mp hz with ⟨j, hj, rfl⟩
            simp only [hj, ↓reduceDIte]
            by_contra hne
            exact ((hLg (eR u).2 ⟨j, hj⟩ x).mp hne) (hall ⟨j, hj⟩)
      let missed := ((Finset.univ : Finset G).filter (fun y => ∀ i : Fin t, F (L i) y = 0)).card
      have hcard_eq : ((Finset.univ : Finset (Fin R)).filter
          (fun u => ¬ accept u (run_x u) = true)).card = (d - a) * missed := by
        have h1 : ((Finset.univ : Finset (Fin R)).filter
            (fun u => ¬ accept u (run_x u) = true)).card =
            (((Finset.univ : Finset (Fin d)).filter (fun c => a ≤ c.val)) ×ˢ
              ((Finset.univ : Finset G).filter (fun y => ∀ i : Fin t, F (L i) y = 0))).card := by
          refine Finset.card_bij (fun u _ => ((eR u).1, x * (eR u).2)) ?_ ?_ ?_
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
            rcases (hpred u).mp hu with ⟨hle, hall⟩
            simp [hle, hall]
          · intro u1 _ u2 _ h
            simp only [Prod.mk.injEq] at h
            apply eR.injective
            apply Prod.ext h.1
            exact mul_left_cancel h.2
          · rintro ⟨c, y⟩ hcy
            simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hcy
            refine ⟨eR.symm (c, x⁻¹ * y), ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [hpred, eR.apply_symm_apply]
              simpa [mul_inv_cancel_left] using hcy
            · rw [eR.apply_symm_apply]
              simp [mul_inv_cancel_left]
        rw [h1, Finset.card_product]
        have hda_card : ((Finset.univ : Finset (Fin d)).filter (fun c => a ≤ c.val)).card = d - a := by
          have hcomp2 := card_filter_add_not (Finset.univ : Finset (Fin d))
            (fun c => c.val < a)
          rw [Finset.card_univ, Fintype.card_fin] at hcomp2
          have hlt_card : ((Finset.univ : Finset (Fin d)).filter (fun c => c.val < a)).card = a := by
            calc ((Finset.univ : Finset (Fin d)).filter (fun c => c.val < a)).card
                = (Finset.range a).card := by
                  refine Finset.card_bij (fun (c : Fin d) _ => c.val) ?_ ?_ ?_
                  · intro c hc
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
                    exact Finset.mem_range.mpr hc
                  · intro c1 _ c2 _ h
                    exact Fin.ext h
                  · intro k hk
                    rw [Finset.mem_range] at hk
                    refine ⟨⟨k, lt_of_lt_of_le hk had⟩, ?_, rfl⟩
                    simp [hk]
              _ = a := Finset.card_range a
          have hge_eq : (Finset.univ : Finset (Fin d)).filter (fun c => a ≤ c.val) =
              (Finset.univ : Finset (Fin d)).filter (fun c => ¬ c.val < a) := by
            ext c
            simp
          rw [hge_eq]
          omega
        rw [hda_card]
      rw [hcard_eq]
      calc d * ((d - a) * missed)
          ≤ d * (a * Fintype.card G) := Nat.mul_le_mul_left d hL
        _ = a * (d * Fintype.card G) := by ring

end PEqualNP.Outside.L_lib_1017_aux

theorem PEqualNP.Outside.L_lib_1017 :
  ∀ (G Q : Type) [Group G] [Fintype G] [DecidableEq G] [Nonempty Q]
  (F : Q → G → ℂ),
  (∀ (g : G) (s : Q), ∃ v : Q, ∀ x : G, F v x ≠ 0 ↔ F s (x*g) ≠ 0) →
  ∀ (t a d : ℕ), 0 < d → a ≤ d →
  ((∃ (R : ℕ) (ask : Fin R → ℕ → List ℂ → Q) (accept : Fin R → List ℂ → Bool),
    0 < R ∧
    let run := fun (obs : Q → ℂ) (u : Fin R) =>
      (List.range t).foldl (fun h j => obs (ask u j h) :: h) ([] : List ℂ)
    let yes := fun obs : Q → ℂ =>
      ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run obs u))).card
    d * yes (fun _ => 0) ≤ a*R ∧ (∀ x : G, d*(R - yes (fun s => F s x)) ≤ a*R)) ↔
  ∃ L : Fin t → Q,
    let missed := ((Finset.univ : Finset G).filter (fun x => ∀ i : Fin t, F (L i) x = 0)).card
    (d-a)*missed ≤ a*Fintype.card G) := by
  intro G Q _ _ _ _ F horb t a d hd had
  exact PEqualNP.Outside.L_lib_1017_aux.main_iff G Q F horb t a d hd had
