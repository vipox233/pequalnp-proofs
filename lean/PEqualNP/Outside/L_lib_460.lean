import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_460

private lemma log_fiber_sum_le {α β : Type*} [DecidableEq β]
    (E : Finset α) (S : Finset β) (f : α → β)
    (hf : ∀ x ∈ E, f x ∈ S) :
    ∑ x ∈ E, Real.log ((E.card : ℝ) / ((E.filter (fun y => f y = f x)).card : ℝ)) ≤
      (E.card : ℝ) * Real.log (S.card : ℝ) := by
  by_cases hE : E = ∅
  · subst hE
    simp
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    have hE_pos : (0 : ℝ) < (E.card : ℝ) := Nat.cast_pos.mpr hE_ne.card_pos
    obtain ⟨x₀, hx₀⟩ := hE_ne
    have hS_pos : (0 : ℝ) < (S.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨f x₀, hf x₀ hx₀⟩)
    have hfib :
        ∑ x ∈ E, Real.log ((E.card : ℝ) / ((E.filter (fun y => f y = f x)).card : ℝ)) =
          ∑ b ∈ S, ((E.filter (fun y => f y = b)).card : ℝ) *
            Real.log ((E.card : ℝ) / ((E.filter (fun y => f y = b)).card : ℝ)) := by
      rw [← Finset.sum_fiberwise_of_maps_to hf]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hcongr : ∀ x ∈ E.filter (fun y => f y = b),
          Real.log ((E.card : ℝ) / ((E.filter (fun y => f y = f x)).card : ℝ)) =
            Real.log ((E.card : ℝ) / ((E.filter (fun y => f y = b)).card : ℝ)) := by
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
    have hcard : ∑ b ∈ S, ((E.filter (fun y => f y = b)).card : ℝ) = (E.card : ℝ) := by
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise hf).symm
    have hpt : ∀ b ∈ S,
        ((E.filter (fun y => f y = b)).card : ℝ) *
            Real.log ((E.card : ℝ) / ((E.filter (fun y => f y = b)).card : ℝ)) -
          ((E.filter (fun y => f y = b)).card : ℝ) * Real.log (S.card : ℝ) ≤
        (E.card : ℝ) / (S.card : ℝ) - ((E.filter (fun y => f y = b)).card : ℝ) := by
      intro b _
      set w := (E.filter (fun y => f y = b)).card
      by_cases hw : w = 0
      · simp only [hw, Nat.cast_zero, zero_mul, sub_zero]
        exact div_nonneg hE_pos.le hS_pos.le
      · have hw_pos : (0 : ℝ) < (w : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hw)
        have hlog :
            Real.log ((E.card : ℝ) / (w : ℝ)) - Real.log (S.card : ℝ) =
              Real.log ((E.card : ℝ) / ((w : ℝ) * (S.card : ℝ))) := by
          rw [← Real.log_div (div_ne_zero hE_pos.ne' hw_pos.ne') hS_pos.ne', div_div]
        have hle := Real.log_le_sub_one_of_pos (div_pos hE_pos (mul_pos hw_pos hS_pos))
        have hmul := mul_le_mul_of_nonneg_left hle hw_pos.le
        rw [← mul_sub, hlog]
        calc
          (w : ℝ) * Real.log ((E.card : ℝ) / ((w : ℝ) * (S.card : ℝ)))
              ≤ (w : ℝ) * ((E.card : ℝ) / ((w : ℝ) * (S.card : ℝ)) - 1) := hmul
          _ = (E.card : ℝ) / (S.card : ℝ) - (w : ℝ) := by
              rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_mul_left _ _ hw_pos.ne']
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcard, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hS_pos.ne', hcard, sub_self] at hsum
    rw [hfib]
    exact sub_nonpos.mp hsum

private lemma log_factorial_eq_sum_Icc (d : ℕ) :
    Real.log ((d.factorial : ℕ) : ℝ) = ∑ m ∈ Finset.Icc 1 d, Real.log (m : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos d), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)), add_comm]

private lemma sum_perm_log_rank {n : ℕ} (T : Finset (Fin n)) (i : Fin n) (hi : i ∈ T) :
    (T.card : ℝ) *
        ∑ r : Equiv.Perm (Fin n),
          Real.log (((T.filter (fun u => (r i).1 ≤ (r u).1)).card : ℕ) : ℝ) =
      (n.factorial : ℝ) * Real.log ((T.card.factorial : ℕ) : ℝ) := by
  have hsymm : ∀ u ∈ T,
      ∑ r : Equiv.Perm (Fin n),
          Real.log (((T.filter (fun w => (r u).1 ≤ (r w).1)).card : ℕ) : ℝ) =
        ∑ r : Equiv.Perm (Fin n),
          Real.log (((T.filter (fun w => (r i).1 ≤ (r w).1)).card : ℕ) : ℝ) := by
    intro u hu
    refine (Equiv.sum_comp (Equiv.mulRight (Equiv.swap u i)) _).symm.trans ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 2
    have hmem : ∀ w, w ∈ T → Equiv.swap u i w ∈ T := by
      intro w hw
      by_cases hwu : w = u
      · subst hwu
        simpa [Equiv.swap_apply_left] using hi
      · by_cases hwi : w = i
        · subst hwi
          simpa [Equiv.swap_apply_right] using hu
        · simpa [Equiv.swap_apply_of_ne_of_ne hwu hwi] using hw
    have hinv : ∀ w, Equiv.swap u i (Equiv.swap u i w) = w := by
      intro w
      by_cases hwu : w = u
      · subst hwu
        simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
      · by_cases hwi : w = i
        · subst hwi
          simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
        · simp [Equiv.swap_apply_of_ne_of_ne hwu hwi]
    have hmul : ∀ x, ((Equiv.mulRight (Equiv.swap u i)) r) x = r (Equiv.swap u i x) :=
      fun _ => rfl
    refine Finset.card_bij (fun w _ => Equiv.swap u i w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, hmul, Equiv.swap_apply_left] at hw ⊢
      exact ⟨hmem w hw.1, hw.2⟩
    · intro w₁ _ w₂ _ h
      exact (Equiv.swap u i).injective h
    · intro w hw
      refine ⟨Equiv.swap u i w, ?_, hinv w⟩
      simp only [Finset.mem_filter, hmul, Equiv.swap_apply_left, hinv] at hw ⊢
      exact ⟨hmem w hw.1, hw.2⟩
  have hinner : ∀ r : Equiv.Perm (Fin n),
      ∑ u ∈ T, Real.log (((T.filter (fun w => (r u).1 ≤ (r w).1)).card : ℕ) : ℝ) =
        Real.log ((T.card.factorial : ℕ) : ℝ) := by
    intro r
    let rank : Fin n → ℕ := fun u => (T.filter (fun w => (r u).1 ≤ (r w).1)).card
    have hinj : Set.InjOn rank ↑T := by
      intro u₁ hu₁ u₂ hu₂ hreq
      by_contra hne
      have hrne : (r u₁).1 ≠ (r u₂).1 := fun h => hne (r.injective (Fin.ext h))
      have hlt : ∀ a b, a ∈ T → b ∈ T → (r a).1 < (r b).1 → rank b < rank a := by
        intro a b ha _ hab
        refine Finset.card_lt_card ?_
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro w hw
          simp only [Finset.mem_filter] at hw ⊢
          exact ⟨hw.1, le_trans hab.le hw.2⟩
        · intro heq
          have ha_in : a ∈ T.filter (fun w => (r a).1 ≤ (r w).1) :=
            Finset.mem_filter.mpr ⟨ha, le_rfl⟩
          rw [← heq] at ha_in
          have hba := (Finset.mem_filter.mp ha_in).2
          omega
      rcases lt_or_gt_of_ne hrne with h12 | h21
      · exact (hlt u₁ u₂ hu₁ hu₂ h12).ne hreq.symm
      · exact (hlt u₂ u₁ hu₂ hu₁ h21).ne hreq
    have hsub : T.image rank ⊆ Finset.Icc 1 T.card := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨u, hu, rfl⟩
      rw [Finset.mem_Icc]
      refine ⟨?_, Finset.card_le_card (Finset.filter_subset _ _)⟩
      exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, le_rfl⟩⟩
    have himg : T.image rank = Finset.Icc 1 T.card := by
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
      omega
    rw [log_factorial_eq_sum_Icc, ← himg, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  calc
    (T.card : ℝ) *
        ∑ r : Equiv.Perm (Fin n),
          Real.log (((T.filter (fun u => (r i).1 ≤ (r u).1)).card : ℕ) : ℝ)
        = ∑ _u ∈ T, ∑ r : Equiv.Perm (Fin n),
            Real.log (((T.filter (fun w => (r i).1 ≤ (r w).1)).card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ u ∈ T, ∑ r : Equiv.Perm (Fin n),
            Real.log (((T.filter (fun w => (r u).1 ≤ (r w).1)).card : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun u hu => (hsymm u hu).symm
    _ = ∑ r : Equiv.Perm (Fin n), ∑ u ∈ T,
            Real.log (((T.filter (fun w => (r u).1 ≤ (r w).1)).card : ℕ) : ℝ) :=
          Finset.sum_comm
    _ = ∑ _r : Equiv.Perm (Fin n), Real.log ((T.card.factorial : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun r _ => hinner r
    _ = (n.factorial : ℝ) * Real.log ((T.card.factorial : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]

private def avail {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (r σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => A i j = 1 ∧ ∀ t : Fin n, (r t).1 < (r i).1 → σ t ≠ j)

private def prefixClass {n : ℕ} (M : Finset (Equiv.Perm (Fin n)))
    (r : Equiv.Perm (Fin n)) (k : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  M.filter (fun τ => ∀ t : Fin n, (r t).1 < k → τ t = σ t)

private def prefixHist {n : ℕ} (r : Equiv.Perm (Fin n)) (k : ℕ)
    (σ : Equiv.Perm (Fin n)) : Fin n → Option (Fin n) :=
  fun t => if (r t).1 < k then some (σ t) else none

private lemma prefixHist_eq_iff {n : ℕ} (r : Equiv.Perm (Fin n)) (k : ℕ)
    (τ σ : Equiv.Perm (Fin n)) :
    prefixHist r k τ = prefixHist r k σ ↔ ∀ t : Fin n, (r t).1 < k → τ t = σ t := by
  constructor
  · intro heq t ht
    have h := congrFun heq t
    simpa [prefixHist, ht] using h
  · intro hall
    funext t
    dsimp only [prefixHist]
    split_ifs with ht
    · exact congrArg some (hall t ht)
    · rfl

private lemma step_entropy_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (r : Equiv.Perm (Fin n)) (k : Fin n) :
    let M := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, A i (σ i) = 1)
    ∑ σ ∈ M, Real.log (((prefixClass M r k.1 σ).card : ℝ) /
        ((prefixClass M r (k.1 + 1) σ).card : ℝ)) ≤
      ∑ σ ∈ M, Real.log (((avail A r σ (r.symm k)).card : ℕ) : ℝ) := by
  intro M
  have hmaps : ∀ σ ∈ M, prefixHist r k.1 σ ∈ M.image (prefixHist r k.1) :=
    fun σ hσ => Finset.mem_image_of_mem _ hσ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun h hh => ?_
  rcases Finset.mem_image.mp hh with ⟨σ₀, hσ₀, rfl⟩
  set E := M.filter (fun τ => prefixHist r k.1 τ = prefixHist r k.1 σ₀)
  have hclass_k : ∀ σ ∈ E, prefixClass M r k.1 σ = E := by
    intro σ hσ
    have hσh : prefixHist r k.1 σ = prefixHist r k.1 σ₀ := (Finset.mem_filter.mp hσ).2
    ext τ
    simp only [prefixClass, E, Finset.mem_filter, ← prefixHist_eq_iff, hσh]
  have hclass_succ : ∀ σ ∈ E,
      prefixClass M r (k.1 + 1) σ = E.filter (fun τ => τ (r.symm k) = σ (r.symm k)) := by
    intro σ hσ
    have hσh : prefixHist r k.1 σ = prefixHist r k.1 σ₀ := (Finset.mem_filter.mp hσ).2
    ext τ
    simp only [prefixClass, E, Finset.mem_filter]
    constructor
    · rintro ⟨hτM, hall⟩
      refine ⟨⟨hτM, (prefixHist_eq_iff r k.1 τ σ₀).mpr ?_⟩, ?_⟩
      · intro t ht
        have ht1 : (r t).1 < k.1 + 1 := Nat.lt_succ_of_lt ht
        exact (hall t ht1).trans ((prefixHist_eq_iff r k.1 σ σ₀).mp hσh t ht)
      · exact hall (r.symm k) (by simp)
    · rintro ⟨⟨hτM, hτh⟩, hτk⟩
      refine ⟨hτM, fun t ht => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
      · exact ((prefixHist_eq_iff r k.1 τ σ₀).mp hτh t hlt).trans
          ((prefixHist_eq_iff r k.1 σ σ₀).mp hσh t hlt).symm
      · have hrt : r t = k := Fin.ext heq
        have hti : t = r.symm k := (Equiv.eq_symm_apply r).mpr hrt
        rw [hti, hτk]
  have havail_eq : ∀ σ ∈ E, avail A r σ (r.symm k) = avail A r σ₀ (r.symm k) := by
    intro σ hσ
    have hσh : ∀ t : Fin n, (r t).1 < k.1 → σ t = σ₀ t :=
      (prefixHist_eq_iff r k.1 σ σ₀).mp (Finset.mem_filter.mp hσ).2
    ext j
    simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
    refine and_congr_right fun _ => ?_
    refine forall_congr' fun t => ?_
    refine imp_congr_right fun ht => ?_
    rw [hσh t ht]
  have hmaps_avail : ∀ σ ∈ E, σ (r.symm k) ∈ avail A r σ₀ (r.symm k) := by
    intro σ hσ
    rw [← havail_eq σ hσ]
    have hσM : σ ∈ M := (Finset.mem_filter.mp hσ).1
    have hA1 : ∀ i, A i (σ i) = 1 := (Finset.mem_filter.mp hσM).2
    simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hA1 (r.symm k), fun t ht heq => ?_⟩
    have hti : t = r.symm k := σ.injective heq
    rw [hti] at ht
    exact lt_irrefl _ ht
  have hbound := log_fiber_sum_le E (avail A r σ₀ (r.symm k)) (fun τ => τ (r.symm k)) hmaps_avail
  have hlhs :
      ∑ σ ∈ E, Real.log (((prefixClass M r k.1 σ).card : ℝ) /
          ((prefixClass M r (k.1 + 1) σ).card : ℝ)) =
        ∑ σ ∈ E, Real.log ((E.card : ℝ) /
          ((E.filter (fun τ => τ (r.symm k) = σ (r.symm k))).card : ℝ)) := by
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [hclass_k σ hσ, hclass_succ σ hσ]
  have hrhs :
      ∑ σ ∈ E, Real.log (((avail A r σ (r.symm k)).card : ℕ) : ℝ) =
        (E.card : ℝ) * Real.log (((avail A r σ₀ (r.symm k)).card : ℕ) : ℝ) := by
    have hc : ∀ σ ∈ E,
        Real.log (((avail A r σ (r.symm k)).card : ℕ) : ℝ) =
          Real.log (((avail A r σ₀ (r.symm k)).card : ℕ) : ℝ) := by
      intro σ hσ
      rw [havail_eq σ hσ]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hbound

private lemma order_entropy_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (r : Equiv.Perm (Fin n)) :
    let M := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, A i (σ i) = 1)
    (M.card : ℝ) * Real.log (M.card : ℝ) ≤
      ∑ σ ∈ M, ∑ i : Fin n, Real.log (((avail A r σ i).card : ℕ) : ℝ) := by
  intro M
  have hsum :
      ∑ k : Fin n, ∑ σ ∈ M, Real.log (((prefixClass M r k.1 σ).card : ℝ) /
          ((prefixClass M r (k.1 + 1) σ).card : ℝ)) ≤
        ∑ k : Fin n, ∑ σ ∈ M, Real.log (((avail A r σ (r.symm k)).card : ℕ) : ℝ) :=
    Finset.sum_le_sum fun k _ => step_entropy_bound A r k
  have hlhs :
      ∑ k : Fin n, ∑ σ ∈ M, Real.log (((prefixClass M r k.1 σ).card : ℝ) /
          ((prefixClass M r (k.1 + 1) σ).card : ℝ)) =
        (M.card : ℝ) * Real.log (M.card : ℝ) := by
    rw [Finset.sum_comm]
    have htele : ∀ σ ∈ M,
        ∑ k : Fin n, Real.log (((prefixClass M r k.1 σ).card : ℝ) /
            ((prefixClass M r (k.1 + 1) σ).card : ℝ)) =
          Real.log (M.card : ℝ) := by
      intro σ hσ
      have hpos : ∀ m : ℕ, ((prefixClass M r m σ).card : ℝ) ≠ 0 := by
        intro m
        exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr
          ⟨σ, Finset.mem_filter.mpr ⟨hσ, fun _ _ => rfl⟩⟩).ne'
      have hdiff : ∀ k : Fin n,
          Real.log (((prefixClass M r k.1 σ).card : ℝ) /
              ((prefixClass M r (k.1 + 1) σ).card : ℝ)) =
            Real.log ((prefixClass M r k.1 σ).card : ℝ) -
              Real.log ((prefixClass M r (k.1 + 1) σ).card : ℝ) :=
        fun k => Real.log_div (hpos k.1) (hpos (k.1 + 1))
      simp_rw [hdiff]
      rw [Fin.sum_univ_eq_sum_range (fun m =>
        Real.log ((prefixClass M r m σ).card : ℝ) -
          Real.log ((prefixClass M r (m + 1) σ).card : ℝ)),
        Finset.sum_range_sub' (fun m => Real.log ((prefixClass M r m σ).card : ℝ)) n]
      have h0 : prefixClass M r 0 σ = M := by
        ext τ
        simp [prefixClass]
      have hn : prefixClass M r n σ = {σ} := by
        ext τ
        simp only [prefixClass, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hall⟩
          exact Equiv.ext fun t => hall t (r t).2
        · rintro rfl
          exact ⟨hσ, fun _ _ => rfl⟩
      rw [h0, hn, Finset.card_singleton, Nat.cast_one, Real.log_one, sub_zero]
    rw [Finset.sum_congr rfl htele, Finset.sum_const, nsmul_eq_mul]
  have hrhs :
      ∑ k : Fin n, ∑ σ ∈ M, Real.log (((avail A r σ (r.symm k)).card : ℕ) : ℝ) =
        ∑ σ ∈ M, ∑ i : Fin n, Real.log (((avail A r σ i).card : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact Equiv.sum_comp r.symm (fun i : Fin n => Real.log (((avail A r σ i).card : ℕ) : ℝ))
  rw [← hlhs, ← hrhs]
  exact hsum

private lemma avail_card_eq_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (r σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (avail A r σ i).card =
      ((Finset.univ.filter (fun u : Fin n => A i (σ u) = 1)).filter
        (fun u => (r i).1 ≤ (r u).1)).card := by
  symm
  refine Finset.card_bij (fun u _ => σ u) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hu.1, fun t ht heq => ?_⟩
    have htu : t = u := σ.injective heq
    rw [htu] at ht
    omega
  · intro u₁ _ u₂ _ h
    exact σ.injective h
  · intro j hj
    simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨σ.symm j, ?_, Equiv.apply_symm_apply σ j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
    refine ⟨hj.1, ?_⟩
    by_contra hlt
    exact hj.2 (σ.symm j) (not_le.mp hlt) (Equiv.apply_symm_apply σ j)

private lemma owner_card_eq_deg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (Finset.univ.filter (fun u : Fin n => A i (σ u) = 1)).card = ∑ j : Fin n, A i j := by
  have hbij :
      (Finset.univ.filter (fun u : Fin n => A i (σ u) = 1)).card =
        (Finset.univ.filter (fun j : Fin n => A i j = 1)).card := by
    refine Finset.card_bij (fun u _ => σ u) ?_ ?_ ?_
    · intro u hu
      simpa using hu
    · intro u₁ _ u₂ _ h
      exact σ.injective h
    · intro j hj
      exact ⟨σ.symm j, by simpa using hj, Equiv.apply_symm_apply σ j⟩
  rw [hbij, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle := hA i j
  split_ifs with h
  · exact h.symm
  · omega

private lemma permanent_eq_card_matchings {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) :
    A.permanent =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, A i (σ i) = 1)).card := by
  rw [← Matrix.permanent_transpose, Matrix.permanent, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.transpose_apply]
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => h i
  · rcases not_forall.mp h with ⟨i, hi⟩
    have h0 : A i (σ i) = 0 := by
      have := hA i (σ i)
      omega
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0

end PEqualNP.Outside.L_lib_460

theorem PEqualNP.Outside.L_lib_460 : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ), (∀ i j, A i j ≤ 1) →
  let deg := fun (i : Fin n) => ∑ j : Fin n, A i j
  (∀ i, 0 < deg i) →
    A.permanent ^ (Nat.factorial n) ≤
      ∏ i : Fin n, (Nat.factorial (deg i))^(Nat.factorial n / deg i) := by
  intro n A hA deg hdeg
  set M := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, A i (σ i) = 1)
  have hperm : A.permanent = M.card :=
    PEqualNP.Outside.L_lib_460.permanent_eq_card_matchings A hA
  rw [hperm]
  by_cases hM : M.card = 0
  · rw [hM, zero_pow (Nat.factorial_ne_zero n)]
    exact Nat.zero_le _
  · have hM_pos : 0 < M.card := Nat.pos_of_ne_zero hM
    have hM_pos_r : (0 : ℝ) < (M.card : ℝ) := Nat.cast_pos.mpr hM_pos
    have hdeg_le : ∀ i : Fin n, deg i ≤ n := by
      intro i
      calc
        deg i = ∑ j : Fin n, A i j := rfl
        _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => hA i j
        _ = n := by simp
    have hdeg_dvd : ∀ i : Fin n, deg i ∣ n.factorial :=
      fun i => Nat.dvd_factorial (hdeg i) (hdeg_le i)
    have hterm : ∀ σ ∈ M, ∀ i : Fin n,
        ∑ r : Equiv.Perm (Fin n),
            Real.log (((PEqualNP.Outside.L_lib_460.avail A r σ i).card : ℕ) : ℝ) =
          ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
      intro σ hσ i
      set T := Finset.univ.filter (fun u : Fin n => A i (σ u) = 1)
      have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hσ).2 i⟩
      have hTcard : T.card = deg i := PEqualNP.Outside.L_lib_460.owner_card_eq_deg A hA σ i
      have hrank := PEqualNP.Outside.L_lib_460.sum_perm_log_rank T i hiT
      have hcongr :
          ∑ r : Equiv.Perm (Fin n),
              Real.log (((PEqualNP.Outside.L_lib_460.avail A r σ i).card : ℕ) : ℝ) =
            ∑ r : Equiv.Perm (Fin n),
              Real.log (((T.filter (fun u => (r i).1 ≤ (r u).1)).card : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [PEqualNP.Outside.L_lib_460.avail_card_eq_rank]
      rw [hcongr]
      have hdeg_ne : (deg i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg i).ne'
      apply mul_left_cancel₀ hdeg_ne
      rw [← hTcard, hrank, hTcard]
      have hmul : (deg i : ℝ) * ((n.factorial / deg i : ℕ) : ℝ) = (n.factorial : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' (hdeg_dvd i)
      rw [← mul_assoc, hmul]
    have hsum_all :
        (n.factorial : ℝ) * ((M.card : ℝ) * Real.log (M.card : ℝ)) ≤
          (M.card : ℝ) * ∑ i : Fin n,
            ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
      calc
        (n.factorial : ℝ) * ((M.card : ℝ) * Real.log (M.card : ℝ))
            = ∑ _r : Equiv.Perm (Fin n), ((M.card : ℝ) * Real.log (M.card : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
                nsmul_eq_mul]
        _ ≤ ∑ r : Equiv.Perm (Fin n), ∑ σ ∈ M, ∑ i : Fin n,
              Real.log (((PEqualNP.Outside.L_lib_460.avail A r σ i).card : ℕ) : ℝ) :=
              Finset.sum_le_sum fun r _ => PEqualNP.Outside.L_lib_460.order_entropy_bound A r
        _ = ∑ σ ∈ M, ∑ r : Equiv.Perm (Fin n), ∑ i : Fin n,
              Real.log (((PEqualNP.Outside.L_lib_460.avail A r σ i).card : ℕ) : ℝ) :=
              Finset.sum_comm
        _ = ∑ σ ∈ M, ∑ i : Fin n, ∑ r : Equiv.Perm (Fin n),
              Real.log (((PEqualNP.Outside.L_lib_460.avail A r σ i).card : ℕ) : ℝ) := by
              refine Finset.sum_congr rfl fun σ _ => Finset.sum_comm
        _ = ∑ _σ ∈ M, ∑ i : Fin n,
              ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
              refine Finset.sum_congr rfl fun σ hσ => ?_
              exact Finset.sum_congr rfl fun i _ => hterm σ hσ i
        _ = (M.card : ℝ) * ∑ i : Fin n,
              ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hlog_ineq :
        (n.factorial : ℝ) * Real.log (M.card : ℝ) ≤
          ∑ i : Fin n,
            ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
      have hmul' :
          (M.card : ℝ) * ((n.factorial : ℝ) * Real.log (M.card : ℝ)) ≤
            (M.card : ℝ) * ∑ i : Fin n,
              ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
        simpa [mul_left_comm] using hsum_all
      exact le_of_mul_le_mul_left hmul' hM_pos_r
    have hlhs_pos : (0 : ℝ) < ((M.card ^ n.factorial : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (pow_pos hM_pos n.factorial)
    have hrhs_pos :
        (0 : ℝ) < ((∏ i : Fin n, (deg i).factorial ^ (n.factorial / deg i) : ℕ) : ℝ) := by
      refine Nat.cast_pos.mpr (Finset.prod_pos fun i _ => ?_)
      exact pow_pos (Nat.factorial_pos (deg i)) _
    have hlog_both :
        Real.log ((M.card ^ n.factorial : ℕ) : ℝ) ≤
          Real.log ((∏ i : Fin n, (deg i).factorial ^ (n.factorial / deg i) : ℕ) : ℝ) := by
      have h1 : Real.log ((M.card ^ n.factorial : ℕ) : ℝ) =
          (n.factorial : ℝ) * Real.log (M.card : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
      have h2 :
          Real.log ((∏ i : Fin n, (deg i).factorial ^ (n.factorial / deg i) : ℕ) : ℝ) =
            ∑ i : Fin n,
              ((n.factorial / deg i : ℕ) : ℝ) * Real.log (((deg i).factorial : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.cast_pow, Real.log_pow]
        · intro i _
          exact Nat.cast_ne_zero.mpr (pow_pos (Nat.factorial_pos (deg i)) _).ne'
      rw [h1, h2]
      exact hlog_ineq
    exact_mod_cast (Real.log_le_log_iff hlhs_pos hrhs_pos).mp hlog_both
