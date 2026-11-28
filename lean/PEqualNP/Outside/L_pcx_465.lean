import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_465_aux

open scoped BigOperators

def sgn (b : ZMod 2) : ℚ :=
  if b = 0 then 1 else -1

lemma zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma sgn_zero : sgn 0 = 1 := by
  simp [sgn]

lemma sgn_one : sgn 1 = -1 := by
  simp [sgn]

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · rw [zmod2_add_self]; simp [sgn]

lemma sgn_mul_eq (a b : ZMod 2) :
    sgn a * sgn b = if a = b then (1 : ℚ) else -1 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> simp [sgn]

lemma sgn_eq_hit (a b : ZMod 2) :
    sgn a = (2 * (if a = b then (1 : ℚ) else 0) - 1) * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [sgn] <;> norm_num

lemma sum_sgn_dot_eq_zero {n : ℕ} {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    ∑ x : Fin n → ZMod 2, sgn (dotProduct v x) = 0 := by
  have hex : ∃ l : Fin n, v l ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  rcases hex with ⟨l, hl⟩
  have hvl : v l = 1 := (zmod2_cases (v l)).resolve_left hl
  let e : Fin n → ZMod 2 := Pi.single l 1
  have hdot : dotProduct v e = 1 := by
    simp [dotProduct, e, Pi.single_apply, hvl]
  have hshift : ∀ x : Fin n → ZMod 2,
      sgn (dotProduct v (x + e)) = -sgn (dotProduct v x) := by
    intro x
    rw [dotProduct_add, hdot, sgn_add, sgn_one]
    ring
  have hcomp : ∑ x : Fin n → ZMod 2, sgn (dotProduct v (x + e)) =
      ∑ x : Fin n → ZMod 2, sgn (dotProduct v x) :=
    Equiv.sum_comp (Equiv.addRight e) (fun x => sgn (dotProduct v x))
  have hneg : ∑ x : Fin n → ZMod 2, sgn (dotProduct v (x + e)) =
      -(∑ x : Fin n → ZMod 2, sgn (dotProduct v x)) := by
    simp only [hshift, Finset.sum_neg_distrib]
  linarith

lemma card_annihilator_le {n j : ℕ} (T : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2)) :
    ((Finset.univ : Finset (Fin n → ZMod 2)).filter
      (fun freq => ∀ h : Fin n → ZMod 2, T h = 0 → dotProduct freq h = 0)).card ≤ 2 ^ j := by
  let S : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun freq => ∀ h : Fin n → ZMod 2, T h = 0 → dotProduct freq h = 0)
  let K : Finset (Fin n → ZMod 2) := Finset.univ.filter (fun h => T h = 0)
  let I : Finset (Fin j → ZMod 2) := Finset.univ.image T
  have h0S : (0 : Fin n → ZMod 2) ∈ S := by
    simp [S]
  have h0K : (0 : Fin n → ZMod 2) ∈ K := by
    simp [K]
  have hK_pos : 0 < K.card := Finset.card_pos.mpr ⟨0, h0K⟩
  have hS_add : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv ⊢
    intro h hh
    rw [add_dotProduct, hu h hh, hv h hh, add_zero]
  have hK_mul_I : K.card * I.card = 2 ^ n := by
    have hpart : (Finset.univ : Finset (Fin n → ZMod 2)).card =
        ∑ y ∈ I, ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => T x = y)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext x
        simp [I]
      · intro y₁ _ y₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hfib : ∀ y ∈ I,
        ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => T x = y)).card = K.card := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x₀, _, rfl⟩
      refine Finset.card_bij (fun x _ => x + x₀) ?_ ?_ ?_
      · intro x hx
        have hTx : T x = T x₀ := (Finset.mem_filter.mp hx).2
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [map_add, hTx]
        ext l
        exact zmod2_add_self (T x₀ l)
      · intro x₁ _ x₂ _ h
        exact add_right_cancel h
      · intro h hh
        have hTh : T h = 0 := (Finset.mem_filter.mp hh).2
        refine ⟨h + x₀, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_add, hTh, zero_add]
        · ext l
          simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
    have hcard_univ : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
      simp [ZMod.card]
    rw [hcard_univ, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm] at hpart
    exact hpart.symm
  have hchar_nn : ∀ x : Fin n → ZMod 2, 0 ≤ ∑ freq ∈ S, sgn (dotProduct freq x) := by
    intro x
    by_cases hex : ∃ freq₀ ∈ S, dotProduct freq₀ x ≠ 0
    · rcases hex with ⟨freq₀, hf₀, hdot⟩
      have hdot1 : dotProduct freq₀ x = 1 := (zmod2_cases _).resolve_left hdot
      have hneg : ∑ freq ∈ S, sgn (dotProduct freq x) = 0 := by
        have hsum_eq : ∑ freq ∈ S, sgn (dotProduct (freq + freq₀) x) =
            ∑ freq ∈ S, sgn (dotProduct freq x) := by
          refine Finset.sum_bij (fun freq _ => freq + freq₀) ?_ ?_ ?_ ?_
          · intro freq hfreq; exact hS_add freq hfreq freq₀ hf₀
          · intro f₁ _ f₂ _ h; exact add_right_cancel h
          · intro freq hfreq
            refine ⟨freq + freq₀, hS_add freq hfreq freq₀ hf₀, ?_⟩
            ext l
            simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
          · intro _ _; rfl
        have hsum_neg : ∑ freq ∈ S, sgn (dotProduct (freq + freq₀) x) =
            -(∑ freq ∈ S, sgn (dotProduct freq x)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro freq _
          rw [add_dotProduct, hdot1, sgn_add, sgn_one]
          ring
        linarith
      linarith
    · push Not at hex
      apply Finset.sum_nonneg
      intro freq hfreq
      rw [hex freq hfreq, sgn_zero]
      norm_num
  have hchar_K : ∀ x ∈ K, ∑ freq ∈ S, sgn (dotProduct freq x) = (S.card : ℚ) := by
    intro x hx
    have hTx : T x = 0 := (Finset.mem_filter.mp hx).2
    have h1 : ∀ freq ∈ S, sgn (dotProduct freq x) = 1 := by
      intro freq hfreq
      have h0 := (Finset.mem_filter.mp hfreq).2 x hTx
      rw [h0, sgn_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have htot : ∑ x : Fin n → ZMod 2, ∑ freq ∈ S, sgn (dotProduct freq x) = (2 ^ n : ℚ) := by
    rw [Finset.sum_comm, Finset.sum_eq_single (0 : Fin n → ZMod 2)]
    · simp [sgn_zero, ZMod.card]
    · intro freq _ hne
      exact sum_sgn_dot_eq_zero hne
    · intro h; exact absurd h0S h
  have hle_q : (K.card : ℚ) * (S.card : ℚ) ≤ (2 ^ n : ℚ) := by
    have h1 : ∑ x ∈ K, ∑ freq ∈ S, sgn (dotProduct freq x) ≤
        ∑ x : Fin n → ZMod 2, ∑ freq ∈ S, sgn (dotProduct freq x) :=
      Finset.sum_le_univ_sum_of_nonneg hchar_nn
    rw [Finset.sum_congr rfl hchar_K, Finset.sum_const, nsmul_eq_mul, htot] at h1
    exact h1
  have hle_nat : K.card * S.card ≤ 2 ^ n := by
    exact_mod_cast hle_q
  have hS_le_I : S.card ≤ I.card := by
    rw [← hK_mul_I] at hle_nat
    exact Nat.le_of_mul_le_mul_left hle_nat hK_pos
  have hI_le : I.card ≤ 2 ^ j := by
    have hsub : I.card ≤ (Finset.univ : Finset (Fin j → ZMod 2)).card :=
      Finset.card_le_card (Finset.subset_univ I)
    simpa [Fintype.card_fun, ZMod.card] using hsub
  exact le_trans hS_le_I hI_le

end PEqualNP.Outside.L_pcx_465_aux

theorem PEqualNP.Outside.L_pcx_465 :
  ∀ n j k r : ℕ,
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin j → F
  ∀ (f : X → F) (A : Fin k → X →ₗ[F] Y)
    (pick : Fin r → Fin k) (out : Fin r → Y → F)
    (w : Fin r → ℚ) (mu : X → ℚ) (p : ℚ),
    let hit := fun (z : Fin r) (x : X) => out z (A (pick z) x)=f x
    let prob := fun x : X => ∑ z : Fin r, if hit z x then w z else 0
    let walsh := fun freq : X => ∑ x : X, if f x = dotProduct freq x then (1 : ℤ) else -1
    (∀ z, 0 ≤ w z) → (∑ z, w z)=1 →
    (∀ x, 0 < mu x) → (∑ x, mu x)=1 → 1/2 < p →
    (∀ z, 0 < w z → (∑ x : X, if hit z x then mu x else 0) ≤ p) →
    (∀ x, p ≤ prob x) →
    (∀ x, prob x=p) ∧
    (∀ freq, walsh freq ≠ 0 → ∃ z, 0 < w z ∧
      ∀ h : X, A (pick z) h=0 → dotProduct freq h=0) ∧
    Nat.card {freq : X // freq ≠ 0 ∧ walsh freq ≠ 0} ≤ k*(2^j-1) := by
  intro n j k r
  dsimp only
  intro f A pick out w mu p hw_nn hw_sum hmu_pos hmu_sum hp_half hz_ub hx_lb
  let hit := fun (z : Fin r) (x : Fin n → ZMod 2) => out z (A (pick z) x) = f x
  let prob := fun x : Fin n → ZMod 2 => ∑ z : Fin r, if hit z x then w z else 0
  let walsh := fun freq : Fin n → ZMod 2 =>
    ∑ x : Fin n → ZMod 2, if f x = dotProduct freq x then (1 : ℤ) else -1
  have hS_eq : ∑ x : Fin n → ZMod 2, mu x * prob x =
      ∑ z : Fin r, w z * (∑ x : Fin n → ZMod 2, if hit z x then mu x else 0) := by
    calc ∑ x : Fin n → ZMod 2, mu x * prob x
        = ∑ x : Fin n → ZMod 2, ∑ z : Fin r, if hit z x then mu x * w z else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          dsimp only [prob]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> ring
      _ = ∑ z : Fin r, ∑ x : Fin n → ZMod 2, if hit z x then mu x * w z else 0 := Finset.sum_comm
      _ = ∑ z : Fin r, w z * (∑ x : Fin n → ZMod 2, if hit z x then mu x else 0) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> ring
  have hS_le : ∑ x : Fin n → ZMod 2, mu x * prob x ≤ p := by
    rw [hS_eq]
    have h1 : ∑ z : Fin r, w z * (∑ x : Fin n → ZMod 2, if hit z x then mu x else 0) ≤
        ∑ z : Fin r, w z * p := by
      apply Finset.sum_le_sum
      intro z _
      rcases eq_or_lt_of_le (hw_nn z) with hw0 | hwpos
      · rw [← hw0]; simp
      · exact mul_le_mul_of_nonneg_left (hz_ub z hwpos) (hw_nn z)
    rw [← Finset.sum_mul, hw_sum, one_mul] at h1
    exact h1
  have hprob_eq : ∀ x : Fin n → ZMod 2, prob x = p := by
    have hsum0 : ∑ x : Fin n → ZMod 2, mu x * (prob x - p) = 0 := by
      have hge : 0 ≤ ∑ x : Fin n → ZMod 2, mu x * (prob x - p) := by
        apply Finset.sum_nonneg
        intro x _
        exact mul_nonneg (hmu_pos x).le (sub_nonneg.mpr (hx_lb x))
      have hle : ∑ x : Fin n → ZMod 2, mu x * (prob x - p) ≤ 0 := by
        have hrew : ∑ x : Fin n → ZMod 2, mu x * (prob x - p) =
            (∑ x : Fin n → ZMod 2, mu x * prob x) - p := by
          have : ∑ x : Fin n → ZMod 2, mu x * (prob x - p) =
              (∑ x : Fin n → ZMod 2, mu x * prob x) - (∑ x : Fin n → ZMod 2, mu x) * p := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _; ring
          rw [this, hmu_sum, one_mul]
        linarith
      linarith
    have heach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => mul_nonneg (hmu_pos x).le (sub_nonneg.mpr (hx_lb x)))).mp hsum0
    intro x
    have h0 := heach x (Finset.mem_univ x)
    have hsub := (mul_eq_zero.mp h0).resolve_left (hmu_pos x).ne'
    linarith
  have hcov : ∀ freq : Fin n → ZMod 2, walsh freq ≠ 0 →
      ∃ z : Fin r, 0 < w z ∧ ∀ h : Fin n → ZMod 2, A (pick z) h = 0 → dotProduct freq h = 0 := by
    intro freq hwf
    have hpoint : ∀ x : Fin n → ZMod 2,
        ∑ z : Fin r, w z * PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) =
          (2 * p - 1) * PEqualNP.Outside.L_pcx_465_aux.sgn (f x) := by
      intro x
      have h1 : ∀ z : Fin r,
          w z * PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) =
          (2 * (if hit z x then w z else 0) - w z) * PEqualNP.Outside.L_pcx_465_aux.sgn (f x) := by
        intro z
        rw [PEqualNP.Outside.L_pcx_465_aux.sgn_eq_hit (out z (A (pick z) x)) (f x)]
        dsimp only [hit]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun z _ => h1 z), ← Finset.sum_mul, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      change (2 * prob x - ∑ z : Fin r, w z) * PEqualNP.Outside.L_pcx_465_aux.sgn (f x) = _
      rw [hprob_eq x, hw_sum]
    have hwalsh_q : ∑ x : Fin n → ZMod 2,
        PEqualNP.Outside.L_pcx_465_aux.sgn (f x) *
          PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x) = (walsh freq : ℚ) := by
      dsimp only [walsh]
      push_cast
      apply Finset.sum_congr rfl
      intro x _
      exact PEqualNP.Outside.L_pcx_465_aux.sgn_mul_eq (f x) (dotProduct freq x)
    have hsum_ne : ∑ z : Fin r, w z *
        (∑ x : Fin n → ZMod 2,
          PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) *
            PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x)) ≠ 0 := by
      have hswap : ∑ z : Fin r, w z *
          (∑ x : Fin n → ZMod 2,
            PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) *
              PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x)) =
          (2 * p - 1) * (walsh freq : ℚ) := by
        calc ∑ z : Fin r, w z *
              (∑ x : Fin n → ZMod 2,
                PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) *
                  PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x))
            = ∑ z : Fin r, ∑ x : Fin n → ZMod 2,
                (w z * PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x))) *
                  PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x) := by
              apply Finset.sum_congr rfl
              intro z _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _; ring
          _ = ∑ x : Fin n → ZMod 2,
                (∑ z : Fin r, w z * PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x))) *
                  PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.sum_mul]
          _ = ∑ x : Fin n → ZMod 2,
                ((2 * p - 1) * PEqualNP.Outside.L_pcx_465_aux.sgn (f x)) *
                  PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [hpoint x]
          _ = (2 * p - 1) * ∑ x : Fin n → ZMod 2,
                PEqualNP.Outside.L_pcx_465_aux.sgn (f x) *
                  PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _; ring
          _ = (2 * p - 1) * (walsh freq : ℚ) := by rw [hwalsh_q]
      rw [hswap]
      apply mul_ne_zero
      · linarith
      · exact_mod_cast hwf
    have hex : ∃ z : Fin r, w z *
        (∑ x : Fin n → ZMod 2,
          PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) *
            PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x)) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hsum_ne (Finset.sum_eq_zero (fun z _ => hall z))
    rcases hex with ⟨z, hz⟩
    have hwz_ne : w z ≠ 0 := left_ne_zero_of_mul hz
    have hcorr_ne : ∑ x : Fin n → ZMod 2,
        PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) *
          PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x) ≠ 0 :=
      right_ne_zero_of_mul hz
    refine ⟨z, lt_of_le_of_ne (hw_nn z) (Ne.symm hwz_ne), ?_⟩
    intro h hAh
    by_contra hdot_ne
    have hdot1 : dotProduct freq h = 1 :=
      (PEqualNP.Outside.L_pcx_465_aux.zmod2_cases _).resolve_left hdot_ne
    let g : (Fin n → ZMod 2) → ℚ := fun x =>
      PEqualNP.Outside.L_pcx_465_aux.sgn (out z (A (pick z) x)) *
        PEqualNP.Outside.L_pcx_465_aux.sgn (dotProduct freq x)
    have hshift : ∀ x : Fin n → ZMod 2, g (x + h) = -g x := by
      intro x
      dsimp only [g]
      rw [map_add, hAh, add_zero, dotProduct_add, hdot1, PEqualNP.Outside.L_pcx_465_aux.sgn_add,
        PEqualNP.Outside.L_pcx_465_aux.sgn_one]
      ring
    have hcomp : ∑ x : Fin n → ZMod 2, g (x + h) = ∑ x : Fin n → ZMod 2, g x :=
      Equiv.sum_comp (Equiv.addRight h) g
    have hneg : ∑ x : Fin n → ZMod 2, g (x + h) = -(∑ x : Fin n → ZMod 2, g x) := by
      simp only [hshift, Finset.sum_neg_distrib]
    exact hcorr_ne (by linarith)
  have hcard : Nat.card {freq : Fin n → ZMod 2 // freq ≠ 0 ∧ walsh freq ≠ 0} ≤ k * (2 ^ j - 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    let U : Fin k → Finset (Fin n → ZMod 2) := fun i =>
      Finset.univ.filter (fun freq => freq ≠ 0 ∧ ∀ h : Fin n → ZMod 2, A i h = 0 → dotProduct freq h = 0)
    have hsub : (Finset.univ.filter (fun freq : Fin n → ZMod 2 => freq ≠ 0 ∧ walsh freq ≠ 0)) ⊆
        Finset.univ.biUnion U := by
      intro freq hfreq
      rcases Finset.mem_filter.mp hfreq with ⟨_, hne0, hwf⟩
      rcases hcov freq hwf with ⟨z, _, hann⟩
      exact Finset.mem_biUnion.mpr ⟨pick z, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne0, hann⟩⟩
    have hle1 : (Finset.univ.filter (fun freq : Fin n → ZMod 2 => freq ≠ 0 ∧ walsh freq ≠ 0)).card ≤
        ∑ i : Fin k, (U i).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hU_le : ∀ i : Fin k, (U i).card ≤ 2 ^ j - 1 := by
      intro i
      let S : Finset (Fin n → ZMod 2) :=
        Finset.univ.filter (fun freq => ∀ h : Fin n → ZMod 2, A i h = 0 → dotProduct freq h = 0)
      have h0S : (0 : Fin n → ZMod 2) ∈ S := by simp [S]
      have hUeq : U i = S.erase 0 := by
        ext freq
        simp only [U, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      rw [hUeq, Finset.card_erase_of_mem h0S]
      exact Nat.sub_le_sub_right (PEqualNP.Outside.L_pcx_465_aux.card_annihilator_le (A i)) 1
    have hle2 : ∑ i : Fin k, (U i).card ≤ ∑ _i : Fin k, (2 ^ j - 1) :=
      Finset.sum_le_sum (fun i _ => hU_le i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle2
    exact le_trans hle1 hle2
  exact ⟨hprob_eq, hcov, hcard⟩
