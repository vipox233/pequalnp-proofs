import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_244_aux

open scoped BigOperators
open PEqualNP.ProofComplexity

abbrev F := ZMod 2

lemma zmod2_add_self (x : F) : x + x = 0 := by
  revert x; decide

lemma mv_coeff_add {V : Type*} (m : V →₀ ℕ) (p q : MvPolynomial V F) :
    (p + q).coeff m = p.coeff m + q.coeff m := by
  rw [AddMonoidAlgebra.coeff_add]; rfl

lemma mv_two_eq_zero {V : Type*} : (2 : MvPolynomial V F) = 0 := by
  have h1 : (2 : MvPolynomial V F) = 1 + 1 := by ring
  rw [h1, ← map_one MvPolynomial.C, ← map_add]
  have h2 : (1 : F) + 1 = 0 := by decide
  rw [h2, map_zero]

lemma mv_add_self {V : Type*} (x : MvPolynomial V F) : x + x = 0 := by
  calc
    x + x = (2 : MvPolynomial V F) * x := by ring
    _ = 0 := by rw [mv_two_eq_zero, zero_mul]

lemma clausePoly_pair {V : Type} [DecidableEq V] {i j : V} (hij : i ≠ j) (s1 s2 : Bool) :
    clausePoly ({(i, s1), (j, s2)} : Clause V) =
      (if s1 = true then 1 + MvPolynomial.X i else MvPolynomial.X i) *
      (if s2 = true then 1 + MvPolynomial.X j else MvPolynomial.X j) := by
  unfold clausePoly
  have hne : (i, s1) ≠ (j, s2) := fun h => hij (congrArg Prod.fst h)
  rw [Finset.prod_pair hne]

lemma totalDegree_lit {V : Type} (v : V) (s : Bool) :
    (if s = true then (1 : MvPolynomial V F) + MvPolynomial.X v else MvPolynomial.X v).totalDegree ≤ 1 := by
  cases s
  · simp [MvPolynomial.totalDegree_X]
  · simp only [↓reduceIte]
    exact le_trans (MvPolynomial.totalDegree_add _ _) (by simp [MvPolynomial.totalDegree_X])

lemma totalDegree_clausePoly_pair {V : Type} [DecidableEq V] {i j : V} (hij : i ≠ j) (s1 s2 : Bool) :
    (clausePoly ({(i, s1), (j, s2)} : Clause V)).totalDegree = 2 := by
  rw [clausePoly_pair hij]
  apply le_antisymm
  · exact le_trans (MvPolynomial.totalDegree_mul _ _)
      (Nat.add_le_add (totalDegree_lit i s1) (totalDegree_lit j s2))
  · let m : V →₀ ℕ := Finsupp.single i 1 + Finsupp.single j 1
    have hm_sum : m.sum (fun _ e => e) = 2 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp [Finsupp.sum_single_index]
    have hm_ne0 : m ≠ 0 := by
      intro h
      have := congrArg (fun f : V →₀ ℕ => f i) h
      simp [m, hij] at this
    have hm_nei : m ≠ Finsupp.single i 1 := by
      intro h
      have := congrArg (fun f : V →₀ ℕ => f j) h
      simp [m, hij.symm] at this
    have hm_nej : m ≠ Finsupp.single j 1 := by
      intro h
      have := congrArg (fun f : V →₀ ℕ => f i) h
      simp [m, hij] at this
    have hXmul : (MvPolynomial.X i : MvPolynomial V F) * MvPolynomial.X j = MvPolynomial.monomial m 1 := by
      simp [MvPolynomial.X, m]
    have hcoeff1 : ((MvPolynomial.X i : MvPolynomial V F) * MvPolynomial.X j).coeff m = 1 := by
      rw [hXmul, MvPolynomial.coeff_monomial]
      simp
    have hcoeff0 : (1 : MvPolynomial V F).coeff m = 0 := by
      rw [MvPolynomial.coeff_one]; simp [hm_ne0.symm]
    have hcoeffi : (MvPolynomial.X i : MvPolynomial V F).coeff m = 0 := by
      rw [MvPolynomial.coeff_X]; simp [hm_nei.symm]
    have hcoeffj : (MvPolynomial.X j : MvPolynomial V F).coeff m = 0 := by
      rw [MvPolynomial.coeff_X]; simp [hm_nej.symm]
    have hcoeff :
        ((if s1 = true then (1 : MvPolynomial V F) + MvPolynomial.X i else MvPolynomial.X i) *
         (if s2 = true then 1 + MvPolynomial.X j else MvPolynomial.X j)).coeff m = 1 := by
      cases s1 <;> cases s2
      · simpa using hcoeff1
      · simp only [Bool.false_eq_true, ↓reduceIte, mul_add, mul_one, mv_coeff_add,
          hcoeffi, hcoeff1, zero_add]
      · simp only [Bool.false_eq_true, ↓reduceIte, add_mul, one_mul, mv_coeff_add,
          hcoeffj, hcoeff1, zero_add]
      · simp only [↓reduceIte, add_mul, mul_add, one_mul, mul_one, mv_coeff_add,
          hcoeff0, hcoeffi, hcoeffj, hcoeff1, zero_add]
    have hmem : m ∈ ((if s1 = true then (1 : MvPolynomial V F) + MvPolynomial.X i else MvPolynomial.X i) *
        (if s2 = true then 1 + MvPolynomial.X j else MvPolynomial.X j)).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [hcoeff]; decide)
    have hle := MvPolynomial.le_totalDegree hmem
    omega

def RevStep (p a : ℕ) (S T : Finset ℕ) : Prop :=
  S.card ≤ p ∧ T.card ≤ p ∧
  (∀ x ∈ S, a ≤ x) ∧ (∀ x ∈ T, a ≤ x) ∧
  (S = T ∨ ∃ j : ℕ, a ≤ j ∧ (j = a ∨ j - 1 ∈ S) ∧
    (T = insert j S ∨ S = insert j T))

lemma revStep_symm {p a : ℕ} {S T : Finset ℕ} (h : RevStep p a S T) : RevStep p a T S := by
  rcases h with ⟨hSc, hTc, hSa, hTa, rfl | ⟨j, hja, hpre, hST⟩⟩
  · exact ⟨hSc, hTc, hSa, hTa, Or.inl rfl⟩
  · refine ⟨hTc, hSc, hTa, hSa, Or.inr ⟨j, hja, ?_, hST.symm⟩⟩
    by_cases hja_eq : j = a
    · exact Or.inl hja_eq
    · right
      rcases hpre with rfl | hmem
      · exact absurd rfl hja_eq
      · rcases hST with rfl | rfl
        · exact Finset.mem_insert_of_mem hmem
        · have hne : j - 1 ≠ j := by omega
          rcases Finset.mem_insert.mp hmem with heq | hT
          · exact absurd heq hne
          · exact hT

def ValidWalk (p a L : ℕ) (W : ℕ → Finset ℕ) : Prop :=
  ∀ i < L, RevStep p a (W i) (W (i + 1))

lemma validWalk_card_le {p a L : ℕ} {W : ℕ → Finset ℕ} (hW : ValidWalk p a L W)
    (h0 : (W 0).card ≤ p) {i : ℕ} (hi : i ≤ L) : (W i).card ≤ p := by
  cases i with
  | zero => exact h0
  | succ k => exact (hW k (by omega)).2.1

lemma validWalk_ge {p a L : ℕ} {W : ℕ → Finset ℕ} (hW : ValidWalk p a L W)
    (h0 : ∀ x ∈ W 0, a ≤ x) {i : ℕ} (hi : i ≤ L) : ∀ x ∈ W i, a ≤ x := by
  cases i with
  | zero => exact h0
  | succ k => exact (hW k (by omega)).2.2.2.1

lemma validWalk_reverse {p a L : ℕ} {W : ℕ → Finset ℕ} (hW : ValidWalk p a L W) :
    ValidWalk p a L (fun i => W (L - i)) := by
  intro i hi
  dsimp only
  have h1 : L - i = (L - (i + 1)) + 1 := by omega
  rw [h1]
  exact revStep_symm (hW (L - (i + 1)) (by omega))

lemma validWalk_concat {p a L1 L2 : ℕ} {W1 W2 : ℕ → Finset ℕ}
    (h1 : ValidWalk p a L1 W1) (h2 : ValidWalk p a L2 W2) (hmid : W1 L1 = W2 0) :
    ∃ W : ℕ → Finset ℕ, ValidWalk p a (L1 + L2) W ∧ W 0 = W1 0 ∧ W (L1 + L2) = W2 L2 := by
  let W : ℕ → Finset ℕ := fun i => if i ≤ L1 then W1 i else W2 (i - L1)
  refine ⟨W, ?_, by simp [W], ?_⟩
  · intro i hi
    by_cases hlt : i < L1
    · have h1le : i ≤ L1 := by omega
      have h2le : i + 1 ≤ L1 := by omega
      simp only [W, h1le, h2le, ↓reduceIte]
      exact h1 i hlt
    · by_cases heq : i = L1
      · subst heq
        have hle : i ≤ i := le_refl i
        have hnot : ¬ i + 1 ≤ i := by omega
        simp only [W, hle, hnot, ↓reduceIte, hmid, show i + 1 - i = 1 by omega]
        exact h2 0 (by omega)
      · have hnot1 : ¬ i ≤ L1 := by omega
        have hnot2 : ¬ i + 1 ≤ L1 := by omega
        simp only [W, hnot1, hnot2, ↓reduceIte, show i + 1 - L1 = (i - L1) + 1 by omega]
        exact h2 (i - L1) (by omega)
  · by_cases hL2 : L2 = 0
    · subst hL2; simp [W, hmid]
    · have hnot : ¬ L1 + L2 ≤ L1 := by omega
      simp only [W, hnot, ↓reduceIte, show L1 + L2 - L1 = L2 by omega]

lemma pebble_reach_bound : ∀ (p : ℕ), 1 ≤ p →
    ∀ (L a : ℕ) (W : ℕ → Finset ℕ), ValidWalk p a L W → W 0 = ∅ →
      ∀ y ∈ W L, y ≤ a + 2 ^ p - 2 := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ihp =>
    intro _
    by_cases hp0 : p = 0
    · subst hp0
      intro L a W hW hW0 y hy
      have hall : ∀ t ≤ L, ∀ z ∈ W t, z = a := by
        intro t
        induction t with
        | zero => intro _ z hz; rw [hW0] at hz; exact absurd hz (Finset.notMem_empty z)
        | succ t iht =>
          intro htl z hz
          rcases hW t (by omega) with ⟨hSc, hTc, hSa, hTa, heq | ⟨j, hja, hpre, hST⟩⟩
          · rw [← heq] at hz; exact iht (by omega) z hz
          · rcases hST with hT | hS
            · rw [hT] at hz
              rcases Finset.mem_insert.mp hz with rfl | hmem
              · by_cases hza : z = a
                · exact hza
                · rcases hpre with rfl | hjm
                  · rfl
                  · exfalso
                    have hne : z - 1 ≠ z := by omega
                    have hsub : ({z - 1, z} : Finset ℕ) ⊆ W (t + 1) := by
                      intro u hu
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
                      rw [hT]
                      rcases hu with hu | hu
                      · rw [hu]; exact Finset.mem_insert_of_mem hjm
                      · rw [hu]; exact Finset.mem_insert_self z _
                    have hc := Finset.card_le_card hsub
                    rw [Finset.card_pair hne] at hc
                    omega
              · exact iht (by omega) z hmem
            · rw [hS] at iht
              exact iht (by omega) z (Finset.mem_insert_of_mem hz)
      have hy_eq := hall L (le_refl L) y hy
      omega
    · have hp1 : 1 ≤ p := by omega
      intro L
      induction L using Nat.strong_induction_on with
      | ind L ihL =>
        intro a W hW hW0 y hy
        by_contra hgt
        have hy_ge : a + 2 ^ (p + 1) - 1 ≤ y := by omega
        let M : ℕ := a + 2 ^ p - 1
        have haM : a < M := by
          have : 2 ≤ 2 ^ p := by
            calc
              2 = 2 ^ 1 := by decide
              _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp1
          omega
        have hMy : M < y := by
          have : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [pow_succ]; omega
          omega
        have hex_hi : ∃ t, t ≤ L ∧ ((W t).filter (fun z => M ≤ z)).Nonempty :=
          ⟨L, le_refl L, ⟨y, Finset.mem_filter.mpr ⟨hy, by omega⟩⟩⟩
        classical
        let t1 := Nat.find hex_hi
        have ht1_spec := Nat.find_spec hex_hi
        have ht1_le : t1 ≤ L := ht1_spec.1
        have ht1_ne : ((W t1).filter (fun z => M ≤ z)).Nonempty := ht1_spec.2
        have ht1_pos : 0 < t1 := by
          by_contra h0
          have hz : t1 = 0 := by omega
          rw [hz, hW0] at ht1_ne
          simp at ht1_ne
        have ht1_prev : (W (t1 - 1)).filter (fun z => M ≤ z) = ∅ := by
          have hmin := Nat.find_min hex_hi (show t1 - 1 < t1 by omega)
          by_contra hne
          exact hmin ⟨by omega, Finset.nonempty_iff_ne_empty.mpr hne⟩
        have ht1_hi_empty : (W t1).filter (fun z => M + 1 ≤ z) = ∅ := by
          have hstep := hW (t1 - 1) (by omega)
          rw [show t1 - 1 + 1 = t1 by omega] at hstep
          rcases hstep with ⟨_, _, _, _, heq | ⟨j, hja, hpre, hST⟩⟩
          · rw [← heq] at ht1_ne
            rw [ht1_prev] at ht1_ne
            simp at ht1_ne
          · rcases hST with hT | hS
            · have hjM : M ≤ j := by
                rcases ht1_ne with ⟨z, hz⟩
                have hzW : z ∈ W t1 := (Finset.mem_filter.mp hz).1
                have hzM : M ≤ z := (Finset.mem_filter.mp hz).2
                rw [hT] at hzW
                rcases Finset.mem_insert.mp hzW with rfl | hprev
                · exact hzM
                · exfalso
                  have hmem : z ∈ (W (t1 - 1)).filter (fun u => M ≤ u) :=
                    Finset.mem_filter.mpr ⟨hprev, hzM⟩
                  rw [ht1_prev] at hmem
                  exact Finset.notMem_empty z hmem
              have hj_eq : j = M := by
                rcases hpre with rfl | hjm
                · omega
                · have hltM : j - 1 < M := by
                    by_contra hge
                    have hmem : j - 1 ∈ (W (t1 - 1)).filter (fun u => M ≤ u) :=
                      Finset.mem_filter.mpr ⟨hjm, by omega⟩
                    rw [ht1_prev] at hmem
                    exact Finset.notMem_empty _ hmem
                  omega
              ext z
              simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
              intro hzW hzM1
              rw [hT, hj_eq] at hzW
              rcases Finset.mem_insert.mp hzW with rfl | hprev
              · omega
              · have hmem : z ∈ (W (t1 - 1)).filter (fun u => M ≤ u) :=
                  Finset.mem_filter.mpr ⟨hprev, by omega⟩
                rw [ht1_prev] at hmem
                exact Finset.notMem_empty z hmem
            · exfalso
              rcases ht1_ne with ⟨z, hz⟩
              have hzW : z ∈ W t1 := (Finset.mem_filter.mp hz).1
              have hzM : M ≤ z := (Finset.mem_filter.mp hz).2
              have hprev : z ∈ W (t1 - 1) := by rw [hS]; exact Finset.mem_insert_of_mem hzW
              have hmem : z ∈ (W (t1 - 1)).filter (fun u => M ≤ u) :=
                Finset.mem_filter.mpr ⟨hprev, hzM⟩
              rw [ht1_prev] at hmem
              exact Finset.notMem_empty z hmem
        by_cases hlow_all : ∀ t, t1 ≤ t → t ≤ L → ((W t).filter (fun z => z ≤ M)).Nonempty
        · let T : ℕ → Finset ℕ := fun i => (W (t1 + i)).filter (fun z => M + 1 ≤ z)
          have hT0 : T 0 = ∅ := by simpa [T] using ht1_hi_empty
          have hT_walk : ValidWalk p (M + 1) (L - t1) T := by
            intro i hi
            have hstep := hW (t1 + i) (by omega)
            have hne1 := hlow_all (t1 + i) (by omega) (by omega)
            have hne2 := hlow_all (t1 + i + 1) (by omega) (by omega)
            have hcard1 : (T i).card ≤ p := by
              have htot := Finset.card_filter_add_card_filter_not (s := W (t1 + i)) (p := fun z => z ≤ M)
              have hneg : (W (t1 + i)).filter (fun z => ¬ z ≤ M) = T i := by
                ext z; simp only [T, Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
              rw [hneg] at htot
              have hpos := Finset.card_pos.mpr hne1
              have hle := hstep.1
              omega
            have hcard2 : (T (i + 1)).card ≤ p := by
              have htot := Finset.card_filter_add_card_filter_not (s := W (t1 + i + 1)) (p := fun z => z ≤ M)
              have hneg : (W (t1 + i + 1)).filter (fun z => ¬ z ≤ M) = T (i + 1) := by
                ext z; simp only [T, Finset.mem_filter, show t1 + (i + 1) = t1 + i + 1 by omega]
                constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
              rw [hneg] at htot
              have hpos := Finset.card_pos.mpr hne2
              have hle := hstep.2.1
              omega
            refine ⟨hcard1, hcard2, fun z hz => (Finset.mem_filter.mp hz).2,
              fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
            rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
            · left; simp only [T, show t1 + (i + 1) = t1 + i + 1 by omega, heq]
            · by_cases hjM1 : M + 1 ≤ j
              · right
                refine ⟨j, hjM1, ?_, ?_⟩
                · by_cases hjeq : j = M + 1
                  · exact Or.inl hjeq
                  · right
                    rcases hpre with rfl | hjm
                    · omega
                    · exact Finset.mem_filter.mpr ⟨hjm, by omega⟩
                · rcases hST with hT' | hS'
                  · left; ext z
                    simp only [T, show t1 + (i + 1) = t1 + i + 1 by omega, hT',
                      Finset.mem_filter, Finset.mem_insert]
                    constructor
                    · rintro ⟨rfl | hmem, hz⟩
                      · exact Or.inl rfl
                      · exact Or.inr ⟨hmem, hz⟩
                    · rintro (rfl | ⟨hmem, hz⟩)
                      · exact ⟨Or.inl rfl, hjM1⟩
                      · exact ⟨Or.inr hmem, hz⟩
                  · right; ext z
                    simp only [T, show t1 + (i + 1) = t1 + i + 1 by omega, hS',
                      Finset.mem_filter, Finset.mem_insert]
                    constructor
                    · rintro ⟨rfl | hmem, hz⟩
                      · exact Or.inl rfl
                      · exact Or.inr ⟨hmem, hz⟩
                    · rintro (rfl | ⟨hmem, hz⟩)
                      · exact ⟨Or.inl rfl, hjM1⟩
                      · exact ⟨Or.inr hmem, hz⟩
              · left; ext z
                simp only [T, show t1 + (i + 1) = t1 + i + 1 by omega, Finset.mem_filter]
                rcases hST with hT' | hS'
                · rw [hT']; simp only [Finset.mem_insert]
                  constructor
                  · rintro ⟨hmem, hz⟩; exact ⟨Or.inr hmem, hz⟩
                  · rintro ⟨rfl | hmem, hz⟩
                    · omega
                    · exact ⟨hmem, hz⟩
                · rw [hS']; simp only [Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | hmem, hz⟩
                    · omega
                    · exact ⟨hmem, hz⟩
                  · rintro ⟨hmem, hz⟩; exact ⟨Or.inr hmem, hz⟩
          have hyT : y ∈ T (L - t1) := by
            dsimp only [T]
            rw [show t1 + (L - t1) = L by omega]
            exact Finset.mem_filter.mpr ⟨hy, by omega⟩
          have hbd := ihp hp1 (L - t1) (M + 1) T hT_walk hT0 y hyT
          have hpow : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [pow_succ]; omega
          omega
        · push Not at hlow_all
          rcases hlow_all with ⟨t2, ht12, ht2L, ht2_low_empty⟩
          by_cases ht2_hi : ((W t2).filter (fun z => M + 1 ≤ z)).Nonempty
          · let S_empty : Finset ℕ := (Finset.range (t2 + 1)).filter
              (fun t => t1 ≤ t ∧ (W t).filter (fun z => M + 1 ≤ z) = ∅)
            have hS_ne : S_empty.Nonempty :=
              ⟨t1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_refl t1, ht1_hi_empty⟩⟩
            let tstar := S_empty.max' hS_ne
            have htstar_mem := Finset.mem_filter.mp (Finset.max'_mem S_empty hS_ne)
            have htstar_le : tstar ≤ t2 := by
              have := Finset.mem_range.mp htstar_mem.1; omega
            have htstar_ge : t1 ≤ tstar := htstar_mem.2.1
            have htstar_empty : (W tstar).filter (fun z => M + 1 ≤ z) = ∅ := htstar_mem.2.2
            have htstar_lt : tstar < t2 := by
              by_contra hge
              have heq : tstar = t2 := by omega
              rw [heq] at htstar_empty
              rw [htstar_empty] at ht2_hi
              simp at ht2_hi
            have hhi_all : ∀ t, tstar + 1 ≤ t → t ≤ t2 → ((W t).filter (fun z => M + 1 ≤ z)).Nonempty := by
              intro t ht1' ht2'
              by_contra hemp
              rw [Finset.not_nonempty_iff_eq_empty] at hemp
              have hmem : t ∈ S_empty :=
                Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hemp⟩
              have hle := Finset.le_max' S_empty t hmem
              omega
            have hM_in : M ∈ W (tstar + 1) := by
              have hne1 := hhi_all (tstar + 1) (le_refl _) (by omega)
              have hstep := hW tstar (by omega)
              rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
              · rw [← heq] at hne1
                rw [htstar_empty] at hne1
                simp at hne1
              · rcases hST with hT | hS
                · have hjM1 : M + 1 ≤ j := by
                    rcases hne1 with ⟨z, hz⟩
                    have hzW := (Finset.mem_filter.mp hz).1
                    have hzM := (Finset.mem_filter.mp hz).2
                    rw [hT] at hzW
                    rcases Finset.mem_insert.mp hzW with rfl | hprev
                    · exact hzM
                    · exfalso
                      have hmem : z ∈ (W tstar).filter (fun u => M + 1 ≤ u) :=
                        Finset.mem_filter.mpr ⟨hprev, hzM⟩
                      rw [htstar_empty] at hmem
                      exact Finset.notMem_empty z hmem
                  have hj_eq : j = M + 1 := by
                    rcases hpre with rfl | hjm
                    · omega
                    · have hltM1 : j - 1 < M + 1 := by
                        by_contra hge
                        have hmem : j - 1 ∈ (W tstar).filter (fun u => M + 1 ≤ u) :=
                          Finset.mem_filter.mpr ⟨hjm, by omega⟩
                        rw [htstar_empty] at hmem
                        exact Finset.notMem_empty _ hmem
                      omega
                  rcases hpre with rfl | hjm
                  · omega
                  · rw [hj_eq, Nat.add_sub_cancel] at hjm
                    rw [hT]
                    exact Finset.mem_insert_of_mem hjm
                · exfalso
                  rcases hne1 with ⟨z, hz⟩
                  have hzW := (Finset.mem_filter.mp hz).1
                  have hzM := (Finset.mem_filter.mp hz).2
                  have hprev : z ∈ W tstar := by rw [hS]; exact Finset.mem_insert_of_mem hzW
                  have hmem : z ∈ (W tstar).filter (fun u => M + 1 ≤ u) :=
                    Finset.mem_filter.mpr ⟨hprev, hzM⟩
                  rw [htstar_empty] at hmem
                  exact Finset.notMem_empty z hmem
            let R : ℕ → Finset ℕ := fun i => (W (tstar + 1 + i)).filter (fun z => z ≤ M)
            have hR_walk : ValidWalk p a (t2 - (tstar + 1)) R := by
              intro i hi
              have hstep := hW (tstar + 1 + i) (by omega)
              have hne1 := hhi_all (tstar + 1 + i) (by omega) (by omega)
              have hne2 := hhi_all (tstar + 1 + i + 1) (by omega) (by omega)
              have hcard1 : (R i).card ≤ p := by
                have htot := Finset.card_filter_add_card_filter_not (s := W (tstar + 1 + i)) (p := fun z => z ≤ M)
                have hneg : (W (tstar + 1 + i)).filter (fun z => ¬ z ≤ M) =
                    (W (tstar + 1 + i)).filter (fun z => M + 1 ≤ z) := by
                  ext z; simp only [Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
                rw [hneg] at htot
                have hpos := Finset.card_pos.mpr hne1
                have hle := hstep.1
                dsimp only [R]
                omega
              have hcard2 : (R (i + 1)).card ≤ p := by
                have htot := Finset.card_filter_add_card_filter_not (s := W (tstar + 1 + i + 1)) (p := fun z => z ≤ M)
                have hneg : (W (tstar + 1 + i + 1)).filter (fun z => ¬ z ≤ M) =
                    (W (tstar + 1 + i + 1)).filter (fun z => M + 1 ≤ z) := by
                  ext z; simp only [Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
                rw [hneg] at htot
                have hpos := Finset.card_pos.mpr hne2
                have hle := hstep.2.1
                dsimp only [R]
                rw [show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega]
                omega
              refine ⟨hcard1, hcard2, fun z hz => hstep.2.2.1 z (Finset.mem_filter.mp hz).1,
                fun z hz => hstep.2.2.2.1 z (Finset.mem_filter.mp hz).1, ?_⟩
              rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
              · left; simp only [R, show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, heq]
              · by_cases hjM : j ≤ M
                · right
                  refine ⟨j, hja, ?_, ?_⟩
                  · rcases hpre with rfl | hjm
                    · exact Or.inl rfl
                    · exact Or.inr (Finset.mem_filter.mpr ⟨hjm, by omega⟩)
                  · rcases hST with hT' | hS'
                    · left; ext z
                      simp only [R, show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, hT',
                        Finset.mem_filter, Finset.mem_insert]
                      constructor
                      · rintro ⟨rfl | hmem, hz⟩
                        · exact Or.inl rfl
                        · exact Or.inr ⟨hmem, hz⟩
                      · rintro (rfl | ⟨hmem, hz⟩)
                        · exact ⟨Or.inl rfl, hjM⟩
                        · exact ⟨Or.inr hmem, hz⟩
                    · right; ext z
                      simp only [R, show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, hS',
                        Finset.mem_filter, Finset.mem_insert]
                      constructor
                      · rintro ⟨rfl | hmem, hz⟩
                        · exact Or.inl rfl
                        · exact Or.inr ⟨hmem, hz⟩
                      · rintro (rfl | ⟨hmem, hz⟩)
                        · exact ⟨Or.inl rfl, hjM⟩
                        · exact ⟨Or.inr hmem, hz⟩
                · left; ext z
                  simp only [R, show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, Finset.mem_filter]
                  rcases hST with hT' | hS'
                  · rw [hT']; simp only [Finset.mem_insert]
                    constructor
                    · rintro ⟨hmem, hz⟩; exact ⟨Or.inr hmem, hz⟩
                    · rintro ⟨rfl | hmem, hz⟩
                      · omega
                      · exact ⟨hmem, hz⟩
                  · rw [hS']; simp only [Finset.mem_insert]
                    constructor
                    · rintro ⟨rfl | hmem, hz⟩
                      · omega
                      · exact ⟨hmem, hz⟩
                    · rintro ⟨hmem, hz⟩; exact ⟨Or.inr hmem, hz⟩
            have hRrev := validWalk_reverse hR_walk
            have hRrev0 : R (t2 - (tstar + 1) - 0) = ∅ := by
              dsimp only [R]
              rw [Nat.sub_zero, show tstar + 1 + (t2 - (tstar + 1)) = t2 by omega]
              exact ht2_low_empty
            have hM_rev : M ∈ R (t2 - (tstar + 1) - (t2 - (tstar + 1))) := by
              rw [Nat.sub_self]
              exact Finset.mem_filter.mpr ⟨hM_in, le_refl M⟩
            have hbd := ihp hp1 (t2 - (tstar + 1)) a (fun i => R (t2 - (tstar + 1) - i)) hRrev hRrev0 M hM_rev
            omega
          · rw [Finset.not_nonempty_iff_eq_empty] at ht2_hi
            have hWt2_empty : W t2 = ∅ := by
              ext z
              simp only [Finset.notMem_empty, iff_false]
              intro hz
              by_cases hzM : z ≤ M
              · have hmem : z ∈ (W t2).filter (fun u => u ≤ M) := Finset.mem_filter.mpr ⟨hz, hzM⟩
                rw [ht2_low_empty] at hmem
                exact Finset.notMem_empty z hmem
              · have hmem : z ∈ (W t2).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hz, by omega⟩
                rw [ht2_hi] at hmem
                exact Finset.notMem_empty z hmem
            let W' : ℕ → Finset ℕ := fun i => W (t2 + i)
            have hW'_walk : ValidWalk (p + 1) a (L - t2) W' := fun i hi => by
              dsimp only [W']
              rw [show t2 + (i + 1) = t2 + i + 1 by omega]
              exact hW (t2 + i) (by omega)
            have hW'0 : W' 0 = ∅ := by simpa [W'] using hWt2_empty
            have hyW' : y ∈ W' (L - t2) := by
              dsimp only [W']; rw [show t2 + (L - t2) = L by omega]; exact hy
            have hbd := ihL (L - t2) (by omega) a W' hW'_walk hW'0 y hyW'
            omega

lemma validWalk_add_bg {p a L : ℕ} {W : ℕ → Finset ℕ} (B : Finset ℕ)
    (hBdisj : ∀ x ∈ B, x < a) (hW : ValidWalk p a L W) (hW0 : W 0 = ∅)
    (hBpre : a = 0 ∨ a - 1 ∈ B) (a0 : ℕ) (ha0 : a0 ≤ a) (hBa0 : ∀ x ∈ B, a0 ≤ x) :
    ValidWalk (B.card + p) a0 L (fun i => B ∪ W i) := by
  intro i hi
  have hstep := hW i hi
  have hdisj1 : Disjoint B (W i) := by
    rw [Finset.disjoint_left]
    intro x hxB hxW
    have h1 := hBdisj x hxB
    have h2 := hstep.2.2.1 x hxW
    omega
  have hdisj2 : Disjoint B (W (i + 1)) := by
    rw [Finset.disjoint_left]
    intro x hxB hxW
    have h1 := hBdisj x hxB
    have h2 := hstep.2.2.2.1 x hxW
    omega
  refine ⟨by rw [Finset.card_union_of_disjoint hdisj1]; have := hstep.1; omega,
    by rw [Finset.card_union_of_disjoint hdisj2]; have := hstep.2.1; omega,
    fun x hx => by
      rcases Finset.mem_union.mp hx with hB | hWi
      · exact hBa0 x hB
      · exact le_trans ha0 (hstep.2.2.1 x hWi),
    fun x hx => by
      rcases Finset.mem_union.mp hx with hB | hWi
      · exact hBa0 x hB
      · exact le_trans ha0 (hstep.2.2.2.1 x hWi), ?_⟩
  dsimp only
  rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
  · left; rw [heq]
  · right
    refine ⟨j, le_trans ha0 hja, ?_, ?_⟩
    · rcases hpre with rfl | hjm
      · rcases hBpre with rfl | hB1
        · exact Or.inl (by omega)
        · exact Or.inr (Finset.mem_union_left _ hB1)
      · exact Or.inr (Finset.mem_union_right _ hjm)
    · rcases hST with hT | hS
      · left; rw [hT, Finset.union_insert]
      · right; rw [hS, Finset.union_insert]

lemma pebble_singleton_upper : ∀ (p : ℕ), 1 ≤ p →
    ∀ (a t : ℕ), t < 2 ^ (p - 1) →
      ∃ (L : ℕ) (W : ℕ → Finset ℕ), ValidWalk p a L W ∧ W 0 = ∅ ∧ W L = {a + t} := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ihp =>
    intro _ a t ht
    by_cases hp0 : p = 0
    · subst hp0
      have ht0 : t = 0 := by simp at ht; omega
      subst ht0
      let W : ℕ → Finset ℕ := fun i => if i = 0 then ∅ else {a}
      refine ⟨1, W, ?_, by simp [W], by simp [W]⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [W, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      refine ⟨by simp, by simp, fun _ h => absurd h (Finset.notMem_empty _),
        fun z hz => by rw [Finset.mem_singleton.mp hz], Or.inr ⟨a, le_refl a, Or.inl rfl, Or.inl (by simp)⟩⟩
    · have hp1 : 1 ≤ p := by omega
      by_cases hsmall : t < 2 ^ (p - 1)
      · rcases ihp hp1 a t hsmall with ⟨L, W, hW, hW0, hWL⟩
        refine ⟨L, W, fun i hi => ?_, hW0, hWL⟩
        rcases hW i hi with ⟨h1, h2, h3, h4, h5⟩
        exact ⟨by omega, by omega, h3, h4, h5⟩
      · have hpow : 2 ^ p = 2 ^ (p - 1) + 2 ^ (p - 1) := by
          have : p = (p - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          omega
        let h : ℕ := 2 ^ (p - 1) - 1
        have hh : h < 2 ^ (p - 1) := by
          have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
          omega
        let t' : ℕ := t - (h + 1)
        have ht' : t' < 2 ^ (p - 1) := by
          simp only [Nat.add_sub_cancel] at ht
          omega
        rcases ihp hp1 a h hh with ⟨L1, W1, hW1, hW10, hW1L⟩
        rcases ihp hp1 (a + h + 1) t' ht' with ⟨L2, W2, hW2, hW20, hW2L⟩
        have hW1_lift : ValidWalk (p + 1) a L1 W1 := fun i hi => by
          rcases hW1 i hi with ⟨h1, h2, h3, h4, h5⟩
          exact ⟨by omega, by omega, h3, h4, h5⟩
        have hW2_bg : ValidWalk (p + 1) a L2 (fun i => {a + h} ∪ W2 i) := by
          have h := validWalk_add_bg ({a + h} : Finset ℕ) (fun x hx => by rw [Finset.mem_singleton.mp hx]; omega)
            hW2 hW20 (Or.inr (by simp)) a (by omega) (fun x hx => by rw [Finset.mem_singleton.mp hx]; omega)
          simpa [Nat.add_comm] using h
        have hW1_rev : ValidWalk p a L1 (fun i => W1 (L1 - i)) := validWalk_reverse hW1
        have hW1_rev_bg : ValidWalk (p + 1) a L1 (fun i => {a + t} ∪ W1 (L1 - i)) := by
          intro i hi
          have hstep := hW1_rev i hi
          have hcard1 : ({a + t} ∪ W1 (L1 - i)).card ≤ p + 1 := by
            have := Finset.card_union_le ({a + t} : Finset ℕ) (W1 (L1 - i))
            have := hstep.1
            simp at *
            omega
          have hcard2 : ({a + t} ∪ W1 (L1 - (i + 1))).card ≤ p + 1 := by
            have := Finset.card_union_le ({a + t} : Finset ℕ) (W1 (L1 - (i + 1)))
            have := hstep.2.1
            simp at *
            omega
          refine ⟨hcard1, hcard2,
            fun x hx => by
              rcases Finset.mem_union.mp hx with h1 | h2
              · rw [Finset.mem_singleton.mp h1]; omega
              · exact hstep.2.2.1 x h2,
            fun x hx => by
              rcases Finset.mem_union.mp hx with h1 | h2
              · rw [Finset.mem_singleton.mp h1]; omega
              · exact hstep.2.2.2.1 x h2, ?_⟩
          dsimp only
          dsimp only at hstep
          rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
          · left; rw [heq]
          · right
            refine ⟨j, hja, ?_, ?_⟩
            · rcases hpre with rfl | hjm
              · exact Or.inl rfl
              · exact Or.inr (Finset.mem_union_right _ hjm)
            · rcases hST with hT | hS
              · left; rw [hT, Finset.union_insert]
              · right; rw [hS, Finset.union_insert]
        have hmid1 : W1 L1 = {a + h} ∪ W2 0 := by rw [hW1L, hW20, Finset.union_empty]
        rcases validWalk_concat hW1_lift hW2_bg hmid1 with ⟨W12, hW12, hW12_0, hW12_L⟩
        have hmid2 : W12 (L1 + L2) = {a + t} ∪ W1 (L1 - 0) := by
          rw [hW12_L, hW2L, Nat.sub_zero, hW1L, show a + h + 1 + t' = a + t by omega, Finset.union_comm]
        rcases validWalk_concat hW12 hW1_rev_bg hmid2 with ⟨W123, hW123, hW123_0, hW123_L⟩
        refine ⟨L1 + L2 + L1, W123, hW123, by rw [hW123_0, hW12_0, hW10], ?_⟩
        rw [hW123_L, Nat.sub_self, hW10, Finset.union_empty]

lemma pebble_site_upper : ∀ (p : ℕ), 1 ≤ p →
    ∀ (a t : ℕ), t + 1 < 2 ^ p →
      ∃ (L : ℕ) (W : ℕ → Finset ℕ), ValidWalk p a L W ∧ W 0 = ∅ ∧ a + t ∈ W L := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ihp =>
    intro _ a t ht
    by_cases hp0 : p = 0
    · subst hp0
      have ht0 : t = 0 := by omega
      subst ht0
      rcases pebble_singleton_upper 1 (le_refl 1) a 0 (by decide) with ⟨L, W, hW, hW0, hWL⟩
      exact ⟨L, W, hW, hW0, by rw [hWL]; simp⟩
    · have hp1 : 1 ≤ p := by omega
      by_cases hsmall : t < 2 ^ p
      · rcases pebble_singleton_upper (p + 1) (by omega) a t (by simpa using hsmall) with ⟨L, W, hW, hW0, hWL⟩
        exact ⟨L, W, hW, hW0, by rw [hWL]; simp⟩
      · have hpow : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [pow_succ]; omega
        let h : ℕ := 2 ^ p - 1
        have hh : h < 2 ^ p := by
          have : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by omega)
          omega
        let t' : ℕ := t - (h + 1)
        have ht' : t' + 1 < 2 ^ p := by omega
        rcases pebble_singleton_upper (p + 1) (by omega) a h (by simpa using hh) with ⟨L1, W1, hW1, hW10, hW1L⟩
        rcases ihp hp1 (a + h + 1) t' ht' with ⟨L2, W2, hW2, hW20, hW2L⟩
        have hW2_bg : ValidWalk (p + 1) a L2 (fun i => {a + h} ∪ W2 i) := by
          have h := validWalk_add_bg ({a + h} : Finset ℕ) (fun x hx => by rw [Finset.mem_singleton.mp hx]; omega)
            hW2 hW20 (Or.inr (by simp)) a (by omega) (fun x hx => by rw [Finset.mem_singleton.mp hx]; omega)
          simpa [Nat.add_comm] using h
        have hmid : W1 L1 = {a + h} ∪ W2 0 := by rw [hW1L, hW20, Finset.union_empty]
        rcases validWalk_concat hW1 hW2_bg hmid with ⟨W12, hW12, hW12_0, hW12_L⟩
        refine ⟨L1 + L2, W12, hW12, by rw [hW12_0, hW10], ?_⟩
        rw [hW12_L]
        exact Finset.mem_union_right _ (by simpa [show a + h + 1 + t' = a + t by omega] using hW2L)

def multilin {m : ℕ} (f : MvPolynomial (Fin m) F) : Finset (Fin m) → F :=
  fun S => ∑ α ∈ f.support.filter (fun α => α.support = S), f.coeff α

lemma multilin_eq_sum_support {m : ℕ} (f : MvPolynomial (Fin m) F) (S : Finset (Fin m)) :
    multilin f S = ∑ α ∈ f.support, if α.support = S then f.coeff α else 0 := by
  unfold multilin
  rw [Finset.sum_filter]

lemma multilin_add {m : ℕ} (f g : MvPolynomial (Fin m) F) (S : Finset (Fin m)) :
    multilin (f + g) S = multilin f S + multilin g S := by
  let U : Finset (Fin m →₀ ℕ) := f.support ∪ g.support
  have hU : ∀ h : MvPolynomial (Fin m) F, h.support ⊆ U →
      multilin h S = ∑ α ∈ U, if α.support = S then h.coeff α else 0 := by
    intro h hsub
    rw [multilin_eq_sum_support]
    refine Finset.sum_subset hsub fun α _ hnot => ?_
    have hc0 : h.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hnot
    simp [hc0]
  rw [hU (f + g) MvPolynomial.support_add, hU f Finset.subset_union_left,
    hU g Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · exact mv_coeff_add α f g
  · simp

lemma multilin_zero {m : ℕ} (S : Finset (Fin m)) : multilin (0 : MvPolynomial (Fin m) F) S = 0 := by
  simp [multilin]

lemma multilin_sum {ι : Type*} {m : ℕ} (s : Finset ι) (f : ι → MvPolynomial (Fin m) F) (S : Finset (Fin m)) :
    multilin (∑ i ∈ s, f i) S = ∑ i ∈ s, multilin (f i) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multilin_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, multilin_add, ih]

lemma multilin_monomial {m : ℕ} (α : Fin m →₀ ℕ) (c : F) (S : Finset (Fin m)) :
    multilin (MvPolynomial.monomial α c) S = if α.support = S then c else 0 := by
  by_cases hc : c = 0
  · subst hc; simp [multilin_zero]
  · simp [multilin_eq_sum_support, MvPolynomial.support_monomial, hc, MvPolynomial.coeff_monomial]

lemma multilin_one {m : ℕ} (S : Finset (Fin m)) :
    multilin (1 : MvPolynomial (Fin m) F) S = if S = ∅ then 1 else 0 := by
  have h1 : (1 : MvPolynomial (Fin m) F) = MvPolynomial.monomial 0 1 := rfl
  rw [h1, multilin_monomial]
  by_cases hS : S = ∅
  · subst hS; simp
  · simp [Finsupp.support_zero, hS, Ne.symm hS]

lemma multilin_mul_bool_axiom {m : ℕ} (f : MvPolynomial (Fin m) F) (k : Fin m) (S : Finset (Fin m)) :
    multilin (f * (MvPolynomial.X k * MvPolynomial.X k + MvPolynomial.X k)) S = 0 := by
  rw [MvPolynomial.as_sum f, Finset.sum_mul, multilin_sum]
  refine Finset.sum_eq_zero fun α _ => ?_
  have hX : (MvPolynomial.X k : MvPolynomial (Fin m) F) * MvPolynomial.X k =
      MvPolynomial.monomial (Finsupp.single k 2) 1 := by
    simp [MvPolynomial.X, ← Finsupp.single_add]
  have hX1 : (MvPolynomial.X k : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single k 1) 1 := rfl
  rw [mul_add, hX, hX1, MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial, mul_one,
    multilin_add, multilin_monomial, multilin_monomial]
  have hsupp : (α + Finsupp.single k 2).support = (α + Finsupp.single k 1).support := by
    ext j
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj]
  rw [hsupp]
  split_ifs
  · exact zmod2_add_self _
  · simp

lemma multilin_eval_linear_on_component {m d : ℕ} (hd : 2 ≤ d) (hm : 0 < m)
    (R : Finset (Finset (Fin m)))
    (hR0 : ∀ S : Finset (Fin m), S.card ≤ d - 2 → (⟨0, hm⟩ : Fin m) ∉ S →
      (S ∈ R ↔ insert ⟨0, hm⟩ S ∈ R))
    (hR_int : ∀ (k : Fin m) (hk : k.val + 1 < m) (T : Finset (Fin m)),
      T.card ≤ d - 1 → k ∈ T → ⟨k.val + 1, hk⟩ ∉ T →
      (T ∈ R ↔ insert ⟨k.val + 1, hk⟩ T ∈ R))
    (hR_sink : ∀ T : Finset (Fin m), T.card ≤ d - 1 → ∀ (_hm' : 0 < m), ⟨m - 1, by omega⟩ ∈ T → T ∉ R)
    (A B : MvPolynomial (Fin m) F)
    (hA : A = 0 ∨ A.totalDegree ≤ d - 2)
    (hB : B = 0 ∨ B.totalDegree ≤ d - 2)
    (Q : Fin (m - 1) → MvPolynomial (Fin m) F)
    (hQ : ∀ k : Fin (m - 1), Q k = 0 ∨ (Q k).totalDegree ≤ d - 2)
    (G : Fin m → MvPolynomial (Fin m) F) :
    (∑ S ∈ R, multilin (A * (1 + MvPolynomial.X ⟨0, hm⟩) +
      (∑ k : Fin (m - 1), Q k * (MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩))) +
      B * MvPolynomial.X ⟨m - 1, by omega⟩ +
      ∑ v : Fin m, G v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) S) = 0 := by
  have hlin_mon : ∀ (f : MvPolynomial (Fin m) F) (h : MvPolynomial (Fin m) F),
      (∀ α ∈ f.support, (∑ S ∈ R, multilin (MvPolynomial.monomial α (f.coeff α) * h) S) = 0) →
      (∑ S ∈ R, multilin (f * h) S) = 0 := by
    intro f h hall
    rw [MvPolynomial.as_sum f, Finset.sum_mul]
    simp_rw [multilin_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero hall
  have h1 : (∑ S ∈ R, multilin (A * (1 + MvPolynomial.X ⟨0, hm⟩)) S) = 0 := by
    rcases hA with rfl | hAdeg
    · simp [multilin_zero]
    · refine hlin_mon A _ fun α hα => ?_
      have hcard : α.support.card ≤ d - 2 := by
        have hle := MvPolynomial.le_totalDegree hα
        have hsc : α.support.card ≤ α.sum (fun _ e => e) := by
          rw [Finset.card_eq_sum_ones, Finsupp.sum]
          refine Finset.sum_le_sum fun v hv => ?_
          have hne : α v ≠ 0 := Finsupp.mem_support_iff.mp hv
          omega
        omega
      have hX0 : (MvPolynomial.X ⟨0, hm⟩ : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single ⟨0, hm⟩ 1) 1 := rfl
      rw [mul_add, mul_one, hX0, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_add, multilin_monomial]
      rw [Finset.sum_add_distrib]
      have hsupp : (α + Finsupp.single (⟨0, hm⟩ : Fin m) 1).support = insert ⟨0, hm⟩ α.support := by
        ext v
        simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
        by_cases hv : (⟨0, hm⟩ : Fin m) = v
        · subst hv; simp
        · simp [hv, Ne.symm hv]
      rw [hsupp]
      have hsum_single : ∀ T : Finset (Fin m),
          (∑ S ∈ R, if T = S then A.coeff α else 0) = if T ∈ R then A.coeff α else 0 := by
        intro T
        by_cases hTR : T ∈ R
        · rw [Finset.sum_eq_single T]
          · simp [hTR]
          · intro S _ hne; simp [Ne.symm hne]
          · intro h; exact absurd hTR h
        · rw [Finset.sum_eq_zero]
          · simp [hTR]
          · intro S hSR; have hne : T ≠ S := fun h => hTR (h ▸ hSR); simp [hne]
      rw [hsum_single α.support, hsum_single (insert ⟨0, hm⟩ α.support)]
      by_cases h0 : (⟨0, hm⟩ : Fin m) ∈ α.support
      · rw [Finset.insert_eq_of_mem h0]; split_ifs <;> simp [zmod2_add_self]
      · have hiff := hR0 α.support hcard h0
        by_cases hmem : α.support ∈ R
        · simp [hmem, hiff.mp hmem, zmod2_add_self]
        · have hnot : insert ⟨0, hm⟩ α.support ∉ R := fun h => hmem (hiff.mpr h)
          simp [hmem, hnot]
  have h2 : ∀ k : Fin (m - 1),
      (∑ S ∈ R, multilin (Q k * (MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩))) S) = 0 := by
    intro k
    rcases hQ k with hQ0 | hQdeg
    · rw [hQ0]; simp [multilin_zero]
    · refine hlin_mon (Q k) _ fun α hα => ?_
      have hcard : α.support.card ≤ d - 2 := by
        have hle := MvPolynomial.le_totalDegree hα
        have hsc : α.support.card ≤ α.sum (fun _ e => e) := by
          rw [Finset.card_eq_sum_ones, Finsupp.sum]
          refine Finset.sum_le_sum fun v hv => ?_
          have hne : α v ≠ 0 := Finsupp.mem_support_iff.mp hv
          omega
        omega
      let k0 : Fin m := ⟨k.val, by omega⟩
      let k1 : Fin m := ⟨k.val + 1, by omega⟩
      have hX0 : (MvPolynomial.X k0 : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single k0 1) 1 := rfl
      have hX1 : (MvPolynomial.X k1 : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single k1 1) 1 := rfl
      rw [mul_add, mul_one, mul_add, ← mul_assoc, hX0, MvPolynomial.monomial_mul_monomial, mul_one,
        hX1, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_add, multilin_monomial]
      rw [Finset.sum_add_distrib]
      let T : Finset (Fin m) := insert k0 α.support
      have hsupp1 : (α + Finsupp.single k0 1).support = T := by
        ext v
        simp only [T, Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
        by_cases hv : k0 = v
        · subst hv; simp
        · simp [hv, Ne.symm hv]
      have hsupp2 : (α + Finsupp.single k0 1 + Finsupp.single k1 1).support = insert k1 T := by
        ext v
        simp only [← hsupp1, Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
        by_cases hv : k1 = v
        · subst hv; simp
        · simp [hv, Ne.symm hv]
      rw [hsupp1, hsupp2]
      have hsum_single : ∀ U : Finset (Fin m),
          (∑ S ∈ R, if U = S then (Q k).coeff α else 0) = if U ∈ R then (Q k).coeff α else 0 := by
        intro U
        by_cases hUR : U ∈ R
        · rw [Finset.sum_eq_single U]
          · simp [hUR]
          · intro S _ hne; simp [Ne.symm hne]
          · intro h; exact absurd hUR h
        · rw [Finset.sum_eq_zero]
          · simp [hUR]
          · intro S hSR; have hne : U ≠ S := fun h => hUR (h ▸ hSR); simp [hne]
      rw [hsum_single T, hsum_single (insert k1 T)]
      by_cases hk1 : k1 ∈ T
      · rw [Finset.insert_eq_of_mem hk1]; split_ifs <;> simp [zmod2_add_self]
      · have hTcard : T.card ≤ d - 1 := by
          dsimp only [T]
          have := Finset.card_insert_le k0 α.support
          omega
        have hk0T : k0 ∈ T := Finset.mem_insert_self k0 _
        have hiff := hR_int k0 (by dsimp only [k0]; omega) T hTcard hk0T hk1
        have hk1_eq : (⟨k0.val + 1, by dsimp only [k0]; omega⟩ : Fin m) = k1 := rfl
        rw [hk1_eq] at hiff
        by_cases hmem : T ∈ R
        · simp [hmem, hiff.mp hmem, zmod2_add_self]
        · have hnot : insert k1 T ∉ R := fun h => hmem (hiff.mpr h)
          simp [hmem, hnot]
  have h3 : (∑ S ∈ R, multilin (B * MvPolynomial.X ⟨m - 1, by omega⟩) S) = 0 := by
    rcases hB with rfl | hBdeg
    · simp [multilin_zero]
    · refine hlin_mon B _ fun α hα => ?_
      have hcard : α.support.card ≤ d - 2 := by
        have hle := MvPolynomial.le_totalDegree hα
        have hsc : α.support.card ≤ α.sum (fun _ e => e) := by
          rw [Finset.card_eq_sum_ones, Finsupp.sum]
          refine Finset.sum_le_sum fun v hv => ?_
          have hne : α v ≠ 0 := Finsupp.mem_support_iff.mp hv
          omega
        omega
      let km : Fin m := ⟨m - 1, by omega⟩
      have hXm : (MvPolynomial.X km : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single km 1) 1 := rfl
      rw [hXm, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_monomial]
      have hsupp : (α + Finsupp.single km 1).support = insert km α.support := by
        ext v
        simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
        by_cases hv : km = v
        · subst hv; simp
        · simp [hv, Ne.symm hv]
      rw [hsupp]
      have hTcard : (insert km α.support).card ≤ d - 1 := by
        have := Finset.card_insert_le km α.support
        omega
      have hnotR : insert km α.support ∉ R := hR_sink _ hTcard hm (Finset.mem_insert_self km _)
      refine Finset.sum_eq_zero fun S hSR => ?_
      have hne : insert km α.support ≠ S := fun h => hnotR (h ▸ hSR)
      simp [hne]
  have h4 : (∑ S ∈ R, multilin (∑ v : Fin m, G v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) S) = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [multilin_sum]
    exact Finset.sum_eq_zero fun v _ => multilin_mul_bool_axiom (G v) v S
  simp_rw [multilin_add, multilin_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    h1, zero_add, Finset.sum_comm, Finset.sum_eq_zero fun k _ => h2 k, zero_add, h3, zero_add]
  simpa [multilin_sum] using h4

lemma totalDegree_finset_sum_le {ι V : Type*} (s : Finset ι) (f : ι → MvPolynomial V F) :
    (∑ i ∈ s, f i).totalDegree ≤ s.sup (fun i => (f i).totalDegree) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le (le_max_left _ _) (le_trans ih (le_max_right _ _)))

lemma totalDegree_finset_prod_le {ι V : Type*} (s : Finset ι) (f : ι → MvPolynomial V F) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add_left ih _)

lemma eval2Hom_totalDegree_le {V W : Type*} (f : V → MvPolynomial W F)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (p : MvPolynomial V F) :
    (MvPolynomial.eval₂Hom MvPolynomial.C f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p, map_sum]
  refine le_trans (totalDegree_finset_sum_le _ _) ?_
  rw [Finset.sup_le_iff]
  intro α hα
  rw [MvPolynomial.eval₂Hom_monomial]
  have h1 : (MvPolynomial.C (p.coeff α) * α.prod fun v e => f v ^ e).totalDegree ≤
      (α.prod fun v e => f v ^ e).totalDegree := by
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (by simp [MvPolynomial.totalDegree_C])
  have h2 : (α.prod fun v e => f v ^ e).totalDegree ≤ α.sum (fun _ e => e) := by
    rw [Finsupp.prod, Finsupp.sum]
    refine le_trans (totalDegree_finset_prod_le _ _) ?_
    refine Finset.sum_le_sum fun v _ => ?_
    exact le_trans (MvPolynomial.totalDegree_pow _ _) (by have := hf v; nlinarith)
  exact le_trans h1 (le_trans h2 (MvPolynomial.le_totalDegree hα))

lemma prod_X_totalDegree {n : ℕ} (S : Finset (Fin n)) :
    (∏ v ∈ S, (MvPolynomial.X v : MvPolynomial (Fin n) F)).totalDegree ≤ S.card := by
  classical
  refine le_trans (totalDegree_finset_prod_le _ _) ?_
  calc
    (∑ v ∈ S, (MvPolynomial.X v : MvPolynomial (Fin n) F).totalDegree)
        ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum fun v _ => by simp [MvPolynomial.totalDegree_X]
    _ = S.card := by simp

noncomputable def liftFin {m : ℕ} (S : Finset (Fin m)) : Finset ℕ :=
  S.image (fun k => k.val + 1)

noncomputable def reachSet (m d : ℕ) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter fun S =>
    ∃ (L : ℕ) (W : ℕ → Finset ℕ), ValidWalk d 0 L W ∧ W 0 = ∅ ∧ W L = liftFin S

lemma reachSet_empty (m d : ℕ) : (∅ : Finset (Fin m)) ∈ reachSet m d := by
  classical
  unfold reachSet
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, fun _ => ∅, fun i hi => by omega, rfl, by simp [liftFin]⟩

lemma liftFin_card {m : ℕ} (S : Finset (Fin m)) : (liftFin S).card = S.card :=
  Finset.card_image_of_injective S (fun a b h => Fin.ext (by omega))

lemma liftFin_insert {m : ℕ} (k : Fin m) (S : Finset (Fin m)) :
    liftFin (insert k S) = insert (k.val + 1) (liftFin S) :=
  Finset.image_insert _ _ _

lemma reachSet_step0 {m d : ℕ} (hd : 2 ≤ d) (hm : 0 < m)
    (S : Finset (Fin m)) (hSc : S.card ≤ d - 2) (_h0not : (⟨0, hm⟩ : Fin m) ∉ S) :
    S ∈ reachSet m d ↔ insert ⟨0, hm⟩ S ∈ reachSet m d := by
  classical
  have hstep3 : ∃ W : ℕ → Finset ℕ, ValidWalk d 0 3 W ∧ W 0 = liftFin S ∧ W 3 = liftFin (insert ⟨0, hm⟩ S) := by
    let A0 := liftFin S
    let A1 := insert 0 A0
    let A2 := insert 1 A1
    let A3 := insert 1 A0
    let W : ℕ → Finset ℕ := fun i => if i = 0 then A0 else if i = 1 then A1 else if i = 2 then A2 else A3
    have hA0c : A0.card ≤ d - 2 := by rw [liftFin_card]; exact hSc
    have hA1c : A1.card ≤ d - 1 := by
      dsimp only [A1]; have := Finset.card_insert_le 0 A0; omega
    have hA2c : A2.card ≤ d := by
      dsimp only [A2]; have := Finset.card_insert_le 1 A1; omega
    have hA3c : A3.card ≤ d - 1 := by
      dsimp only [A3]; have := Finset.card_insert_le 1 A0; omega
    have hA2_eq : A2 = insert 0 A3 := by
      dsimp only [A2, A1, A3]; exact Finset.insert_comm 1 0 A0
    refine ⟨W, ?_, by simp [W, A0], by simp [W, A3, A0, liftFin_insert]⟩
    intro i hi
    interval_cases i
    · simp only [W, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      exact ⟨by omega, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
        Or.inr ⟨0, le_refl 0, Or.inl rfl, Or.inl rfl⟩⟩
    · simp only [W, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, show (2 : ℕ) ≠ 0 by decide,
        show (2 : ℕ) ≠ 1 by decide]
      exact ⟨by omega, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
        Or.inr ⟨1, by omega, Or.inr (Finset.mem_insert_self 0 A0), Or.inl rfl⟩⟩
    · simp only [W, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
        show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide]
      exact ⟨by omega, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
        Or.inr ⟨0, le_refl 0, Or.inl rfl, Or.inr hA2_eq⟩⟩
  rcases hstep3 with ⟨W3, hW3, hW30, hW33⟩
  unfold reachSet
  constructor
  · intro hSR
    rcases (Finset.mem_filter.mp hSR).2 with ⟨L, W, hW, hW0, hWL⟩
    rcases validWalk_concat hW hW3 (hWL.trans hW30.symm) with ⟨W', hW', hW'0, hW'L⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L + 3, W', hW', hW'0.trans hW0, hW'L.trans hW33⟩
  · intro hSR
    rcases (Finset.mem_filter.mp hSR).2 with ⟨L, W, hW, hW0, hWL⟩
    have hW3rev := validWalk_reverse hW3
    rcases validWalk_concat hW hW3rev (hWL.trans (by simpa using hW33.symm)) with ⟨W', hW', hW'0, hW'L⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L + 3, W', hW', hW'0.trans hW0,
      hW'L.trans (by simpa using hW30)⟩

lemma reachSet_step_int {m d : ℕ} (hd : 1 ≤ d) (k : Fin m) (hk : k.val + 1 < m) (T : Finset (Fin m))
    (hTc : T.card ≤ d - 1) (hkT : k ∈ T) (_hk1not : ⟨k.val + 1, hk⟩ ∉ T) :
    T ∈ reachSet m d ↔ insert ⟨k.val + 1, hk⟩ T ∈ reachSet m d := by
  classical
  have hstep1 : RevStep d 0 (liftFin T) (liftFin (insert ⟨k.val + 1, hk⟩ T)) := by
    rw [liftFin_insert]
    have h1 : (liftFin T).card ≤ d := by rw [liftFin_card]; omega
    have h2 : (insert (k.val + 1 + 1) (liftFin T)).card ≤ d := by
      have := Finset.card_insert_le (k.val + 1 + 1) (liftFin T)
      rw [liftFin_card] at this; omega
    refine ⟨h1, h2, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
      Or.inr ⟨k.val + 2, by omega, Or.inr ?_, Or.inl rfl⟩⟩
    exact Finset.mem_image.mpr ⟨k, hkT, rfl⟩
  let W1 : ℕ → Finset ℕ := fun i => if i = 0 then liftFin T else liftFin (insert ⟨k.val + 1, hk⟩ T)
  have hW1 : ValidWalk d 0 1 W1 := fun i hi => by
    have hi0 : i = 0 := by omega
    subst hi0; simpa [W1] using hstep1
  unfold reachSet
  constructor
  · intro hTR
    rcases (Finset.mem_filter.mp hTR).2 with ⟨L, W, hW, hW0, hWL⟩
    rcases validWalk_concat hW hW1 (by simpa [W1] using hWL) with ⟨W', hW', hW'0, hW'L⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L + 1, W', hW', hW'0.trans hW0, by simpa [W1] using hW'L⟩
  · intro hTR
    rcases (Finset.mem_filter.mp hTR).2 with ⟨L, W, hW, hW0, hWL⟩
    have hW1rev := validWalk_reverse hW1
    rcases validWalk_concat hW hW1rev (by simpa [W1] using hWL) with ⟨W', hW', hW'0, hW'L⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L + 1, W', hW', hW'0.trans hW0, by simpa [W1] using hW'L⟩

lemma reachSet_sink {m d : ℕ} (hd : 1 ≤ d) (hnot_lt : ¬ (m + 2 < 2 ^ d))
    (T : Finset (Fin m)) (hTc : T.card ≤ d - 1) (hm : 0 < m)
    (hlast : ⟨m - 1, by omega⟩ ∈ T) : T ∉ reachSet m d := by
  classical
  unfold reachSet
  intro hTR
  rcases (Finset.mem_filter.mp hTR).2 with ⟨L, W, hW, hW0, hWL⟩
  have hstep_end : RevStep d 0 (liftFin T) (insert (m + 1) (liftFin T)) := by
    have h1 : (liftFin T).card ≤ d := by rw [liftFin_card]; omega
    have h2 : (insert (m + 1) (liftFin T)).card ≤ d := by
      have := Finset.card_insert_le (m + 1) (liftFin T)
      rw [liftFin_card] at this; omega
    refine ⟨h1, h2, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
      Or.inr ⟨m + 1, by omega, Or.inr ?_, Or.inl rfl⟩⟩
    exact Finset.mem_image.mpr ⟨⟨m - 1, by omega⟩, hlast, by dsimp; omega⟩
  let Wend : ℕ → Finset ℕ := fun i => if i = 0 then liftFin T else insert (m + 1) (liftFin T)
  have hWend : ValidWalk d 0 1 Wend := fun i hi => by
    have hi0 : i = 0 := by omega
    subst hi0; simpa [Wend] using hstep_end
  rcases validWalk_concat hW hWend (by simpa [Wend] using hWL) with ⟨W', hW', hW'0, hW'L⟩
  have hlen_in : m + 1 ∈ W' (L + 1) := by rw [hW'L]; simp [Wend]
  have hbd := pebble_reach_bound d hd (L + 1) 0 W' hW' (hW'0.trans hW0) (m + 1) hlen_in
  omega

end PEqualNP.Outside.L_pcx_244_aux

open PEqualNP.Outside.L_pcx_244_aux
open PEqualNP.ProofComplexity

theorem PEqualNP.Outside.L_pcx_244 :
∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
  let P := MvPolynomial (Fin n) (ZMod 2)
  let static := fun (axioms : Finset (PEqualNP.ProofComplexity.Clause (Fin n))) (budget : ℕ) =>
    ∃ (q : PEqualNP.ProofComplexity.Clause (Fin n) → P) (b : Fin n → P),
      (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (PEqualNP.ProofComplexity.clausePoly C).totalDegree ≤ budget) ∧
      (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
      axioms.sum (fun C => q C * PEqualNP.ProofComplexity.clausePoly C) +
        (∑ v, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 1
  let pos := fun i : ℕ => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)
  let blockers := fun T : Fin n → Bool → Bool → Bool =>
    let blocks := (Finset.univ : Finset (Fin n × (Bool × Bool))).filter
      (fun z => T z.1 z.2.1 z.2.2 = false)
    blocks.image (fun row =>
      ({(row.1, !row.2.1), (pos (row.1.val+1), !row.2.2)} : PEqualNP.ProofComplexity.Clause (Fin n)))
  ∀ len : ℕ, 1 ≤ len → len ≤ n →
    let allowed := fun (i : Fin n) (a b : Bool) =>
      if len ≤ i.val then true else if len = 1 then false
      else if i.val = 0 then b else if i.val+1 = len then !a else (!a || b)
    ∀ d : ℕ, static (blockers allowed) d ↔ len+1 < 2^d := by
  classical
  intro n hn hn2 P static pos blockers len hlen1 hlenn allowed d
  have hpos_ne : ∀ i : Fin n, i ≠ pos (i.val + 1) := by
    intro i heq
    have hval := congrArg Fin.val heq
    dsimp only [pos] at hval
    by_cases hlast : i.val + 1 = n
    · rw [hlast, Nat.mod_self] at hval; omega
    · have hlt : i.val + 1 < n := by have := i.2; omega
      rw [Nat.mod_eq_of_lt hlt] at hval; omega
  have hdeg2 : ∀ C ∈ blockers allowed, (clausePoly C).totalDegree = 2 := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨⟨i, a, b⟩, _, rfl⟩
    exact totalDegree_clausePoly_pair (hpos_ne i) (!a) (!b)
  have hstatic_ge2 : static (blockers allowed) d → 2 ≤ d := by
    rintro ⟨q, b, hq, hb, hsum⟩
    by_contra hlt
    have hq0 : ∀ C ∈ blockers allowed, q C = 0 := by
      intro C hC
      rcases hq C hC with h0 | hdeg
      · exact h0
      · rw [hdeg2 C hC] at hdeg; omega
    have hb0 : ∀ v : Fin n, b v = 0 := by
      intro v
      rcases hb v with h0 | hdeg
      · exact h0
      · omega
    have h1 : (blockers allowed).sum (fun C => q C * clausePoly C) = 0 :=
      Finset.sum_eq_zero fun C hC => by rw [hq0 C hC, zero_mul]
    have h2 : (∑ v : Fin n, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 0 :=
      Finset.sum_eq_zero fun v _ => by rw [hb0 v, zero_mul]
    rw [h1, h2, add_zero] at hsum
    have hc := congrArg (fun p : P => p.coeff (0 : Fin n →₀ ℕ)) hsum
    simp at hc
  by_cases hlen_eq1 : len = 1
  · subst hlen_eq1
    constructor
    · intro hs
      have hd2 := hstatic_ge2 hs
      have hpow : 4 ≤ 2 ^ d := by
        calc
          4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd2
      omega
    · intro hlt
      have hd2 : 2 ≤ d := by
        by_contra h
        have hd1 : d ≤ 1 := by omega
        interval_cases d <;> omega
      let i0 : Fin n := ⟨0, hn⟩
      let i1 : Fin n := ⟨1, by omega⟩
      have hpos0 : pos (i0.val + 1) = i1 := by
        apply Fin.ext; dsimp only [pos, i0, i1]; rw [Nat.mod_eq_of_lt (by omega)]
      let Cff : Clause (Fin n) := {(i0, true), (i1, true)}
      let Cft : Clause (Fin n) := {(i0, true), (i1, false)}
      let Ctf : Clause (Fin n) := {(i0, false), (i1, true)}
      let Ctt : Clause (Fin n) := {(i0, false), (i1, false)}
      have hbl_eq : blockers allowed = {Cff, Cft, Ctf, Ctt} := by
        ext C
        simp only [blockers, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨i, a, b⟩, hall, rfl⟩
          have hi0 : i = i0 := by
            apply Fin.ext; dsimp only [i0]
            by_contra hne
            have hge1 : 1 ≤ i.val := by omega
            simp [allowed, hge1] at hall
          subst hi0
          rw [hpos0]
          cases a <;> cases b <;> simp [Cff, Cft, Ctf, Ctt]
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨(i0, false, false), by simp [allowed, i0], by simp [Cff, hpos0]⟩
          · exact ⟨(i0, false, true), by simp [allowed, i0], by simp [Cft, hpos0]⟩
          · exact ⟨(i0, true, false), by simp [allowed, i0], by simp [Ctf, hpos0]⟩
          · exact ⟨(i0, true, true), by simp [allowed, i0], by simp [Ctt, hpos0]⟩
      have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
      have hne1 : Cff ≠ Cft := by
        intro h
        have hmem : (i1, true) ∈ Cft := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Cft, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · exact h01.symm (congrArg Prod.fst h1)
        · simp at h2
      have hne2 : Cff ≠ Ctf := by
        intro h
        have hmem : (i0, true) ∈ Ctf := h ▸ Finset.mem_insert_self _ _
        simp only [Ctf, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · exact h01 (congrArg Prod.fst h2)
      have hne3 : Cff ≠ Ctt := by
        intro h
        have hmem : (i0, true) ∈ Ctt := h ▸ Finset.mem_insert_self _ _
        simp only [Ctt, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · exact h01 (congrArg Prod.fst h2)
      have hne4 : Cft ≠ Ctf := by
        intro h
        have hmem : (i0, true) ∈ Ctf := h ▸ Finset.mem_insert_self _ _
        simp only [Ctf, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · exact h01 (congrArg Prod.fst h2)
      have hne5 : Cft ≠ Ctt := by
        intro h
        have hmem : (i0, true) ∈ Ctt := h ▸ Finset.mem_insert_self _ _
        simp only [Ctt, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · exact h01 (congrArg Prod.fst h2)
      have hne6 : Ctf ≠ Ctt := by
        intro h
        have hmem : (i1, true) ∈ Ctt := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Ctt, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · exact h01.symm (congrArg Prod.fst h1)
        · simp at h2
      refine ⟨fun _ => 1, fun _ => 0,
        fun C hC => Or.inr (by rw [hdeg2 C hC, MvPolynomial.totalDegree_one]; omega),
        fun _ => Or.inl rfl, ?_⟩
      simp only [zero_mul, Finset.sum_const_zero, add_zero, one_mul, hbl_eq]
      rw [Finset.sum_insert (by simp [hne1, hne2, hne3]),
        Finset.sum_insert (by simp [hne4, hne5]),
        Finset.sum_insert (by simp [hne6]), Finset.sum_singleton]
      rw [clausePoly_pair h01, clausePoly_pair h01, clausePoly_pair h01, clausePoly_pair h01]
      simp only [↓reduceIte, Bool.false_eq_true]
      have hcalc : (1 + MvPolynomial.X i0) * (1 + MvPolynomial.X i1) +
          ((1 + MvPolynomial.X i0) * MvPolynomial.X i1 +
          (MvPolynomial.X i0 * (1 + MvPolynomial.X i1) + MvPolynomial.X i0 * MvPolynomial.X i1)) =
          1 + (2 : P) * MvPolynomial.X i0 + (2 : P) * MvPolynomial.X i1 +
          (2 : P) * ((2 : P) * MvPolynomial.X i0 * MvPolynomial.X i1) := by
        ring
      rw [hcalc, mv_two_eq_zero]; ring
  · have hlen2 : 2 ≤ len := by omega
    let m : ℕ := len - 1
    have hm_pos : 0 < m := by omega
    let C00 : Clause (Fin n) := {(⟨0, hn⟩, true), (⟨1, by omega⟩, true)}
    let C01 : Clause (Fin n) := {(⟨0, hn⟩, false), (⟨1, by omega⟩, true)}
    let Cint : Fin (m - 1) → Clause (Fin n) := fun k =>
      {(⟨k.val + 1, by omega⟩, false), (⟨k.val + 2, by omega⟩, true)}
    let Cl0 : Clause (Fin n) := {(⟨len - 1, by omega⟩, false), (pos len, true)}
    let Cl1 : Clause (Fin n) := {(⟨len - 1, by omega⟩, false), (pos len, false)}
    have hpos_small : ∀ (j : ℕ) (hj : j < n), pos j = ⟨j, hj⟩ := fun j hj => by
      apply Fin.ext; dsimp only [pos]; exact Nat.mod_eq_of_lt hj
    have hpos_last : pos ((len - 1) + 1) = pos len := by rw [show len - 1 + 1 = len by omega]
    have hC00_mem : C00 ∈ blockers allowed := by
      refine Finset.mem_image.mpr ⟨(⟨0, hn⟩, false, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [allowed, hlen_eq1, show ¬ len ≤ 0 by omega]
      · simp [C00, hpos_small 1 (by omega)]
    have hC01_mem : C01 ∈ blockers allowed := by
      refine Finset.mem_image.mpr ⟨(⟨0, hn⟩, true, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [allowed, hlen_eq1, show ¬ len ≤ 0 by omega]
      · simp [C01, hpos_small 1 (by omega)]
    have hCint_mem : ∀ k : Fin (m - 1), Cint k ∈ blockers allowed := by
      intro k
      refine Finset.mem_image.mpr ⟨(⟨k.val + 1, by omega⟩, true, false),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have hlt : ¬ len ≤ k.val + 1 := by omega
        have hnel : k.val + 1 + 1 ≠ len := by omega
        simp [allowed, hlt, hlen_eq1, hnel]
      · simp [Cint, hpos_small (k.val + 2) (by omega)]
    have hCl0_mem : Cl0 ∈ blockers allowed := by
      refine Finset.mem_image.mpr ⟨(⟨len - 1, by omega⟩, true, false),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have hlt : ¬ len ≤ len - 1 := by omega
        have hne0 : len - 1 ≠ 0 := by omega
        have heql : len - 1 + 1 = len := by omega
        simp [allowed, hlt, hlen_eq1, hne0, heql]
      · simp [Cl0, hpos_last]
    have hCl1_mem : Cl1 ∈ blockers allowed := by
      refine Finset.mem_image.mpr ⟨(⟨len - 1, by omega⟩, true, true),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have hlt : ¬ len ≤ len - 1 := by omega
        have hne0 : len - 1 ≠ 0 := by omega
        have heql : len - 1 + 1 = len := by omega
        simp [allowed, hlt, hlen_eq1, hne0, heql]
      · simp [Cl1, hpos_last]
    constructor
    · intro hstat
      have hd2 := hstatic_ge2 hstat
      rcases hstat with ⟨q, b, hq, hb, hsum⟩
      let ρfun : Fin n → MvPolynomial (Fin m) F := fun v =>
        if h : 1 ≤ v.val ∧ v.val < len then MvPolynomial.X ⟨v.val - 1, by omega⟩ else 0
      let ρ : P →+* MvPolynomial (Fin m) F := MvPolynomial.eval₂Hom MvPolynomial.C ρfun
      have hρ_deg : ∀ f : P, (ρ f).totalDegree ≤ f.totalDegree := fun f =>
        eval2Hom_totalDegree_le ρfun (fun v => by
          dsimp only [ρfun]; split_ifs
          · simp [MvPolynomial.totalDegree_X]
          · simp) f
      have hρ_X : ∀ v : Fin n, ρ (MvPolynomial.X v) = ρfun v := fun v => MvPolynomial.eval₂Hom_X' _ _ v
      have hρ_pos_len : ρfun (pos len) = 0 := by
        dsimp only [ρfun, pos]
        by_cases hln : len = n
        · subst hln; simp
        · have hlt : len < n := by omega
          simp [Nat.mod_eq_of_lt hlt]
      have hρ_C00 : ρ (clausePoly C00) = 1 + MvPolynomial.X ⟨0, hm_pos⟩ := by
        rw [clausePoly_pair (by intro h; have := congrArg Fin.val h; simp at this)]
        have h1 : 1 ≤ (1 : ℕ) ∧ (1 : ℕ) < len := by omega
        simp [map_mul, map_add, map_one, hρ_X, ρfun, h1]
      have hρ_C01 : ρ (clausePoly C01) = 0 := by
        rw [clausePoly_pair (by intro h; have := congrArg Fin.val h; simp at this)]
        simp [map_mul, map_add, map_one, hρ_X, ρfun]
      have hρ_Cint : ∀ k : Fin (m - 1),
          ρ (clausePoly (Cint k)) = MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩) := by
        intro k
        rw [clausePoly_pair (by intro h; have := congrArg Fin.val h; simp at this)]
        have h1 : 1 ≤ k.val + 1 ∧ k.val + 1 < len := by omega
        have h2 : 1 ≤ k.val + 2 ∧ k.val + 2 < len := by omega
        simp [map_mul, map_add, map_one, hρ_X, ρfun, h1, h2]
      have hρ_Cl0 : ρ (clausePoly Cl0) = MvPolynomial.X ⟨m - 1, by omega⟩ := by
        have hne : (⟨len - 1, by omega⟩ : Fin n) ≠ pos len := by
          have := hpos_ne ⟨len - 1, by omega⟩
          simpa [hpos_last] using this
        rw [clausePoly_pair hne]
        have h1 : 1 ≤ len - 1 ∧ len - 1 < len := by omega
        simp [map_mul, map_add, map_one, hρ_X, hρ_pos_len, ρfun, h1, m]
      have hρ_Cl1 : ρ (clausePoly Cl1) = 0 := by
        have hne : (⟨len - 1, by omega⟩ : Fin n) ≠ pos len := by
          have := hpos_ne ⟨len - 1, by omega⟩
          simpa [hpos_last] using this
        rw [clausePoly_pair hne]
        simp [map_mul, hρ_X, hρ_pos_len]
      have hsum_ρ := congrArg ρ hsum
      rw [map_add, map_sum, map_sum, map_one] at hsum_ρ
      have hbool_ρ : (∑ v : Fin n, ρ (b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v))) =
          ∑ k : Fin m, ρ (b ⟨k.val + 1, by omega⟩) *
            (MvPolynomial.X k * MvPolynomial.X k + MvPolynomial.X k) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : Fin n => 1 ≤ v.val ∧ v.val < len)]
        have h0 : (∑ v ∈ Finset.univ.filter (fun v : Fin n => ¬ (1 ≤ v.val ∧ v.val < len)),
            ρ (b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v))) = 0 := by
          refine Finset.sum_eq_zero fun v hv => ?_
          have hnot := (Finset.mem_filter.mp hv).2
          simp [map_mul, map_add, hρ_X, ρfun, hnot]
        rw [h0, add_zero]
        refine Finset.sum_bij (fun v hv => ⟨v.val - 1, by have := (Finset.mem_filter.mp hv).2; omega⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun v1 hv1 v2 hv2 heq => Fin.ext (by
            have h1 := (Finset.mem_filter.mp hv1).2
            have h2 := (Finset.mem_filter.mp hv2).2
            have hval := congrArg (fun x : Fin m => x.val) heq
            dsimp at hval; omega))
          (fun k _ => ⟨⟨k.val + 1, by have hk := k.isLt; dsimp only [m] at hk; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have hk := k.isLt; dsimp only [m] at hk; dsimp; omega⟩,
            Fin.ext (by simp)⟩)
          (fun v hv => by
            have h1 := (Finset.mem_filter.mp hv).2
            simp [map_mul, map_add, hρ_X, ρfun, h1])
      have hbl_sub : ∀ C ∈ blockers allowed, C = C00 ∨ C = C01 ∨ C = Cl0 ∨ C = Cl1 ∨ ∃ k : Fin (m - 1), C = Cint k := by
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨⟨i, a, b⟩, hmem, rfl⟩
        have hall := (Finset.mem_filter.mp hmem).2
        have hlt : i.val < len := by
          by_contra hge
          simp [allowed, show len ≤ i.val by omega] at hall
        by_cases hi0 : i.val = 0
        · have hi_eq : i = ⟨0, hn⟩ := Fin.ext hi0
          subst hi_eq
          have hbf : b = false := by
            cases hb' : b
            · rfl
            · simp [allowed, hlen_eq1, show ¬ len ≤ 0 by omega, hb'] at hall
          subst hbf
          cases a
          · left; simp [C00, hpos_small 1 (by omega)]
          · right; left; simp [C01, hpos_small 1 (by omega)]
        · by_cases hil : i.val + 1 = len
          · have hlen_lt : len - 1 < n := by omega
            have hi_eq : i = ⟨len - 1, hlen_lt⟩ := Fin.ext (by dsimp; omega)
            subst hi_eq
            have hat : a = true := by
              cases ha' : a
              · simp [allowed, hlen_eq1, show ¬ len ≤ len - 1 by omega, show len - 1 ≠ 0 by omega,
                  show len - 1 + 1 = len by omega, ha'] at hall
              · rfl
            subst hat
            cases b
            · right; right; left; simp [Cl0, hpos_last]
            · right; right; right; left; simp [Cl1, hpos_last]
          · right; right; right; right
            have hmem' : a = true ∧ b = false := by
              cases a <;> cases b <;>
                simp [allowed, hlen_eq1, show ¬ len ≤ i.val by omega, hi0, hil] at hall ⊢
            rcases hmem' with ⟨rfl, rfl⟩
            refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
            have hi_eq : i = ⟨i.val - 1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
            have hpos_i : pos (i.val + 1) = ⟨i.val - 1 + 2, by omega⟩ := by
              rw [hpos_small (i.val + 1) (by omega)]; exact Fin.ext (by dsimp; omega)
            simp [Cint, ← hi_eq, hpos_i]
      have hC00_ne_Cl0 : C00 ≠ Cl0 := by
        intro h
        have hmem : (⟨0, hn⟩, true) ∈ Cl0 := h ▸ Finset.mem_insert_self _ _
        simp only [Cl0, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · have hpos_eq : (⟨0, hn⟩ : Fin n) = pos len := congrArg Prod.fst h2
          have hmem1 : (⟨1, by omega⟩, true) ∈ Cl0 :=
            h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          simp only [Cl0, Finset.mem_insert, Finset.mem_singleton] at hmem1
          rcases hmem1 with h3 | h4
          · simp at h3
          · have h10 : (⟨1, by omega⟩ : Fin n) = ⟨0, hn⟩ := (congrArg Prod.fst h4).trans hpos_eq.symm
            have := congrArg Fin.val h10; simp at this
      have hC00_ne_Cint : ∀ k : Fin (m - 1), C00 ≠ Cint k := by
        intro k h
        have hmem : (⟨0, hn⟩, true) ∈ Cint k := h ▸ Finset.mem_insert_self _ _
        simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · have := congrArg (fun p : Fin n × Bool => p.1.val) h2; simp at this
      have hCl0_ne_Cint : ∀ k : Fin (m - 1), Cl0 ≠ Cint k := by
        intro k h
        have hmem : (⟨len - 1, by omega⟩, false) ∈ Cint k := h ▸ Finset.mem_insert_self _ _
        simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · have := congrArg (fun p : Fin n × Bool => p.1.val) h1; dsimp at this; omega
        · simp at h2
      have hCint_inj : Function.Injective Cint := by
        intro k1 k2 h
        have hmem : (⟨k1.val + 1, by omega⟩, false) ∈ Cint k2 := h ▸ Finset.mem_insert_self _ _
        simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · have := congrArg (fun p : Fin n × Bool => p.1.val) h1; dsimp at this; exact Fin.ext (by omega)
        · simp at h2
      let active : Finset (Clause (Fin n)) := {C00, Cl0} ∪ Finset.univ.image Cint
      have hactive_sub : active ⊆ blockers allowed := by
        intro C hC
        rcases Finset.mem_union.mp hC with h1 | h2
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with rfl | rfl
          · exact hC00_mem
          · exact hCl0_mem
        · rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
          exact hCint_mem k
      have hbl_ρ : (∑ C ∈ blockers allowed, ρ (q C * clausePoly C)) =
          ρ (q C00) * (1 + MvPolynomial.X ⟨0, hm_pos⟩) +
          (∑ k : Fin (m - 1), ρ (q (Cint k)) *
            (MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩))) +
          ρ (q Cl0) * MvPolynomial.X ⟨m - 1, by omega⟩ := by
        rw [← Finset.sum_subset hactive_sub]
        · have hdisj : Disjoint ({C00, Cl0} : Finset (Clause (Fin n))) (Finset.univ.image Cint) := by
            rw [Finset.disjoint_left]
            intro C h1 h2
            rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1
            rcases h1 with h | h
            · exact hC00_ne_Cint k h.symm
            · exact hCl0_ne_Cint k h.symm
          rw [Finset.sum_union hdisj, Finset.sum_pair hC00_ne_Cl0,
            Finset.sum_image (fun k1 _ k2 _ h => hCint_inj h)]
          simp only [map_mul, hρ_C00, hρ_Cl0, hρ_Cint]
          ring
        · intro C hC hnot
          rcases hbl_sub C hC with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
          · exact absurd (Finset.mem_union_left _ (Finset.mem_insert_self _ _)) hnot
          · rw [map_mul, hρ_C01, mul_zero]
          · exact absurd (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hnot
          · rw [map_mul, hρ_Cl1, mul_zero]
          · exact absurd (Finset.mem_union_right _ (Finset.mem_image_of_mem Cint (Finset.mem_univ k))) hnot
      rw [hbl_ρ, hbool_ρ] at hsum_ρ
      by_contra hnot_lt
      have hnot_lt' : ¬ (m + 2 < 2 ^ d) := by dsimp only [m]; omega
      have hA_deg : ρ (q C00) = 0 ∨ (ρ (q C00)).totalDegree ≤ d - 2 := by
        rcases hq C00 hC00_mem with h0 | hd
        · left; rw [h0, map_zero]
        · right; have h1 := hρ_deg (q C00); rw [hdeg2 C00 hC00_mem] at hd; omega
      have hB_deg : ρ (q Cl0) = 0 ∨ (ρ (q Cl0)).totalDegree ≤ d - 2 := by
        rcases hq Cl0 hCl0_mem with h0 | hd
        · left; rw [h0, map_zero]
        · right; have h1 := hρ_deg (q Cl0); rw [hdeg2 Cl0 hCl0_mem] at hd; omega
      have hQ_deg : ∀ k : Fin (m - 1), ρ (q (Cint k)) = 0 ∨ (ρ (q (Cint k))).totalDegree ≤ d - 2 := by
        intro k
        rcases hq (Cint k) (hCint_mem k) with h0 | hd
        · left; rw [h0, map_zero]
        · right; have h1 := hρ_deg (q (Cint k)); rw [hdeg2 (Cint k) (hCint_mem k)] at hd; omega
      have hzero := multilin_eval_linear_on_component hd2 hm_pos (reachSet m d)
        (reachSet_step0 hd2 hm_pos) (reachSet_step_int (by omega)) (reachSet_sink (by omega) hnot_lt')
        (ρ (q C00)) (ρ (q Cl0)) hA_deg hB_deg (fun k => ρ (q (Cint k))) hQ_deg
        (fun k => ρ (b ⟨k.val + 1, by omega⟩))
      rw [hsum_ρ] at hzero
      have hone : (∑ S ∈ reachSet m d, multilin (1 : MvPolynomial (Fin m) F) S) = 1 := by
        simp_rw [multilin_one]
        rw [Finset.sum_eq_single (∅ : Finset (Fin m))]
        · simp
        · intro S _ hne; simp [hne]
        · intro h; exact absurd (reachSet_empty m d) h
      rw [hone] at hzero
      exact absurd hzero (by decide)
    · intro hlt
      have hd2 : 2 ≤ d := by
        by_contra h
        have hd1 : d ≤ 1 := by omega
        interval_cases d <;> omega
      rcases pebble_site_upper d (by omega) 0 len hlt with ⟨L, W, hW, hW0, hWL⟩
      have hex_len : ∃ t, t ≤ L ∧ len ∈ W t := ⟨L, le_refl L, by simpa using hWL⟩
      let tfirst := Nat.find hex_len
      have htf_spec := Nat.find_spec hex_len
      have htf_le : tfirst ≤ L := htf_spec.1
      have htf_mem : len ∈ W tfirst := htf_spec.2
      have htf_pos : 0 < tfirst := by
        by_contra h0
        have hz : tfirst = 0 := by omega
        rw [hz, hW0] at htf_mem
        exact Finset.notMem_empty len htf_mem
      have htf_before : ∀ t < tfirst, ∀ z ∈ W t, z < len := by
        intro t ht
        induction t with
        | zero => intro z hz; rw [hW0] at hz; exact absurd hz (Finset.notMem_empty z)
        | succ t iht =>
          intro z hz
          have hnot_len : len ∉ W (t + 1) := by
            intro hmem
            exact Nat.find_min hex_len ht ⟨by omega, hmem⟩
          have hstep := hW t (by omega)
          rcases hstep.2.2.2.2 with heq | ⟨j, _, hpre, hST⟩
          · rw [← heq] at hz; exact iht (by omega) z hz
          · rcases hST with hT | hS
            · rw [hT] at hz
              rcases Finset.mem_insert.mp hz with rfl | hprev
              · rcases hpre with rfl | hjm
                · omega
                · have hlt' := iht (by omega) (z - 1) hjm
                  have hne : z ≠ len := fun heq => hnot_len (heq ▸ (hT ▸ Finset.mem_insert_self z _))
                  omega
              · exact iht (by omega) z hprev
            · exact iht (by omega) z (by rw [hS]; exact Finset.mem_insert_of_mem hz)
      have hprev_last : len - 1 ∈ W (tfirst - 1) ∧ (W (tfirst - 1)).card ≤ d - 1 := by
        have hstep := hW (tfirst - 1) (by omega)
        rw [show tfirst - 1 + 1 = tfirst by omega] at hstep
        have hnot_prev : len ∉ W (tfirst - 1) := fun h => by
          have := htf_before (tfirst - 1) (by omega) len h; omega
        rcases hstep.2.2.2.2 with heq | ⟨j, _, hpre, hST⟩
        · rw [← heq] at htf_mem; exact absurd htf_mem hnot_prev
        · rcases hST with hT | hS
          · have hjeq : j = len := by
              rw [hT] at htf_mem
              rcases Finset.mem_insert.mp htf_mem with rfl | hprev
              · rfl
              · exact absurd hprev hnot_prev
            subst hjeq
            have hcard_ins : (W tfirst).card = (W (tfirst - 1)).card + 1 := by
              rw [hT, Finset.card_insert_of_notMem hnot_prev]
            have hle_c := hstep.2.1
            rcases hpre with h0 | hjm
            · omega
            · exact ⟨hjm, by omega⟩
          · exfalso
            have hprev : len ∈ W (tfirst - 1) := by rw [hS]; exact Finset.mem_insert_of_mem htf_mem
            exact hnot_prev hprev
      let proj : Finset ℕ → Finset (Fin n) := fun S =>
        Finset.univ.filter (fun v : Fin n => 1 ≤ v.val ∧ v.val < len ∧ v.val ∈ S)
      let mon : Finset ℕ → P := fun S => ∏ v ∈ proj S, MvPolynomial.X v
      have hproj_card : ∀ S : Finset ℕ, (proj S).card ≤ S.card := by
        intro S
        refine Finset.card_le_card_of_injOn Fin.val ?_ (fun a _ b _ h => Fin.ext h)
        intro v hv
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2.2.2
      have hproj_card_of_zero : ∀ S : Finset ℕ, 0 ∈ S → (proj S).card + 1 ≤ S.card := by
        intro S h0S
        have hsub : (proj S).image Fin.val ⊆ S.erase 0 := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
          have hf := (Finset.mem_filter.mp hv).2
          exact Finset.mem_erase.mpr ⟨by omega, hf.2.2⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_erase_of_mem h0S] at hle
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, h0S⟩
        omega
      have hP0_sum : clausePoly C00 + clausePoly C01 = 1 + MvPolynomial.X ⟨1, by omega⟩ := by
        have hne : (⟨0, hn⟩ : Fin n) ≠ ⟨1, by omega⟩ := by intro h; have := congrArg Fin.val h; simp at this
        rw [clausePoly_pair hne, clausePoly_pair hne]
        simp only [↓reduceIte, Bool.false_eq_true]
        have hc : (1 + MvPolynomial.X ⟨0, hn⟩) * (1 + MvPolynomial.X ⟨1, by omega⟩) +
            MvPolynomial.X ⟨0, hn⟩ * (1 + MvPolynomial.X ⟨1, by omega⟩) =
            (1 + MvPolynomial.X ⟨1, by omega⟩) + (2 : P) * MvPolynomial.X ⟨0, hn⟩ * (1 + MvPolynomial.X ⟨1, by omega⟩) := by
          ring
        rw [hc, mv_two_eq_zero]; ring
      have hPl_sum : clausePoly Cl0 + clausePoly Cl1 = MvPolynomial.X ⟨len - 1, by omega⟩ := by
        have hne : (⟨len - 1, by omega⟩ : Fin n) ≠ pos len := by
          have := hpos_ne ⟨len - 1, by omega⟩; simpa [hpos_last] using this
        rw [clausePoly_pair hne, clausePoly_pair hne]
        simp only [↓reduceIte, Bool.false_eq_true]
        have hc : MvPolynomial.X ⟨len - 1, by omega⟩ * (1 + MvPolynomial.X (pos len)) +
            MvPolynomial.X ⟨len - 1, by omega⟩ * MvPolynomial.X (pos len) =
            MvPolynomial.X ⟨len - 1, by omega⟩ + (2 : P) * MvPolynomial.X ⟨len - 1, by omega⟩ * MvPolynomial.X (pos len) := by
          ring
        rw [hc, mv_two_eq_zero]; ring
      have hstep_rep : ∀ t < tfirst - 1,
          ∃ q_t : Clause (Fin n) → P,
            (∀ C ∈ blockers allowed, q_t C = 0 ∨ (q_t C).totalDegree + (clausePoly C).totalDegree ≤ d) ∧
            (blockers allowed).sum (fun C => q_t C * clausePoly C) = mon (W t) + mon (W (t + 1)) := by
        intro t ht
        have hstep := hW t (by omega)
        have hC00_ne_C01 : C00 ≠ C01 := by
          intro h
          have hmem : (⟨0, hn⟩, true) ∈ C01 := h ▸ Finset.mem_insert_self _ _
          simp only [C01, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h2
          · simp at h1
          · have := congrArg (fun p : Fin n × Bool => p.1.val) h2; simp at this
        rcases hstep.2.2.2.2 with heq | ⟨j, _, hpre, hST⟩
        · refine ⟨fun _ => 0, fun _ _ => Or.inl rfl, ?_⟩
          rw [heq]; simp; exact (mv_add_self (mon (W (t + 1)))).symm
        · by_cases hj0 : j = 0
          · subst hj0
            have hpeq : proj (W t) = proj (W (t + 1)) := by
              ext v; simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and]
              rcases hST with hT | hS
              · rw [hT, Finset.mem_insert]; constructor
                · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, Or.inr h3⟩
                · rintro ⟨h1, h2, h3 | h3⟩
                  · omega
                  · exact ⟨h1, h2, h3⟩
              · rw [hS, Finset.mem_insert]; constructor
                · rintro ⟨h1, h2, h3 | h3⟩
                  · omega
                  · exact ⟨h1, h2, h3⟩
                · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, Or.inr h3⟩
            refine ⟨fun _ => 0, fun _ _ => Or.inl rfl, ?_⟩
            have hmeq : mon (W t) = mon (W (t + 1)) := by simp [mon, hpeq]
            rw [hmeq]; simp; exact (mv_add_self (mon (W (t + 1)))).symm
          · have hjlt : j < len := by
              rcases hST with hT | hS
              · exact htf_before (t + 1) (by omega) j (hT ▸ Finset.mem_insert_self j _)
              · exact htf_before t (by omega) j (hS ▸ Finset.mem_insert_self j _)
            have hnot_both_eq : ∀ (A B : Finset ℕ) (v : Fin n),
                (B = insert v.val A ∨ A = insert v.val B) → 1 ≤ v.val → v.val < len →
                (v ∉ proj A ∨ v ∉ proj B) →
                mon A + mon B = (∏ u ∈ (proj A ∩ proj B), MvPolynomial.X u) * (1 + MvPolynomial.X v) := by
              intro A B v hAB h1 h2 hdiff
              have hprod_ins : ∀ (U : Finset (Fin n)), v ∉ U →
                  (∏ u ∈ U, (MvPolynomial.X u : P)) + (∏ u ∈ insert v U, MvPolynomial.X u) =
                  (∏ u ∈ U, MvPolynomial.X u) * (1 + MvPolynomial.X v) := by
                intro U hvU
                rw [Finset.prod_insert hvU]; ring
              rcases hAB with rfl | rfl
              · by_cases hvA : v ∈ proj A
                · exfalso
                  have hvB : v ∈ proj (insert v.val A) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, Finset.mem_insert_self _ _⟩
                  rcases hdiff with h | h <;> exact h (by assumption)
                · have hpB : proj (insert v.val A) = insert v (proj A) := by
                    ext u; simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
                    constructor
                    · rintro ⟨hu1, hu2, hu3 | hu3⟩
                      · exact Or.inl (Fin.ext hu3)
                      · exact Or.inr ⟨hu1, hu2, hu3⟩
                    · rintro (rfl | ⟨hu1, hu2, hu3⟩)
                      · exact ⟨h1, h2, Or.inl rfl⟩
                      · exact ⟨hu1, hu2, Or.inr hu3⟩
                  have hinter : proj A ∩ proj (insert v.val A) = proj A := by
                    rw [hpB]; ext u; simp
                  rw [hinter]
                  dsimp only [mon]
                  rw [hpB]
                  exact hprod_ins (proj A) hvA
              · by_cases hvB : v ∈ proj B
                · exfalso
                  have hvA : v ∈ proj (insert v.val B) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, Finset.mem_insert_self _ _⟩
                  rcases hdiff with h | h <;> exact h (by assumption)
                · have hpA : proj (insert v.val B) = insert v (proj B) := by
                    ext u; simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
                    constructor
                    · rintro ⟨hu1, hu2, hu3 | hu3⟩
                      · exact Or.inl (Fin.ext hu3)
                      · exact Or.inr ⟨hu1, hu2, hu3⟩
                    · rintro (rfl | ⟨hu1, hu2, hu3⟩)
                      · exact ⟨h1, h2, Or.inl rfl⟩
                      · exact ⟨hu1, hu2, Or.inr hu3⟩
                  have hinter : proj (insert v.val B) ∩ proj B = proj B := by
                    rw [hpA]; ext u; simp
                  rw [hinter]
                  dsimp only [mon]
                  rw [hpA, add_comm]
                  exact hprod_ins (proj B) hvB
            by_cases hsame : W t = W (t + 1)
            · refine ⟨fun _ => 0, fun _ _ => Or.inl rfl, ?_⟩
              rw [hsame]; simp; exact (mv_add_self (mon (W (t + 1)))).symm
            · have hv_diff : (⟨j, by omega⟩ : Fin n) ∉ proj (W t) ∨ (⟨j, by omega⟩ : Fin n) ∉ proj (W (t + 1)) := by
                rcases hST with hT | hS
                · left; intro hmem
                  have hjW : j ∈ W t := (Finset.mem_filter.mp hmem).2.2.2
                  exact hsame (hT.trans (Finset.insert_eq_of_mem hjW)).symm
                · right; intro hmem
                  have hjW : j ∈ W (t + 1) := (Finset.mem_filter.mp hmem).2.2.2
                  exact hsame (hS.trans (Finset.insert_eq_of_mem hjW))
              have hmon_eq := hnot_both_eq (W t) (W (t + 1)) ⟨j, by omega⟩ hST (by dsimp; omega) hjlt hv_diff
              let U := proj (W t) ∩ proj (W (t + 1))
              by_cases hj1 : j = 1
              · subst hj1
                have h0_both : 0 ∈ W t ∧ 0 ∈ W (t + 1) := by
                  rcases hpre with h0 | h0mem
                  · omega
                  · rcases hST with hT | hS
                    · exact ⟨h0mem, hT ▸ Finset.mem_insert_of_mem h0mem⟩
                    · have hne : (0 : ℕ) ≠ 1 := by decide
                      rcases Finset.mem_insert.mp (hS ▸ h0mem) with h | h
                      · exact absurd h hne
                      · exact ⟨h0mem, h⟩
                have hUcard : U.card ≤ d - 2 := by
                  rcases hv_diff with hnot | hnot
                  · have hsub : insert (⟨1, by omega⟩ : Fin n) U ⊆ proj (W (t + 1)) := by
                      intro u hu
                      rcases Finset.mem_insert.mp hu with rfl | hU
                      · rcases hST with hT | hS
                        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hT ▸ Finset.mem_insert_self _ _⟩
                        · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hS ▸ Finset.mem_insert_self _ _⟩)
                      · exact (Finset.mem_inter.mp hU).2
                    have hnotU : (⟨1, by omega⟩ : Fin n) ∉ U := fun h => hnot (Finset.mem_inter.mp h).1
                    have h1 := Finset.card_le_card hsub
                    rw [Finset.card_insert_of_notMem hnotU] at h1
                    have h2 := hproj_card_of_zero (W (t + 1)) h0_both.2
                    have h3 := hstep.2.1
                    omega
                  · have hsub : insert (⟨1, by omega⟩ : Fin n) U ⊆ proj (W t) := by
                      intro u hu
                      rcases Finset.mem_insert.mp hu with rfl | hU
                      · rcases hST with hT | hS
                        · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hT ▸ Finset.mem_insert_self _ _⟩)
                        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hS ▸ Finset.mem_insert_self _ _⟩
                      · exact (Finset.mem_inter.mp hU).1
                    have hnotU : (⟨1, by omega⟩ : Fin n) ∉ U := fun h => hnot (Finset.mem_inter.mp h).2
                    have h1 := Finset.card_le_card hsub
                    rw [Finset.card_insert_of_notMem hnotU] at h1
                    have h2 := hproj_card_of_zero (W t) h0_both.1
                    have h3 := hstep.1
                    omega
                let cof : P := ∏ u ∈ U, MvPolynomial.X u
                let q_t : Clause (Fin n) → P := fun C => if C = C00 ∨ C = C01 then cof else 0
                refine ⟨q_t, ?_, ?_⟩
                · intro C hC
                  by_cases hC0 : C = C00 ∨ C = C01
                  · right
                    simp only [q_t, hC0, ↓reduceIte]
                    rw [hdeg2 C hC]
                    dsimp only [cof]
                    have := prod_X_totalDegree U
                    omega
                  · left; simp [q_t, hC0]
                · rw [← Finset.sum_subset (s₁ := {C00, C01}) (by
                    intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
                    rcases hC with rfl | rfl; exact hC00_mem; exact hC01_mem)]
                  · rw [Finset.sum_pair hC00_ne_C01]
                    simp only [q_t, true_or, or_true, ↓reduceIte]
                    rw [← mul_add, hP0_sum, hmon_eq]
                  · intro C _ hnot
                    have h1 : ¬ (C = C00 ∨ C = C01) := by simpa using hnot
                    simp [q_t, h1]
              · have hj2 : 2 ≤ j := by omega
                have hjm_both : j - 1 ∈ W t ∧ j - 1 ∈ W (t + 1) := by
                  rcases hpre with h0 | hjm
                  · omega
                  · rcases hST with hT | hS
                    · exact ⟨hjm, hT ▸ Finset.mem_insert_of_mem hjm⟩
                    · have hne : j - 1 ≠ j := by omega
                      rcases Finset.mem_insert.mp (hS ▸ hjm) with h | h
                      · exact absurd h hne
                      · exact ⟨hjm, h⟩
                let vprev : Fin n := ⟨j - 1, by omega⟩
                have hvprev_U : vprev ∈ U :=
                  Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [vprev]; omega, by dsimp only [vprev]; omega, hjm_both.1⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [vprev]; omega, by dsimp only [vprev]; omega, hjm_both.2⟩⟩
                let U' := U.erase vprev
                have hU'_card : U'.card ≤ d - 2 := by
                  have hUcard : U.card ≤ d - 1 := by
                    rcases hv_diff with hnot | hnot
                    · have hsub : insert (⟨j, by omega⟩ : Fin n) U ⊆ proj (W (t + 1)) := by
                        intro u hu
                        rcases Finset.mem_insert.mp hu with rfl | hU
                        · rcases hST with hT | hS
                          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hT ▸ Finset.mem_insert_self _ _⟩
                          · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hS ▸ Finset.mem_insert_self _ _⟩)
                        · exact (Finset.mem_inter.mp hU).2
                      have hnotU : (⟨j, by omega⟩ : Fin n) ∉ U := fun h => hnot (Finset.mem_inter.mp h).1
                      have h1 := Finset.card_le_card hsub
                      rw [Finset.card_insert_of_notMem hnotU] at h1
                      have h2 := hproj_card (W (t + 1))
                      have h3 := hstep.2.1
                      omega
                    · have hsub : insert (⟨j, by omega⟩ : Fin n) U ⊆ proj (W t) := by
                        intro u hu
                        rcases Finset.mem_insert.mp hu with rfl | hU
                        · rcases hST with hT | hS
                          · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hT ▸ Finset.mem_insert_self _ _⟩)
                          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hjlt, hS ▸ Finset.mem_insert_self _ _⟩
                        · exact (Finset.mem_inter.mp hU).1
                      have hnotU : (⟨j, by omega⟩ : Fin n) ∉ U := fun h => hnot (Finset.mem_inter.mp h).2
                      have h1 := Finset.card_le_card hsub
                      rw [Finset.card_insert_of_notMem hnotU] at h1
                      have h2 := hproj_card (W t)
                      have h3 := hstep.1
                      omega
                  rw [Finset.card_erase_of_mem hvprev_U]
                  omega
                let k : Fin (m - 1) := ⟨j - 2, by omega⟩
                let cof : P := ∏ u ∈ U', MvPolynomial.X u
                let q_t : Clause (Fin n) → P := fun C => if C = Cint k then cof else 0
                refine ⟨q_t, ?_, ?_⟩
                · intro C hC
                  by_cases hCk : C = Cint k
                  · right
                    simp only [q_t, hCk, ↓reduceIte]
                    rw [hdeg2 (Cint k) (hCint_mem k)]
                    dsimp only [cof]
                    have := prod_X_totalDegree U'
                    omega
                  · left; simp [q_t, hCk]
                · rw [Finset.sum_eq_single (Cint k)]
                  · simp only [q_t, ↓reduceIte]
                    have hne : (⟨k.val + 1, by omega⟩ : Fin n) ≠ ⟨k.val + 2, by omega⟩ := by
                      intro h; have := congrArg Fin.val h; simp at this
                    rw [clausePoly_pair hne]
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have hv1 : (⟨k.val + 1, by omega⟩ : Fin n) = vprev := Fin.ext (by dsimp [k, vprev]; omega)
                    have hv2 : (⟨k.val + 2, by omega⟩ : Fin n) = ⟨j, by omega⟩ := Fin.ext (by dsimp [k]; omega)
                    rw [hv1, hv2, hmon_eq]
                    have hprod : (∏ u ∈ U, (MvPolynomial.X u : P)) = cof * MvPolynomial.X vprev := by
                      dsimp only [cof, U']
                      rw [mul_comm, Finset.mul_prod_erase U (fun u => (MvPolynomial.X u : P)) hvprev_U]
                    rw [hprod]; ring
                  · intro C _ hne; simp [q_t, hne]
                  · intro h; exact absurd (hCint_mem k) h
      have hCl0_ne_Cl1 : Cl0 ≠ Cl1 := by
        intro h
        have hmem : (pos len, true) ∈ Cl1 := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Cl1, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h1 | h2
        · simp at h1
        · simp at h2
      let vlast : Fin n := ⟨len - 1, by omega⟩
      have hvlast_mem : vlast ∈ proj (W (tfirst - 1)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [vlast]; omega, by dsimp only [vlast]; omega, hprev_last.1⟩
      let Uend := (proj (W (tfirst - 1))).erase vlast
      have hUend_card : Uend.card ≤ d - 2 := by
        rw [Finset.card_erase_of_mem hvlast_mem]
        have h1 := hproj_card (W (tfirst - 1))
        have h2 := hprev_last.2
        omega
      let cof_end : P := ∏ u ∈ Uend, MvPolynomial.X u
      let q_end : Clause (Fin n) → P := fun C => if C = Cl0 ∨ C = Cl1 then cof_end else 0
      have hq_end_deg : ∀ C ∈ blockers allowed,
          q_end C = 0 ∨ (q_end C).totalDegree + (clausePoly C).totalDegree ≤ d := by
        intro C hC
        by_cases hCl : C = Cl0 ∨ C = Cl1
        · right
          simp only [q_end, hCl, ↓reduceIte]
          rw [hdeg2 C hC]
          dsimp only [cof_end]
          have := prod_X_totalDegree Uend
          omega
        · left; simp [q_end, hCl]
      have hq_end_sum : (blockers allowed).sum (fun C => q_end C * clausePoly C) = mon (W (tfirst - 1)) := by
        rw [← Finset.sum_subset (s₁ := {Cl0, Cl1}) (by
          intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
          rcases hC with rfl | rfl; exact hCl0_mem; exact hCl1_mem)]
        · rw [Finset.sum_pair hCl0_ne_Cl1]
          simp only [q_end, true_or, or_true, ↓reduceIte]
          rw [← mul_add, hPl_sum]
          dsimp only [mon, cof_end, Uend]
          rw [mul_comm, Finset.mul_prod_erase (proj (W (tfirst - 1))) (fun u => (MvPolynomial.X u : P)) hvlast_mem]
        · intro C _ hnot
          have h1 : ¬ (C = Cl0 ∨ C = Cl1) := by simpa using hnot
          simp [q_end, h1]
      let q_step : Fin (tfirst - 1) → (Clause (Fin n) → P) := fun t => Classical.choose (hstep_rep t.val t.2)
      have hq_step_deg : ∀ (t : Fin (tfirst - 1)) (C : Clause (Fin n)), C ∈ blockers allowed →
          q_step t C = 0 ∨ (q_step t C).totalDegree + (clausePoly C).totalDegree ≤ d := fun t C hC =>
        (Classical.choose_spec (hstep_rep t.val t.2)).1 C hC
      have hq_step_sum : ∀ t : Fin (tfirst - 1),
          (blockers allowed).sum (fun C => q_step t C * clausePoly C) = mon (W t.val) + mon (W (t.val + 1)) :=
        fun t => (Classical.choose_spec (hstep_rep t.val t.2)).2
      let q_tot : Clause (Fin n) → P := fun C => (∑ t : Fin (tfirst - 1), q_step t C) + q_end C
      refine ⟨q_tot, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
      · intro C hC
        right
        have hsum_deg : (∑ t : Fin (tfirst - 1), q_step t C).totalDegree ≤ d - 2 := by
          refine le_trans (totalDegree_finset_sum_le _ _) ?_
          rw [Finset.sup_le_iff]
          intro t _
          rcases hq_step_deg t C hC with h0 | hdeg
          · rw [h0]; simp
          · rw [hdeg2 C hC] at hdeg; omega
        have hend_deg : (q_end C).totalDegree ≤ d - 2 := by
          rcases hq_end_deg C hC with h0 | hdeg
          · rw [h0]; simp
          · rw [hdeg2 C hC] at hdeg; omega
        have htot_deg : (q_tot C).totalDegree ≤ d - 2 :=
          le_trans (MvPolynomial.totalDegree_add _ _) (max_le hsum_deg hend_deg)
        rw [hdeg2 C hC]
        omega
      · simp only [zero_mul, Finset.sum_const_zero, add_zero]
        have hdist : (blockers allowed).sum (fun C => q_tot C * clausePoly C) =
            (∑ t : Fin (tfirst - 1), (blockers allowed).sum (fun C => q_step t C * clausePoly C)) +
            (blockers allowed).sum (fun C => q_end C * clausePoly C) := by
          simp_rw [q_tot, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
          rw [Finset.sum_comm]
        rw [hdist, hq_end_sum]
        simp_rw [hq_step_sum]
        have htele : ∀ K : ℕ, (∑ t : Fin K, (mon (W t.val) + mon (W (t.val + 1)))) + mon (W K) = mon (W 0) := by
          intro K
          induction K with
          | zero => simp
          | succ K ih =>
            rw [Fin.sum_univ_castSucc]
            calc
              ((∑ x : Fin K, (mon (W x.val) + mon (W (x.val + 1)))) + (mon (W K) + mon (W (K + 1)))) + mon (W (K + 1))
                  = ((∑ x : Fin K, (mon (W x.val) + mon (W (x.val + 1)))) + mon (W K)) +
                    (mon (W (K + 1)) + mon (W (K + 1))) := by ring
              _ = mon (W 0) + 0 := by rw [ih, mv_add_self]
              _ = mon (W 0) := add_zero _
        rw [htele (tfirst - 1), hW0]
        have hemp : proj ∅ = ∅ := by ext v; simp [proj]
        simp [mon, hemp]
