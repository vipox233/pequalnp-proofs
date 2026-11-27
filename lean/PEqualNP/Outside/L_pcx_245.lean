import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_245_aux

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

noncomputable def litPoly {V : Type} (v : V) (a : Bool) : MvPolynomial V F :=
  if a = true then MvPolynomial.X v else 1 + MvPolynomial.X v

lemma litPoly_add_not {V : Type} (v : V) (a : Bool) :
    litPoly v a + litPoly v (!a) = 1 := by
  cases a
  · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    calc
      1 + MvPolynomial.X v + MvPolynomial.X v = 1 + (MvPolynomial.X v + MvPolynomial.X v) := by ring
      _ = 1 := by rw [mv_add_self, add_zero]
  · simp only [litPoly, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    calc
      MvPolynomial.X v + (1 + MvPolynomial.X v) = 1 + (MvPolynomial.X v + MvPolynomial.X v) := by ring
      _ = 1 := by rw [mv_add_self, add_zero]

lemma litPoly_mul_not {V : Type} (v : V) (a : Bool) :
    litPoly v a * litPoly v (!a) = MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v := by
  cases a <;> simp only [litPoly, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] <;> ring

lemma totalDegree_litPoly {V : Type} (v : V) (a : Bool) :
    (litPoly v a).totalDegree ≤ 1 := by
  cases a
  · simp only [litPoly, Bool.false_eq_true, ↓reduceIte]
    exact le_trans (MvPolynomial.totalDegree_add _ _) (by simp [MvPolynomial.totalDegree_X])
  · simp [litPoly, MvPolynomial.totalDegree_X]

lemma clausePoly_pair {V : Type} [DecidableEq V] {i j : V} (hij : i ≠ j) (s1 s2 : Bool) :
    clausePoly ({(i, s1), (j, s2)} : Clause V) =
      (if s1 = true then 1 + MvPolynomial.X i else MvPolynomial.X i) *
      (if s2 = true then 1 + MvPolynomial.X j else MvPolynomial.X j) := by
  unfold clausePoly
  have hne : (i, s1) ≠ (j, s2) := fun h => hij (congrArg Prod.fst h)
  rw [Finset.prod_pair hne]

lemma clausePoly_blocker {V : Type} [DecidableEq V] {i j : V} (hij : i ≠ j) (a b : Bool) :
    clausePoly ({(i, !a), (j, !b)} : Clause V) = litPoly i a * litPoly j b := by
  rw [clausePoly_pair hij]
  cases a <;> cases b <;> simp [litPoly]

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

lemma totalDegree_boolAxiom {V : Type} [DecidableEq V] (v : V) :
    ((MvPolynomial.X v : MvPolynomial V F) * MvPolynomial.X v + MvPolynomial.X v).totalDegree = 2 := by
  apply le_antisymm
  · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ (by simp [MvPolynomial.totalDegree_X]))
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (by simp [MvPolynomial.totalDegree_X])
  · let m : V →₀ ℕ := Finsupp.single v 2
    have hm_sum : m.sum (fun _ e => e) = 2 := by simp [m]
    have hm_ne : m ≠ Finsupp.single v 1 := by
      intro h
      have := congrArg (fun f : V →₀ ℕ => f v) h
      simp [m] at this
    have hX2 : (MvPolynomial.X v : MvPolynomial V F) * MvPolynomial.X v = MvPolynomial.monomial m 1 := by
      simp [MvPolynomial.X, m, ← Finsupp.single_add]
    have hc : ((MvPolynomial.X v : MvPolynomial V F) * MvPolynomial.X v + MvPolynomial.X v).coeff m = 1 := by
      rw [mv_coeff_add, hX2, MvPolynomial.coeff_monomial, MvPolynomial.coeff_X]
      simp [hm_ne.symm]
    have hmem : m ∈ ((MvPolynomial.X v : MvPolynomial V F) * MvPolynomial.X v + MvPolynomial.X v).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [hc]; decide)
    have hle := MvPolynomial.le_totalDegree hmem
    omega

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

lemma prod_litPoly_totalDegree {ι V : Type} (s : Finset ι) (u : ι → V) (a : ι → Bool) :
    (∏ i ∈ s, litPoly (u i) (a i)).totalDegree ≤ s.card := by
  classical
  refine le_trans (totalDegree_finset_prod_le _ _) ?_
  calc
    (∑ i ∈ s, (litPoly (u i) (a i)).totalDegree) ≤ ∑ _i ∈ s, 1 :=
      Finset.sum_le_sum fun i _ => totalDegree_litPoly (u i) (a i)
    _ = s.card := by simp

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
              intro t h1 h2
              by_contra hne
              have hemp : (W t).filter (fun z => M + 1 ≤ z) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
              have hmem : t ∈ S_empty :=
                Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hemp⟩
              have hle := Finset.le_max' S_empty t hmem
              omega
            have hM_in : M ∈ W (tstar + 1) := by
              have hne := hhi_all (tstar + 1) (le_refl _) (by omega)
              have hstep := hW tstar (by omega)
              rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
              · rw [← heq] at hne
                rw [htstar_empty] at hne
                simp at hne
              · rcases hST with hT | hS
                · have hj_ge : M + 1 ≤ j := by
                    rcases hne with ⟨z, hz⟩
                    have hzW : z ∈ W (tstar + 1) := (Finset.mem_filter.mp hz).1
                    have hzM : M + 1 ≤ z := (Finset.mem_filter.mp hz).2
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
                    · have hlt : j - 1 < M + 1 := by
                        by_contra hge
                        have hmem : j - 1 ∈ (W tstar).filter (fun u => M + 1 ≤ u) :=
                          Finset.mem_filter.mpr ⟨hjm, by omega⟩
                        rw [htstar_empty] at hmem
                        exact Finset.notMem_empty _ hmem
                      omega
                  rcases hpre with hja' | hjm
                  · omega
                  · rw [hT, show M = j - 1 by omega]
                    exact Finset.mem_insert_of_mem hjm
                · exfalso
                  rcases hne with ⟨z, hz⟩
                  have hzW : z ∈ W (tstar + 1) := (Finset.mem_filter.mp hz).1
                  have hzM : M + 1 ≤ z := (Finset.mem_filter.mp hz).2
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
            have hRrev0 : (fun i => R (t2 - (tstar + 1) - i)) 0 = ∅ := by
              dsimp only [R]
              rw [Nat.sub_zero, show tstar + 1 + (t2 - (tstar + 1)) = t2 by omega]
              exact ht2_low_empty
            have hM_end : M ∈ (fun i => R (t2 - (tstar + 1) - i)) (t2 - (tstar + 1)) := by
              dsimp only [R]
              rw [Nat.sub_self, Nat.add_zero]
              exact Finset.mem_filter.mpr ⟨hM_in, le_refl M⟩
            have hbd := ihp hp1 (t2 - (tstar + 1)) a _ hRrev hRrev0 M hM_end
            omega
          · have ht2_hi_empty : (W t2).filter (fun z => M + 1 ≤ z) = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp ht2_hi
            have hWt2_empty : W t2 = ∅ := by
              ext z
              simp only [Finset.notMem_empty, iff_false]
              intro hz
              by_cases hzM : z ≤ M
              · have : z ∈ (W t2).filter (fun u => u ≤ M) := Finset.mem_filter.mpr ⟨hz, hzM⟩
                rw [ht2_low_empty] at this
                exact Finset.notMem_empty z this
              · have : z ∈ (W t2).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hz, by omega⟩
                rw [ht2_hi_empty] at this
                exact Finset.notMem_empty z this
            have hltL : L - t2 < L := by omega
            let W' : ℕ → Finset ℕ := fun i => W (t2 + i)
            have hW'_walk : ValidWalk (p + 1) a (L - t2) W' := by
              intro i hi
              dsimp only [W']
              rw [show t2 + (i + 1) = t2 + i + 1 by omega]
              exact hW (t2 + i) (by omega)
            have hW'0 : W' 0 = ∅ := by simpa [W'] using hWt2_empty
            have hyW' : y ∈ W' (L - t2) := by
              dsimp only [W']; rw [show t2 + (L - t2) = L by omega]; exact hy
            have hbd := ihL (L - t2) hltL a W' hW'_walk hW'0 y hyW'
            omega

lemma pebble_no_one_and_top {d n L : ℕ} {W : ℕ → Finset ℕ}
    (hd : 3 ≤ d) (hnot : ¬ (n + 2 < 2 ^ d))
    (hW : ValidWalk d 0 L W) (hW0 : W 0 = ∅) (h1 : 1 ∈ W L) (hn : n ∈ W L) : False := by
  classical
  let p : ℕ := d - 1
  have hp2 : 2 ≤ p := by omega
  have hdp : d = p + 1 := by omega
  have hpow : 2 ^ d = 2 ^ p + 2 ^ p := by rw [hdp, pow_succ]; omega
  have h2p : 4 ≤ 2 ^ p := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp2
  let M : ℕ := 2 ^ p - 1
  have h1M : 1 < M := by omega
  have hMn : M + 1 ≤ n := by omega
  have hW_p1 : ValidWalk (p + 1) 0 L W := hdp ▸ hW
  let S_empty : Finset ℕ := (Finset.range (L + 1)).filter
    (fun t => (W t).filter (fun z => M + 1 ≤ z) = ∅)
  have hS_ne : S_empty.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simp [hW0]⟩⟩
  let tstar := S_empty.max' hS_ne
  have htstar_mem := Finset.mem_filter.mp (Finset.max'_mem S_empty hS_ne)
  have htstar_le : tstar ≤ L := by have := Finset.mem_range.mp htstar_mem.1; omega
  have htstar_empty : (W tstar).filter (fun z => M + 1 ≤ z) = ∅ := htstar_mem.2
  have htstar_lt : tstar < L := by
    by_contra hge
    have heq : tstar = L := by omega
    have hn_in : n ∈ (W L).filter (fun z => M + 1 ≤ z) := Finset.mem_filter.mpr ⟨hn, hMn⟩
    rw [← heq, htstar_empty] at hn_in
    exact Finset.notMem_empty n hn_in
  have hhi_all : ∀ t, tstar + 1 ≤ t → t ≤ L → ((W t).filter (fun z => M + 1 ≤ z)).Nonempty := by
    intro t ht1 ht2
    by_contra hne
    have hemp : (W t).filter (fun z => M + 1 ≤ z) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hmem : t ∈ S_empty := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hemp⟩
    have hle := Finset.le_max' S_empty t hmem
    omega
  have hM_in : M ∈ W (tstar + 1) := by
    have hne := hhi_all (tstar + 1) (le_refl _) (by omega)
    have hstep := hW_p1 tstar (by omega)
    rcases hstep.2.2.2.2 with heq | ⟨j, _, hpre, hST⟩
    · rw [← heq] at hne; rw [htstar_empty] at hne; simp at hne
    · rcases hST with hT | hS
      · have hj_ge : M + 1 ≤ j := by
          rcases hne with ⟨z, hz⟩
          have hzW : z ∈ W (tstar + 1) := (Finset.mem_filter.mp hz).1
          have hzM : M + 1 ≤ z := (Finset.mem_filter.mp hz).2
          rw [hT] at hzW
          rcases Finset.mem_insert.mp hzW with rfl | hprev
          · exact hzM
          · exfalso
            have hmem : z ∈ (W tstar).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hprev, hzM⟩
            rw [htstar_empty] at hmem
            exact Finset.notMem_empty z hmem
        have hj_eq : j = M + 1 := by
          rcases hpre with rfl | hjm
          · omega
          · have hlt : j - 1 < M + 1 := by
              by_contra hge
              have hmem : j - 1 ∈ (W tstar).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hjm, by omega⟩
              rw [htstar_empty] at hmem
              exact Finset.notMem_empty _ hmem
            omega
        rcases hpre with h0 | hjm
        · omega
        · rw [hT, show M = j - 1 by omega]
          exact Finset.mem_insert_of_mem hjm
      · exfalso
        rcases hne with ⟨z, hz⟩
        have hzW : z ∈ W (tstar + 1) := (Finset.mem_filter.mp hz).1
        have hzM : M + 1 ≤ z := (Finset.mem_filter.mp hz).2
        have hprev : z ∈ W tstar := by rw [hS]; exact Finset.mem_insert_of_mem hzW
        have hmem : z ∈ (W tstar).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hprev, hzM⟩
        rw [htstar_empty] at hmem
        exact Finset.notMem_empty z hmem
  have hR_walk_to : ∀ t2, tstar + 1 ≤ t2 → t2 ≤ L →
      ValidWalk p 0 (t2 - (tstar + 1)) (fun i => (W (tstar + 1 + i)).filter (fun z => z ≤ M)) := by
    intro t2 ht2_1 ht2_2 i hi
    have hstep := hW_p1 (tstar + 1 + i) (by omega)
    have hne1 := hhi_all (tstar + 1 + i) (by omega) (by omega)
    have hne2 := hhi_all (tstar + 1 + i + 1) (by omega) (by omega)
    have hcard1 : ((W (tstar + 1 + i)).filter (fun z => z ≤ M)).card ≤ p := by
      have htot := Finset.card_filter_add_card_filter_not (s := W (tstar + 1 + i)) (p := fun z => z ≤ M)
      have hneg : (W (tstar + 1 + i)).filter (fun z => ¬ z ≤ M) =
          (W (tstar + 1 + i)).filter (fun z => M + 1 ≤ z) := by
        ext z; simp only [Finset.mem_filter]; constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by omega⟩
      rw [hneg] at htot
      have hpos := Finset.card_pos.mpr hne1
      have hle := hstep.1
      omega
    have hcard2 : ((W (tstar + 1 + (i + 1))).filter (fun z => z ≤ M)).card ≤ p := by
      rw [show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega]
      have htot := Finset.card_filter_add_card_filter_not (s := W (tstar + 1 + i + 1)) (p := fun z => z ≤ M)
      have hneg : (W (tstar + 1 + i + 1)).filter (fun z => ¬ z ≤ M) =
          (W (tstar + 1 + i + 1)).filter (fun z => M + 1 ≤ z) := by
        ext z; simp only [Finset.mem_filter]; constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by omega⟩
      rw [hneg] at htot
      have hpos := Finset.card_pos.mpr hne2
      have hle := hstep.2.1
      omega
    dsimp only
    refine ⟨hcard1, hcard2, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _, ?_⟩
    rcases hstep.2.2.2.2 with heq | ⟨j, hja, hpre, hST⟩
    · left; rw [show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, heq]
    · by_cases hjM : j ≤ M
      · right
        refine ⟨j, hja, ?_, ?_⟩
        · rcases hpre with rfl | hjm
          · exact Or.inl rfl
          · exact Or.inr (Finset.mem_filter.mpr ⟨hjm, by omega⟩)
        · rcases hST with hT' | hS'
          · left; ext z
            simp only [show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, hT', Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hmem, hz⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hmem, hz⟩
            · rintro (rfl | ⟨hmem, hz⟩)
              · exact ⟨Or.inl rfl, hjM⟩
              · exact ⟨Or.inr hmem, hz⟩
          · right; ext z
            simp only [show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, hS', Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hmem, hz⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hmem, hz⟩
            · rintro (rfl | ⟨hmem, hz⟩)
              · exact ⟨Or.inl rfl, hjM⟩
              · exact ⟨Or.inr hmem, hz⟩
      · left; ext z
        simp only [show tstar + 1 + (i + 1) = tstar + 1 + i + 1 by omega, Finset.mem_filter]
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
  by_cases hlow1 : ((W L).filter (fun z => z ≤ M)).card ≤ 1
  · have hlow_eq : (W L).filter (fun z => z ≤ M) = {1} := by
      have h1in : 1 ∈ (W L).filter (fun z => z ≤ M) := Finset.mem_filter.mpr ⟨h1, by omega⟩
      have hsub : ({1} : Finset ℕ) ⊆ (W L).filter (fun z => z ≤ M) := Finset.singleton_subset_iff.mpr h1in
      exact (Finset.eq_of_subset_of_card_le hsub (by simpa using hlow1)).symm
    let Winit : ℕ → Finset ℕ := fun i => if i = 0 then ∅ else if i = 1 then {0} else if i = 2 then {0, 1} else {1}
    have hWinit : ValidWalk p 0 3 Winit := by
      intro i hi
      interval_cases i
      · simp only [Winit, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
        exact ⟨by simp, by simp; omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
          Or.inr ⟨0, le_refl 0, Or.inl rfl, Or.inl (by simp)⟩⟩
      · simp only [Winit, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
        refine ⟨by simp; omega, ?_, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
          Or.inr ⟨1, by omega, Or.inr (Finset.mem_singleton_self 0), Or.inl ?_⟩⟩
        · rw [Finset.card_pair (by decide)]; omega
        · ext x; simp; tauto
      · simp only [Winit, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
          show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide]
        refine ⟨?_, by simp; omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
          Or.inr ⟨0, le_refl 0, Or.inl rfl, Or.inr rfl⟩⟩
        rw [Finset.card_pair (by decide)]; omega
    have hR := hR_walk_to L (by omega) (le_refl L)
    have hRrev := validWalk_reverse hR
    have hmid : Winit 3 = (fun i => (W (tstar + 1 + (L - (tstar + 1) - i))).filter (fun z => z ≤ M)) 0 := by
      simp only [Winit, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
      rw [Nat.sub_zero, show tstar + 1 + (L - (tstar + 1)) = L by omega, hlow_eq]
    rcases validWalk_concat hWinit hRrev hmid with ⟨Wcat, hWcat, hWcat0, hWcatL⟩
    have hM_end : M ∈ Wcat (3 + (L - (tstar + 1))) := by
      rw [hWcatL]
      rw [Nat.sub_self, Nat.add_zero]
      exact Finset.mem_filter.mpr ⟨hM_in, le_refl M⟩
    have hbd := pebble_reach_bound p (by omega) (3 + (L - (tstar + 1))) 0 Wcat hWcat (by simpa [Winit] using hWcat0) M hM_end
    omega
  · by_cases hlow_all : ∀ t, tstar ≤ t → t ≤ L → ((W t).filter (fun z => z ≤ M)).Nonempty
    · let T : ℕ → Finset ℕ := fun i => (W (tstar + i)).filter (fun z => M + 1 ≤ z)
      have hT0 : T 0 = ∅ := by simpa [T] using htstar_empty
      have hT_walk : ValidWalk p (M + 1) (L - tstar) T := by
        intro i hi
        have hstep := hW_p1 (tstar + i) (by omega)
        have hne1 := hlow_all (tstar + i) (by omega) (by omega)
        have hne2 := hlow_all (tstar + i + 1) (by omega) (by omega)
        have hcard1 : (T i).card ≤ p := by
          have htot := Finset.card_filter_add_card_filter_not (s := W (tstar + i)) (p := fun z => z ≤ M)
          have hneg : (W (tstar + i)).filter (fun z => ¬ z ≤ M) = T i := by
            ext z; simp only [T, Finset.mem_filter]; constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by omega⟩
          rw [hneg] at htot
          have hpos := Finset.card_pos.mpr hne1
          have hle := hstep.1
          omega
        have hcard2 : (T (i + 1)).card ≤ p := by
          have htot := Finset.card_filter_add_card_filter_not (s := W (tstar + i + 1)) (p := fun z => z ≤ M)
          have hneg : (W (tstar + i + 1)).filter (fun z => ¬ z ≤ M) = T (i + 1) := by
            ext z; simp only [T, Finset.mem_filter, show tstar + (i + 1) = tstar + i + 1 by omega]
            constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by omega⟩
          rw [hneg] at htot
          have hpos := Finset.card_pos.mpr hne2
          have hle := hstep.2.1
          omega
        refine ⟨hcard1, hcard2, fun z hz => (Finset.mem_filter.mp hz).2,
          fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
        rcases hstep.2.2.2.2 with heq | ⟨j, _, hpre, hST⟩
        · left; simp only [T, show tstar + (i + 1) = tstar + i + 1 by omega, heq]
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
                simp only [T, show tstar + (i + 1) = tstar + i + 1 by omega, hT', Finset.mem_filter, Finset.mem_insert]
                constructor
                · rintro ⟨rfl | hmem, hz⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨hmem, hz⟩
                · rintro (rfl | ⟨hmem, hz⟩)
                  · exact ⟨Or.inl rfl, hjM1⟩
                  · exact ⟨Or.inr hmem, hz⟩
              · right; ext z
                simp only [T, show tstar + (i + 1) = tstar + i + 1 by omega, hS', Finset.mem_filter, Finset.mem_insert]
                constructor
                · rintro ⟨rfl | hmem, hz⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨hmem, hz⟩
                · rintro (rfl | ⟨hmem, hz⟩)
                  · exact ⟨Or.inl rfl, hjM1⟩
                  · exact ⟨Or.inr hmem, hz⟩
          · left; ext z
            simp only [T, show tstar + (i + 1) = tstar + i + 1 by omega, Finset.mem_filter]
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
      have hTL_card : (T (L - tstar)).card ≤ p - 1 := by
        have htot := Finset.card_filter_add_card_filter_not (s := W L) (p := fun z => z ≤ M)
        have hneg : (W L).filter (fun z => ¬ z ≤ M) = T (L - tstar) := by
          ext z; simp only [T, show tstar + (L - tstar) = L by omega, Finset.mem_filter]
          constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by omega⟩
        rw [hneg] at htot
        have hWL_c : (W L).card ≤ p + 1 := by
          have := (hW_p1 (L - 1) (by omega)).2.1
          rwa [show L - 1 + 1 = L by omega] at this
        omega
      have hnT : n ∈ T (L - tstar) := by
        dsimp only [T]; rw [show tstar + (L - tstar) = L by omega]; exact Finset.mem_filter.mpr ⟨hn, hMn⟩
      have hstep_end : RevStep p (M + 1) (T (L - tstar)) (insert (n + 1) (T (L - tstar))) := by
        have h1c : (T (L - tstar)).card ≤ p := by omega
        have h2c : (insert (n + 1) (T (L - tstar))).card ≤ p := by
          have := Finset.card_insert_le (n + 1) (T (L - tstar)); omega
        refine ⟨h1c, h2c, fun z hz => (Finset.mem_filter.mp hz).2,
          fun z hz => by
            rcases Finset.mem_insert.mp hz with rfl | hmem
            · omega
            · exact (Finset.mem_filter.mp hmem).2,
          Or.inr ⟨n + 1, by omega, Or.inr (by simpa using hnT), Or.inl rfl⟩⟩
      let Tend : ℕ → Finset ℕ := fun i => if i = 0 then T (L - tstar) else insert (n + 1) (T (L - tstar))
      have hTend : ValidWalk p (M + 1) 1 Tend := fun i hi => by
        have hi0 : i = 0 := by omega
        subst hi0; simpa [Tend] using hstep_end
      rcases validWalk_concat hT_walk hTend (by simp [Tend]) with ⟨T', hT', hT'0, hT'L⟩
      have hn1_in : n + 1 ∈ T' (L - tstar + 1) := by rw [hT'L]; simp [Tend]
      have hbd := pebble_reach_bound p (by omega) (L - tstar + 1) (M + 1) T' hT' (hT'0.trans hT0) (n + 1) hn1_in
      omega
    · push Not at hlow_all
      rcases hlow_all with ⟨t2, ht2_ge, ht2_le, ht2_empty⟩
      have ht2_gt : tstar + 1 ≤ t2 := by
        by_contra hlt
        have heq : t2 = tstar := by omega
        have hM_ts : M ∈ W tstar := by
          have hstep := hW_p1 tstar (by omega)
          have hne := hhi_all (tstar + 1) (le_refl _) (by omega)
          rcases hstep.2.2.2.2 with heq' | ⟨j, _, hpre, hST⟩
          · rw [← heq'] at hne; rw [htstar_empty] at hne; simp at hne
          · rcases hST with hT | hS
            · have hj_ge : M + 1 ≤ j := by
                rcases hne with ⟨z, hz⟩
                have hzW := (Finset.mem_filter.mp hz).1
                have hzM := (Finset.mem_filter.mp hz).2
                rw [hT] at hzW
                rcases Finset.mem_insert.mp hzW with rfl | hprev
                · exact hzM
                · exfalso
                  have hmem : z ∈ (W tstar).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hprev, hzM⟩
                  rw [htstar_empty] at hmem
                  exact Finset.notMem_empty z hmem
              have hj_eq : j = M + 1 := by
                rcases hpre with rfl | hjm
                · omega
                · have hlt' : j - 1 < M + 1 := by
                    by_contra hge
                    have hmem : j - 1 ∈ (W tstar).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hjm, by omega⟩
                    rw [htstar_empty] at hmem
                    exact Finset.notMem_empty _ hmem
                  omega
              rcases hpre with h0 | hjm
              · omega
              · rwa [show M = j - 1 by omega]
            · exfalso
              rcases hne with ⟨z, hz⟩
              have hzW := (Finset.mem_filter.mp hz).1
              have hzM := (Finset.mem_filter.mp hz).2
              have hprev : z ∈ W tstar := by rw [hS]; exact Finset.mem_insert_of_mem hzW
              have hmem : z ∈ (W tstar).filter (fun u => M + 1 ≤ u) := Finset.mem_filter.mpr ⟨hprev, hzM⟩
              rw [htstar_empty] at hmem
              exact Finset.notMem_empty z hmem
        have hMin : M ∈ (W t2).filter (fun z => z ≤ M) := Finset.mem_filter.mpr ⟨heq ▸ hM_ts, le_refl M⟩
        rw [ht2_empty] at hMin
        exact Finset.notMem_empty M hMin
      have hR := hR_walk_to t2 ht2_gt ht2_le
      have hRrev := validWalk_reverse hR
      have hRrev0 : (fun i => (W (tstar + 1 + (t2 - (tstar + 1) - i))).filter (fun z => z ≤ M)) 0 = ∅ := by
        dsimp only
        rw [Nat.sub_zero, show tstar + 1 + (t2 - (tstar + 1)) = t2 by omega]
        exact ht2_empty
      have hM_end : M ∈ (fun i => (W (tstar + 1 + (t2 - (tstar + 1) - i))).filter (fun z => z ≤ M)) (t2 - (tstar + 1)) := by
        dsimp only
        rw [Nat.sub_self, Nat.add_zero]
        exact Finset.mem_filter.mpr ⟨hM_in, le_refl M⟩
      have hbd := pebble_reach_bound p (by omega) (t2 - (tstar + 1)) 0 _ hRrev hRrev0 M hM_end
      omega

lemma validWalk_add_bg {p a L : ℕ} {W : ℕ → Finset ℕ} (B : Finset ℕ)
    (hBdisj : ∀ x ∈ B, x < a)
    (hW : ValidWalk p a L W) (_hW0 : W 0 = ∅) (hBpre : a = 0 ∨ a - 1 ∈ B)
    (a0 : ℕ) (ha0 : a0 ≤ a) (hBa0 : ∀ x ∈ B, a0 ≤ x) :
    ValidWalk (p + B.card) a0 L (fun i => B ∪ W i) := by
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
    have hA1c : A1.card ≤ d - 1 := by dsimp only [A1]; have := Finset.card_insert_le 0 A0; omega
    have hA2c : A2.card ≤ d := by dsimp only [A2]; have := Finset.card_insert_le 1 A1; omega
    have hA3c : A3.card ≤ d - 1 := by dsimp only [A3]; have := Finset.card_insert_le 1 A0; omega
    have hA2_eq : A2 = insert 0 A3 := by dsimp only [A2, A1, A3]; exact Finset.insert_comm 1 0 A0
    refine ⟨W, ?_, by simp [W, A0], by simp [W, A3, A0, liftFin_insert]⟩
    intro i hi
    interval_cases i
    · simp only [W, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      exact ⟨by omega, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _,
        Or.inr ⟨0, le_refl 0, Or.inl rfl, Or.inl rfl⟩⟩
    · simp only [W, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
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
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L + 3, W', hW', hW'0.trans hW0, hW'L.trans (by simpa using hW30)⟩

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

lemma reachSet_no_both_ends {m d : ℕ} (hm3 : 3 ≤ m) (hd : 2 ≤ d) (hnot_lt : ¬ (m + 2 < 2 ^ d))
    (T : Finset (Fin m)) (h0 : ⟨0, by omega⟩ ∈ T) (hlast : ⟨m - 1, by omega⟩ ∈ T) :
    T ∉ reachSet m d := by
  classical
  unfold reachSet
  intro hTR
  rcases (Finset.mem_filter.mp hTR).2 with ⟨L, W, hW, hW0, hWL⟩
  have h1_in : 1 ∈ W L := by
    rw [hWL]
    exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, h0, by dsimp⟩
  have hm_in : m ∈ W L := by
    rw [hWL]
    exact Finset.mem_image.mpr ⟨⟨m - 1, by omega⟩, hlast, by dsimp; omega⟩
  by_cases hd2 : d = 2
  · subst hd2
    have hbd := pebble_reach_bound 2 (by omega) L 0 W hW hW0 m hm_in
    omega
  · exact pebble_no_one_and_top (by omega) hnot_lt hW hW0 h1_in hm_in

lemma multilin_eval_anchored_zero {m d : ℕ} (hm3 : 3 ≤ m) (hd : 2 ≤ d) (hnot_lt : ¬ (m + 2 < 2 ^ d))
    (A B C : MvPolynomial (Fin m) F)
    (hA : A = 0 ∨ A.totalDegree ≤ d - 2)
    (hB : B = 0 ∨ B.totalDegree ≤ d - 2)
    (hC : C = 0 ∨ C.totalDegree ≤ d - 2)
    (Q : Fin (m - 1) → MvPolynomial (Fin m) F)
    (hQ : ∀ k : Fin (m - 1), Q k = 0 ∨ (Q k).totalDegree ≤ d - 2)
    (G : Fin m → MvPolynomial (Fin m) F) :
    let R := reachSet m d
    let v0 : Fin m := ⟨0, by omega⟩
    let vl : Fin m := ⟨m - 1, by omega⟩
    (∑ S ∈ R, multilin (
      A * ((1 + MvPolynomial.X vl) * (1 + MvPolynomial.X v0)) +
      B * (MvPolynomial.X vl * (1 + MvPolynomial.X v0)) +
      C * (MvPolynomial.X vl * MvPolynomial.X v0) +
      (∑ k : Fin (m - 1), Q k * (MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩))) +
      ∑ v : Fin m, G v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) S) = 0 := by
  intro R v0 vl
  have hm_pos : 0 < m := by omega
  have hlin_mon : ∀ (f h : MvPolynomial (Fin m) F),
      (∀ α ∈ f.support, (∑ S ∈ R, multilin (MvPolynomial.monomial α (f.coeff α) * h) S) = 0) →
      (∑ S ∈ R, multilin (f * h) S) = 0 := by
    intro f h hall
    rw [MvPolynomial.as_sum f, Finset.sum_mul]
    simp_rw [multilin_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero hall
  have hcard_of_deg : ∀ {f : MvPolynomial (Fin m) F} {α : Fin m →₀ ℕ},
      f.totalDegree ≤ d - 2 → α ∈ f.support → α.support.card ≤ d - 2 := by
    intro f α hdeg hα
    have hle := MvPolynomial.le_totalDegree hα
    have hsc : α.support.card ≤ α.sum (fun _ e => e) := by
      rw [Finset.card_eq_sum_ones, Finsupp.sum]
      refine Finset.sum_le_sum fun v hv => ?_
      have hne : α v ≠ 0 := Finsupp.mem_support_iff.mp hv
      omega
    omega
  have hsupp_ins : ∀ (α : Fin m →₀ ℕ) (v : Fin m),
      (α + Finsupp.single v 1).support = insert v α.support := by
    intro α v; ext u
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
    by_cases hv : v = u
    · subst hv; simp
    · simp [hv, Ne.symm hv]
  have hsum_single : ∀ (c : F) (T : Finset (Fin m)),
      (∑ S ∈ R, if T = S then c else 0) = if T ∈ R then c else 0 := by
    intro c T
    by_cases hTR : T ∈ R
    · rw [Finset.sum_eq_single T]
      · simp [hTR]
      · intro S _ hne; simp [Ne.symm hne]
      · intro h; exact absurd hTR h
    · rw [Finset.sum_eq_zero]
      · simp [hTR]
      · intro S hSR; have hne : T ≠ S := fun h => hTR (h ▸ hSR); simp [hne]
  have hkill_1_v0 : ∀ (f : MvPolynomial (Fin m) F), (f = 0 ∨ f.totalDegree ≤ d - 2) →
      (∑ S ∈ R, multilin (f * (1 + MvPolynomial.X v0)) S) = 0 := by
    intro f hf
    rcases hf with rfl | hdeg
    · simp [multilin_zero]
    · refine hlin_mon f _ fun α hα => ?_
      have hcard := hcard_of_deg hdeg hα
      have hX0 : (MvPolynomial.X v0 : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single v0 1) 1 := rfl
      rw [mul_add, mul_one, hX0, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_add, multilin_monomial]
      rw [Finset.sum_add_distrib, hsupp_ins, hsum_single, hsum_single]
      by_cases h0 : v0 ∈ α.support
      · rw [Finset.insert_eq_of_mem h0]; split_ifs <;> simp [zmod2_add_self]
      · have hiff : α.support ∈ R ↔ insert v0 α.support ∈ R := reachSet_step0 hd hm_pos α.support hcard h0
        by_cases hmem : α.support ∈ R
        · simp [hmem, hiff.mp hmem, zmod2_add_self]
        · have hnot : insert v0 α.support ∉ R := fun h => hmem (hiff.mpr h)
          simp [hmem, hnot]
  have hkill_vl : ∀ (f : MvPolynomial (Fin m) F), (f = 0 ∨ f.totalDegree ≤ d - 2) →
      (∑ S ∈ R, multilin (f * MvPolynomial.X vl) S) = 0 := by
    intro f hf
    rcases hf with rfl | hdeg
    · simp [multilin_zero]
    · refine hlin_mon f _ fun α hα => ?_
      have hcard := hcard_of_deg hdeg hα
      have hXl : (MvPolynomial.X vl : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single vl 1) 1 := rfl
      rw [hXl, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_monomial]
      rw [hsupp_ins]
      have hTc : (insert vl α.support).card ≤ d - 1 := by have := Finset.card_insert_le vl α.support; omega
      have hnotR : insert vl α.support ∉ R := reachSet_sink (by omega) hnot_lt _ hTc hm_pos (Finset.mem_insert_self vl _)
      refine Finset.sum_eq_zero fun S hSR => ?_
      have hne : insert vl α.support ≠ S := fun h => hnotR (h ▸ hSR)
      simp [hne]
  have hkill_vl_v0 : ∀ (f : MvPolynomial (Fin m) F), (f = 0 ∨ f.totalDegree ≤ d - 2) →
      (∑ S ∈ R, multilin (f * (MvPolynomial.X vl * MvPolynomial.X v0)) S) = 0 := by
    intro f hf
    rcases hf with rfl | hdeg
    · simp [multilin_zero]
    · refine hlin_mon f _ fun α hα => ?_
      have hXl : (MvPolynomial.X vl : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single vl 1) 1 := rfl
      have hX0 : (MvPolynomial.X v0 : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single v0 1) 1 := rfl
      rw [← mul_assoc, hXl, MvPolynomial.monomial_mul_monomial, mul_one, hX0, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_monomial]
      rw [hsupp_ins, hsupp_ins]
      have hnotR : insert v0 (insert vl α.support) ∉ R :=
        reachSet_no_both_ends hm3 hd hnot_lt _ (Finset.mem_insert_self v0 _)
          (Finset.mem_insert_of_mem (Finset.mem_insert_self vl _))
      refine Finset.sum_eq_zero fun S hSR => ?_
      have hne : insert v0 (insert vl α.support) ≠ S := fun h => hnotR (h ▸ hSR)
      simp [hne]
  have hA0 : (∑ S ∈ R, multilin (A * ((1 + MvPolynomial.X vl) * (1 + MvPolynomial.X v0))) S) = 0 := by
    have heq : A * ((1 + MvPolynomial.X vl) * (1 + MvPolynomial.X v0)) =
        A * (1 + MvPolynomial.X v0) + A * MvPolynomial.X vl + A * (MvPolynomial.X vl * MvPolynomial.X v0) := by ring
    rw [heq]
    simp_rw [multilin_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hkill_1_v0 A hA, hkill_vl A hA, hkill_vl_v0 A hA]
    simp
  have hB0 : (∑ S ∈ R, multilin (B * (MvPolynomial.X vl * (1 + MvPolynomial.X v0))) S) = 0 := by
    have heq : B * (MvPolynomial.X vl * (1 + MvPolynomial.X v0)) =
        B * MvPolynomial.X vl + B * (MvPolynomial.X vl * MvPolynomial.X v0) := by ring
    rw [heq]
    simp_rw [multilin_add]
    rw [Finset.sum_add_distrib, hkill_vl B hB, hkill_vl_v0 B hB, add_zero]
  have hC0 : (∑ S ∈ R, multilin (C * (MvPolynomial.X vl * MvPolynomial.X v0)) S) = 0 :=
    hkill_vl_v0 C hC
  have hQ0 : ∀ k : Fin (m - 1),
      (∑ S ∈ R, multilin (Q k * (MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩))) S) = 0 := by
    intro k
    rcases hQ k with hQk0 | hQdeg
    · rw [hQk0]; simp [multilin_zero]
    · refine hlin_mon (Q k) _ fun α hα => ?_
      have hcard := hcard_of_deg hQdeg hα
      let k0 : Fin m := ⟨k.val, by omega⟩
      let k1 : Fin m := ⟨k.val + 1, by omega⟩
      have hX0 : (MvPolynomial.X k0 : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single k0 1) 1 := rfl
      have hX1 : (MvPolynomial.X k1 : MvPolynomial (Fin m) F) = MvPolynomial.monomial (Finsupp.single k1 1) 1 := rfl
      rw [mul_add, mul_one, mul_add, ← mul_assoc, hX0, MvPolynomial.monomial_mul_monomial, mul_one,
        hX1, MvPolynomial.monomial_mul_monomial, mul_one]
      simp_rw [multilin_add, multilin_monomial]
      rw [Finset.sum_add_distrib, hsupp_ins, hsupp_ins, hsupp_ins, hsum_single, hsum_single]
      let T : Finset (Fin m) := insert k0 α.support
      change (if T ∈ R then (Q k).coeff α else 0) + (if insert k1 T ∈ R then (Q k).coeff α else 0) = 0
      by_cases hk1 : k1 ∈ T
      · rw [Finset.insert_eq_of_mem hk1]; split_ifs <;> simp [zmod2_add_self]
      · have hTcard : T.card ≤ d - 1 := by dsimp only [T]; have := Finset.card_insert_le k0 α.support; omega
        have hk0T : k0 ∈ T := Finset.mem_insert_self k0 _
        have hiff : T ∈ R ↔ insert k1 T ∈ R :=
          reachSet_step_int (by omega) k0 (by dsimp only [k0]; omega) T hTcard hk0T hk1
        by_cases hmem : T ∈ R
        · simp [hmem, hiff.mp hmem, zmod2_add_self]
        · have hnot : insert k1 T ∉ R := fun h => hmem (hiff.mpr h)
          simp [hmem, hnot]
  have hG0 : (∑ S ∈ R, multilin (∑ v : Fin m, G v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) S) = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [multilin_sum]
    exact Finset.sum_eq_zero fun v _ => multilin_mul_bool_axiom (G v) v S
  simp_rw [multilin_add, multilin_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hA0, zero_add, hB0, zero_add, hC0, zero_add, Finset.sum_comm, Finset.sum_eq_zero fun k _ => hQ0 k, zero_add]
  simpa [multilin_sum] using hG0

def posFn (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt _ hn⟩

def prevFn (n : ℕ) (hn : 0 < n) (v : Fin n) : Fin n :=
  ⟨(v.val + n - 1) % n, Nat.mod_lt _ hn⟩

lemma posFn_ne {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) (i : Fin n) :
    i ≠ posFn n hn (i.val + 1) := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [posFn] at hv
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self] at hv; omega
  · have hlt : i.val + 1 < n := by have := i.2; omega
    rw [Nat.mod_eq_of_lt hlt] at hv; omega

lemma posFn_prevFn {n : ℕ} (hn : 0 < n) (v : Fin n) :
    posFn n hn ((prevFn n hn v).val + 1) = v := by
  apply Fin.ext
  dsimp only [posFn, prevFn]
  by_cases hv0 : v.val = 0
  · have hlt : n - 1 < n := by omega
    rw [hv0, Nat.zero_add, Nat.mod_eq_of_lt hlt, show n - 1 + 1 = n by omega, Nat.mod_self]
  · have h1 : v.val + n - 1 = n + (v.val - 1) := by omega
    have hlt : v.val - 1 < n := by have := v.2; omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hlt,
      show v.val - 1 + 1 = v.val by omega, Nat.mod_eq_of_lt v.2]

lemma prevFn_posFn {n : ℕ} (hn : 0 < n) (v : Fin n) :
    prevFn n hn (posFn n hn (v.val + 1)) = v := by
  apply Fin.ext
  dsimp only [posFn, prevFn]
  by_cases hlast : v.val + 1 = n
  · rw [hlast, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  · have hlt : v.val + 1 < n := by have := v.2; omega
    rw [Nat.mod_eq_of_lt hlt, show v.val + 1 + n - 1 = n + v.val by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt v.2]

lemma posFn_ne_prevFn {n : ℕ} (hn : 0 < n) (hn3 : 3 ≤ n) (v : Fin n) :
    posFn n hn (v.val + 1) ≠ prevFn n hn v := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [posFn, prevFn] at hv
  by_cases hv0 : v.val = 0
  · rw [hv0, Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
  · by_cases hlast : v.val + 1 = n
    · rw [hlast, Nat.mod_self] at hv
      have h1 : v.val + n - 1 = n + (v.val - 1) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hv; omega
    · have hlt : v.val + 1 < n := by have := v.2; omega
      have h1 : v.val + n - 1 = n + (v.val - 1) := by omega
      rw [Nat.mod_eq_of_lt hlt, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hv; omega

lemma posFn_add_one_eq_iff {n : ℕ} (hn : 0 < n) (u v : Fin n) :
    posFn n hn (u.val + 1) = v ↔ u = prevFn n hn v := by
  constructor
  · intro h; rw [← h, prevFn_posFn]
  · intro h; rw [h, posFn_prevFn]

def blockersFn (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) : Finset (Clause (Fin n)) :=
  let blocks := (Finset.univ : Finset (Fin n × (Bool × Bool))).filter
    (fun z => T z.1 z.2.1 z.2.2 = false)
  blocks.image (fun row =>
    ({(row.1, !row.2.1), (posFn n hn (row.1.val + 1), !row.2.2)} : Clause (Fin n)))

def rejectsFn (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) : Prop :=
  ¬ ∃ x : Fin n → Bool, ∀ i : Fin n, T i (x i) (x (posFn n hn (i.val + 1))) = true

def staticFn (n : ℕ) (axioms : Finset (Clause (Fin n))) (budget : ℕ) : Prop :=
  ∃ (q : Clause (Fin n) → MvPolynomial (Fin n) F) (b : Fin n → MvPolynomial (Fin n) F),
    (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (clausePoly C).totalDegree ≤ budget) ∧
    (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
    axioms.sum (fun C => q C * clausePoly C) +
      (∑ v, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 1

lemma blocker_mem_blockersFn {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    {i : Fin n} {a b : Bool} (h : T i a b = false) :
    ({(i, !a), (posFn n hn (i.val + 1), !b)} : Clause (Fin n)) ∈ blockersFn n hn T :=
  Finset.mem_image.mpr ⟨(i, a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

lemma blockersFn_deg2 {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) (T : Fin n → Bool → Bool → Bool)
    {C : Clause (Fin n)} (hC : C ∈ blockersFn n hn T) :
    (clausePoly C).totalDegree = 2 := by
  rcases Finset.mem_image.mp hC with ⟨⟨i, a, b⟩, _, rfl⟩
  exact totalDegree_clausePoly_pair (posFn_ne hn hn2 i) (!a) (!b)

lemma staticFn_ge2 {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) (T : Fin n → Bool → Bool → Bool) {d : ℕ}
    (hs : staticFn n (blockersFn n hn T) d) : 2 ≤ d := by
  rcases hs with ⟨q, b, hq, hb, hsum⟩
  by_contra hlt
  have hq0 : ∀ C ∈ blockersFn n hn T, q C = 0 := by
    intro C hC
    rcases hq C hC with h0 | hdeg
    · exact h0
    · rw [blockersFn_deg2 hn hn2 T hC] at hdeg; omega
  have hb0 : ∀ v : Fin n, b v = 0 := by
    intro v
    rcases hb v with h0 | hdeg
    · exact h0
    · omega
  have h1 : (blockersFn n hn T).sum (fun C => q C * clausePoly C) = 0 :=
    Finset.sum_eq_zero fun C hC => by rw [hq0 C hC, zero_mul]
  have h2 : (∑ v : Fin n, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 0 :=
    Finset.sum_eq_zero fun v _ => by rw [hb0 v, zero_mul]
  rw [h1, h2, add_zero] at hsum
  have hc := congrArg (fun p : MvPolynomial (Fin n) F => p.coeff (0 : Fin n →₀ ℕ)) hsum
  simp at hc

lemma staticFn_mono {n : ℕ} {axioms : Finset (Clause (Fin n))} {d1 d2 : ℕ}
    (hle : d1 ≤ d2) (hs : staticFn n axioms d1) : staticFn n axioms d2 := by
  rcases hs with ⟨q, b, hq, hb, hsum⟩
  refine ⟨q, b, fun C hC => ?_, fun v => ?_, hsum⟩
  · rcases hq C hC with h0 | hdeg
    · exact Or.inl h0
    · exact Or.inr (le_trans hdeg hle)
  · rcases hb v with h0 | hdeg
    · exact Or.inl h0
    · exact Or.inr (le_trans hdeg hle)

def anchoredTable (n : ℕ) : Fin n → Bool → Bool → Bool :=
  fun i a b => if i.val = 0 then (!a) && b else (!a) || b

lemma anchoredTable_rejects {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) :
    rejectsFn n hn (anchoredTable n) := by
  rintro ⟨x, hx⟩
  have h0 := hx ⟨0, hn⟩
  have hpos0 : posFn n hn (0 + 1) = ⟨1, by omega⟩ := by
    apply Fin.ext; dsimp only [posFn]; exact Nat.mod_eq_of_lt (by omega)
  simp only [anchoredTable, hpos0, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at h0
  have hx0 : x ⟨0, hn⟩ = false := h0.1
  have hx1 : x ⟨1, by omega⟩ = true := h0.2
  have hall : ∀ k : ℕ, 1 ≤ k → (hk : k < n) → x ⟨k, hk⟩ = true := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro h1 hlt
      by_cases hk0 : k = 0
      · subst hk0; exact hx1
      · have hprev := ih (by omega) (by omega)
        have hstep := hx ⟨k, by omega⟩
        have hposk : posFn n hn (k + 1) = ⟨k + 1, hlt⟩ := by
          apply Fin.ext; dsimp only [posFn]; exact Nat.mod_eq_of_lt hlt
        simp only [anchoredTable, hk0, ↓reduceIte, hposk, hprev, Bool.not_true, Bool.false_or] at hstep
        exact hstep
  have hlast_true := hall (n - 1) (by omega) (by omega)
  have hlast_step := hx ⟨n - 1, by omega⟩
  have hpos_last : posFn n hn (n - 1 + 1) = ⟨0, hn⟩ := by
    apply Fin.ext; dsimp only [posFn]; rw [show n - 1 + 1 = n by omega, Nat.mod_self]
  have hne0 : n - 1 ≠ 0 := by omega
  simp only [anchoredTable, hne0, ↓reduceIte, hpos_last, hlast_true, hx0, Bool.not_true, Bool.false_or] at hlast_step
  exact Bool.false_ne_true hlast_step

lemma anchored_static_lower {n d : ℕ} (hn : 0 < n) (hn3 : 3 ≤ n)
    (hs : staticFn n (blockersFn n hn (anchoredTable n)) d) : n + 2 < 2 ^ d := by
  classical
  have hd2 := staticFn_ge2 hn (by omega) (anchoredTable n) hs
  rcases hs with ⟨q, b, hq, hb, hsum⟩
  let φ : Fin n → Fin n := prevFn n hn
  let ρ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun v => MvPolynomial.X (φ v))
  have hρ_deg : ∀ f : MvPolynomial (Fin n) F, (ρ f).totalDegree ≤ f.totalDegree :=
    fun f => eval2Hom_totalDegree_le (fun v => MvPolynomial.X (φ v))
      (fun v => by simp [MvPolynomial.totalDegree_X]) f
  have hρ_X : ∀ v : Fin n, ρ (MvPolynomial.X v) = MvPolynomial.X (φ v) :=
    fun v => MvPolynomial.eval₂Hom_X' _ _ v
  let v0 : Fin n := ⟨0, hn⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let vl : Fin n := ⟨n - 1, by omega⟩
  have hφ0 : φ v0 = vl := by
    apply Fin.ext; dsimp only [φ, prevFn, v0, vl]; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  have hφ_succ : ∀ k : Fin (n - 1), φ ⟨k.val + 1, by omega⟩ = ⟨k.val, by omega⟩ := by
    intro k
    apply Fin.ext; dsimp only [φ, prevFn]
    rw [show k.val + 1 + n - 1 = n + k.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hφ1 : φ v1 = v0 := by
    have := hφ_succ ⟨0, by omega⟩; simpa [v1, v0] using this
  have hpos_small : ∀ (j : ℕ) (hj : j < n), posFn n hn j = ⟨j, hj⟩ := fun j hj => by
    apply Fin.ext; dsimp only [posFn]; exact Nat.mod_eq_of_lt hj
  let C00 : Clause (Fin n) := {(v0, true), (v1, true)}
  let C10 : Clause (Fin n) := {(v0, false), (v1, true)}
  let C11 : Clause (Fin n) := {(v0, false), (v1, false)}
  let Cint : Fin (n - 1) → Clause (Fin n) := fun k =>
    {(⟨k.val + 1, by omega⟩, false), (posFn n hn (k.val + 2), true)}
  have hC00_mem : C00 ∈ blockersFn n hn (anchoredTable n) := by
    have h := blocker_mem_blockersFn hn (T := anchoredTable n) (i := v0) (a := false) (b := false)
      (by simp [anchoredTable, v0])
    simpa [C00, v0, v1, hpos_small 1 (by omega)] using h
  have hC10_mem : C10 ∈ blockersFn n hn (anchoredTable n) := by
    have h := blocker_mem_blockersFn hn (T := anchoredTable n) (i := v0) (a := true) (b := false)
      (by simp [anchoredTable, v0])
    simpa [C10, v0, v1, hpos_small 1 (by omega)] using h
  have hC11_mem : C11 ∈ blockersFn n hn (anchoredTable n) := by
    have h := blocker_mem_blockersFn hn (T := anchoredTable n) (i := v0) (a := true) (b := true)
      (by simp [anchoredTable, v0])
    simpa [C11, v0, v1, hpos_small 1 (by omega)] using h
  have hCint_mem : ∀ k : Fin (n - 1), Cint k ∈ blockersFn n hn (anchoredTable n) := by
    intro k
    have h := blocker_mem_blockersFn hn (T := anchoredTable n) (i := ⟨k.val + 1, by omega⟩) (a := true) (b := false)
      (by simp [anchoredTable])
    simpa [Cint] using h
  have hbl_eq : blockersFn n hn (anchoredTable n) = {C00, C10, C11} ∪ Finset.univ.image Cint := by
    ext C
    constructor
    · intro hC
      rcases Finset.mem_image.mp hC with ⟨⟨i, a, b⟩, hmem, rfl⟩
      have hall := (Finset.mem_filter.mp hmem).2
      by_cases hi0 : i.val = 0
      · have hieq : i = v0 := Fin.ext hi0
        subst hieq
        simp only [anchoredTable, v0, ↓reduceIte] at hall
        have hpos1 : posFn n hn (0 + 1) = v1 := hpos_small 1 (by omega)
        cases a <;> cases b
        · exact Finset.mem_union_left _ (by simp [C00, v0, hpos1])
        · simp at hall
        · exact Finset.mem_union_left _ (by simp [C10, v0, hpos1])
        · exact Finset.mem_union_left _ (by simp [C11, v0, hpos1])
      · simp only [anchoredTable, hi0, ↓reduceIte] at hall
        have hab : a = true ∧ b = false := by cases a <;> cases b <;> simp at hall ⊢
        rcases hab with ⟨rfl, rfl⟩
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩)
        have hieq : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
        have hpos_eq : posFn n hn (i.val - 1 + 2) = posFn n hn (i.val + 1) := by
          congr 1; omega
        simp [Cint, hieq, hpos_eq]
    · intro hC
      rcases Finset.mem_union.mp hC with h1 | h2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
        rcases h1 with rfl | rfl | rfl
        · exact hC00_mem
        · exact hC10_mem
        · exact hC11_mem
      · rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
        exact hCint_mem k
  have hv01 : v0 ≠ v1 := by intro h; have := congrArg Fin.val h; simp [v0, v1] at this
  have hC00_ne_C10 : C00 ≠ C10 := by
    intro h
    have hmem : (v0, true) ∈ C10 := h ▸ Finset.mem_insert_self _ _
    simp only [C10, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2
    · simp at h1
    · exact hv01 (congrArg Prod.fst h2)
  have hC00_ne_C11 : C00 ≠ C11 := by
    intro h
    have hmem : (v0, true) ∈ C11 := h ▸ Finset.mem_insert_self _ _
    simp only [C11, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2
    · simp at h1
    · simp at h2
  have hC10_ne_C11 : C10 ≠ C11 := by
    intro h
    have hmem : (v1, true) ∈ C11 := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [C11, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2
    · simp at h1
    · simp at h2
  have hdisj : Disjoint ({C00, C10, C11} : Finset (Clause (Fin n))) (Finset.univ.image Cint) := by
    rw [Finset.disjoint_left]
    intro C h1 h2
    rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h | h
    · have hmem : (v0, true) ∈ Cint k := h ▸ Finset.mem_insert_self _ _
      simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · simp at h'
      · have hpos_k : posFn n hn (k.val + 2) = v0 := (congrArg Prod.fst h').symm
        have hkl : k.val + 1 = n - 1 := by
          have := congrArg Fin.val hpos_k; dsimp only [posFn, v0] at this
          by_cases hklt : k.val + 2 < n
          · rw [Nat.mod_eq_of_lt hklt] at this; omega
          · omega
        have hmem1 : (v1, true) ∈ Cint k := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem1
        rcases hmem1 with h'' | h''
        · simp at h''
        · have := (congrArg Prod.fst h'').trans hpos_k; exact hv01.symm this
    · have hmem : (v0, false) ∈ Cint k := h ▸ Finset.mem_insert_self _ _
      simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · have := congrArg (fun p : Fin n × Bool => p.1.val) h'; simp [v0] at this
      · simp at h'
    · have hmem : (v1, false) ∈ Cint k := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · have hk0 : k.val = 0 := by have := congrArg (fun p : Fin n × Bool => p.1.val) h'; simp [v1] at this; omega
        have hmem0 : (v0, false) ∈ Cint k := h ▸ Finset.mem_insert_self _ _
        simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem0
        rcases hmem0 with h'' | h''
        · have := congrArg (fun p : Fin n × Bool => p.1.val) h''; simp [v0] at this
        · simp at h''
      · simp at h'
  have hCint_inj : Function.Injective Cint := by
    intro k1 k2 h
    have hmem : ((⟨k1.val + 1, by omega⟩ : Fin n), false) ∈ Cint k2 := h ▸ Finset.mem_insert_self _ _
    simp only [Cint, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2
    · have := congrArg (fun p : Fin n × Bool => p.1.val) h1; dsimp at this; exact Fin.ext (by omega)
    · simp at h2
  have hρ_C00 : ρ (clausePoly C00) = (1 + MvPolynomial.X vl) * (1 + MvPolynomial.X v0) := by
    rw [clausePoly_pair hv01]
    simp [map_mul, map_add, map_one, hρ_X, hφ0, hφ1]
  have hρ_C10 : ρ (clausePoly C10) = MvPolynomial.X vl * (1 + MvPolynomial.X v0) := by
    rw [clausePoly_pair hv01]
    simp [map_mul, map_add, map_one, hρ_X, hφ0, hφ1]
  have hρ_C11 : ρ (clausePoly C11) = MvPolynomial.X vl * MvPolynomial.X v0 := by
    rw [clausePoly_pair hv01]
    simp [map_mul, hρ_X, hφ0, hφ1]
  have hρ_Cint : ∀ k : Fin (n - 1),
      ρ (clausePoly (Cint k)) = MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩) := by
    intro k
    have hne : (⟨k.val + 1, by omega⟩ : Fin n) ≠ posFn n hn (k.val + 2) :=
      posFn_ne hn (by omega) ⟨k.val + 1, by omega⟩
    rw [clausePoly_pair hne]
    have hφ2 : φ (posFn n hn (k.val + 2)) = ⟨k.val + 1, by omega⟩ := by
      have := prevFn_posFn hn ⟨k.val + 1, by omega⟩
      simpa [φ] using this
    simp [map_mul, map_add, map_one, hρ_X, hφ_succ k, hφ2]
  have hsum_ρ := congrArg ρ hsum
  rw [map_add, map_sum, map_sum, map_one, hbl_eq, Finset.sum_union hdisj,
    Finset.sum_insert (by simp [hC00_ne_C10, hC00_ne_C11]),
    Finset.sum_insert (by simp [hC10_ne_C11]), Finset.sum_singleton,
    Finset.sum_image (fun k1 _ k2 _ h => hCint_inj h)] at hsum_ρ
  simp only [map_mul, hρ_C00, hρ_C10, hρ_C11, hρ_Cint] at hsum_ρ
  have hbool_ρ : (∑ v : Fin n, ρ (b v) * ρ (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) =
      ∑ u : Fin n, ρ (b (posFn n hn (u.val + 1))) * (MvPolynomial.X u * MvPolynomial.X u + MvPolynomial.X u) := by
    refine Finset.sum_bij (fun v _ => φ v) (fun _ _ => Finset.mem_univ _)
      (fun v1 _ v2 _ h => by
        have := congrArg (fun u : Fin n => posFn n hn (u.val + 1)) h
        simpa [φ, posFn_prevFn] using this)
      (fun u _ => ⟨posFn n hn (u.val + 1), Finset.mem_univ _, prevFn_posFn hn u⟩)
      (fun v _ => by simp [map_add, map_mul, hρ_X, φ, posFn_prevFn])
  rw [hbool_ρ] at hsum_ρ
  by_contra hnot_lt
  have hA : ρ (q C00) = 0 ∨ (ρ (q C00)).totalDegree ≤ d - 2 := by
    rcases hq C00 hC00_mem with h0 | hd
    · left; rw [h0, map_zero]
    · right; have := hρ_deg (q C00); rw [blockersFn_deg2 hn (by omega) _ hC00_mem] at hd; omega
  have hB : ρ (q C10) = 0 ∨ (ρ (q C10)).totalDegree ≤ d - 2 := by
    rcases hq C10 hC10_mem with h0 | hd
    · left; rw [h0, map_zero]
    · right; have := hρ_deg (q C10); rw [blockersFn_deg2 hn (by omega) _ hC10_mem] at hd; omega
  have hC : ρ (q C11) = 0 ∨ (ρ (q C11)).totalDegree ≤ d - 2 := by
    rcases hq C11 hC11_mem with h0 | hd
    · left; rw [h0, map_zero]
    · right; have := hρ_deg (q C11); rw [blockersFn_deg2 hn (by omega) _ hC11_mem] at hd; omega
  have hQ : ∀ k : Fin (n - 1), ρ (q (Cint k)) = 0 ∨ (ρ (q (Cint k))).totalDegree ≤ d - 2 := by
    intro k
    rcases hq (Cint k) (hCint_mem k) with h0 | hd
    · left; rw [h0, map_zero]
    · right; have := hρ_deg (q (Cint k)); rw [blockersFn_deg2 hn (by omega) _ (hCint_mem k)] at hd; omega
  have hzero := multilin_eval_anchored_zero hn3 hd2 hnot_lt
    (ρ (q C00)) (ρ (q C10)) (ρ (q C11)) hA hB hC (fun k => ρ (q (Cint k))) hQ
    (fun u => ρ (b (posFn n hn (u.val + 1))))
  have heq_sum :
      ρ (q C00) * ((1 + MvPolynomial.X vl) * (1 + MvPolynomial.X v0)) +
      ρ (q C10) * (MvPolynomial.X vl * (1 + MvPolynomial.X v0)) +
      ρ (q C11) * (MvPolynomial.X vl * MvPolynomial.X v0) +
      (∑ k : Fin (n - 1), ρ (q (Cint k)) * (MvPolynomial.X ⟨k.val, by omega⟩ * (1 + MvPolynomial.X ⟨k.val + 1, by omega⟩))) +
      (∑ u : Fin n, ρ (b (posFn n hn (u.val + 1))) * (MvPolynomial.X u * MvPolynomial.X u + MvPolynomial.X u)) = 1 := by
    rw [add_assoc (ρ (q C00) * ((1 + MvPolynomial.X vl) * (1 + MvPolynomial.X v0)))]
    exact hsum_ρ
  dsimp only at hzero
  rw [heq_sum] at hzero
  have hone : (∑ S ∈ reachSet n d, multilin (1 : MvPolynomial (Fin n) F) S) = 1 := by
    simp_rw [multilin_one]
    rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
    · simp
    · intro S _ hne; simp [hne]
    · intro h; exact absurd (reachSet_empty n d) h
  rw [hone] at hzero
  exact absurd hzero (by decide)

def IsOddTwist {n : ℕ} (T : Fin n → Bool → Bool → Bool) : Prop :=
  ∃ f : Fin n → Bool,
    (∀ i a b, T i a b = !(a ^^ b ^^ f i)) ∧
    (∑ i : Fin n, if f i = true then (1 : F) else 0) = 1

lemma oddTwist_row_eq {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} {f : Fin n → Bool}
    (hf : ∀ i a b, T i a b = !(a ^^ b ^^ f i)) (i : Fin n) :
    let v := posFn n hn (i.val + 1)
    let C1 : Clause (Fin n) := {(i, true), (v, f i)}
    let C2 : Clause (Fin n) := {(i, false), (v, !(f i))}
    C1 ∈ blockersFn n hn T ∧ C2 ∈ blockersFn n hn T ∧ C1 ≠ C2 ∧
    clausePoly C1 + clausePoly C2 =
      (if f i = true then (1 : MvPolynomial (Fin n) F) else 0) + MvPolynomial.X i + MvPolynomial.X v := by
  intro v C1 C2
  have hne : i ≠ v := posFn_ne hn hn2 i
  have h1 : C1 ∈ blockersFn n hn T := by
    have hT : T i false (!(f i)) = false := by rw [hf]; cases f i <;> decide
    simpa [C1, v] using blocker_mem_blockersFn hn hT
  have h2 : C2 ∈ blockersFn n hn T := by
    have hT : T i true (f i) = false := by rw [hf]; cases f i <;> decide
    simpa [C2, v] using blocker_mem_blockersFn hn hT
  have hCne : C1 ≠ C2 := by
    intro h
    have hmem : (i, true) ∈ C2 := h ▸ Finset.mem_insert_self _ _
    simp only [C2, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · simp at h'
    · exact hne (congrArg Prod.fst h')
  refine ⟨h1, h2, hCne, ?_⟩
  rw [clausePoly_pair hne, clausePoly_pair hne]
  cases hfi : f i
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    calc
      (1 + MvPolynomial.X i) * MvPolynomial.X v + MvPolynomial.X i * (1 + MvPolynomial.X v)
          = (0 + MvPolynomial.X i + MvPolynomial.X v) + (2 : MvPolynomial (Fin n) F) * (MvPolynomial.X i * MvPolynomial.X v) := by ring
      _ = 0 + MvPolynomial.X i + MvPolynomial.X v := by rw [mv_two_eq_zero, zero_mul, add_zero]
  · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
    calc
      (1 + MvPolynomial.X i) * (1 + MvPolynomial.X v) + MvPolynomial.X i * MvPolynomial.X v
          = (1 + MvPolynomial.X i + MvPolynomial.X v) + (2 : MvPolynomial (Fin n) F) * (MvPolynomial.X i * MvPolynomial.X v) := by ring
      _ = 1 + MvPolynomial.X i + MvPolynomial.X v := by rw [mv_two_eq_zero, zero_mul, add_zero]

lemma oddTwist_sum_eq_one {n : ℕ} (hn : 0 < n) {f : Fin n → Bool}
    (hodd : (∑ i : Fin n, if f i = true then (1 : F) else 0) = 1) :
    (∑ i : Fin n, ((if f i = true then (1 : MvPolynomial (Fin n) F) else 0) +
      MvPolynomial.X i + MvPolynomial.X (posFn n hn (i.val + 1)))) = 1 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hXeq : (∑ i : Fin n, (MvPolynomial.X (posFn n hn (i.val + 1)) : MvPolynomial (Fin n) F)) =
      ∑ i : Fin n, MvPolynomial.X i := by
    refine Finset.sum_bij (fun i _ => posFn n hn (i.val + 1)) (fun _ _ => Finset.mem_univ _)
      (fun i1 _ i2 _ h => by
        have := congrArg (prevFn n hn) h
        simpa [prevFn_posFn] using this)
      (fun u _ => ⟨prevFn n hn u, Finset.mem_univ _, posFn_prevFn hn u⟩)
      (fun _ _ => rfl)
  rw [hXeq, add_assoc, mv_add_self, add_zero]
  have hc : (∑ i : Fin n, if f i = true then (1 : MvPolynomial (Fin n) F) else 0) =
      MvPolynomial.C (∑ i : Fin n, if f i = true then (1 : F) else 0) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases f i <;> simp
  rw [hc, hodd, map_one]

lemma oddTwist_static2 {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} (h : IsOddTwist T) :
    staticFn n (blockersFn n hn T) 2 := by
  classical
  rcases h with ⟨f, hf, hodd⟩
  let C1 : Fin n → Clause (Fin n) := fun i => {(i, true), (posFn n hn (i.val + 1), f i)}
  let C2 : Fin n → Clause (Fin n) := fun i => {(i, false), (posFn n hn (i.val + 1), !(f i))}
  let qi : Fin n → Clause (Fin n) → MvPolynomial (Fin n) F := fun i C =>
    if C = C1 i ∨ C = C2 i then 1 else 0
  let q : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => ∑ i : Fin n, qi i C
  refine ⟨q, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
  · intro C hC
    right
    rw [blockersFn_deg2 hn hn2 T hC]
    have hdeg0 : (q C).totalDegree ≤ 0 := by
      refine le_trans (totalDegree_finset_sum_le _ _) ?_
      rw [Finset.sup_le_iff]
      intro i _
      dsimp only [qi]; split_ifs <;> simp
    omega
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    have hcomm : (blockersFn n hn T).sum (fun C => q C * clausePoly C) =
        ∑ i : Fin n, (blockersFn n hn T).sum (fun C => qi i C * clausePoly C) := by
      simp_rw [q, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hcomm]
    have hrow : ∀ i : Fin n, (blockersFn n hn T).sum (fun C => qi i C * clausePoly C) =
        (if f i = true then (1 : MvPolynomial (Fin n) F) else 0) +
          MvPolynomial.X i + MvPolynomial.X (posFn n hn (i.val + 1)) := by
      intro i
      rcases oddTwist_row_eq hn hn2 hf i with ⟨h1, h2, hne, heq⟩
      rw [← Finset.sum_subset (s₁ := {C1 i, C2 i}) (by
        intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
        rcases hC with rfl | rfl; exact h1; exact h2)]
      · rw [Finset.sum_pair hne]
        simp only [qi, C1, C2, true_or, or_true, ↓reduceIte, one_mul]
        exact heq
      · intro C _ hnot
        have h' : ¬ (C = C1 i ∨ C = C2 i) := by simpa using hnot
        simp [qi, h']
    simp_rw [hrow]
    exact oddTwist_sum_eq_one hn hodd

lemma pc_sum_derivable {ι V : Type} {G : Set (MvPolynomial V F)} {B : ℕ}
    (s : Finset ι) (f : ι → MvPolynomial V F)
    (hf : ∀ i ∈ s, PCDerivable G B (f i)) :
    PCDerivable G B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact PCDerivable.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PCDerivable.add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma oddTwist_pc2 {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} (h : IsOddTwist T) :
    PCRefutable (cnfSystem (↑(blockersFn n hn T) : Set (Clause (Fin n)))) 2 := by
  rcases h with ⟨f, hf, hodd⟩
  unfold PCRefutable
  rw [← oddTwist_sum_eq_one hn hodd]
  refine pc_sum_derivable Finset.univ _ fun i _ => ?_
  rcases oddTwist_row_eq hn hn2 hf i with ⟨h1, h2, _, heq⟩
  rw [← heq]
  exact PCDerivable.add
    (PCDerivable.ax (Or.inr ⟨_, h1, rfl⟩) (by rw [blockersFn_deg2 hn hn2 T h1]))
    (PCDerivable.ax (Or.inr ⟨_, h2, rfl⟩) (by rw [blockersFn_deg2 hn hn2 T h2]))

def InitUnit {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (v : Fin n) (a : Bool) : Prop :=
  (T v a false = false ∧ T v a true = false) ∨
  (T (prevFn n hn v) false a = false ∧ T (prevFn n hn v) true a = false)

def StepImp {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (u : Fin n) (a : Bool) (v : Fin n) (b : Bool) : Prop :=
  (v = posFn n hn (u.val + 1) ∧ T u a (!b) = false) ∨
  (u = posFn n hn (v.val + 1) ∧ T v (!b) a = false)

lemma stepImp_contrapose {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    {u v : Fin n} {a b : Bool} (h : StepImp hn T u a v b) :
    StepImp hn T v (!b) u (!a) := by
  rcases h with ⟨rfl, hT⟩ | ⟨rfl, hT⟩
  · right; exact ⟨rfl, by simpa using hT⟩
  · left; exact ⟨rfl, by simpa using hT⟩

lemma initUnit_clauses {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) {T : Fin n → Bool → Bool → Bool}
    {v : Fin n} {a : Bool} (h : InitUnit hn T v a) :
    ∃ C1 C2 : Clause (Fin n), C1 ∈ blockersFn n hn T ∧ C2 ∈ blockersFn n hn T ∧ C1 ≠ C2 ∧
      clausePoly C1 + clausePoly C2 = litPoly v a := by
  rcases h with ⟨hf, ht⟩ | ⟨hf, ht⟩
  · let w := posFn n hn (v.val + 1)
    have hne : v ≠ w := posFn_ne hn hn2 v
    refine ⟨{(v, !a), (w, true)}, {(v, !a), (w, false)},
      blocker_mem_blockersFn hn hf, blocker_mem_blockersFn hn ht, ?_, ?_⟩
    · intro heq
      have hmem : (w, true) ∈ ({(v, !a), (w, false)} : Clause (Fin n)) :=
        heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h2
      · exact hne.symm (congrArg Prod.fst h1)
      · simp at h2
    · rw [show ({(v, !a), (w, true)} : Clause (Fin n)) = {(v, !a), (w, !false)} by rfl,
        show ({(v, !a), (w, false)} : Clause (Fin n)) = {(v, !a), (w, !true)} by rfl,
        clausePoly_blocker hne, clausePoly_blocker hne, ← mul_add,
        show litPoly w false + litPoly w true = 1 from litPoly_add_not w false, mul_one]
  · let u := prevFn n hn v
    have hpos : posFn n hn (u.val + 1) = v := posFn_prevFn hn v
    have hne : u ≠ v := by rw [← hpos]; exact posFn_ne hn hn2 u
    refine ⟨{(u, true), (v, !a)}, {(u, false), (v, !a)},
      by simpa [u, hpos] using blocker_mem_blockersFn hn hf,
      by simpa [u, hpos] using blocker_mem_blockersFn hn ht, ?_, ?_⟩
    · intro heq
      have hmem : (u, true) ∈ ({(u, false), (v, !a)} : Clause (Fin n)) :=
        heq ▸ Finset.mem_insert_self _ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h2
      · simp at h1
      · exact hne (congrArg Prod.fst h2)
    · rw [show ({(u, true), (v, !a)} : Clause (Fin n)) = {(u, !false), (v, !a)} by rfl,
        show ({(u, false), (v, !a)} : Clause (Fin n)) = {(u, !true), (v, !a)} by rfl,
        clausePoly_blocker hne, clausePoly_blocker hne, ← add_mul,
        show litPoly u false + litPoly u true = 1 from litPoly_add_not u false, one_mul]

lemma stepImp_clause {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) {T : Fin n → Bool → Bool → Bool}
    {u v : Fin n} {a b : Bool} (h : StepImp hn T u a v b) :
    ∃ C : Clause (Fin n), C ∈ blockersFn n hn T ∧ clausePoly C = litPoly u a * litPoly v (!b) := by
  rcases h with ⟨rfl, hT⟩ | ⟨rfl, hT⟩
  · refine ⟨{(u, !a), (posFn n hn (u.val + 1), !(!b))}, blocker_mem_blockersFn hn hT, ?_⟩
    exact clausePoly_blocker (posFn_ne hn hn2 u) a (!b)
  · refine ⟨{(v, !(!b)), (posFn n hn (v.val + 1), !a)}, blocker_mem_blockersFn hn hT, ?_⟩
    rw [clausePoly_blocker (posFn_ne hn hn2 v) (!b) a, mul_comm]

inductive UnitDeriv {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) : Fin n → Bool → Prop
  | init {v a} : InitUnit hn T v a → UnitDeriv hn T v a
  | step {u a v b} : UnitDeriv hn T u a → StepImp hn T u (!a) v (!b) → UnitDeriv hn T v b

lemma pc_mul_litPoly {V : Type} {G : Set (MvPolynomial V F)} {p : MvPolynomial V F}
    (hp : PCDerivable G 2 p) (hdeg : p.totalDegree ≤ 1) (v : V) (b : Bool) :
    PCDerivable G 2 (p * litPoly v b) := by
  have hXp : (MvPolynomial.X v * p).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_mul _ _) (by simp [MvPolynomial.totalDegree_X]; omega)
  cases b
  · simp only [litPoly, Bool.false_eq_true, ↓reduceIte]
    rw [show p * (1 + MvPolynomial.X v) = p + MvPolynomial.X v * p by ring]
    exact PCDerivable.add hp (PCDerivable.mulX v hp hXp)
  · simp only [litPoly, ↓reduceIte]
    rw [mul_comm]
    exact PCDerivable.mulX v hp hXp

lemma unitDeriv_to_pc {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) {T : Fin n → Bool → Bool → Bool}
    {v : Fin n} {a : Bool} (h : UnitDeriv hn T v a) :
    PCDerivable (cnfSystem (↑(blockersFn n hn T) : Set (Clause (Fin n)))) 2 (litPoly v a) := by
  induction h with
  | init hi =>
    rcases initUnit_clauses hn hn2 hi with ⟨C1, C2, h1, h2, _, heq⟩
    rw [← heq]
    exact PCDerivable.add
      (PCDerivable.ax (Or.inr ⟨C1, h1, rfl⟩) (by rw [blockersFn_deg2 hn hn2 T h1]))
      (PCDerivable.ax (Or.inr ⟨C2, h2, rfl⟩) (by rw [blockersFn_deg2 hn hn2 T h2]))
  | @step u a' v' b' _ hst ih =>
    rcases stepImp_clause hn hn2 hst with ⟨C, hC, hCeq⟩
    have hmul := pc_mul_litPoly ih (totalDegree_litPoly u a') v' b'
    have hax : PCDerivable (cnfSystem (↑(blockersFn n hn T) : Set (Clause (Fin n)))) 2 (clausePoly C) :=
      PCDerivable.ax (Or.inr ⟨C, hC, rfl⟩) (by rw [blockersFn_deg2 hn hn2 T hC])
    have hsum := PCDerivable.add hmul hax
    have heq : litPoly u a' * litPoly v' b' + clausePoly C = litPoly v' b' := by
      rw [hCeq, Bool.not_not, ← add_mul, litPoly_add_not, one_mul]
    rwa [heq] at hsum

lemma bool_mat_has_double (m00 m01 m10 m11 : Bool)
    (hr0 : m00 = true ∨ m01 = true) (hr1 : m10 = true ∨ m11 = true)
    (hc0 : m00 = true ∨ m10 = true) (hc1 : m01 = true ∨ m11 = true)
    (hnb0 : ¬ (m00 = true ∧ m01 = false ∧ m10 = false ∧ m11 = true))
    (hnb1 : ¬ (m00 = false ∧ m01 = true ∧ m10 = true ∧ m11 = false)) :
    (m00 = true ∧ m01 = true) ∨ (m10 = true ∧ m11 = true) := by
  revert hr0 hr1 hc0 hc1 hnb0 hnb1
  cases m00 <;> cases m01 <;> cases m10 <;> cases m11 <;> decide

lemma rejects_not_oddTwist_unit_contra {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} (hrej : rejectsFn n hn T) (hnot : ¬ IsOddTwist T) :
    ∃ w : Fin n, UnitDeriv hn T w false ∧ UnitDeriv hn T w true := by
  classical
  by_contra hno
  push Not at hno
  let U : Fin n → Bool → Prop := fun v a => ¬ UnitDeriv hn T v a
  have hU_nonempty : ∀ v : Fin n, ∃ a : Bool, U v a := by
    intro v
    by_cases hf : UnitDeriv hn T v false
    · exact ⟨true, hno v hf⟩
    · exact ⟨false, hf⟩
  have hU_row : ∀ (i : Fin n) (a : Bool), U i a → ∃ b : Bool, T i a b = true := by
    intro i a hUa
    by_contra hall
    have hf : T i a false = false := by
      cases h : T i a false
      · rfl
      · exact absurd ⟨false, h⟩ hall
    have ht : T i a true = false := by
      cases h : T i a true
      · rfl
      · exact absurd ⟨true, h⟩ hall
    exact hUa (UnitDeriv.init (Or.inl ⟨hf, ht⟩))
  have hU_col : ∀ (i : Fin n) (b : Bool), U (posFn n hn (i.val + 1)) b → ∃ a : Bool, T i a b = true := by
    intro i b hUb
    by_contra hall
    have hf : T i false b = false := by
      cases h : T i false b
      · rfl
      · exact absurd ⟨false, h⟩ hall
    have ht : T i true b = false := by
      cases h : T i true b
      · rfl
      · exact absurd ⟨true, h⟩ hall
    have hi : i = prevFn n hn (posFn n hn (i.val + 1)) := (prevFn_posFn hn i).symm
    exact hUb (UnitDeriv.init (Or.inr ⟨hi ▸ hf, hi ▸ ht⟩))
  have hU_fwd : ∀ (i : Fin n) (a b : Bool), ¬ U i (!a) → T i a b = false → ¬ U (posFn n hn (i.val + 1)) b := by
    intro i a b hna hT hUb
    have hda : UnitDeriv hn T i (!a) := by simpa [U] using hna
    have hst : StepImp hn T i (!(!a)) (posFn n hn (i.val + 1)) (!b) := Or.inl ⟨rfl, by simpa using hT⟩
    exact hUb (UnitDeriv.step hda hst)
  have hU_bwd : ∀ (i : Fin n) (a b : Bool), ¬ U (posFn n hn (i.val + 1)) (!b) → T i a b = false → ¬ U i a := by
    intro i a b hnb hT hUa
    have hdb : UnitDeriv hn T (posFn n hn (i.val + 1)) (!b) := by simpa [U] using hnb
    have hst : StepImp hn T (posFn n hn (i.val + 1)) (!(!b)) i (!a) := Or.inr ⟨rfl, by simpa using hT⟩
    exact hUa (UnitDeriv.step hdb hst)
  by_cases hall2 : ∀ v a, U v a
  · by_cases hbij : ∀ i : Fin n, ∃ fi : Bool, ∀ a b, T i a b = !(a ^^ b ^^ fi)
    · choose f hf using hbij
      have hnot_odd : (∑ i : Fin n, if f i = true then (1 : F) else 0) ≠ 1 :=
        fun hodd => hnot ⟨f, hf, hodd⟩
      have heven : (∑ i : Fin n, if f i = true then (1 : F) else 0) = 0 := by
        have hv : ∀ z : F, z ≠ 1 → z = 0 := by decide
        exact hv _ hnot_odd
      let x : Fin n → Bool := fun v =>
        let s : F := ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < v.val), if f j = true then (1 : F) else 0
        decide (s = 1)
      have hx_sat : ∀ i : Fin n, T i (x i) (x (posFn n hn (i.val + 1))) = true := by
        intro i
        rw [hf]
        let s : Fin n → F := fun v =>
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < v.val), if f j = true then (1 : F) else 0
        have hstep : s (posFn n hn (i.val + 1)) = s i + (if f i = true then (1 : F) else 0) := by
          by_cases hlast : i.val + 1 = n
          · have hpos0 : posFn n hn (i.val + 1) = ⟨0, hn⟩ := by
              apply Fin.ext; dsimp only [posFn]; rw [hlast, Nat.mod_self]
            have hs0 : s ⟨0, hn⟩ = 0 := by
              refine Finset.sum_eq_zero fun j hj => ?_
              have := (Finset.mem_filter.mp hj).2; dsimp at this; omega
            have hpart : Finset.univ.filter (fun j : Fin n => j.val < i.val) = Finset.univ.erase i := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
              constructor
              · intro hlt heq; rw [heq] at hlt; omega
              · intro hne; have hj := j.2; have hval : j.val ≠ i.val := fun hv => hne (Fin.ext hv); omega
            have hsum_all := Finset.add_sum_erase Finset.univ (fun j : Fin n => if f j = true then (1 : F) else 0) (Finset.mem_univ i)
            rw [heven, ← hpart] at hsum_all
            rw [hpos0, hs0]
            have hadd : s i + (if f i = true then (1 : F) else 0) = 0 := by
              simpa [s, add_comm] using hsum_all
            exact hadd.symm
          · have hlt : i.val + 1 < n := by have := i.2; omega
            have hposk : posFn n hn (i.val + 1) = ⟨i.val + 1, hlt⟩ := by
              apply Fin.ext; dsimp only [posFn]; exact Nat.mod_eq_of_lt hlt
            have hpart : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
                insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · intro h
                by_cases heq : j.val = i.val
                · exact Or.inl (Fin.ext heq)
                · exact Or.inr (by omega)
              · rintro (rfl | h) <;> omega
            have hnoti : i ∉ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by simp
            rw [hposk]
            dsimp only [s]
            rw [hpart, Finset.sum_insert hnoti, add_comm]
        have hx_eq : ∀ v : Fin n, x v = decide (s v = 1) := fun _ => rfl
        rw [hx_eq, hx_eq, hstep]
        generalize s i = si
        revert si
        cases f i <;> decide
      exact hrej ⟨x, hx_sat⟩
    · push Not at hbij
      rcases hbij with ⟨i0, hi0⟩
      have hex_both : ∃ a0 : Bool, T i0 a0 false = true ∧ T i0 a0 true = true := by
        have hr0 : T i0 false false = true ∨ T i0 false true = true := by
          rcases hU_row i0 false (hall2 i0 false) with ⟨b, hb⟩; cases b <;> [exact Or.inl hb; exact Or.inr hb]
        have hr1 : T i0 true false = true ∨ T i0 true true = true := by
          rcases hU_row i0 true (hall2 i0 true) with ⟨b, hb⟩; cases b <;> [exact Or.inl hb; exact Or.inr hb]
        have hc0 : T i0 false false = true ∨ T i0 true false = true := by
          rcases hU_col i0 false (hall2 _ false) with ⟨a, ha⟩; cases a <;> [exact Or.inl ha; exact Or.inr ha]
        have hc1 : T i0 false true = true ∨ T i0 true true = true := by
          rcases hU_col i0 true (hall2 _ true) with ⟨a, ha⟩; cases a <;> [exact Or.inl ha; exact Or.inr ha]
        have hnb0 : ¬ (T i0 false false = true ∧ T i0 false true = false ∧ T i0 true false = false ∧ T i0 true true = true) := by
          rintro ⟨h00, h01, h10, h11⟩
          rcases hi0 false with ⟨a, b, hab⟩
          cases a <;> cases b <;> simp [h00, h01, h10, h11] at hab
        have hnb1 : ¬ (T i0 false false = false ∧ T i0 false true = true ∧ T i0 true false = true ∧ T i0 true true = false) := by
          rintro ⟨h00, h01, h10, h11⟩
          rcases hi0 true with ⟨a, b, hab⟩
          cases a <;> cases b <;> simp [h00, h01, h10, h11] at hab
        rcases bool_mat_has_double _ _ _ _ hr0 hr1 hc0 hc1 hnb0 hnb1 with h | h
        · exact ⟨false, h⟩
        · exact ⟨true, h⟩
      rcases hex_both with ⟨a0, ha0f, ha0t⟩
      let seq : ℕ → Bool := Nat.rec a0 fun k cur =>
        Classical.choose (hU_col (posFn n hn (i0.val + n - (k + 1) % n)) cur (hall2 _ cur))
      let shiftBack : ℕ → Fin n := fun k => ⟨(i0.val + n - k % n) % n, Nat.mod_lt _ hn⟩
      have hpos_back : ∀ k : ℕ, k < n → posFn n hn ((shiftBack (k + 1)).val + 1) = shiftBack k := by
        intro k hk
        apply Fin.ext
        dsimp only [posFn, shiftBack]
        rw [Nat.mod_eq_of_lt (by omega : k < n)]
        by_cases hk1 : k + 1 = n
        · rw [hk1, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i0.2]
          have h1 : i0.val + n - k = (i0.val + 1) + n - n := by omega
          by_cases hil : i0.val + 1 = n
          · rw [hil, Nat.mod_self]
            have : i0.val + n - k = n := by omega
            rw [this, Nat.mod_self]
          · rw [Nat.mod_eq_of_lt (by have := i0.2; omega)]
            have : i0.val + n - k = i0.val + 1 := by omega
            rw [this, Nat.mod_eq_of_lt (by have := i0.2; omega)]
        · have hk1lt : k + 1 < n := by omega
          rw [Nat.mod_eq_of_lt hk1lt]
          by_cases hge : k + 1 ≤ i0.val
          · have h1 : i0.val + n - (k + 1) = n + (i0.val - (k + 1)) := by omega
            have h2 : i0.val + n - k = n + (i0.val - k) := by omega
            have hlt_a : i0.val - (k + 1) < n := by have := i0.2; omega
            have hlt_b : i0.val - k < n := by have := i0.2; omega
            rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_a,
              h2, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_b,
              show i0.val - (k + 1) + 1 = i0.val - k by omega, Nat.mod_eq_of_lt hlt_b]
          · have hlt1 : i0.val + n - (k + 1) < n := by omega
            rw [Nat.mod_eq_of_lt hlt1]
            by_cases hge2 : k ≤ i0.val
            · have heq : k = i0.val := by omega
              rw [heq, show i0.val + n - (i0.val + 1) + 1 = n by omega, Nat.mod_self,
                show i0.val + n - i0.val = n by omega, Nat.mod_self]
            · have hlt2 : i0.val + n - k < n := by omega
              rw [show i0.val + n - (k + 1) + 1 = i0.val + n - k by omega]
      have hback_step : ∀ k : ℕ, k < n →
          T (shiftBack (k + 1)) (seq (k + 1)) (seq k) = true := by
        intro k hk
        have hspec := Classical.choose_spec (hU_col (shiftBack (k + 1)) (seq k) (hall2 _ (seq k)))
        exact hspec
      let distBack : Fin n → ℕ := fun v => (i0.val + n - v.val) % n
      have hdist_lt : ∀ v : Fin n, distBack v < n := fun v => Nat.mod_lt _ hn
      have hshift_dist : ∀ v : Fin n, shiftBack (distBack v) = v := by
        intro v
        apply Fin.ext
        dsimp only [shiftBack, distBack]
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hn)]
        by_cases hvi : v.val ≤ i0.val
        · have h1 : i0.val + n - v.val = n + (i0.val - v.val) := by omega
          have hlt_a : i0.val - v.val < n := by have := i0.2; omega
          rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_a,
            show i0.val + n - (i0.val - v.val) = n + v.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt v.2]
        · have hlt : i0.val + n - v.val < n := by omega
          rw [Nat.mod_eq_of_lt hlt, show i0.val + n - (i0.val + n - v.val) = v.val by omega, Nat.mod_eq_of_lt v.2]
      let x : Fin n → Bool := fun v => seq (distBack v)
      have hx_sat : ∀ i : Fin n, T i (x i) (x (posFn n hn (i.val + 1))) = true := by
        intro i
        by_cases hi : i = i0
        · rw [hi]
          have hd0 : distBack i0 = 0 := by dsimp only [distBack]; rw [show i0.val + n - i0.val = n by omega, Nat.mod_self]
          have hxi0 : x i0 = a0 := by simp [x, hd0, seq]
          rw [hxi0]
          cases x (posFn n hn (i0.val + 1))
          · exact ha0f
          · exact ha0t
        · let k := distBack (posFn n hn (i.val + 1))
          have hklt : k < n := hdist_lt _
          have hdi : distBack i = k + 1 := by
            have h1 : shiftBack (k + 1) = i := by
              have hp := hpos_back k hklt
              rw [hshift_dist] at hp
              exact ((posFn_add_one_eq_iff hn _ _).mp hp).trans (prevFn_posFn hn i)
            have hlt1 : k + 1 < n := by
              by_contra hge
              have heq : k + 1 = n := by omega
              have hsi0 : shiftBack (k + 1) = i0 := by
                apply Fin.ext; dsimp only [shiftBack]; rw [heq, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i0.2]
              exact hi (h1.symm.trans hsi0)
            have hd_shift : ∀ m < n, distBack (shiftBack m) = m := by
              intro m hm
              dsimp only [distBack, shiftBack]
              rw [Nat.mod_eq_of_lt hm]
              by_cases hmi : m ≤ i0.val
              · have h2 : i0.val + n - m = n + (i0.val - m) := by omega
                have hlt_a : i0.val - m < n := by have := i0.2; omega
                rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_a,
                  show i0.val + n - (i0.val - m) = n + m by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hm]
              · have hlt2 : i0.val + n - m < n := by omega
                rw [Nat.mod_eq_of_lt hlt2, show i0.val + n - (i0.val + n - m) = m by omega, Nat.mod_eq_of_lt hm]
            rw [← h1, hd_shift (k + 1) hlt1]
          have hsi : shiftBack (k + 1) = i := by rw [← hdi, hshift_dist]
          have hdk : distBack (posFn n hn (i.val + 1)) = k := rfl
          dsimp only [x]
          rw [hdk, hdi, ← hsi]
          exact hback_step k hklt
      exact hrej ⟨x, hx_sat⟩
  · push Not at hall2
    rcases hall2 with ⟨v0, a_forb, hna0⟩
    have ha0 : U v0 (!a_forb) := by
      rcases hU_nonempty v0 with ⟨a, ha⟩
      by_cases h : a = !a_forb
      · rwa [← h]
      · have heq : a = a_forb := by cases a <;> cases a_forb <;> simp_all
        exact absurd (heq ▸ ha) hna0
    let seq : ℕ → Bool := Nat.rec (!a_forb) fun k cur =>
      let vnext := posFn n hn (v0.val + k + 1)
      if h : U vnext false ∧ U vnext true then
        if T (posFn n hn (v0.val + k)) cur false = true then false else true
      else if U vnext false then false else true
    have hseq_U : ∀ k : ℕ, U (posFn n hn (v0.val + k)) (seq k) := by
      intro k
      induction k with
      | zero =>
        have hp0 : posFn n hn (v0.val + 0) = v0 := by
          apply Fin.ext; dsimp only [posFn]; rw [Nat.add_zero, Nat.mod_eq_of_lt v0.2]
        rw [hp0]
        exact ha0
      | succ k _ =>
        dsimp only [seq]
        split_ifs with hboth _ hf
        · exact hboth.1
        · exact hboth.2
        · exact hf
        · rcases hU_nonempty (posFn n hn (v0.val + k + 1)) with ⟨b, hb⟩
          cases b
          · exact absurd hb hf
          · exact hb
    have hseq_step : ∀ k : ℕ,
        T (posFn n hn (v0.val + k)) (seq k) (seq (k + 1)) = true := by
      intro k
      let u := posFn n hn (v0.val + k)
      let v := posFn n hn (v0.val + k + 1)
      have hv_pos : v = posFn n hn (u.val + 1) := by
        apply Fin.ext; dsimp only [u, v, posFn]; simp [Nat.add_mod]
      have hUk : U u (seq k) := hseq_U k
      dsimp only [seq]
      change T u (seq k) (if h : U v false ∧ U v true then
        if T u (seq k) false = true then false else true
      else if U v false then false else true) = true
      split_ifs with hboth hTf hUf
      · exact hTf
      · rcases hU_row u (seq k) hUk with ⟨b, hb⟩
        cases b
        · exact absurd hb hTf
        · exact hb
      · have hnt : ¬ U v true := fun ht => hboth ⟨hUf, ht⟩
        by_contra hF
        have hF' : T u (seq k) false = false := Bool.eq_false_iff.mpr hF
        have hnotU := hU_bwd u (seq k) false (by simpa [hv_pos] using hnt) hF'
        exact hnotU hUk
      · have hUt : U v true := by
          rcases hU_nonempty v with ⟨b, hb⟩
          cases b
          · exact absurd hb hUf
          · exact hb
        by_contra hF
        have hF' : T u (seq k) true = false := Bool.eq_false_iff.mpr hF
        have hnotU := hU_bwd u (seq k) true (by simpa [hv_pos] using hUf) hF'
        exact hnotU hUk
    let distFwd : Fin n → ℕ := fun v => (v.val + n - v0.val) % n
    have hpos_dist : ∀ v : Fin n, posFn n hn (v0.val + distFwd v) = v := by
      intro v
      apply Fin.ext; dsimp only [posFn, distFwd]
      by_cases hle : v0.val ≤ v.val
      · have h1 : v.val + n - v0.val = n + (v.val - v0.val) := by omega
        have hlt_a : v.val - v0.val < n := by have := v.2; omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_a,
          show v0.val + (v.val - v0.val) = v.val by omega, Nat.mod_eq_of_lt v.2]
      · have hlt : v.val + n - v0.val < n := by omega
        rw [Nat.mod_eq_of_lt hlt, show v0.val + (v.val + n - v0.val) = n + v.val by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt v.2]
    let x : Fin n → Bool := fun v => seq (distFwd v)
    have hx_sat : ∀ i : Fin n, T i (x i) (x (posFn n hn (i.val + 1))) = true := by
      intro i
      let k := distFwd i
      have hklt : k < n := Nat.mod_lt _ hn
      have hpi : posFn n hn (v0.val + k) = i := hpos_dist i
      by_cases hlast : k + 1 = n
      · have hpos_v0 : posFn n hn (i.val + 1) = v0 := by
          rw [← hpi]; apply Fin.ext; dsimp only [posFn]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show v0.val + k + 1 = v0.val + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt v0.2]
        have hd0 : distFwd v0 = 0 := by dsimp only [distFwd]; rw [show v0.val + n - v0.val = n by omega, Nat.mod_self]
        rw [hpos_v0]
        dsimp only [x]
        rw [hd0]
        change T i (seq k) (!a_forb) = true
        by_contra hF
        have hF' : T i (seq k) (!a_forb) = false := Bool.eq_false_iff.mpr hF
        have hnotU := hU_bwd i (seq k) (!a_forb) (by simpa [hpos_v0] using hna0) hF'
        exact hnotU (hpi ▸ hseq_U k)
      · have hk1lt : k + 1 < n := by omega
        have hd_next : distFwd (posFn n hn (i.val + 1)) = k + 1 := by
          have hnext : posFn n hn (i.val + 1) = posFn n hn (v0.val + (k + 1)) := by
            rw [← hpi]; apply Fin.ext; dsimp only [posFn]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show v0.val + k + 1 = v0.val + (k + 1) by omega]
          rw [hnext]
          dsimp only [distFwd, posFn]
          by_cases hlt : v0.val + (k + 1) < n
          · rw [Nat.mod_eq_of_lt hlt, show v0.val + (k + 1) + n - v0.val = n + (k + 1) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt hk1lt]
          · have h1 : v0.val + (k + 1) = n + (v0.val + (k + 1) - n) := by omega
            have h2 : v0.val + (k + 1) - n < n := by have := v0.2; omega
            rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt h2,
              show v0.val + (k + 1) - n + n - v0.val = k + 1 by omega, Nat.mod_eq_of_lt hk1lt]
        have hdi : distFwd i = k := rfl
        dsimp only [x]
        rw [hd_next, hdi, ← hpi]
        exact hseq_step k
    exact hrej ⟨x, hx_sat⟩

lemma part1_pc_refutable {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    (T : Fin n → Bool → Bool → Bool) (hrej : rejectsFn n hn T) :
    let G := cnfSystem (↑(blockersFn n hn T) : Set (Clause (Fin n)))
    PCRefutable G 2 ∧ ¬ PCRefutable G 1 := by
  intro G
  constructor
  · by_cases hot : IsOddTwist T
    · exact oddTwist_pc2 hn hn2 hot
    · rcases rejects_not_oddTwist_unit_contra hn hn2 hrej hot with ⟨w, hf, ht⟩
      have hpf := unitDeriv_to_pc hn hn2 hf
      have hpt := unitDeriv_to_pc hn hn2 ht
      have hsum := PCDerivable.add hpf hpt
      have heq : litPoly w false + litPoly w true = 1 := litPoly_add_not w false
      rwa [heq] at hsum
  · intro href
    have hall0 : ∀ p : MvPolynomial (Fin n) F, PCDerivable G 1 p → p = 0 := by
      intro p hp
      induction hp with
      | ax hmem hdeg =>
        rcases hmem with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
        · have := totalDegree_boolAxiom v; omega
        · have := blockersFn_deg2 hn hn2 T hC; omega
      | zero => rfl
      | add _ _ ih1 ih2 => rw [ih1, ih2, add_zero]
      | mulX j _ _ ih => rw [ih, mul_zero]
    have h10 := hall0 1 href
    have hc := congrArg (fun p : MvPolynomial (Fin n) F => p.coeff (0 : Fin n →₀ ℕ)) h10
    simp at hc

def ImpPath {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (L : ℕ) (vs : ℕ → Fin n) (as : ℕ → Bool) : Prop :=
  InitUnit hn T (vs 0) (!(as 0)) ∧
  (∀ k < L, StepImp hn T (vs k) (as k) (vs (k + 1)) (as (k + 1))) ∧
  InitUnit hn T (vs L) (as L)

lemma unitDeriv_to_chain {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    {v : Fin n} {a : Bool} (h : UnitDeriv hn T v a) :
    ∃ (L : ℕ) (vs : ℕ → Fin n) (as : ℕ → Bool),
      InitUnit hn T (vs 0) (!(as 0)) ∧
      (∀ k < L, StepImp hn T (vs k) (as k) (vs (k + 1)) (as (k + 1))) ∧
      vs L = v ∧ as L = !a := by
  induction h with
  | @init v' a' hi =>
    refine ⟨0, fun _ => v', fun _ => !a', ?_, fun _ hk => by omega, rfl, rfl⟩
    simpa using hi
  | @step u' a' v' b' _ hst ih =>
    rcases ih with ⟨L, vs, as, h0, hsteps, hvL, haL⟩
    let vs' : ℕ → Fin n := fun k => if k ≤ L then vs k else v'
    let as' : ℕ → Bool := fun k => if k ≤ L then as k else !b'
    refine ⟨L + 1, vs', as', by simpa [vs', as'] using h0, ?_, by simp [vs'], by simp [as']⟩
    intro k hk
    by_cases hlt : k < L
    · have h1 : k ≤ L := by omega
      have h2 : k + 1 ≤ L := by omega
      simp only [vs', as', h1, h2, ↓reduceIte]
      exact hsteps k hlt
    · have heq : k = L := by omega
      subst heq
      have h1 : k ≤ k := le_refl k
      have h2 : ¬ k + 1 ≤ k := by omega
      simp only [vs', as', h1, h2, ↓reduceIte, hvL, haL]
      exact hst

lemma exists_short_impPath {n : ℕ} (hn : 0 < n) (hn3 : 3 ≤ n)
    {T : Fin n → Bool → Bool → Bool}
    (hex_contra : ∃ w : Fin n, UnitDeriv hn T w false ∧ UnitDeriv hn T w true) :
    ∃ (L : ℕ) (vs : ℕ → Fin n) (as : ℕ → Bool),
      L ≤ n - 1 ∧ ImpPath hn T L vs as := by
  classical
  have hex_path : ∃ L : ℕ, ∃ (vs : ℕ → Fin n) (as : ℕ → Bool), ImpPath hn T L vs as := by
    rcases hex_contra with ⟨w, hf, ht⟩
    rcases unitDeriv_to_chain hn hf with ⟨L1, vs1, as1, h10, h1s, hv1L, ha1L⟩
    rcases unitDeriv_to_chain hn ht with ⟨L2, vs2, as2, h20, h2s, hv2L, ha2L⟩
    let vs : ℕ → Fin n := fun k => if k ≤ L1 then vs1 k else vs2 (L1 + L2 - k)
    let as : ℕ → Bool := fun k => if k ≤ L1 then as1 k else !(as2 (L1 + L2 - k))
    refine ⟨L1 + L2, vs, as, by simpa [vs, as] using h10, ?_, ?_⟩
    · intro k hk
      by_cases hlt : k < L1
      · have h1 : k ≤ L1 := by omega
        have h2 : k + 1 ≤ L1 := by omega
        simp only [vs, as, h1, h2, ↓reduceIte]
        exact h1s k hlt
      · by_cases heq : k = L1
        · subst heq
          have h1 : k ≤ k := le_refl k
          have h2 : ¬ k + 1 ≤ k := by omega
          simp only [vs, as, h1, h2, ↓reduceIte, hv1L, ha1L]
          have hsub : k + L2 - (k + 1) = L2 - 1 := by omega
          rw [hsub]
          have hstep := stepImp_contrapose hn (h2s (L2 - 1) (by omega))
          rw [show L2 - 1 + 1 = L2 by omega, hv2L, ha2L] at hstep
          simpa using hstep
        · have h1 : ¬ k ≤ L1 := by omega
          have h2 : ¬ k + 1 ≤ L1 := by omega
          simp only [vs, as, h1, h2, ↓reduceIte]
          have hsub : L1 + L2 - k = (L1 + L2 - (k + 1)) + 1 := by omega
          rw [hsub]
          exact stepImp_contrapose hn (h2s (L1 + L2 - (k + 1)) (by omega))
    · by_cases hL2 : L2 = 0
      · subst hL2
        simp only [vs, as, Nat.add_zero, le_refl, ↓reduceIte, hv1L, ha1L]
        rw [← hv2L]
        simpa [ha2L] using h20
      · have hnot : ¬ L1 + L2 ≤ L1 := by omega
        simp only [vs, as, hnot, ↓reduceIte, Nat.sub_self]
        exact h20
  let L := Nat.find hex_path
  have hL_spec := Nat.find_spec hex_path
  rcases hL_spec with ⟨vs, as, h0, hsteps, hEnd⟩
  have hmin : ∀ L' < L, ∀ (vs' : ℕ → Fin n) (as' : ℕ → Bool), ¬ ImpPath hn T L' vs' as' :=
    fun L' hlt vs' as' hp => Nat.find_min hex_path hlt ⟨vs', as', hp⟩
  have hno_dup_lit : ∀ p q : ℕ, p < q → q ≤ L → ¬ (vs p = vs q ∧ as p = as q) := by
    rintro p q hpq hqL ⟨hv_eq, ha_eq⟩
    let L' := L - (q - p)
    let vs' : ℕ → Fin n := fun k => if k ≤ p then vs k else vs (k + (q - p))
    let as' : ℕ → Bool := fun k => if k ≤ p then as k else as (k + (q - p))
    refine hmin L' (by omega) vs' as' ⟨by simpa [vs', as'] using h0, ?_, ?_⟩
    · intro k hk
      by_cases hlt : k < p
      · have h1 : k ≤ p := by omega
        have h2 : k + 1 ≤ p := by omega
        simp only [vs', as', h1, h2, ↓reduceIte]
        exact hsteps k (by omega)
      · by_cases heq : k = p
        · subst heq
          have h1 : k ≤ k := le_refl k
          have h2 : ¬ k + 1 ≤ k := by omega
          simp only [vs', as', h1, h2, ↓reduceIte, hv_eq, ha_eq, show k + 1 + (q - k) = q + 1 by omega]
          exact hsteps q (by omega)
        · have h1 : ¬ k ≤ p := by omega
          have h2 : ¬ k + 1 ≤ p := by omega
          simp only [vs', as', h1, h2, ↓reduceIte, show k + 1 + (q - p) = k + (q - p) + 1 by omega]
          exact hsteps (k + (q - p)) (by omega)
    · by_cases hqeq : q = L
      · subst hqeq
        have hL' : L' = p := by omega
        simp only [vs', as', hL', le_refl, ↓reduceIte, hv_eq, ha_eq]
        exact hEnd
      · have hnot : ¬ L' ≤ p := by omega
        simp only [vs', as', hnot, ↓reduceIte, show L' + (q - p) = L by omega]
        exact hEnd
  have hno_rev : ∀ k : ℕ, 1 ≤ k → k < L → vs (k - 1) ≠ vs (k + 1) := by
    intro k hk1 hkL heq
    by_cases ha_eq : as (k - 1) = as (k + 1)
    · exact hno_dup_lit (k - 1) (k + 1) (by omega) (by omega) ⟨heq, ha_eq⟩
    · have ha_neg : as (k + 1) = !(as (k - 1)) := by
        revert ha_eq; cases as (k - 1) <;> cases as (k + 1) <;> decide
      have hs1 := hsteps (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at hs1
      have hs2 := hsteps k hkL
      rw [← heq, ha_neg] at hs2
      have hiu : InitUnit hn T (vs (k - 1)) (as (k - 1)) := by
        rcases hs1 with ⟨hvk, hT1⟩ | ⟨hvk, hT1⟩
        · rcases hs2 with ⟨hvk2, hT2⟩ | ⟨_, hT2⟩
          · exfalso
            have := posFn_ne_prevFn hn hn3 (vs (k - 1))
            have hprev : vs k = prevFn n hn (vs (k - 1)) := (posFn_add_one_eq_iff hn _ _).mp hvk2.symm
            exact this (hvk.symm.trans hprev)
          · left
            cases hak : as k
            · rw [hak] at hT1 hT2; exact ⟨by simpa using hT2, by simpa using hT1⟩
            · rw [hak] at hT1 hT2; exact ⟨by simpa using hT1, by simpa using hT2⟩
        · rcases hs2 with ⟨_, hT2⟩ | ⟨hvk2, hT2⟩
          · right
            have hprev : prevFn n hn (vs (k - 1)) = vs k := by rw [hvk, prevFn_posFn]
            rw [hprev]
            cases hak : as k
            · rw [hak] at hT1 hT2; exact ⟨by simpa using hT2, by simpa using hT1⟩
            · rw [hak] at hT1 hT2; exact ⟨by simpa using hT1, by simpa using hT2⟩
          · exfalso
            have := posFn_ne_prevFn hn hn3 (vs (k - 1))
            have hprev : vs k = prevFn n hn (vs (k - 1)) := (posFn_add_one_eq_iff hn _ _).mp hvk.symm
            exact this (hvk2.symm.trans hprev)
      exact hmin (k - 1) (by omega) vs as ⟨h0, fun j hj => hsteps j (by omega), hiu⟩
  have hmono : (∀ k < L, vs (k + 1) = posFn n hn ((vs k).val + 1)) ∨
      (∀ k < L, vs k = posFn n hn ((vs (k + 1)).val + 1)) := by
    by_cases hL0 : L = 0
    · left; intro k hk; omega
    · rcases hsteps 0 (by omega) with ⟨hdir0, _⟩ | ⟨hdir0, _⟩
      · left
        intro k
        induction k with
        | zero => intro _; exact hdir0
        | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          rcases hsteps (k + 1) hk with ⟨hf, _⟩ | ⟨hb, _⟩
          · exact hf
          · exfalso
            have heq : vs k = vs (k + 2) := by
              have h1 := congrArg (prevFn n hn) (hprev.symm.trans hb)
              simpa [prevFn_posFn] using h1
            exact hno_rev (k + 1) (by omega) hk (by simpa using heq)
      · right
        intro k
        induction k with
        | zero => intro _; exact hdir0
        | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          rcases hsteps (k + 1) hk with ⟨hf, _⟩ | ⟨hb, _⟩
          · exfalso
            have heq : vs k = vs (k + 2) := hprev.trans hf.symm
            exact hno_rev (k + 1) (by omega) hk (by simpa using heq)
          · exact hb
  have hL_le : L ≤ n - 1 := by
    by_contra hgt
    have hLn : n ≤ L := by omega
    rcases hmono with hfwd | hbwd
    · have hvs_k : ∀ k ≤ L, vs k = posFn n hn ((vs 0).val + k) := by
        intro k
        induction k with
        | zero => intro _; apply Fin.ext; dsimp only [posFn]; rw [Nat.add_zero, Nat.mod_eq_of_lt (vs 0).2]
        | succ k ih =>
          intro hk
          rw [hfwd k (by omega), ih (by omega)]
          apply Fin.ext; dsimp only [posFn]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show (vs 0).val + k + 1 = (vs 0).val + (k + 1) by omega]
      have hvsn : vs n = vs 0 := by
        rw [hvs_k n hLn]; apply Fin.ext; dsimp only [posFn]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt (vs 0).2]
      by_cases han : as n = as 0
      · exact hno_dup_lit 0 n hn hLn ⟨hvsn.symm, han.symm⟩
      · have han' : as n = !(as 0) := by revert han; cases as 0 <;> cases as n <;> decide
        by_cases hLgt : n < L
        · exact hmin n hLgt vs as ⟨h0, fun k hk => hsteps k (by omega), by rw [hvsn, han']; exact h0⟩
        · have hLeq : L = n := by omega
          have h0' := h0
          rcases h0' with ⟨h0f, h0t⟩ | ⟨h0f, h0t⟩
          · have hs0 := hsteps 0 (by omega)
            have hT0 : T (vs 0) (as 0) (!(as 1)) = false := by
              rcases hs0 with ⟨_, hT⟩ | ⟨hb, _⟩
              · exact hT
              · exfalso
                have := posFn_ne_prevFn hn hn3 (vs 0)
                exact this ((hfwd 0 (by omega)).symm.trans ((posFn_add_one_eq_iff hn _ _).mp hb.symm))
            have hiu1 : InitUnit hn T (vs 1) (!(as 1)) := by
              right
              have hp1 : prevFn n hn (vs 1) = vs 0 := by rw [hfwd 0 (by omega), prevFn_posFn]
              rw [hp1]
              cases ha0 : as 0
              · rw [ha0] at h0f h0t hT0
                cases h1 : !(as 1)
                · rw [h1] at hT0; exact ⟨hT0, by simpa using h0f⟩
                · rw [h1] at hT0; exact ⟨hT0, by simpa using h0t⟩
              · rw [ha0] at h0f h0t hT0
                cases h1 : !(as 1)
                · rw [h1] at hT0; exact ⟨by simpa using h0f, hT0⟩
                · rw [h1] at hT0; exact ⟨by simpa using h0t, hT0⟩
            refine hmin (n - 1) (by omega) (fun k => vs (k + 1)) (fun k => as (k + 1))
              ⟨hiu1, fun k hk => hsteps (k + 1) (by omega), ?_⟩
            dsimp only
            rw [show n - 1 + 1 = n by omega]
            dsimp only [L] at hLeq
            rw [hLeq] at hEnd
            exact hEnd
          · have hsn := hsteps (n - 1) (by omega)
            have hprev_eq : prevFn n hn (vs 0) = vs (n - 1) := by
              have hvsn' : vs (n - 1 + 1) = vs 0 := by rwa [show n - 1 + 1 = n by omega]
              rw [← hvsn', hfwd (n - 1) (by omega), prevFn_posFn]
            have hTn : T (vs (n - 1)) (as (n - 1)) (as 0) = false := by
              rcases hsn with ⟨_, hT⟩ | ⟨hb, _⟩
              · rw [show n - 1 + 1 = n by omega, han', Bool.not_not] at hT; exact hT
              · exfalso
                have := posFn_ne_prevFn hn hn3 (vs (n - 1))
                exact this ((hfwd (n - 1) (by omega)).symm.trans ((posFn_add_one_eq_iff hn _ _).mp hb.symm))
            have hiu_end : InitUnit hn T (vs (n - 1)) (as (n - 1)) := by
              left
              rw [hprev_eq] at h0f h0t
              cases ha0 : as 0
              · rw [ha0] at h0f h0t hTn
                cases ha1 : as (n - 1)
                · rw [ha1] at hTn; exact ⟨hTn, by simpa using h0f⟩
                · rw [ha1] at hTn; exact ⟨hTn, by simpa using h0t⟩
              · rw [ha0] at h0f h0t hTn
                cases ha1 : as (n - 1)
                · rw [ha1] at hTn; exact ⟨by simpa using h0f, hTn⟩
                · rw [ha1] at hTn; exact ⟨by simpa using h0t, hTn⟩
            exact hmin (n - 1) (by omega) vs as ⟨h0, fun k hk => hsteps k (by omega), hiu_end⟩
    · have hvs_k : ∀ k ≤ L, vs k = posFn n hn ((vs 0).val + n - k % n) := by
        intro k
        induction k with
        | zero => intro _; apply Fin.ext; dsimp only [posFn]; rw [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (vs 0).2]
        | succ k ih =>
          intro hk
          have hprev_step : vs (k + 1) = prevFn n hn (vs k) := ((posFn_add_one_eq_iff hn _ _).mp (hbwd k (by omega)).symm)
          rw [hprev_step, ih (by omega)]
          apply Fin.ext; dsimp only [prevFn, posFn]
          have hkm : k % n < n := Nat.mod_lt _ hn
          by_cases hwrap : k % n + 1 = n
          · have hk1 : (k + 1) % n = 0 := by
              rw [Nat.add_mod, show k % n + 1 % n = n by rw [Nat.mod_eq_of_lt (by omega : 1 < n)]; exact hwrap, Nat.mod_self]
            rw [hk1, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (vs 0).2]
            have hsub : (vs 0).val + n - k % n = (vs 0).val + 1 := by omega
            rw [hsub]
            by_cases hil : (vs 0).val + 1 = n
            · rw [hil, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
            · have hlt_v : (vs 0).val + 1 < n := by have := (vs 0).2; omega
              rw [Nat.mod_eq_of_lt hlt_v,
                show (vs 0).val + 1 + n - 1 = n + (vs 0).val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (vs 0).2]
          · have hk1 : (k + 1) % n = k % n + 1 := by
              rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega)]
            rw [hk1]
            by_cases hge : k % n ≤ (vs 0).val
            · have h1 : (vs 0).val + n - k % n = n + ((vs 0).val - k % n) := by omega
              have hlt_a : (vs 0).val - k % n < n := by have := (vs 0).2; omega
              rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_a]
              by_cases heq : k % n = (vs 0).val
              · have hlt_nm : n - 1 < n := by omega
                rw [heq, Nat.sub_self, Nat.zero_add, Nat.mod_eq_of_lt hlt_nm,
                  show (vs 0).val + n - ((vs 0).val + 1) = n - 1 by omega, Nat.mod_eq_of_lt hlt_nm]
              · have h2 : (vs 0).val + n - (k % n + 1) = n + ((vs 0).val - k % n - 1) := by omega
                have hlt_b : (vs 0).val - k % n - 1 < n := by have := (vs 0).2; omega
                rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt hlt_b,
                  show (vs 0).val - k % n + n - 1 = n + ((vs 0).val - k % n - 1) by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt hlt_b]
            · have hlt1 : (vs 0).val + n - k % n < n := by omega
              have hlt2 : (vs 0).val + n - (k % n + 1) < n := by omega
              rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2,
                show (vs 0).val + n - k % n + n - 1 = n + ((vs 0).val + n - (k % n + 1)) by omega,
                Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
      have hvsn : vs n = vs 0 := by
        rw [hvs_k n hLn]; apply Fin.ext; dsimp only [posFn]
        rw [Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (vs 0).2]
      by_cases han : as n = as 0
      · exact hno_dup_lit 0 n hn hLn ⟨hvsn.symm, han.symm⟩
      · have han' : as n = !(as 0) := by revert han; cases as 0 <;> cases as n <;> decide
        by_cases hLgt : n < L
        · exact hmin n hLgt vs as ⟨h0, fun k hk => hsteps k (by omega), by rw [hvsn, han']; exact h0⟩
        · have hLeq : L = n := by omega
          have h0' := h0
          rcases h0' with ⟨h0f, h0t⟩ | ⟨h0f, h0t⟩
          · have hsn := hsteps (n - 1) (by omega)
            have hvsn' : vs (n - 1 + 1) = vs 0 := by rwa [show n - 1 + 1 = n by omega]
            have hpos0 : posFn n hn ((vs 0).val + 1) = vs (n - 1) := by
              rw [← hvsn']
              exact (hbwd (n - 1) (by omega)).symm
            have hTn : T (vs 0) (as 0) (as (n - 1)) = false := by
              rcases hsn with ⟨hf, _⟩ | ⟨_, hT⟩
              · exfalso
                have := posFn_ne_prevFn hn hn3 (vs (n - 1))
                have h1 : vs (n - 1 + 1) = prevFn n hn (vs (n - 1)) :=
                  (posFn_add_one_eq_iff hn _ _).mp (hbwd (n - 1) (by omega)).symm
                exact this (hf.symm.trans h1)
              · rw [show n - 1 + 1 = n by omega, hvsn, han', Bool.not_not] at hT; exact hT
            have hiu_end : InitUnit hn T (vs (n - 1)) (as (n - 1)) := by
              right
              have hp_end : prevFn n hn (vs (n - 1)) = vs 0 := by rw [← hpos0, prevFn_posFn]
              rw [hp_end]
              cases ha0 : as 0
              · rw [ha0] at h0f h0t hTn
                cases ha1 : as (n - 1)
                · rw [ha1] at hTn; exact ⟨hTn, by simpa using h0f⟩
                · rw [ha1] at hTn; exact ⟨hTn, by simpa using h0t⟩
              · rw [ha0] at h0f h0t hTn
                cases ha1 : as (n - 1)
                · rw [ha1] at hTn; exact ⟨by simpa using h0f, hTn⟩
                · rw [ha1] at hTn; exact ⟨by simpa using h0t, hTn⟩
            exact hmin (n - 1) (by omega) vs as ⟨h0, fun k hk => hsteps k (by omega), hiu_end⟩
          · have hs0 := hsteps 0 (by omega)
            have hprev0 : prevFn n hn (vs 0) = vs 1 := ((posFn_add_one_eq_iff hn _ _).mp (hbwd 0 (by omega)).symm).symm
            have hT0 : T (vs 1) (!(as 1)) (as 0) = false := by
              rcases hs0 with ⟨hf, _⟩ | ⟨_, hT⟩
              · exfalso
                have := posFn_ne_prevFn hn hn3 (vs 0)
                exact this (hf.symm.trans hprev0.symm)
              · exact hT
            have hiu1 : InitUnit hn T (vs 1) (!(as 1)) := by
              left
              rw [hprev0] at h0f h0t
              cases ha0 : as 0
              · rw [ha0] at h0f h0t hT0
                cases h1 : !(as 1)
                · rw [h1] at hT0; exact ⟨hT0, by simpa using h0f⟩
                · rw [h1] at hT0; exact ⟨hT0, by simpa using h0t⟩
              · rw [ha0] at h0f h0t hT0
                cases h1 : !(as 1)
                · rw [h1] at hT0; exact ⟨by simpa using h0f, hT0⟩
                · rw [h1] at hT0; exact ⟨by simpa using h0t, hT0⟩
            refine hmin (n - 1) (by omega) (fun k => vs (k + 1)) (fun k => as (k + 1))
              ⟨hiu1, fun k hk => hsteps (k + 1) (by omega), ?_⟩
            dsimp only
            rw [show n - 1 + 1 = n by omega]
            dsimp only [L] at hLeq
            rw [hLeq] at hEnd
            exact hEnd
  exact ⟨L, vs, as, hL_le, ⟨h0, hsteps, hEnd⟩⟩

lemma static_of_n2 {n d : ℕ} (hn : 0 < n) (hn_eq : n = 2) (hd2 : 2 ≤ d)
    (T : Fin n → Bool → Bool → Bool) (hrej : rejectsFn n hn T) :
    staticFn n (blockersFn n hn T) d := by
  classical
  subst hn_eq
  let i0 : Fin 2 := ⟨0, by decide⟩
  let i1 : Fin 2 := ⟨1, by decide⟩
  have h01 : i0 ≠ i1 := by decide
  have hpos0 : posFn 2 hn (i0.val + 1) = i1 := by apply Fin.ext; dsimp only [posFn, i0, i1]
  have hpos1 : posFn 2 hn (i1.val + 1) = i0 := by apply Fin.ext; dsimp only [posFn, i0, i1]
  have hmem_all : ∀ a b : Bool, ({(i0, !a), (i1, !b)} : Clause (Fin 2)) ∈ blockersFn 2 hn T := by
    intro a b
    let x : Fin 2 → Bool := fun v => if v = i0 then a else b
    have hnot_all : ¬ ∀ i : Fin 2, T i (x i) (x (posFn 2 hn (i.val + 1))) = true :=
      fun h => hrej ⟨x, h⟩
    push Not at hnot_all
    rcases hnot_all with ⟨i, hi⟩
    have hF : T i (x i) (x (posFn 2 hn (i.val + 1))) = false := by
      cases h : T i (x i) (x (posFn 2 hn (i.val + 1))) <;> simp_all
    fin_cases i
    · have hbl := blocker_mem_blockersFn hn (T := T) (i := i0) (a := a) (b := b) (by simpa [x, i0, i1, hpos0] using hF)
      simpa [hpos0] using hbl
    · have hbl := blocker_mem_blockersFn hn (T := T) (i := i1) (a := b) (b := a) (by simpa [x, i0, i1, hpos1] using hF)
      have hcomm : ({(i1, !b), (i0, !a)} : Clause (Fin 2)) = {(i0, !a), (i1, !b)} := Finset.pair_comm _ _
      simpa [hpos1, hcomm] using hbl
  let Cff : Clause (Fin 2) := {(i0, true), (i1, true)}
  let Cft : Clause (Fin 2) := {(i0, true), (i1, false)}
  let Ctf : Clause (Fin 2) := {(i0, false), (i1, true)}
  let Ctt : Clause (Fin 2) := {(i0, false), (i1, false)}
  have hsub : ({Cff, Cft, Ctf, Ctt} : Finset (Clause (Fin 2))) ⊆ blockersFn 2 hn T := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · exact hmem_all false false
    · exact hmem_all false true
    · exact hmem_all true false
    · exact hmem_all true true
  have hne1 : Cff ≠ Cft := by decide
  have hne2 : Cff ≠ Ctf := by decide
  have hne3 : Cff ≠ Ctt := by decide
  have hne4 : Cft ≠ Ctf := by decide
  have hne5 : Cft ≠ Ctt := by decide
  have hne6 : Ctf ≠ Ctt := by decide
  let q : Clause (Fin 2) → MvPolynomial (Fin 2) F := fun C =>
    if C ∈ ({Cff, Cft, Ctf, Ctt} : Finset (Clause (Fin 2))) then 1 else 0
  refine ⟨q, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
  · intro C hC
    by_cases h : C ∈ ({Cff, Cft, Ctf, Ctt} : Finset (Clause (Fin 2)))
    · right; simp only [q, h, ↓reduceIte, MvPolynomial.totalDegree_one]; rw [blockersFn_deg2 hn (by omega) T hC]; omega
    · left; simp only [q, h, ↓reduceIte]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_insert (by simp [hne1, hne2, hne3]),
        Finset.sum_insert (by simp [hne4, hne5]),
        Finset.sum_insert (by simp [hne6]), Finset.sum_singleton]
      simp only [q, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, ↓reduceIte, one_mul]
      rw [clausePoly_pair h01, clausePoly_pair h01, clausePoly_pair h01, clausePoly_pair h01]
      simp only [↓reduceIte, Bool.false_eq_true]
      have hcalc : (1 + MvPolynomial.X i0) * (1 + MvPolynomial.X i1) +
          ((1 + MvPolynomial.X i0) * MvPolynomial.X i1 +
          (MvPolynomial.X i0 * (1 + MvPolynomial.X i1) + MvPolynomial.X i0 * MvPolynomial.X i1)) =
          1 + (2 : MvPolynomial (Fin 2) F) * MvPolynomial.X i0 + (2 : MvPolynomial (Fin 2) F) * MvPolynomial.X i1 +
          (2 : MvPolynomial (Fin 2) F) * ((2 : MvPolynomial (Fin 2) F) * MvPolynomial.X i0 * MvPolynomial.X i1) := by
        ring
      rw [hcalc, mv_two_eq_zero]; ring
    · intro C _ hnot; simp only [q, hnot, ↓reduceIte, zero_mul]

lemma static_of_short_impPath {n d L : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} {vs : ℕ → Fin n} {as : ℕ → Bool}
    (hLn : L ≤ n - 1) (hd_lt : n + 2 < 2 ^ d)
    (hpath : ImpPath hn T L vs as) :
    staticFn n (blockersFn n hn T) d := by
  classical
  have hd2 : 2 ≤ d := by
    by_contra h
    have hd1 : d ≤ 1 := by omega
    interval_cases d <;> omega
  rcases hpath with ⟨h0_init, hsteps, hEnd_init⟩
  rcases initUnit_clauses hn hn2 h0_init with ⟨Cs0, Cs1, hCs0_mem, hCs1_mem, hCs_ne, hCs_sum⟩
  rcases initUnit_clauses hn hn2 hEnd_init with ⟨Ce0, Ce1, hCe0_mem, hCe1_mem, hCe_ne, hCe_sum⟩
  have h1_Z0 : clausePoly Cs0 + clausePoly Cs1 = 1 + litPoly (vs 0) (as 0) := by
    rw [hCs_sum]
    have hadd := litPoly_add_not (vs 0) (as 0)
    calc
      litPoly (vs 0) (!(as 0)) = (litPoly (vs 0) (as 0) + litPoly (vs 0) (!(as 0))) + litPoly (vs 0) (as 0) := by
        rw [add_comm (litPoly (vs 0) (as 0)), add_assoc, mv_add_self, add_zero]
      _ = 1 + litPoly (vs 0) (as 0) := by rw [hadd]
  by_cases hL0 : L = 0
  · subst hL0
    let qs : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => if C = Cs0 ∨ C = Cs1 then 1 else 0
    let qe : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => if C = Ce0 ∨ C = Ce1 then 1 else 0
    let q : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => qs C + qe C
    refine ⟨q, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
    · intro C hC
      right
      rw [blockersFn_deg2 hn hn2 T hC]
      have hds : (qs C).totalDegree ≤ 0 := by dsimp only [qs]; split_ifs <;> simp
      have hde : (qe C).totalDegree ≤ 0 := by dsimp only [qe]; split_ifs <;> simp
      have := le_trans (MvPolynomial.totalDegree_add (qs C) (qe C)) (max_le hds hde)
      dsimp only [q]; omega
    · simp only [zero_mul, Finset.sum_const_zero, add_zero]
      simp_rw [q, add_mul, Finset.sum_add_distrib]
      have hs : (blockersFn n hn T).sum (fun C => qs C * clausePoly C) = 1 + litPoly (vs 0) (as 0) := by
        rw [← Finset.sum_subset (s₁ := {Cs0, Cs1}) (by
          intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
          rcases hC with rfl | rfl; exact hCs0_mem; exact hCs1_mem)]
        · rw [Finset.sum_pair hCs_ne]; simp only [qs, true_or, or_true, ↓reduceIte, one_mul]; exact h1_Z0
        · intro C _ hnot; have h' : ¬ (C = Cs0 ∨ C = Cs1) := by simpa using hnot
          simp only [qs, h', ↓reduceIte, zero_mul]
      have he : (blockersFn n hn T).sum (fun C => qe C * clausePoly C) = litPoly (vs 0) (as 0) := by
        rw [← Finset.sum_subset (s₁ := {Ce0, Ce1}) (by
          intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
          rcases hC with rfl | rfl; exact hCe0_mem; exact hCe1_mem)]
        · rw [Finset.sum_pair hCe_ne]; simp only [qe, true_or, or_true, ↓reduceIte, one_mul]; exact hCe_sum
        · intro C _ hnot; have h' : ¬ (C = Ce0 ∨ C = Ce1) := by simpa using hnot
          simp only [qe, h', ↓reduceIte, zero_mul]
      rw [hs, he, add_assoc, mv_add_self, add_zero]
  · let m : ℕ := L + 1
    let len : ℕ := m + 1
    have hlen_lt : len + 1 < 2 ^ d := by dsimp only [len, m]; omega
    rcases pebble_site_upper d (by omega) 0 len hlen_lt with ⟨Len, W, hW, hW0, hWL⟩
    have hex_len : ∃ t, t ≤ Len ∧ len ∈ W t := ⟨Len, le_refl Len, by simpa using hWL⟩
    let tfirst := Nat.find hex_len
    have htf_spec := Nat.find_spec hex_len
    have htf_le : tfirst ≤ Len := htf_spec.1
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
        have hnot_len : len ∉ W (t + 1) := fun hmem => Nat.find_min hex_len ht ⟨by omega, hmem⟩
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
          exact hnot_prev (hS ▸ Finset.mem_insert_of_mem htf_mem)
    let Z : Fin m → MvPolynomial (Fin n) F := fun idx => litPoly (vs idx.val) (as idx.val)
    have hZ_deg : ∀ idx : Fin m, (Z idx).totalDegree ≤ 1 := fun idx => totalDegree_litPoly _ _
    have hprod_Z_deg : ∀ U : Finset (Fin m), (∏ idx ∈ U, Z idx).totalDegree ≤ U.card := fun U =>
      prod_litPoly_totalDegree U (fun idx => vs idx.val) (fun idx => as idx.val)
    let proj : Finset ℕ → Finset (Fin m) := fun S =>
      Finset.univ.filter (fun idx : Fin m => idx.val + 1 ∈ S)
    let mon : Finset ℕ → MvPolynomial (Fin n) F := fun S => ∏ idx ∈ proj S, Z idx
    have hproj_card : ∀ S : Finset ℕ, (proj S).card ≤ S.card := by
      intro S
      refine Finset.card_le_card_of_injOn (fun idx : Fin m => idx.val + 1) ?_ (fun a _ b _ h => Fin.ext (by dsimp at h; omega))
      intro idx hidx
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hidx)).2
    have hproj_card_of_zero : ∀ S : Finset ℕ, 0 ∈ S → (proj S).card + 1 ≤ S.card := by
      intro S h0S
      have hsub : (proj S).image (fun idx : Fin m => idx.val + 1) ⊆ S.erase 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨idx, hidx, rfl⟩
        exact Finset.mem_erase.mpr ⟨by omega, (Finset.mem_filter.mp hidx).2⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega)), Finset.card_erase_of_mem h0S] at hle
      have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, h0S⟩
      omega
    have hstep_rep : ∀ t < tfirst - 1,
        ∃ q_t : Clause (Fin n) → MvPolynomial (Fin n) F,
          (∀ C ∈ blockersFn n hn T, q_t C = 0 ∨ (q_t C).totalDegree + (clausePoly C).totalDegree ≤ d) ∧
          (blockersFn n hn T).sum (fun C => q_t C * clausePoly C) = mon (W t) + mon (W (t + 1)) := by
      intro t ht
      have hstep := hW t (by omega)
      rcases hstep.2.2.2.2 with heq | ⟨j, _, hpre, hST⟩
      · refine ⟨fun _ => 0, fun _ _ => Or.inl rfl, ?_⟩
        rw [heq]; simp; exact (mv_add_self (mon (W (t + 1)))).symm
      · by_cases hj0 : j = 0
        · subst hj0
          have hpeq : proj (W t) = proj (W (t + 1)) := by
            ext idx; simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hST with hT | hS
            · rw [hT, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (h | h); omega; exact h
            · rw [hS, Finset.mem_insert]; constructor
              · rintro (h | h); omega; exact h
              · exact Or.inr
          refine ⟨fun _ => 0, fun _ _ => Or.inl rfl, ?_⟩
          have hmeq : mon (W t) = mon (W (t + 1)) := by simp [mon, hpeq]
          rw [hmeq]; simp; exact (mv_add_self (mon (W (t + 1)))).symm
        · have hjlt : j < len := by
            rcases hST with hT | hS
            · exact htf_before (t + 1) (by omega) j (hT ▸ Finset.mem_insert_self j _)
            · exact htf_before t (by omega) j (hS ▸ Finset.mem_insert_self j _)
          by_cases hsame : W t = W (t + 1)
          · refine ⟨fun _ => 0, fun _ _ => Or.inl rfl, ?_⟩
            rw [hsame]; simp; exact (mv_add_self (mon (W (t + 1)))).symm
          · let idxj : Fin m := ⟨j - 1, by dsimp only [len] at hjlt; omega⟩
            have hv_diff : idxj ∉ proj (W t) ∨ idxj ∉ proj (W (t + 1)) := by
              rcases hST with hT | hS
              · left; intro hmem
                have hjW : j ∈ W t := by
                  have := (Finset.mem_filter.mp hmem).2
                  simpa [idxj, show j - 1 + 1 = j by omega] using this
                exact hsame (hT.trans (Finset.insert_eq_of_mem hjW)).symm
              · right; intro hmem
                have hjW : j ∈ W (t + 1) := by
                  have := (Finset.mem_filter.mp hmem).2
                  simpa [idxj, show j - 1 + 1 = j by omega] using this
                exact hsame (hS.trans (Finset.insert_eq_of_mem hjW))
            let U := proj (W t) ∩ proj (W (t + 1))
            have hmon_eq : mon (W t) + mon (W (t + 1)) = (∏ u ∈ U, Z u) * (1 + Z idxj) := by
              have hprod_ins : ∀ (S0 : Finset (Fin m)), idxj ∉ S0 →
                  (∏ u ∈ S0, Z u) + (∏ u ∈ insert idxj S0, Z u) = (∏ u ∈ S0, Z u) * (1 + Z idxj) := fun S0 h => by
                rw [Finset.prod_insert h]; ring
              rcases hST with hT | hS
              · rcases hv_diff with hnot | hnot
                · have hpB : proj (W (t + 1)) = insert idxj (proj (W t)) := by
                    ext u; simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hT]
                    constructor
                    · rintro (hu | hu)
                      · exact Or.inl (Fin.ext (by dsimp only [idxj]; omega))
                      · exact Or.inr hu
                    · rintro (rfl | hu)
                      · exact Or.inl (by dsimp only [idxj]; omega)
                      · exact Or.inr hu
                  have hUeq : U = proj (W t) := by dsimp only [U]; rw [hpB]; ext u; simp
                  rw [hUeq]; dsimp only [mon]; rw [hpB]; exact hprod_ins _ hnot
                · exfalso
                  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hT, show idxj.val + 1 = j by dsimp [idxj]; omega]; exact Finset.mem_insert_self _ _⟩)
              · rcases hv_diff with hnot | hnot
                · exfalso
                  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hS, show idxj.val + 1 = j by dsimp [idxj]; omega]; exact Finset.mem_insert_self _ _⟩)
                · have hpA : proj (W t) = insert idxj (proj (W (t + 1))) := by
                    ext u; simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hS]
                    constructor
                    · rintro (hu | hu)
                      · exact Or.inl (Fin.ext (by dsimp only [idxj]; omega))
                      · exact Or.inr hu
                    · rintro (rfl | hu)
                      · exact Or.inl (by dsimp only [idxj]; omega)
                      · exact Or.inr hu
                  have hUeq : U = proj (W (t + 1)) := by dsimp only [U]; rw [hpA]; ext u; simp
                  rw [hUeq]; dsimp only [mon]; rw [hpA, add_comm]; exact hprod_ins _ hnot
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
                · have hsub : insert idxj U ⊆ proj (W (t + 1)) := by
                    intro u hu
                    rcases Finset.mem_insert.mp hu with rfl | hU
                    · rcases hST with hT | hS
                      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hT]; simp [idxj]⟩
                      · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hS]; simp [idxj]⟩)
                    · exact (Finset.mem_inter.mp hU).2
                  have hnotU : idxj ∉ U := fun h => hnot (Finset.mem_inter.mp h).1
                  have h1 := Finset.card_le_card hsub
                  rw [Finset.card_insert_of_notMem hnotU] at h1
                  have h2 := hproj_card_of_zero (W (t + 1)) h0_both.2
                  have h3 := hstep.2.1
                  omega
                · have hsub : insert idxj U ⊆ proj (W t) := by
                    intro u hu
                    rcases Finset.mem_insert.mp hu with rfl | hU
                    · rcases hST with hT | hS
                      · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hT]; simp [idxj]⟩)
                      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hS]; simp [idxj]⟩
                    · exact (Finset.mem_inter.mp hU).1
                  have hnotU : idxj ∉ U := fun h => hnot (Finset.mem_inter.mp h).2
                  have h1 := Finset.card_le_card hsub
                  rw [Finset.card_insert_of_notMem hnotU] at h1
                  have h2 := hproj_card_of_zero (W t) h0_both.1
                  have h3 := hstep.1
                  omega
              let cof : MvPolynomial (Fin n) F := ∏ u ∈ U, Z u
              let q_t : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => if C = Cs0 ∨ C = Cs1 then cof else 0
              refine ⟨q_t, ?_, ?_⟩
              · intro C hC
                by_cases hC0 : C = Cs0 ∨ C = Cs1
                · right
                  simp only [q_t, hC0, ↓reduceIte]
                  rw [blockersFn_deg2 hn hn2 T hC]
                  dsimp only [cof]; have := hprod_Z_deg U; omega
                · left; simp [q_t, hC0]
              · rw [← Finset.sum_subset (s₁ := {Cs0, Cs1}) (by
                  intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
                  rcases hC with rfl | rfl; exact hCs0_mem; exact hCs1_mem)]
                · rw [Finset.sum_pair hCs_ne]
                  simp only [q_t, true_or, or_true, ↓reduceIte]
                  rw [← mul_add, h1_Z0, hmon_eq]
                · intro C _ hnot
                  have h1 : ¬ (C = Cs0 ∨ C = Cs1) := by simpa using hnot
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
              let idxp : Fin m := ⟨j - 2, by dsimp only [len] at hjlt; omega⟩
              have hidxp_U : idxp ∈ U :=
                Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [idxp]; rw [show j - 2 + 1 = j - 1 by omega]; exact hjm_both.1⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [idxp]; rw [show j - 2 + 1 = j - 1 by omega]; exact hjm_both.2⟩⟩
              let U' := U.erase idxp
              have hU'_card : U'.card ≤ d - 2 := by
                have hUcard : U.card ≤ d - 1 := by
                  rcases hv_diff with hnot | hnot
                  · have hsub : insert idxj U ⊆ proj (W (t + 1)) := by
                      intro u hu
                      rcases Finset.mem_insert.mp hu with rfl | hU
                      · rcases hST with hT | hS
                        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hT, show idxj.val + 1 = j by dsimp [idxj]; omega]; exact Finset.mem_insert_self _ _⟩
                        · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hS, show idxj.val + 1 = j by dsimp [idxj]; omega]; exact Finset.mem_insert_self _ _⟩)
                      · exact (Finset.mem_inter.mp hU).2
                    have hnotU : idxj ∉ U := fun h => hnot (Finset.mem_inter.mp h).1
                    have h1 := Finset.card_le_card hsub
                    rw [Finset.card_insert_of_notMem hnotU] at h1
                    have h2 := hproj_card (W (t + 1))
                    have h3 := hstep.2.1
                    omega
                  · have hsub : insert idxj U ⊆ proj (W t) := by
                      intro u hu
                      rcases Finset.mem_insert.mp hu with rfl | hU
                      · rcases hST with hT | hS
                        · exfalso; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hT, show idxj.val + 1 = j by dsimp [idxj]; omega]; exact Finset.mem_insert_self _ _⟩)
                        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hS, show idxj.val + 1 = j by dsimp [idxj]; omega]; exact Finset.mem_insert_self _ _⟩
                      · exact (Finset.mem_inter.mp hU).1
                    have hnotU : idxj ∉ U := fun h => hnot (Finset.mem_inter.mp h).2
                    have h1 := Finset.card_le_card hsub
                    rw [Finset.card_insert_of_notMem hnotU] at h1
                    have h2 := hproj_card (W t)
                    have h3 := hstep.1
                    omega
                rw [Finset.card_erase_of_mem hidxp_U]; omega
              have hst_j := hsteps (j - 2) (by dsimp only [len, m] at hjlt; omega)
              rcases stepImp_clause hn hn2 hst_j with ⟨Ck, hCk_mem, hCk_eq⟩
              have hCk_Z : clausePoly Ck = Z idxp * (1 + Z idxj) := by
                rw [hCk_eq]
                dsimp only [Z, idxp, idxj]
                rw [show j - 2 + 1 = j - 1 by omega]
                have hadd := litPoly_add_not (vs (j - 1)) (as (j - 1))
                have h1z : litPoly (vs (j - 1)) (!(as (j - 1))) = 1 + litPoly (vs (j - 1)) (as (j - 1)) := by
                  calc
                    litPoly (vs (j - 1)) (!(as (j - 1))) =
                        (litPoly (vs (j - 1)) (as (j - 1)) + litPoly (vs (j - 1)) (!(as (j - 1)))) +
                        litPoly (vs (j - 1)) (as (j - 1)) := by
                      rw [add_comm (litPoly _ _), add_assoc, mv_add_self, add_zero]
                    _ = 1 + litPoly (vs (j - 1)) (as (j - 1)) := by rw [hadd]
                rw [h1z]
              let cof : MvPolynomial (Fin n) F := ∏ u ∈ U', Z u
              let q_t : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => if C = Ck then cof else 0
              refine ⟨q_t, ?_, ?_⟩
              · intro C hC
                by_cases hCk : C = Ck
                · right
                  simp only [q_t, hCk, ↓reduceIte]
                  rw [blockersFn_deg2 hn hn2 T hCk_mem]
                  dsimp only [cof]; have := hprod_Z_deg U'; omega
                · left; simp [q_t, hCk]
              · rw [Finset.sum_eq_single Ck]
                · simp only [q_t, ↓reduceIte]
                  rw [hCk_Z, hmon_eq]
                  have hprod : (∏ u ∈ U, Z u) = cof * Z idxp := by
                    dsimp only [cof, U']
                    rw [mul_comm, Finset.mul_prod_erase U Z hidxp_U]
                  rw [hprod]; ring
                · intro C _ hne; simp [q_t, hne]
                · intro h; exact absurd hCk_mem h
    let idxlast : Fin m := ⟨L, by dsimp only [m]; omega⟩
    have hidxlast_mem : idxlast ∈ proj (W (tfirst - 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [idxlast, len, m] at *; exact hprev_last.1⟩
    let Uend := (proj (W (tfirst - 1))).erase idxlast
    have hUend_card : Uend.card ≤ d - 2 := by
      rw [Finset.card_erase_of_mem hidxlast_mem]
      have h1 := hproj_card (W (tfirst - 1))
      have h2 := hprev_last.2
      omega
    let cof_end : MvPolynomial (Fin n) F := ∏ u ∈ Uend, Z u
    let q_end : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => if C = Ce0 ∨ C = Ce1 then cof_end else 0
    have hq_end_deg : ∀ C ∈ blockersFn n hn T,
        q_end C = 0 ∨ (q_end C).totalDegree + (clausePoly C).totalDegree ≤ d := by
      intro C hC
      by_cases hCe : C = Ce0 ∨ C = Ce1
      · right
        simp only [q_end, hCe, ↓reduceIte]
        rw [blockersFn_deg2 hn hn2 T hC]
        dsimp only [cof_end]; have := hprod_Z_deg Uend; omega
      · left; simp [q_end, hCe]
    have hq_end_sum : (blockersFn n hn T).sum (fun C => q_end C * clausePoly C) = mon (W (tfirst - 1)) := by
      rw [← Finset.sum_subset (s₁ := {Ce0, Ce1}) (by
        intro C hC; simp only [Finset.mem_insert, Finset.mem_singleton] at hC
        rcases hC with rfl | rfl; exact hCe0_mem; exact hCe1_mem)]
      · rw [Finset.sum_pair hCe_ne]
        simp only [q_end, true_or, or_true, ↓reduceIte]
        rw [← mul_add, hCe_sum]
        dsimp only [mon, cof_end, Uend]
        change (∏ x ∈ (proj (W (tfirst - 1))).erase idxlast, Z x) * Z idxlast = ∏ idx ∈ proj (W (tfirst - 1)), Z idx
        rw [mul_comm, Finset.mul_prod_erase (proj (W (tfirst - 1))) Z hidxlast_mem]
      · intro C _ hnot
        have h1 : ¬ (C = Ce0 ∨ C = Ce1) := by simpa using hnot
        simp [q_end, h1]
    let q_step : Fin (tfirst - 1) → (Clause (Fin n) → MvPolynomial (Fin n) F) :=
      fun t => Classical.choose (hstep_rep t.val t.2)
    have hq_step_deg : ∀ (t : Fin (tfirst - 1)) (C : Clause (Fin n)), C ∈ blockersFn n hn T →
        q_step t C = 0 ∨ (q_step t C).totalDegree + (clausePoly C).totalDegree ≤ d := fun t C hC =>
      (Classical.choose_spec (hstep_rep t.val t.2)).1 C hC
    have hq_step_sum : ∀ t : Fin (tfirst - 1),
        (blockersFn n hn T).sum (fun C => q_step t C * clausePoly C) = mon (W t.val) + mon (W (t.val + 1)) :=
      fun t => (Classical.choose_spec (hstep_rep t.val t.2)).2
    let q_tot : Clause (Fin n) → MvPolynomial (Fin n) F := fun C => (∑ t : Fin (tfirst - 1), q_step t C) + q_end C
    refine ⟨q_tot, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
    · intro C hC
      right
      have hsum_deg : (∑ t : Fin (tfirst - 1), q_step t C).totalDegree ≤ d - 2 := by
        refine le_trans (totalDegree_finset_sum_le _ _) ?_
        rw [Finset.sup_le_iff]
        intro t _
        rcases hq_step_deg t C hC with h0 | hdeg
        · rw [h0]; simp
        · rw [blockersFn_deg2 hn hn2 T hC] at hdeg; omega
      have hend_deg : (q_end C).totalDegree ≤ d - 2 := by
        rcases hq_end_deg C hC with h0 | hdeg
        · rw [h0]; simp
        · rw [blockersFn_deg2 hn hn2 T hC] at hdeg; omega
      have htot_deg : (q_tot C).totalDegree ≤ d - 2 :=
        le_trans (MvPolynomial.totalDegree_add _ _) (max_le hsum_deg hend_deg)
      rw [blockersFn_deg2 hn hn2 T hC]
      omega
    · simp only [zero_mul, Finset.sum_const_zero, add_zero]
      have hdist : (blockersFn n hn T).sum (fun C => q_tot C * clausePoly C) =
          (∑ t : Fin (tfirst - 1), (blockersFn n hn T).sum (fun C => q_step t C * clausePoly C)) +
          (blockersFn n hn T).sum (fun C => q_end C * clausePoly C) := by
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
      have hemp : proj ∅ = ∅ := by ext idx; simp [proj]
      simp [mon, hemp]

end PEqualNP.Outside.L_pcx_245_aux

open PEqualNP.Outside.L_pcx_245_aux
open PEqualNP.ProofComplexity

theorem PEqualNP.Outside.L_pcx_245 :
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
  let rejects := fun candidate : Fin n → Bool → Bool → Bool =>
    ¬ ∃ x : Fin n → Bool, ∀ i : Fin n, candidate i (x i) (x (pos (i.val+1))) = true
  (∀ table, rejects table →
    let G := PEqualNP.ProofComplexity.cnfSystem (↑(blockers table) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    PEqualNP.ProofComplexity.PCRefutable G 2 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable G 1) ∧
  (∀ d : ℕ, (∀ table, rejects table → static (blockers table) d) ↔ (n = 2 ∧ 2 ≤ d) ∨ n+2 < 2^d) := by
  intro n hn hn2 P static pos blockers rejects
  constructor
  · intro table hrej
    exact part1_pc_refutable hn hn2 table hrej
  · intro d
    constructor
    · intro hall
      have hanch := hall (anchoredTable n) (anchoredTable_rejects hn hn2)
      have hd2 := staticFn_ge2 hn hn2 (anchoredTable n) hanch
      by_cases hn2eq : n = 2
      · exact Or.inl ⟨hn2eq, hd2⟩
      · exact Or.inr (anchored_static_lower hn (by omega) hanch)
    · rintro (⟨hn2eq, hd2⟩ | hlt) table hrej
      · exact static_of_n2 hn hn2eq hd2 table hrej
      · have hd2 : 2 ≤ d := by
          by_contra h
          have hd1 : d ≤ 1 := by omega
          interval_cases d <;> omega
        by_cases hn2eq : n = 2
        · exact static_of_n2 hn hn2eq hd2 table hrej
        · by_cases hot : IsOddTwist table
          · exact staticFn_mono hd2 (oddTwist_static2 hn hn2 hot)
          · have hcontra := rejects_not_oddTwist_unit_contra hn hn2 hrej hot
            rcases exists_short_impPath hn (by omega) hcontra with ⟨L, vs, as, hLn, hpath⟩
            exact static_of_short_impPath hn hn2 hLn hlt hpath
