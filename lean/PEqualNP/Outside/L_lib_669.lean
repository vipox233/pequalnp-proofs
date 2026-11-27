import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_669_aux

private abbrev W (n : ℕ) := Fin n → Bool
private abbrev Lit (n : ℕ) := Fin n × Bool
private abbrev F (n : ℕ) := Finset (Lit n × Lit n)

private abbrev satAux {n : ℕ} (A : F n) (z : W n) : Prop :=
  ∀ cl ∈ A, z cl.1.1 ≠ cl.1.2 ∨ z cl.2.1 ≠ cl.2.2

private abbrev massAux {n : ℕ} (A : F n) : ℕ :=
  (Finset.univ.filter (fun x : W n => decide (satAux A x) = true)).card

private def clVars {n : ℕ} (cl : Lit n × Lit n) : Finset (Fin n) :=
  {cl.1.1, cl.2.1}

private def isTaut {n : ℕ} (cl : Lit n × Lit n) : Prop :=
  cl.1.1 = cl.2.1 ∧ cl.1.2 ≠ cl.2.2

private instance {n : ℕ} (cl : Lit n × Lit n) : Decidable (isTaut cl) := by
  unfold isTaut; infer_instance

private def stripTaut {n : ℕ} (A : F n) : F n :=
  A.filter (fun cl => ¬ isTaut cl)

private lemma satAux_stripTaut {n : ℕ} (A : F n) (z : W n) :
    satAux A z ↔ satAux (stripTaut A) z := by
  constructor
  · intro h cl hcl
    exact h cl (Finset.mem_filter.1 hcl).1
  · intro h cl hcl
    by_cases ht : isTaut cl
    · rcases ht with ⟨hv, hb⟩
      rw [← hv]
      cases hz : z cl.1.1 <;> cases hb1 : cl.1.2 <;> cases hb2 : cl.2.2 <;> simp_all
    · exact h cl (Finset.mem_filter.2 ⟨hcl, ht⟩)

private lemma massAux_stripTaut {n : ℕ} (A : F n) :
    massAux (stripTaut A) = massAux A := by
  unfold massAux
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  exact (satAux_stripTaut A z).symm

private lemma card_W (n : ℕ) : (Finset.univ : Finset (W n)).card = 2 ^ n := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp

private lemma card_filter_update1 {n : ℕ} (v : Fin n) (b : Bool) (P : W n → Prop)
    [DecidablePred P] (hP : ∀ z c, P (Function.update z v c) ↔ P z) :
    2 * (Finset.univ.filter (fun z : W n => P z ∧ z v ≠ b)).card =
      (Finset.univ.filter (fun z : W n => P z)).card := by
  let S0 := Finset.univ.filter (fun z : W n => P z ∧ z v ≠ b)
  let S := Finset.univ.filter (fun z : W n => P z)
  have hprod : ((Finset.univ : Finset Bool) ×ˢ S0).card = 2 * S0.card := by
    rw [Finset.card_product]
    simp
  rw [← hprod]
  refine Finset.card_bij (fun (cz : Bool × W n) _ => Function.update cz.2 v cz.1) ?_ ?_ ?_
  · intro cz hcz
    have hz : P cz.2 := (Finset.mem_filter.1 (Finset.mem_product.1 hcz).2).2.1
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hP cz.2 cz.1).2 hz⟩
  · intro cz1 h1 cz2 h2 heq
    have hz1 := (Finset.mem_filter.1 (Finset.mem_product.1 h1).2).2.2
    have hz2 := (Finset.mem_filter.1 (Finset.mem_product.1 h2).2).2.2
    have hc : cz1.1 = cz2.1 := by
      have h := congrArg (fun w : W n => w v) heq
      simpa using h
    apply Prod.ext hc
    funext i
    by_cases hi : i = v
    · subst hi
      cases h1' : cz1.2 i <;> cases h2' : cz2.2 i <;> cases hb : b <;> simp_all
    · have h := congrArg (fun w : W n => w i) heq
      simpa [hi] using h
  · intro z hz
    have hPz : P z := (Finset.mem_filter.1 hz).2
    refine ⟨(z v, Function.update z v (!b)), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨Finset.mem_univ _, ?_⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hP z (!b)).2 hPz, ?_⟩
      cases b <;> simp
    · funext i
      by_cases hi : i = v
      · subst hi; simp
      · simp [hi]

private lemma card_filter_update2 {n : ℕ} {v1 v2 : Fin n} (hne : v1 ≠ v2)
    (b1 b2 : Bool) (P : W n → Prop) [DecidablePred P]
    (hP : ∀ z c1 c2, P (Function.update (Function.update z v1 c1) v2 c2) ↔ P z) :
    4 * (Finset.univ.filter (fun z : W n => P z ∧ (z v1 ≠ b1 ∨ z v2 ≠ b2))).card =
      3 * (Finset.univ.filter (fun z : W n => P z)).card := by
  let Sbad := Finset.univ.filter (fun z : W n => P z ∧ z v1 = b1 ∧ z v2 = b2)
  let Sgood := Finset.univ.filter (fun z : W n => P z ∧ (z v1 ≠ b1 ∨ z v2 ≠ b2))
  let S := Finset.univ.filter (fun z : W n => P z)
  have hdisj : Disjoint Sbad Sgood := by
    refine Finset.disjoint_left.2 fun z h1 h2 => ?_
    have hb := (Finset.mem_filter.1 h1).2.2
    have hg := (Finset.mem_filter.1 h2).2.2
    rcases hg with hne1 | hne2
    · exact hne1 hb.1
    · exact hne2 hb.2
  have hunion : Sbad ∪ Sgood = S := by
    ext z
    simp only [Sbad, Sgood, S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : z v1 = b1 <;> by_cases h2 : z v2 = b2 <;> simp [h1, h2]
  have hsum : Sbad.card + Sgood.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hbad : 4 * Sbad.card = S.card := by
    have hprod : ((Finset.univ : Finset (Bool × Bool)) ×ˢ Sbad).card = 4 * Sbad.card := by
      rw [Finset.card_product]
      have h4 : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
      rw [h4]
    rw [← hprod]
    refine Finset.card_bij
      (fun (pz : (Bool × Bool) × W n) _ => Function.update (Function.update pz.2 v1 pz.1.1) v2 pz.1.2)
      ?_ ?_ ?_
    · intro pz hpz
      have hz : P pz.2 := (Finset.mem_filter.1 (Finset.mem_product.1 hpz).2).2.1
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hP pz.2 pz.1.1 pz.1.2).2 hz⟩
    · intro pz1 h1 pz2 h2 heq
      have hz1 := (Finset.mem_filter.1 (Finset.mem_product.1 h1).2).2.2
      have hz2 := (Finset.mem_filter.1 (Finset.mem_product.1 h2).2).2.2
      have hc2 : pz1.1.2 = pz2.1.2 := by
        have h := congrArg (fun w : W n => w v2) heq
        simpa using h
      have hc1 : pz1.1.1 = pz2.1.1 := by
        have h := congrArg (fun w : W n => w v1) heq
        simpa [hne] using h
      apply Prod.ext (Prod.ext hc1 hc2)
      funext i
      by_cases hi2 : i = v2
      · subst hi2; rw [hz1.2, hz2.2]
      · by_cases hi1 : i = v1
        · subst hi1; rw [hz1.1, hz2.1]
        · have h := congrArg (fun w : W n => w i) heq
          simpa [hi1, hi2] using h
    · intro z hz
      have hPz : P z := (Finset.mem_filter.1 hz).2
      let z0 := Function.update (Function.update z v1 b1) v2 b2
      refine ⟨((z v1, z v2), z0), ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨Finset.mem_univ _, ?_⟩
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hP z b1 b2).2 hPz, ?_, ?_⟩
        · simp [z0, hne]
        · simp [z0]
      · funext i
        by_cases hi2 : i = v2
        · subst hi2; simp [z0]
        · by_cases hi1 : i = v1
          · subst hi1; simp [z0, hne]
          · simp [z0, hi1, hi2]
  show 4 * Sgood.card = 3 * S.card
  omega

private lemma packing_mass_bound {n : ℕ} :
    ∀ M : F n,
      (∀ cl ∈ M, ¬ isTaut cl) →
      (∀ c1 ∈ M, ∀ c2 ∈ M, c1 ≠ c2 → Disjoint (clVars c1) (clVars c2)) →
      4 ^ M.card * massAux M ≤ 3 ^ M.card * 2 ^ n := by
  intro M
  induction M using Finset.induction_on with
  | empty =>
      intro _ _
      simp only [Finset.card_empty, pow_zero, one_mul, massAux, satAux, Finset.notMem_empty,
        IsEmpty.forall_iff, implies_true, decide_true, Finset.filter_true, card_W, le_refl]
  | @insert cl M hcl ih =>
      intro hnt hdisj
      have hntM : ∀ c ∈ M, ¬ isTaut c := fun c hc => hnt c (Finset.mem_insert_of_mem hc)
      have hdisjM : ∀ c1 ∈ M, ∀ c2 ∈ M, c1 ≠ c2 → Disjoint (clVars c1) (clVars c2) :=
        fun c1 h1 c2 h2 hne =>
          hdisj c1 (Finset.mem_insert_of_mem h1) c2 (Finset.mem_insert_of_mem h2) hne
      have hIH := ih hntM hdisjM
      have hcl_nt : ¬ isTaut cl := hnt cl (Finset.mem_insert_self cl M)
      have hcl_disj : ∀ c ∈ M, Disjoint (clVars cl) (clVars c) := by
        intro c hc
        have hne : cl ≠ c := fun h => hcl (h ▸ hc)
        exact hdisj cl (Finset.mem_insert_self cl M) c (Finset.mem_insert_of_mem hc) hne
      have hcl_not_in_M : ∀ v ∈ clVars cl, ∀ c ∈ M, c.1.1 ≠ v ∧ c.2.1 ≠ v := by
        intro v hv c hc
        have hd := hcl_disj c hc
        constructor
        · intro heq
          exact Finset.disjoint_left.1 hd hv (by simp [clVars, heq])
        · intro heq
          exact Finset.disjoint_left.1 hd hv (by simp [clVars, heq])
      have hmass_step : 4 * massAux (insert cl M) ≤ 3 * massAux M := by
        have heq_ins :
            massAux (insert cl M) =
              (Finset.univ.filter (fun z : W n =>
                satAux M z ∧ (z cl.1.1 ≠ cl.1.2 ∨ z cl.2.1 ≠ cl.2.2))).card := by
          unfold massAux
          congr 1
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, satAux,
            Finset.mem_insert, forall_eq_or_imp, and_comm]
        have heq_M : massAux M = (Finset.univ.filter (fun z : W n => satAux M z)).card := by
          refine congrArg Finset.card ?_
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        rw [heq_ins, heq_M]
        by_cases hv : cl.1.1 = cl.2.1
        · have hb : cl.1.2 = cl.2.2 := by
            by_contra hne
            exact hcl_nt ⟨hv, hne⟩
          have hP : ∀ z c, satAux M (Function.update z cl.1.1 c) ↔ satAux M z := by
            intro z c
            have hnv : ∀ d ∈ M, d.1.1 ≠ cl.1.1 ∧ d.2.1 ≠ cl.1.1 :=
              hcl_not_in_M cl.1.1 (by simp [clVars])
            constructor <;> intro h d hd
            · have h1 := h d hd
              rw [Function.update_of_ne (hnv d hd).1, Function.update_of_ne (hnv d hd).2] at h1
              exact h1
            · rw [Function.update_of_ne (hnv d hd).1, Function.update_of_ne (hnv d hd).2]
              exact h d hd
          have h1 := card_filter_update1 cl.1.1 cl.1.2 (satAux M) hP
          have hfilt :
              Finset.univ.filter (fun z : W n =>
                satAux M z ∧ (z cl.1.1 ≠ cl.1.2 ∨ z cl.2.1 ≠ cl.2.2)) =
              Finset.univ.filter (fun z : W n => satAux M z ∧ z cl.1.1 ≠ cl.1.2) := by
            ext z
            simp [hv, hb]
          rw [hfilt]
          omega
        · have hP : ∀ z c1 c2,
              satAux M (Function.update (Function.update z cl.1.1 c1) cl.2.1 c2) ↔ satAux M z := by
            intro z c1 c2
            have hnv1 := hcl_not_in_M cl.1.1 (by simp [clVars])
            have hnv2 := hcl_not_in_M cl.2.1 (by simp [clVars])
            constructor <;> intro h d hd
            · have h1 := h d hd
              rw [Function.update_of_ne (hnv2 d hd).1, Function.update_of_ne (hnv1 d hd).1,
                Function.update_of_ne (hnv2 d hd).2, Function.update_of_ne (hnv1 d hd).2] at h1
              exact h1
            · rw [Function.update_of_ne (hnv2 d hd).1, Function.update_of_ne (hnv1 d hd).1,
                Function.update_of_ne (hnv2 d hd).2, Function.update_of_ne (hnv1 d hd).2]
              exact h d hd
          have h2 := card_filter_update2 hv cl.1.2 cl.2.2 (satAux M) hP
          omega
      rw [Finset.card_insert_of_notMem hcl, pow_succ, pow_succ]
      calc
        4 ^ M.card * 4 * massAux (insert cl M)
            = 4 ^ M.card * (4 * massAux (insert cl M)) := by ring
        _ ≤ 4 ^ M.card * (3 * massAux M) := Nat.mul_le_mul_left _ hmass_step
        _ = 3 * (4 ^ M.card * massAux M) := by ring
        _ ≤ 3 * (3 ^ M.card * 2 ^ n) := Nat.mul_le_mul_left 3 hIH
        _ = 3 ^ M.card * 3 * 2 ^ n := by ring

private lemma pow_four_gt_two_mul_pow_three :
    ∀ r : ℕ, 1 ≤ r → 2 ^ r * 3 ^ (3 * r) < 4 ^ (3 * r)
  | 0, hr => absurd hr (by omega)
  | 1, _ => by decide
  | r + 1, _ => by
      by_cases hr0 : r = 0
      · subst hr0; decide
      · have ih := pow_four_gt_two_mul_pow_three r (by omega)
        have h1 : 3 * (r + 1) = 3 * r + 3 := by omega
        rw [h1, pow_succ, pow_add, pow_add]
        have hpos : 0 < 2 ^ r * 3 ^ (3 * r) :=
          Nat.mul_pos (pow_pos (by decide) r) (pow_pos (by decide) (3 * r))
        have hstep : 2 ^ r * 2 * (3 ^ (3 * r) * 3 ^ 3) =
            (2 ^ r * 3 ^ (3 * r)) * 54 := by ring
        have hrhs : 4 ^ (3 * r) * 4 ^ 3 = 4 ^ (3 * r) * 64 := by ring
        rw [hstep, hrhs]
        omega

private lemma exists_small_cover {n m : ℕ} (A : F n)
    (hdens : 2 ^ n ≤ 2 ^ (m + 1) * massAux A) :
    ∃ C : Finset (Fin n),
      C.card ≤ 6 * (1 + m) ∧
      ∀ cl ∈ stripTaut A, cl.1.1 ∈ C ∨ cl.2.1 ∈ C := by
  let A' := stripTaut A
  let Packings := A'.powerset.filter (fun M =>
    ∀ c1 ∈ M, ∀ c2 ∈ M, c1 ≠ c2 → Disjoint (clVars c1) (clVars c2))
  have hempty : (∅ : F n) ∈ Packings := by
    simp [Packings]
  rcases Finset.exists_max_image Packings Finset.card ⟨∅, hempty⟩ with ⟨M, hM_mem, hM_max⟩
  have hM_sub : M ⊆ A' := Finset.mem_powerset.1 (Finset.mem_filter.1 hM_mem).1
  have hM_disj : ∀ c1 ∈ M, ∀ c2 ∈ M, c1 ≠ c2 → Disjoint (clVars c1) (clVars c2) :=
    (Finset.mem_filter.1 hM_mem).2
  have hM_nt : ∀ cl ∈ M, ¬ isTaut cl := fun cl hcl => (Finset.mem_filter.1 (hM_sub hcl)).2
  let C : Finset (Fin n) := M.biUnion clVars
  have hcover : ∀ cl ∈ A', cl.1.1 ∈ C ∨ cl.2.1 ∈ C := by
    intro cl hcl
    by_contra hno
    push Not at hno
    have hdisj_cl : ∀ c ∈ M, Disjoint (clVars cl) (clVars c) := by
      intro c hc
      refine Finset.disjoint_left.2 fun v hv1 hv2 => ?_
      have hvC : v ∈ C := Finset.mem_biUnion.2 ⟨c, hc, hv2⟩
      simp only [clVars, Finset.mem_insert, Finset.mem_singleton] at hv1
      rcases hv1 with rfl | rfl
      · exact hno.1 hvC
      · exact hno.2 hvC
    have hnotM : cl ∉ M := by
      intro hmem
      have h1 : cl.1.1 ∈ C := Finset.mem_biUnion.2 ⟨cl, hmem, by simp [clVars]⟩
      exact hno.1 h1
    have hins_mem : insert cl M ∈ Packings := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hcl hM_sub), ?_⟩
      intro c1 h1 c2 h2 hne
      rcases Finset.mem_insert.1 h1 with rfl | h1M
      · rcases Finset.mem_insert.1 h2 with rfl | h2M
        · exact absurd rfl hne
        · exact hdisj_cl c2 h2M
      · rcases Finset.mem_insert.1 h2 with rfl | h2M
        · exact (hdisj_cl c1 h1M).symm
        · exact hM_disj c1 h1M c2 h2M hne
    have hle := hM_max (insert cl M) hins_mem
    rw [Finset.card_insert_of_notMem hnotM] at hle
    omega
  have hmass_le : massAux A ≤ massAux M := by
    rw [← massAux_stripTaut A]
    refine Finset.card_le_card fun z hz => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hz ⊢
    intro cl hcl
    exact hz cl (hM_sub hcl)
  have hpack := packing_mass_bound M hM_nt hM_disj
  have hmul : 4 ^ M.card * 2 ^ n ≤ 2 ^ (m + 1) * 3 ^ M.card * 2 ^ n := by
    calc
      4 ^ M.card * 2 ^ n
          ≤ 4 ^ M.card * (2 ^ (m + 1) * massAux A) := Nat.mul_le_mul_left _ hdens
      _ ≤ 4 ^ M.card * (2 ^ (m + 1) * massAux M) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmass_le)
      _ = 2 ^ (m + 1) * (4 ^ M.card * massAux M) := by ring
      _ ≤ 2 ^ (m + 1) * (3 ^ M.card * 2 ^ n) := Nat.mul_le_mul_left _ hpack
      _ = 2 ^ (m + 1) * 3 ^ M.card * 2 ^ n := by ring
  have hpow_le : 4 ^ M.card ≤ 2 ^ (m + 1) * 3 ^ M.card :=
    Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide : 0 < 2) n)
  have hM_lt : M.card < 3 * (m + 1) := by
    by_contra hge
    push Not at hge
    have hstrict := pow_four_gt_two_mul_pow_three (m + 1) (by omega)
    let d := M.card - 3 * (m + 1)
    have hdecomp : M.card = 3 * (m + 1) + d := by omega
    have hpow_le' : 4 ^ (3 * (m + 1)) * 4 ^ d ≤ 2 ^ (m + 1) * (3 ^ (3 * (m + 1)) * 3 ^ d) := by
      rw [← pow_add, ← pow_add, ← hdecomp]
      exact hpow_le
    have h34 : 3 ^ d ≤ 4 ^ d := Nat.pow_le_pow_left (by decide) d
    have h4pos : 0 < 4 ^ d := pow_pos (by decide) d
    have hlt1 : 2 ^ (m + 1) * (3 ^ (3 * (m + 1)) * 3 ^ d) ≤
        2 ^ (m + 1) * 3 ^ (3 * (m + 1)) * 4 ^ d := by
      have : 2 ^ (m + 1) * (3 ^ (3 * (m + 1)) * 3 ^ d) =
          (2 ^ (m + 1) * 3 ^ (3 * (m + 1))) * 3 ^ d := by ring
      rw [this]
      exact Nat.mul_le_mul_left _ h34
    have hlt2 : 2 ^ (m + 1) * 3 ^ (3 * (m + 1)) * 4 ^ d < 4 ^ (3 * (m + 1)) * 4 ^ d :=
      Nat.mul_lt_mul_of_pos_right hstrict h4pos
    omega
  have hC_card : C.card ≤ 2 * M.card := by
    calc
      C.card ≤ ∑ cl ∈ M, (clVars cl).card := Finset.card_biUnion_le
      _ ≤ ∑ _cl ∈ M, 2 := Finset.sum_le_sum fun cl _ => Finset.card_le_two
      _ = 2 * M.card := by simp [mul_comm]
  exact ⟨C, by omega, hcover⟩

private def Forbid {n : ℕ} (A' : F n) (C : Finset (Fin n)) (α : {x : Fin n // x ∈ C} → Bool)
    (v : Fin n) (b : Bool) : Prop :=
  v ∉ C ∧ ∃ cl ∈ A',
    (∃ h : cl.1.1 ∈ C, α ⟨cl.1.1, h⟩ = cl.1.2 ∧ cl.2 = (v, b)) ∨
    (∃ h : cl.2.1 ∈ C, α ⟨cl.2.1, h⟩ = cl.2.2 ∧ cl.1 = (v, b))

private instance {n : ℕ} (A' : F n) (C : Finset (Fin n)) (α : {x : Fin n // x ∈ C} → Bool)
    (v : Fin n) (b : Bool) : Decidable (Forbid A' C α v b) := by
  unfold Forbid; infer_instance

private def forcedVars {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (α : {x : Fin n // x ∈ C} → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => Forbid A' C α v false ∨ Forbid A' C α v true)

private def fiber {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (α : {x : Fin n // x ∈ C} → Bool) : Finset (W n) :=
  Finset.univ.filter (fun z => satAux A' z ∧ ∀ v : {x : Fin n // x ∈ C}, z v.1 = α v)

private def expOf {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (α : {x : Fin n // x ∈ C} → Bool) : ℕ :=
  C.card + (forcedVars A' C α).card

private lemma forbid_forces {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (α : {x : Fin n // x ∈ C} → Bool) {z : W n} (hz : z ∈ fiber A' C α)
    {v : Fin n} {b : Bool} (hf : Forbid A' C α v b) :
    z v ≠ b := by
  have hsat : satAux A' z := (Finset.mem_filter.1 hz).2.1
  have hα : ∀ u : {x : Fin n // x ∈ C}, z u.1 = α u := (Finset.mem_filter.1 hz).2.2
  rcases hf.2 with ⟨cl, hcl, ⟨h1, hα1, hcl2⟩ | ⟨h2, hα2, hcl1⟩⟩
  · have hor := hsat cl hcl
    rw [hα ⟨cl.1.1, h1⟩, hα1] at hor
    rcases hor with hbad | hok
    · exact absurd rfl hbad
    · rw [hcl2] at hok; exact hok
  · have hor := hsat cl hcl
    rw [hα ⟨cl.2.1, h2⟩, hα2] at hor
    rcases hor with hok | hbad
    · rw [hcl1] at hok; exact hok
    · exact absurd rfl hbad

private lemma fiber_card_eq {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (hcover : ∀ cl ∈ A', cl.1.1 ∈ C ∨ cl.2.1 ∈ C)
    (α : {x : Fin n // x ∈ C} → Bool) (hne : (fiber A' C α).Nonempty) :
    expOf A' C α ≤ n ∧ (fiber A' C α).card = 2 ^ (n - expOf A' C α) := by
  let D := forcedVars A' C α
  have hdisjCD : Disjoint C D := by
    refine Finset.disjoint_left.2 fun v hvC hvD => ?_
    rcases (Finset.mem_filter.1 hvD).2 with hf | ht
    · exact hf.1 hvC
    · exact ht.1 hvC
  have hUcard : (C ∪ D).card = expOf A' C α := by
    rw [Finset.card_union_of_disjoint hdisjCD]
    rfl
  have hexp_le : expOf A' C α ≤ n := by
    rw [← hUcard]
    simpa using Finset.card_le_univ (C ∪ D)
  refine ⟨hexp_le, ?_⟩
  let Free : Finset (Fin n) := Finset.univ \ (C ∪ D)
  have hFree_card : Free.card = n - expOf A' C α := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hUcard]
  rcases hne with ⟨z0, hz0⟩
  have hcard_bij : (fiber A' C α).card = Free.powerset.card := by
    refine Finset.card_bij (fun z _ => Free.filter (fun v => z v = true)) ?_ ?_ ?_
    · intro z _
      exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
    · intro z1 h1 z2 h2 heq
      funext v
      by_cases hvC : v ∈ C
      · rw [(Finset.mem_filter.1 h1).2.2 ⟨v, hvC⟩, (Finset.mem_filter.1 h2).2.2 ⟨v, hvC⟩]
      · by_cases hvD : v ∈ D
        · rcases (Finset.mem_filter.1 hvD).2 with hf | ht
          · have e1 := forbid_forces A' C α h1 hf
            have e2 := forbid_forces A' C α h2 hf
            cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
          · have e1 := forbid_forces A' C α h1 ht
            have e2 := forbid_forces A' C α h2 ht
            cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
        · have hvF : v ∈ Free := Finset.mem_sdiff.2
            ⟨Finset.mem_univ v, by simp [hvC, hvD]⟩
          have hmem : v ∈ Free.filter (fun x => z1 x = true) ↔
              v ∈ Free.filter (fun x => z2 x = true) := by rw [heq]
          simp only [Finset.mem_filter, hvF, true_and] at hmem
          cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
    · intro T hT
      have hTF : T ⊆ Free := Finset.mem_powerset.1 hT
      let z : W n := fun v => if v ∈ Free then decide (v ∈ T) else z0 v
      have hz_notF : ∀ v, v ∉ Free → z v = z0 v := by
        intro v hv; simp [z, hv]
      have hz_C : ∀ v : {x : Fin n // x ∈ C}, z v.1 = α v := by
        intro v
        have hnf : v.1 ∉ Free := by simp [Free, v.2]
        rw [hz_notF v.1 hnf]
        exact (Finset.mem_filter.1 hz0).2.2 v
      have hz_sat : satAux A' z := by
        intro cl hcl
        have hsat0 := (Finset.mem_filter.1 hz0).2.1 cl hcl
        have hα0 := (Finset.mem_filter.1 hz0).2.2
        rcases hcover cl hcl with h1C | h2C
        · by_cases h2C : cl.2.1 ∈ C
          · rw [hz_C ⟨cl.1.1, h1C⟩, hz_C ⟨cl.2.1, h2C⟩]
            rw [hα0 ⟨cl.1.1, h1C⟩, hα0 ⟨cl.2.1, h2C⟩] at hsat0
            exact hsat0
          · by_cases hact : α ⟨cl.1.1, h1C⟩ = cl.1.2
            · right
              have hf : Forbid A' C α cl.2.1 cl.2.2 :=
                ⟨h2C, cl, hcl, Or.inl ⟨h1C, hact, by cases cl.2; rfl⟩⟩
              have hD2 : cl.2.1 ∈ D := by
                refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
                cases hb : cl.2.2
                · exact Or.inl (hb ▸ hf)
                · exact Or.inr (hb ▸ hf)
              have hnf2 : cl.2.1 ∉ Free := by simp [Free, hD2]
              rw [hz_notF cl.2.1 hnf2]
              exact forbid_forces A' C α hz0 hf
            · left
              rw [hz_C ⟨cl.1.1, h1C⟩]
              exact hact
        · by_cases h1C : cl.1.1 ∈ C
          · rw [hz_C ⟨cl.1.1, h1C⟩, hz_C ⟨cl.2.1, h2C⟩]
            rw [hα0 ⟨cl.1.1, h1C⟩, hα0 ⟨cl.2.1, h2C⟩] at hsat0
            exact hsat0
          · by_cases hact : α ⟨cl.2.1, h2C⟩ = cl.2.2
            · left
              have hf : Forbid A' C α cl.1.1 cl.1.2 :=
                ⟨h1C, cl, hcl, Or.inr ⟨h2C, hact, by cases cl.1; rfl⟩⟩
              have hD1 : cl.1.1 ∈ D := by
                refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
                cases hb : cl.1.2
                · exact Or.inl (hb ▸ hf)
                · exact Or.inr (hb ▸ hf)
              have hnf1 : cl.1.1 ∉ Free := by simp [Free, hD1]
              rw [hz_notF cl.1.1 hnf1]
              exact forbid_forces A' C α hz0 hf
            · right
              rw [hz_C ⟨cl.2.1, h2C⟩]
              exact hact
      refine ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz_sat, hz_C⟩, ?_⟩
      ext v
      simp only [Finset.mem_filter, z]
      by_cases hv : v ∈ Free
      · simp [hv]
      · simp only [hv, false_and, false_iff]
        intro hvT
        exact hv (hTF hvT)
  rw [hcard_bij, Finset.card_powerset, hFree_card]

private lemma massAux_eq_sum_fibers {n : ℕ} (A' : F n) (C : Finset (Fin n)) :
    massAux A' =
      ∑ α ∈ (Finset.univ : Finset ({x : Fin n // x ∈ C} → Bool)).filter
        (fun α => (fiber A' C α).Nonempty), (fiber A' C α).card := by
  let S := Finset.univ.filter (fun z : W n => decide (satAux A' z) = true)
  let Act := (Finset.univ : Finset ({x : Fin n // x ∈ C} → Bool)).filter
    (fun α => (fiber A' C α).Nonempty)
  have hmaps : ∀ z ∈ S, (fun v : {x : Fin n // x ∈ C} => z v.1) ∈ Act := by
    intro z hz
    have hsat : satAux A' z := of_decide_eq_true (Finset.mem_filter.1 hz).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨z, ?_⟩⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsat, fun _ => rfl⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  change S.card = ∑ α ∈ Act, (fiber A' C α).card
  rw [hsum]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  ext z
  simp only [S, fiber, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
    funext_iff]

private def insertBy {α : Type*} (f : α → ℕ) (a : α) : List α → List α
  | [] => [a]
  | x :: xs => if f a ≤ f x then a :: x :: xs else x :: insertBy f a xs

private def sortBy {α : Type*} (f : α → ℕ) : List α → List α
  | [] => []
  | x :: xs => insertBy f x (sortBy f xs)

private lemma insertBy_perm {α : Type*} (f : α → ℕ) (a : α) :
    ∀ l : List α, (insertBy f a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | x :: xs => by
      unfold insertBy
      split_ifs
      · exact List.Perm.refl _
      · exact (List.Perm.cons x (insertBy_perm f a xs)).trans (List.Perm.swap a x xs)

private lemma sortBy_perm {α : Type*} (f : α → ℕ) :
    ∀ l : List α, (sortBy f l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertBy_perm f x (sortBy f xs)).trans (List.Perm.cons x (sortBy_perm f xs))

private lemma insertBy_pairwise {α : Type*} (f : α → ℕ) (a : α) :
    ∀ l : List α, l.Pairwise (fun x y => f x ≤ f y) →
      (insertBy f a l).Pairwise (fun x y => f x ≤ f y)
  | [], _ => List.pairwise_singleton _ _
  | x :: xs, hp => by
      unfold insertBy
      split_ifs with hle
      · rw [List.pairwise_cons] at hp ⊢
        refine ⟨?_, List.pairwise_cons.2 hp⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hyxs
        · exact hle
        · exact le_trans hle (hp.1 y hyxs)
      · rw [List.pairwise_cons] at hp ⊢
        refine ⟨?_, insertBy_pairwise f a xs hp.2⟩
        intro y hy
        have hmem : y ∈ a :: xs := (insertBy_perm f a xs).mem_iff.1 hy
        rcases List.mem_cons.1 hmem with rfl | hyxs
        · omega
        · exact hp.1 y hyxs

private lemma sortBy_pairwise {α : Type*} (f : α → ℕ) :
    ∀ l : List α, (sortBy f l).Pairwise (fun x y => f x ≤ f y)
  | [] => List.Pairwise.nil
  | x :: xs => insertBy_pairwise f x (sortBy f xs) (sortBy_pairwise f xs)

private lemma pairwise_le_getElem {l : List ℕ} (hp : l.Pairwise (· ≤ ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[i] ≤ l[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact List.pairwise_iff_getElem.1 hp i j hi hj hlt

private def sumE (n : ℕ) (l : List ℕ) : ℕ :=
  (l.map (fun e => 2 ^ (n - e))).sum

private lemma sumE_append (n : ℕ) (l1 l2 : List ℕ) :
    sumE n (l1 ++ l2) = sumE n l1 + sumE n l2 := by
  simp [sumE, List.map_append, List.sum_append]

private lemma sumE_take_add_drop (n : ℕ) (l : List ℕ) (k : ℕ) :
    sumE n (l.take k) + sumE n (l.drop k) = sumE n l := by
  rw [← sumE_append, List.take_append_drop]

private lemma dvd_sumE_of_le (n e_max : ℕ) :
    ∀ l : List ℕ, (∀ e ∈ l, e ≤ e_max) → 2 ^ (n - e_max) ∣ sumE n l
  | [], _ => dvd_zero _
  | e :: es, hle => by
      have he : e ≤ e_max := hle e (by simp)
      have h1 : 2 ^ (n - e_max) ∣ 2 ^ (n - e) := Nat.pow_dvd_pow 2 (by omega)
      have h2 := dvd_sumE_of_le n e_max es (fun x hx => hle x (by simp [hx]))
      simpa [sumE] using dvd_add h1 h2

private lemma sumE_le_length_mul (n e_min : ℕ) :
    ∀ l : List ℕ, (∀ e ∈ l, e_min ≤ e) → sumE n l ≤ l.length * 2 ^ (n - e_min)
  | [], _ => by simp [sumE]
  | e :: es, hge => by
      have he : e_min ≤ e := hge e (by simp)
      have h1 : 2 ^ (n - e) ≤ 2 ^ (n - e_min) := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 := sumE_le_length_mul n e_min es (fun x hx => hge x (by simp [hx]))
      simp only [sumE, List.map_cons, List.sum_cons, List.length_cons]
      have : (es.length + 1) * 2 ^ (n - e_min) = 2 ^ (n - e_min) + es.length * 2 ^ (n - e_min) := by
        ring
      rw [this]
      exact Nat.add_le_add h1 h2

private def noJump (es : List ℕ) (L : ℕ) (k : ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < k) → (hil : i < es.length) →
    es[i] < (if h0 : i = 0 then 0 else es[i - 1]'(by omega)) + L

private instance (es : List ℕ) (L k : ℕ) : Decidable (noJump es L k) := by
  unfold noJump; infer_instance

private lemma noJump_bound {es : List ℕ} {L k : ℕ} (hnj : noJump es L k) :
    ∀ i : ℕ, (hi : i < k) → (hil : i < es.length) → es[i] < (i + 1) * L
  | 0, hi, hil => by
      have h := hnj 0 hi hil
      simpa using h
  | i + 1, hi, hil => by
      have ih := noJump_bound hnj i (by omega) (by omega)
      have h := hnj (i + 1) hi hil
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel] at h
      have hmul : (i + 1 + 1) * L = (i + 1) * L + L := by ring
      omega

private lemma dyadic_gap_or_prefix {p q c n : ℕ} (hp : 0 < p)
    (es : List ℕ) (hsorted : es.Pairwise (· ≤ ·))
    (hlen : es.length ≤ 2 ^ c) (hle_n : ∀ e ∈ es, e ≤ n) :
    let L := Nat.clog 2 q + c + 1
    let H := 2 ^ c * L
    (p * 2 ^ n ≤ q * sumE n es →
      ∃ k ≤ es.length, p * 2 ^ n ≤ q * sumE n (es.take k) ∧ ∀ e ∈ es.take k, e ≤ H) ∧
    (q * sumE n es < p * 2 ^ n →
      q * sumE n es * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1)) := by
  intro L H
  have h2L : 2 * q * 2 ^ c ≤ 2 ^ L := by
    have hq : q ≤ 2 ^ Nat.clog 2 q := Nat.le_pow_clog (by decide : 1 < 2) q
    have h1 : 2 ^ L = 2 * 2 ^ Nat.clog 2 q * 2 ^ c := by
      dsimp only [L]
      rw [pow_succ, pow_add]
      ring
    rw [h1]
    have h2 : 2 * q * 2 ^ c = 2 * 2 ^ c * q := by ring
    have h3 : 2 * 2 ^ Nat.clog 2 q * 2 ^ c = 2 * 2 ^ c * 2 ^ Nat.clog 2 q := by ring
    rw [h2, h3]
    exact Nat.mul_le_mul_left _ hq
  let goodK := (Finset.range (es.length + 1)).filter (fun k => noJump es L k)
  have h0_mem : 0 ∈ goodK := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos _), ?_⟩
    intro i hi _
    omega
  let kmax := goodK.max' ⟨0, h0_mem⟩
  have hkmax_mem : kmax ∈ goodK := Finset.max'_mem goodK ⟨0, h0_mem⟩
  have hkmax_le : kmax ≤ es.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hkmax_mem).1)
  have hkmax_nj : noJump es L kmax := (Finset.mem_filter.1 hkmax_mem).2
  have htake_le_H : ∀ e ∈ es.take kmax, e ≤ H := by
    intro e he
    rcases List.mem_iff_getElem.1 he with ⟨i, hi_len, rfl⟩
    have hi_k : i < kmax := by
      have : (es.take kmax).length = kmax := List.length_take_of_le hkmax_le
      omega
    have hi_es : i < es.length := by omega
    rw [List.getElem_take]
    have hb := noJump_bound hkmax_nj i hi_k hi_es
    have hmul : (i + 1) * L ≤ 2 ^ c * L := Nat.mul_le_mul_right L (by omega)
    exact le_of_lt (lt_of_lt_of_le hb hmul)
  have hgap_of_lt_prefix :
      kmax < es.length → q * sumE n (es.take kmax) < p * 2 ^ n →
        q * sumE n es * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1) := by
    intro hk_lt hpref_lt
    have hnot_succ : ¬ noJump es L (kmax + 1) := by
      intro hnj1
      have hmem1 : kmax + 1 ∈ goodK :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hnj1⟩
      have hle := Finset.le_max' goodK (kmax + 1) hmem1
      omega
    let e_prev : ℕ := if h0 : kmax = 0 then 0 else es[kmax - 1]'(by omega)
    have hjmp : e_prev + L ≤ es[kmax]'hk_lt := by
      by_contra hlt_j
      push Not at hlt_j
      apply hnot_succ
      intro i hi hil
      by_cases hik : i < kmax
      · exact hkmax_nj i hik hil
      · have hieq : i = kmax := by omega
        subst hieq
        exact hlt_j
    have he_prev_le_H : e_prev ≤ H := by
      by_cases h0 : kmax = 0
      · simp [e_prev, h0]
      · simp only [e_prev, h0, ↓reduceDIte]
        have hb := noJump_bound hkmax_nj (kmax - 1) (by omega) (by omega)
        have hmul : (kmax - 1 + 1) * L ≤ 2 ^ c * L := Nat.mul_le_mul_right L (by omega)
        omega
    have he_prev_le_n : e_prev ≤ n := by
      by_cases h0 : kmax = 0
      · simp [e_prev, h0]
      · simp only [e_prev, h0, ↓reduceDIte]
        exact hle_n _ (List.getElem_mem _)
    have hek_le_n : es[kmax]'hk_lt ≤ n := hle_n _ (List.getElem_mem _)
    have hpref_dvd : 2 ^ (n - e_prev) ∣ sumE n (es.take kmax) := by
      refine dvd_sumE_of_le n e_prev (es.take kmax) fun e he => ?_
      rcases List.mem_iff_getElem.1 he with ⟨i, hi_len, rfl⟩
      have hi_k : i < kmax := by
        have : (es.take kmax).length = kmax := List.length_take_of_le hkmax_le
        omega
      rw [List.getElem_take]
      have h0 : kmax ≠ 0 := by omega
      simp only [e_prev, h0, ↓reduceDIte]
      exact pairwise_le_getElem hsorted (by omega) (by omega) (by omega)
    have h2n_dvd : 2 ^ (n - e_prev) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
    have hgap1 : q * sumE n (es.take kmax) + 2 ^ (n - e_prev) ≤ p * 2 ^ n := by
      have hd1 : 2 ^ (n - e_prev) ∣ p * 2 ^ n := dvd_mul_of_dvd_right h2n_dvd p
      have hd2 : 2 ^ (n - e_prev) ∣ q * sumE n (es.take kmax) := dvd_mul_of_dvd_right hpref_dvd q
      rcases hd1 with ⟨a, ha⟩
      rcases hd2 with ⟨b, hb⟩
      rw [ha, hb] at hpref_lt ⊢
      have hba : b + 1 ≤ a := by
        have hpos : 0 < 2 ^ (n - e_prev) := pow_pos (by decide) _
        have : b < a := by
          by_contra hge
          push Not at hge
          have := Nat.mul_le_mul_left (2 ^ (n - e_prev)) hge
          omega
        omega
      calc
        2 ^ (n - e_prev) * b + 2 ^ (n - e_prev) = 2 ^ (n - e_prev) * (b + 1) := by ring
        _ ≤ 2 ^ (n - e_prev) * a := Nat.mul_le_mul_left _ hba
    have htail_ge : ∀ e ∈ es.drop kmax, es[kmax]'hk_lt ≤ e := by
      intro e he
      rcases List.mem_iff_getElem.1 he with ⟨i, hi_len, rfl⟩
      rw [List.getElem_drop]
      have hlt_es : kmax + i < es.length := by
        rw [List.length_drop] at hi_len; omega
      exact pairwise_le_getElem hsorted hk_lt hlt_es (by omega)
    have htail_le : sumE n (es.drop kmax) ≤ 2 ^ c * 2 ^ (n - es[kmax]'hk_lt) := by
      have h1 := sumE_le_length_mul n (es[kmax]'hk_lt) (es.drop kmax) htail_ge
      have hlen_d : (es.drop kmax).length ≤ 2 ^ c := by
        rw [List.length_drop]; omega
      exact le_trans h1 (Nat.mul_le_mul_right _ hlen_d)
    have h2q_tail : 2 * (q * sumE n (es.drop kmax)) ≤ 2 ^ (n - e_prev) := by
      calc
        2 * (q * sumE n (es.drop kmax))
            ≤ 2 * (q * (2 ^ c * 2 ^ (n - es[kmax]'hk_lt))) :=
              Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left q htail_le)
        _ = (2 * q * 2 ^ c) * 2 ^ (n - es[kmax]'hk_lt) := by ring
        _ ≤ 2 ^ L * 2 ^ (n - es[kmax]'hk_lt) := Nat.mul_le_mul_right _ h2L
        _ = 2 ^ (L + (n - es[kmax]'hk_lt)) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ (n - e_prev) := Nat.pow_le_pow_right (by decide) (by omega)
    have hhalf : 2 * (q * sumE n es) + 2 ^ (n - e_prev) ≤ 2 * (p * 2 ^ n) := by
      have hsum_eq := sumE_take_add_drop n es kmax
      rw [← hsum_eq, mul_add]
      omega
    have hmul_prev := Nat.mul_le_mul_right (2 ^ e_prev) hhalf
    have hpow_n : 2 ^ (n - e_prev) * 2 ^ e_prev = 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel he_prev_le_n]
    have hpow_e : q * sumE n es * 2 ^ (e_prev + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (e_prev + 1) := by
      have h1 : (2 * (q * sumE n es) + 2 ^ (n - e_prev)) * 2 ^ e_prev =
          q * sumE n es * 2 ^ (e_prev + 1) + 2 ^ n := by
        rw [add_mul, hpow_n, pow_succ]
        ring
      have h2 : 2 * (p * 2 ^ n) * 2 ^ e_prev = p * 2 ^ n * 2 ^ (e_prev + 1) := by
        rw [pow_succ]; ring
      rw [h1, h2] at hmul_prev
      exact hmul_prev
    have hmul_H := Nat.mul_le_mul_right (2 ^ (H - e_prev)) hpow_e
    have hpow_H : 2 ^ (e_prev + 1) * 2 ^ (H - e_prev) = 2 ^ (H + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h1_le : 1 ≤ 2 ^ (H - e_prev) := Nat.one_le_two_pow
    have h2n_le : 2 ^ n ≤ 2 ^ n * 2 ^ (H - e_prev) := Nat.le_mul_of_pos_right _ (by omega)
    have hL_eq : (q * sumE n es * 2 ^ (e_prev + 1) + 2 ^ n) * 2 ^ (H - e_prev) =
        q * sumE n es * 2 ^ (H + 1) + 2 ^ n * 2 ^ (H - e_prev) := by
      rw [add_mul, mul_assoc, hpow_H]
    have hR_eq : p * 2 ^ n * 2 ^ (e_prev + 1) * 2 ^ (H - e_prev) = p * 2 ^ n * 2 ^ (H + 1) := by
      rw [mul_assoc, hpow_H]
    rw [hL_eq, hR_eq] at hmul_H
    omega
  constructor
  · intro hge
    by_cases hlt : kmax < es.length
    · by_cases hpref : p * 2 ^ n ≤ q * sumE n (es.take kmax)
      · exact ⟨kmax, hkmax_le, hpref, htake_le_H⟩
      · push Not at hpref
        have hgap := hgap_of_lt_prefix hlt hpref
        have hpos : 0 < 2 ^ n := pow_pos (by decide) n
        have hmul_ge := Nat.mul_le_mul_right (2 ^ (H + 1)) hge
        omega
    · have hkeq : kmax = es.length := by omega
      refine ⟨es.length, le_refl _, ?_, ?_⟩
      · rw [List.take_length]; exact hge
      · rw [← hkeq]; exact htake_le_H
  · intro hlt_all
    by_cases hlt : kmax < es.length
    · have hpref_le : sumE n (es.take kmax) ≤ sumE n es := by
        have := sumE_take_add_drop n es kmax; omega
      have hpref_lt : q * sumE n (es.take kmax) < p * 2 ^ n :=
        lt_of_le_of_lt (Nat.mul_le_mul_left q hpref_le) hlt_all
      exact hgap_of_lt_prefix hlt hpref_lt
    · have hkeq : kmax = es.length := by omega
      by_cases hlen0 : es.length = 0
      · have hes : es = [] := List.eq_nil_of_length_eq_zero hlen0
        rw [hes]
        simp only [sumE, List.map_nil, List.sum_nil, mul_zero, zero_mul, zero_add]
        have h1 : 1 ≤ p * 2 ^ (H + 1) := Nat.mul_pos hp (pow_pos (by decide) _)
        calc
          2 ^ n = 2 ^ n * 1 := (mul_one _).symm
          _ ≤ 2 ^ n * (p * 2 ^ (H + 1)) := Nat.mul_le_mul_left _ h1
          _ = p * 2 ^ n * 2 ^ (H + 1) := by ring
      · let e_last := es[es.length - 1]'(by omega)
        have he_last_le_n : e_last ≤ n := hle_n _ (List.getElem_mem _)
        have he_last_le_H : e_last ≤ H := by
          have hmem : e_last ∈ es.take kmax := by
            rw [hkeq, List.take_length]
            exact List.getElem_mem _
          exact htake_le_H e_last hmem
        have hdvd_es : 2 ^ (n - e_last) ∣ sumE n es := by
          refine dvd_sumE_of_le n e_last es fun e he => ?_
          rcases List.mem_iff_getElem.1 he with ⟨i, hi, rfl⟩
          exact pairwise_le_getElem hsorted hi (by omega) (by omega)
        have hdvd_2n : 2 ^ (n - e_last) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
        have hgap1 : q * sumE n es + 2 ^ (n - e_last) ≤ p * 2 ^ n := by
          rcases dvd_mul_of_dvd_right hdvd_2n p with ⟨a, ha⟩
          rcases dvd_mul_of_dvd_right hdvd_es q with ⟨b, hb⟩
          rw [ha, hb] at hlt_all ⊢
          have hba : b + 1 ≤ a := by
            have hpos : 0 < 2 ^ (n - e_last) := pow_pos (by decide) _
            have : b < a := by
              by_contra hge
              push Not at hge
              have := Nat.mul_le_mul_left (2 ^ (n - e_last)) hge
              omega
            omega
          calc
            2 ^ (n - e_last) * b + 2 ^ (n - e_last) = 2 ^ (n - e_last) * (b + 1) := by ring
            _ ≤ 2 ^ (n - e_last) * a := Nat.mul_le_mul_left _ hba
        have hmul := Nat.mul_le_mul_right (2 ^ (H + 1)) hgap1
        have h2n_le : 2 ^ n ≤ 2 ^ (n - e_last) * 2 ^ (H + 1) := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        rw [add_mul] at hmul
        omega

private def outNbr {n : ℕ} (A' : F n) (C : Finset (Fin n)) (l : Lit n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => w ∉ C ∧
    ∃ b2 : Bool, (l, (w, b2)) ∈ A' ∨ ((w, b2), l) ∈ A')

private lemma outNbr_subset_forcedVars {n : ℕ} (A' : F n) (C : Finset (Fin n))
    (α : {x : Fin n // x ∈ C} → Bool) {l : Lit n} (hlC : l.1 ∈ C) (hact : α ⟨l.1, hlC⟩ = l.2) :
    outNbr A' C l ⊆ forcedVars A' C α := by
  intro w hw
  rcases (Finset.mem_filter.1 hw).2 with ⟨hwC, b2, hcl | hcl⟩
  · have hf : Forbid A' C α w b2 := ⟨hwC, (l, (w, b2)), hcl, Or.inl ⟨hlC, hact, rfl⟩⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    cases b2
    · exact Or.inl hf
    · exact Or.inr hf
  · have hf : Forbid A' C α w b2 := ⟨hwC, ((w, b2), l), hcl, Or.inr ⟨hlC, hact, rfl⟩⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    cases b2
    · exact Or.inl hf
    · exact Or.inr hf

private lemma main_theorem_aux (p q : ℕ) (hp : 0 < p) (hpq : p ≤ q) (n : ℕ) (A : F n) :
    let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
    let H := 2 ^ c * (Nat.clog 2 q + c + 1)
    let K := c + 2 * c * H
    (p * 2 ^ n ≤ q * massAux A →
      ∃ (S : Finset (Fin n)) (pins : Finset (Lit n)) (B : F n),
        S.card ≤ K ∧ (∀ l ∈ pins, l.1 ∈ S) ∧
        (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ p * 2 ^ n ≤ q * massAux B ∧
        ∀ z : W n, decide (satAux B z) = true ↔
          decide (satAux A z) = true ∧ ∀ l ∈ pins, z l.1 = l.2) ∧
    (q * massAux A < p * 2 ^ n →
      q * massAux A * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1)) := by
  intro c H K
  by_cases hlow : 2 * q * massAux A < p * 2 ^ n
  · constructor
    · intro hge
      have h2 : q * massAux A ≤ 2 * q * massAux A := by
        calc
          q * massAux A = 1 * (q * massAux A) := (one_mul _).symm
          _ ≤ 2 * (q * massAux A) := Nat.mul_le_mul_right _ (by decide)
          _ = 2 * q * massAux A := by ring
      omega
    · intro _
      have h1 : q * massAux A * 2 ^ (H + 1) = (2 * q * massAux A) * 2 ^ H := by
        rw [pow_succ]; ring
      have h2 : p * 2 ^ n * 2 ^ (H + 1) = (p * 2 ^ n) * 2 ^ H + (p * 2 ^ n) * 2 ^ H := by
        rw [pow_succ]; ring
      rw [h1, h2]
      have h3 : (2 * q * massAux A) * 2 ^ H ≤ (p * 2 ^ n) * 2 ^ H :=
        Nat.mul_le_mul_right _ (le_of_lt hlow)
      have h4 : 2 ^ n ≤ (p * 2 ^ n) * 2 ^ H := by
        have hpos : 1 ≤ p * 2 ^ H := Nat.mul_pos hp (pow_pos (by decide) H)
        calc
          2 ^ n = 2 ^ n * 1 := (mul_one _).symm
          _ ≤ 2 ^ n * (p * 2 ^ H) := Nat.mul_le_mul_left _ hpos
          _ = (p * 2 ^ n) * 2 ^ H := by ring
      omega
  · push Not at hlow
    let m := Nat.clog 2 ((q + p - 1) / p)
    have hq_le : q ≤ p * 2 ^ m := by
      have hdiv : q ≤ p * ((q + p - 1) / p) := by
        have hmod : (q + p - 1) % p < p := Nat.mod_lt _ hp
        have hdm := Nat.div_add_mod (q + p - 1) p
        omega
      have hclog : (q + p - 1) / p ≤ 2 ^ m := Nat.le_pow_clog (by decide : 1 < 2) _
      exact le_trans hdiv (Nat.mul_le_mul_left p hclog)
    have hdens : 2 ^ n ≤ 2 ^ (m + 1) * massAux A := by
      have h1 : p * 2 ^ n ≤ p * (2 ^ (m + 1) * massAux A) := by
        calc
          p * 2 ^ n ≤ 2 * q * massAux A := hlow
          _ ≤ 2 * (p * 2 ^ m) * massAux A :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hq_le)
          _ = p * (2 ^ (m + 1) * massAux A) := by rw [pow_succ]; ring
      exact Nat.le_of_mul_le_mul_left h1 hp
    rcases exists_small_cover A hdens with ⟨C, hC_card, hcover⟩
    have hC_le_c : C.card ≤ c := hC_card
    let A' := stripTaut A
    let Act := (Finset.univ : Finset ({x : Fin n // x ∈ C} → Bool)).filter
      (fun α => (fiber A' C α).Nonempty)
    let sortedAct := sortBy (expOf A' C) Act.toList
    have hperm : sortedAct.Perm Act.toList := sortBy_perm (expOf A' C) Act.toList
    have hnodup : sortedAct.Nodup := hperm.nodup_iff.2 Act.nodup_toList
    have hlen_eq : sortedAct.length = Act.card := by
      rw [hperm.length_eq, Finset.length_toList]
    have hlen_le : sortedAct.length ≤ 2 ^ c := by
      rw [hlen_eq]
      calc
        Act.card ≤ Fintype.card ({x : Fin n // x ∈ C} → Bool) := Finset.card_le_univ Act
        _ = 2 ^ C.card := by rw [Fintype.card_pi]; simp
        _ ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hC_le_c
    let es : List ℕ := sortedAct.map (expOf A' C)
    have hes_sorted : es.Pairwise (· ≤ ·) := by
      have hp' := sortBy_pairwise (expOf A' C) Act.toList
      exact List.pairwise_map.2 hp'
    have hes_len : es.length ≤ 2 ^ c := by
      simpa [es] using hlen_le
    have hes_le_n : ∀ e ∈ es, e ≤ n := by
      intro e he
      rcases List.mem_map.1 he with ⟨α, hα, rfl⟩
      have hα_act : α ∈ Act := Finset.mem_toList.1 (hperm.mem_iff.1 hα)
      exact (fiber_card_eq A' C hcover α (Finset.mem_filter.1 hα_act).2).1
    have hmass_eq : massAux A = sumE n es := by
      rw [← massAux_stripTaut A, massAux_eq_sum_fibers A' C]
      have hsum_act :
          ∑ α ∈ Act, (fiber A' C α).card = ∑ α ∈ Act, 2 ^ (n - expOf A' C α) := by
        refine Finset.sum_congr rfl fun α hα => ?_
        exact (fiber_card_eq A' C hcover α (Finset.mem_filter.1 hα).2).2
      rw [hsum_act]
      have hlist :
          (sortedAct.map (fun α => 2 ^ (n - expOf A' C α))).sum =
            ∑ α ∈ Act, 2 ^ (n - expOf A' C α) := by
        rw [(hperm.map _).sum_eq, ← List.sum_toFinset _ Act.nodup_toList, Finset.toList_toFinset]
      have hsumE : sumE n es = (sortedAct.map (fun α => 2 ^ (n - expOf A' C α))).sum := by
        simp [sumE, es, List.map_map, Function.comp_def]
      rw [hsumE, hlist]
    have hgap := dyadic_gap_or_prefix (q := q) (c := c) hp es hes_sorted hes_len hes_le_n
    dsimp only at hgap
    constructor
    · intro hge
      rw [hmass_eq] at hge
      rcases hgap.1 hge with ⟨k, hk_le, hk_ge, hk_H⟩
      have hk_le_act : k ≤ sortedAct.length := by simpa [es] using hk_le
      let prefList := sortedAct.take k
      have hpref_nodup : prefList.Nodup := hnodup.sublist (List.take_sublist k sortedAct)
      let Good : Finset ({x : Fin n // x ∈ C} → Bool) := prefList.toFinset
      have hGood_sub : Good ⊆ Act := by
        intro α hα
        have hmem : α ∈ sortedAct :=
          (List.take_sublist k sortedAct).subset (List.mem_toFinset.1 hα)
        exact Finset.mem_toList.1 (hperm.mem_iff.1 hmem)
      have hGood_exp : ∀ α ∈ Good, expOf A' C α ≤ H := by
        intro α hα
        have hmem : α ∈ prefList := List.mem_toFinset.1 hα
        have he_mem : expOf A' C α ∈ es.take k := by
          rw [show es.take k = prefList.map (expOf A' C) by simp [es, prefList, List.map_take]]
          exact List.mem_map_of_mem hmem
        exact hk_H _ he_mem
      have hGood_sum : sumE n (es.take k) = ∑ α ∈ Good, (fiber A' C α).card := by
        have htake_map : es.take k = prefList.map (expOf A' C) := by
          simp [es, prefList, List.map_take]
        rw [htake_map]
        have h1 : sumE n (prefList.map (expOf A' C)) =
            (prefList.map (fun α => 2 ^ (n - expOf A' C α))).sum := by
          simp [sumE, List.map_map, Function.comp_def]
        rw [h1, ← List.sum_toFinset _ hpref_nodup]
        refine Finset.sum_congr rfl fun α hα => ?_
        have hα_act : α ∈ Act := hGood_sub hα
        exact (fiber_card_eq A' C hcover α (Finset.mem_filter.1 hα_act).2).2.symm
      let coverLits : Finset (Lit n) := C ×ˢ (Finset.univ : Finset Bool)
      let Heavy : Finset (Lit n) := coverLits.filter (fun l => H < (outNbr A' C l).card)
      let Light : Finset (Lit n) := coverLits.filter (fun l => (outNbr A' C l).card ≤ H)
      let pins : Finset (Lit n) := Heavy.image (fun l => (l.1, !l.2))
      let S : Finset (Fin n) := C ∪ Light.biUnion (outNbr A' C)
      let B_pins : F n := pins.image (fun l => ((l.1, !l.2), (l.1, !l.2)))
      let B_light : F n := A'.filter (fun cl => cl.1 ∉ Heavy ∧ cl.2 ∉ Heavy)
      let B : F n := B_pins ∪ B_light
      have hLight_card : Light.card ≤ 2 * C.card := by
        calc
          Light.card ≤ coverLits.card := Finset.card_filter_le _ _
          _ = C.card * 2 := by rw [Finset.card_product]; simp
          _ = 2 * C.card := by ring
      have hS_card : S.card ≤ K := by
        have hbu : (Light.biUnion (outNbr A' C)).card ≤ Light.card * H := by
          calc
            (Light.biUnion (outNbr A' C)).card
                ≤ ∑ l ∈ Light, (outNbr A' C l).card := Finset.card_biUnion_le
            _ ≤ ∑ _l ∈ Light, H := Finset.sum_le_sum fun l hl => (Finset.mem_filter.1 hl).2
            _ = Light.card * H := by simp
        have h2c : Light.card * H ≤ 2 * c * H :=
          Nat.mul_le_mul_right H (le_trans hLight_card (Nat.mul_le_mul_left 2 hC_le_c))
        have hu := Finset.card_union_le C (Light.biUnion (outNbr A' C))
        show (C ∪ Light.biUnion (outNbr A' C)).card ≤ c + 2 * c * H
        omega
      have hpins_S : ∀ l ∈ pins, l.1 ∈ S := by
        intro l hl
        rcases Finset.mem_image.1 hl with ⟨h, hh, rfl⟩
        have hhC : h.1 ∈ C := (Finset.mem_product.1 (Finset.mem_filter.1 hh).1).1
        exact Finset.mem_union_left _ hhC
      have hB_S : ∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S := by
        intro cl hcl
        rcases Finset.mem_union.1 hcl with hp_mem | hl_mem
        · rcases Finset.mem_image.1 hp_mem with ⟨l, hl, rfl⟩
          exact ⟨hpins_S l hl, hpins_S l hl⟩
        · rcases Finset.mem_filter.1 hl_mem with ⟨hclA', h1nH, h2nH⟩
          rcases hcover cl hclA' with h1C | h2C
          · refine ⟨Finset.mem_union_left _ h1C, ?_⟩
            by_cases h2C' : cl.2.1 ∈ C
            · exact Finset.mem_union_left _ h2C'
            · have h1L : cl.1 ∈ Light := by
                refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1C, Finset.mem_univ _⟩, ?_⟩
                by_contra hgt
                push Not at hgt
                exact h1nH (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1C, Finset.mem_univ _⟩, hgt⟩)
              have h2nbr : cl.2.1 ∈ outNbr A' C cl.1 :=
                Finset.mem_filter.2 ⟨Finset.mem_univ _, h2C', cl.2.2, Or.inl hclA'⟩
              exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨cl.1, h1L, h2nbr⟩)
          · refine ⟨?_, Finset.mem_union_left _ h2C⟩
            by_cases h1C' : cl.1.1 ∈ C
            · exact Finset.mem_union_left _ h1C'
            · have h2L : cl.2 ∈ Light := by
                refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h2C, Finset.mem_univ _⟩, ?_⟩
                by_contra hgt
                push Not at hgt
                exact h2nH (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h2C, Finset.mem_univ _⟩, hgt⟩)
              have h1nbr : cl.1.1 ∈ outNbr A' C cl.2 :=
                Finset.mem_filter.2 ⟨Finset.mem_univ _, h1C', cl.1.2, Or.inr hclA'⟩
              exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨cl.2, h2L, h1nbr⟩)
      have hsat_iff : ∀ z : W n, decide (satAux B z) = true ↔
          decide (satAux A z) = true ∧ ∀ l ∈ pins, z l.1 = l.2 := by
        intro z
        simp only [decide_eq_true_eq]
        rw [satAux_stripTaut A z]
        have hpins_eq : satAux B_pins z ↔ ∀ l ∈ pins, z l.1 = l.2 := by
          constructor
          · intro h l hl
            have hor := h ((l.1, !l.2), (l.1, !l.2)) (Finset.mem_image.2 ⟨l, hl, rfl⟩)
            cases hz : z l.1 <;> cases hl2 : l.2 <;> simp_all
          · intro h cl hcl
            rcases Finset.mem_image.1 hcl with ⟨l, hl, rfl⟩
            have heq := h l hl
            cases hz : z l.1 <;> cases hl2 : l.2 <;> simp_all
        have hheavy_inactive : (∀ l ∈ pins, z l.1 = l.2) → ∀ h ∈ Heavy, z h.1 ≠ h.2 := by
          intro hpins h hh
          have heq := hpins (h.1, !h.2) (Finset.mem_image.2 ⟨h, hh, rfl⟩)
          cases hz : z h.1 <;> cases hh2 : h.2 <;> simp_all
        constructor
        · intro hB
          have hBp : satAux B_pins z := fun cl hcl => hB cl (Finset.mem_union_left _ hcl)
          have hBl : satAux B_light z := fun cl hcl => hB cl (Finset.mem_union_right _ hcl)
          have hpins_z := hpins_eq.1 hBp
          refine ⟨?_, hpins_z⟩
          intro cl hclA'
          by_cases h1 : cl.1 ∈ Heavy
          · exact Or.inl (hheavy_inactive hpins_z cl.1 h1)
          · by_cases h2 : cl.2 ∈ Heavy
            · exact Or.inr (hheavy_inactive hpins_z cl.2 h2)
            · exact hBl cl (Finset.mem_filter.2 ⟨hclA', h1, h2⟩)
        · rintro ⟨hA', hpins_z⟩ cl hclB
          rcases Finset.mem_union.1 hclB with hp_mem | hl_mem
          · exact hpins_eq.2 hpins_z cl hp_mem
          · exact hA' cl (Finset.mem_filter.1 hl_mem).1
      have hmass_B : ∑ α ∈ Good, (fiber A' C α).card ≤ massAux B := by
        let GoodWords := Good.biUnion (fiber A' C)
        have hdisj_G : (Good : Set ({x : Fin n // x ∈ C} → Bool)).PairwiseDisjoint (fiber A' C) := by
          intro α1 _ α2 _ hne
          refine Finset.disjoint_left.2 fun z h1 h2 => hne ?_
          funext v
          rw [← (Finset.mem_filter.1 h1).2.2 v, (Finset.mem_filter.1 h2).2.2 v]
        have hGW_card : GoodWords.card = ∑ α ∈ Good, (fiber A' C α).card :=
          Finset.card_biUnion hdisj_G
        rw [← hGW_card]
        refine Finset.card_le_card fun z hz => ?_
        rcases Finset.mem_biUnion.1 hz with ⟨α, hαG, hzF⟩
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hsat_iff z).2 ⟨?_, ?_⟩⟩
        · rw [decide_eq_true_eq, satAux_stripTaut]
          exact (Finset.mem_filter.1 hzF).2.1
        · intro l hl
          rcases Finset.mem_image.1 hl with ⟨h, hh, rfl⟩
          have hhC : h.1 ∈ C := (Finset.mem_product.1 (Finset.mem_filter.1 hh).1).1
          have hh_gt : H < (outNbr A' C h).card := (Finset.mem_filter.1 hh).2
          have hne_α : α ⟨h.1, hhC⟩ ≠ h.2 := by
            intro hact
            have hsub := outNbr_subset_forcedVars A' C α hhC hact
            have hle1 : (outNbr A' C h).card ≤ (forcedVars A' C α).card := Finset.card_le_card hsub
            have hle2 : (forcedVars A' C α).card ≤ expOf A' C α := Nat.le_add_left _ _
            have hle3 : expOf A' C α ≤ H := hGood_exp α hαG
            omega
          have hz_eq : z h.1 = α ⟨h.1, hhC⟩ := (Finset.mem_filter.1 hzF).2.2 ⟨h.1, hhC⟩
          rw [hz_eq]
          cases hαv : α ⟨h.1, hhC⟩ <;> cases hh2 : h.2 <;> simp_all
      have hB_dens : p * 2 ^ n ≤ q * massAux B := by
        rw [hGood_sum] at hk_ge
        exact le_trans hk_ge (Nat.mul_le_mul_left q hmass_B)
      exact ⟨S, pins, B, hS_card, hpins_S, hB_S, hB_dens, hsat_iff⟩
    · intro hlt
      rw [hmass_eq] at hlt ⊢
      exact hgap.2 hlt

end PEqualNP.Outside.L_lib_669_aux

theorem PEqualNP.Outside.L_lib_669 : (
let W := fun width : ℕ => Fin width → Bool
let Lit := fun width : ℕ => Fin width × Bool
let F := fun width : ℕ => Finset (Lit width × Lit width)
let sat := fun (len : ℕ) (A : F len) (word : W len) => decide (∀ c ∈ A,
  word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2)
let mass := fun (len : ℕ) (A : F len) =>
  (Finset.univ.filter (fun x : W len => sat len A x = true)).card
∀ p q : ℕ, 0 < p → p ≤ q →
  let c := 6 * (1 + Nat.clog 2 ((q + p - 1) / p))
  let H := 2 ^ c * (Nat.clog 2 q + c + 1)
  let K := c + 2 * c * H
  ∀ (n : ℕ) (A : F n),
    (p * 2 ^ n ≤ q * mass n A →
      ∃ (S : Finset (Fin n)) (pins : Finset (Lit n)) (B : F n),
        S.card ≤ K ∧ (∀ l ∈ pins, l.1 ∈ S) ∧
        (∀ cl ∈ B, cl.1.1 ∈ S ∧ cl.2.1 ∈ S) ∧ p * 2 ^ n ≤ q * mass n B ∧
        ∀ z : W n, sat n B z = true ↔ sat n A z = true ∧ ∀ l ∈ pins, z l.1 = l.2) ∧
    (q * mass n A < p * 2 ^ n →
      q * mass n A * 2 ^ (H + 1) + 2 ^ n ≤ p * 2 ^ n * 2 ^ (H + 1))
) := by
  intro W Lit F sat mass p q hp hpq c H K n A
  exact PEqualNP.Outside.L_lib_669_aux.main_theorem_aux p q hp hpq n A
