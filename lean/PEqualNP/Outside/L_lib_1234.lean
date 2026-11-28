import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1234_aux

-- =========================================================================
-- Part 1: Auxiliary graph with exactly M independent sets on <= 2*(log2 M + 1) vertices
-- =========================================================================

private def isIndep {α : Type*} (G : α → Finset α) (I : Finset α) : Prop :=
  ∀ u ∈ I, ∀ v ∈ G u, v ∉ I

private instance instDecIsIndep {α : Type*} [DecidableEq α] (G : α → Finset α) (I : Finset α) :
    Decidable (isIndep G I) := by
  unfold isIndep; infer_instance

private lemma exists_indGraph_add_isolated {k : ℕ} {H : Fin k → Finset (Fin k)}
    (hloop : ∀ v, v ∉ H v) (hsym : ∀ u v, v ∈ H u ↔ u ∈ H v) :
    ∃ H' : Fin (k + 1) → Finset (Fin (k + 1)),
      (∀ v, v ∉ H' v) ∧ (∀ u v, v ∈ H' u ↔ u ∈ H' v) ∧
      ((Finset.univ : Finset (Finset (Fin (k + 1)))).filter (fun I => isIndep H' I)).card =
        2 * ((Finset.univ : Finset (Finset (Fin k))).filter (fun I => isIndep H I)).card := by
  classical
  let emb : Fin k → Fin (k + 1) := Fin.castSucc
  let H' : Fin (k + 1) → Finset (Fin (k + 1)) := fun u =>
    if h : u.val < k then (H ⟨u.val, h⟩).image emb else ∅
  refine ⟨H', ?_, ?_, ?_⟩
  · intro u hu
    dsimp only [H'] at hu
    split_ifs at hu with h
    · rcases Finset.mem_image.mp hu with ⟨v, hv, hvu⟩
      have hvEq : v = ⟨u.val, h⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val hvu)
      subst hvEq
      exact hloop ⟨u.val, h⟩ hv
    · exact Finset.notMem_empty u hu
  · intro u v
    dsimp only [H']
    split_ifs with hu hv hv
    · simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, hwv⟩
        have hwEq : w = ⟨v.val, hv⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val hwv)
        subst hwEq
        exact ⟨⟨u.val, hu⟩, (hsym _ _).mp hw, Fin.ext rfl⟩
      · rintro ⟨w, hw, hwu⟩
        have hwEq : w = ⟨u.val, hu⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val hwu)
        subst hwEq
        exact ⟨⟨v.val, hv⟩, (hsym _ _).mp hw, Fin.ext rfl⟩
    · simp only [Finset.mem_image, Finset.notMem_empty, iff_false, not_exists, not_and]
      intro w _ hwv
      have : w.val = v.val := congrArg Fin.val hwv
      omega
    · simp only [Finset.notMem_empty, Finset.mem_image, false_iff, not_exists, not_and]
      intro w _ hwu
      have : w.val = u.val := congrArg Fin.val hwu
      omega
    · simp
  · let S := (Finset.univ : Finset (Finset (Fin (k + 1)))).filter (fun I => isIndep H' I)
    let T := (Finset.univ : Finset (Finset (Fin k))).filter (fun I => isIndep H I)
    change S.card = 2 * T.card
    let lastV : Fin (k + 1) := Fin.last k
    have hbij : S.card = (T ×ˢ (Finset.univ : Finset Bool)).card := by
      let toPair : Finset (Fin (k + 1)) → Finset (Fin k) × Bool := fun I =>
        (Finset.univ.filter (fun u : Fin k => emb u ∈ I), decide (lastV ∈ I))
      let fromPair : Finset (Fin k) × Bool → Finset (Fin (k + 1)) := fun p =>
        if p.2 then insert lastV (p.1.image emb) else p.1.image emb
      refine Finset.card_bij' (fun I _ => toPair I) (fun p _ => fromPair p) ?_ ?_ ?_ ?_
      · intro I hI
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hI
        simp only [toPair, Finset.mem_product, T, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        intro u hu v hv hvI
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hvI
        have hmem : emb v ∈ H' (emb u) := by
          simp only [H', emb, Fin.val_castSucc, u.isLt, ↓reduceDIte, Finset.mem_image]
          exact ⟨v, hv, rfl⟩
        exact hI (emb u) hu (emb v) hmem hvI
      · intro p hp
        simp only [Finset.mem_product, T, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        intro u hu v hv hvI
        have hlast_not : ∀ w : Fin (k + 1), w ≠ lastV ↔ w.val < k := fun w => by
          constructor
          · intro hne; have := w.isLt; have : w.val ≠ k := fun h => hne (Fin.ext h); omega
          · intro hlt hEq; have : w.val = k := congrArg Fin.val hEq; omega
        have hmemF : ∀ w : Fin (k + 1), w ∈ fromPair p ↔
            (p.2 = true ∧ w = lastV) ∨ ∃ a ∈ p.1, emb a = w := by
          intro w; dsimp only [fromPair]
          cases p.2 <;> simp [Finset.mem_insert, Finset.mem_image]
        rcases (hmemF u).mp hu with ⟨_, rfl⟩ | ⟨a, ha, rfl⟩
        · simp [H', lastV] at hv
        · simp only [H', emb, Fin.val_castSucc, a.isLt, ↓reduceDIte, Finset.mem_image] at hv
          rcases hv with ⟨b, hb, rfl⟩
          rcases (hmemF (emb b)).mp hvI with ⟨_, hEq⟩ | ⟨c, hc, hcEq⟩
          · have : b.val = k := congrArg Fin.val hEq; omega
          · have hcb : c = b := Fin.castSucc_inj.mp hcEq
            subst hcb
            exact hp a ha c hb hc
      · intro I _
        ext u
        dsimp only [fromPair, toPair]
        by_cases hlt : u.val < k
        · have hne : u ≠ lastV := fun h => by have : u.val = k := congrArg Fin.val h; omega
          cases hl : decide (lastV ∈ I) <;> simp only [Bool.false_eq_true, ↓reduceIte,
            Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            hne, false_or]
          · constructor
            · rintro ⟨a, ha, rfl⟩; exact ha
            · intro hu; exact ⟨⟨u.val, hlt⟩, hu, Fin.ext rfl⟩
          · constructor
            · rintro ⟨a, ha, rfl⟩; exact ha
            · intro hu; exact ⟨⟨u.val, hlt⟩, hu, Fin.ext rfl⟩
        · have huEq : u = lastV := Fin.ext (by have := u.isLt; simp only [lastV, Fin.val_last]; omega)
          subst huEq
          by_cases hlast : lastV ∈ I
          · simp [hlast]
          · simp only [hlast, decide_false, Bool.false_eq_true, ↓reduceIte, Finset.mem_image,
              Finset.mem_filter, Finset.mem_univ, true_and, iff_false, not_exists, not_and]
            intro a _ hEq
            have : a.val = k := congrArg Fin.val hEq; omega
      · intro p _
        rcases p with ⟨I0, b⟩
        dsimp only [toPair, fromPair]
        apply Prod.ext
        · ext a
          have hne : emb a ≠ lastV := fun h => by have : a.val = k := congrArg Fin.val h; omega
          cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_insert, Finset.mem_image, hne, false_or]
          · constructor
            · rintro ⟨c, hc, hca⟩; exact (Fin.castSucc_inj.mp hca) ▸ hc
            · intro ha; exact ⟨a, ha, rfl⟩
          · constructor
            · rintro ⟨c, hc, hca⟩; exact (Fin.castSucc_inj.mp hca) ▸ hc
            · intro ha; exact ⟨a, ha, rfl⟩
        · cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, Finset.mem_image,
              not_exists, not_and]
            intro a _ hEq; have : a.val = k := congrArg Fin.val hEq; omega
          · simp
    rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]

private lemma exists_indGraph_add_universal {k : ℕ} {H : Fin k → Finset (Fin k)}
    (hloop : ∀ v, v ∉ H v) (hsym : ∀ u v, v ∈ H u ↔ u ∈ H v) :
    ∃ H' : Fin (k + 1) → Finset (Fin (k + 1)),
      (∀ v, v ∉ H' v) ∧ (∀ u v, v ∈ H' u ↔ u ∈ H' v) ∧
      ((Finset.univ : Finset (Finset (Fin (k + 1)))).filter (fun I => isIndep H' I)).card =
        ((Finset.univ : Finset (Finset (Fin k))).filter (fun I => isIndep H I)).card + 1 := by
  classical
  let emb : Fin k → Fin (k + 1) := Fin.castSucc
  let lastV : Fin (k + 1) := Fin.last k
  let H' : Fin (k + 1) → Finset (Fin (k + 1)) := fun u =>
    if h : u.val < k then insert lastV ((H ⟨u.val, h⟩).image emb)
    else Finset.univ.image emb
  refine ⟨H', ?_, ?_, ?_⟩
  · intro u hu
    dsimp only [H'] at hu
    split_ifs at hu with h
    · rcases Finset.mem_insert.mp hu with hEq | hImg
      · have : u.val = k := congrArg Fin.val hEq; omega
      · rcases Finset.mem_image.mp hImg with ⟨v, hv, hvu⟩
        have hvEq : v = ⟨u.val, h⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val hvu)
        subst hvEq; exact hloop ⟨u.val, h⟩ hv
    · rcases Finset.mem_image.mp hu with ⟨v, _, hvu⟩
      have : v.val = u.val := congrArg Fin.val hvu; omega
  · intro u v
    dsimp only [H']
    split_ifs with hu hv hv
    · simp only [Finset.mem_insert, Finset.mem_image]
      have hneV : v ≠ lastV := fun h => by have : v.val = k := congrArg Fin.val h; omega
      have hneU : u ≠ lastV := fun h => by have : u.val = k := congrArg Fin.val h; omega
      simp only [hneV, hneU, false_or]
      constructor
      · rintro ⟨w, hw, hwv⟩
        have hwEq : w = ⟨v.val, hv⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val hwv)
        subst hwEq
        exact ⟨⟨u.val, hu⟩, (hsym _ _).mp hw, Fin.ext rfl⟩
      · rintro ⟨w, hw, hwu⟩
        have hwEq : w = ⟨u.val, hu⟩ := Fin.ext (by simpa [emb] using congrArg Fin.val hwu)
        subst hwEq
        exact ⟨⟨v.val, hv⟩, (hsym _ _).mp hw, Fin.ext rfl⟩
    · have hvEq : v = lastV := Fin.ext (by have := v.isLt; simp only [lastV, Fin.val_last]; omega)
      subst hvEq
      simp only [Finset.mem_insert, true_or, Finset.mem_image, Finset.mem_univ, true_and, true_iff]
      exact ⟨⟨u.val, hu⟩, Fin.ext rfl⟩
    · have huEq : u = lastV := Fin.ext (by have := u.isLt; simp only [lastV, Fin.val_last]; omega)
      subst huEq
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, true_or, iff_true]
      exact ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
    · have huEq : u = lastV := Fin.ext (by have := u.isLt; simp only [lastV, Fin.val_last]; omega)
      have hvEq : v = lastV := Fin.ext (by have := v.isLt; simp only [lastV, Fin.val_last]; omega)
      subst huEq; subst hvEq
      rfl
  · let S := (Finset.univ : Finset (Finset (Fin (k + 1)))).filter (fun I => isIndep H' I)
    let T := (Finset.univ : Finset (Finset (Fin k))).filter (fun I => isIndep H I)
    change S.card = T.card + 1
    have hlast_in : {lastV} ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro u hu v hv hvI
      have huEq : u = lastV := Finset.mem_singleton.mp hu
      have hvEq : v = lastV := Finset.mem_singleton.mp hvI
      subst huEq; subst hvEq
      simp only [H', lastV, Fin.val_last, lt_self_iff_false, ↓reduceDIte, Finset.mem_image,
        Finset.mem_univ, true_and] at hv
      rcases hv with ⟨a, ha⟩; have := congrArg Fin.val ha; simp [emb] at this; omega
    have hsplit : S = insert {lastV} (T.image (fun I => I.image emb)) := by
      ext I
      simp only [Finset.mem_insert, Finset.mem_image]
      constructor
      · intro hI
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hI
        by_cases hlast : lastV ∈ I
        · left
          ext u
          simp only [Finset.mem_singleton]
          constructor
          · intro hu
            by_contra hne
            have hlt : u.val < k := by have := u.isLt; have : u.val ≠ k := fun h => hne (Fin.ext h); omega
            have hmem : u ∈ H' lastV := by
              simp only [H', lastV, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
                Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨⟨u.val, hlt⟩, Fin.ext rfl⟩
            exact hI lastV hlast u hmem hu
          · rintro rfl; exact hlast
        · right
          let I0 := Finset.univ.filter (fun a : Fin k => emb a ∈ I)
          refine ⟨I0, ?_, ?_⟩
          · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
            intro a ha b hb hbI
            simp only [I0, Finset.mem_filter, Finset.mem_univ, true_and] at ha hbI
            have hmem : emb b ∈ H' (emb a) := by
              simp only [H', emb, Fin.val_castSucc, a.isLt, ↓reduceDIte, Finset.mem_insert,
                Finset.mem_image]
              exact Or.inr ⟨b, hb, rfl⟩
            exact hI (emb a) ha (emb b) hmem hbI
          · ext u
            simp only [Finset.mem_image, I0, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨a, ha, rfl⟩; exact ha
            · intro hu
              have hne : u ≠ lastV := fun h => hlast (h ▸ hu)
              have hlt : u.val < k := by have := u.isLt; have : u.val ≠ k := fun h => hne (Fin.ext h); omega
              exact ⟨⟨u.val, hlt⟩, hu, Fin.ext rfl⟩
      · rintro (rfl | ⟨I0, hI0, rfl⟩)
        · exact hlast_in
        · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hI0
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          intro u hu v hv hvI
          rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
          rcases Finset.mem_image.mp hvI with ⟨b, hb, rfl⟩
          simp only [H', emb, Fin.val_castSucc, a.isLt, ↓reduceDIte, Finset.mem_insert,
            Finset.mem_image] at hv
          rcases hv with hEq | ⟨c, hc, hcEq⟩
          · have : b.val = k := congrArg Fin.val hEq; omega
          · have hcb : c = b := Fin.castSucc_inj.mp hcEq
            subst hcb; exact hI0 a ha c hc hb
    have hnot : {lastV} ∉ T.image (fun I => I.image emb) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro I0 _ hEq
      have hm : lastV ∈ I0.image emb := hEq.symm ▸ Finset.mem_singleton_self lastV
      rcases Finset.mem_image.mp hm with ⟨a, _, ha⟩
      have : a.val = k := congrArg Fin.val ha; omega
    have hinj : Function.Injective (fun I : Finset (Fin k) => I.image emb) := by
      intro I1 I2 hEq
      ext a
      have := Finset.ext_iff.mp hEq (emb a)
      simp only [Finset.mem_image] at this
      constructor
      · intro ha; rcases this.mp ⟨a, ha, rfl⟩ with ⟨b, hb, hba⟩
        exact (Fin.castSucc_inj.mp hba) ▸ hb
      · intro ha; rcases this.mpr ⟨a, ha, rfl⟩ with ⟨b, hb, hba⟩
        exact (Fin.castSucc_inj.mp hba) ▸ hb
    rw [hsplit, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective T hinj]

private lemma exists_indGraph_card : ∀ M : ℕ, 1 ≤ M →
    ∃ (k : ℕ) (H : Fin k → Finset (Fin k)),
      k ≤ 2 * (Nat.log2 M + 1) ∧
      (∀ v, v ∉ H v) ∧ (∀ u v, v ∈ H u ↔ u ∈ H v) ∧
      ((Finset.univ : Finset (Finset (Fin k))).filter (fun I => isIndep H I)).card = M := by
  classical
  intro M
  induction M using Nat.strong_induction_on with
  | ind M ih =>
    intro hM
    by_cases hM1 : M = 1
    · subst hM1
      refine ⟨0, Fin.elim0, by omega, fun v => v.elim0, fun u => u.elim0, ?_⟩
      have hEq : ((Finset.univ : Finset (Finset (Fin 0))).filter (fun I => isIndep Fin.elim0 I)) = {∅} := by
        ext I; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _; ext x; exact x.elim0
        · rintro rfl u hu; exact absurd hu (Finset.notMem_empty u)
      rw [hEq, Finset.card_singleton]
    · have hM2 : 2 ≤ M := by omega
      have hq_pos : 1 ≤ M / 2 := by omega
      have hq_lt : M / 2 < M := Nat.div_lt_self (by omega) (by omega)
      have hlog : Nat.log2 M = Nat.log2 (M / 2) + 1 := by
        rw [Nat.log2_def]; simp [hM2]
      rcases ih (M / 2) hq_lt hq_pos with ⟨k, H, hk, hloop, hsym, hcard⟩
      rcases exists_indGraph_add_isolated hloop hsym with ⟨H1, hloop1, hsym1, hcard1⟩
      by_cases hev : M % 2 = 0
      · refine ⟨k + 1, H1, by omega, hloop1, hsym1, ?_⟩
        rw [hcard1, hcard]; omega
      · rcases exists_indGraph_add_universal hloop1 hsym1 with ⟨H2, hloop2, hsym2, hcard2⟩
        refine ⟨k + 2, H2, by omega, hloop2, hsym2, ?_⟩
        rw [hcard2, hcard1, hcard]; omega

-- =========================================================================
-- Part 2: Binary bit-expansion lemma
-- =========================================================================

private lemma sum_testBit_two_pow : ∀ b : ℕ, ∀ a : ℕ, a < 2 ^ b →
    (∑ j : Fin b, if a.testBit j.val then 2 ^ j.val else 0) = a := by
  intro b
  induction b with
  | zero =>
    intro a ha; simp at ha ⊢; omega
  | succ b ih =>
    intro a ha
    rw [Fin.sum_univ_succ]
    have hdiv : a / 2 < 2 ^ b := by
      have : 2 ^ (b + 1) = 2 ^ b * 2 := pow_succ 2 b
      omega
    have hbit0 : (if a.testBit 0 = true then 1 else 0) = a % 2 := by
      rw [Nat.testBit_zero]
      have := Nat.mod_two_eq_zero_or_one a
      rcases this with h0 | h1
      · simp [h0]
      · simp [h1]
    have htail : (∑ i : Fin b, if a.testBit i.succ.val then 2 ^ i.succ.val else 0) =
        2 * ∑ i : Fin b, if (a / 2).testBit i.val then 2 ^ i.val else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hb : a.testBit (i.val + 1) = (a / 2).testBit i.val := by
        rw [Nat.testBit_succ]
      simp only [Fin.val_succ, hb, pow_succ]
      split_ifs <;> ring
    simp only [Fin.val_zero, pow_zero]
    rw [hbit0, htail, ih (a / 2) hdiv]
    omega

private lemma lt_two_pow_log2_succ (M : ℕ) (hM : 1 ≤ M) : M < 2 ^ (Nat.log2 M + 1) := by
  have := Nat.lt_pow_succ_log_self (by omega : 1 < 2) M
  simpa [Nat.log2_eq_log_two] using this

-- =========================================================================
-- Part 3: Vertex types, clauses, graph construction, and counting
-- =========================================================================

private inductive ClauseId (n t : ℕ)
  | pinPair (j : Fin n)
  | prefPair (s : Fin (t + 1))
  | prefZero
  | prefTop
  | slotSw (s : Fin t)
  deriving DecidableEq

private inductive BaseV (n t b : ℕ)
  | pin (j : Fin n)
  | pinBar (j : Fin n)
  | pref (s : Fin (t + 1))
  | prefBar (s : Fin (t + 1))
  | sw (s : Fin t)
  | wt (u : Fin b)
  deriving DecidableEq

private inductive Vtx (n t b kH : ℕ)
  | base (v : BaseV n t b)
  | gad (c : ClauseId n t) (v : Fin kH)
  deriving DecidableEq

private def clauseEquiv (n t : ℕ) :
    ClauseId n t ≃ (Fin n ⊕ Fin (t + 1) ⊕ Unit ⊕ Unit ⊕ Fin t) where
  toFun
    | .pinPair j => Sum.inl j
    | .prefPair s => Sum.inr (Sum.inl s)
    | .prefZero => Sum.inr (Sum.inr (Sum.inl ()))
    | .prefTop => Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
    | .slotSw s => Sum.inr (Sum.inr (Sum.inr (Sum.inr s)))
  invFun
    | Sum.inl j => .pinPair j
    | Sum.inr (Sum.inl s) => .prefPair s
    | Sum.inr (Sum.inr (Sum.inl ())) => .prefZero
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))) => .prefTop
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr s))) => .slotSw s
  left_inv c := by cases c <;> rfl
  right_inv x := by rcases x with _ | _ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | _ <;> rfl

private def baseEquiv (n t b : ℕ) :
    BaseV n t b ≃ (Fin n ⊕ Fin n ⊕ Fin (t + 1) ⊕ Fin (t + 1) ⊕ Fin t ⊕ Fin b) where
  toFun
    | .pin j => Sum.inl j
    | .pinBar j => Sum.inr (Sum.inl j)
    | .pref s => Sum.inr (Sum.inr (Sum.inl s))
    | .prefBar s => Sum.inr (Sum.inr (Sum.inr (Sum.inl s)))
    | .sw s => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl s))))
    | .wt u => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr u))))
  invFun
    | Sum.inl j => .pin j
    | Sum.inr (Sum.inl j) => .pinBar j
    | Sum.inr (Sum.inr (Sum.inl s)) => .pref s
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl s))) => .prefBar s
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl s)))) => .sw s
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr u)))) => .wt u
  left_inv v := by cases v <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ | _ | _ <;> rfl

private def vtxEquiv (n t b kH : ℕ) :
    Vtx n t b kH ≃ (BaseV n t b ⊕ (ClauseId n t × Fin kH)) where
  toFun
    | .base v => Sum.inl v
    | .gad c v => Sum.inr (c, v)
  invFun
    | Sum.inl v => .base v
    | Sum.inr (c, v) => .gad c v
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | ⟨_, _⟩ <;> rfl

private instance instFintypeClause (n t : ℕ) : Fintype (ClauseId n t) :=
  Fintype.ofEquiv _ (clauseEquiv n t).symm

private instance instFintypeBase (n t b : ℕ) : Fintype (BaseV n t b) :=
  Fintype.ofEquiv _ (baseEquiv n t b).symm

private instance instFintypeVtx (n t b kH : ℕ) : Fintype (Vtx n t b kH) :=
  Fintype.ofEquiv _ (vtxEquiv n t b kH).symm

private lemma card_clause (n t : ℕ) : Fintype.card (ClauseId n t) = n + 2 * t + 3 := by
  have h := Fintype.card_congr (clauseEquiv n t)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h
  omega

private lemma card_base (n t b : ℕ) : Fintype.card (BaseV n t b) = 2 * n + 3 * t + b + 2 := by
  have h := Fintype.card_congr (baseEquiv n t b)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

private lemma card_vtx (n t b kH : ℕ) :
    Fintype.card (Vtx n t b kH) = 2 * n + 3 * t + b + 2 + (n + 2 * t + 3) * kH := by
  have h := Fintype.card_congr (vtxEquiv n t b kH)
  rw [h, Fintype.card_sum, Fintype.card_prod, card_base, card_clause, Fintype.card_fin]

private def clauseBase {n t b : ℕ} : ClauseId n t → Finset (BaseV n t b)
  | .pinPair j => {.pin j, .pinBar j}
  | .prefPair s => {.pref s, .prefBar s}
  | .prefZero => {.prefBar ⟨0, Nat.zero_lt_succ t⟩}
  | .prefTop => {.pref ⟨t, Nat.lt_succ_self t⟩}
  | .slotSw s => {.pref ⟨s.val, by omega⟩, .prefBar ⟨s.val + 1, by omega⟩, .sw s}

private def slotEquiv (m b : ℕ) (hb : 0 < b) : Fin m × Fin b ≃ Fin (m * b) where
  toFun p := ⟨p.1.val * b + p.2.val, by
    have h1 : p.1.val + 1 ≤ m := p.1.isLt
    have h2 : (p.1.val + 1) * b ≤ m * b := Nat.mul_le_mul_right b h1
    have := p.2.isLt
    nlinarith⟩
  invFun s := (⟨s.val / b, Nat.div_lt_of_lt_mul (by have := s.isLt; nlinarith)⟩,
               ⟨s.val % b, Nat.mod_lt s.val hb⟩)
  left_inv p := by
    rcases p with ⟨i, j⟩
    apply Prod.ext
    · apply Fin.ext
      dsimp only
      rw [mul_comm i.val b, Nat.mul_add_div hb, Nat.div_eq_of_lt j.isLt, add_zero]
    · apply Fin.ext
      dsimp only
      rw [mul_comm i.val b, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  right_inv s := by
    apply Fin.ext
    dsimp only
    exact Nat.div_add_mod' s.val b

private def baseAdjDir {n m b : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool) :
    BaseV n (m * b) b → BaseV n (m * b) b → Bool
  | .pin j, .pinBar j' => j == j'
  | .pref s, .prefBar s' => (s == s') || (s.val + 1 == s'.val)
  | .sw s, .pref s' => s.val == s'.val
  | .sw s, .prefBar s' => s.val + 1 == s'.val
  | .sw s, .pin k =>
    let p := (slotEquiv m b hb).symm s
    pat p.1 k == some false
  | .sw s, .pinBar k =>
    let p := (slotEquiv m b hb).symm s
    pat p.1 k == some true
  | .sw s, .wt u =>
    let p := (slotEquiv m b hb).symm s
    decide (p.2.val ≤ u.val)
  | _, _ => false

private def baseAdj {n m b : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    (u v : BaseV n (m * b) b) : Bool :=
  baseAdjDir hb pat u v || baseAdjDir hb pat v u

private lemma baseAdj_irrefl {n m b : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    (u : BaseV n (m * b) b) : baseAdj hb pat u u = false := by
  cases u <;> simp [baseAdj, baseAdjDir]

private lemma baseAdj_symm {n m b : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    (u v : BaseV n (m * b) b) : baseAdj hb pat u v = baseAdj hb pat v u := by
  simp [baseAdj, Bool.or_comm]

private def fullAdj {n m b kH : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    (H : Fin kH → Finset (Fin kH)) (u v : Vtx n (m * b) b kH) : Bool :=
  match u, v with
  | .base x, .base y => baseAdj hb pat x y
  | .base x, .gad c _ => decide (x ∈ clauseBase c)
  | .gad c _, .base y => decide (y ∈ clauseBase c)
  | .gad c1 a, .gad c2 d => decide (c1 = c2 ∧ d ∈ H a)

private lemma fullAdj_irrefl {n m b kH : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    {H : Fin kH → Finset (Fin kH)} (hloop : ∀ a, a ∉ H a) (u : Vtx n (m * b) b kH) :
    fullAdj hb pat H u u = false := by
  cases u with
  | base x => exact baseAdj_irrefl hb pat x
  | gad c a => simp [fullAdj, hloop a]

private lemma fullAdj_symm {n m b kH : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    {H : Fin kH → Finset (Fin kH)} (hsym : ∀ a d, d ∈ H a ↔ a ∈ H d)
    (u v : Vtx n (m * b) b kH) :
    fullAdj hb pat H u v = fullAdj hb pat H v u := by
  cases u <;> cases v
  · exact baseAdj_symm hb pat _ _
  · rfl
  · rfl
  · simp only [fullAdj, eq_comm, hsym]

-- =========================================================================
-- Part 4: Counting independent sets modulo M
-- =========================================================================

private lemma card_fibers_prod {n m b kH M : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    {H : Fin kH → Finset (Fin kH)}
    (hHcard : ((Finset.univ : Finset (Finset (Fin kH))).filter (fun I => isIndep H I)).card = M)
    (f : Fin m → Fin M) (x : Fin n → Bool) :
    let t := m * b
    let G : Vtx n t b kH → Finset (Vtx n t b kH) := fun u =>
      Finset.univ.filter (fun v => fullAdj hb pat H u v = true)
    let liveB : BaseV n t b → Prop := fun v =>
      ∀ s : Fin t, v = .sw s → (f ((slotEquiv m b hb).symm s).1).val.testBit ((slotEquiv m b hb).symm s).2.val = true
    let liveV : Vtx n t b kH → Prop := fun v =>
      ∀ k : Fin m × Fin b, v = .base (.sw (slotEquiv m b hb k)) → (f k.1).val.testBit k.2.val = true
    ((Finset.univ : Finset (Finset (Vtx n t b kH))).filter (fun I =>
      (∀ v ∈ I, liveV v) ∧ (∀ j, Vtx.base (BaseV.pin j) ∈ I ↔ x j = true) ∧
      isIndep G I)).card =
    ∑ I0 ∈ (Finset.univ : Finset (Finset (BaseV n t b))).filter (fun I0 =>
      (∀ v ∈ I0, liveB v) ∧ (∀ j, BaseV.pin j ∈ I0 ↔ x j = true) ∧
      ∀ u ∈ I0, ∀ v ∈ I0, baseAdj hb pat u v = false),
      ∏ c : ClauseId n t, if (∃ u ∈ clauseBase c, u ∈ I0) then 1 else M := by
  classical
  intro t G liveB liveV
  let S := (Finset.univ : Finset (Finset (Vtx n t b kH))).filter (fun I =>
    (∀ v ∈ I, liveV v) ∧ (∀ j, Vtx.base (BaseV.pin j) ∈ I ↔ x j = true) ∧ isIndep G I)
  let B0 := (Finset.univ : Finset (Finset (BaseV n t b))).filter (fun I0 =>
    (∀ v ∈ I0, liveB v) ∧ (∀ j, BaseV.pin j ∈ I0 ↔ x j = true) ∧
    ∀ u ∈ I0, ∀ v ∈ I0, baseAdj hb pat u v = false)
  let proj : Finset (Vtx n t b kH) → Finset (BaseV n t b) := fun I =>
    Finset.univ.filter (fun v => Vtx.base v ∈ I)
  have hmaps : ∀ I ∈ S, proj I ∈ B0 := by
    intro I hI
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hI
    rcases hI with ⟨hlive, hpin, hind⟩
    simp only [B0, proj, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv s hvs
      subst hvs
      have h1 := hlive (.base (.sw s)) hv ((slotEquiv m b hb).symm s) (by simp)
      exact h1
    · intro j; exact hpin j
    · intro u hu v hv
      cases h : baseAdj hb pat u v
      · rfl
      · have hmem : Vtx.base v ∈ G (Vtx.base u) := by simp [G, fullAdj, h]
        exact absurd hv (hind (.base u) hu (.base v) hmem)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro I0 hI0
  simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and] at hI0
  rcases hI0 with ⟨hlive0, hpin0, hind0⟩
  let allowed (c : ClauseId n t) : Finset (Finset (Fin kH)) :=
    if ∃ u ∈ clauseBase c, u ∈ I0 then {∅}
    else (Finset.univ : Finset (Finset (Fin kH))).filter (fun J => isIndep H J)
  have hall_card : ∀ c : ClauseId n t, (allowed c).card = if (∃ u ∈ clauseBase c, u ∈ I0) then 1 else M := by
    intro c; dsimp only [allowed]
    split_ifs
    · exact Finset.card_singleton ∅
    · exact hHcard
  rw [← Finset.prod_congr rfl (fun c _ => hall_card c), ← Fintype.card_piFinset]
  let toPi : Finset (Vtx n t b kH) → (c : ClauseId n t) → Finset (Fin kH) := fun I c =>
    Finset.univ.filter (fun a => Vtx.gad c a ∈ I)
  let fromPi : ((c : ClauseId n t) → Finset (Fin kH)) → Finset (Vtx n t b kH) := fun g =>
    Finset.univ.filter (fun w => match w with | .base v => v ∈ I0 | .gad c a => a ∈ g c)
  refine Finset.card_bij' (fun I _ => toPi I) (fun g _ => fromPi g) ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Finset.mem_filter] at hI
    rcases hI with ⟨hIS, hproj⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hIS
    rcases hIS with ⟨_, _, hind⟩
    rw [Fintype.mem_piFinset]
    intro c
    dsimp only [allowed, toPi]
    split_ifs with hex
    · rw [Finset.mem_singleton]
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro haI
      rcases hex with ⟨u, huC, huI0⟩
      have huI : Vtx.base u ∈ I := by
        rw [← hproj] at huI0; exact (Finset.mem_filter.mp huI0).2
      have hmem : Vtx.gad c a ∈ G (Vtx.base u) := by simp [G, fullAdj, huC]
      exact hind (.base u) huI (.gad c a) hmem haI
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha d hd hdI
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hdI
      have hmem : Vtx.gad c d ∈ G (Vtx.gad c a) := by simp [G, fullAdj, hd]
      exact hind (.gad c a) ha (.gad c d) hmem hdI
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    simp only [Finset.mem_filter, S, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro w hw k hwk
      subst hwk
      simp only [fromPi, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have h1 := hlive0 (.sw (slotEquiv m b hb k)) hw (slotEquiv m b hb k) rfl
      simpa using h1
    · intro j; simp [fromPi, hpin0 j]
    · intro u hu v hv hvI
      simp only [fromPi, Finset.mem_filter, Finset.mem_univ, true_and] at hu hvI
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      cases u with
      | base x =>
        cases v with
        | base y =>
          dsimp only at hu hvI
          simp only [fullAdj] at hv
          rw [hind0 x hu y hvI] at hv; cases hv
        | gad c a =>
          dsimp only at hu hvI
          simp only [fullAdj, decide_eq_true_eq] at hv
          have hgc := hg c
          dsimp only [allowed] at hgc
          rw [if_pos ⟨x, hv, hu⟩, Finset.mem_singleton] at hgc
          rw [hgc] at hvI; exact Finset.notMem_empty a hvI
      | gad c a =>
        cases v with
        | base y =>
          dsimp only at hu hvI
          simp only [fullAdj, decide_eq_true_eq] at hv
          have hgc := hg c
          dsimp only [allowed] at hgc
          rw [if_pos ⟨y, hv, hvI⟩, Finset.mem_singleton] at hgc
          rw [hgc] at hu; exact Finset.notMem_empty a hu
        | gad c2 d =>
          dsimp only at hu hvI
          simp only [fullAdj, decide_eq_true_eq] at hv
          rcases hv with ⟨rfl, hd⟩
          have hgc := hg c
          dsimp only [allowed] at hgc
          split_ifs at hgc with hex
          · rw [Finset.mem_singleton] at hgc; rw [hgc] at hu; exact Finset.notMem_empty a hu
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hgc
            exact hgc a hu d hd hvI
    · ext v; simp [proj, fromPi]
  · intro I hI
    have hproj : proj I = I0 := (Finset.mem_filter.mp hI).2
    ext w
    simp only [fromPi, toPi, Finset.mem_filter, Finset.mem_univ, true_and]
    cases w with
    | base v =>
      rw [← hproj]; simp [proj]
    | gad c a =>
      simp
  · intro g _
    funext c; ext a
    simp [toPi, fromPi]

private lemma prod_clause_mod (M : ℕ) {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∏ c : α, if P c then 1 else M) % M = (if ∀ c : α, P c then 1 else 0) % M := by
  by_cases hall : ∀ c : α, P c
  · simp [hall]
  · simp only [hall, ↓reduceIte, Nat.zero_mod]
    push_neg at hall
    rcases hall with ⟨c0, hc0⟩
    apply Nat.mod_eq_zero_of_dvd
    have hdvd : (if P c0 then 1 else M) ∣ ∏ c : α, if P c then 1 else M :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ c0)
    simpa [hc0] using hdvd

private lemma sum_mod_congr {α : Type*} (s : Finset α) (f g : α → ℕ) (M : ℕ)
    (h : ∀ x ∈ s, f x % M = g x % M) :
    (∑ x ∈ s, f x) % M = (∑ x ∈ s, g x) % M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mod,
      h a (Finset.mem_insert_self a s), ih (fun x hx => h x (Finset.mem_insert_of_mem hx)),
      ← Nat.add_mod]

private lemma base_good_count {n m b M : ℕ} (hb : 0 < b) (hM : 2 ≤ M)
    (hMlt : M < 2 ^ b) (pat : Fin m → Fin n → Option Bool) (f : Fin m → Fin M) (x : Fin n → Bool) :
    let t := m * b
    let liveB : BaseV n t b → Prop := fun v =>
      ∀ s : Fin t, v = .sw s → (f ((slotEquiv m b hb).symm s).1).val.testBit ((slotEquiv m b hb).symm s).2.val = true
    ((Finset.univ : Finset (Finset (BaseV n t b))).filter (fun I0 =>
      ((∀ v ∈ I0, liveB v) ∧ (∀ j, BaseV.pin j ∈ I0 ↔ x j = true) ∧
        ∀ u ∈ I0, ∀ v ∈ I0, baseAdj hb pat u v = false) ∧
      ∀ c : ClauseId n t, ∃ u ∈ clauseBase c, u ∈ I0)).card =
    ((Finset.univ : Finset (Fin m)).filter
      (fun i => ∀ j, (pat i j).elim true (fun v => decide (v = x j)) = true)).sum
      (fun i => (f i).val) := by
  classical
  intro t liveB
  let Good := (Finset.univ : Finset (Finset (BaseV n t b))).filter (fun I0 =>
    ((∀ v ∈ I0, liveB v) ∧ (∀ j, BaseV.pin j ∈ I0 ↔ x j = true) ∧
      ∀ u ∈ I0, ∀ v ∈ I0, baseAdj hb pat u v = false) ∧
    ∀ c : ClauseId n t, ∃ u ∈ clauseBase c, u ∈ I0)
  let ActiveSlots := (Finset.univ : Finset (Fin m × Fin b)).filter (fun p =>
    (∀ j, (pat p.1 j).elim true (fun v => decide (v = x j)) = true) ∧
    (f p.1).val.testBit p.2.val = true)
  let mkBase (p : Fin m × Fin b) (W : Finset (Fin b)) : Finset (BaseV n t b) :=
    Finset.univ.filter (fun v => match v with
      | .pin j => x j = true
      | .pinBar j => x j = false
      | .pref s => (slotEquiv m b hb p).val < s.val
      | .prefBar s => s.val ≤ (slotEquiv m b hb p).val
      | .sw s => s = slotEquiv m b hb p
      | .wt u => u ∈ W)
  let Target := ActiveSlots.sigma (fun p =>
    (Finset.univ.filter (fun u : Fin b => u.val < p.2.val)).powerset)
  have hbij : Good.card = Target.card := by
    have hslot_unique : ∀ I0 ∈ Good, ∃! s : Fin t, BaseV.sw s ∈ I0 := by
      intro I0 hI0
      simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hI0
      rcases hI0 with ⟨⟨_, _, hind⟩, hcl⟩
      have hpref_bar : ∀ s : Fin (t + 1), BaseV.prefBar s ∈ I0 ↔ BaseV.pref s ∉ I0 := by
        intro s
        constructor
        · intro hpb hp
          have h := hind (.pref s) hp (.prefBar s) hpb
          simp [baseAdj, baseAdjDir] at h
        · intro hp
          rcases hcl (.prefPair s) with ⟨u, huC, huI⟩
          simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at huC
          rcases huC with rfl | rfl
          · exact absurd huI hp
          · exact huI
      have hp0 : BaseV.pref ⟨0, Nat.zero_lt_succ t⟩ ∉ I0 := by
        rcases hcl .prefZero with ⟨u, huC, huI⟩
        simp only [clauseBase, Finset.mem_singleton] at huC
        subst huC
        exact (hpref_bar _).mp huI
      have hpt : BaseV.pref ⟨t, Nat.lt_succ_self t⟩ ∈ I0 := by
        rcases hcl .prefTop with ⟨u, huC, huI⟩
        simp only [clauseBase, Finset.mem_singleton] at huC
        subst huC; exact huI
      have hmono : ∀ s : Fin t, BaseV.pref ⟨s.val, by omega⟩ ∈ I0 →
          BaseV.pref ⟨s.val + 1, by omega⟩ ∈ I0 := by
        intro s hs
        by_contra hnot
        have hbar : BaseV.prefBar ⟨s.val + 1, by omega⟩ ∈ I0 := (hpref_bar _).mpr hnot
        have h := hind (.pref ⟨s.val, by omega⟩) hs (.prefBar ⟨s.val + 1, by omega⟩) hbar
        simp [baseAdj, baseAdjDir] at h
      have hmono_le : ∀ a b' : Fin (t + 1), a.val ≤ b'.val →
          BaseV.pref a ∈ I0 → BaseV.pref b' ∈ I0 := by
        intro a b' hle ha
        have hd : ∀ d : ℕ, ∀ hlt : a.val + d < t + 1, BaseV.pref ⟨a.val + d, hlt⟩ ∈ I0 := by
          intro d
          induction d with
          | zero => intro hlt; simpa using ha
          | succ d ih =>
            intro hlt
            exact hmono ⟨a.val + d, by omega⟩ (ih (by omega))
        have hres := hd (b'.val - a.val) (by have := b'.isLt; omega)
        have hEq : (⟨a.val + (b'.val - a.val), by have := b'.isLt; omega⟩ : Fin (t + 1)) = b' :=
          Fin.ext (by dsimp only; omega)
        rwa [hEq] at hres
      have hsw_iff : ∀ s : Fin t, BaseV.sw s ∈ I0 ↔
          BaseV.pref ⟨s.val, by omega⟩ ∉ I0 ∧ BaseV.pref ⟨s.val + 1, by omega⟩ ∈ I0 := by
        intro s
        constructor
        · intro hsw
          constructor
          · intro hp
            have h := hind (.sw s) hsw (.pref ⟨s.val, by omega⟩) hp
            simp [baseAdj, baseAdjDir] at h
          · by_contra hnot
            have hbar := (hpref_bar ⟨s.val + 1, by omega⟩).mpr hnot
            have h := hind (.sw s) hsw (.prefBar ⟨s.val + 1, by omega⟩) hbar
            simp [baseAdj, baseAdjDir] at h
        · rintro ⟨h0, h1⟩
          rcases hcl (.slotSw s) with ⟨u, huC, huI⟩
          simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at huC
          rcases huC with rfl | rfl | rfl
          · exact absurd huI h0
          · exact absurd h1 ((hpref_bar _).mp huI)
          · exact huI
      have hex_rise : ∃ s : Fin t, BaseV.pref ⟨s.val, by omega⟩ ∉ I0 ∧
          BaseV.pref ⟨s.val + 1, by omega⟩ ∈ I0 := by
        have hfind : ∀ k : ℕ, ∀ hk : k ≤ t, BaseV.pref ⟨k, by omega⟩ ∈ I0 →
            ∃ s : Fin t, BaseV.pref ⟨s.val, by omega⟩ ∉ I0 ∧ BaseV.pref ⟨s.val + 1, by omega⟩ ∈ I0 := by
          intro k
          induction k with
          | zero => intro _ h0; exact absurd h0 hp0
          | succ k ih =>
            intro hle hk1
            by_cases hk : BaseV.pref ⟨k, by omega⟩ ∈ I0
            · exact ih (by omega) hk
            · exact ⟨⟨k, by omega⟩, hk, hk1⟩
        exact hfind t (le_refl t) hpt
      rcases hex_rise with ⟨r, hr0, hr1⟩
      refine ⟨r, (hsw_iff r).mpr ⟨hr0, hr1⟩, ?_⟩
      intro s hs
      rcases (hsw_iff s).mp hs with ⟨hs0, hs1⟩
      apply Fin.ext
      by_contra hne
      have hs_lt := s.isLt
      have hr_lt := r.isLt
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hr0 (hmono_le ⟨s.val + 1, by omega⟩ ⟨r.val, by omega⟩ (by dsimp only; omega) hs1)
      · exact hs0 (hmono_le ⟨r.val + 1, by omega⟩ ⟨s.val, by omega⟩ (by dsimp only; omega) hr1)
    let toT (I0 : Finset (BaseV n t b)) (hI0 : I0 ∈ Good) :
        Σ _ : Fin m × Fin b, Finset (Fin b) :=
      let s := Classical.choose (hslot_unique I0 hI0)
      ⟨(slotEquiv m b hb).symm s, Finset.univ.filter (fun u : Fin b => BaseV.wt u ∈ I0)⟩
    refine Finset.card_bij (fun I0 hI0 => toT I0 hI0) ?_ ?_ ?_
    · intro I0 hI0
      have hs := Classical.choose_spec (hslot_unique I0 hI0)
      set s := Classical.choose (hslot_unique I0 hI0)
      have hsw : BaseV.sw s ∈ I0 := hs.1
      simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hI0
      rcases hI0 with ⟨⟨hlive, hpin, hind⟩, hcl⟩
      have hpinBar : ∀ j : Fin n, BaseV.pinBar j ∈ I0 ↔ x j = false := by
        intro j
        constructor
        · intro hpb
          cases hxj : x j
          · rfl
          · have hp := (hpin j).mpr hxj
            have h := hind (.pin j) hp (.pinBar j) hpb
            simp [baseAdj, baseAdjDir] at h
        · intro hxf
          rcases hcl (.pinPair j) with ⟨u, huC, huI⟩
          simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at huC
          rcases huC with rfl | rfl
          · have := (hpin j).mp huI; rw [hxf] at this; cases this
          · exact huI
      simp only [Target, Finset.mem_sigma, ActiveSlots, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_powerset, toT]
      refine ⟨⟨?_, hlive (.sw s) hsw s rfl⟩, ?_⟩
      · intro j
        cases hpat : pat ((slotEquiv m b hb).symm s).1 j with
        | none => rfl
        | some v =>
          simp only [Option.elim_some, decide_eq_true_eq]
          cases v
          · cases hxj : x j
            · rfl
            · have hp := (hpin j).mpr hxj
              have h := hind (.sw s) hsw (.pin j) hp
              simp [baseAdj, baseAdjDir, hpat] at h
          · cases hxj : x j
            · have hpb := (hpinBar j).mpr hxj
              have h := hind (.sw s) hsw (.pinBar j) hpb
              simp [baseAdj, baseAdjDir, hpat] at h
            · rfl
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        by_contra hge
        have hle : ((slotEquiv m b hb).symm s).2.val ≤ u.val := by dsimp only [s] at *; omega
        have h := hind (.sw s) hsw (.wt u) hu
        simp [baseAdj, baseAdjDir, hle] at h
    · intro I1 hI1 I2 hI2 hEq
      have hs1 := Classical.choose_spec (hslot_unique I1 hI1)
      have hs2 := Classical.choose_spec (hslot_unique I2 hI2)
      set s1 := Classical.choose (hslot_unique I1 hI1)
      set s2 := Classical.choose (hslot_unique I2 hI2)
      have hp_eq : (slotEquiv m b hb).symm s1 = (slotEquiv m b hb).symm s2 :=
        congrArg Sigma.fst hEq
      have hs_eq : s1 = s2 := (slotEquiv m b hb).symm.injective hp_eq
      have hW_eq : (Finset.univ.filter (fun u : Fin b => BaseV.wt u ∈ I1)) =
          (Finset.univ.filter (fun u : Fin b => BaseV.wt u ∈ I2)) := by
        have := congrArg Sigma.snd hEq
        simpa [toT] using this
      have hchar : ∀ I0 (hI0 : I0 ∈ Good) (s : Fin t), BaseV.sw s ∈ I0 →
          I0 = mkBase ((slotEquiv m b hb).symm s) (Finset.univ.filter (fun u : Fin b => BaseV.wt u ∈ I0)) := by
        intro I0 hI0 s hsw
        have hu_s := hslot_unique I0 hI0
        simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hI0
        rcases hI0 with ⟨⟨_, hpin, hind⟩, hcl⟩
        have hpinBar : ∀ j : Fin n, BaseV.pinBar j ∈ I0 ↔ x j = false := by
          intro j; constructor
          · intro hpb; cases hxj : x j; rfl
            have h := hind (.pin j) ((hpin j).mpr hxj) (.pinBar j) hpb
            simp [baseAdj, baseAdjDir] at h
          · intro hxf
            rcases hcl (.pinPair j) with ⟨u, huC, huI⟩
            simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at huC
            rcases huC with rfl | rfl
            · have := (hpin j).mp huI; rw [hxf] at this; cases this
            · exact huI
        have hpref_bar : ∀ r : Fin (t + 1), BaseV.prefBar r ∈ I0 ↔ BaseV.pref r ∉ I0 := by
          intro r; constructor
          · intro hpb hp; have h := hind (.pref r) hp (.prefBar r) hpb; simp [baseAdj, baseAdjDir] at h
          · intro hp
            rcases hcl (.prefPair r) with ⟨u, huC, huI⟩
            simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at huC
            rcases huC with rfl | rfl
            · exact absurd huI hp
            · exact huI
        have hmono : ∀ r : Fin t, BaseV.pref ⟨r.val, by omega⟩ ∈ I0 →
            BaseV.pref ⟨r.val + 1, by omega⟩ ∈ I0 := by
          intro r hr; by_contra hnot
          have h := hind (.pref ⟨r.val, by omega⟩) hr (.prefBar ⟨r.val + 1, by omega⟩) ((hpref_bar _).mpr hnot)
          simp [baseAdj, baseAdjDir] at h
        have hmono_le : ∀ a b' : Fin (t + 1), a.val ≤ b'.val →
            BaseV.pref a ∈ I0 → BaseV.pref b' ∈ I0 := by
          intro a b' hle ha
          have hd : ∀ d : ℕ, ∀ hlt : a.val + d < t + 1, BaseV.pref ⟨a.val + d, hlt⟩ ∈ I0 := by
            intro d; induction d with
            | zero => intro hlt; simpa using ha
            | succ d ih => intro hlt; exact hmono ⟨a.val + d, by omega⟩ (ih (by omega))
          have hres := hd (b'.val - a.val) (by have := b'.isLt; omega)
          have hEq : (⟨a.val + (b'.val - a.val), by have := b'.isLt; omega⟩ : Fin (t + 1)) = b' :=
            Fin.ext (by dsimp only; omega)
          rwa [hEq] at hres
        have hs_lt := s.isLt
        have hs0 : BaseV.pref ⟨s.val, by omega⟩ ∉ I0 := fun hp => by
          have h := hind (.sw s) hsw (.pref ⟨s.val, by omega⟩) hp; simp [baseAdj, baseAdjDir] at h
        have hs1 : BaseV.pref ⟨s.val + 1, by omega⟩ ∈ I0 := by
          by_contra hnot
          have h := hind (.sw s) hsw (.prefBar ⟨s.val + 1, by omega⟩) ((hpref_bar _).mpr hnot)
          simp [baseAdj, baseAdjDir] at h
        have hpref_iff : ∀ r : Fin (t + 1), BaseV.pref r ∈ I0 ↔ s.val < r.val := by
          intro r; constructor
          · intro hr; by_contra hle
            exact hs0 (hmono_le r ⟨s.val, by omega⟩ (by dsimp only; omega) hr)
          · intro hlt
            exact hmono_le ⟨s.val + 1, by omega⟩ r (by dsimp only; omega) hs1
        ext v
        simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
        cases v with
        | pin j => exact hpin j
        | pinBar j => exact hpinBar j
        | pref r => exact hpref_iff r
        | prefBar r => rw [hpref_bar, hpref_iff]; omega
        | sw r =>
          constructor
          · intro hr
            rcases hu_s with ⟨r0, hr0, huniq⟩
            exact (huniq r hr).trans (huniq s hsw).symm
          · rintro rfl; exact hsw
        | wt u => simp
      rw [hchar I1 hI1 s1 hs1.1, hchar I2 hI2 s2 hs2.1, hs_eq, hW_eq]
    · intro pair hpair
      rcases pair with ⟨p, W⟩
      simp only [Target, Finset.mem_sigma, ActiveSlots, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_powerset] at hpair
      rcases hpair with ⟨⟨hpat, hbit⟩, hWsub⟩
      let s0 := slotEquiv m b hb p
      have hmk_good : mkBase p W ∈ Good := by
        simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · intro v hv s hvs
          subst hvs
          simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          subst hv
          simpa using hbit
        · intro j; simp [mkBase]
        · intro u hu v hv
          simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
          have hdir : ∀ a b' : BaseV n t b,
              (match a with | .pin j => x j = true | .pinBar j => x j = false | .pref s => s0.val < s.val | .prefBar s => s.val ≤ s0.val | .sw s => s = s0 | .wt u => u ∈ W) →
              (match b' with | .pin j => x j = true | .pinBar j => x j = false | .pref s => s0.val < s.val | .prefBar s => s.val ≤ s0.val | .sw s => s = s0 | .wt u => u ∈ W) →
              baseAdjDir hb pat a b' = false := by
            intro a b' ha hb'
            cases a <;> cases b' <;> dsimp only at ha hb' <;>
              simp only [baseAdjDir, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                ne_eq, decide_eq_false_iff_not, not_le]
            all_goals try rfl
            · intro h; subst h; rw [ha] at hb'; cases hb'
            · constructor
              · intro h; subst h; omega
              · omega
            · rename_i _ k
              dsimp only [s0] at ha; subst ha
              simp only [Equiv.symm_apply_apply]
              have hpatj := hpat k
              cases h : pat p.1 k with
              | none => simp
              | some val =>
                simp only [h, Option.elim_some, decide_eq_true_eq] at hpatj
                intro heq; injection heq with hval; subst hval
                rw [hb'] at hpatj; cases hpatj
            · rename_i _ k
              dsimp only [s0] at ha; subst ha
              simp only [Equiv.symm_apply_apply]
              have hpatj := hpat k
              cases h : pat p.1 k with
              | none => simp
              | some val =>
                simp only [h, Option.elim_some, decide_eq_true_eq] at hpatj
                intro heq; injection heq with hval; subst hval
                rw [hb'] at hpatj; cases hpatj
            · subst ha; omega
            · subst ha; omega
            · dsimp only [s0] at ha; subst ha
              simp only [Equiv.symm_apply_apply]
              have := hWsub hb'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
              exact this
          simp only [baseAdj, hdir u v hu hv, hdir v u hv hu, Bool.or_self]
        · intro c
          cases c with
          | pinPair j =>
            cases hxj : x j
            · exact ⟨.pinBar j, by simp [clauseBase], by simp [mkBase, hxj]⟩
            · exact ⟨.pin j, by simp [clauseBase], by simp [mkBase, hxj]⟩
          | prefPair s =>
            by_cases hlt : s0.val < s.val
            · exact ⟨.pref s, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt⟩
            · exact ⟨.prefBar s, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; dsimp only [s0] at hlt; omega⟩
          | prefZero =>
            exact ⟨.prefBar ⟨0, Nat.zero_lt_succ t⟩, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; exact Nat.zero_le _⟩
          | prefTop =>
            exact ⟨.pref ⟨t, Nat.lt_succ_self t⟩, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; exact s0.isLt⟩
          | slotSw s =>
            by_cases hlt : s0.val < s.val
            · exact ⟨.pref ⟨s.val, by omega⟩, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt⟩
            · by_cases hgt : s.val + 1 ≤ s0.val
              · exact ⟨.prefBar ⟨s.val + 1, by omega⟩, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; exact hgt⟩
              · have hEq : s = s0 := Fin.ext (by omega)
                exact ⟨.sw s, by simp [clauseBase], by simp only [mkBase, Finset.mem_filter, Finset.mem_univ, true_and]; exact hEq⟩
      refine ⟨mkBase p W, hmk_good, ?_⟩
      have hs := Classical.choose_spec (hslot_unique (mkBase p W) hmk_good)
      have hsw_in : BaseV.sw s0 ∈ mkBase p W := by simp [mkBase, s0]
      have hchoose : Classical.choose (hslot_unique (mkBase p W) hmk_good) = s0 :=
        (hs.2 s0 hsw_in).symm
      dsimp only [toT]
      rw [hchoose]
      simp only [s0, Equiv.symm_apply_apply]
      congr 1
      ext u; simp [mkBase]
  rw [hbij]
  simp only [Target, Finset.card_sigma, Finset.card_powerset]
  have hcard_lt : ∀ p : Fin m × Fin b,
      ((Finset.univ : Finset (Fin b)).filter (fun u : Fin b => u.val < p.2.val)).card = p.2.val := by
    intro p
    refine (Finset.card_bij (t := Finset.range p.2.val) (fun (u : Fin b) _ => u.val) ?_ ?_ ?_).trans
      (Finset.card_range p.2.val)
    · intro u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact Finset.mem_range.mpr hu
    · intro u1 _ u2 _ h; exact Fin.ext h
    · intro k hk
      have hlt : k < p.2.val := Finset.mem_range.mp hk
      exact ⟨⟨k, lt_trans hlt p.2.isLt⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt, rfl⟩
  rw [Finset.sum_congr rfl (fun p _ => by rw [hcard_lt p])]
  have hprod_sum : (∑ p ∈ ActiveSlots, 2 ^ p.2.val) =
      ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i =>
        ∀ j, (pat i j).elim true (fun v => decide (v = x j)) = true),
      ∑ j : Fin b, if (f i).val.testBit j.val then 2 ^ j.val else 0 := by
    have h1 : (∑ p ∈ ActiveSlots, 2 ^ p.2.val) =
        ∑ p : Fin m × Fin b, if p ∈ ActiveSlots then 2 ^ p.2.val else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [h1, Fintype.sum_prod_type, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hmi : ∀ j, (pat i j).elim true (fun v => decide (v = x j)) = true
    · rw [if_pos hmi]
      apply Finset.sum_congr rfl
      intro j _
      simp [ActiveSlots, hmi]
    · rw [if_neg hmi]
      simp [ActiveSlots, hmi]
  rw [hprod_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_testBit_two_pow b (f i).val (lt_trans (f i).isLt hMlt)

-- =========================================================================
-- Part 5: Path decomposition on Vtx with bag size <= 2*n + 3*b + 5
-- =========================================================================

private def coreBag {n t b kH : ℕ} : Finset (Vtx n t b kH) :=
  (Finset.univ.image (fun j : Fin n => Vtx.base (BaseV.pin j))) ∪
  (Finset.univ.image (fun j : Fin n => Vtx.base (BaseV.pinBar j))) ∪
  (Finset.univ.image (fun u : Fin b => Vtx.base (BaseV.wt u)))

private def gadBag {n t b kH : ℕ} (c : ClauseId n t) : Finset (Vtx n t b kH) :=
  Finset.univ.image (fun v : Fin kH => Vtx.gad c v)

private lemma coreBag_card_le (n t b kH : ℕ) : (coreBag (n := n) (t := t) (b := b) (kH := kH)).card ≤ 2 * n + b := by
  let s1 : Finset (Vtx n t b kH) := Finset.univ.image (fun j : Fin n => Vtx.base (BaseV.pin j))
  let s2 : Finset (Vtx n t b kH) := Finset.univ.image (fun j : Fin n => Vtx.base (BaseV.pinBar j))
  let s3 : Finset (Vtx n t b kH) := Finset.univ.image (fun u : Fin b => Vtx.base (BaseV.wt u))
  change (s1 ∪ s2 ∪ s3).card ≤ 2 * n + b
  have h1 := Finset.card_union_le (s1 ∪ s2) s3
  have h2 := Finset.card_union_le s1 s2
  have ha : s1.card ≤ n := by simpa [s1] using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n => Vtx.base (t := t) (b := b) (kH := kH) (BaseV.pin j))
  have hb' : s2.card ≤ n := by simpa [s2] using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n => Vtx.base (t := t) (b := b) (kH := kH) (BaseV.pinBar j))
  have hc : s3.card ≤ b := by simpa [s3] using Finset.card_image_le (s := (Finset.univ : Finset (Fin b))) (f := fun u : Fin b => Vtx.base (n := n) (t := t) (kH := kH) (BaseV.wt u))
  omega

private lemma gadBag_card_le (n t b kH : ℕ) (c : ClauseId n t) :
    (gadBag (n := n) (t := t) (b := b) (kH := kH) c).card ≤ kH := by
  unfold gadBag
  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin kH)))
    (f := fun v : Fin kH => Vtx.gad (n := n) (t := t) (b := b) c v)

-- Bag layout indexed by Fin (n + 2*t + 3):
--   idx < n:               pinPair ⟨idx, _⟩  -> core ∪ gadBag (pinPair j)
--   idx = n:               prefZero          -> core ∪ {pref 0, prefBar 0} ∪ gadBag prefZero
--   idx = n + 1:           prefPair 0        -> core ∪ {pref 0, prefBar 0} ∪ gadBag (prefPair 0)
--   idx = n + 2 + 2*s:     slotSw s          -> core ∪ {pref s, prefBar s, pref (s+1), prefBar (s+1), sw s} ∪ gadBag (slotSw s)
--   idx = n + 2 + 2*s + 1: prefPair (s+1)    -> core ∪ {pref (s+1), prefBar (s+1)} ∪ gadBag (prefPair (s+1))
--   idx = n + 2*t + 2:     prefTop           -> core ∪ {pref t, prefBar t} ∪ gadBag prefTop
private def pathBag (n t b kH : ℕ) (idx : Fin (n + 2 * t + 3)) : Finset (Vtx n t b kH) :=
  if h1 : idx.val < n then
    coreBag ∪ gadBag (.pinPair ⟨idx.val, h1⟩)
  else if h2 : idx.val = n then
    coreBag ∪ {.base (.pref ⟨0, Nat.zero_lt_succ t⟩), .base (.prefBar ⟨0, Nat.zero_lt_succ t⟩)} ∪ gadBag .prefZero
  else if h3 : idx.val = n + 1 then
    coreBag ∪ {.base (.pref ⟨0, Nat.zero_lt_succ t⟩), .base (.prefBar ⟨0, Nat.zero_lt_succ t⟩)} ∪
      gadBag (.prefPair ⟨0, Nat.zero_lt_succ t⟩)
  else if htop : idx.val = n + 2 * t + 2 then
    coreBag ∪ {.base (.pref ⟨t, Nat.lt_succ_self t⟩), .base (.prefBar ⟨t, Nat.lt_succ_self t⟩)} ∪ gadBag .prefTop
  else if hev : (idx.val - (n + 2)) % 2 = 0 then
    coreBag ∪
      {.base (.pref ⟨(idx.val - (n + 2)) / 2, by have := idx.isLt; omega⟩),
       .base (.prefBar ⟨(idx.val - (n + 2)) / 2, by have := idx.isLt; omega⟩),
       .base (.pref ⟨(idx.val - (n + 2)) / 2 + 1, by have := idx.isLt; omega⟩),
       .base (.prefBar ⟨(idx.val - (n + 2)) / 2 + 1, by have := idx.isLt; omega⟩),
       .base (.sw ⟨(idx.val - (n + 2)) / 2, by have := idx.isLt; omega⟩)} ∪
      gadBag (.slotSw ⟨(idx.val - (n + 2)) / 2, by have := idx.isLt; omega⟩)
  else
    coreBag ∪
      {.base (.pref ⟨(idx.val - (n + 2)) / 2 + 1, by have := idx.isLt; omega⟩),
       .base (.prefBar ⟨(idx.val - (n + 2)) / 2 + 1, by have := idx.isLt; omega⟩)} ∪
      gadBag (.prefPair ⟨(idx.val - (n + 2)) / 2 + 1, by have := idx.isLt; omega⟩)

private lemma pathBag_card_le {n t b kH : ℕ} (hkH : kH ≤ 2 * b) (idx : Fin (n + 2 * t + 3)) :
    (pathBag n t b kH idx).card ≤ 2 * n + 3 * b + 5 := by
  have hc := coreBag_card_le n t b kH
  have hg := fun c => le_trans (gadBag_card_le n t b kH c) hkH
  have hU : ∀ (s : Finset (Vtx n t b kH)) (c : ClauseId n t), s.card ≤ 5 →
      (coreBag (n := n) (t := t) (b := b) (kH := kH) ∪ s ∪ gadBag c).card ≤ 2 * n + 3 * b + 5 := by
    intro s c hs
    have h1 := Finset.card_union_le (coreBag (n := n) (t := t) (b := b) (kH := kH) ∪ s) (gadBag c)
    have h2 := Finset.card_union_le (coreBag (n := n) (t := t) (b := b) (kH := kH)) s
    have h3 := hg c
    omega
  have hcard2 : ∀ a1 a2 : Vtx n t b kH, ({a1, a2} : Finset (Vtx n t b kH)).card ≤ 5 := by
    intro a1 a2
    have := Finset.card_insert_le a1 ({a2} : Finset (Vtx n t b kH))
    simp only [Finset.card_singleton] at this
    omega
  have hcard5 : ∀ a1 a2 a3 a4 a5 : Vtx n t b kH, ({a1, a2, a3, a4, a5} : Finset (Vtx n t b kH)).card ≤ 5 := by
    intro a1 a2 a3 a4 a5
    have h1 := Finset.card_insert_le a1 ({a2, a3, a4, a5} : Finset (Vtx n t b kH))
    have h2 := Finset.card_insert_le a2 ({a3, a4, a5} : Finset (Vtx n t b kH))
    have h3 := Finset.card_insert_le a3 ({a4, a5} : Finset (Vtx n t b kH))
    have h4 := Finset.card_insert_le a4 ({a5} : Finset (Vtx n t b kH))
    simp only [Finset.card_singleton] at h4
    omega
  unfold pathBag
  split_ifs with h1 h2 h3 h4 h5
  · have ha := Finset.card_union_le (coreBag (n := n) (t := t) (b := b) (kH := kH)) (gadBag (.pinPair ⟨idx.val, h1⟩))
    have hb := hg (.pinPair ⟨idx.val, h1⟩)
    omega
  · exact hU _ _ (hcard2 _ _)
  · exact hU _ _ (hcard2 _ _)
  · exact hU _ _ (hcard2 _ _)
  · exact hU _ _ (hcard5 _ _ _ _ _)
  · exact hU _ _ (hcard2 _ _)

private lemma mem_core_in_pathBag (n t b kH : ℕ) (v : Vtx n t b kH) (hv : v ∈ coreBag)
    (idx : Fin (n + 2 * t + 3)) : v ∈ pathBag n t b kH idx := by
  unfold pathBag
  split_ifs <;> simp [Finset.mem_union, hv]

private lemma pin_mem_core (n t b kH : ℕ) (j : Fin n) :
    Vtx.base (BaseV.pin j) ∈ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
  simp [coreBag]

private lemma pinBar_mem_core (n t b kH : ℕ) (j : Fin n) :
    Vtx.base (BaseV.pinBar j) ∈ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
  simp [coreBag]

private lemma wt_mem_core (n t b kH : ℕ) (u : Fin b) :
    Vtx.base (BaseV.wt u) ∈ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
  simp [coreBag]

private def inBagPred {n t b kH : ℕ} (v : Vtx n t b kH) (k : ℕ) : Prop :=
  match v with
  | .base (.pin _) => True
  | .base (.pinBar _) => True
  | .base (.wt _) => True
  | .base (.pref r) => n + 2 * r.val ≤ k ∧ k ≤ n + 2 * r.val + 2
  | .base (.prefBar r) => n + 2 * r.val ≤ k ∧ k ≤ n + 2 * r.val + 2
  | .base (.sw s) => k = n + 2 + 2 * s.val
  | .gad (.pinPair j) _ => k = j.val
  | .gad .prefZero _ => k = n
  | .gad (.prefPair s) _ => k = n + 1 + 2 * s.val
  | .gad .prefTop _ => k = n + 2 * t + 2
  | .gad (.slotSw s) _ => k = n + 2 + 2 * s.val

private lemma mem_gadBag_iff {n t b kH : ℕ} (c1 c2 : ClauseId n t) (a : Fin kH) :
    Vtx.gad c1 a ∈ gadBag (n := n) (t := t) (b := b) (kH := kH) c2 ↔ c1 = c2 := by
  simp only [gadBag, Finset.mem_image, Finset.mem_univ, true_and, Vtx.gad.injEq]
  constructor
  · rintro ⟨_, h, _⟩; exact h.symm
  · intro h; exact ⟨a, h.symm, rfl⟩

private lemma mem_pathBag_iff (n t b kH : ℕ) (v : Vtx n t b kH) (idx : Fin (n + 2 * t + 3)) :
    v ∈ pathBag n t b kH idx ↔ inBagPred v idx.val := by
  have hidx := idx.isLt
  have hni_core_pref : ∀ r : Fin (t + 1), Vtx.base (BaseV.pref r) ∉ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
    intro r; simp [coreBag]
  have hni_core_pbar : ∀ r : Fin (t + 1), Vtx.base (BaseV.prefBar r) ∉ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
    intro r; simp [coreBag]
  have hni_core_sw : ∀ s : Fin t, Vtx.base (BaseV.sw s) ∉ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
    intro s; simp [coreBag]
  have hni_core_gad : ∀ c a, Vtx.gad c a ∉ coreBag (n := n) (t := t) (b := b) (kH := kH) := by
    intro c a; simp [coreBag]
  have hni_gad_base : ∀ x c, Vtx.base x ∉ gadBag (n := n) (t := t) (b := b) (kH := kH) c := by
    intro x c; simp [gadBag]
  cases v with
  | base x =>
    cases x with
    | pin j => simp [inBagPred, mem_core_in_pathBag n t b kH _ (pin_mem_core n t b kH j)]
    | pinBar j => simp [inBagPred, mem_core_in_pathBag n t b kH _ (pinBar_mem_core n t b kH j)]
    | wt u => simp [inBagPred, mem_core_in_pathBag n t b kH _ (wt_mem_core n t b kH u)]
    | pref r =>
      have hr := r.isLt
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_pref, hni_gad_base, false_or, or_false, Vtx.base.injEq, BaseV.pref.injEq,
        reduceCtorEq, Fin.ext_iff]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
    | prefBar r =>
      have hr := r.isLt
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_pbar, hni_gad_base, false_or, or_false, Vtx.base.injEq, BaseV.prefBar.injEq,
        reduceCtorEq, Fin.ext_iff]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
    | sw s =>
      have hs := s.isLt
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_sw, hni_gad_base, false_or, or_false, Vtx.base.injEq, BaseV.sw.injEq,
        reduceCtorEq, Fin.ext_iff]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
  | gad c a =>
    cases c with
    | pinPair j =>
      have hj := j.isLt
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_gad, mem_gadBag_iff, false_or, or_false,
        ClauseId.pinPair.injEq, reduceCtorEq, Fin.ext_iff]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
    | prefZero =>
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_gad, mem_gadBag_iff, false_or, or_false, reduceCtorEq]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
    | prefPair s =>
      have hs := s.isLt
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_gad, mem_gadBag_iff, false_or, or_false,
        ClauseId.prefPair.injEq, reduceCtorEq, Fin.ext_iff]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
    | prefTop =>
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_gad, mem_gadBag_iff, false_or, or_false, reduceCtorEq]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega
    | slotSw s =>
      have hs := s.isLt
      unfold pathBag inBagPred
      split_ifs with h1 h2 h3 h4 h5
      all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hni_core_gad, mem_gadBag_iff, false_or, or_false,
        ClauseId.slotSw.injEq, reduceCtorEq, Fin.ext_iff]
      all_goals constructor <;> intro h <;> first | exact False.elim h | trivial | omega

private lemma pathBag_ri (n t b kH : ℕ) (v : Vtx n t b kH)
    (i j k : Fin (n + 2 * t + 3)) (hij : i ≤ j) (hjk : j ≤ k)
    (hvi : v ∈ pathBag n t b kH i) (hvk : v ∈ pathBag n t b kH k) :
    v ∈ pathBag n t b kH j := by
  rw [mem_pathBag_iff] at hvi hvk ⊢
  have hij' : i.val ≤ j.val := hij
  have hjk' : j.val ≤ k.val := hjk
  cases v with
  | base x =>
    cases x <;> simp only [inBagPred] at hvi hvk ⊢ <;> first | trivial | omega
  | gad c a =>
    cases c <;> simp only [inBagPred] at hvi hvk ⊢ <;> omega

private lemma pathBag_cover_v (n t b kH : ℕ) (v : Vtx n t b kH) :
    ∃ idx : Fin (n + 2 * t + 3), v ∈ pathBag n t b kH idx := by
  cases v with
  | base x =>
    cases x with
    | pin j => exact ⟨⟨n, by omega⟩, (mem_pathBag_iff ..).mpr trivial⟩
    | pinBar j => exact ⟨⟨n, by omega⟩, (mem_pathBag_iff ..).mpr trivial⟩
    | wt u => exact ⟨⟨n, by omega⟩, (mem_pathBag_iff ..).mpr trivial⟩
    | pref r =>
      have := r.isLt
      exact ⟨⟨n + 2 * r.val, by omega⟩, (mem_pathBag_iff ..).mpr (by simp [inBagPred])⟩
    | prefBar r =>
      have := r.isLt
      exact ⟨⟨n + 2 * r.val, by omega⟩, (mem_pathBag_iff ..).mpr (by simp [inBagPred])⟩
    | sw s =>
      have := s.isLt
      exact ⟨⟨n + 2 + 2 * s.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl⟩
  | gad c a =>
    cases c with
    | pinPair j => have := j.isLt; exact ⟨⟨j.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl⟩
    | prefZero => exact ⟨⟨n, by omega⟩, (mem_pathBag_iff ..).mpr rfl⟩
    | prefPair s => have := s.isLt; exact ⟨⟨n + 1 + 2 * s.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl⟩
    | prefTop => exact ⟨⟨n + 2 * t + 2, by omega⟩, (mem_pathBag_iff ..).mpr rfl⟩
    | slotSw s => have := s.isLt; exact ⟨⟨n + 2 + 2 * s.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl⟩

private lemma pathBag_cover_e {n m b kH : ℕ} (hb : 0 < b) (pat : Fin m → Fin n → Option Bool)
    (H : Fin kH → Finset (Fin kH)) (u v : Vtx n (m * b) b kH)
    (huv : fullAdj hb pat H u v = true) :
    ∃ idx : Fin (n + 2 * (m * b) + 3), u ∈ pathBag n (m * b) b kH idx ∧ v ∈ pathBag n (m * b) b kH idx := by
  have hbase_dir : ∀ x y : BaseV n (m * b) b, baseAdjDir hb pat x y = true →
      ∃ idx : Fin (n + 2 * (m * b) + 3), Vtx.base x ∈ pathBag n (m * b) b kH idx ∧ Vtx.base y ∈ pathBag n (m * b) b kH idx := by
    intro x y hxy
    cases x with
    | pin j =>
      cases y with
      | pinBar j' =>
        exact ⟨⟨n, by omega⟩, (mem_pathBag_iff ..).mpr trivial, (mem_pathBag_iff ..).mpr trivial⟩
      | pin _ | pref _ | prefBar _ | sw _ | wt _ => simp [baseAdjDir] at hxy
    | pref s1 =>
      cases y with
      | prefBar s2 =>
        simp only [baseAdjDir, Bool.or_eq_true, beq_iff_eq] at hxy
        have hs1 := s1.isLt; have hs2 := s2.isLt
        rcases hxy with hEq | hSucc
        · subst hEq
          exact ⟨⟨n + 2 * s1.val, by omega⟩,
            (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega),
            (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)⟩
        · exact ⟨⟨n + 2 + 2 * s1.val, by omega⟩,
            (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega),
            (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)⟩
      | pin _ | pinBar _ | pref _ | sw _ | wt _ => simp [baseAdjDir] at hxy
    | sw s =>
      have hs := s.isLt
      cases y with
      | pref s' =>
        simp only [baseAdjDir, beq_iff_eq] at hxy
        exact ⟨⟨n + 2 + 2 * s.val, by omega⟩,
          (mem_pathBag_iff ..).mpr rfl,
          (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)⟩
      | prefBar s' =>
        simp only [baseAdjDir, beq_iff_eq] at hxy
        exact ⟨⟨n + 2 + 2 * s.val, by omega⟩,
          (mem_pathBag_iff ..).mpr rfl,
          (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)⟩
      | pin k =>
        exact ⟨⟨n + 2 + 2 * s.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl, (mem_pathBag_iff ..).mpr trivial⟩
      | pinBar k =>
        exact ⟨⟨n + 2 + 2 * s.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl, (mem_pathBag_iff ..).mpr trivial⟩
      | wt w =>
        exact ⟨⟨n + 2 + 2 * s.val, by omega⟩, (mem_pathBag_iff ..).mpr rfl, (mem_pathBag_iff ..).mpr trivial⟩
      | sw _ => simp [baseAdjDir] at hxy
    | pinBar _ | prefBar _ | wt _ =>
      cases y <;> simp [baseAdjDir] at hxy
  have hclause_cov : ∀ (c : ClauseId n (m * b)) (x : BaseV n (m * b) b) (a : Fin kH), x ∈ clauseBase c →
      ∃ idx : Fin (n + 2 * (m * b) + 3), Vtx.base x ∈ pathBag n (m * b) b kH idx ∧ Vtx.gad c a ∈ pathBag n (m * b) b kH idx := by
    intro c x a hx
    cases c with
    | pinPair j =>
      have := j.isLt
      simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at hx
      refine ⟨⟨j.val, by omega⟩, ?_, (mem_pathBag_iff ..).mpr rfl⟩
      rcases hx with rfl | rfl <;> exact (mem_pathBag_iff ..).mpr trivial
    | prefPair s =>
      have := s.isLt
      simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at hx
      refine ⟨⟨n + 1 + 2 * s.val, by omega⟩, ?_, (mem_pathBag_iff ..).mpr rfl⟩
      rcases hx with rfl | rfl <;> exact (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)
    | prefZero =>
      simp only [clauseBase, Finset.mem_singleton] at hx; subst hx
      exact ⟨⟨n, by omega⟩, (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega), (mem_pathBag_iff ..).mpr rfl⟩
    | prefTop =>
      simp only [clauseBase, Finset.mem_singleton] at hx; subst hx
      exact ⟨⟨n + 2 * (m * b) + 2, by omega⟩, (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega), (mem_pathBag_iff ..).mpr rfl⟩
    | slotSw s =>
      have := s.isLt
      simp only [clauseBase, Finset.mem_insert, Finset.mem_singleton] at hx
      refine ⟨⟨n + 2 + 2 * s.val, by omega⟩, ?_, (mem_pathBag_iff ..).mpr rfl⟩
      rcases hx with rfl | rfl | rfl
      · exact (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)
      · exact (mem_pathBag_iff ..).mpr (by simp only [inBagPred]; omega)
      · exact (mem_pathBag_iff ..).mpr rfl
  cases u with
  | base x =>
    cases v with
    | base y =>
      simp only [fullAdj, baseAdj, Bool.or_eq_true] at huv
      rcases huv with h | h
      · exact hbase_dir x y h
      · rcases hbase_dir y x h with ⟨idx, hy, hx⟩; exact ⟨idx, hx, hy⟩
    | gad c a =>
      simp only [fullAdj, decide_eq_true_eq] at huv
      exact hclause_cov c x a huv
  | gad c a =>
    cases v with
    | base y =>
      simp only [fullAdj, decide_eq_true_eq] at huv
      rcases hclause_cov c y a huv with ⟨idx, hy, hg⟩; exact ⟨idx, hg, hy⟩
    | gad c2 d =>
      simp only [fullAdj, decide_eq_true_eq] at huv
      rcases huv with ⟨rfl, _⟩
      rcases pathBag_cover_v n (m * b) b kH (.gad c a) with ⟨idx, ha⟩
      refine ⟨idx, ha, ?_⟩
      rw [mem_pathBag_iff] at ha ⊢
      cases c <;> exact ha

-- =========================================================================
-- Part 6: Transport along Fintype.equivFin and main theorem
-- =========================================================================

private lemma main_aux_core (M n m : ℕ) (hM : 2 ≤ M)
    (pat : Fin m → Fin n → Option Bool) :
    let b := Nat.log2 M + 1
    let t := m * b
    ∃ (N : ℕ) (G : Fin N → Finset (Fin N)) (pin : Fin n → Fin N)
      (sw : Fin m × Fin b → Fin N),
      N ≤ (2 + 2 * b) * (n + t + 1) + t + 2 * b * (t + 2) + b ∧
      Function.Injective pin ∧ Function.Injective sw ∧
      (∀ j k, pin j ≠ sw k) ∧ (∀ v, v ∉ G v) ∧
      (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
      (∃ (h : ℕ) (bag : Fin h → Finset (Fin N)),
        (∀ i, (bag i).card ≤ 2 * n + 3 * b + 5) ∧ (∀ i j, pin j ∈ bag i) ∧
        (∀ v, ∃ i, v ∈ bag i) ∧
        (∀ u v, v ∈ G u → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
        ∀ v i j k, i ≤ j → j ≤ k → v ∈ bag i → v ∈ bag k → v ∈ bag j) ∧
      ∀ (f : Fin m → Fin M) (x : Fin n → Bool),
        let live := fun v => ∀ k, v = sw k → (f k.1).val.testBit k.2.val = true
        let count := ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
          (∀ v ∈ I, live v) ∧ (∀ j, pin j ∈ I ↔ x j = true) ∧
          ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card
        count % M = (((Finset.univ : Finset (Fin m)).filter
          (fun i => ∀ j, (pat i j).elim true (fun v => decide (v = x j)) = true)).sum
          (fun i => (f i).val)) % M := by
  classical
  intro b t
  have hb : 0 < b := Nat.succ_pos _
  rcases exists_indGraph_card M (by omega) with ⟨kH, H, hkH, hHloop, hHsym, hHcard⟩
  let e : Vtx n t b kH ≃ Fin (Fintype.card (Vtx n t b kH)) := Fintype.equivFin (Vtx n t b kH)
  set N := Fintype.card (Vtx n t b kH)
  let G : Fin N → Finset (Fin N) := fun u =>
    Finset.univ.filter (fun v => fullAdj hb pat H (e.symm u) (e.symm v) = true)
  let pin : Fin n → Fin N := fun j => e (.base (.pin j))
  let sw : Fin m × Fin b → Fin N := fun k => e (.base (.sw (slotEquiv m b hb k)))
  have hNle : N ≤ (2 + 2 * b) * (n + t + 1) + t + 2 * b * (t + 2) + b := by
    have hcard : N = 2 * n + 3 * t + b + 2 + (n + 2 * t + 3) * kH := card_vtx n t b kH
    have hmul : (n + 2 * t + 3) * kH ≤ (n + 2 * t + 3) * (2 * b) := Nat.mul_le_mul_left _ hkH
    nlinarith
  have hpin_inj : Function.Injective pin := by
    intro j1 j2 h
    have := e.injective h; cases this; rfl
  have hsw_inj : Function.Injective sw := by
    intro k1 k2 h
    have h1 := e.injective h
    injection h1 with h2
    injection h2 with h3
    exact (slotEquiv m b hb).injective h3
  have hpin_sw : ∀ j k, pin j ≠ sw k := by
    intro j k h
    have := e.injective h; cases this
  have hloop : ∀ v, v ∉ G v := by
    intro v hv
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [fullAdj_irrefl hb pat hHloop] at hv; cases hv
  have hsym : ∀ u v, v ∈ G u ↔ u ∈ G v := by
    intro u v
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fullAdj_symm hb pat hHsym]
  refine ⟨N, G, pin, sw, hNle, hpin_inj, hsw_inj, hpin_sw, hloop, hsym, ?_, ?_⟩
  · let bag : Fin (n + 2 * t + 3) → Finset (Fin N) := fun i => (pathBag n t b kH i).image e
    refine ⟨n + 2 * t + 3, bag, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact le_trans Finset.card_image_le (pathBag_card_le hkH i)
    · intro i j
      exact Finset.mem_image.mpr ⟨.base (.pin j),
        mem_core_in_pathBag n t b kH _ (pin_mem_core n t b kH j) i, rfl⟩
    · intro v
      rcases pathBag_cover_v n t b kH (e.symm v) with ⟨i, hi⟩
      exact ⟨i, Finset.mem_image.mpr ⟨e.symm v, hi, e.apply_symm_apply v⟩⟩
    · intro u v hv
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases pathBag_cover_e hb pat H (e.symm u) (e.symm v) hv with ⟨i, hu, hv'⟩
      exact ⟨i, Finset.mem_image.mpr ⟨e.symm u, hu, e.apply_symm_apply u⟩,
                Finset.mem_image.mpr ⟨e.symm v, hv', e.apply_symm_apply v⟩⟩
    · intro v i j k hij hjk hvi hvk
      have hm : ∀ r, v ∈ bag r ↔ e.symm v ∈ pathBag n t b kH r := by
        intro r; simp only [bag, Finset.mem_image]
        constructor
        · rintro ⟨w, hw, hwv⟩; rw [← hwv, Equiv.symm_apply_apply]; exact hw
        · intro hv; exact ⟨e.symm v, hv, e.apply_symm_apply v⟩
      exact (hm j).mpr (pathBag_ri n t b kH (e.symm v) i j k hij hjk ((hm i).mp hvi) ((hm k).mp hvk))
  · intro f x live count
    let Gv : Vtx n t b kH → Finset (Vtx n t b kH) := fun u =>
      Finset.univ.filter (fun v => fullAdj hb pat H u v = true)
    let liveV : Vtx n t b kH → Prop := fun v =>
      ∀ k : Fin m × Fin b, v = .base (.sw (slotEquiv m b hb k)) → (f k.1).val.testBit k.2.val = true
    have hcount_eq : count = ((Finset.univ : Finset (Finset (Vtx n t b kH))).filter (fun I =>
        (∀ v ∈ I, liveV v) ∧ (∀ j, Vtx.base (BaseV.pin j) ∈ I ↔ x j = true) ∧
        isIndep Gv I)).card := by
      refine Finset.card_bij' (fun I _ => I.image e.symm) (fun J _ => J.image e) ?_ ?_ ?_ ?_
      · intro I hI
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI ⊢
        rcases hI with ⟨hl, hp, hi⟩
        refine ⟨?_, ?_, ?_⟩
        · intro v hv k hvk
          rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
          exact hl w hw k (by dsimp only [sw]; rw [← hvk, e.apply_symm_apply])
        · intro j
          simp only [Finset.mem_image]
          rw [← hp j]
          constructor
          · rintro ⟨w, hw, hwj⟩
            have hwEq : w = pin j := by dsimp only [pin]; rw [← hwj, e.apply_symm_apply]
            exact hwEq ▸ hw
          · intro hj; exact ⟨pin j, hj, by simp [pin]⟩
        · intro u hu v hv hvI
          rcases Finset.mem_image.mp hu with ⟨w1, hw1, rfl⟩
          rcases Finset.mem_image.mp hvI with ⟨w2, hw2, hw2eq⟩
          simp only [Gv, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          have hmem : w2 ∈ G w1 := by simp [G, hw2eq, hv]
          exact hi w1 hw1 w2 hmem hw2
      · intro J hJ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
        rcases hJ with ⟨hl, hp, hi⟩
        refine ⟨?_, ?_, ?_⟩
        · intro v hv k hvk
          rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
          exact hl w hw k (e.injective hvk)
        · intro j
          simp only [Finset.mem_image]
          rw [← hp j]
          constructor
          · rintro ⟨w, hw, hwj⟩; exact (e.injective hwj) ▸ hw
          · intro hj; exact ⟨.base (.pin j), hj, rfl⟩
        · intro u hu v hv hvI
          rcases Finset.mem_image.mp hu with ⟨w1, hw1, rfl⟩
          rcases Finset.mem_image.mp hvI with ⟨w2, hw2, rfl⟩
          simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at hv
          exact hi w1 hw1 w2 (by simp [Gv, hv]) hw2
      · intro I _
        ext w; simp only [Finset.mem_image]
        constructor
        · rintro ⟨a, ⟨w', hw', rfl⟩, rfl⟩; simpa using hw'
        · intro hw; exact ⟨e.symm w, ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩
      · intro J _
        ext w; simp only [Finset.mem_image]
        constructor
        · rintro ⟨a, ⟨w', hw', rfl⟩, rfl⟩; simpa using hw'
        · intro hw; exact ⟨e w, ⟨w, hw, rfl⟩, e.symm_apply_apply w⟩
    rw [hcount_eq, card_fibers_prod hb pat hHcard f x]
    let B0 := (Finset.univ : Finset (Finset (BaseV n t b))).filter (fun I0 =>
      (∀ v ∈ I0, ∀ s : Fin t, v = .sw s →
        (f ((slotEquiv m b hb).symm s).1).val.testBit ((slotEquiv m b hb).symm s).2.val = true) ∧
      (∀ j, BaseV.pin j ∈ I0 ↔ x j = true) ∧
      ∀ u ∈ I0, ∀ v ∈ I0, baseAdj hb pat u v = false)
    have hsum1 := sum_mod_congr B0
      (fun I0 => ∏ c : ClauseId n t, if (∃ u ∈ clauseBase c, u ∈ I0) then 1 else M)
      (fun I0 => if ∀ c : ClauseId n t, ∃ u ∈ clauseBase c, u ∈ I0 then 1 else 0)
      M (fun I0 _ => prod_clause_mod M (fun c => ∃ u ∈ clauseBase c, u ∈ I0))
    rw [hsum1]
    have hsum_card : (∑ I0 ∈ B0, if ∀ c : ClauseId n t, ∃ u ∈ clauseBase c, u ∈ I0 then 1 else 0) =
        ((Finset.univ : Finset (Finset (BaseV n t b))).filter (fun I0 =>
          ((∀ v ∈ I0, ∀ s : Fin t, v = .sw s →
            (f ((slotEquiv m b hb).symm s).1).val.testBit ((slotEquiv m b hb).symm s).2.val = true) ∧
            (∀ j, BaseV.pin j ∈ I0 ↔ x j = true) ∧
            ∀ u ∈ I0, ∀ v ∈ I0, baseAdj hb pat u v = false) ∧
          ∀ c : ClauseId n t, ∃ u ∈ clauseBase c, u ∈ I0)).card := by
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1; ext I0
      simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsum_card, base_good_count hb hM (lt_two_pow_log2_succ M (by omega)) pat f x]

private lemma card_filter_congr_inst {α : Type*} {s : Finset α} {P Q : α → Prop}
    {d1 : DecidablePred P} {d2 : DecidablePred Q} (h : ∀ x ∈ s, P x ↔ Q x) :
    (@Finset.filter α P d1 s).card = (@Finset.filter α Q d2 s).card := by
  congr 1; ext x; simp only [Finset.mem_filter]; exact and_congr_right (h x)

private lemma sum_filter_congr_inst {α : Type*} {s : Finset α} {P Q : α → Prop}
    {d1 : DecidablePred P} {d2 : DecidablePred Q} (g : α → ℕ) (h : ∀ x ∈ s, P x ↔ Q x) :
    (@Finset.filter α P d1 s).sum g = (@Finset.filter α Q d2 s).sum g := by
  congr 1; ext x; simp only [Finset.mem_filter]; exact and_congr_right (h x)

private lemma main_aux :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (M n m : Nat), 2 ≤ M →
      let b := Nat.log2 M + 1
      let t := m*b
      ∀ (pat : Fin m → Fin n → Option Bool),
        ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (pin : Fin n → Fin N)
          (sw : Fin m × Fin b → Fin N),
          N ≤ (2+2*b)*(n+t+1)+t+2*b*(t+2)+b ∧
          Function.Injective pin ∧ Function.Injective sw ∧
          (∀ j k, pin j ≠ sw k) ∧ (∀ v, v ∉ G v) ∧
          (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
          (∃ (h : Nat) (bag : Fin h → Finset (Fin N)),
            (∀ i, (bag i).card ≤ 2*n+3*b+5) ∧ (∀ i j, pin j ∈ bag i) ∧
            (∀ v, ∃ i, v ∈ bag i) ∧
            (∀ u v, v ∈ G u → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
            ∀ v i j k, i ≤ j → j ≤ k → v ∈ bag i → v ∈ bag k → v ∈ bag j) ∧
          ∀ (f : Fin m → Fin M) (x : Fin n → Bool),
            let live := fun v => ∀ k, v = sw k → (f k.1).val.testBit k.2.val = true
            let count := ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
              (∀ v ∈ I, live v) ∧ (∀ j, pin j ∈ I ↔ x j = true) ∧
              ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card
            count % M = (((Finset.univ : Finset (Fin m)).filter
              (fun i => ∀ j, (pat i j).elim true (fun v => decide (v = x j)) = true)).sum
              (fun i => (f i).val)) % M := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro M n m hM b t pat
  rcases main_aux_core M n m hM pat with
    ⟨N, G, pin, sw, hN, hpi, hsi, hps, hloop, hsym, hbag, hcnt⟩
  refine ⟨N, G, pin, sw, hN, hpi, hsi, hps, hloop, hsym, hbag, ?_⟩
  intro f x live count
  have h0 := hcnt f x
  dsimp only at h0
  refine (congrArg (· % M) (card_filter_congr_inst (fun _ _ => Iff.rfl))).trans (h0.trans (congrArg (· % M) ?_))
  apply sum_filter_congr_inst
  intro i _
  constructor <;> intro h j <;> have hj := h j <;> cases hp : pat i j with
  | none => simp [hp]
  | some v =>
    simp only [hp, Option.elim_some] at hj ⊢
    have hd : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
      fun P d1 d2 => by rw [Subsingleton.elim d1 d2]
    exact (hd (v = x j) _ _).symm.trans hj

end PEqualNP.Outside.L_lib_1234_aux

theorem PEqualNP.Outside.L_lib_1234 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (M n m : Nat), 2 ≤ M →
      let b := Nat.log2 M + 1
      let t := m*b
      ∀ (pat : Fin m → Fin n → Option Bool),
        ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (pin : Fin n → Fin N)
          (sw : Fin m × Fin b → Fin N),
          N ≤ (2+2*b)*(n+t+1)+t+2*b*(t+2)+b ∧
          Function.Injective pin ∧ Function.Injective sw ∧
          (∀ j k, pin j ≠ sw k) ∧ (∀ v, v ∉ G v) ∧
          (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
          (∃ (h : Nat) (bag : Fin h → Finset (Fin N)),
            (∀ i, (bag i).card ≤ 2*n+3*b+5) ∧ (∀ i j, pin j ∈ bag i) ∧
            (∀ v, ∃ i, v ∈ bag i) ∧
            (∀ u v, v ∈ G u → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
            ∀ v i j k, i ≤ j → j ≤ k → v ∈ bag i → v ∈ bag k → v ∈ bag j) ∧
          ∀ (f : Fin m → Fin M) (x : Fin n → Bool),
            let live := fun v => ∀ k, v = sw k → (f k.1).val.testBit k.2.val = true
            let count := ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
              (∀ v ∈ I, live v) ∧ (∀ j, pin j ∈ I ↔ x j = true) ∧
              ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card
            count % M = (((Finset.univ : Finset (Fin m)).filter
              (fun i => ∀ j, (pat i j).elim true (fun v => decide (v = x j)) = true)).sum
              (fun i => (f i).val)) % M := by
  exact PEqualNP.Outside.L_lib_1234_aux.main_aux
