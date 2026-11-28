import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1235_aux

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
-- Part 6: No-bag wrapper around the weighted pinned-assignment gadget
-- =========================================================================

private lemma gadget_1234 (M n m : ℕ) (hM : 2 ≤ M)
    (pat : Fin m → Fin n → Option Bool) :
    let b := Nat.log2 M + 1
    let t := m * b
    ∃ (N : ℕ) (G : Fin N → Finset (Fin N)) (pin : Fin n → Fin N)
      (sw : Fin m × Fin b → Fin N),
      N ≤ (2 + 2 * b) * (n + t + 1) + t + 2 * b * (t + 2) + b ∧
      Function.Injective pin ∧ Function.Injective sw ∧
      (∀ j k, pin j ≠ sw k) ∧ (∀ v, v ∉ G v) ∧
      (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
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
  refine ⟨N, G, pin, sw, hNle, hpin_inj, hsw_inj, hpin_sw, hloop, hsym, ?_⟩
  intro f x live count
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

-- =========================================================================
-- Part 7: Character orthogonality over (Key -> ZMod (base + 2))
-- =========================================================================

private noncomputable def zetaM (base : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I / ((base + 2 : ℕ) : ℂ))

private noncomputable def chiM (base : ℕ) (x : ZMod (base + 2)) : ℂ :=
  (zetaM base) ^ x.val

private lemma zetaM_pow (base : ℕ) : (zetaM base) ^ (base + 2) = 1 := by
  unfold zetaM
  rw [← Complex.exp_nat_mul]
  have hMne : ((base + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have harg : ((base + 2 : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I / ((base + 2 : ℕ) : ℂ)) =
      2 * ↑Real.pi * Complex.I := by
    field_simp [hMne]
  rw [harg]
  exact Complex.exp_two_pi_mul_I

private lemma zetaM_pow_mod (base n : ℕ) :
    (zetaM base) ^ (n % (base + 2)) = (zetaM base) ^ n := by
  have hdiv : n = (base + 2) * (n / (base + 2)) + n % (base + 2) :=
    (Nat.div_add_mod n (base + 2)).symm
  conv_rhs => rw [hdiv, pow_add, pow_mul, zetaM_pow, one_pow, one_mul]

private lemma chiM_zero (base : ℕ) : chiM base 0 = 1 := by
  unfold chiM
  simp

private lemma chiM_add (base : ℕ) (x y : ZMod (base + 2)) :
    chiM base (x + y) = chiM base x * chiM base y := by
  unfold chiM
  rw [ZMod.val_add, zetaM_pow_mod, pow_add]

private lemma chiM_sum {ι : Type*} (base : ℕ) (s : Finset ι) (u : ι → ZMod (base + 2)) :
    chiM base (∑ i ∈ s, u i) = ∏ i ∈ s, chiM base (u i) := by
  induction s using Finset.cons_induction with
  | empty => simp [chiM_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, chiM_add, ih]

private lemma chiM_ne_one (base : ℕ) {x : ZMod (base + 2)} (hx : x ≠ 0) :
    chiM base x ≠ 1 := by
  have hval_pos : 0 < x.val := by
    by_contra h0
    have hv : x.val = 0 := by omega
    exact hx (by rw [← ZMod.natCast_zmod_val x, hv]; simp)
  have hval_lt : x.val < base + 2 := ZMod.val_lt x
  unfold chiM zetaM
  rw [← Complex.exp_nat_mul]
  intro h1
  rw [Complex.exp_eq_one_iff] at h1
  rcases h1 with ⟨k, hk⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hMne : ((base + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hEq : (x.val : ℂ) / ((base + 2 : ℕ) : ℂ) = (k : ℂ) := by
    have h2 : ((x.val : ℂ) / ((base + 2 : ℕ) : ℂ)) * (2 * ↑Real.pi * Complex.I) =
        (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      calc ((x.val : ℂ) / ((base + 2 : ℕ) : ℂ)) * (2 * ↑Real.pi * Complex.I)
          = (x.val : ℂ) * (2 * ↑Real.pi * Complex.I / ((base + 2 : ℕ) : ℂ)) := by ring
        _ = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := hk
    exact mul_right_cancel₀ hpi h2
  have hEq2 : (x.val : ℂ) = (k : ℂ) * ((base + 2 : ℕ) : ℂ) := (div_eq_iff hMne).mp hEq
  have hEqZ : ((x.val : ℤ) : ℂ) = ((k * ((base + 2 : ℕ) : ℤ) : ℤ) : ℂ) := by
    simpa [Int.cast_mul, Int.cast_natCast] using hEq2
  have hInt : (x.val : ℤ) = k * ((base + 2 : ℕ) : ℤ) := Int.cast_injective hEqZ
  have h1' : (0 : ℤ) < (x.val : ℤ) := Int.natCast_pos.mpr hval_pos
  have h2' : (x.val : ℤ) < ((base + 2 : ℕ) : ℤ) := Int.ofNat_lt.mpr hval_lt
  rcases le_or_gt k 0 with hle | hgt <;> nlinarith

private lemma sum_chiM_mul (base : ℕ) (c : ZMod (base + 2)) :
    (∑ t : ZMod (base + 2), chiM base (c * t)) = if c = 0 then ((base + 2 : ℕ) : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, chiM_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one, ↓reduceIte]
  · rw [if_neg hc]
    have hshift : chiM base c * (∑ t : ZMod (base + 2), chiM base (c * t)) =
        ∑ t : ZMod (base + 2), chiM base (c * t) := by
      rw [Finset.mul_sum]
      have hrew : (∑ t : ZMod (base + 2), chiM base c * chiM base (c * t)) =
          ∑ t : ZMod (base + 2), chiM base (c * (t + 1)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← chiM_add]
        congr 1; ring
      rw [hrew]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod (base + 2))) (fun t => chiM base (c * t))
    have hzero : (chiM base c - 1) * (∑ t : ZMod (base + 2), chiM base (c * t)) = 0 := by
      linear_combination hshift
    have hne : chiM base c - 1 ≠ 0 := sub_ne_zero.mpr (chiM_ne_one base hc)
    exact (mul_eq_zero.mp hzero).resolve_left hne

private lemma subgroup_perp_card {Key : Type*} [Fintype Key] [DecidableEq Key]
    (base : ℕ) (H : AddSubgroup (Key → ZMod (base + 2))) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    Nat.card ↥H *
      ((Finset.univ : Finset (Key → ZMod (base + 2))).filter
        (fun g => ∀ d ∈ H, (∑ K : Key, d K * g K) = 0)).card =
      (base + 2) ^ (Fintype.card Key) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  set Hfin : Finset (Key → ZMod (base + 2)) := Finset.univ.filter (fun d => d ∈ H)
  set Hperp : Finset (Key → ZMod (base + 2)) :=
    Finset.univ.filter (fun g => ∀ d ∈ H, (∑ K : Key, d K * g K) = 0)
  have hHcard : Nat.card ↥H = Hfin.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hHcard]
  have hway1 :
      (∑ d ∈ Hfin, ∑ g : Key → ZMod (base + 2), chiM base (∑ K : Key, d K * g K)) =
        (((base + 2 : ℕ) ^ Fintype.card Key : ℕ) : ℂ) := by
    have hinner : ∀ d : Key → ZMod (base + 2),
        (∑ g : Key → ZMod (base + 2), chiM base (∑ K : Key, d K * g K)) =
          if d = 0 then (((base + 2 : ℕ) ^ Fintype.card Key : ℕ) : ℂ) else 0 := by
      intro d
      have hprod : (∑ g : Key → ZMod (base + 2), chiM base (∑ K : Key, d K * g K)) =
          ∏ K : Key, ∑ t : ZMod (base + 2), chiM base (d K * t) := by
        calc (∑ g : Key → ZMod (base + 2), chiM base (∑ K : Key, d K * g K))
            = ∑ g : Key → ZMod (base + 2), ∏ K : Key, chiM base (d K * g K) := by
                apply Finset.sum_congr rfl; intro g _; exact chiM_sum base Finset.univ _
          _ = ∏ K : Key, ∑ t : ZMod (base + 2), chiM base (d K * t) :=
                (Fintype.prod_sum (fun K t => chiM base (d K * t))).symm
      rw [hprod]
      by_cases hd : d = 0
      · subst hd
        rw [if_pos rfl]
        have hfac : ∀ K : Key, (∑ t : ZMod (base + 2), chiM base ((0 : Key → ZMod (base + 2)) K * t)) =
            ((base + 2 : ℕ) : ℂ) := by
          intro K; simpa using sum_chiM_mul base 0
        simp only [hfac, Finset.prod_const, Finset.card_univ, Nat.cast_pow]
      · rw [if_neg hd]
        have hex : ∃ K0 : Key, d K0 ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hd (funext hall)
        rcases hex with ⟨K0, hK0⟩
        apply Finset.prod_eq_zero (Finset.mem_univ K0)
        rw [sum_chiM_mul, if_neg hK0]
    have hsum : (∑ d ∈ Hfin, ∑ g : Key → ZMod (base + 2), chiM base (∑ K : Key, d K * g K)) =
        ∑ d ∈ Hfin, if d = 0 then (((base + 2 : ℕ) ^ Fintype.card Key : ℕ) : ℂ) else 0 :=
      Finset.sum_congr rfl (fun d _ => hinner d)
    rw [hsum, Finset.sum_ite_eq']
    have h0mem : (0 : Key → ZMod (base + 2)) ∈ Hfin := by
      simp [Hfin, H.zero_mem]
    rw [if_pos h0mem]
  have hway2 :
      (∑ d ∈ Hfin, ∑ g : Key → ZMod (base + 2), chiM base (∑ K : Key, d K * g K)) =
        ((Hfin.card * Hperp.card : ℕ) : ℂ) := by
    rw [Finset.sum_comm]
    have hinner : ∀ g : Key → ZMod (base + 2),
        (∑ d ∈ Hfin, chiM base (∑ K : Key, d K * g K)) =
          if g ∈ Hperp then (Hfin.card : ℂ) else 0 := by
      intro g
      by_cases hg : g ∈ Hperp
      · rw [if_pos hg]
        simp only [Hperp, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        have hall : ∀ d ∈ Hfin, chiM base (∑ K : Key, d K * g K) = 1 := by
          intro d hd
          simp only [Hfin, Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [hg d hd, chiM_zero]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
      · rw [if_neg hg]
        simp only [Hperp, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        push Not at hg
        rcases hg with ⟨d0, hd0H, hd0ne⟩
        set w := chiM base (∑ K : Key, d0 K * g K)
        have hwne : w ≠ 1 := chiM_ne_one base hd0ne
        have hshift : w * (∑ d ∈ Hfin, chiM base (∑ K : Key, d K * g K)) =
            ∑ d ∈ Hfin, chiM base (∑ K : Key, d K * g K) := by
          rw [Finset.mul_sum]
          have hrew : (∑ d ∈ Hfin, w * chiM base (∑ K : Key, d K * g K)) =
              ∑ d ∈ Hfin, chiM base (∑ K : Key, (d0 + d) K * g K) := by
            apply Finset.sum_congr rfl
            intro d _
            dsimp only [w]
            rw [← chiM_add, ← Finset.sum_add_distrib]
            congr 1; apply Finset.sum_congr rfl; intro K _
            simp only [Pi.add_apply]; ring
          rw [hrew]
          refine Finset.sum_bij' (fun d _ => d0 + d) (fun d _ => -d0 + d) ?_ ?_ ?_ ?_ ?_
          · intro d hd
            simp only [Hfin, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
            exact H.add_mem hd0H hd
          · intro d hd
            simp only [Hfin, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
            exact H.add_mem (H.neg_mem hd0H) hd
          · intro d _; abel
          · intro d _; abel
          · intro d _; rfl
        have hzero : (w - 1) * (∑ d ∈ Hfin, chiM base (∑ K : Key, d K * g K)) = 0 := by
          linear_combination hshift
        exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hwne)
    calc (∑ g : Key → ZMod (base + 2), ∑ d ∈ Hfin, chiM base (∑ K : Key, d K * g K))
        = ∑ g : Key → ZMod (base + 2), if g ∈ Hperp then (Hfin.card : ℂ) else 0 :=
            Finset.sum_congr rfl (fun g _ => hinner g)
      _ = ∑ _g ∈ Hperp, (Hfin.card : ℂ) := by
            rw [← Finset.sum_filter]; congr 1; ext g; simp
      _ = ((Hfin.card * Hperp.card : ℕ) : ℂ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul, mul_comm]
  have hcast : ((Hfin.card * Hperp.card : ℕ) : ℂ) = (((base + 2 : ℕ) ^ Fintype.card Key : ℕ) : ℂ) :=
    hway2.symm.trans hway1
  exact Nat.cast_injective hcast

-- =========================================================================
-- Part 8: Main proof for L-lib-1235
-- =========================================================================

private lemma zmod_natCast_mod (a M : ℕ) : (((a % M : ℕ) : ZMod M)) = (a : ZMod M) := by
  have h : a = M * (a / M) + a % M := (Nat.div_add_mod a M).symm
  conv_rhs => rw [h]
  push_cast
  simp [ZMod.natCast_self]

private lemma card_filter_congr_inst {α : Type*} {s : Finset α} {P Q : α → Prop}
    {d1 : DecidablePred P} {d2 : DecidablePred Q} (h : ∀ x ∈ s, P x ↔ Q x) :
    (@Finset.filter α P d1 s).card = (@Finset.filter α Q d2 s).card := by
  congr 1; ext x; simp only [Finset.mem_filter]; exact and_congr_right (h x)

private lemma sum_filter_congr_inst {α : Type*} {s : Finset α} {P Q : α → Prop}
    {d1 : DecidablePred P} {d2 : DecidablePred Q} (g : α → ℕ) (h : ∀ x ∈ s, P x ↔ Q x) :
    (@Finset.filter α P d1 s).sum g = (@Finset.filter α Q d2 s).sum g := by
  congr 1; ext x; simp only [Finset.mem_filter]; exact and_congr_right (h x)

private lemma upper_bound_part (base l r : ℕ) (C : Fin l → Finset (Fin r)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let family := (Finset.univ : Finset (Finset (Fin l))).image (fun S => S.biUnion C)
    let Key := ↥family
    let Table := Key → ZMod (base + 2)
    let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
      (p : Fin l → Fin N) (s : Fin r → Fin N) =>
      Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
      (∀ j, side (s j) = true) ∧ (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
      ∀ u v, side u = false → side v = true →
        (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
    let value := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
      ((((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card : Nat) : ZMod (base + 2))
    ∀ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
      (p : Fin l → Fin N) (s : Fin r → Fin N), fits N G side p s →
      ∃ (send : (Fin N → Bool) → Table) (recv : Table → (Fin N → Bool) → ZMod (base + 2)),
        ∀ a d, recv (send a) d = value N G (fun v => if side v then d v else a v) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro family Key Table fits value N G side p s hfits
  rcases hfits with ⟨hpinj, hsinj, hpL, hsR, hloop, hsym, hcross⟩
  let leftKey : Finset (Fin N) → Key := fun I =>
    ⟨((Finset.univ : Finset (Fin l)).filter (fun i => p i ∈ I)).biUnion C,
      Finset.mem_image.mpr ⟨Finset.univ.filter (fun i => p i ∈ I), Finset.mem_univ _, rfl⟩⟩
  let leftSets : (Fin N → Bool) → Key → Finset (Finset (Fin N)) := fun a K =>
    Finset.univ.filter (fun IL =>
      (∀ v ∈ IL, side v = false ∧ a v = true) ∧
      (∀ u ∈ IL, ∀ v ∈ G u, v ∉ IL) ∧
      leftKey IL = K)
  let rightSets : (Fin N → Bool) → Key → Finset (Finset (Fin N)) := fun d K =>
    Finset.univ.filter (fun IR =>
      (∀ v ∈ IR, side v = true ∧ d v = true) ∧
      (∀ u ∈ IR, ∀ v ∈ G u, v ∉ IR) ∧
      (∀ j ∈ K.val, s j ∉ IR))
  let send : (Fin N → Bool) → Table := fun a K => ((leftSets a K).card : ZMod (base + 2))
  let recv : Table → (Fin N → Bool) → ZMod (base + 2) := fun msg d =>
    ∑ K : Key, msg K * ((rightSets d K).card : ZMod (base + 2))
  refine ⟨send, recv, ?_⟩
  intro a d
  dsimp only [send, recv, value]
  have hmul_sum : (∑ K : Key, ((leftSets a K).card : ZMod (base + 2)) * ((rightSets d K).card : ZMod (base + 2))) =
      ((∑ K : Key, (leftSets a K).card * (rightSets d K).card : ℕ) : ZMod (base + 2)) := by
    push_cast; rfl
  rw [hmul_sum]
  congr 1
  let live := fun v => if side v then d v else a v
  let All := (Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
    (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)
  have hcard : All.card = ∑ K : Key, (leftSets a K).card * (rightSets d K).card := by
    have hsig : ((Finset.univ : Finset Key).sigma (fun K => leftSets a K ×ˢ rightSets d K)).card =
        ∑ K : Key, (leftSets a K).card * (rightSets d K).card := by
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro K _
      exact Finset.card_product _ _
    rw [← hsig]
    refine Finset.card_bij'
      (fun I _ => ⟨leftKey (I.filter (fun v => side v = false)),
        (I.filter (fun v => side v = false), I.filter (fun v => side v = true))⟩)
      (fun z _ => z.2.1 ∪ z.2.2) ?_ ?_ ?_ ?_
    · intro I hI
      simp only [All, Finset.mem_filter, Finset.mem_univ, true_and] at hI
      rcases hI with ⟨hlive, hind⟩
      set IL := I.filter (fun v => side v = false)
      set IR := I.filter (fun v => side v = true)
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
        leftSets, rightSets, Finset.mem_filter]
      refine ⟨⟨?_, ?_, trivial⟩, ⟨?_, ?_, ?_⟩⟩
      · intro v hv
        simp only [IL, Finset.mem_filter] at hv
        refine ⟨hv.2, ?_⟩
        have hlv := hlive v hv.1
        dsimp only [live] at hlv
        rw [hv.2] at hlv; simpa using hlv
      · intro u hu v hv hvI
        simp only [IL, Finset.mem_filter] at hu hvI
        exact hind u hu.1 v hv hvI.1
      · intro v hv
        simp only [IR, Finset.mem_filter] at hv
        refine ⟨hv.2, ?_⟩
        have hlv := hlive v hv.1
        dsimp only [live] at hlv
        rw [hv.2] at hlv; simpa using hlv
      · intro u hu v hv hvI
        simp only [IR, Finset.mem_filter] at hu hvI
        exact hind u hu.1 v hv hvI.1
      · intro j hj hsj
        simp only [IR, Finset.mem_filter] at hsj
        simp only [leftKey, IL, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rcases hj with ⟨i, hi, hjC⟩
        have hedge : s j ∈ G (p i) := (hcross (p i) (s j) (hpL i) (hsR j)).mpr ⟨i, j, rfl, rfl, hjC⟩
        exact hind (p i) hi.1 (s j) hedge hsj.1
    · intro z hz
      rcases z with ⟨K, ⟨IL, IR⟩⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
        leftSets, rightSets, Finset.mem_filter] at hz
      rcases hz with ⟨⟨hLside, hLind, hLkey⟩, ⟨hRside, hRind, hRforb⟩⟩
      simp only [All, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with hvL | hvR
        · have ⟨hs, ha⟩ := hLside v hvL
          dsimp only [live]; rw [hs]; simpa using ha
        · have ⟨hs, hd⟩ := hRside v hvR
          dsimp only [live]; rw [hs]; simpa using hd
      · intro u hu v hv hvU
        rcases Finset.mem_union.mp hu with huL | huR <;>
          rcases Finset.mem_union.mp hvU with hvL | hvR
        · exact hLind u huL v hv hvL
        · have hcr := (hcross u v (hLside u huL).1 (hRside v hvR).1).mp hv
          rcases hcr with ⟨i, j, rfl, rfl, hjC⟩
          have hjK : j ∈ K.val := by
            rw [← hLkey]
            exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huL⟩, hjC⟩
          exact hRforb j hjK hvR
        · have hcr := (hcross v u (hLside v hvL).1 (hRside u huR).1).mp ((hsym u v).mp hv)
          rcases hcr with ⟨i, j, rfl, rfl, hjC⟩
          have hjK : j ∈ K.val := by
            rw [← hLkey]
            exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvL⟩, hjC⟩
          exact hRforb j hjK huR
        · exact hRind u huR v hv hvR
    · intro I _
      ext v
      simp only [Finset.mem_union, Finset.mem_filter]
      cases hsv : side v <;> simp
    · intro z hz
      rcases z with ⟨K, ⟨IL, IR⟩⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
        leftSets, rightSets, Finset.mem_filter] at hz
      rcases hz with ⟨⟨hLside, _, hLkey⟩, ⟨hRside, _, _⟩⟩
      have hIL : (IL ∪ IR).filter (fun v => side v = false) = IL := by
        ext v; simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hv | hv, hs⟩
          · exact hv
          · exfalso; have := (hRside v hv).1; rw [hs] at this; cases this
        · intro hv; exact ⟨Or.inl hv, (hLside v hv).1⟩
      have hIR : (IL ∪ IR).filter (fun v => side v = true) = IR := by
        ext v; simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hv | hv, hs⟩
          · exfalso; have := (hLside v hv).1; rw [hs] at this; cases this
          · exact hv
        · intro hv; exact ⟨Or.inr hv, (hRside v hv).1⟩
      apply Sigma.ext
      · rw [hIL]; exact hLkey
      · apply heq_of_eq
        exact Prod.ext hIL hIR
  exact hcard.symm

private lemma nat_sub_lt_sub {a b r : ℕ} (hab : a < b) (hbr : b ≤ r) : r - b < r - a := by
  omega

private lemma phi_bijective {r : ℕ} {family : Finset (Finset (Fin r))} (base : ℕ) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let Key := ↥family
    let Table := Key → ZMod (base + 2)
    Function.Bijective (fun (g : Table) (K1 : Key) =>
      ∑ K2 : Key, if K1.val ⊆ K2.val then g K2 else 0) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro Key Table
  let phi : Table → Table := fun g K1 => ∑ K2 : Key, if K1.val ⊆ K2.val then g K2 else 0
  have hlin : ∀ g1 g2, phi (g1 - g2) = phi g1 - phi g2 := by
    intro g1 g2; funext K1
    change (∑ K2 : Key, if K1.val ⊆ K2.val then (g1 - g2) K2 else 0) =
      (∑ K2 : Key, if K1.val ⊆ K2.val then g1 K2 else 0) -
        (∑ K2 : Key, if K1.val ⊆ K2.val then g2 K2 else 0)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro K2 _
    split_ifs
    · rfl
    · exact (sub_self 0).symm
  have hker : ∀ g : Table, phi g = 0 → g = 0 := by
    intro g hg
    have hstrong : ∀ k : ℕ, ∀ K : Key, r - K.val.card = k → g K = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro K hK
        have h0 : phi g K = 0 := by rw [hg]; rfl
        dsimp only [phi] at h0
        have hsingle : (∑ K2 : Key, if K.val ⊆ K2.val then g K2 else 0) = g K := by
          rw [Finset.sum_eq_single K]
          · simp
          · intro K2 _ hne
            split_ifs with hsub
            · have hssub : K.val ⊂ K2.val :=
                ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne (Subtype.ext heq.symm)⟩
              have hlt : K.val.card < K2.val.card := Finset.card_lt_card hssub
              have hle : K2.val.card ≤ r := by
                simpa [Fintype.card_fin] using Finset.card_le_univ K2.val
              exact ih (r - K2.val.card) (hK ▸ nat_sub_lt_sub hlt hle) K2 rfl
            · rfl
          · intro hni; exact absurd (Finset.mem_univ K) hni
        rw [hsingle] at h0
        exact h0
    funext K
    exact hstrong (r - K.val.card) K rfl
  have hinj : Function.Injective phi := by
    intro g1 g2 h
    have hsub : phi (g1 - g2) = 0 := by rw [hlin, h, sub_self]
    exact sub_eq_zero.mp (hker (g1 - g2) hsub)
  exact Finite.injective_iff_bijective.mp hinj

private lemma lower_bound_part (base l r : ℕ) (C : Fin l → Finset (Fin r)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let M := base + 2
    let b := Nat.log2 M + 1
    let family := (Finset.univ : Finset (Finset (Fin l))).image (fun S => S.biUnion C)
    let Key := ↥family
    let q := family.card
    let Table := Key → ZMod (base + 2)
    let budget := fun n => (2 + 2 * b) * (n + q * b + 1) + q * b + 2 * b * (q * b + 2) + b
    let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
      (p : Fin l → Fin N) (s : Fin r → Fin N) =>
      Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
      (∀ j, side (s j) = true) ∧ (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
      ∀ u v, side u = false → side v = true →
        (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
    let value := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
      ((((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card : Nat) : ZMod (base + 2))
    ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
      (p : Fin l → Fin N) (s : Fin r → Fin N) (tag : Fin N → Option (Key × Fin b)),
      fits N G side p s ∧ N ≤ budget l + budget r ∧
      (∀ i, tag (p i) = none) ∧ (∀ j, tag (s j) = none) ∧
      let out := fun (f g : Table) => value N G (fun v =>
        (tag v).elim true (fun k => (((if side v then g else f) k.1).val.testBit k.2.val)))
      (∀ f g, out f g = (Finset.univ : Finset (Key × Key)).sum (fun z =>
        if z.1.val ⊆ z.2.val then f z.1 * g z.2 else 0)) ∧
      ∀ (A : Finset Table) (a : Table), a ∈ A →
        let H := AddSubgroup.closure {d : Table | ∃ f ∈ A, d = f - a}
        let cols := (Finset.univ : Finset Table).filter (fun g => ∀ f ∈ A, out f g = out a g)
        Nat.card ↥H * cols.card = M ^ q := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro M b family Key q Table budget fits value
  have hM : 2 ≤ M := Nat.le_add_left 2 base
  let eKey : Key ≃ Fin q := (Fintype.equivFin Key).trans (finCongr (Fintype.card_coe family))
  let rep : Key → Finset (Fin l) := fun K =>
    Classical.choose (Finset.mem_image.mp K.property)
  have hrep : ∀ K : Key, (rep K).biUnion C = K.val := fun K =>
    (Classical.choose_spec (Finset.mem_image.mp K.property)).2
  have hrep_inj : Function.Injective rep := by
    intro K1 K2 h
    apply Subtype.ext
    rw [← hrep K1, ← hrep K2, h]
  let patL : Fin q → Fin l → Option Bool := fun idx i =>
    some (decide (i ∈ rep (eKey.symm idx)))
  let patR : Fin q → Fin r → Option Bool := fun idx j =>
    some (decide (j ∉ (eKey.symm idx).val))
  rcases gadget_1234 M l q hM patL with
    ⟨NL, GrL, pinL, swL, hNL, hpinL, hswL, hpsL, hloopL, hsymL, hcntL⟩
  rcases gadget_1234 M r q hM patR with
    ⟨NR, GrR, pinR, swR, hNR, hpinR, hswR, hpsR, hloopR, hsymR, hcntR⟩
  let N := NL + NR
  let eSum : Fin NL ⊕ Fin NR ≃ Fin N := finSumFinEquiv
  let side : Fin N → Bool := fun v =>
    match eSum.symm v with
    | .inl _ => false
    | .inr _ => true
  let p : Fin l → Fin N := fun i => eSum (.inl (pinL i))
  let s : Fin r → Fin N := fun j => eSum (.inr (pinR j))
  let adj : Fin N → Fin N → Prop := fun u v =>
    match eSum.symm u, eSum.symm v with
    | .inl uL, .inl vL => vL ∈ GrL uL
    | .inr uR, .inr vR => vR ∈ GrR uR
    | .inl uL, .inr vR => ∃ i j, uL = pinL i ∧ vR = pinR j ∧ j ∈ C i
    | .inr uR, .inl vL => ∃ i j, vL = pinL i ∧ uR = pinR j ∧ j ∈ C i
  let G : Fin N → Finset (Fin N) := fun u => Finset.univ.filter (fun v => adj u v)
  let tag : Fin N → Option (Key × Fin b) := fun v =>
    match eSum.symm v with
    | .inl uL =>
      if h : ∃ k : Fin q × Fin b, uL = swL k then
        let k := Classical.choose h
        some (eKey.symm k.1, k.2)
      else none
    | .inr uR =>
      if h : ∃ k : Fin q × Fin b, uR = swR k then
        let k := Classical.choose h
        some (eKey.symm k.1, k.2)
      else none
  have hfits : fits N G side p s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i1 i2 h
      have h1 := eSum.injective h
      injection h1 with h2
      exact hpinL h2
    · intro j1 j2 h
      have h1 := eSum.injective h
      injection h1 with h2
      exact hpinR h2
    · intro i; simp [side, p]
    · intro j; simp [side, s]
    · intro v hv
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj] at hv
      cases h : eSum.symm v with
      | inl uL => rw [h] at hv; exact hloopL uL hv
      | inr uR => rw [h] at hv; exact hloopR uR hv
    · intro u v
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj]
      cases hu : eSum.symm u <;> cases hv : eSum.symm v
      · exact hsymL _ _
      · rfl
      · rfl
      · exact hsymR _ _
    · intro u v hu hv
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj]
      cases hsu : eSum.symm u with
      | inr _ => simp [side, hsu] at hu
      | inl uL =>
        cases hsv : eSum.symm v with
        | inl _ => simp [side, hsv] at hv
        | inr vR =>
          constructor
          · rintro ⟨i, j, rfl, rfl, hjC⟩
            refine ⟨i, j, ?_, ?_, hjC⟩
            · dsimp only [p]; rw [← hsu, eSum.apply_symm_apply]
            · dsimp only [s]; rw [← hsv, eSum.apply_symm_apply]
          · rintro ⟨i, j, rfl, rfl, hjC⟩
            simp only [p, s, Equiv.symm_apply_apply] at hsu hsv
            injection hsu with huL
            injection hsv with hvR
            exact ⟨i, j, huL.symm, hvR.symm, hjC⟩
  have hNle : N ≤ budget l + budget r := Nat.add_le_add hNL hNR
  have htagP : ∀ i, tag (p i) = none := by
    intro i
    simp only [tag, p, Equiv.symm_apply_apply]
    rw [dif_neg]
    rintro ⟨k, hk⟩
    exact hpsL i k hk
  have htagS : ∀ j, tag (s j) = none := by
    intro j
    simp only [tag, s, Equiv.symm_apply_apply]
    rw [dif_neg]
    rintro ⟨k, hk⟩
    exact hpsR j k hk
  let out := fun (f g : Table) => value N G (fun v =>
    (tag v).elim true (fun k => (((if side v then g else f) k.1).val.testBit k.2.val)))
  have hout : ∀ f g, out f g = (Finset.univ : Finset (Key × Key)).sum (fun z =>
      if z.1.val ⊆ z.2.val then f z.1 * g z.2 else 0) := by
    intro f g
    let fFin : Fin q → Fin M := fun idx => ⟨(f (eKey.symm idx)).val, ZMod.val_lt _⟩
    let gFin : Fin q → Fin M := fun idx => ⟨(g (eKey.symm idx)).val, ZMod.val_lt _⟩
    let liveG : Fin N → Bool := fun v =>
      (tag v).elim true (fun k => (((if side v then g else f) k.1).val.testBit k.2.val))
    let liveL : Fin NL → Prop := fun uL =>
      ∀ k : Fin q × Fin b, uL = swL k → (fFin k.1).val.testBit k.2.val = true
    let liveR : Fin NR → Prop := fun uR =>
      ∀ k : Fin q × Fin b, uR = swR k → (gFin k.1).val.testBit k.2.val = true
    have hliveL_iff : ∀ uL : Fin NL, liveG (eSum (.inl uL)) = true ↔ liveL uL := by
      intro uL
      dsimp only [liveG, liveL, tag, side]
      simp only [Equiv.symm_apply_apply, Bool.false_eq_true, ↓reduceIte]
      by_cases h : ∃ k : Fin q × Fin b, uL = swL k
      · rw [dif_pos h]
        set k0 := Classical.choose h
        have hk0 : uL = swL k0 := Classical.choose_spec h
        simp only [Option.elim_some]
        constructor
        · intro hbit k hk
          have heq : k = k0 := hswL (hk.symm.trans hk0)
          subst heq; exact hbit
        · intro hall
          exact hall k0 hk0
      · rw [dif_neg h]
        simp only [Option.elim_none, true_iff]
        intro k hk
        exact absurd ⟨k, hk⟩ h
    have hliveR_iff : ∀ uR : Fin NR, liveG (eSum (.inr uR)) = true ↔ liveR uR := by
      intro uR
      dsimp only [liveG, liveR, tag, side]
      simp only [Equiv.symm_apply_apply, ↓reduceIte]
      by_cases h : ∃ k : Fin q × Fin b, uR = swR k
      · rw [dif_pos h]
        set k0 := Classical.choose h
        have hk0 : uR = swR k0 := Classical.choose_spec h
        simp only [Option.elim_some]
        constructor
        · intro hbit k hk
          have heq : k = k0 := hswR (hk.symm.trans hk0)
          subst heq; exact hbit
        · intro hall
          exact hall k0 hk0
      · rw [dif_neg h]
        simp only [Option.elim_none, true_iff]
        intro k hk
        exact absurd ⟨k, hk⟩ h
    let leftFiber : (Fin l → Bool) → Finset (Finset (Fin NL)) := fun x =>
      Finset.univ.filter (fun IL =>
        (∀ v ∈ IL, liveL v) ∧ (∀ i, pinL i ∈ IL ↔ x i = true) ∧
        ∀ u ∈ IL, ∀ v ∈ GrL u, v ∉ IL)
    let rightFiber : (Fin r → Bool) → Finset (Finset (Fin NR)) := fun y =>
      Finset.univ.filter (fun IR =>
        (∀ v ∈ IR, liveR v) ∧ (∀ j, pinR j ∈ IR ↔ y j = true) ∧
        ∀ u ∈ IR, ∀ v ∈ GrR u, v ∉ IR)
    let compat : (Fin l → Bool) → (Fin r → Bool) → Prop := fun x y =>
      ∀ i j, x i = true → y j = true → j ∉ C i
    let AllG := (Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, liveG v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)
    have hAllCard : AllG.card =
        ∑ xy ∈ (Finset.univ : Finset ((Fin l → Bool) × (Fin r → Bool))).filter (fun xy => compat xy.1 xy.2),
          (leftFiber xy.1).card * (rightFiber xy.2).card := by
      let Dom := ((Finset.univ : Finset ((Fin l → Bool) × (Fin r → Bool))).filter
        (fun xy => compat xy.1 xy.2)).sigma (fun xy => leftFiber xy.1 ×ˢ rightFiber xy.2)
      have hDom : Dom.card =
          ∑ xy ∈ (Finset.univ : Finset ((Fin l → Bool) × (Fin r → Bool))).filter (fun xy => compat xy.1 xy.2),
            (leftFiber xy.1).card * (rightFiber xy.2).card := by
        rw [Finset.card_sigma]
        apply Finset.sum_congr rfl
        intro xy _
        exact Finset.card_product _ _
      rw [← hDom]
      let toL : Finset (Fin N) → Finset (Fin NL) := fun I =>
        Finset.univ.filter (fun uL => eSum (.inl uL) ∈ I)
      let toR : Finset (Fin N) → Finset (Fin NR) := fun I =>
        Finset.univ.filter (fun uR => eSum (.inr uR) ∈ I)
      let fromLR : Finset (Fin NL) → Finset (Fin NR) → Finset (Fin N) := fun IL IR =>
        IL.image (fun uL => eSum (.inl uL)) ∪ IR.image (fun uR => eSum (.inr uR))
      refine Finset.card_bij'
        (fun I _ => ⟨(fun i => decide (pinL i ∈ toL I), fun j => decide (pinR j ∈ toR I)),
          (toL I, toR I)⟩)
        (fun z _ => fromLR z.2.1 z.2.2) ?_ ?_ ?_ ?_
      · intro I hI
        simp only [AllG, Finset.mem_filter, Finset.mem_univ, true_and] at hI
        rcases hI with ⟨hlive, hind⟩
        simp only [Dom, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, leftFiber, rightFiber]
        refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
        · intro i j hi hj hjC
          simp only [decide_eq_true_eq, toL, toR, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
          have hedge : eSum (.inr (pinR j)) ∈ G (eSum (.inl (pinL i))) := by
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply]
            exact ⟨i, j, rfl, rfl, hjC⟩
          exact hind _ hi _ hedge hj
        · intro uL huL
          simp only [toL, Finset.mem_filter, Finset.mem_univ, true_and] at huL
          exact (hliveL_iff uL).mp (hlive _ huL)
        · intro i; simp [decide_eq_true_eq]
        · intro uL huL vL hvL hvL'
          simp only [toL, Finset.mem_filter, Finset.mem_univ, true_and] at huL hvL'
          have hedge : eSum (.inl vL) ∈ G (eSum (.inl uL)) := by
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply]
            exact hvL
          exact hind _ huL _ hedge hvL'
        · intro uR huR
          simp only [toR, Finset.mem_filter, Finset.mem_univ, true_and] at huR
          exact (hliveR_iff uR).mp (hlive _ huR)
        · intro j; simp [decide_eq_true_eq]
        · intro uR huR vR hvR hvR'
          simp only [toR, Finset.mem_filter, Finset.mem_univ, true_and] at huR hvR'
          have hedge : eSum (.inr vR) ∈ G (eSum (.inr uR)) := by
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply]
            exact hvR
          exact hind _ huR _ hedge hvR'
      · intro z hz
        rcases z with ⟨⟨x, y⟩, ⟨IL, IR⟩⟩
        simp only [Dom, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, leftFiber, rightFiber] at hz
        rcases hz with ⟨hcmp, ⟨hLL, hLp, hLi⟩, ⟨hRL, hRp, hRi⟩⟩
        simp only [AllG, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases Finset.mem_union.mp hv with hvL | hvR
          · rcases Finset.mem_image.mp hvL with ⟨uL, huL, rfl⟩
            exact (hliveL_iff uL).mpr (hLL uL huL)
          · rcases Finset.mem_image.mp hvR with ⟨uR, huR, rfl⟩
            exact (hliveR_iff uR).mpr (hRL uR huR)
        · intro u hu v hv hvU
          rcases Finset.mem_union.mp hu with huL | huR <;>
            rcases Finset.mem_union.mp hvU with hvL | hvR
          · rcases Finset.mem_image.mp huL with ⟨uL, huL', rfl⟩
            rcases Finset.mem_image.mp hvL with ⟨vL, hvL', rfl⟩
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply] at hv
            exact hLi uL huL' vL hv hvL'
          · rcases Finset.mem_image.mp huL with ⟨uL, huL', rfl⟩
            rcases Finset.mem_image.mp hvR with ⟨vR, hvR', rfl⟩
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply] at hv
            rcases hv with ⟨i, j, rfl, rfl, hjC⟩
            exact hcmp i j ((hLp i).mp huL') ((hRp j).mp hvR') hjC
          · rcases Finset.mem_image.mp huR with ⟨uR, huR', rfl⟩
            rcases Finset.mem_image.mp hvL with ⟨vL, hvL', rfl⟩
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply] at hv
            rcases hv with ⟨i, j, rfl, rfl, hjC⟩
            exact hcmp i j ((hLp i).mp hvL') ((hRp j).mp huR') hjC
          · rcases Finset.mem_image.mp huR with ⟨uR, huR', rfl⟩
            rcases Finset.mem_image.mp hvR with ⟨vR, hvR', rfl⟩
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, adj, Equiv.symm_apply_apply] at hv
            exact hRi uR huR' vR hv hvR'
      · intro I _
        ext v
        simp only [fromLR, Finset.mem_union, Finset.mem_image, toL, toR, Finset.mem_filter,
          Finset.mem_univ, true_and]
        cases hv : eSum.symm v with
        | inl uL =>
          constructor
          · rintro (⟨a, ha, hae⟩ | ⟨a, _, hae⟩)
            · rw [← hae]; exact ha
            · have := eSum.injective (hae.trans (eSum.apply_symm_apply v).symm)
              rw [hv] at this; cases this
          · intro hvI
            left; refine ⟨uL, ?_, ?_⟩
            · rw [← hv, eSum.apply_symm_apply]; exact hvI
            · rw [← hv, eSum.apply_symm_apply]
        | inr uR =>
          constructor
          · rintro (⟨a, _, hae⟩ | ⟨a, ha, hae⟩)
            · have := eSum.injective (hae.trans (eSum.apply_symm_apply v).symm)
              rw [hv] at this; cases this
            · rw [← hae]; exact ha
          · intro hvI
            right; refine ⟨uR, ?_, ?_⟩
            · rw [← hv, eSum.apply_symm_apply]; exact hvI
            · rw [← hv, eSum.apply_symm_apply]
      · intro z hz
        rcases z with ⟨⟨x, y⟩, ⟨IL, IR⟩⟩
        simp only [Dom, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, leftFiber, rightFiber] at hz
        rcases hz with ⟨_, ⟨_, hLp, _⟩, ⟨_, hRp, _⟩⟩
        have hL : toL (fromLR IL IR) = IL := by
          ext uL
          simp only [toL, fromLR, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, Finset.mem_image]
          constructor
          · rintro (⟨a, ha, hae⟩ | ⟨a, _, hae⟩)
            · have h1 := eSum.injective hae; injection h1 with h2; subst h2; exact ha
            · have h1 := eSum.injective hae; cases h1
          · intro huL; exact Or.inl ⟨uL, huL, rfl⟩
        have hR : toR (fromLR IL IR) = IR := by
          ext uR
          simp only [toR, fromLR, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, Finset.mem_image]
          constructor
          · rintro (⟨a, _, hae⟩ | ⟨a, ha, hae⟩)
            · have h1 := eSum.injective hae; cases h1
            · have h1 := eSum.injective hae; injection h1 with h2; subst h2; exact ha
          · intro huR; exact Or.inr ⟨uR, huR, rfl⟩
        have hx : (fun i => decide (pinL i ∈ toL (fromLR IL IR))) = x := by
          funext i; rw [hL]
          cases hxi : x i
          · simp [(hLp i), hxi]
          · simp [(hLp i), hxi]
        have hy : (fun j => decide (pinR j ∈ toR (fromLR IL IR))) = y := by
          funext j; rw [hR]
          cases hyj : y j
          · simp [(hRp j), hyj]
          · simp [(hRp j), hyj]
        apply Sigma.ext
        · exact Prod.ext hx hy
        · apply heq_of_eq; exact Prod.ext hL hR
    let pinOfL : Key → (Fin l → Bool) := fun K1 i => decide (i ∈ rep K1)
    let pinOfR : Key → (Fin r → Bool) := fun K2 j => decide (j ∉ K2.val)
    have hpinOfL_inj : Function.Injective pinOfL := by
      intro K1 K2 h
      apply hrep_inj
      ext i
      have hi := congrFun h i
      dsimp only [pinOfL] at hi
      simpa [decide_eq_decide] using hi
    have hpinOfR_inj : Function.Injective pinOfR := by
      intro K1 K2 h
      apply Subtype.ext
      ext j
      have hj := congrFun h j
      dsimp only [pinOfR] at hj
      simpa [decide_eq_decide] using hj
    have hLval : ∀ x : Fin l → Bool,
        ((leftFiber x).card : ZMod (base + 2)) =
          if h : ∃ K1 : Key, x = pinOfL K1 then f (Classical.choose h) else 0 := by
      intro x
      have hmod := hcntL fFin x
      dsimp only at hmod
      have hcard_mod : (leftFiber x).card % M =
          ((Finset.univ : Finset (Fin q)).filter (fun idx => x = pinOfL (eKey.symm idx))).sum
            (fun idx => (fFin idx).val) % M := by
        refine (congrArg (· % M) (card_filter_congr_inst (fun _ _ => Iff.rfl))).trans
          (hmod.trans (congrArg (· % M) ?_))
        apply sum_filter_congr_inst
        intro idx _
        simp only [patL, Option.elim_some, pinOfL]
        constructor
        · intro h; funext i
          have hi := h i
          have hd : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
            fun P d1 d2 => by rw [Subsingleton.elim d1 d2]
          have h1 : decide (decide (i ∈ rep (eKey.symm idx)) = x i) = true :=
            (hd _ _ _).trans hi
          exact (of_decide_eq_true h1).symm
        · intro h i
          rw [h]
          have hd : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
            fun P d1 d2 => by rw [Subsingleton.elim d1 d2]
          exact (hd _ _ _).trans (decide_eq_true rfl)
      change ((leftFiber x).card : ZMod M) = _
      rw [← zmod_natCast_mod ((leftFiber x).card) M, hcard_mod, zmod_natCast_mod]
      by_cases hex : ∃ K1 : Key, x = pinOfL K1
      · rw [dif_pos hex]
        set K1 := Classical.choose hex
        have hK1 : x = pinOfL K1 := Classical.choose_spec hex
        have hsing : (Finset.univ : Finset (Fin q)).filter (fun idx => x = pinOfL (eKey.symm idx)) =
            {eKey K1} := by
          ext idx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hx
            have hKeq : K1 = eKey.symm idx := hpinOfL_inj (hK1.symm.trans hx)
            rw [hKeq, Equiv.apply_symm_apply]
          · intro hidx; subst hidx; rw [Equiv.symm_apply_apply]; exact hK1
        rw [hsing, Finset.sum_singleton]
        dsimp only [fFin]
        rw [Equiv.symm_apply_apply, ZMod.natCast_zmod_val]
      · rw [dif_neg hex]
        have hemp : (Finset.univ : Finset (Fin q)).filter (fun idx => x = pinOfL (eKey.symm idx)) = ∅ := by
          ext idx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hx; exact hex ⟨eKey.symm idx, hx⟩
        rw [hemp, Finset.sum_empty, Nat.cast_zero]
    have hRval : ∀ y : Fin r → Bool,
        ((rightFiber y).card : ZMod (base + 2)) =
          if h : ∃ K2 : Key, y = pinOfR K2 then g (Classical.choose h) else 0 := by
      intro y
      have hmod := hcntR gFin y
      dsimp only at hmod
      have hcard_mod : (rightFiber y).card % M =
          ((Finset.univ : Finset (Fin q)).filter (fun idx => y = pinOfR (eKey.symm idx))).sum
            (fun idx => (gFin idx).val) % M := by
        refine (congrArg (· % M) (card_filter_congr_inst (fun _ _ => Iff.rfl))).trans
          (hmod.trans (congrArg (· % M) ?_))
        apply sum_filter_congr_inst
        intro idx _
        simp only [patR, Option.elim_some, pinOfR]
        constructor
        · intro h; funext j
          have hj := h j
          have hd : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
            fun P d1 d2 => by rw [Subsingleton.elim d1 d2]
          have h1 : decide (decide (j ∉ (eKey.symm idx).val) = y j) = true :=
            (hd _ _ _).trans hj
          exact (of_decide_eq_true h1).symm
        · intro h j
          rw [h]
          have hd : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
            fun P d1 d2 => by rw [Subsingleton.elim d1 d2]
          exact (hd _ _ _).trans (decide_eq_true rfl)
      change ((rightFiber y).card : ZMod M) = _
      rw [← zmod_natCast_mod ((rightFiber y).card) M, hcard_mod, zmod_natCast_mod]
      by_cases hex : ∃ K2 : Key, y = pinOfR K2
      · rw [dif_pos hex]
        set K2 := Classical.choose hex
        have hK2 : y = pinOfR K2 := Classical.choose_spec hex
        have hsing : (Finset.univ : Finset (Fin q)).filter (fun idx => y = pinOfR (eKey.symm idx)) =
            {eKey K2} := by
          ext idx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hy
            have hKeq : K2 = eKey.symm idx := hpinOfR_inj (hK2.symm.trans hy)
            rw [hKeq, Equiv.apply_symm_apply]
          · intro hidx; subst hidx; rw [Equiv.symm_apply_apply]; exact hK2
        rw [hsing, Finset.sum_singleton]
        dsimp only [gFin]
        rw [Equiv.symm_apply_apply, ZMod.natCast_zmod_val]
      · rw [dif_neg hex]
        have hemp : (Finset.univ : Finset (Fin q)).filter (fun idx => y = pinOfR (eKey.symm idx)) = ∅ := by
          ext idx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hy; exact hex ⟨eKey.symm idx, hy⟩
        rw [hemp, Finset.sum_empty, Nat.cast_zero]
    have hcompat_iff : ∀ K1 K2 : Key, compat (pinOfL K1) (pinOfR K2) ↔ K1.val ⊆ K2.val := by
      intro K1 K2
      dsimp only [compat, pinOfL, pinOfR]
      simp only [decide_eq_true_eq]
      constructor
      · intro h j hj
        rw [← hrep K1] at hj
        rcases Finset.mem_biUnion.mp hj with ⟨i, hi, hjC⟩
        by_contra hni
        exact h i j hi hni hjC
      · intro hsub i j hi hj hjC
        have hjK1 : j ∈ K1.val := by
          rw [← hrep K1]
          exact Finset.mem_biUnion.mpr ⟨i, hi, hjC⟩
        exact hj (hsub hjK1)
    dsimp only [out, value]
    change ((AllG.card : ℕ) : ZMod (base + 2)) = _
    rw [hAllCard, Nat.cast_sum]
    rw [Finset.sum_filter]
    have hrew : (∑ xy : (Fin l → Bool) × (Fin r → Bool),
        if compat xy.1 xy.2 then (((leftFiber xy.1).card * (rightFiber xy.2).card : ℕ) : ZMod (base + 2)) else 0) =
        ∑ xy : (Fin l → Bool) × (Fin r → Bool),
          if compat xy.1 xy.2 then
            (if h1 : ∃ K1 : Key, xy.1 = pinOfL K1 then f (Classical.choose h1) else 0) *
            (if h2 : ∃ K2 : Key, xy.2 = pinOfR K2 then g (Classical.choose h2) else 0)
          else 0 := by
      apply Finset.sum_congr rfl
      intro xy _
      by_cases hc : compat xy.1 xy.2
      · rw [if_pos hc, if_pos hc, Nat.cast_mul, hLval, hRval]
      · rw [if_neg hc, if_neg hc]
    rw [hrew]
    let imgSet : Finset ((Fin l → Bool) × (Fin r → Bool)) :=
      (Finset.univ : Finset (Key × Key)).image (fun z => (pinOfL z.1, pinOfR z.2))
    have hzero_out : ∀ xy : (Fin l → Bool) × (Fin r → Bool), xy ∉ imgSet →
        (if compat xy.1 xy.2 then
          (if h1 : ∃ K1 : Key, xy.1 = pinOfL K1 then f (Classical.choose h1) else 0) *
          (if h2 : ∃ K2 : Key, xy.2 = pinOfR K2 then g (Classical.choose h2) else 0)
        else 0) = 0 := by
      intro xy hni
      split_ifs with hc h1 h2
      · exfalso
        apply hni
        refine Finset.mem_image.mpr ⟨(Classical.choose h1, Classical.choose h2), Finset.mem_univ _, ?_⟩
        exact Prod.ext (Classical.choose_spec h1).symm (Classical.choose_spec h2).symm
      · simp
      · simp
      · simp
      · rfl
    rw [← Finset.sum_subset (Finset.subset_univ imgSet) (fun xy _ hni => hzero_out xy hni)]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z _
      have h1 : ∃ K1 : Key, pinOfL z.1 = pinOfL K1 := ⟨z.1, rfl⟩
      have h2 : ∃ K2 : Key, pinOfR z.2 = pinOfR K2 := ⟨z.2, rfl⟩
      have hch1 : Classical.choose h1 = z.1 := hpinOfL_inj (Classical.choose_spec h1).symm
      have hch2 : Classical.choose h2 = z.2 := hpinOfR_inj (Classical.choose_spec h2).symm
      rw [dif_pos h1, dif_pos h2, hch1, hch2]
      by_cases hsub : z.1.val ⊆ z.2.val
      · rw [if_pos ((hcompat_iff z.1 z.2).mpr hsub), if_pos hsub]
      · rw [if_neg (fun h => hsub ((hcompat_iff z.1 z.2).mp h)), if_neg hsub]
    · intro z1 _ z2 _ heq
      have h1 : pinOfL z1.1 = pinOfL z2.1 := congrArg Prod.fst heq
      have h2 : pinOfR z1.2 = pinOfR z2.2 := congrArg Prod.snd heq
      exact Prod.ext (hpinOfL_inj h1) (hpinOfR_inj h2)
  refine ⟨N, G, side, p, s, tag, hfits, hNle, htagP, htagS, hout, ?_⟩
  intro A a ha H cols
  let phi : Table → Table := fun g K1 => ∑ K2 : Key, if K1.val ⊆ K2.val then g K2 else 0
  have hout_phi : ∀ f g, out f g = ∑ K1 : Key, f K1 * phi g K1 := by
    intro f g
    rw [hout f g, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro K1 _
    dsimp only [phi]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K2 _
    split_ifs <;> simp
  have hout_sub : ∀ f1 f2 g, out (f1 - f2) g = out f1 g - out f2 g := by
    intro f1 f2 g
    rw [hout_phi, hout_phi, hout_phi, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro K1 _
    change (f1 K1 - f2 K1) * phi g K1 = f1 K1 * phi g K1 - f2 K1 * phi g K1
    ring
  have hcol_iff : ∀ g : Table, (∀ f ∈ A, out f g = out a g) ↔
      ∀ d ∈ H, (∑ K : Key, d K * phi g K) = 0 := by
    intro g
    let kerG : AddSubgroup Table :=
      { carrier := {d : Table | (∑ K : Key, d K * phi g K) = 0}
        zero_mem' := by
          show (∑ K : Key, (0 : Table) K * phi g K) = 0
          have hz : ∀ K : Key, (0 : Table) K * phi g K = 0 := fun _ => zero_mul _
          rw [Finset.sum_congr rfl (fun K _ => hz K), Finset.sum_const_zero]
        neg_mem' := by
          intro d hd
          show (∑ K : Key, (-d) K * phi g K) = 0
          have hsum : (∑ K : Key, (-d) K * phi g K) = -(∑ K : Key, d K * phi g K) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl; intro K _
            change (-d K) * phi g K = -(d K * phi g K); ring
          rw [hsum, hd, neg_zero]
        , add_mem' := by
          intro d1 d2 h1 h2
          show (∑ K : Key, (d1 + d2) K * phi g K) = 0
          have hsum : (∑ K : Key, (d1 + d2) K * phi g K) =
              (∑ K : Key, d1 K * phi g K) + (∑ K : Key, d2 K * phi g K) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro K _
            change (d1 K + d2 K) * phi g K = d1 K * phi g K + d2 K * phi g K; ring
          rw [hsum, h1, h2, add_zero] }
    have hle : H ≤ kerG ↔ {d : Table | ∃ f ∈ A, d = f - a} ⊆ (kerG : Set Table) :=
      AddSubgroup.closure_le kerG
    constructor
    · intro hAll d hd
      have hsub : {d : Table | ∃ f ∈ A, d = f - a} ⊆ (kerG : Set Table) := by
        rintro _ ⟨f, hf, rfl⟩
        show (∑ K : Key, (f - a) K * phi g K) = 0
        rw [← hout_phi, hout_sub, hAll f hf, sub_self]
      exact (hle.mpr hsub) hd
    · intro hAll f hf
      have hmem : f - a ∈ H := AddSubgroup.subset_closure ⟨f, hf, rfl⟩
      have h0 := hAll (f - a) hmem
      rw [← hout_phi, hout_sub] at h0
      exact sub_eq_zero.mp h0
  have hphi_bij : Function.Bijective phi := phi_bijective base
  let ePhi : Table ≃ Table := Equiv.ofBijective phi hphi_bij
  let Hperp : Finset Table :=
    Finset.univ.filter (fun g' => ∀ d ∈ H, (∑ K : Key, d K * g' K) = 0)
  have hcols_eq : cols.card = Hperp.card := by
    refine Finset.card_bij' (fun g _ => ePhi g) (fun g' _ => ePhi.symm g') ?_ ?_ ?_ ?_
    · intro g hg
      simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      simp only [Hperp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcol_iff g).mp hg
    · intro g' hg'
      simp only [Hperp, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
      simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
      refine (hcol_iff (ePhi.symm g')).mpr ?_
      have heq : phi (ePhi.symm g') = g' := ePhi.apply_symm_apply g'
      rw [heq]; exact hg'
    · intro g _; exact ePhi.symm_apply_apply g
    · intro g' _; exact ePhi.apply_symm_apply g'
  rw [hcols_eq]
  have hmain := subgroup_perp_card base H
  have hqeq : Fintype.card Key = q := Fintype.card_coe family
  rw [hqeq] at hmain
  have hperp_eq : Hperp.card =
      ((Finset.univ : Finset (Key → ZMod (base + 2))).filter
        (fun g => ∀ d ∈ H, (∑ K : Key, d K * g K) = 0)).card :=
    card_filter_congr_inst (fun _ _ => Iff.rfl)
  rw [hperp_eq]
  exact hmain

private lemma main_aux :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (base l r : Nat) (C : Fin l → Finset (Fin r)),
      let M := base+2
      let b := Nat.log2 M+1
      let family := (Finset.univ : Finset (Finset (Fin l))).image (fun S => S.biUnion C)
      let Key := ↥family
      let q := family.card
      let Table := Key → ZMod (base+2)
      let budget := fun n => (2+2*b)*(n+q*b+1)+q*b+2*b*(q*b+2)+b
      let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
        (p : Fin l → Fin N) (s : Fin r → Fin N) =>
        Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
        (∀ j, side (s j) = true) ∧ (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
        ∀ u v, side u = false → side v = true →
          (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
      let value := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
        ((((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
          (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card : Nat) : ZMod (base+2))
      (∀ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
        (p : Fin l → Fin N) (s : Fin r → Fin N), fits N G side p s →
        ∃ (send : (Fin N → Bool) → Table) (recv : Table → (Fin N → Bool) → ZMod (base+2)),
          ∀ a d, recv (send a) d = value N G (fun v => if side v then d v else a v)) ∧
      ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
        (p : Fin l → Fin N) (s : Fin r → Fin N) (tag : Fin N → Option (Key × Fin b)),
        fits N G side p s ∧ N ≤ budget l + budget r ∧
        (∀ i, tag (p i) = none) ∧ (∀ j, tag (s j) = none) ∧
        let out := fun (f g : Table) => value N G (fun v =>
          (tag v).elim true (fun k => (((if side v then g else f) k.1).val.testBit k.2.val)))
        (∀ f g, out f g = (Finset.univ : Finset (Key × Key)).sum (fun z =>
          if z.1.val ⊆ z.2.val then f z.1 * g z.2 else 0)) ∧
        ∀ (A : Finset Table) (a : Table), a ∈ A →
          let H := AddSubgroup.closure {d : Table | ∃ f ∈ A, d = f-a}
          let cols := (Finset.univ : Finset Table).filter (fun g => ∀ f ∈ A, out f g = out a g)
          Nat.card ↥H * cols.card = M^q := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro base l r C M b family Key q Table budget fits value
  exact ⟨upper_bound_part base l r C, lower_bound_part base l r C⟩

end PEqualNP.Outside.L_lib_1235_aux

theorem PEqualNP.Outside.L_lib_1235 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (base l r : Nat) (C : Fin l → Finset (Fin r)),
      let M := base+2
      let b := Nat.log2 M+1
      let family := (Finset.univ : Finset (Finset (Fin l))).image (fun S => S.biUnion C)
      let Key := ↥family
      let q := family.card
      let Table := Key → ZMod (base+2)
      let budget := fun n => (2+2*b)*(n+q*b+1)+q*b+2*b*(q*b+2)+b
      let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
        (p : Fin l → Fin N) (s : Fin r → Fin N) =>
        Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
        (∀ j, side (s j) = true) ∧ (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
        ∀ u v, side u = false → side v = true →
          (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
      let value := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
        ((((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
          (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card : Nat) : ZMod (base+2))
      (∀ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
        (p : Fin l → Fin N) (s : Fin r → Fin N), fits N G side p s →
        ∃ (send : (Fin N → Bool) → Table) (recv : Table → (Fin N → Bool) → ZMod (base+2)),
          ∀ a d, recv (send a) d = value N G (fun v => if side v then d v else a v)) ∧
      ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
        (p : Fin l → Fin N) (s : Fin r → Fin N) (tag : Fin N → Option (Key × Fin b)),
        fits N G side p s ∧ N ≤ budget l + budget r ∧
        (∀ i, tag (p i) = none) ∧ (∀ j, tag (s j) = none) ∧
        let out := fun (f g : Table) => value N G (fun v =>
          (tag v).elim true (fun k => (((if side v then g else f) k.1).val.testBit k.2.val)))
        (∀ f g, out f g = (Finset.univ : Finset (Key × Key)).sum (fun z =>
          if z.1.val ⊆ z.2.val then f z.1 * g z.2 else 0)) ∧
        ∀ (A : Finset Table) (a : Table), a ∈ A →
          let H := AddSubgroup.closure {d : Table | ∃ f ∈ A, d = f-a}
          let cols := (Finset.univ : Finset Table).filter (fun g => ∀ f ∈ A, out f g = out a g)
          Nat.card ↥H * cols.card = M^q := by
  exact PEqualNP.Outside.L_lib_1235_aux.main_aux
