import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1239

open Finset

def prA {n : ℕ} {ι : Type} [Fintype ι] (h : ι → ZMod n) : (ι → ZMod n) →+ ZMod n where
  toFun g := ∑ t, h t * g t
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

def prB {n : ℕ} {ι : Type} [Fintype ι] (g : ι → ZMod n) : (ι → ZMod n) →+ ZMod n where
  toFun h := ∑ t, h t * g t
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

open Classical in
theorem charsum {n : ℕ} [NeZero n] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : AddSubgroup (ι → ZMod n)) :
    (univ.filter (fun h => h ∈ H)).card *
      (univ.filter (fun g : ι → ZMod n => ∀ h ∈ H, ∑ t, h t * g t = 0)).card ≤
      Fintype.card (ι → ZMod n) := by
  classical
  set ψ : AddChar (ZMod n) ℂ := ZMod.stdAddChar
  have hprim : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar n
  set Hs := univ.filter (fun h : ι → ZMod n => h ∈ H)
  have h1 : ∑ h ∈ Hs, ∑ g, ψ (prA h g) = (Fintype.card (ι → ZMod n) : ℂ) := by
    rw [Finset.sum_eq_single (0 : ι → ZMod n)]
    · simp [prA]
    · intro h _ hne
      have hch : ψ.compAddMonoidHom (prA h) ≠ 0 := by
        obtain ⟨t, ht⟩ : ∃ t, h t ≠ 0 := by
          by_contra hc; push Not at hc; exact hne (funext hc)
        have := hprim ht
        obtain ⟨c, hc⟩ := AddChar.ne_one_iff.1 this
        intro hz
        apply hc
        have := congrArg (fun χ : AddChar (ι → ZMod n) ℂ => χ (Pi.single t c)) hz
        simp only [AddChar.compAddMonoidHom_apply] at this
        rw [AddChar.mulShift_apply]
        have e : prA h (Pi.single t c) = h t * c := by
          simp [prA, Pi.single_apply, mul_ite]
        rw [e] at this
        simpa [AddChar.zero_apply] using this
      have := AddChar.sum_eq_ite (ψ.compAddMonoidHom (prA h))
      rw [if_neg hch] at this
      simpa using this
    · intro h0; exact absurd (by simp [Hs, H.zero_mem]) h0
  have h2 : ∀ g : ι → ZMod n, ∑ h ∈ Hs, ψ (prA h g) =
      ((if ψ.compAddMonoidHom ((prB g).comp H.subtype) = 0 then Hs.card else 0 : ℕ) : ℂ) := by
    intro g
    have e1 : ∑ h ∈ Hs, ψ (prA h g) = ∑ h : H, ψ.compAddMonoidHom ((prB g).comp H.subtype) h := by
      rw [Finset.sum_subtype Hs (p := fun h => h ∈ H) (by simp [Hs])]
      rfl
    rw [e1, AddChar.sum_eq_ite]
    split_ifs
    · congr 1
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp [Hs]))
    · simp
  have h3 : ∑ g : ι → ZMod n, ∑ h ∈ Hs, ψ (prA h g) = ∑ h ∈ Hs, ∑ g, ψ (prA h g) :=
    Finset.sum_comm
  rw [h1] at h3
  simp only [h2] at h3
  rw [← Nat.cast_sum] at h3
  have h4 := Nat.cast_injective h3
  rw [← h4, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  calc ∑ _x ∈ univ.filter (fun g : ι → ZMod n => ∀ h ∈ H, ∑ t, h t * g t = 0), Hs.card
      = ∑ g ∈ univ.filter (fun g : ι → ZMod n => ∀ h ∈ H, ∑ t, h t * g t = 0),
          (if ψ.compAddMonoidHom ((prB g).comp H.subtype) = 0 then Hs.card else 0) := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [if_pos]
        ext x
        simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, AddChar.zero_apply]
        have : prB g (x : ι → ZMod n) = 0 := (mem_filter.1 hg).2 x x.2
        rw [this, AddChar.map_zero_eq_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; exact Nat.zero_le _)


theorem rowbound {n : ℕ} [NeZero n] {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    [DecidableEq (ι → ZMod n)]
    (P : (α → ZMod n) → (ι → ZMod n)) (hP : ∀ f f', P (f + f') = P f + P f')
    (H : Finset (ι → ZMod n)) (f0 : α → ZMod n)
    (R : Finset (α → ZMod n)) (hR : ∀ f ∈ R, P f - P f0 ∈ H) :
    R.card * (univ.image P).card ≤ H.card * Fintype.card (α → ZMod n) := by
  classical
  have hsec : ∀ y ∈ univ.image P, ∃ x, P x = y := by
    intro y hy; obtain ⟨x, _, hx⟩ := mem_image.1 hy; exact ⟨x, hx⟩
  let σ : (ι → ZMod n) → (α → ZMod n) := fun y =>
    if h : ∃ x, P x = y then h.choose else 0
  have hσ : ∀ y ∈ univ.image P, P (σ y) = y := by
    intro y hy; simp only [σ, dif_pos (hsec y hy)]; exact (hsec y hy).choose_spec
  have hPsub : ∀ f f', P (f - f') = P f - P f' := by
    intro f f'
    have := hP (f - f') f'
    rw [sub_add_cancel] at this
    rw [this]; abel
  rw [← card_product, ← card_univ, ← card_product]
  apply Finset.card_le_card_of_injOn (fun q => (P q.1 - P f0, q.1 - σ (P q.1) + σ q.2))
  · intro q hq
    simp only [coe_product, Set.mem_prod, mem_coe] at hq ⊢
    exact ⟨hR _ hq.1, mem_univ _⟩
  · intro q hq q' hq' he
    simp only [coe_product, Set.mem_prod, mem_coe] at hq hq'
    simp only [Prod.mk.injEq] at he
    have e1 : P q.1 = P q'.1 := by have := he.1; exact sub_left_injective this
    have e2 := congrArg P he.2
    rw [hP, hP, hPsub, hPsub, hσ _ hq.2, hσ _ hq'.2, hσ _ (mem_image_of_mem _ (mem_univ _)),
      hσ _ (mem_image_of_mem _ (mem_univ _)), sub_self, sub_self, zero_add, zero_add] at e2
    have e3 := he.2
    rw [e1, e2] at e3
    have : q.1 = q'.1 := sub_left_injective (add_right_cancel e3)
    exact Prod.ext this e2

theorem rectbound {n : ℕ} [NeZero n] {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq α]
    [DecidableEq ι] [DecidableEq (ι → ZMod n)]
    (P : (α → ZMod n) → (ι → ZMod n)) (hP : ∀ f f', P (f + f') = P f + P f')
    (rows : Finset (α → ZMod n)) (cols : Finset (ι → ZMod n)) (guess : (ι → ZMod n) → ZMod n)
    (hc : ∀ f ∈ rows, ∀ g ∈ cols, guess g = ∑ t, P f t * g t) :
    rows.card * cols.card * (univ.image P).card ≤
      Fintype.card (α → ZMod n) * Fintype.card (ι → ZMod n) := by
  classical
  rcases rows.eq_empty_or_nonempty with h | ⟨f0, hf0⟩
  · simp [h]
  let H : AddSubgroup (ι → ZMod n) :=
    AddSubgroup.closure {x | ∃ f ∈ rows, x = P f - P f0}
  have hcols : cols ⊆ univ.filter (fun g : ι → ZMod n => ∀ h ∈ H, ∑ t, h t * g t = 0) := by
    intro g hg
    simp only [mem_filter, mem_univ, true_and]
    have : H ≤ (prB g).ker := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨f, hf, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, prB, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [← hc f hf g hg, ← hc f0 hf0 g hg, sub_self]
    intro h hh
    exact this hh
  have hrows := rowbound P hP (univ.filter (fun h => h ∈ H)) f0 rows (by
    intro f hf
    simp only [mem_filter, mem_univ, true_and]
    exact AddSubgroup.subset_closure ⟨f, hf, rfl⟩)
  have hch := charsum (n := n) H
  have hcc := card_le_card hcols
  calc rows.card * cols.card * (univ.image P).card
      = rows.card * (univ.image P).card * cols.card := by ring
    _ ≤ (univ.filter (fun h => h ∈ H)).card * Fintype.card (α → ZMod n) *
          (univ.filter (fun g : ι → ZMod n => ∀ h ∈ H, ∑ t, h t * g t = 0)).card :=
        Nat.mul_le_mul hrows hcc
    _ = Fintype.card (α → ZMod n) * ((univ.filter (fun h => h ∈ H)).card *
          (univ.filter (fun g : ι → ZMod n => ∀ h ∈ H, ∑ t, h t * g t = 0)).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hch

theorem lowerbound {n : ℕ} [NeZero n] {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq α]
    [DecidableEq ι] [DecidableEq (ι → ZMod n)]
    (P : (α → ZMod n) → (ι → ZMod n)) (hP : ∀ f f', P (f + f') = P f + P f')
    (k : ℕ) (rows : Fin k → Finset (α → ZMod n)) (cols : Fin k → Finset (ι → ZMod n))
    (guess : Fin k → (ι → ZMod n) → ZMod n)
    (hpart : ∀ f g, ∃! i, f ∈ rows i ∧ g ∈ cols i)
    (hc : ∀ i, ∀ f ∈ rows i, ∀ g ∈ cols i, guess i g = ∑ t, P f t * g t) :
    (univ.image P).card ≤ k := by
  classical
  let idx : (α → ZMod n) × (ι → ZMod n) → Fin k := fun q => (hpart q.1 q.2).choose
  have hsum : Fintype.card (α → ZMod n) * Fintype.card (ι → ZMod n) =
      ∑ i, (rows i).card * (cols i).card := by
    rw [← Fintype.card_prod, ← card_univ, card_eq_sum_card_fiberwise (f := idx) (t := univ)
      (fun _ _ => mem_univ _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← card_product]
    congr 1
    ext q
    simp only [mem_filter, mem_univ, true_and, mem_product]
    constructor
    · intro h; rw [← h]; exact (hpart q.1 q.2).choose_spec.1
    · intro h; exact ((hpart q.1 q.2).choose_spec.2 i h).symm
  have hpos : 0 < Fintype.card (α → ZMod n) * Fintype.card (ι → ZMod n) :=
    Nat.mul_pos Fintype.card_pos Fintype.card_pos
  have : (univ.image P).card * (Fintype.card (α → ZMod n) * Fintype.card (ι → ZMod n)) ≤
      k * (Fintype.card (α → ZMod n) * Fintype.card (ι → ZMod n)) := by
    conv_lhs => rw [hsum, Finset.mul_sum]
    calc ∑ i, (univ.image P).card * ((rows i).card * (cols i).card)
        ≤ ∑ _i : Fin k, Fintype.card (α → ZMod n) * Fintype.card (ι → ZMod n) := by
          apply Finset.sum_le_sum
          intro i _
          have := rectbound P hP (rows i) (cols i) (guess i) (hc i)
          calc _ = (rows i).card * (cols i).card * (univ.image P).card := by ring
            _ ≤ _ := this
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_right this hpos


section Decomp

open Classical

variable {N l r : ℕ} (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
  (p : Fin l → Fin N) (s : Fin r → Fin N) (C : Fin l → Finset (Fin r)) (a d : Fin N → Bool)

def cL (S : Finset (Fin l)) : ℕ :=
  (univ.filter (fun A : Finset (Fin N) => (∀ v ∈ A, side v = false ∧ a v = true) ∧
    (∀ u ∈ A, ∀ v ∈ G u, v ∉ A) ∧ ∀ i, p i ∈ A ↔ i ∈ S)).card

def cR (T : Finset (Fin r)) : ℕ :=
  (univ.filter (fun B : Finset (Fin N) => (∀ v ∈ B, side v = true ∧ d v = true) ∧
    (∀ u ∈ B, ∀ v ∈ G u, v ∉ B) ∧ ∀ j, s j ∈ B ↔ j ∈ T)).card

def good (I : Finset (Fin N)) : Prop :=
  (∀ v ∈ I, (if side v then d v else a v) = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I

theorem piece (hps : ∀ i, side (p i) = false) (hss : ∀ j, side (s j) = true)
    (hsym : ∀ u v, v ∈ G u ↔ u ∈ G v)
    (hcross : ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i))
    (S : Finset (Fin l)) (T : Finset (Fin r)) :
    (univ.filter (fun I => good G side a d I ∧ (∀ i, p i ∈ I ↔ i ∈ S) ∧
      (∀ j, s j ∈ I ↔ j ∈ T))).card =
      if (∀ i ∈ S, ∀ j ∈ C i, j ∉ T) then cL G side p a S * cR G side s d T else 0 := by
  classical
  split_ifs with hc
  · unfold cL cR
    rw [← card_product]
    apply Finset.card_nbij' (fun (I : Finset (Fin N)) => (I.filter (fun v => side v = false),
        I.filter (fun v => side v = true))) (fun (q : Finset (Fin N) × Finset (Fin N)) => q.1 ∪ q.2)
    · intro I hI
      rw [mem_coe, mem_filter] at hI
      simp only [good] at hI
      obtain ⟨-, ⟨hl, hind⟩, hS, hT⟩ := hI
      rw [mem_coe, mem_product, mem_filter, mem_filter]
      dsimp only
      simp only [mem_filter]
      refine ⟨⟨mem_univ _, fun v hv => ⟨hv.2, by have := hl v hv.1; rwa [hv.2] at this⟩,
        fun u hu v hv hv' => hind u hu.1 v hv hv'.1, fun i => ?_⟩,
        ⟨mem_univ _, fun v hv => ⟨hv.2, by have := hl v hv.1; rwa [hv.2] at this⟩,
        fun u hu v hv hv' => hind u hu.1 v hv hv'.1, fun j => ?_⟩⟩
      · rw [← hS i]; simp [hps i]
      · rw [← hT j]; simp [hss j]
    · intro q hq
      rw [mem_coe, mem_product, mem_filter, mem_filter] at hq
      obtain ⟨⟨-, hA, hAi, hAS⟩, ⟨-, hB, hBi, hBT⟩⟩ := hq
      rw [mem_coe, mem_filter]
      dsimp only
      simp only [good, mem_union]
      refine ⟨mem_univ _, ⟨?_, ?_⟩, fun i => ?_, fun j => ?_⟩
      · rintro v (hv | hv)
        · rw [(hA v hv).1]; exact (hA v hv).2
        · rw [(hB v hv).1]; exact (hB v hv).2
      · rintro u (hu | hu) v hv (hv' | hv')
        · exact hAi u hu v hv hv'
        · obtain ⟨i, j, rfl, rfl, hj⟩ := (hcross u v (hA u hu).1 (hB v hv').1).1 hv
          exact hc i ((hAS i).1 hu) j hj ((hBT j).1 hv')
        · have hu' := (hsym u v).1 hv
          obtain ⟨i, j, rfl, rfl, hj⟩ := (hcross v u (hA v hv').1 (hB u hu).1).1 hu'
          exact hc i ((hAS i).1 hv') j hj ((hBT j).1 hu)
        · exact hBi u hu v hv hv'
      · constructor
        · rintro (h | h)
          · exact (hAS i).1 h
          · have := (hB _ h).1; rw [hps i] at this; exact absurd this (by simp)
        · intro h; exact Or.inl ((hAS i).2 h)
      · constructor
        · rintro (h | h)
          · have := (hA _ h).1; rw [hss j] at this; exact absurd this (by simp)
          · exact (hBT j).1 h
        · intro h; exact Or.inr ((hBT j).2 h)
    · intro I _
      ext v
      simp only [mem_union, mem_filter]
      cases side v <;> simp
    · intro q hq
      rw [mem_coe, mem_product, mem_filter, mem_filter] at hq
      obtain ⟨⟨-, hA, -, -⟩, ⟨-, hB, -, -⟩⟩ := hq
      ext v
      · simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨h | h, h'⟩
          · exact h
          · rw [(hB v h).1] at h'; exact absurd h' (by simp)
        · intro h; exact ⟨Or.inl h, (hA v h).1⟩
      · simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨h | h, h'⟩
          · rw [(hA v h).1] at h'; exact absurd h' (by simp)
          · exact h
        · intro h; exact ⟨Or.inr h, (hB v h).1⟩
  · push Not at hc
    obtain ⟨i, hi, j, hj, hjT⟩ := hc
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro I - ⟨⟨-, hind⟩, hS, hT⟩
    have hu := (hS i).2 hi
    have hv := (hT j).2 hjT
    exact hind (p i) hu (s j) ((hcross (p i) (s j) (hps i) (hss j)).2 ⟨i, j, rfl, rfl, hj⟩) hv

theorem decomp (hps : ∀ i, side (p i) = false) (hss : ∀ j, side (s j) = true)
    (hsym : ∀ u v, v ∈ G u ↔ u ∈ G v)
    (hcross : ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)) :
    (univ.filter (fun I => good G side a d I)).card =
      ∑ S : Finset (Fin l), ∑ T : Finset (Fin r),
        if (∀ i ∈ S, ∀ j ∈ C i, j ∉ T) then cL G side p a S * cR G side s d T else 0 := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun I => univ.filter (fun i => p i ∈ I)) (t := univ)
    (fun _ _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro S _
  rw [card_eq_sum_card_fiberwise (f := fun I => univ.filter (fun j => s j ∈ I)) (t := univ)
    (fun _ _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro T _
  rw [← piece G side p s C a d hps hss hsym hcross S T, filter_filter, filter_filter]
  congr 1
  apply filter_congr
  intro I _
  simp only [Finset.ext_iff, mem_filter, mem_univ, true_and]

end Decomp


section Total

open Classical

variable {N l r : ℕ} (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
  (p : Fin l → Fin N) (s : Fin r → Fin N) (C : Fin l → Finset (Fin r)) (a d : Fin N → Bool)

theorem cL_zero (L : Fin l → Finset (Fin l)) (hpL : ∀ i j, p j ∈ G (p i) ↔ j ∈ L i)
    (S : Finset (Fin l)) (hS : ¬ ∀ i ∈ S, ∀ j ∈ L i, j ∉ S) : cL G side p a S = 0 := by
  push Not at hS
  obtain ⟨i, hi, j, hj, hjS⟩ := hS
  unfold cL
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro A - ⟨-, hind, htr⟩
  exact hind (p i) ((htr i).2 hi) (p j) ((hpL i j).2 hj) ((htr j).2 hjS)

theorem cR_zero (R : Fin r → Finset (Fin r)) (hsR : ∀ i j, s j ∈ G (s i) ↔ j ∈ R i)
    (T : Finset (Fin r)) (hT : ¬ ∀ i ∈ T, ∀ j ∈ R i, j ∉ T) : cR G side s d T = 0 := by
  push Not at hT
  obtain ⟨i, hi, j, hj, hjT⟩ := hT
  unfold cR
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro A - ⟨-, hind, htr⟩
  exact hind (s i) ((htr i).2 hi) (s j) ((hsR i j).2 hj) ((htr j).2 hjT)

theorem sum_sub {α β : Type} [Fintype α] [AddCommMonoid β] (s : Finset α) (f : α → β) :
    ∑ x : ↥s, f x.val = ∑ x, if x ∈ s then f x else 0 := by
  rw [Finset.sum_coe_sort, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem total {n : ℕ} (L : Fin l → Finset (Fin l)) (R : Fin r → Finset (Fin r))
    (lk : Finset (Finset (Fin l))) (rk : Finset (Finset (Fin r)))
    (hlk : ∀ S, S ∈ lk ↔ ∀ i ∈ S, ∀ j ∈ L i, j ∉ S)
    (hrk : ∀ T, T ∈ rk ↔ ∀ i ∈ T, ∀ j ∈ R i, j ∉ T)
    (hps : ∀ i, side (p i) = false) (hss : ∀ j, side (s j) = true)
    (hsym : ∀ u v, v ∈ G u ↔ u ∈ G v)
    (hpL : ∀ i j, p j ∈ G (p i) ↔ j ∈ L i) (hsR : ∀ i j, s j ∈ G (s i) ↔ j ∈ R i)
    (hcross : ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)) :
    ((univ.filter (fun I => good G side a d I)).card : ZMod n) =
      ∑ T : ↥rk, (∑ S : ↥lk,
          if (∀ i ∈ S.val, ∀ j ∈ C i, j ∉ T.val) then (cL G side p a S.val : ZMod n) else 0) *
        (cR G side s d T.val : ZMod n) := by
  rw [decomp G side p s C a d hps hss hsym hcross]
  push_cast
  rw [Finset.sum_comm]
  rw [sum_sub rk (fun T => (∑ S : ↥lk,
      (if (∀ i ∈ S.val, ∀ j ∈ C i, j ∉ T) then (cL G side p a S.val : ZMod n) else 0)) *
      (cR G side s d T : ZMod n))]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with hT
  · rw [sum_sub lk (fun S => if (∀ i ∈ S, ∀ j ∈ C i, j ∉ T) then
      (cL G side p a S : ZMod n) else 0), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hc hS hS
    · rfl
    · rw [cL_zero G side p a L hpL S (fun h => hS ((hlk S).2 h))]; simp
    · simp
    · simp
  · rw [cR_zero G side s d R hsR T (fun h => hT ((hrk T).2 h))]
    simp

end Total


section Gadget

open Classical

theorem surj {m n : ℕ} [NeZero n] (t : Finset (Fin m) → ZMod n) :
    ∃ mm : Finset (Fin m) → ZMod n, ∀ S, ∑ Q ∈ univ.filter (fun Q => S ⊆ Q), mm Q = t S := by
  let Φ : (Finset (Fin m) → ZMod n) → (Finset (Fin m) → ZMod n) :=
    fun x S => ∑ Q ∈ univ.filter (fun Q => S ⊆ Q), x Q
  have hsplit : ∀ (x : Finset (Fin m) → ZMod n) S,
      Φ x S = x S + ∑ Q ∈ univ.filter (fun Q => S ⊂ Q), x Q := by
    intro x S
    have : univ.filter (fun Q => S ⊆ Q) = insert S (univ.filter (fun Q => S ⊂ Q)) := by
      ext Q
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        rcases h.eq_or_ssubset with h' | h'
        · left; exact h'.symm
        · right; exact h'
      · rintro (h | h)
        · rw [h]
        · exact h.subset
    simp only [Φ]
    rw [this, sum_insert (by simp)]
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have key : ∀ k, ∀ S : Finset (Fin m), m - S.card = k → x S = y S := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro S hS
        have h1 := congrFun hxy S
        rw [hsplit, hsplit] at h1
        have h2 : ∑ Q ∈ univ.filter (fun Q => S ⊂ Q), x Q =
            ∑ Q ∈ univ.filter (fun Q => S ⊂ Q), y Q := by
          apply sum_congr rfl
          intro Q hQ
          rw [mem_filter] at hQ
          have hc := card_lt_card hQ.2
          have hle : Q.card ≤ m := by simpa using card_le_univ Q
          exact ih (m - Q.card) (by omega) Q rfl
        rw [h2] at h1
        exact add_right_cancel h1
    funext S
    exact key _ S rfl
  obtain ⟨mm, hmm⟩ := (Finite.injective_iff_surjective.1 hinj) t
  exact ⟨mm, fun S => congrFun hmm S⟩

def cnt {N m : ℕ} (G : Fin N → Finset (Fin N)) (side : Fin N → Bool) (sd : Bool)
    (q : Fin m → Fin N) (live : Fin N → Bool) (S : Finset (Fin m)) : ℕ :=
  (univ.filter (fun A : Finset (Fin N) => (∀ v ∈ A, side v = sd ∧ live v = true) ∧
    (∀ u ∈ A, ∀ v ∈ G u, v ∉ A) ∧ ∀ i, q i ∈ A ↔ i ∈ S)).card

theorem cnt_formula {N m n : ℕ} [NeZero n] (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (sd : Bool) (q : Fin m → Fin N) (gad : Finset (Fin m) × Fin n → Fin N)
    (live : Fin N → Bool) (L : Fin m → Finset (Fin m)) (mm : Finset (Fin m) → ZMod n)
    (hq : Function.Injective q) (hg : Function.Injective gad) (hqg : ∀ i x, q i ≠ gad x)
    (hcover : ∀ v, side v = sd → (∃ i, v = q i) ∨ ∃ x, v = gad x)
    (hqs : ∀ i, side (q i) = sd) (hgs : ∀ x, side (gad x) = sd)
    (hqq : ∀ i j, q j ∈ G (q i) ↔ j ∈ L i)
    (hqgad : ∀ i x, gad x ∈ G (q i) ↔ i ∉ x.1)
    (hgq : ∀ i x, q i ∈ G (gad x) ↔ i ∉ x.1)
    (hgg : ∀ x y, gad y ∈ G (gad x) ↔ x ≠ y)
    (hlq : ∀ i, live (q i) = true) (hlg : ∀ x, live (gad x) = decide (x.2.val < (mm x.1).val))
    (S : Finset (Fin m)) (hS : ∀ i ∈ S, ∀ j ∈ L i, j ∉ S) :
    cnt G side sd q live S = 1 + ∑ Q ∈ univ.filter (fun Q => S ⊆ Q), (mm Q).val := by
  set P := S.image q with hP
  set W := univ.filter (fun x : Finset (Fin m) × Fin n => S ⊆ x.1 ∧ x.2.val < (mm x.1).val)
  have hmemP : ∀ v, v ∈ P ↔ ∃ i ∈ S, v = q i := by
    intro v; rw [hP, mem_image]; constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  have hqP : ∀ i, q i ∈ P ↔ i ∈ S := by
    intro i; rw [hmemP]; constructor
    · rintro ⟨j, hj, h⟩; rw [hq h]; exact hj
    · intro h; exact ⟨i, h, rfl⟩
  have hgP : ∀ x, gad x ∉ P := by
    intro x h; obtain ⟨i, -, h⟩ := (hmemP _).1 h; exact hqg i x h.symm
  have hset : univ.filter (fun A : Finset (Fin N) => (∀ v ∈ A, side v = sd ∧ live v = true) ∧
      (∀ u ∈ A, ∀ v ∈ G u, v ∉ A) ∧ ∀ i, q i ∈ A ↔ i ∈ S) =
      insert P (W.image (fun x => insert (gad x) P)) := by
    ext A
    rw [mem_filter, mem_insert, mem_image]
    constructor
    · rintro ⟨-, hlive, hind, htr⟩
      have hPA : P ⊆ A := by
        intro v hv; obtain ⟨i, hi, rfl⟩ := (hmemP v).1 hv; exact (htr i).2 hi
      by_cases hga : ∃ x, gad x ∈ A
      · right
        obtain ⟨x, hx⟩ := hga
        refine ⟨x, ?_, ?_⟩
        · rw [mem_filter]
          refine ⟨mem_univ _, ?_, ?_⟩
          · intro i hi
            by_contra hni
            exact hind (q i) ((htr i).2 hi) (gad x) ((hqgad i x).2 hni) hx
          · have := (hlive _ hx).2
            rw [hlg] at this
            exact of_decide_eq_true this
        · ext v
          rw [mem_insert]
          constructor
          · rintro (rfl | hv)
            · exact hx
            · exact hPA hv
          · intro hv
            rcases hcover v (hlive v hv).1 with ⟨i, rfl⟩ | ⟨y, rfl⟩
            · right; exact (hqP i).2 ((htr i).1 hv)
            · left
              by_contra hne
              have hxy : x ≠ y := fun h => hne (by rw [h])
              exact hind (gad x) hx (gad y) ((hgg x y).2 hxy) hv
      · left
        push Not at hga
        ext v
        constructor
        · intro hv
          rcases hcover v (hlive v hv).1 with ⟨i, rfl⟩ | ⟨y, rfl⟩
          · exact (hqP i).2 ((htr i).1 hv)
          · exact absurd hv (hga y)
        · intro hv; exact hPA hv
    · have hPind : ∀ u ∈ P, ∀ v ∈ G u, v ∉ P := by
        intro u hu v hv hv'
        obtain ⟨i, hi, rfl⟩ := (hmemP u).1 hu
        obtain ⟨j, hj, rfl⟩ := (hmemP _).1 hv'
        exact hS i hi j ((hqq i j).1 hv) hj
      have hPlive : ∀ v ∈ P, side v = sd ∧ live v = true := by
        intro v hv
        obtain ⟨i, -, rfl⟩ := (hmemP v).1 hv
        exact ⟨hqs i, hlq i⟩
      rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨mem_univ _, hPlive, hPind, hqP⟩
      · rw [mem_filter] at hx
        obtain ⟨-, hxS, hxl⟩ := hx
        refine ⟨mem_univ _, ?_, ?_, ?_⟩
        · intro v hv
          rw [mem_insert] at hv
          rcases hv with rfl | hv
          · exact ⟨hgs x, by rw [hlg]; exact decide_eq_true hxl⟩
          · exact hPlive v hv
        · intro u hu v hv hv'
          rw [mem_insert] at hu hv'
          rcases hu with rfl | hu <;> rcases hv' with rfl | hv'
          · exact (hgg x x).1 hv rfl
          · obtain ⟨i, hi, rfl⟩ := (hmemP v).1 hv'
            exact (hgq i x).1 hv (hxS hi)
          · obtain ⟨i, hi, rfl⟩ := (hmemP u).1 hu
            exact (hqgad i x).1 hv (hxS hi)
          · exact hPind u hu v hv hv'
        · intro i
          rw [mem_insert, hqP]
          constructor
          · rintro (h | h)
            · exact absurd h (hqg i x)
            · exact h
          · intro h; right; exact h
  unfold cnt
  rw [hset, card_insert_of_notMem, card_image_of_injective, add_comm]
  · congr 1
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ.filter (fun Q => S ⊆ Q))]
    · apply sum_congr rfl
      intro Q hQ
      rw [mem_filter] at hQ
      have : (W.filter (fun x => x.1 = Q)) =
          (univ.filter (fun c : Fin n => (c : ℕ) < (mm Q).val)).map
            ⟨fun c => (Q, c), fun c c' h => by simpa using h⟩ := by
        ext ⟨Q', c⟩
        simp only [W, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨-, h⟩, rfl⟩
          exact ⟨c, h, rfl⟩
        · rintro ⟨c', h, he⟩
          have he' : (Q, c') = (Q', c) := he
          simp only [Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          exact ⟨⟨hQ.2, h⟩, rfl⟩
      rw [this, card_map, Fin.card_filter_val_lt]
      exact min_eq_right (ZMod.val_lt _).le
    · intro x hx
      exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2.1⟩
  · intro x y h
    have h' : insert (gad x) P = insert (gad y) P := h
    have : gad x ∈ insert (gad y) P := by rw [← h']; exact mem_insert_self _ _
    rw [mem_insert] at this
    rcases this with h' | h'
    · exact hg h'
    · exact absurd h' (hgP x)
  · rw [mem_image]
    rintro ⟨x, -, h⟩
    exact hgP x (h ▸ mem_insert_self _ _)

end Gadget


section Construct

open Classical

def adjH {m n : ℕ} (L : Fin m → Finset (Fin m)) :
    (Fin m ⊕ (Finset (Fin m) × Fin n)) → (Fin m ⊕ (Finset (Fin m) × Fin n)) → Prop
  | Sum.inl i, Sum.inl j => j ∈ L i
  | Sum.inl i, Sum.inr x => i ∉ x.1
  | Sum.inr x, Sum.inl i => i ∉ x.1
  | Sum.inr x, Sum.inr y => x ≠ y

def adjV {l r n : ℕ} (L : Fin l → Finset (Fin l)) (R : Fin r → Finset (Fin r))
    (C : Fin l → Finset (Fin r)) :
    ((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))) →
    ((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))) → Prop
  | Sum.inl u, Sum.inl v => adjH L u v
  | Sum.inr u, Sum.inr v => adjH R u v
  | Sum.inl (Sum.inl i), Sum.inr (Sum.inl j) => j ∈ C i
  | Sum.inr (Sum.inl j), Sum.inl (Sum.inl i) => j ∈ C i
  | _, _ => False

theorem construct {l r n : ℕ} [NeZero n] (L : Fin l → Finset (Fin l))
    (R : Fin r → Finset (Fin r)) (C : Fin l → Finset (Fin r))
    (hLi : ∀ i, i ∉ L i) (hLs : ∀ i j, j ∈ L i ↔ i ∈ L j)
    (hRi : ∀ i, i ∉ R i) (hRs : ∀ i j, j ∈ R i ↔ i ∈ R j) :
    ∃ (N : ℕ) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
      (p : Fin l → Fin N) (s : Fin r → Fin N)
      (liveL : (Finset (Fin l) → ZMod n) → Fin N → Bool)
      (liveR : (Finset (Fin r) → ZMod n) → Fin N → Bool),
      Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
      (∀ j, side (s j) = true) ∧ (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
      (∀ i j, p j ∈ G (p i) ↔ j ∈ L i) ∧ (∀ i j, s j ∈ G (s i) ↔ j ∈ R i) ∧
      (∀ u v, side u = false → side v = true →
        (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)) ∧
      (∀ mm i, liveL mm (p i) = true) ∧ (∀ mm j, liveR mm (s j) = true) ∧
      (∀ mm S, (∀ i ∈ S, ∀ j ∈ L i, j ∉ S) →
        cnt G side false p (liveL mm) S = 1 + ∑ Q ∈ univ.filter (fun Q => S ⊆ Q), (mm Q).val) ∧
      (∀ mm T, (∀ i ∈ T, ∀ j ∈ R i, j ∉ T) →
        cnt G side true s (liveR mm) T = 1 + ∑ Q ∈ univ.filter (fun Q => T ⊆ Q), (mm Q).val) := by
  let e : ((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))) ≃ Fin (Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))))) := Fintype.equivFin (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))))
  let G : Fin (Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))))) → Finset (Fin (Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n)))))) :=
    fun u => univ.filter (fun v => adjV (n := n) L R C (e.symm u) (e.symm v))
  have hG : ∀ x y, e y ∈ G (e x) ↔ adjV (n := n) L R C x y := by
    intro x y; simp [G]
  let side : Fin (Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))))) → Bool := fun u => (e.symm u).isRight
  have hside : ∀ x, side (e x) = x.isRight := by intro x; simp [side]
  let liveL : (Finset (Fin l) → ZMod n) → Fin (Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))))) → Bool := fun mm u =>
    match e.symm u with
    | Sum.inl (Sum.inr x) => decide (x.2.val < (mm x.1).val)
    | _ => true
  let liveR : (Finset (Fin r) → ZMod n) → Fin (Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n))))) → Bool := fun mm u =>
    match e.symm u with
    | Sum.inr (Sum.inr x) => decide (x.2.val < (mm x.1).val)
    | _ => true
  refine ⟨Fintype.card (((Fin l ⊕ (Finset (Fin l) × Fin n)) ⊕ (Fin r ⊕ (Finset (Fin r) × Fin n)))), G, side, fun i => e (Sum.inl (Sum.inl i)),
    fun j => e (Sum.inr (Sum.inl j)), liveL, liveR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro i j h; exact Sum.inl_injective (Sum.inl_injective (e.injective h))
  · intro i j h; exact Sum.inl_injective (Sum.inr_injective (e.injective h))
  · intro i; rw [hside]; rfl
  · intro j; rw [hside]; rfl
  · intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    rw [hG]
    rcases x with (i | x) | (j | y) <;> simp [adjV, adjH, hLi, hRi]
  · intro u v
    obtain ⟨x, rfl⟩ := e.surjective u
    obtain ⟨y, rfl⟩ := e.surjective v
    rw [hG, hG]
    rcases x with (i | x) | (i | x) <;> rcases y with (j | y) | (j | y) <;>
      simp [adjV, adjH, hLs, hRs, eq_comm]
  · intro i j; rw [hG]; simp [adjV, adjH]
  · intro i j; rw [hG]; simp [adjV, adjH]
  · intro u v hu hv
    obtain ⟨x, rfl⟩ := e.surjective u
    obtain ⟨y, rfl⟩ := e.surjective v
    rw [hG]
    rw [hside] at hu hv
    simp only [e.injective.eq_iff]
    rcases x with (i | x) | (i | x) <;> rcases y with (j | y) | (j | y) <;>
    first
    | (simp at hu; done)
    | (simp at hv; done)
    | (simp only [adjV]
       constructor
       · intro h; exact ⟨i, j, rfl, rfl, h⟩
       · rintro ⟨i', j', h1, h2, h3⟩
         rw [Sum.inl_injective (Sum.inl_injective h1), Sum.inl_injective (Sum.inr_injective h2)]
         exact h3)
    | (simp only [adjV, false_iff]
       rintro ⟨i', j', h1, h2, -⟩
       first
       | exact Sum.inr_ne_inl (Sum.inl_injective h1)
       | exact Sum.inr_ne_inl (Sum.inr_injective h2))
  · intro mm i; simp [liveL]
  · intro mm j; simp [liveR]
  · intro mm S hS
    apply cnt_formula G side false (fun i => e (Sum.inl (Sum.inl i)))
      (fun x => e (Sum.inl (Sum.inr x))) (liveL mm) L mm
    · intro i j h; exact Sum.inl_injective (Sum.inl_injective (e.injective h))
    · intro x y h; exact Sum.inr_injective (Sum.inl_injective (e.injective h))
    · intro i x h; exact Sum.inl_ne_inr (Sum.inl_injective (e.injective h))
    · intro v hv
      obtain ⟨x, rfl⟩ := e.surjective v
      rw [hside] at hv
      rcases x with (i | x) | (i | x)
      · left; exact ⟨i, rfl⟩
      · right; exact ⟨x, rfl⟩
      · simp at hv
      · simp at hv
    · intro i; rw [hside]; rfl
    · intro x; rw [hside]; rfl
    · intro i j; rw [hG]; simp [adjV, adjH]
    · intro i x; rw [hG]; simp [adjV, adjH]
    · intro i x; rw [hG]; simp [adjV, adjH]
    · intro x y; rw [hG]; simp [adjV, adjH]
    · intro i; simp [liveL]
    · intro x; simp [liveL]
    · exact hS
  · intro mm T hT
    apply cnt_formula G side true (fun j => e (Sum.inr (Sum.inl j)))
      (fun x => e (Sum.inr (Sum.inr x))) (liveR mm) R mm
    · intro i j h; exact Sum.inl_injective (Sum.inr_injective (e.injective h))
    · intro x y h; exact Sum.inr_injective (Sum.inr_injective (e.injective h))
    · intro i x h; exact Sum.inl_ne_inr (Sum.inr_injective (e.injective h))
    · intro v hv
      obtain ⟨x, rfl⟩ := e.surjective v
      rw [hside] at hv
      rcases x with (i | x) | (i | x)
      · simp at hv
      · simp at hv
      · left; exact ⟨i, rfl⟩
      · right; exact ⟨x, rfl⟩
    · intro i; rw [hside]; rfl
    · intro x; rw [hside]; rfl
    · intro i j; rw [hG]; simp [adjV, adjH]
    · intro i x; rw [hG]; simp [adjV, adjH]
    · intro i x; rw [hG]; simp [adjV, adjH]
    · intro x y; rw [hG]; simp [adjV, adjH]
    · intro i; simp [liveR]
    · intro x; simp [liveR]
    · exact hT

theorem proj_add {α ι : Type} [Fintype α] {n : ℕ} (c : α → ι → Prop)
    [∀ a b, Decidable (c a b)] (f f' : α → ZMod n) :
    (fun T => ∑ S, if c S T then (f + f') S else 0) =
      (fun T => ∑ S, if c S T then f S else 0) + (fun T => ∑ S, if c S T then f' S else 0) := by
  funext T
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

end Construct

end PEqualNP.Outside.L_lib_1239

theorem PEqualNP.Outside.L_lib_1239 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (base l r : Nat) (L : Fin l → Finset (Fin l)) (R : Fin r → Finset (Fin r))
  (C : Fin l → Finset (Fin r)),
  (∀ i, i ∉ L i) → (∀ i j, j ∈ L i ↔ i ∈ L j) →
  (∀ i, i ∉ R i) → (∀ i j, j ∈ R i ↔ i ∈ R j) →
  let lk := (Finset.univ : Finset (Finset (Fin l))).filter
    (fun S => ∀ i ∈ S, ∀ j ∈ L i, j ∉ S)
  let rk := (Finset.univ : Finset (Finset (Fin r))).filter
    (fun T => ∀ i ∈ T, ∀ j ∈ R i, j ∉ T)
  let Left := ↥lk → ZMod (base+2)
  let Right := ↥rk → ZMod (base+2)
  let project := fun (f : Left) (T : ↥rk) =>
    (Finset.univ : Finset ↥lk).sum (fun S =>
      if ∀ i ∈ S.val, ∀ j ∈ C i, j ∉ T.val then f S else 0)
  let img := (Finset.univ : Finset Left).image project
  let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N) =>
    Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
    (∀ j, side (s j) = true) ∧ (∀ v, v ∉ G v) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
    (∀ i j, p j ∈ G (p i) ↔ j ∈ L i) ∧ (∀ i j, s j ∈ G (s i) ↔ j ∈ R i) ∧
    ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
  let value := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
    (((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card : ZMod (base+2))
  (∀ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N), fits N G side p s →
    ∃ (send : (Fin N → Bool) → ↥img) (recv : ↥img → (Fin N → Bool) → ZMod (base+2)),
      ∀ a d, recv (send a) d = value N G (fun v => if side v then d v else a v)) ∧
  ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N)
    (onL : Left → Fin N → Bool) (onR : Right → Fin N → Bool),
    fits N G side p s ∧ (∀ f i, onL f (p i) = true) ∧ (∀ g j, onR g (s j) = true) ∧
    let out := fun (f : Left) (g : Right) =>
      value N G (fun v => if side v then onR g v else onL f v)
    (∀ f g, out f g = (Finset.univ : Finset ↥rk).sum (fun T => project f T * g T)) ∧
    ∀ (k : Nat) (rows : Fin k → Finset Left) (cols : Fin k → Finset Right)
      (guess : Fin k → Right → ZMod (base+2)),
      (∀ f g, ∃! i, f ∈ rows i ∧ g ∈ cols i) →
      (∀ i, ∀ f ∈ rows i, ∀ g ∈ cols i, guess i g = out f g) →
      img.card ≤ k) := by
  intro base l r L R C hLi hLs hRi hRs lk rk Left Right project img fits value
  refine ⟨?_, ?_⟩
  · intro N G side p s hf
    obtain ⟨-, -, hps, hss, -, hsym, hpL, hsR, hcross⟩ := hf
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    refine ⟨fun a => ⟨project (fun S => (PEqualNP.Outside.L_lib_1239.cL G side p a S.val :
      ZMod (base+2))), by exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩⟩,
      fun φ d => (Finset.univ : Finset ↥rk).sum (fun T => φ.val T *
        (PEqualNP.Outside.L_lib_1239.cR G side s d T.val : ZMod (base+2))), ?_⟩
    intro a d
    have := PEqualNP.Outside.L_lib_1239.total (n := base+2) G side p s C a d L R lk rk
      (fun S => by simp [lk]) (fun T => by simp [rk]) hps hss hsym hpL hsR hcross
    convert this.symm using 1
    · simp only [project]
      congr!
    · show ((Finset.univ.filter _).card : ZMod (base+2)) = _
      congr 1
      apply Finset.card_bij (fun I _ => I) ?_ (fun _ _ _ _ h => h) ?_
      · intro I hI
        rw [Finset.mem_filter] at hI ⊢
        refine ⟨Finset.mem_univ _, fun v hv => ?_, hI.2.2⟩
        have := hI.2.1 v hv
        revert this
        cases h : side v <;> simp [h]
      · intro I hI
        refine ⟨I, ?_, rfl⟩
        rw [Finset.mem_filter] at hI ⊢
        refine ⟨Finset.mem_univ _, fun v hv => ?_, hI.2.2⟩
        have := hI.2.1 v hv
        revert this
        cases h : side v <;> simp [h]
  · letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    obtain ⟨N, G, side, p, s, liveL, liveR, hpinj, hsinj, hps, hss, hirr, hsym, hpL, hsR, hcross,
      hlp, hls, hcL, hcR⟩ :=
      PEqualNP.Outside.L_lib_1239.construct (n := base+2) L R C hLi hLs hRi hRs
    have hlk : ∀ S, S ∈ lk ↔ ∀ i ∈ S, ∀ j ∈ L i, j ∉ S := fun S => by simp [lk]
    have hrk : ∀ T, T ∈ rk ↔ ∀ i ∈ T, ∀ j ∈ R i, j ∉ T := fun T => by simp [rk]
    have hexL := fun f : Left => PEqualNP.Outside.L_lib_1239.surj (n := base+2)
      (fun S => if h : S ∈ lk then f ⟨S, h⟩ - 1 else 0)
    have hexR := fun g : Right => PEqualNP.Outside.L_lib_1239.surj (n := base+2)
      (fun T => if h : T ∈ rk then g ⟨T, h⟩ - 1 else 0)
    choose mL hmL using hexL
    choose mR hmR using hexR
    have hfL : ∀ (f : Left) (S : ↥lk),
        (PEqualNP.Outside.L_lib_1239.cL G side p (liveL (mL f)) S.val : ZMod (base+2)) = f S := by
      intro f S
      have e1 : PEqualNP.Outside.L_lib_1239.cL G side p (liveL (mL f)) S.val =
          PEqualNP.Outside.L_lib_1239.cnt G side false p (liveL (mL f)) S.val := rfl
      rw [e1, hcL _ _ ((hlk _).1 S.2)]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      rw [hmL, dif_pos S.2]
      ring
    have hfR : ∀ (g : Right) (T : ↥rk),
        (PEqualNP.Outside.L_lib_1239.cR G side s (liveR (mR g)) T.val : ZMod (base+2)) = g T := by
      intro g T
      have e1 : PEqualNP.Outside.L_lib_1239.cR G side s (liveR (mR g)) T.val =
          PEqualNP.Outside.L_lib_1239.cnt G side true s (liveR (mR g)) T.val := rfl
      rw [e1, hcR _ _ ((hrk _).1 T.2)]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      rw [hmR, dif_pos T.2]
      ring
    refine ⟨N, G, side, p, s, fun f => liveL (mL f), fun g => liveR (mR g),
      ⟨hpinj, hsinj, hps, hss, hirr, hsym, hpL, hsR, hcross⟩, fun f i => hlp _ i,
      fun g j => hls _ j, ?_⟩
    intro out
    have hout : ∀ f g, out f g = (Finset.univ : Finset ↥rk).sum (fun T => project f T * g T) := by
      intro f g
      have := PEqualNP.Outside.L_lib_1239.total (n := base+2) G side p s C (liveL (mL f))
        (liveR (mR g)) L R lk rk hlk hrk hps hss hsym hpL hsR hcross
      simp only [hfL, hfR] at this
      convert this using 1
      · show ((Finset.univ.filter _).card : ZMod (base+2)) = _
        congr 1
        apply Finset.card_bij (fun I _ => I) ?_ (fun _ _ _ _ h => h) ?_
        · intro I hI
          rw [Finset.mem_filter] at hI ⊢
          refine ⟨Finset.mem_univ _, fun v hv => ?_, hI.2.2⟩
          have := hI.2.1 v hv
          revert this
          cases h : side v <;> simp [h]
        · intro I hI
          refine ⟨I, ?_, rfl⟩
          rw [Finset.mem_filter] at hI ⊢
          refine ⟨Finset.mem_univ _, fun v hv => ?_, hI.2.2⟩
          have := hI.2.1 v hv
          revert this
          cases h : side v <;> simp [h]
    refine ⟨hout, ?_⟩
    intro k rows cols guess hpart hcorr
    have hP : ∀ f f', project (f + f') = project f + project f' := fun f f' =>
      PEqualNP.Outside.L_lib_1239.proj_add
        (fun (S : ↥lk) (T : ↥rk) => ∀ i ∈ S.val, ∀ j ∈ C i, j ∉ T.val) f f'
    exact PEqualNP.Outside.L_lib_1239.lowerbound project hP k rows cols guess hpart
      (fun i f hf g hg => by rw [hcorr i f hf g hg, hout])
