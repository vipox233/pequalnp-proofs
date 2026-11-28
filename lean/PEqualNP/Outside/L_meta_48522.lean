import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48522

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

section ParityAndKyFan

open scoped Classical

private lemma card_even_of_involution {α : Type} [DecidableEq α] (S : Finset α) (f : α → α)
    (hmem : ∀ a ∈ S, f a ∈ S) (hinv : ∀ a ∈ S, f (f a) = a) (hne : ∀ a ∈ S, f a ≠ a) :
    S.card % 2 = 0 := by
  have hgen : ∀ n : ℕ, ∀ T : Finset α, T.card ≤ n →
      (∀ a ∈ T, f a ∈ T) → (∀ a ∈ T, f (f a) = a) → (∀ a ∈ T, f a ≠ a) → T.card % 2 = 0 := by
    intro n
    induction n with
    | zero =>
      intro T hle _ _ _
      have : T.card = 0 := Nat.eq_zero_of_le_zero hle
      omega
    | succ m ih =>
      intro T hle hm hi hn
      by_cases hemp : T = ∅
      · simp [hemp]
      · rcases Finset.nonempty_iff_ne_empty.mpr hemp with ⟨a, ha⟩
        let T' := (T.erase a).erase (f a)
        have hfa : f a ∈ T := hm a ha
        have hne_a : f a ≠ a := hn a ha
        have hfa_in : f a ∈ T.erase a := Finset.mem_erase.mpr ⟨hne_a, hfa⟩
        have hcard : T'.card + 2 = T.card := by
          have h1 : (T.erase a).card + 1 = T.card := Finset.card_erase_add_one ha
          have h2 : T'.card + 1 = (T.erase a).card := Finset.card_erase_add_one hfa_in
          omega
        have hm' : ∀ x ∈ T', f x ∈ T' := by
          intro x hx
          rcases Finset.mem_erase.mp hx with ⟨hx1, hx2⟩
          rcases Finset.mem_erase.mp hx2 with ⟨hx3, hxT⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hm x hxT⟩⟩
          · intro h; apply hx3; rw [← hi x hxT, h, hi a ha]
          · intro h; apply hx1; rw [← hi x hxT, h]
        have hi' : ∀ x ∈ T', f (f x) = x := fun x hx =>
          hi x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
        have hn' : ∀ x ∈ T', f x ≠ x := fun x hx =>
          hn x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
        have hsub := ih T' (by omega) hm' hi' hn'
        omega
  exact hgen S.card S le_rfl hmem hinv hne

private def SSet (d : ℕ) := Fin d → Option Bool

private instance (d : ℕ) : DecidableEq (SSet d) := inferInstanceAs (DecidableEq (Fin d → Option Bool))

private def flipS {d : ℕ} (s : SSet d) : SSet d := fun e => (s e).map (! ·)

private def leS {d : ℕ} (s₁ s₂ : SSet d) : Prop := ∀ e, s₁ e = none ∨ s₁ e = s₂ e

private def isNonemptyS {d : ℕ} (s : SSet d) : Prop := ∃ e, (s e).isSome = true

private def chainAt {d : ℕ} (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d) : SSet d :=
  fun e => if (π.symm e).val ≤ i.val then some (ε e) else none

private lemma chainAt_nonempty {d : ℕ} (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d) :
    isNonemptyS (chainAt π ε i) :=
  ⟨π i, by simp [chainAt]⟩

private lemma chainAt_mono {d : ℕ} (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) {i j : Fin d}
    (hij : i.val ≤ j.val) : leS (chainAt π ε i) (chainAt π ε j) := by
  intro e; unfold chainAt
  by_cases h : (π.symm e).val ≤ i.val
  · right; rw [if_pos h, if_pos (le_trans h hij)]
  · left; rw [if_neg h]

private lemma chainAt_flip {d : ℕ} (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d) :
    chainAt π (fun e => !(ε e)) i = flipS (chainAt π ε i) := by
  funext e; unfold chainAt flipS; dsimp only; split_ifs <;> rfl

private lemma signSeq_delete_parity {m : ℕ} (s : Fin (m + 1) → Bool) :
    let isAlt (t : ℕ → Bool) (len : ℕ) (first : Bool) : Prop :=
      ∀ r < len, t r = xor first (decide (r % 2 = 1))
    let del (j : Fin (m + 1)) (r : ℕ) : Bool :=
      if h : r < j.val then s ⟨r, lt_trans h j.isLt⟩
      else if h2 : r + 1 < m + 1 then s ⟨r + 1, h2⟩ else false
    let cnt := (Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true)).card
    cnt % 2 = (if isAlt (fun r => if h : r < m + 1 then s ⟨r, h⟩ else false) (m + 1) true then 1 else 0) +
              (if isAlt (fun r => if h : r < m + 1 then s ⟨r, h⟩ else false) (m + 1) false then 1 else 0) := by
  dsimp only
  let isAlt (t : ℕ → Bool) (len : ℕ) (first : Bool) : Prop :=
    ∀ r < len, t r = xor first (decide (r % 2 = 1))
  let del (j : Fin (m + 1)) (r : ℕ) : Bool :=
    if h : r < j.val then s ⟨r, lt_trans h j.isLt⟩
    else if h2 : r + 1 < m + 1 then s ⟨r + 1, h2⟩ else false
  let sf (r : ℕ) : Bool := if h : r < m + 1 then s ⟨r, h⟩ else false
  change (Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true)).card % 2 =
    (if isAlt sf (m + 1) true then 1 else 0) + (if isAlt sf (m + 1) false then 1 else 0)
  have halt_del : ∀ j : Fin (m + 1), isAlt (del j) m true ↔
      (∀ r (hr : r < j.val), s ⟨r, lt_trans hr j.isLt⟩ = xor true (decide (r % 2 = 1))) ∧
      (∀ r, j.val ≤ r → ∀ (hr : r < m), s ⟨r + 1, by omega⟩ = xor true (decide (r % 2 = 1))) := by
    intro j; constructor
    · intro h
      refine ⟨fun r hr => ?_, fun r hr1 hr2 => ?_⟩
      · have hjlt := j.isLt
        have h1 := h r (by omega); simp only [del, dif_pos hr] at h1; exact h1
      · have h1 := h r hr2; simp only [del, dif_neg (by omega : ¬ r < j.val), dif_pos (by omega : r + 1 < m + 1)] at h1; exact h1
    · rintro ⟨h1, h2⟩ r hr
      dsimp only [del]
      by_cases hlt : r < j.val
      · rw [dif_pos hlt]; exact h1 r hlt
      · rw [dif_neg hlt, dif_pos (by omega)]; exact h2 r (by omega) hr
  have hflip : ∀ r : ℕ, xor true (decide ((r + 1) % 2 = 1)) = !xor true (decide (r % 2 = 1)) := by
    intro r; by_cases h : r % 2 = 1
    · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
  have hflipF : ∀ r : ℕ, xor false (decide ((r + 1) % 2 = 1)) = xor true (decide (r % 2 = 1)) := by
    intro r; by_cases h : r % 2 = 1
    · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
  by_cases hT : isAlt sf (m + 1) true
  · have hF : ¬ isAlt sf (m + 1) false := by
      intro hf; have h1 := hT 0 (Nat.succ_pos m); have h2 := hf 0 (Nat.succ_pos m)
      simp at h1 h2; rw [h1] at h2; cases h2
    rw [if_pos hT, if_neg hF, add_zero]
    have hset : Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true) = {Fin.last m} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, halt_del]
      constructor
      · rintro ⟨_, h2⟩
        by_contra hne
        have hlt : j.val < m := by have := j.isLt; exact lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hne (Fin.ext h))
        have ha := h2 j.val le_rfl hlt
        have hb := hT (j.val + 1) (by omega)
        simp only [sf, dif_pos (by omega : j.val + 1 < m + 1)] at hb
        rw [ha, hflip] at hb; cases xor true (decide (j.val % 2 = 1)) <;> simp at hb
      · intro hj; subst hj
        refine ⟨fun r hr => ?_, fun r hr1 hr2 => by dsimp [Fin.last] at hr1; omega⟩
        have hb := hT r (by dsimp [Fin.last] at hr; omega)
        dsimp only [sf] at hb; rw [dif_pos (by dsimp [Fin.last] at hr; omega)] at hb; exact hb
    rw [hset, Finset.card_singleton]
  · by_cases hF : isAlt sf (m + 1) false
    · rw [if_neg hT, if_pos hF, zero_add]
      have hset : Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true) = {⟨0, Nat.succ_pos m⟩} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, halt_del]
        constructor
        · rintro ⟨h1, _⟩
          by_contra hne
          have hpos : 0 < j.val := Nat.pos_of_ne_zero fun h => hne (Fin.ext h)
          have ha := h1 0 hpos
          have hb := hF 0 (Nat.succ_pos m)
          simp only [sf, dif_pos (Nat.succ_pos m)] at hb
          rw [ha] at hb; simp at hb
        · intro hj; subst hj
          refine ⟨fun r hr => by simp at hr, fun r _ hr2 => ?_⟩
          have hb := hF (r + 1) (by omega)
          simp only [sf, dif_pos (by omega : r + 1 < m + 1)] at hb
          rw [hb, hflipF]
      rw [hset, Finset.card_singleton]
    · rw [if_neg hT, if_neg hF, add_zero]
      have hbad : ∃ r : Fin (m + 1), s r ≠ xor true (decide (r.val % 2 = 1)) := by
        by_contra hall; push_neg at hall; apply hT; intro r hr
        simp only [sf, dif_pos hr]; exact hall ⟨r, hr⟩
      let Sbad := Finset.univ.filter (fun r : Fin (m + 1) => s r ≠ xor true (decide (r.val % 2 = 1)))
      have hne_bad : Sbad.Nonempty := by
        rcases hbad with ⟨r, hr⟩; exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
      let r0 := Sbad.min' hne_bad
      have hr0_mem : r0 ∈ Sbad := Finset.min'_mem Sbad hne_bad
      have hr0_ne : s r0 ≠ xor true (decide (r0.val % 2 = 1)) := (Finset.mem_filter.mp hr0_mem).2
      have hr0_prev : ∀ r : Fin (m + 1), r < r0 → s r = xor true (decide (r.val % 2 = 1)) := by
        intro r hlt; by_contra hne
        have hmem : r ∈ Sbad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        exact not_lt_of_ge (Finset.min'_le Sbad r hmem) hlt
      by_cases h0 : r0.val = 0
      · have hs0 : s ⟨0, Nat.succ_pos m⟩ = false := by
          have : r0 = ⟨0, Nat.succ_pos m⟩ := Fin.ext h0
          rw [this] at hr0_ne
          have hmod0 : (0 : ℕ) % 2 ≠ 1 := by omega
          cases hb : s ⟨0, Nat.succ_pos m⟩
          · rfl
          · rw [hb, decide_eq_false hmod0] at hr0_ne; exact (hr0_ne rfl).elim
        have hemp : Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true) = ∅ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, halt_del]
          rintro ⟨h1, h2⟩
          by_cases hj0 : j.val = 0
          · apply hF; intro r hr
            simp only [sf, dif_pos hr]
            cases r with
            | zero => simpa using hs0
            | succ r' => rw [h2 r' (by omega) (by omega), hflipF]
          · have ha := h1 0 (by omega); rw [hs0] at ha; simp at ha
        rw [hemp, Finset.card_empty]
      · have hr0_pos : 0 < r0.val := Nat.pos_of_ne_zero h0
        let j1 : Fin (m + 1) := ⟨r0.val - 1, by omega⟩
        let j2 : Fin (m + 1) := r0
        have hj12 : j1 ≠ j2 := fun h => by
          have hv : j1.val = j2.val := congrArg Fin.val h
          change r0.val - 1 = r0.val at hv
          omega
        have honly : ∀ j : Fin (m + 1), isAlt (del j) m true → j = j1 ∨ j = j2 := by
          intro j hj; rcases (halt_del j).mp hj with ⟨h1, h2⟩
          by_contra hnor; push_neg at hnor
          by_cases hlt : j.val < r0.val - 1
          · have ha := h2 j.val le_rfl (by have := r0.isLt; omega)
            have hb := hr0_prev ⟨j.val + 1, by omega⟩ (by show j.val + 1 < r0.val; omega)
            rw [ha, hflip] at hb; cases xor true (decide (j.val % 2 = 1)) <;> simp at hb
          · have hgt : r0.val < j.val := by
              have hne1 : j.val ≠ r0.val - 1 := fun h => hnor.1 (Fin.ext h)
              have hne2 : j.val ≠ r0.val := fun h => hnor.2 (Fin.ext h)
              omega
            have ha := h1 r0.val hgt
            exact hr0_ne (by convert ha)
        have hsame : isAlt (del j1) m true ↔ isAlt (del j2) m true := by
          have heq_s : s j1 = s j2 := by
            have h1 := hr0_prev j1 (by show r0.val - 1 < r0.val; omega)
            have h2 := hr0_ne
            have hfl : xor true (decide (r0.val % 2 = 1)) = !xor true (decide ((r0.val - 1) % 2 = 1)) := by
              have := hflip (r0.val - 1); rwa [show r0.val - 1 + 1 = r0.val by omega] at this
            rw [hfl] at h2; rw [h1]
            cases hb : s j2 <;> cases hc : xor true (decide ((r0.val - 1) % 2 = 1)) <;> simp [j2, hb, hc] at h2 ⊢
          have hdel_eq : ∀ r < m, del j1 r = del j2 r := by
            intro r hr; dsimp only [del, j1, j2]
            by_cases h1 : r < r0.val - 1
            · rw [dif_pos h1, dif_pos (by omega)]
            · by_cases h2 : r = r0.val - 1
              · rw [dif_neg (by omega), dif_pos (by omega), dif_pos (by omega)]
                have he1 : (⟨r + 1, by omega⟩ : Fin (m + 1)) = j2 := Fin.ext (by dsimp [j2]; omega)
                have he2 : (⟨r, by omega⟩ : Fin (m + 1)) = j1 := Fin.ext (by dsimp [j1]; omega)
                rw [he1, he2, heq_s]
              · simp only [dif_neg (by omega : ¬ r < r0.val - 1), dif_neg (by omega : ¬ r < r0.val), dif_pos (by omega : r + 1 < m + 1)]
          exact ⟨fun h r hr => by rw [← hdel_eq r hr]; exact h r hr, fun h r hr => by rw [hdel_eq r hr]; exact h r hr⟩
        by_cases h1 : isAlt (del j1) m true
        · have hset : Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true) = {j1, j2} := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨honly j, fun h => by rcases h with rfl | rfl; exact h1; exact hsame.mp h1⟩
          rw [hset, Finset.card_pair hj12]
        · have hset : Finset.univ.filter (fun j : Fin (m + 1) => isAlt (del j) m true) = ∅ := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hj; rcases honly j hj with rfl | rfl
            · exact h1 hj
            · exact h1 (hsame.mpr hj)
          rw [hset, Finset.card_empty]

private def isAltLabels {m : ℕ} (f : Fin m → ℤ) (first : Bool) : Prop :=
  (∀ i j : Fin m, i ≠ j → (f i).natAbs ≠ (f j).natAbs) ∧
  (∀ i : Fin m,
    let rk := (Finset.univ.filter (fun j : Fin m => (f j).natAbs < (f i).natAbs)).card
    decide (0 < f i) = xor first (decide (rk % 2 = 1)))

private lemma isAltLabels_neg {m : ℕ} (f : Fin m → ℤ) (h0 : ∀ i, f i ≠ 0) (first : Bool) :
    isAltLabels (fun i => -f i) first ↔ isAltLabels f (!first) := by
  have hneg_pos : ∀ z : ℤ, z ≠ 0 → decide (0 < -z) = !decide (0 < z) := by
    intro z hz; by_cases h : 0 < z
    · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
  unfold isAltLabels
  simp only [Int.natAbs_neg]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [hneg_pos (f i) (h0 i)]
  generalize decide ((Finset.univ.filter (fun j : Fin m => (f j).natAbs < (f i).natAbs)).card % 2 = 1) = p
  cases first <;> cases decide (0 < f i) <;> cases p <;> simp

private lemma isAltLabels_del_parity {m : ℕ} (f : Fin (m + 1) → ℤ)
    (h0 : ∀ i, f i ≠ 0) (hnocomp : ∀ i j, f i ≠ -f j) :
    let delF (j : Fin (m + 1)) (i : Fin m) : ℤ := f (j.succAbove i)
    (Finset.univ.filter (fun j : Fin (m + 1) => isAltLabels (delF j) true)).card % 2 =
      ((if isAltLabels f true then 1 else 0) + (if isAltLabels f false then 1 else 0)) % 2 := by
  let delF (j : Fin (m + 1)) (i : Fin m) : ℤ := f (j.succAbove i)
  change (Finset.univ.filter (fun j : Fin (m + 1) => isAltLabels (delF j) true)).card % 2 =
    ((if isAltLabels f true then 1 else 0) + (if isAltLabels f false then 1 else 0)) % 2
  have heq_of_abs : ∀ i j : Fin (m + 1), (f i).natAbs = (f j).natAbs → f i = f j := by
    intro i j habs
    have hcases : f i = f j ∨ f i = -f j := Int.natAbs_eq_natAbs_iff.mp habs
    exact hcases.resolve_right (hnocomp i j)
  by_cases hinj : Function.Injective (fun i => (f i).natAbs)
  · have hlt_inj : ∀ i j : Fin (m + 1), i ≠ j → (f i).natAbs ≠ (f j).natAbs := fun i j hne h => hne (hinj h)
    let rk (i : Fin (m + 1)) : ℕ := (Finset.univ.filter (fun j : Fin (m + 1) => (f j).natAbs < (f i).natAbs)).card
    have hrk_lt : ∀ i : Fin (m + 1), rk i < m + 1 := fun i => by
      have h1 : rk i < (Finset.univ : Finset (Fin (m + 1))).card :=
        Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => (lt_irrefl _) (Finset.mem_filter.mp (hsub (Finset.mem_univ i))).2⟩
      rwa [Finset.card_univ, Fintype.card_fin] at h1
    have hrk_mono : ∀ i j : Fin (m + 1), (f i).natAbs < (f j).natAbs → rk i < rk j := fun i j hlt =>
      Finset.card_lt_card ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hx).2 hlt⟩,
        fun hsub => lt_irrefl _ (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))).2⟩
    let σ : Fin (m + 1) ≃ Fin (m + 1) :=
      Equiv.ofBijective (fun i => ⟨rk i, hrk_lt i⟩) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j h => by
        have hv : rk i = rk j := Fin.mk.inj h
        rcases lt_trichotomy (f i).natAbs (f j).natAbs with h1 | h2 | h3
        · exact absurd hv (ne_of_lt (hrk_mono i j h1))
        · exact hinj h2
        · exact absurd hv (ne_of_gt (hrk_mono j i h3)), by simp⟩)
    let s : Fin (m + 1) → Bool := fun r => decide (0 < f (σ.symm r))
    have hσ_lt : ∀ i j : Fin (m + 1), (f i).natAbs < (f j).natAbs ↔ (σ i).val < (σ j).val := fun i j => by
      constructor
      · exact hrk_mono i j
      · intro hlt
        rcases lt_trichotomy (f i).natAbs (f j).natAbs with h1 | h2 | h3
        · exact h1
        · rw [hinj h2] at hlt; exact absurd hlt (lt_irrefl _)
        · have := hrk_mono j i h3; exact absurd (lt_trans hlt this) (lt_irrefl _)
    have halt_iff : ∀ first : Bool, isAltLabels f first ↔
        (∀ r < m + 1, (if h : r < m + 1 then s ⟨r, h⟩ else false) = xor first (decide (r % 2 = 1))) := by
      intro first; constructor
      · rintro ⟨_, h2⟩ r hr
        simp only [dif_pos hr, s]
        have := h2 (σ.symm ⟨r, hr⟩)
        have hrk_eq : (Finset.univ.filter (fun j : Fin (m + 1) => (f j).natAbs < (f (σ.symm ⟨r, hr⟩)).natAbs)).card = r := by
          change (σ (σ.symm ⟨r, hr⟩)).val = r; simp
        rwa [hrk_eq] at this
      · intro h; refine ⟨hlt_inj, fun i => ?_⟩
        have h1 := h (σ i).val (σ i).isLt
        simp only [dif_pos (σ i).isLt, s, Fin.eta, Equiv.symm_apply_apply] at h1
        exact h1
    let delS (k : Fin (m + 1)) (r : ℕ) : Bool :=
      if h : r < k.val then s ⟨r, lt_trans h k.isLt⟩
      else if h2 : r + 1 < m + 1 then s ⟨r + 1, h2⟩ else false
    have hdel_iff : ∀ j : Fin (m + 1), isAltLabels (delF j) true ↔
        (∀ r < m, delS (σ j) r = xor true (decide (r % 2 = 1))) := by
      intro j
      have hcard_del : ∀ i : Fin m,
          (Finset.univ.filter (fun i' : Fin m => (f (j.succAbove i')).natAbs < (f (j.succAbove i)).natAbs)).card =
          if (σ (j.succAbove i)).val < (σ j).val then (σ (j.succAbove i)).val else (σ (j.succAbove i)).val - 1 := by
        intro i
        let a := j.succAbove i
        have haj : a ≠ j := Fin.succAbove_ne j i
        let A := Finset.univ.filter (fun x : Fin (m + 1) => (f x).natAbs < (f a).natAbs)
        have hbij : (Finset.univ.filter (fun i' : Fin m => (f (j.succAbove i')).natAbs < (f a).natAbs)).card = (A.erase j).card := by
          refine Finset.card_bij (fun i' _ => j.succAbove i') ?_ ?_ ?_
          · intro i' hi'; exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne j i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi').2⟩⟩
          · intro _ _ _ _ h; exact Fin.succAbove_right_injective h
          · intro x hx
            rcases Finset.mem_erase.mp hx with ⟨hxj, hxA⟩
            rcases Fin.exists_succAbove_eq hxj with ⟨i', rfl⟩
            exact ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxA).2⟩, rfl⟩
        rw [hbij]
        by_cases hlt : (σ a).val < (σ j).val
        · rw [if_pos hlt]
          have hnj : j ∉ A := by
            intro hj; have := (hσ_lt j a).mp (Finset.mem_filter.mp hj).2; omega
          rw [Finset.erase_eq_of_notMem hnj]; rfl
        · rw [if_neg hlt]
          have hgt : (σ j).val < (σ a).val := by
            have hne : (σ j).val ≠ (σ a).val := fun h => haj (σ.injective (Fin.ext h)).symm
            omega
          have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hσ_lt j a).mpr hgt⟩
          have h1 := Finset.card_erase_add_one hjA
          have hA : A.card = (σ (j.succAbove i)).val := rfl
          have hgt' : (σ j).val < (σ (j.succAbove i)).val := hgt
          rw [hA] at h1; omega
      constructor
      · rintro ⟨_, h2⟩ r hr
        dsimp only [delS]
        by_cases hlt : r < (σ j).val
        · rw [dif_pos hlt]
          let a := σ.symm ⟨r, lt_trans hlt (σ j).isLt⟩
          have haj : a ≠ j := fun h => by
            have := congrArg (fun x => (σ x).val) h; simp [a] at this; omega
          rcases Fin.exists_succAbove_eq haj with ⟨i, hi⟩
          have h2i := h2 i
          rw [hcard_del i, hi] at h2i
          have hσa : (σ a).val = r := by simp [a]
          rw [hσa, if_pos hlt] at h2i
          simpa [delF, hi, s, a] using h2i
        · rw [dif_neg hlt, dif_pos (by omega)]
          let a := σ.symm ⟨r + 1, by omega⟩
          have haj : a ≠ j := fun h => by
            have := congrArg (fun x => (σ x).val) h; simp [a] at this; omega
          rcases Fin.exists_succAbove_eq haj with ⟨i, hi⟩
          have h2i := h2 i
          rw [hcard_del i, hi] at h2i
          have hσa : (σ a).val = r + 1 := by simp [a]
          rw [hσa, if_neg (by omega), Nat.add_sub_cancel] at h2i
          simpa [delF, hi, s, a] using h2i
      · intro h
        refine ⟨fun i1 i2 hne => hlt_inj _ _ (fun heq => hne (Fin.succAbove_right_injective heq)), fun i => ?_⟩
        rw [hcard_del i]
        let a := j.succAbove i
        have haj : a ≠ j := Fin.succAbove_ne j i
        by_cases hlt : (σ a).val < (σ j).val
        · rw [if_pos hlt]
          have hr := h (σ a).val (by have := (σ j).isLt; omega)
          dsimp only [delS] at hr; rw [dif_pos hlt] at hr
          simpa [delF, a, s] using hr
        · rw [if_neg hlt]
          have hgt : (σ j).val < (σ a).val := by
            have hne : (σ j).val ≠ (σ a).val := fun e => haj (σ.injective (Fin.ext e)).symm
            omega
          have hr := h ((σ a).val - 1) (by have := (σ a).isLt; omega)
          dsimp only [delS] at hr
          rw [dif_neg (by omega), dif_pos (by have := (σ a).isLt; omega)] at hr
          have heq_f : (⟨(σ a).val - 1 + 1, by have := (σ a).isLt; omega⟩ : Fin (m + 1)) = σ a := Fin.ext (by dsimp; omega)
          rw [heq_f] at hr
          simpa [delF, a, s] using hr
    have hbij : (Finset.univ.filter (fun j : Fin (m + 1) => isAltLabels (delF j) true)).card =
        (Finset.univ.filter (fun k : Fin (m + 1) => ∀ r < m, delS k r = xor true (decide (r % 2 = 1)))).card := by
      refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
      · intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hdel_iff j).mp (Finset.mem_filter.mp hj).2⟩
      · intro _ _ _ _ h; exact σ.injective h
      · intro k hk; exact ⟨σ.symm k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hdel_iff (σ.symm k)).mpr (by simpa using (Finset.mem_filter.mp hk).2)⟩, by simp⟩
    have hpar := signSeq_delete_parity s
    rw [hbij, hpar, halt_iff true, halt_iff false]
    by_cases h1 : ∀ r < m + 1, (if h : r < m + 1 then s ⟨r, h⟩ else false) = xor true (decide (r % 2 = 1))
    · have h2 : ¬ ∀ r < m + 1, (if h : r < m + 1 then s ⟨r, h⟩ else false) = xor false (decide (r % 2 = 1)) := by
        intro hf; have a1 := h1 0 (Nat.succ_pos m); have a2 := hf 0 (Nat.succ_pos m); simp at a1 a2; rw [a1] at a2; cases a2
      rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2]
    · by_cases h2 : ∀ r < m + 1, (if h : r < m + 1 then s ⟨r, h⟩ else false) = xor false (decide (r % 2 = 1))
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
  · have hnotT : ¬ isAltLabels f true := fun h => hinj fun i j habs => by_contra fun hne => h.1 i j hne habs
    have hnotF : ¬ isAltLabels f false := fun h => hinj fun i j habs => by_contra fun hne => h.1 i j hne habs
    rw [if_neg hnotT, if_neg hnotF, add_zero, Nat.zero_mod]
    have hex : ∃ p q : Fin (m + 1), p ≠ q ∧ (f p).natAbs = (f q).natAbs := by
      by_contra hall; push_neg at hall; apply hinj; intro i j habs; by_contra hne; exact hall i j hne habs
    rcases hex with ⟨p, q, hpq, habs⟩
    have hf_eq : f p = f q := heq_of_abs p q habs
    have honly : ∀ j : Fin (m + 1), isAltLabels (delF j) true → j = p ∨ j = q := by
      intro j hj
      by_contra hnor; push_neg at hnor
      rcases Fin.exists_succAbove_eq hnor.1.symm with ⟨ip, hip⟩
      rcases Fin.exists_succAbove_eq hnor.2.symm with ⟨iq, hiq⟩
      have hne_i : ip ≠ iq := fun h => hpq (by rw [← hip, ← hiq, h])
      exact hj.1 ip iq hne_i (by dsimp only [delF]; rw [hip, hiq, habs])
    have hsame : isAltLabels (delF p) true ↔ isAltLabels (delF q) true := by
      have hperm : ∃ e : Fin m ≃ Fin m, ∀ i, delF p i = delF q (e i) := by
        let f1 : Fin m → {x : Fin (m + 1) // x ≠ p} := fun i => ⟨p.succAbove i, Fin.succAbove_ne p i⟩
        let f2 : Fin m → {x : Fin (m + 1) // x ≠ q} := fun i => ⟨q.succAbove i, Fin.succAbove_ne q i⟩
        have hb1 : Function.Bijective f1 := ⟨fun _ _ h => Fin.succAbove_right_injective (Subtype.ext_iff.mp h),
          fun ⟨x, hx⟩ => by rcases Fin.exists_succAbove_eq hx with ⟨i, rfl⟩; exact ⟨i, rfl⟩⟩
        have hb2 : Function.Bijective f2 := ⟨fun _ _ h => Fin.succAbove_right_injective (Subtype.ext_iff.mp h),
          fun ⟨x, hx⟩ => by rcases Fin.exists_succAbove_eq hx with ⟨i, rfl⟩; exact ⟨i, rfl⟩⟩
        let sw : {x : Fin (m + 1) // x ≠ p} ≃ {x : Fin (m + 1) // x ≠ q} :=
          { toFun := fun ⟨x, hx⟩ => ⟨Equiv.swap p q x, fun h => hx ((Equiv.swap p q).injective (by simpa [Equiv.swap_apply_left] using h))⟩
            invFun := fun ⟨x, hx⟩ => ⟨Equiv.swap p q x, fun h => hx ((Equiv.swap p q).injective (by simpa [Equiv.swap_apply_right] using h))⟩
            left_inv := fun ⟨x, _⟩ => Subtype.ext (Equiv.swap_apply_self p q x)
            right_inv := fun ⟨x, _⟩ => Subtype.ext (Equiv.swap_apply_self p q x) }
        let e : Fin m ≃ Fin m := ((Equiv.ofBijective f1 hb1).trans sw).trans (Equiv.ofBijective f2 hb2).symm
        refine ⟨e, fun i => ?_⟩
        have heq : q.succAbove (e i) = Equiv.swap p q (p.succAbove i) := by
          have := Equiv.apply_symm_apply (Equiv.ofBijective f2 hb2) (sw (Equiv.ofBijective f1 hb1 i))
          exact congrArg Subtype.val this
        dsimp only [delF]; rw [heq]
        by_cases hq' : p.succAbove i = q
        · rw [hq', Equiv.swap_apply_right, hf_eq]
        · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne p i) hq']
      rcases hperm with ⟨e, he⟩
      have hdir : ∀ (g1 g2 : Fin m → ℤ) (e' : Fin m ≃ Fin m), (∀ i, g1 i = g2 (e' i)) →
          isAltLabels g1 true → isAltLabels g2 true := by
        intro g1 g2 e' hge ⟨h1, h2⟩
        refine ⟨fun i1 i2 hne => ?_, fun i => ?_⟩
        · rw [← Equiv.apply_symm_apply e' i1, ← Equiv.apply_symm_apply e' i2, ← hge, ← hge]
          exact h1 _ _ (fun h => hne (by rw [← Equiv.apply_symm_apply e' i1, ← Equiv.apply_symm_apply e' i2, h]))
        · have h2i := h2 (e'.symm i)
          rw [hge, Equiv.apply_symm_apply] at h2i
          have hcard : (Finset.univ.filter (fun j : Fin m => (g1 j).natAbs < (g2 i).natAbs)).card =
              (Finset.univ.filter (fun j : Fin m => (g2 j).natAbs < (g2 i).natAbs)).card := by
            refine Finset.card_bij (fun j _ => e' j) ?_ (fun _ _ _ _ h => e'.injective h) ?_
            · intro j hj; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have := (Finset.mem_filter.mp hj).2; rwa [hge j] at this
            · intro j hj; refine ⟨e'.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Equiv.apply_symm_apply e' j⟩
              rw [hge, Equiv.apply_symm_apply]; exact (Finset.mem_filter.mp hj).2
          rwa [← hcard]
      exact ⟨hdir (delF p) (delF q) e he, hdir (delF q) (delF p) e.symm (fun i => by rw [he, Equiv.apply_symm_apply])⟩
    by_cases hp : isAltLabels (delF p) true
    · have hset : Finset.univ.filter (fun j : Fin (m + 1) => isAltLabels (delF j) true) = {p, q} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨honly j, fun h => by rcases h with rfl | rfl; exact hp; exact hsame.mp hp⟩
      rw [hset, Finset.card_pair hpq]
    · have hset : Finset.univ.filter (fun j : Fin (m + 1) => isAltLabels (delF j) true) = ∅ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hj; rcases honly j hj with rfl | rfl; exact hp hj; exact hp (hsame.mpr hj)
      rw [hset, Finset.card_empty]

private lemma kyFan_odd : ∀ d : ℕ, 1 ≤ d →
    ∀ (lam : SSet d → ℤ),
      (∀ s, isNonemptyS s → lam s ≠ 0) →
      (∀ s, isNonemptyS s → lam (flipS s) = -lam s) →
      (∀ s₁ s₂, isNonemptyS s₁ → leS s₁ s₂ → lam s₁ ≠ -lam s₂) →
      (Finset.univ.filter (fun p : Equiv.Perm (Fin d) × (Fin d → Bool) =>
        isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true)).card % 2 = 1 := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ m ih =>
    cases m with
    | zero =>
      intro _ lam h0 hanti _
      let sT : SSet 1 := fun _ => some true
      let sF : SSet 1 := fun _ => some false
      have hneT : isNonemptyS sT := ⟨0, rfl⟩
      have hflipT : flipS sT = sF := by funext e; rfl
      have hlamF : lam sF = -lam sT := by rw [← hflipT]; exact hanti sT hneT
      have h0T : lam sT ≠ 0 := h0 sT hneT
      have hfin1 : ∀ a b : Fin 1, a = b := fun a b => Fin.ext (by omega)
      have hcard : (Finset.univ.filter (fun p : Equiv.Perm (Fin 1) × (Fin 1 → Bool) =>
          isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true)).card = 1 := by
        by_cases hpos : 0 < lam sT
        · have hset : Finset.univ.filter (fun p : Equiv.Perm (Fin 1) × (Fin 1 → Bool) =>
              isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true) = {(Equiv.refl (Fin 1), fun _ => true)} := by
            ext ⟨π, ε⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            have hπ : π = Equiv.refl (Fin 1) := Equiv.ext fun x => hfin1 _ _
            subst hπ
            have hch : chainAt (Equiv.refl (Fin 1)) ε 0 = fun _ => some (ε 0) := by
              funext e; rw [hfin1 e 0]; simp [chainAt]
            constructor
            · rintro ⟨_, h2⟩
              have h20 := h2 0
              have hfilt : (Finset.univ.filter (fun j : Fin 1 => (lam (chainAt (Equiv.refl (Fin 1)) ε j)).natAbs < (lam (chainAt (Equiv.refl (Fin 1)) ε 0)).natAbs)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j _; rw [hfin1 j 0]; exact lt_irrefl _
              dsimp only at h20; rw [hfilt] at h20
              have hlam0 : lam (chainAt (Equiv.refl (Fin 1)) ε 0) = lam (fun _ => some (ε 0)) := congrArg lam hch
              simp only [hlam0] at h20
              cases hε : ε 0
              · have heq : (fun _ : Fin 1 => some (ε 0)) = sF := by funext e; rw [hε]
                simp only [heq, hlamF, decide_eq_false (by omega : ¬ 0 < -lam sT)] at h20; cases h20
              · exact Prod.ext rfl (funext fun e => by dsimp only; rw [hfin1 e 0, hε])
            · intro h; rcases Prod.mk.inj h with ⟨_, hε⟩; subst hε
              refine ⟨fun i j hne => (hne (hfin1 i j)).elim, fun i => ?_⟩
              rw [hfin1 i 0]
              have hfilt : (Finset.univ.filter (fun j : Fin 1 => (lam (chainAt (Equiv.refl (Fin 1)) (fun _ => true) j)).natAbs < (lam (chainAt (Equiv.refl (Fin 1)) (fun _ => true) 0)).natAbs)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j _; rw [hfin1 j 0]; exact lt_irrefl _
              dsimp only; rw [hfilt]
              have hlam0 : lam (chainAt (Equiv.refl (Fin 1)) (fun _ => true) 0) = lam sT := congrArg lam hch
              simp only [hlam0, decide_eq_true hpos]; decide
          rw [hset, Finset.card_singleton]
        · have hposF : 0 < lam sF := by rw [hlamF]; omega
          have hset : Finset.univ.filter (fun p : Equiv.Perm (Fin 1) × (Fin 1 → Bool) =>
              isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true) = {(Equiv.refl (Fin 1), fun _ => false)} := by
            ext ⟨π, ε⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            have hπ : π = Equiv.refl (Fin 1) := Equiv.ext fun x => hfin1 _ _
            subst hπ
            have hch : chainAt (Equiv.refl (Fin 1)) ε 0 = fun _ => some (ε 0) := by
              funext e; rw [hfin1 e 0]; simp [chainAt]
            constructor
            · rintro ⟨_, h2⟩
              have h20 := h2 0
              have hfilt : (Finset.univ.filter (fun j : Fin 1 => (lam (chainAt (Equiv.refl (Fin 1)) ε j)).natAbs < (lam (chainAt (Equiv.refl (Fin 1)) ε 0)).natAbs)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j _; rw [hfin1 j 0]; exact lt_irrefl _
              dsimp only at h20; rw [hfilt] at h20
              have hlam0 : lam (chainAt (Equiv.refl (Fin 1)) ε 0) = lam (fun _ => some (ε 0)) := congrArg lam hch
              simp only [hlam0] at h20
              cases hε : ε 0
              · exact Prod.ext rfl (funext fun e => by dsimp only; rw [hfin1 e 0, hε])
              · have heq : (fun _ : Fin 1 => some (ε 0)) = sT := by funext e; rw [hε]
                simp only [heq, decide_eq_false hpos] at h20; cases h20
            · intro h; rcases Prod.mk.inj h with ⟨_, hε⟩; subst hε
              refine ⟨fun i j hne => (hne (hfin1 i j)).elim, fun i => ?_⟩
              rw [hfin1 i 0]
              have hfilt : (Finset.univ.filter (fun j : Fin 1 => (lam (chainAt (Equiv.refl (Fin 1)) (fun _ => false) j)).natAbs < (lam (chainAt (Equiv.refl (Fin 1)) (fun _ => false) 0)).natAbs)).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j _; rw [hfin1 j 0]; exact lt_irrefl _
              dsimp only; rw [hfilt]
              have hlam0 : lam (chainAt (Equiv.refl (Fin 1)) (fun _ => false) 0) = lam sF := congrArg lam hch
              simp only [hlam0, decide_eq_true hposF]; decide
          rw [hset, Finset.card_singleton]
      rw [hcard]
    | succ d' =>
      intro _ lam h0 hanti hnocomp
      let last : Fin (d' + 2) := Fin.last (d' + 1)
      let Hplus : Finset (Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool)) :=
        Finset.univ.filter (fun p => p.2 last = true)
      let ridgeOk (p : Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool)) (j : Fin (d' + 2)) : Prop :=
        isAltLabels (fun i : Fin (d' + 1) => lam (chainAt p.1 p.2 (j.succAbove i))) true
      let Pairs := (Hplus ×ˢ (Finset.univ : Finset (Fin (d' + 2)))).filter (fun pj => ridgeOk pj.1 pj.2)
      have hLHS : Pairs.card % 2 = (Finset.univ.filter (fun p : Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool) =>
          isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true)).card % 2 := by
        have hsum : Pairs.card = ∑ p ∈ Hplus, (Finset.univ.filter (fun j : Fin (d' + 2) => ridgeOk p j)).card := by
          unfold Pairs
          rw [Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.card_filter]
        have hmod_sum : ∀ (S : Finset (Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool))) (f1 f2 : _ → ℕ),
            (∀ x ∈ S, f1 x % 2 = f2 x % 2) → (∑ x ∈ S, f1 x) % 2 = (∑ x ∈ S, f2 x) % 2 := by
          intro S f1 f2 heq
          induction S using Finset.induction_on with
          | empty => simp
          | insert a s ha ihs =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            have h1 := heq a (Finset.mem_insert_self a s)
            have h2 := ihs (fun x hx => heq x (Finset.mem_insert_of_mem hx))
            omega
        rw [hsum]
        have hstep := hmod_sum Hplus (fun p => (Finset.univ.filter (fun j : Fin (d' + 2) => ridgeOk p j)).card)
          (fun p => (if isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true then 1 else 0) +
                    (if isAltLabels (fun i => lam (chainAt p.1 p.2 i)) false then 1 else 0)) fun p _ => by
          refine isAltLabels_del_parity (fun i => lam (chainAt p.1 p.2 i))
            (fun i => h0 _ (chainAt_nonempty p.1 p.2 i)) fun i j => ?_
          by_cases hij : i.val ≤ j.val
          · exact hnocomp _ _ (chainAt_nonempty p.1 p.2 i) (chainAt_mono p.1 p.2 hij)
          · intro h
            have hji : j.val ≤ i.val := by omega
            exact hnocomp _ _ (chainAt_nonempty p.1 p.2 j) (chainAt_mono p.1 p.2 hji) (by linarith)
        rw [hstep, Finset.sum_add_distrib]
        have hA : (∑ p ∈ Hplus, if isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true then 1 else 0) =
            (Finset.univ.filter (fun p : Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool) =>
              p.2 last = true ∧ isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true)).card := by
          rw [Finset.card_filter]; simp only [Hplus, Finset.sum_filter]
          refine Finset.sum_congr rfl fun p _ => by split_ifs <;> simp_all
        have hB : (∑ p ∈ Hplus, if isAltLabels (fun i => lam (chainAt p.1 p.2 i)) false then 1 else 0) =
            (Finset.univ.filter (fun p : Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool) =>
              p.2 last = false ∧ isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true)).card := by
          rw [← Finset.card_filter]
          refine Finset.card_bij (fun p _ => (p.1, fun e => !(p.2 e))) ?_ ?_ ?_
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hpH, halt⟩
            have hlast : p.2 last = true := (Finset.mem_filter.mp hpH).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hlast], ?_⟩
            have hfn : (fun i => lam (chainAt p.1 (fun e => !(p.2 e)) i)) = fun i => -lam (chainAt p.1 p.2 i) := by
              funext i; rw [chainAt_flip, hanti _ (chainAt_nonempty p.1 p.2 i)]
            rw [hfn, isAltLabels_neg _ (fun i => h0 _ (chainAt_nonempty p.1 p.2 i))]; simpa using halt
          · intro p1 _ p2 _ heq
            rcases Prod.mk.inj heq with ⟨h1, h2⟩
            refine Prod.ext h1 (funext fun e => ?_)
            have he := congrFun h2 e
            cases h1e : p1.2 e <;> cases h2e : p2.2 e <;> simp [h1e, h2e] at he ⊢
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨_, hlast, halt⟩
            refine ⟨(p.1, fun e => !(p.2 e)), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hlast]⟩, ?_⟩,
              Prod.ext rfl (funext fun e => Bool.not_not _)⟩
            have hfn : (fun i => lam (chainAt p.1 (fun e => !(p.2 e)) i)) = fun i => -lam (chainAt p.1 p.2 i) := by
              funext i; rw [chainAt_flip, hanti _ (chainAt_nonempty p.1 p.2 i)]
            rw [hfn, isAltLabels_neg _ (fun i => h0 _ (chainAt_nonempty p.1 p.2 i))]; simpa using halt
        rw [hA, hB, ← Finset.card_union_of_disjoint]
        · congr 2; ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases p.2 last <;> simp
        · rw [Finset.disjoint_left]; intro p h1 h2
          have e1 := (Finset.mem_filter.mp h1).2.1; have e2 := (Finset.mem_filter.mp h2).2.1; rw [e1] at e2; cases e2
      let Bdry := Pairs.filter (fun pj => pj.2 = last ∧ pj.1.1 last = last)
      let Intr := Pairs.filter (fun pj => ¬ (pj.2 = last ∧ pj.1.1 last = last))
      have hsplit : Pairs.card = Bdry.card + Intr.card := (Finset.card_filter_add_card_filter_not _).symm
      have hIntr_even : Intr.card % 2 = 0 := by
        let ι : (Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool)) × Fin (d' + 2) →
                (Equiv.Perm (Fin (d' + 2)) × (Fin (d' + 2) → Bool)) × Fin (d' + 2) := fun ⟨⟨π, ε⟩, j⟩ =>
          if hj : j.val < d' + 1 then
            ((π * Equiv.swap j ⟨j.val + 1, by omega⟩, ε), j)
          else
            ((π, Function.update ε (π last) (!(ε (π last)))), j)
        refine card_even_of_involution Intr ι ?_ ?_ ?_
        · intro ⟨⟨π, ε⟩, j⟩ hmem
          rcases Finset.mem_filter.mp hmem with ⟨hP, hnotB⟩
          rcases Finset.mem_filter.mp hP with ⟨hProd, hOk⟩
          have hH : ε last = true := (Finset.mem_filter.mp (Finset.mem_product.mp hProd).1).2
          dsimp only [ι]
          by_cases hj : j.val < d' + 1
          · rw [dif_pos hj]
            have hne_j : j ≠ last := fun h => by subst h; dsimp [last, Fin.last] at hj; omega
            have hch_eq : ∀ i : Fin (d' + 1), chainAt (π * Equiv.swap j ⟨j.val + 1, by omega⟩) ε (j.succAbove i) = chainAt π ε (j.succAbove i) := by
              intro i; funext e; unfold chainAt
              have hsymm : (π * Equiv.swap j ⟨j.val + 1, by omega⟩).symm e = Equiv.swap j ⟨j.val + 1, by omega⟩ (π.symm e) := by
                simp [Equiv.Perm.mul_def]
              rw [hsymm]
              have hiff : (Equiv.swap j ⟨j.val + 1, by omega⟩ (π.symm e)).val ≤ (j.succAbove i).val ↔ (π.symm e).val ≤ (j.succAbove i).val := by
                have hne_sa : (j.succAbove i).val ≠ j.val := fun h => Fin.succAbove_ne j i (Fin.ext h)
                by_cases h1 : π.symm e = j
                · rw [h1, Equiv.swap_apply_left]; dsimp; omega
                · by_cases h2 : π.symm e = ⟨j.val + 1, by omega⟩
                  · rw [h2, Equiv.swap_apply_right]; dsimp; omega
                  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
              by_cases hc : (π.symm e).val ≤ (j.succAbove i).val
              · rw [if_pos (hiff.mpr hc), if_pos hc]
              · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH⟩, Finset.mem_univ _⟩, ?_⟩,
              fun h => hne_j h.1⟩
            dsimp only [ridgeOk]; simp_rw [hch_eq]; exact hOk
          · rw [dif_neg hj]
            have hjeq : j = last := Fin.ext (by have := j.isLt; dsimp [last, Fin.last]; omega)
            have hπne : π last ≠ last := fun h => hnotB ⟨hjeq, h⟩
            have hch_eq : ∀ i : Fin (d' + 1), chainAt π (Function.update ε (π last) (!(ε (π last)))) (j.succAbove i) = chainAt π ε (j.succAbove i) := by
              intro i; funext e; unfold chainAt
              by_cases he : e = π last
              · subst he; rw [Equiv.symm_apply_apply]
                have hne_val : (j.succAbove i).val ≠ last.val := fun h => by
                  have := Fin.succAbove_ne j i; exact this (Fin.ext (h.trans (congrArg Fin.val hjeq.symm)))
                have hlt : (j.succAbove i).val < last.val := by
                  have := (j.succAbove i).isLt; dsimp [last, Fin.last] at hne_val ⊢; omega
                rw [if_neg (by omega), if_neg (by omega)]
              · rw [Function.update_of_ne he]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩, ?_⟩,
              fun h => hπne h.2⟩
            · dsimp only; rw [Function.update_of_ne hπne.symm]; exact hH
            · dsimp only [ridgeOk]; simp_rw [hch_eq]; exact hOk
        · intro ⟨⟨π, ε⟩, j⟩ _
          dsimp only [ι]
          by_cases hj : j.val < d' + 1
          · rw [dif_pos hj, dif_pos hj]
            refine Prod.ext (Prod.ext ?_ rfl) rfl
            ext x; simp [Equiv.Perm.mul_def]
          · rw [dif_neg hj, dif_neg hj]
            refine Prod.ext (Prod.ext rfl ?_) rfl
            funext e
            by_cases he : e = π last
            · subst he; simp
            · simp [Function.update_of_ne he]
        · intro ⟨⟨π, ε⟩, j⟩ _
          dsimp only [ι]
          by_cases hj : j.val < d' + 1
          · rw [dif_pos hj]; intro h
            have hπ : π * Equiv.swap j ⟨j.val + 1, by omega⟩ = π := congrArg (fun x => x.1.1) h
            have hsw : (π * Equiv.swap j ⟨j.val + 1, by omega⟩) j = π j := congrArg (fun f => f j) hπ
            simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hsw
            have := congrArg Fin.val (π.injective hsw); dsimp at this; omega
          · rw [dif_neg hj]; intro h
            have hε : Function.update ε (π last) (!(ε (π last))) = ε := congrArg (fun x => x.1.2) h
            have hev := congrFun hε (π last)
            rw [Function.update_self] at hev; cases ε (π last) <;> simp at hev
      let embS (s : SSet (d' + 1)) : SSet (d' + 2) := fun e =>
        if h : e.val < d' + 1 then s ⟨e.val, h⟩ else none
      let lam' : SSet (d' + 1) → ℤ := fun s => lam (embS s)
      have hemb_ne : ∀ s, isNonemptyS s → isNonemptyS (embS s) := fun s ⟨e, he⟩ =>
        ⟨e.castSucc, by dsimp only [embS]; rw [dif_pos (by simp [e.isLt] : e.castSucc.val < d' + 1)]; simpa only [Fin.val_castSucc, Fin.eta] using he⟩
      have hemb_flip : ∀ s, embS (flipS s) = flipS (embS s) := fun s => by
        funext e; unfold embS flipS; dsimp only; split_ifs <;> rfl
      have hemb_le : ∀ s₁ s₂, leS s₁ s₂ → leS (embS s₁) (embS s₂) := fun s₁ s₂ h e => by
        unfold embS; split_ifs with he
        · exact h ⟨e.val, he⟩
        · exact Or.inl rfl
      have hIH := ih (Nat.succ_pos d') lam' (fun s hs => h0 _ (hemb_ne s hs))
        (fun s hs => by dsimp only [lam']; rw [hemb_flip]; exact hanti _ (hemb_ne s hs))
        (fun s₁ s₂ hs₁ hle => hnocomp _ _ (hemb_ne s₁ hs₁) (hemb_le s₁ s₂ hle))
      have hBdry_eq : Bdry.card = (Finset.univ.filter (fun p : Equiv.Perm (Fin (d' + 1)) × (Fin (d' + 1) → Bool) =>
          isAltLabels (fun i => lam' (chainAt p.1 p.2 i)) true)).card := by
        let extP (π' : Equiv.Perm (Fin (d' + 1))) : Equiv.Perm (Fin (d' + 2)) :=
          { toFun := fun e => if h : e.val < d' + 1 then (π' ⟨e.val, h⟩).castSucc else last
            invFun := fun e => if h : e.val < d' + 1 then (π'.symm ⟨e.val, h⟩).castSucc else last
            left_inv := fun e => by
              by_cases h : e.val < d' + 1
              · simp [h, (π' ⟨e.val, h⟩).isLt]
              · have he : e = last := Fin.ext (by have := e.isLt; dsimp [last, Fin.last]; omega)
                simp [h, last, Fin.last, he]
            right_inv := fun e => by
              by_cases h : e.val < d' + 1
              · simp [h, (π'.symm ⟨e.val, h⟩).isLt]
              · have he : e = last := Fin.ext (by have := e.isLt; dsimp [last, Fin.last]; omega)
                simp [h, last, Fin.last, he] }
        let extE (ε' : Fin (d' + 1) → Bool) : Fin (d' + 2) → Bool :=
          fun e => if h : e.val < d' + 1 then ε' ⟨e.val, h⟩ else true
        have hch_emb : ∀ π' ε' (i : Fin (d' + 1)),
            chainAt (extP π') (extE ε') (last.succAbove i) = embS (chainAt π' ε' i) := by
          intro π' ε' i; funext e; unfold chainAt embS extP extE
          have hsa : last.succAbove i = i.castSucc := congrFun (Fin.succAbove_last) i
          rw [hsa]
          by_cases h : e.val < d' + 1
          · simp only [h, ↓reduceDIte, Equiv.coe_fn_symm_mk, Fin.val_castSucc]
          · simp only [h, ↓reduceDIte, Equiv.coe_fn_symm_mk]
            have hlt : ¬ last.val ≤ i.castSucc.val := by dsimp [last, Fin.last]; omega
            rw [if_neg hlt]
        symm
        refine Finset.card_bij (fun p _ => ((extP p.1, extE p.2), last)) ?_ ?_ ?_
        · intro ⟨π', ε'⟩ hp
          have halt := (Finset.mem_filter.mp hp).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩, ?_⟩, rfl, ?_⟩
          · dsimp only [extE, last, Fin.last]; rw [dif_neg (by omega)]
          · dsimp only [ridgeOk]; simp_rw [hch_emb]; exact halt
          · dsimp only [extP, Equiv.coe_fn_mk, last, Fin.last]; rw [dif_neg (by omega)]
        · intro ⟨π1, ε1⟩ _ ⟨π2, ε2⟩ _ heq
          have hp := congrArg (fun x => x.1.1) heq
          have hε := congrArg (fun x => x.1.2) heq
          refine Prod.ext (Equiv.ext fun x => ?_) (funext fun x => ?_)
          · have hx := congrArg (fun f => f x.castSucc) hp
            dsimp only [extP, Equiv.coe_fn_mk] at hx
            simp only [Fin.val_castSucc, x.isLt, ↓reduceDIte] at hx
            exact Fin.ext (Fin.mk.inj hx)
          · have hx := congrFun hε x.castSucc
            dsimp only [extE] at hx
            simp only [Fin.val_castSucc, x.isLt, ↓reduceDIte] at hx; exact hx
        · intro ⟨⟨π, ε⟩, j⟩ hmem
          rcases Finset.mem_filter.mp hmem with ⟨hP, rfl, hπlast⟩
          rcases Finset.mem_filter.mp hP with ⟨hProd, hOk⟩
          have hH : ε last = true := (Finset.mem_filter.mp (Finset.mem_product.mp hProd).1).2
          have hπlt : ∀ e : Fin (d' + 1), (π e.castSucc).val < d' + 1 := by
            intro e; have hne : π e.castSucc ≠ last := fun h => by
              have := π.injective (h.trans hπlast.symm); have := congrArg Fin.val this; dsimp [last, Fin.last] at this; omega
            have := (π e.castSucc).isLt; by_contra hge; apply hne; exact Fin.ext (by dsimp [last, Fin.last]; omega)
          have hπslt : ∀ e : Fin (d' + 1), (π.symm e.castSucc).val < d' + 1 := by
            intro e; have hne : π.symm e.castSucc ≠ last := fun h => by
              have := congrArg π h; rw [Equiv.apply_symm_apply, hπlast] at this
              have := congrArg Fin.val this; dsimp [last, Fin.last] at this; omega
            have := (π.symm e.castSucc).isLt; by_contra hge; apply hne; exact Fin.ext (by dsimp [last, Fin.last]; omega)
          let π' : Equiv.Perm (Fin (d' + 1)) :=
            { toFun := fun e => ⟨(π e.castSucc).val, hπlt e⟩
              invFun := fun e => ⟨(π.symm e.castSucc).val, hπslt e⟩
              left_inv := fun e => Fin.ext (by dsimp; rw [Equiv.symm_apply_apply]; rfl)
              right_inv := fun e => Fin.ext (by dsimp; rw [Equiv.apply_symm_apply]; rfl) }
          let ε' : Fin (d' + 1) → Bool := fun e => ε e.castSucc
          have hpeq : extP π' = π := by
            ext e; dsimp only [extP, π', Equiv.coe_fn_mk]
            by_cases h : e.val < d' + 1
            · rw [dif_pos h]; rfl
            · rw [dif_neg h]
              have he : e = last := Fin.ext (by have := e.isLt; dsimp [last, Fin.last]; omega)
              rw [he, hπlast]
          have hεeq : extE ε' = ε := by
            funext e; dsimp only [extE, ε']
            by_cases h : e.val < d' + 1
            · rw [dif_pos h]; rfl
            · rw [dif_neg h]
              have he : e = last := Fin.ext (by have := e.isLt; dsimp [last, Fin.last]; omega)
              rw [he, hH]
          refine ⟨(π', ε'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext (Prod.ext hpeq hεeq) rfl⟩
          dsimp only [ridgeOk] at hOk
          rw [← hpeq, ← hεeq] at hOk
          simp_rw [hch_emb] at hOk; exact hOk
      rw [← hLHS, hsplit, hBdry_eq]; omega

private lemma octahedral_tucker {d M : ℕ} (hd : 1 ≤ d) (lam : SSet d → ℤ)
    (h0 : ∀ s, isNonemptyS s → lam s ≠ 0)
    (hbnd : ∀ s, isNonemptyS s → (lam s).natAbs ≤ M)
    (hanti : ∀ s, isNonemptyS s → lam (flipS s) = -lam s)
    (hnocomp : ∀ s₁ s₂, isNonemptyS s₁ → leS s₁ s₂ → lam s₁ ≠ -lam s₂) :
    d ≤ M := by
  have hodd := kyFan_odd d hd lam h0 hanti hnocomp
  have hpos : 0 < (Finset.univ.filter (fun p : Equiv.Perm (Fin d) × (Fin d → Bool) =>
      isAltLabels (fun i => lam (chainAt p.1 p.2 i)) true)).card := by omega
  rcases Finset.card_pos.mp hpos with ⟨⟨π, ε⟩, hp⟩
  have halt := (Finset.mem_filter.mp hp).2
  let vals : Finset ℕ := Finset.univ.image (fun i : Fin d => (lam (chainAt π ε i)).natAbs)
  have hcard_vals : vals.card = d := by
    rw [Finset.card_image_of_injective _ (fun i j heq => by_contra fun hne => halt.1 i j hne heq)]
    simp
  have hsub : vals ⊆ Finset.Icc 1 M := by
    intro v hv; rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    have h1 := h0 _ (chainAt_nonempty π ε i)
    have h2 := hbnd _ (chainAt_nonempty π ε i)
    exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr h1, h2⟩
  have hle := Finset.card_le_card hsub
  rw [hcard_vals, Nat.card_Icc] at hle
  omega

end ParityAndKyFan

section TwoShoreAndShrink

open scoped Classical

private def runsG {α : Type} (g : Finset α → α → Bool) : ℕ → Finset α → Prop
  | 0, _ => True
  | m + 1, x => ∃ u v : Finset α, ∃ j : α, runsG g m u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false

private lemma runsG_mono_x {α : Type} {g : Finset α → α → Bool} {m : ℕ} {x y : Finset α}
    (hxy : x ⊆ y) (h : runsG g m x) : runsG g m y := by
  cases m with
  | zero => trivial
  | succ m =>
    rcases h with ⟨u, v, j, hm, huv, hvx, hgu, hgv⟩
    exact ⟨u, v, j, hm, huv, hvx.trans hxy, hgu, hgv⟩

private lemma runsG_anti_m {α : Type} {g : Finset α → α → Bool} {m₁ m₂ : ℕ}
    (hle : m₁ ≤ m₂) {x : Finset α} (h : runsG g m₂ x) : runsG g m₁ x := by
  induction m₂ generalizing m₁ x with
  | zero =>
    have : m₁ = 0 := by omega
    subst this; trivial
  | succ m₂ ih =>
    by_cases hlt : m₁ ≤ m₂
    · rcases h with ⟨u, v, _, hm, huv, hvx, _, _⟩
      exact runsG_mono_x (huv.trans hvx) (ih hlt hm)
    · have : m₁ = m₂ + 1 := by omega
      subst this; exact h

private lemma testBit_add_two_pow (p : ℕ) :
    ∀ (x k : ℕ), x.testBit p = false → (x + 2 ^ p).testBit k = if k = p then true else x.testBit k := by
  induction p with
  | zero =>
    intro x k hx
    have hev : x % 2 = 0 := by rw [Nat.testBit_zero] at hx; simpa using hx
    cases k with
    | zero => rw [if_pos rfl, pow_zero, Nat.testBit_zero]; simp [Nat.add_mod, hev]
    | succ k' =>
      rw [if_neg (Nat.succ_ne_zero k'), pow_zero, Nat.testBit_succ, Nat.testBit_succ]
      have hdiv : (x + 1) / 2 = x / 2 := by omega
      rw [hdiv]
  | succ p' ih =>
    intro x k hx
    rw [Nat.testBit_succ] at hx
    cases k with
    | zero =>
      rw [if_neg (Ne.symm (Nat.succ_ne_zero p')), Nat.testBit_zero, Nat.testBit_zero]
      have hpow : 2 ^ (p' + 1) = 2 * 2 ^ p' := by rw [pow_succ]; ring
      rw [hpow]; simp [Nat.add_mod]
    | succ k' =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have hpow : 2 ^ (p' + 1) = 2 * 2 ^ p' := by rw [pow_succ]; ring
      have hdiv : (x + 2 ^ (p' + 1)) / 2 = x / 2 + 2 ^ p' := by rw [hpow]; omega
      rw [hdiv, ih (x / 2) k' hx]
      by_cases h : k' = p'
      · subst h; simp
      · simp [h]

private lemma testBit_sum_two_pow (T : Finset ℕ) (k : ℕ) :
    (∑ b ∈ T, 2 ^ b).testBit k = decide (k ∈ T) := by
  induction T using Finset.induction_on generalizing k with
  | empty => simp
  | @insert c T hc ih =>
    rw [Finset.sum_insert hc, Nat.add_comm]
    have h0 : (∑ b ∈ T, 2 ^ b).testBit c = false := by rw [ih c]; simp [hc]
    rw [testBit_add_two_pow c _ k h0, ih k]
    by_cases hck : k = c
    · subst hck; simp
    · simp [hck]

private lemma codeF_injective {α : Type} [Fintype α] [DecidableEq α] (e : α ≃ Fin (Fintype.card α)) :
    Function.Injective (fun S : Finset α => ∑ i ∈ S, 2 ^ (e i).val) := by
  intro S₁ S₂ heq
  dsimp only at heq
  have hmap : ∀ S : Finset α, ∑ i ∈ S, 2 ^ (e i).val = ∑ a ∈ S.image (fun i => (e i).val), 2 ^ a := by
    intro S
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact e.injective (Fin.ext hxy)
  rw [hmap S₁, hmap S₂] at heq
  ext i
  have h1 := testBit_sum_two_pow (S₁.image (fun j => (e j).val)) (e i).val
  have h2 := testBit_sum_two_pow (S₂.image (fun j => (e j).val)) (e i).val
  rw [heq] at h1
  have hdec : decide ((e i).val ∈ S₁.image (fun j => (e j).val)) =
      decide ((e i).val ∈ S₂.image (fun j => (e j).val)) := h1.symm.trans h2
  have hiff : (e i).val ∈ S₁.image (fun j => (e j).val) ↔ (e i).val ∈ S₂.image (fun j => (e j).val) := by
    simpa [decide_eq_true_eq] using congrArg (· = true) hdec
  simp only [Finset.mem_image] at hiff
  constructor
  · intro hi
    rcases hiff.mp ⟨i, hi, rfl⟩ with ⟨j, hj, hje⟩
    have : j = i := e.injective (Fin.ext hje)
    rwa [← this]
  · intro hi
    rcases hiff.mpr ⟨i, hi, rfl⟩ with ⟨j, hj, hje⟩
    have : j = i := e.injective (Fin.ext hje)
    rwa [← this]

private lemma two_shore_runs {k t : ℕ} (ht : 0 < t) (h2tk : 2 * t < k)
    (g : Finset {s : Finset (Fin (2 * k + 2 * t)) // s.card = k} →
      {s : Finset (Fin (2 * k + 2 * t)) // s.card = k} → Bool)
    (hfits : (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → g x j = true) ∧
             (∀ x j, j ∈ x → g x j = false))
    (hdec : ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true) :
    ∃ A B : Finset (Fin (2 * k + 2 * t)),
      Disjoint A B ∧ k ≤ B.card ∧
      runsG g (t + 1) (Finset.univ.filter fun i : {s : Finset (Fin (2 * k + 2 * t)) // s.card = k} => i.val ⊆ A) := by
  let d := 2 * k + 2 * t
  let K := {s : Finset (Fin d) // s.card = k}
  by_contra hnone
  push_neg at hnone
  let U (A : Finset (Fin d)) : Finset K := Finset.univ.filter fun i : K => i.val ⊆ A
  have hU_mono : ∀ A B, A ⊆ B → U A ⊆ U B := fun A B hAB i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans hAB⟩
  have hU_nonempty : ∀ A : Finset (Fin d), k ≤ A.card → (U A).Nonempty := fun A hA => by
    rcases Finset.exists_subset_card_eq hA with ⟨S, hSA, hSc⟩
    exact ⟨⟨S, hSc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSA⟩⟩
  let rk (x : Finset K) : ℕ :=
    ((Finset.range (t + 2)).filter fun m => runsG g m x).max'
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), trivial⟩⟩
  have hrk_mem : ∀ x, runsG g (rk x) x ∧ rk x ≤ t + 1 := fun x => by
    have hmem := Finset.max'_mem ((Finset.range (t + 2)).filter fun m => runsG g m x)
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), trivial⟩⟩
    rcases Finset.mem_filter.mp hmem with ⟨hr, hrun⟩
    exact ⟨hrun, Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)⟩
  have hrk_ge : ∀ x m, m ≤ t + 1 → runsG g m x → m ≤ rk x := fun x m hmt hm =>
    Finset.le_max' _ m (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm⟩)
  have hrk_mono : ∀ x y, x ⊆ y → rk x ≤ rk y := fun x y hxy =>
    hrk_ge y (rk x) (hrk_mem x).2 (runsG_mono_x hxy (hrk_mem x).1)
  have hrk_pos_of_k : ∀ A : Finset (Fin d), k ≤ A.card → 1 ≤ rk (U A) := fun A hA => by
    rcases hU_nonempty A hA with ⟨i, hi⟩
    have hr1 : runsG g 1 (U A) := ⟨∅, U A, i, trivial, Finset.empty_subset _, Finset.Subset.refl _,
      hfits.1 ∅ i (fun _ h => by simp at h), hfits.2 (U A) i hi⟩
    exact hrk_ge (U A) 1 (by omega) hr1
  have hrk_le_t_of_disj : ∀ A B : Finset (Fin d), Disjoint A B → k ≤ B.card → rk (U A) ≤ t := by
    intro A B hdisj hB
    have hnoA : ¬ runsG g (t + 1) (U A) := hnone A B hdisj hB
    have hmem := hrk_mem (U A)
    by_contra hgt
    have heq : rk (U A) = t + 1 := by omega
    rw [heq] at hmem
    exact hnoA hmem.1
  let F (x : Finset K) : Finset K := Finset.univ.filter fun j => g x j = false
  have hF_const : ∀ x y, x ⊆ y → rk x = rk y → rk x ≤ t → F x = F y := by
    intro x y hxy heq hlt
    ext j; simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hgx; by_contra hgy
      have hgt : g y j = true := Bool.eq_true_of_not_eq_false hgy
      have hxt := hdec x y hxy j hgt; rw [hgx] at hxt; cases hxt
    · intro hgy; by_contra hgx
      have hxt : g x j = true := Bool.eq_true_of_not_eq_false hgx
      have hrun : runsG g (rk x + 1) y := ⟨x, y, j, (hrk_mem x).1, hxy, Finset.Subset.refl _, hxt, hgy⟩
      have := hrk_ge y (rk x + 1) (by omega) hrun; omega
  let posS (s : SSet d) : Finset (Fin d) := Finset.univ.filter fun e => s e = some true
  let negS (s : SSet d) : Finset (Fin d) := Finset.univ.filter fun e => s e = some false
  let suppS (s : SSet d) : Finset (Fin d) := Finset.univ.filter fun e => (s e).isSome = true
  have hdisj_pn : ∀ s : SSet d, Disjoint (posS s) (negS s) := fun s => by
    rw [Finset.disjoint_left]; intro e h1 h2
    have e1 := (Finset.mem_filter.mp h1).2; have e2 := (Finset.mem_filter.mp h2).2; rw [e1] at e2; cases e2
  have hsupp_eq : ∀ s : SSet d, suppS s = posS s ∪ negS s := fun s => by
    ext e; simp only [suppS, posS, negS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases s e with | none => simp | some b => cases b <;> simp
  have hsupp_card : ∀ s : SSet d, (suppS s).card = (posS s).card + (negS s).card := fun s => by
    rw [hsupp_eq s, Finset.card_union_of_disjoint (hdisj_pn s)]
  have hflip_pn : ∀ s : SSet d, posS (flipS s) = negS s ∧ negS (flipS s) = posS s ∧ suppS (flipS s) = suppS s := fun s => by
    refine ⟨?_, ?_, ?_⟩
    · ext e; simp only [posS, negS, flipS, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : s e with | none => simp [h] | some b => cases b <;> simp [h]
    · ext e; simp only [posS, negS, flipS, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : s e with | none => simp [h] | some b => cases b <;> simp [h]
    · ext e; simp only [suppS, flipS, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : s e with | none => simp [h] | some b => cases b <;> simp [h]
  have hF_ne : ∀ s : SSet d, k ≤ (posS s).card → F (U (posS s)) ≠ F (U (negS s)) := by
    intro s hp heq
    rcases hU_nonempty (posS s) hp with ⟨a, ha⟩
    have haF : a ∈ F (U (posS s)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfits.2 _ _ ha⟩
    rw [heq] at haF
    have haF2 : g (U (negS s)) a = false := (Finset.mem_filter.mp haF).2
    have htrue : g (U (negS s)) a = true := hfits.1 _ _ fun i hi =>
      (hdisj_pn s).symm.mono (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp ha).2
    rw [htrue] at haF2; cases haF2
  let eK : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let codeF (S : Finset K) : ℕ := ∑ i ∈ S, 2 ^ (eK i).val
  have hcodeF_inj : Function.Injective codeF := codeF_injective eK
  let lam (s : SSet d) : ℤ :=
    if hp : k ≤ (posS s).card then
      if hn : k ≤ (negS s).card then
        let mag : ℤ := ((2 * k - 2 + rk (U (posS s)) + rk (U (negS s)) : ℕ) : ℤ)
        if codeF (F (U (posS s))) < codeF (F (U (negS s))) then mag else -mag
      else ((2 * k - 1 : ℕ) : ℤ)
    else if hn : k ≤ (negS s).card then
      -((2 * k - 1 : ℕ) : ℤ)
    else if hne : (suppS s).Nonempty then
      if s ((suppS s).min' hne) = some true then ((suppS s).card : ℤ) else -((suppS s).card : ℤ)
    else 0
  have hlam_0 : ∀ s, isNonemptyS s → lam s ≠ 0 := by
    intro s ⟨e, he⟩
    have hne : (suppS s).Nonempty := ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    have hpos_card : 0 < (suppS s).card := Finset.card_pos.mpr hne
    dsimp only [lam]
    by_cases hp : k ≤ (posS s).card
    · by_cases hn : k ≤ (negS s).card
      · rw [dif_pos hp, dif_pos hn]; split_ifs <;> omega
      · rw [dif_pos hp, dif_neg hn]; omega
    · by_cases hn : k ≤ (negS s).card
      · rw [dif_neg hp, dif_pos hn]; omega
      · rw [dif_neg hp, dif_neg hn, dif_pos hne]; split_ifs <;> omega
  have hlam_bnd : ∀ s, isNonemptyS s → (lam s).natAbs ≤ d - 2 := by
    intro s ⟨e, he⟩
    have hne : (suppS s).Nonempty := ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    dsimp only [lam]
    by_cases hp : k ≤ (posS s).card
    · by_cases hn : k ≤ (negS s).card
      · rw [dif_pos hp, dif_pos hn]
        have h1 := hrk_le_t_of_disj (posS s) (negS s) (hdisj_pn s) hn
        have h2 := hrk_le_t_of_disj (negS s) (posS s) (hdisj_pn s).symm hp
        split_ifs <;> simp <;> omega
      · rw [dif_pos hp, dif_neg hn]; simp; omega
    · by_cases hn : k ≤ (negS s).card
      · rw [dif_neg hp, dif_pos hn]; simp; omega
      · rw [dif_neg hp, dif_neg hn, dif_pos hne]
        have hsum := hsupp_card s
        split_ifs <;> simp <;> omega
  have hlam_anti : ∀ s, isNonemptyS s → lam (flipS s) = -lam s := by
    intro s ⟨e, he⟩
    have hne : (suppS s).Nonempty := ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    rcases hflip_pn s with ⟨hfp, hfn, hfsp⟩
    have hne' : (suppS (flipS s)).Nonempty := hfsp ▸ hne
    dsimp only [lam]
    by_cases hp : k ≤ (posS s).card
    · by_cases hn : k ≤ (negS s).card
      · rw [dif_pos (by rw [hfp]; exact hn), dif_pos (by rw [hfn]; exact hp), dif_pos hp, dif_pos hn, hfp, hfn]
        have hneF : F (U (posS s)) ≠ F (U (negS s)) := hF_ne s hp
        have hneC : codeF (F (U (posS s))) ≠ codeF (F (U (negS s))) := fun h => hneF (hcodeF_inj h)
        have hmag : ((2 * k - 2 + rk (U (negS s)) + rk (U (posS s)) : ℕ) : ℤ) =
            ((2 * k - 2 + rk (U (posS s)) + rk (U (negS s)) : ℕ) : ℤ) := by omega
        rw [hmag]
        by_cases hlt : codeF (F (U (posS s))) < codeF (F (U (negS s)))
        · rw [if_pos hlt, if_neg (by omega)]
        · rw [if_neg hlt, if_pos (by omega), neg_neg]
      · rw [dif_neg (by rw [hfp]; exact hn), dif_pos (by rw [hfn]; exact hp), dif_pos hp, dif_neg hn]
    · by_cases hn : k ≤ (negS s).card
      · rw [dif_pos (by rw [hfp]; exact hn), dif_neg (by rw [hfn]; exact hp), dif_neg hp, dif_pos hn, neg_neg]
      · rw [dif_neg (by rw [hfp]; exact hn), dif_neg (by rw [hfn]; exact hp), dif_pos hne',
          dif_neg hp, dif_neg hn, dif_pos hne]
        have hmin_eq : (suppS (flipS s)).min' hne' = (suppS s).min' hne := by simp only [hfsp]
        rw [hmin_eq, hfsp]
        have hmem : (suppS s).min' hne ∈ suppS s := Finset.min'_mem _ hne
        have hsome : (s ((suppS s).min' hne)).isSome = true := (Finset.mem_filter.mp hmem).2
        dsimp only [flipS]
        have hfl : ∀ (o : Option Bool) (c : ℤ), o.isSome = true →
            (if o.map (! ·) = some true then c else -c) = -(if o = some true then c else -c) := fun o c ho => by
          cases o with | none => cases ho | some b => cases b <;> simp
        exact hfl (s ((suppS s).min' hne)) ((suppS s).card : ℤ) hsome
  have hlam_nocomp : ∀ s₁ s₂, isNonemptyS s₁ → leS s₁ s₂ → lam s₁ ≠ -lam s₂ := by
    intro s₁ s₂ ⟨e₁, he₁⟩ hle heq
    have hne₁ : (suppS s₁).Nonempty := ⟨e₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₁⟩⟩
    have hsub_p : posS s₁ ⊆ posS s₂ := fun e he => by
      have h1 : s₁ e = some true := (Finset.mem_filter.mp he).2
      rcases hle e with h0 | hs
      · rw [h1] at h0; cases h0
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.symm.trans h1⟩
    have hsub_n : negS s₁ ⊆ negS s₂ := fun e he => by
      have h1 : s₁ e = some false := (Finset.mem_filter.mp he).2
      rcases hle e with h0 | hs
      · rw [h1] at h0; cases h0
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.symm.trans h1⟩
    have hsub_s : suppS s₁ ⊆ suppS s₂ := by rw [hsupp_eq, hsupp_eq]; exact Finset.union_subset_union hsub_p hsub_n
    have hne₂ : (suppS s₂).Nonempty := hne₁.mono hsub_s
    have hcp : (posS s₁).card ≤ (posS s₂).card := Finset.card_le_card hsub_p
    have hcn : (negS s₁).card ≤ (negS s₂).card := Finset.card_le_card hsub_n
    have habs : (lam s₁).natAbs = (lam s₂).natAbs := by rw [heq, Int.natAbs_neg]
    have hmag_info : ∀ s, isNonemptyS s →
        (k ≤ (posS s).card ∧ k ≤ (negS s).card → 2 * k ≤ (lam s).natAbs) ∧
        ((k ≤ (posS s).card ∧ ¬ k ≤ (negS s).card) ∨ (¬ k ≤ (posS s).card ∧ k ≤ (negS s).card) → (lam s).natAbs = 2 * k - 1) ∧
        (¬ k ≤ (posS s).card ∧ ¬ k ≤ (negS s).card → (lam s).natAbs = (suppS s).card ∧ (suppS s).card ≤ 2 * k - 2) := by
      intro s ⟨e, he⟩
      have hne : (suppS s).Nonempty := ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨hp, hn⟩
        dsimp only [lam]; rw [dif_pos hp, dif_pos hn]
        have h1 := hrk_pos_of_k (posS s) hp
        have h2 := hrk_pos_of_k (negS s) hn
        split_ifs <;> simp <;> omega
      · rintro (⟨hp, hn⟩ | ⟨hp, hn⟩)
        · dsimp only [lam]; rw [dif_pos hp, dif_neg hn]; simp
        · dsimp only [lam]; rw [dif_neg hp, dif_pos hn]; simp
      · rintro ⟨hp, hn⟩
        dsimp only [lam]; rw [dif_neg hp, dif_neg hn, dif_pos hne]
        have hsum := hsupp_card s
        split_ifs <;> simp <;> omega
    have hne2_s : isNonemptyS s₂ := by rcases hne₂ with ⟨e, he⟩; exact ⟨e, (Finset.mem_filter.mp he).2⟩
    have hm1 := hmag_info s₁ ⟨e₁, he₁⟩
    have hm2 := hmag_info s₂ hne2_s
    by_cases hp1 : k ≤ (posS s₁).card <;> by_cases hn1 : k ≤ (negS s₁).card
    · have hp2 : k ≤ (posS s₂).card := le_trans hp1 hcp
      have hn2 : k ≤ (negS s₂).card := le_trans hn1 hcn
      have hsr_eq : rk (U (posS s₁)) + rk (U (negS s₁)) = rk (U (posS s₂)) + rk (U (negS s₂)) := by
        dsimp only [lam] at habs; rw [dif_pos hp1, dif_pos hn1, dif_pos hp2, dif_pos hn2] at habs
        split_ifs at habs <;> simp at habs <;> omega
      have hrp_le : rk (U (posS s₁)) ≤ rk (U (posS s₂)) := hrk_mono _ _ (hU_mono _ _ hsub_p)
      have hrn_le : rk (U (negS s₁)) ≤ rk (U (negS s₂)) := hrk_mono _ _ (hU_mono _ _ hsub_n)
      have hrp_t : rk (U (posS s₁)) ≤ t := hrk_le_t_of_disj (posS s₁) (negS s₁) (hdisj_pn s₁) hn1
      have hrn_t : rk (U (negS s₁)) ≤ t := hrk_le_t_of_disj (negS s₁) (posS s₁) (hdisj_pn s₁).symm hp1
      have hFp : F (U (posS s₁)) = F (U (posS s₂)) := hF_const _ _ (hU_mono _ _ hsub_p) (by omega) hrp_t
      have hFn : F (U (negS s₁)) = F (U (negS s₂)) := hF_const _ _ (hU_mono _ _ hsub_n) (by omega) hrn_t
      have hp1_pos := hrk_pos_of_k (posS s₁) hp1
      have hn1_pos := hrk_pos_of_k (negS s₁) hn1
      dsimp only [lam] at heq; rw [dif_pos hp1, dif_pos hn1, dif_pos hp2, dif_pos hn2, hFp, hFn] at heq
      split_ifs at heq <;> omega
    · have hp2 : k ≤ (posS s₂).card := le_trans hp1 hcp
      by_cases hn2 : k ≤ (negS s₂).card
      · have a1 := hm1.2.1 (Or.inl ⟨hp1, hn1⟩)
        have a2 := hm2.1 ⟨hp2, hn2⟩
        omega
      · dsimp only [lam] at heq; rw [dif_pos hp1, dif_neg hn1, dif_pos hp2, dif_neg hn2] at heq; omega
    · have hn2 : k ≤ (negS s₂).card := le_trans hn1 hcn
      by_cases hp2 : k ≤ (posS s₂).card
      · have a1 := hm1.2.1 (Or.inr ⟨hp1, hn1⟩)
        have a2 := hm2.1 ⟨hp2, hn2⟩
        omega
      · dsimp only [lam] at heq; rw [dif_neg hp1, dif_pos hn1, dif_neg hp2, dif_pos hn2] at heq; omega
    · by_cases hp2 : k ≤ (posS s₂).card <;> by_cases hn2 : k ≤ (negS s₂).card
      · have a1 := hm1.2.2 ⟨hp1, hn1⟩
        have a2 := hm2.1 ⟨hp2, hn2⟩
        omega
      · have a1 := hm1.2.2 ⟨hp1, hn1⟩
        have a2 := hm2.2.1 (Or.inl ⟨hp2, hn2⟩)
        omega
      · have a1 := hm1.2.2 ⟨hp1, hn1⟩
        have a2 := hm2.2.1 (Or.inr ⟨hp2, hn2⟩)
        omega
      · have a1 := hm1.2.2 ⟨hp1, hn1⟩
        have a2 := hm2.2.2 ⟨hp2, hn2⟩
        have hceq : (suppS s₁).card = (suppS s₂).card := by omega
        have hseq : s₁ = s₂ := by
          have hsupp_eq' : suppS s₁ = suppS s₂ := Finset.eq_of_subset_of_card_le hsub_s (le_of_eq hceq.symm)
          funext e
          rcases hle e with h0 | hs
          · by_contra hne_e
            have he2 : e ∈ suppS s₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by cases hb : s₂ e <;> simp_all⟩
            rw [← hsupp_eq'] at he2
            have := (Finset.mem_filter.mp he2).2; rw [h0] at this; cases this
          · exact hs
        rw [hseq] at heq
        exact hlam_0 s₂ hne2_s (by omega)
  have htuck := octahedral_tucker (by omega : 1 ≤ d) lam hlam_0 hlam_bnd hlam_anti hlam_nocomp
  omega

private lemma shrink_step {k' t : ℕ} (hk' : 0 < k') (ht : 0 < t) :
    let d' := 2 * k' + 2 * t
    ∃ φ : {s : Finset (Fin (d' + 2)) // s.card = k' + 1} → {s : Finset (Fin d') // s.card = k'},
      ∀ i j, Disjoint i.val j.val → Disjoint (φ i).val (φ j).val := by
  let d' := 2 * k' + 2 * t
  let p1 : Fin (d' + 2) := ⟨d', by omega⟩
  let p2 : Fin (d' + 2) := ⟨d' + 1, by omega⟩
  let emb : Fin d' ↪ Fin (d' + 2) := ⟨fun e => ⟨e.val, by omega⟩, fun a b h => Fin.ext (Fin.mk.inj h)⟩
  let baseOf (s : Finset (Fin (d' + 2))) : Finset (Fin d') := Finset.univ.filter fun e => emb e ∈ s
  have hbase_card : ∀ s : Finset (Fin (d' + 2)),
      s.card = (baseOf s).card + (if p1 ∈ s then 1 else 0) + (if p2 ∈ s then 1 else 0) := by
    intro s
    let sLow := s.filter fun x => x.val < d'
    let sHi := s.filter fun x => ¬ x.val < d'
    have hsplit : s.card = sLow.card + sHi.card := by
      have h1 := Finset.sum_filter_add_sum_filter_not s (fun x => x.val < d') (fun _ => (1 : ℕ))
      simpa [sLow, sHi] using h1.symm
    have hlow_eq : sLow = (baseOf s).map emb := by
      ext x
      simp only [sLow, baseOf, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hxs, hxlt⟩
        have heq : emb ⟨x.val, hxlt⟩ = x := Fin.ext rfl
        exact ⟨⟨x.val, hxlt⟩, by rw [heq]; exact hxs, heq⟩
      · rintro ⟨e, hes, rfl⟩
        exact ⟨hes, e.isLt⟩
    have hlow_card : sLow.card = (baseOf s).card := by rw [hlow_eq, Finset.card_map]
    have hhi_eq : sHi = ({p1, p2} : Finset (Fin (d' + 2))).filter fun x => x ∈ s := by
      ext x
      simp only [sHi, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hxs, hge⟩
        have hxlt := x.isLt
        have hor : x = p1 ∨ x = p2 := by
          by_cases h1 : x.val = d'
          · left; exact Fin.ext h1
          · right; exact Fin.ext (by dsimp only [p2]; omega)
        exact ⟨hor, hxs⟩
      · rintro ⟨rfl | rfl, hxs⟩
        · exact ⟨hxs, by dsimp [p1]; omega⟩
        · exact ⟨hxs, by dsimp [p2]; omega⟩
    have hp12 : p1 ≠ p2 := fun h => by have := congrArg Fin.val h; dsimp [p1, p2] at this; omega
    have hhi_card : sHi.card = (if p1 ∈ s then 1 else 0) + (if p2 ∈ s then 1 else 0) := by
      rw [hhi_eq]
      by_cases h1 : p1 ∈ s <;> by_cases h2 : p2 ∈ s
      · have : ({p1, p2} : Finset (Fin (d' + 2))).filter (fun x => x ∈ s) = {p1, p2} := by
          ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.1, fun h => ⟨h, by rcases h with rfl | rfl <;> assumption⟩⟩
        rw [this, Finset.card_pair hp12, if_pos h1, if_pos h2]
      · have : ({p1, p2} : Finset (Fin (d' + 2))).filter (fun x => x ∈ s) = {p1} := by
          ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, hx⟩; rfl; exact absurd hx h2
          · rintro rfl; exact ⟨Or.inl rfl, h1⟩
        rw [this, Finset.card_singleton, if_pos h1, if_neg h2]
      · have : ({p1, p2} : Finset (Fin (d' + 2))).filter (fun x => x ∈ s) = {p2} := by
          ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, hx⟩; exact absurd hx h1; rfl
          · rintro rfl; exact ⟨Or.inr rfl, h2⟩
        rw [this, Finset.card_singleton, if_neg h1, if_pos h2]
      · have : ({p1, p2} : Finset (Fin (d' + 2))).filter (fun x => x ∈ s) = ∅ := by
          ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨rfl | rfl, hx⟩; exact h1 hx; exact h2 hx
        rw [this, Finset.card_empty, if_neg h1, if_neg h2]
    rw [hsplit, hlow_card, hhi_card]; omega
  let φVal (s : {s : Finset (Fin (d' + 2)) // s.card = k' + 1}) : Finset (Fin d') :=
    if h12 : p1 ∈ s.val ∧ p2 ∈ s.val then
      have hne : (Finset.univ \ baseOf s.val).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have hc := hbase_card s.val
        rw [s.2, if_pos h12.1, if_pos h12.2] at hc
        omega
      insert ((Finset.univ \ baseOf s.val).min' hne) (baseOf s.val)
    else if h0 : p1 ∉ s.val ∧ p2 ∉ s.val then
      have hne : (baseOf s.val).Nonempty := by
        rw [← Finset.card_pos]
        have hc := hbase_card s.val
        rw [s.2, if_neg h0.1, if_neg h0.2] at hc
        omega
      (baseOf s.val).erase ((baseOf s.val).min' hne)
    else baseOf s.val
  have hφ_card : ∀ s, (φVal s).card = k' := by
    intro s
    have hc := hbase_card s.val
    rw [s.2] at hc
    dsimp only [φVal]
    by_cases h12 : p1 ∈ s.val ∧ p2 ∈ s.val
    · rw [dif_pos h12]
      rw [if_pos h12.1, if_pos h12.2] at hc
      have hne : (Finset.univ \ baseOf s.val).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      have hm : (Finset.univ \ baseOf s.val).min' hne ∉ baseOf s.val :=
        (Finset.mem_sdiff.mp (Finset.min'_mem _ hne)).2
      rw [Finset.card_insert_of_notMem hm]
      omega
    · rw [dif_neg h12]
      by_cases h0 : p1 ∉ s.val ∧ p2 ∉ s.val
      · rw [dif_pos h0]
        rw [if_neg h0.1, if_neg h0.2] at hc
        have hne : (baseOf s.val).Nonempty := by
          rw [← Finset.card_pos]; omega
        have hm : (baseOf s.val).min' hne ∈ baseOf s.val := Finset.min'_mem _ hne
        rw [Finset.card_erase_of_mem hm]
        omega
      · rw [dif_neg h0]
        by_cases h1 : p1 ∈ s.val <;> by_cases h2 : p2 ∈ s.val
        · exact absurd ⟨h1, h2⟩ h12
        · rw [if_pos h1, if_neg h2] at hc; omega
        · rw [if_neg h1, if_pos h2] at hc; omega
        · exact absurd ⟨h1, h2⟩ h0
  refine ⟨fun s => ⟨φVal s, hφ_card s⟩, fun i j hdisj => ?_⟩
  have hdb : Disjoint (baseOf i.val) (baseOf j.val) := by
    rw [Finset.disjoint_left]; intro e he1 he2
    exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp he1).2 (Finset.mem_filter.mp he2).2
  have hboth_case : ∀ (a b : {s : Finset (Fin (d' + 2)) // s.card = k' + 1}),
      Disjoint a.val b.val → p1 ∈ a.val ∧ p2 ∈ a.val → Disjoint (φVal a) (φVal b) := by
    intro a b hab ha12
    have hb0 : p1 ∉ b.val ∧ p2 ∉ b.val :=
      ⟨Finset.disjoint_left.mp hab ha12.1, Finset.disjoint_left.mp hab ha12.2⟩
    have hnb12 : ¬ (p1 ∈ b.val ∧ p2 ∈ b.val) := fun h => hb0.1 h.1
    have hdab : Disjoint (baseOf a.val) (baseOf b.val) := by
      rw [Finset.disjoint_left]; intro e he1 he2
      exact Finset.disjoint_left.mp hab (Finset.mem_filter.mp he1).2 (Finset.mem_filter.mp he2).2
    dsimp only [φVal]
    rw [dif_pos ha12, dif_neg hnb12, dif_pos hb0]
    rw [Finset.disjoint_left]
    intro e hea heb
    rcases Finset.mem_insert.mp hea with rfl | heba
    · rcases Finset.mem_erase.mp heb with ⟨hne, hebb⟩
      have hne_a : (Finset.univ \ baseOf a.val).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have hc := hbase_card a.val
        rw [a.2, if_pos ha12.1, if_pos ha12.2] at hc
        omega
      have hne_b : (baseOf b.val).Nonempty := by
        rw [← Finset.card_pos]
        have hc := hbase_card b.val
        rw [b.2, if_neg hb0.1, if_neg hb0.2] at hc
        omega
      have hm2_mem : (baseOf b.val).min' hne_b ∈ baseOf b.val := Finset.min'_mem _ hne_b
      have hm2_le : (baseOf b.val).min' hne_b ≤ (Finset.univ \ baseOf a.val).min' hne_a :=
        Finset.min'_le _ _ hebb
      have hm2_not_a : (baseOf b.val).min' hne_b ∉ baseOf a.val :=
        Finset.disjoint_right.mp hdab hm2_mem
      have hm1_le : (Finset.univ \ baseOf a.val).min' hne_a ≤ (baseOf b.val).min' hne_b :=
        Finset.min'_le _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hm2_not_a⟩)
      exact hne (le_antisymm hm1_le hm2_le)
    · exact Finset.disjoint_left.mp hdab heba (Finset.mem_of_mem_erase heb)
  by_cases hi12 : p1 ∈ i.val ∧ p2 ∈ i.val
  · exact hboth_case i j hdisj hi12
  · by_cases hj12 : p1 ∈ j.val ∧ p2 ∈ j.val
    · exact (hboth_case j i hdisj.symm hj12).symm
    · have hsub_i : φVal i ⊆ baseOf i.val := by
        dsimp only [φVal]; rw [dif_neg hi12]
        by_cases h0 : p1 ∉ i.val ∧ p2 ∉ i.val
        · rw [dif_pos h0]; exact Finset.erase_subset ..
        · rw [dif_neg h0]
      have hsub_j : φVal j ⊆ baseOf j.val := by
        dsimp only [φVal]; rw [dif_neg hj12]
        by_cases h0 : p1 ∉ j.val ∧ p2 ∉ j.val
        · rw [dif_pos h0]; exact Finset.erase_subset ..
        · rw [dif_neg h0]
      exact hdb.mono hsub_i hsub_j

private lemma shrink_iter (D t r : ℕ) (hD : 0 < D) (ht : 0 < t) :
    ∃ φ : {s : Finset (Fin (2 * (D + r) + 2 * t)) // s.card = D + r} →
          {s : Finset (Fin (2 * D + 2 * t)) // s.card = D},
      ∀ i j, Disjoint i.val j.val → Disjoint (φ i).val (φ j).val := by
  induction r with
  | zero =>
    exact ⟨id, fun _ _ h => h⟩
  | succ r ih =>
    rcases ih with ⟨φ1, hφ1⟩
    rcases shrink_step (k' := D + r) (t := t) (by omega) ht with ⟨φ2, hφ2⟩
    have hdim : 2 * (D + (r + 1)) + 2 * t = (2 * (D + r) + 2 * t) + 2 := by omega
    let castS : {s : Finset (Fin (2 * (D + (r + 1)) + 2 * t)) // s.card = D + (r + 1)} →
        {s : Finset (Fin ((2 * (D + r) + 2 * t) + 2)) // s.card = (D + r) + 1} :=
      fun s => ⟨s.val.map (Fin.castOrderIso hdim).toEmbedding, by rw [Finset.card_map, s.2]; omega⟩
    refine ⟨fun s => φ1 (φ2 (castS s)), fun i j hdisj => hφ1 _ _ (hφ2 _ _ ?_)⟩
    rw [Finset.disjoint_left]
    intro e he1 he2
    rcases Finset.mem_map.mp he1 with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp he2 with ⟨b, hb, hab⟩
    have heq : a = b := (Fin.castOrderIso hdim).toEmbedding.injective hab.symm
    subst heq
    exact Finset.disjoint_left.mp hdisj ha hb

private lemma sdiff_card_step {α : Type} [DecidableEq α] (C B1 B2 : Finset α) (hsub : B1 ⊆ B2) :
    (C \ B1).card - (C \ B2).card ≤ B2.card - B1.card := by
  have hdecomp : C \ B1 = (C \ B2) ∪ ((C ∩ B2) \ B1) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · intro ⟨hC, h1⟩
      by_cases h2 : x ∈ B2
      · exact Or.inr ⟨⟨hC, h2⟩, h1⟩
      · exact Or.inl ⟨hC, h2⟩
    · rintro (⟨hC, h2⟩ | ⟨⟨hC, _⟩, h1⟩)
      · exact ⟨hC, fun h1 => h2 (hsub h1)⟩
      · exact ⟨hC, h1⟩
  have hdisj : Disjoint (C \ B2) ((C ∩ B2) \ B1) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx2).1).2
  have hsub2 : (C ∩ B2) \ B1 ⊆ B2 \ B1 := fun x hx =>
    Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2, (Finset.mem_sdiff.mp hx).2⟩
  have h1 : (C \ B1).card = (C \ B2).card + ((C ∩ B2) \ B1).card := by
    rw [hdecomp, Finset.card_union_of_disjoint hdisj]
  have h2 : ((C ∩ B2) \ B1).card ≤ (B2 \ B1).card := Finset.card_le_card hsub2
  have h3 : (B2 \ B1).card = B2.card - B1.card := by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  omega

private theorem main_thm_core (k t D : ℕ) (ht : 0 < t) (h2tk : 2 * t < k) (hD : 0 < D) (hDk : D ≤ k)
    (dec : DecidableEq (Fin (2 * D + 2 * t))) :
    letI : DecidableEq (Fin (2 * D + 2 * t)) := dec
    let d := 2 * k + 2 * t
    let K := {s : Finset (Fin d) // s.card = k}
    let X := Finset K
    let fit := fun (f : X → K → ℕ) =>
      (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = D) ∧
      (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)
    let cost := fun (l : ℕ) (p : Fin (l + 1) → X) (a : Fin l → K) (f : X → K → ℕ) =>
      Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
    let inc := fun (l : ℕ) (p : Fin (l + 1) → X) =>
      ∀ i : Fin l, p i.castSucc ⊆ p i.succ
    (∃ C : K → Finset (Fin (2 * D + 2 * t)),
      (∀ j, (C j).card = D) ∧ (∀ i j, Disjoint i.val j.val → Disjoint (C i) (C j)) ∧
      let F := fun (x : X) (j : K) => ((C j) \ (x.biUnion C)).card
      fit F ∧ ∀ l p a, inc l p → cost l p a F ≤ 2 * D + 2 * t) ∧
    (∀ f, fit f → ∃ l p a, inc l p ∧ 2 * D + t ≤ cost l p a f) := by
  letI : DecidableEq (Fin (2 * D + 2 * t)) := dec
  let d := 2 * k + 2 * t
  let K := {s : Finset (Fin d) // s.card = k}
  let X := Finset K
  let fit := fun (f : X → K → ℕ) =>
    (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = D) ∧
    (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)
  let cost := fun (l : ℕ) (p : Fin (l + 1) → X) (a : Fin l → K) (f : X → K → ℕ) =>
    Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
  let inc := fun (l : ℕ) (p : Fin (l + 1) → X) =>
    ∀ i : Fin l, p i.castSucc ⊆ p i.succ
  constructor
  · rcases shrink_iter D t (k - D) hD ht with ⟨φ, hφ⟩
    have hkeq : D + (k - D) = k := Nat.add_sub_cancel' hDk
    have hdeq : 2 * k + 2 * t = 2 * (D + (k - D)) + 2 * t := by omega
    let castK : K → {s : Finset (Fin (2 * (D + (k - D)) + 2 * t)) // s.card = D + (k - D)} :=
      fun s => ⟨s.val.map (Fin.castOrderIso hdeq).toEmbedding, by rw [Finset.card_map, s.2, hkeq]⟩
    let C : K → Finset (Fin (2 * D + 2 * t)) := fun j => (φ (castK j)).val
    have hC_card : ∀ j, (C j).card = D := fun j => (φ (castK j)).2
    have hC_disj : ∀ i j, Disjoint i.val j.val → Disjoint (C i) (C j) := by
      intro i j hij
      refine hφ (castK i) (castK j) ?_
      rw [Finset.disjoint_left]; intro e he1 he2
      rcases Finset.mem_map.mp he1 with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp he2 with ⟨b, hb, hab⟩
      have heq : a = b := (Fin.castOrderIso hdeq).toEmbedding.injective hab.symm
      subst heq
      exact Finset.disjoint_left.mp hij ha hb
    let F : X → K → ℕ := fun x j => ((C j) \ (x.biUnion C)).card
    refine ⟨C, hC_card, hC_disj, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x j
      exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq (hC_card j))
    · intro x j hdisj
      have hd : Disjoint (C j) (x.biUnion C) := by
        rw [Finset.disjoint_left]; intro e he1 he2
        rcases Finset.mem_biUnion.mp he2 with ⟨i, hi, hei⟩
        exact Finset.disjoint_left.mp (hC_disj i j (hdisj i hi)) hei he1
      dsimp only
      rw [Finset.sdiff_eq_self_of_disjoint hd, hC_card j]
    · intro x j hj
      have hsub : C j ⊆ x.biUnion C := Finset.subset_biUnion_of_mem C hj
      dsimp only
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
    · intro x y hxy j
      have hbu : x.biUnion C ⊆ y.biUnion C := Finset.biUnion_subset_biUnion_of_subset_left C hxy
      exact Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hbu)
    · intro l p a hinc
      have htele : ∀ (m : ℕ) (p : Fin (m + 1) → X) (a : Fin m → K), inc m p →
          cost m p a F + ((p 0).biUnion C).card ≤ ((p (Fin.last m)).biUnion C).card := by
        intro m
        induction m with
        | zero =>
          intro p a _; simp [cost]
        | succ m ih =>
          intro p a hinc'
          let p' : Fin (m + 1) → X := fun i => p i.castSucc
          let a' : Fin m → K := fun i => a i.castSucc
          have hinc_prev : inc m p' := fun i => hinc' i.castSucc
          have hprev := ih p' a' hinc_prev
          have hlast_sub : (p' (Fin.last m)).biUnion C ⊆ (p (Fin.last (m + 1))).biUnion C :=
            Finset.biUnion_subset_biUnion_of_subset_left C (hinc' (Fin.last m))
          have hlast_card : ((p' (Fin.last m)).biUnion C).card ≤ ((p (Fin.last (m + 1))).biUnion C).card :=
            Finset.card_le_card hlast_sub
          have hFstep : F (p' (Fin.last m)) (a (Fin.last m)) - F (p (Fin.last (m + 1))) (a (Fin.last m)) ≤
              ((p (Fin.last (m + 1))).biUnion C).card - ((p' (Fin.last m)).biUnion C).card :=
            sdiff_card_step (C (a (Fin.last m))) ((p' (Fin.last m)).biUnion C)
              ((p (Fin.last (m + 1))).biUnion C) hlast_sub
          have hsum : cost (m + 1) p a F = cost m p' a' F +
              (F (p' (Fin.last m)) (a (Fin.last m)) - F (p (Fin.last (m + 1))) (a (Fin.last m))) := by
            unfold cost
            rw [Fin.sum_univ_castSucc]
            rfl
          rw [hsum]
          have hp0 : p' 0 = p 0 := rfl
          rw [hp0] at hprev
          omega
      have ht1 := htele l p a hinc
      have hcard_le : ((p (Fin.last l)).biUnion C).card ≤ 2 * D + 2 * t := by
        calc ((p (Fin.last l)).biUnion C).card
            ≤ (Finset.univ : Finset (Fin (2 * D + 2 * t))).card := Finset.card_le_card (Finset.subset_univ _)
          _ = 2 * D + 2 * t := by simp
      change cost l p a F ≤ 2 * D + 2 * t
      omega
  · intro f hf
    let g : X → K → Bool := fun x j => decide (0 < f x j)
    have hg_fits : (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → g x j = true) ∧
        (∀ x j, j ∈ x → g x j = false) := by
      refine ⟨fun x j h => ?_, fun x j h => ?_⟩
      · dsimp only [g]; rw [hf.2.1 x j h]; exact decide_eq_true hD
      · dsimp only [g]; rw [hf.2.2.1 x j h]; exact decide_eq_false (by omega)
    have hg_dec : ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true := by
      intro x y hxy j hy
      dsimp only [g] at hy ⊢
      have hy' : 0 < f y j := of_decide_eq_true hy
      have hle := hf.2.2.2 x y hxy j
      exact decide_eq_true (by omega)
    rcases two_shore_runs ht h2tk g hg_fits hg_dec with ⟨A, B, hdisj, hB, hrun⟩
    have hruns_to_chain : ∀ (m : ℕ), 1 ≤ m → ∀ x : X, runsG g m x →
        ∃ (l : ℕ) (p : Fin (l + 1) → X) (a : Fin l → K),
          inc l p ∧ p (Fin.last l) ⊆ x ∧ D + (m - 1) ≤ cost l p a f := by
      intro m
      induction m with
      | zero => intro h; omega
      | succ m ih =>
        intro _ x hrm
        rcases hrm with ⟨u, v, j, hprev, huv, hvx, hgu, hgv⟩
        have hfu : 0 < f u j := of_decide_eq_true hgu
        have hfv : f v j = 0 := by
          have h0 : ¬ 0 < f v j := of_decide_eq_false hgv
          omega
        by_cases hm0 : m = 0
        · subst hm0
          let p : Fin 2 → X := fun i => if i.val = 0 then ∅ else v
          let a : Fin 1 → K := fun _ => j
          refine ⟨1, p, a, ?_, ?_, ?_⟩
          · intro i
            have hi0 : i = 0 := Fin.eq_zero i
            simp [p, hi0]
            exact Finset.empty_subset _
          · simpa [p, Fin.last] using hvx
          · simp only [cost, Fin.sum_univ_one, Fin.castSucc_zero, Fin.succ_zero_eq_one]
            have h0 : p 0 = ∅ := rfl
            have h1 : p 1 = v := rfl
            rw [h0, h1, hf.2.1 ∅ j (fun _ h => by simp at h), hfv]
            omega
        · rcases ih (by omega) u hprev with ⟨l, p, a, hinc, hlast, hcost⟩
          let p' : Fin (l + 2) → X := fun i => if hi : i.val ≤ l then p ⟨i.val, by omega⟩ else v
          let a' : Fin (l + 1) → K := fun i => if hi : i.val < l then a ⟨i.val, hi⟩ else j
          refine ⟨l + 1, p', a', ?_, ?_, ?_⟩
          · intro i
            dsimp only [p']
            by_cases hi : i.val < l
            · have h1 : i.val ≤ l := by omega
              have h2 : i.val + 1 ≤ l := by omega
              simp only [Fin.val_castSucc, Fin.val_succ, h1, h2, ↓reduceDIte]
              exact hinc ⟨i.val, hi⟩
            · have heq : i.val = l := by have := i.isLt; omega
              have h1 : i.val ≤ l := by omega
              have h2 : ¬ i.val + 1 ≤ l := by omega
              simp only [Fin.val_castSucc, Fin.val_succ, h1, h2, ↓reduceDIte]
              have hfeq : (⟨i.val, by omega⟩ : Fin (l + 1)) = Fin.last l := Fin.ext heq
              rw [hfeq]
              exact hlast.trans huv
          · dsimp only [p', Fin.last]
            have hnot : ¬ l + 1 ≤ l := by omega
            simp only [hnot, ↓reduceDIte]; exact hvx
          · have hsum : cost (l + 1) p' a' f = cost l p a f + (f (p (Fin.last l)) j - f v j) := by
              unfold cost
              rw [Fin.sum_univ_castSucc]
              congr 1
              · refine Finset.sum_congr rfl fun i _ => ?_
                have h1 : i.val ≤ l := by have := i.isLt; omega
                have h2 : i.val + 1 ≤ l := by have := i.isLt; omega
                have h3 : i.val < l := i.isLt
                simp only [p', a', Fin.val_castSucc, Fin.val_succ, h1, h2, h3, ↓reduceDIte]
                rfl
              · have h1 : ¬ l + 1 ≤ l := by omega
                simp [p', a', Fin.last, h1]
            have hf_last : 1 ≤ f (p (Fin.last l)) j := by
              have hle := hf.2.2.2 (p (Fin.last l)) u hlast j
              omega
            rw [hsum, hfv]
            omega
    rcases hruns_to_chain (t + 1) (by omega) _ hrun with ⟨l, p, a, hinc, hlast, hcost⟩
    rcases Finset.exists_subset_card_eq hB with ⟨SB, hSB_sub, hSB_card⟩
    let jB : K := ⟨SB, hSB_card⟩
    have hdisj_last : ∀ i ∈ p (Fin.last l), Disjoint i.val jB.val := by
      intro i hi
      have hiA : i.val ⊆ A := (Finset.mem_filter.mp (hlast hi)).2
      exact hdisj.mono hiA hSB_sub
    let p' : Fin (l + 2) → X := fun i => if hi : i.val ≤ l then p ⟨i.val, by omega⟩ else insert jB (p (Fin.last l))
    let a' : Fin (l + 1) → K := fun i => if hi : i.val < l then a ⟨i.val, hi⟩ else jB
    refine ⟨l + 1, p', a', ?_, ?_⟩
    · intro i
      dsimp only [p']
      by_cases hi : i.val < l
      · have h1 : i.val ≤ l := by omega
        have h2 : i.val + 1 ≤ l := by omega
        simp only [Fin.val_castSucc, Fin.val_succ, h1, h2, ↓reduceDIte]
        exact hinc ⟨i.val, hi⟩
      · have heq : i.val = l := by have := i.isLt; omega
        have h1 : i.val ≤ l := by omega
        have h2 : ¬ i.val + 1 ≤ l := by omega
        simp only [Fin.val_castSucc, Fin.val_succ, h1, h2, ↓reduceDIte]
        have hfeq : (⟨i.val, by omega⟩ : Fin (l + 1)) = Fin.last l := Fin.ext heq
        rw [hfeq]
        exact Finset.subset_insert ..
    · have hsum : cost (l + 1) p' a' f = cost l p a f + (f (p (Fin.last l)) jB - f (insert jB (p (Fin.last l))) jB) := by
        unfold cost
        rw [Fin.sum_univ_castSucc]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          have h1 : i.val ≤ l := by have := i.isLt; omega
          have h2 : i.val + 1 ≤ l := by have := i.isLt; omega
          have h3 : i.val < l := i.isLt
          simp only [p', a', Fin.val_castSucc, Fin.val_succ, h1, h2, h3, ↓reduceDIte]
          rfl
        · have h1 : ¬ l + 1 ≤ l := by omega
          simp [p', a', Fin.last, h1]
      change 2 * D + t ≤ cost (l + 1) p' a' f
      rw [hsum, hf.2.1 (p (Fin.last l)) jB hdisj_last, hf.2.2.1 _ jB (Finset.mem_insert_self ..)]
      omega

end TwoShoreAndShrink

end PEqualNP.Outside.L_meta_48522

theorem PEqualNP.Outside.L_meta_48522 :
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (k t D : Nat), 0 < t → 2*t < k → 0 < D → D ≤ k →
    let d := 2*k+2*t
    let K := {s : Finset (Fin d) // s.card = k}
    let X := Finset K
    let fit := fun (f : X → K → Nat) =>
      (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = D) ∧
      (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)
    let cost := fun (l : Nat) (p : Fin (l+1) → X) (a : Fin l → K) (f : X → K → Nat) =>
      Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
    let inc := fun (l : Nat) (p : Fin (l+1) → X) =>
      ∀ i : Fin l, p i.castSucc ⊆ p i.succ
    (∃ C : K → Finset (Fin (2*D+2*t)),
      (∀ j, (C j).card = D) ∧ (∀ i j, Disjoint i.val j.val → Disjoint (C i) (C j)) ∧
      let F := fun (x : X) (j : K) => ((C j) \ (x.biUnion C)).card
      fit F ∧ ∀ l p a, inc l p → cost l p a F ≤ 2*D+2*t) ∧
    (∀ f, fit f → ∃ l p a, inc l p ∧ 2*D+t ≤ cost l p a f) := by
  intro k t D ht h2tk hD hDk
  exact PEqualNP.Outside.L_meta_48522.main_thm_core k t D ht h2tk hD hDk _
