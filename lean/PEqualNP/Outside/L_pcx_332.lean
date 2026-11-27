import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Dist
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_332_aux

open scoped BigOperators

private def mkRead (n h : ℕ) (target : Bool) : (Fin n × Fin 4 × Bool × Fin 4) → Bool
  | (i, s, b, t) =>
    if i.val + 1 < h then
      (s == 0 && t == 0) ||
      (s == 0 && b && t == 1) ||
      (s == 1 && t == 1) ||
      (s == 2 && !b && t == 2) ||
      (s == 2 && b && t == 3) ||
      (s == 3 && !b && t == 3) ||
      (s == 3 && b && t == 2)
    else if i.val + 1 == h then
      (s == 0 && b && t == 0) ||
      (s == 1 && t == 0) ||
      (s == 2 && (b == target) && t == 2) ||
      (s == 3 && ((!b) == target) && t == 2)
    else
      (s == 0 && t == 0) ||
      (s == 2 && t == 2)

private def wtPref {n : ℕ} (h : ℕ) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i.val < h ∧ x i = true)).card

private def prefPar {n : ℕ} (x : Fin n → Bool) (m : ℕ) : Bool :=
  decide (wtPref m x % 2 = 1)

private def validWalks {n : ℕ} (enabled : (Fin n × Fin 4 × Bool × Fin 4) → Bool)
    (x : Fin n → Bool) : Finset (Fin (n + 1) → Fin 4) :=
  Finset.univ.filter (fun p : Fin (n + 1) → Fin 4 =>
    p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i, p i.castSucc, x i, p i.succ) = true)

private lemma wtPref_zero {n : ℕ} (x : Fin n → Bool) : wtPref 0 x = 0 := by
  simp [wtPref]

private lemma wtPref_succ {n : ℕ} (x : Fin n → Bool) {m : ℕ} (hm : m < n) :
    wtPref (m + 1) x = wtPref m x + (if x ⟨m, hm⟩ = true then 1 else 0) := by
  unfold wtPref
  by_cases hx : x ⟨m, hm⟩ = true
  · simp only [hx, ↓reduceIte]
    have hEq : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < m + 1 ∧ x i = true) =
        insert ⟨m, hm⟩ ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ x i = true)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      constructor
      · intro ⟨hi, hxi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact Or.inr ⟨hlt, hxi⟩
        · exact Or.inl heq
      · rintro (heq | ⟨hlt, hxi⟩)
        · have hi : i = ⟨m, hm⟩ := Fin.ext heq
          subst hi; exact ⟨Nat.lt_succ_self m, hx⟩
        · exact ⟨by omega, hxi⟩
    have hnot : (⟨m, hm⟩ : Fin n) ∉
        (Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ x i = true) := by
      simp
    rw [hEq, Finset.card_insert_of_notMem hnot, add_comm]
  · have hzero : (if x ⟨m, hm⟩ = true then 1 else 0) = 0 := by simp [hx]
    rw [hzero, add_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hi, hxi⟩
      refine ⟨?_, hxi⟩
      by_contra hge
      have heq : i = ⟨m, hm⟩ := Fin.ext (by simp; omega)
      subst heq
      exact hx hxi
    · intro ⟨hlt, hxi⟩; exact ⟨by omega, hxi⟩

private lemma prefPar_zero {n : ℕ} (x : Fin n → Bool) : prefPar x 0 = false := by
  simp [prefPar, wtPref_zero]

private lemma prefPar_succ {n : ℕ} (x : Fin n → Bool) {m : ℕ} (hm : m < n) :
    prefPar x (m + 1) = xor (prefPar x m) (x ⟨m, hm⟩) := by
  simp only [prefPar, wtPref_succ x hm]
  cases hx : x ⟨m, hm⟩
  · simp
  · simp only [↓reduceIte, Bool.xor_true]
    rcases Nat.mod_two_eq_zero_or_one (wtPref m x) with h0 | h1
    · have : (wtPref m x + 1) % 2 = 1 := by omega
      simp [h0, this]
    · have : (wtPref m x + 1) % 2 = 0 := by omega
      simp [h1, this]

private lemma fin4_cases (s : Fin 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
  fin_cases s <;> simp

private lemma mkRead_seam_dst {n h : ℕ} (target : Bool) {i : Fin n} (hi : i.val + 1 = h)
    {s t : Fin 4} {b : Bool} (hen : mkRead n h target (i, s, b, t) = true) :
    t = 0 ∨ t = 2 := by
  simp only [mkRead, hi, lt_self_iff_false, ↓reduceIte, beq_self_eq_true] at hen
  fin_cases t <;> fin_cases s <;> cases b <;> cases target <;> simp at hen ⊢

private lemma mkRead_tail {n h : ℕ} (target : Bool) {i : Fin n} (hi : h ≤ i.val)
    {s t : Fin 4} {b : Bool} (hen : mkRead n h target (i, s, b, t) = true) :
    (s = 0 ∧ t = 0) ∨ (s = 2 ∧ t = 2) := by
  have h1 : ¬ (i.val + 1 < h) := by omega
  have h2 : ¬ (i.val + 1 = h) := by omega
  simp only [mkRead, h1, ↓reduceIte, beq_iff_eq, h2] at hen
  fin_cases s <;> fin_cases t <;> simp at hen ⊢

private lemma valid_tail_const {n h : ℕ} (hh : 0 < h) (hhn : h ≤ n) (target : Bool)
    (x : Fin n → Bool) {p : Fin (n + 1) → Fin 4}
    (hp : p ∈ validWalks (mkRead n h target) x) :
    (p 0 = 0 ∧ ∀ t : Fin (n + 1), h ≤ t.val → p t = 0) ∨
    (p 0 = 2 ∧ ∀ t : Fin (n + 1), h ≤ t.val → p t = 2) := by
  simp only [validWalks, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hcyc, hsteps⟩ := hp
  have hseam := mkRead_seam_dst target (i := ⟨h - 1, by omega⟩) (by simp; omega) (hsteps ⟨h - 1, by omega⟩)
  have hsucc : (⟨h - 1, by omega⟩ : Fin n).succ = ⟨h, by omega⟩ := Fin.ext (by simp; omega)
  rw [hsucc] at hseam
  have hstay : ∀ c : Fin 4, p ⟨h, by omega⟩ = c →
      ∀ d : ℕ, (hd : h + d ≤ n) → p ⟨h + d, by omega⟩ = c := by
    intro c hc d
    induction d with
    | zero => intro _; exact hc
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hst := mkRead_tail target (i := ⟨h + d, by omega⟩) (by simp) (hsteps ⟨h + d, by omega⟩)
      have hcs : (⟨h + d, by omega⟩ : Fin n).castSucc = ⟨h + d, by omega⟩ := Fin.ext rfl
      have hsc : (⟨h + d, by omega⟩ : Fin n).succ = ⟨h + (d + 1), by omega⟩ := Fin.ext (by simp; omega)
      rw [hcs, hsc, hprev] at hst
      rcases hst with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;> exact ht
  rcases hseam with h0 | h2
  · left
    have hall : ∀ t : Fin (n + 1), h ≤ t.val → p t = 0 := fun t ht => by
      have := hstay 0 h0 (t.val - h) (by omega)
      have hteq : (⟨h + (t.val - h), by omega⟩ : Fin (n + 1)) = t := Fin.ext (by simp; omega)
      rwa [hteq] at this
    exact ⟨hcyc.trans (hall (Fin.last n) (by simp; omega)), hall⟩
  · right
    have hall : ∀ t : Fin (n + 1), h ≤ t.val → p t = 2 := fun t ht => by
      have := hstay 2 h2 (t.val - h) (by omega)
      have hteq : (⟨h + (t.val - h), by omega⟩ : Fin (n + 1)) = t := Fin.ext (by simp; omega)
      rwa [hteq] at this
    exact ⟨hcyc.trans (hall (Fin.last n) (by simp; omega)), hall⟩

private def walkA {n : ℕ} (h : ℕ) (k : Fin n) : Fin (n + 1) → Fin 4 :=
  fun t => if k.val < t.val ∧ t.val < h then 1 else 0

private lemma card_validA {n h : ℕ} (hh : 0 < h) (hhn : h ≤ n) (target : Bool)
    (x : Fin n → Bool) :
    ((validWalks (mkRead n h target) x).filter (fun p => p 0 = 0)).card = wtPref h x := by
  unfold wtPref
  symm
  refine Finset.card_bij (fun k _ => walkA h k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨hkh, hxk⟩ := hk
    simp only [validWalks, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [walkA, show ¬ (n < h) by omega]
    · intro i
      unfold mkRead walkA
      by_cases h1 : i.val + 1 < h
      · simp only [h1, ↓reduceIte, Fin.val_castSucc, Fin.val_succ]
        by_cases hki : k.val < i.val
        · have hki1 : k.val < i.val + 1 := by omega
          have hih : i.val < h := by omega
          simp [hki, hih, hki1]
        · by_cases heq : k.val = i.val
          · have hki1 : k.val < i.val + 1 := by omega
            have hxi : x i = true := by
              have : i = k := Fin.ext heq.symm
              rw [this]; exact hxk
            simp [hki, hki1, hxi]
          · have hki1 : ¬ (k.val < i.val + 1) := by omega
            simp [hki, hki1]
      · by_cases h2 : i.val + 1 = h
        · simp only [↓reduceIte, h2, lt_self_iff_false, beq_self_eq_true, Fin.val_castSucc,
            Fin.val_succ, and_false]
          by_cases hki : k.val < i.val
          · have hih : i.val < h := by omega
            simp [hki, hih]
          · have heq : i = k := Fin.ext (by omega)
            have hxi : x i = true := by rw [heq]; exact hxk
            simp [hki, hxi]
        · simp [h1, h2, show ¬ (i.val < h) by omega]
    · simp [walkA]
  · intro k₁ hk₁ k₂ hk₂ hEq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
    by_contra hne
    have hval : k₁.val ≠ k₂.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
    · have hpt := congrFun hEq ⟨k₁.val + 1, by omega⟩
      simp only [walkA, show k₁.val < k₁.val + 1 by omega, show k₁.val + 1 < h by omega,
        and_self, ↓reduceIte, show ¬ (k₂.val < k₁.val + 1) by omega, false_and] at hpt
      exact absurd hpt (by decide)
    · have hpt := congrFun hEq ⟨k₂.val + 1, by omega⟩
      simp only [walkA, show k₂.val < k₂.val + 1 by omega, show k₂.val + 1 < h by omega,
        and_self, ↓reduceIte, show ¬ (k₁.val < k₂.val + 1) by omega, false_and] at hpt
      exact absurd hpt (by decide)
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpv, hp0⟩ := hp
    have htail := valid_tail_const hh hhn target x hpv
    have htail0 : ∀ t : Fin (n + 1), h ≤ t.val → p t = 0 := by
      rcases htail with ⟨_, h0⟩ | ⟨h2, _⟩
      · exact h0
      · rw [hp0] at h2; exact absurd h2 (by decide)
    simp only [validWalks, Finset.mem_filter, Finset.mem_univ, true_and] at hpv
    obtain ⟨_, hsteps⟩ := hpv
    have h01 : ∀ m : ℕ, (hm : m < h) → p ⟨m, by omega⟩ = 0 ∨ p ⟨m, by omega⟩ = 1 := by
      intro m
      induction m with
      | zero => intro _; exact Or.inl hp0
      | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hst := hsteps ⟨m, by omega⟩
        have hlt : m + 1 < h := hm
        simp only [mkRead, hlt, ↓reduceIte] at hst
        have hcs : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, by omega⟩ := Fin.ext rfl
        have hsc : (⟨m, by omega⟩ : Fin n).succ = ⟨m + 1, by omega⟩ := Fin.ext rfl
        rw [hcs, hsc] at hst
        rcases hprev with h0 | h1
        · rw [h0] at hst
          rcases fin4_cases (p ⟨m + 1, by omega⟩) with hv | hv | hv | hv <;>
            rw [hv] at hst ⊢ <;> cases x ⟨m, by omega⟩ <;> simp at hst ⊢
        · rw [h1] at hst
          rcases fin4_cases (p ⟨m + 1, by omega⟩) with hv | hv | hv | hv <;>
            rw [hv] at hst ⊢ <;> cases x ⟨m, by omega⟩ <;> simp at hst ⊢
    have hmono : ∀ m : ℕ, (hm : m + 1 < h) → p ⟨m, by omega⟩ = 1 → p ⟨m + 1, by omega⟩ = 1 := by
      intro m hm h1
      have hst := hsteps ⟨m, by omega⟩
      simp only [mkRead, hm, ↓reduceIte] at hst
      have hcs : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, by omega⟩ := Fin.ext rfl
      have hsc : (⟨m, by omega⟩ : Fin n).succ = ⟨m + 1, by omega⟩ := Fin.ext rfl
      rw [hcs, hsc, h1] at hst
      rcases fin4_cases (p ⟨m + 1, by omega⟩) with hv | hv | hv | hv <;>
        rw [hv] at hst ⊢ <;> cases x ⟨m, by omega⟩ <;> simp at hst ⊢
    have hmono_le : ∀ a b : ℕ, (hab : a ≤ b) → (hb : b < h) → p ⟨a, by omega⟩ = 1 → p ⟨b, by omega⟩ = 1 := by
      intro a b
      induction b with
      | zero =>
        intro hab _ ha
        obtain rfl : a = 0 := by omega
        exact ha
      | succ b ih =>
        intro hab hb ha
        rcases Nat.lt_or_eq_of_le hab with hlt | rfl
        · exact hmono b hb (ih (by omega) (by omega) ha)
        · exact ha
    by_cases hlast : p ⟨h - 1, by omega⟩ = 0
    · have hall0 : ∀ m : ℕ, (hm : m < h) → p ⟨m, by omega⟩ = 0 := by
        intro m hm
        rcases h01 m hm with h0 | h1
        · exact h0
        · have := hmono_le m (h - 1) (by omega) (by omega) h1
          rw [hlast] at this; exact absurd this (by decide)
      have hxlast : x ⟨h - 1, by omega⟩ = true := by
        have hst := hsteps ⟨h - 1, by omega⟩
        have h2 : h - 1 + 1 = h := by omega
        simp only [mkRead, h2, lt_self_iff_false, ↓reduceIte, beq_self_eq_true] at hst
        have hcs : (⟨h - 1, by omega⟩ : Fin n).castSucc = ⟨h - 1, by omega⟩ := Fin.ext rfl
        have hsc : (⟨h - 1, by omega⟩ : Fin n).succ = ⟨h, by omega⟩ := Fin.ext (by simp; omega)
        rw [hcs, hsc, hlast, htail0 ⟨h, by omega⟩ (by simp)] at hst
        cases hx : x ⟨h - 1, by omega⟩ <;> simp [hx] at hst ⊢
      refine ⟨⟨h - 1, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, hxlast⟩
      · funext t
        by_cases ht : t.val < h
        · rw [show t = ⟨t.val, by omega⟩ from Fin.ext rfl, hall0 t.val ht]
          simp [walkA, show ¬ (h - 1 < t.val ∧ t.val < h) by omega]
        · rw [htail0 t (by omega)]
          simp [walkA, ht]
    · have hlast1 : p ⟨h - 1, by omega⟩ = 1 := by
        rcases h01 (h - 1) (by omega) with h0 | h1
        · exact absurd h0 hlast
        · exact h1
      have hex1 : ∃ m : ℕ, ∃ hm : m < h, p ⟨m, by omega⟩ = 1 := ⟨h - 1, by omega, hlast1⟩
      let m₁ := Nat.find hex1
      have hm₁_spec : ∃ hm : m₁ < h, p ⟨m₁, by omega⟩ = 1 := Nat.find_spec hex1
      have hm₁_lt : m₁ < h := hm₁_spec.1
      have hm₁_eq : p ⟨m₁, by omega⟩ = 1 := hm₁_spec.2
      have hm₁_pos : 0 < m₁ := by
        by_contra h0
        have hm0 : m₁ = 0 := by omega
        have := hm₁_eq
        rw [show (⟨m₁, by omega⟩ : Fin (n + 1)) = 0 from Fin.ext hm0, hp0] at this
        exact absurd this (by decide)
      let k := m₁ - 1
      have hkm : k + 1 = m₁ := by omega
      have hpk0 : p ⟨k, by omega⟩ = 0 := by
        have hlt : k < m₁ := by omega
        have hnot := Nat.find_min hex1 hlt
        rcases h01 k (by omega) with h0 | h1
        · exact h0
        · exact absurd ⟨by omega, h1⟩ hnot
      have hxk : x ⟨k, by omega⟩ = true := by
        have hst := hsteps ⟨k, by omega⟩
        have hlt : k + 1 < h := by omega
        simp only [mkRead, hlt, ↓reduceIte] at hst
        have hcs : (⟨k, by omega⟩ : Fin n).castSucc = ⟨k, by omega⟩ := Fin.ext rfl
        have hsc : (⟨k, by omega⟩ : Fin n).succ = ⟨m₁, by omega⟩ := Fin.ext (by simp; omega)
        rw [hcs, hsc, hpk0, hm₁_eq] at hst
        cases hx : x ⟨k, by omega⟩ <;> simp [hx] at hst ⊢
      refine ⟨⟨k, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, hxk⟩
      · funext t
        by_cases ht : t.val < h
        · by_cases hkt : k < t.val
          · have ht1 : p t = 1 := by
              rw [show t = ⟨t.val, by omega⟩ from Fin.ext rfl]
              exact hmono_le m₁ t.val (by omega) ht hm₁_eq
            rw [ht1]; simp [walkA, hkt, ht]
          · have ht0 : p t = 0 := by
              have hnot := Nat.find_min hex1 (show t.val < m₁ by omega)
              rcases h01 t.val ht with h0 | h1
              · rw [show t = ⟨t.val, by omega⟩ from Fin.ext rfl]; exact h0
              · exact absurd ⟨ht, h1⟩ hnot
            rw [ht0]; simp [walkA, hkt]
        · rw [htail0 t (by omega)]
          simp [walkA, ht]

private def walkB {n : ℕ} (h : ℕ) (x : Fin n → Bool) : Fin (n + 1) → Fin 4 :=
  fun t => if t.val < h ∧ prefPar x t.val = true then 3 else 2

private lemma card_validB {n h : ℕ} (hh : 0 < h) (hhn : h ≤ n) (target : Bool)
    (x : Fin n → Bool) :
    ((validWalks (mkRead n h target) x).filter (fun p => p 0 = 2)).card =
      if prefPar x h = target then 1 else 0 := by
  have huniq : ∀ p ∈ (validWalks (mkRead n h target) x).filter (fun p => p 0 = 2),
      p = walkB h x ∧ prefPar x h = target := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpv, hp0⟩ := hp
    have htail := valid_tail_const hh hhn target x hpv
    have htail2 : ∀ t : Fin (n + 1), h ≤ t.val → p t = 2 := by
      rcases htail with ⟨h0, _⟩ | ⟨_, h2⟩
      · rw [hp0] at h0; exact absurd h0 (by decide)
      · exact h2
    simp only [validWalks, Finset.mem_filter, Finset.mem_univ, true_and] at hpv
    obtain ⟨_, hsteps⟩ := hpv
    have hpref : ∀ m : ℕ, (hm : m < h) → p ⟨m, by omega⟩ = if prefPar x m = true then 3 else 2 := by
      intro m
      induction m with
      | zero => intro _; simp [prefPar_zero]; exact hp0
      | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hst := hsteps ⟨m, by omega⟩
        simp only [mkRead, hm, ↓reduceIte] at hst
        have hcs : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, by omega⟩ := Fin.ext rfl
        have hsc : (⟨m, by omega⟩ : Fin n).succ = ⟨m + 1, by omega⟩ := Fin.ext rfl
        rw [hcs, hsc, hprev] at hst
        rw [prefPar_succ x (by omega)]
        cases hp_m : prefPar x m <;> cases hx_m : x ⟨m, by omega⟩ <;>
          simp [hp_m, hx_m] at hst ⊢ <;>
          (rcases fin4_cases (p ⟨m + 1, by omega⟩) with hv | hv | hv | hv <;>
            rw [hv] at hst ⊢ <;> simp at hst ⊢)
    have hpeq : p = walkB h x := by
      funext t
      by_cases ht : t.val < h
      · rw [show t = ⟨t.val, by omega⟩ from Fin.ext rfl, hpref t.val ht]
        simp [walkB, ht]
      · rw [htail2 t (by omega)]
        simp [walkB, ht]
    have hpar : prefPar x h = target := by
      have hst := hsteps ⟨h - 1, by omega⟩
      have h2 : h - 1 + 1 = h := by omega
      simp only [mkRead, h2, lt_self_iff_false, ↓reduceIte, beq_self_eq_true] at hst
      have hcs : (⟨h - 1, by omega⟩ : Fin n).castSucc = ⟨h - 1, by omega⟩ := Fin.ext rfl
      have hsc : (⟨h - 1, by omega⟩ : Fin n).succ = ⟨h, by omega⟩ := Fin.ext (by simp; omega)
      rw [hcs, hsc, hpref (h - 1) (by omega), htail2 ⟨h, by omega⟩ (by simp)] at hst
      rw [show h = (h - 1) + 1 by omega, prefPar_succ x (by omega)]
      cases hp1 : prefPar x (h - 1) <;> cases hx1 : x ⟨h - 1, by omega⟩ <;>
        cases target <;> simp [hp1, hx1] at hst ⊢
    exact ⟨hpeq, hpar⟩
  by_cases hpar : prefPar x h = target
  · simp only [hpar, ↓reduceIte]
    have hmem : walkB h x ∈ (validWalks (mkRead n h target) x).filter (fun p => p 0 = 2) := by
      simp only [validWalks, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [walkB, prefPar_zero, show ¬ (n < h) by omega]
      · intro i
        unfold mkRead walkB
        by_cases h1 : i.val + 1 < h
        · have hih : i.val < h := by omega
          simp only [h1, ↓reduceIte, Fin.val_castSucc, Fin.val_succ, hih]
          have hps := prefPar_succ x i.isLt
          have heq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
          rw [heq] at hps
          rw [hps]
          cases prefPar x i.val <;> cases x i <;> simp
        · by_cases h2 : i.val + 1 = h
          · have hih : i.val < h := by omega
            simp only [h2, lt_self_iff_false, ↓reduceIte, beq_self_eq_true, Fin.val_castSucc,
              Fin.val_succ, hih, false_and]
            have hps := prefPar_succ x i.isLt
            have heq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
            rw [heq, h2, hpar] at hps
            cases hp1 : prefPar x i.val <;> cases hx1 : x i <;> cases target <;>
              simp [hp1, hx1] at hps ⊢
          · simp [h1, h2, show ¬ (i.val < h) by omega]
      · simp [walkB, prefPar_zero]
    have hsing : (validWalks (mkRead n h target) x).filter (fun p => p 0 = 2) = {walkB h x} := by
      ext p
      simp only [Finset.mem_singleton]
      exact ⟨fun hp => (huniq p hp).1, fun hp => hp ▸ hmem⟩
    rw [hsing, Finset.card_singleton]
  · simp only [hpar, ↓reduceIte]
    have hemp : (validWalks (mkRead n h target) x).filter (fun p => p 0 = 2) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      exact hpar (huniq p hp).2
    rw [hemp, Finset.card_empty]

private lemma mult_mkRead {n h : ℕ} (hh : 0 < h) (hhn : h ≤ n) (target : Bool)
    (x : Fin n → Bool) :
    (validWalks (mkRead n h target) x).card =
      wtPref h x + (if prefPar x h = target then 1 else 0) := by
  have hunion : validWalks (mkRead n h target) x =
      ((validWalks (mkRead n h target) x).filter (fun p => p 0 = 0)) ∪
      ((validWalks (mkRead n h target) x).filter (fun p => p 0 = 2)) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases valid_tail_const hh hhn target x hp with ⟨h0, _⟩ | ⟨h2, _⟩
      · exact Or.inl ⟨hp, h0⟩
      · exact Or.inr ⟨hp, h2⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint
      ((validWalks (mkRead n h target) x).filter (fun p => p 0 = 0))
      ((validWalks (mkRead n h target) x).filter (fun p => p 0 = 2)) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact absurd h2.2 (by decide)
  rw [hunion, Finset.card_union_of_disjoint hdisj, card_validA hh hhn, card_validB hh hhn]

private lemma card_wtPref_zero {n h : ℕ} (hhn : h ≤ n) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => wtPref h x = 0)).card = 2 ^ (n - h) := by
  let toTail : (Fin n → Bool) → (Fin (n - h) → Bool) := fun x j => x ⟨h + j.val, by omega⟩
  let ofTail : (Fin (n - h) → Bool) → (Fin n → Bool) := fun y i =>
    if hi : h ≤ i.val then y ⟨i.val - h, by omega⟩ else false
  have hbij : ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => wtPref h x = 0)).card =
      (Finset.univ : Finset (Fin (n - h) → Bool)).card := by
    refine Finset.card_bij (fun x _ => toTail x) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro x₁ hx₁ x₂ hx₂ hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, wtPref, Finset.card_eq_zero,
        Finset.eq_empty_iff_forall_notMem] at hx₁ hx₂
      funext i
      by_cases hi : i.val < h
      · have h1 : x₁ i = false := by
          cases h : x₁ i
          · rfl
          · exact absurd ⟨hi, h⟩ (hx₁ i)
        have h2 : x₂ i = false := by
          cases h : x₂ i
          · rfl
          · exact absurd ⟨hi, h⟩ (hx₂ i)
        rw [h1, h2]
      · have hpt := congrFun hEq ⟨i.val - h, by omega⟩
        dsimp only [toTail] at hpt
        have heq : (⟨h + (i.val - h), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
        rwa [heq] at hpt
    · intro y _
      refine ⟨ofTail y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, wtPref, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]
        intro i _ ⟨hi, hxi⟩
        simp only [ofTail, show ¬ (h ≤ i.val) by omega, ↓reduceDIte] at hxi
        exact Bool.noConfusion hxi
      · funext j
        simp [toTail, ofTail]
  rw [hbij]
  simp [Fintype.card_pi]

private lemma wtPref_le {n : ℕ} (h : ℕ) (x : Fin n → Bool) : wtPref h x ≤ h := by
  unfold wtPref
  calc ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < h ∧ x i = true)).card
      ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < h)).card :=
        Finset.card_le_card (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact hi.1)
    _ ≤ (Finset.range h).card := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hi ⊢
          exact hi
        · intro a _ b _ hab; exact Fin.ext hab
    _ = h := Finset.card_range h

private lemma exists_wtPref_eq {n h : ℕ} (hhn : h ≤ n) (m : ℕ) (hm : m ≤ h) :
    ∃ x : Fin n → Bool, wtPref h x = m := by
  refine ⟨fun i => decide (i.val < m), ?_⟩
  unfold wtPref
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < h ∧ decide (i.val < m) = true)).card =
      (Finset.range m).card := by
    refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_range] at hi ⊢
      exact hi.2
    · intro a _ b _ hab; exact Fin.ext hab
    · intro a ha
      rw [Finset.mem_range] at ha
      refine ⟨⟨a, by omega⟩, ?_, rfl⟩
      simp [show a < h by omega, ha]
  rw [hcard, Finset.card_range]

private def wtFin {m : ℕ} (v : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun k : Fin m => v k = true)).card

private lemma wtFin_update_not {m : ℕ} (v : Fin m → Bool) (a : Fin m) :
    wtFin (Function.update v a (!v a)) % 2 ≠ wtFin v % 2 := by
  unfold wtFin
  by_cases hva : v a = true
  · have hEq : (Finset.univ : Finset (Fin m)).filter (fun k => v k = true) =
        insert a ((Finset.univ : Finset (Fin m)).filter (fun k => Function.update v a (!v a) k = true)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hka : k = a
      · subst hka; simp [hva]
      · simp [hka]
    have hnot : a ∉ (Finset.univ : Finset (Fin m)).filter (fun k => Function.update v a (!v a) k = true) := by
      simp [hva]
    rw [hEq, Finset.card_insert_of_notMem hnot]
    omega
  · have hvaf : v a = false := Bool.eq_false_iff.mpr hva
    have hEq : (Finset.univ : Finset (Fin m)).filter (fun k => Function.update v a (!v a) k = true) =
        insert a ((Finset.univ : Finset (Fin m)).filter (fun k => v k = true)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hka : k = a
      · subst hka; simp [hvaf]
      · simp [hka]
    have hnot : a ∉ (Finset.univ : Finset (Fin m)).filter (fun k => v k = true) := by simp [hvaf]
    rw [hEq, Finset.card_insert_of_notMem hnot]
    omega

private lemma parity_moment_diff (m j : ℕ) :
    (∑ v : Fin m → Bool, (if wtFin v % 2 = 0 then (1 : ℤ) else -1) * (wtFin v : ℤ) ^ j) =
      (if j = m then (if m % 2 = 0 then (1 : ℤ) else -1) * (Nat.factorial m : ℤ) else
        if j < m then 0 else
          ∑ f : Fin j → Fin m, if Function.Surjective f then (if m % 2 = 0 then (1 : ℤ) else -1) else 0) := by
  have hexpand : ∀ v : Fin m → Bool,
      ((wtFin v : ℤ) ^ j) =
        ∑ f : Fin j → Fin m, (if ∀ t : Fin j, v (f t) = true then (1 : ℤ) else 0) := by
    intro v
    have hw : (wtFin v : ℤ) = ∑ k : Fin m, (if v k = true then (1 : ℤ) else 0) := by
      simp [wtFin, Finset.sum_boole]
    rw [hw, Fintype.sum_pow]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hall : ∀ t : Fin j, v (f t) = true
    · simp [hall]
    · simp only [hall, ↓reduceIte]
      push Not at hall
      rcases hall with ⟨t₀, ht₀⟩
      exact Finset.prod_eq_zero (Finset.mem_univ t₀) (by simp [ht₀])
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ f : Fin j → Fin m,
      (∑ v : Fin m → Bool, (if wtFin v % 2 = 0 then (1 : ℤ) else -1) *
        (if ∀ t : Fin j, v (f t) = true then (1 : ℤ) else 0)) =
      if Function.Surjective f then (if m % 2 = 0 then (1 : ℤ) else -1) else 0 := by
    intro f
    by_cases hsurj : Function.Surjective f
    · simp only [hsurj, ↓reduceIte]
      rw [Finset.sum_eq_single (fun _ : Fin m => true)]
      · have hall : wtFin (fun _ : Fin m => true) = m := by simp [wtFin]
        simp [hall]
      · intro v _ hne
        have hex : ∃ a : Fin m, v a ≠ true := by
          by_contra hall; push Not at hall; exact hne (funext hall)
        rcases hex with ⟨a, ha⟩
        rcases hsurj a with ⟨t, rfl⟩
        have hnot : ¬ ∀ t' : Fin j, v (f t') = true := fun h => ha (h t)
        simp [hnot]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hsurj, ↓reduceIte]
      have hex : ∃ a : Fin m, ∀ t : Fin j, f t ≠ a := by
        simpa [Function.Surjective] using hsurj
      rcases hex with ⟨a, ha⟩
      let flip : (Fin m → Bool) → (Fin m → Bool) := fun v => Function.update v a (!v a)
      have hflip_invol : ∀ v, flip (flip v) = v := fun v => by
        funext k
        by_cases hka : k = a
        · subst hka; simp [flip]
        · simp [flip, hka]
      have hterm : ∀ v,
          (if wtFin (flip v) % 2 = 0 then (1 : ℤ) else -1) *
            (if ∀ t : Fin j, flip v (f t) = true then (1 : ℤ) else 0) =
          -((if wtFin v % 2 = 0 then (1 : ℤ) else -1) *
            (if ∀ t : Fin j, v (f t) = true then (1 : ℤ) else 0)) := by
        intro v
        have hcov : (∀ t : Fin j, flip v (f t) = true) ↔ (∀ t : Fin j, v (f t) = true) := by
          refine forall_congr' fun t => ?_
          simp [flip, ha t]
        have hpar : wtFin (flip v) % 2 ≠ wtFin v % 2 := wtFin_update_not v a
        rcases Nat.mod_two_eq_zero_or_one (wtFin v) with h0 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (wtFin (flip v)) with h0' | h1'
        · omega
        · simp [h0, h1', hcov]; split_ifs <;> rfl
        · simp [h1, h0', hcov]; split_ifs <;> rfl
        · omega
      let g : (Fin m → Bool) → ℤ := fun v =>
        (if wtFin v % 2 = 0 then (1 : ℤ) else -1) *
          (if ∀ t : Fin j, v (f t) = true then (1 : ℤ) else 0)
      have hsum_flip : (∑ v : Fin m → Bool, g (flip v)) = ∑ v : Fin m → Bool, g v := by
        refine Fintype.sum_equiv ⟨flip, flip, hflip_invol, hflip_invol⟩ _ _ fun _ => rfl
      have hsum_neg : (∑ v : Fin m → Bool, g (flip v)) = - ∑ v : Fin m → Bool, g v := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun v _ => hterm v
      have : (∑ v : Fin m → Bool, g v) = - ∑ v : Fin m → Bool, g v := hsum_flip.symm.trans hsum_neg
      change (∑ v : Fin m → Bool, g v) = 0
      omega
  simp_rw [hinner]
  by_cases hjm : j = m
  · subst hjm
    simp only [↓reduceIte]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have hcard : ((Finset.univ : Finset (Fin j → Fin j)).filter (fun f => Function.Surjective f)).card =
        Nat.factorial j := by
      have hfin : Fintype.card (Equiv.Perm (Fin j)) =
          ((Finset.univ : Finset (Fin j → Fin j)).filter (fun f => Function.Surjective f)).card := by
        refine Finset.card_bij (fun e _ => (e : Fin j → Fin j)) ?_ ?_ ?_
        · intro e _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact e.surjective
        · intro e₁ _ e₂ _ h; exact Equiv.ext (congrFun h)
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
          exact ⟨Equiv.ofBijective f hbij, Finset.mem_univ _, rfl⟩
      rw [← hfin, Fintype.card_perm, Fintype.card_fin]
    exact_mod_cast hcard
  · simp only [hjm, ↓reduceIte]
    by_cases hlt : j < m
    · simp only [hlt, ↓reduceIte]
      refine Finset.sum_eq_zero fun f _ => ?_
      have hns : ¬ Function.Surjective f := fun hs => by
        have hle := Fintype.card_le_of_surjective f hs
        simp only [Fintype.card_fin] at hle
        omega
      simp [hns]
    · simp only [hlt, ↓reduceIte]

private lemma sum_moment_factor {n h : ℕ} (hhn : h ≤ n) (g : ℕ → ℕ) :
    (∑ x : Fin n → Bool, g (wtPref h x)) =
      2 ^ (n - h) * ∑ y : Fin h → Bool, g (wtFin y) := by
  let splitEquiv : (Fin n → Bool) ≃ (Fin h → Bool) × (Fin (n - h) → Bool) :=
    { toFun := fun x => (fun i => x ⟨i.val, by omega⟩, fun j => x ⟨h + j.val, by omega⟩)
      invFun := fun p i =>
        if hi : i.val < h then p.1 ⟨i.val, hi⟩ else p.2 ⟨i.val - h, by omega⟩
      left_inv := fun x => funext fun i => by
        by_cases hi : i.val < h
        · simp [hi]
        · simp only [hi, ↓reduceDIte]
          congr 1; apply Fin.ext; simp; omega
      right_inv := fun ⟨y, z⟩ => by
        ext i
        · simp [i.isLt]
        · simp [show ¬ (h + i.val < h) by omega] }
  have hwt : ∀ x : Fin n → Bool, wtPref h x = wtFin (splitEquiv x).1 := by
    intro x
    unfold wtPref wtFin
    refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2.1⟩) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.2
    · intro a _ b _ hab; exact Fin.ext (congrArg (Fin.val : Fin h → ℕ) hab)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨⟨k.val, by omega⟩, ?_, Fin.ext rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k.isLt, hk⟩
  rw [Fintype.sum_equiv splitEquiv _ (fun p => g (wtFin p.1)) (fun x => by rw [hwt x])]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum]

private lemma sum_even_odd_completion (h j : ℕ) :
    ((∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 1 then 1 else 0) ^ j : ℕ) : ℤ) -
    ((∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 0 then 1 else 0) ^ j : ℕ) : ℤ) =
      ∑ v : Fin (h + 1) → Bool, (if wtFin v % 2 = 0 then (1 : ℤ) else -1) * (wtFin v : ℤ) ^ j := by
  let extEven : (Fin h → Bool) → (Fin (h + 1) → Bool) :=
    fun y => Fin.snoc y (decide (wtFin y % 2 = 1))
  let extOdd : (Fin h → Bool) → (Fin (h + 1) → Bool) :=
    fun y => Fin.snoc y (decide (wtFin y % 2 = 0))
  have hwt_snoc : ∀ (y : Fin h → Bool) (b : Bool),
      wtFin (Fin.snoc (α := fun _ => Bool) y b) = wtFin y + (if b = true then 1 else 0) := by
    intro y b
    unfold wtFin
    have hsplit : ((Finset.univ : Finset (Fin (h + 1))).filter
        (fun k => Fin.snoc (α := fun _ => Bool) y b k = true)).card =
        ((Finset.univ : Finset (Fin h)).filter (fun k => y k = true)).card +
        (if b = true then 1 else 0) := by
      have hcast : (Finset.univ : Finset (Fin (h + 1))).filter
          (fun k => Fin.snoc (α := fun _ => Bool) y b k = true) =
          (((Finset.univ : Finset (Fin h)).filter (fun k => y k = true)).image Fin.castSucc) ∪
          (if b = true then {Fin.last h} else ∅) := by
        ext k
        refine Fin.lastCases ?_ ?_ k
        · simp [Fin.snoc]
          cases b <;> simp
        · intro i
          simp [Fin.snoc, Fin.castSucc_ne_last]
          cases b <;> simp [Fin.castSucc_ne_last]
      have hdisj : Disjoint
          (((Finset.univ : Finset (Fin h)).filter (fun k => y k = true)).image Fin.castSucc)
          (if b = true then {Fin.last h} else ∅) := by
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        rcases Finset.mem_image.mp hk1 with ⟨i, _, rfl⟩
        cases b
        · simp at hk2
        · simp only [↓reduceIte, Finset.mem_singleton] at hk2
          exact Fin.castSucc_ne_last i hk2
      rw [hcast, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (Fin.castSucc_injective h)]
      cases b <;> simp
    exact hsplit
  have heven_sum : (∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 1 then 1 else 0) ^ j) =
      ∑ v ∈ (Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 0),
        (wtFin v) ^ j := by
    refine Finset.sum_bij (fun y _ => extEven y) ?_ ?_ ?_ ?_
    · intro y _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, extEven, hwt_snoc, decide_eq_true_eq]
      split_ifs <;> omega
    · intro y₁ _ y₂ _ hEq
      funext i
      have hpt := congrFun hEq i.castSucc
      simpa [extEven, Fin.snoc] using hpt
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨Fin.init v, Finset.mem_univ _, ?_⟩
      have hv_snoc : v = Fin.snoc (α := fun _ => Bool) (Fin.init v) (v (Fin.last h)) := by
        funext k; refine Fin.lastCases ?_ ?_ k <;> simp [Fin.snoc, Fin.init]
      have hwtv := hwt_snoc (Fin.init v) (v (Fin.last h))
      rw [← hv_snoc] at hwtv
      have hlast : v (Fin.last h) = decide (wtFin (Fin.init v) % 2 = 1) := by
        cases hvl : v (Fin.last h)
        · simp [hvl] at hwtv ⊢; omega
        · simp [hvl] at hwtv ⊢; omega
      conv_rhs => rw [hv_snoc, hlast]
    · intro y _
      simp only [extEven, hwt_snoc, decide_eq_true_eq]
  have hodd_sum : (∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 0 then 1 else 0) ^ j) =
      ∑ v ∈ (Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 1),
        (wtFin v) ^ j := by
    refine Finset.sum_bij (fun y _ => extOdd y) ?_ ?_ ?_ ?_
    · intro y _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, extOdd, hwt_snoc, decide_eq_true_eq]
      split_ifs <;> omega
    · intro y₁ _ y₂ _ hEq
      funext i
      have hpt := congrFun hEq i.castSucc
      simpa [extOdd, Fin.snoc] using hpt
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨Fin.init v, Finset.mem_univ _, ?_⟩
      have hv_snoc : v = Fin.snoc (α := fun _ => Bool) (Fin.init v) (v (Fin.last h)) := by
        funext k; refine Fin.lastCases ?_ ?_ k <;> simp [Fin.snoc, Fin.init]
      have hwtv := hwt_snoc (Fin.init v) (v (Fin.last h))
      rw [← hv_snoc] at hwtv
      have hlast : v (Fin.last h) = decide (wtFin (Fin.init v) % 2 = 0) := by
        cases hvl : v (Fin.last h)
        · simp [hvl] at hwtv ⊢; omega
        · simp [hvl] at hwtv ⊢; omega
      conv_rhs => rw [hv_snoc, hlast]
    · intro y _
      simp only [extOdd, hwt_snoc, decide_eq_true_eq]
  rw [heven_sum, hodd_sum]
  push_cast
  have hpart : (Finset.univ : Finset (Fin (h + 1) → Bool)) =
      ((Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 0)) ∪
      ((Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 1)) := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact Nat.mod_two_eq_zero_or_one (wtFin v)
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 0))
      ((Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 1)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega
  conv_rhs => rw [hpart, Finset.sum_union hdisj]
  have hs1 : (∑ v ∈ (Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 0),
      (if wtFin v % 2 = 0 then (1 : ℤ) else -1) * (wtFin v : ℤ) ^ j) =
      ∑ v ∈ (Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 0),
        (wtFin v : ℤ) ^ j :=
    Finset.sum_congr rfl fun v hv => by simp [(Finset.mem_filter.mp hv).2]
  have hs2 : (∑ v ∈ (Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 1),
      (if wtFin v % 2 = 0 then (1 : ℤ) else -1) * (wtFin v : ℤ) ^ j) =
      - ∑ v ∈ (Finset.univ : Finset (Fin (h + 1) → Bool)).filter (fun v => wtFin v % 2 = 1),
        (wtFin v : ℤ) ^ j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v hv => by
      have h1 : wtFin v % 2 = 1 := (Finset.mem_filter.mp hv).2
      simp [show ¬ (wtFin v % 2 = 0) by omega]
  rw [hs1, hs2, sub_eq_add_neg]

private lemma prove_332 (n h : ℕ) (hh : 0 < h) (hhn : h ≤ n) :
    let W := Fin n → Bool
    let Edge := Fin n × Fin 4 × Bool × Fin 4
    let mult := fun (enabled : Edge → Bool) (x : W) =>
      (Finset.univ.filter (fun p : Fin (n + 1) → Fin 4 =>
        p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i, p i.castSucc, x i, p i.succ) = true)).card
    let words := fun (enabled : Edge → Bool) => Finset.univ.filter (fun x : W => 0 < mult enabled x)
    let levels := fun (enabled : Edge → Bool) => ((words enabled).image (mult enabled)).card
    let moment := fun (enabled : Edge → Bool) (j : ℕ) => ∑ x : W, (mult enabled x) ^ j
    ∃ evenRead oddRead : Edge → Bool,
      (words evenRead).card + 2 ^ (n - h) = 2 ^ n ∧ (words oddRead).card = 2 ^ n ∧
      levels evenRead = (h + 1) / 2 ∧ levels oddRead = (h + 2) / 2 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ h → moment evenRead j = moment oddRead j) ∧
      Nat.dist (moment evenRead (h + 1)) (moment oddRead (h + 1)) =
        2 ^ (n - h) * Nat.factorial (h + 1) := by
  intro W Edge mult words levels moment
  refine ⟨mkRead n h true, mkRead n h false, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hmult : ∀ x : W, mult (mkRead n h true) x = wtPref h x + (if wtPref h x % 2 = 1 then 1 else 0) :=
      fun x => by
        have h1 := mult_mkRead hh hhn true x
        simpa [mult, validWalks, prefPar] using h1
    have hzero : (Finset.univ : Finset W).filter (fun x => ¬ (0 < mult (mkRead n h true) x)) =
        (Finset.univ : Finset W).filter (fun x => wtPref h x = 0) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmult]
      split_ifs <;> omega
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset W))
      (fun x => 0 < mult (mkRead n h true) x)
    rw [hzero, card_wtPref_zero hhn] at hsum
    have huniv : (Finset.univ : Finset W).card = 2 ^ n := by simp [W, Fintype.card_pi]
    rw [huniv] at hsum
    exact hsum
  ·
    have hmult : ∀ x : W, mult (mkRead n h false) x = wtPref h x + (if wtPref h x % 2 = 0 then 1 else 0) :=
      fun x => by
        have h1 := mult_mkRead hh hhn false x
        simp only [mult, validWalks, prefPar, decide_eq_false_iff_not] at h1 ⊢
        rcases Nat.mod_two_eq_zero_or_one (wtPref h x) with hm | hm <;> simp [hm] at h1 ⊢ <;> exact h1
    have hall : words (mkRead n h false) = Finset.univ := by
      ext x
      simp only [words, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hmult]
      split_ifs <;> omega
    rw [hall]
    simp [W, Fintype.card_pi]
  ·
    have hmult : ∀ x : W, mult (mkRead n h true) x = wtPref h x + (if wtPref h x % 2 = 1 then 1 else 0) :=
      fun x => by
        have h1 := mult_mkRead hh hhn true x
        simpa [mult, validWalks, prefPar] using h1
    have himg : (words (mkRead n h true)).image (mult (mkRead n h true)) =
        (Finset.range ((h + 1) / 2)).image (fun m => 2 * (m + 1)) := by
      ext v
      simp only [Finset.mem_image, words, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨x, hxpos, rfl⟩
        rw [hmult] at hxpos ⊢
        have hle := wtPref_le h x
        have hpos : 0 < wtPref h x := by split_ifs at hxpos <;> omega
        refine ⟨(wtPref h x - 1) / 2, by omega, ?_⟩
        rcases Nat.mod_two_eq_zero_or_one (wtPref h x) with hm | hm <;> simp [hm] <;> omega
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨x, hx⟩ := exists_wtPref_eq hhn (2 * m + 1) (by omega)
        refine ⟨x, ?_, ?_⟩
        · rw [hmult, hx]; omega
        · rw [hmult, hx]
          have : (2 * m + 1) % 2 = 1 := by omega
          simp [this]; omega
    unfold levels
    rw [himg, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]
  ·
    have hmult : ∀ x : W, mult (mkRead n h false) x = wtPref h x + (if wtPref h x % 2 = 0 then 1 else 0) :=
      fun x => by
        have h1 := mult_mkRead hh hhn false x
        simp only [mult, validWalks, prefPar, decide_eq_false_iff_not] at h1 ⊢
        rcases Nat.mod_two_eq_zero_or_one (wtPref h x) with hm | hm <;> simp [hm] at h1 ⊢ <;> exact h1
    have himg : (words (mkRead n h false)).image (mult (mkRead n h false)) =
        (Finset.range ((h + 2) / 2)).image (fun m => 2 * m + 1) := by
      ext v
      simp only [Finset.mem_image, words, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨x, _, rfl⟩
        rw [hmult]
        have hle := wtPref_le h x
        refine ⟨wtPref h x / 2, by omega, ?_⟩
        rcases Nat.mod_two_eq_zero_or_one (wtPref h x) with hm | hm <;> simp [hm] <;> omega
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨x, hx⟩ := exists_wtPref_eq hhn (2 * m) (by omega)
        refine ⟨x, ?_, ?_⟩
        · rw [hmult, hx]; split_ifs <;> omega
        · rw [hmult, hx]
          have : (2 * m) % 2 = 0 := by omega
          simp [this]
    unfold levels
    rw [himg, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]
  ·
    intro j _ hjh
    have heven : moment (mkRead n h true) j =
        2 ^ (n - h) * ∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 1 then 1 else 0) ^ j := by
      have h1 : moment (mkRead n h true) j =
          ∑ x : W, (wtPref h x + if wtPref h x % 2 = 1 then 1 else 0) ^ j :=
        Finset.sum_congr rfl fun x _ => by
          have hm := mult_mkRead hh hhn true x
          simpa [mult, validWalks, prefPar] using congrArg (· ^ j) hm
      rw [h1]
      exact sum_moment_factor hhn (fun w => (w + if w % 2 = 1 then 1 else 0) ^ j)
    have hodd : moment (mkRead n h false) j =
        2 ^ (n - h) * ∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 0 then 1 else 0) ^ j := by
      have h1 : moment (mkRead n h false) j =
          ∑ x : W, (wtPref h x + if wtPref h x % 2 = 0 then 1 else 0) ^ j :=
        Finset.sum_congr rfl fun x _ => by
          have hm := mult_mkRead hh hhn false x
          simp only [mult, validWalks, prefPar, decide_eq_false_iff_not] at hm ⊢
          rcases Nat.mod_two_eq_zero_or_one (wtPref h x) with hpar | hpar <;>
            simp [hpar] at hm ⊢ <;> rw [hm]
      rw [h1]
      exact sum_moment_factor hhn (fun w => (w + if w % 2 = 0 then 1 else 0) ^ j)
    rw [heven, hodd]
    congr 1
    have hdiff := sum_even_odd_completion h j
    rw [parity_moment_diff (h + 1) j] at hdiff
    simp only [show ¬ (j = h + 1) by omega, ↓reduceIte, show j < h + 1 by omega] at hdiff
    omega
  ·
    have heven : moment (mkRead n h true) (h + 1) =
        2 ^ (n - h) * ∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 1 then 1 else 0) ^ (h + 1) := by
      have h1 : moment (mkRead n h true) (h + 1) =
          ∑ x : W, (wtPref h x + if wtPref h x % 2 = 1 then 1 else 0) ^ (h + 1) :=
        Finset.sum_congr rfl fun x _ => by
          have hm := mult_mkRead hh hhn true x
          simpa [mult, validWalks, prefPar] using congrArg (· ^ (h + 1)) hm
      rw [h1]
      exact sum_moment_factor hhn (fun w => (w + if w % 2 = 1 then 1 else 0) ^ (h + 1))
    have hodd : moment (mkRead n h false) (h + 1) =
        2 ^ (n - h) * ∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 0 then 1 else 0) ^ (h + 1) := by
      have h1 : moment (mkRead n h false) (h + 1) =
          ∑ x : W, (wtPref h x + if wtPref h x % 2 = 0 then 1 else 0) ^ (h + 1) :=
        Finset.sum_congr rfl fun x _ => by
          have hm := mult_mkRead hh hhn false x
          simp only [mult, validWalks, prefPar, decide_eq_false_iff_not] at hm ⊢
          rcases Nat.mod_two_eq_zero_or_one (wtPref h x) with hpar | hpar <;>
            simp [hpar] at hm ⊢ <;> rw [hm]
      rw [h1]
      exact sum_moment_factor hhn (fun w => (w + if w % 2 = 0 then 1 else 0) ^ (h + 1))
    rw [heven, hodd]
    have hdiff := sum_even_odd_completion h (h + 1)
    rw [parity_moment_diff (h + 1) (h + 1)] at hdiff
    simp only [↓reduceIte] at hdiff
    set A := ∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 1 then 1 else 0) ^ (h + 1)
    set B := ∑ y : Fin h → Bool, (wtFin y + if wtFin y % 2 = 0 then 1 else 0) ^ (h + 1)
    rw [Nat.dist]
    by_cases hpar : (h + 1) % 2 = 0
    · simp only [hpar, ↓reduceIte, one_mul] at hdiff
      have hAB : A = B + Nat.factorial (h + 1) := by omega
      rw [hAB, mul_add]
      omega
    · simp only [hpar, ↓reduceIte] at hdiff
      have hBA : B = A + Nat.factorial (h + 1) := by omega
      rw [hBA, mul_add]
      omega

end PEqualNP.Outside.L_pcx_332_aux

theorem PEqualNP.Outside.L_pcx_332 : (∀ (n h : ℕ), 0 < h → h ≤ n →
  let W := Fin n → Bool
  let Edge := Fin n × Fin 4 × Bool × Fin 4
  let mult := fun (enabled : Edge → Bool) (x : W) =>
    (Finset.univ.filter (fun p : Fin (n+1) → Fin 4 =>
      p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i,p i.castSucc,x i,p i.succ) = true)).card
  let words := fun (enabled : Edge → Bool) => Finset.univ.filter (fun x : W => 0 < mult enabled x)
  let levels := fun (enabled : Edge → Bool) => ((words enabled).image (mult enabled)).card
  let moment := fun (enabled : Edge → Bool) (j : ℕ) => ∑ x : W, (mult enabled x)^j
  ∃ evenRead oddRead : Edge → Bool,
    (words evenRead).card + 2^(n-h) = 2^n ∧ (words oddRead).card = 2^n ∧
    levels evenRead = (h+1)/2 ∧ levels oddRead = (h+2)/2 ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ h → moment evenRead j = moment oddRead j) ∧
    Nat.dist (moment evenRead (h+1)) (moment oddRead (h+1)) =
      2^(n-h) * Nat.factorial (h+1)) :=
  PEqualNP.Outside.L_pcx_332_aux.prove_332
