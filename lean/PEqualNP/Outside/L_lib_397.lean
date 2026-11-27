import PEqualNP.Defs

-- L-lib-397: backward induction on n. The admissible run ending at n starts at lst n (one after the last cut
-- below n). A cut row is a rectangle, so a path through it splits into a domain test and a range test; a run
-- row lets both states stay, so with two states a run is crossed by staying or by one transition.

namespace PEqualNP.Outside.L_lib_397_aux

def lst (cut : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if cut m = true then m + 1 else lst cut m

theorem lst_spec (cut : ℕ → Bool) : ∀ m l : ℕ,
    (l ≤ m ∧ (l = 0 ∨ cut (l - 1) = true) ∧ ∀ i, l ≤ i → i < m → cut i = false) ↔ l = lst cut m := by
  intro m
  induction m with
  | zero =>
    intro l
    simp only [lst]
    constructor
    · rintro ⟨h, -, -⟩; omega
    · rintro rfl; exact ⟨le_refl _, Or.inl rfl, fun i h1 h2 => absurd h2 (by omega)⟩
  | succ m ih =>
    intro l
    by_cases hc : cut m = true
    · simp only [lst, hc, if_true]
      constructor
      · rintro ⟨h1, -, h3⟩
        by_contra hne
        have := h3 m (by omega) (by omega)
        rw [hc] at this; exact absurd this (by simp)
      · rintro rfl
        refine ⟨le_refl _, Or.inr (by simpa using hc), fun i h1 h2 => absurd h2 (by omega)⟩
    · have hc' : cut m = false := by simpa using hc
      simp only [lst, hc', Bool.false_eq_true, if_false]
      rw [← ih l]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hlm : l ≤ m := by
          by_contra hlt
          have : l = m + 1 := by omega
          subst this
          rcases h2 with h2 | h2
          · omega
          · simp only [Nat.add_sub_cancel] at h2; rw [hc'] at h2; exact absurd h2 (by simp)
        exact ⟨hlm, h2, fun i hi1 hi2 => h3 i hi1 (by omega)⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun i hi1 hi2 => ?_⟩
        by_cases him : i = m
        · subst him; exact hc'
        · exact h3 i hi1 (by omega)

def start (E : ℕ → Bool → Bool → Bool) (s : Bool) (l : ℕ) (a : Bool) : Prop :=
  if l = 0 then a = s else ∃ z : Bool, E (l - 1) z a = true

def Inner (E : ℕ → Bool → Bool → Bool) (s : Bool) (l r : ℕ) (P : Bool → Prop) : Prop :=
  ∃ a b : Bool, start E s l a ∧ P b ∧ (a = b ∨ ∃ i : ℕ, l ≤ i ∧ i < r ∧ E i a b = true)

def Early (E : ℕ → Bool → Bool → Bool) (cut : ℕ → Bool) (s : Bool) (m : ℕ) : Prop :=
  ∀ l r : ℕ, l ≤ r → r < m → (l = 0 ∨ cut (l - 1) = true) →
    (∀ i : ℕ, l ≤ i → i < r → cut i = false) → cut r = true →
    Inner E s l r (fun b => ∃ z : Bool, E r b z = true)

def Reach (E : ℕ → Bool → Bool → Bool) (s : Bool) (n : ℕ) (t : Bool) : Prop :=
  ∃ path : ℕ → Bool, path 0 = s ∧ path n = t ∧ ∀ i < n, E i (path i) (path (i + 1)) = true

theorem reach_succ (E : ℕ → Bool → Bool → Bool) (s : Bool) (n : ℕ) (t : Bool) :
    Reach E s (n + 1) t ↔ ∃ b, Reach E s n b ∧ E n b t = true := by
  constructor
  · rintro ⟨p, h0, hn, hs⟩
    exact ⟨p n, ⟨p, h0, rfl, fun i hi => hs i (by omega)⟩, hn ▸ hs n (by omega)⟩
  · rintro ⟨b, ⟨p, h0, hn, hs⟩, he⟩
    refine ⟨fun i => if i ≤ n then p i else t, by simpa using h0, by simp, fun i hi => ?_⟩
    by_cases hin : i < n
    · simp only [show i ≤ n by omega, show i + 1 ≤ n by omega, if_true]; exact hs i hin
    · have : i = n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]
      rw [hn]; exact he

theorem inner_eq_iff (E : ℕ → Bool → Bool → Bool) (s : Bool) (l r : ℕ) (P : Bool → Prop) :
    Inner E s l r P ↔ ∃ b, P b ∧ Inner E s l r (fun x => x = b) := by
  constructor
  · rintro ⟨a, b, h1, h2, h3⟩; exact ⟨b, h2, a, b, h1, rfl, h3⟩
  · rintro ⟨b, hb, a, b', h1, rfl, h3⟩; exact ⟨a, b', h1, hb, h3⟩

theorem inner_step (E : ℕ → Bool → Bool → Bool) (s : Bool) (L n : ℕ) (t : Bool) (hL : L ≤ n)
    (hstay : ∀ b : Bool, E n b b = true) :
    Inner E s L (n + 1) (fun x => x = t) ↔
      ∃ b, Inner E s L n (fun x => x = b) ∧ E n b t = true := by
  constructor
  · rintro ⟨a, b, h1, rfl, h3⟩
    rcases h3 with h3 | ⟨i, hi1, hi2, hi3⟩
    · subst h3; exact ⟨a, ⟨a, a, h1, rfl, Or.inl rfl⟩, hstay a⟩
    · by_cases hin : i < n
      · exact ⟨b, ⟨a, b, h1, rfl, Or.inr ⟨i, hi1, hin, hi3⟩⟩, hstay b⟩
      · have : i = n := by omega
        subst this
        exact ⟨a, ⟨a, a, h1, rfl, Or.inl rfl⟩, hi3⟩
  · rintro ⟨b, ⟨a, b', h1, rfl, h3⟩, he⟩
    rcases h3 with h3 | ⟨i, hi1, hi2, hi3⟩
    · subst h3; exact ⟨a, t, h1, rfl, Or.inr ⟨n, hL, by omega, he⟩⟩
    · by_cases hbt : b' = t
      · subst hbt; exact ⟨a, b', h1, rfl, Or.inr ⟨i, hi1, by omega, hi3⟩⟩
      · by_cases hat : a = t
        · exact ⟨a, t, h1, rfl, Or.inl hat⟩
        · have hab : a = b' := by
            cases a <;> cases b' <;> cases t <;> simp_all
          subst hab
          exact ⟨a, t, h1, rfl, Or.inr ⟨n, hL, by omega, he⟩⟩

theorem main (E : ℕ → Bool → Bool → Bool) (cut : ℕ → Bool) (s : Bool) (N : ℕ)
    (hstay : ∀ i < N, cut i = false → ∀ b : Bool, E i b b = true)
    (hrect : ∀ i < N, cut i = true → ∀ a b : Bool,
      E i a b = true ↔ (∃ z : Bool, E i a z = true) ∧ (∃ z : Bool, E i z b = true)) :
    ∀ m ≤ N, ∀ t : Bool, Reach E s m t ↔ Early E cut s m ∧ Inner E s (lst cut m) m (fun x => x = t) := by
  intro m
  induction m with
  | zero =>
    intro _ t
    simp only [lst]
    constructor
    · rintro ⟨p, h0, hn, -⟩
      exact ⟨fun l r _ hr => absurd hr (by omega), s, t, by simp [start], rfl, Or.inl (h0 ▸ hn)⟩
    · rintro ⟨-, a, b, h1, rfl, h3⟩
      simp only [start, if_true] at h1
      subst h1
      rcases h3 with h3 | ⟨i, -, hi, -⟩
      · exact ⟨fun _ => a, rfl, h3, fun i hi => absurd hi (by omega)⟩
      · omega
  | succ m ih =>
    intro hm t
    have ih' := ih (by omega)
    have hLm : lst cut m ≤ m := ((lst_spec cut m (lst cut m)).2 rfl).1
    -- Early (m+1) splits into Early m and the run ending at m when m is a cut
    have hearly : Early E cut s (m + 1) ↔ Early E cut s m ∧
        (cut m = true → Inner E s (lst cut m) m (fun b => ∃ z : Bool, E m b z = true)) := by
      constructor
      · intro h
        refine ⟨fun l r h1 h2 h3 h4 h5 => h l r h1 (by omega) h3 h4 h5, fun hc => ?_⟩
        have hs := (lst_spec cut m (lst cut m)).2 rfl
        exact h (lst cut m) m hs.1 (by omega) hs.2.1 hs.2.2 hc
      · rintro ⟨h, hc⟩ l r h1 h2 h3 h4 h5
        by_cases hr : r < m
        · exact h l r h1 hr h3 h4 h5
        · have : r = m := by omega
          subst this
          have hl : l = lst cut r := (lst_spec cut r l).1 ⟨h1, h3, h4⟩
          subst hl
          exact hc h5
    rw [reach_succ, hearly]
    by_cases hc : cut m = true
    · have hR := hrect m (by omega) hc
      have hlst : lst cut (m + 1) = m + 1 := by simp [lst, hc]
      rw [hlst]
      have hfin : Inner E s (m + 1) (m + 1) (fun x => x = t) ↔ ∃ z : Bool, E m z t = true := by
        constructor
        · rintro ⟨a, b, h1, rfl, h3⟩
          simp only [start, show m + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel] at h1
          rcases h3 with h3 | ⟨i, hi1, hi2, -⟩
          · subst h3; exact h1
          · omega
        · intro h
          exact ⟨t, t, by simpa [start] using h, rfl, Or.inl rfl⟩
      rw [hfin]
      constructor
      · rintro ⟨b, hb, he⟩
        rw [ih' b] at hb
        rw [hR] at he
        refine ⟨⟨hb.1, fun _ => ?_⟩, he.2⟩
        exact (inner_eq_iff E s _ _ _).2 ⟨b, he.1, hb.2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        obtain ⟨b, hb, hin⟩ := (inner_eq_iff E s _ _ _).1 (h2 hc)
        exact ⟨b, (ih' b).2 ⟨h1, hin⟩, (hR b t).2 ⟨hb, h3⟩⟩
    · have hc' : cut m = false := by simpa using hc
      have hlst : lst cut (m + 1) = lst cut m := by simp [lst, hc]
      rw [hlst, inner_step E s _ m t hLm (hstay m (by omega) hc')]
      constructor
      · rintro ⟨b, hb, he⟩
        rw [ih' b] at hb
        exact ⟨⟨hb.1, fun h => absurd h hc⟩, b, hb.2, he⟩
      · rintro ⟨⟨h1, -⟩, b, hb, he⟩
        exact ⟨b, (ih' b).2 ⟨h1, hb⟩, he⟩

theorem ok_iff (E : ℕ → Bool → Bool → Bool) (cut : ℕ → Bool) (s t : Bool) (n : ℕ) :
    (∀ l r : ℕ, l ≤ r → r ≤ n →
      (l = 0 ∨ cut (l - 1) = true) → (r = n ∨ cut r = true) →
      (∀ i : ℕ, l ≤ i → i < r → cut i = false) →
      ∃ a b : Bool,
        (if l = 0 then a = s else ∃ z : Bool, E (l - 1) z a = true) ∧
        (if r = n then b = t else ∃ z : Bool, E r b z = true) ∧
        (a = b ∨ ∃ i : ℕ, l ≤ i ∧ i < r ∧ E i a b = true)) ↔
    Early E cut s n ∧ Inner E s (lst cut n) n (fun x => x = t) := by
  constructor
  · intro h
    refine ⟨fun l r h1 h2 h3 h4 h5 => ?_, ?_⟩
    · obtain ⟨a, b, ha, hb, hab⟩ := h l r h1 (by omega) h3 (Or.inr h5) h4
      rw [if_neg (by omega)] at hb
      exact ⟨a, b, ha, hb, hab⟩
    · have hs := (lst_spec cut n (lst cut n)).2 rfl
      obtain ⟨a, b, ha, hb, hab⟩ := h (lst cut n) n hs.1 (le_refl _) hs.2.1 (Or.inl rfl) hs.2.2
      rw [if_pos rfl] at hb
      exact ⟨a, b, ha, hb, hab⟩
  · rintro ⟨he, hf⟩ l r h1 h2 h3 h4 h5
    by_cases hr : r = n
    · subst hr
      have hl : l = lst cut r := (lst_spec cut r l).1 ⟨h1, h3, h5⟩
      subst hl
      obtain ⟨a, b, ha, hb, hab⟩ := hf
      exact ⟨a, b, ha, by rw [if_pos rfl]; exact hb, hab⟩
    · have hc : cut r = true := by tauto
      obtain ⟨a, b, ha, hb, hab⟩ := he l r h1 (by omega) h3 h5 hc
      exact ⟨a, b, ha, by rw [if_neg hr]; exact hb, hab⟩

end PEqualNP.Outside.L_lib_397_aux

open PEqualNP.Outside.L_lib_397_aux in
theorem PEqualNP.Outside.L_lib_397 :
    ∀ (n : ℕ) (E : ℕ → Bool → Bool → Bool) (cut : ℕ → Bool) (s t : Bool),
      (∀ i < n, cut i = false → ∀ b : Bool, E i b b = true) →
      (∀ i < n, cut i = true → ∀ a b : Bool,
        E i a b = true ↔ (∃ z : Bool, E i a z = true) ∧ (∃ z : Bool, E i z b = true)) →
      ((∃ path : ℕ → Bool, path 0 = s ∧ path n = t ∧
           ∀ i < n, E i (path i) (path (i + 1)) = true) ↔
        ∀ l r : ℕ, l ≤ r → r ≤ n →
          (l = 0 ∨ cut (l - 1) = true) → (r = n ∨ cut r = true) →
          (∀ i : ℕ, l ≤ i → i < r → cut i = false) →
          ∃ a b : Bool,
            (if l = 0 then a = s else ∃ z : Bool, E (l - 1) z a = true) ∧
            (if r = n then b = t else ∃ z : Bool, E r b z = true) ∧
            (a = b ∨ ∃ i : ℕ, l ≤ i ∧ i < r ∧ E i a b = true)) := by
  intro n E cut s t hstay hrect
  rw [ok_iff]
  exact main E cut s n hstay hrect n (le_refl _) t
