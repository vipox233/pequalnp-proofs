import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25568_aux

def mix (word : ℤ → Bool) (z : ℤ) : Bool := xor (xor (word z) (word (z - 1))) (word (z + 1))

def before (word : ℤ → Bool) (z : ℤ) : Bool :=
  xor (mix word z) (!(mix word (z + 1)) && mix word (z + 2))

def state (pub : ℕ → ℤ → Bool) (start : ℤ → Bool) (rounds : ℕ) : ℤ → Bool :=
  (List.range rounds).foldl (fun (prev : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
    xor (xor (before prev z) (start (z + 1 - 2 * (tick : ℤ)))) (pub (tick + 1) z)) start

def guard (S : ℤ → Bool) (a : ℤ) : Bool := xor (xor (S a) (S (a + 1))) (S (a + 2))

def e (pub : ℕ → ℤ → Bool) (base : ℤ → Bool) (Q : ℤ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    if guard (state pub base t) (Q - 3 * (t : ℤ) + (e pub base Q t : ℤ) - 3) = false
    then e pub base Q t else e pub base Q t + 1

theorem e_succ (pub : ℕ → ℤ → Bool) (base : ℤ → Bool) (Q : ℤ) (t : ℕ) :
    e pub base Q (t + 1) =
      if guard (state pub base t) (Q - 3 * (t : ℤ) + (e pub base Q t : ℤ) - 3) = false
      then e pub base Q t else e pub base Q t + 1 := rfl

theorem e_succ_le (pub : ℕ → ℤ → Bool) (base : ℤ → Bool) (Q : ℤ) (t : ℕ) :
    e pub base Q t ≤ e pub base Q (t + 1) ∧ e pub base Q (t + 1) ≤ e pub base Q t + 1 := by
  rw [e_succ]; split_ifs <;> omega

theorem e_le (pub : ℕ → ℤ → Bool) (base : ℤ → Bool) (Q : ℤ) (t : ℕ) : e pub base Q t ≤ t := by
  induction t with
  | zero => exact le_of_eq rfl
  | succ t ih => have := e_succ_le pub base Q t; omega

theorem e_mono (pub : ℕ → ℤ → Bool) (base : ℤ → Bool) (Q : ℤ) : Monotone (e pub base Q) :=
  monotone_nat_of_le_succ (fun t => (e_succ_le pub base Q t).1)

theorem state_succ (pub : ℕ → ℤ → Bool) (start : ℤ → Bool) (t : ℕ) :
    state pub start (t + 1) = fun z =>
      xor (xor (before (state pub start t) z) (start (z + 1 - 2 * (t : ℤ)))) (pub (t + 1) z) := by
  simp only [state, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem mix_agree (s s' : ℤ → Bool) (c : ℤ) (h : ∀ z < c, s z = s' z) (w : ℤ) (hw : w + 1 < c) :
    mix s w = mix s' w := by
  simp only [mix]
  rw [h w (by omega), h (w - 1) (by omega), h (w + 1) (by omega)]

theorem before_agree (s s' : ℤ → Bool) (c : ℤ) (h : ∀ z < c, s z = s' z) :
    ∀ z < c - 3, before s z = before s' z := by
  intro z hz
  simp only [before]
  rw [mix_agree s s' c h z (by omega), mix_agree s s' c h (z + 1) (by omega),
    mix_agree s s' c h (z + 2) (by omega)]

theorem before_agree_odd (s s' : ℤ → Bool) (a : ℤ) (h : ∀ z < a + 3, s z = s' z)
    (hg : guard s a = true) : before s a = before s' a := by
  have h1 : mix s a = mix s' a := mix_agree s s' (a + 3) h a (by omega)
  have h2 : mix s (a + 1) = true := by
    simp only [mix, guard] at hg ⊢
    rw [show a + 1 - 1 = a by ring, show a + 1 + 1 = a + 2 by ring]
    revert hg
    cases s a <;> cases s (a + 1) <;> cases s (a + 2) <;> decide
  have h3 : mix s' (a + 1) = true := by
    rw [← mix_agree s s' (a + 3) h (a + 1) (by omega)]; exact h2
  simp [before, h1, h2, h3]

theorem before_front (pub : ℕ → ℤ → Bool) (base other : ℤ → Bool) (Q : ℤ) (t : ℕ)
    (hinv : ∀ z < Q - 3 * (t : ℤ) + (e pub base Q t : ℤ),
      state pub base t z = state pub other t z) :
    ∀ z < Q - 3 * ((t + 1 : ℕ) : ℤ) + (e pub base Q (t + 1) : ℤ),
      before (state pub base t) z = before (state pub other t) z := by
  intro z hz
  rw [e_succ] at hz
  by_cases hg : guard (state pub base t) (Q - 3 * (t : ℤ) + (e pub base Q t : ℤ) - 3) = false
  · simp only [hg, ↓reduceIte] at hz
    exact before_agree _ _ _ hinv z (by push_cast at hz ⊢; omega)
  · simp only [hg] at hz
    have hg' : guard (state pub base t) (Q - 3 * (t : ℤ) + (e pub base Q t : ℤ) - 3) = true := by
      simpa using hg
    rcases lt_or_eq_of_le (show z ≤ Q - 3 * (t : ℤ) + (e pub base Q t : ℤ) - 3 by
      push_cast at hz ⊢; omega) with h | h
    · exact before_agree _ _ _ hinv z h
    · rw [h]
      exact before_agree_odd _ _ _ (fun z hz => hinv z (by omega)) hg'

theorem inv (pub : ℕ → ℤ → Bool) (base other : ℤ → Bool) (Q : ℤ)
    (hag : ∀ z < Q, base z = other z) :
    ∀ t : ℕ, ∀ z < Q - 3 * (t : ℤ) + (e pub base Q t : ℤ),
      state pub base t z = state pub other t z := by
  intro t
  induction t with
  | zero =>
    intro z hz
    have h0 : e pub base Q 0 = 0 := rfl
    rw [h0] at hz
    simp only [state, List.range_zero, List.foldl_nil]
    exact hag z (by push_cast at hz; omega)
  | succ t ih =>
    intro z hz
    rw [state_succ, state_succ]
    show xor (xor (before (state pub base t) z) (base (z + 1 - 2 * (t : ℤ)))) (pub (t + 1) z) =
      xor (xor (before (state pub other t) z) (other (z + 1 - 2 * (t : ℤ)))) (pub (t + 1) z)
    have hle := e_le pub base Q (t + 1)
    rw [before_front pub base other Q t ih z hz,
      hag (z + 1 - 2 * (t : ℤ)) (by push_cast at hz; omega)]

theorem main (r D : ℕ) (i : ℤ) (hr : 5 + D ≤ r) (base other : ℤ → Bool) (pub : ℕ → ℤ → Bool)
    (hag : ∀ z < i + 3 * (r : ℤ) - (D : ℤ), base z = other z)
    (hne : before (state pub base (r - 1)) i ≠ before (state pub other (r - 1)) i) :
    ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧
      ∀ j : Fin (r - (4 + D)),
        5 + j.val ≤ times j ∧ times j ≤ 5 + D + j.val ∧ times j ≤ r ∧
          5 + D + j.val - times j ≤ 4 * (r - times j) ∧
          xor (xor (state pub base (times j - 1)
              (i + 3 * (r : ℤ) - 3 * (times j : ℤ) - ((5 + D + j.val - times j : ℕ) : ℤ)))
            (state pub base (times j - 1)
              (i + 3 * (r : ℤ) - 3 * (times j : ℤ) - ((5 + D + j.val - times j : ℕ) : ℤ) + 1)))
            (state pub base (times j - 1)
              (i + 3 * (r : ℤ) - 3 * (times j : ℤ) - ((5 + D + j.val - times j : ℕ) : ℤ) + 2))
            = false := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = i + 3 * (r : ℤ) - (D : ℤ) := ⟨_, rfl⟩
  rw [← hQ] at hag
  have hinv := inv pub base other Q hag (r - 1)
  have hfront := before_front pub base other Q (r - 1) hinv
  have hr1 : r - 1 + 1 = r := by omega
  rw [hr1] at hfront
  have heD : e pub base Q r ≤ D := by
    by_contra hc
    exact hne (hfront i (by omega))
  have ex : ∀ j : Fin (r - (4 + D)), ∃ t, 5 + j.val + e pub base Q t ≤ t :=
    fun j => ⟨r, by have := j.isLt; omega⟩
  obtain ⟨times, htimes⟩ : ∃ times : Fin (r - (4 + D)) → ℕ, ∀ j, times j = Nat.find (ex j) :=
    ⟨fun j => Nat.find (ex j), fun _ => rfl⟩
  have spec : ∀ j : Fin (r - (4 + D)), 5 + j.val + e pub base Q (times j) ≤ times j ∧
      times j ≤ r ∧ ∃ s, times j = s + 1 ∧ e pub base Q (s + 1) = e pub base Q s ∧
        s + 1 = 5 + j.val + e pub base Q (s + 1) := by
    intro j
    rw [htimes j]
    have h1 := Nat.find_spec (ex j)
    have h2 : Nat.find (ex j) ≤ r := Nat.find_min' (ex j) (by have := j.isLt; omega)
    obtain ⟨s, hs⟩ : ∃ s, Nat.find (ex j) = s + 1 := ⟨Nat.find (ex j) - 1, by omega⟩
    have h3 : ¬ (5 + j.val + e pub base Q s ≤ s) := Nat.find_min (ex j) (by omega)
    have h4 := e_succ_le pub base Q s
    refine ⟨h1, h2, s, hs, ?_, ?_⟩
    · rw [hs] at h1; omega
    · rw [hs] at h1; omega
  refine ⟨times, ?_, ?_⟩
  · intro j j' hjj'
    have hjj : j.val < j'.val := hjj'
    obtain ⟨a1, -, s, hs, -, heq⟩ := spec j
    obtain ⟨b1, -, -⟩ := spec j'
    have hle : times j ≤ times j' := by
      rw [htimes j]
      exact Nat.find_min' (ex j) (by omega)
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hs] at heq
      rw [h] at heq
      omega
  · intro j
    obtain ⟨h1, h2, s, hs, hes, heq⟩ := spec j
    have hmono : e pub base Q (times j) ≤ e pub base Q r := e_mono pub base Q h2
    have hgd : guard (state pub base s) (Q - 3 * (s : ℤ) + (e pub base Q s : ℤ) - 3) = false := by
      have := e_succ pub base Q s
      by_contra hc
      simp only [hc, ↓reduceIte] at this
      omega
    rw [hs] at h1 h2 hmono ⊢
    have ha : i + 3 * (r : ℤ) - 3 * ((s + 1 : ℕ) : ℤ) - ((5 + D + j.val - (s + 1) : ℕ) : ℤ) =
        Q - 3 * (s : ℤ) + (e pub base Q s : ℤ) - 3 := by
      omega
    refine ⟨by omega, by omega, h2, by omega, ?_⟩
    rw [ha, show s + 1 - 1 = s from rfl]
    exact hgd

end PEqualNP.Outside.L_meta_25568_aux

theorem PEqualNP.Outside.L_meta_25568 : (∀ (r D : ℕ) (i : ℤ), 5 + D ≤ r →
  ∀ (base other : ℤ → Bool) (publicBit : ℕ → ℤ → Bool),
  let mix := fun (word : ℤ → Bool) (z : ℤ) =>
    xor (xor (word z) (word (z - 1))) (word (z + 1))
  let before := fun (word : ℤ → Bool) (z : ℤ) =>
    xor (mix word z) (!(mix word (z + 1)) && mix word (z + 2))
  let state := fun (start : ℤ → Bool) (rounds : ℕ) =>
    (List.range rounds).foldl (fun (prev : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
      xor (xor (before prev z) (start (z + 1 - 2 * (tick : ℤ)))) (publicBit (tick + 1) z)) start
  let P := i + 3 * (r : ℤ)
  (∀ z < P - (D : ℤ), base z = other z) →
  before (state base (r - 1)) i ≠ before (state other (r - 1)) i →
  ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧
    ∀ j, let t := times j
         let level := 5 + D + j.val
         let g := level - t
         let a := P - 3 * (t : ℤ) - (g : ℤ)
         let z := state base (t - 1)
         5 + j.val ≤ t ∧ t ≤ level ∧ t ≤ r ∧ g ≤ 4 * (r - t) ∧
           xor (xor (z a) (z (a + 1))) (z (a + 2)) = false) := by
  intro r D i hr base other publicBit mix before state P hag hne
  exact PEqualNP.Outside.L_meta_25568_aux.main r D i hr base other publicBit hag hne
