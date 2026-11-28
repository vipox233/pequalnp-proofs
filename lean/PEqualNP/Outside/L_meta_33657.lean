import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33657

def row (c T μ : ℕ → Bool) (j : ℕ) : Prop :=
  xor (xor (μ j) (c j)) (!(xor (μ (j+1)) (c (j+1))) && xor (μ (j+2)) (c (j+2))) = T j

def Mem (h : ℕ) (c T μ : ℕ → Bool) : Prop := ∀ j < h, row c T μ j

def F (T c0 c1 c2 : Bool) (p : Bool × Bool) : Bool := xor (xor T c0) (!(xor p.1 c1) && xor p.2 c2)

lemma xor_eq_iff (a r t : Bool) : xor a r = t ↔ a = xor t r := by
  cases a <;> cases r <;> cases t <;> decide

lemma row_iff {c T μ : ℕ → Bool} {j : ℕ} :
    row c T μ j ↔ μ j = F (T j) (c j) (c (j+1)) (c (j+2)) (μ (j+1), μ (j+2)) := by
  unfold row F
  dsimp only
  generalize (!(xor (μ (j+1)) (c (j+1))) && xor (μ (j+2)) (c (j+2))) = P
  cases μ j <;> cases c j <;> cases T j <;> cases P <;> decide

lemma agree_down {h : ℕ} {c T μ ν : ℕ → Bool} (hμ : Mem h c T μ) (hν : Mem h c T ν)
    (h0 : μ h = ν h) (h1 : μ (h+1) = ν (h+1)) : ∀ q ≤ h + 1, μ q = ν q := by
  intro q hq
  induction' hm : h + 1 - q using Nat.strong_induction_on with m ih generalizing q
  rcases (show q = h + 1 ∨ q = h ∨ q < h by omega) with rfl | rfl | hlt
  · exact h1
  · exact h0
  · rw [row_iff.1 (hμ q hlt), row_iff.1 (hν q hlt), ih _ (by omega) (q+1) (by omega) rfl,
      ih _ (by omega) (q+2) (by omega) rfl]

lemma agree_low {h : ℕ} {c T μ ν : ℕ → Bool} (hμ : Mem h c T μ) (hν : Mem h c T ν)
    (h0 : μ h = ν h) (hw : xor (μ h) (c h) = true) : ∀ q ≤ h, μ q = ν q := by
  intro q hq
  induction' hm : h - q using Nat.strong_induction_on with m ih generalizing q
  rcases (show q = h ∨ q + 1 = h ∨ q + 2 ≤ h by omega) with rfl | hq1 | hq2
  · exact h0
  · have hwν : xor (ν h) (c h) = true := h0 ▸ hw
    rw [row_iff.1 (hμ q (by omega)), row_iff.1 (hν q (by omega))]
    simp only [F, hq1, hw, hwν, Bool.not_true, Bool.false_and]
  · rw [row_iff.1 (hμ q (by omega)), row_iff.1 (hν q (by omega)), ih _ (by omega) (q+1) (by omega) rfl,
      ih _ (by omega) (q+2) (by omega) rfl]

lemma mem_congr {h : ℕ} {c T μ ν : ℕ → Bool} (he : ∀ q ≤ h + 1, μ q = ν q) :
    Mem h c T μ ↔ Mem h c T ν := by
  unfold Mem row
  refine forall₂_congr fun j hj => ?_
  rw [he j (by omega), he (j+1) (by omega), he (j+2) (by omega)]

set_option maxRecDepth 100000 in
lemma F_last (T c0 c1 c2 T' c0' c1' c2' : Bool) (p : Fin 4 → Bool × Bool) (hp : Function.Injective p)
    (h : ∀ i : Fin 4, i ≠ 0 → F T c0 c1 c2 (p i) = F T' c0' c1' c2' (p i)) :
    F T c0 c1 c2 (p 0) = F T' c0' c1' c2' (p 0) := by
  revert p T c0 c1 c2 T' c0' c1' c2'
  decide

set_option maxRecDepth 100000 in
lemma pick (τ : Fin 4 → Bool × Bool) (hτ : Function.Injective τ) (a : Bool) :
    ∃ j : Fin 4, j ≠ 0 ∧ (τ j).1 = a ∧ ∃ i, i ≠ j ∧ (τ i).1 = a := by
  revert τ a
  decide

theorem core {h : ℕ} (c T ν : Fin 4 → ℕ → Bool)
    (hpat : ∀ l i, Mem h (c l) (T l) (ν i) ↔ (i = 0 ∨ l ≠ i)) : False := by
  have m0 : ∀ i, Mem h (c 0) (T 0) (ν i) := fun i => (hpat 0 i).2 (by
    by_cases hi : i = 0
    · exact Or.inl hi
    · exact Or.inr (Ne.symm hi))

  let τ : Fin 4 → Bool × Bool := fun i => (ν i h, ν i (h+1))
  have hinj : Function.Injective τ := by
    intro i i' he
    by_contra hne
    have hag := agree_down (m0 i) (m0 i') (congrArg Prod.fst he) (congrArg Prod.snd he)
    have hsame := fun l => mem_congr (c := c l) (T := T l) hag
    by_cases hi : i = 0
    · subst hi
      have := (hsame i').1 ((hpat i' 0).2 (Or.inl rfl))
      exact ((hpat i' i').1 this).elim (fun h => hne h.symm) (fun h => h rfl)
    · have := (hsame i).2 ((hpat i i').2 (Or.inr hne))
      exact ((hpat i i).1 this).elim (fun h => hi h) (fun h => h rfl)
  obtain ⟨j, hj0, hja, i, hij, hia⟩ := pick τ hinj (!(c 0 h))
  have hji : ν j h = ν i h := by simp only [τ] at hja hia; rw [hja, hia]
  have hw : xor (ν j h) (c 0 h) = true := by
    simp only [τ] at hja; rw [hja]; cases c 0 h <;> rfl
  have hag := agree_low (m0 j) (m0 i) hji hw
  have mij : Mem h (c j) (T j) (ν i) := (hpat j i).2 (Or.inr (Ne.symm hij))

  have mjj : Mem h (c j) (T j) (ν j) := by
    intro r hr
    by_cases hlast : r + 1 = h
    · subst hlast
      rw [row_iff]
      have h0 := row_iff.1 (m0 j r hr)
      let p : Fin 4 → Bool × Bool := τ ∘ Equiv.swap 0 j
      have hp : Function.Injective p := hinj.comp (Equiv.injective _)
      have key := F_last (T j r) (c j r) (c j (r+1)) (c j (r+2)) (T 0 r) (c 0 r) (c 0 (r+1)) (c 0 (r+2)) p hp
        (fun i' hi' => by
          have hs : Equiv.swap 0 j i' ≠ j := by
            intro he; apply hi'; rw [← (Equiv.swap 0 j).symm_apply_apply i', he]; simp
          have a1 := row_iff.1 (((hpat j (Equiv.swap 0 j i')).2 (Or.inr (Ne.symm hs))) r hr)
          have a2 := row_iff.1 (m0 (Equiv.swap 0 j i') r hr)
          simp only [p, Function.comp, τ]
          rw [← a1, ← a2])
      simp only [p, Function.comp, τ, Equiv.swap_apply_left] at key
      rw [key, ← h0]
    · have := mij r hr
      unfold row at this ⊢
      rw [hag r (by omega), hag (r+1) (by omega), hag (r+2) (by omega)]
      exact this
  exact ((hpat j j).1 mjj).elim (fun h => hj0 h) (fun h => h rfl)

end PEqualNP.Outside.L_meta_33657

open PEqualNP.Outside.L_meta_33657 Finset in
theorem PEqualNP.Outside.L_meta_33657 : ∀ (k b : Nat) (hk : 0 < k),
  let W := Fin k → Bool
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (p : Fin k) => xor (x p) (y p)
  let mix := fun (gap : Nat) (x : W) (p : Fin k) =>
    xor (xor (x (ix (p.val + k - gap % k))) (x p)) (x (ix (p.val + gap)))
  let step := fun (z : W) (p : Fin k) =>
    xor (z p) (!(z (ix (p.val+1))) && z (ix (p.val+2)))
  ∀ (h d start : Fin b → Nat), (∀ i, 0 < h i ∧ h i ≤ k ∧ 0 < d i) →
    ∀ (initial inj : Fin b → W → W) (desired : (i : Fin b) → W → Fin (h i) → Bool),
      let pass := fun (K : Finset W) (names : Fin b → W) =>
        ∀ x ∈ K, ∀ i (j : Fin (h i)),
          let state := add (step (mix (d i) (add (names i) (initial i x)))) (inj i x)
          state (ix (start i+j.val)) = desired i x j
      ∀ K : Finset W, K.Nonempty → (∃ names, pass K names) →
        ∀ S ⊆ K, (∀ names, pass S names ↔ pass K names) →
          (∀ x ∈ S, ∃ names, pass (S.erase x) names ∧ ¬ pass S names) →
          S.card ≤ max 3 (2*b) := by
  intro k b hk W ix add mix step h d start hh initial inj desired pass K hKne hKpass S hSK heq hirr
  classical

  let test : Fin b → W → W → Prop := fun i x n => ∀ j : Fin (h i),
      add (step (mix (d i) (add n (initial i x)))) (inj i x) (ix (start i + j.val)) = desired i x j

  let μs : Fin b → W → ℕ → Bool := fun i n q => mix (d i) n (ix (start i + q))
  let Ts : Fin b → W → ℕ → Bool := fun i x q =>
    if hq : q < h i then xor (desired i x ⟨q, hq⟩) (inj i x (ix (start i + q))) else false
  have hix : ∀ m t, ix ((ix m).val + t) = ix (m + t) := fun m t =>
    Fin.ext (by simp only [ix, Nat.mod_add_mod])
  have hmix : ∀ g (x y : W) Q, mix g (add x y) Q = xor (mix g x Q) (mix g y Q) := by
    intro g x y Q
    simp only [mix, add]
    cases x (ix (Q.val + k - g % k)) <;> cases x Q <;> cases x (ix (Q.val + g)) <;>
      cases y (ix (Q.val + k - g % k)) <;> cases y Q <;> cases y (ix (Q.val + g)) <;> rfl
  have htr : ∀ i x n, test i x n ↔ Mem (h i) (μs i (initial i x)) (Ts i x) (μs i n) := by
    intro i x n
    have hrow : ∀ j (hj : j < h i), (add (step (mix (d i) (add n (initial i x)))) (inj i x)
        (ix (start i + j)) = desired i x ⟨j, hj⟩) ↔ row (μs i (initial i x)) (Ts i x) (μs i n) j := by
      intro j hj
      simp only [row, μs, Ts, hj, ↓reduceDIte, add, step, hmix, hix, Nat.add_assoc]
      exact xor_eq_iff _ _ _
    constructor
    · intro ht j hj; exact (hrow j hj).1 (ht ⟨j, hj⟩)
    · intro hm j; exact (hrow j.val j.isLt).2 (hm j.val j.isLt)

  have hwit : ∀ x ∈ S, ∃ i n, (∀ y ∈ S, y ≠ x → test i y n) ∧ ¬test i x n := by
    intro x hx
    obtain ⟨names, hp, hnp⟩ := hirr x hx
    have : ∃ y ∈ S, ∃ i, ¬test i y (names i) := by
      by_contra hno
      push Not at hno
      exact hnp fun y hy i j => hno y hy i j
    obtain ⟨y, hy, i, hti⟩ := this
    by_cases hyx : y = x
    · subst hyx
      exact ⟨i, names i, fun z hz hzx => hp z (mem_erase.2 ⟨hzx, hz⟩) i, hti⟩
    · exact absurd (fun j => hp y (mem_erase.2 ⟨hyx, hy⟩) i j) hti
  by_contra hlt
  push Not at hlt
  rw [max_lt_iff] at hlt
  obtain ⟨h3, h2b⟩ := hlt
  obtain ⟨x0, hx0⟩ : S.Nonempty := card_pos.1 (by omega)
  obtain ⟨i00, -⟩ := hwit x0 hx0
  have : Nonempty (Fin b) := ⟨i00⟩
  choose! β e hgood hfail using hwit

  obtain ⟨i0, -, hi0⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := S) (t := univ)
    (f := β) (n := 2) (fun _ _ => mem_univ _) (by simpa [mul_comm] using h2b)
  obtain ⟨x1, x2, x3, hx1, hx2, hx3, h12, h13, h23⟩ := two_lt_card_iff.1 hi0
  rw [mem_filter] at hx1 hx2 hx3
  obtain ⟨x4, hx4S, hx4⟩ := exists_mem_notMem_of_card_lt_card (s := {x1, x2, x3}) (t := S)
    ((card_le_three).trans_lt h3)
  simp only [mem_insert, mem_singleton, not_or] at hx4

  obtain ⟨names0, hp0⟩ := hKpass
  have hs0 : ∀ y ∈ S, test i0 y (names0 i0) := fun y hy j => ((heq names0).2 hp0) y hy i0 j
  let key : Fin 4 → W := ![x4, x1, x2, x3]
  let nm : Fin 4 → W := ![names0 i0, e x1, e x2, e x3]
  have hkeyS : ∀ l, key l ∈ S := by
    intro l; fin_cases l
    exacts [hx4S, hx1.1, hx2.1, hx3.1]
  have hkey : Function.Injective key := by
    intro a a' haa
    fin_cases a <;> fin_cases a' <;> simp_all [key]
  have hpriv : ∀ x ∈ S, ∀ y ∈ S, test (β x) y (e x) ↔ y ≠ x := fun x hx y hy =>
    ⟨fun ht hyx => hfail x hx (hyx ▸ ht), hgood x hx y hy⟩
  have hn : ∀ i : Fin 4, ∀ y ∈ S, test i0 y (nm i) ↔ (i = 0 ∨ y ≠ key i) := by
    intro i y hy
    fin_cases i
    · simpa [nm] using hs0 y hy
    · show test i0 y (e x1) ↔ ((1 : Fin 4) = 0 ∨ y ≠ x1)
      rw [← hx1.2, hpriv x1 hx1.1 y hy]; simp
    · show test i0 y (e x2) ↔ ((2 : Fin 4) = 0 ∨ y ≠ x2)
      rw [← hx2.2, hpriv x2 hx2.1 y hy]; simp
    · show test i0 y (e x3) ↔ ((3 : Fin 4) = 0 ∨ y ≠ x3)
      rw [← hx3.2, hpriv x3 hx3.1 y hy]; simp
  exact core (h := h i0) (fun l => μs i0 (initial i0 (key l))) (fun l => Ts i0 (key l))
    (fun i => μs i0 (nm i)) fun l i => by
      rw [← htr, hn i (key l) (hkeyS l), hkey.ne_iff]
