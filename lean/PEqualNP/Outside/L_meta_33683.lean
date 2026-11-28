import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33683

def sol (z : ℕ → Bool) (h : ℕ) (a b : Bool) : ℕ → Bool
  | 0 => b
  | 1 => a
  | (i+2) => xor (z (h-1-i)) (!(sol z h a b (i+1)) && sol z h a b i)

theorem sol2 (z : ℕ → Bool) (h : ℕ) (a b : Bool) (i : ℕ) :
    sol z h a b (i+2) = xor (z (h-1-i)) (!(sol z h a b (i+1)) && sol z h a b i) := by
  rw [sol]

def G (z : ℕ → Bool) (h : ℕ) (V : ℕ → Bool) : Prop :=
  ∀ i < h, V (i+2) = xor (z (h-1-i)) (!(V (i+1)) && V i)

theorem G_iff (z : ℕ → Bool) (h : ℕ) (V : ℕ → Bool) :
    G z h V ↔ ∀ i < h+2, V i = sol z h (V 1) (V 0) i := by
  constructor
  · intro hG
    have key : ∀ n, n + 1 < h + 2 →
        V n = sol z h (V 1) (V 0) n ∧ V (n+1) = sol z h (V 1) (V 0) (n+1) := by
      intro n
      induction n with
      | zero => intro _; exact ⟨rfl, rfl⟩
      | succ n ih =>
        intro hn
        obtain ⟨h1, h2⟩ := ih (by omega)
        refine ⟨h2, ?_⟩
        rw [sol2, hG n (by omega), ← h1, ← h2]
    intro i hi
    rcases i with _ | i
    · rfl
    · exact (key i (by omega)).2
  · intro hs i hi
    rw [hs (i+2) (by omega), hs (i+1) (by omega), hs i (by omega), sol2]

theorem G_congr (z : ℕ → Bool) (h : ℕ) (V V' : ℕ → Bool) (hV : ∀ i < h+2, V i = V' i) :
    G z h V ↔ G z h V' := by
  unfold G
  constructor
  · intro hG i hi
    rw [← hV (i+2) (by omega), ← hV (i+1) (by omega), ← hV i (by omega)]; exact hG i hi
  · intro hG i hi
    rw [hV (i+2) (by omega), hV (i+1) (by omega), hV i (by omega)]; exact hG i hi

theorem headSpec (P : ℕ → Bool) : ∀ n a : ℕ,
    a ≤ ((List.range' a n).filter P).headD (a+n) ∧
    ((List.range' a n).filter P).headD (a+n) ≤ a + n ∧
    (∀ t, a ≤ t → t < ((List.range' a n).filter P).headD (a+n) → P t = false) ∧
    (((List.range' a n).filter P).headD (a+n) < a + n →
      P (((List.range' a n).filter P).headD (a+n)) = true) := by
  intro n
  induction n with
  | zero =>
    intro a
    simp only [List.range'_zero, List.filter_nil, List.headD_nil]
    exact ⟨by omega, by omega, fun t h1 h2 => by omega, fun h => by omega⟩
  | succ n ih =>
    intro a
    rw [List.range'_succ]
    by_cases hp : P a = true
    · rw [List.filter_cons_of_pos hp]
      simp only [List.headD_cons]
      refine ⟨le_refl _, by omega, fun t h1 h2 => by omega, fun _ => hp⟩
    · rw [List.filter_cons_of_neg hp]
      obtain ⟨i1, i2, i3, i4⟩ := ih (a+1)
      rw [show a + 1 + n = a + (n+1) by omega] at i1 i2 i3 i4
      refine ⟨by omega, i2, ?_, i4⟩
      intro t h1 h2
      by_cases e : t = a
      · subst e; simpa using hp
      · exact i3 t (by omega) h2

def stopF (z : ℕ → Bool) (h lane : ℕ) : ℕ :=
  ((List.range ((h-lane)/2)).filter (fun t => z (h-1-lane-2*t))).headD ((h-lane)/2)

theorem stopSpec (z : ℕ → Bool) (h lane : ℕ) :
    stopF z h lane ≤ (h-lane)/2 ∧
    (∀ t < stopF z h lane, z (h-1-lane-2*t) = false) ∧
    (stopF z h lane < (h-lane)/2 → z (h-1-lane-2*stopF z h lane) = true) := by
  have := headSpec (fun t => z (h-1-lane-2*t)) ((h-lane)/2) 0
  simp only [Nat.zero_add, ← List.range_eq_range'] at this
  obtain ⟨_, i2, i3, i4⟩ := this
  exact ⟨i2, fun t ht => i3 t (Nat.zero_le _) ht, i4⟩

theorem sol0 (z : ℕ → Bool) (h : ℕ) (a b : Bool) : sol z h a b 0 = b := rfl
theorem sol1 (z : ℕ → Bool) (h : ℕ) (a b : Bool) : sol z h a b 1 = a := rfl
theorem solTwo (z : ℕ → Bool) (h : ℕ) (a b : Bool) :
    sol z h a b 2 = xor (z (h-1)) (!a && b) := rfl

theorem sameFrom (z : ℕ → Bool) (h : ℕ) (a b a' b' : Bool) (j : ℕ)
    (h0 : sol z h a b j = sol z h a' b' j) (h1 : sol z h a b (j+1) = sol z h a' b' (j+1)) :
    ∀ n, sol z h a b (j+n) = sol z h a' b' (j+n) ∧
      sol z h a b (j+n+1) = sol z h a' b' (j+n+1) := by
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih =>
    obtain ⟨i1, i2⟩ := ih
    refine ⟨i2, ?_⟩
    rw [show j + (n+1) + 1 = (j+n) + 2 by omega, sol2, sol2, i1, i2]

theorem F3 (z : ℕ → Bool) (h : ℕ) (i : ℕ) (hi : 1 ≤ i) :
    sol z h true true i = sol z h true false i := by
  have := sameFrom z h true true true false 1 rfl (by rw [solTwo, solTwo]; simp) (i-1)
  rw [show 1 + (i-1) = i by omega] at this
  exact this.1

def Apat (s i : ℕ) : Bool := decide (i % 2 = 1 ∧ i / 2 ≤ s)
def Cpat (s i : ℕ) : Bool := decide (i % 2 = 0 ∧ 2 ≤ i ∧ i / 2 ≤ s + 1)

theorem F1 (z : ℕ → Bool) (h : ℕ) (i : ℕ) (hi : i < h + 2) :
    xor (sol z h true false i) (sol z h false false i) = Apat (stopF z h 0) i := by
  obtain ⟨sle, sfalse, strue⟩ := stopSpec z h 0
  set s := stopF z h 0 with hs
  have inv : ∀ t, t ≤ s → sol z h true false (2*t) = false ∧ sol z h false false (2*t) = false ∧
      sol z h true false (2*t+1) = !(sol z h false false (2*t+1)) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rfl, rfl, rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have zf : z (h-1-2*t) = false := by
        have := sfalse t (by omega); simpa using this
      have e2 : ∀ a : Bool, sol z h a false (2*(t+1)) = false := by
        intro a
        rw [show 2*(t+1) = 2*t+2 by ring, sol2, zf]
        cases a
        · rw [i2]; simp
        · rw [i1]; simp
      refine ⟨e2 true, e2 false, ?_⟩
      rw [show 2*(t+1)+1 = (2*t+1)+2 by ring, sol2 z h true false (2*t+1),
        sol2 z h false false (2*t+1), show 2*t+1+1 = 2*(t+1) by ring, e2, e2, i3]
      simp
  obtain ⟨j0, j1, j2⟩ := inv s (le_refl _)
  have m2 : sol z h true false (2*s+2) = sol z h false false (2*s+2) := by
    rw [sol2, sol2, j0, j1]; simp
  rcases Nat.lt_or_ge i (2*s+2) with hlt | hge
  · obtain ⟨t, ht | ht⟩ : ∃ t, i = 2*t ∨ i = 2*t+1 := ⟨i/2, by omega⟩
    · subst ht
      obtain ⟨k1, k2, _⟩ := inv t (by omega)
      rw [k1, k2, Apat, decide_eq_false (by omega)]; rfl
    · subst ht
      obtain ⟨_, _, k3⟩ := inv t (by omega)
      rw [k3, Apat, decide_eq_true (by omega)]; simp
  · rw [Apat, decide_eq_false (by omega)]
    rcases Nat.eq_or_lt_of_le hge with e | hgt
    · rw [← e, m2]; simp
    · have hsm : s < h/2 := by omega
      have zt : z (h-1-2*s) = true := by
        have := strue hsm; simpa using this
      have m3 : sol z h true false (2*s+2+1) = sol z h false false (2*s+2+1) := by
        rw [sol2, sol2, sol2, sol2, j0, j1, zt]; simp
      have := (sameFrom z h true false false false (2*s+2) m2 m3 (i - (2*s+2))).1
      rw [show 2*s+2 + (i - (2*s+2)) = i by omega] at this
      rw [this]; simp

theorem F2 (z : ℕ → Bool) (h : ℕ) (i : ℕ) (hi : i < h + 2) :
    xor (sol z h false true i) (sol z h false false i) =
      xor (decide (i = 0)) (Cpat (stopF z h 1) i) := by
  obtain ⟨sle, sfalse, strue⟩ := stopSpec z h 1
  set s := stopF z h 1 with hs
  have inv : ∀ t, t ≤ s → sol z h false true (2*t+1) = false ∧
      sol z h false false (2*t+1) = false ∧
      sol z h false true (2*t+2) = !(sol z h false false (2*t+2)) := by
    intro t
    induction t with
    | zero => intro _; refine ⟨rfl, rfl, ?_⟩; rw [solTwo, solTwo]; simp
    | succ t ih =>
      intro ht
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have zf : z (h-1-(2*t+1)) = false := by
        have := sfalse t (by omega)
        rw [show h - 1 - 1 - 2*t = h-1-(2*t+1) by omega] at this; exact this
      have e2 : ∀ b : Bool, sol z h false b (2*(t+1)+1) = false := by
        intro b
        rw [show 2*(t+1)+1 = (2*t+1)+2 by ring, sol2, zf]
        cases b
        · rw [i2]; simp
        · rw [i1]; simp
      refine ⟨e2 true, e2 false, ?_⟩
      rw [show 2*(t+1)+2 = (2*t+2)+2 by ring, sol2 z h false true (2*t+2),
        sol2 z h false false (2*t+2), show 2*t+2+1 = 2*(t+1)+1 by ring, e2, e2, i3]
      simp
  obtain ⟨j0, j1, j2⟩ := inv s (le_refl _)
  have m3 : sol z h false true (2*s+3) = sol z h false false (2*s+3) := by
    rw [show 2*s+3 = (2*s+1)+2 by ring, sol2 z h false true (2*s+1),
      sol2 z h false false (2*s+1), j0, j1]; simp
  rcases Nat.lt_or_ge i (2*s+3) with hlt | hge
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [sol0, sol0]; simp [Cpat]
    obtain ⟨t, ht | ht⟩ : ∃ t, i = 2*t+1 ∨ i = 2*t+2 := ⟨(i-1)/2, by omega⟩
    · subst ht
      obtain ⟨k1, k2, _⟩ := inv t (by omega)
      rw [k1, k2, Cpat, decide_eq_false (show ¬ (2*t+1 = 0) by omega),
        decide_eq_false (show ¬ ((2*t+1) % 2 = 0 ∧ 2 ≤ 2*t+1 ∧ (2*t+1)/2 ≤ s+1) by omega)]
    · subst ht
      obtain ⟨_, _, k3⟩ := inv t (by omega)
      rw [k3, Cpat, decide_eq_false (show ¬ (2*t+2 = 0) by omega),
        decide_eq_true (show ((2*t+2) % 2 = 0 ∧ 2 ≤ 2*t+2 ∧ (2*t+2)/2 ≤ s+1) by omega)]; simp
  · rw [Cpat, decide_eq_false (show ¬ (i = 0) by omega),
      decide_eq_false (show ¬ (i % 2 = 0 ∧ 2 ≤ i ∧ i/2 ≤ s+1) by omega)]
    rcases Nat.eq_or_lt_of_le hge with e | hgt
    · rw [← e, m3]; simp
    · have hsm : s < (h-1)/2 := by omega
      have zt : z (h-1-(2*s+1)) = true := by
        have := strue hsm
        rw [show h - 1 - 1 - 2*s = h-1-(2*s+1) by omega] at this; exact this
      have m4 : sol z h false true (2*s+3+1) = sol z h false false (2*s+3+1) := by
        rw [show 2*s+3+1 = (2*s+2)+2 by ring, sol2 z h false true (2*s+2),
          sol2 z h false false (2*s+2), show 2*s+2+1 = (2*s+1)+2 by ring,
          sol2 z h false true (2*s+1), sol2 z h false false (2*s+1), j0, j1, zt]; simp
      have := (sameFrom z h false true false false (2*s+3) m3 m4 (i - (2*s+3))).1
      rw [show 2*s+3 + (i - (2*s+3)) = i by omega] at this
      rw [this]; simp

def Dpat (a b : Bool) (s0 s1 i : ℕ) : Bool :=
  xor (xor (a && Apat s0 i) (b && decide (i = 0))) (b && !a && Cpat s1 i)

theorem Dform (z : ℕ → Bool) (h : ℕ) (a b : Bool) (i : ℕ) (hi : i < h + 2) :
    xor (sol z h a b i) (sol z h false false i) = Dpat a b (stopF z h 0) (stopF z h 1) i := by
  cases a <;> cases b
  · simp [Dpat]
  · rw [F2 z h i hi]; simp [Dpat]
  · rw [F1 z h i hi]; simp [Dpat]
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [sol0, sol0]; simp [Dpat, Apat]
    · rw [F3 z h i hpos, F1 z h i hi]; simp [Dpat, show i ≠ 0 by omega]

theorem Apat_inj (h s s' : ℕ) (h1 : s ≤ h/2) (h2 : s' ≤ h/2)
    (hA : ∀ i < h+2, Apat s i = Apat s' i) : s = s' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hA (2*s'+1) (by omega)
    rw [Apat, Apat, decide_eq_false (by omega), decide_eq_true (by omega)] at this
    exact Bool.false_ne_true this
  · have := hA (2*s+1) (by omega)
    rw [Apat, Apat, decide_eq_true (by omega), decide_eq_false (by omega)] at this
    exact Bool.false_ne_true this.symm

theorem Cpat_inj (h s s' : ℕ) (h1 : s ≤ (h-1)/2) (h2 : s' ≤ (h-1)/2) (hh : 0 < h)
    (hC : ∀ i < h+2, Cpat s i = Cpat s' i) : s = s' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hC (2*s'+2) (by omega)
    rw [Cpat, Cpat, decide_eq_false (by omega), decide_eq_true (by omega)] at this
    exact Bool.false_ne_true this
  · have := hC (2*s+2) (by omega)
    rw [Cpat, Cpat, decide_eq_true (by omega), decide_eq_false (by omega)] at this
    exact Bool.false_ne_true this.symm

theorem bxc : ∀ x c c' : Bool, xor x c = xor x c' → c = c' := by decide

theorem Deq_iff (h : ℕ) (hh : 0 < h) (z0 z1 : ℕ → Bool) :
    (∀ a b : Bool, ∀ i < h+2, xor (sol z0 h a b i) (sol z0 h false false i) =
      xor (sol z1 h a b i) (sol z1 h false false i)) ↔
    (stopF z0 h 0 = stopF z1 h 0 ∧ stopF z0 h 1 = stopF z1 h 1) := by
  constructor
  · intro hD
    constructor
    · apply Apat_inj h _ _ (by have := (stopSpec z0 h 0).1; simpa using this)
        (by have := (stopSpec z1 h 0).1; simpa using this)
      intro i hi
      have := hD true false i hi
      rw [Dform z0 h _ _ i hi, Dform z1 h _ _ i hi] at this
      simpa [Dpat] using this
    · apply Cpat_inj h _ _ (stopSpec z0 h 1).1 (stopSpec z1 h 1).1 hh
      intro i hi
      have := hD false true i hi
      rw [Dform z0 h _ _ i hi, Dform z1 h _ _ i hi] at this
      simp only [Dpat, Bool.false_and, Bool.true_and, Bool.not_false, Bool.false_xor] at this
      exact bxc _ _ _ this
  · rintro ⟨e0, e1⟩ a b i hi
    rw [Dform z0 h _ _ i hi, Dform z1 h _ _ i hi, e0, e1]

theorem keyE : ∀ x y e0 e1 e2 : Bool,
    (∀ a b : Bool, xor (xor x (!a && b)) e2 = xor y (!(xor a e1) && xor b e0)) →
      e0 = false ∧ e1 = false := by decide
theorem bxe : ∀ X e Y : Bool, xor X e = Y → e = xor X Y := by decide
theorem b4 : ∀ A A0 B B0 : Bool, xor A (xor A0 B0) = B → xor A A0 = xor B B0 := by decide
theorem b6 : ∀ v e A A0 B B0 : Bool, e = xor A0 B0 → xor A A0 = xor B B0 →
    (v = A ↔ xor v e = B) := by decide

theorem window (h : ℕ) (hh : 0 < h) (z0 z1 e : ℕ → Bool) :
    (∀ V : ℕ → Bool, G z0 h V ↔ G z1 h (fun i => xor (V i) (e i))) ↔
    ((stopF z0 h 0 = stopF z1 h 0 ∧ stopF z0 h 1 = stopF z1 h 1) ∧
      ∀ i < h+2, e i = xor (sol z0 h false false i) (sol z1 h false false i)) := by
  constructor
  · intro hP
    have Eq : ∀ a b : Bool, ∀ i < h+2,
        xor (sol z0 h a b i) (e i) = sol z1 h (xor a (e 1)) (xor b (e 0)) i := by
      intro a b
      have hG0 : G z0 h (sol z0 h a b) := (G_iff _ _ _).2 (fun i _ => rfl)
      exact (G_iff _ _ _).1 ((hP _).1 hG0)
    have he : e 0 = false ∧ e 1 = false := by
      apply keyE (z0 (h-1)) (z1 (h-1)) (e 0) (e 1) (e 2)
      intro a b
      have := Eq a b 2 (by omega)
      rw [solTwo, solTwo] at this
      exact this
    have he' : ∀ i < h+2, e i = xor (sol z0 h false false i) (sol z1 h false false i) := by
      intro i hi
      have := Eq false false i hi
      rw [he.1, he.2] at this
      exact bxe _ _ _ this
    refine ⟨(Deq_iff h hh z0 z1).1 ?_, he'⟩
    intro a b i hi
    have := Eq a b i hi
    rw [he.1, he.2, Bool.xor_false, Bool.xor_false, he' i hi] at this
    exact b4 _ _ _ _ this
  · rintro ⟨hs, he⟩ V
    have hD := (Deq_iff h hh z0 z1).2 hs
    have e0 : e 0 = false := by rw [he 0 (by omega)]; rfl
    have e1 : e 1 = false := by rw [he 1 (by omega)]; rfl
    rw [G_iff, G_iff]
    simp only [e0, e1, Bool.xor_false]
    apply forall_congr'; intro i; apply imp_congr_right; intro hi
    exact b6 _ _ _ _ _ _ (he i hi) (hD _ _ i hi)

-- The halving and counting pattern below follows the count lemma of the merged
-- PEqualNP.Outside.L_meta_25883 (credit to its author), rewritten for Fin k to Bool words.
theorem halve {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α) (hS : ∀ x ∈ S, f x ∈ S)
    (hinv : ∀ x, f (f x) = x) (p : α → Bool) (hp : ∀ x ∈ S, p (f x) = !p x) (b : Bool) :
    2 * (S.filter (fun x => p x = b)).card = S.card := by
  have e : (S.filter (fun x => p x = b)).card = (S.filter (fun x => ¬ p x = b)).card := by
    apply Finset.card_bij' (fun x _ => f x) (fun x _ => f x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hS x hx.1, ?_⟩
      rw [hp x hx.1, hx.2]; cases b <;> simp
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hS x hx.1, ?_⟩
      have h2 := hx.2
      rw [hp x hx.1]; revert h2; cases b <;> cases p x <;> simp
    · intro x _; exact hinv x
    · intro x _; exact hinv x
  have := Finset.card_filter_add_card_filter_not (s := S) (fun x => p x = b)
  omega

theorem count {α : Type*} [Fintype α] [DecidableEq α] (N : ℕ) (g : α → ℕ → Bool)
    (τ : ℕ → Bool) (f : ℕ → α → α) (hinv : ∀ t x, f t (f t x) = x)
    (hflip : ∀ t < N, ∀ x, g (f t x) t = !g x t)
    (hkeep : ∀ t < N, ∀ t' < t, ∀ x, g (f t x) t' = g x t') :
    ∀ n ≤ N, 2^n * (Finset.univ.filter (fun x => ∀ t < n, g x t = τ t)).card =
      Fintype.card α := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have e : Finset.univ.filter (fun x => ∀ t < n+1, g x t = τ t) =
        (Finset.univ.filter (fun x => ∀ t < n, g x t = τ t)).filter
          (fun x => g x n = τ n) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx; exact ⟨fun t ht => hx t (by omega), hx n (by omega)⟩
      · rintro ⟨h1, h2⟩ t ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
        · exact h1 t h
        · rw [h]; exact h2
    have hS : ∀ x ∈ Finset.univ.filter (fun x => ∀ t < n, g x t = τ t),
        f n x ∈ Finset.univ.filter (fun x => ∀ t < n, g x t = τ t) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro t ht; rw [hkeep n (by omega) t ht]; exact hx t ht
    have := halve _ (f n) hS (hinv n) (fun x => g x n)
      (fun x _ => hflip n (by omega) x) (τ n)
    rw [e, ← ih (by omega), ← this]
    ring

section
open Fin.CommRing
variable {k : ℕ} [NeZero k]

theorem ixN (n : ℕ) (h : n % k < k) : (⟨n % k, h⟩ : Fin k) = (n : Fin k) := by
  ext; simp [Fin.val_natCast]

theorem castA (q : Fin k) (s : ℕ) : ((q.val + s : ℕ) : Fin k) = q + (s : Fin k) := by
  push_cast; simp

theorem castS (q : Fin k) (s : ℕ) : ((q.val + k - s % k : ℕ) : Fin k) = q - (s : Fin k) := by
  have h1 : s % k ≤ q.val + k := by have := Nat.mod_lt s (NeZero.pos k); omega
  rw [Nat.cast_sub h1]
  have h2 : ((s % k : ℕ) : Fin k) = (s : Fin k) := by
    ext; simp [Fin.val_natCast]
  push_cast
  rw [h2]
  simp

theorem natEq (a b : ℕ) (ha : a < k) (hb : b < k) : ((a : Fin k) = (b : Fin k)) ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

theorem eqShift (X Y U V : Fin k) (h : X - Y = U - V) : (X = Y) ↔ (U = V) := by
  rw [← sub_eq_zero, h, sub_eq_zero]

def Mx (g : ℕ) (x : Fin k → Bool) (p : Fin k) : Bool :=
  xor (xor (x (p - (g : Fin k))) (x p)) (x (p + (g : Fin k)))
def St (z : Fin k → Bool) (p : Fin k) : Bool :=
  xor (z p) (!(z (p + ((1 : ℕ) : Fin k))) && z (p + ((2 : ℕ) : Fin k)))
def Ad (x y : Fin k → Bool) (p : Fin k) : Bool := xor (x p) (y p)
def dl (f : Fin k) (q : Fin k) : Bool := decide (q = f)

theorem bx6 : ∀ a b c d e f : Bool,
    xor (xor (xor a d) (xor b e)) (xor c f) = xor (xor (xor a b) c) (xor (xor d e) f) := by
  decide

theorem Mx_ad (g : ℕ) (Y N : Fin k → Bool) : Mx g (Ad Y N) = Ad (Mx g Y) (Mx g N) := by
  funext q; exact bx6 _ _ _ _ _ _

def Pp (h start i : ℕ) : Fin k := (start : Fin k) + ((h+1-i : ℕ) : Fin k)
def gg (d h start : ℕ) (x : Fin k → Bool) (i : ℕ) : Bool := Mx d x (Pp h start i)

theorem bxz : ∀ a c z : Bool, xor a c = z → a = xor z c := by decide
theorem bxz' : ∀ a c z : Bool, a = xor z c → xor a c = z := by decide

theorem linkG (h start : ℕ) (z : ℕ → Bool) (Y : Fin k → Bool) :
    (∀ j < h, St Y ((start + j : ℕ) : Fin k) = z j) ↔
      G z h (fun i => Y (Pp h start i)) := by
  have pos : ∀ j : ℕ, (start : Fin k) + ((j : ℕ) : Fin k) = ((start + j : ℕ) : Fin k) ∧
      (start : Fin k) + ((j+1 : ℕ) : Fin k) = ((start + j : ℕ) : Fin k) + ((1:ℕ) : Fin k) ∧
      (start : Fin k) + ((j+2 : ℕ) : Fin k) = ((start + j : ℕ) : Fin k) + ((2:ℕ) : Fin k) := by
    intro j; refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> ring
  unfold G Pp
  constructor
  · intro H i hi
    obtain ⟨j, e2, e1, e0, ej⟩ : ∃ j, h+1-(i+2) = j ∧ h+1-(i+1) = j+1 ∧ h+1-i = j+2 ∧
        h-1-i = j := ⟨h-1-i, by omega, by omega, by omega, rfl⟩
    have Hj := H j (by omega)
    simp only [St] at Hj
    beta_reduce
    rw [e2, e1, e0, ej, (pos j).1, (pos j).2.1, (pos j).2.2]
    exact bxz _ _ _ Hj
  · intro H j hj
    obtain ⟨i, e2, e1, e0, ej, hi⟩ : ∃ i, h+1-(i+2) = j ∧ h+1-(i+1) = j+1 ∧ h+1-i = j+2 ∧
        h-1-i = j ∧ i < h := ⟨h-1-j, by omega, by omega, by omega, by omega, by omega⟩
    have Hi := H i hi
    beta_reduce at Hi
    rw [e2, e1, e0, ej, (pos j).1, (pos j).2.1, (pos j).2.2] at Hi
    simp only [St]
    exact bxz' _ _ _ Hi

theorem hdl (h d start t t' : ℕ) (hd : 0 < d) (hk : h+2+2*d ≤ k) (ht : t' ≤ t)
    (htk : t < h+2) :
    Mx d (dl (Pp h start t - (d : Fin k))) (Pp h start t') = decide (t' = t) := by
  simp only [Mx, dl]
  have i1 : (Pp h start t' - (d : Fin k) = Pp h start t - (d : Fin k)) ↔ t' = t := by
    rw [eqShift _ _ ((h+1-t' : ℕ) : Fin k) ((h+1-t : ℕ) : Fin k) (by simp only [Pp]; ring),
      natEq _ _ (by omega) (by omega)]
    omega
  have i2 : ¬ (Pp h start t' = Pp h start t - (d : Fin k)) := by
    rw [eqShift _ _ ((h+1-t' + d : ℕ) : Fin k) ((h+1-t : ℕ) : Fin k)
      (by rw [Nat.cast_add]; simp only [Pp]; ring), natEq _ _ (by omega) (by omega)]
    omega
  have i3 : ¬ (Pp h start t' + (d : Fin k) = Pp h start t - (d : Fin k)) := by
    rw [eqShift _ _ ((h+1-t' + d + d : ℕ) : Fin k) ((h+1-t : ℕ) : Fin k)
      (by rw [Nat.cast_add, Nat.cast_add]; simp only [Pp]; ring), natEq _ _ (by omega) (by omega)]
    omega
  rw [decide_eq_false i2, decide_eq_false i3, Bool.xor_false, Bool.xor_false]
  exact decide_eq_decide.mpr i1

theorem gflip (d h start t t' : ℕ) (x : Fin k → Bool) :
    gg d h start (Ad x (dl (Pp h start t - (d : Fin k)))) t' =
      xor (gg d h start x t') (Mx d (dl (Pp h start t - (d : Fin k))) (Pp h start t')) := by
  simp only [gg]; rw [Mx_ad]; rfl

theorem hcount (h d start : ℕ) (hd : 0 < d) (hk : h+2+2*d ≤ k) (τ : ℕ → Bool) :
    (Finset.univ.filter (fun x : Fin k → Bool => ∀ t < h+2, gg d h start x t = τ t)).card =
      2^(k-(h+2)) := by
  have := count (h+2) (gg d h start) τ (fun t x => Ad x (dl (Pp h start t - (d : Fin k))))
    (by intro t x; funext p; simp [Ad])
    (by intro t ht x; rw [gflip, hdl h d start t t hd hk le_rfl ht]; simp)
    (by intro t ht t' ht' x; rw [gflip, hdl h d start t t' hd hk (by omega) ht, decide_eq_false (by omega),
      Bool.xor_false])
    (h+2) le_rfl
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  have e : 2^k = 2^(h+2) * 2^(k-(h+2)) := by rw [← pow_add]; congr 1; omega
  rw [e] at this
  exact Nat.eq_of_mul_eq_mul_left (by positivity) this

theorem bA : ∀ v o0 o1 u dd : Bool, u = xor v o0 →
    xor v (xor (xor o0 dd) o1) = xor (xor u dd) o1 := by decide
theorem bB : ∀ u o0 o1 dd : Bool,
    xor (xor u o0) (xor (xor o0 dd) o1) = xor (xor u dd) o1 := by decide
theorem bC : ∀ a x b s : Bool, (xor (xor a x) b = s) ↔ (x = xor (xor a b) s) := by decide

theorem mainCount (h d start : ℕ) (hd : 0 < d) (hh : 0 < h) (hk : h+2+2*d ≤ k)
    (o0 o1 : Fin k → Bool) (z0 z1 : ℕ → Bool) :
    (Finset.univ.filter (fun δ : Fin k → Bool => ∀ u : Fin k → Bool,
      (∀ j < h, St (Mx d (Ad u o0)) ((start + j : ℕ) : Fin k) = z0 j) ↔
      (∀ j < h, St (Mx d (Ad (Ad u δ) o1)) ((start + j : ℕ) : Fin k) = z1 j))).card =
    if (stopF z0 h 0 = stopF z1 h 0 ∧ stopF z0 h 1 = stopF z1 h 1) then 2^(k-(h+2)) else 0 := by
  have hA : ∀ (o : Fin k → Bool) z u, (∀ j < h, St (Mx d (Ad u o)) ((start + j : ℕ) : Fin k) = z j)
      ↔ G z h (fun i => xor (gg d h start u i) (gg d h start o i)) := by
    intro o z u; rw [linkG, Mx_ad]; rfl
  have hsurj : ∀ w : ℕ → Bool, ∃ u : Fin k → Bool, ∀ i < h+2, gg d h start u i = w i := by
    intro w
    have := hcount h d start hd hk w
    have hp : 0 < (Finset.univ.filter
        (fun x : Fin k → Bool => ∀ t < h+2, gg d h start x t = w t)).card := by
      rw [this]; positivity
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
    exact ⟨u, (Finset.mem_filter.mp hu).2⟩
  have gad : ∀ u δ : Fin k → Bool, ∀ i, gg d h start (Ad u δ) i =
      xor (gg d h start u i) (gg d h start δ i) := by
    intro u δ i; simp only [gg]; rw [Mx_ad]; rfl
  have hkey : ∀ δ : Fin k → Bool, (∀ u : Fin k → Bool,
      (∀ j < h, St (Mx d (Ad u o0)) ((start + j : ℕ) : Fin k) = z0 j) ↔
      (∀ j < h, St (Mx d (Ad (Ad u δ) o1)) ((start + j : ℕ) : Fin k) = z1 j)) ↔
      ((stopF z0 h 0 = stopF z1 h 0 ∧ stopF z0 h 1 = stopF z1 h 1) ∧
        ∀ i < h+2, gg d h start δ i = xor (xor (gg d h start o0 i) (gg d h start o1 i))
          (xor (sol z0 h false false i) (sol z1 h false false i))) := by
    intro δ
    have s1 : (∀ u : Fin k → Bool,
        (∀ j < h, St (Mx d (Ad u o0)) ((start + j : ℕ) : Fin k) = z0 j) ↔
        (∀ j < h, St (Mx d (Ad (Ad u δ) o1)) ((start + j : ℕ) : Fin k) = z1 j)) ↔
        ∀ V : ℕ → Bool, G z0 h V ↔ G z1 h (fun i => xor (V i)
          (xor (xor (gg d h start o0 i) (gg d h start δ i)) (gg d h start o1 i))) := by
      constructor
      · intro H V
        obtain ⟨u, hu⟩ := hsurj (fun i => xor (V i) (gg d h start o0 i))
        have := H u
        rw [hA, hA] at this
        rw [G_congr z0 h V (fun i => xor (gg d h start u i) (gg d h start o0 i))
          (by intro i hi; rw [hu i hi]; revert hi; cases V i <;> cases gg d h start o0 i <;> simp),
          this]
        apply G_congr
        intro i hi
        rw [gad]
        exact (bA _ _ _ _ _ (hu i hi)).symm
      · intro H u
        rw [hA, hA, H]
        apply G_congr
        intro i hi
        rw [gad]
        exact bB _ _ _ _
    rw [s1, window h hh]
    apply and_congr_right; intro _
    apply forall_congr'; intro i; apply imp_congr_right; intro _
    exact bC _ _ _ _
  split_ifs with hc
  · rw [← hcount h d start hd hk (fun i => xor (xor (gg d h start o0 i) (gg d h start o1 i))
      (xor (sol z0 h false false i) (sol z1 h false false i)))]
    congr 1
    apply Finset.filter_congr
    intro δ _
    rw [hkey δ]
    exact and_iff_right hc
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro δ _ hδ
    exact hc ((hkey δ).1 hδ).1


-- New for this step: translation classes of the two accepted sets and the per-lane count.

theorem bxzIff : ∀ a c z : Bool, (xor a c = z) ↔ (a = xor z c) := by decide

theorem classIff (h d start : ℕ) (hd : 0 < d) (hh : 0 < h) (hk : h+2+2*d ≤ k)
    (o0 o1 : Fin k → Bool) (z0 z1 : ℕ → Bool) :
    (∃ δ : Fin k → Bool, ∀ u : Fin k → Bool,
      (∀ j < h, St (Mx d (Ad u o0)) ((start + j : ℕ) : Fin k) = z0 j) ↔
      (∀ j < h, St (Mx d (Ad (Ad u δ) o1)) ((start + j : ℕ) : Fin k) = z1 j)) ↔
    (stopF z0 h 0 = stopF z1 h 0 ∧ stopF z0 h 1 = stopF z1 h 1) := by
  have H := mainCount h d start hd hh hk o0 o1 z0 z1
  constructor
  · rintro ⟨δ, hδ⟩
    by_contra hc
    rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at H
    exact H (Finset.mem_univ δ) hδ
  · intro hc
    rw [if_pos hc] at H
    have hp : 0 < (Finset.univ.filter (fun δ : Fin k → Bool => ∀ u : Fin k → Bool,
      (∀ j < h, St (Mx d (Ad u o0)) ((start + j : ℕ) : Fin k) = z0 j) ↔
      (∀ j < h, St (Mx d (Ad (Ad u δ) o1)) ((start + j : ℕ) : Fin k) = z1 j))).card := by
      rw [H]; positivity
    obtain ⟨δ, hδ⟩ := Finset.card_pos.mp hp
    exact ⟨δ, (Finset.mem_filter.mp hδ).2⟩

theorem nonemp (h d start : ℕ) (hd : 0 < d) (hk : h+2+2*d ≤ k) (o : Fin k → Bool)
    (z : ℕ → Bool) :
    ∃ u : Fin k → Bool, ∀ j < h, St (Mx d (Ad u o)) ((start + j : ℕ) : Fin k) = z j := by
  have hsurj : ∀ w : ℕ → Bool, ∃ u : Fin k → Bool, ∀ i < h+2, gg d h start u i = w i := by
    intro w
    have := hcount h d start hd hk w
    have hp : 0 < (Finset.univ.filter
        (fun x : Fin k → Bool => ∀ t < h+2, gg d h start x t = w t)).card := by
      rw [this]; positivity
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
    exact ⟨u, (Finset.mem_filter.mp hu).2⟩
  obtain ⟨u, hu⟩ := hsurj (fun i => xor (sol z h false false i) (gg d h start o i))
  refine ⟨u, ?_⟩
  rw [linkG, Mx_ad]
  rw [G_congr z h _ (sol z h false false) ?_]
  · exact (G_iff z h _).2 (fun i _ => rfl)
  · intro i hi
    show xor (gg d h start u i) (gg d h start o i) = sol z h false false i
    rw [hu i hi]
    cases sol z h false false i <;> cases gg d h start o i <;> rfl

theorem Ad_assoc (u s e : Fin k → Bool) : Ad (Ad u s) e = Ad u (Ad s e) := by
  funext q; simp only [Ad, Bool.xor_assoc]

theorem Ad_self (u e : Fin k → Bool) : Ad (Ad u e) e = u := by
  funext q; simp only [Ad, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem Ad_zero (u : Fin k → Bool) : Ad u (fun _ => false) = u := by
  funext q; simp only [Ad, Bool.xor_false]

theorem orbSub (PA PB : (Fin k → Bool) → (Fin k → Bool) → Prop)
    [∀ a, DecidablePred (PA a)] [∀ a, DecidablePred (PB a)] (x y dA dB : Fin k → Bool)
    (hA : ∀ u, PA x u ↔ PA y (Ad u dA)) (hB : ∀ u, PB x u ↔ PB y (Ad u dB)) :
    (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).image (fun s =>
      (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).filter (fun nm =>
        PA x (Ad nm.1 s.1) ∧ PB x (Ad nm.2 s.2))) ⊆
    (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).image (fun s =>
      (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).filter (fun nm =>
        PA y (Ad nm.1 s.1) ∧ PB y (Ad nm.2 s.2))) := by
  intro S hS
  rw [Finset.mem_image] at hS ⊢
  obtain ⟨s, _, rfl⟩ := hS
  refine ⟨(Ad s.1 dA, Ad s.2 dB), Finset.mem_univ _, ?_⟩
  ext nm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hA, hB, Ad_assoc, Ad_assoc]

theorem orbEq (PA PB : (Fin k → Bool) → (Fin k → Bool) → Prop)
    [∀ a, DecidablePred (PA a)] [∀ a, DecidablePred (PB a)] (x y : Fin k → Bool)
    (nA : ∀ a, ∃ u, PA a u) (nB : ∀ a, ∃ u, PB a u) :
    (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).image (fun s =>
      (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).filter (fun nm =>
        PA x (Ad nm.1 s.1) ∧ PB x (Ad nm.2 s.2))) =
    (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).image (fun s =>
      (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).filter (fun nm =>
        PA y (Ad nm.1 s.1) ∧ PB y (Ad nm.2 s.2))) ↔
    ((∃ dA, ∀ u, PA x u ↔ PA y (Ad u dA)) ∧ (∃ dB, ∀ u, PB x u ↔ PB y (Ad u dB))) := by
  constructor
  · intro E
    have hm : (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).filter (fun nm =>
        PA x (Ad nm.1 (fun _ => false)) ∧ PB x (Ad nm.2 (fun _ => false))) ∈
        (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).image (fun s =>
        (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool))).filter (fun nm =>
          PA x (Ad nm.1 s.1) ∧ PB x (Ad nm.2 s.2))) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ ((fun _ => false), (fun _ => false)))
    rw [E, Finset.mem_image] at hm
    obtain ⟨s, _, hs⟩ := hm
    have key : ∀ a b, (PA y (Ad a s.1) ∧ PB y (Ad b s.2)) ↔ (PA x a ∧ PB x b) := by
      intro a b
      have := congrArg (fun T => (a, b) ∈ T) hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ad_zero, eq_iff_iff] at this
      exact this
    obtain ⟨a0, ha0⟩ := nA x
    obtain ⟨b0, hb0⟩ := nB x
    have y0 := (key a0 b0).2 ⟨ha0, hb0⟩
    refine ⟨⟨s.1, fun u => ⟨fun hu => ((key u b0).2 ⟨hu, hb0⟩).1,
      fun hu => ((key u b0).1 ⟨hu, y0.2⟩).1⟩⟩,
      ⟨s.2, fun u => ⟨fun hu => ((key a0 u).2 ⟨ha0, hu⟩).2,
      fun hu => ((key a0 u).1 ⟨y0.1, hu⟩).2⟩⟩⟩
  · rintro ⟨⟨dA, hA⟩, ⟨dB, hB⟩⟩
    apply Finset.Subset.antisymm (orbSub PA PB x y dA dB hA hB)
    apply orbSub PA PB y x dA dB
    · intro u; rw [hA, Ad_self]
    · intro u; rw [hB, Ad_self]

theorem cardImg {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ] (f : α → β)
    (g : α → γ) (H : ∀ x y, f x = f y ↔ g x = g y) :
    (Finset.univ.image f).card = (Finset.univ.image g).card := by
  apply Finset.card_bij (fun b hb => g (Classical.choose (Finset.mem_image.mp hb)))
  · intro b hb; exact Finset.mem_image_of_mem g (Finset.mem_univ _)
  · intro b1 hb1 b2 hb2 he
    have e1 := (Classical.choose_spec (Finset.mem_image.mp hb1)).2
    have e2 := (Classical.choose_spec (Finset.mem_image.mp hb2)).2
    rw [← e1, ← e2]; exact (H _ _).2 he
  · intro c hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨f a, Finset.mem_image_of_mem f (Finset.mem_univ _), ?_⟩
    have e := (Classical.choose_spec
      (Finset.mem_image.mp (Finset.mem_image_of_mem f (Finset.mem_univ a)))).2
    exact (H _ _).1 e

def pos' (h start n : ℕ) : Fin k := ((start + h + 3 : ℕ) : Fin k) - ((n + 4 : ℕ) : Fin k)

theorem pos'_inj (h start a b : ℕ) (hk : h + 7 ≤ k) (ha : a < h + 3) (hb : b < h + 3)
    (e : (pos' h start a : Fin k) = pos' h start b) : a = b := by
  unfold pos' at e
  rw [sub_right_inj, natEq _ _ (by omega) (by omega)] at e
  omega

theorem rowPos (h start l t : ℕ) (ht : l + 2*t + 1 ≤ h) :
    ((start + (h-1-l-2*t) : ℕ) : Fin k) - ((0 : ℕ) : Fin k) = pos' h start (l + 2*t) := by
  unfold pos'
  rw [show start + h + 3 = (start + (h-1-l-2*t)) + (l+2*t+4) by omega]
  push_cast; ring

theorem colPos (h start l t : ℕ) (ht : l + 2*t + 1 ≤ h) :
    ((start + (h-1-l-2*t) : ℕ) : Fin k) - ((4 : ℕ) : Fin k) = pos' h start (l + 2*(t+2)) := by
  unfold pos'
  rw [show start + h + 3 = (start + (h-1-l-2*t)) + (l+2*t+4) by omega]
  push_cast; ring

theorem mkKey (N : ℕ) (P : ℕ → Fin k) (hinj : ∀ a b, a < N → b < N → P a = P b → a = b)
    (v : ℕ → Bool) : ∃ key : Fin k → Bool, ∀ n < N, key (P n) = v n := by
  classical
  refine ⟨fun q => if hq : ∃ n, n < N ∧ P n = q then v (Classical.choose hq) else false, ?_⟩
  intro n hn
  have hq : ∃ n', n' < N ∧ P n' = P n := ⟨n, hn, rfl⟩
  show (if hq : ∃ n', n' < N ∧ P n' = P n then v (Classical.choose hq) else false) = v n
  rw [dif_pos hq]
  have := Classical.choose_spec hq
  rw [hinj _ _ this.1 hn this.2]

end

def fs (n : ℕ) (P : ℕ → Bool) : ℕ := ((List.range n).filter P).headD n

theorem fsSpec (n : ℕ) (P : ℕ → Bool) :
    fs n P ≤ n ∧ (∀ t < fs n P, P t = false) ∧ (fs n P < n → P (fs n P) = true) := by
  have := headSpec P n 0
  simp only [Nat.zero_add, ← List.range_eq_range'] at this
  obtain ⟨_, i2, i3, i4⟩ := this
  exact ⟨i2, fun t ht => i3 t (Nat.zero_le _) ht, i4⟩

theorem fsEq (n : ℕ) (P : ℕ → Bool) (a : ℕ) (ha : a ≤ n) (h1 : ∀ t < a, P t = false)
    (h2 : a < n → P a = true) : fs n P = a := by
  obtain ⟨s1, s2, s3⟩ := fsSpec n P
  rcases Nat.lt_trichotomy (fs n P) a with h | h | h
  · have := h1 _ h; rw [s3 (by omega)] at this; exact absurd this (by simp)
  · exact h
  · have := s2 a h; rw [h2 (by omega)] at this; exact absurd this (by simp)

theorem fs_congr (n : ℕ) (P Q : ℕ → Bool) (h : ∀ t < n, P t = Q t) : fs n P = fs n Q := by
  unfold fs
  congr 1
  apply List.filter_congr
  intro t ht
  exact h t (List.mem_range.mp ht)

abbrev Reach (m p a b : ℕ) : Prop :=
  a ≤ 1 ∨ (2 ≤ a ∧ a < m ∧ ((a-2 < p ∧ b = a-2) ∨ (a-2 = p ∧ p < b) ∨ (p < a-2 ∧ b = p))) ∨
    (a = m ∧ 2 ≤ m ∧ ((p = m-2 ∧ m-2 ≤ b) ∨ (p < m-2 ∧ b = p)))


def rowS (m : ℕ) (r x : ℕ → Bool) : ℕ := fs m (fun t => xor (r t) (x t))
def colS (m : ℕ) (c x : ℕ → Bool) : ℕ := fs m (fun t => xor (c t) (x (t+2)))
def pp (m : ℕ) (r c : ℕ → Bool) : ℕ := fs (m-2) (fun t => r (t+2) != c t)
def SS (m : ℕ) (r c : ℕ → Bool) : Finset (ℕ × ℕ) :=
  (Finset.range (m+1) ×ˢ Finset.range (m+1)).filter (fun ab => Reach m (pp m r c) ab.1 ab.2)

theorem bxf : ∀ u v : Bool, xor u v = false → v = u := by decide
theorem bxt : ∀ u v : Bool, xor u v = true → v = !u := by decide
theorem bnf : ∀ u v : Bool, (u != v) = false → v = u := by decide
theorem bnt : ∀ u v : Bool, (u != v) = true → v = !u := by decide
theorem xnt : ∀ u : Bool, xor u (!u) = true := by decide
theorem xnf : ∀ u : Bool, xor (!u) (!u) = false := by decide

theorem laneIn (m : ℕ) (r c x : ℕ → Bool) : (rowS m r x, colS m c x) ∈ SS m r c := by
  obtain ⟨p1, p2, p3⟩ := fsSpec (m-2) (fun t => r (t+2) != c t)
  obtain ⟨a1, a2, a3⟩ := fsSpec m (fun t => xor (r t) (x t))
  obtain ⟨b1, b2, b3⟩ := fsSpec m (fun t => xor (c t) (x (t+2)))
  unfold SS
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  simp only [rowS, colS, pp]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  generalize fs (m-2) (fun t => r (t+2) != c t) = p at p1 p2 p3
  generalize fs m (fun t => xor (r t) (x t)) = a at a1 a2 a3
  generalize fs m (fun t => xor (c t) (x (t+2))) = b at b1 b2 b3
  have hx : ∀ t < a, x t = r t := fun t ht => bxf _ _ (a2 t ht)
  have hc : ∀ t < p, c t = r (t+2) := fun t ht => bnf _ _ (p2 t ht)
  unfold Reach
  by_cases a01 : a ≤ 1
  · exact Or.inl a01
  right
  by_cases am : a < m
  · left
    refine ⟨by omega, am, ?_⟩
    have xa : x a = !r a := bxt _ _ (a3 am)
    rcases Nat.lt_trichotomy (a-2) p with hq | hq | hq
    · left; refine ⟨hq, ?_⟩
      by_contra hb
      rcases Nat.lt_or_gt_of_ne hb with hb | hb
      · have := b3 (by omega)
        rw [hx (b+2) (by omega), hc b (by omega)] at this; simp at this
      · have := b2 (a-2) hb
        rw [hc (a-2) hq, show a - 2 + 2 = a by omega, xa, xnt] at this
        exact absurd this (by simp)
    · right; left; refine ⟨hq, ?_⟩
      have hcp : c p = !r (p+2) := bnt _ _ (p3 (by omega))
      by_contra hb
      have := b3 (by omega)
      rcases Nat.lt_or_ge b p with hb2 | hb2
      · rw [hx (b+2) (by omega), hc b hb2] at this; simp at this
      · rw [show b = p by omega, hcp, show p + 2 = a by omega, xa, xnf] at this
        exact absurd this (by simp)
    · right; right; refine ⟨hq, ?_⟩
      have hcp : c p = !r (p+2) := bnt _ _ (p3 (by omega))
      by_contra hb
      rcases Nat.lt_or_gt_of_ne hb with hb | hb
      · have := b3 (by omega)
        rw [hx (b+2) (by omega), hc b (by omega)] at this; simp at this
      · have := b2 p hb
        rw [hcp, hx (p+2) (by omega), Bool.xor_comm, xnt] at this
        exact absurd this (by simp)
  · right
    refine ⟨by omega, by omega, ?_⟩
    by_cases pc : p = m-2
    · left; refine ⟨pc, ?_⟩
      by_contra hb
      have := b3 (by omega)
      rw [hx (b+2) (by omega), hc b (by omega)] at this; simp at this
    · right; refine ⟨by omega, ?_⟩
      have hcp : c p = !r (p+2) := bnt _ _ (p3 (by omega))
      by_contra hb
      rcases Nat.lt_or_gt_of_ne hb with hb | hb
      · have := b3 (by omega)
        rw [hx (b+2) (by omega), hc b (by omega)] at this; simp at this
      · have := b2 p hb
        rw [hcp, hx (p+2) (by omega), Bool.xor_comm, xnt] at this
        exact absurd this (by simp)

theorem laneReal (m : ℕ) (r c : ℕ → Bool) (ab : ℕ × ℕ) (hab : ab ∈ SS m r c) :
    ∃ x : ℕ → Bool, rowS m r x = ab.1 ∧ colS m c x = ab.2 := by
  obtain ⟨a, b⟩ := ab
  unfold SS at hab
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
  obtain ⟨⟨ha, hb⟩, hR⟩ := hab
  dsimp only at ha hb hR
  obtain ⟨p1, p2, p3⟩ := fsSpec (m-2) (fun t => r (t+2) != c t)
  have hpp : pp m r c = fs (m-2) (fun t => r (t+2) != c t) := rfl
  rw [hpp] at hR
  generalize fs (m-2) (fun t => r (t+2) != c t) = p at p1 p2 p3 hR
  have hc : ∀ t < p, c t = r (t+2) := fun t ht => bnf _ _ (p2 t ht)
  let x : ℕ → Bool := fun t => if t < a then r t else if t = a ∧ a < m then !r t else
    (if t - 2 < b then c (t-2) else !c (t-2))
  have X1 : ∀ t < a, x t = r t := fun t ht => if_pos ht
  have X2 : a < m → x a = !r a := fun h => by
    show (if a < a then r a else if a = a ∧ a < m then !r a else _) = _
    rw [if_neg (lt_irrefl a), if_pos ⟨rfl, h⟩]
  have X3 : ∀ t, ¬ t + 2 < a → ¬ (t + 2 = a ∧ a < m) →
      x (t+2) = if t < b then c t else !c t := by
    intro t h1 h2
    show (if t+2 < a then r (t+2) else if t+2 = a ∧ a < m then !r (t+2) else
      (if t + 2 - 2 < b then c (t+2-2) else !c (t+2-2))) = _
    rw [if_neg h1, if_neg h2, Nat.add_sub_cancel]
  have hrow : rowS m r x = a := by
    apply fsEq _ _ _ (by omega)
    · intro t ht; rw [X1 t ht]; simp
    · intro h; rw [X2 h]; exact xnt _
  refine ⟨x, hrow, ?_⟩
  show fs m (fun t => xor (c t) (x (t+2))) = b
  -- column value outside the row part
  have Cfree : ∀ t, ¬ t + 2 < a → ¬ (t + 2 = a ∧ a < m) → t < b →
      xor (c t) (x (t+2)) = false := by
    intro t h1 h2 h3; rw [X3 t h1 h2, if_pos h3]; simp
  have Cstop : b < m → ¬ b + 2 < a → ¬ (b + 2 = a ∧ a < m) → xor (c b) (x (b+2)) = true := by
    intro h0 h1 h2; rw [X3 b h1 h2, if_neg (lt_irrefl b)]; exact xnt _
  have Crow : ∀ t, t < p → t + 2 < a → xor (c t) (x (t+2)) = false := by
    intro t h1 h2; rw [X1 (t+2) h2, hc t h1]; simp
  unfold Reach at hR
  rcases hR with h01 | ⟨h2a, ham, hq⟩ | ⟨ham, h2m, hq⟩
  · apply fsEq _ _ _ (by omega)
    · intro t ht; exact Cfree t (by omega) (by omega) ht
    · intro h0; exact Cstop h0 (by omega) (by omega)
  · rcases hq with ⟨hq, hbq⟩ | ⟨hq, hbq⟩ | ⟨hq, hbq⟩
    · apply fsEq _ _ _ (by omega)
      · intro t ht; exact Crow t (by omega) (by omega)
      · intro _
        rw [show b + 2 = a by omega, X2 ham, hc b (by omega), show b + 2 = a by omega]
        exact xnt _
    · have hcp : c p = !r (p+2) := bnt _ _ (p3 (by omega))
      apply fsEq _ _ _ (by omega)
      · intro t ht
        rcases Nat.lt_trichotomy t p with h | h | h
        · exact Crow t h (by omega)
        · rw [h, hcp, show p + 2 = a by omega, X2 ham]; exact xnf _
        · exact Cfree t (by omega) (by omega) ht
      · intro h0; exact Cstop h0 (by omega) (by omega)
    · have hcp : c p = !r (p+2) := bnt _ _ (p3 (by omega))
      apply fsEq _ _ _ (by omega)
      · intro t ht; exact Crow t (by omega) (by omega)
      · intro _
        rw [hbq, hcp, X1 (p+2) (by omega), Bool.xor_comm]; exact xnt _
  · rcases hq with ⟨hq, hbq⟩ | ⟨hq, hbq⟩
    · apply fsEq _ _ _ (by omega)
      · intro t ht
        by_cases h : t < m - 2
        · exact Crow t (by omega) (by omega)
        · exact Cfree t (by omega) (by omega) ht
      · intro h0; exact Cstop h0 (by omega) (by omega)
    · have hcp : c p = !r (p+2) := bnt _ _ (p3 (by omega))
      apply fsEq _ _ _ (by omega)
      · intro t ht; exact Crow t (by omega) (by omega)
      · intro _
        rw [hbq, hcp, X1 (p+2) (by omega), Bool.xor_comm]; exact xnt _

def Fv (m p a : ℕ) : ℕ :=
  if a ≤ 1 then m+1 else if a < m then (if a - 2 = p then m - p else 1) else
    (if p = m-2 then 3 else 1)

theorem fiber (m p a : ℕ) (ha : a ≤ m) (hp : p ≤ m-2) :
    ((Finset.range (m+1)).filter (fun b => Reach m p a b)).card = Fv m p a := by
  have e : ∀ lo hi, (∀ b ≤ m, Reach m p a b ↔ lo ≤ b ∧ b ≤ hi) → hi ≤ m →
      ((Finset.range (m+1)).filter (fun b => Reach m p a b)).card = hi + 1 - lo := by
    intro lo hi H hm
    rw [← Nat.card_Icc]
    congr 1
    ext b
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact (H b (by omega)).1 h2
    · rintro ⟨h1, h2⟩; exact ⟨by omega, (H b (by omega)).2 ⟨h1, h2⟩⟩
  unfold Fv
  split_ifs with h1 h2 h3 h4
  · rw [e 0 m (by intro b hb; unfold Reach; omega) le_rfl]; omega
  · rw [e (p+1) m (by intro b hb; unfold Reach; omega) le_rfl]; omega
  · rcases Nat.lt_or_gt_of_ne h3 with h | h
    · rw [e (a-2) (a-2) (by intro b hb; unfold Reach; omega) (by omega)]; omega
    · rw [e p p (by intro b hb; unfold Reach; omega) (by omega)]; omega
  · rw [e (m-2) m (by intro b hb; unfold Reach; omega) le_rfl]; omega
  · rw [e p p (by intro b hb; unfold Reach; omega) (by omega)]; omega

theorem sumF (m p : ℕ) (hp : p ≤ m-2) : ∀ n, 2 ≤ n → n ≤ m →
    ∑ a ∈ Finset.range n, Fv m p a = 2*(m+1) + (n-2) + (if p + 2 < n then m-p-1 else 0) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _
    simp [Finset.sum_range_succ, Fv]
    omega
  | succ n hn ih =>
    intro hm
    rw [Finset.sum_range_succ, ih (by omega)]
    unfold Fv
    split_ifs <;> omega

theorem laneCard (m : ℕ) (r c : ℕ → Bool) :
    (SS m r c).card = if m ≤ 1 then (m+1)^2 else if pp m r c = m-2 then 3*(m+1)
      else 4*m - pp m r c := by
  have hp : pp m r c ≤ m-2 := (fsSpec _ _).1
  unfold SS
  generalize pp m r c = p at hp ⊢
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ a ∈ Finset.range (m+1),
      (∑ b ∈ Finset.range (m+1), if Reach m p (a, b).1 (a, b).2 then 1 else 0) = Fv m p a := by
    intro a ha
    rw [← fiber m p a (by simpa [Nat.lt_succ_iff] using ha) hp, Finset.card_filter]
  rw [Finset.sum_congr rfl inner]
  split_ifs with h1 h2
  · rw [Finset.sum_congr rfl (fun a ha => show Fv m p a = m+1 by
      unfold Fv; rw [if_pos (by simp at ha; omega)])]
    simp; ring
  · rw [Finset.sum_range_succ, sumF m p hp m (by omega) le_rfl]
    unfold Fv
    split_ifs <;> omega
  · rw [Finset.sum_range_succ, sumF m p hp m (by omega) le_rfl]
    unfold Fv
    split_ifs <;> omega


end PEqualNP.Outside.L_meta_33683

open Fin.CommRing PEqualNP.Outside.L_meta_33683 in
theorem PEqualNP.Outside.L_meta_33683 : ∀ (k h start : Nat) (hk : 0 < k), 0 < h → h+7 ≤ k →
  let W := Fin k → Bool
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (p : Fin k) => xor (x p) (y p)
  let mix := fun (gap : Nat) (x : W) (p : Fin k) =>
    xor (xor (x (ix (p.val + k - gap % k))) (x p)) (x (ix (p.val + gap)))
  let step := fun (z : W) (p : Fin k) =>
    xor (z p) (!(z (ix (p.val+1))) && z (ix (p.val+2)))
  let rot := fun (s : Nat) (x : W) (p : Fin k) => x (ix (p.val + k - s % k))
  ∀ (rc cc : W) (rt ct : Nat → Bool),
    let R := fun j : Nat => xor (rt j) (rc (ix (start+j)))
    let C := fun j : Nat => xor (ct j) (cc (ix (start+j)))
    let pass := fun (gap ini fin : Nat) (mask : Nat → Bool) (name key : W) =>
      ∀ j : Fin h,
        let site := ix (start+j.val)
        xor (step (mix gap (add name (rot ini key))) site) (rot fin key site) = mask j.val
    let orbit := fun key : W =>
      (Finset.univ : Finset (W × W)).image (fun shift =>
        (Finset.univ : Finset (W × W)).filter (fun nm =>
          pass 1 1 0 R (add nm.1 shift.1) key ∧ pass 2 3 4 C (add nm.2 shift.2) key))
    let count := fun lane : Nat =>
      let m := (h-lane)/2
      let site := fun t : Nat => h-1-lane-2*t
      let cut := m-2
      let p := ((List.range cut).filter (fun t => R (site (t+2)) != C (site t))).headD cut
      if m ≤ 1 then (m+1)^2 else if p = cut then 3*(m+1) else 4*m-p
    ((Finset.univ : Finset W).image orbit).card = count 0 * count 1 := by
  intro k h start hk hh hhk W ix add mix step rot rc cc rt ct R C pass orbit count
  have : NeZero k := ⟨by omega⟩
  have hP : ∀ (gap ini fin : ℕ) (mask : ℕ → Bool) (name key : W),
      pass gap ini fin mask name key ↔
      ∀ j < h, St (Mx gap (Ad name (fun q => key (q - (ini : Fin k))))) ((start + j : ℕ) : Fin k) =
        xor (mask j) (key (((start + j : ℕ) : Fin k) - (fin : Fin k))) := by
    intro gap ini fin mask name key
    simp only [pass, step, mix, add, rot, ix, ixN, castA, castS, St, Mx, Ad, Fin.forall_iff]
    apply forall_congr'; intro j; apply imp_congr_right; intro _
    exact bxzIff _ _ _
  let zA : W → ℕ → Bool := fun key j =>
    xor (R j) (key (((start + j : ℕ) : Fin k) - ((0 : ℕ) : Fin k)))
  let zB : W → ℕ → Bool := fun key j =>
    xor (C j) (key (((start + j : ℕ) : Fin k) - ((4 : ℕ) : Fin k)))
  have nA : ∀ key : W, ∃ u, pass 1 1 0 R u key := by
    intro key
    obtain ⟨u, hu⟩ := nonemp h 1 start (by omega) (by omega)
      (fun q => key (q - ((1 : ℕ) : Fin k))) (zA key)
    exact ⟨u, (hP 1 1 0 R u key).2 hu⟩
  have nB : ∀ key : W, ∃ u, pass 2 3 4 C u key := by
    intro key
    obtain ⟨u, hu⟩ := nonemp h 2 start (by omega) (by omega)
      (fun q => key (q - ((3 : ℕ) : Fin k))) (zB key)
    exact ⟨u, (hP 2 3 4 C u key).2 hu⟩
  have hcls : ∀ x y : W, orbit x = orbit y ↔
      ((stopF (zA x) h 0 = stopF (zA y) h 0 ∧ stopF (zA x) h 1 = stopF (zA y) h 1) ∧
       (stopF (zB x) h 0 = stopF (zB y) h 0 ∧ stopF (zB x) h 1 = stopF (zB y) h 1)) := by
    intro x y
    have E := orbEq (fun key u => pass 1 1 0 R u key) (fun key u => pass 2 3 4 C u key) x y nA nB
    refine E.trans ?_
    apply and_congr
    · rw [← classIff h 1 start (by omega) hh (by omega)
        (fun q => x (q - ((1 : ℕ) : Fin k))) (fun q => y (q - ((1 : ℕ) : Fin k))) (zA x) (zA y)]
      simp only [hP]
      rfl
    · rw [← classIff h 2 start (by omega) hh (by omega)
        (fun q => x (q - ((3 : ℕ) : Fin k))) (fun q => y (q - ((3 : ℕ) : Fin k))) (zB x) (zB y)]
      simp only [hP]
      rfl
  let g : W → (ℕ × ℕ) × (ℕ × ℕ) := fun key =>
    ((stopF (zA key) h 0, stopF (zB key) h 0), (stopF (zA key) h 1, stopF (zB key) h 1))
  rw [cardImg orbit g (fun x y => by rw [hcls]; simp only [g, Prod.mk.injEq]; tauto)]
  let rl : ℕ → ℕ → Bool := fun l t => R (h-1-l-2*t)
  let cl : ℕ → ℕ → Bool := fun l t => C (h-1-l-2*t)
  have sA : ∀ (key : W) (l : ℕ), stopF (zA key) h l =
      rowS ((h-l)/2) (rl l) (fun t => key (pos' h start (l+2*t))) := by
    intro key l
    show fs ((h-l)/2) (fun t => zA key (h-1-l-2*t)) = _
    unfold rowS
    apply fs_congr
    intro t ht
    show xor (R _) (key _) = xor (R _) (key _)
    rw [rowPos h start l t (by omega)]
  have sB : ∀ (key : W) (l : ℕ), stopF (zB key) h l =
      colS ((h-l)/2) (cl l) (fun t => key (pos' h start (l+2*t))) := by
    intro key l
    show fs ((h-l)/2) (fun t => zB key (h-1-l-2*t)) = _
    unfold colS
    apply fs_congr
    intro t ht
    show xor (C _) (key _) = xor (C _) (key _)
    rw [colPos h start l t (by omega)]
  have himg : (Finset.univ : Finset W).image g =
      SS ((h-0)/2) (rl 0) (cl 0) ×ˢ SS ((h-1)/2) (rl 1) (cl 1) := by
    ext ⟨ab0, ab1⟩
    rw [Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨key, _, hk⟩
      rw [← hk]
      show (stopF (zA key) h 0, stopF (zB key) h 0) ∈ _ ∧ (stopF (zA key) h 1, stopF (zB key) h 1) ∈ _
      rw [sA, sB, sA, sB]
      exact ⟨laneIn _ _ _ _, laneIn _ _ _ _⟩
    · rintro ⟨m0, m1⟩
      obtain ⟨x0, e0, f0⟩ := laneReal _ _ _ _ m0
      obtain ⟨x1, e1, f1⟩ := laneReal _ _ _ _ m1
      obtain ⟨key, hkey⟩ := mkKey (h+3) (pos' h start)
        (fun a b ha hb e => pos'_inj h start a b hhk ha hb e)
        (fun n => if n % 2 = 0 then x0 (n/2) else x1 (n/2))
      have k0 : ∀ t < (h-0)/2 + 2, key (pos' h start (0+2*t)) = x0 t := by
        intro t ht; rw [hkey _ (by omega), if_pos (by omega), show (0+2*t)/2 = t by omega]
      have k1 : ∀ t < (h-1)/2 + 2, key (pos' h start (1+2*t)) = x1 t := by
        intro t ht; rw [hkey _ (by omega), if_neg (by omega), show (1+2*t)/2 = t by omega]
      refine ⟨key, Finset.mem_univ _, ?_⟩
      show ((stopF (zA key) h 0, stopF (zB key) h 0), (stopF (zA key) h 1, stopF (zB key) h 1)) = _
      rw [sA, sB, sA, sB]
      obtain ⟨a0, b0⟩ := ab0
      obtain ⟨a1, b1⟩ := ab1
      simp only at e0 f0 e1 f1
      rw [← e0, ← f0, ← e1, ← f1]
      unfold rowS colS
      congr 2
      · exact fs_congr _ _ _ (fun t ht => by
          show xor _ (key _) = xor _ (x0 t); rw [k0 t (by omega)])
      · exact fs_congr _ _ _ (fun t ht => by
          show xor _ (key _) = xor _ (x0 (t+2)); rw [k0 (t+2) (by omega)])
      · exact fs_congr _ _ _ (fun t ht => by
          show xor _ (key _) = xor _ (x1 t); rw [k1 t (by omega)])
      · exact fs_congr _ _ _ (fun t ht => by
          show xor _ (key _) = xor _ (x1 (t+2)); rw [k1 (t+2) (by omega)])
  rw [himg, Finset.card_product, laneCard, laneCard]
  rfl
