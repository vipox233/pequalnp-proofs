import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33682

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

end

end PEqualNP.Outside.L_meta_33682

open Fin.CommRing PEqualNP.Outside.L_meta_33682 in
theorem PEqualNP.Outside.L_meta_33682 : ∀ (k h d start : Nat) (hk : 0 < k), 0 < d → 0 < h → h+2+2*d ≤ k →
  let W := Fin k → Bool
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (p : Fin k) => xor (x p) (y p)
  let mix := fun (gap : Nat) (x : W) (p : Fin k) =>
    xor (xor (x (ix (p.val + k - gap % k))) (x p)) (x (ix (p.val + gap)))
  let step := fun (z : W) (p : Fin k) =>
    xor (z p) (!(z (ix (p.val+1))) && z (ix (p.val+2)))
  let accepts := fun (offset : W) (z : Nat → Bool) (u : W) =>
    ∀ j : Fin h, step (mix d (add u offset)) (ix (start+j.val)) = z j.val
  let stop := fun (z : Nat → Bool) (lane : Nat) =>
    let m := (h-lane)/2
    ((List.range m).filter (fun t => z (h-1-lane-2*t))).headD m
  ∀ (offset₀ offset₁ : W) (z₀ z₁ : Nat → Bool),
    let shifts := (Finset.univ : Finset W).filter (fun delta =>
      ∀ u : W, accepts offset₀ z₀ u ↔ accepts offset₁ z₁ (add u delta))
    shifts.card = if stop z₀ 0 = stop z₁ 0 ∧ stop z₀ 1 = stop z₁ 1
      then 2^(k-(h+2)) else 0 := by
  intro k h d start hk hd hh hhk W ix add mix step accepts stop offset₀ offset₁ z₀ z₁ shifts
  have : NeZero k := ⟨by omega⟩
  have hA : ∀ (o : W) (z : ℕ → Bool) (u : W), accepts o z u ↔
      ∀ j < h, St (Mx d (Ad u o)) ((start + j : ℕ) : Fin k) = z j := by
    intro o z u
    simp only [accepts, step, mix, add, ix, ixN, castA, castS, St, Mx, Ad, Fin.forall_iff]
  have hs : ∀ z lane, stop z lane = stopF z h lane := fun _ _ => rfl
  have e : shifts = Finset.univ.filter (fun δ : Fin k → Bool => ∀ u : Fin k → Bool,
      (∀ j < h, St (Mx d (Ad u offset₀)) ((start + j : ℕ) : Fin k) = z₀ j) ↔
      (∀ j < h, St (Mx d (Ad (Ad u δ) offset₁)) ((start + j : ℕ) : Fin k) = z₁ j)) := by
    ext δ
    simp only [shifts, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'; intro u
    rw [hA, hA]
    rfl
  rw [e, hs, hs, hs, hs]
  exact mainCount h d start hd hh hhk offset₀ offset₁ z₀ z₁
