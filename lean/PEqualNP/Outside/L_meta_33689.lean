import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33689_aux

def bitf (u j : ℕ) : Bool :=
  xor (u.testBit j) (!(u.testBit (j+1)) && u.testBit (j+2))

def reply (h u : ℕ) : ℕ := ∑ j ∈ Finset.range h, if bitf u j then 2^j else 0

def mask (top r : ℕ) : ℕ := ∑ i ∈ Finset.range (r+1), 2^(top - 2*i)

def dist (Q : List (ℕ × ℕ)) (u v : ℕ) : ℕ :=
  (Q.filter (fun p => bitf (u ^^^ p.1) p.2 != bitf (v ^^^ p.1) p.2)).length

def wt (Q : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (Q.filter (fun p => xor
    (v.testBit (p.2+1) && p.1.testBit (p.2+2))
    (v.testBit (p.2+2) && p.1.testBit (p.2+1)))).length

def Sol (h z u : ℕ) : Prop := u < 2^(h+2) ∧ ∀ j < h, bitf u j = z.testBit j

def RunA (h z r : ℕ) : Prop :=
  r ≤ h/2 ∧ (∀ i < r, z.testBit (h-1-2*i) = false) ∧ (r < h/2 → z.testBit (h-1-2*r) = true)

def RunC (h z s : ℕ) : Prop :=
  s ≤ (h-1)/2 ∧ (∀ i < s, z.testBit (h-2-2*i) = false) ∧ (s < (h-1)/2 → z.testBit (h-2-2*s) = true)

theorem sum_pow_lt_aux (N : ℕ) (c : ℕ → Bool) :
    (∑ i ∈ Finset.range N, if c i then 2^i else 0) < 2^N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    split <;> omega

theorem testBit_sum_pow (N : ℕ) (c : ℕ → Bool) (j : ℕ) :
    (∑ i ∈ Finset.range N, if c i then 2^i else 0).testBit j = (decide (j < N) && c j) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hS := sum_pow_lt_aux n c
    rw [Finset.sum_range_succ]
    generalize (∑ i ∈ Finset.range n, if c i then 2^i else 0) = S at ih hS ⊢
    rcases Nat.lt_trichotomy j n with hj | hj | hj
    · have e : (decide (j < n + 1) && c j) = (decide (j < n) && c j) := by
        simp [hj, Nat.lt_succ_of_lt hj]
      rw [e, ← ih]
      split
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hj]
      · rw [Nat.add_zero]
    · subst hj
      have hb : S.testBit j = false := Nat.testBit_lt_two_pow hS
      cases hc : c j
      · simp [hb]
      · rw [ite_eq_left rfl, Nat.add_comm, Nat.testBit_two_pow_add_eq, hb]
        simp
    · have hlt : S + (if c n then 2^n else 0) < 2^j := by
        have h1 : S + (if c n then 2^n else 0) < 2^(n+1) := by
          rw [pow_succ]
          split <;> omega
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hj)
      rw [Nat.testBit_lt_two_pow hlt]
      have hnj : ¬ j < n + 1 := by omega
      simp [hnj]

theorem sum_pow_lt (N : ℕ) (c : ℕ → Bool) :
    (∑ i ∈ Finset.range N, if c i then 2^i else 0) < 2^N := by
  exact sum_pow_lt_aux N c

theorem testBit_mask (top r j : ℕ) (hr : 2*r ≤ top) :
    (mask top r).testBit j = decide (j ≤ top ∧ (top - j) % 2 = 0 ∧ (top - j) / 2 ≤ r) := by
  have himg : (Finset.range (top+1)).filter
        (fun i => decide (i ≤ top ∧ (top - i) % 2 = 0 ∧ (top - i) / 2 ≤ r) = true)
      = (Finset.range (r+1)).image (fun i => top - 2*i) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h1, h2, h3⟩
      exact ⟨(top - a)/2, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨by omega, by omega, by omega, by omega⟩
  have hinj : Set.InjOn (fun i => top - 2*i) (Finset.range (r+1) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < r + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hx)
    have hy' : y < r + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hy)
    have hxy' : top - 2*x = top - 2*y := hxy
    omega
  have key : mask top r = ∑ i ∈ Finset.range (top+1),
      if decide (i ≤ top ∧ (top - i) % 2 = 0 ∧ (top - i) / 2 ≤ r) then 2^i else 0 := by
    unfold mask
    rw [← Finset.sum_filter, himg, Finset.sum_image hinj]
  rw [key, testBit_sum_pow]
  by_cases h : j ≤ top
  · have h' : j < top + 1 := by omega
    simp [h']
  · simp [h]

theorem flip_mem (h a : ℕ) (hah : a < h) (S : Finset ℕ) (ha : a ∉ S) (val : ℕ → Bool) (z : ℕ)
    (hz : z ∈ (Finset.range (2^h)).filter (fun z => ∀ i ∈ S, z.testBit i = val i)) :
    z ^^^ 2^a ∈ (Finset.range (2^h)).filter (fun z => ∀ i ∈ S, z.testBit i = val i) ∧
      (z ^^^ 2^a).testBit a = !z.testBit a := by
  rw [Finset.mem_filter, Finset.mem_range] at hz ⊢
  refine ⟨⟨Nat.xor_lt_two_pow hz.1 (Nat.pow_lt_pow_right (by norm_num) hah), fun i hi => ?_⟩, ?_⟩
  · rw [Nat.testBit_xor, Nat.testBit_two_pow]
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    simp [hne, hz.2 i hi]
  · rw [Nat.testBit_xor, Nat.testBit_two_pow]
    simp

theorem card_half (F : Finset ℕ) (a : ℕ) (b : Bool)
    (hflip : ∀ z ∈ F, z ^^^ 2^a ∈ F ∧ (z ^^^ 2^a).testBit a = !z.testBit a) :
    2 * (F.filter (fun z => z.testBit a = b)).card = F.card := by
  have h1 : (F.filter (fun z => z.testBit a = b)).card
      ≤ (F.filter (fun z => ¬ z.testBit a = b)).card := by
    apply Finset.card_le_card_of_injOn (fun z => z ^^^ 2^a)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      obtain ⟨m, t⟩ := hflip z hz.1
      refine ⟨m, ?_⟩
      rw [t, hz.2]
      cases b <;> simp
    · intro x _ y _ hxy
      exact Nat.xor_left_injective hxy
  have h2 : (F.filter (fun z => ¬ z.testBit a = b)).card
      ≤ (F.filter (fun z => z.testBit a = b)).card := by
    apply Finset.card_le_card_of_injOn (fun z => z ^^^ 2^a)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      obtain ⟨m, t⟩ := hflip z hz.1
      refine ⟨m, ?_⟩
      have h3 := hz.2
      rw [t]
      revert h3
      generalize z.testBit a = c
      cases c <;> cases b <;> simp
    · intro x _ y _ hxy
      exact Nat.xor_left_injective hxy
  have hsplit : (F.filter (fun z => z.testBit a = b)).card
      + (F.filter (fun z => ¬ z.testBit a = b)).card = F.card :=
    Finset.card_filter_add_card_filter_not _
  omega

theorem card_bits (h : ℕ) (S : Finset ℕ) (hS : ∀ i ∈ S, i < h) (val : ℕ → Bool) :
    ((Finset.range (2^h)).filter (fun z => ∀ i ∈ S, z.testBit i = val i)).card
      = 2^(h - S.card) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS' : ∀ i ∈ S, i < h := fun i hi => hS i (Finset.mem_insert_of_mem hi)
    have hah : a < h := hS a (Finset.mem_insert_self a S)
    have ih' := ih hS'
    have hcard : S.card + 1 ≤ h := by
      have hsub : insert a S ⊆ Finset.range h := fun i hi => Finset.mem_range.mpr (hS i hi)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem ha, Finset.card_range] at hle
      exact hle
    have hhalf := card_half
      ((Finset.range (2^h)).filter (fun z => ∀ i ∈ S, z.testBit i = val i)) a (val a)
      (fun z hz => flip_mem h a hah S ha val z hz)
    have heq : (Finset.range (2^h)).filter (fun z => ∀ i ∈ insert a S, z.testBit i = val i)
        = ((Finset.range (2^h)).filter (fun z => ∀ i ∈ S, z.testBit i = val i)).filter
            (fun z => z.testBit a = val a) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_range, Finset.forall_mem_insert]
      tauto
    rw [heq, Finset.card_insert_of_notMem ha]
    have hpow : 2^(h - S.card) = 2 * 2^(h - (S.card+1)) := by
      rw [← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (hhalf.trans (ih'.trans hpow))

theorem dist_eq_wt (h : ℕ) (Q : List (ℕ × ℕ)) (hQ : ∀ p ∈ Q, p.2 < h) (u u' : ℕ)
    (huu : ∀ j < h, bitf u j = bitf u' j) : dist Q u u' = wt Q (u ^^^ u') := by
  unfold dist wt
  refine congrArg List.length (List.filter_congr ?_)
  intro p hp
  have e := huu p.2 (hQ p hp)
  simp only [bitf, Nat.testBit_xor] at e ⊢
  revert e
  generalize u.testBit p.2 = a0
  generalize u.testBit (p.2+1) = a1
  generalize u.testBit (p.2+2) = a2
  generalize u'.testBit p.2 = b0
  generalize u'.testBit (p.2+1) = b1
  generalize u'.testBit (p.2+2) = b2
  generalize p.1.testBit p.2 = c0
  generalize p.1.testBit (p.2+1) = c1
  generalize p.1.testBit (p.2+2) = c2
  revert a0 a1 a2 b0 b1 b2 c0 c1 c2
  decide

def laneSet (h r s : ℕ) : Finset ℕ :=
  (Finset.range (min (r+1) (h/2))).image (fun i => h-1-2*i) ∪
    (Finset.range (min (s+1) ((h-1)/2))).image (fun i => h-2-2*i)

def laneVal (h r s j : ℕ) : Bool :=
  decide ((r < h/2 ∧ j = h-1-2*r) ∨ (s < (h-1)/2 ∧ j = h-2-2*s))

theorem mem_laneSet (h r s j : ℕ) : j ∈ laneSet h r s ↔
    (∃ i, i < min (r+1) (h/2) ∧ h-1-2*i = j) ∨ (∃ i, i < min (s+1) ((h-1)/2) ∧ h-2-2*i = j) := by
  simp only [laneSet, Finset.mem_union, Finset.mem_image, Finset.mem_range]

theorem laneSet_lt (h r s : ℕ) (hh : 0 < h) : ∀ j ∈ laneSet h r s, j < h := by
  intro j hj
  rw [mem_laneSet] at hj
  rcases hj with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> omega

theorem laneVal_false (h r s j : ℕ) : laneVal h r s j = false ↔
    ¬ ((r < h/2 ∧ j = h-1-2*r) ∨ (s < (h-1)/2 ∧ j = h-2-2*s)) := by
  simp only [laneVal, decide_eq_false_iff_not]

theorem laneVal_true (h r s j : ℕ) : laneVal h r s j = true ↔
    ((r < h/2 ∧ j = h-1-2*r) ∨ (s < (h-1)/2 ∧ j = h-2-2*s)) := by
  simp only [laneVal, decide_eq_true_eq]

theorem laneSet_card (h r s : ℕ) :
    (laneSet h r s).card = min (r+1) (h/2) + min (s+1) ((h-1)/2) := by
  have hinj1 : Set.InjOn (fun i => h-1-2*i) (Finset.range (min (r+1) (h/2)) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < min (r+1) (h/2) := Finset.mem_range.mp (Finset.mem_coe.mp hx)
    have hy' : y < min (r+1) (h/2) := Finset.mem_range.mp (Finset.mem_coe.mp hy)
    have hxy' : h-1-2*x = h-1-2*y := hxy
    omega
  have hinj2 : Set.InjOn (fun i => h-2-2*i) (Finset.range (min (s+1) ((h-1)/2)) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < min (s+1) ((h-1)/2) := Finset.mem_range.mp (Finset.mem_coe.mp hx)
    have hy' : y < min (s+1) ((h-1)/2) := Finset.mem_range.mp (Finset.mem_coe.mp hy)
    have hxy' : h-2-2*x = h-2-2*y := hxy
    omega
  have hdisj : Disjoint ((Finset.range (min (r+1) (h/2))).image (fun i => h-1-2*i))
      ((Finset.range (min (s+1) ((h-1)/2))).image (fun i => h-2-2*i)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_image, Finset.mem_range] at h1 h2
    obtain ⟨i, hi, rfl⟩ := h1
    obtain ⟨i', hi', e⟩ := h2
    omega
  unfold laneSet
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
    Finset.card_image_of_injOn hinj2, Finset.card_range, Finset.card_range]

theorem count_type_aux (h r s : ℕ) (hr : r ≤ h/2) (hs : s ≤ (h-1)/2) (z : ℕ) :
    (RunA h z r ∧ RunC h z s) ↔ ∀ j ∈ laneSet h r s, z.testBit j = laneVal h r s j := by
  constructor
  · rintro ⟨⟨_, a1, a2⟩, ⟨_, c1, c2⟩⟩ j hj
    rw [mem_laneSet] at hj
    rcases hj with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · by_cases hir : i < r
      · rw [a1 i hir, eq_comm, laneVal_false]
        omega
      · have hir' : i = r := by omega
        subst hir'
        rw [a2 (by omega), eq_comm, laneVal_true]
        omega
    · by_cases his : i < s
      · rw [c1 i his, eq_comm, laneVal_false]
        omega
      · have his' : i = s := by omega
        subst his'
        rw [c2 (by omega), eq_comm, laneVal_true]
        omega
  · intro H
    refine ⟨⟨hr, fun i hi => ?_, fun hlt => ?_⟩, ⟨hs, fun i hi => ?_, fun hlt => ?_⟩⟩
    · rw [H _ ((mem_laneSet _ _ _ _).mpr (Or.inl ⟨i, by omega, rfl⟩)), laneVal_false]
      omega
    · rw [H _ ((mem_laneSet _ _ _ _).mpr (Or.inl ⟨r, by omega, rfl⟩)), laneVal_true]
      omega
    · rw [H _ ((mem_laneSet _ _ _ _).mpr (Or.inr ⟨i, by omega, rfl⟩)), laneVal_false]
      omega
    · rw [H _ ((mem_laneSet _ _ _ _).mpr (Or.inr ⟨s, by omega, rfl⟩)), laneVal_true]
      omega

open Classical in
theorem count_type (h r s : ℕ) (hh : 0 < h) (hr : r ≤ h/2) (hs : s ≤ (h-1)/2) :
    ((Finset.range (2^h)).filter (fun z => RunA h z r ∧ RunC h z s)).card
      = 2^(h - (min (r+1) (h/2) + min (s+1) ((h-1)/2))) := by
  have h1 := card_bits h (laneSet h r s) (laneSet_lt h r s hh) (laneVal h r s)
  rw [laneSet_card h r s] at h1
  rw [← h1]
  exact congrArg Finset.card (Finset.filter_congr fun z _ => count_type_aux h r s hr hs z)

theorem sol_rec (h z u j a b : ℕ) (hu : Sol h z u) (hj : j < h) (ha : a = j + 1)
    (hb : b = j + 2) :
    u.testBit j = xor (z.testBit j) (!(u.testBit a) && u.testBit b) := by
  subst ha hb
  have := hu.2 j hj
  unfold bitf at this
  rw [← this]
  cases u.testBit j <;> cases u.testBit (j+1) <;> cases u.testBit (j+2) <;> rfl

theorem sol_high (h z u j : ℕ) (hu : Sol h z u) (hj : h + 2 ≤ j) : u.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hu.1 (Nat.pow_le_pow_right (by norm_num) hj))

theorem sol_down (h z u u' : ℕ) (hu : Sol h z u) (hu' : Sol h z u') (p : ℕ) (hp : p ≤ h)
    (e0 : u.testBit p = u'.testBit p) (e1 : u.testBit (p+1) = u'.testBit (p+1)) :
    ∀ k j, j + k = p + 1 → u.testBit j = u'.testBit j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj
    rcases k with _ | _ | k
    · have hjp : j = p + 1 := by omega
      rw [hjp]; exact e1
    · have hjp : j = p := by omega
      rw [hjp]; exact e0
    · rw [sol_rec h z u j (j+1) (j+2) hu (by omega) rfl rfl,
        sol_rec h z u' j (j+1) (j+2) hu' (by omega) rfl rfl,
        ih (k+1) (by omega) (j+1) (by omega), ih k (by omega) (j+2) (by omega)]

theorem delta_rec (h z X Y j a b : ℕ) (hX : Sol h z X) (hY : Sol h z Y) (hj : j < h)
    (ha : a = j + 1) (hb : b = j + 2) :
    (X ^^^ Y).testBit j
      = xor ((X ^^^ Y).testBit b && !(xor (X.testBit a) ((X ^^^ Y).testBit a)))
          ((X ^^^ Y).testBit a && X.testBit b) := by
  subst ha hb
  simp only [Nat.testBit_xor]
  rw [sol_rec h z X j (j+1) (j+2) hX hj rfl rfl, sol_rec h z Y j (j+1) (j+2) hY hj rfl rfl]
  cases z.testBit j <;> cases X.testBit (j+1) <;> cases X.testBit (j+2) <;>
    cases Y.testBit (j+1) <;> cases Y.testBit (j+2) <;> rfl

theorem lane_gen (h z X Y t r : ℕ) (hX : Sol h z X) (hY : Sol h z Y) (ht : t ≤ h)
    (d0 : (X ^^^ Y).testBit t = true) (d1 : (X ^^^ Y).testBit (t+1) = false)
    (x1 : X.testBit (t+1) = false) (hr : RunA t z r) :
    ∀ i p, p + 2*i = t → ((X ^^^ Y).testBit p = decide (i ≤ r)) ∧
      (∀ q, q + 1 = p → (X ^^^ Y).testBit q = false ∧ (i ≤ r → X.testBit q = z.testBit q)) := by
  obtain ⟨hr1, hr2, hr3⟩ := hr
  intro i
  induction i with
  | zero =>
    intro p hp
    have hpt : p = t := by omega
    refine ⟨by rw [hpt, d0]; simp, ?_⟩
    intro q hq
    constructor
    · rw [delta_rec h z X Y q t (t+1) hX hY (by omega) (by omega) (by omega), d0, d1, x1]
      simp
    · intro _
      rw [sol_rec h z X q t (t+1) hX (by omega) (by omega) (by omega), x1]
      simp
  | succ i ih =>
    intro p hp
    obtain ⟨ihA, ihB⟩ := ih (p+2) (by omega)
    obtain ⟨ihB1, ihB2⟩ := ihB (p+1) (by omega)
    have hA : (X ^^^ Y).testBit p = decide (i + 1 ≤ r) := by
      rw [delta_rec h z X Y p (p+1) (p+2) hX hY (by omega) rfl rfl, ihA, ihB1]
      rcases Nat.lt_trichotomy i r with hir | hir | hir
      · have e1 := ihB2 (by omega)
        have e2 := hr2 i hir
        have e3 : t - 1 - 2*i = p + 1 := by omega
        rw [e3] at e2
        rw [e1, e2, decide_eq_true (by omega : i ≤ r), decide_eq_true (by omega : i + 1 ≤ r)]
        simp
      · have e1 := ihB2 (by omega)
        have e2 := hr3 (by omega)
        have e3 : t - 1 - 2*r = p + 1 := by omega
        rw [e3] at e2
        rw [e1, e2, decide_eq_true (by omega : i ≤ r), decide_eq_false (by omega : ¬ i + 1 ≤ r)]
        simp
      · rw [decide_eq_false (by omega : ¬ i ≤ r), decide_eq_false (by omega : ¬ i + 1 ≤ r)]
        simp
    refine ⟨hA, ?_⟩
    intro q hq
    have hB : (X ^^^ Y).testBit q = false := by
      rw [delta_rec h z X Y q p (p+1) hX hY (by omega) (by omega) (by omega), ihB1, hA]
      by_cases hir : i + 1 ≤ r
      · have e1 := ihB2 (by omega)
        have e2 := hr2 i (by omega)
        have e3 : t - 1 - 2*i = p + 1 := by omega
        rw [e3] at e2
        rw [e1, e2]
        simp
      · rw [decide_eq_false hir]
        simp
    refine ⟨hB, ?_⟩
    intro hir
    have e1 := ihB2 (by omega)
    have e2 := hr2 i (by omega)
    have e3 : t - 1 - 2*i = p + 1 := by omega
    rw [e3] at e2
    rw [sol_rec h z X q p (p+1) hX (by omega) (by omega) (by omega), e1, e2]
    simp

theorem lane_bits (h z X Y t r : ℕ) (hX : Sol h z X) (hY : Sol h z Y) (ht : t ≤ h)
    (d0 : (X ^^^ Y).testBit t = true) (d1 : (X ^^^ Y).testBit (t+1) = false)
    (x1 : X.testBit (t+1) = false) (hr : RunA t z r) (j : ℕ) (hj : j ≤ t) :
    (X ^^^ Y).testBit j = (mask t r).testBit j := by
  have hr' := hr.1
  have key := lane_gen h z X Y t r hX hY ht d0 d1 x1 hr
  rw [testBit_mask t r j (by omega)]
  rcases Nat.mod_two_eq_zero_or_one (t - j) with he | he
  · rw [(key ((t - j)/2) j (by omega)).1]
    exact decide_eq_decide.mpr ⟨fun hh => ⟨hj, he, hh⟩, fun hh => hh.2.2⟩
  · rw [((key ((t - j - 1)/2) (j+1) (by omega)).2 j rfl).1]
    symm
    apply decide_eq_false
    omega

theorem sol_unique (h z u u' : ℕ) (hu : Sol h z u) (hu' : Sol h z u')
    (e0 : u.testBit h = u'.testBit h) (e1 : u.testBit (h+1) = u'.testBit (h+1)) : u = u' := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j ≤ h + 1
  · exact sol_down h z u u' hu hu' h le_rfl e0 e1 (h + 1 - j) j (by omega)
  · rw [sol_high h z u j hu (by omega), sol_high h z u' j hu' (by omega)]

theorem sol_top (h z u u' : ℕ) (hh : 0 < h) (hu : Sol h z u) (hu' : Sol h z u')
    (t : u.testBit h = true) (t' : u'.testBit h = true)
    (ne : u.testBit (h+1) ≠ u'.testBit (h+1)) : u ^^^ u' = 2^(h+1) := by
  have e0 : u.testBit (h-1) = u'.testBit (h-1) := by
    rw [sol_rec h z u (h-1) h (h+1) hu (by omega) (by omega) (by omega),
      sol_rec h z u' (h-1) h (h+1) hu' (by omega) (by omega) (by omega), t, t']
    simp
  have e1 : u.testBit (h-1+1) = u'.testBit (h-1+1) := by
    have e : h - 1 + 1 = h := by omega
    rw [e, t, t']
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy j (h+1) with hj | hj | hj
  · rw [sol_down h z u u' hu hu' (h-1) (by omega) e0 e1 (h - j) j (by omega),
      decide_eq_false (by omega : ¬ h + 1 = j)]
    simp
  · rw [hj]
    revert ne
    cases u.testBit (h+1) <;> cases u'.testBit (h+1) <;> simp
  · rw [sol_high h z u j hu (by omega), sol_high h z u' j hu' (by omega),
      decide_eq_false (by omega : ¬ h + 1 = j)]
    simp

theorem lane_a (h z r X Y : ℕ) (hh : 0 < h) (hX : Sol h z X) (hY : Sol h z Y)
    (x0 : X.testBit h = false) (x1 : X.testBit (h+1) = false)
    (y0 : Y.testBit h = true) (y1 : Y.testBit (h+1) = false)
    (hr : RunA h z r) : X ^^^ Y = mask h r := by
  have _ := hh
  have d0 : (X ^^^ Y).testBit h = true := by rw [Nat.testBit_xor, x0, y0]; rfl
  have d1 : (X ^^^ Y).testBit (h+1) = false := by rw [Nat.testBit_xor, x1, y1]; rfl
  have hr' := hr.1
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j ≤ h
  · exact lane_bits h z X Y h r hX hY le_rfl d0 d1 x1 hr j hj
  · rw [testBit_mask h r j (by omega)]
    have hd : (X ^^^ Y).testBit j = false := by
      by_cases hj1 : j = h + 1
      · rw [hj1]; exact d1
      · rw [Nat.testBit_xor, sol_high h z X j hX (by omega), sol_high h z Y j hY (by omega)]
        rfl
    rw [hd]
    symm
    apply decide_eq_false
    omega

theorem lane_c (h z s X Z : ℕ) (hh : 0 < h) (hX : Sol h z X) (hZ : Sol h z Z)
    (x0 : X.testBit h = false) (x1 : X.testBit (h+1) = false)
    (z0 : Z.testBit h = false) (z1 : Z.testBit (h+1) = true)
    (hs : RunC h z s) : X ^^^ Z = 2^(h+1) ^^^ mask (h-1) s := by
  have hr : RunA (h-1) z s := by
    obtain ⟨a, b, c⟩ := hs
    refine ⟨a, fun i hi => ?_, fun hi => ?_⟩
    · have hb := b i hi
      have e : h - 1 - 1 - 2*i = h - 2 - 2*i := by omega
      rw [e]; exact hb
    · have hc := c hi
      have e : h - 1 - 1 - 2*s = h - 2 - 2*s := by omega
      rw [e]; exact hc
  have hr' := hr.1
  have dh1 : (X ^^^ Z).testBit (h+1) = true := by rw [Nat.testBit_xor, x1, z1]; rfl
  have dh : (X ^^^ Z).testBit h = false := by rw [Nat.testBit_xor, x0, z0]; rfl
  have d0 : (X ^^^ Z).testBit (h-1) = true := by
    rw [delta_rec h z X Z (h-1) h (h+1) hX hZ (by omega) (by omega) (by omega), dh1, dh, x0]
    rfl
  have eh : h - 1 + 1 = h := by omega
  have d1 : (X ^^^ Z).testBit (h-1+1) = false := by rw [eh]; exact dh
  have x1' : X.testBit (h-1+1) = false := by rw [eh]; exact x0
  apply Nat.eq_of_testBit_eq
  intro j
  have e : (2^(h+1) ^^^ mask (h-1) s).testBit j
      = xor (decide (h+1 = j)) ((mask (h-1) s).testBit j) := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rw [e]
  by_cases hj : j ≤ h - 1
  · rw [lane_bits h z X Z (h-1) s hX hZ (by omega) d0 d1 x1' hr j hj,
      decide_eq_false (by omega : ¬ h + 1 = j)]
    simp
  · have hm : (mask (h-1) s).testBit j = false := by
      rw [testBit_mask (h-1) s j (by omega)]
      apply decide_eq_false
      omega
    rw [hm]
    by_cases hj0 : j = h
    · rw [hj0, dh, decide_eq_false (by omega : ¬ h + 1 = h)]
      rfl
    · by_cases hj1 : j = h + 1
      · rw [hj1, dh1]
        simp
      · rw [Nat.testBit_xor, sol_high h z X j hX (by omega), sol_high h z Z j hZ (by omega),
          decide_eq_false (by omega : ¬ h + 1 = j)]

def fiber (h z : ℕ) : Finset ℕ := (Finset.range (2^(h+2))).filter (fun u => reply h u = z)

def six (h r s : ℕ) : List ℕ :=
  [mask h r, 2^(h+1), mask h r ^^^ 2^(h+1), 2^(h+1) ^^^ mask (h-1) s,
    (mask h r ^^^ 2^(h+1)) ^^^ mask (h-1) s, mask h r ^^^ mask (h-1) s]

theorem reply_lt (h u : ℕ) : reply h u < 2^h := sum_pow_lt h (bitf u)

theorem reply_eq_iff (h u z : ℕ) (hz : z < 2^h) :
    reply h u = z ↔ ∀ j < h, bitf u j = z.testBit j := by
  constructor
  · intro e j hj
    have h1 := testBit_sum_pow h (bitf u) j
    rw [← e]
    unfold reply
    rw [h1]
    simp [hj]
  · intro hb
    apply Nat.eq_of_testBit_eq
    intro j
    unfold reply
    rw [testBit_sum_pow]
    by_cases hj : j < h
    · simp [hj, hb j hj]
    · have h2 : z.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)))
      simp [hj, h2]

theorem mem_fiber {h z u : ℕ} (hz : z < 2^h) : u ∈ fiber h z ↔ Sol h z u := by
  unfold fiber Sol
  rw [Finset.mem_filter, Finset.mem_range, reply_eq_iff h u z hz]

theorem card_fiber_le {h z : ℕ} (hz : z < 2^h) : (fiber h z).card ≤ 4 := by
  have h1 : (fiber h z).card ≤ (Finset.univ : Finset (Bool × Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun u => (u.testBit h, u.testBit (h+1)))
    · intro u _; exact Finset.mem_univ _
    · intro u hu u2 hu2 e
      have e2 : u.testBit h = u2.testBit h ∧ u.testBit (h+1) = u2.testBit (h+1) := by
        simpa using e
      exact sol_unique h z u u2 ((mem_fiber hz).mp (Finset.mem_coe.mp hu))
        ((mem_fiber hz).mp (Finset.mem_coe.mp hu2)) e2.1 e2.2
  simpa using h1

theorem card_fiber {h z : ℕ} (hz : z < 2^h) : (fiber h z).card = 4 := by
  have total : (Finset.range (2^(h+2))).card = ∑ y ∈ Finset.range (2^h), (fiber h y).card :=
    Finset.card_eq_sum_card_fiberwise (fun u _ => Finset.mem_range.mpr (reply_lt h u))
  have hle : ∀ y ∈ Finset.range (2^h), (fiber h y).card ≤ 4 :=
    fun y hy => card_fiber_le (Finset.mem_range.mp hy)
  have hsum : ∑ y ∈ Finset.range (2^h), (fiber h y).card = ∑ _y ∈ Finset.range (2^h), 4 := by
    rw [← total]
    simp only [Finset.card_range, Finset.sum_const, smul_eq_mul]
    ring
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum z (Finset.mem_range.mpr hz)

theorem exists_tail {h z : ℕ} (hz : z < 2^h) (t0 t1 : Bool) :
    ∃ u, Sol h z u ∧ u.testBit h = t0 ∧ u.testBit (h+1) = t1 := by
  have hinj : Set.InjOn (fun u : ℕ => (u.testBit h, u.testBit (h+1))) (fiber h z : Set ℕ) := by
    intro u hu u2 hu2 e
    have e2 : u.testBit h = u2.testBit h ∧ u.testBit (h+1) = u2.testBit (h+1) := by
      simpa using e
    exact sol_unique h z u u2 ((mem_fiber hz).mp (Finset.mem_coe.mp hu))
      ((mem_fiber hz).mp (Finset.mem_coe.mp hu2)) e2.1 e2.2
  have hc : ((fiber h z).image (fun u : ℕ => (u.testBit h, u.testBit (h+1)))).card
      = (Finset.univ : Finset (Bool × Bool)).card := by
    rw [Finset.card_image_of_injOn hinj, card_fiber hz]
    simp
  have huniv := Finset.eq_univ_of_card _ hc
  have hm : (t0, t1) ∈ (fiber h z).image (fun u : ℕ => (u.testBit h, u.testBit (h+1))) := by
    rw [huniv]; exact Finset.mem_univ _
  obtain ⟨u, hu, e⟩ := Finset.mem_image.mp hm
  have e2 : u.testBit h = t0 ∧ u.testBit (h+1) = t1 := by simpa using e
  exact ⟨u, (mem_fiber hz).mp hu, e2.1, e2.2⟩

theorem xor_cancel_left (p q : ℕ) : p ^^^ (p ^^^ q) = q := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases p.testBit i <;> cases q.testBit i <;> rfl

theorem six_diffs (X Y Z W a b c : ℕ) (eA : X ^^^ Y = a) (eB : Y ^^^ W = b)
    (eC : X ^^^ Z = b ^^^ c) :
    X ^^^ W = a ^^^ b ∧ Y ^^^ Z = (a ^^^ b) ^^^ c ∧ Z ^^^ W = a ^^^ c := by
  subst eA eB
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply Nat.eq_of_testBit_eq
    intro i
    have h3 := congrArg (fun t : ℕ => t.testBit i) eC
    simp only [Nat.testBit_xor] at h3 ⊢
    revert h3
    cases X.testBit i <;> cases Y.testBit i <;> cases Z.testBit i <;> cases W.testBit i <;>
      cases c.testBit i <;> simp

theorem pairs_iff (h z r s : ℕ) (hh : 0 < h) (hz : z < 2^h) (hr : RunA h z r)
    (hs : RunC h z s) (P : ℕ → Prop) :
    (∀ u ∈ fiber h z, ∀ u2 ∈ fiber h z, u ≠ u2 → P (u ^^^ u2)) ↔ ∀ v ∈ six h r s, P v := by
  obtain ⟨X, hX, x0, x1⟩ := exists_tail hz false false
  obtain ⟨Y, hY, y0, y1⟩ := exists_tail hz true false
  obtain ⟨Z, hZ, z0, z1⟩ := exists_tail hz false true
  obtain ⟨W, hW, w0, w1⟩ := exists_tail hz true true
  have eA : X ^^^ Y = mask h r := lane_a h z r X Y hh hX hY x0 x1 y0 y1 hr
  have eB : Y ^^^ W = 2^(h+1) :=
    sol_top h z Y W hh hY hW y0 w0 (by rw [y1, w1]; exact Bool.false_ne_true)
  have eC : X ^^^ Z = 2^(h+1) ^^^ mask (h-1) s := lane_c h z s X Z hh hX hZ x0 x1 z0 z1 hs
  obtain ⟨eXW, eYZ, eZW⟩ := six_diffs X Y Z W _ _ _ eA eB eC
  have nXY : X ≠ Y := fun e => by rw [e, y0] at x0; exact Bool.noConfusion x0
  have nXZ : X ≠ Z := fun e => by rw [e, z1] at x1; exact Bool.noConfusion x1
  have nXW : X ≠ W := fun e => by rw [e, w0] at x0; exact Bool.noConfusion x0
  have nYZ : Y ≠ Z := fun e => by rw [e, z0] at y0; exact Bool.noConfusion y0
  have nYW : Y ≠ W := fun e => by rw [e, w1] at y1; exact Bool.noConfusion y1
  have nZW : Z ≠ W := fun e => by rw [e, w0] at z0; exact Bool.noConfusion z0
  have fX := (mem_fiber hz).mpr hX
  have fY := (mem_fiber hz).mpr hY
  have fZ := (mem_fiber hz).mpr hZ
  have fW := (mem_fiber hz).mpr hW
  have which : ∀ u ∈ fiber h z, u = X ∨ u = Y ∨ u = Z ∨ u = W := by
    intro u hu
    have su := (mem_fiber hz).mp hu
    rcases Bool.eq_false_or_eq_true (u.testBit h) with t0 | t0 <;>
      rcases Bool.eq_false_or_eq_true (u.testBit (h+1)) with t1 | t1
    · exact Or.inr (Or.inr (Or.inr (sol_unique h z u W su hW (by rw [t0, w0]) (by rw [t1, w1]))))
    · exact Or.inr (Or.inl (sol_unique h z u Y su hY (by rw [t0, y0]) (by rw [t1, y1])))
    · exact Or.inr (Or.inr (Or.inl (sol_unique h z u Z su hZ (by rw [t0, z0]) (by rw [t1, z1]))))
    · exact Or.inl (sol_unique h z u X su hX (by rw [t0, x0]) (by rw [t1, x1]))
  constructor
  · intro H v hv
    simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← eA]; exact H X fX Y fY nXY
    · rw [← eB]; exact H Y fY W fW nYW
    · rw [← eXW]; exact H X fX W fW nXW
    · rw [← eC]; exact H X fX Z fZ nXZ
    · rw [← eYZ]; exact H Y fY Z fZ nYZ
    · rw [← eZW]; exact H Z fZ W fW nZW
  · intro H u hu u2 hu2 hne
    have m1 : mask h r ∈ six h r s := by simp [six]
    have m2 : 2^(h+1) ∈ six h r s := by simp [six]
    have m3 : mask h r ^^^ 2^(h+1) ∈ six h r s := by simp [six]
    have m4 : 2^(h+1) ^^^ mask (h-1) s ∈ six h r s := by simp [six]
    have m5 : (mask h r ^^^ 2^(h+1)) ^^^ mask (h-1) s ∈ six h r s := by simp [six]
    have m6 : mask h r ^^^ mask (h-1) s ∈ six h r s := by simp [six]
    rcases which u hu with e | e | e | e <;> rcases which u2 hu2 with e2 | e2 | e2 | e2 <;>
      subst e <;> subst e2
    · exact absurd rfl hne
    · rw [eA]; exact H _ m1
    · rw [eC]; exact H _ m4
    · rw [eXW]; exact H _ m3
    · rw [Nat.xor_comm, eA]; exact H _ m1
    · exact absurd rfl hne
    · rw [eYZ]; exact H _ m5
    · rw [eB]; exact H _ m2
    · rw [Nat.xor_comm, eC]; exact H _ m4
    · rw [Nat.xor_comm, eYZ]; exact H _ m5
    · exact absurd rfl hne
    · rw [eZW]; exact H _ m6
    · rw [Nat.xor_comm, eXW]; exact H _ m3
    · rw [Nat.xor_comm, eB]; exact H _ m2
    · rw [Nat.xor_comm, eZW]; exact H _ m6
    · exact absurd rfl hne

theorem good_iff (h z r s : ℕ) (hh : 0 < h) (hz : z < 2^h) (hr : RunA h z r)
    (hs : RunC h z s) (Q : List (ℕ × ℕ)) (hQ : ∀ p ∈ Q, p.2 < h) (D : ℕ) :
    (((fiber h z).product (fiber h z)).filter
        (fun uv => uv.1 ≠ uv.2 ∧ dist Q uv.1 uv.2 < D)).card = 0 ↔
      (six h r s).all (fun v => decide (D ≤ wt Q v)) = true := by
  have hd : ∀ u ∈ fiber h z, ∀ u2 ∈ fiber h z, dist Q u u2 = wt Q (u ^^^ u2) := by
    intro u hu u2 hu2
    apply dist_eq_wt h Q hQ
    intro j hj
    rw [((mem_fiber hz).mp hu).2 j hj, ((mem_fiber hz).mp hu2).2 j hj]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff, List.all_eq_true]
  constructor
  · intro H v hv
    rw [decide_eq_true_eq]
    refine (pairs_iff h z r s hh hz hr hs (fun v => D ≤ wt Q v)).mp ?_ v hv
    intro u hu u2 hu2 hne
    have h1 := @H (u, u2) (Finset.mem_product.mpr ⟨hu, hu2⟩)
    rw [← hd u hu u2 hu2]
    by_contra hlt
    exact h1 ⟨hne, not_le.mp hlt⟩
  · intro H uv hm hbad
    obtain ⟨hu, hu2⟩ := Finset.mem_product.mp hm
    have h1 := (pairs_iff h z r s hh hz hr hs (fun v => D ≤ wt Q v)).mpr
      (fun v hv => by have h2 := H v hv; rwa [decide_eq_true_eq] at h2) uv.1 hu uv.2 hu2 hbad.1
    rw [← hd uv.1 hu uv.2 hu2] at h1
    exact absurd hbad.2 (not_lt.mpr h1)

theorem exists_runA (h z : ℕ) : ∃ r, RunA h z r := by
  classical
  by_cases hex : ∃ i, i < h/2 ∧ z.testBit (h-1-2*i) = true
  · have hsp := Nat.find_spec hex
    refine ⟨Nat.find hex, le_of_lt hsp.1, ?_, fun _ => hsp.2⟩
    intro i hi
    have hmin := Nat.find_min hex hi
    have hi2 : i < h/2 := lt_trans hi hsp.1
    by_contra hne
    exact hmin ⟨hi2, by simpa using hne⟩
  · refine ⟨h/2, le_rfl, ?_, fun hlt => absurd hlt (lt_irrefl _)⟩
    intro i hi
    by_contra hne
    exact hex ⟨i, hi, by simpa using hne⟩

theorem exists_runC (h z : ℕ) : ∃ s, RunC h z s := by
  classical
  by_cases hex : ∃ i, i < (h-1)/2 ∧ z.testBit (h-2-2*i) = true
  · have hsp := Nat.find_spec hex
    refine ⟨Nat.find hex, le_of_lt hsp.1, ?_, fun _ => hsp.2⟩
    intro i hi
    have hmin := Nat.find_min hex hi
    have hi2 : i < (h-1)/2 := lt_trans hi hsp.1
    by_contra hne
    exact hmin ⟨hi2, by simpa using hne⟩
  · refine ⟨(h-1)/2, le_rfl, ?_, fun hlt => absurd hlt (lt_irrefl _)⟩
    intro i hi
    by_contra hne
    exact hex ⟨i, hi, by simpa using hne⟩

theorem runA_unique (h z r r2 : ℕ) (a : RunA h z r) (b : RunA h z r2) : r = r2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := a.2.2 (lt_of_lt_of_le hlt b.1)
    have h2 := b.2.1 r hlt
    rw [h1] at h2
    exact Bool.noConfusion h2
  · have h1 := b.2.2 (lt_of_lt_of_le hlt a.1)
    have h2 := a.2.1 r2 hlt
    rw [h1] at h2
    exact Bool.noConfusion h2

theorem runC_unique (h z s s2 : ℕ) (a : RunC h z s) (b : RunC h z s2) : s = s2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := a.2.2 (lt_of_lt_of_le hlt b.1)
    have h2 := b.2.1 s hlt
    rw [h1] at h2
    exact Bool.noConfusion h2
  · have h1 := b.2.2 (lt_of_lt_of_le hlt a.1)
    have h2 := a.2.1 s2 hlt
    rw [h1] at h2
    exact Bool.noConfusion h2

noncomputable def rOf (h z : ℕ) : ℕ := Classical.choose (exists_runA h z)

noncomputable def sOf (h z : ℕ) : ℕ := Classical.choose (exists_runC h z)

theorem rOf_spec (h z : ℕ) : RunA h z (rOf h z) := Classical.choose_spec (exists_runA h z)

theorem sOf_spec (h z : ℕ) : RunC h z (sOf h z) := Classical.choose_spec (exists_runC h z)

open Classical in
theorem sum_eq (h : ℕ) (hh : 0 < h) (C : ℕ → ℕ → Prop) [inst : ∀ r s, Decidable (C r s)] :
    (∑ r ∈ Finset.range (h/2+1), ∑ s ∈ Finset.range ((h-1)/2+1),
        if C r s then 2^(h-(min (r+1) (h/2) + min (s+1) ((h-1)/2))) else 0)
      = ((Finset.range (2^h)).filter (fun z => C (rOf h z) (sOf h z))).card := by
  have step1 : ((Finset.range (2^h)).filter (fun z => C (rOf h z) (sOf h z))).card
      = ∑ r ∈ Finset.range (h/2+1),
        (((Finset.range (2^h)).filter (fun z => C (rOf h z) (sOf h z))).filter
          (fun z => rOf h z = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun z _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (rOf_spec h z).1))
  rw [step1]
  apply Finset.sum_congr rfl
  intro r hr
  have step2 : (((Finset.range (2^h)).filter (fun z => C (rOf h z) (sOf h z))).filter
        (fun z => rOf h z = r)).card
      = ∑ s ∈ Finset.range ((h-1)/2+1),
        ((((Finset.range (2^h)).filter (fun z => C (rOf h z) (sOf h z))).filter
          (fun z => rOf h z = r)).filter (fun z => sOf h z = s)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun z _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (sOf_spec h z).1))
  rw [step2]
  apply Finset.sum_congr rfl
  intro s hs
  have hr2 : r ≤ h/2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hs2 : s ≤ (h-1)/2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  by_cases hc : C r s
  · rw [if_pos hc, ← count_type h r s hh hr2 hs2]
    congr 1
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, ha, hc2⟩
      have e1 : rOf h z = r := runA_unique h z _ _ (rOf_spec h z) ha
      have e2 : sOf h z = s := runC_unique h z _ _ (sOf_spec h z) hc2
      exact ⟨⟨⟨hz, by rw [e1, e2]; exact hc⟩, e1⟩, e2⟩
    · rintro ⟨⟨⟨hz, _⟩, e1⟩, e2⟩
      exact ⟨hz, e1 ▸ rOf_spec h z, e2 ▸ sOf_spec h z⟩
  · rw [if_neg hc]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz e2
    have hz2 := Finset.mem_filter.mp hz
    have hz3 := Finset.mem_filter.mp hz2.1
    apply hc
    have h4 := hz3.2
    rw [hz2.2, e2] at h4
    exact h4

theorem main (h : ℕ) (hh : 0 < h) (menu : Finset (List (ℕ × ℕ))) (b D target : ℕ)
    (hmenu : ∀ Q ∈ menu, ∀ p ∈ Q, p.2 < h) :
    (∃ pick : ℕ → List (ℕ × ℕ), (Finset.range (2^h)).image pick ⊆ menu ∧
      ((Finset.range (2^h)).image pick).card ≤ b ∧
      target ≤ ((Finset.range (2^h)).filter (fun z =>
        (((fiber h z).product (fiber h z)).filter
          (fun uv => uv.1 ≠ uv.2 ∧ dist (pick z) uv.1 uv.2 < D)).card = 0)).card) ↔
    ∃ bank : Finset (List (ℕ × ℕ)), bank.Nonempty ∧ bank ⊆ menu ∧ bank.card ≤ b ∧
      target ≤ ∑ r ∈ Finset.range (h/2+1), ∑ s ∈ Finset.range ((h-1)/2+1),
        if (bank.filter (fun Q => (six h r s).all (fun v => decide (D ≤ wt Q v)) = true)).Nonempty
        then 2^(h-(min (r+1) (h/2) + min (s+1) ((h-1)/2))) else 0 := by
  classical
  have hgood : ∀ z ∈ Finset.range (2^h), ∀ Q ∈ menu,
      ((((fiber h z).product (fiber h z)).filter
          (fun uv => uv.1 ≠ uv.2 ∧ dist Q uv.1 uv.2 < D)).card = 0 ↔
        (six h (rOf h z) (sOf h z)).all (fun v => decide (D ≤ wt Q v)) = true) :=
    fun z hz Q hQ => good_iff h z _ _ hh (Finset.mem_range.mp hz) (rOf_spec h z) (sOf_spec h z)
      Q (hmenu Q hQ) D
  constructor
  · rintro ⟨pick, hsub, hcard, htar⟩
    refine ⟨(Finset.range (2^h)).image pick, ?_, hsub, hcard, le_trans htar ?_⟩
    · exact ⟨pick 0, Finset.mem_image_of_mem pick (Finset.mem_range.mpr (by positivity))⟩
    · rw [sum_eq h hh (fun r s => (((Finset.range (2^h)).image pick).filter
          (fun Q => (six h r s).all (fun v => decide (D ≤ wt Q v)) = true)).Nonempty)]
      apply Finset.card_le_card
      intro z hzm
      have hz2 := Finset.mem_filter.mp hzm
      refine Finset.mem_filter.mpr ⟨hz2.1, pick z, ?_⟩
      have hin : pick z ∈ (Finset.range (2^h)).image pick := Finset.mem_image_of_mem pick hz2.1
      exact Finset.mem_filter.mpr ⟨hin, (hgood z hz2.1 (pick z) (hsub hin)).mp hz2.2⟩
  · rintro ⟨bank, ⟨Q0, hQ0⟩, hsub, hcard, htar⟩
    let C : ℕ → ℕ → Prop := fun r s =>
      (bank.filter (fun Q => (six h r s).all (fun v => decide (D ≤ wt Q v)) = true)).Nonempty
    let pick : ℕ → List (ℕ × ℕ) := fun z =>
      if hc : C (rOf h z) (sOf h z) then hc.choose else Q0
    have hpick : ∀ z, pick z ∈ bank := by
      intro z
      by_cases hc : C (rOf h z) (sOf h z)
      · have e : pick z = hc.choose := dif_pos hc
        rw [e]; exact (Finset.mem_filter.mp hc.choose_spec).1
      · have e : pick z = Q0 := dif_neg hc
        rw [e]; exact hQ0
    have himg : (Finset.range (2^h)).image pick ⊆ bank := by
      intro Q hQ
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hQ
      exact hpick z
    refine ⟨pick, himg.trans hsub, (Finset.card_le_card himg).trans hcard, le_trans htar ?_⟩
    rw [sum_eq h hh C]
    apply Finset.card_le_card
    intro z hzm
    have hz2 := Finset.mem_filter.mp hzm
    have hc : C (rOf h z) (sOf h z) := hz2.2
    have e : pick z = hc.choose := dif_pos hc
    refine Finset.mem_filter.mpr ⟨hz2.1, ?_⟩
    rw [e]
    exact (hgood z hz2.1 _ (hsub (Finset.mem_filter.mp hc.choose_spec).1)).mpr
      (Finset.mem_filter.mp hc.choose_spec).2

end PEqualNP.Outside.L_meta_33689_aux

theorem PEqualNP.Outside.L_meta_33689 : (∀ h : Nat, 0 < h →
  let bit := fun (u j : Nat) =>
    xor (u.testBit j) (!(u.testBit (j+1)) && u.testBit (j+2))
  let reply := fun u : Nat =>
    ∑ j ∈ Finset.range h, if bit u j then 2^j else 0
  let fiber := fun z : Nat =>
    (Finset.range (2^(h+2))).filter (fun u => reply u = z)
  let dist := fun (Q : List (Nat × Nat)) (u v : Nat) =>
    (Q.filter (fun p => bit (u ^^^ p.1) p.2 != bit (v ^^^ p.1) p.2)).length
  let mask := fun (top r : Nat) => ∑ i ∈ Finset.range (r+1), 2^(top-2*i)
  let six := fun (r s : Nat) =>
    let a := mask h r
    let b := 2^(h+1)
    let c := mask (h-1) s
    [a, b, a ^^^ b, b ^^^ c, (a ^^^ b) ^^^ c, a ^^^ c]
  let wt := fun (Q : List (Nat × Nat)) (v : Nat) =>
    (Q.filter (fun p => xor
      (v.testBit (p.2+1) && p.1.testBit (p.2+2))
      (v.testBit (p.2+2) && p.1.testBit (p.2+1)))).length
  let replies := Finset.range (2^h)
  let m := h/2
  let n := (h-1)/2
  ∀ (menu : Finset (List (Nat × Nat))) (b D target : Nat),
    (∀ Q ∈ menu, ∀ p ∈ Q, p.2 < h) →
    let good := fun (z : Nat) (Q : List (Nat × Nat)) =>
      (((fiber z).product (fiber z)).filter
        (fun uv => uv.1 ≠ uv.2 ∧ dist Q uv.1 uv.2 < D)).card = 0
    (∃ pick : Nat → List (Nat × Nat), replies.image pick ⊆ menu ∧
      (replies.image pick).card ≤ b ∧
      target ≤ (replies.filter (fun z => good z (pick z))).card) ↔
    ∃ bank : Finset (List (Nat × Nat)), bank.Nonempty ∧ bank ⊆ menu ∧ bank.card ≤ b ∧
      target ≤ ∑ r ∈ Finset.range (m+1), ∑ s ∈ Finset.range (n+1),
        if (bank.filter (fun Q => (six r s).all (fun v => decide (D ≤ wt Q v)) = true)).Nonempty
        then 2^(h-(min (r+1) m + min (s+1) n)) else 0) := by
  intro h hh bit reply fiber dist mask six wt replies m n menu b D target hmenu good
  exact PEqualNP.Outside.L_meta_33689_aux.main h hh menu b D target hmenu
