import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_527

def ms (w : ℕ) (rows : ℕ → ℕ → Bool) (h seed tail : ℕ) : ℕ :=
  ((List.range (2^(w+h))).filter (fun bits =>
      bits % 2^w == seed && (bits >>> h) % 2^w == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*2^w))))).length

theorem cnt_eq (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = ∑ i ∈ Finset.range n, if p i = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    cases h : p n <;> simp [h]

theorem split_sum (a b : ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ Finset.range (a * b), f x = ∑ q ∈ Finset.range b, ∑ r ∈ Finset.range a, f (r + a * q) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [Nat.add_comm]

theorem ms_eq (w : ℕ) (rows : ℕ → ℕ → Bool) (h seed tail : ℕ) :
    ms w rows h seed tail = ∑ x ∈ Finset.range (2^(w+h)),
      if x % 2^w = seed ∧ x / 2^h % 2^w = tail ∧ (∀ i < h, rows i (x / 2^i % (2*2^w)) = true)
      then 1 else 0 := by
  unfold ms
  rw [cnt_eq]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Nat.shiftRight_eq_div_pow, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, and_assoc]

theorem shmod (w h1 i r q : ℕ) (hi : i < h1) :
    (r + 2^(w+h1) * q) / 2^i % (2*2^w) = r / 2^i % (2*2^w) := by
  have e : 2^(w+h1) * q = 2^i * (2*2^w * (2^(h1 - i - 1) * q)) := by
    have hh : w + h1 = i + 1 + w + (h1 - i - 1) := by omega
    rw [hh, pow_add, pow_add, pow_add, pow_one]; ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem ite_split {A B F C E : Prop} [Decidable A] [Decidable B] [Decidable F] [Decidable C]
    [Decidable E] (h : F ↔ C ∧ E) :
    (if A ∧ B ∧ F then 1 else 0 : ℕ) = (if A ∧ C then 1 else 0) * (if B ∧ E then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hE : E <;> simp [hA, hB, hC, hE, h]

theorem ite_A {A B F : Prop} [Decidable A] [Decidable B] [Decidable F] :
    (if A ∧ B ∧ F then 1 else 0 : ℕ) = (if A ∧ F then 1 else 0) * (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hF : F <;> simp [hA, hB, hF]

theorem point (w h1 h2 : ℕ) (rows : ℕ → ℕ → Bool) (seed tail r q : ℕ) :
    (if (r + 2^(w+h1) * q) % 2^w = seed ∧ (r + 2^(w+h1) * q) / 2^(h1+h2) % 2^w = tail ∧
        (∀ i < h1 + h2, rows i ((r + 2^(w+h1) * q) / 2^i % (2*2^w)) = true) then 1 else 0) =
    (if r % 2^w = seed ∧ (∀ i < h1, rows i (r / 2^i % (2*2^w)) = true) then 1 else 0) *
    (if (r / 2^h1 + 2^w * q) / 2^h2 % 2^w = tail ∧
        (∀ j < h2, rows (h1 + j) ((r / 2^h1 + 2^w * q) / 2^j % (2*2^w)) = true) then 1 else 0) := by
  have e0 : (r + 2^(w+h1) * q) % 2^w = r % 2^w := by
    rw [show 2^(w+h1) * q = 2^w * (2^h1 * q) by rw [pow_add]; ring, Nat.add_mul_mod_self_left]
  have e1 : (r + 2^(w+h1) * q) / 2^h1 = r / 2^h1 + 2^w * q := by
    rw [show 2^(w+h1) * q = 2^h1 * (2^w * q) by rw [pow_add]; ring,
      Nat.add_mul_div_left _ _ (by positivity)]
  have e2 : ∀ j, (r + 2^(w+h1) * q) / 2^(h1 + j) = (r / 2^h1 + 2^w * q) / 2^j := by
    intro j; rw [show (2:ℕ)^(h1 + j) = 2^h1 * 2^j from pow_add 2 h1 j, ← Nat.div_div_eq_div_mul, e1]
  have hiff : (∀ i < h1 + h2, rows i ((r + 2^(w+h1) * q) / 2^i % (2*2^w)) = true) ↔
      ((∀ i < h1, rows i (r / 2^i % (2*2^w)) = true) ∧
      (∀ j < h2, rows (h1 + j) ((r / 2^h1 + 2^w * q) / 2^j % (2*2^w)) = true)) := by
    constructor
    · intro H
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · rw [← shmod w h1 i r q hi]; exact H i (by omega)
      · rw [← e2 j]; exact H (h1 + j) (by omega)
    · rintro ⟨H1, H2⟩ i hi
      by_cases hi1 : i < h1
      · rw [shmod w h1 i r q hi1]; exact H1 i hi1
      · obtain ⟨j, rfl⟩ : ∃ j, i = h1 + j := ⟨i - h1, by omega⟩
        rw [e2 j]; exact H2 j (by omega)
  rw [e0, e2 h2]
  exact ite_split hiff

theorem compo (w : ℕ) (rows : ℕ → ℕ → Bool) (h1 h2 seed tail : ℕ) :
    ms w rows (h1 + h2) seed tail =
      ∑ m ∈ Finset.range (2^w), ms w rows h1 seed m * ms w (fun i => rows (h1 + i)) h2 m tail := by
  have hB : ∀ m, m < 2^w → ms w (fun i => rows (h1 + i)) h2 m tail =
      ∑ q ∈ Finset.range (2^h2), if (m + 2^w * q) / 2^h2 % 2^w = tail ∧
          (∀ j < h2, rows (h1 + j) ((m + 2^w*q) / 2^j % (2*2^w)) = true) then 1 else 0 := by
    intro m hm
    rw [ms_eq, pow_add, split_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_eq_single m]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]
      simp only [true_and]
    · intro r hr hne
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      simp only [hne, false_and, ite_false]
    · intro hm'; exact absurd (Finset.mem_range.mpr hm) hm'
  have hA : ∀ m, ms w rows h1 seed m = ∑ r ∈ Finset.range (2^(w+h1)),
      (if r % 2^w = seed ∧ (∀ i < h1, rows i (r / 2^i % (2*2^w)) = true) then 1 else 0) *
      (if r / 2^h1 = m then 1 else 0) := by
    intro m
    rw [ms_eq]
    apply Finset.sum_congr rfl
    intro r hr
    have hlt : r / 2^h1 < 2^w := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; exact Finset.mem_range.mp hr
    rw [Nat.mod_eq_of_lt hlt]
    exact ite_A
  rw [Finset.sum_congr rfl (fun m hm => by rw [hA m, hB m (Finset.mem_range.mp hm), Finset.sum_mul])]
  rw [Finset.sum_comm]
  conv_lhs => rw [ms_eq, show (2:ℕ)^(w + (h1 + h2)) = 2^(w+h1) * 2^h2 by rw [← pow_add, Nat.add_assoc],
    split_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r / 2^h1 < 2^w := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; exact Finset.mem_range.mp hr
  rw [Finset.sum_eq_single (s := Finset.range (2^w)) (r / 2^h1)]
  · rw [if_pos rfl, mul_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact point w h1 h2 rows seed tail r q
  · intro m _ hm
    rw [if_neg (Ne.symm hm), mul_zero, zero_mul]
  · intro hm; exact absurd (Finset.mem_range.mpr hr') hm

theorem ms_zero (w : ℕ) (rows : ℕ → ℕ → Bool) (s m : ℕ) (hs : s < 2^w) :
    ms w rows 0 s m = if s = m then 1 else 0 := by
  rw [ms_eq, Nat.add_zero, Finset.sum_eq_single s]
  · simp [Nat.mod_eq_of_lt hs]
  · intro x hx hne
    simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hx), hne]
  · intro h; exact absurd (Finset.mem_range.mpr hs) h

theorem ms_congr (w : ℕ) (rows rows' : ℕ → ℕ → Bool) (h : ℕ) (H : ∀ i < h, rows i = rows' i)
    (s t : ℕ) : ms w rows h s t = ms w rows' h s t := by
  rw [ms_eq, ms_eq]
  apply Finset.sum_congr rfl
  intro x _
  have hh : (∀ i < h, rows i (x / 2^i % (2*2^w)) = true) ↔
      (∀ i < h, rows' i (x / 2^i % (2*2^w)) = true) := by
    constructor
    · intro H' i hi; rw [← H i hi]; exact H' i hi
    · intro H' i hi; rw [H i hi]; exact H' i hi
  simp only [hh]

def copyR (w : ℕ) : ℕ → Bool := fun x => decide (x % 2 = x / 2^w)

def zeroR (w : ℕ) : ℕ → Bool := fun x => decide (x < 2^w)

theorem bits_eq (n : ℕ) : ∀ x y, x < 2^n → y < 2^n →
    (∀ j < n, x / 2^j % 2 = y / 2^j % 2) → x = y := by
  induction n with
  | zero => intro x y hx hy _; simp at hx hy; omega
  | succ n ih =>
    intro x y hx hy H
    have h0 := H 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have hx' : x / 2 < 2^n := by rw [pow_succ] at hx; omega
    have hy' : y / 2 < 2^n := by rw [pow_succ] at hy; omega
    have : x / 2 = y / 2 := ih (x/2) (y/2) hx' hy' (fun j hj => by
        have := H (j+1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this)
    omega

theorem half_eq_iff (w u u' : ℕ) (hw : 0 < w) (hu : u < 2^w) (hu' : u' < 2^w) :
    (∀ i, 1 ≤ i → i < w → u / 2^i % 2 = u' / 2^i % 2) ↔ u / 2 = u' / 2 := by
  have hp : 2^w = 2 * 2^(w-1) := by rw [← pow_succ']; congr 1; omega
  constructor
  · intro H
    apply bits_eq (w - 1) (u/2) (u'/2) (by omega) (by omega)
    intro j hj
    have := H (j + 1) (by omega) (by omega)
    rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
  · intro H i hi1 hiw
    have : 2^i = 2 * 2^(i-1) := by rw [← pow_succ']; congr 1; omega
    rw [this, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, H]

theorem win0 (w u u' : ℕ) (hu : u < 2^w) :
    (u + 2^w * u') / 2^0 % (2*2^w) = u + 2^w * (u' % 2) := by
  rw [pow_zero, Nat.div_one]
  have e : u + 2^w * u' = (u + 2^w * (u' % 2)) + (2 * 2^w) * (u' / 2) := by
    conv_lhs => rw [← Nat.mod_add_div u' 2]
    ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  rcases Nat.mod_two_eq_zero_or_one u' with h | h <;> rw [h] <;> omega

theorem wini (w u u' i : ℕ) (hu : u < 2^w) (hi1 : 1 ≤ i) (hiw : i < w) :
    copyR w ((u + 2^w * u') / 2^i % (2*2^w)) = decide (u / 2^i % 2 = u' / 2^i % 2) := by
  unfold copyR
  have e1 : 2^w * u' = 2^i * (2 * (2^(w - i - 1) * u')) := by
    have hh : w = i + 1 + (w - i - 1) := by omega
    conv_lhs => rw [hh]
    rw [pow_add, pow_add, pow_one]; ring
  have hy : (u + 2^w * u') / 2^i = u / 2^i + 2 * (2^(w-i-1) * u') := by
    rw [e1, Nat.add_mul_div_left _ _ (by positivity)]
  have hz : (u + 2^w * u') / 2^i / 2^w = u' / 2^i := by
    rw [Nat.div_div_eq_div_mul, mul_comm (2^i) (2^w), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add]
  have m1 : (u + 2^w * u') / 2^i % (2*2^w) % 2 = u / 2^i % 2 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 (2^w)), hy, Nat.add_mul_mod_self_left]
  have m2 : (u + 2^w * u') / 2^i % (2*2^w) / 2^w = u' / 2^i % 2 := by
    rw [mul_comm 2 (2^w), Nat.mod_mul_right_div_self, hz]
  rw [m1, m2]

theorem round (w : ℕ) (hw : 0 < w) (rows : ℕ → ℕ → Bool) (op : ℕ → Bool) (h0 : rows 0 = op)
    (hc : ∀ i, 1 ≤ i → i < w → rows i = copyR w) (u u' : ℕ) (hu : u < 2^w) (hu' : u' < 2^w) :
    ms w rows w u u' = if u / 2 = u' / 2 ∧ op (u + 2^w * (u' % 2)) = true then 1 else 0 := by
  rw [ms_eq, pow_add, split_sum, Finset.sum_eq_single u']
  · rw [Finset.sum_eq_single u]
    · have e1 : (u + 2^w * u') % 2^w = u := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
      have e2 : (u + 2^w * u') / 2^w % 2^w = u' := by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add,
          Nat.mod_eq_of_lt hu']
      have key : (∀ i < w, rows i ((u + 2^w * u') / 2^i % (2*2^w)) = true) ↔
          (u / 2 = u' / 2 ∧ op (u + 2^w * (u' % 2)) = true) := by
        rw [← half_eq_iff w u u' hw hu hu']
        constructor
        · intro H
          refine ⟨fun i hi1 hiw => ?_, ?_⟩
          · have := H i hiw
            rw [hc i hi1 hiw, wini w u u' i hu hi1 hiw] at this
            simpa using this
          · have := H 0 hw
            rwa [h0, win0 w u u' hu] at this
        · rintro ⟨H1, H2⟩ i hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · rwa [h0, win0 w u u' hu]
          · rw [hc i hi0 hi, wini w u u' i hu hi0 hi]
            simpa using H1 i hi0 hi
      rw [e1, e2]
      exact if_congr ⟨fun h => key.mp h.2.2, fun h => ⟨rfl, rfl, key.mpr h⟩⟩ rfl rfl
    · intro r hr hne
      have : (r + 2^w * u') % 2^w = r := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      rw [this, if_neg]
      exact fun h => hne h.1
    · intro h; exact absurd (Finset.mem_range.mpr hu) h
  · intro q hq hne
    apply Finset.sum_eq_zero
    intro r hr
    have : (r + 2^w * q) / 2^w % 2^w = q := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (Finset.mem_range.mp hr),
        zero_add, Nat.mod_eq_of_lt (Finset.mem_range.mp hq)]
    rw [this, if_neg]
    exact fun h => hne h.2.1
  · intro h; exact absurd (Finset.mem_range.mpr hu') h

theorem small (w K : ℕ) : ∀ r, r < 2^(w+K) → (∀ i < K, r / 2^i % (2*2^w) < 2^w) → r < 2^w := by
  induction K with
  | zero => intro r hr _; simpa using hr
  | succ K ih =>
    intro r hr H
    apply ih r _ (fun i hi => H i (by omega))
    have h1 := H K (by omega)
    have h2 : r / 2^K < 2 * 2^w := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc r < 2^(w + (K+1)) := hr
        _ = 2 * 2^w * 2^K := by rw [pow_add, pow_succ]; ring
    rw [Nat.mod_eq_of_lt h2, Nat.div_lt_iff_lt_mul (by positivity)] at h1
    calc r < 2^w * 2^K := h1
      _ = 2^(w+K) := by rw [pow_add]

theorem jblock (w K : ℕ) (rows : ℕ → ℕ → Bool) (hz : ∀ i < K, rows i = zeroR w)
    (hf : ∀ i, K ≤ i → i < K + w → rows i = fun _ => true) (m1 m2 : ℕ) (h1 : m1 < 2^w)
    (h2 : m2 < 2^w) : ms w rows (K + w) m1 m2 = 1 := by
  have hP : 2^w ≤ 2^(w+K) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have emod : ∀ r q, (r + 2^(w+K) * q) % 2^w = r % 2^w := by
    intro r q
    rw [show 2^(w+K) * q = 2^w * (2^K * q) by rw [pow_add]; ring, Nat.add_mul_mod_self_left]
  have ediv : ∀ r q, r < 2^(w+K) → (r + 2^(w+K) * q) / 2^(K+w) = q := by
    intro r q hr
    rw [show K + w = w + K by omega, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr,
      zero_add]
  rw [ms_eq, show (2:ℕ)^(w + (K + w)) = 2^(w+K) * 2^w by rw [← pow_add]; congr 1; omega,
    split_sum, Finset.sum_eq_single m2]
  · rw [Finset.sum_eq_single m1]
    · rw [if_pos]
      refine ⟨by rw [emod, Nat.mod_eq_of_lt h1],
        by rw [ediv _ _ (lt_of_lt_of_le h1 hP), Nat.mod_eq_of_lt h2], ?_⟩
      intro i hi
      by_cases hik : i < K
      · rw [hz i hik]
        unfold zeroR
        rw [decide_eq_true_eq, shmod w K i m1 m2 hik]
        calc m1 / 2^i % (2*2^w) ≤ m1 / 2^i := Nat.mod_le _ _
          _ ≤ m1 := Nat.div_le_self _ _
          _ < 2^w := h1
      · rw [hf i (by omega) hi]
    · intro r hr hne
      rw [if_neg]
      rintro ⟨e1, _, e3⟩
      apply hne
      have hr' : r < 2^(w+K) := Finset.mem_range.mp hr
      have hsmall : r < 2^w := small w K r hr' (fun i hi => by
        have := e3 i (by omega)
        rw [hz i hi] at this
        unfold zeroR at this
        rw [decide_eq_true_eq, shmod w K i r m2 hi] at this
        exact this)
      rw [emod, Nat.mod_eq_of_lt hsmall] at e1
      exact e1
    · intro h; exact absurd (Finset.mem_range.mpr (lt_of_lt_of_le h1 hP)) h
  · intro q hq hne
    apply Finset.sum_eq_zero
    intro r hr
    rw [if_neg]
    rintro ⟨_, e2, _⟩
    apply hne
    rw [ediv _ _ (Finset.mem_range.mp hr), Nat.mod_eq_of_lt (Finset.mem_range.mp hq)] at e2
    exact e2
  · intro h; exact absurd (Finset.mem_range.mpr h2) h

def opv (x y e c : ℕ) : Bool :=
  if x = y then (if x ≤ 1 then decide (e = c) else true)
  else if y < x then (if e = 0 then true else decide (c = 1))
  else (if e = 0 then decide (c = 0) else true)

def stepv (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 = p.2 then (if p.1 ≤ 1 then p else (p.1 - 1, 1))
  else if p.2 < p.1 then (p.1 - p.2, p.2)
  else (p.1, p.2 - p.1)

def cp (e : ℕ) (p : ℕ × ℕ) : ℕ := if e = 0 then p.1 else p.2

theorem opv_step (x y e : ℕ) (he : e < 2) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (if opv x y e 0 = true then cp 0 (stepv (x, y)) else 0) +
    (if opv x y e 1 = true then cp 1 (stepv (x, y)) else 0) = cp e (x, y) := by
  unfold opv stepv cp
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;> split_ifs <;> simp_all <;> omega

theorem iter_inv (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) : ∀ n,
    1 ≤ (stepv^[n] (x, y)).1 ∧ 1 ≤ (stepv^[n] (x, y)).2 ∧
    ((stepv^[n] (x, y)).1 = 1 ∧ (stepv^[n] (x, y)).2 = 1 ∨
      (stepv^[n] (x, y)).1 + (stepv^[n] (x, y)).2 + n ≤ x + y) := by
  intro n
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; omega
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    generalize stepv^[n] (x, y) = p at ih ⊢
    obtain ⟨a, b⟩ := p
    simp only at ih ⊢
    unfold stepv
    split_ifs <;> (try simp only) <;> omega

theorem iter_one (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (n : ℕ) (hn : x + y ≤ n) :
    stepv^[n] (x, y) = (1, 1) := by
  obtain ⟨h1, h2, h3⟩ := iter_inv x y hx hy n
  rcases h3 with h | h
  · exact Prod.ext h.1 h.2
  · omega

theorem comboA (p : ℕ × ℕ) (e : ℕ) (he : e < 2) (hx : 1 ≤ p.1) (hy : 1 ≤ p.2) (k : ℕ) :
    (if k = k ∧ opv p.1 p.2 e 0 = true then 1 else 0) * cp 0 (stepv p) +
    (if k = k ∧ opv p.1 p.2 e 1 = true then 1 else 0) * cp 1 (stepv p) = cp e p := by
  obtain ⟨x, y⟩ := p
  have := opv_step x y e he hx hy
  simp only at hx hy ⊢
  rw [← this]
  by_cases h0 : opv x y e 0 = true <;> by_cases h1 : opv x y e 1 = true <;> simp [h0, h1]

theorem comboB (p : ℕ × ℕ) (e : ℕ) (he : e < 2) (hx : 1 ≤ p.1) (hy : 1 ≤ p.2) (k : ℕ) :
    cp 0 (stepv p) * (if k = k ∧ opv p.1 p.2 e 0 = true then 1 else 0) +
    cp 1 (stepv p) * (if k = k ∧ opv p.1 p.2 e 1 = true then 1 else 0) = cp e p := by
  rw [mul_comm (cp 0 (stepv p)), mul_comm (cp 1 (stepv p))]
  exact comboA p e he hx hy k

def aa (w : ℕ) (a : Fin (2^w) → ℕ) (n : ℕ) : ℕ := if h : n < 2^w then a ⟨n, h⟩ else 1

def st (w : ℕ) (a : Fin (2^w) → ℕ) (k r : ℕ) : ℕ × ℕ :=
  stepv^[r] (aa w a (2*k), aa w a (2*k+1))

def opA (w : ℕ) (a : Fin (2^w) → ℕ) (r : ℕ) : ℕ → Bool := fun x =>
  opv (st w a (x % 2^w / 2) r).1 (st w a (x % 2^w / 2) r).2 (x % 2) (x / 2^w)

def rowsA (w : ℕ) (a : Fin (2^w) → ℕ) : ℕ → ℕ → Bool := fun t =>
  if t % w = 0 then opA w a (t / w) else copyR w

def opB (w : ℕ) (b : Fin (2^w) → ℕ) (N r : ℕ) : ℕ → Bool := fun x =>
  opv (st w b (x % 2^w / 2) (N - 1 - r)).1 (st w b (x % 2^w / 2) (N - 1 - r)).2 (x / 2^w) (x % 2)

def rowsB (w : ℕ) (b : Fin (2^w) → ℕ) (N : ℕ) : ℕ → ℕ → Bool := fun t =>
  if t % w = 0 then opB w b N (t / w) else copyR w

theorem st_succ (w : ℕ) (a : Fin (2^w) → ℕ) (k r : ℕ) : st w a k (r + 1) = stepv (st w a k r) := by
  unfold st; exact Function.iterate_succ_apply' _ _ _

theorem aa_pos (w : ℕ) (a : Fin (2^w) → ℕ) (ha : ∀ i, 0 < a i) (n : ℕ) : 1 ≤ aa w a n := by
  unfold aa; split_ifs with h
  · exact ha _
  · exact le_refl 1

theorem aa_le (w : ℕ) (a : Fin (2^w) → ℕ) (n : ℕ) (hn : n < 2^w) :
    aa w a n ≤ ((List.finRange (2^w)).map a).sum := by
  unfold aa
  rw [dif_pos hn]
  apply List.le_sum_of_mem
  exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩

theorem st_pos (w : ℕ) (a : Fin (2^w) → ℕ) (ha : ∀ i, 0 < a i) (k r : ℕ) :
    1 ≤ (st w a k r).1 ∧ 1 ≤ (st w a k r).2 := by
  obtain ⟨h1, h2, _⟩ := iter_inv _ _ (aa_pos w a ha (2*k)) (aa_pos w a ha (2*k+1)) r
  exact ⟨h1, h2⟩

theorem st_fin (w : ℕ) (a : Fin (2^w) → ℕ) (ha : ∀ i, 0 < a i) (N : ℕ)
    (hN : 2 * ((List.finRange (2^w)).map a).sum ≤ N) (k : ℕ) (hk : 2 * k + 1 < 2^w) :
    st w a k N = (1, 1) := by
  apply iter_one _ _ (aa_pos w a ha _) (aa_pos w a ha _)
  have := aa_le w a (2*k) (by omega)
  have := aa_le w a (2*k+1) hk
  omega

theorem evx (w : ℕ) (hw : 0 < w) (s c : ℕ) (hs : s < 2^w) (hc : c < 2) :
    (s + 2^w * c) % 2^w / 2 = s / 2 ∧ (s + 2^w * c) % 2 = s % 2 ∧ (s + 2^w * c) / 2^w = c := by
  have hp : 2^w = 2 * 2^(w-1) := by rw [← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  · rw [hp, mul_assoc, Nat.add_mul_mod_self_left]
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hs, zero_add]

theorem pair_lt (w : ℕ) (hw : 0 < w) (s : ℕ) (hs : s < 2^w) : 2 * (s / 2) + 1 < 2^w := by
  have hp : 2^w = 2 * 2^(w-1) := by rw [← pow_succ']; congr 1; omega
  omega

theorem pair_sum (D k : ℕ) (hk : 2 * k + 1 < D) (f : ℕ → ℕ) (hf : ∀ v, v / 2 ≠ k → f v = 0) :
    ∑ v ∈ Finset.range D, f v = f (2 * k) + f (2 * k + 1) := by
  apply Finset.sum_eq_add (2*k) (2*k+1) (by omega)
  · intro c _ hc; apply hf; omega
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_range.mpr hk) h

theorem roundA (w : ℕ) (hw : 0 < w) (a : Fin (2^w) → ℕ) (r s v : ℕ) (hs : s < 2^w)
    (hv : v < 2^w) :
    ms w (fun i => rowsA w a (w * r + i)) w s v =
      if s / 2 = v / 2 ∧ opv (st w a (s/2) r).1 (st w a (s/2) r).2 (s % 2) (v % 2) = true
      then 1 else 0 := by
  rw [round w hw _ (opA w a r) ?_ ?_ s v hs hv]
  · obtain ⟨e1, e2, e3⟩ := evx w hw s (v % 2) hs (Nat.mod_lt _ (by norm_num))
    have hop : opA w a r (s + 2^w * (v % 2)) =
        opv (st w a (s/2) r).1 (st w a (s/2) r).2 (s % 2) (v % 2) := by
      simp only [opA]; rw [e1, e2, e3]
    rw [hop]
  · show rowsA w a (w * r + 0) = opA w a r
    unfold rowsA
    rw [Nat.add_zero, if_pos (Nat.mul_mod_right w r), Nat.mul_div_cancel_left r hw]
  · intro i hi1 hiw
    show rowsA w a (w * r + i) = copyR w
    unfold rowsA
    rw [if_neg]
    rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hiw]; omega

theorem roundB (w : ℕ) (hw : 0 < w) (b : Fin (2^w) → ℕ) (N n v z : ℕ) (hv : v < 2^w)
    (hz : z < 2^w) :
    ms w (fun i => rowsB w b N (w * n + i)) w v z =
      if v / 2 = z / 2 ∧ opv (st w b (z/2) (N - 1 - n)).1 (st w b (z/2) (N - 1 - n)).2
        (z % 2) (v % 2) = true then 1 else 0 := by
  rw [round w hw _ (opB w b N n) ?_ ?_ v z hv hz]
  · obtain ⟨e1, e2, e3⟩ := evx w hw v (z % 2) hv (Nat.mod_lt _ (by norm_num))
    have hop : opB w b N n (v + 2^w * (z % 2)) =
        opv (st w b (v/2) (N - 1 - n)).1 (st w b (v/2) (N - 1 - n)).2 (z % 2) (v % 2) := by
      simp only [opB]; rw [e1, e2, e3]
    rw [hop]
    by_cases h : v / 2 = z / 2
    · rw [h]
    · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h h'.1)]
  · show rowsB w b N (w * n + 0) = opB w b N n
    unfold rowsB
    rw [Nat.add_zero, if_pos (Nat.mul_mod_right w n), Nat.mul_div_cancel_left n hw]
  · intro i hi1 hiw
    show rowsB w b N (w * n + i) = copyR w
    unfold rowsB
    rw [if_neg]
    rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hiw]; omega

theorem partA (w : ℕ) (hw : 0 < w) (a : Fin (2^w) → ℕ) (ha : ∀ i, 0 < a i) (N : ℕ)
    (hN : ∀ k, 2 * k + 1 < 2^w → st w a k N = (1, 1)) :
    ∀ n r, r + n = N → ∀ s, s < 2^w →
      ∑ m ∈ Finset.range (2^w), ms w (fun i => rowsA w a (w * r + i)) (w * n) s m =
        cp (s % 2) (st w a (s / 2) r) := by
  intro n
  induction n with
  | zero =>
    intro r hr s hs
    rw [Nat.mul_zero, Finset.sum_congr rfl (fun m _ => ms_zero w _ s m hs), Finset.sum_ite_eq,
      if_pos (Finset.mem_range.mpr hs)]
    rw [Nat.add_zero] at hr
    rw [hr, hN (s / 2) (pair_lt w hw s hs)]
    unfold cp; split_ifs <;> rfl
  | succ n ih =>
    intro r hr s hs
    have e1 : ∀ m, ms w (fun i => rowsA w a (w * r + i)) (w * (n + 1)) s m =
        ∑ v ∈ Finset.range (2^w), ms w (fun i => rowsA w a (w * r + i)) w s v *
          ms w (fun i => rowsA w a (w * (r + 1) + i)) (w * n) v m := by
      intro m
      rw [show w * (n + 1) = w + w * n by ring, compo]
      apply Finset.sum_congr rfl
      intro v _
      rw [ms_congr w _ (fun i => rowsA w a (w * (r + 1) + i)) (w * n)
        (fun i _ => by
          show rowsA w a (w * r + (w + i)) = rowsA w a (w * (r + 1) + i)
          congr 1; ring)]
    rw [Finset.sum_congr rfl (fun m _ => e1 m), Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v hv => by
      rw [ih (r + 1) (by omega) v (Finset.mem_range.mp hv),
        roundA w hw a r s v hs (Finset.mem_range.mp hv)])]
    rw [pair_sum (2^w) (s / 2) (pair_lt w hw s hs)]
    · have q0 : 2 * (s / 2) / 2 = s / 2 := by omega
      have r0 : 2 * (s / 2) % 2 = 0 := by omega
      have q1 : (2 * (s / 2) + 1) / 2 = s / 2 := by omega
      have r1 : (2 * (s / 2) + 1) % 2 = 1 := by omega
      rw [q0, r0, q1, r1, st_succ]
      exact comboA _ _ (Nat.mod_lt _ (by norm_num)) (st_pos w a ha _ _).1 (st_pos w a ha _ _).2 _
    · intro v hv
      rw [if_neg (fun h => hv h.1.symm), zero_mul]

theorem partB (w : ℕ) (hw : 0 < w) (b : Fin (2^w) → ℕ) (hb : ∀ j, 0 < b j) (N : ℕ)
    (hN : ∀ k, 2 * k + 1 < 2^w → st w b k N = (1, 1)) :
    ∀ n, n ≤ N → ∀ z, z < 2^w →
      ∑ m ∈ Finset.range (2^w), ms w (rowsB w b N) (w * n) m z =
        cp (z % 2) (st w b (z / 2) (N - n)) := by
  intro n
  induction n with
  | zero =>
    intro _ z hz
    rw [Nat.mul_zero, Finset.sum_congr rfl (fun m hm => ms_zero w _ m z (Finset.mem_range.mp hm)),
      Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hz), Nat.sub_zero,
      hN (z / 2) (pair_lt w hw z hz)]
    unfold cp; split_ifs <;> rfl
  | succ n ih =>
    intro hn z hz
    have e1 : ∀ m, ms w (rowsB w b N) (w * (n + 1)) m z =
        ∑ v ∈ Finset.range (2^w), ms w (rowsB w b N) (w * n) m v *
          ms w (fun i => rowsB w b N (w * n + i)) w v z := by
      intro m
      rw [show w * (n + 1) = w * n + w by ring, compo]
    rw [Finset.sum_congr rfl (fun m _ => e1 m), Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun v hv => by
      rw [ih (by omega) v (Finset.mem_range.mp hv),
        roundB w hw b N n v z (Finset.mem_range.mp hv) hz])]
    rw [pair_sum (2^w) (z / 2) (pair_lt w hw z hz)]
    · have q0 : 2 * (z / 2) / 2 = z / 2 := by omega
      have r0 : 2 * (z / 2) % 2 = 0 := by omega
      have q1 : (2 * (z / 2) + 1) / 2 = z / 2 := by omega
      have r1 : (2 * (z / 2) + 1) % 2 = 1 := by omega
      rw [q0, r0, q1, r1, show N - n = (N - 1 - n) + 1 by omega,
        show N - (n + 1) = N - 1 - n by omega, st_succ]
      exact comboB _ _ (Nat.mod_lt _ (by norm_num)) (st_pos w b hb _ _).1 (st_pos w b hb _ _).2 _
    · intro v hv
      rw [if_neg (fun h => hv h.1), mul_zero]

theorem cp_st0 (w : ℕ) (a : Fin (2^w) → ℕ) (s : ℕ) : cp (s % 2) (st w a (s / 2) 0) = aa w a s := by
  unfold cp st
  simp only [Function.iterate_zero, id_eq]
  split_ifs with h
  · congr 1; omega
  · congr 1; omega

def tbl (w N K : ℕ) (a b : Fin (2^w) → ℕ) : ℕ → ℕ → Bool := fun t =>
  if t < w * N then rowsA w a t
  else if t < w * N + K then zeroR w
  else if t < w * N + K + w then (fun _ => true)
  else rowsB w b N (t - (w * N + K + w))

theorem main (w : ℕ) (hw : 0 < w) (a b : Fin (2^w) → ℕ) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (L : ℕ)
    (hL : 9*w*(((List.finRange (2^w)).map a).sum + ((List.finRange (2^w)).map b).sum) + 3*w ≤ L) :
    ∃ table : ℕ → ℕ → Bool, ∀ s z : Fin (2^w), ms w table L s.val z.val = a s * b z := by
  obtain ⟨Sa, hSa⟩ : ∃ S, S = ((List.finRange (2^w)).map a).sum := ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ S, S = ((List.finRange (2^w)).map b).sum := ⟨_, rfl⟩
  rw [← hSa, ← hSb] at hL
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * (Sa + Sb) := ⟨_, rfl⟩
  have hLN : w * N + w + w * N ≤ L := by
    have e1 : w * N + w + w * N = 4 * (w * (Sa + Sb)) + w := by rw [hN]; ring
    have e2 : 9 * w * (Sa + Sb) = 9 * (w * (Sa + Sb)) := by ring
    omega
  obtain ⟨K, hK⟩ : ∃ K, K = L - (w * N + w + w * N) := ⟨_, rfl⟩
  have hL' : L = w * N + (K + w + w * N) := by omega
  refine ⟨tbl w N K a b, fun s z => ?_⟩
  have hs := s.isLt
  have hz := z.isLt
  have hNa : ∀ k, 2 * k + 1 < 2^w → st w a k N = (1, 1) := fun k hk =>
    st_fin w a ha N (by rw [← hSa]; omega) k hk
  have hNb : ∀ k, 2 * k + 1 < 2^w → st w b k N = (1, 1) := fun k hk =>
    st_fin w b hb N (by rw [← hSb]; omega) k hk
  have hA : ∀ m, ms w (tbl w N K a b) (w * N) s.val m =
      ms w (fun i => rowsA w a (w * 0 + i)) (w * N) s.val m := by
    intro m
    apply ms_congr
    intro i hi
    show tbl w N K a b i = rowsA w a (w * 0 + i)
    unfold tbl
    rw [if_pos hi, Nat.mul_zero, Nat.zero_add]
  have hJB : ∀ m, m < 2^w → ms w (fun i => tbl w N K a b (w * N + i)) (K + w + w * N) m z.val =
      ∑ m2 ∈ Finset.range (2^w), ms w (rowsB w b N) (w * N) m2 z.val := by
    intro m hm
    rw [compo]
    apply Finset.sum_congr rfl
    intro m2 hm2
    rw [jblock w K _ ?_ ?_ m m2 hm (Finset.mem_range.mp hm2), one_mul]
    · apply ms_congr
      intro i hi
      show tbl w N K a b (w * N + (K + w + i)) = rowsB w b N i
      unfold tbl
      split_ifs <;> first | omega | rfl | (congr 1; omega)
    · intro i hi
      show tbl w N K a b (w * N + i) = zeroR w
      unfold tbl
      split_ifs <;> first | omega | rfl
    · intro i hi1 hi2
      show tbl w N K a b (w * N + i) = fun _ => true
      unfold tbl
      split_ifs <;> first | omega | rfl
  rw [hL', compo]
  rw [Finset.sum_congr rfl (fun m hm => by rw [hA m, hJB m (Finset.mem_range.mp hm)])]
  rw [← Finset.sum_mul]
  rw [partA w hw a ha N hNa N 0 (by omega) s.val hs]
  rw [partB w hw b hb N hNb N le_rfl z.val hz]
  rw [Nat.sub_self, cp_st0, cp_st0]
  unfold aa
  rw [dif_pos hs, dif_pos hz]

end PEqualNP.Outside.L_lib_527

theorem PEqualNP.Outside.L_lib_527 : ∀ w : Nat, 0 < w →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  ∀ a b : Fin D → Nat, (∀ i, 0 < a i) → (∀ j, 0 < b j) →
    let weight := ((List.finRange D).map a).sum + ((List.finRange D).map b).sum
    ∀ L : Nat, 9*w*weight + 3*w ≤ L →
      ∃ table : Rows, ∀ s z : Fin D, mass table L s.val z.val = a s * b z := by
  intro w hw
  exact PEqualNP.Outside.L_lib_527.main w hw
