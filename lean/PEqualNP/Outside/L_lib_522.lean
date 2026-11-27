import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_522_aux

section Cyclic

def next (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def step (n : ℕ) (hn : 0 < n) (i : Fin n) (d : ℕ) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ hn⟩

def off (n : ℕ) (first i : Fin n) : ℕ :=
  (i.val + n - first.val) % n

theorem step_zero (n : ℕ) (hn : 0 < n) (i : Fin n) : step n hn i 0 = i := by
  ext
  simp [step, Nat.mod_eq_of_lt i.isLt]

theorem step_succ (n : ℕ) (hn : 0 < n) (i : Fin n) (d : ℕ) :
    step n hn i (d + 1) = next n hn (step n hn i d) := by
  ext
  simp only [step, next, Nat.mod_add_mod, Nat.add_assoc]

theorem step_n (n : ℕ) (hn : 0 < n) (i : Fin n) : step n hn i n = i := by
  ext
  simp [step, Nat.mod_eq_of_lt i.isLt]

theorem step_add (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    step n hn (step n hn i a) b = step n hn i (a + b) := by
  ext
  simp only [step, Nat.mod_add_mod, Nat.add_assoc]

theorem off_lt (n : ℕ) (hn : 0 < n) (first i : Fin n) : off n first i < n :=
  Nat.mod_lt _ hn

theorem off_step (n : ℕ) (hn : 0 < n) {first : Fin n} {d : ℕ} (hd : d < n) :
    off n first (step n hn first d) = d := by
  dsimp only [off, step]
  by_cases h : first.val + d < n
  · rw [Nat.mod_eq_of_lt h]
    have h1 : first.val + d + n - first.val = d + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · have hlt : first.val + d - n < n := by omega
    have hmod : (first.val + d) % n = first.val + d - n := by
      calc (first.val + d) % n = ((first.val + d - n) + n) % n := by congr 1; omega
        _ = (first.val + d - n) % n := Nat.add_mod_right _ _
        _ = first.val + d - n := Nat.mod_eq_of_lt hlt
    rw [hmod]
    have h1 : first.val + d - n + n - first.val = d := by omega
    rw [h1, Nat.mod_eq_of_lt hd]

theorem step_off (n : ℕ) (hn : 0 < n) (first i : Fin n) : step n hn first (off n first i) = i := by
  ext
  dsimp only [step, off]
  by_cases h : first.val ≤ i.val
  · have h1 : i.val + n - first.val = (i.val - first.val) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - first.val < n)]
    have h2 : first.val + (i.val - first.val) = i.val := by omega
    rw [h2, Nat.mod_eq_of_lt i.isLt]
  · have hlt : i.val + n - first.val < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have h2 : first.val + (i.val + n - first.val) = i.val + n := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem off_eq_zero_iff (n : ℕ) (hn : 0 < n) (first i : Fin n) : off n first i = 0 ↔ i = first := by
  constructor
  · intro h
    have hs := step_off n hn first i
    rw [h, step_zero] at hs
    exact hs.symm
  · rintro rfl
    have h := off_step n hn (first := i) (d := 0) hn
    simpa [step_zero] using h

theorem off_next_of_lt (n : ℕ) (hn : 0 < n) {first i : Fin n} (h : off n first i + 1 < n) :
    off n first (next n hn i) = off n first i + 1 := by
  have heq : next n hn i = step n hn first (off n first i + 1) := by
    rw [step_succ, step_off]
  rw [heq, off_step n hn h]

theorem next_of_off_succ_eq (n : ℕ) (hn : 0 < n) {first i : Fin n} (h : off n first i + 1 = n) :
    next n hn i = first := by
  have heq : next n hn i = step n hn first (off n first i + 1) := by
    rw [step_succ, step_off]
  rw [heq, h, step_n]

theorem next_inj (n : ℕ) (hn : 0 < n) {i j : Fin n} (h : next n hn i = next n hn j) : i = j := by
  have hval : (i.val + 1) % n = (j.val + 1) % n := congrArg Fin.val h
  ext
  by_cases hi : i.val + 1 < n <;> by_cases hj : j.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hval; omega
  · have hje : j.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt hi, hje, Nat.mod_self] at hval; omega
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self, Nat.mod_eq_of_lt hj] at hval; omega
  · omega

theorem next_ne_self (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) (i : Fin n) : next n hn i ≠ i := by
  intro h
  have hv : (i.val + 1) % n = i.val := congrArg Fin.val h
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv; omega
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self] at hv; omega

def xorRange (n : ℕ) (hn : 0 < n) (flip : Fin n → Bool) (start : Fin n) : ℕ → Bool
  | 0 => false
  | d + 1 => xor (xorRange n hn flip start d) (flip (step n hn start d))

theorem xorRange_card (n : ℕ) (hn : 0 < n) (flip : Fin n → Bool) (start : Fin n) :
    ∀ d ≤ n, xorRange n hn flip start d =
      decide (((Finset.range d).filter fun k => flip (step n hn start k) = true).card % 2 = 1) := by
  intro d
  induction d with
  | zero => intro _; simp [xorRange]
  | succ d ih =>
    intro hd
    rw [xorRange, ih (Nat.le_of_succ_le hd), Finset.range_add_one, Finset.filter_insert]
    have hnot : d ∉ (Finset.range d).filter (fun k => flip (step n hn start k) = true) := by
      simp
    cases hf : flip (step n hn start d)
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    · simp only [↓reduceIte, Finset.card_insert_of_notMem hnot]
      set c := ((Finset.range d).filter fun k => flip (step n hn start k) = true).card
      have hc : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
      rcases hc with h0 | h1
      · have h1' : (c + 1) % 2 = 1 := by omega
        simp [h0, h1']
      · have h0' : (c + 1) % 2 = 0 := by omega
        simp [h1, h0']

theorem xorRange_n_eq (n : ℕ) (hn : 0 < n) (flip : Fin n → Bool) (start : Fin n) :
    xorRange n hn flip start n =
      decide ((Finset.univ.filter fun j : Fin n => flip j = true).card % 2 = 1) := by
  rw [xorRange_card n hn flip start n le_rfl]
  have hcard : ((Finset.range n).filter fun k => flip (step n hn start k) = true).card =
      (Finset.univ.filter fun j : Fin n => flip j = true).card := by
    refine Finset.card_bij (fun k _ => step n hn start k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp [hk.2]
    · intro k1 hk1 k2 hk2 heq
      have h1 := off_step n hn (first := start) (Finset.mem_range.mp (Finset.mem_filter.mp hk1).1)
      have h2 := off_step n hn (first := start) (Finset.mem_range.mp (Finset.mem_filter.mp hk2).1)
      rw [← h1, heq, h2]
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨off n start j, ?_, step_off n hn start j⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨off_lt n hn start j, by rw [step_off]; exact hj⟩
  rw [hcard]

theorem xor_chain (n : ℕ) (hn : 0 < n) (flip : Fin n → Bool) (x : Fin n → Bool) (start : Fin n) (d : ℕ)
    (hstep : ∀ k < d, x (next n hn (step n hn start k)) = xor (x (step n hn start k)) (flip (step n hn start k))) :
    x (step n hn start d) = xor (x start) (xorRange n hn flip start d) := by
  induction d with
  | zero => simp [step_zero, xorRange]
  | succ d ih =>
    rw [step_succ, hstep d (Nat.lt_succ_self d), ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk)),
      xorRange, Bool.xor_assoc]

end Cyclic

section Main

def Uses (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) (x : Fin n → Bool) (i : Fin n) : Prop :=
  T (i, x i, x (next n hn i)) = true

def MaximalFalse (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) : Prop :=
  (¬ ∃ x : Fin n → Bool, ∀ i, Uses n hn T x i) ∧
  ∀ e : Fin n × (Bool × Bool), T e = false → ∃ x : Fin n → Bool,
    x e.1 = e.2.1 ∧ x (next n hn e.1) = e.2.2 ∧ ∀ i, i ≠ e.1 → Uses n hn T x i

def IsTwist (n : ℕ) (T : Fin n × (Bool × Bool) → Bool) : Prop :=
  ∃ flip : Fin n → Bool,
    (Finset.univ.filter (fun j : Fin n => flip j = true)).card % 2 = 1 ∧
    ∀ i a b, T (i, a, b) = true ↔ b = xor a (flip i)

def IsSingleton (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) : Prop :=
  ∃ (marked : Fin n) (v : Fin n → Bool), ∀ i a b,
    T (i, a, b) = true ↔
      if i = marked then a ≠ v i ∧ b = v (next n hn i) else a ≠ v i ∨ b = v (next n hn i)

def IsInterval (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) : Prop :=
  ∃ (first : Fin n) (length : ℕ) (v : Fin n → Bool),
    1 ≤ length ∧ length ≤ n ∧ ∀ i a b,
      let offset := off n first i
      T (i, a, b) = true ↔
        if length ≤ offset then True
        else if length = 1 then False
        else if offset = 0 then b = v (next n hn i)
        else if offset + 1 = length then a ≠ v i
        else a ≠ v i ∨ b = v (next n hn i)

theorem twist_to_maximalFalse (n : ℕ) (hn : 0 < n) {T : Fin n × (Bool × Bool) → Bool}
    (ht : IsTwist n T) : MaximalFalse n hn T := by
  obtain ⟨flip, hodd, hT⟩ := ht
  constructor
  · rintro ⟨x, hx⟩
    let s0 : Fin n := ⟨0, hn⟩
    have hc := xor_chain n hn flip x s0 n (fun k _ => (hT _ _ _).mp (hx _))
    rw [step_n, xorRange_n_eq, hodd] at hc
    simp only [decide_true] at hc
    cases hx0 : x s0 <;> simp [hx0] at hc
  · rintro ⟨i, a, b⟩ he
    have hne : b ≠ xor a (flip i) := fun h => by
      have := (hT i a b).mpr h
      rw [he] at this; cases this
    have hb_eq : b = xor a (!(flip i)) := by
      cases a <;> cases b <;> cases hf : flip i <;> simp_all
    let s1 : Fin n := next n hn i
    let x : Fin n → Bool := fun j => xor b (xorRange n hn flip s1 (off n s1 j))
    have hxs1 : x s1 = b := by
      have h0 : off n s1 s1 = 0 := (off_eq_zero_iff n hn s1 s1).mpr rfl
      simp [x, h0, xorRange]
    have hstep_all : ∀ k < n - 1,
        x (next n hn (step n hn s1 k)) = xor (x (step n hn s1 k)) (flip (step n hn s1 k)) := by
      intro k hk
      have hk1 : k + 1 < n := by omega
      have hkn : k < n := by omega
      have hs1 : step n hn s1 (k + 1) = next n hn (step n hn s1 k) := step_succ n hn s1 k
      rw [← hs1]
      dsimp only [x]
      rw [off_step n hn hk1, off_step n hn hkn, xorRange, Bool.xor_assoc]
    have hstep_n1 : step n hn s1 (n - 1) = i := by
      have h1 : next n hn (step n hn s1 (n - 1)) = next n hn i := by
        rw [← step_succ, show n - 1 + 1 = n by omega, step_n]
      exact next_inj n hn h1
    have hxi : x i = a := by
      have htot := xorRange_n_eq n hn flip s1
      rw [hodd] at htot
      simp only [decide_true] at htot
      have hsplit : xorRange n hn flip s1 n =
          xor (xorRange n hn flip s1 (n - 1)) (flip i) := by
        have hstep_eq : xorRange n hn flip s1 n = xorRange n hn flip s1 ((n - 1) + 1) := by
          congr 1; omega
        rw [hstep_eq, xorRange, hstep_n1]
      rw [hsplit] at htot
      have hr : xorRange n hn flip s1 (n - 1) = !(flip i) := by
        cases h1 : xorRange n hn flip s1 (n - 1) <;> cases h2 : flip i <;> simp_all
      have hoffi : off n s1 i = n - 1 := by
        have h := off_step n hn (first := s1) (d := n - 1) (by omega)
        rwa [hstep_n1] at h
      simp only [x, hoffi, hr, hb_eq, Bool.xor_assoc]
      cases a <;> cases flip i <;> decide
    refine ⟨x, hxi, hxs1, fun j hj => ?_⟩
    rw [Uses, hT]
    have hjn : off n s1 j < n - 1 := by
      have hlt := off_lt n hn s1 j
      by_contra hge
      have heq : off n s1 j = n - 1 := by omega
      have := step_off n hn s1 j
      rw [heq, hstep_n1] at this
      exact hj this.symm
    have hst := hstep_all (off n s1 j) hjn
    rwa [step_off] at hst

theorem singleton_to_maximalFalse (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    {T : Fin n × (Bool × Bool) → Bool} (hs : IsSingleton n hn T) : MaximalFalse n hn T := by
  obtain ⟨marked, v, hT⟩ := hs
  constructor
  · rintro ⟨x, hx⟩
    have hm := (hT marked (x marked) (x (next n hn marked))).mp (hx marked)
    simp only [↓reduceIte] at hm
    have hind : ∀ d < n, 1 ≤ d → x (step n hn marked d) = v (step n hn marked d) := by
      intro d
      induction d with
      | zero => intro _ h1; omega
      | succ d ih =>
        intro hdn _
        by_cases hd0 : d = 0
        · subst hd0
          simpa [step_succ, step_zero] using hm.2
        · have hprev := ih (by omega) (by omega)
          have hne : step n hn marked d ≠ marked := by
            intro heq
            have h0 := off_step n hn (first := marked) (d := d) (by omega)
            rw [heq, (off_eq_zero_iff n hn marked marked).mpr rfl] at h0
            omega
          have hu := (hT (step n hn marked d) _ _).mp (hx (step n hn marked d))
          simp only [hne, ↓reduceIte] at hu
          rcases hu with h1 | h2'
          · exact absurd hprev h1
          · rwa [step_succ]
    have hprev := hind (n - 1) (by omega) (by omega)
    have hne : step n hn marked (n - 1) ≠ marked := by
      intro heq
      have h0 := off_step n hn (first := marked) (d := n - 1) (by omega)
      rw [heq, (off_eq_zero_iff n hn marked marked).mpr rfl] at h0
      omega
    have hu := (hT (step n hn marked (n - 1)) _ _).mp (hx (step n hn marked (n - 1)))
    simp only [hne, ↓reduceIte] at hu
    rcases hu with h1 | h2'
    · exact h1 hprev
    · have hback : next n hn (step n hn marked (n - 1)) = marked := by
        rw [← step_succ, show n - 1 + 1 = n by omega, step_n]
      rw [hback] at h2'
      exact hm.1 h2'
  · rintro ⟨i, a, b⟩ he
    by_cases him : i = marked
    · subst him
      have hnot : ¬ (a ≠ v i ∧ b = v (next n hn i)) := fun h => by
        have := (hT i a b).mpr (by simp [h])
        rw [he] at this; cases this
      by_cases hb : b = v (next n hn i)
      · have ha : a = v i := by
          by_contra hne
          exact hnot ⟨hne, hb⟩
        refine ⟨v, ha.symm, hb.symm, fun j hj => ?_⟩
        rw [Uses, hT]
        simp [hj]
      · let x : Fin n → Bool := fun j => if j = i then a else !(v j)
        have hnext_ne : next n hn i ≠ i := next_ne_self n hn h2 i
        have hxb : x (next n hn i) = b := by
          simp only [x, hnext_ne, ↓reduceIte]
          cases b <;> cases hvn : v (next n hn i) <;> simp_all
        refine ⟨x, by simp [x], hxb, fun j hj => ?_⟩
        rw [Uses, hT]
        simp only [hj, ↓reduceIte, x]
        left
        cases v j <;> decide
    · have hnot : ¬ (a ≠ v i ∨ b = v (next n hn i)) := fun h => by
        have := (hT i a b).mpr (by simp [him, h])
        rw [he] at this; cases this
      have ha : a = v i := by
        by_contra hne
        exact hnot (Or.inl hne)
      have hb : b ≠ v (next n hn i) := fun h => hnot (Or.inr h)
      have hoff_pos : 0 < off n marked i := by
        by_contra h0
        exact him ((off_eq_zero_iff n hn marked i).mp (by omega))
      let x : Fin n → Bool := fun j =>
        if 0 < off n marked j ∧ off n marked j ≤ off n marked i then v j else !(v j)
      have hxi : x i = a := by
        simp [x, hoff_pos, ha]
      have hxni : x (next n hn i) = b := by
        have hcond : ¬ (0 < off n marked (next n hn i) ∧ off n marked (next n hn i) ≤ off n marked i) := by
          by_cases hlast : off n marked i + 1 < n
          · rw [off_next_of_lt n hn hlast]; omega
          · have heq : off n marked i + 1 = n := by have := off_lt n hn marked i; omega
            rw [next_of_off_succ_eq n hn heq, (off_eq_zero_iff n hn marked marked).mpr rfl]; omega
        simp only [x, hcond, ↓reduceIte]
        cases b <;> cases hvn : v (next n hn i) <;> simp_all
      refine ⟨x, hxi, hxni, fun j hj => ?_⟩
      rw [Uses, hT]
      by_cases hjm : j = marked
      · subst hjm
        simp only [↓reduceIte]
        have h0 : off n j j = 0 := (off_eq_zero_iff n hn j j).mpr rfl
        have h1 : off n j (next n hn j) = 1 := by
          rw [off_next_of_lt n hn (by rw [h0]; omega), h0]
        constructor
        · simp only [x, h0, lt_self_iff_false, false_and, ↓reduceIte]
          cases v j <;> decide
        · simp only [x, h1]
          have : 0 < 1 ∧ 1 ≤ off n j i := ⟨by decide, hoff_pos⟩
          simp [this]
      · simp only [hjm, ↓reduceIte]
        have hj_pos : 0 < off n marked j := by
          by_contra h0
          exact hjm ((off_eq_zero_iff n hn marked j).mp (by omega))
        by_cases hjlt : off n marked j < off n marked i
        · right
          have hlt_n : off n marked j + 1 < n := by have := off_lt n hn marked i; omega
          have hnext_off := off_next_of_lt n hn hlt_n
          have hcond : 0 < off n marked (next n hn j) ∧ off n marked (next n hn j) ≤ off n marked i := by
            rw [hnext_off]; omega
          simp [x, hcond]
        · left
          have hjgt : off n marked i < off n marked j := by
            have hne_off : off n marked j ≠ off n marked i := by
              intro heq
              have h1 := step_off n hn marked j
              have h2' := step_off n hn marked i
              rw [heq] at h1
              exact hj (h1.symm.trans h2')
            omega
          have hcond : ¬ (0 < off n marked j ∧ off n marked j ≤ off n marked i) := by omega
          simp only [x, hcond, ↓reduceIte]
          cases v j <;> decide

theorem interval_to_maximalFalse (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    {T : Fin n × (Bool × Bool) → Bool} (hi : IsInterval n hn T) : MaximalFalse n hn T := by
  obtain ⟨first, len, v, hlen1, hlenn, hT⟩ := hi
  constructor
  · rintro ⟨x, hx⟩
    by_cases hlen_eq1 : len = 1
    · have hu := (hT first (x first) (x (next n hn first))).mp (hx first)
      have h0 : off n first first = 0 := (off_eq_zero_iff n hn first first).mpr rfl
      simp [h0, hlen_eq1] at hu
    · have hind : ∀ d, 1 ≤ d → d < len → x (step n hn first d) = v (step n hn first d) := by
        intro d
        induction d with
        | zero => intro h1 _; omega
        | succ d ih =>
          intro _ hdlen
          by_cases hd0 : d = 0
          · subst hd0
            have hu := (hT first (x first) (x (next n hn first))).mp (hx first)
            have h0 : off n first first = 0 := (off_eq_zero_iff n hn first first).mpr rfl
            simp only [h0, show ¬ len ≤ 0 by omega, hlen_eq1, ↓reduceIte] at hu
            simpa [step_succ, step_zero] using hu
          · have hprev := ih (by omega) (by omega)
            have hoff := off_step n hn (first := first) (d := d) (by omega)
            have hu := (hT (step n hn first d) _ _).mp (hx (step n hn first d))
            simp only [hoff, show ¬ len ≤ d by omega, hlen_eq1, show d ≠ 0 by omega,
              show d + 1 ≠ len by omega, ↓reduceIte] at hu
            rcases hu with h1 | h2'
            · exact absurd hprev h1
            · rwa [step_succ]
      have hlast := hind (len - 1) (by omega) (by omega)
      have hoff := off_step n hn (first := first) (d := len - 1) (by omega)
      have hu := (hT (step n hn first (len - 1)) _ _).mp (hx (step n hn first (len - 1)))
      simp only [hoff, show ¬ len ≤ len - 1 by omega, hlen_eq1, show len - 1 ≠ 0 by omega,
        show len - 1 + 1 = len by omega, ↓reduceIte] at hu
      exact hu hlast
  · rintro ⟨i, a, b⟩ he
    have hnot : ¬ (if len ≤ off n first i then True
        else if len = 1 then False
        else if off n first i = 0 then b = v (next n hn i)
        else if off n first i + 1 = len then a ≠ v i
        else a ≠ v i ∨ b = v (next n hn i)) := fun h => by
      have := (hT i a b).mpr h
      rw [he] at this; cases this
    have hoff_lt : off n first i < len := by
      by_contra hge
      exact hnot (by simp [Nat.le_of_not_lt hge])
    by_cases hlen_eq1 : len = 1
    · have hif : i = first := (off_eq_zero_iff n hn first i).mp (by omega)
      let x : Fin n → Bool := fun j => if j = i then a else b
      have hne : next n hn i ≠ i := next_ne_self n hn h2 i
      refine ⟨x, by simp [x], by simp [x, hne], fun j hj => ?_⟩
      rw [Uses]
      refine (hT j (x j) (x (next n hn j))).mpr ?_
      have hj_pos : 1 ≤ off n first j := by
        by_contra h0
        exact hj (((off_eq_zero_iff n hn first j).mp (by omega)).trans hif.symm)
      simp [hlen_eq1, hj_pos]
    · have ha_if_pos : 0 < off n first i → a = v i := by
        intro hpos
        by_contra hne
        apply hnot
        simp only [show ¬ len ≤ off n first i by omega, hlen_eq1, show off n first i ≠ 0 by omega, ↓reduceIte]
        split_ifs
        · exact hne
        · exact Or.inl hne
      have hb_if_lt : off n first i + 1 < len → b ≠ v (next n hn i) := by
        intro hlt hbeq
        apply hnot
        simp only [show ¬ len ≤ off n first i by omega, hlen_eq1, ↓reduceIte]
        split_ifs with h0 hlast
        · exact hbeq
        · omega
        · exact Or.inr hbeq
      let x : Fin n → Bool := fun j =>
        if j = i then a
        else if j = next n hn i then b
        else if 0 < off n first j ∧ off n first j ≤ off n first i then v j
        else !(v j)
      have hne_ni : next n hn i ≠ i := next_ne_self n hn h2 i
      have hxi : x i = a := by simp [x]
      have hxni : x (next n hn i) = b := by simp [x, hne_ni]
      have hlow : ∀ k : Fin n, 0 < off n first k → off n first k ≤ off n first i → x k = v k := by
        intro k hk1 hk2
        by_cases hki : k = i
        · subst hki; rw [hxi]; exact ha_if_pos hk1
        · by_cases hkni : k = next n hn i
          · exfalso
            subst hkni
            by_cases hwrap : off n first i + 1 < n
            · rw [off_next_of_lt n hn hwrap] at hk2; omega
            · have heq : off n first i + 1 = n := by have := off_lt n hn first i; omega
              rw [next_of_off_succ_eq n hn heq, (off_eq_zero_iff n hn first first).mpr rfl] at hk1; omega
          · simp [x, hki, hkni, hk1, hk2]
      have hhigh_len : ∀ k : Fin n, off n first i < off n first k → off n first k < len → x k ≠ v k := by
        intro k hk hklen
        have hki : k ≠ i := fun h => by subst h; omega
        by_cases hkni : k = next n hn i
        · subst hkni
          rw [hxni]
          apply hb_if_lt
          have hwrap : off n first i + 1 < n := by omega
          rw [off_next_of_lt n hn hwrap] at hklen
          exact hklen
        · simp only [x, hki, hkni, ↓reduceIte, show ¬ (0 < off n first k ∧ off n first k ≤ off n first i) by omega]
          cases v k <;> decide
      refine ⟨x, hxi, hxni, fun j hj => ?_⟩
      rw [Uses]
      refine (hT j (x j) (x (next n hn j))).mpr ?_
      by_cases hjlen : len ≤ off n first j
      · simp [hjlen]
      · simp only [hjlen, hlen_eq1, ↓reduceIte]
        have hjlt_len : off n first j < len := by omega
        have hjne_off : off n first j ≠ off n first i := by
          intro heq
          have h1 := step_off n hn first j
          have h2' := step_off n hn first i
          rw [heq] at h1
          exact hj (h1.symm.trans h2')
        by_cases hj0 : off n first j = 0
        · simp only [hj0, ↓reduceIte]
          have hwrap : off n first j + 1 < n := by omega
          have hn_off := off_next_of_lt n hn hwrap
          rw [hj0] at hn_off
          exact hlow (next n hn j) (by omega) (by omega)
        · simp only [hj0, ↓reduceIte]
          by_cases hjlast : off n first j + 1 = len
          · simp only [hjlast, ↓reduceIte]
            exact hhigh_len j (by omega) hjlt_len
          · simp only [hjlast, ↓reduceIte]
            by_cases hjlt_i : off n first j < off n first i
            · right
              have hwrap : off n first j + 1 < n := by omega
              have hn_off := off_next_of_lt n hn hwrap
              exact hlow (next n hn j) (by omega) (by omega)
            · left
              exact hhigh_len j (by omega) hjlt_len

def HasMatching (n : ℕ) (T : Fin n × (Bool × Bool) → Bool) (i : Fin n) : Prop :=
  ∃ f : Bool, ∀ a : Bool, T (i, a, xor a f) = true

theorem nonmatching_is_rect (R : Bool → Bool → Bool)
    (hno : ¬ ∃ f : Bool, ∀ a : Bool, R a (xor a f) = true) :
    ∀ a b : Bool, R a b = true ↔ (∃ b', R a b' = true) ∧ (∃ a', R a' b = true) := by
  revert R hno
  decide

def Reaches (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) (r : Fin n) (d : ℕ) (b a : Bool) : Prop :=
  ∃ p : ℕ → Bool, p 0 = b ∧ p d = a ∧
    ∀ k < d, T (step n hn (next n hn r) k, p k, p (k + 1)) = true

theorem reaches_zero (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) (r : Fin n) (b a : Bool) :
    Reaches n hn T r 0 b a ↔ b = a := by
  constructor
  · rintro ⟨p, h0, h1, _⟩; exact h0.symm.trans h1
  · rintro rfl; exact ⟨fun _ => b, rfl, rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem reaches_succ (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) (r : Fin n) (d : ℕ) (b a : Bool) :
    Reaches n hn T r (d + 1) b a ↔
      ∃ c : Bool, Reaches n hn T r d b c ∧ T (step n hn (next n hn r) d, c, a) = true := by
  constructor
  · rintro ⟨p, h0, hd1, hall⟩
    exact ⟨p d, ⟨p, h0, rfl, fun k hk => hall k (Nat.lt_succ_of_lt hk)⟩,
      hd1 ▸ hall d (Nat.lt_succ_self d)⟩
  · rintro ⟨c, ⟨p, h0, hd, hall⟩, hlast⟩
    refine ⟨fun k => if k ≤ d then p k else a, by simp [h0], by simp, fun k hk => ?_⟩
    by_cases hkd : k < d
    · have h1 : k ≤ d := Nat.le_of_lt hkd
      have h2 : k + 1 ≤ d := hkd
      simp only [h1, h2, ↓reduceIte]
      exact hall k hkd
    · have hke : k = d := by omega
      rw [hke]
      simp only [le_refl, ↓reduceIte, show ¬ d + 1 ≤ d by omega]
      rwa [hd]

theorem reaches_trans (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) (r : Fin n)
    (d1 d2 : ℕ) (b c a : Bool)
    (h1 : Reaches n hn T r d1 b c) (h2 : Reaches n hn T (step n hn r d1) d2 c a) :
    Reaches n hn T r (d1 + d2) b a := by
  obtain ⟨p1, hp10, hp1d, hp1⟩ := h1
  obtain ⟨p2, hp20, hp2d, hp2⟩ := h2
  refine ⟨fun k => if k ≤ d1 then p1 k else p2 (k - d1), by simp [hp10], ?_, fun k hk => ?_⟩
  · by_cases hd2 : d2 = 0
    · subst hd2; simp [hp1d, ← hp20, hp2d]
    · simp [show ¬ d1 + d2 ≤ d1 by omega, hp2d]
  · by_cases hk1 : k < d1
    · simp only [Nat.le_of_lt hk1, show k + 1 ≤ d1 by omega, ↓reduceIte]
      exact hp1 k hk1
    · by_cases hke : k = d1
      · rw [hke]
        simp only [le_refl, show ¬ d1 + 1 ≤ d1 by omega, ↓reduceIte, hp1d]
        have hstep_eq : step n hn (next n hn r) d1 = step n hn (next n hn (step n hn r d1)) 0 := by
          ext; simp only [step, next, Nat.mod_add_mod]; congr 1; omega
        rw [hstep_eq, show d1 + 1 - d1 = 1 by omega, ← hp20]
        exact hp2 0 (by omega)
      · simp only [show ¬ k ≤ d1 by omega, show ¬ k + 1 ≤ d1 by omega, ↓reduceIte]
        have hstep_eq : step n hn (next n hn r) k = step n hn (next n hn (step n hn r d1)) (k - d1) := by
          ext
          simp only [step, next, Nat.mod_add_mod]
          congr 1; omega
        rw [hstep_eq, show k + 1 - d1 = (k - d1) + 1 by omega]
        exact hp2 (k - d1) (by omega)

theorem reaches_of_matchings (n : ℕ) (hn : 0 < n) (T : Fin n × (Bool × Bool) → Bool) (r : Fin n) (d : ℕ)
    (hm : ∀ k < d, HasMatching n T (step n hn (next n hn r) k)) :
    ∃ f : Bool, ∀ b : Bool, Reaches n hn T r d b (xor b f) := by
  induction d with
  | zero => exact ⟨false, fun b => by rw [reaches_zero]; simp⟩
  | succ d ih =>
    obtain ⟨f1, hf1⟩ := ih (fun k hk => hm k (Nat.lt_succ_of_lt hk))
    obtain ⟨f2, hf2⟩ := hm d (Nat.lt_succ_self d)
    refine ⟨xor f1 f2, fun b => ?_⟩
    rw [reaches_succ]
    refine ⟨xor b f1, hf1 b, ?_⟩
    rw [← Bool.xor_assoc]
    exact hf2 (xor b f1)

theorem case_all_matching (n : ℕ) (hn : 0 < n) {T : Fin n × (Bool × Bool) → Bool}
    (hinfeas : ¬ ∃ x : Fin n → Bool, ∀ i, Uses n hn T x i)
    (hallM : ∀ i : Fin n, HasMatching n T i) : IsTwist n T := by
  classical
  let flip : Fin n → Bool := fun i => Classical.choose (hallM i)
  have hflip : ∀ i a, T (i, a, xor a (flip i)) = true := fun i => Classical.choose_spec (hallM i)
  have hodd : (Finset.univ.filter fun j : Fin n => flip j = true).card % 2 = 1 := by
    have hmod := Nat.mod_two_eq_zero_or_one (Finset.univ.filter fun j : Fin n => flip j = true).card
    rcases hmod with h0 | h1'
    · exfalso
      let s0 : Fin n := ⟨0, hn⟩
      let x : Fin n → Bool := fun j => xorRange n hn flip s0 (off n s0 j)
      apply hinfeas
      refine ⟨x, fun i => ?_⟩
      rw [Uses]
      by_cases hwrap : off n s0 i + 1 < n
      · have hn_off := off_next_of_lt n hn hwrap
        simp only [x, hn_off, xorRange, step_off]
        exact hflip i _
      · have heq : off n s0 i + 1 = n := by have := off_lt n hn s0 i; omega
        have hnext := next_of_off_succ_eq n hn heq
        have hx0 : x (next n hn i) = false := by
          rw [hnext]
          have h00 : off n s0 s0 = 0 := (off_eq_zero_iff n hn s0 s0).mpr rfl
          simp [x, h00, xorRange]
        have htot := xorRange_n_eq n hn flip s0
        rw [h0] at htot
        simp only [show ¬ (0 : ℕ) = 1 by decide, decide_false] at htot
        have hsplit : xorRange n hn flip s0 n =
            xor (xorRange n hn flip s0 (off n s0 i)) (flip i) := by
          have hstep_eq : xorRange n hn flip s0 n = xorRange n hn flip s0 (off n s0 i + 1) := by
            congr 1; omega
          rw [hstep_eq, xorRange, step_off]
        rw [hsplit] at htot
        rw [hx0, ← htot]
        exact hflip i _
    · exact h1'
  refine ⟨flip, hodd, fun i a b => ⟨fun hTab => ?_, fun hb => hb ▸ hflip i a⟩⟩
  by_contra hne
  have hb_eq : b = xor a (!(flip i)) := by
    revert hne; generalize flip i = fi; cases a <;> cases b <;> cases fi <;> decide
  let s1 : Fin n := next n hn i
  let x : Fin n → Bool := fun q => xor b (xorRange n hn flip s1 (off n s1 q))
  have hxs1 : x s1 = b := by
    have h00 : off n s1 s1 = 0 := (off_eq_zero_iff n hn s1 s1).mpr rfl
    simp [x, h00, xorRange]
  have hstep_n1 : step n hn s1 (n - 1) = i := by
    have h1' : next n hn (step n hn s1 (n - 1)) = next n hn i := by
      rw [← step_succ, show n - 1 + 1 = n by omega, step_n]
    exact next_inj n hn h1'
  have hoffi : off n s1 i = n - 1 := by
    have h := off_step n hn (first := s1) (d := n - 1) (by omega)
    rwa [hstep_n1] at h
  have htot := xorRange_n_eq n hn flip s1
  rw [hodd] at htot; simp only [decide_true] at htot
  have hsplit : xorRange n hn flip s1 n =
      xor (xorRange n hn flip s1 (n - 1)) (flip i) := by
    have hstep_eq : xorRange n hn flip s1 n = xorRange n hn flip s1 ((n - 1) + 1) := by
      congr 1; omega
    rw [hstep_eq, xorRange, hstep_n1]
  rw [hsplit] at htot
  have hr : xorRange n hn flip s1 (n - 1) = !(flip i) := by
    revert htot
    generalize xorRange n hn flip s1 (n - 1) = y
    generalize flip i = fi
    cases y <;> cases fi <;> decide
  have hxi : x i = a := by
    simp only [x, hoffi, hr, hb_eq, Bool.xor_assoc]
    cases a <;> cases flip i <;> decide
  apply hinfeas
  refine ⟨x, fun q => ?_⟩
  rw [Uses]
  by_cases hqi : q = i
  · subst hqi; rw [hxi, hxs1]; exact hTab
  · have hqn : off n s1 q < n - 1 := by
      have hlt := off_lt n hn s1 q
      by_contra hge
      have heq : off n s1 q = n - 1 := by omega
      have hst := step_off n hn s1 q
      rw [heq, hstep_n1] at hst
      exact hqi hst.symm
    have hnext_off := off_next_of_lt n hn (by omega : off n s1 q + 1 < n)
    dsimp only [x]
    rw [hnext_off, xorRange, step_off, ← Bool.xor_assoc]
    exact hflip q _

theorem exists_failed_gap (n : ℕ) (hn : 0 < n) {T : Fin n × (Bool × Bool) → Bool}
    (hinfeas : ¬ ∃ x : Fin n → Bool, ∀ i, Uses n hn T x i)
    (Bad : Finset (Fin n)) (hBad_def : ∀ i, i ∈ Bad ↔ ¬ HasMatching n T i)
    (hBad_ne : Bad.Nonempty) :
    ∃ (r0 : Fin n) (d0 : ℕ), r0 ∈ Bad ∧ d0 < n ∧
      step n hn (next n hn r0) d0 ∈ Bad ∧
      (∀ k < d0, HasMatching n T (step n hn (next n hn r0) k)) ∧
      ∀ b a : Bool, (∃ a0, T (r0, a0, b) = true) →
        (∃ b1, T (step n hn (next n hn r0) d0, a, b1) = true) →
        ¬ Reaches n hn T r0 d0 b a := by
  classical
  have hrect : ∀ i ∈ Bad, ∀ a b : Bool,
      T (i, a, b) = true ↔ (∃ b', T (i, a, b') = true) ∧ (∃ a', T (i, a', b) = true) :=
    fun i hi => nonmatching_is_rect (fun a b => T (i, a, b)) ((hBad_def i).mp hi)
  have hgap_ex : ∀ r : Fin n, ∃ d, d < n ∧ step n hn (next n hn r) d ∈ Bad := by
    intro r
    obtain ⟨b, hb⟩ := hBad_ne
    exact ⟨off n (next n hn r) b, off_lt n hn (next n hn r) b, by rw [step_off]; exact hb⟩
  let gapLen : Fin n → ℕ := fun r => Nat.find (hgap_ex r)
  have hgapLen_lt : ∀ r, gapLen r < n := fun r => (Nat.find_spec (hgap_ex r)).1
  have hgapLen_mem : ∀ r, step n hn (next n hn r) (gapLen r) ∈ Bad := fun r => (Nat.find_spec (hgap_ex r)).2
  have hgapLen_min : ∀ r k, k < gapLen r → HasMatching n T (step n hn (next n hn r) k) := by
    intro r k hk
    have hnot := Nat.find_min (hgap_ex r) hk
    have hnb : step n hn (next n hn r) k ∉ Bad := fun hm => hnot ⟨lt_trans hk (hgapLen_lt r), hm⟩
    by_contra hno
    exact hnb ((hBad_def _).mpr hno)
  by_contra hnone
  have hall_good : ∀ r ∈ Bad, ∃ p : ℕ → Bool,
      (∃ a0, T (r, a0, p 0) = true) ∧
      (∃ b1, T (step n hn (next n hn r) (gapLen r), p (gapLen r), b1) = true) ∧
      ∀ k < gapLen r, T (step n hn (next n hn r) k, p k, p (k + 1)) = true := by
    intro r hr
    by_contra hno
    apply hnone
    refine ⟨r, gapLen r, hr, hgapLen_lt r, hgapLen_mem r, hgapLen_min r, fun b a hb ha hreach => ?_⟩
    obtain ⟨p, hp0, hpd, hpk⟩ := hreach
    exact hno ⟨p, hp0.symm ▸ hb, hpd.symm ▸ ha, hpk⟩
  have hprev_ex : ∀ j : Fin n, ∃ d, d < n ∧ step n hn j (n - 1 - d) ∈ Bad := by
    intro j
    obtain ⟨b, hb⟩ := hBad_ne
    have hlt := off_lt n hn j b
    refine ⟨n - 1 - off n j b, by omega, ?_⟩
    have hsub : n - 1 - (n - 1 - off n j b) = off n j b := by omega
    rw [hsub, step_off]; exact hb
  have hprev_spec : ∀ j : Fin n, ∃ r ∈ Bad, ∃ k ≤ gapLen r, step n hn (next n hn r) k = j := by
    intro j
    let m := Nat.find (hprev_ex j)
    have hm_spec := Nat.find_spec (hprev_ex j)
    let r := step n hn j (n - 1 - m)
    have hr : r ∈ Bad := hm_spec.2
    have hm_lt : m < n := hm_spec.1
    have hstep_rj : step n hn (next n hn r) m = j := by
      ext
      simp only [r, step, next, Nat.mod_add_mod]
      rw [Nat.add_assoc, Nat.add_assoc, show (n - 1 - m) + (1 + m) = n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    have hm_le : m ≤ gapLen r := by
      by_contra hgt
      have hlt : gapLen r < m := by omega
      let t := m - 1 - gapLen r
      have hnot := Nat.find_min (hprev_ex j) (show t < m by omega)
      apply hnot
      refine ⟨by omega, ?_⟩
      have heq : step n hn j (n - 1 - t) = step n hn (next n hn r) (gapLen r) := by
        have harith : n - 1 - t = (n - 1 - m) + (1 + gapLen r) := by omega
        rw [harith]
        ext
        simp only [r, step, next, Nat.mod_add_mod, Nat.add_assoc]
      rw [heq]
      exact hgapLen_mem r
    exact ⟨r, hr, m, hm_le, hstep_rj⟩
  have hprev_uniq : ∀ j r1 r2 k1 k2, r1 ∈ Bad → r2 ∈ Bad →
      k1 ≤ gapLen r1 → k2 ≤ gapLen r2 →
      step n hn (next n hn r1) k1 = j → step n hn (next n hn r2) k2 = j →
      r1 = r2 ∧ k1 = k2 := by
    intro j r1 r2 k1 k2 hr1 hr2 hk1 hk2 he1 he2
    have hne_imp : ∀ rA rB kA kB, rA ∈ Bad → rB ∈ Bad → kA ≤ gapLen rA → kB ≤ gapLen rB →
        step n hn (next n hn rA) kA = j → step n hn (next n hn rB) kB = j → kA < kB → False := by
      intro rA rB kA kB hrA _ hkA hkB hA hB hlt
      have hd : kB - kA - 1 < gapLen rB := by omega
      have hgood := hgapLen_min rB (kB - kA - 1) hd
      have heq : step n hn (next n hn rB) (kB - kA - 1) = rA := by
        have h1' : step n hn (step n hn (next n hn rB) (kB - kA - 1)) (kA + 1) =
            step n hn rA (kA + 1) := by
          rw [step_add, show kB - kA - 1 + (kA + 1) = kB by omega, hB, ← hA]
          ext; simp only [step, next, Nat.mod_add_mod]; congr 1; omega
        have hkA1 : kA + 1 ≤ n := by have := hgapLen_lt rA; omega
        let X := step n hn (next n hn rB) (kB - kA - 1)
        have hadd : step n hn X (kA + 1 + (n - (kA + 1))) = step n hn rA (kA + 1 + (n - (kA + 1))) := by
          rw [← step_add n hn X (kA + 1) (n - (kA + 1)), ← step_add n hn rA (kA + 1) (n - (kA + 1))]
          exact congrArg (fun q => step n hn q (n - (kA + 1))) h1'
        rw [show kA + 1 + (n - (kA + 1)) = n by omega, step_n, step_n] at hadd
        exact hadd
      rw [heq] at hgood
      exact (hBad_def rA).mp hrA hgood
    rcases lt_trichotomy k1 k2 with hlt | rfl | hgt
    · exact False.elim (hne_imp r1 r2 k1 k2 hr1 hr2 hk1 hk2 he1 he2 hlt)
    · refine ⟨?_, rfl⟩
      have hk1n : k1 ≤ n := Nat.le_of_lt (lt_of_le_of_lt hk1 (hgapLen_lt r1))
      have hadd := congrArg (fun q => step n hn q (n - k1)) (he1.trans he2.symm)
      have h1' : step n hn (next n hn r1) n = step n hn (next n hn r2) n := by
        simpa [step_add, show k1 + (n - k1) = n by omega] using hadd
      simp only [step_n] at h1'
      exact next_inj n hn h1'
    · exact False.elim (hne_imp r2 r1 k2 k1 hr2 hr1 hk2 hk1 he2 he1 hgt)
  let x : Fin n → Bool := fun j =>
    let r := Classical.choose (hprev_spec j)
    let hr := (Classical.choose_spec (hprev_spec j)).1
    let k := Classical.choose (Classical.choose_spec (hprev_spec j)).2
    Classical.choose (hall_good r hr) k
  have hx_at : ∀ r (hr : r ∈ Bad) k (hk : k ≤ gapLen r),
      x (step n hn (next n hn r) k) = Classical.choose (hall_good r hr) k := by
    intro r hr k hk
    dsimp only [x]
    set j := step n hn (next n hn r) k
    set r' := Classical.choose (hprev_spec j)
    have hr' := (Classical.choose_spec (hprev_spec j)).1
    set k' := Classical.choose (Classical.choose_spec (hprev_spec j)).2
    have hk' := Classical.choose_spec (Classical.choose_spec (hprev_spec j)).2
    have hpair := hprev_uniq j r' r k' k hr' hr hk'.1 hk hk'.2 rfl
    have hfn : ∀ (r1 r2 : Fin n) (h1 : r1 ∈ Bad) (h2 : r2 ∈ Bad) (k1 k2 : ℕ),
        r1 = r2 → k1 = k2 → Classical.choose (hall_good r1 h1) k1 = Classical.choose (hall_good r2 h2) k2 := by
      rintro r1 _ h1 h2 k1 _ rfl rfl; rfl
    exact hfn r' r hr' hr k' k hpair.1 hpair.2
  apply hinfeas
  refine ⟨x, fun j => ?_⟩
  rw [Uses]
  obtain ⟨r, hr, k, hk, rfl⟩ := hprev_spec j
  by_cases hke : k < gapLen r
  · rw [hx_at r hr k (Nat.le_of_lt hke), ← step_succ, hx_at r hr (k + 1) hke]
    exact (Classical.choose_spec (hall_good r hr)).2.2 k hke
  · have hkeq : k = gapLen r := by omega
    rw [hkeq]
    let s := step n hn (next n hn r) (gapLen r)
    have hs : s ∈ Bad := hgapLen_mem r
    have hx1 : x s = Classical.choose (hall_good r hr) (gapLen r) := hx_at r hr (gapLen r) le_rfl
    have hx2 : x (next n hn s) = Classical.choose (hall_good s hs) 0 := by
      have := hx_at s hs 0 (Nat.zero_le _)
      simpa [step_zero] using this
    change T (s, x s, x (next n hn s)) = true
    rw [hx1, hx2, hrect s hs]
    exact ⟨(Classical.choose_spec (hall_good r hr)).2.1, (Classical.choose_spec (hall_good s hs)).1⟩

theorem failed_gap_classify (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    {T : Fin n × (Bool × Bool) → Bool}
    (hmax : ∀ e : Fin n × (Bool × Bool), T e = false → ∃ x : Fin n → Bool,
      x e.1 = e.2.1 ∧ x (next n hn e.1) = e.2.2 ∧ ∀ i, i ≠ e.1 → Uses n hn T x i)
    (hnonempty : ∀ i : Fin n, ∃ a b : Bool, T (i, a, b) = true)
    (r0 : Fin n) (d0 : ℕ) (hr0 : ¬ HasMatching n T r0) (hd0_lt : d0 < n)
    (hs0 : ¬ HasMatching n T (step n hn (next n hn r0) d0))
    (hmatch_gap : ∀ k < d0, HasMatching n T (step n hn (next n hn r0) k))
    (hfail : ∀ b a : Bool, (∃ a0, T (r0, a0, b) = true) →
      (∃ b1, T (step n hn (next n hn r0) d0, a, b1) = true) →
      ¬ Reaches n hn T r0 d0 b a) :
    IsSingleton n hn T ∨ IsInterval n hn T := by
  classical
  let s0 := step n hn (next n hn r0) d0
  have hrect_r0 : ∀ a b, T (r0, a, b) = true ↔ (∃ b', T (r0, a, b') = true) ∧ (∃ a', T (r0, a', b) = true) :=
    nonmatching_is_rect (fun a b => T (r0, a, b)) hr0
  have hrect_s0 : ∀ a b, T (s0, a, b) = true ↔ (∃ b', T (s0, a, b') = true) ∧ (∃ a', T (s0, a', b) = true) :=
    nonmatching_is_rect (fun a b => T (s0, a, b)) hs0
  obtain ⟨fgap, hfgap⟩ := reaches_of_matchings n hn T r0 d0 hmatch_gap
  have hR_uniq : ∃ w0 : Bool, ∀ b : Bool, (∃ a0, T (r0, a0, b) = true) ↔ b = w0 := by
    obtain ⟨a0, b0, h0⟩ := hnonempty r0
    refine ⟨b0, fun b => ⟨fun hb => ?_, fun heq => heq ▸ ⟨a0, h0⟩⟩⟩
    by_contra hne
    obtain ⟨a1, b1, h1⟩ := hnonempty s0
    have hcov : ∀ c : Bool, ∃ a', T (r0, a', c) = true := by
      intro c
      by_cases hcb : c = b0
      · exact hcb ▸ ⟨a0, h0⟩
      · have hcb2 : c = b := by revert hcb hne; cases c <;> cases b0 <;> cases b <;> decide
        exact hcb2 ▸ hb
    exact hfail (xor a1 fgap) a1 (hcov _) ⟨b1, h1⟩ (by
      have := hfgap (xor a1 fgap)
      rwa [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] at this)
  obtain ⟨w0, hw0⟩ := hR_uniq
  have hL_uniq : ∃ u0 : Bool, ∀ a : Bool, (∃ b1, T (s0, a, b1) = true) ↔ a = u0 := by
    obtain ⟨a1, b1, h1⟩ := hnonempty s0
    refine ⟨a1, fun a => ⟨fun ha => ?_, fun heq => heq ▸ ⟨b1, h1⟩⟩⟩
    by_contra hne
    have hcov : ∀ c : Bool, ∃ b', T (s0, c, b') = true := by
      intro c
      by_cases hca : c = a1
      · exact hca ▸ ⟨b1, h1⟩
      · have hca2 : c = a := by revert hca hne; cases c <;> cases a1 <;> cases a <;> decide
        exact hca2 ▸ ha
    exact hfail w0 (xor w0 fgap) ((hw0 w0).mpr rfl) (hcov _) (hfgap w0)
  obtain ⟨u0, hu0⟩ := hL_uniq
  have hreach_uniq : ∀ k ≤ d0, ∃! c : Bool, Reaches n hn T r0 k w0 c := by
    intro k hk
    obtain ⟨fk, hfk⟩ := reaches_of_matchings n hn T r0 k (fun j hj => hmatch_gap j (lt_of_lt_of_le hj hk))
    refine ⟨xor w0 fk, hfk w0, fun c hc => ?_⟩
    by_contra hne
    obtain ⟨frest, hfrest⟩ := reaches_of_matchings n hn T (step n hn r0 k) (d0 - k) (fun j hj => by
      have heq : step n hn (next n hn (step n hn r0 k)) j = step n hn (next n hn r0) (k + j) := by
        ext; simp only [step, next, Nat.mod_add_mod]; congr 1; omega
      rw [heq]
      exact hmatch_gap (k + j) (by omega))
    have hcov : ∀ z : Bool, Reaches n hn T r0 k w0 z := by
      intro z
      by_cases h1' : z = xor w0 fk
      · exact h1' ▸ hfk w0
      · have h2' : z = c := by revert h1' hne; generalize xor w0 fk = y; cases z <;> cases c <;> cases y <;> decide
        exact h2' ▸ hc
    have hreach_u0 : Reaches n hn T r0 d0 w0 u0 := by
      have htr := reaches_trans n hn T r0 k (d0 - k) w0 (xor u0 frest) u0 (hcov _) (by
        have := hfrest (xor u0 frest)
        rwa [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] at this)
      rwa [show k + (d0 - k) = d0 by omega] at htr
    exact hfail w0 u0 ((hw0 w0).mpr rfl) ((hu0 u0).mpr rfl) hreach_u0
  let v : Fin n → Bool := fun j =>
    if h : off n (next n hn r0) j ≤ d0 then
      Classical.choose (hreach_uniq (off n (next n hn r0) j) h).exists
    else false
  have hv_reach : ∀ k (hk : k ≤ d0), Reaches n hn T r0 k w0 (v (step n hn (next n hn r0) k)) := by
    intro k hk
    have hoff : off n (next n hn r0) (step n hn (next n hn r0) k) = k :=
      off_step n hn (first := next n hn r0) (lt_of_le_of_lt hk hd0_lt)
    dsimp only [v]
    have hk' : off n (next n hn r0) (step n hn (next n hn r0) k) ≤ d0 := by rw [hoff]; exact hk
    simp only [hk', ↓reduceDIte]
    have hch := Classical.choose_spec (hreach_uniq (off n (next n hn r0) (step n hn (next n hn r0) k)) hk').exists
    have hconv : ∀ m (hm : m = k) (hm' : m ≤ d0),
        Reaches n hn T r0 m w0 (Classical.choose (hreach_uniq m hm').exists) →
        Reaches n hn T r0 k w0 (Classical.choose (hreach_uniq m hm').exists) := by
      rintro _ rfl _ h; exact h
    exact hconv _ hoff hk' hch
  have hv_eq_of_reach : ∀ k (hk : k ≤ d0) c, Reaches n hn T r0 k w0 c → c = v (step n hn (next n hn r0) k) := by
    intro k hk c hc
    exact (hreach_uniq k hk).unique hc (hv_reach k hk)
  have hv0 : v (next n hn r0) = w0 := by
    have h := hv_eq_of_reach 0 (Nat.zero_le _) w0 ((reaches_zero n hn T r0 w0 w0).mpr rfl)
    simpa [step_zero] using h.symm
  have hvs0 : v s0 ≠ u0 := by
    intro heq
    have h := hv_reach d0 le_rfl
    change Reaches n hn T r0 d0 w0 (v s0) at h
    rw [heq] at h
    exact hfail w0 u0 ((hw0 w0).mpr rfl) ((hu0 u0).mpr rfl) h
  have hvs0_eq : u0 = !(v s0) := by
    revert hvs0; generalize v s0 = y; cases u0 <;> cases y <;> decide
  have hx_prop : ∀ (x : Fin n → Bool) (m : ℕ), m ≤ d0 →
      x (next n hn r0) = w0 →
      (∀ k < m, Uses n hn T x (step n hn (next n hn r0) k)) →
      x (step n hn (next n hn r0) m) = v (step n hn (next n hn r0) m) := by
    intro x m hm hx0 huses
    apply hv_eq_of_reach m hm
    refine ⟨fun k => x (step n hn (next n hn r0) k), by simpa [step_zero] using hx0, rfl, fun k hk => ?_⟩
    dsimp only
    rw [step_succ]
    exact huses k hk
  have hgap_row : ∀ k (hk : k < d0) a b,
      T (step n hn (next n hn r0) k, a, b) = true ↔
        a ≠ v (step n hn (next n hn r0) k) ∨ b = v (next n hn (step n hn (next n hn r0) k)) := by
    intro k hk a b
    let j := step n hn (next n hn r0) k
    have hvk_reach := hv_reach k (Nat.le_of_lt hk)
    have hvk1_reach := hv_reach (k + 1) hk
    obtain ⟨c, hc_reach, hc_T⟩ := (reaches_succ n hn T r0 k w0 _).mp hvk1_reach
    have hc_eq : c = v j := hv_eq_of_reach k (Nat.le_of_lt hk) c hc_reach
    rw [hc_eq, step_succ] at hc_T
    have hbad_edge : T (j, v j, !(v (next n hn j))) = false := by
      cases h : T (j, v j, !(v (next n hn j)))
      · rfl
      · exfalso
        have hr1 : Reaches n hn T r0 (k + 1) w0 (!(v (next n hn j))) :=
          (reaches_succ n hn T r0 k w0 _).mpr ⟨v j, hvk_reach, by exact h⟩
        have heq := hv_eq_of_reach (k + 1) hk (!(v (next n hn j))) hr1
        rw [step_succ] at heq
        change (!(v (next n hn j))) = v (next n hn j) at heq
        cases hvv : v (next n hn j) <;> simp [hvv] at heq
    constructor
    · intro hT_ab
      by_contra hnot
      push Not at hnot
      have ha : a = v j := hnot.1
      have hb : b = !(v (next n hn j)) := by
        have h2 := hnot.2; revert h2; generalize v (next n hn j) = y; cases b <;> cases y <;> decide
      change T (j, a, b) = true at hT_ab
      rw [ha, hb, hbad_edge] at hT_ab; cases hT_ab
    · intro hcond
      by_cases ha : a = v j
      · have hb : b = v (next n hn j) := hcond.resolve_left (not_not.mpr ha)
        change T (j, a, b) = true
        rw [ha, hb]; exact hc_T
      · change T (j, a, b) = true
        cases h : T (j, a, b)
        · exfalso
          obtain ⟨x, hxj, _, hrest⟩ := hmax (j, a, b) h
          have hj_ne_r0 : j ≠ r0 := by
            intro heq
            have hgood := hmatch_gap k hk
            change HasMatching n T j at hgood
            rw [heq] at hgood
            exact hr0 hgood
          have hxr0 : x (next n hn r0) = w0 :=
            (hw0 _).mp ⟨x r0, hrest r0 hj_ne_r0.symm⟩
          have hxj_eq := hx_prop x k (Nat.le_of_lt hk) hxr0 (fun k' hk' => by
            apply hrest
            intro heq
            have h1' := off_step n hn (first := next n hn r0) (lt_trans hk' (lt_trans hk hd0_lt))
            have h2' := off_step n hn (first := next n hn r0) (lt_trans hk hd0_lt)
            change step n hn (next n hn r0) k' = step n hn (next n hn r0) k at heq
            rw [heq] at h1'; omega)
          exact ha (hxj.symm.trans hxj_eq)
        · rfl
  by_cases hrs : r0 = s0
  · left
    refine ⟨r0, v, fun i a b => ?_⟩
    by_cases hir : i = r0
    · subst hir
      simp only [↓reduceIte]
      rw [hrect_r0, hw0, hv0]
      have hL_r0 : (∃ b', T (i, a, b') = true) ↔ a = u0 := by
        have h := hu0 a
        rwa [← hrs] at h
      rw [hL_r0, hvs0_eq, ← hrs]
      cases a <;> cases v i <;> simp
    · simp only [hir, ↓reduceIte]
      have hd0_eq : d0 = n - 1 := by
        have hstep_n1 : step n hn (next n hn r0) (n - 1) = r0 := by
          have h1' : next n hn (step n hn (next n hn r0) (n - 1)) = next n hn r0 := by
            rw [← step_succ, show n - 1 + 1 = n by omega, step_n]
          exact next_inj n hn h1'
        have h1' := off_step n hn (first := next n hn r0) hd0_lt
        have h2' := off_step n hn (first := next n hn r0) (by omega : n - 1 < n)
        change off n (next n hn r0) s0 = d0 at h1'
        rw [← hrs] at h1'
        rw [hstep_n1] at h2'
        omega
      have hk_lt : off n (next n hn r0) i < d0 := by
        have hlt := off_lt n hn (next n hn r0) i
        by_contra hge
        have heq : off n (next n hn r0) i = d0 := by omega
        have hst := step_off n hn (next n hn r0) i
        rw [heq] at hst
        exact hir (hst.symm.trans hrs.symm)
      have hrow := hgap_row (off n (next n hn r0) i) hk_lt a b
      simpa [step_off] using hrow
  · right
    have hd0_le : d0 + 2 ≤ n := by
      have hne_n1 : d0 ≠ n - 1 := by
        intro heq
        have h1' : next n hn s0 = next n hn r0 := by
          change next n hn (step n hn (next n hn r0) d0) = next n hn r0
          rw [← step_succ, heq, show n - 1 + 1 = n by omega, step_n]
        exact hrs (next_inj n hn h1').symm
      omega
    have hL_r0_full : ∀ a : Bool, ∃ b', T (r0, a, b') = true := by
      intro a
      refine ⟨w0, ?_⟩
      cases h : T (r0, a, w0)
      · exfalso
        obtain ⟨x, _, hxn, hrest⟩ := hmax (r0, a, w0) h
        have hxs0 := hx_prop x d0 le_rfl hxn (fun k hk => by
          apply hrest
          intro heq
          have hgood := hmatch_gap k hk
          rw [heq] at hgood
          exact hr0 hgood)
        have hus0 := hrest s0 (fun heq => hrs heq.symm)
        have hxs0_u0 : x s0 = u0 := (hu0 _).mp ⟨x (next n hn s0), hus0⟩
        exact hvs0 (hxs0.symm.trans hxs0_u0)
      · rfl
    have hR_s0_full : ∀ b : Bool, ∃ a', T (s0, a', b) = true := by
      intro b
      refine ⟨u0, ?_⟩
      cases h : T (s0, u0, b)
      · exfalso
        obtain ⟨x, hxs, _, hrest⟩ := hmax (s0, u0, b) h
        have hxr0 : x (next n hn r0) = w0 := (hw0 _).mp ⟨x r0, hrest r0 hrs⟩
        have hxs0 := hx_prop x d0 le_rfl hxr0 (fun k hk => by
          apply hrest
          intro heq
          have h1' := off_step n hn (first := next n hn r0) (lt_trans hk hd0_lt)
          have h2' := off_step n hn (first := next n hn r0) hd0_lt
          change off n (next n hn r0) s0 = d0 at h2'
          rw [heq, h2'] at h1'; omega)
        exact hvs0 (hxs0.symm.trans hxs)
      · rfl
    refine ⟨r0, d0 + 2, v, by omega, hd0_le, fun i a b => ?_⟩
    have hlen_ne1 : d0 + 2 ≠ 1 := by omega
    by_cases hle : d0 + 2 ≤ off n r0 i
    · simp only [hle, ↓reduceIte, iff_true]
      cases h : T (i, a, b)
      · exfalso
        obtain ⟨x, _, _, hrest⟩ := hmax (i, a, b) h
        have hi_ne_r0 : i ≠ r0 := fun heq => by
          rw [heq, (off_eq_zero_iff n hn r0 r0).mpr rfl] at hle; omega
        have hoff_s0 : off n r0 s0 = d0 + 1 := by
          have hs0_eq : s0 = step n hn r0 (d0 + 1) := by
            ext; simp only [s0, step, next, Nat.mod_add_mod]; congr 1; omega
          rw [hs0_eq, off_step n hn (by omega)]
        have hi_ne_s0 : i ≠ s0 := fun heq => by rw [heq, hoff_s0] at hle; omega
        have hxr0 : x (next n hn r0) = w0 := (hw0 _).mp ⟨x r0, hrest r0 hi_ne_r0.symm⟩
        have hxs0 := hx_prop x d0 le_rfl hxr0 (fun k hk => by
          apply hrest
          intro heq
          have hstep_eq : step n hn (next n hn r0) k = step n hn r0 (k + 1) := by
            ext; simp only [step, next, Nat.mod_add_mod]; congr 1; omega
          have hoff_k : off n r0 (step n hn (next n hn r0) k) = k + 1 := by
            rw [hstep_eq, off_step n hn (by omega)]
          dsimp only at heq
          rw [heq] at hoff_k; omega)
        have hxs0_u0 : x s0 = u0 := (hu0 _).mp ⟨x (next n hn s0), hrest s0 hi_ne_s0.symm⟩
        exact hvs0 (hxs0.symm.trans hxs0_u0)
      · rfl
    · simp only [hle, hlen_ne1, ↓reduceIte]
      by_cases h0 : off n r0 i = 0
      · simp only [h0, ↓reduceIte]
        have hir : i = r0 := (off_eq_zero_iff n hn r0 i).mp h0
        subst hir
        rw [hrect_r0, hw0, hv0]
        simp [hL_r0_full]
      · simp only [h0, ↓reduceIte]
        by_cases hlast : off n r0 i + 1 = d0 + 2
        · simp only [hlast, ↓reduceIte]
          have his : i = s0 := by
            have h1' := step_off n hn r0 i
            rw [show off n r0 i = d0 + 1 by omega] at h1'
            rw [← h1']
            ext; simp only [s0, step, next, Nat.mod_add_mod]; congr 1; omega
          subst his
          rw [hrect_s0, hu0, hvs0_eq]
          simp only [hR_s0_full, and_true]
          cases a <;> cases v s0 <;> simp
        · simp only [hlast, ↓reduceIte]
          let k := off n r0 i - 1
          have hk_lt : k < d0 := by omega
          have hi_eq : step n hn (next n hn r0) k = i := by
            have h1' : step n hn (next n hn r0) k = step n hn r0 (off n r0 i) := by
              ext; simp only [step, next, Nat.mod_add_mod]; congr 1; omega
            rw [h1', step_off]
          have hrow := hgap_row k hk_lt a b
          simpa [hi_eq] using hrow

theorem maximalFalse_to_three (n : ℕ) (hn : 0 < n) {T : Fin n × (Bool × Bool) → Bool}
    (hmf : MaximalFalse n hn T) :
    IsTwist n T ∨ (2 ≤ n ∧ (IsSingleton n hn T ∨ IsInterval n hn T)) := by
  classical
  obtain ⟨hinfeas, hmax⟩ := hmf
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨fun _ => true, by decide, fun i a b => ?_⟩
    have hi0 : i = (0 : Fin 1) := Fin.ext (by omega)
    subst hi0
    have h00 : T ((0 : Fin 1), false, false) = false := by
      cases h : T ((0 : Fin 1), false, false)
      · rfl
      · exfalso; apply hinfeas; refine ⟨fun _ => false, fun j => ?_⟩
        have hj : j = (0 : Fin 1) := Fin.ext (by omega); subst hj; exact h
    have h11 : T ((0 : Fin 1), true, true) = false := by
      cases h : T ((0 : Fin 1), true, true)
      · rfl
      · exfalso; apply hinfeas; refine ⟨fun _ => true, fun j => ?_⟩
        have hj : j = (0 : Fin 1) := Fin.ext (by omega); subst hj; exact h
    have h01 : T ((0 : Fin 1), false, true) = true := by
      cases h : T ((0 : Fin 1), false, true)
      · exfalso
        obtain ⟨x, hx1, hx2, _⟩ := hmax ((0 : Fin 1), false, true) h
        have hnx : next 1 (by decide) (0 : Fin 1) = (0 : Fin 1) := by decide
        rw [hnx, hx1] at hx2; cases hx2
      · rfl
    have h10 : T ((0 : Fin 1), true, false) = true := by
      cases h : T ((0 : Fin 1), true, false)
      · exfalso
        obtain ⟨x, hx1, hx2, _⟩ := hmax ((0 : Fin 1), true, false) h
        have hnx : next 1 (by decide) (0 : Fin 1) = (0 : Fin 1) := by decide
        rw [hnx, hx1] at hx2; cases hx2
      · rfl
    cases a <;> cases b
    · simp [h00]
    · simp [h01]
    · simp [h10]
    · simp [h11]
  have h2 : 2 ≤ n := by omega
  by_cases hempty : ∃ i0 : Fin n, ∀ a b : Bool, T (i0, a, b) = false
  · obtain ⟨i0, hi0⟩ := hempty
    right; refine ⟨h2, Or.inr ⟨i0, 1, fun _ => false, le_rfl, by omega, fun i a b => ?_⟩⟩
    by_cases hii0 : i = i0
    · subst hii0
      have h0 : off n i i = 0 := (off_eq_zero_iff n hn i i).mpr rfl
      simp [h0, hi0]
    · have hpos : 1 ≤ off n i0 i := by
        by_contra hlt
        exact hii0 ((off_eq_zero_iff n hn i0 i).mp (by omega))
      simp only [hpos, ↓reduceIte, iff_true]
      cases h : T (i, a, b)
      · exfalso
        obtain ⟨x, _, _, hrest⟩ := hmax (i, a, b) h
        have hu := hrest i0 (fun heq => hii0 heq.symm)
        rw [Uses, hi0] at hu; cases hu
      · rfl
  have hnonempty : ∀ i : Fin n, ∃ a b : Bool, T (i, a, b) = true := by
    intro i
    by_contra hno
    apply hempty
    refine ⟨i, fun a b => ?_⟩
    cases h : T (i, a, b)
    · rfl
    · exfalso; exact hno ⟨a, b, h⟩
  by_cases hallM : ∀ i : Fin n, HasMatching n T i
  · exact Or.inl (case_all_matching n hn hinfeas hallM)
  · right
    refine ⟨h2, ?_⟩
    let Bad : Finset (Fin n) := Finset.univ.filter fun i => ¬ HasMatching n T i
    have hBad_def : ∀ i, i ∈ Bad ↔ ¬ HasMatching n T i := fun i => by simp [Bad]
    have hBad_ne : Bad.Nonempty := by
      by_contra hne
      apply hallM
      intro i
      by_contra hno
      exact hne ⟨i, (hBad_def i).mpr hno⟩
    obtain ⟨r0, d0, hr0, hd0_lt, hs0, hmatch_gap, hfail⟩ :=
      exists_failed_gap n hn hinfeas Bad hBad_def hBad_ne
    exact failed_gap_classify n hn h2 hmax hnonempty r0 d0 ((hBad_def r0).mp hr0) hd0_lt
      ((hBad_def _).mp hs0) hmatch_gap hfail

end Main

end PEqualNP.Outside.L_lib_522_aux

theorem PEqualNP.Outside.L_lib_522 : (∀ (n : ℕ) (hn : 0 < n),
  let Row := Fin n
  let next := fun site : Row => (⟨(site.val + 1) % n, Nat.mod_lt _ hn⟩ : Row)
  let E := Row × (Bool × Bool)
  ∀ T : E → Bool,
    let uses := fun (x : Row → Bool) (i : Row) => T (i, x i, x (next i)) = true
    let maximalFalse :=
      (¬ ∃ x : Row → Bool, ∀ i, uses x i) ∧
      ∀ e : E, T e = false → ∃ x : Row → Bool,
        x e.1 = e.2.1 ∧ x (next e.1) = e.2.2 ∧ ∀ i, i ≠ e.1 → uses x i
    let twist := ∃ flip : Row → Bool,
      (Finset.univ.filter (fun j : Row => flip j = true)).card % 2 = 1 ∧
      ∀ i a b, T (i, a, b) = true ↔ b = xor a (flip i)
    let singleton := ∃ (marked : Row) (v : Row → Bool), ∀ i a b,
      T (i, a, b) = true ↔
        if i = marked then a ≠ v i ∧ b = v (next i) else a ≠ v i ∨ b = v (next i)
    let interval := ∃ (first : Row) (length : ℕ) (v : Row → Bool),
      1 ≤ length ∧ length ≤ n ∧ ∀ i a b,
        let offset := (i.val + n - first.val) % n
        T (i, a, b) = true ↔
          if length ≤ offset then True
          else if length = 1 then False
          else if offset = 0 then b = v (next i)
          else if offset + 1 = length then a ≠ v i
          else a ≠ v i ∨ b = v (next i)
    maximalFalse ↔ twist ∨ (2 ≤ n ∧ (singleton ∨ interval))) := by
  intro n hn
  dsimp only
  intro T
  constructor
  · exact PEqualNP.Outside.L_lib_522_aux.maximalFalse_to_three n hn
  · rintro (ht | ⟨h2, hs | hi⟩)
    · exact PEqualNP.Outside.L_lib_522_aux.twist_to_maximalFalse n hn ht
    · exact PEqualNP.Outside.L_lib_522_aux.singleton_to_maximalFalse n hn h2 hs
    · exact PEqualNP.Outside.L_lib_522_aux.interval_to_maximalFalse n hn h2 hi
