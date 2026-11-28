import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1434_aux

def piv (s j : ℕ) : ℕ := (2*(s/(2^(j+1)))+1)*2^j

theorem div_split (s J : ℕ) : s/2^J = 2*(s/2^(J+1)) + s/2^J%2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega

theorem piv_le (s J : ℕ) (h : s/2^J%2 = 1) : 1 ≤ piv s J ∧ piv s J ≤ s := by
  have h1 := div_split s J
  have h3 : 2*(s/2^(J+1))+1 = s/2^J := by omega
  unfold piv; rw [h3]
  have h4 : 1 ≤ s/2^J := by omega
  exact ⟨Nat.mul_pos h4 (Nat.two_pow_pos J), Nat.div_mul_le_self s (2^J)⟩

theorem piv_gt (s J : ℕ) (h : ¬ s/2^J%2 = 1) : s < piv s J := by
  have h1 := div_split s J
  have h3 : 2*(s/2^(J+1))+1 = s/2^J + 1 := by omega
  unfold piv; rw [h3]
  have e1 := Nat.div_add_mod s (2^J)
  have e2 := Nat.mod_lt s (Nat.two_pow_pos J)
  nlinarith

theorem piv_lt (a s J : ℕ) (hs : s < 4*2^a) (hJ : J < a+2) : piv s J < 4*2^a := by
  obtain ⟨c, hc⟩ : ∃ c, a + 1 = J + c := ⟨a+1-J, by omega⟩
  have hM : 4*2^a = 2^(J+1) * 2^c := by
    rw [← pow_add]
    have : J+1+c = a+2 := by omega
    rw [this]; ring
  have hq : s/2^(J+1) < 2^c := Nat.div_lt_of_lt_mul (by rw [← hM]; exact hs)
  have h5 : (s/2^(J+1) + 1) * 2^J ≤ 2^c * 2^J := Nat.mul_le_mul_right _ hq
  have h6 : (2:ℕ)^(J+1) = 2*2^J := by ring
  have hp := Nat.two_pow_pos J
  have hM' : 4*2^a = 2*(2^c*2^J) := by rw [hM, h6]; ring
  unfold piv
  rw [hM']
  generalize s/2^(J+1) = q at *
  nlinarith

theorem piv_aux (q q' J c : ℕ) : (2*q+1)*2^J ≠ (2*q'+1)*2^(J+c+1) := by
  intro h
  have e : (2*q'+1)*2^(J+c+1) = (2*((2*q'+1)*2^c))*2^J := by ring
  rw [e] at h
  have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos J) h
  omega

theorem piv_inj (s J J' : ℕ) (h : piv s J = piv s J') : J = J' := by
  unfold piv at h
  rcases lt_trichotomy J J' with h1 | h1 | h1
  · obtain ⟨c, rfl⟩ : ∃ c, J' = J + c + 1 := ⟨J' - J - 1, by omega⟩
    exact (piv_aux _ _ _ _ h).elim
  · exact h1
  · obtain ⟨c, rfl⟩ : ∃ c, J = J' + c + 1 := ⟨J - J' - 1, by omega⟩
    exact (piv_aux _ _ _ _ h.symm).elim

theorem bitsplit (n s t : ℕ) (hst : s < t) (ht : t < 2^(n+1)) :
    ∃ J, J ≤ n ∧ s/2^(J+1) = t/2^(J+1) ∧ ¬ s/2^J%2 = 1 ∧ t/2^J%2 = 1 := by
  have hn : s/2^(n+1) = t/2^(n+1) := by
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt ht]
  have hex : ∃ J, s/2^(J+1) = t/2^(J+1) := ⟨n, hn⟩
  classical
  obtain ⟨J, hJn, hJ, hmin⟩ : ∃ J, J ≤ n ∧ s/2^(J+1) = t/2^(J+1) ∧ ∀ m < J, ¬ s/2^(m+1) = t/2^(m+1) :=
    ⟨Nat.find hex, Nat.find_min' hex hn, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hne : s/2^J ≠ t/2^J := by
    cases J with
    | zero => intro h; simp at h; omega
    | succ m => exact hmin m (by omega)
  have hle : s/2^J ≤ t/2^J := Nat.div_le_div_right (by omega)
  have := div_split s J
  have := div_split t J
  refine ⟨J, hJn, hJ, ?_, ?_⟩ <;> omega

theorem dec_iff (p : Prop) [Decidable p] (v : Bool) : decide p = v ↔ (p ↔ v = true) := by
  cases v <;> simp

def PM (a d e : ℕ) (L : Fin (4*2^a) → Fin 3 → Fin e × Bool) (s : Fin (4*2^a)) (j : Fin 3)
    (v : Bool) (x : ℕ) : Prop :=
  (∃ o c, (s.val < 2*2^a ∧ o = 0 ∨ ¬ s.val < 2*2^a ∧ o = 2*e) ∧
      ((L s j).2 = v ∧ c = 1 ∨ (L s j).2 ≠ v ∧ c = 0) ∧ x = d + o + 2*(L s j).1.val + c)
  ∨ (((L s j).1.val < d ∧ (L s j).2 = true ∧ (s.val < 2*2^a ↔ v = true)) ∧ x = (L s j).1.val)
  ∨ (∃ k, k < 2 ∧ (j.val/2^k % 2 = 1 ↔ v = true) ∧ x = d+4*e+2*s.val+k)
  ∨ (∃ jj, jj < a+2 ∧ (s.val/2^jj % 2 = 1 ↔ v = true) ∧ x = d+4*e+2*(4*2^a) + piv s.val jj)

def CM (a d e : ℕ) (X : Finset ℕ) (x : ℕ) : Prop :=
  x ∈ X ∨ (d ≤ x ∧ x < d+2*e) ∨ (d+4*e ≤ x ∧ x < d+4*e+4*2^a) ∨
    ∃ j, 1 ≤ j ∧ j ≤ 2*2^a-1 ∧ x = d+4*e+2*(4*2^a)+j

theorem P_range {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s : Fin (4*2^a)) (j : Fin 3) (v : Bool)
    (x : ℕ) (hx : x ∈ pins s j v) : x < d+4*e+2*(4*2^a)+4*2^a := by
  have hs := s.isLt
  have hi := (L s j).1.isLt
  have hpos := Nat.two_pow_pos a
  rcases (hp s j v x).1 hx with ⟨o, c, ho, hc, rfl⟩ | ⟨⟨h1, -, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨jj, hjj, -, rfl⟩
  · have ho2 : o ≤ 2*e := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    have hc2 : c ≤ 1 := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    omega
  · omega
  · omega
  · have := piv_lt a s.val jj hs hjj; omega

theorem cut_range {a d e : ℕ} {X : Finset ℕ} (hXd : X ⊆ Finset.range d) (x : ℕ)
    (h : CM a d e X x) : x < d+4*e+2*(4*2^a)+4*2^a := by
  have hpos := Nat.two_pow_pos a
  rcases h with h | h | h | ⟨q, h1, h2, h3⟩
  · have := Finset.mem_range.1 (hXd h); omega
  · omega
  · omega
  · omega

theorem NP_disj {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s t : Fin (4*2^a)) (j k : Fin 3)
    (hts : t ≤ s) (hside : s.val < 2*2^a ↔ t.val < 2*2^a) (hjk : s = t → j = k)
    (hw : (L s j).1 = (L t k).1 → (L s j).2 = (L t k).2) (x : ℕ)
    (hN : x ∈ pins s j false) (hP : x ∈ pins t k true) : False := by
  have hs := s.isLt
  have ht := t.isLt
  have hi := (L s j).1.isLt
  have hi' := (L t k).1.isLt
  have hts' : t.val ≤ s.val := hts
  rcases (hp s j false x).1 hN with ⟨o, c, ho, hc, rfl⟩ | ⟨⟨h1, h2, h3⟩, rfl⟩ | ⟨k1, hk1, hb1, rfl⟩ | ⟨j1, hj1, hb1, rfl⟩
  · have ho2 : o ≤ 2*e := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    have hc2 : c ≤ 1 := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · have hc2' : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      have hoo : o = o' := by omega
      have hii : (L s j).1 = (L t k).1 := Fin.ext (by omega)
      have hbb := hw hii
      have hcc : c = c' := by omega
      rcases hc with ⟨hc1, rfl⟩ | ⟨hc1, rfl⟩ <;> rcases hc' with ⟨hc3, rfl⟩ | ⟨hc3, rfl⟩ <;> simp_all
    · omega
    · omega
    · omega
  · rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · omega
    · have a1 : ¬ s.val < 2*2^a := fun hh => Bool.false_ne_true (h3.1 hh)
      exact a1 (hside.2 (h3'.2 rfl))
    · omega
    · omega
  · rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · have ho2 : o' ≤ 2*e := by rcases ho' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      have hc2' : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      omega
    · omega
    · have hst : s = t := Fin.ext (by omega)
      have hkk : k1 = k2 := by omega
      have := hjk hst
      subst hst; subst hkk; subst this
      exact Bool.false_ne_true (hb1.1 (hb2.2 rfl))
    · omega
  · have g1 := piv_gt s.val j1 (fun hh => Bool.false_ne_true (hb1.1 hh))
    rcases (hp t k true _).1 hP with ⟨o', c', ho', hc', h⟩ | ⟨⟨h1', h2', h3'⟩, h⟩ | ⟨k2, hk2, hb2, h⟩ | ⟨j2, hj2, hb2, h⟩
    · have ho2 : o' ≤ 2*e := by rcases ho' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      have hc2' : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
      omega
    · omega
    · omega
    · have g2 := piv_le t.val j2 (hb2.2 rfl)
      omega

theorem consist {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    (Y : Fin (4*2^a) → Finset ℕ) (hY : Monotone Y) (s t : Fin (4*2^a)) (j k : Fin 3) (hst : s ≤ t)
    (hside : s.val < 2*2^a ↔ t.val < 2*2^a) (hPs : pins s j true ⊆ Y s)
    (hNt : Disjoint (pins t k false) (Y t)) (hi : (L s j).1 = (L t k).1) :
    (L s j).2 = (L t k).2 := by
  by_contra hne
  obtain ⟨o, ho⟩ : ∃ o, (s.val < 2*2^a ∧ o = 0 ∨ ¬ s.val < 2*2^a ∧ o = 2*e) := by
    by_cases h : s.val < 2*2^a
    · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨2*e, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨c, hc⟩ : ∃ c, ((L s j).2 = true ∧ c = 1 ∨ (L s j).2 ≠ true ∧ c = 0) := by
    cases (L s j).2 <;> simp
  have m1 : d + o + 2*(L s j).1.val + c ∈ pins s j true := (hp _ _ _ _).2 (Or.inl ⟨o, c, ho, hc, rfl⟩)
  have ho' : (t.val < 2*2^a ∧ o = 0 ∨ ¬ t.val < 2*2^a ∧ o = 2*e) := by
    rcases ho with ⟨h, e1⟩ | ⟨h, e1⟩
    · exact Or.inl ⟨hside.1 h, e1⟩
    · exact Or.inr ⟨fun h' => h (hside.2 h'), e1⟩
  have hc' : ((L t k).2 = false ∧ c = 1 ∨ (L t k).2 ≠ false ∧ c = 0) := by
    revert hc hne
    cases (L s j).2 <;> cases (L t k).2 <;> simp
  have m2 : d + o + 2*(L s j).1.val + c ∈ pins t k false :=
    (hp _ _ _ _).2 (Or.inl ⟨o, c, ho', hc', by rw [hi]⟩)
  exact Finset.disjoint_left.1 hNt m2 (hY hst (hPs m1))

theorem P_sub_cut {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (X : Finset ℕ) (s : Fin (4*2^a)) (j : Fin 3)
    (hs : s.val < 2*2^a)
    (hpub : (L s j).1.val < d → (L s j).2 = true → (L s j).1.val ∈ X) (x : ℕ)
    (hx : x ∈ pins s j true) : CM a d e X x := by
  have hi := (L s j).1.isLt
  rcases (hp s j true x).1 hx with ⟨o, c, ho, hc, rfl⟩ | ⟨⟨h1, h2, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨jj, hjj, hb, rfl⟩
  · have ho2 : o = 0 := by omega
    have hc2 : c ≤ 1 := by rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    exact Or.inr (Or.inl (by omega))
  · exact Or.inl (hpub h1 h2)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · have := piv_le s.val jj (hb.2 rfl)
    exact Or.inr (Or.inr (Or.inr ⟨_, this.1, by omega, rfl⟩))

theorem N_miss_cut {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (X : Finset ℕ) (hX : X ⊆ Finset.range d)
    (s : Fin (4*2^a)) (j : Fin 3) (hs : ¬ s.val < 2*2^a)
    (hpub : (L s j).1.val < d → (L s j).2 = true → (L s j).1.val ∉ X) (x : ℕ)
    (hx : x ∈ pins s j false) (hc : CM a d e X x) : False := by
  have hi := (L s j).1.isLt
  have hsl := s.isLt
  have hXd : ∀ y, y ∈ X → y < d := fun y h => Finset.mem_range.1 (hX h)
  rcases (hp s j false x).1 hx with ⟨o, c, ho, hc', rfl⟩ | ⟨⟨h1, h2, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨jj, hjj, hb, rfl⟩
  · have ho2 : o = 2*e := by omega
    have hc2 : c ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    rcases hc with h | h | h | ⟨q, _, _, h⟩
    · have := hXd _ h; omega
    · omega
    · omega
    · omega
  · rcases hc with h | h | h | ⟨q, _, _, h⟩
    · exact hpub h1 h2 h
    · omega
    · omega
    · omega
  · rcases hc with h | h | h | ⟨q, _, _, h⟩
    · have := hXd _ h; omega
    · omega
    · omega
    · omega
  · have := piv_gt s.val jj (fun hh => Bool.false_ne_true (hb.1 hh))
    rcases hc with h | h | h | ⟨q, _, _, h⟩
    · have := hXd _ h; omega
    · omega
    · omega
    · omega

theorem sat_of_chain {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3) (hY : Monotone Y)
    (S : Fin (4*2^a) → Prop) (hS : ∀ s t, S s → S t → (s.val < 2*2^a ↔ t.val < 2*2^a))
    (h : ∀ s, S s → pins s (v s) true ⊆ Y s ∧ Disjoint (pins s (v s) false) (Y s)) :
    ∃ w : Fin e → Bool, (∀ s, S s → w (L s (v s)).1 = (L s (v s)).2) ∧
      ∀ i, w i = true → ∃ s, S s ∧ L s (v s) = (i, true) := by
  classical
  refine ⟨fun i => decide (∃ s, S s ∧ L s (v s) = (i, true)), ?_, ?_⟩
  · intro s hs
    by_cases hb : (L s (v s)).2 = true
    · rw [hb, decide_eq_true_eq]; exact ⟨s, hs, Prod.ext rfl hb⟩
    · have hb0 : (L s (v s)).2 = false := by simpa using hb
      rw [hb0, decide_eq_false_iff_not]
      rintro ⟨t, ht, hLt⟩
      have hi : (L s (v s)).1 = (L t (v t)).1 := by rw [hLt]
      have hb' : (L t (v t)).2 = true := by rw [hLt]
      have : (L s (v s)).2 = (L t (v t)).2 := by
        rcases le_total s t with hst | hst
        · exact consist hp Y hY s t _ _ hst (hS s t hs ht) (h s hs).1 (h t ht).2 hi
        · exact (consist hp Y hY t s _ _ hst (hS t s ht hs) (h t ht).1 (h s hs).2 hi.symm).symm
      rw [hb0, hb'] at this; exact Bool.false_ne_true this
  · intro i hi; simpa using hi

theorem chainT_pos {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3) (hY : Monotone Y)
    (h : ∀ s : Fin (4*2^a), s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ Y s ⊆ cut X) :
    ∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
      ∀ i : Fin e, i.val < d → w i = true → i.val ∈ X := by
  obtain ⟨w, hw1, hw2⟩ := sat_of_chain hp Y v hY (fun s => s.val < 2*2^a)
    (fun s t hs ht => ⟨fun _ => ht, fun _ => hs⟩) (fun s hs => ⟨(h s hs).1.2.1, (h s hs).1.2.2⟩)
  refine ⟨w, fun s hs => ⟨v s, hw1 s hs⟩, fun i hid hwi => ?_⟩
  obtain ⟨s, hs, hL⟩ := hw2 i hwi
  have hm : i.val ∈ pins s (v s) true :=
    (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨by rw [hL]; exact hid, by rw [hL], ⟨fun _ => rfl, fun _ => hs⟩⟩, by rw [hL]⟩))
  rcases (hc X _).1 ((h s hs).2 ((h s hs).1.2.1 hm)) with h2 | h2 | h2 | ⟨q, _, _, h2⟩
  · exact h2
  · omega
  · omega
  · omega

theorem chainF_neg {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3) (hY : Monotone Y)
    (h : ∀ s : Fin (4*2^a), ¬ s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ cut X ⊆ Y s) :
    ∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), ¬ s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
      ∀ i : Fin e, i.val < d → w i = true → i.val ∉ X := by
  obtain ⟨w, hw1, hw2⟩ := sat_of_chain hp Y v hY (fun s => ¬ s.val < 2*2^a)
    (fun s t hs ht => ⟨fun h => absurd h hs, fun h => absurd h ht⟩)
    (fun s hs => ⟨(h s hs).1.2.1, (h s hs).1.2.2⟩)
  refine ⟨w, fun s hs => ⟨v s, hw1 s hs⟩, fun i hid hwi hiX => ?_⟩
  obtain ⟨s, hs, hL⟩ := hw2 i hwi
  have hm : i.val ∈ pins s (v s) false :=
    (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨by rw [hL]; exact hid, by rw [hL],
      ⟨fun h => absurd h hs, fun h => absurd h Bool.false_ne_true⟩⟩, by rw [hL]⟩))
  exact Finset.disjoint_left.1 (h s hs).1.2.2 hm ((h s hs).2 ((hc X _).2 (Or.inl hiX)))

theorem pos_chainT {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (hXd : X ⊆ Finset.range d) (w : Fin e → Bool)
    (hsat : ∀ s : Fin (4*2^a), s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2)
    (hX : ∀ i : Fin e, i.val < d → w i = true → i.val ∈ X) :
    ∃ (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3), Monotone Y ∧
      ∀ s : Fin (4*2^a), s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ Y s ⊆ cut X := by
  classical
  choose! v hv using hsat
  refine ⟨fun s => (cut X).filter (fun x => ∃ t, t ≤ s ∧ t.val < 2*2^a ∧ x ∈ pins t (v t) true), v, ?_, ?_⟩
  · intro s s' hss x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨hx1, t, ht, ht2, hx2⟩ := hx
    exact ⟨hx1, t, le_trans ht hss, ht2, hx2⟩
  · intro s hs
    refine ⟨⟨?_, ?_, ?_⟩, Finset.filter_subset _ _⟩
    · intro x hx
      exact Finset.mem_range.2 (cut_range hXd x ((hc X x).1 (Finset.mem_filter.1 hx).1))
    · intro x hx
      exact Finset.mem_filter.2 ⟨(hc X x).2 (P_sub_cut hp X s (v s) hs
        (fun h1 h2 => hX _ h1 (by rw [hv s hs]; exact h2)) x hx), s, le_refl s, hs, hx⟩
    · rw [Finset.disjoint_left]
      intro x hxN hxY
      obtain ⟨-, t, ht, ht2, hxP⟩ := Finset.mem_filter.1 hxY
      exact NP_disj hp s t (v s) (v t) ht ⟨fun _ => ht2, fun _ => hs⟩ (fun hst => by rw [hst])
        (fun hi => by rw [← hv s hs, ← hv t ht2, hi]) x hxN hxP

theorem neg_chainF {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) (X : Finset ℕ)
    (hXd : X ⊆ Finset.range d) (w : Fin e → Bool)
    (hsat : ∀ s : Fin (4*2^a), ¬ s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2)
    (hX : ∀ i : Fin e, i.val < d → w i = true → i.val ∉ X) :
    ∃ (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3), Monotone Y ∧
      ∀ s : Fin (4*2^a), ¬ s.val < 2*2^a →
      (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s)) ∧ cut X ⊆ Y s := by
  classical
  choose! v hv using hsat
  refine ⟨fun s => (Finset.range (d+4*e+2*(4*2^a)+4*2^a)).filter
    (fun x => x ∈ cut X ∨ ∃ t, t ≤ s ∧ ¬ t.val < 2*2^a ∧ x ∈ pins t (v t) true), v, ?_, ?_⟩
  · intro s s' hss x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨hx1, hx2 | ⟨t, ht, ht2, hx2⟩⟩ := hx
    · exact ⟨hx1, Or.inl hx2⟩
    · exact ⟨hx1, Or.inr ⟨t, le_trans ht hss, ht2, hx2⟩⟩
  · intro s hs
    refine ⟨⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
    · intro x hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (P_range hp s (v s) true x hx),
        Or.inr ⟨s, le_refl s, hs, hx⟩⟩
    · rw [Finset.disjoint_left]
      intro x hxN hxY
      rcases (Finset.mem_filter.1 hxY).2 with hcut | ⟨t, ht, ht2, hxP⟩
      · exact N_miss_cut hp X hXd s (v s) hs (fun h1 h2 => hX _ h1 (by rw [hv s hs]; exact h2))
          x hxN ((hc X x).1 hcut)
      · exact NP_disj hp s t (v s) (v t) ht ⟨fun h => absurd h hs, fun h => absurd h ht2⟩
          (fun hst => by rw [hst]) (fun hi => by rw [← hv s hs, ← hv t ht2, hi]) x hxN hxP
    · intro x hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (cut_range hXd x ((hc X x).1 hx)), Or.inl hx⟩

theorem conj2 {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s t : Fin (4*2^a)) (j k : Fin 3)
    (Y : Finset ℕ) (h1 : pins s j true ⊆ Y) (h1' : Disjoint (pins s j false) Y)
    (h2 : pins t k true ⊆ Y) (h2' : Disjoint (pins t k false) Y) : s = t ∧ j = k := by
  have key : ∀ (s t : Fin (4*2^a)) (j k : Fin 3), s.val < t.val → pins t k true ⊆ Y →
      Disjoint (pins s j false) Y → False := by
    intro s t j k hlt hP hN
    obtain ⟨J, hJ, hq, hbs, hbt⟩ := bitsplit (a+1) s.val t.val hlt
      (by have := t.isLt; rw [pow_succ, pow_succ]; omega)
    have hpiv : piv s.val J = piv t.val J := by unfold piv; rw [hq]
    have m1 : (d+4*e+2*(4*2^a) + piv s.val J) ∈ pins t k true :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inr ⟨J, by omega, ⟨fun _ => rfl, fun _ => hbt⟩, by rw [hpiv]⟩)))
    have m2 : (d+4*e+2*(4*2^a) + piv s.val J) ∈ pins s j false :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inr ⟨J, by omega,
        ⟨fun h => absurd h hbs, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    exact Finset.disjoint_left.1 hN m2 (hP m1)
  have hst : s = t := by
    rcases lt_trichotomy s.val t.val with h | h | h
    · exact (key s t j k h h2 h1').elim
    · exact Fin.ext h
    · exact (key t s k j h h1 h2').elim
  subst hst
  refine ⟨rfl, ?_⟩
  by_contra hjk
  have hbits : ∀ j k : Fin 3, j ≠ k → ∃ k0 : Fin 2, ((j.val/2^k0.val % 2 = 1 ∧ ¬ k.val/2^k0.val % 2 = 1) ∨
      (k.val/2^k0.val % 2 = 1 ∧ ¬ j.val/2^k0.val % 2 = 1)) := by decide
  obtain ⟨k0, hh | hh⟩ := hbits j k hjk
  · have m1 : d+4*e+2*s.val+k0.val ∈ pins s j true :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt, ⟨fun _ => rfl, fun _ => hh.1⟩, rfl⟩)))
    have m2 : d+4*e+2*s.val+k0.val ∈ pins s k false :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt,
        ⟨fun h => absurd h hh.2, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    exact Finset.disjoint_left.1 h2' m2 (h1 m1)
  · have m1 : d+4*e+2*s.val+k0.val ∈ pins s k true :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt, ⟨fun _ => rfl, fun _ => hh.1⟩, rfl⟩)))
    have m2 : d+4*e+2*s.val+k0.val ∈ pins s j false :=
      (hp _ _ _ _).2 (Or.inr (Or.inr (Or.inl ⟨k0.val, k0.isLt,
        ⟨fun h => absurd h hh.2, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    exact Finset.disjoint_left.1 h1' m2 (h2 m1)

theorem conj4 {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x)
    {cut : Finset ℕ → Finset ℕ} (hc : ∀ X x, x ∈ cut X ↔ CM a d e X x) :
    (∃ (Y : Fin (4*2^a) → Finset ℕ) (v : Fin (4*2^a) → Fin 3), Monotone Y ∧
      ∀ s : Fin (4*2^a), (Y s ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧ pins s (v s) true ⊆ Y s ∧
        Disjoint (pins s (v s) false) (Y s))) ↔
    ∃ X : Finset ℕ, X ⊆ Finset.range d ∧
      (∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
        ∀ i : Fin e, i.val < d → w i = true → i.val ∈ X) ∧
      (∃ w : Fin e → Bool, (∀ s : Fin (4*2^a), ¬ s.val < 2*2^a → ∃ j, w (L s j).1 = (L s j).2) ∧
        ∀ i : Fin e, i.val < d → w i = true → i.val ∉ X) := by
  classical
  have hpos := Nat.two_pow_pos a
  constructor
  · rintro ⟨Y, v, hY, h⟩
    have h2H : 2*2^a - 1 < 4*2^a := by omega
    let m : Fin (4*2^a) := ⟨2*2^a-1, h2H⟩
    let X : Finset ℕ := (Finset.range d).filter (fun x => x ∈ Y m)
    have hXd : X ⊆ Finset.range d := Finset.filter_subset _ _
    refine ⟨X, hXd,
      chainT_pos hp hc X (fun s => (Y s).filter (fun x => x ∈ cut X)) v ?_ ?_,
      chainF_neg hp hc X (fun s => (Finset.range (d+4*e+2*(4*2^a)+4*2^a)).filter
        (fun x => x ∈ Y s ∨ x ∈ cut X)) v ?_ ?_⟩
    · intro s s' hss x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hY hss hx.1, hx.2⟩
    · intro s hs
      refine ⟨⟨fun x hx => (h s).1 (Finset.mem_filter.1 hx).1, ?_, ?_⟩,
        fun x hx => (Finset.mem_filter.1 hx).2⟩
      · intro x hx
        refine Finset.mem_filter.2 ⟨(h s).2.1 hx, (hc X x).2 (P_sub_cut hp X s (v s) hs
          (fun h1 h2 => ?_) x hx)⟩
        have hm : (L s (v s)).1.val ∈ pins s (v s) true :=
          (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨h1, h2, ⟨fun _ => rfl, fun _ => hs⟩⟩, rfl⟩))
        have hsm : s ≤ m := Fin.le_def.2 (by show s.val ≤ 2*2^a-1; omega)
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, hY hsm ((h s).2.1 hm)⟩
      · rw [Finset.disjoint_left]
        intro x hxN hxY
        exact Finset.disjoint_left.1 (h s).2.2 hxN (Finset.mem_filter.1 hxY).1
    · intro s s' hss x hx
      simp only [Finset.mem_filter] at hx ⊢
      rcases hx with ⟨hx1, hx2 | hx2⟩
      · exact ⟨hx1, Or.inl (hY hss hx2)⟩
      · exact ⟨hx1, Or.inr hx2⟩
    · intro s hs
      refine ⟨⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
      · intro x hx
        exact Finset.mem_filter.2 ⟨(h s).1 ((h s).2.1 hx), Or.inl ((h s).2.1 hx)⟩
      · rw [Finset.disjoint_left]
        intro x hxN hxY
        rcases (Finset.mem_filter.1 hxY).2 with hy | hcut
        · exact Finset.disjoint_left.1 (h s).2.2 hxN hy
        · refine N_miss_cut hp X hXd s (v s) hs (fun h1 h2 hiX => ?_) x hxN ((hc X x).1 hcut)
          have hm : (L s (v s)).1.val ∈ pins s (v s) false :=
            (hp _ _ _ _).2 (Or.inr (Or.inl ⟨⟨h1, h2,
              ⟨fun h => absurd h hs, fun h => absurd h Bool.false_ne_true⟩⟩, rfl⟩))
          have hms : m ≤ s := Fin.le_def.2 (by show 2*2^a-1 ≤ s.val; omega)
          exact Finset.disjoint_left.1 (h s).2.2 hm (hY hms (Finset.mem_filter.1 hiX).2)
      · intro x hx
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (cut_range hXd x ((hc X x).1 hx)), Or.inr hx⟩
  · rintro ⟨X, hXd, ⟨w1, hs1, hX1⟩, ⟨w2, hs2, hX2⟩⟩
    obtain ⟨Y1, v1, m1, h1⟩ := pos_chainT hp hc X hXd w1 hs1 hX1
    obtain ⟨Y2, v2, m2, h2⟩ := neg_chainF hp hc X hXd w2 hs2 hX2
    refine ⟨fun s => if s.val < 2*2^a then Y1 s else Y2 s,
      fun s => if s.val < 2*2^a then v1 s else v2 s, ?_, ?_⟩
    · intro s t hst
      dsimp only
      by_cases hs : s.val < 2*2^a <;> by_cases ht : t.val < 2*2^a
      · rw [if_pos hs, if_pos ht]; exact m1 hst
      · rw [if_pos hs, if_neg ht]; exact (h1 s hs).2.trans (h2 t ht).2
      · exfalso; have : s.val ≤ t.val := hst; omega
      · rw [if_neg hs, if_neg ht]; exact m2 hst
    · intro s
      dsimp only
      by_cases hs : s.val < 2*2^a
      · simp only [if_pos hs]; exact (h1 s hs).1
      · simp only [if_neg hs]; exact (h2 s hs).1

theorem conj1 {a d e : ℕ} {L : Fin (4*2^a) → Fin 3 → Fin e × Bool}
    {pins : Fin (4*2^a) → Fin 3 → Bool → Finset ℕ}
    (hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x) (s : Fin (4*2^a)) (j : Fin 3)
    (U : Finset ℕ) (hU : ∀ x, x ∈ U ↔ x ∈ pins s j true ∨ x ∈ pins s j false) (c : ℕ)
    (hc1 : ((L s j).2 = true ∧ (L s j).1.val < d) → c = 1)
    (hc0 : ¬ ((L s j).2 = true ∧ (L s j).1.val < d) → c = 0) :
    Disjoint (pins s j true) (pins s j false) ∧ U ⊆ Finset.range (d+4*e+2*(4*2^a)+4*2^a) ∧
      U.card = a+6+c := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hP hN
    exact NP_disj hp s s j j le_rfl Iff.rfl (fun _ => rfl) (fun _ => rfl) x hN hP
  · intro x hx
    rcases (hU x).1 hx with h | h <;> exact Finset.mem_range.2 (P_range hp s j _ x h)
  · have hs := s.isLt
    have hi := (L s j).1.isLt
    obtain ⟨o, ho⟩ : ∃ o, (s.val < 2*2^a ∧ o = 0 ∨ ¬ s.val < 2*2^a ∧ o = 2*e) := by
      by_cases h : s.val < 2*2^a
      · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨2*e, Or.inr ⟨h, rfl⟩⟩
    have ho2 : o ≤ 2*e := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    obtain ⟨B, hB, hBc⟩ : ∃ B : Finset ℕ, (∀ x, x ∈ B ↔ ((L s j).2 = true ∧ (L s j).1.val < d) ∧ x = (L s j).1.val) ∧ B.card = c := by
      by_cases h : (L s j).2 = true ∧ (L s j).1.val < d
      · exact ⟨{(L s j).1.val}, fun x => by simp [h], by rw [hc1 h]; simp⟩
      · exact ⟨∅, fun x => by simp [h], by rw [hc0 h]; simp⟩
    set z := d + o + 2*(L s j).1.val with hz
    set q := d+4*e+2*s.val with hq
    set off := d+4*e+2*(4*2^a) with hoff
    have hE : U = (({z, z+1} ∪ B) ∪ ({q, q+1} ∪ (Finset.range (a+2)).image (fun J => off + piv s.val J))) := by
      ext x
      simp only [hU, hp, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_range, hB]
      constructor
      · rintro (h | h) <;>
        rcases h with ⟨o', c', ho', hc', rfl⟩ | ⟨⟨h1, h2, -⟩, rfl⟩ | ⟨k, hk, -, rfl⟩ | ⟨J, hJ, -, rfl⟩
        · have hc2 : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
          exact Or.inl (Or.inl (by omega))
        · exact Or.inl (Or.inr ⟨⟨h2, h1⟩, rfl⟩)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨J, hJ, rfl⟩)
        · have hc2 : c' ≤ 1 := by rcases hc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
          exact Or.inl (Or.inl (by omega))
        · exact Or.inl (Or.inr ⟨⟨h2, h1⟩, rfl⟩)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr ⟨J, hJ, rfl⟩)
      · rintro (((rfl | rfl) | ⟨⟨h2, h1⟩, rfl⟩) | ((rfl | rfl) | ⟨J, hJ, rfl⟩))
        · by_cases hb : (L s j).2 = true
          · exact Or.inr (Or.inl ⟨o, 0, ho, Or.inr ⟨by simp [hb], rfl⟩, rfl⟩)
          · exact Or.inl (Or.inl ⟨o, 0, ho, Or.inr ⟨hb, rfl⟩, rfl⟩)
        · by_cases hb : (L s j).2 = true
          · exact Or.inl (Or.inl ⟨o, 1, ho, Or.inl ⟨hb, rfl⟩, rfl⟩)
          · exact Or.inr (Or.inl ⟨o, 1, ho, Or.inl ⟨by simpa using hb, rfl⟩, rfl⟩)
        · by_cases hl : s.val < 2*2^a
          · exact Or.inl (Or.inr (Or.inl ⟨⟨h1, h2, ⟨fun _ => rfl, fun _ => hl⟩⟩, rfl⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨⟨h1, h2, ⟨fun h => absurd h hl, fun h => absurd h Bool.false_ne_true⟩⟩, rfl⟩))
        · by_cases hb : j.val/2^0%2 = 1
          · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨0, by omega, ⟨fun _ => rfl, fun _ => hb⟩, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0, by omega, ⟨fun h => absurd h hb, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
        · by_cases hb : j.val/2^1%2 = 1
          · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨1, by omega, ⟨fun _ => rfl, fun _ => hb⟩, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1, by omega, ⟨fun h => absurd h hb, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
        · by_cases hb : s.val/2^J%2 = 1
          · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨J, hJ, ⟨fun _ => rfl, fun _ => hb⟩, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨J, hJ, ⟨fun h => absurd h hb, fun h => absurd h Bool.false_ne_true⟩, rfl⟩)))
    have hBd : ∀ x, x ∈ B → x < d := fun x hx => by
      obtain ⟨⟨-, h⟩, rfl⟩ := (hB x).1 hx; exact h
    have hD : ((Finset.range (a+2)).image (fun J => off + piv s.val J)).card = a+2 := by
      rw [Finset.card_image_of_injective _ (fun J J' h => piv_inj s.val J J' (by simpa using h)),
        Finset.card_range]
    rw [hE, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint, hD, hBc, Finset.card_pair (by omega), Finset.card_pair (by omega)]
    · omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_range] at hx hx'
      obtain ⟨J, -, rfl⟩ := hx'
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      have := hBd x hx'
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_range] at hx hx'
      have h1 : x < d + 4*e := by
        rcases hx with (h | h) | h
        · omega
        · omega
        · have := hBd x h; omega
      rcases hx' with (h | h) | ⟨J, -, rfl⟩ <;> omega

end PEqualNP.Outside.L_lib_1434_aux

open PEqualNP.Outside.L_lib_1434_aux in
theorem PEqualNP.Outside.L_lib_1434 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let pivot := fun (s j : Nat) => (2*(s/(2^(j+1)))+1)*2^j
let path := fun (h s : Nat) (v : Bool) =>
  ((Finset.range h).filter (fun j => decide (s/2^j % 2=1)=v)).image (pivot s)
∀ (a d e : Nat) (L : Fin (4*2^a) → Fin 3 → Fin e × Bool), d ≤ e →
  let H := 2^a
  let M := 4*H
  let off := d+4*e+2*M
  let r := off+M
  let pins := fun (s : Fin M) (j : Fin 3) (v : Bool) =>
    let l := L s j
    let left := decide (s.val<2*H)
    let z := d+(if left then 0 else 2*e)+2*l.1.val
    let lit := z+(if l.2=v then 1 else 0)
    let pub : Finset Nat := if l.1.val<d ∧ l.2=true ∧ left=v then {l.1.val} else ∅
    let selector := ((Finset.range 2).filter (fun k => decide (j.val/2^k % 2=1)=v)).image (fun k => d+4*e+2*s.val+k)
    insert lit (pub ∪ selector ∪ (path (a+2) s.val v).image (fun i => off+i))
  let cell := fun (s : Fin M) (j : Fin 3) (Y : Finset Nat) =>
    Y ⊆ Finset.range r ∧ pins s j true ⊆ Y ∧ Disjoint (pins s j false) Y
  let sat := fun (side : Bool) (w : Fin e → Bool) =>
    ∀ s : Fin M, decide (s.val<2*H)=side → ∃ j, w (L s j).1=(L s j).2
  let pos := fun X : Finset Nat => ∃ w, sat true w ∧ ∀ i : Fin e, i.val<d → w i=true → i.val ∈ X
  let neg := fun X : Finset Nat => ∃ w, sat false w ∧ ∀ i : Fin e, i.val<d → w i=true → i.val ∉ X
  let cut := fun (X : Finset Nat) => X ∪ Finset.Ico d (d+2*e) ∪ Finset.Ico (d+4*e) (d+4*e+4*H) ∪
    (Finset.Icc 1 (2*H-1)).image (fun j => off+j)
  let chain := fun (side : Bool) (X : Finset Nat) =>
    ∃ (Y : Fin M → Finset Nat) (v : Fin M → Fin 3), Monotone Y ∧
      ∀ s, decide (s.val<2*H)=side → cell s (v s) (Y s) ∧ (if side then Y s ⊆ cut X else cut X ⊆ Y s)
  (∀ s j, Disjoint (pins s j true) (pins s j false) ∧ pins s j true ∪ pins s j false ⊆ Finset.range r ∧
    ((pins s j true ∪ pins s j false).card = a+6+(if (L s j).2=true ∧ (L s j).1.val<d then 1 else 0))) ∧
  (∀ s t j k Y, cell s j Y → cell t k Y → s=t ∧ j=k) ∧
  (∀ X ⊆ Finset.range d, (chain true X ↔ pos X) ∧ (chain false X ↔ neg X)) ∧
  ((∃ (Y : Fin M → Finset Nat) (v : Fin M → Fin 3), Monotone Y ∧ ∀ s, cell s (v s) (Y s)) ↔
    ∃ X ⊆ Finset.range d, pos X ∧ neg X)) := by
  intro pivot path a d e L hde H M off r pins cell sat pos neg cut chain
  have hp : ∀ s j v x, x ∈ pins s j v ↔ PM a d e L s j v x := by
    intro s j v x
    simp only [pins, path, pivot, PM, H, M, off, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range, dec_iff, or_assoc]
    refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
    · by_cases hs : s.val < 2*2^a <;> by_cases hb : (L s j).2 = v <;> simp [hs, hb]
    · split_ifs with h <;> simp [h]
    · constructor
      · rintro ⟨k, ⟨h1, h2⟩, rfl⟩; exact ⟨k, h1, h2, rfl⟩
      · rintro ⟨k, h1, h2, rfl⟩; exact ⟨k, ⟨h1, h2⟩, rfl⟩
    · constructor
      · rintro ⟨_, ⟨k, ⟨h1, h2⟩, rfl⟩, rfl⟩; exact ⟨k, h1, h2, rfl⟩
      · rintro ⟨k, h1, h2, rfl⟩; exact ⟨_, ⟨k, ⟨h1, h2⟩, rfl⟩, rfl⟩
  have hc : ∀ X x, x ∈ cut X ↔ CM a d e X x := by
    intro X x
    simp only [cut, CM, H, M, off, Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Finset.mem_Icc, or_assoc]
    refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr Iff.rfl ?_))
    constructor
    · rintro ⟨q, ⟨h1, h2⟩, rfl⟩; exact ⟨q, h1, h2, rfl⟩
    · rintro ⟨q, h1, h2, rfl⟩; exact ⟨q, ⟨h1, h2⟩, rfl⟩
  clear_value pins cut
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s j
    refine conj1 hp s j _ ?_ _ ?_ ?_
    · intro x; simp only [Finset.mem_union]
    · intro h; exact if_pos h
    · intro h; exact if_neg h
  · intro s t j k Y h1 h2
    exact conj2 hp s t j k Y h1.2.1 h1.2.2 h2.2.1 h2.2.2
  · intro X hXd
    simp only [chain, pos, neg, sat, cell, r, off, M, H, decide_eq_true_eq, decide_eq_false_iff_not,
      reduceIte, Bool.false_eq_true]
    exact ⟨⟨fun ⟨Y, v, hY, h⟩ => chainT_pos hp hc X Y v hY h,
        fun ⟨w, h1, h2⟩ => pos_chainT hp hc X hXd w h1 h2⟩,
      ⟨fun ⟨Y, v, hY, h⟩ => chainF_neg hp hc X Y v hY h,
        fun ⟨w, h1, h2⟩ => neg_chainF hp hc X hXd w h1 h2⟩⟩
  · simp only [pos, neg, sat, cell, r, off, M, H, decide_eq_true_eq, decide_eq_false_iff_not]
    exact conj4 hp hc
