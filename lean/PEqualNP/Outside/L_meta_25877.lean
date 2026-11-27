import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25877_aux

lemma testBit_nat_xor (x y t : ℕ) :
    (Nat.xor x y).testBit t = xor (x.testBit t) (y.testBit t) :=
  Nat.testBit_xor x y t

lemma nat_xor_comm (x y : ℕ) : Nat.xor x y = Nat.xor y x :=
  Nat.xor_comm x y

lemma zero_nat_xor (x : ℕ) : Nat.xor 0 x = x :=
  Nat.zero_xor x

lemma xor_cancel_left (x y : ℕ) : Nat.xor x (Nat.xor x y) = y := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [testBit_nat_xor]
  cases x.testBit t <;> cases y.testBit t <;> rfl

lemma xor_cancel_right (x y : ℕ) : Nat.xor (Nat.xor x y) y = x := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [testBit_nat_xor]
  cases x.testBit t <;> cases y.testBit t <;> rfl

lemma xor_cancel_mid (x y : ℕ) : Nat.xor y (Nat.xor x y) = x := by
  rw [nat_xor_comm x y]
  exact xor_cancel_left y x

lemma xor_three (u v z : ℕ) : Nat.xor (Nat.xor u z) (Nat.xor u v) = Nat.xor v z := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [testBit_nat_xor]
  cases u.testBit t <;> cases v.testBit t <;> cases z.testBit t <;> rfl

lemma xor_eq_zero_iff (x y : ℕ) : Nat.xor x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    have ht := congrArg (fun n => n.testBit t) h
    simp only [testBit_nat_xor, Nat.zero_testBit] at ht
    cases hx : x.testBit t <;> cases hy : y.testBit t <;> simp_all
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    intro t
    simp only [testBit_nat_xor, Nat.zero_testBit]
    cases x.testBit t <;> rfl

lemma xor_lt_two_pow_aux {x y k : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    Nat.xor x y < 2 ^ k :=
  Nat.xor_lt_two_pow hx hy

lemma mod_two_pow_eq_zero_iff (h m : ℕ) :
    h % 2 ^ m = 0 ↔ ∀ t < m, h.testBit t = false := by
  constructor
  · intro h0 t ht
    have h1 := congrArg (fun x => x.testBit t) h0
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit] at h1
    simpa [ht] using h1
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases ht : t < m
    · simp [ht, hall t ht]
    · simp [ht]

lemma mod_two_pow_eq_sub_one_iff (h m : ℕ) :
    h % 2 ^ m = 2 ^ m - 1 ↔ ∀ t < m, h.testBit t = true := by
  constructor
  · intro h1 t ht
    have h2 := congrArg (fun x => x.testBit t) h1
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one] at h2
    simpa [ht] using h2
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases ht : t < m
    · simp [ht, hall t ht]
    · simp [ht]

lemma bool_dist_eq (p1 p2 a b u1 u2 c : Bool)
    (hu : xor u1 u2 = c) (hP : xor p1 p2 = c) :
    (xor (xor p1 a) u1 ≠ xor (xor p2 b) u2) ↔ (a ≠ b) := by
  cases p1 <;> cases p2 <;> cases a <;> cases b <;> cases u1 <;> cases u2 <;> cases c <;> simp_all

lemma bool_dist_ne (p1 p2 u1 u2 c : Bool)
    (hu : xor u1 u2 = c) (hP : xor p1 p2 ≠ c) :
    xor (xor p1 false) u1 ≠ xor (xor p2 false) u2 := by
  cases p1 <;> cases p2 <;> cases u1 <;> cases u2 <;> cases c <;> simp_all

lemma bool_flip_ne (a b c : Bool) (h : xor a b = c) : xor (!a) b ≠ c := by
  cases a <;> cases b <;> cases c <;> simp_all

def E (k : ℕ) (D : Finset ℕ) (u : Fin (2 ^ k)) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun z : Fin (2 ^ k) => Nat.xor u.val z.val ∈ D)

def OV (D : Finset ℕ) (h : ℕ) : Finset ℕ :=
  D.filter (fun w => Nat.xor w h ∈ D)

def SD {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α) : Finset α :=
  Finset.univ.filter (fun z : α => decide (z ∈ A) ≠ decide (z ∈ B))

def tgt (k a : ℕ) (D : Finset ℕ) (x y : Fin (2 ^ k)) : Bool :=
  xor (x.val.testBit (y.val % 2 ^ a)) (decide (Nat.xor x.val y.val ∈ D))

lemma decide_mem_E_row (k : ℕ) (D : Finset ℕ) (u z : Fin (2 ^ k)) :
    decide (Nat.xor u.val z.val ∈ D) = decide (z ∈ E k D u) := by
  simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]

lemma decide_mem_E_col (k : ℕ) (D : Finset ℕ) (u z : Fin (2 ^ k)) :
    decide (Nat.xor z.val u.val ∈ D) = decide (z ∈ E k D u) := by
  rw [nat_xor_comm z.val u.val]
  exact decide_mem_E_row k D u z

lemma card_E {k : ℕ} {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k)) (u : Fin (2 ^ k)) :
    (E k D u).card = D.card := by
  refine Finset.card_bij (fun z _ => Nat.xor u.val z.val) ?_ ?_ ?_
  · intro z hz
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz
  · intro z1 _ z2 _ h
    apply Fin.ext
    have h1 := congrArg (fun w => Nat.xor u.val w) h
    simpa [xor_cancel_left] using h1
  · intro d hd
    have hdlt : d < 2 ^ k := Finset.mem_range.mp (hD hd)
    refine ⟨⟨Nat.xor u.val d, xor_lt_two_pow_aux u.isLt hdlt⟩, ?_, ?_⟩
    · simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [xor_cancel_left] using hd
    · exact xor_cancel_left u.val d

lemma card_inter_E {k : ℕ} {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k))
    (u v : Fin (2 ^ k)) :
    (E k D u ∩ E k D v).card = (OV D (Nat.xor u.val v.val)).card := by
  refine Finset.card_bij (fun z _ => Nat.xor u.val z.val) ?_ ?_ ?_
  · intro z hz
    simp only [E, OV, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    refine ⟨hz.1, ?_⟩
    rw [xor_three]
    exact hz.2
  · intro z1 _ z2 _ h
    apply Fin.ext
    have h1 := congrArg (fun w => Nat.xor u.val w) h
    simpa [xor_cancel_left] using h1
  · intro w hw
    simp only [OV, Finset.mem_filter] at hw
    have hwlt : w < 2 ^ k := Finset.mem_range.mp (hD hw.1)
    refine ⟨⟨Nat.xor u.val w, xor_lt_two_pow_aux u.isLt hwlt⟩, ?_, ?_⟩
    · simp only [E, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · simpa [xor_cancel_left] using hw.1
      · have hxv : Nat.xor v.val (Nat.xor u.val w) = Nat.xor w (Nat.xor u.val v.val) := by
          apply Nat.eq_of_testBit_eq
          intro t
          simp only [testBit_nat_xor]
          cases u.val.testBit t <;> cases v.val.testBit t <;> cases w.testBit t <;> rfl
        rw [hxv]
        exact hw.2
    · exact xor_cancel_left u.val w

lemma card_SD_eq {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α)
    (hAB : A.card = B.card) :
    (SD A B).card = 2 * (A.card - (A ∩ B).card) := by
  have hsd : SD A B = (A \ B) ∪ (B \ A) := by
    ext z
    simp only [SD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    by_cases ha : z ∈ A <;> by_cases hb : z ∈ B <;> simp [ha, hb]
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_sdiff] at hz1 hz2
    exact hz1.2 hz2.1
  rw [hsd, Finset.card_union_of_disjoint hdisj]
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  have h3 : (B ∩ A).card = (A ∩ B).card := by rw [Finset.inter_comm]
  have h4 : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  omega

lemma card_SD_E {k : ℕ} {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k))
    (u v : Fin (2 ^ k)) :
    (SD (E k D u) (E k D v)).card = 2 * (D.card - (OV D (Nat.xor u.val v.val)).card) := by
  have h1 := card_E hD u
  have h2 := card_E hD v
  have h3 := card_inter_E hD u v
  rw [card_SD_eq (E k D u) (E k D v) (by rw [h1, h2]), h1, h3]

lemma dist_eq_SD {α : Type} [Fintype α] [DecidableEq α]
    (F1 F2 P1 P2 Q1 Q2 u1 u2 : α → Bool) (A B : Finset α) (c : Bool)
    (hF1 : ∀ z, F1 z = xor (xor (P1 z) (Q1 z)) (u1 z))
    (hF2 : ∀ z, F2 z = xor (xor (P2 z) (Q2 z)) (u2 z))
    (hQ1 : ∀ z, Q1 z = decide (z ∈ A))
    (hQ2 : ∀ z, Q2 z = decide (z ∈ B))
    (hu : ∀ z, xor (u1 z) (u2 z) = c)
    (hP : ∀ z, xor (P1 z) (P2 z) = c) :
    (Finset.univ.filter (fun z : α => F1 z ≠ F2 z)).card = (SD A B).card := by
  congr 1
  ext z
  rw [Finset.mem_filter, SD, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [hF1 z, hF2 z, hQ1 z, hQ2 z]
  exact bool_dist_eq (P1 z) (P2 z) (decide (z ∈ A)) (decide (z ∈ B)) (u1 z) (u2 z) c (hu z) (hP z)

lemma dist_ge_sub {α : Type} [Fintype α] [DecidableEq α]
    (F1 F2 P1 P2 Q1 Q2 u1 u2 : α → Bool) (A B : Finset α) (c : Bool)
    (hF1 : ∀ z, F1 z = xor (xor (P1 z) (Q1 z)) (u1 z))
    (hF2 : ∀ z, F2 z = xor (xor (P2 z) (Q2 z)) (u2 z))
    (hQ1 : ∀ z, Q1 z = decide (z ∈ A))
    (hQ2 : ∀ z, Q2 z = decide (z ∈ B))
    (hu : ∀ z, xor (u1 z) (u2 z) = c) :
    (Finset.univ.filter (fun z : α => xor (P1 z) (P2 z) ≠ c)).card - (A.card + B.card) ≤
    (Finset.univ.filter (fun z : α => F1 z ≠ F2 z)).card := by
  set Bset := Finset.univ.filter (fun z : α => xor (P1 z) (P2 z) ≠ c)
  set Fset := Finset.univ.filter (fun z : α => F1 z ≠ F2 z)
  have hsub : Bset \ (A ∪ B) ⊆ Fset := by
    intro z hz
    simp only [Bset, Fset, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or] at hz ⊢
    rw [hF1 z, hF2 z, hQ1 z, hQ2 z, decide_eq_false hz.2.1, decide_eq_false hz.2.2]
    exact bool_dist_ne (P1 z) (P2 z) (u1 z) (u2 z) c (hu z) hz.1
  have h1 : (Bset \ (A ∪ B)).card ≤ Fset.card := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter Bset (A ∪ B)
  have h3 : (Bset ∩ (A ∪ B)).card ≤ (A ∪ B).card := Finset.card_le_card Finset.inter_subset_right
  have h4 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  omega

lemma card_filter_target_col_eq_SD {k a : ℕ} {D : Finset ℕ}
    (hD : D ⊆ Finset.range (2 ^ k)) (i j : Fin (2 ^ k))
    (hmod : i.val % (2 ^ a) = j.val % (2 ^ a)) :
    (Finset.univ.filter (fun x : Fin (2 ^ k) =>
      tgt k a D x i ≠ tgt k a D x j)).card =
    2 * (D.card - (OV D (Nat.xor i.val j.val)).card) := by
  have heq : (Finset.univ.filter (fun x : Fin (2 ^ k) =>
      tgt k a D x i ≠ tgt k a D x j)) = SD (E k D i) (E k D j) := by
    ext x
    rw [Finset.mem_filter, SD, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [← decide_mem_E_col k D i x, ← decide_mem_E_col k D j x]
    dsimp only [tgt]
    rw [hmod]
    cases x.val.testBit (j.val % (2 ^ a)) <;>
      cases decide (Nat.xor x.val i.val ∈ D) <;>
      cases decide (Nat.xor x.val j.val ∈ D) <;> simp
  rw [heq]
  exact card_SD_E hD i j

lemma part1_mp {k a : ℕ} (ha_pos : 0 < a) (hrk : 2 ^ a ≤ k)
    {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k)) {s : ℕ}
    (hsep : ∀ f g : Fin (2 ^ k) → Bool, ∀ i j : Fin (2 ^ k), i ≠ j →
      2 * s ≤ (Finset.univ.filter (fun z : Fin (2 ^ k) =>
        xor (tgt k a D i z) (xor (f i) (g z)) ≠
        xor (tgt k a D j z) (xor (f j) (g z)))).card ∧
      2 * s ≤ (Finset.univ.filter (fun z : Fin (2 ^ k) =>
        xor (tgt k a D z i) (xor (f z) (g i)) ≠
        xor (tgt k a D z j) (xor (f z) (g j)))).card)
    {h : ℕ} (hh_pos : 0 < h) (hh_lt : h < 2 ^ k)
    (hcond : h % 2 ^ a = 0 ∨ h % (2 ^ (2 ^ a)) = 2 ^ (2 ^ a) - 1) :
    (OV D h).card + s ≤ D.card := by
  have hr_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hN_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  have _ := ha_pos
  have _ := hrk
  let i0 : Fin (2 ^ k) := ⟨0, hN_pos⟩
  let j0 : Fin (2 ^ k) := ⟨h, hh_lt⟩
  have hi0j0 : i0 ≠ j0 := by
    intro heq
    have hval := congrArg Fin.val heq
    simp only [i0, j0] at hval
    omega
  have hxor_ij : Nat.xor i0.val j0.val = h := zero_nat_xor h
  have hov_le : (OV D h).card ≤ D.card := Finset.card_filter_le _ _
  have hsd := card_SD_E hD i0 j0
  rw [hxor_ij] at hsd
  rcases hcond with hmod0 | hmod1
  · have hcol := (hsep (fun _ => false) (fun _ => false) i0 j0 hi0j0).2
    have hP : ∀ z : Fin (2 ^ k),
        xor (z.val.testBit (i0.val % 2 ^ a)) (z.val.testBit (j0.val % 2 ^ a)) = false := by
      intro z
      have hm : i0.val % 2 ^ a = j0.val % 2 ^ a := by
        simp only [i0, j0, Nat.zero_mod, hmod0]
      rw [hm]
      cases z.val.testBit (j0.val % 2 ^ a) <;> rfl
    have hdist := dist_eq_SD
      (fun z : Fin (2 ^ k) => xor (tgt k a D z i0) (xor false false))
      (fun z : Fin (2 ^ k) => xor (tgt k a D z j0) (xor false false))
      (fun z : Fin (2 ^ k) => z.val.testBit (i0.val % 2 ^ a))
      (fun z : Fin (2 ^ k) => z.val.testBit (j0.val % 2 ^ a))
      (fun z : Fin (2 ^ k) => decide (Nat.xor z.val i0.val ∈ D))
      (fun z : Fin (2 ^ k) => decide (Nat.xor z.val j0.val ∈ D))
      (fun _ : Fin (2 ^ k) => xor false false)
      (fun _ : Fin (2 ^ k) => xor false false)
      (E k D i0) (E k D j0) false
      (fun _ => rfl) (fun _ => rfl)
      (decide_mem_E_col k D i0) (decide_mem_E_col k D j0)
      (fun _ => rfl) hP
    rw [hdist, hsd] at hcol
    omega
  · have hbits : ∀ t < 2 ^ a, h.testBit t = true :=
      (mod_two_pow_eq_sub_one_iff h (2 ^ a)).mp hmod1
    have hrow := (hsep (fun x => decide (x = j0)) (fun _ => false) i0 j0 hi0j0).1
    have hP : ∀ z : Fin (2 ^ k),
        xor (i0.val.testBit (z.val % 2 ^ a)) (j0.val.testBit (z.val % 2 ^ a)) = true := by
      intro z
      have hzt : z.val % 2 ^ a < 2 ^ a := Nat.mod_lt z.val hr_pos
      simp only [i0, j0, Nat.zero_testBit, hbits (z.val % 2 ^ a) hzt]
      rfl
    have hu : ∀ _ : Fin (2 ^ k),
        xor (xor (decide (i0 = j0)) false) (xor (decide (j0 = j0)) false) = true := by
      intro _
      simp [hi0j0]
    have hdist := dist_eq_SD
      (fun z : Fin (2 ^ k) => xor (tgt k a D i0 z) (xor (decide (i0 = j0)) false))
      (fun z : Fin (2 ^ k) => xor (tgt k a D j0 z) (xor (decide (j0 = j0)) false))
      (fun z : Fin (2 ^ k) => i0.val.testBit (z.val % 2 ^ a))
      (fun z : Fin (2 ^ k) => j0.val.testBit (z.val % 2 ^ a))
      (fun z : Fin (2 ^ k) => decide (Nat.xor i0.val z.val ∈ D))
      (fun z : Fin (2 ^ k) => decide (Nat.xor j0.val z.val ∈ D))
      (fun _ : Fin (2 ^ k) => xor (decide (i0 = j0)) false)
      (fun _ : Fin (2 ^ k) => xor (decide (j0 = j0)) false)
      (E k D i0) (E k D j0) true
      (fun _ => rfl) (fun _ => rfl)
      (decide_mem_E_row k D i0) (decide_mem_E_row k D j0)
      hu hP
    rw [hdist, hsd] at hrow
    omega

lemma part1_mpr_row {k a : ℕ} (ha_pos : 0 < a) (hrk : 2 ^ a ≤ k)
    {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k)) (hDcard : 4 * D.card ≤ 2 ^ k / 2 ^ a)
    {s : ℕ} (hs_le_D : s ≤ D.card)
    (hov : ∀ h : ℕ, 0 < h → h < 2 ^ k → (h % 2 ^ a = 0 ∨ h % (2 ^ (2 ^ a)) = 2 ^ (2 ^ a) - 1) →
      (OV D h).card + s ≤ D.card)
    (f g : Fin (2 ^ k) → Bool) (i j : Fin (2 ^ k)) (hij : i ≠ j) :
    2 * s ≤ (Finset.univ.filter (fun z : Fin (2 ^ k) =>
      xor (tgt k a D i z) (xor (f i) (g z)) ≠
      xor (tgt k a D j z) (xor (f j) (g z)))).card := by
  have ha_lt_r : a < 2 ^ a := Nat.lt_two_pow_self
  have ha_lt_k : a < k := lt_of_lt_of_le ha_lt_r hrk
  have hr_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hr_dvd_N : 2 ^ a ∣ 2 ^ k := Nat.pow_dvd_pow 2 (le_of_lt ha_lt_k)
  have hN_eq : (2 ^ k / 2 ^ a) * 2 ^ a = 2 ^ k := Nat.div_mul_cancel hr_dvd_N
  have hNr_le_N : 2 ^ k / 2 ^ a ≤ 2 ^ k := Nat.div_le_self (2 ^ k) (2 ^ a)
  have _ := ha_pos
  let h := Nat.xor i.val j.val
  have hh_pos : 0 < h := by
    by_contra h0
    have heq0 : h = 0 := by omega
    exact hij (Fin.ext ((xor_eq_zero_iff i.val j.val).mp heq0))
  have hh_lt : h < 2 ^ k := xor_lt_two_pow_aux i.isLt j.isLt
  have hEA : (E k D i).card = D.card := card_E hD i
  have hEB : (E k D j).card = D.card := card_E hD j
  have hsd : (SD (E k D i) (E k D j)).card = 2 * (D.card - (OV D h).card) := card_SD_E hD i j
  let c := xor (f i) (f j)
  have hu : ∀ z : Fin (2 ^ k), xor (xor (f i) (g z)) (xor (f j) (g z)) = c := by
    intro z
    simp only [c]
    cases f i <;> cases f j <;> cases g z <;> rfl
  have hPxor : ∀ z : Fin (2 ^ k),
      xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) =
        h.testBit (z.val % 2 ^ a) := by
    intro z
    exact (testBit_nat_xor i.val j.val (z.val % 2 ^ a)).symm
  by_cases hall0 : ∀ t < 2 ^ a, h.testBit t = false
  · have hmod0 : h % 2 ^ a = 0 := by
      rw [mod_two_pow_eq_zero_iff]
      intro t ht
      exact hall0 t (lt_trans ht ha_lt_r)
    have hbound := hov h hh_pos hh_lt (Or.inl hmod0)
    rcases (Bool.eq_false_or_eq_true c).symm with hc | hc
    · have hP : ∀ z : Fin (2 ^ k),
          xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) = false := by
        intro z
        rw [hPxor z]
        exact hall0 (z.val % 2 ^ a) (Nat.mod_lt z.val hr_pos)
      have hdist := dist_eq_SD
        (fun z : Fin (2 ^ k) => xor (tgt k a D i z) (xor (f i) (g z)))
        (fun z : Fin (2 ^ k) => xor (tgt k a D j z) (xor (f j) (g z)))
        (fun z : Fin (2 ^ k) => i.val.testBit (z.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => j.val.testBit (z.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => decide (Nat.xor i.val z.val ∈ D))
        (fun z : Fin (2 ^ k) => decide (Nat.xor j.val z.val ∈ D))
        (fun z : Fin (2 ^ k) => xor (f i) (g z))
        (fun z : Fin (2 ^ k) => xor (f j) (g z))
        (E k D i) (E k D j) false
        (fun _ => rfl) (fun _ => rfl)
        (decide_mem_E_row k D i) (decide_mem_E_row k D j)
        (fun z => (hu z).trans hc) hP
      rw [hdist, hsd]
      omega
    · have hge := dist_ge_sub
        (fun z : Fin (2 ^ k) => xor (tgt k a D i z) (xor (f i) (g z)))
        (fun z : Fin (2 ^ k) => xor (tgt k a D j z) (xor (f j) (g z)))
        (fun z : Fin (2 ^ k) => i.val.testBit (z.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => j.val.testBit (z.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => decide (Nat.xor i.val z.val ∈ D))
        (fun z : Fin (2 ^ k) => decide (Nat.xor j.val z.val ∈ D))
        (fun z : Fin (2 ^ k) => xor (f i) (g z))
        (fun z : Fin (2 ^ k) => xor (f j) (g z))
        (E k D i) (E k D j) true
        (fun _ => rfl) (fun _ => rfl)
        (decide_mem_E_row k D i) (decide_mem_E_row k D j)
        (fun z => (hu z).trans hc)
      have hB : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
          xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) ≠ true)).card =
          2 ^ k := by
        have hfuniv : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
            xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) ≠ true)) =
            Finset.univ := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          rw [hPxor z, hall0 (z.val % 2 ^ a) (Nat.mod_lt z.val hr_pos)]
          decide
        rw [hfuniv, Finset.card_univ, Fintype.card_fin]
      rw [hB, hEA, hEB] at hge
      omega
  · by_cases hall1 : ∀ t < 2 ^ a, h.testBit t = true
    · have hmod1 : h % (2 ^ (2 ^ a)) = 2 ^ (2 ^ a) - 1 :=
        (mod_two_pow_eq_sub_one_iff h (2 ^ a)).mpr hall1
      have hbound := hov h hh_pos hh_lt (Or.inr hmod1)
      rcases (Bool.eq_false_or_eq_true c).symm with hc | hc
      · have hge := dist_ge_sub
          (fun z : Fin (2 ^ k) => xor (tgt k a D i z) (xor (f i) (g z)))
          (fun z : Fin (2 ^ k) => xor (tgt k a D j z) (xor (f j) (g z)))
          (fun z : Fin (2 ^ k) => i.val.testBit (z.val % 2 ^ a))
          (fun z : Fin (2 ^ k) => j.val.testBit (z.val % 2 ^ a))
          (fun z : Fin (2 ^ k) => decide (Nat.xor i.val z.val ∈ D))
          (fun z : Fin (2 ^ k) => decide (Nat.xor j.val z.val ∈ D))
          (fun z : Fin (2 ^ k) => xor (f i) (g z))
          (fun z : Fin (2 ^ k) => xor (f j) (g z))
          (E k D i) (E k D j) false
          (fun _ => rfl) (fun _ => rfl)
          (decide_mem_E_row k D i) (decide_mem_E_row k D j)
          (fun z => (hu z).trans hc)
        have hB : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
            xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) ≠ false)).card =
            2 ^ k := by
          have hfuniv : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
              xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) ≠ false)) =
              Finset.univ := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            rw [hPxor z, hall1 (z.val % 2 ^ a) (Nat.mod_lt z.val hr_pos)]
            decide
          rw [hfuniv, Finset.card_univ, Fintype.card_fin]
        rw [hB, hEA, hEB] at hge
        omega
      · have hP : ∀ z : Fin (2 ^ k),
            xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) = true := by
          intro z
          rw [hPxor z]
          exact hall1 (z.val % 2 ^ a) (Nat.mod_lt z.val hr_pos)
        have hdist := dist_eq_SD
          (fun z : Fin (2 ^ k) => xor (tgt k a D i z) (xor (f i) (g z)))
          (fun z : Fin (2 ^ k) => xor (tgt k a D j z) (xor (f j) (g z)))
          (fun z : Fin (2 ^ k) => i.val.testBit (z.val % 2 ^ a))
          (fun z : Fin (2 ^ k) => j.val.testBit (z.val % 2 ^ a))
          (fun z : Fin (2 ^ k) => decide (Nat.xor i.val z.val ∈ D))
          (fun z : Fin (2 ^ k) => decide (Nat.xor j.val z.val ∈ D))
          (fun z : Fin (2 ^ k) => xor (f i) (g z))
          (fun z : Fin (2 ^ k) => xor (f j) (g z))
          (E k D i) (E k D j) true
          (fun _ => rfl) (fun _ => rfl)
          (decide_mem_E_row k D i) (decide_mem_E_row k D j)
          (fun z => (hu z).trans hc) hP
        rw [hdist, hsd]
        omega
    · have hex : ∃ t < 2 ^ a, h.testBit t ≠ c := by
        rcases (Bool.eq_false_or_eq_true c).symm with hc | hc
        · push_neg at hall0
          rcases hall0 with ⟨t, ht, hne⟩
          exact ⟨t, ht, by rw [hc]; exact hne⟩
        · push_neg at hall1
          rcases hall1 with ⟨t, ht, hne⟩
          exact ⟨t, ht, by rw [hc]; exact hne⟩
      rcases hex with ⟨t, ht_lt, htb⟩
      set Bset := Finset.univ.filter (fun z : Fin (2 ^ k) =>
        xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a)) ≠ c)
      have hBcard : 2 ^ k / 2 ^ a ≤ Bset.card := by
        have h1 : (Finset.univ : Finset (Fin (2 ^ k / 2 ^ a))).card ≤ Bset.card := by
          refine Finset.card_le_card_of_injOn
            (fun q : Fin (2 ^ k / 2 ^ a) => (⟨q.val * 2 ^ a + t, by
              have hq : q.val + 1 ≤ 2 ^ k / 2 ^ a := q.isLt
              have hmul : (q.val + 1) * 2 ^ a ≤ (2 ^ k / 2 ^ a) * 2 ^ a :=
                Nat.mul_le_mul_right (2 ^ a) hq
              rw [hN_eq, Nat.add_mul, Nat.one_mul] at hmul
              omega⟩ : Fin (2 ^ k))) ?_ ?_
          · intro q _
            simp only [Bset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
            have hqm : (q.val * 2 ^ a + t) % 2 ^ a = t := by
              rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
                Nat.mod_eq_of_lt ht_lt]
            rw [hqm, ← testBit_nat_xor]
            exact htb
          · intro q1 _ q2 _ heq
            have hval : q1.val * 2 ^ a + t = q2.val * 2 ^ a + t := congrArg Fin.val heq
            have hmul : q1.val * 2 ^ a = q2.val * 2 ^ a := by omega
            exact Fin.ext (Nat.mul_right_cancel hr_pos hmul)
        simpa [Finset.card_univ, Fintype.card_fin] using h1
      have hge := dist_ge_sub
        (fun z : Fin (2 ^ k) => xor (tgt k a D i z) (xor (f i) (g z)))
        (fun z : Fin (2 ^ k) => xor (tgt k a D j z) (xor (f j) (g z)))
        (fun z : Fin (2 ^ k) => i.val.testBit (z.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => j.val.testBit (z.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => decide (Nat.xor i.val z.val ∈ D))
        (fun z : Fin (2 ^ k) => decide (Nat.xor j.val z.val ∈ D))
        (fun z : Fin (2 ^ k) => xor (f i) (g z))
        (fun z : Fin (2 ^ k) => xor (f j) (g z))
        (E k D i) (E k D j) c
        (fun _ => rfl) (fun _ => rfl)
        (decide_mem_E_row k D i) (decide_mem_E_row k D j) hu
      rw [hEA, hEB] at hge
      have hBge : 2 ^ k / 2 ^ a - (D.card + D.card) ≤ Bset.card - (D.card + D.card) :=
        Nat.sub_le_sub_right hBcard (D.card + D.card)
      have h2s : 2 * s ≤ 2 ^ k / 2 ^ a - (D.card + D.card) := by omega
      exact le_trans h2s (le_trans hBge hge)

lemma part1_mpr_col {k a : ℕ} (ha_pos : 0 < a) (hrk : 2 ^ a ≤ k)
    {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k)) (hDcard : 4 * D.card ≤ 2 ^ k / 2 ^ a)
    {s : ℕ} (hs_le_D : s ≤ D.card)
    (hov : ∀ h : ℕ, 0 < h → h < 2 ^ k → (h % 2 ^ a = 0 ∨ h % (2 ^ (2 ^ a)) = 2 ^ (2 ^ a) - 1) →
      (OV D h).card + s ≤ D.card)
    (f g : Fin (2 ^ k) → Bool) (i j : Fin (2 ^ k)) (hij : i ≠ j) :
    2 * s ≤ (Finset.univ.filter (fun z : Fin (2 ^ k) =>
      xor (tgt k a D z i) (xor (f z) (g i)) ≠
      xor (tgt k a D z j) (xor (f z) (g j)))).card := by
  have ha_lt_r : a < 2 ^ a := Nat.lt_two_pow_self
  have ha_lt_k : a < k := lt_of_lt_of_le ha_lt_r hrk
  have hr_ge2 : 2 ≤ 2 ^ a := by
    have h1 : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha_pos
    simpa using h1
  have hr_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hr_dvd_N : 2 ^ a ∣ 2 ^ k := Nat.pow_dvd_pow 2 (le_of_lt ha_lt_k)
  have hN_eq : (2 ^ k / 2 ^ a) * 2 ^ a = 2 ^ k := Nat.div_mul_cancel hr_dvd_N
  have h2Nr_le_N : 2 * (2 ^ k / 2 ^ a) ≤ 2 ^ k := by
    have h1 : 2 * (2 ^ k / 2 ^ a) ≤ 2 ^ a * (2 ^ k / 2 ^ a) :=
      Nat.mul_le_mul_right (2 ^ k / 2 ^ a) hr_ge2
    have h2 : 2 ^ a * (2 ^ k / 2 ^ a) = 2 ^ k := by rw [Nat.mul_comm, hN_eq]
    omega
  have hNr_le_N : 2 ^ k / 2 ^ a ≤ 2 ^ k := Nat.div_le_self (2 ^ k) (2 ^ a)
  let h := Nat.xor i.val j.val
  have hh_pos : 0 < h := by
    by_contra h0
    have heq0 : h = 0 := by omega
    exact hij (Fin.ext ((xor_eq_zero_iff i.val j.val).mp heq0))
  have hh_lt : h < 2 ^ k := xor_lt_two_pow_aux i.isLt j.isLt
  have hEA : (E k D i).card = D.card := card_E hD i
  have hEB : (E k D j).card = D.card := card_E hD j
  have hsd : (SD (E k D i) (E k D j)).card = 2 * (D.card - (OV D h).card) := card_SD_E hD i j
  let c := xor (g i) (g j)
  have hu : ∀ z : Fin (2 ^ k), xor (xor (f z) (g i)) (xor (f z) (g j)) = c := by
    intro z
    simp only [c]
    cases f z <;> cases g i <;> cases g j <;> rfl
  by_cases hmod : i.val % 2 ^ a = j.val % 2 ^ a
  · have hmod0 : h % 2 ^ a = 0 := by
      rw [mod_two_pow_eq_zero_iff]
      intro t ht
      have hi_bit : i.val.testBit t = (i.val % 2 ^ a).testBit t := by
        rw [Nat.testBit_mod_two_pow]
        simp [ht]
      have hj_bit : j.val.testBit t = (j.val % 2 ^ a).testBit t := by
        rw [Nat.testBit_mod_two_pow]
        simp [ht]
      have heq_bit : i.val.testBit t = j.val.testBit t := by
        rw [hi_bit, hj_bit]
        exact congrArg (fun x => x.testBit t) hmod
      simp only [h, testBit_nat_xor, heq_bit]
      cases j.val.testBit t <;> rfl
    have hbound := hov h hh_pos hh_lt (Or.inl hmod0)
    rcases (Bool.eq_false_or_eq_true c).symm with hc | hc
    · have hP : ∀ z : Fin (2 ^ k),
          xor (z.val.testBit (i.val % 2 ^ a)) (z.val.testBit (j.val % 2 ^ a)) = false := by
        intro z
        rw [hmod]
        cases z.val.testBit (j.val % 2 ^ a) <;> rfl
      have hdist := dist_eq_SD
        (fun z : Fin (2 ^ k) => xor (tgt k a D z i) (xor (f z) (g i)))
        (fun z : Fin (2 ^ k) => xor (tgt k a D z j) (xor (f z) (g j)))
        (fun z : Fin (2 ^ k) => z.val.testBit (i.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => z.val.testBit (j.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => decide (Nat.xor z.val i.val ∈ D))
        (fun z : Fin (2 ^ k) => decide (Nat.xor z.val j.val ∈ D))
        (fun z : Fin (2 ^ k) => xor (f z) (g i))
        (fun z : Fin (2 ^ k) => xor (f z) (g j))
        (E k D i) (E k D j) false
        (fun _ => rfl) (fun _ => rfl)
        (decide_mem_E_col k D i) (decide_mem_E_col k D j)
        (fun z => (hu z).trans hc) hP
      rw [hdist, hsd]
      omega
    · have hge := dist_ge_sub
        (fun z : Fin (2 ^ k) => xor (tgt k a D z i) (xor (f z) (g i)))
        (fun z : Fin (2 ^ k) => xor (tgt k a D z j) (xor (f z) (g j)))
        (fun z : Fin (2 ^ k) => z.val.testBit (i.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => z.val.testBit (j.val % 2 ^ a))
        (fun z : Fin (2 ^ k) => decide (Nat.xor z.val i.val ∈ D))
        (fun z : Fin (2 ^ k) => decide (Nat.xor z.val j.val ∈ D))
        (fun z : Fin (2 ^ k) => xor (f z) (g i))
        (fun z : Fin (2 ^ k) => xor (f z) (g j))
        (E k D i) (E k D j) true
        (fun _ => rfl) (fun _ => rfl)
        (decide_mem_E_col k D i) (decide_mem_E_col k D j)
        (fun z => (hu z).trans hc)
      have hB : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
          xor (z.val.testBit (i.val % 2 ^ a)) (z.val.testBit (j.val % 2 ^ a)) ≠ true)).card =
          2 ^ k := by
        have hfuniv : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
            xor (z.val.testBit (i.val % 2 ^ a)) (z.val.testBit (j.val % 2 ^ a)) ≠ true)) =
            Finset.univ := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          rw [hmod]
          cases z.val.testBit (j.val % 2 ^ a) <;> decide
        rw [hfuniv, Finset.card_univ, Fintype.card_fin]
      rw [hB, hEA, hEB] at hge
      omega
  · let u := i.val % 2 ^ a
    let v := j.val % 2 ^ a
    have huv : u ≠ v := hmod
    have hu_lt_k : u < k := lt_of_lt_of_le (Nat.mod_lt i.val hr_pos) hrk
    have h2u_lt : 2 ^ u < 2 ^ k := Nat.pow_lt_pow_right (by omega) hu_lt_k
    let flipU : Fin (2 ^ k) → Fin (2 ^ k) := fun z =>
      ⟨Nat.xor z.val (2 ^ u), xor_lt_two_pow_aux z.isLt h2u_lt⟩
    have hflip_inv : ∀ z : Fin (2 ^ k), flipU (flipU z) = z := by
      intro z
      apply Fin.ext
      exact xor_cancel_right z.val (2 ^ u)
    set Bset := Finset.univ.filter (fun z : Fin (2 ^ k) =>
      xor (z.val.testBit u) (z.val.testBit v) ≠ c)
    have hle_B : (Finset.univ \ Bset).card ≤ Bset.card := by
      refine Finset.card_le_card_of_injOn flipU ?_ ?_
      · intro z hz
        simp only [Bset, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter,
          Finset.mem_univ, true_and, not_not] at hz ⊢
        have hfu : (flipU z).val.testBit u = !(z.val.testBit u) := by
          have hbit1 : (2 ^ u).testBit u = true := by
            rw [Nat.testBit_two_pow]
            simp
          simp only [flipU, testBit_nat_xor, hbit1]
          cases z.val.testBit u <;> rfl
        have hfv : (flipU z).val.testBit v = z.val.testBit v := by
          have hbit0 : (2 ^ u).testBit v = false := by
            rw [Nat.testBit_two_pow]
            simp [huv, Ne.symm huv]
          simp only [flipU, testBit_nat_xor, hbit0]
          cases z.val.testBit v <;> rfl
        rw [hfu, hfv]
        exact bool_flip_ne _ _ _ hz
      · intro z1 _ z2 _ heq
        have h1 := congrArg flipU heq
        simpa [hflip_inv] using h1
    have hsum : (Finset.univ \ Bset).card + Bset.card = 2 ^ k := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Bset)
      simpa [Finset.card_univ, Fintype.card_fin] using h1
    have hBcard : 2 ^ k / 2 ^ a ≤ Bset.card := by omega
    have hge := dist_ge_sub
      (fun z : Fin (2 ^ k) => xor (tgt k a D z i) (xor (f z) (g i)))
      (fun z : Fin (2 ^ k) => xor (tgt k a D z j) (xor (f z) (g j)))
      (fun z : Fin (2 ^ k) => z.val.testBit u)
      (fun z : Fin (2 ^ k) => z.val.testBit v)
      (fun z : Fin (2 ^ k) => decide (Nat.xor z.val i.val ∈ D))
      (fun z : Fin (2 ^ k) => decide (Nat.xor z.val j.val ∈ D))
      (fun z : Fin (2 ^ k) => xor (f z) (g i))
      (fun z : Fin (2 ^ k) => xor (f z) (g j))
      (E k D i) (E k D j) c
      (fun _ => rfl) (fun _ => rfl)
      (decide_mem_E_col k D i) (decide_mem_E_col k D j) hu
    rw [hEA, hEB] at hge
    have hBge : 2 ^ k / 2 ^ a - (D.card + D.card) ≤ Bset.card - (D.card + D.card) :=
      Nat.sub_le_sub_right hBcard (D.card + D.card)
    have h2s : 2 * s ≤ 2 ^ k / 2 ^ a - (D.card + D.card) := by omega
    exact le_trans h2s (le_trans hBge hge)

lemma part2 {k a : ℕ} (ha_pos : 0 < a) (hrk : 2 ^ a ≤ k)
    {D : Finset ℕ} (hD : D ⊆ Finset.range (2 ^ k)) :
    ∃ i j : Fin (2 ^ k), i ≠ j ∧ i.val % 2 ^ a = j.val % 2 ^ a ∧
      (Finset.univ.filter (fun x : Fin (2 ^ k) => tgt k a D x i ≠ tgt k a D x j)).card ≤
        2 * (if D.card ≤ 2 ^ a then D.card else D.card - 2) := by
  have ha_lt_r : a < 2 ^ a := Nat.lt_two_pow_self
  have ha_lt_k : a < k := lt_of_lt_of_le ha_lt_r hrk
  have hr_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hN_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hr_lt_N : 2 ^ a < 2 ^ k := Nat.pow_lt_pow_right (by omega) ha_lt_k
  have _ := ha_pos
  by_cases hle : D.card ≤ 2 ^ a
  · refine ⟨⟨0, hN_pos⟩, ⟨2 ^ a, hr_lt_N⟩, ?_, ?_, ?_⟩
    · intro heq
      have hval : 0 = 2 ^ a := congrArg Fin.val heq
      omega
    · simp [Nat.zero_mod, Nat.mod_self]
    · have hcard := card_filter_target_col_eq_SD (a := a) hD ⟨0, hN_pos⟩ ⟨2 ^ a, hr_lt_N⟩
        (by simp [Nat.zero_mod, Nat.mod_self])
      simp only [hle, ↓reduceIte]
      rw [hcard]
      omega
  · have hgt : 2 ^ a < D.card := by omega
    have hcard_lt : (Finset.univ : Finset (Fin (2 ^ a))).card < D.card := by
      simpa [Finset.card_univ, Fintype.card_fin] using hgt
    obtain ⟨d1, hd1, d2, hd2, hd12, hmod_fin⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt
        (f := fun d : ℕ => (⟨d % 2 ^ a, Nat.mod_lt d hr_pos⟩ : Fin (2 ^ a)))
        (fun _ _ => Finset.mem_univ _)
    have hd1_lt : d1 < 2 ^ k := Finset.mem_range.mp (hD hd1)
    have hd2_lt : d2 < 2 ^ k := Finset.mem_range.mp (hD hd2)
    have hmod_eq : d1 % 2 ^ a = d2 % 2 ^ a := congrArg Fin.val hmod_fin
    refine ⟨⟨d1, hd1_lt⟩, ⟨d2, hd2_lt⟩, ?_, hmod_eq, ?_⟩
    · intro heq
      exact hd12 (congrArg Fin.val heq)
    · have hcard := card_filter_target_col_eq_SD (a := a) hD ⟨d1, hd1_lt⟩ ⟨d2, hd2_lt⟩ hmod_eq
      have hsub_ov : ({d1, d2} : Finset ℕ) ⊆ OV D (Nat.xor d1 d2) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [OV, Finset.mem_filter]
        rcases hw with rfl | rfl
        · refine ⟨hd1, ?_⟩
          rw [xor_cancel_left]
          exact hd2
        · refine ⟨hd2, ?_⟩
          rw [xor_cancel_mid]
          exact hd1
      have hov_ge2 : 2 ≤ (OV D (Nat.xor d1 d2)).card := by
        have hpair : ({d1, d2} : Finset ℕ).card = 2 := Finset.card_pair hd12
        calc
          2 = ({d1, d2} : Finset ℕ).card := hpair.symm
          _ ≤ (OV D (Nat.xor d1 d2)).card := Finset.card_le_card hsub_ov
      dsimp only at hcard
      simp only [hle, ↓reduceIte]
      rw [hcard]
      omega

end PEqualNP.Outside.L_meta_25877_aux

theorem PEqualNP.Outside.L_meta_25877 : (∀ k a : ℕ, (0 < a ∧ 2^a ≤ k) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  let target := fun (D : Finset ℕ) (x y : I) =>
    xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
  let separated := fun (D : Finset ℕ) (d : ℕ) =>
    ∀ f g : I → Bool,
      let T := fun x y : I => xor (target D x y) (xor (f x) (g y))
      ∀ i j : I, i ≠ j →
        d ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
        d ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card
  ∀ D : Finset ℕ, D ⊆ Finset.range N → 4*D.card ≤ N/r →
    (∀ s : ℕ, separated D (2*s) ↔
      ∀ h : ℕ, 0 < h → h < N → (h % r = 0 ∨ h % (2^r) = 2^r-1) →
        (D.filter (fun z => Nat.xor z h ∈ D)).card + s ≤ D.card) ∧
    ∃ i j : I, i ≠ j ∧ i.val % r = j.val % r ∧
      (Finset.univ.filter (fun x : I => target D x i ≠ target D x j)).card ≤
        2*(if D.card ≤ r then D.card else D.card-2)) := by
  intro k a ⟨ha_pos, hrk⟩ N r I target separated D hD hDcard
  have ha_lt_k : a < k := lt_of_lt_of_le Nat.lt_two_pow_self hrk
  have hr_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hr_lt_N : 2 ^ a < 2 ^ k := Nat.pow_lt_pow_right (by omega) ha_lt_k
  constructor
  · intro s
    constructor
    · intro hsep h hh_pos hh_lt hcond
      exact PEqualNP.Outside.L_meta_25877_aux.part1_mp ha_pos hrk hD hsep hh_pos hh_lt hcond
    · intro hov
      have hs_le_D : s ≤ D.card := by
        have h1 := hov (2 ^ a) hr_pos hr_lt_N (Or.inl (Nat.mod_self (2 ^ a)))
        omega
      intro f g T i j hij
      exact ⟨
        PEqualNP.Outside.L_meta_25877_aux.part1_mpr_row ha_pos hrk hD hDcard hs_le_D hov f g i j hij,
        PEqualNP.Outside.L_meta_25877_aux.part1_mpr_col ha_pos hrk hD hDcard hs_le_D hov f g i j hij⟩
  · exact PEqualNP.Outside.L_meta_25877_aux.part2 ha_pos hrk hD
