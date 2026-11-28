import Mathlib

namespace PEqualNP.Outside.L_meta_38526

theorem F_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem ne_zero_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  rcases F_cases x with h' | h'
  · exact absurd h' h
  · exact h'

theorem add_self' (x : ZMod 2) : x + x = 0 := by
  rcases F_cases x with h | h <;> subst h <;> decide

def det2 (M : Fin 2 → Fin 2 → ZMod 2) : ZMod 2 := M 0 0 * M 1 1 - M 0 1 * M 1 0

def Good (H0 H1 : Fin 2 → Fin 2 → ZMod 2) : Prop :=
  ∃ e f g h : ZMod 2, (∃ r r' : Fin 2, e * H0 r r' + f * H1 r r' ≠ 0) ∧
    det2 (fun r r' => g * H0 r r' + h * H1 r r') ≠ 0 ∧
    det2 (fun r r' => (g + e) * H0 r r' + (h + f) * H1 r r') ≠ 0

theorem dep_key : ∀ a b c d : ZMod 2, (a ≠ 0 ∨ b ≠ 0) → a * d - b * c = 0 →
    ∃ l : ZMod 2, c = l * a ∧ d = l * b := by decide

theorem span_of_det {ι : Type} (J : Finset ι) (β : ι → ZMod 2) (p q : ι → Fin 2 → ZMod 2)
    (hdet : det2 (fun r r' => ∑ i ∈ J, β i * p i r * q i r') ≠ 0) :
    ∃ i1 ∈ J, ∃ i2 ∈ J, p i1 0 * p i2 1 - p i1 1 * p i2 0 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hdet
  by_cases hz : ∃ i ∈ J, p i ≠ 0
  · obtain ⟨i0, hi0, hne⟩ := hz
    have hw : p i0 0 ≠ 0 ∨ p i0 1 ≠ 0 := by
      by_contra hh
      push_neg at hh
      apply hne
      funext r
      fin_cases r
      · exact hh.1
      · exact hh.2
    have hlam : ∀ i ∈ J, ∃ l : ZMod 2, p i 0 = l * p i0 0 ∧ p i 1 = l * p i0 1 :=
      fun i hi => dep_key _ _ _ _ hw (hcon i0 hi0 i hi)
    choose! l hl using hlam
    have hN : ∀ r r', ∑ i ∈ J, β i * p i r * q i r' = p i0 r * ∑ i ∈ J, β i * l i * q i r' := by
      intro r r'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hpr : p i r = l i * p i0 r := by
        fin_cases r
        · exact (hl i hi).1
        · exact (hl i hi).2
      rw [hpr]
      ring
    simp only [det2, hN]
    ring
  · push_neg at hz
    have h0 : ∀ r r', ∑ i ∈ J, β i * p i r * q i r' = 0 := fun r r' =>
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    simp only [det2, h0]
    ring

theorem lower {ι : Type} [DecidableEq ι] : ∀ (m : ℕ) (I : Finset ι) (U V : ι → Fin m → Fin 2 → ZMod 2)
    (c : Fin m → Fin 2 → ι → ZMod 2) (H : Fin m → Fin 2 → Fin 2 → Fin 2 → ZMod 2),
    (∀ j, Good (H j 0) (H j 1)) →
    (∀ j k j1 r1 j2 r2, (if j1 = j ∧ j2 = j then H j k r1 r2 else 0) =
        ∑ i ∈ I, c j k i * U i j1 r1 * V i j2 r2) →
    3 * m ≤ I.card
  | 0, I, _, _, _, _, _, _ => by simp
  | m + 1, I, U, V, c, H, hG, hE => by
    obtain ⟨e, f, g, h, ⟨r0, r0', hA⟩, hB, hAB⟩ := hG (Fin.last m)
    have hlin : ∀ (s s' : ZMod 2) j1 r1 j2 r2,
        (if j1 = Fin.last m ∧ j2 = Fin.last m then
          s * H (Fin.last m) 0 r1 r2 + s' * H (Fin.last m) 1 r1 r2 else 0)
        = ∑ i ∈ I, (s * c (Fin.last m) 0 i + s' * c (Fin.last m) 1 i) * U i j1 r1 * V i j2 r2 := by
      intro s s' j1 r1 j2 r2
      have e0 := hE (Fin.last m) 0 j1 r1 j2 r2
      have e1 := hE (Fin.last m) 1 j1 r1 j2 r2
      have hsplit : ∑ i ∈ I, (s * c (Fin.last m) 0 i + s' * c (Fin.last m) 1 i) * U i j1 r1 * V i j2 r2
          = s * ∑ i ∈ I, c (Fin.last m) 0 i * U i j1 r1 * V i j2 r2
            + s' * ∑ i ∈ I, c (Fin.last m) 1 i * U i j1 r1 * V i j2 r2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsplit, ← e0, ← e1]
      split_ifs <;> ring

    obtain ⟨i0, hi0, hα0⟩ : ∃ i0 ∈ I, e * c (Fin.last m) 0 i0 + f * c (Fin.last m) 1 i0 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hA
      have hh := hlin e f (Fin.last m) r0 (Fin.last m) r0'
      rw [if_pos ⟨rfl, rfl⟩] at hh
      rw [hh]
      exact Finset.sum_eq_zero (fun i hi => by rw [hcon i hi]; ring)
    have hα1 : e * c (Fin.last m) 0 i0 + f * c (Fin.last m) 1 i0 = 1 := ne_zero_eq_one hα0

    set β0 : ZMod 2 := g * c (Fin.last m) 0 i0 + h * c (Fin.last m) 1 i0 with hβ0
    have hBdet : det2 (fun r r' => (g + β0 * e) * H (Fin.last m) 0 r r'
        + (h + β0 * f) * H (Fin.last m) 1 r r') ≠ 0 := by
      rcases F_cases β0 with hb | hb
      · rw [hb]; simpa using hB
      · rw [hb]; simpa using hAB
    have hcoef0 : (g + β0 * e) * c (Fin.last m) 0 i0 + (h + β0 * f) * c (Fin.last m) 1 i0 = 0 := by
      have : (g + β0 * e) * c (Fin.last m) 0 i0 + (h + β0 * f) * c (Fin.last m) 1 i0
          = β0 + β0 * (e * c (Fin.last m) 0 i0 + f * c (Fin.last m) 1 i0) := by
        rw [hβ0]; ring
      rw [this, hα1, mul_one, add_self']
    have hspan := span_of_det (I.erase i0)
      (fun i => (g + β0 * e) * c (Fin.last m) 0 i + (h + β0 * f) * c (Fin.last m) 1 i)
      (fun i => U i (Fin.last m)) (fun i => V i (Fin.last m)) (by
        have hsum : ∀ r r', ∑ i ∈ I.erase i0,
            ((g + β0 * e) * c (Fin.last m) 0 i + (h + β0 * f) * c (Fin.last m) 1 i)
              * U i (Fin.last m) r * V i (Fin.last m) r'
            = (g + β0 * e) * H (Fin.last m) 0 r r' + (h + β0 * f) * H (Fin.last m) 1 r r' := by
          intro r r'
          rw [Finset.sum_erase _ (by rw [hcoef0]; ring)]
          rw [← hlin, if_pos ⟨rfl, rfl⟩]
        simp only [hsum]
        exact hBdet)
    obtain ⟨i1, hi1, i2, hi2, hD0⟩ := hspan
    have hD : U i1 (Fin.last m) 0 * U i2 (Fin.last m) 1 - U i1 (Fin.last m) 1 * U i2 (Fin.last m) 0 = 1 :=
      ne_zero_eq_one hD0
    have h12 : i2 ≠ i1 := by
      rintro rfl
      apply hD0
      ring
    have hi1I : i1 ∈ I := Finset.mem_of_mem_erase hi1
    have hi2' : i2 ∈ (I.erase i0).erase i1 := Finset.mem_erase.mpr ⟨h12, hi2⟩

    let l1 : (Fin 2 → ZMod 2) → ZMod 2 := fun w =>
      U i2 (Fin.last m) 1 * w 0 - U i2 (Fin.last m) 0 * w 1
    let l2 : (Fin 2 → ZMod 2) → ZMod 2 := fun w =>
      U i1 (Fin.last m) 0 * w 1 - U i1 (Fin.last m) 1 * w 0
    let U' : ι → Fin m → Fin 2 → ZMod 2 := fun i j r =>
      U i j.castSucc r - l1 (U i (Fin.last m)) * U i1 j.castSucc r - l2 (U i (Fin.last m)) * U i2 j.castSucc r
    let V' : ι → Fin m → Fin 2 → ZMod 2 := fun i j r => V i j.castSucc r
    let c' : Fin m → Fin 2 → ι → ZMod 2 := fun j k i =>
      c j.castSucc k i + c j.castSucc k i0 * (e * c (Fin.last m) 0 i + f * c (Fin.last m) 1 i)
    have hU1 : ∀ j r, U' i1 j r = 0 := by
      intro j r
      have a1 : l1 (U i1 (Fin.last m)) = 1 := by
        rw [← hD]; simp only [l1]; ring
      have a2 : l2 (U i1 (Fin.last m)) = 0 := by
        simp only [l2]; ring
      simp only [U', a1, a2]
      ring
    have hU2 : ∀ j r, U' i2 j r = 0 := by
      intro j r
      have a1 : l1 (U i2 (Fin.last m)) = 0 := by
        simp only [l1]; ring
      have a2 : l2 (U i2 (Fin.last m)) = 1 := by
        rw [← hD]
      simp only [U', a1, a2]
      ring
    have hc0 : ∀ j k, c' j k i0 = 0 := by
      intro j k
      simp only [c']
      rw [hα1, mul_one, add_self']
    have hMat : ∀ (j : Fin m) (k : Fin 2) (x1 : Fin (m + 1)) (s1 : Fin 2) (x2 : Fin (m + 1)) (s2 : Fin 2),
        ∑ i ∈ I, c' j k i * U i x1 s1 * V i x2 s2
        = (if x1 = j.castSucc ∧ x2 = j.castSucc then H j.castSucc k s1 s2 else 0)
          + c j.castSucc k i0 * (if x1 = Fin.last m ∧ x2 = Fin.last m then
              e * H (Fin.last m) 0 s1 s2 + f * H (Fin.last m) 1 s1 s2 else 0) := by
      intro j k x1 s1 x2 s2
      rw [hE j.castSucc k x1 s1 x2 s2, hlin e f x1 s1 x2 s2, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [c']
      ring
    have hne : ∀ j : Fin m, j.castSucc ≠ Fin.last m := fun j => (Fin.castSucc_lt_last j).ne
    have hE' : ∀ j k j1 r1 j2 r2, (if j1 = j ∧ j2 = j then H j.castSucc k r1 r2 else 0) =
        ∑ i ∈ ((I.erase i0).erase i1).erase i2, c' j k i * U' i j1 r1 * V' i j2 r2 := by
      intro j k j1 r1 j2 r2
      rw [Finset.sum_erase _ (by rw [hU2]; ring), Finset.sum_erase _ (by rw [hU1]; ring),
        Finset.sum_erase _ (by rw [hc0]; ring)]
      have hL0 := hMat j k (Fin.last m) 0 j2.castSucc r2
      have hL1 := hMat j k (Fin.last m) 1 j2.castSucc r2
      have hC := hMat j k j1.castSucc r1 j2.castSucc r2
      rw [if_neg (fun hh => hne j hh.1.symm), if_neg (fun hh => hne j2 hh.2)] at hL0 hL1
      rw [if_neg (show ¬(j1.castSucc = Fin.last m ∧ j2.castSucc = Fin.last m) from
        fun hh => hne j1 hh.1)] at hC
      have hiff : (j1.castSucc = j.castSucc ∧ j2.castSucc = j.castSucc) ↔ (j1 = j ∧ j2 = j) := by
        simp [Fin.castSucc_inj]
      have hexp : ∑ i ∈ I, c' j k i * U' i j1 r1 * V' i j2 r2
          = ∑ i ∈ I, c' j k i * U i j1.castSucc r1 * V i j2.castSucc r2
            - (U i1 j1.castSucc r1 * U i2 (Fin.last m) 1 - U i2 j1.castSucc r1 * U i1 (Fin.last m) 1)
              * ∑ i ∈ I, c' j k i * U i (Fin.last m) 0 * V i j2.castSucc r2
            - (U i2 j1.castSucc r1 * U i1 (Fin.last m) 0 - U i1 j1.castSucc r1 * U i2 (Fin.last m) 0)
              * ∑ i ∈ I, c' j k i * U i (Fin.last m) 1 * V i j2.castSucc r2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [U', V', l1, l2]
        ring
      rw [hexp, hL0, hL1, hC]
      by_cases hjj : j1 = j ∧ j2 = j
      · rw [if_pos hjj, if_pos (hiff.mpr hjj)]; ring
      · rw [if_neg hjj, if_neg (fun hh => hjj (hiff.mp hh))]; ring
    have ih := lower m (((I.erase i0).erase i1).erase i2) U' V' c' (fun j => H j.castSucc)
      (fun j => hG j.castSucc) hE'
    have k1 := Finset.card_erase_add_one hi0
    have k2 := Finset.card_erase_add_one hi1
    have k3 := Finset.card_erase_add_one hi2'
    omega

def pt {n : ℕ} (j : Fin n) (r : Fin 3) : Fin n → Fin 3 := Function.update (fun _ => 0) j r

def Gf (P : Fin 3 → Fin 3 → Fin 3) (k : Fin 2) (p q : Fin 3) : ZMod 2 := if P p q = k.succ then 1 else 0

def Hred (G : Fin 3 → Fin 3 → ZMod 2) (r r' : Fin 2) : ZMod 2 :=
  G r.castSucc r'.castSucc + G r.castSucc 2 + G 2 r'.castSucc + G 2 2

def third (p q : Fin 3) : Fin 3 := if p ≠ 0 ∧ q ≠ 0 then 0 else if p ≠ 1 ∧ q ≠ 1 then 1 else 2

def Ptab (d0 d1 d2 : Fin 3) (p q : Fin 3) : Fin 3 :=
  if p = q then (if p = 0 then d0 else if p = 1 then d1 else d2) else third p q

theorem forced : ∀ z p q : Fin 3, p ≠ q → z ≠ p → z ≠ q → z = third p q := by decide

theorem P_eq (P : Fin 3 → Fin 3 → Fin 3) (hP : ∀ x y, P x y ≠ x ∧ P x y ≠ y) :
    P = Ptab (P 0 0) (P 1 1) (P 2 2) := by
  funext p q
  by_cases hpq : p = q
  · subst hpq
    fin_cases p <;> simp [Ptab]
  · simp only [Ptab, hpq, if_false]
    exact forced _ _ _ hpq (hP p q).1 (hP p q).2

theorem goodTab : ∀ d0 d1 d2 : Fin 3, d0 ≠ 0 → d1 ≠ 1 → d2 ≠ 2 →
    Good (Hred (Gf (Ptab d0 d1 d2) 0)) (Hred (Gf (Ptab d0 d1 d2) 1)) := by
  unfold Good det2 Hred Gf Ptab third
  decide

theorem goodP (P : Fin 3 → Fin 3 → Fin 3) (hP : ∀ x y, P x y ≠ x ∧ P x y ≠ y) :
    Good (Hred (Gf P 0)) (Hred (Gf P 1)) := by
  rw [P_eq P hP]
  exact goodTab _ _ _ (hP 0 0).1 (hP 1 1).1 (hP 2 2).1

theorem cancel4 : ∀ A C : ZMod 2, 0 = A + A + C + C := by decide

theorem cancel4' : ∀ A B : ZMod 2, 0 = A + B + A + B := by decide

theorem reduce_id {n t : ℕ} (pick : Fin n → Fin 3 → Fin 3 → Fin 3)
    (u v : Fin t → (Fin n → Fin 3) → ZMod 2) (a b : Fin n → Fin 2 → (Fin n → Fin 3) → ZMod 2)
    (coeff : Fin n → Fin 2 → Fin t → ZMod 2)
    (hE : ∀ (x y : Fin n → Fin 3) (j : Fin n) (k : Fin 2),
      (if pick j (x j) (y j) = k.succ then (1 : ZMod 2) else 0) =
      a j k x + b j k y + ∑ i, coeff j k i * u i x * v i y)
    (j : Fin n) (k : Fin 2) (j1 : Fin n) (r1 : Fin 2) (j2 : Fin n) (r2 : Fin 2) :
    (if j1 = j ∧ j2 = j then Hred (Gf (pick j) k) r1 r2 else 0) =
      ∑ i ∈ Finset.univ, coeff j k i * (u i (pt j1 r1.castSucc) + u i (pt j1 2))
        * (v i (pt j2 r2.castSucc) + v i (pt j2 2)) := by
  have e11 := hE (pt j1 r1.castSucc) (pt j2 r2.castSucc) j k
  have e12 := hE (pt j1 r1.castSucc) (pt j2 2) j k
  have e21 := hE (pt j1 2) (pt j2 r2.castSucc) j k
  have e22 := hE (pt j1 2) (pt j2 2) j k
  have hsum : ∑ i ∈ Finset.univ, coeff j k i * (u i (pt j1 r1.castSucc) + u i (pt j1 2))
        * (v i (pt j2 r2.castSucc) + v i (pt j2 2))
      = ∑ i, coeff j k i * u i (pt j1 r1.castSucc) * v i (pt j2 r2.castSucc)
      + ∑ i, coeff j k i * u i (pt j1 r1.castSucc) * v i (pt j2 2)
      + ∑ i, coeff j k i * u i (pt j1 2) * v i (pt j2 r2.castSucc)
      + ∑ i, coeff j k i * u i (pt j1 2) * v i (pt j2 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hT : (if j1 = j ∧ j2 = j then Hred (Gf (pick j) k) r1 r2 else 0) =
      (if pick j (pt j1 r1.castSucc j) (pt j2 r2.castSucc j) = k.succ then (1 : ZMod 2) else 0)
      + (if pick j (pt j1 r1.castSucc j) (pt j2 2 j) = k.succ then (1 : ZMod 2) else 0)
      + (if pick j (pt j1 2 j) (pt j2 r2.castSucc j) = k.succ then (1 : ZMod 2) else 0)
      + (if pick j (pt j1 2 j) (pt j2 2 j) = k.succ then (1 : ZMod 2) else 0) := by
    by_cases h1 : j1 = j
    · by_cases h2 : j2 = j
      · subst h1
        subst h2
        rw [if_pos ⟨rfl, rfl⟩]
        simp only [pt, Function.update_self, Hred, Gf]
      · have hz : ∀ r : Fin 3, pt j2 r j = 0 := fun r => by
          simp [pt, Function.update_apply, Ne.symm h2]
        rw [if_neg (fun hh => h2 hh.2)]
        simp only [hz]
        exact cancel4 _ _
    · have hz : ∀ r : Fin 3, pt j1 r j = 0 := fun r => by
        simp [pt, Function.update_apply, Ne.symm h1]
      rw [if_neg (fun hh => h1 hh.1)]
      simp only [hz]
      exact cancel4' _ _
  rw [hsum, hT]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination e11 + e12 + e21 + e22
    + (a j k (pt j1 r1.castSucc) + a j k (pt j1 2) + b j k (pt j2 r2.castSucc) + b j k (pt j2 2)) * h2

def w (r p : Fin 3) : ZMod 2 := if p = 2 then 0 else if r = 2 then 1 else if p = r then 1 else 0

def Kc (G : Fin 3 → Fin 3 → ZMod 2) (r : Fin 3) : ZMod 2 :=
  if r = 0 then Hred G 0 0 + Hred G 0 1 else if r = 1 then Hred G 1 1 + Hred G 0 1 else Hred G 0 1

theorem blk_key : ∀ a00 a01 a02 a10 a11 a12 a20 a21 a22 : ZMod 2,
    a01 = a10 → a02 = a20 → a12 = a21 →
    let G : Fin 3 → Fin 3 → ZMod 2 := fun p q =>
      if p = 0 then (if q = 0 then a00 else if q = 1 then a01 else a02)
      else if p = 1 then (if q = 0 then a10 else if q = 1 then a11 else a12)
      else (if q = 0 then a20 else if q = 1 then a21 else a22)
    ∀ p q : Fin 3, G p q = (G p 2 + G 2 2) + G 2 q
      + (Kc G 0 * w 0 p * w 0 q + Kc G 1 * w 1 p * w 1 q + Kc G 2 * w 2 p * w 2 q) := by
  unfold Kc Hred w
  decide

theorem blk (G : Fin 3 → Fin 3 → ZMod 2) (h01 : G 0 1 = G 1 0) (h02 : G 0 2 = G 2 0)
    (h12 : G 1 2 = G 2 1) (p q : Fin 3) :
    G p q = (G p 2 + G 2 2) + G 2 q
      + (Kc G 0 * w 0 p * w 0 q + Kc G 1 * w 1 p * w 1 q + Kc G 2 * w 2 p * w 2 q) := by
  have hG : G = fun p q =>
      if p = 0 then (if q = 0 then G 0 0 else if q = 1 then G 0 1 else G 0 2)
      else if p = 1 then (if q = 0 then G 1 0 else if q = 1 then G 1 1 else G 1 2)
      else (if q = 0 then G 2 0 else if q = 1 then G 2 1 else G 2 2) := by
    funext p q
    fin_cases p <;> fin_cases q <;> rfl
  rw [hG]
  exact blk_key _ _ _ _ _ _ _ _ _ h01 h02 h12 p q

def emb {n t : ℕ} (h : 3 * n ≤ t) (j : Fin n) (r : Fin 3) : Fin t :=
  ⟨3 * j.val + r.val, by have := j.isLt; have := r.isLt; omega⟩

theorem emb_eq {n t : ℕ} (h : 3 * n ≤ t) (j j' : Fin n) (r r' : Fin 3) :
    emb h j r = emb h j' r' ↔ j = j' ∧ r = r' := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    simp only [emb] at hv
    have := r.isLt
    have := r'.isLt
    constructor
    · ext; omega
    · ext; omega
  · rintro ⟨rfl, rfl⟩
    rfl

def uu {n t : ℕ} (h : 3 * n ≤ t) (i : Fin t) (x : Fin n → Fin 3) : ZMod 2 :=
  ∑ j : Fin n, ∑ r : Fin 3, if i = emb h j r then w r (x j) else 0

theorem uu_emb {n t : ℕ} (h : 3 * n ≤ t) (j : Fin n) (r : Fin 3) (x : Fin n → Fin 3) :
    uu h (emb h j r) x = w r (x j) := by
  unfold uu
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hr'
      rw [if_neg]
      intro hh
      exact hr' ((emb_eq h j j r r').mp hh).2.symm
    · intro hr; exact absurd (Finset.mem_univ r) hr
  · intro j' _ hj'
    apply Finset.sum_eq_zero
    intro r' _
    rw [if_neg]
    intro hh
    exact hj' ((emb_eq h j j' r r').mp hh).1.symm
  · intro hj; exact absurd (Finset.mem_univ j) hj

def cc {n t : ℕ} (h : 3 * n ≤ t) (pick : Fin n → Fin 3 → Fin 3 → Fin 3) (j : Fin n) (k : Fin 2)
    (i : Fin t) : ZMod 2 :=
  ∑ r : Fin 3, if i = emb h j r then Kc (Gf (pick j) k) r else 0

theorem collapse {n t : ℕ} (h : 3 * n ≤ t) (pick : Fin n → Fin 3 → Fin 3 → Fin 3) (j : Fin n)
    (k : Fin 2) (x y : Fin n → Fin 3) :
    ∑ i, cc h pick j k i * uu h i x * uu h i y
      = ∑ r : Fin 3, Kc (Gf (pick j) k) r * w r (x j) * w r (y j) := by
  unfold cc
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_ite_eq']
  simp [uu_emb]

theorem sym_pick {n : ℕ} (pick : Fin n → Fin 3 → Fin 3 → Fin 3)
    (hpick : ∀ j x y, pick j x y ≠ x ∧ pick j x y ≠ y) (j : Fin n) (p q : Fin 3) (hpq : p ≠ q) :
    pick j p q = pick j q p := by
  rw [forced (pick j p q) p q hpq (hpick j p q).1 (hpick j p q).2,
    forced (pick j q p) q p (Ne.symm hpq) (hpick j q p).1 (hpick j q p).2]
  revert hpq
  revert p q
  decide

end PEqualNP.Outside.L_meta_38526

open PEqualNP.Outside.L_meta_38526 in
theorem PEqualNP.Outside.L_meta_38526 : (∀ (n t : Nat) (pick : Fin n → Fin 3 → Fin 3 → Fin 3),
  (∀ j x y, pick j x y ≠ x ∧ pick j x y ≠ y) →
  let W := Fin n → Fin 3
  let F := ZMod 2
  (∃ (u v : Fin t → W → F) (a b : Fin n → Fin 2 → W → F)
     (coeff : Fin n → Fin 2 → Fin t → F),
    ∀ (x y : W) (j : Fin n) (k : Fin 2),
      (if pick j (x j) (y j) = k.succ then (1 : F) else 0) =
      a j k x + b j k y + ∑ i, coeff j k i * u i x * v i y) ↔ 3*n ≤ t) := by
  intro n t pick hpick
  dsimp only
  constructor
  · rintro ⟨u, v, a, b, coeff, hE⟩
    have hlow := lower n (Finset.univ : Finset (Fin t))
      (fun i j r => u i (pt j r.castSucc) + u i (pt j 2))
      (fun i j r => v i (pt j r.castSucc) + v i (pt j 2))
      coeff (fun j k => Hred (Gf (pick j) k))
      (fun j => goodP (pick j) (hpick j))
      (fun j k j1 r1 j2 r2 => reduce_id pick u v a b coeff hE j k j1 r1 j2 r2)
    simpa using hlow
  · intro h3
    refine ⟨uu h3, uu h3, fun j k x => Gf (pick j) k (x j) 2 + Gf (pick j) k 2 2,
      fun j k y => Gf (pick j) k 2 (y j), cc h3 pick, ?_⟩
    intro x y j k
    rw [collapse h3 pick j k x y, Fin.sum_univ_three]
    have hs : ∀ p q : Fin 3, p ≠ q → Gf (pick j) k p q = Gf (pick j) k q p := by
      intro p q hpq
      unfold Gf
      rw [sym_pick pick hpick j p q hpq]
    exact blk (Gf (pick j) k) (hs 0 1 (by decide)) (hs 0 2 (by decide)) (hs 1 2 (by decide)) (x j) (y j)
