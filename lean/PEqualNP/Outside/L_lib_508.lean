import Mathlib

namespace PEqualNP.Outside.L_lib_508_aux

open scoped BigOperators

private abbrev Bits (n : ℕ) := Fin n → ZMod 2

private def aff {n : ℕ} (c : Bits n) (e : ZMod 2) (x : Bits n) : ZMod 2 :=
  dotProduct c x + e

private theorem aff_add {n : ℕ} (c c' : Bits n) (e e' : ZMod 2) (x : Bits n) :
    aff (c + c') (e + e') x = aff c e x + aff c' e' x := by
  simp only [aff, dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem aff_smul {n : ℕ} (t : ZMod 2) (c : Bits n) (e : ZMod 2) (x : Bits n) :
    aff (t • c) (t * e) x = t * aff c e x := by
  simp only [aff, dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

private def vote (a b : ZMod 2) : ℤ := if a = b then 1 else -1

private def score {X : Type*} (D : Finset X) (f g : X → ZMod 2) : ℤ :=
  ∑ x ∈ D, vote (f x) (g x)

private theorem vote_flip (a b h : ZMod 2) :
    vote a b + vote a (b + h) = if h = 0 then 2 * vote a b else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases h <;> decide

private theorem bit_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem bit_substitute (u t : ZMod 2) : u + t = 0 ↔ u = t := by
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  rcases bit_cases u with rfl | rfl <;> rcases bit_cases t with rfl | rfl <;> simp [h]

/-- Keep the larger fiber of one affine factor, approximate recursively there,
then choose the extension with fewer errors off that fiber. -/
private theorem approximate {n s : ℕ} (I : Finset (Fin s))
    (A B : Fin s → Bits n) (a b : Fin s → ZMod 2)
    (D : Finset (Bits n)) (f : Bits n → ZMod 2) (c : Bits n) (e : ZMod 2)
    (hf : ∀ x ∈ D, f x = aff c e x + ∑ i ∈ I, aff (A i) (a i) x * aff (B i) (b i) x) :
    ∃ c' e', (D.card : ℤ) ≤ 2 ^ I.card * score D f (aff c' e') := by
  classical
  induction I using Finset.induction_on generalizing D c e with
  | empty =>
      refine ⟨c, e, ?_⟩
      simp only [Finset.card_empty, pow_zero, one_mul, score]
      have hsum : (∑ x ∈ D, vote (f x) (aff c e x)) = ∑ _x ∈ D, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [vote, show f x = aff c e x by simpa using hf x hx]
      rw [hsum]
      simp
  | @insert i I hi ih =>
      let u := aff (A i) (a i)
      have hmajor : ∃ t : ZMod 2, D.card ≤ 2 * (D.filter fun x => u x = t).card := by
        have hs := Finset.card_filter_add_card_filter_not (s := D) (fun x => u x = 0)
        by_cases h : D.card ≤ 2 * (D.filter fun x => u x = 0).card
        · exact ⟨0, h⟩
        refine ⟨1, ?_⟩
        have he : (D.filter fun x => ¬ u x = 0) = D.filter fun x => u x = 1 := by
          ext x
          simp only [Finset.mem_filter]
          rcases bit_cases (u x) with hzero | hone
          · simp [hzero]
          · simp [hone]
        rw [he] at hs
        omega
      obtain ⟨t, ht⟩ := hmajor
      let R := D.filter fun x => u x = t
      have hr : ∀ x ∈ R, f x = aff (c + t • B i) (e + t * b i) x +
          ∑ j ∈ I, aff (A j) (a j) x * aff (B j) (b j) x := by
        intro x hx
        obtain ⟨hxD, hxu⟩ := Finset.mem_filter.mp hx
        change aff (A i) (a i) x = t at hxu
        rw [hf x hxD, Finset.sum_insert hi, aff_add, aff_smul, hxu]
        ring
      obtain ⟨p, q, hp⟩ := ih R (c + t • B i) (e + t * b i) hr
      let g := aff p q
      let g' := aff (p + A i) (q + (a i + t))
      have hsplit : score D f g + score D f g' = 2 * score R f g := by
        classical
        simp only [score, ← Finset.sum_add_distrib, Finset.mul_sum, R, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        have hgg : g' x = g x + (u x + t) := by
          dsimp [g', g, u]
          rw [aff_add]
          simp only [aff]
          ring
        rw [hgg, vote_flip]
        by_cases he : u x = t <;> simp [bit_substitute, he]
      have hm : ∃ p' q', score R f g ≤ score D f (aff p' q') := by
        by_cases h : score R f g ≤ score D f g
        · exact ⟨p, q, h⟩
        exact ⟨p + A i, q + (a i + t), by change score R f g ≤ score D f g'; omega⟩
      obtain ⟨p', q', hm⟩ := hm
      refine ⟨p', q', ?_⟩
      rw [Finset.card_insert_of_notMem hi, pow_succ]
      have ht' : (D.card : ℤ) ≤ 2 * (R.card : ℤ) := by exact_mod_cast ht
      change (R.card : ℤ) ≤ 2 ^ I.card * score R f g at hp
      calc
        (D.card : ℤ) ≤ 2 * R.card := ht'
        _ ≤ 2 * (2 ^ I.card * score R f g) := by omega
        _ ≤ 2 ^ I.card * 2 * score D f (aff p' q') := by
          rw [mul_assoc, mul_left_comm (2 : ℤ)]
          gcongr

private theorem score_dist {X : Type*} (D : Finset X) (f g : X → ZMod 2) :
    score D f g = (D.card : ℤ) - 2 * ((D.filter fun x => f x ≠ g x).card : ℤ) := by
  simp only [score, vote]
  have h : ∑ x ∈ D, (if f x = g x then (1 : ℤ) else -1) =
      ∑ x ∈ D, (1 - 2 * if f x ≠ g x then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases he : f x = g x <;> simp [he]
  rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  simp

end PEqualNP.Outside.L_lib_508_aux

open PEqualNP.Outside.L_lib_508_aux

theorem PEqualNP.Outside.L_lib_508 :
    ∀ n m s d : ℕ, 1 ≤ d → d ≤ n →
      let V := Fin n → ZMod 2
      let W := Fin m → ZMod 2
      ∀ (F : V → W) (A B : Fin s → V) (a b : Fin s → ZMod 2)
        (weights : Fin m → Fin s → ZMod 2) (lin : Fin m → V) (offset : W),
        (∀ (x : V) (j : Fin m), F x j = dotProduct (lin j) x + offset j +
          ∑ i : Fin s, weights j i * (dotProduct (A i) x + a i) * (dotProduct (B i) x + b i)) →
        (∀ (w : W), w ≠ 0 → ∀ (c : V) (e : ZMod 2),
          2*((Finset.univ : Finset V).filter
            (fun x => dotProduct w (F x) ≠ dotProduct c x + e)).card + 2^(n-d) ≥ 2^n) →
        let tag := fun (w : W) (i : Fin s) => ∑ j : Fin m, w j * weights j i
        Function.Injective tag ∧ ∀ w : W, w ≠ 0 →
          d ≤ ((Finset.univ : Finset (Fin s)).filter (fun j => tag w j ≠ 0)).card := by
  classical
  intro n m s d hd hdn V W F A B a b weights lin offset hF hfar tag
  have hweight : ∀ w : W, w ≠ 0 →
      d ≤ ((Finset.univ : Finset (Fin s)).filter (fun j => tag w j ≠ 0)).card := by
    intro w hw
    let I := (Finset.univ : Finset (Fin s)).filter fun i => tag w i ≠ 0
    let c : V := fun k => ∑ j : Fin m, w j * lin j k
    let e : ZMod 2 := dotProduct w offset
    let f : V → ZMod 2 := fun x => dotProduct w (F x)
    have hf : ∀ x ∈ (Finset.univ : Finset V), f x = aff c e x +
        ∑ i ∈ I, aff (A i) (a i) x * aff (B i) (b i) x := by
      intro x hx
      have hlin : (∑ j : Fin m, w j * dotProduct (lin j) x) = dotProduct c x := by
        simp only [dotProduct, c, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      have hprod : (∑ j : Fin m, w j * ∑ i : Fin s,
          weights j i * aff (A i) (a i) x * aff (B i) (b i) x) =
          ∑ i ∈ I, aff (A i) (a i) x * aff (B i) (b i) x := by
        simp only [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul]
        rw [show (∑ i : Fin s, tag w i * aff (A i) (a i) x * aff (B i) (b i) x) =
          ∑ i : Fin s, if tag w i ≠ 0 then aff (A i) (a i) x * aff (B i) (b i) x else 0 from ?_, ← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        rcases bit_cases (tag w i) with hzero | hone
        · simp [hzero]
        · simp [hone]
      simp only [f, dotProduct, hF]
      change (∑ j : Fin m, w j * (dotProduct (lin j) x + offset j +
        ∑ i : Fin s, weights j i * aff (A i) (a i) x * aff (B i) (b i) x)) =
        dotProduct c x + e + _
      simp only [mul_add, Finset.sum_add_distrib]
      change (∑ j : Fin m, w j * dotProduct (lin j) x) + e + _ = _
      rw [hlin, hprod]
    obtain ⟨p, q, hp⟩ := approximate I A B a b Finset.univ f c e hf
    have hcard : ((Finset.univ : Finset V).card : ℤ) = 2 ^ n := by
      simp [V, ZMod.card]
    have hup : score Finset.univ f (aff p q) ≤ 2 ^ (n - d) := by
      rw [score_dist, hcard]
      have h := hfar w hw p q
      change 2 * ((Finset.univ : Finset V).filter fun x => f x ≠ aff p q x).card +
        2 ^ (n - d) ≥ 2 ^ n at h
      have hi : (2 ^ n : ℤ) ≤
          2 * (((Finset.univ : Finset V).filter fun x => f x ≠ aff p q x).card : ℤ) +
            2 ^ (n - d) := by exact_mod_cast h
      omega
    change d ≤ I.card
    by_contra! hlt
    have hlt' : I.card + (n - d) < n := by omega
    rw [hcard] at hp
    have hmul : (2 : ℤ) ^ I.card * score Finset.univ f (aff p q) ≤ 2 ^ (I.card + (n - d)) := by
      rw [pow_add]
      gcongr
    have hpow : (2 : ℤ) ^ (I.card + (n - d)) < 2 ^ n := by
      gcongr
      decide
    omega
  refine ⟨?_, hweight⟩
  intro w w' hww
  by_contra hne
  have hnz : w - w' ≠ 0 := sub_ne_zero.mpr hne
  have hz : tag (w - w') = 0 := by
    funext i
    change (∑ j : Fin m, (w j - w' j) * weights j i) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    change tag w i - tag w' i = 0
    rw [hww, sub_self]
  have h := hweight (w - w') hnz
  simp [hz] at h
  omega
