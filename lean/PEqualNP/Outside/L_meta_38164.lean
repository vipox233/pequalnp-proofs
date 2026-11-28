import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38164

private def chi (bits : Nat → Bool) (j : Nat) : Bool :=
  xor (bits j) (!(bits (j + 1)) && bits (j + 2))

private def mix (d x i : Nat) : Bool :=
  xor (x.testBit i) (xor (x.testBit (i + d)) (x.testBit (i + 2 * d)))

private def packBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => packBits f k ||| if f k then 2 ^ k else 0

private lemma packBits_lt (f : Nat → Bool) : ∀ k, packBits f k < 2 ^ k
  | 0 => by simp [packBits]
  | k + 1 => by
    have ih := packBits_lt f k
    simp only [packBits]
    have h1 : packBits f k < 2 ^ (k + 1) := lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : (if f k then 2 ^ k else 0) < 2 ^ (k + 1) := by
      split
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
      · exact Nat.two_pow_pos _
    exact Nat.or_lt_two_pow h1 h2

private lemma testBit_packBits (f : Nat → Bool) :
    ∀ k i, (packBits f k).testBit i = if i < k then f i else false
  | 0, i => by simp [packBits]
  | k + 1, i => by
    have ih := testBit_packBits f k i
    simp only [packBits, Nat.testBit_or, ih]
    by_cases hfk : f k = true
    · simp only [hfk, ite_true, Nat.testBit_two_pow]
      by_cases hi : i < k
      · have hne : k ≠ i := by omega
        have hi1 : i < k + 1 := by omega
        simp [hi, hi1, hne]
      · by_cases heq : i = k
        · subst heq; simp [hfk]
        · have hi1 : ¬ i < k + 1 := by omega
          have hne : k ≠ i := by omega
          simp [hi, hi1, hne]
    · simp only [hfk, Bool.false_eq_true, ite_false, Nat.zero_testBit, Bool.or_false]
      by_cases hi : i < k
      · have hi1 : i < k + 1 := by omega
        simp [hi, hi1]
      · by_cases heq : i = k
        · subst heq
          have : f i = false := by cases h : f i <;> simp_all
          simp [this]
        · have hi1 : ¬ i < k + 1 := by omega
          simp [hi, hi1]

private def reconBit (h : Nat) (z : Finset Nat) (a b : Bool) (i : Nat) : Bool :=
  if hi : i < h then
    xor (decide (i ∈ z)) (!(reconBit h z a b (i + 1)) && reconBit h z a b (i + 2))
  else if i = h then a
  else if i = h + 1 then b
  else false
termination_by h + 2 - i

private lemma reconBit_of_lt {h : Nat} {z : Finset Nat} {a b : Bool} {i : Nat} (hi : i < h) :
    reconBit h z a b i =
      xor (decide (i ∈ z)) (!(reconBit h z a b (i + 1)) && reconBit h z a b (i + 2)) := by
  rw [reconBit]; simp [hi]

private lemma reconBit_h (h : Nat) (z : Finset Nat) (a b : Bool) :
    reconBit h z a b h = a := by
  rw [reconBit]; simp

private lemma reconBit_h1 (h : Nat) (z : Finset Nat) (a b : Bool) :
    reconBit h z a b (h + 1) = b := by
  rw [reconBit]; simp

private lemma reconBit_ge {h : Nat} {z : Finset Nat} {a b : Bool} {i : Nat} (hi : h + 2 ≤ i) :
    reconBit h z a b i = false := by
  rw [reconBit]
  have h1 : ¬ i < h := by omega
  have h2 : i ≠ h := by omega
  have h3 : i ≠ h + 1 := by omega
  simp [h1, h2, h3]

private lemma chi_reconBit {h : Nat} {z : Finset Nat} {a b : Bool} {j : Nat} (hj : j < h) :
    chi (reconBit h z a b) j = decide (j ∈ z) := by
  simp only [chi]
  rw [reconBit_of_lt hj]
  cases decide (j ∈ z) <;> cases reconBit h z a b (j + 1) <;> cases reconBit h z a b (j + 2) <;> rfl

private def recon (h : Nat) (z : Finset Nat) (a b : Bool) : Nat :=
  packBits (reconBit h z a b) (h + 2)

private lemma recon_lt (h : Nat) (z : Finset Nat) (a b : Bool) :
    recon h z a b < 2 ^ (h + 2) :=
  packBits_lt _ _

private lemma testBit_recon (h : Nat) (z : Finset Nat) (a b : Bool) (i : Nat) :
    (recon h z a b).testBit i = reconBit h z a b i := by
  rw [recon, testBit_packBits]
  split
  · rfl
  · rename_i hi
    symm; exact reconBit_ge (by omega)

private lemma first_recon (h : Nat) {z : Finset Nat} (hz : z ⊆ Finset.range h) (a b : Bool) :
    (Finset.range h).filter (fun j => chi (fun i => (recon h z a b).testBit i) j) = z := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hchi⟩
    have heq : chi (fun i => (recon h z a b).testBit i) j = chi (reconBit h z a b) j := by
      simp only [chi, testBit_recon]
    rw [heq, chi_reconBit hj] at hchi
    exact of_decide_eq_true hchi
  · intro hj
    have hlt : j < h := Finset.mem_range.mp (hz hj)
    refine ⟨hlt, ?_⟩
    have heq : chi (fun i => (recon h z a b).testBit i) j = chi (reconBit h z a b) j := by
      simp only [chi, testBit_recon]
    rw [heq, chi_reconBit hlt]
    exact decide_eq_true hj

private lemma recon_first_eq {h u : Nat} (hu : u < 2 ^ (h + 2)) :
    recon h ((Finset.range h).filter (fun j => chi (fun i => u.testBit i) j))
      (u.testBit h) (u.testBit (h + 1)) = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_recon]

  suffices ∀ k i, h + 2 - i = k →
      reconBit h ((Finset.range h).filter (fun j => chi (fun i => u.testBit i) j))
        (u.testBit h) (u.testBit (h + 1)) i = u.testBit i from
    this (h + 2 - i) i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i hk
    by_cases hi : i < h
    · rw [reconBit_of_lt hi]
      have h1 := ih (h + 2 - (i + 1)) (by omega) (i + 1) rfl
      have h2 := ih (h + 2 - (i + 2)) (by omega) (i + 2) rfl
      rw [h1, h2]
      have hmem : decide (i ∈ (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)) =
          chi (fun i => u.testBit i) i := by
        simp [Finset.mem_filter, hi]
      rw [hmem]
      simp only [chi]
      cases u.testBit i <;> cases u.testBit (i + 1) <;> cases u.testBit (i + 2) <;> rfl
    · by_cases hih : i = h
      · subst hih; rw [reconBit_h]
      · by_cases hih1 : i = h + 1
        · subst hih1; rw [reconBit_h1]
        · have hge : h + 2 ≤ i := by omega
          rw [reconBit_ge hge]
          symm
          exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) hge))

private def solveMix (N d : Nat) (hd : 0 < d) (b : Nat → Bool) (i : Nat) : Bool :=
  if hi : i < N then
    xor (b i) (xor (solveMix N d hd b (i + d)) (solveMix N d hd b (i + 2 * d)))
  else false
termination_by N - i

private lemma solveMix_ge {N d : Nat} {hd : 0 < d} {b : Nat → Bool} {i : Nat} (hi : N ≤ i) :
    solveMix N d hd b i = false := by
  rw [solveMix]
  have : ¬ i < N := by omega
  simp [this]

private lemma mix_packBits_solveMix {N d : Nat} (hd : 0 < d) (b : Nat → Bool) {i : Nat} (hi : i < N) :
    mix d (packBits (solveMix N d hd b) N) i = b i := by
  have ht : ∀ j, (packBits (solveMix N d hd b) N).testBit j = solveMix N d hd b j := by
    intro j
    rw [testBit_packBits]
    split
    · rfl
    · rename_i hj; symm; exact solveMix_ge (by omega)
  simp only [mix, ht]
  conv_lhs => arg 1; rw [solveMix]
  simp only [hi, dite_true]
  cases b i <;> cases solveMix N d hd b (i + d) <;> cases solveMix N d hd b (i + 2 * d) <;> rfl

private lemma reconBit_eq_of_bad {h : Nat} (hh : 4 ≤ h) {z : Finset Nat}
    (hz1 : h - 1 ∈ z) (hz2 : h - 2 ∈ z) (a b : Bool) :
    (reconBit h z a b (h - 1) = xor true (!a && b)) ∧
    (reconBit h z a b (h - 2) = true) ∧
    (∀ j ≤ h - 2, reconBit h z a b j = reconBit h z false false j) := by
  have h1 : reconBit h z a b (h - 1) = xor true (!a && b) := by
    rw [reconBit_of_lt (by omega)]
    have e1 : h - 1 + 1 = h := by omega
    have e2 : h - 1 + 2 = h + 1 := by omega
    rw [e1, e2, reconBit_h, reconBit_h1, decide_eq_true hz1]
  have h2 : reconBit h z a b (h - 2) = true := by
    rw [reconBit_of_lt (by omega)]
    have e1 : h - 2 + 1 = h - 1 := by omega
    have e2 : h - 2 + 2 = h := by omega
    rw [e1, e2, h1, reconBit_h, decide_eq_true hz2]
    cases a <;> cases b <;> rfl
  refine ⟨h1, h2, ?_⟩
  intro j hj
  suffices ∀ k j, j ≤ h - 2 → h - 2 - j = k →
      reconBit h z a b j = reconBit h z false false j from
    this (h - 2 - j) j hj rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro j hj hk
    by_cases heq : j = h - 2
    · subst heq
      rw [h2]
      have h2' : reconBit h z false false (h - 2) = true := by
        rw [reconBit_of_lt (by omega)]
        have e1 : h - 2 + 1 = h - 1 := by omega
        have e2 : h - 2 + 2 = h := by omega
        rw [e1, e2, reconBit_of_lt (by omega)]
        have e3 : h - 1 + 1 = h := by omega
        have e4 : h - 1 + 2 = h + 1 := by omega
        rw [e3, e4, reconBit_h, reconBit_h1, decide_eq_true hz1, decide_eq_true hz2]
        rfl
      rw [h2']
    · by_cases heq3 : j = h - 3
      · subst heq3
        conv_lhs => rw [reconBit_of_lt (by omega)]
        conv_rhs => rw [reconBit_of_lt (by omega)]
        have e1 : h - 3 + 1 = h - 2 := by omega
        rw [e1, h2]
        have h2' : reconBit h z false false (h - 2) = true := by
          rw [reconBit_of_lt (by omega)]
          have e1' : h - 2 + 1 = h - 1 := by omega
          have e2' : h - 2 + 2 = h := by omega
          rw [e1', e2', reconBit_of_lt (by omega)]
          have e3 : h - 1 + 1 = h := by omega
          have e4 : h - 1 + 2 = h + 1 := by omega
          rw [e3, e4, reconBit_h, reconBit_h1, decide_eq_true hz1, decide_eq_true hz2]
          rfl
        rw [h2']
        simp
      · conv_lhs => rw [reconBit_of_lt (by omega)]
        conv_rhs => rw [reconBit_of_lt (by omega)]
        have r1 := ih (h - 2 - (j + 1)) (by omega) (j + 1) (by omega) rfl
        have r2 := ih (h - 2 - (j + 2)) (by omega) (j + 2) (by omega) rfl
        rw [r1, r2]

private def badChi (m3 m2 m1 m0 mp : Bool) (u3 a b : Bool) (idx : Fin 3) : Bool :=
  let u1 := xor true (!a && b)
  let b3 := xor u3 m3
  let b2 := xor true m2
  let b1 := xor u1 m1
  let b0 := xor a m0
  let bp := xor b mp
  match idx with
  | ⟨0, _⟩ => xor b3 (!b2 && b1)
  | ⟨1, _⟩ => xor b2 (!b1 && b0)
  | ⟨2, _⟩ => xor b1 (!b0 && bp)

private lemma bad_collision_drop3 (m3 m2 m1 m0 mp u3 : Bool) :
    ∃ p q : Bool × Bool, p ≠ q ∧
      badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨1, by omega⟩ =
        badChi m3 m2 m1 m0 mp u3 q.1 q.2 ⟨1, by omega⟩ ∧
      badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨2, by omega⟩ =
        badChi m3 m2 m1 m0 mp u3 q.1 q.2 ⟨2, by omega⟩ := by
  revert m3 m2 m1 m0 mp u3; decide

private lemma bad_collision_drop2 (m3 m2 m1 m0 mp u3 : Bool) :
    ∃ p q : Bool × Bool, p ≠ q ∧
      badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨0, by omega⟩ =
        badChi m3 m2 m1 m0 mp u3 q.1 q.2 ⟨0, by omega⟩ ∧
      badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨2, by omega⟩ =
        badChi m3 m2 m1 m0 mp u3 q.1 q.2 ⟨2, by omega⟩ := by
  revert m3 m2 m1 m0 mp u3; decide

private def lowerOut (z4 z3 z2 z1 a b : Bool) : Bool × Bool × Bool :=
  let u1 := xor z1 (!a && b)
  let u2 := xor z2 (!u1 && a)
  let u3 := xor z3 (!u2 && u1)
  let u4 := xor z4 (!u3 && u2)
  let m3 := !z1
  let m2 := z1
  let m1 := z1
  let m0 := true
  let b4 := u4
  let b3 := xor u3 m3
  let b2 := xor u2 m2
  let b1 := xor u1 m1
  let b0 := xor a m0
  let bp := b
  (xor b4 (!b3 && b2), xor b2 (!b1 && b0), xor b1 (!b0 && bp))

private lemma lower_card_eq (z4 z3 z2 z1 : Bool) :
    ((Finset.univ : Finset (Bool × Bool)).image (fun p => lowerOut z4 z3 z2 z1 p.1 p.2)).card =
      if z1 && z2 then 3 else 4 := by
  revert z4 z3 z2 z1; decide

private lemma sum_fiber_budget {h : Nat} (hh : 4 ≤ h) :
    ∑ z ∈ (Finset.range h).powerset, (if h - 1 ∈ z ∧ h - 2 ∈ z then 3 else 4) =
      15 * 2 ^ (h - 2) := by
  have h1 : h - 1 ∈ Finset.range h := Finset.mem_range.mpr (by omega)
  have h2 : h - 2 ∈ Finset.range h := Finset.mem_range.mpr (by omega)
  have hne : h - 1 ≠ h - 2 := by omega

  have hsum : ∑ z ∈ (Finset.range h).powerset, (if h - 1 ∈ z ∧ h - 2 ∈ z then 3 else 4) +
      ((Finset.range h).powerset.filter (fun z => h - 1 ∈ z ∧ h - 2 ∈ z)).card =
      ∑ _z ∈ (Finset.range h).powerset, 4 := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : h - 1 ∈ z ∧ h - 2 ∈ z <;> simp [hz]
  have htot : ∑ _z ∈ (Finset.range h).powerset, 4 = 4 * 2 ^ h := by
    simp [Finset.card_powerset, Finset.card_range, mul_comm]
  have hbad : ((Finset.range h).powerset.filter (fun z => h - 1 ∈ z ∧ h - 2 ∈ z)).card =
      2 ^ (h - 2) := by
    have hbij : ((Finset.range h).powerset.filter (fun z => h - 1 ∈ z ∧ h - 2 ∈ z)) =
        ((Finset.range (h - 2)).powerset).image (fun s => insert (h - 1) (insert (h - 2) s)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      constructor
      · rintro ⟨hz, hz1, hz2⟩
        refine ⟨z.erase (h - 1) |>.erase (h - 2), ?_, ?_⟩
        · intro x hx
          have hx' : x ∈ z ∧ x ≠ h - 1 ∧ x ≠ h - 2 := by
            simp only [Finset.mem_erase] at hx
            exact ⟨hx.2.2, hx.2.1, hx.1⟩
          have hxr := Finset.mem_range.mp (hz hx'.1)
          exact Finset.mem_range.mpr (by omega)
        · ext x
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hx1 : x = h - 1
          · subst hx1; simp [hz1]
          · by_cases hx2 : x = h - 2
            · subst hx2; simp [hz2, hx1]
            · simp [hx1, hx2]
      · rintro ⟨s, hs, rfl⟩
        refine ⟨?_, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
        intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hxs
        · exact h1
        · exact h2
        · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hxs); omega)
    rw [hbij, Finset.card_image_of_injOn]
    · simp [Finset.card_powerset, Finset.card_range]
    · intro s₁ hs₁ s₂ hs₂ heq
      ext x
      have hx1 : ∀ s ∈ (Finset.range (h - 2)).powerset, h - 1 ∉ s ∧ h - 2 ∉ s := by
        intro s hs
        rw [Finset.mem_powerset] at hs
        constructor <;> intro hm <;> have := Finset.mem_range.mp (hs hm) <;> omega
      have := Finset.ext_iff.mp heq x
      simp only [Finset.mem_insert] at this
      have h1a := hx1 s₁ hs₁
      have h2a := hx1 s₂ hs₂
      by_cases hxh1 : x = h - 1
      · subst hxh1; simp [h1a.1, h2a.1]
      · by_cases hxh2 : x = h - 2
        · subst hxh2; simp [h1a.2, h2a.2]
        · simpa [hxh1, hxh2] using this
  have hpow : 2 ^ h = 4 * 2 ^ (h - 2) := by
    have : h = (h - 2) + 2 := by omega
    conv_lhs => rw [this, pow_add]
    omega
  omega

private lemma card_image_pairs {h : Nat} (g : Finset Nat → Nat → Finset Nat) :
    ((Finset.range (2 ^ (h + 2))).image (fun u =>
      let z := (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
      (z, g z u))).card =
    ∑ z ∈ (Finset.range h).powerset,
      ((Finset.univ : Finset (Bool × Bool)).image (fun p => g z (recon h z p.1 p.2))).card := by
  let first := fun u : Nat => (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let S := (Finset.range (2 ^ (h + 2))).image (fun u => (first u, g (first u) u))
  have hmap : ∀ p ∈ S, p.1 ∈ (Finset.range h).powerset := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨u, _, rfl⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro z hz
  have hzsub : z ⊆ Finset.range h := Finset.mem_powerset.mp hz
  have hfib : S.filter (fun p => p.1 = z) =
      ((Finset.univ : Finset (Bool × Bool)).image (fun p => (z, g z (recon h z p.1 p.2)))) := by
    ext ⟨z', y⟩
    simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨u, hu, rfl, rfl⟩, rfl⟩
      refine ⟨(u.testBit h, u.testBit (h + 1)), rfl, ?_⟩
      rw [recon_first_eq hu]
    · rintro ⟨⟨a, b⟩, rfl, rfl⟩
      refine ⟨⟨recon h z a b, recon_lt h z a b, first_recon h hzsub a b, ?_⟩, rfl⟩
      dsimp only [first]
      rw [first_recon h hzsub a b]
  have hfib' : S.filter (fun p => p.1 = z) =
      ((Finset.univ : Finset (Bool × Bool)).image (fun p => g z (recon h z p.1 p.2))).image
        (fun y => (z, y)) := by
    rw [hfib, Finset.image_image]
    rfl
  rw [hfib', Finset.card_image_of_injective _ (fun _ _ hxy => (Prod.mk.inj hxy).2)]

theorem main_proof : (∀ (h d : Nat), 4 ≤ h → 0 < d →
  let strips := Finset.range (2^(h+2))
  let limit := 2^(h+2+2*d)
  let mix := fun (x i : Nat) =>
    xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let first := fun u : Nat =>
    (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let count := fun (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat) =>
    (strips.image (fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
      (z, (mask z).filter (fun j => chi bits j)))).card
  (∃ x y : Nat, x < limit ∧ y < limit ∧
    count (fun z => if h-1 ∈ z then y else x)
      (fun _ => {h-4,h-2,h-1}) = 15 * 2^(h-2)) ∧
  ∀ (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat),
    (∀ z ∈ strips.image first, pick z < limit ∧ mask z ⊆ Finset.range h ∧
      (h-3 ∉ mask z ∨ h-2 ∉ mask z)) →
    count pick mask ≤ 15 * 2^(h-2)) := by
  intro h d hh hd
  dsimp only
  constructor
  ·
    let bx : Nat → Bool := fun i => decide (i = h - 3) || decide (i = h)
    let by_ : Nat → Bool := fun i => decide (i = h - 2) || decide (i = h - 1) || decide (i = h)
    let x := packBits (solveMix (h + 2) d hd bx) (h + 2)
    let y := packBits (solveMix (h + 2) d hd by_) (h + 2)
    have hx : x < 2 ^ (h + 2 + 2 * d) :=
      lt_of_lt_of_le (packBits_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega))
    have hy : y < 2 ^ (h + 2 + 2 * d) :=
      lt_of_lt_of_le (packBits_lt _ _) (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨x, y, hx, hy, ?_⟩
    refine (card_image_pairs (h := h) (g := fun z u =>
      ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j =>
        chi (fun i => xor (u.testBit i) (mix d (if h - 1 ∈ z then y else x) i)) j))).trans ?_
    rw [← sum_fiber_budget hh]
    apply Finset.sum_congr rfl
    intro z hz

    let z4 := decide (h - 4 ∈ z)
    let z3 := decide (h - 3 ∈ z)
    let z2 := decide (h - 2 ∈ z)
    let z1 := decide (h - 1 ∈ z)
    have hcard_eq :
        ((Finset.univ : Finset (Bool × Bool)).image (fun p =>
          ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j =>
            chi (fun i => xor ((recon h z p.1 p.2).testBit i)
              (mix d (if h - 1 ∈ z then y else x) i)) j))).card =
        ((Finset.univ : Finset (Bool × Bool)).image (fun p => lowerOut z4 z3 z2 z1 p.1 p.2)).card := by
      let enc : Bool × Bool × Bool → Finset Nat := fun t =>
        (if t.1 then {h - 4} else ∅) ∪ (if t.2.1 then {h - 2} else ∅) ∪ (if t.2.2 then {h - 1} else ∅)
      have henc_mem : ∀ (t : Bool × Bool × Bool) (j : Nat),
          j ∈ enc t ↔
            (j = h - 4 ∧ t.1 = true) ∨ (j = h - 2 ∧ t.2.1 = true) ∨ (j = h - 1 ∧ t.2.2 = true) := by
        rintro ⟨a, b, c⟩ j
        cases a <;> cases b <;> cases c <;> simp [enc]; tauto
      have henc_inj : Function.Injective enc := by
        rintro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hEq
        have h42 : h - 4 ≠ h - 2 := by omega
        have h41 : h - 4 ≠ h - 1 := by omega
        have h21 : h - 2 ≠ h - 1 := by omega
        have ha : a1 = a2 := by
          have := (henc_mem (a1, b1, c1) (h - 4)).symm.trans
            ((Finset.ext_iff.mp hEq (h - 4)).trans (henc_mem (a2, b2, c2) (h - 4)))
          simpa [h42, h41] using this
        have hb : b1 = b2 := by
          have := (henc_mem (a1, b1, c1) (h - 2)).symm.trans
            ((Finset.ext_iff.mp hEq (h - 2)).trans (henc_mem (a2, b2, c2) (h - 2)))
          simpa [Ne.symm h42, h21] using this
        have hc : c1 = c2 := by
          have := (henc_mem (a1, b1, c1) (h - 1)).symm.trans
            ((Finset.ext_iff.mp hEq (h - 1)).trans (henc_mem (a2, b2, c2) (h - 1)))
          simpa [Ne.symm h41, Ne.symm h21] using this
        subst ha; subst hb; subst hc; rfl
      have hfun : ∀ p : Bool × Bool,
          ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j =>
            chi (fun i => xor ((recon h z p.1 p.2).testBit i)
              (mix d (if h - 1 ∈ z then y else x) i)) j) =
          enc (lowerOut z4 z3 z2 z1 p.1 p.2) := by
        intro ⟨a, b⟩
        have hmx : ∀ i < h + 2, mix d (if h - 1 ∈ z then y else x) i =
            if h - 1 ∈ z then by_ i else bx i := by
          intro i hi
          split
          · exact mix_packBits_solveMix hd by_ hi
          · exact mix_packBits_solveMix hd bx hi
        have hu1 : reconBit h z a b (h - 1) = xor z1 (!a && b) := by
          rw [reconBit_of_lt (by omega)]
          have e1 : h - 1 + 1 = h := by omega
          have e2 : h - 1 + 2 = h + 1 := by omega
          rw [e1, e2, reconBit_h, reconBit_h1]
        have hu2 : reconBit h z a b (h - 2) = xor z2 (!(reconBit h z a b (h - 1)) && a) := by
          rw [reconBit_of_lt (by omega)]
          have e1 : h - 2 + 1 = h - 1 := by omega
          have e2 : h - 2 + 2 = h := by omega
          rw [e1, e2, reconBit_h]
        have hu3 : reconBit h z a b (h - 3) =
            xor z3 (!(reconBit h z a b (h - 2)) && reconBit h z a b (h - 1)) := by
          rw [reconBit_of_lt (by omega)]
          have e1 : h - 3 + 1 = h - 2 := by omega
          have e2 : h - 3 + 2 = h - 1 := by omega
          rw [e1, e2]
        have hu4 : reconBit h z a b (h - 4) =
            xor z4 (!(reconBit h z a b (h - 3)) && reconBit h z a b (h - 2)) := by
          rw [reconBit_of_lt (by omega)]
          have e1 : h - 4 + 1 = h - 3 := by omega
          have e2 : h - 4 + 2 = h - 2 := by omega
          rw [e1, e2]
        have hbit : ∀ i < h + 2,
            xor ((recon h z a b).testBit i) (mix d (if h - 1 ∈ z then y else x) i) =
            xor (reconBit h z a b i) (if h - 1 ∈ z then by_ i else bx i) := by
          intro i hi
          rw [testBit_recon, hmx i hi]
        have hc4 : chi (fun i => xor ((recon h z a b).testBit i)
            (mix d (if h - 1 ∈ z then y else x) i)) (h - 4) = (lowerOut z4 z3 z2 z1 a b).1 := by
          simp only [chi]
          have e1 : h - 4 + 1 = h - 3 := by omega
          have e2 : h - 4 + 2 = h - 2 := by omega
          rw [e1, e2, hbit (h - 4) (by omega), hbit (h - 3) (by omega), hbit (h - 2) (by omega)]
          rw [hu4, hu3, hu2, hu1]
          simp only [lowerOut, bx, by_, z1]
          have hn1 : h - 4 ≠ h - 3 := by omega
          have hn2 : h - 4 ≠ h - 2 := by omega
          have hn3 : h - 4 ≠ h - 1 := by omega
          have hn4 : h - 4 ≠ h := by omega
          have hn5 : h - 3 ≠ h - 2 := by omega
          have hn5' : h - 2 ≠ h - 3 := by omega
          have hn6 : h - 3 ≠ h - 1 := by omega
          have hn7 : h - 3 ≠ h := by omega
          have hn8 : h - 2 ≠ h - 1 := by omega
          have hn9 : h - 2 ≠ h := by omega
          by_cases hz1 : h - 1 ∈ z <;> simp [hz1, hn1, hn2, hn3, hn4, hn5, hn5', hn6, hn7, hn8, hn9]
        have hc2 : chi (fun i => xor ((recon h z a b).testBit i)
            (mix d (if h - 1 ∈ z then y else x) i)) (h - 2) = (lowerOut z4 z3 z2 z1 a b).2.1 := by
          simp only [chi]
          have e1 : h - 2 + 1 = h - 1 := by omega
          have e2 : h - 2 + 2 = h := by omega
          rw [e1, e2, hbit (h - 2) (by omega), hbit (h - 1) (by omega), hbit h (by omega)]
          rw [hu2, hu1, reconBit_h]
          simp only [lowerOut, bx, by_, z1]
          have hn1 : h - 2 ≠ h - 3 := by omega
          have hn2 : h - 2 ≠ h - 1 := by omega
          have hn3 : h - 2 ≠ h := by omega
          have hn4 : h - 1 ≠ h - 3 := by omega
          have hn5 : h - 1 ≠ h - 2 := by omega
          have hn6 : h - 1 ≠ h := by omega
          have hn7 : h ≠ h - 3 := by omega
          have hn8 : h ≠ h - 2 := by omega
          have hn9 : h ≠ h - 1 := by omega
          by_cases hz1 : h - 1 ∈ z <;> simp [hz1, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
        have hc1 : chi (fun i => xor ((recon h z a b).testBit i)
            (mix d (if h - 1 ∈ z then y else x) i)) (h - 1) = (lowerOut z4 z3 z2 z1 a b).2.2 := by
          simp only [chi]
          have e1 : h - 1 + 1 = h := by omega
          have e2 : h - 1 + 2 = h + 1 := by omega
          rw [e1, e2, hbit (h - 1) (by omega), hbit h (by omega), hbit (h + 1) (by omega)]
          rw [hu1, reconBit_h, reconBit_h1]
          simp only [lowerOut, bx, by_, z1]
          have hn1 : h - 1 ≠ h - 3 := by omega
          have hn2 : h - 1 ≠ h - 2 := by omega
          have hn3 : h - 1 ≠ h := by omega
          have hn4 : h ≠ h - 3 := by omega
          have hn5 : h ≠ h - 2 := by omega
          have hn6 : h ≠ h - 1 := by omega
          have hn7 : h + 1 ≠ h - 3 := by omega
          have hn8 : h + 1 ≠ h - 2 := by omega
          have hn9 : h + 1 ≠ h - 1 := by omega
          have hn10 : h + 1 ≠ h := by omega
          by_cases hz1 : h - 1 ∈ z <;>
            simp [hz1, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
        ext j
        rw [Finset.mem_filter, henc_mem]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hcj⟩
          · exact Or.inl ⟨rfl, hc4 ▸ hcj⟩
          · exact Or.inr (Or.inl ⟨rfl, hc2 ▸ hcj⟩)
          · exact Or.inr (Or.inr ⟨rfl, hc1 ▸ hcj⟩)
        · rintro (⟨rfl, hcj⟩ | ⟨rfl, hcj⟩ | ⟨rfl, hcj⟩)
          · exact ⟨Or.inl rfl, hc4.symm ▸ hcj⟩
          · exact ⟨Or.inr (Or.inl rfl), hc2.symm ▸ hcj⟩
          · exact ⟨Or.inr (Or.inr rfl), hc1.symm ▸ hcj⟩
      have himg : ((Finset.univ : Finset (Bool × Bool)).image (fun p =>
            ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j =>
              chi (fun i => xor ((recon h z p.1 p.2).testBit i)
                (mix d (if h - 1 ∈ z then y else x) i)) j))) =
          ((Finset.univ : Finset (Bool × Bool)).image (fun p => lowerOut z4 z3 z2 z1 p.1 p.2)).image enc := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro p _
        exact hfun p
      rw [himg, Finset.card_image_of_injective _ henc_inj]
    rw [hcard_eq, lower_card_eq]
    by_cases hz1 : h - 1 ∈ z <;> by_cases hz2 : h - 2 ∈ z <;> simp [z1, z2, hz1, hz2]
  ·
    intro pick mask hcond
    refine le_of_eq_of_le (card_image_pairs (h := h) (g := fun z u =>
      (mask z).filter (fun j =>
        chi (fun i => xor (u.testBit i) (mix d (pick z) i)) j))) ?_
    rw [← sum_fiber_budget hh]
    apply Finset.sum_le_sum
    intro z hz
    have hz_img : z ∈ (Finset.range (2 ^ (h + 2))).image
        (fun u => (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)) := by
      refine Finset.mem_image.mpr ⟨recon h z false false,
        Finset.mem_range.mpr (recon_lt h z false false),
        first_recon h (Finset.mem_powerset.mp hz) false false⟩
    have ⟨_, hmask_sub, hmiss⟩ := hcond z hz_img
    by_cases hbad : h - 1 ∈ z ∧ h - 2 ∈ z
    · simp only [hbad]

      let f : Bool × Bool → Finset Nat := fun p =>
        (mask z).filter (fun j =>
          chi (fun i => xor ((recon h z p.1 p.2).testBit i) (mix d (pick z) i)) j)
      suffices ∃ p q : Bool × Bool, p ≠ q ∧ f p = f q by
        rcases this with ⟨p, q, hpq, hfpq⟩
        have hsub : (Finset.univ : Finset (Bool × Bool)).image f ⊆
            ((Finset.univ : Finset (Bool × Bool)).erase q).image f := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨r, _, rfl⟩
          by_cases hrq : r = q
          · subst hrq
            exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ _⟩, hfpq⟩
          · exact Finset.mem_image.mpr ⟨r, Finset.mem_erase.mpr ⟨hrq, Finset.mem_univ _⟩, rfl⟩
        calc ((Finset.univ : Finset (Bool × Bool)).image f).card
            ≤ (((Finset.univ : Finset (Bool × Bool)).erase q).image f).card :=
              Finset.card_le_card hsub
          _ ≤ ((Finset.univ : Finset (Bool × Bool)).erase q).card := Finset.card_image_le
          _ = 3 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ q)]
              decide
      let m3 := mix d (pick z) (h - 3)
      let m2 := mix d (pick z) (h - 2)
      let m1 := mix d (pick z) (h - 1)
      let m0 := mix d (pick z) h
      let mp := mix d (pick z) (h + 1)
      let u3 := reconBit h z false false (h - 3)
      have hagree : ∀ p q : Bool × Bool, ∀ j ≤ h - 4,
          chi (fun i => xor ((recon h z p.1 p.2).testBit i) (mix d (pick z) i)) j =
          chi (fun i => xor ((recon h z q.1 q.2).testBit i) (mix d (pick z) i)) j := by
        intro p q j hj
        have hp := (reconBit_eq_of_bad hh hbad.1 hbad.2 p.1 p.2).2.2
        have hq := (reconBit_eq_of_bad hh hbad.1 hbad.2 q.1 q.2).2.2
        simp only [chi, testBit_recon]
        rw [hp j (by omega), hp (j + 1) (by omega), hp (j + 2) (by omega),
            hq j (by omega), hq (j + 1) (by omega), hq (j + 2) (by omega)]
      have hbadChi : ∀ p : Bool × Bool,
          chi (fun i => xor ((recon h z p.1 p.2).testBit i) (mix d (pick z) i)) (h - 3) =
            badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨0, by omega⟩ ∧
          chi (fun i => xor ((recon h z p.1 p.2).testBit i) (mix d (pick z) i)) (h - 2) =
            badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨1, by omega⟩ ∧
          chi (fun i => xor ((recon h z p.1 p.2).testBit i) (mix d (pick z) i)) (h - 1) =
            badChi m3 m2 m1 m0 mp u3 p.1 p.2 ⟨2, by omega⟩ := by
        intro ⟨a, b⟩
        have hrec := reconBit_eq_of_bad hh hbad.1 hbad.2 a b
        refine ⟨?_, ?_, ?_⟩
        · simp only [chi, testBit_recon, badChi]
          have e1 : h - 3 + 1 = h - 2 := by omega
          have e2 : h - 3 + 2 = h - 1 := by omega
          rw [e1, e2, hrec.2.2 (h - 3) (by omega), hrec.2.1, hrec.1]
        · simp only [chi, testBit_recon, badChi]
          have e1 : h - 2 + 1 = h - 1 := by omega
          have e2 : h - 2 + 2 = h := by omega
          rw [e1, e2, hrec.2.1, hrec.1, reconBit_h]
        · simp only [chi, testBit_recon, badChi]
          have e1 : h - 1 + 1 = h := by omega
          have e2 : h - 1 + 2 = h + 1 := by omega
          rw [e1, e2, hrec.1, reconBit_h, reconBit_h1]
      rcases hmiss with hno3 | hno2
      · rcases bad_collision_drop3 m3 m2 m1 m0 mp u3 with ⟨p, q, hpq, hc2, hc1⟩
        refine ⟨p, q, hpq, ?_⟩
        ext j
        simp only [f, Finset.mem_filter]
        constructor <;> rintro ⟨hjm, hcj⟩ <;> refine ⟨hjm, ?_⟩
        · have hjlt : j < h := Finset.mem_range.mp (hmask_sub hjm)
          by_cases hj1 : j = h - 1
          · subst hj1; rw [(hbadChi p).2.2] at hcj; rw [(hbadChi q).2.2, ← hc1]; exact hcj
          · by_cases hj2 : j = h - 2
            · subst hj2; rw [(hbadChi p).2.1] at hcj; rw [(hbadChi q).2.1, ← hc2]; exact hcj
            · have hj3 : j ≠ h - 3 := fun he => hno3 (he ▸ hjm)
              rw [← hagree p q j (by omega)]; exact hcj
        · have hjlt : j < h := Finset.mem_range.mp (hmask_sub hjm)
          by_cases hj1 : j = h - 1
          · subst hj1; rw [(hbadChi q).2.2] at hcj; rw [(hbadChi p).2.2, hc1]; exact hcj
          · by_cases hj2 : j = h - 2
            · subst hj2; rw [(hbadChi q).2.1] at hcj; rw [(hbadChi p).2.1, hc2]; exact hcj
            · have hj3 : j ≠ h - 3 := fun he => hno3 (he ▸ hjm)
              rw [hagree p q j (by omega)]; exact hcj
      · rcases bad_collision_drop2 m3 m2 m1 m0 mp u3 with ⟨p, q, hpq, hc3, hc1⟩
        refine ⟨p, q, hpq, ?_⟩
        ext j
        simp only [f, Finset.mem_filter]
        constructor <;> rintro ⟨hjm, hcj⟩ <;> refine ⟨hjm, ?_⟩
        · have hjlt : j < h := Finset.mem_range.mp (hmask_sub hjm)
          by_cases hj1 : j = h - 1
          · subst hj1; rw [(hbadChi p).2.2] at hcj; rw [(hbadChi q).2.2, ← hc1]; exact hcj
          · by_cases hj3 : j = h - 3
            · subst hj3; rw [(hbadChi p).1] at hcj; rw [(hbadChi q).1, ← hc3]; exact hcj
            · have hj2 : j ≠ h - 2 := fun he => hno2 (he ▸ hjm)
              rw [← hagree p q j (by omega)]; exact hcj
        · have hjlt : j < h := Finset.mem_range.mp (hmask_sub hjm)
          by_cases hj1 : j = h - 1
          · subst hj1; rw [(hbadChi q).2.2] at hcj; rw [(hbadChi p).2.2, hc1]; exact hcj
          · by_cases hj3 : j = h - 3
            · subst hj3; rw [(hbadChi q).1] at hcj; rw [(hbadChi p).1, hc3]; exact hcj
            · have hj2 : j ≠ h - 2 := fun he => hno2 (he ▸ hjm)
              rw [hagree p q j (by omega)]; exact hcj
    · simp only [hbad, ite_false]
      calc ((Finset.univ : Finset (Bool × Bool)).image _).card
          ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_image_le
        _ = 4 := by decide

end PEqualNP.Outside.L_meta_38164

theorem PEqualNP.Outside.L_meta_38164 : (∀ (h d : Nat), 4 ≤ h → 0 < d →
  let strips := Finset.range (2^(h+2))
  let limit := 2^(h+2+2*d)
  let mix := fun (x i : Nat) =>
    xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let first := fun u : Nat =>
    (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let count := fun (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat) =>
    (strips.image (fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
      (z, (mask z).filter (fun j => chi bits j)))).card
  (∃ x y : Nat, x < limit ∧ y < limit ∧
    count (fun z => if h-1 ∈ z then y else x)
      (fun _ => {h-4,h-2,h-1}) = 15 * 2^(h-2)) ∧
  ∀ (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat),
    (∀ z ∈ strips.image first, pick z < limit ∧ mask z ⊆ Finset.range h ∧
      (h-3 ∉ mask z ∨ h-2 ∉ mask z)) →
    count pick mask ≤ 15 * 2^(h-2)) := by
  exact PEqualNP.Outside.L_meta_38164.main_proof
