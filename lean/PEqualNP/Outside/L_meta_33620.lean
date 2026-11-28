import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25883

namespace PEqualNP.Outside.L_meta_33620_aux

open PEqualNP.Outside.L_meta_25883_aux

-- Bit packing into Nat < 2^n

def packBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if f n then packBits f n ^^^ 2^n else packBits f n

lemma packBits_lt (f : Nat → Bool) : ∀ n, packBits f n < 2^n
  | 0 => by simp [packBits]
  | n + 1 => by
    have ih := packBits_lt f n
    have h1 : packBits f n < 2^(n + 1) :=
      lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : 2^n < 2^(n + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [packBits]
    split_ifs
    · exact Nat.xor_lt_two_pow h1 h2
    · exact h1

lemma packBits_testBit (f : Nat → Bool) :
    ∀ n t, (packBits f n).testBit t = (decide (t < n) && f t)
  | 0, t => by simp [packBits]
  | n + 1, t => by
    have ih := packBits_testBit f n t
    by_cases hlt : t < n
    · have hne : n ≠ t := by omega
      simp only [packBits]
      split_ifs
      · rw [Nat.testBit_xor, Nat.testBit_two_pow, ih]
        simp [hlt, hne, show t < n + 1 by omega]
      · rw [ih]
        simp [hlt, show t < n + 1 by omega]
    · by_cases heq : t = n
      · subst heq
        have h0 : (packBits f t).testBit t = false := Nat.testBit_lt_two_pow (packBits_lt f t)
        simp only [packBits]
        split_ifs with hf
        · rw [Nat.testBit_xor, Nat.testBit_two_pow, h0]
          simp [hf]
        · rw [h0]
          simp [hf]
      · have hgt : n + 1 ≤ t := by omega
        have hlt2 : packBits f (n + 1) < 2^t :=
          lt_of_lt_of_le (packBits_lt f (n + 1)) (Nat.pow_le_pow_right (by decide) hgt)
        rw [Nat.testBit_lt_two_pow hlt2]
        have hnot : ¬ (t < n + 1) := by omega
        simp [hnot]

lemma packBits_testBit_of_lt {f : Nat → Bool} {n t : Nat} (ht : t < n) :
    (packBits f n).testBit t = f t := by
  rw [packBits_testBit, decide_eq_true ht, Bool.true_and]

lemma eq_of_testBit_lt {n z z' : Nat} (hz : z < 2^n) (hz' : z' < 2^n)
    (h : ∀ t < n, z.testBit t = z'.testBit t) : z = z' := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < n
  · exact h t ht
  · have h1 : z.testBit t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : z'.testBit t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hz' (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [h1, h2]

-- Strip maps and polar algebra

def polar (b1 b2 : Bool) : Bool := !b1 && b2

def Fbit (z j : Nat) : Bool :=
  xor (z.testBit j) (polar (z.testBit (j + 1)) (z.testBit (j + 2)))

def FbitH (h : Nat → Bool) (z j : Nat) : Bool :=
  xor (xor (z.testBit j) (h j))
    (polar (xor (z.testBit (j + 1)) (h (j + 1))) (xor (z.testBit (j + 2)) (h (j + 2))))

def phi (a : Nat) (h : Nat → Bool) (z : Nat) : Finset Nat × Finset Nat :=
  ((Finset.range a).filter (fun j => Fbit z j),
   (Finset.range a).filter (fun j => FbitH h z j))

lemma polar_shift_eq (z1 z2 h1 h2 d1 d2 : Bool)
    (hc1 : h1 = false → h2 = true → d1 = false)
    (hc2 : h1 = true → h2 = false → d2 = false)
    (hc3 : h1 = true → h2 = true → d1 = d2) :
    xor (polar z1 z2) (polar (xor z1 d1) (xor z2 d2)) =
      xor (polar (xor z1 h1) (xor z2 h2))
        (polar (xor (xor z1 d1) h1) (xor (xor z2 d2) h2)) := by
  revert z1 z2 h1 h2 d1 d2 hc1 hc2 hc3
  decide

lemma F_shift_eq (z0 z0' h0 p0 p0' q0 q0' : Bool)
    (hF : xor z0 p0 = xor z0' p0')
    (hP : xor p0 p0' = xor q0 q0') :
    xor (xor z0 h0) q0 = xor (xor z0' h0) q0' := by
  revert z0 z0' h0 p0 p0' q0 q0' hF hP
  decide

lemma F_eq_of_delta (z0 d0 p0 p0' : Bool) (h : d0 = xor p0 p0') :
    xor (xor z0 d0) p0' = xor z0 p0 := by
  revert z0 d0 p0 p0' h
  decide

lemma polar_flip_same (b : Bool) :
    xor (polar b b) (polar (xor b true) (xor b true)) = false := by
  revert b; decide

lemma polar_flip_diff (b1 b2 : Bool) (h : b1 = !b2) :
    xor (polar b1 b2) (polar (xor b1 true) (xor b2 true)) = true := by
  revert b1 b2 h; decide

lemma allOnes_xor_eq (z0 z1 z2 z0' z1' z2' : Bool)
    (h1 : xor z0 (polar z1 z2) = xor z0' (polar z1' z2'))
    (h2 : xor (xor z0 true) (polar (xor z1 true) (xor z2 true)) =
          xor (xor z0' true) (polar (xor z1' true) (xor z2' true))) :
    xor z1 z1' = xor z2 z2' := by
  revert z0 z1 z2 z0' z1' z2' h1 h2
  decide

lemma allOnes_alt_step (z0 z1 z2 : Bool)
    (h : xor z0 (polar z1 z2) = xor (!z0) (polar (!z1) (!z2))) :
    z2 = !z1 := by
  revert z0 z1 z2 h
  decide

lemma allOnes_same_zero (z0 z1 z2 z0' : Bool)
    (h : xor z0 (polar z1 z2) = xor z0' (polar z1 z2)) :
    z0 = z0' := by
  revert z0 z1 z2 z0' h
  decide

-- Connecting count x y to image of phi on Finset.range (2^(a+2))

def shiftPair (Lx Ly : Nat → Bool) (a : Nat) (p : Finset Nat × Finset Nat) :
    Finset Nat × Finset Nat :=
  ((Finset.range a).filter (fun j => xor (decide (j ∈ p.1)) (Lx j)),
   (Finset.range a).filter (fun j => xor (decide (j ∈ p.2)) (Ly j)))

lemma shiftPair_invol (Lx Ly : Nat → Bool) (a : Nat) (p : Finset Nat × Finset Nat)
    (h1 : p.1 ⊆ Finset.range a) (h2 : p.2 ⊆ Finset.range a) :
    shiftPair Lx Ly a (shiftPair Lx Ly a p) = p := by
  rcases p with ⟨s1, s2⟩
  dsimp only [shiftPair]
  congr 1
  · ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hj, hxor⟩
      by_cases hm : j ∈ s1
      · exact hm
      · simp [hj, hm] at hxor
    · intro hm
      have hj : j < a := Finset.mem_range.mp (h1 hm)
      refine ⟨hj, ?_⟩
      simp [hj, hm]
  · ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hj, hxor⟩
      by_cases hm : j ∈ s2
      · exact hm
      · simp [hj, hm] at hxor
    · intro hm
      have hj : j < a := Finset.mem_range.mp (h2 hm)
      refine ⟨hj, ?_⟩
      simp [hj, hm]

lemma count_eq_phi_card {k d a start init last c x y : Nat}
    (hd : 0 < d) (hk : a + 2 + 2 * d ≤ k) :
    let words := Finset.range (2^k)
    let response := fun (u w : Nat) => (Finset.range a).filter (fun j => label k d start init last c u w j)
    let h := fun t => xor ((mix k d (rot k init x)).testBit (site k start t))
                          ((mix k d (rot k init y)).testBit (site k start t))
    (words.image (fun u => (response u x, response u y))).card =
      ((Finset.range (2^(a + 2))).image (phi a h)).card := by
  intro words response h
  have hk0 : 0 < k := by omega
  have hdk : d < k := by omega
  let rx : Nat → Bool := fun t => (mix k d (rot k init x)).testBit (site k start t)
  let ry : Nat → Bool := fun t => (mix k d (rot k init y)).testBit (site k start t)
  let Lx : Nat → Bool := fun j => xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j))
  let Ly : Nat → Bool := fun j => xor ((rot k last y).testBit (site k start j)) (c.testBit (site k start j))
  let strip : Nat → Nat := fun u =>
    packBits (fun t => (mix k d (rot k init x ^^^ u)).testBit (site k start t)) (a + 2)
  have hstrip_lt : ∀ u, strip u < 2^(a + 2) := fun u => packBits_lt _ _
  have hstrip_bit : ∀ u t, t < a + 2 →
      (strip u).testBit t = (mix k d (rot k init x ^^^ u)).testBit (site k start t) :=
    fun u t ht => packBits_testBit_of_lt ht
  have hstrip_bit_y : ∀ u, u < 2^k → ∀ t, t < a + 2 →
      xor ((strip u).testBit t) (h t) = (mix k d (rot k init y ^^^ u)).testBit (site k start t) := by
    intro u hu t ht
    rw [hstrip_bit u t ht]
    have hs := site_lt hk0 start t
    rw [mixLin hd hdk hs (rot_lt _ _ _) hu, mixLin hd hdk hs (rot_lt _ _ _) hu]
    dsimp only [h]
    generalize (mix k d (rot k init x)).testBit (site k start t) = A
    generalize (mix k d (rot k init y)).testBit (site k start t) = B
    generalize (mix k d u).testBit (site k start t) = C
    revert A B C; decide
  have hresp_eq : ∀ u ∈ words,
      (response u x, response u y) = shiftPair Lx Ly a (phi a h (strip u)) := by
    intro u hu
    have hu' : u < 2^k := Finset.mem_range.mp hu
    dsimp only [response, shiftPair, phi]
    congr 1
    · apply Finset.filter_congr
      intro j hj
      have hj' : j < a := Finset.mem_range.mp hj
      have hm : decide (j ∈ (Finset.range a).filter (fun j => Fbit (strip u) j)) = Fbit (strip u) j := by
        simp [Finset.mem_filter, Finset.mem_range, hj']
      rw [hm]
      dsimp only [Fbit, polar, label, Lx]
      rw [hstrip_bit u j (by omega), hstrip_bit u (j + 1) (by omega), hstrip_bit u (j + 2) (by omega)]
    · apply Finset.filter_congr
      intro j hj
      have hj' : j < a := Finset.mem_range.mp hj
      have hm : decide (j ∈ (Finset.range a).filter (fun j => FbitH h (strip u) j)) = FbitH h (strip u) j := by
        simp [Finset.mem_filter, Finset.mem_range, hj']
      rw [hm]
      dsimp only [FbitH, polar, label, Ly]
      rw [hstrip_bit_y u hu' j (by omega), hstrip_bit_y u hu' (j + 1) (by omega),
          hstrip_bit_y u hu' (j + 2) (by omega)]
  have hsurj : ∀ z < 2^(a + 2), ∃ u ∈ words, strip u = z := by
    intro z hz
    have hcnt := count k (fun u t => (mix k d u).testBit (site k start t))
      (fun t => (site k start t + d) % k)
      (fun t => xor (rx t) (z.testBit t))
      (a + 2) (by omega) (fun t _ => Nat.mod_lt _ hk0)
      (by
        intro t ht w hw
        show (mix k d (w ^^^ 2^((site k start t + d) % k))).testBit (site k start t) = _
        rw [mixFlip hd hdk (site_lt hk0 _ _) hw (Nat.mod_lt _ hk0), indName start hd hk ht]
        simp)
      (by
        intro t ht t' ht' w hw
        show (mix k d (w ^^^ 2^((site k start t + d) % k))).testBit (site k start t') = _
        rw [mixFlip hd hdk (site_lt hk0 _ _) hw (Nat.mod_lt _ hk0), indName' start hd hk ht ht']
        simp)
    have hpos : 0 < ((Finset.range (2^k)).filter
        (fun u => ∀ t < a + 2, (mix k d u).testBit (site k start t) = xor (rx t) (z.testBit t))).card := by
      rw [hcnt]; positivity
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    refine ⟨u, Finset.mem_range.mpr hu.1, ?_⟩
    apply eq_of_testBit_lt (hstrip_lt u) hz
    intro t ht
    rw [hstrip_bit u t ht, mixLin hd hdk (site_lt hk0 start t) (rot_lt _ _ _) hu.1, hu.2 t ht]
    dsimp only [rx]
    generalize (mix k d (rot k init x)).testBit (site k start t) = A
    generalize z.testBit t = B
    revert A B; decide
  have himg : words.image (fun u => (response u x, response u y)) =
      ((Finset.range (2^(a + 2))).image (phi a h)).image (shiftPair Lx Ly a) := by
    ext p
    simp only [words, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨phi a h (strip u), ⟨strip u, hstrip_lt u, rfl⟩, (hresp_eq u (Finset.mem_range.mpr hu)).symm⟩
    · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨u, hu, hsu⟩ := hsurj z hz
      refine ⟨u, Finset.mem_range.mp hu, ?_⟩
      rw [hresp_eq u hu, hsu]
  rw [himg]
  apply Finset.card_image_of_injOn
  intro p1 hp1 p2 hp2 heq
  simp only [Finset.mem_coe, Finset.mem_image] at hp1 hp2
  obtain ⟨z1, _, rfl⟩ := hp1
  obtain ⟨z2, _, rfl⟩ := hp2
  have h1 := shiftPair_invol Lx Ly a (phi a h z1) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h2 := shiftPair_invol Lx Ly a (phi a h z2) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← h1, ← h2, heq]

-- Finding y with all-ones mixed shift relative to x = 0

lemma exists_all_ones_y {k d a start init : Nat} (hd : 0 < d) (hk : a + 2 + 2 * d ≤ k) :
    ∃ y ∈ Finset.range (2^k),
      ∀ t < a + 2, (mix k d (rot k init y)).testBit (site k start t) = true := by
  have hk0 : 0 < k := by omega
  have hdk : d < k := by omega
  have hcnt := count k
    (fun y t => (mix k d (rot k init y)).testBit (site k start t))
    (fun t => (((site k start t + d) % k) + k - init % k) % k)
    (fun _ => true)
    (a + 2) (by omega) (fun t _ => Nat.mod_lt _ hk0)
    (by
      intro t ht w hw
      have hkf := keyFlip (k := k) (d := d) (j := site k start t)
        (q := (site k start t + d) % k) (key := w) (u := 0) init hd hdk
        (site_lt hk0 _ _) (Nat.mod_lt _ hk0) hw (by positivity)
      simp only [Nat.xor_zero] at hkf
      rw [hkf, indName start hd hk ht]; simp)
    (by
      intro t ht t' ht' w hw
      have hkf := keyFlip (k := k) (d := d) (j := site k start t')
        (q := (site k start t + d) % k) (key := w) (u := 0) init hd hdk
        (site_lt hk0 _ _) (Nat.mod_lt _ hk0) hw (by positivity)
      simp only [Nat.xor_zero] at hkf
      rw [hkf, indName' start hd hk ht ht']; simp)
  have hpos : 0 < ((Finset.range (2^k)).filter
      (fun y => ∀ t < a + 2, (mix k d (rot k init y)).testBit (site k start t) = true)).card := by
    rw [hcnt]; positivity
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hy
  exact ⟨y, hy.1, hy.2⟩

-- Upper bound infrastructure

def fourBools : Finset (Bool × Bool) :=
  {(false, false), (false, true), (true, false), (true, true)}

lemma card_fourBools : fourBools.card = 4 := by decide

lemma card_sdiff_eq {α : Type*} [DecidableEq α] {s t : Finset α} (h : t ⊆ s) :
    (s \ t).card = s.card - t.card := by
  have h1 : (s \ t).card + t.card = s.card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left, Finset.sdiff_union_of_subset h]
  omega

lemma card_image_le_of_shadow {α : Type*} [DecidableEq α] (n : Nat) (f : Nat → α)
    (A0 : Finset Nat) (hSub : A0 ⊆ Finset.range n) (hCard : 4 ≤ A0.card)
    (hShadow : ∀ z ∈ A0, ∃ z' ∈ Finset.range n \ A0, f z' = f z) :
    ((Finset.range n).image f).card ≤ n - 4 := by
  have hImg : (Finset.range n).image f ⊆ (Finset.range n \ A0).image f := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    by_cases hA : z ∈ A0
    · obtain ⟨z', hz', heq⟩ := hShadow z hA
      exact Finset.mem_image.mpr ⟨z', hz', heq⟩
    · exact Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hA⟩, rfl⟩
  have h1 := Finset.card_le_card hImg
  have h2 := Finset.card_image_le (f := f) (s := Finset.range n \ A0)
  have h3 := card_sdiff_eq hSub
  rw [Finset.card_range] at h3
  omega

-- Case a = 1 upper bound

lemma phi_card_le_one (h : Nat → Bool) :
    ((Finset.range (2^(1 + 2))).image (phi 1 h)).card ≤ 2^(1 + 2) - 4 := by
  let S : Finset (Finset Nat × Finset Nat) :=
    {(∅, ∅), (∅, {0}), ({0}, ∅), ({0}, {0})}
  have hSub : (Finset.range (2^(1 + 2))).image (phi 1 h) ⊆ S := by
    intro p hp
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
    have hfilt : ∀ q : Nat → Bool, (Finset.range 1).filter (fun j => q j) = ∅ ∨
        (Finset.range 1).filter (fun j => q j) = {0} := by
      intro q
      cases hq : q 0
      · left; ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
        intro ⟨hj, hqj⟩; have : j = 0 := by omega
        subst this; simp [hq] at hqj
      · right; ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro ⟨hj, _⟩; omega
        · intro rfl; exact ⟨by omega, by simp [hq]⟩
    dsimp only [phi]
    rcases hfilt (Fbit z) with h1 | h1 <;> rcases hfilt (FbitH h z) with h2 | h2
    · rw [h1, h2]; simp [S]
    · rw [h1, h2]; simp [S]
    · rw [h1, h2]; simp [S]
    · rw [h1, h2]; simp [S]
  have hcard : S.card ≤ 4 := by
    dsimp only [S]
    calc _ ≤ _ + 1 := Finset.card_insert_le _ _
      _ ≤ (_ + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ((_ + 1) + 1) + 1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ = 4 := by simp
  have := Finset.card_le_card hSub
  omega

-- Run of ones containing a

def runStart (h : Nat → Bool) : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => if h (n + 1) then runStart h (n + 1) else n + 2

lemma runStart_spec (h : Nat → Bool) :
    ∀ a, 1 ≤ a → h a = true →
      let L := runStart h a
      1 ≤ L ∧ L ≤ a ∧ (∀ t, L ≤ t → t ≤ a → h t = true) ∧ (1 < L → h (L - 1) = false)
  | 0, ha, _ => by omega
  | 1, _, h1 => by
    simp only [runStart]
    refine ⟨by omega, by omega, ?_, by omega⟩
    intro t ht1 ht2
    have : t = 1 := by omega
    subst this; exact h1
  | n + 2, _, hn2 => by
    simp only [runStart]
    cases hn1 : h (n + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro t ht1 ht2
        have : t = n + 2 := by omega
        subst this; exact hn2
      · intro _; exact hn1
    · simp only [↓reduceIte]
      obtain ⟨hL1, hL2, hLall, hLprev⟩ := runStart_spec h (n + 1) (by omega) hn1
      refine ⟨hL1, by omega, ?_, hLprev⟩
      intro t ht1 ht2
      by_cases heq : t = n + 2
      · subst heq; exact hn2
      · exact hLall t ht1 (by omega)

def tailBit (a L t : Nat) : Bool :=
  if t < L then true
  else if t = a + 1 then decide (L < a)
  else if t = L ∧ L < a then decide ((a - (L + 1)) % 2 = 1)
  else decide ((a - t) % 2 = 1)

lemma tailBit_of_lt {a L t : Nat} (h : t < L) : tailBit a L t = true := by
  simp only [tailBit, h, ↓reduceIte]

lemma tailBit_last {a L : Nat} (h : L ≤ a) : tailBit a L (a + 1) = decide (L < a) := by
  simp only [tailBit, show ¬ (a + 1 < L) by omega, ↓reduceIte]

lemma tailBit_at_L {a L : Nat} (h : L < a) :
    tailBit a L L = decide ((a - (L + 1)) % 2 = 1) := by
  simp only [tailBit, show ¬ (L < L) by omega, show L ≠ a + 1 by omega, h, and_self, ↓reduceIte]

lemma tailBit_at_a {a L : Nat} (h : L ≤ a) : tailBit a L a = false := by
  simp only [tailBit, show ¬ (a < L) by omega, show a ≠ a + 1 by omega,
             show ¬ (a = L ∧ L < a) by omega, Nat.sub_self, Nat.zero_mod, ↓reduceIte]
  decide

lemma tailBit_mid {a L t : Nat} (h1 : L < t) (h2 : t ≤ a) :
    tailBit a L t = decide ((a - t) % 2 = 1) := by
  simp only [tailBit, show ¬ (t < L) by omega, show t ≠ a + 1 by omega,
             show ¬ (t = L ∧ L < a) by omega, ↓reduceIte]

-- General upper bound for arbitrary h and a ≥ 1

lemma phi_card_le (a : Nat) (ha : 0 < a) (h : Nat → Bool) :
    ((Finset.range (2^(a + 2))).image (phi a h)).card ≤ 2^(a + 2) - 4 := by
  by_cases ha1 : a = 1
  · subst ha1; exact phi_card_le_one h
  have ha2 : 2 ≤ a := by omega
  by_cases hha : h a = false
  · -- Case 1: h a = false, flip site a+1 only
    let g : Bool → Bool → Nat := fun b0 b1 =>
      packBits (fun t => if t = 0 then b0 else if t = 1 then b1 else decide (t = a)) (a + 2)
    let A0 : Finset Nat := fourBools.image (fun p => g p.1 p.2)
    have hg_lt : ∀ b0 b1, g b0 b1 < 2^(a + 2) := fun _ _ => packBits_lt _ _
    have hg_inj : Function.Injective (fun p : Bool × Bool => g p.1 p.2) := by
      intro ⟨a0, a1⟩ ⟨b0, b1⟩ heq
      dsimp only at heq
      have e0 : (g a0 a1).testBit 0 = (g b0 b1).testBit 0 := by rw [heq]
      have e1 : (g a0 a1).testBit 1 = (g b0 b1).testBit 1 := by rw [heq]
      rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e0
      rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e1
      simp only [↓reduceIte, show (1 : Nat) ≠ 0 by omega] at e0 e1
      exact Prod.ext e0 e1
    apply card_image_le_of_shadow (2^(a + 2)) (phi a h) A0
    · intro z hz
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_range.mpr (hg_lt p.1 p.2)
    · rw [Finset.card_image_of_injective _ hg_inj, card_fourBools]
    · intro z hz
      obtain ⟨⟨b0, b1⟩, _, rfl⟩ := Finset.mem_image.mp hz
      let z' : Nat := packBits (fun t =>
        if t = 0 then b0 else if t = 1 then b1 else decide (t = a ∨ t = a + 1)) (a + 2)
      refine ⟨z', Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (packBits_lt _ _), ?_⟩, ?_⟩
      · intro hmem
        obtain ⟨⟨c0, c1⟩, _, hc⟩ := Finset.mem_image.mp hmem
        dsimp only at hc
        have e : (g c0 c1).testBit (a + 1) = z'.testBit (a + 1) := by rw [hc]
        dsimp only [g, z'] at e
        rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e
        simp only [show a + 1 ≠ 0 by omega, show a + 1 ≠ 1 by omega, show a + 1 ≠ a by omega,
                   ↓reduceIte, decide_false, false_or, decide_true] at e
        cases e
      · have hbit_eq : ∀ t < a + 1, z'.testBit t = (g b0 b1).testBit t := by
          intro t ht
          dsimp only [g, z']
          rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)]
          simp [show t ≠ a + 1 by omega]
        have hza : (g b0 b1).testBit a = true := by
          dsimp only [g]
          rw [packBits_testBit_of_lt (by omega)]
          simp [show a ≠ 0 by omega, show a ≠ 1 by omega]
        have hz'a : z'.testBit a = true := by rw [hbit_eq a (by omega), hza]
        dsimp only [phi]
        congr 1
        · apply Finset.filter_congr
          intro j hj
          have hj' : j < a := Finset.mem_range.mp hj
          dsimp only [Fbit, polar]
          by_cases hlast : j + 1 = a
          · rw [hbit_eq j (by omega), hlast, hz'a, hza]
            simp
          · rw [hbit_eq j (by omega), hbit_eq (j + 1) (by omega), hbit_eq (j + 2) (by omega)]
        · apply Finset.filter_congr
          intro j hj
          have hj' : j < a := Finset.mem_range.mp hj
          dsimp only [FbitH, polar]
          by_cases hlast : j + 1 = a
          · rw [hbit_eq j (by omega), hlast, hz'a, hza, hha]
            simp
          · rw [hbit_eq j (by omega), hbit_eq (j + 1) (by omega), hbit_eq (j + 2) (by omega)]
  · -- Case 2: h a = true, flip run [L, R] containing a (plus site 0 to match row 0)
    have hha1 : h a = true := by
      cases hh : h a
      · exact False.elim (hha hh)
      · rfl
    let L := runStart h a
    have hLspec : 1 ≤ L ∧ L ≤ a ∧ (∀ t, L ≤ t → t ≤ a → h t = true) ∧ (1 < L → h (L - 1) = false) :=
      runStart_spec h a (by omega) hha1
    obtain ⟨hL1, hLa, hLall, hLprev⟩ := hLspec
    let R := if h (a + 1) then a + 1 else a
    have hRa : a ≤ R := by dsimp only [R]; split_ifs <;> omega
    have hRle : R ≤ a + 1 := by dsimp only [R]; split_ifs <;> omega
    have hRall : ∀ t, L ≤ t → t ≤ R → h t = true := by
      intro t ht1 ht2
      by_cases hta : t ≤ a
      · exact hLall t ht1 hta
      · have ht1' : t = a + 1 := by omega
        subst ht1'
        dsimp only [R] at ht2
        cases hha2 : h (a + 1)
        · simp [hha2] at ht2
        · rfl
    have hRnext : R = a → h (a + 1) = false := by
      intro hEq
      dsimp only [R] at hEq
      cases hha2 : h (a + 1)
      · rfl
      · simp [hha2] at hEq
    let delta : Nat → Bool := fun t => decide (L ≤ t ∧ t ≤ R)
    have hdelta_a : delta a = true := by
      simp only [delta, decide_eq_true_eq]
      exact ⟨hLa, hRa⟩
    let g : Bool → Bool → Nat := fun b0 b1 =>
      packBits (fun t => if t = 0 then b0 else if t = 1 then b1 else tailBit a L t) (a + 2)
    let A0 : Finset Nat := fourBools.image (fun p => g p.1 p.2)
    have hg_lt : ∀ b0 b1, g b0 b1 < 2^(a + 2) := fun _ _ => packBits_lt _ _
    have hg_inj : Function.Injective (fun p : Bool × Bool => g p.1 p.2) := by
      intro ⟨a0, a1⟩ ⟨b0, b1⟩ heq
      dsimp only at heq
      have e0 : (g a0 a1).testBit 0 = (g b0 b1).testBit 0 := by rw [heq]
      have e1 : (g a0 a1).testBit 1 = (g b0 b1).testBit 1 := by rw [heq]
      rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e0
      rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e1
      simp only [↓reduceIte, show (1 : Nat) ≠ 0 by omega] at e0 e1
      exact Prod.ext e0 e1
    have hga_false : ∀ b0 b1, (g b0 b1).testBit a = false := by
      intro b0 b1
      dsimp only [g]
      rw [packBits_testBit_of_lt (by omega)]
      simp only [show a ≠ 0 by omega, show a ≠ 1 by omega, ↓reduceIte]
      exact tailBit_at_a hLa
    apply card_image_le_of_shadow (2^(a + 2)) (phi a h) A0
    · intro z hz
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_range.mpr (hg_lt p.1 p.2)
    · rw [Finset.card_image_of_injective _ hg_inj, card_fourBools]
    · intro z hz
      obtain ⟨⟨b0, b1⟩, _, rfl⟩ := Finset.mem_image.mp hz
      let z0 := g b0 b1
      let d0 : Bool :=
        xor (polar (z0.testBit 1) (z0.testBit 2))
            (polar (xor (z0.testBit 1) (delta 1)) (xor (z0.testBit 2) (delta 2)))
      let z' : Nat := packBits (fun t =>
        if t = 0 then xor (z0.testBit 0) d0 else xor (z0.testBit t) (delta t)) (a + 2)
      have hz'_bit0 : z'.testBit 0 = xor (z0.testBit 0) d0 := by
        dsimp only [z']
        rw [packBits_testBit_of_lt (by omega)]; simp
      have hz'_bit : ∀ t, 1 ≤ t → t < a + 2 → z'.testBit t = xor (z0.testBit t) (delta t) := by
        intro t ht1 ht2
        dsimp only [z']
        rw [packBits_testBit_of_lt ht2]
        simp [show t ≠ 0 by omega]
      refine ⟨z', Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (packBits_lt _ _), ?_⟩, ?_⟩
      · intro hmem
        obtain ⟨⟨c0, c1⟩, _, hc⟩ := Finset.mem_image.mp hmem
        dsimp only at hc
        have e : (g c0 c1).testBit a = z'.testBit a := by rw [hc]
        rw [hga_false c0 c1, hz'_bit a (by omega) (by omega), hga_false b0 b1, hdelta_a] at e
        simp at e
      · -- Verify Fbit z' j = Fbit z0 j for all j < a
        have hF : ∀ j < a, Fbit z' j = Fbit z0 j := by
          intro j hj
          dsimp only [Fbit]
          by_cases hj0 : j = 0
          · subst hj0
            rw [hz'_bit0, hz'_bit 1 (by omega) (by omega), hz'_bit 2 (by omega) (by omega)]
            exact F_eq_of_delta _ _ _ _ rfl
          · have hj1 : 1 ≤ j := by omega
            rw [hz'_bit j hj1 (by omega), hz'_bit (j + 1) (by omega) (by omega),
                hz'_bit (j + 2) (by omega) (by omega)]
            apply F_eq_of_delta
            have ht1 : z0.testBit (j + 1) = tailBit a L (j + 1) := by
              dsimp only [z0, g]
              rw [packBits_testBit_of_lt (by omega)]
              simp only [show j + 1 ≠ 0 by omega, show j + 1 ≠ 1 by omega, ↓reduceIte]
            have ht2 : z0.testBit (j + 2) = tailBit a L (j + 2) := by
              dsimp only [z0, g]
              rw [packBits_testBit_of_lt (by omega)]
              simp only [show j + 2 ≠ 0 by omega, show j + 2 ≠ 1 by omega, ↓reduceIte]
            rw [ht1, ht2]
            -- Split on j relative to L
            by_cases hltL2 : j + 2 < L
            · have d0' : delta j = false := by simp [delta]; omega
              have d1' : delta (j + 1) = false := by simp [delta]; omega
              have d2' : delta (j + 2) = false := by simp [delta]; omega
              rw [d0', d1', d2']; simp
            · by_cases heqL2 : j + 2 = L
              · have d0' : delta j = false := by simp [delta]; omega
                have d1' : delta (j + 1) = false := by simp [delta]; omega
                have d2' : delta (j + 2) = true := by simp [delta]; omega
                have tb1 : tailBit a L (j + 1) = true := tailBit_of_lt (by omega)
                rw [d0', d1', d2', tb1]
                cases tailBit a L (j + 2) <;> decide
              · by_cases heqL1 : j + 1 = L
                · have d0' : delta j = false := by simp [delta]; omega
                  have d1' : delta (j + 1) = true := by simp [delta]; omega
                  by_cases hLlt : L < a
                  · have d2' : delta (j + 2) = true := by simp [delta]; omega
                    have tb1 : tailBit a L (j + 1) = decide ((a - (L + 1)) % 2 = 1) := by
                      rw [heqL1]; exact tailBit_at_L hLlt
                    have tb2 : tailBit a L (j + 2) = decide ((a - (L + 1)) % 2 = 1) := by
                      rw [tailBit_mid (by omega) (by omega), show a - (j + 2) = a - (L + 1) by omega]
                    rw [d0', d1', d2', tb1, tb2]
                    exact (polar_flip_same _).symm
                  · have hLeq : L = a := by omega
                    have hj1a : j + 1 = a := by omega
                    have hj2 : j + 2 = a + 1 := by omega
                    have tb1 : tailBit a L (j + 1) = false := by
                      rw [hj1a]; exact tailBit_at_a hLa
                    have tb2 : tailBit a L (j + 2) = false := by
                      rw [hj2, tailBit_last hLa, decide_eq_false (by omega)]
                    rw [d0', d1', tb1, tb2]
                    cases delta (j + 2) <;> decide
                · -- L ≤ j < a
                  have hLj : L ≤ j := by omega
                  have hLlt : L < a := by omega
                  have d0' : delta j = true := by simp [delta]; omega
                  have d1' : delta (j + 1) = true := by simp [delta]; omega
                  by_cases hlast : j + 1 = a
                  · have hj2 : j + 2 = a + 1 := by omega
                    have tb1 : tailBit a L (j + 1) = false := by
                      rw [hlast]; exact tailBit_at_a hLa
                    have tb2 : tailBit a L (j + 2) = true := by
                      rw [hj2, tailBit_last hLa, decide_eq_true hLlt]
                    rw [d0', d1', tb1, tb2]
                    cases delta (j + 2) <;> decide
                  · have d2' : delta (j + 2) = true := by simp [delta]; omega
                    have tb1 : tailBit a L (j + 1) = decide ((a - (j + 1)) % 2 = 1) :=
                      tailBit_mid (by omega) (by omega)
                    have tb2 : tailBit a L (j + 2) = decide ((a - (j + 2)) % 2 = 1) :=
                      tailBit_mid (by omega) (by omega)
                    have hdiff : decide ((a - (j + 1)) % 2 = 1) = !(decide ((a - (j + 2)) % 2 = 1)) := by
                      have : a - (j + 1) = (a - (j + 2)) + 1 := by omega
                      rw [this]
                      cases hmod : (a - (j + 2)) % 2 with
                      | zero => simp [Nat.add_mod, hmod]
                      | succ m =>
                        have hm : m = 0 := by omega
                        subst hm; simp [Nat.add_mod, hmod]
                    rw [d0', d1', d2', tb1, tb2]
                    exact (polar_flip_diff _ _ hdiff).symm
        -- Verify polar shift invariance for probe y for all j < a
        have hP : ∀ j < a,
            xor (polar (z0.testBit (j + 1)) (z0.testBit (j + 2)))
                (polar (z'.testBit (j + 1)) (z'.testBit (j + 2))) =
            xor (polar (xor (z0.testBit (j + 1)) (h (j + 1)))
                       (xor (z0.testBit (j + 2)) (h (j + 2))))
                (polar (xor (z'.testBit (j + 1)) (h (j + 1)))
                       (xor (z'.testBit (j + 2)) (h (j + 2)))) := by
          intro j hj
          rw [hz'_bit (j + 1) (by omega) (by omega), hz'_bit (j + 2) (by omega) (by omega)]
          apply polar_shift_eq
          · intro h1 _
            dsimp only [delta]
            rw [decide_eq_false_iff_not]
            intro ⟨hl, hr⟩
            have := hRall (j + 1) hl hr
            rw [this] at h1; cases h1
          · intro _ h2
            dsimp only [delta]
            rw [decide_eq_false_iff_not]
            intro ⟨hl, hr⟩
            have := hRall (j + 2) hl hr
            rw [this] at h2; cases h2
          · intro h1 h2
            dsimp only [delta]
            by_cases m1 : L ≤ j + 1 ∧ j + 1 ≤ R
            · by_cases m2 : L ≤ j + 2 ∧ j + 2 ≤ R
              · rw [decide_eq_true m1, decide_eq_true m2]
              · exfalso
                have hReq : j + 1 = R := by omega
                have hRa' : R = a := by omega
                have h2f := hRnext hRa'
                have hj2 : j + 2 = a + 1 := by omega
                rw [hj2, h2f] at h2; cases h2
            · by_cases m2 : L ≤ j + 2 ∧ j + 2 ≤ R
              · exfalso
                have hLeq : j + 2 = L := by omega
                have hLgt : 1 < L := by omega
                have h1f := hLprev hLgt
                have hj1 : L - 1 = j + 1 := by omega
                rw [hj1] at h1f
                rw [h1f] at h1; cases h1
              · rw [decide_eq_false m1, decide_eq_false m2]
        dsimp only [phi]
        congr 1
        · apply Finset.filter_congr
          intro j hj
          rw [hF j (Finset.mem_range.mp hj)]
        · apply Finset.filter_congr
          intro j hj
          have hj' := Finset.mem_range.mp hj
          have hFj := hF j hj'
          have hPj := hP j hj'
          dsimp only [Fbit] at hFj
          dsimp only [FbitH]
          rw [F_shift_eq (z0.testBit j) (z'.testBit j) (h j) _ _ _ _ hFj.symm hPj]

-- Exact count for all-ones shift h1 = fun _ => true

def altStrip (b0 b1 b2 : Bool) (t : Nat) : Bool :=
  if t = 0 then b0
  else if t = 1 then b1
  else xor b2 (decide ((t - 2) % 2 = 1))

lemma altStrip_step (b0 b1 b2 : Bool) {t : Nat} (ht : 2 ≤ t) :
    altStrip b0 b1 b2 (t + 1) = !(altStrip b0 b1 b2 t) := by
  simp only [altStrip, show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega,
             show t ≠ 0 by omega, show t ≠ 1 by omega, ↓reduceIte]
  have hsub : t + 1 - 2 = (t - 2) + 1 := by omega
  rw [hsub]
  cases hmod : (t - 2) % 2 with
  | zero => cases b2 <;> simp [Nat.add_mod, hmod]
  | succ m =>
    have hm : m = 0 := by omega
    subst hm; cases b2 <;> simp [Nat.add_mod, hmod]

lemma phi_allOnes_card (a : Nat) (ha : 0 < a) :
    ((Finset.range (2^(a + 2))).image (phi a (fun _ => true))).card = 2^(a + 2) - 4 := by
  let h1 : Nat → Bool := fun _ => true
  let g1 : Bool → Bool → Nat := fun b0 b2 => packBits (altStrip b0 false b2) (a + 2)
  let A0 : Finset Nat := fourBools.image (fun p => g1 p.1 p.2)
  have hSub : A0 ⊆ Finset.range (2^(a + 2)) := by
    intro z hz
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (packBits_lt _ _)
  have hg1_inj : Function.Injective (fun p : Bool × Bool => g1 p.1 p.2) := by
    intro ⟨a0, a2⟩ ⟨b0, b2⟩ heq
    dsimp only at heq
    have e0 : (g1 a0 a2).testBit 0 = (g1 b0 b2).testBit 0 := by rw [heq]
    have e2 : (g1 a0 a2).testBit 2 = (g1 b0 b2).testBit 2 := by rw [heq]
    rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e0
    rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)] at e2
    simp only [altStrip, ↓reduceIte, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega,
               Nat.sub_self, Nat.zero_mod, show (0 : Nat) ≠ 1 by omega, decide_false, Bool.xor_false] at e0 e2
    exact Prod.ext e0 e2
  have hCardA0 : A0.card = 4 := by
    rw [Finset.card_image_of_injective _ hg1_inj, card_fourBools]
  have hA0_bit1 : ∀ z ∈ A0, z.testBit 1 = false := by
    intro z hz
    obtain ⟨⟨b0, b2⟩, _, rfl⟩ := Finset.mem_image.mp hz
    rw [packBits_testBit_of_lt (by omega)]
    simp [altStrip]
  -- Image on Finset.range (2^(a+2)) equals image on Finset.range (2^(a+2)) \ A0
  have hImgEq : (Finset.range (2^(a + 2))).image (phi a h1) =
      (Finset.range (2^(a + 2)) \ A0).image (phi a h1) := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      by_cases hA : z ∈ A0
      · obtain ⟨⟨b0, b2⟩, _, rfl⟩ := Finset.mem_image.mp hA
        let z' : Nat := packBits (altStrip (xor b0 b2) true (!b2)) (a + 2)
        refine Finset.mem_image.mpr ⟨z', Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (packBits_lt _ _), ?_⟩, ?_⟩
        · intro hmem
          have h1f := hA0_bit1 z' hmem
          have h1t : z'.testBit 1 = true := by
            rw [packBits_testBit_of_lt (by omega)]; simp [altStrip]
          rw [h1t] at h1f; cases h1f
        · have hflip : ∀ t, 1 ≤ t → t < a + 2 → z'.testBit t = !((g1 b0 b2).testBit t) := by
            intro t ht1 ht2
            rw [packBits_testBit_of_lt ht2, packBits_testBit_of_lt ht2]
            by_cases h1eq : t = 1
            · subst h1eq; simp [altStrip]
            · simp only [altStrip, show t ≠ 0 by omega, h1eq, ↓reduceIte]
              cases b2 <;> cases decide ((t - 2) % 2 = 1) <;> rfl
          dsimp only [phi]
          congr 1
          · apply Finset.filter_congr
            intro j hj
            have hj' := Finset.mem_range.mp hj
            dsimp only [Fbit, polar]
            by_cases hj0 : j = 0
            · subst hj0
              rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega),
                  packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega),
                  packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)]
              simp only [altStrip, ↓reduceIte, show (1 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
                         show (2 : Nat) ≠ 1 by omega, Nat.sub_self, Nat.zero_mod,
                         show (0 : Nat) ≠ 1 by omega, decide_false, Bool.xor_false]
              cases b0 <;> cases b2 <;> decide
            · have hj1 : 1 ≤ j := by omega
              rw [hflip j hj1 (by omega), hflip (j + 1) (by omega) (by omega),
                  hflip (j + 2) (by omega) (by omega)]
              have halt : (g1 b0 b2).testBit (j + 2) = !((g1 b0 b2).testBit (j + 1)) := by
                rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)]
                exact altStrip_step b0 false b2 (by omega)
              rw [halt]
              cases (g1 b0 b2).testBit j <;> cases (g1 b0 b2).testBit (j + 1) <;> decide
          · apply Finset.filter_congr
            intro j hj
            have hj' := Finset.mem_range.mp hj
            dsimp only [FbitH, polar, h1]
            by_cases hj0 : j = 0
            · subst hj0
              rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega),
                  packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega),
                  packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)]
              simp only [altStrip, ↓reduceIte, show (1 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
                         show (2 : Nat) ≠ 1 by omega, Nat.sub_self, Nat.zero_mod,
                         show (0 : Nat) ≠ 1 by omega, decide_false, Bool.xor_false]
              cases b0 <;> cases b2 <;> decide
            · have hj1 : 1 ≤ j := by omega
              rw [hflip j hj1 (by omega), hflip (j + 1) (by omega) (by omega),
                  hflip (j + 2) (by omega) (by omega)]
              have halt : (g1 b0 b2).testBit (j + 2) = !((g1 b0 b2).testBit (j + 1)) := by
                rw [packBits_testBit_of_lt (by omega), packBits_testBit_of_lt (by omega)]
                exact altStrip_step b0 false b2 (by omega)
              rw [halt]
              cases (g1 b0 b2).testBit j <;> cases (g1 b0 b2).testBit (j + 1) <;> decide
      · exact Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hA⟩, rfl⟩
    · exact Finset.image_subset_image Finset.sdiff_subset
  -- phi a h1 is injective on Finset.range (2^(a+2)) \ A0
  have hInj : Set.InjOn (phi a h1) ↑(Finset.range (2^(a + 2)) \ A0) := by
    intro z hz z' hz' heq
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_range] at hz hz'
    have hF : ∀ j < a, Fbit z j = Fbit z' j := by
      intro j hj
      have h1e := congrArg Prod.fst heq
      have hm : j ∈ (phi a h1 z).1 ↔ j ∈ (phi a h1 z').1 := by rw [h1e]
      simp only [phi, Finset.mem_filter, Finset.mem_range, hj, true_and] at hm
      exact Bool.eq_iff_iff.mpr hm
    have hFH : ∀ j < a, FbitH h1 z j = FbitH h1 z' j := by
      intro j hj
      have h2e := congrArg Prod.snd heq
      have hm : j ∈ (phi a h1 z).2 ↔ j ∈ (phi a h1 z').2 := by rw [h2e]
      simp only [phi, Finset.mem_filter, Finset.mem_range, hj, true_and] at hm
      exact Bool.eq_iff_iff.mpr hm
    have hstep : ∀ j < a, xor (z.testBit (j + 1)) (z'.testBit (j + 1)) =
        xor (z.testBit (j + 2)) (z'.testBit (j + 2)) :=
      fun j hj => allOnes_xor_eq _ _ _ _ _ _ (hF j hj) (hFH j hj)
    have hconst : ∀ t, 1 ≤ t → t < a + 2 →
        xor (z.testBit t) (z'.testBit t) = xor (z.testBit 1) (z'.testBit 1) := by
      intro t ht1 ht2
      induction t with
      | zero => omega
      | succ m ih =>
        by_cases hm : m = 0
        · subst hm; rfl
        · have hs := hstep (m - 1) (by omega)
          rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega] at hs
          rw [← hs]
          exact ih (by omega) (by omega)
    cases h1b : xor (z.testBit 1) (z'.testBit 1)
    · -- Same tail: z = z'
      have htail : ∀ t, 1 ≤ t → t < a + 2 → z.testBit t = z'.testBit t := by
        intro t ht1 ht2
        have hc := hconst t ht1 ht2
        rw [h1b] at hc
        cases hzt : z.testBit t <;> cases hz't : z'.testBit t <;> simp [hzt, hz't] at hc ⊢
      have h0 : z.testBit 0 = z'.testBit 0 := by
        have hf0 := hF 0 ha
        dsimp only [Fbit] at hf0
        rw [htail 1 (by omega) (by omega), htail 2 (by omega) (by omega)] at hf0
        exact allOnes_same_zero _ _ _ _ hf0
      apply eq_of_testBit_lt hz.1 hz'.1
      intro t ht
      by_cases ht0 : t = 0
      · subst ht0; exact h0
      · exact htail t (by omega) ht
    · -- Flipped tail: one of z, z' lies in A0, contradiction
      have hflip : ∀ t, 1 ≤ t → t < a + 2 → z'.testBit t = !(z.testBit t) := by
        intro t ht1 ht2
        have hc := hconst t ht1 ht2
        rw [h1b] at hc
        cases hzt : z.testBit t <;> cases hz't : z'.testBit t <;> simp [hzt, hz't] at hc ⊢
      have halt_z : ∀ t, 2 ≤ t → t + 1 < a + 2 → z.testBit (t + 1) = !(z.testBit t) := by
        intro t ht2 htlt
        have hfj := hF (t - 1) (by omega)
        dsimp only [Fbit] at hfj
        have e1 : t - 1 + 1 = t := by omega
        have e2 : t - 1 + 2 = t + 1 := by omega
        rw [e1, e2, hflip (t - 1) (by omega) (by omega), hflip t (by omega) (by omega),
            hflip (t + 1) (by omega) htlt] at hfj
        exact allOnes_alt_step _ _ _ hfj
      have hform : ∀ w < 2^(a + 2),
          (∀ t, 2 ≤ t → t + 1 < a + 2 → w.testBit (t + 1) = !(w.testBit t)) →
          w.testBit 1 = false → w ∈ A0 := by
        intro w hw halt hw1
        have hbits : ∀ t < a + 2, w.testBit t = altStrip (w.testBit 0) false (w.testBit 2) t := by
          intro t ht
          by_cases ht0 : t = 0
          · subst ht0; simp [altStrip]
          · by_cases ht1 : t = 1
            · subst ht1; simp [altStrip, hw1]
            · induction t with
              | zero => omega
              | succ m ih =>
                by_cases hm : m = 1
                · subst hm
                  simp [altStrip]
                · rw [halt m (by omega) ht, ih (by omega) (by omega) (by omega),
                      altStrip_step _ _ _ (by omega)]
        have heqw : w = g1 (w.testBit 0) (w.testBit 2) := by
          apply eq_of_testBit_lt hw (packBits_lt _ _)
          intro t ht
          rw [packBits_testBit_of_lt ht]
          exact hbits t ht
        rw [heqw]
        refine Finset.mem_image.mpr ⟨(w.testBit 0, w.testBit 2), ?_, rfl⟩
        cases w.testBit 0 <;> cases w.testBit 2 <;> simp [fourBools]
      cases hz1 : z.testBit 1
      · exact False.elim (hz.2 (hform z hz.1 halt_z hz1))
      · have hz'1 : z'.testBit 1 = false := by rw [hflip 1 (by omega) (by omega), hz1]; rfl
        have halt_z' : ∀ t, 2 ≤ t → t + 1 < a + 2 → z'.testBit (t + 1) = !(z'.testBit t) := by
          intro t ht2 htlt
          rw [hflip (t + 1) (by omega) htlt, hflip t (by omega) (by omega), halt_z t ht2 htlt]
        exact False.elim (hz'.2 (hform z' hz'.1 halt_z' hz'1))
  rw [hImgEq, Finset.card_image_of_injOn hInj, card_sdiff_eq hSub, Finset.card_range, hCardA0]

lemma main_33620 :
    ∀ (k d a start init last c : Nat), 0 < d → 0 < a → a + 2 + 2 * d ≤ k →
  let words := Finset.range (2^k)
  let rot' := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix' := fun z : Nat => z ^^^ rot' d z ^^^ rot' (k - d) z
  let site' := fun j : Nat => (start + j) % k
  let label' := fun (u x j : Nat) =>
    let y := mix' (rot' init x ^^^ u)
    xor (xor (y.testBit (site' j))
      (!(y.testBit (site' (j + 1))) && y.testBit (site' (j + 2))))
      (xor ((rot' last x).testBit (site' j)) (c.testBit (site' j)))
  let response := fun (u x : Nat) => (Finset.range a).filter (fun j => label' u x j)
  let count := fun (x y : Nat) =>
    (words.image (fun u => (response u x, response u y))).card
  (∀ x ∈ words, ∀ y ∈ words, count x y ≤ 2^(a + 2) - 4) ∧
  ∃ y ∈ words, count 0 y = 2^(a + 2) - 4 := by
  intro k d a start init last c hd ha hk words rot' mix' site' label' response count
  have hcount : ∀ x ∈ words, ∀ y ∈ words,
      count x y = ((Finset.range (2^(a + 2))).image
        (phi a (fun t => xor ((mix k d (rot k init x)).testBit (site k start t))
                             ((mix k d (rot k init y)).testBit (site k start t))))).card := by
    intro x _ y _
    exact count_eq_phi_card hd hk
  constructor
  · intro x hx y hy
    rw [hcount x hx y hy]
    exact phi_card_le a ha _
  · obtain ⟨y, hy, hy1⟩ := exists_all_ones_y (k := k) (d := d) (a := a) (start := start) (init := init) hd hk
    refine ⟨y, hy, ?_⟩
    have h0mem : 0 ∈ words := Finset.mem_range.mpr (by positivity)
    rw [hcount 0 h0mem y hy]
    have h0rot : rot k init 0 = 0 := by simp [rot]
    have h0mix : mix k d 0 = 0 := by simp [mix, rot]
    have hphi_eq : ∀ z ∈ Finset.range (2^(a + 2)),
        phi a (fun t => xor ((mix k d (rot k init 0)).testBit (site k start t))
                            ((mix k d (rot k init y)).testBit (site k start t))) z =
        phi a (fun _ => true) z := by
      intro z _
      dsimp only [phi]
      congr 1
      apply Finset.filter_congr
      intro j hj
      have hj' := Finset.mem_range.mp hj
      dsimp only [FbitH]
      rw [h0rot, h0mix, Nat.zero_testBit, Nat.zero_testBit, Nat.zero_testBit,
          hy1 j (by omega), hy1 (j + 1) (by omega), hy1 (j + 2) (by omega)]
      simp
    have himg : (Finset.range (2^(a + 2))).image
        (phi a (fun t => xor ((mix k d (rot k init 0)).testBit (site k start t))
                             ((mix k d (rot k init y)).testBit (site k start t)))) =
        (Finset.range (2^(a + 2))).image (phi a (fun _ => true)) := by
      ext p
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, (hphi_eq z hz).symm⟩
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, hphi_eq z hz⟩
    rw [himg]
    exact phi_allOnes_card a ha

end PEqualNP.Outside.L_meta_33620_aux

theorem PEqualNP.Outside.L_meta_33620 :
    ∀ (k d a start init last c : Nat), 0 < d → 0 < a → a + 2 + 2*d ≤ k →
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let site := fun j : Nat => (start+j) % k
  let label := fun (u x j : Nat) =>
    let y := mix (rot init x ^^^ u)
    xor (xor (y.testBit (site j))
      (!(y.testBit (site (j+1))) && y.testBit (site (j+2))))
      (xor ((rot last x).testBit (site j)) (c.testBit (site j)))
  let response := fun (u x : Nat) => (Finset.range a).filter (fun j => label u x j)
  let count := fun (x y : Nat) =>
    (words.image (fun u => (response u x, response u y))).card
  (∀ x ∈ words, ∀ y ∈ words, count x y ≤ 2^(a+2) - 4) ∧
  ∃ y ∈ words, count 0 y = 2^(a+2) - 4 :=
  PEqualNP.Outside.L_meta_33620_aux.main_33620
