import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1433

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def pivot (s j : ℕ) : ℕ := (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j

def path (h s : ℕ) (v : Bool) : Finset ℕ :=
  ((Finset.range h).filter (fun j => decide (s / 2 ^ j % 2 = 1) = v)).image (pivot s)

def cell (h : ℕ) (s : Fin (2 ^ h)) (Y : Finset ℕ) : Prop :=
  path h s.val true ⊆ Y ∧ Disjoint (path h s.val false) Y

lemma pivot_inj (s : ℕ) : Function.Injective (pivot s) := by
  intro j1 j2 h
  unfold pivot at h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hdiv : 2 ^ j1 ∣ (2 * (s / 2 ^ (j2 + 1)) + 1) * 2 ^ j2 := by
      have : 2 ^ j1 ∣ 2 ^ j2 := Nat.pow_dvd_pow 2 (Nat.le_of_lt hlt)
      exact dvd_mul_of_dvd_right this _
    have h1 : 2 * (s / 2 ^ (j1 + 1)) + 1 = (2 * (s / 2 ^ (j2 + 1)) + 1) * 2 ^ (j2 - j1) := by
      have hpow : 2 ^ j2 = 2 ^ (j2 - j1) * 2 ^ j1 := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      rw [hpow, ← Nat.mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 2)) h
    have heven : 2 ∣ (2 * (s / 2 ^ (j2 + 1)) + 1) * 2 ^ (j2 - j1) := by
      apply dvd_mul_of_dvd_right
      exact dvd_pow_self 2 (by omega)
    rw [← h1] at heven
    omega
  · have h1 : 2 * (s / 2 ^ (j2 + 1)) + 1 = (2 * (s / 2 ^ (j1 + 1)) + 1) * 2 ^ (j1 - j2) := by
      have hpow : 2 ^ j1 = 2 ^ (j1 - j2) * 2 ^ j2 := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
      rw [hpow, ← Nat.mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 2)) h.symm
    have heven : 2 ∣ (2 * (s / 2 ^ (j1 + 1)) + 1) * 2 ^ (j1 - j2) := by
      apply dvd_mul_of_dvd_right
      exact dvd_pow_self 2 (by omega)
    rw [← h1] at heven
    omega

lemma pivot_pos (s j : ℕ) : 1 ≤ pivot s j := by
  unfold pivot
  have h2 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
  have h1 : 1 ≤ 2 * (s / 2 ^ (j + 1)) + 1 := by omega
  nlinarith

lemma pivot_lt {h s j : ℕ} (hs : s < 2 ^ h) (hj : j < h) : pivot s j < 2 ^ h := by
  unfold pivot
  have hpow : 2 ^ h = 2 ^ (h - (j + 1)) * 2 ^ (j + 1) := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hdiv : s / 2 ^ (j + 1) < 2 ^ (h - (j + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]
    rw [← hpow]
    exact hs
  have h1 : 2 * (s / 2 ^ (j + 1)) + 1 < 2 * 2 ^ (h - (j + 1)) := by omega
  have h2 : (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j < (2 * 2 ^ (h - (j + 1))) * 2 ^ j :=
    Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by decide : 0 < 2))
  have h3 : (2 * 2 ^ (h - (j + 1))) * 2 ^ j = 2 ^ h := by
    calc (2 * 2 ^ (h - (j + 1))) * 2 ^ j
        = 2 ^ (h - (j + 1)) * (2 ^ j * 2) := by ring
      _ = 2 ^ (h - (j + 1)) * 2 ^ (j + 1) := by rw [← Nat.pow_succ]
      _ = 2 ^ h := hpow.symm
  rw [h3] at h2
  exact h2

lemma nat_bit_decomp (s j : ℕ) :
    s = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + (s / 2 ^ j % 2) * 2 ^ j + s % 2 ^ j := by
  have h1 := (Nat.div_add_mod s (2 ^ j)).symm
  have h2 := (Nat.div_add_mod (s / 2 ^ j) 2).symm
  have h3 : (s / 2 ^ j) / 2 = s / 2 ^ (j + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  rw [h3] at h2
  have h4 : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
  calc s = 2 ^ j * (s / 2 ^ j) + s % 2 ^ j := h1
    _ = 2 ^ j * (2 * (s / 2 ^ (j + 1)) + s / 2 ^ j % 2) + s % 2 ^ j := by nth_rw 1 [h2]
    _ = (s / 2 ^ (j + 1)) * (2 ^ j * 2) + (s / 2 ^ j % 2) * 2 ^ j + s % 2 ^ j := by ring
    _ = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + (s / 2 ^ j % 2) * 2 ^ j + s % 2 ^ j := by rw [← h4]

lemma pivot_le_of_bit1 {s j : ℕ} (hb : s / 2 ^ j % 2 = 1) : pivot s j ≤ s := by
  have hd := nat_bit_decomp s j
  rw [hb] at hd
  unfold pivot
  have h4 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
  have : (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + 1 * 2 ^ j := by
    rw [h4]; ring
  omega

lemma lt_pivot_of_bit0 {s j : ℕ} (hb : s / 2 ^ j % 2 = 0) : s < pivot s j := by
  have hd := nat_bit_decomp s j
  rw [hb] at hd
  have hmod : s % 2 ^ j < 2 ^ j := Nat.mod_lt s (Nat.pow_pos (by decide : 0 < 2))
  unfold pivot
  have h4 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
  have : (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j = (s / 2 ^ (j + 1)) * 2 ^ (j + 1) + 2 ^ j := by
    rw [h4]; ring
  omega

lemma part1 (h : ℕ) (s : Fin (2 ^ h)) :
    (path h s.val true ∪ path h s.val false).card = h ∧ cell h s (Finset.Icc 1 s.val) := by
  constructor
  · have hunion : path h s.val true ∪ path h s.val false = (Finset.range h).image (pivot s.val) := by
      unfold path
      rw [← Finset.image_union]
      congr 1
      ext j
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
      · intro hj
        cases hdec : decide (s.val / 2 ^ j % 2 = 1)
        · exact Or.inr ⟨hj, rfl⟩
        · exact Or.inl ⟨hj, rfl⟩
    rw [hunion, Finset.card_image_of_injective _ (pivot_inj s.val), Finset.card_range]
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨_, hb⟩, rfl⟩ := hp
      exact Finset.mem_Icc.mpr ⟨pivot_pos s.val j, pivot_le_of_bit1 hb⟩
    · rw [Finset.disjoint_left]
      intro p hp hmem
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨_, hb⟩, rfl⟩ := hp
      have hb0 : s.val / 2 ^ j % 2 = 0 := by omega
      have hlt := lt_pivot_of_bit0 hb0
      have hle := (Finset.mem_Icc.mp hmem).2
      omega

lemma exists_highest_diff : ∀ (h s t : ℕ), s < 2 ^ h → t < 2 ^ h → t < s →
    ∃ j < h, s / 2 ^ (j + 1) = t / 2 ^ (j + 1) ∧ s / 2 ^ j % 2 = 1 ∧ t / 2 ^ j % 2 = 0 := by
  intro h
  induction h with
  | zero => intro s t hs ht hlt; omega
  | succ k ih =>
    intro s t hs ht hlt
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hs1 : s / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt hs
    have ht1 : t / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt ht
    by_cases hsk : s / 2 ^ k = t / 2 ^ k
    · have hs' : s % 2 ^ k < 2 ^ k := Nat.mod_lt s (Nat.pow_pos (by decide : 0 < 2))
      have ht' : t % 2 ^ k < 2 ^ k := Nat.mod_lt t (Nat.pow_pos (by decide : 0 < 2))
      have hlt' : t % 2 ^ k < s % 2 ^ k := by
        have h1 := Nat.div_add_mod s (2 ^ k)
        have h2 := Nat.div_add_mod t (2 ^ k)
        rw [hsk] at h1
        omega
      obtain ⟨j, hj, hdiv, hsb, htb⟩ := ih (s % 2 ^ k) (t % 2 ^ k) hs' ht' hlt'
      refine ⟨j, by omega, ?_, ?_, ?_⟩
      · have hpow2 : 2 ^ k = 2 ^ (j + 1) * 2 ^ (k - (j + 1)) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
        have h1 : s = 2 ^ (j + 1) * (s / 2 ^ k * 2 ^ (k - (j + 1))) + s % 2 ^ k := by
          calc s = 2 ^ k * (s / 2 ^ k) + s % 2 ^ k := (Nat.div_add_mod s (2 ^ k)).symm
            _ = 2 ^ (j + 1) * (s / 2 ^ k * 2 ^ (k - (j + 1))) + s % 2 ^ k := by rw [hpow2]; ring
        have h2 : t = 2 ^ (j + 1) * (t / 2 ^ k * 2 ^ (k - (j + 1))) + t % 2 ^ k := by
          calc t = 2 ^ k * (t / 2 ^ k) + t % 2 ^ k := (Nat.div_add_mod t (2 ^ k)).symm
            _ = 2 ^ (j + 1) * (t / 2 ^ k * 2 ^ (k - (j + 1))) + t % 2 ^ k := by rw [hpow2]; ring
        rw [h1, h2, hsk,
            Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)),
            Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), hdiv]
      · have hpow2 : 2 ^ k = 2 ^ j * (2 * 2 ^ (k - j - 1)) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]
          congr 1; omega
        have h1 : s = 2 ^ j * (2 * (s / 2 ^ k * 2 ^ (k - j - 1))) + s % 2 ^ k := by
          calc s = 2 ^ k * (s / 2 ^ k) + s % 2 ^ k := (Nat.div_add_mod s (2 ^ k)).symm
            _ = 2 ^ j * (2 * (s / 2 ^ k * 2 ^ (k - j - 1))) + s % 2 ^ k := by rw [hpow2]; ring
        rw [h1, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), Nat.mul_add_mod, hsb]
      · have hpow2 : 2 ^ k = 2 ^ j * (2 * 2 ^ (k - j - 1)) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]
          congr 1; omega
        have h2 : t = 2 ^ j * (2 * (t / 2 ^ k * 2 ^ (k - j - 1))) + t % 2 ^ k := by
          calc t = 2 ^ k * (t / 2 ^ k) + t % 2 ^ k := (Nat.div_add_mod t (2 ^ k)).symm
            _ = 2 ^ j * (2 * (t / 2 ^ k * 2 ^ (k - j - 1))) + t % 2 ^ k := by rw [hpow2]; ring
        rw [h2, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), Nat.mul_add_mod, htb]
    · have hsle : s / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]; omega
      have htle : t / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))]; omega
      have hle : t / 2 ^ k ≤ s / 2 ^ k := Nat.div_le_div_right (Nat.le_of_lt hlt)
      have hsbit : s / 2 ^ k = 1 := by
        generalize ha : s / 2 ^ k = a at hsle hle hsk
        generalize hb : t / 2 ^ k = b at htle hle hsk
        omega
      have htbit : t / 2 ^ k = 0 := by
        generalize ha : s / 2 ^ k = a at hsle hle hsk
        generalize hb : t / 2 ^ k = b at htle hle hsk
        omega
      exact ⟨k, by omega, by rw [hs1, ht1], by simp [hsbit], by simp [htbit]⟩

lemma part3 (h : ℕ) (X Y : Finset ℕ) (s t : Fin (2 ^ h))
    (hXY : X ⊆ Y) (hs : cell h s X) (ht : cell h t Y) : s ≤ t := by
  by_contra hgt
  have hlt : t.val < s.val := Nat.lt_of_not_ge hgt
  obtain ⟨j, hj, hdiv, hsb, htb⟩ := exists_highest_diff h s.val t.val s.isLt t.isLt hlt
  have hp : pivot s.val j = pivot t.val j := by unfold pivot; rw [hdiv]
  have hinX : pivot s.val j ∈ X := hs.1 (by
    simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨j, ⟨hj, by simp [hsb]⟩, rfl⟩)
  have hinY : pivot t.val j ∈ Y := hp ▸ hXY hinX
  have hnotY : pivot t.val j ∉ Y := Finset.disjoint_left.mp ht.2 (by
    simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨j, ⟨hj, by simp [htb]⟩, rfl⟩)
  exact hnotY hinY

def findIdx : ℕ → ℕ → Finset ℕ → ℕ
  | 0, base, _ => base
  | k + 1, base, Y =>
    if (base + 2 ^ k) ∈ Y then findIdx k (base + 2 ^ k) Y else findIdx k base Y

lemma findIdx_spec (Y : Finset ℕ) : ∀ (k q : ℕ),
    q * 2 ^ k ≤ findIdx k (q * 2 ^ k) Y ∧
    findIdx k (q * 2 ^ k) Y < (q + 1) * 2 ^ k ∧
    ∀ j < k, (findIdx k (q * 2 ^ k) Y / 2 ^ j % 2 = 1 ↔ pivot (findIdx k (q * 2 ^ k) Y) j ∈ Y) := by
  intro k
  induction k with
  | zero =>
    intro q
    simp only [findIdx, Nat.pow_zero, Nat.mul_one]
    exact ⟨le_rfl, by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro q
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hq0 : q * 2 ^ (k + 1) = (2 * q) * 2 ^ k := by rw [hpow]; ring
    have hq1 : q * 2 ^ (k + 1) + 2 ^ k = (2 * q + 1) * 2 ^ k := by rw [hpow]; ring
    unfold findIdx
    by_cases hin : q * 2 ^ (k + 1) + 2 ^ k ∈ Y
    · simp only [hin, ite_true]
      rw [hq1]
      obtain ⟨hlo, hhi, hbits⟩ := ih (2 * q + 1)
      set r := findIdx k ((2 * q + 1) * 2 ^ k) Y
      have hdivk1 : r / 2 ^ (k + 1) = q := by
        have hp : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by rw [hpow]; nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [hpow]; nlinarith)
      have hdivk : r / 2 ^ k = 2 * q + 1 := by
        have hp : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr hlo
      refine ⟨by rw [hpow]; nlinarith, by rw [hpow]; nlinarith, fun j hj => ?_⟩
      by_cases hjk : j < k
      · exact hbits j hjk
      · have heq : j = k := by omega
        subst j
        have hpiv : pivot r k = q * 2 ^ (k + 1) + 2 ^ k := by
          unfold pivot; rw [hdivk1, hq1]
        rw [hdivk, hpiv]
        simp [hin]
    · simp only [hin, ite_false]
      rw [hq0]
      obtain ⟨hlo, hhi, hbits⟩ := ih (2 * q)
      set r := findIdx k ((2 * q) * 2 ^ k) Y
      have hdivk1 : r / 2 ^ (k + 1) = q := by
        have hp : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by rw [hpow]; nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [hpow]; nlinarith)
      have hdivk : r / 2 ^ k = 2 * q := by
        have hp : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith))
        · exact (Nat.le_div_iff_mul_le hp).mpr hlo
      refine ⟨hlo, by rw [hpow]; nlinarith, fun j hj => ?_⟩
      by_cases hjk : j < k
      · exact hbits j hjk
      · have heq : j = k := by omega
        subst j
        have hpiv : pivot r k = q * 2 ^ (k + 1) + 2 ^ k := by
          unfold pivot; rw [hdivk1, hq1]
        rw [hdivk, hpiv]
        simp [hin]

lemma part2 (h : ℕ) (Y : Finset ℕ) : ∃! s : Fin (2 ^ h), cell h s Y := by
  have hspec := findIdx_spec Y h 0
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul] at hspec
  obtain ⟨_, hlt, hbits⟩ := hspec
  let s : Fin (2 ^ h) := ⟨findIdx h 0 Y, hlt⟩
  refine ⟨s, ?_, fun t ht => le_antisymm (part3 h Y Y t s (Finset.Subset.refl _) ht ?_)
    (part3 h Y Y s t (Finset.Subset.refl _) ?_ ht)⟩
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact (hbits j hj).mp hb
    · rw [Finset.disjoint_left]
      intro p hp hin
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact hb ((hbits j hj).mpr hin)
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact (hbits j hj).mp hb
    · rw [Finset.disjoint_left]
      intro p hp hin
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact hb ((hbits j hj).mpr hin)
  · constructor
    · intro p hp
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact (hbits j hj).mp hb
    · rw [Finset.disjoint_left]
      intro p hp hin
      simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not] at hp
      obtain ⟨j, ⟨hj, hb⟩, rfl⟩ := hp
      exact hb ((hbits j hj).mpr hin)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma runW_nil (w : List Bool) : runW [] w = w := rfl

lemma runW_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runW (g :: gs) w = runW gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma runW_append (gs hs : List Gate) (w : List Bool) :
    runW (gs ++ hs) w = runW hs (runW gs w) := by
  simp [runW, List.foldl_append]

lemma runW_len (gs : List Gate) : ∀ w : List Bool, (runW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [runW]
  | cons g gs ih => intro w; rw [runW_cons, ih]; simp; omega

lemma runW_old (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (runW gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [runW_cons, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma eval_eq_runW (C : Circuit) (w : List Bool) :
    C.eval w = (runW C.gates w).getD C.output false := rfl

def notCnt (gs : List Gate) : ℕ :=
  notCount ⟨gs, 0⟩

lemma notCnt_append (gs hs : List Gate) : notCnt (gs ++ hs) = notCnt gs + notCnt hs := by
  simp [notCnt, notCount, List.filter_append]

lemma notCnt_of_no_not (gs : List Gate) (h : ∀ g ∈ gs, g.op ≠ GateOp.not) : notCnt gs = 0 := by
  unfold notCnt notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp [h g hg]

def validGs (base : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < base + j)

lemma validGs_nil (base : ℕ) : validGs base [] :=
  ⟨fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (Nat.not_lt_zero _)⟩

lemma validGs_append {base : ℕ} {gs hs : List Gate}
    (h1 : validGs base gs) (h2 : validGs (base + gs.length) hs) : validGs base (gs ++ hs) := by
  refine ⟨fun g hg => ?_, fun j hj i hi => ?_⟩
  · rcases List.mem_append.mp hg with hg | hg
    · exact h1.1 g hg
    · exact h2.1 g hg
  · by_cases hlt : j < gs.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      exact h1.2 j hlt i hi
    · have hge : gs.length ≤ j := Nat.le_of_not_gt hlt
      rw [List.getD_append_right _ _ _ _ hge] at hi
      have hlt2 : j - gs.length < hs.length := by simp at hj; omega
      have := h2.2 (j - gs.length) hlt2 i hi
      omega

def orChain (acc base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: ws =>
    let p := orChain base (base + 1) ws
    (⟨.or, [acc, w]⟩ :: p.1, p.2)

lemma orChain_len (ws : List ℕ) : ∀ acc base, (orChain acc base ws).1.length = ws.length := by
  induction ws with
  | nil => intro _ _; rfl
  | cons w ws ih => intro acc base; simp [orChain, ih]

lemma orChain_out (ws : List ℕ) : ∀ acc base, acc < base →
    (orChain acc base ws).2 < base + ws.length := by
  induction ws with
  | nil => intro acc base h; simpa [orChain] using h
  | cons w ws ih =>
    intro acc base h
    have := ih base (base + 1) (by omega)
    simp only [orChain, List.length_cons]
    omega

lemma orChain_notCnt (ws : List ℕ) : ∀ acc base, notCnt (orChain acc base ws).1 = 0 := by
  induction ws with
  | nil => intro _ _; rfl
  | cons w ws ih =>
    intro acc base
    have h1 : (orChain acc base (w :: ws)).1 = [⟨.or, [acc, w]⟩] ++ (orChain base (base + 1) ws).1 := rfl
    rw [h1, notCnt_append, ih base (base + 1), Nat.add_zero]
    exact notCnt_of_no_not _ (fun g hg => by simp at hg; subst hg; simp)

lemma orChain_valid (ws : List ℕ) : ∀ acc base, acc < base → (∀ w ∈ ws, w < base) →
    validGs base (orChain acc base ws).1 := by
  induction ws with
  | nil => intro _ _ _ _; exact validGs_nil _
  | cons w ws ih =>
    intro acc base hacc hws
    have hw0 : w < base := hws w List.mem_cons_self
    have hrest := ih base (base + 1) (by omega) (fun x hx => by have := hws x (List.mem_cons_of_mem _ hx); omega)
    have h1 : validGs base [⟨.or, [acc, w]⟩] := by
      refine ⟨fun g hg => by simp at hg; subst hg; simp, fun j hj i hi => ?_⟩
      simp at hj; subst hj
      simp only [List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    exact validGs_append h1 hrest

lemma orChain_eval (ws : List ℕ) : ∀ (acc : ℕ) (init : List Bool),
    acc < init.length → (∀ w ∈ ws, w < init.length) →
    (runW (orChain acc init.length ws).1 init).getD (orChain acc init.length ws).2 false =
      (init.getD acc false || ws.any (fun w => init.getD w false)) := by
  induction ws with
  | nil =>
    intro acc init _ _
    simp [orChain, runW]
  | cons w ws ih =>
    intro acc init hacc hws
    have hw0 : w < init.length := hws w List.mem_cons_self
    let init1 := init ++ [GateOp.or.eval ([acc, w].map fun i => init.getD i false)]
    have hlen1 : init1.length = init.length + 1 := by simp [init1]
    simp only [orChain, runW_cons]
    change (runW (orChain init.length (init.length + 1) ws).1 init1).getD
      (orChain init.length (init.length + 1) ws).2 false = _
    rw [← hlen1, ih init.length init1 (by omega) (fun x hx => by have := hws x (List.mem_cons_of_mem _ hx); omega)]
    have hlast : init1.getD init.length false = (init.getD acc false || init.getD w false) := by
      simp [init1, GateOp.eval]
    have hany : ws.any (fun x => init1.getD x false) = ws.any (fun x => init.getD x false) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      exact exists_congr fun x => and_congr_right fun hx => by
        rw [List.getD_append _ _ _ _ (hws x (List.mem_cons_of_mem _ hx))]
    rw [hlast, hany]
    simp [Bool.or_assoc]

def orList (base zeroWire : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], zeroWire)
  | w :: ws => orChain w base ws

lemma orList_len_le (base zeroWire : ℕ) (ws : List ℕ) :
    (orList base zeroWire ws).1.length ≤ ws.length := by
  cases ws with
  | nil => simp [orList]
  | cons w ws => simp [orList, orChain_len]

lemma orList_out (base zeroWire : ℕ) (ws : List ℕ) (hz : zeroWire < base) (hws : ∀ w ∈ ws, w < base) :
    (orList base zeroWire ws).2 < base + (orList base zeroWire ws).1.length := by
  cases ws with
  | nil => simpa [orList] using hz
  | cons w ws =>
    simp only [orList, orChain_len]
    exact orChain_out ws w base (hws w List.mem_cons_self)

lemma orList_notCnt (base zeroWire : ℕ) (ws : List ℕ) : notCnt (orList base zeroWire ws).1 = 0 := by
  cases ws with
  | nil => rfl
  | cons w ws => exact orChain_notCnt ws w base

lemma orList_valid (base zeroWire : ℕ) (ws : List ℕ) (hws : ∀ w ∈ ws, w < base) :
    validGs base (orList base zeroWire ws).1 := by
  cases ws with
  | nil => exact validGs_nil _
  | cons w ws =>
    exact orChain_valid ws w base (hws w List.mem_cons_self) (fun x hx => hws x (List.mem_cons_of_mem _ hx))

lemma orList_eval (zeroWire : ℕ) (ws : List ℕ) (init : List Bool)
    (hz : init.getD zeroWire false = false) (hws : ∀ w ∈ ws, w < init.length) :
    (runW (orList init.length zeroWire ws).1 init).getD (orList init.length zeroWire ws).2 false =
      ws.any (fun w => init.getD w false) := by
  cases ws with
  | nil => simpa [orList, runW] using hz
  | cons w ws =>
    simp only [orList, List.any_cons]
    exact orChain_eval ws w init (hws w List.mem_cons_self) (fun x hx => hws x (List.mem_cons_of_mem _ hx))

def andPivotGs (k : ℕ) (flags : List ℕ) : List Gate :=
  flags.mapIdx (fun q w => ⟨.and, [w, (2 * q + 1) * 2 ^ k]⟩)

lemma andPivotGs_len (k : ℕ) (flags : List ℕ) : (andPivotGs k flags).length = flags.length := by
  simp [andPivotGs]

lemma andPivotGs_notCnt (k : ℕ) (flags : List ℕ) : notCnt (andPivotGs k flags) = 0 := by
  apply notCnt_of_no_not
  intro g hg
  simp only [andPivotGs, List.mem_iff_getElem, List.length_mapIdx, List.getElem_mapIdx] at hg
  obtain ⟨i, _, rfl⟩ := hg
  simp

lemma andPivotGs_valid (h k base : ℕ) (flags : List ℕ) (hM : 2 ^ h ≤ base)
    (hfl : ∀ w ∈ flags, w < base) (hflLen : flags.length * 2 ^ (k + 1) ≤ 2 ^ h) :
    validGs base (andPivotGs k flags) := by
  refine ⟨fun g hg => ?_, fun j hj i hi => ?_⟩
  · simp only [andPivotGs, List.mem_iff_getElem, List.length_mapIdx, List.getElem_mapIdx] at hg
    obtain ⟨_, _, rfl⟩ := hg; simp
  · rw [andPivotGs_len] at hj
    have hget : (andPivotGs k flags).getD j ⟨GateOp.or, []⟩ =
        ⟨.and, [flags[j], (2 * j + 1) * 2 ^ k]⟩ := by
      simp [andPivotGs, List.getD_eq_getElem?_getD, hj]
    rw [hget] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := hfl flags[j] (List.getElem_mem hj); omega
    · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have h1 : (2 * j + 1) * 2 ^ k < (j + 1) * 2 ^ (k + 1) := by rw [hpow]; nlinarith [Nat.pow_pos (a := 2) (n := k) (by decide)]
      have h2 : (j + 1) * 2 ^ (k + 1) ≤ flags.length * 2 ^ (k + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega

lemma andPivotGs_eval_aux (k : ℕ) : ∀ (off : ℕ) (flags : List ℕ) (init : List Bool),
    (∀ w ∈ flags, w < init.length) →
    (∀ q < flags.length, (2 * (off + q) + 1) * 2 ^ k < init.length) →
    ∀ q < flags.length,
      (runW (flags.mapIdx fun q w => ⟨.and, [w, (2 * (off + q) + 1) * 2 ^ k]⟩) init).getD (init.length + q) false =
        (init.getD (flags.getD q 0) false && init.getD ((2 * (off + q) + 1) * 2 ^ k) false) := by
  intro off flags
  induction flags generalizing off with
  | nil => intro _ _ _ q hq; exact absurd hq (Nat.not_lt_zero _)
  | cons w ws ih =>
    intro init hfl hpiv q hq
    have hw0 : w < init.length := hfl w List.mem_cons_self
    have hp0 : (2 * (off + 0) + 1) * 2 ^ k < init.length := hpiv 0 (by simp)
    have hmap : ((w :: ws).mapIdx fun q w => ({ op := .and, inputs := [w, (2 * (off + q) + 1) * 2 ^ k] } : Gate)) =
        ({ op := .and, inputs := [w, (2 * off + 1) * 2 ^ k] } : Gate) ::
        (ws.mapIdx fun q w => ({ op := .and, inputs := [w, (2 * ((off + 1) + q) + 1) * 2 ^ k] } : Gate)) := by
      simp only [List.mapIdx_cons, Nat.add_zero]
      congr 1
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_mapIdx]
      congr 2; congr 1; congr 1; omega
    rw [hmap, runW_cons]
    let init1 := init ++ [GateOp.and.eval ([w, (2 * off + 1) * 2 ^ k].map fun i => init.getD i false)]
    have hl1 : init1.length = init.length + 1 := by simp [init1]
    change (runW (ws.mapIdx fun q w => ⟨.and, [w, (2 * ((off + 1) + q) + 1) * 2 ^ k]⟩) init1).getD
      (init.length + q) false = _
    cases q with
    | zero =>
      simp only [Nat.add_zero]
      rw [runW_old _ init1 init.length (by omega)]
      simp [init1, GateOp.eval]
    | succ q' =>
      have hq' : q' < ws.length := by simp at hq; omega
      have hidx : init.length + (q' + 1) = init1.length + q' := by omega
      rw [hidx]
      have hres := ih (off + 1) init1
        (fun x hx => by have := hfl x (List.mem_cons_of_mem _ hx); omega)
        (fun r hr => by
          have := hpiv (r + 1) (by simp; omega)
          have heq : off + 1 + r = off + (r + 1) := by omega
          rw [heq]; omega)
        q' hq'
      rw [hres]
      have hflq : ws.getD q' 0 < init.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq', Option.getD_some]
        exact hfl ws[q'] (List.mem_cons_of_mem _ (List.getElem_mem hq'))
      have hpq : (2 * (off + 1 + q') + 1) * 2 ^ k < init.length := by
        have := hpiv (q' + 1) (by simp; omega)
        have heq : off + 1 + q' = off + (q' + 1) := by omega
        rw [heq]; exact this
      rw [List.getD_append _ _ _ _ hflq, List.getD_append _ _ _ _ hpq]
      have heq : off + 1 + q' = off + (q' + 1) := by omega
      rw [heq]
      rfl

def leftGs (nsel : ℕ) (flags : List ℕ) : List Gate :=
  flags.map (fun w => ⟨.and, [w, nsel]⟩)

lemma leftGs_len (nsel : ℕ) (flags : List ℕ) : (leftGs nsel flags).length = flags.length := by
  simp [leftGs]

lemma leftGs_notCnt (nsel : ℕ) (flags : List ℕ) : notCnt (leftGs nsel flags) = 0 := by
  apply notCnt_of_no_not
  intro g hg
  simp only [leftGs, List.mem_map] at hg
  obtain ⟨_, _, rfl⟩ := hg; simp

lemma leftGs_valid (nsel base : ℕ) (flags : List ℕ) (hns : nsel < base) (hfl : ∀ w ∈ flags, w < base) :
    validGs base (leftGs nsel flags) := by
  refine ⟨fun g hg => ?_, fun j hj i hi => ?_⟩
  · simp only [leftGs, List.mem_map] at hg; obtain ⟨_, _, rfl⟩ := hg; simp
  · rw [leftGs_len] at hj
    have hget : (leftGs nsel flags).getD j ⟨GateOp.or, []⟩ = ⟨.and, [flags[j], nsel]⟩ := by
      simp [leftGs, List.getD_eq_getElem?_getD, hj]
    rw [hget] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := hfl flags[j] (List.getElem_mem hj); omega
    · omega

lemma leftGs_eval (nsel : ℕ) : ∀ (flags : List ℕ) (init : List Bool),
    nsel < init.length → (∀ w ∈ flags, w < init.length) →
    ∀ q < flags.length,
      (runW (leftGs nsel flags) init).getD (init.length + q) false =
        (init.getD (flags.getD q 0) false && init.getD nsel false) := by
  intro flags
  induction flags with
  | nil => intro _ _ _ q hq; exact absurd hq (Nat.not_lt_zero _)
  | cons w ws ih =>
    intro init hns hfl q hq
    have hcons : leftGs nsel (w :: ws) = ⟨.and, [w, nsel]⟩ :: leftGs nsel ws := rfl
    rw [hcons, runW_cons]
    let init1 := init ++ [GateOp.and.eval ([w, nsel].map fun i => init.getD i false)]
    have hl1 : init1.length = init.length + 1 := by simp [init1]
    cases q with
    | zero =>
      simp only [Nat.add_zero]
      rw [runW_old _ init1 init.length (by omega)]
      simp [init1, GateOp.eval]
    | succ q' =>
      have hq' : q' < ws.length := by simp at hq; omega
      have hidx : init.length + (q' + 1) = init1.length + q' := by omega
      rw [hidx]
      have hres := ih init1 (by omega)
        (fun x hx => by have := hfl x (List.mem_cons_of_mem _ hx); omega) q' hq'
      rw [hres]
      have hflq : ws.getD q' 0 < init.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq', Option.getD_some]
        exact hfl ws[q'] (List.mem_cons_of_mem _ (List.getElem_mem hq'))
      rw [List.getD_append _ _ _ _ hflq, List.getD_append _ _ _ _ hns]
      rfl

def levelStep (h k base : ℕ) (flags : List ℕ) : List Gate × List ℕ :=
  let m := flags.length
  let g1 := andPivotGs k flags
  let tWires := (List.range m).map (fun q => base + q)
  let selP := orList (base + m) (2 ^ h) tWires
  let nselWire := base + m + selP.1.length
  let g3 := [⟨.not, [selP.2]⟩]
  let leftBase := nselWire + 1
  let g4 := leftGs nselWire flags
  let newFlags := (List.range m).flatMap (fun q => [leftBase + q, base + q])
  (g1 ++ selP.1 ++ g3 ++ g4, newFlags)

lemma flatMap_pair_len (m : ℕ) (f1 f2 : ℕ → ℕ) :
    ((List.range m).flatMap (fun q => [f1 q, f2 q])).length = 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp; omega

lemma flatMap_pair_getD (m : ℕ) (f1 f2 : ℕ → ℕ) (r : ℕ) (hr : r < 2 * m) :
    ((List.range m).flatMap (fun q => [f1 q, f2 q])).getD r 0 =
      if r % 2 = 0 then f1 (r / 2) else f2 (r / 2) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hlt : r < 2 * m
    · rw [List.getD_append _ _ _ _ (by rw [flatMap_pair_len]; exact hlt)]
      exact ih hlt
    · rw [List.getD_append_right _ _ _ _ (by rw [flatMap_pair_len]; omega)]
      rw [flatMap_pair_len]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hcases : r = 2 * m ∨ r = 2 * m + 1 := by omega
      rcases hcases with rfl | rfl
      · simp
      · have hsub : 2 * m + 1 - 2 * m = 1 := by omega
        have hmod : (2 * m + 1) % 2 = 1 := by omega
        have hdiv : (2 * m + 1) / 2 = m := by omega
        rw [hsub, hmod, hdiv]
        simp

lemma levelStep_len (h k base : ℕ) (flags : List ℕ) :
    (levelStep h k base flags).1.length ≤ 3 * flags.length + 1 ∧
    notCnt (levelStep h k base flags).1 = 1 ∧
    (levelStep h k base flags).2.length = 2 * flags.length := by
  unfold levelStep
  dsimp only
  have hl1 : (andPivotGs k flags).length = flags.length := andPivotGs_len k flags
  have hl2 : (orList (base + flags.length) (2 ^ h) ((List.range flags.length).map (fun q => base + q))).1.length ≤
      flags.length := by
    have := orList_len_le (base + flags.length) (2 ^ h) ((List.range flags.length).map (fun q => base + q))
    simpa using this
  refine ⟨by simp only [List.length_append, List.length_singleton, hl1, leftGs_len]; omega, ?_, ?_⟩
  · simp only [notCnt_append, andPivotGs_notCnt, orList_notCnt, leftGs_notCnt]
    rfl
  · exact flatMap_pair_len flags.length _ _

lemma levelStep_valid (h k base : ℕ) (flags : List ℕ) (hM : 2 ^ h < base)
    (hfl : ∀ w ∈ flags, w < base) (hflLen : flags.length * 2 ^ (k + 1) ≤ 2 ^ h) :
    validGs base (levelStep h k base flags).1 ∧
    ∀ w ∈ (levelStep h k base flags).2, w < base + (levelStep h k base flags).1.length := by
  unfold levelStep
  dsimp only
  set m := flags.length
  set g1 := andPivotGs k flags
  set tWires := (List.range m).map (fun q => base + q)
  set selP := orList (base + m) (2 ^ h) tWires
  set nselWire := base + m + selP.1.length
  set g3 : List Gate := [⟨.not, [selP.2]⟩]
  set leftBase := nselWire + 1
  set g4 := leftGs nselWire flags
  have hg1len : g1.length = m := andPivotGs_len k flags
  have hv1 : validGs base g1 := andPivotGs_valid h k base flags (by omega) hfl hflLen
  have htW : ∀ w ∈ tWires, w < base + m := by
    intro w hw; simp only [tWires, List.mem_map, List.mem_range] at hw
    obtain ⟨q, hq, rfl⟩ := hw; omega
  have hv2 : validGs (base + g1.length) selP.1 := by
    rw [hg1len]; exact orList_valid (base + m) (2 ^ h) tWires htW
  have hselOut : selP.2 < nselWire := by
    exact orList_out (base + m) (2 ^ h) tWires (by omega) htW
  have hv3 : validGs (base + (g1 ++ selP.1).length) g3 := by
    refine ⟨fun g hg => by simp [g3] at hg; subst hg; simp, fun j hj i hi => ?_⟩
    simp [g3] at hj; subst hj
    simp only [g3, List.getD_cons_zero, List.mem_singleton] at hi
    subst hi
    simp only [List.length_append, hg1len]; omega
  have hv4 : validGs (base + (g1 ++ selP.1 ++ g3).length) g4 := by
    have heq : base + (g1 ++ selP.1 ++ g3).length = leftBase := by
      simp only [List.length_append, List.length_singleton, g3, hg1len, leftBase, nselWire]; omega
    rw [heq]
    exact leftGs_valid nselWire leftBase flags (by omega) (fun w hw => by have := hfl w hw; omega)
  constructor
  · exact validGs_append (validGs_append (validGs_append hv1 hv2) hv3) hv4
  · intro w hw
    have hg4len : g4.length = m := leftGs_len nselWire flags
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain ⟨q, hq, rfl | rfl⟩ := hw
    · simp only [List.length_append, List.length_singleton, hg1len, hg4len, g3, leftBase, nselWire]
      omega
    · simp only [List.length_append, List.length_singleton, hg1len, hg4len, g3]
      omega

lemma levelStep_eval (h k : ℕ) (hk : k < h) (flags : List ℕ) (init : List Bool) (Y : Finset ℕ)
    (s : Fin (2 ^ h)) (hcell : cell h s Y)
    (hM : 2 ^ h < init.length) (hz : init.getD (2 ^ h) false = false)
    (hY : ∀ p < 2 ^ h, init.getD p false = decide (p ∈ Y))
    (hfl : ∀ w ∈ flags, w < init.length)
    (hflLen : flags.length * 2 ^ (k + 1) = 2 ^ h)
    (hinv : ∀ q < flags.length, init.getD (flags.getD q 0) false = decide (q = s.val / 2 ^ (k + 1))) :
    ∀ r < 2 * flags.length,
      (runW (levelStep h k init.length flags).1 init).getD ((levelStep h k init.length flags).2.getD r 0) false =
        decide (r = s.val / 2 ^ k) := by
  intro r hr
  unfold levelStep
  dsimp only
  set m := flags.length
  set base := init.length
  set g1 := andPivotGs k flags
  set tWires := (List.range m).map (fun q => base + q)
  set selP := orList (base + m) (2 ^ h) tWires
  set nselWire := base + m + selP.1.length
  set g3 : List Gate := [⟨.not, [selP.2]⟩]
  set leftBase := nselWire + 1
  set g4 := leftGs nselWire flags
  let w1 := runW g1 init
  let w2 := runW selP.1 w1
  let w3 := runW g3 w2
  let w4 := runW g4 w3
  have hw1len : w1.length = base + m := by simp [w1, runW_len, g1, andPivotGs_len, base, m]
  have hw2len : w2.length = nselWire := by simp [w2, runW_len, hw1len, nselWire]
  have hw3len : w3.length = leftBase := by simp [w3, runW_len, hw2len, g3, leftBase]
  have hrun : runW (g1 ++ selP.1 ++ g3 ++ g4) init = w4 := by
    simp only [w4, w3, w2, w1, runW_append]
  rw [hrun, flatMap_pair_getD m _ _ r hr]
  have hpivLt : ∀ q < m, (2 * q + 1) * 2 ^ k < 2 ^ h := by
    intro q hq
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : (2 * q + 1) * 2 ^ k < (q + 1) * 2 ^ (k + 1) := by
      rw [hpow]; nlinarith [Nat.pow_pos (a := 2) (n := k) (by decide)]
    have h2 : (q + 1) * 2 ^ (k + 1) ≤ m * 2 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have htq : ∀ q < m, w1.getD (base + q) false =
      (decide (q = s.val / 2 ^ (k + 1)) && decide ((2 * q + 1) * 2 ^ k ∈ Y)) := by
    intro q hq
    have hev := andPivotGs_eval_aux k 0 flags init hfl (fun i hi => by
      simp only [Nat.zero_add]; have := hpivLt i hi; omega) q hq
    simp only [Nat.zero_add] at hev
    dsimp only [w1, g1, andPivotGs, base]
    rw [hev, hinv q hq, hY _ (hpivLt q hq)]
  have hsdivLt : s.val / 2 ^ (k + 1) < m := by
    have : (s.val / 2 ^ (k + 1)) * 2 ^ (k + 1) ≤ s.val := Nat.div_mul_le_self _ _
    have hlt : (s.val / 2 ^ (k + 1)) * 2 ^ (k + 1) < m * 2 ^ (k + 1) := by omega
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hselBit : decide (pivot s.val k ∈ Y) = decide (s.val / 2 ^ k % 2 = 1) := by
    cases hb : decide (s.val / 2 ^ k % 2 = 1) with
    | true =>
      have hin : pivot s.val k ∈ Y := hcell.1 (by
        simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        exact ⟨k, ⟨hk, hb⟩, rfl⟩)
      simp [hin]
    | false =>
      have hnot : pivot s.val k ∉ Y := Finset.disjoint_left.mp hcell.2 (by
        simp only [path, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        exact ⟨k, ⟨hk, hb⟩, rfl⟩)
      simp [hnot]
  have hselVal : w2.getD selP.2 false = decide (s.val / 2 ^ k % 2 = 1) := by
    have hev := orList_eval (2 ^ h) tWires w1
      (by rw [runW_old g1 init (2 ^ h) hM, hz])
      (fun w hw => by
        simp only [tWires, List.mem_map, List.mem_range] at hw
        obtain ⟨q, hq, rfl⟩ := hw; omega)
    rw [hw1len] at hev
    change w2.getD selP.2 false = _
    rw [hev, ← hselBit]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨w, hw, hwt⟩
      simp only [tWires, List.mem_map, List.mem_range] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      rw [htq q hq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwt
      obtain ⟨rfl, hin⟩ := hwt
      exact hin
    · intro hin
      refine ⟨base + s.val / 2 ^ (k + 1), ?_, ?_⟩
      · simp only [tWires, List.mem_map, List.mem_range]
        exact ⟨s.val / 2 ^ (k + 1), hsdivLt, rfl⟩
      · rw [htq _ hsdivLt, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨rfl, hin⟩
  have hnselVal : w3.getD nselWire false = decide (s.val / 2 ^ k % 2 = 0) := by
    have hstep : w3 = w2 ++ [!w2.getD selP.2 false] := by
      simp [w3, g3, runW, GateOp.eval]
    rw [hstep, ← hw2len, List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self, List.getD_cons_zero, hselVal]
    cases hmod : s.val / 2 ^ k % 2 with
    | zero => rfl
    | succ n =>
      have : n = 0 := by omega
      subst this; rfl
  have hr2 : r / 2 < m := by omega
  have hdiv2 : (s.val / 2 ^ k) / 2 = s.val / 2 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  by_cases heven : r % 2 = 0
  · simp only [heven, ite_true]
    have hfl3 : ∀ w ∈ flags, w < w3.length := fun w hw => by have := hfl w hw; omega
    have hev4 := leftGs_eval nselWire flags w3 (by omega) hfl3 (r / 2) hr2
    rw [hw3len] at hev4
    change w4.getD (leftBase + r / 2) false = _
    rw [hev4, hnselVal]
    have hflq : flags.getD (r / 2) 0 < base := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr2, Option.getD_some]
      exact hfl flags[r / 2] (List.getElem_mem hr2)
    have h3eq : w3.getD (flags.getD (r / 2) 0) false = init.getD (flags.getD (r / 2) 0) false := by
      rw [runW_old g3 w2 _ (by omega), runW_old selP.1 w1 _ (by omega), runW_old g1 init _ hflq]
    rw [h3eq, hinv (r / 2) hr2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; omega
    · intro h1; subst h1; exact ⟨hdiv2, heven⟩
  · simp only [heven, ite_false]
    have h4eq : w4.getD (base + r / 2) false = w1.getD (base + r / 2) false := by
      rw [runW_old g4 w3 _ (by omega), runW_old g3 w2 _ (by omega), runW_old selP.1 w1 _ (by omega)]
    rw [h4eq, htq (r / 2) hr2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hp : pivot s.val k ∈ Y := by unfold pivot; rw [← h1]; exact h2
      have hsb : s.val / 2 ^ k % 2 = 1 := by
        have := hselBit
        simp [hp] at this
        exact this
      omega
    · intro h1
      subst h1
      refine ⟨hdiv2, ?_⟩
      have hsb : s.val / 2 ^ k % 2 = 1 := by omega
      have := hselBit
      simp [hsb] at this
      unfold pivot at this
      rw [hdiv2]
      exact this

def buildTreeAux (h : ℕ) : ℕ → List Gate × List ℕ
  | 0 => ([], [2 ^ h + 1])
  | d + 1 =>
    let p := buildTreeAux h d
    let step := levelStep h (h - 1 - d) (2 ^ h + 2 + p.1.length) p.2
    (p.1 ++ step.1, step.2)

lemma buildTreeAux_props (h : ℕ) : ∀ d ≤ h,
    (buildTreeAux h d).2.length = 2 ^ d ∧
    notCnt (buildTreeAux h d).1 = d ∧
    (buildTreeAux h d).1.length ≤ 3 * (2 ^ d - 1) + d ∧
    validGs (2 ^ h + 2) (buildTreeAux h d).1 ∧
    (∀ w ∈ (buildTreeAux h d).2, w < 2 ^ h + 2 + (buildTreeAux h d).1.length) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [buildTreeAux, Nat.pow_zero, List.length_singleton, List.length_nil, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero, le_refl, true_and]
    refine ⟨rfl, validGs_nil _, fun w hw => by simp at hw; omega⟩
  | succ d ih =>
    intro hd
    obtain ⟨hlen, hnot, hsz, hval, hfl⟩ := ih (by omega)
    unfold buildTreeAux
    dsimp only
    set p := buildTreeAux h d
    set k := h - 1 - d
    set step := levelStep h k (2 ^ h + 2 + p.1.length) p.2
    have hstep : step = levelStep h k (2 ^ h + 2 + p.1.length) p.2 := rfl
    obtain ⟨hsLen, hsNot, hsFlen⟩ := levelStep_len h k (2 ^ h + 2 + p.1.length) p.2
    rw [← hstep] at hsLen hsNot hsFlen
    have hmul : p.2.length * 2 ^ (k + 1) = 2 ^ h := by
      rw [hlen, ← Nat.pow_add]; congr 1; omega
    obtain ⟨hvStep, hflStep⟩ := levelStep_valid h k (2 ^ h + 2 + p.1.length) p.2 (by omega) hfl (le_of_eq hmul)
    rw [← hstep] at hvStep hflStep
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsFlen, hlen, Nat.pow_succ, Nat.mul_comm]
    · rw [notCnt_append, hnot, hsNot]
    · rw [List.length_append]
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
      omega
    · exact validGs_append hval (by simpa only [Nat.add_assoc] using hvStep)
    · intro w hw
      have := hflStep w hw
      rw [List.length_append]
      omega

lemma buildTreeAux_eval (h : ℕ) (Y : Finset ℕ) (s : Fin (2 ^ h)) (hcell : cell h s Y)
    (init : List Bool) (hinitLen : init.length = 2 ^ h + 2)
    (hinitZ : init.getD (2 ^ h) false = false) (hinitO : init.getD (2 ^ h + 1) false = true)
    (hinitY : ∀ p < 2 ^ h, init.getD p false = decide (p ∈ Y)) :
    ∀ d ≤ h, ∀ r < 2 ^ d,
      (runW (buildTreeAux h d).1 init).getD ((buildTreeAux h d).2.getD r 0) false =
        decide (r = s.val / 2 ^ (h - d)) := by
  intro d
  induction d with
  | zero =>
    intro _ r hr
    have hr0 : r = 0 := by simp at hr; exact hr
    subst hr0
    simp only [buildTreeAux, runW_nil, List.getD_cons_zero, Nat.sub_zero, hinitO]
    have hdiv : s.val / 2 ^ h = 0 := Nat.div_eq_of_lt s.isLt
    simp [hdiv]
  | succ d ih =>
    intro hd r hr
    obtain ⟨hlen, _, _, _, hfl⟩ := buildTreeAux_props h d (by omega)
    unfold buildTreeAux
    dsimp only
    set p := buildTreeAux h d
    set k := h - 1 - d
    set w0 := runW p.1 init
    have hw0len : w0.length = 2 ^ h + 2 + p.1.length := by rw [runW_len, hinitLen]
    rw [runW_append]
    change (runW (levelStep h k (2 ^ h + 2 + p.1.length) p.2).1 w0).getD
      ((levelStep h k (2 ^ h + 2 + p.1.length) p.2).2.getD r 0) false = _
    rw [← hw0len]
    have hmul : p.2.length * 2 ^ (k + 1) = 2 ^ h := by
      rw [hlen, ← Nat.pow_add]; congr 1; omega
    have hr' : r < 2 * p.2.length := by rw [hlen, ← Nat.mul_comm, ← Nat.pow_succ]; exact hr
    have hk1 : k + 1 = h - d := by omega
    have hres := levelStep_eval h k (by omega) p.2 w0 Y s hcell (by omega)
      (by rw [runW_old p.1 init (2 ^ h) (by omega), hinitZ])
      (fun x hx => by rw [runW_old p.1 init x (by omega), hinitY x hx])
      (fun w hw => by rw [hw0len]; exact hfl w hw)
      hmul
      (fun q hq => by rw [hk1]; exact ih (by omega) q (by omega))
      r hr'
    have hkeq : h - (d + 1) = k := by omega
    rw [hkeq]
    exact hres

lemma part4 (h : ℕ) (f : Fin (2 ^ h) → Bool) :
    let bits := fun (r : ℕ) (Y : Finset ℕ) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false, true]
    ∃ D : Circuit,
      (FanInTwo D ∧ ReadsBack (2 ^ h + 2) D ∧ D.output < 2 ^ h + 2 + D.size) ∧
      notCount D ≤ h ∧ D.size - notCount D ≤ 6 * 2 ^ h ∧
      ∀ Y ⊆ Finset.range (2 ^ h), ∀ s : Fin (2 ^ h), cell h s Y → D.eval (bits (2 ^ h) Y) = f s := by
  intro bits
  let M := 2 ^ h
  let tree := buildTreeAux h h
  obtain ⟨hlen, hnot, hsz, hval, hfl⟩ := buildTreeAux_props h h le_rfl
  let selLeaves : List ℕ :=
    (List.finRange M).filterMap (fun i => if f i then some (tree.2.getD i.val 0) else none)
  have hselLen : selLeaves.length ≤ M := by
    calc selLeaves.length ≤ (List.finRange M).length := List.length_filterMap_le _ _
      _ = M := List.length_finRange
  have hselLt : ∀ w ∈ selLeaves, w < M + 2 + tree.1.length := by
    intro w hw
    simp only [selLeaves, List.mem_filterMap] at hw
    obtain ⟨i, _, hi⟩ := hw
    split at hi
    · injection hi with hEq
      subst hEq
      have hiLt : i.val < tree.2.length := by rw [hlen]; exact i.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiLt, Option.getD_some]
      exact hfl tree.2[i.val] (List.getElem_mem hiLt)
    · contradiction
  let outP := orList (M + 2 + tree.1.length) M selLeaves
  let D : Circuit := ⟨tree.1 ++ outP.1, outP.2⟩
  have hDval : validGs (M + 2) D.gates :=
    validGs_append hval (orList_valid (M + 2 + tree.1.length) M selLeaves hselLt)
  have hDnot : notCount D = h := by
    change notCnt (tree.1 ++ outP.1) = h
    rw [notCnt_append, hnot, orList_notCnt, Nat.add_zero]
  have hDout : D.output < M + 2 + D.size := by
    have hout : outP.2 < M + 2 + tree.1.length + outP.1.length :=
      orList_out (M + 2 + tree.1.length) M selLeaves (by omega) hselLt
    change outP.2 < M + 2 + (tree.1 ++ outP.1).length
    rw [List.length_append]
    omega
  have hDsz : D.size - notCount D ≤ 6 * M := by
    rw [hDnot]
    have ho : outP.1.length ≤ M := le_trans (orList_len_le _ _ _) hselLen
    have ht : tree.1.length ≤ 3 * (2 ^ h - 1) + h := hsz
    change (tree.1 ++ outP.1).length - h ≤ 6 * M
    rw [List.length_append]
    omega
  refine ⟨D, ⟨hDval.1, hDval.2, hDout⟩, le_of_eq hDnot, hDsz, fun Y _ s hcell => ?_⟩
  let init := bits M Y
  have hinitLen : init.length = M + 2 := by simp [init, bits]
  have hinitZ : init.getD M false = false := by
    simp [init, bits]
  have hinitO : init.getD (M + 1) false = true := by
    have h1 : (List.ofFn (fun j : Fin M => decide (j.val ∈ Y))).length = M := by simp
    simp only [init, bits]
    rw [List.getD_append_right _ _ _ _ (by omega), h1]
    have : M + 1 - M = 1 := by omega
    rw [this]; rfl
  have hinitY : ∀ p < M, init.getD p false = decide (p ∈ Y) := by
    intro p hp
    simp only [init, bits]
    rw [List.getD_append _ _ _ _ (by simp [hp])]
    simp [List.getD_eq_getElem?_getD, hp]
  have htreeEv := buildTreeAux_eval h Y s hcell init hinitLen hinitZ hinitO hinitY h le_rfl
  let wTree := runW tree.1 init
  have hwTreeLen : wTree.length = M + 2 + tree.1.length := by rw [runW_len, hinitLen]
  rw [eval_eq_runW]
  change (runW (tree.1 ++ outP.1) init).getD outP.2 false = f s
  rw [runW_append]
  have hevOut := orList_eval M selLeaves wTree
    (by rw [runW_old tree.1 init M (by omega), hinitZ])
    (fun w hw => by rw [hwTreeLen]; exact hselLt w hw)
  rw [hwTreeLen] at hevOut
  rw [hevOut]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, hw, hwt⟩
    simp only [selLeaves, List.mem_filterMap] at hw
    obtain ⟨i, _, hi⟩ := hw
    cases hfi : f i with
    | false => simp [hfi] at hi
    | true =>
      simp only [hfi, ite_true, Option.some.injEq] at hi
      subst hi
      have h1 := htreeEv i.val i.isLt
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at h1
      rw [h1, decide_eq_true_eq] at hwt
      have his : i = s := Fin.ext hwt
      rw [← his, hfi]
  · intro hfs
    refine ⟨tree.2.getD s.val 0, ?_, ?_⟩
    · simp only [selLeaves, List.mem_filterMap]
      exact ⟨s, List.mem_finRange s, by simp [hfs]⟩
    · have h1 := htreeEv s.val s.isLt
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one, decide_true] at h1
      exact h1

end PEqualNP.Outside.L_lib_1433

theorem PEqualNP.Outside.L_lib_1433 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true]
let valid := fun (r : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧ D.output < r+2+D.size
let pivot := fun (s j : Nat) => (2*(s/(2^(j+1)))+1)*2^j
let path := fun (h s : Nat) (v : Bool) =>
  ((Finset.range h).filter (fun j => decide (s/2^j % 2=1)=v)).image (pivot s)
∀ h : Nat,
  let M := 2^h
  let cell := fun (s : Fin M) (Y : Finset Nat) => path h s.val true ⊆ Y ∧ Disjoint (path h s.val false) Y
  (∀ s : Fin M, (path h s.val true ∪ path h s.val false).card = h ∧ cell s (Finset.Icc 1 s.val)) ∧
  (∀ Y ⊆ Finset.range M, ∃! s : Fin M, cell s Y) ∧
  (∀ (X Y : Finset Nat) (s t : Fin M), X ⊆ Y → cell s X → cell t Y → s ≤ t) ∧
  (∀ f : Fin M → Bool, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, valid M D ∧
    PEqualNP.NotBracket.notCount D ≤ h ∧ D.size-PEqualNP.NotBracket.notCount D ≤ 6*M ∧
    ∀ Y ⊆ Finset.range M, ∀ s, cell s Y → D.eval (bits M Y)=f s)) := by
  dsimp only
  intro h
  have hpath : ∀ s v,
      (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
       Finset.image (fun j => (2 * (s / 2 ^ (j + 1)) + 1) * 2 ^ j)
         ({j ∈ Finset.range h | decide (s / 2 ^ j % 2 = 1) = v})) =
      PEqualNP.Outside.L_lib_1433.path h s v := by
    intro s v
    ext x
    simp only [PEqualNP.Outside.L_lib_1433.path, PEqualNP.Outside.L_lib_1433.pivot,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact exists_congr fun j => and_congr_left fun _ => and_congr_right fun _ => by
      rw [Subsingleton.elim (Classical.propDecidable _) (inferInstance)]
  have hbits : ∀ Y : Finset ℕ,
      List.ofFn (fun j : Fin (2 ^ h) => @decide (j.val ∈ Y) (Classical.propDecidable _)) ++ [false, true] =
      List.ofFn (fun j : Fin (2 ^ h) => decide (j.val ∈ Y)) ++ [false, true] := by
    intro Y
    congr 1; apply congrArg List.ofFn; funext j
    exact congrArg (@decide (j.val ∈ Y)) (Subsingleton.elim _ _)
  simp only [hpath, hbits]
  refine ⟨fun s => by convert PEqualNP.Outside.L_lib_1433.part1 h s; rfl,
    fun Y _ => PEqualNP.Outside.L_lib_1433.part2 h Y,
    PEqualNP.Outside.L_lib_1433.part3 h,
    PEqualNP.Outside.L_lib_1433.part4 h⟩
