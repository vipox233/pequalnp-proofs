import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25834

def fwd (d : ℕ) (T : ℕ → ZMod 2) (n : ℕ) : ZMod 2 :=
  if _h : n < 2 * d ∨ d = 0 then 0
  else T (n - 2 * d) - fwd d T (n - 2 * d) - fwd d T (n - d)
termination_by n
decreasing_by all_goals omega

lemma mix_surj (k lo d m : ℕ) [NeZero k] (hd : 0 < d) (hlo : d ≤ lo) (hm : m + 2 * d ≤ k)
    (T : ZMod k → ZMod 2) :
    ∃ w : ZMod k → ZMod 2, ∀ j, j < m →
      w (((lo + j : ℕ) : ZMod k) - (d : ZMod k)) + w ((lo + j : ℕ) : ZMod k)
        + w (((lo + j : ℕ) : ZMod k) + (d : ZMod k)) = T ((lo + j : ℕ) : ZMod k) := by
  refine ⟨fun s => fwd d (fun j => T ((lo + j : ℕ) : ZMod k)) (s - ((lo - d : ℕ) : ZMod k)).val, ?_⟩
  intro j hj
  have e1 : ((lo + j : ℕ) : ZMod k) - (d : ZMod k) - ((lo - d : ℕ) : ZMod k) = ((j : ℕ) : ZMod k) := by
    rw [Nat.cast_sub hlo]; push_cast; ring
  have e2 : ((lo + j : ℕ) : ZMod k) - ((lo - d : ℕ) : ZMod k) = ((j + d : ℕ) : ZMod k) := by
    rw [Nat.cast_sub hlo]; push_cast; ring
  have e3 : ((lo + j : ℕ) : ZMod k) + (d : ZMod k) - ((lo - d : ℕ) : ZMod k) = ((j + 2 * d : ℕ) : ZMod k) := by
    rw [Nat.cast_sub hlo]; push_cast; ring
  simp only [e1, e2, e3]
  rw [ZMod.val_cast_of_lt (show j < k by omega), ZMod.val_cast_of_lt (show j + d < k by omega),
    ZMod.val_cast_of_lt (show j + 2 * d < k by omega)]
  have hstep : fwd d (fun j => T ((lo + j : ℕ) : ZMod k)) (j + 2 * d)
      = T ((lo + j : ℕ) : ZMod k) - fwd d (fun j => T ((lo + j : ℕ) : ZMod k)) j
        - fwd d (fun j => T ((lo + j : ℕ) : ZMod k)) (j + d) := by
    conv_lhs => rw [fwd]
    rw [dif_neg (by omega)]
    rw [show j + 2 * d - 2 * d = j by omega, show j + 2 * d - d = j + d by omega]
  rw [hstep]; ring

def back (k lo : ℕ) (t : ℕ → ZMod 2) (n : ℕ) : ZMod 2 :=
  if _h : lo ≤ n ∧ n < k then t n - (1 + back k lo t (n + 1)) * back k lo t (n + 2) else 0
termination_by k - n
decreasing_by all_goals omega

lemma back_cast (k lo m : ℕ) [NeZero k] (t : ℕ → ZMod 2) (hm : m < k + lo) (hlk : lo ≤ k) :
    back k lo t ((m : ZMod k)).val = back k lo t m := by
  by_cases h : m < k
  · rw [ZMod.val_cast_of_lt h]
  · have hk : k ≤ m := by omega
    have hv : ((m : ZMod k)).val = m - k := by
      have : ((m : ZMod k)) = ((m - k : ℕ) : ZMod k) := by
        rw [Nat.cast_sub hk, ZMod.natCast_self, sub_zero]
      rw [this, ZMod.val_cast_of_lt]
      have := NeZero.ne k
      omega
    rw [hv]
    conv_lhs => rw [back]
    conv_rhs => rw [back]
    rw [dif_neg (by omega), dif_neg (by omega)]

lemma chi_surj (k lo : ℕ) [NeZero k] (hlo : 2 ≤ lo) (hlk : lo ≤ k) (t : ZMod k → ZMod 2) :
    ∃ Q : ZMod k → ZMod 2, ∀ i : ZMod k, lo ≤ i.val → Q i + (1 + Q (i + 1)) * Q (i + 2) = t i := by
  refine ⟨fun s => back k lo (fun n => t (n : ZMod k)) s.val, ?_⟩
  intro i hi
  have hlt : i.val < k := ZMod.val_lt i
  have e1 : i + 1 = ((i.val + 1 : ℕ) : ZMod k) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have e2 : i + 2 = ((i.val + 2 : ℕ) : ZMod k) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  simp only []
  rw [e1, e2, back_cast k lo _ _ (by omega) hlk, back_cast k lo _ _ (by omega) hlk]
  have h0 : back k lo (fun n => t (n : ZMod k)) i.val
      = t i - (1 + back k lo (fun n => t (n : ZMod k)) (i.val + 1))
          * back k lo (fun n => t (n : ZMod k)) (i.val + 2) := by
    conv_lhs => rw [back]
    rw [dif_pos ⟨hi, hlt⟩, ZMod.natCast_zmod_val]
  rw [h0]; ring

lemma coeffs : ∀ r0 r1 r2 δ : ZMod 2,
    (∀ x y : ZMod 2, (0 + r0 + (1 + (x + r1)) * (y + r2)) + (0 + (1 + x) * y) + δ = 0) →
    r2 = 0 ∧ r1 = 0 ∧ r0 = δ := by decide

lemma split_row (k : ℕ) [NeZero k] (hk : 3 ≤ k) (r : ZMod k → ZMod 2) (i : ZMod k) (δ : ZMod 2)
    (H : ∀ P : ZMod k → ZMod 2,
      ((P i + r i) + (1 + (P (i+1) + r (i+1))) * (P (i+2) + r (i+2)))
        + (P i + (1 + P (i+1)) * P (i+2)) + δ = 0) :
    r (i+2) = 0 ∧ r (i+1) = 0 ∧ r i = δ := by
  have ne : ∀ n : ℕ, 0 < n → n < k → (n : ZMod k) ≠ 0 := by
    intro n h0 hn e
    have := congrArg ZMod.val e
    rw [ZMod.val_cast_of_lt hn, ZMod.val_zero] at this
    omega
  have n1 : (1 : ZMod k) ≠ 0 := by simpa using ne 1 (by omega) (by omega)
  have n2 : (2 : ZMod k) ≠ 0 := by simpa using ne 2 (by omega) (by omega)
  have a1 : i ≠ i + 1 := fun e => n1 (by linear_combination -e)
  have a2 : i ≠ i + 2 := fun e => n2 (by linear_combination -e)
  have a3 : i + 2 ≠ i + 1 := fun e => n1 (by linear_combination e)
  apply coeffs
  intro x y
  have := H (fun s => if s = i + 1 then x else if s = i + 2 then y else 0)
  simpa [a1, a2, a3] using this

end PEqualNP.Outside.L_meta_25834

theorem PEqualNP.Outside.L_meta_25834 : (∀ (k : ℕ) [NeZero k] (h : ℕ), 5 ≤ h → h + 7 ≤ k →
  let I := ZMod k
  let W := I → ZMod 2
  let lo := k - h
  let turn := fun (dist : ℕ) (word : W) (site : I) => word (site - (dist : I))
  let mix := fun (dist : ℕ) (word : W) (site : I) =>
    word (site - (dist : I)) + word site + word (site + (dist : I))
  let chi := fun (word : W) (site : I) =>
    word site + (1 + word (site+1)) * word (site+2)
  let tested := fun site : I => lo ≤ site.val
  ∀ (rowConst colConst : W),
    let good := fun (u v key : W) =>
      let row := chi (mix 1 (turn 1 key + u)) + key + rowConst
      let col := chi (mix 2 (turn 3 key + v)) + turn 4 key + colConst
      ∀ site : I, tested site → row site = 0 ∧ col site = 0
    let lifts := fun (a b d : W) => ∀ u v key : W,
      good u v key ↔ good (u+a) (v+b) (key+d)
    let active := fun i : I => tested i ∨ i = 0 ∨ i = 1
    ∀ a b d : W, lifts a b d ↔
      (∀ i : I, lo-3 ≤ i.val → d i = 0) ∧
      (∀ i : I, active i → mix 1 (a + turn 1 d) i = 0) ∧
      (∀ i : I, active i →
        mix 2 (b + turn 3 d) i = if i = (lo : I) then d ((lo-4 : ℕ) : I) else 0)) := by
  intro k _ h h5 hk I W lo turn mix chi tested rowConst colConst good lifts active a b d
  have hlo7 : 7 ≤ lo := by show 7 ≤ k - h; omega
  have hlok : lo + h = k := by show k - h + h = k; omega
  have two : ∀ z : ZMod 2, z + z = 0 := by decide
  have val_n : ∀ n : ℕ, n < k → ((n : I)).val = n := fun n hn => ZMod.val_cast_of_lt hn
  have cast_val : ∀ i : I, ((i.val : ℕ) : I) = i := fun i => ZMod.natCast_zmod_val i
  have wrap : ∀ n : ℕ, ((k + n : ℕ) : I) = (n : I) := by
    intro n; show (((k + n : ℕ)) : ZMod k) = (n : ZMod k)
    rw [Nat.cast_add, ZMod.natCast_self, zero_add]
  have act_n : ∀ j, j < h + 2 → active ((lo + j : ℕ) : I) := by
    intro j hj
    by_cases c : j < h
    · left; show lo ≤ (((lo + j : ℕ) : I)).val; rw [val_n _ (by omega)]; omega
    · right
      rcases (show j = h ∨ j = h + 1 by omega) with e | e
      · left; rw [e, hlok]; exact ZMod.natCast_self k
      · right
        rw [e, show lo + (h + 1) = k + 1 by omega, wrap]; exact Nat.cast_one
  have act_inv : ∀ i : I, active i → ∃ j, j < h + 2 ∧ i = ((lo + j : ℕ) : I) := by
    intro i hi
    rcases hi with ht | h0 | h1
    · have ht' : lo ≤ i.val := ht
      have hlt : i.val < k := ZMod.val_lt i
      refine ⟨i.val - lo, by omega, ?_⟩
      rw [show lo + (i.val - lo) = i.val by omega, cast_val]
    · exact ⟨h, by omega, by rw [h0, hlok]; exact (ZMod.natCast_self k).symm⟩
    · refine ⟨h + 1, by omega, ?_⟩
      rw [h1, show lo + (h + 1) = k + 1 by omega, wrap]; exact Nat.cast_one.symm
  have near : ∀ i : I, tested i → active i ∧ active (i+1) ∧ active (i+2) := by
    intro i ht
    have ht' : lo ≤ i.val := ht
    have hlt : i.val < k := ZMod.val_lt i
    have e1 : i + 1 = ((lo + (i.val - lo + 1) : ℕ) : I) := by
      rw [show lo + (i.val - lo + 1) = i.val + 1 by omega, Nat.cast_add, cast_val, Nat.cast_one]
    have e2 : i + 2 = ((lo + (i.val - lo + 2) : ℕ) : I) := by
      rw [show lo + (i.val - lo + 2) = i.val + 2 by omega, Nat.cast_add, cast_val, Nat.cast_ofNat]
    refine ⟨Or.inl ht, ?_, ?_⟩
    · rw [e1]; exact act_n _ (by omega)
    · rw [e2]; exact act_n _ (by omega)
  have pa : ∀ (f g : W) (x : I), (f + g) x = f x + g x := fun _ _ _ => rfl
  have addR : ∀ (u key : W) (i : I), mix 1 (turn 1 (key + d) + (u + a)) i
      = mix 1 (turn 1 key + u) i + mix 1 (a + turn 1 d) i := by
    intro u key i; simp only [mix, turn, pa]; ring
  have addC : ∀ (v key : W) (i : I), mix 2 (turn 3 (key + d) + (v + b)) i
      = mix 2 (turn 3 key + v) i + mix 2 (b + turn 3 d) i := by
    intro v key i; simp only [mix, turn, pa]; ring
  constructor
  swap
  · rintro ⟨hd, hra, hrb⟩ u v key
    show (∀ site : I, tested site → _) ↔ (∀ site : I, tested site → _)
    refine forall_congr' fun i => imp_congr_right fun ht => ?_
    have ht' : lo ≤ i.val := ht
    have hlt : i.val < k := ZMod.val_lt i
    obtain ⟨a0, a1, a2⟩ := near i ht
    have notlo : ∀ s : ℕ, 1 ≤ s → s ≤ 2 → i + (s : I) ≠ (lo : I) := by
      intro s s1 s2 e
      have e' : (((i.val + s : ℕ)) : I) = (lo : I) := by rw [Nat.cast_add, cast_val]; exact e
      have hv := congrArg ZMod.val e'
      rw [val_n lo (by omega)] at hv
      by_cases c : i.val + s < k
      · rw [val_n _ c] at hv; omega
      · rw [show i.val + s = k + (i.val + s - k) by omega, wrap, val_n _ (by omega)] at hv; omega
    have b1 : mix 2 (b + turn 3 d) (i+1) = 0 := by
      rw [hrb _ a1, if_neg]; simpa using notlo 1 (by omega) (by omega)
    have b2 : mix 2 (b + turn 3 d) (i+2) = 0 := by
      rw [hrb _ a2, if_neg]; simpa using notlo 2 (by omega) (by omega)
    have bd : mix 2 (b + turn 3 d) i = d (i - (4 : ℕ)) := by
      rw [hrb _ a0]
      have e4 : i - ((4 : ℕ) : I) = ((i.val - 4 : ℕ) : I) := by
        rw [Nat.cast_sub (show 4 ≤ i.val by omega), cast_val]
      by_cases c : i = (lo : I)
      · rw [if_pos c, e4]
        have : i.val = lo := by rw [c]; exact val_n lo (by omega)
        rw [this]
      · rw [if_neg c]
        have : i.val ≠ lo := fun e => c (by rw [← e, cast_val])
        symm
        apply hd
        rw [e4, val_n _ (by omega)]; omega
    have di : d i = 0 := hd i (by omega)
    have rowEq : chi (mix 1 (turn 1 (key + d) + (u + a))) i + (key + d) i + rowConst i
        = chi (mix 1 (turn 1 key + u)) i + key i + rowConst i := by
      simp only [chi, addR, hra _ a0, hra _ a1, hra _ a2, add_zero, pa, di]
    have colEq : chi (mix 2 (turn 3 (key + d) + (v + b))) i + turn 4 (key + d) i + colConst i
        = chi (mix 2 (turn 3 key + v)) i + turn 4 key i + colConst i := by
      have t4 : turn 4 (key + d) i = turn 4 key i + d (i - (4 : ℕ)) := rfl
      simp only [chi, addC, b1, b2, add_zero, t4]
      rw [bd]
      linear_combination two (d (i - (4 : ℕ)))
    show (chi (mix 1 (turn 1 key + u)) i + key i + rowConst i = 0 ∧
        chi (mix 2 (turn 3 key + v)) i + turn 4 key i + colConst i = 0) ↔
      (chi (mix 1 (turn 1 (key + d) + (u + a))) i + (key + d) i + rowConst i = 0 ∧
        chi (mix 2 (turn 3 (key + d) + (v + b))) i + turn 4 (key + d) i + colConst i = 0)
    rw [rowEq, colEq]
  · intro hl
    have realizeR : ∀ (key : W) (P : W), ∃ u : W, ∀ i, active i → mix 1 (turn 1 key + u) i = P i := by
      intro key P
      obtain ⟨w, hw⟩ := PEqualNP.Outside.L_meta_25834.mix_surj k lo 1 (h+2) (by omega) (by omega) (by omega) P
      refine ⟨w - turn 1 key, fun i hi => ?_⟩
      obtain ⟨j, hj, rfl⟩ := act_inv i hi
      have : turn 1 key + (w - turn 1 key) = w := by abel
      rw [this]; exact hw j hj
    have realizeC : ∀ (key : W) (Q : W), ∃ v : W, ∀ i, active i → mix 2 (turn 3 key + v) i = Q i := by
      intro key Q
      obtain ⟨w, hw⟩ := PEqualNP.Outside.L_meta_25834.mix_surj k lo 2 (h+2) (by omega) (by omega) (by omega) Q
      refine ⟨w - turn 3 key, fun i hi => ?_⟩
      obtain ⟨j, hj, rfl⟩ := act_inv i hi
      have : turn 3 key + (w - turn 3 key) = w := by abel
      rw [this]; exact hw j hj
    have surj : ∀ t : W, ∃ Q : W, ∀ i : I, tested i → chi Q i = t i := fun t =>
      PEqualNP.Outside.L_meta_25834.chi_surj k lo (by omega) (by omega) t
    have main : ∀ (key P Q : W),
        (∀ i : I, tested i → chi P i + key i + rowConst i = 0) →
        (∀ i : I, tested i → chi Q i + turn 4 key i + colConst i = 0) →
        ∀ i : I, tested i →
          chi (fun s => P s + mix 1 (a + turn 1 d) s) i + (key + d) i + rowConst i = 0 ∧
          chi (fun s => Q s + mix 2 (b + turn 3 d) s) i + turn 4 (key + d) i + colConst i = 0 := by
      intro key P Q hP hQ i ht
      obtain ⟨u, hu⟩ := realizeR key P
      obtain ⟨v, hv⟩ := realizeC key Q
      have g : good u v key := by
        intro s hs
        obtain ⟨s0, s1, s2⟩ := near s hs
        refine ⟨?_, ?_⟩
        · have e : chi (mix 1 (turn 1 key + u)) s = chi P s := by
            simp only [chi, hu _ s0, hu _ s1, hu _ s2]
          show chi (mix 1 (turn 1 key + u)) s + key s + rowConst s = 0
          rw [e]; exact hP s hs
        · have e : chi (mix 2 (turn 3 key + v)) s = chi Q s := by
            simp only [chi, hv _ s0, hv _ s1, hv _ s2]
          show chi (mix 2 (turn 3 key + v)) s + turn 4 key s + colConst s = 0
          rw [e]; exact hQ s hs
      have g' := (hl u v key).1 g i ht
      obtain ⟨s0, s1, s2⟩ := near i ht
      have e1 : chi (mix 1 (turn 1 (key + d) + (u + a))) i
          = chi (fun s => P s + mix 1 (a + turn 1 d) s) i := by
        simp only [chi, addR, hu _ s0, hu _ s1, hu _ s2]
      have e2 : chi (mix 2 (turn 3 (key + d) + (v + b))) i
          = chi (fun s => Q s + mix 2 (b + turn 3 d) s) i := by
        simp only [chi, addC, hv _ s0, hv _ s1, hv _ s2]
      rw [← e1, ← e2]; exact g'
    have hrow : ∀ (P : W) (i : I), tested i →
        chi (fun s => P s + mix 1 (a + turn 1 d) s) i + chi P i + d i = 0 := by
      intro P i ht
      let key : W := fun s => chi P s + rowConst s
      obtain ⟨Q, hQ⟩ := surj (fun s => turn 4 key s + colConst s)
      have := (main key P Q
        (fun s _ => by
          show chi P s + (chi P s + rowConst s) + rowConst s = 0
          linear_combination two (chi P s) + two (rowConst s))
        (fun s hs => by
          rw [hQ s hs]
          linear_combination two (turn 4 key s) + two (colConst s)) i ht).1
      have k1 : (key + d) i = chi P i + rowConst i + d i := rfl
      rw [k1] at this
      linear_combination this - two (rowConst i)
    have hcol : ∀ (Q : W) (i : I), tested i →
        chi (fun s => Q s + mix 2 (b + turn 3 d) s) i + chi Q i + d (i - (4 : ℕ)) = 0 := by
      intro Q i ht
      let key : W := fun s => chi Q (s + (4 : ℕ)) + colConst (s + (4 : ℕ))
      have k4 : ∀ s : I, turn 4 key s = chi Q s + colConst s := by
        intro s
        show chi Q (s - (4 : ℕ) + (4 : ℕ)) + colConst (s - (4 : ℕ) + (4 : ℕ)) = _
        rw [sub_add_cancel]
      obtain ⟨P, hP⟩ := surj (fun s => key s + rowConst s)
      have := (main key P Q
        (fun s hs => by
          rw [hP s hs]
          linear_combination two (key s) + two (rowConst s))
        (fun s _ => by
          rw [k4]
          linear_combination two (chi Q s) + two (colConst s)) i ht).2
      have k5 : turn 4 (key + d) i = turn 4 key i + d (i - (4 : ℕ)) := rfl
      rw [k5, k4] at this
      linear_combination this - two (colConst i)
    have R : ∀ n : ℕ, lo ≤ n → n < k →
        mix 1 (a + turn 1 d) ((n : I) + 2) = 0 ∧ mix 1 (a + turn 1 d) ((n : I) + 1) = 0 ∧
          mix 1 (a + turn 1 d) (n : I) = d (n : I) := by
      intro n h1 h2
      have ht : tested (n : I) := by show lo ≤ ((n : I)).val; rw [val_n n h2]; exact h1
      exact PEqualNP.Outside.L_meta_25834.split_row k (by omega) _ _ _ (fun P => hrow P _ ht)
    have C : ∀ n : ℕ, lo ≤ n → n < k →
        mix 2 (b + turn 3 d) ((n : I) + 2) = 0 ∧ mix 2 (b + turn 3 d) ((n : I) + 1) = 0 ∧
          mix 2 (b + turn 3 d) (n : I) = d ((n : I) - (4 : ℕ)) := by
      intro n h1 h2
      have ht : tested (n : I) := by show lo ≤ ((n : I)).val; rw [val_n n h2]; exact h1
      exact PEqualNP.Outside.L_meta_25834.split_row k (by omega) _ _ _ (fun P => hcol P _ ht)
    have succ1 : ∀ n : ℕ, ((n + 1 : ℕ) : I) = (n : I) + 1 := fun n => by rw [Nat.cast_add, Nat.cast_one]
    have dz : ∀ i : I, lo - 3 ≤ i.val → d i = 0 := by
      intro i hi
      have hlt : i.val < k := ZMod.val_lt i
      rw [← cast_val i]
      by_cases c : lo + 1 ≤ i.val
      · have x := (R (i.val - 1) (by omega) (by omega)).2.1
        rw [← succ1, show i.val - 1 + 1 = i.val by omega] at x
        rw [← (R i.val (by omega) hlt).2.2]; exact x
      · have x := (C (i.val + 3) (by omega) (by omega)).2.1
        rw [← succ1] at x
        have y := (C (i.val + 4) (by omega) (by omega)).2.2
        rw [show i.val + 3 + 1 = i.val + 4 by omega] at x
        rw [x, Nat.cast_add i.val 4, add_sub_cancel_right] at y
        exact y.symm
    have after : ∀ (r : I → ZMod 2),
        (∀ n : ℕ, lo ≤ n → n < k → r ((n : I) + 2) = 0 ∧ r ((n : I) + 1) = 0) →
        ∀ j, 1 ≤ j → j < h + 2 → r ((lo + j : ℕ) : I) = 0 := by
      intro r H j j1 j2
      by_cases c : j ≤ h
      · have x := (H (lo + j - 1) (by omega) (by omega)).2
        rw [← succ1, show lo + j - 1 + 1 = lo + j by omega] at x
        exact x
      · have x := (H (k - 1) (by omega) (by omega)).1
        have e : ((k - 1 : ℕ) : I) + 2 = ((lo + j : ℕ) : I) := by
          rw [show lo + j = (k - 1) + 2 by omega, Nat.cast_add (k-1) 2, Nat.cast_ofNat]
        rwa [e] at x
    refine ⟨dz, ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := act_inv i hi
      by_cases c : j = 0
      · subst c
        rw [Nat.add_zero, (R lo (le_refl _) (by omega)).2.2]
        apply dz; rw [val_n lo (by omega)]; omega
      · exact after _ (fun n h1 h2 => ⟨(R n h1 h2).1, (R n h1 h2).2.1⟩) j (by omega) hj
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := act_inv i hi
      by_cases c : j = 0
      · subst c
        rw [Nat.add_zero, if_pos rfl, (C lo (le_refl _) (by omega)).2.2,
          Nat.cast_sub (show 4 ≤ lo by omega)]
      · rw [if_neg]
        · exact after _ (fun n h1 h2 => ⟨(C n h1 h2).1, (C n h1 h2).2.1⟩) j (by omega) hj
        · intro e
          have hv := congrArg ZMod.val e
          rw [val_n lo (by omega)] at hv
          by_cases c2 : lo + j < k
          · rw [val_n _ c2] at hv; omega
          · rw [show lo + j = k + (lo + j - k) by omega, wrap, val_n _ (by omega)] at hv; omega
